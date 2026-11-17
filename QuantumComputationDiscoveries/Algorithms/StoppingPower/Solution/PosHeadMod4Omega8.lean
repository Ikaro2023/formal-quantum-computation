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

public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.PosHeadRev18Cache

set_option Elab.async false

@[expose] public section

namespace QuantumComputation.Specs.StoppingPowerSolution
open SpecsAux

section ModPosHeadMod4_15476
@[expose] public section
set_option maxRecDepth 262144
set_option exponentiation.threshold 8192

namespace PosHeadMod4_15476

open Operator QProg Matrix HermitianMat LocalClassicalPerm _root_.DynamicCircuit DynCircuitExt
open scoped Matrix BigOperators ComplexOrder MatrixOrder Circuit.Notation
open SpecsAux.SpecMirror
open SpecsAux.DyadicSubgridToeplitz128 (anchorSubTarget1D)
open OctahedralOrbit Dyadic128CoulombMath
open CanonRank7Circuit
open MeasureBranchHadamardSem
  (bitSign bit_cases projZeroAll)
open StreamingBchComparator BchCubeDecoder
open PosSlots24BranchConcrete
open PosMomSelectSandwich (slotBitProj)
open ZeroAncillaUSP (omega8 omega8_sq)

instance (priority := 100000) instNeZeroTwoPowHeadMod4 (n : ℕ) : NeZero (2 ^ n) :=
  ⟨(Nat.two_pow_pos n).ne'⟩

theorem omega8_pow_four : omega8 ^ 4 = -1 := by
  rw [show 4 = 2 * 2 from rfl, pow_mul, omega8_sq, Complex.I_sq]

theorem omega8_pow_eight : omega8 ^ 8 = 1 := by
  rw [show 8 = 4 + 4 from rfl, pow_add, omega8_pow_four]
  norm_num

theorem omega8_ne_zero : omega8 ≠ 0 := fun h ↦
  one_ne_zero (omega8_pow_eight.symm.trans (by rw [h]; norm_num))

theorem star_omega8 : (starRingEnd ℂ) omega8 = omega8 ^ 7 := by
  apply mul_left_cancel₀ omega8_ne_zero
  rw [show omega8 * omega8 ^ 7 = omega8 ^ 8 by ring, omega8_pow_eight]
  dsimp [omega8]
  rw [map_div₀, map_add, map_one, Complex.conj_I, Complex.conj_ofReal, div_mul_div_comm,
    show (1 + Complex.I) * (1 + -Complex.I) = 2 by linear_combination -Complex.I_sq,
    ZeroAncillaUSP.sqrt2_mul_self_c, div_self two_ne_zero]

theorem star_mul_omega8_pow (k : ℕ) : star (omega8 ^ k) * omega8 ^ k = 1 := by
  rw [star_pow, ← mul_pow, show star omega8 * omega8 = 1 by
    change (starRingEnd ℂ) omega8 * omega8 = 1
    rw [star_omega8, show omega8 ^ 7 * omega8 = omega8 ^ 8 by ring, omega8_pow_eight],
    _root_.one_pow]

theorem omega8_pow_mod8 (m : ℕ) : omega8 ^ (m % 8) = omega8 ^ m := by
  conv_rhs =>
    rw [← Nat.div_add_mod m 8, pow_add, pow_mul, omega8_pow_eight, _root_.one_pow, one_mul]

theorem omega8_zmod8_add (a b : ZMod 8) :
    omega8 ^ (a + b).val = omega8 ^ a.val * omega8 ^ b.val := by
  rw [ZMod.val_add, omega8_pow_mod8, pow_add]

lemma diagMulEqOne {m : ℕ} (f g : Fin m → ℂ) (h : ∀ x, f x * g x = 1) :
    Matrix.diagonal f * Matrix.diagonal g = 1 := by
  rw [Matrix.diagonal_mul_diagonal, show (fun x ↦ f x * g x) = fun _ ↦ 1 from funext h,
    Matrix.diagonal_one]

noncomputable def diagZ8UnitaryN {n : ℕ} (p : BitAssignment n → ZMod 8) : Unitary (2 ^ n) :=
  ⟨Matrix.diagonal (fun x : Fin (2 ^ n) ↦ omega8 ^ (p (basisBits n x)).val), by
    rw [Unitary.mem_iff, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose]
    exact ⟨diagMulEqOne _ _ fun _ ↦ star_mul_omega8_pow _,
      diagMulEqOne _ _ fun _ ↦ (mul_comm _ _).trans (star_mul_omega8_pow _)⟩⟩

private lemma basisBits_symm {n : ℕ} (β : BitAssignment n) :
    basisBits n ((basisBitsEquiv n).symm β) = β :=
  (basisBitsEquiv n).apply_symm_apply β

private lemma single_smul_ket {n : ℕ} (c : ℂ) (β : BitAssignment n) :
    (Pi.single ((basisBitsEquiv n).symm β) c : Fin (2 ^ n) → ℂ) = c • ket β :=
  funext fun x ↦ by by_cases hx : x = (basisBitsEquiv n).symm β <;> simp [hx, ket, basisState]

private lemma ket_eq_single_symm {n : ℕ} (β : BitAssignment n) :
    (Pi.single ((basisBitsEquiv n).symm β) (1 : ℂ) : Fin (2 ^ n) → ℂ) = ket β :=
  (single_smul_ket 1 β).trans (one_smul _ _)

theorem ket_diagZ8UnitaryN {n : ℕ} (p : BitAssignment n → ZMod 8) (β : BitAssignment n) :
    (diagZ8UnitaryN p).1.mulVec (ket β) = (omega8 ^ (p β).val) • ket β := by
  change (Matrix.diagonal _).mulVec (ket β) = _
  rw [← ket_eq_single_symm β, Matrix.diagonal_mulVec_single,
    basisBits_symm, mul_one, single_smul_ket]

theorem diagZ8UnitaryN_mul {n : ℕ} (p₁ p₂ : BitAssignment n → ZMod 8) :
    diagZ8UnitaryN p₁ * diagZ8UnitaryN p₂ = diagZ8UnitaryN (fun β ↦ p₁ β + p₂ β) := by
  apply Subtype.ext
  simp only [Submonoid.coe_mul, diagZ8UnitaryN, Matrix.diagonal_mul_diagonal]
  exact congrArg Matrix.diagonal (funext fun _ ↦ (omega8_zmod8_add _ _).symm)

theorem diagZ8UnitaryN_comm_projZeroAll {n k : ℕ} (scr : Fin k → Wire n)
    (p : BitAssignment n → ZMod 8) :
    (diagZ8UnitaryN p).1 * projZeroAll k scr = projZeroAll k scr * (diagZ8UnitaryN p).1 := by
  rw [PosSlots24BranchConcrete.projZeroAll_eq_diagonal]
  change Matrix.diagonal _ * Matrix.diagonal _ = Matrix.diagonal _ * Matrix.diagonal _
  rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  exact congrArg Matrix.diagonal (funext fun _ ↦ mul_comm _ _)

theorem embedUnitary_diagZ8UnitaryN {n kAct : ℕ} (rAct : QRegister kAct n)
    (p : BitAssignment kAct → ZMod 8) : rAct.embedUnitary (diagZ8UnitaryN p) =
      diagZ8UnitaryN (fun β : BitAssignment n ↦ p (fun i ↦ β (rAct i))) := by
  apply Subtype.ext
  ext r c
  by_cases hrc : r = c
  · subst hrc
    simp only [QRegister.embedUnitary_val, QRegister.embedMatrix_apply, diagZ8UnitaryN, ↓reduceIte,
      Matrix.diagonal_apply_eq, mul_one]
    rw [show basisBits kAct (rAct.extractIndex r) = fun i ↦ basisBits n r (rAct i) from
      funext (QRegister.basisBits_extractIndex rAct r)]
  · simp only [QRegister.embedUnitary_val, QRegister.embedMatrix_apply, diagZ8UnitaryN,
      Matrix.diagonal_apply_ne _ hrc]
    by_cases envEq : (rAct.basisSplitEquiv r).2 = (rAct.basisSplitEquiv c).2
    · have hex : rAct.extractIndex r ≠ rAct.extractIndex c := fun heq ↦ hrc <|
        (basisBitsEquiv n).injective <| funext fun q ↦ by
          by_cases hq : q ∈ Set.range rAct.wires
          · obtain ⟨i, rfl⟩ := hq
            change basisBits n r (rAct.wires i) = basisBits n c (rAct.wires i)
            simpa only [QRegister.basisBits_extractIndex] using congrFun (congrArg (basisBits kAct)
              heq) i
          · exact (rAct.basisSplit_environment_eq_iff r c).mp envEq q hq
      simp [envEq, Matrix.diagonal_apply_ne _ hex]
    · simp [envEq]

private lemma qreg_slice_wires_eq {k n : ℕ} (r : QRegister k n) (o w : ℕ) (h : o + w ≤ k)
    (i : Fin w) : (r.slice o w h).wires i = r.wires ⟨o + i.val, by omega⟩ := by
  simp

/-! ## Section 2: `2-T` Controlled-`S` + `CZ` Leaf (`leafMod4`) & `70-T`/Slot `pointEqMod4SlotDyn`
-/

theorem ket_T_eval {n : ℕ} (q : Wire n) (γ : BitAssignment n) :
    (Circuit.T q).eval.1.mulVec (ket γ) =
      (omega8 ^ (if γ q = 0 then (0 : ZMod 8) else 1).val) • ket γ := by
  rw [Circuit.eval_single, QRegister.embedUnitary_val, PrimitiveGate.eval_t_val,
    OctahedralOrbit.singleton_embedMatrix_mulVec_ket]
  rcases bit_cases (γ q) with hb | hb <;>
    simp [hb, (congrArg (Function.update γ q) hb.symm).trans (Function.update_eq_self q γ),
      omega8, show (1 : ZMod 8).val = 1 from rfl]

theorem ket_S_eval {n : ℕ} (q : Wire n) (γ : BitAssignment n) :
    (Circuit.S q).eval.1.mulVec (ket γ) = (if γ q = 0 then (1 : ℂ) else Complex.I) • ket γ := by
  rw [Circuit.eval_single, QRegister.embedUnitary_val, PrimitiveGate.eval_s_val,
    OctahedralOrbit.singleton_embedMatrix_mulVec_ket]
  rcases bit_cases (γ q) with hb | hb <;>
    simp [hb, (congrArg (Function.update γ q) hb.symm).trans (Function.update_eq_self q γ)]

theorem ket_Z_eval {n : ℕ} (q : Wire n) (γ : BitAssignment n) :
    (Circuit.Z q).eval.1.mulVec (ket γ) = bitSign (γ q) • ket γ := by
  rw [Circuit.eval_single, QRegister.embedUnitary_val, PrimitiveGate.eval]
  change ((QRegister.singleton q).embedMatrix !![1,0; 0,-1]).mulVec _ = _
  rw [OctahedralOrbit.singleton_embedMatrix_mulVec_ket]
  rcases bit_cases (γ q) with hb | hb <;>
    simp [hb, (congrArg (Function.update γ q) hb.symm).trans (Function.update_eq_self q γ),
      bitSign]

theorem ket_Tinv_eval {n : ℕ} (q : Wire n) (γ : BitAssignment n) :
    (Circuit.T q).inverse.eval.1.mulVec (ket γ) =
      (omega8 ^ (if γ q = 0 then (0 : ZMod 8) else 7).val) • ket γ := by
  change (Circuit.T q ;;ᶜ (Circuit.S q ;;ᶜ (Circuit.Z q ;;ᶜ .identity))).eval.1.mulVec (ket γ) = _
  simp only [OctahedralOrbit.eval_seq_mulVec, Circuit.eval_identity, Submonoid.coe_one,
    Matrix.one_mulVec, ket_T_eval, ket_S_eval, ket_Z_eval, Matrix.mulVec_smul, smul_smul]
  rcases bit_cases (γ q) with hb | hb
  · simp [hb, bitSign]
  · refine congrArg (· • ket γ) ?_
    simp only [hb, one_ne_zero, ↓reduceIte, bitSign, show (1 : ZMod 8).val = 1 from rfl,
      show (7 : ZMod 8).val = 7 from rfl, ← omega8_sq, ← omega8_pow_four]
    ring

theorem ket_czCircuit_z8 {n : ℕ} (c t : Wire n) (hct : c ≠ t) (γ : BitAssignment n) :
    (DynCircuitExt.czCircuit c t hct).eval.1.mulVec (ket γ) =
      (omega8 ^ (if γ c * γ t = 0 then (0 : ZMod 8) else 4).val) • ket γ := by
  rw [← mbh_ket_eq_ket, ← gket_eq_ket, DynCircuitExt.gket_czCircuit, gket_eq_ket, mbh_ket_eq_ket]
  rcases bit_cases (γ c * γ t) with h | h <;>
    simp [h, DynCircuitExt.gbitSign, show (4 : ZMod 8).val = 4 from rfl, omega8_pow_four]

theorem count_withAndChain_t_const {Var : Type} {n : ℕ} (v : Var) (cLeafT : ℕ) :
    ∀ (k : ℕ) (acc : Wire n) (ctrls scratches : Fin k → Wire n)
      (hacc_c : ∀ i, acc ≠ ctrls i) (hacc_s : ∀ i, acc ≠ scratches i)
      (hc_s : ∀ i j, ctrls i ≠ scratches j) (hs_inj : Function.Injective scratches)
      (leaf : (w : Wire n) → (w = acc ∨ ∃ i, w = scratches i) → DynamicCircuit Var n),
      (∀ w hw, (leaf w hw).count PrimitiveGate.T = cLeafT) →
      (DynCircuitExt.withAndChain v k acc ctrls scratches hacc_c hacc_s hc_s hs_inj leaf).count
        PrimitiveGate.T = 4 * k + cLeafT
  | 0, acc, _, _, _, _, _, _, leaf, h0 =>
    by simpa [DynCircuitExt.withAndChain] using h0 acc (Or.inl rfl)
  | k + 1, _, ctrls, scratches, _, _, hc_s, hs_inj, _, h0 => by
      unfold DynCircuitExt.withAndChain
      rw [DynCircuitExt.count_withTempAnd_t, count_withAndChain_t_const v cLeafT k (scratches 0)
        (fun i ↦ ctrls i.succ) (fun i ↦ scratches i.succ) (fun i ↦ (hc_s i.succ 0).symm)
        (fun i h ↦ Fin.succ_ne_zero i (hs_inj h).symm) (fun i j ↦ hc_s i.succ j.succ)
        (hs_inj.comp (Fin.succ_injective _)) _ fun w _ ↦ h0 w _]
      omega

/-! ## Section 3: `N`-Slot Streaming Mod-4 Phase Accumulator (`streamingMod4AccumDyn`) -/

/-! ## Section 4: Unconditional Involution `flipThClean` & `monomialZ8UnitaryN` Combinators -/

/-- Flip wire `wTh` when `b = true`. -/
def flipTh {n : ℕ} (wTh : Wire n) (b : Bool) (γ : BitAssignment n) : BitAssignment n :=
  if b then Function.update γ wTh (γ wTh + 1) else γ

/-- Unconditional involution flipping `wTh` when `d (Function.update γ wTh 0) = true`. -/
def flipThClean {n : ℕ} (wTh : Wire n) (d : BitAssignment n → Bool) (γ : BitAssignment n) :
    BitAssignment n := flipTh wTh (d (Function.update γ wTh 0)) γ

@[simp] theorem flipTh_update_zero {n : ℕ} (wTh : Wire n) (b : Bool) (γ : BitAssignment n) :
    Function.update (flipTh wTh b γ) wTh 0 = Function.update γ wTh 0 := by
  unfold flipTh
  split_ifs <;> simp

@[simp] theorem flipTh_involutive {n : ℕ} (wTh : Wire n) (b : Bool) (γ : BitAssignment n) :
    flipTh wTh b (flipTh wTh b γ) = γ := by
  cases b
  · rfl
  · simp [flipTh, add_assoc, CharTwo.add_self_eq_zero]

@[simp] theorem flipThClean_update_zero {n : ℕ} (wTh : Wire n) (d : BitAssignment n → Bool)
    (γ : BitAssignment n) : Function.update (flipThClean wTh d γ) wTh 0 = Function.update γ wTh 0 :=
  flipTh_update_zero wTh _ γ

@[simp] theorem flipThClean_involutive {n : ℕ} (wTh : Wire n) (d : BitAssignment n → Bool)
    (γ : BitAssignment n) : flipThClean wTh d (flipThClean wTh d γ) = γ := by
  unfold flipThClean
  rw [flipTh_update_zero, flipTh_involutive]

theorem flipTh_apply_ne {n : ℕ} (wTh : Wire n) (b : Bool) (γ : BitAssignment n) {q : Wire n}
    (hq : q ≠ wTh) : flipTh wTh b γ q = γ q := by
  unfold flipTh
  split_ifs <;> simp [Function.update_of_ne hq]

theorem flipThClean_apply_ne {n : ℕ} (wTh : Wire n) (d : BitAssignment n → Bool)
    (γ : BitAssignment n) {q : Wire n} (hq : q ≠ wTh) : flipThClean wTh d γ q = γ q :=
  flipTh_apply_ne wTh _ γ hq

/-- Involution permutation on `Fin (2 ^ n)` induced by `flipThClean wTh d`. -/
noncomputable def permThClean {n : ℕ} (wTh : Wire n) (d : BitAssignment n → Bool) :
    Equiv.Perm (Fin (2 ^ n)) where
  toFun x := (basisBitsEquiv n).symm (flipThClean wTh d (basisBits n x))
  invFun x := (basisBitsEquiv n).symm (flipThClean wTh d (basisBits n x))
  left_inv x := by simp
  right_inv x := by simp

@[simp] theorem permThClean_symm {n : ℕ} (wTh : Wire n) (d : BitAssignment n → Bool) :
    (permThClean wTh d).symm = permThClean wTh d := rfl

theorem ket_permThClean {n : ℕ} (wTh : Wire n) (d : BitAssignment n → Bool) (β : BitAssignment n) :
    (permutationUnitary (permThClean wTh d)).1.mulVec (ket β) = ket (flipThClean wTh d β) := by
  rw [← ket_eq_single_symm β, Operator.permutationUnitary_mulVec_single]
  dsimp [permThClean]
  rw [basisBits_symm β, ket_eq_single_symm]

/-- Monomial unitary multiplying `ket β` by `omega8 ^ (p β).val` and flipping `wTh` when
`d (Function.update β wTh 0) = true`. -/
noncomputable def monomialZ8UnitaryN {n : ℕ} (wTh : Wire n) (d : BitAssignment n → Bool)
    (p : BitAssignment n → ZMod 8) : Unitary (2 ^ n) :=
  permutationUnitary (permThClean wTh d) * diagZ8UnitaryN p

theorem ket_monomialZ8UnitaryN {n : ℕ} (wTh : Wire n) (d : BitAssignment n → Bool)
    (p : BitAssignment n → ZMod 8) (β : BitAssignment n) :
    (monomialZ8UnitaryN wTh d p).1.mulVec (ket β) =
      (omega8 ^ (p β).val) • ket (flipThClean wTh d β) := by
  dsimp only [monomialZ8UnitaryN, Submonoid.coe_mul]
  rw [← Matrix.mulVec_mulVec, ket_diagZ8UnitaryN, Matrix.mulVec_smul, ket_permThClean]

theorem embedUnitary_permThClean {n kAct : ℕ} (rAct : QRegister kAct n) (iTh : Wire kAct)
    (d : BitAssignment kAct → Bool) :
    rAct.embedUnitary (permutationUnitary (permThClean iTh d)) =
      permutationUnitary (permThClean (rAct iTh) fun β : BitAssignment n ↦ d fun i ↦ β (rAct i)) :=
        by
  apply Subtype.ext
  apply matrix_ext_of_ket
  intro β
  let fβ := flipThClean (rAct iTh) (fun γ : BitAssignment n ↦ d fun i ↦ γ (rAct i)) β
  have hcomp_upd : ∀ v : ZMod 2, (fun i ↦ Function.update β (rAct iTh) v (rAct i)) =
      Function.update (fun i ↦ β (rAct i)) iTh v := fun v ↦ funext fun i ↦ by
    by_cases hi : i = iTh
    · subst hi; simp
    · rw [Function.update_of_ne hi, Function.update_of_ne (rAct.wires.injective.ne hi)]
  rw [ket_permThClean, ket_eq_basisKet, ket_eq_basisKet]
  refine InterWalkRSum42Hoist.embedPermGen_mulVec_basisKet rAct (permThClean iTh d) β fβ
    (fun w hw ↦ flipThClean_apply_ne (rAct iTh) _ β
      fun heq ↦ hw ((QRegister.mem_image rAct w).mpr ⟨iTh, heq.symm⟩)) ?_
  apply (basisBitsEquiv kAct).injective
  funext j
  change basisBits kAct _ j = basisBits kAct _ j
  dsimp [permThClean]
  rw [QRegister.basisBits_extractIndex, basisBits_symm,
    basisBits_symm,
    show basisBits kAct (rAct.extractIndex ((basisBitsEquiv n).symm β)) = fun i ↦ β (rAct i) from
      funext fun i ↦ (QRegister.basisBits_extractIndex rAct _ i).trans
        (congrFun (basisBits_symm β) (rAct i))]
  dsimp only [fβ]
  unfold flipThClean flipTh
  simp only [hcomp_upd 0]
  split_ifs
  · exact congrFun (hcomp_upd (β (rAct iTh) + 1)) j
  · rfl

theorem embedUnitary_monomialZ8UnitaryN {n kAct : ℕ} (rAct : QRegister kAct n) (iTh : Wire kAct)
    (d : BitAssignment kAct → Bool) (p : BitAssignment kAct → ZMod 8) :
    rAct.embedUnitary (monomialZ8UnitaryN iTh d p) = monomialZ8UnitaryN (rAct iTh)
      (fun β : BitAssignment n ↦ d fun i ↦ β (rAct i))
      (fun β : BitAssignment n ↦ p fun i ↦ β (rAct i)) := by
  dsimp only [monomialZ8UnitaryN]
  rw [QRegister.embedUnitary_mul, embedUnitary_permThClean, embedUnitary_diagZ8UnitaryN]

private theorem monomialZ8UnitaryN_self_adj {n : ℕ} (wTh : Wire n) (d : BitAssignment n → Bool)
    (p : BitAssignment n → ZMod 8) (hp : ∀ β : BitAssignment n, p β + p (flipThClean wTh d β) = 0) :
    (monomialZ8UnitaryN wTh d p).1ᴴ = (monomialZ8UnitaryN wTh d p).1 := by
  let U := monomialZ8UnitaryN wTh d p
  have hsq : U.1 * U.1 = 1 := matrix_ext_of_ket fun β ↦ by
    rw [Matrix.one_mulVec, ← Matrix.mulVec_mulVec, ket_monomialZ8UnitaryN, Matrix.mulVec_smul,
      ket_monomialZ8UnitaryN, flipThClean_involutive, smul_smul, ← omega8_zmod8_add, hp β,
      show (0 : ZMod 8).val = 0 from rfl, _root_.pow_zero, one_smul]
  have hu : U.1ᴴ * U.1 = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using Unitary.coe_star_mul_self U
  rw [← Matrix.mul_one U.1ᴴ, ← hsq, ← Matrix.mul_assoc, hu, Matrix.one_mul]

/-! ## Section 5: `15,476-T` Mod-4 Head Phase Circuit (`dHeadPhaseMod4_236Dyn` &
`dHeadPhaseMod4_246Dyn`) & Clean-Workspace Realization -/

theorem ket_S_z8 {n : ℕ} (q : Wire n) (γ : BitAssignment n) :
    (Circuit.S q).eval.1.mulVec (ket γ) = (omega8 ^ (if γ q = 0 then (0 : ZMod 8) else
      2).val) • ket γ := by
  rw [ket_S_eval]
  congr 1
  rcases bit_cases (γ q) with hb | hb <;> simp [hb, show (2 : ZMod 8).val = 2 from rfl, omega8_sq]

private lemma wHeadThresh_ne_coreIdx {n : ℕ} (rCore : QRegister posCoreWires n)
    (k : Fin posCoreWires) (hk : k.val ≠ 3985) : wHeadThresh rCore ≠ rCore.wires k := by
  rw [show wHeadThresh rCore = rCore.wires ⟨3985, by decide⟩ from
    qreg_slice_wires_eq rCore 3954 80 (by decide) ⟨31, by decide⟩]
  exact fun h ↦ hk (congrArg Fin.val (rCore.wires.injective h)).symm

private lemma wHeadThresh_ne_subSlice {n : ℕ} (rCore : QRegister posCoreWires n)
    (o w : ℕ) (h : o + w ≤ 80) (i : Fin w) (hne : o + i.val ≠ 31) :
    wHeadThresh rCore ≠ (rSubPayloadCore rCore).slice o w h i := by
  change (rSubPayloadCore rCore).wires ⟨31,
    by decide⟩ ≠ ((rSubPayloadCore rCore).slice o w h).wires i
  rw [qreg_slice_wires_eq]
  exact fun heq ↦ hne (congrArg Fin.val ((rSubPayloadCore rCore).wires.injective heq)).symm

theorem wHeadThresh_ne_rNucIdx {n : ℕ} (rCore : QRegister posCoreWires n) (i : Fin 8) :
    wHeadThresh rCore ≠ rNucIdx rCore i :=
  wHeadThresh_ne_subSlice rCore 6 8 (by decide) i (by have := i.isLt; omega)

theorem wHeadThresh_ne_rAnchorIdx {n : ℕ} (rCore : QRegister posCoreWires n) (i : Fin 8) :
    wHeadThresh rCore ≠ rAnchorIdx rCore i :=
  wHeadThresh_ne_subSlice rCore 14 8 (by decide) i (by have := i.isLt; omega)

theorem wHeadThresh_ne_wSlot0Core {n : ℕ} (rCore : QRegister posCoreWires n) :
    wHeadThresh rCore ≠ wSlot0Core rCore :=
  wHeadThresh_ne_coreIdx rCore ⟨3948, by decide⟩ (by decide)

theorem wHeadThresh_ne_wSlot1Core {n : ℕ} (rCore : QRegister posCoreWires n) :
    wHeadThresh rCore ≠ wSlot1Core rCore :=
  wHeadThresh_ne_coreIdx rCore ⟨3949, by decide⟩ (by decide)

theorem wHeadThresh_ne_wSlot2Core {n : ℕ} (rCore : QRegister posCoreWires n) :
    wHeadThresh rCore ≠ wSlot2Core rCore :=
  wHeadThresh_ne_coreIdx rCore ⟨3950, by decide⟩ (by decide)

theorem wHeadThresh_ne_wSubReject {n : ℕ} (rCore : QRegister posCoreWires n) :
    wHeadThresh rCore ≠ wSubReject rCore :=
  fun h ↦ absurd (congrArg Fin.val ((rSubPayloadCore rCore).wires.injective h)) (by decide)

theorem wHeadThresh_ne_wIsHead {n : ℕ} (rCore : QRegister posCoreWires n) :
    wHeadThresh rCore ≠ wIsHead rCore :=
  fun h ↦ absurd (congrArg Fin.val ((rSubPayloadCore rCore).wires.injective h)) (by decide)

theorem wHeadThresh_ne_rCosetB0 {n : ℕ} (rCore : QRegister posCoreWires n) (w : Fin 3) :
    wHeadThresh rCore ≠ rCosetB0 rCore w :=
  wHeadThresh_ne_subSlice rCore 3 3 (by decide) w (by have := w.isLt; omega)

theorem wHeadThresh_ne_rHeadFine21 {n : ℕ} (rCore : QRegister posCoreWires n) (idx : Fin 21) :
    wHeadThresh rCore ≠ rHeadFine21 rCore idx :=
  wHeadThresh_ne_subSlice rCore 32 21 (by decide) idx (by have := idx.isLt; omega)
set_option allowUnsafeReducibility true in

def headEnBoolSpec (β : BitAssignment posCoreWires) : Bool :=
  let rCore := QRegExt.ofFin posCoreWires
  let isPos01B : Bool := (β (wSlot2Core rCore) == 0) && Bool.not (β (wSlot1Core rCore) == 1)
  let s0 := β (wSlot0Core rCore) == 1
  let nucOk := Bool.not s0 → regVal (rNucIdx rCore) β < 216
  let ancOk := regVal (rAnchorIdx rCore) β < 218
  let inB : Bool := decide nucOk && decide ancOk
  isPos01B && Bool.not (β (wSubReject rCore) == 1) && inB && (β (wIsHead rCore) == 1)

/-- Head hit set `S(β) ⊆ Fin 218` on `posCoreWires`. -/
def headHitSetSpec (β : BitAssignment posCoreWires) : Finset (Fin 218) :=
  let rCore := QRegExt.ofFin posCoreWires
  let s0 := β (wSlot0Core rCore) == 1
  let dHead := fineCoordOfReg21 (rHeadFine21 rCore) β
  let y0 := slotSubGridCoord64 (rElecSlot rCore 0) β
  let b0 := parity3OfReg (rCosetB0 rCore) β
  let yTarget : SubGridCoord64 := fun w ↦
    if Bool.not s0 then ⟨(dHead w).val / 2, by omega⟩
    else (anchorSubTarget1D (y0 w) (if b0 w then 1 else 0) (dHead w)).1
  Finset.univ.filter fun e ↦
    (Bool.not s0 || decide (e.val ≠ 0)) &&
      decide (slotSubGridCoord64 (rElecSlot rCore e) β = yTarget)

/-- `ZMod 8` phase exponent of the Mod-4 Head Phase Oracle on `posCoreWires`. -/
def headPhaseMod4Z8Spec (β : BitAssignment posCoreWires) : ZMod 8 :=
  let rCore := QRegExt.ofFin posCoreWires
  if Bool.not (headEnBoolSpec β) then 0
  else
    let s0Z8 : ZMod 8 := if β (wSlot0Core rCore) == 1 then 4 else 0
    let tZ8 : ZMod 8 := if β (wHeadThresh rCore) == 1 then 4 else 0
    s0Z8 + ((headHitSetSpec β).card : ZMod 8) * (2 + tZ8)

/-- Combined `ZMod 8` phase exponent of the Mod-4 Position Phase Oracle on `posCoreWires`. -/
def posPhaseMod4Z8Spec (slot2SwappedTo0 : Bool) (tailSign : Fin orbitCount47905 → Bool)
    (tailMag30 : Fin orbitCount47905 → Fin (2 ^ 30)) (β : BitAssignment posCoreWires) : ZMod 8
    := headPhaseMod4Z8Spec β + (if tailAndSlackPhaseBitSpec slot2SwappedTo0 tailSign tailMag30
    β then 4 else 0)

/-- Target `Unitary (2 ^ posCoreWires)` realized by `dHeadPhaseMod4_236Dyn` and
  `dHeadPhaseMod4_246Dyn`. -/
noncomputable def uHeadPhaseMod4 : Unitary (2 ^ posCoreWires) := monomialZ8UnitaryN
    (wHeadThresh (QRegExt.ofFin posCoreWires)) headEnBoolSpec headPhaseMod4Z8Spec

/-- Target `Unitary (2 ^ posCoreWires)` realized by `dPosPhaseFromTailMod4_236Dyn` and
  `dPosPhaseFromTailMod4_246Dyn`. -/
noncomputable def uPosPhaseMod4 (slot2SwappedTo0 : Bool)
    (tailSign : Fin orbitCount47905 → Bool)
    (tailMag30 : Fin orbitCount47905 → Fin (2 ^ 30)) : Unitary (2 ^ posCoreWires) :=
  monomialZ8UnitaryN (wHeadThresh (QRegExt.ofFin posCoreWires))
    headEnBoolSpec (posPhaseMod4Z8Spec slot2SwappedTo0 tailSign tailMag30)

private lemma upd_wTh_ne {w : Wire posCoreWires}
    (hne : w ≠ wHeadThresh (QRegExt.ofFin posCoreWires))
    (β : BitAssignment posCoreWires) (v : ZMod 2) :
    Function.update β (wHeadThresh (QRegExt.ofFin posCoreWires)) v w = β w :=
  Function.update_of_ne hne _ _

private lemma regVal_upd_wTh {m : ℕ} (r : QRegister m posCoreWires)
    (hr : ∀ i, r i ≠ wHeadThresh (QRegExt.ofFin posCoreWires))
    (β : BitAssignment posCoreWires) (v : ZMod 2) :
    regVal r (Function.update β (wHeadThresh (QRegExt.ofFin posCoreWires)) v) = regVal r β := by
  unfold regVal bitsVal
  exact Finset.sum_congr rfl fun i _ ↦ by dsimp only; rw [upd_wTh_ne (hr i)]

private lemma parity3_upd_wTh (r : QRegister 3 posCoreWires)
    (hr : ∀ i, r i ≠ wHeadThresh (QRegExt.ofFin posCoreWires))
    (β : BitAssignment posCoreWires) (v : ZMod 2) :
    parity3OfReg r (Function.update β (wHeadThresh (QRegExt.ofFin posCoreWires)) v) =
      parity3OfReg r β :=
  funext fun i ↦ by dsimp [parity3OfReg]; rw [upd_wTh_ne (hr i)]

private lemma elecCoord_upd_wHeadThresh (β : BitAssignment posCoreWires) (v : ZMod 2)
    (e : Fin 218) :
    slotSubGridCoord64 (rElecSlot (QRegExt.ofFin posCoreWires) e)
      (Function.update β (wHeadThresh (QRegExt.ofFin posCoreWires)) v) =
    slotSubGridCoord64 (rElecSlot (QRegExt.ofFin posCoreWires) e) β := by
  let rCore := QRegExt.ofFin posCoreWires
  funext w
  ext
  change bitsVal (fun j : Fin 6 ↦ Function.update β (wHeadThresh rCore) v
      (axisBitRev6 (rElecSlot rCore e) w j)) =
    bitsVal (fun j : Fin 6 ↦ β (axisBitRev6 (rElecSlot rCore e) w j))
  unfold bitsVal
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  dsimp only
  rw [upd_wTh_ne fun h ↦ by
    have hv : 18 * e.val + (6 * w.val + (5 - j.val)) = 3985 := congrArg Fin.val h
    have := e.isLt
    have := w.isLt
    have := j.isLt
    omega]

theorem headEnBoolSpec_update_wHeadThresh (β : BitAssignment posCoreWires) (v : ZMod 2) :
    headEnBoolSpec (Function.update β (wHeadThresh (QRegExt.ofFin posCoreWires)) v) =
      headEnBoolSpec β := by
  dsimp only [headEnBoolSpec]
  rw [upd_wTh_ne (wHeadThresh_ne_wSlot2Core (QRegExt.ofFin posCoreWires)).symm,
    upd_wTh_ne (wHeadThresh_ne_wSlot1Core (QRegExt.ofFin posCoreWires)).symm,
    upd_wTh_ne (wHeadThresh_ne_wSlot0Core (QRegExt.ofFin posCoreWires)).symm,
    upd_wTh_ne (wHeadThresh_ne_wSubReject (QRegExt.ofFin posCoreWires)).symm,
    upd_wTh_ne (wHeadThresh_ne_wIsHead (QRegExt.ofFin posCoreWires)).symm,
    regVal_upd_wTh (rNucIdx (QRegExt.ofFin posCoreWires))
      (fun i ↦ (wHeadThresh_ne_rNucIdx (QRegExt.ofFin posCoreWires) i).symm),
    regVal_upd_wTh (rAnchorIdx (QRegExt.ofFin posCoreWires))
      (fun i ↦ (wHeadThresh_ne_rAnchorIdx (QRegExt.ofFin posCoreWires) i).symm)]

theorem headHitSetSpec_update_wHeadThresh (β : BitAssignment posCoreWires) (v : ZMod 2) :
    headHitSetSpec (Function.update β (wHeadThresh (QRegExt.ofFin posCoreWires)) v) =
      headHitSetSpec β := by
  have hFine : fineCoordOfReg21 (rHeadFine21 (QRegExt.ofFin posCoreWires))
      (Function.update β (wHeadThresh (QRegExt.ofFin posCoreWires)) v) =
      fineCoordOfReg21 (rHeadFine21 (QRegExt.ofFin posCoreWires)) β :=
    funext fun w ↦ Fin.ext <| regVal_upd_wTh
      ((rHeadFine21 (QRegExt.ofFin posCoreWires)).slice (7 * w.val) 7 (by omega))
      (fun i ↦ (wHeadThresh_ne_rHeadFine21 (QRegExt.ofFin posCoreWires)
        ⟨7 * w.val + i.val, by omega⟩).symm) β v
  dsimp only [headHitSetSpec]
  simp only [upd_wTh_ne (wHeadThresh_ne_wSlot0Core (QRegExt.ofFin posCoreWires)).symm, hFine,
    parity3_upd_wTh (rCosetB0 (QRegExt.ofFin posCoreWires))
      (fun w ↦ (wHeadThresh_ne_rCosetB0 (QRegExt.ofFin posCoreWires) w).symm),
    elecCoord_upd_wHeadThresh]

theorem tailAndSlackPhaseBitSpec_update_wHeadThresh (slot2SwappedTo0 : Bool)
    (tailSign : Fin orbitCount47905 → Bool) (tailMag30 : Fin orbitCount47905 → Fin (2 ^ 30))
    (β : BitAssignment posCoreWires) (v : ZMod 2) :
    tailAndSlackPhaseBitSpec slot2SwappedTo0 tailSign tailMag30
      (Function.update β (wHeadThresh (QRegExt.ofFin posCoreWires)) v) =
      tailAndSlackPhaseBitSpec slot2SwappedTo0 tailSign tailMag30 β := by
  dsimp only [tailAndSlackPhaseBitSpec]
  simp only [upd_wTh_ne (wHeadThresh_ne_wSlot2Core (QRegExt.ofFin posCoreWires)).symm,
    upd_wTh_ne (wHeadThresh_ne_wSlot1Core (QRegExt.ofFin posCoreWires)).symm,
    upd_wTh_ne (wHeadThresh_ne_wSlot0Core (QRegExt.ofFin posCoreWires)).symm,
    upd_wTh_ne (wHeadThresh_ne_wSubReject (QRegExt.ofFin posCoreWires)).symm,
    upd_wTh_ne (wHeadThresh_ne_wIsHead (QRegExt.ofFin posCoreWires)).symm,
    upd_wTh_ne (by decide : wRejectZero (QRegExt.ofFin posCoreWires) ≠
      wHeadThresh (QRegExt.ofFin posCoreWires)),
    regVal_upd_wTh (rNucIdx (QRegExt.ofFin posCoreWires))
      (fun i ↦ (wHeadThresh_ne_rNucIdx (QRegExt.ofFin posCoreWires) i).symm),
    regVal_upd_wTh (rAnchorIdx (QRegExt.ofFin posCoreWires))
      (fun i ↦ (wHeadThresh_ne_rAnchorIdx (QRegExt.ofFin posCoreWires) i).symm),
    regVal_upd_wTh (rPartnerIdx (QRegExt.ofFin posCoreWires)) (fun i ↦ by revert i; decide),
    regVal_upd_wTh (rTailKeep30 (QRegExt.ofFin posCoreWires)) (fun i ↦ by revert i; decide),
    parity3_upd_wTh (rCosetB1 (QRegExt.ofFin posCoreWires)) (fun w ↦ by revert w; decide),
    parity3_upd_wTh (rCosetB0 (QRegExt.ofFin posCoreWires))
      (fun w ↦ (wHeadThresh_ne_rCosetB0 (QRegExt.ofFin posCoreWires) w).symm),
    elecCoord_upd_wHeadThresh]

theorem uPosPhaseMod4_sa_core (slot2SwappedTo0 : Bool) (tailSign : Fin orbitCount47905 → Bool)
    (tailMag30 : Fin orbitCount47905 → Fin (2 ^ 30)) :
    (uPosPhaseMod4 slot2SwappedTo0 tailSign tailMag30).1ᴴ =
      (uPosPhaseMod4 slot2SwappedTo0 tailSign tailMag30).1 := by
  let rCore := QRegExt.ofFin posCoreWires
  refine monomialZ8UnitaryN_self_adj (wHeadThresh rCore) headEnBoolSpec
    (posPhaseMod4Z8Spec slot2SwappedTo0 tailSign tailMag30) fun β ↦ ?_
  unfold flipThClean flipTh posPhaseMod4Z8Spec headPhaseMod4Z8Spec
  rw [headEnBoolSpec_update_wHeadThresh]
  cases hen : headEnBoolSpec β
  · simp only [Bool.false_eq_true, ↓reduceIte, hen, Bool.not_false, zero_add]
    cases tailAndSlackPhaseBitSpec slot2SwappedTo0 tailSign tailMag30 β <;> decide
  · simp only [rCore, ↓reduceIte]
    rw [tailAndSlackPhaseBitSpec_update_wHeadThresh, headEnBoolSpec_update_wHeadThresh, hen,
      headHitSetSpec_update_wHeadThresh,
      Function.update_of_ne (wHeadThresh_ne_wSlot0Core (QRegExt.ofFin posCoreWires)).symm,
      Function.update_self]
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    generalize β (wSlot0Core (QRegExt.ofFin posCoreWires)) = s0,
      β (wHeadThresh (QRegExt.ofFin posCoreWires)) = th,
      ((headHitSetSpec β).card : ZMod 8) = c,
      tailAndSlackPhaseBitSpec slot2SwappedTo0 tailSign tailMag30 β = t
    fin_cases s0 <;> fin_cases th <;> fin_cases c <;> cases t <;> decide

private theorem slotBitProj_one_mulVec_ket {n : ℕ} (w2 : Wire n) (β : BitAssignment n) :
    (slotBitProj w2 1).mulVec (ket β) = if β w2 = 1 then ket β else 0 := by
  change (Matrix.diagonal (fun x : Fin (2 ^ n) ↦
    if (basisBits n x w2).val = 1 then (1 : ℂ) else 0)).mulVec (ket β) = _
  rw [← ket_eq_single_symm β, Matrix.diagonal_mulVec_single, basisBits_symm]
  rcases bit_cases (β w2) with h | h <;> simp [h, show (1 : ZMod 2).val = 1 from rfl]

theorem uPosPhaseMod4_on_P1 (slot2SwappedTo0 : Bool) (tailSign : Fin orbitCount47905 → Bool)
    (tailMag30 : Fin orbitCount47905 → Fin (2 ^ 30)) :
    (uPosPhaseMod4 slot2SwappedTo0 tailSign tailMag30).1 *
      slotBitProj (wSlot2Core (QRegExt.ofFin posCoreWires)) 1 =
      slotBitProj (wSlot2Core (QRegExt.ofFin posCoreWires)) 1 := by
  refine matrix_ext_of_ket fun β ↦ ?_
  rw [← Matrix.mulVec_mulVec, slotBitProj_one_mulVec_ket]
  by_cases hw2 : β (wSlot2Core (QRegExt.ofFin posCoreWires)) = 1
  · have hen0 : headEnBoolSpec β = false := by
      unfold headEnBoolSpec
      simp [hw2]
    have htail0 : tailAndSlackPhaseBitSpec slot2SwappedTo0 tailSign tailMag30 β = false := by
      unfold tailAndSlackPhaseBitSpec
      simp [hw2]
    rw [ite_eq_left hw2]
    dsimp only [uPosPhaseMod4]
    rw [ket_monomialZ8UnitaryN,
      show flipThClean (wHeadThresh (QRegExt.ofFin posCoreWires)) headEnBoolSpec β = β by
        unfold flipThClean flipTh
        simp [headEnBoolSpec_update_wHeadThresh, hen0]]
    simp [posPhaseMod4Z8Spec, headPhaseMod4Z8Spec, hen0, htail0]
  · rw [ite_eq_right hw2, Matrix.mulVec_zero]

theorem headEnRaw_eq_headEnBoolSpec {n : ℕ} (rCore : QRegister posCoreWires n)
    (γ : BitAssignment n) :
    (((γ (wSlot2Core rCore) == 0) && Bool.not (γ (wSlot1Core rCore) == 1) &&
      Bool.not (γ (wSubReject rCore) == 1) &&
      (decide (Bool.not (γ (wSlot0Core rCore) == 1) → regVal (rNucIdx rCore) γ < 216) &&
        decide (regVal (rAnchorIdx rCore) γ < 218)) &&
      (γ (wIsHead rCore) == 1))) = headEnBoolSpec (fun i ↦ γ (rCore i)) := by
  have hNuc : regVal (rNucIdx rCore) γ =
      regVal (rNucIdx (QRegExt.ofFin posCoreWires)) (fun i ↦ γ (rCore i)) := rfl
  have hAnc : regVal (rAnchorIdx rCore) γ =
      regVal (rAnchorIdx (QRegExt.ofFin posCoreWires)) (fun i ↦ γ (rCore i)) := rfl
  unfold headEnBoolSpec
  dsimp only
  rw [← hNuc, ← hAnc]
  rfl

set_option allowUnsafeReducibility true in
theorem diagonalSignUnitaryN_tail_mul_uHeadPhaseMod4 (slot2SwappedTo0 : Bool)
    (tailSign : Fin orbitCount47905 → Bool) (tailMag30 : Fin orbitCount47905 → Fin (2 ^ 30)) :
    diagonalSignUnitaryN (tailAndSlackPhaseBitSpec slot2SwappedTo0 tailSign tailMag30) *
      uHeadPhaseMod4 = uPosPhaseMod4 slot2SwappedTo0 tailSign tailMag30 := by
  apply Subtype.ext
  refine matrix_ext_of_ket fun β ↦ ?_
  rw [Submonoid.coe_mul, ← Matrix.mulVec_mulVec]
  dsimp only [uHeadPhaseMod4, uPosPhaseMod4]
  rw [ket_monomialZ8UnitaryN, Matrix.mulVec_smul, PosSlots24BranchConcrete.ket_diagonalSignUnitaryN,
    ket_monomialZ8UnitaryN, smul_smul,
    show tailAndSlackPhaseBitSpec slot2SwappedTo0 tailSign tailMag30
        (flipThClean (wHeadThresh (QRegExt.ofFin posCoreWires)) headEnBoolSpec β) =
      tailAndSlackPhaseBitSpec slot2SwappedTo0 tailSign tailMag30 β by
      unfold flipThClean flipTh
      split_ifs
      · exact tailAndSlackPhaseBitSpec_update_wHeadThresh slot2SwappedTo0 tailSign tailMag30 β _
      · rfl]
  congr 1
  unfold posPhaseMod4Z8Spec
  rw [omega8_zmod8_add]
  refine congrArg (omega8 ^ (headPhaseMod4Z8Spec β).val * ·) ?_
  cases tailAndSlackPhaseBitSpec slot2SwappedTo0 tailSign tailMag30 β
  · simp
  · simp only [↓reduceIte]
    exact omega8_pow_four.symm

end PosHeadMod4_15476
end
end ModPosHeadMod4_15476

end QuantumComputation.Specs.StoppingPowerSolution
