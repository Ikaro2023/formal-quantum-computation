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

public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.Slot3UnpackBlock0


@[expose] public section
set_option exponentiation.threshold 8192
set_option allowUnsafeReducibility true

namespace QuantumComputation.Specs.StoppingPowerSolution

section ModBiGqspVerifierCore
set_option maxRecDepth 250000
@[expose] public section
namespace BiGqspVerifierCoreAlt
theorem qreg_ext {k n : ℕ} {r s : QRegister k n} (h : ∀ i, r i = s i) : r = s :=
  QRegister.ext (Function.Embedding.ext h)
end BiGqspVerifierCoreAlt
namespace SpecsAux
open Operator
variable {Var : Type}
open SpecsAux.SpecMirror
attribute [reducible] Function.Injective Function.Involutive
@[simp] theorem matrix_star_eq_conjTranspose_compat {d : ℕ} (M : Operator d) :
    star M = Matrix.conjTranspose M := rfl
namespace GridStatesGuard
open Matrix QProg HermitianMat Circuit
open scoped Matrix ComplexOrder MatrixOrder QHLExpectation
variable {Var : Type}
section KetSemantics
variable {n k : ℕ}
@[simp] theorem basisBits_basisBitsEquiv_symm (q : ℕ) (β : BitAssignment q) : basisBits q
    ((basisBitsEquiv q).symm β) = β := (basisBitsEquiv q).apply_symm_apply β
@[simp] theorem basisBitsEquiv_symm_basisBits (q : ℕ) (j : Fin (2 ^ q)) :
    (basisBitsEquiv q).symm (basisBits q j) = j := (basisBitsEquiv q).symm_apply_apply j
end KetSemantics
section SeqRangeCombinator
@[simp] theorem count_seq {n a : ℕ} (p₁ p₂ : DynamicCircuit Var n) (g : PrimitiveGate a) :
    (DynamicCircuit.seq p₁ p₂).count g = p₁.count g + p₂.count g := rfl
end SeqRangeCombinator
end GridStatesGuard
end SpecsAux
local instance (priority := 1000000) instNeZeroTwoPowBiGqsp (k : Nat) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩
namespace PhaseGradSignalRot
open Operator Matrix Circuit Function SpecsAux
open SpecsAux.FullScaleBESector (phaseGradientState)
open scoped Matrix
variable {n k : ℕ}
noncomputable abbrev ket (β : BitAssignment n) : Fin (2 ^ n) → ℂ :=
  basisState ((basisBitsEquiv n).symm β)
@[simp] theorem basisBits_basisBitsEquiv_symm (q : ℕ) (β : BitAssignment q) : basisBits q
    ((basisBitsEquiv q).symm β) = β := (basisBitsEquiv q).apply_symm_apply β
@[simp] theorem basisBitsEquiv_symm_basisBits (q : ℕ) (j : Fin (2 ^ q)) :
    (basisBitsEquiv q).symm (basisBits q j) = j := (basisBitsEquiv q).symm_apply_apply j
theorem single_eq_ket (g : Fin (2 ^ n)) :
    (Pi.single g 1 : Fin (2 ^ n) → ℂ) = ket (basisBits n g) := by
  simp [ket]
noncomputable def writeReg (β : BitAssignment n) (r : QRegister k n) (γ : BitAssignment k) :
    BitAssignment n :=
  basisBits n (r.replaceIndex ((basisBitsEquiv n).symm β) ((basisBitsEquiv k).symm γ))
@[simp]
theorem writeReg_apply_reg (β : BitAssignment n) (r : QRegister k n) (γ : BitAssignment k)
    (i : Fin k) : writeReg β r γ (r i) = γ i := by
  simp [writeReg, QRegister.basisBits_replaceIndex_apply]
theorem writeReg_apply_of_not_mem (β : BitAssignment n) (r : QRegister k n) (γ : BitAssignment k)
    (w : Wire n) (hw : w ∉ Set.range r.wires) : writeReg β r γ w = β w := by
  simp [writeReg, QRegister.basisBits_replaceIndex_of_not_mem _ _ _ _ hw]
theorem writeReg_eq_update (β : BitAssignment n) (r : QRegister k n) (γ : BitAssignment k)
    (i₀ : Fin k) (hγ : ∀ i, i ≠ i₀ → γ i = β (r i)) :
    writeReg β r γ = Function.update β (r i₀) (γ i₀) := by
  funext w
  by_cases hw : w ∈ Set.range r.wires
  · rcases hw with ⟨i, rfl⟩
    rcases eq_or_ne i i₀ with rfl | hi
    · simp
    · rw [writeReg_apply_reg, Function.update_of_ne fun h ↦ hi (r.wires.injective h), hγ i hi]
  · rw [writeReg_apply_of_not_mem _ _ _ _ hw, Function.update_of_ne fun h ↦ hw ⟨i₀, h.symm⟩]
noncomputable abbrev localIdx (r : QRegister k n) (β : BitAssignment n) : Fin (2 ^ k) :=
  (basisBitsEquiv k).symm (fun i ↦ β (r i))
theorem embedMatrix_mulVec_ket (r : QRegister k n) (A : Matrix (Fin (2 ^ k)) (Fin (2 ^ k)) ℂ)
    (β : BitAssignment n) : (r.embedMatrix A).mulVec (ket β) = ∑ l : Fin (2 ^ k), A l
    (localIdx r β) • ket (writeReg β r (basisBits k l)) := by
  rw [ket, basisState, r.embedMatrix_mulVec_single_factors,
    show r.extractIndex ((basisBitsEquiv n).symm β) = localIdx r β by
      simp [QRegister.extractIndex],
    show A.mulVec (Pi.single (localIdx r β) 1) = ∑ l : Fin (2 ^ k), A l (localIdx r β) •
      Pi.single l 1 from funext fun _ ↦ by simp [Matrix.mulVec, dotProduct, Pi.single_apply],
    QRegister.tensorState_sum_left]
  refine Finset.sum_congr rfl fun l _ ↦ ?_
  rw [QRegister.tensorState_smul_left, QRegister.tensorState_single_replaceIndex]
  simp [writeReg, ket, basisState]
theorem embedMatrix_permMatrix_mulVec_ket (r : QRegister k n) (σ : Equiv.Perm (Fin (2 ^ k)))
    (β : BitAssignment n) : (r.embedMatrix (Equiv.Perm.permMatrix ℂ σ)).mulVec (ket β) = ket
    (writeReg β r (basisBits k (σ.symm (localIdx r β)))) := by
  rw [embedMatrix_mulVec_ket, Finset.sum_eq_single (σ.symm (localIdx r β))]
  · simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]
  · exact fun l _ hl ↦ by
      simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply,
        show σ l ≠ localIdx r β from fun h ↦ hl (by rw [← h, Equiv.symm_apply_apply])]
  · simp
theorem singleton_embedMatrix_mulVec_ket (q : Wire n) (A : Matrix (Fin 2) (Fin 2) ℂ)
    (β : BitAssignment n) : ((QRegister.singleton q).embedMatrix A).mulVec (ket β) = A 0
    (if β q = 0 then 0 else 1) • ket (Function.update β q 0) + A 1 (if β q = 0 then 0 else 1)
    • ket (Function.update β q 1) := by
  have hw (l : Fin 2) (b : ZMod 2) (hb : basisBits 1 l = fun _ ↦ b) :
      writeReg β (QRegister.singleton q) (basisBits 1 l) = Function.update β q b := by
    rw [writeReg_eq_update _ _ _ 0 fun i hi ↦ absurd (Subsingleton.elim i 0) hi, hb]
    rfl
  rw [embedMatrix_mulVec_ket, show localIdx (QRegister.singleton q) β =
    if β q = 0 then 0 else 1 from (by decide : ∀ b : ZMod 2,
      ((basisBitsEquiv 1).symm (fun _ ↦ b) : Fin 2) = if b = 0 then 0 else 1) (β q)]
  exact (Fin.sum_univ_two _).trans (by rw [hw 0 0 (by decide), hw 1 1 (by decide)])
theorem bit_cases (b : ZMod 2) : b = 0 ∨ b = 1 := (by decide : ∀ x : ZMod 2, x = 0 ∨ x = 1) b
theorem one_add_one_zmod2 : (1 : ZMod 2) + 1 = 0 := rfl
theorem ket_X (q : Wire n) (β : BitAssignment n) :
    (Circuit.X q).eval.1.mulVec (ket β) = ket (Function.update β q (β q + 1)) := by
  rw [Circuit.eval_single, QRegister.embedUnitary_val,
    show PrimitiveGate.X.eval.1 = Qubit.X.1 from rfl, singleton_embedMatrix_mulVec_ket]
  rcases bit_cases (β q) with hb | hb <;> simp [hb, Qubit.X]
theorem ket_CNOT (c t : Wire n) (h : c ≠ t) (β : BitAssignment n) :
    (Circuit.CNOT c t h).eval.1.mulVec (ket β) = ket (Function.update β t (β t + β c)) := by
  rw [Circuit.eval_gate, QRegister.embedUnitary_val, PrimitiveGate.eval_cnot_val,
    embedMatrix_permMatrix_mulVec_ket, localIdx,
    (by decide : ∀ γ : BitAssignment 2,
      basisBits 2 ((Equiv.swap (1 : Fin 4) 3).symm ((basisBitsEquiv 2).symm γ)) =
        Function.update γ 1 (γ 1 + γ 0)),
    writeReg_eq_update _ _ _ 1 fun _ hi ↦ by rw [Function.update_of_ne hi]]
  simp
theorem ket_TOFF (c₁ c₂ t : Wire n) (h₁₂ : c₁ ≠ c₂) (h₁t : c₁ ≠ t) (h₂t : c₂ ≠ t)
    (β : BitAssignment n) : (Circuit.TOFF c₁ c₂ t h₁₂ h₁t h₂t).eval.1.mulVec (ket β) = ket
    (Function.update β t (β t + β c₁ * β c₂)) := by
  rw [Circuit.eval_gate, QRegister.embedUnitary_val, PrimitiveGate.eval_toffoli_val,
    embedMatrix_permMatrix_mulVec_ket, localIdx,
    (by decide : ∀ γ : BitAssignment 3,
      basisBits 3 ((Equiv.swap (3 : Fin 8) 7).symm ((basisBitsEquiv 3).symm γ)) =
        Function.update γ 2 (γ 2 + γ 0 * γ 1)),
    writeReg_eq_update _ _ _ 2 fun _ hi ↦ by rw [Function.update_of_ne hi]]
  simp
inductive RevStep (n : ℕ) : Type where
  | x (q : Wire n)
  | cnot (c t : Wire n)
  | toff (c₁ c₂ t : Wire n)
namespace RevStep
def run : RevStep n → BitAssignment n → BitAssignment n
  | x q, β => update β q (β q + 1)
  | cnot c t, β => if c ≠ t then update β t (β t + β c) else β
  | toff c₁ c₂ t, β => if c₁ ≠ c₂ ∧ c₁ ≠ t ∧ c₂ ≠ t then update β t (β t + β c₁ * β c₂) else β
def toCircuit : RevStep n → Circuit n
  | x q => Circuit.X q
  | cnot c t => if h : c ≠ t then Circuit.CNOT c t h else .identity
  | toff c₁ c₂ t =>
      if h : c₁ ≠ c₂ ∧ c₁ ≠ t ∧ c₂ ≠ t then Circuit.TOFF c₁ c₂ t h.1 h.2.1 h.2.2 else .identity
def toffCount : RevStep n → ℕ
  | toff c₁ c₂ t => if c₁ ≠ c₂ ∧ c₁ ≠ t ∧ c₂ ≠ t then 1 else 0
  | _ => 0
theorem toffCount_le : ∀ s : RevStep n, s.toffCount ≤ 1
  | x _ => Nat.zero_le 1
  | cnot _ _ => Nat.zero_le 1
  | toff c₁ c₂ t =>
    if h : c₁ ≠ c₂ ∧ c₁ ≠ t ∧ c₂ ≠ t then by simp [toffCount, h] else by simp [toffCount, h]
@[simp] theorem toCircuit_count_T : ∀ s : RevStep n, s.toCircuit.count PrimitiveGate.T = 0
  | x _ => rfl
  | cnot c t => if h : c ≠ t then by simp [toCircuit, h] else by simp [toCircuit, h]
  | toff c₁ c₂ t =>
    if h : c₁ ≠ c₂ ∧ c₁ ≠ t ∧ c₂ ≠ t then by simp [toCircuit, h] else by simp [toCircuit, h]
@[simp] theorem toCircuit_count_TOFF :
    ∀ s : RevStep n, s.toCircuit.count PrimitiveGate.TOFF = s.toffCount
  | x _ => rfl
  | cnot c t =>
    if h : c ≠ t then by simp [toCircuit, toffCount, h] else by simp [toCircuit, toffCount, h]
  | toff c₁ c₂ t =>
    if h : c₁ ≠ c₂ ∧ c₁ ≠ t ∧ c₂ ≠ t then by simp [toCircuit, toffCount, h]
    else by simp [toCircuit, toffCount, h]
@[simp] theorem run_idem (s : RevStep n) (β : BitAssignment n) : s.run (s.run β) = β := by
  have hz (x y : ZMod 2) : x + y + y = x := by rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
  cases s with
  | x q => simp [run, update_self, update_idem, hz]
  | cnot c t =>
    exact if h : c ≠ t then by simp [run, h, update_self, update_idem, hz]
    else by simp [run, h]
  | toff c₁ c₂ t =>
    exact if h : c₁ ≠ c₂ ∧ c₁ ≠ t ∧ c₂ ≠ t then by simp [run, h, update_self, update_idem, hz]
    else by simp [run, h]
end RevStep
def runRevList : List (RevStep n) → BitAssignment n → BitAssignment n
  | [], β => β
  | s :: ss, β => runRevList ss (s.run β)
@[simp] theorem runRevList_nil (β : BitAssignment n) : runRevList [] β = β := rfl
@[simp]
theorem runRevList_cons (s : RevStep n) (ss : List (RevStep n)) (β : BitAssignment n) :
    runRevList (s :: ss) β = runRevList ss (s.run β) := rfl
@[simp] theorem runRevList_append : ∀ (ss ts : List (RevStep n)) (β : BitAssignment n),
      runRevList (ss ++ ts) β = runRevList ts (runRevList ss β)
  | [], _, _ => rfl
  | s :: ss, ts, β => runRevList_append ss ts (s.run β)
@[simp] theorem runRevList_reverse :
    ∀ (ss : List (RevStep n)) (β : BitAssignment n), runRevList ss.reverse (runRevList ss β) = β
  | [], _ => rfl
  | s :: ss, β => by simp [List.reverse_cons, runRevList_append, runRevList_reverse ss]
def compileRevList : List (RevStep n) → Circuit n
  | [] => .identity
  | s :: ss => s.toCircuit.seq (compileRevList ss)
@[simp] theorem compileRevList_count_T :
    ∀ ss : List (RevStep n), (compileRevList ss).count PrimitiveGate.T = 0
  | [] => rfl
  | _ :: ss => by simp [compileRevList, compileRevList_count_T ss]
@[simp] theorem compileRevList_count_TOFF : ∀ ss : List (RevStep n),
      (compileRevList ss).count PrimitiveGate.TOFF = (ss.map RevStep.toffCount).sum
  | [] => rfl
  | _ :: ss => by simp [compileRevList, compileRevList_count_TOFF ss]
theorem compileRevList_mulVec_ket (ss : List (RevStep n)) (β : BitAssignment n) :
    (compileRevList ss).eval.1.mulVec (ket β) = ket (runRevList ss β) := by
  induction ss generalizing β with
  | nil => simp [compileRevList]
  | cons s ss ih =>
    rw [compileRevList, Circuit.eval_seq, Submonoid.coe_mul, ← Matrix.mulVec_mulVec,
      runRevList_cons, ← ih]
    congr 1
    cases s with
    | x q => exact ket_X q β
    | cnot c t =>
      by_cases h : c ≠ t
      · simpa [RevStep.toCircuit, RevStep.run, h] using ket_CNOT c t h β
      · simp [RevStep.toCircuit, RevStep.run, h]
    | toff c₁ c₂ t =>
      by_cases h : c₁ ≠ c₂ ∧ c₁ ≠ t ∧ c₂ ≠ t
      · simpa [RevStep.toCircuit, RevStep.run, h] using ket_TOFF c₁ c₂ t h.1 h.2.1 h.2.2 β
      · simp [RevStep.toCircuit, RevStep.run, h]
@[simp] theorem writeReg_writeReg (β : BitAssignment n) (r : QRegister k n)
    (γ γ' : BitAssignment k) : writeReg (writeReg β r γ) r γ' = writeReg β r γ' := by
  simp [writeReg]
@[simp] theorem localIdx_writeReg_self {k : ℕ} (r : QRegister k n) (β : BitAssignment n)
    (m : Fin (2 ^ k)) : localIdx r (writeReg β r (basisBits k m)) = m := by
  rw [localIdx, show (fun i ↦ writeReg β r (basisBits k m) (r i)) = basisBits k m
    from funext (writeReg_apply_reg β r (basisBits k m))]
  exact (basisBitsEquiv k).symm_apply_apply m
def CtrlNe (c : Option (Wire n)) (w : Wire n) : Prop := ∀ c₀, c = some c₀ → c₀ ≠ w
theorem CtrlNe.some {a w : Wire n} (h : a ≠ w) : CtrlNe (some a) w :=
  fun _ h' ↦ Option.some.inj h' ▸ h
section SingleQubitRotations
def ryMatrix (c s : ℝ) : Operator 2 :=
  (c : ℂ) • (1 : Operator 2) + (s : ℂ) • (Qubit.X.1 * Qubit.Z.1)
theorem ryMatrix_conjTranspose_mul_self (c s : ℝ) :
    (ryMatrix c s)ᴴ * ryMatrix c s = ((c ^ 2 + s ^ 2 : ℝ) : ℂ) • (1 : Operator 2) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ryMatrix, Qubit.X, Qubit.Z, Matrix.mul_apply, Fin.sum_univ_two, Complex.conj_ofReal] <;>
    ring
noncomputable def ryUnitary (θ : ℝ) : Unitary 2 :=
  ⟨ryMatrix (Real.cos (θ / 2)) (Real.sin (θ / 2)), by
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose,
      ryMatrix_conjTranspose_mul_self, Real.cos_sq_add_sin_sq, Complex.ofReal_one, one_smul]⟩
@[simp] theorem ryUnitary_val (θ : ℝ) :
    (ryUnitary θ).1 = ryMatrix (Real.cos (θ / 2)) (Real.sin (θ / 2)) := rfl
noncomputable def rzDiagMatrix (α : ℝ) : Operator 2 :=
  Matrix.diagonal ![Complex.exp ((α : ℂ) * Complex.I), Complex.exp (-((α : ℂ) * Complex.I))]
theorem rzDiagMatrix_eq_cos_add_sin_iZ (α : ℝ) : rzDiagMatrix α = (Real.cos α : ℂ) •
    (1 : Operator 2) + (Real.sin α : ℂ) • (Complex.I • Qubit.Z.1) := by
  ext i j
  fin_cases i
  · fin_cases j
    · simp [rzDiagMatrix, Qubit.Z, Complex.exp_mul_I]
    · simp [rzDiagMatrix, Qubit.Z]
  · fin_cases j
    · simp [rzDiagMatrix, Qubit.Z]
    · simp [rzDiagMatrix, Qubit.Z, ← neg_mul, Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg]
noncomputable def twoPhaseDiagMatrix (b θ₀ θ₁ : ℕ) : Operator 2 := Matrix.diagonal ![
    Complex.exp ((2 * Real.pi * Complex.I * (θ₀ : ℂ)) / 2 ^ b), Complex.exp ((2 * Real.pi *
    Complex.I * (θ₁ : ℂ)) / 2 ^ b) ]
noncomputable def twoPhaseDiagUnitary (b θ₀ θ₁ : ℕ) : Unitary 2 :=
  ⟨twoPhaseDiagMatrix b θ₀ θ₁, by
    have hexp (θ : ℕ) : star (Complex.exp ((2 * Real.pi * Complex.I * (θ : ℂ)) / 2 ^ b)) *
        Complex.exp ((2 * Real.pi * Complex.I * (θ : ℂ)) / 2 ^ b) = 1 := by
      rw [Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add]
      convert Complex.exp_zero
      simp only [map_div₀, map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I,
        map_natCast, map_pow]
      ring
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, twoPhaseDiagMatrix,
      Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    refine congrArg Matrix.diagonal (funext fun i ↦ ?_)
    fin_cases i
    · exact hexp θ₀
    · exact hexp θ₁⟩
theorem twoPhaseDiagMatrix_sym (b C : ℕ) (hC : C ≤ 2 ^ b) :
    twoPhaseDiagMatrix b C (2 ^ b - C) = rzDiagMatrix ((2 * Real.pi * (C : ℝ)) / 2 ^ b) := by
  refine congrArg Matrix.diagonal (funext fun i ↦ ?_)
  fin_cases i
  · simp only [Fin.zero_eta, Matrix.cons_val_zero]
    push_cast
    exact congrArg Complex.exp (by ring)
  · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
    rw [show (2 * (Real.pi : ℂ) * Complex.I * ((2 ^ b - C : ℕ) : ℂ)) / (2 : ℂ) ^ b =
        2 * (Real.pi : ℂ) * Complex.I +
          -((2 * (Real.pi : ℂ) * (C : ℂ) / (2 : ℂ) ^ b) * Complex.I) by
      rw [Nat.cast_sub hC, Nat.cast_pow, Nat.cast_ofNat]
      field_simp [pow_ne_zero b (two_ne_zero' ℂ)]
      ring, Complex.exp_add, show Complex.exp (2 * Real.pi * Complex.I) = 1 by simp, one_mul]
    push_cast
    rfl
theorem sH_conj_rzDiagMatrix (α : ℝ) : (Qubit.S.1 * Qubit.H.1) * rzDiagMatrix α *
    (Qubit.H.1 * (Qubit.Z.1 * Qubit.S.1)) = (ryUnitary (-(2 * α))).1 := by
  have hsH1 : (Qubit.S.1 * Qubit.H.1) * (Qubit.H.1 * (Qubit.Z.1 * Qubit.S.1)) = 1 :=
    congrArg Subtype.val (show Qubit.S * Qubit.H * (Qubit.H * (Qubit.Z * Qubit.S)) = 1 by
      rw [mul_assoc Qubit.S, ← mul_assoc Qubit.H, Qubit.H_sq, one_mul, Qubit.Z_mul_S_eq_S_inv,
        mul_inv_cancel])
  have hsHiZ : (Qubit.S.1 * Qubit.H.1) * (Complex.I • Qubit.Z.1) *
      (Qubit.H.1 * (Qubit.Z.1 * Qubit.S.1)) = -(Qubit.X.1 * Qubit.Z.1) := by
    rw [show (Qubit.S.1 * Qubit.H.1) * (Complex.I • Qubit.Z.1) *
        (Qubit.H.1 * (Qubit.Z.1 * Qubit.S.1)) =
      Qubit.S.1 * (Complex.I • (Qubit.H.1 * Qubit.Z.1 * Qubit.H.1)) * (Qubit.Z.1 * Qubit.S.1) by
        simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc],
      show Qubit.H.1 * Qubit.Z.1 * Qubit.H.1 = Qubit.X.1 from congrArg Subtype.val
        (show Qubit.H * Qubit.Z * Qubit.H = Qubit.X by
          rw [Qubit.H_mul_Z_eq_X_mul_H, mul_assoc, Qubit.H_sq, mul_one])]
    refine Matrix.ext fun i j ↦ ?_
    fin_cases i
    · fin_cases j
      · simp [Qubit.Z, Qubit.S, Qubit.X, Matrix.mul_apply, Fin.sum_univ_two]
      · simp [Qubit.Z, Qubit.S, Qubit.X, Matrix.mul_apply, Fin.sum_univ_two]
    · fin_cases j
      · simp [Qubit.Z, Qubit.S, Qubit.X, Matrix.mul_apply, Fin.sum_univ_two]
      · simp [Qubit.Z, Qubit.S, Qubit.X, Matrix.mul_apply, Fin.sum_univ_two]
  rw [ryUnitary_val, show -(2 * α) / 2 = -α by ring, Real.cos_neg, Real.sin_neg,
    rzDiagMatrix_eq_cos_add_sin_iZ, ryMatrix, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul,
    Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hsH1, hsHiZ,
    Complex.ofReal_neg, neg_smul, smul_neg]
end SingleQubitRotations
section CatalystAndKickback
def IntertwinesCat {N : ℕ} (U_cat P_Cat0 M_cat M_eff : Operator N) : Prop := M_cat * U_cat *
    P_Cat0 = U_cat * M_eff * P_Cat0 ∧ M_eff * U_cat = U_cat * M_eff ∧ M_eff * P_Cat0 = P_Cat0
    * M_eff
theorem IntertwinesCat.refl_of_comm {N : ℕ} {U_cat P_Cat0 M : Operator N}
    (hU : M * U_cat = U_cat * M) (hP : M * P_Cat0 = P_Cat0 * M) :
    IntertwinesCat U_cat P_Cat0 M M := ⟨by rw [hU], hU, hP⟩
theorem IntertwinesCat.mul {N : ℕ} {U_cat P_Cat0 A_cat A_eff B_cat B_eff : Operator N}
    (hA : IntertwinesCat U_cat P_Cat0 A_cat A_eff) (hB : IntertwinesCat U_cat P_Cat0 B_cat B_eff) :
    IntertwinesCat U_cat P_Cat0 (A_cat * B_cat) (A_eff * B_eff) :=
  ⟨by calc (A_cat * B_cat) * U_cat * P_Cat0
        _ = A_cat * (B_cat * U_cat * P_Cat0) := by simp only [Matrix.mul_assoc]
        _ = A_cat * U_cat * (P_Cat0 * B_eff) := by
            rw [hB.1, ← hB.2.2]
            simp only [Matrix.mul_assoc]
        _ = (A_cat * U_cat * P_Cat0) * B_eff := by simp only [Matrix.mul_assoc]
        _ = U_cat * (A_eff * B_eff) * P_Cat0 := by
            rw [hA.1, Matrix.mul_assoc (U_cat * A_eff), ← hB.2.2]
            simp only [Matrix.mul_assoc],
   by rw [Matrix.mul_assoc, hB.2.1, ← Matrix.mul_assoc, hA.2.1, Matrix.mul_assoc],
   by rw [Matrix.mul_assoc, hB.2.2, ← Matrix.mul_assoc, hA.2.2, Matrix.mul_assoc]⟩
def modAddPerm (b θ : ℕ) : Equiv.Perm (Fin (2 ^ b)) where
  toFun m := ⟨(m.val + θ) % 2 ^ b, Nat.mod_lt _ (Nat.two_pow_pos b)⟩
  invFun m := ⟨(m.val + (2 ^ b - θ % 2 ^ b)) % 2 ^ b, Nat.mod_lt _ (Nat.two_pow_pos b)⟩
  left_inv m := by
    ext
    dsimp only
    rw [← Nat.add_mod_mod m.val θ (2 ^ b), Nat.mod_add_mod, Nat.add_assoc,
      Nat.add_sub_of_le (Nat.mod_lt θ (Nat.two_pow_pos b)).le, Nat.add_mod_right,
      Nat.mod_eq_of_lt m.isLt]
  right_inv m := by
    ext
    dsimp only
    rw [Nat.mod_add_mod, ← Nat.add_mod_mod (m.val + (2 ^ b - θ % 2 ^ b)) θ (2 ^ b),
      Nat.add_assoc, Nat.sub_add_cancel (Nat.mod_lt θ (Nat.two_pow_pos b)).le,
      Nat.add_mod_right, Nat.mod_eq_of_lt m.isLt]
noncomputable def modAddUnitary (b θ : ℕ) : Unitary (2 ^ b) :=
  Operator.permutationUnitary (modAddPerm b θ)
theorem modAddUnitary_mulVec_phaseGradientState (b θ : ℕ) :
    (modAddUnitary b θ).1.mulVec (phaseGradientState b) =
      Complex.exp ((2 * Real.pi * Complex.I * (θ : ℂ)) / 2 ^ b) • phaseGradientState b := by
  ext y
  change (Equiv.Perm.permMatrix ℂ ((modAddPerm b θ)⁻¹)).mulVec (phaseGradientState b) y =
    Complex.exp ((2 * Real.pi * Complex.I * (θ : ℂ)) / 2 ^ b) * phaseGradientState b y
  rw [Matrix.permMatrix_mulVec]
  dsimp only [Function.comp_apply, Equiv.Perm.inv_def]
  let x := (modAddPerm b θ).symm y
  let q := (x.val + θ) / 2 ^ b
  have hdiv : y.val + 2 ^ b * q = x.val + θ := by
    rw [← congrArg Fin.val ((modAddPerm b θ).apply_symm_apply y)]
    exact Nat.mod_add_div (x.val + θ) (2 ^ b)
  have hexp_split : -(2 * Real.pi * Complex.I * (x.val : ℂ)) / 2 ^ b =
      ((2 * Real.pi * Complex.I * (θ : ℂ)) / 2 ^ b +
        (-(2 * Real.pi * Complex.I * (y.val : ℂ)) / 2 ^ b)) +
      Int.cast (-(q : ℤ)) * (2 * Real.pi * Complex.I) := by
    have hdivC : ((y.val + 2 ^ b * q : ℕ) : ℂ) = ((x.val + θ : ℕ) : ℂ) := congrArg Nat.cast hdiv
    push_cast at hdivC ⊢
    rw [show (x.val : ℂ) = (y.val : ℂ) - (θ : ℂ) + (2 : ℂ) ^ b * (q : ℂ) by
      linear_combination -hdivC]
    field_simp [pow_ne_zero b (two_ne_zero' ℂ)]
    ring
  change phaseGradientState b x = _
  dsimp only [phaseGradientState]
  rw [hexp_split, Complex.exp_add, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  ring
theorem matrix_ext_ket {A B : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ}
    (h : ∀ β : BitAssignment n, A.mulVec (ket β) = B.mulVec (ket β)) : A = B := by
  ext i j
  simpa [← single_eq_ket, Matrix.mulVec_single_one] using congrFun (h (basisBits n j)) i
theorem basisOutcomeProjector_zero_mulVec_ket {m : ℕ} (rAnc : QRegister m n)
    (β : BitAssignment n) : (rAnc.basisOutcomeProjector 0).mulVec (ket β) = if localIdx rAnc β
    = 0 then ket β else 0 := by
  have hext : rAnc.extractIndex ((basisBitsEquiv n).symm β) = localIdx rAnc β := by
    simp [QRegister.extractIndex, localIdx]
  rw [QRegister.basisOutcomeProjector_eq_diagonal]
  funext i
  simp only [ket, basisState, Matrix.mulVec, dotProduct, Matrix.diagonal_apply, Pi.single_apply,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  rcases eq_or_ne i ((basisBitsEquiv n).symm β) with rfl | hi
  · by_cases h : localIdx rAnc β = 0 <;> simp [hext, h]
  · simp [apply_ite (fun f : Fin (2 ^ n) → ℂ ↦ f i), hi]
theorem apply_eq_zero_of_localIdx_eq_zero {m : ℕ} (r : QRegister m n) (β : BitAssignment n)
    (h0 : localIdx r β = 0) (i : Fin m) : β (r i) = 0 := by
  have hbits := congrArg (basisBits m) h0
  rw [basisBits_basisBitsEquiv_symm] at hbits
  have hi := congrFun hbits i
  simpa [-Nat.reducePow, basisBits_eq_div_mod] using hi
theorem singleton_embedMatrix_twoPhaseDiagMatrix_mulVec_ket (q_sig : Wire n) (b θ₀ θ₁ : ℕ)
    (β : BitAssignment n) : ((QRegister.singleton q_sig).embedMatrix (twoPhaseDiagMatrix b θ₀
    θ₁)).mulVec (ket β) = Complex.exp ((2 * Real.pi * Complex.I * ((if β q_sig = 0 then θ₀
    else θ₁ : ℕ) : ℂ)) / 2 ^ b) • ket β := by
  rw [singleton_embedMatrix_mulVec_ket]
  rcases bit_cases (β q_sig) with h0 | h1
  · simp [twoPhaseDiagMatrix, h0,
      show Function.update β q_sig 0 = β by rw [← h0, update_eq_self]]
  · simp [twoPhaseDiagMatrix, h1, one_ne_zero,
      show Function.update β q_sig 1 = β by rw [← h1, update_eq_self]]
theorem intertwinesCat_singleton_q_sig (q_sig : Wire n) (rCat : QRegister 42 n)
    (P_Scratch0 : Operator (2 ^ n)) (hSigCat : (QRegister.singleton q_sig).DisjointWires rCat)
    (hSigScratch_comm : ∀ M : Operator 2, (QRegister.singleton q_sig).embedMatrix M * P_Scratch0 =
        P_Scratch0 * (QRegister.singleton q_sig).embedMatrix M)
    (U_cat_0 : Unitary (2 ^ 42)) (U_loc : Unitary 2) :
    let P_Joint0 := rCat.basisOutcomeProjector 0 * P_Scratch0
    IntertwinesCat (rCat.embedUnitary U_cat_0).1 P_Joint0
      ((QRegister.singleton q_sig).embedUnitary U_loc).1
      ((QRegister.singleton q_sig).embedUnitary U_loc).1 := by
  intro P_Joint0
  let rSig := QRegister.singleton q_sig
  have hU : rSig.embedMatrix U_loc.1 * (rCat.embedUnitary U_cat_0).1 =
      (rCat.embedUnitary U_cat_0).1 * rSig.embedMatrix U_loc.1 :=
    rSig.embedMatrix_comm_of_disjoint rCat hSigCat U_loc.1 U_cat_0.1
  have hCat0 : rSig.embedMatrix U_loc.1 * rCat.basisOutcomeProjector 0 =
      rCat.basisOutcomeProjector 0 * rSig.embedMatrix U_loc.1 :=
    rSig.embedMatrix_comm_of_disjoint rCat hSigCat U_loc.1 (compProj 0)
  have hJoint : rSig.embedMatrix U_loc.1 * P_Joint0 = P_Joint0 * rSig.embedMatrix U_loc.1 := by
    dsimp only [P_Joint0]
    rw [← Matrix.mul_assoc, hCat0, Matrix.mul_assoc, hSigScratch_comm U_loc.1, ← Matrix.mul_assoc]
  exact IntertwinesCat.refl_of_comm hU hJoint
theorem embedUnitary_mul_val {m : ℕ} (r : QRegister m n) (A B : Unitary (2 ^ m)) :
    (r.embedUnitary (A * B)).1 = (r.embedUnitary A).1 * (r.embedUnitary B).1 := by
  rw [r.embedUnitary_mul, Submonoid.coe_mul]
end CatalystAndKickback
section SymmetricSignalRot
def trailingZeros42Aux : ℕ → ℕ → ℕ
  | 0, _ => 0
  | fuel + 1, c =>
    if c = 0 then fuel + 1 else if c % 2 = 0 then 1 + trailingZeros42Aux fuel (c / 2) else 0
def trailingZeros42 (c : ℕ) : ℕ := trailingZeros42Aux 42 c
def activeMsbWidth42 (c : ℕ) : ℕ := 42 - trailingZeros42 c
theorem trailingZeros42Aux_le : ∀ fuel c, trailingZeros42Aux fuel c ≤ fuel
  | 0, _ => le_rfl
  | fuel + 1, c => by
    unfold trailingZeros42Aux
    split_ifs
    · exact le_rfl
    · have := trailingZeros42Aux_le fuel (c / 2)
      omega
    · omega
theorem trailingZeros42_le_42 (c : ℕ) : trailingZeros42 c ≤ 42 := trailingZeros42Aux_le 42 c
theorem two_pow_trailingZeros42_dvd (c : ℕ) : 2 ^ trailingZeros42 c ∣ c := by
  suffices h : ∀ fuel x, 2 ^ trailingZeros42Aux fuel x ∣ x from h 42 c
  intro fuel
  induction fuel with
  | zero => exact fun _ ↦ by simp [trailingZeros42Aux]
  | succ fuel ih =>
    intro x
    unfold trailingZeros42Aux
    split_ifs with h0 hmod
    · exact h0 ▸ dvd_zero _
    · rcases Nat.dvd_of_mod_eq_zero hmod with ⟨x', rfl⟩
      rw [Nat.mul_div_cancel_left x' (by positivity), Nat.pow_add, pow_one]
      exact Nat.mul_dvd_mul_left 2 (ih x')
    · simp
theorem add_mul_pow_mod_split {W : ℕ} (m_val θ_sub k b : ℕ) (hk : k + b = W) :
    (m_val + 2 ^ k * θ_sub) % 2 ^ W =
      m_val % 2 ^ k + 2 ^ k * ((m_val / 2 ^ k + θ_sub) % 2 ^ b) := by
  have h2W : 2 ^ W = 2 ^ k * 2 ^ b := by rw [← hk, Nat.pow_add]
  let r := m_val % 2 ^ k
  let q := (m_val / 2 ^ k + θ_sub) % 2 ^ b
  let p := (m_val / 2 ^ k + θ_sub) / 2 ^ b
  have hm_eq : r + 2 ^ k * (m_val / 2 ^ k) = m_val := Nat.mod_add_div m_val (2 ^ k)
  have hq_eq : q + 2 ^ b * p = m_val / 2 ^ k + θ_sub := Nat.mod_add_div _ (2 ^ b)
  have hr_lt : r < 2 ^ k := Nat.mod_lt m_val (Nat.two_pow_pos k)
  have hq_lt : q < 2 ^ b := Nat.mod_lt _ (Nat.two_pow_pos b)
  rw [show m_val + 2 ^ k * θ_sub = (r + 2 ^ k * q) + 2 ^ W * p by nlinarith,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by nlinarith)]
end SymmetricSignalRot
end PhaseGradSignalRot
namespace TFreeLaurentGQSP
open Operator Matrix Circuit SpecsAux
open SpecsAux.FullScaleBESector (IsQubitizedBlockEncodingUnitary)
open scoped Matrix
def chebT {R : Type*} [Ring R] : ℕ → R → R
  | 0, _ => 1
  | 1, X => X
  | k + 2, X => 2 * X * chebT (k + 1) X - chebT k X
@[simp] theorem chebT_zero {R : Type*} [Ring R] (X : R) : chebT 0 X = 1 := rfl
@[simp] theorem chebT_one {R : Type*} [Ring R] (X : R) : chebT 1 X = X := rfl
theorem chebT_add_two {R : Type*} [Ring R] (k : ℕ) (X : R) :
    chebT (k + 2) X = 2 * X * chebT (k + 1) X - chebT k X := rfl
theorem comm_chebT {R : Type*} [Ring R] (k : ℕ) (X : R) : X * chebT k X = chebT k X * X := by
  induction k using Nat.strong_induction_on with
  | h n ih =>
    rcases n with _ | _ | k
    · simp
    · simp
    · rw [chebT_add_two, show X * (2 * X * chebT (k + 1) X - chebT k X) =
            2 * X * (X * chebT (k + 1) X) - X * chebT k X by noncomm_ring,
          ih (k + 1) (by omega), ih k (by omega)]
      noncomm_ring
theorem embedMatrix_chebT {k n : ℕ} (r : QRegister k n) (m : ℕ) (X : Operator (2 ^ k)) :
    r.embedMatrix (chebT m X) = chebT m (r.embedMatrix X) := by
  induction m using Nat.strong_induction_on with
  | h d ih =>
    rcases d with _ | _ | d
    · simp
    · simp
    · rw [chebT_add_two, chebT_add_two, sub_eq_add_neg, ← neg_one_smul ℂ (chebT d X),
        r.embedMatrix_add, r.embedMatrix_smul, neg_one_smul, ← sub_eq_add_neg, r.embedMatrix_mul,
        r.embedMatrix_mul, show (2 : Operator (2 ^ k)) = 1 + 1 from one_add_one_eq_two.symm,
        r.embedMatrix_add, r.embedMatrix_one, one_add_one_eq_two,
        ih (d + 1) (by omega), ih d (by omega)]
noncomputable def szegedyRefl (k m : ℕ) : Operator (2 ^ (k + m)) :=
  let P_anc := (QRegister.block k m le_rfl : QRegister m (k + m)).basisOutcomeProjector 0
  2 * P_anc - 1
noncomputable def szegedyWalk {k m : ℕ} (U_BE : Unitary (2 ^ (k + m))) : Operator (2 ^ (k + m)) :=
  szegedyRefl k m * U_BE.1
noncomputable def szegedyWalkInv {k m : ℕ} (U_BE : Unitary (2 ^ (k + m))) : Operator (2 ^ (k +
    m)) :=
  U_BE.1 * szegedyRefl k m
theorem qubitized_mul_self {k m : ℕ} {α : ℝ} {A : Operator (2 ^ k)}
    {U_BE : Unitary (2 ^ (k + m))} (hBE : IsQubitizedBlockEncodingUnitary α A U_BE) :
    U_BE.1 * U_BE.1 = 1 :=
  (congrArg (· * U_BE.1) hBE.2.1.symm).trans (Matrix.star_eq_conjTranspose U_BE.1 ▸ U_BE.2.1)
theorem szegedyRefl_mul_self (k m : ℕ) : szegedyRefl k m * szegedyRefl k m = 1 := by
  unfold szegedyRefl
  let P := (QRegister.block k m le_rfl : QRegister m (k + m)).basisOutcomeProjector 0
  rw [show (2 * P - 1) * (2 * P - 1) = 4 * (P * P) - 4 * P + 1 by noncomm_ring,
    (QRegister.block k m le_rfl).basisOutcomeProjector_mul_self 0]
  noncomm_ring
theorem chebWalk_blockEncoding {k m : ℕ} {α : ℝ} {A : Operator (2 ^ k)}
    {U_BE : Unitary (2 ^ (k + m))} (hBE : IsQubitizedBlockEncodingUnitary α A U_BE) (d : ℕ) :
    let sys : QRegister k (k + m) := QRegister.block 0 k (by omega)
    let anc : QRegister m (k + m) := QRegister.block k m le_rfl
    let P_anc := anc.basisOutcomeProjector 0
    let Q := szegedyWalk U_BE
    P_anc * Q ^ d * P_anc = sys.embedMatrix (chebT d ((α : ℂ)⁻¹ • A)) * P_anc := by
  intro sys anc P_anc Q
  set X : Operator (2 ^ k) := (α : ℂ)⁻¹ • A
  set S : Operator (2 ^ (k + m)) := sys.embedMatrix X
  have hdisj : sys.DisjointWires anc :=
    QRegister.block_disjoint_of_le 0 k k m (by omega) le_rfl (by omega)
  have hSP : S * P_anc = P_anc * S := sys.embedMatrix_comm_of_disjoint anc hdisj X (compProj 0)
  have hP_idem : P_anc * P_anc = P_anc := anc.basisOutcomeProjector_mul_self 0
  have hU_sq : U_BE.1 * U_BE.1 = 1 := qubitized_mul_self hBE
  have hPUP : P_anc * U_BE.1 * P_anc = S * P_anc := by
    have hblock : P_anc * U_BE.1 * P_anc = (α : ℂ)⁻¹ • (P_anc * sys.embedMatrix A * P_anc) :=
      hBE.2.2
    have hcommA : sys.embedMatrix A * P_anc = P_anc * sys.embedMatrix A :=
      sys.embedMatrix_comm_of_disjoint anc hdisj A (compProj 0)
    rw [hblock, ← hcommA, Matrix.mul_assoc, hP_idem, ← smul_mul_assoc, ← sys.embedMatrix_smul]
  have hQUP' : Q * U_BE.1 * P_anc = P_anc := by
    rw [show Q * U_BE.1 * P_anc = (2 * P_anc - 1) * (U_BE.1 * U_BE.1) * P_anc by
        dsimp [Q, szegedyWalk, szegedyRefl]
        noncomm_ring,
      hU_sq, mul_one, sub_mul, Matrix.mul_assoc, hP_idem]
    noncomm_ring
  have hQP : Q * P_anc = 2 * S * P_anc - U_BE.1 * P_anc := by
    rw [show Q * P_anc = 2 * (P_anc * U_BE.1 * P_anc) - U_BE.1 * P_anc by
        dsimp [Q, szegedyWalk, szegedyRefl]
        noncomm_ring, hPUP]
    noncomm_ring
  have hQ2P : Q ^ 2 * P_anc = 2 * Q * S * P_anc - P_anc := by
    rw [sq, Matrix.mul_assoc, hQP, mul_sub, ← Matrix.mul_assoc Q U_BE.1, hQUP']
    noncomm_ring
  have hrec (n : ℕ) : P_anc * Q ^ (n + 2) * P_anc =
      2 * (P_anc * Q ^ (n + 1) * P_anc) * S - P_anc * Q ^ n * P_anc := by
    rw [pow_add Q n 2, show P_anc * (Q ^ n * Q ^ 2) * P_anc =
        P_anc * Q ^ n * (Q ^ 2 * P_anc) by noncomm_ring, hQ2P,
      show P_anc * Q ^ n * (2 * Q * S * P_anc - P_anc) =
        2 * (P_anc * (Q ^ n * Q) * (S * P_anc)) - P_anc * Q ^ n * P_anc by noncomm_ring,
      ← pow_succ Q n, hSP]
    noncomm_ring
  have hind (n : ℕ) : P_anc * Q ^ n * P_anc = chebT n S * P_anc := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      rcases n with _ | _ | n
      · simp [hP_idem]
      · rw [Nat.zero_add, pow_one, chebT_one, Matrix.mul_assoc, hQP,
          show P_anc * (2 * S * P_anc - U_BE.1 * P_anc) =
            2 * (P_anc * S) * P_anc - P_anc * U_BE.1 * P_anc by noncomm_ring,
          ← hSP, hPUP,
          show 2 * (S * P_anc) * P_anc - S * P_anc =
            2 * S * (P_anc * P_anc) - S * P_anc by noncomm_ring, hP_idem]
        noncomm_ring
      · rw [hrec n, ih (n + 1) (by omega), ih n (by omega), chebT_add_two,
          show 2 * (chebT (n + 1) S * P_anc) * S - chebT n S * P_anc =
            2 * chebT (n + 1) S * (P_anc * S) - chebT n S * P_anc by noncomm_ring,
          ← hSP, show 2 * chebT (n + 1) S * (S * P_anc) =
            2 * (chebT (n + 1) S * S) * P_anc by noncomm_ring,
          (comm_chebT (n + 1) S).symm]
        noncomm_ring
  rw [hind d, ← embedMatrix_chebT]
noncomputable def laurentWalk {k m : ℕ} (U_BE : Unitary (2 ^ (k + m))) : Operator (2 ^ (k + m)) :=
  Complex.I • szegedyWalk U_BE
noncomputable def laurentWalkInv {k m : ℕ} (U_BE : Unitary (2 ^ (k + m))) : Operator (2 ^ (k +
    m)) :=
  (-Complex.I) • szegedyWalkInv U_BE
theorem laurentWalk_pow {k m : ℕ} (U_BE : Unitary (2 ^ (k + m))) (d : ℕ) : (laurentWalk U_BE)
    ^ d = (Complex.I ^ d) • (szegedyWalk U_BE) ^ d := smul_pow _ _ d
theorem laurentWalkInv_pow {k m : ℕ} (U_BE : Unitary (2 ^ (k + m))) (d : ℕ) :
    (laurentWalkInv U_BE) ^ d = ((-Complex.I) ^ d) • (szegedyWalkInv U_BE) ^ d := smul_pow _ _ d
theorem szegedyRefl_mem_unitaryGroup (k m : ℕ) :
    szegedyRefl k m ∈ Matrix.unitaryGroup (Fin (2 ^ (k + m))) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, show star (szegedyRefl k m) = szegedyRefl k m by
    unfold szegedyRefl
    dsimp only
    rw [two_mul, star_sub, star_add, star_one, Matrix.star_eq_conjTranspose,
      (QRegister.block k m le_rfl : QRegister m (k + m)).basisOutcomeProjector_conjTranspose 0]]
  exact szegedyRefl_mul_self k m
theorem szegedyWalk_mem_unitaryGroup {k m : ℕ} (U_BE : Unitary (2 ^ (k + m))) :
    szegedyWalk U_BE ∈ Matrix.unitaryGroup (Fin (2 ^ (k + m))) ℂ :=
  Submonoid.mul_mem _ (szegedyRefl_mem_unitaryGroup k m) U_BE.2
theorem szegedyWalkInv_mem_unitaryGroup {k m : ℕ} (U_BE : Unitary (2 ^ (k + m))) :
    szegedyWalkInv U_BE ∈ Matrix.unitaryGroup (Fin (2 ^ (k + m))) ℂ :=
  Submonoid.mul_mem _ U_BE.2 (szegedyRefl_mem_unitaryGroup k m)
open scoped Matrix.Norms.L2Operator in
theorem norm_of_mem_unitaryGroup_le_one {n : Type*} [Fintype n] [DecidableEq n]
    {U : Matrix n n ℂ} (hU : U ∈ Matrix.unitaryGroup n ℂ) : ‖U‖ ≤ 1 := by
  rcases isEmpty_or_nonempty n with _ | _
  · exact Subsingleton.elim U 0 ▸ norm_zero.le.trans zero_le_one
  · exact (CStarRing.norm_coe_unitary ⟨U, hU⟩).le
open scoped Matrix.Norms.L2Operator in
theorem norm_projector_le_one {n : Type*} [Fintype n] [DecidableEq n] (P : Matrix n n ℂ)
    (hP_herm : P.IsHermitian) (hP_idem : P * P = P) : ‖P‖ ≤ 1 := by
  have hsq : ‖P‖ = ‖P‖ * ‖P‖ := by
    rw [← Matrix.l2_opNorm_conjTranspose_mul_self P, hP_herm.eq, hP_idem]
  nlinarith [norm_nonneg P]
open scoped Matrix.Norms.L2Operator in
theorem norm_basisOutcomeProjector_le_one {n m : ℕ} (r : QRegister m n) (o : Fin (2 ^ m)) :
    ‖r.basisOutcomeProjector o‖ ≤ 1 := norm_projector_le_one (r.basisOutcomeProjector o)
    (r.basisOutcomeProjector_conjTranspose o) (r.basisOutcomeProjector_mul_self o)
open scoped Matrix.Norms.L2Operator in
theorem norm_szegedyWalk_sub_inv_pow_le_two {k m : ℕ} (U_BE : Unitary (2 ^ (k + m))) (d : ℕ) :
    ‖(szegedyWalk U_BE) ^ d - (szegedyWalkInv U_BE) ^ d‖ ≤ 2 :=
  (norm_sub_le _ _).trans <| by
    linarith [norm_of_mem_unitaryGroup_le_one (Submonoid.pow_mem _ (szegedyWalk_mem_unitaryGroup
      U_BE) d), norm_of_mem_unitaryGroup_le_one (Submonoid.pow_mem _
      (szegedyWalkInv_mem_unitaryGroup U_BE) d)]
section SignalQubitBlockAlgebra
variable {n : ℕ}
def ryMatrix (c s : ℝ) : Operator 2 :=
  (c : ℂ) • (1 : Operator 2) + (s : ℂ) • (Qubit.X.1 * Qubit.Z.1)
noncomputable def sigPair (q_sig : Wire n) (P_op Q_op : Operator (2 ^ n)) : Operator (2 ^ n) :=
  let P_sig0 := (QRegister.singleton q_sig).basisOutcomeProjector 0
  let X_sig := (Circuit.X q_sig).eval.1
  P_sig0 * P_op + (X_sig * P_sig0) * Q_op
theorem sig_proj_mul_of_ne (q_sig : Wire n) {a b : Fin 2} (h : a ≠ b) :
    (QRegister.singleton q_sig).basisOutcomeProjector a *
      (QRegister.singleton q_sig).basisOutcomeProjector b = 0 := by
  rw [QRegister.basisOutcomeProjector, QRegister.basisOutcomeProjector,
    ← (QRegister.singleton q_sig).embedMatrix_mul, compProj_mul_of_ne h,
    (QRegister.singleton q_sig).embedMatrix_zero]
theorem local_X_mul_compProj0 :
    Qubit.X.1 * compProj (0 : Fin 2) = compProj (1 : Fin 2) * Qubit.X.1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Qubit.X, compProj, Matrix.mul_apply, Fin.sum_univ_two]
theorem local_X_mul_self : Qubit.X.1 * Qubit.X.1 = (1 : Operator 2) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Qubit.X, Matrix.mul_apply, Fin.sum_univ_two]
theorem local_Z_mul_compProj0 : Qubit.Z.1 * compProj (0 : Fin 2) = compProj (0 : Fin 2) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Qubit.Z, compProj, Matrix.mul_apply, Fin.sum_univ_two]
theorem local_Z_mul_X_mul_compProj0 :
    Qubit.Z.1 * (Qubit.X.1 * compProj (0 : Fin 2)) = -(Qubit.X.1 * compProj (0 : Fin 2)) := by
  have hZX : Qubit.Z.1 * Qubit.X.1 = -(Qubit.X.1 * Qubit.Z.1) := by
    simpa using congrArg Subtype.val Qubit.Z_X_anticomm
  rw [← Matrix.mul_assoc, hZX, neg_mul, Matrix.mul_assoc, local_Z_mul_compProj0]
theorem eval_X_eq_embedMatrix_X (q_sig : Wire n) :
    (Circuit.X q_sig).eval.1 = (QRegister.singleton q_sig).embedMatrix Qubit.X.1 := by
  rw [Circuit.eval_single, QRegister.embedUnitary_val]
  rfl
theorem eval_X_mul_sig_proj0 (q_sig : Wire n) :
    (Circuit.X q_sig).eval.1 * (QRegister.singleton q_sig).basisOutcomeProjector 0 =
      (QRegister.singleton q_sig).basisOutcomeProjector 1 * (Circuit.X q_sig).eval.1 := by
  rw [eval_X_eq_embedMatrix_X, QRegister.basisOutcomeProjector,
    QRegister.basisOutcomeProjector, ← (QRegister.singleton q_sig).embedMatrix_mul,
    ← (QRegister.singleton q_sig).embedMatrix_mul, local_X_mul_compProj0]
open scoped Matrix.Norms.L2Operator in
theorem norm_ryMatrix_le_one (c s : ℝ) (hcs : c ^ 2 + s ^ 2 ≤ 1) : ‖ryMatrix c s‖ ≤ 1 := by
  have h1_norm : ‖(1 : Operator 2)‖ ≤ 1 :=
    norm_of_mem_unitaryGroup_le_one (Submonoid.one_mem (Matrix.unitaryGroup (Fin 2) ℂ))
  have hsq : ‖ryMatrix c s‖ * ‖ryMatrix c s‖ ≤ 1 := by
    rw [← Matrix.l2_opNorm_conjTranspose_mul_self (ryMatrix c s),
      show ryMatrix c s = PhaseGradSignalRot.ryMatrix c s from rfl,
      PhaseGradSignalRot.ryMatrix_conjTranspose_mul_self, norm_smul, Complex.norm_real,
      Real.norm_of_nonneg (by positivity)]
    nlinarith [norm_nonneg (1 : Operator 2)]
  nlinarith [norm_nonneg (ryMatrix c s)]
theorem embedMatrix_ryMatrix_mul_sigPair (q_sig : Wire n) (c s : ℝ)
    (P_op Q_op : Operator (2 ^ n)) :
    (QRegister.singleton q_sig).embedMatrix (ryMatrix c s) * sigPair q_sig P_op Q_op =
      sigPair q_sig ((c : ℂ) • P_op - (s : ℂ) • Q_op) ((s : ℂ) • P_op + (c : ℂ) • Q_op) := by
  let rSig := QRegister.singleton q_sig
  have hV0 : rSig.embedMatrix (ryMatrix c s) * rSig.basisOutcomeProjector 0 =
      (c : ℂ) • rSig.basisOutcomeProjector 0 +
        (s : ℂ) • ((Circuit.X q_sig).eval.1 * rSig.basisOutcomeProjector 0) := by
    rw [eval_X_eq_embedMatrix_X, QRegister.basisOutcomeProjector, ← rSig.embedMatrix_mul,
      show ryMatrix c s * compProj (0 : Fin 2) =
        (c : ℂ) • compProj 0 + (s : ℂ) • (Qubit.X.1 * compProj 0) by
        rw [ryMatrix, add_mul, smul_mul_assoc, one_mul, smul_mul_assoc, Matrix.mul_assoc,
          local_Z_mul_compProj0],
      rSig.embedMatrix_add, rSig.embedMatrix_smul, rSig.embedMatrix_smul, rSig.embedMatrix_mul]
  have hV1 : rSig.embedMatrix (ryMatrix c s) *
      ((Circuit.X q_sig).eval.1 * rSig.basisOutcomeProjector 0) =
      (-(s : ℂ)) • rSig.basisOutcomeProjector 0 +
        (c : ℂ) • ((Circuit.X q_sig).eval.1 * rSig.basisOutcomeProjector 0) := by
    rw [eval_X_eq_embedMatrix_X, QRegister.basisOutcomeProjector,
      ← rSig.embedMatrix_mul Qubit.X.1, ← rSig.embedMatrix_mul (ryMatrix c s),
      show ryMatrix c s * (Qubit.X.1 * compProj (0 : Fin 2)) =
        (-(s : ℂ)) • compProj 0 + (c : ℂ) • (Qubit.X.1 * compProj 0) by
        rw [ryMatrix, add_mul, smul_mul_assoc, one_mul, smul_mul_assoc, Matrix.mul_assoc,
          local_Z_mul_X_mul_compProj0, mul_neg, ← Matrix.mul_assoc, local_X_mul_self,
          one_mul, smul_neg, ← neg_smul, add_comm],
      rSig.embedMatrix_add, rSig.embedMatrix_smul, rSig.embedMatrix_smul, rSig.embedMatrix_mul]
  unfold sigPair
  dsimp only
  rw [mul_add, ← Matrix.mul_assoc, hV0, ← Matrix.mul_assoc, hV1, add_mul, add_mul,
    smul_mul_assoc, smul_mul_assoc, smul_mul_assoc, smul_mul_assoc, mul_sub, mul_add,
    mul_smul_comm, mul_smul_comm, mul_smul_comm, mul_smul_comm, neg_smul, sub_eq_add_neg]
  abel
theorem proj_step_mul_sigPair (q_sig : Wire n) (W0 W1 P_op Q_op : Operator (2 ^ n))
    (h0 : W0 * (QRegister.singleton q_sig).basisOutcomeProjector 0 =
      (QRegister.singleton q_sig).basisOutcomeProjector 0 * W0)
    (h10 : W1 * (QRegister.singleton q_sig).basisOutcomeProjector 0 =
      (QRegister.singleton q_sig).basisOutcomeProjector 0 * W1)
    (h1X : W1 * (Circuit.X q_sig).eval.1 = (Circuit.X q_sig).eval.1 * W1) :
    (W0 * (QRegister.singleton q_sig).basisOutcomeProjector 0 +
      W1 * (QRegister.singleton q_sig).basisOutcomeProjector 1) * sigPair q_sig P_op Q_op =
      sigPair q_sig (W0 * P_op) (W1 * Q_op) := by
  let P0 := (QRegister.singleton q_sig).basisOutcomeProjector 0
  let P1 := (QRegister.singleton q_sig).basisOutcomeProjector 1
  let X_sig := (Circuit.X q_sig).eval.1
  unfold sigPair
  dsimp only
  calc (W0 * P0 + W1 * P1) * (P0 * P_op + (X_sig * P0) * Q_op)
    _ = W0 * (P0 * P0) * P_op + W0 * (P0 * (X_sig * P0)) * Q_op +
          W1 * (P1 * P0) * P_op + W1 * (P1 * (X_sig * P0)) * Q_op := by noncomm_ring
    _ = P0 * (W0 * P_op) + (X_sig * P0) * (W1 * Q_op) := by
        rw [(QRegister.singleton q_sig).basisOutcomeProjector_mul_self 0,
          show P0 * (X_sig * P0) = 0 by
            rw [eval_X_mul_sig_proj0, ← Matrix.mul_assoc, sig_proj_mul_of_ne q_sig (by decide),
              Matrix.zero_mul],
          sig_proj_mul_of_ne q_sig (by decide),
          show P1 * (X_sig * P0) = X_sig * P0 by
            rw [eval_X_mul_sig_proj0, ← Matrix.mul_assoc,
              (QRegister.singleton q_sig).basisOutcomeProjector_mul_self 1],
          h0, show W1 * (X_sig * P0) = (X_sig * P0) * W1 by
            rw [← Matrix.mul_assoc, h1X, Matrix.mul_assoc, h10, ← Matrix.mul_assoc]]
        noncomm_ring
open scoped Matrix.Norms.L2Operator in
theorem norm_sigPair_sub_target_mul_le (q_sig : Wire n)
    (P_op Q_op U_target P_in : Operator (2 ^ n)) :
    let P_sig0 := (QRegister.singleton q_sig).basisOutcomeProjector 0
    ‖(sigPair q_sig P_op Q_op - P_sig0 * U_target) * P_in‖ ≤
      ‖(P_op - U_target) * P_in‖ + ‖Q_op * P_in‖ := by
  intro P_sig0
  have hP0 := norm_basisOutcomeProjector_le_one (QRegister.singleton q_sig) 0
  have hX := norm_of_mem_unitaryGroup_le_one (Circuit.X q_sig).eval.2
  rw [show (sigPair q_sig P_op Q_op - P_sig0 * U_target) * P_in =
      P_sig0 * ((P_op - U_target) * P_in) +
        (Circuit.X q_sig).eval.1 * (P_sig0 * (Q_op * P_in)) by
    dsimp [sigPair, P_sig0]
    noncomm_ring]
  exact (norm_add_le _ _).trans (add_le_add
    ((norm_mul_le _ _).trans (by nlinarith [norm_nonneg ((P_op - U_target) * P_in)]))
    ((norm_mul_le _ _).trans (by
      nlinarith [norm_mul_le P_sig0 (Q_op * P_in), norm_nonneg (P_sig0 * (Q_op * P_in)),
        norm_nonneg (Q_op * P_in)])))
end SignalQubitBlockAlgebra
section LaurentPolynomialRecurrence
def laurentTerm {A : Type*} [Monoid A] (M : ℕ) (W W_inv : A) (i : Fin (2 * M + 1)) : A := if
    i.val < M then W_inv ^ (M - i.val) else W ^ (i.val - M)
@[simp] theorem laurentTerm_mid {A : Type*} [Monoid A] (M : ℕ) (W W_inv : A) :
    laurentTerm M W W_inv ⟨M, by omega⟩ = 1 := by simp [laurentTerm]
theorem laurentTerm_add {A : Type*} [Monoid A] (M d : ℕ) (hd : d ≤ M) (W W_inv : A) :
    laurentTerm M W W_inv ⟨M + d, by omega⟩ = W ^ d := by
  dsimp [laurentTerm]
  rw [ite_eq_right (by omega), Nat.add_sub_cancel_left]
theorem mul_laurentTerm_castSucc {A : Type*} [Monoid A] (M : ℕ) (W W_inv : A)
    (hW_inv : W * W_inv = 1) (i : Fin (2 * M)) :
    W * laurentTerm M W W_inv i.castSucc = laurentTerm M W W_inv i.succ := by
  unfold laurentTerm
  simp only [Fin.val_castSucc, Fin.val_succ]
  by_cases h1 : i.val + 1 < M
  · rw [ite_eq_left (by omega), ite_eq_left h1, show M - i.val = (M - (i.val + 1)) + 1 by omega,
      pow_succ', ← mul_assoc, hW_inv, one_mul]
  · by_cases h0 : i.val < M
    · rw [ite_eq_left h0, ite_eq_right h1, show M - i.val = 1 by omega,
        show i.val + 1 - M = 0 by omega,
        pow_one, pow_zero, hW_inv]
    · rw [ite_eq_right h0, ite_eq_right h1, show i.val + 1 - M = (i.val - M) + 1 by omega,
        pow_succ']
noncomputable def laurentEval {A : Type*} [Ring A] [Algebra ℂ A]
    (M : ℕ) (W W_inv : A) (p : Fin (2 * M + 1) → ℝ) : A :=
  ∑ i : Fin (2 * M + 1), (p i : ℂ) • laurentTerm M W W_inv i
def shiftRight (M : ℕ) (p : Fin (2 * M + 1) → ℝ) (i : Fin (2 * M + 1)) : ℝ :=
  if h : i.val = 0 then 0 else p ⟨i.val - 1, by omega⟩
def shiftLeft (M : ℕ) (p : Fin (2 * M + 1) → ℝ) (i : Fin (2 * M + 1)) : ℝ :=
  if h : i.val < 2 * M then p ⟨i.val + 1, by omega⟩ else 0
@[simp] theorem shiftRight_zero (M : ℕ) (p : Fin (2 * M + 1) → ℝ) : shiftRight M p 0 = 0 := by
  simp [shiftRight]
@[simp] theorem shiftRight_succ (M : ℕ) (p : Fin (2 * M + 1) → ℝ) (i : Fin (2 * M)) :
    shiftRight M p i.succ = p i.castSucc := by
  simp only [shiftRight, Fin.val_succ, Nat.succ_ne_zero, ↓reduceDIte, Nat.add_sub_cancel]
  rfl
@[simp] theorem shiftLeft_last (M : ℕ) (p : Fin (2 * M + 1) → ℝ) :
    shiftLeft M p (Fin.last (2 * M)) = 0 := by simp [shiftLeft]
@[simp] theorem shiftLeft_castSucc (M : ℕ) (p : Fin (2 * M + 1) → ℝ) (i : Fin (2 * M)) :
    shiftLeft M p i.castSucc = p i.succ := by
  simp only [shiftLeft, Fin.val_castSucc, i.isLt, ↓reduceDIte]
  rfl
theorem mul_inv_laurentEval_of_zero_eq_zero {A : Type*} [Ring A] [Algebra ℂ A] (M : ℕ)
    (W W_inv : A) (hW_inv : W * W_inv = 1) (hWinv_W : W_inv * W = 1) (p : Fin (2 * M + 1) → ℝ)
    (hzero : p 0 = 0) :
    W_inv * laurentEval M W W_inv p = laurentEval M W W_inv (shiftLeft M p) := by
  unfold laurentEval
  rw [Fin.sum_univ_succ, hzero, Complex.ofReal_zero, zero_smul, zero_add, Finset.mul_sum,
    Fin.sum_univ_castSucc (f := fun i ↦ (shiftLeft M p i : ℂ) • laurentTerm M W W_inv i),
    shiftLeft_last, Complex.ofReal_zero, zero_smul, add_zero]
  exact Finset.sum_congr rfl fun i _ ↦ by
    rw [mul_smul_comm, ← mul_laurentTerm_castSucc M W W_inv hW_inv i, ← mul_assoc, hWinv_W,
      one_mul, shiftLeft_castSucc]
theorem laurentEval_linear {A : Type*} [Ring A] [Algebra ℂ A] (M : ℕ) (W W_inv : A) (c s : ℝ)
    (p q : Fin (2 * M + 1) → ℝ) : (c : ℂ) • laurentEval M W W_inv p + (s : ℂ) • laurentEval M
    W W_inv q = laurentEval M W W_inv (fun i ↦ c * p i + s * q i) := by
  unfold laurentEval
  rw [Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ ↦ by
    rw [smul_smul, smul_smul, ← add_smul]
    norm_cast
theorem laurentEval_sub_linear {A : Type*} [Ring A] [Algebra ℂ A] (M : ℕ) (W W_inv : A)
    (c s : ℝ) (p q : Fin (2 * M + 1) → ℝ) : (c : ℂ) • laurentEval M W W_inv p - (s : ℂ) •
    laurentEval M W W_inv q = laurentEval M W W_inv (fun i ↦ c * p i - s * q i) := by
  simpa only [Complex.ofReal_neg, neg_smul, neg_mul, ← sub_eq_add_neg] using
    laurentEval_linear M W W_inv c (-s) p q
def laurentChebWeight (M : ℕ) (p : Fin (2 * M + 1) → ℝ) (d : ℕ) : ℝ :=
  if d = 0 then p ⟨M, by omega⟩
  else if h : d ≤ M then (-1 : ℝ) ^ d * p ⟨M + d, by omega⟩ + p ⟨M - d, by omega⟩
  else 0
def laurentAsymDefect (M : ℕ) (p : Fin (2 * M + 1) → ℝ) (j : Fin M) : ℝ :=
  |(-1 : ℝ) ^ (j.val + 1) * p ⟨M + (j.val + 1), by omega⟩ - p ⟨M - (j.val + 1), by omega⟩|
open scoped Matrix.Norms.L2Operator in
theorem norm_laurentEval_sub_cheb_sum_mul_proj_le {k m : ℕ} {α : ℝ} {A : Operator (2 ^ k)}
    {U_BE : Unitary (2 ^ (k + m))} (hBE : IsQubitizedBlockEncodingUnitary α A U_BE)
    (M : ℕ) (p : Fin (2 * M + 1) → ℝ) :
    let sys : QRegister k (k + m) := QRegister.block 0 k (by omega)
    let anc : QRegister m (k + m) := QRegister.block k m le_rfl
    let P_anc := anc.basisOutcomeProjector 0
    let W := laurentWalk U_BE
    let W_inv := laurentWalkInv U_BE
    let S_cheb := ∑ d ∈ Finset.range (M + 1),
      ((-Complex.I) ^ d * (laurentChebWeight M p d : ℂ)) •
        sys.embedMatrix (chebT d ((α : ℂ)⁻¹ • A))
    ‖(laurentEval M W W_inv p - S_cheb) * P_anc‖ ≤
      ∑ j : Fin M, laurentAsymDefect M p j := by
  intro sys anc P_anc W W_inv S_cheb
  let Q := szegedyWalk U_BE
  let Q_inv := szegedyWalkInv U_BE
  have hIcc (r : ℕ) (hr : r ≤ M) (F : ℕ → Operator (2 ^ (k + m))) :
      (∑ i ∈ Finset.Icc (M - r) (M + r), F i) = F M +
        ∑ d ∈ Finset.range r, (F (M + (d + 1)) + F (M - (d + 1))) := by
    induction r with
    | zero => simp
    | succ r ih =>
      rw [show Finset.Icc (M - (r + 1)) (M + (r + 1)) =
          insert (M - (r + 1)) (insert (M + (r + 1)) (Finset.Icc (M - r) (M + r))) from
        Finset.ext fun _ ↦ by
          simp only [Finset.mem_Icc, Finset.mem_insert]
          omega,
        Finset.sum_insert (by
          simp only [Finset.mem_insert, Finset.mem_Icc]
          omega),
        Finset.sum_insert (by
          simp only [Finset.mem_Icc]
          omega),
        ih (by omega), Finset.sum_range_succ]
      abel
  have hsplit (f : Fin (2 * M + 1) → Operator (2 ^ (k + m))) :
      (∑ i : Fin (2 * M + 1), f i) = f ⟨M, by omega⟩ +
        ∑ d : Fin M, (f ⟨M + (d.val + 1), by omega⟩ + f ⟨M - (d.val + 1), by omega⟩) := by
    let F : ℕ → Operator (2 ^ (k + m)) := fun i ↦ if h : i < 2 * M + 1 then f ⟨i, h⟩ else 0
    rw [show (∑ i : Fin (2 * M + 1), f i) = ∑ i ∈ Finset.Icc (M - M) (M + M), F i by
      rw [Nat.sub_self, ← Nat.two_mul, show Finset.Icc 0 (2 * M) = Finset.range (2 * M + 1) from
        Finset.ext fun _ ↦ by
          simp only [Finset.mem_Icc, Finset.mem_range]
          omega, ← Fin.sum_univ_eq_sum_range]
      exact Finset.sum_congr rfl fun i _ ↦ (show F i = f i from dite_eq_left i.isLt).symm,
      hIcc M le_rfl F, ← Fin.sum_univ_eq_sum_range,
      show F M = f ⟨M, by omega⟩ from dite_eq_left (by omega)]
    exact congrArg (f ⟨M, by omega⟩ + ·) (Finset.sum_congr rfl fun d _ ↦ by
      have := d.isLt
      dsimp [F]
      rw [dite_eq_left (by omega), dite_eq_left (by omega)])
  have hsym (d : ℕ) : (Q ^ d + Q_inv ^ d) * P_anc =
      2 * sys.embedMatrix (chebT d ((α : ℂ)⁻¹ • A)) * P_anc := by
    have hQinv (n : ℕ) : Q_inv ^ n * P_anc = szegedyRefl k m * Q ^ n * P_anc := by
      induction n with
      | zero =>
        rw [pow_zero, pow_zero, one_mul, mul_one]
        change P_anc = (2 * P_anc - 1) * P_anc
        rw [sub_mul, Matrix.mul_assoc, anc.basisOutcomeProjector_mul_self 0]
        noncomm_ring
      | succ n ih =>
        rw [pow_succ', pow_succ', Matrix.mul_assoc, ih,
          show Q_inv * (szegedyRefl k m * Q ^ n * P_anc) =
            U_BE.1 * (szegedyRefl k m * szegedyRefl k m) * Q ^ n * P_anc by
            dsimp [Q_inv, szegedyWalkInv]
            noncomm_ring,
          szegedyRefl_mul_self, mul_one, ← one_mul (U_BE.1 * Q ^ n * P_anc),
          ← szegedyRefl_mul_self k m]
        dsimp [Q, szegedyWalk]
        noncomm_ring
    rw [add_mul, hQinv d, show Q ^ d * P_anc + szegedyRefl k m * Q ^ d * P_anc =
        2 * (P_anc * Q ^ d * P_anc) by
        dsimp [szegedyRefl]
        noncomm_ring,
      chebWalk_blockEncoding hBE d, Matrix.mul_assoc]
  have h_pair (j : Fin M) : (p ⟨M + (j.val + 1), by omega⟩ : ℂ) •
          (laurentTerm M W W_inv ⟨M + (j.val + 1), by omega⟩ * P_anc) +
        (p ⟨M - (j.val + 1), by omega⟩ : ℂ) •
          (laurentTerm M W W_inv ⟨M - (j.val + 1), by omega⟩ * P_anc) =
      ((-Complex.I) ^ (j.val + 1) * (laurentChebWeight M p (j.val + 1) : ℂ)) •
          (sys.embedMatrix (chebT (j.val + 1) ((α : ℂ)⁻¹ • A)) * P_anc) +
        ((-Complex.I) ^ (j.val + 1) *
          ((((-1 : ℝ) ^ (j.val + 1) * p ⟨M + (j.val + 1), by omega⟩ -
            p ⟨M - (j.val + 1), by omega⟩) / 2 : ℝ) : ℂ)) •
          ((Q ^ (j.val + 1) - Q_inv ^ (j.val + 1)) * P_anc) := by
    set d := j.val + 1
    have hjM : d ≤ M := by omega
    have hcw : laurentChebWeight M p d =
        (-1 : ℝ) ^ d * p ⟨M + d, by omega⟩ + p ⟨M - d, by omega⟩ := by
      unfold laurentChebWeight
      rw [ite_eq_right (by omega), dite_eq_left hjM]
    rw [laurentTerm_add M d hjM W W_inv,
      show laurentTerm M W W_inv ⟨M - d, by omega⟩ = W_inv ^ d by
        dsimp [laurentTerm]
        rw [ite_eq_left (by omega), Nat.sub_sub_self hjM],
      laurentWalk_pow, laurentWalkInv_pow, smul_mul_assoc, smul_mul_assoc, smul_smul, smul_smul,
      show (Complex.I : ℂ) ^ d = (-1 : ℂ) ^ d * (-Complex.I) ^ d by
        rw [← mul_pow, neg_one_mul, neg_neg],
      hcw, show sys.embedMatrix (chebT d ((α : ℂ)⁻¹ • A)) * P_anc =
        (2 : ℂ)⁻¹ • (Q ^ d * P_anc + Q_inv ^ d * P_anc) by
        rw [← add_mul, hsym d, Matrix.mul_assoc, two_mul, ← two_smul ℂ,
          inv_smul_smul₀ two_ne_zero],
      sub_mul]
    ext r c
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, inv_eq_one_div]
    push_cast
    ring
  have h_diff : (laurentEval M W W_inv p - S_cheb) * P_anc = ∑ j : Fin M,
      ((-Complex.I) ^ (j.val + 1) * ((((-1 : ℝ) ^ (j.val + 1) * p ⟨M + (j.val + 1), by omega⟩ -
        p ⟨M - (j.val + 1), by omega⟩) / 2 : ℝ) : ℂ)) •
        ((Q ^ (j.val + 1) - Q_inv ^ (j.val + 1)) * P_anc) := by
    rw [sub_mul, show laurentEval M W W_inv p * P_anc =
        ((-Complex.I) ^ 0 * (laurentChebWeight M p 0 : ℂ)) •
          (sys.embedMatrix (chebT 0 ((α : ℂ)⁻¹ • A)) * P_anc) +
        ∑ j : Fin M, ((p ⟨M + (j.val + 1), by omega⟩ : ℂ) •
            (laurentTerm M W W_inv ⟨M + (j.val + 1), by omega⟩ * P_anc) +
          (p ⟨M - (j.val + 1), by omega⟩ : ℂ) •
            (laurentTerm M W W_inv ⟨M - (j.val + 1), by omega⟩ * P_anc)) by
      unfold laurentEval
      rw [Finset.sum_mul]
      simp_rw [smul_mul_assoc]
      rw [hsplit]
      simp [laurentTerm_mid, laurentChebWeight],
      show S_cheb * P_anc = ((-Complex.I) ^ 0 * (laurentChebWeight M p 0 : ℂ)) •
        (sys.embedMatrix (chebT 0 ((α : ℂ)⁻¹ • A)) * P_anc) + ∑ j : Fin M,
        ((-Complex.I) ^ (j.val + 1) * (laurentChebWeight M p (j.val + 1) : ℂ)) •
          (sys.embedMatrix (chebT (j.val + 1) ((α : ℂ)⁻¹ • A)) * P_anc) by
      dsimp [S_cheb]
      rw [Finset.sum_range_succ', ← Fin.sum_univ_eq_sum_range _ M, add_mul, Finset.sum_mul]
      simp_rw [smul_mul_assoc]
      abel]
    simp_rw [h_pair, Finset.sum_add_distrib]
    abel
  rw [h_diff]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ ↦ ?_)
  rw [norm_smul, norm_mul, norm_pow, norm_neg, Complex.norm_I, one_pow, one_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hQ_sub : ‖(Q ^ (j.val + 1) - Q_inv ^ (j.val + 1)) * P_anc‖ ≤ 2 :=
    (norm_mul_le _ _).trans ((mul_le_of_le_one_right (norm_nonneg _)
      (norm_basisOutcomeProjector_le_one anc 0)).trans
      (norm_szegedyWalk_sub_inv_pow_le_two U_BE (j.val + 1)))
  unfold laurentAsymDefect
  nlinarith [abs_nonneg ((-1 : ℝ) ^ (j.val + 1) * p ⟨M + (j.val + 1), by omega⟩ -
    p ⟨M - (j.val + 1), by omega⟩)]
open scoped Matrix.Norms.L2Operator in
theorem norm_laurentEval_le_l1 {k m : ℕ} (U_BE : Unitary (2 ^ (k + m)))
    (M : ℕ) (q : Fin (2 * M + 1) → ℝ) :
    ‖laurentEval M (laurentWalk U_BE) (laurentWalkInv U_BE) q‖ ≤ ∑ i : Fin (2 * M + 1), |q i| := by
  unfold laurentEval
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ ↦ ?_)
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
  have ht : ‖laurentTerm M (laurentWalk U_BE) (laurentWalkInv U_BE) i‖ ≤ 1 := by
    unfold laurentTerm
    split_ifs
    · rw [laurentWalkInv_pow, norm_smul, norm_pow, norm_neg, Complex.norm_I, one_pow, one_mul]
      exact norm_of_mem_unitaryGroup_le_one
        (Submonoid.pow_mem _ (szegedyWalkInv_mem_unitaryGroup U_BE) _)
    · rw [laurentWalk_pow, norm_smul, norm_pow, Complex.norm_I, one_pow, one_mul]
      exact norm_of_mem_unitaryGroup_le_one
        (Submonoid.pow_mem _ (szegedyWalk_mem_unitaryGroup U_BE) _)
  nlinarith [abs_nonneg (q i)]
end LaurentPolynomialRecurrence
section LaurentRecurrenceExecution
theorem laurentWalk_mul_inv {k m : ℕ} {α : ℝ} {A : Operator (2 ^ k)}
    {U_BE : Unitary (2 ^ (k + m))} (hBE : IsQubitizedBlockEncodingUnitary α A U_BE) :
    laurentWalk U_BE * laurentWalkInv U_BE = 1 := by
  rw [laurentWalk, laurentWalkInv, smul_mul_smul_comm, szegedyWalk, szegedyWalkInv,
    Matrix.mul_assoc, ← Matrix.mul_assoc U_BE.1, qubitized_mul_self hBE, one_mul,
    szegedyRefl_mul_self, mul_neg, Complex.I_mul_I, neg_neg, one_smul]
theorem laurentWalkInv_mul {k m : ℕ} {α : ℝ} {A : Operator (2 ^ k)}
    {U_BE : Unitary (2 ^ (k + m))} (hBE : IsQubitizedBlockEncodingUnitary α A U_BE) :
    laurentWalkInv U_BE * laurentWalk U_BE = 1 := by
  rw [laurentWalk, laurentWalkInv, smul_mul_smul_comm, szegedyWalk, szegedyWalkInv,
    Matrix.mul_assoc, ← Matrix.mul_assoc (szegedyRefl k m), szegedyRefl_mul_self, one_mul,
    qubitized_mul_self hBE, neg_mul, Complex.I_mul_I, neg_neg, one_smul]
def gqspRotStep (M : ℕ) (c s : ℝ) (pq : (Fin (2 * M + 1) → ℝ) × (Fin (2 * M + 1) → ℝ)) :
    (Fin (2 * M + 1) → ℝ) × (Fin (2 * M + 1) → ℝ) :=
  (fun i ↦ c * pq.1 i - s * pq.2 i, fun i ↦ s * pq.1 i + c * pq.2 i)
theorem embedMatrix_comm_sig_proj {m n : ℕ} (r : QRegister m n) (q_sig : Wire n)
    (hdisj : r.DisjointWires (QRegister.singleton q_sig)) (X : Operator (2 ^ m)) (o : Fin 2) :
    r.embedMatrix X * (QRegister.singleton q_sig).basisOutcomeProjector o =
    (QRegister.singleton q_sig).basisOutcomeProjector o * r.embedMatrix X := by
  rw [QRegister.basisOutcomeProjector]
  exact r.embedMatrix_comm_of_disjoint (QRegister.singleton q_sig) hdisj X _
theorem embedMatrix_comm_sig_X {m n : ℕ} (r : QRegister m n) (q_sig : Wire n)
    (hdisj : r.DisjointWires (QRegister.singleton q_sig)) (X : Operator (2 ^ m)) :
    r.embedMatrix X * (Circuit.X q_sig).eval.1 = (Circuit.X q_sig).eval.1 * r.embedMatrix X := by
  rw [eval_X_eq_embedMatrix_X q_sig]
  exact r.embedMatrix_comm_of_disjoint (QRegister.singleton q_sig) hdisj X Qubit.X.1
theorem embedMatrix_sub {m n : ℕ} (r : QRegister m n) (X Y : Operator (2 ^ m)) :
    r.embedMatrix (X - Y) = r.embedMatrix X - r.embedMatrix Y := by
  rw [sub_eq_add_neg, sub_eq_add_neg, ← neg_one_smul ℂ Y, r.embedMatrix_add,
    r.embedMatrix_smul, neg_one_smul]
end LaurentRecurrenceExecution
section TaylorChebyshevBridge
section ChebyshevTaylorAlgebra
variable {A : Type*} [Ring A] [Algebra ℂ A]
noncomputable def taylorPoly (x : A) (K : ℕ) : A :=
  ∑ k ∈ Finset.range (K + 1),((k.factorial : ℂ)⁻¹) • (x ^ k)
end ChebyshevTaylorAlgebra
def stepChebScaled (c : ℕ → ℕ) : ℕ → ℕ
  | 0 => c 1
  | 1 => 2 * c 0 + c 2
  | m + 2 => c (m + 1) + c (m + 3)
def powChebScaled : ℕ → ℕ → ℕ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, d => stepChebScaled (powChebScaled n) d
theorem powChebScaled_eq_zero_of_lt : ∀ {n d : ℕ}, n < d → powChebScaled n d = 0
  | 0, 0, h => by omega
  | 0, _ + 1, _ => rfl
  | _ + 1, 0, h => by omega
  | _ + 1, 1, h => by omega
  | n + 1, d + 2, h => by simp [powChebScaled, stepChebScaled,
      powChebScaled_eq_zero_of_lt (by omega : n < d + 1),
      powChebScaled_eq_zero_of_lt (by omega : n < d + 3)]
theorem powChebScaled_eq_zero_of_odd_add : ∀ {n d : ℕ}, (n + d) % 2 = 1 → powChebScaled n d = 0
  | 0, 0, h => by omega
  | 0, _ + 1, _ => rfl
  | n + 1, 0, h => by
      simp [powChebScaled, stepChebScaled, powChebScaled_eq_zero_of_odd_add (n := n) (by omega)]
  | n + 1, 1, h => by simp [powChebScaled, stepChebScaled,
      powChebScaled_eq_zero_of_odd_add (n := n) (d := 0) (by omega),
      powChebScaled_eq_zero_of_odd_add (n := n) (d := 2) (by omega)]
  | n + 1, d + 2, h => by simp [powChebScaled, stepChebScaled,
      powChebScaled_eq_zero_of_odd_add (n := n) (d := d + 1) (by omega),
      powChebScaled_eq_zero_of_odd_add (n := n) (d := d + 3) (by omega)]
noncomputable def chebTaylorWeight (β : ℝ) (D d : ℕ) : ℝ := ∑ n ∈ Finset.range (D + 1),
    ((-1 : ℝ) ^ ((n - d) / 2)) * ((n.factorial : ℝ)⁻¹ * β ^ n) *
    ((powChebScaled n d : ℝ) * ((2 : ℝ) ^ n)⁻¹)
@[simp] theorem extractIndex_zero {k n : ℕ} (r : QRegister k n) : r.extractIndex 0 = 0 := by
  refine (basisBitsEquiv k).injective (funext fun i ↦ ?_)
  change basisBits k (r.extractIndex 0) i = basisBits k 0 i
  rw [QRegister.basisBits_extractIndex, basisBits_eq_div_mod, basisBits_eq_div_mod]
  simp
theorem basisOutcomeProjector_zero_compose_mul {n m ℓ : ℕ} (rAnc : QRegister m n)
    (inner : QRegister ℓ m) : (rAnc.compose inner).basisOutcomeProjector 0 *
    rAnc.basisOutcomeProjector 0 = rAnc.basisOutcomeProjector 0 := by
  rw [QRegister.basisOutcomeProjector_eq_diagonal, QRegister.basisOutcomeProjector_eq_diagonal,
    Matrix.diagonal_mul_diagonal]
  refine congrArg Matrix.diagonal (funext fun g ↦ ?_)
  by_cases hg : rAnc.extractIndex g = 0
  · simp [hg, QRegister.extractIndex_compose]
  · simp [hg]
open scoped Matrix.Norms.L2Operator in
theorem norm_chebT_embedMatrix_proj_le_one {k m_BE m : ℕ} (hm : m_BE ≤ m)
    {α : ℝ} {A : Operator (2 ^ k)} {U_BE : Unitary (2 ^ (k + m_BE))}
    (hBE : IsQubitizedBlockEncodingUnitary α A U_BE) (d : ℕ) :
    let sys : QRegister k (k + m) := QRegister.block 0 k (by omega)
    let anc : QRegister m (k + m) := QRegister.block k m le_rfl
    let P₀ := anc.basisOutcomeProjector 0
    ‖sys.embedMatrix (chebT d ((α : ℂ)⁻¹ • A)) * P₀‖ ≤ 1 := by
  intro sys anc P₀
  let rSysBE : QRegister (k + m_BE) (k + m) := QRegister.block 0 (k + m_BE) (by omega)
  let sys0 : QRegister k (k + m_BE) := QRegister.block 0 k (by omega)
  let anc0 : QRegister m_BE (k + m_BE) := QRegister.block k m_BE le_rfl
  let innerBE : QRegister m_BE m := QRegister.block 0 m_BE (by omega)
  let P_BE := (anc.compose innerBE).basisOutcomeProjector 0
  have hcomp_sys : rSysBE.compose sys0 = sys :=
    BiGqspVerifierCoreAlt.qreg_ext fun _ ↦ Fin.ext (by simp [rSysBE, sys0, sys])
  have hcomp_anc : rSysBE.compose anc0 = anc.compose innerBE :=
    BiGqspVerifierCoreAlt.qreg_ext fun _ ↦
      Fin.ext (by simp [rSysBE, anc0, anc, innerBE])
  have hP_BE_P0 : P_BE * P₀ = P₀ := basisOutcomeProjector_zero_compose_mul anc innerBE
  have hwalk := congrArg rSysBE.embedMatrix (chebWalk_blockEncoding hBE d)
  simp only [rSysBE.embedMatrix_mul] at hwalk
  rw [← QRegister.embedMatrix_compose, hcomp_sys, QRegister.basisOutcomeProjector,
    ← QRegister.embedMatrix_compose, hcomp_anc, ← QRegister.basisOutcomeProjector] at hwalk
  rw [show sys.embedMatrix (chebT d ((α : ℂ)⁻¹ • A)) * P₀ =
      P_BE * (rSysBE.embedMatrix ((szegedyWalk U_BE) ^ d) * P₀) by
    nth_rw 1 [← hP_BE_P0]
    rw [← Matrix.mul_assoc, ← hwalk, Matrix.mul_assoc, hP_BE_P0, Matrix.mul_assoc]]
  exact (norm_mul_le _ _).trans ((mul_le_of_le_one_left (norm_nonneg _)
    (norm_basisOutcomeProjector_le_one _ 0)).trans ((norm_mul_le _ _).trans
      ((mul_le_of_le_one_left (norm_nonneg _)
        (norm_of_mem_unitaryGroup_le_one (rSysBE.embedUnitary
          ⟨_, Submonoid.pow_mem _ (szegedyWalk_mem_unitaryGroup U_BE) d⟩).2)).trans
        (norm_basisOutcomeProjector_le_one anc 0))))
open scoped Matrix.Norms.L2Operator in
theorem norm_chebSum_sub_taylorPoly_le {k m_BE m : ℕ} (hm : m_BE ≤ m) {α : ℝ} (τ : ℝ)
    (hα : α ≠ 0) {A : Operator (2 ^ k)} {U_BE : Unitary (2 ^ (k + m_BE))}
    (hBE : IsQubitizedBlockEncodingUnitary α A U_BE) (K : ℕ) (w_approx : ℕ → ℝ) :
    let sys : QRegister k (k + m) := QRegister.block 0 k (by omega)
    let anc : QRegister m (k + m) := QRegister.block k m le_rfl
    let P₀ := anc.basisOutcomeProjector 0
    let S_approx := ∑ d ∈ Finset.range (K + 1),
      ((-Complex.I) ^ d * (w_approx d : ℂ)) • sys.embedMatrix (chebT d ((α : ℂ)⁻¹ • A))
    let S_exact := sys.embedMatrix (taylorPoly ((-Complex.I * (τ : ℂ)) • A) K)
    ‖(S_approx - S_exact) * P₀‖ ≤
      ∑ d ∈ Finset.range (K + 1), |w_approx d - chebTaylorWeight (α * τ) K d| := by
  intro sys anc P₀ S_approx S_exact
  have h_sum_tay : (∑ d ∈ Finset.range (K + 1),
      ((-Complex.I) ^ d * (chebTaylorWeight (α * τ) K d : ℂ)) • chebT d ((α : ℂ)⁻¹ • A)) =
      taylorPoly ((-Complex.I * ((α * τ : ℝ) : ℂ)) • ((α : ℂ)⁻¹ • A)) K := by
    let X : Operator (2 ^ k) := (α : ℂ)⁻¹ • A
    have hpow (n : ℕ) : ((2 : ℂ) ^ n) • X ^ n =
        ∑ d ∈ Finset.range (n + 1), (powChebScaled n d : ℂ) • chebT d X := by
      induction n with
      | zero => simp [powChebScaled]
      | succ n ih =>
        set F : ℕ → Operator (2 ^ k) := fun m ↦ (powChebScaled n (m + 1) : ℂ) • chebT m X
        have hF : ∑ m ∈ Finset.range n, F m = (∑ m ∈ Finset.range n, F (m + 2)) + F 1 + F 0 := by
          rw [show ∑ m ∈ Finset.range n, F m = ∑ m ∈ Finset.range (n + 2), F m by
              simp [Finset.sum_range_succ, F, powChebScaled_eq_zero_of_lt (by omega : n < n + 1),
                powChebScaled_eq_zero_of_lt (by omega : n < n + 2)],
            Finset.sum_range_succ' F (n + 1), Finset.sum_range_succ' (fun k ↦ F (k + 1)) n]
        have hsucc : ∑ m ∈ Finset.range n,
            (2 : ℂ) • (X * ((powChebScaled n (m + 1) : ℂ) • chebT (m + 1) X)) =
            (∑ m ∈ Finset.range n, (powChebScaled n (m + 1) : ℂ) • chebT (m + 2) X) +
              ∑ m ∈ Finset.range n, F m := by
          rw [← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun m _ ↦ by
            rw [mul_smul_comm, smul_comm (2 : ℂ),
              show (2 : ℂ) • (X * chebT (m + 1) X) = chebT (m + 2) X + chebT m X by
                rw [chebT_add_two, two_smul]
                noncomm_ring, smul_add]
        rw [pow_succ', pow_succ', mul_smul (2 : ℂ), ← mul_smul_comm ((2 : ℂ) ^ n), ih,
          Finset.sum_range_succ' _ n, mul_add, smul_add, Finset.mul_sum, Finset.smul_sum, hsucc,
          hF, show (2 : ℂ) • (X * ((powChebScaled n 0 : ℂ) • chebT 0 X)) =
            (2 * (powChebScaled n 0 : ℂ)) • chebT 1 X by
            rw [mul_smul_comm, chebT_zero, mul_one, chebT_one, smul_smul],
          Finset.sum_range_succ' _ (n + 1), Finset.sum_range_succ'
            (fun k ↦ (powChebScaled (n + 1) (k + 1) : ℂ) • chebT (k + 1) X) n,
          show ∑ m ∈ Finset.range n, (powChebScaled (n + 1) (m + 2) : ℂ) • chebT (m + 2) X =
            (∑ m ∈ Finset.range n, (powChebScaled n (m + 1) : ℂ) • chebT (m + 2) X) +
              ∑ m ∈ Finset.range n, F (m + 2) by
            rw [← Finset.sum_add_distrib]
            exact Finset.sum_congr rfl fun _ _ ↦ by
              simp only [powChebScaled, stepChebScaled, Nat.cast_add, add_smul, F]]
        simp only [powChebScaled, stepChebScaled, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
          add_smul, F]
        abel
    have hpowD {n : ℕ} (hn : n ≤ K) : X ^ n = ∑ d ∈ Finset.range (K + 1),
        ((powChebScaled n d : ℂ) * ((2 : ℂ) ^ n)⁻¹) • chebT d X := by
      rw [← inv_smul_smul₀ (pow_ne_zero n (two_ne_zero' ℂ)) (X ^ n), hpow n, Finset.smul_sum]
      refine (Finset.sum_congr rfl fun d _ ↦ by rw [smul_smul, mul_comm]).trans
        (Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ hn)) fun d _ hnot ↦ ?_)
      rw [Finset.mem_range, not_lt] at hnot
      simp [powChebScaled_eq_zero_of_lt (by omega : n < d)]
    change (∑ d ∈ Finset.range (K + 1),
        ((-Complex.I) ^ d * (chebTaylorWeight (α * τ) K d : ℂ)) • chebT d X) =
      taylorPoly ((-Complex.I * ((α * τ : ℝ) : ℂ)) • X) K
    unfold chebTaylorWeight taylorPoly
    push_cast
    simp_rw [Finset.mul_sum, Finset.sum_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun n hn ↦ ?_
    rw [smul_pow, smul_smul, hpowD (Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)), Finset.smul_sum]
    refine Finset.sum_congr rfl fun d _ ↦ ?_
    rw [smul_smul]
    congr 1
    by_cases hlt : n < d
    · simp [powChebScaled_eq_zero_of_lt hlt]
    · by_cases hodd : (n + d) % 2 = 1
      · simp [powChebScaled_eq_zero_of_odd_add hodd]
      · rw [mul_pow (-Complex.I), mul_pow,
          show (-Complex.I) ^ n = (-Complex.I) ^ d * (-1 : ℂ) ^ ((n - d) / 2) by
          conv_lhs => rw [show n = d + 2 * ((n - d) / 2) by omega]
          rw [pow_add, pow_mul, show (-Complex.I) ^ 2 = -1 by simp [sq]]]
        ring
  rw [show (S_approx - S_exact) * P₀ = ∑ d ∈ Finset.range (K + 1), ((-Complex.I) ^ d *
      ((w_approx d - chebTaylorWeight (α * τ) K d : ℝ) : ℂ)) •
      (sys.embedMatrix (chebT d ((α : ℂ)⁻¹ • A)) * P₀) by
    dsimp [S_approx, S_exact]
    rw [show (-Complex.I * (τ : ℂ)) • A = (-Complex.I * ((α * τ : ℝ) : ℂ)) • ((α : ℂ)⁻¹ • A) by
      rw [smul_smul]
      congr 1
      push_cast
      rw [mul_assoc (-Complex.I), mul_right_comm (α : ℂ) (τ : ℂ),
        mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hα), one_mul],
      ← h_sum_tay, sys.embedMatrix_sum, ← Finset.sum_sub_distrib, Finset.sum_mul]
    refine Finset.sum_congr rfl fun d _ ↦ ?_
    rw [sys.embedMatrix_smul, ← sub_smul, smul_mul_assoc]
    congr 1
    push_cast
    ring]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun d _ ↦ ?_)
  rw [norm_smul, norm_mul, norm_pow, norm_neg, Complex.norm_I, one_pow, one_mul,
    Complex.norm_real, Real.norm_eq_abs]
  nlinarith [norm_chebT_embedMatrix_proj_le_one hm hBE d,
    abs_nonneg (w_approx d - chebTaylorWeight (α * τ) K d)]
open scoped Matrix.Norms.L2Operator in
theorem norm_embedMatrix_le {k n : ℕ} (r : QRegister k n)
    (M : Matrix (Fin (2 ^ k)) (Fin (2 ^ k)) ℂ) : ‖r.embedMatrix M‖ ≤ ‖M‖ := by
  let T := Matrix.toEuclideanCLM (n := Fin (2 ^ n)) (𝕜 := ℂ) (r.embedMatrix M)
  let TM := Matrix.toEuclideanCLM (n := Fin (2 ^ k)) (𝕜 := ℂ) M
  rw [← Matrix.l2_opNorm_toEuclideanCLM (r.embedMatrix M)]
  refine T.opNorm_le_bound (norm_nonneg M) fun x ↦
    (sq_le_sq₀ (by positivity) (by positivity)).mp ?_
  rw [mul_pow, EuclideanSpace.norm_sq_eq (T x), Matrix.ofLp_toEuclideanCLM,
    ← r.basisSplitEquiv.symm.sum_comp (fun i ↦ ‖((r.embedMatrix M).mulVec x.ofLp) i‖ ^ 2),
    Fintype.sum_prod_type_right, EuclideanSpace.norm_sq_eq x,
    ← r.basisSplitEquiv.symm.sum_comp (fun i ↦ ‖x.ofLp i‖ ^ 2),
    Fintype.sum_prod_type_right, Finset.mul_sum]
  refine Finset.sum_le_sum fun env _ ↦ ?_
  let x_env : EuclideanSpace ℂ (Fin (2 ^ k)) :=
    WithLp.toLp 2 (fun j ↦ x.ofLp (r.basisSplitEquiv.symm (j, env)))
  have hmul (j : Fin (2 ^ k)) : ((r.embedMatrix M).mulVec x.ofLp)
      (r.basisSplitEquiv.symm (j, env)) = (TM x_env).ofLp j := by
    rw [Matrix.ofLp_toEuclideanCLM, r.embedMatrix_mulVec_apply,
      ← QRegister.basisSplitEquiv_apply_fst, Equiv.apply_symm_apply]
    rfl
  simp_rw [hmul]
  rw [← EuclideanSpace.norm_sq_eq (TM x_env),
    show (∑ j : Fin (2 ^ k), ‖x.ofLp (r.basisSplitEquiv.symm (j, env))‖ ^ 2) = ‖x_env‖ ^ 2 from
      (EuclideanSpace.norm_sq_eq x_env).symm, ← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (Matrix.l2_opNorm_toEuclideanCLM M ▸ TM.le_opNorm x_env) 2
end TaylorChebyshevBridge
section TFreeRyApproxCircuit
variable {n : ℕ}
structure DyadicRyGate where
  T0 : ℕ
  T1 : ℕ
  neg_c : Bool
  neg_s : Bool
end TFreeRyApproxCircuit
section FiveTermSegmentErrorBound
theorem norm_mul_le_of_left_le_one {A : Type*} [NormedRing A] {U X : A} (hU : ‖U‖ ≤ 1) :
    ‖U * X‖ ≤ ‖X‖ :=
  (norm_mul_le U X).trans (by simpa using mul_le_mul_of_nonneg_right hU (norm_nonneg X))
theorem norm_mul_le_of_right_le_one {A : Type*} [NormedRing A] {X U : A} (hU : ‖U‖ ≤ 1) :
    ‖X * U‖ ≤ ‖X‖ :=
  (norm_mul_le X U).trans (by simpa using mul_le_mul_of_nonneg_left hU (norm_nonneg X))
theorem sig_proj0_add_proj1 {n : ℕ} (q_sig : Wire n) :
    (QRegister.singleton q_sig).basisOutcomeProjector 0 +
      (QRegister.singleton q_sig).basisOutcomeProjector 1 = 1 := by
  have h : ∑ b : Fin 2, (QRegister.singleton q_sig).basisOutcomeProjector b = 1 :=
    (QRegister.singleton q_sig).sum_basisOutcomeProjector
  rwa [Fin.sum_univ_two] at h
theorem proj_pair_mem_unitaryGroup {n : ℕ} (P Q U : Operator (2 ^ n))
    (hU : U ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ) (hP_sa : Pᴴ = P) (hQ_sa : Qᴴ = Q)
    (hPP : P * P = P) (hQQ : Q * Q = Q) (hPQ : P * Q = 0) (hQP : Q * P = 0)
    (hadd : P + Q = 1) (hcomm : U * P = P * U) :
    U * P + Q ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  have hPs : star P = P := by rwa [Matrix.star_eq_conjTranspose]
  have hQs : star Q = Q := by rwa [Matrix.star_eq_conjTranspose]
  have hcs : P * star U = star U * P := by simpa [star_mul, hPs] using congrArg star hcomm
  calc star (U * P + Q) * (U * P + Q)
    _ = P * (star U * U) * P + (P * star U) * Q + Q * (U * P) + Q * Q := by
        rw [star_add, star_mul, hPs, hQs]
        noncomm_ring
    _ = P * P + star U * (P * Q) + (Q * P) * U + Q := by
        rw [hU.1, hcs, hcomm, hQQ]
        noncomm_ring
    _ = 1 := by rw [hPP, hPQ, hQP, mul_zero, zero_mul, add_zero, add_zero, hadd]
theorem c0_step_mem_unitaryGroup {n : ℕ} (q_sig : Wire n) (U : Operator (2 ^ n))
    (hU : U ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ)
    (hcomm0 : U * (QRegister.singleton q_sig).basisOutcomeProjector 0 =
      (QRegister.singleton q_sig).basisOutcomeProjector 0 * U) :
    let P_sig0 := (QRegister.singleton q_sig).basisOutcomeProjector 0
    let P_sig1 := (QRegister.singleton q_sig).basisOutcomeProjector 1
    U * P_sig0 + P_sig1 ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ :=
  proj_pair_mem_unitaryGroup _ _ U hU
    ((QRegister.singleton q_sig).basisOutcomeProjector_conjTranspose 0)
    ((QRegister.singleton q_sig).basisOutcomeProjector_conjTranspose 1)
    ((QRegister.singleton q_sig).basisOutcomeProjector_mul_self 0)
    ((QRegister.singleton q_sig).basisOutcomeProjector_mul_self 1)
    (sig_proj_mul_of_ne q_sig (by decide)) (sig_proj_mul_of_ne q_sig (by decide))
    (sig_proj0_add_proj1 q_sig) hcomm0
theorem c1_step_mem_unitaryGroup {n : ℕ} (q_sig : Wire n) (U : Operator (2 ^ n))
    (hU : U ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ)
    (hcomm1 : U * (QRegister.singleton q_sig).basisOutcomeProjector 1 =
      (QRegister.singleton q_sig).basisOutcomeProjector 1 * U) :
    let P_sig0 := (QRegister.singleton q_sig).basisOutcomeProjector 0
    let P_sig1 := (QRegister.singleton q_sig).basisOutcomeProjector 1
    P_sig0 + U * P_sig1 ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ := by
  intro P_sig0 P_sig1
  rw [add_comm]
  exact proj_pair_mem_unitaryGroup P_sig1 P_sig0 U hU
    ((QRegister.singleton q_sig).basisOutcomeProjector_conjTranspose 1)
    ((QRegister.singleton q_sig).basisOutcomeProjector_conjTranspose 0)
    ((QRegister.singleton q_sig).basisOutcomeProjector_mul_self 1)
    ((QRegister.singleton q_sig).basisOutcomeProjector_mul_self 0)
    (sig_proj_mul_of_ne q_sig (by decide)) (sig_proj_mul_of_ne q_sig (by decide))
    ((add_comm P_sig1 P_sig0).trans (sig_proj0_add_proj1 q_sig)) hcomm1
end FiveTermSegmentErrorBound
end TFreeLaurentGQSP
namespace CatalyzedLaurentGQSP
open Operator Matrix Circuit Function SpecsAux
open PhaseGradSignalRot TFreeLaurentGQSP
open scoped Matrix
variable {n : ℕ}
section RyMatrixLipschitz
@[simp] theorem phaseGrad_ryMatrix_eq (c s : ℝ) :
    PhaseGradSignalRot.ryMatrix c s =
      TFreeLaurentGQSP.ryMatrix c s := rfl
theorem ryMatrix_sub (c₁ s₁ c₂ s₂ : ℝ) : TFreeLaurentGQSP.ryMatrix c₁ s₁ -
    TFreeLaurentGQSP.ryMatrix c₂ s₂ = TFreeLaurentGQSP.ryMatrix (c₁ - c₂) (s₁ - s₂) := by
  simp only [TFreeLaurentGQSP.ryMatrix, Complex.ofReal_sub, sub_smul]
  abel
open scoped Matrix.Norms.L2Operator in
theorem norm_ryMatrix_le_of_sq_le (c s B : ℝ) (hB : 0 ≤ B) (hcs : c ^ 2 + s ^ 2 ≤ B ^ 2) :
    ‖TFreeLaurentGQSP.ryMatrix c s‖ ≤ B := by
  let M := TFreeLaurentGQSP.ryMatrix c s
  have h1_norm : ‖(1 : Operator 2)‖ ≤ 1 := TFreeLaurentGQSP.norm_of_mem_unitaryGroup_le_one
    (Submonoid.one_mem (Matrix.unitaryGroup (Fin 2) ℂ))
  have hsq : ‖M‖ * ‖M‖ ≤ B * B := by
    rw [← Matrix.l2_opNorm_conjTranspose_mul_self M,
      show M = PhaseGradSignalRot.ryMatrix c s from rfl,
      PhaseGradSignalRot.ryMatrix_conjTranspose_mul_self,
      norm_smul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    nlinarith [norm_nonneg (1 : Operator 2)]
  nlinarith [norm_nonneg M]
open scoped Matrix.Norms.L2Operator in
theorem norm_ryMatrix_cos_sin_sub_le (θ₁ θ₂ : ℝ) :
    ‖TFreeLaurentGQSP.ryMatrix (Real.cos (θ₁ / 2)) (Real.sin (θ₁ / 2)) -
        TFreeLaurentGQSP.ryMatrix (Real.cos (θ₂ / 2)) (Real.sin (θ₂ / 2))‖ ≤
      |θ₁ - θ₂| / 2 := by
  rw [ryMatrix_sub]
  refine norm_ryMatrix_le_of_sq_le _ _ (|θ₁ - θ₂| / 2) (by positivity) ?_
  have htrig : (Real.cos (θ₁ / 2) - Real.cos (θ₂ / 2)) ^ 2 +
      (Real.sin (θ₁ / 2) - Real.sin (θ₂ / 2)) ^ 2 = 4 * Real.sin ((θ₁ - θ₂) / 4) ^ 2 := by
    have hcos2 : Real.cos (θ₁ / 2 - θ₂ / 2) =
        Real.cos ((θ₁ - θ₂) / 4) ^ 2 - Real.sin ((θ₁ - θ₂) / 4) ^ 2 := by
      rw [show θ₁ / 2 - θ₂ / 2 = (θ₁ - θ₂) / 4 + (θ₁ - θ₂) / 4 by ring, Real.cos_add]
      ring
    linear_combination Real.cos_sq_add_sin_sq (θ₁ / 2) + Real.cos_sq_add_sin_sq (θ₂ / 2) +
      2 * Real.cos_sub (θ₁ / 2) (θ₂ / 2) - 2 * hcos2 -
      2 * Real.cos_sq_add_sin_sq ((θ₁ - θ₂) / 4)
  rw [htrig, div_pow, sq_abs]
  linarith [show Real.sin ((θ₁ - θ₂) / 4) ^ 2 ≤ ((θ₁ - θ₂) / 4) ^ 2 by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) Real.abs_sin_le_abs 2]
noncomputable def catAngle42 (C_d : Fin (2 ^ 42)) : ℝ := -((4 * Real.pi * (C_d.val : ℝ)) / 2 ^ 42)
noncomputable def catCS42 (C_d : Fin (2 ^ 42)) : ℝ × ℝ :=
  (Real.cos (catAngle42 C_d / 2), Real.sin (catAngle42 C_d / 2))
theorem ryUnitary_catAngle42_val (C_d : Fin (2 ^ 42)) : (ryUnitary (catAngle42 C_d)).1 =
    TFreeLaurentGQSP.ryMatrix (catCS42 C_d).1 (catCS42 C_d).2 := by
  rw [ryUnitary_val, phaseGrad_ryMatrix_eq]
  rfl
end RyMatrixLipschitz
end CatalyzedLaurentGQSP
namespace BidirectionalCatalyzedGQSP
open Operator Matrix Circuit Function SpecsAux
open PhaseGradSignalRot TFreeLaurentGQSP
open CatalyzedLaurentGQSP
open scoped Matrix
variable {n : ℕ}
section ZeroFlagAndCZFlag
theorem basisOutcomeProjector_comm {a b : ℕ} (r₁ : QRegister a n) (r₂ : QRegister b n)
    (x : Fin (2 ^ a)) (y : Fin (2 ^ b)) : r₁.basisOutcomeProjector x *
    r₂.basisOutcomeProjector y = r₂.basisOutcomeProjector y * r₁.basisOutcomeProjector x := by
  rw [QRegister.basisOutcomeProjector_eq_diagonal, QRegister.basisOutcomeProjector_eq_diagonal,
    Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  exact congrArg Matrix.diagonal (funext fun _ ↦ mul_comm _ _)
end ZeroFlagAndCZFlag
section MergedReflRot
noncomputable def ctrlNegRefl (b : Bool) (q_sig : Wire n) (R0_emb : Operator (2 ^ n)) :
    Operator (2 ^ n) :=
  let P0 := (QRegister.singleton q_sig).basisOutcomeProjector 0
  let P1 := (QRegister.singleton q_sig).basisOutcomeProjector 1
  if b then P0 - R0_emb * P1 else -(R0_emb * P0) + P1
end MergedReflRot
section BidirectionalWalkAndSegment
theorem sig_block_diag_mul (q_sig : Wire n) (A0 A1 B0 B1 : Operator (2 ^ n))
    (hB0_0 : B0 * (QRegister.singleton q_sig).basisOutcomeProjector 0 =
      (QRegister.singleton q_sig).basisOutcomeProjector 0 * B0)
    (hB0_1 : B0 * (QRegister.singleton q_sig).basisOutcomeProjector 1 =
      (QRegister.singleton q_sig).basisOutcomeProjector 1 * B0)
    (hB1_0 : B1 * (QRegister.singleton q_sig).basisOutcomeProjector 0 =
      (QRegister.singleton q_sig).basisOutcomeProjector 0 * B1)
    (hB1_1 : B1 * (QRegister.singleton q_sig).basisOutcomeProjector 1 =
      (QRegister.singleton q_sig).basisOutcomeProjector 1 * B1) :
    let P0 := (QRegister.singleton q_sig).basisOutcomeProjector 0
    let P1 := (QRegister.singleton q_sig).basisOutcomeProjector 1
    (A0 * P0 + A1 * P1) * (B0 * P0 + B1 * P1) = (A0 * B0) * P0 + (A1 * B1) * P1 := by
  intro P0 P1
  calc (A0 * P0 + A1 * P1) * (B0 * P0 + B1 * P1)
    _ = A0 * (P0 * B0) * P0 + A0 * (P0 * B1) * P1 +
          A1 * (P1 * B0) * P0 + A1 * (P1 * B1) * P1 := by noncomm_ring
    _ = (A0 * B0) * (P0 * P0) + (A0 * B1) * (P0 * P1) +
          (A1 * B0) * (P1 * P0) + (A1 * B1) * (P1 * P1) := by
        rw [← hB0_0, ← hB1_0, ← hB0_1, ← hB1_1]
        noncomm_ring
    _ = (A0 * B0) * P0 + (A1 * B1) * P1 := by
        rw [(QRegister.singleton q_sig).basisOutcomeProjector_mul_self 0,
          (QRegister.singleton q_sig).basisOutcomeProjector_mul_self 1,
          TFreeLaurentGQSP.sig_proj_mul_of_ne q_sig (by decide),
          TFreeLaurentGQSP.sig_proj_mul_of_ne q_sig (by decide)]
        noncomm_ring
def biCode (M : ℕ) (C : Fin (M + 1) → Fin (2 ^ 42)) (j : ℕ) : Fin (2 ^ 42) :=
  if hj : j < M + 1 then C ⟨j, hj⟩ else 0
noncomputable def biCS (M : ℕ) (C : Fin (M + 1) → Fin (2 ^ 42)) (j : ℕ) : ℝ × ℝ :=
  catCS42 (biCode M C j)
noncomputable def biWalkStepOp (q_sig : Wire n) (W_emb W_inv_emb : Operator (2 ^ n)) :
    Operator (2 ^ n) := W_emb * (QRegister.singleton q_sig).basisOutcomeProjector 0 +
    W_inv_emb * (QRegister.singleton q_sig).basisOutcomeProjector 1
noncomputable def biGqspLoopOp (q_sig : Wire n) (W_emb W_inv_emb : Operator (2 ^ n))
    (cs : ℕ → ℝ × ℝ) : ℕ → Operator (2 ^ n)
  | 0 => (QRegister.singleton q_sig).embedMatrix (TFreeLaurentGQSP.ryMatrix (cs 0).1 (cs 0).2)
  | t + 1 => ((QRegister.singleton q_sig).embedMatrix
      (TFreeLaurentGQSP.ryMatrix (cs (t + 1)).1 (cs (t + 1)).2) *
      biWalkStepOp q_sig W_emb W_inv_emb) * biGqspLoopOp q_sig W_emb W_inv_emb cs t
noncomputable def biGqspSegmentOp (q_sig : Wire n) (W_emb W_inv_emb : Operator (2 ^ n))
    (cs : ℕ → ℝ × ℝ) (M : ℕ) : Operator (2 ^ n) :=
  let P_sig0 := (QRegister.singleton q_sig).basisOutcomeProjector 0
  let P_sig1 := (QRegister.singleton q_sig).basisOutcomeProjector 1
  let H_sig := (Circuit.H q_sig).eval.1
  H_sig * (W_inv_emb * P_sig0 + P_sig1) * biGqspLoopOp q_sig W_emb W_inv_emb cs M *
    (P_sig0 + W_emb * P_sig1) * H_sig
theorem local_diagNegIPosI_eq : Qubit.S.1 * ((Qubit.X.1 * (Qubit.Z.1 * Qubit.S.1)) * Qubit.X.1) =
      (-Complex.I) • compProj (0 : Fin 2) + Complex.I • compProj (1 : Fin 2) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Qubit.S, Qubit.X, Qubit.Z, compProj, Matrix.single, Matrix.mul_apply, Fin.sum_univ_two]
theorem local_Z_mul_S_eq : Qubit.Z.1 * Qubit.S.1 = compProj (0 : Fin 2) + (-Complex.I) •
    compProj (1 : Fin 2) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Qubit.S, Qubit.Z, compProj, Matrix.single, Matrix.mul_apply, Fin.sum_univ_two]
def diagNegIPosICircuit (q_sig : Wire n) : Circuit n := ((Circuit.X q_sig).seq (((Circuit.S
    q_sig).seq (Circuit.Z q_sig)).seq (Circuit.X q_sig))).seq (Circuit.S q_sig)
@[simp] theorem diagNegIPosICircuit_count_T (q_sig : Wire n) :
    (diagNegIPosICircuit q_sig).count PrimitiveGate.T = 0 := by
  simp [diagNegIPosICircuit, Circuit.X, Circuit.S, Circuit.Z, Circuit.single]
@[simp] theorem diagNegIPosICircuit_count_TOFF (q_sig : Wire n) :
    (diagNegIPosICircuit q_sig).count PrimitiveGate.TOFF = 0 := by
  simp [diagNegIPosICircuit, Circuit.X, Circuit.S, Circuit.Z, Circuit.single]
theorem diagNegIPosICircuit_eval_eq_proj (q_sig : Wire n) : (diagNegIPosICircuit q_sig).eval.1 =
    ((-Complex.I) • (1 : Operator (2 ^ n))) * (QRegister.singleton q_sig).basisOutcomeProjector
    0 + (Complex.I • (1 : Operator (2 ^ n))) *
    (QRegister.singleton q_sig).basisOutcomeProjector 1 := by
  let rSig := QRegister.singleton q_sig
  unfold diagNegIPosICircuit
  simp only [Circuit.eval_seq, Submonoid.coe_mul, Circuit.X, Circuit.S, Circuit.Z,
    Circuit.eval_single, QRegister.embedUnitary_val, PrimitiveGate.eval,
    ← QRegister.embedMatrix_mul]
  rw [local_diagNegIPosI_eq, rSig.embedMatrix_add, rSig.embedMatrix_smul, rSig.embedMatrix_smul,
    smul_mul_assoc, one_mul, smul_mul_assoc, one_mul]
  rfl
theorem eval_SZ_eq_proj (q_sig : Wire n) : ((Circuit.S q_sig).seq (Circuit.Z q_sig)).eval.1 =
      (1 : Operator (2 ^ n)) * (QRegister.singleton q_sig).basisOutcomeProjector 0 +
      ((-Complex.I) • (1 : Operator (2 ^ n))) *
        (QRegister.singleton q_sig).basisOutcomeProjector 1 := by
  let rSig := QRegister.singleton q_sig
  simp only [Circuit.eval_seq, Submonoid.coe_mul, Circuit.S, Circuit.Z, Circuit.eval_single,
    QRegister.embedUnitary_val, PrimitiveGate.eval, ← QRegister.embedMatrix_mul]
  rw [local_Z_mul_S_eq, rSig.embedMatrix_add, rSig.embedMatrix_smul, one_mul, smul_mul_assoc,
    one_mul]
  rfl
theorem ctrlNegRefl_false_eq (q_sig : Wire n) (R0_emb : Operator (2 ^ n)) : ctrlNegRefl false
    q_sig R0_emb = (-R0_emb) * (QRegister.singleton q_sig).basisOutcomeProjector 0 +
    (1 : Operator (2 ^ n)) * (QRegister.singleton q_sig).basisOutcomeProjector 1 := by
  simp only [ctrlNegRefl, Bool.false_eq_true, ↓reduceIte, neg_mul, one_mul]
theorem ctrlNegRefl_true_eq (q_sig : Wire n) (R0_emb : Operator (2 ^ n)) : ctrlNegRefl true
    q_sig R0_emb = (1 : Operator (2 ^ n)) * (QRegister.singleton q_sig).basisOutcomeProjector
    0 + (-R0_emb) * (QRegister.singleton q_sig).basisOutcomeProjector 1 := by
  simp only [ctrlNegRefl, ↓reduceIte, sub_eq_add_neg, neg_mul, one_mul]
theorem biRightBoundary_refl_algebra (q_sig : Wire n) (R0_emb U_BE_emb : Operator (2 ^ n))
    (hU0 : U_BE_emb * (QRegister.singleton q_sig).basisOutcomeProjector 0 =
      (QRegister.singleton q_sig).basisOutcomeProjector 0 * U_BE_emb)
    (hU1 : U_BE_emb * (QRegister.singleton q_sig).basisOutcomeProjector 1 =
      (QRegister.singleton q_sig).basisOutcomeProjector 1 * U_BE_emb) :
    let P0 := (QRegister.singleton q_sig).basisOutcomeProjector 0
    let P1 := (QRegister.singleton q_sig).basisOutcomeProjector 1
    ctrlNegRefl true q_sig R0_emb *
      ((1 : Operator (2 ^ n)) * P0 + ((-Complex.I) • U_BE_emb) * P1) =
    P0 + (Complex.I • (R0_emb * U_BE_emb)) * P1 := by
  intro P0 P1
  rw [ctrlNegRefl_true_eq, sig_block_diag_mul q_sig 1 (-R0_emb) 1 ((-Complex.I) • U_BE_emb)
    (by rw [one_mul, mul_one]) (by rw [one_mul, mul_one])
    (by rw [smul_mul_assoc, hU0, mul_smul_comm]) (by rw [smul_mul_assoc, hU1, mul_smul_comm]),
    mul_one, one_mul, neg_mul, mul_smul_comm, ← neg_smul, neg_neg]
theorem biInteriorWalk_refl_algebra (q_sig : Wire n) (R0_emb U_BE_emb : Operator (2 ^ n))
    (hU0 : U_BE_emb * (QRegister.singleton q_sig).basisOutcomeProjector 0 =
      (QRegister.singleton q_sig).basisOutcomeProjector 0 * U_BE_emb)
    (hU1 : U_BE_emb * (QRegister.singleton q_sig).basisOutcomeProjector 1 =
      (QRegister.singleton q_sig).basisOutcomeProjector 1 * U_BE_emb)
    (hR0 : R0_emb * (QRegister.singleton q_sig).basisOutcomeProjector 0 =
      (QRegister.singleton q_sig).basisOutcomeProjector 0 * R0_emb)
    (hR1 : R0_emb * (QRegister.singleton q_sig).basisOutcomeProjector 1 =
      (QRegister.singleton q_sig).basisOutcomeProjector 1 * R0_emb) :
    let P0 := (QRegister.singleton q_sig).basisOutcomeProjector 0
    let P1 := (QRegister.singleton q_sig).basisOutcomeProjector 1
    ctrlNegRefl false q_sig R0_emb *
      (((-Complex.I) • U_BE_emb) * P0 + (Complex.I • U_BE_emb) * P1) *
      ctrlNegRefl true q_sig R0_emb =
    (Complex.I • (R0_emb * U_BE_emb)) * P0 + ((-Complex.I) • (U_BE_emb * R0_emb)) * P1 := by
  intro P0 P1
  rw [ctrlNegRefl_false_eq, ctrlNegRefl_true_eq,
    sig_block_diag_mul q_sig (-R0_emb) 1 ((-Complex.I) • U_BE_emb) (Complex.I • U_BE_emb)
      (by rw [smul_mul_assoc, hU0, mul_smul_comm]) (by rw [smul_mul_assoc, hU1, mul_smul_comm])
      (by rw [smul_mul_assoc, hU0, mul_smul_comm]) (by rw [smul_mul_assoc, hU1, mul_smul_comm]),
    sig_block_diag_mul q_sig ((-R0_emb) * ((-Complex.I) • U_BE_emb))
      (1 * (Complex.I • U_BE_emb)) 1 (-R0_emb) (by rw [one_mul, mul_one])
      (by rw [one_mul, mul_one]) (by rw [neg_mul, hR0, mul_neg])
      (by rw [neg_mul, hR1, mul_neg])]
  exact congrArg₂ (· + ·)
    (by rw [mul_one, neg_mul, mul_smul_comm, ← neg_smul, neg_neg])
    (by rw [one_mul, mul_neg, smul_mul_assoc, ← neg_smul])
end BidirectionalWalkAndSegment
end BidirectionalCatalyzedGQSP
namespace TFreeLaurentGQSPPresets
open Operator Matrix Circuit SpecsAux TFreeLaurentGQSP
open scoped Matrix
section IntegerScaledVerification
def gateNc (g : DyadicRyGate) : ℤ := if g.neg_c then -(g.T0 : ℤ) else (g.T0 : ℤ)
def gateNs (g : DyadicRyGate) : ℤ :=
  if g.neg_c != g.neg_s then -((g.T1 - g.T0 : ℕ) : ℤ) else ((g.T1 - g.T0 : ℕ) : ℤ)
noncomputable def gateCos (b : ℕ) (g : DyadicRyGate) : ℝ := (gateNc g : ℝ) / (2 ^ b : ℝ)
noncomputable def gateSin (b : ℕ) (g : DyadicRyGate) : ℝ := (gateNs g : ℝ) / (2 ^ b : ℝ)
noncomputable def gatePair (b : ℕ) (g : DyadicRyGate) : ℝ × ℝ := (gateCos b g, gateSin b g)
def defaultGate : DyadicRyGate := ⟨0,0, false, false⟩
theorem gateCos_sq_add_gateSin_sq_le_one (b : ℕ) (g : DyadicRyGate)
    (h : gateNc g ^ 2 + gateNs g ^ 2 ≤ (2 ^ (2 * b) : ℤ)) :
    gateCos b g ^ 2 + gateSin b g ^ 2 ≤ 1 := by
  rw [gateCos, gateSin, div_pow, div_pow, ← add_div, div_le_one (by positivity),
    ← pow_mul, mul_comm b 2]
  exact_mod_cast h
end IntegerScaledVerification
namespace FastRecurrenceVerifier
def forceNatFast {α : Type*} (x : ℕ) (f : ℕ → α) : α := match x with
  | 0 => f 0
  | Nat.succ k => f (Nat.add k 1)
theorem forceNatFast_eq {α : Type*} (x : ℕ) (f : ℕ → α) : forceNatFast x f = f x := by
  rcases x with _ | k <;> rfl
def smToInt (s : Bool) (m : ℕ) : ℤ := if s then -(m : ℤ) else (m : ℤ)
@[simp] theorem smToInt_false (m : ℕ) : smToInt false m = (m : ℤ) := rfl
@[simp] theorem smToInt_true (m : ℕ) : smToInt true m = -(m : ℤ) := rfl
@[simp] theorem smToInt_zero (s : Bool) : smToInt s 0 = 0 := by cases s <;> rfl
theorem smToInt_mul (s1 : Bool) (m1 : ℕ) (s2 : Bool) (m2 : ℕ) :
    smToInt (xor s1 s2) (Nat.mul m1 m2) = smToInt s1 m1 * smToInt s2 m2 := by
  cases s1 <;> cases s2 <;> simp [smToInt, Nat.mul_eq]
theorem smToInt_neg (s : Bool) (m : ℕ) : smToInt (Bool.not s) m = - smToInt s m := by
  cases s <;> simp [smToInt]
def smAdd {α : Type*} (s1 : Bool) (m1 : ℕ) (s2 : Bool) (m2 : ℕ) (f : Bool → ℕ → α) : α :=
  match xor s1 s2 with
  | false => forceNatFast (Nat.add m1 m2) (f s1)
  | true =>
      match Nat.ble m2 m1 with
      | true => forceNatFast (Nat.sub m1 m2) (f s1)
      | false => forceNatFast (Nat.sub m2 m1) (f s2)
theorem smAdd_eq_pair {α : Type*} (s1 : Bool) (m1 : ℕ) (s2 : Bool) (m2 : ℕ) (f : Bool → ℕ → α) :
    smAdd s1 m1 s2 m2 f = let res := smAdd s1 m1 s2 m2 (fun s m ↦ (s, m))
      f res.1 res.2 := by
  unfold smAdd
  cases xor s1 s2 <;> simp only [forceNatFast_eq]
  cases Nat.ble m2 m1 <;> rfl
theorem smToInt_smAdd (s1 : Bool) (m1 : ℕ) (s2 : Bool) (m2 : ℕ) :
    smAdd s1 m1 s2 m2 smToInt = smToInt s1 m1 + smToInt s2 m2 := by
  unfold smAdd smToInt
  have hb : Nat.ble m2 m1 = decide (m2 ≤ m1) :=
    Bool.eq_iff_iff.mpr (Iff.trans (by rw [Nat.ble_eq]) decide_eq_true_iff.symm)
  rw [hb]
  cases s1
  · cases s2
    · simp [forceNatFast_eq]
    · by_cases h : m2 ≤ m1
      · simp [h, forceNatFast_eq, Nat.sub_eq]
        omega
      · simp [h, forceNatFast_eq, Nat.sub_eq]
        omega
  · cases s2
    · by_cases h : m2 ≤ m1
      · simp [h, forceNatFast_eq, Nat.sub_eq]
        omega
      · simp [h, forceNatFast_eq, Nat.sub_eq]
        omega
    · simp [forceNatFast_eq]
      omega
def smAbsDiff (s1 : Bool) (m1 : ℕ) (s2 : Bool) (m2 : ℕ) : ℕ :=
  smAdd s1 m1 (Bool.not s2) m2 (fun _ m ↦ m)
theorem smAbsDiff_cast_eq (s1 : Bool) (m1 : ℕ) (s2 : Bool) (m2 : ℕ) :
    ((smAbsDiff s1 m1 s2 m2 : ℕ) : ℤ) = |smToInt s1 m1 - smToInt s2 m2| := by
  unfold smAbsDiff
  let res := smAdd s1 m1 (Bool.not s2) m2 (fun s m ↦ (s, m))
  have habs : |smToInt res.1 res.2| = (res.2 : ℤ) := by
    cases res.1
    · simp [smToInt]
    · simp [smToInt]
  rw [smAdd_eq_pair s1 m1 (Bool.not s2) m2 (fun _ m ↦ m), ← habs,
    ← smAdd_eq_pair s1 m1 (Bool.not s2) m2 smToInt, smToInt_smAdd, smToInt_neg, sub_eq_add_neg]
def gateSM (g : DyadicRyGate) : (Bool × ℕ) × (Bool × ℕ) :=
  ((g.neg_c, g.T0),(xor g.neg_c g.neg_s, Nat.sub g.T1 g.T0))
theorem gateSM_toInt (g : DyadicRyGate) : smToInt (gateSM g).1.1 (gateSM g).1.2 = gateNc g ∧
    smToInt (gateSM g).2.1 (gateSM g).2.2 = gateNs g := by
  unfold gateSM gateNc gateNs smToInt
  constructor
  · rfl
  · cases g.neg_c <;> cases g.neg_s <;> simp [Nat.sub_eq]
end FastRecurrenceVerifier
namespace FastIntervalRecurrenceVerifier
open TFreeLaurentGQSPPresets
open TFreeLaurentGQSPPresets.FastRecurrenceVerifier
def powMulFast (D : ℕ) : ℕ → ℕ → ℕ
  | 0, acc => acc
  | k + 1, acc => forceNatFast (Nat.mul D acc) fun acc' ↦ powMulFast D k acc'
structure PQPair where
  p : ℕ
  q : ℕ
@[inline] def mkPQConsLazy (np nq : ℕ) (rest : List PQPair) : List PQPair :=
  match np, nq with
  | 0,0 => ⟨0,0⟩ :: rest
  | 0, b + 1 => ⟨0, Nat.add b 1⟩ :: rest
  | a + 1,0 => ⟨Nat.add a 1,0⟩ :: rest
  | a + 1, b + 1 => ⟨Nat.add a 1, Nat.add b 1⟩ :: rest
theorem mkPQConsLazy_eq (np nq : ℕ) (rest : List PQPair) :
    mkPQConsLazy np nq rest = ⟨np, nq⟩ :: rest := by
  rcases np with _ | a <;> rcases nq with _ | b <;> rfl
noncomputable def chebTermExact (β_nat scale0 n d : ℕ) : ℝ := (scale0 : ℝ) *
    ((n.factorial : ℝ)⁻¹ * (β_nat : ℝ) ^ n) * ((powChebScaled n d : ℝ) * ((2 : ℝ) ^ n)⁻¹)
theorem chebTermExact_eq_zero_of_lt {β_nat scale0 n d : ℕ} (h : n < d) :
    chebTermExact β_nat scale0 n d = 0 := by
  simp [chebTermExact, powChebScaled_eq_zero_of_lt h]
def wMult (d : ℕ) : ℕ := if d = 0 then 1 else 2
theorem wMult_pos (d : ℕ) : 1 ≤ wMult d ∧ wMult d ≤ 2 := by
  unfold wMult
  split_ifs <;> omega
section MasterCertificate
theorem abs_sub_add_le_three (a b c : ℝ) : |a - b + c| ≤ |a| + |b| + |c| := by
  linarith [abs_add_le (a - b) c, abs_sub a b]
theorem abs_add_sub_add_le_four (a b c d : ℝ) : |a + b - c + d| ≤ |a| + |b| + |c| + |d| := by
  linarith [abs_add_le (a + b - c) d, abs_sub (a + b) c, abs_add_le a b]
@[inline] def natAbsDiff (a b : ℕ) : ℕ :=
  match Nat.ble a b with
  | true => Nat.sub b a
  | false => Nat.sub a b
theorem natAbsDiff_cast_real (a b : ℕ) : (natAbsDiff a b : ℝ) = |(a : ℝ) - (b : ℝ)| := by
  unfold natAbsDiff
  rcases h : Nat.ble a b with _ | _
  · have hba : b ≤ a :=
      (Nat.not_le.mp (fun hab ↦ Bool.noConfusion (h.symm.trans (Nat.ble_eq.mpr hab)))).le
    simp only [Nat.sub_eq, Nat.cast_sub hba]
    exact (abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast hba))).symm
  · have hab : a ≤ b := Nat.ble_eq.mp h
    simp only [Nat.sub_eq, Nat.cast_sub hab, abs_sub_comm (a : ℝ)]
    exact (abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast hab))).symm
@[inline] def uParityFlip (d B2 u : ℕ) : ℕ :=
  if Nat.beq (Nat.mod d 2) 1 then Nat.sub B2 u else u
theorem uParityFlip_spec (d B B2 u : ℕ) (X R : ℝ) (hB2 : B2 = 2 * B)
    (hu_mag : |(u : ℤ) - (B : ℤ)| ≤ (B : ℤ)) (hu_err : |X - ((u : ℝ) - (B : ℝ))| ≤ R) :
    |((-1 : ℝ) ^ d * X) - ((uParityFlip d B2 u : ℝ) - (B : ℝ))| ≤ R := by
  have hu_le : u ≤ B2 := by
    have := (abs_le.mp hu_mag).2
    omega
  unfold uParityFlip
  rcases (by omega : d % 2 = 0 ∨ d % 2 = 1) with h0 | h1
  · simpa [show Nat.beq (Nat.mod d 2) 1 = false by
        change Nat.beq (d % 2) 1 = false
        rw [h0]
        rfl,
      Even.neg_one_pow (Nat.even_iff.mpr h0)] using hu_err
  · simp only [show Nat.beq (Nat.mod d 2) 1 = true by
        change Nat.beq (d % 2) 1 = true
        rw [h1]
        rfl, ↓reduceIte, Nat.sub_eq]
    rw [Nat.cast_sub hu_le, hB2, Odd.neg_one_pow (Nat.odd_iff.mpr h1)]
    push_cast
    rwa [show -1 * X - (2 * (B : ℝ) - (u : ℝ) - (B : ℝ)) = -(X - ((u : ℝ) - (B : ℝ))) by ring,
      abs_neg]
def chebL1SumBiased (M : ℕ) (B B2 Bw R_final W_err_d0 W_err_dpos : ℕ)
    (pq : List PQPair) : ℕ → List ℕ → ℕ → ℕ
  | _, [], acc => acc
  | d, w :: wt, acc =>
      let term := if Nat.beq d 0 then
          Nat.add (natAbsDiff (Nat.add (pq.getD M ⟨B, B⟩).p Bw) (Nat.add w B))
            (Nat.add R_final W_err_d0)
        else if Nat.ble d M then
          Nat.add (natAbsDiff (Nat.add (Nat.add (uParityFlip d B2 (pq.getD (Nat.add M d) ⟨B, B⟩).p)
            (pq.getD (Nat.sub M d) ⟨B, B⟩).p) Bw) (Nat.add w B2))
            (Nat.add (Nat.mul 2 R_final) W_err_dpos)
        else Nat.add (natAbsDiff w Bw) W_err_dpos
      forceNatFast (Nat.add acc term) fun acc' ↦
        chebL1SumBiased M B B2 Bw R_final W_err_d0 W_err_dpos pq (Nat.add d 1) wt acc'
def asymDefectSumBiased (M B B2 R_final : ℕ) (pq : List PQPair) : ℕ → ℕ → ℕ
  | 0, acc => acc
  | j + 1, acc =>
      let d := Nat.add j 1
      let term := Nat.add (natAbsDiff (uParityFlip d B2 (pq.getD (Nat.add M d) ⟨B, B⟩).p)
        (pq.getD (Nat.sub M d) ⟨B, B⟩).p) (Nat.mul 2 R_final)
      forceNatFast (Nat.add acc term) fun acc' ↦ asymDefectSumBiased M B B2 R_final pq j acc'
theorem asymDefectSumBiased_spec (M scale0 B B2 R_final : ℕ) (hB2 : B2 = 2 * B)
    (pq : List PQPair) (p : Fin (2 * M + 1) → ℝ)
    (hpq : ∀ k (hk : k < 2 * M + 1), let pk := (pq.getD k ⟨B, B⟩).p
      |(pk : ℤ) - (B : ℤ)| ≤ (B : ℤ) ∧
      |(scale0 : ℝ) * p ⟨k, hk⟩ - ((pk : ℝ) - (B : ℝ))| ≤ (R_final : ℝ)) :
    ∀ (m : ℕ) (_ : m ≤ M) (acc : ℕ), (acc : ℝ) + (∑ j ∈ Finset.range m,
      (scale0 : ℝ) * (if hj : j < M then laurentAsymDefect M p ⟨j, hj⟩ else 0)) ≤
      (asymDefectSumBiased M B B2 R_final pq m acc : ℝ)
  | 0, _, acc => by simp [asymDefectSumBiased]
  | j + 1, hm, acc => by
    unfold asymDefectSumBiased
    simp only [forceNatFast_eq, Nat.add_eq, Nat.mul_eq, Nat.sub_eq]
    have hj_lt : j < M := by omega
    let d := j + 1
    rcases hpq (M + d) (by omega) with ⟨hpos_mag, hpos_err⟩
    rcases hpq (M - d) (by omega) with ⟨_, hneg_err⟩
    let p_pos := uParityFlip d B2 (pq.getD (M + d) ⟨B, B⟩).p
    let p_neg := (pq.getD (M - d) ⟨B, B⟩).p
    let term := natAbsDiff p_pos p_neg + 2 * R_final
    have hflip := uParityFlip_spec d B B2 (pq.getD (M + d) ⟨B, B⟩).p
      ((scale0 : ℝ) * p ⟨M + d, by omega⟩) (R_final : ℝ) hB2 hpos_mag hpos_err
    have h_term : (scale0 : ℝ) * laurentAsymDefect M p ⟨j, hj_lt⟩ ≤ (term : ℝ) := by
      unfold laurentAsymDefect
      rw [← abs_of_nonneg (Nat.cast_nonneg scale0 : (0 : ℝ) ≤ scale0), ← abs_mul, mul_sub,
        show (scale0 : ℝ) * ((-1 : ℝ) ^ d * p ⟨M + d, by omega⟩) -
            (scale0 : ℝ) * p ⟨M - d, by omega⟩ =
          ((-1 : ℝ) ^ d * ((scale0 : ℝ) * p ⟨M + d, by omega⟩) - ((p_pos : ℝ) - (B : ℝ))) -
            ((scale0 : ℝ) * p ⟨M - d, by omega⟩ - ((p_neg : ℝ) - (B : ℝ))) +
            ((p_pos : ℝ) - (p_neg : ℝ)) by ring]
      dsimp [term]
      push_cast
      linarith [abs_sub_add_le_three
        ((-1 : ℝ) ^ d * ((scale0 : ℝ) * p ⟨M + d, by omega⟩) - ((p_pos : ℝ) - (B : ℝ)))
        ((scale0 : ℝ) * p ⟨M - d, by omega⟩ - ((p_neg : ℝ) - (B : ℝ)))
        ((p_pos : ℝ) - (p_neg : ℝ)), natAbsDiff_cast_real p_pos p_neg]
    have ih := asymDefectSumBiased_spec M scale0 B B2 R_final hB2 pq p hpq j
      (by omega) (acc + term)
    rw [Finset.sum_range_succ, dite_eq_left hj_lt]
    rw [Nat.cast_add] at ih
    linarith
def qResidSumBiased (B R_final : ℕ) : List PQPair → ℕ → ℕ
  | [], acc => acc
  | ⟨_, q⟩ :: rest, acc =>
      let term := Nat.add (natAbsDiff q B) R_final
      forceNatFast (Nat.add acc term) fun acc' ↦
        qResidSumBiased B R_final rest acc'
theorem qResidSumBiased_spec (scale0 B R_final : ℕ) :
    ∀ (pq_rem : List PQPair) (q_fn : ℕ → ℝ) (acc : ℕ), (∀ k < pq_rem.length,
        |(scale0 : ℝ) * q_fn k - (((pq_rem.getD k ⟨B, B⟩).q : ℝ) - (B : ℝ))| ≤ (R_final : ℝ)) →
      (acc : ℝ) + (∑ k ∈ Finset.range pq_rem.length, (scale0 : ℝ) * |q_fn k|) ≤
        (qResidSumBiased B R_final pq_rem acc : ℝ)
  | [], _, acc, _ => by simp [qResidSumBiased]
  | ⟨_, q0⟩ :: rest, q_fn, acc, hq => by
    unfold qResidSumBiased
    simp only [forceNatFast_eq, Nat.add_eq]
    have hq0 : |(scale0 : ℝ) * q_fn 0 - ((q0 : ℝ) - (B : ℝ))| ≤ (R_final : ℝ) :=
      hq 0 (Nat.succ_pos _)
    have h_term : (scale0 : ℝ) * |q_fn 0| ≤ ((natAbsDiff q0 B + R_final : ℕ) : ℝ) := by
      rw [← abs_of_nonneg (Nat.cast_nonneg scale0 : (0 : ℝ) ≤ scale0), ← abs_mul,
        show (scale0 : ℝ) * q_fn 0 =
          ((scale0 : ℝ) * q_fn 0 - ((q0 : ℝ) - (B : ℝ))) + ((q0 : ℝ) - (B : ℝ)) by ring]
      push_cast
      linarith [abs_add_le ((scale0 : ℝ) * q_fn 0 - ((q0 : ℝ) - (B : ℝ))) ((q0 : ℝ) - (B : ℝ)),
        natAbsDiff_cast_real q0 B]
    have ih := qResidSumBiased_spec scale0 B R_final rest (fun k ↦ q_fn (k + 1))
      (acc + (natAbsDiff q0 B + R_final)) fun k hk ↦ by
        simpa [List.getD_eq_getElem?_getD] using hq (k + 1) (Nat.succ_lt_succ hk)
    rw [List.length_cons, Finset.sum_range_succ']
    rw [Nat.cast_add] at ih
    linarith
end MasterCertificate
end FastIntervalRecurrenceVerifier
end TFreeLaurentGQSPPresets
namespace CatalyzedLaurentGQSPBridge
open Real Operator Matrix Circuit SpecsAux
open TFreeLaurentGQSP CatalyzedLaurentGQSP
open TFreeLaurentGQSPPresets
open scoped Matrix
section CosSinTaylorBounds
noncomputable def cosTaylor : ℕ → ℝ → ℝ
  | 0, _ => 0
  | m + 1, x => cosTaylor m x + (-1 : ℝ) ^ m * x ^ (2 * m) / ((2 * m).factorial : ℝ)
noncomputable def sinTaylor : ℕ → ℝ → ℝ
  | 0, _ => 0
  | m + 1, x => sinTaylor m x + (-1 : ℝ) ^ m * x ^ (2 * m + 1) / ((2 * m + 1).factorial : ℝ)
theorem hasDerivAt_pow_div_fact (k : ℕ) (x : ℝ) : HasDerivAt
    (fun t : ℝ ↦ t ^ (k + 1) / ((k + 1).factorial : ℝ)) (x ^ k / (k.factorial : ℝ)) x := by
  refine ((hasDerivAt_pow (k + 1) x).div_const ((k + 1).factorial : ℝ)).congr_deriv ?_
  rw [Nat.add_sub_cancel, Nat.factorial_succ, Nat.cast_mul]
  field_simp [Nat.cast_ne_zero.mpr (Nat.succ_ne_zero k)]
theorem nonneg_of_hasDerivAt_nonneg {f f' : ℝ → ℝ} (hf0 : f 0 = 0)
    (hderiv : ∀ x, HasDerivAt f (f' x) x) (hnonneg : ∀ x ≥ 0, 0 ≤ f' x) {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ f x := by
  have hdiff : Differentiable ℝ f := fun t ↦ (hderiv t).differentiableAt
  have hmono := monotoneOn_of_deriv_nonneg (convex_Ici 0) hdiff.continuous.continuousOn
    hdiff.differentiableOn fun t ht ↦ by
      rw [interior_Ici, Set.mem_Ioi] at ht
      rw [(hderiv t).deriv]
      exact hnonneg t ht.le
  simpa only [hf0] using hmono Set.self_mem_Ici hx hx
theorem cos_sin_taylor_alternating (m : ℕ) : ∀ x ≥ 0, 0 ≤ (-1 : ℝ) ^ (m + 1) *
    (Real.cos x - cosTaylor (m + 1) x) ∧ 0 ≤ (-1 : ℝ) ^ (m + 1) *
    (Real.sin x - sinTaylor (m + 1) x) := by
  have hc0 (k : ℕ) : cosTaylor (k + 1) 0 = 1 := by
    induction k with
    | zero => simp [cosTaylor]
    | succ k ih =>
      rw [cosTaylor, ih, zero_pow (by omega : 2 * (k + 1) ≠ 0), mul_zero, zero_div, add_zero]
  have hs0 (k : ℕ) : sinTaylor k 0 = 0 := by
    induction k with
    | zero => rfl
    | succ k ih => simp [sinTaylor, ih]
  have hds (k : ℕ) (u : ℝ) : HasDerivAt (sinTaylor k) (cosTaylor k u) u := by
    induction k with
    | zero => exact hasDerivAt_const u (0 : ℝ)
    | succ k ih =>
      rw [show sinTaylor (k + 1) = fun t ↦ sinTaylor k t +
          (-1 : ℝ) ^ k * (t ^ (2 * k + 1) / ((2 * k + 1).factorial : ℝ)) from
        funext fun _ ↦ by simp [sinTaylor, mul_div_assoc]]
      exact (ih.add ((hasDerivAt_pow_div_fact (2 * k) u).const_mul _)).congr_deriv
        (by simp [cosTaylor, mul_div_assoc])
  have hdc (k : ℕ) (u : ℝ) : HasDerivAt (cosTaylor (k + 1)) (-sinTaylor k u) u := by
    induction k with
    | zero =>
      rw [show cosTaylor 1 = fun _ ↦ (1 : ℝ) from funext fun _ ↦ by simp [cosTaylor]]
      simpa [sinTaylor] using hasDerivAt_const u (1 : ℝ)
    | succ k ih =>
      rw [show cosTaylor (k + 2) = fun t ↦ cosTaylor (k + 1) t +
          (-1 : ℝ) ^ (k + 1) * (t ^ (2 * (k + 1)) / ((2 * (k + 1)).factorial : ℝ)) from
        funext fun _ ↦ by simp [cosTaylor, mul_div_assoc]]
      exact (ih.add (by simpa [Nat.mul_succ] using
        (hasDerivAt_pow_div_fact (2 * k + 1) u).const_mul ((-1 : ℝ) ^ (k + 1)))).congr_deriv
        (by
          simp only [sinTaylor, pow_succ]
          ring)
  induction m with
  | zero =>
    intro x hx
    have hc : ∀ t ≥ 0, 0 ≤ (-1 : ℝ) ^ 1 * (Real.cos t - cosTaylor 1 t) := fun t _ ↦ by
      simp only [cosTaylor, pow_zero, zero_add]
      linarith [Real.cos_le_one t]
    exact ⟨hc x hx, nonneg_of_hasDerivAt_nonneg (by simp [hs0])
      (fun t ↦ ((Real.hasDerivAt_sin t).sub (hds 1 t)).const_mul _) hc hx⟩
  | succ m ih =>
    intro x hx
    have hc : ∀ t ≥ 0, 0 ≤ (-1 : ℝ) ^ (m + 2) * (Real.cos t - cosTaylor (m + 2) t) := fun t ht ↦
      nonneg_of_hasDerivAt_nonneg (by simp [hc0])
        (fun u ↦ (((Real.hasDerivAt_cos u).sub (hdc (m + 1) u)).const_mul _).congr_deriv
          (by
            rw [pow_succ (-1 : ℝ) (m + 1)]
            ring))
        (fun u hu ↦ (ih u hu).2) ht
    exact ⟨hc x hx, nonneg_of_hasDerivAt_nonneg (by simp [hs0])
      (fun u ↦ ((Real.hasDerivAt_sin u).sub (hds (m + 2) u)).const_mul _) hc hx⟩
theorem abs_sub_le_of_alt {d R : ℝ} (m : ℕ) (h1 : 0 ≤ (-1 : ℝ) ^ (m + 1) * d)
    (h2 : 0 ≤ (-1 : ℝ) ^ (m + 2) * (d - (-1 : ℝ) ^ (m + 1) * R)) : |d| ≤ R := by
  have hsq : (-1 : ℝ) ^ (m + 1) * (-1 : ℝ) ^ (m + 1) = 1 := by
    rw [← mul_pow, neg_one_mul, neg_neg, one_pow]
  have hexp : (-1 : ℝ) ^ (m + 2) * (d - (-1 : ℝ) ^ (m + 1) * R) = R - (-1 : ℝ) ^ (m + 1) * d := by
    rw [pow_succ (-1 : ℝ) (m + 1)]
    linear_combination R * hsq
  rw [← (by simp : |(-1 : ℝ) ^ (m + 1)| * |d| = |d|), ← abs_mul, abs_of_nonneg h1]
  linarith
def piApproxNat : ℕ := 0x3243f6a8885a308d3
def catSymMag (c_val : ℕ) : ℕ :=
  if Nat.ble c_val (Nat.pow 2 41) then c_val else Nat.sub (Nat.pow 2 42) c_val
def catSymNeg (c_val : ℕ) : Bool := Nat.ble c_val (Nat.pow 2 41)
def catRatNx (c_val : ℕ) : ℕ := Nat.div (Nat.mul piApproxNat (catSymMag c_val)) (Nat.pow 2 53)
open scoped Matrix.Norms.L2Operator in
theorem norm_ryMatrix_sub_le_abs_add_abs (c₁ s₁ c₂ s₂ : ℝ) :
    ‖TFreeLaurentGQSP.ryMatrix c₁ s₁ - TFreeLaurentGQSP.ryMatrix c₂ s₂‖ ≤
      |c₁ - c₂| + |s₁ - s₂| := by
  rw [CatalyzedLaurentGQSP.ryMatrix_sub]
  refine CatalyzedLaurentGQSP.norm_ryMatrix_le_of_sq_le _ _
    (|c₁ - c₂| + |s₁ - s₂|) (by positivity) ?_
  nlinarith [sq_abs (c₁ - c₂), sq_abs (s₁ - s₂), abs_nonneg (c₁ - c₂), abs_nonneg (s₁ - s₂)]
open scoped Matrix.Norms.L2Operator in
theorem norm_ryMatrix_catCS42_sub_gate_le (C_d : Fin (2 ^ 42)) (g : DyadicRyGate) :
    let x_d := (catRatNx C_d.val : ℝ) / 2 ^ 52
    let sin_signed := if catSymNeg C_d.val then -sinTaylor 15 x_d else sinTaylor 15 x_d
    ‖TFreeLaurentGQSP.ryMatrix (catCS42 C_d).1 (catCS42 C_d).2 -
        TFreeLaurentGQSP.ryMatrix (gateCos 48 g) (gateSin 48 g)‖ ≤
      1 / 2 ^ 50 + |cosTaylor 15 x_d - gateCos 48 g| + |sin_signed - gateSin 48 g| := by
  intro x_d sin_signed
  let θ_sym := Real.pi * (catSymMag C_d.val : ℝ) / 2 ^ 41
  let φ_sym := if catSymNeg C_d.val then -θ_sym else θ_sym
  let φ_rat := if catSymNeg C_d.val then -x_d else x_d
  have hmag : catSymMag C_d.val ≤ 2 ^ 41 := by
    unfold catSymMag
    by_cases hle : C_d.val ≤ 2 ^ 41
    · simpa only [Nat.pow_eq, Nat.ble_eq.mpr hle, ↓reduceIte] using hle
    · have hbf : Nat.ble C_d.val (Nat.pow 2 41) = false :=
        Bool.eq_false_iff.mpr (mt Nat.ble_eq.mp (by simpa only [Nat.pow_eq] using hle))
      simp only [hbf, Bool.false_eq_true, ↓reduceIte, Nat.sub_eq, Nat.pow_eq]
      exact Nat.sub_le_of_le_add (by linarith [C_d.isLt])
  have hcs : (catCS42 C_d).1 = Real.cos φ_sym ∧ (catCS42 C_d).2 = Real.sin φ_sym := by
    dsimp only [φ_sym, θ_sym]
    unfold catCS42 catAngle42 catSymMag catSymNeg
    by_cases hle : C_d.val ≤ 2 ^ 41
    · simp only [Nat.pow_eq, Nat.ble_eq.mpr hle, ↓reduceIte,
        show -((4 * Real.pi * (C_d.val : ℝ)) / 2 ^ 42) / 2 =
          -(Real.pi * (C_d.val : ℝ) / 2 ^ 41) by ring, and_self]
    · have hbf : Nat.ble C_d.val (Nat.pow 2 41) = false :=
        Bool.eq_false_iff.mpr (mt Nat.ble_eq.mp (by simpa only [Nat.pow_eq] using hle))
      simp only [hbf, Bool.false_eq_true, ↓reduceIte]
      rw [show -((4 * Real.pi * (C_d.val : ℝ)) / 2 ^ 42) / 2 =
        Real.pi * ((Nat.sub (Nat.pow 2 42) C_d.val : ℕ) : ℝ) / 2 ^ 41 - 2 * Real.pi by
          rw [Nat.sub_eq, Nat.pow_eq, Nat.cast_sub C_d.isLt.le]
          push_cast
          ring, Real.cos_sub_two_pi, Real.sin_sub_two_pi]
      exact ⟨rfl, rfl⟩
  have hpi : |Real.pi - (piApproxNat : ℝ) / 2 ^ 64| ≤ 1 / 2 ^ 64 := by
    unfold piApproxNat
    exact abs_le.mpr ⟨by linarith [Real.pi_gt_d20], by linarith [Real.pi_lt_d20]⟩
  have h_sym_rat : |φ_sym - φ_rat| ≤ 1 / 2 ^ 64 + 1 / 2 ^ 52 := by
    let q_mid : ℝ := ((piApproxNat : ℝ) / 2 ^ 64) * (catSymMag C_d.val : ℝ) / 2 ^ 41
    have hfrac : (catSymMag C_d.val : ℝ) / 2 ^ 41 ≤ 1 :=
      (div_le_one (by positivity)).mpr (by exact_mod_cast hmag)
    have h1 : |θ_sym - q_mid| ≤ 1 / 2 ^ 64 := by
      rw [show θ_sym - q_mid = (Real.pi - (piApproxNat : ℝ) / 2 ^ 64) *
          ((catSymMag C_d.val : ℝ) / 2 ^ 41) by
          dsimp [θ_sym, q_mid]
          ring,
        abs_mul, abs_of_nonneg (by positivity : 0 ≤ (catSymMag C_d.val : ℝ) / 2 ^ 41)]
      nlinarith [hpi, abs_nonneg (Real.pi - (piApproxNat : ℝ) / 2 ^ 64)]
    let N := piApproxNat * catSymMag C_d.val
    have h2 : |q_mid - x_d| ≤ 1 / 2 ^ 52 := by
      have hdiv_eq : catRatNx C_d.val = N / 2 ^ 53 := rfl
      have hle_r : (catRatNx C_d.val : ℝ) * (2 : ℝ) ^ 53 ≤ (N : ℝ) := by
        exact_mod_cast (hdiv_eq ▸ Nat.div_mul_le_self N (2 ^ 53))
      have hlt_r : (N : ℝ) ≤ (catRatNx C_d.val : ℝ) * (2 : ℝ) ^ 53 + (2 : ℝ) ^ 53 := by
        exact_mod_cast (hdiv_eq ▸ Nat.lt_div_mul_add (by positivity : 0 < 2 ^ 53)).le
      rw [show q_mid = (N : ℝ) / (2 : ℝ) ^ 105 by
          dsimp [q_mid, N]
          push_cast
          ring,
        show x_d = ((catRatNx C_d.val : ℝ) * (2 : ℝ) ^ 53) / (2 : ℝ) ^ 105 by
          dsimp [x_d]
          ring,
        abs_le]
      exact ⟨by linarith, by linarith⟩
    rw [show |φ_sym - φ_rat| = |θ_sym - x_d| by
        dsimp [φ_sym, φ_rat]
        cases catSymNeg C_d.val
        · rfl
        · rw [ite_eq_left rfl, ite_eq_left rfl, show -θ_sym - -x_d = -(θ_sym - x_d) by ring,
            abs_neg],
      show θ_sym - x_d = (θ_sym - q_mid) + (q_mid - x_d) by ring]
    exact (abs_add_le _ _).trans (add_le_add h1 h2)
  have hx0 : 0 ≤ x_d := by positivity
  have hx_le : x_d ≤ 7 / 2 := by
    have hnx : (catRatNx C_d.val : ℝ) ≤ (7 : ℝ) * (2 : ℝ) ^ 51 := by
      exact_mod_cast (show (0x3243f6a8885a308d3 * catSymMag C_d.val) / 2 ^ 53 ≤ 7 * 2 ^ 51 by omega)
    dsimp [x_d]
    linarith
  have hrem (k : ℕ) (hknat : 7 ^ k * 2 ^ 53 ≤ k.factorial * 2 ^ k) :
      x_d ^ k / (k.factorial : ℝ) ≤ 1 / 2 ^ 53 := by
    refine (div_le_div_of_nonneg_right (pow_le_pow_left₀ hx0 hx_le k) (by positivity)).trans ?_
    rw [div_pow, div_div, div_le_div_iff₀ (by positivity) (by positivity), one_mul,
      mul_comm ((2 : ℝ) ^ k)]
    exact_mod_cast hknat
  have hc_tay : |Real.cos φ_rat - cosTaylor 15 x_d| ≤ 1 / 2 ^ 53 := by
    rw [show |Real.cos φ_rat - cosTaylor 15 x_d| = |Real.cos x_d - cosTaylor 15 x_d| by
      dsimp [φ_rat]
      cases catSymNeg C_d.val
      · rfl
      · simp [Real.cos_neg]]
    have hc15 := (cos_sin_taylor_alternating 15 x_d hx0).1
    rw [cosTaylor, mul_div_assoc, ← sub_sub] at hc15
    exact (abs_sub_le_of_alt 14 (cos_sin_taylor_alternating 14 x_d hx0).1 hc15).trans
      (hrem 30 (by decide))
  have hs_tay : |Real.sin φ_rat - sin_signed| ≤ 1 / 2 ^ 53 := by
    rw [show |Real.sin φ_rat - sin_signed| = |Real.sin x_d - sinTaylor 15 x_d| by
      dsimp [φ_rat, sin_signed]
      cases catSymNeg C_d.val
      · rfl
      · simp only [↓reduceIte, Real.sin_neg]
        rw [show -Real.sin x_d - -sinTaylor 15 x_d = -(Real.sin x_d - sinTaylor 15 x_d) by ring,
          abs_neg]]
    have hs15 := (cos_sin_taylor_alternating 15 x_d hx0).2
    rw [sinTaylor, mul_div_assoc, ← sub_sub] at hs15
    exact (abs_sub_le_of_alt 14 (cos_sin_taylor_alternating 14 x_d hx0).2 hs15).trans
      (hrem 31 (by decide))
  let M_sym := TFreeLaurentGQSP.ryMatrix (Real.cos φ_sym) (Real.sin φ_sym)
  let M_rat := TFreeLaurentGQSP.ryMatrix (Real.cos φ_rat) (Real.sin φ_rat)
  let M_tay := TFreeLaurentGQSP.ryMatrix (cosTaylor 15 x_d) sin_signed
  let M_gate := TFreeLaurentGQSP.ryMatrix (gateCos 48 g) (gateSin 48 g)
  have hlip : ‖M_sym - M_rat‖ ≤ |φ_sym - φ_rat| := by
    have h := CatalyzedLaurentGQSP.norm_ryMatrix_cos_sin_sub_le (2 * φ_sym) (2 * φ_rat)
    rwa [mul_div_cancel_left₀ φ_sym two_ne_zero, mul_div_cancel_left₀ φ_rat two_ne_zero,
      ← mul_sub, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
      mul_div_cancel_left₀ _ two_ne_zero] at h
  rw [hcs.1, hcs.2,
    show M_sym - M_gate = (M_sym - M_rat) + (M_rat - M_tay) + (M_tay - M_gate) by abel]
  linarith [norm_add_le ((M_sym - M_rat) + (M_rat - M_tay)) (M_tay - M_gate),
    norm_add_le (M_sym - M_rat) (M_rat - M_tay),
    norm_ryMatrix_sub_le_abs_add_abs (Real.cos φ_rat) (Real.sin φ_rat)
      (cosTaylor 15 x_d) sin_signed, norm_ryMatrix_sub_le_abs_add_abs (cosTaylor 15 x_d) sin_signed
      (gateCos 48 g) (gateSin 48 g),
    (by norm_num : (1 : ℝ) / 2 ^ 64 + 1 / 2 ^ 52 + (1 / 2 ^ 53 + 1 / 2 ^ 53) ≤ 1 / 2 ^ 50)]
end CosSinTaylorBounds
section FastTaylorBridgeVerifier
def oddSign : ℕ → Bool
  | 0 => false
  | m + 1 => Bool.not (oddSign m)
def cosTaylorSM (K29_fact nx : ℕ) : ℕ → Bool × ℕ
  | 0 => (false, 0)
  | m + 1 =>
      let prev := cosTaylorSM K29_fact nx m
      FastRecurrenceVerifier.forceNatFast (Nat.mul (Nat.mul (Nat.div K29_fact
        (Nat.factorial (Nat.mul 2 m))) (Nat.pow nx (Nat.mul 2 m)))
        (Nat.pow 2 (Nat.mul 52 (Nat.sub 29 (Nat.mul 2 m))))) fun term_mag ↦
          FastRecurrenceVerifier.smAdd prev.1 prev.2 (oddSign m) term_mag (fun s mag ↦ (s, mag))
def sinTaylorSM (K29_fact nx : ℕ) : ℕ → Bool × ℕ
  | 0 => (false, 0)
  | m + 1 =>
      let prev := sinTaylorSM K29_fact nx m
      FastRecurrenceVerifier.forceNatFast (Nat.mul (Nat.mul (Nat.div K29_fact
        (Nat.factorial (Nat.add (Nat.mul 2 m) 1))) (Nat.pow nx (Nat.add (Nat.mul 2 m) 1)))
        (Nat.pow 2 (Nat.mul 52 (Nat.sub 29 (Nat.add (Nat.mul 2 m) 1))))) fun term_mag ↦
          FastRecurrenceVerifier.smAdd prev.1 prev.2 (oddSign m) term_mag (fun s mag ↦ (s, mag))
set_option exponentiation.threshold 2048 in
theorem cos_sin_taylorSM_cast_eq (nx : ℕ) :
    ∀ m ≤ 15, (FastRecurrenceVerifier.smToInt (cosTaylorSM (Nat.factorial 29) nx m).1
        (cosTaylorSM (Nat.factorial 29) nx m).2 : ℝ) =
        ((Nat.factorial 29 : ℝ) * (2 : ℝ) ^ (52 * 29)) * cosTaylor m ((nx : ℝ) / 2 ^ 52) ∧
      (FastRecurrenceVerifier.smToInt (sinTaylorSM (Nat.factorial 29) nx m).1
        (sinTaylorSM (Nat.factorial 29) nx m).2 : ℝ) =
        ((Nat.factorial 29 : ℝ) * (2 : ℝ) ^ (52 * 29)) * sinTaylor m ((nx : ℝ) / 2 ^ 52)
  | 0, _ => ⟨by simp [cosTaylorSM, cosTaylor], by simp [sinTaylorSM, sinTaylor]⟩
  | m + 1, hm => by
    have hodd (j n : ℕ) :
        (FastRecurrenceVerifier.smToInt (oddSign j) n : ℝ) = (-1 : ℝ) ^ j * (n : ℝ) := by
      induction j generalizing n with
      | zero => simp [oddSign, FastRecurrenceVerifier.smToInt_false]
      | succ j ih =>
        rw [oddSign, FastRecurrenceVerifier.smToInt_neg, Int.cast_neg, ih, pow_succ]
        ring
    have hstep (prev : Bool × ℕ) (k : ℕ) (hk : k ≤ 29) :
        let term_mag := Nat.mul (Nat.mul (Nat.div (Nat.factorial 29) (Nat.factorial k))
          (Nat.pow nx k)) (Nat.pow 2 (Nat.mul 52 (Nat.sub 29 k)))
        let res :=
          FastRecurrenceVerifier.smAdd prev.1 prev.2 (oddSign m) term_mag (fun s mag ↦ (s, mag))
        (FastRecurrenceVerifier.smToInt res.1 res.2 : ℝ) =
          (FastRecurrenceVerifier.smToInt prev.1 prev.2 : ℝ) +
            ((Nat.factorial 29 : ℝ) * (2 : ℝ) ^ (52 * 29)) *
              ((-1 : ℝ) ^ m * ((nx : ℝ) / 2 ^ 52) ^ k / (k.factorial : ℝ)) := by
      intro term_mag res
      rw [(FastRecurrenceVerifier.smAdd_eq_pair prev.1 prev.2 (oddSign m) term_mag
          FastRecurrenceVerifier.smToInt).symm.trans
          (FastRecurrenceVerifier.smToInt_smAdd prev.1 prev.2 (oddSign m) term_mag),
        Int.cast_add, hodd]
      congr 1
      change (-1 : ℝ) ^ m * (((Nat.factorial 29 / k.factorial * nx ^ k *
        2 ^ (52 * (29 - k)) : ℕ) : ℝ)) = _
      push_cast
      have hfact : ((Nat.factorial 29 / k.factorial : ℕ) : ℝ) * (k.factorial : ℝ) =
          (Nat.factorial 29 : ℝ) := by
        exact_mod_cast Nat.div_mul_cancel (Nat.factorial_dvd_factorial hk)
      rw [div_pow, show (2 : ℝ) ^ (52 * 29) = (2 : ℝ) ^ (52 * (29 - k)) * ((2 : ℝ) ^ 52) ^ k by
          rw [← pow_mul, ← pow_add, show 52 * (29 - k) + 52 * k = 52 * 29 by omega], ← hfact]
      field_simp [Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k),
        (by positivity : ((2 : ℝ) ^ 52) ^ k ≠ 0)]
    rcases cos_sin_taylorSM_cast_eq nx m (by omega) with ⟨hc, hs⟩
    refine ⟨?_, ?_⟩
    · rw [cosTaylorSM, FastRecurrenceVerifier.forceNatFast_eq]
      rw [hstep _ (Nat.mul 2 m) (show 2 * m ≤ 29 by omega), Nat.mul_eq, hc, cosTaylor, mul_add]
    · rw [sinTaylorSM, FastRecurrenceVerifier.forceNatFast_eq]
      rw [hstep _ (Nat.add (Nat.mul 2 m) 1) (show 2 * m + 1 ≤ 29 by omega),
        Nat.add_eq, Nat.mul_eq, hs, sinTaylor, mul_add]
def gateBridgeDiffNat (K29_fact gate_scale : ℕ) (c_raw : ℕ) (g : DyadicRyGate) : ℕ :=
  let c_val := Nat.mod c_raw (Nat.pow 2 42)
  FastRecurrenceVerifier.forceNatFast (catRatNx c_val) fun nx ↦
    let c_sm := cosTaylorSM K29_fact nx 15
    let s_sm := sinTaylorSM K29_fact nx 15
    let s_sign := if catSymNeg c_val then Bool.not s_sm.1 else s_sm.1
    let g_sm := FastRecurrenceVerifier.gateSM g
    FastRecurrenceVerifier.forceNatFast (Nat.mul g_sm.1.2 gate_scale) fun gc_mag ↦
    FastRecurrenceVerifier.forceNatFast (Nat.mul g_sm.2.2 gate_scale) fun gs_mag ↦
      Nat.add (FastRecurrenceVerifier.smAbsDiff c_sm.1 c_sm.2 g_sm.1.1 gc_mag)
        (FastRecurrenceVerifier.smAbsDiff s_sign s_sm.2 g_sm.2.1 gs_mag)
def catPolyDiffListNat (K29_fact gate_scale : ℕ) : List ℕ → List DyadicRyGate → ℕ → ℕ
  | [], _, acc => acc
  | _, [], acc => acc
  | c_raw :: cs, g :: gs, acc =>
      FastRecurrenceVerifier.forceNatFast
        (Nat.add acc (gateBridgeDiffNat K29_fact gate_scale c_raw g))
        fun acc' ↦ catPolyDiffListNat K29_fact gate_scale cs gs acc'
end FastTaylorBridgeVerifier
end CatalyzedLaurentGQSPBridge
namespace BidirectionalCatalyzedGQSPBridge
open Real Operator Matrix Circuit SpecsAux
open SpecsAux.FullScaleBESector (IsQubitizedBlockEncodingUnitary)
open TFreeLaurentGQSP CatalyzedLaurentGQSP
open TFreeLaurentGQSPPresets CatalyzedLaurentGQSPBridge
open BidirectionalCatalyzedGQSP
open scoped Matrix
section SignalQubitBiAlgebra
theorem local_H_eq_sqrt_half_smul_Z_add_X :
    Qubit.H.1 = (Real.sqrt (1 / 2) : ℂ) • (Qubit.Z.1 + Qubit.X.1) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Qubit.H, Qubit.Z, Qubit.X]
theorem eval_Z_eq_embedMatrix_Z {n : ℕ} (q_sig : Wire n) :
    (Circuit.Z q_sig).eval.1 = (QRegister.singleton q_sig).embedMatrix Qubit.Z.1 := by
  rw [Circuit.eval_single, QRegister.embedUnitary_val]
  rfl
theorem eval_Z_mul_sig_proj0 {n : ℕ} (q_sig : Wire n) :
    (Circuit.Z q_sig).eval.1 * (QRegister.singleton q_sig).basisOutcomeProjector 0 =
      (QRegister.singleton q_sig).basisOutcomeProjector 0 := by
  rw [eval_Z_eq_embedMatrix_Z, QRegister.basisOutcomeProjector,
    ← (QRegister.singleton q_sig).embedMatrix_mul, local_Z_mul_compProj0]
end SignalQubitBiAlgebra
section BidirectionalPolynomialRecurrence
def biGqspPreInit (M : ℕ) : (Fin (2 * (M + 1) + 1) → ℝ) × (Fin (2 * (M + 1) + 1) → ℝ) := (fun
    i ↦ if i.val = M + 1 then 1 else 0, fun i ↦ if i.val = M + 2 then 1 else 0)
def biGqspStep (M : ℕ) (c s : ℝ) (pq : (Fin (2 * (M + 1) + 1) → ℝ) × (Fin (2 * (M + 1) + 1) → ℝ)) :
    (Fin (2 * (M + 1) + 1) → ℝ) × (Fin (2 * (M + 1) + 1) → ℝ) :=
  gqspRotStep (M + 1) c s (shiftRight (M + 1) pq.1, shiftLeft (M + 1) pq.2)
def biGqspRunLoop (M : ℕ) (cs : ℕ → ℝ × ℝ) :
    ℕ → (Fin (2 * (M + 1) + 1) → ℝ) × (Fin (2 * (M + 1) + 1) → ℝ)
  | 0 => gqspRotStep (M + 1) (cs 0).1 (cs 0).2 (biGqspPreInit M)
  | t + 1 => biGqspStep M (cs (t + 1)).1 (cs (t + 1)).2 (biGqspRunLoop M cs t)
noncomputable def biGqspRecurrence (M : ℕ) (cs : ℕ → ℝ × ℝ) :
    (Fin (2 * (M + 1) + 1) → ℝ) × (Fin (2 * (M + 1) + 1) → ℝ) :=
  let pqM := biGqspRunLoop M cs M
  let p_left := shiftLeft (M + 1) pqM.1
  (fun i ↦ (2 : ℝ)⁻¹ * (p_left i + pqM.2 i), fun i ↦ (2 : ℝ)⁻¹ * (p_left i - pqM.2 i))
theorem biGqspRunLoop_support (M : ℕ) (cs : ℕ → ℝ × ℝ) : ∀ (t : ℕ), t ≤ M →
    ∀ i : Fin (2 * (M + 1) + 1), (i.val < (M + 1) - t ∨ (M + 2) + t < i.val) →
      (biGqspRunLoop M cs t).1 i = 0 ∧ (biGqspRunLoop M cs t).2 i = 0
  | 0, _, i, hi => by
      simp [biGqspRunLoop, biGqspPreInit, gqspRotStep,
        show i.val ≠ M + 1 by omega, show i.val ≠ M + 2 by omega]
  | t + 1, ht, i, hi => by
      have hp : shiftRight (M + 1) (biGqspRunLoop M cs t).1 i = 0 := by
        unfold shiftRight
        split_ifs
        · rfl
        · exact (biGqspRunLoop_support M cs t (by omega) ⟨i.val - 1, by omega⟩
            (show i.val - 1 < (M + 1) - t ∨ (M + 2) + t < i.val - 1 by omega)).1
      have hq : shiftLeft (M + 1) (biGqspRunLoop M cs t).2 i = 0 := by
        unfold shiftLeft
        split_ifs
        · exact (biGqspRunLoop_support M cs t (by omega) ⟨i.val + 1, by omega⟩
            (show i.val + 1 < (M + 1) - t ∨ (M + 2) + t < i.val + 1 by omega)).2
        · rfl
      simp [biGqspRunLoop, biGqspStep, gqspRotStep, hp, hq]
theorem block_zero_disjoint_singleton {a n : ℕ} (ha : 0 + a ≤ n) (q : Wire n) (hq : a ≤ q.val) :
    (QRegister.block 0 a ha).DisjointWires (QRegister.singleton q) := by
  rw [QRegister.disjoint_iff]
  intro i j h
  have hv := congrArg Fin.val h
  simp [QRegister.singleton] at hv
  omega
open scoped Matrix.Norms.L2Operator in
theorem norm_biGqspRecurrence_sub_exp_mul_proj_le {k m_BE m : ℕ} (hm : m_BE + 1 ≤ m)
    {α : ℝ} (τ : ℝ) (hα : 0 < α) (hτ : 0 ≤ τ) {A : Operator (2 ^ k)}
    {U_BE : Unitary (2 ^ (k + m_BE))} (hBE : IsQubitizedBlockEncodingUnitary α A U_BE)
    (M K : ℕ) (hMK : M + 1 ≤ K) (hβ_lt : α * τ < (K + 2 : ℝ))
    (hnorm_A : ‖(-Complex.I * (τ : ℂ)) • A‖ ≤ α * τ) (cs : ℕ → ℝ × ℝ) :
    let sys : QRegister k (k + m) := QRegister.block 0 k (by omega)
    let anc : QRegister m (k + m) := QRegister.block k m le_rfl
    let rBE : QRegister (k + m_BE) (k + m) := QRegister.block 0 (k + m_BE) (by omega)
    let q_sig : Wire (k + m) := ⟨k + m_BE, by omega⟩
    let P_anc := anc.basisOutcomeProjector 0
    let W := laurentWalk U_BE
    let W_inv := laurentWalkInv U_BE
    let U_rec := biGqspSegmentOp q_sig (rBE.embedMatrix W) (rBE.embedMatrix W_inv) cs M
    let res := biGqspRecurrence M cs
    let U_target := sys.embedMatrix (NormedSpace.exp ((-Complex.I * (τ : ℂ)) • A))
    ‖(U_rec - U_target) * P_anc‖ ≤
      (∑ d ∈ Finset.range (K + 1),
        |laurentChebWeight (M + 1) res.1 d - chebTaylorWeight (α * τ) K d|) +
      (∑ j : Fin (M + 1), laurentAsymDefect (M + 1) res.1 j) +
      (∑ i : Fin (2 * (M + 1) + 1), |res.2 i|) +
      (((K + 1).factorial : ℝ)⁻¹ * (α * τ) ^ (K + 1)) * (1 - (α * τ) / (K + 2 : ℝ))⁻¹ := by
  intro sys anc rBE q_sig P_anc W W_inv U_rec res U_target
  let P_sig0 := (QRegister.singleton q_sig).basisOutcomeProjector 0
  have hP_sig0_P_anc : P_sig0 * P_anc = P_anc := by
    have h_eq : QRegister.singleton q_sig = anc.compose (QRegister.singleton ⟨m_BE, by omega⟩) :=
      BiGqspVerifierCoreAlt.qreg_ext fun _ ↦
        Fin.ext (by simp [q_sig, anc, QRegister.singleton])
    dsimp [P_sig0, P_anc]
    rw [h_eq]
    exact basisOutcomeProjector_zero_compose_mul anc _
  have hP_anc_norm : ‖P_anc‖ ≤ 1 := norm_basisOutcomeProjector_le_one anc 0
  let P_op := rBE.embedMatrix (laurentEval (M + 1) W W_inv res.1)
  let Q_op := rBE.embedMatrix (laurentEval (M + 1) W W_inv res.2)
  have h_eval : U_rec * P_sig0 = sigPair q_sig P_op Q_op := by
    have hdisj := block_zero_disjoint_singleton (by omega : 0 + (k + m_BE) ≤ k + m) q_sig le_rfl
    let P_sig1 := (QRegister.singleton q_sig).basisOutcomeProjector 1
    let ZX_sig := (Circuit.Z q_sig).eval.1 + (Circuit.X q_sig).eval.1
    have hW_0 := embedMatrix_comm_sig_proj rBE q_sig hdisj W 0
    have hW_X := embedMatrix_comm_sig_X rBE q_sig hdisj W
    have hWinv_0 := embedMatrix_comm_sig_proj rBE q_sig hdisj W_inv 0
    have hWinv_X := embedMatrix_comm_sig_X rBE q_sig hdisj W_inv
    have hLoop (t : ℕ) (ht : t ≤ M) :
        biGqspLoopOp q_sig (rBE.embedMatrix W) (rBE.embedMatrix W_inv) cs t *
            sigPair q_sig 1 (rBE.embedMatrix W) =
          sigPair q_sig (rBE.embedMatrix (laurentEval (M + 1) W W_inv (biGqspRunLoop M cs t).1))
            (rBE.embedMatrix (laurentEval (M + 1) W W_inv (biGqspRunLoop M cs t).2)) := by
      induction t with
      | zero =>
        have hp1 : laurentEval (M + 1) W W_inv (biGqspPreInit M).1 = 1 := by
          rw [laurentEval, Finset.sum_eq_single ⟨M + 1, by omega⟩]
          · simp [biGqspPreInit]
          · exact fun i _ hne ↦ by simp [biGqspPreInit, Fin.val_ne_of_ne hne]
          · exact fun h ↦ absurd (Finset.mem_univ _) h
        have hp2 : laurentEval (M + 1) W W_inv (biGqspPreInit M).2 = W := by
          rw [laurentEval, Finset.sum_eq_single ⟨M + 2, by omega⟩]
          · simpa [biGqspPreInit] using laurentTerm_add (M + 1) 1 (by omega) W W_inv
          · exact fun i _ hne ↦ by simp [biGqspPreInit, Fin.val_ne_of_ne hne]
          · exact fun h ↦ absurd (Finset.mem_univ _) h
        dsimp [biGqspLoopOp, biGqspRunLoop, gqspRotStep]
        rw [embedMatrix_ryMatrix_mul_sigPair]
        exact congrArg₂ (sigPair q_sig)
          (by rw [← rBE.embedMatrix_one, ← rBE.embedMatrix_smul, ← rBE.embedMatrix_smul,
                ← embedMatrix_sub rBE]
              exact congrArg rBE.embedMatrix (by rw [← laurentEval_sub_linear, hp1, hp2]))
          (by rw [← rBE.embedMatrix_one, ← rBE.embedMatrix_smul, ← rBE.embedMatrix_smul,
                ← rBE.embedMatrix_add]
              exact congrArg rBE.embedMatrix (by rw [← laurentEval_linear, hp1, hp2]))
      | succ t ih =>
        dsimp only [biGqspLoopOp, biGqspRunLoop, biGqspStep, gqspRotStep]
        rw [Matrix.mul_assoc, ih (by omega),
          Matrix.mul_assoc ((QRegister.singleton q_sig).embedMatrix _),
          biWalkStepOp, proj_step_mul_sigPair q_sig _ _ _ _ hW_0 hWinv_0 hWinv_X,
          ← rBE.embedMatrix_mul W, ← rBE.embedMatrix_mul W_inv,
          show W * laurentEval (M + 1) W W_inv (biGqspRunLoop M cs t).1 =
              laurentEval (M + 1) W W_inv (shiftRight (M + 1) (biGqspRunLoop M cs t).1) by
            unfold laurentEval
            rw [Fin.sum_univ_castSucc, (biGqspRunLoop_support M cs t (by omega) _
                (Or.inr (show (M + 2) + t < 2 * (M + 1) by omega))).1,
              Complex.ofReal_zero, zero_smul, add_zero, Finset.mul_sum,
              Fin.sum_univ_succ (f := fun i ↦ (shiftRight (M + 1) _ i : ℂ) • _),
              shiftRight_zero, Complex.ofReal_zero, zero_smul, zero_add]
            exact Finset.sum_congr rfl fun i _ ↦ by
              rw [mul_smul_comm,
                mul_laurentTerm_castSucc (M + 1) W W_inv (laurentWalk_mul_inv hBE) i,
                shiftRight_succ],
          mul_inv_laurentEval_of_zero_eq_zero (M + 1) W W_inv (laurentWalk_mul_inv hBE)
            (laurentWalkInv_mul hBE) _
            (biGqspRunLoop_support M cs t (by omega) 0
              (Or.inl (show 0 < (M + 1) - t by omega))).2,
          embedMatrix_ryMatrix_mul_sigPair]
        exact congrArg₂ (sigPair q_sig)
          (by rw [← rBE.embedMatrix_smul, ← rBE.embedMatrix_smul, ← embedMatrix_sub rBE,
                laurentEval_sub_linear])
          (by rw [← rBE.embedMatrix_smul, ← rBE.embedMatrix_smul, ← rBE.embedMatrix_add,
                laurentEval_linear])
    have hRight : (P_sig0 + rBE.embedMatrix W * P_sig1) * (ZX_sig * P_sig0) =
        sigPair q_sig 1 (rBE.embedMatrix W) := by
      rw [show ZX_sig * P_sig0 = sigPair q_sig 1 1 by
            unfold sigPair
            dsimp only
            rw [add_mul, eval_Z_mul_sig_proj0, mul_one, mul_one],
        ← one_mul P_sig0, proj_step_mul_sigPair q_sig 1 (rBE.embedMatrix W) 1 1
          (by rw [one_mul, mul_one]) hW_0 hW_X, one_mul, mul_one]
    let pqM := biGqspRunLoop M cs M
    have hsqrt : (Real.sqrt (1 / 2) : ℂ) * (Real.sqrt (1 / 2) : ℂ) = ((2 : ℝ)⁻¹ : ℂ) := by
      exact_mod_cast (show Real.sqrt (1 / 2) * Real.sqrt (1 / 2) = (2 : ℝ)⁻¹ by
        rw [← sq, Real.sq_sqrt (by positivity)]
        ring)
    have hLeft (X Y : Operator (2 ^ (k + m))) : ((2 : ℝ)⁻¹ : ℂ) • (ZX_sig * sigPair q_sig X Y) =
          sigPair q_sig (((2 : ℝ)⁻¹ : ℂ) • (X + Y)) (((2 : ℝ)⁻¹ : ℂ) • (X - Y)) := by
      let rSig := QRegister.singleton q_sig
      rw [show ZX_sig * sigPair q_sig X Y = sigPair q_sig (X + Y) (X - Y) by
        rw [show ZX_sig * sigPair q_sig X Y =
            ((Circuit.Z q_sig).eval.1 * P_sig0 + (Circuit.X q_sig).eval.1 * P_sig0) * X +
            ((Circuit.Z q_sig).eval.1 * ((Circuit.X q_sig).eval.1 * P_sig0) +
              (Circuit.X q_sig).eval.1 * ((Circuit.X q_sig).eval.1 * P_sig0)) * Y by
            dsimp [ZX_sig, sigPair, P_sig0]
            noncomm_ring,
          eval_Z_mul_sig_proj0,
          show (Circuit.Z q_sig).eval.1 * ((Circuit.X q_sig).eval.1 * P_sig0) =
              -((Circuit.X q_sig).eval.1 * P_sig0) by
            dsimp only [P_sig0]
            rw [eval_Z_eq_embedMatrix_Z, eval_X_eq_embedMatrix_X, QRegister.basisOutcomeProjector,
              ← rSig.embedMatrix_mul, ← rSig.embedMatrix_mul, local_Z_mul_X_mul_compProj0,
              ← neg_one_smul ℂ (Qubit.X.1 * compProj 0), rSig.embedMatrix_smul, neg_one_smul],
          show (Circuit.X q_sig).eval.1 * ((Circuit.X q_sig).eval.1 * P_sig0) = P_sig0 by
            rw [← Matrix.mul_assoc, eval_X_eq_embedMatrix_X, ← rSig.embedMatrix_mul,
              local_X_mul_self, rSig.embedMatrix_one, one_mul]]
        dsimp [sigPair, P_sig0]
        noncomm_ring]
      dsimp [sigPair]
      rw [smul_add, mul_smul_comm, mul_smul_comm]
    change (Circuit.H q_sig).eval.1 * (rBE.embedMatrix W_inv * P_sig0 + P_sig1) *
        biGqspLoopOp q_sig (rBE.embedMatrix W) (rBE.embedMatrix W_inv) cs M *
        (P_sig0 + rBE.embedMatrix W * P_sig1) * (Circuit.H q_sig).eval.1 * P_sig0 = _
    rw [show (Circuit.H q_sig).eval.1 = (Real.sqrt (1 / 2) : ℂ) • ZX_sig by
      dsimp only [ZX_sig]
      rw [show (Circuit.H q_sig).eval.1 = (QRegister.singleton q_sig).embedMatrix Qubit.H.1 by
        rw [Circuit.eval_single, QRegister.embedUnitary_val]
        rfl, eval_Z_eq_embedMatrix_Z, eval_X_eq_embedMatrix_X,
        local_H_eq_sqrt_half_smul_Z_add_X, (QRegister.singleton q_sig).embedMatrix_smul,
        (QRegister.singleton q_sig).embedMatrix_add]]
    simp only [smul_mul_assoc, mul_smul_comm, Matrix.mul_assoc, smul_smul, hsqrt]
    rw [hRight, hLoop M le_rfl, ← one_mul P_sig1,
      proj_step_mul_sigPair q_sig (rBE.embedMatrix W_inv) 1 _ _ hWinv_0
        (by rw [one_mul, mul_one]) (by rw [one_mul, mul_one]),
      one_mul, ← rBE.embedMatrix_mul W_inv,
      mul_inv_laurentEval_of_zero_eq_zero (M + 1) W W_inv (laurentWalk_mul_inv hBE)
        (laurentWalkInv_mul hBE) pqM.1
        (biGqspRunLoop_support M cs M le_rfl 0 (Or.inl (show 0 < (M + 1) - M by omega))).1,
      hLeft]
    dsimp [P_op, Q_op, res, biGqspRecurrence]
    congr 1
    · have hlin := laurentEval_linear (M + 1) W W_inv (2 : ℝ)⁻¹ (2 : ℝ)⁻¹
        (shiftLeft (M + 1) pqM.1) pqM.2
      rw [← smul_add] at hlin
      push_cast at hlin ⊢
      rw [← rBE.embedMatrix_add, ← rBE.embedMatrix_smul, hlin]
      exact congrArg (rBE.embedMatrix ∘ laurentEval (M + 1) W W_inv) (funext fun _ ↦ by ring)
    · have hlin := laurentEval_sub_linear (M + 1) W W_inv (2 : ℝ)⁻¹ (2 : ℝ)⁻¹
        (shiftLeft (M + 1) pqM.1) pqM.2
      rw [← smul_sub] at hlin
      push_cast at hlin ⊢
      rw [← embedMatrix_sub rBE, ← rBE.embedMatrix_smul, hlin]
      exact congrArg (rBE.embedMatrix ∘ laurentEval (M + 1) W W_inv) (funext fun _ ↦ by ring)
  have hU_rec_P : U_rec * P_anc = sigPair q_sig P_op Q_op * P_anc :=
    (congrArg (U_rec * ·) hP_sig0_P_anc.symm).trans
      ((Matrix.mul_assoc U_rec P_sig0 P_anc).symm.trans (congrArg (· * P_anc) h_eval))
  have hU_tar_P : U_target * P_anc = (P_sig0 * U_target) * P_anc :=
    (congrArg (U_target * ·) hP_sig0_P_anc.symm).trans
      ((Matrix.mul_assoc U_target P_sig0 P_anc).symm.trans (congrArg (· * P_anc)
        (embedMatrix_comm_sig_proj sys q_sig
          (block_zero_disjoint_singleton _ q_sig (Nat.le_add_right k m_BE)) _ 0)))
  have h_step0 : ‖(U_rec - U_target) * P_anc‖ ≤ ‖(P_op - U_target) * P_anc‖ + ‖Q_op * P_anc‖ := by
    rw [sub_mul, hU_rec_P, hU_tar_P, ← sub_mul]
    exact norm_sigPair_sub_target_mul_le q_sig P_op Q_op U_target P_anc
  have h_Q : ‖Q_op * P_anc‖ ≤ ∑ i : Fin (2 * (M + 1) + 1), |res.2 i| :=
    (norm_mul_le_of_right_le_one hP_anc_norm).trans
      ((norm_embedMatrix_le rBE _).trans (norm_laurentEval_le_l1 U_BE (M + 1) res.2))
  let sys0 : QRegister k (k + m_BE) := QRegister.block 0 k (by omega)
  let anc0 : QRegister m_BE (k + m_BE) := QRegister.block k m_BE le_rfl
  have hcomp_sys : rBE.compose sys0 = sys :=
    BiGqspVerifierCoreAlt.qreg_ext fun _ ↦ Fin.ext (by simp [rBE, sys0, sys])
  have hP_BE_P_anc : rBE.embedMatrix (anc0.basisOutcomeProjector 0) * P_anc = P_anc := by
    have hcomp_anc : rBE.compose anc0 = anc.compose (QRegister.block 0 m_BE (by omega)) :=
      BiGqspVerifierCoreAlt.qreg_ext fun _ ↦ Fin.ext (by simp [rBE, anc0, anc])
    rw [QRegister.basisOutcomeProjector, ← QRegister.embedMatrix_compose, hcomp_anc,
      ← QRegister.basisOutcomeProjector]
    exact basisOutcomeProjector_zero_compose_mul anc _
  let S_cheb0 : Operator (2 ^ (k + m_BE)) := ∑ d ∈ Finset.range ((M + 1) + 1),
      ((-Complex.I) ^ d * (laurentChebWeight (M + 1) res.1 d : ℂ)) •
        sys0.embedMatrix (chebT d ((α : ℂ)⁻¹ • A))
  let S_cheb := rBE.embedMatrix S_cheb0
  let S_tay := sys.embedMatrix (taylorPoly ((-Complex.I * (τ : ℂ)) • A) K)
  have h_asym : ‖(P_op - S_cheb) * P_anc‖ ≤
      ∑ j : Fin (M + 1), laurentAsymDefect (M + 1) res.1 j := by
    rw [show (P_op - S_cheb) * P_anc = rBE.embedMatrix ((laurentEval (M + 1) W W_inv res.1 -
        S_cheb0) * anc0.basisOutcomeProjector 0) * P_anc by
      dsimp [P_op, S_cheb]
      rw [rBE.embedMatrix_mul, Matrix.mul_assoc, hP_BE_P_anc, embedMatrix_sub rBE]]
    exact (norm_mul_le_of_right_le_one hP_anc_norm).trans ((norm_embedMatrix_le rBE _).trans
      (norm_laurentEval_sub_cheb_sum_mul_proj_le hBE (M + 1) res.1))
  have hS_cheb_eq : S_cheb = ∑ d ∈ Finset.range (K + 1),
      ((-Complex.I) ^ d * (laurentChebWeight (M + 1) res.1 d : ℂ)) •
        sys.embedMatrix (chebT d ((α : ℂ)⁻¹ • A)) := by
    dsimp [S_cheb, S_cheb0]
    rw [rBE.embedMatrix_sum]
    refine (Finset.sum_congr rfl fun d _ ↦ by
        rw [rBE.embedMatrix_smul, ← QRegister.embedMatrix_compose, hcomp_sys]).trans
      (Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ hMK)) fun d _ hnot ↦ ?_)
    rw [Finset.mem_range, not_lt] at hnot
    unfold laurentChebWeight
    rw [ite_eq_right (by omega), dite_eq_right (by omega), Complex.ofReal_zero, mul_zero, zero_smul]
  have h_cheb_tay : ‖(S_cheb - S_tay) * P_anc‖ ≤ ∑ d ∈ Finset.range (K + 1),
      |laurentChebWeight (M + 1) res.1 d - chebTaylorWeight (α * τ) K d| := by
    rw [hS_cheb_eq]
    exact norm_chebSum_sub_taylorPoly_le (by omega) τ (ne_of_gt hα) hBE K _
  have h_tay_exp : ‖(S_tay - U_target) * P_anc‖ ≤
      (((K + 1).factorial : ℝ)⁻¹ * (α * τ) ^ (K + 1)) * (1 - (α * τ) / (K + 2 : ℝ))⁻¹ := by
    refine (norm_mul_le_of_right_le_one hP_anc_norm).trans ?_
    dsimp [S_tay, U_target]
    rw [← embedMatrix_sub sys]
    refine (norm_embedMatrix_le sys _).trans ((norm_sub_rev _ _).le.trans ?_)
    set x := (-Complex.I * (τ : ℂ)) • A
    let r : ℝ := (α * τ) / (K + 2 : ℝ)
    let C : ℝ := ((K + 1).factorial : ℝ)⁻¹ * (α * τ) ^ (K + 1)
    have hr0 : 0 ≤ r := by positivity
    have hr1 : r < 1 := (div_lt_one (by positivity)).mpr hβ_lt
    have hsum_geom := (summable_geometric_of_lt_one hr0 hr1).mul_left C
    have hfnat (k : ℕ) : (K + 1).factorial * (K + 2) ^ k ≤ (k + (K + 1)).factorial := by
      induction k with
      | zero => simp
      | succ k ih =>
        rw [pow_succ, ← mul_assoc, Nat.succ_add, Nat.factorial_succ (k + (K + 1)),
          Nat.mul_comm (k + (K + 1) + 1)]
        exact Nat.mul_le_mul ih (by omega)
    have hterm (k : ℕ) : ‖(((k + (K + 1)).factorial : ℂ)⁻¹) • (x ^ (k + (K + 1)))‖ ≤
        C * r ^ k := by
      have hinv : ((k + (K + 1)).factorial : ℝ)⁻¹ ≤
          ((K + 1).factorial : ℝ)⁻¹ * ((K + 2 : ℝ)⁻¹ ^ k) := by
        rw [inv_pow, ← mul_inv]
        exact inv_anti₀ (by positivity) (by exact_mod_cast hfnat k)
      rw [norm_smul, norm_inv, Complex.norm_natCast]
      exact (mul_le_mul hinv ((norm_pow_le' x (Nat.add_pos_right k (Nat.succ_pos K))).trans
          ((pow_le_pow_left₀ (norm_nonneg x) hnorm_A _).trans_eq (by rw [Nat.add_comm, pow_add])))
        (norm_nonneg _) (by positivity)).trans_eq (by
          dsimp [C, r]
          rw [div_eq_mul_inv, mul_pow]
          ring)
    have hsum_lhs := Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) hterm hsum_geom
    rw [show NormedSpace.exp x - taylorPoly x K =
        ∑' k : ℕ, (((k + (K + 1)).factorial : ℂ)⁻¹) • (x ^ (k + (K + 1))) by
      rw [congr_fun (NormedSpace.exp_eq_tsum ℂ) x, taylorPoly,
        ← (NormedSpace.expSeries_summable' x).sum_add_tsum_nat_add (K + 1)]
      abel]
    exact (norm_tsum_le_tsum_norm hsum_lhs).trans ((hsum_lhs.tsum_le_tsum hterm hsum_geom).trans
      (by rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1]))
  have h1 := norm_add_le ((P_op - S_cheb) * P_anc + (S_cheb - S_tay) * P_anc)
    ((S_tay - U_target) * P_anc)
  have h2 := norm_add_le ((P_op - S_cheb) * P_anc) ((S_cheb - S_tay) * P_anc)
  rw [show (P_op - S_cheb) * P_anc + (S_cheb - S_tay) * P_anc + (S_tay - U_target) * P_anc =
    (P_op - U_target) * P_anc by noncomm_ring] at h1
  linarith
end BidirectionalPolynomialRecurrence
section BidirectionalOperatorTelescoping
theorem biWalkStepOp_eq_mul_c0_c1 {n : ℕ} (q_sig : Wire n) (W_emb W_inv_emb : Operator (2 ^ n))
    (hWinv_0 : W_inv_emb * (QRegister.singleton q_sig).basisOutcomeProjector 0 =
      (QRegister.singleton q_sig).basisOutcomeProjector 0 * W_inv_emb)
    (hWinv_1 : W_inv_emb * (QRegister.singleton q_sig).basisOutcomeProjector 1 =
      (QRegister.singleton q_sig).basisOutcomeProjector 1 * W_inv_emb) :
    biWalkStepOp q_sig W_emb W_inv_emb =
      (W_emb * (QRegister.singleton q_sig).basisOutcomeProjector 0 +
        (QRegister.singleton q_sig).basisOutcomeProjector 1) *
      ((QRegister.singleton q_sig).basisOutcomeProjector 0 +
        W_inv_emb * (QRegister.singleton q_sig).basisOutcomeProjector 1) := by
  have h := sig_block_diag_mul q_sig W_emb 1 1 W_inv_emb (by simp) (by simp) hWinv_0 hWinv_1
  dsimp only at h
  simp only [one_mul, mul_one] at h
  exact h.symm
theorem biWalkStepOp_mem_unitaryGroup {n : ℕ} (q_sig : Wire n)
    (W_emb W_inv_emb : Operator (2 ^ n)) (hW_mem : W_emb ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ)
    (hWinv_mem : W_inv_emb ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ)
    (hW_0 : W_emb * (QRegister.singleton q_sig).basisOutcomeProjector 0 =
      (QRegister.singleton q_sig).basisOutcomeProjector 0 * W_emb)
    (hWinv_0 : W_inv_emb * (QRegister.singleton q_sig).basisOutcomeProjector 0 =
      (QRegister.singleton q_sig).basisOutcomeProjector 0 * W_inv_emb)
    (hWinv_1 : W_inv_emb * (QRegister.singleton q_sig).basisOutcomeProjector 1 =
      (QRegister.singleton q_sig).basisOutcomeProjector 1 * W_inv_emb) :
    biWalkStepOp q_sig W_emb W_inv_emb ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ :=
  biWalkStepOp_eq_mul_c0_c1 q_sig W_emb W_inv_emb hWinv_0 hWinv_1 ▸ Submonoid.mul_mem _
    (c0_step_mem_unitaryGroup q_sig W_emb hW_mem hW_0)
    (c1_step_mem_unitaryGroup q_sig W_inv_emb hWinv_mem hWinv_1)
theorem laurentWalk_pair_embed_mem_unitaryGroup {k m_BE n : ℕ}
    (rBE : QRegister (k + m_BE) n) (U_BE : Unitary (2 ^ (k + m_BE))) :
    rBE.embedMatrix (laurentWalk U_BE) ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ ∧
      rBE.embedMatrix (laurentWalkInv U_BE) ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ :=
  ⟨(rBE.embedUnitary ⟨laurentWalk U_BE, Matrix.mem_unitaryGroup_iff'.mpr <| by
      rw [laurentWalk, star_smul, smul_mul_smul_comm, (szegedyWalk_mem_unitaryGroup U_BE).1]
      simp [Complex.I_mul_I]⟩).2,
   (rBE.embedUnitary ⟨laurentWalkInv U_BE, Matrix.mem_unitaryGroup_iff'.mpr <| by
      rw [laurentWalkInv, star_smul, smul_mul_smul_comm, (szegedyWalkInv_mem_unitaryGroup U_BE).1]
      simp [Complex.I_mul_I]⟩).2⟩
theorem biGqspLoopOp_biCS_mem_unitaryGroup {n : ℕ} (q_sig : Wire n)
    (W_emb W_inv_emb : Operator (2 ^ n))
    (hStep : biWalkStepOp q_sig W_emb W_inv_emb ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ)
    (M : ℕ) (C : Fin (M + 1) → Fin (2 ^ 42)) (t : ℕ) :
    biGqspLoopOp q_sig W_emb W_inv_emb (biCS M C) t ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ := by
  have hry (j : ℕ) : (QRegister.singleton q_sig).embedMatrix
      (TFreeLaurentGQSP.ryMatrix (biCS M C j).1 (biCS M C j).2) ∈
      Matrix.unitaryGroup (Fin (2 ^ n)) ℂ := by
    dsimp only [biCS]
    rw [← ryUnitary_catAngle42_val]
    exact ((QRegister.singleton q_sig).embedUnitary _).2
  induction t with
  | zero => exact hry 0
  | succ t ih => exact Submonoid.mul_mem _ (Submonoid.mul_mem _ (hry (t + 1)) hStep) ih
noncomputable def biCatSegmentOp {k m_BE n : ℕ} (rBE : QRegister (k + m_BE) n)
    (q_sig : Wire n) (M : ℕ) (C : Fin (M + 1) → Fin (2 ^ 42))
    (U_BE : Unitary (2 ^ (k + m_BE))) : Operator (2 ^ n) :=
  biGqspSegmentOp q_sig (rBE.embedMatrix (laurentWalk U_BE))
    (rBE.embedMatrix (laurentWalkInv U_BE)) (biCS M C) M
noncomputable def biCatSegmentUnitary (k m_BE M : ℕ) (C : Fin (M + 1) → Fin (2 ^ 42))
    (U_BE : Unitary (2 ^ (k + m_BE))) : Unitary (2 ^ (k + (m_BE + 1))) :=
  let rBE : QRegister (k + m_BE) (k + (m_BE + 1)) := QRegister.block 0 (k + m_BE) (by omega)
  let q_sig : Wire (k + (m_BE + 1)) := ⟨k + m_BE, by omega⟩
  ⟨biCatSegmentOp rBE q_sig M C U_BE, by
    have hBE_sig := block_zero_disjoint_singleton
      (by omega : 0 + (k + m_BE) ≤ k + (m_BE + 1)) q_sig le_rfl
    rcases laurentWalk_pair_embed_mem_unitaryGroup rBE U_BE with ⟨hW, hWinv⟩
    exact Submonoid.mul_mem _ (Submonoid.mul_mem _ (Submonoid.mul_mem _
      (Submonoid.mul_mem _ (Circuit.H q_sig).eval.2 (c0_step_mem_unitaryGroup q_sig _ hWinv
        (embedMatrix_comm_sig_proj rBE q_sig hBE_sig (laurentWalkInv U_BE) 0)))
      (biGqspLoopOp_biCS_mem_unitaryGroup q_sig _ _
        (biWalkStepOp_mem_unitaryGroup q_sig _ _ hW hWinv
          (embedMatrix_comm_sig_proj rBE q_sig hBE_sig (laurentWalk U_BE) 0)
          (embedMatrix_comm_sig_proj rBE q_sig hBE_sig (laurentWalkInv U_BE) 0)
          (embedMatrix_comm_sig_proj rBE q_sig hBE_sig (laurentWalkInv U_BE) 1)) M C M))
      (c1_step_mem_unitaryGroup q_sig _ hW
        (embedMatrix_comm_sig_proj rBE q_sig hBE_sig (laurentWalk U_BE) 1)))
      (Circuit.H q_sig).eval.2⟩
theorem embedMatrix_singleton_embedMatrix {m n : ℕ} (r : QRegister m n) (q : Wire m)
    (X : Operator 2) : r.embedMatrix ((QRegister.singleton q).embedMatrix X) =
    (QRegister.singleton (r q)).embedMatrix X := by
  rw [← QRegister.embedMatrix_compose, show r.compose (QRegister.singleton q) =
    QRegister.singleton (r q) from BiGqspVerifierCoreAlt.qreg_ext fun i ↦ by
      fin_cases i
      rfl]
theorem embedMatrix_singleton_basisOutcomeProjector {m n : ℕ} (r : QRegister m n) (q : Wire m)
    (b : Fin 2) : r.embedMatrix ((QRegister.singleton q).basisOutcomeProjector b) =
    (QRegister.singleton (r q)).basisOutcomeProjector b := by
  rw [QRegister.basisOutcomeProjector, embedMatrix_singleton_embedMatrix,
    ← QRegister.basisOutcomeProjector]
theorem embedMatrix_eval_H {m n : ℕ} (r : QRegister m n) (q : Wire m) :
    r.embedMatrix (Circuit.H q).eval.1 = (Circuit.H (r q)).eval.1 := by
  rw [Circuit.eval_single, Circuit.eval_single, QRegister.embedUnitary_val,
    QRegister.embedUnitary_val]
  exact embedMatrix_singleton_embedMatrix r q Qubit.H.1
theorem embedMatrix_biWalkStepOp {m n : ℕ} (r : QRegister m n) (q_sig : Wire m)
    (W_emb W_inv_emb : Operator (2 ^ m)) : r.embedMatrix (biWalkStepOp q_sig W_emb W_inv_emb) =
    biWalkStepOp (r q_sig) (r.embedMatrix W_emb) (r.embedMatrix W_inv_emb) := by
  unfold biWalkStepOp
  rw [r.embedMatrix_add, r.embedMatrix_mul, r.embedMatrix_mul,
    embedMatrix_singleton_basisOutcomeProjector, embedMatrix_singleton_basisOutcomeProjector]
theorem embedMatrix_biGqspLoopOp {m n : ℕ} (r : QRegister m n) (q_sig : Wire m)
    (W_emb W_inv_emb : Operator (2 ^ m)) (cs : ℕ → ℝ × ℝ) (t : ℕ) :
    r.embedMatrix (biGqspLoopOp q_sig W_emb W_inv_emb cs t) =
      biGqspLoopOp (r q_sig) (r.embedMatrix W_emb) (r.embedMatrix W_inv_emb) cs t := by
  induction t with
  | zero => exact embedMatrix_singleton_embedMatrix r q_sig _
  | succ t ih =>
    dsimp only [biGqspLoopOp]
    rw [r.embedMatrix_mul, r.embedMatrix_mul, ih, embedMatrix_singleton_embedMatrix,
      embedMatrix_biWalkStepOp]
theorem embedMatrix_biGqspSegmentOp {m n : ℕ} (r : QRegister m n) (q_sig : Wire m)
    (W_emb W_inv_emb : Operator (2 ^ m)) (cs : ℕ → ℝ × ℝ) (M : ℕ) :
    r.embedMatrix (biGqspSegmentOp q_sig W_emb W_inv_emb cs M) =
      biGqspSegmentOp (r q_sig) (r.embedMatrix W_emb) (r.embedMatrix W_inv_emb) cs M := by
  unfold biGqspSegmentOp
  rw [r.embedMatrix_mul, r.embedMatrix_mul, r.embedMatrix_mul, r.embedMatrix_mul,
    embedMatrix_eval_H, embedMatrix_biGqspLoopOp, r.embedMatrix_add, r.embedMatrix_mul,
    r.embedMatrix_add, r.embedMatrix_mul, embedMatrix_singleton_basisOutcomeProjector,
    embedMatrix_singleton_basisOutcomeProjector]
open scoped Matrix.Norms.L2Operator in
theorem norm_biGqspLoopOp_le_one {n : ℕ} (q_sig : Wire n) (W_emb W_inv_emb : Operator (2 ^ n))
    (hStep_unit : biWalkStepOp q_sig W_emb W_inv_emb ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ)
    (cs : ℕ → ℝ × ℝ) (t : ℕ) (hcs : ∀ j < t + 1, (cs j).1 ^ 2 + (cs j).2 ^ 2 ≤ 1) :
    ‖biGqspLoopOp q_sig W_emb W_inv_emb cs t‖ ≤ 1 := by
  induction t with
  | zero =>
    dsimp only [biGqspLoopOp]
    exact (norm_embedMatrix_le _ _).trans (norm_ryMatrix_le_one _ _ (hcs 0 (by omega)))
  | succ t ih =>
    dsimp only [biGqspLoopOp]
    have hS_norm : ‖biWalkStepOp q_sig W_emb W_inv_emb‖ ≤ 1 :=
      norm_of_mem_unitaryGroup_le_one hStep_unit
    have hR_norm : ‖(QRegister.singleton q_sig).embedMatrix
        (ryMatrix (cs (t + 1)).1 (cs (t + 1)).2)‖ ≤ 1 :=
      (norm_embedMatrix_le _ _).trans (norm_ryMatrix_le_one _ _ (hcs (t + 1) (by omega)))
    have hRS_norm : ‖(QRegister.singleton q_sig).embedMatrix
        (ryMatrix (cs (t + 1)).1 (cs (t + 1)).2) * biWalkStepOp q_sig W_emb W_inv_emb‖ ≤ 1 :=
      (norm_mul_le_of_left_le_one hR_norm).trans hS_norm
    exact (norm_mul_le_of_left_le_one hRS_norm).trans (ih fun j hj ↦ hcs j (by omega))
open scoped Matrix.Norms.L2Operator in
theorem norm_biGqspLoopOp_sub_le {n : ℕ} (q_sig : Wire n) (W_emb W_inv_emb : Operator (2 ^ n))
    (hStep_unit : biWalkStepOp q_sig W_emb W_inv_emb ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ)
    (cs₁ cs₂ : ℕ → ℝ × ℝ) (t : ℕ) (hcs₁ : ∀ j < t + 1, (cs₁ j).1 ^ 2 + (cs₁ j).2 ^ 2 ≤ 1)
    (hcs₂ : ∀ j < t + 1, (cs₂ j).1 ^ 2 + (cs₂ j).2 ^ 2 ≤ 1) :
    ‖biGqspLoopOp q_sig W_emb W_inv_emb cs₁ t - biGqspLoopOp q_sig W_emb W_inv_emb cs₂ t‖ ≤
      ∑ j ∈ Finset.range (t + 1), ‖TFreeLaurentGQSP.ryMatrix (cs₁ j).1 (cs₁ j).2 -
            TFreeLaurentGQSP.ryMatrix (cs₂ j).1 (cs₂ j).2‖ := by
  induction t with
  | zero =>
    dsimp only [biGqspLoopOp]
    rw [Finset.sum_range_one, ← embedMatrix_sub (QRegister.singleton q_sig)]
    exact norm_embedMatrix_le _ _
  | succ t ih =>
    dsimp only [biGqspLoopOp]
    rw [Finset.sum_range_succ _ (t + 1), add_comm (∑ j ∈ Finset.range (t + 1), _)]
    let S_step := biWalkStepOp q_sig W_emb W_inv_emb
    let R₁ := (QRegister.singleton q_sig).embedMatrix (ryMatrix (cs₁ (t + 1)).1 (cs₁ (t + 1)).2)
    let R₂ := (QRegister.singleton q_sig).embedMatrix (ryMatrix (cs₂ (t + 1)).1 (cs₂ (t + 1)).2)
    have hS : ‖S_step‖ ≤ 1 := norm_of_mem_unitaryGroup_le_one hStep_unit
    rw [show R₁ * S_step * biGqspLoopOp q_sig W_emb W_inv_emb cs₁ t -
        R₂ * S_step * biGqspLoopOp q_sig W_emb W_inv_emb cs₂ t =
      (R₁ - R₂) * S_step * biGqspLoopOp q_sig W_emb W_inv_emb cs₂ t +
      (R₁ * S_step) * (biGqspLoopOp q_sig W_emb W_inv_emb cs₁ t -
        biGqspLoopOp q_sig W_emb W_inv_emb cs₂ t) by noncomm_ring]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · refine (norm_mul_le_of_right_le_one
        (norm_biGqspLoopOp_le_one q_sig W_emb W_inv_emb hStep_unit cs₂ t fun j hj ↦
          hcs₂ j (by omega))).trans ((norm_mul_le_of_right_le_one hS).trans ?_)
      dsimp only [R₁, R₂]
      rw [← embedMatrix_sub (QRegister.singleton q_sig)]
      exact norm_embedMatrix_le _ _
    · have hR₁_norm : ‖R₁‖ ≤ 1 :=
        (norm_embedMatrix_le _ _).trans (norm_ryMatrix_le_one _ _ (hcs₁ (t + 1) (by omega)))
      have hRS₁_norm : ‖R₁ * S_step‖ ≤ 1 := (norm_mul_le_of_left_le_one hR₁_norm).trans hS
      exact (norm_mul_le_of_left_le_one hRS₁_norm).trans
        (ih (fun j hj ↦ hcs₁ j (by omega)) (fun j hj ↦ hcs₂ j (by omega)))
open scoped Matrix.Norms.L2Operator in
theorem norm_biGqspSegmentOp_sub_le {k m_BE n : ℕ} (rBE : QRegister (k + m_BE) n)
    (q_sig : Wire n) (hBE_sig : rBE.DisjointWires (QRegister.singleton q_sig))
    (U_BE : Unitary (2 ^ (k + m_BE))) (M : ℕ) (cs₁ cs₂ : ℕ → ℝ × ℝ)
    (hcs₁ : ∀ j < M + 1, (cs₁ j).1 ^ 2 + (cs₁ j).2 ^ 2 ≤ 1)
    (hcs₂ : ∀ j < M + 1, (cs₂ j).1 ^ 2 + (cs₂ j).2 ^ 2 ≤ 1) : let W := laurentWalk U_BE
    let W_inv := laurentWalkInv U_BE
    ‖biGqspSegmentOp q_sig (rBE.embedMatrix W) (rBE.embedMatrix W_inv) cs₁ M -
        biGqspSegmentOp q_sig (rBE.embedMatrix W) (rBE.embedMatrix W_inv) cs₂ M‖ ≤
      ∑ j ∈ Finset.range (M + 1), ‖TFreeLaurentGQSP.ryMatrix (cs₁ j).1 (cs₁ j).2 -
        TFreeLaurentGQSP.ryMatrix (cs₂ j).1 (cs₂ j).2‖ := by
  intro W W_inv
  rcases laurentWalk_pair_embed_mem_unitaryGroup rBE U_BE with ⟨hW, hWinv⟩
  let L_op := (Circuit.H q_sig).eval.1 *
    (rBE.embedMatrix W_inv * (QRegister.singleton q_sig).basisOutcomeProjector 0 +
      (QRegister.singleton q_sig).basisOutcomeProjector 1)
  let R_op := ((QRegister.singleton q_sig).basisOutcomeProjector 0 +
    rBE.embedMatrix W * (QRegister.singleton q_sig).basisOutcomeProjector 1) *
    (Circuit.H q_sig).eval.1
  have hL : ‖L_op‖ ≤ 1 := norm_of_mem_unitaryGroup_le_one (Submonoid.mul_mem _
    (Circuit.H q_sig).eval.2 (c0_step_mem_unitaryGroup q_sig _ hWinv
      (embedMatrix_comm_sig_proj rBE q_sig hBE_sig W_inv 0)))
  have hR : ‖R_op‖ ≤ 1 := norm_of_mem_unitaryGroup_le_one (Submonoid.mul_mem _
    (c1_step_mem_unitaryGroup q_sig _ hW
      (embedMatrix_comm_sig_proj rBE q_sig hBE_sig W 1)) (Circuit.H q_sig).eval.2)
  rw [show biGqspSegmentOp q_sig (rBE.embedMatrix W) (rBE.embedMatrix W_inv) cs₁ M -
      biGqspSegmentOp q_sig (rBE.embedMatrix W) (rBE.embedMatrix W_inv) cs₂ M =
    L_op * (biGqspLoopOp q_sig (rBE.embedMatrix W) (rBE.embedMatrix W_inv) cs₁ M -
      biGqspLoopOp q_sig (rBE.embedMatrix W) (rBE.embedMatrix W_inv) cs₂ M) * R_op by
    unfold biGqspSegmentOp
    dsimp [L_op, R_op]
    noncomm_ring]
  exact (norm_mul_le_of_right_le_one hR).trans ((norm_mul_le_of_left_le_one hL).trans
    (norm_biGqspLoopOp_sub_le q_sig _ _ (biWalkStepOp_mem_unitaryGroup q_sig _ _ hW hWinv
      (embedMatrix_comm_sig_proj rBE q_sig hBE_sig W 0)
      (embedMatrix_comm_sig_proj rBE q_sig hBE_sig W_inv 0)
      (embedMatrix_comm_sig_proj rBE q_sig hBE_sig W_inv 1)) cs₁ cs₂ M hcs₁ hcs₂))
set_option exponentiation.threshold 2048 in
def biCatBridgeCheckBle (M N_cat : ℕ) (C_list : List ℕ) (g_list : List DyadicRyGate) : Bool :=
  FastRecurrenceVerifier.forceNatFast (Nat.factorial 29) fun K29_fact ↦
  FastRecurrenceVerifier.forceNatFast (Nat.mul K29_fact (Nat.pow 2 1460)) fun gate_scale ↦
  FastRecurrenceVerifier.forceNatFast
    (catPolyDiffListNat K29_fact gate_scale C_list g_list 0)
    fun poly_sum ↦
      let analytic_sum := Nat.mul (Nat.add M 1) (Nat.mul K29_fact (Nat.pow 2 1458))
      Nat.ble (Nat.add poly_sum analytic_sum) (Nat.mul N_cat gate_scale)
open scoped Matrix.Norms.L2Operator in
set_option exponentiation.threshold 2048 in
theorem sum_norm_ryMatrix_biCS_sub_gate_le_of_ble (M N_cat : ℕ) (C_list : List ℕ)
    (hC_len : C_list.length = M + 1) (C : Fin (M + 1) → Fin (2 ^ 42))
    (hC : ∀ i : Fin (M + 1), C i = Fin.ofNat (2 ^ 42) (C_list.getD i.val 0))
    (g_list : List DyadicRyGate) (hg_len : g_list.length = M + 1) (g : ℕ → DyadicRyGate)
    (hg : ∀ s, g s = g_list.getD s defaultGate)
    (h_ble : biCatBridgeCheckBle M N_cat C_list g_list = true) : (∑ j ∈ Finset.range (M + 1),
      ‖TFreeLaurentGQSP.ryMatrix (biCS M C j).1 (biCS M C j).2 -
          TFreeLaurentGQSP.ryMatrix (gateCos 48 (g j)) (gateSin 48 (g j))‖) ≤
      (N_cat : ℝ) / 2 ^ 48 := by
  let K29_fact := Nat.factorial 29
  let gate_scale := K29_fact * 2 ^ 1460
  let D_tay : ℝ := (K29_fact : ℝ) * (2 : ℝ) ^ (52 * 29)
  have hpoly (cs : List ℕ) : ∀ (gs : List DyadicRyGate) (_ : cs.length = gs.length) (acc : ℕ),
      catPolyDiffListNat K29_fact gate_scale cs gs acc = acc + ∑ i ∈ Finset.range cs.length,
        gateBridgeDiffNat K29_fact gate_scale (cs.getD i 0) (gs.getD i defaultGate) := by
    induction cs with
    | nil =>
      rintro (_ | _) hlen acc
      · simp [catPolyDiffListNat]
      · simp at hlen
    | cons c cs ih =>
      rintro (_ | ⟨g0, gs⟩) hlen acc
      · simp at hlen
      · rw [catPolyDiffListNat, FastRecurrenceVerifier.forceNatFast_eq, Nat.add_eq,
          ih gs (by simpa using hlen), List.length_cons, Finset.sum_range_succ']
        simp only [List.getD_eq_getElem?_getD, List.getElem?_cons_zero,
          List.getElem?_cons_succ, Option.getD_some]
        omega
  unfold biCatBridgeCheckBle at h_ble
  rw [FastRecurrenceVerifier.forceNatFast_eq, FastRecurrenceVerifier.forceNatFast_eq,
    FastRecurrenceVerifier.forceNatFast_eq] at h_ble
  have h_nat_le : catPolyDiffListNat K29_fact gate_scale C_list g_list 0 +
      (M + 1) * (K29_fact * 2 ^ 1458) ≤ N_cat * gate_scale := Nat.ble_eq.mp h_ble
  rw [hpoly C_list g_list (hC_len.trans hg_len.symm) 0, zero_add, hC_len] at h_nat_le
  have h_real_le : (∑ i ∈ Finset.range (M + 1), (gateBridgeDiffNat K29_fact gate_scale
      (C_list.getD i 0) (g_list.getD i defaultGate) : ℝ)) + ((M + 1 : ℕ) : ℝ) *
      ((K29_fact : ℝ) * (2 : ℝ) ^ 1458) ≤ (N_cat : ℝ) * (gate_scale : ℝ) := by
    exact_mod_cast h_nat_le
  have hD_pos : (0 : ℝ) < D_tay := by positivity
  have habs_cast (s1 m1 s2 m2) : ((FastRecurrenceVerifier.smAbsDiff s1 m1 s2 m2 : ℕ) : ℝ) =
      |(FastRecurrenceVerifier.smToInt s1 m1 : ℝ) -
        (FastRecurrenceVerifier.smToInt s2 m2 : ℝ)| := by
    exact_mod_cast FastRecurrenceVerifier.smAbsDiff_cast_eq s1 m1 s2 m2
  have hmul_sc (s m) : (FastRecurrenceVerifier.smToInt s (Nat.mul m gate_scale) : ℝ) =
      D_tay * ((FastRecurrenceVerifier.smToInt s m : ℝ) / 2 ^ 48) := by
    have hm := FastRecurrenceVerifier.smToInt_mul s m false gate_scale
    simp only [Bool.xor_false, FastRecurrenceVerifier.smToInt_false] at hm
    rw [hm, Int.cast_mul, Int.cast_natCast, show (gate_scale : ℝ) = D_tay / 2 ^ 48 by
      dsimp only [gate_scale, D_tay, K29_fact]
      push_cast
      rw [eq_div_iff (by positivity : (2 : ℝ) ^ 48 ≠ 0),
        show (1508 : ℕ) = 1460 + 48 from rfl, pow_add]
      ring]
    ring
  have h_term_bound : ∀ j ∈ Finset.range (M + 1),
      D_tay * ‖TFreeLaurentGQSP.ryMatrix (biCS M C j).1 (biCS M C j).2 -
          TFreeLaurentGQSP.ryMatrix (gateCos 48 (g j)) (gateSin 48 (g j))‖ ≤
        (gateBridgeDiffNat K29_fact gate_scale (C_list.getD j 0)
          (g_list.getD j defaultGate) : ℝ) + (K29_fact : ℝ) * (2 : ℝ) ^ 1458 := by
    intro j hj
    rw [Finset.mem_range] at hj
    dsimp only [biCS, biCode]
    rw [dite_eq_left hj, hC ⟨j, hj⟩, hg j]
    let c_raw := C_list.getD j 0
    let gj := g_list.getD j defaultGate
    let C_d : Fin (2 ^ 42) := Fin.ofNat (2 ^ 42) c_raw
    let x_d := (catRatNx C_d.val : ℝ) / 2 ^ 52
    let sin_signed := if catSymNeg C_d.val then -sinTaylor 15 x_d else sinTaylor 15 x_d
    rcases FastRecurrenceVerifier.gateSM_toInt gj with ⟨hgc, hgs⟩
    have h_cast : (gateBridgeDiffNat K29_fact gate_scale c_raw gj : ℝ) =
        D_tay * (|cosTaylor 15 x_d - gateCos 48 gj| + |sin_signed - gateSin 48 gj|) := by
      unfold gateBridgeDiffNat
      rw [show Nat.mod c_raw (Nat.pow 2 42) = C_d.val from rfl,
        FastRecurrenceVerifier.forceNatFast_eq, FastRecurrenceVerifier.forceNatFast_eq,
        FastRecurrenceVerifier.forceNatFast_eq, Nat.add_eq, Nat.cast_add, habs_cast, habs_cast,
        hmul_sc, hmul_sc, hgc, hgs, (cos_sin_taylorSM_cast_eq (catRatNx C_d.val) 15 le_rfl).1,
        show ((Nat.factorial 29 : ℝ) * (2 : ℝ) ^ (52 * 29)) = D_tay from rfl,
        show (FastRecurrenceVerifier.smToInt
          (if catSymNeg C_d.val then Bool.not (sinTaylorSM K29_fact (catRatNx C_d.val) 15).1
            else (sinTaylorSM K29_fact (catRatNx C_d.val) 15).1)
          (sinTaylorSM K29_fact (catRatNx C_d.val) 15).2 : ℝ) = D_tay * sin_signed by
          dsimp only [sin_signed]
          cases catSymNeg C_d.val
          · exact (cos_sin_taylorSM_cast_eq (catRatNx C_d.val) 15 le_rfl).2
          · simp only [↓reduceIte, FastRecurrenceVerifier.smToInt_neg, Int.cast_neg]
            rw [(cos_sin_taylorSM_cast_eq (catRatNx C_d.val) 15 le_rfl).2]
            dsimp only [D_tay, K29_fact, x_d]
            ring,
        ← gateCos, ← gateSin, ← mul_sub, ← mul_sub, abs_mul D_tay, abs_mul D_tay,
        abs_of_pos hD_pos, ← mul_add]
    have h_mul := mul_le_mul_of_nonneg_left
      (norm_ryMatrix_catCS42_sub_gate_le C_d gj) (le_of_lt hD_pos)
    have h_an : D_tay * (1 / 2 ^ 50) = (K29_fact : ℝ) * (2 : ℝ) ^ 1458 := by
      dsimp only [D_tay]
      rw [show (52 * 29 : ℕ) = 1458 + 50 from rfl, pow_add]
      ring
    dsimp only [K29_fact, gate_scale, D_tay, C_d, c_raw, gj, x_d, sin_signed]
      at h_mul h_cast h_an ⊢
    rw [add_assoc, mul_add, h_an, ← h_cast, add_comm] at h_mul
    exact h_mul
  have h_sum_bound : D_tay * (∑ j ∈ Finset.range (M + 1),
      ‖TFreeLaurentGQSP.ryMatrix (biCS M C j).1 (biCS M C j).2 -
          TFreeLaurentGQSP.ryMatrix (gateCos 48 (g j)) (gateSin 48 (g j))‖) ≤
      (N_cat : ℝ) * (gate_scale : ℝ) := by
    rw [Finset.mul_sum]
    have hsum1 := Finset.sum_le_sum h_term_bound
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum1
    dsimp only [K29_fact, gate_scale] at hsum1 h_real_le ⊢
    linarith
  refine le_of_mul_le_mul_left (h_sum_bound.trans_eq ?_) hD_pos
  dsimp only [D_tay, gate_scale]
  rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat,
    show (52 * 29 : ℕ) = 1460 + 48 by rfl, pow_add]
  ring
open scoped Matrix.Norms.L2Operator in
theorem norm_biCatSegment_sub_exp_mul_proj_le_of_rec_bound {k m_BE m : ℕ} (hm : m_BE + 1 ≤ m)
    {α : ℝ} (τ : ℝ) (hα : 0 < α) (hτ : 0 ≤ τ) {A : Operator (2 ^ k)}
    {U_BE : Unitary (2 ^ (k + m_BE))} (hBE : IsQubitizedBlockEncodingUnitary α A U_BE)
    (M K β_nat N_rec N_tay N_cat : ℕ) (hMK : M + 1 ≤ K) (hβ_lt : β_nat < K + 2)
    (hβ_eq : α * τ = (β_nat : ℝ)) (hnorm_A : ‖(-Complex.I * (τ : ℂ)) • A‖ ≤ α * τ)
    (C_list : List ℕ) (hC_len : C_list.length = M + 1) (C : Fin (M + 1) → Fin (2 ^ 42))
    (hC : ∀ i : Fin (M + 1), C i = Fin.ofNat (2 ^ 42) (C_list.getD i.val 0))
    (g_list : List DyadicRyGate) (hg_len : g_list.length = M + 1) (g : ℕ → DyadicRyGate)
    (hg : ∀ s, g s = g_list.getD s defaultGate)
    (hcs_int : ∀ j < M + 1, gateNc (g j) ^ 2 + gateNs (g j) ^ 2 ≤ (2 ^ (2 * 48) : ℤ))
    (h_rec_three : let res := biGqspRecurrence M (fun s ↦ gatePair 48 (g s))
      (∑ d ∈ Finset.range (K + 1),
        |laurentChebWeight (M + 1) res.1 d - chebTaylorWeight (β_nat : ℝ) K d|) +
      (∑ j : Fin (M + 1), laurentAsymDefect (M + 1) res.1 j) +
      (∑ i : Fin (2 * (M + 1) + 1), |res.2 i|) ≤ (N_rec : ℝ) / 2 ^ 48)
    (h_tay_nat : β_nat ^ (K + 1) * (K + 2) * 2 ^ 48 ≤ N_tay * (K + 1).factorial * (K + 2 - β_nat))
    (h_cat_ble : biCatBridgeCheckBle M N_cat C_list g_list = true) :
    let sys : QRegister k (k + m) := QRegister.block 0 k (by omega)
    let anc : QRegister m (k + m) := QRegister.block k m le_rfl
    let rBE : QRegister (k + m_BE) (k + m) := QRegister.block 0 (k + m_BE) (by omega)
    let q_sig : Wire (k + m) := ⟨k + m_BE, by omega⟩
    let P_anc := anc.basisOutcomeProjector 0
    let W := laurentWalk U_BE
    let W_inv := laurentWalkInv U_BE
    let U_cat_eff := biGqspSegmentOp q_sig (rBE.embedMatrix W) (rBE.embedMatrix W_inv) (biCS M C) M
    let U_target := sys.embedMatrix (NormedSpace.exp ((-Complex.I * (τ : ℂ)) • A))
    ‖(U_cat_eff - U_target) * P_anc‖ ≤ ((N_rec + N_tay + N_cat : ℕ) : ℝ) / 2 ^ 48 := by
  intro sys anc rBE q_sig P_anc W W_inv U_cat_eff U_target
  let U_rec := biGqspSegmentOp q_sig (rBE.embedMatrix W) (rBE.embedMatrix W_inv)
    (fun s ↦ gatePair 48 (g s)) M
  have h_cat_rec_P : ‖(U_cat_eff - U_rec) * P_anc‖ ≤ (N_cat : ℝ) / 2 ^ 48 :=
    (norm_mul_le_of_right_le_one (norm_basisOutcomeProjector_le_one anc 0)).trans
      ((norm_biGqspSegmentOp_sub_le rBE q_sig (block_zero_disjoint_singleton _ q_sig le_rfl)
        U_BE M (biCS M C) (fun s ↦ gatePair 48 (g s))
        (fun _ _ ↦ (Real.cos_sq_add_sin_sq _).le)
        (fun j hj ↦ gateCos_sq_add_gateSin_sq_le_one 48 (g j) (hcs_int j hj))).trans
      (sum_norm_ryMatrix_biCS_sub_gate_le_of_ble M N_cat C_list hC_len C hC g_list hg_len g hg
        h_cat_ble))
  have hβ_lt_real : α * τ < (K + 2 : ℝ) := hβ_eq.symm ▸ (by exact_mod_cast hβ_lt)
  have h4 := norm_biGqspRecurrence_sub_exp_mul_proj_le hm τ hα hτ hBE M K hMK
    hβ_lt_real hnorm_A (fun s ↦ gatePair 48 (g s))
  dsimp only at h4 h_rec_three
  rw [hβ_eq] at h4
  have h_tay : (((K + 1).factorial : ℝ)⁻¹ * (β_nat : ℝ) ^ (K + 1)) *
      (1 - (β_nat : ℝ) / (K + 2 : ℝ))⁻¹ ≤ (N_tay : ℝ) / 2 ^ 48 := by
    have hpos : (0 : ℝ) < ((K + 2 - β_nat : ℕ) : ℝ) := by
      exact_mod_cast (show 0 < K + 2 - β_nat by omega)
    rw [show 1 - (β_nat : ℝ) / (K + 2 : ℝ) = ((K + 2 - β_nat : ℕ) : ℝ) / (K + 2 : ℝ) by
      rw [one_sub_div (by positivity), Nat.cast_sub (by omega), Nat.cast_add, Nat.cast_ofNat],
      inv_div, ← div_eq_inv_mul, div_mul_div_comm,
      div_le_div_iff₀ (mul_pos (by positivity) hpos) (by positivity), ← mul_assoc]
    exact_mod_cast h_tay_nat
  have h_tri := norm_add_le ((U_cat_eff - U_rec) * P_anc) ((U_rec - U_target) * P_anc)
  rw [show (U_cat_eff - U_rec) * P_anc + (U_rec - U_target) * P_anc =
    (U_cat_eff - U_target) * P_anc by noncomm_ring] at h_tri
  push_cast
  linarith
end BidirectionalOperatorTelescoping
end BidirectionalCatalyzedGQSPBridge
namespace BidirectionalIntervalRecurrenceVerifier
open Real Operator Matrix Circuit SpecsAux
open TFreeLaurentGQSP CatalyzedLaurentGQSP
open TFreeLaurentGQSPPresets
open TFreeLaurentGQSPPresets.FastRecurrenceVerifier
open TFreeLaurentGQSPPresets.FastIntervalRecurrenceVerifier
open CatalyzedLaurentGQSPBridge
open BidirectionalCatalyzedGQSP
open BidirectionalCatalyzedGQSPBridge
open scoped Matrix
theorem sq_smToInt (s : Bool) (m : ℕ) : smToInt s m ^ 2 = ((m * m : ℕ) : ℤ) := by
  cases s <;> simp [smToInt, sq]
theorem gateCos_eq_smToInt_div (b D : ℕ) (hD : D = 2 ^ b) (g : DyadicRyGate) :
    gateCos b g = (smToInt (gateSM g).1.1 (gateSM g).1.2 : ℝ) / (D : ℝ) := by
  simp [gateCos, (gateSM_toInt g).1, hD]
theorem gateSin_eq_smToInt_div (b D : ℕ) (hD : D = 2 ^ b) (g : DyadicRyGate) :
    gateSin b g = (smToInt (gateSM g).2.1 (gateSM g).2.2 : ℝ) / (D : ℝ) := by
  simp [gateSin, (gateSM_toInt g).2, hD]
def gatesContractionBleAux (D2 : ℕ) : List DyadicRyGate → Bool
  | [] => true
  | g :: gs =>
      let gsm := gateSM g
      let mc := gsm.1.2
      let ms := gsm.2.2
      match Nat.ble (Nat.add (Nat.mul mc mc) (Nat.mul ms ms)) D2 with
      | true => gatesContractionBleAux D2 gs
      | false => false
def gatesContractionBle (b : ℕ) (g_list : List DyadicRyGate) : Bool := forceNatFast
    (Nat.pow 2 (Nat.mul 2 b)) fun D2 ↦ gatesContractionBleAux D2 g_list
theorem gatesContractionBleAux_true_imp (D2 : ℕ) :
    ∀ (g_list : List DyadicRyGate) (j : ℕ), gatesContractionBleAux D2 g_list = true →
      j < g_list.length → let g := g_list.getD j defaultGate
      (gateSM g).1.2 * (gateSM g).1.2 + (gateSM g).2.2 * (gateSM g).2.2 ≤ D2
  | [], _, _, hj => by simp at hj
  | g0 :: gs, j, hble, hj => by
    unfold gatesContractionBleAux at hble
    dsimp only at hble
    rcases h0 : Nat.ble (Nat.add (Nat.mul (gateSM g0).1.2 (gateSM g0).1.2)
      (Nat.mul (gateSM g0).2.2 (gateSM g0).2.2)) D2 with _ | _
    · rw [h0] at hble
      cases hble
    · rw [h0] at hble
      rcases j with _ | k
      · simpa [List.getD_eq_getElem?_getD, Nat.ble_eq, Nat.add_eq, Nat.mul_eq] using h0
      · simpa [List.getD_eq_getElem?_getD] using
          gatesContractionBleAux_true_imp D2 gs k hble (Nat.lt_of_succ_lt_succ hj)
theorem gates_contraction_of_ble (b : ℕ) (g_list : List DyadicRyGate) (g : ℕ → DyadicRyGate)
    (hg : ∀ s, g s = g_list.getD s defaultGate) (h_ble : gatesContractionBle b g_list = true) :
    ∀ j < g_list.length, gateNc (g j) ^ 2 + gateNs (g j) ^ 2 ≤ (2 ^ (2 * b) : ℤ) := by
  unfold gatesContractionBle at h_ble
  simp only [forceNatFast_eq, Nat.pow_eq, Nat.mul_eq] at h_ble
  intro j hj
  rw [hg j, ← (gateSM_toInt _).1, ← (gateSM_toInt _).2, sq_smToInt, sq_smToInt]
  exact_mod_cast gatesContractionBleAux_true_imp (2 ^ (2 * b)) g_list j h_ble hj
theorem hadamardSumU_spec (ux uy B R_cur : ℕ) (X Y : ℝ)
    (hux_mag : |(ux : ℤ) - (B : ℤ)| ≤ (B : ℤ)) (huy_mag : |(uy : ℤ) - (B : ℤ)| ≤ (B : ℤ))
    (hux_err : |X - ((ux : ℝ) - (B : ℝ))| ≤ (R_cur : ℝ))
    (huy_err : |Y - ((uy : ℝ) - (B : ℝ))| ≤ (R_cur : ℝ)) : let u' := (ux + uy) / 2
    |(u' : ℤ) - (B : ℤ)| ≤ (B : ℤ) ∧
    |(2 : ℝ)⁻¹ * (X + Y) - ((u' : ℝ) - (B : ℝ))| ≤ ((R_cur + 1 : ℕ) : ℝ) := by
  intro u'
  have hux_b := abs_le.mp hux_mag
  have huy_b := abs_le.mp huy_mag
  refine ⟨abs_le.mpr ⟨show -(B : ℤ) ≤ (((ux + uy) / 2 : ℕ) : ℤ) - B by omega,
    show (((ux + uy) / 2 : ℕ) : ℤ) - B ≤ B by omega⟩, ?_⟩
  rw [show (2 : ℝ)⁻¹ * (X + Y) - ((u' : ℝ) - (B : ℝ)) =
      (2 : ℝ)⁻¹ * ((X - ((ux : ℝ) - (B : ℝ))) + (Y - ((uy : ℝ) - (B : ℝ))) +
        (((ux + uy) % 2 : ℕ) : ℝ)) by
      have : 2 * (u' : ℝ) + (((ux + uy) % 2 : ℕ) : ℝ) = (ux : ℝ) + (uy : ℝ) := by
        exact_mod_cast Nat.div_add_mod (ux + uy) 2
      linarith,
    abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (2 : ℝ)⁻¹), Nat.cast_add, Nat.cast_one]
  linarith [abs_add_le ((X - ((ux : ℝ) - (B : ℝ))) + (Y - ((uy : ℝ) - (B : ℝ))))
      (((ux + uy) % 2 : ℕ) : ℝ), abs_add_le (X - ((ux : ℝ) - (B : ℝ))) (Y - ((uy : ℝ) - (B : ℝ))),
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ (((ux + uy) % 2 : ℕ) : ℝ)),
    (by exact_mod_cast (show (ux + uy) % 2 ≤ 1 by omega) : (((ux + uy) % 2 : ℕ) : ℝ) ≤ 1)]
def biHadamardFinishPair (B B2 : ℕ) : List PQPair → ℕ → List PQPair
  | [], q_prev => mkPQConsLazy (Nat.div (Nat.add B q_prev) 2)
      (Nat.div (Nat.add B (Nat.sub B2 q_prev)) 2) []
  | ⟨ph, qh⟩ :: t, q_prev => mkPQConsLazy (Nat.div (Nat.add ph q_prev) 2)
      (Nat.div (Nat.add ph (Nat.sub B2 q_prev)) 2) (biHadamardFinishPair B B2 t qh)
theorem biHadamardFinishPair_spec (M B B2 R_loop : ℕ) (scale0 : ℝ) (hB2 : B2 = 2 * B)
    (cs : ℕ → ℝ × ℝ) (pqM : List PQPair) (hpqM_len : pqM.length = 2 * (M + 1))
    (hpqM : ∀ k (hk : k < 2 * (M + 1)), let pk := (pqM.getD k ⟨B, B⟩).p
      let qk := (pqM.getD k ⟨B, B⟩).q
      let idx : Fin (2 * (M + 1) + 1) := ⟨1 + k, by omega⟩
      |(pk : ℤ) - (B : ℤ)| ≤ (B : ℤ) ∧ |(qk : ℤ) - (B : ℤ)| ≤ (B : ℤ) ∧
      |scale0 * (biGqspRunLoop M cs M).1 idx - ((pk : ℝ) - (B : ℝ))| ≤ (R_loop : ℝ) ∧
      |scale0 * (biGqspRunLoop M cs M).2 idx - ((qk : ℝ) - (B : ℝ))| ≤ (R_loop : ℝ)) :
    let pq_final := biHadamardFinishPair B B2 pqM B
    let res := biGqspRecurrence M cs
    pq_final.length = 2 * (M + 1) + 1 ∧ ∀ k (hk : k < 2 * (M + 1) + 1),
      let pk := (pq_final.getD k ⟨B, B⟩).p
      let qk := (pq_final.getD k ⟨B, B⟩).q
      |(pk : ℤ) - (B : ℤ)| ≤ (B : ℤ) ∧ |(qk : ℤ) - (B : ℤ)| ≤ (B : ℤ) ∧
      |scale0 * res.1 ⟨k, hk⟩ - ((pk : ℝ) - (B : ℝ))| ≤ ((R_loop + 1 : ℕ) : ℝ) ∧
      |scale0 * res.2 ⟨k, hk⟩ - ((qk : ℝ) - (B : ℝ))| ≤ ((R_loop + 1 : ℕ) : ℝ) := by
  have hlen (pq : List PQPair) : ∀ qp,
      (biHadamardFinishPair B B2 pq qp).length = pq.length + 1 := by
    induction pq with
    | nil => exact fun _ ↦ by simp [biHadamardFinishPair, mkPQConsLazy_eq]
    | cons hd tl ih => exact fun _ ↦ by simp [biHadamardFinishPair, mkPQConsLazy_eq, ih hd.q]
  have hgetD (pq : List PQPair) : ∀ (qp k : ℕ), k < pq.length + 1 →
      (biHadamardFinishPair B B2 pq qp).getD k ⟨B, B⟩ =
        ⟨((pq.getD k ⟨B, B⟩).p + if k = 0 then qp else (pq.getD (k - 1) ⟨B, B⟩).q) / 2,
          ((pq.getD k ⟨B, B⟩).p +
            (B2 - if k = 0 then qp else (pq.getD (k - 1) ⟨B, B⟩).q)) / 2⟩ := by
    induction pq with
    | nil =>
      intro qp k hk
      rcases Nat.lt_one_iff.mp hk with rfl
      dsimp [biHadamardFinishPair]
      rw [mkPQConsLazy_eq]
      rfl
    | cons hd tl ih =>
      rcases hd with ⟨ph0, qh0⟩
      rintro qp (_ | k) hk
      · dsimp [biHadamardFinishPair]
        rw [mkPQConsLazy_eq]
        rfl
      · dsimp only [biHadamardFinishPair]
        rw [mkPQConsLazy_eq, List.getD_eq_getElem?_getD, List.getElem?_cons_succ,
          ← List.getD_eq_getElem?_getD, ih qh0 k (by simpa using hk)]
        have hp : ((⟨ph0, qh0⟩ :: tl).getD (k + 1) ⟨B, B⟩).p = (tl.getD k ⟨B, B⟩).p := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_cons_succ, ← List.getD_eq_getElem?_getD]
        have hq : (if k + 1 = 0 then qp else ((⟨ph0, qh0⟩ :: tl).getD k ⟨B, B⟩).q) =
            if k = 0 then qh0 else (tl.getD (k - 1) ⟨B, B⟩).q := by
          rcases k with _ | j
          · rfl
          · simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
            rw [List.getD_eq_getElem?_getD, List.getElem?_cons_succ, ← List.getD_eq_getElem?_getD]
        simp only [Nat.add_sub_cancel, hp, hq]
  intro pq_final res
  refine ⟨by rw [hlen, hpqM_len], fun k hk ↦ ?_⟩
  let ph := (pqM.getD k ⟨B, B⟩).p
  let qp := if k = 0 then B else (pqM.getD (k - 1) ⟨B, B⟩).q
  let res_M := biGqspRunLoop M cs M
  let X_k : ℝ := scale0 * shiftLeft (M + 1) res_M.1 ⟨k, hk⟩
  let Y_k : ℝ := scale0 * res_M.2 ⟨k, hk⟩
  have hph : |(ph : ℤ) - (B : ℤ)| ≤ (B : ℤ) ∧ |X_k - ((ph : ℝ) - (B : ℝ))| ≤ (R_loop : ℝ) := by
    dsimp [X_k, shiftLeft]
    by_cases hk_lt : k < 2 * (M + 1)
    · rw [dite_eq_left hk_lt, show (⟨k + 1, by omega⟩ : Fin (2 * (M + 1) + 1)) = ⟨1 + k, by omega⟩
        from Fin.ext (Nat.add_comm k 1)]
      exact ⟨(hpqM k hk_lt).1, (hpqM k hk_lt).2.2.1⟩
    · rw [dite_eq_right hk_lt]
      simp [ph, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : pqM.length ≤ k),
        Nat.cast_nonneg]
  have hqp : |(qp : ℤ) - (B : ℤ)| ≤ (B : ℤ) ∧ |Y_k - ((qp : ℝ) - (B : ℝ))| ≤ (R_loop : ℝ) := by
    rcases k with _ | j
    · dsimp [qp, Y_k]
      rw [(biGqspRunLoop_support M cs M le_rfl 0 (Or.inl (show 0 < (M + 1) - M by omega))).2]
      simp [Nat.cast_nonneg]
    · rcases hpqM j (by omega) with ⟨_, h2, _, h4⟩
      dsimp [qp, Y_k]
      rw [show (⟨j + 1, hk⟩ : Fin (2 * (M + 1) + 1)) = ⟨1 + j, by omega⟩
        from Fin.ext (Nat.add_comm j 1)]
      exact ⟨h2, h4⟩
  have hqp_le : qp ≤ B2 := by
    have := (abs_le.mp hqp.1).2
    omega
  have hqp'_mag : |((B2 - qp : ℕ) : ℤ) - (B : ℤ)| ≤ (B : ℤ) := by
    rw [Nat.cast_sub hqp_le, hB2]
    push_cast
    rw [show 2 * (B : ℤ) - (qp : ℤ) - (B : ℤ) = -((qp : ℤ) - (B : ℤ)) by ring, abs_neg]
    exact hqp.1
  have hqp'_err : |(-Y_k) - (((B2 - qp : ℕ) : ℝ) - (B : ℝ))| ≤ (R_loop : ℝ) := by
    rw [Nat.cast_sub hqp_le, hB2]
    push_cast
    rw [show -Y_k - (2 * (B : ℝ) - (qp : ℝ) - (B : ℝ)) = -(Y_k - ((qp : ℝ) - (B : ℝ))) by ring,
      abs_neg]
    exact hqp.2
  have h_sum := hadamardSumU_spec ph qp B R_loop X_k Y_k hph.1 hqp.1 hph.2 hqp.2
  have h_diff := hadamardSumU_spec ph (B2 - qp) B R_loop X_k (-Y_k)
    hph.1 hqp'_mag hph.2 hqp'_err
  rw [hgetD pqM B k (by omega),
    show scale0 * res.1 ⟨k, hk⟩ = (2 : ℝ)⁻¹ * (X_k + Y_k) by
      dsimp [res, biGqspRecurrence, X_k, Y_k, res_M]
      ring,
    show scale0 * res.2 ⟨k, hk⟩ = (2 : ℝ)⁻¹ * (X_k + -Y_k) by
      dsimp [res, biGqspRecurrence, X_k, Y_k, res_M]
      ring]
  exact ⟨h_sum.1, h_diff.1, h_sum.2, h_diff.2⟩
open Function FullScaleBESector SpecsAux.SpecMirror
section BiPresetB6
def natDist (a b : ℕ) : ℕ := (a - b) + (b - a)
end BiPresetB6
end BidirectionalIntervalRecurrenceVerifier
section BiGqspRootSection
section BiGqspChunkedMillerCore
namespace SpecsAux.SpecMirror.BiGqspChunkedMillerCore
open Real TFreeLaurentGQSPPresets
open TFreeLaurentGQSPPresets.FastRecurrenceVerifier
open TFreeLaurentGQSPPresets.FastIntervalRecurrenceVerifier
open BidirectionalIntervalRecurrenceVerifier
@[inline] def millerStepResidualNat (β_nat Bw d j_prev j_cur j_next : ℕ) : ℕ :=
  let lhs : ℤ := (β_nat : ℤ) * (((j_prev : ℤ) - (Bw : ℤ)) + ((j_next : ℤ) - (Bw : ℤ)))
  let rhs : ℤ := (2 * (d : ℤ)) * ((j_cur : ℤ) - (Bw : ℤ))
  Int.natAbs (lhs - rhs)
lemma natAbs_cast_real (z : ℤ) : ((Int.natAbs z : ℕ) : ℝ) = |(z : ℝ)| := by
  rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]
end SpecsAux.SpecMirror.BiGqspChunkedMillerCore
end BiGqspChunkedMillerCore
end BiGqspRootSection
namespace SpecsAux
section BiGqspChunkedMillerCert_Part26
namespace SpecMirror.BiGqspChunkedMillerCert
section ConfigBiGqspChunkedMillerCert_Part26
set_option maxRecDepth 200000
open TFreeLaurentGQSP TFreeLaurentGQSPPresets
open TFreeLaurentGQSPPresets.FastRecurrenceVerifier
open TFreeLaurentGQSPPresets.FastIntervalRecurrenceVerifier
open BidirectionalCatalyzedGQSP
open BidirectionalIntervalRecurrenceVerifier
open SpecsAux.SpecMirror.BiGqspChunkedMillerCore
def prodRangeLinear_p26 (a : ℕ) : ℕ → ℕ
  | 0 => 1
  | k + 1 => prodRangeLinear_p26 a k * (a + k)
theorem prodRangeLinear_p26_one_eq_fact : ∀ n : ℕ, prodRangeLinear_p26 1 n = n.factorial
  | 0 => rfl
  | k + 1 =>
    by rw [prodRangeLinear_p26, prodRangeLinear_p26_one_eq_fact k, Nat.factorial_succ]; ring
theorem prodRangeLinear_p26_add (a m : ℕ) :
    ∀ k : ℕ, prodRangeLinear_p26 a (m + k) = prodRangeLinear_p26 a m * prodRangeLinear_p26 (a + m) k
  | 0 => by simp [prodRangeLinear_p26]
  | k + 1 => by
      rw [← Nat.add_assoc, prodRangeLinear_p26, prodRangeLinear_p26_add a m k, prodRangeLinear_p26,
        show a + (m + k) = a + m + k by omega]
      ring
end ConfigBiGqspChunkedMillerCert_Part26
end SpecMirror.BiGqspChunkedMillerCert
end BiGqspChunkedMillerCert_Part26
section BiGqspChebWeightCertS4805
namespace SpecMirror.BiGqspChebWeightCertS4805
section ConfigBiGqspChebWeightCertS4805
set_option maxRecDepth 200000
open TFreeLaurentGQSP TFreeLaurentGQSPPresets
open TFreeLaurentGQSPPresets.FastRecurrenceVerifier
open TFreeLaurentGQSPPresets.FastIntervalRecurrenceVerifier
open BidirectionalCatalyzedGQSP
open BidirectionalCatalyzedGQSPBridge
open BidirectionalIntervalRecurrenceVerifier
open SpecsAux.SpecMirror.BiGqspChunkedMillerCore
open SpecsAux.SpecMirror.BiGqspChunkedMillerCert
def powChebQ (n d : ℕ) : ℕ := if d = 0 then 2 * powChebScaled n 0 else powChebScaled n d
lemma powChebQ_succ_succ (n : ℕ) : ∀ d : ℕ,
    (powChebQ (n + 1) (d + 1) : ℝ) = (powChebQ n d : ℝ) + (powChebQ n (d + 2) : ℝ)
  | 0 => by simp [powChebQ, powChebScaled, stepChebScaled]
  | _ + 1 => by simp [powChebQ, powChebScaled, stepChebScaled]
theorem powChebQ_bessel_rec : ∀ (n d : ℕ), ((d + 1 : ℕ) : ℝ) * (powChebQ (n + 1) (d + 1) : ℝ) +
      ((n + 1 : ℕ) : ℝ) * (powChebQ n (d + 2) : ℝ) = ((n + 1 : ℕ) : ℝ) * (powChebQ n d : ℝ)
  | 0, 0 => by simp [powChebQ, powChebScaled, stepChebScaled]
  | 0, _ + 1 => by simp [powChebQ, powChebScaled, stepChebScaled]
  | n + 1, 0 => by
      have h1 := powChebQ_bessel_rec n 1
      have hs0 : (powChebQ (n + 1) 0 : ℝ) = 2 * (powChebQ n 1 : ℝ) := by
        simp [powChebQ, powChebScaled, stepChebScaled]
      push_cast at h1 ⊢
      linear_combination h1 + ((n : ℝ) + 1) * powChebQ_succ_succ n 1 +
        powChebQ_succ_succ (n + 1) 0 - ((n : ℝ) + 1) * hs0
  | n + 1, m + 1 => by
      have h1 := powChebQ_bessel_rec n m
      have h2 := powChebQ_bessel_rec n (m + 2)
      push_cast at h1 h2 ⊢
      linear_combination ((m : ℝ) + 2) * powChebQ_succ_succ (n + 1) (m + 1) + h1 + h2 +
        ((n : ℝ) + 1) * powChebQ_succ_succ n (m + 2) - ((n : ℝ) + 1) * powChebQ_succ_succ n m
theorem sum_powChebScaled_eq_two_pow : ∀ (n N : ℕ), n < N →
    ∑ d ∈ Finset.range N, powChebScaled n d = 2 ^ n
  | 0, 0, h => by omega
  | 0, m + 1, _ => by
      rw [Finset.sum_range_succ', powChebScaled,
        Finset.sum_eq_zero (fun _ _ ↦ rfl : ∀ k ∈ Finset.range m, powChebScaled 0 (k + 1) = 0)]
      rfl
  | _ + 1, 0, h => by omega
  | _ + 1, 1, h => by omega
  | n + 1, M + 2, h => by
      let c := powChebScaled n
      have hstep : ∑ d ∈ Finset.range (M + 2), powChebScaled (n + 1) d =
          (∑ d ∈ Finset.range (M + 1), c d) + (∑ d ∈ Finset.range (M + 3), c d) := by
        rw [Finset.sum_range_succ' _ (M + 1), Finset.sum_range_succ' _ M]
        simp only [powChebScaled, stepChebScaled, Finset.sum_add_distrib]
        rw [Finset.sum_range_succ' c M, Finset.sum_range_succ' c (M + 2),
          Finset.sum_range_succ' (fun k ↦ c (k + 1)) (M + 1),
          Finset.sum_range_succ' (fun k ↦ c (k + 2)) M]
        dsimp only [c]
        simp only [Nat.zero_add, Nat.add_assoc, show (1 : ℕ) + 2 = 3 from rfl]
        omega
      rw [hstep, sum_powChebScaled_eq_two_pow n (M + 1) (by omega),
        sum_powChebScaled_eq_two_pow n (M + 3) (by omega), Nat.pow_succ]
      omega
noncomputable def chebSingleTerm (β_nat scale0 n d : ℕ) : ℝ :=
  ((-1 : ℝ) ^ ((n - d) / 2)) * chebTermExact β_nat scale0 n d / (wMult d : ℝ)
noncomputable def chebSingleScaled (β_nat scale0 K d : ℕ) : ℝ :=
  (scale0 : ℝ) * chebTaylorWeight (β_nat : ℝ) K d / (wMult d : ℝ)
lemma chebSingleScaled_eq_sum (β_nat scale0 K d : ℕ) : chebSingleScaled β_nat scale0 K d =
      ∑ n ∈ Finset.range (K + 1), chebSingleTerm β_nat scale0 n d := by
  unfold chebSingleScaled chebTaylorWeight chebSingleTerm chebTermExact
  rw [Finset.mul_sum, Finset.sum_div]
  exact Finset.sum_congr rfl fun _ _ ↦ by ring
lemma chebSingleScaled_eq_zero_of_lt {β_nat scale0 K d : ℕ} (h : K < d) :
    chebSingleScaled β_nat scale0 K d = 0 := by
  rw [chebSingleScaled_eq_sum]
  exact Finset.sum_eq_zero fun n hn ↦ by
    have := Finset.mem_range.mp hn
    simp [chebSingleTerm, chebTermExact_eq_zero_of_lt (by omega : n < d)]
theorem chebSingleScaled_three_term_rec (β_nat scale0 K d : ℕ) :
    (β_nat : ℝ) * (chebSingleScaled β_nat scale0 K d + chebSingleScaled β_nat scale0 K (d + 2)) -
      2 * ((d + 1 : ℕ) : ℝ) * chebSingleScaled β_nat scale0 K (d + 1) = (β_nat : ℝ) *
        (chebSingleTerm β_nat scale0 K d + chebSingleTerm β_nat scale0 K (d + 2)) := by
  have hQ (m : ℕ) : ∀ j : ℕ, (powChebQ m j : ℝ) = 2 * ((powChebScaled m j : ℝ) / (wMult j : ℝ))
    | 0 => by simp [powChebQ, wMult]
    | _ + 1 => by
        simp only [powChebQ, wMult, Nat.succ_ne_zero, ↓reduceIte]
        ring
  have hstep (n : ℕ) : 2 * ((d + 1 : ℕ) : ℝ) * chebSingleTerm β_nat scale0 (n + 1) (d + 1) =
      (β_nat : ℝ) * (chebSingleTerm β_nat scale0 n d + chebSingleTerm β_nat scale0 n (d + 2)) := by
    have hrec := powChebQ_bessel_rec n d
    rw [hQ, hQ, hQ] at hrec
    have hsign : ((-1 : ℝ) ^ ((n - (d + 2)) / 2)) * (powChebScaled n (d + 2) : ℝ) =
        -((-1 : ℝ) ^ ((n - d) / 2)) * (powChebScaled n (d + 2) : ℝ) := by
      by_cases hlt : n < d + 2
      · simp [powChebScaled_eq_zero_of_lt hlt]
      · by_cases hodd : (n + (d + 2)) % 2 = 1
        · simp [powChebScaled_eq_zero_of_odd_add hodd]
        · rw [show (n - d) / 2 = (n - (d + 2)) / 2 + 1 by omega, pow_succ']
          ring
    have hn1 : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    let C := (scale0 : ℝ) * (n.factorial : ℝ)⁻¹ * (β_nat : ℝ) * (β_nat : ℝ) ^ n * ((2 : ℝ) ^ n)⁻¹
    unfold chebSingleTerm chebTermExact
    rw [show ((n + 1) - (d + 1)) / 2 = (n - d) / 2 from Nat.succ_sub_succ n d ▸ rfl,
      Nat.factorial_succ, Nat.cast_mul, mul_inv, pow_succ' (β_nat : ℝ) n,
      pow_succ' (2 : ℝ) n, mul_inv, show (2 : ℝ)⁻¹ = 1 / 2 by norm_num]
    linear_combination ((-1 : ℝ) ^ ((n - d) / 2) * C * ((n + 1 : ℕ) : ℝ)⁻¹ / 2) * hrec -
      (C / (wMult (d + 2) : ℝ)) * hsign +
      C * ((-1 : ℝ) ^ ((n - d) / 2) * (powChebScaled n d : ℝ) / (wMult d : ℝ) -
        (-1 : ℝ) ^ ((n - d) / 2) * (powChebScaled n (d + 2) : ℝ) / (wMult (d + 2) : ℝ)) *
        inv_mul_cancel₀ hn1
  have hY1 : 2 * ((d + 1 : ℕ) : ℝ) * chebSingleScaled β_nat scale0 K (d + 1) =
      (β_nat : ℝ) * ((∑ n ∈ Finset.range K, chebSingleTerm β_nat scale0 n d) +
        (∑ n ∈ Finset.range K, chebSingleTerm β_nat scale0 n (d + 2))) := by
    rw [chebSingleScaled_eq_sum, Finset.sum_range_succ',
      show chebSingleTerm β_nat scale0 0 (d + 1) = 0 by
        simp [chebSingleTerm, chebTermExact_eq_zero_of_lt (Nat.succ_pos d)],
      add_zero, Finset.mul_sum, ← Finset.sum_add_distrib, Finset.mul_sum]
    exact Finset.sum_congr rfl fun n _ ↦ hstep n
  rw [hY1, chebSingleScaled_eq_sum _ _ K d, Finset.sum_range_succ,
    chebSingleScaled_eq_sum _ _ K (d + 2), Finset.sum_range_succ]
  ring
theorem chebSingleScaled_even_sum_eq_scale0 (β_nat scale0 K : ℕ) :
    chebSingleScaled β_nat scale0 K 0 +
      ∑ m ∈ Finset.range (K / 2), 2 * chebSingleScaled β_nat scale0 K (2 * (m + 1)) =
      (scale0 : ℝ) := by
  have heven : ∑ m ∈ Finset.range (K / 2 + 1), chebTaylorWeight (β_nat : ℝ) K (2 * m) = 1 := by
    unfold chebTaylorWeight
    rw [Finset.sum_comm, Finset.sum_range_succ']
    have h0 : ∑ x ∈ Finset.range (K / 2 + 1), (-1 : ℝ) ^ ((0 - 2 * x) / 2) *
        ((Nat.factorial 0 : ℝ)⁻¹ * (β_nat : ℝ) ^ 0) *
        ((powChebScaled 0 (2 * x) : ℝ) * ((2 : ℝ) ^ 0)⁻¹) = 1 := by
      rw [Finset.sum_range_succ', Finset.sum_eq_zero fun k _ ↦ by
        simp [powChebScaled_eq_zero_of_lt (by omega : 0 < 2 * (k + 1))]]
      simp [powChebScaled]
    have hsucc : ∑ k ∈ Finset.range K, ∑ m ∈ Finset.range (K / 2 + 1),
        (-1 : ℝ) ^ (((k + 1) - 2 * m) / 2) * (((k + 1).factorial : ℝ)⁻¹ * (β_nat : ℝ) ^ (k + 1)) *
          ((powChebScaled (k + 1) (2 * m) : ℝ) * ((2 : ℝ) ^ (k + 1))⁻¹) = 0 := by
      refine Finset.sum_eq_zero fun k hk ↦ ?_
      rw [Finset.mem_range] at hk
      by_cases hodd : (k + 1) % 2 = 1
      · exact Finset.sum_eq_zero fun m _ ↦ by
          simp [powChebScaled_eq_zero_of_odd_add (by omega : ((k + 1) + 2 * m) % 2 = 1)]
      · let C_k := (-1 : ℝ) ^ ((k + 1) / 2) *
          (((k + 1).factorial : ℝ)⁻¹ * (β_nat : ℝ) ^ (k + 1) * ((2 : ℝ) ^ (k + 1))⁻¹)
        let h : ℕ → ℝ := fun
          | 0 => 0 | m + 1 => (-1 : ℝ) ^ m * (powChebScaled k (2 * m + 1) : ℝ)
        have hs : ∀ m,
            (-1 : ℝ) ^ m * (stepChebScaled (powChebScaled k) (2 * m) : ℝ) = h (m + 1) - h m
          | 0 => by simp [h, stepChebScaled]
          | j + 1 => by
            simp only [h, show 2 * (j + 1) = 2 * j + 2 by omega, stepChebScaled, pow_succ']
            push_cast
            ring
        have hterm (m : ℕ) : (-1 : ℝ) ^ (((k + 1) - 2 * m) / 2) *
            (((k + 1).factorial : ℝ)⁻¹ * (β_nat : ℝ) ^ (k + 1)) *
            ((powChebScaled (k + 1) (2 * m) : ℝ) * ((2 : ℝ) ^ (k + 1))⁻¹) =
            C_k * (h (m + 1) - h m) := by
          rw [← hs m]
          dsimp only [C_k]
          by_cases hlt : k + 1 < 2 * m
          · simp [powChebScaled_eq_zero_of_lt hlt,
              show stepChebScaled (powChebScaled k) (2 * m) = 0 from
                powChebScaled_eq_zero_of_lt hlt]
          · rw [show (-1 : ℝ) ^ (((k + 1) - 2 * m) / 2) =
              (-1 : ℝ) ^ ((k + 1) / 2) * (-1 : ℝ) ^ m by
              rw [← show ((k + 1) - 2 * m) / 2 + m = (k + 1) / 2 by omega, pow_add, mul_assoc,
                ← pow_add, ← two_mul, pow_mul]
              norm_num, powChebScaled]
            ring
        simp_rw [hterm]
        rw [← Finset.mul_sum, Finset.sum_range_sub h (K / 2 + 1)]
        simp [h, powChebScaled_eq_zero_of_lt (by omega : k < 2 * (K / 2) + 1)]
    linarith
  have hev := congrArg ((scale0 : ℝ) * ·) heven
  rw [mul_one, Finset.mul_sum, Finset.sum_range_succ'] at hev
  have hm (m : ℕ) : (scale0 : ℝ) * chebTaylorWeight (β_nat : ℝ) K (2 * (m + 1)) =
      2 * chebSingleScaled β_nat scale0 K (2 * (m + 1)) := by
    unfold chebSingleScaled wMult
    simp only [show 2 * (m + 1) ≠ 0 by omega, ↓reduceIte]
    ring
  simp_rw [Nat.mul_zero, show (scale0 : ℝ) * chebTaylorWeight (β_nat : ℝ) K 0 =
    chebSingleScaled β_nat scale0 K 0 by simp [chebSingleScaled, wMult], hm] at hev
  linarith
def omegaWronskian (β : ℝ) (w z : ℕ → ℝ) (k : ℕ) : ℝ := β * (w k * z (k + 1) - w (k + 1) * z k)
def threeTermRes (β : ℝ) (f : ℕ → ℝ) (d : ℕ) : ℝ :=
  β * (f d + f (d + 2)) - 2 * ((d + 1 : ℕ) : ℝ) * f (d + 1)
theorem cramer_elim_eq (β : ℝ) (u v z : ℕ → ℝ) (k : ℕ) :
    β * (u k * v (k + 1) - u (k + 1) * v k) * z k =
      v k * omegaWronskian β u z k - u k * omegaWronskian β v z k := by
  unfold omegaWronskian
  ring
theorem abelWronskian_bound_le_full_sum (β : ℝ) (w z : ℕ → ℝ) (N k : ℕ) (hk : k ≤ N) :
    |omegaWronskian β w z k| ≤ |omegaWronskian β w z N| + ∑ d ∈ Finset.range N,
      (|z (d + 1)| * |threeTermRes β w d| + |w (d + 1)| * |threeTermRes β z d|) := by
  let g := fun d ↦ |z (d + 1)| * |threeTermRes β w d| + |w (d + 1)| * |threeTermRes β z d|
  let A := fun n ↦ |omegaWronskian β w z n| + ∑ d ∈ Finset.range n, g d
  have hmono (m : ℕ) : A k ≤ A (k + m) := by
    induction m with
    | zero => exact le_rfl
    | succ m ih =>
      refine ih.trans ?_
      dsimp [A, g]
      rw [Nat.add_succ, Finset.sum_range_succ,
        show omegaWronskian β w z (k + m) = omegaWronskian β w z (k + m + 1) +
          (z (k + m + 1) * threeTermRes β w (k + m) - w (k + m + 1) * threeTermRes β z (k + m)) by
          unfold omegaWronskian threeTermRes
          ring]
      linarith [(abs_add_le (omegaWronskian β w z (k + m + 1))
          (z (k + m + 1) * threeTermRes β w (k + m) -
            w (k + m + 1) * threeTermRes β z (k + m))).trans
        (add_le_add le_rfl ((abs_sub _ _).trans_eq (by rw [abs_mul, abs_mul])))]
  have hAN := hmono (N - k)
  rw [show k + (N - k) = N by omega] at hAN
  exact (show |omegaWronskian β w z k| ≤ A k by
    dsimp [A, g]
    linarith [Finset.sum_nonneg fun d (_ : d ∈ Finset.range k) ↦
      (by positivity : 0 ≤ g d)]).trans hAN
theorem forbiddenZone_diagDom_sum_le (β : ℝ) (hβ0 : 0 ≤ β) (N L : ℕ) (hL : 0 < L)
    (hβN : β ≤ (N : ℝ)) (z : ℕ → ℝ) (hz_bot : z N = 0) (hz_top : z (N + 1 + L) = 0) :
    2 * (∑ j ∈ Finset.range L, |z (N + 1 + j)|) ≤
      ∑ j ∈ Finset.range L, |threeTermRes β z (N + j)| := by
  have hsum := Finset.sum_le_sum fun j (_ : j ∈ Finset.range L) ↦ (show
      (2 * (N + 1 : ℝ)) * |z (N + 1 + j)| ≤
        β * |z (N + j)| + β * |z (N + 2 + j)| + |threeTermRes β z (N + j)| by
    rw [show N + 1 + j = N + j + 1 by omega, show N + 2 + j = N + j + 2 by omega]
    refine (mul_le_mul_of_nonneg_right
      (by exact_mod_cast (show 2 * (N + 1) ≤ 2 * (N + j + 1) by omega) :
        2 * (N + 1 : ℝ) ≤ 2 * ((N + j + 1 : ℕ) : ℝ)) (abs_nonneg _)).trans ?_
    rw [← abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * ((N + j + 1 : ℕ) : ℝ)), ← abs_mul,
      show 2 * ((N + j + 1 : ℕ) : ℝ) * z (N + j + 1) =
        β * (z (N + j) + z (N + j + 2)) - threeTermRes β z (N + j) by
        unfold threeTermRes
        ring]
    refine (abs_sub _ _).trans (add_le_add ?_ le_rfl)
    rw [abs_mul, abs_of_nonneg hβ0, ← mul_add]
    exact mul_le_mul_of_nonneg_left (abs_add_le _ _) hβ0)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  rcases Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hL) with ⟨L', rfl⟩
  have hs_l : ∑ j ∈ Finset.range (L' + 1), |z (N + j)| ≤
      ∑ j ∈ Finset.range (L' + 1), |z (N + 1 + j)| := by
    rw [Finset.sum_range_succ', Nat.add_zero, hz_bot, abs_zero, add_zero,
      Finset.sum_range_succ _ L',
      Finset.sum_congr rfl fun j _ ↦ congrArg (|z ·|) (show N + (j + 1) = N + 1 + j by omega)]
    linarith [abs_nonneg (z (N + 1 + L'))]
  have hs_r : ∑ j ∈ Finset.range (L' + 1), |z (N + 2 + j)| ≤
      ∑ j ∈ Finset.range (L' + 1), |z (N + 1 + j)| := by
    rw [Finset.sum_range_succ, show N + 2 + L' = N + 1 + (L' + 1) by omega, hz_top, abs_zero,
      add_zero, Finset.sum_range_succ' _ L', Finset.sum_congr rfl fun j _ ↦
        congrArg (|z ·|) (show N + 2 + j = N + 1 + (j + 1) by omega)]
    linarith [abs_nonneg (z (N + 1 + 0))]
  nlinarith [Finset.sum_nonneg fun j (_ : j ∈ Finset.range (L' + 1)) ↦ abs_nonneg (z (N + 1 + j))]
@[simp] lemma getD_cons_zero_nat (x dflt : ℕ) (xs : List ℕ) : (x :: xs).getD 0 dflt = x := by
  simp [List.getD_eq_getElem?_getD]
@[simp] lemma getD_cons_succ_nat (x dflt : ℕ) (xs : List ℕ) (k : ℕ) :
    (x :: xs).getD (k + 1) dflt = xs.getD k dflt := by
  simp [List.getD_eq_getElem?_getD]
lemma getD_drop_nat (dflt : ℕ) : ∀ (a : ℕ) (xs : List ℕ) (k : ℕ),
    (xs.drop a).getD k dflt = xs.getD (a + k) dflt
  | 0, _, _ => by simp
  | _ + 1, [], _ => by simp [List.getD_eq_getElem?_getD]
  | a + 1, _ :: xt, k => by
      rw [List.drop_succ_cons, getD_drop_nat dflt a xt k,
          show a + 1 + k = (a + k) + 1 by omega, getD_cons_succ_nat]
def wsMaxMagLoop (Bw : ℕ) : List ℕ → ℕ → ℕ
  | [], acc => acc
  | w :: wt, acc => forceNatFast (Nat.max acc (natAbsDiff w Bw)) fun acc' ↦ wsMaxMagLoop Bw wt acc'
lemma wsMaxMagLoop_real_le (Bw : ℕ) (ws : List ℕ) (d : ℕ) :
    |(ws.getD d Bw : ℝ) - (Bw : ℝ)| ≤ (wsMaxMagLoop Bw ws 0 : ℝ) := by
  have hmono (xs : List ℕ) : ∀ acc : ℕ, acc ≤ wsMaxMagLoop Bw xs acc := by
    induction xs with
    | nil => exact fun _ ↦ le_rfl
    | cons _ wt ih =>
      exact fun acc ↦ (Nat.le_max_left _ _).trans
        (by simpa only [wsMaxMagLoop, forceNatFast_eq] using ih _)
  have hget (xs : List ℕ) : ∀ acc k : ℕ,
      natAbsDiff (xs.getD k Bw) Bw ≤ wsMaxMagLoop Bw xs acc := by
    induction xs with
    | nil =>
      exact fun _ _ ↦ by simp [List.getD_eq_getElem?_getD, natAbsDiff, Nat.ble_eq.mpr le_rfl]
    | cons _ wt ih =>
      rintro acc (_ | k)
      · simp only [wsMaxMagLoop, forceNatFast_eq, getD_cons_zero_nat]
        exact (Nat.le_max_right _ _).trans (hmono wt _)
      · simp only [wsMaxMagLoop, forceNatFast_eq, getD_cons_succ_nat]
        exact ih _ k
  rw [← natAbsDiff_cast_real]
  exact_mod_cast hget ws 0 d
def millerResCountLoop (β_nat Bw j_top1 : ℕ) : ℕ → ℕ → List ℕ → ℕ → ℕ
  | 0, _, _, acc => acc
  | _ + 1, _, [], acc => acc
  | m + 1, d, j_prev :: rest, acc =>
      forceNatFast (Nat.add acc (millerStepResidualNat β_nat Bw d j_prev
        (rest.getD 0 j_top1) (rest.getD 1 j_top1)))
        fun acc' ↦ millerResCountLoop β_nat Bw j_top1 m (Nat.add d 1) rest acc'
lemma millerResCountLoop_real_eq_sum (β_nat Bw m d0 : ℕ) (js : List ℕ) (R : ℕ)
    (hm : m ≤ (js.drop d0).length)
    (hloop : millerResCountLoop β_nat Bw Bw m (d0 + 1) (js.drop d0) 0 = R) : ∑ k ∈ Finset.range m,
      |threeTermRes (β_nat : ℝ) (fun d ↦ (js.getD d Bw : ℝ) - (Bw : ℝ)) (d0 + k)| =
      (R : ℝ) := by
  have heq (n : ℕ) : ∀ (d : ℕ) (xs : List ℕ) (acc : ℕ), n ≤ xs.length →
      millerResCountLoop β_nat Bw Bw n d xs acc = acc + ∑ k ∈ Finset.range n,
        millerStepResidualNat β_nat Bw (d + k)
          (xs.getD k Bw) (xs.getD (k + 1) Bw) (xs.getD (k + 2) Bw) := by
    induction n with
    | zero => exact fun _ _ _ _ ↦ by simp [millerResCountLoop]
    | succ n ih =>
      rintro d (_ | ⟨j_prev, rest⟩) acc hn
      · simp at hn
      · simp only [millerResCountLoop, forceNatFast_eq, Nat.add_eq]
        rw [ih (d + 1) rest _ (by simpa using hn)]
        have hsum : ∑ k ∈ Finset.range n, millerStepResidualNat β_nat Bw (d + 1 + k)
            (rest.getD k Bw) (rest.getD (k + 1) Bw) (rest.getD (k + 2) Bw) =
            ∑ k ∈ Finset.range n, millerStepResidualNat β_nat Bw (d + (k + 1))
              ((j_prev :: rest).getD (k + 1) Bw) ((j_prev :: rest).getD (k + 1 + 1) Bw)
              ((j_prev :: rest).getD (k + 1 + 2) Bw) :=
          Finset.sum_congr rfl fun k _ ↦ by
            simp only [getD_cons_succ_nat, show d + (k + 1) = d + 1 + k by omega]
        rw [hsum, Finset.sum_range_succ' (fun k ↦ millerStepResidualNat β_nat Bw (d + k)
          ((j_prev :: rest).getD k Bw) ((j_prev :: rest).getD (k + 1) Bw)
          ((j_prev :: rest).getD (k + 2) Bw)) n,
          getD_cons_zero_nat, getD_cons_succ_nat, getD_cons_succ_nat, Nat.add_zero]
        omega
  rw [heq m (d0 + 1) (js.drop d0) 0 hm, zero_add] at hloop
  rw [← (by exact_mod_cast hloop : (∑ k ∈ Finset.range m, (millerStepResidualNat β_nat Bw
    (d0 + 1 + k) ((js.drop d0).getD k Bw) ((js.drop d0).getD (k + 1) Bw)
    ((js.drop d0).getD (k + 2) Bw) : ℝ)) = (R : ℝ))]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [getD_drop_nat, getD_drop_nat, getD_drop_nat,
    show d0 + (k + 1) = d0 + k + 1 by omega, show d0 + (k + 2) = d0 + k + 2 by omega]
  unfold millerStepResidualNat threeTermRes
  dsimp only
  rw [natAbs_cast_real, show d0 + k + 1 = d0 + 1 + k by omega]
  push_cast
  ring_nf
def wronskianStepNat (Bw u0 u1 v0 v1 : ℕ) : ℕ :=
  Int.natAbs (((u0 : ℤ) - (Bw : ℤ)) * ((v1 : ℤ) - (Bw : ℤ)) -
    ((u1 : ℤ) - (Bw : ℤ)) * ((v0 : ℤ) - (Bw : ℤ)))
def wronskianMinCheckBle (Bw W_min : ℕ) : List ℕ → List ℕ → ℕ → Bool
  | _, _, 0 => true
  | u0 :: u1 :: ur, v0 :: v1 :: vr, m + 1 =>
      match Nat.ble W_min (wronskianStepNat Bw u0 u1 v0 v1) with
      | false => false
      | true => wronskianMinCheckBle Bw W_min (u1 :: ur) (v1 :: vr) m
  | _, _, _ + 1 => false
lemma wronskianMinCheckBle_spec (Bw W_min : ℕ) :
    ∀ (m : ℕ) (us vs : List ℕ), wronskianMinCheckBle Bw W_min us vs m = true →
      ∀ k < m, W_min ≤ wronskianStepNat Bw (us.getD k Bw) (us.getD (k + 1) Bw)
        (vs.getD k Bw) (vs.getD (k + 1) Bw)
  | 0, _, _, _, _, hk => by omega
  | _ + 1, [], _, h, _, _ => by simp [wronskianMinCheckBle] at h
  | _ + 1, [_], _, h, _, _ => by simp [wronskianMinCheckBle] at h
  | _ + 1, _ :: _ :: _, [], h, _, _ => by simp [wronskianMinCheckBle] at h
  | _ + 1, _ :: _ :: _, [_], h, _, _ => by simp [wronskianMinCheckBle] at h
  | m + 1, u0 :: u1 :: ur, v0 :: v1 :: vr, h, k, hk => by
      unfold wronskianMinCheckBle at h
      rcases hble : Nat.ble W_min (wronskianStepNat Bw u0 u1 v0 v1) with _ | _
      · rw [hble] at h
        cases h
      · rw [hble] at h
        rcases k with _ | j
        · exact Nat.ble_eq.mp hble
        · simpa [getD_cons_succ_nat] using
            wronskianMinCheckBle_spec Bw W_min m (u1 :: ur) (v1 :: vr) h j (by omega)
lemma wronskianStepNat_real_eq (Bw u0 u1 v0 v1 : ℕ) : (wronskianStepNat Bw u0 u1 v0 v1 : ℝ) =
      |((u0 : ℝ) - (Bw : ℝ)) * ((v1 : ℝ) - (Bw : ℝ)) -
        ((u1 : ℝ) - (Bw : ℝ)) * ((v0 : ℝ) - (Bw : ℝ))| := by
  unfold wronskianStepNat
  rw [natAbs_cast_real]
  push_cast
  ring_nf
def evenTailBiasedLoop (Bw : ℕ) : List ℕ → ℤ → ℤ
  | [], acc => acc
  | [_], acc => acc
  | _ :: u_even :: rest, acc => evenTailBiasedLoop Bw rest (acc + 2 * ((u_even : ℤ) - (Bw : ℤ)))
lemma evenTailBiasedLoop_real_eq_sum (Bw m : ℕ) (us : List ℕ) (S : ℤ)
    (hlen : (us.drop 1).length = 2 * m)
    (hloop : ((us.getD 0 Bw : ℤ) - (Bw : ℤ)) + evenTailBiasedLoop Bw (us.drop 1) 0 = S) :
    ((us.getD 0 Bw : ℝ) - (Bw : ℝ)) +
      ∑ j ∈ Finset.range m, 2 * ((us.getD (2 * (j + 1)) Bw : ℝ) - (Bw : ℝ)) = (S : ℝ) := by
  have heq (n : ℕ) : ∀ (xs : List ℕ) (acc : ℤ), xs.length = 2 * n → evenTailBiasedLoop Bw xs acc =
        acc + ∑ j ∈ Finset.range n, 2 * (((xs.getD (2 * j + 1) Bw : ℕ) : ℤ) - (Bw : ℤ)) := by
    induction n with
    | zero =>
      rintro (_ | _) acc h
      · simp [evenTailBiasedLoop]
      · simp at h
    | succ n ih =>
      rintro (_ | ⟨u_odd, _ | ⟨u_even, rest⟩⟩) acc h
      · simp at h
      · simp only [List.length_singleton] at h
        omega
      · simp only [evenTailBiasedLoop]
        rw [ih rest _ (by simpa [Nat.mul_succ] using h), Finset.sum_range_succ',
          getD_cons_succ_nat, getD_cons_zero_nat,
          Finset.sum_congr rfl fun j _ ↦ (by
            simp only [show 2 * (j + 1) + 1 = (2 * j + 1) + 1 + 1 by omega,
              getD_cons_succ_nat] :
              2 * (((rest.getD (2 * j + 1) Bw : ℕ) : ℤ) - (Bw : ℤ)) =
                2 * ((((u_odd :: u_even :: rest).getD (2 * (j + 1) + 1) Bw : ℕ) : ℤ) - (Bw : ℤ)))]
        ring
  rw [heq m (us.drop 1) 0 hlen, zero_add] at hloop
  rw [← (by exact_mod_cast hloop : (((us.getD 0 Bw : ℤ) - (Bw : ℤ)) + ∑ j ∈ Finset.range m,
      2 * ((((us.drop 1).getD (2 * j + 1) Bw : ℕ) : ℤ) - (Bw : ℤ)) : ℝ) = (S : ℝ))]
  push_cast
  exact congrArg (_ + ·) (Finset.sum_congr rfl fun j _ ↦ by
    rw [getD_drop_nat, show 1 + (2 * j + 1) = 2 * (j + 1) by omega])
def doubleBiasedTail (Bw : ℕ) : List ℕ → List ℕ
  | [] => []
  | u :: ut => forceNatFast (Nat.sub (Nat.mul 2 u) Bw) fun w ↦ w :: doubleBiasedTail Bw ut
def doubleBiasedAllGeBle (Bw : ℕ) : List ℕ → Bool
  | [] => true
  | u :: ut => match Nat.ble Bw (Nat.mul 2 u) with
      | false => false | true => doubleBiasedAllGeBle Bw ut
def buildChebWsFromBiasedU (Bw pad : ℕ) : List ℕ → List ℕ
  | [] => List.replicate (pad + 1) Bw
  | u0 :: ut => u0 :: (doubleBiasedTail Bw ut ++ List.replicate pad Bw)
lemma buildChebWsFromBiasedU_getD_real (Bw pad : ℕ) (us : List ℕ)
    (hne : 0 < us.length) (hge : doubleBiasedAllGeBle Bw (us.drop 1) = true) (d : ℕ) :
    ((buildChebWsFromBiasedU Bw pad us).getD d Bw : ℝ) - (Bw : ℝ) =
      (wMult d : ℝ) * ((us.getD d Bw : ℝ) - (Bw : ℝ)) := by
  have htail (xs : List ℕ) : ∀ k : ℕ, doubleBiasedAllGeBle Bw xs = true →
      ((doubleBiasedTail Bw xs ++ List.replicate pad Bw).getD k Bw : ℝ) - (Bw : ℝ) =
        2 * ((xs.getD k Bw : ℝ) - (Bw : ℝ)) := by
    induction xs with
    | nil =>
      intro k _
      simp only [doubleBiasedTail, List.nil_append, List.getD_eq_getElem?_getD,
        List.getElem?_replicate]
      split
      · simp
      · simp
    | cons u ut ih =>
      intro k h
      unfold doubleBiasedAllGeBle at h
      rcases hble : Nat.ble Bw (Nat.mul 2 u) with _ | _
      · rw [hble] at h
        cases h
      · rw [hble] at h
        rcases k with _ | j
        · have hle : Bw ≤ 2 * u := Nat.ble_eq.mp hble
          simp only [doubleBiasedTail, forceNatFast_eq, List.cons_append, getD_cons_zero_nat,
            Nat.sub_eq, Nat.mul_eq, Nat.cast_sub hle, Nat.cast_mul, Nat.cast_ofNat]
          ring
        · simp only [doubleBiasedTail, forceNatFast_eq, List.cons_append, getD_cons_succ_nat]
          exact ih j h
  rcases us with _ | ⟨u0, ut⟩
  · simp at hne
  · rcases d with _ | k
    · simp [buildChebWsFromBiasedU, wMult]
    · simp only [buildChebWsFromBiasedU, getD_cons_succ_nat, wMult, show k + 1 ≠ 0 by omega,
        ↓reduceIte, Nat.cast_ofNat]
      exact htail ut k (by simpa using hge)
lemma sum_odd_le_sum_two_mul (f : ℕ → ℝ) (hf : ∀ k, 0 ≤ f k) :
    ∀ N : ℕ, ∑ j ∈ Finset.range N, f (2 * j + 1) ≤ ∑ k ∈ Finset.range (2 * N), f k
  | 0 => by simp
  | N + 1 => by
      rw [Finset.sum_range_succ, show 2 * (N + 1) = 2 * N + 1 + 1 by omega,
        Finset.sum_range_succ _ (2 * N + 1), Finset.sum_range_succ _ (2 * N)]
      linarith [sum_odd_le_sum_two_mul f hf N, hf (2 * N)]
lemma threeTermRes_chebSingleScaled_sum_le_of_fact_bound (β_nat scale0 K B_exp a M : ℕ)
    (hble : scale0 * β_nat ^ K ≤ 2 ^ B_exp * K.factorial) : ∑ k ∈ Finset.range M,
      |threeTermRes (β_nat : ℝ) (chebSingleScaled β_nat scale0 K) (a + k)| ≤
      2 * (β_nat : ℝ) * ((2 ^ B_exp : ℕ) : ℝ) := by
  have hshift (b : ℕ) : ∀ (f : ℕ → ℝ), (∀ k, 0 ≤ f k) →
      ∑ k ∈ Finset.range M, f (b + k) ≤ ∑ d ∈ Finset.range (b + M), f d := by
    induction b with
    | zero =>
      intro _ _
      simp
    | succ b ih =>
      intro f hf
      rw [Nat.succ_add, Finset.sum_range_succ', Finset.sum_congr rfl fun k _ ↦
        congrArg f (Nat.add_right_comm b 1 k)]
      linarith [ih (fun d ↦ f (d + 1)) (fun k ↦ hf (k + 1)), hf 0]
  have hcsum (b : ℕ) : ∑ k ∈ Finset.range M, |chebSingleTerm β_nat scale0 K (b + k)| ≤
      ((2 ^ B_exp : ℕ) : ℝ) := by
    have hpow_le : ∑ k ∈ Finset.range M, (powChebScaled K (b + k) : ℝ) ≤ (2 : ℝ) ^ K :=
      (hshift b (fun d ↦ (powChebScaled K d : ℝ)) fun _ ↦ by positivity).trans
        ((Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono
          (show b + M ≤ b + M + K + 1 by omega)) fun _ _ _ ↦ by positivity).trans_eq
          (by exact_mod_cast sum_powChebScaled_eq_two_pow K (b + M + K + 1) (by omega)))
    have hfact_pos : (0 : ℝ) < (K.factorial : ℝ) := by positivity
    calc ∑ k ∈ Finset.range M, |chebSingleTerm β_nat scale0 K (b + k)|
      _ ≤ ((scale0 : ℝ) * (K.factorial : ℝ)⁻¹ * (β_nat : ℝ) ^ K * ((2 : ℝ) ^ K)⁻¹) *
            ((2 : ℝ) ^ K) := by
          refine (Finset.sum_le_sum fun k _ ↦ ?_).trans (by
            rw [← Finset.mul_sum]
            exact mul_le_mul_of_nonneg_left hpow_le (by positivity))
          unfold chebSingleTerm chebTermExact
          rw [abs_div, abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
            abs_of_nonneg (by positivity), abs_of_nonneg (by positivity),
            abs_of_nonneg (by positivity)]
          exact (div_le_self (by positivity)
            (by exact_mod_cast (wMult_pos _).1)).trans_eq (by ring)
      _ = ((scale0 : ℝ) * (β_nat : ℝ) ^ K) / (K.factorial : ℝ) := by
          field_simp [ne_of_gt hfact_pos, (by positivity : ((2 : ℝ) ^ K) ≠ 0)]
      _ ≤ ((2 ^ B_exp : ℕ) : ℝ) := (div_le_iff₀ hfact_pos).mpr (by exact_mod_cast hble)
  have h2 := hcsum (a + 2)
  rw [← Finset.sum_congr rfl fun k _ ↦
    congrArg (|chebSingleTerm β_nat scale0 K ·|) (show a + k + 2 = (a + 2) + k by omega)] at h2
  have hterm (k : ℕ) :
      |threeTermRes (β_nat : ℝ) (chebSingleScaled β_nat scale0 K) (a + k)| ≤
        (β_nat : ℝ) * (|chebSingleTerm β_nat scale0 K (a + k)| +
          |chebSingleTerm β_nat scale0 K (a + k + 2)|) := by
    unfold threeTermRes
    rw [chebSingleScaled_three_term_rec β_nat scale0 K (a + k), abs_mul,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ (β_nat : ℝ))]
    exact mul_le_mul_of_nonneg_left (abs_add_le _ _) (by positivity)
  have hsum_le := Finset.sum_le_sum fun k (_ : k ∈ Finset.range M) ↦ hterm k
  rw [← Finset.mul_sum, Finset.sum_add_distrib] at hsum_le
  nlinarith [(by positivity : (0 : ℝ) ≤ (β_nat : ℝ)), hcsum a, h2]
end ConfigBiGqspChebWeightCertS4805
end SpecMirror.BiGqspChebWeightCertS4805
end BiGqspChebWeightCertS4805
section BiGqspChunkedMillerLinearRecPQ2a
namespace Slim
namespace BiGqspChunkedMillerLinearRecPQ2a
section ConfigBiGqspChunkedMillerLinearRecPQ2a
set_option maxRecDepth 200000
open Real Operator Matrix Circuit SpecsAux.SpecMirror BridgeDuhamel GridStatesGuard SubmatrixOpNorm
open PhaseGradCatalystCore TFreeLaurentGQSP CatalyzedLaurentGQSP PhaseGradSignalRot
open BidirectionalCatalyzedGQSP FullScaleBESector _root_.DynamicCircuit DynCircuitExt SpecsAux
open TFreeLaurentGQSPPresets
open TFreeLaurentGQSPPresets.FastRecurrenceVerifier
open TFreeLaurentGQSPPresets.FastIntervalRecurrenceVerifier
open CatalyzedLaurentGQSPBridge
open BidirectionalCatalyzedGQSPBridge
open BidirectionalIntervalRecurrenceVerifier
open SpecsAux.SpecMirror.BiGqspChunkedMillerCore
open scoped Matrix Matrix.Norms.L2Operator
def splitPQRevLinear (B : ℕ) : ℕ → List PQPair → List ℕ → List ℕ × ℕ × List PQPair
  | 0, [], neg_acc => (neg_acc, B, [])
  | 0, x :: xs, neg_acc => (neg_acc, x.p, xs)
  | m + 1, [], neg_acc => splitPQRevLinear B m [] (B :: neg_acc)
  | m + 1, x :: xs, neg_acc => splitPQRevLinear B m xs (x.p :: neg_acc)
theorem splitPQRevLinear_pos_getD (B : ℕ) :
    ∀ (m : ℕ) (pq : List PQPair) (neg_acc : List ℕ) (i : ℕ),
      ((splitPQRevLinear B m pq neg_acc).2.2.getD i ⟨B, B⟩).p = (pq.getD (m + 1 + i) ⟨B, B⟩).p
  | 0, [], _, _ => by simp [splitPQRevLinear, List.getD_eq_getElem?_getD]
  | 0, _ :: _, _, i => by
      simp [splitPQRevLinear, List.getD_eq_getElem?_getD, show 0 + 1 + i = i + 1 by omega]
  | m + 1, [], na, i => by
      rw [splitPQRevLinear, splitPQRevLinear_pos_getD B m [] (B :: na) i]
      simp [List.getD_eq_getElem?_getD]
  | m + 1, x :: xs, na, i => by
      rw [splitPQRevLinear, splitPQRevLinear_pos_getD B m xs (x.p :: na) i]
      simp [List.getD_eq_getElem?_getD, show (m + 1) + 1 + i = (m + 1 + i) + 1 by omega]
theorem splitPQRevLinear_neg_getD (B : ℕ) :
    ∀ (m : ℕ) (pq : List PQPair) (neg_acc : List ℕ) (i : ℕ),
      (splitPQRevLinear B m pq neg_acc).1.getD i B =
        if i < m then (pq.getD (m - 1 - i) ⟨B, B⟩).p else neg_acc.getD (i - m) B
  | 0, [], _, _ => by simp [splitPQRevLinear]
  | 0, _ :: _, _, _ => by simp [splitPQRevLinear]
  | m + 1, [], na, i => by
      rw [splitPQRevLinear, splitPQRevLinear_neg_getD B m [] (B :: na) i]
      rcases lt_trichotomy i m with hi | rfl | hi
      · simp [hi, show i < m + 1 by omega, List.getD_eq_getElem?_getD]
      · simp [List.getD_eq_getElem?_getD]
      · simp [show ¬ i < m by omega, show ¬ i < m + 1 by omega,
          show i - m = (i - (m + 1)) + 1 by omega, List.getD_eq_getElem?_getD]
  | m + 1, x :: xs, na, i => by
      rw [splitPQRevLinear, splitPQRevLinear_neg_getD B m xs (x.p :: na) i]
      rcases lt_trichotomy i m with hi | rfl | hi
      · simp only [hi, show i < m + 1 by omega, ↓reduceIte,
          show m + 1 - 1 - i = (m - 1 - i) + 1 by omega, List.getD_eq_getElem?_getD,
          List.getElem?_cons_succ]
      · simp [List.getD_eq_getElem?_getD]
      · simp [show ¬ i < m by omega, show ¬ i < m + 1 by omega,
          show i - m = (i - (m + 1)) + 1 by omega, List.getD_eq_getElem?_getD]
def chebL1SumPosLinear (M1 B B2 Bw R_final W_err_dpos : ℕ) :
    ℕ → List ℕ → List PQPair → List ℕ → ℕ → ℕ
  | _, _, _, [], acc => acc
  | d, neg_cur, pos_cur, w :: wt, acc =>
      forceNatFast (Nat.add acc (if Nat.ble d M1 then
        Nat.add (natAbsDiff (Nat.add (Nat.add (uParityFlip d B2 (pos_cur.getD 0 ⟨B, B⟩).p)
          (neg_cur.getD 0 B)) Bw) (Nat.add w B2)) (Nat.add (Nat.mul 2 R_final) W_err_dpos)
        else Nat.add (natAbsDiff w Bw) W_err_dpos)) fun acc' ↦
          chebL1SumPosLinear M1 B B2 Bw R_final W_err_dpos
            (Nat.add d 1) neg_cur.tail pos_cur.tail wt acc'
def chebL1SumLinear (M1 B B2 Bw R_final W_err_d0 W_err_dpos : ℕ)
    (neg_rev : List ℕ) (p_center : ℕ) (pos_tail : List PQPair) : List ℕ → ℕ
  | [] => 0
  | w0 :: wt =>
      forceNatFast (Nat.add (natAbsDiff (Nat.add p_center Bw) (Nat.add w0 B))
        (Nat.add R_final W_err_d0)) fun acc1 ↦
        chebL1SumPosLinear M1 B B2 Bw R_final W_err_dpos 1 neg_rev pos_tail wt acc1
theorem chebL1SumLinear_eq_chebL1SumBiased (M1 B B2 Bw R_final W_err_d0 W_err_dpos : ℕ)
    (pq : List PQPair) (ws : List ℕ) : let sp := splitPQRevLinear B M1 pq []
    chebL1SumLinear M1 B B2 Bw R_final W_err_d0 W_err_dpos sp.1 sp.2.1 sp.2.2 ws =
      chebL1SumBiased M1 B B2 Bw R_final W_err_d0 W_err_dpos pq 0 ws 0 := by
  have hpos_eq (xs : List ℕ) : ∀ (d : ℕ) (nc : List ℕ) (pc : List PQPair) (acc : ℕ), 1 ≤ d →
        (∀ j, d + j ≤ M1 → nc.getD j B = (pq.getD (M1 - d - j) ⟨B, B⟩).p) →
        (∀ j, (pc.getD j ⟨B, B⟩).p = (pq.getD (M1 + d + j) ⟨B, B⟩).p) →
        chebL1SumPosLinear M1 B B2 Bw R_final W_err_dpos d nc pc xs acc =
          chebL1SumBiased M1 B B2 Bw R_final W_err_d0 W_err_dpos pq d xs acc := by
    induction xs with
    | nil => exact fun _ _ _ _ _ _ _ ↦ rfl
    | cons _ wt ih =>
      intro d nc pc acc hd hneg hpos
      have hbeq0 : Nat.beq d 0 = false :=
        Bool.eq_false_iff.mpr fun ht ↦ (by omega : d ≠ 0) (Nat.beq_eq.mp ht)
      have htn (j : ℕ) (hj : d + 1 + j ≤ M1) : nc.tail.getD j B =
          (pq.getD (M1 - (d + 1) - j) ⟨B, B⟩).p := by
        simpa [List.getD_eq_getElem?_getD, show M1 - d - (j + 1) = M1 - (d + 1) - j by omega]
          using hneg (j + 1) (by omega)
      have htp (j : ℕ) : (pc.tail.getD j ⟨B, B⟩).p = (pq.getD (M1 + (d + 1) + j) ⟨B, B⟩).p := by
        simpa [List.getD_eq_getElem?_getD, show M1 + d + (j + 1) = M1 + (d + 1) + j by omega]
          using hpos (j + 1)
      unfold chebL1SumPosLinear chebL1SumBiased
      simp only [hbeq0, Bool.false_eq_true, ↓reduceIte, forceNatFast_eq,
        Nat.add_eq, Nat.mul_eq, Nat.sub_eq]
      rcases hble : Nat.ble d M1 with _ | _
      · rw [ite_eq_right Bool.false_ne_true, ite_eq_right Bool.false_ne_true]
        exact ih (d + 1) _ _ _ (by omega) htn htp
      · rw [ite_eq_left rfl, ite_eq_left rfl,
          show (pc.getD 0 ⟨B, B⟩).p = (pq.getD (M1 + d) ⟨B, B⟩).p by simpa using hpos 0,
          show nc.getD 0 B = (pq.getD (M1 - d) ⟨B, B⟩).p by
            simpa using hneg 0 (Nat.ble_eq.mp hble)]
        exact ih (d + 1) _ _ _ (by omega) htn htp
  have hctr (m : ℕ) : ∀ (xs : List PQPair) (na : List ℕ),
      (splitPQRevLinear B m xs na).2.1 = (xs.getD m ⟨B, B⟩).p := by
    induction m with
    | zero =>
      rintro (_ | _) _
      · simp [splitPQRevLinear, List.getD_eq_getElem?_getD]
      · simp [splitPQRevLinear, List.getD_eq_getElem?_getD]
    | succ m ih =>
      rintro (_ | ⟨x, xt⟩) na
      · simp [splitPQRevLinear, ih [] (B :: na), List.getD_eq_getElem?_getD]
      · simp [splitPQRevLinear, ih xt (x.p :: na), List.getD_eq_getElem?_getD]
  intro sp
  rcases ws with _ | ⟨w0, wt⟩
  · rfl
  · unfold chebL1SumLinear chebL1SumBiased
    simp only [show Nat.beq 0 0 = true from rfl, ↓reduceIte, forceNatFast_eq, Nat.add_eq,
      zero_add, show sp.2.1 = (pq.getD M1 ⟨B, B⟩).p from hctr M1 pq []]
    refine hpos_eq wt 1 sp.1 sp.2.2 _ le_rfl (fun j hj ↦ ?_)
      (fun j ↦ splitPQRevLinear_pos_getD B M1 pq [] j)
    rw [splitPQRevLinear_neg_getD B M1 pq [] j, ite_eq_left (by omega)]
def asymDefectSumLinearLoop (B B2 R_final : ℕ) : ℕ → ℕ → List ℕ → List PQPair → ℕ → ℕ
  | 0, _, _, _, acc => acc
  | k + 1, d, neg_cur, pos_cur, acc =>
      forceNatFast (Nat.add acc (Nat.add (natAbsDiff
        (uParityFlip d B2 (pos_cur.getD 0 ⟨B, B⟩).p) (neg_cur.getD 0 B))
        (Nat.mul 2 R_final))) fun acc' ↦
        asymDefectSumLinearLoop B B2 R_final k (Nat.add d 1) neg_cur.tail pos_cur.tail acc'
def asymDefectSumLinear (M1 B B2 R_final : ℕ) (neg_rev : List ℕ) (pos_tail : List PQPair) : ℕ :=
  asymDefectSumLinearLoop B B2 R_final M1 1 neg_rev pos_tail 0
theorem asymDefectSumLinear_eq_asymDefectSumBiased (M1 B B2 R_final : ℕ) (pq : List PQPair) :
    let sp := splitPQRevLinear B M1 pq []
    asymDefectSumLinear M1 B B2 R_final sp.1 sp.2.2 =
      asymDefectSumBiased M1 B B2 R_final pq M1 0 := by
  let termAt (d : ℕ) : ℕ :=
    natAbsDiff (uParityFlip d B2 (pq.getD (M1 + d) ⟨B, B⟩).p) (pq.getD (M1 - d) ⟨B, B⟩).p +
      2 * R_final
  have hbiased (m : ℕ) : ∀ acc : ℕ, asymDefectSumBiased M1 B B2 R_final pq m acc =
      acc + ∑ j ∈ Finset.range m, termAt (j + 1) := by
    induction m with
    | zero => exact fun _ ↦ by simp [asymDefectSumBiased]
    | succ j ih =>
      exact fun acc ↦ by
        simp only [asymDefectSumBiased, forceNatFast_eq, Nat.add_eq, Nat.mul_eq, Nat.sub_eq, ih,
          Finset.sum_range_succ, termAt]
        omega
  have hloop (k : ℕ) : ∀ (d : ℕ) (nc : List ℕ) (pc : List PQPair) (acc : ℕ), d + k ≤ M1 + 1 →
      (∀ j, d + j ≤ M1 → nc.getD j B = (pq.getD (M1 - d - j) ⟨B, B⟩).p) →
      (∀ j, (pc.getD j ⟨B, B⟩).p = (pq.getD (M1 + d + j) ⟨B, B⟩).p) →
      asymDefectSumLinearLoop B B2 R_final k d nc pc acc =
        acc + ∑ i ∈ Finset.range k, termAt (d + i) := by
    induction k with
    | zero => exact fun _ _ _ _ _ _ _ ↦ by simp [asymDefectSumLinearLoop]
    | succ k ih =>
      intro d nc pc acc hdk hneg hpos
      unfold asymDefectSumLinearLoop
      simp only [forceNatFast_eq, Nat.add_eq, Nat.mul_eq,
        show (pc.getD 0 ⟨B, B⟩).p = (pq.getD (M1 + d) ⟨B, B⟩).p by simpa using hpos 0,
        show nc.getD 0 B = (pq.getD (M1 - d) ⟨B, B⟩).p by simpa using hneg 0 (by omega)]
      rw [ih (d + 1) nc.tail pc.tail _ (by omega)
        (fun j hj ↦ by
          simpa [List.getD_eq_getElem?_getD,
            show M1 - d - (j + 1) = M1 - (d + 1) - j by omega] using hneg (j + 1) (by omega))
        (fun j ↦ by
          simpa [List.getD_eq_getElem?_getD,
            show M1 + d + (j + 1) = M1 + (d + 1) + j by omega] using hpos (j + 1)),
        Finset.sum_range_succ', Finset.sum_congr rfl fun i _ ↦
          congrArg termAt (show d + 1 + i = d + (i + 1) by omega), Nat.add_zero]
      dsimp [termAt]
      omega
  intro sp
  refine (hloop M1 1 sp.1 sp.2.2 0 (by omega) (fun j hj ↦ ?_)
    (fun j ↦ splitPQRevLinear_pos_getD B M1 pq [] j)).trans ?_
  · rw [splitPQRevLinear_neg_getD B M1 pq [] j, ite_eq_left (by omega)]
  · rw [hbiased M1 0, Finset.sum_congr rfl fun j _ ↦ congrArg termAt (Nat.add_comm 1 j)]
end ConfigBiGqspChunkedMillerLinearRecPQ2a
end BiGqspChunkedMillerLinearRecPQ2a
end Slim
end BiGqspChunkedMillerLinearRecPQ2a
section BiGqspTrueAnglesFinalSumS4805
namespace SpecMirror.BiGqspTrueAnglesFinalSumS4805
section ConfigBiGqspTrueAnglesFinalSumS4805
open TFreeLaurentGQSP TFreeLaurentGQSPPresets
open TFreeLaurentGQSPPresets.FastRecurrenceVerifier
open TFreeLaurentGQSPPresets.FastIntervalRecurrenceVerifier
open BidirectionalCatalyzedGQSP
open BidirectionalIntervalRecurrenceVerifier
open SpecsAux.SpecMirror.BiGqspChunkedMillerCore
open SpecsAux.SpecMirror.BiGqspChunkedMillerCert
open SpecsAux.SpecMirror.BiGqspChebWeightCertS4805
open SpecsAux.Slim.BiGqspChunkedMillerLinearRecPQ2a
@[inline] def mkPQConsStrict_true (np nq : ℕ) (rest : List PQPair) : List PQPair :=
  match np, nq, rest with
  | 0,0, [] => [⟨0,0⟩]
  | 0,0, z :: zs => ⟨0,0⟩ :: z :: zs
  | 0, b + 1, [] => [⟨0, Nat.add b 1⟩]
  | 0, b + 1, z :: zs => ⟨0, Nat.add b 1⟩ :: z :: zs
  | a + 1,0, [] => [⟨Nat.add a 1,0⟩]
  | a + 1,0, z :: zs => ⟨Nat.add a 1,0⟩ :: z :: zs
  | a + 1, b + 1, [] => [⟨Nat.add a 1, Nat.add b 1⟩]
  | a + 1, b + 1, z :: zs => ⟨Nat.add a 1, Nat.add b 1⟩ :: z :: zs
theorem mkPQConsStrict_true_eq (np nq : ℕ) (rest : List PQPair) :
    mkPQConsStrict_true np nq rest = mkPQConsLazy np nq rest := by
  rcases np with _ | _ <;> rcases nq with _ | _ <;> rcases rest with _ | ⟨_, _⟩ <;> rfl
@[inline] def withHeadStrictPQ_true {α : Type*} (l : List PQPair) (f : List PQPair → α) : α :=
  match l with
  | [] => f []
  | x :: xs => f (x :: xs)
theorem withHeadStrictPQ_true_eq {α : Type*} (l : List PQPair) (f : List PQPair → α) :
    withHeadStrictPQ_true l f = f l := by
  rcases l with _ | ⟨_, _⟩ <;> rfl
def biHadamardRevAcc (B B2 : ℕ) : List PQPair → ℕ → List PQPair → List PQPair
  | [], q_prev, acc => mkPQConsStrict_true (Nat.div (Nat.add B q_prev) 2)
      (Nat.div (Nat.add B (Nat.sub B2 q_prev)) 2) acc
  | ⟨ph, qh⟩ :: t, q_prev, acc =>
      withHeadStrictPQ_true (mkPQConsStrict_true (Nat.div (Nat.add ph q_prev) 2)
        (Nat.div (Nat.add ph (Nat.sub B2 q_prev)) 2) acc) fun acc' ↦
        biHadamardRevAcc B B2 t qh acc'
theorem biHadamardRevAcc_eq (B B2 : ℕ) : ∀ (pq : List PQPair) (q_prev : ℕ) (acc : List PQPair),
      biHadamardRevAcc B B2 pq q_prev acc = (biHadamardFinishPair B B2 pq q_prev).reverse ++ acc
  | [], _, _ => by
      simp [biHadamardRevAcc, biHadamardFinishPair, mkPQConsStrict_true_eq, mkPQConsLazy_eq]
  | ⟨_, qh⟩ :: t, _, _ => by simp [biHadamardRevAcc, biHadamardFinishPair,
      withHeadStrictPQ_true_eq, mkPQConsStrict_true_eq, mkPQConsLazy_eq,
      biHadamardRevAcc_eq B B2 t qh]
def splitPQRevStrict_true (B : ℕ) : ℕ → List PQPair → List ℕ → List ℕ × ℕ × List PQPair
  | 0, [], neg_acc => (neg_acc, B, [])
  | 0, ⟨p, _⟩ :: xs, neg_acc => (neg_acc, p, xs)
  | m + 1, [], [] => splitPQRevStrict_true B m [] [B]
  | m + 1, [], y :: ys => splitPQRevStrict_true B m [] (B :: y :: ys)
  | m + 1, ⟨p, _⟩ :: xs, [] => splitPQRevStrict_true B m xs [p]
  | m + 1, ⟨p, _⟩ :: xs, y :: ys => splitPQRevStrict_true B m xs (p :: y :: ys)
theorem splitPQRevStrict_true_eq (B : ℕ) : ∀ (m : ℕ) (pq : List PQPair) (neg_acc : List ℕ),
      splitPQRevStrict_true B m pq neg_acc = splitPQRevLinear B m pq neg_acc
  | 0, [], _ => rfl
  | 0, ⟨_, _⟩ :: _, _ => rfl
  | m + 1, [], [] => splitPQRevStrict_true_eq B m [] [B]
  | m + 1, [], _ :: _ => splitPQRevStrict_true_eq B m [] _
  | m + 1, ⟨p, _⟩ :: xs, [] => splitPQRevStrict_true_eq B m xs [p]
  | m + 1, ⟨_, _⟩ :: xs, _ :: _ => splitPQRevStrict_true_eq B m xs _
@[inline] def stepListNat_true (B : ℕ) (xs : List ℕ) (f : ℕ → List ℕ → ℕ) : ℕ :=
  match xs with
  | [] => f B []
  | x :: xt => f x xt
theorem stepListNat_true_eq (B : ℕ) (xs : List ℕ) (f : ℕ → List ℕ → ℕ) :
    stepListNat_true B xs f = f (xs.getD 0 B) xs.tail := by
  rcases xs with _ | ⟨_, _⟩ <;> rfl
@[inline] def stepListPQP_true (B : ℕ) (xs : List PQPair) (f : ℕ → List PQPair → ℕ) : ℕ :=
  match xs with
  | [] => f B []
  | ⟨p, _⟩ :: xt => f p xt
theorem stepListPQP_true_eq (B : ℕ) (xs : List PQPair) (f : ℕ → List PQPair → ℕ) :
    stepListPQP_true B xs f = f (xs.getD 0 ⟨B, B⟩).p xs.tail := by
  rcases xs with _ | ⟨⟨_, _⟩, _⟩ <;> rfl
def chebL1SumPosStrict_true (M1 B B2 Bw W_err_dpos err_d_in : ℕ) :
    ℕ → List ℕ → List PQPair → List ℕ → ℕ → ℕ
  | _, _, _, [], acc => acc
  | d, neg_cur, pos_cur, w :: wt, acc =>
      forceNatFast (Nat.add d 1) fun d1 ↦
      stepListNat_true B neg_cur fun p_neg nt ↦
      stepListPQP_true B pos_cur fun p_pos_raw pt ↦
      let term := if Nat.ble d M1 then Nat.add (natAbsDiff
          (Nat.add (Nat.add (uParityFlip d B2 p_pos_raw) p_neg) Bw) (Nat.add w B2)) err_d_in
        else Nat.add (natAbsDiff w Bw) W_err_dpos
      forceNatFast (Nat.add acc term) fun acc' ↦
        chebL1SumPosStrict_true M1 B B2 Bw W_err_dpos err_d_in d1 nt pt wt acc'
def chebL1SumStrict_true (M1 B B2 Bw R_final W_err_d0 W_err_dpos : ℕ)
    (neg_rev : List ℕ) (p_center : ℕ) (pos_tail : List PQPair) (ws : List ℕ) : ℕ :=
  match ws with
  | [] => 0
  | w0 :: wt =>
      forceNatFast (Nat.add (Nat.mul 2 R_final) W_err_dpos) fun err_d_in ↦
      let term0 := Nat.add (natAbsDiff (Nat.add p_center Bw) (Nat.add w0 B))
        (Nat.add R_final W_err_d0)
      forceNatFast term0 fun acc1 ↦
        chebL1SumPosStrict_true M1 B B2 Bw W_err_dpos err_d_in 1 neg_rev pos_tail wt acc1
theorem chebL1SumStrict_true_eq (M1 B B2 Bw R_final W_err_d0 W_err_dpos : ℕ)
    (neg_rev : List ℕ) (p_center : ℕ) (pos_tail : List PQPair) (ws : List ℕ) :
    chebL1SumStrict_true M1 B B2 Bw R_final W_err_d0 W_err_dpos neg_rev p_center pos_tail ws =
      chebL1SumLinear M1 B B2 Bw R_final W_err_d0 W_err_dpos neg_rev p_center pos_tail ws := by
  have hpos (xs : List ℕ) : ∀ (d : ℕ) (nc : List ℕ) (pc : List PQPair) (acc : ℕ),
      chebL1SumPosStrict_true M1 B B2 Bw W_err_dpos (Nat.add (Nat.mul 2 R_final) W_err_dpos)
        d nc pc xs acc = chebL1SumPosLinear M1 B B2 Bw R_final W_err_dpos d nc pc xs acc := by
    induction xs with
    | nil =>
      intro _ _ _ _
      rfl
    | cons _ xt ih =>
      intro d nc pc acc
      unfold chebL1SumPosStrict_true chebL1SumPosLinear
      simp only [forceNatFast_eq, stepListNat_true_eq, stepListPQP_true_eq, ih]
  rcases ws with _ | ⟨_, _⟩
  · rfl
  · unfold chebL1SumStrict_true chebL1SumLinear
    simp only [forceNatFast_eq, hpos]
def asymDefectSumStrictLoop_true (B B2 two_Rf : ℕ) : ℕ → ℕ → List ℕ → List PQPair → ℕ → ℕ
  | 0, _, _, _, acc => acc
  | k + 1, d, neg_cur, pos_cur, acc =>
      forceNatFast (Nat.add d 1) fun d1 ↦
      stepListNat_true B neg_cur fun p_neg nt ↦
      stepListPQP_true B pos_cur fun p_pos_raw pt ↦
      forceNatFast (Nat.add acc (Nat.add (natAbsDiff (uParityFlip d B2 p_pos_raw) p_neg)
        two_Rf)) fun acc' ↦ asymDefectSumStrictLoop_true B B2 two_Rf k d1 nt pt acc'
def asymDefectSumStrict_true (M1 B B2 R_final : ℕ)
    (neg_rev : List ℕ) (pos_tail : List PQPair) : ℕ :=
  forceNatFast (Nat.mul 2 R_final) fun two_Rf ↦
    asymDefectSumStrictLoop_true B B2 two_Rf M1 1 neg_rev pos_tail 0
theorem asymDefectSumStrict_true_eq (M1 B B2 R_final : ℕ)
    (neg_rev : List ℕ) (pos_tail : List PQPair) :
    asymDefectSumStrict_true M1 B B2 R_final neg_rev pos_tail =
      asymDefectSumLinear M1 B B2 R_final neg_rev pos_tail := by
  have hloop (k : ℕ) : ∀ (d : ℕ) (nc : List ℕ) (pc : List PQPair) (acc : ℕ),
      asymDefectSumStrictLoop_true B B2 (Nat.mul 2 R_final) k d nc pc acc =
        asymDefectSumLinearLoop B B2 R_final k d nc pc acc := by
    induction k with
    | zero =>
      intro _ _ _ _
      rfl
    | succ k ih =>
      intro d nc pc acc
      unfold asymDefectSumStrictLoop_true asymDefectSumLinearLoop
      simp only [forceNatFast_eq, stepListNat_true_eq, stepListPQP_true_eq, ih]
  unfold asymDefectSumStrict_true asymDefectSumLinear
  simp only [forceNatFast_eq, hloop]
end ConfigBiGqspTrueAnglesFinalSumS4805
end SpecMirror.BiGqspTrueAnglesFinalSumS4805
end BiGqspTrueAnglesFinalSumS4805
set_option maxRecDepth 2000
end SpecsAux
end
end ModBiGqspVerifierCore

end QuantumComputation.Specs.StoppingPowerSolution
