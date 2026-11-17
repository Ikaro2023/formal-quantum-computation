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

public import QuantumComputation.Circuits.DynamicCircuit
public import QuantumComputation.Circuits.ResourceCounting
public import QuantumComputation.QuantumHoareLogic.CleanAncilla
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

@[expose] public section

namespace QuantumComputation.Specs

namespace ArcsinImpl

variable {Var : Type}

open Operator Matrix QProg Function
open scoped Matrix ComplexOrder MatrixOrder


section KrausBound

open HermitianMat

variable {Var : Type} [DecidableEq Var] {d : ℕ} [NeZero d]

/-- `R` is an averaged Kraus lower bound of `P`: `Rᴴ A R ≤ wp P A` for every
store-independent postcondition `A` and every store. -/
def LowerKraus (P : QProg Var d) (R : Matrix (Fin d) (Fin d) ℂ) : Prop :=
  ∀ (A : Observable (Fin d)) (σ : Store Var), A.1.conj Rᴴ ≤ (wp P (fun _ ↦ A) σ).1

theorem lowerKraus_qAssign (U : Unitary d) : LowerKraus (Var := Var) (.qAssign U) U.1 := by
  intro A σ
  apply le_of_eq
  ext1
  simp [wp, Matrix.star_eq_conjTranspose]

theorem lowerKraus_skip : LowerKraus (Var := Var) (d := d) .skip 1 := by
  intro A σ
  simp [wp]

namespace LowerKraus

variable {P Q : QProg Var d} {R R₁ R₂ : Matrix (Fin d) (Fin d) ℂ}

theorem conj_le_one (h : LowerKraus P R) (A : Observable (Fin d)) : A.1.conj Rᴴ ≤ 1 :=
  (conj_mono A.2.2).trans ((h 1 (fun _ ↦ 0)).trans (wp P (fun _ ↦ 1) (fun _ ↦ 0)).2.2)

/-- The observable `Rᴴ A R` attached to a lower bound. -/
noncomputable def conjObs (h : LowerKraus P R) (A : Observable (Fin d)) : Observable (Fin d) :=
  ⟨A.1.conj Rᴴ, conj_nonneg _ A.2.1, h.conj_le_one A⟩

theorem qSeq (h₁ : LowerKraus P R₁) (h₂ : LowerKraus Q R₂) :
    LowerKraus (P.qSeq Q) (R₂ * R₁) := by
  intro A σ
  have hmono : (fun _ ↦ h₂.conjObs A) ≤ wp Q (fun _ ↦ A) := fun σ' ↦ h₂ A σ'
  calc A.1.conj (R₂ * R₁)ᴴ = (h₂.conjObs A).1.conj R₁ᴴ := by
        rw [conjObs, conj_conj, conjTranspose_mul]
    _ ≤ (wp P (fun _ ↦ h₂.conjObs A) σ).1 := h₁ _ σ
    _ ≤ (wp P (wp Q (fun _ ↦ A)) σ).1 := wp_mono P hmono σ

end LowerKraus

/-- The real scalar `√½` as a complex number. -/
noncomputable abbrev sqrtHalf : ℂ := (Real.sqrt (1 / 2) : ℝ)

theorem sqrtHalf_mul_sqrtHalf : sqrtHalf * sqrtHalf = 1 / 2 := by
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
  push_cast
  ring

omit [NeZero d] in
private theorem conj_add_conj_eq (A : HermitianMat (Fin d) ℂ) (B₀ B₁ : Matrix (Fin d) (Fin d) ℂ) :
    A.conj B₀ᴴ + A.conj B₁ᴴ =
      A.conj (sqrtHalf • (B₀ + B₁))ᴴ + A.conj (sqrtHalf • (B₀ - B₁))ᴴ := by
  ext1
  have hs : star sqrtHalf = sqrtHalf := Complex.conj_ofReal _
  simp only [HermitianMat.mat_add, conj_apply_mat, conjTranspose_conjTranspose,
    conjTranspose_smul, hs, Matrix.smul_mul, Matrix.mul_smul, conjTranspose_add,
    conjTranspose_sub, Matrix.add_mul, Matrix.mul_add, Matrix.sub_mul, Matrix.mul_sub]
  match_scalars <;> first | ring1 | linear_combination (-2 : ℂ) * sqrtHalf_mul_sqrtHalf

/-- Measurement-based correction: measuring with a two-outcome measurement `ℳ` into `v`,
then applying `F` on outcome `1`, admits the averaged bound `√½ (M₀ + R_F M₁)`. -/
theorem lowerKraus_measure_qIf (v : Var) (ℳ : Measurement d 2) {F : QProg Var d}
    {R_F : Matrix (Fin d) (Fin d) ℂ} (hF : LowerKraus F R_F) :
    LowerKraus ((QProg.qMeasure v ℳ).qSeq (.qIf (fun σ ↦ σ v = 1) F .skip))
      (sqrtHalf • (ℳ.1 0 + R_F * ℳ.1 1)) := by
  intro A σ
  have hwp : (wp ((QProg.qMeasure v ℳ).qSeq (.qIf (fun σ ↦ σ v = 1) F .skip))
      (fun _ ↦ A) σ).1 =
      A.1.conj (ℳ.1 0)ᴴ + (wp F (fun _ ↦ A) (Store.subst σ v 1)).1.conj (ℳ.1 1)ᴴ := by
    simp only [wp, CQAssertion.qMeasure_coe, Fin.sum_univ_two]
    simp [Store.subst]
  rw [hwp]
  calc A.1.conj (sqrtHalf • (ℳ.1 0 + R_F * ℳ.1 1))ᴴ
      ≤ A.1.conj (sqrtHalf • (ℳ.1 0 + R_F * ℳ.1 1))ᴴ +
          A.1.conj (sqrtHalf • (ℳ.1 0 - R_F * ℳ.1 1))ᴴ :=
        le_add_of_nonneg_right (conj_nonneg _ A.2.1)
    _ = A.1.conj (ℳ.1 0)ᴴ + (A.1.conj R_Fᴴ).conj (ℳ.1 1)ᴴ := by
        rw [← conj_add_conj_eq, conj_conj, conjTranspose_mul]
    _ ≤ _ := add_le_add_right (conj_mono (hF A _)) _

/-- An averaged lower bound `R` whose clean-ancilla restriction agrees with the intended unitary
`E = rTarget.embedUnitary U` (i.e. `Π₀ R = Π₀ E Π₀`) yields a clean subroutine. -/
theorem realizesCleanSubroutine_of_lowerKraus {n k m : ℕ} [NeZero (2 ^ n)]
    (rTarget : QRegister k n) (rAnc : QRegister m n) (hdisj : rTarget.DisjointWires rAnc)
    (U : Unitary (2 ^ k)) {P : QProg Var (2 ^ n)} {R : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ}
    (hP : LowerKraus P R)
    (hR : rAnc.basisOutcomeProjector 0 * R =
      rAnc.basisOutcomeProjector 0 * (rTarget.embedUnitary U).1 *
        rAnc.basisOutcomeProjector 0) :
    RealizesCleanSubroutine rTarget rAnc hdisj U P := by
  intro M
  apply Triple.of_le_wp
  intro σ
  change (CQAssertion.restrictToZeroAncilla _ rAnc σ).1 ≤ (wp P _ σ).1
  refine le_trans (le_of_eq ?_) (hP (CQAssertion.restrictToZeroAncilla (fun _ ↦ M) rAnc σ) σ)
  have hR' : Rᴴ * rAnc.basisOutcomeProjector 0 =
      rAnc.basisOutcomeProjector 0 * (rTarget.embedUnitary U).1ᴴ *
        rAnc.basisOutcomeProjector 0 := by
    simpa [conjTranspose_mul, Matrix.mul_assoc] using congrArg conjTranspose hR
  have hpost : (CQAssertion.restrictToZeroAncilla (fun _ ↦ M) rAnc σ).1 =
      M.1.conj (rAnc.basisOutcomeProjector 0) := rfl
  have hpre : (CQAssertion.restrictToZeroAncilla
      (CQAssertion.qAssign (rTarget.embedUnitary U)
        (CQAssertion.restrictToZeroAncilla (fun _ ↦ M) rAnc))
      rAnc σ).1 = ((M.1.conj (rAnc.basisOutcomeProjector 0)).conj
        (star (rTarget.embedUnitary U)).1).conj (rAnc.basisOutcomeProjector 0) := rfl
  rw [hpre, hpost, conj_conj, conj_conj, conj_conj, hR', Unitary.coe_star,
    Matrix.star_eq_conjTranspose]

end KrausBound

variable {n k : ℕ}

abbrev basisBitsEquiv (q : ℕ) : Fin (2 ^ q) ≃ BitAssignment q := basisBits q

/-- Computational-basis vector with bit assignment `β`. -/
noncomputable abbrev ket (β : BitAssignment n) : Fin (2 ^ n) → ℂ :=
  basisState ((basisBits n).symm β)

@[simp]
theorem basisBits_basisBitsEquiv_symm (q : ℕ) (β : BitAssignment q) :
    basisBits q ((basisBits q).symm β) = β :=
  (basisBits q).apply_symm_apply β

@[simp]
theorem basisBitsEquiv_symm_basisBits (q : ℕ) (j : Fin (2 ^ q)) :
    (basisBits q).symm (basisBits q j) = j :=
  (basisBits q).symm_apply_apply j

theorem single_eq_ket (g : Fin (2 ^ n)) :
    (Pi.single g 1 : Fin (2 ^ n) → ℂ) = ket (basisBits n g) := by
  simp [ket]

/-- Overwrite the bits selected by `r` with `γ`. -/
noncomputable def writeReg (β : BitAssignment n) (r : QRegister k n) (γ : BitAssignment k) :
    BitAssignment n :=
  basisBits n (r.replaceIndex ((basisBits n).symm β) ((basisBits k).symm γ))

@[simp]
theorem writeReg_apply_reg (β : BitAssignment n) (r : QRegister k n) (γ : BitAssignment k)
    (i : Fin k) : writeReg β r γ (r i) = γ i := by
  simp [writeReg, QRegister.basisBits_replaceIndex_apply]

theorem writeReg_apply_of_not_mem (β : BitAssignment n) (r : QRegister k n) (γ : BitAssignment k)
    (w : Wire n) (hw : w ∉ Set.range r.wires) : writeReg β r γ w = β w := by
  simp [writeReg, QRegister.basisBits_replaceIndex_of_not_mem _ _ _ _ hw]

/-- Writing a register that agrees with `β` except at position `i₀` is a single-bit update. -/
theorem writeReg_eq_update (β : BitAssignment n) (r : QRegister k n) (γ : BitAssignment k)
    (i₀ : Fin k) (hγ : ∀ i, i ≠ i₀ → γ i = β (r i)) :
    writeReg β r γ = Function.update β (r i₀) (γ i₀) := by
  funext w
  by_cases hw : w ∈ Set.range r.wires
  · obtain ⟨i, rfl⟩ := hw
    rw [writeReg_apply_reg]
    by_cases hi : i = i₀
    · subst hi
      simp
    · rw [Function.update_of_ne (fun h ↦ hi (r.wires.injective h)), hγ i hi]
  · rw [writeReg_apply_of_not_mem _ _ _ _ hw, Function.update_of_ne]
    exact fun h ↦ hw ⟨i₀, h.symm⟩

/-- Local basis index read through a register. -/
noncomputable abbrev localIdx (r : QRegister k n) (β : BitAssignment n) : Fin (2 ^ k) :=
  (basisBits k).symm (fun i ↦ β (r i))

@[simp]
theorem localIdx_writeReg (β : BitAssignment n) (r : QRegister k n) (γ : BitAssignment k) :
    localIdx r (writeReg β r γ) = (basisBits k).symm γ := by
  simp [localIdx]

theorem localIdx_writeReg_of_disjoint {m : ℕ} (β : BitAssignment n) (r : QRegister k n)
    (s : QRegister m n) (hdisj : r.DisjointWires s) (γ : BitAssignment k) :
    localIdx s (writeReg β r γ) = localIdx s β := by
  simp only [localIdx]
  congr 1
  funext i
  exact writeReg_apply_of_not_mem _ _ _ _ fun hw ↦ Set.disjoint_left.1 hdisj hw ⟨i, rfl⟩

@[simp]
theorem writeReg_writeReg (β : BitAssignment n) (r : QRegister k n) (γ γ' : BitAssignment k) :
    writeReg (writeReg β r γ) r γ' = writeReg β r γ' := by
  funext w
  by_cases hw : w ∈ Set.range r.wires
  · obtain ⟨i, rfl⟩ := hw
    rw [writeReg_apply_reg, writeReg_apply_reg]
  · rw [writeReg_apply_of_not_mem _ _ _ _ hw, writeReg_apply_of_not_mem _ _ _ _ hw,
      writeReg_apply_of_not_mem _ _ _ _ hw]

@[simp]
theorem writeReg_self (β : BitAssignment n) (r : QRegister k n) :
    writeReg β r (fun i ↦ β (r i)) = β := by
  funext w
  by_cases hw : w ∈ Set.range r.wires
  · obtain ⟨i, rfl⟩ := hw
    rw [writeReg_apply_reg]
  · rw [writeReg_apply_of_not_mem _ _ _ _ hw]

/-- An embedded local matrix acting on a basis ket. -/
theorem embedMatrix_mulVec_ket (r : QRegister k n) (A : Matrix (Fin (2 ^ k)) (Fin (2 ^ k)) ℂ)
    (β : BitAssignment n) :
    (r.embedMatrix A).mulVec (ket β) =
      ∑ l : Fin (2 ^ k), A l (localIdx r β) • ket (writeReg β r (basisBits k l)) := by
  have hext : r.extractIndex ((basisBits n).symm β) = localIdx r β := by
    simp [QRegister.extractIndex]
  have hcol (j : Fin (2 ^ k)) :
      A.mulVec (Pi.single j 1) = ∑ l : Fin (2 ^ k), A l j • Pi.single l 1 := by
    funext x
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  rw [ket, basisState, r.embedMatrix_mulVec_single_factors, hext, hcol,
    QRegister.tensorState_sum_left]
  refine Finset.sum_congr rfl fun l _ ↦ ?_
  rw [QRegister.tensorState_smul_left, QRegister.tensorState_single_replaceIndex]
  simp [writeReg, ket, basisState]

/-- An embedded permutation matrix maps a basis ket to a basis ket. -/
theorem embedMatrix_permMatrix_mulVec_ket (r : QRegister k n) (σ : Equiv.Perm (Fin (2 ^ k)))
    (β : BitAssignment n) :
    (r.embedMatrix (σ.permMatrix ℂ)).mulVec (ket β) =
      ket (writeReg β r (basisBits k (σ.symm (localIdx r β)))) := by
  rw [embedMatrix_mulVec_ket, Finset.sum_eq_single (σ.symm (localIdx r β))]
  · simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]
  · intro l _ hl
    have : σ l ≠ localIdx r β := fun h ↦ hl (by rw [← h, Equiv.symm_apply_apply])
    simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, this]
  · simp

/-- An embedded one-qubit matrix acting on a basis ket. -/
theorem singleton_embedMatrix_mulVec_ket (q : Wire n) (A : Matrix (Fin 2) (Fin 2) ℂ)
    (β : BitAssignment n) :
    ((QRegister.singleton q).embedMatrix A).mulVec (ket β) =
      A 0 (if β q = 0 then 0 else 1) • ket (Function.update β q 0) +
        A 1 (if β q = 0 then 0 else 1) • ket (Function.update β q 1) := by
  have hloc : localIdx (QRegister.singleton q) β = if β q = 0 then 0 else 1 := by
    have h : ∀ b : ZMod 2,
        ((basisBits 1).symm (fun _ ↦ b) : Fin 2) = if b = 0 then 0 else 1 := by decide
    exact h (β q)
  have hw (l : Fin 2) (b : ZMod 2) (hb : basisBits 1 l = fun _ ↦ b) :
      writeReg β (QRegister.singleton q) (basisBits 1 l) = Function.update β q b := by
    rw [writeReg_eq_update _ _ _ 0 (fun i hi ↦ absurd (Subsingleton.elim i 0) hi), hb]
    rfl
  rw [embedMatrix_mulVec_ket, hloc]
  change ∑ l : Fin 2, _ = _
  rw [Fin.sum_univ_two, hw 0 0 (by decide), hw 1 1 (by decide)]

/-- Sign `(-1)^b` of a bit. -/
abbrev bitSign (b : ZMod 2) : ℂ := if b = 0 then 1 else -1

theorem bit_cases (b : ZMod 2) : b = 0 ∨ b = 1 := by
  fin_cases b
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem one_add_one_zmod2 : (1 : ZMod 2) + 1 = 0 := rfl

theorem ket_X (q : Wire n) (β : BitAssignment n) :
    (Circuit.X q).eval.1.mulVec (ket β) = ket (Function.update β q (β q + 1)) := by
  rw [Circuit.eval_single, QRegister.embedUnitary_val, PrimitiveGate.eval]
  change ((QRegister.singleton q).embedMatrix !![0, 1; 1, 0]).mulVec _ = _
  rw [singleton_embedMatrix_mulVec_ket]
  rcases bit_cases (β q) with hb | hb <;> simp [hb, one_add_one_zmod2]

theorem ket_Z (q : Wire n) (β : BitAssignment n) :
    (Circuit.Z q).eval.1.mulVec (ket β) = bitSign (β q) • ket β := by
  rw [Circuit.eval_single, QRegister.embedUnitary_val, PrimitiveGate.eval]
  change ((QRegister.singleton q).embedMatrix !![1, 0; 0, -1]).mulVec _ = _
  rw [singleton_embedMatrix_mulVec_ket]
  have e := Function.update_eq_self q β
  rcases bit_cases (β q) with hb | hb <;> rw [hb] at e <;> simp [hb, e]

/-- Phase `i^b` of a bit. -/
abbrev bitPhaseI (b : ZMod 2) : ℂ := if b = 0 then 1 else Complex.I

theorem ket_S (q : Wire n) (β : BitAssignment n) :
    (Circuit.S q).eval.1.mulVec (ket β) = bitPhaseI (β q) • ket β := by
  rw [Circuit.eval_single, QRegister.embedUnitary_val, PrimitiveGate.eval]
  change ((QRegister.singleton q).embedMatrix !![1, 0; 0, Complex.I]).mulVec _ = _
  rw [singleton_embedMatrix_mulVec_ket]
  have e := Function.update_eq_self q β
  rcases bit_cases (β q) with hb | hb <;> rw [hb] at e <;> simp [hb, e]

theorem ket_H (q : Wire n) (β : BitAssignment n) :
    (Circuit.H q).eval.1.mulVec (ket β) =
      (Real.sqrt (1 / 2) : ℂ) • (ket (Function.update β q 0) +
        bitSign (β q) • ket (Function.update β q 1)) := by
  rw [Circuit.eval_single, QRegister.embedUnitary_val, PrimitiveGate.eval]
  change ((QRegister.singleton q).embedMatrix
    ((Real.sqrt (1 / 2) : ℝ) • !![(1 : ℂ), 1; 1, -1])).mulVec _ = _
  rw [singleton_embedMatrix_mulVec_ket]
  rcases bit_cases (β q) with hb | hb <;> simp [hb, smul_add, Complex.real_smul]

theorem ket_CNOT (c t : Wire n) (h : c ≠ t) (β : BitAssignment n) :
    (Circuit.CNOT c t h).eval.1.mulVec (ket β) = ket (Function.update β t (β t + β c)) := by
  rw [Circuit.eval_gate, QRegister.embedUnitary_val, PrimitiveGate.eval_cnot_val,
    embedMatrix_permMatrix_mulVec_ket]
  have hloc : ∀ γ : BitAssignment 2,
      basisBits 2 ((Equiv.swap (1 : Fin 4) 3).symm ((basisBits 2).symm γ)) =
        Function.update γ 1 (γ 1 + γ 0) := by decide
  rw [localIdx, hloc, writeReg_eq_update _ _ _ 1]
  · simp
  · intro i hi
    fin_cases i
    · simp
    · exact absurd rfl hi

/-- Exact single-qubit inverse `T† = Z · S · T` using `1` `T` gate and `0` `TOFF` gates. -/
def T_dag (q : Wire n) : Circuit n :=
  .seq (Circuit.Z q) (.seq (Circuit.S q) (Circuit.T q))

/-- Clean-ancilla 4-`T` AND gate on wires `c₁, c₂, t` (`4` `T` gates, `0` `TOFF` gates). -/
def AND4T (c₁ c₂ t : Wire n) (_h₁₂ : c₁ ≠ c₂) (h₁t : c₁ ≠ t) (h₂t : c₂ ≠ t) : Circuit n :=
  .seq (Circuit.H t)
    (.seq (Circuit.CNOT c₂ t h₂t)
      (.seq (T_dag t)
        (.seq (Circuit.CNOT c₁ t h₁t)
          (.seq (Circuit.T t)
            (.seq (Circuit.CNOT c₂ t h₂t)
              (.seq (T_dag t)
                (.seq (Circuit.CNOT c₁ t h₁t)
                  (.seq (Circuit.T t)
                    (.seq (Circuit.H t) (Circuit.S t))))))))))

/-- Monomial phase of `AND4T` on computational basis inputs `a, b, c : ZMod 2`
(`+1` whenever `c = 0`). -/
noncomputable def cleanAndPhase (a b c : ZMod 2) : ℂ :=
  if c = 0 then 1 else if a * b = 1 then -Complex.I else Complex.I

theorem count_T_AND4T (c₁ c₂ t : Wire n) (h₁₂ : c₁ ≠ c₂) (h₁t : c₁ ≠ t) (h₂t : c₂ ≠ t) :
    (AND4T c₁ c₂ t h₁₂ h₁t h₂t).count PrimitiveGate.T = 4 := rfl

theorem count_TOFF_AND4T (c₁ c₂ t : Wire n) (h₁₂ : c₁ ≠ c₂) (h₁t : c₁ ≠ t) (h₂t : c₂ ≠ t) :
    (AND4T c₁ c₂ t h₁₂ h₁t h₂t).count PrimitiveGate.TOFF = 0 := rfl

noncomputable abbrev bitPhaseT (b : ZMod 2) : ℂ :=
  if b = 0 then 1 else (1 + Complex.I) / (Real.sqrt 2 : ℂ)

theorem ket_T (q : Wire n) (β : BitAssignment n) :
    (Circuit.T q).eval.1.mulVec (ket β) = bitPhaseT (β q) • ket β := by
  rw [Circuit.eval_single, QRegister.embedUnitary_val, PrimitiveGate.eval]
  change ((QRegister.singleton q).embedMatrix
    !![1, 0; 0, (1 + Complex.I) / (Real.sqrt 2 : ℂ)]).mulVec _ = _
  rw [singleton_embedMatrix_mulVec_ket]
  have e := Function.update_eq_self q β
  rcases bit_cases (β q) with hb | hb <;> rw [hb] at e <;> simp [hb, e]

theorem seq_mulVec (c₁ c₂ : Circuit n) (ψ : Fin (2 ^ n) → ℂ) :
    (c₁.seq c₂).eval.1.mulVec ψ = c₂.eval.1.mulVec (c₁.eval.1.mulVec ψ) := by
  rw [Circuit.eval_seq, Matrix.mulVec_mulVec]
  rfl

theorem ket_T_dag (q : Wire n) (β : BitAssignment n) :
    (T_dag q).eval.1.mulVec (ket β) =
      (bitSign (β q) * (bitPhaseI (β q) * bitPhaseT (β q))) • ket β := by
  simp only [T_dag, seq_mulVec, ket_Z, ket_S, ket_T, Matrix.mulVec_smul, smul_smul]

theorem ket_AND4T_eq_smul (c₁ c₂ t : Wire n) (h₁₂ : c₁ ≠ c₂) (h₁t : c₁ ≠ t) (h₂t : c₂ ≠ t)
    (β : BitAssignment n) :
    (AND4T c₁ c₂ t h₁₂ h₁t h₂t).eval.1.mulVec (ket β) =
      cleanAndPhase (β c₁) (β c₂) (β t) • ket (Function.update β t (β t + β c₁ * β c₂)) := by
  have hs2 : (Real.sqrt (1 / 2) : ℂ) ^ 2 = 1 / 2 := by
    norm_cast
    rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    norm_num
  have h2 : ((Real.sqrt 2 : ℂ)⁻¹) ^ 2 = 1 / 2 := by
    rw [inv_pow]
    norm_cast
    rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have h4 : ((Real.sqrt 2 : ℂ)⁻¹) ^ 4 = 1 / 4 := by
    linear_combination ((Real.sqrt 2 : ℂ)⁻¹ ^ 2 + 1 / 2) * h2
  have hi2 : Complex.I ^ 2 = -1 := Complex.I_sq
  have hi3 : Complex.I ^ 3 = -Complex.I := by
    linear_combination Complex.I * hi2
  have hi4 : Complex.I ^ 4 = 1 := by
    linear_combination (Complex.I ^ 2 - 1) * hi2
  have hi5 : Complex.I ^ 5 = Complex.I := by
    linear_combination (Complex.I ^ 3 - Complex.I) * hi2
  have hi6 : Complex.I ^ 6 = -1 := by
    linear_combination (Complex.I ^ 4 - Complex.I ^ 2 + 1) * hi2
  have hi7 : Complex.I ^ 7 = -Complex.I := by
    linear_combination (Complex.I ^ 5 - Complex.I ^ 3 + Complex.I) * hi2
  simp only [AND4T, seq_mulVec, ket_H, ket_CNOT, ket_T, ket_T_dag, ket_S,
    Matrix.mulVec_smul, Matrix.mulVec_add, smul_add, smul_smul,
    Function.update_idem, Function.update_self,
    Function.update_of_ne h₁t, Function.update_of_ne h₂t]
  rcases bit_cases (β c₁) with h₁ | h₁ <;>
    rcases bit_cases (β c₂) with h₂ | h₂ <;>
    rcases bit_cases (β t) with ht | ht <;>
    simp only [h₁, h₂, ht, one_add_one_zmod2, cleanAndPhase, bitSign, bitPhaseI, bitPhaseT,
      zero_ne_one, one_ne_zero, ↓reduceIte, zero_add, add_zero, mul_zero, one_mul, mul_one] <;>
    match_scalars <;>
    ring_nf <;>
    simp only [hs2, h2, h4, hi2, hi3, hi4, hi5, hi6, hi7] <;>
    ring


/-- 4-`T` relative-phase Toffoli gate with phase `+1` whenever `a * b * c = 0`. -/
def RCCX0 (c₁ c₂ t : Wire n) (h₁₂ : c₁ ≠ c₂) (h₁t : c₁ ≠ t) (h₂t : c₂ ≠ t) : Circuit n :=
  .seq (Circuit.Z t) (.seq (Circuit.S t) (AND4T c₁ c₂ t h₁₂ h₁t h₂t))

/-- 4-`T` relative-phase Toffoli gate with phase `+1` whenever `a * b * (c + 1) = 0`. -/
def RCCX1 (c₁ c₂ t : Wire n) (h₁₂ : c₁ ≠ c₂) (h₁t : c₁ ≠ t) (h₂t : c₂ ≠ t) : Circuit n :=
  .seq (Circuit.X t) (.seq (RCCX0 c₁ c₂ t h₁₂ h₁t h₂t) (Circuit.X t))

noncomputable def rccx0Phase (a b c : ZMod 2) : ℂ :=
  bitSign c * (bitPhaseI c * cleanAndPhase a b c)

theorem rccx0Phase_eq_one {a b c : ZMod 2} (h : a * b * c = 0) : rccx0Phase a b c = 1 := by
  rcases bit_cases a with rfl | rfl <;>
    rcases bit_cases b with rfl | rfl <;>
    rcases bit_cases c with rfl | rfl <;>
    simp_all [rccx0Phase, bitSign, bitPhaseI, cleanAndPhase, Complex.I_mul_I]

theorem count_T_RCCX0 (c₁ c₂ t : Wire n) (h₁₂ : c₁ ≠ c₂) (h₁t : c₁ ≠ t) (h₂t : c₂ ≠ t) :
    (RCCX0 c₁ c₂ t h₁₂ h₁t h₂t).count PrimitiveGate.T = 4 := rfl

theorem count_TOFF_RCCX0 (c₁ c₂ t : Wire n) (h₁₂ : c₁ ≠ c₂) (h₁t : c₁ ≠ t) (h₂t : c₂ ≠ t) :
    (RCCX0 c₁ c₂ t h₁₂ h₁t h₂t).count PrimitiveGate.TOFF = 0 := rfl

theorem count_T_RCCX1 (c₁ c₂ t : Wire n) (h₁₂ : c₁ ≠ c₂) (h₁t : c₁ ≠ t) (h₂t : c₂ ≠ t) :
    (RCCX1 c₁ c₂ t h₁₂ h₁t h₂t).count PrimitiveGate.T = 4 := rfl

theorem count_TOFF_RCCX1 (c₁ c₂ t : Wire n) (h₁₂ : c₁ ≠ c₂) (h₁t : c₁ ≠ t) (h₂t : c₂ ≠ t) :
    (RCCX1 c₁ c₂ t h₁₂ h₁t h₂t).count PrimitiveGate.TOFF = 0 := rfl

theorem ket_RCCX0_eq_smul (c₁ c₂ t : Wire n) (h₁₂ : c₁ ≠ c₂) (h₁t : c₁ ≠ t) (h₂t : c₂ ≠ t)
    (β : BitAssignment n) :
    (RCCX0 c₁ c₂ t h₁₂ h₁t h₂t).eval.1.mulVec (ket β) =
      rccx0Phase (β c₁) (β c₂) (β t) • ket (Function.update β t (β t + β c₁ * β c₂)) := by
  simp only [RCCX0, seq_mulVec, ket_Z, ket_S, ket_AND4T_eq_smul, Matrix.mulVec_smul, smul_smul,
    rccx0Phase]

theorem ket_RCCX1_eq_smul (c₁ c₂ t : Wire n) (h₁₂ : c₁ ≠ c₂) (h₁t : c₁ ≠ t) (h₂t : c₂ ≠ t)
    (β : BitAssignment n) :
    (RCCX1 c₁ c₂ t h₁₂ h₁t h₂t).eval.1.mulVec (ket β) =
      rccx0Phase (β c₁) (β c₂) (β t + 1) • ket (Function.update β t (β t + β c₁ * β c₂)) := by
  have hadd : ∀ x y : ZMod 2, x + 1 + y + 1 = x + y := by decide
  have hup : Function.update (Function.update (Function.update β t (β t + 1)) t
      (β t + 1 + β c₁ * β c₂)) t (β t + 1 + β c₁ * β c₂ + 1) =
      Function.update β t (β t + β c₁ * β c₂) := by
    rw [Function.update_idem, Function.update_idem, hadd]
  simp only [RCCX1, seq_mulVec, ket_X, ket_RCCX0_eq_smul, Matrix.mulVec_smul,
    Function.update_self, Function.update_of_ne h₁t, Function.update_of_ne h₂t, hup]
/-- Projector onto outcome `o` of a single wire, acting on a basis ket. -/
theorem ket_projector (q : Wire n) (o : Fin 2) (β : BitAssignment n) :
    ((QRegister.singleton q).basisOutcomeProjector o).mulVec (ket β) =
      if β q = (o.val : ZMod 2) then ket β else 0 := by
  rw [ket, basisState, QRegister.basisOutcomeProjector_mulVec_single]
  have h : ∀ (b : ZMod 2) (o : Fin 2),
      (((basisBits 1).symm (fun _ ↦ b) : Fin 2) = o ↔ b = (o.val : ZMod 2)) := by decide
  have hext : (QRegister.singleton q).extractIndex ((basisBits n).symm β) =
      (basisBits 1).symm (fun _ ↦ β q) := by
    simp [QRegister.extractIndex]
  simp only [hext]
  split_ifs with h1 h2 h2 <;> first | rfl | exact absurd ((h _ _).1 h1) h2 |
    exact absurd ((h _ _).2 h2) h1

theorem ket_projector_zero (q : Wire n) (β : BitAssignment n) :
    ((QRegister.singleton q).basisOutcomeProjector 0).mulVec (ket β) =
      if β q = 0 then ket β else 0 :=
  ket_projector q 0 β

theorem ket_projector_one (q : Wire n) (β : BitAssignment n) :
    ((QRegister.singleton q).basisOutcomeProjector 1).mulVec (ket β) =
      if β q = 1 then ket β else 0 :=
  ket_projector q 1 β

/-- Two matrices agreeing on every basis ket are equal. -/
theorem matrix_ext_ket {A B : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ}
    (h : ∀ β, A.mulVec (ket β) = B.mulVec (ket β)) : A = B := by
  ext i j
  have := congrFun (h (basisBits n j)) i
  simpa [← single_eq_ket, Matrix.mulVec_single_one] using this

/-- A register outcome projector acting on a basis ket. -/
theorem basisOutcomeProjector_mulVec_ket (r : QRegister k n) (o : Fin (2 ^ k))
    (β : BitAssignment n) :
    (r.basisOutcomeProjector o).mulVec (ket β) = if localIdx r β = o then ket β else 0 := by
  have hext : r.extractIndex ((basisBits n).symm β) = localIdx r β := by
    simp [QRegister.extractIndex]
  rw [ket, basisState, QRegister.basisOutcomeProjector_mulVec_single, hext]

variable {n : ℕ}

/-- Basis ket of an optional bit assignment, `0` for `none`. -/
noncomputable def optKet : Option (BitAssignment n) → Fin (2 ^ n) → ℂ
  | none => 0
  | some β => ket β

theorem lowerKraus_circuit [DecidableEq Var] [NeZero (2 ^ n)] (c : Circuit n) :
    LowerKraus (Var := Var) c.compile c.eval.1 := by
  induction c with
  | identity => exact lowerKraus_skip
  | gate g r => exact lowerKraus_qAssign _
  | seq c₁ c₂ ih₁ ih₂ => exact ih₁.qSeq ih₂

theorem eval_seq_mulVec (c₁ c₂ : Circuit n) (ψ : Fin (2 ^ n) → ℂ) :
    (Circuit.seq c₁ c₂).eval.1.mulVec ψ = c₂.eval.1.mulVec (c₁.eval.1.mulVec ψ) := by
  rw [Circuit.eval_seq, Matrix.mulVec_mulVec]
  rfl

/-- Phase correction `CZ(c₁, c₂)` (from `S`, `Z` and `CNOT`) followed by `X t`. -/
def fixup (c₁ c₂ t : Wire n) (h : c₁ ≠ c₂) : Circuit n :=
  .seq (Circuit.S c₁) (.seq (Circuit.S c₂) (.seq (Circuit.CNOT c₁ c₂ h) (.seq (Circuit.S c₂)
    (.seq (Circuit.Z c₂) (.seq (Circuit.CNOT c₁ c₂ h) (Circuit.X t))))))

theorem phase_cz (a b : ZMod 2) :
    bitPhaseI a * bitPhaseI b * bitPhaseI (b + a) * bitSign (b + a) = bitSign (a * b) := by
  rcases bit_cases a with rfl | rfl <;> rcases bit_cases b with rfl | rfl <;>
    simp [bitPhaseI, bitSign, one_add_one_zmod2, Complex.I_mul_I]

theorem fixup_mulVec_ket (c₁ c₂ t : Wire n) (h₁₂ : c₁ ≠ c₂) (β : BitAssignment n) :
    (fixup c₁ c₂ t h₁₂).eval.1.mulVec (ket β) =
      bitSign (β c₁ * β c₂) • ket (update β t (β t + 1)) := by
  have hβ : update (update β c₂ (β c₂ + β c₁)) c₂ (β c₂ + β c₁ + β c₁) = β := by
    rw [update_idem, add_assoc, CharTwo.add_self_eq_zero, add_zero, update_eq_self]
  simp only [fixup, eval_seq_mulVec, ket_S, ket_Z, ket_CNOT, ket_X, Matrix.mulVec_smul,
    update_self, update_of_ne h₁₂, hβ, smul_smul]
  rw [← phase_cz]
  ring_nf

theorem lowerKraus_measure_singleton_qIf [DecidableEq Var] [NeZero (2 ^ n)]
    (v : Var) (t : Wire n) {F : QProg Var (2 ^ n)} {R_F : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ}
    (hF : LowerKraus F R_F) :
    LowerKraus ((QProg.measureRegister v (QRegister.singleton t)).qSeq
        (.qIf (fun σ ↦ σ v = 1) F .skip))
      (sqrtHalf • ((QRegister.singleton t).basisOutcomeProjector 0 +
        R_F * (QRegister.singleton t).basisOutcomeProjector 1)) :=
  lowerKraus_measure_qIf v _ hF

/-- Phase correction `Z(c_1) ... Z(c_m)` followed by `X t` for single-wire BGL parity
uncomputation. -/
def fixupZ : List (Wire n) → Wire n → Circuit n
  | [], t => Circuit.X t
  | c :: cs, t => .seq (Circuit.Z c) (fixupZ cs t)

theorem count_T_fixupZ (sources : List (Wire n)) (t : Wire n) :
    (fixupZ sources t).count PrimitiveGate.T = 0 := by
  induction sources with
  | nil => simp [fixupZ]
  | cons _ _ ih => simp [fixupZ, ih]

theorem count_TOFF_fixupZ (sources : List (Wire n)) (t : Wire n) :
    (fixupZ sources t).count PrimitiveGate.TOFF = 0 := by
  induction sources with
  | nil => simp [fixupZ]
  | cons _ _ ih => simp [fixupZ, ih]

theorem bitSign_add (a b : ZMod 2) : bitSign (a + b) = bitSign a * bitSign b := by
  rcases bit_cases a with rfl | rfl <;> rcases bit_cases b with rfl | rfl <;>
    simp [bitSign, one_add_one_zmod2]

theorem fixupZ_mulVec_ket (sources : List (Wire n)) (t : Wire n) (β : BitAssignment n) :
    (fixupZ sources t).eval.1.mulVec (ket β) =
      bitSign ((sources.map β).sum) • ket (update β t (β t + 1)) := by
  induction sources with
  | nil =>
    simp only [fixupZ, List.map_nil, List.sum_nil, bitSign, ↓reduceIte, one_smul]
    exact ket_X t β
  | cons c cs ih =>
    simp only [fixupZ, eval_seq_mulVec, ket_Z, Matrix.mulVec_smul, ih, smul_smul,
      List.map_cons, List.sum_cons, bitSign_add]

/-- Phase correction `CZ(c₁, c₂)` (from `S`, `Z` and `CNOT`). -/
def fixupCZ (c₁ c₂ : Wire n) : Circuit n :=
  if h : c₁ ≠ c₂ then
    .seq (Circuit.S c₁) (.seq (Circuit.S c₂) (.seq (Circuit.CNOT c₁ c₂ h) (.seq (Circuit.S c₂)
      (.seq (Circuit.Z c₂) (Circuit.CNOT c₁ c₂ h)))))
  else
    .identity

theorem count_T_fixupCZ (c₁ c₂ : Wire n) :
    (fixupCZ c₁ c₂).count PrimitiveGate.T = 0 := by
  unfold fixupCZ; split_ifs <;> simp

theorem count_TOFF_fixupCZ (c₁ c₂ : Wire n) :
    (fixupCZ c₁ c₂).count PrimitiveGate.TOFF = 0 := by
  unfold fixupCZ; split_ifs <;> simp

theorem fixupCZ_mulVec_ket (c₁ c₂ : Wire n) (h₁₂ : c₁ ≠ c₂) (β : BitAssignment n) :
    (fixupCZ c₁ c₂).eval.1.mulVec (ket β) =
      bitSign (β c₁ * β c₂) • ket β := by
  have hβ : update (update β c₂ (β c₂ + β c₁)) c₂ (β c₂ + β c₁ + β c₁) = β := by
    rw [update_idem, add_assoc, CharTwo.add_self_eq_zero, add_zero, update_eq_self]
  simp only [fixupCZ, dite_eq_left h₁₂, eval_seq_mulVec, ket_S, ket_Z, ket_CNOT, Matrix.mulVec_smul,
    update_self, update_of_ne h₁₂, hβ, smul_smul]
  rw [← phase_cz]
  ring_nf

/-- Phase correction `CZ(p_1) ... CZ(p_k) Z(c_1) ... Z(c_m)` followed by `X t` for quadratic +
linear BGL uncomputation. -/
def fixupQuad : List (Wire n × Wire n) → List (Wire n) → Wire n → Circuit n
  | [], lins, t => fixupZ lins t
  | (c₁, c₂) :: qs, lins, t => .seq (fixupCZ c₁ c₂) (fixupQuad qs lins t)

theorem count_T_fixupQuad (quads : List (Wire n × Wire n)) (lins : List (Wire n)) (t : Wire n) :
    (fixupQuad quads lins t).count PrimitiveGate.T = 0 := by
  induction quads with
  | nil => exact count_T_fixupZ lins t
  | cons p qs ih => simp [fixupQuad, count_T_fixupCZ, ih]

theorem count_TOFF_fixupQuad (quads : List (Wire n × Wire n)) (lins : List (Wire n)) (t : Wire n) :
    (fixupQuad quads lins t).count PrimitiveGate.TOFF = 0 := by
  induction quads with
  | nil => exact count_TOFF_fixupZ lins t
  | cons p qs ih => simp [fixupQuad, count_TOFF_fixupCZ, ih]

theorem fixupQuad_mulVec_ket (quads : List (Wire n × Wire n)) (lins : List (Wire n)) (t : Wire n)
    (hneq : ∀ p ∈ quads, p.1 ≠ p.2) (β : BitAssignment n) :
    (fixupQuad quads lins t).eval.1.mulVec (ket β) =
      bitSign ((quads.map (fun p ↦ β p.1 * β p.2)).sum + (lins.map β).sum) •
        ket (update β t (β t + 1)) := by
  induction quads with
  | nil =>
    simp only [fixupQuad, List.map_nil, List.sum_nil, zero_add]
    exact fixupZ_mulVec_ket lins t β
  | cons p qs ih =>
    have hp : p.1 ≠ p.2 := hneq p (List.mem_cons_self ..)
    have hqs : ∀ q ∈ qs, q.1 ≠ q.2 := fun q hq ↦ hneq q (List.mem_cons_of_mem _ hq)
    simp only [fixupQuad, eval_seq_mulVec, fixupCZ_mulVec_ket p.1 p.2 hp, Matrix.mulVec_smul,
      ih hqs, smul_smul, List.map_cons, List.sum_cons, add_assoc, bitSign_add]


inductive Step (n : ℕ) : Type where
  | x (q : Wire n)
  | cnot (c t : Wire n)
  | and4t (c₁ c₂ t : Wire n)
  | rccx0 (c₁ c₂ t : Wire n)
  | rccx1 (c₁ c₂ t : Wire n)
  | unand (c₁ c₂ t : Wire n)
  | unxorList (sources : List (Wire n)) (t : Wire n)
  | unquad (quads : List (Wire n × Wire n)) (lins : List (Wire n)) (t : Wire n)


end ArcsinImpl

end QuantumComputation.Specs
