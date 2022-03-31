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
public import QuantumComputation.QuantumHoareLogic.CleanAncilla

/-!
# Cody Jones' 4-`T` Measurement-Assisted Toffoli and Temporary-AND Gadgets

Implements Cody Jones' 4-`T` measurement-assisted Toffoli construction
(*Low-overhead constructions for the fault-tolerant Toffoli gate*, Phys. Rev. A 87, 022328, 2013,
https://arxiv.org/abs/1212.5069, Fig. 1) and its 3-wire temporary-AND compute/uncompute halves:

- `Circuit.andCompute` / `DynamicCircuit.andCompute`: computes `c₁ ∧ c₂` into a clean `|0⟩` ancilla
  using `4` `T` gates (`0` `TOFF`).
- `DynamicCircuit.andUncompute`: uncomputes the temporary-AND wire back to `|0⟩` via Hadamard,
  measurement, and classically controlled `CZ` fixup (`0` `T`, `0` `TOFF`).
- `DynamicCircuit.jonesToffoli`: `andCompute ;; CNOT ;; andUncompute` on 4 distinct wires, realizing
  `TOFF` with `4` `T` gates (`0` `TOFF`) and restoring the ancilla wire to `|0⟩` for reuse.
-/

@[expose] public section

open Operator Matrix QProg HermitianMat
open scoped Matrix ComplexOrder MatrixOrder Circuit.Notation
open CQAssertion (restrictToZeroAncilla restrictToZeroAncilla_coe)

namespace Circuit

variable {n : ℕ}

/-- 3-wire unitary circuit computing the logical AND of `control₁` and `control₂` into a
clean `|0⟩` wire `ancilla` using `4` `T` gates (`T` and `T†` each twice). -/
def andCompute (control₁ control₂ ancilla : Wire n)
    (h₁a : control₁ ≠ ancilla) (h₂a : control₂ ≠ ancilla) :
    Circuit n :=
  Circuit.H ancilla ;;ᶜ
  Circuit.T ancilla ;;ᶜ
  Circuit.CNOT control₂ ancilla h₂a ;;ᶜ
  (Circuit.T ancilla).inverse ;;ᶜ
  Circuit.CNOT control₁ ancilla h₁a ;;ᶜ
  Circuit.T ancilla ;;ᶜ
  Circuit.CNOT control₂ ancilla h₂a ;;ᶜ
  (Circuit.T ancilla).inverse ;;ᶜ
  Circuit.CNOT control₁ ancilla h₁a ;;ᶜ
  Circuit.H ancilla ;;ᶜ
  Circuit.S ancilla

/-- 3-wire fixup circuit for measurement outcome `1` in `andUncompute`: resets `ancilla` to
`|0⟩` with `X ancilla` and applies `CZ` (`H · CNOT · H`) on `(control₁, control₂)`. -/
def andUncomputeFixup (control₁ control₂ ancilla : Wire n) (h₁₂ : control₁ ≠ control₂) :
    Circuit n :=
  Circuit.X ancilla ;;ᶜ
  Circuit.H control₂ ;;ᶜ
  Circuit.CNOT control₁ control₂ h₁₂ ;;ᶜ
  Circuit.H control₂

@[simp]
theorem support_andCompute (control₁ control₂ ancilla : Wire n)
    (h₁a : control₁ ≠ ancilla) (h₂a : control₂ ≠ ancilla) :
    (andCompute control₁ control₂ ancilla h₁a h₂a).support = {control₁, control₂, ancilla} := by
  ext q
  simp only [andCompute, support_seq, support_inverse, support_single, support_cnot,
    Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
  tauto

end Circuit

namespace DynamicCircuit

variable {Var : Type} {n : ℕ}

/-- Compute the logical AND of `control₁` and `control₂` into a clean `|0⟩` wire `ancilla` using
`4` `T` gates and `0` `TOFF` gates. -/
def andCompute (control₁ control₂ ancilla : Wire n)
    (h₁a : control₁ ≠ ancilla) (h₂a : control₂ ≠ ancilla) :
    DynamicCircuit Var n :=
  .circuit (Circuit.andCompute control₁ control₂ ancilla h₁a h₂a)

/-- Uncompute a temporary-AND wire `ancilla` (holding `control₁ ∧ control₂`) back to `|0⟩` using
`0` `T` gates via Hadamard, computational-basis measurement into `v`, and conditional `X`/`CZ`
fixup. -/
def andUncompute (v : Var) (control₁ control₂ ancilla : Wire n)
    (h₁₂ : control₁ ≠ control₂) :
    DynamicCircuit Var n :=
  .seq (.circuit (Circuit.H ancilla))
    (.seq (.measure v (QRegister.singleton ancilla))
      (.qIf (fun σ ↦ σ v = 1)
        (.circuit (Circuit.andUncomputeFixup control₁ control₂ ancilla h₁₂))
        .identity))

/-- Cody Jones' 4-`T` measurement-assisted Toffoli construction
(Phys. Rev. A 87, 022328, 2013; https://arxiv.org/abs/1212.5069, Fig. 1).

When `ancilla` is initialized in `|0⟩` on pairwise-distinct physical wires
`(control₁, control₂, target, ancilla)`, this dynamic circuit realizes `Circuit.TOFF` on
`(control₁, control₂, target)` and returns `ancilla` to `|0⟩` using `4` `T` gates and `0`
`TOFF` gates, allowing the same `ancilla` wire to be reused across sequential Toffoli gates. -/
def jonesToffoli (v : Var) (control₁ control₂ target ancilla : Wire n)
    (h₁₂ : control₁ ≠ control₂)
    (h₁a : control₁ ≠ ancilla) (h₂a : control₂ ≠ ancilla) (hta : target ≠ ancilla) :
    DynamicCircuit Var n :=
  .seq (andCompute control₁ control₂ ancilla h₁a h₂a)
    (.seq (.circuit (Circuit.CNOT ancilla target hta.symm))
      (andUncompute v control₁ control₂ ancilla h₁₂))

@[simp]
theorem support_andCompute (control₁ control₂ ancilla : Wire n)
    (h₁a : control₁ ≠ ancilla) (h₂a : control₂ ≠ ancilla) :
    (andCompute (Var := Var) control₁ control₂ ancilla h₁a h₂a).support =
      {control₁, control₂, ancilla} :=
  Circuit.support_andCompute control₁ control₂ ancilla h₁a h₂a

@[simp]
theorem support_andUncompute (v : Var) (control₁ control₂ ancilla : Wire n)
    (h₁₂ : control₁ ≠ control₂) :
    (andUncompute v control₁ control₂ ancilla h₁₂).support =
      {control₁, control₂, ancilla} := by
  ext q
  simp only [andUncompute, Circuit.andUncomputeFixup, support_seq, support_circuit,
    support_measure, support_qIf, Circuit.support_seq, Circuit.support_single,
    Circuit.support_cnot, Circuit.support_identity, QRegister.image_singleton,
    Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
  tauto

/-- `jonesToffoli` syntactically touches the wires `{control₁, control₂, target, ancilla}`. -/
@[simp]
theorem support_jonesToffoli (v : Var) (control₁ control₂ target ancilla : Wire n)
    (h₁₂ : control₁ ≠ control₂)
    (h₁a : control₁ ≠ ancilla) (h₂a : control₂ ≠ ancilla) (hta : target ≠ ancilla) :
    (jonesToffoli v control₁ control₂ target ancilla h₁₂ h₁a h₂a hta).support =
      {control₁, control₂, target, ancilla} := by
  ext q
  simp only [jonesToffoli, support_seq, support_andCompute, support_circuit,
    Circuit.support_cnot, support_andUncompute,
    Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
  tauto

/-- `jonesToffoli` has support of cardinality `4`, witnessing that it genuinely acts on 4
distinct qubits. -/
theorem card_support_jonesToffoli (v : Var) (control₁ control₂ target ancilla : Wire n)
    (h₁₂ : control₁ ≠ control₂) (h₁t : control₁ ≠ target) (h₂t : control₂ ≠ target)
    (h₁a : control₁ ≠ ancilla) (h₂a : control₂ ≠ ancilla) (hta : target ≠ ancilla) :
    (jonesToffoli v control₁ control₂ target ancilla h₁₂ h₁a h₂a hta).support.card = 4 := by
  simp [h₁₂, h₁t, h₂t, h₁a, h₂a, hta]

variable [DecidableEq Var]

/-!
### Basis-ket evaluation helpers
-/

private noncomputable abbrev ket (β : BitAssignment n) : Fin (2 ^ n) → ℂ :=
  basisState ((basisBits n).symm β)

private theorem single_eq_ket (g : Fin (2 ^ n)) :
    (Pi.single g 1 : Fin (2 ^ n) → ℂ) = ket (basisBits n g) := by
  simp [ket, basisState]

private theorem matrix_ext_ket {A B : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ}
    (h : ∀ β, A *ᵥ ket β = B *ᵥ ket β) : A = B := by
  ext i j
  have := congrFun (h (basisBits n j)) i
  simpa [← single_eq_ket, Matrix.mulVec_single_one] using this

private noncomputable def writeReg {k : ℕ} (β : BitAssignment n) (r : QRegister k n)
    (γ : BitAssignment k) : BitAssignment n :=
  basisBits n (r.replaceIndex ((basisBits n).symm β) ((basisBits k).symm γ))

@[simp]
private theorem writeReg_apply_reg {k : ℕ} (β : BitAssignment n) (r : QRegister k n)
    (γ : BitAssignment k) (i : Fin k) : writeReg β r γ (r i) = γ i := by
  simp [writeReg, QRegister.basisBits_replaceIndex_apply]

private theorem writeReg_apply_of_not_mem {k : ℕ} (β : BitAssignment n) (r : QRegister k n)
    (γ : BitAssignment k) (w : Wire n) (hw : w ∉ Set.range r.wires) :
    writeReg β r γ w = β w := by
  simp [writeReg, QRegister.basisBits_replaceIndex_of_not_mem _ _ _ _ hw]

private theorem writeReg_eq_update {k : ℕ} (β : BitAssignment n) (r : QRegister k n)
    (γ : BitAssignment k) (i₀ : Fin k) (hγ : ∀ i, i ≠ i₀ → γ i = β (r i)) :
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

private noncomputable abbrev localIdx {k : ℕ} (r : QRegister k n) (β : BitAssignment n) :
    Fin (2 ^ k) :=
  (basisBits k).symm (fun i ↦ β (r i))

private theorem embedMatrix_mulVec_ket {k : ℕ} (r : QRegister k n)
    (A : Matrix (Fin (2 ^ k)) (Fin (2 ^ k)) ℂ) (β : BitAssignment n) :
    r.embedMatrix A *ᵥ ket β =
      ∑ l : Fin (2 ^ k), A l (localIdx r β) • ket (writeReg β r (basisBits k l)) := by
  have hext : r.extractIndex ((basisBits n).symm β) = localIdx r β := by
    simp [QRegister.extractIndex]
  have hcol (j : Fin (2 ^ k)) :
      A *ᵥ Pi.single j 1 = ∑ l : Fin (2 ^ k), A l j • Pi.single l 1 := by
    funext x
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  rw [ket, basisState, r.embedMatrix_mulVec_single_factors, hext, hcol,
    QRegister.tensorState_sum_left]
  refine Finset.sum_congr rfl fun l _ ↦ ?_
  rw [QRegister.tensorState_smul_left, QRegister.tensorState_single_replaceIndex]
  simp [writeReg, ket, basisState]

private theorem embedMatrix_permMatrix_mulVec_ket {k : ℕ} (r : QRegister k n)
    (σ : Equiv.Perm (Fin (2 ^ k))) (β : BitAssignment n) :
    r.embedMatrix (σ.permMatrix ℂ) *ᵥ ket β =
      ket (writeReg β r (basisBits k (σ.symm (localIdx r β)))) := by
  rw [embedMatrix_mulVec_ket, Finset.sum_eq_single (σ.symm (localIdx r β))]
  · simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]
  · intro l _ hl
    have : σ l ≠ localIdx r β := fun h ↦ hl (by rw [← h, Equiv.symm_apply_apply])
    simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, this]
  · simp

private theorem singleton_embedMatrix_mulVec_ket (q : Wire n) (A : Matrix (Fin 2) (Fin 2) ℂ)
    (β : BitAssignment n) :
    (QRegister.singleton q).embedMatrix A *ᵥ ket β =
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

private abbrev bitSign (b : ZMod 2) : ℂ := if b = 0 then 1 else -1

private abbrev bitPhaseI (b : ZMod 2) : ℂ := if b = 0 then 1 else Complex.I

private noncomputable def omega8 : ℂ := (1 + Complex.I) / (√2 : ℂ)

private noncomputable abbrev bitPhaseT (b : ZMod 2) : ℂ := if b = 0 then 1 else omega8

private noncomputable abbrev bitPhaseTInv (b : ZMod 2) : ℂ :=
  bitSign b * bitPhaseI b * bitPhaseT b

private noncomputable def sqrtHalf : ℂ := √(1 / 2)

private theorem sqrtHalf_mul_sqrtHalf : sqrtHalf * sqrtHalf = 1 / 2 := by
  dsimp [sqrtHalf]
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
  push_cast
  ring

private theorem sqrtHalf_sq : sqrtHalf ^ 2 = 1 / 2 := by
  linear_combination sqrtHalf_mul_sqrtHalf

private theorem star_sqrtHalf : star sqrtHalf = sqrtHalf := by
  dsimp [sqrtHalf]
  exact Complex.conj_ofReal _

private theorem omega8_mul_omega8 : omega8 * omega8 = Complex.I := by
  dsimp [omega8]
  have h2 : (√2 : ℂ) * (√2 : ℂ) = 2 := by
    exact_mod_cast Real.mul_self_sqrt (by norm_num)
  calc ((1 + Complex.I) / (√2 : ℂ)) * ((1 + Complex.I) / (√2 : ℂ))
      = (1 + 2 * Complex.I + Complex.I * Complex.I) /
          ((√2 : ℂ) * (√2 : ℂ)) := by ring
    _ = Complex.I := by rw [Complex.I_mul_I, h2]; ring

private theorem omega8_sq : omega8 ^ 2 = Complex.I := by
  linear_combination omega8_mul_omega8

private theorem omega8_pow_four : omega8 ^ 4 = -1 := by
  linear_combination (omega8 ^ 2 + Complex.I) * omega8_mul_omega8 + Complex.I_mul_I

private theorem bit_cases (b : ZMod 2) : b = 0 ∨ b = 1 := by
  fin_cases b
  · exact Or.inl rfl
  · exact Or.inr rfl

private theorem one_add_one_zmod2 : (1 : ZMod 2) + 1 = 0 := rfl

private theorem eval_seq_mulVec (c₁ c₂ : Circuit n) (ψ : Fin (2 ^ n) → ℂ) :
    (Circuit.seq c₁ c₂).eval.1 *ᵥ ψ = c₂.eval.1 *ᵥ c₁.eval.1 *ᵥ ψ := by
  rw [Circuit.eval_seq, Matrix.mulVec_mulVec]
  rfl

private theorem ket_X (q : Wire n) (β : BitAssignment n) :
    (Circuit.X q).eval.1 *ᵥ ket β = ket (Function.update β q (β q + 1)) := by
  rw [Circuit.eval_single, QRegister.embedUnitary_val, PrimitiveGate.eval]
  change (QRegister.singleton q).embedMatrix !![0, 1; 1, 0] *ᵥ _ = _
  rw [singleton_embedMatrix_mulVec_ket]
  rcases bit_cases (β q) with hb | hb <;> simp [hb, one_add_one_zmod2]

private theorem ket_Z (q : Wire n) (β : BitAssignment n) :
    (Circuit.Z q).eval.1 *ᵥ ket β = bitSign (β q) • ket β := by
  rw [Circuit.eval_single, QRegister.embedUnitary_val, PrimitiveGate.eval]
  change (QRegister.singleton q).embedMatrix !![1, 0; 0, -1] *ᵥ _ = _
  rw [singleton_embedMatrix_mulVec_ket]
  have e := Function.update_eq_self q β
  rcases bit_cases (β q) with hb | hb <;> rw [hb] at e <;> simp [hb, e]

private theorem ket_S (q : Wire n) (β : BitAssignment n) :
    (Circuit.S q).eval.1 *ᵥ ket β = bitPhaseI (β q) • ket β := by
  rw [Circuit.eval_single, QRegister.embedUnitary_val, PrimitiveGate.eval]
  change (QRegister.singleton q).embedMatrix !![1, 0; 0, Complex.I] *ᵥ _ = _
  rw [singleton_embedMatrix_mulVec_ket]
  have e := Function.update_eq_self q β
  rcases bit_cases (β q) with hb | hb <;> rw [hb] at e <;> simp [hb, e]

private theorem ket_T (q : Wire n) (β : BitAssignment n) :
    (Circuit.T q).eval.1 *ᵥ ket β = bitPhaseT (β q) • ket β := by
  rw [Circuit.eval_single, QRegister.embedUnitary_val, PrimitiveGate.eval]
  change (QRegister.singleton q).embedMatrix !![1, 0; 0, omega8] *ᵥ _ = _
  rw [singleton_embedMatrix_mulVec_ket]
  have e := Function.update_eq_self q β
  rcases bit_cases (β q) with hb | hb <;> rw [hb] at e <;> simp [hb, e]

private theorem ket_T_inv (q : Wire n) (β : BitAssignment n) :
    (Circuit.T q).inverse.eval.1 *ᵥ ket β = bitPhaseTInv (β q) • ket β := by
  change (Circuit.T q ;;ᶜ (Circuit.S q ;;ᶜ (Circuit.Z q ;;ᶜ .identity))).eval.1 *ᵥ ket β = _
  simp only [eval_seq_mulVec, Circuit.eval_identity, Submonoid.coe_one, Matrix.one_mulVec,
    ket_T, ket_S, ket_Z, Matrix.mulVec_smul, smul_smul, bitPhaseTInv]
  congr 1
  ring

private theorem ket_H (q : Wire n) (β : BitAssignment n) :
    (Circuit.H q).eval.1 *ᵥ ket β =
      sqrtHalf • (ket (Function.update β q 0) +
        bitSign (β q) • ket (Function.update β q 1)) := by
  rw [Circuit.eval_single, QRegister.embedUnitary_val, PrimitiveGate.eval]
  change (QRegister.singleton q).embedMatrix
    (√(1 / 2) • !![(1 : ℂ), 1; 1, -1]) *ᵥ _ = _
  rw [singleton_embedMatrix_mulVec_ket]
  rcases bit_cases (β q) with hb | hb <;> simp [hb, sqrtHalf, smul_add, Complex.real_smul]

private theorem ket_CNOT (c t : Wire n) (h : c ≠ t) (β : BitAssignment n) :
    (Circuit.CNOT c t h).eval.1 *ᵥ ket β = ket (Function.update β t (β t + β c)) := by
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

private theorem ket_TOFF (c₁ c₂ t : Wire n) (h₁₂ : c₁ ≠ c₂) (h₁t : c₁ ≠ t) (h₂t : c₂ ≠ t)
    (β : BitAssignment n) :
    (Circuit.TOFF c₁ c₂ t h₁₂ h₁t h₂t).eval.1 *ᵥ ket β =
      ket (Function.update β t (β t + β c₁ * β c₂)) := by
  rw [Circuit.eval_gate, QRegister.embedUnitary_val, PrimitiveGate.eval_toffoli_val,
    embedMatrix_permMatrix_mulVec_ket]
  have hloc : ∀ γ : BitAssignment 3,
      basisBits 3 ((Equiv.swap (3 : Fin 8) 7).symm ((basisBits 3).symm γ)) =
        Function.update γ 2 (γ 2 + γ 0 * γ 1) := by decide
  rw [localIdx, hloc, writeReg_eq_update _ _ _ 2]
  · simp
  · intro i hi
    fin_cases i
    · simp
    · simp
    · exact absurd rfl hi

private theorem ket_projector (q : Wire n) (o : Fin 2) (β : BitAssignment n) :
    (QRegister.singleton q).basisOutcomeProjector o *ᵥ ket β =
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

private theorem ket_projector_zero (q : Wire n) (β : BitAssignment n) :
    (QRegister.singleton q).basisOutcomeProjector 0 *ᵥ ket β =
      if β q = 0 then ket β else 0 :=
  ket_projector q 0 β

private theorem ket_projector_one (q : Wire n) (β : BitAssignment n) :
    (QRegister.singleton q).basisOutcomeProjector 1 *ᵥ ket β =
      if β q = 1 then ket β else 0 :=
  ket_projector q 1 β

private noncomputable def phase4T (c₁ c₂ a : ZMod 2) : ℂ :=
  bitPhaseT (a + c₂ + c₁) * bitPhaseTInv (a + c₂) * bitPhaseT a * bitPhaseTInv (a + c₁)

private theorem phase4T_eq (c₁ c₂ a : ZMod 2) :
    phase4T c₁ c₂ a =
      if c₁ * c₂ = 0 then 1 else if a = 0 then -Complex.I else Complex.I := by
  rcases bit_cases c₁ with rfl | rfl <;>
    rcases bit_cases c₂ with rfl | rfl <;>
    rcases bit_cases a with rfl | rfl <;>
    simp only [phase4T, bitPhaseT, bitPhaseTInv, bitSign, bitPhaseI,
      one_add_one_zmod2, add_zero, zero_add, mul_zero, mul_one,
      one_ne_zero, ↓reduceIte] <;>
    (ring_nf; simp only [omega8_sq, omega8_pow_four, Complex.I_sq, Complex.I_mul_I]; try ring1)

private theorem tempAnd_Combine (c₁ c₂ : ZMod 2) (ψ₀ ψ₁ : Fin (2 ^ n) → ℂ) :
    sqrtHalf •
        (phase4T c₁ c₂ 0 • (sqrtHalf • (ψ₀ + bitPhaseI 1 • ψ₁)) +
          phase4T c₁ c₂ 1 • (sqrtHalf • (ψ₀ + bitSign 1 • bitPhaseI 1 • ψ₁))) =
      if c₁ * c₂ = 0 then ψ₀ else ψ₁ := by
  rw [phase4T_eq c₁ c₂ 0, phase4T_eq c₁ c₂ 1]
  rcases bit_cases (c₁ * c₂) with h | h <;>
    simp only [h, bitPhaseI, bitSign, one_ne_zero, ↓reduceIte,
      smul_add, smul_smul] <;>
    match_scalars <;>
    first
      | ring1
      | (ring_nf; simp only [sqrtHalf_sq, Complex.I_sq]; ring1)

private theorem cz_Combine (c₁ c₂ : ZMod 2) (ψ₀ ψ₁ : Fin (2 ^ n) → ℂ) :
    sqrtHalf •
        (sqrtHalf • (ψ₀ + bitSign c₁ • ψ₁) +
          bitSign c₂ • (sqrtHalf • (ψ₀ + bitSign (1 + c₁) • ψ₁))) =
      bitSign (c₁ * c₂) • (if c₂ = 0 then ψ₀ else ψ₁) := by
  rcases bit_cases c₁ with rfl | rfl <;>
    rcases bit_cases c₂ with rfl | rfl <;>
    simp only [bitSign, one_add_one_zmod2, add_zero, mul_zero, mul_one,
      one_ne_zero, ↓reduceIte, smul_add, smul_smul] <;>
    match_scalars <;>
    first
      | ring1
      | (ring_nf; simp only [sqrtHalf_sq]; ring1)

private theorem jonesPhaseStep_mulVec_ket
    (c₁ c₂ anc : Wire n) (h₁a : c₁ ≠ anc) (h₂a : c₂ ≠ anc)
    (rest : Circuit n) (β : BitAssignment n) :
    (Circuit.T anc ;;ᶜ
      Circuit.CNOT c₂ anc h₂a ;;ᶜ
      (Circuit.T anc).inverse ;;ᶜ
      Circuit.CNOT c₁ anc h₁a ;;ᶜ
      Circuit.T anc ;;ᶜ
      Circuit.CNOT c₂ anc h₂a ;;ᶜ
      (Circuit.T anc).inverse ;;ᶜ
      Circuit.CNOT c₁ anc h₁a ;;ᶜ
      rest).eval.1 *ᵥ ket β =
      phase4T (β c₁) (β c₂) (β anc) • rest.eval.1 *ᵥ ket β := by
  have hadd1 (x y : ZMod 2) : x + y + y = x := by
    rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
  have hadd2 (x y z : ZMod 2) : x + y + z + y = x + z := by
    calc x + y + z + y = x + z + (y + y) := by ring
      _ = x + z := by rw [CharTwo.add_self_eq_zero, add_zero]
  simp only [eval_seq_mulVec, ket_T, ket_T_inv, ket_CNOT, Matrix.mulVec_smul,
    Function.update_self, Function.update_of_ne h₁a, Function.update_of_ne h₂a,
    Function.update_idem, hadd2, hadd1, Function.update_eq_self, smul_smul]
  congr 1
  rw [phase4T]
  ring

private theorem andCompute_mulVec_ket_of_zero
    (control₁ control₂ ancilla : Wire n)
    (h₁a : control₁ ≠ ancilla) (h₂a : control₂ ≠ ancilla)
    (β : BitAssignment n) (hanc : β ancilla = 0) :
    (Circuit.andCompute control₁ control₂ ancilla h₁a h₂a).eval.1 *ᵥ ket β =
      ket (Function.update β ancilla (β control₁ * β control₂)) := by
  have hanc_sign : bitSign (β ancilla) = 1 := by simp [hanc, bitSign]
  rw [Circuit.andCompute, eval_seq_mulVec, ket_H, hanc_sign, one_smul]
  simp only [Matrix.mulVec_smul, Matrix.mulVec_add,
    jonesPhaseStep_mulVec_ket, Function.update_self,
    Function.update_of_ne h₁a, Function.update_of_ne h₂a]
  simp only [eval_seq_mulVec, ket_H, Function.update_self, Function.update_idem,
    Matrix.mulVec_smul, Matrix.mulVec_add, ket_S]
  have h0 : bitPhaseI 0 = 1 := rfl
  have hs0 : bitSign 0 = 1 := rfl
  rw [h0, hs0, one_smul, one_smul, tempAnd_Combine]
  rcases bit_cases (β control₁ * β control₂) with h | h <;> simp [h]

private theorem andUncomputeFixup_mulVec_ket
    (control₁ control₂ ancilla : Wire n)
    (h₁₂ : control₁ ≠ control₂) (h₁a : control₁ ≠ ancilla) (h₂a : control₂ ≠ ancilla)
    (β : BitAssignment n) :
    (Circuit.andUncomputeFixup control₁ control₂ ancilla h₁₂).eval.1 *ᵥ ket β =
      bitSign (β control₁ * β control₂) •
        ket (Function.update β ancilla (β ancilla + 1)) := by
  rw [Circuit.andUncomputeFixup]
  let γ := Function.update β ancilla (β ancilla + 1)
  have hX : (Circuit.X ancilla).eval.1 *ᵥ ket β = ket γ := ket_X ancilla β
  simp only [eval_seq_mulVec, hX, ket_H, Matrix.mulVec_smul, Matrix.mulVec_add,
    ket_CNOT, Function.update_self, Function.update_of_ne h₁₂, Function.update_idem, zero_add]
  have hγ₁ : γ control₁ = β control₁ := Function.update_of_ne h₁a _ _
  have hγ₂ : γ control₂ = β control₂ := Function.update_of_ne h₂a _ _
  rw [hγ₁, hγ₂, cz_Combine (β control₁) (β control₂)]
  have hγ_upd : (if β control₂ = 0 then ket (Function.update γ control₂ 0)
      else ket (Function.update γ control₂ 1)) = ket γ := by
    have e := Function.update_eq_self control₂ γ
    rw [hγ₂] at e
    rcases bit_cases (β control₂) with h₂ | h₂ <;> rw [h₂] at e ⊢ <;> simp [e]
  rw [hγ_upd]

/-!
### General clean-ancilla and `CQAssertion.qAssign` helpers
-/

/-- `Circuit.TOFF control₁ control₂ target` commutes with the clean-ancilla projector on
`ancilla`, since `ancilla` is disjoint from `{control₁, control₂, target}`. -/
private theorem toffoli_comm_ancilla_projector
    (control₁ control₂ target ancilla : Wire n)
    (h₁₂ : control₁ ≠ control₂) (h₁t : control₁ ≠ target) (h₂t : control₂ ≠ target)
    (hta : target ≠ ancilla) :
    let P₀ := (QRegister.singleton ancilla).basisOutcomeProjector 0
    (Circuit.TOFF control₁ control₂ target h₁₂ h₁t h₂t).eval.1 * P₀ =
      P₀ * (Circuit.TOFF control₁ control₂ target h₁₂ h₁t h₂t).eval.1 := by
  intro P₀
  apply matrix_ext_ket
  intro β
  by_cases hanc : β ancilla = 0 <;>
    simp only [P₀, ← Matrix.mulVec_mulVec, ket_TOFF, ket_projector_zero,
      Function.update_of_ne hta.symm, hanc, ↓reduceIte, Matrix.mulVec_zero]

private theorem toffoli_eval_mul_self
    (control₁ control₂ target : Wire n)
    (h₁₂ : control₁ ≠ control₂) (h₁t : control₁ ≠ target) (h₂t : control₂ ≠ target) :
    (Circuit.TOFF control₁ control₂ target h₁₂ h₁t h₂t).eval *
      (Circuit.TOFF control₁ control₂ target h₁₂ h₁t h₂t).eval = 1 := by
  apply Subtype.ext
  apply matrix_ext_ket
  intro β
  simp only [Submonoid.coe_mul, Submonoid.coe_one, ← Matrix.mulVec_mulVec, Matrix.one_mulVec,
    ket_TOFF, Function.update_self, Function.update_of_ne h₁t, Function.update_of_ne h₂t,
    Function.update_idem]
  have hadd : β target + β control₁ * β control₂ + β control₁ * β control₂ = β target := by
    rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
  rw [hadd, Function.update_eq_self]

private theorem toffoli_eval_conjTranspose
    (control₁ control₂ target : Wire n)
    (h₁₂ : control₁ ≠ control₂) (h₁t : control₁ ≠ target) (h₂t : control₂ ≠ target) :
    (Circuit.TOFF control₁ control₂ target h₁₂ h₁t h₂t).eval.1ᴴ =
      (Circuit.TOFF control₁ control₂ target h₁₂ h₁t h₂t).eval.1 := by
  let U := (Circuit.TOFF control₁ control₂ target h₁₂ h₁t h₂t).eval
  have hsq : U.1 * U.1 = 1 :=
    congrArg Subtype.val (toffoli_eval_mul_self control₁ control₂ target h₁₂ h₁t h₂t)
  have hunit : U.1ᴴ * U.1 = 1 := congrArg Subtype.val (Unitary.star_mul_self U)
  calc U.1ᴴ = U.1ᴴ * (U.1 * U.1) := by rw [hsq, Matrix.mul_one]
    _ = (U.1ᴴ * U.1) * U.1 := by rw [← Matrix.mul_assoc]
    _ = U.1 := by rw [hunit, Matrix.one_mul]

private theorem cnot_eval_mul_self (control target : Wire n) (h : control ≠ target) :
    (Circuit.CNOT control target h).eval * (Circuit.CNOT control target h).eval = 1 := by
  apply Subtype.ext
  apply matrix_ext_ket
  intro β
  simp only [Submonoid.coe_mul, Submonoid.coe_one, ← Matrix.mulVec_mulVec, Matrix.one_mulVec,
    ket_CNOT, Function.update_self, Function.update_of_ne h, Function.update_idem]
  have hadd : β target + β control + β control = β target := by
    rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
  rw [hadd, Function.update_eq_self]

private theorem cnot_eval_conjTranspose (control target : Wire n) (h : control ≠ target) :
    (Circuit.CNOT control target h).eval.1ᴴ = (Circuit.CNOT control target h).eval.1 := by
  let U := (Circuit.CNOT control target h).eval
  have hsq : U.1 * U.1 = 1 := congrArg Subtype.val (cnot_eval_mul_self control target h)
  have hunit : U.1ᴴ * U.1 = 1 := congrArg Subtype.val (Unitary.star_mul_self U)
  calc U.1ᴴ = U.1ᴴ * (U.1 * U.1) := by rw [hsq, Matrix.mul_one]
    _ = (U.1ᴴ * U.1) * U.1 := by rw [← Matrix.mul_assoc]
    _ = U.1 := by rw [hunit, Matrix.one_mul]

/-- Weakest precondition of a compiled `Circuit` equals `CQAssertion.qAssign` of its unitary
evaluation on any classical-quantum assertion `Θ`. -/
@[simp]
theorem wp_circuit_compile (c : Circuit n)
    (Θ : CQAssertion (Store Var) (2 ^ n)) :
    wp c.compile Θ = Θ.qAssign c.eval := by
  induction c generalizing Θ with
  | identity =>
      simp [Circuit.compile]
  | gate g r => rfl
  | seq c₁ c₂ ih₁ ih₂ =>
      simp [Circuit.compile, ih₁, ih₂]

/-!
### Temporary-AND computation (`andCompute`)
-/

private theorem andCompute_eval_mul_projector_zero
    (control₁ control₂ ancilla : Wire n)
    (h₁₂ : control₁ ≠ control₂) (h₁a : control₁ ≠ ancilla) (h₂a : control₂ ≠ ancilla) :
    let P₀ := (QRegister.singleton ancilla).basisOutcomeProjector 0
    (Circuit.andCompute control₁ control₂ ancilla h₁a h₂a).eval.1 * P₀ =
      (Circuit.TOFF control₁ control₂ ancilla h₁₂ h₁a h₂a).eval.1 * P₀ := by
  intro P₀
  apply matrix_ext_ket
  intro β
  simp only [P₀, ← Matrix.mulVec_mulVec, ket_projector_zero]
  by_cases hanc : β ancilla = 0
  · simp only [hanc, ↓reduceIte,
      andCompute_mulVec_ket_of_zero control₁ control₂ ancilla h₁a h₂a β hanc,
      ket_TOFF, zero_add]
  · simp [hanc]

private theorem projector_zero_mul_toffoli_mul_andCompute
    (control₁ control₂ ancilla : Wire n)
    (h₁₂ : control₁ ≠ control₂) (h₁a : control₁ ≠ ancilla) (h₂a : control₂ ≠ ancilla) :
    let P₀ := (QRegister.singleton ancilla).basisOutcomeProjector 0
    P₀ * (Circuit.TOFF control₁ control₂ ancilla h₁₂ h₁a h₂a).eval.1 *
      (Circuit.andCompute control₁ control₂ ancilla h₁a h₂a).eval.1 = P₀ := by
  intro P₀
  let C_and := (Circuit.andCompute control₁ control₂ ancilla h₁a h₂a).eval
  let T_anc := (Circuit.TOFF control₁ control₂ ancilla h₁₂ h₁a h₂a).eval
  have hP₀_herm : P₀ᴴ = P₀ := QRegister.basisOutcomeProjector_conjTranspose _ 0
  have hT_herm : T_anc.1ᴴ = T_anc.1 :=
    toffoli_eval_conjTranspose control₁ control₂ ancilla h₁₂ h₁a h₂a
  have hadj : P₀ * T_anc.1 = P₀ * C_and.1ᴴ := by
    have h : (C_and.1 * P₀)ᴴ = (T_anc.1 * P₀)ᴴ :=
      congrArg conjTranspose
        (andCompute_eval_mul_projector_zero control₁ control₂ ancilla h₁₂ h₁a h₂a)
    rw [conjTranspose_mul, conjTranspose_mul, hP₀_herm, hT_herm] at h
    exact h.symm
  have hunit : C_and.1ᴴ * C_and.1 = 1 := congrArg Subtype.val (Unitary.star_mul_self C_and)
  calc P₀ * T_anc.1 * C_and.1 = (P₀ * C_and.1ᴴ) * C_and.1 := by rw [hadj]
    _ = P₀ * (C_and.1ᴴ * C_and.1) := by rw [Matrix.mul_assoc]
    _ = P₀ := by rw [hunit, Matrix.mul_one]

/-- On a clean `|0⟩` wire `ancilla`, `CQAssertion.qAssign` of `Circuit.andCompute` equals
`CQAssertion.qAssign` of `Circuit.TOFF` for any postcondition `Θ`. -/
theorem restrictToZeroAncilla_qAssign_andCompute {State : Type*}
    (control₁ control₂ ancilla : Wire n)
    (h₁₂ : control₁ ≠ control₂) (h₁a : control₁ ≠ ancilla) (h₂a : control₂ ≠ ancilla)
    (Θ : CQAssertion State (2 ^ n)) :
    restrictToZeroAncilla
      (Θ.qAssign (Circuit.andCompute control₁ control₂ ancilla h₁a h₂a).eval)
      (QRegister.singleton ancilla) =
    restrictToZeroAncilla
      (Θ.qAssign (Circuit.TOFF control₁ control₂ ancilla h₁₂ h₁a h₂a).eval)
      (QRegister.singleton ancilla) := by
  funext σ
  apply Subtype.ext
  let P₀ := (QRegister.singleton ancilla).basisOutcomeProjector 0
  have hP₀_herm : P₀ᴴ = P₀ := QRegister.basisOutcomeProjector_conjTranspose _ 0
  have hand' : P₀ * (Circuit.andCompute control₁ control₂ ancilla h₁a h₂a).eval.1ᴴ =
      P₀ * (Circuit.TOFF control₁ control₂ ancilla h₁₂ h₁a h₂a).eval.1ᴴ := by
    have h : ((Circuit.andCompute control₁ control₂ ancilla h₁a h₂a).eval.1 * P₀)ᴴ =
        ((Circuit.TOFF control₁ control₂ ancilla h₁₂ h₁a h₂a).eval.1 * P₀)ᴴ :=
      congrArg conjTranspose
        (andCompute_eval_mul_projector_zero control₁ control₂ ancilla h₁₂ h₁a h₂a)
    rw [conjTranspose_mul, conjTranspose_mul, hP₀_herm] at h
    exact h
  simp only [restrictToZeroAncilla_coe, CQAssertion.qAssign_apply,
    Observable.conj_coe, Unitary.coe_star, Matrix.star_eq_conjTranspose, conj_conj]
  rw [hand']

private theorem qAssign_andCompute_qAssign_toffoli_clean {State : Type*}
    (control₁ control₂ ancilla : Wire n)
    (h₁₂ : control₁ ≠ control₂) (h₁a : control₁ ≠ ancilla) (h₂a : control₂ ≠ ancilla)
    (Θ : CQAssertion State (2 ^ n)) :
    ((Θ.restrictToZeroAncilla (QRegister.singleton ancilla)).qAssign
      (Circuit.TOFF control₁ control₂ ancilla h₁₂ h₁a h₂a).eval).qAssign
      (Circuit.andCompute control₁ control₂ ancilla h₁a h₂a).eval =
    Θ.restrictToZeroAncilla (QRegister.singleton ancilla) := by
  funext σ
  apply Subtype.ext
  let P₀ := (QRegister.singleton ancilla).basisOutcomeProjector 0
  have hP₀_herm : P₀ᴴ = P₀ := QRegister.basisOutcomeProjector_conjTranspose _ 0
  have hadj :
      (Circuit.andCompute control₁ control₂ ancilla h₁a h₂a).eval.1ᴴ *
        ((Circuit.TOFF control₁ control₂ ancilla h₁₂ h₁a h₂a).eval.1ᴴ * P₀) = P₀ := by
    have h : (P₀ * (Circuit.TOFF control₁ control₂ ancilla h₁₂ h₁a h₂a).eval.1 *
        (Circuit.andCompute control₁ control₂ ancilla h₁a h₂a).eval.1)ᴴ = P₀ᴴ :=
      congrArg conjTranspose
        (projector_zero_mul_toffoli_mul_andCompute control₁ control₂ ancilla h₁₂ h₁a h₂a)
    rw [conjTranspose_mul, conjTranspose_mul, hP₀_herm] at h
    exact h
  simp only [restrictToZeroAncilla_coe, CQAssertion.qAssign_apply,
    Observable.conj_coe, Unitary.coe_star, Matrix.star_eq_conjTranspose, conj_conj]
  rw [hadj]

/-- On a clean `|0⟩` wire `ancilla`, the weakest precondition of `andCompute` equals that of
`Circuit.TOFF control₁ control₂ ancilla` for any postcondition `Θ`. -/
theorem restrictToZeroAncilla_wp_andCompute
    (control₁ control₂ ancilla : Wire n)
    (h₁₂ : control₁ ≠ control₂) (h₁a : control₁ ≠ ancilla) (h₂a : control₂ ≠ ancilla)
    (Θ : CQAssertion (Store Var) (2 ^ n)) :
    restrictToZeroAncilla
      (wp (andCompute (Var := Var) control₁ control₂ ancilla h₁a h₂a).compile Θ)
      (QRegister.singleton ancilla) =
    restrictToZeroAncilla
      (Θ.qAssign (Circuit.TOFF control₁ control₂ ancilla h₁₂ h₁a h₂a).eval)
      (QRegister.singleton ancilla) := by
  simp only [andCompute, DynamicCircuit.compile_circuit, wp_circuit_compile,
    restrictToZeroAncilla_qAssign_andCompute control₁ control₂ ancilla h₁₂ h₁a h₂a]

/-- Sequential composition starting with `andCompute` on a clean `|0⟩` wire `ancilla` has the same
clean-ancilla weakest precondition as starting with `Circuit.TOFF control₁ control₂ ancilla`. -/
theorem restrictToZeroAncilla_wp_andCompute_seq
    (control₁ control₂ ancilla : Wire n)
    (h₁₂ : control₁ ≠ control₂) (h₁a : control₁ ≠ ancilla) (h₂a : control₂ ≠ ancilla)
    (P : QProg Var (2 ^ n)) (Θ : CQAssertion (Store Var) (2 ^ n)) :
    restrictToZeroAncilla
      (wp (.qSeq (andCompute (Var := Var) control₁ control₂ ancilla h₁a h₂a).compile P) Θ)
      (QRegister.singleton ancilla) =
    restrictToZeroAncilla
      ((wp P Θ).qAssign (Circuit.TOFF control₁ control₂ ancilla h₁₂ h₁a h₂a).eval)
      (QRegister.singleton ancilla) := by
  change restrictToZeroAncilla
    (wp (andCompute (Var := Var) control₁ control₂ ancilla h₁a h₂a).compile (wp P Θ))
    (QRegister.singleton ancilla) = _
  exact restrictToZeroAncilla_wp_andCompute control₁ control₂ ancilla h₁₂ h₁a h₂a (wp P Θ)

/-!
### Temporary-AND uncomputation (`andUncompute`)
-/

private theorem wp_andUncompute_apply_assertion
    (v : Var) (control₁ control₂ ancilla : Wire n)
    (h₁₂ : control₁ ≠ control₂)
    (Θ : CQAssertion (Store Var) (2 ^ n)) (σ : Store Var) :
    let P₀ := (QRegister.singleton ancilla).basisOutcomeProjector 0
    let P₁ := (QRegister.singleton ancilla).basisOutcomeProjector 1
    let L₀ := P₀ * (Circuit.H ancilla).eval.1
    let L₁ := (Circuit.andUncomputeFixup control₁ control₂ ancilla h₁₂).eval.1 * P₁ *
      (Circuit.H ancilla).eval.1
    (wp (andUncompute v control₁ control₂ ancilla h₁₂).compile Θ σ).1 =
      (Θ (Function.update σ v 0)).1.conj L₀ᴴ + (Θ (Function.update σ v 1)).1.conj L₁ᴴ := by
  intro P₀ P₁ L₀ L₁
  let F := Circuit.andUncomputeFixup control₁ control₂ ancilla h₁₂
  let U := Circuit.H ancilla
  have hmeas_apply :
      (wp (.qSeq (QProg.measureRegister v (QRegister.singleton ancilla))
          (.qIf (fun σ'' ↦ σ'' v = 1) F.compile .skip)) Θ σ).1 =
        (Θ (Function.update σ v 0)).1.conj P₀ᴴ +
          ((Θ (Function.update σ v 1)).1.conj F.eval.1ᴴ).conj P₁ᴴ := by
    have hsubst0 : σ.subst v 0 = Function.update σ v 0 := by
      funext y; simp [Store.subst, Function.update]
    have hsubst1 : σ.subst v 1 = Function.update σ v 1 := by
      funext y; simp [Store.subst, Function.update]
    simp only [wp, QProg.measureRegister, CQAssertion.qMeasure_coe]
    change ∑ o : Fin 2, _ = _
    rw [Fin.sum_univ_two]
    simp [hsubst0, hsubst1, wp_circuit_compile,
      Matrix.star_eq_conjTranspose, QRegister.computationalBasisMeasurement_apply, P₀, P₁, F]
  change (wp U.compile
      (wp (.qSeq (QProg.measureRegister v (QRegister.singleton ancilla))
        (.qIf (fun σ'' ↦ σ'' v = 1) F.compile .skip)) Θ) σ).1 = _
  rw [wp_circuit_compile]
  simp only [CQAssertion.qAssign_apply, Observable.conj_coe, Unitary.coe_star,
    Matrix.star_eq_conjTranspose]
  rw [hmeas_apply, map_add, conj_conj, conj_conj, conj_conj]
  dsimp only [L₀, L₁, U, F]
  simp only [Matrix.mul_assoc, conjTranspose_mul]

/-- Because `andUncompute` overwrites the measurement variable `v` before evaluating its
postcondition, its weakest precondition is invariant under updating `v` in the initial store. -/
@[simp]
theorem wp_andUncompute_update_self
    (v : Var) (control₁ control₂ ancilla : Wire n)
    (h₁₂ : control₁ ≠ control₂)
    (Θ : CQAssertion (Store Var) (2 ^ n)) (σ : Store Var) (val : ℤ) :
    wp (andUncompute v control₁ control₂ ancilla h₁₂).compile
      Θ (Function.update σ v val) =
    wp (andUncompute v control₁ control₂ ancilla h₁₂).compile Θ σ := by
  apply Subtype.ext
  rw [wp_andUncompute_apply_assertion, wp_andUncompute_apply_assertion,
    Function.update_idem, Function.update_idem]

private theorem andUncomputeFixup_clean_ancilla
    (control₁ control₂ ancilla : Wire n)
    (h₁₂ : control₁ ≠ control₂) (h₁a : control₁ ≠ ancilla) (h₂a : control₂ ≠ ancilla) :
    let P₀ := (QRegister.singleton ancilla).basisOutcomeProjector 0
    let P₁ := (QRegister.singleton ancilla).basisOutcomeProjector 1
    P₀ * ((Circuit.andUncomputeFixup control₁ control₂ ancilla h₁₂).eval.1 * P₁) =
      (Circuit.andUncomputeFixup control₁ control₂ ancilla h₁₂).eval.1 * P₁ := by
  intro P₀ P₁
  apply matrix_ext_ket
  intro β
  simp only [P₀, P₁, ← Matrix.mulVec_mulVec, ket_projector_one]
  by_cases hanc : β ancilla = 1
  · simp only [hanc, ↓reduceIte,
      andUncomputeFixup_mulVec_ket control₁ control₂ ancilla h₁₂ h₁a h₂a,
      Matrix.mulVec_smul, ket_projector_zero, Function.update_self, one_add_one_zmod2]
  · simp [hanc]

/-- Clean-ancilla restoration for `andUncompute`: restricting any postcondition `Θ` to `|0⟩` on
`ancilla` leaves `wp (andUncompute ...).compile` unchanged, because both measurement branches leave
`ancilla` in `|0⟩`. -/
theorem wp_andUncompute_clean_post
    (v : Var) (control₁ control₂ ancilla : Wire n)
    (h₁₂ : control₁ ≠ control₂) (h₁a : control₁ ≠ ancilla) (h₂a : control₂ ≠ ancilla)
    (Θ : CQAssertion (Store Var) (2 ^ n)) :
    wp (andUncompute v control₁ control₂ ancilla h₁₂).compile
      (Θ.restrictToZeroAncilla (QRegister.singleton ancilla)) =
    wp (andUncompute v control₁ control₂ ancilla h₁₂).compile Θ := by
  funext σ
  apply Subtype.ext
  let P₀ := (QRegister.singleton ancilla).basisOutcomeProjector 0
  let P₁ := (QRegister.singleton ancilla).basisOutcomeProjector 1
  let L₀ := P₀ * (Circuit.H ancilla).eval.1
  let L₁ := (Circuit.andUncomputeFixup control₁ control₂ ancilla h₁₂).eval.1 * P₁ *
    (Circuit.H ancilla).eval.1
  have hP₀_herm : P₀ᴴ = P₀ := QRegister.basisOutcomeProjector_conjTranspose _ 0
  have hP₀_idem : P₀ * P₀ = P₀ := QRegister.basisOutcomeProjector_mul_self _ 0
  rw [wp_andUncompute_apply_assertion, wp_andUncompute_apply_assertion,
    restrictToZeroAncilla_coe, restrictToZeroAncilla_coe,
    conj_conj, conj_conj]
  have hL₀ : L₀ᴴ * P₀ = L₀ᴴ := by
    have h : P₀ * L₀ = L₀ := by
      dsimp only [L₀]
      rw [← Matrix.mul_assoc, hP₀_idem]
    have h' := congrArg conjTranspose h
    rw [conjTranspose_mul, hP₀_herm] at h'
    exact h'
  have hL₁ : L₁ᴴ * P₀ = L₁ᴴ := by
    have hfix : P₀ * ((Circuit.andUncomputeFixup control₁ control₂ ancilla h₁₂).eval.1 * P₁) =
        (Circuit.andUncomputeFixup control₁ control₂ ancilla h₁₂).eval.1 * P₁ :=
      andUncomputeFixup_clean_ancilla control₁ control₂ ancilla h₁₂ h₁a h₂a
    have h : P₀ * L₁ = L₁ := by
      dsimp only [L₁]
      rw [← Matrix.mul_assoc _ _ (Circuit.H ancilla).eval.1, hfix]
    have h' := congrArg conjTranspose h
    rw [conjTranspose_mul, hP₀_herm] at h'
    exact h'
  rw [hL₀, hL₁]

private theorem andUncompute_kraus_zero_mul_toffoli
    (control₁ control₂ ancilla : Wire n)
    (h₁₂ : control₁ ≠ control₂) (h₁a : control₁ ≠ ancilla) (h₂a : control₂ ≠ ancilla) :
    let P₀ := (QRegister.singleton ancilla).basisOutcomeProjector 0
    P₀ * (Circuit.H ancilla).eval.1 *
      (Circuit.TOFF control₁ control₂ ancilla h₁₂ h₁a h₂a).eval.1 * P₀ =
      sqrtHalf • P₀ := by
  intro P₀
  apply matrix_ext_ket
  intro β
  simp only [P₀, ← Matrix.mulVec_mulVec, Matrix.smul_mulVec, ket_projector_zero]
  by_cases hanc : β ancilla = 0
  · have hupd : Function.update β ancilla 0 = β := by
      funext w
      by_cases hw : w = ancilla
      · subst hw; simp [hanc]
      · simp [hw]
    simp only [hanc, ↓reduceIte, ket_TOFF, ket_H, Matrix.mulVec_smul, Matrix.mulVec_add,
      ket_projector_zero, Function.update_self, Function.update_idem, one_ne_zero, smul_zero,
      add_zero, hupd]
  · simp [hanc]

private theorem andUncompute_kraus_one_mul_toffoli
    (control₁ control₂ ancilla : Wire n)
    (h₁₂ : control₁ ≠ control₂) (h₁a : control₁ ≠ ancilla) (h₂a : control₂ ≠ ancilla) :
    let P₀ := (QRegister.singleton ancilla).basisOutcomeProjector 0
    let P₁ := (QRegister.singleton ancilla).basisOutcomeProjector 1
    (Circuit.andUncomputeFixup control₁ control₂ ancilla h₁₂).eval.1 * P₁ *
      (Circuit.H ancilla).eval.1 *
      (Circuit.TOFF control₁ control₂ ancilla h₁₂ h₁a h₂a).eval.1 * P₀ =
      sqrtHalf • P₀ := by
  intro P₀ P₁
  apply matrix_ext_ket
  intro β
  simp only [P₀, P₁, ← Matrix.mulVec_mulVec, Matrix.smul_mulVec, ket_projector_zero]
  by_cases hanc : β ancilla = 0
  · have hupd : Function.update β ancilla 0 = β := by
      funext w
      by_cases hw : w = ancilla
      · subst hw; simp [hanc]
      · simp [hw]
    have hsign_sq : bitSign (β control₁ * β control₂) * bitSign (β control₁ * β control₂) = 1 := by
      rcases bit_cases (β control₁ * β control₂) with h | h <;> simp [h, bitSign]
    simp only [hanc, ↓reduceIte, ket_TOFF, zero_add, ket_H,
      Matrix.mulVec_smul, Matrix.mulVec_add, ket_projector_one,
      Function.update_self, Function.update_idem, zero_ne_one,
      andUncomputeFixup_mulVec_ket control₁ control₂ ancilla h₁₂ h₁a h₂a,
      Function.update_of_ne h₁a, Function.update_of_ne h₂a, one_add_one_zmod2, hupd]
    rw [smul_smul, smul_smul, mul_assoc, hsign_sq, mul_one]
  · simp [hanc]

private theorem andUncompute_kraus_sum
    (control₁ control₂ ancilla : Wire n)
    (h₁₂ : control₁ ≠ control₂) (h₁a : control₁ ≠ ancilla) (h₂a : control₂ ≠ ancilla) :
    let P₀ := (QRegister.singleton ancilla).basisOutcomeProjector 0
    let P₁ := (QRegister.singleton ancilla).basisOutcomeProjector 1
    let L₀ := P₀ * (Circuit.H ancilla).eval.1
    let L₁ := (Circuit.andUncomputeFixup control₁ control₂ ancilla h₁₂).eval.1 * P₁ *
      (Circuit.H ancilla).eval.1
    sqrtHalf • (L₀ + L₁) =
      P₀ * (Circuit.TOFF control₁ control₂ ancilla h₁₂ h₁a h₂a).eval.1 := by
  dsimp only
  apply matrix_ext_ket
  intro β
  simp only [Matrix.smul_mulVec, Matrix.add_mulVec, ← Matrix.mulVec_mulVec,
    ket_H, ket_TOFF, Matrix.mulVec_smul, Matrix.mulVec_add,
    ket_projector_zero, ket_projector_one, Function.update_self, Function.update_idem,
    ↓reduceIte, one_ne_zero, zero_ne_one, Matrix.mulVec_zero, smul_zero, add_zero, zero_add,
    andUncomputeFixup_mulVec_ket control₁ control₂ ancilla h₁₂ h₁a h₂a,
    Function.update_of_ne h₁a, Function.update_of_ne h₂a, one_add_one_zmod2]
  rcases bit_cases (β ancilla) with hanc | hanc <;>
    rcases bit_cases (β control₁ * β control₂) with hprod | hprod <;>
    simp only [hanc, hprod, bitSign, add_zero, zero_add, one_add_one_zmod2,
      one_ne_zero, ↓reduceIte, smul_add, smul_smul]
  · match_scalars; linear_combination 2 * sqrtHalf_mul_sqrtHalf
  · match_scalars; ring
  · match_scalars; ring
  · match_scalars; linear_combination 2 * sqrtHalf_mul_sqrtHalf

private theorem conj_add_conj_eq (A : HermitianMat (Fin (2 ^ n)) ℂ)
    (B₀ B₁ : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) :
    A.conj B₀ᴴ + A.conj B₁ᴴ =
      A.conj (sqrtHalf • (B₀ + B₁))ᴴ + A.conj (sqrtHalf • (B₀ - B₁))ᴴ := by
  ext1
  simp only [HermitianMat.mat_add, conj_apply_mat, conjTranspose_conjTranspose,
    conjTranspose_smul, star_sqrtHalf, Matrix.smul_mul, Matrix.mul_smul, conjTranspose_add,
    conjTranspose_sub, Matrix.add_mul, Matrix.mul_add, Matrix.sub_mul, Matrix.mul_sub]
  match_scalars <;> first | ring1 | linear_combination (-2 : ℂ) * sqrtHalf_mul_sqrtHalf

/-- Unconditional lower bound for `andUncompute` on the entire Hilbert space: for any assertion `Θ`
independent of `v`, the weakest precondition of `Circuit.TOFF control₁ control₂ ancilla` on the
clean-ancilla postcondition `Θ.restrictToZeroAncilla (QRegister.singleton ancilla)` is
bounded above by `wp (andUncompute ...).compile Θ`. -/
theorem qAssign_toffoli_clean_post_le_wp_andUncompute_of_update_eq
    (v : Var) (control₁ control₂ ancilla : Wire n)
    (h₁₂ : control₁ ≠ control₂) (h₁a : control₁ ≠ ancilla) (h₂a : control₂ ≠ ancilla)
    (Θ : CQAssertion (Store Var) (2 ^ n))
    (hΘ : ∀ σ val, Θ (Function.update σ v val) = Θ σ) :
    (Θ.restrictToZeroAncilla (QRegister.singleton ancilla)).qAssign
      (Circuit.TOFF control₁ control₂ ancilla h₁₂ h₁a h₂a).eval ≤
    wp (andUncompute v control₁ control₂ ancilla h₁₂).compile Θ := by
  intro σ
  apply Subtype.coe_le_coe.mp
  rw [wp_andUncompute_apply_assertion, hΘ σ 0, hΘ σ 1, conj_add_conj_eq,
    andUncompute_kraus_sum control₁ control₂ ancilla h₁₂ h₁a h₂a]
  let P₀ := (QRegister.singleton ancilla).basisOutcomeProjector 0
  have hP₀_herm : P₀ᴴ = P₀ := QRegister.basisOutcomeProjector_conjTranspose _ 0
  have htoff : ((Θ.restrictToZeroAncilla (QRegister.singleton ancilla)).qAssign
      (Circuit.TOFF control₁ control₂ ancilla h₁₂ h₁a h₂a).eval σ).1 =
      (Θ σ).1.conj (P₀ * (Circuit.TOFF control₁ control₂ ancilla h₁₂ h₁a h₂a).eval.1)ᴴ := by
    simp only [CQAssertion.qAssign_apply, Observable.conj_coe, Unitary.coe_star,
      Matrix.star_eq_conjTranspose, restrictToZeroAncilla_coe, conj_conj]
    rw [conjTranspose_mul, hP₀_herm]
  rw [htoff]
  exact le_add_of_nonneg_right (conj_nonneg _ (Θ σ).2.1)

/-- Exact clean-ancilla weakest precondition when `Circuit.TOFF control₁ control₂ ancilla` precedes
`andUncompute`: on the clean-ancilla subspace `P₀`, `TOFF` followed by `andUncompute` acts as the
identity on `Θ`. -/
theorem restrictToZeroAncilla_qAssign_toffoli_wp_andUncompute_of_update_eq
    (v : Var) (control₁ control₂ ancilla : Wire n)
    (h₁₂ : control₁ ≠ control₂) (h₁a : control₁ ≠ ancilla) (h₂a : control₂ ≠ ancilla)
    (Θ : CQAssertion (Store Var) (2 ^ n))
    (hΘ : ∀ σ val, Θ (Function.update σ v val) = Θ σ) :
    restrictToZeroAncilla
      ((wp (andUncompute v control₁ control₂ ancilla h₁₂).compile Θ).qAssign
        (Circuit.TOFF control₁ control₂ ancilla h₁₂ h₁a h₂a).eval)
      (QRegister.singleton ancilla) =
    Θ.restrictToZeroAncilla (QRegister.singleton ancilla) := by
  funext σ
  apply Subtype.ext
  let P₀ := (QRegister.singleton ancilla).basisOutcomeProjector 0
  let P₁ := (QRegister.singleton ancilla).basisOutcomeProjector 1
  let L₀ := P₀ * (Circuit.H ancilla).eval.1
  let L₁ := (Circuit.andUncomputeFixup control₁ control₂ ancilla h₁₂).eval.1 * P₁ *
    (Circuit.H ancilla).eval.1
  let T_anc := (Circuit.TOFF control₁ control₂ ancilla h₁₂ h₁a h₂a).eval.1
  have hP₀_herm : P₀ᴴ = P₀ := QRegister.basisOutcomeProjector_conjTranspose _ 0
  simp only [restrictToZeroAncilla_coe, CQAssertion.qAssign_apply,
    Observable.conj_coe, Unitary.coe_star, Matrix.star_eq_conjTranspose]
  rw [wp_andUncompute_apply_assertion, hΘ σ 0, hΘ σ 1, map_add, map_add,
    conj_conj, conj_conj, conj_conj, conj_conj]
  have hL₀ : P₀ * T_ancᴴ * L₀ᴴ = (sqrtHalf • P₀)ᴴ := by
    have h : (L₀ * T_anc * P₀)ᴴ = (sqrtHalf • P₀)ᴴ :=
      congrArg conjTranspose
        (andUncompute_kraus_zero_mul_toffoli control₁ control₂ ancilla h₁₂ h₁a h₂a)
    rw [conjTranspose_mul, conjTranspose_mul, hP₀_herm, ← Matrix.mul_assoc] at h
    exact h
  have hL₁ : P₀ * T_ancᴴ * L₁ᴴ = (sqrtHalf • P₀)ᴴ := by
    have h : (L₁ * T_anc * P₀)ᴴ = (sqrtHalf • P₀)ᴴ :=
      congrArg conjTranspose
        (andUncompute_kraus_one_mul_toffoli control₁ control₂ ancilla h₁₂ h₁a h₂a)
    rw [conjTranspose_mul, conjTranspose_mul, hP₀_herm, ← Matrix.mul_assoc] at h
    exact h
  change (Θ σ).1.conj (P₀ * T_ancᴴ * L₀ᴴ) + (Θ σ).1.conj (P₀ * T_ancᴴ * L₁ᴴ) =
    (Θ σ).1.conj P₀
  rw [hL₀, hL₁]
  ext1
  simp only [HermitianMat.mat_add, conj_apply_mat, conjTranspose_smul, star_sqrtHalf, hP₀_herm,
    Matrix.smul_mul, Matrix.mul_smul]
  match_scalars
  linear_combination 2 * sqrtHalf_mul_sqrtHalf

/-- Temporary-AND compute/circuit/uncompute theorem for an arbitrary multi-gate circuit `c`:
when `T_anc * c.eval.1 * T_anc` preserves the clean-ancilla subspace `P₀`, running `andCompute`,
then `.circuit c`, then `andUncompute` has the exact same clean-ancilla weakest precondition as
`TOFF control₁ control₂ ancilla ;;ᶜ c ;;ᶜ TOFF control₁ control₂ ancilla`. -/
theorem restrictToZeroAncilla_wp_andCompute_circuit_andUncompute_of_update_eq
    (v : Var) (control₁ control₂ ancilla : Wire n)
    (h₁₂ : control₁ ≠ control₂) (h₁a : control₁ ≠ ancilla) (h₂a : control₂ ≠ ancilla)
    (c : Circuit n)
    (hc :
      let P₀ := (QRegister.singleton ancilla).basisOutcomeProjector 0
      let T_anc := (Circuit.TOFF control₁ control₂ ancilla h₁₂ h₁a h₂a).eval.1
      P₀ * (T_anc * c.eval.1 * T_anc * P₀) = T_anc * c.eval.1 * T_anc * P₀)
    (Θ : CQAssertion (Store Var) (2 ^ n))
    (hΘ : ∀ σ val, Θ (Function.update σ v val) = Θ σ) :
    restrictToZeroAncilla
      (wp (DynamicCircuit.seq (andCompute control₁ control₂ ancilla h₁a h₂a)
        (DynamicCircuit.seq (.circuit c)
          (andUncompute v control₁ control₂ ancilla h₁₂))).compile Θ)
      (QRegister.singleton ancilla) =
    restrictToZeroAncilla
      (Θ.qAssign
        (Circuit.TOFF control₁ control₂ ancilla h₁₂ h₁a h₂a ;;ᶜ
          c ;;ᶜ
          Circuit.TOFF control₁ control₂ ancilla h₁₂ h₁a h₂a).eval)
      (QRegister.singleton ancilla) := by
  let P₀ := (QRegister.singleton ancilla).basisOutcomeProjector 0
  let T_anc := (Circuit.TOFF control₁ control₂ ancilla h₁₂ h₁a h₂a).eval
  let V := T_anc * c.eval * T_anc
  have hT_sq : T_anc * T_anc = 1 :=
    toffoli_eval_mul_self control₁ control₂ ancilla h₁₂ h₁a h₂a
  have hU_eq : c.eval * T_anc = T_anc * V := by
    dsimp [V]
    rw [← mul_assoc, ← mul_assoc, hT_sq, one_mul]
  have hV_P₀ : P₀ * (V.1 * P₀) = V.1 * P₀ := hc
  have hP₀_herm : P₀ᴴ = P₀ := QRegister.basisOutcomeProjector_conjTranspose _ 0
  have hV_restrict (Ψ : CQAssertion (Store Var) (2 ^ n)) :
      restrictToZeroAncilla
        ((restrictToZeroAncilla Ψ (QRegister.singleton ancilla)).qAssign V)
        (QRegister.singleton ancilla) =
      restrictToZeroAncilla (Ψ.qAssign V) (QRegister.singleton ancilla) := by
    funext σ
    apply Subtype.ext
    have hadj : P₀ * V.1ᴴ * P₀ = P₀ * V.1ᴴ := by
      have h := congrArg conjTranspose hV_P₀
      simpa [P₀, conjTranspose_mul, hP₀_herm, ← Matrix.mul_assoc] using h
    simp only [restrictToZeroAncilla_coe, CQAssertion.qAssign_apply,
      Observable.conj_coe, Unitary.coe_star, Matrix.star_eq_conjTranspose, conj_conj]
    rw [← Matrix.mul_assoc, hadj]
  change restrictToZeroAncilla
    (wp (.qSeq (andCompute (Var := Var) control₁ control₂ ancilla h₁a h₂a).compile
      (.qSeq c.compile
        (andUncompute v control₁ control₂ ancilla h₁₂).compile)) Θ)
    (QRegister.singleton ancilla) =
    restrictToZeroAncilla (Θ.qAssign V) (QRegister.singleton ancilla)
  rw [restrictToZeroAncilla_wp_andCompute_seq control₁ control₂ ancilla h₁₂ h₁a h₂a]
  change restrictToZeroAncilla
    ((wp c.compile (wp (andUncompute v control₁ control₂ ancilla h₁₂).compile Θ)).qAssign T_anc)
    (QRegister.singleton ancilla) = _
  rw [wp_circuit_compile, CQAssertion.qAssign_qAssign, hU_eq, ← CQAssertion.qAssign_qAssign,
    ← hV_restrict,
    restrictToZeroAncilla_qAssign_toffoli_wp_andUncompute_of_update_eq
      v control₁ control₂ ancilla h₁₂ h₁a h₂a Θ hΘ,
    hV_restrict]

/-!
### Cody Jones' 4-`T` Toffoli (`jonesToffoli`) via `andCompute` and `andUncompute`
-/

private theorem toffoli_cnot_toffoli_mul_projector_zero
    (control₁ control₂ target ancilla : Wire n)
    (h₁₂ : control₁ ≠ control₂) (h₁t : control₁ ≠ target) (h₂t : control₂ ≠ target)
    (h₁a : control₁ ≠ ancilla) (h₂a : control₂ ≠ ancilla) (hta : target ≠ ancilla) :
    let P₀ := (QRegister.singleton ancilla).basisOutcomeProjector 0
    let T_anc := (Circuit.TOFF control₁ control₂ ancilla h₁₂ h₁a h₂a).eval.1
    T_anc * (Circuit.CNOT ancilla target hta.symm).eval.1 * T_anc * P₀ =
      (Circuit.TOFF control₁ control₂ target h₁₂ h₁t h₂t).eval.1 * P₀ := by
  intro P₀ T_anc
  apply matrix_ext_ket
  intro β
  dsimp only [P₀, T_anc]
  simp only [← Matrix.mulVec_mulVec, ket_projector_zero]
  by_cases hanc : β ancilla = 0
  · simp only [hanc, ↓reduceIte, ket_TOFF, zero_add, ket_CNOT,
      Function.update_self, Function.update_of_ne hta,
      Function.update_of_ne h₁t, Function.update_of_ne h₂t,
      Function.update_of_ne h₁a, Function.update_of_ne h₂a,
      Function.update_comm hta.symm, Function.update_idem,
      CharTwo.add_self_eq_zero]
    congr 1
    funext w
    by_cases hw : w = ancilla
    · subst hw; simp [Function.update_of_ne hta.symm, hanc]
    · simp [Function.update_of_ne hw]
  · simp [hanc]

/-- Because `jonesToffoli` overwrites the measurement variable `v` in `andUncompute` before
evaluating its postcondition, its weakest precondition is always invariant under updating `v` in
the initial store `σ`. -/
@[simp]
theorem wp_jonesToffoli_update_self
    (v : Var) (control₁ control₂ target ancilla : Wire n)
    (h₁₂ : control₁ ≠ control₂)
    (h₁a : control₁ ≠ ancilla) (h₂a : control₂ ≠ ancilla) (hta : target ≠ ancilla)
    (Θ : CQAssertion (Store Var) (2 ^ n)) (σ : Store Var) (val : ℤ) :
    wp (jonesToffoli v control₁ control₂ target ancilla h₁₂ h₁a h₂a hta).compile
      Θ (Function.update σ v val) =
    wp (jonesToffoli v control₁ control₂ target ancilla h₁₂ h₁a h₂a hta).compile
      Θ σ := by
  simp [jonesToffoli, andCompute, wp]

/-- Exact clean-ancilla weakest precondition of `jonesToffoli` for any assertion `Θ` that does
not depend on the scratch measurement variable `v`. -/
theorem restrictToZeroAncilla_wp_jonesToffoli_of_update_eq
    (v : Var) (control₁ control₂ target ancilla : Wire n)
    (h₁₂ : control₁ ≠ control₂) (h₁t : control₁ ≠ target) (h₂t : control₂ ≠ target)
    (h₁a : control₁ ≠ ancilla) (h₂a : control₂ ≠ ancilla) (hta : target ≠ ancilla)
    (Θ : CQAssertion (Store Var) (2 ^ n))
    (hΘ : ∀ σ val, Θ (Function.update σ v val) = Θ σ) :
    restrictToZeroAncilla
      (wp (jonesToffoli v control₁ control₂ target ancilla h₁₂ h₁a h₂a hta).compile Θ)
      (QRegister.singleton ancilla) =
    restrictToZeroAncilla
      (Θ.qAssign (Circuit.TOFF control₁ control₂ target h₁₂ h₁t h₂t).eval)
      (QRegister.singleton ancilla) := by
  rw [jonesToffoli]
  let P₀ := (QRegister.singleton ancilla).basisOutcomeProjector 0
  let T_anc := (Circuit.TOFF control₁ control₂ ancilla h₁₂ h₁a h₂a).eval
  let c_cnot := Circuit.CNOT ancilla target hta.symm
  have hconj := toffoli_cnot_toffoli_mul_projector_zero
    control₁ control₂ target ancilla h₁₂ h₁t h₂t h₁a h₂a hta
  have hcomm := toffoli_comm_ancilla_projector control₁ control₂ target ancilla h₁₂ h₁t h₂t hta
  have hP₀_idem : P₀ * P₀ = P₀ := QRegister.basisOutcomeProjector_mul_self _ 0
  have hc : P₀ * (T_anc.1 * c_cnot.eval.1 * T_anc.1 * P₀) =
      T_anc.1 * c_cnot.eval.1 * T_anc.1 * P₀ := by
    rw [hconj, ← Matrix.mul_assoc, ← hcomm, Matrix.mul_assoc, hP₀_idem]
  rw [restrictToZeroAncilla_wp_andCompute_circuit_andUncompute_of_update_eq
    v control₁ control₂ ancilla h₁₂ h₁a h₂a c_cnot hc Θ hΘ]
  funext σ
  apply Subtype.ext
  have hP₀_herm : P₀ᴴ = P₀ := QRegister.basisOutcomeProjector_conjTranspose _ 0
  have hadj : P₀ * (T_anc * c_cnot.eval * T_anc).1ᴴ =
      P₀ * (Circuit.TOFF control₁ control₂ target h₁₂ h₁t h₂t).eval.1ᴴ := by
    have h : ((T_anc * c_cnot.eval * T_anc).1 * P₀)ᴴ =
        ((Circuit.TOFF control₁ control₂ target h₁₂ h₁t h₂t).eval.1 * P₀)ᴴ :=
      congrArg conjTranspose hconj
    rw [conjTranspose_mul, conjTranspose_mul, hP₀_herm] at h
    exact h
  simp only [restrictToZeroAncilla_coe, CQAssertion.qAssign_apply,
    Observable.conj_coe, Unitary.coe_star, Matrix.star_eq_conjTranspose, conj_conj,
    Circuit.eval_seq]
  rw [hadj]

/-- Exact clean-ancilla weakest precondition of `jonesToffoli`:
when restricted to `|0⟩` on `ancilla`, `wp (jonesToffoli ...).compile (fun _ ↦ M)` is **equal**
to the clean-ancilla weakest precondition of `Circuit.TOFF control₁ control₂ target`. -/
theorem restrictToZeroAncilla_wp_jonesToffoli
    (v : Var) (control₁ control₂ target ancilla : Wire n)
    (h₁₂ : control₁ ≠ control₂) (h₁t : control₁ ≠ target) (h₂t : control₂ ≠ target)
    (h₁a : control₁ ≠ ancilla) (h₂a : control₂ ≠ ancilla) (hta : target ≠ ancilla)
    (M : Observable (Fin (2 ^ n))) :
    restrictToZeroAncilla
      (wp (jonesToffoli v control₁ control₂ target ancilla h₁₂ h₁a h₂a hta).compile
        (fun _ ↦ M))
      (QRegister.singleton ancilla) =
    restrictToZeroAncilla
      (CQAssertion.qAssign (Circuit.TOFF control₁ control₂ target h₁₂ h₁t h₂t).eval (fun _ ↦ M))
      (QRegister.singleton ancilla) :=
  restrictToZeroAncilla_wp_jonesToffoli_of_update_eq
    v control₁ control₂ target ancilla h₁₂ h₁t h₂t h₁a h₂a hta (fun _ ↦ M) (fun _ _ ↦ rfl)

/-- Clean-ancilla restoration: restricting any postcondition `Θ` to `|0⟩` on `ancilla` leaves the
weakest precondition of `jonesToffoli` unchanged, because `andUncompute` leaves `ancilla` in
`|0⟩`. -/
theorem wp_jonesToffoli_clean_post
    (v : Var) (control₁ control₂ target ancilla : Wire n)
    (h₁₂ : control₁ ≠ control₂)
    (h₁a : control₁ ≠ ancilla) (h₂a : control₂ ≠ ancilla) (hta : target ≠ ancilla)
    (Θ : CQAssertion (Store Var) (2 ^ n)) :
    wp (jonesToffoli v control₁ control₂ target ancilla h₁₂ h₁a h₂a hta).compile
      (Θ.restrictToZeroAncilla (QRegister.singleton ancilla)) =
    wp (jonesToffoli v control₁ control₂ target ancilla h₁₂ h₁a h₂a hta).compile
      Θ := by
  simp [jonesToffoli, wp, wp_andUncompute_clean_post v control₁ control₂ ancilla h₁₂ h₁a h₂a]

/-- Unconditional full-space lower bound on `wp (jonesToffoli ...).compile` for any assertion `Θ`
independent of `v`. -/
theorem restrictToZeroAncilla_le_wp_jonesToffoli_of_update_eq
    (v : Var) (control₁ control₂ target ancilla : Wire n)
    (h₁₂ : control₁ ≠ control₂) (h₁t : control₁ ≠ target) (h₂t : control₂ ≠ target)
    (h₁a : control₁ ≠ ancilla) (h₂a : control₂ ≠ ancilla) (hta : target ≠ ancilla)
    (Θ : CQAssertion (Store Var) (2 ^ n))
    (hΘ : ∀ σ val, Θ (Function.update σ v val) = Θ σ) :
    restrictToZeroAncilla
      (Θ.qAssign (Circuit.TOFF control₁ control₂ target h₁₂ h₁t h₂t).eval)
      (QRegister.singleton ancilla) ≤
    wp (jonesToffoli v control₁ control₂ target ancilla h₁₂ h₁a h₂a hta).compile Θ := by
  let P₀ := (QRegister.singleton ancilla).basisOutcomeProjector 0
  let C_and := (Circuit.andCompute control₁ control₂ ancilla h₁a h₂a).eval
  let U_cnot := (Circuit.CNOT ancilla target hta.symm).eval
  let T_anc := (Circuit.TOFF control₁ control₂ ancilla h₁₂ h₁a h₂a).eval
  let T_tar := (Circuit.TOFF control₁ control₂ target h₁₂ h₁t h₂t).eval
  have huncomp :=
    qAssign_toffoli_clean_post_le_wp_andUncompute_of_update_eq
      v control₁ control₂ ancilla h₁₂ h₁a h₂a Θ hΘ
  have hmono :
      (((Θ.restrictToZeroAncilla (QRegister.singleton ancilla)).qAssign T_anc).qAssign
        U_cnot).qAssign C_and ≤
      ((wp (andUncompute v control₁ control₂ ancilla h₁₂).compile Θ).qAssign U_cnot).qAssign
        C_and :=
    CQAssertion.qAssign_mono C_and (CQAssertion.qAssign_mono U_cnot huncomp)
  have hlhs :
      (((Θ.restrictToZeroAncilla (QRegister.singleton ancilla)).qAssign T_anc).qAssign
        U_cnot).qAssign C_and =
      restrictToZeroAncilla
        (Θ.qAssign T_tar)
        (QRegister.singleton ancilla) := by
    let V := T_anc * U_cnot * T_anc
    have hT_sq : T_anc * T_anc = 1 :=
      toffoli_eval_mul_self control₁ control₂ ancilla h₁₂ h₁a h₂a
    have hU_eq : T_anc * U_cnot = V * T_anc := by
      dsimp only [V]
      rw [mul_assoc, hT_sq, mul_one]
    have hVP₀ : V.1 * P₀ = P₀ * T_tar.1 :=
      (toffoli_cnot_toffoli_mul_projector_zero
        control₁ control₂ target ancilla h₁₂ h₁t h₂t h₁a h₂a hta).trans
        (toffoli_comm_ancilla_projector control₁ control₂ target ancilla h₁₂ h₁t h₂t hta)
    have hV_herm : V.1ᴴ = V.1 := by
      dsimp only [V, T_anc, U_cnot]
      simp only [Submonoid.coe_mul, conjTranspose_mul, toffoli_eval_conjTranspose,
        cnot_eval_conjTranspose, Matrix.mul_assoc]
    have hT_tar_herm : T_tar.1ᴴ = T_tar.1 :=
      toffoli_eval_conjTranspose control₁ control₂ target h₁₂ h₁t h₂t
    have hV_step :
        (Θ.restrictToZeroAncilla (QRegister.singleton ancilla)).qAssign V =
          (Θ.qAssign T_tar).restrictToZeroAncilla (QRegister.singleton ancilla) := by
      funext σ'
      apply Subtype.ext
      simp only [CQAssertion.qAssign_apply, Observable.conj_coe, Unitary.coe_star,
        Matrix.star_eq_conjTranspose, restrictToZeroAncilla_coe, conj_conj]
      rw [hV_herm, hT_tar_herm, hVP₀]
    rw [CQAssertion.qAssign_qAssign U_cnot T_anc, hU_eq, ← CQAssertion.qAssign_qAssign T_anc V,
      hV_step, qAssign_andCompute_qAssign_toffoli_clean]
  rw [← hlhs, jonesToffoli]
  simpa only [andCompute, DynamicCircuit.compile_seq, DynamicCircuit.compile_circuit,
    wp, wp_circuit_compile] using hmono

/-- `jonesToffoli` realizes the 3-qubit Toffoli unitary `PrimitiveGate.toffoli.eval` on
`QRegister.triple control₁ control₂ target h₁₂ h₁t h₂t` with clean ancilla register
`QRegister.singleton ancilla`. -/
theorem realizesCleanSubroutine_jonesToffoli
    (v : Var) (control₁ control₂ target ancilla : Wire n)
    (h₁₂ : control₁ ≠ control₂) (h₁t : control₁ ≠ target) (h₂t : control₂ ≠ target)
    (h₁a : control₁ ≠ ancilla) (h₂a : control₂ ≠ ancilla) (hta : target ≠ ancilla)
    (hdisj : (QRegister.triple control₁ control₂ target h₁₂ h₁t h₂t).DisjointWires
      (QRegister.singleton ancilla)) :
    RealizesCleanSubroutine
      (QRegister.triple control₁ control₂ target h₁₂ h₁t h₂t)
      (QRegister.singleton ancilla)
      hdisj
      PrimitiveGate.toffoli.eval
      (jonesToffoli v control₁ control₂ target ancilla h₁₂ h₁a h₂a hta).compile := by
  intro M
  apply Triple.of_le_wp
  exact restrictToZeroAncilla_le_wp_jonesToffoli_of_update_eq
    v control₁ control₂ target ancilla h₁₂ h₁t h₂t h₁a h₂a hta
    (restrictToZeroAncilla (fun _ ↦ M) (QRegister.singleton ancilla))
    (fun _ _ ↦ rfl)

/-- Sequential ancilla reuse: composing `jonesToffoli` with any subsequent program `P` whose
weakest precondition on `Θ` does not depend on the scratch measurement variable `v` (for example,
any program starting with another `jonesToffoli` on `v`, or any program that does not read `v`)
has the same clean-ancilla weakest precondition as running `Circuit.TOFF` followed by `P` with
clean ancilla `ancilla`. -/
theorem restrictToZeroAncilla_wp_jonesToffoli_seq
    (v : Var) (control₁ control₂ target ancilla : Wire n)
    (h₁₂ : control₁ ≠ control₂) (h₁t : control₁ ≠ target) (h₂t : control₂ ≠ target)
    (h₁a : control₁ ≠ ancilla) (h₂a : control₂ ≠ ancilla) (hta : target ≠ ancilla)
    (P : QProg Var (2 ^ n)) (Θ : CQAssertion (Store Var) (2 ^ n))
    (hP : ∀ σ val, wp P Θ (Function.update σ v val) = wp P Θ σ) :
    restrictToZeroAncilla
      (wp (.qSeq
        (jonesToffoli v control₁ control₂ target ancilla h₁₂ h₁a h₂a hta).compile P)
        Θ)
      (QRegister.singleton ancilla) =
    restrictToZeroAncilla
      (((wp P Θ).restrictToZeroAncilla (QRegister.singleton ancilla)).qAssign
        (Circuit.TOFF control₁ control₂ target h₁₂ h₁t h₂t).eval)
      (QRegister.singleton ancilla) := by
  change restrictToZeroAncilla
      (wp (jonesToffoli v control₁ control₂ target ancilla h₁₂ h₁a h₂a hta).compile
        (wp P Θ))
      (QRegister.singleton ancilla) = _
  rw [← wp_jonesToffoli_clean_post v control₁ control₂ target ancilla h₁₂ h₁a h₂a hta]
  exact restrictToZeroAncilla_wp_jonesToffoli_of_update_eq
    v control₁ control₂ target ancilla h₁₂ h₁t h₂t h₁a h₂a hta
    ((wp P Θ).restrictToZeroAncilla (QRegister.singleton ancilla))
    (fun σ val ↦ by
      apply Subtype.ext
      simp [restrictToZeroAncilla_coe, hP σ val])

end DynamicCircuit
