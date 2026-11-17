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
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.ModularDefs
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.CleanAncillaToffoli
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.SeamAdapters
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.GivensDataCerts

/-!
# Raw Unsigned `13`-Bit Rank-2 Bilinear Givens & `94-T`/`98-T` Apex Cascade
Zero-Toffoli (`TOFF = 0`) Givens rotation & spin-segregation
engine for Cytochrome P450 Compound I (`P450.dfthc : THCFactorization 58 261`):

1. **P450 DFTHC Certificates (`decide +kernel`)**:
   - All `319 × 57 = 18,183` entries of `P450.leafAngleTable` (`261 × 57`) and
     `P450.oneBodyAngleTable` (`58 × 57`) satisfy `k < 8192 = 2^13`.
   - All `319` apex (`p = 0`) entries satisfy `2048 ≤ k_0 < 6144`
     (`(k_0 >>> 11) ^^^ (k_0 >>> 12) = 1`),
     giving the exact bit-elimination identity
     `2 * k_0 = 4096 + 4096 * b_12 + 2048 * b_10 + 2 * (k_0 % 1024)` (bit `11` cancels).
   - Exact one-body sign split: `oneBodyWeights[ℓ] < 0` for `ℓ < 30` (`15` `Lac = 2` pairs `0..14`)
     and `oneBodyWeights[ℓ] > 0` for `30 ≤ ℓ < 58` (`14` `Lac = 2` pairs `15..28`).
2. **Unified `(B + 2)`-Bit Raw Unsigned Phase-Kickback Engine**:
   - Directly reads raw `13`-bit unsigned integers `k ∈ [0, 8192)` with zero sign-magnitude
     (`4096 + (-1)^s m`) conversion, zero `s_curr` wire, and zero `Δ_s` wire.
   - Conjugates `rCat` (`phaseGradientLowSlice B 3`) directly by system wire `w_p` via `X` / `CNOT`,
     cancelling the one's-complement `-1` shift via `parityTCircuit c_B w_p` +
     `parityTCircuit a_B w_p`
     + `sdagCircuit w_p`.
   - Instantiated at `B = 11` for general planes `p = 1..56` (`102 T` Rank-2 Bilinear `Lac = 2`,
     `98 T` standalone) and at `B = 10` on `rCat11.slice 1 10` (`phaseGradientLowSlice 10 3`) for
     shifted apex `p = 0` (`94 T` active-1 `Lac = 2`, `98 T` wire-controlled `Lac = 2`,
     `90 T` / `94 T` standalone), using at most `23` clean scratch wires
     (`wV + 11 mask + 11 carry`).
3. **Fermionic `fSWAP` Spin-Segregation & `57`-Plane `givensLeaf 15` Cascade**:
   - `spinSegregateCircuit N` (`0 T`, `0 TOFF`) commutes with `electronSectorProjector (2 * N) η`
     and maps interleaved `orbitalNumberOp N χ σ` to block-local `segOrbitalNumberOp N χ` on
     `QRegister.block 0 N` (`σ = 0`) and `QRegister.block N N` (`σ = 1`), bridged by `4 * N`-`T`
     Fredkin block swap `cswapBlockDyn`.
   - Full `57`-plane `givensLeaf 15` cascade realizing `1` when `active = 0` and
     `1 - (2 : ℂ) • segOrbitalNumberOp 58 (givensLeaf 15 k)` when `active = 1`.
-/

@[expose] public section

namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.CircuitModular.UnsignedGivens
open QuantumComputation.Specs QuantumComputation.Specs.P450

open Operator QProg Matrix HermitianMat QuantumComputation.Specs Solution
open QuantumComputation.Specs.P450
open Solution.CircuitModular
open scoped Matrix ComplexOrder MatrixOrder BigOperators Circuit.Notation

/-! ## Part 1: Bitwise Arithmetic Identities (DFTHC Table Certs Imported from `GivensDataCerts`) -/

theorem zmod2_eq_zero_or_one (b : ZMod 2) : b = 0 ∨ b = 1 := by
  fin_cases b
  · exact Or.inl rfl
  · exact Or.inr rfl

@[simp]
theorem zmod2_add_self (b : ZMod 2) : b + b = 0 := by
  revert b; decide

@[simp]
theorem zmod2_add_cancel_right (a b : ZMod 2) : a + b + b = a := by
  revert a b; decide

@[simp]
theorem zmod2_mul_self (b : ZMod 2) : b * b = b := by
  revert b; decide

/-! ## Part 2: `ket`, Primitive Gate Evolutions & `PhasedPerm` -/

section KetAndPhasedPerm

variable {n : ℕ}

noncomputable abbrev ket (β : BitAssignment n) : Fin (2 ^ n) → ℂ :=
  basisState ((basisBits n).symm β)

@[simp]
theorem basisBits_symm_eq {q : ℕ} (β : BitAssignment q) :
    basisBits q ((basisBits q).symm β) = β :=
  (basisBits q).apply_symm_apply β

@[simp]
theorem symm_basisBits_eq {q : ℕ} (j : Fin (2 ^ q)) :
    (basisBits q).symm (basisBits q j) = j :=
  (basisBits q).symm_apply_apply j

theorem single_eq_ket (g : Fin (2 ^ n)) :
    (Pi.single g 1 : Fin (2 ^ n) → ℂ) = ket (basisBits n g) := by
  simp [ket, basisState]

theorem matrix_ext_ket {A B : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ}
    (h : ∀ β : BitAssignment n, A.mulVec (ket β) = B.mulVec (ket β)) : A = B := by
  ext i j
  have hij := congrFun (h (basisBits n j)) i
  simpa [← single_eq_ket, Matrix.mulVec_single_one] using hij

noncomputable def writeReg {k : ℕ} (β : BitAssignment n) (r : QRegister k n)
    (γ : BitAssignment k) : BitAssignment n :=
  basisBits n (r.replaceIndex ((basisBits n).symm β) ((basisBits k).symm γ))

@[simp]
theorem writeReg_apply_reg {k : ℕ} (β : BitAssignment n) (r : QRegister k n)
    (γ : BitAssignment k) (i : Fin k) : writeReg β r γ (r i) = γ i := by
  simp [writeReg, QRegister.basisBits_replaceIndex_apply]

theorem writeReg_apply_of_not_mem {k : ℕ} (β : BitAssignment n) (r : QRegister k n)
    (γ : BitAssignment k) (w : Wire n) (hw : w ∉ Set.range r.wires) :
    writeReg β r γ w = β w := by
  simp [writeReg, QRegister.basisBits_replaceIndex_of_not_mem _ _ _ _ hw]

theorem writeReg_eq_update {k : ℕ} (β : BitAssignment n) (r : QRegister k n)
    (γ : BitAssignment k) (i₀ : Fin k) (hγ : ∀ i, i ≠ i₀ → γ i = β (r i)) :
    writeReg β r γ = Function.update β (r i₀) (γ i₀) := by
  funext w
  by_cases hw : w ∈ Set.range r.wires
  · obtain ⟨i, rfl⟩ := hw
    rw [writeReg_apply_reg]
    by_cases hi : i = i₀
    · subst hi; simp
    · rw [Function.update_of_ne (fun h ↦ hi (r.wires.injective h)), hγ i hi]
  · rw [writeReg_apply_of_not_mem _ _ _ _ hw, Function.update_of_ne]
    exact fun h ↦ hw ⟨i₀, h.symm⟩

noncomputable abbrev localIdx {k : ℕ} (r : QRegister k n) (β : BitAssignment n) : Fin (2 ^ k) :=
  (basisBits k).symm (fun i ↦ β (r i))

theorem embedMatrix_mulVec_ket {k : ℕ} (r : QRegister k n)
    (A : Matrix (Fin (2 ^ k)) (Fin (2 ^ k)) ℂ) (β : BitAssignment n) :
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

theorem embedMatrix_permMatrix_mulVec_ket {k : ℕ} (r : QRegister k n)
    (σ : Equiv.Perm (Fin (2 ^ k))) (β : BitAssignment n) :
    (r.embedMatrix (Equiv.Perm.permMatrix ℂ σ)).mulVec (ket β) =
      ket (writeReg β r (basisBits k (σ.symm (localIdx r β)))) := by
  rw [embedMatrix_mulVec_ket, Finset.sum_eq_single (σ.symm (localIdx r β))]
  · simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]
  · intro l _ hl
    have : σ l ≠ localIdx r β := fun h ↦ hl (by rw [← h, Equiv.symm_apply_apply])
    simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, this]
  · simp

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

theorem eval_seq_mulVec (c₁ c₂ : Circuit n) (ψ : Fin (2 ^ n) → ℂ) :
    (c₁ ;;ᶜ c₂).eval.1.mulVec ψ = c₂.eval.1.mulVec (c₁.eval.1.mulVec ψ) := by
  rw [Circuit.eval_seq, Submonoid.coe_mul, ← Matrix.mulVec_mulVec]

@[simp]
theorem eval_identity_mulVec (ψ : Fin (2 ^ n) → ℂ) :
    (Circuit.identity : Circuit n).eval.1.mulVec ψ = ψ := by
  rw [Circuit.eval_identity, Submonoid.coe_one, Matrix.one_mulVec]

@[simp] theorem zmod2_val_zero : (0 : ZMod 2).val = 0 := rfl
@[simp] theorem zmod2_val_one : (1 : ZMod 2).val = 1 := rfl

@[simp]
theorem evolve_X_ket (q : Wire n) (β : BitAssignment n) :
    (Circuit.X q).eval.1.mulVec (ket β) = ket (Function.update β q (β q + 1)) := by
  rw [Circuit.eval_single, QRegister.embedUnitary_val, PrimitiveGate.eval]
  change ((QRegister.singleton q).embedMatrix !![0, 1; 1, 0]).mulVec _ = _
  rw [singleton_embedMatrix_mulVec_ket]
  rcases zmod2_eq_zero_or_one (β q) with hb | hb <;> simp [hb]

@[simp]
theorem evolve_Z_ket (q : Wire n) (β : BitAssignment n) :
    (Circuit.Z q).eval.1.mulVec (ket β) = ((-1 : ℂ) ^ (β q).val) • ket β := by
  rw [Circuit.eval_single, QRegister.embedUnitary_val, PrimitiveGate.eval]
  change ((QRegister.singleton q).embedMatrix !![1, 0; 0, -1]).mulVec _ = _
  rw [singleton_embedMatrix_mulVec_ket]
  have e := Function.update_eq_self q β
  rcases zmod2_eq_zero_or_one (β q) with hb | hb <;>
    rw [hb] at e <;> simp [hb, e]

@[simp]
theorem evolve_S_ket (q : Wire n) (β : BitAssignment n) :
    (Circuit.S q).eval.1.mulVec (ket β) = (Complex.I ^ (β q).val) • ket β := by
  rw [Circuit.eval_single, QRegister.embedUnitary_val, PrimitiveGate.eval]
  change ((QRegister.singleton q).embedMatrix Qubit.S.1).mulVec _ = _
  rw [singleton_embedMatrix_mulVec_ket]
  have e := Function.update_eq_self q β
  rcases zmod2_eq_zero_or_one (β q) with hb | hb <;>
    rw [hb] at e <;> simp [hb, e, Qubit.S]

noncomputable def omega8 : ℂ := Complex.exp (Complex.I * Real.pi / 4)

theorem omega8_sq : omega8 ^ 2 = Complex.I := by
  dsimp [omega8]
  rw [← Complex.exp_nat_mul]
  have harg : (2 : ℕ) * (Complex.I * ↑Real.pi / 4) = ↑(Real.pi / 2) * Complex.I := by
    push_cast; ring
  rw [harg, Complex.exp_mul_I]
  simp [Complex.cos_pi_div_two, Complex.sin_pi_div_two]

@[simp]
theorem evolve_T_ket (q : Wire n) (β : BitAssignment n) :
    (Circuit.T q).eval.1.mulVec (ket β) = (omega8 ^ (β q).val) • ket β := by
  rw [Circuit.eval_single, QRegister.embedUnitary_val, PrimitiveGate.eval]
  change ((QRegister.singleton q).embedMatrix Qubit.T.1).mulVec _ = _
  rw [singleton_embedMatrix_mulVec_ket]
  have e := Function.update_eq_self q β
  have ht00 : Qubit.T.1 0 0 = 1 := rfl
  have ht01 : Qubit.T.1 0 1 = 0 := rfl
  have ht10 : Qubit.T.1 1 0 = 0 := rfl
  have ht11 : Qubit.T.1 1 1 = omega8 := by
    have harg : Complex.I * ↑Real.pi / 4 = ↑(Real.pi / 4) * Complex.I := by
      push_cast; ring
    have hexp : omega8 = ↑(Real.cos (Real.pi / 4)) + ↑(Real.sin (Real.pi / 4)) * Complex.I := by
      dsimp [omega8]
      rw [harg, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    rw [hexp, Real.cos_pi_div_four, Real.sin_pi_div_four]
    dsimp [Qubit.T]
    have h2 : (Real.sqrt 2 : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr (by norm_num))
    have hsq : (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ) = 2 := by
      exact_mod_cast Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    push_cast
    field_simp [h2]
    linear_combination (1 + Complex.I) * hsq.symm
  rcases zmod2_eq_zero_or_one (β q) with hb | hb <;>
    rw [hb] at e <;> simp [hb, e, ht00, ht01, ht10, ht11]

noncomputable def sqrtHalfC : ℂ := (Real.sqrt (1 / 2) : ℝ)

theorem sqrtHalfC_mul_self : sqrtHalfC * sqrtHalfC = 1 / 2 := by
  dsimp [sqrtHalfC]
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
  push_cast; ring

theorem sqrtHalfC_sq : sqrtHalfC ^ 2 = 1 / 2 := by
  rw [sq, sqrtHalfC_mul_self]

theorem evolve_H_ket (q : Wire n) (β : BitAssignment n) :
    (Circuit.H q).eval.1.mulVec (ket β) =
      sqrtHalfC • (ket (Function.update β q 0) +
        ((-1 : ℂ) ^ (β q).val) • ket (Function.update β q 1)) := by
  rw [Circuit.eval_single, QRegister.embedUnitary_val, PrimitiveGate.eval]
  change ((QRegister.singleton q).embedMatrix
    ((Real.sqrt (1 / 2) : ℝ) • !![(1 : ℂ), 1; 1, -1])).mulVec _ = _
  rw [singleton_embedMatrix_mulVec_ket]
  rcases zmod2_eq_zero_or_one (β q) with hb | hb <;>
    simp [hb, sqrtHalfC, smul_add, Complex.real_smul]

@[simp]
theorem evolve_CNOT_ket (c t : Wire n) (h : c ≠ t) (β : BitAssignment n) :
    (Circuit.CNOT c t h).eval.1.mulVec (ket β) =
      ket (Function.update β t (β t + β c)) := by
  rw [Circuit.eval_gate, QRegister.embedUnitary_val, PrimitiveGate.eval_cnot_val,
    embedMatrix_permMatrix_mulVec_ket]
  have hloc : ∀ γ : BitAssignment 2,
      basisBits 2 ((Equiv.swap (1 : Fin 4) 3).symm ((basisBits 2).symm γ)) =
        Function.update γ 1 (γ 1 + γ 0) := fun γ ↦ by
    have h0 : ∀ (b0 b1 : ZMod 2) (i : Fin 2),
        basisBits 2 ((Equiv.swap (1 : Fin 4) 3).symm
          ((basisBits 2).symm (fun k ↦ if k = 0 then b0 else b1))) i =
          Function.update (fun k : Fin 2 ↦ if k = 0 then b0 else b1) 1 (b1 + b0) i := by
      intro b0 b1 i; fin_cases b0 <;> fin_cases b1 <;> fin_cases i <;> decide
    have hγ : γ = (fun k : Fin 2 ↦ if k = 0 then γ 0 else γ 1) := by
      funext k; fin_cases k <;> rfl
    funext i; rw [hγ]; exact h0 (γ 0) (γ 1) i
  rw [localIdx, hloc, writeReg_eq_update _ _ _ 1]
  · simp
  · intro i hi; fin_cases i
    · simp
    · exact absurd rfl hi

@[simp]
theorem evolve_TOFF_ket (c₁ c₂ t : Wire n) (h₁₂ : c₁ ≠ c₂) (h₁t : c₁ ≠ t) (h₂t : c₂ ≠ t)
    (β : BitAssignment n) :
    (Circuit.TOFF c₁ c₂ t h₁₂ h₁t h₂t).eval.1.mulVec (ket β) =
      ket (Function.update β t (β t + β c₁ * β c₂)) := by
  rw [Circuit.eval_gate, QRegister.embedUnitary_val, PrimitiveGate.eval_toffoli_val,
    embedMatrix_permMatrix_mulVec_ket]
  have hloc : ∀ γ : BitAssignment 3,
      basisBits 3 ((Equiv.swap (3 : Fin 8) 7).symm ((basisBits 3).symm γ)) =
        Function.update γ 2 (γ 2 + γ 0 * γ 1) := fun γ ↦ by
    have h0 : ∀ (b0 b1 b2 : ZMod 2) (i : Fin 3),
        basisBits 3 ((Equiv.swap (3 : Fin 8) 7).symm
          ((basisBits 3).symm (fun k ↦ if k = 0 then b0 else if k = 1 then b1 else b2))) i =
          Function.update (fun k : Fin 3 ↦ if k = 0 then b0 else if k = 1 then b1 else b2) 2
            (b2 + b0 * b1) i := by
      intro b0 b1 b2 i; fin_cases b0 <;> fin_cases b1 <;> fin_cases b2 <;> fin_cases i <;> decide
    have hγ : γ = (fun k : Fin 3 ↦ if k = 0 then γ 0 else if k = 1 then γ 1 else γ 2) := by
      funext k; fin_cases k <;> rfl
    funext i; rw [hγ]; exact h0 (γ 0) (γ 1) (γ 2) i
  rw [localIdx, hloc, writeReg_eq_update _ _ _ 2]
  · simp
  · intro i hi; fin_cases i
    · simp
    · simp
    · exact absurd rfl hi

@[simp]
theorem evolve_SWAP_ket (a b : Wire n) (hab : a ≠ b) (β : BitAssignment n) :
    (Circuit.SWAP a b hab).eval.1.mulVec (ket β) =
      ket (Function.update (Function.update β a (β b)) b (β a)) := by
  rw [Circuit.eval_gate, QRegister.embedUnitary_val, PrimitiveGate.eval_swap_val,
    embedMatrix_permMatrix_mulVec_ket]
  have hloc : ∀ γ : BitAssignment 2,
      basisBits 2 ((Equiv.swap (1 : Fin 4) 2).symm ((basisBits 2).symm γ)) =
        fun i : Fin 2 ↦ if i = 0 then γ 1 else γ 0 := fun γ ↦ by
    have h0 : ∀ (b0 b1 : ZMod 2) (i : Fin 2),
        basisBits 2 ((Equiv.swap (1 : Fin 4) 2).symm
          ((basisBits 2).symm (fun k ↦ if k = 0 then b0 else b1))) i =
          (if i = 0 then b1 else b0) := by
      intro b0 b1 i; fin_cases b0 <;> fin_cases b1 <;> fin_cases i <;> decide
    have hγ : γ = (fun k : Fin 2 ↦ if k = 0 then γ 0 else γ 1) := by
      funext k; fin_cases k <;> rfl
    funext i; rw [hγ]; exact h0 (γ 0) (γ 1) i
  congr 1
  rw [localIdx, hloc]
  funext w
  by_cases hmem : w ∈ Set.range (QRegister.pair a b hab).wires
  · obtain ⟨i, rfl⟩ := hmem
    rw [writeReg_apply_reg]
    fin_cases i
    · simp [Function.update_of_ne hab]
    · simp
  · rw [writeReg_apply_of_not_mem _ _ _ _ hmem]
    have hwa : w ≠ a := fun h ↦ hmem ⟨0, by simpa using h.symm⟩
    have hwb : w ≠ b := fun h ↦ hmem ⟨1, by simpa using h.symm⟩
    simp [Function.update_of_ne hwb, Function.update_of_ne hwa]

@[simp]
theorem basisOutcomeProjector_zero_ket (q : Wire n) (β : BitAssignment n) :
    ((QRegister.singleton q).basisOutcomeProjector 0).mulVec (ket β) =
      if β q = 0 then ket β else 0 := by
  rw [ket, basisState, QRegister.basisOutcomeProjector_mulVec_single]
  have h : ∀ b : ZMod 2,
      (((basisBits 1).symm (fun _ ↦ b) : Fin 2) = 0 ↔ b = 0) := by decide
  have hext : (QRegister.singleton q).extractIndex ((basisBits n).symm β) =
      (basisBits 1).symm (fun _ ↦ β q) := by
    simp [QRegister.extractIndex]
  simp only [hext]
  split_ifs with h1 h2 h2 <;> first | rfl | exact absurd ((h _).1 h1) h2 |
    exact absurd ((h _).2 h2) h1

theorem register_basisOutcomeProjector_zero_ket {m : ℕ} (r : QRegister m n) (β : BitAssignment n) :
    (r.basisOutcomeProjector 0).mulVec (ket β) =
      if (∀ i : Fin m, β (r i) = 0) then ket β else 0 := by
  rw [ket, basisState, QRegister.basisOutcomeProjector_mulVec_single]
  simp only [QRegister.extractIndex_eq_zero_iff, basisBits_symm_eq]

/-- `S† = Z ;; S` (`0 T`, `0 TOFF`). -/
def sdagCircuit (q : Wire n) : Circuit n :=
  Circuit.Z q ;;ᶜ Circuit.S q

@[simp] theorem count_sdagCircuit_t (q : Wire n) : (sdagCircuit q).count .T = 0 := by
  simp [sdagCircuit]

@[simp] theorem count_sdagCircuit_toff (q : Wire n) : (sdagCircuit q).count .TOFF = 0 := by
  simp [sdagCircuit]

@[simp]
theorem evolve_sdagCircuit_ket (q : Wire n) (β : BitAssignment n) :
    (sdagCircuit q).eval.1.mulVec (ket β) = ((-Complex.I) ^ (β q).val) • ket β := by
  rw [sdagCircuit, eval_seq_mulVec, evolve_Z_ket, Matrix.mulVec_smul, evolve_S_ket, smul_smul]
  congr 1
  rcases zmod2_eq_zero_or_one (β q) with hb | hb <;> simp [hb]

/-- Controlled-`Z` circuit `H t ;; CNOT c t ;; H t` (`0 T`, `0 TOFF`). -/
def czCircuit (c t : Wire n) (hct : c ≠ t) : Circuit n :=
  Circuit.H t ;;ᶜ Circuit.CNOT c t hct ;;ᶜ Circuit.H t

@[simp] theorem count_czCircuit_t (c t : Wire n) (hct : c ≠ t) :
    (czCircuit c t hct).count .T = 0 := by simp [czCircuit]

@[simp] theorem count_czCircuit_toff (c t : Wire n) (hct : c ≠ t) :
    (czCircuit c t hct).count .TOFF = 0 := by simp [czCircuit]

theorem support_czCircuit_subset (c t : Wire n) (hct : c ≠ t) :
    (czCircuit c t hct).support ⊆ {c, t} := by
  intro q hq
  simp only [czCircuit, Circuit.support_seq, Circuit.support_single, Circuit.support_cnot,
    Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hq ⊢
  tauto

private theorem neg_one_pow_zmod2_val (x : ZMod 2) :
    (-1 : ℂ) ^ x.val = if x = 0 then 1 else -1 := by
  rcases zmod2_eq_zero_or_one x with hx | hx <;> simp [hx]

@[simp]
theorem evolve_czCircuit_ket (c t : Wire n) (hct : c ≠ t) (β : BitAssignment n) :
    (czCircuit c t hct).eval.1.mulVec (ket β) = ((-1 : ℂ) ^ (β c * β t).val) • ket β := by
  rw [czCircuit, eval_seq_mulVec, eval_seq_mulVec, evolve_H_ket]
  simp only [Matrix.mulVec_smul, Matrix.mulVec_add, evolve_CNOT_ket, Function.update_self,
    Function.update_idem, Function.update_of_ne hct, evolve_H_ket, smul_add, smul_smul,
    neg_one_pow_zmod2_val]
  rcases zmod2_eq_zero_or_one (β c) with hc | hc <;>
    rcases zmod2_eq_zero_or_one (β t) with ht | ht
  · have hu : Function.update β t 0 = β := Function.update_eq_self_iff.mpr ht.symm
    have h10 : (1 : ZMod 2) ≠ 0 := by decide
    simp only [hc, ht, add_zero, mul_zero, h10, ↓reduceIte, hu]
    ext idx; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring_nf; simp only [sqrtHalfC_sq]; ring
  · have hu : Function.update β t 1 = β := Function.update_eq_self_iff.mpr ht.symm
    have h10 : (1 : ZMod 2) ≠ 0 := by decide
    simp only [hc, ht, add_zero, mul_one, h10, ↓reduceIte, hu]
    ext idx; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring_nf; simp only [sqrtHalfC_sq]; ring
  · have hu : Function.update β t 0 = β := Function.update_eq_self_iff.mpr ht.symm
    have h10 : (1 : ZMod 2) ≠ 0 := by decide
    simp only [hc, ht, zero_add, zmod2_add_self, mul_zero, h10, ↓reduceIte, hu]
    ext idx; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring_nf; simp only [sqrtHalfC_sq]; ring
  · have hu : Function.update β t 1 = β := Function.update_eq_self_iff.mpr ht.symm
    have h10 : (1 : ZMod 2) ≠ 0 := by decide
    simp only [hc, ht, zero_add, zmod2_add_self, mul_one, h10, ↓reduceIte, hu]
    ext idx; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring_nf; simp only [sqrtHalfC_sq]; ring

/-- Parity `T` gadget `CNOT w a ;; T a ;; CNOT w a` (`1 T`, `0 TOFF`), applying phase
`omega8 ^ (β a + β w).val` while leaving all computational-basis bits unchanged. -/
def parityTCircuit (a w : Wire n) (haw : a ≠ w) : Circuit n :=
  Circuit.CNOT w a haw.symm ;;ᶜ Circuit.T a ;;ᶜ Circuit.CNOT w a haw.symm

@[simp] theorem count_parityTCircuit_t (a w : Wire n) (haw : a ≠ w) :
    (parityTCircuit a w haw).count .T = 1 := by simp [parityTCircuit]

@[simp] theorem count_parityTCircuit_toff (a w : Wire n) (haw : a ≠ w) :
    (parityTCircuit a w haw).count .TOFF = 0 := by simp [parityTCircuit]

@[simp]
theorem evolve_parityTCircuit_ket (a w : Wire n) (haw : a ≠ w) (β : BitAssignment n) :
    (parityTCircuit a w haw).eval.1.mulVec (ket β) =
      (omega8 ^ (β a + β w).val) • ket β := by
  rw [parityTCircuit, eval_seq_mulVec, eval_seq_mulVec, evolve_CNOT_ket, evolve_T_ket,
    Matrix.mulVec_smul, evolve_CNOT_ket]
  simp only [Function.update_self, Function.update_of_ne haw.symm, Function.update_idem,
    zmod2_add_cancel_right]
  have hu : Function.update β a (β a) = β := Function.update_eq_self a β
  rw [hu]

private theorem slice_one_apply_eq_succ {G : ℕ} (rSrc : QRegister (G + 1) n) (g : Fin G) :
    (rSrc.slice 1 G (by omega)) g = rSrc g.succ := by
  simp only [QRegister.slice_apply]
  congr 1; ext; dsimp [QRegister.block]; omega

/-- Masked `CNOT` gather from register `rSrc` into target `dst` (`0 T`, `0 TOFF`). -/
def cnotMaskReg : (G : ℕ) → (rSrc : QRegister G n) → (dst : Wire n) → (mask : Fin G → Bool) →
    (hdisj : ∀ g, rSrc g ≠ dst) → Circuit n
  | 0, _, _, _, _ => .identity
  | G + 1, rSrc, dst, mask, hdisj =>
      (if mask 0 then Circuit.CNOT (rSrc 0) dst (hdisj 0) else .identity) ;;ᶜ
        cnotMaskReg G (rSrc.slice 1 G (by omega)) dst (fun g => mask g.succ)
          (fun g => by rw [slice_one_apply_eq_succ]; exact hdisj g.succ)

@[simp] theorem count_cnotMaskReg_t (G : ℕ) (rSrc : QRegister G n) (dst : Wire n)
    (mask : Fin G → Bool) (hdisj : ∀ g, rSrc g ≠ dst) :
    (cnotMaskReg G rSrc dst mask hdisj).count .T = 0 := by
  induction G with
  | zero => simp [cnotMaskReg]
  | succ G ih =>
      simp only [cnotMaskReg, Circuit.count_seq, ih]
      split <;> simp

@[simp] theorem count_cnotMaskReg_toff (G : ℕ) (rSrc : QRegister G n) (dst : Wire n)
    (mask : Fin G → Bool) (hdisj : ∀ g, rSrc g ≠ dst) :
    (cnotMaskReg G rSrc dst mask hdisj).count .TOFF = 0 := by
  induction G with
  | zero => simp [cnotMaskReg]
  | succ G ih =>
      simp only [cnotMaskReg, Circuit.count_seq, ih]
      split <;> simp

theorem support_cnotMaskReg_subset (G : ℕ) (rSrc : QRegister G n) (dst : Wire n)
    (mask : Fin G → Bool) (hdisj : ∀ g, rSrc g ≠ dst) :
    (cnotMaskReg G rSrc dst mask hdisj).support ⊆ insert dst rSrc.image := by
  induction G with
  | zero => simp [cnotMaskReg]
  | succ G ih =>
      intro q hq
      simp only [cnotMaskReg, Circuit.support_seq, Finset.mem_union] at hq
      rcases hq with h0 | hrest
      · split at h0
        · simp only [Circuit.support_cnot, Finset.mem_insert, Finset.mem_singleton] at h0
          rcases h0 with hq0 | hqd
          · rw [hq0]
            exact Finset.mem_insert_of_mem (QRegister.mem_image rSrc _ |>.mpr ⟨0, rfl⟩)
          · rw [hqd]
            exact Finset.mem_insert_self dst _
        · simp at h0
      · have hsub := ih (rSrc.slice 1 G (by omega)) (fun g => mask g.succ) _ hrest
        simp only [Finset.mem_insert, QRegister.mem_image, slice_one_apply_eq_succ] at hsub ⊢
        rcases hsub with rfl | ⟨g, rfl⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨g.succ, rfl⟩

def maskSumBit {G : ℕ} (rSrc : QRegister G n) (mask : Fin G → Bool) (β : BitAssignment n) :
  ZMod 2 :=
  ∑ g : Fin G, if mask g then β (rSrc g) else 0

theorem evolve_cnotMaskReg_ket (G : ℕ) (rSrc : QRegister G n) (dst : Wire n)
    (mask : Fin G → Bool) (hdisj : ∀ g, rSrc g ≠ dst) (β : BitAssignment n) :
    (cnotMaskReg G rSrc dst mask hdisj).eval.1.mulVec (ket β) =
      ket (Function.update β dst (β dst + maskSumBit rSrc mask β)) := by
  induction G generalizing β with
  | zero =>
      rw [cnotMaskReg, eval_identity_mulVec]
      have hz : maskSumBit rSrc mask β = 0 := by simp [maskSumBit]
      rw [hz, add_zero, Function.update_eq_self]
  | succ G ih =>
      let rRest := rSrc.slice 1 G (by omega)
      have hhead : (if mask 0 then Circuit.CNOT (rSrc 0) dst (hdisj 0) else .identity).eval.1.mulVec
        (ket β) =
          ket (Function.update β dst (β dst + if mask 0 then β (rSrc 0) else 0)) := by
        by_cases hm : mask 0
        · simp only [hm, ↓reduceIte, evolve_CNOT_ket]
        · simp only [hm, Bool.false_eq_true, ↓reduceIte, eval_identity_mulVec, add_zero,
            Function.update_eq_self]
      rw [cnotMaskReg, eval_seq_mulVec, hhead, ih rRest]
      congr 1
      have hrest_eq : maskSumBit rRest (fun g => mask g.succ)
          (Function.update β dst (β dst + if mask 0 then β (rSrc 0) else 0)) =
          ∑ g : Fin G, if mask g.succ then β (rSrc g.succ) else 0 := by
        unfold maskSumBit
        refine Finset.sum_congr rfl fun g _ => ?_
        have hidx : rRest g = rSrc g.succ := slice_one_apply_eq_succ rSrc g
        have hne : rRest g ≠ dst := hidx ▸ hdisj g.succ
        rw [Function.update_of_ne hne, hidx]
      rw [Function.update_idem, Function.update_self, hrest_eq]
      congr 1
      rw [maskSumBit, Fin.sum_univ_succ, add_assoc]

/-- `PhasedPerm c φ f` means `c` maps each basis state `ket β` to `φ β • ket (f β)`. -/
def PhasedPerm (c : Circuit n) (φ : BitAssignment n → ℂ)
    (f : BitAssignment n → BitAssignment n) : Prop :=
  ∀ β : BitAssignment n, c.eval.1.mulVec (ket β) = φ β • ket (f β)

theorem PhasedPerm.identity : PhasedPerm (.identity : Circuit n) (fun _ => 1) id := by
  intro β
  rw [eval_identity_mulVec, one_smul, id_eq]

theorem PhasedPerm.seq {c₁ c₂ : Circuit n} {φ₁ φ₂ : BitAssignment n → ℂ}
    {f₁ f₂ : BitAssignment n → BitAssignment n}
    (h₁ : PhasedPerm c₁ φ₁ f₁) (h₂ : PhasedPerm c₂ φ₂ f₂) :
    PhasedPerm (c₁ ;;ᶜ c₂) (fun β => φ₁ β * φ₂ (f₁ β)) (f₂ ∘ f₁) := by
  intro β
  rw [eval_seq_mulVec, h₁ β, Matrix.mulVec_smul, Function.comp_apply, h₂ (f₁ β), smul_smul]

theorem toffoli_conj_preserves_zero_ancilla_of_phasedPerm
    (c₁ c₂ anc : Wire n) (h₁₂ : c₁ ≠ c₂) (h₁a : c₁ ≠ anc) (h₂a : c₂ ≠ anc)
    (c_body : Circuit n) (φ_body : BitAssignment n → ℂ) (f_body : BitAssignment n → BitAssignment n)
    (hperm : PhasedPerm c_body φ_body f_body)
    (hc₁ : ∀ β, f_body β c₁ = β c₁)
    (hc₂ : ∀ β, f_body β c₂ = β c₂)
    (hanc : ∀ β, f_body β anc = β anc) :
    let P₀ := (QRegister.singleton anc).basisOutcomeProjector 0
    let T_anc := (Circuit.TOFF c₁ c₂ anc h₁₂ h₁a h₂a).eval.1
    P₀ * (T_anc * c_body.eval.1 * T_anc * P₀) = T_anc * c_body.eval.1 * T_anc * P₀ := by
  intro P₀ T_anc
  apply matrix_ext_ket
  intro β
  dsimp only [P₀, T_anc]
  simp only [← Matrix.mulVec_mulVec, basisOutcomeProjector_zero_ket]
  by_cases hβ : β anc = 0
  · simp only [hβ, ↓reduceIte, evolve_TOFF_ket, zero_add]
    let β₁ := Function.update β anc (β c₁ * β c₂)
    rw [hperm β₁, Matrix.mulVec_smul, evolve_TOFF_ket, Matrix.mulVec_smul,
      basisOutcomeProjector_zero_ket]
    have h₁ : f_body β₁ c₁ = β c₁ := (hc₁ β₁).trans (Function.update_of_ne h₁a _ _)
    have h₂ : f_body β₁ c₂ = β c₂ := (hc₂ β₁).trans (Function.update_of_ne h₂a _ _)
    have ha : f_body β₁ anc = β c₁ * β c₂ :=
      (hanc β₁).trans (Function.update_self anc (β c₁ * β c₂) β)
    have hzero : f_body β₁ anc + f_body β₁ c₁ * f_body β₁ c₂ = 0 := by
      rw [ha, h₁, h₂, zmod2_add_self]
    simp [Function.update_self, hzero]
  · simp [hβ]

end KetAndPhasedPerm

/-! ## Part 3: `PreservesStoreConst`, `PhasedStep` (`4 T`) & Clean-Workspace Unitary Bridge -/

section PhasedStepAndCleanBridge

variable {Var : Type} {n : ℕ}

def PreservesStoreConst [Fintype Var] [DecidableEq Var] (d : DynamicCircuit Var n) : Prop :=
  ∀ (M : Observable (Fin (2 ^ n))), ∃ M' : Observable (Fin (2 ^ n)), wp d.compile (fun _ =>
    M) = fun _ => M'

theorem PreservesStoreConst.circuit [Fintype Var] [DecidableEq Var] (c : Circuit n) :
    PreservesStoreConst (Var := Var) (.circuit c) := fun M =>
  ⟨qcQAssignObsMap c.eval M, by
    funext σ; simp [DynamicCircuit.compile_circuit, qcWpQAssign]⟩

theorem PreservesStoreConst.identity [Fintype Var] [DecidableEq Var] :
    PreservesStoreConst (Var := Var) (n := n) .identity := fun M => ⟨M, rfl⟩

theorem PreservesStoreConst.seq [Fintype Var] [DecidableEq Var]
    {d₁ d₂ : DynamicCircuit Var n}
    (h₁ : PreservesStoreConst d₁) (h₂ : PreservesStoreConst d₂) :
    PreservesStoreConst (.seq d₁ d₂) := by
  intro M
  obtain ⟨M₂, hM₂⟩ := h₂ M
  obtain ⟨M₁, hM₁⟩ := h₁ M₂
  exact ⟨M₁, by simp only [DynamicCircuit.compile_seq, wp, hM₂, hM₁]⟩

theorem PreservesStoreConst.andCompute [Fintype Var] [DecidableEq Var]
    (c₁ c₂ anc : Wire n) (h₁a : c₁ ≠ anc) (h₂a : c₂ ≠ anc) :
    PreservesStoreConst (Var := Var) (DynamicCircuit.andCompute c₁ c₂ anc h₁a h₂a) :=
  PreservesStoreConst.circuit _

theorem PreservesStoreConst.andUncompute [Fintype Var] [DecidableEq Var]
    (v : Var) (c₁ c₂ anc : Wire n) (h₁₂ : c₁ ≠ c₂) :
    PreservesStoreConst (DynamicCircuit.andUncompute v c₁ c₂ anc h₁₂) := by
  have : NeZero (2 ^ n) := instNeZeroTwoPowP450 n
  intro M
  exact DynamicCircuit.qc_wp_andUncompute_const v c₁ c₂ anc h₁₂ M

theorem disjointWires_iff_disjoint_image {k m : ℕ} (r : QRegister k n) (s : QRegister m n) :
    r.DisjointWires s ↔ Disjoint r.image s.image := by
  rw [QRegister.disjoint_iff, Finset.disjoint_left]
  constructor
  · intro h q hr hs
    rw [QRegister.mem_image] at hr hs
    rcases hr with ⟨i, rfl⟩
    rcases hs with ⟨j, hj⟩
    exact h i j hj.symm
  · intro h i j hij
    exact h (QRegister.mem_image r (r i) |>.mpr ⟨i, rfl⟩)
      (QRegister.mem_image s (r i) |>.mpr ⟨j, hij.symm⟩)

@[simp]
theorem image_concat_eq {k m : ℕ} (r : QRegister k n) (s : QRegister m n)
    (h : r.DisjointWires s) : (r.concat s h).image = r.image ∪ s.image := by
  ext q
  simp only [QRegister.mem_image, Finset.mem_union]
  constructor
  · rintro ⟨i, rfl⟩
    refine Fin.addCases (m := k) (n := m)
      (motive := fun idx ↦ (∃ a, r a = r.concat s h idx) ∨ (∃ b, s b = r.concat s h idx))
      (fun a ↦ Or.inl ⟨a, by simp⟩) (fun b ↦ Or.inr ⟨b, by simp⟩) i
  · rintro (⟨i, rfl⟩ | ⟨j, rfl⟩)
    · exact ⟨Fin.castAdd m i, by simp⟩
    · exact ⟨Fin.natAdd k j, by simp⟩

theorem eval_comm_basisOutcomeProjector_of_disjoint_support {m : ℕ}
    (c : Circuit n) (r : QRegister m n) (hdisj : Disjoint c.support r.image)
    (o : Fin (2 ^ m)) :
    c.eval.1 * r.basisOutcomeProjector o = r.basisOutcomeProjector o * c.eval.1 := by
  induction c with
  | identity => simp
  | gate g rg =>
      simp only [Circuit.support_gate] at hdisj
      have hdisj_wires : rg.DisjointWires r :=
        (disjointWires_iff_disjoint_image rg r).mpr hdisj
      simp only [Circuit.eval_gate, QRegister.embedUnitary_val, QRegister.basisOutcomeProjector]
      exact QRegister.embedMatrix_comm_of_disjoint rg r hdisj_wires g.eval.1 (compProj o)
  | seq c₁ c₂ ih₁ ih₂ =>
      simp only [Circuit.support_seq, Finset.disjoint_union_left] at hdisj
      simp only [Circuit.eval_seq, Submonoid.coe_mul]
      rw [Matrix.mul_assoc, ih₁ hdisj.1, ← Matrix.mul_assoc, ih₂ hdisj.2, Matrix.mul_assoc]

theorem restrictAssertionToZeroAncilla_wp_qAssign_comm_of_disjoint [Fintype Var] {m : ℕ}
    (c : Circuit n) (r : QRegister m n) (hdisj : Disjoint c.support r.image)
    (Θ : QCAssertion Var (2 ^ n)) :
    restrictAssertionToZeroAncilla (qcWpQAssign c.eval Θ) r =
      qcWpQAssign c.eval (restrictAssertionToZeroAncilla Θ r) := by
  funext σ
  apply Subtype.ext
  let P₀ := r.basisOutcomeProjector 0
  have hcomm := eval_comm_basisOutcomeProjector_of_disjoint_support c r hdisj 0
  have hadj : P₀ * c.eval.1ᴴ = c.eval.1ᴴ * P₀ := by
    have h := congrArg conjTranspose hcomm
    simpa only [P₀, conjTranspose_mul, QRegister.basisOutcomeProjector_conjTranspose] using h
  simp only [restrictAssertionToZeroAncilla_coe, qcWpQAssign, qcQAssignObsMap,
    Observable.conj_coe, Unitary.coe_star, Matrix.star_eq_conjTranspose, conj_conj]
  change (Θ σ).1.conj (P₀ * c.eval.1ᴴ) = (Θ σ).1.conj (c.eval.1ᴴ * P₀)
  rw [hadj]

/-- Single `4-T` temporary-`AND` wrapper (`andCompute` + Clifford frame + `andUncompute`). -/
structure PhasedStep (n : ℕ) where
  pre : Circuit n
  c₁ : Wire n
  c₂ : Wire n
  anc : Wire n
  h₁₂ : c₁ ≠ c₂
  h₁a : c₁ ≠ anc
  h₂a : c₂ ≠ anc
  midPre : Circuit n
  midPost : Circuit n
  post : Circuit n

namespace PhasedStep

def wrapCircuit (s : PhasedStep n) (c : Circuit n) : Circuit n :=
  s.pre ;;ᶜ
  Circuit.TOFF s.c₁ s.c₂ s.anc s.h₁₂ s.h₁a s.h₂a ;;ᶜ
  (s.midPre ;;ᶜ c ;;ᶜ s.midPost) ;;ᶜ
  Circuit.TOFF s.c₁ s.c₂ s.anc s.h₁₂ s.h₁a s.h₂a ;;ᶜ
  s.post

def wrapDynamic (v : Var) (s : PhasedStep n) (inner : DynamicCircuit Var n) :
    DynamicCircuit Var n :=
  .seq (.circuit s.pre)
    (.seq
      (.seq (DynamicCircuit.andCompute s.c₁ s.c₂ s.anc s.h₁a s.h₂a)
        (.seq (.seq (.circuit s.midPre) (.seq inner (.circuit s.midPost)))
          (DynamicCircuit.andUncompute v s.c₁ s.c₂ s.anc s.h₁₂)))
      (.circuit s.post))

def IsCliffordWrapper (s : PhasedStep n) : Prop :=
  s.pre.count .TOFF = 0 ∧ s.pre.count .T = 0 ∧
  s.midPre.count .TOFF = 0 ∧ s.midPre.count .T = 0 ∧
  s.midPost.count .TOFF = 0 ∧ s.midPost.count .T = 0 ∧
  s.post.count .TOFF = 0 ∧ s.post.count .T = 0

theorem count_wrapDynamic_toff (v : Var) (s : PhasedStep n) (inner : DynamicCircuit Var n)
    (hs : s.IsCliffordWrapper) :
    (s.wrapDynamic v inner).count .TOFF = inner.count .TOFF := by
  rcases hs with ⟨h1, _, h2, _, h3, _, h4, _⟩
  simp [wrapDynamic, DynamicCircuit.count_andCompute_toff, DynamicCircuit.count_andUncompute_toff,
    h1, h2, h3, h4]

theorem count_wrapDynamic_t (v : Var) (s : PhasedStep n) (inner : DynamicCircuit Var n)
    (hs : s.IsCliffordWrapper) :
    (s.wrapDynamic v inner).count .T = 4 + inner.count .T := by
  rcases hs with ⟨_, h1, _, h2, _, h3, _, h4⟩
  simp [wrapDynamic, DynamicCircuit.count_andCompute_t, DynamicCircuit.count_andUncompute_t,
    h1, h2, h3, h4]

theorem preservesStoreConst_wrapDynamic [Fintype Var] [DecidableEq Var]
    (v : Var) (s : PhasedStep n) {inner : DynamicCircuit Var n}
    (hinner : PreservesStoreConst inner) :
    PreservesStoreConst (s.wrapDynamic v inner) :=
  PreservesStoreConst.seq (PreservesStoreConst.circuit _)
    (PreservesStoreConst.seq
      (PreservesStoreConst.seq (PreservesStoreConst.andCompute _ _ _ _ _)
        (PreservesStoreConst.seq
          (PreservesStoreConst.seq (PreservesStoreConst.circuit _)
            (PreservesStoreConst.seq hinner (PreservesStoreConst.circuit _)))
          (PreservesStoreConst.andUncompute v _ _ _ _)))
      (PreservesStoreConst.circuit _))

end PhasedStep

end PhasedStepAndCleanBridge

end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.CircuitModular.UnsignedGivens

end
