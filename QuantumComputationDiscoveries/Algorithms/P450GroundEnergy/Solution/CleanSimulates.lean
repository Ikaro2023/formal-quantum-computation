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
public import QuantumComputation.Circuits.Toffoli
public import QuantumComputation.QuantumHoareLogic.CleanAncilla
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.ModularDefs
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.CleanAncillaToffoli
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.SeamAdapters

/-!
# Zero-Extra-Ancilla Binary-Tree One-Hot `CNOT` Angle-Stream `SELECT` (`CleanSimulates`)

Clean-workspace `SELECT` primitives (`TOFF = 0`, `Var = PUnit`-safe) for `P450.dfthc`:
- **Section 0 (`KetHelpers`)**: Basis-ket evaluation & self-inverse palindrome lemmas for `X`, `Z`,
  `H`,
  `CNOT`, `TOFF`, and `czCircuit`.
- **Section 1 (`GlobalCleanSimulates`)**: Clean-workspace QHL simulation closed under `.seq`,
  `.circuit`,
  `.congrUnitary`, `.congrClean`, `DynamicCircuit.jonesToffoli`, and `tempAndProg` (`4 T`
  `andCompute`,
  `0 T` `andUncompute`).
- **Section 2 (`cswapSpinBlockProg`)**: `4 * N`-`T` (`232 T` at `N = 58`) Fredkin spin-block swap
  sharing 1 clean ancilla wire.
- **Section 3 (`oneHotTreeProg` & `oneHotActiveProg`)**: In-place binary-tree unary/one-hot decoder
  parameterized over any `1 ≤ D ≤ 2 ^ m` (`D = 319, m = 9` -> `1,272 T` Pass 1; `D = 261, m = 9` ->
  `1,040 T` Pass 2; `0` extra ancillas beyond `rOneHot`, `0 T` uncomputation).
-/

@[expose] public section

namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.OneHotSimulates
open QuantumComputation.Specs QuantumComputation.Specs.P450

open Operator QProg Matrix HermitianMat QuantumComputation.Specs
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution
open CircuitModular
open scoped Matrix ComplexOrder MatrixOrder BigOperators Circuit.Notation

/-! ## Section 0: Basis-Ket & Self-Inverse Palindrome Helpers -/

section KetHelpers

variable {n : ℕ}

theorem zmod2_eq_zero_or_one (b : ZMod 2) : b = 0 ∨ b = 1 := by
  fin_cases b
  · exact Or.inl rfl
  · exact Or.inr rfl

noncomputable abbrev ket (β : BitAssignment n) : Fin (2 ^ n) → ℂ :=
  basisState ((basisBits n).symm β)

@[simp]
theorem basisBits_basisBitsEquiv_symm {q : ℕ} (β : BitAssignment q) :
    basisBits q ((basisBits q).symm β) = β :=
  (basisBits q).apply_symm_apply β

@[simp]
theorem basisBitsEquiv_symm_basisBits {q : ℕ} (j : Fin (2 ^ q)) :
    (basisBits q).symm (basisBits q j) = j :=
  (basisBits q).symm_apply_apply j

theorem single_eq_ket (g : Fin (2 ^ n)) :
    (Pi.single g 1 : Fin (2 ^ n) → ℂ) = ket (basisBits n g) := by
  simp [ket, basisState]

theorem matrix_ext_ket {A B : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ}
    (h : ∀ β, A.mulVec (ket β) = B.mulVec (ket β)) : A = B := by
  ext i j
  have := congrFun (h (basisBits n j)) i
  simpa [← single_eq_ket, Matrix.mulVec_single_one] using this

theorem vec_eq_sum_ket (ψ : Fin (2 ^ n) → ℂ) :
    ψ = ∑ g : Fin (2 ^ n), ψ g • ket (basisBits n g) := by
  funext i
  simp [← single_eq_ket, Finset.sum_apply, Pi.single_apply]

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

noncomputable abbrev localIdx {k : ℕ} (r : QRegister k n) (β : BitAssignment n) :
    Fin (2 ^ k) :=
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
    (Circuit.seq c₁ c₂).eval.1.mulVec ψ = c₂.eval.1.mulVec (c₁.eval.1.mulVec ψ) := by
  rw [Circuit.eval_seq, Matrix.mulVec_mulVec]
  rfl

theorem ket_X (q : Wire n) (β : BitAssignment n) :
    (Circuit.X q).eval.1.mulVec (ket β) = ket (Function.update β q (β q + 1)) := by
  rw [Circuit.eval_single, QRegister.embedUnitary_val, PrimitiveGate.eval]
  change ((QRegister.singleton q).embedMatrix !![0, 1; 1, 0]).mulVec _ = _
  rw [singleton_embedMatrix_mulVec_ket]
  rcases zmod2_eq_zero_or_one (β q) with hb | hb
  · simp [hb]
  · simp [hb, CharTwo.add_self_eq_zero]

theorem ket_CNOT (c t : Wire n) (h : c ≠ t) (β : BitAssignment n) :
    (Circuit.CNOT c t h).eval.1.mulVec (ket β) = ket (Function.update β t (β t + β c)) := by
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
  · intro i hi
    fin_cases i
    · simp
    · exact absurd rfl hi

theorem ket_TOFF (c₁ c₂ t : Wire n) (h₁₂ : c₁ ≠ c₂) (h₁t : c₁ ≠ t) (h₂t : c₂ ≠ t)
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
  · intro i hi
    fin_cases i
    · simp
    · simp
    · exact absurd rfl hi

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

theorem unitary_conjTranspose_eq_self_of_mul_self {d : ℕ} (U : Unitary d)
    (hsq : U * U = 1) : U.1ᴴ = U.1 := by
  have hv : U.1 * U.1 = 1 := congrArg Subtype.val hsq
  have hUU : U.1ᴴ * U.1 = 1 := by
    rw [← Matrix.star_eq_conjTranspose]
    exact U.2.1
  calc U.1ᴴ = U.1ᴴ * (U.1 * U.1) := by rw [hv, Matrix.mul_one]
    _ = (U.1ᴴ * U.1) * U.1 := by rw [← Matrix.mul_assoc]
    _ = U.1 := by rw [hUU, Matrix.one_mul]

theorem cnot_eval_mul_self (c t : Wire n) (h : c ≠ t) :
    (Circuit.CNOT c t h).eval * (Circuit.CNOT c t h).eval = 1 := by
  apply Subtype.ext
  apply matrix_ext_ket
  intro β
  simp only [Submonoid.coe_mul, Submonoid.coe_one, ← Matrix.mulVec_mulVec, Matrix.one_mulVec]
  rw [ket_CNOT, ket_CNOT]
  congr 1
  funext w
  by_cases hw : w = t
  · subst hw
    simp [Function.update_self, Function.update_of_ne h, add_assoc, CharTwo.add_self_eq_zero]
  · simp [Function.update_of_ne hw]

theorem toffoli_eval_mul_self (c₁ c₂ t : Wire n) (h₁₂ : c₁ ≠ c₂) (h₁t : c₁ ≠ t) (h₂t : c₂ ≠ t) :
    (Circuit.TOFF c₁ c₂ t h₁₂ h₁t h₂t).eval * (Circuit.TOFF c₁ c₂ t h₁₂ h₁t h₂t).eval = 1 := by
  apply Subtype.ext
  apply matrix_ext_ket
  intro β
  simp only [Submonoid.coe_mul, Submonoid.coe_one, ← Matrix.mulVec_mulVec, Matrix.one_mulVec]
  rw [ket_TOFF, ket_TOFF]
  congr 1
  funext w
  by_cases hw : w = t
  · subst hw
    simp [Function.update_self, Function.update_of_ne h₁t, Function.update_of_ne h₂t,
      add_assoc, CharTwo.add_self_eq_zero]
  · simp [Function.update_of_ne hw]

end KetHelpers

/-! ## Section 1: `CommutesWithWire`, `GlobalCleanSimulates`, & `tempAndProg` -/

section CleanSimulates

def CommutesWithWire {n : ℕ} (q : Wire n) (A : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) : Prop :=
  ∀ o : Fin 2,
    A * (QRegister.singleton q).basisOutcomeProjector o =
      (QRegister.singleton q).basisOutcomeProjector o * A

theorem CommutesWithWire.one {n : ℕ} (q : Wire n) :
    CommutesWithWire q (1 : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) := by
  intro o; simp

theorem CommutesWithWire.mul {n : ℕ} {q : Wire n}
    {A B : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ}
    (hA : CommutesWithWire q A) (hB : CommutesWithWire q B) :
    CommutesWithWire q (A * B) := by
  intro o
  rw [Matrix.mul_assoc, hB o, ← Matrix.mul_assoc, hA o, Matrix.mul_assoc]

theorem CommutesWithWire.conjTranspose {n : ℕ} {q : Wire n}
    {A : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ}
    (hA : CommutesWithWire q A) :
    CommutesWithWire q Aᴴ := by
  intro o
  have h := congrArg Matrix.conjTranspose (hA o)
  simpa only [Matrix.conjTranspose_mul, QRegister.basisOutcomeProjector_conjTranspose] using h.symm

theorem CommutesWithWire.embedMatrix_of_not_mem {n k : ℕ} {q : Wire n}
    (r : QRegister k n) (hq : q ∉ Set.range r.wires)
    (M : Matrix (Fin (2 ^ k)) (Fin (2 ^ k)) ℂ) :
    CommutesWithWire q (r.embedMatrix M) := by
  intro o
  have hdisj : r.DisjointWires (QRegister.singleton q) := by
    rw [QRegister.disjoint_iff]
    intro i j hij
    have hj : (QRegister.singleton q) j = q := rfl
    exact hq ⟨i, hij.trans hj⟩
  exact r.embedMatrix_comm_basisOutcomeProjector_of_disjoint (QRegister.singleton q) hdisj M o

theorem CommutesWithWire.of_ket_map {n : ℕ} {q : Wire n}
    {A : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ}
    (h : ∀ β : BitAssignment n, ∃ (α : ℂ) (β' : BitAssignment n),
      β' q = β q ∧ A.mulVec (ket β) = α • ket β') :
    CommutesWithWire q A := by
  intro o
  apply matrix_ext_ket
  intro β
  obtain ⟨α, β', hq, hA⟩ := h β
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hA, Matrix.mulVec_smul,
    ket_projector, ket_projector, hq]
  by_cases hb : β q = (o.val : ZMod 2)
  · simp only [hb, ↓reduceIte]; exact hA
  · simp only [hb, ↓reduceIte, Matrix.mulVec_zero, smul_zero]

theorem CommutesWithWire.cnot_of_ne_target {n : ℕ} {q c t : Wire n} (hct : c ≠ t) (hq : q ≠ t) :
    CommutesWithWire q (Circuit.CNOT c t hct).eval.1 :=
  CommutesWithWire.of_ket_map fun β ↦
    ⟨1, Function.update β t (β t + β c), Function.update_of_ne hq _ β,
      by simpa using ket_CNOT c t hct β⟩

theorem CommutesWithWire.toffoli_of_ne_target {n : ℕ} {q c₁ c₂ t : Wire n}
    (h₁₂ : c₁ ≠ c₂) (h₁t : c₁ ≠ t) (h₂t : c₂ ≠ t) (hq : q ≠ t) :
    CommutesWithWire q (Circuit.TOFF c₁ c₂ t h₁₂ h₁t h₂t).eval.1 :=
  CommutesWithWire.of_ket_map fun β ↦
    ⟨1, Function.update β t (β t + β c₁ * β c₂), Function.update_of_ne hq _ β,
      by simpa using ket_TOFF c₁ c₂ t h₁₂ h₁t h₂t β⟩

noncomputable def bitProj {n : ℕ} (q : Wire n) (b : ZMod 2) :
    Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ :=
  (QRegister.singleton q).basisOutcomeProjector (if b = 0 then 0 else 1)

theorem ket_bitProj {n : ℕ} (q : Wire n) (b : ZMod 2) (β : BitAssignment n) :
    (bitProj q b).mulVec (ket β) = if β q = b then ket β else 0 := by
  rcases zmod2_eq_zero_or_one b with rfl | rfl
  · simpa [bitProj] using ket_projector q 0 β
  · simpa [bitProj] using ket_projector q 1 β

theorem CommutesWithWire.comm_bitProj {n : ℕ} {q : Wire n}
    {A : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ} (hA : CommutesWithWire q A) (b : ZMod 2) :
    A * bitProj q b = bitProj q b * A :=
  hA (if b = 0 then 0 else 1)

theorem cnot_conj_commutesWithWire_target {n : ℕ} {c t : Wire n} (hct : c ≠ t)
    {U : Unitary (2 ^ n)}
    (hc : CommutesWithWire c U.1) (ht : CommutesWithWire t U.1) :
    let C := (Circuit.CNOT c t hct).eval
    CommutesWithWire t (C * U * C).1 := by
  intro C o
  let V := C * U * C
  have hsub : ∀ {W : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ},
      CommutesWithWire c W → CommutesWithWire t W →
      (QRegister.singleton t).basisOutcomeProjector o * (C.1 * W * C.1) *
        (QRegister.singleton t).basisOutcomeProjector o =
      (C.1 * W * C.1) * (QRegister.singleton t).basisOutcomeProjector o := by
    intro W hWc hWt
    apply matrix_ext_ket
    intro β
    simp only [← Matrix.mulVec_mulVec, ket_projector]
    by_cases hbt : β t = (o.val : ZMod 2)
    · simp only [hbt, ↓reduceIte]
      have hC1 : C.1.mulVec (ket β) = ket (Function.update β t (β t + β c)) := ket_CNOT c t hct β
      rw [hC1]
      let β₁ := Function.update β t (β t + β c)
      let ψ := W.mulVec (ket β₁)
      change ((QRegister.singleton t).basisOutcomeProjector o).mulVec (C.1.mulVec ψ) =
        C.1.mulVec ψ
      have hfix_c : (bitProj c (β c)).mulVec ψ = ψ := by
        dsimp [ψ]
        rw [Matrix.mulVec_mulVec, ← hWc.comm_bitProj, ← Matrix.mulVec_mulVec, ket_bitProj]
        simp [β₁, Function.update_of_ne hct]
      have hfix_t : (bitProj t (β t + β c)).mulVec ψ = ψ := by
        dsimp [ψ]
        rw [Matrix.mulVec_mulVec, ← hWt.comm_bitProj, ← Matrix.mulVec_mulVec, ket_bitProj]
        simp [β₁]
      have hψ_exp : ψ = (bitProj c (β c)).mulVec ((bitProj t (β t + β c)).mulVec ψ) := by
        rw [hfix_t, hfix_c]
      rw [hψ_exp, vec_eq_sum_ket ψ]
      simp only [Matrix.mulVec_sum, Matrix.mulVec_smul, ket_bitProj]
      refine Finset.sum_congr rfl fun g _ ↦ ?_
      congr 1
      by_cases hgt : basisBits n g t = β t + β c
      · simp only [hgt, ↓reduceIte, ket_bitProj]
        by_cases hgc : basisBits n g c = β c
        · simp only [hgc, ↓reduceIte]
          dsimp only [C]
          rw [ket_CNOT, ket_projector]
          have hsum : basisBits n g t + basisBits n g c = (o.val : ZMod 2) := by
            rw [hgt, hgc, add_assoc, CharTwo.add_self_eq_zero, add_zero, hbt]
          simp [hsum]
        · simp [hgc]
      · simp [hgt]
    · simp [hbt]
  have h1 := hsub hc ht
  have hC_herm : C.1ᴴ = C.1 := unitary_conjTranspose_eq_self_of_mul_self C (cnot_eval_mul_self c t
    hct)
  have h2 := congrArg Matrix.conjTranspose (hsub hc.conjTranspose ht.conjTranspose)
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    QRegister.basisOutcomeProjector_conjTranspose, hC_herm, ← Matrix.mul_assoc] at h2
  have h1' : (QRegister.singleton t).basisOutcomeProjector o * (C.1 * U.1 * C.1) *
      (QRegister.singleton t).basisOutcomeProjector o =
      (C.1 * U.1 * C.1) * (QRegister.singleton t).basisOutcomeProjector o := h1
  have h2' : (QRegister.singleton t).basisOutcomeProjector o * (C.1 * U.1 * C.1) *
      (QRegister.singleton t).basisOutcomeProjector o =
      (QRegister.singleton t).basisOutcomeProjector o * (C.1 * U.1 * C.1) := by
    simpa only [← Matrix.mul_assoc] using h2
  exact h1'.symm.trans h2'

theorem toffoli_conj_commutesWithWire_ancilla {n : ℕ} {c₁ c₂ anc : Wire n}
    (h₁₂ : c₁ ≠ c₂) (h₁a : c₁ ≠ anc) (h₂a : c₂ ≠ anc)
    {U : Unitary (2 ^ n)}
    (hc₁ : CommutesWithWire c₁ U.1) (hc₂ : CommutesWithWire c₂ U.1)
    (hanc : CommutesWithWire anc U.1) :
    let T_anc := (Circuit.TOFF c₁ c₂ anc h₁₂ h₁a h₂a).eval
    CommutesWithWire anc (T_anc * U * T_anc).1 := by
  intro T_anc o
  let V := T_anc * U * T_anc
  have hsub : ∀ {W : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ},
      CommutesWithWire c₁ W → CommutesWithWire c₂ W → CommutesWithWire anc W →
      (QRegister.singleton anc).basisOutcomeProjector o * (T_anc.1 * W * T_anc.1) *
        (QRegister.singleton anc).basisOutcomeProjector o =
      (T_anc.1 * W * T_anc.1) * (QRegister.singleton anc).basisOutcomeProjector o := by
    intro W hW₁ hW₂ hWa
    apply matrix_ext_ket
    intro β
    simp only [← Matrix.mulVec_mulVec, ket_projector]
    by_cases hba : β anc = (o.val : ZMod 2)
    · simp only [hba, ↓reduceIte]
      have hT1 : T_anc.1.mulVec (ket β) = ket (Function.update β anc (β anc + β c₁ * β c₂)) :=
        ket_TOFF c₁ c₂ anc h₁₂ h₁a h₂a β
      rw [hT1]
      let β₁ := Function.update β anc (β anc + β c₁ * β c₂)
      let ψ := W.mulVec (ket β₁)
      change ((QRegister.singleton anc).basisOutcomeProjector o).mulVec (T_anc.1.mulVec ψ) =
        T_anc.1.mulVec ψ
      have hfix₁ : (bitProj c₁ (β c₁)).mulVec ψ = ψ := by
        dsimp [ψ]
        rw [Matrix.mulVec_mulVec, ← hW₁.comm_bitProj, ← Matrix.mulVec_mulVec, ket_bitProj]
        simp [β₁, Function.update_of_ne h₁a]
      have hfix₂ : (bitProj c₂ (β c₂)).mulVec ψ = ψ := by
        dsimp [ψ]
        rw [Matrix.mulVec_mulVec, ← hW₂.comm_bitProj, ← Matrix.mulVec_mulVec, ket_bitProj]
        simp [β₁, Function.update_of_ne h₂a]
      have hfixa : (bitProj anc (β anc + β c₁ * β c₂)).mulVec ψ = ψ := by
        dsimp [ψ]
        rw [Matrix.mulVec_mulVec, ← hWa.comm_bitProj, ← Matrix.mulVec_mulVec, ket_bitProj]
        simp [β₁]
      have hψ_exp : ψ = (bitProj c₁ (β c₁)).mulVec
          ((bitProj c₂ (β c₂)).mulVec ((bitProj anc (β anc + β c₁ * β c₂)).mulVec ψ)) := by
        rw [hfixa, hfix₂, hfix₁]
      rw [hψ_exp, vec_eq_sum_ket ψ]
      simp only [Matrix.mulVec_sum, Matrix.mulVec_smul, ket_bitProj]
      refine Finset.sum_congr rfl fun g _ ↦ ?_
      congr 1
      by_cases hga : basisBits n g anc = β anc + β c₁ * β c₂
      · simp only [hga, ↓reduceIte, ket_bitProj]
        by_cases hg₂ : basisBits n g c₂ = β c₂
        · simp only [hg₂, ↓reduceIte, ket_bitProj]
          by_cases hg₁ : basisBits n g c₁ = β c₁
          · simp only [hg₁, ↓reduceIte]
            dsimp only [T_anc]
            rw [ket_TOFF, ket_projector]
            have hsum : basisBits n g anc + basisBits n g c₁ * basisBits n g c₂ =
                (o.val : ZMod 2) := by
              rw [hga, hg₁, hg₂, add_assoc, CharTwo.add_self_eq_zero, add_zero, hba]
            rw [hsum, Function.update_self]
            simp only [↓reduceIte]
          · simp [hg₁]
        · simp [hg₂]
      · simp [hga]
    · simp [hba]
  have h1 := hsub hc₁ hc₂ hanc
  have hT_herm : T_anc.1ᴴ = T_anc.1 :=
    unitary_conjTranspose_eq_self_of_mul_self T_anc (toffoli_eval_mul_self c₁ c₂ anc h₁₂ h₁a h₂a)
  have h2 := congrArg Matrix.conjTranspose
    (hsub hc₁.conjTranspose hc₂.conjTranspose hanc.conjTranspose)
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    QRegister.basisOutcomeProjector_conjTranspose, hT_herm, ← Matrix.mul_assoc] at h2
  have h1' : (QRegister.singleton anc).basisOutcomeProjector o * (T_anc.1 * U.1 * T_anc.1) *
      (QRegister.singleton anc).basisOutcomeProjector o =
      (T_anc.1 * U.1 * T_anc.1) * (QRegister.singleton anc).basisOutcomeProjector o := h1
  have h2' : (QRegister.singleton anc).basisOutcomeProjector o * (T_anc.1 * U.1 * T_anc.1) *
      (QRegister.singleton anc).basisOutcomeProjector o =
      (QRegister.singleton anc).basisOutcomeProjector o * (T_anc.1 * U.1 * T_anc.1) := by
    simpa only [← Matrix.mul_assoc] using h2
  exact h1'.symm.trans h2'

def regInit {m n : ℕ} (r : QRegister (m + 1) n) : QRegister m n :=
  r.compose ⟨Fin.castSucc, Fin.castSucc_injective m⟩

/-- Global clean-workspace unitary simulation compatible with
`DynamicCircuit.RealizesEmbeddedUnitaryWithCleanWorkspace`. -/
def GlobalCleanSimulates {Var : Type} [Fintype Var] [DecidableEq Var] {n m : ℕ} [NeZero (2 ^ n)]
    (rClean : QRegister m n) (U : Unitary (2 ^ n)) (d : DynamicCircuit Var n) : Prop :=
  (U.1 * rClean.basisOutcomeProjector 0 = rClean.basisOutcomeProjector 0 * U.1) ∧
  ∀ M : Observable (Fin (2 ^ n)), ∃ M' : Observable (Fin (2 ^ n)),
    wp d.compile (fun _ ↦ M) = (fun _ ↦ M') ∧
    rClean.basisOutcomeProjector 0 * M'.1.1 * rClean.basisOutcomeProjector 0 =
      rClean.basisOutcomeProjector 0 * (U.1ᴴ * M.1.1 * U.1) * rClean.basisOutcomeProjector 0

section GlobalCleanCombinators

variable {Var : Type} [Fintype Var] [DecidableEq Var] {n m : ℕ} [NeZero (2 ^ n)]

theorem GlobalCleanSimulates.identity (rClean : QRegister m n) :
    GlobalCleanSimulates (Var := Var) rClean 1 .identity :=
  ⟨by simp, fun M ↦ ⟨M, rfl, by simp⟩⟩

theorem GlobalCleanSimulates.circuit (rClean : QRegister m n) (c : Circuit n)
    (hcomm : c.eval.1 * rClean.basisOutcomeProjector 0 =
      rClean.basisOutcomeProjector 0 * c.eval.1) :
    GlobalCleanSimulates (Var := Var) rClean c.eval (.circuit c) := by
  refine ⟨hcomm, fun M ↦ ⟨qcQAssignObsMap c.eval M, ?_, ?_⟩⟩
  · funext σ
    rw [DynamicCircuit.compile_circuit, DynamicCircuit.qc_wp_circuit_compile]
    rfl
  · simp [qcQAssignObsMap, Matrix.star_eq_conjTranspose, Matrix.mul_assoc]

theorem GlobalCleanSimulates.seq {rClean : QRegister m n}
    {U₁ U₂ : Unitary (2 ^ n)} {d₁ d₂ : DynamicCircuit Var n}
    (h₁ : GlobalCleanSimulates rClean U₁ d₁)
    (h₂ : GlobalCleanSimulates rClean U₂ d₂) :
    GlobalCleanSimulates rClean (U₂ * U₁) (.seq d₁ d₂) := by
  let P := rClean.basisOutcomeProjector 0
  have hP_herm : Pᴴ = P := rClean.basisOutcomeProjector_conjTranspose 0
  refine ⟨?_, fun M ↦ ?_⟩
  · change (U₂.1 * U₁.1) * P = P * (U₂.1 * U₁.1)
    rw [Matrix.mul_assoc, h₁.1, ← Matrix.mul_assoc, h₂.1, Matrix.mul_assoc]
  · obtain ⟨M₂, hwp₂, hproj₂⟩ := h₂.2 M
    obtain ⟨M₁, hwp₁, hproj₁⟩ := h₁.2 M₂
    refine ⟨M₁, ?_, ?_⟩
    · simp only [DynamicCircuit.compile_seq, wp, hwp₂, hwp₁]
    · have hComm1 : U₁.1 * P = P * U₁.1 := h₁.1
      have hCommStar : U₁.1ᴴ * P = P * U₁.1ᴴ := by
        have h := congrArg Matrix.conjTranspose hComm1
        simpa only [Matrix.conjTranspose_mul, hP_herm] using h.symm
      change P * M₁.1.1 * P = P * ((U₂.1 * U₁.1)ᴴ * M.1.1 * (U₂.1 * U₁.1)) * P
      calc P * M₁.1.1 * P = P * (U₁.1ᴴ * M₂.1.1 * U₁.1) * P := hproj₁
        _ = (P * U₁.1ᴴ) * M₂.1.1 * (U₁.1 * P) := by simp only [Matrix.mul_assoc]
        _ = U₁.1ᴴ * (P * M₂.1.1 * P) * U₁.1 := by
            rw [← hCommStar, hComm1]; simp only [Matrix.mul_assoc]
        _ = U₁.1ᴴ * (P * (U₂.1ᴴ * M.1.1 * U₂.1) * P) * U₁.1 := by rw [hproj₂]
        _ = (U₁.1ᴴ * P) * U₂.1ᴴ * M.1.1 * U₂.1 * (P * U₁.1) := by simp only [Matrix.mul_assoc]
        _ = P * ((U₂.1 * U₁.1)ᴴ * M.1.1 * (U₂.1 * U₁.1)) * P := by
            rw [hCommStar, ← hComm1]
            simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]

theorem GlobalCleanSimulates.congrUnitary {rClean : QRegister m n}
    {U U' : Unitary (2 ^ n)} {d : DynamicCircuit Var n}
    (hd : GlobalCleanSimulates rClean U d)
    (heq : U.1 * rClean.basisOutcomeProjector 0 = U'.1 * rClean.basisOutcomeProjector 0)
    (hcomm' : U'.1 * rClean.basisOutcomeProjector 0 = rClean.basisOutcomeProjector 0 * U'.1) :
    GlobalCleanSimulates rClean U' d := by
  let P := rClean.basisOutcomeProjector 0
  have hP_herm : Pᴴ = P := rClean.basisOutcomeProjector_conjTranspose 0
  have hadj : P * U.1ᴴ = P * U'.1ᴴ := by
    have h := congrArg Matrix.conjTranspose heq
    simpa only [P, Matrix.conjTranspose_mul, hP_herm] using h
  refine ⟨hcomm', fun M ↦ ?_⟩
  obtain ⟨M', hwp, hproj⟩ := hd.2 M
  refine ⟨M', hwp, ?_⟩
  calc P * M'.1.1 * P
      = (P * U.1ᴴ) * M.1.1 * (U.1 * P) := by simpa only [P, Matrix.mul_assoc] using hproj
    _ = (P * U'.1ᴴ) * M.1.1 * (U'.1 * P) := by rw [hadj, heq]
    _ = P * (U'.1ᴴ * M.1.1 * U'.1) * P := by simp only [Matrix.mul_assoc]

theorem GlobalCleanSimulates.ofRealizesEmbedded {k : ℕ}
    {rAct : QRegister k n} {rClean : QRegister m n}
    (hdisj : rAct.DisjointWires rClean)
    {u : Unitary (2 ^ k)} {d : DynamicCircuit Var n}
    (hd : DynamicCircuit.RealizesEmbeddedUnitaryWithCleanWorkspace rAct rClean u d) :
    GlobalCleanSimulates rClean (rAct.embedUnitary u) d :=
  ⟨rAct.embedMatrix_comm_basisOutcomeProjector_of_disjoint rClean hdisj u.1 0, hd⟩

theorem GlobalCleanSimulates.toRealizesEmbedded {k : ℕ}
    {rAct : QRegister k n} {rClean : QRegister m n}
    {u : Unitary (2 ^ k)} {d : DynamicCircuit Var n}
    (hd : GlobalCleanSimulates rClean (rAct.embedUnitary u) d) :
    DynamicCircuit.RealizesEmbeddedUnitaryWithCleanWorkspace rAct rClean u d :=
  hd.2

omit [Fintype Var] in
theorem wp_andUncompute_const [Finite Var] (v : Var) (c₁ c₂ anc : Wire n) (h₁₂ : c₁ ≠ c₂)
    (M : Observable (Fin (2 ^ n))) :
    ∃ M_unc : Observable (Fin (2 ^ n)),
      wp (DynamicCircuit.andUncompute v c₁ c₂ anc h₁₂).compile (fun _ ↦ M) = (fun _ ↦ M_unc) := by
  cases nonempty_fintype Var
  refine ⟨wp (DynamicCircuit.andUncompute v c₁ c₂ anc h₁₂).compile (fun _ ↦ M) 0, ?_⟩
  funext σ
  simp only [DynamicCircuit.andUncompute, DynamicCircuit.compile_seq,
    DynamicCircuit.compile_circuit, DynamicCircuit.compile_measure,
    DynamicCircuit.compile_qIf, QProg.measureRegister]
  change qcWpQAssign (Circuit.H anc).eval _ σ = qcWpQAssign (Circuit.H anc).eval _ 0
  simp only [qcWpQAssign]
  congr 1
  simp only [wp_qSeq, wp_qIf, qc_wp_qMeasure', qc_wp_qMeasure_apply, QCAssertion.subst_apply,
    Store.subst]
  congr 1
  funext o
  simp only [DynamicCircuit.qc_wp_circuit_compile, qcWpQAssign, Function.update_self]
  rfl

/-- Temporary-AND compute + body + 0-`T` uncompute gadget (`4 T`, `0 TOFF`). -/
def tempAndProg {Var : Type} {n : ℕ} (v : Var) (c₁ c₂ anc : Wire n)
    (h₁₂ : c₁ ≠ c₂) (h₁a : c₁ ≠ anc) (h₂a : c₂ ≠ anc)
    (body : DynamicCircuit Var n) : DynamicCircuit Var n :=
  .seq (DynamicCircuit.andCompute c₁ c₂ anc h₁a h₂a)
    (.seq body (DynamicCircuit.andUncompute v c₁ c₂ anc h₁₂))

@[simp]
theorem count_tempAndProg_t {Var : Type} {n : ℕ} (v : Var) (c₁ c₂ anc : Wire n)
    (h₁₂ : c₁ ≠ c₂) (h₁a : c₁ ≠ anc) (h₂a : c₂ ≠ anc)
    (body : DynamicCircuit Var n) :
    (tempAndProg v c₁ c₂ anc h₁₂ h₁a h₂a body).count PrimitiveGate.T =
      body.count PrimitiveGate.T + 4 := by
  simp only [tempAndProg, DynamicCircuit.count, DynamicCircuit.count_andCompute_t,
    DynamicCircuit.count_andUncompute_t, add_zero]
  omega

@[simp]
theorem count_tempAndProg_toff {Var : Type} {n : ℕ} (v : Var) (c₁ c₂ anc : Wire n)
    (h₁₂ : c₁ ≠ c₂) (h₁a : c₁ ≠ anc) (h₂a : c₂ ≠ anc)
    (body : DynamicCircuit Var n) :
    (tempAndProg v c₁ c₂ anc h₁₂ h₁a h₂a body).count PrimitiveGate.TOFF =
      body.count PrimitiveGate.TOFF := by
  simp [tempAndProg]

end GlobalCleanCombinators

end CleanSimulates

/-! ## Section 2: Register Slice Helpers, `cswapWireProg` & `cswapSpinBlockProg` -/

section SpinBlockCSWAP

end SpinBlockCSWAP

end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.OneHotSimulates

end
