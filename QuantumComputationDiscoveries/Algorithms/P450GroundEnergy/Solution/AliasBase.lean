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

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import QuantumComputation.Primitives.Hadamard
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.CleanDyn

/-!
# Verified Coherent Alias Sampling State Preparation (`CoherentAlias`)

Provides generic, verified coherent alias-sampling state preparation (`PREP` and `PREP†`) over
`PrimitiveGate` (`TOFF = 0`) using the shared 4-conjunct clean-ancilla weakest-precondition
contract `CleanRealizes` from `CleanDyn`:

1. **C*-Norm Perturbation & Controlled-Unitary Combinators:**
   - C*-algebra operator-norm contraction for `QRegister.embedMatrix`, unitary telescope bounds,
     and `Circuit.inverse` adjoint norm preservation.
   - Multi-controlled 1-qubit unitary combinators (`predCtrlUnitary`, `ctrlUnitary`,
     `ctrlZeroUnitary`, `andCtrlUnitary`, `andCtrlZeroUnitary`, `and3CtrlZeroUnitary`) and
     symbolic Gidney `andSandwich` conjugation via `ket` basis-vector evaluation.
2. **Exact `2`-`T` Controlled-Hadamard & Binary-Tree Uniform Superposition (`15`, `23`, `30`,
   `184`):**
   - Exact `2`-`T` zero-error `ctrlH : Circuit 2` (`I ⊕ H`) and `ctrlHZero : Circuit 2` (`H ⊕ I`).
   - Parameterized binary-tree uniform superposition circuits `unif15Prog`, `unif23Prog`,
     `unif30Prog` (`2 × 15` on `5` wires), and `unif184Prog` (`8 × 23` on `8` wires) plus exact
     inverse circuits (`*DagProg`), with exact state-vector proofs and operator-norm perturbation
     bounds against single-qubit `R_y` approximations (`CliffordTSynthesis` drop-in).
3. **Gidney Ripple-Borrow Comparator (`4 * b` `T` Gates) & Controlled-SWAP (`4 * d` `T` Gates):**
   - Verified `b`-bit `[coin ≥ keep]` comparator (`coinGeKeepProg`, plus `(b + 1)`-bit
     `keep ≤ 2 ^ b` variant `coinGeKeepExtProg`) using `b` `andCompute`s and `0`-`T`
     `andUncompute`s.
   - Verified `d`-bit controlled-SWAP (`cSwapPairsProg`) reusing a single clean scratch wire.
4. **Coherent Alias `PREP` & `PREP†` and Exact Discrete Alias Amplitude / Block-Encoding
   Theorems:**
   - Primary single-QROM mode (keeping `keep` in coherent garbage across `SELECT` so `PREP` and
     `PREP†` each invoke QROM once, bit-for-bit aligned with the outer and inner alias tables)
     plus secondary keep-uncomputed mode, supporting context `ctxBits` and payload `payBits`.
   - Exact marginal probabilities `(w i : ℝ) / (D * 2 ^ b)`, deterministic payload entanglement,
     SOS quadratic-form identity, and LCU block-encoding expectation identity.
-/

@[expose] public section

namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution
open QuantumComputation.Specs QuantumComputation.Specs.P450

open Operator QProg Matrix HermitianMat Real QuantumComputation.Specs
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution CleanDyn
open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator Circuit.Notation

/-- High-priority `NeZero (2 ^ k)` instance avoiding kernel unfolding of `2 ^ k` on wide
circuits. -/
instance (priority := 100000) instNeZeroTwoPowAlias (k : ℕ) : NeZero (2 ^ k) :=
  ⟨Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos k)⟩

namespace CoherentAlias

/-! ## Section 1: C*-Norm Perturbation, Basis-Ket & Controlled-Unitary Helpers -/

/-- Sub-register circuit placement into `CleanRealizes`. -/
theorem cleanRealizes_subcircuit {Var : Type} [Fintype Var] [DecidableEq Var]
    {N k₀ k s : ℕ} [NeZero (2 ^ N)]
    (v : Var) (rAct : QRegister k N) (subAct : QRegister k₀ k) (rScr : QRegister s N)
    (hdisj : rAct.DisjointWires rScr) (c : Circuit k₀)
    (htoff : c.count PrimitiveGate.TOFF = 0) :
    CleanRealizes v rAct rScr (subAct.embedUnitary c.eval)
      (.circuit (c.onRegister (rAct.compose subAct))) := by
  have hdisj₀ : (rAct.compose subAct).DisjointWires rScr := by
    rw [QRegister.disjoint_iff] at hdisj ⊢
    intro i j
    exact hdisj (subAct i) j
  exact (CleanRealizes.circuit v (rAct.compose subAct) rScr hdisj₀ c htoff).subregister
    hdisj Finset.Subset.rfl

/-! ### Basis-Ket Evaluation Helpers -/

/-- Basis state `|β⟩` indexed by a `BitAssignment n = Wire n → ZMod 2`. -/
noncomputable abbrev ket {n : ℕ} (β : BitAssignment n) : Fin (2 ^ n) → ℂ :=
  basisState ((basisBits n).symm β)

@[simp]
theorem basisBits_symm_apply {n : ℕ} (β : BitAssignment n) :
    basisBits n ((basisBits n).symm β) = β :=
  (basisBits n).apply_symm_apply β

@[simp]
theorem symm_basisBits_apply {n : ℕ} (j : Fin (2 ^ n)) :
    (basisBits n).symm (basisBits n j) = j :=
  (basisBits n).symm_apply_apply j

theorem matrix_ext_ket {n : ℕ} {A B : Operator (2 ^ n)}
    (h : ∀ β : BitAssignment n, A *ᵥ ket β = B *ᵥ ket β) : A = B := by
  ext i j
  have h1 : (Pi.single j 1 : Fin (2 ^ n) → ℂ) = ket (basisBits n j) := by
    simp [ket, basisState]
  have hij := congrFun (h (basisBits n j)) i
  simpa [← h1, Matrix.mulVec_single_one] using hij

/-- Update the bits of `β` on register `r` to `γ`. -/
noncomputable def writeReg {n k : ℕ} (β : BitAssignment n) (r : QRegister k n)
    (γ : BitAssignment k) : BitAssignment n :=
  basisBits n (r.replaceIndex ((basisBits n).symm β) ((basisBits k).symm γ))

@[simp]
theorem writeReg_apply_reg {n k : ℕ} (β : BitAssignment n) (r : QRegister k n)
    (γ : BitAssignment k) (i : Fin k) : writeReg β r γ (r i) = γ i := by
  simp [writeReg, QRegister.basisBits_replaceIndex_apply]

theorem writeReg_apply_of_not_mem {n k : ℕ} (β : BitAssignment n) (r : QRegister k n)
    (γ : BitAssignment k) (w : Wire n) (hw : w ∉ Set.range r.wires) :
    writeReg β r γ w = β w := by
  simp [writeReg, QRegister.basisBits_replaceIndex_of_not_mem _ _ _ _ hw]

theorem writeReg_eq_update {n k : ℕ} (β : BitAssignment n) (r : QRegister k n)
    (γ : BitAssignment k) (i₀ : Fin k) (hγ : ∀ i, i ≠ i₀ → γ i = β (r i)) :
    writeReg β r γ = Function.update β (r i₀) (γ i₀) := by
  funext w
  by_cases hw : w ∈ Set.range r.wires
  · obtain ⟨i, rfl⟩ := hw
    simp only [writeReg_apply_reg]
    by_cases hi : i = i₀
    · subst hi; simp
    · rw [Function.update_of_ne (fun h ↦ hi (r.wires.injective h)), hγ i hi]
  · rw [writeReg_apply_of_not_mem _ _ _ _ hw, Function.update_of_ne (fun h ↦ hw ⟨i₀, h.symm⟩)]

/-- Local index on `Fin (2 ^ k)` extracted from `β : BitAssignment n` along `r`. -/
noncomputable abbrev localIdx {n k : ℕ} (r : QRegister k n) (β : BitAssignment n) :
    Fin (2 ^ k) :=
  (basisBits k).symm (fun i ↦ β (r i))

theorem embedMatrix_mulVec_ket {n k : ℕ} (r : QRegister k n)
    (A : Operator (2 ^ k)) (β : BitAssignment n) :
    (r.embedMatrix A) *ᵥ ket β =
      ∑ l : Fin (2 ^ k), A l (localIdx r β) • ket (writeReg β r (basisBits k l)) := by
  have hext : r.extractIndex ((basisBits n).symm β) = localIdx r β := by
    simp [QRegister.extractIndex]
  have hcol (j : Fin (2 ^ k)) :
      A *ᵥ (Pi.single j 1) = ∑ l : Fin (2 ^ k), A l j • Pi.single l 1 := by
    funext x; simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  rw [ket, basisState, r.embedMatrix_mulVec_single_factors, hext, hcol,
    QRegister.tensorState_sum_left]
  refine Finset.sum_congr rfl fun l _ ↦ ?_
  rw [QRegister.tensorState_smul_left, QRegister.tensorState_single_replaceIndex]
  simp [writeReg, ket, basisState]

theorem embedMatrix_permMatrix_mulVec_ket {n k : ℕ} (r : QRegister k n)
    (σ : Equiv.Perm (Fin (2 ^ k))) (β : BitAssignment n) :
    (r.embedMatrix (Equiv.Perm.permMatrix ℂ σ)) *ᵥ ket β =
      ket (writeReg β r (basisBits k (σ.symm (localIdx r β)))) := by
  rw [embedMatrix_mulVec_ket, Finset.sum_eq_single (σ.symm (localIdx r β))]
  · simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]
  · intro l _ hl
    have hne : σ l ≠ localIdx r β := fun h ↦ hl (by rw [← h, Equiv.symm_apply_apply])
    simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, hne]
  · simp

theorem singleton_embedMatrix_mulVec_ket {n : ℕ} (q : Wire n) (A : Operator 2)
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

theorem ket_CNOT {n : ℕ} (c t : Wire n) (h : c ≠ t) (β : BitAssignment n) :
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

/-! ### Generic Controlled Single-Qubit Unitary Combinators -/

/-- `(m + 1)`-qubit matrix applying `M : Operator 2` to the last wire `m` on basis states whose
control bits `0 .. m - 1` satisfy `pred : Fin (2 ^ m) → Bool`, and `1` otherwise. -/
noncomputable def predCtrlMatrix {m : ℕ} (pred : Fin (2 ^ m) → Bool) (M : Operator 2) :
    Operator (2 ^ (m + 1)) :=
  let rCtrl : QRegister m (m + 1) := QRegister.block 0 m (by omega)
  let rTgt : QRegister 1 (m + 1) := QRegister.singleton (Fin.last m)
  rCtrl.embedMatrix (Matrix.diagonal fun c ↦ if pred c then (0 : ℂ) else 1) +
    rCtrl.embedMatrix (Matrix.diagonal fun c ↦ if pred c then (1 : ℂ) else 0) *
      rTgt.embedMatrix M

theorem predCtrlMatrix_conjTranspose {m : ℕ} (pred : Fin (2 ^ m) → Bool) (M : Operator 2) :
    (predCtrlMatrix pred M)ᴴ = predCtrlMatrix pred Mᴴ := by
  let rCtrl : QRegister m (m + 1) := QRegister.block 0 m (by omega)
  let rTgt : QRegister 1 (m + 1) := QRegister.singleton (Fin.last m)
  have hdisj : rCtrl.DisjointWires rTgt := by
    rw [QRegister.disjoint_iff]
    intro i j; fin_cases j
    simp [rCtrl, rTgt, QRegister.singleton, Fin.last, Fin.ext_iff]; omega
  have hcomm := rCtrl.embedMatrix_comm_of_disjoint rTgt hdisj
    (Matrix.diagonal fun c ↦ if pred c then (1 : ℂ) else 0) Mᴴ
  have hd0 : (Matrix.diagonal fun c : Fin (2 ^ m) ↦ if pred c then (0 : ℂ) else 1)ᴴ =
      Matrix.diagonal fun c ↦ if pred c then (0 : ℂ) else 1 := by
    ext i j
    by_cases hij : i = j
    · subst hij; by_cases hp : pred i <;> simp [hp]
    · have hji : j ≠ i := Ne.symm hij; simp [hij, hji]
  have hd1 : (Matrix.diagonal fun c : Fin (2 ^ m) ↦ if pred c then (1 : ℂ) else 0)ᴴ =
      Matrix.diagonal fun c ↦ if pred c then (1 : ℂ) else 0 := by
    ext i j
    by_cases hij : i = j
    · subst hij; by_cases hp : pred i <;> simp [hp]
    · have hji : j ≠ i := Ne.symm hij; simp [hij, hji]
  dsimp only [predCtrlMatrix]
  rw [conjTranspose_add, conjTranspose_mul, ← rCtrl.embedMatrix_conjTranspose,
    ← rCtrl.embedMatrix_conjTranspose, ← rTgt.embedMatrix_conjTranspose, hd0, hd1, ← hcomm]

theorem predCtrlMatrix_mul {m : ℕ} (pred : Fin (2 ^ m) → Bool) (M₁ M₂ : Operator 2) :
    predCtrlMatrix pred M₁ * predCtrlMatrix pred M₂ = predCtrlMatrix pred (M₁ * M₂) := by
  let rCtrl : QRegister m (m + 1) := QRegister.block 0 m (by omega)
  let rTgt : QRegister 1 (m + 1) := QRegister.singleton (Fin.last m)
  have hdisj : rCtrl.DisjointWires rTgt := by
    rw [QRegister.disjoint_iff]
    intro i j; fin_cases j
    simp [rCtrl, rTgt, QRegister.singleton, Fin.last, Fin.ext_iff]; omega
  let P₀ := rCtrl.embedMatrix (Matrix.diagonal fun c ↦ if pred c then (0 : ℂ) else 1)
  let P₁ := rCtrl.embedMatrix (Matrix.diagonal fun c ↦ if pred c then (1 : ℂ) else 0)
  have hP₀₀ : P₀ * P₀ = P₀ := by
    dsimp [P₀]; rw [← rCtrl.embedMatrix_mul, Matrix.diagonal_mul_diagonal]
    congr 1; congr 1; funext c; by_cases hp : pred c <;> simp [hp]
  have hP₁₁ : P₁ * P₁ = P₁ := by
    dsimp [P₁]; rw [← rCtrl.embedMatrix_mul, Matrix.diagonal_mul_diagonal]
    congr 1; congr 1; funext c; by_cases hp : pred c <;> simp [hp]
  have hP₀₁ : P₀ * P₁ = 0 := by
    dsimp [P₀, P₁]; rw [← rCtrl.embedMatrix_mul, Matrix.diagonal_mul_diagonal]
    convert rCtrl.embedMatrix_zero; ext i j
    by_cases hij : i = j
    · subst hij; by_cases hp : pred i <;> simp [hp]
    · simp [hij]
  have hP₁₀ : P₁ * P₀ = 0 := by
    dsimp [P₀, P₁]; rw [← rCtrl.embedMatrix_mul, Matrix.diagonal_mul_diagonal]
    convert rCtrl.embedMatrix_zero; ext i j
    by_cases hij : i = j
    · subst hij; by_cases hp : pred i <;> simp [hp]
    · simp [hij]
  have hc₀ : rTgt.embedMatrix M₁ * P₀ = P₀ * rTgt.embedMatrix M₁ :=
    (rCtrl.embedMatrix_comm_of_disjoint rTgt hdisj _ M₁).symm
  have hc₁ : rTgt.embedMatrix M₁ * P₁ = P₁ * rTgt.embedMatrix M₁ :=
    (rCtrl.embedMatrix_comm_of_disjoint rTgt hdisj _ M₁).symm
  change (P₀ + P₁ * rTgt.embedMatrix M₁) * (P₀ + P₁ * rTgt.embedMatrix M₂) =
    P₀ + P₁ * rTgt.embedMatrix (M₁ * M₂)
  rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, hP₀₀,
    ← Matrix.mul_assoc P₀ P₁, hP₀₁, zero_mul, add_zero,
    Matrix.mul_assoc P₁ (rTgt.embedMatrix M₁) P₀, hc₀, ← Matrix.mul_assoc P₁ P₀, hP₁₀, zero_mul,
    zero_add]
  have hterm : P₁ * rTgt.embedMatrix M₁ * (P₁ * rTgt.embedMatrix M₂) =
      P₁ * rTgt.embedMatrix (M₁ * M₂) := by
    calc P₁ * rTgt.embedMatrix M₁ * (P₁ * rTgt.embedMatrix M₂)
        = P₁ * (rTgt.embedMatrix M₁ * P₁) * rTgt.embedMatrix M₂ := by simp [Matrix.mul_assoc]
      _ = (P₁ * P₁) * (rTgt.embedMatrix M₁ * rTgt.embedMatrix M₂) := by
            rw [hc₁]; simp [Matrix.mul_assoc]
      _ = P₁ * rTgt.embedMatrix (M₁ * M₂) := by rw [hP₁₁, ← rTgt.embedMatrix_mul]
  rw [hterm]

theorem predCtrlMatrix_one {m : ℕ} (pred : Fin (2 ^ m) → Bool) :
    predCtrlMatrix pred (1 : Operator 2) = 1 := by
  dsimp [predCtrlMatrix]
  rw [QRegister.embedMatrix_one, mul_one, ← QRegister.embedMatrix_add]
  convert QRegister.embedMatrix_one _
  ext i j
  by_cases hij : i = j
  · subst hij; by_cases hp : pred i <;> simp [hp]
  · simp [hij]

/-- Bundled `(m + 1)`-qubit controlled unitary for predicate `pred : Fin (2 ^ m) → Bool`. -/
noncomputable def predCtrlUnitary {m : ℕ} (pred : Fin (2 ^ m) → Bool) (V : Unitary 2) :
    Unitary (2 ^ (m + 1)) :=
  ⟨predCtrlMatrix pred V.1, by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
      predCtrlMatrix_conjTranspose, predCtrlMatrix_mul]
    have hV : V.1 * V.1ᴴ = 1 := by simpa [Matrix.star_eq_conjTranspose] using V.2.2
    rw [hV, predCtrlMatrix_one]⟩

@[simp]
theorem predCtrlUnitary_inv {m : ℕ} (pred : Fin (2 ^ m) → Bool) (V : Unitary 2) :
    (predCtrlUnitary pred V)⁻¹ = predCtrlUnitary pred V⁻¹ := by
  apply Subtype.ext
  have h1 : ((predCtrlUnitary pred V)⁻¹).1 = (predCtrlMatrix pred V.1)ᴴ := by
    simp [predCtrlUnitary, Matrix.star_eq_conjTranspose]
  have h2 : (predCtrlUnitary pred V⁻¹).1 = predCtrlMatrix pred V.1ᴴ := by
    simp [predCtrlUnitary, Matrix.star_eq_conjTranspose]
  rw [h1, h2, predCtrlMatrix_conjTranspose]

/-- Action of `rSub.embedMatrix (predCtrlMatrix pred M)` on a basis ket `ket β`: if `pred` holds
on the control bits of `β`, applies `M` to target wire `rSub (Fin.last m)`; otherwise acts as
identity. -/
theorem ket_embed_predCtrlMatrix {m n : ℕ} (rSub : QRegister (m + 1) n)
    (pred : Fin (2 ^ m) → Bool) (M : Operator 2) (β : BitAssignment n) :
    (rSub.embedMatrix (predCtrlMatrix pred M)) *ᵥ ket β =
      if pred ((basisBits m).symm
          (fun i ↦ β ((rSub.compose (QRegister.block 0 m (by omega))) i))) then
        (QRegister.singleton (rSub (Fin.last m))).embedMatrix M *ᵥ ket β
      else
        ket β := by
  let rCtrl_loc : QRegister m (m + 1) := QRegister.block 0 m (by omega)
  let rTgt_loc : QRegister 1 (m + 1) := QRegister.singleton (Fin.last m)
  let rCtrl := rSub.compose rCtrl_loc
  let t := rSub (Fin.last m)
  have hdiag (f : Fin (2 ^ m) → ℂ) (γ : BitAssignment n) :
      (rCtrl.embedMatrix (Matrix.diagonal f)) *ᵥ ket γ =
        f (localIdx rCtrl γ) • ket γ := by
    rw [embedMatrix_mulVec_ket, Finset.sum_eq_single (localIdx rCtrl γ)]
    · have hw : writeReg γ rCtrl (basisBits m (localIdx rCtrl γ)) = γ := by
        funext w
        by_cases hw : w ∈ Set.range rCtrl.wires
        · obtain ⟨i, rfl⟩ := hw
          simp [writeReg, localIdx, QRegister.basisBits_replaceIndex_apply]
        · simp [writeReg, QRegister.basisBits_replaceIndex_of_not_mem _ _ _ _ hw]
      rw [Matrix.diagonal_apply_eq, hw]
    · intro l _ hl
      rw [Matrix.diagonal_apply_ne _ hl, zero_smul]
    · simp
  have hcomp_tgt : rSub.compose rTgt_loc = QRegister.singleton t := by
    ext i; fin_cases i; rfl
  have hdisj : rCtrl.DisjointWires (QRegister.singleton t) := by
    rw [QRegister.disjoint_iff]
    intro i j; fin_cases j
    refine rSub.wires.injective.ne ?_
    simp [rCtrl_loc, Fin.last, Fin.ext_iff]; omega
  have hcomm := rCtrl.embedMatrix_comm_of_disjoint (QRegister.singleton t) hdisj
    (Matrix.diagonal fun c ↦ if pred c then (1 : ℂ) else 0) M
  have hemb : rSub.embedMatrix (predCtrlMatrix pred M) =
      rCtrl.embedMatrix (Matrix.diagonal fun c ↦ if pred c then (0 : ℂ) else 1) +
      (QRegister.singleton t).embedMatrix M *
        rCtrl.embedMatrix (Matrix.diagonal fun c ↦ if pred c then (1 : ℂ) else 0) := by
    change rSub.embedMatrix
        (rCtrl_loc.embedMatrix _ + rCtrl_loc.embedMatrix _ * rTgt_loc.embedMatrix M) =
      (rSub.compose rCtrl_loc).embedMatrix _ +
        (QRegister.singleton t).embedMatrix M * (rSub.compose rCtrl_loc).embedMatrix _
    rw [rSub.embedMatrix_add, rSub.embedMatrix_mul, ← QRegister.embedMatrix_compose,
      ← QRegister.embedMatrix_compose, ← QRegister.embedMatrix_compose, hcomp_tgt]
    exact congrArg _ hcomm
  rw [hemb, Matrix.add_mulVec, ← Matrix.mulVec_mulVec, hdiag, hdiag, Matrix.mulVec_smul]
  dsimp only [localIdx, rCtrl, rCtrl_loc, t]
  by_cases hp : pred ((basisBits m).symm
      (fun i ↦ β (rSub.wires ((QRegister.block 0 m (by omega)).wires i))))
  · simp only [QRegister.compose_apply, hp, ↓reduceIte, zero_smul, one_smul, zero_add]
  · simp only [QRegister.compose_apply, hp, Bool.false_eq_true, ↓reduceIte, one_smul, zero_smul,
      add_zero]

/-- Computable bit-overwrite on a basis index `j : Fin (2 ^ n)`. -/
def setBitIdx {n : ℕ} (j : Fin (2 ^ n)) (t : Wire n) (b : ZMod 2) : Fin (2 ^ n) :=
  (basisBits n).symm (Function.update (basisBits n j) t b)

/-- Computable-index action of `rSub.embedMatrix (predCtrlMatrix pred M)` on `basisState j`. -/
theorem embed_predCtrlMatrix_mulVec_basisState {m n : ℕ} (rSub : QRegister (m + 1) n)
    (pred : Fin (2 ^ m) → Bool) (M : Operator 2) (j : Fin (2 ^ n)) :
    (rSub.embedMatrix (predCtrlMatrix pred M)) *ᵥ basisState j =
      if pred ((rSub.compose (QRegister.block 0 m (by omega))).extractIndex j) then
        let t := rSub (Fin.last m)
        let bit : Fin 2 := if basisBits n j t = 0 then 0 else 1
        M 0 bit • basisState (setBitIdx j t 0) + M 1 bit • basisState (setBitIdx j t 1)
      else
        basisState j := by
  have hj : basisState j = ket (basisBits n j) := by simp [ket]
  rw [hj, ket_embed_predCtrlMatrix, singleton_embedMatrix_mulVec_ket]
  rfl

theorem zmod2_add_self (x : ZMod 2) : x + x = 0 := by
  fin_cases x <;> decide

/-- `|1⟩`-controlled 1-qubit unitary on `2` wires (`wire 0` = control, `wire 1` = target). -/
noncomputable abbrev ctrlUnitary (V : Unitary 2) : Unitary 4 :=
  predCtrlUnitary (m := 1) (fun c ↦ c.val == 1) V

/-! ### Contiguous Block Arithmetic & Product-State Helpers -/

/-- Little-endian natural-number value extracted by a contiguous block `QRegister.block s k h`. -/
theorem extractIndex_block_val {s k n : ℕ} (h : s + k ≤ n) (g : Fin (2 ^ n)) :
    ((QRegister.block s k h).extractIndex g).val = (g.val / 2 ^ s) % 2 ^ k := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_mod_two_pow]
  by_cases hi : i < k
  · simp only [hi, decide_true, Bool.true_and, Nat.testBit_div_two_pow]
    have hb := (QRegister.block s k h).basisBits_extractIndex g ⟨i, hi⟩
    have hval : ((QRegister.block s k h) ⟨i, hi⟩).val = i + s := by
      simp [QRegister.block]; omega
    rw [basisBits_eq_testBit, basisBits_eq_testBit, hval] at hb
    have h01 : (1 : ZMod 2) ≠ 0 := by decide
    cases h1 : ((QRegister.block s k h).extractIndex g).val.testBit i <;>
      cases h2 : g.val.testBit (i + s) <;> simp_all
  · simp only [hi, decide_false, Bool.false_and]
    exact Nat.testBit_lt_two_pow
      (((QRegister.block s k h).extractIndex g).isLt.trans_le
        (Nat.pow_le_pow_right (by norm_num) (Nat.le_of_not_lt hi)))

/-- Product state `ψ₁ ⊗ ψ₂` across complementary blocks `0 .. m - 1` and `m .. m + k - 1`. -/
def blockProdState {m k : ℕ} (ψ₁ : Fin (2 ^ m) → ℂ) (ψ₂ : Fin (2 ^ k) → ℂ) :
    Fin (2 ^ (m + k)) → ℂ :=
  fun g ↦ ψ₁ ((QRegister.block 0 m (by omega)).extractIndex g) *
    ψ₂ ((QRegister.block m k (by omega)).extractIndex g)

theorem blockProdState_basisState_zero (m k : ℕ) :
    blockProdState (basisState (0 : Fin (2 ^ m))) (basisState (0 : Fin (2 ^ k))) =
      basisState (0 : Fin (2 ^ (m + k))) := by
  funext g
  have hlo := extractIndex_block_val (by omega : 0 + m ≤ m + k) g
  have hhi := extractIndex_block_val (by omega : m + k ≤ m + k) g
  have hhi_lt : g.val / 2 ^ m < 2 ^ k := by
    have hg : g.val < 2 ^ m * 2 ^ k := by simpa [pow_add] using g.isLt
    exact Nat.div_lt_of_lt_mul hg
  rw [_root_.pow_zero, Nat.div_one] at hlo
  rw [Nat.mod_eq_of_lt hhi_lt] at hhi
  by_cases hg0 : g = 0
  · subst hg0
    have he0 : (QRegister.block 0 m (by omega)).extractIndex (0 : Fin (2 ^ (m + k))) = 0 := by
      ext; simp [hlo]
    have he1 : (QRegister.block m k (by omega)).extractIndex (0 : Fin (2 ^ (m + k))) = 0 := by
      ext; simp [hhi]
    simp [blockProdState, basisState, he0, he1]
  · have hne : ¬((QRegister.block 0 m (by omega)).extractIndex g = 0 ∧
        (QRegister.block m k (by omega)).extractIndex g = 0) := by
      rintro ⟨h0, h1⟩
      apply hg0
      ext
      have hv0 : g.val % 2 ^ m = 0 := by simpa [h0] using hlo.symm
      have hv1 : g.val / 2 ^ m = 0 := by simpa [h1] using hhi.symm
      change g.val = 0
      rw [← Nat.div_add_mod g.val (2 ^ m), hv0, hv1]; simp
    rcases not_and_or.mp hne with h0 | h1
    · simp [blockProdState, basisState, Pi.single_apply, hg0, h0]
    · simp [blockProdState, basisState, Pi.single_apply, hg0, h1]

theorem embedMatrix_block_lo_mulVec_blockProdState {m k : ℕ}
    (A : Operator (2 ^ m)) (ψ₁ : Fin (2 ^ m) → ℂ) (ψ₂ : Fin (2 ^ k) → ℂ) :
    ((QRegister.block 0 m (by omega)).embedMatrix A) *ᵥ blockProdState ψ₁ ψ₂ =
      blockProdState (A *ᵥ ψ₁) ψ₂ := by
  let rLo : QRegister m (m + k) := QRegister.block 0 m (by omega)
  let rHi : QRegister k (m + k) := QRegister.block m k (by omega)
  have hdisj : rHi.DisjointWires rLo := by
    rw [QRegister.disjoint_iff]
    intro i j
    simp [rLo, rHi, Fin.ext_iff]; omega
  funext g
  rw [rLo.embedMatrix_mulVec_apply]
  dsimp only [blockProdState]
  trans (∑ loc : Fin (2 ^ m), (A (rLo.extractIndex g) loc * ψ₁ loc) * ψ₂ (rHi.extractIndex g))
  · refine Finset.sum_congr rfl fun loc _ ↦ ?_
    change A (rLo.extractIndex g) loc *
        (ψ₁ (rLo.extractIndex (rLo.replaceIndex g loc)) *
          ψ₂ (rHi.extractIndex (rLo.replaceIndex g loc))) =
      (A (rLo.extractIndex g) loc * ψ₁ loc) * ψ₂ (rHi.extractIndex g)
    rw [rLo.extractIndex_replaceIndex, rHi.extractIndex_replaceIndex_of_disjoint rLo hdisj,
      mul_assoc]
  · rw [← Finset.sum_mul]
    rfl

theorem embedMatrix_block_hi_mulVec_blockProdState {m k : ℕ}
    (B : Operator (2 ^ k)) (ψ₁ : Fin (2 ^ m) → ℂ) (ψ₂ : Fin (2 ^ k) → ℂ) :
    ((QRegister.block m k (by omega)).embedMatrix B) *ᵥ blockProdState ψ₁ ψ₂ =
      blockProdState ψ₁ (B *ᵥ ψ₂) := by
  let rLo : QRegister m (m + k) := QRegister.block 0 m (by omega)
  let rHi : QRegister k (m + k) := QRegister.block m k (by omega)
  have hdisj : rLo.DisjointWires rHi := by
    rw [QRegister.disjoint_iff]
    intro i j
    simp [rLo, rHi, Fin.ext_iff]; omega
  funext g
  rw [rHi.embedMatrix_mulVec_apply]
  dsimp only [blockProdState]
  trans (∑ loc : Fin (2 ^ k), ψ₁ (rLo.extractIndex g) * (B (rHi.extractIndex g) loc * ψ₂ loc))
  · refine Finset.sum_congr rfl fun loc _ ↦ ?_
    change B (rHi.extractIndex g) loc *
        (ψ₁ (rLo.extractIndex (rHi.replaceIndex g loc)) *
          ψ₂ (rHi.extractIndex (rHi.replaceIndex g loc))) =
      ψ₁ (rLo.extractIndex g) * (B (rHi.extractIndex g) loc * ψ₂ loc)
    rw [rHi.extractIndex_replaceIndex, rLo.extractIndex_replaceIndex_of_disjoint rHi hdisj]
    ring
  · rw [← Finset.mul_sum]
    rfl

/-! ## Section 2: Exact `2`-`T` Controlled-Hadamard & Binary-Tree Uniform Superposition -/

/-- Conjugate `CNOT 0 1` by a 1-qubit circuit `c` on target wire `1`. -/
def conjCnot01 (c : Circuit 1) : Circuit 2 :=
  c.onRegister (QRegister.singleton 1) ;;ᶜ
  Circuit.CNOT 0 1 (by decide) ;;ᶜ
  c.inverse.onRegister (QRegister.singleton 1)

theorem eval_cnot01 : (Circuit.CNOT (0 : Wire 2) 1 (by decide)).eval = ctrlUnitary Qubit.X := by
  apply Subtype.ext
  apply matrix_ext_ket; intro β
  rw [ket_CNOT, ← QRegister.whole_embedMatrix (n := 2) (ctrlUnitary Qubit.X).1]
  dsimp only [ctrlUnitary, predCtrlUnitary]
  symm
  refine (ket_embed_predCtrlMatrix (m := 1) (n := 2) (QRegister.whole 2)
    (fun c : Fin (2 ^ 1) ↦ c.val == 1) Qubit.X.1 β).trans ?_
  have hp : ∀ b : ZMod 2,
      (((basisBits 1).symm (fun _ ↦ b) : Fin (2 ^ 1)).val == 1) = decide (b = 1) := by decide
  have hr : ((QRegister.whole 2).compose (QRegister.block 0 1 (by omega))) =
      QRegister.singleton 0 := by ext i; fin_cases i; rfl
  have hl : (QRegister.whole 2) (Fin.last 1) = (1 : Wire 2) := rfl
  rw [hr, hl]
  change (if (((basisBits 1).symm (fun _ ↦ β 0) : Fin (2 ^ 1)).val == 1) then
      ((QRegister.singleton (1 : Wire 2)).embedMatrix !![0, 1; 1, 0]) *ᵥ ket β
    else ket β) = ket (Function.update β 1 (β 1 + β 0))
  rw [hp (β 0)]
  have h11 : (1 : ZMod 2) + 1 = 0 := rfl
  have hz2 : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  rcases hz2 (β 0) with h0 | h0
  · simp [h0]
  · simp only [h0, decide_true, ↓reduceIte, singleton_embedMatrix_mulVec_ket]
    rcases hz2 (β 1) with h1 | h1 <;> simp [h1, h11]

theorem eval_conjCnot01 (c : Circuit 1) :
    (conjCnot01 c).eval = ctrlUnitary (c.eval⁻¹ * Qubit.X * c.eval) := by
  apply Subtype.ext
  let rCtrl : QRegister 1 2 := QRegister.block 0 1 (by omega)
  let r₁ : QRegister 1 2 := QRegister.singleton 1
  have hr₁ : QRegister.singleton (Fin.last 1) = r₁ := rfl
  have hdisj : rCtrl.DisjointWires r₁ := by
    rw [QRegister.disjoint_iff]; intro i j; fin_cases i; fin_cases j; decide
  let P₀ := rCtrl.embedMatrix (Matrix.diagonal fun c : Fin 2 ↦ if c.val == 1 then (0 : ℂ) else 1)
  let P₁ := rCtrl.embedMatrix (Matrix.diagonal fun c : Fin 2 ↦ if c.val == 1 then (1 : ℂ) else 0)
  have hc₀ : r₁.embedMatrix (c.eval⁻¹).1 * P₀ = P₀ * r₁.embedMatrix (c.eval⁻¹).1 :=
    (rCtrl.embedMatrix_comm_of_disjoint r₁ hdisj _ (c.eval⁻¹).1).symm
  have hc₁ : r₁.embedMatrix (c.eval⁻¹).1 * P₁ = P₁ * r₁.embedMatrix (c.eval⁻¹).1 :=
    (rCtrl.embedMatrix_comm_of_disjoint r₁ hdisj _ (c.eval⁻¹).1).symm
  have hinv : (c.eval⁻¹).1 * c.eval.1 = 1 := congrArg Subtype.val (inv_mul_cancel c.eval)
  simp only [conjCnot01, Circuit.eval_seq, Circuit.eval_onRegister, Circuit.eval_inverse,
    eval_cnot01, Submonoid.coe_mul, QRegister.embedUnitary_val]
  change r₁.embedMatrix (c.eval⁻¹).1 * (P₀ + P₁ * r₁.embedMatrix Qubit.X.1) *
      r₁.embedMatrix c.eval.1 =
    P₀ + P₁ * r₁.embedMatrix ((c.eval⁻¹).1 * Qubit.X.1 * c.eval.1)
  rw [Matrix.mul_add, Matrix.add_mul, hc₀, Matrix.mul_assoc P₀, ← r₁.embedMatrix_mul, hinv,
    r₁.embedMatrix_one, Matrix.mul_one, ← Matrix.mul_assoc (r₁.embedMatrix (c.eval⁻¹).1) P₁,
    hc₁, Matrix.mul_assoc P₁, Matrix.mul_assoc P₁, ← r₁.embedMatrix_mul, ← r₁.embedMatrix_mul,
    Matrix.mul_assoc]

/-- Half-Hadamard 1-qubit word `S Z H T H S` (`1` `T` gate) used in `ctrlH`. -/
def ctrlHHalf : Circuit 1 :=
  Circuit.S 0 ;;ᶜ Circuit.Z 0 ;;ᶜ Circuit.H 0 ;;ᶜ Circuit.T 0 ;;ᶜ Circuit.H 0 ;;ᶜ Circuit.S 0

/-- Exact `2`-`T`, `0`-`TOFF` Controlled-Hadamard (`I ⊕ H`: wire `0` is `|1⟩`-active control,
wire `1` is target). -/
def ctrlH : Circuit 2 :=
  conjCnot01 ctrlHHalf

@[simp] theorem count_ctrlH_toff : ctrlH.count PrimitiveGate.TOFF = 0 := rfl
@[simp] theorem count_ctrlH_t : ctrlH.count PrimitiveGate.T = 2 := rfl
theorem mul_mat2 (a₁ b₁ c₁ d₁ a₂ b₂ c₂ d₂ : ℂ) :
    !![a₁, b₁; c₁, d₁] * !![a₂, b₂; c₂, d₂] =
      !![a₁ * a₂ + b₁ * c₂, a₁ * b₂ + b₁ * d₂;
         c₁ * a₂ + d₁ * c₂, c₁ * b₂ + d₁ * d₂] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- `ctrlH` evaluates to `ctrlUnitary Qubit.H` with zero error. -/
theorem eval_ctrlH : ctrlH.eval = ctrlUnitary Qubit.H := by
  rw [ctrlH, eval_conjCnot01]
  apply congrArg ctrlUnitary
  rw [mul_assoc, inv_mul_eq_iff_eq_mul]
  apply Subtype.ext
  have hreg : ∀ U : Unitary (2 ^ 1),
      ((QRegister.singleton (0 : Wire 1)).embedUnitary U).1 = U.1 := by
    intro U
    have h0 : QRegister.singleton (0 : Wire 1) = QRegister.whole 1 := by
      ext i; fin_cases i; rfl
    rw [h0, QRegister.whole_embedUnitary]
  let r2 : ℂ := ((√2 : ℝ) : ℂ)⁻¹
  have hr2_sq : r2 ^ 2 = 1 / 2 := by
    dsimp [r2]
    rw [inv_pow]
    have hsq : ((√2 : ℝ) : ℂ) ^ 2 = 2 := by norm_cast; exact Real.sq_sqrt (by norm_num)
    rw [hsq]; ring
  have hs_mat : (PrimitiveGate.eval (k := 1) .s).1 = !![1, 0; 0, Complex.I] := by
    rw [PrimitiveGate.eval_s_val]
    ext i j; fin_cases i <;> fin_cases j <;> simp
  have hz_mat : (PrimitiveGate.eval (k := 1) .z).1 = !![1, 0; 0, -1] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [PrimitiveGate.eval, Qubit.Z]
  have hh_mat : (PrimitiveGate.eval (k := 1) .h).1 = !![r2, r2; r2, -r2] := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [PrimitiveGate.eval, Qubit.H, Complex.real_smul, r2]
  have ht_mat : (PrimitiveGate.eval (k := 1) .t).1 = !![1, 0; 0, (1 + Complex.I) * r2] := by
    rw [PrimitiveGate.eval_t_val]
    ext i j; fin_cases i <;> fin_cases j <;> simp [r2, div_eq_mul_inv]
  have hx_mat : Qubit.X.1 = !![(0 : ℂ), 1; 1, 0] := rfl
  have hH_mat : Qubit.H.1 = !![r2, r2; r2, -r2] := hh_mat
  simp only [ctrlHHalf, Circuit.eval_seq, Submonoid.coe_mul,
    Circuit.S, Circuit.Z, Circuit.H, Circuit.T, Circuit.eval_single, hreg,
    hs_mat, hz_mat, hh_mat, ht_mat, hx_mat, hH_mat]
  repeat rw [mul_mat2]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Fin.zero_eta, Fin.mk_one, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  all_goals
    ring_nf
    try rw [Complex.I_sq]
    try rw [show Complex.I ^ 3 = Complex.I * Complex.I ^ 2 by ring, Complex.I_sq]
    ring_nf
    try rw [hr2_sq]
    try rw [show r2 ^ 3 = r2 * r2 ^ 2 by ring, hr2_sq]
    try rw [show r2 ^ 4 = (r2 ^ 2) ^ 2 by ring, hr2_sq]
    ring

end CoherentAlias
end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution
