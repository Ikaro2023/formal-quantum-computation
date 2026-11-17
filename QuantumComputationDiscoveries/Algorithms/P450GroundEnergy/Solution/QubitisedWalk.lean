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

public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.CleanDyn

/-!
# Spectral-Amplification Walk, Dihedral Reflection-Reversal & Clean `DynamicCircuit` Loop

Provides the verified, `TOFF = 0` spectral-amplification quantum walk engine for the Cytochrome
P450 Compound I ground-state energy algorithm:

1. **`CleanRealizes` & Multiplexed QPE–Walk Unitaries (`qpeMuxUnitary`):**
   - Exact 4-conjunct clean-ancilla weakest-precondition contract `CleanRealizes` (matching
     `QuantumComputation.Specs.CleanRealizes` definitionally), sequential composition, and
     subregister lifting.
   - Block-diagonal QPE-multiplexed unitary `qpeMuxUnitary` on `rQPE ++ rWalk` with homomorphism
     laws and subspace/superposition action lemmas.
2. **Two-Projector Jordan Plane Eigenvalue Decomposition:**
   - Orthogonal projectors `projIn`, `projMid`, `pulledProjMid`, involutory reflections
     `reflInUnitary` ($2\Pi_{\mathrm{in}} - I$), `reflMidUnitary` ($I - 2\Pi_{\mathrm{mid}}$),
     `reflPulledUnitary` ($U_B^\dagger R_{\mathrm{mid}} U_B$), and walk operator
     `walkStepUnitary` ($W_{\mathrm{SA}} = R_1 R_2$).
   - Complete two-projector Jordan decomposition covering all three spectral regimes $s = 0$,
     $0 < s < 1$, and $s = 1$, proving exact integer-power action
     $W_{\mathrm{SA}}^z |e_1\rangle = e^{i z \varphi} |v_+\rangle + e^{-i z \varphi} |v_-\rangle$
     for all $z \in \mathbb{Z}$, together with the `spectralPhase` energy-to-angle bridge
     $E = E_{\mathrm{LB}} + \Lambda(1 - \cos \varphi(E))$.
3. **Dihedral Reflection-Reversal & $M$-Step Operator-Norm Perturbation Bounds:**
   - Inductive proof that the reflection-reversed walk $V_M(m)$ equals $W_{\mathrm{SA}}^{2m - M}$
     for every $m \le M$ using only single controlled reflections per step.
   - Exact $L^2$ operator-norm perturbation bounds (`‖W_impl - W_ideal‖ ≤ 2 δ_UB ≤ 4 δ_UB` and
     `‖walkLoop_impl(M) - walkLoop_ideal(M)‖ ≤ 2 M δ_UB ≤ 4 M δ_UB`) on both per-branch and
     full QPE-multiplexed unitaries without any $2^{b_{\mathrm{qpe}}}$ factor loss.
4. **Concrete `DynamicCircuit` Gidney-AND Ladders & Inductive `walkLoopDyn` (`TOFF = 0`):**
   - Measurement-uncomputed temporary-AND ladders realizing $R_{\mathrm{mid}}$, $R_1$,
     $R_1^{[m \ne k + 1]}$, $R_1^{[m = 0]}$, and the recursive $M$-step walk loop `walkLoopDyn`
     with `0` unrolling, `TOFF = 0`, proved `CleanRealizes`, and exact `T`-gate counts.
-/

@[expose] public section

namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.QubitisedWalk
open QuantumComputation.Specs QuantumComputation.Specs.P450

open Operator QProg Real CleanDyn
open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator Circuit.Notation

/-- High-priority parametric `NeZero (2 ^ k)` instance avoiding unary `Nat.succ` unfolding. -/
instance (priority := 100000) instNeZeroTwoPow_walk (k : ℕ) : NeZero (2 ^ k) :=
  ⟨Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos k)⟩

/-!
## Section 1: `CleanRealizes` Lifting & QPE-Multiplexed Walk Unitaries
-/

theorem restrictAssertionToZeroAncilla_idem {Var : Type} {N s : ℕ}
    (Θ : QCAssertion Var (2 ^ N)) (rScr : QRegister s N) :
    restrictAssertionToZeroAncilla (restrictAssertionToZeroAncilla Θ rScr) rScr =
      restrictAssertionToZeroAncilla Θ rScr := by
  funext σ
  apply Subtype.ext
  simp [HermitianMat.conj_conj, QRegister.basisOutcomeProjector_mul_self]

end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.QubitisedWalk

namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.CleanDyn
open QuantumComputation.Specs Operator QProg

/-- Converse of `CleanRealizes.of_compose`, descending from `whole N` to `rAct`. -/
theorem CleanRealizes.of_whole {Var : Type} [Fintype Var] [DecidableEq Var]
    {N k s : ℕ} {v : Var} {rAct : QRegister k N} {rScr : QRegister s N}
    {U : Unitary (2 ^ k)} {P : DynamicCircuit Var N}
    (h : CleanRealizes v (QRegister.whole N) rScr (rAct.embedUnitary U) P) :
    CleanRealizes v rAct rScr U P := by
  rcases h with ⟨htoff, hupd, hwp, hclean⟩
  refine ⟨htoff, hupd, ?_, hclean⟩
  intro Θ hΘ
  simpa only [QRegister.whole_embedUnitary] using hwp Θ hΘ

end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.CleanDyn

namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.QubitisedWalk
open QuantumComputation.Specs QuantumComputation.Specs.P450
open Operator QProg Real CleanDyn
open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator Circuit.Notation

@[simp]
theorem embedMatrix_sub_local {n k : ℕ} (r : QRegister k n)
    (A B : Operator (2 ^ k)) :
    r.embedMatrix (A - B) = r.embedMatrix A - r.embedMatrix B := by
  rw [sub_eq_add_neg, ← neg_one_smul ℂ B, r.embedMatrix_add, r.embedMatrix_smul,
    neg_one_smul, ← sub_eq_add_neg]

/-- Left block `0 .. b_qpe - 1` inside a combined `(b_qpe + k_walk)`-qubit register. -/
abbrev qpeInCombined (b_qpe k_walk : ℕ) : QRegister b_qpe (b_qpe + k_walk) :=
  QRegister.block 0 b_qpe (by omega)

/-- Right block `b_qpe .. b_qpe + k_walk - 1` inside a combined `(b_qpe + k_walk)`-qubit
register. -/
abbrev walkInCombined (b_qpe k_walk : ℕ) : QRegister k_walk (b_qpe + k_walk) :=
  QRegister.block b_qpe k_walk (by omega)

theorem qpeInCombined_disjoint_walkInCombined (b_qpe k_walk : ℕ) :
    (qpeInCombined b_qpe k_walk).DisjointWires (walkInCombined b_qpe k_walk) :=
  QRegister.block_disjoint_of_le 0 b_qpe b_qpe k_walk (by omega) (by omega) (by omega)

@[simp]
theorem concat_compose_qpeInCombined {N b_qpe k_walk : ℕ}
    (rQPE : QRegister b_qpe N) (rWalk : QRegister k_walk N) (hQW : rQPE.DisjointWires rWalk) :
    (rQPE.concat rWalk hQW).compose (qpeInCombined b_qpe k_walk) = rQPE := by
  ext i
  have hi : qpeInCombined b_qpe k_walk i = Fin.castAdd k_walk i := by
    ext
    simp [qpeInCombined]
  rw [QRegister.compose_apply, hi, QRegister.concat_apply_left]

@[simp]
theorem concat_compose_walkInCombined {N b_qpe k_walk : ℕ}
    (rQPE : QRegister b_qpe N) (rWalk : QRegister k_walk N) (hQW : rQPE.DisjointWires rWalk) :
    (rQPE.concat rWalk hQW).compose (walkInCombined b_qpe k_walk) = rWalk := by
  ext i
  have hi : walkInCombined b_qpe k_walk i = Fin.natAdd b_qpe i := by
    ext
    simp [walkInCombined]
  rw [QRegister.compose_apply, hi, QRegister.concat_apply_right]

/-- Block-diagonal operator on `b_qpe + k_walk` wires applying `F m` on the walk block when the
QPE block is in computational-basis state `|m⟩`. -/
noncomputable def qpeMuxMatrix {b_qpe k_walk : ℕ}
    (F : Fin (2 ^ b_qpe) → Operator (2 ^ k_walk)) :
    Operator (2 ^ (b_qpe + k_walk)) :=
  ∑ m : Fin (2 ^ b_qpe),
    (qpeInCombined b_qpe k_walk).basisOutcomeProjector m *
      (walkInCombined b_qpe k_walk).embedMatrix (F m)

theorem basisOutcomeProjector_mul_of_ne {n k : ℕ} (r : QRegister k n)
    {m₁ m₂ : Fin (2 ^ k)} (hne : m₁ ≠ m₂) :
    r.basisOutcomeProjector m₁ * r.basisOutcomeProjector m₂ = 0 := by
  rw [QRegister.basisOutcomeProjector_eq_diagonal, QRegister.basisOutcomeProjector_eq_diagonal,
    Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases hij : i = j
  · subst hij
    by_cases hm₁ : r.extractIndex i = m₁
    · simp [hm₁, hne]
    · simp [hm₁]
  · simp [hij]

theorem qpeProjector_comm_walkEmbed {b_qpe k_walk : ℕ}
    (m : Fin (2 ^ b_qpe)) (A : Operator (2 ^ k_walk)) :
    (qpeInCombined b_qpe k_walk).basisOutcomeProjector m *
        (walkInCombined b_qpe k_walk).embedMatrix A =
      (walkInCombined b_qpe k_walk).embedMatrix A *
        (qpeInCombined b_qpe k_walk).basisOutcomeProjector m :=
  QRegister.embedMatrix_comm_of_disjoint _ _
    (qpeInCombined_disjoint_walkInCombined b_qpe k_walk) (compProj m) A

@[simp]
theorem qpeMuxMatrix_const {b_qpe k_walk : ℕ} (A : Operator (2 ^ k_walk)) :
    qpeMuxMatrix (b_qpe := b_qpe) (fun _ ↦ A) =
      (walkInCombined b_qpe k_walk).embedMatrix A := by
  simp only [qpeMuxMatrix, ← Finset.sum_mul, QRegister.sum_basisOutcomeProjector, Matrix.one_mul]

@[simp]
theorem qpeMuxMatrix_one {b_qpe k_walk : ℕ} :
    qpeMuxMatrix (b_qpe := b_qpe) (k_walk := k_walk) (fun _ ↦ 1) = 1 := by
  rw [qpeMuxMatrix_const, QRegister.embedMatrix_one]

@[simp]
theorem qpeMuxMatrix_sub {b_qpe k_walk : ℕ}
    (F G : Fin (2 ^ b_qpe) → Operator (2 ^ k_walk)) :
    qpeMuxMatrix F - qpeMuxMatrix G = qpeMuxMatrix (fun m ↦ F m - G m) := by
  rw [qpeMuxMatrix, qpeMuxMatrix, qpeMuxMatrix, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun m _ ↦ ?_
  rw [embedMatrix_sub_local, Matrix.mul_sub]

@[simp]
theorem qpeMuxMatrix_conjTranspose {b_qpe k_walk : ℕ}
    (F : Fin (2 ^ b_qpe) → Operator (2 ^ k_walk)) :
    (qpeMuxMatrix F)ᴴ = qpeMuxMatrix (fun m ↦ (F m)ᴴ) := by
  simp only [qpeMuxMatrix, Matrix.conjTranspose_sum, Matrix.conjTranspose_mul,
    QRegister.basisOutcomeProjector_conjTranspose, ← QRegister.embedMatrix_conjTranspose]
  refine Finset.sum_congr rfl fun m _ ↦ ?_
  exact (qpeProjector_comm_walkEmbed m (F m)ᴴ).symm

@[simp]
theorem qpeMuxMatrix_mul {b_qpe k_walk : ℕ}
    (F G : Fin (2 ^ b_qpe) → Operator (2 ^ k_walk)) :
    qpeMuxMatrix F * qpeMuxMatrix G = qpeMuxMatrix (fun m ↦ F m * G m) := by
  classical
  simp only [qpeMuxMatrix, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m _ ↦ ?_
  rw [Finset.mul_sum]
  rw [Finset.sum_eq_single m]
  · calc
      ((qpeInCombined b_qpe k_walk).basisOutcomeProjector m *
          (walkInCombined b_qpe k_walk).embedMatrix (F m)) *
          ((qpeInCombined b_qpe k_walk).basisOutcomeProjector m *
            (walkInCombined b_qpe k_walk).embedMatrix (G m))
        = (qpeInCombined b_qpe k_walk).basisOutcomeProjector m *
            ((walkInCombined b_qpe k_walk).embedMatrix (F m) *
              (qpeInCombined b_qpe k_walk).basisOutcomeProjector m) *
            (walkInCombined b_qpe k_walk).embedMatrix (G m) := by
            simp [Matrix.mul_assoc]
      _ = ((qpeInCombined b_qpe k_walk).basisOutcomeProjector m *
            (qpeInCombined b_qpe k_walk).basisOutcomeProjector m) *
            ((walkInCombined b_qpe k_walk).embedMatrix (F m) *
              (walkInCombined b_qpe k_walk).embedMatrix (G m)) := by
            rw [← qpeProjector_comm_walkEmbed m (F m)]
            simp only [Matrix.mul_assoc]
      _ = (qpeInCombined b_qpe k_walk).basisOutcomeProjector m *
            (walkInCombined b_qpe k_walk).embedMatrix (F m * G m) := by
            rw [QRegister.basisOutcomeProjector_mul_self, QRegister.embedMatrix_mul]
  · intro m' _ hm'
    have hzero :
        (qpeInCombined b_qpe k_walk).basisOutcomeProjector m *
          (qpeInCombined b_qpe k_walk).basisOutcomeProjector m' = 0 :=
      basisOutcomeProjector_mul_of_ne _ (Ne.symm hm')
    calc
      ((qpeInCombined b_qpe k_walk).basisOutcomeProjector m *
          (walkInCombined b_qpe k_walk).embedMatrix (F m)) *
          ((qpeInCombined b_qpe k_walk).basisOutcomeProjector m' *
            (walkInCombined b_qpe k_walk).embedMatrix (G m'))
        = (qpeInCombined b_qpe k_walk).basisOutcomeProjector m *
            ((walkInCombined b_qpe k_walk).embedMatrix (F m) *
              (qpeInCombined b_qpe k_walk).basisOutcomeProjector m') *
            (walkInCombined b_qpe k_walk).embedMatrix (G m') := by
            simp only [Matrix.mul_assoc]
      _ = ((qpeInCombined b_qpe k_walk).basisOutcomeProjector m *
            (qpeInCombined b_qpe k_walk).basisOutcomeProjector m') *
            ((walkInCombined b_qpe k_walk).embedMatrix (F m) *
              (walkInCombined b_qpe k_walk).embedMatrix (G m')) := by
            rw [← qpeProjector_comm_walkEmbed m' (F m)]
            simp only [Matrix.mul_assoc]
      _ = 0 := by rw [hzero, Matrix.zero_mul]
  · intro hm
    exact absurd (Finset.mem_univ m) hm

/-- Bundled unitary on `b_qpe + k_walk` qubits applying `F m` on the walk block conditioned on
basis state `|m⟩` of the QPE block. -/
noncomputable def qpeMuxUnitary {b_qpe k_walk : ℕ}
    (F : Fin (2 ^ b_qpe) → Unitary (2 ^ k_walk)) :
    Unitary (2 ^ (b_qpe + k_walk)) :=
  ⟨qpeMuxMatrix (fun m ↦ (F m).1), by
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose,
      qpeMuxMatrix_conjTranspose, qpeMuxMatrix_mul]
    have hunit : (fun m ↦ ((F m).1)ᴴ * (F m).1) = fun _ ↦ (1 : Operator (2 ^ k_walk)) := by
      funext m
      exact congrArg Subtype.val (Unitary.star_mul_self (F m))
    rw [hunit, qpeMuxMatrix_one]⟩

@[simp]
theorem qpeMuxUnitary_val {b_qpe k_walk : ℕ}
    (F : Fin (2 ^ b_qpe) → Unitary (2 ^ k_walk)) :
    (qpeMuxUnitary F).1 = qpeMuxMatrix (fun m ↦ (F m).1) := rfl

@[simp]
theorem qpeMuxUnitary_one {b_qpe k_walk : ℕ} :
    qpeMuxUnitary (b_qpe := b_qpe) (k_walk := k_walk) (fun _ ↦ 1) = 1 := by
  apply Subtype.ext
  exact qpeMuxMatrix_one

@[simp]
theorem qpeMuxUnitary_mul {b_qpe k_walk : ℕ}
    (F G : Fin (2 ^ b_qpe) → Unitary (2 ^ k_walk)) :
    qpeMuxUnitary (fun m ↦ F m * G m) = qpeMuxUnitary F * qpeMuxUnitary G := by
  apply Subtype.ext
  exact (qpeMuxMatrix_mul (fun m ↦ (F m).1) (fun m ↦ (G m).1)).symm

@[simp]
theorem qpeMuxUnitary_const {b_qpe k_walk : ℕ} (U : Unitary (2 ^ k_walk)) :
    qpeMuxUnitary (b_qpe := b_qpe) (fun _ ↦ U) =
      (walkInCombined b_qpe k_walk).embedUnitary U := by
  apply Subtype.ext
  exact qpeMuxMatrix_const U.1

/-- Embedding `qpeMuxMatrix F` onto `rQPE.concat rWalk hQW` expands to the sum over QPE outcomes
on `rQPE` times the embedded walk operators on `rWalk`. -/
theorem embedMatrix_qpeMuxMatrix {N b_qpe k_walk : ℕ}
    (rQPE : QRegister b_qpe N) (rWalk : QRegister k_walk N) (hQW : rQPE.DisjointWires rWalk)
    (F : Fin (2 ^ b_qpe) → Operator (2 ^ k_walk)) :
    (rQPE.concat rWalk hQW).embedMatrix (qpeMuxMatrix F) =
      ∑ m : Fin (2 ^ b_qpe), rQPE.basisOutcomeProjector m * rWalk.embedMatrix (F m) := by
  rw [qpeMuxMatrix, QRegister.embedMatrix_sum]
  refine Finset.sum_congr rfl fun m _ ↦ ?_
  rw [QRegister.embedMatrix_mul, QRegister.basisOutcomeProjector,
    ← QRegister.embedMatrix_compose, concat_compose_qpeInCombined,
    ← QRegister.embedMatrix_compose, concat_compose_walkInCombined,
    ← QRegister.basisOutcomeProjector]

theorem basisOutcomeProjector_comm_embedMatrix {N k₁ k₂ : ℕ}
    (r₁ : QRegister k₁ N) (r₂ : QRegister k₂ N) (hdisj : r₁.DisjointWires r₂)
    (m : Fin (2 ^ k₁)) (A : Operator (2 ^ k₂)) :
    r₁.basisOutcomeProjector m * r₂.embedMatrix A =
      r₂.embedMatrix A * r₁.basisOutcomeProjector m :=
  QRegister.embedMatrix_comm_of_disjoint r₁ r₂ hdisj (compProj m) A

/-- Action of an embedded `qpeMuxUnitary F` on any global state projected onto QPE outcome `m`. -/
theorem embed_qpeMuxUnitary_mulVec_proj {N b_qpe k_walk : ℕ}
    (rQPE : QRegister b_qpe N) (rWalk : QRegister k_walk N) (hQW : rQPE.DisjointWires rWalk)
    (F : Fin (2 ^ b_qpe) → Unitary (2 ^ k_walk)) (m : Fin (2 ^ b_qpe))
    (Ψ : Fin (2 ^ N) → ℂ) :
    ((rQPE.concat rWalk hQW).embedUnitary (qpeMuxUnitary F)).1 *ᵥ
        (rQPE.basisOutcomeProjector m *ᵥ Ψ) =
      rQPE.basisOutcomeProjector m *ᵥ ((rWalk.embedUnitary (F m)).1 *ᵥ Ψ) := by
  classical
  rw [QRegister.embedUnitary_val, qpeMuxUnitary_val, embedMatrix_qpeMuxMatrix,
    Matrix.mulVec_mulVec, Finset.sum_mul, Finset.sum_eq_single m]
  · rw [Matrix.mul_assoc, ← basisOutcomeProjector_comm_embedMatrix rQPE rWalk hQW m (F m).1,
      ← Matrix.mul_assoc, QRegister.basisOutcomeProjector_mul_self, ← Matrix.mulVec_mulVec]
    rfl
  · intro m' _ hm'
    rw [Matrix.mul_assoc, ← basisOutcomeProjector_comm_embedMatrix rQPE rWalk hQW m (F m').1,
      ← Matrix.mul_assoc, basisOutcomeProjector_mul_of_ne rQPE hm', Matrix.zero_mul]
  · intro hm
    exact absurd (Finset.mem_univ m) hm

/-- Superposition expansion of an embedded `qpeMuxUnitary F` on any global state `Ψ`. -/
theorem embed_qpeMuxUnitary_mulVec {N b_qpe k_walk : ℕ}
    (rQPE : QRegister b_qpe N) (rWalk : QRegister k_walk N) (hQW : rQPE.DisjointWires rWalk)
    (F : Fin (2 ^ b_qpe) → Unitary (2 ^ k_walk)) (Ψ : Fin (2 ^ N) → ℂ) :
    ((rQPE.concat rWalk hQW).embedUnitary (qpeMuxUnitary F)).1 *ᵥ Ψ =
      ∑ m : Fin (2 ^ b_qpe),
        rQPE.basisOutcomeProjector m *ᵥ ((rWalk.embedUnitary (F m)).1 *ᵥ Ψ) := by
  have hΨ : Ψ = ∑ m : Fin (2 ^ b_qpe), rQPE.basisOutcomeProjector m *ᵥ Ψ := by
    rw [← Matrix.sum_mulVec, QRegister.sum_basisOutcomeProjector, Matrix.one_mulVec]
  conv_lhs => rw [hΨ]
  rw [Matrix.mulVec_sum]
  refine Finset.sum_congr rfl fun m _ ↦ ?_
  exact embed_qpeMuxUnitary_mulVec_proj rQPE rWalk hQW F m Ψ

/-- Standard Hermitian inner product $\langle u, v \rangle = \sum_i \overline{u_i} v_i$ on
`Fin d → ℂ` (conjugate-linear in the first argument, linear in the second). -/
noncomputable def vecInner {d : ℕ} (u v : Fin d → ℂ) : ℂ :=
  dotProduct (star u) v

/-- Squared Euclidean $L^2$ norm $\sum_i |v_i|^2$ on `Fin d → ℂ`. -/
noncomputable def vecNormSq {d : ℕ} (v : Fin d → ℂ) : ℝ :=
  ∑ i : Fin d, Complex.normSq (v i)

theorem vecInner_self_eq_normSq {d : ℕ} (v : Fin d → ℂ) :
    vecInner v v = (vecNormSq v : ℂ) := by
  simp only [vecInner, vecNormSq, dotProduct, Pi.star_apply, RCLike.star_def,
    Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [mul_comm, Complex.mul_conj]

@[simp]
theorem vecNormSq_zero {d : ℕ} : vecNormSq (0 : Fin d → ℂ) = 0 := by
  simp [vecNormSq]

theorem vecNormSq_eq_zero_iff {d : ℕ} (v : Fin d → ℂ) :
    vecNormSq v = 0 ↔ v = 0 := by
  constructor
  · intro h
    have hall := (Finset.sum_eq_zero_iff_of_nonneg
      (fun i _ ↦ Complex.normSq_nonneg (v i))).mp h
    funext i
    exact Complex.normSq_eq_zero.mp (hall i (Finset.mem_univ i))
  · rintro rfl
    exact vecNormSq_zero

@[simp]
theorem vecInner_zero_left {d : ℕ} (v : Fin d → ℂ) : vecInner 0 v = 0 := by
  simp [vecInner]

@[simp]
theorem vecInner_zero_right {d : ℕ} (u : Fin d → ℂ) : vecInner u 0 = 0 := by
  simp [vecInner]

theorem vecInner_add_left {d : ℕ} (u₁ u₂ v : Fin d → ℂ) :
    vecInner (u₁ + u₂) v = vecInner u₁ v + vecInner u₂ v := by
  simp [vecInner, star_add, add_dotProduct]

theorem vecInner_add_right {d : ℕ} (u v₁ v₂ : Fin d → ℂ) :
    vecInner u (v₁ + v₂) = vecInner u v₁ + vecInner u v₂ := by
  simp [vecInner, dotProduct_add]

theorem vecInner_sub_left {d : ℕ} (u₁ u₂ v : Fin d → ℂ) :
    vecInner (u₁ - u₂) v = vecInner u₁ v - vecInner u₂ v := by
  simp [vecInner, star_sub, sub_dotProduct]

theorem vecInner_sub_right {d : ℕ} (u v₁ v₂ : Fin d → ℂ) :
    vecInner u (v₁ - v₂) = vecInner u v₁ - vecInner u v₂ := by
  simp [vecInner, dotProduct_sub]

theorem vecInner_smul_left {d : ℕ} (c : ℂ) (u v : Fin d → ℂ) :
    vecInner (c • u) v = star c * vecInner u v := by
  simp [vecInner, star_smul, smul_dotProduct]

theorem vecInner_smul_right {d : ℕ} (c : ℂ) (u v : Fin d → ℂ) :
    vecInner u (c • v) = c * vecInner u v := by
  simp [vecInner, dotProduct_smul]

theorem star_vecInner {d : ℕ} (u v : Fin d → ℂ) :
    star (vecInner u v) = vecInner v u := by
  simp [vecInner, dotProduct, star_sum, mul_comm]

theorem vecInner_mulVec_left {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) (u v : Fin d → ℂ) :
    vecInner (A *ᵥ u) v = vecInner u (Aᴴ *ᵥ v) := by
  rw [vecInner, vecInner, Matrix.star_mulVec, Matrix.dotProduct_mulVec]

theorem vecNormSq_smul {d : ℕ} (c : ℂ) (v : Fin d → ℂ) :
    vecNormSq (c • v) = Complex.normSq c * vecNormSq v := by
  simp [vecNormSq, Finset.mul_sum, map_mul]

/-- Orthogonal Pythagorean identity for linear combinations `a • u + b • v`. -/
theorem vecNormSq_linear_comb_of_ortho {d : ℕ} {u v : Fin d → ℂ} (huv : vecInner u v = 0)
    (a b : ℂ) :
    vecNormSq (a • u + b • v) =
      Complex.normSq a * vecNormSq u + Complex.normSq b * vecNormSq v := by
  have hvu : vecInner v u = 0 := by
    rw [← star_vecInner, huv, star_zero]
  apply Complex.ofReal_injective
  rw [← vecInner_self_eq_normSq, vecInner_add_left, vecInner_add_right, vecInner_add_right,
    vecInner_smul_left, vecInner_smul_left, vecInner_smul_left, vecInner_smul_left,
    vecInner_smul_right, vecInner_smul_right, vecInner_smul_right, vecInner_smul_right,
    huv, hvu, vecInner_self_eq_normSq, vecInner_self_eq_normSq]
  have hna : star a * a = (Complex.normSq a : ℂ) := by
    rw [RCLike.star_def, mul_comm, Complex.mul_conj]
  have hnb : star b * b = (Complex.normSq b : ℂ) := by
    rw [RCLike.star_def, mul_comm, Complex.mul_conj]
  simp only [mul_zero, add_zero, zero_add, ← mul_assoc, hna, hnb]
  push_cast
  ring

/-- Orthogonal projector onto the all-zero state `|0_all⟩` of `rAll`. -/
noncomputable def projIn {k_walk w_all : ℕ} (rAll : QRegister w_all k_walk) :
    Operator (2 ^ k_walk) :=
  rAll.basisOutcomeProjector 0

/-- Orthogonal projector onto the all-zero state `|0_mid⟩` of `rMid`. -/
noncomputable def projMid {k_walk w_mid : ℕ} (rMid : QRegister w_mid k_walk) :
    Operator (2 ^ k_walk) :=
  rMid.basisOutcomeProjector 0

/-- Pulled-back mid-register projector
$\tilde{\Pi}_{\mathrm{mid}} = U_B^\dagger \Pi_{\mathrm{mid}} U_B$. -/
noncomputable def pulledProjMid {k_walk w_mid : ℕ} (rMid : QRegister w_mid k_walk)
    (U_B : Unitary (2 ^ k_walk)) : Operator (2 ^ k_walk) :=
  U_B.1ᴴ * projMid rMid * U_B.1

@[simp]
theorem projIn_conjTranspose {k_walk w_all : ℕ} (rAll : QRegister w_all k_walk) :
    (projIn rAll)ᴴ = projIn rAll :=
  QRegister.basisOutcomeProjector_conjTranspose rAll 0

@[simp]
theorem projIn_mul_self {k_walk w_all : ℕ} (rAll : QRegister w_all k_walk) :
    projIn rAll * projIn rAll = projIn rAll :=
  QRegister.basisOutcomeProjector_mul_self rAll 0

@[simp]
theorem projMid_conjTranspose {k_walk w_mid : ℕ} (rMid : QRegister w_mid k_walk) :
    (projMid rMid)ᴴ = projMid rMid :=
  QRegister.basisOutcomeProjector_conjTranspose rMid 0

@[simp]
theorem projMid_mul_self {k_walk w_mid : ℕ} (rMid : QRegister w_mid k_walk) :
    projMid rMid * projMid rMid = projMid rMid :=
  QRegister.basisOutcomeProjector_mul_self rMid 0

@[simp]
theorem pulledProjMid_conjTranspose {k_walk w_mid : ℕ} (rMid : QRegister w_mid k_walk)
    (U_B : Unitary (2 ^ k_walk)) :
    (pulledProjMid rMid U_B)ᴴ = pulledProjMid rMid U_B := by
  simp [pulledProjMid, Matrix.conjTranspose_mul, Matrix.mul_assoc]

@[simp]
theorem pulledProjMid_mul_self {k_walk w_mid : ℕ} (rMid : QRegister w_mid k_walk)
    (U_B : Unitary (2 ^ k_walk)) :
    pulledProjMid rMid U_B * pulledProjMid rMid U_B = pulledProjMid rMid U_B := by
  have hUU : U_B.1 * U_B.1ᴴ = 1 := by
    rw [← Matrix.star_eq_conjTranspose]
    exact U_B.2.2
  calc
    (U_B.1ᴴ * projMid rMid * U_B.1) * (U_B.1ᴴ * projMid rMid * U_B.1)
      = U_B.1ᴴ * projMid rMid * (U_B.1 * U_B.1ᴴ) * projMid rMid * U_B.1 := by
          simp [Matrix.mul_assoc]
    _ = U_B.1ᴴ * (projMid rMid * projMid rMid) * U_B.1 := by
          rw [hUU]; simp [Matrix.mul_assoc]
    _ = pulledProjMid rMid U_B := by
          rw [projMid_mul_self]; rfl

theorem two_smul_proj_sub_one_sq {d : ℕ} (P : Operator d) (hP_idem : P * P = P) :
    ((2 : ℂ) • P - 1) * ((2 : ℂ) • P - 1) = 1 := by
  calc
    ((2 : ℂ) • P - 1) * ((2 : ℂ) • P - 1)
      = ((2 : ℂ) • P) * ((2 : ℂ) • P) - (2 : ℂ) • P - (2 : ℂ) • P + 1 := by
          simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one]
          ext i j; simp; ring
    _ = 1 := by
          rw [Matrix.smul_mul, Matrix.mul_smul, hP_idem]
          ext i j; simp; ring

theorem one_sub_two_smul_proj_sq {d : ℕ} (P : Operator d) (hP_idem : P * P = P) :
    (1 - (2 : ℂ) • P) * (1 - (2 : ℂ) • P) = 1 := by
  calc
    (1 - (2 : ℂ) • P) * (1 - (2 : ℂ) • P)
      = 1 - (2 : ℂ) • P - (2 : ℂ) • P + ((2 : ℂ) • P) * ((2 : ℂ) • P) := by
          simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one]
          ext i j; simp; ring
    _ = 1 := by
          rw [Matrix.smul_mul, Matrix.mul_smul, hP_idem]
          ext i j; simp; ring

theorem two_smul_proj_sub_one_mem_unitary {d : ℕ} (P : Operator d)
    (hP_herm : Pᴴ = P) (hP_idem : P * P = P) :
    ((2 : ℂ) • P - 1) ∈ Matrix.unitaryGroup (Fin d) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
  have hherm : ((2 : ℂ) • P - 1)ᴴ = (2 : ℂ) • P - 1 := by
    simp [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, hP_herm]
  rw [hherm]
  exact two_smul_proj_sub_one_sq P hP_idem

theorem one_sub_two_smul_proj_mem_unitary {d : ℕ} (P : Operator d)
    (hP_herm : Pᴴ = P) (hP_idem : P * P = P) :
    (1 - (2 : ℂ) • P) ∈ Matrix.unitaryGroup (Fin d) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
  have hherm : (1 - (2 : ℂ) • P)ᴴ = 1 - (2 : ℂ) • P := by
    simp [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, hP_herm]
  rw [hherm]
  exact one_sub_two_smul_proj_sq P hP_idem

/-- Input-subspace reflection $R_1 = 2\Pi_{\mathrm{in}} - I$ (`+1` on `|0_all⟩`,
`-1` orthogonal). -/
noncomputable def reflInUnitary {k_walk w_all : ℕ} (rAll : QRegister w_all k_walk) :
    Unitary (2 ^ k_walk) :=
  ⟨(2 : ℂ) • projIn rAll - 1,
    two_smul_proj_sub_one_mem_unitary (projIn rAll)
      (projIn_conjTranspose rAll) (projIn_mul_self rAll)⟩

/-- Mid-subspace reflection $R_{\mathrm{mid}} = I - 2\Pi_{\mathrm{mid}}$ (`-1` on `|0_mid⟩`,
`+1` orthogonal). -/
noncomputable def reflMidUnitary {k_walk w_mid : ℕ} (rMid : QRegister w_mid k_walk) :
    Unitary (2 ^ k_walk) :=
  ⟨1 - (2 : ℂ) • projMid rMid,
    one_sub_two_smul_proj_mem_unitary (projMid rMid)
      (projMid_conjTranspose rMid) (projMid_mul_self rMid)⟩

/-- Generalized pulled-back mid reflection $U_{\mathrm{bwd}} R_{\mathrm{mid}} U_{\mathrm{fwd}}$,
supporting independent forward/backward approximate unitaries. -/
noncomputable def reflPulledPair {k_walk w_mid : ℕ} (rMid : QRegister w_mid k_walk)
    (U_fwd U_bwd : Unitary (2 ^ k_walk)) : Unitary (2 ^ k_walk) :=
  U_bwd * reflMidUnitary rMid * U_fwd

/-- Exact pulled-back mid reflection
$R_2 = U_B^{-1} R_{\mathrm{mid}} U_B = I - 2\tilde{\Pi}_{\mathrm{mid}}$. -/
noncomputable abbrev reflPulledUnitary {k_walk w_mid : ℕ} (rMid : QRegister w_mid k_walk)
    (U_B : Unitary (2 ^ k_walk)) : Unitary (2 ^ k_walk) :=
  reflPulledPair rMid U_B U_B⁻¹

/-- Generalized spectral-amplification walk step
$R_1 (U_{\mathrm{bwd}} R_{\mathrm{mid}} U_{\mathrm{fwd}})$. -/
noncomputable def walkStepPair {k_walk w_all w_mid : ℕ}
    (rAll : QRegister w_all k_walk) (rMid : QRegister w_mid k_walk)
    (U_fwd U_bwd : Unitary (2 ^ k_walk)) : Unitary (2 ^ k_walk) :=
  reflInUnitary rAll * reflPulledPair rMid U_fwd U_bwd

/-- Spectral-amplification walk operator
$W_{\mathrm{SA}} = R_1 R_2 = R_1 U_B^{-1} R_{\mathrm{mid}} U_B$. -/
noncomputable abbrev walkStepUnitary {k_walk w_all w_mid : ℕ}
    (rAll : QRegister w_all k_walk) (rMid : QRegister w_mid k_walk)
    (U_B : Unitary (2 ^ k_walk)) : Unitary (2 ^ k_walk) :=
  walkStepPair rAll rMid U_B U_B⁻¹

@[simp]
theorem reflInUnitary_val {k_walk w_all : ℕ} (rAll : QRegister w_all k_walk) :
    (reflInUnitary rAll).1 = (2 : ℂ) • projIn rAll - 1 := rfl

@[simp]
theorem reflMidUnitary_val {k_walk w_mid : ℕ} (rMid : QRegister w_mid k_walk) :
    (reflMidUnitary rMid).1 = 1 - (2 : ℂ) • projMid rMid := rfl

theorem reflPulledUnitary_val {k_walk w_mid : ℕ} (rMid : QRegister w_mid k_walk)
    (U_B : Unitary (2 ^ k_walk)) :
    (reflPulledUnitary rMid U_B).1 = 1 - (2 : ℂ) • pulledProjMid rMid U_B := by
  have hinv : (U_B⁻¹).1 = U_B.1ᴴ := rfl
  have hunit : U_B.1ᴴ * U_B.1 = 1 := congrArg Subtype.val (Unitary.star_mul_self U_B)
  change (U_B⁻¹).1 * (1 - (2 : ℂ) • projMid rMid) * U_B.1 = _
  rw [hinv, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hunit, Matrix.mul_smul,
    Matrix.smul_mul, pulledProjMid]

@[simp]
theorem reflInUnitary_mul_self {k_walk w_all : ℕ} (rAll : QRegister w_all k_walk) :
    reflInUnitary rAll * reflInUnitary rAll = 1 := by
  apply Subtype.ext
  exact two_smul_proj_sub_one_sq (projIn rAll) (projIn_mul_self rAll)

@[simp]
theorem reflMidUnitary_mul_self {k_walk w_mid : ℕ} (rMid : QRegister w_mid k_walk) :
    reflMidUnitary rMid * reflMidUnitary rMid = 1 := by
  apply Subtype.ext
  exact one_sub_two_smul_proj_sq (projMid rMid) (projMid_mul_self rMid)

@[simp]
theorem reflPulledUnitary_mul_self {k_walk w_mid : ℕ} (rMid : QRegister w_mid k_walk)
    (U_B : Unitary (2 ^ k_walk)) :
    reflPulledUnitary rMid U_B * reflPulledUnitary rMid U_B = 1 := by
  dsimp [reflPulledUnitary, reflPulledPair]
  rw [mul_assoc (U_B⁻¹ * reflMidUnitary rMid) U_B _,
    ← mul_assoc U_B (U_B⁻¹ * reflMidUnitary rMid) U_B,
    ← mul_assoc U_B U_B⁻¹, mul_inv_cancel, one_mul,
    ← mul_assoc (U_B⁻¹ * reflMidUnitary rMid) (reflMidUnitary rMid) U_B,
    mul_assoc U_B⁻¹ (reflMidUnitary rMid) (reflMidUnitary rMid),
    reflMidUnitary_mul_self, mul_one, inv_mul_cancel]

/-- Action of any integer power `U ^ z` (`z : ℤ`) of a unitary `U` on an eigenvector with nonzero
eigenvalue `μ`. -/
theorem unitary_zpow_mulVec_of_eigenvector {d : ℕ} (U : Unitary d) {v : Fin d → ℂ} {μ : ℂ}
    (hμ : μ ≠ 0) (heig : U.1 *ᵥ v = μ • v) (z : ℤ) :
    (U ^ z).1 *ᵥ v = (μ ^ z) • v := by
  have hpow : ∀ (V : Unitary d) (ν : ℂ), V.1 *ᵥ v = ν • v →
      ∀ n : ℕ, (V ^ n).1 *ᵥ v = (ν ^ n) • v := by
    intro V ν hV n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [pow_succ', Submonoid.coe_mul, ← Matrix.mulVec_mulVec, ih, Matrix.mulVec_smul, hV,
          smul_smul, mul_comm, ← pow_succ']
  have hinv : (U⁻¹).1 *ᵥ v = μ⁻¹ • v := by
    have h1 : (U⁻¹ * U).1 *ᵥ v = v := by simp
    rw [Submonoid.coe_mul, ← Matrix.mulVec_mulVec, heig, Matrix.mulVec_smul] at h1
    calc
      (U⁻¹).1 *ᵥ v = (μ⁻¹ * μ) • ((U⁻¹).1 *ᵥ v) := by rw [inv_mul_cancel₀ hμ, one_smul]
      _ = μ⁻¹ • (μ • ((U⁻¹).1 *ᵥ v)) := mul_smul μ⁻¹ μ _
      _ = μ⁻¹ • v := by rw [h1]
  cases z with
  | ofNat n =>
      simpa [Int.ofNat_eq_natCast] using hpow U μ heig n
  | negSucc n =>
      have hU_neg : U ^ Int.negSucc n = (U⁻¹) ^ (n + 1) := by
        rw [zpow_negSucc, inv_pow]
      have hμ_neg : μ ^ Int.negSucc n = (μ⁻¹) ^ (n + 1) := by
        rw [zpow_negSucc, inv_pow]
      rw [hU_neg, hμ_neg]
      exact hpow U⁻¹ μ⁻¹ hinv (n + 1)

/-- General two-projector Jordan plane decomposition: for any two Hermitian idempotents `P₁, P₂`
and normalized `e₁` with `P₁ *ᵥ e₁ = e₁` and `P₁ *ᵥ (P₂ *ᵥ e₁) = sin²(φ/2) • e₁` (`φ ∈ [0, π]`),
`e₁` decomposes into orthogonal eigenvectors `v_plus, v_minus` of `(2•P₁ - 1) * (1 - 2•P₂)` with
eigenvalues `exp(±i φ)` (and equal squared norm `1/2` whenever `0 < sin(φ/2) < 1`). -/
theorem two_projector_jordan_decomposition {d : ℕ}
    (P₁ P₂ : Operator d)
    (hP₁_herm : P₁ᴴ = P₁)
    (hP₂_herm : P₂ᴴ = P₂) (hP₂_idem : P₂ * P₂ = P₂)
    (e₁ : Fin d → ℂ) (h_in : P₁ *ᵥ e₁ = e₁) (h_norm : vecNormSq e₁ = 1)
    (φ : ℝ) (hφ0 : 0 ≤ φ) (hφpi : φ ≤ π)
    (h_proj : P₁ *ᵥ (P₂ *ᵥ e₁) = ((Real.sin (φ / 2) ^ 2 : ℝ) : ℂ) • e₁) :
    let R₁ : Operator d := (2 : ℂ) • P₁ - 1
    let R₂ : Operator d := 1 - (2 : ℂ) • P₂
    let W : Operator d := R₁ * R₂
    let s : ℝ := Real.sin (φ / 2)
    ∃ v_plus v_minus : Fin d → ℂ,
      e₁ = v_plus + v_minus ∧
      vecInner v_plus v_minus = 0 ∧
      vecNormSq v_plus + vecNormSq v_minus = 1 ∧
      (0 < s ∧ s < 1 → vecNormSq v_plus = 1 / 2 ∧ vecNormSq v_minus = 1 / 2) ∧
      W *ᵥ v_plus = Complex.exp (Complex.I * (φ : ℂ)) • v_plus ∧
      W *ᵥ v_minus = Complex.exp (-Complex.I * (φ : ℂ)) • v_minus := by
  intro R₁ R₂ W s
  let c : ℝ := Real.cos (φ / 2)
  have hs_nonneg : 0 ≤ s :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [Real.pi_pos])
  have hs_le_one : s ≤ 1 := Real.sin_le_one (φ / 2)
  have hc_nonneg : 0 ≤ c :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], by linarith⟩
  have hsc_sq : s ^ 2 + c ^ 2 = 1 := Real.sin_sq_add_cos_sq (φ / 2)
  have he1_inner : vecInner e₁ e₁ = 1 := by
    rw [vecInner_self_eq_normSq, h_norm, Complex.ofReal_one]
  have hP₂_inner : vecInner e₁ (P₂ *ᵥ e₁) = ((s ^ 2 : ℝ) : ℂ) := by
    calc
      vecInner e₁ (P₂ *ᵥ e₁) = vecInner (P₁ *ᵥ e₁) (P₂ *ᵥ e₁) := by rw [h_in]
      _ = vecInner e₁ (P₁ᴴ *ᵥ (P₂ *ᵥ e₁)) := vecInner_mulVec_left P₁ e₁ _
      _ = vecInner e₁ (P₁ *ᵥ (P₂ *ᵥ e₁)) := by rw [hP₁_herm]
      _ = vecInner e₁ (((s ^ 2 : ℝ) : ℂ) • e₁) := by rw [h_proj]
      _ = ((s ^ 2 : ℝ) : ℂ) := by rw [vecInner_smul_right, he1_inner, mul_one]
  have hP₂_inner_symm : vecInner (P₂ *ᵥ e₁) e₁ = ((s ^ 2 : ℝ) : ℂ) := by
    rw [← star_vecInner, hP₂_inner, RCLike.star_def, Complex.conj_ofReal]
  have hP₂_self : vecInner (P₂ *ᵥ e₁) (P₂ *ᵥ e₁) = ((s ^ 2 : ℝ) : ℂ) := by
    rw [vecInner_mulVec_left, hP₂_herm, Matrix.mulVec_mulVec, hP₂_idem, hP₂_inner]
  have hP₂_normSq : vecNormSq (P₂ *ᵥ e₁) = s ^ 2 := by
    apply Complex.ofReal_injective
    rw [← vecInner_self_eq_normSq, hP₂_self]
  have hR₁_e1 : R₁ *ᵥ e₁ = e₁ := by
    dsimp only [R₁]
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, h_in]
    ext i; simp; ring
  by_cases hs0 : s = 0
  · have hφ_eq : φ = 0 := by
      by_contra hne
      have hpos : 0 < φ / 2 := by positivity
      have hlt : φ / 2 < π := by linarith [Real.pi_pos]
      exact (Real.sin_pos_of_pos_of_lt_pi hpos hlt).ne' hs0
    have hP₂_zero : P₂ *ᵥ e₁ = 0 := by
      rw [← vecNormSq_eq_zero_iff, hP₂_normSq, hs0, sq]
      ring
    have hR₂_e1 : R₂ *ᵥ e₁ = e₁ := by
      dsimp only [R₂]
      rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, hP₂_zero, smul_zero, sub_zero]
    have hW_e1 : W *ᵥ e₁ = e₁ := by
      change (R₁ * R₂) *ᵥ e₁ = e₁
      rw [← Matrix.mulVec_mulVec, hR₂_e1, hR₁_e1]
    refine ⟨e₁, 0, by simp, by simp, by simp [h_norm], ?_, ?_, by simp⟩
    · rintro ⟨hpos, _⟩
      exact absurd hs0 hpos.ne'
    · subst hφ_eq
      simp [hW_e1]
  · by_cases hs1 : s = 1
    · have hφ_eq : φ = π := by
        by_contra hne
        have hlt : φ < π := lt_of_le_of_ne hφpi hne
        have hc_pos : 0 < c :=
          Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith⟩
        nlinarith [hsc_sq, hs1, sq_pos_of_pos hc_pos]
      have hdiff_zero : P₂ *ᵥ e₁ - e₁ = 0 := by
        rw [← vecNormSq_eq_zero_iff]
        apply Complex.ofReal_injective
        rw [← vecInner_self_eq_normSq, vecInner_sub_left, vecInner_sub_right, vecInner_sub_right,
          hP₂_self, hP₂_inner_symm, hP₂_inner, he1_inner, hs1]
        norm_num
      have hP₂_eq : P₂ *ᵥ e₁ = e₁ := sub_eq_zero.mp hdiff_zero
      have hR₂_e1 : R₂ *ᵥ e₁ = (-1 : ℂ) • e₁ := by
        dsimp only [R₂]
        rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, hP₂_eq]
        ext i; simp; ring
      have hW_e1 : W *ᵥ e₁ = (-1 : ℂ) • e₁ := by
        change (R₁ * R₂) *ᵥ e₁ = (-1 : ℂ) • e₁
        rw [← Matrix.mulVec_mulVec, hR₂_e1, Matrix.mulVec_smul, hR₁_e1]
      refine ⟨e₁, 0, by simp, by simp, by simp [h_norm], ?_, ?_, by simp⟩
      · rintro ⟨_, hlt⟩
        exact absurd hs1 hlt.ne
      · subst hφ_eq
        have hexp : Complex.exp (Complex.I * (π : ℂ)) = -1 := by
          rw [mul_comm, Complex.exp_pi_mul_I]
        rw [hexp, hW_e1]
    · have hs_pos : 0 < s := lt_of_le_of_ne hs_nonneg (Ne.symm hs0)
      have hc_pos : 0 < c := by
        have hs_lt : s < 1 := lt_of_le_of_ne hs_le_one hs1
        have hc_sq : 0 < c ^ 2 := by nlinarith
        nlinarith
      have hsc_ne : (s * c : ℝ) ≠ 0 := (mul_pos hs_pos hc_pos).ne'
      let w : Fin d → ℂ := P₂ *ᵥ e₁ - ((s ^ 2 : ℝ) : ℂ) • e₁
      let e₂ : Fin d → ℂ := (((s * c)⁻¹ : ℝ) : ℂ) • w
      have hP₁_w : P₁ *ᵥ w = 0 := by
        dsimp only [w]
        rw [Matrix.mulVec_sub, Matrix.mulVec_smul, h_proj, h_in, sub_self]
      have hP₁_e2 : P₁ *ᵥ e₂ = 0 := by
        dsimp only [e₂]
        rw [Matrix.mulVec_smul, hP₁_w, smul_zero]
      have he1_e2 : vecInner e₁ e₂ = 0 := by
        rw [← h_in, vecInner_mulVec_left, hP₁_herm, hP₁_e2, vecInner_zero_right]
      have hw_normSq : vecNormSq w = (s * c) ^ 2 := by
        apply Complex.ofReal_injective
        rw [← vecInner_self_eq_normSq]
        dsimp only [w]
        rw [vecInner_sub_left, vecInner_sub_right, vecInner_sub_right,
          vecInner_smul_left, vecInner_smul_left, vecInner_smul_right, vecInner_smul_right,
          hP₂_self, hP₂_inner_symm, hP₂_inner, he1_inner, RCLike.star_def, Complex.conj_ofReal]
        push_cast
        linear_combination -(s ^ 2 : ℂ) * (by exact_mod_cast hsc_sq : (s : ℂ) ^ 2 + c ^ 2 = 1)
      have he2_norm : vecNormSq e₂ = 1 := by
        dsimp only [e₂]
        rw [vecNormSq_smul, Complex.normSq_ofReal, hw_normSq]
        field_simp [hsc_ne]
      have hw_eq : w = ((s * c : ℝ) : ℂ) • e₂ := by
        dsimp only [e₂]
        rw [smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hsc_ne, Complex.ofReal_one, one_smul]
      have hP₂_e1 : P₂ *ᵥ e₁ = ((s ^ 2 : ℝ) : ℂ) • e₁ + ((s * c : ℝ) : ℂ) • e₂ := by
        rw [← hw_eq]
        dsimp only [w]
        abel
      have hP₂_e2 : P₂ *ᵥ e₂ = ((s * c : ℝ) : ℂ) • e₁ + ((c ^ 2 : ℝ) : ℂ) • e₂ := by
        have hstep : P₂ *ᵥ (P₂ *ᵥ e₁) = P₂ *ᵥ e₁ := by
          rw [Matrix.mulVec_mulVec, hP₂_idem]
        have hlhs : P₂ *ᵥ (P₂ *ᵥ e₁) =
            ((s ^ 2 : ℝ) : ℂ) • (P₂ *ᵥ e₁) + ((s * c : ℝ) : ℂ) • (P₂ *ᵥ e₂) := by
          conv_lhs => rw [hP₂_e1]
          rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul]
        rw [hstep, hP₂_e1] at hlhs
        have hscaled : ((s * c : ℝ) : ℂ) • (P₂ *ᵥ e₂) =
            ((s * c : ℝ) : ℂ) • (((s * c : ℝ) : ℂ) • e₁ + ((c ^ 2 : ℝ) : ℂ) • e₂) := by
          ext i
          have hi := congrFun hlhs i
          simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hi ⊢
          have hsc_c : (s : ℂ) ^ 2 + (c : ℂ) ^ 2 = 1 := by exact_mod_cast hsc_sq
          push_cast at hi ⊢
          linear_combination -hi - ((s : ℂ) ^ 2 * e₁ i + (s : ℂ) * c * e₂ i) * hsc_c
        calc
          P₂ *ᵥ e₂ = (((s * c)⁻¹ : ℝ) : ℂ) • (((s * c : ℝ) : ℂ) • (P₂ *ᵥ e₂)) := by
            rw [smul_smul, ← Complex.ofReal_mul, inv_mul_cancel₀ hsc_ne, Complex.ofReal_one,
              one_smul]
          _ = ((s * c : ℝ) : ℂ) • e₁ + ((c ^ 2 : ℝ) : ℂ) • e₂ := by
            rw [hscaled, smul_smul, ← Complex.ofReal_mul, inv_mul_cancel₀ hsc_ne,
              Complex.ofReal_one, one_smul]
      have hR₁_e2 : R₁ *ᵥ e₂ = -e₂ := by
        dsimp only [R₁]
        rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, hP₁_e2, smul_zero, zero_sub]
      have hcosφ : Real.cos φ = c ^ 2 - s ^ 2 := by
        have h2 : φ = 2 * (φ / 2) := by ring
        conv_lhs => rw [h2, Real.cos_two_mul']
      have hsinφ : Real.sin φ = 2 * s * c := by
        have h2 : φ = 2 * (φ / 2) := by ring
        conv_lhs => rw [h2, Real.sin_two_mul]
      have hR₂_e1 : R₂ *ᵥ e₁ = (Real.cos φ : ℂ) • e₁ - (Real.sin φ : ℂ) • e₂ := by
        dsimp only [R₂]
        rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, hP₂_e1, hcosφ, hsinφ]
        ext i
        simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        have hsc_c : (s : ℂ) ^ 2 + (c : ℂ) ^ 2 = 1 := by exact_mod_cast hsc_sq
        push_cast
        linear_combination -e₁ i * hsc_c
      have hR₂_e2 : R₂ *ᵥ e₂ = -(Real.sin φ : ℂ) • e₁ - (Real.cos φ : ℂ) • e₂ := by
        dsimp only [R₂]
        rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, hP₂_e2, hcosφ, hsinφ]
        ext i
        simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        have hsc_c : (s : ℂ) ^ 2 + (c : ℂ) ^ 2 = 1 := by exact_mod_cast hsc_sq
        push_cast
        linear_combination -e₂ i * hsc_c
      have hW_e1 : W *ᵥ e₁ = (Real.cos φ : ℂ) • e₁ + (Real.sin φ : ℂ) • e₂ := by
        change (R₁ * R₂) *ᵥ e₁ = _
        rw [← Matrix.mulVec_mulVec, hR₂_e1, Matrix.mulVec_sub, Matrix.mulVec_smul,
          Matrix.mulVec_smul, hR₁_e1, hR₁_e2, smul_neg, sub_neg_eq_add]
      have hW_e2 : W *ᵥ e₂ = -(Real.sin φ : ℂ) • e₁ + (Real.cos φ : ℂ) • e₂ := by
        change (R₁ * R₂) *ᵥ e₂ = _
        rw [← Matrix.mulVec_mulVec, hR₂_e2, Matrix.mulVec_sub, Matrix.mulVec_smul,
          Matrix.mulVec_smul, hR₁_e1, hR₁_e2, smul_neg, sub_neg_eq_add]
      let v_plus : Fin d → ℂ := (2⁻¹ : ℂ) • (e₁ - Complex.I • e₂)
      let v_minus : Fin d → ℂ := (2⁻¹ : ℂ) • (e₁ + Complex.I • e₂)
      have hsum : e₁ = v_plus + v_minus := by
        ext i; simp [v_plus, v_minus]; ring
      have he2_e1 : vecInner e₂ e₁ = 0 := by
        rw [← star_vecInner, he1_e2, star_zero]
      have he2_inner : vecInner e₂ e₂ = 1 := by
        rw [vecInner_self_eq_normSq, he2_norm, Complex.ofReal_one]
      have hortho : vecInner v_plus v_minus = 0 := by
        change vecInner ((2⁻¹ : ℂ) • (e₁ - Complex.I • e₂))
          ((2⁻¹ : ℂ) • (e₁ + Complex.I • e₂)) = 0
        rw [vecInner_smul_left (2⁻¹ : ℂ), vecInner_smul_right (2⁻¹ : ℂ),
          vecInner_sub_left, vecInner_add_right, vecInner_add_right,
          vecInner_smul_right Complex.I e₁ e₂, vecInner_smul_left Complex.I e₂ e₁,
          vecInner_smul_left Complex.I e₂ (Complex.I • e₂),
          vecInner_smul_right Complex.I e₂ e₂, he1_inner, he1_e2, he2_e1, he2_inner]
        simp [Complex.I_mul_I]
      have hnorm_plus : vecNormSq v_plus = 1 / 2 := by
        have hvp : v_plus = (2⁻¹ : ℂ) • e₁ + (-(2⁻¹ * Complex.I) : ℂ) • e₂ := by
          ext i; simp [v_plus]; ring
        rw [hvp, vecNormSq_linear_comb_of_ortho he1_e2, h_norm, he2_norm]
        simp [map_mul, map_inv₀]
        norm_num
      have hnorm_minus : vecNormSq v_minus = 1 / 2 := by
        have hvm : v_minus = (2⁻¹ : ℂ) • e₁ + ((2⁻¹ * Complex.I) : ℂ) • e₂ := by
          ext i; simp [v_minus]; ring
        rw [hvm, vecNormSq_linear_comb_of_ortho he1_e2, h_norm, he2_norm]
        simp [map_mul, map_inv₀]
        norm_num
      have hexp_pos : Complex.exp (Complex.I * (φ : ℂ)) =
          (Real.cos φ : ℂ) + Complex.I * (Real.sin φ : ℂ) := by
        rw [mul_comm, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, mul_comm]
      have hexp_neg : Complex.exp (-Complex.I * (φ : ℂ)) =
          (Real.cos φ : ℂ) - Complex.I * (Real.sin φ : ℂ) := by
        have harg : -Complex.I * (φ : ℂ) = ((-φ : ℝ) : ℂ) * Complex.I := by push_cast; ring
        rw [harg, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg,
          Real.sin_neg]
        push_cast
        ring
      have hW_vp : W *ᵥ v_plus = Complex.exp (Complex.I * (φ : ℂ)) • v_plus := by
        change W *ᵥ ((2⁻¹ : ℂ) • (e₁ - Complex.I • e₂)) =
          Complex.exp (Complex.I * (φ : ℂ)) • ((2⁻¹ : ℂ) • (e₁ - Complex.I • e₂))
        rw [Matrix.mulVec_smul, Matrix.mulVec_sub, Matrix.mulVec_smul, hW_e1, hW_e2, hexp_pos]
        ext i
        simp only [Pi.smul_apply, Pi.sub_apply, Pi.add_apply, smul_eq_mul]
        linear_combination (2⁻¹ : ℂ) * (Real.sin φ : ℂ) * e₂ i * Complex.I_sq
      have hW_vm : W *ᵥ v_minus = Complex.exp (-Complex.I * (φ : ℂ)) • v_minus := by
        change W *ᵥ ((2⁻¹ : ℂ) • (e₁ + Complex.I • e₂)) =
          Complex.exp (-Complex.I * (φ : ℂ)) • ((2⁻¹ : ℂ) • (e₁ + Complex.I • e₂))
        rw [Matrix.mulVec_smul, Matrix.mulVec_add, Matrix.mulVec_smul, hW_e1, hW_e2, hexp_neg]
        ext i
        simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
        linear_combination (2⁻¹ : ℂ) * (Real.sin φ : ℂ) * e₂ i * Complex.I_sq
      exact ⟨v_plus, v_minus, hsum, hortho, by linarith, fun _ ↦ ⟨hnorm_plus, hnorm_minus⟩,
        hW_vp, hW_vm⟩

/-- Complete Jordan-plane and all-integer-power (`z : ℤ`) spectral decomposition for
`walkStepUnitary rAll rMid U_B`. -/
theorem walkStepUnitary_jordan_decomposition {k_walk w_all w_mid : ℕ}
    (rAll : QRegister w_all k_walk) (rMid : QRegister w_mid k_walk)
    (U_B : Unitary (2 ^ k_walk))
    (e₁ : Fin (2 ^ k_walk) → ℂ)
    (h_in : projIn rAll *ᵥ e₁ = e₁)
    (h_norm : vecNormSq e₁ = 1)
    (φ : ℝ) (hφ0 : 0 ≤ φ) (hφpi : φ ≤ π)
    (h_proj : projIn rAll *ᵥ (pulledProjMid rMid U_B *ᵥ e₁) =
      ((Real.sin (φ / 2) ^ 2 : ℝ) : ℂ) • e₁) :
    let W := walkStepUnitary rAll rMid U_B
    let s := Real.sin (φ / 2)
    ∃ v_plus v_minus : Fin (2 ^ k_walk) → ℂ,
      e₁ = v_plus + v_minus ∧
      vecInner v_plus v_minus = 0 ∧
      vecNormSq v_plus + vecNormSq v_minus = 1 ∧
      (0 < s ∧ s < 1 → vecNormSq v_plus = 1 / 2 ∧ vecNormSq v_minus = 1 / 2) ∧
      W.1 *ᵥ v_plus = Complex.exp (Complex.I * (φ : ℂ)) • v_plus ∧
      W.1 *ᵥ v_minus = Complex.exp (-Complex.I * (φ : ℂ)) • v_minus ∧
      ∀ z : ℤ, (W ^ z).1 *ᵥ e₁ =
        Complex.exp (Complex.I * (z : ℂ) * (φ : ℂ)) • v_plus +
          Complex.exp (-Complex.I * (z : ℂ) * (φ : ℂ)) • v_minus := by
  intro W s
  have hW_val : W.1 = ((2 : ℂ) • projIn rAll - 1) * (1 - (2 : ℂ) • pulledProjMid rMid U_B) := by
    change (reflInUnitary rAll).1 * (reflPulledUnitary rMid U_B).1 = _
    rw [reflInUnitary_val, reflPulledUnitary_val]
  obtain ⟨v_plus, v_minus, hsum, hortho, hnorm, hhalf, hvp, hvm⟩ :=
    two_projector_jordan_decomposition (projIn rAll) (pulledProjMid rMid U_B)
      (projIn_conjTranspose rAll)
      (pulledProjMid_conjTranspose rMid U_B) (pulledProjMid_mul_self rMid U_B)
      e₁ h_in h_norm φ hφ0 hφpi h_proj
  rw [← hW_val] at hvp hvm
  refine ⟨v_plus, v_minus, hsum, hortho, hnorm, hhalf, hvp, hvm, fun z ↦ ?_⟩
  rw [hsum, Matrix.mulVec_add,
    unitary_zpow_mulVec_of_eigenvector W (Complex.exp_ne_zero _) hvp z,
    unitary_zpow_mulVec_of_eigenvector W (Complex.exp_ne_zero _) hvm z,
    ← Complex.exp_int_mul, ← Complex.exp_int_mul]
  have harg1 : (z : ℂ) * (Complex.I * (φ : ℂ)) = Complex.I * (z : ℂ) * (φ : ℂ) := by ring
  have harg2 : (z : ℂ) * (-Complex.I * (φ : ℂ)) = -Complex.I * (z : ℂ) * (φ : ℂ) := by ring
  rw [harg1, harg2]

/-- Spectral-amplification walk angle
$\varphi(E) = 2 \arcsin(\sqrt{(E - E_{\mathrm{LB}}) / (2\Lambda)})$
for an energy $E \in [E_{\mathrm{LB}}, E_{\mathrm{LB}} + 2\Lambda]$. -/
noncomputable def spectralPhase (E_LB Λ E : ℝ) : ℝ :=
  2 * Real.arcsin (√((E - E_LB) / (2 * Λ)))

theorem spectralPhase_nonneg {E_LB Λ E : ℝ} :
    0 ≤ spectralPhase E_LB Λ E := by
  unfold spectralPhase
  have h : 0 ≤ Real.arcsin (√((E - E_LB) / (2 * Λ))) :=
    Real.arcsin_nonneg.mpr (Real.sqrt_nonneg _)
  linarith

theorem spectralPhase_le_pi (E_LB Λ E : ℝ) :
    spectralPhase E_LB Λ E ≤ π := by
  unfold spectralPhase
  linarith [Real.arcsin_le_pi_div_two (√((E - E_LB) / (2 * Λ)))]

theorem sin_half_spectralPhase {E_LB Λ E : ℝ} (hΛ : 0 < Λ)
    (_h_lo : E_LB ≤ E) (h_hi : E ≤ E_LB + 2 * Λ) :
    Real.sin (spectralPhase E_LB Λ E / 2) = √((E - E_LB) / (2 * Λ)) := by
  have hhalf : spectralPhase E_LB Λ E / 2 = Real.arcsin (√((E - E_LB) / (2 * Λ))) := by
    unfold spectralPhase; ring
  have hle1 : √((E - E_LB) / (2 * Λ)) ≤ 1 := by
    rw [Real.sqrt_le_one]
    exact (div_le_one (by linarith)).mpr (by linarith)
  rw [hhalf]
  exact Real.sin_arcsin (by linarith [Real.sqrt_nonneg ((E - E_LB) / (2 * Λ))]) hle1

theorem sin_half_spectralPhase_sq {E_LB Λ E : ℝ} (hΛ : 0 < Λ)
    (h_lo : E_LB ≤ E) (h_hi : E ≤ E_LB + 2 * Λ) :
    Real.sin (spectralPhase E_LB Λ E / 2) ^ 2 = (E - E_LB) / (2 * Λ) := by
  rw [sin_half_spectralPhase hΛ h_lo h_hi, Real.sq_sqrt]
  exact div_nonneg (by linarith) (by linarith)

/-- Exact energy recovery identity $E = E_{\mathrm{LB}} + \Lambda(1 - \cos \varphi(E))$. -/
theorem energy_eq_of_spectralPhase {E_LB Λ E : ℝ} (hΛ : 0 < Λ)
    (h_lo : E_LB ≤ E) (h_hi : E ≤ E_LB + 2 * Λ) :
    E_LB + Λ * (1 - Real.cos (spectralPhase E_LB Λ E)) = E := by
  let φ := spectralPhase E_LB Λ E
  have hcos : 1 - Real.cos φ = 2 * Real.sin (φ / 2) ^ 2 := by
    have h2 : φ = 2 * (φ / 2) := by ring
    have hsc := Real.sin_sq_add_cos_sq (φ / 2)
    have hc2 := Real.cos_two_mul' (φ / 2)
    rw [← h2] at hc2
    linarith
  rw [hcos, sin_half_spectralPhase_sq hΛ h_lo h_hi]
  field_simp [hΛ.ne']
  ring

theorem sin_half_spectralPhase_mem_Ioo {E_LB Λ E : ℝ} (hΛ : 0 < Λ)
    (h_lo : E_LB < E) (h_hi : E < E_LB + 2 * Λ) :
    0 < Real.sin (spectralPhase E_LB Λ E / 2) ∧
      Real.sin (spectralPhase E_LB Λ E / 2) < 1 := by
  rw [sin_half_spectralPhase hΛ h_lo.le h_hi.le]
  have hq_pos : 0 < (E - E_LB) / (2 * Λ) := div_pos (by linarith) (by linarith)
  have hq_lt : (E - E_LB) / (2 * Λ) < 1 := (div_lt_one (by linarith)).mpr (by linarith)
  refine ⟨Real.sqrt_pos.mpr hq_pos, ?_⟩
  calc
    √((E - E_LB) / (2 * Λ)) < √1 := Real.sqrt_lt_sqrt hq_pos.le hq_lt
    _ = 1 := Real.sqrt_one

/-- Direct instantiation of `walkStepUnitary_jordan_decomposition` at `φ = spectralPhase E_LB Λ E`
for an eigenstate witness satisfying `Π_in *ᵥ (Π̃_mid *ᵥ e₁) = ((E - E_LB) / (2 * Λ)) • e₁`. -/
theorem walkStepUnitary_eigen_of_energy {k_walk w_all w_mid : ℕ}
    (rAll : QRegister w_all k_walk) (rMid : QRegister w_mid k_walk)
    (U_B : Unitary (2 ^ k_walk))
    (e₁ : Fin (2 ^ k_walk) → ℂ)
    (h_in : projIn rAll *ᵥ e₁ = e₁) (h_norm : vecNormSq e₁ = 1)
    {E_LB Λ E : ℝ} (hΛ : 0 < Λ) (h_lo : E_LB ≤ E) (h_hi : E ≤ E_LB + 2 * Λ)
    (h_proj : projIn rAll *ᵥ (pulledProjMid rMid U_B *ᵥ e₁) =
      (((E - E_LB) / (2 * Λ) : ℝ) : ℂ) • e₁) :
    let φ := spectralPhase E_LB Λ E
    let W := walkStepUnitary rAll rMid U_B
    ∃ v_plus v_minus : Fin (2 ^ k_walk) → ℂ,
      e₁ = v_plus + v_minus ∧
      vecInner v_plus v_minus = 0 ∧
      vecNormSq v_plus + vecNormSq v_minus = 1 ∧
      (E_LB < E ∧ E < E_LB + 2 * Λ →
        vecNormSq v_plus = 1 / 2 ∧ vecNormSq v_minus = 1 / 2) ∧
      W.1 *ᵥ v_plus = Complex.exp (Complex.I * (φ : ℂ)) • v_plus ∧
      W.1 *ᵥ v_minus = Complex.exp (-Complex.I * (φ : ℂ)) • v_minus ∧
      ∀ z : ℤ, (W ^ z).1 *ᵥ e₁ =
        Complex.exp (Complex.I * (z : ℂ) * (φ : ℂ)) • v_plus +
          Complex.exp (-Complex.I * (z : ℂ) * (φ : ℂ)) • v_minus := by
  have hproj' : projIn rAll *ᵥ (pulledProjMid rMid U_B *ᵥ e₁) =
      ((Real.sin (spectralPhase E_LB Λ E / 2) ^ 2 : ℝ) : ℂ) • e₁ := by
    rw [sin_half_spectralPhase_sq hΛ h_lo h_hi]
    exact h_proj
  obtain ⟨v_plus, v_minus, hsum, hortho, hnorm, hhalf, hvp, hvm, hz⟩ :=
    walkStepUnitary_jordan_decomposition rAll rMid U_B e₁ h_in h_norm
      (spectralPhase E_LB Λ E) spectralPhase_nonneg (spectralPhase_le_pi E_LB Λ E) hproj'
  refine ⟨v_plus, v_minus, hsum, hortho, hnorm, ?_, hvp, hvm, hz⟩
  rintro ⟨hlo', hhi'⟩
  exact hhalf (sin_half_spectralPhase_mem_Ioo hΛ hlo' hhi')

/-!
## Section 3: Dihedral Reflection-Reversal & $M$-Step Perturbation Bounds
-/

section DihedralReversal

variable {G : Type*} [Group G]

/-- Dihedral walk inversion: if $R_1^2 = 1$ and $R_2^2 = 1$, then $(R_1 R_2)^{-1} = R_2 R_1$. -/
theorem walk_inv_eq {R₁ R₂ : G} (hR₁ : R₁ * R₁ = 1) (hR₂ : R₂ * R₂ = 1) :
    (R₁ * R₂)⁻¹ = R₂ * R₁ := by
  have hi₁ : R₁⁻¹ = R₁ := inv_eq_of_mul_eq_one_right hR₁
  have hi₂ : R₂⁻¹ = R₂ := inv_eq_of_mul_eq_one_right hR₂
  rw [_root_.mul_inv_rev, hi₂, hi₁]

/-- Conjugating $W = R_1 R_2$ by $R_1$ inverts the walk: $R_1 W R_1 = R_2 R_1 = W^{-1}$. -/
theorem conj_walk_eq_inv {R₁ R₂ : G} (hR₁ : R₁ * R₁ = 1) (hR₂ : R₂ * R₂ = 1) :
    R₁ * (R₁ * R₂) * R₁ = (R₁ * R₂)⁻¹ := by
  rw [walk_inv_eq hR₁ hR₂, ← mul_assoc, hR₁, one_mul]

end DihedralReversal

theorem euclidean_norm_sq_eq_vecNormSq {d : ℕ} (w : EuclideanSpace ℂ (Fin d)) :
    ‖w‖ ^ 2 = vecNormSq w.ofLp := by
  rw [PiLp.norm_sq_eq_of_L2, vecNormSq]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  exact (Complex.normSq_eq_norm_sq (w.ofLp i)).symm

theorem vecNormSq_mulVec_le_opNorm_sq {d : ℕ} (A : Operator d) (v : Fin d → ℂ) :
    vecNormSq (A *ᵥ v) ≤ ‖A‖ ^ 2 * vecNormSq v := by
  let x : EuclideanSpace ℂ (Fin d) := WithLp.toLp 2 v
  have h := Matrix.l2_opNorm_mulVec A x
  have hsq : ‖(EuclideanSpace.equiv (Fin d) ℂ).symm (A *ᵥ x.ofLp)‖ ^ 2 ≤ (‖A‖ * ‖x‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) h 2
  rw [euclidean_norm_sq_eq_vecNormSq, mul_pow, euclidean_norm_sq_eq_vecNormSq] at hsq
  exact hsq

theorem opNorm_le_of_vecNormSq_mulVec {d : ℕ} (A : Operator d) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ v : Fin d → ℂ, vecNormSq (A *ᵥ v) ≤ C ^ 2 * vecNormSq v) :
    ‖A‖ ≤ C := by
  let T := Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ) A
  rw [← Matrix.l2_opNorm_toEuclideanCLM]
  refine T.opNorm_le_bound hC fun x ↦ ?_
  have hx := h x.ofLp
  have hTx : ‖T x‖ * ‖T x‖ ≤ (C * ‖x‖) * (C * ‖x‖) := by
    have h1 : ‖T x‖ ^ 2 = vecNormSq (A *ᵥ x.ofLp) := by
      rw [euclidean_norm_sq_eq_vecNormSq, Matrix.ofLp_toEuclideanCLM]
    have h2 : (C * ‖x‖) ^ 2 = C ^ 2 * vecNormSq x.ofLp := by
      rw [mul_pow, euclidean_norm_sq_eq_vecNormSq]
    nlinarith [hx, h1, h2]
  exact nonneg_le_nonneg_of_sq_le_sq (mul_nonneg hC (norm_nonneg x)) hTx

/-- Every unitary matrix on a nonempty index type has $L^2$ operator norm at most `1`. -/
theorem unitary_opNorm_le_one {d : ℕ} [NeZero d] (U : Unitary d) :
    ‖U.1‖ ≤ 1 := by
  have : Nonempty (Fin d) := ⟨⟨0, NeZero.pos d⟩⟩
  have hsq : ‖U.1ᴴ * U.1‖ = ‖U.1‖ * ‖U.1‖ := Matrix.l2_opNorm_conjTranspose_mul_self U.1
  have hunit : U.1ᴴ * U.1 = 1 := congrArg Subtype.val (Unitary.star_mul_self U)
  rw [hunit, NormOneClass.norm_one] at hsq
  nlinarith [norm_nonneg U.1]

/-- Embedding a local matrix onto any `QRegister` does not increase its $L^2$ operator norm. -/
theorem embedMatrix_opNorm_le {n k : ℕ} (r : QRegister k n) (A : Operator (2 ^ k)) :
    ‖r.embedMatrix A‖ ≤ ‖A‖ := by
  refine opNorm_le_of_vecNormSq_mulVec (r.embedMatrix A) (norm_nonneg A) fun v ↦ ?_
  have hsplit_sum (w : Fin (2 ^ n) → ℂ) :
      vecNormSq w =
        ∑ env : r.Environment → ZMod 2,
          ∑ loc : Fin (2 ^ k), Complex.normSq (w (r.basisSplitEquiv.symm (loc, env))) := by
    unfold vecNormSq
    rw [← r.basisSplitEquiv.symm.sum_comp (fun i ↦ Complex.normSq (w i)),
      Fintype.sum_prod_type_right]
  rw [hsplit_sum, hsplit_sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun env _ ↦ ?_
  let v_env : Fin (2 ^ k) → ℂ := fun loc ↦ v (r.basisSplitEquiv.symm (loc, env))
  have hloc_eq (loc : Fin (2 ^ k)) :
      (r.embedMatrix A *ᵥ v) (r.basisSplitEquiv.symm (loc, env)) = (A *ᵥ v_env) loc := by
    rw [r.embedMatrix_mulVec_apply]
    have hfst : r.extractIndex (r.basisSplitEquiv.symm (loc, env)) = loc := by
      rw [← QRegister.basisSplitEquiv_apply_fst, Equiv.apply_symm_apply]
    have hsnd : (r.basisSplitEquiv (r.basisSplitEquiv.symm (loc, env))).2 = env := by
      rw [Equiv.apply_symm_apply]
    rw [hfst, hsnd]
    rfl
  simp_rw [hloc_eq]
  exact vecNormSq_mulVec_le_opNorm_sq A v_env

theorem zmod2_eq_zero_or_one (b : ZMod 2) : b = 0 ∨ b = 1 := by
  fin_cases b
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem zmod2_prod_eq_one_iff {α : Type*} [Fintype α] (f : α → ZMod 2) :
    (∏ a : α, f a) = 1 ↔ ∀ a : α, f a = 1 := by
  classical
  constructor
  · intro h a
    rcases zmod2_eq_zero_or_one (f a) with h0 | h1
    · exfalso
      have hzero : (∏ x : α, f x) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ a) h0
      rw [h] at hzero
      exact one_ne_zero hzero
    · exact h1
  · intro h
    simp [h]

theorem basisBits_zero (q : ℕ) (i : Fin q) : basisBits q 0 i = 0 := by
  rw [basisBits_eq_testBit]
  simp

theorem extractIndex_eq_iff {N k : ℕ} (r : QRegister k N) (idx : Fin (2 ^ N))
    (m : Fin (2 ^ k)) :
    r.extractIndex idx = m ↔ ∀ i : Fin k, basisBits N idx (r i) = basisBits k m i := by
  constructor
  · intro h i
    rw [← h, QRegister.basisBits_extractIndex]
  · intro h
    apply (basisBits k).injective
    funext i
    exact (QRegister.basisBits_extractIndex r idx i).trans (h i)

theorem extractIndex_eq_zero_iff {N k : ℕ} (r : QRegister k N) (idx : Fin (2 ^ N)) :
    r.extractIndex idx = 0 ↔ ∀ q ∈ r.image, basisBits N idx q = 0 := by
  rw [extractIndex_eq_iff]
  simp only [basisBits_zero, QRegister.mem_image]
  constructor
  · rintro h _ ⟨i, rfl⟩
    exact h i
  · intro h i
    exact h (r i) ⟨i, rfl⟩

theorem basisOutcomeProjector_zero_congr {N s₁ s₂ : ℕ}
    (r₁ : QRegister s₁ N) (r₂ : QRegister s₂ N) (himg : r₁.image = r₂.image) :
    r₁.basisOutcomeProjector 0 = r₂.basisOutcomeProjector 0 := by
  rw [QRegister.basisOutcomeProjector_eq_diagonal, QRegister.basisOutcomeProjector_eq_diagonal]
  congr 1
  funext idx
  simp only [extractIndex_eq_zero_iff, himg]

theorem basisOutcomeProjector_zero_union {N s s₁ s₂ : ℕ}
    (r : QRegister s N) (r₁ : QRegister s₁ N) (r₂ : QRegister s₂ N)
    (himg : r.image = r₁.image ∪ r₂.image) :
    r.basisOutcomeProjector 0 = r₁.basisOutcomeProjector 0 * r₂.basisOutcomeProjector 0 := by
  rw [QRegister.basisOutcomeProjector_eq_diagonal, QRegister.basisOutcomeProjector_eq_diagonal,
    QRegister.basisOutcomeProjector_eq_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext idx
  simp only [extractIndex_eq_zero_iff, himg, Finset.mem_union]
  have hiff :
      (∀ q, q ∈ r₁.image ∨ q ∈ r₂.image → basisBits N idx q = 0) ↔
        (∀ q ∈ r₁.image, basisBits N idx q = 0) ∧
          (∀ q ∈ r₂.image, basisBits N idx q = 0) :=
    ⟨fun h ↦ ⟨fun q hq ↦ h q (Or.inl hq), fun q hq ↦ h q (Or.inr hq)⟩,
      fun ⟨ha, hb⟩ q hq ↦ hq.elim (ha q) (hb q)⟩
  by_cases h1 : ∀ q ∈ r₁.image, basisBits N idx q = 0 <;>
    by_cases h2 : ∀ q ∈ r₂.image, basisBits N idx q = 0
  · rw [ite_eq_left (hiff.mpr ⟨h1, h2⟩), ite_eq_left h1, ite_eq_left h2, mul_one]
  · rw [ite_eq_right (fun h ↦ h2 (hiff.mp h).2), ite_eq_right h2, mul_zero]
  · rw [ite_eq_right (fun h ↦ h1 (hiff.mp h).1), ite_eq_right h1, zero_mul]
  · rw [ite_eq_right (fun h ↦ h1 (hiff.mp h).1), ite_eq_right h1, zero_mul]

theorem restrictAssertionToZeroAncilla_congr_image {Var : Type} {N s₁ s₂ : ℕ}
    (Θ : QCAssertion Var (2 ^ N)) (r₁ : QRegister s₁ N) (r₂ : QRegister s₂ N)
    (himg : r₁.image = r₂.image) :
    restrictAssertionToZeroAncilla Θ r₁ = restrictAssertionToZeroAncilla Θ r₂ := by
  funext σ
  apply Subtype.ext
  simp [basisOutcomeProjector_zero_congr r₁ r₂ himg]

theorem diagonal_comm_diagonal {d : ℕ} (a b : Fin d → ℂ) :
    Matrix.diagonal a * Matrix.diagonal b = Matrix.diagonal b * Matrix.diagonal a := by
  rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  exact mul_comm (a i) (b i)

theorem basisOutcomeProjector_comm_any {N k₁ k₂ : ℕ}
    (r₁ : QRegister k₁ N) (o₁ : Fin (2 ^ k₁))
    (r₂ : QRegister k₂ N) (o₂ : Fin (2 ^ k₂)) :
    r₁.basisOutcomeProjector o₁ * r₂.basisOutcomeProjector o₂ =
      r₂.basisOutcomeProjector o₂ * r₁.basisOutcomeProjector o₁ := by
  rw [QRegister.basisOutcomeProjector_eq_diagonal, QRegister.basisOutcomeProjector_eq_diagonal]
  exact diagonal_comm_diagonal _ _

theorem restrictAssertionToZeroAncilla_union {Var : Type} {N s s₁ s₂ : ℕ}
    (Θ : QCAssertion Var (2 ^ N)) (r : QRegister s N)
    (r₁ : QRegister s₁ N) (r₂ : QRegister s₂ N)
    (himg : r.image = r₁.image ∪ r₂.image) :
    restrictAssertionToZeroAncilla Θ r =
      restrictAssertionToZeroAncilla (restrictAssertionToZeroAncilla Θ r₂) r₁ := by
  funext σ
  apply Subtype.ext
  simp only [restrictAssertionToZeroAncilla_coe, HermitianMat.conj_conj,
    basisOutcomeProjector_zero_union r r₁ r₂ himg]

end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.QubitisedWalk

namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.CleanDyn
open QuantumComputation.Specs Operator QProg

theorem CleanRealizes.congr_scr {Var : Type} [Fintype Var] [DecidableEq Var]
    {N k s₁ s₂ : ℕ}
    {v : Var} {rAct : QRegister k N} {rScr₁ : QRegister s₁ N} {rScr₂ : QRegister s₂ N}
    {U : Unitary (2 ^ k)} {P : DynamicCircuit Var N}
    (h : CleanRealizes v rAct rScr₁ U P) (himg : rScr₁.image = rScr₂.image) :
    CleanRealizes v rAct rScr₂ U P := by
  rcases h with ⟨htoff, hupd, hwp, hclean⟩
  refine ⟨htoff, hupd, ?_, ?_⟩
  · intro Θ hΘ
    rw [← QubitisedWalk.restrictAssertionToZeroAncilla_congr_image _ rScr₁ rScr₂ himg,
      ← QubitisedWalk.restrictAssertionToZeroAncilla_congr_image _ rScr₁ rScr₂ himg]
    exact hwp Θ hΘ
  · intro Θ
    rw [← QubitisedWalk.restrictAssertionToZeroAncilla_congr_image Θ rScr₁ rScr₂ himg,
      ← QubitisedWalk.restrictAssertionToZeroAncilla_congr_image _ rScr₁ rScr₂ himg,
      ← QubitisedWalk.restrictAssertionToZeroAncilla_congr_image (wp P.compile Θ) rScr₁ rScr₂ himg]
    exact hclean Θ

end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.CleanDyn

namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.QubitisedWalk
open QuantumComputation.Specs QuantumComputation.Specs.P450
open Operator QProg Real CleanDyn
open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator Circuit.Notation

theorem disjointWires_of_disjoint_image {N k₁ k₂ : ℕ}
    {r₁ : QRegister k₁ N} {r₂ : QRegister k₂ N}
    (h : Disjoint r₁.image r₂.image) : r₁.DisjointWires r₂ := by
  rw [QRegister.disjoint_iff]
  intro i j hij
  exact Finset.disjoint_left.mp h
    ((QRegister.mem_image r₁ (r₁ i)).mpr ⟨i, rfl⟩)
    ((QRegister.mem_image r₂ (r₁ i)).mpr ⟨j, hij.symm⟩)

theorem circuit_eval_comm_projector_of_disjoint {N s : ℕ}
    (c : Circuit N) (r : QRegister s N) (hdisj : Disjoint c.support r.image) :
    c.eval.1 * r.basisOutcomeProjector 0 = r.basisOutcomeProjector 0 * c.eval.1 := by
  induction c with
  | identity => simp
  | gate g reg =>
      simp only [Circuit.support_gate] at hdisj
      have hdw : r.DisjointWires reg := disjointWires_of_disjoint_image hdisj.symm
      exact (basisOutcomeProjector_comm_embedMatrix r reg hdw 0 g.eval.1).symm
  | seq c₁ c₂ ih₁ ih₂ =>
      simp only [Circuit.support_seq, Finset.disjoint_union_left] at hdisj
      simp only [Circuit.eval_seq, Submonoid.coe_mul]
      rw [Matrix.mul_assoc, ih₁ hdisj.1, ← Matrix.mul_assoc, ih₂ hdisj.2, Matrix.mul_assoc]

theorem wp_qAssign_restrict_of_comm {Var : Type} [Fintype Var] {N s : ℕ}
    (U : Unitary (2 ^ N)) (r : QRegister s N)
    (hcomm : U.1 * r.basisOutcomeProjector 0 = r.basisOutcomeProjector 0 * U.1)
    (Θ : QCAssertion Var (2 ^ N)) :
    qcWpQAssign U (restrictAssertionToZeroAncilla Θ r) =
      restrictAssertionToZeroAncilla (qcWpQAssign U Θ) r := by
  funext σ
  apply Subtype.ext
  have hadj : r.basisOutcomeProjector 0 * U.1ᴴ = U.1ᴴ * r.basisOutcomeProjector 0 := by
    have h := congrArg Matrix.conjTranspose hcomm
    simpa only [Matrix.conjTranspose_mul, QRegister.basisOutcomeProjector_conjTranspose] using h
  simp only [qcWpQAssign, qcQAssignObsMap, Observable.conj_coe, Unitary.coe_star,
    Matrix.star_eq_conjTranspose, restrictAssertionToZeroAncilla_coe, HermitianMat.conj_conj]
  rw [hadj]

private theorem wp_measure_val {Var : Type} [Finite Var] [DecidableEq Var] {N : ℕ}
    (w : Var) (reg : QRegister 1 N) (A : QCAssertion Var (2 ^ N)) (σ : Store Var) :
    (wp (DynamicCircuit.measure w reg).compile A σ).1 =
      ∑ o : Fin 2,
        (A (Store.subst σ w (↑o.val))).1.conj (reg.basisOutcomeProjector o)ᴴ := by
  have := Fintype.ofFinite Var
  rw [DynamicCircuit.compile_measure, QProg.measureRegister, qc_wp_qMeasure',
    qc_wp_qMeasure_apply, qc_qMeasure_obs_map_coe]
  simp [qc_qMeasure_outcome_herm_eq_conj]

/-- Any `DynamicCircuit` whose syntactic support is disjoint from `r.image` commutes with
`restrictAssertionToZeroAncilla _ r` in weakest-precondition semantics. -/
theorem wp_compile_restrict_of_disjoint {Var : Type} [Finite Var] [DecidableEq Var] {N s : ℕ}
    (P : DynamicCircuit Var N) (r : QRegister s N) (hdisj : Disjoint P.support r.image)
    (Θ : QCAssertion Var (2 ^ N)) :
    wp P.compile (restrictAssertionToZeroAncilla Θ r) =
      restrictAssertionToZeroAncilla (wp P.compile Θ) r := by
  have := Fintype.ofFinite Var
  induction P using DynamicCircuit.qcInd generalizing Θ with
  | circuit c =>
      simp only [DynamicCircuit.support_circuit] at hdisj
      rw [DynamicCircuit.compile_circuit, DynamicCircuit.qc_wp_circuit_compile,
        DynamicCircuit.qc_wp_circuit_compile]
      exact wp_qAssign_restrict_of_comm c.eval r
        (circuit_eval_comm_projector_of_disjoint c r hdisj) Θ
  | measure w reg =>
      funext σ
      apply Subtype.ext
      rw [wp_measure_val, restrictAssertionToZeroAncilla_coe, wp_measure_val, map_sum]
      refine Finset.sum_congr rfl fun o _ ↦ ?_
      simp only [restrictAssertionToZeroAncilla_coe, HermitianMat.conj_conj,
        QRegister.basisOutcomeProjector_conjTranspose]
      rw [basisOutcomeProjector_comm_any r 0 reg o]
  | qIf cond t f iht ihf =>
      simp only [DynamicCircuit.support_qcRawQIf, Finset.disjoint_union_left] at hdisj
      funext σ
      apply Subtype.ext
      simp only [DynamicCircuit.compile_qcRawQIf, wp_qcRawQIf, restrictAssertionToZeroAncilla_coe]
      split_ifs with hc
      · simpa only [restrictAssertionToZeroAncilla_coe] using
          congrArg Subtype.val (congrFun (iht hdisj.1 Θ) σ)
      · simpa only [restrictAssertionToZeroAncilla_coe] using
          congrArg Subtype.val (congrFun (ihf hdisj.2 Θ) σ)
  | seq p₁ p₂ ih₁ ih₂ =>
      simp only [DynamicCircuit.support_seq, Finset.disjoint_union_left] at hdisj
      change wp p₁.compile (wp p₂.compile (restrictAssertionToZeroAncilla Θ r)) =
        restrictAssertionToZeroAncilla (wp p₁.compile (wp p₂.compile Θ)) r
      rw [ih₂ hdisj.2 Θ, ih₁ hdisj.1 (wp p₂.compile Θ)]

theorem CleanRealizes_circuit_of_disjoint {Var : Type} [Fintype Var] [DecidableEq Var] {N s : ℕ}
    (v : Var) (rScr : QRegister s N) (c : Circuit N)
    (htoff : c.count PrimitiveGate.TOFF = 0)
    (hdisj : Disjoint c.support rScr.image) :
    CleanRealizes v (QRegister.whole N) rScr c.eval (.circuit c) := by
  refine ⟨htoff, ?_, ?_, ?_⟩
  · intro Θ hΘ σ val
    simp [DynamicCircuit.compile_circuit, qcWpQAssign, hΘ σ val]
  · intro Θ _
    simp [DynamicCircuit.compile_circuit,
      QRegister.whole_embedUnitary]
  · intro Θ
    rw [wp_compile_restrict_of_disjoint (.circuit c) rScr hdisj Θ,
      restrictAssertionToZeroAncilla_idem]

/-!
### Diagonal Sign Unitaries (`diagSignUnitary`) & Gate Conjugation
-/

/-- Phase sign `(-1)^b` for a `ZMod 2` bit `b`. -/
def bitSign (b : ZMod 2) : ℂ :=
  if b = 0 then 1 else -1

@[simp]
theorem bitSign_zero : bitSign 0 = 1 := rfl

@[simp]
theorem bitSign_one : bitSign 1 = -1 := rfl

theorem bitSign_add (a b : ZMod 2) : bitSign (a + b) = bitSign a * bitSign b := by
  have h11 : (1 : ZMod 2) + 1 = 0 := CharTwo.add_self_eq_zero 1
  rcases zmod2_eq_zero_or_one a with rfl | rfl
  · rcases zmod2_eq_zero_or_one b with rfl | rfl <;> simp [bitSign]
  · rcases zmod2_eq_zero_or_one b with rfl | rfl
    · simp [bitSign]
    · simp [bitSign, h11]

@[simp]
theorem star_bitSign (b : ZMod 2) : star (bitSign b) = bitSign b := by
  rcases zmod2_eq_zero_or_one b with rfl | rfl <;> simp [bitSign]

@[simp]
theorem bitSign_mul_self (b : ZMod 2) : bitSign b * bitSign b = 1 := by
  rcases zmod2_eq_zero_or_one b with rfl | rfl <;> norm_num [bitSign]

/-- Diagonal `±1` sign operator `|β⟩ ↦ (-1)^{f β} |β⟩` on `N` qubits. -/
noncomputable def diagSignMatrix {N : ℕ} (f : BitAssignment N → ZMod 2) : Operator (2 ^ N) :=
  Matrix.diagonal fun idx ↦ bitSign (f (basisBits N idx))

@[simp]
theorem diagSignMatrix_conjTranspose {N : ℕ} (f : BitAssignment N → ZMod 2) :
    (diagSignMatrix f)ᴴ = diagSignMatrix f := by
  unfold diagSignMatrix
  rw [Matrix.diagonal_conjTranspose]
  congr 1
  funext idx
  exact star_bitSign _

@[simp]
theorem diagSignMatrix_mul {N : ℕ} (f g : BitAssignment N → ZMod 2) :
    diagSignMatrix f * diagSignMatrix g = diagSignMatrix (fun β ↦ f β + g β) := by
  unfold diagSignMatrix
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext idx
  exact (bitSign_add _ _).symm

@[simp]
theorem diagSignMatrix_zero {N : ℕ} :
    diagSignMatrix (fun _ : BitAssignment N ↦ 0) = 1 := by
  simp [diagSignMatrix]

/-- Bundled diagonal `±1` sign unitary `|β⟩ ↦ (-1)^{f β} |β⟩` on `N` qubits. -/
noncomputable def diagSignUnitary {N : ℕ} (f : BitAssignment N → ZMod 2) : Unitary (2 ^ N) :=
  ⟨diagSignMatrix f, by
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose,
      diagSignMatrix_conjTranspose, diagSignMatrix_mul]
    have hzero : (fun β : BitAssignment N ↦ f β + f β) = fun _ ↦ 0 := by
      funext β
      exact CharTwo.add_self_eq_zero (f β)
    rw [hzero, diagSignMatrix_zero]⟩

@[simp]
theorem diagSignUnitary_val {N : ℕ} (f : BitAssignment N → ZMod 2) :
    (diagSignUnitary f).1 = diagSignMatrix f := rfl

@[simp]
theorem diagSignUnitary_mul {N : ℕ} (f g : BitAssignment N → ZMod 2) :
    diagSignUnitary f * diagSignUnitary g = diagSignUnitary (fun β ↦ f β + g β) := by
  apply Subtype.ext
  exact diagSignMatrix_mul f g

theorem diagSignUnitary_comm_projector {N s : ℕ} (f : BitAssignment N → ZMod 2)
    (r : QRegister s N) :
    (diagSignUnitary f).1 * r.basisOutcomeProjector 0 =
      r.basisOutcomeProjector 0 * (diagSignUnitary f).1 := by
  rw [diagSignUnitary_val, diagSignMatrix, QRegister.basisOutcomeProjector_eq_diagonal]
  exact diagonal_comm_diagonal _ _

theorem wp_qAssign_diagSignUnitary_restrict {Var : Type} [Fintype Var] {N s : ℕ}
    (f : BitAssignment N → ZMod 2) (r : QRegister s N) (Θ : QCAssertion Var (2 ^ N)) :
    qcWpQAssign (diagSignUnitary f) (restrictAssertionToZeroAncilla Θ r) =
      restrictAssertionToZeroAncilla (qcWpQAssign (diagSignUnitary f) Θ) r :=
  wp_qAssign_restrict_of_comm (diagSignUnitary f) r (diagSignUnitary_comm_projector f r) Θ

/-- Computational-basis ket `|β⟩` on `N` qubits. -/
noncomputable abbrev ket {N : ℕ} (β : BitAssignment N) : Fin (2 ^ N) → ℂ :=
  basisState ((basisBits N).symm β)

theorem single_eq_ket {N : ℕ} (g : Fin (2 ^ N)) :
    (Pi.single g 1 : Fin (2 ^ N) → ℂ) = ket (basisBits N g) := by
  have h : (basisBits N).symm (basisBits N g) = g := (basisBits N).symm_apply_apply g
  simp [ket, basisState, h]

theorem matrix_ext_ket {N : ℕ} {A B : Operator (2 ^ N)}
    (h : ∀ β : BitAssignment N, A *ᵥ ket β = B *ᵥ ket β) : A = B := by
  ext i j
  have hij := congrFun (h (basisBits N j)) i
  simpa only [← single_eq_ket, Matrix.mulVec_single_one, Matrix.col_apply] using hij

theorem diagSignUnitary_mulVec_ket {N : ℕ} (f : BitAssignment N → ZMod 2)
    (β : BitAssignment N) :
    (diagSignUnitary f).1 *ᵥ ket β = bitSign (f β) • ket β := by
  funext i
  rw [diagSignUnitary_val, diagSignMatrix, Matrix.mulVec_diagonal]
  simp only [ket, basisState, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
  by_cases hi : i = (basisBits N).symm β
  · subst hi
    have hb : basisBits N ((basisBits N).symm β) = β :=
      (basisBits N).apply_symm_apply β
    simp [hb]
  · simp [hi]

/-- Write local register bits `γ` onto global bit assignment `β`. -/
noncomputable def writeRegBits {N k : ℕ} (β : BitAssignment N) (r : QRegister k N)
    (γ : BitAssignment k) : BitAssignment N :=
  basisBits N (r.replaceIndex ((basisBits N).symm β) ((basisBits k).symm γ))

theorem writeRegBits_eq_update {N k : ℕ} (β : BitAssignment N) (r : QRegister k N)
    (γ : BitAssignment k) (i₀ : Fin k) (hγ : ∀ i, i ≠ i₀ → γ i = β (r i)) :
    writeRegBits β r γ = Function.update β (r i₀) (γ i₀) := by
  have hsymm : basisBits N ((basisBits N).symm β) = β :=
    (basisBits N).apply_symm_apply β
  have hsymm_k : basisBits k ((basisBits k).symm γ) = γ :=
    (basisBits k).apply_symm_apply γ
  funext w
  by_cases hw : w ∈ Set.range r.wires
  · obtain ⟨i, rfl⟩ := hw
    dsimp only [writeRegBits]
    rw [QRegister.basisBits_replaceIndex_apply, hsymm_k]
    by_cases hi : i = i₀
    · subst hi; simp
    · rw [Function.update_of_ne (fun h ↦ hi (r.wires.injective h)), hγ i hi]
  · dsimp only [writeRegBits]
    rw [QRegister.basisBits_replaceIndex_of_not_mem _ _ _ _ hw, hsymm, Function.update_of_ne]
    exact fun h ↦ hw ⟨i₀, h.symm⟩

theorem embedMatrix_mulVec_ket {N k : ℕ} (r : QRegister k N)
    (A : Operator (2 ^ k)) (β : BitAssignment N) :
    r.embedMatrix A *ᵥ ket β =
      ∑ l : Fin (2 ^ k),
        A l ((basisBits k).symm (fun i ↦ β (r i))) •
          ket (writeRegBits β r (basisBits k l)) := by
  have hsymm : basisBits N ((basisBits N).symm β) = β :=
    (basisBits N).apply_symm_apply β
  have hext : r.extractIndex ((basisBits N).symm β) =
      (basisBits k).symm (fun i ↦ β (r i)) := by
    simp [QRegister.extractIndex, hsymm]
  have hcol (j : Fin (2 ^ k)) :
      A *ᵥ (Pi.single j 1) = ∑ l : Fin (2 ^ k), A l j • Pi.single l 1 := by
    funext x
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  rw [ket, basisState, r.embedMatrix_mulVec_single_factors, hext, hcol,
    QRegister.tensorState_sum_left]
  refine Finset.sum_congr rfl fun l _ ↦ ?_
  rw [QRegister.tensorState_smul_left, QRegister.tensorState_single_replaceIndex]
  have hl : (basisBits k).symm (basisBits k l) = l :=
    (basisBits k).symm_apply_apply l
  have hrep : ∀ idx : Fin (2 ^ N), (basisBits N).symm (basisBits N idx) = idx :=
    (basisBits N).symm_apply_apply
  simp [writeRegBits, ket, basisState, hl, hrep]

theorem singleton_embedMatrix_mulVec_ket {N : ℕ} (q : Wire N) (A : Operator 2)
    (β : BitAssignment N) :
    (QRegister.singleton q).embedMatrix A *ᵥ ket β =
      A 0 (if β q = 0 then 0 else 1) • ket (Function.update β q 0) +
        A 1 (if β q = 0 then 0 else 1) • ket (Function.update β q 1) := by
  have hloc : ((basisBits 1).symm (fun _ ↦ β q) : Fin 2) =
      if β q = 0 then 0 else 1 := by
    have h : ∀ b : ZMod 2,
        ((basisBits 1).symm (fun _ ↦ b) : Fin 2) = if b = 0 then 0 else 1 := by decide
    exact h (β q)
  have hw (l : Fin 2) (b : ZMod 2) (hb : basisBits 1 l = fun _ ↦ b) :
      writeRegBits β (QRegister.singleton q) (basisBits 1 l) = Function.update β q b := by
    rw [writeRegBits_eq_update _ _ _ 0 (fun i hi ↦ absurd (Subsingleton.elim i 0) hi), hb]
    rfl
  have hloc' :
      ((basisBits 1).symm (fun i ↦ β ((QRegister.singleton q).wires i)) : Fin 2) =
        if β q = 0 then 0 else 1 := hloc
  rw [embedMatrix_mulVec_ket, hloc']
  change ∑ l : Fin 2, _ = _
  rw [Fin.sum_univ_two, hw 0 0 (by decide), hw 1 1 (by decide)]

theorem embedMatrix_permMatrix_mulVec_ket {N k : ℕ} (r : QRegister k N)
    (σ : Equiv.Perm (Fin (2 ^ k))) (β : BitAssignment N) :
    r.embedMatrix (Equiv.Perm.permMatrix ℂ σ) *ᵥ ket β =
      ket (writeRegBits β r
        (basisBits k (σ.symm ((basisBits k).symm (fun i ↦ β (r i)))))) := by
  let idx := (basisBits k).symm (fun i ↦ β (r i))
  rw [embedMatrix_mulVec_ket, Finset.sum_eq_single (σ.symm idx)]
  · simp [idx, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]
  · intro l _ hl
    have hne : σ l ≠ idx := fun h ↦ hl (by rw [← h, Equiv.symm_apply_apply])
    simp [idx, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, hne]
  · simp

theorem ket_X {N : ℕ} (q : Wire N) (β : BitAssignment N) :
    (Circuit.X q).eval.1 *ᵥ ket β = ket (Function.update β q (β q + 1)) := by
  rw [Circuit.eval_single, QRegister.embedUnitary_val, PrimitiveGate.eval]
  change (QRegister.singleton q).embedMatrix !![0, 1; 1, 0] *ᵥ ket β = _
  rw [singleton_embedMatrix_mulVec_ket]
  have h11 : (1 : ZMod 2) + 1 = 0 := CharTwo.add_self_eq_zero 1
  rcases zmod2_eq_zero_or_one (β q) with hb | hb
  · simp [hb]
  · simp [hb, h11]

theorem ket_Z {N : ℕ} (q : Wire N) (β : BitAssignment N) :
    (Circuit.Z q).eval.1 *ᵥ ket β = bitSign (β q) • ket β := by
  rw [Circuit.eval_single, QRegister.embedUnitary_val, PrimitiveGate.eval]
  change (QRegister.singleton q).embedMatrix !![1, 0; 0, -1] *ᵥ ket β = _
  rw [singleton_embedMatrix_mulVec_ket]
  have e := Function.update_eq_self q β
  rcases zmod2_eq_zero_or_one (β q) with hb | hb <;> rw [hb] at e <;> simp [hb, e, bitSign]

theorem ket_H {N : ℕ} (q : Wire N) (β : BitAssignment N) :
    (Circuit.H q).eval.1 *ᵥ ket β =
      ((√(1 / 2) : ℝ) : ℂ) • (ket (Function.update β q 0) +
        bitSign (β q) • ket (Function.update β q 1)) := by
  rw [Circuit.eval_single, QRegister.embedUnitary_val, PrimitiveGate.eval]
  change (QRegister.singleton q).embedMatrix
    ((√(1 / 2) : ℝ) • !![(1 : ℂ), 1; 1, -1]) *ᵥ ket β = _
  rw [singleton_embedMatrix_mulVec_ket]
  rcases zmod2_eq_zero_or_one (β q) with hb | hb <;>
    simp [hb, bitSign, smul_add, Complex.real_smul]

theorem ket_CNOT {N : ℕ} (c t : Wire N) (h : c ≠ t) (β : BitAssignment N) :
    (Circuit.CNOT c t h).eval.1 *ᵥ ket β = ket (Function.update β t (β t + β c)) := by
  rw [Circuit.eval_gate, QRegister.embedUnitary_val, PrimitiveGate.eval_cnot_val,
    embedMatrix_permMatrix_mulVec_ket]
  have hloc : ∀ γ : BitAssignment 2,
      basisBits 2 ((Equiv.swap (1 : Fin 4) 3).symm ((basisBits 2).symm γ)) =
        Function.update γ 1 (γ 1 + γ 0) := by decide
  rw [hloc, writeRegBits_eq_update _ _ _ 1]
  · simp
  · intro i hi
    fin_cases i
    · simp
    · exact absurd rfl hi

theorem ket_TOFF {N : ℕ} (c₁ c₂ t : Wire N) (h₁₂ : c₁ ≠ c₂) (h₁t : c₁ ≠ t) (h₂t : c₂ ≠ t)
    (β : BitAssignment N) :
    (Circuit.TOFF c₁ c₂ t h₁₂ h₁t h₂t).eval.1 *ᵥ ket β =
      ket (Function.update β t (β t + β c₁ * β c₂)) := by
  rw [Circuit.eval_gate, QRegister.embedUnitary_val, PrimitiveGate.eval_toffoli_val,
    embedMatrix_permMatrix_mulVec_ket]
  have hloc : ∀ γ : BitAssignment 3,
      basisBits 3 ((Equiv.swap (3 : Fin 8) 7).symm ((basisBits 3).symm γ)) =
        Function.update γ 2 (γ 2 + γ 0 * γ 1) := by decide
  rw [hloc, writeRegBits_eq_update _ _ _ 2]
  · simp
  · intro i hi
    fin_cases i
    · simp
    · simp
    · exact absurd rfl hi

theorem z_eval_eq_diagSignUnitary {N : ℕ} (q : Wire N) :
    (Circuit.Z q).eval = diagSignUnitary (fun β ↦ β q) := by
  apply Subtype.ext
  apply matrix_ext_ket
  intro β
  rw [ket_Z, diagSignUnitary_mulVec_ket]

/-- Two-qubit Clifford `CZ` gate (`H target ;;ᶜ CNOT control target ;;ᶜ H target`,
`0` `T` gates). -/
def czCircuit {N : ℕ} (q₁ q₂ : Wire N) (hne : q₁ ≠ q₂) : Circuit N :=
  Circuit.H q₂ ;;ᶜ Circuit.CNOT q₁ q₂ hne ;;ᶜ Circuit.H q₂

@[simp]
theorem czCircuit_count_t {N : ℕ} (q₁ q₂ : Wire N) (hne : q₁ ≠ q₂) :
    (czCircuit q₁ q₂ hne).count PrimitiveGate.T = 0 := by
  simp [czCircuit, Circuit.CNOT]

@[simp]
theorem czCircuit_count_toff {N : ℕ} (q₁ q₂ : Wire N) (hne : q₁ ≠ q₂) :
    (czCircuit q₁ q₂ hne).count PrimitiveGate.TOFF = 0 := by
  simp [czCircuit, Circuit.CNOT]

theorem czCircuit_support {N : ℕ} (q₁ q₂ : Wire N) (hne : q₁ ≠ q₂) :
    (czCircuit q₁ q₂ hne).support = {q₁, q₂} := by
  ext q
  simp only [czCircuit, Circuit.support_seq, Circuit.support_single, Circuit.support_cnot,
    Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
  tauto

theorem czCircuit_eval_eq_diagSignUnitary {N : ℕ} (q₁ q₂ : Wire N) (hne : q₁ ≠ q₂) :
    (czCircuit q₁ q₂ hne).eval = diagSignUnitary (fun β ↦ β q₁ * β q₂) := by
  apply Subtype.ext
  apply matrix_ext_ket
  intro β
  have hsq : (((√(1 / 2) : ℝ) : ℂ) * ((√(1 / 2) : ℝ) : ℂ)) = 1 / 2 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
    norm_num
  have h11 : (1 : ZMod 2) + 1 = 0 := CharTwo.add_self_eq_zero 1
  rw [czCircuit, Circuit.eval_seq, Circuit.eval_seq, Submonoid.coe_mul, Submonoid.coe_mul,
    ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  simp only [ket_H, ket_CNOT, Matrix.mulVec_smul, Matrix.mulVec_add,
    Function.update_self, Function.update_of_ne hne, Function.update_idem,
    diagSignUnitary_mulVec_ket]
  rcases zmod2_eq_zero_or_one (β q₁) with h1 | h1 <;>
    rcases zmod2_eq_zero_or_one (β q₂) with h2 | h2
  · have e0 : Function.update β q₂ 0 = β := by rw [← h2]; exact Function.update_eq_self q₂ β
    simp only [h1, h2, e0, bitSign, add_zero, mul_zero, one_ne_zero, ↓reduceIte,
      smul_add, smul_smul]
    match_scalars <;> first | ring1 | linear_combination 2 * hsq
  · have e1 : Function.update β q₂ 1 = β := by rw [← h2]; exact Function.update_eq_self q₂ β
    simp only [h1, h2, e1, bitSign, add_zero, mul_one, one_ne_zero, ↓reduceIte,
      smul_add, smul_smul]
    match_scalars <;> first | ring1 | linear_combination 2 * hsq
  · have e0 : Function.update β q₂ 0 = β := by rw [← h2]; exact Function.update_eq_self q₂ β
    simp only [h1, h2, e0, h11, zero_add, bitSign, mul_zero, one_ne_zero, ↓reduceIte,
      smul_add, smul_smul]
    match_scalars <;> first | ring1 | linear_combination 2 * hsq
  · have e1 : Function.update β q₂ 1 = β := by rw [← h2]; exact Function.update_eq_self q₂ β
    simp only [h1, h2, e1, h11, zero_add, bitSign, mul_one, one_ne_zero, ↓reduceIte,
      smul_add, smul_smul]
    match_scalars <;> first | ring1 | linear_combination -2 * hsq

/-- Global `-1` Clifford gadget `X q ;;ᶜ Z q ;;ᶜ X q ;;ᶜ Z q` (`0` `T` gates). -/
def globalMinusCircuit {N : ℕ} (q : Wire N) : Circuit N :=
  Circuit.X q ;;ᶜ Circuit.Z q ;;ᶜ Circuit.X q ;;ᶜ Circuit.Z q

@[simp]
theorem globalMinusCircuit_count_t {N : ℕ} (q : Wire N) :
    (globalMinusCircuit q).count PrimitiveGate.T = 0 := by
  simp [globalMinusCircuit]

@[simp]
theorem globalMinusCircuit_count_toff {N : ℕ} (q : Wire N) :
    (globalMinusCircuit q).count PrimitiveGate.TOFF = 0 := by
  simp [globalMinusCircuit]

theorem globalMinusCircuit_support {N : ℕ} (q : Wire N) :
    (globalMinusCircuit q).support = {q} := by
  ext w
  simp [globalMinusCircuit]

theorem globalMinusCircuit_eval_eq_diagSignUnitary {N : ℕ} (q : Wire N) :
    (globalMinusCircuit q).eval = diagSignUnitary (fun _ ↦ 1) := by
  apply Subtype.ext
  apply matrix_ext_ket
  intro β
  rw [globalMinusCircuit, Circuit.eval_seq, Circuit.eval_seq, Circuit.eval_seq,
    Submonoid.coe_mul, Submonoid.coe_mul, Submonoid.coe_mul,
    ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    ket_X, ket_Z, Matrix.mulVec_smul, ket_X, Matrix.mulVec_smul, ket_Z,
    Function.update_self, Function.update_idem, diagSignUnitary_mulVec_ket]
  have hadd : β q + 1 + 1 = β q := by rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
  rw [hadd, Function.update_eq_self, smul_smul, ← bitSign_add]
  have h1 : β q + 1 + β q = 1 := by rw [add_right_comm, CharTwo.add_self_eq_zero, zero_add]
  rw [h1]

theorem x_conj_diagSignUnitary {N : ℕ} (q : Wire N) (f : BitAssignment N → ZMod 2) :
    (Circuit.X q).eval * diagSignUnitary f * (Circuit.X q).eval =
      diagSignUnitary (fun β ↦ f (Function.update β q (β q + 1))) := by
  apply Subtype.ext
  apply matrix_ext_ket
  intro β
  rw [Submonoid.coe_mul, Submonoid.coe_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    ket_X, diagSignUnitary_mulVec_ket, Matrix.mulVec_smul, ket_X,
    Function.update_self, Function.update_idem, diagSignUnitary_mulVec_ket]
  have hadd : β q + 1 + 1 = β q := by rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
  rw [hadd, Function.update_eq_self]

theorem toffoli_conj_diagSignUnitary {N : ℕ} (c₁ c₂ t : Wire N)
    (h₁₂ : c₁ ≠ c₂) (h₁t : c₁ ≠ t) (h₂t : c₂ ≠ t) (f : BitAssignment N → ZMod 2) :
    (Circuit.TOFF c₁ c₂ t h₁₂ h₁t h₂t).eval * diagSignUnitary f *
        (Circuit.TOFF c₁ c₂ t h₁₂ h₁t h₂t).eval =
      diagSignUnitary (fun β ↦ f (Function.update β t (β t + β c₁ * β c₂))) := by
  apply Subtype.ext
  apply matrix_ext_ket
  intro β
  rw [Submonoid.coe_mul, Submonoid.coe_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    ket_TOFF, diagSignUnitary_mulVec_ket, Matrix.mulVec_smul, ket_TOFF,
    Function.update_self, Function.update_of_ne h₁t, Function.update_of_ne h₂t,
    Function.update_idem, diagSignUnitary_mulVec_ket]
  have hadd : β t + β c₁ * β c₂ + β c₁ * β c₂ = β t := by
    rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
  rw [hadd, Function.update_eq_self]

theorem toffoli_eval_sq {N : ℕ} (c₁ c₂ t : Wire N)
    (h₁₂ : c₁ ≠ c₂) (h₁t : c₁ ≠ t) (h₂t : c₂ ≠ t) :
    (Circuit.TOFF c₁ c₂ t h₁₂ h₁t h₂t).eval * (Circuit.TOFF c₁ c₂ t h₁₂ h₁t h₂t).eval = 1 := by
  have h := toffoli_conj_diagSignUnitary c₁ c₂ t h₁₂ h₁t h₂t (fun _ ↦ 0)
  have h1 : diagSignUnitary (fun _ : BitAssignment N ↦ 0) = 1 := by
    apply Subtype.ext; exact diagSignMatrix_zero
  simpa [h1] using h

theorem CleanRealizes_xSandwich {Var : Type} [Fintype Var] [DecidableEq Var] {N s : ℕ}
    {v : Var} {rScr : QRegister s N} {q : Wire N} (hq : q ∉ rScr.image)
    {f : BitAssignment N → ZMod 2} {P : DynamicCircuit Var N}
    (hP : CleanRealizes v (QRegister.whole N) rScr (diagSignUnitary f) P) :
    CleanRealizes v (QRegister.whole N) rScr
      (diagSignUnitary (fun β ↦ f (Function.update β q (β q + 1))))
      (DynamicCircuit.seq (.circuit (Circuit.X q))
        (DynamicCircuit.seq P (.circuit (Circuit.X q)))) := by
  have hX : CleanRealizes v (QRegister.whole N) rScr (Circuit.X q).eval (.circuit (Circuit.X q)) :=
    CleanRealizes_circuit_of_disjoint v rScr (Circuit.X q) rfl (by simp [hq])
  exact (hX.seq (hP.seq hX)).congr_unitary (x_conj_diagSignUnitary q f)

/-- Core Gidney temporary-AND sandwich theorem for diagonal sign unitaries:
if `mid` satisfies `CleanRealizes v (whole N) rScr₂ (diagSignUnitary f) mid`, then wrapping `mid`
in `andSandwichProg v c₁ c₂ anc` on clean wire `anc` realizes
`diagSignUnitary (fun β ↦ f (Function.update β anc (β c₁ * β c₂)))` on `rScr`
(`= {anc} ∪ rScr₂`). -/
theorem CleanRealizes_andSignSandwich {Var : Type} [Fintype Var] [DecidableEq Var]
    {N s s₂ : ℕ} {v : Var}
    {c₁ c₂ anc : Wire N} (h₁₂ : c₁ ≠ c₂) (h₁a : c₁ ≠ anc) (h₂a : c₂ ≠ anc)
    {rScr : QRegister s N} {rScr₂ : QRegister s₂ N}
    (hc₁ : c₁ ∉ rScr₂.image) (hc₂ : c₂ ∉ rScr₂.image) (hanc : anc ∉ rScr₂.image)
    (himg : rScr.image = (QRegister.singleton anc).image ∪ rScr₂.image)
    {f : BitAssignment N → ZMod 2} {mid : DynamicCircuit Var N}
    (hmid : CleanRealizes v (QRegister.whole N) rScr₂ (diagSignUnitary f) mid) :
    CleanRealizes v (QRegister.whole N) rScr
      (diagSignUnitary (fun β ↦ f (Function.update β anc (β c₁ * β c₂))))
      (andSandwichProg v c₁ c₂ anc h₁₂ h₁a h₂a mid) := by
  let U_and : DynamicCircuit Var N := DynamicCircuit.andCompute c₁ c₂ anc h₁a h₂a
  let U_un : DynamicCircuit Var N := DynamicCircuit.andUncompute v c₁ c₂ anc h₁₂
  let rAnc := QRegister.singleton anc
  let T_anc := (Circuit.TOFF c₁ c₂ anc h₁₂ h₁a h₂a).eval
  let g_full : BitAssignment N → ZMod 2 := fun β ↦ f (Function.update β anc (β anc + β c₁ * β c₂))
  let g_zero : BitAssignment N → ZMod 2 := fun β ↦ f (Function.update β anc (β c₁ * β c₂))
  have hdisj_and : Disjoint U_and.support rScr₂.image := by
    rw [DynamicCircuit.support_andCompute]
    simp [hc₁, hc₂, hanc]
  have hdisj_un : Disjoint U_un.support rScr₂.image := by
    rw [DynamicCircuit.support_andUncompute]
    simp [hc₁, hc₂, hanc]
  rcases hmid with ⟨htoff_mid, hupd_mid, hwp_mid, hclean_mid⟩
  refine ⟨by simp [htoff_mid], ?_, ?_, ?_⟩
  · intro Θ _ σ val
    have hun_upd :
        ∀ σ' val', wp U_un.compile Θ (Function.update σ' v val') = wp U_un.compile Θ σ' :=
      fun σ' val' ↦ DynamicCircuit.wp_andUncompute_update_self v c₁ c₂ anc h₁₂ Θ σ' val'
    have hmid_upd := hupd_mid (wp U_un.compile Θ) hun_upd
    change wp U_and.compile (wp mid.compile (wp U_un.compile Θ)) (Function.update σ v val) =
      wp U_and.compile (wp mid.compile (wp U_un.compile Θ)) σ
    simp only [U_and, DynamicCircuit.andCompute, DynamicCircuit.compile_circuit,
      DynamicCircuit.qc_wp_circuit_compile, qcWpQAssign, hmid_upd σ val]
  · intro Θ hΘ
    have hun_upd :
        ∀ σ' val', wp U_un.compile Θ (Function.update σ' v val') = wp U_un.compile Θ σ' :=
      fun σ' val' ↦ DynamicCircuit.wp_andUncompute_update_self v c₁ c₂ anc h₁₂ Θ σ' val'
    have hΘ_scr₂_upd : ∀ σ' val',
        restrictAssertionToZeroAncilla Θ rScr₂ (Function.update σ' v val') =
          restrictAssertionToZeroAncilla Θ rScr₂ σ' := fun σ' val' ↦ by
      apply Subtype.ext
      simp [hΘ σ' val']
    have hT_swap : diagSignUnitary f * T_anc = T_anc * diagSignUnitary g_full := by
      calc
        diagSignUnitary f * T_anc = (T_anc * T_anc) * diagSignUnitary f * T_anc := by
          rw [toffoli_eval_sq c₁ c₂ anc h₁₂ h₁a h₂a, one_mul]
        _ = T_anc * (T_anc * diagSignUnitary f * T_anc) := by simp [mul_assoc]
        _ = T_anc * diagSignUnitary g_full := by
          rw [toffoli_conj_diagSignUnitary c₁ c₂ anc h₁₂ h₁a h₂a f]
    rw [restrictAssertionToZeroAncilla_union _ rScr rAnc rScr₂ himg,
      restrictAssertionToZeroAncilla_union _ rScr rAnc rScr₂ himg]
    change restrictAssertionToZeroAncilla
      (restrictAssertionToZeroAncilla
        (wp U_and.compile (wp mid.compile (wp U_un.compile Θ))) rScr₂) rAnc =
      restrictAssertionToZeroAncilla
        (restrictAssertionToZeroAncilla
          (qcWpQAssign ((QRegister.whole N).embedUnitary (diagSignUnitary g_zero)) Θ) rScr₂) rAnc
    rw [← wp_compile_restrict_of_disjoint U_and rScr₂ hdisj_and,
      hwp_mid (wp U_un.compile Θ) hun_upd, QRegister.whole_embedUnitary,
      QRegister.whole_embedUnitary, ← wp_qAssign_diagSignUnitary_restrict f rScr₂,
      ← wp_compile_restrict_of_disjoint U_un rScr₂ hdisj_un,
      DynamicCircuit.qc_wp_andCompute c₁ c₂ anc h₁₂ h₁a h₂a,
      qc_wp_qAssign_comp, hT_swap, ← qc_wp_qAssign_comp,
      ← restrictAssertionToZeroAncilla_idem (qcWpQAssign (diagSignUnitary g_full) _) rAnc,
      ← wp_qAssign_diagSignUnitary_restrict g_full rAnc,
      DynamicCircuit.qc_wp_toffoli_andUncompute_of_update_eq
        v c₁ c₂ anc h₁₂ h₁a h₂a (restrictAssertionToZeroAncilla Θ rScr₂) hΘ_scr₂_upd,
      wp_qAssign_diagSignUnitary_restrict g_full rAnc, restrictAssertionToZeroAncilla_idem,
      ← wp_qAssign_diagSignUnitary_restrict g_zero rScr₂]
    funext σ
    apply Subtype.ext
    have hdiag_eq : (diagSignUnitary g_full).1 * rAnc.basisOutcomeProjector 0 =
        (diagSignUnitary g_zero).1 * rAnc.basisOutcomeProjector 0 := by
      rw [diagSignUnitary_val, diagSignUnitary_val, diagSignMatrix, diagSignMatrix,
        QRegister.basisOutcomeProjector_eq_diagonal, Matrix.diagonal_mul_diagonal,
        Matrix.diagonal_mul_diagonal]
      congr 1; funext idx
      by_cases h0 : rAnc.extractIndex idx = 0
      · have hanc0 : basisBits N idx anc = 0 :=
          (extractIndex_eq_zero_iff rAnc idx).mp h0 anc (by simp [rAnc])
        simp [h0, g_full, g_zero, hanc0]
      · simp [h0]
    have hadj : rAnc.basisOutcomeProjector 0 * (diagSignUnitary g_full).1ᴴ =
        rAnc.basisOutcomeProjector 0 * (diagSignUnitary g_zero).1ᴴ := by
      have h := congrArg Matrix.conjTranspose hdiag_eq
      simpa only [Matrix.conjTranspose_mul, QRegister.basisOutcomeProjector_conjTranspose] using h
    simp only [restrictAssertionToZeroAncilla_coe, qcWpQAssign, qcQAssignObsMap,
      Observable.conj_coe, Unitary.coe_star, Matrix.star_eq_conjTranspose, HermitianMat.conj_conj]
    rw [← Matrix.mul_assoc, hadj, Matrix.mul_assoc]
  · intro Θ
    rw [restrictAssertionToZeroAncilla_union _ rScr rAnc rScr₂ himg,
      restrictAssertionToZeroAncilla_union (wp _ Θ) rScr rAnc rScr₂ himg]
    change restrictAssertionToZeroAncilla
      (restrictAssertionToZeroAncilla
        (wp U_and.compile (wp mid.compile
          (wp U_un.compile (restrictAssertionToZeroAncilla Θ rScr))))
        rScr₂) rAnc =
      restrictAssertionToZeroAncilla
        (restrictAssertionToZeroAncilla
          (wp U_and.compile (wp mid.compile (wp U_un.compile Θ))) rScr₂) rAnc
    rw [restrictAssertionToZeroAncilla_union Θ rScr rAnc rScr₂ himg,
      DynamicCircuit.wp_andUncompute_clean_post v c₁ c₂ anc h₁₂ h₁a h₂a,
      wp_compile_restrict_of_disjoint U_un rScr₂ hdisj_un Θ,
      ← wp_compile_restrict_of_disjoint U_and rScr₂ hdisj_and,
      hclean_mid (wp U_un.compile Θ),
      wp_compile_restrict_of_disjoint U_and rScr₂ hdisj_and]

/-!
### `withXMask` & `withAllOnesIndicator` Ladder Combinators
-/

/-- Shift bits of `β` on `r i` by `mask i`, leaving wires outside `r` unchanged. -/
noncomputable def maskShiftBits {N k : ℕ} (r : QRegister k N) (mask : Fin k → ZMod 2)
    (β : BitAssignment N) : BitAssignment N :=
  writeRegBits β r (fun i ↦ β (r i) + mask i)

@[simp]
theorem block_wires_apply {n off len : ℕ} (h : off + len ≤ n) (j : Fin len) :
    (QRegister.block off len h).wires j = ⟨off + j.val, by omega⟩ := rfl

@[simp]
theorem slice_wires_apply {N k off len : ℕ} (r : QRegister k N) (h : off + len ≤ k)
    (j : Fin len) :
    (r.slice off len h).wires j = r.wires ⟨off + j.val, by omega⟩ := rfl

@[simp]
theorem maskShiftBits_apply_reg {N k : ℕ} (r : QRegister k N) (mask : Fin k → ZMod 2)
    (β : BitAssignment N) (i : Fin k) :
    maskShiftBits r mask β (r i) = β (r i) + mask i := by
  dsimp only [maskShiftBits, writeRegBits]
  rw [QRegister.basisBits_replaceIndex_apply]
  exact congrFun ((basisBits k).apply_symm_apply (fun j ↦ β (r j) + mask j)) i

theorem maskShiftBits_of_not_mem {N k : ℕ} (r : QRegister k N) (mask : Fin k → ZMod 2)
    (β : BitAssignment N) {q : Wire N} (hq : q ∉ r.image) :
    maskShiftBits r mask β q = β q := by
  have hnr : q ∉ Set.range r.wires := fun ⟨i, hi⟩ ↦
    hq ((QRegister.mem_image r q).mpr ⟨i, hi⟩)
  dsimp only [maskShiftBits, writeRegBits]
  rw [QRegister.basisBits_replaceIndex_of_not_mem _ _ _ _ hnr]
  exact congrFun ((basisBits N).apply_symm_apply β) q

@[simp]
theorem maskShiftBits_zero_len {N : ℕ} (r : QRegister 0 N) (mask : Fin 0 → ZMod 2)
    (β : BitAssignment N) :
    maskShiftBits r mask β = β := by
  funext q
  exact maskShiftBits_of_not_mem r mask β (by simp [QRegister.mem_image])

theorem slice_image_subset {N k : ℕ} (r : QRegister k N) (off len : ℕ) (h : off + len ≤ k) :
    (r.slice off len h).image ⊆ r.image := by
  intro q hq
  obtain ⟨j, rfl⟩ := (QRegister.mem_image _ q).mp hq
  exact (QRegister.mem_image r _).mpr ⟨⟨off + j.val, by omega⟩, by simp⟩

theorem maskShiftBits_succ_eq {N k : ℕ} (r : QRegister (k + 1) N) (mask : Fin (k + 1) → ZMod 2)
    (β : BitAssignment N) :
    maskShiftBits (r.slice 1 k (by omega)) (fun j ↦ mask j.succ)
      (if mask 0 = 1 then Function.update β (r 0) (β (r 0) + 1) else β) =
      maskShiftBits r mask β := by
  let r' := r.slice 1 k (by omega)
  let β₀ := if mask 0 = 1 then Function.update β (r 0) (β (r 0) + 1) else β
  have hβ₀_head : β₀ (r 0) = β (r 0) + mask 0 := by
    rcases zmod2_eq_zero_or_one (mask 0) with h0 | h1
    · simp [β₀, h0]
    · simp [β₀, h1]
  have hβ₀_ne {q : Wire N} (hq : q ≠ r 0) : β₀ q = β q := by
    by_cases h1 : mask 0 = 1 <;> simp [β₀, h1, Function.update_of_ne hq]
  funext q
  by_cases hmem : q ∈ r.image
  · obtain ⟨i, rfl⟩ := (QRegister.mem_image r q).mp hmem
    cases i using Fin.cases with
    | zero =>
        have hnot : r 0 ∉ r'.image := by
          intro hm
          obtain ⟨j, hj⟩ := (QRegister.mem_image r' (r 0)).mp hm
          dsimp only [r'] at hj
          rw [slice_wires_apply] at hj
          have heq : (⟨1 + j.val, by omega⟩ : Fin (k + 1)) = 0 := r.wires.injective hj
          have hval := congrArg Fin.val heq
          dsimp at hval
          omega
        rw [maskShiftBits_of_not_mem r' _ β₀ hnot, hβ₀_head, maskShiftBits_apply_reg]
    | succ j =>
        have hr'j : r' j = r j.succ := by
          change (r.slice 1 k _).wires j = r.wires j.succ
          rw [slice_wires_apply]
          congr 1; ext; dsimp; omega
        have hne : r j.succ ≠ r 0 := fun h ↦ Fin.succ_ne_zero j (r.wires.injective h)
        rw [← hr'j, maskShiftBits_apply_reg, hr'j]
        change β₀ (r j.succ) + mask j.succ = maskShiftBits r mask β (r j.succ)
        rw [hβ₀_ne hne, maskShiftBits_apply_reg]
  · have hnot' : q ∉ r'.image := fun hm ↦ hmem (slice_image_subset r 1 k _ hm)
    have hne : q ≠ r 0 := fun h ↦ hmem (h ▸ (QRegister.mem_image r (r 0)).mpr ⟨0, rfl⟩)
    rw [maskShiftBits_of_not_mem r' _ β₀ hnot', hβ₀_ne hne, maskShiftBits_of_not_mem r mask β hmem]

/-- Wrap `P` with `X (r i)` before and after on every wire `i : Fin k` where `mask i = 1`. -/
def withXMask {Var : Type} {N : ℕ} :
    {k : ℕ} → QRegister k N → (Fin k → ZMod 2) → DynamicCircuit Var N → DynamicCircuit Var N
  | 0, _, _, P => P
  | k + 1, r, mask, P =>
      let inner := withXMask (r.slice 1 k (by omega)) (fun j ↦ mask j.succ) P
      if mask 0 = 1 then
        .seq (.circuit (Circuit.X (r 0))) (.seq inner (.circuit (Circuit.X (r 0))))
      else
        inner

@[simp]
theorem withXMask_count_t {Var : Type} {N k : ℕ}
    (r : QRegister k N) (mask : Fin k → ZMod 2) (P : DynamicCircuit Var N) :
    (withXMask r mask P).count PrimitiveGate.T = P.count PrimitiveGate.T := by
  induction k with
  | zero => rfl
  | succ k ih =>
      dsimp only [withXMask]
      split_ifs <;> simp [ih]

@[simp]
theorem withXMask_count_toff {Var : Type} {N k : ℕ}
    (r : QRegister k N) (mask : Fin k → ZMod 2) (P : DynamicCircuit Var N) :
    (withXMask r mask P).count PrimitiveGate.TOFF = P.count PrimitiveGate.TOFF := by
  induction k with
  | zero => rfl
  | succ k ih =>
      dsimp only [withXMask]
      split_ifs <;> simp [ih]

theorem CleanRealizes_withXMask {Var : Type} [Fintype Var] [DecidableEq Var] {N k s : ℕ}
    {v : Var} {r : QRegister k N} {rScr : QRegister s N}
    (hdisj : Disjoint r.image rScr.image) (mask : Fin k → ZMod 2)
    {f : BitAssignment N → ZMod 2} {P : DynamicCircuit Var N}
    (hP : CleanRealizes v (QRegister.whole N) rScr (diagSignUnitary f) P) :
    CleanRealizes v (QRegister.whole N) rScr
      (diagSignUnitary (fun β ↦ f (maskShiftBits r mask β)))
      (withXMask r mask P) := by
  induction k generalizing f with
  | zero =>
      dsimp only [withXMask]
      exact hP.congr_unitary (by simp [maskShiftBits_zero_len])
  | succ k ih =>
      have hdisj' : Disjoint (r.slice 1 k (by omega)).image rScr.image :=
        Disjoint.mono_left (slice_image_subset r 1 k _) hdisj
      have hinner := ih hdisj' (fun j ↦ mask j.succ) hP
      dsimp only [withXMask]
      by_cases hm0 : mask 0 = 1
      · rw [ite_eq_left hm0]
        have hr0 : r 0 ∉ rScr.image :=
          Finset.disjoint_left.mp hdisj ((QRegister.mem_image r (r 0)).mpr ⟨0, rfl⟩)
        refine (CleanRealizes_xSandwich hr0 hinner).congr_unitary ?_
        congr 1; funext β
        have hstep := maskShiftBits_succ_eq r mask β
        rw [ite_eq_left hm0] at hstep
        rw [hstep]
      · rw [ite_eq_right hm0]
        refine hinner.congr_unitary ?_
        congr 1; funext β
        have hstep := maskShiftBits_succ_eq r mask β
        rw [ite_eq_right hm0] at hstep
        rw [hstep]

/-!
### Slice Image Algebra & `withAllOnesIndicator`
-/

theorem slice_zero_self_image {N s : ℕ} (r : QRegister s N) (hs : 0 + s ≤ s := by omega) :
    (r.slice 0 s hs).image = r.image := by
  ext q
  simp only [QRegister.mem_image]
  constructor
  · rintro ⟨j, rfl⟩
    exact ⟨⟨j.val, j.isLt⟩, by simp⟩
  · rintro ⟨i, rfl⟩
    exact ⟨i, by simp⟩

theorem slice_sub_image_subset {N s : ℕ} (r : QRegister s N)
    {off₁ len₁ off₂ len₂ : ℕ} (h₁ : off₁ + len₁ ≤ s) (h₂ : off₂ + len₂ ≤ s)
    (hoff : off₂ ≤ off₁) (hlen : off₁ + len₁ ≤ off₂ + len₂) :
    (r.slice off₁ len₁ h₁).image ⊆ (r.slice off₂ len₂ h₂).image := by
  intro q hq
  obtain ⟨j, rfl⟩ := (QRegister.mem_image _ q).mp hq
  rw [QRegister.mem_image]
  refine ⟨⟨(off₁ - off₂) + j.val, by omega⟩, ?_⟩
  simp only [slice_wires_apply]
  congr 1; ext; dsimp; omega

theorem slice_image_eq {N s : ℕ} (r : QRegister s N)
    {off₁ len₁ off₂ len₂ : ℕ} (h₁ : off₁ + len₁ ≤ s) (h₂ : off₂ + len₂ ≤ s)
    (hoff : off₁ = off₂) (hlen : len₁ = len₂) :
    (r.slice off₁ len₁ h₁).image = (r.slice off₂ len₂ h₂).image :=
  Finset.Subset.antisymm
    (slice_sub_image_subset r h₁ h₂ (by omega) (by omega))
    (slice_sub_image_subset r h₂ h₁ (by omega) (by omega))

theorem slice_step_image {N s : ℕ} (r : QRegister s N) {off len : ℕ}
    (h : off + (len + 1) ≤ s) :
    (r.slice off (len + 1) h).image =
      (QRegister.singleton (r ⟨off, by omega⟩)).image ∪
        (r.slice (off + 1) len (by omega)).image := by
  ext q
  simp only [QRegister.mem_image, Finset.mem_union]
  constructor
  · rintro ⟨j, rfl⟩
    cases j using Fin.cases with
    | zero =>
        left
        exact ⟨0, by simp⟩
    | succ k =>
        right
        refine ⟨k, ?_⟩
        simp only [slice_wires_apply]
        congr 1; ext; dsimp; omega
  · rintro (⟨i, rfl⟩ | ⟨k, rfl⟩)
    · refine ⟨0, ?_⟩
      fin_cases i
      simp
    · refine ⟨k.succ, ?_⟩
      simp only [slice_wires_apply]
      congr 1; ext; dsimp; omega

theorem apply_not_mem_slice_of_lt {N s : ℕ} (r : QRegister s N)
    {i : Fin s} {off len : ℕ} (h : off + len ≤ s) (hlt : i.val < off) :
    r i ∉ (r.slice off len h).image := by
  intro hm
  obtain ⟨j, hj⟩ := (QRegister.mem_image _ (r i)).mp hm
  rw [QRegister.slice_apply] at hj
  have heq := congrArg Fin.val (r.wires.injective hj)
  dsimp at heq
  omega

theorem disjoint_slice_of_le {N s : ℕ} (r : QRegister s N)
    {off₁ len₁ off₂ len₂ : ℕ} (h₁ : off₁ + len₁ ≤ s) (h₂ : off₂ + len₂ ≤ s)
    (hle : off₁ + len₁ ≤ off₂) :
    Disjoint (r.slice off₁ len₁ h₁).image (r.slice off₂ len₂ h₂).image := by
  rw [Finset.disjoint_left]
  intro q hq₁ hq₂
  obtain ⟨j₁, rfl⟩ := (QRegister.mem_image _ q).mp hq₁
  obtain ⟨j₂, hj₂⟩ := (QRegister.mem_image _ _).mp hq₂
  rw [QRegister.slice_apply, QRegister.slice_apply] at hj₂
  have heq := congrArg Fin.val (r.wires.injective hj₂)
  dsimp at heq
  omega

/-- Gidney measurement-uncomputed temporary-AND ladder reducing `w + 1` wires of `r` to a single
all-ones indicator wire `w_ind ∈ r.image ∪ (rScr.slice off w hoff).image`, using `4 * w` `T` gates
and `0` `TOFF` gates on `rScr.slice off w hoff`. -/
def withAllOnesIndicator {Var : Type} {N s : ℕ} (v : Var) :
    (w : ℕ) → (r : QRegister (w + 1) N) → (rScr : QRegister s N) →
    (off : ℕ) → (hoff : off + w ≤ s) →
    (hdisj : Disjoint r.image (rScr.slice off w hoff).image) →
    (body : (w_ind : Wire N) →
      w_ind ∈ r.image ∪ (rScr.slice off w hoff).image → DynamicCircuit Var N) →
    DynamicCircuit Var N
  | 0, r, _, _, _, _, body =>
      body (r 0) (Finset.mem_union_left _ ((QRegister.mem_image r (r 0)).mpr ⟨0, rfl⟩))
  | w' + 1, r, rScr, off, hoff, hdisj, body =>
      let c₁ := r 0
      let c₂ := r 1
      let anc := rScr ⟨off, by omega⟩
      have h₁₂ : c₁ ≠ c₂ := fun h ↦ by cases r.wires.injective h
      have hanc_mem : anc ∈ (rScr.slice off (w' + 1) hoff).image := by
        rw [QRegister.mem_image]
        exact ⟨⟨0, by omega⟩, by simp [anc]⟩
      have h₁a : c₁ ≠ anc := fun h ↦
        Finset.disjoint_left.mp hdisj ((QRegister.mem_image r c₁).mpr ⟨0, rfl⟩) (h ▸ hanc_mem)
      have h₂a : c₂ ≠ anc := fun h ↦
        Finset.disjoint_left.mp hdisj ((QRegister.mem_image r c₂).mpr ⟨1, rfl⟩) (h ▸ hanc_mem)
      have hTailAnc : (r.slice 2 w' (by omega)).DisjointWires (QRegister.singleton anc) := by
        rw [QRegister.disjoint_iff]
        intro i j hij
        have hi_mem : (r.slice 2 w' (by omega)) i ∈ r.image :=
          slice_image_subset r 2 w' _ ((QRegister.mem_image _ _).mpr ⟨i, rfl⟩)
        have hj_eq : (QRegister.singleton anc) j = anc := rfl
        rw [hj_eq] at hij
        exact Finset.disjoint_left.mp hdisj hi_mem (hij ▸ hanc_mem)
      let rNext : QRegister (w' + 1) N :=
        (r.slice 2 w' (by omega)).concat (QRegister.singleton anc) hTailAnc
      have hdisj_next :
          Disjoint rNext.image (rScr.slice (off + 1) w' (by omega)).image := by
        dsimp only [rNext]
        rw [QRegister.image_concat, Finset.disjoint_union_left]
        refine ⟨?_, ?_⟩
        · exact Disjoint.mono
            (slice_image_subset r 2 w' _)
            (slice_sub_image_subset rScr _ hoff (by omega) (by omega))
            hdisj
        · rw [Finset.disjoint_left]
          intro q hq hm
          obtain ⟨i, rfl⟩ := (QRegister.mem_image _ q).mp hq
          fin_cases i
          exact apply_not_mem_slice_of_lt rScr _ (by dsimp; omega) hm
      have hsub_ind :
          rNext.image ∪ (rScr.slice (off + 1) w' (by omega)).image ⊆
            r.image ∪ (rScr.slice off (w' + 1) hoff).image := by
        intro q hq
        dsimp only [rNext] at hq
        rw [QRegister.image_concat, Finset.mem_union, Finset.mem_union] at hq
        rcases hq with ((hq_tail | hq_anc) | hq_scr)
        · exact Finset.mem_union_left _ (slice_image_subset r 2 w' _ hq_tail)
        · obtain ⟨i, rfl⟩ := (QRegister.mem_image _ q).mp hq_anc
          fin_cases i
          exact Finset.mem_union_right _ hanc_mem
        · exact Finset.mem_union_right _
            (slice_sub_image_subset rScr _ hoff (by omega) (by omega) hq_scr)
      andSandwichProg v c₁ c₂ anc h₁₂ h₁a h₂a
        (withAllOnesIndicator v w' rNext rScr (off + 1) (by omega) hdisj_next
          fun w_ind hw_next ↦ body w_ind (hsub_ind hw_next))

theorem withAllOnesIndicator_count_toff {Var : Type} {N s : ℕ} (v : Var)
    (w : ℕ) (r : QRegister (w + 1) N) (rScr : QRegister s N)
    (off : ℕ) (hoff : off + w ≤ s)
    (hdisj : Disjoint r.image (rScr.slice off w hoff).image)
    (body : (w_ind : Wire N) →
      w_ind ∈ r.image ∪ (rScr.slice off w hoff).image → DynamicCircuit Var N)
    (hbody : ∀ w_ind hw, (body w_ind hw).count PrimitiveGate.TOFF = 0) :
    (withAllOnesIndicator v w r rScr off hoff hdisj body).count PrimitiveGate.TOFF = 0 := by
  induction w generalizing off with
  | zero => exact hbody _ _
  | succ w' ih =>
      dsimp only [withAllOnesIndicator]
      rw [count_andSandwichProg_toff]
      exact ih _ _ _ _ _ fun w_ind hw ↦ hbody w_ind _

theorem withAllOnesIndicator_count_t {Var : Type} {N s : ℕ} (v : Var)
    (w : ℕ) (r : QRegister (w + 1) N) (rScr : QRegister s N)
    (off : ℕ) (hoff : off + w ≤ s)
    (hdisj : Disjoint r.image (rScr.slice off w hoff).image)
    (body : (w_ind : Wire N) →
      w_ind ∈ r.image ∪ (rScr.slice off w hoff).image → DynamicCircuit Var N)
    (c_body : ℕ)
    (hbody : ∀ w_ind hw, (body w_ind hw).count PrimitiveGate.T = c_body) :
    (withAllOnesIndicator v w r rScr off hoff hdisj body).count PrimitiveGate.T =
      4 * w + c_body := by
  induction w generalizing off with
  | zero =>
      dsimp only [withAllOnesIndicator]
      simpa using hbody _ _
  | succ w' ih =>
      dsimp only [withAllOnesIndicator]
      rw [count_andSandwichProg_t, ih _ _ _ _ _ (fun w_ind hw ↦ hbody w_ind _)]
      omega

theorem withAllOnesIndicator_cleanRealizes {Var : Type} [Fintype Var] [DecidableEq Var]
    {N s : ℕ} (v : Var)
    (w : ℕ) (r : QRegister (w + 1) N) (rScr : QRegister s N)
    (off : ℕ) (hoff : off + w ≤ s)
    (hdisj : Disjoint r.image (rScr.slice off w hoff).image)
    (hdisj_rem : Disjoint r.image (rScr.slice off (s - off) (by omega)).image)
    (F : ZMod 2 → BitAssignment N → ZMod 2)
    (hF_indep : ∀ b β q, q ∈ (rScr.slice off w hoff).image →
      ∀ val, F b (Function.update β q val) = F b β)
    (body : (w_ind : Wire N) →
      w_ind ∈ r.image ∪ (rScr.slice off w hoff).image → DynamicCircuit Var N)
    (hbody : ∀ w_ind hw,
      CleanRealizes v (QRegister.whole N)
        (rScr.slice (off + w) (s - (off + w)) (by omega))
        (diagSignUnitary (fun β ↦ F (β w_ind) β))
        (body w_ind hw)) :
    CleanRealizes v (QRegister.whole N)
      (rScr.slice off (s - off) (by omega))
      (diagSignUnitary (fun β ↦ F (∏ i : Fin (w + 1), β (r i)) β))
      (withAllOnesIndicator v w r rScr off hoff hdisj body) := by
  induction w generalizing off with
  | zero =>
      dsimp only [withAllOnesIndicator]
      have hb := hbody (r 0)
        (Finset.mem_union_left _ ((QRegister.mem_image r (r 0)).mpr ⟨0, rfl⟩))
      have himg : (rScr.slice (off + 0) (s - (off + 0)) (by omega)).image =
          (rScr.slice off (s - off) (by omega)).image :=
        slice_image_eq rScr _ _ (by omega) (by omega)
      refine (hb.congr_scr himg).congr_unitary ?_
      congr 1; funext β
      rw [Fin.prod_univ_one]
  | succ w' ih =>
      dsimp only [withAllOnesIndicator]
      let c₁ := r 0
      let c₂ := r 1
      let anc := rScr ⟨off, by omega⟩
      have h₁₂ : c₁ ≠ c₂ := fun h ↦ by cases r.wires.injective h
      have hanc_mem : anc ∈ (rScr.slice off (w' + 1) hoff).image := by
        rw [QRegister.mem_image]
        exact ⟨⟨0, by omega⟩, by simp [anc]⟩
      have h₁a : c₁ ≠ anc := fun h ↦
        Finset.disjoint_left.mp hdisj ((QRegister.mem_image r c₁).mpr ⟨0, rfl⟩) (h ▸ hanc_mem)
      have h₂a : c₂ ≠ anc := fun h ↦
        Finset.disjoint_left.mp hdisj ((QRegister.mem_image r c₂).mpr ⟨1, rfl⟩) (h ▸ hanc_mem)
      have hTailAnc : (r.slice 2 w' (by omega)).DisjointWires (QRegister.singleton anc) := by
        rw [QRegister.disjoint_iff]
        intro i j hij
        have hi_mem : (r.slice 2 w' (by omega)) i ∈ r.image :=
          slice_image_subset r 2 w' _ ((QRegister.mem_image _ _).mpr ⟨i, rfl⟩)
        have hj_eq : (QRegister.singleton anc) j = anc := rfl
        rw [hj_eq] at hij
        exact Finset.disjoint_left.mp hdisj hi_mem (hij ▸ hanc_mem)
      let rNext : QRegister (w' + 1) N :=
        (r.slice 2 w' (by omega)).concat (QRegister.singleton anc) hTailAnc
      have hdisj_rem_next :
          Disjoint rNext.image (rScr.slice (off + 1) (s - (off + 1)) (by omega)).image := by
        dsimp only [rNext]
        rw [QRegister.image_concat, Finset.disjoint_union_left]
        refine ⟨?_, ?_⟩
        · exact Disjoint.mono
            (slice_image_subset r 2 w' _)
            (slice_sub_image_subset rScr _ _ (by omega) (by omega))
            hdisj_rem
        · rw [Finset.disjoint_left]
          intro q hq hm
          obtain ⟨i, rfl⟩ := (QRegister.mem_image _ q).mp hq
          fin_cases i
          exact apply_not_mem_slice_of_lt rScr _ (by dsimp; omega) hm
      have hF_next : ∀ b β q, q ∈ (rScr.slice (off + 1) w' (by omega)).image →
          ∀ val, F b (Function.update β q val) = F b β := fun b β q hq val ↦
        hF_indep b β q (slice_sub_image_subset rScr _ hoff (by omega) (by omega) hq) val
      have himg_end :
          (rScr.slice (off + (w' + 1)) (s - (off + (w' + 1))) (by omega)).image =
            (rScr.slice (off + 1 + w') (s - (off + 1 + w')) (by omega)).image :=
        slice_image_eq rScr _ _ (by omega) (by omega)
      have hsub_rem :
          (rScr.slice (off + 1) (s - (off + 1)) (by omega)).image ⊆
            (rScr.slice off (s - off) (by omega)).image :=
        slice_sub_image_subset rScr _ _ (by omega) (by omega)
      have hc₁_not : c₁ ∉ (rScr.slice (off + 1) (s - (off + 1)) (by omega)).image := fun hm ↦
        Finset.disjoint_left.mp hdisj_rem ((QRegister.mem_image r c₁).mpr ⟨0, rfl⟩) (hsub_rem hm)
      have hc₂_not : c₂ ∉ (rScr.slice (off + 1) (s - (off + 1)) (by omega)).image := fun hm ↦
        Finset.disjoint_left.mp hdisj_rem ((QRegister.mem_image r c₂).mpr ⟨1, rfl⟩) (hsub_rem hm)
      have hanc_not : anc ∉ (rScr.slice (off + 1) (s - (off + 1)) (by omega)).image :=
        apply_not_mem_slice_of_lt rScr _ (by dsimp; omega)
      have himg_step :
          (rScr.slice off (s - off) (by omega)).image =
            (QRegister.singleton anc).image ∪
              (rScr.slice (off + 1) (s - (off + 1)) (by omega)).image := by
        rw [slice_image_eq rScr _ (by omega : off + ((s - (off + 1)) + 1) ≤ s) rfl (by omega),
          slice_step_image]
      refine CleanRealizes.congr_unitary
        (CleanRealizes_andSignSandwich h₁₂ h₁a h₂a hc₁_not hc₂_not hanc_not himg_step
          (ih rNext (off + 1) (by omega) _ hdisj_rem_next hF_next _
            fun w_ind hw_next ↦ (hbody w_ind _).congr_scr himg_end)) ?_
      congr 1; funext β
      let β' := Function.update β anc (β c₁ * β c₂)
      have hprod : (∏ j : Fin (w' + 1), β' (rNext j)) = ∏ i : Fin (w' + 2), β (r i) := by
        rw [Fin.prod_univ_castSucc, Fin.prod_univ_succ, Fin.prod_univ_succ, ← mul_assoc]
        have hlast : β' (rNext (Fin.last w')) = β c₁ * β c₂ := by
          have hrl : rNext (Fin.last w') = anc := by
            have hl : Fin.last w' = Fin.natAdd w' (0 : Fin 1) := by ext; simp
            dsimp only [rNext]
            rw [hl]
            exact QRegister.concat_apply_right _ (QRegister.singleton anc) hTailAnc 0
          simp [β', hrl]
        have htail : (∏ j : Fin w', β' (rNext (Fin.castSucc j))) =
            ∏ j : Fin w', β (r j.succ.succ) := by
          refine Finset.prod_congr rfl fun j _ ↦ ?_
          have hrj : rNext (Fin.castSucc j) = r j.succ.succ := by
            have hcs : Fin.castSucc j = Fin.castAdd 1 j := rfl
            dsimp only [rNext]
            rw [hcs, QRegister.concat_apply_left]
            change (r.slice 2 w' _).wires j = r.wires j.succ.succ
            rw [slice_wires_apply]
            congr 1; ext; dsimp; omega
          have hne : r j.succ.succ ≠ anc := fun h ↦
            Finset.disjoint_left.mp hdisj
              ((QRegister.mem_image r _).mpr ⟨j.succ.succ, rfl⟩) (h ▸ hanc_mem)
          rw [hrj]
          exact Function.update_of_ne hne _ _
        rw [hlast, htail, mul_comm]
        have hc₂_eq : (Fin.succ 0 : Fin (w' + 2)) = 1 := by ext; simp
        dsimp only [c₁, c₂]
        rw [hc₂_eq]
      rw [hprod]
      exact hF_indep _ β anc hanc_mem (β c₁ * β c₂)

/-!
### Concrete `DynamicCircuit` Reflections (`reflMidDyn`, `reflInDyn`, QPE-Conditioned)
-/

theorem fin_prod_of_eq_one {M : Type*} [CommMonoid M] {k : ℕ}
    (hk : k = 1) (f : Fin k → M) :
    (∏ i : Fin k, f i) = f ⟨0, by omega⟩ := by
  subst hk
  exact Fin.prod_univ_one f

theorem fin_prod_head_mul_slice {M : Type*} [CommMonoid M] {k m : ℕ}
    (hk : k = m + 1) (f : Fin k → M) :
    f ⟨0, by omega⟩ * (∏ j : Fin m, f ⟨1 + j.val, by omega⟩) = ∏ i : Fin k, f i := by
  subst hk
  rw [Fin.prod_univ_succ]
  congr 1
  refine Finset.prod_congr rfl fun j _ ↦ ?_
  congr 1
  ext
  simp [Nat.add_comm]

theorem fin_prod_slice_zero_eq {M : Type*} [CommMonoid M] {N k m : ℕ}
    (r : QRegister k N) (hm : m = k) (hm_le : 0 + m ≤ k) (g : Wire N → M) :
    (∏ j : Fin m, g ((r.slice 0 m hm_le) j)) = ∏ i : Fin k, g (r i) := by
  subst hm
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  congr 1
  simp

theorem disjoint_image_of_disjointWires {N k₁ k₂ : ℕ}
    {r₁ : QRegister k₁ N} {r₂ : QRegister k₂ N} (h : r₁.DisjointWires r₂) :
    Disjoint r₁.image r₂.image := by
  rw [Finset.disjoint_left]
  intro q hq₁ hq₂
  obtain ⟨i, rfl⟩ := (QRegister.mem_image r₁ q).mp hq₁
  obtain ⟨j, hj⟩ := (QRegister.mem_image r₂ (r₁ i)).mp hq₂
  exact h.ne i j hj.symm

/-- All-ones phase-flip core (`(-1)^{∏ i, β (r i)}`) using `4 * (w_mid - 2)` `T` gates via a
`CZ` leaf (`0` `T` gates for `w_mid ≤ 2`). -/
def allOnesPhaseDyn {Var : Type} {N w_mid s : ℕ}
    (v : Var) (rMid : QRegister w_mid N) (rScr : QRegister s N)
    (hmid_pos : 1 ≤ w_mid) (hs_mid : w_mid - 2 ≤ s)
    (hMidScr : rMid.DisjointWires rScr) : DynamicCircuit Var N :=
  if hw1 : w_mid = 1 then
    .circuit (Circuit.Z (rMid ⟨0, hmid_pos⟩))
  else
    let q₀ : Wire N := rMid ⟨0, hmid_pos⟩
    let rTail : QRegister ((w_mid - 2) + 1) N :=
      rMid.slice 1 ((w_mid - 2) + 1) (by omega)
    have hdisj_tail : Disjoint rTail.image (rScr.slice 0 (w_mid - 2) (by omega)).image :=
      Disjoint.mono
        (slice_image_subset rMid 1 _ _)
        (slice_image_subset rScr 0 _ _)
        (disjoint_image_of_disjointWires hMidScr)
    withAllOnesIndicator v (w_mid - 2) rTail rScr 0 (by omega) hdisj_tail
      fun w_ind hw ↦
        have hne : q₀ ≠ w_ind := by
          intro heq
          rw [← heq] at hw
          rcases Finset.mem_union.mp hw with hm_tail | hm_scr
          · exact apply_not_mem_slice_of_lt rMid _ (by dsimp; omega) hm_tail
          · exact Finset.disjoint_left.mp (disjoint_image_of_disjointWires hMidScr)
              ((QRegister.mem_image rMid q₀).mpr ⟨⟨0, hmid_pos⟩, rfl⟩)
              (slice_image_subset rScr 0 _ _ hm_scr)
        .circuit (czCircuit q₀ w_ind hne)

/-- Mid-subspace reflection `reflMidDyn`
($R_{\mathrm{mid}} = I - 2|0_{\mathrm{mid}}\rangle\langle 0_{\mathrm{mid}}|$)
using `4 * (w_mid - 2)` `T` gates and `0` `TOFF` gates. -/
def reflMidDyn {Var : Type} {N w_mid s : ℕ}
    (v : Var) (rMid : QRegister w_mid N) (rScr : QRegister s N)
    (hmid_pos : 1 ≤ w_mid) (hs_mid : w_mid - 2 ≤ s)
    (hMidScr : rMid.DisjointWires rScr) : DynamicCircuit Var N :=
  withXMask rMid (fun _ ↦ 1) (allOnesPhaseDyn v rMid rScr hmid_pos hs_mid hMidScr)

@[simp]
theorem reflMidDyn_count_toff {Var : Type} {N w_mid s : ℕ}
    (v : Var) (rMid : QRegister w_mid N) (rScr : QRegister s N)
    (hmid_pos : 1 ≤ w_mid) (hs_mid : w_mid - 2 ≤ s)
    (hMidScr : rMid.DisjointWires rScr) :
    (reflMidDyn v rMid rScr hmid_pos hs_mid hMidScr).count PrimitiveGate.TOFF = 0 := by
  rw [reflMidDyn, withXMask_count_toff, allOnesPhaseDyn]
  split_ifs with hw1
  · rfl
  · exact withAllOnesIndicator_count_toff _ _ _ _ _ _ _ _ fun _ _ ↦ czCircuit_count_toff _ _ _

@[simp]
theorem reflMidDyn_count_t {Var : Type} {N w_mid s : ℕ}
    (v : Var) (rMid : QRegister w_mid N) (rScr : QRegister s N)
    (hmid_pos : 1 ≤ w_mid) (hs_mid : w_mid - 2 ≤ s)
    (hMidScr : rMid.DisjointWires rScr) :
    (reflMidDyn v rMid rScr hmid_pos hs_mid hMidScr).count PrimitiveGate.T =
      4 * (w_mid - 2) := by
  rw [reflMidDyn, withXMask_count_t, allOnesPhaseDyn]
  split_ifs with hw1
  · subst hw1; simp
  · rw [withAllOnesIndicator_count_t _ _ _ _ _ _ _ _ 0 ?_]
    · simp
    · intro _ _; exact czCircuit_count_t _ _ _

theorem reflMidDyn_cleanRealizes_whole {Var : Type} [Fintype Var] [DecidableEq Var]
    {N w_mid s : ℕ}
    (v : Var) (rMid : QRegister w_mid N) (rScr : QRegister s N)
    (hmid_pos : 1 ≤ w_mid) (hs_mid : w_mid - 2 ≤ s)
    (hMidScr : rMid.DisjointWires rScr) :
    CleanRealizes v (QRegister.whole N) rScr
      (diagSignUnitary (fun β ↦ ∏ i : Fin w_mid, (β (rMid i) + 1)))
      (reflMidDyn v rMid rScr hmid_pos hs_mid hMidScr) := by
  have hdisj_ms := disjoint_image_of_disjointWires hMidScr
  have hallOnes : CleanRealizes v (QRegister.whole N) rScr
      (diagSignUnitary (fun β ↦ ∏ i : Fin w_mid, β (rMid i)))
      (allOnesPhaseDyn v rMid rScr hmid_pos hs_mid hMidScr) := by
    dsimp only [allOnesPhaseDyn]
    split_ifs with hw1
    · have hz : CleanRealizes v (QRegister.whole N) rScr
          (Circuit.Z (rMid ⟨0, hmid_pos⟩)).eval (.circuit (Circuit.Z (rMid ⟨0, hmid_pos⟩))) :=
        CleanRealizes_circuit_of_disjoint v rScr _ rfl (by
          rw [Circuit.support_single, Finset.disjoint_singleton_left]
          exact Finset.disjoint_left.mp hdisj_ms
            ((QRegister.mem_image rMid _).mpr ⟨⟨0, hmid_pos⟩, rfl⟩))
      refine hz.congr_unitary ?_
      rw [z_eval_eq_diagSignUnitary]
      congr 1; funext β
      exact (fin_prod_of_eq_one hw1 (fun i ↦ β (rMid i))).symm
    · let q₀ : Wire N := rMid ⟨0, hmid_pos⟩
      let rTail : QRegister ((w_mid - 2) + 1) N :=
        rMid.slice 1 ((w_mid - 2) + 1) (by omega)
      have hdisj_rem : Disjoint rTail.image (rScr.slice 0 (s - 0) (by omega)).image :=
        Disjoint.mono (slice_image_subset rMid 1 _ _) (slice_image_subset rScr 0 _ _) hdisj_ms
      refine CleanRealizes.congr_unitary
        (CleanRealizes.congr_scr
          (withAllOnesIndicator_cleanRealizes v (w_mid - 2) rTail rScr 0 (by omega)
            _ hdisj_rem (fun b β ↦ β q₀ * b)
            (fun b β q hq val ↦ by
              have hne : q₀ ≠ q := fun heq ↦
                Finset.disjoint_left.mp hdisj_ms
                  ((QRegister.mem_image rMid q₀).mpr ⟨⟨0, hmid_pos⟩, rfl⟩)
                  (heq ▸ slice_image_subset rScr 0 _ _ hq)
              simp [Function.update_of_ne hne])
            _
            (fun w_ind hw ↦ by
              have hne : q₀ ≠ w_ind := by
                intro heq
                rw [← heq] at hw
                rcases Finset.mem_union.mp hw with hm_tail | hm_scr
                · exact apply_not_mem_slice_of_lt rMid _ (by dsimp; omega) hm_tail
                · exact Finset.disjoint_left.mp hdisj_ms
                    ((QRegister.mem_image rMid q₀).mpr ⟨⟨0, hmid_pos⟩, rfl⟩)
                    (slice_image_subset rScr 0 _ _ hm_scr)
              have hdisj_leaf : Disjoint (czCircuit q₀ w_ind hne).support
                  (rScr.slice (0 + (w_mid - 2)) (s - (0 + (w_mid - 2))) (by omega)).image := by
                rw [czCircuit_support]
                simp only [Finset.disjoint_insert_left, Finset.disjoint_singleton_left]
                refine ⟨fun hm ↦ Finset.disjoint_left.mp hdisj_ms
                    ((QRegister.mem_image rMid q₀).mpr ⟨⟨0, hmid_pos⟩, rfl⟩)
                    (slice_image_subset rScr _ _ _ hm), ?_⟩
                intro hm
                rcases Finset.mem_union.mp hw with hm_tail | hm_scr
                · exact Finset.disjoint_left.mp hdisj_ms
                    (slice_image_subset rMid 1 _ _ hm_tail)
                    (slice_image_subset rScr _ _ _ hm)
                · exact Finset.disjoint_left.mp
                    (disjoint_slice_of_le rScr (by omega) (by omega) (by omega)) hm_scr hm
              exact (CleanRealizes_circuit_of_disjoint v _ _ (czCircuit_count_toff q₀ w_ind hne)
                hdisj_leaf).congr_unitary (czCircuit_eval_eq_diagSignUnitary q₀ w_ind hne)))
          ((slice_image_eq rScr _ _ rfl (by omega)).trans (slice_zero_self_image rScr)))
        ?_
      congr 1; funext β
      have hslice : (∏ j : Fin ((w_mid - 2) + 1), β (rTail j)) =
          ∏ j : Fin ((w_mid - 2) + 1), β (rMid ⟨1 + j.val, by omega⟩) := by
        refine Finset.prod_congr rfl fun j _ ↦ ?_
        simp [rTail]
      rw [hslice]
      exact fin_prod_head_mul_slice (by omega) (fun i ↦ β (rMid i))
  refine (CleanRealizes_withXMask hdisj_ms (fun _ ↦ 1) hallOnes).congr_unitary ?_
  congr 1; funext β
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  exact maskShiftBits_apply_reg rMid (fun _ ↦ 1) β i

theorem zeroAll_eq_one_iff {N w : ℕ} (r : QRegister w N) (idx : Fin (2 ^ N)) :
    (∏ i : Fin w, (basisBits N idx (r i) + 1)) = 1 ↔ r.extractIndex idx = 0 := by
  rw [zmod2_prod_eq_one_iff, extractIndex_eq_iff]
  simp only [basisBits_zero]
  refine ⟨fun h i ↦ ?_, fun h i ↦ by rw [h i, zero_add]⟩
  have hi := h i
  rcases zmod2_eq_zero_or_one (basisBits N idx (r i)) with h0 | h1
  · exact h0
  · rw [h1] at hi
    exact absurd hi (by decide)

theorem diagSignUnitary_eq_embed_reflMidUnitary {N k_walk w_mid : ℕ}
    (rWalk : QRegister k_walk N) (inMid : QRegister w_mid k_walk) :
    diagSignUnitary (fun β ↦ ∏ i : Fin w_mid, (β ((rWalk.compose inMid) i) + 1)) =
      rWalk.embedUnitary (reflMidUnitary inMid) := by
  let rMid := rWalk.compose inMid
  apply Subtype.ext
  have hrhs : (rWalk.embedUnitary (reflMidUnitary inMid)).1 =
      1 - (2 : ℂ) • rMid.basisOutcomeProjector 0 := by
    rw [QRegister.embedUnitary_val, reflMidUnitary_val, embedMatrix_sub_local,
      QRegister.embedMatrix_one, QRegister.embedMatrix_smul, projMid,
      ← compose_basisOutcomeProjector]
  rw [diagSignUnitary_val, diagSignMatrix, hrhs, QRegister.basisOutcomeProjector_eq_diagonal]
  ext idx j
  by_cases hij : idx = j
  · subst hij
    rw [Matrix.diagonal_apply_eq]
    by_cases h0 : rMid.extractIndex idx = 0
    · have hp : (∏ i : Fin w_mid, (basisBits N idx ((rWalk.compose inMid) i) + 1)) = 1 :=
        (zeroAll_eq_one_iff (rWalk.compose inMid) idx).mpr h0
      rw [hp]
      simp [h0, bitSign]
      norm_num
    · have hp : (∏ i : Fin w_mid, (basisBits N idx ((rWalk.compose inMid) i) + 1)) = 0 := by
        rcases zmod2_eq_zero_or_one
          (∏ i : Fin w_mid, (basisBits N idx ((rWalk.compose inMid) i) + 1)) with hz | ho
        · exact hz
        · exact absurd ((zeroAll_eq_one_iff (rWalk.compose inMid) idx).mp ho) h0
      rw [hp]
      simp [h0, bitSign]
  · simp [hij]

/-- `reflMidDyn` realizes `reflMidUnitary inMid` on `rWalk` with clean scratch `rScr`. -/
theorem reflMidDyn_cleanRealizes {Var : Type} [Fintype Var] [DecidableEq Var]
    {N k_walk w_mid s : ℕ}
    (v : Var) (rWalk : QRegister k_walk N) (inMid : QRegister w_mid k_walk)
    (rScr : QRegister s N)
    (hmid_pos : 1 ≤ w_mid) (hs_mid : w_mid - 2 ≤ s)
    (hMidScr : (rWalk.compose inMid).DisjointWires rScr) :
    CleanRealizes v rWalk rScr (reflMidUnitary inMid)
      (reflMidDyn v (rWalk.compose inMid) rScr hmid_pos hs_mid hMidScr) :=
  ((reflMidDyn_cleanRealizes_whole v (rWalk.compose inMid) rScr hmid_pos hs_mid
    hMidScr).congr_unitary (diagSignUnitary_eq_embed_reflMidUnitary rWalk inMid)).of_whole

/-- Input-subspace reflection `reflInDyn`
($R_1 = 2|0_{\mathrm{all}}\rangle\langle 0_{\mathrm{all}}| - I$)
using `4 * (w_all - 2)` `T` gates and `0` `TOFF` gates. -/
def reflInDyn {Var : Type} {N w_all s : ℕ}
    (v : Var) (rAll : QRegister w_all N) (rScr : QRegister s N)
    (hall_pos : 1 ≤ w_all) (hs_in : w_all - 2 ≤ s)
    (hAllScr : rAll.DisjointWires rScr) : DynamicCircuit Var N :=
  .seq (reflMidDyn v rAll rScr hall_pos hs_in hAllScr)
    (.circuit (globalMinusCircuit (rAll ⟨0, hall_pos⟩)))

@[simp]
theorem reflInDyn_count_toff {Var : Type} {N w_all s : ℕ}
    (v : Var) (rAll : QRegister w_all N) (rScr : QRegister s N)
    (hall_pos : 1 ≤ w_all) (hs_in : w_all - 2 ≤ s)
    (hAllScr : rAll.DisjointWires rScr) :
    (reflInDyn v rAll rScr hall_pos hs_in hAllScr).count PrimitiveGate.TOFF = 0 := by
  simp [reflInDyn]

@[simp]
theorem reflInDyn_count_t {Var : Type} {N w_all s : ℕ}
    (v : Var) (rAll : QRegister w_all N) (rScr : QRegister s N)
    (hall_pos : 1 ≤ w_all) (hs_in : w_all - 2 ≤ s)
    (hAllScr : rAll.DisjointWires rScr) :
    (reflInDyn v rAll rScr hall_pos hs_in hAllScr).count PrimitiveGate.T =
      4 * (w_all - 2) := by
  simp [reflInDyn]

theorem diagSignUnitary_eq_embed_reflInUnitary {N k_walk w_all : ℕ}
    (rWalk : QRegister k_walk N) (inAll : QRegister w_all k_walk) :
    diagSignUnitary (fun β ↦ 1 + ∏ i : Fin w_all, (β ((rWalk.compose inAll) i) + 1)) =
      rWalk.embedUnitary (reflInUnitary inAll) := by
  let rAll := rWalk.compose inAll
  apply Subtype.ext
  have hrhs : (rWalk.embedUnitary (reflInUnitary inAll)).1 =
      (2 : ℂ) • rAll.basisOutcomeProjector 0 - 1 := by
    rw [QRegister.embedUnitary_val, reflInUnitary_val, embedMatrix_sub_local,
      QRegister.embedMatrix_one, QRegister.embedMatrix_smul, projIn,
      ← compose_basisOutcomeProjector]
  rw [diagSignUnitary_val, diagSignMatrix, hrhs, QRegister.basisOutcomeProjector_eq_diagonal]
  ext idx j
  by_cases hij : idx = j
  · subst hij
    rw [Matrix.diagonal_apply_eq]
    by_cases h0 : rAll.extractIndex idx = 0
    · have hp : (∏ i : Fin w_all, (basisBits N idx ((rWalk.compose inAll) i) + 1)) = 1 :=
        (zeroAll_eq_one_iff (rWalk.compose inAll) idx).mpr h0
      rw [hp, CharTwo.add_self_eq_zero]
      simp [h0, bitSign]
      norm_num
    · have hp : (∏ i : Fin w_all, (basisBits N idx ((rWalk.compose inAll) i) + 1)) = 0 := by
        rcases zmod2_eq_zero_or_one
          (∏ i : Fin w_all, (basisBits N idx ((rWalk.compose inAll) i) + 1)) with hz | ho
        · exact hz
        · exact absurd ((zeroAll_eq_one_iff (rWalk.compose inAll) idx).mp ho) h0
      rw [hp, add_zero]
      simp [h0, bitSign]
  · simp [hij]

/-- `reflInDyn` realizes `reflInUnitary inAll` on `rWalk` with clean scratch `rScr`. -/
theorem reflInDyn_cleanRealizes {Var : Type} [Fintype Var] [DecidableEq Var]
    {N k_walk w_all s : ℕ}
    (v : Var) (rWalk : QRegister k_walk N) (inAll : QRegister w_all k_walk)
    (rScr : QRegister s N)
    (hall_pos : 1 ≤ w_all) (hs_in : w_all - 2 ≤ s)
    (hAllScr : (rWalk.compose inAll).DisjointWires rScr) :
    CleanRealizes v rWalk rScr (reflInUnitary inAll)
      (reflInDyn v (rWalk.compose inAll) rScr hall_pos hs_in hAllScr) := by
  let rAll := rWalk.compose inAll
  have hdisj := disjoint_image_of_disjointWires hAllScr
  have hmid := reflMidDyn_cleanRealizes_whole v rAll rScr hall_pos hs_in hAllScr
  have hgm : CleanRealizes v (QRegister.whole N) rScr
      (diagSignUnitary (fun _ ↦ 1)) (.circuit (globalMinusCircuit (rAll ⟨0, hall_pos⟩))) :=
    (CleanRealizes_circuit_of_disjoint v rScr _ (globalMinusCircuit_count_toff _) (by
      rw [globalMinusCircuit_support, Finset.disjoint_singleton_left]
      exact Finset.disjoint_left.mp hdisj ((QRegister.mem_image rAll _).mpr ⟨⟨0, hall_pos⟩, rfl⟩)
    )).congr_unitary (globalMinusCircuit_eval_eq_diagSignUnitary _)
  exact ((hmid.seq hgm).congr_unitary (by
    rw [diagSignUnitary_mul]
    exact diagSignUnitary_eq_embed_reflInUnitary rWalk inAll)).of_whole

/-!
### QPE-Conditioned Reflections (`reflInOnlyAtZeroDyn` & `reflInSkipAtDyn`)
-/

/-- Leaf bit formula `(if invertEq then b_eq + 1 else b_eq) * (b_z + 1)` for
QPE-conditioned `R₁`. -/
def leafBit (invertEq : Bool) (b_eq b_z : ZMod 2) : ZMod 2 :=
  (if invertEq then b_eq + 1 else b_eq) * (b_z + 1)

/-- `X`-wrapped `CZ` leaf circuit (`0` `T` gates, `0` `TOFF` gates) realizing `leafBit`. -/
def leafPhaseCircuit {N : ℕ} (invertEq : Bool) (w_eq w_z : Wire N) (hne : w_eq ≠ w_z) :
    Circuit N :=
  let base := Circuit.X w_z ;;ᶜ czCircuit w_eq w_z hne ;;ᶜ Circuit.X w_z
  if invertEq then Circuit.X w_eq ;;ᶜ base ;;ᶜ Circuit.X w_eq else base

@[simp]
theorem leafPhaseCircuit_count_t {N : ℕ} (invertEq : Bool) (w_eq w_z : Wire N) (hne : w_eq ≠ w_z) :
    (leafPhaseCircuit invertEq w_eq w_z hne).count PrimitiveGate.T = 0 := by
  cases invertEq <;> simp [leafPhaseCircuit]

@[simp]
theorem leafPhaseCircuit_count_toff {N : ℕ} (invertEq : Bool) (w_eq w_z : Wire N)
    (hne : w_eq ≠ w_z) :
    (leafPhaseCircuit invertEq w_eq w_z hne).count PrimitiveGate.TOFF = 0 := by
  cases invertEq <;> simp [leafPhaseCircuit]

theorem leafPhaseCircuit_support_subset {N : ℕ} (invertEq : Bool) (w_eq w_z : Wire N)
    (hne : w_eq ≠ w_z) :
    (leafPhaseCircuit invertEq w_eq w_z hne).support ⊆ {w_eq, w_z} := by
  intro q hq
  cases invertEq <;>
    simp only [leafPhaseCircuit, Bool.false_eq_true, ↓reduceIte, Circuit.support_seq,
      Circuit.support_single, czCircuit_support, Finset.mem_union, Finset.mem_insert,
      Finset.mem_singleton] at hq ⊢ <;>
    tauto

theorem leafPhaseCircuit_eval {N : ℕ} (invertEq : Bool) (w_eq w_z : Wire N) (hne : w_eq ≠ w_z) :
    (leafPhaseCircuit invertEq w_eq w_z hne).eval =
      diagSignUnitary (fun β ↦ leafBit invertEq (β w_eq) (β w_z)) := by
  have hbase : (Circuit.X w_z ;;ᶜ czCircuit w_eq w_z hne ;;ᶜ Circuit.X w_z).eval =
      diagSignUnitary (fun β ↦ β w_eq * (β w_z + 1)) := by
    rw [Circuit.eval_seq, Circuit.eval_seq, czCircuit_eval_eq_diagSignUnitary,
      x_conj_diagSignUnitary]
    congr 1; funext β
    rw [Function.update_of_ne hne, Function.update_self]
  cases invertEq with
  | false =>
      simpa [leafPhaseCircuit, leafBit] using hbase
  | true =>
      simp only [leafPhaseCircuit, ↓reduceIte]
      rw [Circuit.eval_seq, Circuit.eval_seq, hbase, x_conj_diagSignUnitary]
      congr 1; funext β
      simp [leafBit, Function.update_self, Function.update_of_ne hne.symm]

/-- Nested double Gidney-AND ladder reducing `rQPE` (`b_qpe - 1` steps) and `rAll` (`w_all - 1`
steps) to `(w_eq, w_z)` and applying `leafPhaseCircuit`. -/
def qpePatInnerDyn {Var : Type} {N b_qpe w_all s : ℕ}
    (v : Var) (invertEq : Bool)
    (rQPE : QRegister b_qpe N) (rAll : QRegister w_all N) (rScr : QRegister s N)
    (hb : 1 ≤ b_qpe) (hall : 1 ≤ w_all)
    (hs : (b_qpe - 1) + (w_all - 1) ≤ s)
    (hQA : rQPE.DisjointWires rAll)
    (hQS : rQPE.DisjointWires rScr)
    (hAS : rAll.DisjointWires rScr) : DynamicCircuit Var N :=
  let rQSlice := rQPE.slice 0 ((b_qpe - 1) + 1) (by omega)
  let rASlice := rAll.slice 0 ((w_all - 1) + 1) (by omega)
  have hdisjQ : Disjoint rQSlice.image (rScr.slice 0 (b_qpe - 1) (by omega)).image :=
    Disjoint.mono (slice_image_subset rQPE 0 _ _) (slice_image_subset rScr 0 _ _)
      (disjoint_image_of_disjointWires hQS)
  have hdisjA :
      Disjoint rASlice.image (rScr.slice (b_qpe - 1) (w_all - 1) (by omega)).image :=
    Disjoint.mono (slice_image_subset rAll 0 _ _) (slice_image_subset rScr _ _ _)
      (disjoint_image_of_disjointWires hAS)
  withAllOnesIndicator v (b_qpe - 1) rQSlice rScr 0 (by omega) hdisjQ
    fun w_eq hw_eq ↦
      withAllOnesIndicator v (w_all - 1) rASlice rScr (b_qpe - 1) (by omega) hdisjA
        fun w_z hw_z ↦
          have hne : w_eq ≠ w_z := by
            intro heq
            rw [← heq] at hw_z
            rcases Finset.mem_union.mp hw_eq with hq_in | hq_scr
            · rcases Finset.mem_union.mp hw_z with ha_in | ha_scr
              · exact Finset.disjoint_left.mp (disjoint_image_of_disjointWires hQA)
                  (slice_image_subset rQPE 0 _ _ hq_in)
                  (slice_image_subset rAll 0 _ _ ha_in)
              · exact Finset.disjoint_left.mp (disjoint_image_of_disjointWires hQS)
                  (slice_image_subset rQPE 0 _ _ hq_in)
                  (slice_image_subset rScr _ _ _ ha_scr)
            · rcases Finset.mem_union.mp hw_z with ha_in | ha_scr
              · exact Finset.disjoint_left.mp (disjoint_image_of_disjointWires hAS)
                  (slice_image_subset rAll 0 _ _ ha_in)
                  (slice_image_subset rScr 0 _ _ hq_scr)
              · exact Finset.disjoint_left.mp
                  (disjoint_slice_of_le rScr (by omega) (by omega) (by omega)) hq_scr ha_scr
          .circuit (leafPhaseCircuit invertEq w_eq w_z hne)

/-- Pattern-controlled reflection on `(rQPE, rAll)` with `4 * ((b_qpe - 1) + (w_all - 1))` `T`
gates and `0` `TOFF` gates. -/
def qpePatReflInDyn {Var : Type} {N b_qpe w_all s : ℕ}
    (v : Var) (invertEq : Bool) (pat : Fin (2 ^ b_qpe))
    (rQPE : QRegister b_qpe N) (rAll : QRegister w_all N) (rScr : QRegister s N)
    (hb : 1 ≤ b_qpe) (hall : 1 ≤ w_all)
    (hs : (b_qpe - 1) + (w_all - 1) ≤ s)
    (hQA : rQPE.DisjointWires rAll)
    (hQS : rQPE.DisjointWires rScr)
    (hAS : rAll.DisjointWires rScr) : DynamicCircuit Var N :=
  withXMask rQPE (fun j ↦ basisBits b_qpe pat j + 1)
    (withXMask rAll (fun _ ↦ 1)
      (qpePatInnerDyn v invertEq rQPE rAll rScr hb hall hs hQA hQS hAS))

@[simp]
theorem qpePatReflInDyn_count_toff {Var : Type} {N b_qpe w_all s : ℕ}
    (v : Var) (invertEq : Bool) (pat : Fin (2 ^ b_qpe))
    (rQPE : QRegister b_qpe N) (rAll : QRegister w_all N) (rScr : QRegister s N)
    (hb : 1 ≤ b_qpe) (hall : 1 ≤ w_all)
    (hs : (b_qpe - 1) + (w_all - 1) ≤ s)
    (hQA : rQPE.DisjointWires rAll)
    (hQS : rQPE.DisjointWires rScr)
    (hAS : rAll.DisjointWires rScr) :
    (qpePatReflInDyn v invertEq pat rQPE rAll rScr hb hall hs hQA hQS hAS).count
      PrimitiveGate.TOFF = 0 := by
  rw [qpePatReflInDyn, withXMask_count_toff, withXMask_count_toff, qpePatInnerDyn]
  exact withAllOnesIndicator_count_toff _ _ _ _ _ _ _ _ fun _ _ ↦
    withAllOnesIndicator_count_toff _ _ _ _ _ _ _ _ fun _ _ ↦
      leafPhaseCircuit_count_toff _ _ _ _

@[simp]
theorem qpePatReflInDyn_count_t {Var : Type} {N b_qpe w_all s : ℕ}
    (v : Var) (invertEq : Bool) (pat : Fin (2 ^ b_qpe))
    (rQPE : QRegister b_qpe N) (rAll : QRegister w_all N) (rScr : QRegister s N)
    (hb : 1 ≤ b_qpe) (hall : 1 ≤ w_all)
    (hs : (b_qpe - 1) + (w_all - 1) ≤ s)
    (hQA : rQPE.DisjointWires rAll)
    (hQS : rQPE.DisjointWires rScr)
    (hAS : rAll.DisjointWires rScr) :
    (qpePatReflInDyn v invertEq pat rQPE rAll rScr hb hall hs hQA hQS hAS).count
      PrimitiveGate.T = 4 * ((b_qpe - 1) + (w_all - 1)) := by
  rw [qpePatReflInDyn, withXMask_count_t, withXMask_count_t, qpePatInnerDyn]
  rw [withAllOnesIndicator_count_t _ _ _ _ _ _ _ _ (4 * (w_all - 1)) fun _ _ ↦ ?_]
  · omega
  · rw [withAllOnesIndicator_count_t _ _ _ _ _ _ _ _ 0 ?_]
    · simp
    · intro _ _; exact leafPhaseCircuit_count_t _ _ _ _

theorem qpePatReflInDyn_cleanRealizes_whole {Var : Type} [Fintype Var] [DecidableEq Var]
    {N b_qpe w_all s : ℕ}
    (v : Var) (invertEq : Bool) (pat : Fin (2 ^ b_qpe))
    (rQPE : QRegister b_qpe N) (rAll : QRegister w_all N) (rScr : QRegister s N)
    (hb : 1 ≤ b_qpe) (hall : 1 ≤ w_all)
    (hs : (b_qpe - 1) + (w_all - 1) ≤ s)
    (hQA : rQPE.DisjointWires rAll)
    (hQS : rQPE.DisjointWires rScr)
    (hAS : rAll.DisjointWires rScr) :
    CleanRealizes v (QRegister.whole N) rScr
      (diagSignUnitary fun β ↦
        leafBit invertEq
          (∏ j : Fin b_qpe, (β (rQPE j) + (basisBits b_qpe pat j + 1)))
          (∏ i : Fin w_all, (β (rAll i) + 1)))
      (qpePatReflInDyn v invertEq pat rQPE rAll rScr hb hall hs hQA hQS hAS) := by
  have hdQA := disjoint_image_of_disjointWires hQA
  have hdQS := disjoint_image_of_disjointWires hQS
  have hdAS := disjoint_image_of_disjointWires hAS
  let rQSlice := rQPE.slice 0 ((b_qpe - 1) + 1) (by omega)
  let rASlice := rAll.slice 0 ((w_all - 1) + 1) (by omega)
  have hinner : CleanRealizes v (QRegister.whole N) rScr
      (diagSignUnitary fun β ↦
        leafBit invertEq (∏ j : Fin b_qpe, β (rQPE j)) (∏ i : Fin w_all, β (rAll i)))
      (qpePatInnerDyn v invertEq rQPE rAll rScr hb hall hs hQA hQS hAS) := by
    dsimp only [qpePatInnerDyn]
    have hdisjQ_rem : Disjoint rQSlice.image (rScr.slice 0 (s - 0) (by omega)).image :=
      Disjoint.mono (slice_image_subset rQPE 0 _ _) (slice_image_subset rScr 0 _ _) hdQS
    have hdisjA_rem :
        Disjoint rASlice.image (rScr.slice (b_qpe - 1) (s - (b_qpe - 1)) (by omega)).image :=
      Disjoint.mono (slice_image_subset rAll 0 _ _) (slice_image_subset rScr _ _ _) hdAS
    refine CleanRealizes.congr_unitary
      (CleanRealizes.congr_scr
        (withAllOnesIndicator_cleanRealizes v (b_qpe - 1) rQSlice rScr 0 (by omega)
          _ hdisjQ_rem
          (fun b_eq β ↦ leafBit invertEq b_eq (∏ j : Fin ((w_all - 1) + 1), β (rASlice j)))
          (fun b_eq β q hq val ↦ by
            congr 1
            refine Finset.prod_congr rfl fun j _ ↦ ?_
            have hne : rASlice j ≠ q := fun heq ↦
              Finset.disjoint_left.mp hdAS
                (slice_image_subset rAll 0 _ _ ((QRegister.mem_image rASlice _).mpr ⟨j, rfl⟩))
                (heq ▸ slice_image_subset rScr 0 _ _ hq)
            exact Function.update_of_ne hne _ _)
          _
          (fun w_eq hw_eq ↦ by
            have himg_off :
                (rScr.slice (0 + (b_qpe - 1)) (s - (0 + (b_qpe - 1))) (by omega)).image =
                  (rScr.slice (b_qpe - 1) (s - (b_qpe - 1)) (by omega)).image :=
              slice_image_eq rScr _ _ (by omega) (by omega)
            exact CleanRealizes.congr_scr
              (withAllOnesIndicator_cleanRealizes v (w_all - 1) rASlice rScr (b_qpe - 1)
                (by omega) _ hdisjA_rem
                (fun b_z β ↦ leafBit invertEq (β w_eq) b_z)
                (fun b_z β q hq val ↦ by
                  have hne : w_eq ≠ q := by
                    intro heq
                    rw [heq] at hw_eq
                    rcases Finset.mem_union.mp hw_eq with hq_in | hq_scr
                    · exact Finset.disjoint_left.mp hdQS
                        (slice_image_subset rQPE 0 _ _ hq_in)
                        (slice_image_subset rScr _ _ _ hq)
                    · exact Finset.disjoint_left.mp
                        (disjoint_slice_of_le rScr (by omega) (by omega) (by omega)) hq_scr hq
                  simp [Function.update_of_ne hne])
                _
                (fun w_z hw_z ↦ by
                  have hne : w_eq ≠ w_z := by
                    intro heq
                    rw [← heq] at hw_z
                    rcases Finset.mem_union.mp hw_eq with hq_in | hq_scr
                    · rcases Finset.mem_union.mp hw_z with ha_in | ha_scr
                      · exact Finset.disjoint_left.mp hdQA
                          (slice_image_subset rQPE 0 _ _ hq_in)
                          (slice_image_subset rAll 0 _ _ ha_in)
                      · exact Finset.disjoint_left.mp hdQS
                          (slice_image_subset rQPE 0 _ _ hq_in)
                          (slice_image_subset rScr _ _ _ ha_scr)
                    · rcases Finset.mem_union.mp hw_z with ha_in | ha_scr
                      · exact Finset.disjoint_left.mp hdAS
                          (slice_image_subset rAll 0 _ _ ha_in)
                          (slice_image_subset rScr 0 _ _ hq_scr)
                      · exact Finset.disjoint_left.mp
                          (disjoint_slice_of_le rScr (by omega) (by omega) (by omega))
                          hq_scr ha_scr
                  have hdisj_leaf : Disjoint (leafPhaseCircuit invertEq w_eq w_z hne).support
                      (rScr.slice ((b_qpe - 1) + (w_all - 1))
                        (s - ((b_qpe - 1) + (w_all - 1))) (by omega)).image := by
                    refine Disjoint.mono_left
                      (leafPhaseCircuit_support_subset invertEq w_eq w_z hne) ?_
                    simp only [Finset.disjoint_insert_left, Finset.disjoint_singleton_left]
                    refine ⟨?_, ?_⟩
                    · intro hm
                      rcases Finset.mem_union.mp hw_eq with hq_in | hq_scr
                      · exact Finset.disjoint_left.mp hdQS
                          (slice_image_subset rQPE 0 _ _ hq_in)
                          (slice_image_subset rScr _ _ _ hm)
                      · exact Finset.disjoint_left.mp
                          (disjoint_slice_of_le rScr (by omega) (by omega) (by omega)) hq_scr hm
                    · intro hm
                      rcases Finset.mem_union.mp hw_z with ha_in | ha_scr
                      · exact Finset.disjoint_left.mp hdAS
                          (slice_image_subset rAll 0 _ _ ha_in)
                          (slice_image_subset rScr _ _ _ hm)
                      · exact Finset.disjoint_left.mp
                          (disjoint_slice_of_le rScr (by omega) (by omega) (by omega)) ha_scr hm
                  exact (CleanRealizes_circuit_of_disjoint v _ _
                    (leafPhaseCircuit_count_toff invertEq w_eq w_z hne) hdisj_leaf).congr_unitary
                    (leafPhaseCircuit_eval invertEq w_eq w_z hne)))
              himg_off.symm))
        ((slice_image_eq rScr _ _ rfl (by omega)).trans (slice_zero_self_image rScr)))
      ?_
    congr 1; funext β
    rw [fin_prod_slice_zero_eq rQPE (by omega) (by omega) β,
      fin_prod_slice_zero_eq rAll (by omega) (by omega) β]
  have hmaskA := CleanRealizes_withXMask hdAS (fun _ ↦ 1) hinner
  have hmaskQ := CleanRealizes_withXMask hdQS (fun j ↦ basisBits b_qpe pat j + 1) hmaskA
  refine hmaskQ.congr_unitary ?_
  congr 1; funext β
  let β₁ := maskShiftBits rQPE (fun j ↦ basisBits b_qpe pat j + 1) β
  have hQ : (∏ j : Fin b_qpe, maskShiftBits rAll (fun _ ↦ 1) β₁ (rQPE j)) =
      ∏ j : Fin b_qpe, (β (rQPE j) + (basisBits b_qpe pat j + 1)) := by
    refine Finset.prod_congr rfl fun j _ ↦ ?_
    have hnot : rQPE j ∉ rAll.image :=
      Finset.disjoint_left.mp hdQA ((QRegister.mem_image rQPE _).mpr ⟨j, rfl⟩)
    rw [maskShiftBits_of_not_mem rAll _ β₁ hnot]
    dsimp only [β₁]
    rw [maskShiftBits_apply_reg]
  have hA : (∏ i : Fin w_all, maskShiftBits rAll (fun _ ↦ 1) β₁ (rAll i)) =
      ∏ i : Fin w_all, (β (rAll i) + 1) := by
    refine Finset.prod_congr rfl fun i _ ↦ ?_
    have hnot : rAll i ∉ rQPE.image :=
      Finset.disjoint_left.mp hdQA.symm ((QRegister.mem_image rAll _).mpr ⟨i, rfl⟩)
    rw [maskShiftBits_apply_reg]
    dsimp only [β₁]
    rw [maskShiftBits_of_not_mem rQPE _ β hnot]
  dsimp only [β₁] at hQ hA
  rw [hQ, hA]

theorem eqPat_eq_one_iff {N b_qpe : ℕ} (rQPE : QRegister b_qpe N)
    (pat : Fin (2 ^ b_qpe)) (idx : Fin (2 ^ N)) :
    (∏ j : Fin b_qpe, (basisBits N idx (rQPE j) + (basisBits b_qpe pat j + 1))) = 1 ↔
      rQPE.extractIndex idx = pat := by
  have h11 : (1 : ZMod 2) + 1 = 0 := CharTwo.add_self_eq_zero 1
  rw [zmod2_prod_eq_one_iff, extractIndex_eq_iff]
  refine ⟨fun h j ↦ ?_, fun h j ↦ ?_⟩
  · have hj := h j
    rcases zmod2_eq_zero_or_one (basisBits N idx (rQPE j)) with h0 | h1 <;>
      rcases zmod2_eq_zero_or_one (basisBits b_qpe pat j) with p0 | p1 <;>
      simp_all
  · rw [h j]
    rcases zmod2_eq_zero_or_one (basisBits b_qpe pat j) with p0 | p1
    · simp [p0]
    · simp [p1, h11]

theorem diagSignUnitary_eq_embed_qpeMux_reflIn {N b_qpe k_walk w_all : ℕ}
    (invertEq : Bool) (pat : Fin (2 ^ b_qpe))
    (rQPE : QRegister b_qpe N) (rWalk : QRegister k_walk N) (hQW : rQPE.DisjointWires rWalk)
    (inAll : QRegister w_all k_walk) :
    let rAll := rWalk.compose inAll
    let rComb := rQPE.concat rWalk hQW
    diagSignUnitary (fun β ↦
      leafBit invertEq
        (∏ j : Fin b_qpe, (β (rQPE j) + (basisBits b_qpe pat j + 1)))
        (∏ i : Fin w_all, (β (rAll i) + 1))) =
      rComb.embedUnitary (qpeMuxUnitary fun m : Fin (2 ^ b_qpe) ↦
        if (if invertEq then m ≠ pat else m = pat) then reflInUnitary inAll else 1) := by
  intro rAll rComb
  apply Subtype.ext
  have hemb_mux :
      (rComb.embedUnitary (qpeMuxUnitary fun m : Fin (2 ^ b_qpe) ↦
        if (if invertEq then m ≠ pat else m = pat) then reflInUnitary inAll else 1)).1 =
      ∑ m : Fin (2 ^ b_qpe),
        rQPE.basisOutcomeProjector m *
          rWalk.embedMatrix
            (if (if invertEq then m ≠ pat else m = pat) then (reflInUnitary inAll).1 else 1) := by
    rw [QRegister.embedUnitary_val, qpeMuxUnitary_val, qpeMuxMatrix, QRegister.embedMatrix_sum]
    refine Finset.sum_congr rfl fun m _ ↦ ?_
    rw [QRegister.embedMatrix_mul, ← compose_basisOutcomeProjector,
      ← QRegister.embedMatrix_compose, concat_compose_qpeInCombined,
      concat_compose_walkInCombined]
    congr 2
    by_cases hc : (if invertEq then m ≠ pat else m = pat) <;> simp [hc]
  have hrWalk_R₁ : rWalk.embedMatrix (reflInUnitary inAll).1 =
      diagSignMatrix (fun β ↦ 1 + ∏ i : Fin w_all, (β (rAll i) + 1)) := by
    have h := congrArg Subtype.val (diagSignUnitary_eq_embed_reflInUnitary rWalk inAll)
    exact h.symm
  rw [diagSignUnitary_val, diagSignMatrix, hemb_mux]
  ext idx j
  rw [Matrix.sum_apply]
  by_cases hij : idx = j
  · subst hij
    rw [Finset.sum_eq_single (rQPE.extractIndex idx)]
    · rw [QRegister.basisOutcomeProjector_eq_diagonal]
      have hproj_diag :
          ∀ M : Operator (2 ^ N),
            (Matrix.diagonal
              (fun g ↦ if rQPE.extractIndex g = rQPE.extractIndex idx then (1 : ℂ) else 0) * M)
              idx idx = M idx idx := by
        intro M
        simp [Matrix.diagonal_mul]
      rw [hproj_diag, Matrix.diagonal_apply_eq]
      let eqP := ∏ k : Fin b_qpe, (basisBits N idx (rQPE k) + (basisBits b_qpe pat k + 1))
      let zA := ∏ i : Fin w_all, (basisBits N idx (rAll i) + 1)
      have heqP : eqP = if rQPE.extractIndex idx = pat then 1 else 0 := by
        by_cases hp : rQPE.extractIndex idx = pat
        · simp [hp, (eqPat_eq_one_iff rQPE pat idx).mpr hp, eqP]
        · rcases zmod2_eq_zero_or_one eqP with h0 | h1
          · simp [hp, h0]
          · exact absurd ((eqPat_eq_one_iff rQPE pat idx).mp h1) hp
      change bitSign (leafBit invertEq eqP zA) = _
      have h11 : (1 : ZMod 2) + 1 = 0 := CharTwo.add_self_eq_zero 1
      cases invertEq <;> by_cases hp : rQPE.extractIndex idx = pat
      · rw [ite_eq_left (by simp [hp]), hrWalk_R₁, diagSignMatrix, Matrix.diagonal_apply_eq]
        change bitSign (leafBit false eqP zA) = bitSign (1 + zA)
        simp [leafBit, heqP, hp, add_comm]
      · rw [ite_eq_right (by simp [hp]), QRegister.embedMatrix_one, Matrix.one_apply_eq]
        simp [leafBit, heqP, hp]
      · rw [ite_eq_right (by simp [hp]), QRegister.embedMatrix_one, Matrix.one_apply_eq]
        simp [leafBit, heqP, hp, h11]
      · rw [ite_eq_left (by simp [hp]), hrWalk_R₁, diagSignMatrix, Matrix.diagonal_apply_eq]
        change bitSign (leafBit true eqP zA) = bitSign (1 + zA)
        simp [leafBit, heqP, hp, add_comm]
    · intro m _ hm
      rw [QRegister.basisOutcomeProjector_eq_diagonal]
      simp [Matrix.diagonal_mul, hm.symm]
    · simp
  · simp only [Matrix.diagonal_apply_ne _ hij]
    symm
    refine Finset.sum_eq_zero fun m _ ↦ ?_
    rw [QRegister.basisOutcomeProjector_eq_diagonal]
    by_cases hc : (if invertEq then m ≠ pat else m = pat)
    · rw [ite_eq_left hc, hrWalk_R₁, diagSignMatrix, Matrix.diagonal_mul_diagonal,
        Matrix.diagonal_apply_ne _ hij]
    · rw [ite_eq_right hc, QRegister.embedMatrix_one, Matrix.mul_one,
        Matrix.diagonal_apply_ne _ hij]

/-- QPE-zero-only reflection `reflInOnlyAtZeroDyn` ($R_1^{[m = 0]}$) using
`4 * ((b_qpe - 1) + (w_all - 1))` `T` gates and `0` `TOFF` gates. -/
def reflInOnlyAtZeroDyn {Var : Type} {N b_qpe w_all s : ℕ}
    (v : Var) (rQPE : QRegister b_qpe N) (rAll : QRegister w_all N) (rScr : QRegister s N)
    (hb : 1 ≤ b_qpe) (hall : 1 ≤ w_all)
    (hs : (b_qpe - 1) + (w_all - 1) ≤ s)
    (hQA : rQPE.DisjointWires rAll)
    (hQS : rQPE.DisjointWires rScr)
    (hAS : rAll.DisjointWires rScr) : DynamicCircuit Var N :=
  qpePatReflInDyn v false 0 rQPE rAll rScr hb hall hs hQA hQS hAS

@[simp]
theorem reflInOnlyAtZeroDyn_count_toff {Var : Type} {N b_qpe w_all s : ℕ}
    (v : Var) (rQPE : QRegister b_qpe N) (rAll : QRegister w_all N) (rScr : QRegister s N)
    (hb : 1 ≤ b_qpe) (hall : 1 ≤ w_all)
    (hs : (b_qpe - 1) + (w_all - 1) ≤ s)
    (hQA : rQPE.DisjointWires rAll)
    (hQS : rQPE.DisjointWires rScr)
    (hAS : rAll.DisjointWires rScr) :
    (reflInOnlyAtZeroDyn v rQPE rAll rScr hb hall hs hQA hQS hAS).count
      PrimitiveGate.TOFF = 0 :=
  qpePatReflInDyn_count_toff v false 0 rQPE rAll rScr hb hall hs hQA hQS hAS

@[simp]
theorem reflInOnlyAtZeroDyn_count_t {Var : Type} {N b_qpe w_all s : ℕ}
    (v : Var) (rQPE : QRegister b_qpe N) (rAll : QRegister w_all N) (rScr : QRegister s N)
    (hb : 1 ≤ b_qpe) (hall : 1 ≤ w_all)
    (hs : (b_qpe - 1) + (w_all - 1) ≤ s)
    (hQA : rQPE.DisjointWires rAll)
    (hQS : rQPE.DisjointWires rScr)
    (hAS : rAll.DisjointWires rScr) :
    (reflInOnlyAtZeroDyn v rQPE rAll rScr hb hall hs hQA hQS hAS).count
      PrimitiveGate.T = 4 * ((b_qpe - 1) + (w_all - 1)) :=
  qpePatReflInDyn_count_t v false 0 rQPE rAll rScr hb hall hs hQA hQS hAS

theorem reflInOnlyAtZeroDyn_cleanRealizes {Var : Type} [Fintype Var] [DecidableEq Var]
    {N b_qpe k_walk w_all s : ℕ}
    (v : Var) (rQPE : QRegister b_qpe N) (rWalk : QRegister k_walk N)
    (hQW : rQPE.DisjointWires rWalk)
    (inAll : QRegister w_all k_walk) (rScr : QRegister s N)
    (hb : 1 ≤ b_qpe) (hall : 1 ≤ w_all)
    (hs : (b_qpe - 1) + (w_all - 1) ≤ s)
    (hQA : rQPE.DisjointWires (rWalk.compose inAll))
    (hQS : rQPE.DisjointWires rScr)
    (hAS : (rWalk.compose inAll).DisjointWires rScr) :
    CleanRealizes v (rQPE.concat rWalk hQW) rScr
      (qpeMuxUnitary fun m : Fin (2 ^ b_qpe) ↦
        if m.val = 0 then reflInUnitary inAll else 1)
      (reflInOnlyAtZeroDyn v rQPE (rWalk.compose inAll) rScr hb hall hs hQA hQS hAS) := by
  have hw := (qpePatReflInDyn_cleanRealizes_whole v false 0 rQPE (rWalk.compose inAll) rScr
    hb hall hs hQA hQS hAS).congr_unitary
    (diagSignUnitary_eq_embed_qpeMux_reflIn false 0 rQPE rWalk hQW inAll)
  refine hw.of_whole.congr_unitary ?_
  apply Subtype.ext
  rw [qpeMuxUnitary_val, qpeMuxUnitary_val]
  congr 1; funext m
  have hm0 : (m = (0 : Fin (2 ^ b_qpe))) ↔ m.val = 0 := Fin.ext_iff
  by_cases h : m.val = 0 <;> simp [hm0, h]

theorem disjointWires_compose_left {N k w s : ℕ}
    {rWalk : QRegister k N} {sub : QRegister w k} {rScr : QRegister s N}
    (h : rWalk.DisjointWires rScr) : (rWalk.compose sub).DisjointWires rScr := by
  rw [QRegister.disjoint_iff]
  intro i j
  simpa using h.ne (sub i) j

theorem disjointWires_compose_right {N b k w : ℕ}
    {rQPE : QRegister b N} {rWalk : QRegister k N} {sub : QRegister w k}
    (h : rQPE.DisjointWires rWalk) : rQPE.DisjointWires (rWalk.compose sub) := by
  rw [QRegister.disjoint_iff]
  intro i j
  simpa using h.ne i (sub j)

end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.QubitisedWalk
