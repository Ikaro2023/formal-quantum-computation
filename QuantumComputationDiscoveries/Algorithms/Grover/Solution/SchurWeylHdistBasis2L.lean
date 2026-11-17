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
public import QuantumComputationDiscoveries.Algorithms.Grover.Solution.StageLoop
public import QuantumComputationDiscoveries.Algorithms.Grover.Solution.SchurWeylHdistLCertDefs
public import QuantumComputationDiscoveries.Algorithms.Grover.Solution.SchurWeylHdistOverlap2L
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Fintype.CardEmbedding
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
/-!
# Parametric `2 ≤ L ≤ 8` `H_dist_sym_rest` Subspace & Intertwiners (`SchurWeylHdistBasis2L`)

Constructs the `S_N`-equivariant `2L`-dimensional two-row Schur-Weyl conveyor subspace inside
`H_dist_sym_rest(2^n, L)` on `L * n + 1` qubits (`L` address registers of `n` qubits + `1`
weak-measurement flag qubit), its zero-oracle real orthogonal preparation, reflection diffuser
`D_0`, Cayley `SO(2)` Pieri intertwiners `W_1,..., W_{L-1}` composed with the rank-`dim(V_L)`
harmonic complement reflection `V(v)`, single-pulse evolution matching
`SchurWeylLCert.swLPulseStepReal`, hit-count Born probabilities matching
`SchurWeylLCert.swLAttemptProbReal`, and `SchurWeylLCert.IsValidSwLOverlap` for `2 ≤ L ≤ 8`,
`n ≥ 96`, `L ≤ r ≤ 1024`.
-/
@[expose] public section
namespace QuantumComputation.Specs.GroverFindAll
open Operator Matrix Real
open scoped Matrix RealInnerProductSpace
/-! ## Register Layout & Basis Equivalences on `L * n + 1` Qubits -/
/-- Combined `L * n`-qubit address register (`wires 0.. L * n - 1`) inside `L * n + 1`
  qubits. -/
def swLAddrReg (L n : ℕ) : QRegister (L * n) (L * n + 1) :=
  QRegister.block 0 (L * n) (by omega)
/-- Address slot `i: Fin L` (`wires i * n.. (i + 1) * n - 1`) inside `L * n + 1` qubits. -/
def swLSlotReg (L n : ℕ) (i : Fin L) : QRegister n (L * n + 1) :=
  QRegister.block (i.1 * n) n (by nlinarith [i.isLt])
/-- Weak-measurement flag subregister (`wire L * n`) inside `L * n + 1` qubits. -/
def swLFlagReg (L n : ℕ) : QRegister 1 (L * n + 1) :=
  QRegister.block (L * n) 1 (by omega)
/-- Extracted `L`-tuple of `n`-bit addresses from global basis index `z`. -/
def swLTuple (L n : ℕ) (z : Fin (2 ^ (L * n + 1))) : Fin L → Fin (2 ^ n) :=
  fun i ↦ (swLSlotReg L n i).extractIndex z
/-- Pairwise-distinct address predicate on the `L` `n`-qubit slots of `Fin (2 ^ (L * n +
  1))`. -/
def swLIsDist (L n : ℕ) (z : Fin (2 ^ (L * n + 1))) : Prop :=
  Function.Injective (swLTuple L n z)
instance (L n : ℕ) : DecidablePred (swLIsDist L n) :=
  fun z ↦ by unfold swLIsDist; infer_instance
/-- Total number of `R`-hits (`0.. L`) across the `L` `n`-qubit slots of `z`. -/
def swLHitCount (L n : ℕ) (R : Finset (Fin (2 ^ n))) (z : Fin (2 ^ (L * n + 1))) : ℕ :=
  ∑ i : Fin L, if (swLSlotReg L n i).extractIndex z ∈ R then 1 else 0
/-- Phase-flip unitary `-1` on `R` and `+1` outside `R` on `Fin (2 ^ n)`. -/
def swLSetOracleUnitary {n : ℕ} (R : Finset (Fin (2 ^ n))) : Unitary (2 ^ n) :=
  ⟨setOracleMatrix R, by
    rw [setOracleMatrix, Matrix.diagonal_mem_unitary, Pi.mem_unitary_iff]
    intro i
    split_ifs <;> simp⟩
namespace SwLInternal
/-- Local slot `i: Fin L` inside the `L * n`-qubit address register. -/
def addrSlotReg (L n : ℕ) (i : Fin L) : QRegister n (L * n) :=
  QRegister.block (i.1 * n) n (by nlinarith [i.isLt])
/-- Extracted `L`-tuple of `n`-bit addresses from `a: Fin (2 ^ (L * n))`. -/
def addrTuple (L n : ℕ) (a : Fin (2 ^ (L * n))) : Fin L → Fin (2 ^ n) :=
  fun i ↦ (addrSlotReg L n i).extractIndex a
theorem swLSlotReg_eq_compose (L n : ℕ) (i : Fin L) :
    swLSlotReg L n i = (swLAddrReg L n).compose (addrSlotReg L n i) := by
  ext w
  simp [swLSlotReg, swLAddrReg, addrSlotReg, QRegister.block_apply_val]
theorem swLTuple_eq_addrTuple (L n : ℕ) (z : Fin (2 ^ (L * n + 1))) :
    swLTuple L n z = addrTuple L n ((swLAddrReg L n).extractIndex z) := by
  funext i
  rw [swLTuple, addrTuple, swLSlotReg_eq_compose, QRegister.extractIndex_compose]
theorem addrTuple_zero (L n : ℕ) :
    addrTuple L n 0 = fun _ ↦ 0 := by
  funext i
  apply (basisBits n).injective
  funext b
  rw [addrTuple, QRegister.basisBits_extractIndex, basisBits_eq_div_mod, basisBits_eq_div_mod]; simp
theorem swLAddrReg_extractIndex_zero (L n : ℕ) :
    (swLAddrReg L n).extractIndex 0 = 0 := by
  apply (basisBits (L * n)).injective
  funext w
  rw [QRegister.basisBits_extractIndex, basisBits_eq_div_mod, basisBits_eq_div_mod]; simp
theorem swLFlagReg_extractIndex_zero (L n : ℕ) :
    (swLFlagReg L n).extractIndex 0 = 0 := by
  apply (basisBits 1).injective
  funext w
  rw [QRegister.basisBits_extractIndex, basisBits_eq_div_mod, basisBits_eq_div_mod]; simp
theorem addrTuple_bijective (L n : ℕ) :
    Function.Bijective (addrTuple L n) := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨?_, ?_⟩
  · intro a₁ a₂ heq; apply (basisBits (L * n)).injective
    funext w
    have hn : 0 < n := by
      rcases Nat.eq_zero_or_pos n with rfl | hpos
      · exact False.elim (Nat.not_lt_zero w.1 (by simpa using w.2))
      · exact hpos
    let i : Fin L := ⟨w.1 / n, (Nat.div_lt_iff_lt_mul hn).2 w.2⟩
    let b : Fin n := ⟨w.1 % n, Nat.mod_lt w.1 hn⟩
    have hw : (addrSlotReg L n i) b = w := by
      ext
      simp only [addrSlotReg, QRegister.block_apply_val, i, b]; exact (Nat.div_add_mod' w.1 n)
    have hi := congrArg (fun f ↦ basisBits n (f i) b) heq
    simpa only [addrTuple, QRegister.basisBits_extractIndex, hw] using hi
  · simp [Fintype.card_pi, Fintype.card_fin, pow_mul, mul_comm L n]
/-- Equivalence between `Fin (2 ^ (L * n))` and `L`-tuples `Fin L → Fin (2 ^ n)`. -/
noncomputable def addrEquiv (L n : ℕ) : Fin (2 ^ (L * n)) ≃ (Fin L → Fin (2 ^ n)) :=
  Equiv.ofBijective (addrTuple L n) (addrTuple_bijective L n)
@[simp]
theorem addrEquiv_apply (L n : ℕ) (a : Fin (2 ^ (L * n))) :
    addrEquiv L n a = addrTuple L n a := rfl
/-- Split map `z ↦ (addr, flag)` on `Fin (2 ^ (L * n + 1))`. -/
def splitPair (L n : ℕ) (z : Fin (2 ^ (L * n + 1))) : Fin (2 ^ (L * n)) × Fin 2 :=
  ((swLAddrReg L n).extractIndex z, (swLFlagReg L n).extractIndex z)
theorem splitPair_bijective (L n : ℕ) :
    Function.Bijective (splitPair L n) := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨?_, ?_⟩
  · intro z₁ z₂ heq; have ha := congrArg Prod.fst heq
    have hf := congrArg Prod.snd heq; dsimp only [splitPair] at ha hf
    apply (basisBits (L * n + 1)).injective
    funext w
    by_cases hw : w.1 < L * n
    · let u : Fin (L * n) := ⟨w.1, hw⟩
      have hwu : (swLAddrReg L n) u = w := by ext; simp [swLAddrReg, u]
      have hu := congrArg (fun x ↦ basisBits (L * n) x u) ha
      simpa only [QRegister.basisBits_extractIndex, hwu] using hu
    · have hw_eq : w.1 = L * n := by omega
      let u : Fin 1 := ⟨0, by omega⟩
      have hwu : (swLFlagReg L n) u = w := by ext; simp [swLFlagReg, u, hw_eq]
      have hu := congrArg (fun x ↦ basisBits 1 x u) hf
      simpa only [QRegister.basisBits_extractIndex, hwu] using hu
  · simp [Fintype.card_prod, Fintype.card_fin, pow_succ]
/-- Equivalence between `Fin (2 ^ (L * n + 1))` and `Fin (2 ^ (L * n)) × Fin 2`. -/
noncomputable def splitEquiv (L n : ℕ) : Fin (2 ^ (L * n + 1)) ≃ Fin (2 ^ (L * n)) × Fin 2 :=
  Equiv.ofBijective (splitPair L n) (splitPair_bijective L n)
theorem splitEquiv_apply (L n : ℕ) (z : Fin (2 ^ (L * n + 1))) :
    splitEquiv L n z = splitPair L n z := rfl
theorem splitEquiv_zero (L n : ℕ) :
    splitEquiv L n 0 = (0, 0) := by
  simp [splitEquiv_apply, splitPair, swLAddrReg_extractIndex_zero, swLFlagReg_extractIndex_zero]
/-! ## Real Matrix / Endomorphism / Unitary Combinators -/
/-- Matrix of a linear endomorphism on `EuclideanSpace ℝ (Fin D)` in the standard basis. -/
noncomputable def matOfEnd {D : ℕ}
    (T : EuclideanSpace ℝ (Fin D) →ₗ[ℝ] EuclideanSpace ℝ (Fin D)) :
    Matrix (Fin D) (Fin D) ℝ :=
  fun i j ↦ (T (PiLp.single 2 j 1)).ofLp i
theorem toLp_eq_sum_single {D : ℕ} (v : Fin D → ℝ) :
    WithLp.toLp 2 v = ∑ j : Fin D, v j • PiLp.single 2 j (1 : ℝ) := by
  ext i
  simp [Pi.single_apply]
theorem matOfEnd_mulVec {D : ℕ}
    (T : EuclideanSpace ℝ (Fin D) →ₗ[ℝ] EuclideanSpace ℝ (Fin D)) (v : Fin D → ℝ) :
    matOfEnd T *ᵥ v = fun i ↦ (T (WithLp.toLp 2 v)).ofLp i := by
  funext i
  rw [Matrix.mulVec, dotProduct, toLp_eq_sum_single v, map_sum]; simp [matOfEnd, mul_comm]
theorem matOfEnd_id (D : ℕ) :
    matOfEnd (LinearMap.id : EuclideanSpace ℝ (Fin D) →ₗ[ℝ] EuclideanSpace ℝ (Fin D)) = 1 := by
  ext i j
  simp [matOfEnd, Matrix.one_apply]
theorem matOfEnd_add {D : ℕ}
    (A B : EuclideanSpace ℝ (Fin D) →ₗ[ℝ] EuclideanSpace ℝ (Fin D)) :
    matOfEnd (A + B) = matOfEnd A + matOfEnd B := by
  ext i j; simp [matOfEnd]
theorem matOfEnd_sub {D : ℕ}
    (A B : EuclideanSpace ℝ (Fin D) →ₗ[ℝ] EuclideanSpace ℝ (Fin D)) :
    matOfEnd (A - B) = matOfEnd A - matOfEnd B := by
  ext i j; simp [matOfEnd]
theorem matOfEnd_smul {D : ℕ} (c : ℝ)
    (A : EuclideanSpace ℝ (Fin D) →ₗ[ℝ] EuclideanSpace ℝ (Fin D)) :
    matOfEnd (c • A) = c • matOfEnd A := by
  ext i j; simp [matOfEnd]
theorem matOfEnd_comp {D : ℕ}
    (A B : EuclideanSpace ℝ (Fin D) →ₗ[ℝ] EuclideanSpace ℝ (Fin D)) :
    matOfEnd (A.comp B) = matOfEnd A * matOfEnd B := by
  ext i j
  have hmv := congrFun (matOfEnd_mulVec A (fun k ↦ (B (PiLp.single 2 j 1)).ofLp k)) i
  simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, matOfEnd] using hmv.symm
theorem matOfEnd_adjoint {D : ℕ}
    (A : EuclideanSpace ℝ (Fin D) →ₗ[ℝ] EuclideanSpace ℝ (Fin D)) :
    matOfEnd (LinearMap.adjoint A) = (matOfEnd A)ᵀ := by
  ext i j
  have hadj : ⟪PiLp.single 2 i (1 : ℝ), LinearMap.adjoint A
      (PiLp.single 2 j (1 : ℝ))⟫ =
      ⟪A (PiLp.single 2 i (1 : ℝ)), PiLp.single 2 j (1 : ℝ)⟫ := by
    rw [LinearMap.adjoint_inner_right]
  simpa [PiLp.inner_apply, Pi.single_apply, matOfEnd, Matrix.transpose_apply]
    using hadj
/-- Lift a real orthogonal matrix `O` (`Oᵀ * O = 1`) to a `Unitary D`. -/
noncomputable def realOrthToUnitary {D : ℕ} (O : Matrix (Fin D) (Fin D) ℝ)
    (hO : Oᵀ * O = 1) : Unitary D :=
  ⟨O.map Complex.ofRealHom, by
    rw [Matrix.mem_unitaryGroup_iff']
    have hstar : star (O.map Complex.ofRealHom) = Oᵀ.map Complex.ofRealHom := by
      ext i j
      simp [Matrix.star_apply, Matrix.transpose_apply]
    rw [hstar, ← Matrix.map_mul]
    ext i j
    rw [hO]
    by_cases h : i = j <;> simp [Matrix.one_apply, h]⟩
theorem isRealMatrix_realOrthToUnitary {D : ℕ} (O : Matrix (Fin D) (Fin D) ℝ)
    (hO : Oᵀ * O = 1) :
    IsRealMatrix (realOrthToUnitary O hO).1 := by
  intro i j; simp [realOrthToUnitary]
theorem realOrthToUnitary_mulVec {D : ℕ} (O : Matrix (Fin D) (Fin D) ℝ)
    (hO : Oᵀ * O = 1) (v : Fin D → ℝ) :
    (realOrthToUnitary O hO).1 *ᵥ (fun i ↦ (v i : ℂ)) =
      fun i ↦ ((O *ᵥ v) i : ℂ) := by
  funext i
  simp [realOrthToUnitary, Matrix.mulVec, dotProduct]
/-- Rational Householder reflection sending `e₀` to an orthogonal unit vector `u` (`u 0 =
  0`). -/
def orthoSwapReflMat {D : ℕ} [NeZero D] (u : Fin D → ℝ) : Matrix (Fin D) (Fin D) ℝ :=
  let d : Fin D → ℝ := fun i ↦ (if i = 0 then 1 else 0) - u i
  1 - Matrix.of fun i j ↦ d i * d j
theorem orthoSwapReflMat_orth {D : ℕ} [NeZero D] {u : Fin D → ℝ}
    (hu0 : u 0 = 0) (hunorm : ∑ i : Fin D, u i ^ 2 = 1) :
    (orthoSwapReflMat u)ᵀ * orthoSwapReflMat u = 1 := by
  set d : Fin D → ℝ := fun i ↦ (if i = 0 then 1 else 0) - u i
  set M : Matrix (Fin D) (Fin D) ℝ := Matrix.of fun i j ↦ d i * d j
  have hdef : orthoSwapReflMat u = 1 - M := rfl
  have hMsym : Mᵀ = M := by ext i j; simp [M, mul_comm]
  have hsym : (orthoSwapReflMat u)ᵀ = orthoSwapReflMat u := by
    rw [hdef, Matrix.transpose_sub, Matrix.transpose_one, hMsym]
  have hdd : ∑ k : Fin D, d k * d k = 2 := by
    have hsplit : ∀ k : Fin D, d k * d k =
        (if k = 0 then (1 : ℝ) else 0) + u k ^ 2 := by
      intro k
      by_cases hk : k = 0
      · subst hk; simp [d, hu0]
      · simp [d, hk, sq]
    simp_rw [hsplit]; rw [Finset.sum_add_distrib]
    have hs1 : ∑ k : Fin D, (if k = 0 then (1 : ℝ) else 0) = 1 := by simp
    linarith
  have hMM : M * M = (2 : ℝ) • M := by
    ext i j
    simp only [M, Matrix.mul_apply, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
    calc ∑ k : Fin D, d i * d k * (d k * d j)
        = d i * d j * ∑ k : Fin D, d k * d k := by
            rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun k _ ↦ by ring
      _ = 2 * (d i * d j) := by rw [hdd]; ring
  rw [hsym, hdef, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
    Matrix.one_mul, hMM]
  ext i j
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]; ring
theorem orthoSwapReflMat_mulVec_e0 {D : ℕ} [NeZero D] {u : Fin D → ℝ} (hu0 : u 0 = 0) :
    orthoSwapReflMat u *ᵥ Pi.single 0 1 = u := by
  funext i
  simp only [orthoSwapReflMat, Matrix.mulVec, dotProduct, Pi.single_apply]
  rw [Finset.sum_eq_single 0
    (fun k _ hk ↦ by simp [Matrix.sub_apply, Matrix.one_apply, hk])
    (by simp)]
  simp only [Matrix.sub_apply, Matrix.one_apply, Matrix.of_apply, ↓reduceIte, mul_one]
  by_cases hi : i = 0
  · subst hi; simp [hu0]
  · simp [hi, hu0]
/-- Reflection `2 • P - 1` across a real symmetric idempotent matrix `P`. -/
def symProjReflMat {D : ℕ} (P : Matrix (Fin D) (Fin D) ℝ) : Matrix (Fin D) (Fin D) ℝ :=
  (2 : ℝ) • P - 1
theorem symProjReflMat_orth {D : ℕ} {P : Matrix (Fin D) (Fin D) ℝ}
    (hsym : Pᵀ = P) (hidem : P * P = P) :
    (symProjReflMat P)ᵀ * symProjReflMat P = 1 := by
  have hts : (symProjReflMat P)ᵀ = symProjReflMat P := by
    simp [symProjReflMat, Matrix.transpose_sub, Matrix.transpose_smul, hsym]
  rw [hts]
  calc ((2 : ℝ) • P - 1) * ((2 : ℝ) • P - 1)
      = (4 : ℝ) • (P * P) - (4 : ℝ) • P + 1 := by
        ext i j
        simp [Matrix.sub_mul, Matrix.mul_sub]; ring
    _ = 1 := by rw [hidem, sub_self, zero_add]
/-- Cayley `SO(2)` rotation `(1 - P_+ - P_-) + c • (P_+ + P_-) + s • (K - Kᵀ)`. -/
def partialIsomRotMat {D : ℕ} (P₁ P₂ K : Matrix (Fin D) (Fin D) ℝ) (c s : ℝ) :
    Matrix (Fin D) (Fin D) ℝ :=
  (1 - P₁ - P₂) + c • (P₁ + P₂) + s • (K - Kᵀ)
theorem partialIsomRotMat_orth {D : ℕ} {P₁ P₂ K : Matrix (Fin D) (Fin D) ℝ} {c s : ℝ}
    (hP1s : P₁ᵀ = P₁) (hP2s : P₂ᵀ = P₂)
    (hK1 : Kᵀ * K = P₁) (hK2 : K * Kᵀ = P₂)
    (hKP1 : K * P₁ = K) (hP2K : P₂ * K = K)
    (h12 : P₁ * P₂ = 0) (hcs : c ^ 2 + s ^ 2 = 1) :
    (partialIsomRotMat P₁ P₂ K c s)ᵀ * partialIsomRotMat P₁ P₂ K c s = 1 := by
  have h21 : P₂ * P₁ = 0 := by
    calc P₂ * P₁ = P₂ᵀ * P₁ᵀ := by rw [hP2s, hP1s]
      _ = (P₁ * P₂)ᵀ := (Matrix.transpose_mul P₁ P₂).symm
      _ = 0 := by rw [h12, Matrix.transpose_zero]
  have hP1Kt : P₁ * Kᵀ = Kᵀ := by
    calc P₁ * Kᵀ = (K * P₁ᵀ)ᵀ := (Matrix.transpose_mul K P₁ᵀ).symm
      _ = Kᵀ := by rw [hP1s, hKP1]
  have hKtP2 : Kᵀ * P₂ = Kᵀ := by
    calc Kᵀ * P₂ = (P₂ᵀ * K)ᵀ := (Matrix.transpose_mul P₂ᵀ K).symm
      _ = Kᵀ := by rw [hP2s, hP2K]
  have hP1i : P₁ * P₁ = P₁ := by
    calc P₁ * P₁ = P₁ * (Kᵀ * K) := by rw [hK1]
      _ = (P₁ * Kᵀ) * K := (Matrix.mul_assoc P₁ Kᵀ K).symm
      _ = P₁ := by rw [hP1Kt, hK1]
  have hP2i : P₂ * P₂ = P₂ := by
    calc P₂ * P₂ = (K * Kᵀ) * P₂ := by rw [hK2]
      _ = K * (Kᵀ * P₂) := Matrix.mul_assoc K Kᵀ P₂
      _ = P₂ := by rw [hKtP2, hK2]
  have hKK : K * K = 0 := by
    calc K * K = (K * P₁) * (P₂ * K) := by rw [hKP1, hP2K]
      _ = K * (P₁ * P₂) * K := by simp [Matrix.mul_assoc]
      _ = 0 := by rw [h12]; simp
  have hKtKt : Kᵀ * Kᵀ = 0 := by rw [← Matrix.transpose_mul, hKK, Matrix.transpose_zero]
  have hP1K : P₁ * K = 0 := by
    calc P₁ * K = P₁ * (P₂ * K) := by rw [hP2K]
      _ = (P₁ * P₂) * K := (Matrix.mul_assoc P₁ P₂ K).symm
      _ = 0 := by rw [h12, Matrix.zero_mul]
  have hKP2 : K * P₂ = 0 := by
    calc K * P₂ = (K * P₁) * P₂ := by rw [hKP1]
      _ = K * (P₁ * P₂) := Matrix.mul_assoc K P₁ P₂
      _ = 0 := by rw [h12, Matrix.mul_zero]
  have hKtP1 : Kᵀ * P₁ = 0 := by
    calc Kᵀ * P₁ = (P₁ᵀ * K)ᵀ := (Matrix.transpose_mul P₁ᵀ K).symm
      _ = 0 := by rw [hP1s, hP1K, Matrix.transpose_zero]
  have hP2Kt : P₂ * Kᵀ = 0 := by
    calc P₂ * Kᵀ = (K * P₂ᵀ)ᵀ := (Matrix.transpose_mul K P₂ᵀ).symm
      _ = 0 := by rw [hP2s, hKP2, Matrix.transpose_zero]
  set Q := P₁ + P₂; set R := (1 : Matrix (Fin D) (Fin D) ℝ) - Q; set A := K - Kᵀ
  have hQ_idem : Q * Q = Q := by simp [Q, Matrix.add_mul, Matrix.mul_add, hP1i, hP2i, h12, h21]
  have hR_idem : R * R = R := by simp [R, Matrix.sub_mul, Matrix.mul_sub, hQ_idem]
  have hRQ : R * Q = 0 := by simp [R, Matrix.sub_mul, hQ_idem]
  have hQR : Q * R = 0 := by simp [R, Matrix.mul_sub, hQ_idem]
  have hQA : Q * A = A := by
    simp only [Q, A, Matrix.add_mul, Matrix.mul_sub, hP1K, hP2K, hP1Kt, hP2Kt]; abel
  have hAQ : A * Q = A := by
    simp only [Q, A, Matrix.mul_add, Matrix.sub_mul, hKP1, hKP2, hKtP1, hKtP2]; abel
  have hRA : R * A = 0 := by simp [R, Matrix.sub_mul, hQA]
  have hAR : A * R = 0 := by simp [R, Matrix.mul_sub, hAQ]
  have hAA : A * A = -Q := by
    calc A * A = K * K - K * Kᵀ - Kᵀ * K + Kᵀ * Kᵀ := by
          simp [A, Matrix.sub_mul, Matrix.mul_sub]; abel
      _ = -Q := by rw [hKK, hK2, hK1, hKtKt]; simp [Q]; abel
  have hQt : Qᵀ = Q := by simp [Q, hP1s, hP2s]
  have hRt : Rᵀ = R := by simp [R, hQt]
  have hAt : Aᵀ = -A := by simp only [A, Matrix.transpose_sub, Matrix.transpose_transpose]; abel
  have hdef : partialIsomRotMat P₁ P₂ K c s = R + c • Q + s • A := by
    simp [partialIsomRotMat, R, Q, A, sub_sub]
  rw [hdef, Matrix.transpose_add, Matrix.transpose_add, hRt, Matrix.transpose_smul, hQt,
    Matrix.transpose_smul, hAt]
  ext i j
  have hexp : ((R + c • Q + s • -A) * (R + c • Q + s • A)) i j =
      (R + (c ^ 2 + s ^ 2) • Q) i j := by
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.neg_mul, smul_neg, hR_idem, hRQ, hRA, hQR, hQ_idem, hQA, hAR, hAQ, hAA,
      Matrix.add_apply, Matrix.smul_apply, Matrix.neg_apply, Matrix.zero_apply]
    ring
  rw [hexp, hcs, one_smul]; simp [R]
/-- Lift `O` on `addr` with identity on `flag` via `splitEquiv L n`. -/
noncomputable def liftAddrMat (L n : ℕ)
    (O : Matrix (Fin (2 ^ (L * n))) (Fin (2 ^ (L * n))) ℝ) :
    Matrix (Fin (2 ^ (L * n + 1))) (Fin (2 ^ (L * n + 1))) ℝ :=
  fun z₁ z₂ ↦
    let p₁ := splitEquiv L n z₁
    let p₂ := splitEquiv L n z₂
    if p₁.2 = p₂.2 then O p₁.1 p₂.1 else 0
theorem liftAddrMat_transpose (L n : ℕ)
    (O : Matrix (Fin (2 ^ (L * n))) (Fin (2 ^ (L * n))) ℝ) :
    (liftAddrMat L n O)ᵀ = liftAddrMat L n Oᵀ := by
  ext z₁ z₂
  simp only [liftAddrMat, Matrix.transpose_apply]
  by_cases h : (splitEquiv L n z₁).2 = (splitEquiv L n z₂).2
  · simp [h]
  · have h' : (splitEquiv L n z₂).2 ≠ (splitEquiv L n z₁).2 := Ne.symm h; simp [h, h']
theorem liftAddrMat_one (L n : ℕ) :
    liftAddrMat L n 1 = 1 := by
  ext z₁ z₂
  simp only [liftAddrMat, Matrix.one_apply]
  by_cases h : z₁ = z₂
  · subst h; simp
  · have hp : splitEquiv L n z₁ ≠ splitEquiv L n z₂ :=
      fun heq ↦ h ((splitEquiv L n).injective heq)
    by_cases hf : (splitEquiv L n z₁).2 = (splitEquiv L n z₂).2
    · have ha : (splitEquiv L n z₁).1 ≠ (splitEquiv L n z₂).1 :=
        fun ha ↦ hp (Prod.ext ha hf)
      simp [hf, ha, h]
    · simp [hf, h]
theorem liftAddrMat_mul (L n : ℕ)
    (A B : Matrix (Fin (2 ^ (L * n))) (Fin (2 ^ (L * n))) ℝ) :
    liftAddrMat L n A * liftAddrMat L n B = liftAddrMat L n (A * B) := by
  ext z₁ z₂
  rw [Matrix.mul_apply,
    ← (splitEquiv L n).symm.sum_comp (fun j ↦ liftAddrMat L n A z₁ j * liftAddrMat L n B j z₂)]
  simp only [liftAddrMat, Equiv.apply_symm_apply, Fintype.sum_prod_type]
  by_cases hf : (splitEquiv L n z₁).2 = (splitEquiv L n z₂).2
  · simp only [hf, ↓reduceIte, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    rw [Finset.sum_eq_single (splitEquiv L n z₂).2
      (fun f _ hne ↦ by simp [hne.symm]) (by simp)]
    simp
  · simp only [hf, ↓reduceIte]
    refine Finset.sum_eq_zero fun a _ ↦ Finset.sum_eq_zero fun f _ ↦ ?_
    by_cases h1 : (splitEquiv L n z₁).2 = f
    · have h2 : f ≠ (splitEquiv L n z₂).2 := fun h2 ↦ hf (h1.trans h2)
      simp [h1, h2]
    · simp [h1]
theorem liftAddrMat_orth (L n : ℕ)
    {O : Matrix (Fin (2 ^ (L * n))) (Fin (2 ^ (L * n))) ℝ} (hO : Oᵀ * O = 1) :
    (liftAddrMat L n O)ᵀ * liftAddrMat L n O = 1 := by
  rw [liftAddrMat_transpose, liftAddrMat_mul, hO, liftAddrMat_one]
theorem listProd_orth {D : ℕ} :
    ∀ (l : List (Matrix (Fin D) (Fin D) ℝ)),
      (∀ M ∈ l, Mᵀ * M = 1) → l.prodᵀ * l.prod = 1
  | [], _ => by simp
  | M :: tl, hl => by
      have hM : Mᵀ * M = 1 := hl M List.mem_cons_self
      have htl : tl.prodᵀ * tl.prod = 1 :=
        listProd_orth tl (fun N hN ↦ hl N (List.mem_cons_of_mem M hN))
      rw [List.prod_cons, Matrix.transpose_mul, Matrix.mul_assoc,
        ← Matrix.mul_assoc Mᵀ M tl.prod, hM, Matrix.one_mul, htl]
/-- Embed an address-register real vector on `flag = 0` inside `Fin (2 ^ (L * n + 1))`. -/
noncomputable def embedAddr0 (L n : ℕ) (v : Fin (2 ^ (L * n)) → ℝ) :
    Fin (2 ^ (L * n + 1)) → ℝ :=
  fun z ↦ if (splitEquiv L n z).2 = 0 then v (splitEquiv L n z).1 else 0
/-- Embed an address-register real vector on `flag = 1` inside `Fin (2 ^ (L * n + 1))`. -/
noncomputable def embedAddr1 (L n : ℕ) (v : Fin (2 ^ (L * n)) → ℝ) :
    Fin (2 ^ (L * n + 1)) → ℝ :=
  fun z ↦ if (splitEquiv L n z).2 = 1 then v (splitEquiv L n z).1 else 0
theorem embedAddr0_single_zero (L n : ℕ) :
    embedAddr0 L n (Pi.single 0 1) = Pi.single 0 1 := by
  funext z
  simp only [embedAddr0, Pi.single_apply]
  by_cases hz : z = 0
  · subst hz; simp [splitEquiv_zero]
  · by_cases hf : (splitEquiv L n z).2 = 0
    · have ha : (splitEquiv L n z).1 ≠ 0 := fun ha ↦
        hz ((splitEquiv L n).injective ((Prod.ext ha hf).trans (splitEquiv_zero L n).symm))
      simp [hf, ha, hz]
    · simp [hf, hz]
theorem liftAddrMat_mulVec_embedAddr0 (L n : ℕ)
    (O : Matrix (Fin (2 ^ (L * n))) (Fin (2 ^ (L * n))) ℝ) (v : Fin (2 ^ (L * n)) → ℝ) :
    liftAddrMat L n O *ᵥ embedAddr0 L n v = embedAddr0 L n (O *ᵥ v) := by
  funext z
  rw [Matrix.mulVec, dotProduct,
    ← (splitEquiv L n).symm.sum_comp (fun i ↦ liftAddrMat L n O z i * embedAddr0 L n v i)]
  simp only [liftAddrMat, embedAddr0, Equiv.apply_symm_apply, Fintype.sum_prod_type]
  by_cases hf : (splitEquiv L n z).2 = 0
  · simp only [hf, ↓reduceIte, Matrix.mulVec, dotProduct]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    rw [Finset.sum_eq_single 0 (fun f _ hne ↦ by simp [hne]) (by simp)]
    simp
  · simp only [hf, ↓reduceIte]
    refine Finset.sum_eq_zero fun a _ ↦ Finset.sum_eq_zero fun f _ ↦ ?_
    by_cases hf0 : f = 0
    · subst hf0; simp [hf]
    · simp [hf0]
/-- Weak-measurement flag rotation coupled to symmetric idempotent `P` on `Fin (2 ^ (L *
  n))`. -/
noncomputable def weakFlagMat (L n : ℕ)
    (P : Matrix (Fin (2 ^ (L * n))) (Fin (2 ^ (L * n))) ℝ) (c s : ℝ) :
    Matrix (Fin (2 ^ (L * n + 1))) (Fin (2 ^ (L * n + 1))) ℝ :=
  fun z₁ z₂ ↦
    let p₁ := splitEquiv L n z₁
    let p₂ := splitEquiv L n z₂
    match p₁.2.1, p₂.2.1 with
    | 0, 0 => ((1 - P) + c • P) p₁.1 p₂.1
    | 0, _ => (-s • P) p₁.1 p₂.1
    | _, 0 => (s • P) p₁.1 p₂.1
    | _, _ => ((1 - P) + c • P) p₁.1 p₂.1
theorem weakFlagMat_orth (L n : ℕ)
    {P : Matrix (Fin (2 ^ (L * n))) (Fin (2 ^ (L * n))) ℝ} {c s : ℝ}
    (hPs : Pᵀ = P) (hPi : P * P = P) (hcs : c ^ 2 + s ^ 2 = 1) :
    (weakFlagMat L n P c s)ᵀ * weakFlagMat L n P c s = 1 := by
  set D := (1 - P) + c • P
  have hDs : Dᵀ = D := by simp [D, hPs]
  have hDt : ∀ a b, D a b = D b a := fun a b ↦ by
    simpa [Matrix.transpose_apply] using congrFun (congrFun hDs b) a
  have hPt : ∀ a b, P a b = P b a := fun a b ↦ by
    simpa [Matrix.transpose_apply] using congrFun (congrFun hPs b) a
  have hDD : D * D + (s • P) * (s • P) = 1 := by
    ext a b
    have h1 : (D * D + (s • P) * (s • P)) a b = ((1 - P) + (c ^ 2 + s ^ 2) • P) a b := by
      simp only [D, Matrix.add_mul, Matrix.mul_add, Matrix.sub_mul, Matrix.mul_sub,
        Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, hPi, smul_smul,
        Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply]
      ring
    rw [h1, hcs, one_smul, sub_add_cancel]
  have hDP : D * P = c • P := by
    calc D * P = (1 - P) * P + (c • P) * P := Matrix.add_mul (1 - P) (c • P) P
      _ = (P - P * P) + c • (P * P) := by rw [Matrix.sub_mul, Matrix.one_mul, Matrix.smul_mul]
      _ = c • P := by rw [hPi, sub_self, zero_add]
  have hPD : P * D = c • P := by
    calc P * D = P * (1 - P) + P * (c • P) := Matrix.mul_add P (1 - P) (c • P)
      _ = (P - P * P) + c • (P * P) := by rw [Matrix.mul_sub, Matrix.mul_one, Matrix.mul_smul]
      _ = c • P := by rw [hPi, sub_self, zero_add]
  ext z₁ z₂
  rw [Matrix.mul_apply, ← (splitEquiv L n).symm.sum_comp
    (fun j ↦ (weakFlagMat L n P c s)ᵀ z₁ j * weakFlagMat L n P c s j z₂)]
  simp only [Matrix.transpose_apply, weakFlagMat, Equiv.apply_symm_apply, Fintype.sum_prod_type,
    Fin.sum_univ_two, Fin.val_zero, Fin.val_one]
  set p₁ := splitEquiv L n z₁; set p₂ := splitEquiv L n z₂
  have hf1 : p₁.2 = 0 ∨ p₁.2 = 1 := by generalize p₁.2 = b; fin_cases b <;> simp
  have hf2 : p₂.2 = 0 ∨ p₂.2 = 1 := by generalize p₂.2 = b; fin_cases b <;> simp
  rcases hf1 with h1 | h1 <;> rcases hf2 with h2 | h2
  · simp only [h1, h2, Fin.val_zero]; have hrow := congrFun (congrFun hDD p₁.1) p₂.1
    simp only [Matrix.add_apply, Matrix.mul_apply] at hrow
    have hlhs : (∑ x, (D x p₁.1 * D x p₂.1 + (s • P) x p₁.1 * (s • P) x p₂.1)) =
        (∑ x, D p₁.1 x * D x p₂.1) + ∑ x, (s • P) p₁.1 x * (s • P) x p₂.1 := by
      rw [Finset.sum_add_distrib]
      congr 1 <;> refine Finset.sum_congr rfl fun x _ ↦ by
        simp [Matrix.smul_apply, hDt x p₁.1, hPt x p₁.1]
    rw [hlhs, hrow, Matrix.one_apply, Matrix.one_apply]
    by_cases hz : z₁ = z₂
    · have ha : p₁.1 = p₂.1 := congrArg (fun z ↦ (splitEquiv L n z).1) hz
      simp [hz, ha]
    · have ha : p₁.1 ≠ p₂.1 := fun ha ↦
        hz ((splitEquiv L n).injective (Prod.ext ha (h1.trans h2.symm)))
      simp [hz, ha]
  · simp only [h1, h2, Fin.val_zero, Fin.val_one]
    have hz : z₁ ≠ z₂ := fun hz ↦ by
      have := congrArg (fun z ↦ (splitEquiv L n z).2) hz
      dsimp only [p₁, p₂] at h1 h2; rw [h1, h2] at this; cases congrArg Fin.val this
    simp only [Matrix.one_apply, hz, ↓reduceIte]; have h1' := congrFun (congrFun hDP p₁.1) p₂.1
    have h2' := congrFun (congrFun hPD p₁.1) p₂.1
    simp only [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul] at h1' h2'
    have hlhs : (∑ x, (D x p₁.1 * (-s • P) x p₂.1 + (s • P) x p₁.1 * D x p₂.1)) =
        -s * (∑ x, D p₁.1 x * P x p₂.1) + s * ∑ x, P p₁.1 x * D x p₂.1 := by
      rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]; congr 1
      · refine Finset.sum_congr rfl fun x _ ↦ ?_
        simp only [hDt x p₁.1, Matrix.smul_apply, smul_eq_mul]; ring
      · refine Finset.sum_congr rfl fun x _ ↦ ?_
        simp only [hPt x p₁.1, Matrix.smul_apply, smul_eq_mul]; ring
    rw [hlhs, h1', h2']; ring
  · simp only [h1, h2, Fin.val_zero, Fin.val_one]
    have hz : z₁ ≠ z₂ := fun hz ↦ by
      have := congrArg (fun z ↦ (splitEquiv L n z).2) hz
      dsimp only [p₁, p₂] at h1 h2; rw [h1, h2] at this; cases congrArg Fin.val this
    simp only [Matrix.one_apply, hz, ↓reduceIte]; have h1' := congrFun (congrFun hPD p₁.1) p₂.1
    have h2' := congrFun (congrFun hDP p₁.1) p₂.1
    simp only [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul] at h1' h2'
    have hlhs : (∑ x, ((-s • P) x p₁.1 * D x p₂.1 + D x p₁.1 * (s • P) x p₂.1)) =
        -s * (∑ x, P p₁.1 x * D x p₂.1) + s * ∑ x, D p₁.1 x * P x p₂.1 := by
      rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]; congr 1
      · refine Finset.sum_congr rfl fun x _ ↦ ?_
        simp only [hPt x p₁.1, Matrix.smul_apply, smul_eq_mul]; ring
      · refine Finset.sum_congr rfl fun x _ ↦ ?_
        simp only [hDt x p₁.1, Matrix.smul_apply, smul_eq_mul]; ring
    rw [hlhs, h1', h2']; ring
  · simp only [h1, h2, Fin.val_one]; have hrow := congrFun (congrFun hDD p₁.1) p₂.1
    simp only [Matrix.add_apply, Matrix.mul_apply] at hrow
    have hlhs : (∑ x, ((-s • P) x p₁.1 * (-s • P) x p₂.1 + D x p₁.1 * D x p₂.1)) =
        (∑ x, D p₁.1 x * D x p₂.1) + ∑ x, (s • P) p₁.1 x * (s • P) x p₂.1 := by
      rw [Finset.sum_add_distrib, add_comm]; congr 1
      · refine Finset.sum_congr rfl fun x _ ↦ by simp [hDt x p₁.1]
      · refine Finset.sum_congr rfl fun x _ ↦ by
          simp only [hPt x p₁.1, Matrix.smul_apply, smul_eq_mul]; ring
    rw [hlhs, hrow, Matrix.one_apply, Matrix.one_apply]
    by_cases hz : z₁ = z₂
    · have ha : p₁.1 = p₂.1 := congrArg (fun z ↦ (splitEquiv L n z).1) hz
      simp [hz, ha]
    · have ha : p₁.1 ≠ p₂.1 := fun ha ↦
        hz ((splitEquiv L n).injective (Prod.ext ha (h1.trans h2.symm)))
      simp [hz, ha]
theorem weakFlagMat_mulVec_embedAddr0 (L n : ℕ)
    (P : Matrix (Fin (2 ^ (L * n))) (Fin (2 ^ (L * n))) ℝ) (c s : ℝ)
    (v : Fin (2 ^ (L * n)) → ℝ) :
    weakFlagMat L n P c s *ᵥ embedAddr0 L n v =
      embedAddr0 L n (((1 - P) + c • P) *ᵥ v) + embedAddr1 L n ((s • P) *ᵥ v) := by
  funext z
  rw [Matrix.mulVec, dotProduct,
    ← (splitEquiv L n).symm.sum_comp (fun i ↦ weakFlagMat L n P c s z i * embedAddr0 L n v i)]
  simp only [weakFlagMat, embedAddr0, embedAddr1, Equiv.apply_symm_apply, Fintype.sum_prod_type,
    Fin.sum_univ_two, Fin.val_zero, Fin.val_one, Pi.add_apply]
  set p := splitEquiv L n z
  have h01 : (0 : Fin 2) ≠ 1 := fun h ↦ by cases congrArg Fin.val h
  have h10 : (1 : Fin 2) ≠ 0 := fun h ↦ by cases congrArg Fin.val h
  have hpf : p.2 = 0 ∨ p.2 = 1 := by generalize p.2 = b; fin_cases b <;> simp
  rcases hpf with hf | hf
  · simp only [hf, h01, h10, Fin.val_zero, ↓reduceIte, mul_zero, add_zero, Matrix.mulVec,
      dotProduct]
  · simp only [hf, h10, Fin.val_one, ↓reduceIte, mul_zero, add_zero, zero_add, Matrix.mulVec,
      dotProduct]
theorem slotOracle_mulVec (L n : ℕ) (i : Fin L) (R : Finset (Fin (2 ^ n)))
    (ψ : Fin (2 ^ (L * n + 1)) → ℂ) :
    ((swLSlotReg L n i).embedUnitary (swLSetOracleUnitary R)).1 *ᵥ ψ =
      fun z ↦ (if (swLSlotReg L n i).extractIndex z ∈ R then (-1 : ℂ) else 1) * ψ z := by
  funext z
  change ((swLSlotReg L n i).embedMatrix (setOracleMatrix R) *ᵥ ψ) z = _
  rw [(swLSlotReg L n i).embedMatrix_mulVec_apply]
  rw [Finset.sum_eq_single ((swLSlotReg L n i).extractIndex z)
    (fun x _ hx ↦ by simp [setOracleMatrix, hx.symm])
    (by simp)]
  have hrep : (swLSlotReg L n i).basisSplitEquiv.symm
      ((swLSlotReg L n i).extractIndex z, ((swLSlotReg L n i).basisSplitEquiv z).2) = z :=
    (swLSlotReg L n i).replaceIndex_extractIndex z
  rw [hrep]; simp [setOracleMatrix]
/-- Harmonic subspace on `w`-subsets of `Fin N`: supported on `s.card = w` and killed by
  `(w - 1)`-subset incidence sums. -/
def harmonicSubspace (N w : ℕ) : Submodule ℝ (EuclideanSpace ℝ (Finset (Fin N))) where
  carrier := {f | (∀ s : Finset (Fin N), s.card ≠ w → f.ofLp s = 0) ∧
    (1 ≤ w → ∀ a : Finset (Fin N), a.card = w - 1 →
      ∑ y ∈ Finset.univ \ a, f.ofLp (insert y a) = 0)}
  zero_mem' := by simp
  add_mem' {f g} hf hg := by
    refine ⟨fun s hs ↦ by simp [hf.1 s hs, hg.1 s hs], fun hw a ha ↦ ?_⟩
    simp [Finset.sum_add_distrib, hf.2 hw a ha, hg.2 hw a ha]
  smul_mem' c {f} hf := by
    refine ⟨fun s hs ↦ by simp [hf.1 s hs], fun hw a ha ↦ ?_⟩
    simp [← Finset.mul_sum, hf.2 hw a ha]
theorem sum_powersetCard_insert {α : Type*} [DecidableEq α] (U : Finset α) (k : ℕ)
    (F : Finset α → ℝ) :
    (∑ B₀ ∈ U.powersetCard k, ∑ y ∈ U \ B₀, F (insert y B₀)) =
      ((k + 1 : ℕ) : ℝ) * ∑ B' ∈ U.powersetCard (k + 1), F B' := by
  have hrhs : ((k + 1 : ℕ) : ℝ) * (∑ B' ∈ U.powersetCard (k + 1), F B') =
      ∑ B' ∈ U.powersetCard (k + 1), ∑ _y ∈ B', F B' := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun B' hB' ↦ ?_
    have hc : B'.card = k + 1 := (Finset.mem_powersetCard.1 hB').2
    simp [Finset.sum_const, hc, nsmul_eq_mul]
  have hs1 : (∑ B₀ ∈ U.powersetCard k, ∑ y ∈ U \ B₀, F (insert y B₀)) =
      ∑ p ∈ (U.powersetCard k).sigma (fun B₀ ↦ U \ B₀), F (insert p.2 p.1) :=
    (Finset.sum_sigma (U.powersetCard k) (fun B₀ ↦ U \ B₀) (fun p ↦ F (insert p.2 p.1))).symm
  have hs2 : (∑ B' ∈ U.powersetCard (k + 1), ∑ _y ∈ B', F B') =
      ∑ q ∈ (U.powersetCard (k + 1)).sigma (fun B' ↦ B'), F q.1 :=
    (Finset.sum_sigma (U.powersetCard (k + 1)) (fun B' ↦ B') (fun q ↦ F q.1)).symm
  rw [hrhs, hs1, hs2]
  refine Finset.sum_nbij' (fun p ↦ ⟨insert p.2 p.1, p.2⟩) (fun q ↦ ⟨q.1.erase q.2, q.2⟩)
    (fun p hp ↦ ?_) (fun q hq ↦ ?_) (fun p hp ↦ ?_) (fun q hq ↦ ?_) (fun _ _ ↦ rfl)
  · rcases Finset.mem_sigma.1 hp with ⟨hB, hy⟩
    rcases Finset.mem_powersetCard.1 hB with ⟨hBU, hcB⟩
    rcases Finset.mem_sdiff.1 hy with ⟨hyU, hyB⟩
    refine Finset.mem_sigma.2 ⟨Finset.mem_powersetCard.2 ⟨?_, ?_⟩, Finset.mem_insert_self _ _⟩
    · exact Finset.insert_subset_iff.2 ⟨hyU, hBU⟩
    · rw [Finset.card_insert_of_notMem hyB, hcB]
  · rcases Finset.mem_sigma.1 hq with ⟨hB', hy⟩
    rcases Finset.mem_powersetCard.1 hB' with ⟨hB'U, hcB'⟩
    refine Finset.mem_sigma.2 ⟨Finset.mem_powersetCard.2 ⟨?_, ?_⟩, ?_⟩
    · exact (Finset.erase_subset q.2 q.1).trans hB'U
    · rw [Finset.card_erase_of_mem hy, hcB', Nat.add_sub_cancel]
    · exact Finset.mem_sdiff.2 ⟨hB'U hy, Finset.notMem_erase q.2 q.1⟩
  · rcases Finset.mem_sigma.1 hp with ⟨_, hy⟩
    rcases Finset.mem_sdiff.1 hy with ⟨_, hyB⟩
    ext <;> simp [Finset.erase_insert hyB]
  · rcases Finset.mem_sigma.1 hq with ⟨_, hy⟩
    ext <;> simp [Finset.insert_erase hy]
theorem sum_harmonic_compl_powersetCard {N w : ℕ} (hw : 1 ≤ w)
    {g : EuclideanSpace ℝ (Finset (Fin N))} (hg : g ∈ harmonicSubspace N w)
    {S₁ I : Finset (Fin N)} (hIS : I ⊆ S₁) (hIw : I.card ≤ w) :
    (∑ J ∈ (Finset.univ \ S₁).powersetCard (w - I.card), g.ofLp (I ∪ J)) =
      (-1 : ℝ) ^ (w - I.card) *
        ∑ B ∈ (S₁ \ I).powersetCard (w - I.card), g.ofLp (I ∪ B) := by
  set m := w - I.card
  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
  · simp [hm0]
  · let Ψ : ℕ → ℝ := fun k ↦
      ∑ B ∈ (S₁ \ I).powersetCard k,
        ∑ C ∈ (Finset.univ \ S₁).powersetCard (m - k), g.ofLp (I ∪ B ∪ C)
    have hstep : ∀ k < m,
        ((m - k : ℕ) : ℝ) * Ψ k + ((k + 1 : ℕ) : ℝ) * Ψ (k + 1) = 0 := by
      intro k hk
      have hzero : ∑ B₀ ∈ (S₁ \ I).powersetCard k,
          ∑ C₀ ∈ (Finset.univ \ S₁).powersetCard (m - 1 - k),
            ∑ y ∈ Finset.univ \ (I ∪ B₀ ∪ C₀), g.ofLp (insert y (I ∪ B₀ ∪ C₀)) = 0 := by
        refine Finset.sum_eq_zero fun B₀ hB₀ ↦ Finset.sum_eq_zero fun C₀ hC₀ ↦ ?_
        rcases Finset.mem_powersetCard.1 hB₀ with ⟨hB₀sub, hcB₀⟩
        rcases Finset.mem_powersetCard.1 hC₀ with ⟨hC₀sub, hcC₀⟩
        have hIB : Disjoint I B₀ := Disjoint.mono_right hB₀sub disjoint_sdiff_self_right
        have hIBC : Disjoint (I ∪ B₀) C₀ := by
          refine Disjoint.mono_right hC₀sub ?_
          have hsub : I ∪ B₀ ⊆ S₁ :=
            Finset.union_subset hIS (hB₀sub.trans Finset.sdiff_subset)
          exact Disjoint.mono_left hsub disjoint_sdiff_self_right
        have hcard : (I ∪ B₀ ∪ C₀).card = w - 1 := by
          rw [Finset.card_union_of_disjoint hIBC, Finset.card_union_of_disjoint hIB, hcB₀, hcC₀]
          omega
        exact hg.2 hw _ hcard
      have hsplit : ∀ B₀ ∈ (S₁ \ I).powersetCard k,
          ∀ C₀ ∈ (Finset.univ \ S₁).powersetCard (m - 1 - k),
            (∑ y ∈ Finset.univ \ (I ∪ B₀ ∪ C₀), g.ofLp (insert y (I ∪ B₀ ∪ C₀))) =
              (∑ y ∈ (S₁ \ I) \ B₀, g.ofLp (I ∪ insert y B₀ ∪ C₀)) +
                ∑ y ∈ (Finset.univ \ S₁) \ C₀, g.ofLp (I ∪ B₀ ∪ insert y C₀) := by
        intro B₀ hB₀ C₀ hC₀; have hB₀sub : B₀ ⊆ S₁ \ I := (Finset.mem_powersetCard.1 hB₀).1
        have hC₀sub : C₀ ⊆ Finset.univ \ S₁ := (Finset.mem_powersetCard.1 hC₀).1
        have hunion : Finset.univ \ (I ∪ B₀ ∪ C₀) =
            ((S₁ \ I) \ B₀) ∪ ((Finset.univ \ S₁) \ C₀) := by
          ext y
          simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_univ, true_and]
          have hISy : y ∈ I → y ∈ S₁ := fun hy ↦ hIS hy
          have hBSy : y ∈ B₀ → y ∈ S₁ := fun hy ↦ (Finset.mem_sdiff.1 (hB₀sub hy)).1
          have hCSy : y ∈ C₀ → y ∉ S₁ := fun hy ↦ (Finset.mem_sdiff.1 (hC₀sub hy)).2
          tauto
        have hdisj : Disjoint ((S₁ \ I) \ B₀) ((Finset.univ \ S₁) \ C₀) := by
          rw [Finset.disjoint_left]; intro y hy1 hy2
          exact (Finset.mem_sdiff.1 (Finset.mem_sdiff.1 hy2).1).2
            (Finset.mem_sdiff.1 (Finset.mem_sdiff.1 hy1).1).1
        rw [hunion, Finset.sum_union hdisj]; congr 1
        · refine Finset.sum_congr rfl fun y _ ↦
            congrArg g.ofLp (by ext z; simp)
        · refine Finset.sum_congr rfl fun y _ ↦
            congrArg g.ofLp (by ext z; simp)
      have h1 : (∑ B₀ ∈ (S₁ \ I).powersetCard k, ∑ C₀ ∈ (Finset.univ \ S₁).powersetCard (m - 1 - k),
            ∑ y ∈ (S₁ \ I) \ B₀, g.ofLp (I ∪ insert y B₀ ∪ C₀)) =
          ((k + 1 : ℕ) : ℝ) * Ψ (k + 1) := by
        rw [Finset.sum_comm]
        have hinner : ∀ C₀ ∈ (Finset.univ \ S₁).powersetCard (m - 1 - k),
            (∑ B₀ ∈ (S₁ \ I).powersetCard k, ∑ y ∈ (S₁ \ I) \ B₀, g.ofLp (I ∪ insert y B₀ ∪ C₀)) =
            ((k + 1 : ℕ) : ℝ) * ∑ B' ∈ (S₁ \ I).powersetCard (k + 1), g.ofLp (I ∪ B' ∪ C₀) :=
          fun C₀ _ ↦ sum_powersetCard_insert (S₁ \ I) k (fun B' ↦ g.ofLp (I ∪ B' ∪ C₀))
        rw [Finset.sum_congr rfl hinner, ← Finset.mul_sum, Finset.sum_comm]
        have hmk : m - 1 - k = m - (k + 1) := by omega
        simp [Ψ, hmk]
      have h2 : (∑ B₀ ∈ (S₁ \ I).powersetCard k, ∑ C₀ ∈ (Finset.univ \ S₁).powersetCard (m - 1 - k),
            ∑ y ∈ (Finset.univ \ S₁) \ C₀, g.ofLp (I ∪ B₀ ∪ insert y C₀)) =
          ((m - k : ℕ) : ℝ) * Ψ k := by
        have hmk : m - 1 - k + 1 = m - k := by omega
        have hinner : ∀ B₀ ∈ (S₁ \ I).powersetCard k,
            (∑ C₀ ∈ (Finset.univ \ S₁).powersetCard (m - 1 - k),
              ∑ y ∈ (Finset.univ \ S₁) \ C₀, g.ofLp (I ∪ B₀ ∪ insert y C₀)) =
            ((m - k : ℕ) : ℝ) *
              ∑ C' ∈ (Finset.univ \ S₁).powersetCard (m - k), g.ofLp (I ∪ B₀ ∪ C') := by
          intro B₀ _
          simpa [hmk] using sum_powersetCard_insert (Finset.univ \ S₁) (m - 1 - k)
            (fun C' ↦ g.ofLp (I ∪ B₀ ∪ C'))
        rw [Finset.sum_congr rfl hinner, ← Finset.mul_sum]
      have hsum0 : ((k + 1 : ℕ) : ℝ) * Ψ (k + 1) + ((m - k : ℕ) : ℝ) * Ψ k = 0 := by
        rw [← h1, ← h2, ← Finset.sum_add_distrib]; rw [← hzero]
        refine Finset.sum_congr rfl fun B₀ hB₀ ↦ ?_
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun C₀ hC₀ ↦ (hsplit B₀ hB₀ C₀ hC₀).symm
      linarith
    let Φ : ℕ → ℝ := fun k ↦ (k.factorial : ℝ) * ((m - k).factorial : ℝ) * Ψ k
    have hΦ : ∀ k ≤ m, Φ k = (-1 : ℝ) ^ k * Φ 0 := by
      intro k
      induction k with
      | zero => intro _; simp [Φ]
      | succ k ih =>
          intro hkm
          have hklt : k < m := by omega
          have hstepk := hstep k hklt
          have hfac1 : ((k + 1).factorial : ℝ) = ((k + 1 : ℕ) : ℝ) * (k.factorial : ℝ) := by
            exact_mod_cast Nat.factorial_succ k
          have hfac2 : ((m - k).factorial : ℝ) =
              ((m - k : ℕ) : ℝ) * ((m - (k + 1)).factorial : ℝ) := by
            have hmkeq : m - k = (m - (k + 1)) + 1 := by omega
            rw [hmkeq]
            exact_mod_cast Nat.factorial_succ (m - (k + 1))
          have hrel : Φ (k + 1) + Φ k = (k.factorial : ℝ) * ((m - (k + 1)).factorial : ℝ) *
                (((m - k : ℕ) : ℝ) * Ψ k + ((k + 1 : ℕ) : ℝ) * Ψ (k + 1)) := by
            dsimp only [Φ]; rw [hfac1, hfac2]; ring
          rw [hstepk, mul_zero] at hrel
          have hneg : Φ (k + 1) = -Φ k := by linarith
          rw [hneg, ih (by omega), pow_succ]
          ring
    have hm := hΦ m (le_refl m); dsimp only [Φ] at hm
    simp only [Nat.sub_self, Nat.sub_zero, Nat.factorial_zero, Nat.cast_one, mul_one, one_mul] at hm
    have hfac_ne : (m.factorial : ℝ) ≠ 0 := by positivity
    have hΨ : Ψ m = (-1 : ℝ) ^ m * Ψ 0 := by apply mul_left_cancel₀ hfac_ne; linarith
    have hΨ0 : Ψ 0 = ∑ J ∈ (Finset.univ \ S₁).powersetCard m, g.ofLp (I ∪ J) := by simp [Ψ]
    have hΨm : Ψ m = ∑ B ∈ (S₁ \ I).powersetCard m, g.ofLp (I ∪ B) := by simp [Ψ]
    have h0_eq : Ψ 0 = (-1 : ℝ) ^ m * Ψ m := by
      rw [hΨ, ← mul_assoc, ← pow_add, ← two_mul, pow_mul]; norm_num
    rw [← hΨ0, ← hΨm, h0_eq]
/-- Partial injective tuple on `U ⊆ Fin L`, padded by `0` outside `U`. -/
def PartialInj {L N : ℕ} [NeZero N] (U : Finset (Fin L)) (x : Fin L → Fin N) : Prop :=
  (∀ i ∈ U, ∀ j ∈ U, x i = x j → i = j) ∧ ∀ i : Fin L, i ∉ U → x i = 0
instance {L N : ℕ} [NeZero N] (U : Finset (Fin L)) : DecidablePred (PartialInj (N := N) U) :=
  fun x ↦ by unfold PartialInj; infer_instance
theorem partialInj_empty {L N : ℕ} [NeZero N] (x : Fin L → Fin N) :
    PartialInj ∅ x ↔ x = fun _ ↦ 0 := by
  constructor
  · intro hx; funext i; exact hx.2 i (Finset.notMem_empty i)
  · rintro rfl; exact ⟨fun _ hi ↦ False.elim (Finset.notMem_empty _ hi), fun _ _ ↦ rfl⟩
theorem partialInj_univ {L N : ℕ} [NeZero N] (x : Fin L → Fin N) :
    PartialInj Finset.univ x ↔ Function.Injective x := by
  constructor
  · intro hx i j hij; exact hx.1 i (Finset.mem_univ i) j (Finset.mem_univ j) hij
  · intro hx; exact ⟨fun i _ j _ hij ↦ hx hij, fun i hi ↦ False.elim (hi (Finset.mem_univ i))⟩
theorem card_image_of_partialInj {L N : ℕ} [NeZero N] {U : Finset (Fin L)} {x : Fin L → Fin N}
    (hx : PartialInj U x) : (U.image x).card = U.card :=
  Finset.card_image_of_injOn (fun i hi j hj hij ↦ hx.1 i hi j hj hij)
theorem sum_partialInj_insert {L N : ℕ} [NeZero N] {U : Finset (Fin L)} {i₀ : Fin L}
    (hi₀ : i₀ ∉ U) (F : (Fin L → Fin N) → ℝ) :
    (∑ x : Fin L → Fin N with PartialInj (insert i₀ U) x, F x) =
      ∑ x : Fin L → Fin N with PartialInj U x,
        ∑ y ∈ Finset.univ \ U.image x, F (Function.update x i₀ y) := by
  have hs : (∑ x : Fin L → Fin N with PartialInj U x,
        ∑ y ∈ Finset.univ \ U.image x, F (Function.update x i₀ y)) =
      ∑ p ∈ (Finset.univ.filter (PartialInj (N := N) U)).sigma
        (fun x ↦ Finset.univ \ U.image x), F (Function.update p.1 i₀ p.2) :=
    (Finset.sum_sigma (Finset.univ.filter (PartialInj (N := N) U))
      (fun x ↦ Finset.univ \ U.image x) (fun p ↦ F (Function.update p.1 i₀ p.2))).symm
  rw [hs]
  refine Finset.sum_nbij' (fun x' ↦ ⟨Function.update x' i₀ 0, x' i₀⟩)
    (fun p ↦ Function.update p.1 i₀ p.2)
    (fun x' hx' ↦ ?_) (fun p hp ↦ ?_) (fun x' _ ↦ ?_) (fun p hp ↦ ?_) (fun _ _ ↦ by simp)
  · have hx := (Finset.mem_filter.1 hx').2
    have himg : U.image (Function.update x' i₀ 0) = U.image x' := by
      refine Finset.image_congr fun j hj ↦ ?_
      have hjne : j ≠ i₀ := fun heq ↦ hi₀ (heq ▸ hj)
      simp [hjne]
    refine Finset.mem_sigma.2 ⟨Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_, ?_⟩, ?_⟩
    · intro j₁ hj₁ j₂ hj₂ heq
      have h1 : j₁ ≠ i₀ := fun h ↦ hi₀ (h ▸ hj₁)
      have h2 : j₂ ≠ i₀ := fun h ↦ hi₀ (h ▸ hj₂)
      simp only [Function.update_of_ne h1, Function.update_of_ne h2] at heq
      exact hx.1 j₁ (Finset.mem_insert_of_mem hj₁) j₂ (Finset.mem_insert_of_mem hj₂) heq
    · intro j hj
      by_cases hji : j = i₀
      · subst hji; simp
      · have hj' : j ∉ insert i₀ U := fun h ↦ (Finset.mem_insert.1 h).elim hji hj
        simp [hji, hx.2 j hj']
    · rw [himg, Finset.mem_sdiff]
      refine ⟨Finset.mem_univ _, fun hmem ↦ ?_⟩
      rcases Finset.mem_image.1 hmem with ⟨j, hjU, hjx⟩
      have heq := hx.1 j (Finset.mem_insert_of_mem hjU) i₀ (Finset.mem_insert_self i₀ U) hjx
      exact hi₀ (heq ▸ hjU)
  · rcases Finset.mem_sigma.1 hp with ⟨hx_mem, hy_mem⟩
    have hx := (Finset.mem_filter.1 hx_mem).2
    have hy : p.2 ∉ U.image p.1 := (Finset.mem_sdiff.1 hy_mem).2
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_, ?_⟩
    · intro j₁ hj₁ j₂ hj₂ heq
      rcases Finset.mem_insert.1 hj₁ with h1eq | hj₁U <;>
        rcases Finset.mem_insert.1 hj₂ with h2eq | hj₂U
      · exact h1eq.trans h2eq.symm
      · exfalso
        subst j₁
        have h2 : j₂ ≠ i₀ := fun h ↦ hi₀ (h ▸ hj₂U)
        simp only [Function.update_self, Function.update_of_ne h2] at heq
        exact hy (heq ▸ Finset.mem_image_of_mem p.1 hj₂U)
      · exfalso
        subst j₂
        have h1 : j₁ ≠ i₀ := fun h ↦ hi₀ (h ▸ hj₁U)
        simp only [Function.update_of_ne h1, Function.update_self] at heq
        exact hy (heq.symm ▸ Finset.mem_image_of_mem p.1 hj₁U)
      · have h1 : j₁ ≠ i₀ := fun h ↦ hi₀ (h ▸ hj₁U)
        have h2 : j₂ ≠ i₀ := fun h ↦ hi₀ (h ▸ hj₂U)
        simp only [Function.update_of_ne h1, Function.update_of_ne h2] at heq
        exact hx.1 j₁ hj₁U j₂ hj₂U heq
    · intro j hj
      have hji : j ≠ i₀ := fun h ↦ hj (h ▸ Finset.mem_insert_self i₀ U)
      have hjU : j ∉ U := fun h ↦ hj (Finset.mem_insert_of_mem h)
      simp [hji, hx.2 j hjU]
  · simp
  · rcases Finset.mem_sigma.1 hp with ⟨hx_mem, _⟩
    have hx := (Finset.mem_filter.1 hx_mem).2
    refine Sigma.ext ?_ (heq_of_eq (by simp))
    funext k
    by_cases hk : k = i₀
    · subst k; simp [hx.2 i₀ hi₀]
    · simp [hk]
theorem sum_partialInj_image_disjoint {L N : ℕ} [NeZero N] (U V : Finset (Fin L))
    (hUV : Disjoint U V) (H : (Fin L → Fin N) → Finset (Fin N) → ℝ)
    (hH : ∀ x₁ x₂, (∀ i ∈ U, x₁ i = x₂ i) → ∀ J, H x₁ J = H x₂ J) :
    (∑ x : Fin L → Fin N with PartialInj (U ∪ V) x, H x (V.image x)) =
      (V.card.factorial : ℝ) *
        ∑ x : Fin L → Fin N with PartialInj U x,
          ∑ J ∈ (Finset.univ \ U.image x).powersetCard V.card, H x J := by
  induction V using Finset.induction_on generalizing H with
  | empty => simp
  | @insert v₀ V' hv₀V' ih =>
      have hv₀U : v₀ ∉ U := (Finset.disjoint_insert_right.1 hUV).1
      have hUV' : Disjoint U V' := (Finset.disjoint_insert_right.1 hUV).2
      have hv₀UV' : v₀ ∉ U ∪ V' := Finset.notMem_union.2 ⟨hv₀U, hv₀V'⟩
      have hunion : U ∪ insert v₀ V' = insert v₀ (U ∪ V') := by ext i; simp
      rw [hunion, sum_partialInj_insert hv₀UV']
      have hinner : ∀ x ∈ Finset.univ.filter (PartialInj (N := N) (U ∪ V')),
          (∑ y ∈ Finset.univ \ (U ∪ V').image x,
            H (Function.update x v₀ y) ((insert v₀ V').image (Function.update x v₀ y))) =
            ∑ y ∈ (Finset.univ \ U.image x) \ V'.image x,
              H x (insert y (V'.image x)) := by
        intro x _
        have hHx : ∀ y J, H (Function.update x v₀ y) J = H x J := fun y J ↦
          hH _ _ (fun i hi ↦ Function.update_of_ne (fun h : i = v₀ ↦ hv₀U (h ▸ hi)) y x) J
        have hVx : ∀ y, (insert v₀ V').image (Function.update x v₀ y) = insert y (V'.image x) := by
          intro y; rw [Finset.image_insert, Function.update_self]; congr 1
          exact Finset.image_congr fun i hi ↦
            Function.update_of_ne (fun h : i = v₀ ↦ hv₀V' (h ▸ hi)) y x
        have hsdiff : Finset.univ \ (U ∪ V').image x =
            (Finset.univ \ U.image x) \ V'.image x := by
          ext y
          simp only [Finset.mem_sdiff, Finset.mem_image, Finset.mem_union, Finset.mem_univ,
            true_and]
          constructor
          · intro hy
            exact ⟨fun ⟨i, hi, hxi⟩ ↦ hy ⟨i, Or.inl hi, hxi⟩,
              fun ⟨i, hi, hxi⟩ ↦ hy ⟨i, Or.inr hi, hxi⟩⟩
          · rintro ⟨h1, h2⟩ ⟨i, hi | hi, hxi⟩
            · exact h1 ⟨i, hi, hxi⟩
            · exact h2 ⟨i, hi, hxi⟩
        rw [hsdiff]
        refine Finset.sum_congr rfl fun y _ ↦ by rw [hHx, hVx]
      rw [Finset.sum_congr rfl hinner,
        ih hUV' (fun x J' ↦ ∑ y ∈ (Finset.univ \ U.image x) \ J', H x (insert y J'))
          (fun x₁ x₂ hx J' ↦ by
            have hUimg : U.image x₁ = U.image x₂ := Finset.image_congr hx; rw [hUimg]
            refine Finset.sum_congr rfl fun y _ ↦ hH x₁ x₂ hx (insert y J'))]
      have hcard : (insert v₀ V').card = V'.card + 1 := Finset.card_insert_of_notMem hv₀V'
      rw [hcard, Nat.factorial_succ, Nat.cast_mul, mul_comm ((V'.card + 1 : ℕ) : ℝ), mul_assoc]
      congr 1; rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ ↦
        sum_powersetCard_insert (Finset.univ \ U.image x) V'.card (H x)
theorem sum_partialInj_indep {L N : ℕ} [NeZero N] {U W : Finset (Fin L)}
    (hUW : U ⊆ W) (F : (Fin L → Fin N) → ℝ)
    (hF : ∀ x₁ x₂, (∀ i ∈ U, x₁ i = x₂ i) → F x₁ = F x₂) :
    (∑ x : Fin L → Fin N with PartialInj W x, F x) =
      (((W.card - U.card).factorial * (N - U.card).choose (W.card - U.card) : ℕ) : ℝ) *
        ∑ x : Fin L → Fin N with PartialInj U x, F x := by
  have hunion : W = U ∪ (W \ U) := (Finset.union_sdiff_of_subset hUW).symm
  have hdisj : Disjoint U (W \ U) := disjoint_sdiff_self_right
  have h1 := sum_partialInj_image_disjoint (N := N) U (W \ U) hdisj
    (fun x _ ↦ F x) (fun x₁ x₂ hx _ ↦ hF x₁ x₂ hx)
  conv_lhs => rw [hunion, h1]
  rw [Finset.mul_sum, Finset.mul_sum]
  have hsub : (W \ U).card = W.card - U.card := Finset.card_sdiff_of_subset hUW
  refine Finset.sum_congr rfl fun x hx_mem ↦ ?_
  have hx := (Finset.mem_filter.1 hx_mem).2
  have hcardU : (U.image x).card = U.card := card_image_of_partialInj hx
  have hsdiff : (Finset.univ \ U.image x).card = N - U.card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin,
      hcardU]
  simp only [Finset.sum_const, Finset.card_powersetCard, hsdiff, hsub, nsmul_eq_mul, Nat.cast_mul]
  ring
theorem card_injTuple {L N : ℕ} [NeZero N] :
    (∑ _x : Fin L → Fin N with Function.Injective _x, (1 : ℝ)) =
      ((L.factorial * N.choose L : ℕ) : ℝ) := by
  have heq : Finset.univ.filter (Function.Injective : (Fin L → Fin N) → Prop) =
      Finset.univ.filter (PartialInj (N := N) Finset.univ) := by
    ext x; simp [partialInj_univ]
  rw [heq, sum_partialInj_indep (Finset.empty_subset Finset.univ) (fun _ ↦ 1) (fun _ _ _ ↦ rfl)]
  have hempty : Finset.univ.filter (PartialInj (N := N) (∅ : Finset (Fin L))) = {fun _ ↦ 0} := by
    ext x; simp [partialInj_empty]
  simp [hempty]
theorem sum_inj_pair_lt {L N w₂ : ℕ} [NeZero N] (hw₂ : 1 ≤ w₂)
    {K M : Finset (Fin L)} (hKM : K.card < w₂) (hM : M.card = w₂)
    (φ : Finset (Fin N) → ℝ) {g : EuclideanSpace ℝ (Finset (Fin N))}
    (hg : g ∈ harmonicSubspace N w₂) :
    (∑ x : Fin L → Fin N with Function.Injective x,
      φ (K.image x) * g.ofLp (M.image x)) = 0 := by
  have heq : Finset.univ.filter (Function.Injective : (Fin L → Fin N) → Prop) =
      Finset.univ.filter (PartialInj (N := N) Finset.univ) := by
    ext x; simp [partialInj_univ]
  rw [heq, sum_partialInj_indep (Finset.subset_univ (K ∪ M)) _ (fun x₁ x₂ h ↦ by
    have hK : K.image x₁ = K.image x₂ :=
      Finset.image_congr fun i hi ↦ h i (Finset.mem_union_left M hi)
    have hM' : M.image x₁ = M.image x₂ :=
      Finset.image_congr fun i hi ↦ h i (Finset.mem_union_right K hi)
    rw [hK, hM'])]
  suffices h0 : (∑ x : Fin L → Fin N with PartialInj (K ∪ M) x,
      φ (K.image x) * g.ofLp (M.image x)) = 0 by rw [h0, mul_zero]
  have hunion : K ∪ M = K ∪ (M \ K) := Finset.union_sdiff_self_eq_union.symm
  have hMsplit : M = (K ∩ M) ∪ (M \ K) := by ext i; simp; tauto
  have hrew : ∀ x : Fin L → Fin N, φ (K.image x) * g.ofLp (M.image x) =
        φ (K.image x) * g.ofLp ((K ∩ M).image x ∪ (M \ K).image x) := by
    intro x; conv_lhs => rw [hMsplit, Finset.image_union]
  simp_rw [hrew]
  rw [hunion, sum_partialInj_image_disjoint K (M \ K) disjoint_sdiff_self_right
    (fun x J ↦ φ (K.image x) * g.ofLp ((K ∩ M).image x ∪ J))
    (fun x₁ x₂ hx J ↦ by
      have hK : K.image x₁ = K.image x₂ := Finset.image_congr hx
      have hKM' : (K ∩ M).image x₁ = (K ∩ M).image x₂ :=
        Finset.image_congr fun i hi ↦ hx i (Finset.mem_of_mem_inter_left hi)
      rw [hK, hKM'])]
  suffices hinner0 : ∀ x ∈ Finset.univ.filter (PartialInj (N := N) K),
      (∑ J ∈ (Finset.univ \ K.image x).powersetCard (M \ K).card,
        φ (K.image x) * g.ofLp ((K ∩ M).image x ∪ J)) = 0 by
    rw [Finset.sum_eq_zero hinner0, mul_zero]
  intro x hx_mem; have hx := (Finset.mem_filter.1 hx_mem).2
  rw [← Finset.mul_sum]; set S₁ := K.image x; set I₀ := (K ∩ M).image x
  have hIS : I₀ ⊆ S₁ := Finset.image_subset_image Finset.inter_subset_left
  have hcS : S₁.card = K.card := card_image_of_partialInj hx
  have hcI : I₀.card = (K ∩ M).card :=
    Finset.card_image_of_injOn fun i hi j hj hij ↦
      hx.1 i (Finset.mem_of_mem_inter_left hi) j (Finset.mem_of_mem_inter_left hj) hij
  have hcMK : (M \ K).card = w₂ - I₀.card := by
    have := Finset.card_inter_add_card_sdiff M K; rw [Finset.inter_comm] at this; omega
  have hIM : (K ∩ M).card ≤ M.card := Finset.card_le_card Finset.inter_subset_right
  have hIK : (K ∩ M).card ≤ K.card := Finset.card_le_card Finset.inter_subset_left
  have hIw : I₀.card ≤ w₂ := by omega
  rw [hcMK, sum_harmonic_compl_powersetCard hw₂ hg hIS hIw]
  have hemp : (S₁ \ I₀).powersetCard (w₂ - I₀.card) = ∅ := by
    rw [Finset.powersetCard_eq_empty, Finset.card_sdiff_of_subset hIS]; omega
  simp [hemp]
theorem sum_inj_pair_eq {L N w : ℕ} [NeZero N] (hw : 1 ≤ w)
    {K M : Finset (Fin L)} (hK : K.card = w) (hM : M.card = w)
    {f g : EuclideanSpace ℝ (Finset (Fin N))}
    (hf : f ∈ harmonicSubspace N w) (hg : g ∈ harmonicSubspace N w) :
    (∑ x : Fin L → Fin N with Function.Injective x,
      f.ofLp (K.image x) * g.ofLp (M.image x)) =
      (-1 : ℝ) ^ (w - (K ∩ M).card) *
        ((L - (2 * w - (K ∩ M).card)).factorial : ℝ) *
        ((N - (2 * w - (K ∩ M).card)).choose (L - (2 * w - (K ∩ M).card)) : ℝ) *
        ((w - (K ∩ M).card).factorial : ℝ) *
        (w.factorial : ℝ) * ⟪f, g⟫ := by
  have heq : Finset.univ.filter (Function.Injective : (Fin L → Fin N) → Prop) =
      Finset.univ.filter (PartialInj (N := N) Finset.univ) := by
    ext x; simp [partialInj_univ]
  have hKM_card : (K ∪ M).card = 2 * w - (K ∩ M).card := by
    have := Finset.card_union_add_card_inter K M; omega
  rw [heq, sum_partialInj_indep (Finset.subset_univ (K ∪ M)) _ (fun x₁ x₂ h ↦ by
    have hK' : K.image x₁ = K.image x₂ :=
      Finset.image_congr fun i hi ↦ h i (Finset.mem_union_left M hi)
    have hM' : M.image x₁ = M.image x₂ :=
      Finset.image_congr fun i hi ↦ h i (Finset.mem_union_right K hi)
    rw [hK', hM'])]
  simp only [Fintype.card_fin, Finset.card_univ, hKM_card, Nat.cast_mul]
  have hunion : K ∪ M = K ∪ (M \ K) := Finset.union_sdiff_self_eq_union.symm
  have hMsplit : M = (K ∩ M) ∪ (M \ K) := by ext i; simp; tauto
  have hrew : ∀ x : Fin L → Fin N, f.ofLp (K.image x) * g.ofLp (M.image x) =
        f.ofLp (K.image x) * g.ofLp ((K ∩ M).image x ∪ (M \ K).image x) := by
    intro x; conv_lhs => rw [hMsplit, Finset.image_union]
  simp_rw [hrew]
  have hMK_card : (M \ K).card = w - (K ∩ M).card := by
    have := Finset.card_inter_add_card_sdiff M K; rw [Finset.inter_comm] at this; omega
  rw [hunion, sum_partialInj_image_disjoint K (M \ K) disjoint_sdiff_self_right
    (fun x J ↦ f.ofLp (K.image x) * g.ofLp ((K ∩ M).image x ∪ J))
    (fun x₁ x₂ hx J ↦ by
      have hK' : K.image x₁ = K.image x₂ := Finset.image_congr hx
      have hKM' : (K ∩ M).image x₁ = (K ∩ M).image x₂ :=
        Finset.image_congr fun i hi ↦ hx i (Finset.mem_of_mem_inter_left hi)
      rw [hK', hKM']), hMK_card]
  have hstep1 : ∀ x ∈ Finset.univ.filter (PartialInj (N := N) K),
      (∑ J ∈ (Finset.univ \ K.image x).powersetCard (w - (K ∩ M).card),
        f.ofLp (K.image x) * g.ofLp ((K ∩ M).image x ∪ J)) =
        (-1 : ℝ) ^ (w - (K ∩ M).card) * (f.ofLp (K.image x) * g.ofLp (K.image x)) := by
    intro x hx_mem; have hx := (Finset.mem_filter.1 hx_mem).2
    rw [← Finset.mul_sum]; set S₁ := K.image x; set I₀ := (K ∩ M).image x
    have hIS : I₀ ⊆ S₁ := Finset.image_subset_image Finset.inter_subset_left
    have hcS : S₁.card = w := (card_image_of_partialInj hx).trans hK
    have hcI : I₀.card = (K ∩ M).card :=
      Finset.card_image_of_injOn fun i hi j hj hij ↦
        hx.1 i (Finset.mem_of_mem_inter_left hi) j (Finset.mem_of_mem_inter_left hj) hij
    have hIw : I₀.card ≤ w := by
      have : (K ∩ M).card ≤ K.card := Finset.card_le_card Finset.inter_subset_left; omega
    rw [← hcI, sum_harmonic_compl_powersetCard hw hg hIS hIw]
    have hsd_card : w - I₀.card = (S₁ \ I₀).card := by rw [Finset.card_sdiff_of_subset hIS, hcS]
    rw [hsd_card, Finset.powersetCard_self, Finset.sum_singleton,
      Finset.union_sdiff_of_subset hIS, ← hsd_card, hcI]
    ring
  rw [Finset.sum_congr rfl hstep1, ← Finset.mul_sum]
  have hstep2 : (∑ x : Fin L → Fin N with PartialInj K x,
      f.ofLp (K.image x) * g.ofLp (K.image x)) = (w.factorial : ℝ) * ⟪f, g⟫ := by
    have h0K : Finset.univ.filter (PartialInj (N := N) K) =
        Finset.univ.filter (PartialInj (N := N) (∅ ∪ K)) := by simp
    have hdisj0 : Disjoint (∅ : Finset (Fin L)) K := Finset.disjoint_empty_left K
    rw [h0K, sum_partialInj_image_disjoint ∅ K hdisj0
      (fun _ S₁ ↦ f.ofLp S₁ * g.ofLp S₁) (fun _ _ _ _ ↦ rfl), hK]
    have hempty : Finset.univ.filter (PartialInj (N := N) (∅ : Finset (Fin L))) = {fun _ ↦ 0} := by
      ext x; simp [partialInj_empty]
    rw [hempty, Finset.sum_singleton]; simp only [Finset.image_empty, Finset.sdiff_empty]
    congr 1; rw [PiLp.inner_apply]
    symm; rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.powersetCard w))]
    · refine Finset.sum_congr rfl fun s _ ↦ by simp [mul_comm]
    · intro s _ hs
      have hne : s.card ≠ w := fun hc ↦
        hs (Finset.mem_powersetCard.2 ⟨Finset.subset_univ s, hc⟩)
      simp [hf.1 s hne]
  rw [hstep2]; ring
theorem alt_sum_choose_shift :
    ∀ (m A K : ℕ), m ≤ K →
      (∑ t ∈ Finset.range (m + 1),
        (-1 : ℝ) ^ (m - t) * (m.choose t : ℝ) * ((A + t).choose K : ℝ)) =
        (A.choose (K - m) : ℝ)
  | 0, A, K, _ => by simp
  | m + 1, A, K, hmK => by
      obtain ⟨K', rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by omega⟩
      have hmK' : m ≤ K' := by omega
      have ih := alt_sum_choose_shift m A K' hmK'
      have hstep : ∀ t : ℕ, ((A + t).choose K' : ℝ) =
          ((A + (t + 1)).choose (K' + 1) : ℝ) - ((A + t).choose (K' + 1) : ℝ) := by
        intro t; have := Nat.choose_succ_succ (A + t) K'
        have hAt : A + (t + 1) = A + t + 1 := by omega
        rw [hAt, this, Nat.cast_add]; ring
      simp_rw [hstep, mul_sub, Finset.sum_sub_distrib] at ih
      rw [Finset.sum_range_succ' (fun t ↦
        (-1 : ℝ) ^ (m + 1 - t) * ((m + 1).choose t : ℝ) * ((A + t).choose (K' + 1) : ℝ))]
      simp only [Nat.sub_zero, Nat.choose_zero_right, Nat.cast_one, mul_one, add_zero]
      have hpascal : (∑ t ∈ Finset.range (m + 1),
          (-1 : ℝ) ^ (m + 1 - (t + 1)) * ((m + 1).choose (t + 1) : ℝ) *
            ((A + (t + 1)).choose (K' + 1) : ℝ)) =
          (∑ t ∈ Finset.range (m + 1),
            (-1 : ℝ) ^ (m - t) * (m.choose t : ℝ) * ((A + (t + 1)).choose (K' + 1) : ℝ)) +
          ∑ t ∈ Finset.range (m + 1),
            (-1 : ℝ) ^ (m - t) * (m.choose (t + 1) : ℝ) * ((A + (t + 1)).choose (K' + 1) : ℝ) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun t _ ↦ ?_
        rw [Nat.succ_sub_succ_eq_sub, Nat.choose_succ_succ m t, Nat.cast_add]; ring
      rw [hpascal]
      have hshift2 : (-1 : ℝ) ^ (m + 1) * (A.choose (K' + 1) : ℝ) + (∑ t ∈ Finset.range (m + 1),
            (-1 : ℝ) ^ (m - t) * (m.choose (t + 1) : ℝ) * ((A + (t + 1)).choose (K' + 1) : ℝ)) =
          - ∑ t ∈ Finset.range (m + 1),
            (-1 : ℝ) ^ (m - t) * (m.choose t : ℝ) * ((A + t).choose (K' + 1) : ℝ) := by
        have h1 := Finset.sum_range_succ'
          (fun t ↦ (-1 : ℝ) ^ (m + 1 - t) * (m.choose t : ℝ) * ((A + t).choose (K' + 1) : ℝ))
          (m + 1)
        have h2 := Finset.sum_range_succ
          (fun t ↦ (-1 : ℝ) ^ (m + 1 - t) * (m.choose t : ℝ) * ((A + t).choose (K' + 1) : ℝ))
          (m + 1)
        simp only [Nat.choose_succ_self, Nat.cast_zero, mul_zero, zero_mul, add_zero,
          Nat.sub_zero, Nat.choose_zero_right, Nat.cast_one, mul_one] at h1 h2
        have hrew1 : (∑ k ∈ Finset.range (m + 1),
            (-1 : ℝ) ^ (m + 1 - (k + 1)) * (m.choose (k + 1) : ℝ) *
              ((A + (k + 1)).choose (K' + 1) : ℝ)) =
            ∑ t ∈ Finset.range (m + 1),
              (-1 : ℝ) ^ (m - t) * (m.choose (t + 1) : ℝ) * ((A + (t + 1)).choose (K' + 1) : ℝ) :=
          Finset.sum_congr rfl fun t _ ↦ by rw [Nat.succ_sub_succ_eq_sub]
        have hrew2 : (∑ x ∈ Finset.range (m + 1),
            (-1 : ℝ) ^ (m + 1 - x) * (m.choose x : ℝ) * ((A + x).choose (K' + 1) : ℝ)) =
            - ∑ t ∈ Finset.range (m + 1),
              (-1 : ℝ) ^ (m - t) * (m.choose t : ℝ) * ((A + t).choose (K' + 1) : ℝ) := by
          rw [← Finset.sum_neg_distrib]
          refine Finset.sum_congr rfl fun t ht ↦ ?_
          have htm : t ≤ m := Nat.lt_succ_iff.1 (Finset.mem_range.1 ht)
          have hsub : m + 1 - t = (m - t) + 1 := by omega
          rw [hsub, pow_succ]; ring
        linarith
      have hKm : K' + 1 - (m + 1) = K' - m := Nat.succ_sub_succ_eq_sub K' m; rw [hKm]; linarith
theorem sum_pairs_powersetCard_inter {α : Type*} [DecidableEq α] (U₀ : Finset α) (k₁ k₂ : ℕ)
    (hk : k₁ ≤ k₂) (F : ℕ → ℝ) :
    (∑ K₁ ∈ U₀.powersetCard k₁, ∑ K₂ ∈ U₀.powersetCard k₂, F (K₁ ∩ K₂).card) =
      ∑ t ∈ Finset.range (k₁ + 1),
        ((U₀.card.choose k₁ * k₁.choose t * (U₀.card - k₁).choose (k₂ - t) : ℕ) : ℝ) * F t := by
  have hinner : ∀ K₁ ∈ U₀.powersetCard k₁, (∑ K₂ ∈ U₀.powersetCard k₂, F (K₁ ∩ K₂).card) =
        ∑ t ∈ Finset.range (k₁ + 1),
          ((k₁.choose t * (U₀.card - k₁).choose (k₂ - t) : ℕ) : ℝ) * F t := by
    intro K₁ hK₁
    rcases Finset.mem_powersetCard.1 hK₁ with ⟨hK₁U, hcK₁⟩
    have hbij : (∑ K₂ ∈ U₀.powersetCard k₂, F (K₁ ∩ K₂).card) =
        ∑ p ∈ K₁.powerset.sigma (fun I ↦ (U₀ \ K₁).powersetCard (k₂ - I.card)), F p.1.card := by
      refine Finset.sum_nbij' (fun K₂ ↦ ⟨K₁ ∩ K₂, K₂ \ K₁⟩) (fun p ↦ p.1 ∪ p.2)
        (fun K₂ hK₂ ↦ ?_) (fun p hp ↦ ?_) (fun K₂ _ ↦ by ext x; simp; tauto)
        (fun p hp ↦ ?_) (fun _ _ ↦ rfl)
      · rcases Finset.mem_powersetCard.1 hK₂ with ⟨hK₂U, hcK₂⟩
        refine Finset.mem_sigma.2 ⟨Finset.mem_powerset.2 Finset.inter_subset_left,
          Finset.mem_powersetCard.2 ⟨Finset.sdiff_subset_sdiff hK₂U (Finset.Subset.refl K₁), ?_⟩⟩
        dsimp only; have := Finset.card_inter_add_card_sdiff K₂ K₁
        rw [Finset.inter_comm] at this; omega
      · rcases Finset.mem_sigma.1 hp with ⟨hI, hJ⟩
        have hIK₁ : p.1 ⊆ K₁ := Finset.mem_powerset.1 hI
        have hIk₂ : p.1.card ≤ k₂ := (Finset.card_le_card hIK₁).trans (hcK₁.le.trans hk)
        rcases Finset.mem_powersetCard.1 hJ with ⟨hJU, hcJ⟩
        have hdisj : Disjoint p.1 p.2 := Disjoint.mono hIK₁ hJU disjoint_sdiff_self_right
        refine Finset.mem_powersetCard.2 ⟨Finset.union_subset (hIK₁.trans hK₁U)
          (hJU.trans Finset.sdiff_subset), ?_⟩
        rw [Finset.card_union_of_disjoint hdisj, hcJ]; omega
      · rcases Finset.mem_sigma.1 hp with ⟨hI, hJ⟩
        have hIK₁ : p.1 ⊆ K₁ := Finset.mem_powerset.1 hI
        have hJU : p.2 ⊆ U₀ \ K₁ := (Finset.mem_powersetCard.1 hJ).1
        refine Sigma.ext ?_ (heq_of_eq ?_)
        · ext x
          simp only [Finset.mem_inter, Finset.mem_union]
          have hxJ : x ∈ p.2 → x ∉ K₁ := fun hx ↦ (Finset.mem_sdiff.1 (hJU hx)).2
          have hxI : x ∈ p.1 → x ∈ K₁ := fun hx ↦ hIK₁ hx
          tauto
        · ext x
          simp only [Finset.mem_sdiff, Finset.mem_union]
          have hxJ : x ∈ p.2 → x ∉ K₁ := fun hx ↦ (Finset.mem_sdiff.1 (hJU hx)).2
          have hxI : x ∈ p.1 → x ∈ K₁ := fun hx ↦ hIK₁ hx
          tauto
    rw [hbij, Finset.sum_sigma]
    have hpow : K₁.powerset = (Finset.range (k₁ + 1)).biUnion K₁.powersetCard := by
      ext I
      simp only [Finset.mem_powerset, Finset.mem_biUnion, Finset.mem_range, Finset.mem_powersetCard]
      constructor
      · intro hsub; exact ⟨I.card, Nat.lt_succ_of_le (hcK₁ ▸ Finset.card_le_card hsub), hsub, rfl⟩
      · rintro ⟨_, _, hsub, _⟩; exact hsub
    have hdisj_bi : Set.PairwiseDisjoint (Finset.range (k₁ + 1) : Set ℕ) K₁.powersetCard := by
      intro t₁ _ t₂ _ hne; rw [Function.onFun, Finset.disjoint_left]; intro I h1 h2
      exact hne ((Finset.mem_powersetCard.1 h1).2.symm.trans (Finset.mem_powersetCard.1 h2).2)
    rw [hpow, Finset.sum_biUnion hdisj_bi]
    refine Finset.sum_congr rfl fun t _ ↦ ?_
    have hcU : (U₀ \ K₁).card = U₀.card - k₁ := by rw [Finset.card_sdiff_of_subset hK₁U, hcK₁]
    have hinner_t : ∀ I ∈ K₁.powersetCard t,
        (∑ _J ∈ (U₀ \ K₁).powersetCard (k₂ - I.card), F I.card) =
          (((U₀.card - k₁).choose (k₂ - t) : ℕ) : ℝ) * F t := by
      intro I hI; have hcI : I.card = t := (Finset.mem_powersetCard.1 hI).2
      simp [hcI, Finset.card_powersetCard, hcU]
    rw [Finset.sum_congr rfl hinner_t, Finset.sum_const, Finset.card_powersetCard, hcK₁,
      nsmul_eq_mul, Nat.cast_mul]
    ring
  rw [Finset.sum_congr rfl hinner, Finset.sum_const, Finset.card_powersetCard, nsmul_eq_mul,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ ↦ ?_
  push_cast; ring
theorem choose_mul_fact_symm (n₀ a M K : ℕ) (h : K + n₀ = M + a) :
    n₀.choose a * a.factorial * (n₀ - a).factorial * M.choose (n₀ - a) =
      n₀.factorial * M.choose K := by
  by_cases ha : a ≤ n₀
  · rw [Nat.choose_mul_factorial_mul_factorial ha]
    have hk : n₀ - a ≤ M := by omega
    have hsub : M - (n₀ - a) = K := by omega
    rw [← Nat.choose_symm hk, hsub]
  · rw [Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge ha), zero_mul, zero_mul, zero_mul]
    have hMK : M < K := by omega
    rw [Nat.choose_eq_zero_of_lt hMK, mul_zero]
theorem choose_pred_mul_fact (L w : ℕ) (hw1 : 1 ≤ w) (hwL : w ≤ L) :
    (L - 1).choose (w - 1) * w.factorial * (L - w).factorial = (L - 1).factorial * w := by
  have hw_sub : w - 1 ≤ L - 1 := by omega
  have hLw : L - 1 - (w - 1) = L - w := by omega
  have hwf : w.factorial = w * (w - 1).factorial := by
    obtain ⟨w', rfl⟩ : ∃ w', w = w' + 1 := ⟨w - 1, by omega⟩
    simp [Nat.factorial_succ]
  calc (L - 1).choose (w - 1) * w.factorial * (L - w).factorial
      = ((L - 1).choose (w - 1) * (w - 1).factorial * (L - 1 - (w - 1)).factorial) * w := by
          rw [hwf, hLw]; ring
    _ = (L - 1).factorial * w := by rw [Nat.choose_mul_factorial_mul_factorial hw_sub]
/-- Tail slot indices `Finset.univ.erase 0` of size `L - 1`. -/
def tailSlots (L : ℕ) [NeZero L] : Finset (Fin L) :=
  Finset.univ.erase 0
theorem card_tailSlots (L : ℕ) [NeZero L] : (tailSlots L).card = L - 1 := by
  simp [tailSlots]
/-- Raw slot-`0`-inclusive lift `L_{w,+}^{\mathrm{raw}}` on injective `L`-tuples. -/
noncomputable def rawLiftA {L N : ℕ} [NeZero L] (w : ℕ)
    (f : EuclideanSpace ℝ (Finset (Fin N))) : EuclideanSpace ℝ (Fin L → Fin N) :=
  WithLp.toLp 2 fun x ↦
    if Function.Injective x then
      ∑ K' ∈ (tailSlots L).powersetCard (w - 1), f.ofLp ((insert (0 : Fin L) K').image x)
    else 0
/-- Raw tail-only lift `L_{w,T}^{\mathrm{raw}}` on injective `L`-tuples. -/
noncomputable def rawLiftT {L N : ℕ} [NeZero L] (w : ℕ)
    (f : EuclideanSpace ℝ (Finset (Fin N))) : EuclideanSpace ℝ (Fin L → Fin N) :=
  WithLp.toLp 2 fun x ↦
    if Function.Injective x then
      ∑ K ∈ (tailSlots L).powersetCard w, f.ofLp (K.image x)
    else 0
/-- Orthogonalized second lift `(L - w) • rawLiftA + (N - 2w + 1) • rawLiftT`. -/
noncomputable def rawLiftB {L N : ℕ} [NeZero L] (w : ℕ)
    (f : EuclideanSpace ℝ (Finset (Fin N))) : EuclideanSpace ℝ (Fin L → Fin N) :=
  ((L - w : ℕ) : ℝ) • rawLiftA (L := L) w f + ((N - 2 * w + 1 : ℕ) : ℝ) • rawLiftT (L := L) w f
/-- Uniform normalized distinct-tuple state `b_0` on `Fin L → Fin N`. -/
noncomputable def b0TupleVec (L N : ℕ) : EuclideanSpace ℝ (Fin L → Fin N) :=
  (1 / √((L.factorial * N.choose L : ℕ) : ℝ)) •
    WithLp.toLp 2 (fun x : Fin L → Fin N ↦ if Function.Injective x then 1 else 0)
theorem inner_inj_expand {L N : ℕ} (u v : (Fin L → Fin N) → ℝ) :
    ⟪(WithLp.toLp 2 fun x ↦ if Function.Injective x then u x else 0 :
        EuclideanSpace ℝ (Fin L → Fin N)),
     (WithLp.toLp 2 fun x ↦ if Function.Injective x then v x else 0 :
        EuclideanSpace ℝ (Fin L → Fin N))⟫ =
      ∑ x : Fin L → Fin N with Function.Injective x, u x * v x := by
  rw [PiLp.inner_apply, Finset.sum_filter]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  by_cases h : Function.Injective x <;> simp [h, mul_comm]
theorem inner_rawLiftA_self {L N w : ℕ} [NeZero L] [NeZero N]
    (hw1 : 1 ≤ w) (hwL : w ≤ L) (hN : 2 * L ≤ N)
    {f g : EuclideanSpace ℝ (Finset (Fin N))}
    (hf : f ∈ harmonicSubspace N w) (hg : g ∈ harmonicSubspace N w) :
    ⟪rawLiftA (L := L) w f, rawLiftA (L := L) w g⟫ =
      (((L - 1).factorial * w * (N - 2 * w + 1).choose (L - w) : ℕ) : ℝ) * ⟪f, g⟫ := by
  unfold rawLiftA; rw [inner_inj_expand]
  have hexp : (∑ x : Fin L → Fin N with Function.Injective x,
      (∑ K₁ ∈ (tailSlots L).powersetCard (w - 1), f.ofLp ((insert 0 K₁).image x)) *
      (∑ K₂ ∈ (tailSlots L).powersetCard (w - 1), g.ofLp ((insert 0 K₂).image x))) =
      ∑ K₁ ∈ (tailSlots L).powersetCard (w - 1), ∑ K₂ ∈ (tailSlots L).powersetCard (w - 1),
          ∑ x : Fin L → Fin N with Function.Injective x,
            f.ofLp ((insert 0 K₁).image x) * g.ofLp ((insert 0 K₂).image x) := by
    simp_rw [Finset.sum_mul_sum]; rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun K₁ _ ↦ Finset.sum_comm
  rw [hexp]
  let F : ℕ → ℝ := fun t ↦
    (-1 : ℝ) ^ (w - (t + 1)) * ((L - (2 * w - (t + 1))).factorial : ℝ) *
      ((N - (2 * w - (t + 1))).choose (L - (2 * w - (t + 1))) : ℝ) *
      ((w - (t + 1)).factorial : ℝ) *
      (w.factorial : ℝ) * ⟪f, g⟫
  have hpair : ∀ K₁ ∈ (tailSlots L).powersetCard (w - 1), ∀ K₂ ∈ (tailSlots L).powersetCard (w - 1),
        (∑ x : Fin L → Fin N with Function.Injective x,
          f.ofLp ((insert (0 : Fin L) K₁).image x) * g.ofLp ((insert (0 : Fin L) K₂).image x)) =
          F (K₁ ∩ K₂).card := by
    intro K₁ hK₁ K₂ hK₂
    have h0₁ : (0 : Fin L) ∉ K₁ := fun h0 ↦
      (Finset.mem_erase.1 ((Finset.mem_powersetCard.1 hK₁).1 h0)).1 rfl
    have h0₂ : (0 : Fin L) ∉ K₂ := fun h0 ↦
      (Finset.mem_erase.1 ((Finset.mem_powersetCard.1 hK₂).1 h0)).1 rfl
    have hc₁ : (insert (0 : Fin L) K₁).card = w := by
      rw [Finset.card_insert_of_notMem h0₁, (Finset.mem_powersetCard.1 hK₁).2]; omega
    have hc₂ : (insert (0 : Fin L) K₂).card = w := by
      rw [Finset.card_insert_of_notMem h0₂, (Finset.mem_powersetCard.1 hK₂).2]; omega
    have hint : (insert (0 : Fin L) K₁ ∩ insert (0 : Fin L) K₂).card = (K₁ ∩ K₂).card + 1 := by
      rw [← Finset.insert_inter_distrib, Finset.card_insert_of_notMem
        (fun h ↦ h0₁ (Finset.mem_of_mem_inter_left h))]
    rw [sum_inj_pair_eq hw1 hc₁ hc₂ hf hg, hint]
  rw [Finset.sum_congr rfl fun K₁ hK₁ ↦ Finset.sum_congr rfl fun K₂ hK₂ ↦ hpair K₁ hK₁ K₂ hK₂,
    sum_pairs_powersetCard_inter (tailSlots L) (w - 1) (w - 1) (le_refl _) F, card_tailSlots]
  have hterm : ∀ t ∈ Finset.range (w - 1 + 1), (((L - 1).choose (w - 1) * (w - 1).choose t *
        (L - 1 - (w - 1)).choose (w - 1 - t) : ℕ) : ℝ) * F t =
        (((L - 1).factorial * w : ℕ) : ℝ) * ⟪f, g⟫ *
          ((-1 : ℝ) ^ (w - 1 - t) * ((w - 1).choose t : ℝ) *
            ((N - 2 * w + 1 + t).choose (N - L) : ℝ)) := by
    intro t ht; have htw : t ≤ w - 1 := Nat.lt_succ_iff.1 (Finset.mem_range.1 ht); dsimp only [F]
    have ha1 : w - (t + 1) = w - 1 - t := by omega
    have hn0 : L - 1 - (w - 1) = L - w := by omega
    have hsubL : L - (2 * w - (t + 1)) = (L - w) - (w - 1 - t) := by omega
    have hsubN : N - (2 * w - (t + 1)) = N - 2 * w + 1 + t := by omega
    rw [ha1, hn0, hsubL, hsubN]
    have hcm := congrArg (Nat.cast (R := ℝ))
      (choose_mul_fact_symm (L - w) (w - 1 - t) (N - 2 * w + 1 + t) (N - L) (by omega))
    have hcp := congrArg (Nat.cast (R := ℝ)) (choose_pred_mul_fact L w hw1 hwL)
    push_cast at hcm hcp ⊢
    linear_combination
      ((-1 : ℝ) ^ (w - 1 - t) * ((w - 1).choose t : ℝ) * ⟪f, g⟫ *
        (((L - 1).choose (w - 1) : ℝ) * (w.factorial : ℝ))) * hcm +
      ((-1 : ℝ) ^ (w - 1 - t) * ((w - 1).choose t : ℝ) * ⟪f, g⟫ *
        ((N - 2 * w + 1 + t).choose (N - L) : ℝ)) * hcp
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum,
    alt_sum_choose_shift (w - 1) (N - 2 * w + 1) (N - L) (by omega)]
  have hsymm : (N - 2 * w + 1).choose (N - L - (w - 1)) = (N - 2 * w + 1).choose (L - w) := by
    have hk : L - w ≤ N - 2 * w + 1 := by omega
    have hsub : N - 2 * w + 1 - (L - w) = N - L - (w - 1) := by omega
    rw [← hsub, Nat.choose_symm hk]
  rw [hsymm]; push_cast; ring
theorem inner_rawLiftA_rawLiftT {L N w : ℕ} [NeZero L] [NeZero N]
    (hw1 : 1 ≤ w) (hwL : w + 1 ≤ L) (hN : 2 * L ≤ N)
    {f g : EuclideanSpace ℝ (Finset (Fin N))}
    (hf : f ∈ harmonicSubspace N w) (hg : g ∈ harmonicSubspace N w) :
    ⟪rawLiftA (L := L) w f, rawLiftT (L := L) w g⟫ =
      - (((L - 1).factorial * w * (N - 2 * w).choose (L - 1 - w) : ℕ) : ℝ) * ⟪f, g⟫ := by
  unfold rawLiftA rawLiftT; rw [inner_inj_expand]
  have hexp : (∑ x : Fin L → Fin N with Function.Injective x,
      (∑ K₁ ∈ (tailSlots L).powersetCard (w - 1), f.ofLp ((insert 0 K₁).image x)) *
      (∑ K₂ ∈ (tailSlots L).powersetCard w, g.ofLp (K₂.image x))) =
      ∑ K₁ ∈ (tailSlots L).powersetCard (w - 1), ∑ K₂ ∈ (tailSlots L).powersetCard w,
          ∑ x : Fin L → Fin N with Function.Injective x,
            f.ofLp ((insert 0 K₁).image x) * g.ofLp (K₂.image x) := by
    simp_rw [Finset.sum_mul_sum]; rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun K₁ _ ↦ Finset.sum_comm
  rw [hexp]
  let F : ℕ → ℝ := fun t ↦
    (-1 : ℝ) ^ (w - t) * ((L - (2 * w - t)).factorial : ℝ) *
      ((N - (2 * w - t)).choose (L - (2 * w - t)) : ℝ) *
      ((w - t).factorial : ℝ) *
      (w.factorial : ℝ) * ⟪f, g⟫
  have hpair : ∀ K₁ ∈ (tailSlots L).powersetCard (w - 1), ∀ K₂ ∈ (tailSlots L).powersetCard w,
        (∑ x : Fin L → Fin N with Function.Injective x,
          f.ofLp ((insert (0 : Fin L) K₁).image x) * g.ofLp (K₂.image x)) =
          F (K₁ ∩ K₂).card := by
    intro K₁ hK₁ K₂ hK₂
    have h0₁ : (0 : Fin L) ∉ K₁ := fun h0 ↦
      (Finset.mem_erase.1 ((Finset.mem_powersetCard.1 hK₁).1 h0)).1 rfl
    have h0₂ : (0 : Fin L) ∉ K₂ := fun h0 ↦
      (Finset.mem_erase.1 ((Finset.mem_powersetCard.1 hK₂).1 h0)).1 rfl
    have hc₁ : (insert (0 : Fin L) K₁).card = w := by
      rw [Finset.card_insert_of_notMem h0₁, (Finset.mem_powersetCard.1 hK₁).2]; omega
    have hc₂ : K₂.card = w := (Finset.mem_powersetCard.1 hK₂).2
    have hint : (insert (0 : Fin L) K₁ ∩ K₂).card = (K₁ ∩ K₂).card := by
      congr 1; ext i; simp only [Finset.mem_inter, Finset.mem_insert]
      have : i ∈ K₂ → i ≠ 0 := fun hi h0 ↦ h0₂ (h0 ▸ hi)
      tauto
    rw [sum_inj_pair_eq hw1 hc₁ hc₂ hf hg, hint]
  rw [Finset.sum_congr rfl fun K₁ hK₁ ↦ Finset.sum_congr rfl fun K₂ hK₂ ↦ hpair K₁ hK₁ K₂ hK₂,
    sum_pairs_powersetCard_inter (tailSlots L) (w - 1) w (Nat.sub_le w 1) F, card_tailSlots]
  have hterm : ∀ t ∈ Finset.range (w - 1 + 1), (((L - 1).choose (w - 1) * (w - 1).choose t *
        (L - 1 - (w - 1)).choose (w - t) : ℕ) : ℝ) * F t =
        (- (((L - 1).factorial * w : ℕ) : ℝ) * ⟪f, g⟫) *
          ((-1 : ℝ) ^ (w - 1 - t) * ((w - 1).choose t : ℝ) *
            ((N - 2 * w + t).choose (N - L) : ℝ)) := by
    intro t ht; have htw : t ≤ w - 1 := Nat.lt_succ_iff.1 (Finset.mem_range.1 ht); dsimp only [F]
    have hpow1 : (-1 : ℝ) ^ (w - t) = - (-1 : ℝ) ^ (w - 1 - t) := by
      have hwt : w - t = (w - 1 - t) + 1 := by omega
      rw [hwt, pow_succ]; ring
    have hn0 : L - 1 - (w - 1) = L - w := by omega
    have hsubL : L - (2 * w - t) = (L - w) - (w - t) := by omega
    have hsubN : N - (2 * w - t) = N - 2 * w + t := by omega
    rw [hpow1, hn0, hsubL, hsubN]
    have hcm := congrArg (Nat.cast (R := ℝ))
      (choose_mul_fact_symm (L - w) (w - t) (N - 2 * w + t) (N - L) (by omega))
    have hcp := congrArg (Nat.cast (R := ℝ)) (choose_pred_mul_fact L w hw1 (by omega))
    push_cast at hcm hcp ⊢
    linear_combination
      (- (-1 : ℝ) ^ (w - 1 - t) * ((w - 1).choose t : ℝ) * ⟪f, g⟫ *
        (((L - 1).choose (w - 1) : ℝ) * (w.factorial : ℝ))) * hcm +
      (- (-1 : ℝ) ^ (w - 1 - t) * ((w - 1).choose t : ℝ) * ⟪f, g⟫ *
        ((N - 2 * w + t).choose (N - L) : ℝ)) * hcp
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum,
    alt_sum_choose_shift (w - 1) (N - 2 * w) (N - L) (by omega)]
  have hsymm : (N - 2 * w).choose (N - L - (w - 1)) = (N - 2 * w).choose (L - 1 - w) := by
    have hk : L - 1 - w ≤ N - 2 * w := by omega
    have hsub : N - 2 * w - (L - 1 - w) = N - L - (w - 1) := by omega
    rw [← hsub, Nat.choose_symm hk]
  rw [hsymm]; push_cast; ring
theorem inner_rawLiftA_rawLiftT_rel_self {L N w : ℕ} [NeZero L] [NeZero N]
    (hw1 : 1 ≤ w) (hwL : w + 1 ≤ L) (hN : 2 * L ≤ N)
    {f g : EuclideanSpace ℝ (Finset (Fin N))} (hf : f ∈ harmonicSubspace N w) :
    ((N - L + 1 : ℕ) : ℝ) * ⟪rawLiftA (L := L) w f, rawLiftT (L := L) w g⟫ =
      - (w : ℝ) * ⟪rawLiftT (L := L) w f, rawLiftT (L := L) w g⟫ := by
  unfold rawLiftA rawLiftT; rw [inner_inj_expand, inner_inj_expand]
  have heq : Finset.univ.filter (Function.Injective : (Fin L → Fin N) → Prop) =
      Finset.univ.filter (PartialInj (N := N) (insert (0 : Fin L) (tailSlots L))) := by
    ext x
    rw [Finset.mem_filter, Finset.mem_filter, tailSlots, Finset.insert_erase (Finset.mem_univ _),
      partialInj_univ]
  have h0_not : (0 : Fin L) ∉ tailSlots L := Finset.notMem_erase 0 Finset.univ
  rw [heq, sum_partialInj_insert h0_not, sum_partialInj_insert h0_not]
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x hx_mem ↦ ?_
  have hx := (Finset.mem_filter.1 hx_mem).2; set S₁ := (tailSlots L).image x
  have hcS₁ : S₁.card = L - 1 := (card_image_of_partialInj hx).trans (card_tailSlots L)
  have hcCompl : (Finset.univ \ S₁).card = N - L + 1 := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin,
      hcS₁]
    omega
  have hupd_tail : ∀ (y : Fin N) {K : Finset (Fin L)}, K ⊆ tailSlots L →
      K.image (Function.update x 0 y) = K.image x := fun y _ hK ↦
    Finset.image_congr fun i hi ↦
      Function.update_of_ne (fun h0 : i = 0 ↦ h0_not (h0 ▸ hK hi)) y x
  have hrhs : (∑ y ∈ Finset.univ \ S₁,
      (∑ K ∈ (tailSlots L).powersetCard w, f.ofLp (K.image (Function.update x 0 y))) *
      (∑ K ∈ (tailSlots L).powersetCard w, g.ofLp (K.image (Function.update x 0 y)))) =
      ((N - L + 1 : ℕ) : ℝ) * ((∑ K ∈ (tailSlots L).powersetCard w, f.ofLp (K.image x)) *
         (∑ K ∈ (tailSlots L).powersetCard w, g.ofLp (K.image x))) := by
    have hconst : ∀ y ∈ Finset.univ \ S₁,
        (∑ K ∈ (tailSlots L).powersetCard w, f.ofLp (K.image (Function.update x 0 y))) *
        (∑ K ∈ (tailSlots L).powersetCard w, g.ofLp (K.image (Function.update x 0 y))) =
        (∑ K ∈ (tailSlots L).powersetCard w, f.ofLp (K.image x)) *
        (∑ K ∈ (tailSlots L).powersetCard w, g.ofLp (K.image x)) := by
      intro y _
      congr 1 <;> refine Finset.sum_congr rfl fun K hK ↦
        by rw [hupd_tail y (Finset.mem_powersetCard.1 hK).1]
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, hcCompl, nsmul_eq_mul]
  have hlhs : (∑ y ∈ Finset.univ \ S₁, (∑ K' ∈ (tailSlots L).powersetCard (w - 1),
        f.ofLp ((insert 0 K').image (Function.update x 0 y))) *
      (∑ K ∈ (tailSlots L).powersetCard w, g.ofLp (K.image (Function.update x 0 y)))) =
      (- (w : ℝ) * ∑ K ∈ (tailSlots L).powersetCard w, f.ofLp (K.image x)) *
      (∑ K ∈ (tailSlots L).powersetCard w, g.ofLp (K.image x)) := by
    have hcongr : ∀ y ∈ Finset.univ \ S₁, (∑ K' ∈ (tailSlots L).powersetCard (w - 1),
          f.ofLp ((insert 0 K').image (Function.update x 0 y))) *
        (∑ K ∈ (tailSlots L).powersetCard w, g.ofLp (K.image (Function.update x 0 y))) =
        (∑ K' ∈ (tailSlots L).powersetCard (w - 1), f.ofLp (insert y (K'.image x))) *
        (∑ K ∈ (tailSlots L).powersetCard w, g.ofLp (K.image x)) := by
      intro y _; congr 1
      · refine Finset.sum_congr rfl fun K' hK' ↦ ?_
        rw [Finset.image_insert, Function.update_self,
          hupd_tail y (Finset.mem_powersetCard.1 hK').1]
      · refine Finset.sum_congr rfl fun K hK ↦ by rw [hupd_tail y (Finset.mem_powersetCard.1 hK).1]
    rw [Finset.sum_congr rfl hcongr, ← Finset.sum_mul]; congr 1; rw [Finset.sum_comm]
    have hK'_harm : ∀ K' ∈ (tailSlots L).powersetCard (w - 1),
        (∑ y ∈ Finset.univ \ S₁, f.ofLp (insert y (K'.image x))) =
          - ∑ y ∈ S₁ \ K'.image x, f.ofLp (insert y (K'.image x)) := by
      intro K' hK'
      rcases Finset.mem_powersetCard.1 hK' with ⟨hK'sub, hcK'⟩
      have hsub : K'.image x ⊆ S₁ := Finset.image_subset_image hK'sub
      have hcIm : (K'.image x).card = w - 1 :=
        (Finset.card_image_of_injOn fun i hi j hj hij ↦
          hx.1 i (hK'sub hi) j (hK'sub hj) hij).trans hcK'
      have hzero := hf.2 hw1 (K'.image x) hcIm
      have hpart : Finset.univ \ K'.image x = (Finset.univ \ S₁) ∪ (S₁ \ K'.image x) := by
        ext z; simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_univ, true_and]
        have : z ∈ K'.image x → z ∈ S₁ := fun hz ↦ hsub hz
        tauto
      have hdisj : Disjoint (Finset.univ \ S₁) (S₁ \ K'.image x) := by
        rw [Finset.disjoint_left]; intro z hz1 hz2
        exact (Finset.mem_sdiff.1 hz1).2 (Finset.mem_sdiff.1 hz2).1
      rw [hpart, Finset.sum_union hdisj] at hzero; linarith
    rw [Finset.sum_congr rfl hK'_harm, Finset.sum_neg_distrib]
    have hbij1 : (∑ K' ∈ (tailSlots L).powersetCard (w - 1),
        ∑ y ∈ S₁ \ K'.image x, f.ofLp (insert y (K'.image x))) =
        ∑ I ∈ S₁.powersetCard (w - 1), ∑ y ∈ S₁ \ I, f.ofLp (insert y I) := by
      refine Finset.sum_nbij' (fun K' ↦ K'.image x)
        (fun I ↦ (tailSlots L).filter (fun i ↦ x i ∈ I))
        (fun K' hK' ↦ ?_) (fun I hI ↦ ?_) (fun K' hK' ↦ ?_) (fun I hI ↦ ?_) (fun _ _ ↦ rfl)
      · rcases Finset.mem_powersetCard.1 hK' with ⟨hsub, hc⟩
        exact Finset.mem_powersetCard.2 ⟨Finset.image_subset_image hsub,
          (Finset.card_image_of_injOn fun i hi j hj hij ↦ hx.1 i (hsub hi) j (hsub hj) hij).trans
            hc⟩
      · rcases Finset.mem_powersetCard.1 hI with ⟨hsub, hc⟩
        have himg : ((tailSlots L).filter (fun i ↦ x i ∈ I)).image x = I := by
          ext z; simp only [Finset.mem_image, Finset.mem_filter]
          constructor
          · rintro ⟨i, ⟨_, hi⟩, rfl⟩; exact hi
          · intro hz
            rcases Finset.mem_image.1 (hsub hz) with ⟨i, hi, rfl⟩
            exact ⟨i, ⟨hi, hz⟩, rfl⟩
        refine Finset.mem_powersetCard.2 ⟨Finset.filter_subset _ _, ?_⟩
        have hinj := Finset.card_image_of_injOn (s := (tailSlots L).filter (fun i ↦ x i ∈ I))
          (f := x) (fun i hi j hj hij ↦
            hx.1 i (Finset.mem_filter.1 hi).1 j (Finset.mem_filter.1 hj).1 hij)
        rw [himg] at hinj; exact hinj.symm.trans hc
      · have hsub := (Finset.mem_powersetCard.1 hK').1
        ext i; simp only [Finset.mem_filter, Finset.mem_image]
        constructor
        · rintro ⟨hi, j, hj, hji⟩
          exact (hx.1 j (hsub hj) i hi hji) ▸ hj
        · intro hi; exact ⟨hsub hi, i, hi, rfl⟩
      · have hsub := (Finset.mem_powersetCard.1 hI).1
        ext z; simp only [Finset.mem_image, Finset.mem_filter]
        constructor
        · rintro ⟨i, ⟨_, hi⟩, rfl⟩; exact hi
        · intro hz
          rcases Finset.mem_image.1 (hsub hz) with ⟨i, hi, rfl⟩
          exact ⟨i, ⟨hi, hz⟩, rfl⟩
    have hbij2 : (∑ B ∈ S₁.powersetCard w, f.ofLp B) =
        ∑ K ∈ (tailSlots L).powersetCard w, f.ofLp (K.image x) := by
      symm
      refine Finset.sum_nbij' (fun K ↦ K.image x)
        (fun B ↦ (tailSlots L).filter (fun i ↦ x i ∈ B))
        (fun K hK ↦ ?_) (fun B hB ↦ ?_) (fun K hK ↦ ?_) (fun B hB ↦ ?_) (fun _ _ ↦ rfl)
      · rcases Finset.mem_powersetCard.1 hK with ⟨hsub, hc⟩
        exact Finset.mem_powersetCard.2 ⟨Finset.image_subset_image hsub,
          (Finset.card_image_of_injOn fun i hi j hj hij ↦ hx.1 i (hsub hi) j (hsub hj) hij).trans
            hc⟩
      · rcases Finset.mem_powersetCard.1 hB with ⟨hsub, hc⟩
        have himg : ((tailSlots L).filter (fun i ↦ x i ∈ B)).image x = B := by
          ext z; simp only [Finset.mem_image, Finset.mem_filter]
          constructor
          · rintro ⟨i, ⟨_, hi⟩, rfl⟩; exact hi
          · intro hz
            rcases Finset.mem_image.1 (hsub hz) with ⟨i, hi, rfl⟩
            exact ⟨i, ⟨hi, hz⟩, rfl⟩
        refine Finset.mem_powersetCard.2 ⟨Finset.filter_subset _ _, ?_⟩
        have hinj := Finset.card_image_of_injOn (s := (tailSlots L).filter (fun i ↦ x i ∈ B))
          (f := x) (fun i hi j hj hij ↦
            hx.1 i (Finset.mem_filter.1 hi).1 j (Finset.mem_filter.1 hj).1 hij)
        rw [himg] at hinj; exact hinj.symm.trans hc
      · have hsub := (Finset.mem_powersetCard.1 hK).1
        ext i; simp only [Finset.mem_filter, Finset.mem_image]
        constructor
        · rintro ⟨hi, j, hj, hji⟩
          exact (hx.1 j (hsub hj) i hi hji) ▸ hj
        · intro hi; exact ⟨hsub hi, i, hi, rfl⟩
      · have hsub := (Finset.mem_powersetCard.1 hB).1
        ext z; simp only [Finset.mem_image, Finset.mem_filter]
        constructor
        · rintro ⟨i, ⟨_, hi⟩, rfl⟩; exact hi
        · intro hz
          rcases Finset.mem_image.1 (hsub hz) with ⟨i, hi, rfl⟩
          exact ⟨i, ⟨hi, hz⟩, rfl⟩
    rw [hbij1, sum_powersetCard_insert S₁ (w - 1) f.ofLp,
      show w - 1 + 1 = w by omega, hbij2]
    ring
  rw [hlhs, hrhs]; ring
theorem inner_rawLiftT_self {L N w : ℕ} [NeZero L] [NeZero N]
    (hw1 : 1 ≤ w) (hwL : w + 1 ≤ L) (hN : 2 * L ≤ N)
    {f g : EuclideanSpace ℝ (Finset (Fin N))}
    (hf : f ∈ harmonicSubspace N w) (hg : g ∈ harmonicSubspace N w) :
    ⟪rawLiftT (L := L) w f, rawLiftT (L := L) w g⟫ =
      (((L - 1).factorial * (N - L + 1) * (N - 2 * w).choose (L - 1 - w) : ℕ) : ℝ) * ⟪f, g⟫ := by
  have hrel := inner_rawLiftA_rawLiftT_rel_self hw1 hwL hN (g := g) hf
  rw [inner_rawLiftA_rawLiftT hw1 hwL hN hf hg] at hrel
  have hw_ne : (w : ℝ) ≠ 0 := by positivity
  apply mul_left_cancel₀ hw_ne; push_cast at hrel ⊢; linarith
theorem inner_rawLiftA_rawLiftB {L N w : ℕ} [NeZero L] [NeZero N]
    (hw1 : 1 ≤ w) (hwL : w + 1 ≤ L) (hN : 2 * L ≤ N)
    {f g : EuclideanSpace ℝ (Finset (Fin N))}
    (hf : f ∈ harmonicSubspace N w) (hg : g ∈ harmonicSubspace N w) :
    ⟪rawLiftA (L := L) w f, rawLiftB (L := L) w g⟫ = 0 := by
  unfold rawLiftB
  rw [inner_add_right, inner_smul_right, inner_smul_right,
    inner_rawLiftA_self hw1 (by omega) hN hf hg,
    inner_rawLiftA_rawLiftT hw1 hwL hN hf hg]
  have habs : (N - 2 * w + 1) * (N - 2 * w).choose (L - 1 - w) =
      (L - w) * (N - 2 * w + 1).choose (L - w) := by
    set n₀ := N - 2 * w; set k₀ := L - 1 - w
    have hk₀ : k₀ ≤ n₀ := by omega
    have hLsub : L - w = k₀ + 1 := by omega
    rw [hLsub]; have h1 := Nat.choose_mul_factorial_mul_factorial hk₀
    have h2 := Nat.choose_mul_factorial_mul_factorial (Nat.succ_le_succ hk₀)
    rw [Nat.succ_sub_succ_eq_sub, Nat.factorial_succ k₀, Nat.factorial_succ n₀] at h2
    have hpos : 0 < k₀.factorial * (n₀ - k₀).factorial :=
      Nat.mul_pos (Nat.factorial_pos _) (Nat.factorial_pos _)
    apply Nat.eq_of_mul_eq_mul_right hpos
    calc (n₀ + 1) * n₀.choose k₀ * (k₀.factorial * (n₀ - k₀).factorial)
        = (n₀ + 1) * (n₀.choose k₀ * k₀.factorial * (n₀ - k₀).factorial) := by ring
      _ = (n₀ + 1) * n₀.factorial := by rw [h1]
      _ = (n₀ + 1).choose (k₀ + 1) * ((k₀ + 1) * k₀.factorial) * (n₀ - k₀).factorial := h2.symm
      _ = (k₀ + 1) * (n₀ + 1).choose (k₀ + 1) * (k₀.factorial * (n₀ - k₀).factorial) := by ring
  have habsR := congrArg (Nat.cast (R := ℝ)) habs; push_cast at habsR ⊢
  linear_combination (((L - 1).factorial : ℝ) * (w : ℝ) * ⟪f, g⟫) * (-habsR)
theorem inner_rawLiftB_self {L N w : ℕ} [NeZero L] [NeZero N]
    (hw1 : 1 ≤ w) (hwL : w + 1 ≤ L) (hN : 2 * L ≤ N)
    {f g : EuclideanSpace ℝ (Finset (Fin N))}
    (hf : f ∈ harmonicSubspace N w) (hg : g ∈ harmonicSubspace N w) :
    ⟪rawLiftB (L := L) w f, rawLiftB (L := L) w g⟫ =
      (((L - 1).factorial * (N - 2 * w + 1) * (N - w + 1) * (N - L - w + 1) *
        (N - 2 * w).choose (L - 1 - w) : ℕ) : ℝ) * ⟪f, g⟫ := by
  have horth : ⟪rawLiftA (L := L) w f, rawLiftB (L := L) w g⟫ = 0 :=
    inner_rawLiftA_rawLiftB hw1 hwL hN hf hg
  have hexp : ⟪rawLiftB (L := L) w f, rawLiftB (L := L) w g⟫ =
      ((L - w : ℕ) : ℝ) * ⟪rawLiftA (L := L) w f, rawLiftB (L := L) w g⟫ +
      ((N - 2 * w + 1 : ℕ) : ℝ) * ⟪rawLiftT (L := L) w f, rawLiftB (L := L) w g⟫ := by
    unfold rawLiftB; rw [inner_add_left, inner_smul_left, inner_smul_left]; simp
  rw [hexp, horth, mul_zero, zero_add]
  have hTB : ⟪rawLiftT (L := L) w f, rawLiftB (L := L) w g⟫ =
      ((L - w : ℕ) : ℝ) * ⟪rawLiftA (L := L) w g, rawLiftT (L := L) w f⟫ +
      ((N - 2 * w + 1 : ℕ) : ℝ) * ⟪rawLiftT (L := L) w f, rawLiftT (L := L) w g⟫ := by
    conv_lhs => unfold rawLiftB
    rw [inner_add_right, inner_smul_right, inner_smul_right, real_inner_comm (rawLiftA w g)]
  rw [hTB, inner_rawLiftA_rawLiftT hw1 hwL hN hg hf, real_inner_comm g f,
    inner_rawLiftT_self hw1 hwL hN hf hg, real_inner_comm f g]
  push_cast
  rw [Nat.cast_sub (by omega : w ≤ L), Nat.cast_sub (by omega : 2 * w ≤ N),
    Nat.cast_sub (by omega : L ≤ N), Nat.cast_sub (by omega : w ≤ N),
    Nat.cast_sub (by omega : w ≤ N - L), Nat.cast_sub (by omega : L ≤ N)]
  push_cast; ring
theorem inner_rawLiftA_lt {L N w₁ w₂ : ℕ} [NeZero L] [NeZero N]
    (hw₁ : 1 ≤ w₁) (hw₁₂ : w₁ < w₂) {f g : EuclideanSpace ℝ (Finset (Fin N))}
    (hg : g ∈ harmonicSubspace N w₂) :
    ⟪rawLiftA (L := L) w₁ f, rawLiftA (L := L) w₂ g⟫ = 0 ∧
    ⟪rawLiftT (L := L) w₁ f, rawLiftA (L := L) w₂ g⟫ = 0 ∧
    ⟪rawLiftA (L := L) w₁ f, rawLiftT (L := L) w₂ g⟫ = 0 ∧
    ⟪rawLiftT (L := L) w₁ f, rawLiftT (L := L) w₂ g⟫ = 0 := by
  have hw₂ : 1 ≤ w₂ := by omega
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · try unfold rawLiftA
    try unfold rawLiftT
    rw [inner_inj_expand]; simp_rw [Finset.sum_mul_sum]; rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun K₁ hK₁ ↦ ?_
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun K₂ hK₂ ↦ ?_
    first
    | (have h0₁ : (0 : Fin L) ∉ K₁ := fun h0 ↦
         (Finset.mem_erase.1 ((Finset.mem_powersetCard.1 hK₁).1 h0)).1 rfl
       have h0₂ : (0 : Fin L) ∉ K₂ := fun h0 ↦
         (Finset.mem_erase.1 ((Finset.mem_powersetCard.1 hK₂).1 h0)).1 rfl
       have hc₁ : (insert (0 : Fin L) K₁).card < w₂ := by
         rw [Finset.card_insert_of_notMem h0₁, (Finset.mem_powersetCard.1 hK₁).2]; omega
       have hc₂ : (insert (0 : Fin L) K₂).card = w₂ := by
         rw [Finset.card_insert_of_notMem h0₂, (Finset.mem_powersetCard.1 hK₂).2]; omega
       exact sum_inj_pair_lt hw₂ hc₁ hc₂ f.ofLp hg)
    | (have h0₂ : (0 : Fin L) ∉ K₂ := fun h0 ↦
         (Finset.mem_erase.1 ((Finset.mem_powersetCard.1 hK₂).1 h0)).1 rfl
       have hc₁ : K₁.card < w₂ := by rw [(Finset.mem_powersetCard.1 hK₁).2]; omega
       have hc₂ : (insert (0 : Fin L) K₂).card = w₂ := by
         rw [Finset.card_insert_of_notMem h0₂, (Finset.mem_powersetCard.1 hK₂).2]; omega
       exact sum_inj_pair_lt hw₂ hc₁ hc₂ f.ofLp hg)
    | (have h0₁ : (0 : Fin L) ∉ K₁ := fun h0 ↦
         (Finset.mem_erase.1 ((Finset.mem_powersetCard.1 hK₁).1 h0)).1 rfl
       have hc₁ : (insert (0 : Fin L) K₁).card < w₂ := by
         rw [Finset.card_insert_of_notMem h0₁, (Finset.mem_powersetCard.1 hK₁).2]; omega
       have hc₂ : K₂.card = w₂ := (Finset.mem_powersetCard.1 hK₂).2
       exact sum_inj_pair_lt hw₂ hc₁ hc₂ f.ofLp hg)
    | (have hc₁ : K₁.card < w₂ := by rw [(Finset.mem_powersetCard.1 hK₁).2]; omega
       have hc₂ : K₂.card = w₂ := (Finset.mem_powersetCard.1 hK₂).2
       exact sum_inj_pair_lt hw₂ hc₁ hc₂ f.ofLp hg)
theorem inner_b0TupleVec_self {L N : ℕ} [NeZero N] (hLN : L ≤ N) :
    ⟪b0TupleVec L N, b0TupleVec L N⟫ = 1 := by
  unfold b0TupleVec; rw [inner_smul_left, inner_smul_right, inner_inj_expand]
  simp only [mul_one, card_injTuple, RCLike.conj_to_real]
  have hpos : (0 : ℝ) < ((L.factorial * N.choose L : ℕ) : ℝ) := by
    exact_mod_cast Nat.mul_pos (Nat.factorial_pos L) (Nat.choose_pos hLN)
  field_simp; exact (Real.sq_sqrt hpos.le).symm
theorem b0TupleVec_zero_eq_zero {L N : ℕ} (hL : 2 ≤ L) [NeZero N] :
    (b0TupleVec L N).ofLp (fun _ ↦ 0) = 0 := by
  unfold b0TupleVec; simp only [PiLp.smul_apply, smul_eq_mul, mul_eq_zero]
  right
  change (if Function.Injective (fun _ : Fin L ↦ (0 : Fin N)) then (1 : ℝ) else 0) = 0
  rw [ite_eq_right_iff]; intro hinj
  have h01 : (⟨0, by omega⟩ : Fin L) = ⟨1, by omega⟩ := hinj rfl
  have hv := congrArg Fin.val h01; simp at hv
theorem inner_b0TupleVec_rawLift {L N w : ℕ} [NeZero L] [NeZero N]
    (hw1 : 1 ≤ w) {g : EuclideanSpace ℝ (Finset (Fin N))} (hg : g ∈ harmonicSubspace N w) :
    ⟪b0TupleVec L N, rawLiftA (L := L) w g⟫ = 0 ∧
    ⟪b0TupleVec L N, rawLiftT (L := L) w g⟫ = 0 := by
  refine ⟨?_, ?_⟩ <;>
  · unfold b0TupleVec
    try unfold rawLiftA
    try unfold rawLiftT
    rw [inner_smul_left, inner_inj_expand]; simp only [RCLike.conj_to_real]
    simp_rw [one_mul]; rw [Finset.sum_comm]
    refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun K hK ↦ ?_)
    first
    | (have h0₁ : (0 : Fin L) ∉ K := fun h0 ↦
         (Finset.mem_erase.1 ((Finset.mem_powersetCard.1 hK).1 h0)).1 rfl
       have hc : (insert (0 : Fin L) K).card = w := by
         rw [Finset.card_insert_of_notMem h0₁, (Finset.mem_powersetCard.1 hK).2]; omega
       simpa using sum_inj_pair_lt hw1 (K := ∅) (by simp; omega) hc (fun _ ↦ 1) hg)
    | (have hc : K.card = w := (Finset.mem_powersetCard.1 hK).2
       simpa using sum_inj_pair_lt hw1 (K := ∅) (by simp; omega) hc (fun _ ↦ 1) hg)
theorem sum_powersetCard_inter_card {α : Type*} [DecidableEq α] {U₀ H₀ : Finset α}
    (hHU : H₀ ⊆ U₀) (k : ℕ) (F : ℕ → ℝ) :
    (∑ K ∈ U₀.powersetCard k, F (H₀ ∩ K).card) =
      ∑ j ∈ Finset.range (k + 1),
        ((H₀.card.choose j * (U₀.card - H₀.card).choose (k - j) : ℕ) : ℝ) * F j := by
  have hbij : (∑ K ∈ U₀.powersetCard k, F (H₀ ∩ K).card) = ∑ p ∈ (Finset.range (k + 1)).sigma
        (fun j ↦ H₀.powersetCard j ×ˢ (U₀ \ H₀).powersetCard (k - j)), F p.1 := by
    refine Finset.sum_nbij' (fun K ↦ ⟨(H₀ ∩ K).card, H₀ ∩ K, K \ H₀⟩) (fun p ↦ p.2.1 ∪ p.2.2)
      (fun K hK ↦ ?_) (fun p hp ↦ ?_) (fun K _ ↦ by ext x; simp; tauto)
      (fun p hp ↦ ?_) (fun _ _ ↦ rfl)
    · rcases Finset.mem_powersetCard.1 hK with ⟨hKU, hcK⟩
      have hjk : (H₀ ∩ K).card ≤ k := hcK ▸ Finset.card_le_card Finset.inter_subset_right
      refine Finset.mem_sigma.2 ⟨Finset.mem_range.2 (Nat.lt_succ_of_le hjk),
        Finset.mem_product.2 ⟨Finset.mem_powersetCard.2 ⟨Finset.inter_subset_left, rfl⟩,
          Finset.mem_powersetCard.2 ⟨Finset.sdiff_subset_sdiff hKU (Finset.Subset.refl H₀), ?_⟩⟩⟩
      dsimp only; have := Finset.card_inter_add_card_sdiff K H₀
      rw [Finset.inter_comm] at this; omega
    · rcases Finset.mem_sigma.1 hp with ⟨hj, hp2⟩
      have hjk : p.1 ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
      rcases Finset.mem_product.1 hp2 with ⟨hA, hB⟩
      rcases Finset.mem_powersetCard.1 hA with ⟨hAH, hcA⟩
      rcases Finset.mem_powersetCard.1 hB with ⟨hBU, hcB⟩
      have hdisj : Disjoint p.2.1 p.2.2 := Disjoint.mono hAH hBU disjoint_sdiff_self_right
      refine Finset.mem_powersetCard.2 ⟨Finset.union_subset (hAH.trans hHU)
        (hBU.trans Finset.sdiff_subset), ?_⟩
      rw [Finset.card_union_of_disjoint hdisj, hcA, hcB]; omega
    · rcases Finset.mem_sigma.1 hp with ⟨_, hp2⟩
      rcases Finset.mem_product.1 hp2 with ⟨hA, hB⟩
      rcases Finset.mem_powersetCard.1 hA with ⟨hAH, hcA⟩
      rcases Finset.mem_powersetCard.1 hB with ⟨hBU, _⟩
      have h1 : H₀ ∩ (p.2.1 ∪ p.2.2) = p.2.1 := by
        ext x
        simp only [Finset.mem_inter, Finset.mem_union]
        have hxB : x ∈ p.2.2 → x ∉ H₀ := fun hx ↦ (Finset.mem_sdiff.1 (hBU hx)).2
        have hxA : x ∈ p.2.1 → x ∈ H₀ := fun hx ↦ hAH hx
        tauto
      have h2 : (p.2.1 ∪ p.2.2) \ H₀ = p.2.2 := by
        ext x
        simp only [Finset.mem_sdiff, Finset.mem_union]
        have hxB : x ∈ p.2.2 → x ∉ H₀ := fun hx ↦ (Finset.mem_sdiff.1 (hBU hx)).2
        have hxA : x ∈ p.2.1 → x ∈ H₀ := fun hx ↦ hAH hx
        tauto
      refine Sigma.ext (by rw [h1, hcA]) (heq_of_eq (Prod.ext h1 h2))
  rw [hbij, Finset.sum_sigma]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  dsimp only
  rw [Finset.sum_const, Finset.card_product, Finset.card_powersetCard, Finset.card_powersetCard,
    Finset.card_sdiff_of_subset hHU, nsmul_eq_mul, Nat.cast_mul]
theorem sum_choose_hockey (u m : ℕ) :
    (∑ j ∈ Finset.range (m + 1), (u + j).choose j) = (u + m + 1).choose m := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Finset.sum_range_succ, ih]
      have h1 : u + (m + 1) + 1 = (u + m + 1) + 1 := by omega
      have h2 : u + (m + 1) = u + m + 1 := by omega
      rw [h1, h2, Nat.choose_succ_succ (u + m + 1) m, add_comm]
theorem upper_vandermonde :
    ∀ (w r u : ℕ), w ≤ r →
      (∑ j ∈ Finset.range (w + 1), (r - j).choose (w - j) * (u + j).choose j) =
        (r + u + 1).choose w
  | 0, r, u, _ => by simp
  | w + 1, r, u, hwr => by
      obtain ⟨d, rfl⟩ : ∃ d, r = w + 1 + d := ⟨r - (w + 1), by omega⟩
      induction d with
      | zero =>
          simp only [add_zero]
          have h1 : ∀ j ∈ Finset.range (w + 1 + 1),
              (w + 1 - j).choose (w + 1 - j) * (u + j).choose j = (u + j).choose j :=
            fun j _ ↦ by simp
          rw [Finset.sum_congr rfl h1, sum_choose_hockey u (w + 1)]; congr 1; omega
      | succ d ih =>
          have hwr' : w + 1 ≤ w + 1 + d := by omega
          have ihd := ih hwr'
          have ihw := upper_vandermonde w (w + 1 + d) u (by omega)
          rw [Finset.sum_range_succ] at ihd; rw [Finset.sum_range_succ]
          have htop1 : (w + 1 + (d + 1) - (w + 1)).choose (w + 1 - (w + 1)) = 1 := by simp
          have htop2 : (w + 1 + d - (w + 1)).choose (w + 1 - (w + 1)) = 1 := by simp
          rw [htop1]; rw [htop2] at ihd
          have hsplit : (∑ x ∈ Finset.range (w + 1),
              (w + 1 + (d + 1) - x).choose (w + 1 - x) * (u + x).choose x) =
              (∑ x ∈ Finset.range (w + 1), (w + 1 + d - x).choose (w + 1 - x) * (u + x).choose x) +
              (∑ x ∈ Finset.range (w + 1),
                (w + 1 + d - x).choose (w - x) * (u + x).choose x) := by
            rw [← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl fun x hx ↦ ?_
            have hxw : x ≤ w := Nat.lt_succ_iff.1 (Finset.mem_range.1 hx)
            have hc : (w + 1 + (d + 1) - x).choose (w + 1 - x) =
                (w + 1 + d - x).choose (w + 1 - x) + (w + 1 + d - x).choose (w - x) := by
              have ha : w + 1 + (d + 1) - x = (w + 1 + d - x) + 1 := by omega
              have hb : w + 1 - x = (w - x) + 1 := by omega
              rw [ha, hb, Nat.choose_succ_succ (w + 1 + d - x) (w - x), Nat.add_comm]
            rw [hc, Nat.right_distrib]
          have hgoal : w + 1 + (d + 1) + u + 1 = (w + 1 + d + u + 1) + 1 := by omega
          rw [hsplit, ihw, hgoal, Nat.choose_succ_succ (w + 1 + d + u + 1) w]; linarith
/-- Unnormalized factorial harmonic vector `q_w^{\mathrm{raw}}` for `R ⊆ Fin N`. -/
def qVecRaw {N : ℕ} (R : Finset (Fin N)) (w : ℕ) : EuclideanSpace ℝ (Finset (Fin N)) :=
  WithLp.toLp 2 fun S ↦
    if S.card = w then
      (-1 : ℝ) ^ (w + (S ∩ R).card) *
        (((R.card - (S ∩ R).card).factorial *
          (N - R.card - w + (S ∩ R).card).factorial : ℕ) : ℝ)
    else 0
theorem qVecRaw_mem_harmonic {N r w : ℕ} {R : Finset (Fin N)}
    (hw1 : 1 ≤ w) (hwr : w ≤ r) (hrN : r + w ≤ N) (hR : R.card = r) :
    qVecRaw R w ∈ harmonicSubspace N w := by
  refine ⟨fun s hs ↦ ?_, fun _ t ht ↦ ?_⟩
  · unfold qVecRaw; simp [hs]
  · set j := (t ∩ R).card; have hjt : j ≤ w - 1 := ht ▸ Finset.card_le_card Finset.inter_subset_left
    have hpart : Finset.univ \ t = (R \ t) ∪ ((Finset.univ \ R) \ t) := by
      ext y; simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_univ, true_and]; tauto
    have hdisj : Disjoint (R \ t) ((Finset.univ \ R) \ t) := by
      rw [Finset.disjoint_left]; intro y hy1 hy2
      exact (Finset.mem_sdiff.1 (Finset.mem_sdiff.1 hy2).1).2 (Finset.mem_sdiff.1 hy1).1
    rw [hpart, Finset.sum_union hdisj]
    have hc1 : (R \ t).card = r - j := by
      have := Finset.card_inter_add_card_sdiff R t; rw [Finset.inter_comm, hR] at this; omega
    have hc2 : ((Finset.univ \ R) \ t).card = N - r - w + 1 + j := by
      have h1 := Finset.card_inter_add_card_sdiff (Finset.univ \ R) t
      have h2 : ((Finset.univ \ R) ∩ t).card = w - 1 - j := by
        have h3 : (Finset.univ \ R) ∩ t = t \ R := by ext y; simp; tauto
        have h4 := Finset.card_inter_add_card_sdiff t R; rw [h3]; omega
      have h5 : (Finset.univ \ R).card = N - r := by
        rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin,
          hR]
      omega
    have hs1 : ∀ y ∈ R \ t, (qVecRaw R w).ofLp (insert y t) = (-1 : ℝ) ^ (w + j + 1) *
          (((r - (j + 1)).factorial * (N - r - w + (j + 1)).factorial : ℕ) : ℝ) := by
      intro y hy
      rcases Finset.mem_sdiff.1 hy with ⟨hyR, hyt⟩
      have hc : (insert y t).card = w := by rw [Finset.card_insert_of_notMem hyt, ht]; omega
      have hint : (insert y t ∩ R) = insert y (t ∩ R) := by
        ext z; simp only [Finset.mem_inter, Finset.mem_insert]
        have : z = y → z ∈ R := fun h ↦ h ▸ hyR
        tauto
      have hcint : (insert y t ∩ R).card = j + 1 := by
        rw [hint, Finset.card_insert_of_notMem (fun h ↦ hyt (Finset.mem_of_mem_inter_left h))]
      unfold qVecRaw; simp [hc, hcint, hR, add_assoc]
    have hs2 : ∀ y ∈ (Finset.univ \ R) \ t, (qVecRaw R w).ofLp (insert y t) = (-1 : ℝ) ^ (w + j) *
          (((r - j).factorial * (N - r - w + j).factorial : ℕ) : ℝ) := by
      intro y hy
      rcases Finset.mem_sdiff.1 hy with ⟨hyc, hyt⟩
      have hyR : y ∉ R := (Finset.mem_sdiff.1 hyc).2
      have hc : (insert y t).card = w := by rw [Finset.card_insert_of_notMem hyt, ht]; omega
      have hint : (insert y t ∩ R) = t ∩ R := by
        ext z; simp only [Finset.mem_inter, Finset.mem_insert]
        have : z = y → z ∉ R := fun h ↦ h ▸ hyR
        tauto
      have hcint : (insert y t ∩ R).card = j := by rw [hint]
      unfold qVecRaw; simp [hc, hcint, hR]
    rw [Finset.sum_congr rfl hs1, Finset.sum_congr rfl hs2, Finset.sum_const, Finset.sum_const,
      hc1, hc2, nsmul_eq_mul, nsmul_eq_mul]
    have hf1 : (r - j) * (r - (j + 1)).factorial = (r - j).factorial := by
      have hrj : r - j = (r - (j + 1)) + 1 := by omega
      conv_rhs => rw [hrj, Nat.factorial_succ]
      rw [← hrj]
    have hf2 : (N - r - w + (j + 1)).factorial =
        (N - r - w + 1 + j) * (N - r - w + j).factorial := by
      have hNj : N - r - w + (j + 1) = (N - r - w + j) + 1 := by omega
      have hNj2 : N - r - w + 1 + j = N - r - w + j + 1 := by omega
      rw [hNj, hNj2, Nat.factorial_succ]
    have hnat : (r - j) * ((r - (j + 1)).factorial * (N - r - w + (j + 1)).factorial) =
        (N - r - w + 1 + j) * ((r - j).factorial * (N - r - w + j).factorial) := by
      calc (r - j) * ((r - (j + 1)).factorial * (N - r - w + (j + 1)).factorial)
          = ((r - j) * (r - (j + 1)).factorial) * (N - r - w + (j + 1)).factorial := by ring
        _ = (r - j).factorial * ((N - r - w + 1 + j) * (N - r - w + j).factorial) := by
            rw [hf1, hf2]
        _ = (N - r - w + 1 + j) * ((r - j).factorial * (N - r - w + j).factorial) := by ring
    have hnatR := congrArg (Nat.cast (R := ℝ)) hnat; push_cast at hnatR ⊢
    rw [pow_succ (-1 : ℝ) (w + j)]
    linear_combination ((-1 : ℝ) ^ (w + j) * (-1 : ℝ)) * hnatR
theorem inner_qVecRaw_self {N r w : ℕ} {R : Finset (Fin N)}
    (hwr : w ≤ r) (hrN : r + w ≤ N) (hR : R.card = r) :
    ⟪qVecRaw R w, qVecRaw R w⟫ = (swLQNormSqNat N r w : ℝ) := by
  rw [PiLp.inner_apply]; simp only [RCLike.inner_apply, RCLike.conj_to_real]
  have hsub : (∑ S : Finset (Fin N), (qVecRaw R w).ofLp S * (qVecRaw R w).ofLp S) =
      ∑ S ∈ (Finset.univ : Finset (Fin N)).powersetCard w,
        (qVecRaw R w).ofLp S * (qVecRaw R w).ofLp S := by
    symm
    refine Finset.sum_subset (Finset.subset_univ _) fun S _ hS ↦ ?_
    have hne : S.card ≠ w := fun hc ↦ hS (Finset.mem_powersetCard.2 ⟨Finset.subset_univ S, hc⟩)
    unfold qVecRaw; simp [hne]
  rw [hsub]
  let F : ℕ → ℝ := fun j ↦ (((r - j).factorial * (N - r - w + j).factorial : ℕ) : ℝ) ^ 2
  have hterm : ∀ S ∈ (Finset.univ : Finset (Fin N)).powersetCard w,
      (qVecRaw R w).ofLp S * (qVecRaw R w).ofLp S = F (R ∩ S).card := by
    intro S hS; have hc : S.card = w := (Finset.mem_powersetCard.1 hS).2; unfold qVecRaw; dsimp only
    rw [Finset.inter_comm S R]; simp only [hc, ↓reduceIte, hR, F]
    have hpow : (-1 : ℝ) ^ (w + (R ∩ S).card) * (-1 : ℝ) ^ (w + (R ∩ S).card) = 1 := by
      rw [← pow_add, ← two_mul, pow_mul]; norm_num
    linear_combination
      ((((r - (R ∩ S).card).factorial * (N - r - w + (R ∩ S).card).factorial : ℕ) : ℝ) ^ 2) * hpow
  rw [Finset.sum_congr rfl hterm, sum_powersetCard_inter_card (Finset.subset_univ R) w F,
    Finset.card_univ, Fintype.card_fin, hR]
  have hj_eq : ∀ j ∈ Finset.range (w + 1), ((r.choose j * (N - r).choose (w - j) : ℕ) : ℝ) * F j =
        ((r.factorial * (N - r).factorial * (r - w).factorial * (N - r - w).factorial : ℕ) : ℝ) *
          (((r - j).choose (w - j) * (N - r - w + j).choose j : ℕ) : ℝ) := by
    intro j hj; have hjw : j ≤ w := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj); dsimp only [F]
    have hnat : r.choose j * (N - r).choose (w - j) *
        (((r - j).factorial * (N - r - w + j).factorial) *
         ((r - j).factorial * (N - r - w + j).factorial)) =
        (r.factorial * (N - r).factorial * (r - w).factorial * (N - r - w).factorial) *
          ((r - j).choose (w - j) * (N - r - w + j).choose j) := by
      have h1 := Nat.choose_mul_factorial_mul_factorial (hjw.trans hwr)
      have h2 := Nat.choose_mul_factorial_mul_factorial (by omega : w - j ≤ N - r)
      have h2sub : N - r - (w - j) = N - r - w + j := by omega
      rw [h2sub] at h2
      have h3 := Nat.choose_mul_factorial_mul_factorial (by omega : w - j ≤ r - j)
      have h3sub : r - j - (w - j) = r - w := by omega
      rw [h3sub] at h3
      have h4 := Nat.choose_mul_factorial_mul_factorial (by omega : j ≤ N - r - w + j)
      have h4sub : N - r - w + j - j = N - r - w := by omega
      rw [h4sub] at h4
      have hpos : 0 < j.factorial * (w - j).factorial :=
        Nat.mul_pos (Nat.factorial_pos _) (Nat.factorial_pos _)
      apply Nat.eq_of_mul_eq_mul_right hpos
      calc r.choose j * (N - r).choose (w - j) *
            (((r - j).factorial * (N - r - w + j).factorial) *
             ((r - j).factorial * (N - r - w + j).factorial)) *
            (j.factorial * (w - j).factorial)
          = (r.choose j * j.factorial * (r - j).factorial) *
            ((N - r).choose (w - j) * (w - j).factorial * (N - r - w + j).factorial) *
            (r - j).factorial * (N - r - w + j).factorial := by ring
        _ = r.factorial * (N - r).factorial *
            ((r - j).choose (w - j) * (w - j).factorial * (r - w).factorial) *
            ((N - r - w + j).choose j * j.factorial * (N - r - w).factorial) := by
            rw [h1, h2, ← h3, ← h4]
        _ = (r.factorial * (N - r).factorial * (r - w).factorial * (N - r - w).factorial) *
              ((r - j).choose (w - j) * (N - r - w + j).choose j) *
            (j.factorial * (w - j).factorial) := by ring
    have hnatR := congrArg (Nat.cast (R := ℝ)) hnat; push_cast at hnatR ⊢; simpa [sq] using hnatR
  rw [Finset.sum_congr rfl hj_eq, ← Finset.mul_sum]
  have hv := congrArg (Nat.cast (R := ℝ)) (upper_vandermonde w r (N - r - w) hwr)
  have hru : r + (N - r - w) + 1 = N - w + 1 := by omega
  rw [hru] at hv; push_cast at hv; simp_rw [Nat.cast_mul]; rw [hv]
  unfold swLQNormSqNat; push_cast; ring
/-- Normalized `R`-harmonic vector `q_w ∈ harmonicSubspace N w` (`‖q_w‖ = 1`). -/
noncomputable def qVec {N : ℕ} (R : Finset (Fin N)) (w : ℕ) : EuclideanSpace ℝ (Finset (Fin N)) :=
  (1 / √(swLQNormSqNat N R.card w : ℝ)) • qVecRaw R w
theorem qVec_mem_harmonic {N r w : ℕ} {R : Finset (Fin N)}
    (hw1 : 1 ≤ w) (hwr : w ≤ r) (hrN : r + w ≤ N) (hR : R.card = r) :
    qVec R w ∈ harmonicSubspace N w :=
  (harmonicSubspace N w).smul_mem _ (qVecRaw_mem_harmonic hw1 hwr hrN hR)
theorem inner_qVec_self {N r w : ℕ} {R : Finset (Fin N)}
    (hwr : w ≤ r) (hrN : r + w ≤ N) (hR : R.card = r) :
    ⟪qVec R w, qVec R w⟫ = 1 := by
  unfold qVec; rw [inner_smul_left, inner_smul_right, inner_qVecRaw_self hwr hrN hR, hR]
  simp only [RCLike.conj_to_real]
  have hpos : (0 : ℝ) < (swLQNormSqNat N r w : ℝ) := by
    unfold swLQNormSqNat
    exact_mod_cast Nat.mul_pos
      (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (Nat.factorial_pos _) (Nat.factorial_pos _))
        (Nat.factorial_pos _)) (Nat.factorial_pos _))
      (Nat.choose_pos (by omega))
  field_simp; exact (Real.sq_sqrt hpos.le).symm
theorem sum_powersetCard_erase {α : Type*} [DecidableEq α] (U₀ : Finset α) (k : ℕ)
    (g : Finset α → ℝ) :
    ((U₀.card - k : ℕ) : ℝ) * (∑ K' ∈ U₀.powersetCard k, g K') =
      ∑ K ∈ U₀.powersetCard (k + 1), ∑ i ∈ K, g (K.erase i) := by
  have hlhs : ((U₀.card - k : ℕ) : ℝ) * (∑ K' ∈ U₀.powersetCard k, g K') =
      ∑ p ∈ (U₀.powersetCard k).sigma (fun K' ↦ U₀ \ K'), g p.1 := by
    rw [Finset.sum_sigma, Finset.mul_sum]
    refine Finset.sum_congr rfl fun K' hK' ↦ ?_
    rcases Finset.mem_powersetCard.1 hK' with ⟨hsub, hc⟩
    dsimp only; rw [Finset.sum_const, Finset.card_sdiff_of_subset hsub, hc, nsmul_eq_mul]
  have hrhs : (∑ K ∈ U₀.powersetCard (k + 1), ∑ i ∈ K, g (K.erase i)) =
      ∑ q ∈ (U₀.powersetCard (k + 1)).sigma (fun K ↦ K), g (q.1.erase q.2) :=
    (Finset.sum_sigma (U₀.powersetCard (k + 1)) (fun K ↦ K) (fun q ↦ g (q.1.erase q.2))).symm
  rw [hlhs, hrhs]
  refine Finset.sum_nbij' (fun p ↦ ⟨insert p.2 p.1, p.2⟩) (fun q ↦ ⟨q.1.erase q.2, q.2⟩)
    (fun p hp ↦ ?_) (fun q hq ↦ ?_) (fun p hp ↦ ?_) (fun q hq ↦ ?_) (fun p hp ↦ ?_)
  · rcases Finset.mem_sigma.1 hp with ⟨hK', hi⟩
    rcases Finset.mem_powersetCard.1 hK' with ⟨hsub, hc⟩
    rcases Finset.mem_sdiff.1 hi with ⟨hiU, hiK'⟩
    exact Finset.mem_sigma.2 ⟨Finset.mem_powersetCard.2
      ⟨Finset.insert_subset_iff.2 ⟨hiU, hsub⟩, by rw [Finset.card_insert_of_notMem hiK', hc]⟩,
      Finset.mem_insert_self _ _⟩
  · rcases Finset.mem_sigma.1 hq with ⟨hK, hi⟩
    rcases Finset.mem_powersetCard.1 hK with ⟨hsub, hc⟩
    exact Finset.mem_sigma.2 ⟨Finset.mem_powersetCard.2
      ⟨(Finset.erase_subset _ _).trans hsub, by rw [Finset.card_erase_of_mem hi, hc]; omega⟩,
      Finset.mem_sdiff.2 ⟨hsub hi, Finset.notMem_erase _ _⟩⟩
  · rcases Finset.mem_sigma.1 hp with ⟨_, hi⟩
    have hiK' : p.2 ∉ p.1 := (Finset.mem_sdiff.1 hi).2
    exact Sigma.ext (Finset.erase_insert hiK') (heq_of_eq rfl)
  · rcases Finset.mem_sigma.1 hq with ⟨_, hi⟩
    exact Sigma.ext (Finset.insert_erase hi) (heq_of_eq rfl)
  · rcases Finset.mem_sigma.1 hp with ⟨_, hi⟩
    have hiK' : p.2 ∉ p.1 := (Finset.mem_sdiff.1 hi).2; dsimp only; rw [Finset.erase_insert hiK']
theorem rawLiftB_qVecRaw_of_notMem {L N r w : ℕ} [NeZero L]
    (hw1 : 1 ≤ w) (hwL : w + 1 ≤ L) (hwr : w + 1 ≤ r) (hrN : r + L ≤ N)
    {R : Finset (Fin N)} (hR : R.card = r) {x : Fin L → Fin N} (hx0 : x 0 ∉ R) :
    (rawLiftB (L := L) w (qVecRaw R w)).ofLp x =
      - (((N - r - w) * (N - w + 1) : ℕ) : ℝ) *
        (rawLiftA (L := L) (w + 1) (qVecRaw R (w + 1))).ofLp x := by
  unfold rawLiftB rawLiftA rawLiftT; simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  by_cases hx : Function.Injective x
  · simp only [hx, ↓reduceIte, Nat.add_sub_cancel]
    have hcard_er : ((tailSlots L).card - (w - 1)) = L - w := by rw [card_tailSlots]; omega
    have hw_succ : w - 1 + 1 = w := by omega
    have her := sum_powersetCard_erase (tailSlots L) (w - 1)
      (fun K' ↦ (qVecRaw R w).ofLp ((insert (0 : Fin L) K').image x))
    rw [hcard_er, hw_succ] at her
    rw [her, Finset.mul_sum, ← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun K hK ↦ ?_
    rcases Finset.mem_powersetCard.1 hK with ⟨hKsub, hcK⟩
    have h0K : (0 : Fin L) ∉ K := fun h0 ↦ (Finset.mem_erase.1 (hKsub h0)).1 rfl
    set H := K.filter (fun i ↦ x i ∈ R)
    set j := H.card; have hjw : j ≤ w := hcK ▸ Finset.card_le_card (Finset.filter_subset _ K)
    have hcH_not : (K.filter (fun i ↦ x i ∉ R)).card = w - j := by
      have h1 := Finset.sum_filter_add_sum_filter_not K (fun i ↦ x i ∈ R) (fun _ ↦ (1 : ℕ))
      simp only [Finset.sum_const, smul_eq_mul, mul_one, hcK] at h1
      have hj_def : (K.filter (fun i ↦ x i ∈ R)).card = j := rfl
      rw [hj_def] at h1; omega
    have himgK_card : (K.image x).card = w :=
      (Finset.card_image_of_injOn fun idx1 _ idx2 _ hab ↦ hx hab).trans hcK
    have himgK_hit : (K.image x ∩ R).card = j := by
      have heq : K.image x ∩ R = H.image x := by
        ext z; simp only [Finset.mem_inter, Finset.mem_image, H, Finset.mem_filter]
        constructor
        · rintro ⟨⟨idx, hidx, rfl⟩, hzR⟩; exact ⟨idx, ⟨hidx, hzR⟩, rfl⟩
        · rintro ⟨idx, ⟨hidx, hidxR⟩, rfl⟩; exact ⟨⟨idx, hidx, rfl⟩, hidxR⟩
      rw [heq, Finset.card_image_of_injOn fun idx1 _ idx2 _ hab ↦ hx hab]
    have himg0K_card : ((insert (0 : Fin L) K).image x).card = w + 1 := by
      rw [Finset.card_image_of_injOn fun idx1 _ idx2 _ hab ↦ hx hab,
        Finset.card_insert_of_notMem h0K, hcK]
    have himg0K_hit : ((insert (0 : Fin L) K).image x ∩ R).card = j := by
      have heq : (insert (0 : Fin L) K).image x ∩ R = K.image x ∩ R := by
        rw [Finset.image_insert]
        ext z; simp only [Finset.mem_inter, Finset.mem_insert]
        have : z = x 0 → z ∉ R := fun h ↦ h ▸ hx0
        tauto
      rw [heq, himgK_hit]
    rw [← Finset.sum_filter_add_sum_filter_not K (fun i ↦ x i ∈ R)]
    set u := N - r - w
    have hu1 : 1 ≤ u := by omega
    have hs_in : ∀ i ∈ K.filter (fun i ↦ x i ∈ R),
        (qVecRaw R w).ofLp ((insert (0 : Fin L) (K.erase i)).image x) = - (-1 : ℝ) ^ (w + j) *
            (((r + 1 - j) * (r - j).factorial * (u - 1 + j).factorial : ℕ) : ℝ) := by
      intro i hi
      rcases Finset.mem_filter.1 hi with ⟨hiK, hxiR⟩
      have hj1 : 1 ≤ j := Finset.card_pos.2 ⟨i, hi⟩
      have h0er : (0 : Fin L) ∉ K.erase i := fun h0 ↦ h0K (Finset.mem_of_mem_erase h0)
      have hcard : ((insert (0 : Fin L) (K.erase i)).image x).card = w := by
        rw [Finset.card_image_of_injOn fun idx1 _ idx2 _ hab ↦ hx hab,
          Finset.card_insert_of_notMem h0er, Finset.card_erase_of_mem hiK, hcK]; omega
      have hhit : ((insert (0 : Fin L) (K.erase i)).image x ∩ R).card = j - 1 := by
        have heq1 : (insert (0 : Fin L) (K.erase i)).image x ∩ R = (K.erase i).image x ∩ R := by
          rw [Finset.image_insert]
          ext z; simp only [Finset.mem_inter, Finset.mem_insert]
          have : z = x 0 → z ∉ R := fun h ↦ h ▸ hx0
          tauto
        have heq2 : (K.erase i).image x ∩ R = (H.erase i).image x := by
          ext z; simp only [Finset.mem_inter, Finset.mem_image, Finset.mem_erase, H,
            Finset.mem_filter]
          constructor
          · rintro ⟨⟨idx, ⟨hidx_ne, hidxK⟩, rfl⟩, hidxR⟩
            exact ⟨idx, ⟨hidx_ne, hidxK, hidxR⟩, rfl⟩
          · rintro ⟨idx, ⟨hidx_ne, hidxK, hidxR⟩, rfl⟩
            exact ⟨⟨idx, ⟨hidx_ne, hidxK⟩, rfl⟩, hidxR⟩
        rw [heq1, heq2, Finset.card_image_of_injOn fun idx1 _ idx2 _ hab ↦ hx hab,
          Finset.card_erase_of_mem hi]
      unfold qVecRaw; simp only [hcard, ↓reduceIte, hhit, hR]
      have hpow : (-1 : ℝ) ^ (w + (j - 1)) = - (-1 : ℝ) ^ (w + j) := by
        have hwj : w + j = (w + (j - 1)) + 1 := by omega
        rw [hwj, pow_succ]; ring
      have hrf : (r - (j - 1)).factorial = (r + 1 - j) * (r - j).factorial := by
        have hr1 : r - (j - 1) = (r - j) + 1 := by omega
        have hr2 : r + 1 - j = (r - j) + 1 := by omega
        rw [hr1, hr2, Nat.factorial_succ]
      have huf : N - r - w + (j - 1) = u - 1 + j := by omega
      rw [hpow, hrf, huf]
    have hs_out : ∀ i ∈ K.filter (fun i ↦ x i ∉ R),
        (qVecRaw R w).ofLp ((insert (0 : Fin L) (K.erase i)).image x) = (-1 : ℝ) ^ (w + j) *
            (((u + j) * (r - j).factorial * (u - 1 + j).factorial : ℕ) : ℝ) := by
      intro i hi
      rcases Finset.mem_filter.1 hi with ⟨hiK, hxiR⟩
      have h0er : (0 : Fin L) ∉ K.erase i := fun h0 ↦ h0K (Finset.mem_of_mem_erase h0)
      have hcard : ((insert (0 : Fin L) (K.erase i)).image x).card = w := by
        rw [Finset.card_image_of_injOn fun idx1 _ idx2 _ hab ↦ hx hab,
          Finset.card_insert_of_notMem h0er, Finset.card_erase_of_mem hiK, hcK]; omega
      have hhit : ((insert (0 : Fin L) (K.erase i)).image x ∩ R).card = j := by
        have heq1 : (insert (0 : Fin L) (K.erase i)).image x ∩ R = H.image x := by
          rw [Finset.image_insert]
          ext z; simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_image,
            Finset.mem_erase, H, Finset.mem_filter]
          constructor
          · rintro ⟨(rfl | ⟨idx, ⟨_, hidxK⟩, rfl⟩), hzR⟩
            · exact False.elim (hx0 hzR)
            · exact ⟨idx, ⟨hidxK, hzR⟩, rfl⟩
          · rintro ⟨idx, ⟨hidxK, hidxR⟩, rfl⟩
            exact ⟨Or.inr ⟨idx, ⟨fun hidx_eq ↦ hxiR (hidx_eq ▸ hidxR), hidxK⟩, rfl⟩, hidxR⟩
        rw [heq1, Finset.card_image_of_injOn fun idx1 _ idx2 _ hab ↦ hx hab]
      unfold qVecRaw; simp only [hcard, ↓reduceIte, hhit, hR]
      have huf : (N - r - w + j).factorial = (u + j) * (u - 1 + j).factorial := by
        have hu2 : N - r - w + j = (u - 1 + j) + 1 := by omega
        rw [hu2]; exact Nat.factorial_succ (u - 1 + j)
      rw [huf]; push_cast; ring
    have hK_val : (qVecRaw R w).ofLp (K.image x) = (-1 : ℝ) ^ (w + j) *
          (((u + j) * (r - j).factorial * (u - 1 + j).factorial : ℕ) : ℝ) := by
      unfold qVecRaw; simp only [himgK_card, ↓reduceIte, himgK_hit, hR]
      have huf : (N - r - w + j).factorial = (u + j) * (u - 1 + j).factorial := by
        have hu2 : N - r - w + j = (u - 1 + j) + 1 := by omega
        rw [hu2]; exact Nat.factorial_succ (u - 1 + j)
      rw [huf]; push_cast; ring
    have h0K_val : (qVecRaw R (w + 1)).ofLp ((insert (0 : Fin L) K).image x) =
        - (-1 : ℝ) ^ (w + j) *
          (((r - j).factorial * (u - 1 + j).factorial : ℕ) : ℝ) := by
      unfold qVecRaw; simp only [himg0K_card, ↓reduceIte, himg0K_hit, hR]
      have hpow : (-1 : ℝ) ^ (w + 1 + j) = - (-1 : ℝ) ^ (w + j) := by
        have hwj : w + 1 + j = (w + j) + 1 := by omega
        rw [hwj, pow_succ]; ring
      have huf : N - r - (w + 1) + j = u - 1 + j := by omega
      rw [hpow, huf]
    have hj_def : (K.filter (fun i ↦ x i ∈ R)).card = j := rfl
    rw [Finset.sum_congr rfl hs_in, Finset.sum_congr rfl hs_out, Finset.sum_const,
      Finset.sum_const, hj_def, hcH_not, nsmul_eq_mul, nsmul_eq_mul, hK_val, h0K_val]
    push_cast
    rw [Nat.cast_sub (by omega : j ≤ r + 1), Nat.cast_sub (by omega : j ≤ w),
      Nat.cast_sub (by omega : 2 * w ≤ N), Nat.cast_sub (by omega : w ≤ N),
      Nat.cast_sub (by omega : w ≤ N - r), Nat.cast_sub (by omega : r ≤ N)]
    push_cast; ring
  · simp [hx]
theorem rawLiftB_qVecRaw_of_mem {L N r w : ℕ} [NeZero L]
    (hw1 : 1 ≤ w) (hwL : w + 1 ≤ L) (hwr : w + 1 ≤ r) (hrN : r + L ≤ N)
    {R : Finset (Fin N)} (hR : R.card = r) {x : Fin L → Fin N} (hx0 : x 0 ∈ R) :
    (rawLiftB (L := L) w (qVecRaw R w)).ofLp x =
      (((r - w) * (N - w + 1) : ℕ) : ℝ) *
        (rawLiftA (L := L) (w + 1) (qVecRaw R (w + 1))).ofLp x := by
  unfold rawLiftB rawLiftA rawLiftT; simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  by_cases hx : Function.Injective x
  · simp only [hx, ↓reduceIte, Nat.add_sub_cancel]
    have hcard_er : ((tailSlots L).card - (w - 1)) = L - w := by rw [card_tailSlots]; omega
    have hw_succ : w - 1 + 1 = w := by omega
    have her := sum_powersetCard_erase (tailSlots L) (w - 1)
      (fun K' ↦ (qVecRaw R w).ofLp ((insert (0 : Fin L) K').image x))
    rw [hcard_er, hw_succ] at her
    rw [her, Finset.mul_sum, ← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun K hK ↦ ?_
    rcases Finset.mem_powersetCard.1 hK with ⟨hKsub, hcK⟩
    have h0K : (0 : Fin L) ∉ K := fun h0 ↦ (Finset.mem_erase.1 (hKsub h0)).1 rfl
    set H := K.filter (fun i ↦ x i ∈ R)
    set j := H.card; have hjw : j ≤ w := hcK ▸ Finset.card_le_card (Finset.filter_subset _ K)
    have hcH_not : (K.filter (fun i ↦ x i ∉ R)).card = w - j := by
      have h1 := Finset.sum_filter_add_sum_filter_not K (fun i ↦ x i ∈ R) (fun _ ↦ (1 : ℕ))
      simp only [Finset.sum_const, smul_eq_mul, mul_one, hcK] at h1
      have hj_def : (K.filter (fun i ↦ x i ∈ R)).card = j := rfl
      rw [hj_def] at h1; omega
    have himgK_card : (K.image x).card = w :=
      (Finset.card_image_of_injOn fun idx1 _ idx2 _ hab ↦ hx hab).trans hcK
    have himgK_hit : (K.image x ∩ R).card = j := by
      have heq : K.image x ∩ R = H.image x := by
        ext z; simp only [Finset.mem_inter, Finset.mem_image, H, Finset.mem_filter]
        constructor
        · rintro ⟨⟨idx, hidx, rfl⟩, hzR⟩; exact ⟨idx, ⟨hidx, hzR⟩, rfl⟩
        · rintro ⟨idx, ⟨hidx, hidxR⟩, rfl⟩; exact ⟨⟨idx, hidx, rfl⟩, hidxR⟩
      rw [heq, Finset.card_image_of_injOn fun idx1 _ idx2 _ hab ↦ hx hab]
    have himg0K_card : ((insert (0 : Fin L) K).image x).card = w + 1 := by
      rw [Finset.card_image_of_injOn fun idx1 _ idx2 _ hab ↦ hx hab,
        Finset.card_insert_of_notMem h0K, hcK]
    have hx0_not_imgK : x 0 ∉ K.image x := by
      intro hmem
      rcases Finset.mem_image.1 hmem with ⟨idx, hidx, hidx0⟩
      exact h0K ((hx hidx0) ▸ hidx)
    have himg0K_hit : ((insert (0 : Fin L) K).image x ∩ R).card = j + 1 := by
      have heq : (insert (0 : Fin L) K).image x ∩ R = insert (x 0) (K.image x ∩ R) := by
        rw [Finset.image_insert]
        ext z; simp only [Finset.mem_inter, Finset.mem_insert]
        have : z = x 0 → z ∈ R := fun h ↦ h ▸ hx0
        tauto
      rw [heq, Finset.card_insert_of_notMem
        (fun h ↦ hx0_not_imgK (Finset.mem_of_mem_inter_left h)), himgK_hit]
    rw [← Finset.sum_filter_add_sum_filter_not K (fun i ↦ x i ∈ R)]
    set u := N - r - w
    have hs_in : ∀ i ∈ K.filter (fun i ↦ x i ∈ R),
        (qVecRaw R w).ofLp ((insert (0 : Fin L) (K.erase i)).image x) = (-1 : ℝ) ^ (w + j) *
            (((r - j) * (r - 1 - j).factorial * (u + j).factorial : ℕ) : ℝ) := by
      intro i hi
      rcases Finset.mem_filter.1 hi with ⟨hiK, _⟩
      have h0er : (0 : Fin L) ∉ K.erase i := fun h0 ↦ h0K (Finset.mem_of_mem_erase h0)
      have hcard : ((insert (0 : Fin L) (K.erase i)).image x).card = w := by
        rw [Finset.card_image_of_injOn fun idx1 _ idx2 _ hab ↦ hx hab,
          Finset.card_insert_of_notMem h0er, Finset.card_erase_of_mem hiK, hcK]; omega
      have hhit : ((insert (0 : Fin L) (K.erase i)).image x ∩ R).card = j := by
        have heq1 : (insert (0 : Fin L) (K.erase i)).image x ∩ R =
            insert (x 0) ((H.erase i).image x) := by
          rw [Finset.image_insert]
          ext z; simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_image,
            Finset.mem_erase, H, Finset.mem_filter]
          constructor
          · rintro ⟨(rfl | ⟨idx, ⟨hidx_ne, hidxK⟩, rfl⟩), hzR⟩
            · exact Or.inl rfl
            · exact Or.inr ⟨idx, ⟨hidx_ne, hidxK, hzR⟩, rfl⟩
          · rintro (rfl | ⟨idx, ⟨hidx_ne, hidxK, hidxR⟩, rfl⟩)
            · exact ⟨Or.inl rfl, hx0⟩
            · exact ⟨Or.inr ⟨idx, ⟨hidx_ne, hidxK⟩, rfl⟩, hidxR⟩
        have hx0_not : x 0 ∉ (H.erase i).image x := by
          intro hmem
          rcases Finset.mem_image.1 hmem with ⟨idx, hidx, hidx0⟩
          exact h0K ((hx hidx0) ▸ (Finset.mem_filter.1 (Finset.mem_of_mem_erase hidx)).1)
        rw [heq1, Finset.card_insert_of_notMem hx0_not,
          Finset.card_image_of_injOn fun idx1 _ idx2 _ hab ↦ hx hab,
          Finset.card_erase_of_mem hi]
        have hj1 : 1 ≤ j := Finset.card_pos.2 ⟨i, hi⟩; exact Nat.sub_add_cancel hj1
      unfold qVecRaw; simp only [hcard, ↓reduceIte, hhit, hR]
      have hrf : (r - j).factorial = (r - j) * (r - 1 - j).factorial := by
        have hr1 : r - j = (r - 1 - j) + 1 := by omega
        conv_lhs => rw [hr1, Nat.factorial_succ]
        rw [← hr1]
      rw [hrf]
    have hs_out : ∀ i ∈ K.filter (fun i ↦ x i ∉ R),
        (qVecRaw R w).ofLp ((insert (0 : Fin L) (K.erase i)).image x) = - (-1 : ℝ) ^ (w + j) *
            (((u + j + 1) * (r - 1 - j).factorial * (u + j).factorial : ℕ) : ℝ) := by
      intro i hi
      rcases Finset.mem_filter.1 hi with ⟨hiK, hxiR⟩
      have h0er : (0 : Fin L) ∉ K.erase i := fun h0 ↦ h0K (Finset.mem_of_mem_erase h0)
      have hcard : ((insert (0 : Fin L) (K.erase i)).image x).card = w := by
        rw [Finset.card_image_of_injOn fun idx1 _ idx2 _ hab ↦ hx hab,
          Finset.card_insert_of_notMem h0er, Finset.card_erase_of_mem hiK, hcK]; omega
      have hhit : ((insert (0 : Fin L) (K.erase i)).image x ∩ R).card = j + 1 := by
        have heq1 : (insert (0 : Fin L) (K.erase i)).image x ∩ R =
            insert (x 0) (H.image x) := by
          rw [Finset.image_insert]
          ext z; simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_image,
            Finset.mem_erase, H, Finset.mem_filter]
          constructor
          · rintro ⟨(rfl | ⟨idx, ⟨_, hidxK⟩, rfl⟩), hzR⟩
            · exact Or.inl rfl
            · exact Or.inr ⟨idx, ⟨hidxK, hzR⟩, rfl⟩
          · rintro (rfl | ⟨idx, ⟨hidxK, hidxR⟩, rfl⟩)
            · exact ⟨Or.inl rfl, hx0⟩
            · exact ⟨Or.inr ⟨idx, ⟨fun hidx_eq ↦ hxiR (hidx_eq ▸ hidxR), hidxK⟩, rfl⟩, hidxR⟩
        have hx0_not : x 0 ∉ H.image x := by
          intro hmem
          rcases Finset.mem_image.1 hmem with ⟨idx, hidx, hidx0⟩
          exact h0K ((hx hidx0) ▸ (Finset.mem_filter.1 hidx).1)
        rw [heq1, Finset.card_insert_of_notMem hx0_not,
          Finset.card_image_of_injOn fun idx1 _ idx2 _ hab ↦ hx hab]
      unfold qVecRaw; simp only [hcard, ↓reduceIte, hhit, hR]
      have hpow : (-1 : ℝ) ^ (w + (j + 1)) = - (-1 : ℝ) ^ (w + j) := by
        have hwj : w + (j + 1) = (w + j) + 1 := by omega
        rw [hwj, pow_succ]; ring
      have hrf : r - (j + 1) = r - 1 - j := by omega
      have huf : (N - r - w + (j + 1)).factorial = (u + j + 1) * (u + j).factorial := by
        have hu1 : N - r - w + (j + 1) = (u + j) + 1 := by omega
        rw [hu1, Nat.factorial_succ]
      rw [hpow, hrf, huf]; push_cast; ring
    have hK_val : (qVecRaw R w).ofLp (K.image x) = (-1 : ℝ) ^ (w + j) *
          (((r - j) * (r - 1 - j).factorial * (u + j).factorial : ℕ) : ℝ) := by
      unfold qVecRaw; simp only [himgK_card, ↓reduceIte, himgK_hit, hR]
      have hrf : (r - j).factorial = (r - j) * (r - 1 - j).factorial := by
        have hr1 : r - j = (r - 1 - j) + 1 := by omega
        conv_lhs => rw [hr1, Nat.factorial_succ]
        rw [← hr1]
      rw [hrf]
    have h0K_val : (qVecRaw R (w + 1)).ofLp ((insert (0 : Fin L) K).image x) = (-1 : ℝ) ^ (w + j) *
          (((r - 1 - j).factorial * (u + j).factorial : ℕ) : ℝ) := by
      unfold qVecRaw; simp only [himg0K_card, ↓reduceIte, himg0K_hit, hR]
      have hpow : (-1 : ℝ) ^ (w + 1 + (j + 1)) = (-1 : ℝ) ^ (w + j) := by
        have hwj : w + 1 + (j + 1) = (w + j) + 2 := by omega
        rw [hwj, pow_add]; norm_num
      have hrf : r - (j + 1) = r - 1 - j := by omega
      have huf : N - r - (w + 1) + (j + 1) = u + j := by omega
      rw [hpow, hrf, huf]
    have hj_def : (K.filter (fun i ↦ x i ∈ R)).card = j := rfl
    rw [Finset.sum_congr rfl hs_in, Finset.sum_congr rfl hs_out, Finset.sum_const,
      Finset.sum_const, hj_def, hcH_not, nsmul_eq_mul, nsmul_eq_mul, hK_val, h0K_val]
    push_cast
    rw [Nat.cast_sub (by omega : j ≤ r), Nat.cast_sub (by omega : j ≤ w),
      Nat.cast_sub (by omega : 2 * w ≤ N), Nat.cast_sub (by omega : w ≤ r),
      Nat.cast_sub (by omega : w ≤ N), Nat.cast_sub (by omega : w ≤ N - r),
      Nat.cast_sub (by omega : r ≤ N)]
    push_cast; ring
  · simp [hx]
/-- Normalization constant for `rawLiftB w`. -/
noncomputable def cBBNat (L N w : ℕ) : ℕ :=
  (L - 1).factorial * (N - 2 * w + 1) * (N - w + 1) * (N - L - w + 1) *
    (N - 2 * w).choose (L - 1 - w)
theorem cAANat_pos {L N w : ℕ} (hw1 : 1 ≤ w) (hwL : w ≤ L) (hN : 2 * L ≤ N) :
    0 < swLCaaNat L N w := by
  unfold swLCaaNat
  exact Nat.mul_pos (Nat.mul_pos (Nat.factorial_pos _) (by omega)) (Nat.choose_pos (by omega))
theorem cBBNat_pos {L N w : ℕ} (hwL : w + 1 ≤ L) (hN : 2 * L ≤ N) :
    0 < cBBNat L N w := by
  unfold cBBNat
  exact Nat.mul_pos
    (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (Nat.factorial_pos _) (by omega)) (by omega)) (by omega))
    (Nat.choose_pos (by omega))
theorem sub_mul_choose_eq (n k : ℕ) (h1 : 1 ≤ n) (hk : k ≤ n - 1) :
    (n - k) * n.choose k = n * (n - 1).choose k := by
  have hnk : k ≤ n := by omega
  have h1f := Nat.choose_mul_factorial_mul_factorial hnk
  have h2f := Nat.choose_mul_factorial_mul_factorial hk
  have hn_succ : n = (n - 1) + 1 := by omega
  have hsub_succ : n - k = (n - 1 - k) + 1 := by omega
  have hf1 : n.factorial = n * (n - 1).factorial := by
    conv_lhs => rw [hn_succ, Nat.factorial_succ]
    rw [← hn_succ]
  have hf2 : (n - k).factorial = (n - k) * (n - 1 - k).factorial := by
    conv_lhs => rw [hsub_succ, Nat.factorial_succ]
    rw [← hsub_succ]
  have hpos : 0 < k.factorial * (n - 1 - k).factorial :=
    Nat.mul_pos (Nat.factorial_pos _) (Nat.factorial_pos _)
  apply Nat.eq_of_mul_eq_mul_right hpos
  calc (n - k) * n.choose k * (k.factorial * (n - 1 - k).factorial)
      = n.choose k * k.factorial * ((n - k) * (n - 1 - k).factorial) := by ring
    _ = n.factorial := by rw [← hf2, h1f]
    _ = n * ((n - 1).choose k * k.factorial * (n - 1 - k).factorial) := by rw [hf1, ← h2f]
    _ = n * (n - 1).choose k * (k.factorial * (n - 1 - k).factorial) := by ring
theorem cBBNat_mul_qVecNormSqNat {L N r w : ℕ}
    (hw1 : 1 ≤ w) (hwL : w + 1 ≤ L) (hwr : w + 1 ≤ r) (hrN : r + L ≤ N) :
    cBBNat L N w * swLQNormSqNat N r w =
      (r - w) * (N - r - w) * (N - w + 1) ^ 2 *
        (swLCaaNat L N (w + 1) * swLQNormSqNat N r (w + 1)) := by
  unfold cBBNat swLCaaNat swLQNormSqNat
  have hch1 : (N - L - w + 1) * (N - 2 * w).choose (L - 1 - w) =
      (N - 2 * w) * (N - 2 * w - 1).choose (L - 1 - w) := by
    have hsub : (N - 2 * w) - (L - 1 - w) = N - L - w + 1 := by omega
    rw [← hsub]
    exact sub_mul_choose_eq (N - 2 * w) (L - 1 - w) (by omega) (by omega)
  have hch2 : (N - 2 * w + 1) * (N - 2 * w) * (N - w + 1).choose w =
      (N - w + 1) * (w + 1) * (N - w).choose (w + 1) := by
    have hf1 := Nat.choose_mul_factorial_mul_factorial (by omega : w ≤ N - w + 1)
    have hsub1 : N - w + 1 - w = N - 2 * w + 1 := by omega
    rw [hsub1] at hf1
    have hf2 := Nat.choose_mul_factorial_mul_factorial (by omega : w + 1 ≤ N - w)
    have hsub2 : N - w - (w + 1) = N - 2 * w - 1 := by omega
    rw [hsub2] at hf2
    have hfact2w : (N - 2 * w + 1).factorial =
        (N - 2 * w + 1) * (N - 2 * w) * (N - 2 * w - 1).factorial := by
      have ha : N - 2 * w + 1 = (N - 2 * w) + 1 := rfl
      have hb : N - 2 * w = (N - 2 * w - 1) + 1 := by omega
      conv_lhs => rw [ha, Nat.factorial_succ, hb, Nat.factorial_succ]
      rw [← hb]; ring
    have hfactNw : (N - w + 1).factorial = (N - w + 1) * (N - w).factorial := by
      have ha : N - w + 1 = (N - w) + 1 := by omega
      conv_lhs => rw [ha, Nat.factorial_succ]
    have hpos : 0 < w.factorial * (N - 2 * w - 1).factorial :=
      Nat.mul_pos (Nat.factorial_pos _) (Nat.factorial_pos _)
    apply Nat.eq_of_mul_eq_mul_right hpos
    calc (N - 2 * w + 1) * (N - 2 * w) * (N - w + 1).choose w *
          (w.factorial * (N - 2 * w - 1).factorial)
        = (N - w + 1).choose w * w.factorial *
          ((N - 2 * w + 1) * (N - 2 * w) * (N - 2 * w - 1).factorial) := by ring
      _ = (N - w + 1).factorial := by rw [← hfact2w, hf1]
      _ = (N - w + 1) * ((N - w).choose (w + 1) * (w + 1).factorial *
          (N - 2 * w - 1).factorial) := by rw [hfactNw, ← hf2]
      _ = (N - w + 1) * (w + 1) * (N - w).choose (w + 1) *
          (w.factorial * (N - 2 * w - 1).factorial) := by rw [Nat.factorial_succ w]; ring
  have hrf : (r - w).factorial = (r - w) * (r - (w + 1)).factorial := by
    have ha : r - w = (r - (w + 1)) + 1 := by omega
    conv_lhs => rw [ha, Nat.factorial_succ]
    rw [← ha]
  have huf : (N - r - w).factorial = (N - r - w) * (N - r - (w + 1)).factorial := by
    have ha : N - r - w = (N - r - (w + 1)) + 1 := by omega
    conv_lhs => rw [ha, Nat.factorial_succ]
    rw [← ha]
  have hsub_2w : N - 2 * (w + 1) + 1 = N - 2 * w - 1 := by omega
  have hsub_Lw : L - (w + 1) = L - 1 - w := by omega
  have hsub_Nw : N - (w + 1) + 1 = N - w := by omega
  rw [hsub_2w, hsub_Lw, hsub_Nw, hrf, huf]
  calc _ = (L - 1).factorial * (N - 2 * w + 1) * (N - w + 1) *
        ((N - L - w + 1) * (N - 2 * w).choose (L - 1 - w)) *
        (r.factorial * (N - r).factorial * ((r - w) * (r - (w + 1)).factorial) *
          ((N - r - w) * (N - r - (w + 1)).factorial) * (N - w + 1).choose w) := by ring
    _ = (L - 1).factorial * (N - w + 1) * (N - 2 * w - 1).choose (L - 1 - w) *
        ((N - 2 * w + 1) * (N - 2 * w) * (N - w + 1).choose w) *
        ((r - w) * (N - r - w) * r.factorial * (N - r).factorial *
          (r - (w + 1)).factorial * (N - r - (w + 1)).factorial) := by
          rw [hch1]; ring
    _ = (r - w) * (N - r - w) * (N - w + 1) ^ 2 *
        ((L - 1).factorial * (w + 1) * (N - 2 * w - 1).choose (L - 1 - w) *
          (r.factorial * (N - r).factorial * (r - (w + 1)).factorial *
            (N - r - (w + 1)).factorial * (N - w).choose (w + 1))) := by
          rw [hch2]; ring
theorem cAANat_one_mul_qVecNormSqNat {L N r : ℕ}
    (hL : 2 ≤ L) (hr1 : 1 ≤ r) (hrN : r + L ≤ N) :
    swLCaaNat L N 1 * swLQNormSqNat N r 1 =
      r * (N - r) * ((r - 1).factorial * (N - r - 1).factorial) ^ 2 *
        (L.factorial * N.choose L) := by
  unfold swLCaaNat swLQNormSqNat
  have hsub1 : N - 2 * 1 + 1 = N - 1 := by omega
  have hsub2 : N - 1 + 1 = N := by omega
  rw [hsub1, hsub2, Nat.choose_one_right]
  have hch : N * (L - 1).factorial * (N - 1).choose (L - 1) = L.factorial * N.choose L := by
    have h1 := sub_mul_choose_eq N L (by omega) (by omega)
    have h2 := Nat.choose_mul_factorial_mul_factorial (by omega : L ≤ N)
    have h3 := Nat.choose_mul_factorial_mul_factorial (by omega : L - 1 ≤ N - 1)
    have hsub3 : N - 1 - (L - 1) = N - L := by omega
    rw [hsub3] at h3
    have hN_fact : N.factorial = N * (N - 1).factorial := by
      have ha : N = (N - 1) + 1 := by omega
      conv_lhs => rw [ha, Nat.factorial_succ]
      rw [← ha]
    have hpos : 0 < (N - L).factorial := Nat.factorial_pos _; apply Nat.eq_of_mul_eq_mul_right hpos
    calc N * (L - 1).factorial * (N - 1).choose (L - 1) * (N - L).factorial
        = N * ((N - 1).choose (L - 1) * (L - 1).factorial * (N - L).factorial) := by ring
      _ = N.factorial := by rw [h3, ← hN_fact]
      _ = L.factorial * N.choose L * (N - L).factorial := by rw [← h2]; ring
  have hrf : r.factorial = r * (r - 1).factorial := by
    have ha : r = (r - 1) + 1 := by omega
    conv_lhs => rw [ha, Nat.factorial_succ]
    rw [← ha]
  have huf : (N - r).factorial = (N - r) * (N - r - 1).factorial := by
    have ha : N - r = (N - r - 1) + 1 := by omega
    conv_lhs => rw [ha, Nat.factorial_succ]
    rw [← ha]
  calc (L - 1).factorial * 1 * (N - 1).choose (L - 1) *
        (r.factorial * (N - r).factorial * (r - 1).factorial * (N - r - 1).factorial * N)
      = (N * (L - 1).factorial * (N - 1).choose (L - 1)) *
        ((r * (r - 1).factorial) * ((N - r) * (N - r - 1).factorial) *
          (r - 1).factorial * (N - r - 1).factorial) := by
          rw [hrf, huf]; ring
    _ = r * (N - r) * ((r - 1).factorial * (N - r - 1).factorial) ^ 2 *
        (L.factorial * N.choose L) := by rw [hch]; ring
/-- Linear map wrapper around `rawLiftA`. -/
noncomputable def rawLiftALin (L N w : ℕ) [NeZero L] :
    EuclideanSpace ℝ (Finset (Fin N)) →ₗ[ℝ] EuclideanSpace ℝ (Fin L → Fin N) where
  toFun := rawLiftA (L := L) w
  map_add' f g := by
    ext x
    unfold rawLiftA
    simp only [PiLp.add_apply]
    change (if Function.Injective x then _ else 0) =
      (if Function.Injective x then _ else 0) + (if Function.Injective x then _ else 0)
    by_cases hx : Function.Injective x
    · simp [hx, Finset.sum_add_distrib]
    · simp [hx]
  map_smul' c f := by
    ext x
    unfold rawLiftA
    simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply]
    change (if Function.Injective x then _ else 0) = c * (if Function.Injective x then _ else 0)
    by_cases hx : Function.Injective x
    · simp [hx, Finset.mul_sum]
    · simp [hx]
/-- Linear map wrapper around `rawLiftT`. -/
noncomputable def rawLiftTLin (L N w : ℕ) [NeZero L] :
    EuclideanSpace ℝ (Finset (Fin N)) →ₗ[ℝ] EuclideanSpace ℝ (Fin L → Fin N) where
  toFun := rawLiftT (L := L) w
  map_add' f g := by
    ext x
    unfold rawLiftT
    simp only [PiLp.add_apply]
    change (if Function.Injective x then _ else 0) =
      (if Function.Injective x then _ else 0) + (if Function.Injective x then _ else 0)
    by_cases hx : Function.Injective x
    · simp [hx, Finset.sum_add_distrib]
    · simp [hx]
  map_smul' c f := by
    ext x
    unfold rawLiftT
    simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply]
    change (if Function.Injective x then _ else 0) = c * (if Function.Injective x then _ else 0)
    by_cases hx : Function.Injective x
    · simp [hx, Finset.mul_sum]
    · simp [hx]
/-- Linear map wrapper around `rawLiftB`. -/
noncomputable def rawLiftBLin (L N w : ℕ) [NeZero L] :
    EuclideanSpace ℝ (Finset (Fin N)) →ₗ[ℝ] EuclideanSpace ℝ (Fin L → Fin N) :=
  ((L - w : ℕ) : ℝ) • rawLiftALin L N w + ((N - 2 * w + 1 : ℕ) : ℝ) • rawLiftTLin L N w
theorem rawLiftALin_apply {L N w : ℕ} [NeZero L] (f : EuclideanSpace ℝ (Finset (Fin N))) :
    rawLiftALin L N w f = rawLiftA (L := L) w f := rfl
theorem rawLiftBLin_apply {L N w : ℕ} [NeZero L] (f : EuclideanSpace ℝ (Finset (Fin N))) :
    rawLiftBLin L N w f = rawLiftB (L := L) w f := rfl
/-- Linear isometry `ι_{-, w}: harmonicSubspace N w →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin L → Fin
  N)`. -/
noncomputable def liftMinusTupleLI (L N w : ℕ) [NeZero L] [NeZero N]
    (hw1 : 1 ≤ w) (hwL : w ≤ L) (hN : 2 * L ≤ N) :
    harmonicSubspace N w →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin L → Fin N) where
  toLinearMap :=
    ((1 / √(swLCaaNat L N w : ℝ)) • rawLiftALin L N w).comp (harmonicSubspace N w).subtype
  norm_map' f := by
    rw [norm_eq_sqrt_real_inner, norm_eq_sqrt_real_inner]
    congr 1
    change ⟪(1 / √(swLCaaNat L N w : ℝ)) • rawLiftA (L := L) w f.1,
      (1 / √(swLCaaNat L N w : ℝ)) • rawLiftA (L := L) w f.1⟫ = ⟪f.1, f.1⟫
    rw [inner_smul_left, inner_smul_right, inner_rawLiftA_self hw1 hwL hN f.2 f.2]
    simp only [RCLike.conj_to_real]
    have hpos : (0 : ℝ) < (swLCaaNat L N w : ℝ) := by exact_mod_cast cAANat_pos hw1 hwL hN
    change (1 / √(swLCaaNat L N w : ℝ)) * ((1 / √(swLCaaNat L N w : ℝ)) *
      ((swLCaaNat L N w : ℝ) * ⟪f.1, f.1⟫)) = ⟪f.1, f.1⟫
    field_simp
    rw [Real.sq_sqrt hpos.le]
/-- Linear isometry `ι_{+, w}: harmonicSubspace N w →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin L → Fin
  N)`. -/
noncomputable def liftPlusTupleLI (L N w : ℕ) [NeZero L] [NeZero N]
    (hw1 : 1 ≤ w) (hwL : w + 1 ≤ L) (hN : 2 * L ≤ N) :
    harmonicSubspace N w →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin L → Fin N) where
  toLinearMap := ((1 / √(cBBNat L N w : ℝ)) • rawLiftBLin L N w).comp (harmonicSubspace N w).subtype
  norm_map' f := by
    rw [norm_eq_sqrt_real_inner, norm_eq_sqrt_real_inner]
    congr 1
    change ⟪(1 / √(cBBNat L N w : ℝ)) • rawLiftB (L := L) w f.1,
      (1 / √(cBBNat L N w : ℝ)) • rawLiftB (L := L) w f.1⟫ = ⟪f.1, f.1⟫
    rw [inner_smul_left, inner_smul_right, inner_rawLiftB_self hw1 hwL hN f.2 f.2]
    simp only [RCLike.conj_to_real]
    have hpos : (0 : ℝ) < (cBBNat L N w : ℝ) := by exact_mod_cast cBBNat_pos hwL hN
    change (1 / √(cBBNat L N w : ℝ)) * ((1 / √(cBBNat L N w : ℝ)) *
      ((cBBNat L N w : ℝ) * ⟪f.1, f.1⟫)) = ⟪f.1, f.1⟫
    field_simp
    rw [Real.sq_sqrt hpos.le]
/-- Subspace `V_{-, w}` (`1 ≤ w ≤ L`) on `EuclideanSpace ℝ (Fin L → Fin N)`. -/
noncomputable def vMinusSubspace (L N w : ℕ) [NeZero L] [NeZero N]
    (hw1 : 1 ≤ w) (hwL : w ≤ L) (hN : 2 * L ≤ N) :
    Submodule ℝ (EuclideanSpace ℝ (Fin L → Fin N)) :=
  LinearMap.range (liftMinusTupleLI L N w hw1 hwL hN).toLinearMap
/-- Subspace `V_{+, w}` (`1 ≤ w ≤ L - 1`) on `EuclideanSpace ℝ (Fin L → Fin N)`. -/
noncomputable def vPlusSubspace (L N w : ℕ) [NeZero L] [NeZero N]
    (hw1 : 1 ≤ w) (hwL : w + 1 ≤ L) (hN : 2 * L ≤ N) :
    Submodule ℝ (EuclideanSpace ℝ (Fin L → Fin N)) :=
  LinearMap.range (liftPlusTupleLI L N w hw1 hwL hN).toLinearMap
/-- Orthogonal projector endomorphism onto `K: Submodule ℝ E`. -/
noncomputable def orthProjEnd {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (K : Submodule ℝ E) : E →ₗ[ℝ] E :=
  K.subtypeL.toLinearMap.comp K.orthogonalProjectionOnto.toLinearMap
theorem orthProjEnd_self_adjoint {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (K : Submodule ℝ E) :
    LinearMap.adjoint (orthProjEnd K) = orthProjEnd K := by
  apply LinearMap.ext; intro x; apply ext_inner_left ℝ; intro y
  rw [LinearMap.adjoint_inner_right]; unfold orthProjEnd
  simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe, Submodule.coe_subtypeL,
    Submodule.coe_subtype]
  exact Submodule.inner_starProjection_left_eq_right K y x
theorem orthProjEnd_eq_self {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {K : Submodule ℝ E} {x : E} (hx : x ∈ K) :
    orthProjEnd K x = x := by
  change (K.orthogonalProjectionOnto x : E) = x
  rw [Submodule.orthogonalProjectionOnto_mem_subspace_eq_self ⟨x, hx⟩]
theorem orthProjEnd_idem {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (K : Submodule ℝ E) :
    (orthProjEnd K).comp (orthProjEnd K) = orthProjEnd K := by
  ext x
  exact orthProjEnd_eq_self (K.orthogonalProjectionOnto x).2
theorem orthProjEnd_eq_zero {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {K : Submodule ℝ E} {x : E} (hx : ∀ y ∈ K, ⟪y, x⟫ = 0) :
    orthProjEnd K x = 0 := by
  have hmem : x ∈ Kᗮ := (Submodule.mem_orthogonal K x).2 hx
  change (K.orthogonalProjectionOnto x : E) = 0
  rw [(Submodule.orthogonalProjectionOnto_eq_zero_iff).2 hmem]; rfl
/-- Partial isometry endomorphism `K_w = ι_{+, w} ∘ ι_{-, w}^{-1} ∘ P_{V_{-, w}}`. -/
noncomputable def pieriIsomEnd {E H : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H] (ι₁ ι₂ : H →ₗᵢ[ℝ] E) : E →ₗ[ℝ] E :=
  let K₁ := LinearMap.range ι₁.toLinearMap
  ι₂.toLinearMap.comp (ι₁.equivRange.symm.toLinearMap.comp K₁.orthogonalProjectionOnto.toLinearMap)
theorem pieriIsomEnd_apply_ι₁ {E H : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H] (ι₁ ι₂ : H →ₗᵢ[ℝ] E) (q : H) :
    pieriIsomEnd ι₁ ι₂ (ι₁ q) = ι₂ q := by
  have hmem : ι₁ q ∈ LinearMap.range ι₁.toLinearMap := ⟨q, rfl⟩
  have hproj : (LinearMap.range ι₁.toLinearMap).orthogonalProjectionOnto (ι₁ q) = ⟨ι₁ q, hmem⟩ :=
    Submodule.orthogonalProjectionOnto_mem_subspace_eq_self ⟨ι₁ q, hmem⟩
  have heq : ⟨ι₁ q, hmem⟩ = ι₁.equivRange q := rfl
  change ι₂ (ι₁.equivRange.symm ((LinearMap.range ι₁.toLinearMap).orthogonalProjectionOnto (ι₁ q)))
    = ι₂ q
  rw [hproj, heq, LinearIsometryEquiv.symm_apply_apply]
theorem pieriIsomEnd_apply_orth {E H : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H] (ι₁ ι₂ : H →ₗᵢ[ℝ] E) {x : E}
    (hx : ∀ q : H, ⟪ι₁ q, x⟫ = 0) :
    pieriIsomEnd ι₁ ι₂ x = 0 := by
  have hmem : x ∈ (LinearMap.range ι₁.toLinearMap)ᗮ := by
    rw [Submodule.mem_orthogonal]
    rintro y ⟨q, rfl⟩
    exact hx q
  have hzero : (LinearMap.range ι₁.toLinearMap).orthogonalProjectionOnto x = 0 :=
    (Submodule.orthogonalProjectionOnto_eq_zero_iff).2 hmem
  change ι₂ (ι₁.equivRange.symm ((LinearMap.range ι₁.toLinearMap).orthogonalProjectionOnto x)) = 0
  rw [hzero, map_zero, map_zero]
theorem pieriIsomEnd_adjoint {E H : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H] (ι₁ ι₂ : H →ₗᵢ[ℝ] E) :
    LinearMap.adjoint (pieriIsomEnd ι₁ ι₂) = pieriIsomEnd ι₂ ι₁ := by
  apply LinearMap.ext; intro y; apply ext_inner_left ℝ; intro x
  rw [LinearMap.adjoint_inner_right]; set K₁ := LinearMap.range ι₁.toLinearMap
  set K₂ := LinearMap.range ι₂.toLinearMap; set p₁ := K₁.orthogonalProjectionOnto x
  set p₂ := K₂.orthogonalProjectionOnto y; set q₁ := ι₁.equivRange.symm p₁
  set q₂ := ι₂.equivRange.symm p₂
  have hp₁ : (p₁ : E) = ι₁ q₁ := congrArg Subtype.val (ι₁.equivRange.apply_symm_apply p₁).symm
  have hp₂ : (p₂ : E) = ι₂ q₂ := congrArg Subtype.val (ι₂.equivRange.apply_symm_apply p₂).symm
  have hlhs : pieriIsomEnd ι₁ ι₂ x = ι₂ q₁ := rfl; have hrhs : pieriIsomEnd ι₂ ι₁ y = ι₁ q₂ := rfl
  rw [hlhs, hrhs]
  have h1 : ⟪ι₂ q₁, y⟫ = ⟪ι₂ q₁, (p₂ : E)⟫ := by
    have hm : ι₂ q₁ ∈ K₂ := ⟨q₁, rfl⟩
    have hst := Submodule.inner_starProjection_left_eq_right K₂ (ι₂ q₁) y
    have hproj : K₂.starProjection (ι₂ q₁) = ι₂ q₁ := orthProjEnd_eq_self hm
    have hp2_st : K₂.starProjection y = (p₂ : E) := rfl; rw [hproj, hp2_st] at hst; exact hst
  have h2 : ⟪x, ι₁ q₂⟫ = ⟪(p₁ : E), ι₁ q₂⟫ := by
    have hm : ι₁ q₂ ∈ K₁ := ⟨q₂, rfl⟩
    have hst := Submodule.inner_starProjection_left_eq_right K₁ x (ι₁ q₂)
    have hproj : K₁.starProjection (ι₁ q₂) = ι₁ q₂ := orthProjEnd_eq_self hm
    have hp1_st : K₁.starProjection x = (p₁ : E) := rfl; rw [hproj, hp1_st] at hst; exact hst.symm
  rw [h1, hp₂, ι₂.inner_map_map, h2, hp₁, ι₁.inner_map_map]
theorem pieriIsomEnd_props {E H : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H] (ι₁ ι₂ : H →ₗᵢ[ℝ] E)
    (horth : ∀ q₁ q₂ : H, ⟪ι₁ q₁, ι₂ q₂⟫ = 0) :
    let P₁ := orthProjEnd (LinearMap.range ι₁.toLinearMap)
    let P₂ := orthProjEnd (LinearMap.range ι₂.toLinearMap)
    let K := pieriIsomEnd ι₁ ι₂
    (LinearMap.adjoint K).comp K = P₁ ∧
    K.comp (LinearMap.adjoint K) = P₂ ∧
    K.comp P₁ = K ∧
    P₂.comp K = K ∧
    P₁.comp P₂ = 0 := by
  intro P₁ P₂ K; have hadj : LinearMap.adjoint K = pieriIsomEnd ι₂ ι₁ := pieriIsomEnd_adjoint ι₁ ι₂
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · ext x
    rw [LinearMap.comp_apply, hadj]
    set p₁ := (LinearMap.range ι₁.toLinearMap).orthogonalProjectionOnto x
    set q₁ := ι₁.equivRange.symm p₁; have hKx : K x = ι₂ q₁ := rfl
    have hp₁ : (p₁ : E) = ι₁ q₁ := congrArg Subtype.val (ι₁.equivRange.apply_symm_apply p₁).symm
    rw [hKx, pieriIsomEnd_apply_ι₁]; exact hp₁.symm
  · ext x
    rw [LinearMap.comp_apply, hadj]
    set p₂ := (LinearMap.range ι₂.toLinearMap).orthogonalProjectionOnto x
    set q₂ := ι₂.equivRange.symm p₂; have hKtx : pieriIsomEnd ι₂ ι₁ x = ι₁ q₂ := rfl
    have hp₂ : (p₂ : E) = ι₂ q₂ := congrArg Subtype.val (ι₂.equivRange.apply_symm_apply p₂).symm
    rw [hKtx, pieriIsomEnd_apply_ι₁]; exact hp₂.symm
  · ext x
    rw [LinearMap.comp_apply]; set p₁ := (LinearMap.range ι₁.toLinearMap).orthogonalProjectionOnto x
    set q₁ := ι₁.equivRange.symm p₁
    have hp₁ : P₁ x = ι₁ q₁ := congrArg Subtype.val (ι₁.equivRange.apply_symm_apply p₁).symm
    rw [hp₁, pieriIsomEnd_apply_ι₁]; rfl
  · ext x
    rw [LinearMap.comp_apply]; set p₁ := (LinearMap.range ι₁.toLinearMap).orthogonalProjectionOnto x
    set q₁ := ι₁.equivRange.symm p₁; have hKx : K x = ι₂ q₁ := rfl
    rw [hKx]; exact orthProjEnd_eq_self (LinearMap.mem_range.2 ⟨q₁, rfl⟩)
  · ext x
    rw [LinearMap.comp_apply, LinearMap.zero_apply]
    set p₂ := (LinearMap.range ι₂.toLinearMap).orthogonalProjectionOnto x
    rcases p₂.2 with ⟨q₂, hq₂⟩
    have hP₂x : P₂ x = ι₂ q₂ := hq₂.symm; rw [hP₂x]
    exact orthProjEnd_eq_zero fun y ⟨q₁, hq₁⟩ ↦ hq₁ ▸ horth q₁ q₂
/-- Target-dependent `2L`-dimensional orthonormal basis `b_0,..., b_{2L-1}` on `Fin L → Fin
  N`. -/
noncomputable def bTuple (L N : ℕ) [NeZero L] (R : Finset (Fin N)) (j : Fin (2 * L)) :
    EuclideanSpace ℝ (Fin L → Fin N) :=
  if j.1 = 0 then
    b0TupleVec L N
  else if j.1 % 2 = 1 then
    let m := (j.1 + 1) / 2
    (1 / √(swLCaaNat L N m : ℝ)) • rawLiftA (L := L) m (qVec R m)
  else
    let w := j.1 / 2
    (1 / √(cBBNat L N w : ℝ)) • rawLiftB (L := L) w (qVec R w)
theorem bTuple_zero (L N : ℕ) [NeZero L] (R : Finset (Fin N)) (hL : 1 ≤ L) :
    bTuple L N R ⟨0, by omega⟩ = b0TupleVec L N := by
  simp [bTuple]
theorem bTuple_odd (L N : ℕ) [NeZero L] (R : Finset (Fin N)) {m : ℕ}
    (hm1 : 1 ≤ m) (hmL : m ≤ L) :
    bTuple L N R ⟨2 * m - 1, by omega⟩ =
      (1 / √(swLCaaNat L N m : ℝ)) • rawLiftA (L := L) m (qVec R m) := by
  unfold bTuple
  have hne0 : 2 * m - 1 ≠ 0 := by omega
  have hmod : (2 * m - 1) % 2 = 1 := by omega
  have hdiv : (2 * m - 1 + 1) / 2 = m := by omega
  simp [hne0, hmod, hdiv]
theorem bTuple_even (L N : ℕ) [NeZero L] (R : Finset (Fin N)) {w : ℕ}
    (hw1 : 1 ≤ w) (hwL : w + 1 ≤ L) :
    bTuple L N R ⟨2 * w, by omega⟩ =
      (1 / √(cBBNat L N w : ℝ)) • rawLiftB (L := L) w (qVec R w) := by
  unfold bTuple
  have hne0 : 2 * w ≠ 0 := by omega
  have hmod : (2 * w) % 2 = 0 := by omega
  have hdiv : (2 * w) / 2 = w := by omega
  simp [hne0, hmod, hdiv]
theorem inner_bTuple {L N r : ℕ} [NeZero L] [NeZero N]
    (hL : 2 ≤ L) (hrL : L ≤ r) (hrN : r + L ≤ N) {R : Finset (Fin N)} (hR : R.card = r)
    (i j : Fin (2 * L)) :
    ⟪bTuple L N R i, bTuple L N R j⟫ = if i = j then 1 else 0 := by
  have hN : 2 * L ≤ N := by omega
  by_cases hij : i = j
  · subst hij
    simp only [↓reduceIte]
    by_cases hi0 : i.1 = 0
    · have hi_eq : i = ⟨0, by omega⟩ := Fin.ext hi0
      rw [hi_eq, bTuple_zero L N R (by omega)]
      exact inner_b0TupleVec_self (by omega)
    · by_cases himod : i.1 % 2 = 1
      · set m := (i.1 + 1) / 2
        have hm1 : 1 ≤ m := by omega
        have hmL : m ≤ L := by omega
        have hi_eq : i = ⟨2 * m - 1, by omega⟩ := Fin.ext (by dsimp [m]; omega)
        rw [hi_eq, bTuple_odd L N R hm1 hmL]
        have hq := qVec_mem_harmonic hm1 (by omega) (by omega) hR
        have hli := (liftMinusTupleLI L N m hm1 hmL hN).inner_map_map ⟨qVec R m, hq⟩ ⟨qVec R m, hq⟩
        exact hli.trans (inner_qVec_self (by omega) (by omega) hR)
      · set w := i.1 / 2
        have hw1 : 1 ≤ w := by omega
        have hwL : w + 1 ≤ L := by omega
        have hi_eq : i = ⟨2 * w, by omega⟩ := Fin.ext (by dsimp [w]; omega)
        rw [hi_eq, bTuple_even L N R hw1 hwL]
        have hq := qVec_mem_harmonic hw1 (by omega) (by omega) hR
        have hli := (liftPlusTupleLI L N w hw1 hwL hN).inner_map_map ⟨qVec R w, hq⟩ ⟨qVec R w, hq⟩
        exact hli.trans (inner_qVec_self (by omega) (by omega) hR)
  · simp only [hij, ↓reduceIte]
    suffices hlt : ∀ a b : Fin (2 * L), a.1 < b.1 → ⟪bTuple L N R a, bTuple L N R b⟫ = 0 by
      rcases Nat.lt_trichotomy i.1 j.1 with h | h | h
      · exact hlt i j h
      · exact False.elim (hij (Fin.ext h))
      · rw [real_inner_comm]; exact hlt j i h
    intro a b hab
    by_cases ha0 : a.1 = 0
    · have ha_bt : bTuple L N R a = b0TupleVec L N := by
        have ha_eq : a = ⟨0, by omega⟩ := Fin.ext ha0
        rw [ha_eq, bTuple_zero L N R (by omega)]
      rw [ha_bt]
      by_cases hbmod : b.1 % 2 = 1
      · set m := (b.1 + 1) / 2
        have hm1 : 1 ≤ m := by omega
        have hmL : m ≤ L := by omega
        have hb_bt : bTuple L N R b =
            (1 / √(swLCaaNat L N m : ℝ)) • rawLiftA (L := L) m (qVec R m) := by
          have hb_eq : b = ⟨2 * m - 1, by omega⟩ := Fin.ext (by dsimp [m]; omega)
          rw [hb_eq, bTuple_odd L N R hm1 hmL]
        rw [hb_bt, inner_smul_right,
          (inner_b0TupleVec_rawLift hm1 (qVec_mem_harmonic hm1 (by omega) (by omega) hR)).1,
          mul_zero]
      · set w := b.1 / 2
        have hw1 : 1 ≤ w := by omega
        have hwL : w + 1 ≤ L := by omega
        have hb_bt : bTuple L N R b =
            (1 / √(cBBNat L N w : ℝ)) • rawLiftB (L := L) w (qVec R w) := by
          have hb_eq : b = ⟨2 * w, by omega⟩ := Fin.ext (by dsimp [w]; omega)
          rw [hb_eq, bTuple_even L N R hw1 hwL]
        rw [hb_bt, inner_smul_right]; unfold rawLiftB
        have h0 := inner_b0TupleVec_rawLift (L := L) hw1
          (qVec_mem_harmonic hw1 (by omega) (by omega) hR)
        rw [inner_add_right, inner_smul_right, inner_smul_right, h0.1, h0.2]; ring
    · set wa := (a.1 + 1) / 2; set wb := (b.1 + 1) / 2
      have hwa1 : 1 ≤ wa := by omega
      have hwb1 : 1 ≤ wb := by omega
      have hwbL : wb ≤ L := by omega
      have hqb := qVec_mem_harmonic hwb1 (by omega) (by omega) hR
      by_cases hw_eq : wa = wb
      · have ha_odd : a.1 = 2 * wa - 1 := by omega
        have hb_even : b.1 = 2 * wa := by omega
        have hwaL : wa + 1 ≤ L := by omega
        have ha_bt : bTuple L N R a =
            (1 / √(swLCaaNat L N wa : ℝ)) • rawLiftA (L := L) wa (qVec R wa) := by
          have ha_eq : a = ⟨2 * wa - 1, by omega⟩ := Fin.ext ha_odd
          rw [ha_eq, bTuple_odd L N R hwa1 (by omega)]
        have hb_bt : bTuple L N R b =
            (1 / √(cBBNat L N wa : ℝ)) • rawLiftB (L := L) wa (qVec R wa) := by
          have hb_eq : b = ⟨2 * wa, by omega⟩ := Fin.ext hb_even
          rw [hb_eq, bTuple_even L N R hwa1 hwaL]
        have hqa := qVec_mem_harmonic hwa1 (by omega) (by omega) hR
        rw [ha_bt, hb_bt,
          inner_smul_left, inner_smul_right, inner_rawLiftA_rawLiftB hwa1 hwaL hN hqa hqa]
        ring
      · have hw_lt : wa < wb := by omega
        rcases inner_rawLiftA_lt (L := L) hwa1 hw_lt (f := qVec R wa) hqb with
          ⟨hcAA, hcTA, hcAT, hcTT⟩
        by_cases hamod : a.1 % 2 = 1 <;> by_cases hbmod : b.1 % 2 = 1
        · have ha_bt : bTuple L N R a =
              (1 / √(swLCaaNat L N wa : ℝ)) • rawLiftA (L := L) wa (qVec R wa) := by
            have ha_eq : a = ⟨2 * wa - 1, by omega⟩ := Fin.ext (by dsimp [wa]; omega)
            rw [ha_eq, bTuple_odd L N R hwa1 (by omega)]
          have hb_bt : bTuple L N R b =
              (1 / √(swLCaaNat L N wb : ℝ)) • rawLiftA (L := L) wb (qVec R wb) := by
            have hb_eq : b = ⟨2 * wb - 1, by omega⟩ := Fin.ext (by dsimp [wb]; omega)
            rw [hb_eq, bTuple_odd L N R hwb1 hwbL]
          rw [ha_bt, hb_bt, inner_smul_left, inner_smul_right, hcAA]; ring
        · have hwbL' : wb + 1 ≤ L := by omega
          have ha_bt : bTuple L N R a =
              (1 / √(swLCaaNat L N wa : ℝ)) • rawLiftA (L := L) wa (qVec R wa) := by
            have ha_eq : a = ⟨2 * wa - 1, by omega⟩ := Fin.ext (by dsimp [wa]; omega)
            rw [ha_eq, bTuple_odd L N R hwa1 (by omega)]
          have hb_bt : bTuple L N R b =
              (1 / √(cBBNat L N wb : ℝ)) • rawLiftB (L := L) wb (qVec R wb) := by
            have hb_eq : b = ⟨2 * wb, by omega⟩ := Fin.ext (by dsimp [wb]; omega)
            rw [hb_eq, bTuple_even L N R hwb1 hwbL']
          rw [ha_bt, hb_bt, inner_smul_left, inner_smul_right]; unfold rawLiftB
          rw [inner_add_right, inner_smul_right, inner_smul_right, hcAA, hcAT]; ring
        · have hwaL' : wa + 1 ≤ L := by omega
          have ha_bt : bTuple L N R a =
              (1 / √(cBBNat L N wa : ℝ)) • rawLiftB (L := L) wa (qVec R wa) := by
            have ha_eq : a = ⟨2 * wa, by omega⟩ := Fin.ext (by dsimp [wa]; omega)
            rw [ha_eq, bTuple_even L N R hwa1 hwaL']
          have hb_bt : bTuple L N R b =
              (1 / √(swLCaaNat L N wb : ℝ)) • rawLiftA (L := L) wb (qVec R wb) := by
            have hb_eq : b = ⟨2 * wb - 1, by omega⟩ := Fin.ext (by dsimp [wb]; omega)
            rw [hb_eq, bTuple_odd L N R hwb1 hwbL]
          rw [ha_bt, hb_bt, inner_smul_left, inner_smul_right]; unfold rawLiftB
          rw [inner_add_left, inner_smul_left, inner_smul_left, hcAA, hcTA]; ring
        · have hwaL' : wa + 1 ≤ L := by omega
          have hwbL' : wb + 1 ≤ L := by omega
          have ha_bt : bTuple L N R a =
              (1 / √(cBBNat L N wa : ℝ)) • rawLiftB (L := L) wa (qVec R wa) := by
            have ha_eq : a = ⟨2 * wa, by omega⟩ := Fin.ext (by dsimp [wa]; omega)
            rw [ha_eq, bTuple_even L N R hwa1 hwaL']
          have hb_bt : bTuple L N R b =
              (1 / √(cBBNat L N wb : ℝ)) • rawLiftB (L := L) wb (qVec R wb) := by
            have hb_eq : b = ⟨2 * wb, by omega⟩ := Fin.ext (by dsimp [wb]; omega)
            rw [hb_eq, bTuple_even L N R hwb1 hwbL']
          rw [ha_bt, hb_bt, inner_smul_left, inner_smul_right]; unfold rawLiftB
          rw [inner_add_left, inner_smul_left, inner_smul_left,
            inner_add_right, inner_smul_right, inner_smul_right,
            inner_add_right, inner_smul_right, inner_smul_right, hcAA, hcTA, hcAT, hcTT]
          ring
theorem bTuple_plane_notMem {L N r : ℕ} [NeZero L] [NeZero N]
    (hL : 2 ≤ L) (hrL : L ≤ r) (hrN : r + L ≤ N) {R : Finset (Fin N)} (hR : R.card = r)
    (w : Fin L) {x : Fin L → Fin N} (hx0 : x 0 ∉ R) :
    √((r - w.1 : ℕ) : ℝ) * (bTuple L N R ⟨2 * w.1, by omega⟩).ofLp x +
      √((N - r - w.1 : ℕ) : ℝ) * (bTuple L N R ⟨2 * w.1 + 1, by omega⟩).ofLp x = 0 := by
  by_cases hw0 : w.1 = 0
  · have hw_eq : (⟨2 * w.1, by omega⟩ : Fin (2 * L)) = ⟨0, by omega⟩ :=
      Fin.ext (by simp [hw0])
    have hw_odd : (⟨2 * w.1 + 1, by omega⟩ : Fin (2 * L)) = ⟨2 * 1 - 1, by omega⟩ :=
      Fin.ext (by simp [hw0])
    rw [hw_eq, hw_odd, hw0, Nat.sub_zero, Nat.sub_zero, bTuple_zero L N R (by omega),
      bTuple_odd L N R (by omega) (by omega)]
    unfold b0TupleVec qVec; rw [hR]; simp only [PiLp.smul_apply, smul_eq_mul]
    by_cases hx : Function.Injective x
    · have hraw : (rawLiftA (L := L) 1 ((1 / √(swLQNormSqNat N r 1 : ℝ)) • qVecRaw R 1)).ofLp x =
          (1 / √(swLQNormSqNat N r 1 : ℝ)) * (rawLiftA (L := L) 1 (qVecRaw R 1)).ofLp x :=
        congrFun (congrArg WithLp.ofLp ((rawLiftALin L N 1).map_smul _ (qVecRaw R 1))) x
      rw [hraw]
      have hval : (rawLiftA (L := L) 1 (qVecRaw R 1)).ofLp x =
          - (((r * ((r - 1).factorial * (N - r - 1).factorial) : ℕ) : ℝ)) := by
        unfold rawLiftA qVecRaw
        have himg : Finset.image x (insert 0 ∅) = {x 0} := by simp
        simp only [hx, ↓reduceIte, Nat.sub_self, Finset.powersetCard_zero, Finset.sum_singleton,
          himg, Finset.card_singleton]
        have hint : ({x 0} ∩ R : Finset (Fin N)) = ∅ := by
          ext z; simp only [Finset.mem_inter, Finset.mem_singleton, Finset.notMem_empty, iff_false]
          rintro ⟨rfl, hz⟩; exact hx0 hz
        simp only [hint, Finset.card_empty, add_zero, pow_one, Nat.sub_zero, hR]
        have hrf : r.factorial = r * (r - 1).factorial := by
          have ha : r = (r - 1) + 1 := by omega
          conv_lhs => rw [ha, Nat.factorial_succ]
          rw [← ha]
        rw [hrf]; push_cast; ring
      rw [hval]; simp only [hx, ↓reduceIte]
      have hrel := congrArg (Nat.cast (R := ℝ))
        (cAANat_one_mul_qVecNormSqNat (L := L) hL (by omega) hrN)
      have hsq_root : √(swLCaaNat L N 1 : ℝ) * √(swLQNormSqNat N r 1 : ℝ) =
          √(r : ℝ) * √((N - r : ℕ) : ℝ) * (((r - 1).factorial * (N - r - 1).factorial : ℕ) : ℝ) *
            √((L.factorial * N.choose L : ℕ) : ℝ) := by
        rw [← Real.sqrt_mul (by positivity), ← Nat.cast_mul, hrel]
        push_cast
        rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity),
          Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
      have hposL : (0 : ℝ) < √((L.factorial * N.choose L : ℕ) : ℝ) :=
        Real.sqrt_pos.2 (by
          exact_mod_cast Nat.mul_pos (Nat.factorial_pos L) (Nat.choose_pos (by omega)))
      have hposR : (0 : ℝ) < √(r : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast (by omega : 0 < r))
      have hposU : (0 : ℝ) < √((N - r : ℕ) : ℝ) :=
        Real.sqrt_pos.2 (by exact_mod_cast (by omega : 0 < N - r))
      have hposF : (0 : ℝ) < (((r - 1).factorial * (N - r - 1).factorial : ℕ) : ℝ) := by
        exact_mod_cast Nat.mul_pos (Nat.factorial_pos _) (Nat.factorial_pos _)
      have h1 : (1 / √(swLCaaNat L N 1 : ℝ)) * ((1 / √(swLQNormSqNat N r 1 : ℝ)) *
          -(((r * ((r - 1).factorial * (N - r - 1).factorial) : ℕ) : ℝ))) =
          -(((r * ((r - 1).factorial * (N - r - 1).factorial) : ℕ) : ℝ)) /
            (√(swLCaaNat L N 1 : ℝ) * √(swLQNormSqNat N r 1 : ℝ)) := by ring
      rw [h1, hsq_root]; push_cast; field_simp [hposL.ne', hposR.ne', hposU.ne', hposF.ne']
      rw [Real.sq_sqrt (by positivity)]
      ring
    · have hraw0 : ∀ f, (rawLiftA (L := L) 1 f).ofLp x = 0 := fun f ↦ by
        unfold rawLiftA; simp [hx]
      simp [hx, hraw0]
  · have hw1 : 1 ≤ w.1 := by omega
    have hwL : w.1 + 1 ≤ L := by omega
    have hw_odd : (⟨2 * w.1 + 1, by omega⟩ : Fin (2 * L)) = ⟨2 * (w.1 + 1) - 1, by omega⟩ :=
      Fin.ext (by simp; omega)
    rw [bTuple_even L N R hw1 hwL, hw_odd, bTuple_odd L N R (by omega) hwL]
    unfold qVec; rw [hR]
    have hrawB := congrFun (congrArg WithLp.ofLp
      ((rawLiftBLin L N w.1).map_smul (1 / √(swLQNormSqNat N r w.1 : ℝ)) (qVecRaw R w.1))) x
    have hrawA := congrFun (congrArg WithLp.ofLp ((rawLiftALin L N (w.1 + 1)).map_smul
        (1 / √(swLQNormSqNat N r (w.1 + 1) : ℝ)) (qVecRaw R (w.1 + 1)))) x
    simp only [PiLp.smul_apply, smul_eq_mul] at hrawB hrawA ⊢
    rw [rawLiftBLin_apply, rawLiftBLin_apply] at hrawB
    rw [rawLiftALin_apply, rawLiftALin_apply] at hrawA
    change √((r - w.1 : ℕ) : ℝ) * (1 / √(cBBNat L N w.1 : ℝ) *
          (rawLiftB (L := L) w.1 ((1 / √(swLQNormSqNat N r w.1 : ℝ)) • qVecRaw R w.1)).ofLp x) +
      √((N - r - w.1 : ℕ) : ℝ) * (1 / √(swLCaaNat L N (w.1 + 1) : ℝ) * (rawLiftA (L := L) (w.1 + 1)
            ((1 / √(swLQNormSqNat N r (w.1 + 1) : ℝ)) • qVecRaw R (w.1 + 1))).ofLp x) = 0
    rw [hrawB, hrawA, rawLiftB_qVecRaw_of_notMem hw1 hwL (by omega) hrN hR hx0]
    set A := (rawLiftA (L := L) (w.1 + 1) (qVecRaw R (w.1 + 1))).ofLp x
    have hrel := congrArg (Nat.cast (R := ℝ))
      (cBBNat_mul_qVecNormSqNat (L := L) hw1 hwL (by omega) hrN)
    have hsq_root : √(cBBNat L N w.1 : ℝ) * √(swLQNormSqNat N r w.1 : ℝ) =
        √((r - w.1 : ℕ) : ℝ) * √((N - r - w.1 : ℕ) : ℝ) * ((N - w.1 + 1 : ℕ) : ℝ) *
          (√(swLCaaNat L N (w.1 + 1) : ℝ) * √(swLQNormSqNat N r (w.1 + 1) : ℝ)) := by
      rw [← Real.sqrt_mul (by positivity), ← Nat.cast_mul, hrel,
        Nat.cast_mul, Nat.cast_mul, Nat.cast_mul, Nat.cast_mul]
      rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity),
        Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity)]
      push_cast
      rw [Real.sqrt_sq (by positivity)]
    have hposrw : (0 : ℝ) < √((r - w.1 : ℕ) : ℝ) :=
      Real.sqrt_pos.2 (by exact_mod_cast (by omega : 0 < r - w.1))
    have hposu : (0 : ℝ) < √((N - r - w.1 : ℕ) : ℝ) :=
      Real.sqrt_pos.2 (by exact_mod_cast (by omega : 0 < N - r - w.1))
    have hposN : (0 : ℝ) < ((N - w.1 + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < N - w.1 + 1)
    have hposA1 : (0 : ℝ) < √(swLCaaNat L N (w.1 + 1) : ℝ) :=
      Real.sqrt_pos.2 (by exact_mod_cast cAANat_pos (by omega) hwL (by omega))
    have hposQ1 : (0 : ℝ) < √(swLQNormSqNat N r (w.1 + 1) : ℝ) := by
      unfold swLQNormSqNat; apply Real.sqrt_pos.2
      exact_mod_cast Nat.mul_pos
        (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (Nat.factorial_pos _) (Nat.factorial_pos _))
          (Nat.factorial_pos _)) (Nat.factorial_pos _))
        (Nat.choose_pos (by omega))
    have hrew : 1 / √(cBBNat L N w.1 : ℝ) * (1 / √(swLQNormSqNat N r w.1 : ℝ) *
          (-(((N - r - w.1) * (N - w.1 + 1) : ℕ) : ℝ) * A)) =
        -(((N - r - w.1) * (N - w.1 + 1) : ℕ) : ℝ) * A /
          (√(cBBNat L N w.1 : ℝ) * √(swLQNormSqNat N r w.1 : ℝ)) := by ring
    rw [hrew, hsq_root]; rw [Nat.cast_mul]
    field_simp [hposrw.ne', hposu.ne', hposN.ne', hposA1.ne', hposQ1.ne']
    rw [Real.sq_sqrt (by positivity)]
    ring
theorem bTuple_plane_mem {L N r : ℕ} [NeZero L] [NeZero N]
    (hL : 2 ≤ L) (hrL : L ≤ r) (hrN : r + L ≤ N) {R : Finset (Fin N)} (hR : R.card = r)
    (w : Fin L) {x : Fin L → Fin N} (hx0 : x 0 ∈ R) :
    √((N - r - w.1 : ℕ) : ℝ) * (bTuple L N R ⟨2 * w.1, by omega⟩).ofLp x -
      √((r - w.1 : ℕ) : ℝ) * (bTuple L N R ⟨2 * w.1 + 1, by omega⟩).ofLp x = 0 := by
  by_cases hw0 : w.1 = 0
  · have hw_eq : (⟨2 * w.1, by omega⟩ : Fin (2 * L)) = ⟨0, by omega⟩ :=
      Fin.ext (by simp [hw0])
    have hw_odd : (⟨2 * w.1 + 1, by omega⟩ : Fin (2 * L)) = ⟨2 * 1 - 1, by omega⟩ :=
      Fin.ext (by simp [hw0])
    rw [hw_eq, hw_odd, hw0, Nat.sub_zero, Nat.sub_zero, bTuple_zero L N R (by omega),
      bTuple_odd L N R (by omega) (by omega)]
    unfold b0TupleVec qVec; rw [hR]; simp only [PiLp.smul_apply, smul_eq_mul]
    by_cases hx : Function.Injective x
    · have hraw : (rawLiftA (L := L) 1 ((1 / √(swLQNormSqNat N r 1 : ℝ)) • qVecRaw R 1)).ofLp x =
          (1 / √(swLQNormSqNat N r 1 : ℝ)) * (rawLiftA (L := L) 1 (qVecRaw R 1)).ofLp x :=
        congrFun (congrArg WithLp.ofLp ((rawLiftALin L N 1).map_smul _ (qVecRaw R 1))) x
      rw [hraw]
      have hval : (rawLiftA (L := L) 1 (qVecRaw R 1)).ofLp x =
          (((N - r) * ((r - 1).factorial * (N - r - 1).factorial) : ℕ) : ℝ) := by
        unfold rawLiftA qVecRaw
        have himg : Finset.image x (insert 0 ∅) = {x 0} := by simp
        simp only [hx, ↓reduceIte, Nat.sub_self, Finset.powersetCard_zero, Finset.sum_singleton,
          himg, Finset.card_singleton]
        have hint : ({x 0} ∩ R : Finset (Fin N)) = {x 0} := by
          ext z; simp only [Finset.mem_inter, Finset.mem_singleton, and_iff_left_iff_imp]
          rintro rfl; exact hx0
        simp only [hint, Finset.card_singleton, hR]
        have hpow : (-1 : ℝ) ^ (1 + 1) = 1 := by norm_num
        have hsub : N - r - 1 + 1 = N - r := by omega
        have huf : (N - r).factorial = (N - r) * (N - r - 1).factorial := by
          have ha : N - r = (N - r - 1) + 1 := by omega
          conv_lhs => rw [ha, Nat.factorial_succ]
          rw [← ha]
        rw [hpow, hsub, huf]; push_cast; ring
      rw [hval]; simp only [hx, ↓reduceIte]
      have hrel := congrArg (Nat.cast (R := ℝ))
        (cAANat_one_mul_qVecNormSqNat (L := L) hL (by omega) hrN)
      have hsq_root : √(swLCaaNat L N 1 : ℝ) * √(swLQNormSqNat N r 1 : ℝ) =
          √(r : ℝ) * √((N - r : ℕ) : ℝ) * (((r - 1).factorial * (N - r - 1).factorial : ℕ) : ℝ) *
            √((L.factorial * N.choose L : ℕ) : ℝ) := by
        rw [← Real.sqrt_mul (by positivity), ← Nat.cast_mul, hrel]
        push_cast
        rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity),
          Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
      have hposL : (0 : ℝ) < √((L.factorial * N.choose L : ℕ) : ℝ) :=
        Real.sqrt_pos.2 (by
          exact_mod_cast Nat.mul_pos (Nat.factorial_pos L) (Nat.choose_pos (by omega)))
      have hposR : (0 : ℝ) < √(r : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast (by omega : 0 < r))
      have hposU : (0 : ℝ) < √((N - r : ℕ) : ℝ) :=
        Real.sqrt_pos.2 (by exact_mod_cast (by omega : 0 < N - r))
      have hposF : (0 : ℝ) < (((r - 1).factorial * (N - r - 1).factorial : ℕ) : ℝ) := by
        exact_mod_cast Nat.mul_pos (Nat.factorial_pos _) (Nat.factorial_pos _)
      have h1 : (1 / √(swLCaaNat L N 1 : ℝ)) * ((1 / √(swLQNormSqNat N r 1 : ℝ)) *
          (((N - r) * ((r - 1).factorial * (N - r - 1).factorial) : ℕ) : ℝ)) =
          (((N - r) * ((r - 1).factorial * (N - r - 1).factorial) : ℕ) : ℝ) /
            (√(swLCaaNat L N 1 : ℝ) * √(swLQNormSqNat N r 1 : ℝ)) := by ring
      rw [h1, hsq_root]; push_cast; field_simp [hposL.ne', hposR.ne', hposU.ne', hposF.ne']
      rw [Real.sq_sqrt (by positivity)]
      ring
    · have hraw0 : ∀ f, (rawLiftA (L := L) 1 f).ofLp x = 0 := fun f ↦ by
        unfold rawLiftA; simp [hx]
      simp [hx, hraw0]
  · have hw1 : 1 ≤ w.1 := by omega
    have hwL : w.1 + 1 ≤ L := by omega
    have hw_odd : (⟨2 * w.1 + 1, by omega⟩ : Fin (2 * L)) = ⟨2 * (w.1 + 1) - 1, by omega⟩ :=
      Fin.ext (by simp; omega)
    rw [bTuple_even L N R hw1 hwL, hw_odd, bTuple_odd L N R (by omega) hwL]
    unfold qVec; rw [hR]
    have hrawB := congrFun (congrArg WithLp.ofLp
      ((rawLiftBLin L N w.1).map_smul (1 / √(swLQNormSqNat N r w.1 : ℝ)) (qVecRaw R w.1))) x
    have hrawA := congrFun (congrArg WithLp.ofLp ((rawLiftALin L N (w.1 + 1)).map_smul
        (1 / √(swLQNormSqNat N r (w.1 + 1) : ℝ)) (qVecRaw R (w.1 + 1)))) x
    simp only [PiLp.smul_apply, smul_eq_mul] at hrawB hrawA ⊢
    rw [rawLiftBLin_apply, rawLiftBLin_apply] at hrawB
    rw [rawLiftALin_apply, rawLiftALin_apply] at hrawA
    change √((N - r - w.1 : ℕ) : ℝ) * (1 / √(cBBNat L N w.1 : ℝ) *
          (rawLiftB (L := L) w.1 ((1 / √(swLQNormSqNat N r w.1 : ℝ)) • qVecRaw R w.1)).ofLp x) -
      √((r - w.1 : ℕ) : ℝ) * (1 / √(swLCaaNat L N (w.1 + 1) : ℝ) * (rawLiftA (L := L) (w.1 + 1)
            ((1 / √(swLQNormSqNat N r (w.1 + 1) : ℝ)) • qVecRaw R (w.1 + 1))).ofLp x) = 0
    rw [hrawB, hrawA, rawLiftB_qVecRaw_of_mem hw1 hwL (by omega) hrN hR hx0]
    set A := (rawLiftA (L := L) (w.1 + 1) (qVecRaw R (w.1 + 1))).ofLp x
    have hrel := congrArg (Nat.cast (R := ℝ))
      (cBBNat_mul_qVecNormSqNat (L := L) hw1 hwL (by omega) hrN)
    have hsq_root : √(cBBNat L N w.1 : ℝ) * √(swLQNormSqNat N r w.1 : ℝ) =
        √((r - w.1 : ℕ) : ℝ) * √((N - r - w.1 : ℕ) : ℝ) * ((N - w.1 + 1 : ℕ) : ℝ) *
          (√(swLCaaNat L N (w.1 + 1) : ℝ) * √(swLQNormSqNat N r (w.1 + 1) : ℝ)) := by
      rw [← Real.sqrt_mul (by positivity), ← Nat.cast_mul, hrel,
        Nat.cast_mul, Nat.cast_mul, Nat.cast_mul, Nat.cast_mul]
      rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity),
        Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity)]
      push_cast
      rw [Real.sqrt_sq (by positivity)]
    have hposrw : (0 : ℝ) < √((r - w.1 : ℕ) : ℝ) :=
      Real.sqrt_pos.2 (by exact_mod_cast (by omega : 0 < r - w.1))
    have hposu : (0 : ℝ) < √((N - r - w.1 : ℕ) : ℝ) :=
      Real.sqrt_pos.2 (by exact_mod_cast (by omega : 0 < N - r - w.1))
    have hposN : (0 : ℝ) < ((N - w.1 + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < N - w.1 + 1)
    have hposA1 : (0 : ℝ) < √(swLCaaNat L N (w.1 + 1) : ℝ) :=
      Real.sqrt_pos.2 (by exact_mod_cast cAANat_pos (by omega) hwL (by omega))
    have hposQ1 : (0 : ℝ) < √(swLQNormSqNat N r (w.1 + 1) : ℝ) := by
      unfold swLQNormSqNat; apply Real.sqrt_pos.2
      exact_mod_cast Nat.mul_pos
        (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (Nat.factorial_pos _) (Nat.factorial_pos _))
          (Nat.factorial_pos _)) (Nat.factorial_pos _))
        (Nat.choose_pos (by omega))
    have hrew : 1 / √(cBBNat L N w.1 : ℝ) * (1 / √(swLQNormSqNat N r w.1 : ℝ) *
          ((((r - w.1) * (N - w.1 + 1) : ℕ) : ℝ) * A)) =
        (((r - w.1) * (N - w.1 + 1) : ℕ) : ℝ) * A /
          (√(cBBNat L N w.1 : ℝ) * √(swLQNormSqNat N r w.1 : ℝ)) := by ring
    rw [hrew, hsq_root]; rw [Nat.cast_mul]
    field_simp [hposrw.ne', hposu.ne', hposN.ne', hposA1.ne', hposQ1.ne']
    rw [Real.sq_sqrt (by positivity)]
    ring
theorem oracle0_plane_rot {α β ue uo : ℝ} (hα : 0 < α) (hβ : 0 < β) (hit : Bool)
    (hrel : if hit then √α * ue - √β * uo = 0 else √β * ue + √α * uo = 0) :
    let σ : ℝ := if hit then -1 else 1
    let cw : ℝ := (α - β) / (α + β)
    let sw : ℝ := 2 * √α * √β / (α + β)
    σ * ue = cw * ue - sw * uo ∧ σ * uo = -sw * ue - cw * uo := by
  intro σ cw sw
  have hsum : (α + β) ≠ 0 := by linarith
  have hsqα : √α * √α = α := Real.mul_self_sqrt hα.le
  have hsqβ : √β * √β = β := Real.mul_self_sqrt hβ.le
  cases hit
  · simp only [Bool.false_eq_true, ↓reduceIte, one_mul, σ, cw, sw] at hrel ⊢
    constructor
    · field_simp [hsum]
      linear_combination 2 * √β * hrel - 2 * ue * hsqβ
    · field_simp [hsum]
      linear_combination 2 * √α * hrel - 2 * uo * hsqα
  · simp only [↓reduceIte, neg_one_mul, σ, cw, sw] at hrel ⊢
    constructor
    · field_simp [hsum]
      linear_combination -2 * √α * hrel + 2 * ue * hsqα
    · field_simp [hsum]
      linear_combination 2 * √β * hrel + 2 * uo * hsqβ
theorem cos_sin_two_arcsin_sqrt {N r w : ℕ} (hwr : w < r) (hrN : r + w < N) :
    let θ := 2 * Real.arcsin √((r - w : ℝ) / (N - 2 * w : ℝ))
    let α : ℝ := ((N - r - w : ℕ) : ℝ)
    let β : ℝ := ((r - w : ℕ) : ℝ)
    Real.cos θ = (α - β) / (α + β) ∧
    Real.sin θ = 2 * √α * √β / (α + β) := by
  intro θ α β
  have hβ_eq : (r - w : ℝ) = β := (Nat.cast_sub (by omega : w ≤ r)).symm
  have hden_eq : (N : ℝ) - 2 * (w : ℝ) = α + β := by
    dsimp [α, β]
    rw [Nat.cast_sub (by omega : w ≤ N - r), Nat.cast_sub (by omega : r ≤ N),
      Nat.cast_sub (by omega : w ≤ r)]
    ring
  have hα : 0 < α := by dsimp [α]; exact_mod_cast (by omega : 0 < N - r - w)
  have hβ : 0 < β := by dsimp [β]; exact_mod_cast (by omega : 0 < r - w)
  have hsum : 0 < α + β := by linarith
  have hq_nonneg : 0 ≤ β / (α + β) := div_nonneg hβ.le hsum.le
  have hq_le : β / (α + β) ≤ 1 := (div_le_one hsum).2 (by linarith)
  set s := √(β / (α + β)); have hs_nonneg : 0 ≤ s := Real.sqrt_nonneg _
  have hs_le : s ≤ 1 := Real.sqrt_le_one.2 hq_le
  have hθ : θ = 2 * Real.arcsin s := by simp [θ, s, hβ_eq, hden_eq]
  have hsin_a : Real.sin (Real.arcsin s) = s := Real.sin_arcsin (by linarith) hs_le
  have hcos_a : Real.cos (Real.arcsin s) = √(α / (α + β)) := by
    rw [Real.cos_arcsin]; congr 1; rw [Real.sq_sqrt hq_nonneg]; field_simp [hsum.ne']; ring
  rw [hθ]
  constructor
  · rw [Real.cos_two_mul', hcos_a, hsin_a, Real.sq_sqrt (div_nonneg hα.le hsum.le),
      Real.sq_sqrt hq_nonneg]
    ring
  · rw [Real.sin_two_mul, hsin_a, hcos_a]
    change 2 * √(β / (α + β)) * √(α / (α + β)) = 2 * √α * √β / (α + β)
    rw [Real.sqrt_div hβ.le, Real.sqrt_div hα.le]; field_simp [(Real.sqrt_pos.2 hsum).ne', hsum.ne']
    rw [Real.sq_sqrt hsum.le]
theorem succ_fact_mul_choose (u k : ℕ) (hu : k + 1 ≤ u) :
    (k + 1).factorial * u.choose (k + 1) = u * (k.factorial * (u - 1).choose k) := by
  have hf1 := Nat.choose_mul_factorial_mul_factorial hu
  have hk_le : k ≤ u - 1 := by omega
  have hf2 := Nat.choose_mul_factorial_mul_factorial hk_le
  have hsub : u - 1 - k = u - (k + 1) := by omega
  rw [hsub] at hf2
  have huf : u.factorial = u * (u - 1).factorial := by
    have ha : u = (u - 1) + 1 := by omega
    conv_lhs => rw [ha, Nat.factorial_succ]
    rw [← ha]
  have hpos : 0 < (u - (k + 1)).factorial := Nat.factorial_pos _
  apply Nat.eq_of_mul_eq_mul_right hpos
  calc (k + 1).factorial * u.choose (k + 1) * (u - (k + 1)).factorial
      = u.choose (k + 1) * (k + 1).factorial * (u - (k + 1)).factorial := by ring
    _ = u.factorial := hf1
    _ = u * ((u - 1).choose k * k.factorial * (u - (k + 1)).factorial) := by rw [huf, ← hf2]
    _ = u * (k.factorial * (u - 1).choose k) * (u - (k + 1)).factorial := by ring
/-- Set of slot indices landing in `R`. -/
def hitSlotSet {L N : ℕ} (R : Finset (Fin N)) (x : Fin L → Fin N) : Finset (Fin L) :=
  Finset.univ.filter fun i ↦ x i ∈ R
/-- Injective `L`-tuples whose exact hit-slot set is `S₁`. -/
def exactHitSet (L N : ℕ) (R : Finset (Fin N)) (S₁ : Finset (Fin L)) :
    Finset (Fin L → Fin N) :=
  Finset.univ.filter fun x ↦ Function.Injective x ∧ hitSlotSet R x = S₁
/-- Bijection between `exactHitSet L N R S₁` and pairs of embeddings `(S₁ ↪ R) × (S₁ᶜ ↪
  Rᶜ)`. -/
def exactHitSetEquiv {L N : ℕ} (R : Finset (Fin N)) (S₁ : Finset (Fin L)) :
    ↥(exactHitSet L N R S₁) ≃ (↥S₁ ↪ ↥R) × (↥(S₁ᶜ) ↪ ↥(Rᶜ)) where
  toFun x :=
    let hx := (Finset.mem_filter.1 x.2).2
    have hmem : ∀ i : Fin L, i ∈ S₁ ↔ x.1 i ∈ R := fun i ↦ by
      have h := congrArg (i ∈ ·) hx.2.symm
      simpa [hitSlotSet] using h
    (⟨fun i ↦ ⟨x.1 i.1, (hmem i.1).1 i.2⟩,
        fun i j hij ↦ Subtype.ext (hx.1 (congrArg Subtype.val hij))⟩,
      ⟨fun i ↦ ⟨x.1 i.1, Finset.mem_compl.2 fun hR ↦
          (Finset.mem_compl.1 i.2) ((hmem i.1).2 hR)⟩,
        fun i j hij ↦ Subtype.ext (hx.1 (congrArg Subtype.val hij))⟩)
  invFun p :=
    let g : Fin L → Fin N := fun i ↦
      if hi : i ∈ S₁ then (p.1 ⟨i, hi⟩).1 else (p.2 ⟨i, Finset.mem_compl.2 hi⟩).1
    have hg_mem : ∀ i : Fin L, g i ∈ R ↔ i ∈ S₁ := fun i ↦ by
      by_cases hi : i ∈ S₁
      · simp [g, hi, (p.1 ⟨i, hi⟩).2]
      · have hc : g i ∉ R := by
          have hm := (p.2 ⟨i, Finset.mem_compl.2 hi⟩).2
          simpa [g, hi] using Finset.mem_compl.1 hm
        simp [hi, hc]
    ⟨g, Finset.mem_filter.2 ⟨Finset.mem_univ _, ⟨fun i j hij ↦ by
        have hiff : i ∈ S₁ ↔ j ∈ S₁ := by
          rw [← hg_mem i, hij, hg_mem j]
        by_cases hi : i ∈ S₁
        · have hj : j ∈ S₁ := hiff.1 hi
          have heq : (p.1 ⟨i, hi⟩).1 = (p.1 ⟨j, hj⟩).1 := by simpa [g, hi, hj] using hij
          exact congrArg Subtype.val (p.1.injective (Subtype.ext heq))
        · have hj : j ∉ S₁ := fun h ↦ hi (hiff.2 h)
          have heq : (p.2 ⟨i, Finset.mem_compl.2 hi⟩).1 =
              (p.2 ⟨j, Finset.mem_compl.2 hj⟩).1 := by simpa [g, hi, hj] using hij
          exact congrArg Subtype.val (p.2.injective (Subtype.ext heq)),
      by ext i; simp [hitSlotSet, hg_mem]⟩⟩⟩
  left_inv x := by
    ext i
    by_cases hi : i ∈ S₁ <;> simp only [hi, ↓reduceDIte] <;> rfl
  right_inv p := by
    refine Prod.ext (Function.Embedding.ext fun ⟨i, hi⟩ ↦ Subtype.ext ?_)
      (Function.Embedding.ext fun ⟨i, hi⟩ ↦ Subtype.ext ?_)
    · change (if hi' : i ∈ S₁ then (p.1 ⟨i, hi'⟩).1 else (p.2 ⟨i, Finset.mem_compl.2 hi'⟩).1) =
        (p.1 ⟨i, hi⟩).1
      simp only [hi, ↓reduceDIte]
    · have hni : i ∉ S₁ := Finset.mem_compl.1 hi
      change (if hi' : i ∈ S₁ then (p.1 ⟨i, hi'⟩).1 else (p.2 ⟨i, Finset.mem_compl.2 hi'⟩).1) =
        (p.2 ⟨i, hi⟩).1
      simp only [hni, ↓reduceDIte]
theorem card_exactHitSet {L N : ℕ} (R : Finset (Fin N)) (S₁ : Finset (Fin L)) :
    (exactHitSet L N R S₁).card =
      (S₁.card.factorial * R.card.choose S₁.card) *
        ((L - S₁.card).factorial * (N - R.card).choose (L - S₁.card)) := by
  have hc := Fintype.card_congr (exactHitSetEquiv R S₁)
  rw [Fintype.card_coe, Fintype.card_prod, Fintype.card_embedding_eq, Fintype.card_embedding_eq,
    Fintype.card_coe, Fintype.card_coe, Fintype.card_coe, Fintype.card_coe,
    Finset.card_compl, Finset.card_compl, Fintype.card_fin, Fintype.card_fin] at hc
  rw [hc, Nat.descFactorial_eq_factorial_mul_choose, Nat.descFactorial_eq_factorial_mul_choose]
/-- Set of tail slots landing in `R`. -/
def tailHitSet (L : ℕ) {N : ℕ} [NeZero L] (R : Finset (Fin N)) (x : Fin L → Fin N) :
    Finset (Fin L) :=
  (tailSlots L).filter fun p ↦ x p ∈ R
/-- Orbit index `2 * |tailHitSet| + [x 0 ∈ R]` in `Fin (2 * L)`. -/
def orbitIdxOf (L : ℕ) {N : ℕ} [NeZero L] (R : Finset (Fin N)) (x : Fin L → Fin N) :
    Fin (2 * L) :=
  ⟨2 * (tailHitSet L R x).card + (if x 0 ∈ R then 1 else 0), by
    have hle : (tailHitSet L R x).card ≤ (tailSlots L).card := Finset.card_filter_le _ _
    rw [card_tailSlots] at hle
    have hpos : 1 ≤ L := NeZero.one_le
    split_ifs <;> omega⟩
/-- Set of injective `L`-tuples in orbit `o: Fin (2 * L)`. -/
def orbitSet (L N : ℕ) [NeZero L] (R : Finset (Fin N)) (o : Fin (2 * L)) :
    Finset (Fin L → Fin N) :=
  Finset.univ.filter fun x ↦ Function.Injective x ∧ orbitIdxOf L R x = o
theorem mem_orbitSet_iff {L N : ℕ} [NeZero L] {R : Finset (Fin N)} {o : Fin (2 * L)}
    {x : Fin L → Fin N} :
    x ∈ orbitSet L N R o ↔
      Function.Injective x ∧
      (tailHitSet L R x).card = o.1 / 2 ∧
      (if x 0 ∈ R then 1 else 0) = o.1 % 2 := by
  simp only [orbitSet, Finset.mem_filter, Finset.mem_univ, true_and, Fin.ext_iff, orbitIdxOf]
  constructor
  · rintro ⟨hx, heq⟩
    refine ⟨hx, ?_, ?_⟩ <;> split_ifs at heq ⊢ <;> omega
  · rintro ⟨hx, hdiv, hmod⟩
    refine ⟨hx, ?_⟩
    omega
theorem orbitSet_disjoint {L N : ℕ} [NeZero L] (R : Finset (Fin N))
    {o₁ o₂ : Fin (2 * L)} (hne : o₁ ≠ o₂) :
    Disjoint (orbitSet L N R o₁) (orbitSet L N R o₂) := by
  rw [Finset.disjoint_left]; intro x hx1 hx2
  exact hne (((Finset.mem_filter.1 hx1).2.2).symm.trans (Finset.mem_filter.1 hx2).2.2)
theorem orbitSet_card_eq {L N r : ℕ} [NeZero L]
    (hL : 2 ≤ L) (hrL : L ≤ r) (hrN : r + L ≤ N) {R : Finset (Fin N)} (hR : R.card = r)
    (o : Fin (2 * L)) :
    (orbitSet L N R o).card = swLOrbitCardNat L N r o := by
  set b := o.1 % 2; set h := o.1 / 2
  have hhL : h ≤ L - 1 := by omega
  by_cases hb0 : b = 0
  · have horb : orbitSet L N R o =
        ((tailSlots L).powersetCard h).biUnion (exactHitSet L N R) := by
      ext x
      rw [mem_orbitSet_iff, Finset.mem_biUnion]
      constructor
      · rintro ⟨hx, hcard, hmod⟩
        have hx0 : x 0 ∉ R := by
          have hm : (if x 0 ∈ R then 1 else 0) = 0 := hmod.trans hb0
          intro h0R; simp [h0R] at hm
        refine ⟨tailHitSet L R x, Finset.mem_powersetCard.2 ⟨Finset.filter_subset _ _, hcard⟩,
          Finset.mem_filter.2 ⟨Finset.mem_univ _, hx, ?_⟩⟩
        ext i
        simp only [hitSlotSet, tailHitSet, tailSlots, Finset.mem_filter, Finset.mem_univ,
          true_and, Finset.mem_erase]
        by_cases hi0 : i = 0
        · subst hi0; simp [hx0]
        · simp [hi0]
      · rintro ⟨H, hH, hxH⟩
        rcases Finset.mem_powersetCard.1 hH with ⟨hHsub, hHcard⟩
        rcases (Finset.mem_filter.1 hxH).2 with ⟨hx, hhit⟩
        have h0H : (0 : Fin L) ∉ H := fun h0 ↦ (Finset.mem_erase.1 (hHsub h0)).1 rfl
        have hx0 : x 0 ∉ R := by
          intro hx0R
          have : (0 : Fin L) ∈ hitSlotSet R x := Finset.mem_filter.2 ⟨Finset.mem_univ _, hx0R⟩
          rw [hhit] at this; exact h0H this
        have htail : tailHitSet L R x = H := by
          ext i
          have hiH : i ∈ H ↔ x i ∈ R := by rw [← hhit]; simp [hitSlotSet]
          simp only [tailHitSet, Finset.mem_filter, ← hiH]
          exact ⟨fun h ↦ h.2, fun hi ↦ ⟨hHsub hi, hi⟩⟩
        refine ⟨hx, by rw [htail, hHcard], ?_⟩
        simp only [hx0, ↓reduceIte]; exact hb0.symm
    have hdisj : Set.PairwiseDisjoint
        ((tailSlots L).powersetCard h : Set (Finset (Fin L))) (exactHitSet L N R) := by
      intro H₁ _ H₂ _ hne; rw [Function.onFun, Finset.disjoint_left]; intro x hx1 hx2
      exact hne (((Finset.mem_filter.1 hx1).2.2).symm.trans (Finset.mem_filter.1 hx2).2.2)
    rw [horb, Finset.card_biUnion hdisj]
    have hconst : ∀ H ∈ (tailSlots L).powersetCard h, (exactHitSet L N R H).card =
          (h.factorial * r.choose h) * ((L - h).factorial * (N - r).choose (L - h)) := by
      intro H hH; rw [card_exactHitSet, (Finset.mem_powersetCard.1 hH).2, hR]
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, Finset.card_powersetCard, card_tailSlots,
      smul_eq_mul]
    unfold swLOrbitCardNat; have hb0' : o.1 % 2 = 0 := hb0; simp only [hb0', ↓reduceIte]
    have hLh : L - h = (L - 1 - h) + 1 := by omega
    have hsucc := succ_fact_mul_choose (N - r) (L - 1 - h) (by omega)
    rw [← hLh] at hsucc
    calc (L - 1).choose h * ((h.factorial * r.choose h) *
            ((L - h).factorial * (N - r).choose (L - h)))
        = (L - 1).choose h * (h.factorial * r.choose h) *
            ((L - h).factorial * (N - r).choose (L - h)) := by ring
      _ = (L - 1).choose h * (h.factorial * r.choose h) *
            ((N - r) * ((L - 1 - h).factorial * (N - r - 1).choose (L - 1 - h))) := by rw [hsucc]
      _ = (N - r) * (L - 1).choose h * (h.factorial * r.choose h) *
            ((L - 1 - h).factorial * (N - r - 1).choose (L - 1 - h)) := by ring
  · have hb1 : b = 1 := by omega
    have horb : orbitSet L N R o =
        ((tailSlots L).powersetCard h).biUnion (fun H ↦ exactHitSet L N R (insert 0 H)) := by
      ext x
      rw [mem_orbitSet_iff, Finset.mem_biUnion]
      constructor
      · rintro ⟨hx, hcard, hmod⟩
        have hx0 : x 0 ∈ R := by
          have hm : (if x 0 ∈ R then 1 else 0) = 1 := hmod.trans hb1
          by_contra h0R; simp [h0R] at hm
        refine ⟨tailHitSet L R x, Finset.mem_powersetCard.2 ⟨Finset.filter_subset _ _, hcard⟩,
          Finset.mem_filter.2 ⟨Finset.mem_univ _, hx, ?_⟩⟩
        ext i
        simp only [hitSlotSet, tailHitSet, tailSlots, Finset.mem_filter, Finset.mem_univ,
          true_and, Finset.mem_insert, Finset.mem_erase]
        by_cases hi0 : i = 0
        · subst hi0; simp [hx0]
        · simp [hi0]
      · rintro ⟨H, hH, hxH⟩
        rcases Finset.mem_powersetCard.1 hH with ⟨hHsub, hHcard⟩
        rcases (Finset.mem_filter.1 hxH).2 with ⟨hx, hhit⟩
        have h0H : (0 : Fin L) ∉ H := fun h0 ↦ (Finset.mem_erase.1 (hHsub h0)).1 rfl
        have hx0 : x 0 ∈ R := by
          have : (0 : Fin L) ∈ insert 0 H := Finset.mem_insert_self 0 H; rw [← hhit] at this
          exact (Finset.mem_filter.1 this).2
        have htail : tailHitSet L R x = H := by
          ext i
          have hiH : i ∈ insert 0 H ↔ x i ∈ R := by rw [← hhit]; simp [hitSlotSet]
          simp only [tailHitSet, tailSlots, Finset.mem_filter, Finset.mem_erase, Finset.mem_univ,
             and_true, ← hiH, Finset.mem_insert]
          constructor
          · rintro ⟨hne, rfl | hi⟩
            · exact False.elim (hne rfl)
            · exact hi
          · intro hi; exact ⟨(Finset.mem_erase.1 (hHsub hi)).1, Or.inr hi⟩
        refine ⟨hx, by rw [htail, hHcard], ?_⟩
        simp only [hx0, ↓reduceIte]; exact hb1.symm
    have hdisj : Set.PairwiseDisjoint
        ((tailSlots L).powersetCard h : Set (Finset (Fin L)))
        (fun H ↦ exactHitSet L N R (insert 0 H)) := by
      intro H₁ hH₁ H₂ hH₂ hne; rw [Function.onFun, Finset.disjoint_left]; intro x hx1 hx2
      have hins : insert (0 : Fin L) H₁ = insert (0 : Fin L) H₂ :=
        ((Finset.mem_filter.1 hx1).2.2).symm.trans (Finset.mem_filter.1 hx2).2.2
      have h01 : (0 : Fin L) ∉ H₁ := fun h0 ↦
        (Finset.mem_erase.1 ((Finset.mem_powersetCard.1 hH₁).1 h0)).1 rfl
      have h02 : (0 : Fin L) ∉ H₂ := fun h0 ↦
        (Finset.mem_erase.1 ((Finset.mem_powersetCard.1 hH₂).1 h0)).1 rfl
      have heq : H₁ = H₂ := by rw [← Finset.erase_insert h01, hins, Finset.erase_insert h02]
      exact hne heq
    rw [horb, Finset.card_biUnion hdisj]
    have hconst : ∀ H ∈ (tailSlots L).powersetCard h, (exactHitSet L N R (insert 0 H)).card =
          ((h + 1).factorial * r.choose (h + 1)) *
            ((L - 1 - h).factorial * (N - r).choose (L - 1 - h)) := by
      intro H hH
      rcases Finset.mem_powersetCard.1 hH with ⟨hHsub, hHcard⟩
      have h0H : (0 : Fin L) ∉ H := fun h0 ↦ (Finset.mem_erase.1 (hHsub h0)).1 rfl
      have hc : (insert (0 : Fin L) H).card = h + 1 := by
        rw [Finset.card_insert_of_notMem h0H, hHcard]
      have hsub : L - (h + 1) = L - 1 - h := by omega
      rw [card_exactHitSet, hc, hsub, hR]
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, Finset.card_powersetCard, card_tailSlots,
      smul_eq_mul]
    unfold swLOrbitCardNat; have hb0' : o.1 % 2 ≠ 0 := hb0; simp only [hb0', ↓reduceIte]
    have hsucc := succ_fact_mul_choose r h (by omega)
    calc (L - 1).choose h * (((h + 1).factorial * r.choose (h + 1)) *
            ((L - 1 - h).factorial * (N - r).choose (L - 1 - h)))
        = (L - 1).choose h * ((h + 1).factorial * r.choose (h + 1)) *
            ((L - 1 - h).factorial * (N - r).choose (L - 1 - h)) := by ring
      _ = (L - 1).choose h * (r * (h.factorial * (r - 1).choose h)) *
            ((L - 1 - h).factorial * (N - r).choose (L - 1 - h)) := by rw [hsucc]
      _ = r * (L - 1).choose h * (h.factorial * (r - 1).choose h) *
            ((L - 1 - h).factorial * (N - r).choose (L - 1 - h)) := by ring
theorem swLOrbitCardNat_pos {L N r : ℕ}
    (hL : 2 ≤ L) (hrL : L ≤ r) (hrN : r + L ≤ N) (o : Fin (2 * L)) :
    0 < swLOrbitCardNat L N r o := by
  unfold swLOrbitCardNat; dsimp only
  split_ifs
  · exact Nat.mul_pos
      (Nat.mul_pos (Nat.mul_pos (by omega) (Nat.choose_pos (by omega)))
        (Nat.mul_pos (Nat.factorial_pos _) (Nat.choose_pos (by omega))))
      (Nat.mul_pos (Nat.factorial_pos _) (Nat.choose_pos (by omega)))
  · exact Nat.mul_pos
      (Nat.mul_pos (Nat.mul_pos (by omega) (Nat.choose_pos (by omega)))
        (Nat.mul_pos (Nat.factorial_pos _) (Nat.choose_pos (by omega))))
      (Nat.mul_pos (Nat.factorial_pos _) (Nat.choose_pos (by omega)))
theorem rawLiftA_qVecRaw_on_orbit {L N r m : ℕ} [NeZero L]
    (hm1 : 1 ≤ m) (_hmL : m ≤ L) {R : Finset (Fin N)} (hR : R.card = r)
    {o : Fin (2 * L)} {x : Fin L → Fin N} (hx_orb : x ∈ orbitSet L N R o) :
    (rawLiftA (L := L) m (qVecRaw R m)).ofLp x =
      swLRawLiftAOnOrbit L N r m (o.1 % 2) (o.1 / 2) := by
  rcases mem_orbitSet_iff.1 hx_orb with ⟨hx, hcard, hmod⟩
  set b := o.1 % 2; set h := o.1 / 2
  set H := tailHitSet L R x; have hHU : H ⊆ tailSlots L := Finset.filter_subset _ _; unfold rawLiftA
  change (if Function.Injective x then
      ∑ K' ∈ (tailSlots L).powersetCard (m - 1),
        (qVecRaw R m).ofLp ((insert (0 : Fin L) K').image x)
    else 0) = swLRawLiftAOnOrbit L N r m b h
  simp only [hx, ↓reduceIte]
  have hterm : ∀ K' ∈ (tailSlots L).powersetCard (m - 1),
      (qVecRaw R m).ofLp ((insert (0 : Fin L) K').image x) = (-1 : ℝ) ^ (m + (b + (H ∩ K').card)) *
          (((r - (b + (H ∩ K').card)).factorial *
            (N - r - m + (b + (H ∩ K').card)).factorial : ℕ) : ℝ) := by
    intro K' hK'
    rcases Finset.mem_powersetCard.1 hK' with ⟨hK'sub, hK'card⟩
    have h0K' : (0 : Fin L) ∉ K' := fun h0 ↦ (Finset.mem_erase.1 (hK'sub h0)).1 rfl
    have hcard_img : ((insert (0 : Fin L) K').image x).card = m := by
      rw [Finset.card_image_of_injective _ hx, Finset.card_insert_of_notMem h0K', hK'card]; omega
    have hinter_card : (((insert (0 : Fin L) K').image x) ∩ R).card = b + (H ∩ K').card := by
      have himg_inter : ((insert (0 : Fin L) K').image x) ∩ R =
          ((insert (0 : Fin L) K').filter fun i ↦ x i ∈ R).image x := by
        ext y
        simp only [Finset.mem_inter, Finset.mem_image, Finset.mem_filter]
        constructor
        · rintro ⟨⟨i, hi, rfl⟩, hyR⟩
          exact ⟨i, ⟨hi, hyR⟩, rfl⟩
        · rintro ⟨i, ⟨hi, hyR⟩, rfl⟩
          exact ⟨⟨i, hi, rfl⟩, hyR⟩
      rw [himg_inter, Finset.card_image_of_injective _ hx, Finset.filter_insert]
      have hfilt_eq : K'.filter (fun i ↦ x i ∈ R) = H ∩ K' := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_inter, H, tailHitSet]
        exact ⟨fun ⟨hiK, hxi⟩ ↦ ⟨⟨hK'sub hiK, hxi⟩, hiK⟩, fun ⟨⟨_, hxi⟩, hiK⟩ ↦ ⟨hiK, hxi⟩⟩
      split_ifs with hx0R
      · have hb1 : b = 1 := by
          have : (if x 0 ∈ R then 1 else 0) = 1 := by simp [hx0R]
          exact hmod.symm.trans this
        have h0HK : (0 : Fin L) ∉ K'.filter (fun i ↦ x i ∈ R) :=
          fun h0 ↦ h0K' (Finset.mem_filter.1 h0).1
        rw [Finset.card_insert_of_notMem h0HK, hfilt_eq, hb1, add_comm]
      · have hb0 : b = 0 := by
          have : (if x 0 ∈ R then 1 else 0) = 0 := by simp [hx0R]
          exact hmod.symm.trans this
        rw [hfilt_eq, hb0, zero_add]
    unfold qVecRaw
    change (if ((insert (0 : Fin L) K').image x).card = m then _ else 0) = _
    simp only [hcard_img, ↓reduceIte, hinter_card, hR]
  rw [Finset.sum_congr rfl hterm]
  have hsum := sum_powersetCard_inter_card hHU (m - 1) (fun u ↦
    (-1 : ℝ) ^ (m + (b + u)) *
      (((r - (b + u)).factorial * (N - r - m + (b + u)).factorial : ℕ) : ℝ))
  have hm_eq : m - 1 + 1 = m := by omega
  rw [hsum, hm_eq, hcard, card_tailSlots]; unfold swLRawLiftAOnOrbit
  refine Finset.sum_congr rfl fun u _ ↦ by ring
theorem bTuple_of_not_injective {L N : ℕ} [NeZero L] (R : Finset (Fin N))
    (j : Fin (2 * L)) {x : Fin L → Fin N} (hx : ¬ Function.Injective x) :
    (bTuple L N R j).ofLp x = 0 := by
  unfold bTuple
  split_ifs
  · unfold b0TupleVec; simp only [PiLp.smul_apply, smul_eq_mul]
    change _ * (if Function.Injective x then 1 else 0) = 0
    simp [hx]
  · simp only [PiLp.smul_apply, smul_eq_mul]; unfold rawLiftA
    change _ * (if Function.Injective x then _ else 0) = 0
    simp [hx]
  · simp only [PiLp.smul_apply, smul_eq_mul]; unfold rawLiftB rawLiftA rawLiftT
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    change _ * (_ * (if Function.Injective x then _ else 0) +
      _ * (if Function.Injective x then _ else 0)) = 0
    simp [hx]
theorem bTuple_const_on_orbit {L N r : ℕ} [NeZero L] [NeZero N]
    (hL : 2 ≤ L) (hrL : L ≤ r) (hrN : r + L ≤ N) {R : Finset (Fin N)} (hR : R.card = r)
    (o j : Fin (2 * L)) {x₁ x₂ : Fin L → Fin N}
    (hx₁ : x₁ ∈ orbitSet L N R o) (hx₂ : x₂ ∈ orbitSet L N R o) :
    (bTuple L N R j).ofLp x₁ = (bTuple L N R j).ofLp x₂ := by
  rcases mem_orbitSet_iff.1 hx₁ with ⟨hinj₁, _, hmod₁⟩
  rcases mem_orbitSet_iff.1 hx₂ with ⟨hinj₂, _, hmod₂⟩
  have hodd : ∀ (m : ℕ) (hm1 : 1 ≤ m) (hmL : m ≤ L),
      (bTuple L N R ⟨2 * m - 1, by omega⟩).ofLp x₁ =
        (bTuple L N R ⟨2 * m - 1, by omega⟩).ofLp x₂ := by
    intro m hm1 hmL; rw [bTuple_odd L N R hm1 hmL]; unfold qVec
    have h1 := congrFun (congrArg WithLp.ofLp
      ((rawLiftALin L N m).map_smul (1 / √(swLQNormSqNat N R.card m : ℝ)) (qVecRaw R m))) x₁
    have h2 := congrFun (congrArg WithLp.ofLp
      ((rawLiftALin L N m).map_smul (1 / √(swLQNormSqNat N R.card m : ℝ)) (qVecRaw R m))) x₂
    simp only [PiLp.smul_apply, smul_eq_mul, rawLiftALin_apply] at h1 h2 ⊢
    change 1 / √(swLCaaNat L N m : ℝ) *
        (rawLiftA (L := L) m ((1 / √(swLQNormSqNat N R.card m : ℝ)) • qVecRaw R m)).ofLp x₁ =
      1 / √(swLCaaNat L N m : ℝ) *
        (rawLiftA (L := L) m ((1 / √(swLQNormSqNat N R.card m : ℝ)) • qVecRaw R m)).ofLp x₂
    rw [h1, h2, rawLiftA_qVecRaw_on_orbit hm1 hmL hR hx₁, rawLiftA_qVecRaw_on_orbit hm1 hmL hR hx₂]
  by_cases hj0 : j.1 = 0
  · have hj_eq : j = ⟨0, by omega⟩ := Fin.ext hj0
    rw [hj_eq, bTuple_zero L N R (by omega)]
    unfold b0TupleVec; simp only [PiLp.smul_apply, smul_eq_mul]
    change _ * (if Function.Injective x₁ then 1 else 0) =
      _ * (if Function.Injective x₂ then 1 else 0)
    simp [hinj₁, hinj₂]
  · by_cases hjmod : j.1 % 2 = 1
    · set m := (j.1 + 1) / 2
      have hj_eq : j = ⟨2 * m - 1, by omega⟩ := Fin.ext (by dsimp [m]; omega)
      rw [hj_eq]
      exact hodd m (by omega) (by omega)
    · set w := j.1 / 2
      have hw1 : 1 ≤ w := by omega
      have hwL : w < L := by omega
      have hj_eq : j = ⟨2 * w, by omega⟩ := Fin.ext (by dsimp [w]; omega)
      rw [hj_eq]
      have hodd_w := hodd (w + 1) (by omega) (by omega)
      have hw_idx : (⟨2 * (w + 1) - 1, by omega⟩ : Fin (2 * L)) = ⟨2 * w + 1, by omega⟩ :=
        Fin.ext (by simp; omega)
      rw [hw_idx] at hodd_w
      by_cases hb0 : o.1 % 2 = 0
      · have hx1_0 : x₁ 0 ∉ R := by have hm := hmod₁.trans hb0; intro h0R; simp [h0R] at hm
        have hx2_0 : x₂ 0 ∉ R := by have hm := hmod₂.trans hb0; intro h0R; simp [h0R] at hm
        have hp1 := bTuple_plane_notMem hL hrL hrN hR ⟨w, hwL⟩ hx1_0
        have hp2 := bTuple_plane_notMem hL hrL hrN hR ⟨w, hwL⟩ hx2_0; dsimp only at hp1 hp2
        have hpos : (0 : ℝ) < √((r - w : ℕ) : ℝ) :=
          Real.sqrt_pos.2 (by exact_mod_cast (by omega : 0 < r - w))
        have hdiff : √((r - w : ℕ) : ℝ) *
            ((bTuple L N R ⟨2 * w, by omega⟩).ofLp x₁ -
              (bTuple L N R ⟨2 * w, by omega⟩).ofLp x₂) = 0 := by
          linear_combination hp1 - hp2 - √((N - r - w : ℕ) : ℝ) * hodd_w
        rcases mul_eq_zero.1 hdiff with h0 | h0
        · exact False.elim (hpos.ne' h0)
        · linarith
      · have hb1 : o.1 % 2 = 1 := by omega
        have hx1_0 : x₁ 0 ∈ R := by
          have hm := hmod₁.trans hb1; by_contra h0R; simp [h0R] at hm
        have hx2_0 : x₂ 0 ∈ R := by
          have hm := hmod₂.trans hb1; by_contra h0R; simp [h0R] at hm
        have hp1 := bTuple_plane_mem hL hrL hrN hR ⟨w, hwL⟩ hx1_0
        have hp2 := bTuple_plane_mem hL hrL hrN hR ⟨w, hwL⟩ hx2_0; dsimp only at hp1 hp2
        have hpos : (0 : ℝ) < √((N - r - w : ℕ) : ℝ) :=
          Real.sqrt_pos.2 (by exact_mod_cast (by omega : 0 < N - r - w))
        have hdiff : √((N - r - w : ℕ) : ℝ) *
            ((bTuple L N R ⟨2 * w, by omega⟩).ofLp x₁ -
              (bTuple L N R ⟨2 * w, by omega⟩).ofLp x₂) = 0 := by
          linear_combination hp1 - hp2 + √((r - w : ℕ) : ℝ) * hodd_w
        rcases mul_eq_zero.1 hdiff with h0 | h0
        · exact False.elim (hpos.ne' h0)
        · linarith
/-- Normalized indicator unit vector on `orbitSet L N R o`. -/
noncomputable def orbitUnitVec (L N : ℕ) [NeZero L] (R : Finset (Fin N)) (o : Fin (2 * L)) :
    EuclideanSpace ℝ (Fin L → Fin N) :=
  (1 / √((orbitSet L N R o).card : ℝ)) •
    WithLp.toLp 2 (fun x : Fin L → Fin N ↦ if x ∈ orbitSet L N R o then (1 : ℝ) else 0)
theorem inner_orbitUnitVec {L N r : ℕ} [NeZero L]
    (hL : 2 ≤ L) (hrL : L ≤ r) (hrN : r + L ≤ N) {R : Finset (Fin N)} (hR : R.card = r)
    (o₁ o₂ : Fin (2 * L)) :
    ⟪orbitUnitVec L N R o₁, orbitUnitVec L N R o₂⟫ = if o₁ = o₂ then 1 else 0 := by
  by_cases heq : o₁ = o₂
  · subst heq
    simp only [↓reduceIte, orbitUnitVec, inner_smul_left, inner_smul_right,
      PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
    have hsum : (∑ x : Fin L → Fin N,
        (if x ∈ orbitSet L N R o₁ then (1 : ℝ) else 0) *
          (if x ∈ orbitSet L N R o₁ then (1 : ℝ) else 0)) =
        ((orbitSet L N R o₁).card : ℝ) := by
      have h1 : ∀ x : Fin L → Fin N,
          (if x ∈ orbitSet L N R o₁ then (1 : ℝ) else 0) *
            (if x ∈ orbitSet L N R o₁ then (1 : ℝ) else 0) =
          if x ∈ orbitSet L N R o₁ then 1 else 0 := fun x ↦ by split_ifs <;> ring
      simp_rw [h1]; simp
    change (1 / √((orbitSet L N R o₁).card : ℝ)) * ((1 / √((orbitSet L N R o₁).card : ℝ)) * _) = 1
    rw [hsum]
    have hpos : (0 : ℝ) < ((orbitSet L N R o₁).card : ℝ) := by
      rw [orbitSet_card_eq hL hrL hrN hR]
      exact_mod_cast swLOrbitCardNat_pos hL hrL hrN o₁
    field_simp; rw [Real.sq_sqrt hpos.le]
  · simp only [heq, ↓reduceIte, orbitUnitVec, inner_smul_left, inner_smul_right,
      PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
    have h0 : ∀ x : Fin L → Fin N,
        (if x ∈ orbitSet L N R o₂ then (1 : ℝ) else 0) *
          (if x ∈ orbitSet L N R o₁ then (1 : ℝ) else 0) = 0 := by
      intro x
      by_cases hx1 : x ∈ orbitSet L N R o₁
      · have hx2 : x ∉ orbitSet L N R o₂ := Finset.disjoint_left.1 (orbitSet_disjoint R heq) hx1
        simp [hx1, hx2]
      · simp [hx1]
    change _ * (_ * ∑ x : Fin L → Fin N,
      (if x ∈ orbitSet L N R o₂ then (1 : ℝ) else 0) *
        (if x ∈ orbitSet L N R o₁ then (1 : ℝ) else 0)) = 0
    simp_rw [h0, Finset.sum_const_zero, mul_zero]
/-- `2L × 2L` overlap matrix `M o j = ⟪orbitUnitVec L N R o, bTuple L N R j⟫`. -/
noncomputable def overlapTupleMat (L N : ℕ) [NeZero L] (R : Finset (Fin N))
    (o j : Fin (2 * L)) : ℝ :=
  ⟪orbitUnitVec L N R o, bTuple L N R j⟫
theorem overlapTupleMat_eq_on_orbit {L N r : ℕ} [NeZero L] [NeZero N]
    (hL : 2 ≤ L) (hrL : L ≤ r) (hrN : r + L ≤ N) {R : Finset (Fin N)} (hR : R.card = r)
    (o j : Fin (2 * L)) {x₀ : Fin L → Fin N} (hx₀ : x₀ ∈ orbitSet L N R o) :
    overlapTupleMat L N R o j =
      √((orbitSet L N R o).card : ℝ) * (bTuple L N R j).ofLp x₀ := by
  unfold overlapTupleMat orbitUnitVec
  simp only [inner_smul_left, PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  have hsum : (∑ x : Fin L → Fin N,
      (bTuple L N R j).ofLp x * (if x ∈ orbitSet L N R o then (1 : ℝ) else 0)) =
      ((orbitSet L N R o).card : ℝ) * (bTuple L N R j).ofLp x₀ := by
    have h1 : ∀ x : Fin L → Fin N,
        (bTuple L N R j).ofLp x * (if x ∈ orbitSet L N R o then (1 : ℝ) else 0) =
          if x ∈ orbitSet L N R o then (bTuple L N R j).ofLp x else 0 :=
      fun x ↦ by split_ifs <;> ring
    simp_rw [h1, ← Finset.sum_filter]
    have hfilt : Finset.univ.filter (fun x ↦ x ∈ orbitSet L N R o) = orbitSet L N R o := by
      ext x; simp
    rw [hfilt]
    have hconst : ∀ x ∈ orbitSet L N R o, (bTuple L N R j).ofLp x = (bTuple L N R j).ofLp x₀ :=
      fun x hx ↦ bTuple_const_on_orbit hL hrL hrN hR o j hx hx₀
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul]
  change (1 / √((orbitSet L N R o).card : ℝ)) * _ = _; rw [hsum]
  have hpos : (0 : ℝ) < ((orbitSet L N R o).card : ℝ) := by
    rw [orbitSet_card_eq hL hrL hrN hR]
    exact_mod_cast swLOrbitCardNat_pos hL hrL hrN o
  have hsp : (0 : ℝ) < √((orbitSet L N R o).card : ℝ) := Real.sqrt_pos.2 hpos; field_simp [hsp.ne']
  rw [Real.sq_sqrt hpos.le]
theorem bTuple_eq_sum_orbitUnitVec {L N r : ℕ} [NeZero L] [NeZero N]
    (hL : 2 ≤ L) (hrL : L ≤ r) (hrN : r + L ≤ N) {R : Finset (Fin N)} (hR : R.card = r)
    (j : Fin (2 * L)) :
    bTuple L N R j = ∑ o : Fin (2 * L), overlapTupleMat L N R o j • orbitUnitVec L N R o := by
  ext x
  have hsum_ofLp : ∀ (s : Finset (Fin (2 * L)))
      (F : Fin (2 * L) → EuclideanSpace ℝ (Fin L → Fin N)),
      (∑ o ∈ s, F o).ofLp x = ∑ o ∈ s, (F o).ofLp x := fun s F ↦ by
    induction s using Finset.induction_on with
    | empty => rfl
    | insert a s ha ih => simp [Finset.sum_insert ha, ih]
  rw [hsum_ofLp]
  by_cases hx : Function.Injective x
  · set o₀ := orbitIdxOf L R x
    have hx₀ : x ∈ orbitSet L N R o₀ := Finset.mem_filter.2 ⟨Finset.mem_univ _, hx, rfl⟩
    rw [Finset.sum_eq_single o₀]
    · rw [overlapTupleMat_eq_on_orbit hL hrL hrN hR o₀ j hx₀]; unfold orbitUnitVec
      simp only [PiLp.smul_apply, smul_eq_mul]
      change (bTuple L N R j).ofLp x = (√((orbitSet L N R o₀).card : ℝ) * (bTuple L N R j).ofLp x) *
          ((1 / √((orbitSet L N R o₀).card : ℝ)) *
            (if x ∈ orbitSet L N R o₀ then 1 else 0))
      simp only [hx₀, ↓reduceIte]
      have hpos : (0 : ℝ) < √((orbitSet L N R o₀).card : ℝ) := by
        rw [orbitSet_card_eq hL hrL hrN hR]
        exact Real.sqrt_pos.2 (by exact_mod_cast swLOrbitCardNat_pos hL hrL hrN o₀)
      field_simp [hpos.ne']
    · intro o _ hne
      have hno : x ∉ orbitSet L N R o := Finset.disjoint_left.1 (orbitSet_disjoint R hne.symm) hx₀
      unfold orbitUnitVec; simp only [PiLp.smul_apply, smul_eq_mul]
      change _ * (_ * (if x ∈ orbitSet L N R o then 1 else 0)) = 0
      simp [hno]
    · intro habs; exact False.elim (habs (Finset.mem_univ o₀))
  · rw [bTuple_of_not_injective R j hx]; symm
    refine Finset.sum_eq_zero fun o _ ↦ ?_
    have hno : x ∉ orbitSet L N R o := fun hm ↦ hx (Finset.mem_filter.1 hm).2.1
    unfold orbitUnitVec; simp only [PiLp.smul_apply, smul_eq_mul]
    change _ * (_ * (if x ∈ orbitSet L N R o then 1 else 0)) = 0
    simp [hno]
theorem overlapTupleMat_col_orth {L N r : ℕ} [NeZero L] [NeZero N]
    (hL : 2 ≤ L) (hrL : L ≤ r) (hrN : r + L ≤ N) {R : Finset (Fin N)} (hR : R.card = r)
    (i j : Fin (2 * L)) :
    (∑ o : Fin (2 * L), overlapTupleMat L N R o i * overlapTupleMat L N R o j) =
      if i = j then 1 else 0 := by
  rw [← inner_bTuple hL hrL hrN hR i j]
  conv_rhs =>
    rw [bTuple_eq_sum_orbitUnitVec hL hrL hrN hR i, bTuple_eq_sum_orbitUnitVec hL hrL hrN hR j]
  rw [sum_inner]
  refine Finset.sum_congr rfl fun o _ ↦ ?_
  rw [inner_sum]; rw [Finset.sum_eq_single o]
  · rw [inner_smul_left, inner_smul_right, RCLike.conj_to_real,
      inner_orbitUnitVec hL hrL hrN hR o o]
    simp
  · intro o₂ _ hne
    rw [inner_smul_left, inner_smul_right, RCLike.conj_to_real,
      inner_orbitUnitVec hL hrL hrN hR o o₂]
    simp [hne.symm]
  · intro habs; exact False.elim (habs (Finset.mem_univ o))
theorem overlapTupleMat_row_orth {L N r : ℕ} [NeZero L] [NeZero N]
    (hL : 2 ≤ L) (hrL : L ≤ r) (hrN : r + L ≤ N) {R : Finset (Fin N)} (hR : R.card = r)
    (o j : Fin (2 * L)) :
    (∑ k : Fin (2 * L), overlapTupleMat L N R o k * overlapTupleMat L N R j k) =
      if o = j then 1 else 0 := by
  set M := overlapTupleMat L N R
  let F : (Fin (2 * L) → ℝ) →ₗ[ℝ] (Fin (2 * L) → ℝ) :=
    { toFun := fun v a ↦ ∑ k : Fin (2 * L), M a k * v k
      map_add' := fun v w ↦ funext fun a ↦ by simp [mul_add, Finset.sum_add_distrib]
      map_smul' := fun c v ↦ funext fun a ↦ by simp [mul_left_comm, Finset.mul_sum] }
  let G : (Fin (2 * L) → ℝ) →ₗ[ℝ] (Fin (2 * L) → ℝ) :=
    { toFun := fun w k ↦ ∑ a : Fin (2 * L), M a k * w a
      map_add' := fun v w ↦ funext fun k ↦ by simp [mul_add, Finset.sum_add_distrib]
      map_smul' := fun c v ↦ funext fun k ↦ by simp [mul_left_comm, Finset.mul_sum] }
  have hGF : ∀ v : Fin (2 * L) → ℝ, G (F v) = v := by
    intro v
    ext k
    change (∑ a : Fin (2 * L), M a k * ∑ l : Fin (2 * L), M a l * v l) = v k
    simp_rw [Finset.mul_sum]; rw [Finset.sum_comm]
    have hterm : ∀ l : Fin (2 * L), (∑ a : Fin (2 * L), M a k * (M a l * v l)) =
          (∑ a : Fin (2 * L), M a k * M a l) * v l := fun l ↦ by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun a _ ↦ by ring
    have hcol : ∀ l : Fin (2 * L),
        (∑ a : Fin (2 * L), M a k * M a l) = if k = l then 1 else 0 :=
      overlapTupleMat_col_orth hL hrL hrN hR k
    simp_rw [hterm, hcol]; simp [ite_mul]
  have hinj : Function.Injective F := Function.LeftInverse.injective hGF
  have hsurj : Function.Surjective F := LinearMap.injective_iff_surjective.1 hinj
  let w₀ : Fin (2 * L) → ℝ := fun a ↦ if a = j then 1 else 0
  rcases hsurj w₀ with ⟨v₀, hv₀⟩
  have hFG : F (G w₀) = w₀ := by rw [← hv₀, hGF v₀]
  have hFG_o := congrFun hFG o
  have hGw₀ : ∀ k : Fin (2 * L), G w₀ k = M j k := by
    intro k
    change (∑ a : Fin (2 * L), M a k * (if a = j then 1 else 0)) = M j k
    simp
  change (∑ k : Fin (2 * L), M o k * M j k) = if o = j then 1 else 0
  simp_rw [← hGw₀]; exact hFG_o
theorem overlapTupleMat_diag_eq {L N r : ℕ} [NeZero L] [NeZero N]
    (hL : 2 ≤ L) (hrL : L ≤ r) (hrN : r + L ≤ N) {R : Finset (Fin N)} (hR : R.card = r)
    (j : Fin (2 * L)) :
    overlapTupleMat L N R j j = swLDiagOverlap L N r j := by
  have hcard : (orbitSet L N R j).card = swLOrbitCardNat L N r j := orbitSet_card_eq hL hrL hrN hR j
  have hne : (orbitSet L N R j).Nonempty :=
    Finset.card_pos.1 (hcard ▸ swLOrbitCardNat_pos hL hrL hrN j)
  rcases hne with ⟨x₀, hx₀⟩
  rw [overlapTupleMat_eq_on_orbit hL hrL hrN hR j j hx₀, hcard]
  rcases mem_orbitSet_iff.1 hx₀ with ⟨hinj, _, hmod⟩
  unfold swLDiagOverlap; dsimp only
  by_cases hj0 : j.1 = 0
  · simp only [hj0, ↓reduceIte]
    have hj_eq : j = ⟨0, by omega⟩ := Fin.ext hj0
    have hb0 : (bTuple L N R j).ofLp x₀ = 1 / √((L.factorial * N.choose L : ℕ) : ℝ) := by
      have hbt : bTuple L N R j = b0TupleVec L N := by
        rw [hj_eq, bTuple_zero L N R (by omega)]
      rw [hbt]; unfold b0TupleVec; simp only [PiLp.smul_apply, smul_eq_mul]
      change _ * (if Function.Injective x₀ then 1 else 0) = _
      simp [hinj]
    rw [hb0, Real.sqrt_div (Nat.cast_nonneg _)]; ring
  · simp only [hj0, ↓reduceIte]
    by_cases hjmod : j.1 % 2 = 1
    · simp only [hjmod, ↓reduceIte]; set m := (j.1 + 1) / 2
      have hm1 : 1 ≤ m := by omega
      have hmL : m ≤ L := by omega
      have hj_eq : j = ⟨2 * m - 1, by omega⟩ := Fin.ext (by dsimp [m]; omega)
      have hb_odd : (bTuple L N R j).ofLp x₀ = swLRawLiftAOnOrbit L N r m 1 (m - 1) /
            √((swLCaaNat L N m * swLQNormSqNat N r m : ℕ) : ℝ) := by
        have hbt : bTuple L N R j =
            (1 / √(swLCaaNat L N m : ℝ)) • rawLiftA (L := L) m (qVec R m) := by
          rw [hj_eq, bTuple_odd L N R hm1 hmL]
        rw [hbt]; unfold qVec; rw [hR]
        have h1 := congrFun (congrArg WithLp.ofLp
          ((rawLiftALin L N m).map_smul (1 / √(swLQNormSqNat N r m : ℝ)) (qVecRaw R m))) x₀
        simp only [PiLp.smul_apply, smul_eq_mul, rawLiftALin_apply] at h1 ⊢
        change 1 / √(swLCaaNat L N m : ℝ) *
            (rawLiftA (L := L) m ((1 / √(swLQNormSqNat N r m : ℝ)) • qVecRaw R m)).ofLp x₀ = _
        rw [h1, rawLiftA_qVecRaw_on_orbit hm1 hmL hR hx₀]
        have hdiv : j.1 / 2 = m - 1 := by omega
        rw [hjmod, hdiv, Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg _)]; ring
      rw [hb_odd]; ring
    · simp only [hjmod, ↓reduceIte]; set w := j.1 / 2
      have hw1 : 1 ≤ w := by omega
      have hwL : w < L := by omega
      have hj_mod0 : j.1 % 2 = 0 := by omega
      have hx0_not : x₀ 0 ∉ R := by have hm := hmod.trans hj_mod0; intro h0R; simp [h0R] at hm
      have hp := bTuple_plane_notMem hL hrL hrN hR ⟨w, hwL⟩ hx0_not; dsimp only at hp
      have hj_eq : j = ⟨2 * w, by omega⟩ := Fin.ext (by dsimp [w]; omega)
      have hbt_j : (bTuple L N R j).ofLp x₀ =
          (bTuple L N R ⟨2 * w, by omega⟩).ofLp x₀ :=
        congrArg (fun idx ↦ (bTuple L N R idx).ofLp x₀) hj_eq
      have hposrw : (0 : ℝ) < √((r - w : ℕ) : ℝ) :=
        Real.sqrt_pos.2 (by exact_mod_cast (by omega : 0 < r - w))
      have hb_even : (bTuple L N R j).ofLp x₀ = -(√((N - r - w : ℕ) : ℝ) / √((r - w : ℕ) : ℝ)) *
            (bTuple L N R ⟨2 * w + 1, by omega⟩).ofLp x₀ := by
        rw [hbt_j]; field_simp [hposrw.ne']; linarith
      have hb_next : (bTuple L N R ⟨2 * w + 1, by omega⟩).ofLp x₀ =
          swLRawLiftAOnOrbit L N r (w + 1) 0 w /
            √((swLCaaNat L N (w + 1) * swLQNormSqNat N r (w + 1) : ℕ) : ℝ) := by
        have hw_odd : (⟨2 * w + 1, by omega⟩ : Fin (2 * L)) = ⟨2 * (w + 1) - 1, by omega⟩ :=
          Fin.ext (by simp; omega)
        rw [hw_odd, bTuple_odd L N R (by omega) (by omega)]
        unfold qVec; rw [hR]
        have h1 := congrFun (congrArg WithLp.ofLp ((rawLiftALin L N (w + 1)).map_smul
            (1 / √(swLQNormSqNat N r (w + 1) : ℝ)) (qVecRaw R (w + 1)))) x₀
        simp only [PiLp.smul_apply, smul_eq_mul, rawLiftALin_apply] at h1 ⊢
        change 1 / √(swLCaaNat L N (w + 1) : ℝ) * (rawLiftA (L := L) (w + 1)
              ((1 / √(swLQNormSqNat N r (w + 1) : ℝ)) • qVecRaw R (w + 1))).ofLp x₀ = _
        rw [h1, rawLiftA_qVecRaw_on_orbit (by omega) (by omega) hR hx₀, hj_mod0,
          Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg _)]
        ring
      rw [hb_even, hb_next, Real.sqrt_div (Nat.cast_nonneg _)]; ring
/-! ## Self-Contained Cayley & Fin-Pair Partition Helpers -/
theorem cayley_cos_sq_add_sin_sq {num : ℤ} {den : ℕ} (hd : 0 < den) :
    SchurWeylLCert.swLCayleyCos num den ^ 2 +
      SchurWeylLCert.swLCayleySin num den ^ 2 = 1 := by
  unfold SchurWeylLCert.swLCayleyCos SchurWeylLCert.swLCayleySin
  have hdr : (0 : ℝ) < (den : ℝ) := by exact_mod_cast hd
  have hpos : (0 : ℝ) < (den : ℝ) ^ 2 + (num : ℝ) ^ 2 :=
    add_pos_of_pos_of_nonneg (sq_pos_of_pos hdr) (sq_nonneg _)
  field_simp [hpos.ne']; ring
theorem sum_range_two_mul_add {E : Type*} [AddCommMonoid E] :
    ∀ (L : ℕ) (g : ℕ → E),
      ∑ j ∈ Finset.range (2 * L), g j =
        ∑ w ∈ Finset.range L, (g (2 * w) + g (2 * w + 1))
  | 0, _ => by simp
  | L + 1, g => by
      have h2 : 2 * (L + 1) = 2 * L + 1 + 1 := by omega
      rw [h2, Finset.sum_range_succ, Finset.sum_range_succ, sum_range_two_mul_add L g,
        Finset.sum_range_succ, add_assoc]
theorem sum_fin_two_mul_add {L : ℕ} {E : Type*} [AddCommMonoid E] (f : Fin (2 * L) → E) :
    ∑ j : Fin (2 * L), f j =
      ∑ w : Fin L, (f ⟨2 * w.1, by omega⟩ + f ⟨2 * w.1 + 1, by omega⟩) := by
  set g : ℕ → E := fun i ↦ if hi : i < 2 * L then f ⟨i, hi⟩ else 0
  have hl : ∑ j : Fin (2 * L), f j = ∑ j ∈ Finset.range (2 * L), g j := by
    rw [← Fin.sum_univ_eq_sum_range g (2 * L)]
    exact Finset.sum_congr rfl fun j _ ↦ by simp [g, j.2]
  have hr : ∑ w : Fin L, (f ⟨2 * w.1, by omega⟩ + f ⟨2 * w.1 + 1, by omega⟩) =
      ∑ w ∈ Finset.range L, (g (2 * w) + g (2 * w + 1)) := by
    rw [← Fin.sum_univ_eq_sum_range (fun w ↦ g (2 * w) + g (2 * w + 1)) L]
    refine Finset.sum_congr rfl fun w _ ↦ ?_
    have h0 : 2 * w.1 < 2 * L := by omega
    have h1 : 2 * w.1 + 1 < 2 * L := by omega
    simp [g, h0, h1]
  rw [hl, hr, sum_range_two_mul_add]
theorem sum_range_interior_pairs_add {L : ℕ} (hL : 2 ≤ L) {E : Type*} [AddCommMonoid E]
    (g : ℕ → E) :
    ∑ j ∈ Finset.range (2 * L), g j =
      g 0 + (∑ w0 ∈ Finset.range (L - 1), (g (2 * w0 + 1) + g (2 * w0 + 2))) +
        g (2 * L - 1) := by
  induction L, hL using Nat.le_induction with
  | base =>
      rw [show 2 * 2 = 4 from rfl, show 2 - 1 = 1 from rfl]; simp [Finset.sum_range_succ, add_assoc]
  | succ m hm ih =>
      have h2 : 2 * (m + 1) = 2 * m + 1 + 1 := by omega
      conv_lhs => rw [h2, Finset.sum_range_succ, Finset.sum_range_succ, ih]
      conv_rhs => rw [show m + 1 - 1 = (m - 1) + 1 by omega, Finset.sum_range_succ]
      have h1 : g (2 * (m - 1) + 1) = g (2 * m - 1) := congrArg g (by omega)
      have h2' : g (2 * (m - 1) + 2) = g (2 * m) := congrArg g (by omega)
      have h3 : g (2 * m + 1) = g (2 * (m + 1) - 1) := congrArg g (by omega)
      rw [h1, h2', h3]; simp only [add_assoc]
theorem sum_fin_interior_pairs_add {L : ℕ} (hL : 2 ≤ L) {E : Type*} [AddCommMonoid E]
    (f : Fin (2 * L) → E) :
    ∑ j : Fin (2 * L), f j =
      f ⟨0, by omega⟩ +
        (∑ w0 : Fin (L - 1), (f ⟨2 * w0.1 + 1, by omega⟩ + f ⟨2 * w0.1 + 2, by omega⟩)) +
        f ⟨2 * L - 1, by omega⟩ := by
  set g : ℕ → E := fun i ↦ if hi : i < 2 * L then f ⟨i, hi⟩ else 0
  have hl : ∑ j : Fin (2 * L), f j = ∑ j ∈ Finset.range (2 * L), g j := by
    rw [← Fin.sum_univ_eq_sum_range g (2 * L)]
    exact Finset.sum_congr rfl fun j _ ↦ by simp [g, j.2]
  have h0 : g 0 = f ⟨0, by omega⟩ := by
    have hlt : 0 < 2 * L := by omega
    simp [g, hlt]
  have hlast : g (2 * L - 1) = f ⟨2 * L - 1, by omega⟩ := by
    have hlt : 2 * L - 1 < 2 * L := by omega
    simp [g, hlt]
  have hmid : ∑ w0 ∈ Finset.range (L - 1), (g (2 * w0 + 1) + g (2 * w0 + 2)) =
      ∑ w0 : Fin (L - 1), (f ⟨2 * w0.1 + 1, by omega⟩ + f ⟨2 * w0.1 + 2, by omega⟩) := by
    rw [← Fin.sum_univ_eq_sum_range (fun w0 ↦ g (2 * w0 + 1) + g (2 * w0 + 2)) (L - 1)]
    refine Finset.sum_congr rfl fun w0 _ ↦ ?_
    have h1 : 2 * w0.1 + 1 < 2 * L := by omega
    have h2 : 2 * w0.1 + 2 < 2 * L := by omega
    simp [g, h1, h2]
  rw [hl, sum_range_interior_pairs_add hL g, h0, hmid, hlast]
/-! ## Subspace Orthogonality & Address-Register Transport -/
theorem inner_b0_liftMinus {L N m : ℕ} [NeZero L] [NeZero N]
    (hm1 : 1 ≤ m) (hmL : m ≤ L) (hN : 2 * L ≤ N) (q : harmonicSubspace N m) :
    ⟪liftMinusTupleLI L N m hm1 hmL hN q, b0TupleVec L N⟫ = 0 := by
  rw [real_inner_comm]
  change ⟪b0TupleVec L N, (1 / √(swLCaaNat L N m : ℝ)) • rawLiftA (L := L) m q.1⟫ = 0
  rw [inner_smul_right, (inner_b0TupleVec_rawLift (L := L) hm1 q.2).1, mul_zero]
theorem inner_b0_liftPlus {L N w : ℕ} [NeZero L] [NeZero N]
    (hw1 : 1 ≤ w) (hwL : w + 1 ≤ L) (hN : 2 * L ≤ N) (q : harmonicSubspace N w) :
    ⟪liftPlusTupleLI L N w hw1 hwL hN q, b0TupleVec L N⟫ = 0 := by
  rw [real_inner_comm]
  change ⟪b0TupleVec L N, (1 / √(cBBNat L N w : ℝ)) • rawLiftB (L := L) w q.1⟫ = 0
  rw [inner_smul_right]; unfold rawLiftB
  rcases inner_b0TupleVec_rawLift (L := L) hw1 q.2 with ⟨h1, h2⟩
  rw [inner_add_right, inner_smul_right, inner_smul_right, h1, h2]; ring
theorem inner_liftMinus_ne {L N m₁ m₂ : ℕ} [NeZero L] [NeZero N]
    (hm1 : 1 ≤ m₁) (hm1L : m₁ ≤ L) (hm2 : 1 ≤ m₂) (hm2L : m₂ ≤ L) (hN : 2 * L ≤ N)
    (hne : m₁ ≠ m₂) (q₁ : harmonicSubspace N m₁) (q₂ : harmonicSubspace N m₂) :
    ⟪liftMinusTupleLI L N m₁ hm1 hm1L hN q₁, liftMinusTupleLI L N m₂ hm2 hm2L hN q₂⟫ = 0 := by
  rcases Nat.lt_trichotomy m₁ m₂ with hlt | heq | hgt
  · change ⟪(1 / √(swLCaaNat L N m₁ : ℝ)) • rawLiftA (L := L) m₁ q₁.1,
        (1 / √(swLCaaNat L N m₂ : ℝ)) • rawLiftA (L := L) m₂ q₂.1⟫ = 0
    rw [inner_smul_left, inner_smul_right, (inner_rawLiftA_lt (L := L) hm1 hlt q₂.2).1]; ring
  · exact False.elim (hne heq)
  · rw [real_inner_comm]
    change ⟪(1 / √(swLCaaNat L N m₂ : ℝ)) • rawLiftA (L := L) m₂ q₂.1,
        (1 / √(swLCaaNat L N m₁ : ℝ)) • rawLiftA (L := L) m₁ q₁.1⟫ = 0
    rw [inner_smul_left, inner_smul_right, (inner_rawLiftA_lt (L := L) hm2 hgt q₁.2).1]; ring
theorem inner_liftMinus_liftPlus {L N m w : ℕ} [NeZero L] [NeZero N]
    (hm1 : 1 ≤ m) (hmL : m ≤ L) (hw1 : 1 ≤ w) (hwL : w + 1 ≤ L) (hN : 2 * L ≤ N)
    (qm : harmonicSubspace N m) (qw : harmonicSubspace N w) :
    ⟪liftMinusTupleLI L N m hm1 hmL hN qm, liftPlusTupleLI L N w hw1 hwL hN qw⟫ = 0 := by
  rcases Nat.lt_trichotomy m w with hlt | rfl | hgt
  · change ⟪(1 / √(swLCaaNat L N m : ℝ)) • rawLiftA (L := L) m qm.1,
        (1 / √(cBBNat L N w : ℝ)) • rawLiftB (L := L) w qw.1⟫ = 0
    rcases inner_rawLiftA_lt (L := L) hm1 hlt (f := qm.1) qw.2 with ⟨hcAA, _, hcAT, _⟩
    rw [inner_smul_left, inner_smul_right]; unfold rawLiftB
    rw [inner_add_right, inner_smul_right, inner_smul_right, hcAA, hcAT]; ring
  · change ⟪(1 / √(swLCaaNat L N m : ℝ)) • rawLiftA (L := L) m qm.1,
        (1 / √(cBBNat L N m : ℝ)) • rawLiftB (L := L) m qw.1⟫ = 0
    rw [inner_smul_left, inner_smul_right, inner_rawLiftA_rawLiftB hm1 hwL hN qm.2 qw.2]; ring
  · rw [real_inner_comm]
    change ⟪(1 / √(cBBNat L N w : ℝ)) • rawLiftB (L := L) w qw.1,
        (1 / √(swLCaaNat L N m : ℝ)) • rawLiftA (L := L) m qm.1⟫ = 0
    rcases inner_rawLiftA_lt (L := L) hw1 hgt (f := qw.1) qm.2 with ⟨hcAA, hcTA, _, _⟩
    rw [inner_smul_left, inner_smul_right]; unfold rawLiftB
    rw [inner_add_left, inner_smul_left, inner_smul_left, hcAA, hcTA]; ring
theorem inner_liftPlus_ne {L N w₁ w₂ : ℕ} [NeZero L] [NeZero N]
    (hw1 : 1 ≤ w₁) (hw1L : w₁ + 1 ≤ L) (hw2 : 1 ≤ w₂) (hw2L : w₂ + 1 ≤ L) (hN : 2 * L ≤ N)
    (hne : w₁ ≠ w₂) (q₁ : harmonicSubspace N w₁) (q₂ : harmonicSubspace N w₂) :
    ⟪liftPlusTupleLI L N w₁ hw1 hw1L hN q₁, liftPlusTupleLI L N w₂ hw2 hw2L hN q₂⟫ = 0 := by
  suffices hlt_lem : ∀ (a b : ℕ) (ha1 : 1 ≤ a) (haL : a + 1 ≤ L)
      (hb1 : 1 ≤ b) (hbL : b + 1 ≤ L), a < b →
      ∀ (qa : harmonicSubspace N a) (qb : harmonicSubspace N b),
      ⟪liftPlusTupleLI L N a ha1 haL hN qa, liftPlusTupleLI L N b hb1 hbL hN qb⟫ = 0 by
    rcases Nat.lt_trichotomy w₁ w₂ with hlt | heq | hgt
    · exact hlt_lem w₁ w₂ hw1 hw1L hw2 hw2L hlt q₁ q₂
    · exact False.elim (hne heq)
    · rw [real_inner_comm]; exact hlt_lem w₂ w₁ hw2 hw2L hw1 hw1L hgt q₂ q₁
  intro a b ha1 haL _ _ hab qa qb
  change ⟪(1 / √(cBBNat L N a : ℝ)) • rawLiftB (L := L) a qa.1,
      (1 / √(cBBNat L N b : ℝ)) • rawLiftB (L := L) b qb.1⟫ = 0
  rcases inner_rawLiftA_lt (L := L) ha1 hab (f := qa.1) qb.2 with ⟨hcAA, hcTA, hcAT, hcTT⟩
  rw [inner_smul_left, inner_smul_right]; unfold rawLiftB
  rw [inner_add_left, inner_smul_left, inner_smul_left,
    inner_add_right, inner_smul_right, inner_smul_right,
    inner_add_right, inner_smul_right, inner_smul_right, hcAA, hcTA, hcAT, hcTT]
  ring
/-- Linear isometry equivalence between `Fin L → Fin (2 ^ n)` and `Fin (2 ^ (L * n))`. -/
noncomputable def addrEuclidLIE (L n : ℕ) :
    EuclideanSpace ℝ (Fin L → Fin (2 ^ n)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (2 ^ (L * n))) where
  toLinearEquiv :=
    { toFun := fun v ↦ WithLp.toLp 2 (fun a ↦ v.ofLp (addrEquiv L n a))
      invFun := fun u ↦ WithLp.toLp 2 (fun x ↦ u.ofLp ((addrEquiv L n).symm x))
      left_inv := fun v ↦ by
        ext x; rw [WithLp.ofLp_toLp]; exact congrArg v.ofLp ((addrEquiv L n).apply_symm_apply x)
      right_inv := fun u ↦ by
        ext a; rw [WithLp.ofLp_toLp]; exact congrArg u.ofLp ((addrEquiv L n).symm_apply_apply a)
      map_add' := fun v w ↦ by ext a; simp
      map_smul' := fun c v ↦ by ext a; simp }
  norm_map' v := by
    rw [norm_eq_sqrt_real_inner, norm_eq_sqrt_real_inner]
    congr 1
    simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
    exact (addrEquiv L n).sum_comp (fun x ↦ v.ofLp x * v.ofLp x)
theorem matOfEnd_mulVec_ofLp {D : ℕ}
    (T : EuclideanSpace ℝ (Fin D) →ₗ[ℝ] EuclideanSpace ℝ (Fin D))
    (v : EuclideanSpace ℝ (Fin D)) :
    matOfEnd T *ᵥ (fun a ↦ v.ofLp a) = fun a ↦ (T v).ofLp a := by
  simpa using matOfEnd_mulVec T (fun a ↦ v.ofLp a)
/-- Transported isometric embedding `ι_{-, m}` into `EuclideanSpace ℝ (Fin (2 ^ (L * n)))`. -/
noncomputable def liftMinusAddrLI (L n m : ℕ) [NeZero L]
    (hm1 : 1 ≤ m) (hmL : m ≤ L) (hn : 2 * L ≤ 2 ^ n) :
    harmonicSubspace (2 ^ n) m →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (2 ^ (L * n))) :=
  letI : NeZero (2 ^ n) := ⟨Nat.pos_iff_ne_zero.1 (Nat.two_pow_pos n)⟩
  (addrEuclidLIE L n).toLinearIsometry.comp (liftMinusTupleLI L (2 ^ n) m hm1 hmL hn)
/-- Transported isometric embedding `ι_{+, w}` into `EuclideanSpace ℝ (Fin (2 ^ (L * n)))`. -/
noncomputable def liftPlusAddrLI (L n w : ℕ) [NeZero L]
    (hw1 : 1 ≤ w) (hwL : w + 1 ≤ L) (hn : 2 * L ≤ 2 ^ n) :
    harmonicSubspace (2 ^ n) w →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (2 ^ (L * n))) :=
  letI : NeZero (2 ^ n) := ⟨Nat.pos_iff_ne_zero.1 (Nat.two_pow_pos n)⟩
  (addrEuclidLIE L n).toLinearIsometry.comp (liftPlusTupleLI L (2 ^ n) w hw1 hwL hn)
/-- Transported `2L`-basis vector in `EuclideanSpace ℝ (Fin (2 ^ (L * n)))`. -/
noncomputable def bAddrEuclid (L n : ℕ) [NeZero L] (R : Finset (Fin (2 ^ n)))
    (j : Fin (2 * L)) : EuclideanSpace ℝ (Fin (2 ^ (L * n))) :=
  addrEuclidLIE L n (bTuple L (2 ^ n) R j)
/-- Raw function form of `bAddrEuclid` on `Fin (2 ^ (L * n))`. -/
noncomputable def bAddrVec (L n : ℕ) (R : Finset (Fin (2 ^ n))) (j : Fin (2 * L)) :
    Fin (2 ^ (L * n)) → ℝ :=
  if hL0 : L = 0 then 0
  else
    letI : NeZero L := ⟨hL0⟩
    fun a ↦ (bAddrEuclid L n R j).ofLp a
theorem bAddrVec_eq_of_neZero (L n : ℕ) [NeZero L] (R : Finset (Fin (2 ^ n)))
    (j : Fin (2 * L)) :
    bAddrVec L n R j = fun a ↦ (bAddrEuclid L n R j).ofLp a := by
  have hL0 : L ≠ 0 := NeZero.ne L; simp [bAddrVec, hL0]
theorem bAddrEuclid_odd_eq_liftMinus {L n r m : ℕ} [NeZero L]
    (hm1 : 1 ≤ m) (hmL : m ≤ L) (hrL : L ≤ r) (hrN : r + L ≤ 2 ^ n)
    {R : Finset (Fin (2 ^ n))} (hR : R.card = r) :
    bAddrEuclid L n R ⟨2 * m - 1, by omega⟩ =
      liftMinusAddrLI L n m hm1 hmL (by omega)
        ⟨qVec R m, qVec_mem_harmonic hm1 (by omega) (by omega) hR⟩ := by
  unfold bAddrEuclid liftMinusAddrLI
  simp only [LinearIsometry.coe_comp, Function.comp_apply, LinearIsometryEquiv.coe_toLinearIsometry]
  congr 1; exact bTuple_odd L (2 ^ n) R hm1 hmL
theorem bAddrEuclid_even_eq_liftPlus {L n r w : ℕ} [NeZero L]
    (hw1 : 1 ≤ w) (hwL : w + 1 ≤ L) (hrL : L ≤ r) (hrN : r + L ≤ 2 ^ n)
    {R : Finset (Fin (2 ^ n))} (hR : R.card = r) :
    bAddrEuclid L n R ⟨2 * w, by omega⟩ =
      liftPlusAddrLI L n w hw1 hwL (by omega)
        ⟨qVec R w, qVec_mem_harmonic hw1 (by omega) (by omega) hR⟩ := by
  unfold bAddrEuclid liftPlusAddrLI
  simp only [LinearIsometry.coe_comp, Function.comp_apply, LinearIsometryEquiv.coe_toLinearIsometry]
  congr 1; exact bTuple_even L (2 ^ n) R hw1 hwL
theorem inner_liftMinusAddr_bAddrEuclid_of_ne {L n r m : ℕ} [NeZero L]
    (hm1 : 1 ≤ m) (hmL : m ≤ L) (hn : 2 * L ≤ 2 ^ n)
    (hrL : L ≤ r) (hrN : r + L ≤ 2 ^ n) {R : Finset (Fin (2 ^ n))} (hR : R.card = r)
    {j : Fin (2 * L)} (hj : j.1 ≠ 2 * m - 1) (q : harmonicSubspace (2 ^ n) m) :
    ⟪liftMinusAddrLI L n m hm1 hmL hn q, bAddrEuclid L n R j⟫ = 0 := by
  have : NeZero (2 ^ n) := ⟨Nat.pos_iff_ne_zero.1 (Nat.two_pow_pos n)⟩
  unfold liftMinusAddrLI bAddrEuclid
  simp only [LinearIsometry.coe_comp, Function.comp_apply,
    LinearIsometryEquiv.coe_toLinearIsometry, LinearIsometryEquiv.inner_map_map]
  by_cases hj0 : j.1 = 0
  · have hj_eq : j = ⟨0, by omega⟩ := Fin.ext hj0
    rw [hj_eq, bTuple_zero L (2 ^ n) R (by omega)]
    exact inner_b0_liftMinus hm1 hmL hn q
  · by_cases hjmod : j.1 % 2 = 1
    · set m' := (j.1 + 1) / 2
      have hm'1 : 1 ≤ m' := by omega
      have hm'L : m' ≤ L := by omega
      have hne : m ≠ m' := by omega
      have hj_eq : j = ⟨2 * m' - 1, by omega⟩ := Fin.ext (by dsimp [m']; omega)
      have hbt : bTuple L (2 ^ n) R j = liftMinusTupleLI L (2 ^ n) m' hm'1 hm'L hn
            ⟨qVec R m', qVec_mem_harmonic hm'1 (by omega) (by omega) hR⟩ :=
        (congrArg (bTuple L (2 ^ n) R) hj_eq).trans (bTuple_odd L (2 ^ n) R hm'1 hm'L)
      rw [hbt]; exact inner_liftMinus_ne hm1 hmL hm'1 hm'L hn hne q _
    · set w := j.1 / 2
      have hw1 : 1 ≤ w := by omega
      have hwL : w + 1 ≤ L := by omega
      have hj_eq : j = ⟨2 * w, by omega⟩ := Fin.ext (by dsimp [w]; omega)
      have hbt : bTuple L (2 ^ n) R j = liftPlusTupleLI L (2 ^ n) w hw1 hwL hn
            ⟨qVec R w, qVec_mem_harmonic hw1 (by omega) (by omega) hR⟩ :=
        (congrArg (bTuple L (2 ^ n) R) hj_eq).trans (bTuple_even L (2 ^ n) R hw1 hwL)
      rw [hbt]; exact inner_liftMinus_liftPlus hm1 hmL hw1 hwL hn q _
theorem inner_liftPlusAddr_bAddrEuclid_of_ne {L n r w : ℕ} [NeZero L]
    (hw1 : 1 ≤ w) (hwL : w + 1 ≤ L) (hn : 2 * L ≤ 2 ^ n)
    (hrL : L ≤ r) (hrN : r + L ≤ 2 ^ n) {R : Finset (Fin (2 ^ n))} (hR : R.card = r)
    {j : Fin (2 * L)} (hj : j.1 ≠ 2 * w) (q : harmonicSubspace (2 ^ n) w) :
    ⟪liftPlusAddrLI L n w hw1 hwL hn q, bAddrEuclid L n R j⟫ = 0 := by
  have : NeZero (2 ^ n) := ⟨Nat.pos_iff_ne_zero.1 (Nat.two_pow_pos n)⟩
  unfold liftPlusAddrLI bAddrEuclid
  simp only [LinearIsometry.coe_comp, Function.comp_apply,
    LinearIsometryEquiv.coe_toLinearIsometry, LinearIsometryEquiv.inner_map_map]
  by_cases hj0 : j.1 = 0
  · have hj_eq : j = ⟨0, by omega⟩ := Fin.ext hj0
    rw [hj_eq, bTuple_zero L (2 ^ n) R (by omega)]
    exact inner_b0_liftPlus hw1 hwL hn q
  · by_cases hjmod : j.1 % 2 = 1
    · set m := (j.1 + 1) / 2
      have hm1 : 1 ≤ m := by omega
      have hmL : m ≤ L := by omega
      have hj_eq : j = ⟨2 * m - 1, by omega⟩ := Fin.ext (by dsimp [m]; omega)
      have hbt : bTuple L (2 ^ n) R j = liftMinusTupleLI L (2 ^ n) m hm1 hmL hn
            ⟨qVec R m, qVec_mem_harmonic hm1 (by omega) (by omega) hR⟩ :=
        (congrArg (bTuple L (2 ^ n) R) hj_eq).trans (bTuple_odd L (2 ^ n) R hm1 hmL)
      rw [hbt, real_inner_comm]; exact inner_liftMinus_liftPlus hm1 hmL hw1 hwL hn _ q
    · set w' := j.1 / 2
      have hw'1 : 1 ≤ w' := by omega
      have hw'L : w' + 1 ≤ L := by omega
      have hne : w ≠ w' := by omega
      have hj_eq : j = ⟨2 * w', by omega⟩ := Fin.ext (by dsimp [w']; omega)
      have hbt : bTuple L (2 ^ n) R j = liftPlusTupleLI L (2 ^ n) w' hw'1 hw'L hn
            ⟨qVec R w', qVec_mem_harmonic hw'1 (by omega) (by omega) hR⟩ :=
        (congrArg (bTuple L (2 ^ n) R) hj_eq).trans (bTuple_even L (2 ^ n) R hw'1 hw'L)
      rw [hbt]; exact inner_liftPlus_ne hw1 hwL hw'1 hw'L hn hne q _
theorem projMinus_bAddrEuclid {L n r m : ℕ} [NeZero L]
    (hm1 : 1 ≤ m) (hmL : m ≤ L) (hn : 2 * L ≤ 2 ^ n)
    (hrL : L ≤ r) (hrN : r + L ≤ 2 ^ n) {R : Finset (Fin (2 ^ n))} (hR : R.card = r)
    (j : Fin (2 * L)) :
    orthProjEnd (LinearMap.range (liftMinusAddrLI L n m hm1 hmL hn).toLinearMap)
        (bAddrEuclid L n R j) =
      if j.1 = 2 * m - 1 then bAddrEuclid L n R j else 0 := by
  by_cases hj : j.1 = 2 * m - 1
  · simp only [hj, ↓reduceIte]
    have hj_eq : j = ⟨2 * m - 1, by omega⟩ := Fin.ext hj
    rw [hj_eq, bAddrEuclid_odd_eq_liftMinus hm1 hmL hrL hrN hR]; exact orthProjEnd_eq_self ⟨_, rfl⟩
  · simp only [hj, ↓reduceIte]
    refine orthProjEnd_eq_zero fun y ⟨q, hq⟩ ↦ ?_
    rw [← hq]; exact inner_liftMinusAddr_bAddrEuclid_of_ne hm1 hmL hn hrL hrN hR hj q
theorem projPlus_bAddrEuclid {L n r w : ℕ} [NeZero L]
    (hw1 : 1 ≤ w) (hwL : w + 1 ≤ L) (hn : 2 * L ≤ 2 ^ n)
    (hrL : L ≤ r) (hrN : r + L ≤ 2 ^ n) {R : Finset (Fin (2 ^ n))} (hR : R.card = r)
    (j : Fin (2 * L)) :
    orthProjEnd (LinearMap.range (liftPlusAddrLI L n w hw1 hwL hn).toLinearMap)
        (bAddrEuclid L n R j) =
      if j.1 = 2 * w then bAddrEuclid L n R j else 0 := by
  by_cases hj : j.1 = 2 * w
  · simp only [hj, ↓reduceIte]
    have hj_eq : j = ⟨2 * w, by omega⟩ := Fin.ext hj
    rw [hj_eq, bAddrEuclid_even_eq_liftPlus hw1 hwL hrL hrN hR]; exact orthProjEnd_eq_self ⟨_, rfl⟩
  · simp only [hj, ↓reduceIte]
    refine orthProjEnd_eq_zero fun y ⟨q, hq⟩ ↦ ?_
    rw [← hq]; exact inner_liftPlusAddr_bAddrEuclid_of_ne hw1 hwL hn hrL hrN hR hj q
theorem pieriIsom_bAddrEuclid {L n r w : ℕ} [NeZero L]
    (hw1 : 1 ≤ w) (hwL : w + 1 ≤ L) (hn : 2 * L ≤ 2 ^ n)
    (hrL : L ≤ r) (hrN : r + L ≤ 2 ^ n) {R : Finset (Fin (2 ^ n))} (hR : R.card = r)
    (j : Fin (2 * L)) :
    pieriIsomEnd (liftMinusAddrLI L n w hw1 (by omega) hn) (liftPlusAddrLI L n w hw1 hwL hn)
        (bAddrEuclid L n R j) =
      if j.1 = 2 * w - 1 then bAddrEuclid L n R ⟨2 * w, by omega⟩ else 0 := by
  by_cases hj : j.1 = 2 * w - 1
  · simp only [hj, ↓reduceIte]
    have hj_eq : j = ⟨2 * w - 1, by omega⟩ := Fin.ext hj
    rw [hj_eq, bAddrEuclid_odd_eq_liftMinus hw1 (by omega) hrL hrN hR, pieriIsomEnd_apply_ι₁,
      bAddrEuclid_even_eq_liftPlus hw1 hwL hrL hrN hR]
  · simp only [hj, ↓reduceIte]
    exact pieriIsomEnd_apply_orth _ _ fun q ↦
      inner_liftMinusAddr_bAddrEuclid_of_ne hw1 (by omega) hn hrL hrN hR hj q
theorem pieriIsomAdj_bAddrEuclid {L n r w : ℕ} [NeZero L]
    (hw1 : 1 ≤ w) (hwL : w + 1 ≤ L) (hn : 2 * L ≤ 2 ^ n)
    (hrL : L ≤ r) (hrN : r + L ≤ 2 ^ n) {R : Finset (Fin (2 ^ n))} (hR : R.card = r)
    (j : Fin (2 * L)) :
    LinearMap.adjoint
        (pieriIsomEnd (liftMinusAddrLI L n w hw1 (by omega) hn) (liftPlusAddrLI L n w hw1 hwL hn))
        (bAddrEuclid L n R j) =
      if j.1 = 2 * w then bAddrEuclid L n R ⟨2 * w - 1, by omega⟩ else 0 := by
  rw [pieriIsomEnd_adjoint]
  by_cases hj : j.1 = 2 * w
  · simp only [hj, ↓reduceIte]
    have hj_eq : j = ⟨2 * w, by omega⟩ := Fin.ext hj
    rw [hj_eq, bAddrEuclid_even_eq_liftPlus hw1 hwL hrL hrN hR, pieriIsomEnd_apply_ι₁,
      bAddrEuclid_odd_eq_liftMinus hw1 (by omega) hrL hrN hR]
  · simp only [hj, ↓reduceIte]
    exact pieriIsomEnd_apply_orth _ _ fun q ↦
      inner_liftPlusAddr_bAddrEuclid_of_ne hw1 hwL hn hrL hrN hR hj q
/-! ## Preparation, Diffuser, Pieri & Weak-Measurement Matrices -/
/-- Zero-oracle uniform distinct `L`-tuple vector on `Fin (2 ^ (L * n))`. -/
noncomputable def b0AddrVec (L n : ℕ) [NeZero L] : Fin (2 ^ (L * n)) → ℝ :=
  fun a ↦ (b0TupleVec L (2 ^ n)).ofLp (addrTuple L n a)
theorem b0AddrVec_zero {L n : ℕ} [NeZero L] (hL : 2 ≤ L) :
    b0AddrVec L n 0 = 0 := by
  unfold b0AddrVec b0TupleVec; rw [addrTuple_zero]; simp only [PiLp.smul_apply, smul_eq_mul]
  have hni : ¬ Function.Injective (fun _ : Fin L ↦ (0 : Fin (2 ^ n))) := by
    intro hinj
    have h01 : (0 : Fin L) = ⟨1, by omega⟩ := hinj rfl
    exact absurd (congrArg Fin.val h01) (by simp)
  change _ * (if Function.Injective (fun _ : Fin L ↦ (0 : Fin (2 ^ n))) then 1 else 0) = 0
  simp [hni]
theorem b0AddrVec_normSq {L n : ℕ} [NeZero L] (hn : 2 * L ≤ 2 ^ n) :
    ∑ a : Fin (2 ^ (L * n)), (b0AddrVec L n a) ^ 2 = 1 := by
  have hsum : ∑ a : Fin (2 ^ (L * n)), (b0AddrVec L n a) ^ 2 =
      ⟪b0TupleVec L (2 ^ n), b0TupleVec L (2 ^ n)⟫ := by
    unfold b0AddrVec; simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, sq]
    exact (addrEquiv L n).sum_comp (fun x ↦ (b0TupleVec L (2 ^ n)).ofLp x *
      (b0TupleVec L (2 ^ n)).ofLp x)
  rw [hsum]
  exact inner_b0TupleVec_self (by omega)
/-- Orthogonal projector onto `⊕_{m=1}^L V_{-, m}` on `EuclideanSpace ℝ (Fin (2 ^ (L *
  n)))`. -/
noncomputable def pMinusSumEnd (L n : ℕ) [NeZero L] (hn : 2 * L ≤ 2 ^ n) :
    EuclideanSpace ℝ (Fin (2 ^ (L * n))) →ₗ[ℝ] EuclideanSpace ℝ (Fin (2 ^ (L * n))) :=
  ∑ i : Fin L,
    orthProjEnd
      (LinearMap.range (liftMinusAddrLI L n (i.1 + 1) (by omega) (by omega) hn).toLinearMap)
theorem pMinusSumEnd_self_adjoint (L n : ℕ) [NeZero L] (hn : 2 * L ≤ 2 ^ n) :
    LinearMap.adjoint (pMinusSumEnd L n hn) = pMinusSumEnd L n hn := by
  unfold pMinusSumEnd; rw [map_sum]
  exact Finset.sum_congr rfl fun i _ ↦ orthProjEnd_self_adjoint _
theorem pMinusSumEnd_idem (L n : ℕ) [NeZero L] (hn : 2 * L ≤ 2 ^ n) :
    (pMinusSumEnd L n hn).comp (pMinusSumEnd L n hn) = pMinusSumEnd L n hn := by
  have : NeZero (2 ^ n) := ⟨Nat.pos_iff_ne_zero.1 (Nat.two_pow_pos n)⟩; unfold pMinusSumEnd
  apply LinearMap.ext; intro x; rw [LinearMap.comp_apply, LinearMap.sum_apply, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [map_sum, Finset.sum_eq_single i]
  · exact LinearMap.congr_fun (orthProjEnd_idem _) x
  · intro k _ hki
    set Ki := LinearMap.range (liftMinusAddrLI L n (i.1 + 1) (by omega) (by omega) hn).toLinearMap
    set Kk := LinearMap.range (liftMinusAddrLI L n (k.1 + 1) (by omega) (by omega) hn).toLinearMap
    rcases (Kk.orthogonalProjectionOnto x).2 with ⟨qk, hqk⟩
    have hpk : orthProjEnd Kk x = liftMinusAddrLI L n (k.1 + 1) (by omega) (by omega) hn qk :=
      hqk.symm
    rw [hpk]
    refine orthProjEnd_eq_zero fun y ⟨qi, hqi⟩ ↦ ?_
    rw [← hqi]; unfold liftMinusAddrLI
    simp only [LinearIsometry.coe_toLinearMap, LinearIsometry.coe_comp, Function.comp_apply,
      LinearIsometryEquiv.coe_toLinearIsometry, LinearIsometryEquiv.inner_map_map]
    exact inner_liftMinus_ne (by omega) (by omega) (by omega) (by omega) hn (by omega) qi qk
  · intro habs; exact False.elim (habs (Finset.mem_univ i))
/-- Diffuser real matrix `1 - 2 P_{V_-}` on `Fin (2 ^ (L * n))`. -/
noncomputable def diffAddrMat (L n : ℕ) [NeZero L] (hn : 2 * L ≤ 2 ^ n) :
    Matrix (Fin (2 ^ (L * n))) (Fin (2 ^ (L * n))) ℝ :=
  symProjReflMat (matOfEnd (LinearMap.id - pMinusSumEnd L n hn))
theorem diffAddrMat_orth (L n : ℕ) [NeZero L] (hn : 2 * L ≤ 2 ^ n) :
    (diffAddrMat L n hn)ᵀ * diffAddrMat L n hn = 1 := by
  apply symProjReflMat_orth
  · rw [ ← matOfEnd_adjoint, map_sub, LinearMap.adjoint_id, pMinusSumEnd_self_adjoint]
  · rw [ ← matOfEnd_comp]; congr 1
    ext x
    have hidem := LinearMap.congr_fun (pMinusSumEnd_idem L n hn) x
    simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply, map_sub] at hidem ⊢
    rw [hidem, sub_self, sub_zero]
theorem diffAddrMat_mulVec_bAddrVec {L n r : ℕ} [NeZero L]
    (hn : 2 * L ≤ 2 ^ n) (hrL : L ≤ r) (hrN : r + L ≤ 2 ^ n)
    {R : Finset (Fin (2 ^ n))} (hR : R.card = r) (j : Fin (2 * L)) :
    diffAddrMat L n hn *ᵥ bAddrVec L n R j =
      if j.1 % 2 = 1 then - bAddrVec L n R j else bAddrVec L n R j := by
  rw [bAddrVec_eq_of_neZero]
  have hp : pMinusSumEnd L n hn (bAddrEuclid L n R j) =
      if j.1 % 2 = 1 then bAddrEuclid L n R j else 0 := by
    unfold pMinusSumEnd; rw [LinearMap.sum_apply]
    by_cases hjodd : j.1 % 2 = 1
    · simp only [hjodd, ↓reduceIte]
      let i₀ : Fin L := ⟨j.1 / 2, by omega⟩
      rw [Finset.sum_eq_single i₀]
      · rw [projMinus_bAddrEuclid (by omega) (by omega) hn hrL hrN hR j]
        have heq : j.1 = 2 * (i₀.1 + 1) - 1 := by dsimp [i₀]; omega
        simp [heq]
      · intro i _ hne
        rw [projMinus_bAddrEuclid (by omega) (by omega) hn hrL hrN hR j]
        have hne' : j.1 ≠ 2 * (i.1 + 1) - 1 := by intro h; apply hne; ext; dsimp [i₀]; omega
        simp [hne']
      · intro habs; exact False.elim (habs (Finset.mem_univ i₀))
    · simp only [hjodd, ↓reduceIte]
      refine Finset.sum_eq_zero fun i _ ↦ ?_
      rw [projMinus_bAddrEuclid (by omega) (by omega) hn hrL hrN hR j]
      have hne : j.1 ≠ 2 * (i.1 + 1) - 1 := by omega
      simp [hne]
  unfold diffAddrMat symProjReflMat
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, matOfEnd_mulVec_ofLp]
  funext a
  simp only [LinearMap.sub_apply, LinearMap.id_apply, hp]
  by_cases hjodd : j.1 % 2 = 1
  · simp [hjodd]
  · simp only [hjodd, ↓reduceIte, sub_zero, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring
/-- Single Pieri `SO(2)` rotation matrix `W_{w0 + 1}(u_{w0})` on `Fin (2 ^ (L * n))`. -/
noncomputable def pieriRotMat (L n : ℕ) [NeZero L] (hn : 2 * L ≤ 2 ^ n)
    (p : SchurWeylLCert.SwLPulseRat L) (w0 : Fin (L - 1)) :
    Matrix (Fin (2 ^ (L * n))) (Fin (2 ^ (L * n))) ℝ :=
  let w := w0.1 + 1
  let ι₁ := liftMinusAddrLI L n w (by omega) (by omega) hn
  let ι₂ := liftPlusAddrLI L n w (by omega) (by omega) hn
  let P₁ := matOfEnd (orthProjEnd (LinearMap.range ι₁.toLinearMap))
  let P₂ := matOfEnd (orthProjEnd (LinearMap.range ι₂.toLinearMap))
  let K := matOfEnd (pieriIsomEnd ι₁ ι₂)
  partialIsomRotMat P₁ P₂ K
    (SchurWeylLCert.swLCayleyCos (p.uNum w0) p.uvDen)
    (SchurWeylLCert.swLCayleySin (p.uNum w0) p.uvDen)
theorem pieriRotMat_orth (L n : ℕ) [NeZero L] (hn : 2 * L ≤ 2 ^ n)
    (p : SchurWeylLCert.SwLPulseRat L) (hp : SchurWeylLCert.swLPulseValid p = true)
    (w0 : Fin (L - 1)) :
    (pieriRotMat L n hn p w0)ᵀ * pieriRotMat L n hn p w0 = 1 := by
  have : NeZero (2 ^ n) := ⟨Nat.pos_iff_ne_zero.1 (Nat.two_pow_pos n)⟩; set w := w0.1 + 1
  set ι₁ := liftMinusAddrLI L n w (by omega) (by omega) hn
  set ι₂ := liftPlusAddrLI L n w (by omega) (by omega) hn
  have horth : ∀ q₁ q₂ : harmonicSubspace (2 ^ n) w, ⟪ι₁ q₁, ι₂ q₂⟫ = 0 := by
    intro q₁ q₂; unfold ι₁ ι₂ liftMinusAddrLI liftPlusAddrLI
    simp only [LinearIsometry.coe_comp, Function.comp_apply,
      LinearIsometryEquiv.coe_toLinearIsometry, LinearIsometryEquiv.inner_map_map]
    exact inner_liftMinus_liftPlus (by omega) (by omega) (by omega) (by omega) hn q₁ q₂
  rcases pieriIsomEnd_props ι₁ ι₂ horth with ⟨hK1, hK2, hKP1, hP2K, h12⟩
  have hden : 0 < p.uvDen := by simpa [SchurWeylLCert.swLPulseValid] using hp
  apply partialIsomRotMat_orth
  · rw [← matOfEnd_adjoint, orthProjEnd_self_adjoint]
  · rw [← matOfEnd_adjoint, orthProjEnd_self_adjoint]
  · rw [← matOfEnd_adjoint, ← matOfEnd_comp, hK1]
  · rw [← matOfEnd_adjoint, ← matOfEnd_comp, hK2]
  · rw [← matOfEnd_comp, hKP1]
  · rw [← matOfEnd_comp, hP2K]
  · rw [← matOfEnd_comp, h12]; ext i j; simp [matOfEnd]
  · exact cayley_cos_sq_add_sin_sq hden
theorem pieriRotMat_mulVec_bAddrVec {L n r : ℕ} [NeZero L]
    (hn : 2 * L ≤ 2 ^ n) (hrL : L ≤ r) (hrN : r + L ≤ 2 ^ n)
    {R : Finset (Fin (2 ^ n))} (hR : R.card = r)
    (p : SchurWeylLCert.SwLPulseRat L) (w0 : Fin (L - 1)) (j : Fin (2 * L)) :
    pieriRotMat L n hn p w0 *ᵥ bAddrVec L n R j =
      if j.1 = 2 * w0.1 + 1 then
        SchurWeylLCert.swLCayleyCos (p.uNum w0) p.uvDen •
          bAddrVec L n R ⟨2 * w0.1 + 1, by omega⟩ +
        SchurWeylLCert.swLCayleySin (p.uNum w0) p.uvDen •
          bAddrVec L n R ⟨2 * w0.1 + 2, by omega⟩
      else if j.1 = 2 * w0.1 + 2 then
        (-SchurWeylLCert.swLCayleySin (p.uNum w0) p.uvDen) •
          bAddrVec L n R ⟨2 * w0.1 + 1, by omega⟩ +
        SchurWeylLCert.swLCayleyCos (p.uNum w0) p.uvDen •
          bAddrVec L n R ⟨2 * w0.1 + 2, by omega⟩
      else bAddrVec L n R j := by
  simp only [bAddrVec_eq_of_neZero]; set w := w0.1 + 1
  set ι₁ := liftMinusAddrLI L n w (by omega) (by omega) hn
  set ι₂ := liftPlusAddrLI L n w (by omega) (by omega) hn
  have hKt : (matOfEnd (pieriIsomEnd ι₁ ι₂))ᵀ = matOfEnd (LinearMap.adjoint (pieriIsomEnd ι₁ ι₂)) :=
    (matOfEnd_adjoint (pieriIsomEnd ι₁ ι₂)).symm
  unfold pieriRotMat partialIsomRotMat; dsimp only; rw [hKt]
  have hp1 := projMinus_bAddrEuclid (L := L) (n := n) (m := w)
    (by omega) (by omega) hn hrL hrN hR j
  have hp2 := projPlus_bAddrEuclid (L := L) (n := n) (w := w)
    (by omega) (by omega) hn hrL hrN hR j
  have hk1 := pieriIsom_bAddrEuclid (L := L) (n := n) (w := w)
    (by omega) (by omega) hn hrL hrN hR j
  have hk2 := pieriIsomAdj_bAddrEuclid (L := L) (n := n) (w := w)
    (by omega) (by omega) hn hrL hrN hR j
  have h2w1 : 2 * w - 1 = 2 * w0.1 + 1 := by dsimp [w]; omega
  have h2w2 : 2 * w = 2 * w0.1 + 2 := by dsimp [w]; omega
  have idx2 : (⟨2 * w, by omega⟩ : Fin (2 * L)) = ⟨2 * w0.1 + 2, by omega⟩ := Fin.ext h2w2
  have idx1 : (⟨2 * w - 1, by omega⟩ : Fin (2 * L)) = ⟨2 * w0.1 + 1, by omega⟩ := Fin.ext h2w1
  have hc1 : (j.1 = 2 * w - 1) ↔ (j.1 = 2 * w0.1 + 1) := by rw [h2w1]
  have hc2 : (j.1 = 2 * w) ↔ (j.1 = 2 * w0.1 + 2) := by rw [h2w2]
  simp only [Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    matOfEnd_mulVec_ofLp]
  rw [hp1, hp2, hk1, hk2, idx1, idx2]; simp only [hc1, hc2]
  by_cases h1 : j.1 = 2 * w0.1 + 1
  · have hj_eq : j = ⟨2 * w0.1 + 1, by omega⟩ := Fin.ext h1
    have h2 : j.1 ≠ 2 * w0.1 + 2 := by omega
    repeat rw [ite_eq_left h1]
    repeat rw [ite_eq_right h2]
    funext a
    rw [hj_eq]; simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, PiLp.zero_apply, smul_eq_mul]
    ring
  · by_cases h2 : j.1 = 2 * w0.1 + 2
    · have hj_eq : j = ⟨2 * w0.1 + 2, by omega⟩ := Fin.ext h2
      repeat rw [ite_eq_right h1]
      repeat rw [ite_eq_left h2]
      funext a
      rw [hj_eq]
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, neg_smul, Pi.neg_apply,
        PiLp.zero_apply, smul_eq_mul]
      ring
    · repeat rw [ite_eq_right h1]
      repeat rw [ite_eq_right h2]
      funext a
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, PiLp.zero_apply, smul_eq_mul]; ring
theorem listProd_mulVec_fix {D : ℕ} :
    ∀ (l : List (Matrix (Fin D) (Fin D) ℝ)) (v : Fin D → ℝ),
      (∀ M ∈ l, M *ᵥ v = v) → l.prod *ᵥ v = v
  | [], v, _ => by simp
  | M :: tl, v, hl => by
      rw [List.prod_cons, ← Matrix.mulVec_mulVec,
        listProd_mulVec_fix tl v (fun N hN ↦ hl N (List.mem_cons_of_mem M hN)),
        hl M List.mem_cons_self]
theorem nodup_map_prod_mulVec {α : Type*} {D : ℕ}
    (f : α → Matrix (Fin D) (Fin D) ℝ) {u u' : Fin D → ℝ} {w0 : α} :
    ∀ {l : List α}, l.Nodup → w0 ∈ l → f w0 *ᵥ u = u' →
      (∀ w1 ∈ l, w1 ≠ w0 → f w1 *ᵥ u = u ∧ f w1 *ᵥ u' = u') →
      (l.map f).prod *ᵥ u = u'
  | [], _, hw0, _, _ => False.elim (List.not_mem_nil hw0)
  | a :: tl, hnd, hw0, hact, hfix => by
      rcases List.nodup_cons.1 hnd with ⟨hanot, hnd_tl⟩
      rw [List.map_cons, List.prod_cons, ← Matrix.mulVec_mulVec]
      by_cases ha : a = w0
      · subst ha
        have htl : (tl.map f).prod *ᵥ u = u := by
          apply listProd_mulVec_fix; intro M hM
          rcases List.mem_map.1 hM with ⟨w1, hw1, rfl⟩
          have hne : w1 ≠ a := fun heq ↦ hanot (heq ▸ hw1)
          exact (hfix w1 (List.mem_cons_of_mem a hw1) hne).1
        rw [htl, hact]
      · have hw0_tl : w0 ∈ tl := by
          rcases List.mem_cons.1 hw0 with heq | hmem
          · exact False.elim (ha heq.symm)
          · exact hmem
        have ih := nodup_map_prod_mulVec f hnd_tl hw0_tl hact
          (fun w1 hw1 hne ↦ hfix w1 (List.mem_cons_of_mem a hw1) hne)
        rw [ih]; exact (hfix a List.mem_cons_self ha).2
/-- Top-level projector matrix `P_{V_{-, L}}` on `Fin (2 ^ (L * n))`. -/
noncomputable def pMinusLMat (L n : ℕ) [NeZero L] (hL : 1 ≤ L) (hn : 2 * L ≤ 2 ^ n) :
    Matrix (Fin (2 ^ (L * n))) (Fin (2 ^ (L * n))) ℝ :=
  matOfEnd (orthProjEnd (LinearMap.range (liftMinusAddrLI L n L hL le_rfl hn).toLinearMap))
theorem pMinusLMat_symm_idem (L n : ℕ) [NeZero L] (hL : 1 ≤ L) (hn : 2 * L ≤ 2 ^ n) :
    (pMinusLMat L n hL hn)ᵀ = pMinusLMat L n hL hn ∧
    pMinusLMat L n hL hn * pMinusLMat L n hL hn = pMinusLMat L n hL hn := by
  unfold pMinusLMat
  exact ⟨by rw [← matOfEnd_adjoint, orthProjEnd_self_adjoint],
    by rw [← matOfEnd_comp, orthProjEnd_idem]⟩
theorem pMinusLMat_mulVec_bAddrVec {L n r : ℕ} [NeZero L]
    (hL : 1 ≤ L) (hn : 2 * L ≤ 2 ^ n) (hrL : L ≤ r) (hrN : r + L ≤ 2 ^ n)
    {R : Finset (Fin (2 ^ n))} (hR : R.card = r) (j : Fin (2 * L)) :
    pMinusLMat L n hL hn *ᵥ bAddrVec L n R j =
      if j.1 = 2 * L - 1 then bAddrVec L n R j else 0 := by
  rw [bAddrVec_eq_of_neZero]; unfold pMinusLMat
  rw [matOfEnd_mulVec_ofLp, projMinus_bAddrEuclid hL le_rfl hn hrL hrN hR j]
  by_cases hj : j.1 = 2 * L - 1
  · simp [hj]
  · simp [hj]; rfl
end SwLInternal
open SwLInternal
/-! ## Public Unitary & State Definitions -/
/-- Zero-oracle real orthogonal unitary preparing uniform distinct `L`-tuple `|b_0, 0⟩` from
  `|0⟩`. -/
noncomputable def swLPrepUnitary (L n : ℕ) (hL : 2 ≤ L) (hn : 2 * L ≤ 2 ^ n) :
    Unitary (2 ^ (L * n + 1)) :=
  letI : NeZero L := ⟨by omega⟩
  letI : NeZero (2 ^ (L * n)) := ⟨Nat.pos_iff_ne_zero.1 (Nat.two_pow_pos (L * n))⟩
  SwLInternal.realOrthToUnitary
    (SwLInternal.liftAddrMat L n (SwLInternal.orthoSwapReflMat (SwLInternal.b0AddrVec L n)))
    (SwLInternal.liftAddrMat_orth L n
      (SwLInternal.orthoSwapReflMat_orth
        (SwLInternal.b0AddrVec_zero hL) (SwLInternal.b0AddrVec_normSq hn)))
theorem isRealMatrix_swLPrepUnitary (L n : ℕ) (hL : 2 ≤ L) (hn : 2 * L ≤ 2 ^ n) :
    IsRealMatrix (swLPrepUnitary L n hL hn).1 :=
  SwLInternal.isRealMatrix_realOrthToUnitary _ _
/-- Zero-oracle real symmetric reflection diffuser `D_0 ⊗ I_2` on `L * n + 1` qubits. -/
noncomputable def swLDiffuserUnitary (L n : ℕ) (hL : 2 ≤ L) (hn : 2 * L ≤ 2 ^ n) :
    Unitary (2 ^ (L * n + 1)) :=
  letI : NeZero L := ⟨by omega⟩
  SwLInternal.realOrthToUnitary
    (SwLInternal.liftAddrMat L n (SwLInternal.diffAddrMat L n hn))
    (SwLInternal.liftAddrMat_orth L n (SwLInternal.diffAddrMat_orth L n hn))
theorem isRealMatrix_swLDiffuserUnitary (L n : ℕ) (hL : 2 ≤ L) (hn : 2 * L ≤ 2 ^ n) :
    IsRealMatrix (swLDiffuserUnitary L n hL hn).1 :=
  SwLInternal.isRealMatrix_realOrthToUnitary _ _
/-- Single Grover round `(D_0 ⊗ I_2) * (O_{R, grid} ⊗ I)` on `L * n + 1` qubits. -/
noncomputable def swLGroverRoundUnitary (L n : ℕ) (hL : 2 ≤ L) (hn : 2 * L ≤ 2 ^ n)
    (R : Finset (Fin (2 ^ n))) : Unitary (2 ^ (L * n + 1)) :=
  swLDiffuserUnitary L n hL hn *
    (swLSlotReg L n ⟨0, by omega⟩).embedUnitary (swLSetOracleUnitary R)
/-- Zero-oracle real unitary `V(v) * ((∏_{w=1}^{L-1} W_w(u_w)) ⊗ I_2)` for pulse `p`. -/
noncomputable def swLPulseTailUnitary (L n : ℕ) (hL : 2 ≤ L) (hn : 2 * L ≤ 2 ^ n)
    (p : SchurWeylLCert.SwLPulseRat L)
    (hp : SchurWeylLCert.swLPulseValid p = true) : Unitary (2 ^ (L * n + 1)) :=
  letI : NeZero L := ⟨by omega⟩
  let pieriProd := ((List.finRange (L - 1)).map (SwLInternal.pieriRotMat L n hn p)).prod
  let PL := SwLInternal.pMinusLMat L n (by omega) hn
  let cv := SchurWeylLCert.swLCayleyCos p.vNum p.uvDen
  let sv := SchurWeylLCert.swLCayleySin p.vNum p.uvDen
  let W := SwLInternal.weakFlagMat L n PL cv sv
  let A := SwLInternal.liftAddrMat L n pieriProd
  SwLInternal.realOrthToUnitary (W * A) (by
    have hPL := SwLInternal.pMinusLMat_symm_idem L n (by omega) hn
    have hden : 0 < p.uvDen := by simpa [SchurWeylLCert.swLPulseValid] using hp
    have hW : Wᵀ * W = 1 :=
      SwLInternal.weakFlagMat_orth L n hPL.1 hPL.2 (SwLInternal.cayley_cos_sq_add_sin_sq hden)
    have hP : pieriProdᵀ * pieriProd = 1 := by
      apply SwLInternal.listProd_orth
      intro M hM
      rcases List.mem_map.1 hM with ⟨w0, _, rfl⟩
      exact SwLInternal.pieriRotMat_orth L n hn p hp w0
    have hA : Aᵀ * A = 1 := SwLInternal.liftAddrMat_orth L n hP
    rw [Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Wᵀ W A, hW,
      Matrix.one_mul, hA])
theorem isRealMatrix_swLPulseTailUnitary (L n : ℕ) (hL : 2 ≤ L) (hn : 2 * L ≤ 2 ^ n)
    (p : SchurWeylLCert.SwLPulseRat L)
    (hp : SchurWeylLCert.swLPulseValid p = true) :
    IsRealMatrix (swLPulseTailUnitary L n hL hn p hp).1 := by
  unfold swLPulseTailUnitary; dsimp only; exact SwLInternal.isRealMatrix_realOrthToUnitary _ _
/-- Unnormalized surviving `flag = 0` `2L`-basis state `∑_{j=0}^{2L-1} st_j |b_j, 0⟩`. -/
noncomputable def swLSurvVec (L n : ℕ) (R : Finset (Fin (2 ^ n)))
    (st : Fin (2 * L) → ℝ) : Fin (2 ^ (L * n + 1)) → ℂ :=
  fun z ↦ (SwLInternal.embedAddr0 L n
    (∑ j : Fin (2 * L), st j • SwLInternal.bAddrVec L n R j) z : ℂ)
/-- Normalized `flag = 1` early-exit click state `|b_{2L-1}, 1⟩` on `L * n + 1` qubits. -/
noncomputable def swLClickVec (L n : ℕ) (R : Finset (Fin (2 ^ n))) :
    Fin (2 ^ (L * n + 1)) → ℂ :=
  if hL0 : L = 0 then 0
  else
    fun z ↦ (SwLInternal.embedAddr1 L n
      (SwLInternal.bAddrVec L n R ⟨2 * L - 1, by omega⟩) z : ℂ)
/-- Exact `2L × 2L` orbit-to-basis overlap matrix `M o j = ⟨orbit_o | b_j⟩` for `R ⊆ Fin (2
  ^ n)`. -/
noncomputable def swLOverlapMatFn (L : ℕ) {n : ℕ} (R : Finset (Fin (2 ^ n))) :
    Fin (2 * L) → Fin (2 * L) → ℝ :=
  if hL0 : L = 0 then fun _ _ ↦ 0
  else
    letI : NeZero L := ⟨hL0⟩
    overlapTupleMat L (2 ^ n) R
/-! ## Public Dynamics, Born & Overlap Theorems -/
theorem swLPrepUnitary_mulVec_zero {L n r : ℕ} (hL : 2 ≤ L) (hn : 2 * L ≤ 2 ^ n)
    {R : Finset (Fin (2 ^ n))} (_hrL : L ≤ r) (_hrN : r + L ≤ 2 ^ n) (_hR : R.card = r) :
    (swLPrepUnitary L n hL hn).1 *ᵥ Pi.single 0 1 =
      swLSurvVec L n R (fun j ↦ if j.1 = 0 then 1 else 0) := by
  have : NeZero L := ⟨by omega⟩
  have : NeZero (2 ^ (L * n)) := ⟨Nat.pos_iff_ne_zero.1 (Nat.two_pow_pos (L * n))⟩
  have hsingle : (Pi.single 0 (1 : ℂ) : Fin (2 ^ (L * n + 1)) → ℂ) =
      fun z ↦ ((Pi.single 0 (1 : ℝ) : Fin (2 ^ (L * n + 1)) → ℝ) z : ℂ) := by
    funext z; by_cases hz : z = 0 <;> simp [hz]
  unfold swLPrepUnitary swLSurvVec
  rw [hsingle, SwLInternal.realOrthToUnitary_mulVec, ← SwLInternal.embedAddr0_single_zero L n,
    SwLInternal.liftAddrMat_mulVec_embedAddr0,
    SwLInternal.orthoSwapReflMat_mulVec_e0 (SwLInternal.b0AddrVec_zero hL)]
  funext z
  congr 1
  have hsum : (∑ j : Fin (2 * L),
      (if j.1 = 0 then (1 : ℝ) else 0) • SwLInternal.bAddrVec L n R j) =
      SwLInternal.b0AddrVec L n := by
    rw [Finset.sum_eq_single ⟨0, by omega⟩]
    · simp only [↓reduceIte, one_smul, SwLInternal.bAddrVec_eq_of_neZero]
      funext a
      unfold SwLInternal.bAddrEuclid SwLInternal.b0AddrVec
      rw [bTuple_zero L (2 ^ n) R (by omega)]
      rfl
    · intro j _ hj
      have hj0 : j.1 ≠ 0 := fun h ↦ hj (Fin.ext h)
      simp [hj0]
    · intro habs; exact False.elim (habs (Finset.mem_univ _))
  rw [hsum]
namespace SwLInternal
theorem swLGroverRotVec_even {L : ℕ} (cs : Fin L → ℝ × ℝ) (st : Fin (2 * L) → ℝ)
    (w : Fin L) :
    SchurWeylLCert.swLGroverRotVec L cs st ⟨2 * w.1, by omega⟩ =
      (cs w).1 * st ⟨2 * w.1, by omega⟩ - (cs w).2 * st ⟨2 * w.1 + 1, by omega⟩ := by
  have hev : (2 * w.1) % 2 = 0 := by omega
  have hdiv : (2 * w.1) / 2 = w.1 := by omega
  have hw : (⟨(2 * w.1) / 2, by omega⟩ : Fin L) = w := Fin.ext hdiv
  dsimp only [SchurWeylLCert.swLGroverRotVec]; rw [ite_eq_left hev, hw]
  have h0 : (⟨2 * (⟨(2 * w.1) / 2, by omega⟩ : Fin L).1, by omega⟩ : Fin (2 * L)) =
      ⟨2 * w.1, by omega⟩ := Fin.ext (by dsimp; omega)
  have h1 : (⟨2 * (⟨(2 * w.1) / 2, by omega⟩ : Fin L).1 + 1, by omega⟩ : Fin (2 * L)) =
      ⟨2 * w.1 + 1, by omega⟩ := Fin.ext (by dsimp; omega)
  rw [h0, h1]
theorem swLGroverRotVec_odd {L : ℕ} (cs : Fin L → ℝ × ℝ) (st : Fin (2 * L) → ℝ)
    (w : Fin L) :
    SchurWeylLCert.swLGroverRotVec L cs st ⟨2 * w.1 + 1, by omega⟩ =
      (cs w).2 * st ⟨2 * w.1, by omega⟩ + (cs w).1 * st ⟨2 * w.1 + 1, by omega⟩ := by
  have hodd : (2 * w.1 + 1) % 2 ≠ 0 := by omega
  have hdiv : (2 * w.1 + 1) / 2 = w.1 := by omega
  have hw : (⟨(2 * w.1 + 1) / 2, by omega⟩ : Fin L) = w := Fin.ext hdiv
  dsimp only [SchurWeylLCert.swLGroverRotVec]; rw [ite_eq_right hodd, hw]
  have h0 : (⟨2 * (⟨(2 * w.1 + 1) / 2, by omega⟩ : Fin L).1, by omega⟩ : Fin (2 * L)) =
      ⟨2 * w.1, by omega⟩ := Fin.ext (by dsimp; omega)
  have h1 : (⟨2 * (⟨(2 * w.1 + 1) / 2, by omega⟩ : Fin L).1 + 1, by omega⟩ : Fin (2 * L)) =
      ⟨2 * w.1 + 1, by omega⟩ := Fin.ext (by dsimp; omega)
  rw [h0, h1]
theorem groverRound_mulVec_survVec {L n r : ℕ} (hL : 2 ≤ L) (hn : 2 * L ≤ 2 ^ n)
    {R : Finset (Fin (2 ^ n))} (hrL : L ≤ r) (hrN : r + L ≤ 2 ^ n) (hR : R.card = r)
    (st : Fin (2 * L) → ℝ) :
    let cs₁ : Fin L → ℝ × ℝ := fun w ↦
      (Real.cos (SchurWeylLCert.swLThetaShiftReal (2 ^ n) r w.1),
       Real.sin (SchurWeylLCert.swLThetaShiftReal (2 ^ n) r w.1))
    (swLGroverRoundUnitary L n hL hn R).1 *ᵥ swLSurvVec L n R st =
      swLSurvVec L n R (SchurWeylLCert.swLGroverRotVec L cs₁ st) := by
  intro cs₁
  have : NeZero L := ⟨by omega⟩
  have : NeZero (2 ^ n) := ⟨Nat.pos_iff_ne_zero.1 (Nat.two_pow_pos n)⟩
  set v := ∑ j : Fin (2 * L), st j • bAddrVec L n R j
  set vOracle : Fin (2 ^ (L * n)) → ℝ :=
    fun a ↦ (if addrTuple L n a 0 ∈ R then (-1 : ℝ) else 1) * v a
  have horacle : ((swLSlotReg L n ⟨0, by omega⟩).embedUnitary (swLSetOracleUnitary R)).1 *ᵥ
      swLSurvVec L n R st = fun z ↦ (embedAddr0 L n vOracle z : ℂ) := by
    rw [slotOracle_mulVec]
    funext z
    unfold swLSurvVec embedAddr0
    by_cases hf : (splitEquiv L n z).2 = 0
    · have hgrd : (swLSlotReg L n ⟨0, by omega⟩).extractIndex z =
          addrTuple L n (splitEquiv L n z).1 0 := by
        have ht := congrFun (swLTuple_eq_addrTuple L n z) 0; exact ht
      simp only [hf, ↓reduceIte, hgrd, vOracle]
      by_cases hm : addrTuple L n (splitEquiv L n z).1 0 ∈ R <;> simp [hm, v]
    · simp [hf]
  have hvOracle_eq : vOracle = ∑ w : Fin L,
      ((cs₁ w).1 * st ⟨2 * w.1, by omega⟩ - (cs₁ w).2 * st ⟨2 * w.1 + 1, by omega⟩) •
        bAddrVec L n R ⟨2 * w.1, by omega⟩ +
      ∑ w : Fin L,
        (-((cs₁ w).2 * st ⟨2 * w.1, by omega⟩ + (cs₁ w).1 * st ⟨2 * w.1 + 1, by omega⟩)) •
          bAddrVec L n R ⟨2 * w.1 + 1, by omega⟩ := by
    funext a
    set x := addrTuple L n a
    have hv_pair : v a = ∑ w : Fin L,
        (st ⟨2 * w.1, by omega⟩ * bAddrVec L n R ⟨2 * w.1, by omega⟩ a +
          st ⟨2 * w.1 + 1, by omega⟩ * bAddrVec L n R ⟨2 * w.1 + 1, by omega⟩ a) := by
      have hp := congrFun (sum_fin_two_mul_add (fun j ↦ st j • bAddrVec L n R j)) a
      simpa [v, Finset.sum_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul] using hp
    dsimp only [vOracle]; rw [hv_pair, Finset.mul_sum]
    simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun w _ ↦ ?_
    have hcs := cos_sin_two_arcsin_sqrt (N := 2 ^ n) (r := r) (w := w.1) (by omega) (by omega)
    have hcw : (cs₁ w).1 = (((2 ^ n - r - w.1 : ℕ) : ℝ) - ((r - w.1 : ℕ) : ℝ)) /
          (((2 ^ n - r - w.1 : ℕ) : ℝ) + ((r - w.1 : ℕ) : ℝ)) := hcs.1
    have hsw : (cs₁ w).2 = 2 * √((2 ^ n - r - w.1 : ℕ) : ℝ) * √((r - w.1 : ℕ) : ℝ) /
          (((2 ^ n - r - w.1 : ℕ) : ℝ) + ((r - w.1 : ℕ) : ℝ)) := hcs.2
    let hit0 : Bool := if x 0 ∈ R then true else false
    have hrel : if hit0 then
        √((2 ^ n - r - w.1 : ℕ) : ℝ) * (bTuple L (2 ^ n) R ⟨2 * w.1, by omega⟩).ofLp x -
          √((r - w.1 : ℕ) : ℝ) * (bTuple L (2 ^ n) R ⟨2 * w.1 + 1, by omega⟩).ofLp x = 0
      else
        √((r - w.1 : ℕ) : ℝ) * (bTuple L (2 ^ n) R ⟨2 * w.1, by omega⟩).ofLp x +
          √((2 ^ n - r - w.1 : ℕ) : ℝ) *
            (bTuple L (2 ^ n) R ⟨2 * w.1 + 1, by omega⟩).ofLp x = 0 := by
      by_cases hx0 : x 0 ∈ R
      · simp only [hit0, hx0, ↓reduceIte]; exact bTuple_plane_mem hL hrL hrN hR w hx0
      · simp only [hit0, hx0, Bool.false_eq_true, ↓reduceIte]
        exact bTuple_plane_notMem hL hrL hrN hR w hx0
    have hrot := oracle0_plane_rot
      (by exact_mod_cast (by omega : 0 < 2 ^ n - r - w.1))
      (by exact_mod_cast (by omega : 0 < r - w.1)) hit0 hrel
    simp only [bAddrVec_eq_of_neZero]
    change (if x 0 ∈ R then (-1 : ℝ) else 1) *
        (st ⟨2 * w.1, by omega⟩ * (bTuple L (2 ^ n) R ⟨2 * w.1, by omega⟩).ofLp x +
          st ⟨2 * w.1 + 1, by omega⟩ * (bTuple L (2 ^ n) R ⟨2 * w.1 + 1, by omega⟩).ofLp x) =
      ((cs₁ w).1 * st ⟨2 * w.1, by omega⟩ - (cs₁ w).2 * st ⟨2 * w.1 + 1, by omega⟩) *
        (bTuple L (2 ^ n) R ⟨2 * w.1, by omega⟩).ofLp x +
      (-((cs₁ w).2 * st ⟨2 * w.1, by omega⟩ + (cs₁ w).1 * st ⟨2 * w.1 + 1, by omega⟩)) *
        (bTuple L (2 ^ n) R ⟨2 * w.1 + 1, by omega⟩).ofLp x
    have hsig : (if x 0 ∈ R then (-1 : ℝ) else 1) =
        if hit0 then -1 else 1 := by by_cases hx0 : x 0 ∈ R <;> simp [hit0, hx0]
    have hmul1 : (if hit0 then (-1 : ℝ) else 1) *
          (st ⟨2 * w.1, by omega⟩ * (bTuple L (2 ^ n) R ⟨2 * w.1, by omega⟩).ofLp x) =
        st ⟨2 * w.1, by omega⟩ * ((if hit0 then (-1 : ℝ) else 1) *
          (bTuple L (2 ^ n) R ⟨2 * w.1, by omega⟩).ofLp x) := by ring
    have hmul2 : (if hit0 then (-1 : ℝ) else 1) *
          (st ⟨2 * w.1 + 1, by omega⟩ * (bTuple L (2 ^ n) R ⟨2 * w.1 + 1, by omega⟩).ofLp x) =
        st ⟨2 * w.1 + 1, by omega⟩ * ((if hit0 then (-1 : ℝ) else 1) *
          (bTuple L (2 ^ n) R ⟨2 * w.1 + 1, by omega⟩).ofLp x) := by ring
    rw [hsig, left_distrib, hmul1, hmul2, hrot.1, hrot.2, hcw, hsw]; ring
  unfold swLGroverRoundUnitary
  change ((swLDiffuserUnitary L n hL hn).1 *
    ((swLSlotReg L n ⟨0, by omega⟩).embedUnitary (swLSetOracleUnitary R)).1) *ᵥ
      swLSurvVec L n R st = _
  rw [← Matrix.mulVec_mulVec, horacle]; unfold swLDiffuserUnitary
  rw [realOrthToUnitary_mulVec, liftAddrMat_mulVec_embedAddr0]; unfold swLSurvVec
  funext z; congr 1
  rw [hvOracle_eq, Matrix.mulVec_add, Matrix.mulVec_sum, Matrix.mulVec_sum,
    sum_fin_two_mul_add (fun j ↦ SchurWeylLCert.swLGroverRotVec L cs₁ st j • bAddrVec L n R j),
    Finset.sum_add_distrib]
  have h_even : ∑ w : Fin L, diffAddrMat L n hn *ᵥ
        (((cs₁ w).1 * st ⟨2 * w.1, by omega⟩ - (cs₁ w).2 * st ⟨2 * w.1 + 1, by omega⟩) •
          bAddrVec L n R ⟨2 * w.1, by omega⟩) =
      ∑ w : Fin L,
        SchurWeylLCert.swLGroverRotVec L cs₁ st ⟨2 * w.1, by omega⟩ •
          bAddrVec L n R ⟨2 * w.1, by omega⟩ := by
    refine Finset.sum_congr rfl fun w _ ↦ ?_
    rw [Matrix.mulVec_smul, diffAddrMat_mulVec_bAddrVec hn hrL hrN hR, swLGroverRotVec_even]
    have hev : (2 * w.1) % 2 ≠ 1 := by omega
    rw [ite_eq_right hev]
  have h_odd : ∑ w : Fin L, diffAddrMat L n hn *ᵥ
        ((-((cs₁ w).2 * st ⟨2 * w.1, by omega⟩ + (cs₁ w).1 * st ⟨2 * w.1 + 1, by omega⟩)) •
          bAddrVec L n R ⟨2 * w.1 + 1, by omega⟩) =
      ∑ w : Fin L,
        SchurWeylLCert.swLGroverRotVec L cs₁ st ⟨2 * w.1 + 1, by omega⟩ •
          bAddrVec L n R ⟨2 * w.1 + 1, by omega⟩ := by
    refine Finset.sum_congr rfl fun w _ ↦ ?_
    rw [Matrix.mulVec_smul, diffAddrMat_mulVec_bAddrVec hn hrL hrN hR, swLGroverRotVec_odd]
    have hodd : (2 * w.1 + 1) % 2 = 1 := by omega
    rw [ite_eq_left hodd, smul_neg, neg_smul, neg_neg]
  rw [h_even, h_odd]
theorem groverPow_mulVec_survVec {L n r : ℕ} (hL : 2 ≤ L) (hn : 2 * L ≤ 2 ^ n)
    {R : Finset (Fin (2 ^ n))} (hrL : L ≤ r) (hrN : r + L ≤ 2 ^ n) (hR : R.card = r)
    (st : Fin (2 * L) → ℝ) :
    ∀ k : ℕ,
      let csk : Fin L → ℝ × ℝ := fun w ↦
        (Real.cos ((k : ℝ) * SchurWeylLCert.swLThetaShiftReal (2 ^ n) r w.1),
         Real.sin ((k : ℝ) * SchurWeylLCert.swLThetaShiftReal (2 ^ n) r w.1))
      ((swLGroverRoundUnitary L n hL hn R ^ k).1) *ᵥ swLSurvVec L n R st =
        swLSurvVec L n R (SchurWeylLCert.swLGroverRotVec L csk st)
  | 0 => by
      intro csk
      simp only [pow_zero, Submonoid.coe_one, Matrix.one_mulVec, csk, Nat.cast_zero, zero_mul,
        Real.cos_zero, Real.sin_zero]
      have hid : SchurWeylLCert.swLGroverRotVec L (fun _ ↦ (1, 0)) st = st := by
        funext j
        unfold SchurWeylLCert.swLGroverRotVec; dsimp only
        by_cases hj : j.1 % 2 = 0
        · simp only [hj, ↓reduceIte, one_mul, zero_mul, sub_zero]; congr 1; ext; simp; omega
        · simp only [hj, ↓reduceIte, zero_mul, one_mul, zero_add]; congr 1; ext; simp; omega
      rw [hid]
  | k + 1 => by
      intro csk; rw [pow_succ' (swLGroverRoundUnitary L n hL hn R) k]
      change ((swLGroverRoundUnitary L n hL hn R).1 *
        (swLGroverRoundUnitary L n hL hn R ^ k).1) *ᵥ swLSurvVec L n R st = _
      rw [← Matrix.mulVec_mulVec, groverPow_mulVec_survVec hL hn hrL hrN hR st k,
        groverRound_mulVec_survVec hL hn hrL hrN hR]
      congr 1
      funext j
      set w : Fin L := ⟨j.1 / 2, by omega⟩
      set θ := SchurWeylLCert.swLThetaShiftReal (2 ^ n) r w.1
      have hadd : ((k + 1 : ℕ) : ℝ) * θ = (k : ℝ) * θ + θ := by push_cast; ring
      by_cases hj : j.1 % 2 = 0
      · have hj_eq : j = ⟨2 * w.1, by omega⟩ := Fin.ext (by dsimp [w]; omega)
        rw [hj_eq, swLGroverRotVec_even, swLGroverRotVec_even, swLGroverRotVec_odd,
          swLGroverRotVec_even]
        dsimp only [csk]
        change Real.cos θ * (Real.cos ((k : ℝ) * θ) * st ⟨2 * w.1, _⟩ -
              Real.sin ((k : ℝ) * θ) * st ⟨2 * w.1 + 1, _⟩) -
            Real.sin θ * (Real.sin ((k : ℝ) * θ) * st ⟨2 * w.1, _⟩ +
              Real.cos ((k : ℝ) * θ) * st ⟨2 * w.1 + 1, _⟩) =
          Real.cos (((k + 1 : ℕ) : ℝ) * θ) * st ⟨2 * w.1, _⟩ -
            Real.sin (((k + 1 : ℕ) : ℝ) * θ) * st ⟨2 * w.1 + 1, _⟩
        rw [hadd, Real.cos_add, Real.sin_add]; ring
      · have hj_eq : j = ⟨2 * w.1 + 1, by omega⟩ := Fin.ext (by dsimp [w]; omega)
        rw [hj_eq, swLGroverRotVec_odd, swLGroverRotVec_even, swLGroverRotVec_odd,
          swLGroverRotVec_odd]
        dsimp only [csk]
        change Real.sin θ * (Real.cos ((k : ℝ) * θ) * st ⟨2 * w.1, _⟩ -
              Real.sin ((k : ℝ) * θ) * st ⟨2 * w.1 + 1, _⟩) +
            Real.cos θ * (Real.sin ((k : ℝ) * θ) * st ⟨2 * w.1, _⟩ +
              Real.cos ((k : ℝ) * θ) * st ⟨2 * w.1 + 1, _⟩) =
          Real.sin (((k + 1 : ℕ) : ℝ) * θ) * st ⟨2 * w.1, _⟩ +
            Real.cos (((k + 1 : ℕ) : ℝ) * θ) * st ⟨2 * w.1 + 1, _⟩
        rw [hadd, Real.cos_add, Real.sin_add]; ring
end SwLInternal
theorem swLPulseStep_mulVec {L n r : ℕ} (hL : 2 ≤ L) (hn : 2 * L ≤ 2 ^ n)
    {R : Finset (Fin (2 ^ n))} (hrL : L ≤ r) (hrN : r + L ≤ 2 ^ n) (hR : R.card = r)
    (K_blk : ℕ) (p : SchurWeylLCert.SwLPulseRat L)
    (hp : SchurWeylLCert.swLPulseValid p = true)
    (st : Fin (2 * L) → ℝ) (cum surv : ℝ) :
    let cs : Fin L → ℝ × ℝ := fun w ↦
      (Real.cos ((K_blk : ℝ) * SchurWeylLCert.swLThetaShiftReal (2 ^ n) r w.1),
       Real.sin ((K_blk : ℝ) * SchurWeylLCert.swLThetaShiftReal (2 ^ n) r w.1))
    let out := SchurWeylLCert.swLPulseStepReal L hL cs st cum surv p
    let u := (swLPulseTailUnitary L n hL hn p hp).1 *ᵥ
      ((swLGroverRoundUnitary L n hL hn R ^ K_blk).1 *ᵥ swLSurvVec L n R st)
    ∃ α : ℝ,
      α ^ 2 = out.2.1 - cum ∧
      out.2.2 = surv + (1 - cum) ∧
      (fun z ↦ if (swLFlagReg L n).extractIndex z = 0 then u z else 0) =
        swLSurvVec L n R out.1 ∧
      (fun z ↦ if (swLFlagReg L n).extractIndex z = 1 then u z else 0) =
        (α : ℂ) • swLClickVec L n R := by
  intro cs out u
  have : NeZero L := ⟨by omega⟩
  set na := SchurWeylLCert.swLGroverRotVec L cs st
  set nxt := SchurWeylLCert.swLPieriAndWeakVec L hL p na
  set cv := SchurWeylLCert.swLCayleyCos p.vNum p.uvDen
  set sv := SchurWeylLCert.swLCayleySin p.vNum p.uvDen
  have hgrover : (swLGroverRoundUnitary L n hL hn R ^ K_blk).1 *ᵥ swLSurvVec L n R st =
      swLSurvVec L n R na :=
    SwLInternal.groverPow_mulVec_survVec hL hn hrL hrN hR st K_blk
  set pieriProd := ((List.finRange (L - 1)).map (SwLInternal.pieriRotMat L n hn p)).prod
  set PL := SwLInternal.pMinusLMat L n (by omega) hn
  have hpieri : pieriProd *ᵥ (∑ j : Fin (2 * L), na j • SwLInternal.bAddrVec L n R j) =
      na ⟨0, by omega⟩ • SwLInternal.bAddrVec L n R ⟨0, by omega⟩ +
      (∑ w0 : Fin (L - 1),
        (nxt ⟨2 * w0.1 + 1, by omega⟩ • SwLInternal.bAddrVec L n R ⟨2 * w0.1 + 1, by omega⟩ +
          nxt ⟨2 * w0.1 + 2, by omega⟩ • SwLInternal.bAddrVec L n R ⟨2 * w0.1 + 2, by omega⟩)) +
      na ⟨2 * L - 1, by omega⟩ • SwLInternal.bAddrVec L n R ⟨2 * L - 1, by omega⟩ := by
    rw [SwLInternal.sum_fin_interior_pairs_add hL
        (fun j ↦ na j • SwLInternal.bAddrVec L n R j),
      Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
      Matrix.mulVec_sum]
    have hb0 : pieriProd *ᵥ SwLInternal.bAddrVec L n R ⟨0, by omega⟩ =
        SwLInternal.bAddrVec L n R ⟨0, by omega⟩ := by
      apply SwLInternal.listProd_mulVec_fix; intro M hM
      rcases List.mem_map.1 hM with ⟨w0, _, rfl⟩
      rw [SwLInternal.pieriRotMat_mulVec_bAddrVec hn hrL hrN hR p w0]; simp
    have hbL : pieriProd *ᵥ SwLInternal.bAddrVec L n R ⟨2 * L - 1, by omega⟩ =
        SwLInternal.bAddrVec L n R ⟨2 * L - 1, by omega⟩ := by
      apply SwLInternal.listProd_mulVec_fix; intro M hM
      rcases List.mem_map.1 hM with ⟨w0, _, rfl⟩
      rw [SwLInternal.pieriRotMat_mulVec_bAddrVec hn hrL hrN hR p w0]
      have h1 : 2 * L - 1 ≠ 2 * w0.1 + 1 := by omega
      have h2 : 2 * L - 1 ≠ 2 * w0.1 + 2 := by omega
      simp [h1, h2]
    rw [hb0, hbL]; congr 1; congr 1
    refine Finset.sum_congr rfl fun w0 _ ↦ ?_
    apply SwLInternal.nodup_map_prod_mulVec (SwLInternal.pieriRotMat L n hn p)
      (List.nodup_finRange (L - 1)) (List.mem_finRange w0)
    · rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
        SwLInternal.pieriRotMat_mulVec_bAddrVec hn hrL hrN hR p w0 ⟨2 * w0.1 + 1, by omega⟩,
        SwLInternal.pieriRotMat_mulVec_bAddrVec hn hrL hrN hR p w0 ⟨2 * w0.1 + 2, by omega⟩]
      have h12 : 2 * w0.1 + 2 ≠ 2 * w0.1 + 1 := by omega
      simp only [↓reduceIte, h12]
      have hnxt1 : nxt ⟨2 * w0.1 + 1, by omega⟩ =
          SchurWeylLCert.swLCayleyCos (p.uNum w0) p.uvDen * na ⟨2 * w0.1 + 1, by omega⟩ -
            SchurWeylLCert.swLCayleySin (p.uNum w0) p.uvDen * na ⟨2 * w0.1 + 2, by omega⟩ := by
        have hn0 : 2 * w0.1 + 1 ≠ 0 := by omega
        have hlt : 2 * w0.1 + 1 < 2 * L - 1 := by omega
        have hdiv : (2 * w0.1 + 1 - 1) / 2 = w0.1 := by omega
        have hmod : (2 * w0.1 + 1 - 1) % 2 = 0 := by omega
        have hw_eq : (⟨(2 * w0.1 + 1 - 1) / 2, by omega⟩ : Fin (L - 1)) = w0 := Fin.ext hdiv
        dsimp only [nxt, SchurWeylLCert.swLPieriAndWeakVec]
        rw [dite_eq_right hn0, dite_eq_left hlt, hw_eq, ite_eq_left hmod]
        have h01 : (⟨2 * (⟨(2 * w0.1 + 1 - 1) / 2, by omega⟩ : Fin (L - 1)).1 + 1, by omega⟩ :
            Fin (2 * L)) = ⟨2 * w0.1 + 1, by omega⟩ := Fin.ext (by dsimp; omega)
        have h02 : (⟨2 * (⟨(2 * w0.1 + 1 - 1) / 2, by omega⟩ : Fin (L - 1)).1 + 2, by omega⟩ :
            Fin (2 * L)) = ⟨2 * w0.1 + 2, by omega⟩ := Fin.ext (by dsimp; omega)
        rw [h01, h02]
      have hnxt2 : nxt ⟨2 * w0.1 + 2, by omega⟩ =
          SchurWeylLCert.swLCayleySin (p.uNum w0) p.uvDen * na ⟨2 * w0.1 + 1, by omega⟩ +
            SchurWeylLCert.swLCayleyCos (p.uNum w0) p.uvDen * na ⟨2 * w0.1 + 2, by omega⟩ := by
        have hn0 : 2 * w0.1 + 2 ≠ 0 := by omega
        have hlt : 2 * w0.1 + 2 < 2 * L - 1 := by omega
        have hdiv : (2 * w0.1 + 2 - 1) / 2 = w0.1 := by omega
        have hmod : (2 * w0.1 + 2 - 1) % 2 ≠ 0 := by omega
        have hw_eq : (⟨(2 * w0.1 + 2 - 1) / 2, by omega⟩ : Fin (L - 1)) = w0 := Fin.ext hdiv
        dsimp only [nxt, SchurWeylLCert.swLPieriAndWeakVec]
        rw [dite_eq_right hn0, dite_eq_left hlt, hw_eq, ite_eq_right hmod]
        have h01 : (⟨2 * (⟨(2 * w0.1 + 2 - 1) / 2, by omega⟩ : Fin (L - 1)).1 + 1, by omega⟩ :
            Fin (2 * L)) = ⟨2 * w0.1 + 1, by omega⟩ := Fin.ext (by dsimp; omega)
        have h02 : (⟨2 * (⟨(2 * w0.1 + 2 - 1) / 2, by omega⟩ : Fin (L - 1)).1 + 2, by omega⟩ :
            Fin (2 * L)) = ⟨2 * w0.1 + 2, by omega⟩ := Fin.ext (by dsimp; omega)
        rw [h01, h02]
      rw [hnxt1, hnxt2]
      funext a; simp only [Pi.add_apply, Pi.smul_apply, neg_smul, Pi.neg_apply, smul_eq_mul]; ring
    · intro w1 _ hne
      have hfix1 : SwLInternal.pieriRotMat L n hn p w1 *ᵥ
          SwLInternal.bAddrVec L n R ⟨2 * w0.1 + 1, by omega⟩ =
          SwLInternal.bAddrVec L n R ⟨2 * w0.1 + 1, by omega⟩ := by
        rw [SwLInternal.pieriRotMat_mulVec_bAddrVec hn hrL hrN hR p w1]
        have hne_val : w1.1 ≠ w0.1 := fun h ↦ hne (Fin.ext h)
        have h1 : 2 * w0.1 + 1 ≠ 2 * w1.1 + 1 := by omega
        have h2 : 2 * w0.1 + 1 ≠ 2 * w1.1 + 2 := by omega
        rw [ite_eq_right h1, ite_eq_right h2]
      have hfix2 : SwLInternal.pieriRotMat L n hn p w1 *ᵥ
          SwLInternal.bAddrVec L n R ⟨2 * w0.1 + 2, by omega⟩ =
          SwLInternal.bAddrVec L n R ⟨2 * w0.1 + 2, by omega⟩ := by
        rw [SwLInternal.pieriRotMat_mulVec_bAddrVec hn hrL hrN hR p w1]
        have hne_val : w1.1 ≠ w0.1 := fun h ↦ hne (Fin.ext h)
        have h1 : 2 * w0.1 + 2 ≠ 2 * w1.1 + 1 := by omega
        have h2 : 2 * w0.1 + 2 ≠ 2 * w1.1 + 2 := by omega
        rw [ite_eq_right h1, ite_eq_right h2]
      refine ⟨?_, ?_⟩ <;>
        rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hfix1, hfix2]
  set wMid := pieriProd *ᵥ (∑ j : Fin (2 * L), na j • SwLInternal.bAddrVec L n R j)
  have hPL_wMid : PL *ᵥ wMid =
      na ⟨2 * L - 1, by omega⟩ • SwLInternal.bAddrVec L n R ⟨2 * L - 1, by omega⟩ := by
    rw [hpieri, Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
      Matrix.mulVec_sum]
    have h0 : PL *ᵥ SwLInternal.bAddrVec L n R ⟨0, by omega⟩ = 0 := by
      rw [SwLInternal.pMinusLMat_mulVec_bAddrVec (by omega) hn hrL hrN hR]
      have : (0 : ℕ) ≠ 2 * L - 1 := by omega
      simp [this]
    have hmid : ∑ w0 : Fin (L - 1), PL *ᵥ
        (nxt ⟨2 * w0.1 + 1, by omega⟩ • SwLInternal.bAddrVec L n R ⟨2 * w0.1 + 1, by omega⟩ +
          nxt ⟨2 * w0.1 + 2, by omega⟩ • SwLInternal.bAddrVec L n R ⟨2 * w0.1 + 2, by omega⟩) =
        0 := by
      refine Finset.sum_eq_zero fun w0 _ ↦ ?_
      rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
        SwLInternal.pMinusLMat_mulVec_bAddrVec (by omega) hn hrL hrN hR,
        SwLInternal.pMinusLMat_mulVec_bAddrVec (by omega) hn hrL hrN hR]
      have h1 : 2 * w0.1 + 1 ≠ 2 * L - 1 := by omega
      have h2 : 2 * w0.1 + 2 ≠ 2 * L - 1 := by omega
      simp [h1, h2]
    have hlast : PL *ᵥ SwLInternal.bAddrVec L n R ⟨2 * L - 1, by omega⟩ =
        SwLInternal.bAddrVec L n R ⟨2 * L - 1, by omega⟩ := by
      rw [SwLInternal.pMinusLMat_mulVec_bAddrVec (by omega) hn hrL hrN hR]; simp
    rw [h0, hmid, hlast, smul_zero, add_zero, zero_add]
  have hsurv_wMid : ((1 - PL) + cv • PL) *ᵥ wMid =
      ∑ j : Fin (2 * L), nxt j • SwLInternal.bAddrVec L n R j := by
    rw [Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, hPL_wMid,
      SwLInternal.sum_fin_interior_pairs_add hL (fun j ↦ nxt j • SwLInternal.bAddrVec L n R j)]
    have hnxt0 : nxt ⟨0, by omega⟩ = na ⟨0, by omega⟩ := by
      dsimp only [nxt, SchurWeylLCert.swLPieriAndWeakVec]; rw [dite_eq_left rfl]
    have hnxtL : nxt ⟨2 * L - 1, by omega⟩ = cv * na ⟨2 * L - 1, by omega⟩ := by
      have hn0 : 2 * L - 1 ≠ 0 := by omega
      have hnlt : ¬ (2 * L - 1 < 2 * L - 1) := by omega
      dsimp only [nxt, SchurWeylLCert.swLPieriAndWeakVec, cv]
      rw [dite_eq_right hn0, dite_eq_right hnlt]
    rw [hnxt0, hnxtL, hpieri]
    funext a
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring
  have hclick_wMid : (sv • PL) *ᵥ wMid =
      (sv * na ⟨2 * L - 1, by omega⟩) • SwLInternal.bAddrVec L n R ⟨2 * L - 1, by omega⟩ := by
    rw [Matrix.smul_mulVec, hPL_wMid, smul_smul]
  have hu_eq : u = fun z ↦
      ((SwLInternal.embedAddr0 L n (∑ j : Fin (2 * L), nxt j • SwLInternal.bAddrVec L n R j) z +
        SwLInternal.embedAddr1 L n
          ((sv * na ⟨2 * L - 1, by omega⟩) •
            SwLInternal.bAddrVec L n R ⟨2 * L - 1, by omega⟩) z : ℝ) : ℂ) := by
    dsimp only [u]; rw [hgrover]; unfold swLPulseTailUnitary swLSurvVec
    rw [SwLInternal.realOrthToUnitary_mulVec, ← Matrix.mulVec_mulVec,
      SwLInternal.liftAddrMat_mulVec_embedAddr0, SwLInternal.weakFlagMat_mulVec_embedAddr0]
    change (fun z ↦ (((SwLInternal.embedAddr0 L n (((1 - PL) + cv • PL) *ᵥ wMid) +
        SwLInternal.embedAddr1 L n ((sv • PL) *ᵥ wMid)) z : ℝ) : ℂ)) = _
    rw [hsurv_wMid, hclick_wMid]; rfl
  refine ⟨sv * na ⟨2 * L - 1, by omega⟩, ?_, rfl, ?_, ?_⟩
  · dsimp [out, SchurWeylLCert.swLPulseStepReal, na, sv]; ring
  · rw [hu_eq]
    funext z
    have hfl : (swLFlagReg L n).extractIndex z = (SwLInternal.splitEquiv L n z).2 := rfl
    have h01 : (0 : Fin 2) ≠ 1 := fun h ↦ by cases congrArg Fin.val h
    rw [hfl]; unfold swLSurvVec SwLInternal.embedAddr0 SwLInternal.embedAddr1
    by_cases hf : (SwLInternal.splitEquiv L n z).2 = 0
    · simp [hf, h01, out, SchurWeylLCert.swLPulseStepReal, nxt, na]
    · simp [hf]
  · rw [hu_eq]
    funext z
    have hfl : (swLFlagReg L n).extractIndex z = (SwLInternal.splitEquiv L n z).2 := rfl
    have h10 : (1 : Fin 2) ≠ 0 := fun h ↦ by cases congrArg Fin.val h
    have hL0 : L ≠ 0 := by omega
    rw [hfl]; unfold swLClickVec SwLInternal.embedAddr0 SwLInternal.embedAddr1
    simp only [hL0, ↓reduceDIte, Pi.smul_apply]
    by_cases hf : (SwLInternal.splitEquiv L n z).2 = 1
    · simp [hf, h10]
    · simp [hf]
namespace SwLInternal
theorem hitCount_tuple_eq_orbit {L N : ℕ} [NeZero L] (R : Finset (Fin N)) (x : Fin L → Fin N) :
    (∑ i : Fin L, if x i ∈ R then 1 else 0) = ((orbitIdxOf L R x).1 + 1) / 2 := by
  have huniv : (Finset.univ : Finset (Fin L)) = insert 0 (tailSlots L) := by ext i; simp [tailSlots]
  have h0not : (0 : Fin L) ∉ tailSlots L := by simp [tailSlots]
  rw [huniv, Finset.sum_insert h0not]
  have htail : (∑ i ∈ tailSlots L, if x i ∈ R then 1 else 0) = (tailHitSet L R x).card := by
    rw [← Finset.sum_filter]; simp [tailHitSet]
  rw [htail]; unfold orbitIdxOf; dsimp only
  split_ifs <;> omega
theorem sum_hitCount_bTuple_sq {L N r : ℕ} [NeZero L] [NeZero N]
    (hL : 2 ≤ L) (hrL : L ≤ r) (hrN : r + L ≤ N) {R : Finset (Fin N)} (hR : R.card = r)
    (c : Fin (2 * L) → ℝ) (h : ℕ) :
    (∑ x : Fin L → Fin N with (∑ i : Fin L, if x i ∈ R then 1 else 0) = h,
      ((∑ j : Fin (2 * L), c j • bTuple L N R j).ofLp x) ^ 2) =
    ∑ o : Fin (2 * L) with (o.1 + 1) / 2 = h,
      (SchurWeylLCert.swLOrbitProj (overlapTupleMat L N R) c o) ^ 2 := by
  set M := overlapTupleMat L N R
  have hexp : ∑ j : Fin (2 * L), c j • bTuple L N R j =
      ∑ o : Fin (2 * L), (SchurWeylLCert.swLOrbitProj M c o) • orbitUnitVec L N R o := by
    calc ∑ j : Fin (2 * L), c j • bTuple L N R j
        = ∑ j : Fin (2 * L), c j • ∑ o : Fin (2 * L), M o j • orbitUnitVec L N R o := by
            refine Finset.sum_congr rfl fun j _ ↦ by
              rw [← bTuple_eq_sum_orbitUnitVec hL hrL hrN hR j]
      _ = ∑ j : Fin (2 * L), ∑ o : Fin (2 * L), (M o j * c j) • orbitUnitVec L N R o := by
            refine Finset.sum_congr rfl fun j _ ↦ ?_
            rw [Finset.smul_sum]
            exact Finset.sum_congr rfl fun o _ ↦ by rw [smul_smul, mul_comm]
      _ = ∑ o : Fin (2 * L), ∑ j : Fin (2 * L), (M o j * c j) • orbitUnitVec L N R o :=
            Finset.sum_comm
      _ = ∑ o : Fin (2 * L), (SchurWeylLCert.swLOrbitProj M c o) • orbitUnitVec L N R o := by
            refine Finset.sum_congr rfl fun o _ ↦ by
              rw [← Finset.sum_smul]; rfl
  rw [hexp]
  have hsum_ofLp : ∀ (x : Fin L → Fin N),
      (∑ o : Fin (2 * L), (SchurWeylLCert.swLOrbitProj M c o) • orbitUnitVec L N R o).ofLp x =
      ∑ o : Fin (2 * L),
        ((SchurWeylLCert.swLOrbitProj M c o) • orbitUnitVec L N R o).ofLp x := fun x ↦ by
    have hgen : ∀ (s : Finset (Fin (2 * L)))
        (F : Fin (2 * L) → EuclideanSpace ℝ (Fin L → Fin N)),
        (∑ o ∈ s, F o).ofLp x = ∑ o ∈ s, (F o).ofLp x := fun s F ↦ by
      induction s using Finset.induction_on with
      | empty => rfl
      | insert a s ha ih => simp [Finset.sum_insert ha, ih]
    exact hgen Finset.univ _
  have hval_sq : ∀ x : Fin L → Fin N, ((∑ o : Fin (2 * L),
          (SchurWeylLCert.swLOrbitProj M c o) • orbitUnitVec L N R o).ofLp x) ^ 2 =
        ∑ o : Fin (2 * L),
          if x ∈ orbitSet L N R o then
            (SchurWeylLCert.swLOrbitProj M c o) ^ 2 / ((orbitSet L N R o).card : ℝ)
          else 0 := by
    intro x; rw [hsum_ofLp]
    by_cases hx : Function.Injective x
    · set o₀ := orbitIdxOf L R x
      have hx₀ : x ∈ orbitSet L N R o₀ := Finset.mem_filter.2 ⟨Finset.mem_univ _, hx, rfl⟩
      rw [Finset.sum_eq_single o₀]
      · rw [Finset.sum_eq_single o₀]
        · unfold orbitUnitVec; simp only [hx₀, ↓reduceIte, PiLp.smul_apply, smul_eq_mul, mul_one]
          rw [mul_pow, div_pow, one_pow, Real.sq_sqrt (Nat.cast_nonneg _)]; ring
        · intro o _ hne
          have hno : x ∉ orbitSet L N R o :=
            Finset.disjoint_left.1 (orbitSet_disjoint R hne.symm) hx₀
          simp [hno]
        · intro habs; exact False.elim (habs (Finset.mem_univ o₀))
      · intro o _ hne
        have hno : x ∉ orbitSet L N R o := Finset.disjoint_left.1 (orbitSet_disjoint R hne.symm) hx₀
        unfold orbitUnitVec; simp only [PiLp.smul_apply, smul_eq_mul]
        change _ * (_ * (if x ∈ orbitSet L N R o then 1 else 0)) = 0
        simp [hno]
      · intro habs; exact False.elim (habs (Finset.mem_univ o₀))
    · have hl0 : (∑ o : Fin (2 * L),
          ((SchurWeylLCert.swLOrbitProj M c o) • orbitUnitVec L N R o).ofLp x) = 0 := by
        refine Finset.sum_eq_zero fun o _ ↦ ?_
        have hno : x ∉ orbitSet L N R o := fun hm ↦ hx (Finset.mem_filter.1 hm).2.1
        unfold orbitUnitVec; simp only [PiLp.smul_apply, smul_eq_mul]
        change _ * (_ * (if x ∈ orbitSet L N R o then 1 else 0)) = 0
        simp [hno]
      rw [hl0, zero_pow (by omega)]
      symm
      refine Finset.sum_eq_zero fun o _ ↦ ?_
      have hno : x ∉ orbitSet L N R o := fun hm ↦ hx (Finset.mem_filter.1 hm).2.1
      simp [hno]
  simp_rw [hval_sq]; rw [Finset.sum_comm, Finset.sum_filter]
  refine Finset.sum_congr rfl fun o _ ↦ ?_
  have hfilt_eq : ∀ x ∈ orbitSet L N R o,
      (∑ i : Fin L, if x i ∈ R then 1 else 0) = (o.1 + 1) / 2 := by
    intro x hx; rw [hitCount_tuple_eq_orbit R x, (Finset.mem_filter.1 hx).2.2]
  by_cases hh : (o.1 + 1) / 2 = h
  · simp only [hh, ↓reduceIte]
    have hsub : (∑ x : Fin L → Fin N with (∑ i : Fin L, if x i ∈ R then 1 else 0) =
          (o.1 + 1) / 2,
        if x ∈ orbitSet L N R o then
          (SchurWeylLCert.swLOrbitProj M c o) ^ 2 / ((orbitSet L N R o).card : ℝ)
        else 0) =
        ∑ x ∈ orbitSet L N R o,
          ((SchurWeylLCert.swLOrbitProj M c o) ^ 2 / ((orbitSet L N R o).card : ℝ)) := by
      rw [← Finset.sum_filter]; congr 1
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fun ⟨_, hx⟩ ↦ hx, fun hx ↦ ⟨hfilt_eq x hx, hx⟩⟩
    rw [← hh, hsub, Finset.sum_const, nsmul_eq_mul]
    have hpos : (0 : ℝ) < ((orbitSet L N R o).card : ℝ) := by
      rw [orbitSet_card_eq hL hrL hrN hR]
      exact_mod_cast swLOrbitCardNat_pos hL hrL hrN o
    exact mul_div_cancel₀ _ hpos.ne'
  · simp only [hh, ↓reduceIte]
    refine Finset.sum_eq_zero fun x hx ↦ ?_
    have hx_not : x ∉ orbitSet L N R o := by
      intro hmem; exact hh ((hfilt_eq x hmem).symm.trans (Finset.mem_filter.1 hx).2)
    simp [hx_not]
end SwLInternal
theorem swLSurvVec_and_clickVec_born {L n r : ℕ} (hL : 2 ≤ L) (_hn : 2 * L ≤ 2 ^ n)
    {R : Finset (Fin (2 ^ n))} (hrL : L ≤ r) (hrN : r + L ≤ 2 ^ n) (hR : R.card = r) :
    (∀ (st : Fin (2 * L) → ℝ) (z : Fin (2 ^ (L * n + 1))),
      (swLFlagReg L n).extractIndex z ≠ 0 → swLSurvVec L n R st z = 0) ∧
    (∀ z : Fin (2 ^ (L * n + 1)),
      (swLFlagReg L n).extractIndex z ≠ 1 → swLClickVec L n R z = 0) ∧
    (∀ (st : Fin (2 * L) → ℝ) (z : Fin (2 ^ (L * n + 1))),
      ¬ swLIsDist L n z → swLSurvVec L n R st z = 0) ∧
    (∀ z : Fin (2 ^ (L * n + 1)),
      ¬ swLIsDist L n z → swLClickVec L n R z = 0) ∧
    (∀ st : Fin (2 * L) → ℝ,
      (∑ z : Fin (2 ^ (L * n + 1)), Complex.normSq (swLSurvVec L n R st z)) =
        SchurWeylLCert.swLNormSq st) ∧
    ((∑ z : Fin (2 ^ (L * n + 1)), Complex.normSq (swLClickVec L n R z)) = 1) ∧
    (∀ (st : Fin (2 * L) → ℝ) (cum : ℝ) (h : ℕ),
      (∑ z : Fin (2 ^ (L * n + 1)) with swLHitCount L n R z = h,
        Complex.normSq (swLSurvVec L n R st z)) +
      cum * (∑ z : Fin (2 ^ (L * n + 1)) with swLHitCount L n R z = h,
        Complex.normSq (swLClickVec L n R z)) =
        SchurWeylLCert.swLAttemptProbReal L hL (swLOverlapMatFn L R) st cum h) := by
  have : NeZero L := ⟨by omega⟩
  have : NeZero (2 ^ n) := ⟨Nat.pos_iff_ne_zero.1 (Nat.two_pow_pos n)⟩
  have hL0 : L ≠ 0 := by omega
  have hsum_ofLp : ∀ (c : Fin (2 * L) → ℝ) (x : Fin L → Fin (2 ^ n)),
      (∑ j : Fin (2 * L), c j • bTuple L (2 ^ n) R j).ofLp x =
        ∑ j : Fin (2 * L), c j * (bTuple L (2 ^ n) R j).ofLp x := fun c x ↦ by
    have hgen : ∀ (s : Finset (Fin (2 * L)))
        (F : Fin (2 * L) → EuclideanSpace ℝ (Fin L → Fin (2 ^ n))),
        (∑ j ∈ s, F j).ofLp x = ∑ j ∈ s, (F j).ofLp x := fun s F ↦ by
      induction s using Finset.induction_on with
      | empty => rfl
      | insert a s ha ih => simp [Finset.sum_insert ha, ih]
    rw [hgen]; rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro st z hf; have hfl : (SwLInternal.splitEquiv L n z).2 ≠ 0 := hf
    simp [swLSurvVec, SwLInternal.embedAddr0, hfl]
  · intro z hf; have hfl : (SwLInternal.splitEquiv L n z).2 ≠ 1 := hf
    simp [swLClickVec, hL0, SwLInternal.embedAddr1, hfl]
  · intro st z hnd
    have hni : ¬ Function.Injective
        (SwLInternal.addrTuple L n (SwLInternal.splitEquiv L n z).1) := by
      intro hinj; apply hnd; unfold swLIsDist; rw [SwLInternal.swLTuple_eq_addrTuple]; exact hinj
    unfold swLSurvVec SwLInternal.embedAddr0
    by_cases hf : (SwLInternal.splitEquiv L n z).2 = 0
    · simp only [hf, ↓reduceIte, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
        SwLInternal.bAddrVec_eq_of_neZero, Complex.ofReal_eq_zero]
      refine Finset.sum_eq_zero fun j _ ↦ ?_
      change st j * (bTuple L (2 ^ n) R j).ofLp
          (SwLInternal.addrTuple L n (SwLInternal.splitEquiv L n z).1) = 0
      rw [bTuple_of_not_injective R j hni, mul_zero]
    · simp [hf]
  · intro z hnd
    have hni : ¬ Function.Injective
        (SwLInternal.addrTuple L n (SwLInternal.splitEquiv L n z).1) := by
      intro hinj; apply hnd; unfold swLIsDist; rw [SwLInternal.swLTuple_eq_addrTuple]; exact hinj
    unfold swLClickVec SwLInternal.embedAddr1; simp only [hL0, ↓reduceDIte]
    by_cases hf : (SwLInternal.splitEquiv L n z).2 = 1
    · simp only [hf, ↓reduceIte, SwLInternal.bAddrVec_eq_of_neZero, Complex.ofReal_eq_zero]
      exact bTuple_of_not_injective R ⟨2 * L - 1, by omega⟩ hni
    · simp [hf]
  · intro st
    rw [← (SwLInternal.splitEquiv L n).symm.sum_comp
      (fun z ↦ Complex.normSq (swLSurvVec L n R st z))]
    simp only [Fintype.sum_prod_type, Fin.sum_univ_two, Finset.sum_add_distrib]
    have h01 : (1 : Fin 2) ≠ 0 := fun h ↦ by cases congrArg Fin.val h
    have hsum1 : ∑ a : Fin (2 ^ (L * n)),
        Complex.normSq (swLSurvVec L n R st ((SwLInternal.splitEquiv L n).symm (a, 0))) =
        ⟪∑ j : Fin (2 * L), st j • bTuple L (2 ^ n) R j,
          ∑ j : Fin (2 * L), st j • bTuple L (2 ^ n) R j⟫ := by
      have ha_eq : ∀ a : Fin (2 ^ (L * n)),
          Complex.normSq (swLSurvVec L n R st ((SwLInternal.splitEquiv L n).symm (a, 0))) =
            ((∑ j : Fin (2 * L), st j • bTuple L (2 ^ n) R j).ofLp
              (SwLInternal.addrEquiv L n a)) ^ 2 := by
        intro a; unfold swLSurvVec SwLInternal.embedAddr0
        simp only [Equiv.apply_symm_apply, ↓reduceIte, Complex.normSq_ofReal, sq,
          Finset.sum_apply, Pi.smul_apply, smul_eq_mul, SwLInternal.bAddrVec_eq_of_neZero,
          hsum_ofLp]
        rfl
      simp_rw [ha_eq]
      rw [(SwLInternal.addrEquiv L n).sum_comp
          (fun x ↦ ((∑ j : Fin (2 * L), st j • bTuple L (2 ^ n) R j).ofLp x) ^ 2),
        PiLp.inner_apply]
      refine Finset.sum_congr rfl fun x _ ↦ ?_
      simp [sq]
    have hsum2 : ∑ a : Fin (2 ^ (L * n)),
        Complex.normSq (swLSurvVec L n R st ((SwLInternal.splitEquiv L n).symm (a, 1))) = 0 := by
      refine Finset.sum_eq_zero fun a _ ↦ ?_
      unfold swLSurvVec SwLInternal.embedAddr0; simp [h01]
    rw [hsum1, hsum2, add_zero, sum_inner]; unfold SchurWeylLCert.swLNormSq
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [inner_sum, Finset.sum_eq_single j]
    · rw [inner_smul_left, inner_smul_right, RCLike.conj_to_real, inner_bTuple hL hrL hrN hR j j]
      simp [sq]
    · intro k _ hkj
      rw [inner_smul_left, inner_smul_right, RCLike.conj_to_real, inner_bTuple hL hrL hrN hR j k]
      simp [hkj.symm]
    · intro habs; exact False.elim (habs (Finset.mem_univ j))
  · rw [← (SwLInternal.splitEquiv L n).symm.sum_comp
      (fun z ↦ Complex.normSq (swLClickVec L n R z))]
    simp only [Fintype.sum_prod_type, Fin.sum_univ_two, Finset.sum_add_distrib]
    have h01 : (0 : Fin 2) ≠ 1 := fun h ↦ by cases congrArg Fin.val h
    have hsum0 : ∑ a : Fin (2 ^ (L * n)),
        Complex.normSq (swLClickVec L n R ((SwLInternal.splitEquiv L n).symm (a, 0))) = 0 := by
      refine Finset.sum_eq_zero fun a _ ↦ ?_
      unfold swLClickVec SwLInternal.embedAddr1; simp [hL0, h01]
    have hsum1 : ∑ a : Fin (2 ^ (L * n)),
        Complex.normSq (swLClickVec L n R ((SwLInternal.splitEquiv L n).symm (a, 1))) =
        ⟪bTuple L (2 ^ n) R ⟨2 * L - 1, by omega⟩,
          bTuple L (2 ^ n) R ⟨2 * L - 1, by omega⟩⟫ := by
      have ha_eq : ∀ a : Fin (2 ^ (L * n)),
          Complex.normSq (swLClickVec L n R ((SwLInternal.splitEquiv L n).symm (a, 1))) =
            ((bTuple L (2 ^ n) R ⟨2 * L - 1, by omega⟩).ofLp
              (SwLInternal.addrEquiv L n a)) ^ 2 := by
        intro a; unfold swLClickVec SwLInternal.embedAddr1
        simp only [hL0, ↓reduceDIte, Equiv.apply_symm_apply, ↓reduceIte, Complex.normSq_ofReal, sq,
          SwLInternal.bAddrVec_eq_of_neZero]
        rfl
      simp_rw [ha_eq]
      rw [(SwLInternal.addrEquiv L n).sum_comp
          (fun x ↦ ((bTuple L (2 ^ n) R ⟨2 * L - 1, by omega⟩).ofLp x) ^ 2),
        PiLp.inner_apply]
      refine Finset.sum_congr rfl fun x _ ↦ ?_
      simp [sq]
    rw [hsum0, zero_add, hsum1, inner_bTuple hL hrL hrN hR]; simp
  · intro st cum h
    have hhit_z : ∀ z : Fin (2 ^ (L * n + 1)), swLHitCount L n R z = ∑ i : Fin L,
            if SwLInternal.addrEquiv L n (SwLInternal.splitEquiv L n z).1 i ∈ R then 1 else 0 := by
      intro z; unfold swLHitCount
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      have ht := congrFun (SwLInternal.swLTuple_eq_addrTuple L n z) i
      exact congrArg (fun u ↦ if u ∈ R then 1 else 0) ht
    have hsurv_sum : (∑ z : Fin (2 ^ (L * n + 1)) with swLHitCount L n R z = h,
        Complex.normSq (swLSurvVec L n R st z)) =
        ∑ o : Fin (2 * L) with (o.1 + 1) / 2 = h,
          (SchurWeylLCert.swLOrbitProj (overlapTupleMat L (2 ^ n) R) st o) ^ 2 := by
      rw [Finset.sum_filter, ← (SwLInternal.splitEquiv L n).symm.sum_comp
          (fun z ↦ if swLHitCount L n R z = h then Complex.normSq (swLSurvVec L n R st z) else 0)]
      simp only [Fintype.sum_prod_type, Fin.sum_univ_two, Finset.sum_add_distrib]
      have h01 : (1 : Fin 2) ≠ 0 := fun h ↦ by cases congrArg Fin.val h
      have hf1 : ∑ a : Fin (2 ^ (L * n)),
          (if swLHitCount L n R ((SwLInternal.splitEquiv L n).symm (a, 1)) = h then
            Complex.normSq (swLSurvVec L n R st ((SwLInternal.splitEquiv L n).symm (a, 1)))
          else 0) = 0 := by
        refine Finset.sum_eq_zero fun a _ ↦ ?_
        unfold swLSurvVec SwLInternal.embedAddr0; simp [h01]
      rw [hf1, add_zero]
      have hf0 : ∀ a : Fin (2 ^ (L * n)),
          (if swLHitCount L n R ((SwLInternal.splitEquiv L n).symm (a, 0)) = h then
            Complex.normSq (swLSurvVec L n R st ((SwLInternal.splitEquiv L n).symm (a, 0)))
          else 0) =
          if (∑ i : Fin L, if SwLInternal.addrEquiv L n a i ∈ R then 1 else 0) = h then
            ((∑ j : Fin (2 * L), st j • bTuple L (2 ^ n) R j).ofLp
              (SwLInternal.addrEquiv L n a)) ^ 2
          else 0 := by
        intro a; rw [hhit_z]; unfold swLSurvVec SwLInternal.embedAddr0
        simp only [Equiv.apply_symm_apply, ↓reduceIte, Complex.normSq_ofReal, sq,
          Finset.sum_apply, Pi.smul_apply, smul_eq_mul, SwLInternal.bAddrVec_eq_of_neZero,
          hsum_ofLp]
        rfl
      simp_rw [hf0]
      rw [(SwLInternal.addrEquiv L n).sum_comp
          (fun x ↦ if (∑ i : Fin L, if x i ∈ R then 1 else 0) = h then
            ((∑ j : Fin (2 * L), st j • bTuple L (2 ^ n) R j).ofLp x) ^ 2 else 0),
        ← Finset.sum_filter]
      exact SwLInternal.sum_hitCount_bTuple_sq hL hrL hrN hR st h
    let eClick : Fin (2 * L) → ℝ := fun j ↦ if j = ⟨2 * L - 1, by omega⟩ then 1 else 0
    have hclick_sum : (∑ z : Fin (2 ^ (L * n + 1)) with swLHitCount L n R z = h,
        Complex.normSq (swLClickVec L n R z)) =
        ∑ o : Fin (2 * L) with (o.1 + 1) / 2 = h,
          (overlapTupleMat L (2 ^ n) R o ⟨2 * L - 1, by omega⟩) ^ 2 := by
      rw [Finset.sum_filter, ← (SwLInternal.splitEquiv L n).symm.sum_comp
          (fun z ↦ if swLHitCount L n R z = h then Complex.normSq (swLClickVec L n R z) else 0)]
      simp only [Fintype.sum_prod_type, Fin.sum_univ_two, Finset.sum_add_distrib]
      have h01 : (0 : Fin 2) ≠ 1 := fun h ↦ by cases congrArg Fin.val h
      have hf0 : ∑ a : Fin (2 ^ (L * n)),
          (if swLHitCount L n R ((SwLInternal.splitEquiv L n).symm (a, 0)) = h then
            Complex.normSq (swLClickVec L n R ((SwLInternal.splitEquiv L n).symm (a, 0)))
          else 0) = 0 := by
        refine Finset.sum_eq_zero fun a _ ↦ ?_
        unfold swLClickVec SwLInternal.embedAddr1; simp [hL0, h01]
      rw [hf0, zero_add]
      have heClick_vec : ∑ j : Fin (2 * L), eClick j • bTuple L (2 ^ n) R j =
          bTuple L (2 ^ n) R ⟨2 * L - 1, by omega⟩ := by
        simp [eClick]
      have hf1 : ∀ a : Fin (2 ^ (L * n)),
          (if swLHitCount L n R ((SwLInternal.splitEquiv L n).symm (a, 1)) = h then
            Complex.normSq (swLClickVec L n R ((SwLInternal.splitEquiv L n).symm (a, 1)))
          else 0) =
          if (∑ i : Fin L, if SwLInternal.addrEquiv L n a i ∈ R then 1 else 0) = h then
            ((∑ j : Fin (2 * L), eClick j • bTuple L (2 ^ n) R j).ofLp
              (SwLInternal.addrEquiv L n a)) ^ 2
          else 0 := by
        intro a; rw [hhit_z, heClick_vec]; unfold swLClickVec SwLInternal.embedAddr1
        simp only [hL0, ↓reduceDIte, Equiv.apply_symm_apply, ↓reduceIte, Complex.normSq_ofReal, sq,
          SwLInternal.bAddrVec_eq_of_neZero]
        rfl
      simp_rw [hf1]
      rw [(SwLInternal.addrEquiv L n).sum_comp
          (fun x ↦ if (∑ i : Fin L, if x i ∈ R then 1 else 0) = h then
            ((∑ j : Fin (2 * L), eClick j • bTuple L (2 ^ n) R j).ofLp x) ^ 2 else 0),
        ← Finset.sum_filter, SwLInternal.sum_hitCount_bTuple_sq hL hrL hrN hR eClick h]
      refine Finset.sum_congr rfl fun o _ ↦ ?_
      have hproj : SchurWeylLCert.swLOrbitProj (overlapTupleMat L (2 ^ n) R) eClick o =
          overlapTupleMat L (2 ^ n) R o ⟨2 * L - 1, by omega⟩ := by
        unfold SchurWeylLCert.swLOrbitProj; simp [eClick]
      rw [hproj]
    have hM : swLOverlapMatFn L R = overlapTupleMat L (2 ^ n) R := by simp [swLOverlapMatFn, hL0]
    rw [hsurv_sum, hclick_sum, hM]; unfold SchurWeylLCert.swLAttemptProbReal
    by_cases hh0 : h = 0
    · subst hh0
      simp only [↓reduceIte]
      have hset : (Finset.univ.filter fun o : Fin (2 * L) ↦ (o.1 + 1) / 2 = 0) =
          {⟨0, by omega⟩} := by
        ext o; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
          Fin.ext_iff]; omega
      rw [hset, Finset.sum_singleton, Finset.sum_singleton]
    · simp only [hh0, ↓reduceIte]
      by_cases hhl : h < L
      · simp only [hhl, ↓reduceDIte]
        have hset : (Finset.univ.filter fun o : Fin (2 * L) ↦ (o.1 + 1) / 2 = h) =
            {⟨2 * h - 1, by omega⟩, ⟨2 * h, by omega⟩} := by
          ext o
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
            Finset.mem_singleton, Fin.ext_iff]
          omega
        have hne_pair : (⟨2 * h - 1, by omega⟩ : Fin (2 * L)) ≠ ⟨2 * h, by omega⟩ := by
          intro heq; have := congrArg Fin.val heq; dsimp at this; omega
        rw [hset, Finset.sum_pair hne_pair, Finset.sum_pair hne_pair]
      · simp only [hhl, ↓reduceDIte]
        by_cases hhL : h = L
        · simp only [hhL, ↓reduceIte]
          have hset : (Finset.univ.filter fun o : Fin (2 * L) ↦ (o.1 + 1) / 2 = L) =
              {⟨2 * L - 1, by omega⟩} := by
            ext o
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
              Fin.ext_iff]
            have := o.2; omega
          rw [hset, Finset.sum_singleton, Finset.sum_singleton]
        · simp only [hhL, ↓reduceIte]
          have hset : (Finset.univ.filter fun o : Fin (2 * L) ↦ (o.1 + 1) / 2 = h) = ∅ := by
            ext o
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
            have := o.2; omega
          rw [hset, Finset.sum_empty, Finset.sum_empty, mul_zero, add_zero]
theorem swLSurvVec_orbit_const {L n r : ℕ} (hL : 2 ≤ L) (_hn : 2 * L ≤ 2 ^ n)
    {R : Finset (Fin (2 ^ n))} (hrL : L ≤ r) (hrN : r + L ≤ 2 ^ n) (hR : R.card = r)
    (st : Fin (2 * L) → ℝ) {z₁ z₂ : Fin (2 ^ (L * n + 1))}
    (hf : (swLFlagReg L n).extractIndex z₁ = (swLFlagReg L n).extractIndex z₂)
    (hd : swLIsDist L n z₁ ↔ swLIsDist L n z₂)
    (hm : ∀ i : Fin L, ((swLSlotReg L n i).extractIndex z₁ ∈ R) ↔
      ((swLSlotReg L n i).extractIndex z₂ ∈ R)) :
    swLSurvVec L n R st z₁ = swLSurvVec L n R st z₂ := by
  have : NeZero L := ⟨by omega⟩
  have : NeZero (2 ^ n) := ⟨Nat.pos_iff_ne_zero.1 (Nat.two_pow_pos n)⟩
  have hf' : (SwLInternal.splitEquiv L n z₁).2 = (SwLInternal.splitEquiv L n z₂).2 := hf
  unfold swLSurvVec SwLInternal.embedAddr0
  by_cases hf0 : (SwLInternal.splitEquiv L n z₁).2 = 0
  · have hf0' : (SwLInternal.splitEquiv L n z₂).2 = 0 := hf'.symm.trans hf0
    simp only [hf0, hf0', ↓reduceIte]
    set x₁ := SwLInternal.addrTuple L n (SwLInternal.splitEquiv L n z₁).1
    set x₂ := SwLInternal.addrTuple L n (SwLInternal.splitEquiv L n z₂).1
    have hx₁_eq : swLTuple L n z₁ = x₁ := SwLInternal.swLTuple_eq_addrTuple L n z₁
    have hx₂_eq : swLTuple L n z₂ = x₂ := SwLInternal.swLTuple_eq_addrTuple L n z₂
    by_cases hdist₁ : swLIsDist L n z₁
    · have hdist₂ : swLIsDist L n z₂ := hd.1 hdist₁
      have hinj₁ : Function.Injective x₁ := by rwa [swLIsDist, hx₁_eq] at hdist₁
      have hinj₂ : Function.Injective x₂ := by rwa [swLIsDist, hx₂_eq] at hdist₂
      have hm_tup : ∀ i : Fin L, x₁ i ∈ R ↔ x₂ i ∈ R := by
        intro i; have h1 : (swLSlotReg L n i).extractIndex z₁ = x₁ i := congrFun hx₁_eq i
        have h2 : (swLSlotReg L n i).extractIndex z₂ = x₂ i := congrFun hx₂_eq i; rw [← h1, ← h2]
        exact hm i
      set o := orbitIdxOf L R x₁
      have ho_eq : orbitIdxOf L R x₂ = o := by
        apply Fin.ext; unfold orbitIdxOf tailHitSet; dsimp only [o, orbitIdxOf, tailHitSet]
        have hfilt : (tailSlots L).filter (fun p ↦ x₂ p ∈ R) =
            (tailSlots L).filter (fun p ↦ x₁ p ∈ R) := by
          ext p; simp [hm_tup p]
        have h0 : (if x₂ 0 ∈ R then 1 else 0) = (if x₁ 0 ∈ R then 1 else 0) := by
          by_cases h0R : x₁ 0 ∈ R
          · have h0R2 : x₂ 0 ∈ R := (hm_tup 0).1 h0R; simp [h0R, h0R2]
          · have h0R2 : x₂ 0 ∉ R := fun h ↦ h0R ((hm_tup 0).2 h); simp [h0R, h0R2]
        rw [hfilt, h0]
      have hx₁_orb : x₁ ∈ orbitSet L (2 ^ n) R o :=
        Finset.mem_filter.2 ⟨Finset.mem_univ _, hinj₁, rfl⟩
      have hx₂_orb : x₂ ∈ orbitSet L (2 ^ n) R o :=
        Finset.mem_filter.2 ⟨Finset.mem_univ _, hinj₂, ho_eq⟩
      congr 1
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, SwLInternal.bAddrVec_eq_of_neZero]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      congr 1; exact bTuple_const_on_orbit hL hrL hrN hR o j hx₁_orb hx₂_orb
    · have hdist₂ : ¬ swLIsDist L n z₂ := fun h ↦ hdist₁ (hd.2 h)
      have hni₁ : ¬ Function.Injective x₁ := by rwa [swLIsDist, hx₁_eq] at hdist₁
      have hni₂ : ¬ Function.Injective x₂ := by rwa [swLIsDist, hx₂_eq] at hdist₂
      congr 1
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, SwLInternal.bAddrVec_eq_of_neZero]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      change st j * (bTuple L (2 ^ n) R j).ofLp x₁ = st j * (bTuple L (2 ^ n) R j).ofLp x₂
      rw [bTuple_of_not_injective R j hni₁, bTuple_of_not_injective R j hni₂]
  · have hf0' : (SwLInternal.splitEquiv L n z₂).2 ≠ 0 := fun h ↦ hf0 (hf'.trans h)
    simp [hf0, hf0']
theorem isValidSwLOverlap_swLOverlapMatFn {L n r : ℕ} (hL : 2 ≤ L) (hL8 : L ≤ 8) (hn : 96 ≤ n)
    {R : Finset (Fin (2 ^ n))} (hrL : L ≤ r) (hr1024 : r ≤ 1024) (hR : R.card = r) :
    SchurWeylLCert.IsValidSwLOverlap (swLOverlapMatFn L R) := by
  have : NeZero L := ⟨by omega⟩
  have : NeZero (2 ^ n) := ⟨Nat.pos_iff_ne_zero.1 (Nat.two_pow_pos n)⟩
  have hL0 : L ≠ 0 := by omega
  have hrN : r + L ≤ 2 ^ n := by
    have h96 : 1032 ≤ 2 ^ 96 := by norm_num
    have hpow := Nat.pow_le_pow_right (by omega : 1 ≤ 2) hn
    omega
  have hM : swLOverlapMatFn L R = overlapTupleMat L (2 ^ n) R := by simp [swLOverlapMatFn, hL0]
  rw [hM]
  refine isValidSwLOverlap_of_orth_and_diag
    (overlapTupleMat_col_orth hL hrL hrN hR)
    (overlapTupleMat_row_orth hL hrL hrN hR)
    (fun j ↦ ?_) (fun j ↦ ?_)
  · rw [overlapTupleMat_diag_eq hL hrL hrN hR j]
    exact (swLDiagOverlap_bounds hL hL8 hn hrL hr1024 j).1
  · rw [overlapTupleMat_diag_eq hL hrL hrN hR j]
    exact (swLDiagOverlap_bounds hL hL8 hn hrL hr1024 j).2
end QuantumComputation.Specs.GroverFindAll
