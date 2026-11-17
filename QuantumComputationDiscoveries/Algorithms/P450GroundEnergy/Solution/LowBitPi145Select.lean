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

public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.SelectMux
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.SelectSwapQROM
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.Balanced160Core145
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.Pi145SOSPermBridge
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.Defs

/-!
# Bell-Basis `CSWAP_58` Singlet-Parity Bridge

Implements spin-swap conjugation around a spin-idle `pMid` using an asymmetric
Bell-singlet exit/entry pair `dBellExit58Dyn` (`232 T`, `0 TOFF`, Cody Jones 4-`T` `jonesToffoli`
singlet-parity cascade into `wBellDst` + `CZ wSig1 wBellDst`) and `dBellEntry58Dyn` (`0 T`,
`0 TOFF`, `CZ wSig2 wBellDst` + `X`-basis measurement/reset + classical 58-pair `CZ` fixup).

References:
- C. Jones, "Low-overhead constructions for the fault-tolerant Toffoli gate",
  Phys. Rev. A 87, 022328 (2013), arXiv:1212.5069.
- C. Gidney, "Halving the cost of quantum addition", Quantum 2, 74 (2018), arXiv:1709.06648.
- R. Babbush, C. Gidney, D. W. Berry, N. Wiebe, J. McClean, A. Paler, A. Fowler, and H. Neven,
  "Encoding Electronic Spectra in Quantum Circuits with Linear T Complexity",
  Phys. Rev. X 8, 041015 (2018), arXiv:1805.03662.
-/

@[expose] public section

namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.BellSingletCSwap58
open QuantumComputation.Specs QuantumComputation.Specs.P450

open Operator Matrix Circuit QProg HermitianMat Real
open Solution.BlockEncodingCore Solution.BlockEncodingCircuit
open QuantumComputation.Specs.P450 Solution
open Solution.SelectSwapQROM
open scoped Matrix BigOperators ComplexOrder MatrixOrder Circuit.Notation

/-! ## Section 1: Disjoint-Support Commutation, `UsesDisjointWires`, and `PreservesVInv` -/

/-- Classical-variable `v`-invariance preservation contract for a middle `DynamicCircuit`. -/
def PreservesVInv {Var : Type} [Fintype Var] [DecidableEq Var] {N : ℕ} [NeZero (2 ^ N)]
    (v : Var) (p : DynamicCircuit Var N) : Prop :=
  ∀ Θ : QCAssertion Var (2 ^ N), (∀ σ val, Θ (Function.update σ v val) = Θ σ) →
    ∀ σ val, wp p.compile Θ (Function.update σ v val) = wp p.compile Θ σ

theorem disjointWires_of_disjoint_image {N k m : ℕ}
    {r₁ : QRegister k N} {r₂ : QRegister m N} (h : Disjoint r₁.image r₂.image) :
    r₁.DisjointWires r₂ := by
  rw [QRegister.disjoint_iff]; intro i j heq
  exact Finset.disjoint_left.mp h ((QRegister.mem_image r₁ _).mpr ⟨i, rfl⟩)
    (heq ▸ (QRegister.mem_image r₂ _).mpr ⟨j, rfl⟩)

theorem embedMatrix_comm_circuit_of_disjoint {N k : ℕ} (r : QRegister k N) (A : Operator (2 ^ k))
    (c : Circuit N) (h : Disjoint r.image c.support) :
    r.embedMatrix A * c.eval.1 = c.eval.1 * r.embedMatrix A := by
  induction c with
  | identity => simp
  | gate g r' =>
    exact r.embedMatrix_comm_of_disjoint r' (disjointWires_of_disjoint_image h) A g.eval.1
  | seq c₁ c₂ ih₁ ih₂ =>
    simp only [Circuit.support_seq, Finset.disjoint_union_right] at h
    simp only [Circuit.eval_seq, Submonoid.coe_mul]
    rw [← Matrix.mul_assoc, ih₂ h.2, Matrix.mul_assoc, ih₁ h.1, ← Matrix.mul_assoc]

theorem circuit_eval_comm_of_disjoint {N : ℕ} (c₁ c₂ : Circuit N)
    (h : Disjoint c₁.support c₂.support) : c₁.eval * c₂.eval = c₂.eval * c₁.eval := by
  induction c₁ with
  | identity => simp
  | gate g r => apply Subtype.ext; exact embedMatrix_comm_circuit_of_disjoint r g.eval.1 c₂ h
  | seq a b iha ihb =>
    simp only [Circuit.support_seq, Finset.disjoint_union_left] at h
    simp only [Circuit.eval_seq]; rw [mul_assoc, iha h.1, ← mul_assoc, ihb h.2, mul_assoc]

theorem wp_qAssign_comm_wp_of_disjoint {Var : Type} [Fintype Var] [DecidableEq Var]
    {N : ℕ} [NeZero (2 ^ N)] (uCirc : Circuit N) (p : DynamicCircuit Var N)
    (hDisj : Disjoint p.support uCirc.support) (Θ : QCAssertion Var (2 ^ N)) :
    qcWpQAssign uCirc.eval (wp p.compile Θ) = wp p.compile (qcWpQAssign uCirc.eval Θ) := by
  induction p using DynamicCircuit.qcInd generalizing Θ with
  | circuit c =>
    simp only [DynamicCircuit.compile_circuit, DynamicCircuit.qc_wp_circuit_compile,
      qc_wp_qAssign_comp, circuit_eval_comm_of_disjoint c uCirc hDisj]
  | measure x r =>
    funext σ; apply Subtype.ext
    simp only [DynamicCircuit.compile_measure, QProg.measureRegister, qc_wp_qMeasure',
      qc_wp_qMeasure_apply, qc_qMeasure_obs_map_coe, QCAssertion.subst_apply, qcWpQAssign,
      qcQAssignObsMap, Observable.conj_coe, Unitary.coe_star, Matrix.star_eq_conjTranspose, map_sum,
      qc_qMeasure_outcome_herm_eq_conj, CompleteMeasurement.toMeasurement_coe,
      QRegister.computationalBasisMeasurement_apply, conj_conj]
    refine Finset.sum_congr rfl fun o _ ↦ ?_
    have hc : r.basisOutcomeProjector o * uCirc.eval.1 =
        uCirc.eval.1 * r.basisOutcomeProjector o :=
      embedMatrix_comm_circuit_of_disjoint r (compProj o) uCirc hDisj
    have hadj : uCirc.eval.1ᴴ * (r.basisOutcomeProjector o)ᴴ =
        (r.basisOutcomeProjector o)ᴴ * uCirc.eval.1ᴴ := by
      simpa only [conjTranspose_mul] using congrArg conjTranspose hc
    rw [hadj]
  | qIf cond t f iht ihf =>
    simp only [DynamicCircuit.support_qcRawQIf, Finset.disjoint_union_left] at hDisj
    funext σ; simp only [DynamicCircuit.compile_qcRawQIf, wp_qcRawQIf, qcWpQAssign]
    split_ifs
    · exact congrFun (iht hDisj.1 Θ) σ
    · exact congrFun (ihf hDisj.2 Θ) σ
  | seq p₁ p₂ ih₁ ih₂ =>
    simp only [DynamicCircuit.support_seq, Finset.disjoint_union_left] at hDisj
    change qcWpQAssign uCirc.eval (wp p₁.compile (wp p₂.compile Θ)) =
      wp p₁.compile (wp p₂.compile (qcWpQAssign uCirc.eval Θ))
    rw [ih₁ hDisj.1 (wp p₂.compile Θ), ih₂ hDisj.2 Θ]
/-! ## Section 2: Local `2 * 58` Bell-Basis Circuits & Singlet-Parity SWAP Identity -/
/-- Single-orbital Bell-basis entry pair `CNOT a b ;;ᶜ H a`. -/
def bellPrePair {N : ℕ} (a b : Wire N) (hab : a ≠ b) : Circuit N := Circuit.CNOT a b hab ;;ᶜ .H a
/-- Single-orbital Bell-basis exit pair `H a ;;ᶜ CNOT a b`. -/
def bellPostPair {N : ℕ} (a b : Wire N) (hab : a ≠ b) : Circuit N := Circuit.H a ;;ᶜ .CNOT a b hab
theorem bellPostPair_mulVec_superpos {N : ℕ} (a b : Wire N) (hab : a ≠ b)
    (β₁ : BitAssignment N) (s : ZMod 2) :
    (bellPostPair a b hab).eval.1.mulVec
        (sqrtHalf • (ket (Function.update β₁ a 0) + bitSign s • ket (Function.update β₁ a 1))) =
      ket (Function.update (Function.update β₁ a s) b (β₁ b + s)) := by
  have hHa : (Circuit.H a).eval.1.mulVec
      (sqrtHalf • (ket (Function.update β₁ a 0) + bitSign s • ket (Function.update β₁ a 1))) =
      ket (Function.update β₁ a s) := by
    simp only [Matrix.mulVec_smul, Matrix.mulVec_add, ket_H, Function.update_self,
      Function.update_idem, smul_add, smul_smul]
    have hbs0 : bitSign 0 = 1 := rfl
    have hbs1 : bitSign 1 = -1 := rfl
    rcases bit_cases s with rfl | rfl <;> {
      rw [hbs0, hbs1]; funext g; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring_nf; rw [sq, sqrtHalf_mul_sqrtHalf]; ring }
  rw [bellPostPair, eval_seq_mulVec, hHa, ket_CNOT, Function.update_self,
    Function.update_of_ne hab.symm]

theorem bellPostPair_mul_bellPrePair {N : ℕ} (a b : Wire N) (hab : a ≠ b) :
    (bellPostPair a b hab).eval * (bellPrePair a b hab).eval = 1 := by
  apply Subtype.ext; apply matrix_ext_ket; intro β
  simp only [Submonoid.coe_mul, Submonoid.coe_one, ← Matrix.mulVec_mulVec, Matrix.one_mulVec]
  rw [bellPrePair, eval_seq_mulVec, ket_CNOT, ket_H, Function.update_of_ne hab,
    bellPostPair_mulVec_superpos a b hab _ (β a), Function.update_self,
    Function.update_comm hab.symm, Function.update_idem]
  have hadd : β b + β a + β a = β b := by rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
  rw [hadd, Function.update_eq_self, Function.update_eq_self]

theorem bellPostPair_cz_bellPrePair_ket {N : ℕ} (a b : Wire N) (hab : a ≠ b)
    (β : BitAssignment N) :
    (bellPostPair a b hab).eval.1.mulVec
        ((czCircuit a b hab).eval.1.mulVec ((bellPrePair a b hab).eval.1.mulVec (ket β))) =
      ket (Function.update (Function.update β a (β b)) b (β a)) := by
  let β₁ := Function.update β b (β b + β a)
  have hcz : (czCircuit a b hab).eval.1.mulVec ((bellPrePair a b hab).eval.1.mulVec (ket β)) =
      sqrtHalf • (ket (Function.update β₁ a 0) + bitSign (β b) • ket (Function.update β₁ a 1)) := by
    rw [bellPrePair, eval_seq_mulVec, ket_CNOT, ket_H, Function.update_of_ne hab]
    simp only [Matrix.mulVec_smul, Matrix.mulVec_add, ket_czCircuit, Function.update_self,
      Function.update_of_ne hab.symm, zero_mul, one_mul, β₁]
    have hbs0 : bitSign 0 = 1 := rfl
    have hbs : bitSign (β a) * bitSign (β b + β a) = bitSign (β b) := by
      rw [bitSign_add, mul_comm (bitSign (β b)), ← mul_assoc, bitSign_mul_self, one_mul]
    rw [hbs0, one_smul, smul_smul, hbs]
  rw [hcz, bellPostPair_mulVec_superpos a b hab β₁ (β b)]; dsimp only [β₁]
  rw [Function.update_self, Function.update_comm hab.symm, Function.update_idem]
  have hadd : β b + β a + β b = β a := by rw [add_right_comm, CharTwo.add_self_eq_zero, zero_add]
  rw [hadd]

theorem pairM_ne (M k : ℕ) (hk : k < M) : (⟨k, by omega⟩ : Wire (2 * M)) ≠ ⟨M + k, by omega⟩ := by
  intro h; have := congrArg Fin.val h; dsimp at this; omega

/-- Prefix of `k ≤ M` orbital Bell-entry pairs on `2 * M` wires. -/
def bellPrePrefix (M : ℕ) : (k : ℕ) → k ≤ M → Circuit (2 * M)
  | 0, _ => .identity
  | k + 1, hk =>
    bellPrePrefix M k (by omega) ;;ᶜ bellPrePair ⟨k, by omega⟩ ⟨M + k, by omega⟩ (pairM_ne M k hk)
/-- Prefix of `k ≤ M` orbital Bell-exit pairs on `2 * M` wires. -/
def bellPostPrefix (M : ℕ) : (k : ℕ) → k ≤ M → Circuit (2 * M)
  | 0, _ => .identity
  | k + 1, hk =>
    bellPostPair ⟨k, by omega⟩ ⟨M + k, by omega⟩ (pairM_ne M k hk) ;;ᶜ bellPostPrefix M k (by omega)
/-- Prefix of `k ≤ M` orbital-pair `CZ (p, M + p)` gates on `2 * M` wires. -/
def czPairsPrefixLoc (M : ℕ) : (k : ℕ) → k ≤ M → Circuit (2 * M)
  | 0, _ => .identity
  | k + 1, hk =>
    czPairsPrefixLoc M k (by omega) ;;ᶜ czCircuit ⟨k, by omega⟩ ⟨M + k, by omega⟩ (pairM_ne M k hk)

theorem pair58_ne (k : ℕ) (hk : k < 58) : (⟨k, by omega⟩ : Wire (2 * 58)) ≠ ⟨58 + k, by omega⟩ :=
  pairM_ne 58 k hk

/-- Clifford Bell-basis entry transform on `2 * 58` spin-orbital wires (`0 T`, `0 TOFF`). -/
def bellPre58Circuit : Circuit (2 * 58) := bellPrePrefix 58 58 le_rfl
/-- Clifford Bell-basis exit transform on `2 * 58` spin-orbital wires (`0 T`, `0 TOFF`). -/
def bellPost58Circuit : Circuit (2 * 58) := bellPostPrefix 58 58 le_rfl
/-- Product of `58` orbital-pair `CZ (p, 58 + p)` gates on `2 * 58` wires (`0 T`, `0 TOFF`). -/
def czPairs58Circuit : Circuit (2 * 58) := czPairsPrefixLoc 58 58 le_rfl
/-- Ambient relocation of `bellPre58Circuit` onto `rSys116`. -/
abbrev bellPre58On {N : ℕ} (r : QRegister (2 * 58) N) : Circuit N := bellPre58Circuit.onRegister r
/-- Ambient relocation of `bellPost58Circuit` onto `rSys116`. -/
abbrev bellPost58On {N : ℕ} (r : QRegister (2 * 58) N) : Circuit N := bellPost58Circuit.onRegister r
/-- Ambient relocation of `czPairs58Circuit` onto `rSys116`. -/
abbrev czPairs58On {N : ℕ} (r : QRegister (2 * 58) N) : Circuit N := czPairs58Circuit.onRegister r

theorem prefixM_counts (M k : ℕ) (hk : k ≤ M) :
    (bellPrePrefix M k hk).count .T = 0 ∧ (bellPrePrefix M k hk).count .TOFF = 0 ∧
      (bellPostPrefix M k hk).count .T = 0 ∧ (bellPostPrefix M k hk).count .TOFF = 0 ∧
      (czPairsPrefixLoc M k hk).count .T = 0 ∧ (czPairsPrefixLoc M k hk).count .TOFF = 0 := by
  induction k with
  | zero => exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  | succ k ih =>
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := ih (by omega)
    simp [bellPrePrefix, bellPostPrefix, czPairsPrefixLoc, bellPrePair, bellPostPair,
      Circuit.CNOT, Circuit.H, Circuit.single, h1, h2, h3, h4, h5, h6]

@[simp] theorem bellPre58Circuit_count_t : bellPre58Circuit.count .T = 0 :=
  (prefixM_counts 58 58 le_rfl).1
@[simp] theorem bellPre58Circuit_count_toff : bellPre58Circuit.count .TOFF = 0 :=
  (prefixM_counts 58 58 le_rfl).2.1
@[simp] theorem bellPost58Circuit_count_t : bellPost58Circuit.count .T = 0 :=
  (prefixM_counts 58 58 le_rfl).2.2.1
@[simp] theorem bellPost58Circuit_count_toff : bellPost58Circuit.count .TOFF = 0 :=
  (prefixM_counts 58 58 le_rfl).2.2.2.1
@[simp] theorem czPairs58Circuit_count_t : czPairs58Circuit.count .T = 0 :=
  (prefixM_counts 58 58 le_rfl).2.2.2.2.1
@[simp] theorem czPairs58Circuit_count_toff : czPairs58Circuit.count .TOFF = 0 :=
  (prefixM_counts 58 58 le_rfl).2.2.2.2.2

theorem bellPre58Circuit_eq : bellPre58Circuit = bellPrePrefix 58 58 le_rfl := rfl
theorem bellPost58Circuit_eq : bellPost58Circuit = bellPostPrefix 58 58 le_rfl := rfl
theorem czPairs58Circuit_eq : czPairs58Circuit = czPairsPrefixLoc 58 58 le_rfl := rfl

theorem bellPostPrefix_mul_bellPrePrefix (M k : ℕ) (hk : k ≤ M) :
    (bellPostPrefix M k hk).eval * (bellPrePrefix M k hk).eval = 1 := by
  induction k with
  | zero => simp [bellPostPrefix, bellPrePrefix]
  | succ k ih =>
    let hk' : k ≤ M := Nat.le_of_succ_le hk
    let a : Wire (2 * M) := ⟨k, by omega⟩
    let b : Wire (2 * M) := ⟨M + k, by omega⟩
    let hab : a ≠ b := pairM_ne M k hk
    simp only [bellPostPrefix, bellPrePrefix, Circuit.eval_seq]
    calc ((bellPostPrefix M k hk').eval * (bellPostPair a b hab).eval) *
          ((bellPrePair a b hab).eval * (bellPrePrefix M k hk').eval)
        = (bellPostPrefix M k hk').eval * ((bellPostPair a b hab).eval *
            (bellPrePair a b hab).eval) * (bellPrePrefix M k hk').eval := by simp only [mul_assoc]
      _ = 1 := by rw [bellPostPair_mul_bellPrePair a b hab, mul_one, ih hk']

theorem bellPrePrefix_mul_bellPostPrefix (M : ℕ) :
    (bellPrePrefix M M le_rfl).eval * (bellPostPrefix M M le_rfl).eval = 1 := by
  rw [eq_inv_of_mul_eq_one_left (bellPostPrefix_mul_bellPrePrefix M M le_rfl), mul_inv_cancel]
theorem bellPostPrefix_onRegister_mul (M : ℕ) {N : ℕ} (r : QRegister (2 * M) N) :
    ((bellPostPrefix M M le_rfl).onRegister r).eval *
      ((bellPrePrefix M M le_rfl).onRegister r).eval = 1 := by
  rw [Circuit.eval_onRegister, Circuit.eval_onRegister, ← r.embedUnitary_mul,
    bellPostPrefix_mul_bellPrePrefix M M le_rfl, r.embedUnitary_one]
theorem bellPrePrefix_onRegister_mul (M : ℕ) {N : ℕ} (r : QRegister (2 * M) N) :
    ((bellPrePrefix M M le_rfl).onRegister r).eval *
      ((bellPostPrefix M M le_rfl).onRegister r).eval = 1 := by
  rw [Circuit.eval_onRegister, Circuit.eval_onRegister, ← r.embedUnitary_mul,
    bellPrePrefix_mul_bellPostPrefix M, r.embedUnitary_one]
theorem bellPost58On_mul_bellPre58On {N : ℕ} (r : QRegister (2 * 58) N) :
    (bellPost58On r).eval * (bellPre58On r).eval = 1 := by
  rw [bellPost58On, bellPre58On, bellPost58Circuit_eq, bellPre58Circuit_eq]
  exact bellPostPrefix_onRegister_mul 58 r
theorem bellPre58On_mul_bellPost58On {N : ℕ} (r : QRegister (2 * 58) N) :
    (bellPre58On r).eval * (bellPost58On r).eval = 1 := by
  rw [bellPre58On, bellPost58On, bellPre58Circuit_eq, bellPost58Circuit_eq]
  exact bellPrePrefix_onRegister_mul 58 r

theorem pair_support_sub {N : ℕ} (a b : Wire N) (hab : a ≠ b) :
    (bellPrePair a b hab).support ⊆ {a, b} ∧ (bellPostPair a b hab).support ⊆ {a, b} ∧
      (czCircuit a b hab).support ⊆ {a, b} := by
  refine ⟨?_, ?_, ?_⟩ <;> intro w hw <;>
    simp [bellPrePair, bellPostPair, czCircuit, Circuit.H, Circuit.single] at hw ⊢ <;> tauto

theorem prefixM_support_lt (M k : ℕ) (hk : k ≤ M) (w : Wire (2 * M))
    (hw : w ∈ (bellPostPrefix M k hk).support ∪ (czPairsPrefixLoc M k hk).support) :
    w.val < k ∨ (M ≤ w.val ∧ w.val < M + k) := by
  induction k with
  | zero => simp [bellPostPrefix, czPairsPrefixLoc] at hw
  | succ k ih =>
    have hsub := pair_support_sub ⟨k, by omega⟩ ⟨M + k, by omega⟩ (pairM_ne M k hk)
    simp only [bellPostPrefix, czPairsPrefixLoc, Circuit.support_seq, Finset.mem_union] at hw
    rcases hw with (hw | hw) | (hw | hw)
    · have := hsub.2.1 hw; simp only [Finset.mem_insert, Finset.mem_singleton] at this
      rcases this with rfl | rfl <;> dsimp <;> omega
    · rcases ih (by omega) (Finset.mem_union_left _ hw) with h | h <;> omega
    · rcases ih (by omega) (Finset.mem_union_right _ hw) with h | h <;> omega
    · have := hsub.2.2 hw; simp only [Finset.mem_insert, Finset.mem_singleton] at this
      rcases this with rfl | rfl <;> dsimp <;> omega

theorem bellPostPrefix_czPairsPrefix_bellPrePrefix_eval (M : ℕ) :
    (bellPostPrefix M M le_rfl).eval * (czPairsPrefixLoc M M le_rfl).eval *
        (bellPrePrefix M M le_rfl).eval = Operator.permutationUnitary (spinSwapEquiv M) := by
  have hpref : ∀ (k : ℕ) (hk : k ≤ M) (β : BitAssignment (2 * M)),
      ((bellPostPrefix M k hk).eval * (czPairsPrefixLoc M k hk).eval *
        (bellPrePrefix M k hk).eval).1.mulVec (ket β) =
        ket (fun w ↦ β (spinSwapPrefixWireMap M k hk w)) := by
    intro k hk; induction k with
    | zero =>
      intro β; simp only [bellPostPrefix, czPairsPrefixLoc, bellPrePrefix, Circuit.eval_identity,
        mul_one, Submonoid.coe_one, Matrix.one_mulVec]
      congr 1; funext w; unfold spinSwapPrefixWireMap
      rw [dite_eq_right (by omega), dite_eq_right (by omega)]
    | succ k ih =>
      intro β
      let hk' : k ≤ M := Nat.le_of_succ_le hk
      let a : Wire (2 * M) := ⟨k, by omega⟩
      let b : Wire (2 * M) := ⟨M + k, by omega⟩
      have hab : a ≠ b := pairM_ne M k hk
      have hsub := pair_support_sub a b hab
      have hdisj (c₁ c₂ : Circuit (2 * M))
          (hc₁ : c₁.support ⊆ (bellPostPrefix M k hk').support ∪ (czPairsPrefixLoc M k hk').support)
          (hc₂ : c₂.support ⊆ {a, b}) : c₁.eval * c₂.eval = c₂.eval * c₁.eval := by
        refine circuit_eval_comm_of_disjoint c₁ c₂ (Finset.disjoint_left.mpr fun w hw₁ hw₂ ↦ ?_)
        have hlt := prefixM_support_lt M k hk' w (hc₁ hw₁)
        have habw := hc₂ hw₂; simp only [Finset.mem_insert, Finset.mem_singleton] at habw
        rcases habw with rfl | rfl <;> dsimp [a, b] at hlt <;> omega
      let Upost := (bellPostPrefix M k hk').eval
      let Ucz := (czPairsPrefixLoc M k hk').eval
      let Upre := (bellPrePrefix M k hk').eval
      let upost := (bellPostPair a b hab).eval
      let ucz := (czCircuit a b hab).eval
      let upre := (bellPrePair a b hab).eval
      have hcomm1 : Ucz * upre = upre * Ucz :=
        hdisj (czPairsPrefixLoc M k hk') (bellPrePair a b hab) Finset.subset_union_right hsub.1
      have hcomm2 : Upost * (upost * ucz * upre) = (upost * ucz * upre) * Upost := by
        have h := hdisj (bellPostPrefix M k hk')
          (bellPrePair a b hab ;;ᶜ czCircuit a b hab ;;ᶜ bellPostPair a b hab)
          Finset.subset_union_left (by
            rw [Circuit.support_seq, Circuit.support_seq]
            exact Finset.union_subset hsub.1 (Finset.union_subset hsub.2.2 hsub.2.1))
        simpa only [Circuit.eval_seq] using h
      have halg : (bellPostPrefix M (k + 1) hk).eval * (czPairsPrefixLoc M (k + 1) hk).eval *
          (bellPrePrefix M (k + 1) hk).eval = (upost * ucz * upre) * (Upost * Ucz * Upre) := by
        simp only [bellPostPrefix, czPairsPrefixLoc, bellPrePrefix, Circuit.eval_seq]
        calc (Upost * upost) * (ucz * Ucz) * (upre * Upre)
            = Upost * upost * ucz * (Ucz * upre) * Upre := by simp only [mul_assoc]
          _ = (Upost * (upost * ucz * upre)) * (Ucz * Upre) := by rw [hcomm1]; simp only [mul_assoc]
          _ = (upost * ucz * upre) * (Upost * Ucz * Upre) := by rw [hcomm2]; simp only [mul_assoc]
      rw [halg, Submonoid.coe_mul, ← Matrix.mulVec_mulVec, ih hk' β]
      simp only [upost, ucz, upre, Submonoid.coe_mul, ← Matrix.mulVec_mulVec]
      rw [bellPostPair_cz_bellPrePair_ket]; congr 1; funext w
      have ha0 : spinSwapPrefixWireMap M k hk' a = a := by
        unfold spinSwapPrefixWireMap
        rw [dite_eq_right (by dsimp [a]; omega), dite_eq_right (by dsimp [a]; omega)]
      have hb0 : spinSwapPrefixWireMap M k hk' b = b := by
        unfold spinSwapPrefixWireMap
        rw [dite_eq_right (by dsimp [b]; omega), dite_eq_right (by dsimp [b]; omega)]
      by_cases hwb : w = b
      · subst hwb; rw [Function.update_self, ha0]; unfold spinSwapPrefixWireMap
        rw [dite_eq_right (by dsimp [b]; omega), dite_eq_left (by dsimp [b]; omega)]
        congr 2; ext; dsimp [a, b]; omega
      · rw [Function.update_of_ne hwb]
        by_cases hwa : w = a
        · subst hwa; rw [Function.update_self, hb0]; unfold spinSwapPrefixWireMap
          rw [dite_eq_left (by dsimp [a]; omega)]
        · rw [Function.update_of_ne hwa]
          have hna : w.val ≠ k := fun hv ↦ hwa (Fin.ext hv)
          have hnb : w.val ≠ M + k := fun hv ↦ hwb (Fin.ext hv)
          by_cases h1 : w.val < k
          · have h1' : w.val < k + 1 := by omega
            congr 1; simp only [spinSwapPrefixWireMap, h1, h1', ↓reduceDIte]
          · have h1' : ¬w.val < k + 1 := by omega
            congr 1; by_cases h2 : M ≤ w.val ∧ w.val < M + k
            · have h2' : M ≤ w.val ∧ w.val < M + (k + 1) := by omega
              simp only [spinSwapPrefixWireMap, h1, h1', h2, h2', ↓reduceDIte]
            · have h2' : ¬(M ≤ w.val ∧ w.val < M + (k + 1)) := by omega
              simp only [spinSwapPrefixWireMap, h1, h1', h2, h2', ↓reduceDIte]
  apply Subtype.ext; apply matrix_ext_ket; intro β
  rw [hpref M le_rfl β, ket, basisState, Operator.permutationUnitary_mulVec_single, single_eq_ket]
  congr 1; funext w
  simp only [Equiv.apply_symm_apply]; rfl

theorem embedUnitary_spinSwapEquiv_eq_onRegister (M : ℕ) {N : ℕ} (r : QRegister (2 * M) N) :
    r.embedUnitary (Operator.permutationUnitary (spinSwapEquiv M)) =
      ((bellPostPrefix M M le_rfl).onRegister r).eval *
        ((czPairsPrefixLoc M M le_rfl).onRegister r).eval *
        ((bellPrePrefix M M le_rfl).onRegister r).eval := by
  rw [← bellPostPrefix_czPairsPrefix_bellPrePrefix_eval M, r.embedUnitary_mul, r.embedUnitary_mul,
    ← Circuit.eval_onRegister, ← Circuit.eval_onRegister, ← Circuit.eval_onRegister]
theorem embedUnitary_spinSwapEquiv58_eq {N : ℕ} (r : QRegister (2 * 58) N) :
    r.embedUnitary (Operator.permutationUnitary (spinSwapEquiv 58)) =
      (bellPost58On r).eval * (czPairs58On r).eval * (bellPre58On r).eval := by
  rw [bellPost58On, czPairs58On, bellPre58On, bellPost58Circuit_eq, czPairs58Circuit_eq,
    bellPre58Circuit_eq]
  exact embedUnitary_spinSwapEquiv_eq_onRegister 58 r

attribute [irreducible] bellPre58Circuit bellPost58Circuit

/-! ## Section 3: Singlet-Parity Isomorphism `bellIso58Unitary` & `cswap58Unitary` Conjugation -/

theorem ne_of_disjoint_singleton {N k : ℕ} {r : QRegister k N} {w : Wire N}
    (h : r.DisjointWires (QRegister.singleton w)) (i : Fin k) : r i ≠ w := h.ne i 0

/-- Specification-only prefix of `k ≤ 58` Toffoli gates accumulating orbital-pair ANDs. -/
def toffPairsPrefix {N : ℕ} (rSys116 : QRegister (2 * 58) N) (wBellDst : Wire N)
    (hSysDst : rSys116.DisjointWires (QRegister.singleton wBellDst)) : (k : ℕ) → k ≤ 58 → Circuit N
  | 0, _ => .identity
  | k + 1, hk =>
    toffPairsPrefix rSys116 wBellDst hSysDst k (by omega) ;;ᶜ
      Circuit.TOFF (rSys116 ⟨k, by omega⟩) (rSys116 ⟨58 + k, by omega⟩) wBellDst
        (rSys116.wires.injective.ne (pair58_ne k hk))
        (ne_of_disjoint_singleton hSysDst ⟨k, by omega⟩)
        (ne_of_disjoint_singleton hSysDst ⟨58 + k, by omega⟩)
/-- Specification-only 58-Toffoli cascade XORing singlet parity into `wBellDst`. -/
def toffPairs58Circuit {N : ℕ} (rSys116 : QRegister (2 * 58) N) (wBellDst : Wire N)
    (hSysDst : rSys116.DisjointWires (QRegister.singleton wBellDst)) : Circuit N :=
  toffPairsPrefix rSys116 wBellDst hSysDst 58 le_rfl
/-- Specification-only static circuit for the Bell-singlet basis isomorphism `V_iso`. -/
def bellIso58Circuit {N : ℕ} (rSys116 : QRegister (2 * 58) N) (wBellDst : Wire N)
    (hSysDst : rSys116.DisjointWires (QRegister.singleton wBellDst)) : Circuit N :=
  bellPre58On rSys116 ;;ᶜ toffPairs58Circuit rSys116 wBellDst hSysDst
/-- Bell-singlet basis isomorphism unitary `V_iso` supported on `rSys116.image ∪ {wBellDst}`. -/
noncomputable def bellIso58Unitary {N : ℕ} (rSys116 : QRegister (2 * 58) N) (wBellDst : Wire N)
    (hSysDst : rSys116.DisjointWires (QRegister.singleton wBellDst)) : Unitary (2 ^ N) :=
  (bellIso58Circuit rSys116 wBellDst hSysDst).eval
/-- Ambient 58-pair controlled-SWAP unitary controlled by `wSig` on `rSys116`. -/
noncomputable def cswap58Unitary {N : ℕ} (wSig : Wire N) (rSys116 : QRegister (2 * 58) N)
    (hSigSys : (QRegister.singleton wSig).DisjointWires rSys116) : Unitary (2 ^ N) :=
  muxUnitary (QRegister.singleton wSig) rSys116 hSigSys
    (fun σ ↦ if σ = 0 then 1 else Operator.permutationUnitary (spinSwapEquiv 58))

theorem cswap58Unitary_eq_embed_cswapBlockCircuit {N : ℕ} (wSig : Wire N)
    (rSys116 : QRegister (2 * 58) N) (hSigSys : (QRegister.singleton wSig).DisjointWires rSys116) :
    ((QRegister.singleton wSig).concat rSys116 hSigSys).embedUnitary
        (cswapBlockCircuit 58).eval = cswap58Unitary wSig rSys116 hSigSys := by
  let rPlace := (QRegister.singleton wSig).concat rSys116 hSigSys
  have hc0 : rPlace.compose (QRegister.singleton 0) = QRegister.singleton wSig := by
    ext i; fin_cases i
    change ((QRegister.singleton wSig).concat rSys116 hSigSys (Fin.castAdd (2 * 58) 0)).val =
      ((QRegister.singleton wSig) 0).val
    rw [QRegister.concat_apply_left]
  have hc1 : rPlace.compose (QRegister.block 1 (2 * 58) (by omega)) = rSys116 := by
    ext j
    have hj : QRegister.block 1 (2 * 58) (by omega : 1 + 2 * 58 ≤ 1 + 2 * 58) j =
        Fin.natAdd 1 j := by ext; simp
    change ((QRegister.singleton wSig).concat rSys116 hSigSys
      (QRegister.block 1 (2 * 58) (by omega) j)).val = (rSys116 j).val
    rw [hj, QRegister.concat_apply_right]
  apply Subtype.ext; rw [cswapBlockCircuit_eval, QRegister.embedUnitary_val]
  dsimp only [cswap58Unitary, muxUnitary]; rw [rPlace.embedMatrix_sum]
  refine Finset.sum_congr rfl fun c _ ↦ ?_
  rw [QRegister.embedMatrix_mul]; unfold QRegister.basisOutcomeProjector
  rw [← QRegister.embedMatrix_compose, hc0, ← QRegister.embedMatrix_compose, hc1]

theorem toffPairs58Circuit_support_subset {N : ℕ} (rSys116 : QRegister (2 * 58) N)
    (wBellDst : Wire N) (hSysDst : rSys116.DisjointWires (QRegister.singleton wBellDst)) :
    (toffPairs58Circuit rSys116 wBellDst hSysDst).support ⊆ rSys116.image ∪ {wBellDst} := by
  suffices hToff : ∀ (k : ℕ) (hk : k ≤ 58),
      (toffPairsPrefix rSys116 wBellDst hSysDst k hk).support ⊆ rSys116.image ∪ {wBellDst} from
    hToff 58 le_rfl
  intro k hk; induction k with
  | zero => simp [toffPairsPrefix]
  | succ k ih =>
    simp only [toffPairsPrefix, Circuit.support_seq, Circuit.support_toffoli]
    refine Finset.union_subset (ih (by omega)) (fun w hw ↦ ?_)
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union] at hw ⊢
    rcases hw with rfl | rfl | rfl
    · exact Or.inl ((QRegister.mem_image rSys116 _).mpr ⟨⟨k, by omega⟩, rfl⟩)
    · exact Or.inl ((QRegister.mem_image rSys116 _).mpr ⟨⟨58 + k, by omega⟩, rfl⟩)
    · exact Or.inr rfl

theorem bellIso58Circuit_support_subset {N : ℕ} (rSys116 : QRegister (2 * 58) N)
    (wBellDst : Wire N) (hSysDst : rSys116.DisjointWires (QRegister.singleton wBellDst)) :
    (bellIso58Circuit rSys116 wBellDst hSysDst).support ⊆ rSys116.image ∪ {wBellDst} :=
  Finset.union_subset
    ((Circuit.support_onRegister_subset rSys116 bellPre58Circuit).trans Finset.subset_union_left)
    (toffPairs58Circuit_support_subset rSys116 wBellDst hSysDst)

/-- `ZMod 2` orbital-pair singlet parity `∑_{p < k} β (rSys116 p) * β (rSys116 (58 + p))`. -/
def singletParityPrefix {N : ℕ} (rSys116 : QRegister (2 * 58) N)
    (β : BitAssignment N) : (k : ℕ) → k ≤ 58 → ZMod 2
  | 0, _ => 0
  | k + 1, _ =>
    singletParityPrefix rSys116 β k (by omega) +
      β (rSys116 ⟨k, by omega⟩) * β (rSys116 ⟨58 + k, by omega⟩)
/-- Full 58-orbital `ZMod 2` singlet parity on `rSys116`. -/
def singletParity58 {N : ℕ} (rSys116 : QRegister (2 * 58) N) (β : BitAssignment N) : ZMod 2 :=
  singletParityPrefix rSys116 β 58 le_rfl
theorem singletParityPrefix_update_dst {N : ℕ} (rSys116 : QRegister (2 * 58) N) (wBellDst : Wire N)
    (hSysDst : rSys116.DisjointWires (QRegister.singleton wBellDst)) (β : BitAssignment N)
    (val : ZMod 2) (k : ℕ) (hk : k ≤ 58) :
    singletParityPrefix rSys116 (Function.update β wBellDst val) k hk =
      singletParityPrefix rSys116 β k hk := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [singletParityPrefix, ih (by omega),
      Function.update_of_ne (ne_of_disjoint_singleton hSysDst ⟨k, by omega⟩),
      Function.update_of_ne (ne_of_disjoint_singleton hSysDst ⟨58 + k, by omega⟩)]
theorem singletParity58_update_dst {N : ℕ} (rSys116 : QRegister (2 * 58) N) (wBellDst : Wire N)
    (hSysDst : rSys116.DisjointWires (QRegister.singleton wBellDst)) (β : BitAssignment N)
    (val : ZMod 2) :
    singletParity58 rSys116 (Function.update β wBellDst val) = singletParity58 rSys116 β :=
  singletParityPrefix_update_dst rSys116 wBellDst hSysDst β val 58 le_rfl
theorem toffPairsPrefix_ket {N : ℕ} (rSys116 : QRegister (2 * 58) N) (wBellDst : Wire N)
    (hSysDst : rSys116.DisjointWires (QRegister.singleton wBellDst)) (k : ℕ) (hk : k ≤ 58)
    (β : BitAssignment N) :
    (toffPairsPrefix rSys116 wBellDst hSysDst k hk).eval.1.mulVec (ket β) =
      ket (Function.update β wBellDst (β wBellDst + singletParityPrefix rSys116 β k hk)) := by
  induction k with
  | zero => rw [toffPairsPrefix, singletParityPrefix, ket_identity, add_zero,
      Function.update_eq_self]
  | succ k ih =>
    rw [toffPairsPrefix, eval_seq_mulVec, ih (by omega), ket_TOFF, Function.update_self,
      Function.update_of_ne (ne_of_disjoint_singleton hSysDst ⟨k, by omega⟩),
      Function.update_of_ne (ne_of_disjoint_singleton hSysDst ⟨58 + k, by omega⟩),
      Function.update_idem, singletParityPrefix, add_assoc]
theorem toffPairs58_ket {N : ℕ} (rSys116 : QRegister (2 * 58) N) (wBellDst : Wire N)
    (hSysDst : rSys116.DisjointWires (QRegister.singleton wBellDst)) (β : BitAssignment N) :
    (toffPairs58Circuit rSys116 wBellDst hSysDst).eval.1.mulVec (ket β) =
      ket (Function.update β wBellDst (β wBellDst + singletParity58 rSys116 β)) :=
  toffPairsPrefix_ket rSys116 wBellDst hSysDst 58 le_rfl β
theorem onRegister_czCircuit {N m : ℕ} (r : QRegister m N) (a b : Wire m) (hab : a ≠ b) :
    (czCircuit a b hab).onRegister r = czCircuit (r a) (r b) (r.wires.injective.ne hab) := by
  have h1 : r.compose (QRegister.singleton b) = QRegister.singleton (r b) := by
    ext i; fin_cases i; rfl
  have h2 : r.compose (QRegister.pair a b hab) =
      QRegister.pair (r a) (r b) (r.wires.injective.ne hab) := by ext i; fin_cases i <;> rfl
  simp [czCircuit, Circuit.H, Circuit.single, Circuit.CNOT, h1, h2]
theorem czPairsPrefix_onRegister_ket {N : ℕ} (rSys116 : QRegister (2 * 58) N)
    (k : ℕ) (hk : k ≤ 58) (β : BitAssignment N) :
    ((czPairsPrefixLoc 58 k hk).onRegister rSys116).eval.1.mulVec (ket β) =
      bitSign (singletParityPrefix rSys116 β k hk) • ket β := by
  induction k with
  | zero =>
    rw [czPairsPrefixLoc, Circuit.onRegister_identity, ket_identity, singletParityPrefix]
    exact (one_smul ℂ (ket β)).symm
  | succ k ih =>
    simp only [czPairsPrefixLoc, Circuit.onRegister_seq, eval_seq_mulVec, ih (by omega),
      Matrix.mulVec_smul, onRegister_czCircuit, ket_czCircuit, smul_smul, singletParityPrefix,
      bitSign_add]
theorem czPairs58On_ket {N : ℕ} (rSys116 : QRegister (2 * 58) N) (β : BitAssignment N) :
    (czPairs58On rSys116).eval.1.mulVec (ket β) = bitSign (singletParity58 rSys116 β) • ket β :=
  czPairsPrefix_onRegister_ket rSys116 58 le_rfl β
theorem toffPairs58_mul_self {N : ℕ} (rSys116 : QRegister (2 * 58) N) (wBellDst : Wire N)
    (hSysDst : rSys116.DisjointWires (QRegister.singleton wBellDst)) :
    (toffPairs58Circuit rSys116 wBellDst hSysDst).eval *
      (toffPairs58Circuit rSys116 wBellDst hSysDst).eval = 1 := by
  apply Subtype.ext; apply matrix_ext_ket; intro β
  simp only [Submonoid.coe_mul, Submonoid.coe_one, ← Matrix.mulVec_mulVec,
    Matrix.one_mulVec, toffPairs58_ket, Function.update_self, Function.update_idem,
    singletParity58_update_dst rSys116 wBellDst hSysDst]
  have hadd : β wBellDst + singletParity58 rSys116 β + singletParity58 rSys116 β = β wBellDst := by
    rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
  rw [hadd, Function.update_eq_self]

theorem toffPairs58_conj_z {N : ℕ} (rSys116 : QRegister (2 * 58) N) (wBellDst : Wire N)
    (hSysDst : rSys116.DisjointWires (QRegister.singleton wBellDst)) :
    (toffPairs58Circuit rSys116 wBellDst hSysDst).eval * (Circuit.Z wBellDst).eval *
      (toffPairs58Circuit rSys116 wBellDst hSysDst).eval =
      (Circuit.Z wBellDst).eval * (czPairs58On rSys116).eval := by
  apply Subtype.ext; apply matrix_ext_ket; intro β
  simp only [Submonoid.coe_mul, ← Matrix.mulVec_mulVec, toffPairs58_ket, ket_Z, Matrix.mulVec_smul,
    czPairs58On_ket, Function.update_self, Function.update_idem,
    singletParity58_update_dst rSys116 wBellDst hSysDst, smul_smul, bitSign_add]
  have hadd : β wBellDst + singletParity58 rSys116 β + singletParity58 rSys116 β = β wBellDst := by
    rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
  rw [hadd, Function.update_eq_self, mul_comm (bitSign (β wBellDst))]

attribute [irreducible] czPairs58Circuit toffPairs58Circuit singletParity58

theorem z_mul_bellIso58Unitary {N : ℕ} (rSys116 : QRegister (2 * 58) N)
    (wBellDst : Wire N) (hSysDst : rSys116.DisjointWires (QRegister.singleton wBellDst)) :
    (Circuit.Z wBellDst).eval * bellIso58Unitary rSys116 wBellDst hSysDst =
      bellIso58Unitary rSys116 wBellDst hSysDst * (Circuit.Z wBellDst).eval *
        rSys116.embedUnitary (Operator.permutationUnitary (spinSwapEquiv 58)) := by
  have hCommPreZ : (bellPre58On rSys116).eval * (Circuit.Z wBellDst).eval =
      (Circuit.Z wBellDst).eval * (bellPre58On rSys116).eval := by
    refine circuit_eval_comm_of_disjoint _ _ (Finset.disjoint_left.mpr fun w hw₁ hw₂ ↦ ?_)
    obtain ⟨i, rfl⟩ := (QRegister.mem_image rSys116 w).mp
      (Circuit.support_onRegister_subset rSys116 bellPre58Circuit hw₁)
    rw [Circuit.Z, Circuit.support_single, Finset.mem_singleton] at hw₂
    exact hSysDst.ne i 0 hw₂
  have hPrePost := bellPre58On_mul_bellPost58On rSys116
  symm; rw [bellIso58Unitary, bellIso58Circuit, Circuit.eval_seq, embedUnitary_spinSwapEquiv58_eq]
  calc (toffPairs58Circuit rSys116 wBellDst hSysDst).eval * (bellPre58On rSys116).eval *
        (Circuit.Z wBellDst).eval *
        ((bellPost58On rSys116).eval * (czPairs58On rSys116).eval * (bellPre58On rSys116).eval)
      = (toffPairs58Circuit rSys116 wBellDst hSysDst).eval *
          ((bellPre58On rSys116).eval * (Circuit.Z wBellDst).eval) *
          (bellPost58On rSys116).eval * (czPairs58On rSys116).eval *
          (bellPre58On rSys116).eval := by simp only [mul_assoc]
    _ = (toffPairs58Circuit rSys116 wBellDst hSysDst).eval * (Circuit.Z wBellDst).eval *
          ((bellPre58On rSys116).eval * (bellPost58On rSys116).eval) *
          (czPairs58On rSys116).eval * (bellPre58On rSys116).eval := by
        rw [hCommPreZ]; simp only [mul_assoc]
    _ = (toffPairs58Circuit rSys116 wBellDst hSysDst).eval *
          ((Circuit.Z wBellDst).eval * (czPairs58On rSys116).eval) *
          (bellPre58On rSys116).eval := by rw [hPrePost, mul_one]; simp only [mul_assoc]
    _ = ((toffPairs58Circuit rSys116 wBellDst hSysDst).eval *
          (toffPairs58Circuit rSys116 wBellDst hSysDst).eval) * (Circuit.Z wBellDst).eval *
          ((toffPairs58Circuit rSys116 wBellDst hSysDst).eval * (bellPre58On rSys116).eval) := by
        rw [← toffPairs58_conj_z rSys116 wBellDst hSysDst]; simp only [mul_assoc]
    _ = (Circuit.Z wBellDst).eval *
          ((toffPairs58Circuit rSys116 wBellDst hSysDst).eval * (bellPre58On rSys116).eval) := by
        rw [toffPairs58_mul_self, one_mul]

theorem muxUnitary_singleton_val {N k : ℕ} (w : Wire N) (r : QRegister k N)
    (h : (QRegister.singleton w).DisjointWires r) (U₁ : Unitary (2 ^ k)) :
    (muxUnitary (QRegister.singleton w) r h (fun σ ↦ if σ = 0 then 1 else U₁)).1 =
      (QRegister.singleton w).basisOutcomeProjector 0 +
        (QRegister.singleton w).basisOutcomeProjector 1 * (r.embedUnitary U₁).1 := by
  have hsum (f : Fin (2 ^ 1) → Operator (2 ^ N)) : ∑ c, f c = f 0 + f 1 := Fin.sum_univ_two f
  dsimp only [muxUnitary]; rw [hsum, QRegister.embedUnitary_val]
  simp only [↓reduceIte, Fin.isValue, one_ne_zero, Submonoid.coe_one, r.embedMatrix_one, mul_one]

theorem czCircuit_mul_bellIso58Unitary {N : ℕ} (wSig : Wire N) (rSys116 : QRegister (2 * 58) N)
    (wBellDst : Wire N) (hSysDst : rSys116.DisjointWires (QRegister.singleton wBellDst))
    (hSigSys : (QRegister.singleton wSig).DisjointWires rSys116) (hSigDst : wSig ≠ wBellDst) :
    (czCircuit wSig wBellDst hSigDst).eval * bellIso58Unitary rSys116 wBellDst hSysDst =
      bellIso58Unitary rSys116 wBellDst hSysDst * (czCircuit wSig wBellDst hSigDst).eval *
        cswap58Unitary wSig rSys116 hSigSys := by
  let P₀ := (QRegister.singleton wSig).basisOutcomeProjector 0
  let P₁ := (QRegister.singleton wSig).basisOutcomeProjector 1
  let V := bellIso58Unitary rSys116 wBellDst hSysDst
  let Z := (Circuit.Z wBellDst).eval
  set Usw : Unitary (2 ^ N) := rSys116.embedUnitary (Operator.permutationUnitary (spinSwapEquiv 58))
  have hCZ : (czCircuit wSig wBellDst hSigDst).eval.1 = P₀ + P₁ * Z.1 := by
    apply matrix_ext_ket; intro β
    simp only [P₀, P₁, Z, Matrix.add_mulVec, ← Matrix.mulVec_mulVec, ket_czCircuit, ket_Z,
      Matrix.mulVec_smul, singleton_projector_zero_mulVec_ket, singleton_projector_one_mulVec_ket]
    rcases bit_cases (β wSig) with h | h <;> simp [h]
  have hCS : (cswap58Unitary wSig rSys116 hSigSys).1 = P₀ + P₁ * Usw.1 := by
    rw [cswap58Unitary]
    exact muxUnitary_singleton_val wSig rSys116 hSigSys
      (Operator.permutationUnitary (spinSwapEquiv 58))
  have hDisjIso : Disjoint (QRegister.singleton wSig).image
      (bellIso58Circuit rSys116 wBellDst hSysDst).support := by
    refine Finset.disjoint_left.mpr fun w hw₁ hw₂ ↦ ?_
    rw [QRegister.image_singleton, Finset.mem_singleton] at hw₁; subst w
    rcases Finset.mem_union.mp (bellIso58Circuit_support_subset rSys116 wBellDst hSysDst hw₂) with
      h | h
    · obtain ⟨i, hi⟩ := (QRegister.mem_image rSys116 wSig).mp h
      exact hSigSys.ne 0 i hi.symm
    · exact hSigDst (Finset.mem_singleton.mp h)
  have hDisjZ : Disjoint (QRegister.singleton wSig).image (Circuit.Z wBellDst).support := by
    simp [Circuit.Z, hSigDst]
  have hPV (c : Fin 2) : (QRegister.singleton wSig).basisOutcomeProjector c * V.1 =
      V.1 * (QRegister.singleton wSig).basisOutcomeProjector c := by
    dsimp only [V]; rw [QRegister.basisOutcomeProjector, bellIso58Unitary]
    exact embedMatrix_comm_circuit_of_disjoint (QRegister.singleton wSig) (compProj c)
      (bellIso58Circuit rSys116 wBellDst hSysDst) hDisjIso
  have hPZ (c : Fin 2) : (QRegister.singleton wSig).basisOutcomeProjector c * Z.1 =
      Z.1 * (QRegister.singleton wSig).basisOutcomeProjector c := by
    dsimp only [Z]; rw [QRegister.basisOutcomeProjector]
    exact embedMatrix_comm_circuit_of_disjoint (QRegister.singleton wSig) (compProj c)
      (Circuit.Z wBellDst) hDisjZ
  have h10 : (1 : Fin (2 ^ 1)) ≠ 0 := one_ne_zero
  have hP01 : P₀ * P₁ = 0 ∧ P₁ * P₀ = 0 := by
    refine ⟨?_, ?_⟩ <;> dsimp only [P₀, P₁] <;>
      rw [QRegister.basisOutcomeProjector, QRegister.basisOutcomeProjector,
        ← QRegister.embedMatrix_mul]
    · rw [compProj_mul_of_ne h10.symm, QRegister.embedMatrix_zero]
    · rw [compProj_mul_of_ne h10, QRegister.embedMatrix_zero]
  have hZV : Z.1 * V.1 = V.1 * Z.1 * Usw.1 :=
    congrArg Subtype.val (z_mul_bellIso58Unitary rSys116 wBellDst hSysDst)
  have hMid : (P₀ + P₁ * Z.1) * (P₀ + P₁ * Usw.1) = P₀ + P₁ * Z.1 * Usw.1 := by
    have hZ0 : Z.1 * P₀ = P₀ * Z.1 := (hPZ 0).symm
    have hZ1 : Z.1 * P₁ = P₁ * Z.1 := (hPZ 1).symm
    calc (P₀ + P₁ * Z.1) * (P₀ + P₁ * Usw.1)
        = P₀ * P₀ + (P₀ * P₁) * Usw.1 + P₁ * (Z.1 * P₀) + P₁ * (Z.1 * P₁) * Usw.1 := by
          simp only [add_mul, mul_add, Matrix.mul_assoc]; abel
      _ = P₀ + P₁ * Z.1 * Usw.1 := by
          rw [hZ0, hZ1, ← Matrix.mul_assoc P₁ P₀, ← Matrix.mul_assoc P₁ P₁, hP01.1, hP01.2,
            QRegister.basisOutcomeProjector_mul_self, QRegister.basisOutcomeProjector_mul_self]
          simp only [zero_mul, add_zero]; rfl
  have h1 : P₁ * Z.1 * V.1 = V.1 * (P₁ * Z.1 * Usw.1) := by
    rw [Matrix.mul_assoc P₁ Z.1 V.1, hZV, ← Matrix.mul_assoc P₁, ← Matrix.mul_assoc P₁, hPV 1]
    simp only [Matrix.mul_assoc]; rfl
  apply Subtype.ext; simp only [Submonoid.coe_mul]
  rw [Matrix.mul_assoc V.1, hCZ, hCS, hMid, add_mul, mul_add, hPV 0, h1]

theorem cswap58_comm_zeroProjOn_singleton {N : ℕ} (wSig : Wire N)
    (rSys116 : QRegister (2 * 58) N) (wBellDst : Wire N)
    (hSysDst : rSys116.DisjointWires (QRegister.singleton wBellDst))
    (hSigSys : (QRegister.singleton wSig).DisjointWires rSys116) (hSigDst : wSig ≠ wBellDst) :
    zeroProjOn {wBellDst} * (cswap58Unitary wSig rSys116 hSigSys).1 =
      (cswap58Unitary wSig rSys116 hSigSys).1 * zeroProjOn {wBellDst} := by
  let rPlace := (QRegister.singleton wSig).concat rSys116 hSigSys
  rw [← cswap58Unitary_eq_embed_cswapBlockCircuit, ← Circuit.eval_onRegister,
    ← QRegister.image_singleton wBellDst, ← basisOutcomeProjector_zero_eq_zeroProjOn]
  refine embedMatrix_comm_circuit_of_disjoint _ (compProj 0) _
    (Finset.disjoint_left.mpr fun w hw₁ hw₂ ↦ ?_)
  rw [QRegister.image_singleton, Finset.mem_singleton] at hw₁; subst w
  have hmem := (QRegister.image_concat _ _ hSigSys) ▸
    Circuit.support_onRegister_subset rPlace (cswapBlockCircuit 58) hw₂
  rcases Finset.mem_union.mp hmem with h | h
  · rw [QRegister.image_singleton, Finset.mem_singleton] at h; exact hSigDst h.symm
  · obtain ⟨i, hi⟩ := (QRegister.mem_image rSys116 wBellDst).mp h; exact hSysDst.ne i 0 hi

theorem czCircuit_mul_bellIso_mul_zeroProjOn {N : ℕ} (wSig : Wire N)
    (rSys116 : QRegister (2 * 58) N) (wBellDst : Wire N)
    (hSysDst : rSys116.DisjointWires (QRegister.singleton wBellDst))
    (hSigSys : (QRegister.singleton wSig).DisjointWires rSys116) (hSigDst : wSig ≠ wBellDst) :
    ((czCircuit wSig wBellDst hSigDst).eval * bellIso58Unitary rSys116 wBellDst hSysDst).1 *
        zeroProjOn {wBellDst} =
      (bellIso58Unitary rSys116 wBellDst hSysDst * cswap58Unitary wSig rSys116 hSigSys).1 *
        zeroProjOn {wBellDst} := by
  have hCZ0 : (czCircuit wSig wBellDst hSigDst).eval.1 * zeroProjOn {wBellDst} =
      zeroProjOn {wBellDst} := by
    apply matrix_ext_ket; intro β
    simp only [← Matrix.mulVec_mulVec, zeroProjOn_mulVec_ket, Finset.mem_singleton, forall_eq]
    by_cases h0 : β wBellDst = 0
    · rw [ite_eq_left h0, ket_czCircuit, h0, mul_zero]; simp
    · rw [ite_eq_right h0, Matrix.mulVec_zero]
  rw [czCircuit_mul_bellIso58Unitary wSig rSys116 wBellDst hSysDst hSigSys hSigDst]
  simp only [Submonoid.coe_mul, Matrix.mul_assoc]
  rw [← cswap58_comm_zeroProjOn_singleton wSig rSys116 wBellDst hSysDst hSigSys hSigDst,
    ← Matrix.mul_assoc (czCircuit wSig wBellDst hSigDst).eval.1, hCZ0]

/-! ## Section 4: `dBellExit58Dyn` (`232 T`, `0 TOFF`, Step a) -/

theorem cleanRealizesSet_circuit_of_disjoint {Var : Type} [Fintype Var]
    [DecidableEq Var] {N : ℕ} [NeZero (2 ^ N)] (v : Var) (S : Finset (Wire N))
    (c : Circuit N) (hToff : c.count .TOFF = 0) (hDisj : Disjoint c.support S) :
    CleanRealizesSet v S c.eval (.circuit c) := by
  refine ⟨hToff,
    fun Θ hΘ σ val ↦ by simp only [DynamicCircuit.compile_circuit,
      DynamicCircuit.qc_wp_circuit_compile, qcWpQAssign, hΘ σ val],
    fun Θ _ ↦ by rw [DynamicCircuit.compile_circuit, DynamicCircuit.qc_wp_circuit_compile],
    fun Θ ↦ ?_⟩
  rw [wp_restrictZeroSet_of_disjoint (.circuit c) S hDisj Θ, SelectSwapQROM.restrictZeroSet_idem]

/-- Prefix of `k ≤ 58` 4-`T` `jonesToffoli` gates XORing singlet parity into `wBellDst`. -/
def jonesToffPairsPrefix {Var : Type} {N : ℕ} (v : Var)
    (rSys116 : QRegister (2 * 58) N) (wBellDst wBellTmp : Wire N)
    (hSysTmp : rSys116.DisjointWires (QRegister.singleton wBellTmp))
    (hDstTmp : wBellDst ≠ wBellTmp) : (k : ℕ) → k ≤ 58 → DynamicCircuit Var N
  | 0, _ => .identity
  | k + 1, hk =>
    .seq (jonesToffPairsPrefix v rSys116 wBellDst wBellTmp hSysTmp hDstTmp k (by omega))
      (DynamicCircuit.jonesToffoli v (rSys116 ⟨k, by omega⟩) (rSys116 ⟨58 + k, by omega⟩)
        wBellDst wBellTmp (rSys116.wires.injective.ne (pair58_ne k hk))
        (ne_of_disjoint_singleton hSysTmp ⟨k, by omega⟩)
        (ne_of_disjoint_singleton hSysTmp ⟨58 + k, by omega⟩) hDstTmp)

/-- 58-orbital 4-`T` `jonesToffoli` singlet-parity cascade (`232 T`, `0 TOFF`). -/
def jonesToffPairs58Dyn {Var : Type} {N : ℕ} (v : Var)
    (rSys116 : QRegister (2 * 58) N) (wBellDst wBellTmp : Wire N)
    (hSysTmp : rSys116.DisjointWires (QRegister.singleton wBellTmp))
    (hDstTmp : wBellDst ≠ wBellTmp) : DynamicCircuit Var N :=
  jonesToffPairsPrefix v rSys116 wBellDst wBellTmp hSysTmp hDstTmp 58 le_rfl

theorem jonesToffPairsPrefix_props {Var : Type} {N : ℕ} (v : Var)
    (rSys116 : QRegister (2 * 58) N) (wBellDst wBellTmp : Wire N)
    (hSysTmp : rSys116.DisjointWires (QRegister.singleton wBellTmp))
    (hDstTmp : wBellDst ≠ wBellTmp) (k : ℕ) (hk : k ≤ 58) :
    (jonesToffPairsPrefix v rSys116 wBellDst wBellTmp hSysTmp hDstTmp k hk).count .TOFF = 0 ∧
      (jonesToffPairsPrefix v rSys116 wBellDst wBellTmp hSysTmp hDstTmp k hk).count .T = 4 * k ∧
      (jonesToffPairsPrefix v rSys116 wBellDst wBellTmp hSysTmp hDstTmp k hk).support ⊆
        {wBellDst, wBellTmp} ∪ rSys116.image := by
  induction k with
  | zero => simp [jonesToffPairsPrefix]
  | succ k ih =>
    obtain ⟨hToff, hT, hSup⟩ := ih (by omega)
    refine ⟨by simp [jonesToffPairsPrefix, hToff],
      by simp [jonesToffPairsPrefix, hT]; omega, ?_⟩
    simp only [jonesToffPairsPrefix, DynamicCircuit.support_seq,
      DynamicCircuit.support_jonesToffoli]
    refine Finset.union_subset hSup (fun w hw ↦ ?_)
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union] at hw ⊢
    rcases hw with rfl | rfl | rfl | rfl
    · exact Or.inr ((QRegister.mem_image rSys116 _).mpr ⟨⟨k, by omega⟩, rfl⟩)
    · exact Or.inr ((QRegister.mem_image rSys116 _).mpr ⟨⟨58 + k, by omega⟩, rfl⟩)
    · exact Or.inl (Or.inl rfl)
    · exact Or.inl (Or.inr rfl)

@[simp] theorem jonesToffPairs58Dyn_count_toff {Var : Type} {N : ℕ} (v : Var)
    (rSys116 : QRegister (2 * 58) N) (wBellDst wBellTmp : Wire N)
    (hSysTmp : rSys116.DisjointWires (QRegister.singleton wBellTmp))
    (hDstTmp : wBellDst ≠ wBellTmp) :
    (jonesToffPairs58Dyn v rSys116 wBellDst wBellTmp hSysTmp hDstTmp).count .TOFF = 0 :=
  (jonesToffPairsPrefix_props v rSys116 wBellDst wBellTmp hSysTmp hDstTmp 58 le_rfl).1
@[simp] theorem jonesToffPairs58Dyn_count_t {Var : Type} {N : ℕ} (v : Var)
    (rSys116 : QRegister (2 * 58) N) (wBellDst wBellTmp : Wire N)
    (hSysTmp : rSys116.DisjointWires (QRegister.singleton wBellTmp))
    (hDstTmp : wBellDst ≠ wBellTmp) :
    (jonesToffPairs58Dyn v rSys116 wBellDst wBellTmp hSysTmp hDstTmp).count .T = 232 :=
  (jonesToffPairsPrefix_props v rSys116 wBellDst wBellTmp hSysTmp hDstTmp 58 le_rfl).2.1
theorem jonesToffPairs58Dyn_support_subset {Var : Type} {N : ℕ} (v : Var)
    (rSys116 : QRegister (2 * 58) N) (wBellDst wBellTmp : Wire N)
    (hSysTmp : rSys116.DisjointWires (QRegister.singleton wBellTmp))
    (hDstTmp : wBellDst ≠ wBellTmp) :
    (jonesToffPairs58Dyn v rSys116 wBellDst wBellTmp hSysTmp hDstTmp).support ⊆
      {wBellDst, wBellTmp} ∪ rSys116.image :=
  (jonesToffPairsPrefix_props v rSys116 wBellDst wBellTmp hSysTmp hDstTmp 58 le_rfl).2.2

theorem cleanRealizesSet_jonesToffPairsPrefix {Var : Type} [Fintype Var] [DecidableEq Var]
    {N : ℕ} [NeZero (2 ^ N)] (v : Var) (rSys116 : QRegister (2 * 58) N)
    (wBellDst wBellTmp : Wire N) (hSysDst : rSys116.DisjointWires (QRegister.singleton wBellDst))
    (hSysTmp : rSys116.DisjointWires (QRegister.singleton wBellTmp))
    (hDstTmp : wBellDst ≠ wBellTmp) (k : ℕ) (hk : k ≤ 58) :
    CleanRealizesSet v {wBellTmp} (toffPairsPrefix rSys116 wBellDst hSysDst k hk).eval
      (jonesToffPairsPrefix v rSys116 wBellDst wBellTmp hSysTmp hDstTmp k hk) := by
  induction k with
  | zero => exact CleanRealizesSet.identity v {wBellTmp}
  | succ k ih =>
    exact (ih (by omega)).seq (CleanRealizesSet.jonesToffoli v {wBellTmp}
      (rSys116 ⟨k, by omega⟩) (rSys116 ⟨58 + k, by omega⟩) wBellDst wBellTmp
      (rSys116.wires.injective.ne (pair58_ne k hk))
      (ne_of_disjoint_singleton hSysDst ⟨k, by omega⟩)
      (ne_of_disjoint_singleton hSysDst ⟨58 + k, by omega⟩)
      (ne_of_disjoint_singleton hSysTmp ⟨k, by omega⟩)
      (ne_of_disjoint_singleton hSysTmp ⟨58 + k, by omega⟩) hDstTmp (Finset.mem_singleton_self _)
      (fun h ↦ ne_of_disjoint_singleton hSysTmp ⟨k, by omega⟩ (Finset.mem_singleton.mp h))
      (fun h ↦ ne_of_disjoint_singleton hSysTmp ⟨58 + k, by omega⟩ (Finset.mem_singleton.mp h))
      (by simp [hDstTmp]))

theorem cleanRealizesSet_jonesToffPairs58Dyn {Var : Type} [Fintype Var] [DecidableEq Var]
    {N : ℕ} [NeZero (2 ^ N)] (v : Var) (rSys116 : QRegister (2 * 58) N)
    (wBellDst wBellTmp : Wire N) (hSysDst : rSys116.DisjointWires (QRegister.singleton wBellDst))
    (hSysTmp : rSys116.DisjointWires (QRegister.singleton wBellTmp))
    (hDstTmp : wBellDst ≠ wBellTmp) :
    CleanRealizesSet v {wBellTmp} (toffPairs58Circuit rSys116 wBellDst hSysDst).eval
      (jonesToffPairs58Dyn v rSys116 wBellDst wBellTmp hSysTmp hDstTmp) := by
  unfold toffPairs58Circuit jonesToffPairs58Dyn
  exact cleanRealizesSet_jonesToffPairsPrefix v rSys116 wBellDst wBellTmp hSysDst hSysTmp
    hDstTmp 58 le_rfl

attribute [irreducible] jonesToffPairs58Dyn

/-- Bell-basis exit gadget (`232 T`, `0 TOFF`): rotates `rSys116` into the Bell basis, accumulates
singlet parity into `wBellDst` via `jonesToffoli`, and applies `CZ wSig wBellDst`. -/
def dBellExit58Dyn {Var : Type} {N : ℕ} (v : Var) (wSig : Wire N)
    (rSys116 : QRegister (2 * 58) N) (wBellDst wBellTmp : Wire N) : DynamicCircuit Var N :=
  if h : rSys116.DisjointWires (QRegister.singleton wBellDst) ∧
      rSys116.DisjointWires (QRegister.singleton wBellTmp) ∧
      wBellDst ≠ wBellTmp ∧ wSig ≠ wBellDst then
    .seq (.circuit (bellPre58On rSys116))
      (.seq (jonesToffPairs58Dyn v rSys116 wBellDst wBellTmp h.2.1 h.2.2.1)
        (.circuit (czCircuit wSig wBellDst h.2.2.2)))
  else .identity

@[simp] theorem dBellExit58Dyn_count_toff {Var : Type} {N : ℕ} (v : Var) (wSig : Wire N)
    (rSys116 : QRegister (2 * 58) N) (wBellDst wBellTmp : Wire N) :
    (dBellExit58Dyn v wSig rSys116 wBellDst wBellTmp).count .TOFF = 0 := by
  dsimp [dBellExit58Dyn]; split_ifs <;> simp
theorem dBellExit58Dyn_count_t {Var : Type} {N : ℕ} (v : Var) (wSig : Wire N)
    (rSys116 : QRegister (2 * 58) N) (wBellDst wBellTmp : Wire N)
    (hSysDst : rSys116.DisjointWires (QRegister.singleton wBellDst))
    (hSysTmp : rSys116.DisjointWires (QRegister.singleton wBellTmp))
    (hDstTmp : wBellDst ≠ wBellTmp) (hSigDst : wSig ≠ wBellDst) :
    (dBellExit58Dyn v wSig rSys116 wBellDst wBellTmp).count .T = 232 := by
  dsimp only [dBellExit58Dyn]
  split_ifs with hc
  · simp
  · exact False.elim (hc ⟨hSysDst, hSysTmp, hDstTmp, hSigDst⟩)

theorem dBellExit58Dyn_support_subset {Var : Type} {N : ℕ} (v : Var) (wSig : Wire N)
    (rSys116 : QRegister (2 * 58) N) (wBellDst wBellTmp : Wire N) :
    (dBellExit58Dyn v wSig rSys116 wBellDst wBellTmp).support ⊆
      {wSig, wBellDst, wBellTmp} ∪ rSys116.image := by
  dsimp only [dBellExit58Dyn]
  split_ifs with h
  · intro w hw
    have hJ := jonesToffPairs58Dyn_support_subset (Var := Var) v rSys116 wBellDst wBellTmp
      h.2.1 h.2.2.1
    have hPre := Circuit.support_onRegister_subset rSys116 bellPre58Circuit
    have hCZ := (pair_support_sub wSig wBellDst h.2.2.2).2.2
    simp only [DynamicCircuit.support_seq, DynamicCircuit.support_circuit, Finset.mem_union] at hw
    rcases hw with hw | hw | hw
    · exact Finset.mem_union_right _ (hPre hw)
    · have := hJ hw; simp only [Finset.mem_union, Finset.mem_insert,
        Finset.mem_singleton] at this ⊢; tauto
    · have := hCZ hw; simp only [Finset.mem_union, Finset.mem_insert,
        Finset.mem_singleton] at this ⊢; tauto
  · simp

theorem cleanRealizesSet_dBellExit58Dyn {Var : Type} [Fintype Var] [DecidableEq Var]
    {N : ℕ} [NeZero (2 ^ N)] (v : Var) (wSig : Wire N) (rSys116 : QRegister (2 * 58) N)
    (wBellDst wBellTmp : Wire N) (hSysDst : rSys116.DisjointWires (QRegister.singleton wBellDst))
    (hSysTmp : rSys116.DisjointWires (QRegister.singleton wBellTmp))
    (hDstTmp : wBellDst ≠ wBellTmp) (hSigDst : wSig ≠ wBellDst) (hSigTmp : wSig ≠ wBellTmp) :
    CleanRealizesSet v {wBellTmp}
      ((czCircuit wSig wBellDst hSigDst).eval * bellIso58Unitary rSys116 wBellDst hSysDst)
      (dBellExit58Dyn v wSig rSys116 wBellDst wBellTmp) := by
  dsimp only [dBellExit58Dyn]
  split_ifs with hc
  swap
  · exact False.elim (hc ⟨hSysDst, hSysTmp, hDstTmp, hSigDst⟩)
  have hPre : CleanRealizesSet v {wBellTmp} (bellPre58On rSys116).eval
      (.circuit (bellPre58On rSys116)) := by
    refine cleanRealizesSet_circuit_of_disjoint v {wBellTmp} _ (by simp)
      (Finset.disjoint_left.mpr fun w hw₁ hw₂ ↦ ?_)
    obtain ⟨i, rfl⟩ := (QRegister.mem_image rSys116 w).mp
      (Circuit.support_onRegister_subset rSys116 bellPre58Circuit hw₁)
    exact hSysTmp.ne i 0 (Finset.mem_singleton.mp hw₂)
  have hJ := cleanRealizesSet_jonesToffPairs58Dyn (Var := Var) v rSys116 wBellDst wBellTmp
    hSysDst hSysTmp hDstTmp
  have hCZ : CleanRealizesSet v {wBellTmp} (czCircuit wSig wBellDst hSigDst).eval
      (.circuit (czCircuit wSig wBellDst hSigDst)) := by
    refine cleanRealizesSet_circuit_of_disjoint v {wBellTmp} _ (by simp)
      (Finset.disjoint_left.mpr fun w hw₁ hw₂ ↦ ?_)
    have hw := (pair_support_sub wSig wBellDst hSigDst).2.2 hw₁
    rw [Finset.mem_singleton] at hw₂; subst w
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with h1 | h2
    · exact hSigTmp h1.symm
    · exact hDstTmp h2.symm
  have hSeq := hPre.seq (hJ.seq hCZ)
  have hEqU : (czCircuit wSig wBellDst hSigDst).eval *
      (toffPairs58Circuit rSys116 wBellDst hSysDst).eval * (bellPre58On rSys116).eval =
      (czCircuit wSig wBellDst hSigDst).eval * bellIso58Unitary rSys116 wBellDst hSysDst := by
    rw [bellIso58Unitary, bellIso58Circuit, Circuit.eval_seq, mul_assoc]
  rwa [hEqU] at hSeq

attribute [irreducible] dBellExit58Dyn

theorem restrictZeroSet_wp_dBellExit58Dyn_eq_of_subset {Var : Type} [Fintype Var]
    [DecidableEq Var] {N : ℕ} [NeZero (2 ^ N)] (v : Var) (wSig : Wire N)
    (rSys116 : QRegister (2 * 58) N) (wBellDst wBellTmp : Wire N) (S : Finset (Wire N))
    (hwDst : wBellDst ∈ S) (hwTmp : wBellTmp ∈ S) (hSigNotS : wSig ∉ S)
    (hSysDisjS : Disjoint rSys116.image S)
    (hSysDst : rSys116.DisjointWires (QRegister.singleton wBellDst)) (hDstTmp : wBellDst ≠ wBellTmp)
    (hSigSys : (QRegister.singleton wSig).DisjointWires rSys116)
    (Ψ : QCAssertion Var (2 ^ N)) (hΨ : ∀ σ val, Ψ (Function.update σ v val) = Ψ σ) :
    SelectSwapQROM.restrictZeroSet (wp
      (dBellExit58Dyn v wSig rSys116 wBellDst wBellTmp).compile Ψ) S =
      SelectSwapQROM.restrictZeroSet (qcWpQAssign (bellIso58Unitary rSys116 wBellDst hSysDst *
        cswap58Unitary wSig rSys116 hSigSys) Ψ) S := by
  have hSysTmp : rSys116.DisjointWires (QRegister.singleton wBellTmp) :=
    disjointWires_of_disjoint_image (hSysDisjS.mono_right (by simpa using hwTmp))
  have hSigDst : wSig ≠ wBellDst := fun h ↦ hSigNotS (h ▸ hwDst)
  have hSigTmp : wSig ≠ wBellTmp := fun h ↦ hSigNotS (h ▸ hwTmp)
  have hSub : ({wBellTmp} : Finset (Wire N)) ⊆ S.erase wBellDst :=
    Finset.singleton_subset_iff.mpr (Finset.mem_erase.mpr ⟨hDstTmp.symm, hwTmp⟩)
  have hDisjExt : Disjoint (dBellExit58Dyn (Var := Var) v wSig rSys116 wBellDst wBellTmp).support
      (S.erase wBellDst \ {wBellTmp}) := by
    refine Finset.disjoint_left.mpr fun w hw hmem ↦ ?_
    obtain ⟨hmemE, hnotTmp⟩ := Finset.mem_sdiff.mp hmem
    obtain ⟨hnotDst, hmemS⟩ := Finset.mem_erase.mp hmemE
    rcases Finset.mem_union.mp (dBellExit58Dyn_support_subset v wSig rSys116 wBellDst wBellTmp hw)
      with h3 | hSys
    · simp only [Finset.mem_insert, Finset.mem_singleton] at h3
      rcases h3 with rfl | rfl | rfl
      · exact hSigNotS hmemS
      · exact hnotDst rfl
      · exact hnotTmp (Finset.mem_singleton_self _)
    · exact Finset.disjoint_left.mp hSysDisjS hSys hmemS
  have hCR := (cleanRealizesSet_dBellExit58Dyn (Var := Var) v wSig rSys116 wBellDst wBellTmp
    hSysDst hSysTmp hDstTmp hSigDst hSigTmp).extend hSub hDisjExt
  have hU1 : S.erase wBellDst ∪ {wBellDst} = S := by
    rw [Finset.union_comm, Finset.singleton_union, Finset.insert_erase hwDst]
  rw [← hU1, ← SelectSwapQROM.restrictZeroSet_union, hCR.2.2.1 Ψ hΨ,
    SelectSwapQROM.restrictZeroSet_union, hU1]
  have hU2 : {wBellDst} ∪ S = S := by rw [Finset.singleton_union, Finset.insert_eq_of_mem hwDst]
  have hMat : ((czCircuit wSig wBellDst hSigDst).eval *
      bellIso58Unitary rSys116 wBellDst hSysDst).1 * zeroProjOn S =
      (bellIso58Unitary rSys116 wBellDst hSysDst *
        cswap58Unitary wSig rSys116 hSigSys).1 * zeroProjOn S := by
    rw [← hU2, ← zeroProjOn_mul_union, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      czCircuit_mul_bellIso_mul_zeroProjOn wSig rSys116 wBellDst hSysDst hSigSys hSigDst]
  have hAdj : zeroProjOn S * ((czCircuit wSig wBellDst hSigDst).eval *
      bellIso58Unitary rSys116 wBellDst hSysDst).1ᴴ =
      zeroProjOn S * (bellIso58Unitary rSys116 wBellDst hSysDst *
        cswap58Unitary wSig rSys116 hSigSys).1ᴴ := by
    simpa only [conjTranspose_mul, zeroProjOn_conjTranspose] using congrArg conjTranspose hMat
  funext σ; apply Subtype.ext; ext1
  simp only [SelectSwapQROM.restrictZeroSet_coe, qcWpQAssign, qcQAssignObsMap,
    Observable.conj_coe,
    Unitary.coe_star, Matrix.star_eq_conjTranspose, conj_conj, conj_apply_mat]; rw [hAdj]

/-! ## Section 5: `dBellEntry58Dyn` (`0 T`, `0 TOFF`, Step c) -/

/-- Bell-basis entry gadget (`0 T`, `0 TOFF`): `CZ wSig wBellDst`, `X`-basis measurement/reset of
`wBellDst` with classical `58`-pair `CZ` phase fixup on `rSys116`, then `bellPost58On`. -/
def dBellEntry58Dyn {Var : Type} {N : ℕ} (v : Var) (wSig : Wire N)
    (rSys116 : QRegister (2 * 58) N) (wBellDst : Wire N) : DynamicCircuit Var N :=
  if hSigDst : wSig ≠ wBellDst then
    .seq (.circuit (czCircuit wSig wBellDst hSigDst))
      (.seq (.circuit (Circuit.H wBellDst))
        (.seq (.measure v (QRegister.singleton wBellDst))
          (.seq (qcQIf (fun σ ↦ σ v) (.circuit (Circuit.X wBellDst ;;ᶜ czPairs58On rSys116))
              .identity) (.circuit (bellPost58On rSys116)))))
  else .identity

@[simp] theorem dBellEntry58Dyn_count_t {Var : Type} {N : ℕ} (v : Var) (wSig : Wire N)
    (rSys116 : QRegister (2 * 58) N) (wBellDst : Wire N) :
    (dBellEntry58Dyn v wSig rSys116 wBellDst).count .T = 0 := by
  dsimp [dBellEntry58Dyn]; split_ifs <;> simp [Circuit.H, Circuit.X, Circuit.single]
@[simp] theorem dBellEntry58Dyn_count_toff {Var : Type} {N : ℕ} (v : Var) (wSig : Wire N)
    (rSys116 : QRegister (2 * 58) N) (wBellDst : Wire N) :
    (dBellEntry58Dyn v wSig rSys116 wBellDst).count .TOFF = 0 := by
  dsimp [dBellEntry58Dyn]; split_ifs <;> simp [Circuit.H, Circuit.X, Circuit.single]

theorem wp_dBellEntry58Dyn_apply {Var : Type} [Finite Var] [DecidableEq Var]
    {N : ℕ} [NeZero (2 ^ N)] (v : Var) (wSig : Wire N) (rSys116 : QRegister (2 * 58) N)
    (wBellDst : Wire N) (hSigDst : wSig ≠ wBellDst) (Θ : QCAssertion Var (2 ^ N)) (σ : Store Var) :
    let P₀ := (QRegister.singleton wBellDst).basisOutcomeProjector 0
    let P₁ := (QRegister.singleton wBellDst).basisOutcomeProjector 1
    let K₀ := (bellPost58On rSys116).eval.1 * P₀ * (Circuit.H wBellDst).eval.1 *
      (czCircuit wSig wBellDst hSigDst).eval.1
    let K₁ := (bellPost58On rSys116).eval.1 * (czPairs58On rSys116).eval.1 *
      (Circuit.X wBellDst).eval.1 * P₁ * (Circuit.H wBellDst).eval.1 *
      (czCircuit wSig wBellDst hSigDst).eval.1
    (wp (dBellEntry58Dyn v wSig rSys116 wBellDst).compile Θ σ).1 =
      (Θ (Function.update σ v 0)).1.conj K₀ᴴ + (Θ (Function.update σ v 1)).1.conj K₁ᴴ := by
  cases nonempty_fintype Var
  intro P₀ P₁ K₀ K₁; rw [dBellEntry58Dyn, dite_eq_left hSigDst]
  let cCZ := czCircuit wSig wBellDst hSigDst
  let cH := Circuit.H wBellDst
  let cFix := Circuit.X wBellDst ;;ᶜ czPairs58On rSys116
  let cPost := bellPost58On rSys116
  let Θp := wp cPost.compile Θ
  have hmeas : (wp (.qSeq (QProg.measureRegister v (QRegister.singleton wBellDst))
        (qcQIf (fun σ'' ↦ σ'' v) cFix.compile .skip)) Θp σ).1 =
      (Θp (Function.update σ v 0)).1.conj P₀ᴴ +
        ((Θp (Function.update σ v 1)).1.conj cFix.eval.1ᴴ).conj P₁ᴴ := by
    have hs0 : σ.subst v 0 = Function.update σ v 0 := by
      funext y; simp [Store.subst, Function.update]
    have hs1 : σ.subst v 1 = Function.update σ v 1 := by
      funext y; simp [Store.subst, Function.update]
    have hcFix : wp cFix.compile Θp = qcWpQAssign cFix.eval Θp :=
      DynamicCircuit.qc_wp_circuit_compile cFix Θp
    simp only [wp_qSeq, QProg.measureRegister, qc_wp_qMeasure', qc_wp_qMeasure_apply,
      qc_qMeasure_obs_map_coe, QCAssertion.subst_apply, wp_qIf, hcFix, wp_skip]
    change ∑ o : Fin 2, _ = _; rw [Fin.sum_univ_two]
    simp [qc_qMeasure_outcome_herm_eq_conj, qcWpQAssign, qcQAssignObsMap, Observable.conj_coe,
      Unitary.coe_star, Matrix.star_eq_conjTranspose, QRegister.computationalBasisMeasurement_apply,
      P₀, P₁, hs0, hs1]
  change (wp cCZ.compile (wp cH.compile
      (wp (.qSeq (QProg.measureRegister v (QRegister.singleton wBellDst))
        (qcQIf (fun σ'' ↦ σ'' v) cFix.compile .skip)) Θp)) σ).1 = _
  ext1; rw [DynamicCircuit.qc_wp_circuit_compile, DynamicCircuit.qc_wp_circuit_compile]
  simp only [qcWpQAssign, qcQAssignObsMap, Observable.conj_coe, Unitary.coe_star,
    Matrix.star_eq_conjTranspose]
  rw [hmeas]
  simp only [Θp, cFix, DynamicCircuit.qc_wp_circuit_compile, qcWpQAssign, qcQAssignObsMap,
    Observable.conj_coe, Unitary.coe_star, Matrix.star_eq_conjTranspose, Circuit.eval_seq,
    Submonoid.coe_mul, map_add, HermitianMat.mat_add, conj_apply_mat, K₀, K₁, cCZ, cH, cPost,
    conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]

attribute [irreducible] dBellEntry58Dyn

theorem wp_dBellEntry58Dyn_update_self {Var : Type} [Finite Var] [DecidableEq Var]
    {N : ℕ} [NeZero (2 ^ N)] (v : Var) (wSig : Wire N) (rSys116 : QRegister (2 * 58) N)
    (wBellDst : Wire N) (hSigDst : wSig ≠ wBellDst)
    (Θ : QCAssertion Var (2 ^ N)) (σ : Store Var) (val : ℤ) :
    wp (dBellEntry58Dyn v wSig rSys116 wBellDst).compile Θ (Function.update σ v val) =
      wp (dBellEntry58Dyn v wSig rSys116 wBellDst).compile Θ σ := by
  apply Subtype.ext; rw [wp_dBellEntry58Dyn_apply v wSig rSys116 wBellDst hSigDst,
    wp_dBellEntry58Dyn_apply v wSig rSys116 wBellDst hSigDst, Function.update_idem,
    Function.update_idem]

theorem onRegister_sys116_comm_zeroProjOn {N : ℕ} (rSys116 : QRegister (2 * 58) N)
    (wBellDst : Wire N) (hSysDst : rSys116.DisjointWires (QRegister.singleton wBellDst))
    (c : Circuit (2 * 58)) :
    zeroProjOn {wBellDst} * (c.onRegister rSys116).eval.1 =
      (c.onRegister rSys116).eval.1 * zeroProjOn {wBellDst} := by
  rw [← QRegister.image_singleton wBellDst, ← basisOutcomeProjector_zero_eq_zeroProjOn]
  refine embedMatrix_comm_circuit_of_disjoint _ (compProj 0) _
    (Finset.disjoint_left.mpr fun w hw₁ hw₂ ↦ ?_)
  rw [QRegister.image_singleton, Finset.mem_singleton] at hw₁; subst w
  obtain ⟨i, hi⟩ := (QRegister.mem_image rSys116 wBellDst).mp
    (Circuit.support_onRegister_subset rSys116 c hw₂)
  exact hSysDst.ne i 0 hi

theorem dBellEntry_kraus_bellIso {N : ℕ} (wSig : Wire N)
    (rSys116 : QRegister (2 * 58) N) (wBellDst : Wire N)
    (hSysDst : rSys116.DisjointWires (QRegister.singleton wBellDst))
    (hSigSys : (QRegister.singleton wSig).DisjointWires rSys116) (hSigDst : wSig ≠ wBellDst) :
    let P₀ := (QRegister.singleton wBellDst).basisOutcomeProjector 0
    let P₁ := (QRegister.singleton wBellDst).basisOutcomeProjector 1
    let K₀ := (bellPost58On rSys116).eval.1 * P₀ * (Circuit.H wBellDst).eval.1 *
      (czCircuit wSig wBellDst hSigDst).eval.1
    let K₁ := (bellPost58On rSys116).eval.1 * (czPairs58On rSys116).eval.1 *
      (Circuit.X wBellDst).eval.1 * P₁ * (Circuit.H wBellDst).eval.1 *
      (czCircuit wSig wBellDst hSigDst).eval.1
    K₀ * (bellIso58Unitary rSys116 wBellDst hSysDst).1 * zeroProjOn {wBellDst} =
      sqrtHalf • ((cswap58Unitary wSig rSys116 hSigSys).1 * zeroProjOn {wBellDst}) ∧
    K₁ * (bellIso58Unitary rSys116 wBellDst hSysDst).1 * zeroProjOn {wBellDst} =
      sqrtHalf • ((cswap58Unitary wSig rSys116 hSigSys).1 * zeroProjOn {wBellDst}) := by
  intro P₀ P₁ K₀ K₁
  have hCommSys (c : Circuit (2 * 58)) :=
    (onRegister_sys116_comm_zeroProjOn rSys116 wBellDst hSysDst c).symm
  have hPostPre : (bellPost58On rSys116).eval.1 * (bellPre58On rSys116).eval.1 = 1 :=
    congrArg Subtype.val (bellPost58On_mul_bellPre58On rSys116)
  have hCore0 : P₀ * (Circuit.H wBellDst).eval.1 *
      (toffPairs58Circuit rSys116 wBellDst hSysDst).eval.1 * zeroProjOn {wBellDst} =
      sqrtHalf • zeroProjOn {wBellDst} := by
    apply matrix_ext_ket; intro β
    simp only [P₀, ← Matrix.mulVec_mulVec, Matrix.smul_mulVec, zeroProjOn_mulVec_ket,
      Finset.mem_singleton, forall_eq]
    by_cases h0 : β wBellDst = 0
    · have hβ0 : Function.update β wBellDst 0 = β := h0 ▸ Function.update_eq_self wBellDst β
      rw [ite_eq_left h0, toffPairs58_ket, h0, zero_add, ket_H, Function.update_self,
        Function.update_idem, hβ0]
      simp only [Matrix.mulVec_smul, Matrix.mulVec_add, singleton_projector_zero_mulVec_ket, h0,
        ↓reduceIte, Function.update_self, one_ne_zero, smul_zero, add_zero]
    · simp only [h0, ↓reduceIte, Matrix.mulVec_zero, smul_zero]
  have hCore1 : (czPairs58On rSys116).eval.1 * (Circuit.X wBellDst).eval.1 * P₁ *
      (Circuit.H wBellDst).eval.1 *
      (toffPairs58Circuit rSys116 wBellDst hSysDst).eval.1 * zeroProjOn {wBellDst} =
      sqrtHalf • zeroProjOn {wBellDst} := by
    apply matrix_ext_ket; intro β
    simp only [P₁, ← Matrix.mulVec_mulVec, Matrix.smul_mulVec, zeroProjOn_mulVec_ket,
      Finset.mem_singleton, forall_eq]
    by_cases h0 : β wBellDst = 0
    · have hβ0 : Function.update β wBellDst 0 = β := h0 ▸ Function.update_eq_self wBellDst β
      rw [ite_eq_left h0, toffPairs58_ket, h0, zero_add, ket_H, Function.update_self,
        Function.update_idem, hβ0]
      simp only [Matrix.mulVec_smul, Matrix.mulVec_add, singleton_projector_one_mulVec_ket, h0,
        zero_ne_one, ↓reduceIte, Function.update_self, zero_add, ket_X, Function.update_idem,
        one_add_one_zmod2, hβ0, czPairs58On_ket, smul_smul]
      rw [mul_assoc, bitSign_mul_self, mul_one]
    · simp only [h0, ↓reduceIte, Matrix.mulVec_zero, smul_zero]
  have hCSComm : (cswap58Unitary wSig rSys116 hSigSys).1 * zeroProjOn {wBellDst} =
      zeroProjOn {wBellDst} * (cswap58Unitary wSig rSys116 hSigSys).1 :=
    (cswap58_comm_zeroProjOn_singleton wSig rSys116 wBellDst hSysDst hSigSys hSigDst).symm
  have hStep := czCircuit_mul_bellIso_mul_zeroProjOn wSig rSys116 wBellDst hSysDst hSigSys hSigDst
  simp only [Submonoid.coe_mul, Matrix.mul_assoc] at hStep
  rw [hCSComm] at hStep
  have hViso0 : (bellIso58Unitary rSys116 wBellDst hSysDst).1 * zeroProjOn {wBellDst} =
      (toffPairs58Circuit rSys116 wBellDst hSysDst).eval.1 *
        (zeroProjOn {wBellDst} * (bellPre58On rSys116).eval.1) := by
    simp only [bellIso58Unitary, bellIso58Circuit, bellPre58On, Circuit.eval_seq,
      Submonoid.coe_mul, Matrix.mul_assoc]
    rw [hCommSys bellPre58Circuit]
  constructor
  · calc K₀ * (bellIso58Unitary rSys116 wBellDst hSysDst).1 * zeroProjOn {wBellDst}
        = (bellPost58On rSys116).eval.1 * (P₀ * (Circuit.H wBellDst).eval.1 *
            (toffPairs58Circuit rSys116 wBellDst hSysDst).eval.1 * zeroProjOn {wBellDst}) *
            (bellPre58On rSys116).eval.1 * (cswap58Unitary wSig rSys116 hSigSys).1 := by
          dsimp only [K₀]; simp only [Matrix.mul_assoc]
          rw [hStep, ← Matrix.mul_assoc (bellIso58Unitary rSys116 wBellDst hSysDst).1, hViso0]
          simp only [Matrix.mul_assoc]
      _ = sqrtHalf • ((cswap58Unitary wSig rSys116 hSigSys).1 * zeroProjOn {wBellDst}) := by
          rw [hCore0]; simp only [Matrix.mul_smul, Matrix.smul_mul, bellPost58On]
          rw [hCommSys bellPost58Circuit, Matrix.mul_assoc (zeroProjOn {wBellDst}),
            hPostPre, mul_one, ← hCSComm]
  · calc K₁ * (bellIso58Unitary rSys116 wBellDst hSysDst).1 * zeroProjOn {wBellDst}
        = (bellPost58On rSys116).eval.1 * ((czPairs58On rSys116).eval.1 *
            (Circuit.X wBellDst).eval.1 * P₁ * (Circuit.H wBellDst).eval.1 *
            (toffPairs58Circuit rSys116 wBellDst hSysDst).eval.1 * zeroProjOn {wBellDst}) *
            (bellPre58On rSys116).eval.1 * (cswap58Unitary wSig rSys116 hSigSys).1 := by
          dsimp only [K₁]; simp only [Matrix.mul_assoc]
          rw [hStep, ← Matrix.mul_assoc (bellIso58Unitary rSys116 wBellDst hSysDst).1, hViso0]
          simp only [Matrix.mul_assoc]
      _ = sqrtHalf • ((cswap58Unitary wSig rSys116 hSigSys).1 * zeroProjOn {wBellDst}) := by
          rw [hCore1]; simp only [Matrix.mul_smul, Matrix.smul_mul, bellPost58On]
          rw [hCommSys bellPost58Circuit, Matrix.mul_assoc (zeroProjOn {wBellDst}),
            hPostPre, mul_one, ← hCSComm]

theorem wp_qAssign_bellIso_wp_dBellEntry58Dyn_aux {Var : Type} [Fintype Var]
    [DecidableEq Var] {N : ℕ} [NeZero (2 ^ N)] (v : Var) (wSig : Wire N)
    (rSys116 : QRegister (2 * 58) N) (wBellDst : Wire N)
    (hSysDst : rSys116.DisjointWires (QRegister.singleton wBellDst))
    (hSigSys : (QRegister.singleton wSig).DisjointWires rSys116) (hSigDst : wSig ≠ wBellDst)
    (Ψ : QCAssertion Var (2 ^ N)) (σ : Store Var) :
    (SelectSwapQROM.restrictZeroSet
        (qcWpQAssign (bellIso58Unitary rSys116 wBellDst hSysDst)
          (wp (dBellEntry58Dyn v wSig rSys116 wBellDst).compile Ψ)) {wBellDst} σ).1 =
      (1 / 2 : ℝ) • (SelectSwapQROM.restrictZeroSet (qcWpQAssign
        (cswap58Unitary wSig rSys116 hSigSys) Ψ)
          {wBellDst} (Function.update σ v 0)).1 +
        (1 / 2 : ℝ) • (SelectSwapQROM.restrictZeroSet (qcWpQAssign
          (cswap58Unitary wSig rSys116 hSigSys) Ψ)
          {wBellDst} (Function.update σ v 1)).1 := by
  let P₀ := (QRegister.singleton wBellDst).basisOutcomeProjector 0
  let P₁ := (QRegister.singleton wBellDst).basisOutcomeProjector 1
  let K₀ := (bellPost58On rSys116).eval.1 * P₀ * (Circuit.H wBellDst).eval.1 *
    (czCircuit wSig wBellDst hSigDst).eval.1
  let K₁ := (bellPost58On rSys116).eval.1 * (czPairs58On rSys116).eval.1 *
    (Circuit.X wBellDst).eval.1 * P₁ * (Circuit.H wBellDst).eval.1 *
    (czCircuit wSig wBellDst hSigDst).eval.1
  let V := bellIso58Unitary rSys116 wBellDst hSysDst
  let CS := cswap58Unitary wSig rSys116 hSigSys
  have hK : K₀ * V.1 * zeroProjOn {wBellDst} = sqrtHalf • (CS.1 * zeroProjOn {wBellDst}) ∧
      K₁ * V.1 * zeroProjOn {wBellDst} = sqrtHalf • (CS.1 * zeroProjOn {wBellDst}) :=
    dBellEntry_kraus_bellIso wSig rSys116 wBellDst hSysDst hSigSys hSigDst
  have hadj (K : Operator (2 ^ N))
      (h : K * V.1 * zeroProjOn {wBellDst} = sqrtHalf • (CS.1 * zeroProjOn {wBellDst})) :
      zeroProjOn {wBellDst} * V.1ᴴ * Kᴴ = sqrtHalf • (zeroProjOn {wBellDst} * CS.1ᴴ) := by
    have h' := congrArg conjTranspose h
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_smul, zeroProjOn_conjTranspose,
      star_sqrtHalf, Matrix.mul_assoc] at h' ⊢
    exact h'
  rw [SelectSwapQROM.restrictZeroSet_coe, SelectSwapQROM.restrictZeroSet_coe,
    SelectSwapQROM.restrictZeroSet_coe]
  simp only [qcWpQAssign, qcQAssignObsMap, Observable.conj_coe, Unitary.coe_star,
    Matrix.star_eq_conjTranspose, conj_conj]
  rw [wp_dBellEntry58Dyn_apply v wSig rSys116 wBellDst hSigDst Ψ σ, map_add, conj_conj, conj_conj,
    hadj K₀ hK.1, hadj K₁ hK.2]
  ext1
  simp only [HermitianMat.mat_add, HermitianMat.mat_smul, conj_apply_mat,
    Matrix.conjTranspose_smul, star_sqrtHalf, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    sqrtHalf_mul_sqrtHalf, CS]
  ext i j
  simp [Complex.real_smul]

theorem restrictZeroSet_wp_qAssign_bellIso_wp_dBellEntry58Dyn {Var : Type} [Fintype Var]
    [DecidableEq Var] {N : ℕ} [NeZero (2 ^ N)] (v : Var) (wSig : Wire N)
    (rSys116 : QRegister (2 * 58) N) (wBellDst : Wire N)
    (hSysDst : rSys116.DisjointWires (QRegister.singleton wBellDst))
    (hSigSys : (QRegister.singleton wSig).DisjointWires rSys116) (hSigDst : wSig ≠ wBellDst)
    (Θ : QCAssertion Var (2 ^ N)) (hΘ : ∀ σ val, Θ (Function.update σ v val) = Θ σ) :
    SelectSwapQROM.restrictZeroSet
        (qcWpQAssign (bellIso58Unitary rSys116 wBellDst hSysDst)
          (wp (dBellEntry58Dyn v wSig rSys116 wBellDst).compile Θ)) {wBellDst} =
      SelectSwapQROM.restrictZeroSet (qcWpQAssign
        (cswap58Unitary wSig rSys116 hSigSys) Θ) {wBellDst} := by
  funext σ; apply Subtype.ext
  rw [wp_qAssign_bellIso_wp_dBellEntry58Dyn_aux v wSig rSys116 wBellDst hSysDst hSigSys hSigDst Θ σ]
  have hup (val : ℤ) : SelectSwapQROM.restrictZeroSet (qcWpQAssign
    (cswap58Unitary wSig rSys116 hSigSys) Θ)
      {wBellDst} (Function.update σ v val) =
      SelectSwapQROM.restrictZeroSet (qcWpQAssign
        (cswap58Unitary wSig rSys116 hSigSys) Θ) {wBellDst} σ := by
    simp [SelectSwapQROM.restrictZeroSet, qcWpQAssign, hΘ σ val]
  have h12 : (1 / 2 : ℝ) + 1 / 2 = 1 := by norm_num
  rw [hup 0, hup 1, ← add_smul, h12, one_smul]

/-! ## Section 6: End-to-End Bell-Singlet Sandwich & `CleanRealizesSet` Splice (Steps d–e) -/

theorem wp_qAssign_cswap58_restrictZeroSet {Var : Type} [Fintype Var]
    {N : ℕ} [NeZero (2 ^ N)] (wSig : Wire N) (rSys116 : QRegister (2 * 58) N)
    (hSigSys : (QRegister.singleton wSig).DisjointWires rSys116)
    (T : Finset (Wire N)) (hwSig : wSig ∉ T) (hSysT : Disjoint rSys116.image T)
    (Ψ : QCAssertion Var (2 ^ N)) :
    qcWpQAssign (cswap58Unitary wSig rSys116 hSigSys) (SelectSwapQROM.restrictZeroSet Ψ T) =
      SelectSwapQROM.restrictZeroSet (qcWpQAssign (cswap58Unitary wSig rSys116 hSigSys) Ψ) T := by
  classical
  let rP := (QRegister.singleton wSig).concat rSys116 hSigSys
  let c := (cswapBlockCircuit 58).onRegister rP
  have hceval : cswap58Unitary wSig rSys116 hSigSys = c.eval := by
    rw [← cswap58Unitary_eq_embed_cswapBlockCircuit, Circuit.eval_onRegister]
  have hDisj : Disjoint c.support T := by
    refine Finset.disjoint_left.mpr fun w hw hT ↦ ?_
    have hm := (QRegister.image_concat _ _ hSigSys) ▸
      Circuit.support_onRegister_subset rP (cswapBlockCircuit 58) hw
    rcases Finset.mem_union.mp hm with h | h
    · rw [QRegister.image_singleton, Finset.mem_singleton] at h; exact hwSig (h ▸ hT)
    · exact Finset.disjoint_left.mp hSysT h hT
  rw [hceval, ← DynamicCircuit.qc_wp_circuit_compile, ← DynamicCircuit.qc_wp_circuit_compile]
  exact wp_restrictZeroSet_of_disjoint (.circuit c) T hDisj Ψ

theorem bellSandwich58_wp_step {Var : Type} [Fintype Var] [DecidableEq Var]
    {N : ℕ} [NeZero (2 ^ N)] (v : Var) (wSig1 wSig2 : Wire N)
    (rSys116 : QRegister (2 * 58) N) (wBellDst wBellTmp : Wire N) (S : Finset (Wire N))
    (hwDst : wBellDst ∈ S) (hwTmp : wBellTmp ∈ S) (hSig1NotS : wSig1 ∉ S)
    (hSysDisjS : Disjoint rSys116.image S)
    (hSysDst : rSys116.DisjointWires (QRegister.singleton wBellDst))
    (hDstTmp : wBellDst ≠ wBellTmp)
    (hSig1Sys : (QRegister.singleton wSig1).DisjointWires rSys116)
    (hSig2Dst : wSig2 ≠ wBellDst) (pMid : DynamicCircuit Var N)
    (hMidDisj : Disjoint pMid.support (rSys116.image ∪ {wBellDst}))
    (hMidV : PreservesVInv v pMid) (A : QCAssertion Var (2 ^ N)) :
    SelectSwapQROM.restrictZeroSet (wp (DynamicCircuit.seq
      (dBellExit58Dyn v wSig1 rSys116 wBellDst wBellTmp)
        (.seq pMid (dBellEntry58Dyn v wSig2 rSys116 wBellDst))).compile A) S =
      qcWpQAssign (cswap58Unitary wSig1 rSys116 hSig1Sys) (SelectSwapQROM.restrictZeroSet
        (wp pMid.compile (SelectSwapQROM.restrictZeroSet (qcWpQAssign
          (bellIso58Unitary rSys116 wBellDst hSysDst)
          (wp (dBellEntry58Dyn v wSig2 rSys116 wBellDst).compile A)) {wBellDst})) S) := by
  have hMidIso : Disjoint pMid.support (bellIso58Circuit rSys116 wBellDst hSysDst).support :=
    hMidDisj.mono_right (bellIso58Circuit_support_subset rSys116 wBellDst hSysDst)
  have hMidDst : Disjoint pMid.support {wBellDst} := hMidDisj.mono_right Finset.subset_union_right
  have hUS : {wBellDst} ∪ S = S := by rw [Finset.singleton_union, Finset.insert_eq_of_mem hwDst]
  have hA_inv := hMidV _ (wp_dBellEntry58Dyn_update_self v wSig2 rSys116 wBellDst hSig2Dst A)
  change SelectSwapQROM.restrictZeroSet (wp
    (dBellExit58Dyn v wSig1 rSys116 wBellDst wBellTmp).compile
    (wp pMid.compile (wp (dBellEntry58Dyn v wSig2 rSys116 wBellDst).compile A))) S = _
  rw [restrictZeroSet_wp_dBellExit58Dyn_eq_of_subset v wSig1 rSys116 wBellDst wBellTmp S
      hwDst hwTmp hSig1NotS hSysDisjS hSysDst hDstTmp hSig1Sys _ hA_inv,
    ← qc_wp_qAssign_comp, bellIso58Unitary,
    wp_qAssign_comm_wp_of_disjoint (bellIso58Circuit rSys116 wBellDst hSysDst) pMid hMidIso,
    ← bellIso58Unitary,
    ← wp_qAssign_cswap58_restrictZeroSet wSig1 rSys116 hSig1Sys S hSig1NotS hSysDisjS,
    ← hUS, ← SelectSwapQROM.restrictZeroSet_union,
      ← wp_restrictZeroSet_of_disjoint pMid {wBellDst} hMidDst, hUS]

theorem restrictZeroSet_wp_bellSandwich58_eq_wp_qAssign {Var : Type} [Fintype Var]
    [DecidableEq Var] {N : ℕ} [NeZero (2 ^ N)] (v : Var) (wSig1 wSig2 : Wire N)
    (rSys116 : QRegister (2 * 58) N) (wBellDst wBellTmp : Wire N) (S : Finset (Wire N))
    (hwDst : wBellDst ∈ S) (hwTmp : wBellTmp ∈ S) (hSig1NotS : wSig1 ∉ S)
    (hSysDisjS : Disjoint rSys116.image S) (hDstTmp : wBellDst ≠ wBellTmp)
    (hSig1Sys : (QRegister.singleton wSig1).DisjointWires rSys116)
    (hSig2Sys : (QRegister.singleton wSig2).DisjointWires rSys116)
    (hSig2Dst : wSig2 ≠ wBellDst) (pMid : DynamicCircuit Var N)
    (hMidDisj : Disjoint pMid.support (rSys116.image ∪ {wBellDst}))
    (hMidV : PreservesVInv v pMid) (Θ : QCAssertion Var (2 ^ N))
    (hΘ : ∀ σ val, Θ (Function.update σ v val) = Θ σ) :
    SelectSwapQROM.restrictZeroSet (wp (DynamicCircuit.seq
      (dBellExit58Dyn v wSig1 rSys116 wBellDst wBellTmp)
        (.seq pMid (dBellEntry58Dyn v wSig2 rSys116 wBellDst))).compile Θ) S =
      SelectSwapQROM.restrictZeroSet (qcWpQAssign (cswap58Unitary wSig1 rSys116 hSig1Sys)
        (wp pMid.compile (qcWpQAssign (cswap58Unitary wSig2 rSys116 hSig2Sys) Θ))) S := by
  have hSysDst : rSys116.DisjointWires (QRegister.singleton wBellDst) :=
    disjointWires_of_disjoint_image (hSysDisjS.mono_right (by simpa using hwDst))
  have hMidDst : Disjoint pMid.support {wBellDst} := hMidDisj.mono_right Finset.subset_union_right
  have hUS : {wBellDst} ∪ S = S := by rw [Finset.singleton_union, Finset.insert_eq_of_mem hwDst]
  rw [bellSandwich58_wp_step v wSig1 wSig2 rSys116 wBellDst wBellTmp S hwDst hwTmp hSig1NotS
      hSysDisjS hSysDst hDstTmp hSig1Sys hSig2Dst pMid hMidDisj hMidV Θ,
    restrictZeroSet_wp_qAssign_bellIso_wp_dBellEntry58Dyn v wSig2 rSys116 wBellDst hSysDst
      hSig2Sys hSig2Dst Θ hΘ,
    wp_restrictZeroSet_of_disjoint pMid {wBellDst} hMidDst, SelectSwapQROM.restrictZeroSet_union,
      hUS,
    wp_qAssign_cswap58_restrictZeroSet wSig1 rSys116 hSig1Sys S hSig1NotS hSysDisjS]

theorem restrictZeroSet_wp_bellSandwich58_eq_cswapCircuit {Var : Type} [Fintype Var]
    [DecidableEq Var] {N : ℕ} [NeZero (2 ^ N)] (v : Var) (wSig1 wSig2 : Wire N)
    (rSys116 : QRegister (2 * 58) N) (wBellDst wBellTmp : Wire N) (S : Finset (Wire N))
    (hwDst : wBellDst ∈ S) (hwTmp : wBellTmp ∈ S) (hSig1NotS : wSig1 ∉ S)
    (hSysDisjS : Disjoint rSys116.image S) (hDstTmp : wBellDst ≠ wBellTmp)
    (hSig1Sys : (QRegister.singleton wSig1).DisjointWires rSys116)
    (hSig2Sys : (QRegister.singleton wSig2).DisjointWires rSys116)
    (hSig2Dst : wSig2 ≠ wBellDst) (pMid : DynamicCircuit Var N)
    (hMidDisj : Disjoint pMid.support (rSys116.image ∪ {wBellDst}))
    (hMidV : PreservesVInv v pMid) (Θ : QCAssertion Var (2 ^ N))
    (hΘ : ∀ σ val, Θ (Function.update σ v val) = Θ σ) :
    let c1 :=
      (cswapBlockCircuit 58).onRegister ((QRegister.singleton wSig1).concat rSys116 hSig1Sys)
    let c2 :=
      (cswapBlockCircuit 58).onRegister ((QRegister.singleton wSig2).concat rSys116 hSig2Sys)
    SelectSwapQROM.restrictZeroSet (wp (DynamicCircuit.seq
      (dBellExit58Dyn v wSig1 rSys116 wBellDst wBellTmp)
        (.seq pMid (dBellEntry58Dyn v wSig2 rSys116 wBellDst))).compile Θ) S =
      SelectSwapQROM.restrictZeroSet (wp (DynamicCircuit.seq (.circuit c1) (.seq pMid
        (.circuit c2))).compile Θ)
        S := by
  intro c1 c2
  rw [restrictZeroSet_wp_bellSandwich58_eq_wp_qAssign v wSig1 wSig2 rSys116 wBellDst wBellTmp S
    hwDst hwTmp hSig1NotS hSysDisjS hDstTmp hSig1Sys hSig2Sys hSig2Dst pMid hMidDisj hMidV Θ hΘ]
  change _ = SelectSwapQROM.restrictZeroSet (wp c1.compile (wp pMid.compile (wp c2.compile Θ))) S
  rw [DynamicCircuit.qc_wp_circuit_compile, DynamicCircuit.qc_wp_circuit_compile,
    Circuit.eval_onRegister, Circuit.eval_onRegister,
    cswap58Unitary_eq_embed_cswapBlockCircuit, cswap58Unitary_eq_embed_cswapBlockCircuit]

end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.BellSingletCSwap58
end

/-!
# Streamed-`rA` Gidney Unsigned Phase-Kick Engine (`0 ≤ d < B`, `0 TOFF`)

Streams `d` low `rA` ancilla bits of the unsigned `(B + 2)`-bit phase-kick adder via a
forward-compute / backward-uncompute streamed prefix on `a0 = rASh 0`, using temporary logical-ANDs
(`andCompute` / `andUncompute`) from C. Gidney, "Halving the cost of quantum addition," *Quantum*
**2**, 74 (2018), DOI: `10.22331/q-2018-06-18-74`, at `8 * B + 10 + 4 * d` `T`-gates and `0 TOFF`
on workspace `rASh.concat rC` of `2 * B - d` clean wires. Used for the cytochrome P450 active-space
Hamiltonian of J. J. Goings *et al.*, "Reliably assessing the electronic structure of cytochrome
P450 on today's classical computers and tomorrow's quantum computers," *Proc. Natl. Acad. Sci.
U.S.A.* **119**(37), e2203533119 (2022), DOI: `10.1073/pnas.2203533119`.
-/
@[expose] public section

namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.PhaseB154Pi145Select
open QuantumComputation.Specs QuantumComputation.Specs.P450

open Operator QProg Matrix HermitianMat Real
open QuantumComputation.Specs Solution QuantumComputation.Specs.P450 Solution
open Solution.BlockEncodingCore Solution.BlockEncodingCircuit
open Solution.CircuitModular Solution.GivensOps
open Solution.StepEncK
open Solution.Balanced160Select
open Solution.CleanDyn
open scoped Matrix ComplexOrder MatrixOrder BigOperators Matrix.Norms.L2Operator Circuit.Notation

/-! ## Section 1A: `SubspaceStepU` Temporary-AND Combinators & 4-Wire Gidney Primitives -/

theorem toffoli_eval_mul_self {n : ℕ} (c₁ c₂ t : Wire n)
    (h₁₂ : c₁ ≠ c₂) (h₁t : c₁ ≠ t) (h₂t : c₂ ≠ t) :
    (Circuit.TOFF c₁ c₂ t h₁₂ h₁t h₂t).eval.1 *
      (Circuit.TOFF c₁ c₂ t h₁₂ h₁t h₂t).eval.1 = 1 := by
  apply UnsignedGivens.matrix_ext_ket; intro β
  rw [← Matrix.mulVec_mulVec, UnsignedGivens.evolve_TOFF_ket, UnsignedGivens.evolve_TOFF_ket,
    Matrix.one_mulVec]
  apply congrArg UnsignedGivens.ket
  simp only [Function.update_of_ne h₁t, Function.update_of_ne h₂t, Function.update_self,
    UnsignedGivens.zmod2_add_cancel_right]
  funext w; by_cases hw : w = t <;> simp [hw]

theorem SubspaceStepU_of_andUncompute {Var : Type} [Fintype Var] [DecidableEq Var]
    {n : ℕ} {R₁ : Operator (2 ^ n)} (v : Var) (c₁ c₂ anc : Wire n)
    (h₁₂ : c₁ ≠ c₂) (h₁a : c₁ ≠ anc) (h₂a : c₂ ≠ anc)
    (hClean : (QRegister.singleton anc).basisOutcomeProjector 0 * R₁ = R₁) :
    SubspaceStepU ((Circuit.TOFF c₁ c₂ anc h₁₂ h₁a h₂a).eval.1 * R₁) R₁
      (DynamicCircuit.andUncompute v c₁ c₂ anc h₁₂) := fun M ↦ by
  have : NeZero (2 ^ n) := ⟨Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos n)⟩
  obtain ⟨M', hwp⟩ := UnsignedGivens.PreservesStoreConst.andUncompute v c₁ c₂ anc h₁₂ M
  let P₀ := (QRegister.singleton anc).basisOutcomeProjector 0
  have hPherm : P₀ᴴ = P₀ := QRegister.basisOutcomeProjector_conjTranspose _ 0
  have hadj : R₁ᴴ * P₀ = R₁ᴴ := by
    have hc : P₀ * R₁ = R₁ := hClean
    simpa only [Matrix.conjTranspose_mul, hPherm] using congrArg (·ᴴ) hc
  have hrest := congrArg (fun x : Observable (Fin (2 ^ n)) ↦ x.1)
    (congrFun
      (DynamicCircuit.qc_wp_toffoli_andUncompute_of_update_eq
        v c₁ c₂ anc h₁₂ h₁a h₂a (fun _ ↦ M) (fun _ _ ↦ rfl)) (fun _ ↦ 0))
  rw [hwp] at hrest
  simp only [restrictAssertionToZeroAncilla_coe, qcWpQAssign, qcQAssignObsMap,
    Observable.conj_coe, Unitary.coe_star, Matrix.star_eq_conjTranspose] at hrest
  refine ⟨M', hwp, ?_⟩
  generalize (Circuit.TOFF c₁ c₂ anc h₁₂ h₁a h₂a).eval = U₂ at hrest ⊢
  have hmat : P₀ * (U₂.1ᴴ * M'.1.1 * U₂.1) * P₀ = P₀ * M.1.1 * P₀ := by
    have hv : (M'.1.conj U₂.1ᴴ).conj P₀ = M.1.conj P₀ := hrest
    have hv1 := congrArg Subtype.val hv
    change P₀ * (U₂.1ᴴ * M'.1.1 * U₂.1ᴴᴴ) * P₀ᴴ = P₀ * M.1.1 * P₀ᴴ at hv1
    simpa only [Matrix.conjTranspose_conjTranspose, hPherm] using hv1
  calc (U₂.1 * R₁)ᴴ * M'.1.1 * (U₂.1 * R₁)
      = (R₁ᴴ * P₀) * U₂.1ᴴ * M'.1.1 * U₂.1 * (P₀ * R₁) := by
          rw [hadj, hClean, Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = R₁ᴴ * (P₀ * (U₂.1ᴴ * M'.1.1 * U₂.1) * P₀) * R₁ := by simp only [Matrix.mul_assoc]
    _ = R₁ᴴ * (P₀ * M.1.1 * P₀) * R₁ := by rw [hmat]
    _ = (R₁ᴴ * P₀) * M.1.1 * (P₀ * R₁) := by simp only [Matrix.mul_assoc]
    _ = R₁ᴴ * M.1.1 * R₁ := by rw [hadj, hClean]

theorem SubspaceStepU_of_andUncompute_fwd {Var : Type} [Fintype Var] [DecidableEq Var]
    {n : ℕ} {R₀ : Operator (2 ^ n)} (v : Var) (c₁ c₂ anc : Wire n)
    (h₁₂ : c₁ ≠ c₂) (h₁a : c₁ ≠ anc) (h₂a : c₂ ≠ anc)
    (hClean : (QRegister.singleton anc).basisOutcomeProjector 0 *
      ((Circuit.TOFF c₁ c₂ anc h₁₂ h₁a h₂a).eval.1 * R₀) =
      (Circuit.TOFF c₁ c₂ anc h₁₂ h₁a h₂a).eval.1 * R₀) :
    SubspaceStepU R₀ ((Circuit.TOFF c₁ c₂ anc h₁₂ h₁a h₂a).eval.1 * R₀)
      (DynamicCircuit.andUncompute v c₁ c₂ anc h₁₂) := by
  refine (SubspaceStepU_of_andUncompute v c₁ c₂ anc h₁₂ h₁a h₂a hClean).congr ?_ rfl
  rw [← Matrix.mul_assoc, toffoli_eval_mul_self, Matrix.one_mul]

theorem SubspaceStepU_wrapDynamic_ref {Var : Type} [Fintype Var] [DecidableEq Var]
    {n : ℕ} {R₀ : Operator (2 ^ n)} (v : Var) (s : UnsignedGivens.PhasedStep n)
    (c_in : Circuit n) (d_in : DynamicCircuit Var n)
    (h0 : (QRegister.singleton s.anc).basisOutcomeProjector 0 * (s.pre.eval.1 * R₀) =
      s.pre.eval.1 * R₀)
    (h_in :
      let R_in := s.midPre.eval.1 *
        ((Circuit.TOFF s.c₁ s.c₂ s.anc s.h₁₂ s.h₁a s.h₂a).eval.1 * (s.pre.eval.1 * R₀))
      SubspaceStepU R_in (c_in.eval.1 * R_in) d_in)
    (h1 :
      let R_in := s.midPre.eval.1 *
        ((Circuit.TOFF s.c₁ s.c₂ s.anc s.h₁₂ s.h₁a s.h₂a).eval.1 * (s.pre.eval.1 * R₀))
      let R_bwd := (Circuit.TOFF s.c₁ s.c₂ s.anc s.h₁₂ s.h₁a s.h₂a).eval.1 *
        (s.midPost.eval.1 * (c_in.eval.1 * R_in))
      (QRegister.singleton s.anc).basisOutcomeProjector 0 * R_bwd = R_bwd) :
    SubspaceStepU R₀ ((s.wrapCircuit c_in).eval.1 * R₀) (s.wrapDynamic v d_in) := by
  dsimp only [UnsignedGivens.PhasedStep.wrapDynamic]
  let T_anc := Circuit.TOFF s.c₁ s.c₂ s.anc s.h₁₂ s.h₁a s.h₂a
  let R₁ := s.pre.eval.1 * R₀
  let R₂ := T_anc.eval.1 * R₁
  let R_in := s.midPre.eval.1 * R₂
  let R₄ := s.midPost.eval.1 * (c_in.eval.1 * R_in)
  have hs1 := SubspaceStepU.of_circuit (Var := Var) (R₀ := R₀) s.pre rfl
  have hs2 := SubspaceStepU.of_andCompute (Var := Var) s.c₁ s.c₂ s.anc s.h₁₂ s.h₁a s.h₂a h0
  have hs3 := SubspaceStepU.of_circuit (Var := Var) (R₀ := R₂) s.midPre rfl
  have hs5 := SubspaceStepU.of_circuit (Var := Var) (R₀ := c_in.eval.1 * R_in) s.midPost rfl
  have hs6 := SubspaceStepU_of_andUncompute_fwd (R₀ := R₄) v s.c₁ s.c₂ s.anc s.h₁₂ s.h₁a s.h₂a h1
  have hs7 := SubspaceStepU.of_circuit (Var := Var) (R₀ := T_anc.eval.1 * R₄) s.post rfl
  refine (hs1.seq ((hs2.seq ((hs3.seq (h_in.seq hs5)).seq hs6)).seq hs7)).congr rfl ?_
  dsimp only [UnsignedGivens.PhasedStep.wrapCircuit, T_anc, R₁, R₂, R_in, R₄]
  simp only [Circuit.eval_seq, Submonoid.coe_mul, Matrix.mul_assoc]

theorem SubspaceStepU_cleanBitStep_wrap {Var : Type} [Fintype Var] [DecidableEq Var]
    {n : ℕ} {R₀ : Operator (2 ^ n)} (v : Var)
    {s : UnsignedGivens.PhasedStep n} {bitVal : BitAssignment n → ZMod 2} {S_ctrl : Finset (Wire n)}
    (hs : UnsignedGivens.IsCleanBitStep s bitVal S_ctrl)
    {c_in : Circuit n} {φ_in : BitAssignment n → ℂ} {f_in : BitAssignment n → BitAssignment n}
    (hperm_in : UnsignedGivens.PhasedPerm c_in φ_in f_in)
    (hfix_anc : ∀ β, f_in β s.anc = β s.anc)
    (hfix_ctrl : ∀ β w, w ∈ S_ctrl → f_in β w = β w)
    (h_anc0 : (QRegister.singleton s.anc).basisOutcomeProjector 0 * R₀ = R₀)
    (d_in : DynamicCircuit Var n)
    (h_in :
      let R_in := s.midPre.eval.1 *
        ((Circuit.TOFF s.c₁ s.c₂ s.anc s.h₁₂ s.h₁a s.h₂a).eval.1 * (s.pre.eval.1 * R₀))
      SubspaceStepU R_in (c_in.eval.1 * R_in) d_in) :
    SubspaceStepU R₀ ((s.wrapCircuit c_in).eval.1 * R₀) (s.wrapDynamic v d_in) := by
  let P₀ := (QRegister.singleton s.anc).basisOutcomeProjector 0
  have hpre_disj : Disjoint s.pre.support (QRegister.singleton s.anc).image := by
    rw [QRegister.image_singleton, Finset.disjoint_singleton_right]; exact hs.anc_not_mem_pre
  have hpre_comm := UnsignedGivens.eval_comm_basisOutcomeProjector_of_disjoint_support s.pre
    (QRegister.singleton s.anc) hpre_disj 0
  have h0 : P₀ * (s.pre.eval.1 * R₀) = s.pre.eval.1 * R₀ := by
    rw [← Matrix.mul_assoc, ← hpre_comm, Matrix.mul_assoc, h_anc0]
  have hbwd := (UnsignedGivens.cleanBitStep_wrap_spec hs hperm_in hfix_anc hfix_ctrl).2.2.2
  refine SubspaceStepU_wrapDynamic_ref v s c_in d_in h0 h_in ?_
  dsimp only
  let T_anc := (Circuit.TOFF s.c₁ s.c₂ s.anc s.h₁₂ s.h₁a s.h₂a).eval.1
  have hbody : (s.midPre ;;ᶜ c_in ;;ᶜ s.midPost).eval.1 =
      s.midPost.eval.1 * c_in.eval.1 * s.midPre.eval.1 := by
    simp only [Circuit.eval_seq, Submonoid.coe_mul, Matrix.mul_assoc]
  calc P₀ * (T_anc * (s.midPost.eval.1 * (c_in.eval.1 *
          (s.midPre.eval.1 * (T_anc * (s.pre.eval.1 * R₀))))))
      = (P₀ * (T_anc * (s.midPre ;;ᶜ c_in ;;ᶜ s.midPost).eval.1 * T_anc * P₀)) *
          (s.pre.eval.1 * R₀) := by rw [hbody]; nth_rw 1 [← h0]; simp only [Matrix.mul_assoc]
    _ = T_anc * (s.midPost.eval.1 * (c_in.eval.1 *
          (s.midPre.eval.1 * (T_anc * (s.pre.eval.1 * R₀))))) := by
          rw [hbwd, hbody]; simp only [Matrix.mul_assoc]; rw [h0]

theorem singleton_proj_zero_mul_eval_mul_work_eq {m n : ℕ}
    (q : Wire n) (rWork : QRegister m n) (c : Circuit n)
    {φ : BitAssignment n → ℂ} {f : BitAssignment n → BitAssignment n}
    (hp : UnsignedGivens.PhasedPerm c φ f)
    (hq0 : ∀ β : BitAssignment n, (∀ i : Fin m, β (rWork i) = 0) → f β q = 0) :
    (QRegister.singleton q).basisOutcomeProjector 0 * (c.eval.1 * rWork.basisOutcomeProjector 0) =
      c.eval.1 * rWork.basisOutcomeProjector 0 := by
  apply UnsignedGivens.matrix_ext_ket; intro β
  simp only [← Matrix.mulVec_mulVec, UnsignedGivens.register_basisOutcomeProjector_zero_ket]
  by_cases h0 : ∀ i : Fin m, β (rWork i) = 0
  · rw [ite_eq_left_of_eq_true _ _ (eq_true h0), hp β, Matrix.mulVec_smul,
      UnsignedGivens.basisOutcomeProjector_zero_ket,
        ite_eq_left_of_eq_true _ _ (eq_true (hq0 β h0))]
  · rw [ite_eq_right_of_eq_false _ _ (eq_false h0), Matrix.mulVec_zero, Matrix.mulVec_zero]

theorem realizesCleanRef_of_subspaceStepU {Var : Type} [Fintype Var] [DecidableEq Var]
    {n m : ℕ} [NeZero (2 ^ n)] (rWork : QRegister m n) (c_ref : Circuit n)
    (d_prog : DynamicCircuit Var n)
    (hclean : c_ref.eval.1 * rWork.basisOutcomeProjector 0 =
      rWork.basisOutcomeProjector 0 * c_ref.eval.1 * rWork.basisOutcomeProjector 0)
    (hStep : SubspaceStepU (rWork.basisOutcomeProjector 0)
      (c_ref.eval.1 * rWork.basisOutcomeProjector 0) d_prog) :
    UnsignedGivens.RealizesCleanRef rWork c_ref d_prog := by
  let P₀ := rWork.basisOutcomeProjector 0
  have hPherm : P₀ᴴ = P₀ := rWork.basisOutcomeProjector_conjTranspose 0
  refine ⟨hclean, fun M ↦ ?_⟩
  obtain ⟨M', hwp, heq⟩ := hStep M
  refine ⟨M', hwp, ?_⟩
  calc P₀ * M'.1.1 * P₀ = P₀ᴴ * M'.1.1 * P₀ := by rw [hPherm]
    _ = (c_ref.eval.1 * P₀)ᴴ * M.1.1 * (c_ref.eval.1 * P₀) := heq
    _ = P₀ * (c_ref.eval.1ᴴ * M.1.1 * c_ref.eval.1) * P₀ := by
          rw [Matrix.conjTranspose_mul, hPherm]; simp only [Matrix.mul_assoc]

/-- Forward 4-wire Gidney carry-compute block (`CNOT` pre + `TOFF` + `CNOT` carry). -/
def gFwd4 {n : ℕ} (wy wa wc wp : Wire n)
    (hya : wy ≠ wa) (hyc : wy ≠ wc) (hac : wa ≠ wc)
    (hyp : wy ≠ wp) (hap : wa ≠ wp) (hcp : wc ≠ wp) : Circuit n :=
  (Circuit.CNOT wp wy hyp.symm ;;ᶜ Circuit.CNOT wp wa hap.symm) ;;ᶜ
  Circuit.TOFF wy wa wc hya hyc hac ;;ᶜ
  Circuit.CNOT wp wc hcp.symm

/-- Mid-step bit assignment produced by `gFwd4` (or `TOFF` when `cp = 0`). -/
def gMidAssign {n : ℕ} (wy wa wc : Wire n) (cp : ZMod 2) (β : BitAssignment n) :
    BitAssignment n :=
  Function.update
    (Function.update (Function.update β wy (β wy + cp)) wa (β wa + cp))
    wc (β wc + ((β wy + cp) * (β wa + cp) + cp))

theorem evolve_gFwd4_ket {n : ℕ} (wy wa wc wp : Wire n)
    (hya : wy ≠ wa) (hyc : wy ≠ wc) (hac : wa ≠ wc)
    (hyp : wy ≠ wp) (hap : wa ≠ wp) (hcp : wc ≠ wp) (β : BitAssignment n) :
    (gFwd4 wy wa wc wp hya hyc hac hyp hap hcp).eval.1.mulVec (UnsignedGivens.ket β) =
      UnsignedGivens.ket (gMidAssign wy wa wc (β wp) β) := by
  dsimp only [gFwd4, gMidAssign]
  simp only [UnsignedGivens.eval_seq_mulVec, UnsignedGivens.evolve_CNOT_ket,
    UnsignedGivens.evolve_TOFF_ket]
  apply congrArg UnsignedGivens.ket; funext w
  rw [Function.update_of_ne hya.symm, Function.update_of_ne hyp.symm]
  set β₁ := Function.update (Function.update β wy (β wy + β wp)) wa (β wa + β wp)
  have h1y : β₁ wy = β wy + β wp := by simp [β₁, Function.update_of_ne hya]
  have h1a : β₁ wa = β wa + β wp := by simp [β₁]
  have h1c : β₁ wc = β wc := by
    simp [β₁, Function.update_of_ne hac.symm, Function.update_of_ne hyc.symm]
  have h1p : β₁ wp = β wp := by
    simp [β₁, Function.update_of_ne hap.symm, Function.update_of_ne hyp.symm]
  rw [h1y, h1a, h1c]
  have h2p : Function.update β₁ wc (β wc + (β wy + β wp) * (β wa + β wp)) wp = β wp := by
    rw [Function.update_of_ne hcp.symm, h1p]
  rw [h2p, Function.update_self, Function.update_idem, add_assoc]

/-- Backward 4-wire Gidney carry-uncompute and sum block. -/
def gBwd4 {n : ℕ} (wy wa wc wp : Wire n)
    (hya : wy ≠ wa) (hyc : wy ≠ wc) (hac : wa ≠ wc)
    (hap : wa ≠ wp) (hcp : wc ≠ wp) : Circuit n :=
  Circuit.CNOT wp wc hcp.symm ;;ᶜ
  Circuit.TOFF wy wa wc hya hyc hac ;;ᶜ
  (Circuit.CNOT wp wa hap.symm ;;ᶜ Circuit.CNOT wa wy hya.symm)

theorem evolve_gBwd4_ket {n : ℕ} (wy wa wc wp : Wire n)
    (hya : wy ≠ wa) (hyc : wy ≠ wc) (hac : wa ≠ wc)
    (hap : wa ≠ wp) (hcp : wc ≠ wp)
    (γ : BitAssignment n) (y0 a0 c0 cp : ZMod 2)
    (hy : γ wy = y0 + cp) (ha : γ wa = a0 + cp)
    (hc : γ wc = c0 + ((y0 + cp) * (a0 + cp) + cp)) (hp : γ wp = cp) :
    (gBwd4 wy wa wc wp hya hyc hac hap hcp).eval.1.mulVec (UnsignedGivens.ket γ) =
      UnsignedGivens.ket (Function.update (Function.update (Function.update γ wc c0) wa a0)
        wy (y0 + cp + a0)) := by
  dsimp only [gBwd4]
  simp only [UnsignedGivens.eval_seq_mulVec, UnsignedGivens.evolve_CNOT_ket,
    UnsignedGivens.evolve_TOFF_ket]
  apply congrArg UnsignedGivens.ket
  rw [hc, hp, ← add_assoc, UnsignedGivens.zmod2_add_cancel_right]
  set γ₁ := Function.update γ wc (c0 + (y0 + cp) * (a0 + cp))
  have h1y : γ₁ wy = y0 + cp := by simp [γ₁, Function.update_of_ne hyc, hy]
  have h1a : γ₁ wa = a0 + cp := by simp [γ₁, Function.update_of_ne hac, ha]
  have h1c : γ₁ wc = c0 + (y0 + cp) * (a0 + cp) := by simp [γ₁]
  rw [h1y, h1a, h1c, Function.update_idem, UnsignedGivens.zmod2_add_cancel_right]
  set γ₂ := Function.update γ wc c0
  have h2a : γ₂ wa = a0 + cp := by simp [γ₂, Function.update_of_ne hac, ha]
  have h2p : γ₂ wp = cp := by simp [γ₂, Function.update_of_ne hcp.symm, hp]
  rw [h2a, h2p, UnsignedGivens.zmod2_add_cancel_right]
  set γ₃ := Function.update γ₂ wa a0
  have h3y : γ₃ wy = y0 + cp := by
    simp [γ₃, γ₂, Function.update_of_ne hya, Function.update_of_ne hyc, hy]
  have h3a : γ₃ wa = a0 := by simp [γ₃]
  rw [h3y, h3a]

/-- Backward 3-wire Gidney sum block (`j = 0`). -/
def gBwd3 {n : ℕ} (wy wa wc : Wire n) (hya : wy ≠ wa) (hyc : wy ≠ wc) (hac : wa ≠ wc) :
    Circuit n :=
  Circuit.TOFF wy wa wc hya hyc hac ;;ᶜ Circuit.CNOT wa wy hya.symm

theorem evolve_gBwd3_ket {n : ℕ} (wy wa wc : Wire n)
    (hya : wy ≠ wa) (hyc : wy ≠ wc) (hac : wa ≠ wc)
    (γ : BitAssignment n) (y0 a0 c0 : ZMod 2)
    (hy : γ wy = y0) (ha : γ wa = a0) (hc : γ wc = c0 + y0 * a0) :
    (gBwd3 wy wa wc hya hyc hac).eval.1.mulVec (UnsignedGivens.ket γ) =
      UnsignedGivens.ket (Function.update (Function.update (Function.update γ wc c0) wa a0)
        wy (y0 + 0 + a0)) := by
  dsimp only [gBwd3]
  simp only [UnsignedGivens.eval_seq_mulVec, UnsignedGivens.evolve_CNOT_ket,
    UnsignedGivens.evolve_TOFF_ket, add_zero]
  apply congrArg UnsignedGivens.ket
  rw [hy, ha, hc, UnsignedGivens.zmod2_add_cancel_right]
  set γ₁ := Function.update γ wc c0
  have h1y : γ₁ wy = y0 := by simp [γ₁, Function.update_of_ne hyc, hy]
  have h1a : γ₁ wa = a0 := by simp [γ₁, Function.update_of_ne hac, ha]
  rw [h1y, h1a]; funext w
  by_cases hwy : w = wy
  · subst hwy; simp
  · by_cases hwa : w = wa
    · subst hwa; simp [hwy, h1a]
    · simp [Function.update_of_ne hwy, Function.update_of_ne hwa]

theorem evolve_gidneyFwd4_ket {n : ℕ} (wy wa wc wp : Wire n)
    (hya : wy ≠ wa) (hyc : wy ≠ wc) (hac : wa ≠ wc)
    (hyp : wy ≠ wp) (hap : wa ≠ wp) (hcp : wc ≠ wp) (β : BitAssignment n) :
    (gFwd4 wy wa wc wp hya hyc hac hyp hap hcp ;;ᶜ
      (Circuit.CNOT wp wa hap.symm ;;ᶜ
        Circuit.CNOT wp wy hyp.symm)).eval.1.mulVec (UnsignedGivens.ket β) =
      UnsignedGivens.ket (Function.update β wc
        (β wc + ((β wy + β wp) * (β wa + β wp) + β wp))) := by
  rw [UnsignedGivens.eval_seq_mulVec, evolve_gFwd4_ket, UnsignedGivens.eval_seq_mulVec,
    UnsignedGivens.evolve_CNOT_ket, UnsignedGivens.evolve_CNOT_ket]
  apply congrArg UnsignedGivens.ket; funext w; dsimp only [gMidAssign]
  by_cases hwc : w = wc
  · subst hwc; simp [Function.update_of_ne hyc.symm, Function.update_of_ne hac.symm]
  · by_cases hwa : w = wa
    · subst hwa
      simp [hwc, Function.update_of_ne hya.symm, Function.update_of_ne hcp.symm,
        Function.update_of_ne hap.symm, Function.update_of_ne hyp.symm]
    · by_cases hwy : w = wy
      · subst hwy
        simp [hwc, hwa, Function.update_of_ne hcp.symm, Function.update_of_ne hap.symm,
          Function.update_of_ne hyp.symm]
      · simp [Function.update_of_ne hwc, Function.update_of_ne hwa, Function.update_of_ne hwy]

theorem evolve_gidneyBwd4_ket {n : ℕ} (wy wa wc wp : Wire n)
    (hya : wy ≠ wa) (hyc : wy ≠ wc) (hac : wa ≠ wc)
    (hyp : wy ≠ wp) (hap : wa ≠ wp) (hcp : wc ≠ wp)
    (γ : BitAssignment n) (c0 : ZMod 2)
    (hc : γ wc = c0 + ((γ wy + γ wp) * (γ wa + γ wp) + γ wp)) :
    ((Circuit.CNOT wp wy hyp.symm ;;ᶜ Circuit.CNOT wp wa hap.symm) ;;ᶜ
      gBwd4 wy wa wc wp hya hyc hac hap hcp).eval.1.mulVec (UnsignedGivens.ket γ) =
      UnsignedGivens.ket (Function.update (Function.update γ wc c0) wy (γ wy + γ wp + γ wa)) := by
  rw [UnsignedGivens.eval_seq_mulVec, UnsignedGivens.eval_seq_mulVec,
    UnsignedGivens.evolve_CNOT_ket, UnsignedGivens.evolve_CNOT_ket,
    Function.update_of_ne hya.symm, Function.update_of_ne hyp.symm]
  set γ' := Function.update (Function.update γ wy (γ wy + γ wp)) wa (γ wa + γ wp)
  rw [evolve_gBwd4_ket wy wa wc wp hya hyc hac hap hcp γ' (γ wy) (γ wa) c0 (γ wp)
    (by simp [γ', Function.update_of_ne hya]) (by simp [γ'])
    (by simp [γ', Function.update_of_ne hac.symm, Function.update_of_ne hyc.symm, hc])
    (by simp [γ', Function.update_of_ne hap.symm, Function.update_of_ne hyp.symm])]
  apply congrArg UnsignedGivens.ket; funext w
  by_cases hwy : w = wy
  · subst hwy; simp
  · by_cases hwa : w = wa
    · subst hwa; simp [hwy, Function.update_of_ne hac]
    · by_cases hwc : w = wc
      · subst hwc; simp [hwy, hwa]
      · simp [γ', Function.update_of_ne hwy, Function.update_of_ne hwa, Function.update_of_ne hwc]

/-! ## Section 1B: Streamed-`rA` Gidney Unsigned Phase-Kick Engine (`0 ≤ d < B`) -/

/-- Pairwise disjointness witness for the compact `(B - d)`-ancilla Gidney phase-kick engine. -/
structure CompactGidneyDisjoint {n B d : ℕ} (rCat : QRegister B n) (rASh : QRegister (B - d) n)
    (rC : QRegister B n) (w_p : Wire n) : Prop where
  disj_cat_A : rCat.DisjointWires rASh
  disj_cat_C : rCat.DisjointWires rC
  disj_A_C : rASh.DisjointWires rC
  ne_cat_wp : ∀ i, rCat i ≠ w_p
  ne_A_wp : ∀ i, rASh i ≠ w_p
  ne_C_wp : ∀ i, rC i ≠ w_p

namespace CompactGidneyDisjoint

theorem ne_cat_A {n B d : ℕ} {rCat : QRegister B n} {rASh : QRegister (B - d) n}
    {rC : QRegister B n} {w_p : Wire n} (h : CompactGidneyDisjoint rCat rASh rC w_p)
    (i : Fin B) (j : Fin (B - d)) : rCat i ≠ rASh j := QRegister.disjoint_iff.mp h.disj_cat_A i j

theorem ne_cat_C {n B d : ℕ} {rCat : QRegister B n} {rASh : QRegister (B - d) n}
    {rC : QRegister B n} {w_p : Wire n} (h : CompactGidneyDisjoint rCat rASh rC w_p)
    (i j : Fin B) : rCat i ≠ rC j := QRegister.disjoint_iff.mp h.disj_cat_C i j

theorem ne_A_C {n B d : ℕ} {rCat : QRegister B n} {rASh : QRegister (B - d) n}
    {rC : QRegister B n} {w_p : Wire n} (h : CompactGidneyDisjoint rCat rASh rC w_p)
    (i : Fin (B - d)) (j : Fin B) : rASh i ≠ rC j := QRegister.disjoint_iff.mp h.disj_A_C i j

end CompactGidneyDisjoint

/-- Target `rASh` wire for bit `j < B`: `rASh 0` for `j < d`, and `rASh (j - d)` for `d ≤ j < B`. -/
def ancSh {n B : ℕ} (d : ℕ) (hdB : d < B) (rASh : QRegister (B - d) n) (j : Fin B) : Wire n :=
  if j.val < d then rASh ⟨0, by omega⟩ else rASh ⟨j.val - d, by omega⟩

/-- Bundle of `(B + 2)` clean bit-loader steps targeting `rASh : QRegister (B - d) n`. -/
structure CompactPhaseKickBitSteps {n B d : ℕ} (hdB : d < B) (rCat : QRegister B n)
    (rASh : QRegister (B - d) n) (rC : QRegister B n) (w_p : Wire n)
    (S_ctrl : Finset (Wire n)) where
  stepTop : UnsignedGivens.PhasedStep n
  stepMid : UnsignedGivens.PhasedStep n
  stepLo : Fin B → UnsignedGivens.PhasedStep n
  bitTop : BitAssignment n → ZMod 2
  bitMid : BitAssignment n → ZMod 2
  bitLo : BitAssignment n → Fin B → ZMod 2
  ancTop : stepTop.anc = rASh ⟨0, by omega⟩
  ancMid : stepMid.anc = rASh ⟨0, by omega⟩
  ancLo : ∀ j : Fin B, (stepLo j).anc = ancSh d hdB rASh j
  cleanTop : UnsignedGivens.IsCleanBitStep stepTop bitTop S_ctrl
  cleanMid : UnsignedGivens.IsCleanBitStep stepMid bitMid S_ctrl
  cleanLo : ∀ j : Fin B, UnsignedGivens.IsCleanBitStep (stepLo j) (fun β => bitLo β j) S_ctrl
  disj_ctrl_wp : w_p ∉ S_ctrl
  disj_ctrl_cat : Disjoint S_ctrl rCat.image
  disj_ctrl_A : Disjoint S_ctrl rASh.image
  disj_ctrl_C : Disjoint S_ctrl rC.image

section CompactKickDefs

variable {Var : Type} {n B d : ℕ}

/-- Resident Gidney `PhasedStep` at bit `d ≤ j < B` using `rASh ⟨j - d, _⟩` (`4 T`, `0 TOFF`). -/
def gidneyResidBitStep (rCat : QRegister B n) (rASh : QRegister (B - d) n) (rC : QRegister B n)
    (w_p : Wire n) (hd : CompactGidneyDisjoint rCat rASh rC w_p)
    (j : ℕ) (hdj : d ≤ j) (hj : j < B) : UnsignedGivens.PhasedStep n :=
  let jf : Fin B := ⟨j, hj⟩
  let ja : Fin (B - d) := ⟨j - d, by omega⟩
  if h0 : 0 < j then
    let jprev : Fin B := ⟨j - 1, by omega⟩
    have hpne : jprev ≠ jf := by
      intro heq; have := congrArg Fin.val heq; dsimp [jprev, jf] at this; omega
    { c₁ := rCat jf, c₂ := rASh ja, anc := rC jf
      h₁₂ := hd.ne_cat_A jf ja, h₁a := hd.ne_cat_C jf jf, h₂a := hd.ne_A_C ja jf
      pre := Circuit.CNOT (rC jprev) (rCat jf) (hd.ne_cat_C jf jprev).symm ;;ᶜ
             Circuit.CNOT (rC jprev) (rASh ja) (hd.ne_A_C ja jprev).symm
      midPre := Circuit.CNOT (rC jprev) (rC jf) (UnsignedGivens.GidneyKickDisjoint.ne_C_C rC hpne)
      midPost := Circuit.CNOT (rC jprev) (rC jf) (UnsignedGivens.GidneyKickDisjoint.ne_C_C rC hpne)
      post := Circuit.CNOT (rC jprev) (rASh ja) (hd.ne_A_C ja jprev).symm ;;ᶜ
              Circuit.CNOT (rASh ja) (rCat jf) (hd.ne_cat_A jf ja).symm }
  else
    { c₁ := rCat jf, c₂ := rASh ja, anc := rC jf
      h₁₂ := hd.ne_cat_A jf ja, h₁a := hd.ne_cat_C jf jf, h₂a := hd.ne_A_C ja jf
      pre := .identity, midPre := .identity, midPost := .identity
      post := Circuit.CNOT (rASh ja) (rCat jf) (hd.ne_cat_A jf ja).symm }

theorem isCliffordWrapper_gidneyResidBitStep (rCat : QRegister B n) (rASh : QRegister (B - d) n)
    (rC : QRegister B n) (w_p : Wire n) (hd : CompactGidneyDisjoint rCat rASh rC w_p)
    (j : ℕ) (hdj : d ≤ j) (hj : j < B) :
    (gidneyResidBitStep rCat rASh rC w_p hd j hdj hj).IsCliffordWrapper := by
  by_cases h0 : 0 < j <;> simp [gidneyResidBitStep, UnsignedGivens.PhasedStep.IsCliffordWrapper, h0]

/-- Resident suffix `rem ≤ B - d` (`j = B - rem .. B - 1`) wrapping `parityTCircuit`. -/
def gidneyResidSuffixDyn (v : Var) (hdB : d < B) (rCat : QRegister B n)
    (rASh : QRegister (B - d) n) (rC : QRegister B n) (w_p : Wire n)
    (hd : CompactGidneyDisjoint rCat rASh rC w_p) :
    (rem : ℕ) → rem ≤ B - d → DynamicCircuit Var n
  | 0, _ => .circuit
      (UnsignedGivens.parityTCircuit (rC ⟨B - 1, by omega⟩) w_p (hd.ne_C_wp ⟨B - 1, by omega⟩))
  | rem + 1, _ =>
      (gidneyResidBitStep rCat rASh rC w_p hd (B - (rem + 1)) (by omega) (by omega)).wrapDynamic v
        (gidneyResidSuffixDyn v hdB rCat rASh rC w_p hd rem (by omega))

/-- Reference pure `Circuit n` for `gidneyResidSuffixDyn`. -/
def gidneyResidSuffixRef (hdB : d < B) (rCat : QRegister B n) (rASh : QRegister (B - d) n)
    (rC : QRegister B n) (w_p : Wire n) (hd : CompactGidneyDisjoint rCat rASh rC w_p) :
    (rem : ℕ) → rem ≤ B - d → Circuit n
  | 0, _ => UnsignedGivens.parityTCircuit (rC ⟨B - 1, by omega⟩) w_p (hd.ne_C_wp ⟨B - 1, by omega⟩)
  | rem + 1, _ =>
      (gidneyResidBitStep rCat rASh rC w_p hd (B - (rem + 1)) (by omega) (by omega)).wrapCircuit
        (gidneyResidSuffixRef hdB rCat rASh rC w_p hd rem (by omega))

/-- Resident loader for `rem ≤ B - d` bits `B - rem .. B - 1` wrapping `gidneyResidSuffixDyn`. -/
def loadResidSuffixDyn (v : Var) (hdB : d < B) (rCat : QRegister B n)
    (rASh : QRegister (B - d) n) (rC : QRegister B n) (w_p : Wire n)
    (hd : CompactGidneyDisjoint rCat rASh rC w_p) {S_ctrl : Finset (Wire n)}
    (bs : CompactPhaseKickBitSteps hdB rCat rASh rC w_p S_ctrl) :
    (rem : ℕ) → rem ≤ B - d → DynamicCircuit Var n
  | 0, _ => gidneyResidSuffixDyn v hdB rCat rASh rC w_p hd (B - d) le_rfl
  | rem + 1, _ =>
      (bs.stepLo ⟨B - (rem + 1), by omega⟩).wrapDynamic v
        (loadResidSuffixDyn v hdB rCat rASh rC w_p hd bs rem (by omega))

/-- Reference pure `Circuit n` for `loadResidSuffixDyn`. -/
def loadResidSuffixRef (hdB : d < B) (rCat : QRegister B n) (rASh : QRegister (B - d) n)
    (rC : QRegister B n) (w_p : Wire n) (hd : CompactGidneyDisjoint rCat rASh rC w_p)
    {S_ctrl : Finset (Wire n)} (bs : CompactPhaseKickBitSteps hdB rCat rASh rC w_p S_ctrl) :
    (rem : ℕ) → rem ≤ B - d → Circuit n
  | 0, _ => gidneyResidSuffixRef hdB rCat rASh rC w_p hd (B - d) le_rfl
  | rem + 1, _ =>
      (bs.stepLo ⟨B - (rem + 1), by omega⟩).wrapCircuit
        (loadResidSuffixRef hdB rCat rASh rC w_p hd bs rem (by omega))

/-- Forward carry-compute body at streamed bit `j < d` using `a0 = rASh 0` (`4 T`, `0 TOFF`). -/
def gidneyFwdDyn (hdB : d < B) (rCat : QRegister B n) (rASh : QRegister (B - d) n)
    (rC : QRegister B n) (w_p : Wire n) (hd : CompactGidneyDisjoint rCat rASh rC w_p)
    (j : ℕ) (hjd : j < d) : DynamicCircuit Var n :=
  let jf : Fin B := ⟨j, by omega⟩
  let i0 : Fin (B - d) := ⟨0, by omega⟩
  if h0 : 0 < j then
    let jprev : Fin B := ⟨j - 1, by omega⟩
    have hpne : jprev ≠ jf := by
      intro heq; have := congrArg Fin.val heq; dsimp [jprev, jf] at this; omega
    .seq
      (.circuit (Circuit.CNOT (rC jprev) (rCat jf) (hd.ne_cat_C jf jprev).symm ;;ᶜ
                 Circuit.CNOT (rC jprev) (rASh i0) (hd.ne_A_C i0 jprev).symm))
      (.seq (DynamicCircuit.andCompute (rCat jf) (rASh i0) (rC jf) (hd.ne_cat_C jf jf)
              (hd.ne_A_C i0 jf))
        (.circuit (Circuit.CNOT (rC jprev) (rC jf)
          (UnsignedGivens.GidneyKickDisjoint.ne_C_C rC hpne) ;;ᶜ
          (Circuit.CNOT (rC jprev) (rASh i0) (hd.ne_A_C i0 jprev).symm ;;ᶜ
           Circuit.CNOT (rC jprev) (rCat jf) (hd.ne_cat_C jf jprev).symm))))
  else
    DynamicCircuit.andCompute (rCat jf) (rASh i0) (rC jf) (hd.ne_cat_C jf jf) (hd.ne_A_C i0 jf)

/-- Reference pure `Circuit n` for `gidneyFwdDyn`. -/
def gidneyFwdRef (hdB : d < B) (rCat : QRegister B n) (rASh : QRegister (B - d) n)
    (rC : QRegister B n) (w_p : Wire n) (hd : CompactGidneyDisjoint rCat rASh rC w_p)
    (j : ℕ) (hjd : j < d) : Circuit n :=
  let jf : Fin B := ⟨j, by omega⟩
  let i0 : Fin (B - d) := ⟨0, by omega⟩
  if h0 : 0 < j then
    let jprev : Fin B := ⟨j - 1, by omega⟩
    have hpne : jprev ≠ jf := by
      intro heq; have := congrArg Fin.val heq; dsimp [jprev, jf] at this; omega
    gFwd4 (rCat jf) (rASh i0) (rC jf) (rC jprev) (hd.ne_cat_A jf i0) (hd.ne_cat_C jf jf)
      (hd.ne_A_C i0 jf) (hd.ne_cat_C jf jprev) (hd.ne_A_C i0 jprev)
      (UnsignedGivens.GidneyKickDisjoint.ne_C_C rC hpne).symm ;;ᶜ
    (Circuit.CNOT (rC jprev) (rASh i0) (hd.ne_A_C i0 jprev).symm ;;ᶜ
     Circuit.CNOT (rC jprev) (rCat jf) (hd.ne_cat_C jf jprev).symm)
  else
    Circuit.TOFF (rCat jf) (rASh i0) (rC jf) (hd.ne_cat_A jf i0) (hd.ne_cat_C jf jf)
      (hd.ne_A_C i0 jf)

/-- Backward carry-uncompute and sum body at streamed bit `j < d` (`0 T`, `0 TOFF`). -/
def gidneyBwdDyn (v : Var) (hdB : d < B) (rCat : QRegister B n) (rASh : QRegister (B - d) n)
    (rC : QRegister B n) (w_p : Wire n) (hd : CompactGidneyDisjoint rCat rASh rC w_p)
    (j : ℕ) (hjd : j < d) : DynamicCircuit Var n :=
  let jf : Fin B := ⟨j, by omega⟩
  let i0 : Fin (B - d) := ⟨0, by omega⟩
  if h0 : 0 < j then
    let jprev : Fin B := ⟨j - 1, by omega⟩
    have hpne : jprev ≠ jf := by
      intro heq; have := congrArg Fin.val heq; dsimp [jprev, jf] at this; omega
    .seq
      (.circuit ((Circuit.CNOT (rC jprev) (rCat jf) (hd.ne_cat_C jf jprev).symm ;;ᶜ
                  Circuit.CNOT (rC jprev) (rASh i0) (hd.ne_A_C i0 jprev).symm) ;;ᶜ
                 Circuit.CNOT (rC jprev) (rC jf)
                   (UnsignedGivens.GidneyKickDisjoint.ne_C_C rC hpne)))
      (.seq (DynamicCircuit.andUncompute v (rCat jf) (rASh i0) (rC jf) (hd.ne_cat_A jf i0))
        (.circuit (Circuit.CNOT (rC jprev) (rASh i0) (hd.ne_A_C i0 jprev).symm ;;ᶜ
                   Circuit.CNOT (rASh i0) (rCat jf) (hd.ne_cat_A jf i0).symm)))
  else
    .seq (DynamicCircuit.andUncompute v (rCat jf) (rASh i0) (rC jf) (hd.ne_cat_A jf i0))
      (.circuit (Circuit.CNOT (rASh i0) (rCat jf) (hd.ne_cat_A jf i0).symm))

/-- Reference pure `Circuit n` for `gidneyBwdDyn`. -/
def gidneyBwdRef (hdB : d < B) (rCat : QRegister B n) (rASh : QRegister (B - d) n)
    (rC : QRegister B n) (w_p : Wire n) (hd : CompactGidneyDisjoint rCat rASh rC w_p)
    (j : ℕ) (hjd : j < d) : Circuit n :=
  let jf : Fin B := ⟨j, by omega⟩
  let i0 : Fin (B - d) := ⟨0, by omega⟩
  if h0 : 0 < j then
    let jprev : Fin B := ⟨j - 1, by omega⟩
    have hpne : jprev ≠ jf := by
      intro heq; have := congrArg Fin.val heq; dsimp [jprev, jf] at this; omega
    (Circuit.CNOT (rC jprev) (rCat jf) (hd.ne_cat_C jf jprev).symm ;;ᶜ
     Circuit.CNOT (rC jprev) (rASh i0) (hd.ne_A_C i0 jprev).symm) ;;ᶜ
    gBwd4 (rCat jf) (rASh i0) (rC jf) (rC jprev) (hd.ne_cat_A jf i0) (hd.ne_cat_C jf jf)
      (hd.ne_A_C i0 jf) (hd.ne_A_C i0 jprev) (UnsignedGivens.GidneyKickDisjoint.ne_C_C rC hpne).symm
  else
    gBwd3 (rCat jf) (rASh i0) (rC jf) (hd.ne_cat_A jf i0) (hd.ne_cat_C jf jf) (hd.ne_A_C i0 jf)

/-- Streamed low prefix of `k ≤ d` bits `d - k .. d - 1` wrapping `loadResidSuffixDyn`. -/
def streamedPrefixDyn (v : Var) (hdB : d < B) (rCat : QRegister B n)
    (rASh : QRegister (B - d) n) (rC : QRegister B n) (w_p : Wire n)
    (hd : CompactGidneyDisjoint rCat rASh rC w_p) {S_ctrl : Finset (Wire n)}
    (bs : CompactPhaseKickBitSteps hdB rCat rASh rC w_p S_ctrl) :
    (k : ℕ) → k ≤ d → DynamicCircuit Var n
  | 0, _ => loadResidSuffixDyn v hdB rCat rASh rC w_p hd bs (B - d) le_rfl
  | k + 1, _ =>
      let j := d - (k + 1)
      let jf : Fin B := ⟨j, by omega⟩
      .seq ((bs.stepLo jf).wrapDynamic v (gidneyFwdDyn hdB rCat rASh rC w_p hd j (by omega)))
        (.seq (streamedPrefixDyn v hdB rCat rASh rC w_p hd bs k (by omega))
          ((bs.stepLo jf).wrapDynamic v (gidneyBwdDyn v hdB rCat rASh rC w_p hd j (by omega))))

/-- Reference pure `Circuit n` for `streamedPrefixDyn`. -/
def streamedPrefixRef (hdB : d < B) (rCat : QRegister B n) (rASh : QRegister (B - d) n)
    (rC : QRegister B n) (w_p : Wire n) (hd : CompactGidneyDisjoint rCat rASh rC w_p)
    {S_ctrl : Finset (Wire n)} (bs : CompactPhaseKickBitSteps hdB rCat rASh rC w_p S_ctrl) :
    (k : ℕ) → k ≤ d → Circuit n
  | 0, _ => loadResidSuffixRef hdB rCat rASh rC w_p hd bs (B - d) le_rfl
  | k + 1, _ =>
      let j := d - (k + 1)
      let jf : Fin B := ⟨j, by omega⟩
      (bs.stepLo jf).wrapCircuit (gidneyFwdRef hdB rCat rASh rC w_p hd j (by omega)) ;;ᶜ
      (streamedPrefixRef hdB rCat rASh rC w_p hd bs k (by omega) ;;ᶜ
       (bs.stepLo jf).wrapCircuit (gidneyBwdRef hdB rCat rASh rC w_p hd j (by omega)))

/-- Streamed-ancilla `(B + 2)`-bit unsigned phase-kick engine (`8 * B + 10 + 4 * d` `T`, `0 TOFF`,
workspace `rASh.concat rC` of `2 * B - d` clean wires). -/
def compactRawUnsignedPhaseKickDyn (v : Var) (hdB : d < B) (rCat : QRegister B n)
    (rASh : QRegister (B - d) n) (rC : QRegister B n) (w_p : Wire n)
    (hd : CompactGidneyDisjoint rCat rASh rC w_p) {S_ctrl : Finset (Wire n)}
    (bs : CompactPhaseKickBitSteps hdB rCat rASh rC w_p S_ctrl) : DynamicCircuit Var n :=
  let a0 := rASh ⟨0, by omega⟩
  let kickTop := bs.stepTop.wrapDynamic v
    (.circuit (Circuit.S a0 ;;ᶜ UnsignedGivens.czCircuit w_p a0 (hd.ne_A_wp ⟨0, by omega⟩).symm))
  let kickMid := DynamicCircuit.seq
    (bs.stepMid.wrapDynamic v (.circuit (UnsignedGivens.parityTCircuit a0 w_p (hd.ne_A_wp ⟨0, by
      omega⟩))))
    (.circuit (UnsignedGivens.sdagCircuit w_p))
  let fan := UnsignedGivens.cnotFanoutReg B w_p rCat (fun j => (hd.ne_cat_wp j).symm)
  let kickLo := DynamicCircuit.seq (.circuit fan)
    (DynamicCircuit.seq (streamedPrefixDyn v hdB rCat rASh rC w_p hd bs d le_rfl) (.circuit fan))
  DynamicCircuit.seq kickTop (DynamicCircuit.seq kickMid kickLo)

/-- Reference pure `Circuit n` for `compactRawUnsignedPhaseKickDyn`. -/
def compactRawUnsignedPhaseKickRef (hdB : d < B) (rCat : QRegister B n)
    (rASh : QRegister (B - d) n) (rC : QRegister B n) (w_p : Wire n)
    (hd : CompactGidneyDisjoint rCat rASh rC w_p) {S_ctrl : Finset (Wire n)}
    (bs : CompactPhaseKickBitSteps hdB rCat rASh rC w_p S_ctrl) : Circuit n :=
  let a0 := rASh ⟨0, by omega⟩
  let kickTop := bs.stepTop.wrapCircuit
    (Circuit.S a0 ;;ᶜ UnsignedGivens.czCircuit w_p a0 (hd.ne_A_wp ⟨0, by omega⟩).symm)
  let kickMid := bs.stepMid.wrapCircuit (UnsignedGivens.parityTCircuit a0 w_p (hd.ne_A_wp ⟨0, by
    omega⟩)) ;;ᶜ
    UnsignedGivens.sdagCircuit w_p
  let fan := UnsignedGivens.cnotFanoutReg B w_p rCat (fun j => (hd.ne_cat_wp j).symm)
  let kickLo := fan ;;ᶜ streamedPrefixRef hdB rCat rASh rC w_p hd bs d le_rfl ;;ᶜ fan
  kickTop ;;ᶜ (kickMid ;;ᶜ kickLo)

theorem count_gidneyResidSuffixDyn (v : Var) (hdB : d < B) (rCat : QRegister B n)
    (rASh : QRegister (B - d) n) (rC : QRegister B n) (w_p : Wire n)
    (hd : CompactGidneyDisjoint rCat rASh rC w_p) (rem : ℕ) (hrem : rem ≤ B - d) :
    (gidneyResidSuffixDyn v hdB rCat rASh rC w_p hd rem hrem).count .TOFF = 0 ∧
    (gidneyResidSuffixDyn v hdB rCat rASh rC w_p hd rem hrem).count .T = 4 * rem + 1 := by
  induction rem with
  | zero => simp [gidneyResidSuffixDyn]
  | succ rem ih =>
      obtain ⟨h0, h1⟩ := ih (by omega)
      refine ⟨?_, ?_⟩
      · rw [gidneyResidSuffixDyn, UnsignedGivens.PhasedStep.count_wrapDynamic_toff _ _ _
          (isCliffordWrapper_gidneyResidBitStep _ _ _ _ _ _ _ _), h0]
      · rw [gidneyResidSuffixDyn, UnsignedGivens.PhasedStep.count_wrapDynamic_t _ _ _
          (isCliffordWrapper_gidneyResidBitStep _ _ _ _ _ _ _ _), h1]; omega

theorem count_loadResidSuffixDyn (v : Var) (hdB : d < B) (rCat : QRegister B n)
    (rASh : QRegister (B - d) n) (rC : QRegister B n) (w_p : Wire n)
    (hd : CompactGidneyDisjoint rCat rASh rC w_p) {S_ctrl : Finset (Wire n)}
    (bs : CompactPhaseKickBitSteps hdB rCat rASh rC w_p S_ctrl) (rem : ℕ) (hrem : rem ≤ B - d) :
    (loadResidSuffixDyn v hdB rCat rASh rC w_p hd bs rem hrem).count .TOFF = 0 ∧
    (loadResidSuffixDyn v hdB rCat rASh rC w_p hd bs rem hrem).count .T =
      4 * rem + 4 * (B - d) + 1 := by
  induction rem with
  | zero =>
      obtain ⟨h0, h1⟩ := count_gidneyResidSuffixDyn v hdB rCat rASh rC w_p hd (B - d) le_rfl
      exact ⟨h0, by dsimp only [loadResidSuffixDyn]; rw [h1]; omega⟩
  | succ rem ih =>
      obtain ⟨h0, h1⟩ := ih (by omega)
      refine ⟨?_, ?_⟩
      · rw [loadResidSuffixDyn,
          UnsignedGivens.PhasedStep.count_wrapDynamic_toff _ _ _ (bs.cleanLo _).clifford, h0]
      · rw [loadResidSuffixDyn,
          UnsignedGivens.PhasedStep.count_wrapDynamic_t _ _ _ (bs.cleanLo _).clifford, h1]; omega

theorem count_gidneyFwdBwdDyn (v : Var) (hdB : d < B) (rCat : QRegister B n)
    (rASh : QRegister (B - d) n) (rC : QRegister B n) (w_p : Wire n)
    (hd : CompactGidneyDisjoint rCat rASh rC w_p) (j : ℕ) (hjd : j < d) :
    (gidneyFwdDyn (Var := Var) hdB rCat rASh rC w_p hd j hjd).count .TOFF = 0 ∧
    (gidneyFwdDyn (Var := Var) hdB rCat rASh rC w_p hd j hjd).count .T = 4 ∧
    (gidneyBwdDyn v hdB rCat rASh rC w_p hd j hjd).count .TOFF = 0 ∧
    (gidneyBwdDyn v hdB rCat rASh rC w_p hd j hjd).count .T = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · by_cases h0 : 0 < j <;> simp [gidneyFwdDyn, h0, DynamicCircuit.count_andCompute_toff]
  · by_cases h0 : 0 < j <;> simp [gidneyFwdDyn, h0, DynamicCircuit.count_andCompute_t]
  · by_cases h0 : 0 < j <;> simp [gidneyBwdDyn, h0, DynamicCircuit.count_andUncompute_toff]
  · by_cases h0 : 0 < j <;> simp [gidneyBwdDyn, h0, DynamicCircuit.count_andUncompute_t]

theorem count_streamedPrefixDyn (v : Var) (hdB : d < B) (rCat : QRegister B n)
    (rASh : QRegister (B - d) n) (rC : QRegister B n) (w_p : Wire n)
    (hd : CompactGidneyDisjoint rCat rASh rC w_p) {S_ctrl : Finset (Wire n)}
    (bs : CompactPhaseKickBitSteps hdB rCat rASh rC w_p S_ctrl) (k : ℕ) (hk : k ≤ d) :
    (streamedPrefixDyn v hdB rCat rASh rC w_p hd bs k hk).count .TOFF = 0 ∧
    (streamedPrefixDyn v hdB rCat rASh rC w_p hd bs k hk).count .T =
      12 * k + 8 * (B - d) + 1 := by
  induction k with
  | zero =>
      obtain ⟨h0, h1⟩ := count_loadResidSuffixDyn v hdB rCat rASh rC w_p hd bs (B - d) le_rfl
      exact ⟨h0, by dsimp only [streamedPrefixDyn]; rw [h1]; omega⟩
  | succ k ih =>
      obtain ⟨h0, h1⟩ := ih (by omega)
      obtain ⟨hf0, hf1, hb0, hb1⟩ :=
        count_gidneyFwdBwdDyn v hdB rCat rASh rC w_p hd (d - (k + 1)) (by omega)
      refine ⟨?_, ?_⟩
      · dsimp only [streamedPrefixDyn, DynamicCircuit.count]
        rw [UnsignedGivens.PhasedStep.count_wrapDynamic_toff _ _ _ (bs.cleanLo _).clifford,
          UnsignedGivens.PhasedStep.count_wrapDynamic_toff _ _ _ (bs.cleanLo _).clifford,
          hf0, hb0, h0]
      · dsimp only [streamedPrefixDyn, DynamicCircuit.count]
        rw [UnsignedGivens.PhasedStep.count_wrapDynamic_t _ _ _ (bs.cleanLo _).clifford,
          UnsignedGivens.PhasedStep.count_wrapDynamic_t _ _ _ (bs.cleanLo _).clifford,
          hf1, hb1, h1]; omega

@[simp] theorem count_compactRawUnsignedPhaseKickDyn_toff (v : Var) (hdB : d < B)
    (rCat : QRegister B n) (rASh : QRegister (B - d) n) (rC : QRegister B n) (w_p : Wire n)
    (hd : CompactGidneyDisjoint rCat rASh rC w_p) {S_ctrl : Finset (Wire n)}
    (bs : CompactPhaseKickBitSteps hdB rCat rASh rC w_p S_ctrl) :
    (compactRawUnsignedPhaseKickDyn v hdB rCat rASh rC w_p hd bs).count .TOFF = 0 := by
  dsimp only [compactRawUnsignedPhaseKickDyn, DynamicCircuit.count]
  rw [UnsignedGivens.PhasedStep.count_wrapDynamic_toff _ _ _ bs.cleanTop.clifford,
    UnsignedGivens.PhasedStep.count_wrapDynamic_toff _ _ _ bs.cleanMid.clifford,
    (count_streamedPrefixDyn v hdB rCat rASh rC w_p hd bs d le_rfl).1]
  simp [DynamicCircuit.count]

@[simp] theorem count_compactRawUnsignedPhaseKickDyn_t (v : Var) (hdB : d < B)
    (rCat : QRegister B n) (rASh : QRegister (B - d) n) (rC : QRegister B n) (w_p : Wire n)
    (hd : CompactGidneyDisjoint rCat rASh rC w_p) {S_ctrl : Finset (Wire n)}
    (bs : CompactPhaseKickBitSteps hdB rCat rASh rC w_p S_ctrl) :
    (compactRawUnsignedPhaseKickDyn v hdB rCat rASh rC w_p hd bs).count .T =
      8 * B + 10 + 4 * d := by
  dsimp only [compactRawUnsignedPhaseKickDyn, DynamicCircuit.count]
  rw [UnsignedGivens.PhasedStep.count_wrapDynamic_t _ _ _ bs.cleanTop.clifford,
    UnsignedGivens.PhasedStep.count_wrapDynamic_t _ _ _ bs.cleanMid.clifford,
    (count_streamedPrefixDyn v hdB rCat rASh rC w_p hd bs d le_rfl).2]
  have htop : (Circuit.S (rASh ⟨0, by omega⟩) ;;ᶜ
      UnsignedGivens.czCircuit w_p (rASh ⟨0, by omega⟩) (hd.ne_A_wp ⟨0, by
          omega⟩).symm).count .T = 0 := by
    simp
  have hmid : (UnsignedGivens.parityTCircuit (rASh ⟨0, by omega⟩) w_p (hd.ne_A_wp ⟨0, by
    omega⟩)).count .T =
      1 := UnsignedGivens.count_parityTCircuit_t _ _ _
  have hsd : (UnsignedGivens.sdagCircuit w_p).count .T = 0 := UnsignedGivens.count_sdagCircuit_t _
  have hfan : (UnsignedGivens.cnotFanoutReg B w_p rCat (fun j =>
    (hd.ne_cat_wp j).symm)).count .T = 0 :=
    UnsignedGivens.count_cnotFanoutReg_t _ _ _ _
  dsimp only [DynamicCircuit.count]
  rw [htop, hmid, hsd, hfan]; omega

end CompactKickDefs

/-! ## Section 1C: Soundness of `compactRawUnsignedPhaseKickDyn` (`RealizesCleanRef` & `ket`) -/

section CompactKickSoundness

variable {Var : Type} {n B d : ℕ}

@[simp] theorem update_update_self_eq {α : Type*} {γ : α → Type*} [DecidableEq α]
    (f : (a : α) → γ a) (a : α) (x : γ a) :
    Function.update (Function.update f a x) a (f a) = f := by
  funext b; by_cases h : b = a <;> simp [h]

@[simp] theorem gMidAssign_zero (wy wa wc : Wire n) (β : BitAssignment n) :
    gMidAssign wy wa wc 0 β = Function.update β wc (β wc + β wy * β wa) := by
  dsimp only [gMidAssign]; funext w
  by_cases hwc : w = wc <;> by_cases hwa : w = wa <;> by_cases hwy : w = wy <;> simp [*]

theorem gidneyResidBitStep_pre_mid_ket (rCat : QRegister B n) (rASh : QRegister (B - d) n)
    (rC : QRegister B n) (w_p : Wire n) (hd : CompactGidneyDisjoint rCat rASh rC w_p)
    (j : ℕ) (hdj : d ≤ j) (hj : j < B) (β : BitAssignment n) :
    let s := gidneyResidBitStep rCat rASh rC w_p hd j hdj hj
    let cp : ZMod 2 := if h0 : 0 < j then β (rC ⟨j - 1, by omega⟩) else 0
    (s.pre ;;ᶜ Circuit.TOFF s.c₁ s.c₂ s.anc s.h₁₂ s.h₁a s.h₂a ;;ᶜ s.midPre).eval.1.mulVec
        (UnsignedGivens.ket β) =
      UnsignedGivens.ket (gMidAssign (rCat ⟨j, hj⟩) (rASh ⟨j - d, by
          omega⟩) (rC ⟨j, hj⟩) cp β) := by
  intro s cp; dsimp only [s, gidneyResidBitStep, cp]
  by_cases h0 : 0 < j
  · simp only [h0, ↓reduceDIte]
    simpa only [gFwd4, UnsignedGivens.eval_seq_mulVec] using
      evolve_gFwd4_ket (rCat ⟨j, hj⟩) (rASh ⟨j - d, by omega⟩) (rC ⟨j, hj⟩)
        (rC ⟨j - 1, by omega⟩) (hd.ne_cat_A _ _) (hd.ne_cat_C _ _) (hd.ne_A_C _ _)
        (hd.ne_cat_C _ _) (hd.ne_A_C _ _)
        (UnsignedGivens.GidneyKickDisjoint.ne_C_C rC
          (by intro h; have := congrArg Fin.val h; dsimp at this; omega)).symm β
  · simp only [h0, ↓reduceDIte, UnsignedGivens.eval_seq_mulVec, UnsignedGivens.eval_identity_mulVec,
      UnsignedGivens.evolve_TOFF_ket, gMidAssign_zero]

theorem gidneyResidBitStep_mid_post_ket (rCat : QRegister B n) (rASh : QRegister (B - d) n)
    (rC : QRegister B n) (w_p : Wire n) (hd : CompactGidneyDisjoint rCat rASh rC w_p)
    (j : ℕ) (hdj : d ≤ j) (hj : j < B) (γ : BitAssignment n) (y0 a0 c0 : ZMod 2)
    (hy : γ (rCat ⟨j, hj⟩) = y0 + if h0 : 0 < j then γ (rC ⟨j - 1, by omega⟩) else 0)
    (ha : γ (rASh ⟨j - d, by omega⟩) = a0 + if h0 : 0 < j then γ (rC ⟨j - 1, by omega⟩) else 0)
    (hc : γ (rC ⟨j, hj⟩) = c0 +
      ((y0 + if h0 : 0 < j then γ (rC ⟨j - 1, by omega⟩) else 0) *
        (a0 + if h0 : 0 < j then γ (rC ⟨j - 1, by omega⟩) else 0) +
        if h0 : 0 < j then γ (rC ⟨j - 1, by omega⟩) else 0)) :
    let s := gidneyResidBitStep rCat rASh rC w_p hd j hdj hj
    let cp : ZMod 2 := if h0 : 0 < j then γ (rC ⟨j - 1, by omega⟩) else 0
    (s.midPost ;;ᶜ Circuit.TOFF s.c₁ s.c₂ s.anc s.h₁₂ s.h₁a s.h₂a ;;ᶜ s.post).eval.1.mulVec
        (UnsignedGivens.ket γ) =
      UnsignedGivens.ket (Function.update
        (Function.update (Function.update γ (rC ⟨j, hj⟩) c0) (rASh ⟨j - d, by omega⟩) a0)
        (rCat ⟨j, hj⟩) (y0 + cp + a0)) := by
  intro s cp; dsimp only [s, gidneyResidBitStep, cp] at hy ha hc ⊢
  by_cases h0 : 0 < j
  · simp only [h0, ↓reduceDIte] at hy ha hc ⊢
    simpa only [gBwd4, UnsignedGivens.eval_seq_mulVec] using
      evolve_gBwd4_ket (rCat ⟨j, hj⟩) (rASh ⟨j - d, by omega⟩) (rC ⟨j, hj⟩)
        (rC ⟨j - 1, by omega⟩) (hd.ne_cat_A _ _) (hd.ne_cat_C _ _) (hd.ne_A_C _ _)
        (hd.ne_A_C _ _)
        (UnsignedGivens.GidneyKickDisjoint.ne_C_C rC
          (by intro h; have := congrArg Fin.val h; dsimp at this; omega)).symm
        γ y0 a0 c0 _ hy ha hc rfl
  · simp only [h0, ↓reduceDIte, add_zero] at hy ha hc ⊢
    simpa only [gBwd3, UnsignedGivens.eval_seq_mulVec, UnsignedGivens.eval_identity_mulVec,
      add_zero] using
      evolve_gBwd3_ket (rCat ⟨j, hj⟩) (rASh ⟨j - d, by omega⟩) (rC ⟨j, hj⟩)
        (hd.ne_cat_A _ _) (hd.ne_cat_C _ _) (hd.ne_A_C _ _) γ y0 a0 c0 hy ha hc

theorem gidneyResidSuffixRef_spec (hdB : d < B) (rCat : QRegister B n)
    (rASh : QRegister (B - d) n) (rC : QRegister B n) (w_p : Wire n)
    (hd : CompactGidneyDisjoint rCat rASh rC w_p) (rem : ℕ) (hrem : rem ≤ B - d) :
    ∃ (φ : BitAssignment n → ℂ) (f : BitAssignment n → BitAssignment n),
      UnsignedGivens.PhasedPerm (gidneyResidSuffixRef hdB rCat rASh rC w_p hd rem hrem) φ f ∧
      (∀ β (w : Wire n), (∀ k : Fin B, B - rem ≤ k.val → w ≠ rCat k) → f β w = β w) ∧
      (∀ β (yc a : ℕ), yc < 2 ^ B → a < 2 ^ B →
        (∀ k : Fin B, B - rem ≤ k.val →
          β (rCat k) = ((yc / 2 ^ k.val % 2 : ℕ) : ZMod 2) ∧
          β (rASh ⟨k.val - d, by omega⟩) = ((a / 2 ^ k.val % 2 : ℕ) : ZMod 2) ∧
          β (rC k) = 0) →
        (∀ _h0 : 0 < B - rem,
          β (rC ⟨B - rem - 1, by omega⟩) = ((UnsignedGivens.carryAt yc a (B - rem) : ℕ) : ZMod 2)) →
        φ β = UnsignedGivens.omega8 ^ ((((yc + a) / 2 ^ B : ℕ) : ZMod 2) + β w_p).val ∧
        ∀ k : Fin B, B - rem ≤ k.val →
          f β (rCat k) = (((yc + a) / 2 ^ k.val % 2 : ℕ) : ZMod 2)) := by
  induction rem with
  | zero =>
      refine ⟨fun β ↦ UnsignedGivens.omega8 ^ (β (rC ⟨B - 1, by omega⟩) + β w_p).val, id, ?_, ?_,
        ?_⟩
      · intro β; dsimp only [gidneyResidSuffixRef];
          exact UnsignedGivens.evolve_parityTCircuit_ket _ _ _ β
      · intro _ _ _; rfl
      · intro β yc a hyc ha _ hprev
        have hcB := hprev (by omega : 0 < B - 0)
        simp only [Nat.sub_zero, UnsignedGivens.carryAt_of_lt hyc ha] at hcB
        exact ⟨by dsimp only; rw [hcB], fun k hk ↦ absurd k.isLt (by omega)⟩
  | succ rem ih =>
      obtain ⟨φ_in, f_in, hperm_in, hfix_in, hval_in⟩ := ih (by omega)
      let j := B - (rem + 1)
      have hdj : d ≤ j := by omega
      have hj : j < B := by omega
      let jf : Fin B := ⟨j, hj⟩
      let ja : Fin (B - d) := ⟨j - d, by omega⟩
      let cp (β : BitAssignment n) : ZMod 2 := if h0 : 0 < j then β (rC ⟨j - 1, by omega⟩) else 0
      let β_mid (β : BitAssignment n) := gMidAssign (rCat jf) (rASh ja) (rC jf) (cp β) β
      let f_out (β : BitAssignment n) :=
        Function.update
          (Function.update (Function.update (f_in (β_mid β)) (rC jf) (β (rC jf)))
            (rASh ja) (β (rASh ja)))
          (rCat jf) (β (rCat jf) + cp β + β (rASh ja))
      have hfix_jf (γ : BitAssignment n) : f_in γ (rCat jf) = γ (rCat jf) :=
        hfix_in γ _ fun k hk h ↦
          by have := congrArg Fin.val (rCat.wires.injective h); dsimp [jf] at this; omega
      have hfix_A (γ : BitAssignment n) : f_in γ (rASh ja) = γ (rASh ja) :=
        hfix_in γ _ fun k _ ↦ (hd.ne_cat_A k ja).symm
      have hfix_C (γ : BitAssignment n) (m : Fin B) : f_in γ (rC m) = γ (rC m) :=
        hfix_in γ _ fun k _ ↦ (hd.ne_cat_C k m).symm
      refine ⟨fun β ↦ φ_in (β_mid β), f_out, ?_, ?_, ?_⟩
      · intro β
        dsimp only [gidneyResidSuffixRef, UnsignedGivens.PhasedStep.wrapCircuit]
        have h1 := gidneyResidBitStep_pre_mid_ket rCat rASh rC w_p hd j hdj hj β
        have hm_prev : ∀ h0 : 0 < j, β_mid β (rC ⟨j - 1, by omega⟩) = β (rC ⟨j - 1, by omega⟩) := by
          intro h0; dsimp only [β_mid, gMidAssign]
          have hcne : rC ⟨j - 1, by omega⟩ ≠ rC jf :=
            UnsignedGivens.GidneyKickDisjoint.ne_C_C rC
              (by intro h; have := congrArg Fin.val h; dsimp [jf] at this; omega)
          rw [Function.update_of_ne hcne, Function.update_of_ne (hd.ne_A_C ja _).symm,
            Function.update_of_ne (hd.ne_cat_C jf _).symm]
        have hcp_eq : (if h0 : 0 < j then f_in (β_mid β) (rC ⟨j - 1, by omega⟩) else 0) = cp β := by
          by_cases h0 : 0 < j <;> simp [cp, h0, hfix_C, hm_prev]
        have h3 := gidneyResidBitStep_mid_post_ket rCat rASh rC w_p hd j hdj hj (f_in (β_mid β))
          (β (rCat jf)) (β (rASh ja)) (β (rC jf))
          (by rw [hfix_jf, hcp_eq]; dsimp only [β_mid, gMidAssign]
              rw [Function.update_of_ne (hd.ne_cat_C jf jf),
                Function.update_of_ne (hd.ne_cat_A jf ja), Function.update_self])
          (by rw [hfix_A, hcp_eq]; dsimp only [β_mid, gMidAssign]
              rw [Function.update_of_ne (hd.ne_A_C ja jf), Function.update_self])
          (by rw [hfix_C, hcp_eq]; dsimp only [β_mid, gMidAssign]; rw [Function.update_self])
        simp only [UnsignedGivens.eval_seq_mulVec] at h1 h3 ⊢
        rw [h1, hperm_in (β_mid β)]
        simp only [Matrix.mulVec_smul]
        rw [h3]
        dsimp only [f_out, jf, ja]; rw [hcp_eq]
      · intro β w hw; dsimp only [f_out]
        have hne_cat : w ≠ rCat jf := hw jf (by dsimp [jf]; omega)
        rw [Function.update_of_ne hne_cat]
        by_cases hwA : w = rASh ja
        · subst hwA; simp
        · rw [Function.update_of_ne hwA]
          by_cases hwC : w = rC jf
          · subst hwC; simp
          · rw [Function.update_of_ne hwC, hfix_in _ w fun k hk ↦ hw k (by omega)]
            simp [β_mid, gMidAssign, hne_cat, hwA, hwC]
      · intro β yc a hyc ha hhigh hprev
        have hj_hi := hhigh jf (by dsimp [jf]; omega)
        have hcp_val : cp β = ((UnsignedGivens.carryAt yc a j : ℕ) : ZMod 2) := by
          by_cases h0 : 0 < j
          · simpa only [cp, h0, ↓reduceDIte] using hprev h0
          · have hj0 : j = 0 := by omega
            simp [cp, hj0]
        have hmid_hi : ∀ k : Fin B, B - rem ≤ k.val →
            β_mid β (rCat k) = ((yc / 2 ^ k.val % 2 : ℕ) : ZMod 2) ∧
            β_mid β (rASh ⟨k.val - d, by omega⟩) = ((a / 2 ^ k.val % 2 : ℕ) : ZMod 2) ∧
            β_mid β (rC k) = 0 := by
          intro k hk
          have hcat_ne : rCat k ≠ rCat jf := fun h ↦ by
            have := congrArg Fin.val (rCat.wires.injective h); dsimp [jf] at this; omega
          have hA_ne : rASh ⟨k.val - d, by omega⟩ ≠ rASh ja := fun h ↦ by
            have := congrArg Fin.val (rASh.wires.injective h); dsimp [ja] at this; omega
          have hC_ne : rC k ≠ rC jf := fun h ↦ by
            have := congrArg Fin.val (rC.wires.injective h); dsimp [jf] at this; omega
          have hk_hi := hhigh k (by omega)
          dsimp only [β_mid, gMidAssign]
          simp only [Function.update_of_ne hC_ne, Function.update_of_ne hA_ne,
            Function.update_of_ne hcat_ne, Function.update_of_ne (hd.ne_cat_C k jf),
            Function.update_of_ne (hd.ne_cat_A k ja), Function.update_of_ne (hd.ne_A_C _ jf),
            Function.update_of_ne (hd.ne_A_C ja k).symm,
            Function.update_of_ne (hd.ne_cat_C jf k).symm,
            Function.update_of_ne (hd.ne_cat_A jf _).symm]
          exact hk_hi
        have hmid_prev : ∀ _h0 : 0 < B - rem,
            β_mid β (rC ⟨B - rem - 1, by omega⟩) =
              ((UnsignedGivens.carryAt yc a (B - rem) : ℕ) : ZMod 2) := by
          intro _
          have hidx : (⟨B - rem - 1, by omega⟩ : Fin B) = jf := by ext; dsimp [jf]; omega
          have hb_eq : B - rem = j + 1 := by omega
          rw [hidx, hb_eq]; dsimp only [β_mid, gMidAssign]
          rw [Function.update_self, hj_hi.2.2, zero_add, hj_hi.1, hj_hi.2.1, hcp_val,
            add_comm _ ((UnsignedGivens.carryAt yc a j : ℕ) : ZMod 2), UnsignedGivens.carryAt_succ]
          exact UnsignedGivens.gidney_maj_zmod2 (UnsignedGivens.carryAt_lt_two yc a j)
            (Nat.mod_lt _ (by omega)) (Nat.mod_lt _ (by omega))
        have hin := hval_in (β_mid β) yc a hyc ha hmid_hi hmid_prev
        have hwp_mid : β_mid β w_p = β w_p := by
          dsimp only [β_mid, gMidAssign]
          rw [Function.update_of_ne (hd.ne_C_wp jf).symm,
            Function.update_of_ne (hd.ne_A_wp ja).symm,
            Function.update_of_ne (hd.ne_cat_wp jf).symm]
        refine ⟨by dsimp only; rw [hin.1, hwp_mid], fun k hk ↦ ?_⟩
        by_cases hkj : k.val = j
        · have hk_eq : k = jf := Fin.ext hkj
          rw [hk_eq]; dsimp only [f_out]
          rw [Function.update_self, hcp_val, hj_hi.1, hj_hi.2.1]
          simpa only [jf, UnsignedGivens.add_div_pow_mod_two] using
            UnsignedGivens.gidney_sum_zmod2 (UnsignedGivens.carryAt yc a j) (yc / 2 ^ j % 2) (a /
              2 ^ j % 2)
        · have hcat_ne : rCat k ≠ rCat jf := fun h ↦
            hkj (congrArg Fin.val (rCat.wires.injective h))
          dsimp only [f_out]
          rw [Function.update_of_ne hcat_ne, Function.update_of_ne (hd.ne_cat_A k ja),
            Function.update_of_ne (hd.ne_cat_C k jf)]
          exact hin.2 k (by omega)

theorem cleanWrap_perm_of_eq
    {s : UnsignedGivens.PhasedStep n} {bitVal : BitAssignment n → ZMod 2} {S_ctrl : Finset (Wire n)}
    (hs : UnsignedGivens.IsCleanBitStep s bitVal S_ctrl)
    {c_in : Circuit n} {φ_in : BitAssignment n → ℂ} {f_in f_tgt : BitAssignment n → BitAssignment n}
    (hperm_in : UnsignedGivens.PhasedPerm c_in φ_in f_in)
    (hfix_anc : ∀ β, f_in β s.anc = β s.anc)
    (hfix_ctrl : ∀ β w, w ∈ S_ctrl → f_in β w = β w)
    (heq : ∀ β, Function.update (f_in (Function.update β s.anc (β s.anc + bitVal β)))
      s.anc (β s.anc) = f_tgt β) :
    UnsignedGivens.PhasedPerm (s.wrapCircuit c_in)
      (fun β ↦ φ_in (Function.update β s.anc (β s.anc + bitVal β))) f_tgt := by
  have hw := (UnsignedGivens.cleanBitStep_wrap_spec hs hperm_in hfix_anc hfix_ctrl).1
  intro β; simpa only [heq β] using hw β

theorem loadResidSuffixRef_spec (hdB : d < B) (rCat : QRegister B n)
    (rASh : QRegister (B - d) n) (rC : QRegister B n) (w_p : Wire n)
    (hd : CompactGidneyDisjoint rCat rASh rC w_p) {S_ctrl : Finset (Wire n)}
    (bs : CompactPhaseKickBitSteps hdB rCat rASh rC w_p S_ctrl) (rem : ℕ) (hrem : rem ≤ B - d) :
    ∃ (φ : BitAssignment n → ℂ) (f : BitAssignment n → BitAssignment n),
      UnsignedGivens.PhasedPerm (loadResidSuffixRef hdB rCat rASh rC w_p hd bs rem hrem) φ f ∧
      (∀ β (w : Wire n), (∀ k : Fin B, d ≤ k.val → w ≠ rCat k) → f β w = β w) ∧
      (∀ β (yc a : ℕ), yc < 2 ^ B → a < 2 ^ B →
        (∀ k : Fin B, d ≤ k.val → β (rCat k) = ((yc / 2 ^ k.val % 2 : ℕ) : ZMod 2)) →
        (∀ k : Fin B, d ≤ k.val → k.val < B - rem →
          β (rASh ⟨k.val - d, by omega⟩) = ((a / 2 ^ k.val % 2 : ℕ) : ZMod 2)) →
        (∀ k : Fin B, B - rem ≤ k.val →
          β (rASh ⟨k.val - d, by omega⟩) = 0 ∧
          bs.bitLo β k = ((a / 2 ^ k.val % 2 : ℕ) : ZMod 2)) →
        (∀ k : Fin B, d ≤ k.val → β (rC k) = 0) →
        (∀ _hd0 : 0 < d, β (rC ⟨d - 1, by
          omega⟩) = ((UnsignedGivens.carryAt yc a d : ℕ) : ZMod 2)) →
        φ β = UnsignedGivens.omega8 ^ ((((yc + a) / 2 ^ B : ℕ) : ZMod 2) + β w_p).val ∧
        ∀ k : Fin B, d ≤ k.val →
          f β (rCat k) = (((yc + a) / 2 ^ k.val % 2 : ℕ) : ZMod 2)) := by
  induction rem with
  | zero =>
      obtain ⟨φ, f, hperm, hfix, hval⟩ :=
        gidneyResidSuffixRef_spec hdB rCat rASh rC w_p hd (B - d) le_rfl
      refine ⟨φ, f, hperm, fun β w hw ↦ hfix β w fun k hk ↦ hw k (by omega), ?_⟩
      intro β yc a hyc ha hcat hA_lt _ hC hprev
      have hhigh : ∀ k : Fin B, B - (B - d) ≤ k.val →
          β (rCat k) = ((yc / 2 ^ k.val % 2 : ℕ) : ZMod 2) ∧
          β (rASh ⟨k.val - d, by omega⟩) = ((a / 2 ^ k.val % 2 : ℕ) : ZMod 2) ∧
          β (rC k) = 0 := fun k hk ↦
        ⟨hcat k (by omega), hA_lt k (by omega) (by omega), hC k (by omega)⟩
      have hp : ∀ h0 : 0 < B - (B - d),
          β (rC ⟨B - (B - d) - 1, by omega⟩) =
            ((UnsignedGivens.carryAt yc a (B - (B - d)) : ℕ) : ZMod 2) := by
        intro h0; have hbd : B - (B - d) = d := by omega
        simpa only [hbd] using hprev (by omega)
      have hv := hval β yc a hyc ha hhigh hp
      exact ⟨hv.1, fun k hk ↦ hv.2 k (by omega)⟩
  | succ rem ih =>
      let j := B - (rem + 1)
      let jf : Fin B := ⟨j, by omega⟩
      let ja : Fin (B - d) := ⟨j - d, by omega⟩
      let s := bs.stepLo jf
      have hs_anc : s.anc = rASh ja := by
        rw [bs.ancLo jf]; simp only [ancSh, jf, ja, show ¬ j < d by omega, ↓reduceIte]
      obtain ⟨φ_in, f_in, hperm_in, hfix_in, hval_in⟩ := ih (by omega)
      let φ_out (β : BitAssignment n) := φ_in (Function.update β s.anc (β s.anc + bs.bitLo β jf))
      let f_out (β : BitAssignment n) :=
        Function.update (f_in (Function.update β s.anc (β s.anc + bs.bitLo β jf))) s.anc (β s.anc)
      have hperm_out : UnsignedGivens.PhasedPerm (s.wrapCircuit _) φ_out f_out :=
        cleanWrap_perm_of_eq (bs.cleanLo jf) hperm_in
          (fun β ↦ hfix_in β s.anc fun k _ ↦ by rw [hs_anc]; exact (hd.ne_cat_A k ja).symm)
          (fun β w hw ↦ hfix_in β w fun k _ hk ↦
            Finset.disjoint_left.mp bs.disj_ctrl_cat hw
              (QRegister.mem_image rCat _ |>.mpr ⟨k, hk.symm⟩))
          (fun _ ↦ rfl)
      refine ⟨φ_out, f_out, hperm_out, ?_, ?_⟩
      · intro β w hw; dsimp only [f_out]
        by_cases hws : w = s.anc
        · subst hws; exact Function.update_self _ _ _
        · rw [Function.update_of_ne hws, hfix_in _ w hw, Function.update_of_ne hws]
      · intro β yc a hyc ha hcat hA_lt hA_ge hC hprev
        have hj_ge := hA_ge jf (by dsimp [jf]; omega)
        let β₁ := Function.update β s.anc (β s.anc + bs.bitLo β jf)
        have hβ₁ : β₁ = Function.update β (rASh ja) (((a / 2 ^ j % 2 : ℕ) : ZMod 2)) := by
          dsimp only [β₁]; rw [hs_anc, hj_ge.1, zero_add, hj_ge.2]
        have hwp₁ : β₁ w_p = β w_p := by
          rw [hβ₁, Function.update_of_ne (hd.ne_A_wp ja).symm]
        have hv := hval_in β₁ yc a hyc ha
          (fun k hk ↦ by rw [hβ₁, Function.update_of_ne (hd.ne_cat_A k ja), hcat k hk])
          (fun k hkd hkl ↦ by
            rw [hβ₁]
            by_cases hkj : k.val = j
            · have hja : (⟨k.val - d, by omega⟩ : Fin (B - d)) = ja := by ext; dsimp [ja]; omega
              rw [hja, Function.update_self, hkj]
            · have hne : rASh ⟨k.val - d, by omega⟩ ≠ rASh ja := fun h ↦ by
                have := congrArg Fin.val (rASh.wires.injective h); dsimp [ja] at this; omega
              rw [Function.update_of_ne hne]; exact hA_lt k hkd (by omega))
          (fun k hk ↦ by
            have hne : rASh ⟨k.val - d, by omega⟩ ≠ rASh ja := fun h ↦ by
              have := congrArg Fin.val (rASh.wires.injective h); dsimp [ja] at this; omega
            refine ⟨by rw [hβ₁, Function.update_of_ne hne, (hA_ge k (by omega)).1], ?_⟩
            rw [(bs.cleanLo k).bitVal_congr β₁ β fun w hw ↦ by
              dsimp only [β₁]; apply Function.update_of_ne
              rintro rfl; exact (bs.cleanLo jf).anc_not_mem_ctrl hw]
            exact (hA_ge k (by omega)).2)
          (fun k hk ↦ by rw [hβ₁, Function.update_of_ne (hd.ne_A_C ja k).symm, hC k hk])
          (fun hd0 ↦ by rw [hβ₁, Function.update_of_ne (hd.ne_A_C ja _).symm, hprev hd0])
        refine ⟨by dsimp only [φ_out]; rw [hv.1, hwp₁], fun k hk ↦ ?_⟩
        dsimp only [f_out]
        have hne_anc : rCat k ≠ s.anc := by rw [hs_anc]; exact hd.ne_cat_A k ja
        rw [Function.update_of_ne hne_anc]; exact hv.2 k hk

theorem proj_zero_of_post_eq (q : Wire n) (c_post : Circuit n) (hq : q ∉ c_post.support)
    {X : Operator (2 ^ n)}
    (h : (QRegister.singleton q).basisOutcomeProjector 0 * (c_post.eval.1 * X) =
      c_post.eval.1 * X) :
    (QRegister.singleton q).basisOutcomeProjector 0 * X = X := by
  let P₀ := (QRegister.singleton q).basisOutcomeProjector 0
  have hdisj : Disjoint c_post.support (QRegister.singleton q).image := by
    rw [QRegister.image_singleton, Finset.disjoint_singleton_right]; exact hq
  have hcomm := UnsignedGivens.eval_comm_basisOutcomeProjector_of_disjoint_support c_post _ hdisj 0
  have hU : c_post.eval.1ᴴ * c_post.eval.1 = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using c_post.eval.2.1
  have hUX : c_post.eval.1 * (P₀ * X) = c_post.eval.1 * X := by
    rw [← Matrix.mul_assoc, hcomm, Matrix.mul_assoc, h]
  calc P₀ * X = (c_post.eval.1ᴴ * c_post.eval.1) * (P₀ * X) := by rw [hU, Matrix.one_mul]
    _ = c_post.eval.1ᴴ * (c_post.eval.1 * X) := by rw [Matrix.mul_assoc, hUX]
    _ = X := by rw [← Matrix.mul_assoc, hU, Matrix.one_mul]

theorem gidneyFwdBwdRef_perm (hdB : d < B) (rCat : QRegister B n)
    (rASh : QRegister (B - d) n) (rC : QRegister B n) (w_p : Wire n)
    (hd : CompactGidneyDisjoint rCat rASh rC w_p) (j : ℕ) (hjd : j < d) :
    let jf : Fin B := ⟨j, by omega⟩
    let i0 : Fin (B - d) := ⟨0, by omega⟩
    let cp (β : BitAssignment n) : ZMod 2 := if h0 : 0 < j then β (rC ⟨j - 1, by omega⟩) else 0
    let δ (β : BitAssignment n) : ZMod 2 :=
      (β (rCat jf) + cp β) * (β (rASh i0) + cp β) + cp β
    UnsignedGivens.PhasedPerm (gidneyFwdRef hdB rCat rASh rC w_p hd j hjd) (fun _ ↦ 1)
      (fun β ↦ Function.update β (rC jf) (β (rC jf) + δ β)) ∧
    UnsignedGivens.PhasedPerm (gidneyBwdRef hdB rCat rASh rC w_p hd j hjd) (fun _ ↦ 1)
      (fun β ↦ Function.update
        (Function.update β (rC jf) (β (rC jf) + δ β))
        (rCat jf) (β (rCat jf) + cp β + β (rASh i0))) := by
  intro jf i0 cp δ; refine ⟨fun β ↦ ?_, fun β ↦ ?_⟩
  · rw [one_smul]; dsimp only [gidneyFwdRef, cp, δ, jf, i0]
    by_cases h0 : 0 < j
    · simp only [h0, ↓reduceDIte]
      exact evolve_gidneyFwd4_ket _ _ _ _ _ _ _ _ _ _ β
    · simp only [h0, ↓reduceDIte, add_zero, UnsignedGivens.evolve_TOFF_ket]
  · rw [one_smul]; dsimp only [gidneyBwdRef, cp, δ, jf, i0]
    by_cases h0 : 0 < j
    · simp only [h0, ↓reduceDIte]
      exact evolve_gidneyBwd4_ket _ _ _ _ _ _ _ (hd.ne_cat_C _ _) _ _ β _
        (UnsignedGivens.zmod2_add_cancel_right _ _).symm
    · simp only [h0, ↓reduceDIte, add_zero]
      rw [evolve_gBwd3_ket _ _ _ _ _ _ β _ _ _ rfl rfl
        (UnsignedGivens.zmod2_add_cancel_right _ _).symm]
      apply congrArg UnsignedGivens.ket; funext w
      rcases eq_or_ne w (rCat ⟨j, by omega⟩) with rfl | hwy
      · simp
      · rcases eq_or_ne w (rASh ⟨0, by omega⟩) with rfl | hwa <;>
          simp [*, Function.update_of_ne (hd.ne_A_C _ _)]

theorem streamedPrefixRef_spec (hdB : d < B) (rCat : QRegister B n)
    (rASh : QRegister (B - d) n) (rC : QRegister B n) (w_p : Wire n)
    (hd : CompactGidneyDisjoint rCat rASh rC w_p) {S_ctrl : Finset (Wire n)}
    (bs : CompactPhaseKickBitSteps hdB rCat rASh rC w_p S_ctrl) (k : ℕ) (hk : k ≤ d) :
    ∃ (φ : BitAssignment n → ℂ) (f : BitAssignment n → BitAssignment n),
      UnsignedGivens.PhasedPerm (streamedPrefixRef hdB rCat rASh rC w_p hd bs k hk) φ f ∧
      (∀ β (w : Wire n), (∀ m : Fin B, d - k ≤ m.val → w ≠ rCat m) → f β w = β w) ∧
      (∀ β (yc a : ℕ), yc < 2 ^ B → a < 2 ^ B →
        (∀ m : Fin B, d - k ≤ m.val → β (rCat m) = ((yc / 2 ^ m.val % 2 : ℕ) : ZMod 2)) →
        (∀ i : Fin (B - d), β (rASh i) = 0) →
        (∀ m : Fin B, d - k ≤ m.val → bs.bitLo β m = ((a / 2 ^ m.val % 2 : ℕ) : ZMod 2)) →
        (∀ m : Fin B, d - k ≤ m.val → β (rC m) = 0) →
        (∀ _h0 : 0 < d - k,
          β (rC ⟨d - k - 1, by omega⟩) = ((UnsignedGivens.carryAt yc a (d - k) : ℕ) : ZMod 2)) →
        φ β = UnsignedGivens.omega8 ^ ((((yc + a) / 2 ^ B : ℕ) : ZMod 2) + β w_p).val ∧
        ∀ m : Fin B, d - k ≤ m.val →
          f β (rCat m) = (((yc + a) / 2 ^ m.val % 2 : ℕ) : ZMod 2)) := by
  induction k with
  | zero =>
      obtain ⟨φ, f, hperm, hfix, hval⟩ :=
        loadResidSuffixRef_spec hdB rCat rASh rC w_p hd bs (B - d) le_rfl
      refine ⟨φ, f, hperm, fun β w hw ↦ hfix β w fun m hm ↦ hw m (by omega), ?_⟩
      intro β yc a hyc ha hcat hA hbit hC hprev
      have hv := hval β yc a hyc ha
        (fun m hm ↦ hcat m (by omega))
        (fun m _ hml ↦ absurd hml (by omega))
        (fun m _ ↦ ⟨hA _, hbit m (by omega)⟩)
        (fun m hm ↦ hC m (by omega))
        (fun hd0 ↦ by simpa only [Nat.sub_zero] using hprev (by omega))
      exact ⟨hv.1, fun m hm ↦ hv.2 m (by omega)⟩
  | succ k ih =>
      obtain ⟨φ_in, f_in, hperm_in, hfix_in, hval_in⟩ := ih (by omega)
      let j := d - (k + 1)
      have hjd : j < d := by omega
      let jf : Fin B := ⟨j, by omega⟩
      let i0 : Fin (B - d) := ⟨0, by omega⟩
      let s := bs.stepLo jf
      have hs_anc : s.anc = rASh i0 := by
        rw [bs.ancLo jf]; simp only [ancSh, jf, i0, hjd, ↓reduceIte]
      have hC_not_ctrl : rC jf ∉ S_ctrl := fun hm ↦
        Finset.disjoint_left.mp bs.disj_ctrl_C hm (QRegister.mem_image rC _ |>.mpr ⟨jf, rfl⟩)
      have hcat_not_ctrl : rCat jf ∉ S_ctrl := fun hm ↦
        Finset.disjoint_left.mp bs.disj_ctrl_cat hm (QRegister.mem_image rCat _ |>.mpr ⟨jf, rfl⟩)
      let cp (γ : BitAssignment n) : ZMod 2 := if h0 : 0 < j then γ (rC ⟨j - 1, by omega⟩) else 0
      let a_eff (γ : BitAssignment n) : ZMod 2 := γ (rASh i0) + bs.bitLo γ jf
      let δc (γ : BitAssignment n) : ZMod 2 :=
        (γ (rCat jf) + cp γ) * (a_eff γ + cp γ) + cp γ
      let β₁ (β : BitAssignment n) := Function.update β (rC jf) (β (rC jf) + δc β)
      let f_bwd (γ : BitAssignment n) :=
        Function.update
          (Function.update γ (rC jf)
            (γ (rC jf) + ((γ (rCat jf) + cp γ) * (γ (rASh i0) + cp γ) + cp γ)))
          (rCat jf) (γ (rCat jf) + cp γ + γ (rASh i0))
      have hpermF : UnsignedGivens.PhasedPerm (gidneyFwdRef hdB rCat rASh rC w_p hd j hjd) (fun _ ↦
        1)
          (fun β ↦ Function.update β (rC jf)
            (β (rC jf) + ((β (rCat jf) + cp β) * (β (rASh i0) + cp β) + cp β))) :=
        (gidneyFwdBwdRef_perm hdB rCat rASh rC w_p hd j hjd).1
      have hpermB : UnsignedGivens.PhasedPerm (gidneyBwdRef hdB rCat rASh rC w_p hd j hjd) (fun _ ↦
        1)
          f_bwd :=
        (gidneyFwdBwdRef_perm hdB rCat rASh rC w_p hd j hjd).2
      have hperm_wrapF : UnsignedGivens.PhasedPerm
          (s.wrapCircuit (gidneyFwdRef hdB rCat rASh rC w_p hd j hjd)) (fun _ ↦ 1) β₁ :=
        cleanWrap_perm_of_eq (bs.cleanLo jf) hpermF
          (fun β ↦ by rw [hs_anc]; exact Function.update_of_ne (hd.ne_A_C i0 jf) _ _)
          (fun β w hw ↦ Function.update_of_ne (by rintro rfl; exact hC_not_ctrl hw) _ _)
          (fun β ↦ by
            rw [hs_anc, Function.update_self,
              Function.update_of_ne (hd.ne_A_C i0 jf).symm,
              Function.update_of_ne (hd.ne_cat_A jf i0)]
            have hcp1 :
                cp (Function.update β (rASh i0) (β (rASh i0) + bs.bitLo β jf)) = cp β := by
              by_cases h0 : 0 < j <;> simp [cp, h0, Function.update_of_ne (hd.ne_A_C i0 _).symm]
            rw [hcp1]; funext w
            rcases eq_or_ne w (rC jf) with rfl | hwc
            · simp [β₁, δc, a_eff, Function.update_of_ne (hd.ne_A_C i0 jf).symm]
            · rcases eq_or_ne w (rASh i0) with rfl | hwa <;> simp [β₁, *])
      let f_wrapB (γ : BitAssignment n) :=
        Function.update (f_bwd (Function.update γ s.anc (γ s.anc + bs.bitLo γ jf))) s.anc (γ s.anc)
      have hperm_wrapB : UnsignedGivens.PhasedPerm
          (s.wrapCircuit (gidneyBwdRef hdB rCat rASh rC w_p hd j hjd)) (fun _ ↦ 1) f_wrapB :=
        cleanWrap_perm_of_eq (bs.cleanLo jf) hpermB
          (fun β ↦ by
            dsimp only [f_bwd]; rw [hs_anc, Function.update_of_ne (hd.ne_cat_A jf i0).symm,
              Function.update_of_ne (hd.ne_A_C i0 jf)])
          (fun β w hw ↦ by
            dsimp only [f_bwd]
            rw [Function.update_of_ne (by rintro rfl; exact hcat_not_ctrl hw),
              Function.update_of_ne (by rintro rfl; exact hC_not_ctrl hw)])
          (fun _ ↦ rfl)
      let f_out (β : BitAssignment n) :=
        Function.update
          (Function.update (f_in (β₁ β)) (rC jf) (β (rC jf)))
          (rCat jf) (β (rCat jf) + cp β + a_eff β)
      have hfB_eq (β : BitAssignment n) : f_wrapB (f_in (β₁ β)) = f_out β := by
        have hγ_cat : f_in (β₁ β) (rCat jf) = β (rCat jf) := by
          rw [hfix_in (β₁ β) (rCat jf) fun m hm h ↦ by
            have := congrArg Fin.val (rCat.wires.injective h); dsimp [jf] at this; omega]
          exact Function.update_of_ne (hd.ne_cat_C jf jf) _ _
        have hγ_a0 : f_in (β₁ β) (rASh i0) = β (rASh i0) := by
          rw [hfix_in (β₁ β) (rASh i0) fun m _ ↦ (hd.ne_cat_A m i0).symm]
          exact Function.update_of_ne (hd.ne_A_C i0 jf) _ _
        have hγ_C : f_in (β₁ β) (rC jf) = β (rC jf) + δc β := by
          rw [hfix_in (β₁ β) (rC jf) fun m _ ↦ (hd.ne_cat_C m jf).symm]
          exact Function.update_self _ _ _
        have hγ_bit : bs.bitLo (f_in (β₁ β)) jf = bs.bitLo β jf :=
          (bs.cleanLo jf).bitVal_congr (f_in (β₁ β)) β fun w hw ↦ by
            rw [hfix_in (β₁ β) w fun m _ hm ↦
              Finset.disjoint_left.mp bs.disj_ctrl_cat hw
                (QRegister.mem_image rCat _ |>.mpr ⟨m, hm.symm⟩)]
            exact Function.update_of_ne (by rintro rfl; exact hC_not_ctrl hw) _ _
        have hcp_γ : cp (Function.update (f_in (β₁ β)) (rASh i0)
            (f_in (β₁ β) (rASh i0) + bs.bitLo (f_in (β₁ β)) jf)) = cp β := by
          by_cases h0 : 0 < j
          · simp only [cp, h0, ↓reduceDIte, Function.update_of_ne (hd.ne_A_C i0 _).symm]
            rw [hfix_in (β₁ β) (rC ⟨j - 1, by omega⟩) fun m _ ↦ (hd.ne_cat_C m _).symm]
            exact Function.update_of_ne (UnsignedGivens.GidneyKickDisjoint.ne_C_C rC
              (by intro h; have := congrArg Fin.val h; dsimp [jf] at this; omega)) _ _
          · simp [cp, h0]
        dsimp only [f_wrapB, f_bwd]
        rw [hs_anc, Function.update_self, Function.update_of_ne (hd.ne_A_C i0 jf).symm,
          Function.update_of_ne (hd.ne_cat_A jf i0), hcp_γ, hγ_cat, hγ_a0, hγ_bit, hγ_C]
        change Function.update (Function.update
            (Function.update (Function.update (f_in (β₁ β)) (rASh i0) (a_eff β)) (rC jf)
              (β (rC jf) + δc β + δc β))
            (rCat jf) (β (rCat jf) + cp β + a_eff β)) (rASh i0) (β (rASh i0)) = f_out β
        rw [UnsignedGivens.zmod2_add_cancel_right]; funext w
        rcases eq_or_ne w (rASh i0) with rfl | hwa
        · dsimp only [f_out]
          rw [Function.update_self, Function.update_of_ne (hd.ne_cat_A jf i0).symm,
            Function.update_of_ne (hd.ne_A_C i0 jf)]
          exact hγ_a0.symm
        · rcases eq_or_ne w (rCat jf) with rfl | hwy
          · dsimp only [f_out]; simp [hwa]
          · rcases eq_or_ne w (rC jf) with rfl | hwc <;> dsimp only [f_out] <;> simp [*]
      refine ⟨fun β ↦ φ_in (β₁ β), f_out, ?_, ?_, ?_⟩
      · intro β; dsimp only [streamedPrefixRef]
        simp only [UnsignedGivens.eval_seq_mulVec]
        rw [hperm_wrapF β, one_smul, hperm_in (β₁ β), Matrix.mulVec_smul,
          hperm_wrapB (f_in (β₁ β)), one_smul, hfB_eq β]
      · intro β w hw; dsimp only [f_out]
        have hne_cat : w ≠ rCat jf := hw jf (by dsimp [jf]; omega)
        rw [Function.update_of_ne hne_cat]
        by_cases hwc : w = rC jf
        · subst hwc; simp
        · rw [Function.update_of_ne hwc, hfix_in _ w fun m hm ↦ hw m (by omega)]
          simp [β₁, hwc]
      · intro β yc a hyc ha hcat hA hbit hC hprev
        have hcp_val : cp β = ((UnsignedGivens.carryAt yc a j : ℕ) : ZMod 2) := by
          by_cases h0 : 0 < j
          · simpa only [cp, h0, ↓reduceDIte] using hprev h0
          · have hj0 : j = 0 := by omega
            simp [cp, hj0]
        have ha_eff : a_eff β = ((a / 2 ^ j % 2 : ℕ) : ZMod 2) := by
          dsimp only [a_eff]; rw [hA i0, zero_add, hbit jf (by dsimp [jf]; omega)]
        have hcat_jf : β (rCat jf) = ((yc / 2 ^ j % 2 : ℕ) : ZMod 2) :=
          hcat jf (by dsimp [jf]; omega)
        have hC_jf : β (rC jf) = 0 := hC jf (by dsimp [jf]; omega)
        have hcarry_next : β₁ β (rC jf) = ((UnsignedGivens.carryAt yc a (j + 1) : ℕ) : ZMod 2) := by
          dsimp only [β₁, δc]
          rw [Function.update_self, hC_jf, zero_add, hcat_jf, ha_eff, hcp_val,
            add_comm _ ((UnsignedGivens.carryAt yc a j : ℕ) : ZMod 2), UnsignedGivens.carryAt_succ]
          exact UnsignedGivens.gidney_maj_zmod2 (UnsignedGivens.carryAt_lt_two yc a j)
            (Nat.mod_lt _ (by omega)) (Nat.mod_lt _ (by omega))
        have hin := hval_in (β₁ β) yc a hyc ha
          (fun m hm ↦ by
            dsimp only [β₁]; rw [Function.update_of_ne (hd.ne_cat_C m jf)]; exact hcat m (by omega))
          (fun i ↦ by dsimp only [β₁]; rw [Function.update_of_ne (hd.ne_A_C i jf), hA i])
          (fun m hm ↦ by
            rw [(bs.cleanLo m).bitVal_congr (β₁ β) β fun w hw ↦
              Function.update_of_ne (by rintro rfl; exact hC_not_ctrl hw) _ _]
            exact hbit m (by omega))
          (fun m hm ↦ by
            have hne : rC m ≠ rC jf := fun h ↦ by
              have := congrArg Fin.val (rC.wires.injective h); dsimp [jf] at this; omega
            dsimp only [β₁]; rw [Function.update_of_ne hne]; exact hC m (by omega))
          (fun _ ↦ by
            have hidx : (⟨d - k - 1, by omega⟩ : Fin B) = jf := by ext; dsimp [jf]; omega
            have hdk : d - k = j + 1 := by omega
            rw [hidx, hdk]; exact hcarry_next)
        have hwp₁ : β₁ β w_p = β w_p := Function.update_of_ne (hd.ne_C_wp jf).symm _ _
        refine ⟨by dsimp only; rw [hin.1, hwp₁], fun m hm ↦ ?_⟩
        by_cases hmj : m.val = j
        · have hm_eq : m = jf := Fin.ext hmj
          rw [hm_eq]; dsimp only [f_out]
          rw [Function.update_self, hcp_val, hcat_jf, ha_eff]
          simpa only [jf, UnsignedGivens.add_div_pow_mod_two] using
            UnsignedGivens.gidney_sum_zmod2 (UnsignedGivens.carryAt yc a j) (yc / 2 ^ j % 2) (a /
              2 ^ j % 2)
        · have hcat_ne : rCat m ≠ rCat jf := fun h ↦
            hmj (congrArg Fin.val (rCat.wires.injective h))
          dsimp only [f_out]
          rw [Function.update_of_ne hcat_ne, Function.update_of_ne (hd.ne_cat_C m jf)]
          exact hin.2 m (by omega)

/-- Left-invariance of `R` under `|0⟩⟨0|` on wire `q`. -/
def ZeroOnWire (q : Wire n) (R : Operator (2 ^ n)) : Prop :=
  (QRegister.singleton q).basisOutcomeProjector 0 * R = R

theorem comm_proj_zero_of_phasedPerm_fix (q : Wire n) (c : Circuit n)
    {φ : BitAssignment n → ℂ} {f : BitAssignment n → BitAssignment n}
    (hp : UnsignedGivens.PhasedPerm c φ f) (hfix : ∀ β, f β q = β q) :
    (QRegister.singleton q).basisOutcomeProjector 0 * c.eval.1 =
      c.eval.1 * (QRegister.singleton q).basisOutcomeProjector 0 := by
  apply UnsignedGivens.matrix_ext_ket; intro β
  simp only [← Matrix.mulVec_mulVec, UnsignedGivens.basisOutcomeProjector_zero_ket]
  by_cases h0 : β q = 0
  · simp only [h0, ↓reduceIte, hp β, Matrix.mulVec_smul,
      UnsignedGivens.basisOutcomeProjector_zero_ket,
      hfix β]
  · simp only [h0, ↓reduceIte, Matrix.mulVec_zero, hp β, Matrix.mulVec_smul,
      UnsignedGivens.basisOutcomeProjector_zero_ket, hfix β, smul_zero]

theorem zeroOnWire_mul_of_phasedPerm_fix (q : Wire n) (c : Circuit n)
    {φ : BitAssignment n → ℂ} {f : BitAssignment n → BitAssignment n}
    (hp : UnsignedGivens.PhasedPerm c φ f) (hfix : ∀ β, f β q = β q) {R : Operator (2 ^ n)}
    (hR : ZeroOnWire q R) : ZeroOnWire q (c.eval.1 * R) := by
  unfold ZeroOnWire at hR ⊢
  rw [← Matrix.mul_assoc, comm_proj_zero_of_phasedPerm_fix q c hp hfix, Matrix.mul_assoc, hR]

theorem zeroOnWire_of_mul_phasedPerm_fix (q : Wire n) (c : Circuit n)
    {φ : BitAssignment n → ℂ} {f : BitAssignment n → BitAssignment n}
    (hp : UnsignedGivens.PhasedPerm c φ f) (hfix : ∀ β, f β q = β q) {R : Operator (2 ^ n)}
    (hR : ZeroOnWire q (c.eval.1 * R)) : ZeroOnWire q R := by
  let P₀ := (QRegister.singleton q).basisOutcomeProjector 0
  have hU : c.eval.1ᴴ * c.eval.1 = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using c.eval.2.1
  have hUX : c.eval.1 * (P₀ * R) = c.eval.1 * R := by
    rw [← Matrix.mul_assoc, ← comm_proj_zero_of_phasedPerm_fix q c hp hfix, Matrix.mul_assoc, hR]
  calc P₀ * R = (c.eval.1ᴴ * c.eval.1) * (P₀ * R) := by rw [hU, Matrix.one_mul]
    _ = c.eval.1ᴴ * (c.eval.1 * R) := by rw [Matrix.mul_assoc, hUX]
    _ = R := by rw [← Matrix.mul_assoc, hU, Matrix.one_mul]

theorem zeroOnWire_mul_of_not_mem_support (q : Wire n) (c : Circuit n) (hq : q ∉ c.support)
    {R : Operator (2 ^ n)} (hR : ZeroOnWire q R) : ZeroOnWire q (c.eval.1 * R) := by
  have hdisj : Disjoint c.support (QRegister.singleton q).image := by
    rw [QRegister.image_singleton, Finset.disjoint_singleton_right]; exact hq
  have hcomm := UnsignedGivens.eval_comm_basisOutcomeProjector_of_disjoint_support c _ hdisj 0
  unfold ZeroOnWire at hR ⊢
  rw [← Matrix.mul_assoc, ← hcomm, Matrix.mul_assoc, hR]

theorem SubspaceStepU_gidneyResidSuffixDyn [Fintype Var] [DecidableEq Var] (v : Var)
    (hdB : d < B) (rCat : QRegister B n) (rASh : QRegister (B - d) n) (rC : QRegister B n)
    (w_p : Wire n) (hd : CompactGidneyDisjoint rCat rASh rC w_p)
    (rem : ℕ) (hrem : rem ≤ B - d) {R₀ : Operator (2 ^ n)}
    (hC0 : ∀ k : Fin B, B - rem ≤ k.val → ZeroOnWire (rC k) R₀) :
    SubspaceStepU R₀ ((gidneyResidSuffixRef hdB rCat rASh rC w_p hd rem hrem).eval.1 * R₀)
      (gidneyResidSuffixDyn v hdB rCat rASh rC w_p hd rem hrem) := by
  induction rem generalizing R₀ with
  | zero => exact SubspaceStepU.of_circuit _ rfl
  | succ rem ih =>
      let j := B - (rem + 1)
      have hdj : d ≤ j := by omega
      have hj : j < B := by omega
      let jf : Fin B := ⟨j, hj⟩
      let ja : Fin (B - d) := ⟨j - d, by omega⟩
      let s := gidneyResidBitStep rCat rASh rC w_p hd j hdj hj
      have hs_anc : s.anc = rC jf := by
        dsimp only [s, gidneyResidBitStep]; by_cases h0 : 0 < j <;> simp [h0, jf]
      have hpre_not : rC jf ∉ s.pre.support := by
        dsimp only [s, gidneyResidBitStep]; by_cases h0 : 0 < j
        · simp only [h0, ↓reduceDIte, Circuit.support_seq, Circuit.support_cnot,
            Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, not_or]
          have hne : (⟨j - 1, by omega⟩ : Fin B) ≠ jf := by
            intro h; have := congrArg Fin.val h; dsimp [jf] at this; omega
          exact ⟨⟨(UnsignedGivens.GidneyKickDisjoint.ne_C_C rC hne).symm, (hd.ne_cat_C jf jf).symm⟩,
            ⟨(UnsignedGivens.GidneyKickDisjoint.ne_C_C rC hne).symm, (hd.ne_A_C ja jf).symm⟩⟩
        · simp [h0]
      have hpost_not : rC jf ∉ s.post.support := by
        dsimp only [s, gidneyResidBitStep]; by_cases h0 : 0 < j
        · simp only [h0, ↓reduceDIte, Circuit.support_seq, Circuit.support_cnot,
            Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, not_or]
          have hne : (⟨j - 1, by omega⟩ : Fin B) ≠ jf := by
            intro h; have := congrArg Fin.val h; dsimp [jf] at this; omega
          exact ⟨⟨(UnsignedGivens.GidneyKickDisjoint.ne_C_C rC hne).symm, (hd.ne_A_C ja jf).symm⟩,
            ⟨(hd.ne_A_C ja jf).symm, (hd.ne_cat_C jf jf).symm⟩⟩
        · simp only [h0, ↓reduceDIte, Circuit.support_cnot, Finset.mem_insert,
            Finset.mem_singleton, not_or]
          exact ⟨(hd.ne_A_C ja jf).symm, (hd.ne_cat_C jf jf).symm⟩
      have h0 : ZeroOnWire s.anc (s.pre.eval.1 * R₀) := by
        rw [hs_anc]
        exact zeroOnWire_mul_of_not_mem_support (rC jf) s.pre hpre_not
          (hC0 jf (by dsimp [jf]; omega))
      have hpm_perm : UnsignedGivens.PhasedPerm
          (s.pre ;;ᶜ Circuit.TOFF s.c₁ s.c₂ s.anc s.h₁₂ s.h₁a s.h₂a ;;ᶜ s.midPre)
          (fun _ ↦ 1)
          (fun β ↦ gMidAssign (rCat jf) (rASh ja) (rC jf)
            (if h0 : 0 < j then β (rC ⟨j - 1, by omega⟩) else 0) β) := fun β ↦ by
        rw [one_smul]; exact gidneyResidBitStep_pre_mid_ket rCat rASh rC w_p hd j hdj hj β
      let R_in := s.midPre.eval.1 *
        ((Circuit.TOFF s.c₁ s.c₂ s.anc s.h₁₂ s.h₁a s.h₂a).eval.1 * (s.pre.eval.1 * R₀))
      have hR_in_eq : R_in =
          (s.pre ;;ᶜ Circuit.TOFF s.c₁ s.c₂ s.anc s.h₁₂ s.h₁a s.h₂a ;;ᶜ s.midPre).eval.1 * R₀ := by
        dsimp only [R_in]; simp only [Circuit.eval_seq, Submonoid.coe_mul, Matrix.mul_assoc]
      have h_in := ih (by omega) (R₀ := R_in) fun k hk ↦ by
        rw [hR_in_eq]
        refine zeroOnWire_mul_of_phasedPerm_fix (rC k) _ hpm_perm (fun β ↦ ?_)
          (hC0 k (by omega))
        have hne : rC k ≠ rC jf := fun h ↦ by
          have := congrArg Fin.val (rC.wires.injective h); dsimp [jf] at this; omega
        dsimp only [gMidAssign]
        rw [Function.update_of_ne hne, Function.update_of_ne (hd.ne_A_C ja k).symm,
          Function.update_of_ne (hd.ne_cat_C jf k).symm]
      obtain ⟨φ_all, f_all, hperm_all, hfix_all, _⟩ :=
        gidneyResidSuffixRef_spec hdB rCat rASh rC w_p hd (rem + 1) hrem
      have hall_C : ZeroOnWire (rC jf)
          ((gidneyResidSuffixRef hdB rCat rASh rC w_p hd (rem + 1) hrem).eval.1 * R₀) :=
        zeroOnWire_mul_of_phasedPerm_fix (rC jf) _ hperm_all
          (fun β ↦ hfix_all β (rC jf) fun k _ ↦ (hd.ne_cat_C k jf).symm)
          (hC0 jf (by dsimp [jf]; omega))
      refine SubspaceStepU_wrapDynamic_ref v s _ _ h0 h_in ?_
      have hproj_eq : (QRegister.singleton s.anc).basisOutcomeProjector 0 =
          (QRegister.singleton (rC jf)).basisOutcomeProjector 0 := by rw [hs_anc]
      dsimp only; rw [hproj_eq]
      apply proj_zero_of_post_eq (rC jf) s.post hpost_not
      let c_inner := gidneyResidSuffixRef hdB rCat rASh rC w_p hd rem (by omega)
      have hwrap_eq : s.post.eval.1 * ((Circuit.TOFF s.c₁ s.c₂ s.anc s.h₁₂ s.h₁a s.h₂a).eval.1 *
          (s.midPost.eval.1 * (c_inner.eval.1 * R_in))) =
          (gidneyResidSuffixRef hdB rCat rASh rC w_p hd (rem + 1) hrem).eval.1 * R₀ := by
        dsimp only [gidneyResidSuffixRef, UnsignedGivens.PhasedStep.wrapCircuit, c_inner, R_in, s,
          j]
        simp only [Circuit.eval_seq, Submonoid.coe_mul, Matrix.mul_assoc]
      rw [hwrap_eq]; exact hall_C

theorem SubspaceStepU_loadResidSuffixDyn [Fintype Var] [DecidableEq Var] (v : Var)
    (hdB : d < B) (rCat : QRegister B n) (rASh : QRegister (B - d) n) (rC : QRegister B n)
    (w_p : Wire n) (hd : CompactGidneyDisjoint rCat rASh rC w_p) {S_ctrl : Finset (Wire n)}
    (bs : CompactPhaseKickBitSteps hdB rCat rASh rC w_p S_ctrl)
    (rem : ℕ) (hrem : rem ≤ B - d) {R₀ : Operator (2 ^ n)}
    (hA0 : ∀ k : Fin B, B - rem ≤ k.val → ZeroOnWire (rASh ⟨k.val - d, by omega⟩) R₀)
    (hC0 : ∀ k : Fin B, d ≤ k.val → ZeroOnWire (rC k) R₀) :
    SubspaceStepU R₀ ((loadResidSuffixRef hdB rCat rASh rC w_p hd bs rem hrem).eval.1 * R₀)
      (loadResidSuffixDyn v hdB rCat rASh rC w_p hd bs rem hrem) := by
  induction rem generalizing R₀ with
  | zero =>
      exact SubspaceStepU_gidneyResidSuffixDyn v hdB rCat rASh rC w_p hd (B - d) le_rfl
        fun k hk ↦ hC0 k (by omega)
  | succ rem ih =>
      let j := B - (rem + 1)
      let jf : Fin B := ⟨j, by omega⟩
      let ja : Fin (B - d) := ⟨j - d, by omega⟩
      let s := bs.stepLo jf
      have hs_anc : s.anc = rASh ja := by
        rw [bs.ancLo jf]; simp only [ancSh, jf, ja, show ¬ j < d by omega, ↓reduceIte]
      obtain ⟨φ_in, f_in, hperm_in, hfix_in, _⟩ :=
        loadResidSuffixRef_spec hdB rCat rASh rC w_p hd bs rem (by omega)
      refine SubspaceStepU_cleanBitStep_wrap v (bs.cleanLo jf) hperm_in
        (fun β ↦ hfix_in β s.anc fun k _ ↦ by rw [hs_anc]; exact (hd.ne_cat_A k ja).symm)
        (fun β w hw ↦ hfix_in β w fun k _ hk ↦
          Finset.disjoint_left.mp bs.disj_ctrl_cat hw
            (QRegister.mem_image rCat _ |>.mpr ⟨k, hk.symm⟩))
        (by rw [hs_anc]; exact hA0 jf (by dsimp [jf]; omega)) _ ?_
      dsimp only
      let c_pm := s.pre ;;ᶜ Circuit.TOFF s.c₁ s.c₂ s.anc s.h₁₂ s.h₁a s.h₂a ;;ᶜ s.midPre
      have hc_pm : s.midPre.eval.1 *
          ((Circuit.TOFF s.c₁ s.c₂ s.anc s.h₁₂ s.h₁a s.h₂a).eval.1 * (s.pre.eval.1 * R₀)) =
          c_pm.eval.1 * R₀ := by
        dsimp only [c_pm]; simp only [Circuit.eval_seq, Submonoid.coe_mul, Matrix.mul_assoc]
      rw [hc_pm]
      refine ih (by omega) (fun k hk ↦ ?_) (fun k hk ↦ ?_)
      · refine zeroOnWire_mul_of_phasedPerm_fix _ c_pm (bs.cleanLo jf).pre_mid_perm (fun β ↦ ?_)
          (hA0 k (by omega))
        rw [hs_anc]; apply Function.update_of_ne; intro h
        have := congrArg Fin.val (rASh.wires.injective h); dsimp [ja] at this; omega
      · refine zeroOnWire_mul_of_phasedPerm_fix _ c_pm (bs.cleanLo jf).pre_mid_perm (fun β ↦ ?_)
          (hC0 k hk)
        rw [hs_anc]; exact Function.update_of_ne (hd.ne_A_C ja k).symm _ _

attribute [irreducible] gidneyResidSuffixDyn loadResidSuffixDyn

end CompactKickSoundness

end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.PhaseB154Pi145Select

end

/-!
# Low-Bit `π145` `SiZero` Router, `Core145Bundle` Engine & `StageA` Core (`160` Wires)

Constructs the `State24` `RouterStep` evaluator, the core-polymorphic `23`-wire `0`-`TOFF`
`SELECT` engine (`Core145Bundle`, `selectLowBitCoreUnitDyn`, `selectLowBitCoreDyn`), the `61`-AND
(`14 + 47`, `244 T`) `23`-wire `π145` `SiZero` Stage-1 router, the shared pass-indexed pure
unitaries `(selectLowBitPi145FwdPureUnitary, selectLowBitPi145BwdPureUnitary)`, and the
`159`-inner-wire `11,818-T` `stageACore145Bundle` (`12,526 T/pass`, `160 ≤ sUb`).

## References
- D. W. Berry, C. Gidney, M. Motta, J. R. McClean, and R. Babbush, "Qubitization of Arbitrary
  Basis Quantum Chemistry Leveraging Sparsity and Low Rank Factorization," *Quantum* **3**, 208
  (2019), DOI: `10.22331/q-2019-12-02-208`.
- R. Babbush, C. Gidney, D. W. Berry, N. Wiebe, J. McClean, A. Paler, A. Fowler, and H. Neven,
  "Encoding Electronic Spectra in Quantum Circuits with Linear T Complexity," *Phys. Rev. X* **8**,
  041015 (2018), DOI: `10.1103/PhysRevX.8.041015`.
- J. Lee, D. W. Berry, C. Gidney, W. J. Huggins, J. R. McClean, N. Wiebe, and R. Babbush,
  "Even More Efficient Quantum Computations of Chemistry Through Tensor Hypercontraction,"
  *PRX Quantum* **2**, 030305 (2021), DOI: `10.1103/PRXQuantum.2.030305`.
-/

@[expose] public section
namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.LowBitPi145Select
open QuantumComputation.Specs QuantumComputation.Specs.P450

open Operator QProg Matrix HermitianMat Real CoherentAlias
open QuantumComputation.Specs Solution QuantumComputation.Specs.P450 Solution
open Solution.CircuitModular Solution.GivensOps
open Solution.BlockEncodingCore Solution.BlockEncodingCircuit
open Solution.SelectSwapQROM Solution.GivensCascade
open Solution.SelectRouter10 Solution.TopIntegrationBridge
open Solution.Lac2Fused184Select Solution.Lac2Fused184SelectWrap Solution.Router10Lac2Select
open Solution.Phase2MidSandwich Solution.PolymorphicFused184Select Solution.Lac2ZeroPar183Select
open Solution.CompactFoldedSelect Solution.ReordOuter13Bridge Solution.CompactStepFast176Select
open Solution.StepEncK Solution.StepDecK Solution.CompactStepFast175Core
open Solution.CompactOuter9Bound50Core Solution.CompactOuter9Bound50Select
open Solution.MobiusOptSubcube163Walk
open Solution.CompactTuned162StepWalk Solution.CompactTuned162StepZeroCmp20
open Solution.CompactZeroCmp20OuterParam Solution.CompactStepZeroCmp20OuterParam
open Solution.Balanced160Select Solution.Pi145SOSPermBridge Solution.OneHotSimulates
open WalkQPEBridge WalkQPEBridgeXMeas WalkQPEFlexBridge Solution.CleanDyn
open scoped Matrix BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator Circuit.Notation
local instance (priority := 1000000) instNeZeroTwoPowPi145_2 (k : ℕ) : NeZero (2 ^ k) :=
    ⟨(Nat.two_pow_pos k).ne'⟩
/-! ## Section 1: Kernel-Reducible `State24` Evaluator & `liftRouterStepsN` -/

/-- Packed 8-bit boolean tuple for kernel-reducible `RouterStep` evaluation. -/
structure State8 where
  (b0 b1 b2 b3 b4 b5 b6 b7 : Bool)
  deriving DecidableEq
/-- Read bit `i` from a `State8`. -/
@[inline] def State8.get8 (s : State8) (i : Fin 8) : Bool :=
  match i with
  | ⟨0, _⟩ => s.b0 | ⟨1, _⟩ => s.b1 | ⟨2, _⟩ => s.b2 | ⟨3, _⟩ => s.b3
  | ⟨4, _⟩ => s.b4 | ⟨5, _⟩ => s.b5 | ⟨6, _⟩ => s.b6 | ⟨7, _⟩ => s.b7
/-- Update bit `i` of a `State8` to `v`. -/
@[inline] def State8.set8 (s : State8) (i : Fin 8) (v : Bool) : State8 :=
  match i with
  | ⟨0, _⟩ => { s with b0 := v } | ⟨1, _⟩ => { s with b1 := v }
  | ⟨2, _⟩ => { s with b2 := v } | ⟨3, _⟩ => { s with b3 := v }
  | ⟨4, _⟩ => { s with b4 := v } | ⟨5, _⟩ => { s with b5 := v }
  | ⟨6, _⟩ => { s with b6 := v } | ⟨7, _⟩ => { s with b7 := v }
theorem State8.get8_set8 (s : State8) (i j : Fin 8) (v : Bool) : (s.set8 i v).get8 j = if j = i
    then v else s.get8 j := by
  rcases s with ⟨_, _, _, _, _, _, _, _⟩; fin_cases i <;> fin_cases j <;> rfl
theorem State8.ext8 {s₁ s₂ : State8} (h : ∀ i : Fin 8, s₁.get8 i = s₂.get8 i) : s₁ = s₂ := by
  rcases s₁ with ⟨_, _, _, _, _, _, _, _⟩; rcases s₂ with ⟨_, _, _, _, _, _, _, _⟩
  have h0 := h 0; have h1 := h 1; have h2 := h 2; have h3 := h 3
  have h4 := h 4; have h5 := h 5; have h6 := h 6; have h7 := h 7
  dsimp [State8.get8] at h0 h1 h2 h3 h4 h5 h6 h7; subst h0 h1 h2 h3 h4 h5 h6 h7; rfl
/-- All-false `State8`. -/
@[inline] def zeroState8 : State8 := ⟨false, false, false, false, false, false, false, false⟩
/-- Packed 24-bit boolean tuple built from three `State8` octets. -/
structure State24 where
  (q0 q1 q2 : State8)
  deriving DecidableEq
/-- Read bit `i` from a `State24`. -/
@[inline] def State24.get24 (s : State24) (i : Fin 24) : Bool := if h0 : i.val < 8 then s.q0.get8
    ⟨i.val, h0⟩ else if h1 : i.val < 16 then s.q1.get8 ⟨i.val - 8, by omega⟩
  else s.q2.get8 ⟨i.val - 16, by omega⟩
/-- Update bit `i` of a `State24` to `v`. -/
@[inline] def State24.set24 (s : State24) (i : Fin 24) (v : Bool) : State24 :=
  if h0 : i.val < 8 then { s with q0 := s.q0.set8 ⟨i.val, h0⟩ v }
  else if h1 : i.val < 16 then { s with q1 := s.q1.set8 ⟨i.val - 8, by omega⟩ v }
  else { s with q2 := s.q2.set8 ⟨i.val - 16, by omega⟩ v }
theorem State24.get24_set24 (s : State24) (i j : Fin 24) (v : Bool) : (s.set24 i v).get24 j = if j
    = i then v else s.get24 j := by
  rcases s with ⟨_, _, _⟩
  fin_cases i <;> fin_cases j <;> simp [State24.set24, State24.get24, State8.get8_set8]
theorem State24.ext24 {s₁ s₂ : State24} (h : ∀ i : Fin 24, s₁.get24 i = s₂.get24 i) : s₁ = s₂ := by
  rcases s₁ with ⟨_, _, _⟩; rcases s₂ with ⟨_, _, _⟩; congr 1
  · exact State8.ext8 fun i ↦ by
      fin_cases i <;> [exact h 0; exact h 1; exact h 2; exact h 3;
        exact h 4; exact h 5; exact h 6; exact h 7]
  · exact State8.ext8 fun i ↦ by
      fin_cases i <;> [exact h 8; exact h 9; exact h 10; exact h 11;
        exact h 12; exact h 13; exact h 14; exact h 15]
  · exact State8.ext8 fun i ↦ by
      fin_cases i <;> [exact h 16; exact h 17; exact h 18; exact h 19;
        exact h 20; exact h 21; exact h 22; exact h 23]
/-- Lift a single `RouterStep k` along an injective `k`-wire register `r : QRegister k N`. -/
def RouterStep.liftN {k N : ℕ} (r : QRegister k N) : RouterStep k → RouterStep N
  | .x t => .x (r t)
  | .cnot c t hne => .cnot (r c) (r t) (r.wires.injective.ne hne)
  | .andAlloc c₁ c₂ anc h₁₂ h₁a h₂a =>
      .andAlloc (r c₁) (r c₂) (r anc) (r.wires.injective.ne h₁₂) (r.wires.injective.ne h₁a)
        (r.wires.injective.ne h₂a)
  | .andFree c₁ c₂ anc h₁₂ h₁a h₂a =>
      .andFree (r c₁) (r c₂) (r anc) (r.wires.injective.ne h₁₂) (r.wires.injective.ne h₁a)
        (r.wires.injective.ne h₂a)
/-- Lift a `RouterStep k` list along `r : QRegister k N`. -/
def liftRouterStepsN {k N : ℕ} (r : QRegister k N) (steps : List (RouterStep k)) : List (RouterStep
    N) := steps.map (RouterStep.liftN r)
@[simp] theorem numRouterAnds_liftRouterStepsN {k N : ℕ} (r : QRegister k N) (steps : List
    (RouterStep k)) : numRouterAnds (liftRouterStepsN r steps) = numRouterAnds steps := by
  induction steps with
  | nil => rfl
  | cons s rest ih => cases s <;> simpa [liftRouterStepsN, RouterStep.liftN, numRouterAnds] using ih
theorem touchesIn_liftRouterStepsN {k N : ℕ} (r : QRegister k N) (W : Wire N → Prop) (hr : ∀ u :
    Wire k, W (r u)) (steps : List (RouterStep k)) : ∀ s ∈ liftRouterStepsN r steps, s.TouchesIn W
    := by
  intro s hs; rcases List.mem_map.mp hs with ⟨s₀, _, rfl⟩
  cases s₀ with
  | x t => exact hr t
  | cnot c t _ => exact ⟨hr c, hr t⟩
  | andAlloc c₁ c₂ anc _ _ _ => exact ⟨hr c₁, hr c₂, hr anc⟩
  | andFree c₁ c₂ anc _ _ _ => exact ⟨hr c₁, hr c₂, hr anc⟩
/-- Execute a single `RouterStep k` (`k ≤ 24`) on `State24`, checking ancilla conditions. -/
@[inline] def runStep24 {k : ℕ} (hk : k ≤ 24) (s : RouterStep k) (st : State24) : Option State24 :=
  match s with
  | .x t =>
      let t' : Fin 24 := ⟨t.val, by omega⟩; some (st.set24 t' (!st.get24 t'))
  | .cnot c t _ =>
      let c' : Fin 24 := ⟨c.val, by omega⟩; let t' : Fin 24 := ⟨t.val, by omega⟩
      some (st.set24 t' (xor (st.get24 t') (st.get24 c')))
  | .andAlloc c₁ c₂ anc _ _ _ =>
      let c₁' : Fin 24 := ⟨c₁.val, by omega⟩; let c₂' : Fin 24 := ⟨c₂.val, by omega⟩
      let a' : Fin 24 := ⟨anc.val, by omega⟩
      if !st.get24 a' then some (st.set24 a' (st.get24 c₁' && st.get24 c₂')) else none
  | .andFree c₁ c₂ anc _ _ _ =>
      let c₁' : Fin 24 := ⟨c₁.val, by omega⟩; let c₂' : Fin 24 := ⟨c₂.val, by omega⟩
      let a' : Fin 24 := ⟨anc.val, by omega⟩
      if st.get24 a' == (st.get24 c₁' && st.get24 c₂') then some (st.set24 a' false) else none
/-- Execute a list of `RouterStep k` (`k ≤ 24`) on `State24`. -/
def runSteps24 {k : ℕ} (hk : k ≤ 24) : List (RouterStep k) → State24 → Option State24
  | [], st => some st
  | s :: rest, st =>
      match runStep24 hk s st with
      | none => none
      | some st' => runSteps24 hk rest st'
/-- Bitwise multiplex two `State8` octets under `m0..m7`. -/
@[inline] def mergeState8 (m0 m1 m2 m3 m4 m5 m6 m7 : Bool) (a b : State8) : State8 := ⟨if m0 then
    a.b0 else b.b0, if m1 then a.b1 else b.b1, if m2 then a.b2 else b.b2, if m3 then a.b3 else
    b.b3, if m4 then a.b4 else b.b4, if m5 then a.b5 else b.b5, if m6 then a.b6 else b.b6, if m7
    then a.b7 else b.b7⟩
/-- Bitwise multiplex two `State24` tuples according to `mask : Fin 24 → Bool`. -/
@[inline] def mergeState24 (mask : Fin 24 → Bool) (a b : State24) : State24 := ⟨mergeState8 (mask
    0) (mask 1) (mask 2) (mask 3) (mask 4) (mask 5) (mask 6) (mask 7) a.q0 b.q0, mergeState8 (mask
    8) (mask 9) (mask 10) (mask 11) (mask 12) (mask 13) (mask 14) (mask 15) a.q1 b.q1, mergeState8
    (mask 16) (mask 17) (mask 18) (mask 19) (mask 20) (mask 21) (mask 22) (mask 23) a.q2 b.q2⟩
theorem get24_mergeState24 (mask : Fin 24 → Bool) (a b : State24) (i : Fin 24) : (mergeState24 mask
    a b).get24 i = if mask i then a.get24 i else b.get24 i := by
  rcases a with ⟨⟨_, _, _, _, _, _, _, _⟩, ⟨_, _, _, _, _, _, _, _⟩, ⟨_, _, _, _, _, _, _, _⟩⟩
  rcases b with ⟨⟨_, _, _, _, _, _, _, _⟩, ⟨_, _, _, _, _, _, _, _⟩, ⟨_, _, _, _, _, _, _, _⟩⟩
  fin_cases i <;> rfl
theorem set24_mergeState24_of_true (mask : Fin 24 → Bool) (a b : State24) (i : Fin 24) (hi : mask i
    = true) (v : Bool) : (mergeState24 mask a b).set24 i v = mergeState24 mask (a.set24 i v) b :=
    by
  apply State24.ext24; intro j
  rw [State24.get24_set24, get24_mergeState24, get24_mergeState24, State24.get24_set24]
  by_cases hji : j = i
  · subst hji; simp [hi]
  · simp [hji]
theorem runSteps24_append {k : ℕ} (hk : k ≤ 24) (l₁ l₂ : List (RouterStep k)) (st st₁ : State24)
    (h₁ : runSteps24 hk l₁ st = some st₁) : runSteps24 hk (l₁ ++ l₂) st = runSteps24 hk l₂ st₁ :=
    by
  induction l₁ generalizing st with
  | nil => dsimp [runSteps24] at h₁; injection h₁ with h; subst h; rfl
  | cons s rest ih =>
      dsimp [runSteps24] at h₁ ⊢
      cases hs : runStep24 hk s st with
      | none => rw [hs] at h₁; cases h₁
      | some st' => rw [hs] at h₁; exact ih st' h₁
/-- Check whether every wire touched by `s : RouterStep k` (`k ≤ 24`) satisfies `mask`. -/
def routerStepInMask24 {k : ℕ} (hk : k ≤ 24) (mask : Fin 24 → Bool) : RouterStep k → Bool
  | .x t => mask ⟨t.val, by omega⟩
  | .cnot c t _ => mask ⟨c.val, by omega⟩ && mask ⟨t.val, by omega⟩
  | .andAlloc c₁ c₂ anc _ _ _ =>
      mask ⟨c₁.val, by omega⟩ && mask ⟨c₂.val, by omega⟩ && mask ⟨anc.val, by omega⟩
  | .andFree c₁ c₂ anc _ _ _ =>
      mask ⟨c₁.val, by omega⟩ && mask ⟨c₂.val, by omega⟩ && mask ⟨anc.val, by omega⟩
theorem runStep24_merge {k : ℕ} (hk : k ≤ 24) (mask : Fin 24 → Bool) (s : RouterStep k) (hm :
    routerStepInMask24 hk mask s = true) (st st' bg : State24) (hs : runStep24 hk s st = some st')
    : runStep24 hk s (mergeState24 mask st bg) = some (mergeState24 mask st' bg) := by
  cases s with
  | x t =>
      dsimp only [routerStepInMask24] at hm
      dsimp only [runStep24] at hs ⊢; injection hs with hEq; subst hEq
      rw [get24_mergeState24, hm, ite_eq_left rfl, set24_mergeState24_of_true _ _ _ _ hm]
  | cnot c t _ =>
      dsimp only [routerStepInMask24] at hm; obtain ⟨hc, ht⟩ := Bool.and_eq_true_iff.mp hm
      dsimp only [runStep24] at hs ⊢; injection hs with hEq; subst hEq
      rw [get24_mergeState24, get24_mergeState24, hc, ht, ite_eq_left rfl, ite_eq_left rfl,
        set24_mergeState24_of_true _ _ _ _ ht]
  | andAlloc c₁ c₂ anc _ _ _ =>
      dsimp only [routerStepInMask24] at hm; obtain ⟨hc12, ha⟩ := Bool.and_eq_true_iff.mp hm
      obtain ⟨hc1, hc2⟩ := Bool.and_eq_true_iff.mp hc12; dsimp only [runStep24] at hs ⊢
      rw [get24_mergeState24, get24_mergeState24, get24_mergeState24, ha, hc1, hc2, ite_eq_left
        rfl, ite_eq_left rfl, ite_eq_left rfl]
      cases hanc : st.get24 ⟨anc.val, by omega⟩
      · rw [hanc] at hs; simp only [Bool.not_false, ↓reduceIte] at hs ⊢
        injection hs with hEq; subst hEq; rw [set24_mergeState24_of_true _ _ _ _ ha]
      · rw [hanc] at hs; simp at hs
  | andFree c₁ c₂ anc _ _ _ =>
      dsimp only [routerStepInMask24] at hm; obtain ⟨hc12, ha⟩ := Bool.and_eq_true_iff.mp hm
      obtain ⟨hc1, hc2⟩ := Bool.and_eq_true_iff.mp hc12; dsimp only [runStep24] at hs ⊢
      rw [get24_mergeState24, get24_mergeState24, get24_mergeState24, ha, hc1, hc2, ite_eq_left
        rfl, ite_eq_left rfl, ite_eq_left rfl]
      cases heqB : (st.get24 ⟨anc.val, by omega⟩ ==
          (st.get24 ⟨c₁.val, by omega⟩ && st.get24 ⟨c₂.val, by omega⟩))
      · rw [heqB] at hs; simp at hs
      · rw [heqB] at hs; simp only [↓reduceIte] at hs ⊢
        injection hs with hEq; subst hEq; rw [set24_mergeState24_of_true _ _ _ _ ha]
theorem runSteps24_merge {k : ℕ} (hk : k ≤ 24) (mask : Fin 24 → Bool) (steps : List (RouterStep k))
    (hm : steps.all (routerStepInMask24 hk mask) = true) (st st' bg : State24) (hs : runSteps24 hk
    steps st = some st') : runSteps24 hk steps (mergeState24 mask st bg) = some (mergeState24 mask
    st' bg) := by
  induction steps generalizing st with
  | nil => dsimp [runSteps24] at hs; injection hs with hEq; subst hEq; rfl
  | cons s rest ih =>
      simp only [List.all_cons, Bool.and_eq_true] at hm; dsimp [runSteps24] at hs ⊢
      cases h1 : runStep24 hk s st with
      | none => rw [h1] at hs; cases hs
      | some st1 =>
          rw [h1] at hs; rw [runStep24_merge hk mask s hm.1 st st1 bg h1]; exact ih hm.2 st1 hs
theorem liftRouterStepN_spec24 {k N : ℕ} (hk : k ≤ 24) (r : QRegister k N) (s : RouterStep k) (st
    st' : State24) (hs : runStep24 hk s st = some st') (β : BitAssignment N)
    (hβ : ∀ u : Wire k, β (r u) = if st.get24 ⟨u.val, by omega⟩ then 1 else 0) : (match s with
     | .x _ => True | .cnot _ _ _ => True
     | .andAlloc _ _ anc _ _ _ => β (r anc) = 0
     | .andFree c₁ c₂ anc _ _ _ => β (r anc) = β (r c₁) * β (r c₂)) ∧
    (∀ u : Wire k,
      ((RouterStep.liftN r s).assign β) (r u) = if st'.get24 ⟨u.val, by omega⟩ then 1 else 0) ∧
    (∀ w : Wire N, w ∉ Set.range r.wires → ((RouterStep.liftN r s).assign β) w = β w) := by
  have hFinEq {u v : Wire k} : ((⟨u.val, by omega⟩ : Fin 24) = ⟨v.val, by omega⟩) ↔ u = v :=
    ⟨fun h ↦ Fin.ext (congrArg (Fin.val : Fin 24 → ℕ) h), fun h ↦ by subst h; rfl⟩
  have hUpd (t : Wire k) (vB : Bool) (zv : ZMod 2) (hzv : zv = if vB then 1 else 0) (u : Wire k) :
    Function.update β (r t) zv (r u) =
        if (st.set24 ⟨t.val, by omega⟩ vB).get24 ⟨u.val, by omega⟩ then 1 else 0 := by
    by_cases hut : u = t
    · subst hut; rw [Function.update_self, State24.get24_set24, ite_eq_left rfl, hzv]
    · rw [Function.update_of_ne (r.wires.injective.ne hut), hβ u, State24.get24_set24, ite_eq_right
        (mt hFinEq.mp hut)]
  cases s with
  | x t =>
      dsimp only [runStep24] at hs; injection hs with hEq; subst hEq
      refine ⟨trivial, hUpd t _ _ (by rw [hβ t]; cases st.get24 ⟨t.val, by omega⟩ <;> decide),
        fun w hw ↦ Function.update_of_ne (fun h ↦ hw ⟨t, h.symm⟩) _ _⟩
  | cnot c t _ =>
      dsimp only [runStep24] at hs; injection hs with hEq; subst hEq
      refine ⟨trivial, hUpd t _ _ (by
          rw [hβ t, hβ c]; cases st.get24 ⟨t.val, by omega⟩ <;>
            cases st.get24 ⟨c.val, by omega⟩ <;> decide),
        fun w hw ↦ Function.update_of_ne (fun h ↦ hw ⟨t, h.symm⟩) _ _⟩
  | andAlloc c₁ c₂ anc _ _ _ =>
      dsimp only [runStep24] at hs; cases ha : st.get24 ⟨anc.val, by omega⟩
      · rw [ha] at hs; simp only [Bool.not_false, ↓reduceIte] at hs; injection hs with hEq
        subst hEq
        refine ⟨by dsimp only; rw [hβ anc, ha]; rfl, hUpd anc _ _ (by
            rw [hβ anc, ha, hβ c₁, hβ c₂]; cases st.get24 ⟨c₁.val, by omega⟩ <;>
              cases st.get24 ⟨c₂.val, by omega⟩ <;> decide),
          fun w hw ↦ Function.update_of_ne (fun h ↦ hw ⟨anc, h.symm⟩) _ _⟩
      · rw [ha] at hs; simp at hs
  | andFree c₁ c₂ anc _ _ _ =>
      dsimp only [runStep24] at hs
      cases heqB : (st.get24 ⟨anc.val, by omega⟩ ==
          (st.get24 ⟨c₁.val, by omega⟩ && st.get24 ⟨c₂.val, by omega⟩))
      · rw [heqB] at hs; simp at hs
      · rw [heqB] at hs; simp only [↓reduceIte] at hs; injection hs with hEq; subst hEq
        have haEq := beq_iff_eq.mp heqB
        refine ⟨by dsimp only; rw [hβ anc, haEq, hβ c₁, hβ c₂]
                   cases st.get24 ⟨c₁.val, by omega⟩ <;>
                     cases st.get24 ⟨c₂.val, by omega⟩ <;> decide,
          hUpd anc _ _ (by
            rw [hβ anc, haEq, hβ c₁, hβ c₂]; cases st.get24 ⟨c₁.val, by omega⟩ <;>
              cases st.get24 ⟨c₂.val, by omega⟩ <;> decide),
          fun w hw ↦ Function.update_of_ne (fun h ↦ hw ⟨anc, h.symm⟩) _ _⟩
theorem liftRouterStepsN_spec24 {k N : ℕ} (hk : k ≤ 24) (r : QRegister k N) (steps : List
    (RouterStep k)) (st st' : State24) (hs : runSteps24 hk steps st = some st') (β : BitAssignment
    N) (hβ : ∀ u : Wire k, β (r u) = if st.get24 ⟨u.val, by omega⟩ then 1 else 0) :
    routerStepsOk (liftRouterStepsN r steps) β ∧
    (∀ u : Wire k, routerStepsAssign (liftRouterStepsN r steps) β (r u) =
      if st'.get24 ⟨u.val, by omega⟩ then 1 else 0) ∧
    (∀ w : Wire N, w ∉ Set.range r.wires → routerStepsAssign (liftRouterStepsN r steps) β w = β w)
      := by
  induction steps generalizing st β with
  | nil =>
      dsimp only [runSteps24] at hs; injection hs with hEq; subst hEq
      exact ⟨trivial, hβ, fun _ _ ↦ rfl⟩
  | cons s rest ih =>
      dsimp only [runSteps24] at hs
      cases h1 : runStep24 hk s st with
      | none => rw [h1] at hs; cases hs
      | some st1 =>
          rw [h1] at hs; obtain ⟨hok1, hβ1, hout1⟩ := liftRouterStepN_spec24 hk r s st st1 h1 β hβ
          obtain ⟨hok2, hβ2, hout2⟩ := ih st1 hs ((RouterStep.liftN r s).assign β) hβ1
          refine ⟨?_, hβ2, fun w hw ↦ (hout2 w hw).trans (hout1 w hw)⟩
          cases s <;> first | exact hok2 | exact ⟨hok1, hok2⟩
/-! ## Section 2: Core-Polymorphic `23`-Wire `SELECT` Engine (`sUb ≥ 1 + kInner`) -/

/-- Width bound `23 ≤ 24` for `State24` evaluation of `RouterStep 23` programs. -/
theorem hk23Le24 : 23 ≤ 24 := by decide
/-- Initial `State24` of `rRouter23`: `w0 = false`, `w1..w16 = x16 0..15`, `w17..w23 = false`. -/
def initState23 (x16 : Fin 16 → Bool) : State24 := ⟨⟨false, x16 0, x16 1, x16 2, x16 3, x16 4, x16
    5, x16 6⟩, ⟨x16 7, x16 8, x16 9, x16 10, x16 11, x16 12, x16 13, x16 14⟩, ⟨x16 15, false,
    false, false, false, false, false, false⟩⟩
theorem get24_initState23 (x16 : Fin 16 → Bool) (u : Wire 23) :
    (initState23 x16).get24 ⟨u.val, by omega⟩ = if u.val = 0 then false
      else if h17 : u.val < 17 then x16 ⟨u.val - 1, by omega⟩ else false := by
  fin_cases u <;> rfl
/-- `10`-wire Stage-2 control indices inside `23 = (1 + 16) + 6`: `[10, 8, 11, 12, 13, 14, 5, 6, 7,
0]`. -/
def routed10Wire23 (u : Fin 10) : Wire 23 :=
  ⟨(routed10Wire17 u).val, by have := (routed10Wire17 u).isLt; omega⟩
/-- Routed `10`-bit Stage-2 control word extracted from a `State24`. -/
def ctrl10OfState24 (st : State24) (u : Fin 10) : Bool :=
  st.get24 ⟨(routed10Wire23 u).val, by have := (routed10Wire23 u).isLt; omega⟩
/-- Routed spin-swap bit `sigSel` on wire `15` (`rCtrl16 14`) of `st : State24`. -/
def sigSelOfState24 (st : State24) : Bool := st.get24 15
/-- Entry Clifford phase kick `(!w8) && w16` evaluated on `stA : State24` after `stepsA`. -/
def signBitOfState24 (stA : State24) : Bool := (!stA.get24 8) && stA.get24 16
/-- `12`-bit `selectGenCoreBranch` controls produced by `(specA, specB)` on `x16`. -/
def y12OfState24 (specA : (Fin 16 → Bool) → State24) (specB : State24 → State24) (x16 : Fin 16 →
    Bool) (j : Fin 12) : Bool :=
  let stA := specA x16; let stB := specB stA
  if h10 : j.val < 10 then ctrl10OfState24 stB ⟨j.val, h10⟩
  else if j.val = 10 then sigSelOfState24 stB else signBitOfState24 stA
/-- Snapshot the `23` bits of `rRouter23` in `β` into a `State24` (`w23 = false`). -/
def state24OfRouter23 {N : ℕ} (rRouter23 : QRegister 23 N) (β : BitAssignment N) : State24 :=
  let b (u : Wire 23) : Bool := decide (β (rRouter23 u) = 1)
  ⟨⟨b 0, b 1, b 2, b 3, b 4, b 5, b 6, b 7⟩, ⟨b 8, b 9, b 10, b 11, b 12, b 13, b 14, b 15⟩, ⟨b 16,
    b 17, b 18, b 19, b 20, b 21, b 22, false⟩⟩
theorem get24_state24OfRouter23 {N : ℕ} (rRouter23 : QRegister 23 N) (β : BitAssignment N) (i : Fin
    24) : (state24OfRouter23 rRouter23 β).get24 i = if h : i.val < 23 then decide (β (rRouter23
    ⟨i.val, h⟩) = 1) else false := by
  fin_cases i <;> rfl
theorem assign_of_state24OfRouter23_eq {N : ℕ} (rRouter23 : QRegister 23 N) (β : BitAssignment N)
    (st : State24) (h : state24OfRouter23 rRouter23 β = st) (u : Wire 23) :
    β (rRouter23 u) = if st.get24 ⟨u.val, by omega⟩ then 1 else 0 := by
  have hu := congrArg (fun s ↦ s.get24 ⟨u.val, by omega⟩) h
  rw [get24_state24OfRouter23, dite_eq_left u.isLt] at hu; rw [← hu]
  rcases UnsignedGivens.zmod2_eq_zero_or_one (β (rRouter23 u)) with h0 | h0 <;> rw [h0] <;> decide
/-- Decode a `23`-bit index `c23 : Fin (2 ^ 23)` into `State24` (`w23 = false`). -/
noncomputable def state24OfFin23 (c23 : Fin (2 ^ 23)) : State24 :=
  let b (u : Wire 23) : Bool := bitsOfFin 23 c23 u
  ⟨⟨b 0, b 1, b 2, b 3, b 4, b 5, b 6, b 7⟩, ⟨b 8, b 9, b 10, b 11, b 12, b 13, b 14, b 15⟩, ⟨b 16,
    b 17, b 18, b 19, b 20, b 21, b 22, false⟩⟩
theorem state24OfFin23_localIdx_eq {N : ℕ} (rRouter23 : QRegister 23 N) (β : BitAssignment N) :
    state24OfFin23 (UnsignedGivens.localIdx rRouter23 β) = state24OfRouter23 rRouter23 β := by
  have hb (u : Wire 23) : bitsOfFin 23 (UnsignedGivens.localIdx rRouter23 β) u =
    decide (β (rRouter23 u) =
    1) := by
    change decide (basisBits 23 ((basisBits 23).symm (fun i ↦ β (rRouter23 i))) u = 1) = _
    rw [congrFun (UnsignedGivens.basisBits_symm_eq (fun i ↦ β (rRouter23 i))) u]
  dsimp only [state24OfFin23, state24OfRouter23]; simp only [hb]
/-- Bundled Stage-2 register layout `[rSpin : 58 | rCtrl10 : 10 | rCat11 : 11 | rInner : kInner]`.
-/
structure Core145Layout (kInner n : ℕ) where
  rFull : QRegister (((58 + 10) + 11) + kInner) n
/-- `58`-qubit first spin block of `L : Core145Layout kInner n`. -/
def Core145Layout.rSpin {kInner n : ℕ} (L : Core145Layout kInner n) : QRegister 58 n :=
    L.rFull.compose (QRegister.block 0 58 (by omega) )
/-- `10`-qubit Stage-2 control register of `L : Core145Layout kInner n`. -/
def Core145Layout.rCtrl10 {kInner n : ℕ} (L : Core145Layout kInner n) : QRegister 10 n :=
    L.rFull.compose (QRegister.block 58 10 (by omega) )
/-- `11`-qubit phase-gradient catalyst register of `L : Core145Layout kInner n`. -/
def Core145Layout.rCat11 {kInner n : ℕ} (L : Core145Layout kInner n) : QRegister 11 n :=
    L.rFull.compose (QRegister.block 68 11 (by omega) )
/-- `kInner`-qubit clean Stage-2 workspace register of `L : Core145Layout kInner n`. -/
def Core145Layout.rInner {kInner n : ℕ} (L : Core145Layout kInner n) : QRegister kInner n :=
    L.rFull.compose (QRegister.block 79 kInner (by omega) )
/-- `8`-qubit `pair8` slice `rCtrl10[2..9]` of `L : Core145Layout kInner n`. -/
def Core145Layout.rSelPair8 {kInner n : ℕ} (L : Core145Layout kInner n) : QRegister 8 n :=
    L.rCtrl10.compose Lac2Fused184Select.selPair10
theorem Core145Layout.hsc {kInner n : ℕ} (L : Core145Layout kInner n) : L.rSpin.DisjointWires
    L.rCtrl10 := by
  rw [QRegister.disjoint_iff]; intro _ _ heq
  have hv := congrArg Fin.val (L.rFull.wires.injective heq); simp at hv; omega
theorem Core145Layout.hac {kInner n : ℕ} (L : Core145Layout kInner n) : (L.rSpin.concat L.rCtrl10
    L.hsc).DisjointWires L.rCat11 := by
  refine QRegister.disjointWires_concat_left L.hsc ?_ ?_ <;>
    (rw [QRegister.disjoint_iff]; intro _ _ heq
     have hv := congrArg Fin.val (L.rFull.wires.injective heq); simp at hv; omega)
/-- Valid Stage-2 entry subspace (`pair8 < 145` and `rInner = 0`) for `L : Core145Layout kInner n`.
-/
def sValidCore {kInner n : ℕ} (L : Core145Layout kInner n) (β : BitAssignment n) : Prop :=
    (UnsignedGivens.localIdx L.rSelPair8 β).val < 145 ∧ ∀ idx : Fin kInner, β (L.rInner idx) = 0
/-- Abstract `145`-leaf Stage-2 core package parameterized by `(kInner, tCore)`. -/
structure Core145Bundle (kInner tCore : ℕ) (actFlipMask : Fin 145 → Bool)
    (orbitalOf : Fin 145 → Bool → Fin 319) (negMask : Fin 145 → Bool) where
  hk6 : 6 ≤ kInner
  coreUnitDyn : ∀ {n : ℕ}, Core145Layout kInner n → DynamicCircuit Unit n
  count_toff : ∀ {n : ℕ} (L : Core145Layout kInner n), (coreUnitDyn L).count .TOFF = 0
  count_t : ∀ {n : ℕ} (L : Core145Layout kInner n), (coreUnitDyn L).count .T = tCore
  simCore : ∀ {n : ℕ} (L : Core145Layout kInner n), ∃ wPhased : Fin (2 ^ 10) → Unitary (2 ^ (58 +
    11)), DiagProjSimulates (ketPredProj (sValidCore L)) (((L.rSpin.concat L.rCat11
    (OneHotMux.disj_sys_cat_of L.hsc L.hac)).concat L.rCtrl10 (OneHotMux.disj_sysCat_ctrl_of L.hsc
    L.hac)).embedUnitary (UnsignedGivens.muxCtrlUnitary wPhased)) (coreUnitDyn L) ∧ ∀ (c10 :
      Fin (2 ^ 10))
    (ψ : Fin (2 ^ 58) → ℂ), (wPhased c10).1 *ᵥ prodState ψ (phaseGradientLowFactor 11 3) =
    prodState ((phase2Bal145PhasedBranch actFlipMask orbitalOf negMask c10).1 *ᵥ ψ)
    (phaseGradientLowFactor 11 3)
/-- Canonical index `6 + idx` inside `Fin kInner` for non-router inner scratch wires. -/
def innerAfter6Idx {kInner : ℕ} (idx : Fin (kInner - 6)) : Fin kInner := ⟨6 + idx.val, by omega⟩
/-- `23`-wire router register `(rScr[0..0] ++ rCtrl16) ++ rScr[1..6]` (`6 ≤ kInner`). -/
def lowBitRouter23 {N kInner : ℕ} (hk6 : 6 ≤ kInner) (wOuter wInner2 : ℕ) (wNegIn :
    Wire wInner2) (rMain :
    QRegister (nUB wOuter wInner2 + 11) N) (rScr : QRegister (1 + kInner) N) (hdisj :
      rMain.DisjointWires
    rScr) : QRegister 23 N :=
  let rCtrl16 := rMain.compose (rPolyCtrl16InCat wOuter wInner2 wNegIn)
  let rCtrl1 := rScr.compose (QRegister.block 0 1 (by omega))
  let rBorrow6 := rScr.compose (QRegister.block 1 6 (by omega))
  have hC1C16 : rCtrl1.DisjointWires rCtrl16 := QRegister.disjoint_iff.mpr fun _ _ ↦ (hdisj.ne _
    _).symm
  let rRouter17 := rCtrl1.concat rCtrl16 hC1C16
  have hC17B6 : rRouter17.DisjointWires rBorrow6 := by
    refine QRegister.disjointWires_concat_left hC1C16 ?_ (QRegister.disjoint_iff.mpr fun _ _ ↦
      hdisj.ne _ _)
    rw [QRegister.disjoint_iff]; intro _ _ heq
    have hv := congrArg Fin.val (rScr.wires.injective heq); simp at hv; omega
  rRouter17.concat rBorrow6 hC17B6
theorem lowBitRouter23_apply {N kInner : ℕ} (hk6 : 6 ≤ kInner) (wOuter wInner2 : ℕ) (wNegIn :
    Wire wInner2)
    (rMain : QRegister (nUB wOuter wInner2 + 11) N) (rScr : QRegister (1 + kInner) N) (hdisj :
    rMain.DisjointWires rScr) (u : Wire 23) :
      lowBitRouter23 hk6 wOuter wInner2 wNegIn rMain rScr hdisj u
    = if h1 : u.val = 0 then rScr ⟨0, by omega⟩ else if h17 : u.val < 17 then
        (rMain.compose (rPolyCtrl16InCat wOuter wInner2 wNegIn)) ⟨u.val - 1, by omega⟩
      else rScr ⟨1 + (u.val - 17), by omega⟩ := by
  dsimp only [lowBitRouter23]
  by_cases h1 : u.val = 0
  · rw [dite_eq_left h1, show u = Fin.castAdd 6 (Fin.castAdd 16 (0 : Fin 1)) by ext; simp [h1],
      QRegister.concat_apply_left, QRegister.concat_apply_left]; rfl
  · rw [dite_eq_right h1]; by_cases h17 : u.val < 17
    · rw [dite_eq_left h17]
      have hu : u = Fin.castAdd 6 (Fin.natAdd 1 (⟨u.val - 1, by omega⟩ : Fin 16)) := by
        ext; simp; omega
      conv_lhs => rw [hu, QRegister.concat_apply_left, QRegister.concat_apply_right]
    · rw [dite_eq_right h17]
      have hu : u = Fin.natAdd (1 + 16) (⟨u.val - 17, by omega⟩ : Fin 6) := by ext; simp; omega
      (conv_lhs => rw [hu, QRegister.concat_apply_right]); rfl
/-- `Core145Layout kInner N` built from `rMain` and `rScr : QRegister (1 + kInner) N`. -/
def lowBitCoreLayout {N kInner : ℕ} (wOuter wInner2 : ℕ) (wNegIn : Wire wInner2) (rMain :
    QRegister (nUB wOuter
    wInner2 + 11) N) (rScr : QRegister (1 + kInner) N) (hdisj : rMain.DisjointWires rScr) :
    Core145Layout kInner N :=
  let rCtrl16 := rMain.compose (rPolyCtrl16InCat wOuter wInner2 wNegIn)
  let rSysCat := rMain.compose (rSysCatUB wOuter wInner2 11)
  let rSpin := rSysCat.compose (QRegister.block 0 58 (by decide))
  let rCat11 := rSysCat.compose (QRegister.block (2 * 58) 11 (by decide))
  let rCtrl1 := rScr.compose (QRegister.block 0 1 (by omega))
  let rInner := rScr.compose (QRegister.block 1 kInner (by omega))
  have hC1C16 : rCtrl1.DisjointWires rCtrl16 := QRegister.disjoint_iff.mpr fun _ _ ↦ (hdisj.ne _
    _).symm
  let rRouter17 := rCtrl1.concat rCtrl16 hC1C16
  let rCtrl10 := rRouter17.compose routed10Sub17
  have hSysRt : rSysCat.DisjointWires rRouter17 := by
    refine QRegister.disjoint_comm.mp (QRegister.disjointWires_concat_left hC1C16
      (QRegister.disjoint_iff.mpr fun _ _ ↦ (hdisj.ne _ _).symm) ?_)
    exact QRegister.disjoint_iff.mpr fun _ _ heq ↦
      (disjoint_rAllInCat_rSysCatUB wOuter wInner2 11).ne _ _
      (rMain.wires.injective heq)
  have hsc : rSpin.DisjointWires rCtrl10 := QRegister.disjoint_iff.mpr fun _ _ ↦ hSysRt.ne _ _
  have hac : (rSpin.concat rCtrl10 hsc).DisjointWires rCat11 := by
    refine QRegister.disjointWires_concat_left hsc ?_ (QRegister.disjoint_iff.mpr fun _ _ heq ↦
      hSysRt.ne _ _ heq.symm)
    rw [QRegister.disjoint_iff]; intro _ _ heq
    have hv := congrArg Fin.val (rSysCat.wires.injective heq); simp at hv; omega
  have hRtIn : rRouter17.DisjointWires rInner := by
    refine QRegister.disjointWires_concat_left hC1C16 ?_ (QRegister.disjoint_iff.mpr fun _ _ ↦
      hdisj.ne _ _)
    rw [QRegister.disjoint_iff]; intro _ _ heq
    have hv := congrArg Fin.val (rScr.wires.injective heq); simp at hv; omega
  have hInner : ((rSpin.concat rCtrl10 hsc).concat rCat11 hac).DisjointWires rInner :=
    QRegister.disjointWires_concat_left hac (QRegister.disjointWires_concat_left hsc
    (QRegister.disjoint_iff.mpr fun _ _ ↦ hdisj.ne _ _) (QRegister.disjoint_iff.mpr fun _ _ ↦
    hRtIn.ne _ _)) (QRegister.disjoint_iff.mpr fun _ _ ↦ hdisj.ne _ _)
  { rFull := (((rSpin.concat rCtrl10 hsc).concat rCat11 hac).concat rInner hInner) }
theorem lowBitCoreLayout_wires {N kInner : ℕ} (hk6 : 6 ≤ kInner) (wOuter wInner2 : ℕ) (wNegIn :
    Wire wInner2)
    (rMain : QRegister (nUB wOuter wInner2 + 11) N) (rScr : QRegister (1 + kInner) N) (hdisj :
    rMain.DisjointWires rScr) :
    let L := lowBitCoreLayout wOuter wInner2 wNegIn rMain rScr hdisj
    let rSysCat := rMain.compose (rSysCatUB wOuter wInner2 11)
    L.rSpin = rSysCat.compose (QRegister.block 0 58 (by decide)) ∧
    L.rCat11 = rSysCat.compose (QRegister.block (2 * 58) 11 (by decide)) ∧
    L.rInner = rScr.compose (QRegister.block 1 kInner (by omega)) ∧
    (∀ u : Fin 10,
      L.rCtrl10 u = lowBitRouter23 hk6 wOuter wInner2 wNegIn rMain rScr hdisj (routed10Wire23
      u)) := by
  refine ⟨CoherentAlias.qreg_ext fun i ↦ ?_, CoherentAlias.qreg_ext fun j ↦ ?_,
    CoherentAlias.qreg_ext fun idx ↦ ?_, fun u ↦ ?_⟩
  · dsimp only [Core145Layout.rSpin, lowBitCoreLayout]
    rw [QRegister.compose_apply, show QRegister.block 0 58 (by omega : 0 + 58 ≤ 79 + kInner) i =
      Fin.castAdd kInner (Fin.castAdd 11 (Fin.castAdd 10 i)) by ext; simp,
      QRegister.concat_apply_left, QRegister.concat_apply_left, QRegister.concat_apply_left]
  · dsimp only [Core145Layout.rCat11, lowBitCoreLayout]
    rw [QRegister.compose_apply, show QRegister.block 68 11 (by omega : 68 + 11 ≤ 79 + kInner) j =
      Fin.castAdd kInner (Fin.natAdd (58 + 10) j) by ext; simp,
      QRegister.concat_apply_left, QRegister.concat_apply_right]
  · dsimp only [Core145Layout.rInner, lowBitCoreLayout]
    rw [QRegister.compose_apply, show QRegister.block 79 kInner
      (by omega : 79 + kInner ≤ 79 + kInner) idx = Fin.natAdd 79 idx by ext; simp,
      QRegister.concat_apply_right]
  · dsimp only [Core145Layout.rCtrl10, lowBitCoreLayout]
    rw [QRegister.compose_apply, show QRegister.block 58 10 (by omega : 58 + 10 ≤ 79 + kInner) u =
      Fin.castAdd kInner (Fin.castAdd 11 (Fin.natAdd 58 u)) by ext; simp,
      QRegister.concat_apply_left, QRegister.concat_apply_left, QRegister.concat_apply_right,
      lowBitRouter23_apply]
    let w : Fin (1 + 16) := routed10Wire17 u
    have hwv : (routed10Wire23 u).val = w.val := rfl
    by_cases hw0 : w.val = 0
    · rw [dite_eq_left (hwv.trans hw0), QRegister.compose_apply,
        show routed10Sub17 u = Fin.castAdd 16 (0 : Fin 1) from Fin.ext hw0,
        QRegister.concat_apply_left]; rfl
    · rw [dite_eq_right (hwv ▸ hw0), dite_eq_left (hwv ▸ w.isLt), QRegister.compose_apply,
        show routed10Sub17 u = Fin.natAdd 1 ⟨w.val - 1, by omega⟩ from
          Fin.ext (by change w.val = 1 + (w.val - 1); omega),
        QRegister.concat_apply_right]; rfl
theorem lowBit_disj_sysCat_router23 {N kInner : ℕ} (hk6 : 6 ≤ kInner) (wOuter wInner2 : ℕ) (wNegIn :
    Wire
    wInner2) (rMain : QRegister (nUB wOuter wInner2 + 11) N) (rScr : QRegister (1 +
      kInner) N) (hdisj :
    rMain.DisjointWires rScr) : (rMain.compose (rSysCatUB wOuter wInner2 11)).DisjointWires
    (lowBitRouter23 hk6 wOuter wInner2 wNegIn rMain rScr hdisj) := by
  rw [QRegister.disjoint_iff]; intro k u heq; rw [lowBitRouter23_apply] at heq; split_ifs at heq
  · exact hdisj.ne _ _ heq
  · exact (disjoint_rAllInCat_rSysCatUB wOuter wInner2 11).ne _ _ (rMain.wires.injective heq).symm
  · exact hdisj.ne _ _ heq
theorem lowBit_inner6_not_mem_router23 {N kInner : ℕ} (hk6 : 6 ≤ kInner) (wOuter wInner2 :
    ℕ) (wNegIn :
    Wire wInner2) (rMain : QRegister (nUB wOuter wInner2 + 11) N) (rScr : QRegister (1 +
      kInner) N) (hdisj :
    rMain.DisjointWires rScr) (idx : Fin (kInner - 6)) :
      (lowBitCoreLayout wOuter wInner2 wNegIn rMain
    rScr hdisj).rInner (innerAfter6Idx idx) ∉ Set.range
      (lowBitRouter23 hk6 wOuter wInner2 wNegIn rMain
    rScr hdisj).wires := by
  rintro ⟨u, hu⟩
  rw [(lowBitCoreLayout_wires hk6 wOuter wInner2 wNegIn rMain rScr hdisj).2.2.1,
    QRegister.compose_apply,
    lowBitRouter23_apply] at hu
  split_ifs at hu
  · have hv := congrArg Fin.val (rScr.wires.injective hu)
    simp [innerAfter6Idx] at hv; omega
  · exact hdisj.ne _ _ hu
  · have hv := congrArg Fin.val (rScr.wires.injective hu)
    simp [innerAfter6Idx] at hv; omega
theorem disj_singleton0_block1 (m : ℕ) : (QRegister.singleton (0 : Wire (1 + m))).DisjointWires
    (QRegister.block 1 m (by omega) ) := by
  rw [QRegister.disjoint_iff]; intro a c heq; fin_cases a
  have hv : (0 : ℕ) = 1 + c.val := congrArg Fin.val heq; omega
theorem cswap58_mul_ketPredProj_eq {N : ℕ} (wSi : Wire N) (rSys116 : QRegister (2 * 58) N) (hSys2
    : (QRegister.singleton wSi).DisjointWires rSys116) (S : BitAssignment N → Prop) (b : Bool) (hSi
    : ∀ δ : BitAssignment N, S δ → δ wSi = (if b then 1 else 0)) : (((QRegister.singleton
    wSi).concat rSys116 hSys2).embedUnitary (muxUnitary (QRegister.singleton 0) (QRegister.block 1
    (2 * 58) (by omega) ) (disj_singleton0_block1 (2 * 58)) (fun σ ↦ if σ = 0 then 1 else
    permutationUnitary (spinSwapEquiv 58)))).1 * ketPredProj S = rSys116.embedMatrix (if b then
    permutationUnitary (spinSwapEquiv 58) else 1).1 * ketPredProj S := by
  classical
  let rSwap := (QRegister.singleton wSi).concat rSys116 hSys2
  have hTgt : rSwap.compose (QRegister.block 1 (2 * 58) (by omega)) = rSys116 :=
    CoherentAlias.qreg_ext fun i ↦ by
      rw [QRegister.compose_apply, show QRegister.block 1 (2 * 58)
        (by omega : 1 + 2 * 58 ≤ 1 + 2 * 58) i = Fin.natAdd 1 i by ext; simp,
        QRegister.concat_apply_right]
  have hCtrl : rSwap.compose (QRegister.singleton 0) = QRegister.singleton wSi :=
    CoherentAlias.qreg_ext fun i ↦ by fin_cases i; rfl
  apply OneHotSimulates.matrix_ext_ket; intro δ
  rw [← mulVec_mulVec, ← mulVec_mulVec, ketPredProj_mulVec_ket]
  by_cases hS : S δ
  · simp only [hS, ↓reduceIte]; rw [embedUnitary_muxUnitary]
    let σ₀ : Fin (2 ^ 1) := if b then 1 else 0
    have hproj (q : Fin (2 ^ N)) (hq : (rSwap.compose (QRegister.singleton 0)).extractIndex q ≠ σ₀)
      : OneHotSimulates.ket δ q = 0 := by
      simp only [OneHotSimulates.ket, basisState]; rw [Pi.single_eq_of_ne]; rintro rfl
      refine hq ?_; rw [hCtrl]; apply (basisBits 1).injective; funext j; fin_cases j
      change basisBits 1 _ 0 = basisBits 1 σ₀ 0
      rw [QRegister.basisBits_extractIndex, QRegister.singleton_apply, basisBits_symm, hSi δ hS]
      dsimp only [σ₀]; cases b <;> decide
    change (muxUnitary _ _ _ _).1 *ᵥ OneHotSimulates.ket δ = _
    rw [muxUnitary_mulVec_of_proj _ _ _ _ σ₀ _ hproj, hTgt]; dsimp only [σ₀]; cases b <;> simp
  · simp [hS]
theorem muxCtrl10_mul_ketPredProj_eq {N : ℕ} (rSC : QRegister (58 + 11) N) (rCtrl10 : QRegister 10
    N) (htc : rSC.DisjointWires rCtrl10) (WPhased : Fin (2 ^ 10) → Unitary (2 ^ (58 + 11))) (S :
    BitAssignment N → Prop) (f10 : Fin 10 → Bool) (hCtrl : ∀ δ : BitAssignment N, S δ → ∀ u : Fin
    10, δ (rCtrl10 u) = if f10 u then 1 else 0) : ((rSC.concat rCtrl10 htc).embedUnitary
    (UnsignedGivens.muxCtrlUnitary WPhased)).1 * ketPredProj S =
      rSC.embedMatrix (WPhased (finOfBits 10
    f10)).1 * ketPredProj S := by
  classical
  apply OneHotSimulates.matrix_ext_ket; intro δ
  rw [← mulVec_mulVec, ← mulVec_mulVec, ketPredProj_mulVec_ket]
  by_cases hS : S δ
  · simp only [hS, ↓reduceIte]; rw [UnsignedGivens.embedUnitary_muxCtrlUnitary_mulVec_ket]
    have hidx : UnsignedGivens.localIdx rCtrl10 δ = finOfBits 10 f10 := by
      change (basisBits 10).symm (fun u ↦ δ (rCtrl10 u)) = finOfBits 10 f10
      dsimp only [finOfBits]; congr 1; funext u; exact hCtrl δ hS u
    rw [hidx]; rfl
  · simp [hS]
theorem commutesWithWire_cswap58 {N : ℕ} (wSi : Wire N) (rSys116 : QRegister (2 * 58) N) (hSys2 :
    (QRegister.singleton wSi).DisjointWires rSys116) (q : Wire N) (hq : q ∉ Set.range
    rSys116.wires) : OneHotSimulates.CommutesWithWire q (((QRegister.singleton wSi).concat rSys116
    hSys2).embedUnitary (muxUnitary (QRegister.singleton 0) (QRegister.block 1 (2 * 58) (by omega)
    ) (disj_singleton0_block1 (2 * 58)) (fun σ ↦ if σ = 0 then 1 else permutationUnitary
    (spinSwapEquiv 58)))).1 := by
  let rSwap := (QRegister.singleton wSi).concat rSys116 hSys2
  have hTgt : rSwap.compose (QRegister.block 1 (2 * 58) (by omega)) = rSys116 :=
    CoherentAlias.qreg_ext fun i ↦ by
      rw [QRegister.compose_apply, show QRegister.block 1 (2 * 58)
        (by omega : 1 + 2 * 58 ≤ 1 + 2 * 58) i = Fin.natAdd 1 i by ext; simp,
        QRegister.concat_apply_right]
  have hd : rSys116.DisjointWires (QRegister.singleton q) :=
    QRegister.disjoint_iff.mpr fun i j hij ↦ by fin_cases j; exact hq ⟨i, hij⟩
  intro o; rw [embedUnitary_muxUnitary]; dsimp only [muxUnitary]
  rw [hTgt, Finset.sum_mul, Finset.mul_sum]; refine Finset.sum_congr rfl fun σ _ ↦ ?_
  have hc1 := (IsDiagProj.basisOutcomeProjector (rSwap.compose (QRegister.singleton 0)) σ).comm
    (IsDiagProj.basisOutcomeProjector (QRegister.singleton q) o)
  have hc2 := rSys116.embedMatrix_comm_basisOutcomeProjector_of_disjoint (QRegister.singleton q) hd
    (if σ = 0 then (1 : Unitary _) else permutationUnitary (spinSwapEquiv 58)).1 o
  rw [mul_assoc, hc2, ← mul_assoc, hc1, mul_assoc]
@[simp] theorem dyn_count_seq {Var : Type} {n k : ℕ} (p₁ p₂ : DynamicCircuit Var n) (g :
    PrimitiveGate k) : (DynamicCircuit.seq p₁ p₂).count g = p₁.count g + p₂.count g := rfl
@[simp] theorem dyn_count_circuit {Var : Type} {n k : ℕ} (c : Circuit n) (g : PrimitiveGate k) :
    (DynamicCircuit.circuit (Var := Var) c).count g = c.count g := rfl
/-- `117`-wire `[si : 1 | rSys116 : 116]` swap register inside `rMain`. -/
def rSwap117LowBit {N : ℕ} (wOuter wInner2 : ℕ) (wNegIn : Wire wInner2) (rMain :
    QRegister (nUB wOuter wInner2 + 11)
    N) : QRegister (1 + 2 * 58) N :=
  let rCtrl16 := rMain.compose (rPolyCtrl16InCat wOuter wInner2 wNegIn)
  let rSys116 := (rMain.compose (rSysCatUB wOuter wInner2 11)).compose (QRegister.block 0 (2 * 58)
    (by decide) )
  (QRegister.singleton (rCtrl16 14)).concat rSys116 (QRegister.disjoint_iff.mpr fun i _ heq ↦ by
      fin_cases i
      exact (disjoint_rAllInCat_rSysCatUB wOuter wInner2 11).ne _ _ (rMain.wires.injective heq))
/-- Reusable `State24` conjugation wrapper around `DiagProjSimulates.routerSteps`. -/
theorem diagProjSimulates_liftRouterStepsN {k m N : ℕ} (hk : k ≤ 24)
    (rRt : QRegister k N) (rSys : QRegister m N) (hSysRt : rSys.DisjointWires rRt)
    (steps : List (RouterStep k))
    (PBody : Operator (2 ^ N)) (UBody UTgt : Unitary (2 ^ N)) (dBody : DynamicCircuit Unit N)
    (hBody : DiagProjSimulates PBody UBody dBody)
    (hCommBody : ∀ q : Wire N,
      q ∉ Set.range rSys.wires → OneHotSimulates.CommutesWithWire q UBody.1)
    (SIn : BitAssignment N → Prop)
    (stIn stOut : BitAssignment N → State24) (B : BitAssignment N → Unitary (2 ^ m))
    (hStInEq : ∀ β (l : Fin (2 ^ m)), SIn β → stIn (writeRegBitsBound50 β rSys (basisBits m l)) =
      stIn β)
    (hStOutEq : ∀ β (l : Fin (2 ^ m)), SIn β → stOut (writeRegBitsBound50 β rSys (basisBits m l)) =
      stOut β) (hInit : ∀ β, SIn β →
      ∀ u : Wire k, β (rRt u) = if (stIn β).get24 ⟨u.val, by omega⟩ then 1 else 0)
    (hRun : ∀ β, SIn β → runSteps24 hk steps (stIn β) = some (stOut β))
    (hFix : ∀ β, SIn β → PBody.mulVec (OneHotSimulates.ket (routerStepsAssign (liftRouterStepsN rRt
      steps) β)) = OneHotSimulates.ket (routerStepsAssign (liftRouterStepsN rRt steps) β))
    (hBodyAct : ∀ β,
      SIn β → UBody.1.mulVec (OneHotSimulates.ket (routerStepsAssign (liftRouterStepsN
      rRt steps) β)) = (rSys.embedMatrix (B β).1).mulVec (OneHotSimulates.ket (routerStepsAssign
      (liftRouterStepsN rRt steps) β)))
    (hTgtAct : ∀ β, SIn β → UTgt.1.mulVec (OneHotSimulates.ket β) =
      (rSys.embedMatrix (B β).1).mulVec
      (OneHotSimulates.ket β)) (hCommTgt : UTgt.1 * ketPredProj SIn = ketPredProj SIn * UTgt.1) :
    DiagProjSimulates (ketPredProj SIn) UTgt (routerStepsProg () (liftRouterStepsN rRt steps)
      dBody) := by
  classical
  let lS := liftRouterStepsN rRt steps
  have hStepsW : ∀ s ∈ lS, s.TouchesIn (fun q ↦ q ∉ Set.range rSys.wires) :=
    touchesIn_liftRouterStepsN rRt _ (fun u ⟨i, hi⟩ ↦ hSysRt.ne i u hi) steps
  have hOk : ∀ β, SIn β → routerStepsOk lS β := fun β hS ↦ (liftRouterStepsN_spec24 hk rRt steps _
    _ (hRun β hS) β (hInit β hS)).1
  have hEqU : ((routerStepsCircuit lS).eval⁻¹ * UBody * (routerStepsCircuit lS).eval).1 *
    ketPredProj SIn = UTgt.1 * ketPredProj SIn := by
    let Dc := (routerStepsCircuit lS).eval
    apply OneHotSimulates.matrix_ext_ket; intro β
    rw [← mulVec_mulVec, ← mulVec_mulVec, ketPredProj_mulVec_ket]
    by_cases hS : SIn β
    · simp only [hS, ↓reduceIte]
      let βRt := routerStepsAssign lS β
      obtain ⟨_, hRtW, hRtOut⟩ := liftRouterStepsN_spec24 hk rRt steps _ _ (hRun β hS) β (hInit β
        hS)
      have hket : (OneHotSimulates.ket : BitAssignment N → Fin (2 ^ N) → ℂ) = CoherentAlias.ket :=
        rfl
      have hSysIdx : (fun i ↦ βRt (rSys i)) = (fun i ↦ β (rSys i)) := funext fun i ↦ hRtOut (rSys
        i) (fun ⟨u, hu⟩ ↦ hSysRt.ne i u hu.symm)
      have hDcInv (l : Fin (2 ^ m)) : (Dc⁻¹).1.mulVec (CoherentAlias.ket (writeRegBitsBound50 βRt
        rSys (basisBits m l))) =
            CoherentAlias.ket (writeRegBitsBound50 β rSys (basisBits m l)) := by
        let γL := writeRegBitsBound50 β rSys (basisBits m l)
        have hγInit (u : Wire k) :
            γL (rRt u) = if (stIn γL).get24 ⟨u.val, by omega⟩ then 1 else 0 := by
          rw [hStInEq β l hS]
          exact (writeRegBitsBound50_apply_of_not_mem β rSys _ (rRt u) (fun ⟨i, hi⟩ ↦ hSysRt.ne i u
            hi)).trans (hInit β hS u)
        have hγRun : runSteps24 hk steps (stIn γL) = some (stOut γL) := by
          rw [hStInEq β l hS, hStOutEq β l hS]; exact hRun β hS
        obtain ⟨_, hγW, hγOut⟩ := liftRouterStepsN_spec24 hk rRt steps _ _ hγRun γL hγInit
        have hAssignEq : routerStepsAssign lS γL =
            writeRegBitsBound50 βRt rSys (basisBits m l) := by
          funext w; by_cases hwR : w ∈ Set.range rRt.wires
          · rcases hwR with ⟨u, rfl⟩
            dsimp only [βRt];
              rw [hγW u, hStOutEq β l hS, writeRegBitsBound50_apply_of_not_mem _ _ _ _
              (fun ⟨i, hi⟩ ↦ hSysRt.ne i u hi), hRtW u]
          · rw [hγOut w hwR]; by_cases hwS : w ∈ Set.range rSys.wires
            · rcases hwS with ⟨i, rfl⟩
              dsimp only [γL]; rw [writeRegBitsBound50_apply_reg, writeRegBitsBound50_apply_reg]
            · dsimp only [γL, βRt]; rw [writeRegBitsBound50_apply_of_not_mem _ _ _ _ hwS,
                writeRegBitsBound50_apply_of_not_mem _ _ _ _ hwS, hRtOut w hwR]
        calc (Dc⁻¹).1.mulVec (OneHotSimulates.ket (writeRegBitsBound50 βRt rSys (basisBits m l)))
            = (Dc⁻¹).1.mulVec (Dc.1.mulVec (OneHotSimulates.ket γL)) := by
                rw [ket_routerStepsCircuit, hAssignEq]
          _ = ((Dc⁻¹ * Dc).1).mulVec (OneHotSimulates.ket γL) := by rw [mulVec_mulVec]; rfl
          _ = OneHotSimulates.ket γL := by rw [inv_mul_cancel, Submonoid.coe_one, one_mulVec]
      change ((Dc⁻¹ * UBody * Dc).1).mulVec (OneHotSimulates.ket β) =
        UTgt.1.mulVec (OneHotSimulates.ket β)
      rw [Submonoid.coe_mul, Submonoid.coe_mul, ← mulVec_mulVec, ← mulVec_mulVec,
        ket_routerStepsCircuit, hBodyAct β hS, hTgtAct β hS, hket, embedMatrix_mulVec_ket_bound50,
        embedMatrix_mulVec_ket_bound50, hSysIdx, mulVec_sum]
      exact Finset.sum_congr rfl fun l _ ↦ by rw [mulVec_smul, hDcInv l]
    · simp [hS]
  exact DiagProjSimulates.routerSteps () _ lS hStepsW hBody hCommBody SIn hOk hFix hEqU hCommTgt
/-- Midpoint `(2 * 58 + 11)`-qubit branch unitary for a given `stB : State24`. -/
noncomputable abbrev lowBitMidBranch23 (specB : State24 → State24) (WPhased : Fin (2 ^ 10) →
    Unitary (2 ^ (58 + 11))) (stA : State24) : Unitary (2 ^ (2 * 58 + 11)) :=
  let stB := specB stA
  let sSw : Unitary (2 ^ (2 * 58 + 11)) := (QRegister.block 0 (2 * 58) (by decide) ).embedUnitary
    (if sigSelOfState24 stB then permutationUnitary (spinSwapEquiv 58) else 1)
  let uRf : Unitary (2 ^ (2 * 58 + 11)) := (spinCatSub 11).embedUnitary (WPhased (finOfBits 10
    (ctrl10OfState24 stB)))
  sSw * (uRf * sSw)
/-- Midpoint unitary on `rRouter23` + `rSysCat` realized by `selectLowBitInnerBUnitDyn`. -/
noncomputable def lowBitMidUnitary23 {N : ℕ} (specB : State24 → State24) (rRouter23 : QRegister 23
    N) (rSysCat : QRegister (2 * 58 + 11) N) (hRtSys : rRouter23.DisjointWires rSysCat) (WPhased :
    Fin (2 ^ 10) → Unitary (2 ^ (58 + 11))) : Unitary (2 ^ N) := (rRouter23.concat rSysCat
    hRtSys).embedUnitary
    (muxUnitary (QRegister.block 0 23 (by omega)) (QRegister.block 23 (2 * 58 + 11) (by omega)) (by
        rw [QRegister.disjoint_iff]; intro _ _ h
        have hv := congrArg Fin.val h; simp at hv; omega)
      fun c23 ↦ lowBitMidBranch23 specB WPhased (state24OfFin23 c23))
theorem lowBitMidUnitary23_mulVec_ket {N : ℕ} (specB : State24 → State24) (rRouter23 : QRegister 23
    N) (rSysCat : QRegister (2 * 58 + 11) N) (hRtSys : rRouter23.DisjointWires rSysCat) (WPhased :
    Fin (2 ^ 10) → Unitary (2 ^ (58 + 11))) (β : BitAssignment N) :
    let stB := specB (state24OfRouter23 rRouter23 β)
    let sSw : Unitary (2 ^ (2 * 58 + 11)) := (QRegister.block 0 (2 * 58) (by decide) ).embedUnitary
      (if sigSelOfState24 stB then permutationUnitary (spinSwapEquiv 58) else 1)
    let uRf : Unitary (2 ^ (2 * 58 + 11)) := (spinCatSub 11).embedUnitary (WPhased (finOfBits 10
      (ctrl10OfState24 stB)))
    (lowBitMidUnitary23 specB rRouter23 rSysCat hRtSys WPhased).1.mulVec (OneHotSimulates.ket β) =
      (rSysCat.embedMatrix (sSw * (uRf * sSw)).1).mulVec (OneHotSimulates.ket β) := by
  dsimp only [lowBitMidUnitary23]; rw [embedUnitary_muxUnitary]
  have hL : (rRouter23.concat rSysCat hRtSys).compose (QRegister.block 0 23 (by omega)) =
      rRouter23 := CoherentAlias.qreg_ext fun i ↦ by
    rw [QRegister.compose_apply, show QRegister.block 0 23 (by omega : 0 + 23 ≤ 23 + 127) i =
      Fin.castAdd 127 i by ext; simp, QRegister.concat_apply_left]
  have hR : (rRouter23.concat rSysCat hRtSys).compose
      (QRegister.block 23 (2 * 58 + 11) (by omega)) = rSysCat := CoherentAlias.qreg_ext fun j ↦ by
    rw [QRegister.compose_apply, show QRegister.block 23 127 (by omega : 23 + 127 ≤ 23 + 127) j =
      Fin.natAdd 23 j by ext; simp, QRegister.concat_apply_right]
  let c₀ := UnsignedGivens.localIdx rRouter23 β
  have hproj (q : Fin (2 ^ N)) (hq : ((rRouter23.concat rSysCat hRtSys).compose (QRegister.block 0
    23 (by omega) )).extractIndex q ≠ c₀) : OneHotSimulates.ket β q = 0 := by
    simp only [OneHotSimulates.ket, basisState]; rw [Pi.single_eq_of_ne]; rintro rfl
    apply hq; rw [hL]; apply (basisBits 23).injective; funext u
    rw [QRegister.basisBits_extractIndex, basisBits_symm,
      congrFun (UnsignedGivens.basisBits_symm_eq (fun i
      ↦ β (rRouter23 i))) u]
  change (muxUnitary _ _ _ _).1 *ᵥ OneHotSimulates.ket β = _
  rw [muxUnitary_mulVec_of_proj _ _ _ _ c₀ _ hproj, hR, state24OfFin23_localIdx_eq]
theorem commutesWithWire_lowBitMidUnitary23 {N : ℕ} (specB : State24 → State24) (rRouter23 :
    QRegister 23 N) (rSysCat : QRegister (2 * 58 + 11) N) (hRtSys : rRouter23.DisjointWires
    rSysCat) (WPhased : Fin (2 ^ 10) → Unitary (2 ^ (58 + 11))) (q : Wire N) (hq : q ∉ Set.range
    rSysCat.wires) : OneHotSimulates.CommutesWithWire q (lowBitMidUnitary23 specB rRouter23 rSysCat
    hRtSys WPhased).1 := by
  have hd : rSysCat.DisjointWires (QRegister.singleton q) :=
    QRegister.disjoint_iff.mpr fun i j hij ↦ by fin_cases j; exact hq ⟨i, hij⟩
  have hR : (rRouter23.concat rSysCat hRtSys).compose
      (QRegister.block 23 (2 * 58 + 11) (by omega)) = rSysCat := CoherentAlias.qreg_ext fun j ↦ by
    rw [QRegister.compose_apply, show QRegister.block 23 127 (by omega : 23 + 127 ≤ 23 + 127) j =
      Fin.natAdd 23 j by ext; simp, QRegister.concat_apply_right]
  let rC23 := (rRouter23.concat rSysCat hRtSys).compose (QRegister.block 0 23 (by omega))
  intro o; dsimp only [lowBitMidUnitary23]; rw [embedUnitary_muxUnitary]; dsimp only [muxUnitary]
  rw [hR, Finset.sum_mul, Finset.mul_sum]; refine Finset.sum_congr rfl fun c23 _ ↦ ?_
  have hc1 := (IsDiagProj.basisOutcomeProjector rC23 c23).comm (IsDiagProj.basisOutcomeProjector
    (QRegister.singleton q) o)
  have hc2 := rSysCat.embedMatrix_comm_basisOutcomeProjector_of_disjoint (QRegister.singleton q) hd
    (lowBitMidBranch23 specB WPhased (state24OfFin23 c23)).1 o
  rw [mul_assoc, hc2, ← mul_assoc, hc1, mul_assoc]
/-- Midpoint subspace predicate after `stepsA` (`rRouter23` in `Set.range specA`, `rInner[6..] =
0`). -/
def sMidLowBit {N kInner : ℕ} (hk6 : 6 ≤ kInner) (specA : (Fin 16 → Bool) →
    State24) (wOuter wInner2 : ℕ)
    (wNegIn : Wire wInner2) (rMain : QRegister (nUB wOuter wInner2 + 11) N) (rScr : QRegister (1 +
      kInner) N)
    (hdisj : rMain.DisjointWires rScr) (β : BitAssignment N) : Prop := (∃ x16 : Fin 16 → Bool,
    state24OfRouter23 (lowBitRouter23 hk6 wOuter wInner2 wNegIn rMain rScr hdisj) β = specA x16) ∧
      ∀ idx :
    Fin (kInner - 6),
      β ((lowBitCoreLayout wOuter wInner2 wNegIn rMain rScr hdisj).rInner (innerAfter6Idx
    idx)) = 0
theorem state24OfRouter23_writeReg_sysCat {N kInner : ℕ} (hk6 : 6 ≤ kInner) (wOuter wInner2 :
    ℕ) (wNegIn :
    Wire wInner2) (rMain : QRegister (nUB wOuter wInner2 + 11) N) (rScr : QRegister (1 +
      kInner) N) (hdisj :
    rMain.DisjointWires rScr) (β : BitAssignment N) (l : Fin (2 ^ (2 * 58 + 11))) :
    state24OfRouter23 (lowBitRouter23 hk6 wOuter wInner2 wNegIn rMain rScr hdisj)
      (writeRegBitsBound50 β
    (rMain.compose (rSysCatUB wOuter wInner2 11)) (basisBits _ l)) =
      state24OfRouter23 (lowBitRouter23 hk6
    wOuter wInner2 wNegIn rMain rScr hdisj) β := by
  have hSysRt := lowBit_disj_sysCat_router23 hk6 wOuter wInner2 wNegIn rMain rScr hdisj
  apply State24.ext24; intro i; rw [get24_state24OfRouter23, get24_state24OfRouter23]
  by_cases h : i.val < 23
  · rw [dite_eq_left h, dite_eq_left h, writeRegBitsBound50_apply_of_not_mem _ _ _ _ (fun ⟨k, hk⟩ ↦
      hSysRt.ne k _ hk)]
  · rw [dite_eq_right h, dite_eq_right h]
theorem negOneUnitary_mul_self_inv {k : ℕ} {U : Unitary (2 ^ k)} (hU : U⁻¹ = U) : (negOneUnitary k
    * U)⁻¹ = negOneUnitary k * U := by
  apply Subtype.ext
  change ((negOneUnitary k).1 * U.1)ᴴ = (negOneUnitary k).1 * U.1
  have hUval : U.1ᴴ = U.1 := congrArg Subtype.val hU
  rw [Matrix.conjTranspose_mul, hUval, negOneUnitary_val, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_one, star_neg, star_one, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
    Matrix.one_mul]
/-! ## Section 3: `π145` `SiZero` Stage-2 Tables & `StageA` Core (`159` Inner Wires) -/

/-- Dyad active-flip mask on `Fin 145` (`false` on the `14` free dyads, `true` elsewhere). -/
def actFlip145 (g : Fin 145) : Bool := !decide (g.val = 15 ∨ g.val = 30 ∨ g.val = 31 ∨ g.val = 47
    ∨ g.val = 62 ∨ g.val = 63 ∨ g.val = 79 ∨ g.val = 94 ∨ g.val = 95 ∨ g.val = 111 ∨ g.val = 126 ∨
    g.val = 127 ∨ g.val = 143 ∨ g.val = 144)
/-- Pass-1 dyad sign mask (`false` iff the dyad's active `1B` orbitals lie in `< 30`). -/
def negMaskPi145Fwd61 (g : Fin 145) : Bool := !decide (g.val = 15 ∨ g.val = 31 ∨ g.val = 62 ∨
    g.val = 63 ∨ g.val = 94 ∨ g.val = 95 ∨ g.val = 111 ∨ g.val = 143)
/-- Pass-2 dyad sign mask (`false` iff the dyad's active `1B` orbitals lie in `< 30`). -/
def negMaskPi145Bwd61 (g : Fin 145) : Bool := !decide (g.val = 15 ∨ g.val = 31 ∨ g.val = 47 ∨
    g.val = 94 ∨ g.val = 126 ∨ g.val = 143 ∨ g.val = 144)
/-- Pass-indexed dyad sign mask (`oddPass = false` for Pass 1, `true` for Pass 2). -/
def negMaskPi14561 (oddPass : Bool) : Fin 145 → Bool := if oddPass then negMaskPi145Bwd61 else
    negMaskPi145Fwd61
/-- Constant `Fin 319` orbital literal constructor. -/
abbrev f319 (n : ℕ) (h : n < 319 := by decide) : Fin 319 := ⟨n, h⟩
/-- Pass-1 `(Fin 145, Bool) → Fin 319` orbital lookup table for `π145` `SiZero`. -/
def orbitalOfPi145Fwd61 (g : Fin 145) (s : Bool) : Fin 319 := if g.val = 15 then (if s then f319
    1 else f319 21) else if g.val = 30 then (if s then f319 34 else f319 31) else if g.val = 31
    then (if s then f319 0 else f319 14) else if g.val = 47 then (if s then f319 40 else f319 47)
    else if g.val = 62 then (if s then f319 15 else f319 23) else if g.val = 63 then (if s then
    f319 29 else f319 13) else if g.val = 79 then (if s then f319 46 else f319 48) else if g.val =
    94 then (if s then f319 9 else f319 16) else if g.val = 95 then (if s then f319 26 else f319
    27) else if g.val = 111 then (if s then f319 3 else f319 5) else if g.val = 126 then (if s then
    f319 32 else f319 57) else if g.val = 127 then (if s then f319 49 else f319 52) else if h142 :
    g.val = 142 ∧ s = true then f319 55 else if h143 : g.val = 143 then (if s then f319 7 else f319
    6) else if h144 : g.val = 144 then (if s then f319 41 else f319 45) else if hc : (g.val = 14 ∨
    g.val = 46 ∨ g.val = 78 ∨ g.val = 110) ∧ s = true then
    ⟨58 + 29 * (g.val / 16 + 1) + 28, by have := g.isLt; omega⟩
  else ⟨58 + 29 * (g.val / 16) + 2 * (g.val % 16) + (if s then 1 else 0),
    by have := g.isLt; cases s <;> simp_all <;> omega⟩
/-- Pass-2 `(Fin 145, Bool) → Fin 319` orbital lookup table for `π145` `SiZero`. -/
def orbitalOfPi145Bwd61 (g : Fin 145) (s : Bool) : Fin 319 := if g.val = 15 then (if s then f319
    28 else f319 12) else if g.val = 30 then (if s then f319 36 else f319 37) else if g.val = 31
    then (if s then f319 10 else f319 22) else if g.val = 47 then (if s then f319 11 else f319 18)
    else if g.val = 62 then (if s then f319 56 else f319 38) else if g.val = 63 then (if s then
    f319 35 else f319 53) else if g.val = 79 then (if s then f319 42 else f319 44) else if g.val =
    94 then (if s then f319 25 else f319 17) else if g.val = 95 then (if s then f319 30 else f319
    33) else if g.val = 111 then (if s then f319 54 else f319 39) else if g.val = 126 then (if s
    then f319 20 else f319 19) else if g.val = 127 then (if s then f319 43 else f319 51) else if
    h142 : g.val = 142 ∧ s = true then f319 50 else if h143 : g.val = 143 then (if s then f319 4
    else f319 24) else if h144 : g.val = 144 then (if s then f319 2 else f319 8) else if hc :
    (g.val = 14 ∨ g.val = 46 ∨ g.val = 78 ∨ g.val = 110) ∧ s = true then
    ⟨58 + 29 * (g.val / 16 + 1) + 28, by have := g.isLt; omega⟩
  else ⟨58 + 29 * (g.val / 16) + 2 * (g.val % 16) + (if s then 1 else 0),
    by have := g.isLt; cases s <;> simp_all <;> omega⟩
/-- Pass-indexed `(Fin 145, Bool) → Fin 319` orbital table (`false` Pass 1, `true` Pass 2). -/
def orbitalOfPi14561 (oddPass : Bool) : Fin 145 → Bool → Fin 319 := if oddPass then
    orbitalOfPi145Bwd61 else orbitalOfPi145Fwd61
end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.LowBitPi145Select

end

/-!
# Low-Bit `π145` `SiZero` Router Proofs, Shared Pure Unitaries & Core-Polymorphic Bridges

Proves the `61`-AND (`14 + 47`, `244 T`) `23`-wire `π145` `SiZero` Stage-1 router contracts,
shared pass-indexed pure unitaries, `SelectCatPi145OneBodyMidCoreComm`, and core-polymorphic
`CleanRealizesSet` and `WalkTopBridge` gate-count bridges.

## References
- D. W. Berry, C. Gidney, M. Motta, J. R. McClean, and R. Babbush, "Qubitization of Arbitrary
  Basis Quantum Chemistry Leveraging Sparsity and Low Rank Factorization," *Quantum* **3**, 208
  (2019), DOI: `10.22331/q-2019-12-02-208`.
- J. Lee, D. W. Berry, C. Gidney, W. J. Huggins, J. R. McClean, N. Wiebe, and R. Babbush,
  "Even More Efficient Quantum Computations of Chemistry Through Tensor Hypercontraction,"
  *PRX Quantum* **2**, 030305 (2021), DOI: `10.1103/PRXQuantum.2.030305`.
- C. Gidney, "Halving the cost of quantum addition," *Quantum* **2**, 74 (2018),
  DOI: `10.22331/q-2018-06-18-74`.
-/

@[expose] public section
namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.LowBitPi145Select
open QuantumComputation.Specs QuantumComputation.Specs.P450
open Operator QProg Matrix HermitianMat Real CoherentAlias
open QuantumComputation.Specs Solution QuantumComputation.Specs.P450 Solution
open Solution.CircuitModular Solution.GivensOps
open Solution.BlockEncodingCore Solution.BlockEncodingCircuit
open Solution.SelectSwapQROM Solution.GivensCascade
open Solution.SelectRouter10 Solution.TopIntegrationBridge
open Solution.Lac2Fused184Select Solution.Lac2Fused184SelectWrap Solution.Router10Lac2Select
open Solution.Phase2MidSandwich Solution.PolymorphicFused184Select Solution.Lac2ZeroPar183Select
open Solution.CompactFoldedSelect Solution.ReordOuter13Bridge Solution.CompactStepFast176Select
open Solution.StepEncK Solution.StepDecK Solution.CompactStepFast175Core
open Solution.CompactOuter9Bound50Core Solution.CompactOuter9Bound50Select
open Solution.MobiusOptSubcube163Walk
open Solution.CompactTuned162StepWalk Solution.CompactTuned162StepZeroCmp20
open Solution.CompactZeroCmp20OuterParam Solution.CompactStepZeroCmp20OuterParam
open Solution.Balanced160Select Solution.Pi145SOSPermBridge Solution.OneHotSimulates
open WalkQPEBridge WalkQPEBridgeXMeas WalkQPEFlexBridge Solution.CleanDyn
open scoped Matrix BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator Circuit.Notation
local instance (priority := 1000000) instNeZeroTwoPowRouterA (k : ℕ) : NeZero (2 ^ k) :=
    ⟨(Nat.two_pow_pos k).ne'⟩
/-! ## Section 1: `61`-AND `23`-Wire `π145` `SiZero` Router & `State24` Proofs -/

/-- Outer-index predicate on `xo' : Fin (2 ^ 8)` selecting the `29` `1B` sectors in Pass 1. -/
def inPass1Pi145Xo (xo' : Fin (2 ^ 8)) : Bool := decide (xo'.val = 127 ∨ (128 ≤ xo'.val ∧ xo'.val <
    184 ∧ xo'.val % 2 = 0))
/-- Force `b : Bool` to WHNF (`true` or `false`) once before invoking `k`. -/
def strictBool {α : Type} (b : Bool) (k : Bool → α) : α :=
  match b with | true => k true | false => k false
@[simp] theorem strictBool_eq {α : Type} (b : Bool) (k : Bool → α) :
    strictBool b k = k b := by cases b <;> rfl
/-- Force all `8` bits of `q : State8` to literal `Bool` constructors before invoking `k`. -/
def strictState8 {α : Type} (q : State8) (k : State8 → α) : α := strictBool q.b0 fun c0 ↦
    strictBool q.b1 fun c1 ↦ strictBool q.b2 fun c2 ↦ strictBool q.b3 fun c3 ↦ strictBool q.b4 fun
    c4 ↦ strictBool q.b5 fun c5 ↦ strictBool q.b6 fun c6 ↦ strictBool q.b7 fun c7 ↦ k ⟨c0, c1, c2,
    c3, c4, c5, c6, c7⟩
@[simp] theorem strictState8_eq {α : Type} (q : State8) (k : State8 → α) :
    strictState8 q k = k q := by rcases q with ⟨_, _, _, _, _, _, _, _⟩; simp [strictState8]
/-- Force all `24` bits of `s : State24` to literal `Bool` constructors before invoking `k`. -/
def strictState24 {α : Type} (s : State24) (k : State24 → α) : α := strictState8 s.q0 fun q0 ↦
    strictState8 s.q1 fun q1 ↦ strictState8 s.q2 fun q2 ↦ k ⟨q0, q1, q2⟩
@[simp] theorem strictState24_eq {α : Type} (s : State24) (k : State24 → α) :
    strictState24 s k = k s := by rcases s with ⟨_, _, _⟩; simp [strictState24]
/-- Proof-free bit read on `State24` for kernel evaluation. -/
def fastGet24 (s : State24) (i : ℕ) : Bool :=
  match i with
  | 0 => s.q0.b0 | 1 => s.q0.b1 | 2 => s.q0.b2 | 3 => s.q0.b3
  | 4 => s.q0.b4 | 5 => s.q0.b5 | 6 => s.q0.b6 | 7 => s.q0.b7
  | 8 => s.q1.b0 | 9 => s.q1.b1 | 10 => s.q1.b2 | 11 => s.q1.b3
  | 12 => s.q1.b4 | 13 => s.q1.b5 | 14 => s.q1.b6 | 15 => s.q1.b7
  | 16 => s.q2.b0 | 17 => s.q2.b1 | 18 => s.q2.b2 | 19 => s.q2.b3
  | 20 => s.q2.b4 | 21 => s.q2.b5 | 22 => s.q2.b6 | _ => s.q2.b7
theorem fastGet24_eq (s : State24) (i : Fin 24) : fastGet24 s i.val = s.get24 i := by
  rcases s with ⟨⟨_, _, _, _, _, _, _, _⟩, ⟨_, _, _, _, _, _, _, _⟩, ⟨_, _, _, _, _, _, _, _⟩⟩
  fin_cases i <;> rfl
/-- Strict constructor-normalizing bit update on `State8`. -/
def fastSet8 {α : Type} (q : State8) (i : ℕ) (v : Bool) (k : State8 → α) : α :=
  match q, v with
  | ⟨x0, x1, x2, x3, x4, x5, x6, x7⟩, true =>
      match i with
      | 0 => k ⟨true, x1, x2, x3, x4, x5, x6, x7⟩ | 1 => k ⟨x0, true, x2, x3, x4, x5, x6, x7⟩
      | 2 => k ⟨x0, x1, true, x3, x4, x5, x6, x7⟩ | 3 => k ⟨x0, x1, x2, true, x4, x5, x6, x7⟩
      | 4 => k ⟨x0, x1, x2, x3, true, x5, x6, x7⟩ | 5 => k ⟨x0, x1, x2, x3, x4, true, x6, x7⟩
      | 6 => k ⟨x0, x1, x2, x3, x4, x5, true, x7⟩ | _ => k ⟨x0, x1, x2, x3, x4, x5, x6, true⟩
  | ⟨x0, x1, x2, x3, x4, x5, x6, x7⟩, false =>
      match i with
      | 0 => k ⟨false, x1, x2, x3, x4, x5, x6, x7⟩ | 1 => k ⟨x0, false, x2, x3, x4, x5, x6, x7⟩
      | 2 => k ⟨x0, x1, false, x3, x4, x5, x6, x7⟩ | 3 => k ⟨x0, x1, x2, false, x4, x5, x6, x7⟩
      | 4 => k ⟨x0, x1, x2, x3, false, x5, x6, x7⟩ | 5 => k ⟨x0, x1, x2, x3, x4, false, x6, x7⟩
      | 6 => k ⟨x0, x1, x2, x3, x4, x5, false, x7⟩ | _ => k ⟨x0, x1, x2, x3, x4, x5, x6, false⟩
/-- Strict constructor-normalizing bit update on `State24`. -/
def fastSet24 {α : Type} (s : State24) (i : ℕ) (v : Bool) (k : State24 → α) : α :=
  match s with
  | ⟨q0, q1, q2⟩ =>
      match Nat.ble i 7 with
      | true => fastSet8 q0 i v fun q0' ↦ k ⟨q0', q1, q2⟩
      | false =>
          match Nat.ble i 15 with
          | true => fastSet8 q1 (i - 8) v fun q1' ↦ k ⟨q0, q1', q2⟩
          | false => fastSet8 q2 (i - 16) v fun q2' ↦ k ⟨q0, q1, q2'⟩
theorem fastSet24_eq {α : Type} (s : State24) (i : Fin 24) (v : Bool) (k : State24 → α) : fastSet24
    s i.val v k = k (s.set24 i v) := by
  rcases s with ⟨⟨_, _, _, _, _, _, _, _⟩, ⟨_, _, _, _, _, _, _, _⟩, ⟨_, _, _, _, _, _, _, _⟩⟩
  cases v <;> fin_cases i <;> rfl
/-- Execute a single `RouterStep k` strictly on `State24` without proof terms. -/
def fastStep24 {k : ℕ} (s : RouterStep k) (st : State24) (cont : State24 → Option State24) : Option
    State24 :=
  match s with
  | .x t => fastSet24 st t.val (!fastGet24 st t.val) cont
  | .cnot c t _ => fastSet24 st t.val (xor (fastGet24 st t.val) (fastGet24 st c.val)) cont
  | .andAlloc c₁ c₂ anc _ _ _ =>
      match fastGet24 st anc.val with
      | false => fastSet24 st anc.val (fastGet24 st c₁.val && fastGet24 st c₂.val) cont
      | true => none
  | .andFree c₁ c₂ anc _ _ _ =>
      match fastGet24 st anc.val == (fastGet24 st c₁.val && fastGet24 st c₂.val) with
      | true => fastSet24 st anc.val false cont
      | false => none
/-- Execute `List (RouterStep k)` strictly on `State24` for kernel `decide`. -/
def fastSteps24 {k : ℕ} : List (RouterStep k) → State24 → Option State24
  | [], st => some st
  | s :: rest, st => fastStep24 s st (fastSteps24 rest)
theorem fastSteps24_eq {k : ℕ} (hk : k ≤ 24) (steps : List (RouterStep k)) (st : State24) :
    fastSteps24 steps st = runSteps24 hk steps st := by
  induction steps generalizing st with
  | nil => rfl
  | cons s rest ih =>
      cases s with
      | x t =>
          let t' : Fin 24 := ⟨t.val, by omega⟩
          change fastSet24 st t'.val (!fastGet24 st t'.val) (fastSteps24 rest) = runSteps24 hk rest
            (st.set24 t' (!st.get24 t'))
          rw [fastGet24_eq, fastSet24_eq, ih]
      | cnot c t _ =>
          let c' : Fin 24 := ⟨c.val, by omega⟩; let t' : Fin 24 := ⟨t.val, by omega⟩
          change fastSet24 st t'.val (xor (fastGet24 st t'.val) (fastGet24 st c'.val)) (fastSteps24
            rest) = runSteps24 hk rest (st.set24 t' (xor (st.get24 t') (st.get24 c')))
          rw [fastGet24_eq, fastGet24_eq, fastSet24_eq, ih]
      | andAlloc c₁ c₂ anc _ _ _ =>
          let c₁' : Fin 24 := ⟨c₁.val, by omega⟩; let c₂' : Fin 24 := ⟨c₂.val, by omega⟩
          let a' : Fin 24 := ⟨anc.val, by omega⟩
          dsimp only [fastSteps24, fastStep24, runSteps24, runStep24]
          change (match fastGet24 st a'.val with
              | false => fastSet24 st a'.val (fastGet24 st c₁'.val && fastGet24 st c₂'.val)
                  (fastSteps24 rest)
              | true => none) = _
          rw [fastGet24_eq, fastGet24_eq, fastGet24_eq]
          cases ha : st.get24 a'
          · simp only [Bool.not_false, ↓reduceIte]; rw [fastSet24_eq, ih]
          · simp
      | andFree c₁ c₂ anc _ _ _ =>
          let c₁' : Fin 24 := ⟨c₁.val, by omega⟩; let c₂' : Fin 24 := ⟨c₂.val, by omega⟩
          let a' : Fin 24 := ⟨anc.val, by omega⟩
          dsimp only [fastSteps24, fastStep24, runSteps24, runStep24]
          change (match fastGet24 st a'.val == (fastGet24 st c₁'.val && fastGet24 st c₂'.val) with
              | true => fastSet24 st a'.val false (fastSteps24 rest)
              | false => none) = _
          rw [fastGet24_eq, fastGet24_eq, fastGet24_eq]
          cases heq : (st.get24 a' == (st.get24 c₁' && st.get24 c₂'))
          · simp
          · simp only [↓reduceIte]; rw [fastSet24_eq, ih]
/-- Strictly evaluate `steps` from `s0` and check `p` on the resulting `State24`. -/
def fastCheckRun24 {k : ℕ} (steps : List (RouterStep k)) (s0 : State24) (p : State24 → Bool) : Bool
    :=
  match fastSteps24 steps (strictState24 s0 id) with
  | none => false
  | some s1 => p s1
theorem fastCheckRun24_iff {k : ℕ} (hk : k ≤ 24) {steps : List (RouterStep k)} {s0 : State24} {p :
    State24 → Bool} (h : fastCheckRun24 steps s0 p = true) : runSteps24 hk steps s0 = some
    ((runSteps24 hk steps s0).getD s0) ∧ p ((runSteps24 hk steps s0).getD s0) = true := by
  dsimp only [fastCheckRun24] at h; rw [strictState24_eq, id_eq, fastSteps24_eq hk] at h
  cases hr : runSteps24 hk steps s0 <;> simp_all
/-- Proof-free `ctrl10OfState24` reading literal `State24` fields `[10, 8, 11..14, 5..7, 0]`. -/
def fastCtrl10 (s : State24) (u : Fin 10) : Bool :=
  match u.val with
  | 0 => s.q1.b2 | 1 => s.q1.b0 | 2 => s.q1.b3 | 3 => s.q1.b4 | 4 => s.q1.b5
  | 5 => s.q1.b6 | 6 => s.q0.b5 | 7 => s.q0.b6 | 8 => s.q0.b7 | _ => s.q0.b0
theorem fastCtrl10_eq (s : State24) : fastCtrl10 s = ctrl10OfState24 s := by
  funext u; fin_cases u <;> rfl
/-- Atomic boolean check `n < 145`. -/
def lt145Nat (n : ℕ) : Bool := decide (n < 145)
/-- Execute `steps` on `st : State24`, falling back to `st` if `none`. -/
def step24_2 (steps : List (RouterStep 23)) (st : State24) : State24 := (runSteps24 hk23Le24 steps
    st).getD st
/-- Strictly execute `steps` from `s0` once and pass the resulting `State24` to `k`. -/
def fastWithRun24 {α : Type} (steps : List (RouterStep 23)) (s0 : State24) (k : State24 → α) : α :=
    strictState24 s0 fun s0' ↦
    match fastSteps24 steps s0' with
    | none => k s0'
    | some s1 => k s1
theorem fastWithRun24_eq {α : Type} (steps : List (RouterStep 23)) (s0 : State24) (k : State24 → α)
    : fastWithRun24 steps s0 k = k (step24_2 steps s0) := by
  dsimp only [fastWithRun24, step24_2]; rw [strictState24_eq, fastSteps24_eq hk23Le24]
  cases runSteps24 hk23Le24 steps s0 <;> rfl
/-- Canonical `9`-bit projection of `st : State24` onto `[0..8]` (`w9..w23 = false`). -/
def canonA (st : State24) : State24 := ⟨st.q0, ⟨st.q1.b0, false, false, false, false, false,
    false, false⟩, zeroState8⟩
/-- Canonical `6`-bit projection onto `[3, 8, 9, 10, 14, 15]` (`w18 = false`). -/
def canonCsA2 (st : State24) : State24 := ⟨⟨false, false, false, st.q0.b3, false, false, false,
    false⟩, ⟨st.q1.b0, st.q1.b1, st.q1.b2, false, false, false, st.q1.b6, st.q1.b7⟩, zeroState8⟩
/-- Active-wire mask `[0, 5..8, 10..14, 17..22]` of the Stage-B post-CSWAP suffix. -/
def maskPost (i : Fin 24) : Bool := i.val == 0 || (5 ≤ i.val && i.val ≤ 8) || (10 ≤ i.val &&
    i.val ≤ 14) || (17 ≤ i.val && i.val ≤ 22)
/-- Post-CSWAP `10`-wire canonical input for `xo' < 126` given `sPre` and `b : Fin 32`. -/
def twoBodyPostIn (sPre : State24) (b : Fin 32) : State24 :=
  let xb := pack16 0 false b false false
  ⟨⟨sPre.q0.b0, false, false, false, false, sPre.q0.b5, sPre.q0.b6, sPre.q0.b7⟩, ⟨false, false, xb
    9, xb 10, xb 11, xb 12, xb 13, false⟩, zeroState8⟩
/-- Factored `9 × 32` two-body post-CSWAP canonical input for `(r : Fin 9, b : Fin 32)`. -/
def twoBodyRIn (r : Fin 9) (b : Fin 32) : State24 :=
  let xb := pack16 0 false b false false
  ⟨⟨r.val / 8 % 2 == 1, false, false, false, false, r.val % 2 == 1, r.val / 2 % 2 == 1, r.val / 4 %
    2 == 1⟩, ⟨false, false, xb 9, xb 10, xb 11, xb 12, xb 13, false⟩, zeroState8⟩
theorem ctrl10_mergeMaskPost (sOut st3 : State24) : ctrl10OfState24 (mergeState24 maskPost
    sOut st3) = ctrl10OfState24 sOut := by
  funext u; fin_cases u <;> rfl
theorem borrow_mergeMaskPost (sOut st3 : State24) (k : Fin 6) :
    (mergeState24 maskPost sOut st3).get24 ⟨17 + k.val, by omega⟩ =
      sOut.get24 ⟨17 + k.val, by omega⟩ := by
  fin_cases k <;> rfl
/-! ## Section 2: `SelectCatPi145OneBodyMidCoreComm`, `CleanRealizesSet` & Pure Branches -/
/-- Non-spin inner block `[b : 5 | g_in : wInner2]` inside `mMidUB wInner2`. -/
abbrev rMidCoreLocLowBit (wInner2 : ℕ) : QRegister (5 + wInner2) (mMidUB wInner2) :=
  QRegister.block 0 (5 + wInner2) (by dsimp [mMidUB]; omega)
/-- `rMidCoreLocLowBit wInner2` embedded inside `nUB wOuter wInner2 + kCat`. -/
abbrev rMidCoreInCatLowBit (wOuter wInner2 kCat : ℕ) : QRegister (5 + wInner2) (nUB wOuter wInner2 +
  kCat) :=
    ((rUBInCat wOuter wInner2 kCat).compose (rMidUB wOuter wInner2)).compose
      (rMidCoreLocLowBit wInner2)
/-- `rXoUB wOuter wInner2` embedded inside `nUB wOuter wInner2 + kCat`. -/
abbrev rXoPolyInCatLowBit (wOuter wInner2 kCat : ℕ) : QRegister 8 (nUB wOuter wInner2 + kCat) :=
  (rUBInCat wOuter
    wInner2 kCat).compose (rXoUB wOuter wInner2)
/-- `10`-wire `(xo : 8, so : 1, si : 1)` slice of `selCtrlInAnc wOuter wInner2`. -/
def selXoSoPolyInAncLowBit (wOuter wInner2 : ℕ) : QRegister 10 (mAncUB wOuter wInner2) :=
  (selCtrlInAnc wOuter
    wInner2).compose ⟨⟨fun j ↦ if hj : j.val < 9 then ⟨j.val, by omega⟩ else ⟨14, by decide⟩, by
      intro a b h; have hv := congrArg Fin.val h; have ha := a.isLt; have hb := b.isLt
      dsimp only at hv; split_ifs at hv <;> simp only at hv <;> exact Fin.ext (by omega)⟩⟩
/-- Polymorphic `(wOuter, wInner2, kCat)` `π145` (`pi145XoEquiv`) one-body `rMidCore` commutation.
-/
structure SelectCatPi145OneBodyMidCoreComm {wOuter wInner2 kCat : ℕ}
    (selectCat : Unitary (2 ^ (nUB wOuter wInner2 + kCat))) : Prop where
  proj_comm : ∀ xo' : Fin (2 ^ 8),
    (rXoPolyInCatLowBit wOuter wInner2 kCat).basisOutcomeProjector xo' *
    selectCat.1 = selectCat.1 * (rXoPolyInCatLowBit wOuter wInner2 kCat).basisOutcomeProjector xo'
  midCore_comm : ∀ (xo' : Fin (2 ^ 8)) (V : Unitary (2 ^ (5 + wInner2))),
    (pi145XoEquiv xo').val < 58 →
    ((rXoPolyInCatLowBit wOuter wInner2 kCat).basisOutcomeProjector xo' * selectCat.1) *
    (rMidCoreInCatLowBit wOuter wInner2 kCat).embedMatrix V.1 = (rMidCoreInCatLowBit wOuter wInner2
    kCat).embedMatrix V.1 * ((rXoPolyInCatLowBit wOuter wInner2 kCat).basisOutcomeProjector xo' *
    selectCat.1)
theorem selXoSoPolyInAnc_disj_midCore_lowBit (wOuter wInner2 : ℕ) : (selXoSoPolyInAncLowBit wOuter
    wInner2).DisjointWires
      ((QRegister.block (mOutUB wOuter) (mMidUB wInner2) (by dsimp [mAncUB]; omega)).compose
        (rMidCoreLocLowBit wInner2)) := by
  rw [QRegister.disjoint_iff]; intro i j h; have hv := congrArg Fin.val h; have hj := j.isLt
  have hmid : (((QRegister.block (mOutUB wOuter) (mMidUB wInner2) (by dsimp [mAncUB]; omega) :
      QRegister (mMidUB wInner2) (mAncUB wOuter wInner2)).compose
        (rMidCoreLocLowBit wInner2)) j).val =
    mOutUB wOuter + j.val := by simp [rMidCoreLocLowBit]
  rw [hmid] at hv
  dsimp only [selXoSoPolyInAncLowBit, QRegister.compose_apply, Function.Embedding.coeFn_mk] at hv
  by_cases hi9 : i.val < 9
  · rw [dite_eq_left hi9] at hv
    have hlt : (selCtrlInAnc wOuter wInner2 ⟨i.val, by omega⟩).val < mOutUB wOuter := by
      by_cases hi8 : i.val < 8
      · rw [show (⟨i.val, by omega⟩ : Fin 15) = Fin.castAdd (5 + 1) (Fin.castAdd 1 ⟨i.val, hi8⟩)
            by ext; simp, selCtrlInAnc, QRegister.concat_apply_left, QRegister.compose_apply,
          selOutCtrlLoc, QRegister.concat_apply_left]; simp; omega
      · rw [show (⟨i.val, by omega⟩ : Fin 15) = Fin.castAdd (5 + 1) (Fin.natAdd 8 (0 : Fin 1))
            by ext; simp; omega, selCtrlInAnc, QRegister.concat_apply_left, QRegister.compose_apply,
          selOutCtrlLoc, QRegister.concat_apply_right]; simp
    omega
  · rw [dite_eq_right hi9] at hv
    have h14 : (selCtrlInAnc wOuter wInner2 ⟨14, by
        decide⟩).val = mOutUB wOuter + (5 + wInner2) := by
      rw [show (⟨14, by decide⟩ : Fin 15) = Fin.natAdd (8 + 1) (Fin.natAdd 5 (0 : Fin 1)) from rfl,
        selCtrlInAnc, QRegister.concat_apply_right, QRegister.compose_apply,
        selMidCtrlLoc, QRegister.concat_apply_right]; simp [rSigInLoc]
    omega
theorem embedMatrix_spinCat11_mulVec_tensorUBCat_lowBit {wOuter wInner2 : ℕ} (A :
    Operator (2 ^ (58 +
    11))) (B : Operator (2 ^ 58)) (cat : Fin (2 ^ 11) → ℂ) (hAB : ∀ ψ₀ : Fin (2 ^ 58) → ℂ, A *ᵥ
    tensorSpinCat ψ₀ cat = tensorSpinCat (B *ᵥ ψ₀) cat) (w : Fin (2 ^ nUB wOuter wInner2) → ℂ) :
    ((rSysCatUB wOuter wInner2 11).embedMatrix ((spinCatSub 11).embedMatrix A)) *ᵥ
      tensorUBCat w cat =
    tensorUBCat (((rSysUB wOuter wInner2).embedMatrix (rSpin0.embedMatrix B)) *ᵥ w) cat := by
  let rSpin0UB : QRegister 58 (nUB wOuter wInner2) := (rSysUB wOuter wInner2).compose rSpin0
  let rSpin0Cat : QRegister (58 + 11) (nUB wOuter wInner2 + 11) :=
    (rSysCatUB wOuter wInner2 11).compose
    (spinCatSub 11)
  rw [← QRegister.embedMatrix_compose, ← QRegister.embedMatrix_compose]
  have hc0 : rSpin0Cat.compose (QRegister.block 0 58 (by decide)) =
      (rUBInCat wOuter wInner2 11).compose rSpin0UB := CoherentAlias.qreg_ext fun i ↦ by
    rw [QRegister.compose_apply, show QRegister.block 0 58 (by decide : 0 + 58 ≤ 69) i =
      Fin.castAdd 11 i by ext; simp, QRegister.compose_apply,
      show spinCatSub 11 (Fin.castAdd 11 i) = Fin.castAdd 11 ⟨i.val, by omega⟩ by
        rw [spinCatSub, QRegister.concat_apply_left]; ext; simp,
      rSysCatUB, QRegister.concat_apply_left]; simp [rSysUB, rUBInCat, rSpin0UB, rSpin0]
  have hc1 : rSpin0Cat.compose (QRegister.block 58 11 (by decide)) = rCatInCat wOuter wInner2 11 :=
    CoherentAlias.qreg_ext fun j ↦ by
      rw [QRegister.compose_apply, show QRegister.block 58 11 (by decide : 58 + 11 ≤ 69) j =
        Fin.natAdd 58 j by ext; simp, QRegister.compose_apply,
        show spinCatSub 11 (Fin.natAdd 58 j) = Fin.natAdd (2 * 58) j by
          rw [spinCatSub, QRegister.concat_apply_right]; ext; simp,
        rSysCatUB, QRegister.concat_apply_right]
  have hrepCat (G : Fin (2 ^ (nUB wOuter wInner2 + 11))) (u : Fin (2 ^ 69)) :
    (rCatInCat wOuter wInner2
    11).extractIndex (rSpin0Cat.replaceIndex G u) = (QRegister.block 58 11 (by decide)
    ).extractIndex u := by
    rw [← hc1, QRegister.extractIndex_compose, QRegister.extractIndex_replaceIndex]
  have hrepUb (G : Fin (2 ^ (nUB wOuter wInner2 + 11))) (u : Fin (2 ^ 69)) :
    (rUBInCat wOuter wInner2
    11).extractIndex (rSpin0Cat.replaceIndex G u) = rSpin0UB.replaceIndex ((rUBInCat wOuter wInner2
    11).extractIndex G) ((QRegister.block 0 58 (by decide) ).extractIndex u) := by
    apply (basisBits (nUB wOuter wInner2)).injective; funext q
    rw [QRegister.basisBits_extractIndex]
    by_cases hq : q.val < 58
    · let p : Wire 58 := ⟨q.val, hq⟩
      have hqp : q = rSpin0UB p := by ext; simp [rSpin0UB, rSysUB, rSpin0, p]
      have hqpC : rUBInCat wOuter wInner2 11 q =
          rSpin0Cat (QRegister.block 0 58 (by decide) p) := by
        rw [hqp, ← QRegister.compose_apply (rUBInCat wOuter wInner2 11) rSpin0UB p, ← hc0]; rfl
      rw [hqpC, QRegister.basisBits_replaceIndex_apply, hqp,
        QRegister.basisBits_replaceIndex_apply, QRegister.basisBits_extractIndex]
    · have hnotUb : q ∉ Set.range rSpin0UB.wires := fun ⟨p, hp⟩ ↦ by
        have hv := congrArg Fin.val hp; simp [rSpin0UB, rSysUB, rSpin0] at hv; omega
      have hnotCat : rUBInCat wOuter wInner2 11 q ∉ Set.range rSpin0Cat.wires := by
        rintro ⟨idx, hidx⟩
        refine Fin.addCases (motive := fun idx ↦
          rSpin0Cat idx = rUBInCat wOuter wInner2 11 q → False)
          (fun a ha ↦ ?_) (fun b hb ↦ ?_) idx hidx
        · have ha' : ((rUBInCat wOuter wInner2 11).compose rSpin0UB) a =
            rUBInCat wOuter wInner2 11 q := by
            rw [← hc0, QRegister.compose_apply,
              ← (by ext; simp : Fin.castAdd 11 a = QRegister.block 0 58 _ a)]; exact ha
          have hv := congrArg Fin.val ha'; simp [rUBInCat, rSpin0UB, rSysUB, rSpin0] at hv; omega
        · have hb' : rCatInCat wOuter wInner2 11 b = rUBInCat wOuter wInner2 11 q := by
            rw [← hc1, QRegister.compose_apply,
              ← (by ext; simp : Fin.natAdd 58 b = QRegister.block 58 11 _ b)]; exact hb
          have hv := congrArg Fin.val hb'; have hql := q.isLt
          simp [rUBInCat, rCatInCat] at hv; omega
      rw [rSpin0Cat.basisBits_replaceIndex_of_not_mem _ _ _ hnotCat,
        rSpin0UB.basisBits_replaceIndex_of_not_mem _ _ _ hnotUb, QRegister.basisBits_extractIndex]
  funext G
  let gUb := (rUBInCat wOuter wInner2 11).extractIndex G
  let ψG : Fin (2 ^ 58) → ℂ := fun u₅₈ ↦ w (rSpin0UB.replaceIndex gUb u₅₈)
  rw [rSpin0Cat.embedMatrix_mulVec_apply]
  have hsum : (∑ u : Fin (2 ^ (58 + 11)), A (rSpin0Cat.extractIndex G) u * tensorUBCat w cat
    (rSpin0Cat.basisSplitEquiv.symm (u, (rSpin0Cat.basisSplitEquiv G).2))) = (A *ᵥ tensorSpinCat ψG
    cat) (rSpin0Cat.extractIndex G) := by
    dsimp only [Matrix.mulVec, dotProduct, tensorUBCat, tensorSpinCat, ψG, gUb]
    refine Finset.sum_congr rfl fun u _ ↦ ?_
    change _ * (w ((rUBInCat wOuter wInner2 11).extractIndex (rSpin0Cat.replaceIndex G u)) * cat
      ((rCatInCat wOuter wInner2 11).extractIndex (rSpin0Cat.replaceIndex G u))) = _
    rw [hrepUb, hrepCat]
  refine hsum.trans ?_; rw [hAB ψG]; dsimp only [tensorSpinCat, tensorUBCat, gUb]
  have hex0 : (QRegister.block 0 58 (by decide) ).extractIndex (rSpin0Cat.extractIndex G) =
    rSpin0UB.extractIndex gUb := by
    rw [← QRegister.extractIndex_compose, hc0, QRegister.extractIndex_compose]
  have hex1 : (QRegister.block 58 11 (by decide)).extractIndex (rSpin0Cat.extractIndex G) =
      (rCatInCat wOuter wInner2 11).extractIndex G := by rw [← QRegister.extractIndex_compose, hc1]
  rw [hex0, hex1, rSpin0UB.embedMatrix_mulVec_apply]; rfl
/-- Exact (`0`-error) `11`-qubit phase-gradient catalyst action of `sel` at `(wOuter, wInner2)`. -/
noncomputable abbrev SelCatEqOuterInner (wOuter wInner2 : ℕ) (sel :
    Unitary (2 ^ (nUB wOuter wInner2 + 11))) (uP :
    Unitary (2 ^ nUB wOuter wInner2)) : Prop :=
      ∀ u : Fin (2 ^ nUB wOuter wInner2) → ℂ, sel.1 *ᵥ tensorUBCat u
    (phaseGradientLowFactor 11 3) = tensorUBCat (uP.1 *ᵥ u) (phaseGradientLowFactor 11 3)
theorem diag_proj_comm_lowBit {N k₁ k₂ : ℕ} (r₁ : QRegister k₁ N) (r₂ : QRegister k₂ N) (x : Fin (2
    ^ k₁)) (y : Fin (2 ^ k₂)) : r₁.basisOutcomeProjector x * r₂.basisOutcomeProjector y =
    r₂.basisOutcomeProjector y * r₁.basisOutcomeProjector x := by
  rw [r₁.basisOutcomeProjector_eq_diagonal, r₂.basisOutcomeProjector_eq_diagonal,
    Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1; funext g; exact mul_comm _ _
end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.LowBitPi145Select

end

/-!
# Low-Bit `π145` `SiZero` `StageA` (`12,526 T`) & `StageB` (`117`/`148` Wires, `24,364 T`)

Constructs the `116`-inner-wire `23,656-T` (`0 TOFF`) split `[0, 64) ⊔ [64, 145)` two-subpass
Lacunary-2 `Core145Bundle` (`11,774 + 11,842 + 40 = 23,656 T` core + `464 T` swaps + `244 T`
router = `24,364 T/pass`, `48,728 T` total) and exports full `bQPE`-parametric `WalkTopBridge` and
`combQubits` `StageA` (`160 ≤ sUb`, `12,526 T/pass`, `25,052 T` total) and `StageB` (`117 ≤ sUb`
and `148 ≤ sUb`) contracts sharing `rfl`-identical pure unitaries.

## References
- D. W. Berry, C. Gidney, M. Motta, J. R. McClean, and R. Babbush, "Qubitization of Arbitrary
  Basis Quantum Chemistry Leveraging Sparsity and Low Rank Factorization," *Quantum* **3**, 208
  (2019), DOI: `10.22331/q-2019-12-02-208`.
- R. Babbush, C. Gidney, D. W. Berry, N. Wiebe, J. McClean, A. Paler, A. Fowler, and H. Neven,
  "Encoding Electronic Spectra in Quantum Circuits with Linear T Complexity," *Phys. Rev. X* **8**,
  041015 (2018), DOI: `10.1103/PhysRevX.8.041015`.
- C. Gidney, "Halving the cost of quantum addition," *Quantum* **2**, 74 (2018),
  DOI: `10.22331/q-2018-06-18-74`.
-/

@[expose] public section
namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.LowBitPi145Select
open QuantumComputation.Specs QuantumComputation.Specs.P450

open Operator QProg Matrix HermitianMat Real CoherentAlias
open QuantumComputation.Specs Solution QuantumComputation.Specs.P450 Solution
open Solution.CircuitModular Solution.GivensOps
open Solution.BlockEncodingCore Solution.BlockEncodingCircuit
open Solution.SelectSwapQROM Solution.GivensCascade
open Solution.SelectRouter10 Solution.TopIntegrationBridge
open Solution.Lac2Fused184Select Solution.Lac2Fused184SelectWrap Solution.Router10Lac2Select
open Solution.Phase2MidSandwich Solution.PolymorphicFused184Select Solution.Lac2ZeroPar183Select
open Solution.CompactFoldedSelect Solution.ReordOuter13Bridge Solution.CompactStepFast176Select
open Solution.StepEncK Solution.StepDecK Solution.CompactStepFast175Core
open Solution.CompactOuter9Bound50Core Solution.CompactOuter9Bound50Select
open Solution.MobiusOptSubcube163Walk
open Solution.CompactTuned162StepWalk Solution.CompactTuned162StepZeroCmp20
open Solution.CompactZeroCmp20OuterParam Solution.CompactStepZeroCmp20OuterParam
open Solution.Balanced160Select Solution.Pi145SOSPermBridge Solution.OneHotSimulates
open WalkQPEBridge WalkQPEBridgeXMeas WalkQPEFlexBridge Solution.CleanDyn
open scoped Matrix BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator Circuit.Notation
local instance (priority := 1000000) instNeZeroTwoPowPhaseB (k : ℕ) : NeZero (2 ^ k) :=
    ⟨(Nat.two_pow_pos k).ne'⟩
/-! ## Section 1: `StageB` Split `[0, 64) ⊔ [64, 145)` Core (`116` Inner Wires, `23,656 T`) -/

/-- `RouterStep.cnot` shorthand on `22` encoder wires. -/
abbrev eC (c t : Wire 22) (h : c ≠ t := by decide) : RouterStep 22 := .cnot c t h
/-! ## Section 2: `embedKet` Branch Equations, `StageA` (`160` Wires) & `StageB` (`117`/`148`
Wires) -/
end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.LowBitPi145Select

end

/-!
# Bell-Singlet `StageA` Two-Pass `SELECT` Pair (`24,820 T`, `0 TOFF`, `160 ≤ sUb`)

Splits `RouterStep` conjugation into `routerStepsFwdUnitDyn` and `routerStepsBwdUnitDyn`, and
realizes the inner spin-swap pair across the spin-idle turnaround in `StageA`
(`stageACore145Bundle`) via `dBellExit58Dyn` (`232 T`) and `dBellEntry58Dyn` (`0 T`)
(C. Jones, *Phys. Rev. A* **87**, 022328 (2013); C. Gidney, *Quantum* **2**, 74 (2018);
R. Babbush *et al.*, *Phys. Rev. X* **8**, 041015 (2018)).
-/
@[expose] public section
namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.BellPhaseASelect
open QuantumComputation.Specs QuantumComputation.Specs.P450
open Operator QProg Matrix HermitianMat Real QuantumComputation.Specs Solution Solution.CleanDyn
open QuantumComputation.Specs.P450 Solution Solution.CircuitModular
open Solution.BlockEncodingCore Solution.BlockEncodingCircuit
open Solution.LowBitPi145Select Solution.Lac2Fused184Select Solution.CompactStepFast176Select
open Solution.CompactOuter9Bound50Core Solution.PolymorphicFused184Select
open Solution.Phase2MidSandwich Solution.MidReflCtxRetain Solution.TopIntegrationBridge
open Solution.CompactTuned162StepWalk Solution.CompactTuned162StepZeroCmp20
open Solution.SelectSwapQROM Solution.BellSingletCSwap58
open scoped Matrix BigOperators ComplexOrder MatrixOrder Circuit.Notation
/-! ## Section 1: Forward/Backward `RouterStep` Programs & Subspace `wp` Algebra -/
/-- Forward half of a single `RouterStep` (`4 T` on `.andAlloc`, `0 T` otherwise, `0 TOFF`). -/
def routerStepFwdUnit {n : ℕ} : RouterStep n → DynamicCircuit Unit n
  | .x t => .circuit (.X t) | .cnot c t hne => .circuit (.CNOT c t hne)
  | .andAlloc c₁ c₂ anc _ h₁a h₂a => .andCompute c₁ c₂ anc h₁a h₂a
  | .andFree c₁ c₂ anc h₁₂ _ _ => .andUncompute () c₁ c₂ anc h₁₂
/-- Backward half of a single `RouterStep` (`4 T` on `.andFree`, `0 T` otherwise, `0 TOFF`). -/
def routerStepBwdUnit {n : ℕ} : RouterStep n → DynamicCircuit Unit n
  | .x t => .circuit (.X t) | .cnot c t hne => .circuit (.CNOT c t hne)
  | .andAlloc c₁ c₂ anc h₁₂ _ _ => .andUncompute () c₁ c₂ anc h₁₂
  | .andFree c₁ c₂ anc _ h₁a h₂a => .andCompute c₁ c₂ anc h₁a h₂a
/-- Forward `DynamicCircuit Unit` sequence for a `RouterStep` list. -/
def routerStepsFwdUnitDyn {n : ℕ} : List (RouterStep n) → DynamicCircuit Unit n
  | [] => .identity | s :: rest => .seq (routerStepFwdUnit s) (routerStepsFwdUnitDyn rest)
/-- Backward `DynamicCircuit Unit` sequence for a `RouterStep` list. -/
def routerStepsBwdUnitDyn {n : ℕ} : List (RouterStep n) → DynamicCircuit Unit n
  | [] => .identity | s :: rest => .seq (routerStepsBwdUnitDyn rest) (routerStepBwdUnit s)
@[simp] theorem count_routerStepsFwdUnitDyn_toff {n : ℕ} (steps : List (RouterStep n)) :
    (routerStepsFwdUnitDyn steps).count .TOFF = 0 := by
  induction steps with
  | nil => rfl | cons s _ ih => cases s <;> simp [routerStepsFwdUnitDyn, routerStepFwdUnit, ih]
@[simp] theorem count_routerStepsBwdUnitDyn_toff {n : ℕ} (steps : List (RouterStep n)) :
    (routerStepsBwdUnitDyn steps).count .TOFF = 0 := by
  induction steps with
  | nil => rfl | cons s _ ih => cases s <;> simp [routerStepsBwdUnitDyn, routerStepBwdUnit, ih]
theorem count_routerStepsFwdBwd_t {n : ℕ} (steps : List (RouterStep n)) :
    (routerStepsFwdUnitDyn steps).count .T + (routerStepsBwdUnitDyn steps).count .T =
      4 * numRouterAnds steps := by
  induction steps with
  | nil => simp [routerStepsFwdUnitDyn, routerStepsBwdUnitDyn, numRouterAnds]
  | cons s _ ih =>
    cases s with
    | x _ | cnot _ _ _ =>
      simp [routerStepsFwdUnitDyn, routerStepsBwdUnitDyn, routerStepFwdUnit, routerStepBwdUnit,
        numRouterAnds, DynamicCircuit.count, ih]
    | andAlloc _ _ _ _ _ _ | andFree _ _ _ _ _ _ =>
      simp only [routerStepsFwdUnitDyn, routerStepsBwdUnitDyn, routerStepFwdUnit, routerStepBwdUnit,
        numRouterAnds, dyn_count_seq, DynamicCircuit.count_andCompute_t,
        DynamicCircuit.count_andUncompute_t]; omega
@[simp] theorem support_liftUnitVar {Var : Type} {n : ℕ} (v : Var) (P : DynamicCircuit Unit n) :
    (liftUnitVar v P).support = P.support := by
  induction P using DynamicCircuit.qcInd with
  | circuit _ => simp [liftUnitVar_circuit]
  | measure _ _ => simp [liftUnitVar_measure]
  | qIf _ _ _ t f => simp [liftUnitVar_qIf, t, f]
  | seq _ _ a b => simp [liftUnitVar_seq, a, b]
theorem support_routerStepsFwdBwd_subset {n : ℕ} {T : Finset (Wire n)} (steps : List (RouterStep n))
    (hT : ∀ s ∈ steps, s.TouchesIn (fun q ↦ q ∈ T)) :
    (routerStepsFwdUnitDyn steps).support ⊆ T ∧ (routerStepsBwdUnitDyn steps).support ⊆ T := by
  induction steps with
  | nil => simp [routerStepsFwdUnitDyn, routerStepsBwdUnitDyn]
  | cons s rest ih =>
    have hs := hT s (List.mem_cons_self ..)
    obtain ⟨ihF, ihB⟩ := ih fun s' hm ↦ hT s' (List.mem_cons_of_mem _ hm)
    have h1 : (routerStepFwdUnit s).support ⊆ T ∧ (routerStepBwdUnit s).support ⊆ T := by
      cases s with
      | x _ =>
        dsimp only [RouterStep.TouchesIn] at hs
        simp [routerStepFwdUnit, routerStepBwdUnit, Circuit.X, hs]
      | cnot _ _ _ =>
        rcases hs with ⟨hc, ht⟩
        simp [routerStepFwdUnit, routerStepBwdUnit, Finset.insert_subset_iff, hc, ht]
      | andAlloc _ _ _ _ _ _ | andFree _ _ _ _ _ _ =>
        rcases hs with ⟨hc₁, hc₂, ha⟩
        simp [routerStepFwdUnit, routerStepBwdUnit, Finset.insert_subset_iff, hc₁, hc₂, ha]
    exact ⟨Finset.union_subset h1.1 ihF, Finset.union_subset ihB h1.2⟩
theorem wp_seq_compile {Var : Type} [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)]
    (a b : DynamicCircuit Var n) (Θ : QCAssertion Var (2 ^ n)) :
    wp (a.seq b).compile Θ = wp a.compile (wp b.compile Θ) := rfl
theorem wp_bell_assoc {Var : Type} [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)]
    (a b c d e f : DynamicCircuit Var n) (Ψ : QCAssertion Var (2 ^ n)) :
    wp (DynamicCircuit.seq a (.seq b (.seq c (.seq d (.seq e f))))).compile Ψ =
      wp (DynamicCircuit.seq a (.seq (.seq b (.seq c d)) e)).compile (wp f.compile Ψ) := by
  simp only [wp_seq_compile]
theorem wp_liftUnitVar_routerStepsProg {Var : Type} [DecidableEq Var] {n : ℕ}
    [NeZero (2 ^ n)] (v : Var) (steps : List (RouterStep n)) (body : DynamicCircuit Unit n)
    (Θ : QCAssertion Var (2 ^ n)) : wp (liftUnitVar v (routerStepsProg () steps body)).compile Θ =
      wp (liftUnitVar v (routerStepsFwdUnitDyn steps)).compile (wp (liftUnitVar v body).compile
        (wp (liftUnitVar v (routerStepsBwdUnitDyn steps)).compile Θ)) := by
  induction steps generalizing Θ with
  | nil => simp [routerStepsProg, routerStepsFwdUnitDyn, routerStepsBwdUnitDyn]
  | cons s rest ih =>
    have hs : routerStepsProg () (s :: rest) body =
        .seq (routerStepFwdUnit s) (.seq (routerStepsProg () rest body) (routerStepBwdUnit s)) := by
      cases s <;> rfl
    rw [hs]; simp only [routerStepsFwdUnitDyn, routerStepsBwdUnitDyn, liftUnitVar_seq,
      DynamicCircuit.compile_seq, wp]; exact congrArg _ (ih _)
/-- Constant-observable `wp` property for a `Unit`-variable `DynamicCircuit`. -/
def ConstWp {n : ℕ} [NeZero (2 ^ n)] (d : DynamicCircuit Unit n) : Prop :=
  ∀ M : Observable (Fin (2 ^ n)), ∃ M' : Observable (Fin (2 ^ n)), wp d.compile (fun _ ↦
    M) = fun _ ↦ M'
theorem ConstWp.circuit {n : ℕ} [NeZero (2 ^ n)] (c : Circuit n) : ConstWp (.circuit c) :=
  fun M ↦ ⟨qcQAssignObsMap c.eval M, by funext _; simp [qcWpQAssign]⟩
theorem ConstWp.seq {n : ℕ} [NeZero (2 ^ n)] {d₁ d₂ : DynamicCircuit Unit n}
    (h₁ : ConstWp d₁) (h₂ : ConstWp d₂) : ConstWp (.seq d₁ d₂) := fun M ↦ by
  obtain ⟨M₂, hM₂⟩ := h₂ M; obtain ⟨M₁, hM₁⟩ := h₁ M₂
  exact ⟨M₁, by simp [DynamicCircuit.compile_seq, hM₂, hM₁]⟩
theorem ConstWp.routerStepsFwdBwd {n : ℕ} [NeZero (2 ^ n)] (steps : List (RouterStep n)) :
    ConstWp (routerStepsFwdUnitDyn steps) ∧ ConstWp (routerStepsBwdUnitDyn steps) := by
  induction steps with
  | nil => exact ⟨ConstWp.circuit .identity, ConstWp.circuit .identity⟩
  | cons s _ ih =>
    have hs : ConstWp (routerStepFwdUnit s) ∧ ConstWp (routerStepBwdUnit s) := by
      cases s with
      | x _ | cnot _ _ _ => exact ⟨ConstWp.circuit _, ConstWp.circuit _⟩
      | andAlloc c₁ c₂ anc h₁₂ _ _ =>
        exact ⟨ConstWp.circuit _, fun M ↦ OneHotSimulates.wp_andUncompute_const () c₁ c₂ anc h₁₂ M⟩
      | andFree c₁ c₂ anc h₁₂ _ _ =>
        exact ⟨fun M ↦ OneHotSimulates.wp_andUncompute_const () c₁ c₂ anc h₁₂ M, ConstWp.circuit _⟩
    exact ⟨hs.1.seq ih.1, ih.2.seq hs.2⟩
theorem wp_liftUnitVar_of_v_inv {Var : Type} [Finite Var] [DecidableEq Var] {n : ℕ}
    [NeZero (2 ^ n)] (v : Var) {d : DynamicCircuit Unit n} (hd : ConstWp d)
    (Θ : QCAssertion Var (2 ^ n)) (hΘ : ∀ σ val, Θ (Function.update σ v val) = Θ σ)
    (σ : Store Var) : wp (liftUnitVar v d).compile Θ σ = wp d.compile (fun _ ↦ Θ σ) 0 := by
  cases nonempty_fintype Var
  obtain ⟨M', hM'⟩ := hd (Θ σ)
  have h1 := wp_eq_of_eq_on_v_fiber (onlyUsesVar_liftUnitVar v d) (Φ₁ := Θ)
    (Φ₂ := fun τ ↦ (fun _ : Store Unit ↦ Θ σ) (fun _ ↦ τ v)) rfl (fun val ↦ hΘ σ val)
  rw [h1, wp_liftUnitVar v d (fun _ ↦ Θ σ) σ, congrFun hM' _, congrFun hM' 0]
theorem ConstWp.preservesVInv {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)]
    (v : Var) {d : DynamicCircuit Unit n} (hd : ConstWp d) : PreservesVInv v (liftUnitVar v d) :=
  fun Θ hΘ σ val ↦ by rw [wp_liftUnitVar_of_v_inv v hd Θ hΘ, wp_liftUnitVar_of_v_inv v hd Θ hΘ, hΘ]
/-- On input projector `P`, `d : DynamicCircuit Unit n` has `ConstWp` and acts as `U` in `wp`. -/
def SimulatesOnProj {n : ℕ} [NeZero (2 ^ n)] (P : Operator (2 ^ n)) (U : Unitary (2 ^ n))
    (d : DynamicCircuit Unit n) : Prop :=
  ConstWp d ∧ ∀ M : Observable (Fin (2 ^ n)),
    P * (wp d.compile (fun _ ↦ M) 0).1.1 * P = P * (U.1ᴴ * M.1.1 * U.1) * P
theorem SimulatesOnProj.ofDiagProj {n : ℕ} [NeZero (2 ^ n)] {P : Operator (2 ^ n)}
    {U : Unitary (2 ^ n)} {d : DynamicCircuit Unit n} (hd : DiagProjSimulates P U d) :
    SimulatesOnProj P U d :=
  ⟨fun M ↦ let ⟨M', h, _⟩ := hd.2.2 M; ⟨M', h⟩,
    fun M ↦ let ⟨_, hwp, hproj⟩ := hd.2.2 M; by rwa [congrFun hwp 0]⟩
theorem SimulatesOnProj.circuit {n : ℕ} [NeZero (2 ^ n)] (P : Operator (2 ^ n)) (c : Circuit n) :
    SimulatesOnProj P c.eval (.circuit c) :=
  ⟨ConstWp.circuit c, fun M ↦ by simp [qcWpQAssign, Matrix.star_eq_conjTranspose, Matrix.mul_assoc]⟩
theorem SimulatesOnProj.seq {n : ℕ} [NeZero (2 ^ n)] {P₁ P₂ : Operator (2 ^ n)}
    {U₁ U₂ : Unitary (2 ^ n)} {d₁ d₂ : DynamicCircuit Unit n}
    (h₁ : SimulatesOnProj P₁ U₁ d₁) (h₂ : SimulatesOnProj P₂ U₂ d₂)
    (hP₁ : P₁ᴴ = P₁) (hP₂ : P₂ᴴ = P₂) (hMap : P₂ * U₁.1 * P₁ = U₁.1 * P₁) :
    SimulatesOnProj P₁ (U₂ * U₁) (.seq d₁ d₂) := by
  refine ⟨h₁.1.seq h₂.1, fun M ↦ ?_⟩
  obtain ⟨M₂, hM₂⟩ := h₂.1 M; have h2 := h₂.2 M; rw [congrFun hM₂ 0] at h2
  have hMapR : P₂ * (U₁.1 * P₁) = U₁.1 * P₁ := by rwa [← Matrix.mul_assoc]
  have hadj : P₁ * U₁.1ᴴ * P₂ = P₁ * U₁.1ᴴ := by
    simpa only [Matrix.conjTranspose_mul, hP₁, hP₂, ← Matrix.mul_assoc] using
      congrArg conjTranspose hMap
  rw [DynamicCircuit.compile_seq]
  change P₁ * (wp d₁.compile (wp d₂.compile (fun _ ↦ M)) 0).1.1 * P₁ = _
  rw [hM₂, h₁.2 M₂]; simp only [Submonoid.coe_mul, Matrix.conjTranspose_mul]
  calc P₁ * (U₁.1ᴴ * M₂.1.1 * U₁.1) * P₁
      = P₁ * U₁.1ᴴ * (P₂ * M₂.1.1 * P₂) * U₁.1 * P₁ := by
          simp only [← Matrix.mul_assoc, hadj]; simp only [Matrix.mul_assoc, hMapR]
    _ = P₁ * ((U₁.1ᴴ * U₂.1ᴴ) * M.1.1 * (U₂.1 * U₁.1)) * P₁ := by
          rw [h2]; simp only [← Matrix.mul_assoc, hadj]; simp only [Matrix.mul_assoc, hMapR]
theorem SimulatesOnProj.wp_conj_eq {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    [NeZero (2 ^ n)] (v : Var) {S : Finset (Wire n)} {U : Unitary (2 ^ n)}
    {d : DynamicCircuit Unit n} (hd : SimulatesOnProj (zeroProjOn S) U d)
    (Ψ : QCAssertion Var (2 ^ n)) (hΨ : ∀ σ val, Ψ (Function.update σ v val) = Ψ σ) :
    SelectSwapQROM.restrictZeroSet (wp (liftUnitVar v d).compile Ψ) S =
      SelectSwapQROM.restrictZeroSet (qcWpQAssign U Ψ) S := by
  funext σ; apply Subtype.ext; apply HermitianMat.ext
  rw [SelectSwapQROM.restrictZeroSet_coe, SelectSwapQROM.restrictZeroSet_coe,
    wp_liftUnitVar_of_v_inv v hd.1 Ψ hΨ σ]
  simpa only [qcWpQAssign, qcQAssignObsMap, Observable.conj_coe, Unitary.coe_star,
    Matrix.star_eq_conjTranspose, conj_apply_mat, conjTranspose_conjTranspose,
    zeroProjOn_conjTranspose, val_eq_coe] using hd.2 (Ψ σ)
theorem SimulatesOnProj.restrictZeroSet_eq {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    [NeZero (2 ^ n)] (v : Var) {S_in S_out : Finset (Wire n)} {U : Unitary (2 ^ n)}
    {d : DynamicCircuit Unit n} (hd : SimulatesOnProj (zeroProjOn S_in) U d)
    (hMap : zeroProjOn S_out * U.1 * zeroProjOn S_in = U.1 * zeroProjOn S_in)
    (Ψ : QCAssertion Var (2 ^ n)) (hΨ : ∀ σ val, Ψ (Function.update σ v val) = Ψ σ) :
    SelectSwapQROM.restrictZeroSet (wp (liftUnitVar v d).compile Ψ) S_in =
      SelectSwapQROM.restrictZeroSet
        (wp (liftUnitVar v d).compile (SelectSwapQROM.restrictZeroSet Ψ S_out)) S_in := by
  have hMapR : zeroProjOn S_out * (U.1 * zeroProjOn S_in) = U.1 * zeroProjOn S_in := by
    rwa [← Matrix.mul_assoc]
  have hadj : zeroProjOn S_in * U.1ᴴ * zeroProjOn S_out = zeroProjOn S_in * U.1ᴴ := by
    simpa only [Matrix.conjTranspose_mul, zeroProjOn_conjTranspose, ← Matrix.mul_assoc] using
      congrArg conjTranspose hMap
  rw [hd.wp_conj_eq v Ψ hΨ,
    hd.wp_conj_eq v _ fun σ val ↦ by simp [SelectSwapQROM.restrictZeroSet, hΨ σ val]]
  funext σ; apply Subtype.ext; apply HermitianMat.ext
  simp only [SelectSwapQROM.restrictZeroSet_coe, qcWpQAssign, qcQAssignObsMap,
    Observable.conj_coe, Unitary.coe_star, Matrix.star_eq_conjTranspose, conj_apply_mat,
    conjTranspose_conjTranspose, zeroProjOn_conjTranspose]
  simp only [← Matrix.mul_assoc, hadj]; simp only [Matrix.mul_assoc, hMapR]
theorem SimulatesOnProj.restrictZeroSet_eq_circuit {Var : Type} [Fintype Var] [DecidableEq Var]
    {n : ℕ} [NeZero (2 ^ n)] (v : Var) {S : Finset (Wire n)} {c : Circuit n}
    {d : DynamicCircuit Unit n} (hd : SimulatesOnProj (zeroProjOn S) c.eval d)
    (Ψ : QCAssertion Var (2 ^ n)) (hΨ : ∀ σ val, Ψ (Function.update σ v val) = Ψ σ) :
    SelectSwapQROM.restrictZeroSet (wp (liftUnitVar v d).compile Ψ) S =
      SelectSwapQROM.restrictZeroSet (wp (DynamicCircuit.circuit c).compile Ψ) S := by
  rw [hd.wp_conj_eq v Ψ hΨ, DynamicCircuit.compile_circuit, DynamicCircuit.qc_wp_circuit_compile]
theorem simulatesOnProj_andAlloc {n : ℕ} [NeZero (2 ^ n)] (c₁ c₂ anc : Wire n)
    (h₁₂ : c₁ ≠ c₂) (h₁a : c₁ ≠ anc) (h₂a : c₂ ≠ anc) (S : BitAssignment n → Prop)
    (hAnc0 : ∀ β, S β → β anc = 0) :
    SimulatesOnProj (ketPredProj S) (Circuit.TOFF c₁ c₂ anc h₁₂ h₁a h₂a).eval
      (.andCompute c₁ c₂ anc h₁a h₂a) := by
  let P_a := (QRegister.singleton anc).basisOutcomeProjector 0
  have hPSa : ketPredProj S * P_a = ketPredProj S := by
    dsimp only [P_a]; rw [basisOutcomeProjector_zero_eq_ketPredProj]
    exact ketPredProj_mul_of_imp fun β hS i ↦ by fin_cases i; exact hAnc0 β hS
  have hPaS : P_a * ketPredProj S = ketPredProj S :=
    ((IsDiagProj.basisOutcomeProjector _ 0).comm ⟨S, rfl⟩).trans hPSa
  refine ⟨ConstWp.circuit _, fun M ↦ ?_⟩
  let M' := qcQAssignObsMap (Circuit.andCompute c₁ c₂ anc h₁a h₂a).eval M
  have hwp : wp (DynamicCircuit.andCompute (Var := Unit) c₁ c₂ anc h₁a h₂a).compile
      (fun _ ↦ M) = fun _ ↦ M' := by
    funext _; simp [DynamicCircuit.andCompute, qcWpQAssign, M']
  have hval := congrArg (fun f : QCAssertion Unit (2 ^ n) ↦ (f 0).1.1)
    (DynamicCircuit.qc_wp_qAssign_andCompute c₁ c₂ anc h₁₂ h₁a h₂a (fun _ : Store Unit ↦ M))
  rw [hwp]
  have hstar : P_a * M'.1.1 * P_a =
      P_a * ((Circuit.TOFF c₁ c₂ anc h₁₂ h₁a h₂a).eval.1ᴴ * M.1.1 *
        (Circuit.TOFF c₁ c₂ anc h₁₂ h₁a h₂a).eval.1) * P_a := by
    dsimp only [P_a, M', restrictAssertionToZeroAncilla_coe, qcWpQAssign, qcQAssignObsMap]
      at hval ⊢
    simpa only [Observable.conj_coe, Unitary.coe_star, Matrix.star_eq_conjTranspose,
      conj_apply_mat, QRegister.basisOutcomeProjector_conjTranspose,
      conjTranspose_conjTranspose, Matrix.mul_assoc, val_eq_coe] using hval
  clear_value P_a M'
  have h2 := congrArg (fun X ↦ ketPredProj S * X * ketPredProj S) hstar
  simp only [← Matrix.mul_assoc, hPSa] at h2
  simpa only [Matrix.mul_assoc, hPaS] using h2
theorem simulatesOnProj_andFree {n : ℕ} [NeZero (2 ^ n)] (c₁ c₂ anc : Wire n)
    (h₁₂ : c₁ ≠ c₂) (h₁a : c₁ ≠ anc) (h₂a : c₂ ≠ anc) (S : BitAssignment n → Prop)
    (hAncEq : ∀ β, S β → β anc = β c₁ * β c₂) :
    SimulatesOnProj (ketPredProj S) (Circuit.TOFF c₁ c₂ anc h₁₂ h₁a h₂a).eval
      (.andUncompute () c₁ c₂ anc h₁₂) := by
  let P_a := (QRegister.singleton anc).basisOutcomeProjector 0
  set T_a := (Circuit.TOFF c₁ c₂ anc h₁₂ h₁a h₂a).eval
  have hPaH : P_aᴴ = P_a := (IsDiagProj.basisOutcomeProjector _ 0).conjTranspose_eq
  have hTsq : T_a.1 * T_a.1 = 1 :=
    congrArg Subtype.val (OneHotSimulates.toffoli_eval_mul_self c₁ c₂ anc h₁₂ h₁a h₂a)
  have hTh := OneHotSimulates.unitary_conjTranspose_eq_self_of_mul_self T_a
    (OneHotSimulates.toffoli_eval_mul_self c₁ c₂ anc h₁₂ h₁a h₂a)
  have hPaT : P_a * T_a.1 * ketPredProj S = T_a.1 * ketPredProj S := by
    classical
    dsimp only [P_a]; rw [basisOutcomeProjector_zero_eq_ketPredProj]
    apply OneHotSimulates.matrix_ext_ket; intro β
    simp only [← Matrix.mulVec_mulVec, ketPredProj_mulVec_ket]
    by_cases hS : S β
    · have h0 : ∀ i : Fin 1, Function.update β anc (β anc + β c₁ * β c₂)
          ((QRegister.singleton anc) i) = 0 := fun i ↦ by
        fin_cases i; simp [Function.update_self, hAncEq β hS, CharTwo.add_self_eq_zero]
      simp only [hS, h0, implies_true, ↓reduceIte, T_a, OneHotSimulates.ket_TOFF,
        ketPredProj_mulVec_ket]
    · simp only [hS, ↓reduceIte, mulVec_zero]
  have hPaTR : P_a * (T_a.1 * ketPredProj S) = T_a.1 * ketPredProj S := by rwa [← Matrix.mul_assoc]
  have hTPa : ketPredProj S * T_a.1 * P_a = ketPredProj S * T_a.1 := by
    simpa only [Matrix.conjTranspose_mul, IsDiagProj.conjTranspose_eq ⟨S, rfl⟩,
      hPaH, hTh, ← Matrix.mul_assoc] using congrArg conjTranspose hPaT
  refine ⟨fun M ↦ OneHotSimulates.wp_andUncompute_const () c₁ c₂ anc h₁₂ M, fun M ↦ ?_⟩
  obtain ⟨M_unc, hwp_unc⟩ := OneHotSimulates.wp_andUncompute_const () c₁ c₂ anc h₁₂ M
  have h1 := congrArg (fun f : QCAssertion Unit (2 ^ n) ↦ (f 0).1.1)
    (DynamicCircuit.qc_wp_toffoli_andUncompute_of_update_eq () c₁ c₂ anc h₁₂ h₁a h₂a
      (fun _ : Store Unit ↦ M) (fun _ _ ↦ rfl))
  rw [hwp_unc] at h1 ⊢
  have hstar : P_a * (T_a.1ᴴ * M_unc.1.1 * T_a.1) * P_a = P_a * M.1.1 * P_a := by
    dsimp only [P_a, T_a, restrictAssertionToZeroAncilla_coe, qcWpQAssign, qcQAssignObsMap]
      at h1 ⊢
    simpa only [Observable.conj_coe, Unitary.coe_star, Matrix.star_eq_conjTranspose,
      conj_apply_mat, QRegister.basisOutcomeProjector_conjTranspose,
      conjTranspose_conjTranspose, Matrix.mul_assoc, val_eq_coe] using h1
  clear_value P_a T_a
  have hTsqR (X : Operator (2 ^ n)) : T_a.1 * (T_a.1 * X) = X := by
    rw [← Matrix.mul_assoc, hTsq, Matrix.one_mul]
  rw [hTh] at hstar
  have h2 := congrArg (fun X ↦ ketPredProj S * T_a.1 * X * (T_a.1 * ketPredProj S)) hstar
  simp only [← Matrix.mul_assoc, hTPa] at h2
  simp only [Matrix.mul_assoc, hPaTR, hTsqR] at h2
  simpa only [hTh, Matrix.mul_assoc] using h2
theorem SimulatesOnProj.routerStepsFwd {n : ℕ} [NeZero (2 ^ n)] (steps : List (RouterStep n))
    (S : BitAssignment n → Prop) (hOk : ∀ β, S β → routerStepsOk steps β) :
    SimulatesOnProj (ketPredProj S) (routerStepsCircuit steps).eval
      (routerStepsFwdUnitDyn steps) := by
  induction steps generalizing S with
  | nil => exact SimulatesOnProj.circuit (ketPredProj S) .identity
  | cons s rest ih =>
    let S' : BitAssignment n → Prop := fun γ ↦ ∃ β, S β ∧ s.assign β = γ
    have hOk' : ∀ γ, S' γ → routerStepsOk rest γ := by
      rintro γ ⟨β, hS, rfl⟩; have h := hOk β hS
      cases s <;> [exact h; exact h; exact h.2; exact h.2]
    have hMap : ketPredProj S' * s.toCircuit.eval.1 * ketPredProj S =
        s.toCircuit.eval.1 * ketPredProj S := by
      classical
      apply OneHotSimulates.matrix_ext_ket; intro β;
        simp only [← mulVec_mulVec, ketPredProj_mulVec_ket]
      by_cases hS : S β
      · have hS' : S' (s.assign β) := ⟨β, hS, rfl⟩
        simp only [hS, hS', ↓reduceIte, ket_routerStep, ketPredProj_mulVec_ket]
      · simp only [hS, ↓reduceIte, mulVec_zero]
    have hs1 : SimulatesOnProj (ketPredProj S) s.toCircuit.eval (routerStepFwdUnit s) := by
      cases s with
      | x _ | cnot _ _ _ => exact SimulatesOnProj.circuit _ _
      | andAlloc c₁ c₂ anc h₁₂ h₁a h₂a =>
        exact simulatesOnProj_andAlloc c₁ c₂ anc h₁₂ h₁a h₂a S fun β h ↦ (hOk β h).1
      | andFree c₁ c₂ anc h₁₂ h₁a h₂a =>
        exact simulatesOnProj_andFree c₁ c₂ anc h₁₂ h₁a h₂a S fun β h ↦ (hOk β h).1
    simpa only [routerStepsCircuit, Circuit.eval_seq, routerStepsFwdUnitDyn] using
      hs1.seq (ih S' hOk') (IsDiagProj.conjTranspose_eq ⟨S, rfl⟩)
        (IsDiagProj.conjTranspose_eq ⟨S', rfl⟩) hMap

/-! ## Section 2: Bell-Singlet `StageA` Two-Pass `SELECT` Pair (`24,820 T`, `0 TOFF`) -/
local instance instNeZeroTwoPowBell (k : ℕ) : NeZero (2 ^ k) := ⟨(Nat.two_pow_pos k).ne'⟩
theorem proj_map_mul {d : ℕ} {P₁ P₂ P₃ A B : Operator d}
    (h₁ : P₂ * A * P₁ = A * P₁) (h₂ : P₃ * B * P₂ = B * P₂) : P₃ * (B * A) * P₁ = (B * A) * P₁ := by
  have h₁R : P₂ * (A * P₁) = A * P₁ := by rwa [← Matrix.mul_assoc]
  calc P₃ * (B * A) * P₁ = (P₃ * B * P₂) * (A * P₁) := by simp only [Matrix.mul_assoc, h₁R]
    _ = (B * A) * P₁ := by rw [h₂]; simp only [Matrix.mul_assoc, h₁R]
theorem disjoint_rSwap117_rInner {N kInner : ℕ} (hk6 : 6 ≤ kInner) (wOuter wInner2 : ℕ) (wNegIn :
    Wire wInner2)
    (rMain : QRegister (nUB wOuter wInner2 + 11) N) (rScr : QRegister (1 + kInner) N)
    (hdisj : rMain.DisjointWires rScr) : (rSwap117LowBit wOuter wInner2 wNegIn rMain).DisjointWires
      (lowBitCoreLayout wOuter wInner2 wNegIn rMain rScr hdisj).rInner := by
  have hIn := (lowBitCoreLayout_wires hk6 wOuter wInner2 wNegIn rMain rScr hdisj).2.2.1
  dsimp only [rSwap117LowBit]; exact QRegister.disjointWires_concat_left _
    (QRegister.disjoint_iff.mpr fun i _ ↦ by fin_cases i; rw [hIn]; exact hdisj.ne _ _)
    (QRegister.disjoint_iff.mpr fun _ _ ↦ by rw [hIn]; exact hdisj.ne _ _)
/-! ## Section 3: Entry Subspace Simulation, Core-Polymorphic 5-Step & `StageA` Wrappers -/

end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.BellPhaseASelect

end

/-!
# Parametric Streamed-`rA` Affine `Lac = 2` Givens Cascade (`0 ≤ d ≤ 10`, `22 - d` Work Wires)

Completes the `SubspaceStepU` / `RealizesCleanRef` verification of the streamed-`rA` Gidney
unsigned phase-kick engine and lifts it through the `58`-orbital
`Lac = 2` affine Givens cascade (`112` non-apex planes at `B = 11` with `d < 11` and fused
apex at `B = 10` with `d - 1 < 10`), recycling `wHot0` to operate in `22 - d` clean work wires
at `11,522 + 448 * d + 4 * (d - 1)` `T`-gates and `0 TOFF`.

## References
- C. Gidney, "Halving the cost of quantum addition," *Quantum* **2**, 74 (2018),
  DOI: `10.22331/q-2018-06-18-74`.
- R. Babbush, C. Gidney, D. W. Berry, N. Wiebe, J. McClean, A. Paler, A. Fowler, and H. Neven,
  "Encoding Electronic Spectra in Quantum Circuits with Linear T Complexity," *Phys. Rev. X* **8**,
  041015 (2018), DOI: `10.1103/PhysRevX.8.041015`.
- D. W. Berry, C. Gidney, M. Motta, J. R. McClean, and R. Babbush, "Qubitization of Arbitrary
  Basis Quantum Chemistry Leveraging Sparsity and Low Rank Factorization," *Quantum* **3**, 208
  (2019), DOI: `10.22331/q-2019-12-02-208`.
- J. Lee, D. W. Berry, C. Gidney, W. J. Huggins, J. R. McClean, N. Wiebe, and R. Babbush,
  "Even More Efficient Quantum Computations of Chemistry Through Tensor Hypercontraction,"
  *PRX Quantum* **2**, 030305 (2021), DOI: `10.1103/PRXQuantum.2.030305`.
- J. J. Goings *et al.*, "Reliably assessing the electronic structure of cytochrome P450 on
  today's classical computers and tomorrow's quantum computers," *Proc. Natl. Acad. Sci. U.S.A.*
  **119**(37), e2203533119 (2022), DOI: `10.1073/pnas.2203533119`.
-/

@[expose] public section

namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.PhaseB154Pi145Select
open QuantumComputation.Specs QuantumComputation.Specs.P450

open Operator QProg Matrix HermitianMat Real CoherentAlias
open QuantumComputation.Specs Solution QuantumComputation.Specs.P450 Solution
open Solution.CircuitModular Solution.GivensOps
open Solution.BlockEncodingCore Solution.BlockEncodingCircuit
open Solution.SelectSwapQROM Solution.GivensCascade
open Solution.SelectRouter10 Solution.TopIntegrationBridge
open Solution.Lac2Fused184Select Solution.Lac2Fused184SelectWrap Solution.Router10Lac2Select
open Solution.Phase2MidSandwich Solution.PolymorphicFused184Select Solution.Lac2ZeroPar183Select
open Solution.CompactFoldedSelect Solution.ReordOuter13Bridge Solution.CompactStepFast176Select
open Solution.StepEncK Solution.StepDecK Solution.CompactStepFast175Core
open Solution.CompactOuter9Bound50Core Solution.CompactOuter9Bound50Select
open Solution.MobiusOptSubcube163Walk
open Solution.CompactTuned162StepWalk Solution.CompactTuned162StepZeroCmp20
open Solution.CompactZeroCmp20OuterParam Solution.CompactStepZeroCmp20OuterParam
open Solution.Balanced160Select Solution.Pi145SOSPermBridge Solution.OneHotSimulates
open Solution.LowBitPi145Select
open WalkQPEBridge WalkQPEBridgeXMeas WalkQPEFlexBridge Solution.CleanDyn
open scoped Matrix BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator Circuit.Notation

/-! ## Section 1: `RealizesCleanRef` & `ket` Bridge for `compactRawUnsignedPhaseKickDyn` -/

section CompactKickBridge

variable {Var : Type} {n B d : ℕ}

theorem SubspaceStepU_gidneyFwdDyn [Fintype Var] [DecidableEq Var] (hdB : d < B)
    (rCat : QRegister B n) (rASh : QRegister (B - d) n) (rC : QRegister B n) (w_p : Wire n)
    (hd : CompactGidneyDisjoint rCat rASh rC w_p) (j : ℕ) (hjd : j < d) {R₀ : Operator (2 ^ n)}
    (hC0 : ZeroOnWire (rC ⟨j, by omega⟩) R₀) :
    SubspaceStepU R₀ ((gidneyFwdRef hdB rCat rASh rC w_p hd j hjd).eval.1 * R₀)
      (gidneyFwdDyn (Var := Var) hdB rCat rASh rC w_p hd j hjd) := by
  let jf : Fin B := ⟨j, by omega⟩; let i0 : Fin (B - d) := ⟨0, by omega⟩
  dsimp only [gidneyFwdDyn, gidneyFwdRef]; by_cases h0 : 0 < j
  · simp only [h0, ↓reduceDIte]
    let jprev : Fin B := ⟨j - 1, by omega⟩
    have hpne : jprev ≠ jf := fun h ↦ by
      have := congrArg Fin.val h; dsimp [jprev, jf] at this; omega
    let cPre := Circuit.CNOT (rC jprev) (rCat jf) (hd.ne_cat_C jf jprev).symm ;;ᶜ
      Circuit.CNOT (rC jprev) (rASh i0) (hd.ne_A_C i0 jprev).symm
    let cPost :=
      Circuit.CNOT (rC jprev) (rC jf) (UnsignedGivens.GidneyKickDisjoint.ne_C_C rC hpne) ;;ᶜ
      (Circuit.CNOT (rC jprev) (rASh i0) (hd.ne_A_C i0 jprev).symm ;;ᶜ
       Circuit.CNOT (rC jprev) (rCat jf) (hd.ne_cat_C jf jprev).symm)
    have hnot : rC jf ∉ cPre.support := by
      simp only [cPre, Circuit.support_seq, Circuit.support_cnot, Finset.mem_union,
        Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨⟨(UnsignedGivens.GidneyKickDisjoint.ne_C_C rC hpne).symm, (hd.ne_cat_C jf jf).symm⟩,
        ⟨(UnsignedGivens.GidneyKickDisjoint.ne_C_C rC hpne).symm, (hd.ne_A_C i0 jf).symm⟩⟩
    have hs1 := SubspaceStepU.of_circuit (Var := Var) (R₀ := R₀) cPre rfl
    have hs2 := SubspaceStepU.of_andCompute (Var := Var) (rCat jf) (rASh i0) (rC jf)
      (hd.ne_cat_A jf i0) (hd.ne_cat_C jf jf) (hd.ne_A_C i0 jf)
      (zeroOnWire_mul_of_not_mem_support (rC jf) cPre hnot hC0)
    refine (hs1.seq (hs2.seq (SubspaceStepU.of_circuit (Var := Var) cPost rfl))).congr rfl ?_
    dsimp only [gFwd4, cPre, cPost, jf, i0, jprev]
    simp only [Circuit.eval_seq, Submonoid.coe_mul, Matrix.mul_assoc]
  · simp only [h0, ↓reduceDIte]
    exact SubspaceStepU.of_andCompute (Var := Var) (rCat jf) (rASh i0) (rC jf)
      (hd.ne_cat_A jf i0) (hd.ne_cat_C jf jf) (hd.ne_A_C i0 jf) hC0

theorem SubspaceStepU_gidneyBwdDyn [Fintype Var] [DecidableEq Var] (v : Var) (hdB : d < B)
    (rCat : QRegister B n) (rASh : QRegister (B - d) n) (rC : QRegister B n) (w_p : Wire n)
    (hd : CompactGidneyDisjoint rCat rASh rC w_p) (j : ℕ) (hjd : j < d) {R₀ : Operator (2 ^ n)}
    (hC1 : ZeroOnWire (rC ⟨j, by omega⟩)
      ((gidneyBwdRef hdB rCat rASh rC w_p hd j hjd).eval.1 * R₀)) :
    SubspaceStepU R₀ ((gidneyBwdRef hdB rCat rASh rC w_p hd j hjd).eval.1 * R₀)
      (gidneyBwdDyn v hdB rCat rASh rC w_p hd j hjd) := by
  let jf : Fin B := ⟨j, by omega⟩; let i0 : Fin (B - d) := ⟨0, by omega⟩
  dsimp only [gidneyBwdDyn, gidneyBwdRef] at hC1 ⊢; by_cases h0 : 0 < j
  · simp only [h0, ↓reduceDIte] at hC1 ⊢
    let jprev : Fin B := ⟨j - 1, by omega⟩
    have hpne : jprev ≠ jf := fun h ↦ by
      have := congrArg Fin.val h; dsimp [jprev, jf] at this; omega
    let cPre := (Circuit.CNOT (rC jprev) (rCat jf) (hd.ne_cat_C jf jprev).symm ;;ᶜ
      Circuit.CNOT (rC jprev) (rASh i0) (hd.ne_A_C i0 jprev).symm) ;;ᶜ
      Circuit.CNOT (rC jprev) (rC jf) (UnsignedGivens.GidneyKickDisjoint.ne_C_C rC hpne)
    let T_anc := Circuit.TOFF (rCat jf) (rASh i0) (rC jf) (hd.ne_cat_A jf i0)
      (hd.ne_cat_C jf jf) (hd.ne_A_C i0 jf)
    let cPost := Circuit.CNOT (rC jprev) (rASh i0) (hd.ne_A_C i0 jprev).symm ;;ᶜ
      Circuit.CNOT (rASh i0) (rCat jf) (hd.ne_cat_A jf i0).symm
    have hnot : rC jf ∉ cPost.support := by
      simp only [cPost, Circuit.support_seq, Circuit.support_cnot, Finset.mem_union,
        Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨⟨(UnsignedGivens.GidneyKickDisjoint.ne_C_C rC hpne).symm, (hd.ne_A_C i0 jf).symm⟩,
        ⟨(hd.ne_A_C i0 jf).symm, (hd.ne_cat_C jf jf).symm⟩⟩
    have href_eq : ((Circuit.CNOT (rC jprev) (rCat jf) (hd.ne_cat_C jf jprev).symm ;;ᶜ
        Circuit.CNOT (rC jprev) (rASh i0) (hd.ne_A_C i0 jprev).symm) ;;ᶜ
        gBwd4 (rCat jf) (rASh i0) (rC jf) (rC jprev) (hd.ne_cat_A jf i0) (hd.ne_cat_C jf jf)
          (hd.ne_A_C i0 jf) (hd.ne_A_C i0 jprev)
          (UnsignedGivens.GidneyKickDisjoint.ne_C_C rC hpne).symm).eval.1 * R₀ =
        cPost.eval.1 * (T_anc.eval.1 * (cPre.eval.1 * R₀)) := by
      dsimp only [gBwd4, cPre, T_anc, cPost, jf, i0, jprev]
      simp only [Circuit.eval_seq, Submonoid.coe_mul, Matrix.mul_assoc]
    have hClean := proj_zero_of_post_eq (rC jf) cPost hnot (by rwa [← href_eq])
    have hs1 := SubspaceStepU.of_circuit (Var := Var) (R₀ := R₀) cPre rfl
    have hs2 := SubspaceStepU_of_andUncompute_fwd (R₀ := cPre.eval.1 * R₀) v (rCat jf) (rASh i0)
      (rC jf) (hd.ne_cat_A jf i0) (hd.ne_cat_C jf jf) (hd.ne_A_C i0 jf) hClean
    exact (hs1.seq (hs2.seq (SubspaceStepU.of_circuit (Var := Var) cPost rfl))).congr rfl
      href_eq.symm
  · simp only [h0, ↓reduceDIte] at hC1 ⊢
    let T_anc := Circuit.TOFF (rCat jf) (rASh i0) (rC jf) (hd.ne_cat_A jf i0)
      (hd.ne_cat_C jf jf) (hd.ne_A_C i0 jf)
    let cPost := Circuit.CNOT (rASh i0) (rCat jf) (hd.ne_cat_A jf i0).symm
    have hnot : rC jf ∉ cPost.support := by
      simp only [cPost, Circuit.support_cnot, Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨(hd.ne_A_C i0 jf).symm, (hd.ne_cat_C jf jf).symm⟩
    have href_eq : (gBwd3 (rCat jf) (rASh i0) (rC jf) (hd.ne_cat_A jf i0) (hd.ne_cat_C jf jf)
        (hd.ne_A_C i0 jf)).eval.1 * R₀ = cPost.eval.1 * (T_anc.eval.1 * R₀) := by
      dsimp only [gBwd3, T_anc, cPost, jf, i0]
      simp only [Circuit.eval_seq, Submonoid.coe_mul, Matrix.mul_assoc]
    have hClean := proj_zero_of_post_eq (rC jf) cPost hnot (by rwa [← href_eq])
    have hs1 := SubspaceStepU_of_andUncompute_fwd (R₀ := R₀) v (rCat jf) (rASh i0) (rC jf)
      (hd.ne_cat_A jf i0) (hd.ne_cat_C jf jf) (hd.ne_A_C i0 jf) hClean
    exact (hs1.seq (SubspaceStepU.of_circuit (Var := Var) cPost rfl)).congr rfl href_eq.symm

theorem SubspaceStepU_streamedPrefixDyn [Fintype Var] [DecidableEq Var] (v : Var) (hdB : d < B)
    (rCat : QRegister B n) (rASh : QRegister (B - d) n) (rC : QRegister B n) (w_p : Wire n)
    (hd : CompactGidneyDisjoint rCat rASh rC w_p) {S_ctrl : Finset (Wire n)}
    (bs : CompactPhaseKickBitSteps hdB rCat rASh rC w_p S_ctrl) (k : ℕ) (hk : k ≤ d)
    {R₀ : Operator (2 ^ n)} (hA0 : ∀ i : Fin (B - d), ZeroOnWire (rASh i) R₀)
    (hC0 : ∀ m : Fin B, d - k ≤ m.val → ZeroOnWire (rC m) R₀) :
    SubspaceStepU R₀ ((streamedPrefixRef hdB rCat rASh rC w_p hd bs k hk).eval.1 * R₀)
      (streamedPrefixDyn v hdB rCat rASh rC w_p hd bs k hk) := by
  induction k generalizing R₀ with
  | zero =>
      exact SubspaceStepU_loadResidSuffixDyn v hdB rCat rASh rC w_p hd bs (B - d) le_rfl
        (fun _ _ ↦ hA0 _) (fun m hm ↦ hC0 m (by omega))
  | succ k ih =>
      let j := d - (k + 1); have hjd : j < d := by omega
      let jf : Fin B := ⟨j, by omega⟩; let i0 : Fin (B - d) := ⟨0, by omega⟩; let s := bs.stepLo jf
      have hs_anc : s.anc = rASh i0 := by
        rw [bs.ancLo jf]; simp only [ancSh, jf, i0, hjd, ↓reduceIte]
      have hC_nc : rC jf ∉ S_ctrl := fun hm ↦
        Finset.disjoint_left.mp bs.disj_ctrl_C hm (QRegister.mem_image rC _ |>.mpr ⟨jf, rfl⟩)
      have hcat_nc : rCat jf ∉ S_ctrl := fun hm ↦
        Finset.disjoint_left.mp bs.disj_ctrl_cat hm (QRegister.mem_image rCat _ |>.mpr ⟨jf, rfl⟩)
      have hpermFB := gidneyFwdBwdRef_perm hdB rCat rASh rC w_p hd j hjd
      let c_pm := s.pre ;;ᶜ Circuit.TOFF s.c₁ s.c₂ s.anc s.h₁₂ s.h₁a s.h₂a ;;ᶜ s.midPre
      have hfixF_anc (β : BitAssignment n) : Function.update β (rC jf)
          (β (rC jf) + ((β (rCat jf) + if h0 : 0 < j then β (rC ⟨j - 1, by omega⟩) else 0) *
            (β (rASh i0) + if h0 : 0 < j then β (rC ⟨j - 1, by omega⟩) else 0) +
            if h0 : 0 < j then β (rC ⟨j - 1, by omega⟩) else 0)) s.anc = β s.anc := by
        rw [hs_anc]; exact Function.update_of_ne (hd.ne_A_C i0 jf) _ _
      have hfixF_ctrl (β : BitAssignment n) (w : Wire n) (hw : w ∈ S_ctrl) :
          Function.update β (rC jf)
            (β (rC jf) + ((β (rCat jf) + if h0 : 0 < j then β (rC ⟨j - 1, by omega⟩) else 0) *
              (β (rASh i0) + if h0 : 0 < j then β (rC ⟨j - 1, by omega⟩) else 0) +
              if h0 : 0 < j then β (rC ⟨j - 1, by omega⟩) else 0)) w = β w :=
        Function.update_of_ne (by rintro rfl; exact hC_nc hw) _ _
      have hsF : SubspaceStepU R₀
          ((s.wrapCircuit (gidneyFwdRef hdB rCat rASh rC w_p hd j hjd)).eval.1 * R₀)
          (s.wrapDynamic v (gidneyFwdDyn hdB rCat rASh rC w_p hd j hjd)) := by
        refine SubspaceStepU_cleanBitStep_wrap v (bs.cleanLo jf) hpermFB.1 hfixF_anc hfixF_ctrl
          (by rw [hs_anc]; exact hA0 i0) _ ?_
        dsimp only
        have hc_pm : s.midPre.eval.1 *
            ((Circuit.TOFF s.c₁ s.c₂ s.anc s.h₁₂ s.h₁a s.h₂a).eval.1 * (s.pre.eval.1 * R₀)) =
            c_pm.eval.1 * R₀ := by
          dsimp only [c_pm]; simp only [Circuit.eval_seq, Submonoid.coe_mul, Matrix.mul_assoc]
        rw [hc_pm]; exact SubspaceStepU_gidneyFwdDyn hdB rCat rASh rC w_p hd j hjd
          (zeroOnWire_mul_of_phasedPerm_fix (rC jf) c_pm (bs.cleanLo jf).pre_mid_perm
            (fun β ↦ by rw [hs_anc]; exact Function.update_of_ne (hd.ne_A_C i0 jf).symm _ _)
            (hC0 jf (by dsimp [jf]; omega)))
      have hwrapF_perm :=
        (UnsignedGivens.cleanBitStep_wrap_spec (bs.cleanLo jf) hpermFB.1 hfixF_anc hfixF_ctrl).1
      let cF := s.wrapCircuit (gidneyFwdRef hdB rCat rASh rC w_p hd j hjd)
      let R₁ := cF.eval.1 * R₀
      have hA0_R1 : ∀ i : Fin (B - d), ZeroOnWire (rASh i) R₁ := fun i ↦ by
        refine zeroOnWire_mul_of_phasedPerm_fix (rASh i) cF hwrapF_perm (fun β ↦ ?_) (hA0 i)
        by_cases hia : rASh i = s.anc
        · rw [hia, Function.update_self]
        · rw [Function.update_of_ne hia, Function.update_of_ne (hd.ne_A_C i jf),
            Function.update_of_ne hia]
      have hC0_R1 : ∀ m : Fin B, d - k ≤ m.val → ZeroOnWire (rC m) R₁ := fun m hm ↦ by
        refine zeroOnWire_mul_of_phasedPerm_fix (rC m) cF hwrapF_perm (fun β ↦ ?_)
          (hC0 m (by omega))
        have hne_anc : rC m ≠ s.anc := by rw [hs_anc]; exact (hd.ne_A_C i0 m).symm
        have hne_C : rC m ≠ rC jf := fun h ↦ by
          have := congrArg Fin.val (rC.wires.injective h); dsimp [jf] at this; omega
        rw [Function.update_of_ne hne_anc, Function.update_of_ne hne_C,
          Function.update_of_ne hne_anc]
      have hsMid := ih (by omega) hA0_R1 hC0_R1
      let cMid := streamedPrefixRef hdB rCat rASh rC w_p hd bs k (by omega)
      let R₂ := cMid.eval.1 * R₁
      obtain ⟨_, _, hperm_mid, hfix_mid, _⟩ :=
        streamedPrefixRef_spec hdB rCat rASh rC w_p hd bs k (by omega)
      have hA0_R2 : ZeroOnWire (rASh i0) R₂ :=
        zeroOnWire_mul_of_phasedPerm_fix (rASh i0) cMid hperm_mid
          (fun β ↦ hfix_mid β (rASh i0) fun m _ ↦ (hd.ne_cat_A m i0).symm) (hA0_R1 i0)
      have hsB : SubspaceStepU R₂
          ((s.wrapCircuit (gidneyBwdRef hdB rCat rASh rC w_p hd j hjd)).eval.1 * R₂)
          (s.wrapDynamic v (gidneyBwdDyn v hdB rCat rASh rC w_p hd j hjd)) := by
        refine SubspaceStepU_cleanBitStep_wrap v (bs.cleanLo jf) hpermFB.2
          (fun β ↦ by rw [hs_anc, Function.update_of_ne (hd.ne_cat_A jf i0).symm,
            Function.update_of_ne (hd.ne_A_C i0 jf)])
          (fun β w hw ↦ by rw [Function.update_of_ne (by rintro rfl; exact hcat_nc hw),
            Function.update_of_ne (by rintro rfl; exact hC_nc hw)])
          (by rw [hs_anc]; exact hA0_R2) _ ?_
        dsimp only; apply SubspaceStepU_gidneyBwdDyn
        let R_in2 := s.midPre.eval.1 *
          ((Circuit.TOFF s.c₁ s.c₂ s.anc s.h₁₂ s.h₁a s.h₂a).eval.1 * (s.pre.eval.1 * R₂))
        let c_mp := s.midPost ;;ᶜ Circuit.TOFF s.c₁ s.c₂ s.anc s.h₁₂ s.h₁a s.h₂a ;;ᶜ s.post
        have hmp_perm : UnsignedGivens.PhasedPerm c_mp (fun _ ↦ 1)
            (fun β ↦ Function.update β s.anc (β s.anc + bs.bitLo β jf)) := fun β ↦ by
          rw [one_smul]; exact (bs.cleanLo jf).mid_post_inv β
        apply zeroOnWire_of_mul_phasedPerm_fix (rC jf) c_mp hmp_perm
          (fun β ↦ by rw [hs_anc]; exact Function.update_of_ne (hd.ne_A_C i0 jf).symm _ _)
        obtain ⟨_, _, hperm_all, hfix_all, _⟩ :=
          streamedPrefixRef_spec hdB rCat rASh rC w_p hd bs (k + 1) hk
        have hall_C := zeroOnWire_mul_of_phasedPerm_fix (rC jf) _ hperm_all
          (fun β ↦ hfix_all β (rC jf) fun m _ ↦ (hd.ne_cat_C m jf).symm)
          (hC0 jf (by dsimp [jf]; omega))
        have hceq : c_mp.eval.1 * ((gidneyBwdRef hdB rCat rASh rC w_p hd j hjd).eval.1 * R_in2) =
            (streamedPrefixRef hdB rCat rASh rC w_p hd bs (k + 1) hk).eval.1 * R₀ := by
          dsimp only [streamedPrefixRef, UnsignedGivens.PhasedStep.wrapCircuit, c_mp, R_in2, R₂, R₁,
            cMid,
            cF, s, j, jf]
          simp only [Circuit.eval_seq, Submonoid.coe_mul, Matrix.mul_assoc]
        rwa [hceq]
      refine (hsF.seq (hsMid.seq hsB)).congr rfl ?_
      dsimp only [streamedPrefixRef, R₂, R₁, cMid, cF, s, j, jf]
      simp only [Circuit.eval_seq, Submonoid.coe_mul, Matrix.mul_assoc]

theorem compactRawUnsignedPhaseKickRef_phasedPerm (hdB : d < B) (rCat : QRegister B n)
    (rASh : QRegister (B - d) n) (rC : QRegister B n) (w_p : Wire n)
    (hd : CompactGidneyDisjoint rCat rASh rC w_p) {S_ctrl : Finset (Wire n)}
    (bs : CompactPhaseKickBitSteps hdB rCat rASh rC w_p S_ctrl) :
    ∃ (φ : BitAssignment n → ℂ) (f : BitAssignment n → BitAssignment n),
      UnsignedGivens.PhasedPerm (compactRawUnsignedPhaseKickRef hdB rCat rASh rC w_p hd bs) φ f ∧
      ∀ β (w : Wire n), w ∉ rCat.image → f β w = β w := by
  let a0 := rASh ⟨0, by omega⟩
  let cTopIn := Circuit.S a0 ;;ᶜ UnsignedGivens.czCircuit w_p a0 (hd.ne_A_wp ⟨0, by omega⟩).symm
  have hp_top_in : UnsignedGivens.PhasedPerm cTopIn
      (fun γ ↦ Complex.I ^ (γ a0).val * (-1 : ℂ) ^ (γ w_p * γ a0).val) id := fun γ ↦ by
    dsimp only [UnsignedGivens.PhasedPerm, cTopIn, id_eq]
    rw [UnsignedGivens.eval_seq_mulVec, UnsignedGivens.evolve_S_ket, Matrix.mulVec_smul,
      UnsignedGivens.evolve_czCircuit_ket, smul_smul]
  have hp₁ := cleanWrap_perm_of_eq bs.cleanTop hp_top_in (fun _ ↦ rfl) (fun _ _ _ ↦ rfl)
    (fun β ↦ update_update_self_eq β _ _)
  let cMidIn := UnsignedGivens.parityTCircuit a0 w_p (hd.ne_A_wp ⟨0, by omega⟩)
  have hp_mid_in : UnsignedGivens.PhasedPerm cMidIn (fun γ ↦
    UnsignedGivens.omega8 ^ (γ a0 + γ w_p).val) id :=
    fun γ ↦ UnsignedGivens.evolve_parityTCircuit_ket _ _ _ γ
  have hp_mid1 := cleanWrap_perm_of_eq bs.cleanMid hp_mid_in (fun _ ↦ rfl) (fun _ _ _ ↦ rfl)
    (fun β ↦ update_update_self_eq β _ _)
  have hp₂ := hp_mid1.seq (fun γ ↦ UnsignedGivens.evolve_sdagCircuit_ket w_p γ)
  let fan := UnsignedGivens.cnotFanoutReg B w_p rCat (fun j ↦ (hd.ne_cat_wp j).symm)
  let f_fan (β : BitAssignment n) (w : Wire n) : ZMod 2 :=
    if w ∈ Set.range rCat.wires then β w + β w_p else β w
  have hperm_fan : UnsignedGivens.PhasedPerm fan (fun _ ↦ 1) f_fan := fun β ↦ by
    rw [one_smul]; exact UnsignedGivens.evolve_cnotFanoutReg_ket B w_p rCat _ β
  have hfix_fan : ∀ β (w : Wire n), w ∉ rCat.image → f_fan β w = β w := fun β w hw ↦
    ite_eq_right_of_eq_false _ _
      (eq_false fun ⟨j, hj⟩ ↦ hw (QRegister.mem_image rCat w |>.mpr ⟨j, hj⟩))
  obtain ⟨_, _, hp_lo, hfix_lo, _⟩ := streamedPrefixRef_spec hdB rCat rASh rC w_p hd bs d le_rfl
  refine ⟨_, _, hp₁.seq (hp₂.seq (hperm_fan.seq (hp_lo.seq hperm_fan))), fun β w hw ↦ ?_⟩
  dsimp only [Function.comp_apply, id_eq]
  rw [hfix_fan _ w hw,
    hfix_lo _ w fun m _ hm ↦ hw (QRegister.mem_image rCat w |>.mpr ⟨m, hm.symm⟩),
    hfix_fan _ w hw]

theorem realizesCleanRef_compactRawUnsignedPhaseKickDyn [Fintype Var] [DecidableEq Var]
    [NeZero (2 ^ n)] (v : Var) (hdB : d < B) (rCat : QRegister B n)
    (rASh : QRegister (B - d) n) (rC : QRegister B n) (w_p : Wire n)
    (hd : CompactGidneyDisjoint rCat rASh rC w_p) {S_ctrl : Finset (Wire n)}
    (bs : CompactPhaseKickBitSteps hdB rCat rASh rC w_p S_ctrl) :
    UnsignedGivens.RealizesCleanRef (rASh.concat rC hd.disj_A_C)
      (compactRawUnsignedPhaseKickRef hdB rCat rASh rC w_p hd bs)
      (compactRawUnsignedPhaseKickDyn v hdB rCat rASh rC w_p hd bs) := by
  let rWork := rASh.concat rC hd.disj_A_C; let P₀ := rWork.basisOutcomeProjector 0
  obtain ⟨_, _, hp_all, hfix_all⟩ :=
    compactRawUnsignedPhaseKickRef_phasedPerm hdB rCat rASh rC w_p hd bs
  have hclean : (compactRawUnsignedPhaseKickRef hdB rCat rASh rC w_p hd bs).eval.1 * P₀ =
      P₀ * (compactRawUnsignedPhaseKickRef hdB rCat rASh rC w_p hd bs).eval.1 * P₀ := by
    refine UnsignedGivens.cleanProjector_of_phasedPerm_fix rWork _ hp_all fun β idx hidx ↦ ?_
    have hnotin : rWork idx ∉ rCat.image := by
      rw [QRegister.mem_image]; rintro ⟨m, hm⟩
      obtain ⟨i | j, rfl⟩ := finSumFinEquiv.surjective idx
      · exact hd.ne_cat_A m i (by simpa [rWork] using hm)
      · exact hd.ne_cat_C m j (by simpa [rWork] using hm)
    rw [hfix_all β (rWork idx) hnotin, hidx]
  refine realizesCleanRef_of_subspaceStepU rWork _ _ hclean ?_
  have hp_id : UnsignedGivens.PhasedPerm (.identity : Circuit n) (fun _ ↦ 1) id := fun β ↦ by
    rw [one_smul]; exact UnsignedGivens.eval_identity_mulVec (UnsignedGivens.ket β)
  have hWorkZero (idx : Fin ((B - d) + B)) : ZeroOnWire (rWork idx) P₀ := by
    simpa only [ZeroOnWire, Circuit.eval_identity, Submonoid.coe_one, Matrix.one_mul] using
      singleton_proj_zero_mul_eval_mul_work_eq (rWork idx) rWork .identity hp_id (fun _ h ↦ h idx)
  have hA0_P0 (i : Fin (B - d)) : ZeroOnWire (rASh i) P₀ := by
    simpa only [rWork, QRegister.concat_apply_left] using hWorkZero (Fin.castAdd B i)
  have hC0_P0 (m : Fin B) : ZeroOnWire (rC m) P₀ := by
    simpa only [rWork, QRegister.concat_apply_right] using hWorkZero (Fin.natAdd (B - d) m)
  let a0 := rASh ⟨0, by omega⟩
  let cTopIn := Circuit.S a0 ;;ᶜ UnsignedGivens.czCircuit w_p a0 (hd.ne_A_wp ⟨0, by omega⟩).symm
  have hp_top_in : UnsignedGivens.PhasedPerm cTopIn
      (fun γ ↦ Complex.I ^ (γ a0).val * (-1 : ℂ) ^ (γ w_p * γ a0).val) id := fun γ ↦ by
    dsimp only [UnsignedGivens.PhasedPerm, cTopIn, id_eq]
    rw [UnsignedGivens.eval_seq_mulVec, UnsignedGivens.evolve_S_ket, Matrix.mulVec_smul,
      UnsignedGivens.evolve_czCircuit_ket, smul_smul]
  have hsTop := SubspaceStepU_cleanBitStep_wrap (R₀ := P₀) v bs.cleanTop hp_top_in
    (fun _ ↦ rfl) (fun _ _ _ ↦ rfl) (by rw [bs.ancTop]; exact hA0_P0 _) (.circuit cTopIn)
    (SubspaceStepU.of_circuit cTopIn rfl)
  have hp₁ := cleanWrap_perm_of_eq bs.cleanTop hp_top_in (fun _ ↦ rfl) (fun _ _ _ ↦ rfl)
    (fun β ↦ update_update_self_eq β _ _)
  let R₁ := (bs.stepTop.wrapCircuit cTopIn).eval.1 * P₀
  have hA0_R1 (i : Fin (B - d)) :=
    zeroOnWire_mul_of_phasedPerm_fix _ _ hp₁ (fun _ ↦ rfl) (hA0_P0 i)
  have hC0_R1 (m : Fin B) := zeroOnWire_mul_of_phasedPerm_fix _ _ hp₁ (fun _ ↦ rfl) (hC0_P0 m)
  let cMidIn := UnsignedGivens.parityTCircuit a0 w_p (hd.ne_A_wp ⟨0, by omega⟩)
  have hp_mid_in : UnsignedGivens.PhasedPerm cMidIn (fun γ ↦
    UnsignedGivens.omega8 ^ (γ a0 + γ w_p).val) id :=
    fun γ ↦ UnsignedGivens.evolve_parityTCircuit_ket _ _ _ γ
  have hsMid1 := SubspaceStepU_cleanBitStep_wrap (R₀ := R₁) v bs.cleanMid hp_mid_in
    (fun _ ↦ rfl) (fun _ _ _ ↦ rfl) (by rw [bs.ancMid]; exact hA0_R1 _) (.circuit cMidIn)
    (SubspaceStepU.of_circuit cMidIn rfl)
  let cMidFull := bs.stepMid.wrapCircuit cMidIn ;;ᶜ UnsignedGivens.sdagCircuit w_p
  let R₂ := cMidFull.eval.1 * R₁
  have hsMid : SubspaceStepU R₁ R₂
      (.seq (bs.stepMid.wrapDynamic v (.circuit cMidIn)) (.circuit
        (UnsignedGivens.sdagCircuit w_p))) :=
    (hsMid1.seq (SubspaceStepU.of_circuit (UnsignedGivens.sdagCircuit w_p) rfl)).congr rfl
      (by dsimp only [R₂, cMidFull]; simp only [Circuit.eval_seq, Submonoid.coe_mul, mul_assoc])
  have hp_midF := (cleanWrap_perm_of_eq bs.cleanMid hp_mid_in (fun _ ↦ rfl) (fun _ _ _ ↦ rfl)
    (fun β ↦ update_update_self_eq β _ _)).seq (fun γ ↦ UnsignedGivens.evolve_sdagCircuit_ket w_p γ)
  let fan := UnsignedGivens.cnotFanoutReg B w_p rCat (fun j ↦ (hd.ne_cat_wp j).symm)
  have hp_fan : UnsignedGivens.PhasedPerm fan (fun _ ↦ 1)
      (fun β w ↦ if w ∈ Set.range rCat.wires then β w + β w_p else β w) := fun β ↦ by
    rw [one_smul]; exact UnsignedGivens.evolve_cnotFanoutReg_ket B w_p rCat _ β
  let R₃ := fan.eval.1 * R₂
  have hA0_Main (i : Fin (B - d)) : ZeroOnWire (rASh i) R₃ :=
    zeroOnWire_mul_of_phasedPerm_fix _ fan hp_fan
      (fun _ ↦ ite_eq_right_of_eq_false _ _ (eq_false fun ⟨m, hm⟩ ↦ hd.ne_cat_A m i hm))
      (zeroOnWire_mul_of_phasedPerm_fix _ cMidFull hp_midF (fun _ ↦ rfl) (hA0_R1 i))
  have hC0_Main (m : Fin B) (_ : d - d ≤ m.val) : ZeroOnWire (rC m) R₃ :=
    zeroOnWire_mul_of_phasedPerm_fix _ fan hp_fan
      (fun _ ↦ ite_eq_right_of_eq_false _ _ (eq_false fun ⟨k, hk⟩ ↦ hd.ne_cat_C k m hk))
      (zeroOnWire_mul_of_phasedPerm_fix _ cMidFull hp_midF (fun _ ↦ rfl) (hC0_R1 m))
  have hsPref :=
    SubspaceStepU_streamedPrefixDyn v hdB rCat rASh rC w_p hd bs d le_rfl hA0_Main hC0_Main
  refine (hsTop.seq (hsMid.seq ((SubspaceStepU.of_circuit fan rfl).seq
    (hsPref.seq (SubspaceStepU.of_circuit fan rfl))))).congr rfl ?_
  dsimp only [compactRawUnsignedPhaseKickRef, R₃, R₂, R₁, P₀, rWork, cMidFull, fan, cMidIn, cTopIn,
    a0]
  simp only [Circuit.eval_seq, Submonoid.coe_mul, Matrix.mul_assoc]

theorem compactRawUnsignedPhaseKickRef_ket_of_zero (hdB : d < B)
    (rCat : QRegister B n) (rASh : QRegister (B - d) n) (rC : QRegister B n) (w_p : Wire n)
    (hd : CompactGidneyDisjoint rCat rASh rC w_p) {S_ctrl : Finset (Wire n)}
    (bs : CompactPhaseKickBitSteps hdB rCat rASh rC w_p S_ctrl) (β : BitAssignment n)
    (hA0 : ∀ i : Fin (B - d), β (rASh i) = 0) (hC0 : ∀ j : Fin B, β (rC j) = 0) :
    let a_lo := UnsignedGivens.bitSeqVal (bs.bitLo β); let b_mid := (bs.bitMid β).val
    let b_top := (bs.bitTop β).val; let y := UnsignedGivens.localIdx rCat β
    let y_out := UnsignedGivens.signedAddModPerm B a_lo (UnsignedGivens.bitSeqVal_lt _) (β w_p) y
    (compactRawUnsignedPhaseKickRef hdB rCat rASh rC w_p hd bs).eval.1.mulVec
      (UnsignedGivens.ket β) =
      UnsignedGivens.rawPhaseStepVal B a_lo b_mid b_top (β w_p) y •
        UnsignedGivens.ket (UnsignedGivens.writeReg β rCat (basisBits B y_out)) := by
  intro a_lo b_mid b_top y y_out
  let a0 := rASh ⟨0, by omega⟩; have ha0 : β a0 = 0 := hA0 ⟨0, by omega⟩
  let cTopIn := Circuit.S a0 ;;ᶜ UnsignedGivens.czCircuit w_p a0 (hd.ne_A_wp ⟨0, by omega⟩).symm
  have hp_top_in : UnsignedGivens.PhasedPerm cTopIn
      (fun γ ↦ Complex.I ^ (γ a0).val * (-1 : ℂ) ^ (γ w_p * γ a0).val) id := fun γ ↦ by
    dsimp only [UnsignedGivens.PhasedPerm, cTopIn, id_eq]
    rw [UnsignedGivens.eval_seq_mulVec, UnsignedGivens.evolve_S_ket, Matrix.mulVec_smul,
      UnsignedGivens.evolve_czCircuit_ket, smul_smul]
  have hwrap_top := UnsignedGivens.cleanBitStep_wrap_spec bs.cleanTop hp_top_in
    (fun _ ↦ rfl) (fun _ _ _ ↦ rfl)
  have htop_ket : (bs.stepTop.wrapCircuit cTopIn).eval.1.mulVec (UnsignedGivens.ket β) =
      (Complex.I ^ b_top * (-1 : ℂ) ^ ((β w_p).val * b_top)) • UnsignedGivens.ket β := by
    rw [hwrap_top.1 β]; dsimp only [id]; rw [update_update_self_eq]; congr 1
    rw [bs.ancTop, ha0, zero_add, Function.update_self,
      Function.update_of_ne (hd.ne_A_wp ⟨0, by omega⟩).symm]
    rcases UnsignedGivens.zmod2_eq_zero_or_one (β w_p) with hw | hw <;>
      rcases UnsignedGivens.zmod2_eq_zero_or_one (bs.bitTop β) with ht | ht <;> simp [b_top, hw, ht]
  let cMidIn := UnsignedGivens.parityTCircuit a0 w_p (hd.ne_A_wp ⟨0, by omega⟩)
  have hp_mid_in : UnsignedGivens.PhasedPerm cMidIn (fun γ ↦
    UnsignedGivens.omega8 ^ (γ a0 + γ w_p).val) id :=
    fun γ ↦ UnsignedGivens.evolve_parityTCircuit_ket _ _ _ γ
  have hwrap_mid := UnsignedGivens.cleanBitStep_wrap_spec bs.cleanMid hp_mid_in
    (fun _ ↦ rfl) (fun _ _ _ ↦ rfl)
  have hmid1_ket : (bs.stepMid.wrapCircuit cMidIn).eval.1.mulVec (UnsignedGivens.ket β) =
      (UnsignedGivens.omega8 ^ ((((b_mid : ℕ) : ZMod 2) + β w_p).val)) • UnsignedGivens.ket β := by
    rw [hwrap_mid.1 β]; dsimp only [id]; rw [update_update_self_eq]; congr 1
    rw [bs.ancMid, ha0, zero_add, Function.update_self,
      Function.update_of_ne (hd.ne_A_wp ⟨0, by omega⟩).symm,
      UnsignedGivens.zmod2_eq_natCast_mod_two (bs.bitMid β)]
  let fan := UnsignedGivens.cnotFanoutReg B w_p rCat (fun j ↦ (hd.ne_cat_wp j).symm)
  let β_fan : BitAssignment n := fun w ↦ if w ∈ Set.range rCat.wires then β w + β w_p else β w
  let yc := if β w_p = 0 then y.val else 2 ^ B - 1 - y.val
  have hyc_val : UnsignedGivens.regVal rCat β_fan = yc := by
    simpa [β_fan, yc, y,
      UnsignedGivens.regVal] using UnsignedGivens.regVal_after_fanout rCat β (β w_p)
  obtain ⟨_, f_lo, hperm_lo, hfix_lo, hval_lo⟩ :=
    streamedPrefixRef_spec hdB rCat rASh rC w_p hd bs d le_rfl
  have hcat_fan (k : Fin B) : β_fan (rCat k) = ((yc / 2 ^ k.val % 2 : ℕ) : ZMod 2) := by
    rw [← hyc_val]; exact UnsignedGivens.reg_bit_eq_natCast_regVal rCat β_fan k
  have hA_fan (i : Fin (B - d)) : β_fan (rASh i) = 0 := by
    simp only [β_fan, show rASh i ∉ Set.range rCat.wires from fun ⟨j, hj⟩ ↦ hd.ne_cat_A j i hj,
      ↓reduceIte, hA0 i]
  have hlo_fan (k : Fin B) (_ : d - d ≤ k.val) :
      bs.bitLo β_fan k = ((a_lo / 2 ^ k.val % 2 : ℕ) : ZMod 2) := by
    have hbv : bs.bitLo β_fan k = bs.bitLo β k :=
      (bs.cleanLo k).bitVal_congr β_fan β fun w hw ↦ by
        have hnot : w ∉ Set.range rCat.wires := fun ⟨j, hj⟩ ↦
          Finset.disjoint_left.mp bs.disj_ctrl_cat hw (QRegister.mem_image rCat _ |>.mpr ⟨j, hj⟩)
        simp only [β_fan, hnot, ↓reduceIte]
    rw [hbv]; exact (UnsignedGivens.bitSeqVal_div_pow_mod_two (bs.bitLo β) k).symm
  have hC_fan (k : Fin B) : β_fan (rC k) = 0 := by
    simp only [β_fan, show rC k ∉ Set.range rCat.wires from fun ⟨j, hj⟩ ↦ hd.ne_cat_C j k hj,
      ↓reduceIte, hC0 k]
  have hv_lo := hval_lo β_fan yc a_lo (hyc_val ▸ UnsignedGivens.regVal_lt rCat β_fan)
    (UnsignedGivens.bitSeqVal_lt _) (fun k _ ↦ hcat_fan k) hA_fan hlo_fan (fun k _ ↦ hC_fan k)
    (fun h0 ↦ absurd h0 (by omega))
  have hwp_fan : β_fan w_p = β w_p := by
    simp only [β_fan, show w_p ∉ Set.range rCat.wires from fun ⟨j, hj⟩ ↦ hd.ne_cat_wp j hj,
      ↓reduceIte]
  have hfan2 : fan.eval.1.mulVec (UnsignedGivens.ket (f_lo β_fan)) =
      UnsignedGivens.ket (UnsignedGivens.writeReg β rCat (basisBits B y_out)) := by
    rw [UnsignedGivens.evolve_cnotFanoutReg_ket]; apply congrArg UnsignedGivens.ket; funext w
    rw [hfix_lo β_fan w_p fun j _ hj ↦ hd.ne_cat_wp j hj.symm, hwp_fan]
    by_cases hw : w ∈ Set.range rCat.wires
    · obtain ⟨k, rfl⟩ := hw
      have hdvd : 2 ^ (k.val + 1) ∣ 2 ^ B := Nat.pow_dvd_pow 2 k.isLt
      have hdm (m : ℕ) : m / 2 ^ k.val % 2 = (m % 2 ^ (k.val + 1)) / 2 ^ k.val := by
        rw [pow_succ, Nat.mod_mul_right_div_self]
      simp only [show rCat k ∈ Set.range rCat.wires from ⟨k, rfl⟩, ↓reduceIte,
        UnsignedGivens.writeReg_apply_reg, hv_lo.2 k (by omega)]
      rcases UnsignedGivens.zmod2_eq_zero_or_one (β w_p) with hwp0 | hwp1
      · simp only [hwp0, add_zero]
        have hyo : y_out.val = (y.val + a_lo) % 2 ^ B := by
          simp [y_out, UnsignedGivens.signedAddModPerm, hwp0]
        rw [basisBits_eq_div_mod, hyo]; simp only [yc, hwp0, ↓reduceIte]; congr 1
        rw [hdm ((y.val + a_lo) % 2 ^ B), Nat.mod_mod_of_dvd _ hdvd, ← hdm]
      · simp only [hwp1]; have h10 : (1 : ZMod 2) ≠ 0 := by decide
        have hyo : y_out.val = 2 ^ B - 1 - ((2 ^ B - 1 - y.val + a_lo) % 2 ^ B) := by
          simp [y_out, UnsignedGivens.signedAddModPerm, hwp1, h10]
        rw [basisBits_eq_div_mod, hyo]
        set ysum := (yc + a_lo) % 2 ^ B
        have hmod_bit : (yc + a_lo) / 2 ^ k.val % 2 = ysum / 2 ^ k.val % 2 := by
          rw [hdm (yc + a_lo), hdm ysum, Nat.mod_mod_of_dvd _ hdvd]
        rw [hmod_bit]
        have hoc := UnsignedGivens.onesComp_div_pow_mod_two k.isLt
          (Nat.mod_lt (yc + a_lo) (Nat.two_pow_pos B))
        have h_xor : (((ysum / 2 ^ k.val % 2 : ℕ) : ZMod 2) + 1) =
            ((1 - ysum / 2 ^ k.val % 2 : ℕ) : ZMod 2) := by
          rcases Nat.mod_two_eq_zero_or_one (ysum / 2 ^ k.val) with h | h <;> simp [h]
        rw [h_xor]; have hyc_def : yc = 2 ^ B - 1 - y.val := by dsimp [yc]; simp [hwp1, h10]
        dsimp [ysum] at hoc ⊢; rw [hyc_def] at hoc; rw [hoc, hyc_def]
    · simp only [hw, ↓reduceIte, UnsignedGivens.writeReg_apply_of_not_mem _ _ _ _ hw]
      rw [hfix_lo β_fan w fun j _ hj ↦ hw ⟨j, hj.symm⟩]; simp only [β_fan, hw, ↓reduceIte]
  dsimp only [compactRawUnsignedPhaseKickRef]; simp only [UnsignedGivens.eval_seq_mulVec]
  rw [htop_ket]; simp only [Matrix.mulVec_smul]; rw [hmid1_ket]; simp only [Matrix.mulVec_smul]
  rw [UnsignedGivens.evolve_sdagCircuit_ket]; simp only [Matrix.mulVec_smul]
  rw [UnsignedGivens.evolve_cnotFanoutReg_ket B w_p rCat _ β, hperm_lo β_fan]
  simp only [Matrix.mulVec_smul]
  rw [hfan2, hv_lo.1, hwp_fan]; simp only [smul_smul]; congr 1
  dsimp [UnsignedGivens.rawPhaseStepVal, yc]; ring

end CompactKickBridge

/-! ## Section 2: Compact Affine `Lac = 2` Cascade (`23 - d` Work Wires) -/

section CompactAffineCascade

open Solution.CompactStepFast176Select.UnsignedGivens (affineBilinearBitStep
  extendHot0 isCleanBitStep_affineBilinearFormula affinePlaneEffK affineApexEffK
  affineUnsignedBilinearLac2CascadeCtrlUnitary clearHot0Circuit evolve_clearHot0Circuit_ket
  clearHot0Circuit_eval_mul_self clearHot0_zero_of_isOneHot)
open Solution.CompactStepFast176Select.OneHotMux
  (clearHot0Circuit_conj_muxCtrlUnitary_eq)

theorem signedAddModPerm_congr {B a₁ a₂ : ℕ} {h₁ : a₁ < 2 ^ B} {h₂ : a₂ < 2 ^ B} (h : a₁ = a₂) :
    UnsignedGivens.signedAddModPerm B a₁ h₁ = UnsignedGivens.signedAddModPerm B a₂ h₂ := by
  subst h; rfl

/-- `CompactPhaseKickBitSteps` reading `(idxTop, idxMid, 0 .. B - 1)` from `row` onto `rASh`. -/
def compactAffineTableBitSteps {n B d G' : ℕ} (hdB : d < B) (idxTop idxMid : ℕ)
    (row : Fin (G' + 1) → Bool → ℕ) (u w_v : Wire n) (rHot' : QRegister G' n)
    (rCat : QRegister B n) (rASh : QRegister (B - d) n) (rC : QRegister B n) (w_p : Wire n)
    (huv : u ≠ w_v) (hh_u : ∀ g, rHot' g ≠ u) (hh_v : ∀ g, rHot' g ≠ w_v)
    (hu_wp : u ≠ w_p) (hv_wp : w_v ≠ w_p) (hh_wp : ∀ g, rHot' g ≠ w_p)
    (hu_cat : ∀ i, u ≠ rCat i) (hv_cat : ∀ i, w_v ≠ rCat i) (hh_cat : ∀ g i, rHot' g ≠ rCat i)
    (hu_A : ∀ i, u ≠ rASh i) (hv_A : ∀ i, w_v ≠ rASh i) (hh_A : ∀ g i, rHot' g ≠ rASh i)
    (hu_C : ∀ i, u ≠ rC i) (hv_C : ∀ i, w_v ≠ rC i) (hh_C : ∀ g i, rHot' g ≠ rC i) :
    CompactPhaseKickBitSteps hdB rCat rASh rC w_p (insert u (insert w_v rHot'.image)) :=
  let a0 := rASh ⟨0, by omega⟩
  have hu_anc (j : Fin B) : u ≠ ancSh d hdB rASh j := by dsimp [ancSh]; split_ifs <;> exact hu_A _
  have hv_anc (j : Fin B) : w_v ≠ ancSh d hdB rASh j := by
    dsimp [ancSh]; split_ifs <;> exact hv_A _
  have hh_anc (j : Fin B) (g : Fin G') : rHot' g ≠ ancSh d hdB rASh j := by
    dsimp [ancSh]; split_ifs <;> exact hh_A g _
  { stepTop := affineBilinearBitStep G' u w_v rHot' (UnsignedGivens.rowBitMask row false idxTop)
      (UnsignedGivens.rowBitMask row true idxTop) a0 huv (hu_A _) (hv_A _) hh_u hh_v (fun g ↦
        hh_A g _)
    stepMid := affineBilinearBitStep G' u w_v rHot' (UnsignedGivens.rowBitMask row false idxMid)
      (UnsignedGivens.rowBitMask row true idxMid) a0 huv (hu_A _) (hv_A _) hh_u hh_v (fun g ↦
        hh_A g _)
    stepLo := fun j ↦
      affineBilinearBitStep G' u w_v rHot' (UnsignedGivens.rowBitMask row false j.val)
      (UnsignedGivens.rowBitMask row true j.val) (ancSh d hdB rASh j) huv (hu_anc j)
        (hv_anc j) hh_u hh_v
      (hh_anc j)
    bitTop := fun β ↦ UnsignedGivens.bilinearBitFormula (β u) (β w_v)
      (extendHot0 (fun g ↦ β (rHot' g))) (UnsignedGivens.rowBitMask row false idxTop)
      (UnsignedGivens.rowBitMask row true idxTop)
    bitMid := fun β ↦ UnsignedGivens.bilinearBitFormula (β u) (β w_v)
      (extendHot0 (fun g ↦ β (rHot' g))) (UnsignedGivens.rowBitMask row false idxMid)
      (UnsignedGivens.rowBitMask row true idxMid)
    bitLo := fun β j ↦ UnsignedGivens.bilinearBitFormula (β u) (β w_v)
      (extendHot0 (fun g ↦ β (rHot' g))) (UnsignedGivens.rowBitMask row false j.val)
      (UnsignedGivens.rowBitMask row true j.val)
    ancTop := rfl, ancMid := rfl, ancLo := fun _ ↦ rfl
    cleanTop := isCleanBitStep_affineBilinearFormula _ _ _ _ _ _ _ _ _ _ _ _ _
    cleanMid := isCleanBitStep_affineBilinearFormula _ _ _ _ _ _ _ _ _ _ _ _ _
    cleanLo := fun _ ↦ isCleanBitStep_affineBilinearFormula _ _ _ _ _ _ _ _ _ _ _ _ _
    disj_ctrl_wp := by
      simp only [Finset.mem_insert, QRegister.mem_image, not_or, not_exists]
      exact ⟨hu_wp.symm, hv_wp.symm, fun g hg ↦ hh_wp g hg⟩
    disj_ctrl_cat := by
      rw [Finset.disjoint_insert_left, Finset.disjoint_insert_left, QRegister.mem_image,
        QRegister.mem_image]
      refine ⟨fun ⟨i, hi⟩ ↦ hu_cat i hi.symm, fun ⟨i, hi⟩ ↦ hv_cat i hi.symm,
        Finset.disjoint_left.mpr fun q hq hc ↦ ?_⟩
      obtain ⟨g, rfl⟩ := QRegister.mem_image rHot' q |>.mp hq
      obtain ⟨i, hi⟩ := QRegister.mem_image rCat _ |>.mp hc; exact hh_cat g i hi.symm
    disj_ctrl_A := by
      rw [Finset.disjoint_insert_left, Finset.disjoint_insert_left, QRegister.mem_image,
        QRegister.mem_image]
      refine ⟨fun ⟨i, hi⟩ ↦ hu_A i hi.symm, fun ⟨i, hi⟩ ↦ hv_A i hi.symm,
        Finset.disjoint_left.mpr fun q hq ha ↦ ?_⟩
      obtain ⟨g, rfl⟩ := QRegister.mem_image rHot' q |>.mp hq
      obtain ⟨i, hi⟩ := QRegister.mem_image rASh _ |>.mp ha; exact hh_A g i hi.symm
    disj_ctrl_C := by
      rw [Finset.disjoint_insert_left, Finset.disjoint_insert_left, QRegister.mem_image,
        QRegister.mem_image]
      refine ⟨fun ⟨i, hi⟩ ↦ hu_C i hi.symm, fun ⟨i, hi⟩ ↦ hv_C i hi.symm,
        Finset.disjoint_left.mpr fun q hq hc ↦ ?_⟩
      obtain ⟨g, rfl⟩ := QRegister.mem_image rHot' q |>.mp hq
      obtain ⟨i, hi⟩ := QRegister.mem_image rC _ |>.mp hc; exact hh_C g i hi.symm }

/-- Bundled wire-disjointness hypotheses for `compactAffineLac2KickDyn`. -/
structure CompactAffineKickDisjoint {n B d G' : ℕ} (w_ctrl sub w_v : Wire n)
    (rHot' : QRegister G' n) (rCat : QRegister B n) (rASh : QRegister (B - d) n)
    (rC : QRegister B n) (w_p : Wire n) : Prop where
  hcs : w_ctrl ≠ sub
  hcv : w_ctrl ≠ w_v
  hsv : sub ≠ w_v
  hh_ctrl : ∀ g, rHot' g ≠ w_ctrl
  hh_v : ∀ g, rHot' g ≠ w_v
  hctrl_wp : w_ctrl ≠ w_p
  hv_wp : w_v ≠ w_p
  hh_wp : ∀ g, rHot' g ≠ w_p
  hctrl_cat : ∀ i, w_ctrl ≠ rCat i
  hv_cat : ∀ i, w_v ≠ rCat i
  hh_cat : ∀ g i, rHot' g ≠ rCat i
  hsub_cat : ∀ i, sub ≠ rCat i
  hctrl_A : ∀ i, w_ctrl ≠ rASh i
  hv_A : ∀ i, w_v ≠ rASh i
  hh_A : ∀ g i, rHot' g ≠ rASh i
  hsub_A : ∀ i, sub ≠ rASh i
  hctrl_C : ∀ i, w_ctrl ≠ rC i
  hv_C : ∀ i, w_v ≠ rC i
  hh_C : ∀ g i, rHot' g ≠ rC i
  hsub_C : ∀ i, sub ≠ rC i

/-- Compact `(B + 2)`-bit `Lac = 2` affine phase-kick circuit (`8 * B + 14 + 4 * d` `T`). -/
def compactAffineLac2KickDyn {Var : Type} {n B d G' : ℕ} (v : Var) (hdB : d < B)
    (idxTop idxMid : ℕ) (row : Fin (G' + 1) → Bool → ℕ) (w_ctrl sub w_v : Wire n)
    (rHot' : QRegister G' n) (rCat : QRegister B n) (rASh : QRegister (B - d) n)
    (rC : QRegister B n) (w_p : Wire n) (hd : CompactGidneyDisjoint rCat rASh rC w_p)
    (hdk : CompactAffineKickDisjoint w_ctrl sub w_v rHot' rCat rASh rC w_p) :
    DynamicCircuit Var n :=
  let bs := compactAffineTableBitSteps hdB idxTop idxMid row w_ctrl w_v rHot' rCat rASh rC w_p
    hdk.hcv hdk.hh_ctrl hdk.hh_v hdk.hctrl_wp hdk.hv_wp hdk.hh_wp hdk.hctrl_cat hdk.hv_cat
    hdk.hh_cat hdk.hctrl_A hdk.hv_A hdk.hh_A hdk.hctrl_C hdk.hv_C hdk.hh_C
  (UnsignedGivens.inPlaceUVStep w_ctrl sub w_v hdk.hcs hdk.hcv hdk.hsv).wrapDynamic v
    (compactRawUnsignedPhaseKickDyn v hdB rCat rASh rC w_p hd bs)

/-- Reference Toffoli circuit matched by `compactAffineLac2KickDyn`. -/
def compactAffineLac2KickRef {n B d G' : ℕ} (hdB : d < B) (idxTop idxMid : ℕ)
    (row : Fin (G' + 1) → Bool → ℕ) (w_ctrl sub w_v : Wire n) (rHot' : QRegister G' n)
    (rCat : QRegister B n) (rASh : QRegister (B - d) n) (rC : QRegister B n) (w_p : Wire n)
    (hd : CompactGidneyDisjoint rCat rASh rC w_p)
    (hdk : CompactAffineKickDisjoint w_ctrl sub w_v rHot' rCat rASh rC w_p) : Circuit n :=
  let bs := compactAffineTableBitSteps hdB idxTop idxMid row w_ctrl w_v rHot' rCat rASh rC w_p
    hdk.hcv hdk.hh_ctrl hdk.hh_v hdk.hctrl_wp hdk.hv_wp hdk.hh_wp hdk.hctrl_cat hdk.hv_cat
    hdk.hh_cat hdk.hctrl_A hdk.hv_A hdk.hh_A hdk.hctrl_C hdk.hv_C hdk.hh_C
  (UnsignedGivens.inPlaceUVStep w_ctrl sub w_v hdk.hcs hdk.hcv hdk.hsv).wrapCircuit
    (compactRawUnsignedPhaseKickRef hdB rCat rASh rC w_p hd bs)

@[simp] theorem count_compactAffineLac2KickDyn_toff {Var : Type} {n B d G' : ℕ} (v : Var)
    (hdB : d < B) (idxTop idxMid : ℕ) (row : Fin (G' + 1) → Bool → ℕ) (w_ctrl sub w_v : Wire n)
    (rHot' : QRegister G' n) (rCat : QRegister B n) (rASh : QRegister (B - d) n)
    (rC : QRegister B n) (w_p : Wire n) (hd : CompactGidneyDisjoint rCat rASh rC w_p)
    (hdk : CompactAffineKickDisjoint w_ctrl sub w_v rHot' rCat rASh rC w_p) :
    (compactAffineLac2KickDyn v hdB idxTop idxMid row w_ctrl sub w_v rHot' rCat rASh rC w_p hd
      hdk).count .TOFF = 0 := by
  unfold compactAffineLac2KickDyn
  rw [UnsignedGivens.PhasedStep.count_wrapDynamic_toff _ _ _
    (UnsignedGivens.isCliffordWrapper_inPlaceUVStep _ _ _ _ _ _)]
  exact count_compactRawUnsignedPhaseKickDyn_toff _ _ _ _ _ _ _ _

@[simp] theorem count_compactAffineLac2KickDyn_t {Var : Type} {n B d G' : ℕ} (v : Var)
    (hdB : d < B) (idxTop idxMid : ℕ) (row : Fin (G' + 1) → Bool → ℕ) (w_ctrl sub w_v : Wire n)
    (rHot' : QRegister G' n) (rCat : QRegister B n) (rASh : QRegister (B - d) n)
    (rC : QRegister B n) (w_p : Wire n) (hd : CompactGidneyDisjoint rCat rASh rC w_p)
    (hdk : CompactAffineKickDisjoint w_ctrl sub w_v rHot' rCat rASh rC w_p) :
    (compactAffineLac2KickDyn v hdB idxTop idxMid row w_ctrl sub w_v rHot' rCat rASh rC w_p hd
      hdk).count .T = 8 * B + 14 + 4 * d := by
  unfold compactAffineLac2KickDyn
  rw [UnsignedGivens.PhasedStep.count_wrapDynamic_t _ _ _
    (UnsignedGivens.isCliffordWrapper_inPlaceUVStep _ _ _ _ _ _),
      count_compactRawUnsignedPhaseKickDyn_t]
  omega

theorem compactAffineLac2KickRef_phasedPerm {n B d G' : ℕ} (hdB : d < B) (idxTop idxMid : ℕ)
    (row : Fin (G' + 1) → Bool → ℕ) (w_ctrl sub w_v : Wire n) (rHot' : QRegister G' n)
    (rCat : QRegister B n) (rASh : QRegister (B - d) n) (rC : QRegister B n) (w_p : Wire n)
    (hd : CompactGidneyDisjoint rCat rASh rC w_p)
    (hdk : CompactAffineKickDisjoint w_ctrl sub w_v rHot' rCat rASh rC w_p) :
    ∃ (φ : BitAssignment n → ℂ) (f : BitAssignment n → BitAssignment n),
      UnsignedGivens.PhasedPerm
        (compactAffineLac2KickRef hdB idxTop idxMid row w_ctrl sub w_v rHot' rCat rASh rC w_p hd
          hdk)
        φ f ∧ ∀ β (w : Wire n), w ∉ rCat.image → f β w = β w := by
  let bs := compactAffineTableBitSteps hdB idxTop idxMid row w_ctrl w_v rHot' rCat rASh rC w_p
    hdk.hcv hdk.hh_ctrl hdk.hh_v hdk.hctrl_wp hdk.hv_wp hdk.hh_wp hdk.hctrl_cat hdk.hv_cat
    hdk.hh_cat hdk.hctrl_A hdk.hv_A hdk.hh_A hdk.hctrl_C hdk.hv_C hdk.hh_C
  obtain ⟨_, _, hp_in, hfix_in⟩ :=
    compactRawUnsignedPhaseKickRef_phasedPerm hdB rCat rASh rC w_p hd bs
  have hc_not : w_ctrl ∉ rCat.image := fun h ↦
    let ⟨i, hi⟩ := QRegister.mem_image rCat _ |>.mp h; hdk.hctrl_cat i hi.symm
  have hs_not : sub ∉ rCat.image := fun h ↦
    let ⟨i, hi⟩ := QRegister.mem_image rCat _ |>.mp h; hdk.hsub_cat i hi.symm
  have hv_not : w_v ∉ rCat.image := fun h ↦
    let ⟨i, hi⟩ := QRegister.mem_image rCat _ |>.mp h; hdk.hv_cat i hi.symm
  have hwrap := UnsignedGivens.inPlaceUVStep_wrap_spec w_ctrl sub w_v hdk.hcs hdk.hcv hdk.hsv hp_in
    (fun β ↦ hfix_in β w_ctrl hc_not) (fun β ↦ hfix_in β sub hs_not) (fun β ↦ hfix_in β w_v hv_not)
  refine ⟨_, _, hwrap.1, fun β w hw ↦ ?_⟩
  by_cases hwc : w = w_ctrl
  · subst w; exact hwrap.2.1 β
  · by_cases hwv : w = w_v
    · subst w; dsimp only; rw [hfix_in _ w_ctrl hc_not, hfix_in _ w_v hv_not, hfix_in _ sub hs_not]
      simp only [Function.update_self, Function.update_of_ne hdk.hcv.symm,
        Function.update_of_ne hdk.hcs.symm, Function.update_of_ne hdk.hsv,
        UnsignedGivens.zmod2_add_cancel_right]
    · dsimp only; rw [Function.update_of_ne hwv, Function.update_of_ne hwc, hfix_in _ w hw]
      simp only [Function.update_of_ne hwc, Function.update_of_ne hwv]

theorem realizesCleanRef_compactAffineLac2KickDyn_widen
    {Var : Type} [Fintype Var] [DecidableEq Var] {n B d G' m : ℕ} [NeZero (2 ^ n)]
    (v : Var) (hdB : d < B) (idxTop idxMid : ℕ) (row : Fin (G' + 1) → Bool → ℕ)
    (w_ctrl sub w_v : Wire n) (rHot' : QRegister G' n) (rCat : QRegister B n)
    (rASh : QRegister (B - d) n) (rC : QRegister B n) (w_p : Wire n)
    (hd : CompactGidneyDisjoint rCat rASh rC w_p)
    (hdk : CompactAffineKickDisjoint w_ctrl sub w_v rHot' rCat rASh rC w_p)
    (rWork : QRegister m n) (hv_mem : w_v ∈ rWork.image) (hA_sub : rASh.image ⊆ rWork.image)
    (hC_sub : rC.image ⊆ rWork.image) (hcat_work : ∀ (i : Fin B) (j : Fin m), rCat i ≠ rWork j) :
    UnsignedGivens.RealizesCleanRef rWork
      (compactAffineLac2KickRef hdB idxTop idxMid row w_ctrl sub w_v rHot' rCat rASh rC w_p hd hdk)
      (compactAffineLac2KickDyn v hdB idxTop idxMid row w_ctrl sub w_v rHot' rCat rASh rC w_p hd
        hdk) := by
  let bs := compactAffineTableBitSteps hdB idxTop idxMid row w_ctrl w_v rHot' rCat rASh rC w_p
    hdk.hcv hdk.hh_ctrl hdk.hh_v hdk.hctrl_wp hdk.hv_wp hdk.hh_wp hdk.hctrl_cat hdk.hv_cat
    hdk.hh_cat hdk.hctrl_A hdk.hv_A hdk.hh_A hdk.hctrl_C hdk.hv_C hdk.hh_C
  let sUV := UnsignedGivens.inPlaceUVStep w_ctrl sub w_v hdk.hcs hdk.hcv hdk.hsv
  let rRest := rASh.concat rC hd.disj_A_C
  obtain ⟨_, _, hp_in, hfix_in⟩ :=
    compactRawUnsignedPhaseKickRef_phasedPerm hdB rCat rASh rC w_p hd bs
  have hwrap_uv :=
    UnsignedGivens.inPlaceUVStep_wrap_spec w_ctrl sub w_v hdk.hcs hdk.hcv hdk.hsv hp_in
    (fun β ↦ hfix_in β w_ctrl fun h ↦
      let ⟨i, hi⟩ := QRegister.mem_image rCat _ |>.mp h; hdk.hctrl_cat i hi.symm)
    (fun β ↦ hfix_in β sub fun h ↦
      let ⟨i, hi⟩ := QRegister.mem_image rCat _ |>.mp h; hdk.hsub_cat i hi.symm)
    (fun β ↦ hfix_in β w_v fun h ↦
      let ⟨i, hi⟩ := QRegister.mem_image rCat _ |>.mp h; hdk.hv_cat i hi.symm)
  obtain ⟨_, _, hp_all, hfix_all⟩ := compactAffineLac2KickRef_phasedPerm hdB idxTop idxMid row
    w_ctrl sub w_v rHot' rCat rASh rC w_p hd hdk
  have hv_nr : w_v ∉ rRest.image := by
    rw [UnsignedGivens.image_concat_eq, Finset.mem_union, QRegister.mem_image, QRegister.mem_image]
    rintro (⟨i, hi⟩ | ⟨i, hi⟩)
    · exact hdk.hv_A i hi.symm
    · exact hdk.hv_C i hi.symm
  have hc_nr : sUV.c₁ ∉ rRest.image := by
    change w_ctrl ∉ rRest.image
    rw [UnsignedGivens.image_concat_eq, Finset.mem_union, QRegister.mem_image, QRegister.mem_image]
    rintro (⟨i, hi⟩ | ⟨i, hi⟩)
    · exact hdk.hctrl_A i hi.symm
    · exact hdk.hctrl_C i hi.symm
  have hs_nr : sUV.c₂ ∉ rRest.image := by
    change sub ∉ rRest.image
    rw [UnsignedGivens.image_concat_eq, Finset.mem_union, QRegister.mem_image, QRegister.mem_image]
    rintro (⟨i, hi⟩ | ⟨i, hi⟩)
    · exact hdk.hsub_A i hi.symm
    · exact hdk.hsub_C i hi.symm
  have hd_anc : (QRegister.singleton sUV.anc).DisjointWires rRest := by
    rw [UnsignedGivens.disjointWires_iff_disjoint_image, QRegister.image_singleton,
      Finset.disjoint_singleton_left]; exact hv_nr
  have hmid_rest : Disjoint sUV.midPre.support rRest.image :=
    Finset.disjoint_left.mpr fun q hq ↦ by
    simp only [sUV, UnsignedGivens.inPlaceUVStep, Circuit.support_cnot, Finset.mem_insert,
      Finset.mem_singleton] at hq
    rcases hq with rfl | rfl
    · exact hv_nr
    · exact hc_nr
  let rTotal := (QRegister.singleton sUV.anc).concat rRest hd_anc
  have hsub_tot : rTotal.image ⊆ rWork.image := by
    rw [UnsignedGivens.image_concat_eq, QRegister.image_singleton, UnsignedGivens.image_concat_eq,
      Finset.union_subset_iff, Finset.singleton_subset_iff, Finset.union_subset_iff]
    exact ⟨hv_mem, hA_sub, hC_sub⟩
  have hcl_tot := UnsignedGivens.cleanProjector_of_phasedPerm_fix rTotal _ hp_all fun β idx hidx ↦
      by
    obtain ⟨j, hj⟩ := QRegister.mem_image rWork _ |>.mp
      (hsub_tot (QRegister.mem_image rTotal _ |>.mpr ⟨idx, rfl⟩))
    rw [hfix_all β (rTotal idx) (by rw [← hj, QRegister.mem_image]; rintro ⟨i, hi⟩
                                    exact hcat_work i j hi), hidx]
  have hcl_wrk := UnsignedGivens.cleanProjector_of_phasedPerm_fix rWork _ hp_all fun β j hj ↦ by
    rw [hfix_all β (rWork j) (by rw [QRegister.mem_image]; rintro ⟨i, hi⟩
                                 exact hcat_work i j hi), hj]
  exact (UnsignedGivens.RealizesCleanRef.wrapDynamic v sUV _ _ rRest hd_anc
    (by simp [sUV, UnsignedGivens.inPlaceUVStep]) (by simp [sUV,
      UnsignedGivens.inPlaceUVStep]) hc_nr hs_nr hmid_rest
    hwrap_uv.2.2.2.2.2
      (realizesCleanRef_compactRawUnsignedPhaseKickDyn v hdB rCat rASh rC w_p hd bs)
    hcl_tot).widenImage hsub_tot hcl_wrk

theorem compactAffineLac2KickRef_ket_of_zero {n B d G' : ℕ} (hdB : d < B) (idxTop idxMid : ℕ)
    (row : Fin (G' + 1) → Bool → ℕ) (w_ctrl sub w_v : Wire n) (rHot' : QRegister G' n)
    (rCat : QRegister B n) (rASh : QRegister (B - d) n) (rC : QRegister B n) (w_p : Wire n)
    (hd : CompactGidneyDisjoint rCat rASh rC w_p)
    (hdk : CompactAffineKickDisjoint w_ctrl sub w_v rHot' rCat rASh rC w_p)
    (β : BitAssignment n) (hv0 : β w_v = 0)
    (hA0 : ∀ i : Fin (B - d), β (rASh i) = 0) (hC0 : ∀ j : Fin B, β (rC j) = 0) :
    let hbits := extendHot0 (fun g : Fin G' ↦ β (rHot' g))
    let a_lo := UnsignedGivens.bilinearRowLo B row (β w_ctrl) (β sub) hbits
    let b_mid := UnsignedGivens.bilinearRowBit idxMid row (β w_ctrl) (β sub) hbits
    let b_top := UnsignedGivens.bilinearRowBit idxTop row (β w_ctrl) (β sub) hbits
    let y := UnsignedGivens.localIdx rCat β
    let y_out := UnsignedGivens.signedAddModPerm B a_lo
      (UnsignedGivens.bilinearRowLo_lt B row (β w_ctrl) (β sub) hbits) (β w_p) y
    (compactAffineLac2KickRef hdB idxTop idxMid row w_ctrl sub w_v rHot' rCat rASh rC w_p hd
      hdk).eval.1.mulVec (UnsignedGivens.ket β) =
      UnsignedGivens.rawPhaseStepVal B a_lo b_mid b_top (β w_p) y •
        UnsignedGivens.ket (UnsignedGivens.writeReg β rCat (basisBits B y_out)) := by
  intro hbits a_lo b_mid b_top y y_out
  let bs := compactAffineTableBitSteps hdB idxTop idxMid row w_ctrl w_v rHot' rCat rASh rC w_p
    hdk.hcv hdk.hh_ctrl hdk.hh_v hdk.hctrl_wp hdk.hv_wp hdk.hh_wp hdk.hctrl_cat hdk.hv_cat
    hdk.hh_cat hdk.hctrl_A hdk.hv_A hdk.hh_A hdk.hctrl_C hdk.hv_C hdk.hh_C
  let v_val := β w_ctrl * β sub; let u_val := β w_ctrl * (1 + β sub)
  let β₁ := Function.update (Function.update β w_v v_val) w_ctrl u_val
  have hβ₁_A0 (i : Fin (B - d)) : β₁ (rASh i) = 0 := by
    dsimp [β₁]; rw [Function.update_of_ne (hdk.hctrl_A i).symm,
      Function.update_of_ne (hdk.hv_A i).symm, hA0 i]
  have hβ₁_C0 (j : Fin B) : β₁ (rC j) = 0 := by
    dsimp [β₁]; rw [Function.update_of_ne (hdk.hctrl_C j).symm,
      Function.update_of_ne (hdk.hv_C j).symm, hC0 j]
  have hβ₁_wp : β₁ w_p = β w_p := by
    dsimp [β₁]; rw [Function.update_of_ne hdk.hctrl_wp.symm, Function.update_of_ne hdk.hv_wp.symm]
  have hβ₁_cat : UnsignedGivens.localIdx rCat β₁ = y := by
    apply (basisBits B).injective; funext i
    rw [UnsignedGivens.basisBits_symm_eq, UnsignedGivens.basisBits_symm_eq]; dsimp [β₁]
    rw [Function.update_of_ne (hdk.hctrl_cat i).symm, Function.update_of_ne (hdk.hv_cat i).symm]
  have hβ₁_u : β₁ w_ctrl = u_val := Function.update_self _ _ _
  have hβ₁_v : β₁ w_v = v_val := by
    dsimp [β₁]; rw [Function.update_of_ne hdk.hcv.symm, Function.update_self]
  have hβ₁_hot : extendHot0 (fun g : Fin G' ↦ β₁ (rHot' g)) = hbits :=
    congrArg extendHot0 (funext fun g ↦ by
      dsimp [β₁]; rw [Function.update_of_ne (hdk.hh_ctrl g), Function.update_of_ne (hdk.hh_v g)])
  have hk_in := compactRawUnsignedPhaseKickRef_ket_of_zero hdB rCat rASh rC w_p hd bs β₁ hβ₁_A0
    hβ₁_C0
  dsimp only at hk_in
  have hlo_eq : UnsignedGivens.bitSeqVal (bs.bitLo β₁) = a_lo := by
    dsimp [bs, compactAffineTableBitSteps, a_lo, UnsignedGivens.bilinearRowLo]; congr 1; funext j
    rw [hβ₁_u, hβ₁_v, hβ₁_hot]
  have hmid_eq : (bs.bitMid β₁).val = b_mid := by
    dsimp [bs, compactAffineTableBitSteps, b_mid, UnsignedGivens.bilinearRowBit];
      rw [hβ₁_u, hβ₁_v, hβ₁_hot]
  have htop_eq : (bs.bitTop β₁).val = b_top := by
    dsimp [bs, compactAffineTableBitSteps, b_top, UnsignedGivens.bilinearRowBit];
      rw [hβ₁_u, hβ₁_v, hβ₁_hot]
  have hperm_eq :
    UnsignedGivens.signedAddModPerm B (UnsignedGivens.bitSeqVal (bs.bitLo β₁))
    (UnsignedGivens.bitSeqVal_lt _)
      (β₁ w_p) (UnsignedGivens.localIdx rCat β₁) = y_out := by
    dsimp only [y_out]; rw [signedAddModPerm_congr hlo_eq, hβ₁_wp, hβ₁_cat]
  unfold compactAffineLac2KickRef;
    dsimp only [UnsignedGivens.inPlaceUVStep, UnsignedGivens.PhasedStep.wrapCircuit]
  simp only [UnsignedGivens.eval_seq_mulVec, UnsignedGivens.eval_identity_mulVec,
    UnsignedGivens.evolve_TOFF_ket,
    UnsignedGivens.evolve_CNOT_ket]
  have hupd_eq : Function.update (Function.update β w_v (β w_v + β w_ctrl * β sub)) w_ctrl
      (Function.update β w_v (β w_v + β w_ctrl * β sub) w_ctrl +
        Function.update β w_v (β w_v + β w_ctrl * β sub) w_v) = β₁ := by
    dsimp only [β₁, u_val, v_val]; rw [hv0, zero_add, Function.update_of_ne hdk.hcv,
      Function.update_self]; congr 1; ring
  rw [hupd_eq, hk_in, Matrix.mulVec_smul, UnsignedGivens.evolve_CNOT_ket, Matrix.mulVec_smul,
    UnsignedGivens.evolve_TOFF_ket, hperm_eq, hlo_eq, hmid_eq, htop_eq, hβ₁_wp, hβ₁_cat]
  congr 1; apply congrArg UnsignedGivens.ket
  have hc_nr : w_ctrl ∉ Set.range rCat.wires := fun ⟨i, hi⟩ ↦ hdk.hctrl_cat i hi.symm
  have hv_nr : w_v ∉ Set.range rCat.wires := fun ⟨i, hi⟩ ↦ hdk.hv_cat i hi.symm
  have hs_nr : sub ∉ Set.range rCat.wires := fun ⟨i, hi⟩ ↦ hdk.hsub_cat i hi.symm
  let β₂ := UnsignedGivens.writeReg β₁ rCat (basisBits B y_out)
  have hβ₂_u : β₂ w_ctrl = u_val := by
    dsimp [β₂]; rw [UnsignedGivens.writeReg_apply_of_not_mem _ _ _ _ hc_nr, hβ₁_u]
  have hβ₂_v : β₂ w_v = v_val := by
    dsimp [β₂]; rw [UnsignedGivens.writeReg_apply_of_not_mem _ _ _ _ hv_nr, hβ₁_v]
  have hβ₂_sub : β₂ sub = β sub := by
    dsimp [β₂, β₁]; rw [UnsignedGivens.writeReg_apply_of_not_mem _ _ _ _ hs_nr,
      Function.update_of_ne hdk.hcs.symm, Function.update_of_ne hdk.hsv]
  have hrest_u : u_val + v_val = β w_ctrl := by
    dsimp [u_val, v_val]
    have hr : β w_ctrl * (1 + β sub) + β w_ctrl * β sub =
        β w_ctrl + (β w_ctrl * β sub + β w_ctrl * β sub) := by ring
    rw [hr, UnsignedGivens.zmod2_add_self, add_zero]
  have hrest_v : v_val + β w_ctrl * β sub = β w_v := by
    dsimp [v_val]; rw [UnsignedGivens.zmod2_add_self, hv0]
  change Function.update (Function.update β₂ w_ctrl (β₂ w_ctrl + β₂ w_v)) w_v
      (Function.update β₂ w_ctrl (β₂ w_ctrl + β₂ w_v) w_v +
        Function.update β₂ w_ctrl (β₂ w_ctrl + β₂ w_v) w_ctrl *
          Function.update β₂ w_ctrl (β₂ w_ctrl + β₂ w_v) sub) = _
  rw [hβ₂_u, hβ₂_v, hrest_u, Function.update_of_ne hdk.hcv.symm, Function.update_self,
    Function.update_of_ne hdk.hcs.symm, hβ₂_v, hβ₂_sub, hrest_v]; funext w
  by_cases hwv : w = w_v
  · subst hwv; rw [Function.update_self, UnsignedGivens.writeReg_apply_of_not_mem _ _ _ _ hv_nr]
  · rw [Function.update_of_ne hwv]; by_cases hwc : w = w_ctrl
    · subst hwc; rw [Function.update_self, UnsignedGivens.writeReg_apply_of_not_mem _ _ _ _ hc_nr]
    · rw [Function.update_of_ne hwc]; by_cases hwr : w ∈ Set.range rCat.wires
      · obtain ⟨i, rfl⟩ := hwr; dsimp [β₂];
          rw [UnsignedGivens.writeReg_apply_reg, UnsignedGivens.writeReg_apply_reg]
      · dsimp [β₂, β₁]; rw [UnsignedGivens.writeReg_apply_of_not_mem _ _ _ _ hwr,
          UnsignedGivens.writeReg_apply_of_not_mem _ _ _ _ hwr, Function.update_of_ne hwc,
          Function.update_of_ne hwv]

attribute [irreducible] compactAffineLac2KickDyn compactAffineLac2KickRef

theorem compactPlaneKickDisj {n N k_ctrl G' d m : ℕ} (hd : d ≤ 10) (p : ℕ) (hp : p + 1 < N)
    (rSpin : QRegister N n) (rCtrl : QRegister k_ctrl n) (hsc : rSpin.DisjointWires rCtrl)
    (selHot' : QRegister G' k_ctrl) (subIdx : Fin k_ctrl) (rCat : QRegister 11 n)
    (rWork : QRegister m n) (hm : 23 - d ≤ m) (hac : (rSpin.concat rCtrl hsc).DisjointWires rCat)
    (hdisj : ((rSpin.concat rCtrl hsc).concat rCat hac).DisjointWires rWork) :
    let rPair := rSpin.compose (GivensOps.pairAdj N p hp)
    let rASh := rWork.slice 0 (11 - d) (by omega)
    let rC := rWork.slice (11 - d) 11 (by omega)
    CompactGidneyDisjoint rCat rASh rC (rPair 0) ∧
      CompactAffineKickDisjoint (rPair 1) (rCtrl subIdx) (rWork ⟨22 - d, by omega⟩)
        (rCtrl.compose selHot') rCat rASh rC (rPair 0) :=
  ⟨{ disj_cat_A := QRegister.disjoint_iff.mpr fun i _ ↦ by
       rw [QRegister.slice_apply]; exact UnsignedGivens.ne_cat_work hsc hac hdisj i _
     disj_cat_C := QRegister.disjoint_iff.mpr fun i _ ↦ by
       rw [QRegister.slice_apply]; exact UnsignedGivens.ne_cat_work hsc hac hdisj i _
     disj_A_C := UnsignedGivens.slice_disjoint_of_nonoverlap rWork (by omega) (by omega) (by omega)
     ne_cat_wp := fun i ↦ (UnsignedGivens.ne_spin_cat hsc hac ⟨p, by omega⟩ i).symm
     ne_A_wp := fun _ ↦ by
       rw [QRegister.slice_apply];
         exact (UnsignedGivens.ne_spin_work hsc hac hdisj ⟨p, by omega⟩ _).symm
     ne_C_wp := fun _ ↦ by
       rw [QRegister.slice_apply];
         exact (UnsignedGivens.ne_spin_work hsc hac hdisj ⟨p, by omega⟩ _).symm },
   { hcs := UnsignedGivens.ne_spin_ctrl hsc ⟨p + 1, hp⟩ subIdx
     hcv := UnsignedGivens.ne_spin_work hsc hac hdisj ⟨p + 1, hp⟩ ⟨22 - d, by omega⟩
     hsv := UnsignedGivens.ne_ctrl_work hsc hac hdisj subIdx ⟨22 - d, by omega⟩
     hh_ctrl := fun g ↦ (UnsignedGivens.ne_spin_ctrl hsc ⟨p + 1, hp⟩ (selHot' g)).symm
     hh_v := fun g ↦ UnsignedGivens.ne_ctrl_work hsc hac hdisj (selHot' g) ⟨22 - d, by omega⟩
     hctrl_wp := fun h ↦ by
       have hv := congrArg Fin.val (rSpin.wires.injective h); simp [GivensOps.pairAdj] at hv
     hv_wp := (UnsignedGivens.ne_spin_work hsc hac hdisj ⟨p, by omega⟩ ⟨22 - d, by omega⟩).symm
     hh_wp := fun g ↦ (UnsignedGivens.ne_spin_ctrl hsc ⟨p, by omega⟩ (selHot' g)).symm
     hctrl_cat := fun i ↦ UnsignedGivens.ne_spin_cat hsc hac ⟨p + 1, hp⟩ i
     hv_cat := fun i ↦ (UnsignedGivens.ne_cat_work hsc hac hdisj i ⟨22 - d, by omega⟩).symm
     hh_cat := fun g i ↦ UnsignedGivens.ne_ctrl_cat hsc hac (selHot' g) i
     hsub_cat := fun i ↦ UnsignedGivens.ne_ctrl_cat hsc hac subIdx i
     hctrl_A := fun _ ↦ by
       rw [QRegister.slice_apply]; exact UnsignedGivens.ne_spin_work hsc hac hdisj ⟨p + 1, hp⟩ _
     hv_A := fun _ ↦ by
       rw [QRegister.slice_apply]; intro h
       have hv := congrArg Fin.val (rWork.wires.injective h); dsimp at hv; omega
     hh_A := fun g _ ↦ by
       rw [QRegister.slice_apply]; exact UnsignedGivens.ne_ctrl_work hsc hac hdisj (selHot' g) _
     hsub_A := fun _ ↦ by
       rw [QRegister.slice_apply]; exact UnsignedGivens.ne_ctrl_work hsc hac hdisj subIdx _
     hctrl_C := fun _ ↦ by
       rw [QRegister.slice_apply]; exact UnsignedGivens.ne_spin_work hsc hac hdisj ⟨p + 1, hp⟩ _
     hv_C := fun _ ↦ by
       rw [QRegister.slice_apply]; intro h
       have hv := congrArg Fin.val (rWork.wires.injective h); dsimp at hv; omega
     hh_C := fun g _ ↦ by
       rw [QRegister.slice_apply]; exact UnsignedGivens.ne_ctrl_work hsc hac hdisj (selHot' g) _
     hsub_C := fun _ ↦ by
       rw [QRegister.slice_apply]; exact UnsignedGivens.ne_ctrl_work hsc hac hdisj subIdx _ }⟩

/-- Compact `13`-bit `Lac = 2` plane phase kick (`102 + 4 * d` `T`, `23 - d ≤ m`). -/
def compactLac2PlaneKickDyn {Var : Type} {n N k_ctrl G' d m : ℕ} (v : Var) (hd : d ≤ 10)
    (p : ℕ) (hp : p + 1 < N) (row : Fin (G' + 1) → Bool → ℕ) (rSpin : QRegister N n)
    (rCtrl : QRegister k_ctrl n) (hsc : rSpin.DisjointWires rCtrl) (selHot' : QRegister G' k_ctrl)
    (subIdx : Fin k_ctrl) (rCat : QRegister 11 n) (rWork : QRegister m n) (hm : 23 - d ≤ m)
    (hac : (rSpin.concat rCtrl hsc).DisjointWires rCat)
    (hdisj : ((rSpin.concat rCtrl hsc).concat rCat hac).DisjointWires rWork) :
    DynamicCircuit Var n :=
  let hdPair := compactPlaneKickDisj hd p hp rSpin rCtrl hsc selHot' subIdx rCat rWork hm hac hdisj
  let rPair := rSpin.compose (GivensOps.pairAdj N p hp)
  compactAffineLac2KickDyn v (by omega : d < 11) 12 11 row (rPair 1) (rCtrl subIdx)
    (rWork ⟨22 - d, by omega⟩) (rCtrl.compose selHot') rCat (rWork.slice 0 (11 - d) (by omega))
    (rWork.slice (11 - d) 11 (by omega)) (rPair 0) hdPair.1 hdPair.2

/-- Compact `Lac = 2` forward Givens plane `DynamicCircuit` (`102 + 4 * d` `T`, `0 TOFF`). -/
def compactLac2PlanePosDyn {Var : Type} {n N k_ctrl G' d m : ℕ} (v : Var) (hd : d ≤ 10)
    (p : ℕ) (hp : p + 1 < N) (row : Fin (G' + 1) → Bool → ℕ) (rSpin : QRegister N n)
    (rCtrl : QRegister k_ctrl n) (hsc : rSpin.DisjointWires rCtrl) (selHot' : QRegister G' k_ctrl)
    (subIdx : Fin k_ctrl) (rCat : QRegister 11 n) (rWork : QRegister m n) (hm : 23 - d ≤ m)
    (hac : (rSpin.concat rCtrl hsc).DisjointWires rCat)
    (hdisj : ((rSpin.concat rCtrl hsc).concat rCat hac).DisjointWires rWork) :
    DynamicCircuit Var n :=
  UnsignedGivens.framedPlanePosDyn p hp rSpin
    (compactLac2PlaneKickDyn v hd p hp row rSpin rCtrl hsc selHot' subIdx rCat rWork hm hac hdisj)

/-- Compact `Lac = 2` backward Givens plane `DynamicCircuit` (`102 + 4 * d` `T`, `0 TOFF`). -/
def compactLac2PlaneNegDyn {Var : Type} {n N k_ctrl G' d m : ℕ} (v : Var) (hd : d ≤ 10)
    (p : ℕ) (hp : p + 1 < N) (row : Fin (G' + 1) → Bool → ℕ) (rSpin : QRegister N n)
    (rCtrl : QRegister k_ctrl n) (hsc : rSpin.DisjointWires rCtrl) (selHot' : QRegister G' k_ctrl)
    (subIdx : Fin k_ctrl) (rCat : QRegister 11 n) (rWork : QRegister m n) (hm : 23 - d ≤ m)
    (hac : (rSpin.concat rCtrl hsc).DisjointWires rCat)
    (hdisj : ((rSpin.concat rCtrl hsc).concat rCat hac).DisjointWires rWork) :
    DynamicCircuit Var n :=
  UnsignedGivens.framedPlaneNegDyn p hp rSpin
    (compactLac2PlaneKickDyn v hd p hp row rSpin rCtrl hsc selHot' subIdx rCat rWork hm hac hdisj)

theorem ctrlMuxCatalytic_compactLac2PlaneKickDyn {Var : Type} [Fintype Var] [DecidableEq Var]
    {n N k_ctrl G' d m : ℕ} [NeZero (2 ^ n)] (v : Var) (hd : d ≤ 10) (p : ℕ) (hp : p + 1 < N)
    (row : Fin (G' + 1) → Bool → ℕ) (rSpin : QRegister N n) (rCtrl : QRegister k_ctrl n)
    (hsc : rSpin.DisjointWires rCtrl) (selHot' : QRegister G' k_ctrl) (subIdx : Fin k_ctrl)
    (rCat : QRegister 11 n) (rWork : QRegister m n) (hm : 23 - d ≤ m)
    (hac : (rSpin.concat rCtrl hsc).DisjointWires rCat)
    (hdisj : ((rSpin.concat rCtrl hsc).concat rCat hac).DisjointWires rWork) :
    let rPair := rSpin.compose (GivensOps.pairAdj N p hp)
    let hpc := UnsignedGivens.disj_sub_ctrl hsc (GivensOps.pairAdj N p hp)
    let hac_pair := UnsignedGivens.disj_sub_cat hsc hac (GivensOps.pairAdj N p hp)
    let α_fn := fun (b₁ : ZMod 2) (c : Fin (2 ^ k_ctrl)) ↦
      2 * π * (affinePlaneEffK row selHot' subIdx b₁ c : ℝ) / (2 : ℝ) ^ (11 + 3)
    OneHotMux.CtrlMuxCatalyticWith (phaseGradientFineLow 11 3) rPair rCat
      (OneHotMux.disj_sys_cat_of hpc hac_pair) rCtrl
        (OneHotMux.disj_sysCat_ctrl_of hpc hac_pair) rWork
      (fun c ↦ UnsignedGivens.phaseDiagUnitary (UnsignedGivens.genKick4 (α_fn 0 c) (α_fn 1 c))
        (UnsignedGivens.genKick4_unit (α_fn 0 c) (α_fn 1 c)))
      (compactLac2PlaneKickDyn v hd p hp row rSpin rCtrl hsc selHot' subIdx rCat rWork hm hac
        hdisj) := by
  intro rPair hpc hac_pair α_fn
  let hdPair := compactPlaneKickDisj hd p hp rSpin rCtrl hsc selHot' subIdx rCat rWork hm hac hdisj
  have hclean := realizesCleanRef_compactAffineLac2KickDyn_widen v (by omega : d < 11) 12 11 row
    (rPair 1) (rCtrl subIdx) (rWork ⟨22 - d, by omega⟩) (rCtrl.compose selHot') rCat
    (rWork.slice 0 (11 - d) (by omega)) (rWork.slice (11 - d) 11 (by omega)) (rPair 0)
    hdPair.1 hdPair.2 rWork (QRegister.mem_image rWork _ |>.mpr ⟨⟨22 - d, by omega⟩, rfl⟩)
    (UnsignedGivens.slice_image_subset rWork (by omega)) (UnsignedGivens.slice_image_subset rWork
      (by omega))
    (UnsignedGivens.ne_cat_work hsc hac hdisj)
  exact OneHotMux.CtrlMuxCatalyticWith.ofRawKick rPair rCat
    (OneHotMux.disj_sys_cat_of hpc hac_pair) rCtrl
    (OneHotMux.disj_sysCat_ctrl_of hpc hac_pair) rWork _ _ hclean
    (fun b₁ c ↦ UnsignedGivens.bilinearRowLo 11 row b₁ (basisBits k_ctrl c subIdx)
      (extendHot0 (UnsignedGivens.ctrlHotBits selHot' c)))
    (fun _ _ ↦ UnsignedGivens.bilinearRowLo_lt _ _ _ _ _)
    (fun b₁ c ↦ UnsignedGivens.bilinearRowBit 11 row b₁ (basisBits k_ctrl c subIdx)
      (extendHot0 (UnsignedGivens.ctrlHotBits selHot' c)))
    (fun b₁ c ↦ UnsignedGivens.bilinearRowBit 12 row b₁ (basisBits k_ctrl c subIdx)
      (extendHot0 (UnsignedGivens.ctrlHotBits selHot' c)))
    (fun _ _ ↦ UnsignedGivens.bilinearRowBit_lt _ _ _ _ _) (fun _ _ ↦
      UnsignedGivens.bilinearRowBit_lt _ _ _ _ _)
    (fun β h0 ↦ by
      have hk := compactAffineLac2KickRef_ket_of_zero (by omega : d < 11) 12 11 row (rPair 1)
        (rCtrl subIdx) (rWork ⟨22 - d, by omega⟩) (rCtrl.compose selHot') rCat
        (rWork.slice 0 (11 - d) (by omega)) (rWork.slice (11 - d) 11 (by omega)) (rPair 0)
        hdPair.1 hdPair.2 β (h0 ⟨22 - d, by omega⟩)
        (fun _ ↦ by rw [QRegister.slice_apply]; exact h0 _)
        (fun _ ↦ by rw [QRegister.slice_apply]; exact h0 _)
      dsimp only at hk ⊢
      have hsub : β (rCtrl subIdx) = basisBits k_ctrl (UnsignedGivens.localIdx rCtrl β) subIdx :=
        (congrFun (UnsignedGivens.basisBits_symm_eq (fun j ↦ β (rCtrl j))) subIdx).symm
      have hhot : extendHot0 (fun g : Fin G' ↦ β ((rCtrl.compose selHot') g)) =
          extendHot0 (UnsignedGivens.ctrlHotBits selHot' (UnsignedGivens.localIdx rCtrl β)) :=
        congrArg extendHot0 (UnsignedGivens.compose_hot_bits_eq rCtrl selHot' β)
      have hlo_eq : UnsignedGivens.bilinearRowLo 11 row (β (rPair 1)) (β (rCtrl subIdx))
          (extendHot0 (fun g : Fin G' ↦ β ((rCtrl.compose selHot') g))) =
          UnsignedGivens.bilinearRowLo 11 row (β (rPair 1))
            (basisBits k_ctrl (UnsignedGivens.localIdx rCtrl β) subIdx)
            (extendHot0 (UnsignedGivens.ctrlHotBits selHot'
                (UnsignedGivens.localIdx rCtrl β))) := by
        rw [hsub, hhot]
      rw [hk, signedAddModPerm_congr hlo_eq]
      · simp only [hsub, hhot]
      · exact UnsignedGivens.bilinearRowLo_lt _ _ _ _ _)

theorem ctrlMuxCatalytic_compactLac2PlanePosDyn {Var : Type} [Fintype Var] [DecidableEq Var]
    {n N k_ctrl G' d m : ℕ} [NeZero (2 ^ n)] (v : Var) (hd : d ≤ 10) (p : ℕ) (hp : p + 1 < N)
    (row : Fin (G' + 1) → Bool → ℕ) (rSpin : QRegister N n) (rCtrl : QRegister k_ctrl n)
    (hsc : rSpin.DisjointWires rCtrl) (selHot' : QRegister G' k_ctrl) (subIdx : Fin k_ctrl)
    (rCat : QRegister 11 n) (rWork : QRegister m n) (hm : 23 - d ≤ m)
    (hac : (rSpin.concat rCtrl hsc).DisjointWires rCat)
    (hdisj : ((rSpin.concat rCtrl hsc).concat rCat hac).DisjointWires rWork) :
    let α_fn := fun (b₁ : ZMod 2) (c : Fin (2 ^ k_ctrl)) ↦
      2 * π * (affinePlaneEffK row selHot' subIdx b₁ c : ℝ) / (2 : ℝ) ^ 14
    OneHotMux.CtrlMuxCatalyticWith (phaseGradientFineLow 11 3) rSpin rCat
      (OneHotMux.disj_sys_cat_of hsc hac) rCtrl (OneHotMux.disj_sysCat_ctrl_of hsc hac) rWork
      (fun c ↦ (GivensOps.pairAdj N p hp).embedUnitary
        (UnsignedGivens.genGivensPosUnitary (α_fn 0 c) (α_fn 1 c)))
      (compactLac2PlanePosDyn v hd p hp row rSpin rCtrl hsc selHot' subIdx rCat rWork hm hac
        hdisj) :=
  OneHotMux.ctrlMuxCatalytic_framedPlanePos
    (phaseGradientFineLow 11 3) p hp rSpin rCtrl hsc rCat rWork
    hac hdisj (ctrlMuxCatalytic_compactLac2PlaneKickDyn v hd p hp row rSpin rCtrl hsc selHot' subIdx
      rCat rWork hm hac hdisj)

theorem ctrlMuxCatalytic_compactLac2PlaneNegDyn {Var : Type} [Fintype Var] [DecidableEq Var]
    {n N k_ctrl G' d m : ℕ} [NeZero (2 ^ n)] (v : Var) (hd : d ≤ 10) (p : ℕ) (hp : p + 1 < N)
    (row : Fin (G' + 1) → Bool → ℕ) (rSpin : QRegister N n) (rCtrl : QRegister k_ctrl n)
    (hsc : rSpin.DisjointWires rCtrl) (selHot' : QRegister G' k_ctrl) (subIdx : Fin k_ctrl)
    (rCat : QRegister 11 n) (rWork : QRegister m n) (hm : 23 - d ≤ m)
    (hac : (rSpin.concat rCtrl hsc).DisjointWires rCat)
    (hdisj : ((rSpin.concat rCtrl hsc).concat rCat hac).DisjointWires rWork) :
    let α_fn := fun (b₁ : ZMod 2) (c : Fin (2 ^ k_ctrl)) ↦
      2 * π * (affinePlaneEffK row selHot' subIdx b₁ c : ℝ) / (2 : ℝ) ^ 14
    OneHotMux.CtrlMuxCatalyticWith (phaseGradientFineLow 11 3) rSpin rCat
      (OneHotMux.disj_sys_cat_of hsc hac) rCtrl (OneHotMux.disj_sysCat_ctrl_of hsc hac) rWork
      (fun c ↦ (GivensOps.pairAdj N p hp).embedUnitary
        (UnsignedGivens.genGivensNegUnitary (α_fn 0 c) (α_fn 1 c)))
      (compactLac2PlaneNegDyn v hd p hp row rSpin rCtrl hsc selHot' subIdx rCat rWork hm hac
        hdisj) :=
  OneHotMux.ctrlMuxCatalytic_framedPlaneNeg
    (phaseGradientFineLow 11 3) p hp rSpin rCtrl hsc rCat rWork
    hac hdisj (ctrlMuxCatalytic_compactLac2PlaneKickDyn v hd p hp row rSpin rCtrl hsc selHot' subIdx
      rCat rWork hm hac hdisj)

theorem compactApexKickDisj {n N k_ctrl G' d m : ℕ} (hd : d ≤ 10) (hN : 1 < N)
    (rSpin : QRegister N n) (rCtrl : QRegister k_ctrl n) (hsc : rSpin.DisjointWires rCtrl)
    (selHot' : QRegister G' k_ctrl) (subIdx : Fin k_ctrl) (rCat : QRegister 11 n)
    (rWork : QRegister m n) (hm : 22 - (d - 1) ≤ m)
    (hac : (rSpin.concat rCtrl hsc).DisjointWires rCat)
    (hdisj : ((rSpin.concat rCtrl hsc).concat rCat hac).DisjointWires rWork) :
    let rPair0 := rSpin.compose (GivensOps.pairAdj N 0 hN)
    let rCat10 := rCat.compose (locRight 1 10)
    let rASh := rWork.slice 0 (10 - (d - 1)) (by omega)
    let rC := rWork.slice (10 - (d - 1)) 10 (by omega)
    CompactGidneyDisjoint rCat10 rASh rC (rPair0 0) ∧
      CompactAffineKickDisjoint (rWork ⟨21 - (d - 1), by omega⟩) (rCtrl subIdx)
        (rWork ⟨20 - (d - 1), by omega⟩) (rCtrl.compose selHot') rCat10 rASh rC (rPair0 0) :=
  ⟨{ disj_cat_A := QRegister.disjoint_iff.mpr fun i _ ↦ by
       rw [QRegister.slice_apply];
         exact UnsignedGivens.ne_cat_work hsc hac hdisj (locRight 1 10 i) _
     disj_cat_C := QRegister.disjoint_iff.mpr fun i _ ↦ by
       rw [QRegister.slice_apply];
         exact UnsignedGivens.ne_cat_work hsc hac hdisj (locRight 1 10 i) _
     disj_A_C := UnsignedGivens.slice_disjoint_of_nonoverlap rWork (by omega) (by omega) (by omega)
     ne_cat_wp := fun i ↦ (UnsignedGivens.ne_spin_cat hsc hac ⟨0, by omega⟩ (locRight 1 10 i)).symm
     ne_A_wp := fun _ ↦ by
       rw [QRegister.slice_apply];
         exact (UnsignedGivens.ne_spin_work hsc hac hdisj ⟨0, by omega⟩ _).symm
     ne_C_wp := fun _ ↦ by
       rw [QRegister.slice_apply];
         exact (UnsignedGivens.ne_spin_work hsc hac hdisj ⟨0, by omega⟩ _).symm },
   { hcs := (UnsignedGivens.ne_ctrl_work hsc hac hdisj subIdx ⟨21 - (d - 1), by omega⟩).symm
     hcv := fun h ↦ by
       have hv := congrArg Fin.val (rWork.wires.injective h); dsimp at hv; omega
     hsv := UnsignedGivens.ne_ctrl_work hsc hac hdisj subIdx ⟨20 - (d - 1), by omega⟩
     hh_ctrl := fun g ↦ UnsignedGivens.ne_ctrl_work hsc hac hdisj (selHot' g) ⟨21 - (d - 1), by
       omega⟩
     hh_v := fun g ↦ UnsignedGivens.ne_ctrl_work hsc hac hdisj (selHot' g) ⟨20 - (d - 1), by omega⟩
     hctrl_wp := (UnsignedGivens.ne_spin_work hsc hac hdisj ⟨0, by omega⟩ ⟨21 - (d - 1), by
       omega⟩).symm
     hv_wp := (UnsignedGivens.ne_spin_work hsc hac hdisj ⟨0, by omega⟩ ⟨20 - (d - 1), by
       omega⟩).symm
     hh_wp := fun g ↦ (UnsignedGivens.ne_spin_ctrl hsc ⟨0, by omega⟩ (selHot' g)).symm
     hctrl_cat := fun i ↦
       (UnsignedGivens.ne_cat_work hsc hac hdisj (locRight 1 10 i) ⟨21 - (d - 1), by omega⟩).symm
     hv_cat := fun i ↦
       (UnsignedGivens.ne_cat_work hsc hac hdisj (locRight 1 10 i) ⟨20 - (d - 1), by omega⟩).symm
     hh_cat := fun g i ↦ UnsignedGivens.ne_ctrl_cat hsc hac (selHot' g) (locRight 1 10 i)
     hsub_cat := fun i ↦ UnsignedGivens.ne_ctrl_cat hsc hac subIdx (locRight 1 10 i)
     hctrl_A := fun _ ↦ by
       rw [QRegister.slice_apply]; intro h
       have hv := congrArg Fin.val (rWork.wires.injective h); dsimp at hv; omega
     hv_A := fun _ ↦ by
       rw [QRegister.slice_apply]; intro h
       have hv := congrArg Fin.val (rWork.wires.injective h); dsimp at hv; omega
     hh_A := fun g _ ↦ by
       rw [QRegister.slice_apply]; exact UnsignedGivens.ne_ctrl_work hsc hac hdisj (selHot' g) _
     hsub_A := fun _ ↦ by
       rw [QRegister.slice_apply]; exact UnsignedGivens.ne_ctrl_work hsc hac hdisj subIdx _
     hctrl_C := fun _ ↦ by
       rw [QRegister.slice_apply]; intro h
       have hv := congrArg Fin.val (rWork.wires.injective h); dsimp at hv; omega
     hv_C := fun _ ↦ by
       rw [QRegister.slice_apply]; intro h
       have hv := congrArg Fin.val (rWork.wires.injective h); dsimp at hv; omega
     hh_C := fun g _ ↦ by
       rw [QRegister.slice_apply]; exact UnsignedGivens.ne_ctrl_work hsc hac hdisj (selHot' g) _
     hsub_C := fun _ ↦ by
       rw [QRegister.slice_apply]; exact UnsignedGivens.ne_ctrl_work hsc hac hdisj subIdx _ }⟩

/-- Compact `Lac = 2` Wire-Controlled fused apex (`98 + 4 * (d - 1)` `T`, `0 TOFF`). -/
def compactLac2ApexCtrlDyn {Var : Type} {n N k_ctrl G' d m : ℕ} (v : Var) (hd : d ≤ 10)
    (hN : 1 < N) (row0 : Fin (G' + 1) → Bool → ℕ) (rSpin : QRegister N n)
    (rCtrl : QRegister k_ctrl n) (hsc : rSpin.DisjointWires rCtrl) (actIdx : Fin k_ctrl)
    (selHot' : QRegister G' k_ctrl) (subIdx : Fin k_ctrl) (rCat : QRegister 11 n)
    (rWork : QRegister m n) (hm : 22 - (d - 1) ≤ m)
    (hac : (rSpin.concat rCtrl hsc).DisjointWires rCat)
    (hdisj : ((rSpin.concat rCtrl hsc).concat rCat hac).DisjointWires rWork) :
    DynamicCircuit Var n :=
  let hdAp := compactApexKickDisj hd hN rSpin rCtrl hsc selHot' subIdx rCat rWork hm hac hdisj
  let w_act1 := rWork ⟨21 - (d - 1), by omega⟩
  UnsignedGivens.framedCtrlApexDyn v hN rSpin rCtrl hsc actIdx w_act1
    (UnsignedGivens.ne_ctrl_work hsc hac hdisj actIdx ⟨21 - (d - 1), by omega⟩)
    (UnsignedGivens.ne_spin_work hsc hac hdisj ⟨1, hN⟩ ⟨21 - (d - 1), by omega⟩)
    (UnsignedGivens.ne_spin_work hsc hac hdisj ⟨0, by omega⟩ ⟨21 - (d - 1), by omega⟩)
    (compactAffineLac2KickDyn v (by omega : d - 1 < 10) 12 10 row0 w_act1 (rCtrl subIdx)
      (rWork ⟨20 - (d - 1), by omega⟩) (rCtrl.compose selHot') (rCat.compose (locRight 1 10))
      (rWork.slice 0 (10 - (d - 1)) (by omega)) (rWork.slice (10 - (d - 1)) 10 (by omega))
      ((rSpin.compose (GivensOps.pairAdj N 0 hN)) 0) hdAp.1 hdAp.2)

theorem ctrlMuxCatalytic_compactLac2ApexCtrlDyn {Var : Type} [Fintype Var] [DecidableEq Var]
    {n N k_ctrl G' d m : ℕ} [NeZero (2 ^ n)] (v : Var) (hd : d ≤ 10) (hN : 1 < N)
    (row0 : Fin (G' + 1) → Bool → ℕ) (rSpin : QRegister N n) (rCtrl : QRegister k_ctrl n)
    (hsc : rSpin.DisjointWires rCtrl) (actIdx : Fin k_ctrl) (selHot' : QRegister G' k_ctrl)
    (subIdx : Fin k_ctrl) (rCat : QRegister 11 n) (rWork : QRegister m n) (hm : 22 - (d - 1) ≤ m)
    (hac : (rSpin.concat rCtrl hsc).DisjointWires rCat)
    (hdisj : ((rSpin.concat rCtrl hsc).concat rCat hac).DisjointWires rWork) :
    let z0 : Fin N := ⟨0, by omega⟩
    let α_fn := fun (b₁ : ZMod 2) (c : Fin (2 ^ k_ctrl)) ↦
      2 * π *
        (affineApexEffK row0 selHot' subIdx (basisBits k_ctrl c actIdx * b₁) c : ℝ) /
        (2 : ℝ) ^ 13
    OneHotMux.CtrlMuxCatalyticWith (phaseGradientFineLow 11 3) rSpin rCat
      (OneHotMux.disj_sys_cat_of hsc hac) rCtrl (OneHotMux.disj_sysCat_ctrl_of hsc hac) rWork
      (fun c ↦ (if basisBits k_ctrl c actIdx = 0 then 1
        else (QRegister.singleton z0).embedUnitary Qubit.Z) *
          (GivensOps.pairAdj N 0 hN).embedUnitary (UnsignedGivens.genGivensPosUnitary (α_fn 0 c)
            (α_fn 1 c)))
      (compactLac2ApexCtrlDyn v hd hN row0 rSpin rCtrl hsc actIdx selHot' subIdx rCat rWork hm hac
        hdisj) := by
  intro z0 α_fn
  let hdAp := compactApexKickDisj hd hN rSpin rCtrl hsc selHot' subIdx rCat rWork hm hac hdisj
  let w_act1 := rWork ⟨21 - (d - 1), by omega⟩
  let w_v := rWork ⟨20 - (d - 1), by omega⟩
  let rPair0 := rSpin.compose (GivensOps.pairAdj N 0 hN)
  let rCat10 := rCat.compose (locRight 1 10)
  let rHot' := rCtrl.compose selHot'
  let rASh := rWork.slice 0 (10 - (d - 1)) (by omega)
  let rC := rWork.slice (10 - (d - 1)) 10 (by omega)
  let rWorkIn := rWork.slice 0 (21 - (d - 1)) (by omega)
  have hv_mem : w_v ∈ rWorkIn.image :=
    QRegister.mem_image rWorkIn _ |>.mpr ⟨⟨20 - (d - 1), by omega⟩, by simp [rWorkIn, w_v]⟩
  have hA_sub : rASh.image ⊆ rWorkIn.image := fun q hq ↦ by
    obtain ⟨i, rfl⟩ := QRegister.mem_image rASh q |>.mp hq
    exact QRegister.mem_image rWorkIn _ |>.mpr ⟨⟨i.val, by omega⟩, by simp [rWorkIn, rASh]⟩
  have hC_sub : rC.image ⊆ rWorkIn.image := fun q hq ↦ by
    obtain ⟨i, rfl⟩ := QRegister.mem_image rC q |>.mp hq
    refine QRegister.mem_image rWorkIn _ |>.mpr ⟨⟨10 - (d - 1) + i.val, by omega⟩, ?_⟩
    simp only [rWorkIn, rC, QRegister.slice_apply]; congr 1; ext; dsimp; omega
  have hclean := realizesCleanRef_compactAffineLac2KickDyn_widen v (by omega : d - 1 < 10) 12 10
    row0 w_act1 (rCtrl subIdx) w_v rHot' rCat10 rASh rC (rPair0 0) hdAp.1 hdAp.2 rWorkIn hv_mem
    hA_sub hC_sub (fun i _ ↦ by
      rw [QRegister.slice_apply];
        exact UnsignedGivens.ne_cat_work hsc hac hdisj (locRight 1 10 i) _)
  have hw1_not : w_act1 ∉ rWorkIn.image := by
    rw [QRegister.mem_image]; rintro ⟨j, hj⟩; dsimp only [rWorkIn, w_act1] at hj
    rw [QRegister.slice_apply] at hj
    have hv := congrArg Fin.val (rWork.wires.injective hj); dsimp at hv; omega
  exact OneHotMux.ctrlMuxCatalytic_framedCtrlApex v hN rSpin rCtrl hsc actIdx rCat rWork hac hdisj
    w_act1 (QRegister.mem_image rWork _ |>.mpr ⟨⟨21 - (d - 1), by omega⟩, rfl⟩) rWorkIn
    (UnsignedGivens.slice_image_subset rWork (by omega)) hw1_not _ _ hclean
    (compactAffineLac2KickRef_phasedPerm (by omega : d - 1 < 10) 12 10 row0 w_act1 (rCtrl subIdx)
      w_v rHot' rCat10 rASh rC (rPair0 0) hdAp.1 hdAp.2)
    (fun qc c ↦ UnsignedGivens.bilinearRowLo 10 row0 qc (basisBits k_ctrl c subIdx)
      (extendHot0 (UnsignedGivens.ctrlHotBits selHot' c)))
    (fun _ _ ↦ UnsignedGivens.bilinearRowLo_lt _ _ _ _ _)
    (fun qc c ↦ UnsignedGivens.bilinearRowBit 10 row0 qc (basisBits k_ctrl c subIdx)
      (extendHot0 (UnsignedGivens.ctrlHotBits selHot' c)))
    (fun qc c ↦ UnsignedGivens.bilinearRowBit 12 row0 qc (basisBits k_ctrl c subIdx)
      (extendHot0 (UnsignedGivens.ctrlHotBits selHot' c)))
    (fun _ _ ↦ UnsignedGivens.bilinearRowBit_lt _ _ _ _ _) (fun _ _ ↦
      UnsignedGivens.bilinearRowBit_lt _ _ _ _ _)
    (fun β h0 ↦ by
      have hv0 : β w_v = 0 := by
        simpa [rWorkIn, w_v] using h0 ⟨20 - (d - 1), by omega⟩
      have hA0 (j : Fin (10 - (d - 1))) : β (rASh j) = 0 := by
        simpa [rWorkIn, rASh] using h0 ⟨j.val, by omega⟩
      have hC0 (j : Fin 10) : β (rC j) = 0 := by
        have h := h0 ⟨10 - (d - 1) + j.val, by omega⟩
        dsimp only [rWorkIn, rC] at h ⊢; rw [QRegister.slice_apply] at h ⊢
        convert h using 2; congr 1; ext; dsimp; omega
      have hk := compactAffineLac2KickRef_ket_of_zero (by omega : d - 1 < 10) 12 10 row0 w_act1
        (rCtrl subIdx) w_v rHot' rCat10 rASh rC (rPair0 0) hdAp.1 hdAp.2 β hv0 hA0 hC0
      dsimp only at hk ⊢
      have hsub : β (rCtrl subIdx) = basisBits k_ctrl (UnsignedGivens.localIdx rCtrl β) subIdx :=
        (congrFun (UnsignedGivens.basisBits_symm_eq (fun j ↦ β (rCtrl j))) subIdx).symm
      have hhot : extendHot0 (fun g : Fin G' ↦ β (rHot' g)) =
          extendHot0 (UnsignedGivens.ctrlHotBits selHot' (UnsignedGivens.localIdx rCtrl β)) :=
        congrArg extendHot0 (UnsignedGivens.compose_hot_bits_eq rCtrl selHot' β)
      have hlo_eq : UnsignedGivens.bilinearRowLo 10 row0 (β w_act1) (β (rCtrl subIdx))
          (extendHot0 (fun g : Fin G' ↦ β (rHot' g))) =
          UnsignedGivens.bilinearRowLo 10 row0 (β w_act1)
            (basisBits k_ctrl (UnsignedGivens.localIdx rCtrl β) subIdx)
            (extendHot0 (UnsignedGivens.ctrlHotBits selHot'
                (UnsignedGivens.localIdx rCtrl β))) := by
        rw [hsub, hhot]
      rw [hk, signedAddModPerm_congr hlo_eq]
      · dsimp only [rPair0, rCat10]; simp only [hsub, hhot]
      · exact UnsignedGivens.bilinearRowLo_lt _ _ _ _ _)

/-- Compact `(N - 1)`-plane Wire-Controlled `Lac = 2` cascade (`23 - d ≤ m`, `0 TOFF`). -/
def compactLac2CascadeCtrlDyn {Var : Type} {n N k_ctrl G' d m : ℕ} (v : Var) (hd : d ≤ 10)
    (hN : 1 < N) (table : Fin (G' + 1) → Bool → Fin N → ℕ) (rSpin : QRegister N n)
    (rCtrl : QRegister k_ctrl n) (hsc : rSpin.DisjointWires rCtrl) (actIdx : Fin k_ctrl)
    (selHot' : QRegister G' k_ctrl) (subIdx : Fin k_ctrl) (rCat : QRegister 11 n)
    (rWork : QRegister m n) (hm : 23 - d ≤ m) (hac : (rSpin.concat rCtrl hsc).DisjointWires rCat)
    (hdisj : ((rSpin.concat rCtrl hsc).concat rCat hac).DisjointWires rWork) :
    DynamicCircuit Var n :=
  UnsignedGivens.genericCascadeDyn hN
    (fun p hp ↦ compactLac2PlanePosDyn v hd p hp (fun g b ↦ table g b ⟨p, by omega⟩) rSpin rCtrl hsc
      selHot' subIdx rCat rWork hm hac hdisj)
    (fun p hp ↦ compactLac2PlaneNegDyn v hd p hp (fun g b ↦ table g b ⟨p, by omega⟩) rSpin rCtrl hsc
      selHot' subIdx rCat rWork hm hac hdisj)
    (compactLac2ApexCtrlDyn v hd hN (fun g b ↦ table g b ⟨0, by omega⟩) rSpin rCtrl hsc actIdx
      selHot' subIdx rCat rWork (by omega) hac hdisj)

@[simp] theorem count_compactLac2CascadeCtrlDyn_toff {Var : Type} {n N k_ctrl G' d m : ℕ} (v : Var)
    (hd : d ≤ 10) (hN : 1 < N) (table : Fin (G' + 1) → Bool → Fin N → ℕ) (rSpin : QRegister N n)
    (rCtrl : QRegister k_ctrl n) (hsc : rSpin.DisjointWires rCtrl) (actIdx : Fin k_ctrl)
    (selHot' : QRegister G' k_ctrl) (subIdx : Fin k_ctrl) (rCat : QRegister 11 n)
    (rWork : QRegister m n) (hm : 23 - d ≤ m) (hac : (rSpin.concat rCtrl hsc).DisjointWires rCat)
    (hdisj : ((rSpin.concat rCtrl hsc).concat rCat hac).DisjointWires rWork) :
    (compactLac2CascadeCtrlDyn v hd hN table rSpin rCtrl hsc actIdx selHot' subIdx rCat rWork hm hac
      hdisj).count .TOFF = 0 := by
  refine UnsignedGivens.count_genericCascadeDyn_toff hN _ _ _ (fun _ _ ↦ ?_) (fun _ _ ↦ ?_) ?_
  · rw [compactLac2PlanePosDyn, UnsignedGivens.count_framedPlanePosDyn_toff];
      simp [compactLac2PlaneKickDyn]
  · rw [compactLac2PlaneNegDyn, UnsignedGivens.count_framedPlaneNegDyn_toff];
      simp [compactLac2PlaneKickDyn]
  · rw [compactLac2ApexCtrlDyn, UnsignedGivens.count_framedCtrlApexDyn_toff]; simp

@[simp] theorem count_compactLac2CascadeCtrlDyn_t {Var : Type} {n N k_ctrl G' d m : ℕ} (v : Var)
    (hd : d ≤ 10) (hN : 1 < N) (table : Fin (G' + 1) → Bool → Fin N → ℕ) (rSpin : QRegister N n)
    (rCtrl : QRegister k_ctrl n) (hsc : rSpin.DisjointWires rCtrl) (actIdx : Fin k_ctrl)
    (selHot' : QRegister G' k_ctrl) (subIdx : Fin k_ctrl) (rCat : QRegister 11 n)
    (rWork : QRegister m n) (hm : 23 - d ≤ m) (hac : (rSpin.concat rCtrl hsc).DisjointWires rCat)
    (hdisj : ((rSpin.concat rCtrl hsc).concat rCat hac).DisjointWires rWork) :
    (compactLac2CascadeCtrlDyn v hd hN table rSpin rCtrl hsc actIdx selHot' subIdx rCat rWork hm hac
      hdisj).count .T = 2 * (N - 2) * (102 + 4 * d) + (98 + 4 * (d - 1)) := by
  refine UnsignedGivens.count_genericCascadeDyn_t hN _ _ _ (102 + 4 * d) (98 + 4 * (d - 1))
    (fun _ _ ↦ ?_) (fun _ _ ↦ ?_) ?_
  · rw [compactLac2PlanePosDyn, UnsignedGivens.count_framedPlanePosDyn_t];
      simp [compactLac2PlaneKickDyn]
  · rw [compactLac2PlaneNegDyn, UnsignedGivens.count_framedPlaneNegDyn_t];
      simp [compactLac2PlaneKickDyn]
  · rw [compactLac2ApexCtrlDyn, UnsignedGivens.count_framedCtrlApexDyn_t]; simp; ring

theorem ctrlMuxCatalytic_compactLac2CascadeCtrlDyn {Var : Type} [Fintype Var] [DecidableEq Var]
    {n N k_ctrl G' d m : ℕ} [NeZero (2 ^ n)] (v : Var) (hd : d ≤ 10) (hN : 1 < N)
    (table : Fin (G' + 1) → Bool → Fin N → ℕ) (rSpin : QRegister N n) (rCtrl : QRegister k_ctrl n)
    (hsc : rSpin.DisjointWires rCtrl) (actIdx : Fin k_ctrl) (selHot' : QRegister G' k_ctrl)
    (subIdx : Fin k_ctrl) (rCat : QRegister 11 n) (rWork : QRegister m n) (hm : 23 - d ≤ m)
    (hac : (rSpin.concat rCtrl hsc).DisjointWires rCat)
    (hdisj : ((rSpin.concat rCtrl hsc).concat rCat hac).DisjointWires rWork) :
    OneHotMux.CtrlMuxCatalyticWith (phaseGradientFineLow 11 3) rSpin rCat
      (OneHotMux.disj_sys_cat_of hsc hac) rCtrl (OneHotMux.disj_sysCat_ctrl_of hsc hac) rWork
      (affineUnsignedBilinearLac2CascadeCtrlUnitary hN table actIdx selHot' subIdx)
      (compactLac2CascadeCtrlDyn v hd hN table rSpin rCtrl hsc actIdx selHot' subIdx rCat rWork hm
        hac hdisj) := by
  let α_pl : ZMod 2 → ℕ → Fin (2 ^ k_ctrl) → ℝ := fun b₁ p c ↦
    if hp : p + 1 < N then
      2 * π * (affinePlaneEffK (fun g b ↦ table g b ⟨p, by omega⟩) selHot' subIdx b₁ c : ℝ) /
        (2 : ℝ) ^ 14
    else 0
  exact OneHotMux.ctrlMuxCatalytic_genericCascadeDyn hN (phaseGradientFineLow 11 3) rSpin rCtrl hsc
    rCat rWork hac hdisj _ _ _ (α_pl 0) (α_pl 1) _
    (fun p hp ↦ (ctrlMuxCatalytic_compactLac2PlanePosDyn v hd p hp _ rSpin rCtrl hsc selHot' subIdx
      rCat rWork hm hac hdisj).congrUnitary (funext fun c ↦ by simp only [α_pl, hp, ↓reduceDIte]))
    (fun p hp ↦ (ctrlMuxCatalytic_compactLac2PlaneNegDyn v hd p hp _ rSpin rCtrl hsc selHot' subIdx
      rCat rWork hm hac hdisj).congrUnitary (funext fun c ↦ by simp only [α_pl, hp, ↓reduceDIte]))
    (ctrlMuxCatalytic_compactLac2ApexCtrlDyn v hd hN _ rSpin rCtrl hsc actIdx selHot' subIdx rCat
      rWork (by omega) hac hdisj)

attribute [irreducible] compactLac2PlaneKickDyn compactLac2PlanePosDyn compactLac2PlaneNegDyn
attribute [irreducible] compactLac2ApexCtrlDyn compactLac2CascadeCtrlDyn

/-- Packaged `22 - d ≤ m` compact `Lac = 2` cascade recycling `wHot0` (`0` extra `T`s). -/
def compactLac2CascadeCtrl22Dyn {Var : Type} {n N k_ctrl G' d m : ℕ} (v : Var) (hd : d ≤ 10)
    (hN : 1 < N) (table : Fin (G' + 1) → Bool → Fin N → ℕ) (rSpin : QRegister N n)
    (rCtrlTail : QRegister k_ctrl n) (hsc : rSpin.DisjointWires rCtrlTail) (actIdx : Fin k_ctrl)
    (selHot' : QRegister G' k_ctrl) (subIdx : Fin k_ctrl) (wHot0 : Wire n) (rCat : QRegister 11 n)
    (rWork : QRegister m n) (hm : 22 - d ≤ m)
    (hac : (rSpin.concat rCtrlTail hsc).DisjointWires rCat)
    (hWork0 : rWork.DisjointWires (QRegister.singleton wHot0))
    (hdisjPlus : ((rSpin.concat rCtrlTail hsc).concat rCat hac).DisjointWires
      (rWork.concat (QRegister.singleton wHot0) hWork0)) :
    DynamicCircuit Var n :=
  let rHot' := rCtrlTail.compose selHot'
  have hne0 (g : Fin G') : rHot' g ≠ wHot0 := by
    simpa [rHot'] using UnsignedGivens.ne_ctrl_work hsc hac hdisjPlus (selHot' g) (Fin.natAdd m 0)
  let cClear0 := clearHot0Circuit rHot' wHot0 hne0
  .seq (.circuit cClear0)
    (.seq (compactLac2CascadeCtrlDyn v hd hN table rSpin rCtrlTail hsc actIdx selHot' subIdx rCat
      (rWork.concat (QRegister.singleton wHot0) hWork0) (by omega) hac hdisjPlus)
      (.circuit cClear0))

@[simp] theorem count_compactLac2CascadeCtrl22Dyn_toff {Var : Type} {n N k_ctrl G' d m : ℕ}
    (v : Var)
    (hd : d ≤ 10) (hN : 1 < N) (table : Fin (G' + 1) → Bool → Fin N → ℕ) (rSpin : QRegister N n)
    (rCtrlTail : QRegister k_ctrl n) (hsc : rSpin.DisjointWires rCtrlTail) (actIdx : Fin k_ctrl)
    (selHot' : QRegister G' k_ctrl) (subIdx : Fin k_ctrl) (wHot0 : Wire n) (rCat : QRegister 11 n)
    (rWork : QRegister m n) (hm : 22 - d ≤ m)
    (hac : (rSpin.concat rCtrlTail hsc).DisjointWires rCat)
    (hWork0 : rWork.DisjointWires (QRegister.singleton wHot0))
    (hdisjPlus : ((rSpin.concat rCtrlTail hsc).concat rCat hac).DisjointWires
      (rWork.concat (QRegister.singleton wHot0) hWork0)) :
    (compactLac2CascadeCtrl22Dyn v hd hN table rSpin rCtrlTail hsc actIdx selHot' subIdx wHot0 rCat
      rWork hm hac hWork0 hdisjPlus).count .TOFF = 0 := by simp [compactLac2CascadeCtrl22Dyn]

@[simp] theorem count_compactLac2CascadeCtrl22Dyn_t {Var : Type} {n N k_ctrl G' d m : ℕ} (v : Var)
    (hd : d ≤ 10) (hN : 1 < N) (table : Fin (G' + 1) → Bool → Fin N → ℕ) (rSpin : QRegister N n)
    (rCtrlTail : QRegister k_ctrl n) (hsc : rSpin.DisjointWires rCtrlTail) (actIdx : Fin k_ctrl)
    (selHot' : QRegister G' k_ctrl) (subIdx : Fin k_ctrl) (wHot0 : Wire n) (rCat : QRegister 11 n)
    (rWork : QRegister m n) (hm : 22 - d ≤ m)
    (hac : (rSpin.concat rCtrlTail hsc).DisjointWires rCat)
    (hWork0 : rWork.DisjointWires (QRegister.singleton wHot0))
    (hdisjPlus : ((rSpin.concat rCtrlTail hsc).concat rCat hac).DisjointWires
      (rWork.concat (QRegister.singleton wHot0) hWork0)) :
    (compactLac2CascadeCtrl22Dyn v hd hN table rSpin rCtrlTail hsc actIdx selHot' subIdx wHot0 rCat
      rWork hm hac hWork0 hdisjPlus).count .T =
      2 * (N - 2) * (102 + 4 * d) + (98 + 4 * (d - 1)) := by simp [compactLac2CascadeCtrl22Dyn]

theorem diagProjSimulates_compactLac2CascadeCtrl22Dyn {Var : Type} [Fintype Var] [DecidableEq Var]
    {n N k_ctrl G' d m : ℕ} [NeZero (2 ^ n)] (v : Var) (hd : d ≤ 10) (hN : 1 < N)
    (table : Fin (G' + 1) → Bool → Fin N → ℕ) (rSpin : QRegister N n)
    (rCtrlTail : QRegister k_ctrl n) (hsc : rSpin.DisjointWires rCtrlTail) (actIdx : Fin k_ctrl)
    (selHot' : QRegister G' k_ctrl) (subIdx : Fin k_ctrl) (wHot0 : Wire n) (rCat : QRegister 11 n)
    (rWork : QRegister m n) (hm : 22 - d ≤ m)
    (hac : (rSpin.concat rCtrlTail hsc).DisjointWires rCat)
    (hWork0 : rWork.DisjointWires (QRegister.singleton wHot0))
    (hdisjPlus : ((rSpin.concat rCtrlTail hsc).concat rCat hac).DisjointWires
      (rWork.concat (QRegister.singleton wHot0) hWork0)) :
    let rSC := rSpin.concat rCat (OneHotMux.disj_sys_cat_of hsc hac)
    let rHot' := rCtrlTail.compose selHot'
    let fullHot (β : BitAssignment n) : Fin (G' + 1) → ZMod 2 :=
      Fin.cases (β wHot0) (fun g ↦ β (rHot' g))
    let S_valid (β : BitAssignment n) : Prop :=
      (∃ g₀ : Fin (G' + 1), UnsignedGivens.IsOneHotBits g₀ (fullHot β)) ∧ ∀ j : Fin m,
        β (rWork j) = 0
    ∃ wAff : Fin (2 ^ k_ctrl) → Unitary (2 ^ (N + 11)),
      DiagProjSimulates (ketPredProj S_valid)
        ((rSC.concat rCtrlTail (OneHotMux.disj_sysCat_ctrl_of hsc hac)).embedUnitary
          (UnsignedGivens.muxCtrlUnitary wAff))
        (compactLac2CascadeCtrl22Dyn v hd hN table rSpin rCtrlTail hsc actIdx selHot' subIdx wHot0
          rCat rWork hm hac hWork0 hdisjPlus) ∧
      ∀ (c : Fin (2 ^ k_ctrl)) (ψ : Fin (2 ^ N) → ℂ),
        (wAff c).1 *ᵥ prodState ψ (phaseGradientFineLow 11 3) =
          prodState
            ((affineUnsignedBilinearLac2CascadeCtrlUnitary hN table actIdx selHot' subIdx c).1
              *ᵥ ψ)
            (phaseGradientFineLow 11 3) := by
  intro rSC rHot' fullHot S_valid
  let rWorkPlus := rWork.concat (QRegister.singleton wHot0) hWork0
  have hne0 (g : Fin G') : rHot' g ≠ wHot0 := by
    simpa [rHot', rWorkPlus] using
      UnsignedGivens.ne_ctrl_work hsc hac hdisjPlus (selHot' g) (Fin.natAdd m 0)
  let cClear0 := clearHot0Circuit rHot' wHot0 hne0
  obtain ⟨wAff, hwAff, hcatAff⟩ := ctrlMuxCatalytic_compactLac2CascadeCtrlDyn v hd hN table rSpin
    rCtrlTail hsc actIdx selHot' subIdx rCat rWorkPlus (by omega) hac hdisjPlus
  have hSimAff : DiagProjSimulates (rWorkPlus.basisOutcomeProjector 0)
      ((rSC.concat rCtrlTail (OneHotMux.disj_sysCat_ctrl_of hsc hac)).embedUnitary
        (UnsignedGivens.muxCtrlUnitary wAff))
      (compactLac2CascadeCtrlDyn v hd hN table rSpin rCtrlTail hsc actIdx selHot' subIdx rCat
        rWorkPlus (by omega) hac hdisjPlus) :=
    DiagProjSimulates.ofGlobalCleanSimulates <|
      GlobalCleanSimulates.ofRealizesEmbedded
        (OneHotMux.disj_sysCatCtrl_work_of hsc hac hdisjPlus) hwAff
  have hClearSq : cClear0.eval * cClear0.eval = 1 :=
    clearHot0Circuit_eval_mul_self rHot' wHot0 hne0
  have hConj := hSimAff.conjSelfInv cClear0 hClearSq
    (fun β ↦ ⟨_, evolve_clearHot0Circuit_ket rHot' wHot0 hne0 β⟩)
  have hNotSC0 : wHot0 ∉ Set.range rSC.wires := by
    rintro ⟨sc, hsc0⟩; revert hsc0; refine Fin.addCases (fun i hsc0 ↦ ?_) (fun j hsc0 ↦ ?_) sc
    · exact UnsignedGivens.ne_spin_work hsc hac hdisjPlus i (Fin.natAdd m 0)
        (by simpa [rSC] using hsc0)
    · exact UnsignedGivens.ne_cat_work hsc hac hdisjPlus j (Fin.natAdd m 0)
        (by simpa [rSC] using hsc0)
  have hNotCtrl0 (j : Fin k_ctrl) : rCtrlTail j ≠ wHot0 := by
    simpa [rWorkPlus] using UnsignedGivens.ne_ctrl_work hsc hac hdisjPlus j (Fin.natAdd m 0)
  rw [clearHot0Circuit_conj_muxCtrlUnitary_eq rSC rCtrlTail
    (OneHotMux.disj_sysCat_ctrl_of hsc hac) selHot' wHot0 hNotSC0 hNotCtrl0 wAff] at hConj
  refine ⟨wAff, hConj.tighten ⟨S_valid, rfl⟩ ?_ ?_, hcatAff⟩
  · apply UnsignedGivens.matrix_ext_ket; intro β; classical
    rw [← Matrix.mulVec_mulVec]
    have hket_eq : @UnsignedGivens.ket n = @OneHotSimulates.ket n := rfl
    by_cases hS : S_valid β
    · have ⟨⟨g₀, hg₀⟩, hw0⟩ := hS
      let β₁ := Function.update β wHot0 (β wHot0 + (1 + ∑ g : Fin G', β (rHot' g)))
      have hk1 : cClear0.eval.1.mulVec (UnsignedGivens.ket β) = UnsignedGivens.ket β₁ :=
        evolve_clearHot0Circuit_ket rHot' wHot0 hne0 β
      have hP0 : (rWorkPlus.basisOutcomeProjector 0).mulVec (UnsignedGivens.ket β₁) =
          UnsignedGivens.ket β₁ := by
        rw [UnsignedGivens.register_basisOutcomeProjector_zero_ket,
          ite_eq_left_of_eq_true _ _ (eq_true ?_)]
        intro idx; refine Fin.addCases (fun j ↦ ?_) (fun z ↦ ?_) idx
        · dsimp only [rWorkPlus, β₁]; rw [QRegister.concat_apply_left]
          rw [Function.update_of_ne (fun heq ↦ QRegister.disjoint_iff.mp hWork0 j 0
            (heq.trans (QRegister.singleton_apply _ _).symm)), hw0 j]
        · fin_cases z; dsimp only [rWorkPlus, β₁]
          rw [QRegister.concat_apply_right, QRegister.singleton_apply, Function.update_self]
          exact (clearHot0_zero_of_isOneHot hg₀).1
      have hClearMat : cClear0.eval.1 * cClear0.eval.1 = 1 := congrArg Subtype.val hClearSq
      have hk2 : cClear0.eval.1.mulVec (UnsignedGivens.ket β₁) = UnsignedGivens.ket β := by
        rw [← hk1, Matrix.mulVec_mulVec, hClearMat, Matrix.one_mulVec]
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hk1, hP0, hk2, hket_eq,
        ketPredProj_mulVec_ket, ite_posE hS]
    · have hcommP := (show IsDiagProj (ketPredProj S_valid) from ⟨S_valid, rfl⟩).comm hConj.1
      rw [Matrix.mulVec_mulVec, hcommP, ← Matrix.mulVec_mulVec, hket_eq, ketPredProj_mulVec_ket]
      simp only [hS, ↓reduceIte, Matrix.mulVec_zero]
  · apply UnsignedGivens.matrix_ext_ket; intro β; classical
    have hket_eq : @UnsignedGivens.ket n = @OneHotSimulates.ket n := rfl
    have hwreg_eq : @UnsignedGivens.writeReg n (N + 11) = @OneHotSimulates.writeReg n (N + 11) :=
      rfl
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hket_eq, ketPredProj_mulVec_ket]
    have hinv (γ : Fin (N + 11) → ZMod 2) : S_valid (UnsignedGivens.writeReg β rSC γ) ↔
        S_valid β := by
      have hf : fullHot (UnsignedGivens.writeReg β rSC γ) = fullHot β := by
        funext k; cases k using Fin.cases with
        | zero => exact UnsignedGivens.writeReg_apply_of_not_mem _ _ _ _ hNotSC0
        | succ g =>
            exact UnsignedGivens.writeReg_apply_of_not_mem _ _ _ _ fun ⟨sc, hsc_eq⟩ ↦
              QRegister.disjoint_iff.mp (OneHotMux.disj_sysCat_ctrl_of hsc hac) sc
                (selHot' g) hsc_eq
      have hw (j : Fin m) : UnsignedGivens.writeReg β rSC γ (rWork j) = β (rWork j) :=
        UnsignedGivens.writeReg_apply_of_not_mem _ _ _ _ fun ⟨sc, hsc_eq⟩ ↦
          QRegister.disjoint_iff.mp (OneHotMux.disj_sysCatCtrl_work_of hsc hac hdisjPlus)
            (Fin.castAdd k_ctrl sc) (Fin.castAdd 1 j)
            (by simpa [rSC, rWorkPlus, QRegister.concat_apply_left] using hsc_eq)
      simp only [S_valid, hf, hw]
    by_cases hS : S_valid β
    · simp only [hS, ↓reduceIte];
        rw [← hket_eq, UnsignedGivens.embedUnitary_muxCtrlUnitary_mulVec_ket,
        QRegister.embedUnitary_val, hket_eq, OneHotSimulates.embedMatrix_mulVec_ket, ← hwreg_eq,
        Matrix.mulVec_sum]
      refine Finset.sum_congr rfl fun l _ ↦ ?_
      rw [Matrix.mulVec_smul, ketPredProj_mulVec_ket]; simp only [(hinv _).mpr hS, ↓reduceIte]
    · simp only [hS, ↓reduceIte, Matrix.mulVec_zero]
      rw [← hket_eq, UnsignedGivens.embedUnitary_muxCtrlUnitary_mulVec_ket,
        QRegister.embedUnitary_val,
        hket_eq, OneHotSimulates.embedMatrix_mulVec_ket, ← hwreg_eq, Matrix.mulVec_sum]
      symm; refine Finset.sum_eq_zero fun l _ ↦ ?_
      rw [Matrix.mulVec_smul, ketPredProj_mulVec_ket]
      simp only [mt (hinv _).mp hS, ↓reduceIte, smul_zero]

attribute [irreducible] compactLac2CascadeCtrl22Dyn

end CompactAffineCascade

end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.PhaseB154Pi145Select

end
