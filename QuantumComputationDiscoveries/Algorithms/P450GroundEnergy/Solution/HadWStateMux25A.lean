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
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.ZeroCmp20Reduced2504
/-!
# Compact `26-T` `W`-State Packet Phase Kickback
Subspace `wp`, `4-T` `wSplitPair4` `1`-hot `W`-state expansion and measurement-based
uncomputation, `26-T` `gatedKeepKickback25Dyn` (`11` scratch) and `gatedKeepKickback30Dyn`
(`16` scratch), plus the `(p0, sKick)` `andSandwichDyn` phase-polynomial loop `andLoopGenDyn`.
## References
- C. Jones, *Phys. Rev. A* **87**, 022328 (2013), DOI: 10.1103/PhysRevA.87.022328.
- C. Gidney, *Quantum* **2**, 74 (2018), DOI: 10.22331/q-2018-06-18-74.
- R. Babbush et al., *Phys. Rev. X* **8**, 041015 (2018), DOI: 10.1103/PhysRevX.8.041015.
-/
@[expose] public section
namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.HadWStateMux25CompactA
open QuantumComputation.Specs QuantumComputation.Specs.P450
open Operator QProg Matrix Circuit Real HermitianMat BlockEncodingCore BlockEncodingCircuit
  QuantumComputation.Specs Solution QuantumComputation.Specs.P450 Solution CoherentAlias AliasPrep
    TopIntegrationBridge
  Phase2MidSandwich CompactBilinearPrep MidReflCtxRetain OptXMeasUnload21
  OptFactoredMag30AndCoin9 Cat11CompactPhase2Bridge ReordOuter13Bridge ZeroRcHotPrepMid21Fast
  Tuned162ScheduledSympQrom21 OptStepSympAnfQrom21 Tuned162StepSympAnfQrom21
  OptU2Grover184PrepOut13 MobiusOptSubcube163Walk CompactTuned162StepWalk
  CompactTuned162StepZeroCmp20 CompactZeroCmp20OuterParam CompactStepZeroCmp20OuterParam
  StepAnfAndCoin14Core CompactStepCompact2504ZeroCmp20
open scoped Matrix BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator Circuit.Notation
local instance (priority := 1000000) instNeZeroTwoPowHad25 (k : ℕ) : NeZero (2 ^ k) :=
  ⟨pow_ne_zero k two_ne_zero⟩
theorem ite_posHad {c : Prop} [Decidable c] (hc : c) {α : Sort*} {t e : α} :
    ite c t e = t := by simp [hc]
theorem identity_eval_mulVecHad {n : ℕ} (ψ : Fin (2 ^ n) → ℂ) : (Circuit.identity : Circuit
    n).eval.1.mulVec ψ = ψ := by rw [Circuit.eval_identity, Submonoid.coe_one, Matrix.one_mulVec]
theorem update_bit_eq_selfHad {n : ℕ} {γ : BitAssignment n} {w : Wire n} {v : ZMod 2} (h : γ w =
    v) : Function.update γ w v = γ := (congrArg (Function.update γ w) h.symm).trans
    (Function.update_eq_self w γ)
/-- Classical variable `v`-invariance of a classical-quantum assertion `Θ`. -/
abbrev IsVInvHad {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ} (v : Var) (Θ : QCAssertion
    Var (2 ^ n)) : Prop := ∀ σ val, Θ (Function.update σ v val) = Θ σ
/-- Partial-isometry operator mapping `|β⟩ ↦ f β` on `S β` and `0` otherwise. -/
noncomputable def ketMapOpHad {n : ℕ} (S : BitAssignment n → Prop) (f : BitAssignment n → (Fin (2
    ^ n) → ℂ)) : Operator (2 ^ n) := open Classical in Matrix.of fun i j ↦ if S (basisBits n j) then
    f (basisBits n j) i else 0
/-- Subspace `wp`-intertwining predicate for dynamic `W`-state stages and MBU decoders. -/
def HadSubspaceStepV {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ} (v : Var) (R₀ R₁ :
    Operator (2 ^ n)) (d : DynamicCircuit Var n) : Prop := d.count .TOFF = 0 ∧ ∀ Θ : QCAssertion Var
    (2 ^ n), IsVInvHad v Θ → IsVInvHad v (wp d.compile Θ) ∧ ∀ σ : Store Var, R₀ᴴ * (wp d.compile
    Θ σ).1.1 * R₀ = R₁ᴴ * (Θ σ).1.1 * R₁
theorem ketMapOpHad_mulVec_ket {n : ℕ} (S : BitAssignment n → Prop) (f : BitAssignment n → (Fin
    (2 ^ n) → ℂ)) (β : BitAssignment n) : (ketMapOpHad S f).mulVec (Solution.XMeasCircuit.ket β) =
    open Classical in if S β then f β else 0 := by
  classical ext i
  have h1 : (ketMapOpHad S f).mulVec (Solution.XMeasCircuit.ket β) i =
      ketMapOpHad S f i ((basisBits n).symm β) := by simp [Solution.XMeasCircuit.ket, basisState]
  rw [h1];
    simp only [ketMapOpHad, Matrix.of_apply, Solution.XMeasCircuit.basisBits_basisBitsEquiv_symm]
  by_cases hS : S β <;> simp [hS]
theorem mul_ketMapOpHad {n : ℕ} (A : Operator (2 ^ n)) (S : BitAssignment n → Prop) (f :
    BitAssignment n → (Fin (2 ^ n) → ℂ)) : A * ketMapOpHad S f = ketMapOpHad S (fun β ↦ A.mulVec
    (f β)) := by
  classical refine Solution.XMeasCircuit.matrix_ext_ket fun β ↦ ?_
  rw [← Matrix.mulVec_mulVec, ketMapOpHad_mulVec_ket, ketMapOpHad_mulVec_ket]
  by_cases hS : S β <;> simp [hS]
theorem smul_ketMapOpHad {n : ℕ} (c : ℂ) (S : BitAssignment n → Prop) (f : BitAssignment n → (Fin
    (2 ^ n) → ℂ)) : c • ketMapOpHad S f = ketMapOpHad S (fun β ↦ c • f β) := by
  classical refine Solution.XMeasCircuit.matrix_ext_ket fun β ↦ ?_
  rw [Matrix.smul_mulVec, ketMapOpHad_mulVec_ket, ketMapOpHad_mulVec_ket]
  by_cases hS : S β <;> simp [hS]
theorem ketMapOpHad_congr {n : ℕ} {S : BitAssignment n → Prop} {f g : BitAssignment n → (Fin (2 ^
    n) → ℂ)} (h : ∀ β, S β → f β = g β) : ketMapOpHad S f = ketMapOpHad S g := by
  classical refine Solution.XMeasCircuit.matrix_ext_ket fun β ↦ ?_
  rw [ketMapOpHad_mulVec_ket, ketMapOpHad_mulVec_ket]; by_cases hS : S β <;> simp [hS, h β]
theorem ketMapOpHad_ket_eq_diagonal {n : ℕ} (S : BitAssignment n → Prop) : ketMapOpHad S
    Solution.XMeasCircuit.ket = open Classical in Matrix.diagonal fun i : Fin (2 ^ n) ↦
      if S (basisBits n i)
    then 1 else 0 := by
  classical ext i j
  simp only [ketMapOpHad, Matrix.of_apply, Matrix.diagonal_apply, Solution.XMeasCircuit.ket,
    basisState,
    Solution.XMeasCircuit.basisBitsEquiv_symm_basisBits]
  by_cases hij : i = j
  · subst hij; by_cases hS : S (basisBits n i) <;> simp [hS]
  · by_cases hS : S (basisBits n j) <;> simp [hS, hij]
theorem ketMapOpHad_ket_conjTranspose {n : ℕ} (S : BitAssignment n → Prop) : (ketMapOpHad S
    Solution.XMeasCircuit.ket)ᴴ = ketMapOpHad S Solution.XMeasCircuit.ket := by
  classical rw [ketMapOpHad_ket_eq_diagonal, Matrix.diagonal_conjTranspose]
  congr 1; funext i; by_cases hS : S (basisBits n i) <;> simp [hS]
theorem HadSubspaceStepV.seq {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ} {v : Var} {R₀ R₁
    R₂ : Operator (2 ^ n)} {d₁ d₂ : DynamicCircuit Var n} (h₁ : HadSubspaceStepV v R₀ R₁ d₁) (h₂ :
    HadSubspaceStepV v R₁ R₂ d₂) : HadSubspaceStepV v R₀ R₂ (.seq d₁ d₂) :=
  ⟨by simp [DynamicCircuit.count, h₁.1, h₂.1], fun Θ hΘ ↦ by
    obtain ⟨hInv₂, heq₂⟩ := h₂.2 Θ hΘ
    obtain ⟨hInv₁, heq₁⟩ := h₁.2 (wp d₂.compile Θ) hInv₂
    have hseq : wp (d₁.seq d₂).compile Θ = wp d₁.compile (wp d₂.compile Θ) := by
      rw [DynamicCircuit.compile_seq, wp_qSeq]
    rw [hseq]; exact ⟨hInv₁, fun σ ↦ (heq₁ σ).trans (heq₂ σ)⟩⟩
theorem HadSubspaceStepV.of_circuit {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ} {v : Var}
    {R₀ R₁ : Operator (2 ^ n)} (c : Circuit n) (hc0 : c.count .TOFF = 0) (hc : c.eval.1 * R₀ = R₁) :
    HadSubspaceStepV v R₀ R₁ (.circuit c) := ⟨hc0, fun Θ hΘ ↦ by
    have hwp (σ : Store Var) : wp (DynamicCircuit.circuit c).compile Θ σ = qcQAssignObsMap c.eval (Θ
      σ) := by
      rw [DynamicCircuit.compile_circuit, DynamicCircuit.qc_wp_circuit_compile (Var := Var),
        qcWpQAssign]
    refine ⟨fun σ val ↦ by rw [hwp, hwp, hΘ σ val], fun σ ↦ ?_⟩
    have hM : (qcQAssignObsMap c.eval (Θ σ)).1.1 = c.eval.1ᴴ * (Θ σ).1.1 * c.eval.1 := by
      simp [qcQAssignObsMap, Matrix.star_eq_conjTranspose]
    have hadj : R₀ᴴ * c.eval.1ᴴ = R₁ᴴ := by
      simpa only [Matrix.conjTranspose_mul] using congrArg Matrix.conjTranspose hc
    rw [hwp, hM]
    calc R₀ᴴ * (c.eval.1ᴴ * (Θ σ).1.1 * c.eval.1) * R₀
        = (R₀ᴴ * c.eval.1ᴴ) * (Θ σ).1.1 * (c.eval.1 * R₀) := by simp only [Matrix.mul_assoc]
      _ = R₁ᴴ * (Θ σ).1.1 * R₁ := by rw [hadj, hc]⟩
theorem HadSubspaceStepV.remeasure {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ} {v : Var}
    {R₀ R₁ : Operator (2 ^ n)} (q : Wire n) (onOne : DynamicCircuit Var n) (h0 :
    (QRegister.singleton q).basisOutcomeProjector 0 * R₀ = Solution.XMeasCircuit.sqrtHalf •
      R₁) (h1 :
    HadSubspaceStepV v ((QRegister.singleton q).basisOutcomeProjector 1 *
      R₀) (Solution.XMeasCircuit.sqrtHalf
    • R₁) onOne) : HadSubspaceStepV v R₀ R₁ (Solution.XMeasCircuit.remeasureIfDyn v q onOne) :=
  ⟨by simp [h1.1], fun Θ hΘ ↦ by
    obtain ⟨hInv₁, heq₁⟩ := h1.2 Θ hΘ
    refine ⟨fun σ val ↦ Solution.XMeasCircuit.wp_remeasureIfDyn_update_self v q onOne Θ σ val,
      fun σ ↦ ?_⟩
    let P₀ := (QRegister.singleton q).basisOutcomeProjector 0
    let P₁ := (QRegister.singleton q).basisOutcomeProjector 1
    have hP₀h : P₀ᴴ = P₀ := QRegister.basisOutcomeProjector_conjTranspose _ 0
    have hP₁h : P₁ᴴ = P₁ := QRegister.basisOutcomeProjector_conjTranspose _ 1
    have hM' : (wp (Solution.XMeasCircuit.remeasureIfDyn v q onOne).compile Θ σ).1.1 = P₀ *
      (Θ σ).1.1 * P₀ᴴ +
      P₁ * (wp onOne.compile Θ σ).1.1 * P₁ᴴ := by
      have hv := Solution.XMeasCircuit.wp_remeasureIfDyn_apply v q onOne Θ σ
      rw [hΘ σ 0, hInv₁ σ 1] at hv; exact congrArg Subtype.val hv
    have h0Eq : (P₀ * R₀)ᴴ * (Θ σ).1.1 * (P₀ * R₀) =
        (Solution.XMeasCircuit.sqrtHalf • R₁)ᴴ * (Θ σ).1.1 * (Solution.XMeasCircuit.sqrtHalf •
          R₁) := by rw [h0]
    have hsum : R₀ᴴ * (wp (Solution.XMeasCircuit.remeasureIfDyn v q onOne).compile Θ σ).1.1 * R₀ =
      (P₀ * R₀)ᴴ *
      (Θ σ).1.1 * (P₀ * R₀) + (P₁ * R₀)ᴴ * (wp onOne.compile Θ σ).1.1 * (P₁ * R₀) := by
      rw [hM', hP₀h, hP₁h, Matrix.mul_add, Matrix.add_mul]
      simp only [Matrix.conjTranspose_mul, hP₀h, hP₁h, Matrix.mul_assoc]
    rw [hsum, h0Eq, heq₁ σ]
    simp only [Matrix.conjTranspose_smul, Solution.XMeasCircuit.star_sqrtHalf, Matrix.smul_mul,
      Matrix.mul_smul, smul_smul, ← add_smul, Solution.XMeasCircuit.sqrtHalf_mul_sqrtHalf];
        norm_num⟩
theorem HadSubspaceStepV.xMeasUnload_circuit {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    {v : Var} {R₁ : Operator (2 ^ n)} (q : Wire n) (f : BitAssignment n → ZMod 2) (hf : ∀ β b, f
    (Function.update β q b) = f β) (cFix : Circuit n) (hcFix0 : cFix.count .TOFF = 0) (hcFix :
    cFix.eval = Solution.XMeasCircuit.phaseFlipUnitary f) (hClean :
      Solution.XMeasCircuit.cleanFinsetProj {q} * R₁ = R₁) :
    HadSubspaceStepV v ((Solution.XMeasCircuit.xorWireUnitary q f hf).1 * R₁) R₁
    (Solution.XMeasCircuit.xMeasUnloadWireDyn v q (.circuit cFix)) := by
  let Uxor := (Solution.XMeasCircuit.xorWireUnitary q f hf).1
  let Hq := (Circuit.H q).eval.1; let Xq := (Circuit.X q).eval.1
  let P₀ := (QRegister.singleton q).basisOutcomeProjector 0
  let P₁ := (QRegister.singleton q).basisOutcomeProjector 1
  have hmem : q ∈ ({q} : Finset (Wire n)) := Finset.mem_singleton_self q
  refine HadSubspaceStepV.seq (HadSubspaceStepV.of_circuit (Circuit.H q) rfl rfl)
    (HadSubspaceStepV.remeasure q _ ?_ ?_)
  · calc P₀ * (Hq * (Uxor * R₁))
        = ((P₀ * Hq) * Uxor * Solution.XMeasCircuit.cleanFinsetProj {q}) * R₁ := by
            nth_rw 1 [← hClean]; simp only [Matrix.mul_assoc]
      _ = (Solution.XMeasCircuit.sqrtHalf • Solution.XMeasCircuit.cleanFinsetProj {q}) * R₁ := by
            rw [Solution.XMeasCircuit.xMeas_kraus_zero q {q} hmem f hf]
      _ = Solution.XMeasCircuit.sqrtHalf • R₁ := by rw [Matrix.smul_mul, hClean]
  · refine HadSubspaceStepV.seq (HadSubspaceStepV.of_circuit (Circuit.X q) rfl rfl)
      (HadSubspaceStepV.of_circuit cFix hcFix0 ?_)
    have hkr1 := Solution.XMeasCircuit.xMeas_kraus_one q {q} hmem f hf
    have hsq : (Solution.XMeasCircuit.phaseFlipUnitary f).1 *
      (Solution.XMeasCircuit.phaseFlipUnitary f).1 = 1 := congrArg
      Subtype.val (Solution.XMeasCircuit.phaseFlipUnitary_mul_self f)
    calc cFix.eval.1 * (Xq * (P₁ * (Hq * (Uxor * R₁))))
        = cFix.eval.1 * (((Xq * P₁ * Hq) * Uxor * Solution.XMeasCircuit.cleanFinsetProj {q}) *
            R₁) := by
            nth_rw 1 [← hClean]; simp only [Matrix.mul_assoc]
      _ = (Solution.XMeasCircuit.phaseFlipUnitary f).1 *
            ((Solution.XMeasCircuit.sqrtHalf • (Solution.XMeasCircuit.cleanFinsetProj {q} *
              (Solution.XMeasCircuit.phaseFlipUnitary f).1)) * R₁) := by rw [hcFix, hkr1]
      _ = Solution.XMeasCircuit.sqrtHalf •
            (((Solution.XMeasCircuit.phaseFlipUnitary f).1 *
              (Solution.XMeasCircuit.cleanFinsetProj {q} *
              (Solution.XMeasCircuit.phaseFlipUnitary f).1)) * R₁) := by
            rw [Matrix.smul_mul, Matrix.mul_smul, ← Matrix.mul_assoc]
      _ = Solution.XMeasCircuit.sqrtHalf • R₁ := by
            rw [← Matrix.mul_assoc (Solution.XMeasCircuit.phaseFlipUnitary f).1,
              Solution.XMeasCircuit.phaseFlipUnitary_comm_cleanFinsetProj f {q}, Matrix.mul_assoc
              (Solution.XMeasCircuit.cleanFinsetProj {q}), hsq, Matrix.mul_one, hClean]
/-- Primitive eighth root of unity `(1 + i) / √2`. -/
noncomputable def omega8HadW : ℂ := (1 + Complex.I) / (√2 : ℂ)
theorem omega8HadW_eq : omega8HadW = (1 + Complex.I) * Solution.XMeasCircuit.sqrtHalf := by
  dsimp only [omega8HadW, Solution.XMeasCircuit.sqrtHalf]
  have h2 : (√2 : ℂ) ≠ 0 := by exact_mod_cast Real.sqrt_ne_zero'.mpr (by norm_num)
  have hmul : (√(1 / 2 : ℝ) : ℂ) * (√2 : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, ← Real.sqrt_mul (by norm_num)]; norm_num
  rw [div_eq_iff h2, mul_assoc, hmul, mul_one]
theorem sqrtHalf_sqHad : Solution.XMeasCircuit.sqrtHalf ^ 2 = 1 / 2 := by
  linear_combination Solution.XMeasCircuit.sqrtHalf_mul_sqrtHalf
theorem sqrtHalf_pow3Had : Solution.XMeasCircuit.sqrtHalf ^ 3 = (1 / 2) *
    Solution.XMeasCircuit.sqrtHalf := by
  linear_combination Solution.XMeasCircuit.sqrtHalf * sqrtHalf_sqHad
theorem sqrtHalf_pow4Had : Solution.XMeasCircuit.sqrtHalf ^ 4 = 1 / 4 := by
  linear_combination (Solution.XMeasCircuit.sqrtHalf ^ 2 + 1 / 2) * sqrtHalf_sqHad
theorem i_pow3Had : Complex.I ^ 3 = -Complex.I := by linear_combination Complex.I * Complex.I_sq
theorem i_pow4Had : Complex.I ^ 4 = 1 := by linear_combination (Complex.I ^ 2 - 1) * Complex.I_sq
theorem ket_SHad {n : ℕ} (q : Wire n) (β : BitAssignment n) : (Circuit.S q).eval.1.mulVec
    (Solution.XMeasCircuit.ket β) = (if β q = 0 then (1 : ℂ) else Complex.I) •
        Solution.XMeasCircuit.ket β := by
  rw [Circuit.eval_single, QRegister.embedUnitary_val, PrimitiveGate.eval]
  change ((QRegister.singleton q).embedMatrix !![1, 0; 0, Complex.I]).mulVec _ = _
  rw [Solution.XMeasCircuit.singleton_embedMatrix_mulVec_ket]
  have e := Function.update_eq_self q β
  rcases Solution.CircuitModular.UnsignedGivens.zmod2_eq_zero_or_one (β q) with hb | hb <;>
    rw [hb] at e <;> simp [hb, e]
theorem ket_THad {n : ℕ} (q : Wire n) (β : BitAssignment n) : (Circuit.T q).eval.1.mulVec
    (Solution.XMeasCircuit.ket β) = (if β q = 0 then (1 : ℂ) else omega8HadW) •
        Solution.XMeasCircuit.ket β := by
  rw [Circuit.eval_single, QRegister.embedUnitary_val, PrimitiveGate.eval]
  change ((QRegister.singleton q).embedMatrix !![1, 0; 0, omega8HadW]).mulVec _ = _
  rw [Solution.XMeasCircuit.singleton_embedMatrix_mulVec_ket]
  have e := Function.update_eq_self q β
  rcases Solution.CircuitModular.UnsignedGivens.zmod2_eq_zero_or_one (β q) with hb | hb <;>
    rw [hb] at e <;> simp [hb, e]
theorem ket_CNOTHad {n : ℕ} (c t : Wire n) (h : c ≠ t) (β : BitAssignment n) : (Circuit.CNOT c t
    h).eval.1.mulVec (Solution.XMeasCircuit.ket β) =
      Solution.XMeasCircuit.ket (Function.update β t (β t + β c)) :=
    Solution.CircuitModular.UnsignedGivens.evolve_CNOT_ket c t h β
theorem eval_seq_mulVecHad {n : ℕ} (c₁ c₂ : Circuit n) (ψ : Fin (2 ^ n) → ℂ) : (c₁ ;;ᶜ
    c₂).eval.1.mulVec ψ = c₂.eval.1.mulVec (c₁.eval.1.mulVec ψ) := by
  rw [Circuit.eval_seq, Submonoid.coe_mul, ← Matrix.mulVec_mulVec]
theorem wSplitPair4_mulVec_ket_00Had {n : ℕ} (a b : Wire n) (h : a ≠ b) {β : BitAssignment n} (ha
    : β a = 0) (hb : β b = 0) : (wSplitPair4 a b h).eval.1.mulVec (Solution.XMeasCircuit.ket β) =
    Solution.XMeasCircuit.ket β := by
  have hub0 : Function.update β b 0 = β := Function.update_eq_self_iff.mpr hb.symm
  have hua0 : Function.update β a 0 = β := Function.update_eq_self_iff.mpr ha.symm
  have h10 : ((1 : ZMod 2) = 0) = False := by decide
  simp only [wSplitPair4, eval_seq_mulVecHad, ket_SHad, ket_THad, Solution.XMeasCircuit.ket_H,
    Solution.XMeasCircuit.ket_Z, ket_CNOTHad, Matrix.mulVec_smul, Matrix.mulVec_add, ha, hb, h10,
    ↓reduceIte, one_smul, add_zero, zero_add, Function.update_self, Function.update_idem,
    Function.update_of_ne h, hub0, hua0, Solution.XMeasCircuit.bitSign, smul_add, smul_smul]
  rw [add_add_add_comm, ← add_smul, ← add_smul]
  refine (congrArg₂ (· + ·) (congrArg (· • _) (?_ : _ = (1 : ℂ))) (congrArg (· • _) (?_ : _ = (0 :
    ℂ)))).trans (by simp)
  · rw [omega8HadW_eq]; ring_nf
    simp only [sqrtHalf_sqHad, sqrtHalf_pow4Had, Complex.I_sq, i_pow3Had]; ring
  · rw [omega8HadW_eq]; ring_nf
    simp only [sqrtHalf_sqHad, sqrtHalf_pow4Had, Complex.I_sq, i_pow3Had, i_pow4Had]
    ring
theorem wSplitPair4_mulVec_ket_10Had {n : ℕ} (a b : Wire n) (h : a ≠ b) {β : BitAssignment n} (ha
    : β a = 1) (hb : β b = 0) : (wSplitPair4 a b h).eval.1.mulVec (Solution.XMeasCircuit.ket β) =
    Solution.XMeasCircuit.sqrtHalf • Solution.XMeasCircuit.ket β + Solution.XMeasCircuit.sqrtHalf •
      Solution.XMeasCircuit.ket (Function.update
    (Function.update β a 0) b 1) := by
  have hub0 : Function.update β b 0 = β := Function.update_eq_self_iff.mpr hb.symm
  have hua1 : Function.update β a 1 = β := Function.update_eq_self_iff.mpr ha.symm
  have h11 : (1 : ZMod 2) + 1 = 0 := rfl
  have h10 : ((1 : ZMod 2) = 0) = False := by decide
  have hcomm : Function.update (Function.update β b 1) a 0 = Function.update (Function.update β a 0)
    b 1 := Function.update_comm h.symm 1 0 β
  simp only [wSplitPair4, eval_seq_mulVecHad, ket_SHad, ket_THad, Solution.XMeasCircuit.ket_H,
    Solution.XMeasCircuit.ket_Z, ket_CNOTHad, Matrix.mulVec_smul, Matrix.mulVec_add, ha, hb, h11,
      h10,
    ↓reduceIte, one_smul, zero_add, add_zero, Function.update_self, Function.update_idem,
    Function.update_of_ne h, hub0, hua1, Solution.XMeasCircuit.bitSign, hcomm, smul_add, smul_smul]
  rw [add_add_add_comm, ← add_smul, ← add_smul]
  refine congrArg₂ (· + ·) (congrArg (· • _) ?_) (congrArg (· • _) ?_)
  · rw [omega8HadW_eq]; ring_nf; simp only [sqrtHalf_pow3Had, Complex.I_sq]; ring
  · rw [omega8HadW_eq]; ring_nf; simp only [sqrtHalf_pow3Had, Complex.I_sq, i_pow3Had]; ring
/-- Three-CNOT swap of distinct wires `a` and `b`. -/
def cnotSwap3HadW {n : ℕ} (a b : Wire n) (h : a ≠ b) : Circuit n := Circuit.CNOT a b h ;;ᶜ
    Circuit.CNOT b a h.symm ;;ᶜ Circuit.CNOT a b h
theorem cnotSwap3HadW_mulVec_ket {n : ℕ} (a b : Wire n) (h : a ≠ b) (γ : BitAssignment n) :
    (cnotSwap3HadW a b h).eval.1.mulVec (Solution.XMeasCircuit.ket γ) =
      Solution.XMeasCircuit.ket (Function.update
    (Function.update γ a (γ b)) b (γ a)) := by
  simp only [cnotSwap3HadW, eval_seq_mulVecHad, ket_CNOTHad]
  congr 1; funext w
  by_cases hwa : w = a
  · rw [hwa]
    simp only [Function.update_self, Function.update_of_ne h, Function.update_of_ne h.symm]
    rcases Solution.CircuitModular.UnsignedGivens.zmod2_eq_zero_or_one (γ a) with ha | ha <;> rcases
      Solution.CircuitModular.UnsignedGivens.zmod2_eq_zero_or_one (γ b) with hb | hb <;> rw [ha,
        hb] <;> decide
  · by_cases hwb : w = b
    · rw [hwb]
      simp only [Function.update_self, Function.update_of_ne h, Function.update_of_ne h.symm]
      rcases Solution.CircuitModular.UnsignedGivens.zmod2_eq_zero_or_one (γ a) with ha | ha <;>
        rcases
        Solution.CircuitModular.UnsignedGivens.zmod2_eq_zero_or_one (γ b) with hb | hb <;> rw [ha,
          hb] <;> decide
    · simp only [Function.update_of_ne hwa, Function.update_of_ne hwb]
theorem czCircuit_eval_eq_phaseFlipHad {n : ℕ} (w₁ w₂ : Wire n) (h : w₁ ≠ w₂) :
    (SelectSwapQROM.czCircuit w₁ w₂ h).eval = Solution.XMeasCircuit.phaseFlipUnitary (fun β ↦
      β w₁ * β w₂) :=
    by
  apply Subtype.ext; refine SelectSwapQROM.matrix_ext_ket fun β ↦ ?_
  have hket : SelectSwapQROM.ket β = Solution.XMeasCircuit.ket β := rfl
  have hbs : SelectSwapQROM.bitSign (β w₁ * β w₂) = Solution.XMeasCircuit.bitSign (β w₁ *
      β w₂) := by
    generalize β w₁ * β w₂ = x; fin_cases x <;> rfl
  rw [SelectSwapQROM.ket_czCircuit w₁ w₂ h β, hket, hbs,
    ← Solution.XMeasCircuit.phaseFlipUnitary_mulVec_ket
    (fun β ↦ β w₁ * β w₂) β]
@[simp] theorem zmod2_add_selfHad (x : ZMod 2) : x + x = 0 := by fin_cases x <;> decide
@[simp] theorem zmod2_add_cancel_rightHad (x y : ZMod 2) : x + y + y = x := by
  rw [add_assoc, zmod2_add_selfHad, add_zero]
/-- Two-`T` controlled Hadamard `ctrlH` placed on distinct wires `(a, b)`. -/
def hadCtrlHPair {n} (a b : Wire n) (h : a ≠ b) : Circuit n := ctrlH.onRegister (QRegister.pair a
    b h)
@[simp] theorem countHadCtrlHPair_t {n} (a b : Wire n) (h) :
    (hadCtrlHPair a b h).count .T = 2 := by simp [hadCtrlHPair]
theorem hadCtrlHPair_mulVec_ket {n : ℕ} (a b : Wire n) (h : a ≠ b) (β : BitAssignment n) :
    (hadCtrlHPair a b h).eval.1.mulVec (Solution.XMeasCircuit.ket β) = if β a = 1 then (Circuit.H
    b).eval.1.mulVec (Solution.XMeasCircuit.ket β) else Solution.XMeasCircuit.ket β := by
  have hr : (QRegister.pair a b h).compose (QRegister.block 0 1 (by omega)) =
      QRegister.singleton a := by ext i; fin_cases i; rfl
  have hp (x : ZMod 2) : (((basisBits 1).symm (fun _ ↦ x) : Fin (2 ^ 1)).val == 1) =
      decide (x = 1) := by fin_cases x <;> decide
  have hH : (QRegister.singleton b).embedMatrix Qubit.H.1 = (Circuit.H b).eval.1 := by
    rw [Circuit.eval_single, QRegister.embedUnitary_val]; rfl
  rw [hadCtrlHPair, Circuit.eval_onRegister, eval_ctrlH, QRegister.embedUnitary_val]
  refine (ket_embed_predCtrlMatrix (m := 1) (QRegister.pair a b h) (fun c ↦ c.val == 1) Qubit.H.1
    β).trans ?_
  rw [hr, show (QRegister.pair a b h) (Fin.last 1) = b from rfl]
  change (if (((basisBits 1).symm (fun _ ↦ β a) : Fin (2 ^ 1)).val == 1) then
    ((QRegister.singleton b).embedMatrix Qubit.H.1).mulVec (Solution.XMeasCircuit.ket β) else _) = _
  rw [hp (β a), hH]
  by_cases ha : β a = 1 <;>
    simp only [ha, decide_true, decide_false, Bool.false_eq_true, ↓reduceIte]
theorem hadCtrlHPair_mulVec_ket_0 {n} (a b : Wire n) (h) {β : BitAssignment n} (ha : β a = 0) :
    (hadCtrlHPair a b h).eval.1.mulVec (Solution.XMeasCircuit.ket β) =
        Solution.XMeasCircuit.ket β := by
  rw [hadCtrlHPair_mulVec_ket, ha]; simp
theorem hadCtrlHPair_mulVec_ket_10 {n} (a b : Wire n) (h) {β : BitAssignment n} (ha : β a = 1) (hb
    : β b = 0) : (hadCtrlHPair a b h).eval.1.mulVec (Solution.XMeasCircuit.ket β) =
      Solution.XMeasCircuit.sqrtHalf •
    Solution.XMeasCircuit.ket β + Solution.XMeasCircuit.sqrtHalf •
        Solution.XMeasCircuit.ket (Function.update β b 1) := by
  rw [hadCtrlHPair_mulVec_ket, ha, ite_posHad rfl, Solution.XMeasCircuit.ket_H, hb,
    update_bit_eq_selfHad hb, Solution.XMeasCircuit.bitSign_zero, one_smul, smul_add]
/-- Build a `QRegister M n` from a concrete wire map `f` whose `List.ofFn f` is nodup. -/
def hadMkNodupReg {M n : ℕ} (f : Fin M → Wire n) (h : (List.ofFn f).Nodup) : QRegister M n := ⟨⟨f,
    List.nodup_ofFn.mp h⟩⟩
/-- Control wire `0` of a `(3 + U + R + R)`-wire stage configuration. -/
abbrev stgCtrl {U R n : ℕ} (cfg : QRegister (3 + U + R + R) n) : Wire n := cfg ⟨0, by omega⟩
/-- Null-indicator wire `1` (`uZero`) of a `(3 + U + R + R)`-wire stage configuration. -/
abbrev stgUZero {U R n : ℕ} (cfg : QRegister (3 + U + R + R) n) : Wire n := cfg ⟨1, by omega⟩
/-- Parity/measurement wire `2` (`qEnc`) of a `(3 + U + R + R)`-wire stage configuration. -/
abbrev stgQEnc {U R n : ℕ} (cfg : QRegister (3 + U + R + R) n) : Wire n := cfg ⟨2, by omega⟩
/-- `j`-th idle leaf wire (`3 + j`) of a `(3 + U + R + R)`-wire stage configuration. -/
abbrev stgIdle {U R n} (cfg : QRegister (3 + U + R + R) n) (j : Fin U) := cfg ⟨3 + j.val, by
    omega⟩
/-- `q`-th active parent wire (`3 + U + q`) of a `(3 + U + R + R)`-wire stage configuration. -/
abbrev stgLo {U R n} (cfg : QRegister (3 + U + R + R) n) (q : Fin R) := cfg ⟨3 + U + q.val, by
    omega⟩
/-- `q`-th fresh child wire (`3 + U + R + q`) of a `(3 + U + R + R)`-wire stage configuration. -/
abbrev stgHi {U R n} (cfg : QRegister (3 + U + R + R) n) (q : Fin R) := cfg ⟨3 + U + R + q.val, by
    omega⟩
theorem stg_ne {U R n} (cfg : QRegister (3 + U + R + R) n) {i j} (h : i.val ≠ j.val) : cfg i ≠ cfg
    j := cfg.wires.injective.ne (Fin.ne_of_val_ne h)
/-- CNOT sweep lumping (and unlumping) the first `m` `stgIdle` wires into `stgUZero` (`0 T`). -/
def lumpIdleCirc {U R n : ℕ} (cfg : QRegister (3 + U + R + R) n) : (m : ℕ) → m ≤ U → Circuit n
  | 0, _ => Circuit.identity
  | m + 1, hm => lumpIdleCirc cfg m (by omega) ;;ᶜ
      Circuit.CNOT (stgIdle cfg ⟨m, hm⟩) (stgUZero cfg) (stg_ne cfg (by dsimp; omega))
/-- Per-pair `wSplitPair4` + `CNOT` parity accumulation onto `stgQEnc` across `m ≤ R` pairs. -/
def splitAndParityCirc {U R n : ℕ} (cfg : QRegister (3 + U + R + R) n) : (m : ℕ) → m ≤ R → Circuit
    n
  | 0, _ => Circuit.identity
  | m + 1, hm => splitAndParityCirc cfg m (by omega) ;;ᶜ
      wSplitPair4 (stgLo cfg ⟨m, hm⟩) (stgHi cfg ⟨m, hm⟩) (stg_ne cfg (by dsimp; omega)) ;;ᶜ
      Circuit.CNOT (stgHi cfg ⟨m, hm⟩) (stgQEnc cfg) (stg_ne cfg (by dsimp; omega))
/-- Conditional 3-CNOT swap sweep across the first `m ≤ R` `(stgLo, stgHi)` pairs (`0 T`). -/
def swapPairsPhaseCirc {U R n : ℕ} (cfg : QRegister (3 + U + R + R) n) : (m : ℕ) → m ≤ R → Circuit
    n
  | 0, _ => Circuit.identity
  | m + 1, hm => swapPairsPhaseCirc cfg m (by omega) ;;ᶜ
      cnotSwap3HadW (stgLo cfg ⟨m, hm⟩) (stgHi cfg ⟨m, hm⟩) (stg_ne cfg (by dsimp; omega))
/-- Gated `W`-state doubling stage (`2 * R + 2` `T` gates). -/
def gatedPhaseDyn {Var : Type} {U R n : ℕ} (v : Var) (cfg : QRegister (3 + U + R + R) n) :
    DynamicCircuit Var n := .seq (.circuit (lumpIdleCirc cfg U le_rfl ;;ᶜ splitAndParityCirc cfg
    R le_rfl ;;ᶜ hadCtrlHPair (stgUZero cfg) (stgQEnc cfg) (stg_ne cfg (by dsimp; omega))
    ;;ᶜ Circuit.CNOT (stgCtrl cfg) (stgQEnc cfg) (stg_ne cfg (by dsimp; omega)))) (.seq
    (Solution.XMeasCircuit.remeasureIfDyn v (stgQEnc cfg) (.circuit (Circuit.X (stgQEnc cfg) ;;ᶜ
    swapPairsPhaseCirc cfg R le_rfl))) (.circuit (lumpIdleCirc cfg U le_rfl)))
/-- CNOT folding sweep from `stgHi q` onto `stgLo q` across `m ≤ R` pairs (`0 T`). -/
def foldPairsPhaseCirc {U R n : ℕ} (cfg : QRegister (3 + U + R + R) n) : (m : ℕ) → m ≤ R → Circuit
    n
  | 0, _ => Circuit.identity
  | m + 1, hm => foldPairsPhaseCirc cfg m (by omega) ;;ᶜ
      Circuit.CNOT (stgHi cfg ⟨m, hm⟩) (stgLo cfg ⟨m, hm⟩) (stg_ne cfg (by dsimp; omega))
/-- Top-down X-measurement unloading sweep across `stgHi [0, m)` (`0 T`). -/
def unloadPairsPhaseDyn {Var : Type} {U R n : ℕ} (v : Var) (cfg : QRegister (3 + U + R + R) n) :
    (m : ℕ) → m ≤ R → DynamicCircuit Var n
  | 0, _ => .circuit Circuit.identity
  | m + 1, hm => .seq (Solution.XMeasCircuit.xMeasUnloadWireDyn v (stgHi cfg ⟨m, hm⟩) (.circuit
      (SelectSwapQROM.czCircuit (stgCtrl cfg) (stgLo cfg ⟨m, hm⟩)
        (stg_ne cfg (by dsimp; omega))))) (unloadPairsPhaseDyn v cfg m (by omega))
/-- `0-T` MBU unstage combinator folding `stgHi` back into `stgLo` and X-measuring `stgHi`. -/
def gatedUnphaseDyn {Var : Type} {U R n : ℕ} (v : Var) (cfg : QRegister (3 + U + R + R) n) :
    DynamicCircuit Var n := .seq (.circuit (foldPairsPhaseCirc cfg R le_rfl))
    (unloadPairsPhaseDyn v cfg R le_rfl)
theorem countLumpIdleCirc_arity3 {U R n} (cfg : QRegister (3 + U + R + R) n) (g : PrimitiveGate
    3) : ∀ (m) (hm : m ≤ U), (lumpIdleCirc cfg m hm).count g = 0
  | 0, _ => rfl
  | m + 1, _ => by rw [lumpIdleCirc, count_seq, countLumpIdleCirc_arity3 cfg g m _]; rfl
theorem countSplitAndParityCirc_arity3 {U R n} (cfg : QRegister (3 + U + R + R) n) (g :
    PrimitiveGate 3) : ∀ (m) (hm : m ≤ R), (splitAndParityCirc cfg m hm).count g = 0
  | 0, _ => rfl
  | m + 1, _ => by simp [splitAndParityCirc, countSplitAndParityCirc_arity3 cfg g m _]; rfl
theorem countSwapPairsPhaseCirc_arity3 {U R n} (cfg : QRegister (3 + U + R + R) n) (g :
    PrimitiveGate 3) : ∀ (m) (hm : m ≤ R), (swapPairsPhaseCirc cfg m hm).count g = 0
  | 0, _ => rfl
  | m + 1, _ => by simp [swapPairsPhaseCirc, countSwapPairsPhaseCirc_arity3 cfg g m _]; rfl
@[simp] theorem countGatedPhaseDyn_arity3 {Var} {U R n} (v : Var) (cfg : QRegister (3 + U + R +
    R) n) (g : PrimitiveGate 3) : (gatedPhaseDyn v cfg).count g = 0 := by
  simp only [gatedPhaseDyn, DynamicCircuit.count, Solution.XMeasCircuit.count_remeasureIfDyn,
    count_seq,
    countLumpIdleCirc_arity3, countSplitAndParityCirc_arity3,
    countSwapPairsPhaseCirc_arity3, hadCtrlHPair, count_onRegister]; rfl
theorem countLumpIdleCirc_t {U R n} (cfg : QRegister (3 + U + R + R) n) : ∀ (m) (hm : m ≤ U),
    (lumpIdleCirc cfg m hm).count .T = 0
  | 0, _ => rfl
  | m + 1, _ => by rw [lumpIdleCirc, count_seq, countLumpIdleCirc_t cfg m _]; rfl
theorem countSplitAndParityCirc_t {U R n} (cfg : QRegister (3 + U + R + R) n) : ∀ (m) (hm : m ≤
    R), (splitAndParityCirc cfg m hm).count .T = 2 * m
  | 0, _ => rfl
  | m + 1, _ => by
      simp only [splitAndParityCirc, count_seq, countSplitAndParityCirc_t cfg m (by omega),
        count_wSplitPair4_t, show (Circuit.CNOT _ _ _).count .T = 0 from rfl]; omega
theorem countSwapPairsPhaseCirc_t {U R n} (cfg : QRegister (3 + U + R + R) n) : ∀ (m) (hm : m ≤
    R), (swapPairsPhaseCirc cfg m hm).count .T = 0
  | 0, _ => rfl
  | m + 1, _ => by simp [swapPairsPhaseCirc, countSwapPairsPhaseCirc_t cfg m _]; rfl
@[simp] theorem countGatedPhaseDyn_t {Var} {U R n} (v : Var) (cfg : QRegister (3 + U + R + R) n)
    : (gatedPhaseDyn v cfg).count .T = 2 * R + 2 := by
  simp only [gatedPhaseDyn, DynamicCircuit.count, Solution.XMeasCircuit.count_remeasureIfDyn,
    count_seq,
    countLumpIdleCirc_t, countSplitAndParityCirc_t, countHadCtrlHPair_t,
    countSwapPairsPhaseCirc_t, show (CNOT _ _ _).count .T = 0 from rfl, show (Circuit.X _).count
    .T = 0 from rfl]; omega
theorem countFoldPairsPhaseCirc_arity3 {U R n} (cfg : QRegister (3 + U + R + R) n) (g :
    PrimitiveGate 3) : ∀ (m) (hm : m ≤ R), (foldPairsPhaseCirc cfg m hm).count g = 0
  | 0, _ => rfl
  | m + 1, _ => by simp [foldPairsPhaseCirc, countFoldPairsPhaseCirc_arity3 cfg g m _]
theorem countUnloadPairsPhaseDyn_arity3 {Var} {U R n} (v : Var) (cfg : QRegister (3 + U + R + R)
    n) (g : PrimitiveGate 3) : ∀ (m) (hm : m ≤ R), (unloadPairsPhaseDyn v cfg m hm).count g = 0
  | 0, _ => rfl
  | m + 1, _ => by
      simp only [unloadPairsPhaseDyn, DynamicCircuit.count,
        Solution.XMeasCircuit.xMeasUnloadWireDyn,
        Solution.XMeasCircuit.count_remeasureIfDyn, countUnloadPairsPhaseDyn_arity3 v cfg g m _];
          rfl
@[simp] theorem countGatedUnphaseDyn_arity3 {Var} {U R n} (v : Var) (cfg : QRegister (3 + U + R +
    R) n) (g : PrimitiveGate 3) : (gatedUnphaseDyn v cfg).count g = 0 := by
  simp [gatedUnphaseDyn, DynamicCircuit.count, countFoldPairsPhaseCirc_arity3,
    countUnloadPairsPhaseDyn_arity3]
theorem countFoldPairsPhaseCirc_t {U R n} (cfg : QRegister (3 + U + R + R) n) : ∀ (m) (hm : m ≤
    R), (foldPairsPhaseCirc cfg m hm).count .T = 0
  | 0, _ => rfl
  | m + 1, _ => by simp [foldPairsPhaseCirc, countFoldPairsPhaseCirc_t cfg m _]
theorem countUnloadPairsPhaseDyn_t {Var} {U R n} (v : Var) (cfg : QRegister (3 + U + R + R) n) :
    ∀ (m) (hm : m ≤ R), (unloadPairsPhaseDyn v cfg m hm).count .T = 0
  | 0, _ => rfl
  | m + 1, _ => by
      simp [unloadPairsPhaseDyn, DynamicCircuit.count,
        Solution.XMeasCircuit.count_xMeasUnloadWireDyn_t,
        countUnloadPairsPhaseDyn_t v cfg m (by omega)]
@[simp] theorem countGatedUnphaseDyn_t {Var : Type} {U R n : ℕ} (v : Var) (cfg : QRegister (3 + U
    + R + R) n) : (gatedUnphaseDyn v cfg).count .T = 0 := by
  simp [gatedUnphaseDyn, DynamicCircuit.count, countFoldPairsPhaseCirc_t,
    countUnloadPairsPhaseDyn_t]
/-- Bit-assignment swapping `stgLo q` and `stgHi q` for `q < m`, leaving other wires fixed. -/
def swapPairsPrefixAssign {U R n : ℕ} (cfg : QRegister (3 + U + R + R) n) : (m : ℕ) → m ≤ R →
    BitAssignment n → BitAssignment n
  | 0, _, γ => γ
  | m + 1, hm, γ => let δ := swapPairsPrefixAssign cfg m (by omega) γ
      Function.update (Function.update δ (stgLo cfg ⟨m, hm⟩) (δ (stgHi cfg ⟨m, hm⟩)))
        (stgHi cfg ⟨m, hm⟩) (δ (stgLo cfg ⟨m, hm⟩))
/-- Full `R`-pair `(stgLo, stgHi)` swap on `BitAssignment n`. -/
abbrev swapPairsAssign {U R n : ℕ} (cfg : QRegister (3 + U + R + R) n) (γ : BitAssignment n) :=
    swapPairsPrefixAssign cfg R le_rfl γ
/-- Output bit-assignment of `gatedPhaseDyn`: swaps `(stgLo, stgHi)` iff `stgCtrl ≠ 0`. -/
def phaseStepAssign {U R n : ℕ} (cfg : QRegister (3 + U + R + R) n) (γ : BitAssignment n) :
    BitAssignment n := if γ (stgCtrl cfg) = 0 then γ else swapPairsAssign cfg γ
theorem swapPairsPhaseCirc_mulVec_ket {U R n : ℕ} (cfg : QRegister (3 + U + R + R) n) : ∀ (m) (hm
    : m ≤ R) (γ : BitAssignment n),
      (swapPairsPhaseCirc cfg m hm).eval.1.mulVec (Solution.XMeasCircuit.ket γ)
    = Solution.XMeasCircuit.ket (swapPairsPrefixAssign cfg m hm γ)
  | 0, _, _ => identity_eval_mulVecHad _
  | m + 1, hm, γ => by
      rw [swapPairsPhaseCirc, eval_seq_mulVecHad, swapPairsPhaseCirc_mulVec_ket cfg m (by
        omega) γ, cnotSwap3HadW_mulVec_ket]; rfl
theorem swapPairsPrefixAssign_of_not_pair {U R n : ℕ} (cfg : QRegister (3 + U + R + R) n) : ∀ (m)
    (hm : m ≤ R) (γ : BitAssignment n) (w : Wire n), (∀ q : Fin m, w ≠ stgLo cfg ⟨q.val, by omega⟩
    ∧ w ≠ stgHi cfg ⟨q.val, by omega⟩) → swapPairsPrefixAssign cfg m hm γ w = γ w
  | 0, _, _, _, _ => rfl
  | m + 1, hm, γ, w, hw => by
      simp only [swapPairsPrefixAssign, Function.update_of_ne (hw ⟨m, Nat.lt_succ_self m⟩).2,
        Function.update_of_ne (hw ⟨m, Nat.lt_succ_self m⟩).1]
      exact swapPairsPrefixAssign_of_not_pair cfg m (by omega) γ w fun q ↦ hw ⟨q.val,
        Nat.lt_succ_of_lt q.isLt⟩
theorem swapPairsPrefixAssign_lo {U R n : ℕ} (cfg : QRegister (3 + U + R + R) n) : ∀ (m) (hm : m ≤
    R) (γ : BitAssignment n) (q : Fin R), swapPairsPrefixAssign cfg m hm γ (stgLo cfg q) = if
    q.val < m then γ (stgHi cfg q) else γ (stgLo cfg q)
  | 0, _, _, _ => by simp [swapPairsPrefixAssign]
  | m + 1, hm, γ, q => by
      dsimp only [swapPairsPrefixAssign]
      rw [Function.update_of_ne (stg_ne cfg (by dsimp; omega))]
      by_cases hqm : q.val = m
      · have hqeq : q = ⟨m, hm⟩ := Fin.ext hqm; subst hqeq
        rw [Function.update_self, swapPairsPrefixAssign_of_not_pair cfg m (by omega) γ _ fun _ ↦
          ⟨stg_ne cfg (by dsimp; omega), stg_ne cfg (by dsimp; omega)⟩]; simp
      · rw [Function.update_of_ne (stg_ne cfg (by dsimp; omega)),
          swapPairsPrefixAssign_lo cfg m (by omega) γ q]
        simp [show (q.val < m + 1) ↔ (q.val < m) by omega]
theorem swapPairsPrefixAssign_hi {U R n : ℕ} (cfg : QRegister (3 + U + R + R) n) : ∀ (m) (hm : m ≤
    R) (γ : BitAssignment n) (q : Fin R), swapPairsPrefixAssign cfg m hm γ (stgHi cfg q) = if
    q.val < m then γ (stgLo cfg q) else γ (stgHi cfg q)
  | 0, _, _, _ => by simp [swapPairsPrefixAssign]
  | m + 1, hm, γ, q => by
      dsimp only [swapPairsPrefixAssign]; by_cases hqm : q.val = m
      · have hqeq : q = ⟨m, hm⟩ := Fin.ext hqm; subst hqeq
        rw [Function.update_self, swapPairsPrefixAssign_lo cfg m (by omega) γ ⟨m, hm⟩]; simp
      · rw [Function.update_of_ne (stg_ne cfg (by dsimp; omega)),
          Function.update_of_ne (stg_ne cfg (by dsimp; omega)),
          swapPairsPrefixAssign_hi cfg m (by omega) γ q]
        simp [show (q.val < m + 1) ↔ (q.val < m) by omega]
theorem swapPairsAssign_apply {U R n} (cfg : QRegister (3 + U + R + R) n) (γ : BitAssignment n) :
    (∀ q : Fin R, swapPairsAssign cfg γ (stgLo cfg q) = γ (stgHi cfg q)) ∧ (∀ q : Fin R,
    swapPairsAssign cfg γ (stgHi cfg q) = γ (stgLo cfg q)) ∧ (∀ w, (∀ q : Fin R, w ≠ stgLo
    cfg q ∧ w ≠ stgHi cfg q) → swapPairsAssign cfg γ w = γ w) :=
  ⟨fun q ↦ by simp [swapPairsAssign, swapPairsPrefixAssign_lo, q.isLt],
   fun q ↦ by simp [swapPairsAssign, swapPairsPrefixAssign_hi, q.isLt],
   fun w hw ↦ swapPairsPrefixAssign_of_not_pair cfg R le_rfl γ w fun q ↦ hw q⟩
theorem swapPairsAssign_prefix {U R n : ℕ} (cfg : QRegister (3 + U + R + R) n) (γ : BitAssignment
    n) {i : Fin (3 + U + R + R)} (hi : i.val < 3 + U) : swapPairsAssign cfg γ (cfg i) = γ (cfg i)
    := (swapPairsAssign_apply cfg γ).2.2 _ fun _ ↦ ⟨stg_ne cfg (by dsimp; omega), stg_ne cfg
    (by dsimp; omega)⟩
@[simp] theorem swapPairsAssign_ctrl {U R n} (cfg : QRegister (3 + U + R + R) n) (γ) :
    swapPairsAssign cfg γ (stgCtrl cfg) = γ (stgCtrl cfg) := swapPairsAssign_prefix cfg γ (i
    := ⟨0, by omega⟩) (by dsimp; omega)
@[simp] theorem swapPairsAssign_uZero {U R n} (cfg : QRegister (3 + U + R + R) n) (γ) :
    swapPairsAssign cfg γ (stgUZero cfg) = γ (stgUZero cfg) := swapPairsAssign_prefix cfg γ
    (i := ⟨1, by omega⟩) (by dsimp; omega)
@[simp] theorem swapPairsAssign_qEnc {U R n} (cfg : QRegister (3 + U + R + R) n) (γ) :
    swapPairsAssign cfg γ (stgQEnc cfg) = γ (stgQEnc cfg) := swapPairsAssign_prefix cfg γ (i
    := ⟨2, by omega⟩) (by dsimp; omega)
@[simp] theorem swapPairsAssign_idle {U R n} (cfg : QRegister (3 + U + R + R) n) (γ) (j : Fin U) :
    swapPairsAssign cfg γ (stgIdle cfg j) = γ (stgIdle cfg j) := swapPairsAssign_prefix cfg
    γ (i := ⟨3 + j.val, by omega⟩) (by have := j.isLt; dsimp; omega)
theorem swapPairsAssign_cases {U R n : ℕ} (cfg : QRegister (3 + U + R + R) n) (w : Wire n) {P :
    Wire n → Prop} (hLo : ∀ q, P (stgLo cfg q)) (hHi : ∀ q, P (stgHi cfg q)) (hOth : ∀ w, (∀ q,
    w ≠ stgLo cfg q ∧ w ≠ stgHi cfg q) → P w) : P w := by
  by_cases hl : ∃ q, w = stgLo cfg q
  · obtain ⟨q, rfl⟩ := hl; exact hLo q
  · by_cases hh : ∃ q, w = stgHi cfg q
    · obtain ⟨q, rfl⟩ := hh; exact hHi q
    · exact hOth w fun q ↦ ⟨fun h ↦ hl ⟨q, h⟩, fun h ↦ hh ⟨q, h⟩⟩
theorem stgAssign_ext {U R n : ℕ} (cfg : QRegister (3 + U + R + R) n) {f₁ f₂ : BitAssignment n}
    (hLo : ∀ q, f₁ (stgLo cfg q) = f₂ (stgLo cfg q)) (hHi : ∀ q, f₁ (stgHi cfg q) = f₂
    (stgHi cfg q)) (hOth : ∀ w, (∀ q, w ≠ stgLo cfg q ∧ w ≠ stgHi cfg q) → f₁ w = f₂ w) : f₁ =
    f₂ := funext fun w ↦ swapPairsAssign_cases (P := fun u ↦ f₁ u = f₂ u) cfg w hLo hHi hOth
theorem stgWire_eq {U R n : ℕ} (cfg : QRegister (3 + U + R + R) n) (f₁ f₂ : BitAssignment n) (w :
    Wire n) (hLo : ∀ q, f₁ (stgLo cfg q) = f₂ (stgLo cfg q)) (hHi : ∀ q, f₁ (stgHi cfg q) = f₂
    (stgHi cfg q)) (hOth : (∀ q, w ≠ stgLo cfg q ∧ w ≠ stgHi cfg q) → f₁ w = f₂ w) : f₁ w = f₂
    w := swapPairsAssign_cases (P := fun u ↦ u = w → f₁ u = f₂ u) cfg w (fun q _ ↦ hLo q) (fun q _
    ↦ hHi q) (fun _ hu huw ↦ huw ▸ hOth (huw ▸ hu)) rfl
theorem swapPairsAssign_invol {U R n : ℕ} (cfg : QRegister (3 + U + R + R) n) (γ : BitAssignment
    n) : swapPairsAssign cfg (swapPairsAssign cfg γ) = γ := funext fun w ↦
    swapPairsAssign_cases cfg w (fun q ↦ ((swapPairsAssign_apply cfg _).1 q).trans
    ((swapPairsAssign_apply cfg γ).2.1 q)) (fun q ↦ ((swapPairsAssign_apply cfg _).2.1 q).trans
    ((swapPairsAssign_apply cfg γ).1 q)) fun u hu ↦ ((swapPairsAssign_apply cfg _).2.2 u
    hu).trans ((swapPairsAssign_apply cfg γ).2.2 u hu)
theorem lumpIdleCirc_mulVec_ket {U R n : ℕ} (cfg : QRegister (3 + U + R + R) n) : ∀ (m) (hm : m ≤
    U) (γ : BitAssignment n), (lumpIdleCirc cfg m hm).eval.1.mulVec (Solution.XMeasCircuit.ket γ) =
    Solution.XMeasCircuit.ket (Function.update γ (stgUZero cfg) (γ (stgUZero cfg) + ∑ j : Fin m, γ
    (stgIdle cfg ⟨j.val, by omega⟩)))
  | 0, _, γ => by rw [lumpIdleCirc, identity_eval_mulVecHad]; simp
  | m + 1, hm, γ => by
      rw [lumpIdleCirc, eval_seq_mulVecHad, lumpIdleCirc_mulVec_ket cfg m (by omega) γ,
        ket_CNOTHad, Function.update_idem, Function.update_self, Function.update_of_ne (stg_ne
        _ (by dsimp; omega)), Fin.sum_univ_castSucc]; simp [add_assoc]
/-- Pre-stage validity predicate on `γ : BitAssignment n` for `gatedPhaseDyn`. -/
abbrev PhaseValid {U R n : ℕ} (cfg : QRegister (3 + U + R + R) n) (γ : BitAssignment n) : Prop :=
    γ (stgQEnc cfg) = 0 ∧ (∀ q : Fin R, γ (stgHi cfg q) = 0) ∧ (((∀ q, γ (stgLo cfg q) = 0) ∧
    γ (stgUZero cfg) + ∑ j : Fin U, γ (stgIdle cfg j) = 1) ∨ ∃ q₀ : Fin R, γ (stgUZero cfg) =
    0 ∧ (∀ j : Fin U, γ (stgIdle cfg j) = 0) ∧ (∀ q : Fin R, γ (stgLo cfg q) = if q = q₀ then 1
    else 0))
theorem splitAndParityCirc_idle {U R n : ℕ} (cfg : QRegister (3 + U + R + R) n) {γ} (hLo : ∀ q, γ
    (stgLo cfg q) = 0) (hHi : ∀ q, γ (stgHi cfg q) = 0) : ∀ (m) (hm : m ≤ R),
    (splitAndParityCirc cfg m hm).eval.1.mulVec (Solution.XMeasCircuit.ket γ) =
      Solution.XMeasCircuit.ket γ
  | 0, _ => identity_eval_mulVecHad _
  | m + 1, hm => by
      rw [splitAndParityCirc, eval_seq_mulVecHad, eval_seq_mulVecHad,
        splitAndParityCirc_idle cfg hLo hHi m (by omega), wSplitPair4_mulVec_ket_00Had _ _ _
        (hLo ⟨m, hm⟩) (hHi ⟨m, hm⟩), ket_CNOTHad, hHi ⟨m, hm⟩, add_zero, Function.update_eq_self]
theorem splitAndParityCirc_active {U R n : ℕ} (cfg : QRegister (3 + U + R + R) n) (q₀ : Fin R) {γ
    : BitAssignment n} (hQ : γ (stgQEnc cfg) = 0) (hLo : ∀ q, γ (stgLo cfg q) = if q = q₀ then 1
    else 0) (hHi : ∀ q, γ (stgHi cfg q) = 0) : ∀ (m) (hm : m ≤ R), (splitAndParityCirc cfg m
    hm).eval.1.mulVec (Solution.XMeasCircuit.ket γ) =
      if q₀.val < m then Solution.XMeasCircuit.sqrtHalf • Solution.XMeasCircuit.ket γ
    + Solution.XMeasCircuit.sqrtHalf •
      Solution.XMeasCircuit.ket (Function.update (swapPairsAssign cfg γ) (stgQEnc
    cfg) 1) else Solution.XMeasCircuit.ket γ
  | 0, _ => by simp only [Nat.not_lt_zero, ↓reduceIte]; exact identity_eval_mulVecHad _
  | m + 1, hm => by
      let γSw := Function.update (swapPairsAssign cfg γ) (stgQEnc cfg) 1
      have hSwEq : Function.update (Function.update γ (stgLo cfg q₀) 0) (stgHi cfg q₀) 1 =
        swapPairsAssign cfg γ := stgAssign_ext cfg (fun q ↦ by
          rw [(swapPairsAssign_apply cfg γ).1 q, hHi q, Function.update_of_ne (stg_ne cfg (by
            dsimp; omega))]; by_cases hqq : q = q₀
          · subst hqq; simp
          · have hv := Fin.val_ne_of_ne hqq
            rw [Function.update_of_ne (stg_ne cfg (by dsimp; omega)), hLo q]; simp [hqq])
        (fun q ↦ by
          rw [(swapPairsAssign_apply cfg γ).2.1 q, hLo q]; by_cases hqq : q = q₀
          · subst hqq; simp
          · have hv := Fin.val_ne_of_ne hqq
            rw [Function.update_of_ne (stg_ne cfg (by dsimp; omega)), Function.update_of_ne
              (stg_ne cfg (by dsimp; omega)), hHi q]; simp [hqq])
        fun u hnot ↦ by rw [(swapPairsAssign_apply cfg γ).2.2 u hnot,
          Function.update_of_ne (hnot q₀).2, Function.update_of_ne (hnot q₀).1]
      rw [splitAndParityCirc, eval_seq_mulVecHad, eval_seq_mulVecHad,
        splitAndParityCirc_active cfg q₀ hQ hLo hHi m (by omega)]; by_cases hlt : q₀.val < m
      · have hmq : (⟨m, hm⟩ : Fin R) ≠ q₀ := Fin.ne_of_val_ne (by dsimp; omega)
        have hLo0 : γ (stgLo cfg ⟨m, hm⟩) = 0 := by simp [hLo, hmq]
        have hSwLo0 : γSw (stgLo cfg ⟨m, hm⟩) = 0 := by
          dsimp only [γSw]; rw [Function.update_of_ne (stg_ne cfg (by dsimp; omega)),
            (swapPairsAssign_apply cfg γ).1, hHi]
        have hSwHi0 : γSw (stgHi cfg ⟨m, hm⟩) = 0 := by
          dsimp only [γSw]; rw [Function.update_of_ne (stg_ne cfg (by dsimp; omega)),
            (swapPairsAssign_apply cfg γ).2.1, hLo0]
        simp only [hlt, show q₀.val < m + 1 by omega, ↓reduceIte,
          show Function.update (swapPairsAssign cfg γ) (stgQEnc cfg) 1 = γSw from rfl,
          Matrix.mulVec_add, Matrix.mulVec_smul, wSplitPair4_mulVec_ket_00Had _ _ _ hLo0
          (hHi ⟨m, hm⟩), wSplitPair4_mulVec_ket_00Had _ _ _ hSwLo0 hSwHi0, ket_CNOTHad,
          hHi ⟨m, hm⟩, hSwHi0, add_zero, Function.update_eq_self]
      · by_cases heq : q₀.val = m
        · have hLo1 : γ (stgLo cfg q₀) = 1 := by simp [hLo]
          simp only [hlt, show q₀.val < m + 1 by omega, ↓reduceIte,
            show (⟨m, hm⟩ : Fin R) = q₀ from Fin.ext heq.symm]
          rw [wSplitPair4_mulVec_ket_10Had _ _ _ hLo1 (hHi q₀), hSwEq, Matrix.mulVec_add,
            Matrix.mulVec_smul, Matrix.mulVec_smul, ket_CNOTHad, ket_CNOTHad, hHi q₀,
            add_zero, Function.update_eq_self, (swapPairsAssign_apply cfg γ).2.1 q₀, hLo1,
            swapPairsAssign_qEnc cfg γ, hQ, zero_add]
        · have hmq : (⟨m, hm⟩ : Fin R) ≠ q₀ := Fin.ne_of_val_ne (by dsimp; omega)
          have hLo0 : γ (stgLo cfg ⟨m, hm⟩) = 0 := by simp [hLo, hmq]
          simp only [hlt, show ¬ (q₀.val < m + 1) by omega, ↓reduceIte,
            wSplitPair4_mulVec_ket_00Had _ _ _ hLo0 (hHi ⟨m, hm⟩), ket_CNOTHad,
            hHi ⟨m, hm⟩, add_zero, Function.update_eq_self]
theorem wpSubspaceGatedPhaseDyn {Var : Type} [Fintype Var] [DecidableEq Var] {U R n : ℕ} (v :
    Var) (cfg : QRegister (3 + U + R + R) n) (S : BitAssignment n → Prop) (f : BitAssignment n →
    BitAssignment n) (hValid : ∀ β, S β → PhaseValid cfg (f β)) : HadSubspaceStepV v
    (ketMapOpHad S (fun β ↦ Solution.XMeasCircuit.ket (f β))) (ketMapOpHad S (fun β ↦
      Solution.XMeasCircuit.ket
    (phaseStepAssign cfg (f β)))) (gatedPhaseDyn v cfg) := by
  let lumpVal (γ : BitAssignment n) := Function.update γ (stgUZero cfg) (γ (stgUZero cfg) + ∑ j
    : Fin U, γ (stgIdle cfg j))
  let outLumped (γ : BitAssignment n) := phaseStepAssign cfg (lumpVal γ)
  let Rmid := ketMapOpHad S (fun β ↦
    Solution.XMeasCircuit.sqrtHalf • Solution.XMeasCircuit.ket (outLumped (f β)) +
    Solution.XMeasCircuit.sqrtHalf •
      Solution.XMeasCircuit.ket (Function.update (swapPairsAssign cfg (outLumped (f β)))
    (stgQEnc cfg) 1))
  let Rpost := ketMapOpHad S (fun β ↦ Solution.XMeasCircuit.ket (outLumped (f β)))
  have hCQ : stgCtrl cfg ≠ stgQEnc cfg := stg_ne cfg (by dsimp; omega)
  have hLumpNotU (γ) {i : Fin (3 + U + R + R)} (hi : i.val ≠ 1) : lumpVal γ (cfg i) = γ (cfg i) :=
    Function.update_of_ne (stg_ne cfg hi) _ _
  have hQ0 (β) (hS : S β) : outLumped (f β) (stgQEnc cfg) = 0 := by
    have hL := (hLumpNotU (f β) (i := ⟨2, by omega⟩) (by dsimp; omega)).trans (hValid β hS).1
    dsimp only [outLumped, phaseStepAssign]
    split_ifs <;> [exact hL; exact (swapPairsAssign_qEnc cfg _).trans hL]
  refine HadSubspaceStepV.seq
    (HadSubspaceStepV.of_circuit _ (by simp only [Circuit.count_seq, countLumpIdleCirc_arity3,
      countSplitAndParityCirc_arity3, hadCtrlHPair, Circuit.count_onRegister]; rfl)
      (R₁ := Rmid) ?_)
    (HadSubspaceStepV.seq (HadSubspaceStepV.remeasure (stgQEnc cfg) _ (R₁ := Rpost) ?_ ?_)
      (HadSubspaceStepV.of_circuit _ (countLumpIdleCirc_arity3 cfg _ U le_rfl) ?_))
  · rw [mul_ketMapOpHad]; refine ketMapOpHad_congr fun β hS ↦ ?_
    obtain ⟨hQ, hHi, hCase⟩ := hValid β hS
    simp only [eval_seq_mulVecHad, lumpIdleCirc_mulVec_ket cfg U le_rfl (f β)]
    rcases hCase with ⟨hLo, hSum1⟩ | ⟨q₀, hU0, hIdle0, hLo⟩
    · have hLU1 : lumpVal (f β) (stgUZero cfg) = 1 := by simp [lumpVal, hSum1]
      have hLQ0 := (hLumpNotU _ (i := ⟨2, by omega⟩) (by dsimp; omega)).trans hQ
      have hLLo (q) := (hLumpNotU _ (i := ⟨3 + U + q.val, by omega⟩) (by dsimp; omega)).trans (hLo
        q)
      have hLHi (q) := (hLumpNotU _ (i := ⟨3 + U + R + q.val, by omega⟩) (by dsimp; omega)).trans
        (hHi q)
      have hSwId : swapPairsAssign cfg (lumpVal (f β)) = lumpVal (f β) := funext fun w ↦
        swapPairsAssign_cases cfg w
          (fun q ↦ by rw [(swapPairsAssign_apply cfg _).1 q, hLHi q, hLLo q])
          (fun q ↦ by rw [(swapPairsAssign_apply cfg _).2.1 q, hLLo q, hLHi q])
          (swapPairsAssign_apply cfg _).2.2
      have hOutId : outLumped (f β) = lumpVal (f β) := by
        dsimp only [outLumped, phaseStepAssign]; split_ifs <;> simp [hSwId]
      have hu0 := update_bit_eq_selfHad hLQ0
      rw [splitAndParityCirc_idle cfg hLLo hLHi R le_rfl, hadCtrlHPair_mulVec_ket_10 _ _ _ hLU1
        hLQ0, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, ket_CNOTHad,
        ket_CNOTHad, hLQ0, zero_add, Function.update_idem, Function.update_self,
        Function.update_of_ne hCQ, hOutId, hSwId,
        hLumpNotU (f β) (i := ⟨0, by omega⟩) (by dsimp; omega),
        show cfg.wires ⟨0, _⟩ = stgCtrl cfg from rfl]
      rcases Solution.CircuitModular.UnsignedGivens.zmod2_eq_zero_or_one (f β
        (stgCtrl cfg)) with hc | hc
      · rw [hc, add_zero, hu0]
      · rw [hc, show (1 : ZMod 2) + 1 = 0 from rfl, hu0]; exact add_comm _ _
    · have hLumpId : lumpVal (f β) = f β := by
        dsimp only [lumpVal]
        rw [hU0, show (∑ j : Fin U, f β (stgIdle cfg j)) = 0 by simp [hIdle0], add_zero]
        exact update_bit_eq_selfHad hU0
      rw [show Function.update (f β) _ _ = lumpVal (f β) from rfl, hLumpId]
      have hSwU0 : Function.update (swapPairsAssign cfg (f β)) (stgQEnc cfg) 1 (stgUZero cfg)
        = 0 := by
        rw [Function.update_of_ne (stg_ne cfg (by dsimp; omega)), swapPairsAssign_uZero, hU0]
      have hSwQ0 := (swapPairsAssign_qEnc cfg (f β)).trans hQ
      rw [splitAndParityCirc_active cfg q₀ hQ hLo hHi R le_rfl]
      simp only [q₀.isLt, ↓reduceIte, Matrix.mulVec_add, Matrix.mulVec_smul, ket_CNOTHad, hQ,
        hadCtrlHPair_mulVec_ket_0 _ _ _ hU0, hadCtrlHPair_mulVec_ket_0 _ _ _ hSwU0, zero_add,
        Function.update_idem, Function.update_self, Function.update_of_ne hCQ,
        swapPairsAssign_ctrl]
      rcases Solution.CircuitModular.UnsignedGivens.zmod2_eq_zero_or_one (f β
        (stgCtrl cfg)) with hc | hc
      · dsimp only [outLumped, phaseStepAssign]; rw [hLumpId, hc]
        simp only [↓reduceIte, add_zero, update_bit_eq_selfHad hQ]
      · dsimp only [outLumped, phaseStepAssign]; rw [hLumpId, hc]
        simp only [one_ne_zero, ↓reduceIte, show (1 : ZMod 2) + 1 = 0 from rfl,
          update_bit_eq_selfHad hSwQ0, swapPairsAssign_invol]; exact add_comm _ _
  · rw [mul_ketMapOpHad, smul_ketMapOpHad]; refine ketMapOpHad_congr fun β hS ↦ ?_
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
      Solution.XMeasCircuit.ket_projector_zero,
      Solution.XMeasCircuit.ket_projector_zero, hQ0 β hS, Function.update_self]; simp
  · refine HadSubspaceStepV.of_circuit _
      (by simp only [Circuit.count_seq, countSwapPairsPhaseCirc_arity3]; rfl) ?_
    rw [mul_ketMapOpHad, mul_ketMapOpHad, smul_ketMapOpHad]
    refine ketMapOpHad_congr fun β hS ↦ ?_
    have hSwQ0 := (swapPairsAssign_qEnc cfg _).trans (hQ0 β hS)
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
      Solution.XMeasCircuit.ket_projector_one,
      Solution.XMeasCircuit.ket_projector_one, hQ0 β hS, Function.update_self]
    simp only [zero_ne_one, ↓reduceIte, smul_zero, zero_add, eval_seq_mulVecHad,
      Matrix.mulVec_smul, Solution.XMeasCircuit.ket_X, Function.update_idem, Function.update_self,
      swapPairsPhaseCirc_mulVec_ket, show (1 : ZMod 2) + 1 = 0 from rfl, update_bit_eq_selfHad
      hSwQ0, swapPairsAssign_invol]
  · rw [mul_ketMapOpHad]; refine ketMapOpHad_congr fun β _ ↦ ?_
    rw [lumpIdleCirc_mulVec_ket]; congr 1; funext w
    have hIdleEq (j : Fin U) : outLumped (f β) (stgIdle cfg j) = f β (stgIdle cfg j) := by
      have hL := hLumpNotU (f β) (i := ⟨3 + j.val, by omega⟩) (by dsimp; omega)
      dsimp only [outLumped, phaseStepAssign]
      split_ifs <;> [exact hL; exact (swapPairsAssign_idle cfg _ j).trans hL]
    have hUZeroEq : outLumped (f β) (stgUZero cfg) = f β (stgUZero cfg) + ∑ j : Fin U, f β
      (stgIdle cfg j) := by
      dsimp only [outLumped, phaseStepAssign, lumpVal]
      split_ifs <;> simp [swapPairsAssign_uZero]
    by_cases hwU : w = stgUZero cfg
    · subst hwU; rw [Function.update_self, hUZeroEq, show (∑ j : Fin U, outLumped (f β)
        (stgIdle cfg ⟨j.val, j.isLt⟩)) = ∑ j : Fin U, f β (stgIdle cfg j) from
          Finset.sum_congr rfl fun j _ ↦ hIdleEq j, zmod2_add_cancel_rightHad]
      dsimp only [phaseStepAssign]
      split_ifs <;> [rfl; exact (swapPairsAssign_uZero cfg _).symm]
    · rw [Function.update_of_ne hwU]; dsimp only [outLumped, phaseStepAssign]
      rw [hLumpNotU (f β) (i := ⟨0, by omega⟩) (by dsimp; omega)]; split_ifs
      · exact Function.update_of_ne hwU _ _
      · let sa := swapPairsAssign_apply cfg
        exact stgWire_eq cfg (swapPairsAssign cfg (lumpVal (f β))) (swapPairsAssign cfg (f β))
          w
          (fun q ↦ by rw [(sa _).1 q, (sa _).1 q]
                      exact hLumpNotU (f β) (i := ⟨3 + U + R + q.val, by omega⟩) (by dsimp; omega))
          (fun q ↦ by rw [(sa _).2.1 q, (sa _).2.1 q]
                      exact hLumpNotU (f β) (i := ⟨3 + U + q.val, by omega⟩) (by dsimp; omega))
          (fun hu ↦ by rw [(sa _).2.2 w hu, (sa _).2.2 w hu]; exact Function.update_of_ne hwU _ _)
/-- Intermediate folded state where `stgHi q` (`q < m`) holds `γ (stgCtrl) * γ (stgLo q)`. -/
def partialHiXor {U R n : ℕ} (cfg : QRegister (3 + U + R + R) n) : (m : ℕ) → m ≤ R → BitAssignment
    n → BitAssignment n
  | 0, _, γ => γ
  | m + 1, hm, γ => Function.update (partialHiXor cfg m (by omega) γ) (stgHi cfg ⟨m, hm⟩)
      (γ (stgCtrl cfg) * γ (stgLo cfg ⟨m, hm⟩))
/-- Bit-assignment action of `foldPairsPhaseCirc cfg m hm`. -/
def foldPairsPrefixAssign {U R n : ℕ} (cfg : QRegister (3 + U + R + R) n) : (m : ℕ) → m ≤ R →
    BitAssignment n → BitAssignment n
  | 0, _, δ => δ
  | m + 1, hm, δ => let δ' := foldPairsPrefixAssign cfg m (by omega) δ
      Function.update δ' (stgLo cfg ⟨m, hm⟩) (δ' (stgLo cfg ⟨m, hm⟩) + δ' (stgHi cfg ⟨m, hm⟩))
theorem foldPairsPhaseCirc_mulVec_ket {U R n : ℕ} (cfg : QRegister (3 + U + R + R) n) : ∀ (m) (hm
    : m ≤ R) (δ : BitAssignment n),
      (foldPairsPhaseCirc cfg m hm).eval.1.mulVec (Solution.XMeasCircuit.ket δ)
    = Solution.XMeasCircuit.ket (foldPairsPrefixAssign cfg m hm δ)
  | 0, _, _ => identity_eval_mulVecHad _
  | m + 1, hm, δ => by
      rw [foldPairsPhaseCirc, eval_seq_mulVecHad, foldPairsPhaseCirc_mulVec_ket cfg m (by
        omega) δ, ket_CNOTHad]; rfl
theorem foldPairsPrefixAssign_of_not_lo {U R n : ℕ} (cfg : QRegister (3 + U + R + R) n) : ∀ (m)
    (hm : m ≤ R) (δ : BitAssignment n) (w : Wire n), (∀ q : Fin m, w ≠ stgLo cfg ⟨q.val, by
    omega⟩) → foldPairsPrefixAssign cfg m hm δ w = δ w
  | 0, _, _, _, _ => rfl
  | m + 1, hm, δ, w, hw => by
      rw [foldPairsPrefixAssign, Function.update_of_ne (hw ⟨m, Nat.lt_succ_self m⟩)]
      exact foldPairsPrefixAssign_of_not_lo cfg m (by omega) δ w fun q ↦ hw ⟨q.val,
        Nat.lt_succ_of_lt q.isLt⟩
theorem foldPairsPrefixAssign_lo {U R n : ℕ} (cfg : QRegister (3 + U + R + R) n) : ∀ (m) (hm : m ≤
    R) (δ : BitAssignment n) (q : Fin R), foldPairsPrefixAssign cfg m hm δ (stgLo cfg q) = if
    q.val < m then δ (stgLo cfg q) + δ (stgHi cfg q) else δ (stgLo cfg q)
  | 0, _, _, _ => by simp [foldPairsPrefixAssign]
  | m + 1, hm, δ, q => by
      dsimp only [foldPairsPrefixAssign]; by_cases hqm : q.val = m
      · have hqeq : q = ⟨m, hm⟩ := Fin.ext hqm; subst hqeq
        rw [Function.update_self, foldPairsPrefixAssign_of_not_lo cfg m (by omega) δ _ fun _ ↦
          stg_ne cfg (by dsimp; omega), foldPairsPrefixAssign_of_not_lo cfg m (by omega) δ _ fun
          _ ↦ stg_ne cfg (by dsimp; omega)]; simp
      · rw [Function.update_of_ne (stg_ne cfg (by dsimp; omega)),
          foldPairsPrefixAssign_lo cfg m (by omega) δ q]
        simp [show (q.val < m + 1) ↔ (q.val < m) by omega]
theorem partialHiXor_of_not_hi {U R n : ℕ} (cfg : QRegister (3 + U + R + R) n) : ∀ (m) (hm : m ≤
    R) (γ : BitAssignment n) (w : Wire n), (∀ q : Fin m, w ≠ stgHi cfg ⟨q.val, by omega⟩) →
    partialHiXor cfg m hm γ w = γ w
  | 0, _, _, _, _ => rfl
  | m + 1, hm, γ, w, hw => by
      rw [partialHiXor, Function.update_of_ne (hw ⟨m, Nat.lt_succ_self m⟩)]
      exact partialHiXor_of_not_hi cfg m (by omega) γ w fun q ↦ hw ⟨q.val, Nat.lt_succ_of_lt
        q.isLt⟩
theorem partialHiXor_hi {U R n : ℕ} (cfg : QRegister (3 + U + R + R) n) : ∀ (m) (hm : m ≤ R) (γ :
    BitAssignment n) (q : Fin R), partialHiXor cfg m hm γ (stgHi cfg q) = if q.val < m then γ
    (stgCtrl cfg) * γ (stgLo cfg q) else γ (stgHi cfg q)
  | 0, _, _, _ => by simp [partialHiXor]
  | m + 1, hm, γ, q => by
      dsimp only [partialHiXor]; by_cases hqm : q.val = m
      · have hqeq : q = ⟨m, hm⟩ := Fin.ext hqm; subst hqeq; simp
      · rw [Function.update_of_ne (stg_ne cfg (by dsimp; omega)),
          partialHiXor_hi cfg m (by omega) γ q]
        simp [show (q.val < m + 1) ↔ (q.val < m) by omega]
theorem foldPairs_phaseStepAssign_eq {U R n : ℕ} (cfg : QRegister (3 + U + R + R) n) {γ :
    BitAssignment n} (hHi : ∀ q, γ (stgHi cfg q) = 0) : foldPairsPrefixAssign cfg R le_rfl
    (phaseStepAssign cfg γ) = partialHiXor cfg R le_rfl γ := stgAssign_ext cfg
    (fun q ↦ by rw [foldPairsPrefixAssign_lo cfg R le_rfl _ q,
                  partialHiXor_of_not_hi cfg R le_rfl γ _ fun _ ↦ stg_ne cfg (by dsimp; omega)]
                simp only [q.isLt, ↓reduceIte, phaseStepAssign]
                rcases Solution.CircuitModular.UnsignedGivens.zmod2_eq_zero_or_one (γ
                  (stgCtrl cfg)) with hc | hc <;>
                  simp [hc, one_ne_zero, (swapPairsAssign_apply cfg γ).1 q,
                  (swapPairsAssign_apply cfg γ).2.1 q, hHi q])
    (fun q ↦ by rw [foldPairsPrefixAssign_of_not_lo cfg R le_rfl _ _
                  fun _ ↦ stg_ne cfg (by dsimp; omega), partialHiXor_hi cfg R le_rfl γ q]
                simp only [q.isLt, ↓reduceIte, phaseStepAssign]
                rcases Solution.CircuitModular.UnsignedGivens.zmod2_eq_zero_or_one (γ
                  (stgCtrl cfg)) with hc | hc <;>
                  simp [hc, one_ne_zero, (swapPairsAssign_apply cfg γ).2.1 q, hHi q])
    fun u hu ↦ by rw [foldPairsPrefixAssign_of_not_lo cfg R le_rfl _ u fun q ↦ (hu q).1,
                    partialHiXor_of_not_hi cfg R le_rfl γ u fun q ↦ (hu q).2]
                  dsimp only [phaseStepAssign]; split_ifs <;>
                    [rfl; exact (swapPairsAssign_apply cfg γ).2.2 u hu]
theorem wpSubspaceUnloadPairsPhaseDyn {Var : Type} [Fintype Var] [DecidableEq Var] {U R n : ℕ} (v
    : Var) (cfg : QRegister (3 + U + R + R) n) (S : BitAssignment n → Prop) (f : BitAssignment n →
    BitAssignment n) (φ : BitAssignment n → ℂ) (hHi : ∀ β, S β → ∀ q, f β (stgHi cfg q) = 0) : ∀
    (m) (hm : m ≤ R), HadSubspaceStepV v (ketMapOpHad S (fun β ↦ φ β • Solution.XMeasCircuit.ket
    (partialHiXor cfg m hm (f β)))) (ketMapOpHad S (fun β ↦ φ β • Solution.XMeasCircuit.ket (f β)))
    (unloadPairsPhaseDyn v cfg m hm)
  | 0, _ => HadSubspaceStepV.of_circuit Circuit.identity rfl (by simp [partialHiXor])
  | m + 1, hm => by
      let q : Fin R := ⟨m, hm⟩
      let gPhase : BitAssignment n → ZMod 2 := fun δ ↦ δ (stgCtrl cfg) * δ (stgLo cfg q)
      have hg (δ) (b) : gPhase (Function.update δ (stgHi cfg q) b) = gPhase δ := by
        dsimp only [gPhase]; rw [Function.update_of_ne (stg_ne cfg (by dsimp; omega)),
          Function.update_of_ne (stg_ne cfg (by dsimp; omega))]
      let Rm := ketMapOpHad S (fun β ↦
        φ β • Solution.XMeasCircuit.ket (partialHiXor cfg m (by omega) (f
        β)))
      have hNotHi {i : Fin (3 + U + R + R)} (hi : i.val < 3 + U + R ∨ i.val = 3 + U + R + m) (β) :
        partialHiXor cfg m (by omega) (f β) (cfg i) = f β (cfg i) := partialHiXor_of_not_hi cfg
        m (by omega) (f β) (cfg i) fun q' ↦ stg_ne cfg (by have := q'.isLt; dsimp; omega)
      have hXor : ketMapOpHad S (fun β ↦
        φ β • Solution.XMeasCircuit.ket (partialHiXor cfg (m + 1) hm (f
        β))) = (Solution.XMeasCircuit.xorWireUnitary (stgHi cfg q) gPhase hg).1 * Rm := by
        rw [mul_ketMapOpHad]; refine ketMapOpHad_congr fun β hS ↦ ?_
        rw [Matrix.mulVec_smul, Solution.XMeasCircuit.xorWireUnitary_mulVec_ket]; congr 2
        dsimp only [partialHiXor, gPhase]
        rw [hNotHi (i := ⟨3 + U + R + m, by omega⟩) (Or.inr rfl) β, hHi β hS q, zero_add,
          hNotHi (i := ⟨0, by omega⟩) (Or.inl (by dsimp; omega)) β,
          hNotHi (i := ⟨3 + U + m, by omega⟩) (Or.inl (by dsimp; omega)) β]
      have hClean : Solution.XMeasCircuit.cleanFinsetProj {stgHi cfg q} * Rm = Rm := by
        rw [mul_ketMapOpHad]; refine ketMapOpHad_congr fun β hS ↦ ?_
        have h0 : ∀ w ∈ ({stgHi cfg q} : Finset (Wire n)), partialHiXor cfg m (by omega) (f β) w
          = 0 := fun w hw ↦ by
          rw [Finset.mem_singleton.mp hw, hNotHi (i := ⟨3 + U + R + m, by omega⟩) (Or.inr rfl) β]
          exact hHi β hS q
        rw [Matrix.mulVec_smul, Solution.XMeasCircuit.ket_cleanFinsetProj]; simp [h0]
      rw [unloadPairsPhaseDyn, hXor]
      exact HadSubspaceStepV.seq (HadSubspaceStepV.xMeasUnload_circuit (stgHi cfg q) gPhase hg
        _ rfl (czCircuit_eval_eq_phaseFlipHad _ _ (stg_ne cfg (by dsimp; omega))) hClean)
        (wpSubspaceUnloadPairsPhaseDyn v cfg S f φ hHi m (by omega))
theorem wpSubspaceGatedUnphaseDyn {Var : Type} [Fintype Var] [DecidableEq Var] {U R n : ℕ} (v :
    Var) (cfg : QRegister (3 + U + R + R) n) (S : BitAssignment n → Prop) (f : BitAssignment n →
    BitAssignment n) (φ : BitAssignment n → ℂ) (hHi : ∀ β, S β → ∀ q, f β (stgHi cfg q) = 0) :
    HadSubspaceStepV v (ketMapOpHad S (fun β ↦
      φ β • Solution.XMeasCircuit.ket (phaseStepAssign cfg (f
    β)))) (ketMapOpHad S (fun β ↦
        φ β • Solution.XMeasCircuit.ket (f β))) (gatedUnphaseDyn v cfg) := by
  refine HadSubspaceStepV.seq (HadSubspaceStepV.of_circuit _ (countFoldPairsPhaseCirc_arity3
    cfg _ R le_rfl) ?_) (wpSubspaceUnloadPairsPhaseDyn v cfg S f φ hHi R le_rfl)
  rw [mul_ketMapOpHad]; refine ketMapOpHad_congr fun β hS ↦ ?_
  rw [Matrix.mulVec_smul, foldPairsPhaseCirc_mulVec_ket, foldPairs_phaseStepAssign_eq cfg (hHi β
    hS)]
/-- `26-T`-compatible `9`-bit packet multiplexer formula (`pkt = 1 ↦ true` at zero coin weight,
swapping equal-weight `pkt = 5 ↔ 6` relative to `mux9Formula`). -/
def mux9AltFormula (p0 p1 p2 p3 k0 k1 k2 k3 k4 k5 k6 k7 k8 : Bool) : Bool := if !p0 then if !p3
    then (if !p2 then !k8 else !k1) else (if !p2 then !k2 else !k3) else if !p1 then if !p3 then
    true else (if !p2 then !k6 else !k4) else if !p3 then (if !p2 then !k5 else !k0) else !k7
/-- `26-T`-compatible `9`-bit swap decision bit `mux9AltBit pkt keep`. -/
def mux9AltBit (pkt : Fin (2 ^ 4)) (keep : Fin (2 ^ 9)) : Bool := mux9AltFormula (bitsOfFin 4
    pkt 0) (bitsOfFin 4 pkt 1) (bitsOfFin 4 pkt 2) (bitsOfFin 4 pkt 3) (bitsOfFin 9 keep 0)
    (bitsOfFin 9 keep 1) (bitsOfFin 9 keep 2) (bitsOfFin 9 keep 3) (bitsOfFin 9 keep 4) (bitsOfFin 9
    keep 5) (bitsOfFin 9 keep 6) (bitsOfFin 9 keep 7) (bitsOfFin 9 keep 8)
theorem mux9AltBit_finOfBitsHad (p : Fin 4 → Bool) (q : Fin 9 → Bool) : mux9AltBit (finOfBits
    4 p) (finOfBits 9 q) = mux9AltFormula (p 0) (p 1) (p 2) (p 3) (q 0) (q 1) (q 2) (q 3) (q 4) (q
    5) (q 6) (q 7) (q 8) := by
  dsimp only [mux9AltBit]; rw [bitsOfFin_finOfBits 4 p, bitsOfFin_finOfBits 9 q]
/-- Boolean-to-`ZMod 2` map `false ↦ 0, true ↦ 1`. -/
def b2zHad (b : Bool) : ZMod 2 := if b then 1 else 0
theorem b2zHad_inj {x y : Bool} (h : b2zHad x = b2zHad y) : x = y := by
  cases x <;> cases y <;> first | rfl | exact absurd h (by decide)
theorem b2zHad_xor (x y : Bool) : b2zHad (xor x y) = b2zHad x + b2zHad y := by
  cases x <;> cases y <;> rfl
theorem b2zHad_and (x y : Bool) : b2zHad (x && y) = b2zHad x * b2zHad y := by
  cases x <;> cases y <;> rfl
theorem b2zHad_ite_not (c a b : Bool) : b2zHad (if !c then a else b) = (1 + b2zHad c) *
    b2zHad a + b2zHad c * b2zHad b := by cases c <;> cases a <;> cases b <;> rfl
/-- Zero vector in `Fin 9 → ZMod 2`. -/
def zVec9HadW (_ : Fin 9) : ZMod 2 := 0
/-- Standard basis vector `e_j` in `Fin 9 → ZMod 2` using computable `Nat` equality. -/
def eVec9HadW (j i : Fin 9) : ZMod 2 := if i.val == j.val then 1 else 0
/-- Explicit `9`-term sum on `Fin 9 → ZMod 2`. -/
def sum9HadW (f : Fin 9 → ZMod 2) : ZMod 2 := f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8
/-- Tuple-to-vector helper in `Fin 9 → ZMod 2` for `9` Boolean inputs. -/
def kVec9HadW (k0 k1 k2 k3 k4 k5 k6 k7 k8 : Bool) (j : Fin 9) : ZMod 2 :=
  match j.val with
  | 0 => b2zHad k0 | 1 => b2zHad k1 | 2 => b2zHad k2 | 3 => b2zHad k3 | 4 => b2zHad k4
  | 5 => b2zHad k5 | 6 => b2zHad k6 | 7 => b2zHad k7 | _ => b2zHad k8
/-- `ZMod 2` polynomial form of `mux9AltFormula` on `(p0..p3, k)`. -/
def altMuxPoly (p0 p1 p2 p3 : Bool) (k : Fin 9 → ZMod 2) : ZMod 2 := b2zHad (mux9AltFormula p0
    p1 p2 p3 (decide (k 0 = 1)) (decide (k 1 = 1)) (decide (k 2 = 1)) (decide (k 3 = 1)) (decide (k
    4 = 1)) (decide (k 5 = 1)) (decide (k 6 = 1)) (decide (k 7 = 1)) (decide (k 8 = 1)))
/-- `ZMod 2` polynomial form of `mux9Formula` with `(p0, p1)` swapped on `p2 && !p3`. -/
def swapMuxPoly (p0 p1 p2 p3 : Bool) (k : Fin 9 → ZMod 2) : ZMod 2 := b2zHad (mux9Formula
    (if p2 && !p3 then p1 else p0) (if p2 && !p3 then p0 else p1) p2 p3 (decide (k 0 = 1)) (decide
    (k 1 = 1)) (decide (k 2 = 1)) (decide (k 3 = 1)) (decide (k 4 = 1)) (decide (k 5 = 1)) (decide
    (k 6 = 1)) (decide (k 7 = 1)) (decide (k 8 = 1)))
theorem mux9AltFormula_eqSwap {p0 p1 p2 p3 : Bool} (hp : !(p0 && !p1 && !p2 && !p3) = true) (k0
    k1 k2 k3 k4 k5 k6 k7 k8 : Bool) : mux9AltFormula p0 p1 p2 p3 k0 k1 k2 k3 k4 k5 k6 k7 k8 =
    mux9Formula (if p2 && !p3 then p1 else p0) (if p2 && !p3 then p0 else p1) p2 p3 k0 k1 k2 k3 k4
    k5 k6 k7 k8 := by
  have h0 : ∀ a b c d, !(a && !b && !c && !d) = true →
      altMuxPoly a b c d zVec9HadW = swapMuxPoly a b c d zVec9HadW := by decide
  have he : ∀ a b c d (j : Fin 9), !(a && !b && !c && !d) = true →
      altMuxPoly a b c d (eVec9HadW j) = swapMuxPoly a b c d (eVec9HadW j) := by decide
  let k := kVec9HadW k0 k1 k2 k3 k4 k5 k6 k7 k8
  have hdec (z : ZMod 2) : b2zHad (decide (z = 1)) = z := by fin_cases z <;> rfl
  have hnot (x : Bool) : b2zHad (!x) = 1 - b2zHad x := by cases x <;> rfl
  have hl : altMuxPoly p0 p1 p2 p3 k = altMuxPoly p0 p1 p2 p3 zVec9HadW + sum9HadW fun j ↦
    (altMuxPoly p0 p1 p2 p3 (eVec9HadW j) - altMuxPoly p0 p1 p2 p3 zVec9HadW) * k j := by
    dsimp only [altMuxPoly, sum9HadW]; simp only [mux9AltFormula, b2zHad_ite_not, hnot, hdec]
    dsimp [eVec9HadW, zVec9HadW]; ring
  have hr : swapMuxPoly p0 p1 p2 p3 k = swapMuxPoly p0 p1 p2 p3 zVec9HadW + sum9HadW fun j
    ↦ (swapMuxPoly p0 p1 p2 p3 (eVec9HadW j) - swapMuxPoly p0 p1 p2 p3 zVec9HadW) * k j :=
    by
    dsimp only [swapMuxPoly, sum9HadW]; simp only [mux9Formula, b2zHad_xor, b2zHad_and,
      hdec]; dsimp [eVec9HadW, zVec9HadW]; ring
  have hEq : altMuxPoly p0 p1 p2 p3 k = swapMuxPoly p0 p1 p2 p3 k := by
    rw [hl, hr, h0 p0 p1 p2 p3 hp]; dsimp only [sum9HadW]
    simp only [fun j ↦ he p0 p1 p2 p3 j hp]
  have hbk (b : Bool) : decide (b2zHad b = 1) = b := by cases b <;> decide
  have hk0 : k 0 = b2zHad k0 := rfl; have hk1 : k 1 = b2zHad k1 := rfl
  have hk2 : k 2 = b2zHad k2 := rfl; have hk3 : k 3 = b2zHad k3 := rfl
  have hk4 : k 4 = b2zHad k4 := rfl; have hk5 : k 5 = b2zHad k5 := rfl
  have hk6 : k 6 = b2zHad k6 := rfl; have hk7 : k 7 = b2zHad k7 := rfl
  have hk8 : k 8 = b2zHad k8 := rfl
  dsimp only [altMuxPoly, swapMuxPoly] at hEq
  simp only [hk0, hk1, hk2, hk3, hk4, hk5, hk6, hk7, hk8, hbk] at hEq; exact b2zHad_inj hEq
/-- Equal-weight transposition `5 ↔ 6` on `4`-bit packet indices `Fin (2 ^ 4)`. -/
def pktSwap56 : Equiv.Perm (Fin (2 ^ 4)) := Equiv.swap 5 6
theorem coin9WeightPktSwap56 (pkt : Fin (2 ^ 4)) :
    coin9Weight (pktSwap56 pkt) = coin9Weight pkt := by fin_cases pkt <;> decide
theorem pktSwap56_bits {pkt : Fin (2 ^ 4)} (hp : pkt ≠ 1) : !(bitsOfFin 4 pkt 0 && !bitsOfFin 4
    pkt 1 && !bitsOfFin 4 pkt 2 && !bitsOfFin 4 pkt 3) = true ∧ bitsOfFin 4 (pktSwap56 pkt) 0 =
    (if bitsOfFin 4 pkt 2 && !bitsOfFin 4 pkt 3 then bitsOfFin 4 pkt 1 else bitsOfFin 4 pkt 0) ∧
    bitsOfFin 4 (pktSwap56 pkt) 1 = (if bitsOfFin 4 pkt 2 && !bitsOfFin 4 pkt 3 then bitsOfFin 4
    pkt 0 else bitsOfFin 4 pkt 1) ∧ bitsOfFin 4 (pktSwap56 pkt) 2 = bitsOfFin 4 pkt 2 ∧ bitsOfFin
    4 (pktSwap56 pkt) 3 = bitsOfFin 4 pkt 3 := by revert pkt; decide
theorem mux9AltBit_eqMux9Bit_swap {pkt : Fin (2 ^ 4)} (hp : pkt ≠ 1) (keep : Fin (2 ^ 9)) :
    mux9AltBit pkt keep = mux9Bit (pktSwap56 pkt) keep := by
  obtain ⟨h1, hb0, hb1, hb2, hb3⟩ := pktSwap56_bits hp
  dsimp only [mux9AltBit, mux9Bit]; rw [hb0, hb1, hb2, hb3]
  exact mux9AltFormula_eqSwap h1 _ _ _ _ _ _ _ _ _
/-! ### Generic 4-Stage `14 + s` Gated `W`-State Phase Kickback Engine -/
/-- Phase exponent `β 0 * (if muxBit pkt keep then 1 else 0)` on `BitAssignment 14`. -/
def keepKickPhaseOf (muxBit : Fin (2 ^ 4) → Fin (2 ^ 9) → Bool) (β : BitAssignment 14) : ZMod 2 :=
    β 0 * (if muxBit (finOfBits 4 fun i ↦ decide (β ⟨1 + i.val, by omega⟩ = 1)) (finOfBits 9 fun j ↦
    decide (β ⟨5 + j.val, by omega⟩ = 1)) then 1 else 0)
/-- Ideal `14`-wire phase-kickback unitary for `mux9AltBit` (`26-T` `gatedKeepKickback25Dyn`).
-/
noncomputable def keepKickAlt14Unitary : Unitary (2 ^ 14) := Solution.XMeasCircuit.phaseFlipUnitary
    (keepKickPhaseOf mux9AltBit)
/-- Active `14`-wire register `[0, 14)` (`wPar`, `pkt[0..3]`, `keep[0..8]`) on `Wire N`. -/
def actKick {N s : ℕ} (hN : 14 + s = N) : QRegister 14 N := QRegister.block 0 14 (by omega)
/-- Clean `s`-wire scratch register `[14, 14 + s)` on `Wire N`. -/
def scrKick {N s : ℕ} (hN : 14 + s = N) : QRegister s N := QRegister.block 14 s (by omega)
/-- Clean-scratch predicate `∀ j : Fin s, β (14 + j) = 0` on `BitAssignment N`. -/
def cleanKick {N s : ℕ} (hN : 14 + s = N) (β : BitAssignment N) : Prop := ∀ j : Fin s, β ⟨14 +
    j.val, by omega⟩ = 0
/-- `0-T` root initializer `uZero := 1 + wPar` on `(0, 14)` inside `Wire N`. -/
def initKickCirc {N s : ℕ} (hN : 14 + s = N) (hs : 1 ≤ s) : Circuit N := Circuit.X ⟨14, by omega⟩
    ;;ᶜ Circuit.CNOT ⟨0, by omega⟩ ⟨14, by omega⟩ (Fin.ne_of_val_ne (by dsimp; omega))
/-- `0-T` root uninitializer + `Z 0` baseline phase flip on `(0, 14)` inside `Wire N`. -/
def uninitZKickCirc {N s : ℕ} (hN : 14 + s = N) (hs : 1 ≤ s) : Circuit N := Circuit.CNOT ⟨0, by
    omega⟩ ⟨14, by omega⟩ (Fin.ne_of_val_ne (by dsimp; omega)) ;;ᶜ Circuit.X ⟨14, by omega⟩ ;;ᶜ
    Circuit.Z ⟨0, by omega⟩
/-- Generic 4-stage gated `W`-state packet phase kickback on `N = 14 + s` wires. -/
def kick4PhaseDyn {Var : Type} {N s U1 R1 U2 R2 U3 R3 U4 R4 : ℕ} (v : Var) (hN : 14 + s = N) (hs :
    1 ≤ s) (cfg1 : QRegister (3 + U1 + R1 + R1) N) (cfg2 : QRegister (3 + U2 + R2 + R2) N) (cfg3 :
    QRegister (3 + U3 + R3 + R3) N) (cfg4 : QRegister (3 + U4 + R4 + R4) N) (cMid : Circuit N) :
    DynamicCircuit Var N := .seq (.circuit (initKickCirc hN hs)) (.seq (gatedPhaseDyn v cfg1)
    (.seq (gatedPhaseDyn v cfg2) (.seq (gatedPhaseDyn v cfg3) (.seq (gatedPhaseDyn v cfg4)
    (.seq (.circuit cMid) (.seq (gatedUnphaseDyn v cfg4) (.seq (gatedUnphaseDyn v cfg3) (.seq
    (gatedUnphaseDyn v cfg2) (.seq (gatedUnphaseDyn v cfg1) (.circuit (uninitZKickCirc hN
    hs)))))))))))
theorem countKick4PhaseDyn_arity3 {Var : Type} {N s U1 R1 U2 R2 U3 R3 U4 R4 : ℕ} (v : Var) (hN :
    14 + s = N) (hs : 1 ≤ s) (cfg1 : QRegister (3 + U1 + R1 + R1) N) (cfg2 : QRegister (3 + U2 + R2
    + R2) N) (cfg3 : QRegister (3 + U3 + R3 + R3) N) (cfg4 : QRegister (3 + U4 + R4 + R4) N) {cMid :
    Circuit N} (g : PrimitiveGate 3) (hcMid : cMid.count g = 0) : (kick4PhaseDyn v hN hs cfg1 cfg2
    cfg3 cfg4 cMid).count g = 0 := by
  cases g; simp only [kick4PhaseDyn, initKickCirc, uninitZKickCirc, DynamicCircuit.count,
    count_seq, countGatedPhaseDyn_arity3, countGatedUnphaseDyn_arity3, hcMid]; rfl
theorem countKick4PhaseDyn_t {Var : Type} {N s U1 R1 U2 R2 U3 R3 U4 R4 : ℕ} (v : Var) (hN : 14 +
    s = N) (hs : 1 ≤ s) (cfg1 : QRegister (3 + U1 + R1 + R1) N) (cfg2 : QRegister (3 + U2 + R2 + R2)
    N) (cfg3 : QRegister (3 + U3 + R3 + R3) N) (cfg4 : QRegister (3 + U4 + R4 + R4) N) {cMid :
    Circuit N} (hcMid : cMid.count .T = 0) : (kick4PhaseDyn v hN hs cfg1 cfg2 cfg3 cfg4
    cMid).count .T = (2 * R1 + 2) + (2 * R2 + 2) + (2 * R3 + 2) + (2 * R4 + 2) := by
  simp only [kick4PhaseDyn, initKickCirc, uninitZKickCirc, DynamicCircuit.count, count_seq,
    countGatedPhaseDyn_t, countGatedUnphaseDyn_t, hcMid, show ∀ w : Wire N, (Circuit.X
    w).count .T = 0 from fun _ ↦ rfl, show ∀ w : Wire N, (Circuit.Z w).count .T = 0 from fun _ ↦
    rfl, show ∀ (c t : Wire N) (h : c ≠ t), (Circuit.CNOT c t h).count .T = 0 from fun _ _ _ ↦ rfl]
  omega
/-- Stage-`0` bit-assignment (`uZero := 1 + wPar`) on `Wire N`. -/
def fKick0 {N s : ℕ} (hN : 14 + s = N) (hs : 1 ≤ s) (β : BitAssignment N) : BitAssignment N :=
    Function.update β ⟨14, by omega⟩ (1 + β ⟨0, by omega⟩)
/-- Canonical `5`-bit (`wPar, p_0..p_3`) extension to `BitAssignment N` (zero on `5..N-1`). -/
def mk5AssignN (N : ℕ) (b0 b1 b2 b3 b4 : Bool) : BitAssignment N := fun w ↦ if w.val = 0 then (if
    b0 then 1 else 0) else if w.val = 1 then (if b1 then 1 else 0) else if w.val = 2 then (if b2
    then 1 else 0) else if w.val = 3 then (if b3 then 1 else 0) else if w.val = 4 then (if b4 then 1
    else 0) else 0
/-- Canonical `5`-bit projection of `β : BitAssignment N` onto `0..4`. -/
abbrev m5AssignN {N s : ℕ} (hN : 14 + s = N) (β : BitAssignment N) : BitAssignment N :=
    mk5AssignN N (decide (β ⟨0, by omega⟩ = 1)) (decide (β ⟨1, by omega⟩ = 1)) (decide (β ⟨2, by
    omega⟩ = 1)) (decide (β ⟨3, by omega⟩ = 1)) (decide (β ⟨4, by omega⟩ = 1))
/-- Agreement on `0..4` (`wPar, pkt`) and `14..N-1` (all scratch wires). -/
def Agree5And14N {N : ℕ} (γ₁ γ₂ : BitAssignment N) : Prop := ∀ w : Wire N, (w.val < 5 ∨ 14 ≤
    w.val) → γ₁ w = γ₂ w
theorem stgValid_of_agree5N {N U R : ℕ} (cfg : QRegister (3 + U + R + R) N) (hCfg : ∀ i, (cfg
    i).val < 5 ∨ 14 ≤ (cfg i).val) {γ₁ γ₂ : BitAssignment N} (hAg : Agree5And14N γ₁ γ₂) (hV :
    PhaseValid cfg γ₂) : PhaseValid cfg γ₁ := by
  have heq (i) : γ₁ (cfg i) = γ₂ (cfg i) := hAg (cfg i) (hCfg i)
  simpa only [PhaseValid, stgQEnc, stgHi, stgLo, stgUZero, stgIdle, heq] using hV
theorem stgStep_agree5N {N U R : ℕ} (cfg : QRegister (3 + U + R + R) N) (hCfg : ∀ i, (cfg i).val <
    5 ∨ 14 ≤ (cfg i).val) {γ₁ γ₂ : BitAssignment N} (hAg : Agree5And14N γ₁ γ₂) : Agree5And14N
    (phaseStepAssign cfg γ₁) (phaseStepAssign cfg γ₂) ∧ ∀ w : Wire N, 5 ≤ w.val → w.val < 14 →
    phaseStepAssign cfg γ₁ w = γ₁ w := by
  refine ⟨fun w hw ↦ ?_, fun w h5 h14 ↦ ?_⟩
  · dsimp only [phaseStepAssign]; rw [hAg (stgCtrl cfg) (hCfg _)]; split_ifs
    · exact hAg w hw
    · let sa := swapPairsAssign_apply cfg
      exact stgWire_eq cfg (swapPairsAssign cfg γ₁) (swapPairsAssign cfg γ₂) w
        (fun q ↦ by rw [(sa _).1 q, (sa _).1 q]; exact hAg _ (hCfg _))
        (fun q ↦ by rw [(sa _).2.1 q, (sa _).2.1 q]; exact hAg _ (hCfg _))
        (fun hu ↦ by rw [(sa _).2.2 w hu, (sa _).2.2 w hu]; exact hAg w hw)
  · dsimp only [phaseStepAssign]; split_ifs
    · rfl
    · refine (swapPairsAssign_apply cfg γ₁).2.2 w fun q ↦ ⟨fun h ↦ ?_, fun h ↦ ?_⟩
      · have hwv : w.val = (cfg ⟨3 + U + q.val, by omega⟩).val := congrArg Fin.val h
        rcases hCfg ⟨3 + U + q.val, by omega⟩ with hc | hc <;> omega
      · have hwv : w.val = (cfg ⟨3 + U + R + q.val, by omega⟩).val := congrArg Fin.val h
        rcases hCfg ⟨3 + U + R + q.val, by omega⟩ with hc | hc <;> omega
theorem kick4Phase_valid_and_agree {N s U1 R1 U2 R2 U3 R3 U4 R4 : ℕ} (hN : 14 + s = N) (hs : 1 ≤
    s) (cfg1 : QRegister (3 + U1 + R1 + R1) N) (cfg2 : QRegister (3 + U2 + R2 + R2) N) (cfg3 :
    QRegister (3 + U3 + R3 + R3) N) (cfg4 : QRegister (3 + U4 + R4 + R4) N) (hCfg1 : ∀ i, (cfg1
    i).val < 5 ∨ 14 ≤ (cfg1 i).val) (hCfg2 : ∀ i, (cfg2 i).val < 5 ∨ 14 ≤ (cfg2 i).val) (hCfg3 : ∀
    i, (cfg3 i).val < 5 ∨ 14 ≤ (cfg3 i).val) (hCfg4 : ∀ i, (cfg4 i).val < 5 ∨ 14 ≤ (cfg4 i).val)
    (hHv1 : ∀ a b c d e, PhaseValid cfg1 (fKick0 hN hs (mk5AssignN N a b c d e))) (hHv2 : ∀ a
    b c d e, PhaseValid cfg2 (phaseStepAssign cfg1 (fKick0 hN hs (mk5AssignN N a b c d e))))
    (hHv3 : ∀ a b c d e, PhaseValid cfg3 (phaseStepAssign cfg2 (phaseStepAssign cfg1 (fKick0
    hN hs (mk5AssignN N a b c d e))))) (hHv4 : ∀ a b c d e, PhaseValid cfg4 (phaseStepAssign
    cfg3 (phaseStepAssign cfg2 (phaseStepAssign cfg1 (fKick0 hN hs (mk5AssignN N a b c d
    e)))))) (β : BitAssignment N) (hS : cleanKick hN β) :
    let f0 := fKick0 hN hs; let f1 := fun γ ↦ phaseStepAssign cfg1 (f0 γ)
    let f2 := fun γ ↦ phaseStepAssign cfg2 (f1 γ); let f3 := fun γ ↦ phaseStepAssign cfg3 (f2 γ)
    let f4 := fun γ ↦ phaseStepAssign cfg4 (f3 γ)
    PhaseValid cfg1 (f0 β) ∧ PhaseValid cfg2 (f1 β) ∧ PhaseValid cfg3 (f2 β) ∧ PhaseValid
      cfg4 (f3 β) ∧ Agree5And14N (f4 β) (f4 (m5AssignN hN β)) ∧ ∀ j : Fin 9, f4 β ⟨5 + j.val, by
      omega⟩ = β ⟨5 + j.val, by omega⟩ := by
  intro f0 f1 f2 f3 f4
  let StepAg (g₁ g₀ : BitAssignment N → BitAssignment N) : Prop := Agree5And14N (g₁ β) (g₁
    (m5AssignN hN β)) ∧ ∀ w : Wire N, 5 ≤ w.val → w.val < 14 → g₁ β w = g₀ β w
  have hBase : StepAg f0 id := by
    refine ⟨fun w hw ↦ ?_, fun w _ h14 ↦ Function.update_of_ne (Fin.ne_of_val_ne (by dsimp; omega))
      _ _⟩
    have hz (z : ZMod 2) : (if z = 1 then (1 : ZMod 2) else 0) = z := by
      rcases Solution.CircuitModular.UnsignedGivens.zmod2_eq_zero_or_one z with rfl | rfl <;> decide
    have hb (u : Wire N) (hu : u.val < 5) : β u = m5AssignN hN β u := by
      have hu5 : u.val = 0 ∨ u.val = 1 ∨ u.val = 2 ∨ u.val = 3 ∨ u.val = 4 := by omega
      rcases hu5 with h0 | h1 | h2 | h3 | h4
      · rw [show u = ⟨0, by omega⟩ from Fin.ext h0]; simp [m5AssignN, mk5AssignN, hz]
      · rw [show u = ⟨1, by omega⟩ from Fin.ext h1]; simp [m5AssignN, mk5AssignN, hz]
      · rw [show u = ⟨2, by omega⟩ from Fin.ext h2]; simp [m5AssignN, mk5AssignN, hz]
      · rw [show u = ⟨3, by omega⟩ from Fin.ext h3]; simp [m5AssignN, mk5AssignN, hz]
      · rw [show u = ⟨4, by omega⟩ from Fin.ext h4]; simp [m5AssignN, mk5AssignN, hz]
    dsimp only [f0, fKick0]; by_cases hw14 : w = ⟨14, by omega⟩
    · subst hw14
      rw [Function.update_self, Function.update_self, hb ⟨0, by omega⟩ (by dsimp; omega)]
    · rw [Function.update_of_ne hw14, Function.update_of_ne hw14]; rcases hw with h5 | h14
      · exact hb w h5
      · simp only [m5AssignN, mk5AssignN, show w.val ≠ 0 by omega, show w.val ≠ 1 by omega,
          show w.val ≠ 2 by omega, show w.val ≠ 3 by omega, show w.val ≠ 4 by omega, ↓reduceIte]
        simpa [Nat.add_sub_cancel' h14] using hS ⟨w.val - 14, by have := w.isLt; omega⟩
  have hS1 : StepAg f1 f0 := stgStep_agree5N cfg1 hCfg1 hBase.1
  have hS2 : StepAg f2 f1 := stgStep_agree5N cfg2 hCfg2 hS1.1
  have hS3 : StepAg f3 f2 := stgStep_agree5N cfg3 hCfg3 hS2.1
  have hS4 : StepAg f4 f3 := stgStep_agree5N cfg4 hCfg4 hS3.1
  refine ⟨stgValid_of_agree5N cfg1 hCfg1 hBase.1 (hHv1 _ _ _ _ _), stgValid_of_agree5N cfg2
    hCfg2 hS1.1 (hHv2 _ _ _ _ _), stgValid_of_agree5N cfg3 hCfg3 hS2.1 (hHv3 _ _ _ _ _),
    stgValid_of_agree5N cfg4 hCfg4 hS3.1 (hHv4 _ _ _ _ _), hS4.1, fun j ↦ ?_⟩
  let w : Wire N := ⟨5 + j.val, by omega⟩
  have a : 5 ≤ w.val := by dsimp [w]; omega
  have b : w.val < 14 := by have := j.isLt; dsimp [w]; omega
  exact (hS4.2 w a b).trans ((hS3.2 w a b).trans ((hS2.2 w a b).trans ((hS1.2 w a b).trans (hBase.2
    w a b))))
theorem cleanRealizesKick4PhaseDyn {Var : Type} [Fintype Var] [DecidableEq Var] {N s U1 R1 U2 R2
    U3 R3 U4 R4 : ℕ} (v : Var) (hN : 14 + s = N) (hs : 1 ≤ s) (cfg1 : QRegister (3 + U1 + R1 + R1)
    N) (cfg2 : QRegister (3 + U2 + R2 + R2) N) (cfg3 : QRegister (3 + U3 + R3 + R3) N) (cfg4 :
    QRegister (3 + U4 + R4 + R4) N) (cMid : Circuit N) (czPhase : BitAssignment N → ZMod 2)
    (targetPhase14 : BitAssignment 14 → ZMod 2) (hcMidToff : cMid.count .toffoli = 0) (hcMidKet : ∀
    δ : BitAssignment N, cMid.eval.1.mulVec (Solution.XMeasCircuit.ket δ) =
      Solution.XMeasCircuit.bitSign (czPhase δ) •
    Solution.XMeasCircuit.ket δ) (hInv : ∀ β : BitAssignment N, cleanKick hN β →
      let f0 := fKick0 hN hs; let f1 := fun γ ↦ phaseStepAssign cfg1 (f0 γ)
      let f2 := fun γ ↦ phaseStepAssign cfg2 (f1 γ)
      let f3 := fun γ ↦ phaseStepAssign cfg3 (f2 γ)
      let f4 := fun γ ↦ phaseStepAssign cfg4 (f3 γ)
      PhaseValid cfg1 (f0 β) ∧ PhaseValid cfg2 (f1 β) ∧ PhaseValid cfg3 (f2 β) ∧ PhaseValid
        cfg4 (f3 β) ∧ czPhase (f4 β) + β ⟨0, by omega⟩ =
        targetPhase14 (fun i ↦ β (actKick hN i))) :
    Solution.XMeasCircuit.CleanRealizes v (actKick hN) (scrKick hN)
      (Solution.XMeasCircuit.phaseFlipUnitary targetPhase14)
      (kick4PhaseDyn v hN hs cfg1 cfg2 cfg3 cfg4 cMid) := by
  let f0 := fKick0 hN hs; let f1 := fun γ ↦ phaseStepAssign cfg1 (f0 γ)
  let f2 := fun γ ↦ phaseStepAssign cfg2 (f1 γ); let f3 := fun γ ↦ phaseStepAssign cfg3 (f2 γ)
  let f4 := fun γ ↦ phaseStepAssign cfg4 (f3 γ)
  let φ4 (β : BitAssignment N) : ℂ := Solution.XMeasCircuit.bitSign (czPhase (f4 β))
  let R₀ := ketMapOpHad (cleanKick hN) Solution.XMeasCircuit.ket
  let R₁ := ketMapOpHad (cleanKick hN) (fun β ↦
    Solution.XMeasCircuit.bitSign (targetPhase14 (fun i ↦ β
    (actKick hN i))) • Solution.XMeasCircuit.ket β)
  have h0ne14 : (⟨0, by omega⟩ : Wire N) ≠ ⟨14, by omega⟩ := Fin.ne_of_val_ne (by dsimp; omega)
  have hInit : HadSubspaceStepV v R₀ (ketMapOpHad (cleanKick hN) (fun β ↦
    Solution.XMeasCircuit.ket (f0
    β))) (.circuit (initKickCirc hN hs)) := HadSubspaceStepV.of_circuit _ rfl <| by
    rw [mul_ketMapOpHad]; refine ketMapOpHad_congr fun β hS ↦ ?_
    have h14 : β ⟨14, by omega⟩ = 0 := hS ⟨0, hs⟩
    rw [initKickCirc, eval_seq_mulVecHad, Solution.XMeasCircuit.ket_X, ket_CNOTHad,
      Function.update_idem, Function.update_self, Function.update_of_ne h0ne14, h14]
    dsimp only [f0, fKick0]; congr 2
  have hMid : HadSubspaceStepV v (ketMapOpHad (cleanKick hN) (fun β ↦
    Solution.XMeasCircuit.ket (f4 β)))
    (ketMapOpHad (cleanKick hN) (fun β ↦
      φ4 β • Solution.XMeasCircuit.ket (f4 β))) (.circuit cMid) :=
    HadSubspaceStepV.of_circuit _ hcMidToff <| by
    rw [mul_ketMapOpHad]; exact ketMapOpHad_congr fun β _ ↦ hcMidKet (f4 β)
  have hEnd : HadSubspaceStepV v (ketMapOpHad (cleanKick hN) (fun β ↦
    φ4 β • Solution.XMeasCircuit.ket
    (f0 β))) R₁ (.circuit (uninitZKickCirc hN hs)) := HadSubspaceStepV.of_circuit _ rfl <| by
    rw [mul_ketMapOpHad]; refine ketMapOpHad_congr fun β hS ↦ ?_
    have h14 : β ⟨14, by omega⟩ = 0 := hS ⟨0, hs⟩
    simp only [uninitZKickCirc, f0, fKick0, eval_seq_mulVecHad, Matrix.mulVec_smul,
      ket_CNOTHad, Solution.XMeasCircuit.ket_X, Solution.XMeasCircuit.ket_Z, Function.update_idem,
      Function.update_self, Function.update_of_ne h0ne14, zmod2_add_cancel_rightHad, show (1 :
      ZMod 2) + 1 = 0 from rfl, update_bit_eq_selfHad h14, smul_smul, φ4, ←
      Solution.XMeasCircuit.bitSign_add]
    have hPh : czPhase (f4 β) + β ⟨0, by omega⟩ =
        targetPhase14 (fun i ↦ β (actKick hN i)) := (hInv β hS).2.2.2.2
    rw [hPh]
  have hWp : HadSubspaceStepV v R₀ R₁ (kick4PhaseDyn v hN hs cfg1 cfg2 cfg3 cfg4 cMid) :=
    hInit.seq <| (wpSubspaceGatedPhaseDyn v cfg1 (cleanKick hN) f0 fun b h ↦ (hInv b h).1).seq
    <| (wpSubspaceGatedPhaseDyn v cfg2 (cleanKick hN) f1 fun b h ↦ (hInv b h).2.1).seq <|
    (wpSubspaceGatedPhaseDyn v cfg3 (cleanKick hN) f2 fun b h ↦ (hInv b h).2.2.1).seq <|
    (wpSubspaceGatedPhaseDyn v cfg4 (cleanKick hN) f3 fun b h ↦ (hInv b h).2.2.2.1).seq <|
    hMid.seq <| (wpSubspaceGatedUnphaseDyn v cfg4 (cleanKick hN) f3 φ4 fun b h ↦ ((hInv b
    h).2.2.2.1).2.1).seq <| (wpSubspaceGatedUnphaseDyn v cfg3 (cleanKick hN) f2 φ4 fun b h ↦
    ((hInv b h).2.2.1).2.1).seq <| (wpSubspaceGatedUnphaseDyn v cfg2 (cleanKick hN) f1 φ4 fun b
    h ↦ ((hInv b h).2.1).2.1).seq <| (wpSubspaceGatedUnphaseDyn v cfg1 (cleanKick hN) f0 φ4 fun
    b h ↦ ((hInv b h).1).2.1).seq hEnd
  have hP0 : (scrKick hN).basisOutcomeProjector 0 = R₀ := by
    dsimp only [R₀]; rw [Solution.XMeasCircuit.basisOutcomeProjector_zero_eq_cleanFinsetProj,
      Solution.XMeasCircuit.cleanFinsetProj, ketMapOpHad_ket_eq_diagonal]; congr 1; funext i
    have hiff : (∀ w ∈ (scrKick hN).image, basisBits N i w = 0) ↔ cleanKick hN (basisBits N i)
      := ⟨fun h j ↦ h (scrKick hN j) ((QRegister.mem_image _ _).mpr ⟨j, rfl⟩),
       fun h w hw ↦ by obtain ⟨j, rfl⟩ := (QRegister.mem_image _ w).mp hw; exact h j⟩
    by_cases hs0 : cleanKick hN (basisBits N i)
    · simp only [eq_true (hiff.mpr hs0), eq_true hs0, ↓reduceIte]
    · simp only [eq_false (mt hiff.mp hs0), eq_false hs0, ↓reduceIte]
  let U_k := Solution.XMeasCircuit.phaseFlipUnitary targetPhase14
  have hR1 : ((actKick hN).embedUnitary U_k).1 * R₀ = R₁ := by
    rw [mul_ketMapOpHad]; exact ketMapOpHad_congr fun β _ ↦ by
      rw [Solution.XMeasCircuit.embedUnitary_phaseFlipUnitary,
        Solution.XMeasCircuit.phaseFlipUnitary_mulVec_ket]
  have hDisj : (actKick hN).DisjointWires (scrKick hN) := QRegister.disjoint_iff.mpr fun i _ hij
    ↦ by
      have hv := congrArg Fin.val hij; have := i.isLt; simp [actKick, scrKick] at hv; omega
  refine Solution.XMeasCircuit.CleanRealizes.mkOfDisjoint
    (SelectSwapQROM.disjoint_image_of_disjointWires
    hDisj) hWp.1 (fun Θ hΘ ↦ (hWp.2 Θ hΘ).1) fun Θ hΘ ↦ ?_
  change restrictAssertionToZeroAncilla (wp (kick4PhaseDyn v hN hs cfg1 cfg2 cfg3 cfg4
    cMid).compile Θ) (scrKick hN) = restrictAssertionToZeroAncilla (qcWpQAssign ((actKick
    hN).embedUnitary U_k) Θ) (scrKick hN)
  funext σ; apply Subtype.ext; apply HermitianMat.ext
  have hR0h : R₀ᴴ = R₀ := ketMapOpHad_ket_conjTranspose (cleanKick hN)
  have hR1h : R₁ᴴ = R₀ * ((actKick hN).embedUnitary U_k).1ᴴ := by
    rw [← hR1, Matrix.conjTranspose_mul, hR0h]
  simp only [restrictAssertionToZeroAncilla_coe, conj_apply_mat, hP0, hR0h]
  simp only [← HermitianMat.val_eq_coe]
  rw [qc_wp_qAssign_apply_mat, show R₀ * (wp (kick4PhaseDyn v hN hs cfg1 cfg2 cfg3 cfg4
    cMid).compile Θ σ).1.1 * R₀ = R₀ᴴ * (wp (kick4PhaseDyn v hN hs cfg1 cfg2 cfg3 cfg4
    cMid).compile Θ σ).1.1 * R₀ by rw [hR0h], (hWp.2 Θ hΘ).2 σ, hR1h, ← hR1]
  simp only [Matrix.mul_assoc]
/-! ### `26-T` `25`-Wire (`11` Scratch) & `30`-Wire (`16` Scratch) `mux9AltBit` Kickbacks -/
/-- `26-T` Stage 1 (`p_0 = 1`, `U = 0, R = 1`, `4 T`) on `Wire 25`. -/
def altStgCfg1 : QRegister (3 + 0 + 1 + 1) 25 := hadMkNodupReg ![1, 14, 15, 0, 16] (by decide)
/-- `26-T` Stage 2 (`p_1 = 2`, `U = 1, R = 1`, `4 T`) on `Wire 25`. -/
def altStgCfg2 : QRegister (3 + 1 + 1 + 1) 25 := hadMkNodupReg ![2, 14, 15, 0, 16, 17] (by
    decide)
/-- `26-T` Stage 3 (`p_3 = 4`, `U = 0, R = 3`, `8 T`) on `Wire 25`. -/
def altStgCfg3 : QRegister (3 + 0 + 3 + 3) 25 := hadMkNodupReg ![4, 14, 15, 0, 16, 17, 18, 19,
    20] (by decide)
/-- `26-T` Stage 4 (`p_2 = 3`, `U = 2, R = 4`, `10 T`) on `Wire 25`. -/
def altStgCfg4 : QRegister (3 + 2 + 4 + 4) 25 := hadMkNodupReg ![3, 14, 15, 16, 20, 0, 18, 19,
    17, 21, 22, 23, 24] (by decide)
/-- `9`-`CZ` leaf-to-`keep` phase kickback layer on `Wire 25` (`0 T`). -/
def middleCz9Circ : Circuit 25 := SelectSwapQROM.czCircuit 24 5 (by decide) ;;ᶜ
    SelectSwapQROM.czCircuit 21 6 (by decide) ;;ᶜ SelectSwapQROM.czCircuit 18 7 (by decide) ;;ᶜ
    SelectSwapQROM.czCircuit 22 8 (by decide) ;;ᶜ SelectSwapQROM.czCircuit 23 9 (by decide) ;;ᶜ
    SelectSwapQROM.czCircuit 17 10 (by decide) ;;ᶜ SelectSwapQROM.czCircuit 19 11 (by decide)
    ;;ᶜ SelectSwapQROM.czCircuit 20 12 (by decide) ;;ᶜ SelectSwapQROM.czCircuit 0 13 (by decide)
/-- Phase sum accumulated by `middleCz9Circ` on `δ : BitAssignment 25`. -/
def cz9Phase (δ : BitAssignment 25) : ZMod 2 := δ 24 * δ 5 + δ 21 * δ 6 + δ 18 * δ 7 + δ 22 * δ 8
    + δ 23 * δ 9 + δ 17 * δ 10 + δ 19 * δ 11 + δ 20 * δ 12 + δ 0 * δ 13
theorem middleCz9Circ_mulVec_ket (δ : BitAssignment 25) : middleCz9Circ.eval.1.mulVec
    (Solution.XMeasCircuit.ket δ) = Solution.XMeasCircuit.bitSign (cz9Phase δ) •
        Solution.XMeasCircuit.ket δ := by
  have hcz (a b : Wire 25) (h : a ≠ b) : (SelectSwapQROM.czCircuit a b h).eval.1.mulVec
    (Solution.XMeasCircuit.ket δ) = Solution.XMeasCircuit.bitSign (δ a * δ b) •
        Solution.XMeasCircuit.ket δ := by
    rw [czCircuit_eval_eq_phaseFlipHad a b h, Solution.XMeasCircuit.phaseFlipUnitary_mulVec_ket]
  simp only [middleCz9Circ, eval_seq_mulVecHad, Matrix.mulVec_smul, hcz, smul_smul, ←
    Solution.XMeasCircuit.bitSign_add, cz9Phase, add_comm, add_left_comm, add_assoc]
/-- `26-T`, `25`-wire (`14` active + `11` scratch) gated `W`-state `mux9AltBit` phase kickback. -/
def gatedKeepKickback25Dyn {Var : Type} (v : Var) : DynamicCircuit Var 25 := kick4PhaseDyn v (s
    := 11) rfl (by decide) altStgCfg1 altStgCfg2 altStgCfg3 altStgCfg4 middleCz9Circ
@[simp] theorem countGatedKeepKickback25Dyn_arity3 {Var : Type} (v : Var) (g : PrimitiveGate 3) :
    (gatedKeepKickback25Dyn v).count g = 0 := by
  cases g; exact countKick4PhaseDyn_arity3 v rfl (by decide) _ _ _ _ .TOFF rfl
@[simp] theorem countGatedKeepKickback25Dyn_t {Var : Type} (v : Var) : (gatedKeepKickback25Dyn
    v).count .T = 26 := countKick4PhaseDyn_t v rfl (by decide) _ _ _ _ rfl
/-- Active `14`-wire register `[0, 14)` on `Wire 25`. -/
abbrev act25 : QRegister 14 25 := actKick (N := 25) (s := 11) rfl
/-- Clean `11`-wire scratch register `[14, 25)` on `Wire 25`. -/
abbrev scr25 : QRegister 11 25 := scrKick (N := 25) (s := 11) rfl
/-- Stage-`4` state of `gatedKeepKickback25Dyn` on `Wire 25`. -/
def altFStg4 (β : BitAssignment 25) : BitAssignment 25 := phaseStepAssign altStgCfg4
    (phaseStepAssign altStgCfg3 (phaseStepAssign altStgCfg2 (phaseStepAssign altStgCfg1
    (fKick0 (N := 25) (s := 11) rfl (by decide) β))))
/-- Left-hand phase polynomial `(cz9Phase + wPar)` on `(b0..b4, k)` for `Wire 25`. -/
def lhsKeep25 (b0 b1 b2 b3 b4 : Bool) (k : Fin 9 → ZMod 2) : ZMod 2 :=
  let δ := altFStg4 (mk5AssignN 25 b0 b1 b2 b3 b4)
  (δ 24 * k 0 + δ 21 * k 1 + δ 18 * k 2 + δ 22 * k 3 + δ 23 * k 4 + δ 17 * k 5 + δ 19 * k 6 + δ 20 *
    k 7 + δ 0 * k 8) + b2zHad b0
/-- Right-hand target phase `wPar * mux9AltFormula` on `(b0..b4, k)`. -/
def rhsKeep25 (b0 b1 b2 b3 b4 : Bool) (k : Fin 9 → ZMod 2) : ZMod 2 := b2zHad b0 * b2zHad
    (mux9AltFormula b1 b2 b3 b4 (decide (k 0 = 1)) (decide (k 1 = 1)) (decide (k 2 = 1)) (decide
    (k 3 = 1)) (decide (k 4 = 1)) (decide (k 5 = 1)) (decide (k 6 = 1)) (decide (k 7 = 1)) (decide
    (k 8 = 1)))
theorem keepKickAlt_phase_identity : ∀ (b0 b1 b2 b3 b4 : Bool) (k : Fin 9 → ZMod 2), lhsKeep25
    b0 b1 b2 b3 b4 k = rhsKeep25 b0 b1 b2 b3 b4 k := by
  have h0 : ∀ b0 b1 b2 b3 b4, lhsKeep25 b0 b1 b2 b3 b4 zVec9HadW =
      rhsKeep25 b0 b1 b2 b3 b4 zVec9HadW := by decide
  have he : ∀ b0 b1 b2 b3 b4 (j : Fin 9), lhsKeep25 b0 b1 b2 b3 b4 (eVec9HadW j) =
      rhsKeep25 b0 b1 b2 b3 b4 (eVec9HadW j) := by decide
  intro b0 b1 b2 b3 b4 k
  have hdec (z : ZMod 2) : b2zHad (decide (z = 1)) = z := by fin_cases z <;> rfl
  have hnot (x : Bool) : b2zHad (!x) = 1 - b2zHad x := by cases x <;> rfl
  have hl : lhsKeep25 b0 b1 b2 b3 b4 k = lhsKeep25 b0 b1 b2 b3 b4 zVec9HadW + sum9HadW fun j ↦
    (lhsKeep25 b0 b1 b2 b3 b4 (eVec9HadW j) - lhsKeep25 b0 b1 b2 b3 b4 zVec9HadW) * k j := by
    dsimp [lhsKeep25, sum9HadW, eVec9HadW, zVec9HadW]; ring
  have hr : rhsKeep25 b0 b1 b2 b3 b4 k = rhsKeep25 b0 b1 b2 b3 b4 zVec9HadW + sum9HadW fun j ↦
    (rhsKeep25 b0 b1 b2 b3 b4 (eVec9HadW j) - rhsKeep25 b0 b1 b2 b3 b4 zVec9HadW) * k j := by
    dsimp only [rhsKeep25, sum9HadW]; simp only [mux9AltFormula, b2zHad_ite_not, hnot, hdec]
    dsimp [eVec9HadW, zVec9HadW]; ring
  rw [hl, hr, h0]; dsimp only [sum9HadW]; simp only [he]
theorem cleanRealizesGatedKeepKickback25Dyn {Var} [Fintype Var] [DecidableEq Var] (v : Var) :
    Solution.XMeasCircuit.CleanRealizes v act25 scr25 keepKickAlt14Unitary
      (gatedKeepKickback25Dyn v)
    := by
  refine cleanRealizesKick4PhaseDyn (N := 25) (s := 11) v rfl (by decide) altStgCfg1
    altStgCfg2 altStgCfg3 altStgCfg4 middleCz9Circ cz9Phase (keepKickPhaseOf
    mux9AltBit) rfl middleCz9Circ_mulVec_ket fun β hS ↦ ?_
  have hVA := kick4Phase_valid_and_agree (N := 25) (s := 11) rfl (by decide) altStgCfg1
    altStgCfg2 altStgCfg3 altStgCfg4 (by decide) (by decide) (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) β hS
  refine ⟨hVA.1, hVA.2.1, hVA.2.2.1, hVA.2.2.2.1, ?_⟩
  obtain ⟨hAg, hk9⟩ := hVA.2.2.2.2
  let p4 : Fin 4 → Bool := fun i ↦ decide (β ⟨1 + i.val, by omega⟩ = 1)
  let k9 : Fin 9 → ZMod 2 := fun j ↦ β ⟨5 + j.val, by omega⟩
  have hb0 : b2zHad (decide (β 0 = 1)) = β 0 := by
    rcases Solution.CircuitModular.UnsignedGivens.zmod2_eq_zero_or_one (β 0) with h | h <;>
      simp [b2zHad, h]
  have hM5 : m5AssignN (N := 25) (s := 11) rfl β = mk5AssignN 25 (decide (β 0 = 1))
      (decide (β 1 = 1)) (decide (β 2 = 1)) (decide (β 3 = 1)) (decide (β 4 = 1)) := rfl
  change Agree5And14N (altFStg4 β) (altFStg4 (m5AssignN (N := 25) (s := 11) rfl β)) at hAg
  rw [hM5] at hAg; change ∀ j : Fin 9, altFStg4 β ⟨5 + j.val, _⟩ = k9 j at hk9
  have hk (w : Wire 25) (j : Fin 9) (hw : w = ⟨5 + j.val, by omega⟩) : altFStg4 β w = k9 j := hw ▸
    hk9 j
  have hLhs : cz9Phase (altFStg4 β) + β 0 = lhsKeep25 (decide (β 0 = 1)) (decide (β 1 = 1))
    (decide (β 2 = 1)) (decide (β 3 = 1)) (decide (β 4 = 1)) k9 := by
    dsimp only [cz9Phase, lhsKeep25]; rw [hb0, hAg 24 (by decide), hAg 21 (by decide), hAg 18
      (by decide), hAg 22 (by decide), hAg 23 (by decide), hAg 17 (by decide), hAg 19 (by decide),
      hAg 20 (by decide), hAg 0 (by decide), hk 5 0 (by decide), hk 6 1 (by decide), hk 7 2
      (by decide), hk 8 3 (by decide), hk 9 4 (by decide), hk 10 5 (by decide), hk 11 6 (by decide),
      hk 12 7 (by decide), hk 13 8 (by decide)]
  have hpEq : (fun i : Fin 4 ↦ decide (β (act25 ⟨1 + i.val, by omega⟩) = 1)) = p4 :=
    funext fun i ↦ by fin_cases i <;> rfl
  have hqEq : (fun j : Fin 9 ↦ decide (β (act25 ⟨5 + j.val, by omega⟩) = 1)) =
      fun j ↦ decide (k9 j = 1) := funext fun j ↦ by fin_cases j <;> rfl
  have hRhs : rhsKeep25 (decide (β 0 = 1)) (decide (β 1 = 1)) (decide (β 2 = 1)) (decide (β 3 =
    1)) (decide (β 4 = 1)) k9 = keepKickPhaseOf mux9AltBit (fun i ↦ β (act25 i)) := by
    dsimp only [keepKickPhaseOf, rhsKeep25]
    rw [hb0, show act25 0 = 0 from rfl, congrArg (finOfBits 4) hpEq, congrArg (finOfBits 9) hqEq,
      mux9AltBit_finOfBitsHad p4 (fun j ↦ decide (k9 j = 1))]; rfl
  exact hLhs.trans ((keepKickAlt_phase_identity _ _ _ _ _ k9).trans hRhs)
/-- Active wire count `2 * (p0 + 1) + 13` for `nPairs = p0 + 1` data pairs + `pkt ++ keep`. -/
abbrev nActGen (p0 : ℕ) : ℕ := 2 * (p0 + 1) + 13
/-- Clean scratch wire count `(p0 + 1) + sKick` (`nPairs` AND ancillas + `sKick` kickback wires). -/
abbrev nScrGen (p0 sKick : ℕ) : ℕ := (p0 + 1) + sKick
/-- Total local wire count `(2 * (p0 + 1) + 13) + ((p0 + 1) + sKick)`. -/
abbrev nLocGen (p0 sKick : ℕ) : ℕ := nActGen p0 + nScrGen p0 sKick
theorem onRegister_cnotHad {k n : ℕ} (r : QRegister k n) (c t : Wire k) (h : c ≠ t) :
    (Circuit.CNOT c t h).onRegister r = Circuit.CNOT (r c) (r t) (r.wires.injective.ne h) := by
  dsimp only [Circuit.CNOT, Circuit.onRegister]; congr 1; ext i; fin_cases i <;> rfl
theorem onRegister_hHad {k n} (r : QRegister k n) (q : Wire k) : (Circuit.H q).onRegister r =
    Circuit.H (r q) := by dsimp only [Circuit.H, Circuit.single, Circuit.onRegister]; congr 1
theorem bitPermUnitary_mulVec_ketHad {n : ℕ} (perm : Equiv.Perm (BitAssignment n)) (β) :
    (CoherentAlias.bitPermUnitary perm).1.mulVec (Solution.XMeasCircuit.ket β) =
        Solution.XMeasCircuit.ket (perm β) := by
  rw [← QRegister.whole_embedUnitary (CoherentAlias.bitPermUnitary perm)]
  exact (embedUnitary_bitPermUnitary_mulVec_ket (QRegister.whole n) perm β).trans (congrArg
    Solution.XMeasCircuit.ket (funext fun u ↦
      CoherentAlias.writeReg_apply_reg β (QRegister.whole n) _ u))
theorem bitPermUnitary_inv_of_involHad {n : ℕ} (perm : Equiv.Perm (BitAssignment n)) (hInv :
    Function.Involutive perm) : (CoherentAlias.bitPermUnitary perm)⁻¹ = CoherentAlias.bitPermUnitary
    perm := by
  symm; apply eq_inv_of_mul_eq_one_left; apply Subtype.ext
  refine Solution.XMeasCircuit.matrix_ext_ket fun β ↦ ?_
  rw [Submonoid.coe_mul, ← Matrix.mulVec_mulVec, Submonoid.coe_one, Matrix.one_mulVec,
    bitPermUnitary_mulVec_ketHad, bitPermUnitary_mulVec_ketHad, hInv β]
/-- Generic `(2 * nP + 13)`-wire controlled-SWAP bit map gated by `muxBit pkt keep`. -/
def pktMuxSwapGenBits (nP : ℕ) (muxBit : Fin (2 ^ 4) → Fin (2 ^ 9) → Bool) (β : BitAssignment (2 *
    nP + 13)) : BitAssignment (2 * nP + 13) :=
  let sw := muxBit (finOfBits 4 fun i ↦ decide (β ⟨2 * nP + i.val, by omega⟩ = 1)) (finOfBits 9 fun
    j ↦ decide (β ⟨2 * nP + 4 + j.val, by omega⟩ = 1))
  fun u ↦ if h1 : u.val < nP then if sw then β ⟨nP + u.val, by omega⟩ else β u else if h2 : u.val <
    2 * nP then if sw then β ⟨u.val - nP, by omega⟩ else β u else β u
theorem pktMuxSwapGenBits_invol (nP : ℕ) (muxBit : Fin (2 ^ 4) → Fin (2 ^ 9) → Bool) :
    Function.Involutive (pktMuxSwapGenBits nP muxBit) := fun β ↦ by
  have hge (q : Wire (2 * nP + 13)) (hq : 2 * nP ≤ q.val) : pktMuxSwapGenBits nP muxBit β q = β q
    := by
    dsimp only [pktMuxSwapGenBits]
    simp [show ¬ (q.val < nP) by omega, show ¬ (q.val < 2 * nP) by omega]
  have hp : (fun i : Fin 4 ↦ decide (pktMuxSwapGenBits nP muxBit β ⟨2 * nP + i.val, by omega⟩ =
    1)) = fun i ↦ decide (β ⟨2 * nP + i.val, by omega⟩ = 1) :=
    funext fun i ↦ by rw [hge ⟨2 * nP + i.val, by omega⟩ (by dsimp; omega)]
  have hk : (fun j : Fin 9 ↦ decide (pktMuxSwapGenBits nP muxBit β ⟨2 * nP + 4 + j.val, by omega⟩
    = 1)) = fun j ↦ decide (β ⟨2 * nP + 4 + j.val, by omega⟩ = 1) :=
    funext fun j ↦ by rw [hge ⟨2 * nP + 4 + j.val, by omega⟩ (by dsimp; omega)]
  funext u; conv_lhs => rw [pktMuxSwapGenBits]
  dsimp only; rw [hp, hk]; by_cases h1 : u.val < nP
  · cases hsw : muxBit (finOfBits 4 fun i ↦ decide (β ⟨2 * nP + i.val, by omega⟩ = 1))
        (finOfBits 9 fun j ↦ decide (β ⟨2 * nP + 4 + j.val, by omega⟩ = 1))
    · simp [h1, pktMuxSwapGenBits, hsw]
    · simp only [h1, ↓reduceDIte, ↓reduceIte, pktMuxSwapGenBits, hsw,
        show ¬ (nP + u.val < nP) by omega, show nP + u.val < 2 * nP by omega]
      exact congrArg β (Fin.ext (by dsimp only; omega))
  · by_cases h2 : u.val < 2 * nP
    · cases hsw : muxBit (finOfBits 4 fun i ↦ decide (β ⟨2 * nP + i.val, by omega⟩ = 1))
          (finOfBits 9 fun j ↦ decide (β ⟨2 * nP + 4 + j.val, by omega⟩ = 1))
      · simp [h1, h2, pktMuxSwapGenBits, hsw]
      · simp only [h1, h2, ↓reduceDIte, ↓reduceIte, pktMuxSwapGenBits, hsw,
          show u.val - nP < nP by omega]; exact congrArg β (Fin.ext (by dsimp only; omega))
    · simp only [h1, h2, ↓reduceDIte, hge u (by omega)]
/-- Involutive bit-permutation equivalence for `pktMuxSwapGenBits nP muxBit`. -/
def pktMuxSwapGenPerm (nP : ℕ) (muxBit : Fin (2 ^ 4) → Fin (2 ^ 9) → Bool) : Equiv.Perm
    (BitAssignment (2 * nP + 13)) := ⟨pktMuxSwapGenBits nP muxBit, pktMuxSwapGenBits nP muxBit,
    pktMuxSwapGenBits_invol nP muxBit, pktMuxSwapGenBits_invol nP muxBit⟩
@[simp] theorem pktMuxSwapGenPerm_apply (nP : ℕ) (muxBit : Fin (2 ^ 4) → Fin (2 ^ 9) → Bool) (γ :
    BitAssignment (2 * nP + 13)) : pktMuxSwapGenPerm nP muxBit γ = pktMuxSwapGenBits nP muxBit γ
    := rfl
/-- Unitary realization of `pktMuxSwapGenPerm nP muxBit` on `2 * nP + 13` wires. -/
noncomputable def pktMuxSwapGenUnitary (nP : ℕ) (muxBit : Fin (2 ^ 4) → Fin (2 ^ 9) → Bool) :
    Unitary (2 ^ (2 * nP + 13)) := CoherentAlias.bitPermUnitary (pktMuxSwapGenPerm nP muxBit)
theorem pktMuxSwapGenUnitary_inv (nP : ℕ) (muxBit : Fin (2 ^ 4) → Fin (2 ^ 9) → Bool) :
    (pktMuxSwapGenUnitary nP muxBit)⁻¹ = pktMuxSwapGenUnitary nP muxBit :=
    bitPermUnitary_inv_of_involHad _ (pktMuxSwapGenBits_invol nP muxBit)
/-- Embeds `14 + sKick` kickback wires (`wPar`, `pkt ++ keep`, `sKick` scratch) in `nLocGen`. -/
def placeKickGen (p0 sKick : ℕ) : QRegister (14 + sKick) (nLocGen p0 sKick) :=
  mkReg (fun i ↦ if i.val = 0 then nActGen p0 + p0
      else if i.val < 14 then 2 * (p0 + 1) + (i.val - 1) else nActGen p0 + (p0 + 1) + (i.val - 14))
    (fun i ↦ by have hi := i.isLt; dsimp only [nLocGen, nActGen, nScrGen]; split_ifs <;> omega)
    (fun i j h ↦ by have hi := i.isLt; have hj := j.isLt; dsimp only [nActGen] at h
                    split_ifs at h <;> omega)
/-- `m`-CNOT fan-in folding `w_0 .. w_{m - 1}` onto `wPar = nActGen p0 + p0` (`0 T`). -/
def xorFanInPre (p0 : ℕ) : (m : ℕ) → m ≤ p0 → Circuit (nActGen p0 + (p0 + 1))
  | 0, _ => Circuit.identity
  | m + 1, hm => xorFanInPre p0 m (by omega) ;;ᶜ
      Circuit.CNOT ⟨nActGen p0 + m, by omega⟩ ⟨nActGen p0 + p0, by omega⟩
        (Fin.ne_of_val_ne (by dsimp; omega))
theorem countXorFanInPre_arity3 (p0 : ℕ) (g : PrimitiveGate 3) : ∀ (m : ℕ) (hm : m ≤ p0),
    (xorFanInPre p0 m hm).count g = 0
  | 0, _ => rfl
  | m + 1, _ => by rw [xorFanInPre, count_seq, countXorFanInPre_arity3 p0 g m _]; rfl
theorem countXorFanInPre_t (p0 : ℕ) : ∀ m (hm : m ≤ p0), (xorFanInPre p0 m hm).count .T = 0
  | 0, _ => rfl
  | m + 1, _ => by rw [xorFanInPre, count_seq, countXorFanInPre_t p0 m _]; rfl
theorem xorFanInPre_mulVec_ket (p0 sKick : ℕ) :
    let rFan := QRegister.block 0 (nActGen p0 + (p0 + 1))
      (by dsimp [nLocGen, nScrGen]; omega : 0 + (nActGen p0 + (p0 + 1)) ≤ nLocGen p0 sKick)
    let wPar : Wire (nLocGen p0 sKick) := ⟨nActGen p0 + p0, by dsimp [nLocGen, nScrGen]; omega⟩
    ∀ (m : ℕ) (hm : m ≤ p0) (γ : BitAssignment (nLocGen p0 sKick)), (rFan.embedUnitary
      (xorFanInPre p0 m hm).eval).1.mulVec (Solution.XMeasCircuit.ket γ) =
        Solution.XMeasCircuit.ket (Function.update γ
      wPar
          (γ wPar + ∑ j : Fin m, γ ⟨nActGen p0 + j.val, by dsimp [nLocGen, nScrGen]; omega⟩)) := by
  intro rFan wPar m hm γ
  induction m with
  | zero =>
    rw [xorFanInPre, Circuit.eval_identity, QRegister.embedUnitary_one, Submonoid.coe_one,
      Matrix.one_mulVec, Finset.univ_eq_empty, Finset.sum_empty, add_zero, Function.update_eq_self]
  | succ m ih =>
    rw [xorFanInPre, ← Circuit.eval_onRegister, Circuit.onRegister_seq, eval_seq_mulVecHad,
      onRegister_cnotHad, Circuit.eval_onRegister, ih (by omega)]
    have hc : rFan ⟨nActGen p0 + m, by omega⟩ =
        ⟨nActGen p0 + m, by dsimp [nLocGen, nScrGen]; omega⟩ := Fin.ext (Nat.zero_add _)
    have ht : rFan ⟨nActGen p0 + p0, by omega⟩ = wPar := Fin.ext (Nat.zero_add _)
    have hne : (⟨nActGen p0 + m, by dsimp [nLocGen, nScrGen]; omega⟩ : Wire (nLocGen p0 sKick)) ≠
        wPar := Fin.ne_of_val_ne (by dsimp [wPar]; omega)
    rw [ket_CNOTHad, hc, ht, Function.update_idem, Function.update_self,
      Function.update_of_ne hne, Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]; rw [add_assoc]
/-- `muxBit` selector read from wires `2 * (p0 + 1) .. nActGen p0 - 1` of `nLocGen p0 sKick`. -/
def swGenBit (p0 sKick : ℕ) (muxBit : Fin (2 ^ 4) → Fin (2 ^ 9) → Bool) (β : BitAssignment
    (nLocGen p0 sKick)) : ZMod 2 := if muxBit (finOfBits 4 fun i ↦ decide (β ⟨2 * (p0 + 1) + i.val,
        by dsimp [nLocGen, nActGen]; omega⟩ = 1))
      (finOfBits 9 fun j ↦ decide (β ⟨2 * (p0 + 1) + 4 + j.val,
        by dsimp [nLocGen, nActGen]; omega⟩ = 1)) then 1 else 0
theorem swGenBit_update_not_sel (p0 sKick : ℕ) (muxBit : Fin (2 ^ 4) → Fin (2 ^ 9) → Bool) (β :
    BitAssignment (nLocGen p0 sKick)) (w : Wire (nLocGen p0 sKick)) (hw : w.val < 2 * (p0 + 1) ∨
    nActGen p0 ≤ w.val) (b : ZMod 2) : swGenBit p0 sKick muxBit (Function.update β w b) =
    swGenBit p0 sKick muxBit β := by
  have hSel (u : Wire (nLocGen p0 sKick)) (h1 : 2 * (p0 + 1) ≤ u.val) (h2 : u.val < nActGen p0) :
    Function.update β w b u = β u := Function.update_of_ne (Fin.ne_of_val_ne (by rcases hw with h |
    h <;> omega)) _ _
  dsimp only [swGenBit]
  simp only [fun i : Fin 4 ↦ hSel ⟨2 * (p0 + 1) + i.val, by dsimp [nLocGen, nActGen]; omega⟩
      (by dsimp; omega) (by dsimp [nActGen]; omega),
    fun j : Fin 9 ↦ hSel ⟨2 * (p0 + 1) + 4 + j.val, by dsimp [nLocGen, nActGen]; omega⟩
      (by dsimp; omega) (by dsimp [nActGen]; omega)]
/-- Intermediate phase polynomial after `m ≤ p0 + 1` `andSandwichDyn` steps on `nLocGen`. -/
def loopPhaseGen (p0 sKick : ℕ) (muxBit : Fin (2 ^ 4) → Fin (2 ^ 9) → Bool) (m : ℕ) (β :
    BitAssignment (nLocGen p0 sKick)) : ZMod 2 := (∑ r : Fin (p0 + 1), if p0 + 1 - m ≤ r.val then
      β ⟨r.val, by dsimp [nLocGen, nActGen]; omega⟩ *
        β ⟨(p0 + 1) + r.val, by dsimp [nLocGen, nActGen]; omega⟩
    else β ⟨nActGen p0 + r.val, by dsimp [nLocGen, nScrGen]; omega⟩) *
    swGenBit p0 sKick muxBit β
/-- Clean scratch register of width `sKick + m` after `m ≤ p0 + 1` steps on `nLocGen p0 sKick`. -/
def loopScrGen (p0 sKick m : ℕ) (hm : m ≤ p0 + 1) : QRegister (sKick + m) (nLocGen p0 sKick) :=
  QRegister.block (nActGen p0 + (p0 + 1) - m) (sKick + m) (by dsimp [nLocGen, nScrGen]; omega)
theorem extractIndex_zeroHad {k n : ℕ} (r : QRegister k n) : r.extractIndex 0 = 0 := by
  apply (basisBits k).injective; funext i
  rw [r.basisBits_extractIndex, CoherentAlias.basisBits_zero_apply,
    CoherentAlias.basisBits_zero_apply]
attribute [irreducible] cnotSwap3HadW hadCtrlHPair lumpIdleCirc splitAndParityCirc
  swapPairsPhaseCirc gatedPhaseDyn foldPairsPhaseCirc unloadPairsPhaseDyn
  gatedUnphaseDyn initKickCirc uninitZKickCirc kick4PhaseDyn middleCz9Circ
  gatedKeepKickback25Dyn xorFanInPre

end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.HadWStateMux25CompactA
end
