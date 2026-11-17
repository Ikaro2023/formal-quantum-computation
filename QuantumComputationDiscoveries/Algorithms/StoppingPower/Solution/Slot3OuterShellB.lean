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

public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.SubvoxelNucTrunc36
public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.Slot3OuterShellA

set_option Elab.async false

@[expose] public section
set_option allowUnsafeReducibility true
set_option exponentiation.threshold 256

namespace QuantumComputation.Specs.StoppingPowerSolution
open SpecsAux

section Slot3Outer2344AndRelayWide_p2
local instance (priority := 1000000) instNeZeroTwoPow_Slot3Outer2344AndRelayWide_p2 (k : ℕ) :
    NeZero (2 ^ k) := ⟨(Nat.two_pow_pos k).ne'⟩

public section

/-! # Slot3Outer2344AndRelayWide: Non-Booth 2,344 T Slot-3 Outer Shell and 262w Relay Infrastructure

Non-Booth Slot-3 outer shell (`pStep1Ultra` 1,288 T, `dSTrue18RevPBuf145_275` 580 T,
`dRevTailRet216_275` 288 T) plus `411`-wire truncation and `swapA`/`StepBundle` relay lemmas. -/

namespace Slot3Outer2344AndRelayWide

namespace Slot3MidKickWidthWide
section ConfigSlot3MidKickWidthWide
set_option maxRecDepth 8192

local instance (priority :=
  100) instLoc_Slot3Outer2344AndRelayWide_8InstNeZeroTwoPow (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩

noncomputable section

open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt HermitianMat Real
open scoped Matrix ComplexOrder MatrixOrder BigOperators Circuit.Notation
-- Root solution namespace already active.
open MomSlot0CircuitHalf (padZeroBits)
open ShiftedMagS1
open _root_.QuantumComputation.Specs.StoppingPowerSolution.Slot3Outer2344AndRelayWide.PosPhase246
  (progSupportsBelowB truncateProgB)

/-! ## Section 2A: Register-Permutation Relay & `411`-Wire Truncation Infrastructure -/

open MeasureBranchHadamardSem (ket matrix_ext_ket
   projZeroAll ket_projZeroAll projZeroAll_conjTranspose
   RealizesCleanUnitary)
open StreamingBchComparator (PreservesStoreConst)
open StepBBlock0 (padZeroBits149_clean)
open Prod57BoothHoist (p57DiagProj ket_p57DiagProj p57DiagProj_conjTranspose p57CleanDiagProj
  ket_p57CleanDiagProj sTrue18FwdPBuf275)
open StepBOuter (coinMuXor275 magUnpack275)
open Slot3Exact216Oracle80
  (validStatic216_275)
open Slot3Outer2344AndRelayWide.Slot3Exact216TruncBr31
  (axisStep3_fast_275)
open _root_.QuantumComputation.Specs.StoppingPowerSolution.Slot3Outer2344AndRelayWide.PosPhase246
  (cliffSupportsBelowB truncateCliffB)

def cliffDisjointBad {M : ℕ} (bad : Wire M → Bool) : CliffProg M → Bool
  | .nil => true
  | .x q => !bad q
  | .cnot c t _ => !bad c && !bad t
  | .seq c₁ c₂ => cliffDisjointBad bad c₁ && cliffDisjointBad bad c₂

def progDisjointBad {M : ℕ} (bad : Wire M → Bool) : TempPhaseProg M → Bool
  | .nil => true
  | .cliff c => cliffDisjointBad bad c
  | .z q => !bad q
  | .seq p₁ p₂ => progDisjointBad bad p₁ && progDisjointBad bad p₂
  | .tempAnd c₁ c₂ anc _ _ _ body =>
      !bad c₁ && (!bad c₂ && (!bad anc && progDisjointBad bad body))

theorem cliffDisjointBad_eval {M : ℕ} (bad : Wire M → Bool) :
    ∀ (c : CliffProg M) (_ : cliffDisjointBad bad c = true)
      (γ₁ γ₂ : BitAssignment M),
      (∀ w, bad w = false → γ₁ w = γ₂ w) →
      (∀ w, bad w = false → c.eval γ₁ w = c.eval γ₂ w) ∧
      (∀ w, bad w = true → c.eval γ₁ w = γ₁ w)
  | .nil, _, _, _, hEq => ⟨hEq, fun _ _ ↦ rfl⟩
  | .x q, hq, γ₁, γ₂, hEq => by
      have hqF : bad q = false := Bool.not_eq_true' _ |>.mp hq
      dsimp only [CliffProg.eval]
      refine ⟨fun w hw ↦ ?_, fun w hw ↦ ?_⟩
      · by_cases h : w = q
        · subst h; rw [Function.update_self, Function.update_self, hEq w hw]
        · rw [Function.update_of_ne h, Function.update_of_ne h, hEq w hw]
      · have hne : w ≠ q := fun h ↦ by subst h; rw [hqF] at hw; exact Bool.noConfusion hw
        rw [Function.update_of_ne hne]
  | .cnot c t _, h, γ₁, γ₂, hEq => by
      obtain ⟨hc0, ht0⟩ := Bool.and_eq_true _ _ |>.mp h
      have hcF : bad c = false := Bool.not_eq_true' _ |>.mp hc0
      have htF : bad t = false := Bool.not_eq_true' _ |>.mp ht0
      dsimp only [CliffProg.eval]
      refine ⟨fun w hw ↦ ?_, fun w hw ↦ ?_⟩
      · by_cases hwt : w = t
        · subst hwt
          rw [Function.update_self, Function.update_self, hEq w hw, hEq c hcF]
        · rw [Function.update_of_ne hwt, Function.update_of_ne hwt, hEq w hw]
      · have hne : w ≠ t := fun hwt ↦ by subst hwt; rw [htF] at hw; exact Bool.noConfusion hw
        rw [Function.update_of_ne hne]
  | .seq c₁ c₂, h, γ₁, γ₂, hEq => by
      obtain ⟨h1, h2⟩ := Bool.and_eq_true _ _ |>.mp h
      obtain ⟨hEq1, hBad1⟩ := cliffDisjointBad_eval bad c₁ h1 γ₁ γ₂ hEq
      obtain ⟨hEq2, hBad2⟩ := cliffDisjointBad_eval bad c₂ h2 (c₁.eval γ₁) (c₁.eval γ₂) hEq1
      exact ⟨hEq2, fun w hw ↦ (hBad2 w hw).trans (hBad1 w hw)⟩

theorem progDisjointBad_eval {M : ℕ} (bad : Wire M → Bool) :
    ∀ (p : TempPhaseProg M) (_ : progDisjointBad bad p = true)
      (γ₁ γ₂ : BitAssignment M),
      (∀ w, bad w = false → γ₁ w = γ₂ w) →
      p.evalSign γ₁ = p.evalSign γ₂ ∧
      (∀ w, bad w = false → p.evalBits γ₁ w = p.evalBits γ₂ w) ∧
      (∀ w, bad w = true → p.evalBits γ₁ w = γ₁ w)
  | .nil, _, _, _, hEq => ⟨rfl, hEq, fun _ _ ↦ rfl⟩
  | .cliff c, hc, γ₁, γ₂, hEq => ⟨rfl, cliffDisjointBad_eval bad c hc γ₁ γ₂ hEq⟩
  | .z q, hq, γ₁, γ₂, hEq => by
      have hqF : bad q = false := Bool.not_eq_true' _ |>.mp hq
      exact ⟨hEq q hqF, hEq, fun _ _ ↦ rfl⟩
  | .seq p₁ p₂, h, γ₁, γ₂, hEq => by
      obtain ⟨h1, h2⟩ := Bool.and_eq_true _ _ |>.mp h
      obtain ⟨hs1, hEq1, hBad1⟩ := progDisjointBad_eval bad p₁ h1 γ₁ γ₂ hEq
      obtain ⟨hs2, hEq2, hBad2⟩ :=
        progDisjointBad_eval bad p₂ h2 (p₁.evalBits γ₁) (p₁.evalBits γ₂) hEq1
      refine ⟨by dsimp [TempPhaseProg.evalSign]; rw [hs1, hs2],
        hEq2, fun w hw ↦ (hBad2 w hw).trans (hBad1 w hw)⟩
  | .tempAnd c₁ c₂ anc _ _ _ body, h, γ₁, γ₂, hEq => by
      obtain ⟨h1, hr1⟩ := Bool.and_eq_true _ _ |>.mp h
      obtain ⟨h2, hr2⟩ := Bool.and_eq_true _ _ |>.mp hr1
      obtain ⟨h3, hbody⟩ := Bool.and_eq_true _ _ |>.mp hr2
      have hc1F : bad c₁ = false := Bool.not_eq_true' _ |>.mp h1
      have hc2F : bad c₂ = false := Bool.not_eq_true' _ |>.mp h2
      have haF : bad anc = false := Bool.not_eq_true' _ |>.mp h3
      let δ₁ := Function.update γ₁ anc (γ₁ anc + γ₁ c₁ * γ₁ c₂)
      let δ₂ := Function.update γ₂ anc (γ₂ anc + γ₂ c₁ * γ₂ c₂)
      have hδ_eq : ∀ w, bad w = false → δ₁ w = δ₂ w := fun w hw ↦ by
        dsimp only [δ₁, δ₂]
        by_cases hwa : w = anc
        · subst hwa
          rw [Function.update_self, Function.update_self, hEq w haF, hEq c₁ hc1F, hEq c₂ hc2F]
        · rw [Function.update_of_ne hwa, Function.update_of_ne hwa, hEq w hw]
      obtain ⟨hsB, hEqB, hBadB⟩ := progDisjointBad_eval bad body hbody δ₁ δ₂ hδ_eq
      dsimp only [TempPhaseProg.evalSign, TempPhaseProg.evalBits]
      refine ⟨hsB, fun w hw ↦ ?_, fun w hw ↦ ?_⟩
      · by_cases hwa : w = anc
        · subst hwa
          rw [Function.update_self, Function.update_self,
            hEqB w haF, hEqB c₁ hc1F, hEqB c₂ hc2F]
        · rw [Function.update_of_ne hwa, Function.update_of_ne hwa, hEqB w hw]
      · have hne : w ≠ anc := fun hwa ↦ by subst hwa; rw [haF] at hw; exact Bool.noConfusion hw
        rw [Function.update_of_ne hne, hBadB w hw]
        dsimp only [δ₁]
        rw [Function.update_of_ne hne]

theorem aux_block0_wire_eq {M' M n : ℕ} (hMM : 0 + M' ≤ M) (r : QRegister M n)
    (w : Wire M) (hw : w.val < M') : r ((QRegister.block 0 M' hMM).wires ⟨w.val, hw⟩) = r w :=
  congrArg r (Fin.ext (by simp))

theorem truncateCliffB_onRegister_eq {M' M n : ℕ} (hMM : 0 + M' ≤ M) (r : QRegister M n) :
    ∀ (c : CliffProg M) (hc : cliffSupportsBelowB M' c = true),
      (truncateCliffB M' c hc).onRegister (r.compose (QRegister.block 0 M' hMM)) =
        c.onRegister r
  | .nil, _ => rfl
  | .x q, _ => by
      dsimp only [truncateCliffB, CliffProg.onRegister, QRegister.compose_apply]
      rw [aux_block0_wire_eq]
  | .cnot c t _, _ => by
      dsimp only [truncateCliffB, CliffProg.onRegister, QRegister.compose_apply]
      simp only [aux_block0_wire_eq]
  | .seq c₁ c₂, _ => by
      dsimp only [truncateCliffB, CliffProg.onRegister]
      rw [truncateCliffB_onRegister_eq hMM r c₁, truncateCliffB_onRegister_eq hMM r c₂]

theorem truncateProgB_onRegister_eq {M' M n : ℕ} (hMM : 0 + M' ≤ M) (r : QRegister M n) :
    ∀ (p : TempPhaseProg M) (hp : progSupportsBelowB M' p = true),
      (truncateProgB M' p hp).onRegister (r.compose (QRegister.block 0 M' hMM)) =
        p.onRegister r
  | .nil, _ => rfl
  | .cliff c, hc => by
      dsimp only [truncateProgB, TempPhaseProg.onRegister]
      rw [truncateCliffB_onRegister_eq hMM r c hc]
  | .z q, _ => by
      dsimp only [truncateProgB, TempPhaseProg.onRegister, QRegister.compose_apply]
      rw [aux_block0_wire_eq]
  | .seq p₁ p₂, _ => by
      dsimp only [truncateProgB, TempPhaseProg.onRegister]
      rw [truncateProgB_onRegister_eq hMM r p₁, truncateProgB_onRegister_eq hMM r p₂]
  | .tempAnd c₁ c₂ anc _ _ _ body, _ => by
      dsimp only [truncateProgB, TempPhaseProg.onRegister, QRegister.compose_apply]
      simp only [aux_block0_wire_eq, truncateProgB_onRegister_eq hMM r body]

def isBadA (w : Wire 437) : Bool := decide (201 ≤ w.val ∧ w.val < 227)

def permOfInvol (f : Wire 437 → Wire 437) (hf : ∀ w, f (f w) = w) : Equiv.Perm (Wire 437) where
  toFun := f
  invFun := f
  left_inv := hf
  right_inv := hf

def zeroTop411 (γ : BitAssignment 437) : BitAssignment 437 :=
  fun w ↦ if w.val < 411 then γ w else 0

def lift411 (δ γ : BitAssignment 437) : BitAssignment 437 :=
  fun w ↦ if w.val < 411 then δ w else γ w

theorem zeroTop411_lt {γ : BitAssignment 437} {w : Wire 437} (hw : w.val < 411) :
    zeroTop411 γ w = γ w := FastMidKick275Aux.fmkItePos hw _ _

theorem zeroTop411_ge {γ : BitAssignment 437} {w : Wire 437} (hw : 411 ≤ w.val) :
    zeroTop411 γ w = 0 := FastMidKick275Aux.fmkIteNeg (by omega) _ _

theorem lift411_lt {δ γ : BitAssignment 437} {w : Wire 437} (hw : w.val < 411) :
    lift411 δ γ w = δ w := FastMidKick275Aux.fmkItePos hw _ _

theorem lift411_ge {δ γ : BitAssignment 437} {w : Wire 437} (hw : 411 ≤ w.val) :
    lift411 δ γ w = γ w := FastMidKick275Aux.fmkIteNeg (by omega) _ _

open Classical in
theorem lift411_idem (δ₂ δ₁ γ : BitAssignment 437) :
    lift411 δ₂ (lift411 δ₁ γ) = lift411 δ₂ γ := by
  funext w; dsimp [lift411]; split_ifs <;> rfl

open Classical in
theorem zeroTop411_lift411 {δ : BitAssignment 437} (γ : BitAssignment 437)
    (hcl : cleanRem 437 (437 - 275) δ) : zeroTop411 (lift411 δ γ) = δ := by
  funext w
  dsimp [zeroTop411, lift411]
  split_ifs with hw
  · rfl
  · exact (hcl w (by omega)).symm

abbrev permReg {M : ℕ} (perm : Equiv.Perm (Fin M)) : QRegister M M := ⟨perm.toEmbedding⟩

theorem writeRegProg_compose_perm {M n : ℕ} (β : BitAssignment n) (r : QRegister M n)
    (perm : Equiv.Perm (Fin M)) (δ' : BitAssignment M) : writeRegProg β
    (r.compose (permReg perm)) δ' = writeRegProg β r (fun idx ↦ δ' (perm.symm idx)) := by
  funext w
  by_cases hmem : w ∈ Set.range r.wires
  · obtain ⟨idx, rfl⟩ := hmem
    have h1 : r idx = (r.compose (permReg perm)) (perm.symm idx) := by
      simp [permReg]
    conv_lhs => rw [h1]
    rw [writeRegProg_apply_reg, writeRegProg_apply_reg]
  · have hmem' : w ∉ Set.range (r.compose (permReg perm)).wires := by
      rintro ⟨j, rfl⟩; exact hmem ⟨perm j, rfl⟩
    rw [writeRegProg_apply_of_not_mem _ _ _ _ hmem',
        writeRegProg_apply_of_not_mem _ _ _ _ hmem]

theorem writeRegProg_idem_437 {n : ℕ} (β : BitAssignment n) (r : QRegister 437 n)
    (δ₁ δ₂ : BitAssignment 437) : writeRegProg (writeRegProg β r δ₁) r δ₂ = writeRegProg β r
    δ₂ := FastMidKick275Aux.fmkWriteRegProg_idem β r δ₁ δ₂

/-! ## Section 2B: `baseDiagProj` & Step-Chaining Engine -/

noncomputable def baseDiagProj {n : ℕ} (rCombBase : QRegister 437 n)
    (Inv : BitAssignment 437 → Prop) : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ :=
  p57DiagProj rCombBase (fun γ ↦
    (∀ w : Wire 437, 275 ≤ w.val → w.val < 411 → γ w = 0) ∧ Inv (zeroTop411 γ))

theorem baseDiagProj_conjTranspose {n : ℕ} (rCombBase : QRegister 437 n)
    (Inv : BitAssignment 437 → Prop) : (baseDiagProj rCombBase Inv)ᴴ = baseDiagProj rCombBase
    Inv := p57DiagProj_conjTranspose rCombBase _

open Classical in
theorem ket_baseDiagProj {n : ℕ} (rCombBase : QRegister 437 n)
    (Inv : BitAssignment 437 → Prop) (β : BitAssignment n) :
    (baseDiagProj rCombBase Inv).mulVec (ket β) = if
    (∀ w : Wire 437, 275 ≤ w.val → w.val < 411 → β (rCombBase w) = 0) ∧ Inv
    (zeroTop411 (fun idx ↦ β (rCombBase idx))) then ket β else 0 := by
  rcases Classical.em ((∀ w : Wire 437, 275 ≤ w.val → w.val < 411 → β (rCombBase w) = 0) ∧
      Inv (zeroTop411 (fun idx ↦ β (rCombBase idx)))) with h | h
  · exact (ket_p57DiagProj rCombBase _ β).trans ((ite_eq_left h).trans (ite_eq_left h).symm)
  · exact (ket_p57DiagProj rCombBase _ β).trans ((ite_eq_right h).trans (ite_eq_right h).symm)

/-! ## Section 2C: `StepBundle` Combinator, `clearMW` / `clearMuCoinMW`, & `HasMuCoinMW` -/

open MeasureBranchHadamardSem
  (projZeroAll_eq_basisOutcomeProjector_zero)

structure StepBundle {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)]
    (v : Var) (rCombBase : QRegister 437 n)
    (δ_in δ_out : BitAssignment 149 → BitAssignment 437)
    (sgn : BitAssignment 149 → ZMod 2)
    (d : DynamicCircuit Var n) : Prop where
  hcl_out : ∀ α, cleanRem 437 (437 - 275) (δ_out α)
  store : PreservesStoreConst d
  exists_u : ∃ U : Unitary (2 ^ n),
    RealizesCleanUnitary v (baseDiagProj rCombBase (fun δ ↦ ∃ α, δ = δ_in α)) d U ∧
    (∀ (β : BitAssignment n) (α : BitAssignment 149),
      zeroTop411 (fun idx ↦ β (rCombBase idx)) = δ_in α →
      U.1.mulVec (ket β) =
        ((-1 : ℂ) ^ (sgn α).val) •
          ket (writeRegProg β rCombBase (lift411 (δ_out α) (fun idx ↦ β (rCombBase idx))))) ∧
    baseDiagProj rCombBase (fun δ ↦ ∃ α, δ = δ_out α) *
      (U.1 * baseDiagProj rCombBase (fun δ ↦ ∃ α, δ = δ_in α)) =
      U.1 * baseDiagProj rCombBase (fun δ ↦ ∃ α, δ = δ_in α)

theorem StepBundle.seq {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)]
    {v : Var} {rCombBase : QRegister 437 n}
    {δ_A δ_B δ_C : BitAssignment 149 → BitAssignment 437}
    {sgn1 sgn2 sgn12 : BitAssignment 149 → ZMod 2} {d1 d2 : DynamicCircuit Var n}
    (h1 : StepBundle v rCombBase δ_A δ_B sgn1 d1)
    (h2 : StepBundle v rCombBase δ_B δ_C sgn2 d2) (hsgn : ∀ α, ((-1 : ℂ) ^ (sgn1 α).val) *
    ((-1 : ℂ) ^ (sgn2 α).val) = ((-1 : ℂ) ^ (sgn12 α).val)) : StepBundle v rCombBase δ_A δ_C
    sgn12 (.seq d1 d2) := by
  obtain ⟨U1, hR1, hM1, hC1⟩ := h1.exists_u
  obtain ⟨U2, hR2, hM2, hC2⟩ := h2.exists_u
  refine ⟨h2.hcl_out, PreservesStoreConst.seq h1.store h2.store, ⟨U2 * U1, ?_, ?_, ?_⟩⟩
  · exact RealizesCleanUnitary_seq_asym (baseDiagProj_conjTranspose rCombBase _)
      (baseDiagProj_conjTranspose rCombBase _) hR1 hR2 hC1
  · intro β α htop
    rw [Submonoid.coe_mul, mul_mulVec_prog, hM1 β α htop, Matrix.mulVec_smul]
    let β' := writeRegProg β rCombBase (lift411 (δ_B α) (fun idx ↦ β (rCombBase idx)))
    have hβ'_reg : (fun idx ↦ β' (rCombBase idx)) = lift411 (δ_B α) (fun idx ↦ β (rCombBase idx)) :=
      funext fun idx ↦ writeRegProg_apply_reg _ _ _ idx
    have htop' : zeroTop411 (fun idx ↦ β' (rCombBase idx)) = δ_B α := by
      rw [hβ'_reg, zeroTop411_lift411 _ (h1.hcl_out α)]
    rw [hM2 β' α htop', smul_smul, hsgn α]
    dsimp only [β']
    rw [hβ'_reg, lift411_idem, writeRegProg_idem_437]
  · have h12 : U2.1 * (U1.1 * baseDiagProj rCombBase (fun δ ↦ ∃ α, δ = δ_A α)) =
        (U2.1 * baseDiagProj rCombBase (fun δ ↦ ∃ α, δ = δ_B α)) *
          (U1.1 * baseDiagProj rCombBase (fun δ ↦ ∃ α, δ = δ_A α)) := by
      rw [Matrix.mul_assoc, hC1]
    simp only [Submonoid.coe_mul]
    rw [Matrix.mul_assoc U2.1 U1.1, h12, ← Matrix.mul_assoc _ (U2.1 * _), hC2]

theorem StepBundle.seq_zero_left {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    [NeZero (2 ^ n)] {v : Var} {rCombBase : QRegister 437 n}
    {δ_A δ_B δ_C : BitAssignment 149 → BitAssignment 437} {sgn2 : BitAssignment 149 → ZMod 2}
    {d1 d2 : DynamicCircuit Var n} (h1 : StepBundle v rCombBase δ_A δ_B (fun _ ↦ 0) d1)
    (h2 : StepBundle v rCombBase δ_B δ_C sgn2 d2) : StepBundle v rCombBase δ_A δ_C sgn2
    (.seq d1 d2) :=
  h1.seq h2 (fun _ ↦ by simp)

theorem StepBundle.seq_zero_right {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    [NeZero (2 ^ n)] {v : Var} {rCombBase : QRegister 437 n}
    {δ_A δ_B δ_C : BitAssignment 149 → BitAssignment 437} {sgn1 : BitAssignment 149 → ZMod 2}
    {d1 d2 : DynamicCircuit Var n} (h1 : StepBundle v rCombBase δ_A δ_B sgn1 d1)
    (h2 : StepBundle v rCombBase δ_B δ_C (fun _ ↦ 0) d2) : StepBundle v rCombBase δ_A δ_C sgn1
    (.seq d1 d2) :=
  h1.seq h2 (fun _ ↦ by simp)

open Classical in
theorem StepBundle.to_cleanWorkspace
    {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)]
    (v : Var)
    (rAct149 : QRegister 149 n)
    (rWork : QRegister 262 n)
    (rDummy26 : QRegister 26 n)
    (hAW : rAct149.DisjointWires rWork)
    (hAD : rAct149.DisjointWires rDummy26)
    (hWD : rWork.DisjointWires rDummy26)
    (uTarget : Unitary (2 ^ 149))
    (permTarget : BitAssignment 149 → BitAssignment 149)
    (phaseTarget : BitAssignment 149 → ZMod 2)
    (huTarget : ∀ α : BitAssignment 149,
      uTarget.1 *ᵥ ket α = ((-1 : ℂ) ^ (phaseTarget α).val) • ket (permTarget α))
    (d : DynamicCircuit Var n)
    (hBundle : StepBundle v
      ((rAct149.concat rWork hAW).concat rDummy26 (disjConcatLeft hAD hWD))
      (fun α ↦ padZeroBits (mClean := 288) α)
      (fun α ↦ padZeroBits (mClean := 288) (permTarget α))
      phaseTarget d) :
    DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace rAct149 rWork uTarget d := by
  let rCombBase : QRegister ((149 + 262) + 26) n :=
    (rAct149.concat rWork hAW).concat rDummy26 (disjConcatLeft hAD hWD)
  obtain ⟨U, hR, hM, _⟩ := hBundle.exists_u
  let P_0 := baseDiagProj rCombBase (fun δ ↦ ∃ α, δ = padZeroBits (mClean := 288) α)
  let P_work := projZeroAll 262 rWork.wires
  have hPw : P_workᴴ = P_work := projZeroAll_conjTranspose 262 _
  have hBaseAct : ∀ i : Fin 149, rCombBase (Fin.castAdd 26 (Fin.castAdd 262 i)) = rAct149 i :=
    fun i ↦ by
    dsimp [rCombBase]
    rw [QRegister.concat_apply_left, QRegister.concat_apply_left]
  have hBaseWork : ∀ j : Fin 262, rCombBase (Fin.castAdd 26 (Fin.natAdd 149 j)) = rWork j := fun j ↦
    by
    dsimp [rCombBase]
    rw [QRegister.concat_apply_left, QRegister.concat_apply_right]
  have hBaseDummy : ∀ k : Fin 26, rCombBase (Fin.natAdd (149 + 262) k) = rDummy26 k := fun k ↦ by
    dsimp [rCombBase]
    rw [QRegister.concat_apply_right]
  have hTopOfWork : ∀ (β : BitAssignment n),
      (∀ j : Fin 262, β (rWork j) = 0) →
      (∀ w : Wire 437, 275 ≤ w.val → w.val < 411 → β (rCombBase w) = 0) ∧
        zeroTop411 (fun idx ↦ β (rCombBase idx)) =
          padZeroBits (mClean := 288) (fun i ↦ β (rAct149 i)) := by
    intro β hw
    have hwork0 : ∀ w : Wire 437, 149 ≤ w.val → w.val < 411 → β (rCombBase w) = 0 := fun w hw1 hw2 ↦
      by
      let j : Fin 262 := ⟨w.val - 149, by omega⟩
      have hweq : w = Fin.castAdd 26 (Fin.natAdd 149 j) := Fin.ext (by dsimp [j]; omega)
      rw [hweq, hBaseWork j]
      exact hw j
    refine ⟨fun w hw1 hw2 ↦ hwork0 w (by omega) hw2, funext fun w ↦ ?_⟩
    by_cases hw149 : w.val < 149
    · let i : Fin 149 := ⟨w.val, hw149⟩
      have hweq1 : w = Fin.castAdd 26 (Fin.castAdd 262 i) := Fin.ext rfl
      rw [zeroTop411_lt (by omega), padZeroBits_ltAux (mClean := 288) _ w hw149]
      change β (rCombBase w) = β (rAct149 i)
      rw [hweq1, hBaseAct i]
    · by_cases hw411 : w.val < 411
      · rw [zeroTop411_lt hw411, hwork0 w (by omega) hw411,
          padZeroBits149_clean _ w (by omega)]
      · rw [zeroTop411_ge (by omega), padZeroBits149_clean _ w (by omega)]
  have hSub : P_0 * P_work = P_work := by
    apply matrix_ext_ket; intro β
    simp only [P_0, P_work, mul_mulVec_prog, ket_projZeroAll]
    by_cases hw : ∀ j : Fin 262, β (rWork j) = 0
    · simp only [hw, imp_true_iff, ↓reduceIte, ket_baseDiagProj]
      obtain ⟨hscr, htop⟩ := hTopOfWork β hw
      split_ifs with h0
      · rfl
      · exact absurd ⟨hscr, ⟨_, htop⟩⟩ h0
    · simp only [hw, ↓reduceIte, Matrix.mulVec_zero]
  have hMono := RealizesCleanUnitary.mono_proj (baseDiagProj_conjTranspose rCombBase _) hPw hSub hR
  have hUeq : U.1 * P_work = (rAct149.embedUnitary uTarget).1 * P_work := by
    apply matrix_ext_ket; intro β
    simp only [P_work, mul_mulVec_prog, ket_projZeroAll]
    by_cases hw : ∀ j : Fin 262, β (rWork j) = 0
    · simp only [hw, imp_true_iff, ↓reduceIte]
      let α : BitAssignment 149 := fun i ↦ β (rAct149 i)
      obtain ⟨_, htop⟩ := hTopOfWork β hw
      rw [hM β α htop]
      have hwComb : writeRegProg β rCombBase
          (lift411 (padZeroBits (mClean := 288) (permTarget α)) (fun idx ↦ β (rCombBase idx))) =
          writeRegProg β rAct149 (permTarget α) := by
        funext w
        by_cases hmem : w ∈ Set.range rCombBase.wires
        · obtain ⟨idx, rfl⟩ := hmem
          rw [writeRegProg_apply_reg]
          by_cases h149 : idx.val < 149
          · let i : Fin 149 := ⟨idx.val, h149⟩
            have hidx1 : idx = Fin.castAdd 26 (Fin.castAdd 262 i) := Fin.ext rfl
            rw [lift411_lt (by omega), padZeroBits_ltAux (mClean := 288) (permTarget α) idx h149]
            change permTarget α i = writeRegProg β rAct149 (permTarget α) (rCombBase idx)
            rw [hidx1, hBaseAct i, writeRegProg_apply_reg]
          · by_cases h411 : idx.val < 411
            · let j : Fin 262 := ⟨idx.val - 149, by omega⟩
              have hidx1 : idx = Fin.castAdd 26 (Fin.natAdd 149 j) := Fin.ext (by dsimp [j]; omega)
              have hnotAct : rWork j ∉ Set.range rAct149.wires := by
                rintro ⟨i, hi⟩; exact hAW.ne i j hi
              rw [lift411_lt h411, padZeroBits149_clean _ idx (by omega),
                hidx1, hBaseWork j, writeRegProg_apply_of_not_mem _ _ _ _ hnotAct, hw j]
            · let k : Fin 26 := ⟨idx.val - 411, by omega⟩
              have hidx1 : idx = Fin.natAdd (149 + 262) k := Fin.ext (by dsimp [k]; omega)
              have hnotAct : rDummy26 k ∉ Set.range rAct149.wires := by
                rintro ⟨i, hi⟩; exact hAD.ne i k hi
              rw [lift411_ge (by omega), hidx1, hBaseDummy k,
                writeRegProg_apply_of_not_mem _ _ _ _ hnotAct]
        · have hnotAct : w ∉ Set.range rAct149.wires := by
            rintro ⟨i, rfl⟩
            exact hmem ⟨Fin.castAdd 26 (Fin.castAdd 262 i), hBaseAct i⟩
          rw [writeRegProg_apply_of_not_mem _ _ _ _ hmem,
            writeRegProg_apply_of_not_mem _ _ _ _ hnotAct]
      rw [hwComb, QRegister.embedUnitary_val, embedMatrix_mulVec_ket_prog]
      have hloc : localIdxProg rAct149 β = (basisBitsEquiv 149).symm α := rfl
      rw [hloc]
      have hEvalAct : ∀ l : Fin (2 ^ 149),
          uTarget.1 l ((basisBitsEquiv 149).symm α) =
            if l = (basisBitsEquiv 149).symm (permTarget α) then
              ((-1 : ℂ) ^ (phaseTarget α).val)
            else 0 := fun l ↦ by
        have hk := congrFun (huTarget α) l
        simpa [ket, basisState, Matrix.mulVec_single_one, Pi.single_apply, eq_comm] using hk
      simp_rw [hEvalAct, ite_smul, zero_smul]
      simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
      have hbb : basisBits 149 ((basisBitsEquiv 149).symm (permTarget α)) = permTarget α :=
        (basisBitsEquiv 149).apply_symm_apply _
      rw [hbb]
    · simp [hw]
  have hTarget := RealizesCleanUnitary.congr_unitary hPw hMono hUeq
  intro M_obs
  obtain ⟨M_out, hM_out⟩ := hBundle.store M_obs
  refine ⟨M_out, hM_out, ?_⟩
  have hconj := hTarget.2 (fun _ ↦ M_obs) (fun _ _ ↦ rfl) default
  have hM_eq : wp d.compile (fun _ ↦ M_obs) default = M_out := congrFun hM_out default
  rw [← hM_eq, ← projZeroAll_eq_basisOutcomeProjector_zero rWork]
  simpa [P_work, hPw, wpQAssignCompat, qAssignObsMap, Observable.conj_coe, Unitary.coe_star,
    Matrix.star_eq_conjTranspose, HermitianMat.conj_apply_mat, Matrix.mul_assoc] using
    congrArg Subtype.val hconj

def isBadMW (w : Wire 437) : Bool := decide (177 ≤ w.val ∧ w.val < 198)
def cliffNotTarget {M : ℕ} (keep : Wire M → Bool) : CliffProg M → Bool
  | .nil => true
  | .x q => !keep q
  | .cnot _ t _ => !keep t
  | .seq c₁ c₂ => cliffNotTarget keep c₁ && cliffNotTarget keep c₂

def progNotTarget {M : ℕ} (keep : Wire M → Bool) : TempPhaseProg M → Bool
  | .nil => true
  | .cliff c => cliffNotTarget keep c
  | .z _ => true
  | .seq p₁ p₂ => progNotTarget keep p₁ && progNotTarget keep p₂
  | .tempAnd _ _ anc _ _ _ body => !keep anc && progNotTarget keep body

theorem cliffNotTarget_eval {M : ℕ} (keep : Wire M → Bool) :
    ∀ (c : CliffProg M) (_ : cliffNotTarget keep c = true)
      (ξ : BitAssignment M) (w : Wire M),
      keep w = true → c.eval ξ w = ξ w
  | .nil, _, _, _, _ => rfl
  | .x q, hq, ξ, w, hw => by
      have hqF : keep q = false := Bool.not_eq_true' _ |>.mp hq
      have hne : w ≠ q := fun h ↦ by subst h; rw [hqF] at hw; exact Bool.noConfusion hw
      exact Function.update_of_ne hne _ _
  | .cnot _ t _, ht, ξ, w, hw => by
      have htF : keep t = false := Bool.not_eq_true' _ |>.mp ht
      have hne : w ≠ t := fun h ↦ by subst h; rw [htF] at hw; exact Bool.noConfusion hw
      exact Function.update_of_ne hne _ _
  | .seq c₁ c₂, h, ξ, w, hw => by
      obtain ⟨h1, h2⟩ := Bool.and_eq_true _ _ |>.mp h
      exact (cliffNotTarget_eval keep c₂ h2 (c₁.eval ξ) w hw).trans
        (cliffNotTarget_eval keep c₁ h1 ξ w hw)

theorem progNotTarget_evalBits {M : ℕ} (keep : Wire M → Bool) :
    ∀ (p : TempPhaseProg M) (_ : progNotTarget keep p = true)
      (ξ : BitAssignment M) (w : Wire M),
      keep w = true → p.evalBits ξ w = ξ w
  | .nil, _, _, _, _ => rfl
  | .cliff c, hc, ξ, w, hw => cliffNotTarget_eval keep c hc ξ w hw
  | .z _, _, _, _, _ => rfl
  | .seq p₁ p₂, h, ξ, w, hw => by
      obtain ⟨h1, h2⟩ := Bool.and_eq_true _ _ |>.mp h
      exact (progNotTarget_evalBits keep p₂ h2 (p₁.evalBits ξ) w hw).trans
        (progNotTarget_evalBits keep p₁ h1 ξ w hw)
  | .tempAnd _ _ anc _ _ _ body, h, ξ, w, hw => by
      obtain ⟨ha, hb⟩ := Bool.and_eq_true _ _ |>.mp h
      have haF : keep anc = false := Bool.not_eq_true' _ |>.mp ha
      have hne : w ≠ anc := fun h ↦ by subst h; rw [haF] at hw; exact Bool.noConfusion hw
      dsimp only [TempPhaseProg.evalBits]
      rw [Function.update_of_ne hne, progNotTarget_evalBits keep body hb _ w hw,
        Function.update_of_ne hne]

def pStep1 : TempPhaseProg 437 :=
  .seq coinMuXor275 (.seq magUnpack275 (.seq validStatic216_275 (.seq axisStep3_fast_275
    sTrue18FwdPBuf275)))

def st0 (α : BitAssignment 149) : BitAssignment 437 :=
  padZeroBits (mClean := 288) α

def st1 (α : BitAssignment 149) : BitAssignment 437 := pStep1.evalBits (st0 α)

open Classical in
theorem p57CleanDiagProj_true_eq {M n : ℕ} (rComb : QRegister M n) (rem : ℕ) (hrem : rem ≤ M) :
    p57CleanDiagProj rComb rem hrem (fun _ ↦ True) = projZeroAll rem (tailScr rComb rem hrem) := by
  apply matrix_ext_ket; intro β
  rw [ket_p57CleanDiagProj, ket_projZeroAll]
  have hiff : (cleanRem M rem (fun idx ↦ β (rComb idx)) ∧ True) ↔
      (∀ j : Fin rem, β (tailScr rComb rem hrem j) = 0) := by
    constructor
    · rintro ⟨hcl, _⟩ j
      exact hcl ⟨(M - rem) + j.val, by omega⟩ (by dsimp; omega)
    · intro hj
      refine ⟨fun w hw ↦ ?_, trivial⟩
      have hweq : rComb w = tailScr rComb rem hrem ⟨w.val - (M - rem), by omega⟩ :=
        congrArg rComb (Fin.ext (by dsimp; omega))
      dsimp only
      rw [hweq]
      exact hj _
  split_ifs with h1 h2 h2
  · rfl
  · exact absurd (hiff.mp h1) h2
  · exact absurd (hiff.mpr h2) h1
  · rfl

/-! ## Section 3: `dCoreExact216_262`, `dSlot3Exact216_262`, & Turnkey `mWork = 262` Oracle -/

end
end ConfigSlot3MidKickWidthWide
end Slot3MidKickWidthWide

namespace Slot3UltraWidthWide
section ConfigSlot3UltraWidthWide
set_option maxRecDepth 8192

local instance (priority :=
  1000000) instLoc_Slot3Outer2344AndRelayWide_9InstNeZeroTwoPow (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩

noncomputable section

open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt HermitianMat Real
open scoped Matrix ComplexOrder MatrixOrder BigOperators Matrix.Norms.L2Operator

open SpecsAux.SpecMirror
open _root_.QuantumComputation.Specs.StoppingPowerSolution (TempPhaseProg cleanRem)
open _root_.QuantumComputation.Specs.StoppingPowerSolution (cleanRem_anti ValidCleanRem)
open MomSlots35Slot3ProjNuclear
  (shellMu3 shellMu3_lt_seven shellMagCoord3 s3ShellMagCoord3_lt_128)
open StepBBlock0 (padZeroBits149_clean seqClean_spec)
open StepBBlock0 (bitsVal_eq_of_testBit)
open Prod57BoothHoist (p57MW)
open Prod57BoothHoist (sTrue18FwdPBuf275 sTrue18FwdPBuf275_spec)
open StepBOuter (muW u22WAux getU22 getU22_congr magUnpack275 magUnpack275_spec coinMuXor275
  coinMuXor275_spec)
open Slot3Exact216Oracle80 (validStatic216_275 tempPhaseProg216_seq_evalBits top7_eq_shellMu3_216)
open Slot3Outer2344AndRelayWide.Slot3Exact216TruncBr31
  (axisStep3_fast_275 axisStep3_fast_275_spec revTail216_br31_275)
open Slot3Outer2344AndRelayWide.Slot3Exact216PrunedAccAndCore
  (validStatic216_fast46_275 validStatic216_fast46_275_spec
   validStatic216_fast46_275_eq_orig magUnpack63_275 magUnpack63_275_spec
   magUnpack63_275_eq_orig)
open Slot3Outer2344AndRelayWide.Slot3MidKickWidthWide

/-! ## Section 1: Pruned Static Steps & `dAccXor50Rev77_275` / `dAccXor49PrunedRev275` Under
`clearMW` -/

/-- Pruned Step 1 (`322` `TempAnd`s = `1,288 T`). -/
def pStep1Ultra : TempPhaseProg 437 := .seq coinMuXor275 (.seq magUnpack63_275 (.seq
    validStatic216_fast46_275 (.seq axisStep3_fast_275 sTrue18FwdPBuf275)))

set_option maxRecDepth 20000 in
theorem pStep1Ultra_disjoint_isBadA :
    progDisjointBad isBadA pStep1Ultra = true ∧
    progDisjointBad isBadA revTail216_br31_275 = true := by decide

theorem pStep1Ultra_clean_spec : ValidCleanRem 437 (437 - 275) pStep1Ultra ∧
    (∀ β, cleanRem 437 (437 - 275) β → pStep1Ultra.evalSign β = 0) ∧ (∀ β, cleanRem 437 (437 -
    275) β → cleanRem 437 (437 - 275) (pStep1Ultra.evalBits β)) := by
  have s45 := seqClean_spec (by decide) axisStep3_fast_275_spec.1.1 sTrue18FwdPBuf275_spec.1
    axisStep3_fast_275_spec.1.2.1 sTrue18FwdPBuf275_spec.2.2.1
    axisStep3_fast_275_spec.1.2.2.1 (fun β hβ ↦ (sTrue18FwdPBuf275_spec.2.2.2 β hβ).1)
  have s35 := seqClean_spec (by decide) validStatic216_fast46_275_spec.1.1 s45.1
    validStatic216_fast46_275_spec.1.2.1 s45.2.2.1
    validStatic216_fast46_275_spec.1.2.2.1 s45.2.2.2.1
  have s25 := seqClean_spec (by decide) magUnpack63_275_spec.1.1 s35.1
    magUnpack63_275_spec.1.2.1 s35.2.2.1 magUnpack63_275_spec.1.2.2.1 s35.2.2.2.1
  have s15 := seqClean_spec (by decide) coinMuXor275_spec.1.1 s25.1
    coinMuXor275_spec.1.2.1 s25.2.2.1 coinMuXor275_spec.1.2.2.1 s25.2.2.2.1
  exact ⟨s15.1, s15.2.2.1, s15.2.2.2.1⟩

open Classical in
theorem pStep1Ultra_evalBits_st0 (α : BitAssignment 149) :
    pStep1Ultra.evalBits (st0 α) = st1 α := by
  obtain ⟨hB1, hE1⟩ := coinMuXor275_spec
  obtain ⟨hB2, hE2⟩ := magUnpack275_spec
  let β₀ := st0 α
  have hcl₀ : cleanRem 437 (437 - 275) β₀ :=
    cleanRem_anti (by decide) (padZeroBits149_clean α)
  have hz₀ : ∀ q : Wire 437, 149 ≤ q.val → β₀ q = 0 :=
    fun q hq ↦ padZeroBits149_clean α q (by omega)
  let β₁ := coinMuXor275.evalBits β₀
  let β₂ := magUnpack275.evalBits β₁
  have hcl₁ := hB1.2.2.1 β₀ hcl₀
  have hcl₂ := hB2.2.2.1 β₁ hcl₁
  have hp1 : ∀ q : Wire 437, q.val ≠ 198 → ¬(174 ≤ q.val ∧ q.val < 177) → β₁ q = β₀ q :=
    fun q hc hm ↦ hB1.2.2.2 β₀ hcl₀ q (fun h ↦ by
      rcases h with rfl | ⟨j, rfl⟩
      · exact hc rfl
      · exact hm ⟨by dsimp [muW]; omega, by dsimp [muW]; omega⟩)
  have hp2 : ∀ q : Wire 437, ¬(177 ≤ q.val ∧ q.val < 198) → β₂ q = β₁ q :=
    fun q hm ↦ hB2.2.2.2 β₁ hcl₁ q (fun ⟨w, b, hq⟩ ↦ by
      subst hq; exact hm ⟨by dsimp [p57MW]; omega, by dsimp [p57MW]; omega⟩)
  have hu22_1 : getU22 β₁ = getU22 β₀ :=
    getU22_congr (fun i ↦ hp1 _ (by dsimp [u22WAux]; omega) (by dsimp [u22WAux]; omega))
  have hu22_2 : getU22 β₂ = getU22 β₀ :=
    getU22_congr (fun i ↦ (hp2 _ (by dsimp [u22WAux]; omega)).trans
      (hp1 _ (by dsimp [u22WAux]; omega) (by dsimp [u22WAux]; omega)))
  have hmu₁ : ∀ j : Fin 3, β₁ (muW j) = if (shellMu3 (getU22 β₀)).testBit j.val then 1 else 0 := by
    intro j
    dsimp only [β₁]
    rw [(hE1 β₀ hcl₀).2 j, hz₀ _ (by dsimp [muW]; omega), zero_add, top7_eq_shellMu3_216 β₀]
  have hmu_val₁ : bitsVal (fun j ↦ β₁ (muW j)) = shellMu3 (getU22 β₁) := by
    rw [hu22_1]
    exact bitsVal_eq_of_testBit _ _ (lt_trans (shellMu3_lt_seven _) (by decide)) hmu₁
  have hmu_val₂ : bitsVal (fun j ↦ β₂ (muW j)) = shellMu3 (getU22 β₂) := by
    have hfn : (fun j ↦ β₂ (muW j)) = fun j ↦ β₁ (muW j) :=
      funext fun j ↦ hp2 (muW j) (by dsimp [muW]; omega)
    rw [hfn, hmu_val₁, hu22_1, hu22_2]
  have hm_val₂ : ∀ w : Fin 3, bitsVal (fun b ↦ β₂ (p57MW w b)) = shellMagCoord3 (getU22 β₂) w := by
    intro w
    rw [hu22_2]
    refine bitsVal_eq_of_testBit _ _ (s3ShellMagCoord3_lt_128 _ w) fun b ↦ ?_
    have hz : β₁ (p57MW w b) = 0 :=
      (hp1 _ (by
        dsimp [p57MW]; omega) (by dsimp [p57MW]; omega)).trans (hz₀ _ (by dsimp [p57MW]; omega))
    have he := hE2 β₁ hcl₁ hmu_val₁ w b
    dsimp only [β₂]
    rw [he, hz, zero_add]
    change (if (shellMagCoord3 (getU22 β₁) w).testBit b.val then (1 : ZMod 2) else 0) = _
    rw [hu22_1]
  dsimp only [pStep1Ultra, st1, pStep1]
  repeat rw [tempPhaseProg216_seq_evalBits]
  change sTrue18FwdPBuf275.evalBits (axisStep3_fast_275.evalBits
    (validStatic216_fast46_275.evalBits (magUnpack63_275.evalBits β₁))) =
    sTrue18FwdPBuf275.evalBits (axisStep3_fast_275.evalBits (validStatic216_275.evalBits β₂))
  rw [magUnpack63_275_eq_orig β₁ hcl₁ hmu_val₁,
    validStatic216_fast46_275_eq_orig β₂ hcl₂ hmu_val₂ hm_val₂]
end
end ConfigSlot3UltraWidthWide
end Slot3UltraWidthWide

end Slot3Outer2344AndRelayWide

end
end Slot3Outer2344AndRelayWide_p2

section Slot3MidKick36_161w
local instance (priority := 1000000) instNeZeroTwoPow_Slot3MidKick36_161w (k : ℕ) :
    NeZero (2 ^ k) := ⟨(Nat.two_pow_pos k).ne'⟩

public section

/-!
# Fixed `Bk = 36`, `161`-Wire (`4,940 T`, `0 .TOFF`) Slot-3 MidKick Engine (`M = 411`)

Implements the standalone `36`-bit (`Bk = 36`, `K_h = 34` hoisted `b1`-splits) Slot-3
`MidKick` dynamic circuit `dMidKick216_36_161w` on `QRegister 411 n` using strictly the
`161` clean scratch wires `[233..258) ∪ [275..411)` (`25 + 136 = 161`, leaving `[258..275)`
completely untouched at `0` gates) at `4,940 T/walk` (`348 + 4 + 364 + 3 * 1,408 = 4,940 T`,
`0 .TOFF`), together with its `TempPhaseProg 411` specification `progMidKick216_36_411` and
exact `trunc36Cfg` physics bridge `modWrapProjNucOp_42_trunc36Cfg`.
-/

namespace Slot3MidKick36_161w

section ConfigSlot3MidKick36_161w

set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false

local instance (priority :=
  10) instLoc_Slot3MidKick36_161w_1InstNeZeroTwoPowMk36 (k : Nat) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩

noncomputable section

open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt Real
open scoped Matrix BigOperators Matrix.Norms.L2Operator Circuit.Notation

open SpecsAux.SpecMirror
open _root_.QuantumComputation.Specs.StoppingPowerSolution
  (wire_ne_of_lt wire_ne_of_gt CliffProg TempPhaseProg cleanRem cleanRem_anti
   ValidCleanRem validCleanRem_mono CliffDisjoint TempCtx
   ctxCliffAlloc ctxCliffAlloc_disjoint ctxCliffAlloc_supports ctxTempBit)
open TwosCompAndWire0Cancel (twosComp8Int)
open PosSlots24MergedVepBound (cellLength_ne_zero)
open ModWrapCoarse8PureMomentum
  (nearestProtonCoord thetaProtonNearest quantizedStructureFactorNearest modWrapProjNucOp)
open FastMidKick275Aux Slot3Exact216Oracle80
open SubvoxelNuclearTrunc36Physics (nuclearM36 trunc36Cfg)

/-! ## Section 1: `trunc36Cfg` Physics Bridge & `64`-Aligned Coordinate Tables -/

open Classical in
/-- `36`-bit negative nuclear coordinate table `(-(nuclearM36 cfg l w)).emod (2^36)` in `ℕ`. -/
noncomputable def mk36NegCoordTable36 (cfg : SpecsAux.SpecMirror.Configuration)
    (w : Fin 3) (idx : Fin 256) : ℕ :=
  let l := 2 * (idx.val % 128) + idx.val / 128
  if hl : l < 216 then
    ((-(nuclearM36 cfg ⟨l, hl⟩ w : ℤ)).emod (2 ^ 36 : ℤ)).toNat
  else 0

open Classical in
theorem mk36NegCoordTable36_lt (cfg : SpecsAux.SpecMirror.Configuration) (w : Fin 3) (idx : Fin 256)
    :
    mk36NegCoordTable36 cfg w idx < 2 ^ 36 := by
  dsimp only [mk36NegCoordTable36]
  split_ifs with hl
  · set z := (-(nuclearM36 cfg ⟨_, hl⟩ w : ℤ)).emod (2 ^ 36 : ℤ)
    have hz0 : 0 ≤ z := Int.emod_nonneg _ (by positivity)
    have hz1 : z < (2 ^ 36 : ℤ) := Int.emod_lt_of_pos _ (by positivity)
    omega
  · positivity

theorem nearestProtonCoord_42_trunc36Cfg (c : SpecsAux.SpecMirror.Configuration) (l : Fin 216)
    (w : Fin 3) : nearestProtonCoord 42 (SpecsAux.SpecMirror.cellVolume ^ (1 / 3 : ℝ))
    ((trunc36Cfg c).nuclei l w) = 64 * (nuclearM36 c l w : ℤ) := by
  have hpow : ((1 : ℝ) / 3) = (1 / 3 : ℝ) := rfl
  have hL : SpecsAux.SpecMirror.cellVolume ^ (1 / 3 : ℝ) ≠ 0 := by
    simpa [one_div] using cellLength_ne_zero
  unfold nearestProtonCoord trunc36Cfg
  dsimp only
  rw [hpow]
  have hval : (2 : ℝ) ^ 42 * ((nuclearM36 c l w : ℝ) * (SpecsAux.SpecMirror.cellVolume ^ (1 / 3 : ℝ)
      / (2 ^ 36 : ℝ)) / SpecsAux.SpecMirror.cellVolume ^ (1 / 3 : ℝ)) + 1 / 2 =
      ((64 * (nuclearM36 c l w : ℤ) : ℤ) : ℝ) + 1 / 2 := by
    field_simp [hL]
    push_cast
    ring
  rw [hval]
  exact Int.floor_eq_iff.mpr ⟨by linarith, by linarith⟩

theorem nearestProtonCoord_36_eq_nuclearM36_add_mul (c : SpecsAux.SpecMirror.Configuration)
    (l : Fin 216) (w : Fin 3) : ∃ k : ℤ, nearestProtonCoord 36
    (SpecsAux.SpecMirror.cellVolume ^ (1 / 3 : ℝ)) (c.nuclei l w) = (nuclearM36 c l w : ℤ) +
    (2 ^ 36 : ℤ) * k := by
  let L : ℝ := SpecsAux.SpecMirror.cellVolume ^ (1 / 3 : ℝ)
  let x : ℝ := c.nuclei l w / L
  have hx_eq : c.nuclei l w / SpecsAux.SpecMirror.cellVolume ^ ((1 : ℝ) / 3) = x := rfl
  have hx_sp : x = (⌊x⌋ : ℝ) + Int.fract x := (Int.floor_add_fract x).symm
  have hfr_nn : 0 ≤ Int.fract x := Int.fract_nonneg x
  let y : ℝ := (2 ^ 36 : ℝ) * Int.fract x + 1 / 2
  have hy_nn : 0 ≤ y := by positivity
  have hy_fl : ⌊y⌋ = (⌊y⌋₊ : ℤ) :=
    Int.floor_eq_iff.mpr ⟨Nat.floor_le hy_nn, by exact_mod_cast Nat.lt_floor_add_one y⟩
  set qy : ℕ := ⌊y⌋₊ / 2 ^ 36
  have hmod : ⌊y⌋₊ = nuclearM36 c l w + 2 ^ 36 * qy := by
    have hm : nuclearM36 c l w = ⌊y⌋₊ % 2 ^ 36 := by
      unfold nuclearM36; rw [hx_eq]
    rw [hm]
    exact (Nat.mod_add_div ⌊y⌋₊ (2 ^ 36)).symm
  refine ⟨⌊x⌋ + (qy : ℤ), ?_⟩
  change ⌊(2 : ℝ) ^ 36 * x + 1 / 2⌋ = _
  have hsplit : (2 : ℝ) ^ 36 * x + 1 / 2 = y + ((2 ^ 36 * ⌊x⌋ : ℤ) : ℝ) := by
    dsimp only [y]
    conv_lhs => rw [hx_sp]
    push_cast
    ring
  rw [hsplit, Int.floor_add_intCast, hy_fl, hmod]
  push_cast
  ring

theorem exp_thetaProtonNearest_42_trunc36Cfg (c : SpecsAux.SpecMirror.Configuration) (l : Fin 216)
    (ν : Fin 3 → ℤ) : Complex.exp ((thetaProtonNearest 42 (trunc36Cfg c) l ν : ℂ) * Complex.I)
    = Complex.exp ((thetaProtonNearest 36 c l ν : ℂ) * Complex.I) := by
  choose k hk using fun w ↦ nearestProtonCoord_36_eq_nuclearM36_add_mul c l w
  have htheta : thetaProtonNearest 36 c l ν = thetaProtonNearest 42 (trunc36Cfg c) l ν +
      ((- ∑ w : Fin 3, ν w * k w : ℤ) : ℝ) * (2 * π) := by
    unfold thetaProtonNearest
    have hsum : (∑ w : Fin 3, (ν w : ℝ) * ((nearestProtonCoord 36 (SpecsAux.SpecMirror.cellVolume ^
        (1 / 3 : ℝ)) (c.nuclei l w) : ℝ) / (2 : ℝ) ^ 36)) = (∑ w : Fin 3, (ν w : ℝ) *
        ((nearestProtonCoord 42 (SpecsAux.SpecMirror.cellVolume ^ (1 / 3 : ℝ)) ((trunc36Cfg
        c).nuclei l w) : ℝ) / (2 : ℝ) ^ 42)) + ∑ w : Fin 3, (ν w : ℝ) * (k w : ℝ) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun w _ ↦ ?_
      rw [hk w, nearestProtonCoord_42_trunc36Cfg c l w]
      push_cast
      ring
    rw [hsum]
    push_cast
    ring
  rw [htheta]
  have hcast : ((thetaProtonNearest 42 (trunc36Cfg c) l ν + ((- ∑ w : Fin 3, ν w * k w : ℤ) :
      ℝ) * (2 * π) : ℝ) : ℂ) * Complex.I = (thetaProtonNearest 42 (trunc36Cfg c) l ν : ℂ) *
      Complex.I + ((- ∑ w : Fin 3, ν w * k w : ℤ) : ℂ) * (2 * ↑π * Complex.I) := by
    push_cast
    ring
  rw [hcast, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

theorem quantizedStructureFactorNearest_42_trunc36Cfg (c : SpecsAux.SpecMirror.Configuration)
    (ν : Fin 3 → ℤ) : quantizedStructureFactorNearest 42 (trunc36Cfg c) ν =
    quantizedStructureFactorNearest 36 c ν := by
  unfold quantizedStructureFactorNearest
  exact Finset.sum_congr rfl fun l _ ↦ exp_thetaProtonNearest_42_trunc36Cfg c l ν

theorem modWrapProjNucOp_42_trunc36Cfg (c : SpecsAux.SpecMirror.Configuration) (B_rad B_damp : ℕ)
    (R_3 wt_3 : ℝ) : modWrapProjNucOp (trunc36Cfg c) B_rad B_damp 42 R_3 wt_3 =
    modWrapProjNucOp c B_rad B_damp 36 R_3 wt_3 := by
  unfold modWrapProjNucOp
  ext x y
  simp only [Matrix.of_apply, quantizedStructureFactorNearest_42_trunc36Cfg]

theorem int_mul64_emod_two_pow42_toNat (z : ℤ) :
    ((64 * z).emod (2 ^ 42 : ℤ)).toNat = 64 * (z.emod (2 ^ 36 : ℤ)).toNat := by
  change ((64 * z) % (2 ^ 42 : ℤ)).toNat = 64 * (z % (2 ^ 36 : ℤ)).toNat
  have hpow : (2 ^ 42 : ℤ) = (64 : ℤ) * (2 ^ 36 : ℤ) := by norm_num
  rw [hpow, @Int.mul_emod_mul_of_pos 64 z (2 ^ 36 : ℤ) (by norm_num)]
  set r : ℤ := z % (2 ^ 36 : ℤ)
  have hr0 : 0 ≤ r := Int.emod_nonneg z (by positivity)
  apply Int.ofNat.inj
  change ((64 * r).toNat : ℤ) = ((64 * r.toNat : ℕ) : ℤ)
  rw [Int.toNat_of_nonneg (mul_nonneg (by norm_num) hr0), Nat.cast_mul, Nat.cast_ofNat,
    Int.toNat_of_nonneg hr0]

open Classical in
theorem fmkNegCoordTable_trunc36Cfg (cfg : SpecsAux.SpecMirror.Configuration)
    (w : Fin 3) (idx : Fin 256) :
    fmkNegCoordTable (trunc36Cfg cfg) w idx = 64 * mk36NegCoordTable36 cfg w idx := by
  dsimp only [fmkNegCoordTable, mk36NegCoordTable36]
  split_ifs with hl
  · rw [nearestProtonCoord_42_trunc36Cfg cfg ⟨_, hl⟩ w]
    have hneg : -(64 * (nuclearM36 cfg ⟨_, hl⟩ w : ℤ)) =
        64 * (-(nuclearM36 cfg ⟨_, hl⟩ w : ℤ)) := by ring
    rw [hneg]
    exact int_mul64_emod_two_pow42_toNat _
  · rfl

/-! ## Section 2: `M = 411` Wire Layout, `mk36Swap411` (`[233..250) ↔ [258..275)`), & `bitsVal`
Helpers -/

def mk36POldW (w : Fin 3) (b : Fin 8) : Wire 411 := ⟨8 * w.val + b.val, by omega⟩
def mk36BParW : Wire 411 := ⟨90, by decide⟩
def mk36U16W (i : Fin 16) : Wire 411 := ⟨91 + i.val, by omega⟩
def mk36Cat42W (j : Fin 42) : Wire 411 := ⟨107 + j.val, by omega⟩
def mk36Cat36W (j : Fin 36) : Wire 411 := ⟨113 + j.val, by omega⟩

theorem mk36Cat36W_eq_cat42 (j : Fin 36) :
    mk36Cat36W j = mk36Cat42W ⟨6 + j.val, by omega⟩ :=
  Fin.ext (by dsimp [mk36Cat36W, mk36Cat42W]; omega)

def mk36AccW : Wire 411 := ⟨149, by decide⟩
def mk36PNewW (w : Fin 3) (b : Fin 8) : Wire 411 := ⟨150 + 8 * w.val + b.val, by omega⟩

theorem mk36PNew_ne_pOld (w : Fin 3) (b : Fin 8) : mk36PNewW w b ≠ mk36POldW w b :=
  wire_ne_of_gt (by dsimp [mk36PNewW, mk36POldW]; omega)

theorem mk36PNew_lt339 (w : Fin 3) (b : Fin 8) : (mk36PNewW w b).val < 339 := by
  dsimp [mk36PNewW]; omega

def mk36FlipP (w : Fin 3) : CliffProg 411 :=
  .seq (.x (mk36PNewW w ⟨7, by decide⟩)) (fmkXVec 7 (fun j : Fin 7 ↦ mk36POldW w j.castSucc))

theorem mk36FlipP_supportsBelow (w : Fin 3) : (mk36FlipP w).SupportsBelow 174 := by
  have hw := w.isLt
  exact ⟨by dsimp [CliffProg.SupportsBelow, mk36PNewW]; omega,
    fmkXVec_supportsBelow 7 _ fun j ↦ by have := j.isLt; dsimp [mk36POldW]; omega⟩

def mk36Walk10W_338 : Wire 411 := ⟨338, by decide⟩
def mk36Bank36W (j : Fin 36) : Wire 411 := ⟨339 + j.val, by omega⟩

theorem mk36Bank36W_inj : Function.Injective mk36Bank36W := fun a b h ↦ by
  have hv := congrArg Fin.val h
  dsimp [mk36Bank36W] at hv
  exact Fin.ext (by omega)

/-- Clean-scratch predicate on `QRegister 411 n`: the `161` wires `[233..258) ∪ [275..411)` are `0`,
leaving `[258..275)` (`17` wires) unconstrained. -/
def mk36Clean161 (γ : BitAssignment 411) : Prop :=
  ∀ w : Wire 411, ((233 ≤ w.val ∧ w.val < 258) ∨ 275 ≤ w.val) → γ w = 0

/-- Involutive wire permutation on `Fin 411` swapping `[233..250)` (`17` wires) with `[258..275)`
(`17` wires), mapping `mk36Clean161` onto the contiguous `161`-wire tail `[250..411)`. -/
def mk36Swap411 (i : Wire 411) : Wire 411 :=
  if _ : 233 ≤ i.val ∧ i.val < 250 then ⟨i.val + 25, by omega⟩
  else if _ : 258 ≤ i.val ∧ i.val < 275 then ⟨i.val - 25, by omega⟩
  else i

open Classical in
theorem mk36Swap411_val (i : Wire 411) : (mk36Swap411 i).val = if 233 ≤ i.val ∧ i.val < 250
    then i.val + 25 else if 258 ≤ i.val ∧ i.val < 275 then i.val - 25 else i.val := by
  unfold mk36Swap411
  split_ifs <;> rfl

open Classical in
theorem mk36Swap411_invol (i : Wire 411) : mk36Swap411 (mk36Swap411 i) = i := by
  apply Fin.ext
  have hi := i.isLt
  rw [mk36Swap411_val, mk36Swap411_val]
  split_ifs <;> omega

theorem mk36Swap411_inj : Function.Injective mk36Swap411 :=
  Function.LeftInverse.injective mk36Swap411_invol

open Classical in
theorem mk36Swap411_of_lt233 (i : Wire 411) (h : i.val < 233) : mk36Swap411 i = i := by
  apply Fin.ext
  rw [mk36Swap411_val]
  split_ifs <;> omega

open Classical in
theorem mk36Swap411_ge233 (i : Wire 411) (h : 233 ≤ i.val) : 233 ≤ (mk36Swap411 i).val := by
  rw [mk36Swap411_val]
  split_ifs <;> omega

open Classical in
theorem mk36CleanRem161_of_clean161 {γ : BitAssignment 411} (h : mk36Clean161 γ) :
    cleanRem 411 161 (γ ∘ mk36Swap411) := fun w hw ↦ by
  apply h (mk36Swap411 w)
  have hw2 := w.isLt
  rw [mk36Swap411_val]
  split_ifs <;> omega

def mk36PermReg411 : QRegister 411 411 where
  wires := ⟨mk36Swap411, mk36Swap411_inj⟩

theorem mk36Update_comp_swap (δ : BitAssignment 411) (t : Wire 411) (v : ZMod 2) :
    (Function.update δ (mk36Swap411 t) v) ∘ mk36Swap411 =
      Function.update (δ ∘ mk36Swap411) t v := by
  funext q
  dsimp only [Function.comp_apply]
  by_cases hqt : q = t
  · subst hqt; simp [Function.update_self]
  · simp [Function.update_of_ne hqt, Function.update_of_ne (mk36Swap411_inj.ne hqt)]

theorem mk36Update_swap_apply (f : BitAssignment 411) (t : Wire 411) (v : ZMod 2) :
    Function.update (fun q ↦ f (mk36Swap411 q)) (mk36Swap411 t) v =
      fun q ↦ Function.update f t v (mk36Swap411 q) := by
  funext q
  by_cases hq : q = mk36Swap411 t
  · subst hq; rw [mk36Swap411_invol]; simp [Function.update_self]
  · have hne : mk36Swap411 q ≠ t := fun h ↦ hq (by rw [← h, mk36Swap411_invol])
    simp [Function.update_of_ne hq, Function.update_of_ne hne]

theorem mk36Cliff_onPerm_eval :
    ∀ (c : CliffProg 411) (γ : BitAssignment 411),
      (c.onRegister mk36PermReg411).eval γ = fun q ↦ c.eval (γ ∘ mk36Swap411) (mk36Swap411 q)
  | .nil, γ => funext fun q ↦ (congrArg γ (mk36Swap411_invol q)).symm
  | .x t, γ => by
      dsimp only [CliffProg.onRegister, CliffProg.eval, mk36PermReg411, Function.Embedding.coeFn_mk]
      have hγ : γ = fun q ↦ (γ ∘ mk36Swap411) (mk36Swap411 q) :=
        funext fun q ↦ (congrArg γ (mk36Swap411_invol q)).symm
      conv_lhs => arg 1; rw [hγ]
      exact mk36Update_swap_apply (γ ∘ mk36Swap411) t _
  | .cnot c t _, γ => by
      dsimp only [CliffProg.onRegister, CliffProg.eval, mk36PermReg411, Function.Embedding.coeFn_mk]
      have hγ : γ = fun q ↦ (γ ∘ mk36Swap411) (mk36Swap411 q) :=
        funext fun q ↦ (congrArg γ (mk36Swap411_invol q)).symm
      conv_lhs => arg 1; rw [hγ]
      exact mk36Update_swap_apply (γ ∘ mk36Swap411) t _
  | .seq c₁ c₂, γ => by
      dsimp only [CliffProg.onRegister, CliffProg.eval]
      rw [mk36Cliff_onPerm_eval c₂, mk36Cliff_onPerm_eval c₁]
      have hcomp : ((fun q ↦ c₁.eval (γ ∘ mk36Swap411) (mk36Swap411 q)) ∘ mk36Swap411) =
          c₁.eval (γ ∘ mk36Swap411) := funext fun q ↦ by
        dsimp only [Function.comp_apply]; rw [mk36Swap411_invol]
      rw [hcomp]

theorem mk36Prog_onPerm_eval :
    ∀ (p : TempPhaseProg 411) (γ : BitAssignment 411),
      (p.onRegister mk36PermReg411).evalSign γ = p.evalSign (γ ∘ mk36Swap411) ∧
      (p.onRegister mk36PermReg411).evalBits γ =
        fun q ↦ p.evalBits (γ ∘ mk36Swap411) (mk36Swap411 q)
  | .nil, γ => ⟨rfl, funext fun q ↦ (congrArg γ (mk36Swap411_invol q)).symm⟩
  | .cliff c, γ => ⟨rfl, mk36Cliff_onPerm_eval c γ⟩
  | .z _, γ => ⟨rfl, funext fun q ↦ (congrArg γ (mk36Swap411_invol q)).symm⟩
  | .seq p₁ p₂, γ => by
      obtain ⟨hs₁, hb₁⟩ := mk36Prog_onPerm_eval p₁ γ
      obtain ⟨hs₂, hb₂⟩ := mk36Prog_onPerm_eval p₂ ((p₁.onRegister mk36PermReg411).evalBits γ)
      have hcomp : (((p₁.onRegister mk36PermReg411).evalBits γ) ∘ mk36Swap411) =
          p₁.evalBits (γ ∘ mk36Swap411) := funext fun q ↦ by
        rw [hb₁]; dsimp only [Function.comp_apply]; rw [mk36Swap411_invol]
      refine ⟨?_, ?_⟩
      · dsimp only [TempPhaseProg.onRegister, TempPhaseProg.evalSign]
        rw [hs₁, hs₂, hcomp]
      · dsimp only [TempPhaseProg.onRegister, TempPhaseProg.evalBits]
        rw [hb₂, hcomp]
  | .tempAnd c₁ c₂ anc h₁₂ h₁a h₂a body, γ => by
      let γ₁ := Function.update γ (mk36Swap411 anc)
        (γ (mk36Swap411 anc) + γ (mk36Swap411 c₁) * γ (mk36Swap411 c₂))
      obtain ⟨hsB, hbB⟩ := mk36Prog_onPerm_eval body γ₁
      have hcomp₁ : (γ₁ ∘ mk36Swap411) = Function.update (γ ∘ mk36Swap411) anc ((γ ∘
          mk36Swap411) anc + (γ ∘ mk36Swap411) c₁ * (γ ∘ mk36Swap411) c₂) :=
          mk36Update_comp_swap γ anc _
      refine ⟨?_, ?_⟩
      · dsimp only [TempPhaseProg.onRegister, TempPhaseProg.evalSign, mk36PermReg411]
        exact hsB.trans (congrArg body.evalSign hcomp₁)
      · dsimp only [TempPhaseProg.onRegister, TempPhaseProg.evalBits, mk36PermReg411,
          Function.Embedding.coeFn_mk]
        change Function.update ((body.onRegister mk36PermReg411).evalBits γ₁) (mk36Swap411 anc)
          (((body.onRegister mk36PermReg411).evalBits γ₁) (mk36Swap411 anc) +
            ((body.onRegister mk36PermReg411).evalBits γ₁) (mk36Swap411 c₁) *
              ((body.onRegister mk36PermReg411).evalBits γ₁) (mk36Swap411 c₂)) = _
        rw [hbB, hcomp₁]
        dsimp only
        rw [mk36Swap411_invol anc, mk36Swap411_invol c₁, mk36Swap411_invol c₂]
        exact mk36Update_swap_apply _ anc _

theorem mk36BitsVal_inj :
    ∀ {W : ℕ} {f g : Fin W → ZMod 2}, bitsVal f = bitsVal g → f = g
  | 0, f, g, _ => funext fun i ↦ i.elim0
  | W + 1, f, g, h => by
      rw [fmkBitsVal_succ_split f, fmkBitsVal_succ_split g] at h
      have hf0 := ZMod.val_lt (f 0)
      have hg0 := ZMod.val_lt (g 0)
      have h0 : (f 0).val = (g 0).val := by omega
      have htail : bitsVal (fun j ↦ f j.succ) = bitsVal (fun j ↦ g j.succ) := by omega
      have hrec := mk36BitsVal_inj htail
      funext i
      cases i using Fin.cases with
      | zero => exact ZMod.val_injective 2 h0
      | succ j => exact congrFun hrec j

theorem mk36BitsVal_42_of_36_mod {f g : Fin 42 → ZMod 2} {d : ℤ}
    (hlo : ∀ i : Fin 42, i.val < 6 → g i = f i)
    (hhi : ((bitsVal (fun j : Fin 36 ↦ g ⟨6 + j.val, by omega⟩) : ℤ)).emod (2 ^ 36 : ℤ) =
      ((bitsVal (fun j : Fin 36 ↦ f ⟨6 + j.val, by omega⟩) : ℤ) + d).emod (2 ^ 36 : ℤ)) :
    ((bitsVal g : ℤ)).emod (2 ^ 42 : ℤ) = ((bitsVal f : ℤ) + 64 * d).emod (2 ^ 42 : ℤ) := by
  have hlin := fmkBitsVal_slice_linear (N := 42) (W := 36) (k := 6) rfl f g hlo
  set G42 := bitsVal g
  set F42 := bitsVal f
  set G36 := bitsVal (fun j : Fin 36 ↦ g ⟨6 + j.val, by omega⟩)
  set F36 := bitsVal (fun j : Fin 36 ↦ f ⟨6 + j.val, by omega⟩)
  have h2_6 : (2 : ℕ) ^ 6 = 64 := rfl
  rw [h2_6] at hlin
  have hlinZ : (G42 : ℤ) - (F42 : ℤ) = 64 * ((G36 : ℤ) - (F36 : ℤ)) := by omega
  have hdiv1 := Int.emod_add_mul_ediv (G36 : ℤ) (2 ^ 36 : ℤ)
  have hdiv2 := Int.emod_add_mul_ediv ((F36 : ℤ) + d) (2 ^ 36 : ℤ)
  change (G36 : ℤ) % (2 ^ 36 : ℤ) = ((F36 : ℤ) + d) % (2 ^ 36 : ℤ) at hhi
  change (G36 : ℤ) % (2 ^ 36 : ℤ) + (2 ^ 36 : ℤ) * ((G36 : ℤ) / (2 ^ 36 : ℤ)) = (G36 : ℤ) at hdiv1
  change ((F36 : ℤ) + d) % (2 ^ 36 : ℤ) + (2 ^ 36 : ℤ) * (((F36 : ℤ) + d) / (2 ^ 36 : ℤ)) =
    (F36 : ℤ) + d at hdiv2
  set q := ((F36 : ℤ) + d) / (2 ^ 36 : ℤ) - (G36 : ℤ) / (2 ^ 36 : ℤ)
  have hrel : (G42 : ℤ) = ((F42 : ℤ) + 64 * d) + (-q) * (2 ^ 42 : ℤ) := by
    dsimp [q]; omega
  rw [hrel]
  exact Int.add_mul_emod_self_right _ _ _

private theorem mk36_cliffDisjoint_fanout {mutW : Wire 411 → Prop} (u : Wire 411) :
    ∀ (n : ℕ) (dst : Fin n → Wire 411) (hne : ∀ j, u ≠ dst j),
      ¬ mutW u → (∀ j, ¬ mutW (dst j)) → CliffDisjoint mutW (fmkFanoutCnot n u dst hne)
  | 0, _, _, _, _ => trivial
  | _ + 1, _, _, hc, hd =>
      ⟨⟨hc, hd 0⟩, mk36_cliffDisjoint_fanout u _ _ _ hc (fun j ↦ hd j.succ)⟩

open Classical in
private theorem mk36_plug_mutBlock {mutW : Wire 411 → Prop} {cur next : ℕ}
    (hrem : 411 - next ≤ 411 - cur)
    (hnm : ∀ w : Wire 411, 411 - (411 - cur) ≤ w.val → ¬ mutW w)
    (K : TempCtx 411) (hdK : K.DisjointFrom mutW) (hsK : K.SupportsBelowCtx next)
    (hlK : fmkTempCtxLiftEx cur next K) (body : TempPhaseProg 411)
    (hvB : ValidCleanRem 411 (411 - next) body)
    (hsB : ∀ δ, cleanRem 411 (411 - next) δ → body.evalSign δ = 0)
    (hnonB : ∀ δ, cleanRem 411 (411 - next) δ → ∀ w, ¬ mutW w → body.evalBits δ w = δ w) :
    (K.plug body).countTempAnd = K.countTempAnd + body.countTempAnd ∧
      fmkIsMutBlock 411 (411 - cur) mutW (K.plug body) ∧
      (∀ γ, cleanRem 411 (411 - cur) γ → cleanRem 411 (411 - next) (K.fwdBits γ)) ∧
      (∀ γ, cleanRem 411 (411 - cur) γ → ∀ w, mutW w →
        (K.plug body).evalBits γ w = body.evalBits (K.fwdBits γ) w) := by
  obtain ⟨hv, hc, hs, hb⟩ := fmkGraft_mutating_clean (M := 411) (rem := 411 - cur)
    (curHole := next) mutW K hdK hsK hrem K.fwdBits (fmkTempCtxLiftEx_probe hlK)
    body hvB hnonB
  have hcl : ∀ γ, cleanRem 411 (411 - cur) γ → cleanRem 411 (411 - next) (K.fwdBits γ) :=
    fun γ hγ ↦ fmkSupportsBelowCtx_cleanRem hsK γ (cleanRem_anti hrem hγ)
  have hnon : ∀ γ, cleanRem 411 (411 - cur) γ → ∀ w, ¬ mutW w →
      (K.plug body).evalBits γ w = γ w :=
    fun γ hγ w hw ↦ (hb γ hγ w).trans (fmkIteNeg hw _ _)
  refine ⟨hc, ⟨hv, fun γ hγ ↦ (hs γ hγ).trans (hsB _ (hcl γ hγ)),
    fun γ hγ w hw ↦ (hnon γ hγ w (hnm w hw)).trans (hγ w hw), hnon⟩, hcl,
    fun γ hγ w hw ↦ (hb γ hγ w).trans (fmkItePos hw _ _)⟩

/-! ## Section 3: `36`-Bit `mk36Add36Bank` (`35` `TempAnd`s) & `mk36MulAxis36_no2a` (`296`
`TempAnd`s) -/

/-- In-place `36`-bit modular addition `cat36 += bank36 (mod 2^36)` (`35` `TempAnd`s, clean
  `[375..410)`). -/
def mk36Add36Bank : TempPhaseProg 411 :=
  let c1W : Wire 411 := ⟨375, by decide⟩
  let bTail : Fin 35 → Wire 411 := fun j ↦ mk36Bank36W j.succ
  let aTail : Fin 35 → Wire 411 := fun j ↦ mk36Cat36W j.succ
  let K0 : TempCtx 411 :=
    ctxTempBit (mk36Bank36W 0) (mk36Cat36W 0) c1W
      (wire_ne_of_gt (by dsimp [mk36Bank36W, mk36Cat36W]; omega))
      (wire_ne_of_lt (by dsimp [mk36Bank36W, c1W]; omega))
      (wire_ne_of_lt (by dsimp [mk36Cat36W, c1W]; omega))
  let addTail : TempPhaseProg 411 :=
    fmkInPlaceAddModCarry 34 376 (by decide) bTail aTail c1W
      (fun j ↦ wire_ne_of_lt (by
        simp only [bTail, aTail, mk36Bank36W, mk36Cat36W, Fin.val_succ]; omega))
      (fun j ↦ wire_ne_of_lt (by simp only [aTail, mk36Cat36W, c1W, Fin.val_succ]; omega))
      (fun j ↦ wire_ne_of_lt (by simp only [bTail, mk36Bank36W, c1W, Fin.val_succ]; omega))
      (fun j ↦ by simp only [bTail, mk36Bank36W, Fin.val_succ]; omega)
      (fun j ↦ by simp only [aTail, mk36Cat36W, Fin.val_succ]; omega)
      (by decide)
  .seq (K0.plug addTail)
    (.cliff (.cnot (mk36Bank36W 0) (mk36Cat36W 0)
      (wire_ne_of_gt (by dsimp [mk36Bank36W, mk36Cat36W]; omega))))

theorem mk36Add36Bank_spec : mk36Add36Bank.countTempAnd = 35 ∧ fmkIsMutBlock 411 (411 - 375)
    (fun w ↦ 107 ≤ w.val ∧ w.val < 149) mk36Add36Bank ∧ (∀ γ : BitAssignment 411, cleanRem 411
    (411 - 375) γ → ((bitsVal (fun m ↦ mk36Add36Bank.evalBits γ (mk36Cat42W m)) : ℤ)).emod (2
    ^ 42 : ℤ) = ((bitsVal (fun m ↦ γ (mk36Cat42W m)) : ℤ) + ((64 * bitsVal (fun m : Fin 36 ↦ γ
    (mk36Bank36W m)) : ℕ) : ℤ)).emod (2 ^ 42 : ℤ)) := by
  let mutCat : Wire 411 → Prop := fun w ↦ 107 ≤ w.val ∧ w.val < 149
  let mutCat36 : Wire 411 → Prop := fun w ↦ 113 ≤ w.val ∧ w.val < 149
  let mutTail : Wire 411 → Prop := fun w ↦ 114 ≤ w.val ∧ w.val < 149
  let c1W : Wire 411 := ⟨375, by decide⟩
  let bTail : Fin 35 → Wire 411 := fun j ↦ mk36Bank36W j.succ
  let aTail : Fin 35 → Wire 411 := fun j ↦ mk36Cat36W j.succ
  let K0 : TempCtx 411 :=
    ctxTempBit (mk36Bank36W 0) (mk36Cat36W 0) c1W
      (wire_ne_of_gt (by dsimp [mk36Bank36W, mk36Cat36W]; omega))
      (wire_ne_of_lt (by dsimp [mk36Bank36W, c1W]; omega))
      (wire_ne_of_lt (by dsimp [mk36Cat36W, c1W]; omega))
  let addTail : TempPhaseProg 411 :=
    fmkInPlaceAddModCarry 34 376 (by decide) bTail aTail c1W
      (fun j ↦ wire_ne_of_lt (by
        simp only [bTail, aTail, mk36Bank36W, mk36Cat36W, Fin.val_succ]; omega))
      (fun j ↦ wire_ne_of_lt (by simp only [aTail, mk36Cat36W, c1W, Fin.val_succ]; omega))
      (fun j ↦ wire_ne_of_lt (by simp only [bTail, mk36Bank36W, c1W, Fin.val_succ]; omega))
      (fun j ↦ by simp only [bTail, mk36Bank36W, Fin.val_succ]; omega)
      (fun j ↦ by simp only [aTail, mk36Cat36W, Fin.val_succ]; omega) (by decide)
  have hb_inj : Function.Injective bTail := fun i j h ↦ by
    have hv := congrArg Fin.val h; simp only [bTail, mk36Bank36W, Fin.val_succ] at hv;
      exact Fin.ext (by omega)
  have ha_inj : Function.Injective aTail := fun i j h ↦ by
    have hv := congrArg Fin.val h; simp only [aTail, mk36Cat36W, Fin.val_succ] at hv;
      exact Fin.ext (by omega)
  obtain ⟨hvAdd, hsAdd, hAdd⟩ := fmkInPlaceAddModCarry_spec 34 376 (by decide) bTail aTail c1W
    (fun i j ↦ wire_ne_of_lt (by
      simp only [bTail, aTail, mk36Bank36W, mk36Cat36W, Fin.val_succ]; omega))
    (fun j ↦ wire_ne_of_lt (by simp only [aTail, mk36Cat36W, c1W, Fin.val_succ]; omega))
    (fun j ↦ wire_ne_of_lt (by simp only [bTail, mk36Bank36W, c1W, Fin.val_succ]; omega))
    hb_inj ha_inj
    (fun j ↦ by simp only [bTail, mk36Bank36W, Fin.val_succ]; omega)
    (fun j ↦ by simp only [aTail, mk36Cat36W, Fin.val_succ]; omega) (by decide)
  have hdK0 : K0.DisjointFrom mutTail :=
    ⟨by dsimp [mutTail, mk36Bank36W]; omega, by dsimp [mutTail, mk36Cat36W]; omega,
      by dsimp [mutTail, c1W]; omega, trivial⟩
  have hsK0 : K0.SupportsBelowCtx 376 := ⟨by dsimp [c1W]; omega, trivial⟩
  have hlK0 : fmkTempCtxLiftEx 375 376 K0 :=
    fmkTempCtxLiftEx_tempBit (cur := 375) (by decide) (mk36Bank36W 0) (mk36Cat36W 0)
      _ (by dsimp [mk36Bank36W]; omega) (by dsimp [mk36Cat36W]; omega)
  have hAddNon : ∀ δ, cleanRem 411 (411 - 376) δ → ∀ w, ¬ mutTail w → addTail.evalBits δ w = δ w :=
    fun δ hδ w hw ↦ (hAdd δ hδ).2.1 w fun j hj ↦
      hw (by rw [hj]; simp only [mutTail, aTail, mk36Cat36W, Fin.val_succ]; omega)
  obtain ⟨hcP, hMutT, hK0_cl, hbP_pos⟩ := mk36_plug_mutBlock (by decide)
    (fun _ hw ht ↦ by dsimp [mutTail] at ht; omega) K0 hdK0 hsK0 hlK0 addTail hvAdd hsAdd hAddNon
  have hMut1 : fmkIsMutBlock 411 (411 - 375) mutCat36 (K0.plug addTail) :=
    ⟨hMutT.1, hMutT.2.1, hMutT.2.2.1,
      fun γ hγ w hw ↦ hMutT.2.2.2 γ hγ w (fun ht ↦ hw ⟨by omega, ht.2⟩)⟩
  let cLsb : CliffProg 411 := .cnot (mk36Bank36W 0) (mk36Cat36W 0)
    (wire_ne_of_gt (by dsimp [mk36Bank36W, mk36Cat36W]; omega))
  have hMut2 : fmkIsMutBlock 411 (411 - 375) mutCat36 (.cliff cLsb) := by
    refine ⟨trivial, fun _ _ ↦ rfl, fun γ hγ w hw ↦ ?_, fun γ _ w hw ↦ ?_⟩
    · dsimp [TempPhaseProg.evalBits, cLsb, CliffProg.eval]
      rw [Function.update_of_ne (wire_ne_of_gt (by dsimp [mk36Cat36W]; omega))]
      exact hγ w hw
    · dsimp [TempPhaseProg.evalBits, cLsb, CliffProg.eval]
      exact Function.update_of_ne (fun h ↦ hw (by rw [h]; dsimp [mutCat36, mk36Cat36W]; omega)) _ _
  have hMut36 := fmkIsMutBlock_seq (by decide) hMut1 hMut2
  have hMut42 : fmkIsMutBlock 411 (411 - 375) mutCat mk36Add36Bank :=
    ⟨hMut36.1, hMut36.2.1, hMut36.2.2.1,
      fun γ hγ w hw ↦ hMut36.2.2.2 γ hγ w (fun h ↦ hw ⟨by omega, h.2⟩)⟩
  have hCnt35 : mk36Add36Bank.countTempAnd = 35 := by
    change (K0.plug addTail).countTempAnd + 0 = 35
    rw [Nat.add_zero, hcP]
    change 1 + addTail.countTempAnd = 35
    dsimp only [addTail]
    rw [fmkInPlaceAddModCarry_countTempAnd]
  refine ⟨hCnt35, hMut42, fun γ hγ ↦ ?_⟩
  let δ := K0.fwdBits γ
  have hδ_eq : δ = Function.update γ c1W (γ (mk36Bank36W 0) * γ (mk36Cat36W 0)) := by
    dsimp only [δ, K0, ctxTempBit, TempCtx.fwdBits]
    rw [hγ c1W (by decide), zero_add]
  have hδ_cl : cleanRem 411 (411 - 376) δ := hK0_cl γ hγ
  let γ1 := (K0.plug addTail).evalBits γ
  have hγ1_0 : γ1 (mk36Cat36W 0) = γ (mk36Cat36W 0) :=
    hMutT.2.2.2 γ hγ _ (by dsimp [mutTail, mk36Cat36W]; omega)
  have hγ1_b0 : γ1 (mk36Bank36W 0) = γ (mk36Bank36W 0) :=
    hMutT.2.2.2 γ hγ _ (by dsimp [mutTail, mk36Bank36W]; omega)
  have hγ1_tail : ∀ j : Fin 35, γ1 (aTail j) = addTail.evalBits δ (aTail j) := fun j ↦
    hbP_pos γ hγ (aTail j) (by simp only [mutTail, aTail, mk36Cat36W, Fin.val_succ]; omega)
  have hout0 : mk36Add36Bank.evalBits γ (mk36Cat36W 0) = γ (mk36Cat36W 0) + γ (mk36Bank36W 0) := by
    change Function.update γ1 (mk36Cat36W 0) (γ1 (mk36Cat36W 0) +
      γ1 (mk36Bank36W 0)) (mk36Cat36W 0) = _
    rw [Function.update_self, hγ1_0, hγ1_b0]
  have hout_tail : (fun j : Fin 35 ↦ mk36Add36Bank.evalBits γ (mk36Cat36W j.succ)) =
      fun j : Fin 35 ↦ addTail.evalBits δ (aTail j) := funext fun j ↦ by
    change Function.update γ1 (mk36Cat36W 0) (γ1 (mk36Cat36W 0) +
      γ1 (mk36Bank36W 0)) (mk36Cat36W j.succ) = _
    rw [Function.update_of_ne (wire_ne_of_gt (by simp only [mk36Cat36W, Fin.val_succ]; omega))]
    exact hγ1_tail j
  have hTailVal := (hAdd δ hδ_cl).2.2
  have hδ_a : (fun j : Fin 35 ↦ δ (aTail j)) = fun j ↦ γ (mk36Cat36W j.succ) := funext fun j ↦ by
    rw [hδ_eq, Function.update_of_ne (wire_ne_of_lt (by
      simp only [aTail, mk36Cat36W, c1W, Fin.val_succ]; omega))]
  have hδ_b : (fun j : Fin 35 ↦ δ (bTail j)) = fun j ↦ γ (mk36Bank36W j.succ) := funext fun j ↦ by
    rw [hδ_eq, Function.update_of_ne (wire_ne_of_lt (by
      simp only [bTail, mk36Bank36W, c1W, Fin.val_succ]; omega))]
  have hδ_c1 : δ c1W = γ (mk36Bank36W 0) * γ (mk36Cat36W 0) := by
    rw [hδ_eq, Function.update_self]
  rw [hδ_a, hδ_b, hδ_c1] at hTailVal
  have h36_mod : ((bitsVal (fun m : Fin 36 ↦ mk36Add36Bank.evalBits γ (mk36Cat36W m)) :
      ℤ)).emod (2 ^ 36 : ℤ) = ((bitsVal (fun m : Fin 36 ↦ γ (mk36Cat36W m)) : ℤ) + (bitsVal
      (fun m : Fin 36 ↦ γ (mk36Bank36W m)) : ℤ)).emod (2 ^ 36 : ℤ) := by
    rw[fmkBitsVal_succ_split (fun m ↦ mk36Add36Bank.evalBits γ (mk36Cat36W m)), hout0,
        hout_tail, hTailVal, fmkBitsVal_succ_split (fun m ↦ γ (mk36Cat36W m)),
        fmkBitsVal_succ_split (fun m ↦ γ (mk36Bank36W m))]
    have hha := fmkHalfAdd_val_eq (γ (mk36Cat36W 0)) (γ (mk36Bank36W 0))
    rw [mul_comm (γ (mk36Bank36W 0)) (γ (mk36Cat36W 0)),
      show 2 ^ (34 + 1) = 2 ^ 35 from rfl]
    set cT := bitsVal (fun j : Fin 35 ↦ γ (mk36Cat36W j.succ))
    set bT := bitsVal (fun j : Fin 35 ↦ γ (mk36Bank36W j.succ))
    set s0 := (γ (mk36Cat36W 0) + γ (mk36Bank36W 0)).val
    set p0 := (γ (mk36Cat36W 0) * γ (mk36Bank36W 0)).val
    set c0 := (γ (mk36Cat36W 0)).val
    set b0 := (γ (mk36Bank36W 0)).val
    set q := (cT + bT + p0) / 2 ^ 35
    set r := (cT + bT + p0) % 2 ^ 35
    have hdiv : 2 ^ 35 * q + r = cT + bT + p0 := Nat.div_add_mod (cT + bT + p0) (2 ^ 35)
    have hnat : (s0 + 2 * r) + 2 ^ 36 * q = (c0 + 2 * cT) + (b0 + 2 * bT) := by
      omega
    have hint : ((s0 + 2 * r : ℕ) : ℤ) =
        (((c0 + 2 * cT : ℕ) : ℤ) + ((b0 + 2 * bT : ℕ) : ℤ)) + (-(q : ℤ)) * (2 ^ 36 : ℤ) := by
      push_cast; zify at hnat; linarith
    change ((s0 + 2 * r : ℕ) : ℤ).emod (2 ^ 36 : ℤ) =
      (((c0 + 2 * cT : ℕ) : ℤ) + ((b0 + 2 * bT : ℕ) : ℤ)).emod (2 ^ 36 : ℤ)
    rw [hint]
    exact Int.add_mul_emod_self_right _ _ _
  have hlo6 : ∀ i : Fin 42,
    i.val < 6 → mk36Add36Bank.evalBits γ (mk36Cat42W i) = γ (mk36Cat42W i) :=
    fun i hi ↦ hMut36.2.2.2 γ hγ (mk36Cat42W i) (by dsimp [mutCat36, mk36Cat42W]; omega)
  have hcat_hi : ∀ δ : BitAssignment 411,
      (fun j : Fin 36 ↦ δ (mk36Cat42W ⟨6 + j.val, by omega⟩)) = fun j : Fin 36 ↦ δ (mk36Cat36W j) :=
    fun δ ↦ funext fun j ↦ congrArg δ (mk36Cat36W_eq_cat42 j).symm
  push_cast
  exact mk36BitsVal_42_of_36_mod hlo6 (by rw [hcat_hi, hcat_hi]; exact h36_mod)

attribute [local irreducible] mk36Add36Bank

def mk36H36NoDummy (u0 : Wire 411) : Fin 36 → Wire 411 :=
  Fin.snoc (fun j : Fin 35 ↦ mk36Bank36W j.succ) u0

theorem mk36H36NoDummy_inj (u0 : Wire 411) (hu0 : u0.val < 339) :
    Function.Injective (mk36H36NoDummy u0) := by
  intro a b
  refine Fin.lastCases ?_ (fun i ↦ ?_) a <;> refine Fin.lastCases ?_ (fun j ↦ ?_) b <;> intro h
  · rfl
  · simp only [mk36H36NoDummy, Fin.snoc_last, Fin.snoc_castSucc] at h
    have hv := congrArg Fin.val h; dsimp only [mk36Bank36W, Fin.val_succ] at hv; omega
  · simp only [mk36H36NoDummy, Fin.snoc_last, Fin.snoc_castSucc] at h
    have hv := congrArg Fin.val h; dsimp only [mk36Bank36W, Fin.val_succ] at hv; omega
  · simp only [mk36H36NoDummy, Fin.snoc_castSucc] at h
    have hv := congrArg Fin.val h; dsimp only [mk36Bank36W, Fin.val_succ] at hv
    exact congrArg Fin.castSucc (Fin.ext (by omega))

theorem mk36H36NoDummy_lt375 (u0 : Wire 411) (hu0 : u0.val < 339) (j : Fin 36) :
    (mk36H36NoDummy u0 j).val < 375 := by
  refine Fin.lastCases ?_ (fun i ↦ ?_) j
  · simp only [mk36H36NoDummy, Fin.snoc_last]; omega
  · simp only [mk36H36NoDummy, Fin.snoc_castSucc, mk36Bank36W, Fin.val_succ]; omega

theorem mk36H36NoDummy_not_cat36 (u0 : Wire 411) (hu_nc : ¬(113 ≤ u0.val ∧ u0.val < 149))
    (j : Fin 36) : ¬(113 ≤ (mk36H36NoDummy u0 j).val ∧ (mk36H36NoDummy u0 j).val < 149) := by
  refine Fin.lastCases ?_ (fun i ↦ ?_) j
  · simp only [mk36H36NoDummy, Fin.snoc_last]; exact hu_nc
  · simp only [mk36H36NoDummy, Fin.snoc_castSucc, mk36Bank36W, Fin.val_succ]; omega

/-- No-`2a` LSB step on `cat36` (`36` `TempAnd`s, clean `[375..411)`). -/
def mk36Step2b36_nodummy (u0 : Wire 411)
    (hu0 : ¬(113 ≤ u0.val ∧ u0.val < 149) ∧ u0.val < 339) : TempPhaseProg 411 :=
  let cin0W : Wire 411 := ⟨375, by decide⟩
  let bankTail : Fin 35 → Wire 411 := fun j ↦ mk36Bank36W j.succ
  let cInner : CliffProg 411 :=
    .seq (.cnot u0 cin0W (wire_ne_of_lt (by have := hu0.2; dsimp [cin0W]; omega)))
      (.seq (.x cin0W)
        (.seq (.x u0)
          (fmkFanoutCnot 35 u0 bankTail
            (fun j ↦ wire_ne_of_lt (by
              have := hu0.2; simp only [bankTail, mk36Bank36W, Fin.val_succ]; omega)))))
  let K2b : TempCtx 411 :=
    (ctxTempBit u0 (mk36Bank36W 0) cin0W
      (wire_ne_of_lt (by have := hu0.2; dsimp [mk36Bank36W]; omega))
      (wire_ne_of_lt (by have := hu0.2; dsimp [cin0W]; omega))
      (wire_ne_of_lt (by dsimp [mk36Bank36W, cin0W]; omega))).append
      (ctxCliffAlloc cInner)
  K2b.plug
    (fmkInPlaceAddModCarry 35 376 (by decide) (mk36H36NoDummy u0) mk36Cat36W cin0W
      (fun j h ↦ mk36H36NoDummy_not_cat36 u0 hu0.1 j (by rw [← h]; dsimp [mk36Cat36W]; omega))
      (fun j ↦ wire_ne_of_lt (by dsimp [mk36Cat36W, cin0W]; omega))
      (fun j ↦ wire_ne_of_lt (mk36H36NoDummy_lt375 u0 hu0.2 j))
      (fun j ↦ fmkLtTrans (mk36H36NoDummy_lt375 u0 hu0.2 j) (by decide))
      (fun j ↦ by dsimp [mk36Cat36W]; omega)
      (by decide))

theorem mk36Step2b36_nodummy_spec (u0 : Wire 411)
    (hu0 : ¬(113 ≤ u0.val ∧ u0.val < 149) ∧ u0.val < 339) :
    (mk36Step2b36_nodummy u0 hu0).countTempAnd = 36 ∧
      fmkIsMutBlock 411 (411 - 375) (fun w ↦ 113 ≤ w.val ∧ w.val < 149)
        (mk36Step2b36_nodummy u0 hu0) ∧
      (∀ γ : BitAssignment 411, cleanRem 411 (411 - 375) γ →
        let K_val := bitsVal (fun m ↦ γ (mk36Bank36W m))
        ((bitsVal (fun m ↦
          (mk36Step2b36_nodummy u0 hu0).evalBits γ (mk36Cat36W m)) : ℤ)).emod (2 ^ 36 : ℤ) =
          ((bitsVal (fun m ↦ γ (mk36Cat36W m)) : ℤ) +
            ((γ u0).val : ℤ) * (K_val : ℤ) - ((K_val / 2 : ℕ) : ℤ)).emod (2 ^ 36 : ℤ)) := by
  have hu_nc := hu0.1
  have hu_lt := hu0.2
  let mutCat36 : Wire 411 → Prop := fun w ↦ 113 ≤ w.val ∧ w.val < 149
  let cin0W : Wire 411 := ⟨375, by decide⟩
  let bankTail : Fin 35 → Wire 411 := fun j ↦ mk36Bank36W j.succ
  have hbt_inj : Function.Injective bankTail := fun a b h ↦ by
    have hv := congrArg Fin.val h; simp only [bankTail, mk36Bank36W, Fin.val_succ] at hv;
      exact Fin.ext (by omega)
  have hcat_inj : Function.Injective mk36Cat36W := fun a b h ↦ by
    have hv := congrArg Fin.val h; dsimp [mk36Cat36W] at hv; exact Fin.ext (by omega)
  let addP := fmkInPlaceAddModCarry 35 376 (by decide) (mk36H36NoDummy u0) mk36Cat36W cin0W
    (fun j h ↦ mk36H36NoDummy_not_cat36 u0 hu_nc j (by rw [← h]; dsimp [mk36Cat36W]; omega))
    (fun j ↦ wire_ne_of_lt (by dsimp [mk36Cat36W, cin0W]; omega))
    (fun j ↦ wire_ne_of_lt (mk36H36NoDummy_lt375 u0 hu_lt j))
    (fun j ↦ fmkLtTrans (mk36H36NoDummy_lt375 u0 hu_lt j) (by decide))
    (fun j ↦ by dsimp [mk36Cat36W]; omega) (by decide)
  obtain ⟨hvAdd, hsAdd, hAdd⟩ := fmkInPlaceAddModCarry_spec 35 376 (by decide)
    (mk36H36NoDummy u0) mk36Cat36W cin0W
    (fun i j h ↦ mk36H36NoDummy_not_cat36 u0 hu_nc j (by rw [← h]; dsimp [mk36Cat36W]; omega))
    (fun j ↦ wire_ne_of_lt (by dsimp [mk36Cat36W, cin0W]; omega))
    (fun j ↦ wire_ne_of_lt (mk36H36NoDummy_lt375 u0 hu_lt j))
    (mk36H36NoDummy_inj u0 hu_lt) hcat_inj
    (fun j ↦ fmkLtTrans (mk36H36NoDummy_lt375 u0 hu_lt j) (by decide))
    (fun j ↦ by dsimp [mk36Cat36W]; omega) (by decide)
  have hNonAdd : ∀ δ, cleanRem 411 (411 - 376) δ → ∀ w, ¬ mutCat36 w → addP.evalBits δ w = δ w :=
    fun δ hδ w hw ↦ (hAdd δ hδ).2.1 w fun j hj ↦ hw (by
      rw [hj]; dsimp [mutCat36, mk36Cat36W]; omega)
  let cInner : CliffProg 411 :=
    .seq (.cnot u0 cin0W (wire_ne_of_lt (by dsimp [cin0W]; omega)))
      (.seq (.x cin0W)
        (.seq (.x u0)
          (fmkFanoutCnot 35 u0 bankTail
            (fun j ↦ wire_ne_of_lt (by simp only [bankTail, mk36Bank36W, Fin.val_succ]; omega)))))
  let K2b : TempCtx 411 :=
    (ctxTempBit u0 (mk36Bank36W 0) cin0W
      (wire_ne_of_lt (by dsimp [mk36Bank36W]; omega))
      (wire_ne_of_lt (by dsimp [cin0W]; omega))
      (wire_ne_of_lt (by dsimp [mk36Bank36W, cin0W]; omega))).append
      (ctxCliffAlloc cInner)
  have hd2b : K2b.DisjointFrom mutCat36 :=
    TempCtx.disjointFrom_append
      ⟨hu_nc, by dsimp [mutCat36, mk36Bank36W]; omega, by dsimp [mutCat36, cin0W]; omega, trivial⟩
      (ctxCliffAlloc_disjoint
        ⟨⟨hu_nc, by dsimp [mutCat36, cin0W]; omega⟩,
          by dsimp [CliffDisjoint, mutCat36, cin0W]; omega, hu_nc,
          mk36_cliffDisjoint_fanout u0 35 bankTail _ hu_nc
            (fun j ↦ by simp only [mutCat36, bankTail, mk36Bank36W, Fin.val_succ]; omega)⟩)
  have hsInner : cInner.SupportsBelow 376 :=
    ⟨⟨by omega, show cin0W.val < 376 by decide⟩,
      show cin0W.val < 376 by decide, show u0.val < 376 by omega,
      fmkFanoutCnot_supportsBelow 35 u0 bankTail _ (by omega)
        (fun j ↦ by simp only [bankTail, mk36Bank36W, Fin.val_succ]; omega)⟩
  have hs2b : K2b.SupportsBelowCtx 376 :=
    TempCtx.supportsBelowCtx_append le_rfl ⟨by decide, trivial⟩ (ctxCliffAlloc_supports hsInner)
  have hl2b : fmkTempCtxLiftEx 375 376 K2b :=
    fmkTempCtxLiftEx_append
      (fmkTempCtxLiftEx_tempBit (cur := 375) (by decide) u0 (mk36Bank36W 0) _ (by omega)
        (by dsimp [mk36Bank36W]; omega))
      (fmkTempCtxLiftEx_cliff (cur := 376) (by decide) cInner hsInner)
  obtain ⟨hc2b, hMut2b, hK2b_cl, hb2b_pos⟩ := mk36_plug_mutBlock (by decide)
    (fun _ hw ht ↦ by dsimp [mutCat36] at ht; omega) K2b hd2b hs2b hl2b addP hvAdd hsAdd hNonAdd
  have h2b_eq : mk36Step2b36_nodummy u0 hu0 = K2b.plug addP := rfl
  have hCnt36 : (mk36Step2b36_nodummy u0 hu0).countTempAnd = 36 := by
    rw [h2b_eq, hc2b]; change (1 + 0) + addP.countTempAnd = 36
    dsimp only [addP]; rw [fmkInPlaceAddModCarry_countTempAnd]
  refine ⟨hCnt36, h2b_eq ▸ hMut2b, fun γ hγ ↦ ?_⟩
  dsimp only
  let δ := K2b.fwdBits γ
  have hδ_cl : cleanRem 411 (411 - 376) δ := hK2b_cl γ hγ
  have h2b_val := (hAdd δ hδ_cl).2.2
  have hout_cat : ∀ m : Fin 36,
      (mk36Step2b36_nodummy u0 hu0).evalBits γ (mk36Cat36W m) = addP.evalBits δ (mk36Cat36W m) :=
    fun m ↦ by rw [h2b_eq]; exact hb2b_pos γ hγ _ (by dsimp [mutCat36, mk36Cat36W]; omega)
  simp_rw [hout_cat]
  let γt : BitAssignment 411 := Function.update γ cin0W (γ cin0W + γ u0 * γ (mk36Bank36W 0))
  have hδ_eq : δ = cInner.eval γt := by dsimp only [δ, K2b]; rw [fmkAppend_fwdBits]; rfl
  have hγt_ne : ∀ w : Wire 411, w ≠ cin0W → γt w = γ w := fun w hw ↦ Function.update_of_ne hw _ _
  have hγt_cin : γt cin0W = γ u0 * γ (mk36Bank36W 0) := by
    dsimp only [γt]; rw [Function.update_self, hγ cin0W (by decide), zero_add]
  have hδ_cat : (fun m ↦ δ (mk36Cat36W m)) = fun m ↦ γ (mk36Cat36W m) := funext fun m ↦ by
    rw [hδ_eq]; dsimp only [cInner, CliffProg.eval]
    rw [fmkFanoutCnot_eval 35 u0 bankTail _ hbt_inj,
      fmkIteNeg (by
        rintro ⟨j, hj⟩; have hv := congrArg Fin.val hj;
        simp only [mk36Cat36W, bankTail, mk36Bank36W, Fin.val_succ] at hv; omega),
      Function.update_of_ne (fun h ↦ hu_nc (by rw [← h]; dsimp [mk36Cat36W]; omega)),
      Function.update_of_ne (wire_ne_of_lt (by dsimp [mk36Cat36W, cin0W]; omega)),
      Function.update_of_ne (wire_ne_of_lt (by dsimp [mk36Cat36W, cin0W]; omega)),
      hγt_ne _ (wire_ne_of_lt (by dsimp [mk36Cat36W, cin0W]; omega))]
  have hδ_cin : δ cin0W = γ u0 * γ (mk36Bank36W 0) + γ u0 + 1 := by
    rw [hδ_eq]; dsimp only [cInner, CliffProg.eval]
    rw [fmkFanoutCnot_eval 35 u0 bankTail _ hbt_inj,
      fmkIteNeg (by
        rintro ⟨j, hj⟩; have hv := congrArg Fin.val hj;
        simp only [cin0W, bankTail, mk36Bank36W, Fin.val_succ] at hv; omega),
      Function.update_of_ne (wire_ne_of_gt (by dsimp [cin0W]; omega)),
      Function.update_self, Function.update_self,
      hγt_ne u0 (wire_ne_of_lt (by dsimp [cin0W]; omega)), hγt_cin]
  let hZero : Fin 36 → ZMod 2 := Fin.snoc (fun j : Fin 35 ↦ γ (mk36Bank36W j.succ)) 0
  have hδ_h36 : ∀ j : Fin 36, δ (mk36H36NoDummy u0 j) = hZero j + (γ u0 + 1) := fun j ↦ by
    rw [hδ_eq]; dsimp only [cInner, CliffProg.eval]
    refine Fin.lastCases ?_ (fun i ↦ ?_) j
    · simp only [mk36H36NoDummy, hZero, Fin.snoc_last, zero_add]
      rw [fmkFanoutCnot_eval 35 u0 bankTail _ hbt_inj,
        fmkIteNeg (by
          rintro ⟨k, hk⟩; have hv := congrArg Fin.val hk;
          simp only [bankTail, mk36Bank36W, Fin.val_succ] at hv; omega),
        Function.update_self, Function.update_of_ne (wire_ne_of_lt (by dsimp [cin0W]; omega)),
        Function.update_of_ne (wire_ne_of_lt (by dsimp [cin0W]; omega)),
        hγt_ne u0 (wire_ne_of_lt (by dsimp [cin0W]; omega))]
    · simp only [mk36H36NoDummy, hZero, Fin.snoc_castSucc]
      have hbi_lt : mk36Bank36W i.succ ≠ cin0W :=
        wire_ne_of_lt (by simp only [mk36Bank36W, cin0W, Fin.val_succ]; omega)
      have hbi_gt : mk36Bank36W i.succ ≠ u0 :=
        wire_ne_of_gt (by simp only [mk36Bank36W, Fin.val_succ]; omega)
      have hu0_lt : u0 ≠ cin0W := wire_ne_of_lt (by dsimp [cin0W]; omega)
      rw [fmkFanoutCnot_eval 35 u0 bankTail _ hbt_inj, fmkItePos ⟨i, rfl⟩,
        Function.update_of_ne hbi_gt, Function.update_of_ne hbi_lt, Function.update_of_ne hbi_lt,
        Function.update_self, Function.update_of_ne hu0_lt, Function.update_of_ne hu0_lt,
        hγt_ne _ hbi_lt, hγt_ne u0 hu0_lt]
  have hhZero_val : bitsVal hZero = bitsVal (fun j : Fin 35 ↦ γ (mk36Bank36W j.succ)) := by
    rw [fmkBitsVal_castSucc_split]
    have hlo : (fun j : Fin 35 ↦ hZero j.castSucc) = fun j ↦ γ (mk36Bank36W j.succ) :=
      funext fun j ↦ by simp only [hZero, Fin.snoc_castSucc]
    have hhi : hZero (Fin.last 35) = 0 := by simp only [hZero, Fin.snoc_last]
    rw [hlo, hhi, ZMod.val_zero, mul_zero, add_zero]
  set C_in := bitsVal (fun m ↦ γ (mk36Cat36W m))
  set H_val := bitsVal (fun j : Fin 35 ↦ γ (mk36Bank36W j.succ))
  set K_val := bitsVal (fun m ↦ γ (mk36Bank36W m))
  have hK_sp : K_val = (γ (mk36Bank36W 0)).val + 2 * H_val := fmkBitsVal_succ_split _
  have hb0_lt : (γ (mk36Bank36W 0)).val < 2 := ZMod.val_lt _
  have hH_div : K_val / 2 = H_val := by omega
  rw [hδ_cat, Nat.add_assoc] at h2b_val
  rw [h2b_val, hH_div]
  set B2 := bitsVal (fun j ↦ δ (mk36H36NoDummy u0 j)) + (δ cin0W).val
  have hH_lt : H_val < 2 ^ 36 := by rw [← hhZero_val]; exact bitsVal_lt_two_pow _
  rcases fmkBit_cases (γ u0) with hu_z | hu_o
  · have hB2 : B2 = 2 ^ 36 - H_val := by
      dsimp only [B2]
      have hfn : (fun j ↦ δ (mk36H36NoDummy u0 j)) = fun j ↦ hZero j + 1 :=
        funext fun j ↦ by rw [hδ_h36 j, hu_z, zero_add]
      have hfl := fmkBitsVal_flip_all 36 hZero
      rw [hhZero_val] at hfl
      rw [hfn, hδ_cin, hu_z, zero_mul, add_zero, zero_add, ZMod.val_one]
      omega
    rw [hu_z, ZMod.val_zero]
    change (((C_in + B2) % 2 ^ 36 : ℕ) : ℤ) % (2 ^ 36 : ℤ) =
      ((C_in : ℤ) + (0 : ℤ) * (K_val : ℤ) - (H_val : ℤ)) % (2 ^ 36 : ℤ)
    clear_value C_in H_val K_val B2; omega
  · have hB2 : B2 = H_val + (γ (mk36Bank36W 0)).val := by
      dsimp only [B2]
      have hfn : (fun j ↦ δ (mk36H36NoDummy u0 j)) = hZero :=
        funext fun j ↦ by rw [hδ_h36 j, hu_o, CharTwo.add_self_eq_zero, add_zero]
      rw [hfn, hhZero_val, hδ_cin, hu_o, one_mul, fmkZmod2_add_self_cancel]
    set b0 := (γ (mk36Bank36W 0)).val
    rw [hu_o, ZMod.val_one]
    change (((C_in + B2) % 2 ^ 36 : ℕ) : ℤ) % (2 ^ 36 : ℤ) =
      ((C_in : ℤ) + (1 : ℤ) * (K_val : ℤ) - (H_val : ℤ)) % (2 ^ 36 : ℤ)
    clear_value C_in H_val K_val B2 b0; omega

attribute [local irreducible] mk36Step2b36_nodummy

/-- Shifted signed-bit modular accumulate step on `cat36` at dynamic `curCarry` (`35 - s.val`
  `TempAnd`s). -/
def mk36ShiftStep36_at (uBit : Wire 411) (curCarry : ℕ) (s : Fin 8) (hu : ¬(113 ≤ uBit.val ∧
    uBit.val < 149) ∧ ¬(339 ≤ uBit.val ∧ uBit.val < 375) ∧ uBit.val < curCarry)
    (hcur : 375 ≤ curCarry ∧ curCarry + (35 - s.val) ≤ 411) : TempPhaseProg 411 :=
  let W := 35 - s.val
  let bankSlice : Fin (W + 1) → Wire 411 := fun j ↦ mk36Bank36W ⟨j.val, by dsimp [W] at *; omega⟩
  let catSlice : Fin (W + 1) → Wire 411 := fun j ↦ mk36Cat36W ⟨s.val + j.val, by
    dsimp [W] at *; omega⟩
  let cPrep : CliffProg 411 :=
    .seq (.x uBit) (fmkFanoutCnot (W + 1) uBit bankSlice
      (fun j h ↦ hu.2.1 (by rw [h]; dsimp [bankSlice, mk36Bank36W]; omega)))
  (ctxCliffAlloc cPrep).plug
    (fmkInPlaceAddModCarry W curCarry (by dsimp [W]; exact hcur.2) bankSlice catSlice uBit
      (fun j ↦ wire_ne_of_lt (by dsimp [catSlice, bankSlice, mk36Cat36W, mk36Bank36W]; omega))
      (fun j h ↦ hu.1 (by rw [← h]; dsimp [catSlice, mk36Cat36W]; omega))
      (fun j h ↦ hu.2.1 (by rw [← h]; dsimp [bankSlice, mk36Bank36W]; omega))
      (fun j ↦ by dsimp [bankSlice, mk36Bank36W]; omega)
      (fun j ↦ by dsimp [catSlice, mk36Cat36W]; omega)
      hu.2.2)

theorem mk36ShiftStep36_at_spec (uBit : Wire 411) (curCarry : ℕ) (s : Fin 8) (hu : ¬(113 ≤
    uBit.val ∧ uBit.val < 149) ∧ ¬(339 ≤ uBit.val ∧ uBit.val < 375) ∧ uBit.val < curCarry)
    (hcur : 375 ≤ curCarry ∧ curCarry + (35 - s.val) ≤ 411) :
    (mk36ShiftStep36_at uBit curCarry s hu hcur).countTempAnd = 35 - s.val ∧ fmkIsMutBlock 411
    (411 - curCarry) (fun w ↦ 113 ≤ w.val ∧ w.val < 149)
    (mk36ShiftStep36_at uBit curCarry s hu hcur) ∧ (∀ γ : BitAssignment 411, cleanRem 411 (411
    - curCarry) γ → ((bitsVal (fun m ↦ (mk36ShiftStep36_at uBit curCarry s hu hcur).evalBits γ
    (mk36Cat36W m)) : ℤ)).emod (2 ^ 36 : ℤ) = ((bitsVal (fun m ↦ γ (mk36Cat36W m)) : ℤ) + (2 ^
    s.val : ℤ) * (2 * ((γ uBit).val : ℤ) - 1) * (bitsVal (fun m ↦ γ (mk36Bank36W m)) :
    ℤ)).emod (2 ^ 36 : ℤ)) := by
  let mutCat36 : Wire 411 → Prop := fun w ↦ 113 ≤ w.val ∧ w.val < 149
  let W := 35 - s.val
  let bankSlice : Fin (W + 1) → Wire 411 := fun j ↦ mk36Bank36W ⟨j.val, by dsimp [W] at *; omega⟩
  let catSlice : Fin (W + 1) → Wire 411 := fun j ↦ mk36Cat36W ⟨s.val + j.val, by
    dsimp [W] at *; omega⟩
  let cPrep : CliffProg 411 :=
    .seq (.x uBit) (fmkFanoutCnot (W + 1) uBit bankSlice
      (fun j h ↦ hu.2.1 (by rw [h]; dsimp [bankSlice, mk36Bank36W]; omega)))
  let addP := fmkInPlaceAddModCarry W curCarry (by dsimp [W]; exact hcur.2) bankSlice catSlice uBit
    (fun j ↦ wire_ne_of_lt (by dsimp [catSlice, bankSlice, mk36Cat36W, mk36Bank36W]; omega))
    (fun j h ↦ hu.1 (by rw [← h]; dsimp [catSlice, mk36Cat36W]; omega))
    (fun j h ↦ hu.2.1 (by rw [← h]; dsimp [bankSlice, mk36Bank36W]; omega))
    (fun j ↦ by dsimp [bankSlice, mk36Bank36W]; omega)
    (fun j ↦ by dsimp [catSlice, mk36Cat36W]; omega) hu.2.2
  have hbank_inj : Function.Injective bankSlice := fun a b h ↦ by
    have hv := congrArg Fin.val h; dsimp [bankSlice, mk36Bank36W] at hv; exact Fin.ext (by omega)
  have hcat_inj : Function.Injective catSlice := fun a b h ↦ by
    have hv := congrArg Fin.val h; dsimp [catSlice, mk36Cat36W] at hv; exact Fin.ext (by omega)
  obtain ⟨hvAdd, hsAdd, hAdd⟩ := fmkInPlaceAddModCarry_spec W curCarry (by dsimp [W]; exact hcur.2)
    bankSlice catSlice uBit
    (fun i j ↦ wire_ne_of_lt (by dsimp [catSlice, bankSlice, mk36Cat36W, mk36Bank36W]; omega))
    (fun j h ↦ hu.1 (by rw [← h]; dsimp [catSlice, mk36Cat36W]; omega))
    (fun j h ↦ hu.2.1 (by rw [← h]; dsimp [bankSlice, mk36Bank36W]; omega))
    hbank_inj hcat_inj
    (fun j ↦ by dsimp [bankSlice, mk36Bank36W]; omega)
    (fun j ↦ by dsimp [catSlice, mk36Cat36W]; omega) hu.2.2
  have hdPrep : (ctxCliffAlloc cPrep).DisjointFrom mutCat36 :=
    ctxCliffAlloc_disjoint ⟨hu.1, mk36_cliffDisjoint_fanout uBit (W + 1) bankSlice _ hu.1
      (fun j ↦ by dsimp [mutCat36, bankSlice, mk36Bank36W]; omega)⟩
  have hsPrep : cPrep.SupportsBelow curCarry :=
    ⟨hu.2.2, fmkFanoutCnot_supportsBelow (W + 1) uBit bankSlice _ hu.2.2
      (fun j ↦ by dsimp [bankSlice, mk36Bank36W]; omega)⟩
  have hlPrep : fmkTempCtxLiftEx curCarry curCarry (ctxCliffAlloc cPrep) :=
    fmkTempCtxLiftEx_cliff (by omega) cPrep hsPrep
  have hAddNon : ∀ δ, cleanRem 411 (411 - curCarry) δ → ∀ w,
    ¬ mutCat36 w → addP.evalBits δ w = δ w :=
    fun δ hδ w hw ↦ (hAdd δ hδ).2.1 w fun j hj ↦ hw (by
      rw [hj]; dsimp [mutCat36, catSlice, mk36Cat36W]; omega)
  obtain ⟨hCnt, hMutP, hPrepCl, hbPos⟩ := mk36_plug_mutBlock le_rfl
    (fun _ hw ht ↦ by dsimp [mutCat36] at ht; omega) (ctxCliffAlloc cPrep) hdPrep
    (ctxCliffAlloc_supports hsPrep) hlPrep addP hvAdd hsAdd hAddNon
  have hCntEq : (ctxCliffAlloc cPrep).countTempAnd + addP.countTempAnd = 35 - s.val := by
    change 0 + addP.countTempAnd = 35 - s.val
    rw [zero_add, fmkInPlaceAddModCarry_countTempAnd]
  refine ⟨hCnt.trans hCntEq, hMutP, fun γ hγ ↦ ?_⟩
  let γ1 := cPrep.eval γ
  have hγ1_cl : cleanRem 411 (411 - curCarry) γ1 := hPrepCl γ hγ
  have hγ1_cat : ∀ m : Fin 36, γ1 (mk36Cat36W m) = γ (mk36Cat36W m) := fun m ↦ by
    dsimp only [γ1, cPrep, CliffProg.eval]
    rw [fmkFanoutCnot_eval (W + 1) uBit bankSlice _ hbank_inj,
      fmkIteNeg (by
        rintro ⟨j, hj⟩; have hv := congrArg Fin.val hj;
        dsimp [mk36Cat36W, bankSlice, mk36Bank36W] at hv; omega),
      Function.update_of_ne (fun h ↦ hu.1 (by rw [← h]; dsimp [mk36Cat36W]; omega))]
  have hout_cat : ∀ m : Fin 36,
      (mk36ShiftStep36_at uBit curCarry s hu hcur).evalBits γ (mk36Cat36W m) =
        addP.evalBits γ1 (mk36Cat36W m) :=
    fun m ↦ hbPos γ hγ _ (by dsimp [mutCat36, mk36Cat36W]; omega)
  simp_rw [hout_cat]
  have hlow_eq : ∀ m : Fin 36, m.val < s.val → addP.evalBits γ1 (mk36Cat36W m) = γ (mk36Cat36W m) :=
    by
    intro m hm
    rw [(hAdd γ1 hγ1_cl).2.1 (mk36Cat36W m) (fun j hj ↦ by
      have hv := congrArg Fin.val hj; dsimp [catSlice, mk36Cat36W] at hv; omega)]
    exact hγ1_cat m
  have hsW : s.val + (W + 1) = 36 := by dsimp [W]; omega
  have hslin := fmkBitsVal_slice_linear hsW (fun m : Fin 36 ↦ γ (mk36Cat36W m))
      (fun m : Fin 36 ↦ addP.evalBits γ1 (mk36Cat36W m)) hlow_eq
  have hcat_in_sl : (fun j : Fin (W + 1) ↦ γ (mk36Cat36W ⟨s.val + j.val, by omega⟩)) =
      fun j : Fin (W + 1) ↦ γ1 (catSlice j) := funext fun j ↦ (hγ1_cat _).symm
  have hcat_out_sl : (fun j : Fin (W + 1) ↦
    addP.evalBits γ1 (mk36Cat36W ⟨s.val + j.val, by omega⟩)) =
      fun j : Fin (W + 1) ↦ addP.evalBits γ1 (catSlice j) := rfl
  rw [hcat_in_sl, hcat_out_sl, (hAdd γ1 hγ1_cl).2.2] at hslin
  have hγ1_u : γ1 uBit = γ uBit + 1 := by
    dsimp only [γ1, cPrep, CliffProg.eval]
    rw [fmkFanoutCnot_eval (W + 1) uBit bankSlice _ hbank_inj,
      fmkIteNeg (by
        rintro ⟨j, hj⟩; exact hu.2.1 (by rw [hj]; dsimp [bankSlice, mk36Bank36W]; omega)),
      Function.update_self]
  have hγ1_bs : ∀ j : Fin (W + 1), γ1 (bankSlice j) = γ (bankSlice j) + (γ uBit + 1) := fun j ↦ by
    dsimp only [γ1, cPrep, CliffProg.eval]
    rw [fmkFanoutCnot_eval (W + 1) uBit bankSlice _ hbank_inj, fmkItePos ⟨j, rfl⟩,
      Function.update_self,
      Function.update_of_ne (fun h ↦ hu.2.1 (by rw [← h]; dsimp [bankSlice, mk36Bank36W]; omega))]
  set C_in := bitsVal (fun m ↦ γ (mk36Cat36W m))
  set C_out := bitsVal (fun m ↦ addP.evalBits γ1 (mk36Cat36W m))
  set C_sl := bitsVal (fun j ↦ γ1 (catSlice j))
  set K_val := bitsVal (fun m ↦ γ (mk36Bank36W m))
  set K_lo := bitsVal (fun j : Fin (W + 1) ↦ γ (bankSlice j))
  have hK_mod : K_lo = K_val % 2 ^ (W + 1) := by
    dsimp only [K_lo, K_val, bankSlice]
    exact fmkBitsVal_take_mod (W + 1) (by dsimp [W]; omega) (fun m ↦ γ (mk36Bank36W m))
  have hK_div := Nat.div_add_mod K_val (2 ^ (W + 1))
  rw [← hK_mod] at hK_div
  have hp36 : 2 ^ s.val * 2 ^ (W + 1) = 2 ^ 36 := by rw [← pow_add, hsW]
  set B_add := bitsVal (fun j ↦ γ1 (bankSlice j)) + (γ1 uBit).val
  rw [Nat.add_assoc C_sl] at hslin
  have hslin' : C_out + 2 ^ s.val * C_sl = C_in + 2 ^ s.val * ((C_sl + B_add) % 2 ^ (W + 1)) :=
    hslin
  have hS_div := Nat.div_add_mod (C_sl + B_add) (2 ^ (W + 1))
  have hK36 : 2 ^ 36 * (K_val / 2 ^ (W + 1)) + 2 ^ s.val * K_lo = 2 ^ s.val * K_val := by
    calc 2 ^ 36 * (K_val / 2 ^ (W + 1)) + 2 ^ s.val * K_lo
      _ = 2 ^ s.val * (2 ^ (W + 1) * (K_val / 2 ^ (W + 1)) + K_lo) := by rw [← hp36]; ring
      _ = 2 ^ s.val * K_val := by rw [hK_div]
  have hS36 : 2 ^ 36 * ((C_sl + B_add) / 2 ^ (W + 1)) + 2 ^ s.val * ((C_sl + B_add) % 2 ^ (W + 1)) =
      2 ^ s.val * C_sl + 2 ^ s.val * B_add := by
    calc 2 ^ 36 * ((C_sl + B_add) / 2 ^ (W + 1)) + 2 ^ s.val * ((C_sl + B_add) % 2 ^ (W + 1))
      _ = 2 ^ s.val * (2 ^ (W + 1) * ((C_sl + B_add) / 2 ^ (W + 1)) + (C_sl + B_add) % 2 ^ (W +
        1)) := by
          rw [← hp36]; ring
      _ = 2 ^ s.val * (C_sl + B_add) := by rw [hS_div]
      _ = 2 ^ s.val * C_sl + 2 ^ s.val * B_add := by ring
  rcases fmkBit_cases (γ uBit) with hu0 | hu1
  · have hB_eq : B_add + K_lo = 2 ^ (W + 1) := by
      dsimp only [B_add]
      have hbs_fn : (fun j ↦ γ1 (bankSlice j)) = fun j ↦ γ (bankSlice j) + 1 :=
        funext fun j ↦ by rw [hγ1_bs j, hu0, zero_add]
      have hfl := fmkBitsVal_flip_all (W + 1) (fun j ↦ γ (bankSlice j))
      have hk_lt := bitsVal_lt_two_pow (fun j ↦ γ (bankSlice j))
      rw [hbs_fn, hγ1_u, hu0, zero_add, ZMod.val_one]
      dsimp only [K_lo]; omega
    have hB36 : 2 ^ s.val * B_add + 2 ^ s.val * K_lo = 2 ^ 36 := by
      calc 2 ^ s.val * B_add + 2 ^ s.val * K_lo
        _ = 2 ^ s.val * (B_add + K_lo) := by ring
        _ = 2 ^ s.val * 2 ^ (W + 1) := by rw [hB_eq]
        _ = 2 ^ 36 := hp36
    have hint_eq : (C_out : ℤ) =
        ((C_in : ℤ) + (2 ^ s.val : ℤ) * (2 * ((γ uBit).val : ℤ) - 1) * (K_val : ℤ)) +
          (1 + (K_val / 2 ^ (W + 1) : ℤ) - ((C_sl + B_add) / 2 ^ (W + 1) : ℤ)) * (2 ^ 36 : ℤ) := by
      rw [hu0, ZMod.val_zero]; zify at hslin' hK36 hS36 hB36 ⊢; linarith
    change (C_out : ℤ) % (2 ^ 36 : ℤ) = _ % (2 ^ 36 : ℤ)
    rw [hint_eq, Int.add_mul_emod_self_right]
  · have hB_eq : B_add = K_lo := by
      dsimp only [B_add]
      have hbs_fn : (fun j ↦ γ1 (bankSlice j)) = fun j ↦ γ (bankSlice j) :=
        funext fun j ↦ by rw [hγ1_bs j, hu1, CharTwo.add_self_eq_zero, add_zero]
      rw [hbs_fn, hγ1_u, hu1, CharTwo.add_self_eq_zero, ZMod.val_zero, add_zero]
    have hB36 : 2 ^ s.val * B_add = 2 ^ s.val * K_lo := congrArg (2 ^ s.val * ·) hB_eq
    have hint_eq : (C_out : ℤ) =
        ((C_in : ℤ) + (2 ^ s.val : ℤ) * (2 * ((γ uBit).val : ℤ) - 1) * (K_val : ℤ)) +
          (-((K_val / 2 ^ (W + 1) : ℤ) + ((C_sl + B_add) / 2 ^ (W + 1) : ℤ))) * (2 ^ 36 : ℤ) := by
      rw [hu1, ZMod.val_one]; zify at hslin' hK36 hS36 hB36 ⊢; linarith
    change (C_out : ℤ) % (2 ^ 36 : ℤ) = _ % (2 ^ 36 : ℤ)
    rw [hint_eq, Int.add_mul_emod_self_right]

attribute [local irreducible] mk36ShiftStep36_at

/-- Interleaved carry-ripple + `36`-bit shifted accumulate for `k = 8 - rem ∈ {1..8}`
(`259` `TempAnd`s at `rem = 7`, clean `[375 + k .. 411)`). -/
def mk36InterleavedU9Shift36 (w : Fin 3) : (rem : ℕ) → (hrem : rem ≤ 7) → TempPhaseProg 411
  | 0, _ =>
      mk36ShiftStep36_at ⟨382, by decide⟩ 383 ⟨7, by decide⟩
        ⟨by decide, by decide, by decide⟩ ⟨by decide, by decide⟩
  | rem + 1, hrem =>
      let k := 8 - (rem + 1)
      let ckW : Wire 411 := ⟨375 + k - 1, by dsimp [k]; omega⟩
      let pNewK : Wire 411 := mk36PNewW w ⟨k, by dsimp [k]; omega⟩
      let pOldK : Wire 411 := mk36POldW w ⟨k, by dsimp [k]; omega⟩
      let cXorSum : CliffProg 411 :=
        .seq (.cnot pOldK pNewK (mk36PNew_ne_pOld w _).symm)
          (.cnot ckW pNewK (wire_ne_of_gt (by dsimp [ckW, pNewK, mk36PNewW]; omega)))
      .seq
        ((ctxCliffAlloc cXorSum).plug
          (mk36ShiftStep36_at pNewK (375 + k) ⟨k - 1, by dsimp [k]; omega⟩
            ⟨by dsimp [pNewK, mk36PNewW]; omega,
             by dsimp [pNewK, mk36PNewW]; omega,
             by dsimp [pNewK, mk36PNewW, k]; omega⟩
            ⟨by omega, by dsimp [k]; omega⟩))
        ((fmkCtxCarryStep (375 + k) (by dsimp [k]; omega) pNewK pOldK ckW
          (mk36PNew_ne_pOld w _)
          (wire_ne_of_lt (by dsimp [pNewK, mk36PNewW, ckW, k]; omega))
          (wire_ne_of_lt (by dsimp [pOldK, mk36POldW, ckW, k]; omega))
          (by dsimp [pNewK, mk36PNewW, k]; omega)
          (by dsimp [pOldK, mk36POldW, k]; omega)
          (by dsimp [ckW, k]; omega)).plug
          (mk36InterleavedU9Shift36 w rem (by omega)))

theorem mk36InterleavedU9Shift36_spec (w : Fin 3) :
    ∀ (rem : ℕ) (hrem : rem ≤ 7),
      let k := 8 - rem
      let pR := mk36InterleavedU9Shift36 w rem hrem
      pR.countTempAnd = (∑ i : Fin (rem + 1), (28 + i.val)) + rem ∧
        fmkIsMutBlock 411 (411 - (375 + k)) (fun q ↦ 113 ≤ q.val ∧ q.val < 149) pR ∧
        (∀ γ : BitAssignment 411, cleanRem 411 (411 - (375 + k)) γ →
          let a : Fin 8 → ZMod 2 := fun b ↦ γ (mk36PNewW w b)
          let b : Fin 8 → ZMod 2 := fun b ↦ γ (mk36POldW w b)
          γ ⟨375 + k - 1, by dsimp [k]; omega⟩ = fmkCarryChain a b k →
          ((bitsVal (fun m ↦ pR.evalBits γ (mk36Cat36W m)) : ℤ)).emod (2 ^ 36 : ℤ) =
            ((bitsVal (fun m ↦ γ (mk36Cat36W m)) : ℤ) +
              (∑ i : Fin (rem + 1),
                (2 ^ (k - 1 + i.val) : ℤ) *
                  (2 * ((fmkSum9 a b ⟨k + i.val, by dsimp [k]; omega⟩).val : ℤ) - 1)) *
                (bitsVal (fun m ↦ γ (mk36Bank36W m)) : ℤ)).emod (2 ^ 36 : ℤ)) := by
  let mutCat36 : Wire 411 → Prop := fun q ↦ 113 ≤ q.val ∧ q.val < 149
  intro rem
  induction rem with
  | zero =>
      intro hrem
      dsimp only [mk36InterleavedU9Shift36]
      obtain ⟨hCnt, hMut, hEv⟩ := mk36ShiftStep36_at_spec ⟨382, by decide⟩ 383 ⟨7, by decide⟩
        ⟨by decide, by decide, by decide⟩ ⟨by decide, by decide⟩
      have hCnt0 : (mk36ShiftStep36_at ⟨382, by decide⟩ 383 ⟨7, by decide⟩
          ⟨by decide, by decide, by decide⟩ ⟨by decide, by decide⟩).countTempAnd =
          (∑ i : Fin (0 + 1), (28 + i.val)) + 0 := by
        rw [hCnt]
        decide
      refine ⟨hCnt0, hMut, fun γ hγ hc8 ↦ ?_⟩
      rw [hEv γ hγ, Fin.sum_univ_succ, Finset.univ_eq_empty, Finset.sum_empty, add_zero]
      have hs8 : fmkSum9 (fun b ↦ γ (mk36PNewW w b)) (fun b ↦ γ (mk36POldW w b)) ⟨8, by decide⟩ =
          γ ⟨382, by decide⟩ := hc8.symm
      change _ =
        ((bitsVal (fun m ↦ γ (mk36Cat36W m)) : ℤ) +
          (2 ^ 7 : ℤ) *
            (2 * ((fmkSum9 (fun b ↦ γ (mk36PNewW w b)) (fun b ↦
              γ (mk36POldW w b)) ⟨8, by decide⟩).val : ℤ) - 1) *
            (bitsVal (fun m ↦ γ (mk36Bank36W m)) : ℤ)).emod (2 ^ 36 : ℤ)
      rw [hs8]
  | succ rem ih =>
      intro hrem
      set k := 8 - (rem + 1)
      have hk_pos : 1 ≤ k := by dsimp [k]; omega
      have hk_lt8 : k < 8 := by dsimp [k]; omega
      let ckW : Wire 411 := ⟨375 + k - 1, by omega⟩
      let pNewK : Wire 411 := mk36PNewW w ⟨k, hk_lt8⟩
      let pOldK : Wire 411 := mk36POldW w ⟨k, hk_lt8⟩
      let cXorSum : CliffProg 411 :=
        .seq (.cnot pOldK pNewK (mk36PNew_ne_pOld w _).symm)
          (.cnot ckW pNewK (wire_ne_of_gt (by dsimp [ckW, pNewK, mk36PNewW]; omega)))
      let shK := mk36ShiftStep36_at pNewK (375 + k) ⟨k - 1, by omega⟩
        ⟨by dsimp [pNewK, mk36PNewW]; omega,
         by dsimp [pNewK, mk36PNewW]; omega,
         by dsimp [pNewK, mk36PNewW]; omega⟩
        ⟨by omega, by dsimp; omega⟩
      obtain ⟨hCntSh, hMutSh, hEvSh⟩ := mk36ShiftStep36_at_spec pNewK (375 + k) ⟨k - 1, by omega⟩
        ⟨by dsimp [pNewK, mk36PNewW]; omega,
         by dsimp [pNewK, mk36PNewW]; omega,
         by dsimp [pNewK, mk36PNewW]; omega⟩
        ⟨by omega, by dsimp; omega⟩
      have hdXor : (ctxCliffAlloc cXorSum).DisjointFrom mutCat36 :=
        ctxCliffAlloc_disjoint ⟨⟨by dsimp [mutCat36, pOldK, mk36POldW]; omega,
          by dsimp [mutCat36, pNewK, mk36PNewW]; omega⟩,
          by dsimp [mutCat36, ckW]; omega, by dsimp [mutCat36, pNewK, mk36PNewW]; omega⟩
      have hsXor : cXorSum.SupportsBelow (375 + k) :=
        ⟨⟨by dsimp [pOldK, mk36POldW]; omega, by dsimp [pNewK, mk36PNewW]; omega⟩,
          by dsimp [ckW]; omega, by dsimp [pNewK, mk36PNewW]; omega⟩
      have hlXor : fmkTempCtxLiftEx (375 + k) (375 + k) (ctxCliffAlloc cXorSum) :=
        fmkTempCtxLiftEx_cliff (by omega) cXorSum hsXor
      let step1 := (ctxCliffAlloc cXorSum).plug shK
      obtain ⟨hc1, hMut1, hXorCl, hb1_pos⟩ := mk36_plug_mutBlock le_rfl
        (fun _ hw ht ↦ by dsimp [mutCat36] at ht; omega) (ctxCliffAlloc cXorSum) hdXor
        (ctxCliffAlloc_supports hsXor) hlXor shK hMutSh.1 hMutSh.2.1 hMutSh.2.2.2
      obtain ⟨hCntRec, hMutRec, hEvRec⟩ := ih (by omega)
      have hk_rec : 8 - rem = k + 1 := by dsimp [k]; omega
      rw [hk_rec] at hMutRec
      let KCarry := fmkCtxCarryStep (375 + k) (by omega) pNewK pOldK ckW
        (mk36PNew_ne_pOld w _)
        (wire_ne_of_lt (by dsimp [pNewK, mk36PNewW, ckW]; omega))
        (wire_ne_of_lt (by dsimp [pOldK, mk36POldW, ckW]; omega))
        (by dsimp [pNewK, mk36PNewW]; omega)
        (by dsimp [pOldK, mk36POldW]; omega)
        (by dsimp [ckW]; omega)
      obtain ⟨hCntC, hdC, hsC, hlC, hFwdC⟩ := fmkCtxCarryStep_spec (mutW := mutCat36) (375 + k) (by
        omega)
        pNewK pOldK ckW (mk36PNew_ne_pOld w _)
        (wire_ne_of_lt (by dsimp [pNewK, mk36PNewW, ckW]; omega))
        (wire_ne_of_lt (by dsimp [pOldK, mk36POldW, ckW]; omega))
        (by dsimp [pNewK, mk36PNewW]; omega)
        (by dsimp [pOldK, mk36POldW]; omega)
        (by dsimp [ckW]; omega)
        (by dsimp [mutCat36, pNewK, mk36PNewW]; omega)
        (by dsimp [mutCat36, pOldK, mk36POldW]; omega)
        (by dsimp [mutCat36, ckW]; omega)
        (by dsimp [mutCat36]; omega)
      have h375 : 375 + (k + 1) = 375 + k + 1 := by omega
      rw [h375] at hMutRec
      let step2 := KCarry.plug (mk36InterleavedU9Shift36 w rem (by omega))
      obtain ⟨hc2, hMut2, hCCl, hb2_pos⟩ := mk36_plug_mutBlock (by omega)
        (fun _ hw ht ↦ by dsimp [mutCat36] at ht; omega) KCarry hdC hsC hlC
        (mk36InterleavedU9Shift36 w rem (by omega)) hMutRec.1 hMutRec.2.1 hMutRec.2.2.2
      have hCntTot : (TempPhaseProg.seq step1 step2).countTempAnd =
          (∑ i : Fin (rem + 1 + 1), (28 + i.val)) + (rem + 1) := by
        change step1.countTempAnd + step2.countTempAnd = _
        rw [hc1, hc2, hCntC, hCntSh, hCntRec, Fin.sum_univ_castSucc (n := rem + 1)]
        simp only [ctxCliffAlloc, TempCtx.countTempAnd, Fin.val_castSucc, Fin.val_last]
        dsimp [k]
        omega
      refine ⟨hCntTot, fmkIsMutBlock_seq (by omega) hMut1 hMut2, fun γ hγ hck ↦ ?_⟩
      let a : Fin 8 → ZMod 2 := fun b ↦ γ (mk36PNewW w b)
      let b : Fin 8 → ZMod 2 := fun b ↦ γ (mk36POldW w b)
      change ((bitsVal (fun m ↦
        step2.evalBits (step1.evalBits γ) (mk36Cat36W m)) : ℤ)).emod (2 ^ 36 : ℤ) = _
      let γx := cXorSum.eval γ
      have hγx_cl : cleanRem 411 (411 - (375 + k)) γx := hXorCl γ hγ
      have hγx_cat : (fun m ↦ γx (mk36Cat36W m)) = fun m ↦ γ (mk36Cat36W m) := funext fun m ↦ by
        dsimp [γx, cXorSum, CliffProg.eval]
        rw [Function.update_of_ne (wire_ne_of_lt (by dsimp [mk36Cat36W, pNewK, mk36PNewW]; omega)),
          Function.update_of_ne (wire_ne_of_lt (by dsimp [mk36Cat36W, pNewK, mk36PNewW]; omega))]
      have hγx_bank : (fun m ↦ γx (mk36Bank36W m)) = fun m ↦ γ (mk36Bank36W m) := funext fun m ↦ by
        dsimp [γx, cXorSum, CliffProg.eval]
        rw [Function.update_of_ne (wire_ne_of_gt (by dsimp [mk36Bank36W, pNewK, mk36PNewW]; omega)),
          Function.update_of_ne (wire_ne_of_gt (by dsimp [mk36Bank36W, pNewK, mk36PNewW]; omega))]
      have hγx_u : γx pNewK = fmkSum9 a b ⟨k, by omega⟩ := by
        dsimp [γx, cXorSum, CliffProg.eval, fmkSum9]
        rw [fmkDItePos hk_lt8, Function.update_self, Function.update_self,
          Function.update_of_ne (wire_ne_of_gt (by dsimp [ckW, pNewK, mk36PNewW]; omega)), hck]
      let γ1 := step1.evalBits γ
      have hγ1_cl : cleanRem 411 (411 - (375 + k)) γ1 := hMut1.2.2.1 γ hγ
      have hγ1_cat_fn : (fun m ↦ γ1 (mk36Cat36W m)) = fun m ↦ shK.evalBits γx (mk36Cat36W m) :=
        funext fun m ↦ hb1_pos γ hγ _ (by dsimp [mutCat36, mk36Cat36W]; omega)
      have hStep1Ev : ((bitsVal (fun m ↦ γ1 (mk36Cat36W m)) : ℤ)).emod (2 ^ 36 : ℤ) =
          ((bitsVal (fun m ↦ γ (mk36Cat36W m)) : ℤ) +
            (2 ^ (k - 1) : ℤ) * (2 * ((fmkSum9 a b ⟨k, by omega⟩).val : ℤ) - 1) *
              (bitsVal (fun m ↦ γ (mk36Bank36W m)) : ℤ)).emod (2 ^ 36 : ℤ) := by
        rw [hγ1_cat_fn, hEvSh γx hγx_cl, hγx_cat, hγx_bank, hγx_u]
      let γ2 := KCarry.fwdBits γ1
      have hγ2_eq : γ2 =
          Function.update γ1 ⟨375 + k,
            by omega⟩ (γ1 ckW + (γ1 pNewK + γ1 ckW) * (γ1 pOldK + γ1 ckW)) :=
        hFwdC γ1 hγ1_cl
      have hγ2_cl : cleanRem 411 (411 - (375 + k + 1)) γ2 := hCCl γ1 hγ1_cl
      have hγ1_non : ∀ q : Wire 411, ¬ mutCat36 q → γ1 q = γ q := hMut1.2.2.2 γ hγ
      have ha2 : (fun i : Fin 8 ↦ γ2 (mk36PNewW w i)) = a := funext fun i ↦ by
        rw [hγ2_eq, Function.update_of_ne (wire_ne_of_lt (by
          have := w.isLt; have := i.isLt; dsimp [mk36PNewW]; omega)),
          hγ1_non _ (by have := w.isLt; have := i.isLt; dsimp [mutCat36, mk36PNewW]; omega)]
      have hb2_fn : (fun i : Fin 8 ↦ γ2 (mk36POldW w i)) = b := funext fun i ↦ by
        rw [hγ2_eq, Function.update_of_ne (wire_ne_of_lt (by
          have := w.isLt; have := i.isLt; dsimp [mk36POldW]; omega)),
          hγ1_non _ (by have := w.isLt; have := i.isLt; dsimp [mutCat36, mk36POldW]; omega)]
      have hγ2_cat : (fun m ↦ γ2 (mk36Cat36W m)) = fun m ↦ γ1 (mk36Cat36W m) := funext fun m ↦ by
        rw [hγ2_eq, Function.update_of_ne (wire_ne_of_lt (by
          have := m.isLt; dsimp [mk36Cat36W]; omega))]
      have hγ2_bank : (fun m ↦ γ2 (mk36Bank36W m)) = fun m ↦ γ (mk36Bank36W m) := funext fun m ↦ by
        rw [hγ2_eq, Function.update_of_ne (wire_ne_of_lt (by
          have := m.isLt; dsimp [mk36Bank36W]; omega)),
          hγ1_non _ (by have := m.isLt; dsimp [mutCat36, mk36Bank36W]; omega)]
      have hck_next : γ2 ⟨375 + k + 1 - 1, by omega⟩ = fmkCarryChain a b (k + 1) := by
        have hw_eq : (⟨375 + k + 1 - 1, by omega⟩ : Wire 411) = ⟨375 + k, by omega⟩ := rfl
        rw [hw_eq, hγ2_eq, Function.update_self,
          hγ1_non ckW (by dsimp [mutCat36, ckW]; omega),
          hγ1_non pNewK (by have := w.isLt; dsimp [mutCat36, pNewK, mk36PNewW]; omega),
          hγ1_non pOldK (by have := w.isLt; dsimp [mutCat36, pOldK, mk36POldW]; omega), hck]
        dsimp [fmkCarryChain, a, b, pNewK, pOldK]
        rw [fmkDItePos hk_lt8]
      have hout2 : (fun m ↦ step2.evalBits γ1 (mk36Cat36W m)) =
          fun m ↦ (mk36InterleavedU9Shift36 w rem (by omega)).evalBits γ2 (mk36Cat36W m) :=
        funext fun m ↦ hb2_pos γ1 hγ1_cl _ (by have := m.isLt; dsimp [mutCat36, mk36Cat36W]; omega)
      have hγ2_cl_rec : cleanRem 411 (411 - (375 + (8 - rem))) γ2 := by
        simpa only [hk_rec, h375] using hγ2_cl
      have hck_rec : γ2 ⟨375 + (8 - rem) - 1, by omega⟩ = fmkCarryChain a b (8 - rem) := by
        have hw_rec : (⟨375 + (8 - rem) - 1, by omega⟩ : Wire 411) = ⟨375 + k + 1 - 1, by omega⟩ :=
          Fin.ext (by dsimp; omega)
        rw [hw_rec, hk_rec]
        exact hck_next
      have hRecEv := hEvRec γ2 hγ2_cl_rec
      dsimp only at hRecEv
      rw [ha2, hb2_fn] at hRecEv
      have hrhs_sum :
          (∑ i : Fin (rem + 1 + 1),
            (2 ^ (8 - (rem + 1) - 1 + i.val) : ℤ) *
              (2 * ((fmkSum9 a b ⟨8 - (rem + 1) + i.val, by omega⟩).val : ℤ) - 1)) =
          (2 ^ (k - 1) : ℤ) * (2 * ((fmkSum9 a b ⟨k, by omega⟩).val : ℤ) - 1) +
            ∑ x : Fin (rem + 1),
              (2 ^ (8 - rem - 1 + x.val) : ℤ) *
                (2 * ((fmkSum9 a b ⟨8 - rem + x.val, by omega⟩).val : ℤ) - 1) := by
        rw [Fin.sum_univ_succ]
        congr 1
        refine Finset.sum_congr rfl fun x _ ↦ ?_
        have h1 : 8 - (rem + 1) - 1 + x.succ.val = 8 - rem - 1 + x.val := by
          simp only [Fin.val_succ]; omega
        have h2 : (⟨8 - (rem + 1) + x.succ.val, by omega⟩ : Fin 9) = ⟨8 - rem + x.val, by omega⟩ :=
          Fin.ext (by simp only [Fin.val_succ]; omega)
        rw [h1, h2]
      rw [hout2, hRecEv hck_rec, hγ2_cat, hγ2_bank, fmkInt_add_emod, hStep1Ev, ← fmkInt_add_emod]
      apply congrArg (fun z : ℤ ↦ z.emod (2 ^ 36 : ℤ))
      change _ =
        (bitsVal (fun m ↦ γ (mk36Cat36W m)) : ℤ) +
          (∑ i : Fin (rem + 1 + 1),
            (2 ^ (8 - (rem + 1) - 1 + i.val) : ℤ) *
              (2 * ((fmkSum9 a b ⟨8 - (rem + 1) + i.val, by omega⟩).val : ℤ) - 1)) *
            (bitsVal (fun m ↦ γ (mk36Bank36W m)) : ℤ)
      rw [hrhs_sum]
      ring

attribute [local irreducible] mk36InterleavedU9Shift36

theorem mk36FlipP_disjoint36 (w : Fin 3) :
    (ctxCliffAlloc (mk36FlipP w)).DisjointFrom (fun q : Wire 411 ↦ 113 ≤ q.val ∧ q.val < 149) := by
  let mutCat36 : Wire 411 → Prop := fun q ↦ 113 ≤ q.val ∧ q.val < 149
  have hdVec : ∀ (n : ℕ) (qs : Fin n → Wire 411),
      (∀ j, ¬ mutCat36 (qs j)) → CliffDisjoint mutCat36 (fmkXVec n qs) := by
    intro n; induction n with
    | zero => intro _ _; trivial
    | succ n ih => intro qs hq; exact ⟨hq 0, ih _ (fun j ↦ hq j.succ)⟩
  have hw := w.isLt
  exact ctxCliffAlloc_disjoint ⟨by dsimp [CliffDisjoint, mk36FlipP, mutCat36, mk36PNewW]; omega,
    hdVec 7 _ (fun j ↦ by have := j.isLt; dsimp [mutCat36, mk36POldW]; omega)⟩

/-- Zero-`2a` interleaved `8 × 36 → 36` modular axis multiplier (`36 + 1 + 259 = 296` `TempAnd`s,
clean `[375..411)`), updating `mk36Cat36W` (`[113..149)`) and hence `mk36Cat42W` modulo `2 ^ 42`. -/
def mk36MulAxis36_no2a (w : Fin 3) : TempPhaseProg 411 :=
  let pNew0 := mk36PNewW w 0
  let pOld0 := mk36POldW w 0
  let c1W : Wire 411 := ⟨375, by decide⟩
  let part0 : TempPhaseProg 411 :=
    (ctxCliffAlloc (.cnot pOld0 pNew0 (mk36PNew_ne_pOld w 0).symm)).plug
      (mk36Step2b36_nodummy pNew0 ⟨by dsimp [pNew0, mk36PNewW]; omega, mk36PNew_lt339 w 0⟩)
  let part1 : TempPhaseProg 411 :=
    (ctxTempBit pNew0 pOld0 c1W (mk36PNew_ne_pOld w 0)
      (wire_ne_of_lt (by dsimp [pNew0, mk36PNewW, c1W]; omega))
      (wire_ne_of_lt (by dsimp [pOld0, mk36POldW, c1W]; omega))).plug
      (mk36InterleavedU9Shift36 w 7 le_rfl)
  (ctxCliffAlloc (mk36FlipP w)).plug (.seq part0 part1)

open Classical in
theorem mk36MulAxis36_no2a_spec (w : Fin 3) :
    (mk36MulAxis36_no2a w).countTempAnd = 296 ∧
      fmkIsMutBlock 411 (411 - 375) (fun q ↦ 107 ≤ q.val ∧ q.val < 149) (mk36MulAxis36_no2a w) ∧
      (∀ β : BitAssignment 411, cleanRem 411 (411 - 375) β →
        let pNew0 : Fin 256 :=
          ⟨bitsVal (fun b : Fin 8 ↦ β ⟨150 + 8 * w.val + b.val, by omega⟩), bitsVal_lt_two_pow _⟩
        let pOld0 : Fin 256 :=
          ⟨bitsVal (fun b : Fin 8 ↦ β ⟨8 * w.val + b.val, by omega⟩), bitsVal_lt_two_pow _⟩
        let K_val := bitsVal (fun m : Fin 36 ↦ β (mk36Bank36W m))
        ((bitsVal (fun m ↦
          (mk36MulAxis36_no2a w).evalBits β (mk36Cat42W m)) : ℤ)).emod (2 ^ 42 : ℤ) =
          ((bitsVal (fun m ↦ β (mk36Cat42W m)) : ℤ) +
            64 * ((twosComp8Int pNew0 - twosComp8Int pOld0) * (K_val : ℤ) -
              ((K_val / 2 : ℕ) : ℤ))).emod (2 ^ 42 : ℤ)) := by
  let mutCat : Wire 411 → Prop := fun q ↦ 107 ≤ q.val ∧ q.val < 149
  let mutCat36 : Wire 411 → Prop := fun q ↦ 113 ≤ q.val ∧ q.val < 149
  let pNew0W := mk36PNewW w 0
  let pOld0W := mk36POldW w 0
  let c1W : Wire 411 := ⟨375, by decide⟩
  obtain ⟨hCnt2b, hMut2b, hEv2b⟩ := mk36Step2b36_nodummy_spec pNew0W
    ⟨by dsimp [pNew0W, mk36PNewW]; omega, mk36PNew_lt339 w 0⟩
  let cXor0 : CliffProg 411 := .cnot pOld0W pNew0W (mk36PNew_ne_pOld w 0).symm
  have hdXor0 : (ctxCliffAlloc cXor0).DisjointFrom mutCat36 :=
    ctxCliffAlloc_disjoint ⟨by dsimp [mutCat36, pOld0W, mk36POldW]; omega,
      by dsimp [mutCat36, pNew0W, mk36PNewW]; omega⟩
  have hsXor0 : cXor0.SupportsBelow 375 :=
    ⟨by dsimp [pOld0W, mk36POldW]; omega, by dsimp [pNew0W, mk36PNewW]; omega⟩
  have hlXor0 : fmkTempCtxLiftEx 375 375 (ctxCliffAlloc cXor0) :=
    fmkTempCtxLiftEx_cliff (by decide) cXor0 hsXor0
  let part0 := (ctxCliffAlloc cXor0).plug (mk36Step2b36_nodummy pNew0W
    ⟨by dsimp [pNew0W, mk36PNewW]; omega, mk36PNew_lt339 w 0⟩)
  obtain ⟨hcP0, hMutP0, hXor0Cl, hbP0_pos⟩ := mk36_plug_mutBlock le_rfl
    (fun _ hw ht ↦ by dsimp [mutCat36] at ht; omega) (ctxCliffAlloc cXor0) hdXor0
    (ctxCliffAlloc_supports hsXor0) hlXor0 _ hMut2b.1 hMut2b.2.1 hMut2b.2.2.2
  obtain ⟨hCntSh, hMutSh, hEvSh⟩ := mk36InterleavedU9Shift36_spec w 7 le_rfl
  let Kc1 := ctxTempBit pNew0W pOld0W c1W (mk36PNew_ne_pOld w 0)
    (wire_ne_of_lt (by dsimp [pNew0W, mk36PNewW, c1W]; omega))
    (wire_ne_of_lt (by dsimp [pOld0W, mk36POldW, c1W]; omega))
  have hdC1 : Kc1.DisjointFrom mutCat36 :=
    ⟨by dsimp [mutCat36, pNew0W, mk36PNewW]; omega, by dsimp [mutCat36, pOld0W, mk36POldW]; omega,
      by dsimp [mutCat36, c1W]; omega, trivial⟩
  have hsC1 : Kc1.SupportsBelowCtx 376 := ⟨by dsimp [c1W]; omega, trivial⟩
  have hlC1 : fmkTempCtxLiftEx 375 376 Kc1 :=
    fmkTempCtxLiftEx_tempBit (cur := 375) (by decide) pNew0W pOld0W _
      (by dsimp [pNew0W, mk36PNewW]; omega) (by dsimp [pOld0W, mk36POldW]; omega)
  let part1 := Kc1.plug (mk36InterleavedU9Shift36 w 7 le_rfl)
  obtain ⟨hcP1, hMutP1, hC1Cl, hbP1_pos⟩ := mk36_plug_mutBlock (by decide)
    (fun _ hw ht ↦ by dsimp [mutCat36] at ht; omega) Kc1 hdC1 hsC1 hlC1 _
    hMutSh.1 hMutSh.2.1 hMutSh.2.2.2
  have hMutBody := fmkIsMutBlock_seq (by decide) hMutP0 hMutP1
  have hsFlip : (mk36FlipP w).SupportsBelow 375 :=
    CliffProg.supportsBelow_mono (b₁ := 174) (b₂ := 375) (by decide) (mk36FlipP_supportsBelow w)
  obtain ⟨hcOut, hMutOut36, hFlipCl, hbOut_pos⟩ := mk36_plug_mutBlock le_rfl
    (fun _ _ ht ↦ by omega) (ctxCliffAlloc (mk36FlipP w))
    (mk36FlipP_disjoint36 w) (ctxCliffAlloc_supports hsFlip)
    (fmkTempCtxLiftEx_cliff (by decide) (mk36FlipP w) hsFlip) (.seq part0 part1)
    hMutBody.1 hMutBody.2.1 hMutBody.2.2.2
  have hCnt296 : (mk36MulAxis36_no2a w).countTempAnd = 296 := by
    change ((ctxCliffAlloc (mk36FlipP w)).plug (.seq part0 part1)).countTempAnd = 296
    rw [hcOut]; change 0 + (part0.countTempAnd + part1.countTempAnd) = 296
    rw [hcP0, hcP1, hCnt2b, hCntSh]
    change 0 + ((0 + 36) + (1 + ((∑ i : Fin 8, (28 + i.val)) + 7))) = 296; decide
  have hNonOut36 : ∀ β, cleanRem 411 (411 - 375) β → ∀ q, ¬ mutCat36 q →
      (mk36MulAxis36_no2a w).evalBits β q = β q := hMutOut36.2.2.2
  refine ⟨hCnt296, ⟨hMutOut36.1, hMutOut36.2.1, hMutOut36.2.2.1,
    fun β hβ q hq ↦ hNonOut36 β hβ q (fun h ↦ hq ⟨by omega, h.2⟩)⟩, fun β hβ ↦ ?_⟩
  dsimp only
  let γ0 := (mk36FlipP w).eval β
  have hγ0_cl : cleanRem 411 (411 - 375) γ0 := hFlipCl β hβ
  have hout_cat36 : ∀ m : Fin 36,
      (mk36MulAxis36_no2a w).evalBits β (mk36Cat36W m) =
        part1.evalBits (part0.evalBits γ0) (mk36Cat36W m) :=
    fun m ↦ hbOut_pos β hβ _ (by dsimp [mutCat36, mk36Cat36W]; omega)
  have hγ0_cat : (fun m ↦ γ0 (mk36Cat36W m)) = fun m ↦ β (mk36Cat36W m) := funext fun m ↦ by
    dsimp [γ0, mk36FlipP, CliffProg.eval]
    rw [fmkXVec_eval 7 _ (fun i j h ↦ by
      have hv := congrArg Fin.val h; dsimp [mk36POldW] at hv; exact Fin.ext (by omega)),
      fmkIteNeg (by
        rintro ⟨j, hj⟩; have hv := congrArg Fin.val hj; dsimp [mk36Cat36W, mk36POldW] at hv; omega),
      Function.update_of_ne (wire_ne_of_lt (by dsimp [mk36Cat36W, mk36PNewW]; omega))]
  have hγ0_bank : (fun m ↦ γ0 (mk36Bank36W m)) = fun m ↦ β (mk36Bank36W m) := funext fun m ↦ by
    dsimp [γ0, mk36FlipP, CliffProg.eval]
    rw [fmkXVec_eval 7 _ (fun i j h ↦ by
      have hv := congrArg Fin.val h; dsimp [mk36POldW] at hv; exact Fin.ext (by omega)),
      fmkIteNeg (by
        rintro ⟨j, hj⟩; have hv := congrArg Fin.val hj; dsimp [mk36Bank36W, mk36POldW] at hv;
        omega),
      Function.update_of_ne (wire_ne_of_gt (by dsimp [mk36Bank36W, mk36PNewW]; omega))]
  let a : Fin 8 → ZMod 2 := fun b ↦ γ0 (mk36PNewW w b)
  let b : Fin 8 → ZMod 2 := fun b ↦ γ0 (mk36POldW w b)
  let γ0x := cXor0.eval γ0
  have hγ0x_cl : cleanRem 411 (411 - 375) γ0x := hXor0Cl γ0 hγ0_cl
  have hγ0x_cat : (fun m ↦ γ0x (mk36Cat36W m)) = fun m ↦ β (mk36Cat36W m) := funext fun m ↦ by
    dsimp [γ0x, cXor0, CliffProg.eval]
    rw [Function.update_of_ne (wire_ne_of_lt (by dsimp [mk36Cat36W, pNew0W, mk36PNewW]; omega))]
    exact congrFun hγ0_cat m
  have hγ0x_bank : (fun m ↦ γ0x (mk36Bank36W m)) = fun m ↦ β (mk36Bank36W m) := funext fun m ↦ by
    dsimp [γ0x, cXor0, CliffProg.eval]
    rw [Function.update_of_ne (wire_ne_of_gt (by dsimp [mk36Bank36W, pNew0W, mk36PNewW]; omega))]
    exact congrFun hγ0_bank m
  have hγ0x_u0 : γ0x pNew0W = fmkSum9 a b 0 := by
    dsimp [γ0x, cXor0, CliffProg.eval, fmkSum9, fmkCarryChain, a, b, pNew0W, pOld0W]
    rw [Function.update_self]
    ring
  let γ1 := part0.evalBits γ0
  have hγ1_cl : cleanRem 411 (411 - 375) γ1 := hMutP0.2.2.1 γ0 hγ0_cl
  have hP0Ev : ((bitsVal (fun m ↦ γ1 (mk36Cat36W m)) : ℤ)).emod (2 ^ 36 : ℤ) =
      ((bitsVal (fun m ↦ β (mk36Cat36W m)) : ℤ) +
        ((fmkSum9 a b 0).val : ℤ) * (bitsVal (fun m ↦ β (mk36Bank36W m)) : ℤ) -
        ((bitsVal (fun m ↦ β (mk36Bank36W m)) / 2 : ℕ) : ℤ)).emod (2 ^ 36 : ℤ) := by
    have hfn : (fun m ↦ γ1 (mk36Cat36W m)) =
        fun m ↦ (mk36Step2b36_nodummy pNew0W _).evalBits γ0x (mk36Cat36W m) :=
      funext fun m ↦ hbP0_pos γ0 hγ0_cl _ (by dsimp [mutCat36, mk36Cat36W]; omega)
    rw [hfn, hEv2b γ0x hγ0x_cl, hγ0x_cat, hγ0x_bank, hγ0x_u0]
  let γ2 := Kc1.fwdBits γ1
  have hγ2_cl : cleanRem 411 (411 - 376) γ2 := hC1Cl γ1 hγ1_cl
  have hγ1_non : ∀ q : Wire 411, ¬ mutCat36 q → γ1 q = γ0 q := hMutP0.2.2.2 γ0 hγ0_cl
  have hγ2_eq : γ2 = Function.update γ1 c1W (a 0 * b 0) := by
    dsimp only [γ2, Kc1, ctxTempBit, TempCtx.fwdBits]
    rw [hγ1_cl c1W (by decide), zero_add,
      hγ1_non pNew0W (by dsimp [mutCat36, pNew0W, mk36PNewW]; omega),
      hγ1_non pOld0W (by dsimp [mutCat36, pOld0W, mk36POldW]; omega)]
  have ha2 : (fun i : Fin 8 ↦ γ2 (mk36PNewW w i)) = a := funext fun i ↦ by
    rw [hγ2_eq, Function.update_of_ne (wire_ne_of_lt (by dsimp [mk36PNewW, c1W]; omega)),
      hγ1_non _ (by dsimp [mutCat36, mk36PNewW]; omega)]
  have hb2 : (fun i : Fin 8 ↦ γ2 (mk36POldW w i)) = b := funext fun i ↦ by
    rw [hγ2_eq, Function.update_of_ne (wire_ne_of_lt (by dsimp [mk36POldW, c1W]; omega)),
      hγ1_non _ (by dsimp [mutCat36, mk36POldW]; omega)]
  have hγ2_cat : (fun m ↦ γ2 (mk36Cat36W m)) = fun m ↦ γ1 (mk36Cat36W m) := funext fun m ↦ by
    rw [hγ2_eq, Function.update_of_ne (wire_ne_of_lt (by dsimp [mk36Cat36W, c1W]; omega))]
  have hγ2_bank : (fun m ↦ γ2 (mk36Bank36W m)) = fun m ↦ β (mk36Bank36W m) := funext fun m ↦ by
    rw [hγ2_eq, Function.update_of_ne (wire_ne_of_lt (by dsimp [mk36Bank36W, c1W]; omega)),
      hγ1_non _ (by dsimp [mutCat36, mk36Bank36W]; omega)]
    exact congrFun hγ0_bank m
  have hc1_eq : γ2 ⟨375 + (8 - 7) - 1, by decide⟩ = fmkCarryChain a b (8 - 7) := by
    have hw_eq : (⟨375 + (8 - 7) - 1, by decide⟩ : Wire 411) = c1W := rfl
    rw [hw_eq, hγ2_eq, Function.update_self]
    dsimp [fmkCarryChain]; simp
  have hout1 : (fun m ↦ part1.evalBits γ1 (mk36Cat36W m)) =
      fun m ↦ (mk36InterleavedU9Shift36 w 7 le_rfl).evalBits γ2 (mk36Cat36W m) :=
    funext fun m ↦ hbP1_pos γ1 hγ1_cl _ (by dsimp [mutCat36, mk36Cat36W]; omega)
  have hShEv := hEvSh γ2 hγ2_cl
  dsimp only at hShEv
  rw [ha2, hb2] at hShEv
  let pNewB : Fin 8 → ZMod 2 := fun i ↦ β ⟨150 + 8 * w.val + i.val, by omega⟩
  let pOldB : Fin 8 → ZMod 2 := fun i ↦ β ⟨8 * w.val + i.val, by omega⟩
  have ha_flip : a = fun i : Fin 8 ↦ if i.val = 7 then pNewB i + 1 else pNewB i := funext fun i ↦ by
    dsimp [a, γ0, mk36FlipP, CliffProg.eval, pNewB, mk36PNewW]
    rw [fmkXVec_eval 7 _ (fun x y h ↦ by
      have hv := congrArg Fin.val h; dsimp [mk36POldW] at hv; exact Fin.ext (by omega)),
      fmkIteNeg (by rintro ⟨j, hj⟩; have hv := congrArg Fin.val hj; dsimp [mk36POldW] at hv; omega)]
    by_cases hi7 : i.val = 7
    · have hi_eq : (⟨150 + 8 * w.val + i.val, by omega⟩ : Wire 411) =
          ⟨150 + 8 * w.val + 7, by omega⟩ := Fin.ext (by dsimp; omega)
      rw [fmkItePos hi7, hi_eq, Function.update_self]
    · rw [fmkIteNeg hi7, Function.update_of_ne (fun h ↦ hi7 (by
        have hv := congrArg Fin.val h; dsimp at hv; omega))]
  have hb_flip : b = fun i : Fin 8 ↦ if i.val < 7 then pOldB i + 1 else pOldB i := funext fun i ↦ by
    dsimp [b, γ0, mk36FlipP, CliffProg.eval, pOldB, mk36POldW]
    by_cases hi7 : i.val < 7
    · rw [fmkItePos hi7,
        fmkXVec_eval 7 _ (fun x y h ↦ by
          have hv := congrArg Fin.val h; dsimp [mk36POldW] at hv; exact Fin.ext (by omega)),
        fmkItePos ⟨⟨i.val, hi7⟩, Fin.ext (by dsimp)⟩,
        Function.update_of_ne (wire_ne_of_lt (by dsimp [mk36PNewW]; omega))]
    · rw [fmkIteNeg hi7,
        fmkXVec_eval 7 _ (fun x y h ↦ by
          have hv := congrArg Fin.val h; dsimp [mk36POldW] at hv; exact Fin.ext (by omega)),
        fmkIteNeg (by rintro ⟨j, hj⟩; have hv := congrArg Fin.val hj; dsimp at hv; omega),
        Function.update_of_ne (wire_ne_of_lt (by dsimp [mk36PNewW]; omega))]
  have hsum9 : bitsVal (fmkSum9 a b) =
      bitsVal (fun i : Fin 8 ↦ if i.val = 7 then pNewB i + 1 else pNewB i) +
      bitsVal (fun i : Fin 8 ↦ if i.val < 7 then pOldB i + 1 else pOldB i) := by
    rw [fmkBitsVal_sum9, ha_flip, hb_flip]
  have hDelta := fmkDeltaBitsAlgebra pNewB pOldB (fmkSum9 a b) hsum9
  dsimp only at hDelta
  have hsum_idx :
      (∑ i : Fin 8, (2 ^ (8 - 7 - 1 + i.val) : ℤ) *
        (2 * ((fmkSum9 a b ⟨8 - 7 + i.val, by omega⟩).val : ℤ) - 1)) =
      ∑ s : Fin 8, (2 ^ s.val : ℤ) * (2 * ((fmkSum9 a b s.succ).val : ℤ) - 1) := by
    refine Finset.sum_congr rfl fun s _ ↦ ?_
    have h1 : 8 - 7 - 1 + s.val = s.val := by omega
    have h2 : (⟨8 - 7 + s.val, by omega⟩ : Fin 9) = s.succ := Fin.ext (by dsimp; omega)
    rw [h1, h2]
  have h36_mod : ((bitsVal (fun m ↦ (mk36MulAxis36_no2a w).evalBits β (mk36Cat36W m)) :
      ℤ)).emod (2 ^ 36 : ℤ) = ((bitsVal (fun m ↦ β (mk36Cat36W m)) : ℤ) + ((twosComp8Int
      ⟨bitsVal pNewB, bitsVal_lt_two_pow _⟩ - twosComp8Int ⟨bitsVal pOldB, bitsVal_lt_two_pow
      _⟩) * (bitsVal (fun m ↦ β (mk36Bank36W m)) : ℤ) - ((bitsVal (fun m ↦ β (mk36Bank36W m))
      / 2 : ℕ) : ℤ))).emod (2 ^ 36 : ℤ) := by
    simp_rw [hout_cat36]
    rw [hout1, hShEv hc1_eq, hγ2_cat, hγ2_bank, hsum_idx, fmkInt_add_emod, hP0Ev, ← fmkInt_add_emod]
    apply congrArg (fun z : ℤ ↦ z.emod (2 ^ 36 : ℤ))
    rw [hDelta]
    ring
  have hlo6 : ∀ i : Fin 42,
    i.val < 6 → (mk36MulAxis36_no2a w).evalBits β (mk36Cat42W i) = β (mk36Cat42W i) :=
    fun i hi ↦ hNonOut36 β hβ (mk36Cat42W i) (by dsimp [mutCat36, mk36Cat42W]; omega)
  have hcat_hi : ∀ δ : BitAssignment 411,
      (fun j : Fin 36 ↦ δ (mk36Cat42W ⟨6 + j.val, by omega⟩)) = fun j : Fin 36 ↦ δ (mk36Cat36W j) :=
    fun δ ↦ funext fun j ↦ congrArg δ (mk36Cat36W_eq_cat42 j).symm
  exact mk36BitsVal_42_of_36_mod hlo6 (by rw [hcat_hi, hcat_hi]; exact h36_mod)

attribute [local irreducible] mk36MulAxis36_no2a

/-! ## Section 4: `36`-Bit Constant Bank Loader `mk36XorBank36_at339` (`56` `TempAnd`s, `K_h = 34`)
-/

/-- `36`-bit XOR-difference predicate `predD` for `mk36XorBitProg34` on bank `b1 ∈ {0, 1}`. -/
def mk36XorPredD (tTab : Fin 256 → ℕ) (j : Fin 36) (b1 p : ℕ) : Bool :=
  xor ((tTab (fmkIdx0 b1 p 0)).testBit j.val) ((tTab (fmkIdx0 b1 p 1)).testBit j.val)

/-- `36`-bit base predicate `predB0` for `mk36XorBitProg34` on bank `b1 ∈ {0, 1}`. -/
def mk36XorPredB (tTab : Fin 256 → ℕ) (j : Fin 36) (b1 p : ℕ) : Bool :=
  (tTab (fmkIdx0 b1 p 0)).testBit j.val

/-- Exact `GF(2)`-linear delta XORed onto `mk36Bank36W j` from `[250..338)` (`K_h = 34`). -/
def mk36XorDeltaBit34 (tTab : Fin 256 → ℕ) (j : Fin 36) (γ : BitAssignment 411) : ZMod 2 :=
  let b0 := γ ⟨91, by decide⟩
  let b1 := γ ⟨92, by decide⟩
  ∑ p : Fin 54,
    let v00 := fmkBitZ ((tTab (fmkIdx0 0 p.val 0)).testBit j.val)
    let v01 := fmkBitZ ((tTab (fmkIdx0 0 p.val 1)).testBit j.val)
    let v10 := fmkBitZ ((tTab (fmkIdx0 1 p.val 0)).testBit j.val)
    let v11 := fmkBitZ ((tTab (fmkIdx0 1 p.val 1)).testBit j.val)
    if p.val < 34 then
      γ ⟨250 + p.val, by omega⟩ * (v00 + b0 * (v00 + v01)) +
        γ ⟨304 + p.val, by omega⟩ * (v10 + b0 * (v10 + v11))
    else
      γ ⟨250 + p.val, by omega⟩ *
        ((1 + b1) * (v00 + b0 * (v00 + v01)) + b1 * (v10 + b0 * (v10 + v11)))

theorem mk36XorDeltaBit34_congr (tTab : Fin 256 → ℕ) (j : Fin 36)
    {γ₁ γ₂ : BitAssignment 411}
    (h91 : γ₁ ⟨91, by decide⟩ = γ₂ ⟨91, by decide⟩)
    (h92 : γ₁ ⟨92, by decide⟩ = γ₂ ⟨92, by decide⟩)
    (hu : ∀ w : Wire 411, 250 ≤ w.val → w.val < 338 → γ₁ w = γ₂ w) :
    mk36XorDeltaBit34 tTab j γ₁ = mk36XorDeltaBit34 tTab j γ₂ := by
  dsimp only [mk36XorDeltaBit34]
  rw [h91, h92]
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  by_cases hp : p.val < 34
  · rw [fmkItePos hp, fmkItePos hp,
      hu ⟨250 + p.val, by omega⟩ (by dsimp; omega) (by dsimp; omega),
      hu ⟨304 + p.val, by omega⟩ (by dsimp; omega) (by dsimp; omega)]
  · rw [fmkIteNeg hp, fmkIteNeg hp,
      hu ⟨250 + p.val, by omega⟩ (by dsimp; omega) (by dsimp; omega)]

open Classical in
theorem mk36XorDeltaBit34_of_unary88 (tTab : Fin 256 → ℕ) (j : Fin 36) (γ : BitAssignment 411)
    (g : ZMod 2) (p0 : ℕ) (hp0 : p0 < 54)
    (hpre : ∀ (p : ℕ) (hp : p < 34),
      γ ⟨250 + p, by omega⟩ = (1 + γ ⟨92, by decide⟩) * (g * (if p = p0 then 1 else 0)) ∧
      γ ⟨304 + p, by omega⟩ = γ ⟨92, by decide⟩ * (g * (if p = p0 then 1 else 0)))
    (hsuf : ∀ (p : ℕ), 34 ≤ p → (hp : p < 54) →
      γ ⟨250 + p, by omega⟩ = g * (if p = p0 then 1 else 0)) :
    mk36XorDeltaBit34 tTab j γ =
      g * fmkBitZ ((tTab (fmkIdx0 (γ ⟨92, by decide⟩).val p0 (γ ⟨91,
        by decide⟩).val)).testBit j.val) := by
  dsimp only [mk36XorDeltaBit34]
  rw [Finset.sum_eq_single ⟨p0, hp0⟩]
  · dsimp only
    have hmux :
        (1 + γ ⟨92, by decide⟩) *
          (fmkBitZ ((tTab (fmkIdx0 0 p0 0)).testBit j.val) +
            γ ⟨91, by decide⟩ * (fmkBitZ ((tTab (fmkIdx0 0 p0 0)).testBit j.val) +
              fmkBitZ ((tTab (fmkIdx0 0 p0 1)).testBit j.val))) +
        γ ⟨92, by decide⟩ *
          (fmkBitZ ((tTab (fmkIdx0 1 p0 0)).testBit j.val) +
            γ ⟨91, by decide⟩ * (fmkBitZ ((tTab (fmkIdx0 1 p0 0)).testBit j.val) +
              fmkBitZ ((tTab (fmkIdx0 1 p0 1)).testBit j.val))) =
        fmkBitZ ((tTab (fmkIdx0 (γ ⟨92, by decide⟩).val p0
          (γ ⟨91, by decide⟩).val)).testBit j.val) := by
      rcases fmkBit_cases (γ ⟨91, by decide⟩) with h0 | h0 <;>
        rcases fmkBit_cases (γ ⟨92, by decide⟩) with h1 | h1 <;>
        rw [h0, h1] <;>
        simp only [ZMod.val_zero, ZMod.val_one, zero_add, add_zero, zero_mul, one_mul,
          CharTwo.add_self_eq_zero]
      · simp only [← fmkBitZ_xor]
        cases (tTab (fmkIdx0 0 p0 0)).testBit j.val <;>
          cases (tTab (fmkIdx0 0 p0 1)).testBit j.val <;> simp [fmkBitZ]
      · simp only [← fmkBitZ_xor]
        cases (tTab (fmkIdx0 1 p0 0)).testBit j.val <;>
          cases (tTab (fmkIdx0 1 p0 1)).testBit j.val <;> simp [fmkBitZ]
    rw [← hmux]
    by_cases hp : p0 < 34
    · rw [fmkItePos hp, (hpre p0 hp).1, (hpre p0 hp).2, fmkItePos rfl, mul_one]
      ring
    · rw [fmkIteNeg hp, hsuf p0 (by omega) hp0, fmkItePos rfl, mul_one]
  · intro p _ hne
    have hp_ne : p.val ≠ p0 := fun h ↦ hne (Fin.ext h)
    by_cases hp : p.val < 34
    · rw [fmkItePos hp, (hpre p.val hp).1, (hpre p.val hp).2, fmkIteNeg hp_ne]
      ring
    · rw [fmkIteNeg hp, hsuf p.val (by omega) p.isLt, fmkIteNeg hp_ne, mul_zero, zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- Fanout of `mk36XorPredD` across `[250..304)`, `[304..338)`, and `[375..395)` onto `dst` (`dst
  ≥ 395`). -/
def mk36FanD34 (tTab : Fin 256 → ℕ) (j : Fin 36) (dst : Wire 411) (hdst : 395 ≤ dst.val) :
    CliffProg 411 := .seq (fmkFanoutUnary 250 dst (mk36XorPredD tTab j 0) 54 (by omega)) (.seq
    (fmkFanoutUnary 304 dst (mk36XorPredD tTab j 1) 34 (by omega)) (fmkFanoutUnary 375 dst
    (fun i ↦ mk36XorPredD tTab j 1 (34 + i)) 20 (by omega)))

/-- Fanout of `mk36XorPredB` across `[250..304)`, `[304..338)`, and `[375..395)` onto `outW =
  396`. -/
def mk36FanB34_out (tTab : Fin 256 → ℕ) (j : Fin 36) : CliffProg 411 :=
  let outW : Wire 411 := ⟨396, by decide⟩
  .seq (fmkFanoutUnary 250 outW (mk36XorPredB tTab j 0) 54 (by decide))
    (.seq (fmkFanoutUnary 304 outW (mk36XorPredB tTab j 1) 34 (by decide))
      (fmkFanoutUnary 375 outW (fun i ↦ mk36XorPredB tTab j 1 (34 + i)) 20 (by decide)))

open Classical in
theorem mk36FanD34_eval (tTab : Fin 256 → ℕ) (j : Fin 36) (dst : Wire 411) (hdst : 395 ≤ dst.val)
    (γ : BitAssignment 411) :
    (mk36FanD34 tTab j dst hdst).eval γ =
      Function.update γ dst
        (γ dst +
          ((∑ p : Fin 54, if mk36XorPredD tTab j 0 p.val then γ ⟨250 + p.val, by omega⟩ else 0) +
           (∑ p : Fin 34, if mk36XorPredD tTab j 1 p.val then γ ⟨304 + p.val, by omega⟩ else 0) +
           (∑ i : Fin 20, if mk36XorPredD tTab j 1 (34 + i.val) then γ ⟨375 + i.val,
             by omega⟩ else 0))) :=
  fmkThreeFan_eval_aux _ _ _ dst
    (fun δ ↦ ∑ p : Fin 54, if mk36XorPredD tTab j 0 p.val then δ ⟨250 + p.val, by omega⟩ else 0)
    (fun δ ↦ ∑ p : Fin 34, if mk36XorPredD tTab j 1 p.val then δ ⟨304 + p.val, by omega⟩ else 0)
    (fun δ ↦
      ∑ i : Fin 20, if mk36XorPredD tTab j 1 (34 + i.val) then δ ⟨375 + i.val, by omega⟩ else 0)
    (fmkFanoutUnary_eval 250 dst (mk36XorPredD tTab j 0) 54 _)
    (fmkFanoutUnary_eval 304 dst (mk36XorPredD tTab j 1) 34 _)
    (fmkFanoutUnary_eval 375 dst (fun i ↦ mk36XorPredD tTab j 1 (34 + i)) 20 _)
    (fun _ _ ↦ Finset.sum_congr rfl fun p _ ↦ by
      rw [Function.update_of_ne (wire_ne_of_lt (by dsimp; omega))])
    (fun _ _ ↦ Finset.sum_congr rfl fun i _ ↦ by
      rw [Function.update_of_ne (wire_ne_of_lt (by dsimp; omega))])
    γ

open Classical in
theorem mk36FanB34_out_eval (tTab : Fin 256 → ℕ) (j : Fin 36) (γ : BitAssignment 411) :
    let outW : Wire 411 := ⟨396, by decide⟩
    (mk36FanB34_out tTab j).eval γ =
      Function.update γ outW
        (γ outW +
          ((∑ p : Fin 54, if mk36XorPredB tTab j 0 p.val then γ ⟨250 + p.val, by omega⟩ else 0) +
           (∑ p : Fin 34, if mk36XorPredB tTab j 1 p.val then γ ⟨304 + p.val, by omega⟩ else 0) +
           (∑ i : Fin 20, if mk36XorPredB tTab j 1 (34 + i.val) then γ ⟨375 + i.val,
             by omega⟩ else 0))) :=
  fmkThreeFan_eval_aux _ _ _ ⟨396, by decide⟩
    (fun δ ↦ ∑ p : Fin 54, if mk36XorPredB tTab j 0 p.val then δ ⟨250 + p.val, by omega⟩ else 0)
    (fun δ ↦ ∑ p : Fin 34, if mk36XorPredB tTab j 1 p.val then δ ⟨304 + p.val, by omega⟩ else 0)
    (fun δ ↦
      ∑ i : Fin 20, if mk36XorPredB tTab j 1 (34 + i.val) then δ ⟨375 + i.val, by omega⟩ else 0)
    (fmkFanoutUnary_eval 250 ⟨396, by decide⟩ (mk36XorPredB tTab j 0) 54 _)
    (fmkFanoutUnary_eval 304 ⟨396, by decide⟩ (mk36XorPredB tTab j 1) 34 _)
    (fmkFanoutUnary_eval 375 ⟨396, by decide⟩ (fun i ↦ mk36XorPredB tTab j 1 (34 + i)) 20 _)
    (fun _ _ ↦ Finset.sum_congr rfl fun p _ ↦ by
      rw [Function.update_of_ne (wire_ne_of_lt (by dsimp; omega))])
    (fun _ _ ↦ Finset.sum_congr rfl fun i _ ↦ by
      rw [Function.update_of_ne (wire_ne_of_lt (by dsimp; omega))])
    γ

theorem mk36FanD34_disjoint {mutW : Wire 411 → Prop} (tTab : Fin 256 → ℕ) (j : Fin 36)
    (dst : Wire 411) (hdst : 395 ≤ dst.val) (hndst : ¬ mutW dst)
    (hnb : ∀ w : Wire 411, ¬(339 ≤ w.val ∧ w.val < 375) → ¬ mutW w) :
    CliffDisjoint mutW (mk36FanD34 tTab j dst hdst) :=
  ⟨fmkFanoutUnary_disjoint_len 250 dst _ hndst 54 (by omega) (fun w _ hw2 ↦ hnb w (by omega)),
   fmkFanoutUnary_disjoint_len 304 dst _ hndst 34 (by omega) (fun w _ hw2 ↦ hnb w (by omega)),
   fmkFanoutUnary_disjoint_len 375 dst _ hndst 20 (by omega) (fun w hw1 _ ↦ hnb w (by omega))⟩

theorem mk36FanD34_supportsBelow (tTab : Fin 256 → ℕ) (j : Fin 36) (dst : Wire 411)
    (hdst : 395 ≤ dst.val) (bnd : ℕ) (hbnd : dst.val < bnd) :
    (mk36FanD34 tTab j dst hdst).SupportsBelow bnd := ⟨fmkFanoutUnary_supportsBelow 250 dst _
    bnd hbnd 54 (by omega), fmkFanoutUnary_supportsBelow 304 dst _ bnd hbnd 34 (by omega),
    fmkFanoutUnary_supportsBelow 375 dst _ bnd hbnd 20 (by omega)⟩

theorem mk36FanB34_out_disjoint {mutW : Wire 411 → Prop} (tTab : Fin 256 → ℕ) (j : Fin 36)
    (hnb : ∀ w : Wire 411, ¬(339 ≤ w.val ∧ w.val < 375) → ¬ mutW w) :
    CliffDisjoint mutW (mk36FanB34_out tTab j) :=
  ⟨fmkFanoutUnary_disjoint_len 250 ⟨396, by decide⟩ _ (hnb _ (by decide)) 54 (by decide)
     (fun w _ hw2 ↦ hnb w (by omega)),
   fmkFanoutUnary_disjoint_len 304 ⟨396, by decide⟩ _ (hnb _ (by decide)) 34 (by decide)
     (fun w _ hw2 ↦ hnb w (by omega)),
   fmkFanoutUnary_disjoint_len 375 ⟨396, by decide⟩ _ (hnb _ (by decide)) 20 (by decide)
     (fun w hw1 _ ↦ hnb w (by omega))⟩

theorem mk36FanB34_out_supportsBelow (tTab : Fin 256 → ℕ) (j : Fin 36) :
    (mk36FanB34_out tTab j).SupportsBelow 397 :=
  ⟨fmkFanoutUnary_supportsBelow 250 ⟨396, by decide⟩ _ 397 (by decide) 54 (by decide),
   fmkFanoutUnary_supportsBelow 304 ⟨396, by decide⟩ _ 397 (by decide) 34 (by decide),
   fmkFanoutUnary_supportsBelow 375 ⟨396, by decide⟩ _ 397 (by decide) 20 (by decide)⟩

attribute [local irreducible] mk36FanD34 mk36FanB34_out

/-- Raw bit-`j` delta expression after `[284..304)` has been split onto `[375..395)`. -/
def mk36RawBit34 (tTab : Fin 256 → ℕ) (j : Fin 36) (γ : BitAssignment 411) : ZMod 2 :=
  γ ⟨91, by decide⟩ *
    ((∑ p : Fin 54, if mk36XorPredD tTab j 0 p.val then γ ⟨250 + p.val, by omega⟩ else 0) +
     (∑ p : Fin 34, if mk36XorPredD tTab j 1 p.val then γ ⟨304 + p.val, by omega⟩ else 0) +
     (∑ i : Fin 20, if mk36XorPredD tTab j 1 (34 + i.val) then γ ⟨375 + i.val, by omega⟩ else 0)) +
  ((∑ p : Fin 54, if mk36XorPredB tTab j 0 p.val then γ ⟨250 + p.val, by omega⟩ else 0) +
   (∑ p : Fin 34, if mk36XorPredB tTab j 1 p.val then γ ⟨304 + p.val, by omega⟩ else 0) +
   (∑ i : Fin 20, if mk36XorPredB tTab j 1 (34 + i.val) then γ ⟨375 + i.val, by omega⟩ else 0))

theorem mk36RawBit34_congr (tTab : Fin 256 → ℕ) (j : Fin 36) {γ₁ γ₂ : BitAssignment 411}
    (hnon : ∀ w : Wire 411, ¬(339 ≤ w.val ∧ w.val < 375) → γ₁ w = γ₂ w) : mk36RawBit34 tTab j
    γ₁ = mk36RawBit34 tTab j γ₂ := by
  dsimp only [mk36RawBit34]
  rw [hnon ⟨91, by decide⟩ (by decide)]
  refine congrArg₂ (· + ·) (congrArg (γ₂ ⟨91, by decide⟩ * ·)
    (congrArg₂ (· + ·) (congrArg₂ (· + ·) ?_ ?_) ?_))
    (congrArg₂ (· + ·) (congrArg₂ (· + ·) ?_ ?_) ?_) <;>
    exact Finset.sum_congr rfl fun _ _ ↦ by rw [hnon _ (by dsimp; omega)]

/-- Scoped `1`-`TempAnd` context on `[395..397)` computing lookup bit `j` on `outW = 396`. -/
def mk36XorBitCtx34 (tTab : Fin 256 → ℕ) (j : Fin 36) : TempCtx 411 :=
  let scrD : Wire 411 := ⟨395, by decide⟩
  let outW : Wire 411 := ⟨396, by decide⟩
  (ctxCliffAlloc (mk36FanD34 tTab j scrD le_rfl)).append
    ((ctxTempBit ⟨91, by decide⟩ scrD outW (by decide) (by decide) (by decide)).append
      (ctxCliffAlloc (.seq (mk36FanB34_out tTab j) (mk36FanD34 tTab j scrD le_rfl).inv)))

theorem mk36XorBitCtx34_def (tTab : Fin 256 → ℕ) (j : Fin 36) :
    mk36XorBitCtx34 tTab j =
      (ctxCliffAlloc (mk36FanD34 tTab j ⟨395, by decide⟩ le_rfl)).append
        ((ctxTempBit ⟨91, by decide⟩ ⟨395, by decide⟩ ⟨396, by decide⟩
            (by decide) (by decide) (by decide)).append
          (ctxCliffAlloc (.seq (mk36FanB34_out tTab j)
            (mk36FanD34 tTab j ⟨395, by decide⟩ le_rfl).inv))) := rfl

attribute [local irreducible] mk36XorBitCtx34

open Classical in
theorem mk36XorBitCtx34_spec (tTab : Fin 256 → ℕ) (j : Fin 36) :
    let mutJ : Wire 411 → Prop := fun w ↦ ∃ _ : Fin 1, w = mk36Bank36W j
    (mk36XorBitCtx34 tTab j).countTempAnd = 1 ∧
      (mk36XorBitCtx34 tTab j).DisjointFrom mutJ ∧
      (mk36XorBitCtx34 tTab j).SupportsBelowCtx 397 ∧
      fmkTempCtxLiftEx 395 397 (mk36XorBitCtx34 tTab j) ∧
      (∀ γ : BitAssignment 411, cleanRem 411 (411 - 395) γ →
        (mk36XorBitCtx34 tTab j).fwdBits γ ⟨396, by decide⟩ = mk36RawBit34 tTab j γ) := by
  intro mutJ
  let scrD : Wire 411 := ⟨395, by decide⟩
  let outW : Wire 411 := ⟨396, by decide⟩
  have hnbank : ∀ w : Wire 411, ¬(339 ≤ w.val ∧ w.val < 375) → ¬ mutJ w := by
    rintro w hw ⟨_, rfl⟩; dsimp [mk36Bank36W] at hw; omega
  have hdD : CliffDisjoint mutJ (mk36FanD34 tTab j scrD le_rfl) :=
    mk36FanD34_disjoint tTab j scrD le_rfl (hnbank scrD (by decide)) hnbank
  have hdB : CliffDisjoint mutJ (mk36FanB34_out tTab j) :=
    mk36FanB34_out_disjoint tTab j hnbank
  have hsD : (mk36FanD34 tTab j scrD le_rfl).SupportsBelow 396 :=
    mk36FanD34_supportsBelow tTab j scrD le_rfl 396 (by decide)
  have hsB : (mk36FanB34_out tTab j).SupportsBelow 397 := mk36FanB34_out_supportsBelow tTab j
  have hsInv : (mk36FanD34 tTab j scrD le_rfl).inv.SupportsBelow 397 :=
    CliffProg.inv_supportsBelow _
      (CliffProg.supportsBelow_mono (b₁ := 396) (b₂ := 397) (by decide) hsD)
  rw [mk36XorBitCtx34_def]
  refine ⟨fmkTwoCliffTemp_countTempAnd _ _ _ _ _ _ _ _,
    TempCtx.disjointFrom_append (ctxCliffAlloc_disjoint hdD)
      (TempCtx.disjointFrom_append
        ⟨hnbank ⟨91, by decide⟩ (by decide), hnbank scrD (by decide),
          hnbank outW (by decide), trivial⟩
        (ctxCliffAlloc_disjoint ⟨hdB, CliffDisjoint.inv hdD⟩)),
    TempCtx.supportsBelowCtx_append (c₁ := 396) (by decide) (ctxCliffAlloc_supports hsD)
      (TempCtx.supportsBelowCtx_append le_rfl ⟨by decide, trivial⟩
        (ctxCliffAlloc_supports ⟨hsB, hsInv⟩)),
    fmkTempCtxLiftEx_append
      (fmkTempCtxLiftEx_mono (cur₀ := 395) (cur₁ := 396) (next₀ := 396) (next₁ := 396)
        (by decide) le_rfl (by decide) (fmkTempCtxLiftEx_cliff (cur := 396) (by decide)
          (mk36FanD34 tTab j scrD le_rfl) hsD))
      (fmkTempCtxLiftEx_append
        (fmkTempCtxLiftEx_tempBit (cur := 396) (by decide) ⟨91, by decide⟩ scrD
          (by decide) (by decide) (by decide))
        (fmkTempCtxLiftEx_cliff (cur := 397) (by decide)
          (.seq (mk36FanB34_out tTab j) (mk36FanD34 tTab j scrD le_rfl).inv)
          ⟨hsB, hsInv⟩)),
    fun γ hγ ↦ ?_⟩
  refine fmkTwoCliffTemp_fwdBits_step (mk36FanD34 tTab j scrD le_rfl) (mk36FanB34_out tTab j)
    ⟨91, by decide⟩ scrD outW (by decide) (by decide) (by decide) γ
    (P := fun γ4 ↦ γ4 outW = mk36RawBit34 tTab j γ) ?_
  intro γ1 γ2 γ3 γ4 hγ1_def hγ2_def hγ3_def hγ4_def
  have hγ4_out : γ4 outW = γ3 outW := (congrFun hγ4_def.symm outW).trans
      (CliffProg.eval_outside (mk36FanD34 tTab j scrD le_rfl).inv (CliffProg.inv_supportsBelow
      _ hsD) γ3 outW (by decide))
  rw [hγ4_out, ← hγ3_def, mk36FanB34_out_eval tTab j γ2, Function.update_self]
  have hγ1_eq : γ1 = (mk36FanD34 tTab j scrD le_rfl).eval γ := hγ1_def.symm
  rw [mk36FanD34_eval tTab j scrD le_rfl γ] at hγ1_eq
  have hγ2_out : γ2 outW = γ ⟨91, by decide⟩ *
      ((∑ p : Fin 54, if mk36XorPredD tTab j 0 p.val then γ ⟨250 + p.val, by omega⟩ else 0) +
       (∑ p : Fin 34, if mk36XorPredD tTab j 1 p.val then γ ⟨304 + p.val, by omega⟩ else 0) +
       (∑ i : Fin 20, if mk36XorPredD tTab j 1 (34 + i.val) then γ ⟨375 + i.val,
         by omega⟩ else 0)) := by
    rw [← hγ2_def, Function.update_self, hγ1_eq,
      Function.update_of_ne (by decide : outW ≠ scrD),
      hγ outW (by decide), zero_add,
      Function.update_of_ne (wire_ne_of_lt (by dsimp [scrD]; decide)),
      Function.update_self, hγ scrD (by decide), zero_add]
  have hγ2_lt : ∀ w : Wire 411, w.val < 395 → γ2 w = γ w := fun w hw ↦ by
    rw [← hγ2_def, Function.update_of_ne (wire_ne_of_lt (by dsimp [outW]; omega)),
      hγ1_eq, Function.update_of_ne (wire_ne_of_lt (by dsimp [scrD]; omega))]
  rw [hγ2_out]
  dsimp only [mk36RawBit34]
  refine fmkAddCongr rfl (congrArg₂ (· + ·) (congrArg₂ (· + ·) ?_ ?_) ?_) <;>
    exact Finset.sum_congr rfl fun _ _ ↦ by rw [hγ2_lt _ (by dsimp; omega)]

/-- Single-bit `B = 2` lookup XORing bit `j` onto `mk36Bank36W j` (`1` `TempAnd`, clean
  `[395..397)`). -/
def mk36XorBitProg34 (tTab : Fin 256 → ℕ) (j : Fin 36) : TempPhaseProg 411 :=
  (mk36XorBitCtx34 tTab j).plug (.cliff (fmkCnotVec 1 (fun _ ↦ ⟨396, by decide⟩) (fun _ ↦
    mk36Bank36W j)
    (fun _ ↦ wire_ne_of_gt (by dsimp [mk36Bank36W]; omega))))

theorem mk36XorBitProg34_def (tTab : Fin 256 → ℕ) (j : Fin 36) :
    mk36XorBitProg34 tTab j =
      (mk36XorBitCtx34 tTab j).plug (.cliff (fmkCnotVec 1 (fun _ ↦ ⟨396, by decide⟩) (fun _ ↦
        mk36Bank36W j)
        (fun _ ↦ wire_ne_of_gt (by dsimp [mk36Bank36W]; omega)))) := rfl

attribute [local irreducible] mk36XorBitProg34

theorem mk36XorBitProg34_spec (tTab : Fin 256 → ℕ) (j : Fin 36) :
    (mk36XorBitProg34 tTab j).countTempAnd = 1 ∧ fmkIsMutBlock 411 (411 - 395)
    (fun w ↦ ∃ i : Fin 36, w = mk36Bank36W i) (mk36XorBitProg34 tTab j) ∧ (∀ γ : BitAssignment
    411, cleanRem 411 (411 - 395) γ → (∀ w : Wire 411, w ≠ mk36Bank36W j → (mk36XorBitProg34
    tTab j).evalBits γ w = γ w) ∧ (mk36XorBitProg34 tTab j).evalBits γ (mk36Bank36W j) = γ
    (mk36Bank36W j) + mk36RawBit34 tTab j γ) := by
  obtain ⟨hCnt1, hDisj, hSupp, hLift, hFwd⟩ := mk36XorBitCtx34_spec tTab j
  have hout_lt : ∀ _ : Fin 1, (mk36Bank36W j).val < 395 := fun _ ↦ by dsimp [mk36Bank36W]; omega
  have hsrc_ge : ∀ _ : Fin 1, 395 ≤ (⟨396, by decide⟩ : Wire 411).val := fun _ ↦ by decide
  obtain ⟨hVal, hCnt, hSgn, hBits⟩ := fmkXorBlock_of_ctx (M := 411) (curStart := 395) (curEnd :=
    397)
    (W := 1) (by omega) (by omega) (fun _ ↦ mk36Bank36W j) hout_lt
    (fun a b _ ↦ Subsingleton.elim a b) (fun _ ↦ ⟨396, by decide⟩) hsrc_ge
    (mk36XorBitCtx34 tTab j) hDisj hSupp (mk36XorBitCtx34 tTab j).fwdBits (fmkTempCtxLiftEx_probe
      hLift)
  have hProgEq : mk36XorBitProg34 tTab j =
      (mk36XorBitCtx34 tTab j).plug (.cliff (fmkCnotVec 1 (fun _ ↦ ⟨396, by decide⟩) (fun _ ↦
        mk36Bank36W j)
        (fun k ↦ wire_ne_of_gt (fmkLtLe (hout_lt k) (hsrc_ge k))))) :=
    (mk36XorBitProg34_def tTab j).trans (congrArg (mk36XorBitCtx34 tTab j).plug rfl)
  have hvOut : ValidCleanRem 411 (411 - 395) (mk36XorBitProg34 tTab j) :=
    fmkOfEq (P := ValidCleanRem 411 (411 - 395)) hProgEq hVal
  have hcOut : (mk36XorBitProg34 tTab j).countTempAnd = 1 :=
    fmkOfEq (P := fun z : TempPhaseProg 411 ↦ z.countTempAnd = 1) hProgEq (hCnt.trans hCnt1)
  have hsOut : ∀ β : BitAssignment 411, cleanRem 411 (411 - 395) β →
      (mk36XorBitProg34 tTab j).evalSign β = 0 :=
    fmkOfEq (P := fun z : TempPhaseProg 411 ↦ ∀ β, cleanRem 411 (411 - 395) β → z.evalSign β = 0)
      hProgEq hSgn
  have hNonJ : ∀ γ : BitAssignment 411, cleanRem 411 (411 - 395) γ →
      ∀ w : Wire 411, w ≠ mk36Bank36W j → (mk36XorBitProg34 tTab j).evalBits γ w = γ w := by
    intro γ hγ w hne
    exact fmkOfEq (P := fun z : TempPhaseProg 411 ↦ z.evalBits γ w = γ w) hProgEq
      (fmkEqTransDIteNeg (hBits γ hγ w) (fun ⟨_, hw⟩ ↦ hne hw))
  have hClJ : ∀ γ : BitAssignment 411, cleanRem 411 (411 - 395) γ →
      cleanRem 411 (411 - 395) ((mk36XorBitProg34 tTab j).evalBits γ) := fun γ hγ w hw ↦ by
    rw [hNonJ γ hγ w (wire_ne_of_gt (by dsimp [mk36Bank36W]; omega))]
    exact hγ w hw
  refine ⟨hcOut, ⟨hvOut, hsOut, hClJ, fun γ hγ w hnw ↦ hNonJ γ hγ w (fun h ↦ hnw ⟨j, h⟩)⟩, fun
    γ hγ ↦ ⟨hNonJ γ hγ, ?_⟩⟩
  have hex : ∃ _ : Fin 1, mk36Bank36W j = mk36Bank36W j := ⟨0, rfl⟩
  have hHit : (mk36XorBitProg34 tTab j).evalBits γ (mk36Bank36W j) =
      γ (mk36Bank36W j) + (mk36XorBitCtx34 tTab j).fwdBits γ ⟨396, by decide⟩ :=
    fmkOfEq (P := fun z : TempPhaseProg 411 ↦ z.evalBits γ (mk36Bank36W j) =
      γ (mk36Bank36W j) + (mk36XorBitCtx34 tTab j).fwdBits γ ⟨396, by decide⟩) hProgEq
      (fmkEqTransDItePos (hBits γ hγ (mk36Bank36W j)) hex)
  rw [hHit, hFwd γ hγ]

def mk36XorBitLoop34 (tTab : Fin 256 → ℕ) : (remJ : ℕ) → remJ ≤ 36 → TempPhaseProg 411
  | 0, _ => .nil
  | remJ + 1, hJ =>
      .seq (mk36XorBitProg34 tTab ⟨36 - (remJ + 1), by omega⟩)
        (mk36XorBitLoop34 tTab remJ (by omega))

open Classical in
theorem mk36XorBitLoop34_spec (tTab : Fin 256 → ℕ) : ∀ (remJ : ℕ) (hJ : remJ ≤ 36),
    (mk36XorBitLoop34 tTab remJ hJ).countTempAnd = remJ ∧ fmkIsMutBlock 411 (411 - 395)
    (fun w ↦ ∃ j : Fin 36, w = mk36Bank36W j) (mk36XorBitLoop34 tTab remJ hJ) ∧ (∀ γ :
    BitAssignment 411, cleanRem 411 (411 - 395) γ → ∀ j : Fin 36, (mk36XorBitLoop34 tTab remJ
    hJ).evalBits γ (mk36Bank36W j) = if 36 - remJ ≤ j.val then γ (mk36Bank36W j) +
    mk36RawBit34 tTab j γ else γ (mk36Bank36W j)) := by
  intro remJ
  induction remJ with
  | zero =>
      intro hJ
      exact ⟨rfl, ⟨trivial, fun _ _ ↦ rfl, fun _ hγ ↦ hγ, fun _ _ _ _ ↦ rfl⟩,
        fun γ _ j ↦ by rw [fmkIteNeg (by omega : ¬(36 ≤ j.val))]; rfl⟩
  | succ remJ ih =>
      intro hJ
      let j0 : Fin 36 := ⟨36 - (remJ + 1), by omega⟩
      obtain ⟨hCnt0, hMut0, hEv0⟩ := mk36XorBitProg34_spec tTab j0
      obtain ⟨hCntR, hMutR, hEvR⟩ := ih (by omega)
      refine ⟨by dsimp [mk36XorBitLoop34, TempPhaseProg.countTempAnd]; rw [hCnt0, hCntR]; omega,
        fmkIsMutBlock_seq (by decide) hMut0 hMutR, fun γ hγ j ↦ ?_⟩
      dsimp only [mk36XorBitLoop34, TempPhaseProg.evalBits]
      let γ1 := (mk36XorBitProg34 tTab j0).evalBits γ
      have hγ1_cl : cleanRem 411 (411 - 395) γ1 := hMut0.2.2.1 γ hγ
      rw [hEvR γ1 hγ1_cl j]
      have hraw_eq : mk36RawBit34 tTab j γ1 = mk36RawBit34 tTab j γ :=
        mk36RawBit34_congr tTab j fun w hw ↦ hMut0.2.2.2 γ hγ w
          (by rintro ⟨k, rfl⟩; dsimp [mk36Bank36W] at hw; omega)
      by_cases hj_eq : j = j0
      · subst hj_eq
        rw [fmkIteNeg (by dsimp [j0]; omega), fmkItePos (by dsimp [j0]; omega)]
        exact (hEv0 γ hγ).2
      · have hj_val_ne : j.val ≠ j0.val := fun h ↦ hj_eq (Fin.ext h)
        have hγ1_j : γ1 (mk36Bank36W j) = γ (mk36Bank36W j) :=
          (hEv0 γ hγ).1 _ (fun h ↦ hj_eq (mk36Bank36W_inj h))
        by_cases hj_gt : 36 - remJ ≤ j.val
        · rw [fmkItePos hj_gt, fmkItePos (by omega), hγ1_j, hraw_eq]
        · rw [fmkIteNeg hj_gt, fmkIteNeg (by dsimp [j0] at hj_val_ne; omega), hγ1_j]

attribute [local irreducible] mk36XorBitLoop34

theorem mk362_lt284 : (⟨92, by decide⟩ : Wire 411).val < 284 := by decide
theorem mk36Split20_gap : 284 + 20 ≤ 375 := by decide
theorem mk36Split20_dst : 375 + 20 ≤ 411 := by decide

/-- `20`-`TempAnd` split context splitting `[284..304)` onto `[375..395)` by `92`. -/
def mk36XorBank36Ctx20 : TempCtx 411 :=
  fmkCtxSplitPrefix 284 375 20 ⟨92, by decide⟩ mk362_lt284 mk36Split20_gap mk36Split20_dst 20 le_rfl

theorem mk36XorBank36Ctx20_def :
    mk36XorBank36Ctx20 =
      fmkCtxSplitPrefix 284 375 20 ⟨92,
        by decide⟩ mk362_lt284 mk36Split20_gap mk36Split20_dst 20 le_rfl := rfl

attribute [local irreducible] mk36XorBank36Ctx20

/-- `56`-`TempAnd` (`20 + 36`) bank XOR loader onto `bank36 = [339..375)` (clean `[375..397)`). -/
def mk36XorBank36_at339 (tTab : Fin 256 → ℕ) : TempPhaseProg 411 :=
  mk36XorBank36Ctx20.plug (mk36XorBitLoop34 tTab 36 le_rfl)

theorem mk36XorBank36_at339_def (tTab : Fin 256 → ℕ) :
    mk36XorBank36_at339 tTab = mk36XorBank36Ctx20.plug (mk36XorBitLoop34 tTab 36 le_rfl) := rfl

attribute [local irreducible] mk36XorBank36_at339

open Classical in
theorem mk36RawBit34_eq_xorDeltaBit34 (tTab : Fin 256 → ℕ) (j : Fin 36)
    (γ δ : BitAssignment 411)
    (hδ91 : δ ⟨91, by decide⟩ = γ ⟨91, by decide⟩)
    (hδ_pre : ∀ (p : ℕ) (hp : p < 34),
      δ ⟨250 + p, by omega⟩ = γ ⟨250 + p, by omega⟩ ∧
      δ ⟨304 + p, by omega⟩ = γ ⟨304 + p, by omega⟩)
    (hδ_suf : ∀ (i : ℕ) (hi : i < 20),
      δ ⟨284 + i, by omega⟩ = γ ⟨284 + i, by omega⟩ + γ ⟨284 + i, by omega⟩ * γ ⟨92, by decide⟩ ∧
      δ ⟨375 + i, by omega⟩ = γ ⟨284 + i, by omega⟩ * γ ⟨92, by decide⟩) :
    mk36RawBit34 tTab j δ = mk36XorDeltaBit34 tTab j γ := by
  dsimp only [mk36RawBit34, mk36XorDeltaBit34]
  rw [hδ91]
  have split54 : ∀ f : Fin 54 → ZMod 2,
      (∑ p : Fin 54, f p) =
        (∑ p : Fin 34, f ⟨p.val, by omega⟩) + (∑ i : Fin 20, f ⟨34 + i.val, by omega⟩) := by
    intro f
    rw [Fin.sum_univ_add (a := 34) (b := 20)]
    rfl
  rw [split54 (fun p ↦ if mk36XorPredD tTab j 0 p.val then δ ⟨250 + p.val, by omega⟩ else 0),
    split54 (fun p ↦ if mk36XorPredB tTab j 0 p.val then δ ⟨250 + p.val, by omega⟩ else 0),
    split54]
  have hRearr : ∀ (b0 a1 a2 a3 a4 b1 b2 b3 b4 : ZMod 2),
      b0 * ((a1 + a2) + a3 + a4) + ((b1 + b2) + b3 + b4) =
      (b0 * (a1 + a3) + (b1 + b3)) + (b0 * (a2 + a4) + (b2 + b4)) := by
    intro _ _ _ _ _ _ _ _ _
    ring
  rw [hRearr]
  refine congrArg₂ (· + ·) ?_ ?_
  · rw [mul_add, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ ↦ ?_
    dsimp only
    rw [fmkItePos p.isLt, (hδ_pre p.val p.isLt).1, (hδ_pre p.val p.isLt).2]
    dsimp only [mk36XorPredD, mk36XorPredB]
    rw [fmkIte_mul_bitZ, fmkIte_mul_bitZ, fmkIte_mul_bitZ, fmkIte_mul_bitZ,
      fmkBitZ_xor, fmkBitZ_xor]
    exact fmkXorTerm_pre _ _ _ _ _ _ _
  · rw [mul_add, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    dsimp only
    rw [fmkIteNeg (by omega : ¬(34 + i.val < 34))]
    have hw284 : (⟨250 + (34 + i.val), by omega⟩ : Wire 411) = ⟨284 + i.val, by omega⟩ :=
      Fin.ext (by dsimp; omega)
    rw [hw284, (hδ_suf i.val i.isLt).1, (hδ_suf i.val i.isLt).2]
    dsimp only [mk36XorPredD, mk36XorPredB]
    rw [fmkIte_mul_bitZ, fmkIte_mul_bitZ, fmkIte_mul_bitZ, fmkIte_mul_bitZ,
      fmkBitZ_xor, fmkBitZ_xor]
    exact fmkXorTerm_suf _ _ _ _ _ _ _

theorem mk36XorBank36_at339_spec (tTab : Fin 256 → ℕ) :
    (mk36XorBank36_at339 tTab).countTempAnd = 56 ∧ fmkIsMutBlock 411 (411 - 375)
    (fun w ↦ ∃ j : Fin 36, w = mk36Bank36W j) (mk36XorBank36_at339 tTab) ∧ (∀ γ :
    BitAssignment 411, cleanRem 411 (411 - 375) γ → ∀ j : Fin 36, (mk36XorBank36_at339
    tTab).evalBits γ (mk36Bank36W j) = γ (mk36Bank36W j) + mk36XorDeltaBit34 tTab j γ) := by
  let mutBank : Wire 411 → Prop := fun w ↦ ∃ j : Fin 36, w = mk36Bank36W j
  obtain ⟨hLCnt, hLMut, hLEv⟩ := mk36XorBitLoop34_spec tTab 36 le_rfl
  have hnbank : ∀ w : Wire 411, ¬(339 ≤ w.val ∧ w.val < 375) → ¬ mutBank w := by
    rintro w hw ⟨k, rfl⟩; dsimp [mk36Bank36W] at hw; omega
  obtain ⟨hd20, hs20⟩ := fmkCtxSplitPrefix_props (mutW := mutBank) 284 375 20 ⟨92, by decide⟩
    mk362_lt284 mk36Split20_gap mk36Split20_dst (hnbank ⟨92, by decide⟩ (by decide))
    (fun w _ hw2 ↦ hnbank w (by omega)) (fun w hw1 _ ↦ hnbank w (by omega)) 20 le_rfl
  obtain ⟨hl20, hSpec20⟩ := fmkCtxSplitPrefix_scoped (M := 411) 284 375 20 ⟨92, by decide⟩
    mk362_lt284 mk36Split20_gap mk36Split20_dst 20 le_rfl
  have hn20_0 : 20 - 20 = 0 := rfl
  have hn375_20 : 375 + 20 = 395 := rfl
  rw [hn375_20] at hs20
  rw [hn20_0, Nat.add_zero, hn375_20] at hl20 hSpec20
  rw [← mk36XorBank36Ctx20_def] at hd20 hs20 hl20 hSpec20
  obtain ⟨hCnt, hMutP, _, hbPos⟩ := mk36_plug_mutBlock (by decide)
    (fun w hw ↦ hnbank w (by omega)) mk36XorBank36Ctx20 hd20 hs20 hl20
    (mk36XorBitLoop34 tTab 36 le_rfl) hLMut.1 hLMut.2.1 hLMut.2.2.2
  have hCntCtx : mk36XorBank36Ctx20.countTempAnd = 20 := by
    rw [mk36XorBank36Ctx20_def]
    exact fmkCtxSplitPrefix_countTempAnd 284 375 20 _ _ _ _ 20 le_rfl
  rw [mk36XorBank36_at339_def]
  refine ⟨by rw [hCnt, hCntCtx, hLCnt], hMutP, fun γ hγ j ↦ ?_⟩
  rw [hbPos γ hγ _ ⟨j, rfl⟩]
  obtain ⟨hcl20, hsrc20, hdst20, hout20⟩ := hSpec20 γ hγ
  let δ := mk36XorBank36Ctx20.fwdBits γ
  rw [hLEv δ hcl20 j, fmkItePos (Nat.zero_le j.val)]
  have hδ_bank : δ (mk36Bank36W j) = γ (mk36Bank36W j) :=
    hout20 (mk36Bank36W j) (by dsimp [mk36Bank36W]; omega) (by dsimp [mk36Bank36W]; omega)
  rw [hδ_bank]
  refine fmkAddCongr rfl ?_
  exact mk36RawBit34_eq_xorDeltaBit34 tTab j γ δ
    (hout20 ⟨91, by decide⟩ (by decide) (by decide))
    (fun p hp ↦ ⟨hout20 ⟨250 + p, by omega⟩ (by dsimp; omega) (by dsimp; omega),
      hout20 ⟨304 + p, by omega⟩ (by dsimp; omega) (by dsimp; omega)⟩)
    (fun i hi ↦ ⟨hsrc20 i (Nat.zero_le _) hi, hdst20 i (Nat.zero_le _) hi⟩)

/-- Pure reference pass: load `tTab` onto `bank36 = [339..375)`, run `passProg` (mutating only
  `catTop42`), and uncompute `tTab` from `bank36`. -/
def mk36RefPass36_339 (tTab : Fin 256 → ℕ) (passProg : TempPhaseProg 411) : TempPhaseProg 411 :=
  .seq (mk36XorBank36_at339 tTab) (.seq passProg (mk36XorBank36_at339 tTab))

theorem mk36RefPass36_339_spec (tTab : Fin 256 → ℕ) (passProg : TempPhaseProg 411)
    (hPass : fmkIsMutBlock 411 (411 - 375) (fun w ↦ 107 ≤ w.val ∧ w.val < 149) passProg) :
    fmkIsMutBlock 411 (411 - 339) (fun w ↦
      107 ≤ w.val ∧ w.val < 149) (mk36RefPass36_339 tTab passProg) ∧
      (∀ γ : BitAssignment 411, cleanRem 411 (411 - 339) γ →
        let γLoaded := (mk36XorBank36_at339 tTab).evalBits γ
        (∀ j : Fin 36, γLoaded (mk36Bank36W j) = mk36XorDeltaBit34 tTab j γ) ∧
        (∀ w : Wire 411, ¬(339 ≤ w.val ∧ w.val < 375) → γLoaded w = γ w) ∧
        cleanRem 411 (411 - 375) γLoaded ∧
        (∀ m : Fin 42, (mk36RefPass36_339 tTab passProg).evalBits γ (mk36Cat42W m) =
          passProg.evalBits γLoaded (mk36Cat42W m))) := by
  let mutCat : Wire 411 → Prop := fun w ↦ 107 ≤ w.val ∧ w.val < 149
  let mutBank : Wire 411 → Prop := fun w ↦ ∃ j : Fin 36, w = mk36Bank36W j
  let mutBoth : Wire 411 → Prop := fun w ↦ mutCat w ∨ mutBank w
  obtain ⟨_, hMX, hEX⟩ := mk36XorBank36_at339_spec tTab
  have liftBank : fmkIsMutBlock 411 (411 - 375) mutBoth (mk36XorBank36_at339 tTab) :=
    ⟨hMX.1, hMX.2.1, hMX.2.2.1, fun γ hγ q hq ↦ hMX.2.2.2 γ hγ q (fun hb ↦ hq (.inr hb))⟩
  have liftCat : fmkIsMutBlock 411 (411 - 375) mutBoth passProg :=
    ⟨hPass.1, hPass.2.1, hPass.2.2.1, fun γ hγ q hq ↦ hPass.2.2.2 γ hγ q (fun hc ↦ hq (.inl hc))⟩
  have hMut375 := fmkIsMutBlock_seq (by
    decide) liftBank (fmkIsMutBlock_seq (by decide) liftCat liftBank)
  have hNon339 : ∀ γ : BitAssignment 411, cleanRem 411 (411 - 339) γ →
      ∀ q : Wire 411, ¬ mutCat q → (mk36RefPass36_339 tTab passProg).evalBits γ q = γ q := by
    intro γ hγ q hnq
    have hγ375 : cleanRem 411 (411 - 375) γ := cleanRem_anti (by decide) hγ
    by_cases hb : mutBank q
    · obtain ⟨j, rfl⟩ := hb
      dsimp only [mk36RefPass36_339, TempPhaseProg.evalBits]
      let γ1 := (mk36XorBank36_at339 tTab).evalBits γ
      have hγ1_cl : cleanRem 411 (411 - 375) γ1 := hMX.2.2.1 γ hγ375
      let γ2 := passProg.evalBits γ1
      have hγ2_cl : cleanRem 411 (411 - 375) γ2 := hPass.2.2.1 γ1 hγ1_cl
      rw [hEX γ2 hγ2_cl j]
      dsimp only [γ2]
      rw [hPass.2.2.2 γ1 hγ1_cl (mk36Bank36W j) (by dsimp [mutCat, mk36Bank36W]; omega)]
      dsimp only [γ1]
      rw [hEX γ hγ375 j]
      have hd_eq : mk36XorDeltaBit34 tTab j γ2 = mk36XorDeltaBit34 tTab j γ :=
        mk36XorDeltaBit34_congr tTab j
          ((hPass.2.2.2 γ1 hγ1_cl _ (by
            decide)).trans (hMX.2.2.2 γ hγ375 _ (by
            rintro ⟨k, hk⟩; have hv := congrArg Fin.val hk; dsimp [mk36Bank36W] at hv; omega)))
          ((hPass.2.2.2 γ1 hγ1_cl _ (by
            decide)).trans (hMX.2.2.2 γ hγ375 _ (by
            rintro ⟨k, hk⟩; have hv := congrArg Fin.val hk; dsimp [mk36Bank36W] at hv; omega)))
          (fun w h1 h2 ↦ (hPass.2.2.2 γ1 hγ1_cl w (by dsimp [mutCat]; omega)).trans
            (hMX.2.2.2 γ hγ375 w (by rintro ⟨k, rfl⟩; dsimp [mk36Bank36W] at h2; omega)))
      rw [hd_eq, fmkZmod2_add_self_cancel]
    · exact hMut375.2.2.2 γ hγ375 q (fun h ↦ h.elim hnq hb)
  refine ⟨⟨validCleanRem_mono (by decide) hMut375.1,
      fun γ hγ ↦ hMut375.2.1 γ (cleanRem_anti (by decide) hγ),
      fun γ hγ q hq ↦ by rw [hNon339 γ hγ q (by dsimp [mutCat]; omega)]; exact hγ q hq,
      hNon339⟩,
    fun γ hγ ↦ ?_⟩
  have hγ375 : cleanRem 411 (411 - 375) γ := cleanRem_anti (by decide) hγ
  let γ1 := (mk36XorBank36_at339 tTab).evalBits γ
  have hγ1_cl : cleanRem 411 (411 - 375) γ1 := hMX.2.2.1 γ hγ375
  let γ2 := passProg.evalBits γ1
  have hγ2_cl : cleanRem 411 (411 - 375) γ2 := hPass.2.2.1 γ1 hγ1_cl
  refine ⟨fun j ↦ ?_, fun w hw ↦ hMX.2.2.2 γ hγ375 w (by
    rintro ⟨k, rfl⟩; dsimp [mk36Bank36W] at hw; omega),
    hγ1_cl, fun m ↦ ?_⟩
  · show (mk36XorBank36_at339 tTab).evalBits γ (mk36Bank36W j) = _
    rw [hEX γ hγ375 j, hγ (mk36Bank36W j) (by dsimp [mk36Bank36W]; omega), zero_add]
  · dsimp only [mk36RefPass36_339, TempPhaseProg.evalBits]
    exact hMX.2.2.2 γ2 hγ2_cl (mk36Cat42W m)
      (by
        rintro ⟨k, hk⟩; have hv := congrArg Fin.val hk; dsimp [mk36Cat42W, mk36Bank36W] at hv;
        omega)

/-- Combined `36`-bit half-sum table `((t0 idx / 2) + (t1 idx / 2) + (t2 idx / 2)) % 2 ^ 36` for
  Pass 0. -/
def mk36HalfSum36 (t0 t1 t2 : Fin 256 → ℕ) (idx : Fin 256) : ℕ :=
  ((t0 idx / 2) + (t1 idx / 2) + (t2 idx / 2)) % 2 ^ 36

theorem mk36HalfSum36_lt (t0 t1 t2 : Fin 256 → ℕ) (idx : Fin 256) : mk36HalfSum36 t0 t1 t2 idx
    < 2 ^ 36 := Nat.mod_lt _ (by positivity)

/-- 4-pass inner reference program on `[339..411)` mutating only `catTop42`. -/
def mk36MidKickInner339_36 (t0 t1 t2 : Fin 256 → ℕ) : TempPhaseProg 411 := .seq
    (mk36RefPass36_339 (mk36HalfSum36 t0 t1 t2) mk36Add36Bank) (.seq (mk36RefPass36_339 t0
    (mk36MulAxis36_no2a 0)) (.seq (mk36RefPass36_339 t1 (mk36MulAxis36_no2a 1))
    (mk36RefPass36_339 t2 (mk36MulAxis36_no2a 2))))

theorem mk36MidKickInner339_36_mut (t0 t1 t2 : Fin 256 → ℕ) : fmkIsMutBlock 411 (411 - 339)
    (fun q : Wire 411 ↦ 107 ≤ q.val ∧ q.val < 149) (mk36MidKickInner339_36 t0 t1 t2) :=
    fmkIsMutBlock_seq (by decide) (mk36RefPass36_339_spec (mk36HalfSum36 t0 t1 t2)
    mk36Add36Bank mk36Add36Bank_spec.2.1).1 (fmkIsMutBlock_seq (by decide)
    (mk36RefPass36_339_spec t0 (mk36MulAxis36_no2a 0) (mk36MulAxis36_no2a_spec 0).2.1).1
    (fmkIsMutBlock_seq (by decide) (mk36RefPass36_339_spec t1 (mk36MulAxis36_no2a 1)
    (mk36MulAxis36_no2a_spec 1).2.1).1 (mk36RefPass36_339_spec t2 (mk36MulAxis36_no2a 2)
    (mk36MulAxis36_no2a_spec 2).2.1).1))

open Classical in
theorem mk36DeltaVal34_catC
    (β γ : BitAssignment 411)
    (hγ_lt250 : ∀ q : Wire 411, q.val < 250 → γ q = β q)
    (idx0 : Fin 256) (p0_idx : ℕ) (hp0_lt : p0_idx < 54)
    (hidx_eq : fmkIdx0 (β ⟨92, by decide⟩).val p0_idx (β ⟨91, by decide⟩).val = idx0)
    (hpre' : ∀ (p : ℕ) (hp : p < 34),
      γ ⟨250 + p, by omega⟩ = (1 + γ ⟨92,
        by decide⟩) * (β mk36AccW * (if p = p0_idx then 1 else 0)) ∧
      γ ⟨304 + p, by omega⟩ = γ ⟨92, by decide⟩ * (β mk36AccW * (if p = p0_idx then 1 else 0)))
    (hsuf' : ∀ (p : ℕ), 34 ≤ p → (hp : p < 54) →
      γ ⟨250 + p, by omega⟩ = β mk36AccW * (if p = p0_idx then 1 else 0))
    (δ : BitAssignment 411)
    (hδ_non : ∀ q : Wire 411, ¬(107 ≤ q.val ∧ q.val < 149) → δ q = γ q)
    (t : Fin 256 → ℕ) (ht : ∀ i, t i < 2 ^ 36)
    (δL : BitAssignment 411)
    (hδL : ∀ j : Fin 36, δL (mk36Bank36W j) = mk36XorDeltaBit34 t j δ) :
    bitsVal (fun j : Fin 36 ↦ δL (mk36Bank36W j)) = (β mk36AccW).val * t idx0 := by
  have hfn : (fun j : Fin 36 ↦ δL (mk36Bank36W j)) =
      fun j : Fin 36 ↦ β mk36AccW * fmkBitZ ((t idx0).testBit j.val) := funext fun j ↦ by
    rw [hδL j,
      mk36XorDeltaBit34_congr t j (hδ_non _ (by decide)) (hδ_non _ (by decide))
        (fun w h1 h2 ↦ hδ_non w (by omega)),
      mk36XorDeltaBit34_of_unary88 t j γ (β mk36AccW) p0_idx hp0_lt hpre' hsuf',
      hγ_lt250 ⟨92, by decide⟩ (by decide), hγ_lt250 ⟨91, by decide⟩ (by decide), hidx_eq]
  rw [hfn]
  rcases fmkBit_cases (β mk36AccW) with ha0 | ha1
  · simp only [ha0, zero_mul, ZMod.val_zero]; exact fmkBitsVal_zero 36
  · simp only [ha1, ZMod.val_one, one_mul]
    exact fmkBitsVal_eq_of_testBit _ _ (ht idx0) (fun _ ↦ rfl)

theorem mk36LoadedAdd_catC (P B : TempPhaseProg 411) (β γ δL : BitAssignment 411)
    (hγ_lt250 : ∀ q : Wire 411, q.val < 250 → γ q = β q) (kVal : ℕ) (hEA : ∀ δ : BitAssignment
    411, cleanRem 411 (411 - 375) δ → ((bitsVal (fun m ↦ B.evalBits δ (mk36Cat42W m)) :
    ℤ)).emod (2 ^ 42 : ℤ) = ((bitsVal (fun m ↦ δ (mk36Cat42W m)) : ℤ) + ((64 * bitsVal (fun m
    : Fin 36 ↦ δ (mk36Bank36W m)) : ℕ) : ℤ)).emod (2 ^ 42 : ℤ))
    (hK_val : bitsVal (fun m : Fin 36 ↦ δL (mk36Bank36W m)) = kVal)
    (hnonL : ∀ q : Wire 411, ¬(339 ≤ q.val ∧ q.val < 375) → δL q = γ q)
    (hclL : cleanRem 411 (411 - 375) δL) (hcatP : ∀ m : Fin 42, P.evalBits γ (mk36Cat42W m) =
    B.evalBits δL (mk36Cat42W m)) : ((bitsVal (fun m ↦ P.evalBits γ (mk36Cat42W m)) : ℤ)).emod
    (2 ^ 42 : ℤ) = ((bitsVal (fun m ↦ β (mk36Cat42W m)) : ℤ) + ((64 * kVal : ℕ) : ℤ)).emod
    (2 ^ 42 : ℤ) := by
  have hcat_L0 : (fun m ↦ δL (mk36Cat42W m)) = fun m ↦ β (mk36Cat42W m) := funext fun m ↦
    (hnonL _ (by dsimp [mk36Cat42W]; omega)).trans (hγ_lt250 _ (by dsimp [mk36Cat42W]; omega))
  have hfn : (fun m ↦ P.evalBits γ (mk36Cat42W m)) = fun m ↦ B.evalBits δL (mk36Cat42W m) :=
    funext hcatP
  rw [hfn, hEA δL hclL, hcat_L0, hK_val]

theorem mk36LoadedAxis_catC
    (w : Fin 3) (P B : TempPhaseProg 411) (β γ sIn δL : BitAssignment 411)
    (hγ_lt250 : ∀ q : Wire 411, q.val < 250 → γ q = β q)
    (hnIn : ∀ q : Wire 411, ¬(107 ≤ q.val ∧ q.val < 149) → sIn q = γ q)
    (pNew0 pOld0 : Fin 3 → Fin 256)
    (hpNew0 : pNew0 w =
      ⟨bitsVal (fun b : Fin 8 ↦ β ⟨150 + 8 * w.val + b.val, by omega⟩), bitsVal_lt_two_pow _⟩)
    (hpOld0 : pOld0 w =
      ⟨bitsVal (fun b : Fin 8 ↦ β ⟨8 * w.val + b.val, by omega⟩), bitsVal_lt_two_pow _⟩)
    (kVal : ℕ)
    (hEMW : ∀ δ : BitAssignment 411, cleanRem 411 (411 - 375) δ →
      let pN : Fin 256 :=
        ⟨bitsVal (fun b : Fin 8 ↦ δ ⟨150 + 8 * w.val + b.val, by omega⟩), bitsVal_lt_two_pow _⟩
      let pO : Fin 256 :=
        ⟨bitsVal (fun b : Fin 8 ↦ δ ⟨8 * w.val + b.val, by omega⟩), bitsVal_lt_two_pow _⟩
      let K_val := bitsVal (fun m : Fin 36 ↦ δ (mk36Bank36W m))
      ((bitsVal (fun m ↦ B.evalBits δ (mk36Cat42W m)) : ℤ)).emod (2 ^ 42 : ℤ) =
        ((bitsVal (fun m ↦ δ (mk36Cat42W m)) : ℤ) +
          64 * ((twosComp8Int pN - twosComp8Int pO) * (K_val : ℤ) -
            ((K_val / 2 : ℕ) : ℤ))).emod (2 ^ 42 : ℤ))
    (hKW : bitsVal (fun m : Fin 36 ↦ δL (mk36Bank36W m)) = kVal)
    (hnonLW : ∀ q : Wire 411, ¬(339 ≤ q.val ∧ q.val < 375) → δL q = sIn q)
    (hclLW : cleanRem 411 (411 - 375) δL)
    (hcatPW : ∀ m : Fin 42, P.evalBits sIn (mk36Cat42W m) = B.evalBits δL (mk36Cat42W m)) :
    ((bitsVal (fun m ↦ P.evalBits sIn (mk36Cat42W m)) : ℤ)).emod (2 ^ 42 : ℤ) =
      ((bitsVal (fun m ↦ sIn (mk36Cat42W m)) : ℤ) +
        64 * ((twosComp8Int (pNew0 w) - twosComp8Int (pOld0 w)) * (kVal : ℤ) -
          ((kVal / 2 : ℕ) : ℤ))).emod (2 ^ 42 : ℤ) := by
  have hcatLW : (fun m ↦ δL (mk36Cat42W m)) = fun m ↦ sIn (mk36Cat42W m) :=
    funext fun m ↦ hnonLW _ (by dsimp [mk36Cat42W]; omega)
  have hpNLW : (⟨bitsVal (fun b : Fin 8 ↦
    δL ⟨150 + 8 * w.val + b.val, by omega⟩), bitsVal_lt_two_pow _⟩ : Fin 256) =
      pNew0 w := (Fin.ext (congrArg bitsVal (funext fun b ↦
    (hnonLW _ (by
      dsimp; omega)).trans ((hnIn _ (by
      dsimp; omega)).trans (hγ_lt250 _ (by dsimp; omega)))))).trans hpNew0.symm
  have hpOLW : (⟨bitsVal (fun b : Fin 8 ↦
    δL ⟨8 * w.val + b.val, by omega⟩), bitsVal_lt_two_pow _⟩ : Fin 256) =
      pOld0 w := (Fin.ext (congrArg bitsVal (funext fun b ↦
    (hnonLW _ (by
      dsimp; omega)).trans ((hnIn _ (by
      dsimp; omega)).trans (hγ_lt250 _ (by dsimp; omega)))))).trans hpOld0.symm
  have hfn : (fun m ↦ P.evalBits sIn (mk36Cat42W m)) = fun m ↦ B.evalBits δL (mk36Cat42W m) :=
    funext hcatPW
  have hEv := hEMW δL hclLW
  dsimp only at hEv
  rw [hfn, hEv, hcatLW, hKW, hpNLW, hpOLW]

theorem mk36Seq4_catC
    (P0 P1 P2 P3 : TempPhaseProg 411)
    (t0 t1 t2 : Fin 256 → ℕ) (idx0 : Fin 256)
    (pNew0 pOld0 : Fin 3 → Fin 256)
    (β γ s1 s2 s3 s4 : BitAssignment 411)
    (hseq4 : ∀ m : Fin 42,
      (TempPhaseProg.seq P0 (.seq P1 (.seq P2 P3))).evalBits γ (mk36Cat42W m) = s4 (mk36Cat42W m))
    (hs1_ev : ((bitsVal (fun m ↦ s1 (mk36Cat42W m)) : ℤ)).emod (2 ^ 42 : ℤ) =
      ((bitsVal (fun m ↦ β (mk36Cat42W m)) : ℤ) +
        ((64 * ((β mk36AccW).val * mk36HalfSum36 t0 t1 t2 idx0) : ℕ) : ℤ)).emod (2 ^ 42 : ℤ))
    (hs2_ev : ((bitsVal (fun m ↦ s2 (mk36Cat42W m)) : ℤ)).emod (2 ^ 42 : ℤ) =
      ((bitsVal (fun m ↦ s1 (mk36Cat42W m)) : ℤ) +
        64 * ((twosComp8Int (pNew0 0) - twosComp8Int (pOld0 0)) * (((β mk36AccW).val *
          t0 idx0 : ℕ) : ℤ) -
          ((((β mk36AccW).val * t0 idx0) / 2 : ℕ) : ℤ))).emod (2 ^ 42 : ℤ))
    (hs3_ev : ((bitsVal (fun m ↦ s3 (mk36Cat42W m)) : ℤ)).emod (2 ^ 42 : ℤ) =
      ((bitsVal (fun m ↦ s2 (mk36Cat42W m)) : ℤ) +
        64 * ((twosComp8Int (pNew0 1) - twosComp8Int (pOld0 1)) * (((β mk36AccW).val *
          t1 idx0 : ℕ) : ℤ) -
          ((((β mk36AccW).val * t1 idx0) / 2 : ℕ) : ℤ))).emod (2 ^ 42 : ℤ))
    (hs4_ev : ((bitsVal (fun m ↦ s4 (mk36Cat42W m)) : ℤ)).emod (2 ^ 42 : ℤ) =
      ((bitsVal (fun m ↦ s3 (mk36Cat42W m)) : ℤ) +
        64 * ((twosComp8Int (pNew0 2) - twosComp8Int (pOld0 2)) * (((β mk36AccW).val *
          t2 idx0 : ℕ) : ℤ) -
          ((((β mk36AccW).val * t2 idx0) / 2 : ℕ) : ℤ))).emod (2 ^ 42 : ℤ)) :
    ((bitsVal (fun m ↦
      (TempPhaseProg.seq P0 (.seq P1 (.seq P2 P3))).evalBits γ (mk36Cat42W m)) : ℤ)).emod (2 ^ 42 :
      ℤ) =
      ((bitsVal (fun m ↦ β (mk36Cat42W m)) : ℤ) + ((β mk36AccW).val : ℤ) *
        ∑ w : Fin 3, (twosComp8Int (pNew0 w) - twosComp8Int (pOld0 w)) *
          (64 * (match w.val with
                | 0 => t0 idx0 | 1 => t1 idx0 | _ => t2 idx0 : ℤ))).emod (2 ^ 42 : ℤ) := by
  have hinner_eq : (fun m ↦
    (TempPhaseProg.seq P0 (.seq P1 (.seq P2 P3))).evalBits γ (mk36Cat42W m)) =
      fun m ↦ s4 (mk36Cat42W m) := funext hseq4
  rw [hinner_eq, fmkChain4_emod hs1_ev hs2_ev hs3_ev hs4_ev]
  have hsum3 : (∑ w : Fin 3, (twosComp8Int (pNew0 w) - twosComp8Int (pOld0 w)) *
        (64 * (match w.val with
                | 0 => t0 idx0 | 1 => t1 idx0 | _ => t2 idx0 : ℤ))) =
      64 * ((twosComp8Int (pNew0 0) - twosComp8Int (pOld0 0)) * (t0 idx0 : ℤ) +
        (twosComp8Int (pNew0 1) - twosComp8Int (pOld0 1)) * (t1 idx0 : ℤ) +
        (twosComp8Int (pNew0 2) - twosComp8Int (pOld0 2)) * (t2 idx0 : ℤ)) := by
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ, Finset.univ_eq_empty,
      Finset.sum_empty]
    dsimp; ring
  rw [hsum3]
  rcases fmkBit_cases (β mk36AccW) with hacc0 | hacc1
  · rw [hacc0]
    simp only [ZMod.val_zero, zero_mul, mul_zero, Nat.zero_div, Nat.cast_zero, sub_zero, add_zero]
  · simp only [hacc1, ZMod.val_one, Nat.cast_one, one_mul]
    dsimp only [mk36HalfSum36]
    set hsum := (t0 idx0 / 2) + (t1 idx0 / 2) + (t2 idx0 / 2)
    have hdiv_mod := Nat.div_add_mod hsum (2 ^ 36)
    set q := hsum / 2 ^ 36
    set r := hsum % 2 ^ 36
    set C0 := (bitsVal (fun m ↦ β (mk36Cat42W m)) : ℤ)
    set D0 := twosComp8Int (pNew0 0) - twosComp8Int (pOld0 0)
    set D1 := twosComp8Int (pNew0 1) - twosComp8Int (pOld0 1)
    set D2 := twosComp8Int (pNew0 2) - twosComp8Int (pOld0 2)
    have hrew : C0 + ((64 * r : ℕ) : ℤ) + 64 * (D0 * (t0 idx0 : ℤ) - ((t0 idx0 / 2 : ℕ) : ℤ))
        + 64 * (D1 * (t1 idx0 : ℤ) - ((t1 idx0 / 2 : ℕ) : ℤ)) + 64 *
        (D2 * (t2 idx0 : ℤ) - ((t2 idx0 / 2 : ℕ) : ℤ)) = (C0 + 64 * (D0 * (t0 idx0 : ℤ) + D1 *
        (t1 idx0 : ℤ) + D2 * (t2 idx0 : ℤ))) + (-(q : ℤ)) * (2 ^ 42 : ℤ) := by
      have hz : (2 ^ 36 : ℤ) * (q : ℤ) + (r : ℤ) =
          ((t0 idx0 / 2 : ℕ) : ℤ) + ((t1 idx0 / 2 : ℕ) : ℤ) + ((t2 idx0 / 2 : ℕ) : ℤ) := by
        exact_mod_cast hdiv_mod
      have hc : ((64 * r : ℕ) : ℤ) = 64 * (r : ℤ) := by push_cast; rfl
      rw [hc]
      linarith
    rw [hrew]
    exact Int.add_mul_emod_self_right _ _ _

open Classical in
theorem mk36MidKickInner339_36_eval_catC (t0 t1 t2 : Fin 256 → ℕ)
    (ht0 : ∀ i, t0 i < 2 ^ 36) (ht1 : ∀ i, t1 i < 2 ^ 36) (ht2 : ∀ i, t2 i < 2 ^ 36)
    (β γ : BitAssignment 411)
    (hcl72 : cleanRem 411 (411 - 339) γ)
    (hγ_lt250 : ∀ q : Wire 411, q.val < 250 → γ q = β q)
    (idx0 : Fin 256)
    (pNew0 pOld0 : Fin 3 → Fin 256)
    (hpNew0 : ∀ w : Fin 3, pNew0 w =
      ⟨bitsVal (fun b : Fin 8 ↦ β ⟨150 + 8 * w.val + b.val, by omega⟩), bitsVal_lt_two_pow _⟩)
    (hpOld0 : ∀ w : Fin 3, pOld0 w =
      ⟨bitsVal (fun b : Fin 8 ↦ β ⟨8 * w.val + b.val, by omega⟩), bitsVal_lt_two_pow _⟩)
    (p0_idx : ℕ) (hp0_lt : p0_idx < 54)
    (hidx_eq : fmkIdx0 (β ⟨92, by decide⟩).val p0_idx (β ⟨91, by decide⟩).val = idx0)
    (hpre' : ∀ (p : ℕ) (hp : p < 34),
      γ ⟨250 + p, by omega⟩ = (1 + γ ⟨92,
        by decide⟩) * (β mk36AccW * (if p = p0_idx then 1 else 0)) ∧
      γ ⟨304 + p, by omega⟩ = γ ⟨92, by decide⟩ * (β mk36AccW * (if p = p0_idx then 1 else 0)))
    (hsuf' : ∀ (p : ℕ), 34 ≤ p → (hp : p < 54) →
      γ ⟨250 + p, by omega⟩ = β mk36AccW * (if p = p0_idx then 1 else 0)) :
    ((bitsVal (fun m ↦
      (mk36MidKickInner339_36 t0 t1 t2).evalBits γ (mk36Cat42W m)) : ℤ)).emod (2 ^ 42 : ℤ) =
      ((bitsVal (fun m ↦ β (mk36Cat42W m)) : ℤ) + ((β mk36AccW).val : ℤ) *
        ∑ w : Fin 3, (twosComp8Int (pNew0 w) - twosComp8Int (pOld0 w)) *
          (64 * (match w.val with
                | 0 => t0 idx0 | 1 => t1 idx0 | _ => t2 idx0 : ℤ))).emod (2 ^ 42 : ℤ) := by
  obtain ⟨_, hMA, hEA⟩ := mk36Add36Bank_spec
  obtain ⟨_, hMM0, hEM0⟩ := mk36MulAxis36_no2a_spec 0
  obtain ⟨_, hMM1, hEM1⟩ := mk36MulAxis36_no2a_spec 1
  obtain ⟨_, hMM2, hEM2⟩ := mk36MulAxis36_no2a_spec 2
  obtain ⟨hMP0, hEP0⟩ := mk36RefPass36_339_spec (mk36HalfSum36 t0 t1 t2) mk36Add36Bank hMA
  obtain ⟨hMP1, hEP1⟩ := mk36RefPass36_339_spec t0 (mk36MulAxis36_no2a 0) hMM0
  obtain ⟨hMP2, hEP2⟩ := mk36RefPass36_339_spec t1 (mk36MulAxis36_no2a 1) hMM1
  obtain ⟨_, hEP3⟩ := mk36RefPass36_339_spec t2 (mk36MulAxis36_no2a 2) hMM2
  let s1 := (mk36RefPass36_339 (mk36HalfSum36 t0 t1 t2) mk36Add36Bank).evalBits γ
  let s2 := (mk36RefPass36_339 t0 (mk36MulAxis36_no2a 0)).evalBits s1
  let s3 := (mk36RefPass36_339 t1 (mk36MulAxis36_no2a 1)).evalBits s2
  let s4 := (mk36RefPass36_339 t2 (mk36MulAxis36_no2a 2)).evalBits s3
  have hc1 := hMP0.2.2.1 γ hcl72
  have hc2 := hMP1.2.2.1 s1 hc1
  have hc3 := hMP2.2.2.1 s2 hc2
  have hn1 := hMP0.2.2.2 γ hcl72
  have hn2 : ∀ q : Wire 411, ¬(107 ≤ q.val ∧ q.val < 149) → s2 q = γ q :=
    fun q hq ↦ (hMP1.2.2.2 s1 hc1 q hq).trans (hn1 q hq)
  have hn3 : ∀ q : Wire 411, ¬(107 ≤ q.val ∧ q.val < 149) → s3 q = γ q :=
    fun q hq ↦ (hMP2.2.2.2 s2 hc2 q hq).trans (hn2 q hq)
  obtain ⟨hbL0, hnonL0, hclL0, hcatP0⟩ := hEP0 γ hcl72
  obtain ⟨hbL1, hnonL1, hclL1, hcatP1⟩ := hEP1 s1 hc1
  obtain ⟨hbL2, hnonL2, hclL2, hcatP2⟩ := hEP2 s2 hc2
  obtain ⟨hbL3, hnonL3, hclL3, hcatP3⟩ := hEP3 s3 hc3
  exact mk36Seq4_catC _ _ _ _ t0 t1 t2 idx0 pNew0 pOld0 β γ s1 s2 s3 s4
    (fun m ↦ fmkSeq4_evalBits_apply _ _ _ _ γ (mk36Cat42W m)) (mk36LoadedAdd_catC _ _ β γ _
    hγ_lt250 _ hEA (mk36DeltaVal34_catC β γ hγ_lt250 idx0 p0_idx hp0_lt hidx_eq hpre' hsuf' γ
    (fun _ _ ↦ rfl) _ (mk36HalfSum36_lt t0 t1 t2) _ hbL0) hnonL0 hclL0 hcatP0)
    (mk36LoadedAxis_catC 0 _ _ β γ s1 _ hγ_lt250 hn1 pNew0 pOld0 (hpNew0 0) (hpOld0 0) _ hEM0
    (mk36DeltaVal34_catC β γ hγ_lt250 idx0 p0_idx hp0_lt hidx_eq hpre' hsuf' s1 hn1 t0 ht0 _
    hbL1) hnonL1 hclL1 hcatP1) (mk36LoadedAxis_catC 1 _ _ β γ s2 _ hγ_lt250 hn2 pNew0 pOld0
    (hpNew0 1) (hpOld0 1) _ hEM1 (mk36DeltaVal34_catC β γ hγ_lt250 idx0 p0_idx hp0_lt hidx_eq
    hpre' hsuf' s2 hn2 t1 ht1 _ hbL2) hnonL2 hclL2 hcatP2) (mk36LoadedAxis_catC 2 _ _ β γ s3 _
    hγ_lt250 hn3 pNew0 pOld0 (hpNew0 2) (hpOld0 2) _ hEM2 (mk36DeltaVal34_catC β γ hγ_lt250
    idx0 p0_idx hp0_lt hidx_eq hpre' hsuf' s3 hn3 t2 ht2 _ hbL3) hnonL3 hclL3 hcatP3)

/-! ## Section 5: Ternary `[250..339)` Context (`87 + 1` `TempAnd`s), X-Basis Fixup, & `4,940 T`
`161w` Circuit -/

open Classical in
/-- Two-step `fmkCtxSplitPrefix` ternary unary expansion on `[250 .. 250 + 3 * N)` (`2 * N`
  `TempAnd`s). -/
theorem mk36TernaryStep_fwd_250 (N : ℕ) (hdst : (250 + 2 * N) + N ≤ 411)
    (aW cW : Wire 411) (ha : aW.val < 250) (hc : cW.val < 250)
    (β : BitAssignment 411) (hβ : cleanRem 411 (411 - (250 + N)) β)
    (g : ZMod 2) (v_lo : ℕ) (hv_lt : v_lo < N)
    (h_in : ∀ k : ℕ, (hk : k < N) →
      β ⟨250 + k, by omega⟩ = g * (if k = v_lo then 1 else 0)) :
    let K₁ := fmkCtxSplitPrefix 250 (250 + N) N cW hc (by omega) (by omega) N le_rfl
    let K₂ := fmkCtxSplitPrefix 250 (250 + 2 * N) N aW ha (by omega) hdst N le_rfl
    let β₂ := K₂.fwdBits (K₁.fwdBits β)
    cleanRem 411 (411 - (250 + 3 * N)) β₂ ∧
      (∀ w : Wire 411, w.val < 250 → β₂ w = β w) ∧
      (∀ k : ℕ, (hk : k < 3 * N) →
        β₂ ⟨250 + k, by omega⟩ =
          g * (if k = v_lo + N * s3Trit (β aW) (β cW) then 1 else 0)) := by
  intro K₁ K₂ β₂
  obtain ⟨hcl1, hlt1, hu1⟩ := fmkSplitPrefix_unary_contiguous (M := 411) 250 N N cW
    hc le_rfl (by omega) β hβ g v_lo hv_lt (fun _ ↦ hv_lt) h_in
  let β₁ := K₁.fwdBits β
  have hu1' : ∀ (k : ℕ) (hk : k < N + N),
      β₁ ⟨250 + k, by omega⟩ = g * (if k = v_lo + N * (β cW).val then 1 else 0) := hu1
  have hβ₁_cl : cleanRem 411 (411 - ((250 + 2 * N) + (N - N))) β₁ :=
    fun w hw ↦ hcl1 w (by omega)
  obtain ⟨_, hSpec2⟩ := fmkCtxSplitPrefix_scoped (M := 411) 250 (250 + 2 * N) N aW
    ha (by omega) hdst N le_rfl
  obtain ⟨hcl2, hSrc2, hDst2, hOut2⟩ := hSpec2 β₁ hβ₁_cl
  have ha1 : β₁ aW = β aW := hlt1 aW ha
  refine ⟨fun w hw ↦ hcl2 w (by omega), fun w hw ↦ (hOut2 w (by omega) (by omega)).trans (hlt1
    w hw), fun k hk ↦ ?_⟩
  by_cases hk1 : k < N
  · change K₂.fwdBits β₁ ⟨250 + k, by omega⟩ = _
    rw [hSrc2 k (by omega) hk1, ha1, hu1' k (by omega)]
    rcases fmkBit_cases (β aW) with ha0 | ha1 <;> rcases fmkBit_cases (β cW) with hc0 | hc1
    · rw [ha0, hc0, s3Trit_00]; simp [ZMod.val_zero]
    · rw [ha0, hc1, s3Trit_01]; simp
    · rw [ha1, hc0, s3Trit_10]
      simp only [ZMod.val_zero, mul_zero, add_zero, mul_one, CharTwo.add_self_eq_zero]
      rw [fmkIteNeg (by omega : ¬(k = v_lo + N * 2)), mul_zero]
    · rw [ha1, hc1, s3Trit_11]
      simp only [ZMod.val_one, mul_one, CharTwo.add_self_eq_zero]
      rw [fmkIteNeg (by omega : ¬(k = v_lo + N)), mul_zero]
  · by_cases hk2 : k < 2 * N
    · change K₂.fwdBits β₁ ⟨250 + k, by omega⟩ = _
      rw [hOut2 ⟨250 + k, by omega⟩ (by dsimp; omega) (by dsimp; omega), hu1' k (by omega)]
      rcases fmkBit_cases (β aW) with ha0 | ha1 <;> rcases fmkBit_cases (β cW) with hc0 | hc1
      · rw [ha0, hc0, s3Trit_00]; simp [ZMod.val_zero]
      · rw [ha0, hc1, s3Trit_01]; simp
      · rw [ha1, hc0, s3Trit_10]
        simp only [ZMod.val_zero, mul_zero, add_zero]
        rw [fmkIteNeg (by omega : ¬(k = v_lo)), fmkIteNeg (by omega : ¬(k = v_lo + N * 2))]
      · rw [ha1, hc1, s3Trit_11]; simp
    · let i := k - 2 * N
      have hiN : i < N := by omega
      have hk_eq : (⟨250 + k, by omega⟩ : Wire 411) = ⟨(250 + 2 * N) + i, by omega⟩ :=
        Fin.ext (by dsimp [i]; omega)
      change K₂.fwdBits β₁ ⟨250 + k, by omega⟩ = _
      rw [hk_eq, hDst2 i (by omega) hiN, ha1, hu1' i (by omega)]
      rcases fmkBit_cases (β aW) with ha0 | ha1 <;> rcases fmkBit_cases (β cW) with hc0 | hc1
      · rw [ha0, hc0, s3Trit_00]
        simp only [ZMod.val_zero, mul_zero, add_zero]
        rw [fmkIteNeg (by omega : ¬(k = v_lo)), mul_zero]
      · rw [ha0, hc1, s3Trit_01]
        simp only [ZMod.val_one, mul_zero, mul_one]
        rw [fmkIteNeg (by omega : ¬(k = v_lo + N)), mul_zero]
      · rw [ha1, hc0, s3Trit_10]
        simp only [ZMod.val_zero, mul_zero, add_zero, mul_one]
        by_cases hiv : i = v_lo
        · rw [fmkItePos hiv, fmkItePos (by dsimp [i] at hiv; omega : k = v_lo + N * 2)]
        · rw [fmkIteNeg hiv, fmkIteNeg (by dsimp [i] at hiv; omega : ¬(k = v_lo + N * 2))]
      · rw [ha1, hc1, s3Trit_11]
        simp only [ZMod.val_one, mul_one]
        rw [fmkIteNeg (by omega : ¬(i = v_lo + N)), fmkIteNeg (by omega : ¬(k = v_lo + N))]

/-- Root-gated `54`-leaf ternary unary tree on `[250..304)` (`1+1+3+3+9+9+27 = 53` `TempAnd`s). -/
def mk36CtxUnary54Ternary_250 : TempCtx 411 :=
  (ctxCliffAlloc (.cnot mk36AccW ⟨250, by decide⟩ (by decide))).append
    ((fmkCtxSplitPrefix 250 251 1 (mk36U16W 3) (by decide) (by decide) (by decide) 1 le_rfl).append
      ((fmkCtxSplitPrefix 250 252 1 (mk36U16W 2) (by
        decide) (by decide) (by decide) 1 le_rfl).append
        ((fmkCtxSplitPrefix 250 253 3 (mk36U16W 5) (by
          decide) (by decide) (by decide) 3 le_rfl).append
          ((fmkCtxSplitPrefix 250 256 3 (mk36U16W 4) (by
            decide) (by decide) (by decide) 3 le_rfl).append
            ((fmkCtxSplitPrefix 250 259 9 (mk36U16W 7) (by
              decide) (by decide) (by decide) 9 le_rfl).append
              ((fmkCtxSplitPrefix 250 268 9 (mk36U16W 6) (by
                decide) (by decide) (by decide) 9 le_rfl).append
                (fmkCtxSplitPrefix 250 277 27 mk36BParW (by
                  decide) (by decide) (by decide) 27 le_rfl)))))))

private abbrev mk36CtxPkg (cur next : ℕ) (K : TempCtx 411) : Prop :=
  K.DisjointFrom (fun w ↦ 107 ≤ w.val ∧ w.val < 149) ∧
    K.SupportsBelowCtx next ∧ fmkTempCtxLiftEx cur next K

private theorem mk36CtxPkg_append {a b c : ℕ} {K₁ K₂ : TempCtx 411} (hbc : b ≤ c)
    (h₁ : mk36CtxPkg a b K₁) (h₂ : mk36CtxPkg b c K₂) :
    mk36CtxPkg a c (K₁.append K₂) :=
  ⟨TempCtx.disjointFrom_append h₁.1 h₂.1,
    TempCtx.supportsBelowCtx_append hbc h₁.2.1 h₂.2.1,
    fmkTempCtxLiftEx_append h₁.2.2 h₂.2.2⟩

private theorem mk36_splitPrefix_pkg (src dst W : ℕ) (ctrl : Wire 411)
    (hc : ctrl.val < src) (hgap : src + W ≤ dst) (hdst : dst + W ≤ 411)
    (hnc : ¬(107 ≤ ctrl.val ∧ ctrl.val < 149)) (hsrc : 250 ≤ src) :
    mk36CtxPkg dst (dst + W) (fmkCtxSplitPrefix src dst W ctrl hc hgap hdst W le_rfl) := by
  obtain ⟨hd, hs⟩ := fmkCtxSplitPrefix_props
    (mutW := fun w : Wire 411 ↦ 107 ≤ w.val ∧ w.val < 149)
    src dst W ctrl hc hgap hdst hnc (fun _ _ _ ↦ by omega) (fun _ _ _ ↦ by omega) W le_rfl
  obtain ⟨hl, _⟩ := fmkCtxSplitPrefix_scoped (M := 411) src dst W ctrl hc hgap hdst W le_rfl
  rw [Nat.sub_self] at hl
  exact ⟨hd, hs, hl⟩

theorem mk36CtxUnary54Ternary_250_props :
    let mutCat : Wire 411 → Prop := fun w ↦ 107 ≤ w.val ∧ w.val < 149
    mk36CtxUnary54Ternary_250.DisjointFrom mutCat ∧
      mk36CtxUnary54Ternary_250.SupportsBelowCtx 304 ∧
      fmkTempCtxLiftEx 250 304 mk36CtxUnary54Ternary_250 := by
  intro mutCat
  have hn_u16 : ∀ i : Fin 16, ¬ mutCat (mk36U16W i) := fun i hc ↦ by
    dsimp [mutCat, mk36U16W] at hc
    omega
  have hp0 : mk36CtxPkg 250 251
      (ctxCliffAlloc (.cnot mk36AccW ⟨250, by decide⟩ (by decide))) :=
    ⟨ctxCliffAlloc_disjoint ⟨by decide, by decide⟩,
      ctxCliffAlloc_supports ⟨by decide, by decide⟩,
      fmkTempCtxLiftEx_mono (cur₀ := 250) (cur₁ := 251) (next₀ := 251) (next₁ := 251)
        (by decide) le_rfl (by decide)
        (fmkTempCtxLiftEx_cliff (cur := 251) (by decide)
          (.cnot mk36AccW ⟨250, by decide⟩ (by decide)) ⟨by decide, by decide⟩)⟩
  exact mk36CtxPkg_append (by decide) hp0
    (mk36CtxPkg_append (by decide)
      (mk36_splitPrefix_pkg 250 251 1 (mk36U16W 3)
        (by decide) (by decide) (by decide) (hn_u16 3) le_rfl)
      (mk36CtxPkg_append (by decide)
        (mk36_splitPrefix_pkg 250 252 1 (mk36U16W 2)
          (by decide) (by decide) (by decide) (hn_u16 2) le_rfl)
        (mk36CtxPkg_append (by decide)
          (mk36_splitPrefix_pkg 250 253 3 (mk36U16W 5)
            (by decide) (by decide) (by decide) (hn_u16 5) le_rfl)
          (mk36CtxPkg_append (by decide)
            (mk36_splitPrefix_pkg 250 256 3 (mk36U16W 4)
              (by decide) (by decide) (by decide) (hn_u16 4) le_rfl)
            (mk36CtxPkg_append (by decide)
              (mk36_splitPrefix_pkg 250 259 9 (mk36U16W 7)
                (by decide) (by decide) (by decide) (hn_u16 7) le_rfl)
              (mk36CtxPkg_append (by decide)
                (mk36_splitPrefix_pkg 250 268 9 (mk36U16W 6)
                  (by decide) (by decide) (by decide) (hn_u16 6) le_rfl)
                (mk36_splitPrefix_pkg 250 277 27 mk36BParW
                  (by decide) (by decide) (by decide) (by decide) le_rfl)))))))

open Classical in
theorem mk36CtxUnary54Ternary_250_fwd (β : BitAssignment 411)
    (hβ : cleanRem 411 (411 - 250) β) :
    cleanRem 411 (411 - 304) (mk36CtxUnary54Ternary_250.fwdBits β) ∧
      (∀ w : Wire 411, w.val < 250 → mk36CtxUnary54Ternary_250.fwdBits β w = β w) ∧
      (∀ p : ℕ, (hp : p < 54) →
        mk36CtxUnary54Ternary_250.fwdBits β ⟨250 + p, by omega⟩ =
          β mk36AccW * (if p = s3NucleusQ27 (fun i ↦
            β (mk36U16W i)) + 27 * (β mk36BParW).val then 1 else 0)) := by
  let β0 := (ctxCliffAlloc (.cnot mk36AccW ⟨250, by decide⟩ (by decide))).fwdBits β
  have hβ0_cl : cleanRem 411 (411 - 251) β0 := fun w hw ↦ by
    dsimp [β0, ctxCliffAlloc, TempCtx.fwdBits, CliffProg.eval]
    rw [Function.update_of_ne (wire_ne_of_gt (by dsimp; omega))]
    exact hβ w (by omega)
  have hβ0_lt : ∀ w : Wire 411, w.val < 250 → β0 w = β w := fun w hw ↦ by
    dsimp [β0, ctxCliffAlloc, TempCtx.fwdBits, CliffProg.eval]
    exact Function.update_of_ne (wire_ne_of_lt hw) _ _
  have hβ0_u : ∀ k : ℕ, (hk : k < 1) → β0 ⟨250 + k,
    by omega⟩ = β mk36AccW * (if k = 0 then 1 else 0) := by
    intro k hk
    have hk0 : k = 0 := by omega
    subst hk0
    have hw_eq : (⟨250 + 0, by omega⟩ : Wire 411) = ⟨250, by decide⟩ := rfl
    rw [hw_eq]
    dsimp only [β0, ctxCliffAlloc, TempCtx.fwdBits, CliffProg.eval]
    rw [Function.update_self, hβ ⟨250, by decide⟩ (by decide), zero_add, fmkItePos rfl, mul_one]
  obtain ⟨hcl1, hlt1, hu1⟩ := mk36TernaryStep_fwd_250 1 (by decide) (mk36U16W 2) (mk36U16W 3)
    (by decide) (by decide) β0 hβ0_cl (β mk36AccW) 0 (by decide) hβ0_u
  let β1 := (fmkCtxSplitPrefix 250 252 1 (mk36U16W 2) (by
    decide) (by decide) (by decide) 1 le_rfl).fwdBits
    ((fmkCtxSplitPrefix 250 251 1 (mk36U16W 3) (by
      decide) (by decide) (by decide) 1 le_rfl).fwdBits β0)
  have hlt1' : ∀ w : Wire 411, w.val < 250 → β1 w = β0 w := hlt1
  have ht0_eq : 0 + 1 * s3Trit (β0 (mk36U16W 2)) (β0 (mk36U16W 3)) =
      s3Trit (β (mk36U16W 2)) (β (mk36U16W 3)) := by
    rw [hβ0_lt (mk36U16W 2) (by decide), hβ0_lt (mk36U16W 3) (by decide)]; omega
  have hu1' : ∀ k : ℕ, (hk : k < 3) →
      β1 ⟨250 + k,
        by omega⟩ = β mk36AccW * (if k = s3Trit (β (mk36U16W 2)) (β (mk36U16W 3)) then 1 else 0) :=
        by
    intro k hk; rw [← ht0_eq]; exact hu1 k hk
  obtain ⟨hcl2, hlt2, hu2⟩ := mk36TernaryStep_fwd_250 3 (by decide) (mk36U16W 4) (mk36U16W 5)
    (by decide) (by decide) β1 hcl1 (β mk36AccW)
    (s3Trit (β (mk36U16W 2)) (β (mk36U16W 3))) (s3Trit_lt_three _ _) hu1'
  let β2 := (fmkCtxSplitPrefix 250 256 3 (mk36U16W 4) (by
    decide) (by decide) (by decide) 3 le_rfl).fwdBits
    ((fmkCtxSplitPrefix 250 253 3 (mk36U16W 5) (by
      decide) (by decide) (by decide) 3 le_rfl).fwdBits β1)
  have hlt2' : ∀ w : Wire 411, w.val < 250 → β2 w = β1 w := hlt2
  have ht1_eq : s3Trit (β (mk36U16W 2)) (β (mk36U16W 3)) + 3 *
    s3Trit (β1 (mk36U16W 4)) (β1 (mk36U16W 5)) =
      s3Trit (β (mk36U16W 2)) (β (mk36U16W 3)) + 3 * s3Trit (β (mk36U16W 4)) (β (mk36U16W 5)) := by
    rw [hlt1' (mk36U16W 4) (by decide), hβ0_lt (mk36U16W 4) (by decide),
      hlt1' (mk36U16W 5) (by decide), hβ0_lt (mk36U16W 5) (by decide)]
  have hu2' : ∀ k : ℕ, (hk : k < 9) →
      β2 ⟨250 + k, by omega⟩ = β mk36AccW *
        (if k = s3Trit (β (mk36U16W 2)) (β (mk36U16W 3)) + 3 *
          s3Trit (β (mk36U16W 4)) (β (mk36U16W 5)) then 1 else 0) := by
    intro k hk; rw [← ht1_eq]; exact hu2 k hk
  obtain ⟨hcl3, hlt3, hu3⟩ := mk36TernaryStep_fwd_250 9 (by decide) (mk36U16W 6) (mk36U16W 7)
    (by decide) (by decide) β2 hcl2 (β mk36AccW)
    (s3Trit (β (mk36U16W 2)) (β (mk36U16W 3)) + 3 * s3Trit (β (mk36U16W 4)) (β (mk36U16W 5)))
    (by have := s3Trit_lt_three (β (mk36U16W 2)) (β (mk36U16W 3))
        have := s3Trit_lt_three (β (mk36U16W 4)) (β (mk36U16W 5)); omega)
    hu2'
  let β3 := (fmkCtxSplitPrefix 250 268 9 (mk36U16W 6) (by
    decide) (by decide) (by decide) 9 le_rfl).fwdBits
    ((fmkCtxSplitPrefix 250 259 9 (mk36U16W 7) (by
      decide) (by decide) (by decide) 9 le_rfl).fwdBits β2)
  have hlt3' : ∀ w : Wire 411, w.val < 250 → β3 w = β2 w := hlt3
  have ht2_eq : s3Trit (β (mk36U16W 2)) (β (mk36U16W 3)) + 3 *
    s3Trit (β (mk36U16W 4)) (β (mk36U16W 5)) +
      9 * s3Trit (β2 (mk36U16W 6)) (β2 (mk36U16W 7)) = s3NucleusQ27 (fun i ↦ β (mk36U16W i)) := by
    rw [hlt2' (mk36U16W 6) (by
      decide), hlt1' (mk36U16W 6) (by decide), hβ0_lt (mk36U16W 6) (by decide),
      hlt2' (mk36U16W 7) (by
        decide), hlt1' (mk36U16W 7) (by decide), hβ0_lt (mk36U16W 7) (by decide)]
    rfl
  have hu3' : ∀ k : ℕ, (hk : k < 27) →
      β3 ⟨250 + k, by omega⟩ = β mk36AccW * (if k = s3NucleusQ27 (fun i ↦
        β (mk36U16W i)) then 1 else 0) := by
    intro k hk; rw [← ht2_eq]; exact hu3 k hk
  obtain ⟨hcl4, hlt4, hu4⟩ := fmkSplitPrefix_unary_contiguous (M := 411) 250 27 27 mk36BParW
    (by decide) le_rfl (by decide) β3 hcl3 (β mk36AccW)
    (s3NucleusQ27 (fun i ↦ β (mk36U16W i)))
    (s3NucleusQ27_lt _) (fun _ ↦ s3NucleusQ27_lt _) hu3'
  have hbpar3 : β3 mk36BParW = β mk36BParW :=
    (hlt3 _ (by
      decide)).trans ((hlt2 _ (by
      decide)).trans ((hlt1 _ (by decide)).trans (hβ0_lt _ (by decide))))
  have hfwd_eq : mk36CtxUnary54Ternary_250.fwdBits β =
      (fmkCtxSplitPrefix 250 277 27 mk36BParW (by
        decide) (by decide) (by decide) 27 le_rfl).fwdBits β3 := by
    dsimp only [mk36CtxUnary54Ternary_250, β0, β1, β2, β3]
    repeat rw [fmkAppend_fwdBits]
  rw [hfwd_eq]
  refine ⟨hcl4, fun w hw ↦ (hlt4 w hw).trans ((hlt3 w hw).trans ((hlt2 w hw).trans ((hlt1 w
    hw).trans (hβ0_lt w hw)))), fun p hp ↦ ?_⟩
  rw [hu4 p hp, hbpar3]

/-- Persistent `87`-`TempAnd` ternary unary + `34`-wire `b1`-split context on `[250..338)` (`53 +
  34 = 87` `TempAnd`s). -/
def mk36CtxUnary87Ternary : TempCtx 411 :=
  mk36CtxUnary54Ternary_250.append
    (fmkCtxSplitPrefix 250 304 34 ⟨92, by decide⟩ (by decide) (by decide) (by decide) 34 le_rfl)

/-- Persistent `88`-`TempAnd` ternary unary + `34`-wire `b1`-split + `mk36Walk10W_338` (`w_10 =
  b1 * b0` on wire `338`) context (`[250..339)`). -/
def mk36CtxUnary88Ternary : TempCtx 411 :=
  mk36CtxUnary87Ternary.append
    (ctxTempBit ⟨92, by decide⟩ ⟨91, by decide⟩ mk36Walk10W_338 (by decide) (by decide) (by decide))

theorem mk36CtxUnary87Ternary_props :
    let mutCat : Wire 411 → Prop := fun w ↦ 107 ≤ w.val ∧ w.val < 149
    mk36CtxUnary87Ternary.DisjointFrom mutCat ∧
      mk36CtxUnary87Ternary.SupportsBelowCtx 338 ∧
      fmkTempCtxLiftEx 250 338 mk36CtxUnary87Ternary := by
  intro mutCat
  exact mk36CtxPkg_append (by decide) mk36CtxUnary54Ternary_250_props
    (mk36_splitPrefix_pkg 250 304 34 ⟨92, by decide⟩
      (by decide) (by decide) (by decide) (by decide) le_rfl)

theorem mk36CtxUnary88Ternary_props :
    let mutCat : Wire 411 → Prop := fun w ↦ 107 ≤ w.val ∧ w.val < 149
    mk36CtxUnary88Ternary.DisjointFrom mutCat ∧
      mk36CtxUnary88Ternary.SupportsBelowCtx 339 ∧
      fmkTempCtxLiftEx 250 339 mk36CtxUnary88Ternary := by
  intro mutCat
  exact mk36CtxPkg_append (by decide) mk36CtxUnary87Ternary_props
    ⟨⟨by decide, by decide, by decide, trivial⟩, ⟨by decide, trivial⟩,
      fmkTempCtxLiftEx_tempBit (cur := 338) (by decide) ⟨92, by decide⟩ ⟨91, by decide⟩
        (by decide) (by decide) (by decide)⟩

open Classical in
theorem mk36CtxUnary88Ternary_fwdBits (β : BitAssignment 411) (hβ : cleanRem 411 (411 - 250) β) :
    let γ := mk36CtxUnary88Ternary.fwdBits β
    let q27 := s3NucleusQ27 (fun i ↦ β (mk36U16W i))
    let bPar := (β mk36BParW).val
    let b0 := β ⟨91, by decide⟩
    let b1 := β ⟨92, by decide⟩
    let leaf (p : ℕ) : ZMod 2 := β mk36AccW * (if p = q27 + 27 * bPar then 1 else 0)
    cleanRem 411 (411 - 339) γ ∧
      (∀ w : Wire 411, w.val < 250 → γ w = β w) ∧
      (∀ (p : ℕ) (hp : p < 34),
        γ ⟨250 + p, by omega⟩ = (1 + b1) * leaf p ∧
        γ ⟨304 + p, by omega⟩ = b1 * leaf p) ∧
      (∀ (p : ℕ), 34 ≤ p → (hp : p < 54) → γ ⟨250 + p, by omega⟩ = leaf p) ∧
      γ mk36Walk10W_338 = b1 * b0 := by
  dsimp only
  let β54 := mk36CtxUnary54Ternary_250.fwdBits β
  obtain ⟨hcl54, hlt54, hu54⟩ := mk36CtxUnary54Ternary_250_fwd β hβ
  let K34 := fmkCtxSplitPrefix (M := 411) 250 304 34 ⟨92, by decide⟩ (by
    decide) (by decide) (by decide) 34 le_rfl
  let β87 := K34.fwdBits β54
  obtain ⟨_, hEv34⟩ := fmkCtxSplitPrefix_scoped (M := 411) 250 304 34 ⟨92, by decide⟩
    (by decide) (by decide) (by decide) 34 le_rfl
  obtain ⟨hcl87, hsrc87, hdst87, hout87⟩ := hEv34 β54 hcl54
  have hlt87_250 : ∀ w : Wire 411, w.val < 250 → β87 w = β54 w :=
    fun w hw ↦ hout87 w (by omega) (by omega)
  have hb1_54 : β54 ⟨92, by decide⟩ = β ⟨92, by decide⟩ := hlt54 ⟨92, by decide⟩ (by decide)
  have hb0_87 : β87 ⟨91, by decide⟩ = β ⟨91, by decide⟩ :=
    (hlt87_250 ⟨91, by decide⟩ (by decide)).trans (hlt54 ⟨91, by decide⟩ (by decide))
  have hb1_87 : β87 ⟨92, by decide⟩ = β ⟨92, by decide⟩ :=
    (hlt87_250 ⟨92, by decide⟩ (by decide)).trans hb1_54
  have hγ_eq : mk36CtxUnary88Ternary.fwdBits β =
      Function.update β87 mk36Walk10W_338 (β ⟨92, by decide⟩ * β ⟨91, by decide⟩) := by
    dsimp only [mk36CtxUnary88Ternary, mk36CtxUnary87Ternary]
    rw [fmkAppend_fwdBits, fmkAppend_fwdBits]
    change Function.update β87 mk36Walk10W_338 (β87 mk36Walk10W_338 + β87 ⟨92, by decide⟩ * β87 ⟨91,
      by decide⟩) = _
    have hcl_w10 : β87 mk36Walk10W_338 = 0 := hcl87 mk36Walk10W_338 (by
      dsimp [mk36Walk10W_338]; omega)
    rw [hcl_w10, zero_add, hb1_87, hb0_87]
  rw [hγ_eq]
  refine ⟨fun w hw ↦ ?_, fun w hw ↦ ?_, fun p hp ↦ ⟨?_, ?_⟩, fun p hlo hhi ↦
    ?_, Function.update_self _ _ _⟩
  · rw [Function.update_of_ne (wire_ne_of_gt (by dsimp [mk36Walk10W_338]; omega))]
    exact hcl87 w (by omega)
  · rw [Function.update_of_ne (wire_ne_of_lt (by dsimp [mk36Walk10W_338]; omega))]
    exact (hlt87_250 w hw).trans (hlt54 w hw)
  · rw [Function.update_of_ne (wire_ne_of_lt (by dsimp [mk36Walk10W_338]; omega))]
    have hs : β87 ⟨250 + p, by omega⟩ = _ := hsrc87 p (by omega) hp
    rw [hs, hb1_54]
    dsimp only [β54]
    rw [hu54 p (by omega)]
    rcases fmkBit_cases (β ⟨92, by decide⟩) with h | h <;>
      rcases fmkBit_cases (β mk36AccW * (if p = s3NucleusQ27 (fun i ↦
        β (mk36U16W i)) + 27 * (β mk36BParW).val then 1 else 0)) with hL | hL <;>
      rw [h, hL] <;> decide
  · rw [Function.update_of_ne (wire_ne_of_lt (by dsimp [mk36Walk10W_338]; omega))]
    have hd : β87 ⟨304 + p, by omega⟩ = _ := hdst87 p (by omega) hp
    rw [hd, hb1_54]
    dsimp only [β54]
    rw [hu54 p (by omega), mul_comm]
  · rw [Function.update_of_ne (wire_ne_of_lt (by dsimp [mk36Walk10W_338]; omega))]
    have ho : β87 ⟨250 + p, by omega⟩ = β54 ⟨250 + p, by omega⟩ :=
      hout87 ⟨250 + p, by omega⟩ (by dsimp; omega) (by dsimp; omega)
    exact ho.trans (hu54 p hhi)

theorem mk36Graft250_frameC (K : TempCtx 411) (hdK : K.DisjointFrom (fun q : Wire 411 ↦ 107 ≤
    q.val ∧ q.val < 149)) (hsK : K.SupportsBelowCtx 339) (hlK : fmkTempCtxLiftEx 250 339 K)
    (body : TempPhaseProg 411) (hMut : fmkIsMutBlock 411 (411 - 339) (fun q : Wire 411 ↦ 107 ≤
    q.val ∧ q.val < 149) body) : ValidCleanRem 411 (411 - 250) (K.plug body) ∧
    (∀ β1, cleanRem 411 (411 - 250) β1 → (K.plug body).evalSign β1 = 0) ∧ (∀ β1, cleanRem 411
    (411 - 250) β1 → cleanRem 411 (411 - 250) ((K.plug body).evalBits β1)) ∧ (∀ β1, cleanRem
    411 (411 - 250) β1 → ∀ q : Wire 411, ¬(107 ≤ q.val ∧ q.val < 149) → (K.plug body).evalBits
    β1 q = β1 q) ∧ (∀ β1, cleanRem 411 (411 - 250) β1 → ∀ m : Fin 42, (K.plug body).evalBits
    β1 (mk36Cat42W m) = body.evalBits (K.fwdBits β1) (mk36Cat42W m)) := by
  obtain ⟨_, hM, _, hbPos⟩ := mk36_plug_mutBlock (by decide)
    (fun _ _ hc ↦ by omega) K hdK hsK hlK body hMut.1 hMut.2.1 hMut.2.2.2
  exact ⟨hM.1, hM.2.1, hM.2.2.1, hM.2.2.2,
    fun β1 h1 m ↦ hbPos β1 h1 _ (by dsimp [mk36Cat42W]; omega)⟩

/-- Contiguous `[250..411)` (`161`-wire) `TempPhaseProg 411` parameterized by three `36`-bit
  tables. -/
def mk36MidKick216FromTables36 (t0 t1 t2 : Fin 256 → ℕ) : TempPhaseProg 411 :=
  mk36CtxUnary88Ternary.plug (mk36MidKickInner339_36 t0 t1 t2)

theorem mk36MidKick216FromTables36_spec (t0 t1 t2 : Fin 256 → ℕ)
    (ht0 : ∀ i, t0 i < 2 ^ 36) (ht1 : ∀ i, t1 i < 2 ^ 36) (ht2 : ∀ i, t2 i < 2 ^ 36) :
    ValidCleanRem 411 161 (mk36MidKick216FromTables36 t0 t1 t2) ∧
      (∀ β, cleanRem 411 161 β → (mk36MidKick216FromTables36 t0 t1 t2).evalSign β = 0) ∧
      (∀ β,
        cleanRem 411 161 β → cleanRem 411 161 ((mk36MidKick216FromTables36 t0 t1 t2).evalBits β)) ∧
      (∀ β, cleanRem 411 161 β → ∀ q : Wire 411, ¬(107 ≤ q.val ∧ q.val < 149) →
        (mk36MidKick216FromTables36 t0 t1 t2).evalBits β q = β q) ∧
      (∀ β, cleanRem 411 161 β →
        let idx0 : Fin 256 :=
          ⟨(β (mk36U16W 0)).val + 2 * (β (mk36U16W 1)).val +
            4 * s3NucleusQ27 (fun i ↦ β (mk36U16W i)) + 128 * (β mk36BParW).val,
            by have := ZMod.val_lt (β (mk36U16W 0))
               have := ZMod.val_lt (β (mk36U16W 1))
               have := s3NucleusQ27_lt (fun i ↦ β (mk36U16W i))
               have := ZMod.val_lt (β mk36BParW); omega⟩
        let pNew0 : Fin 3 → Fin 256 := fun w ↦
          ⟨bitsVal (fun b : Fin 8 ↦ β ⟨150 + 8 * w.val + b.val, by omega⟩), bitsVal_lt_two_pow _⟩
        let pOld0 : Fin 3 → Fin 256 := fun w ↦
          ⟨bitsVal (fun b : Fin 8 ↦ β ⟨8 * w.val + b.val, by omega⟩), bitsVal_lt_two_pow _⟩
        ((bitsVal (fun m ↦
          (mk36MidKick216FromTables36 t0 t1 t2).evalBits β (mk36Cat42W m)) : ℤ)).emod (2 ^ 42 : ℤ) =
          ((bitsVal (fun m ↦ β (mk36Cat42W m)) : ℤ) + ((β mk36AccW).val : ℤ) *
            ∑ w : Fin 3, (twosComp8Int (pNew0 w) - twosComp8Int (pOld0 w)) *
              (64 * (match w.val with
                | 0 => t0 idx0 | 1 => t1 idx0 | _ => t2 idx0 : ℤ))).emod (2 ^ 42 : ℤ)) := by
  obtain ⟨hdU88, hsU88, hlU88⟩ := mk36CtxUnary88Ternary_props
  obtain ⟨hv250, hSign250, hCl250, hNon250, hCat250⟩ :=
    mk36Graft250_frameC mk36CtxUnary88Ternary hdU88 hsU88 hlU88
      (mk36MidKickInner339_36 t0 t1 t2) (mk36MidKickInner339_36_mut t0 t1 t2)
  refine ⟨hv250, hSign250, hCl250, hNon250, fun β hβ ↦ ?_⟩
  intro idx0 pNew0 pOld0
  obtain ⟨hcl72, hlt250, hpre88, hsuf88, _⟩ := mk36CtxUnary88Ternary_fwdBits β hβ
  have hout_cat : (fun m : Fin 42 ↦ (mk36MidKick216FromTables36 t0 t1 t2).evalBits β
      (mk36Cat42W m)) = fun m : Fin 42 ↦ (mk36MidKickInner339_36 t0 t1 t2).evalBits
      (mk36CtxUnary88Ternary.fwdBits β) (mk36Cat42W m) := funext fun m ↦ hCat250 β hβ m
  rw [hout_cat]
  let p0_idx := s3NucleusQ27 (fun i ↦ β (mk36U16W i)) + 27 * (β mk36BParW).val
  have hp0_lt : p0_idx < 54 := by
    have := s3NucleusQ27_lt (fun i ↦ β (mk36U16W i))
    have := ZMod.val_lt (β mk36BParW)
    omega
  have hidx_eq : fmkIdx0 (β ⟨92, by decide⟩).val p0_idx (β ⟨91, by decide⟩).val = idx0 := by
    apply Fin.ext
    dsimp only [fmkIdx0, idx0, p0_idx]
    have h91 := ZMod.val_lt (β ⟨91, by decide⟩)
    have h92 := ZMod.val_lt (β ⟨92, by decide⟩)
    have h90 := ZMod.val_lt (β mk36BParW)
    have hq_lt := s3NucleusQ27_lt (fun i ↦ β (mk36U16W i))
    have hu0_eq : (β (mk36U16W 0)).val = (β ⟨91, by decide⟩).val := rfl
    have hu1_eq : (β (mk36U16W 1)).val = (β ⟨92, by decide⟩).val := rfl
    omega
  have hb1_γ : β ⟨92, by decide⟩ = mk36CtxUnary88Ternary.fwdBits β ⟨92, by decide⟩ :=
    (hlt250 ⟨92, by decide⟩ (by decide)).symm
  refine mk36MidKickInner339_36_eval_catC t0 t1 t2 ht0 ht1 ht2 β
    (mk36CtxUnary88Ternary.fwdBits β) hcl72 hlt250 idx0 pNew0 pOld0
    (fun _ ↦ rfl) (fun _ ↦ rfl) p0_idx hp0_lt hidx_eq (fun p hp ↦ ?_) (fun p h1 h2 ↦ ?_)
  · obtain ⟨e1, e2⟩ := hpre88 p hp
    rw [hb1_γ] at e1 e2
    exact ⟨e1, e2⟩
  · exact hsuf88 p h1 h2

def mk36MaskBit36 (tTab : Fin 256 → ℕ) (g : Fin 36 → Bool) (b1_bit p b0_bit : ℕ) : ZMod 2 :=
  ∑ r : Fin 36, if g r then fmkBitZ ((tTab (fmkIdx0 b1_bit p b0_bit)).testBit r.val) else 0

attribute [local irreducible] mk36RefPass36_339

attribute [local irreducible] mk36MidKickInner339_36

attribute [local irreducible] mk36CtxUnary87Ternary mk36CtxUnary88Ternary
  mk36MidKick216FromTables36

/-- Contiguous `[250..411)` (`161`-wire) `TempPhaseProg 411` specification for `Bk = 36`
  `MidKick`. -/
noncomputable def progMidKick216_36_contig411 (cfg : SpecsAux.SpecMirror.Configuration) :
    TempPhaseProg 411 := s3LockVal (mk36MidKick216FromTables36 (mk36NegCoordTable36 cfg 0)
    (mk36NegCoordTable36 cfg 1) (mk36NegCoordTable36 cfg 2))

/-- Standalone `M = 411` `TempPhaseProg 411` specification using strictly clean wires
`[233..258) ∪ [275..411)` (`161` wires, leaving `[258..275)` untouched). -/
noncomputable def progMidKick216_36_411 (cfg : SpecsAux.SpecMirror.Configuration) : TempPhaseProg
    411 :=
  (progMidKick216_36_contig411 cfg).onRegister mk36PermReg411

private theorem mk36_idx256_lt (b0 b1 bPar : ZMod 2) (u : Fin 16 → ZMod 2) :
    b0.val + 2 * b1.val + 4 * s3NucleusQ27 u + 128 * bPar.val < 256 := by
  have h0 := ZMod.val_lt b0
  have h1 := ZMod.val_lt b1
  have hq := s3NucleusQ27_lt u
  have hp := ZMod.val_lt bPar
  omega

theorem progMidKick216_36_411_raw_spec (cfg : SpecsAux.SpecMirror.Configuration) :
    (∀ γ, mk36Clean161 γ → (progMidKick216_36_411 cfg).evalSign γ = 0) ∧
    (∀ γ, mk36Clean161 γ → mk36Clean161 ((progMidKick216_36_411 cfg).evalBits γ)) ∧
    (∀ γ, mk36Clean161 γ → ∀ q : Wire 411, ¬(107 ≤ q.val ∧ q.val < 149) →
      (progMidKick216_36_411 cfg).evalBits γ q = γ q) ∧
    (∀ γ, mk36Clean161 γ →
      let idx0 : Fin 256 :=
        ⟨(γ (mk36U16W 0)).val + 2 * (γ (mk36U16W 1)).val +
          4 * s3NucleusQ27 (fun i ↦ γ (mk36U16W i)) + 128 * (γ mk36BParW).val,
          by have := ZMod.val_lt (γ (mk36U16W 0))
             have := ZMod.val_lt (γ (mk36U16W 1))
             have := s3NucleusQ27_lt (fun i ↦ γ (mk36U16W i))
             have := ZMod.val_lt (γ mk36BParW); omega⟩
      let pNew0 : Fin 3 → Fin 256 := fun w ↦
        ⟨bitsVal (fun b : Fin 8 ↦ γ ⟨150 + 8 * w.val + b.val, by omega⟩), bitsVal_lt_two_pow _⟩
      let pOld0 : Fin 3 → Fin 256 := fun w ↦
        ⟨bitsVal (fun b : Fin 8 ↦ γ ⟨8 * w.val + b.val, by omega⟩), bitsVal_lt_two_pow _⟩
      ((bitsVal (fun m ↦
        (progMidKick216_36_411 cfg).evalBits γ (mk36Cat42W m)) : ℤ)).emod (2 ^ 42 : ℤ) =
        ((bitsVal (fun m ↦ γ (mk36Cat42W m)) : ℤ) + ((γ mk36AccW).val : ℤ) *
          ∑ w : Fin 3, (twosComp8Int (pNew0 w) - twosComp8Int (pOld0 w)) *
            (fmkNegCoordTable (trunc36Cfg cfg) w idx0 : ℤ)).emod (2 ^ 42 : ℤ)) := by
  obtain ⟨_, hS, _, hN, hE⟩ := mk36MidKick216FromTables36_spec
    (mk36NegCoordTable36 cfg 0) (mk36NegCoordTable36 cfg 1) (mk36NegCoordTable36 cfg 2)
    (mk36NegCoordTable36_lt cfg 0) (mk36NegCoordTable36_lt cfg 1) (mk36NegCoordTable36_lt cfg 2)
  have hdef : progMidKick216_36_contig411 cfg = mk36MidKick216FromTables36
      (mk36NegCoordTable36 cfg 0) (mk36NegCoordTable36 cfg 1) (mk36NegCoordTable36 cfg 2) :=
      s3LockVal_eq _
  have hNonPerm : ∀ γ, mk36Clean161 γ → ∀ q : Wire 411, ¬(107 ≤ q.val ∧ q.val < 149) →
      (progMidKick216_36_411 cfg).evalBits γ q = γ q := by
    intro γ hγ q hq
    obtain ⟨_, hb⟩ := mk36Prog_onPerm_eval (progMidKick216_36_contig411 cfg) γ
    have hsw_not : ¬(107 ≤ (mk36Swap411 q).val ∧ (mk36Swap411 q).val < 149) := by
      by_cases hlt : q.val < 233
      · rwa [mk36Swap411_of_lt233 q hlt]
      · have hge := mk36Swap411_ge233 q (by omega)
        omega
    rw [progMidKick216_36_411, hb, hdef]
    exact (hN (γ ∘ mk36Swap411) (mk36CleanRem161_of_clean161 hγ) (mk36Swap411 q) hsw_not).trans
      (by dsimp only [Function.comp_apply]; rw [mk36Swap411_invol])
  refine ⟨fun γ hγ ↦ ?_, fun γ hγ w hw ↦ ?_, hNonPerm, fun γ hγ ↦ ?_⟩
  · obtain ⟨hs, _⟩ := mk36Prog_onPerm_eval (progMidKick216_36_contig411 cfg) γ
    rw [progMidKick216_36_411, hs, hdef]
    exact hS (γ ∘ mk36Swap411) (mk36CleanRem161_of_clean161 hγ)
  · rw [hNonPerm γ hγ w (by omega)]
    exact hγ w hw
  · intro idx0 pNew0 pOld0
    let β := γ ∘ mk36Swap411
    have hβ : cleanRem 411 161 β := mk36CleanRem161_of_clean161 hγ
    have hβ_lt : ∀ q : Wire 411, q.val < 233 → β q = γ q := fun q hq ↦ by
      dsimp only [β, Function.comp_apply]; rw [mk36Swap411_of_lt233 q hq]
    obtain ⟨_, hb⟩ := mk36Prog_onPerm_eval (progMidKick216_36_contig411 cfg) γ
    have hout_cat : (fun m : Fin 42 ↦ (progMidKick216_36_411 cfg).evalBits γ (mk36Cat42W m)) =
        fun m : Fin 42 ↦ (mk36MidKick216FromTables36
          (mk36NegCoordTable36 cfg 0) (mk36NegCoordTable36 cfg 1) (mk36NegCoordTable36 cfg
            2)).evalBits
            β (mk36Cat42W m) := funext fun m ↦ by
      rw [progMidKick216_36_411, hb, hdef]
      dsimp only
      rw [mk36Swap411_of_lt233 (mk36Cat42W m) (by dsimp [mk36Cat42W]; omega)]
    have hin_cat : (fun m : Fin 42 ↦ β (mk36Cat42W m)) = fun m : Fin 42 ↦ γ (mk36Cat42W m) :=
      funext fun m ↦ hβ_lt (mk36Cat42W m) (by dsimp [mk36Cat42W]; omega)
    have hu_eq : (fun i : Fin 16 ↦ β (mk36U16W i)) = fun i : Fin 16 ↦ γ (mk36U16W i) :=
      funext fun i ↦ hβ_lt (mk36U16W i) (by dsimp [mk36U16W]; omega)
    have hpar_eq : β mk36BParW = γ mk36BParW := hβ_lt mk36BParW (by decide)
    have hacc_eq : β mk36AccW = γ mk36AccW := hβ_lt mk36AccW (by decide)
    have hpN_eq : ∀ w : Fin 3,
        (⟨bitsVal (fun b : Fin 8 ↦ β ⟨150 + 8 * w.val + b.val, by omega⟩),
          bitsVal_lt_two_pow _⟩ : Fin 256) = pNew0 w :=
      fun w ↦ Fin.ext (congrArg bitsVal (funext fun b ↦ hβ_lt _ (by dsimp; omega)))
    have hpO_eq : ∀ w : Fin 3,
        (⟨bitsVal (fun b : Fin 8 ↦ β ⟨8 * w.val + b.val, by omega⟩),
          bitsVal_lt_two_pow _⟩ : Fin 256) = pOld0 w :=
      fun w ↦ Fin.ext (congrArg bitsVal (funext fun b ↦ hβ_lt _ (by dsimp; omega)))
    have hEv := hE β hβ
    dsimp only at hEv
    have hidx_eq : (⟨(β (mk36U16W 0)).val + 2 * (β (mk36U16W 1)).val +
        4 * s3NucleusQ27 (fun i ↦ β (mk36U16W i)) + 128 * (β mk36BParW).val,
        mk36_idx256_lt _ _ _ _⟩ : Fin 256) = idx0 := by
      apply Fin.ext
      dsimp only [idx0]
      rw [hu_eq, hpar_eq, hβ_lt (mk36U16W 0) (by decide), hβ_lt (mk36U16W 1) (by decide)]
    rw [hout_cat, hEv, hin_cat, hacc_eq, hidx_eq]
    refine congrArg (fun s ↦
      ((bitsVal (fun m ↦ γ (mk36Cat42W m)) : ℤ) + ((γ mk36AccW).val : ℤ) * s).emod (2 ^ 42 : ℤ)) ?_
    refine Finset.sum_congr rfl fun w _ ↦ ?_
    rw [hpN_eq w, hpO_eq w]
    fin_cases w <;> simp [fmkNegCoordTable_trunc36Cfg]

theorem progMidKick216_36_411_eq_437 (cfg : SpecsAux.SpecMirror.Configuration)
    (γ : BitAssignment 411) (β : BitAssignment 437)
    (hγ : mk36Clean161 γ) (hβ : cleanRem 437 (437 - 275) β)
    (hlo : ∀ i : ℕ, (hi1 : i < 174) → γ ⟨i, by omega⟩ = β ⟨i, by omega⟩) :
    ∀ i : ℕ, (hi1 : i < 174) →
      (progMidKick216_36_411 cfg).evalBits γ ⟨i, by omega⟩ =
        (progMidKick216_437 (trunc36Cfg cfg)).evalBits β ⟨i, by omega⟩ := by
  obtain ⟨_, _, hN411, hE411⟩ := progMidKick216_36_411_raw_spec cfg
  obtain ⟨_, _, _, hN437, hE437⟩ := progMidKick216_437_raw_spec (trunc36Cfg cfg)
  have hN1 := hN411 γ hγ
  have hE1 := hE411 γ hγ
  have hN2 := hN437 β hβ
  have hE2 := hE437 β hβ
  dsimp only at hE1 hE2
  generalize (progMidKick216_36_411 cfg).evalBits γ = e1 at hN1 hE1 ⊢
  generalize (progMidKick216_437 (trunc36Cfg cfg)).evalBits β = e2 at hN2 hE2 ⊢
  intro i hi1
  by_cases hcat : 107 ≤ i ∧ i < 149
  · have hcat_eq :
        ((bitsVal (fun m : Fin 42 ↦ e1 (mk36Cat42W m)) : ℤ)).emod (2 ^ 42 : ℤ) =
        ((bitsVal (fun m : Fin 42 ↦ e2 ⟨107 + m.val, by omega⟩) : ℤ)).emod (2 ^ 42 : ℤ) := by
      have hin_cat : (fun m : Fin 42 ↦ γ (mk36Cat42W m)) =
          fun m : Fin 42 ↦ β ⟨107 + m.val, by omega⟩ :=
        funext fun m ↦ hlo (107 + m.val) (by omega)
      have hacc : γ mk36AccW = β ⟨149, by decide⟩ := hlo 149 (by decide)
      have hu_eq : (fun k : Fin 16 ↦ γ (mk36U16W k)) =
          fun k : Fin 16 ↦ β ⟨91 + k.val, by omega⟩ :=
        funext fun k ↦ hlo (91 + k.val) (by omega)
      have hidx_eq :
          (⟨(γ (mk36U16W 0)).val + 2 * (γ (mk36U16W 1)).val +
              4 * s3NucleusQ27 (fun k ↦ γ (mk36U16W k)) + 128 * (γ mk36BParW).val,
            mk36_idx256_lt _ _ _ _⟩ : Fin 256) =
          ⟨(β ⟨91, by decide⟩).val + 2 * (β ⟨92, by decide⟩).val +
              4 * s3NucleusQ27 (fun k : Fin 16 ↦ β ⟨91 + k.val, by omega⟩) +
                128 * (β ⟨90, by decide⟩).val,
            mk36_idx256_lt _ _ _ _⟩ := by
        have hu0 : γ (mk36U16W 0) = β ⟨91, by decide⟩ := congrFun hu_eq 0
        have hu1 : γ (mk36U16W 1) = β ⟨92, by decide⟩ := congrFun hu_eq 1
        have hbpar : γ mk36BParW = β ⟨90, by decide⟩ := hlo 90 (by decide)
        refine Fin.ext ?_
        change (γ (mk36U16W 0)).val + 2 * (γ (mk36U16W 1)).val +
            4 * s3NucleusQ27 (fun k ↦ γ (mk36U16W k)) + 128 * (γ mk36BParW).val =
          (β ⟨91, by decide⟩).val + 2 * (β ⟨92, by decide⟩).val +
            4 * s3NucleusQ27 (fun k : Fin 16 ↦ β ⟨91 + k.val, by omega⟩) +
              128 * (β ⟨90, by decide⟩).val
        rw [hu0, hu1, hu_eq, hbpar]
      have hpN_eq : ∀ w : Fin 3,
          (⟨bitsVal (fun b : Fin 8 ↦ γ ⟨150 + 8 * w.val + b.val, by omega⟩),
              bitsVal_lt_two_pow _⟩ : Fin 256) =
          ⟨bitsVal (fun b : Fin 8 ↦ β ⟨150 + 8 * w.val + b.val, by omega⟩),
              bitsVal_lt_two_pow _⟩ :=
        fun w ↦ Fin.ext (congrArg bitsVal (funext fun b ↦ hlo _ (by omega)))
      have hpO_eq : ∀ w : Fin 3,
          (⟨bitsVal (fun b : Fin 8 ↦ γ ⟨8 * w.val + b.val, by omega⟩),
              bitsVal_lt_two_pow _⟩ : Fin 256) =
          ⟨bitsVal (fun b : Fin 8 ↦ β ⟨8 * w.val + b.val, by omega⟩),
              bitsVal_lt_two_pow _⟩ :=
        fun w ↦ Fin.ext (congrArg bitsVal (funext fun b ↦ hlo _ (by omega)))
      rw [hE1, hE2, hin_cat, hacc, hidx_eq]
      refine congrArg (fun s ↦
        ((bitsVal (fun m : Fin 42 ↦ β ⟨107 + m.val, by omega⟩) : ℤ) +
          ((β ⟨149, by decide⟩).val : ℤ) * s).emod (2 ^ 42 : ℤ)) ?_
      refine Finset.sum_congr rfl fun w _ ↦ ?_
      rw [hpN_eq w, hpO_eq w]
      congr 2
    set g1 : Fin 42 → ZMod 2 := fun m ↦ e1 (mk36Cat42W m)
    set g2 : Fin 42 → ZMod 2 := fun m ↦ e2 ⟨107 + m.val, by omega⟩
    have hlt1 : bitsVal g1 < 2 ^ 42 := bitsVal_lt_two_pow g1
    have hlt2 : bitsVal g2 < 2 ^ 42 := bitsVal_lt_two_pow g2
    change ((bitsVal g1 : ℤ) % (2 ^ 42 : ℤ)) = ((bitsVal g2 : ℤ) % (2 ^ 42 : ℤ)) at hcat_eq
    rw [Int.emod_eq_of_lt (Nat.cast_nonneg _) (by exact_mod_cast hlt1),
        Int.emod_eq_of_lt (Nat.cast_nonneg _) (by exact_mod_cast hlt2)] at hcat_eq
    have hb_eq : bitsVal g1 = bitsVal g2 := Int.ofNat.inj hcat_eq
    have hfn_eq : g1 = g2 := mk36BitsVal_inj hb_eq
    have hm := congrFun hfn_eq ⟨i - 107, by omega⟩
    dsimp only [g1, g2, mk36Cat42W] at hm
    have hw1 : (⟨107 + (i - 107), by omega⟩ : Wire 411) = ⟨i, by omega⟩ := Fin.ext (by dsimp; omega)
    have hw2 : (⟨107 + (i - 107), by omega⟩ : Wire 437) = ⟨i, by omega⟩ := Fin.ext (by dsimp; omega)
    rwa [hw1, hw2] at hm
  · rw [hN1 ⟨i, by omega⟩ (by dsimp; exact hcat),
      hN2 ⟨i, by omega⟩ (by dsimp; exact hcat)]
    exact hlo i hi1

end
end ConfigSlot3MidKick36_161w

end Slot3MidKick36_161w
end
end Slot3MidKick36_161w

section Slot3Norm1s36_161w
local instance (priority := 1000000) instNeZeroTwoPow_Slot3Norm1s36_161w (k : ℕ) :
    NeZero (2 ^ k) := ⟨(Nat.two_pow_pos k).ne'⟩

public section

/-
Parametric (K, D) 1-Sided Normalized Slot-3 Momentum Core and 262-Wire Oracle Foundations.

Provides:
1. Structural 18-bit leading-one index `clz18Log2`, normalized mantissa `norm1sMant18`,
   parametric signed hardware product `norm1sHwProd`, exact `wc2True` / `deltaNorm1s` scaling,
   and `mu`-independent 18-entry acceptance thresholds `q19` / `accThr` verified across all
   eight `(K, D)` operating tiers.
2. Verified `Slot3MicroEngine` straight-line circuits for the 16-`TempAnd` 18-bit priority
   encoder (`clz18Ops`), the `d = e - 2 * mu` one-hot subtractor-decoder (`subDOh18Ops`),
   the 3-axis projectile grid guard (`projNe128Ops`), and the `0`-`TempAnd` CNOT threshold
   loader (`accLoadThrLoop`).
3. `M = 437` / `mWork = 262` `StepBundle` bridges connecting `pStep1Ultra` (`1,288 T`),
   `dMidKick216_36_161w` (`4,940 T`, `Bk = 36`), and `dRevTailRet216_275` (`288 T`) onto
   `rCombBase` with zero `.TOFF` gates.
-/

namespace Slot3Norm1s36_161w

section ConfigSlot3Norm1s36_161w

set_option maxRecDepth 4096

noncomputable section

open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt HermitianMat Real
open scoped Matrix ComplexOrder MatrixOrder BigOperators Matrix.Norms.L2Operator

open SpecsAux.SpecMirror
open _root_.QuantumComputation.Specs.StoppingPowerSolution (CliffProg cleanRem cleanRem_anti)
open MomSlots35Slot3ProjNuclear (cRad7Computable)
open StepBBlock0 (padZeroBits149_clean)
open Slot3MicroEngineAux (MicroOp microValid microAllocs microAnds)
open Slot3MicroEngineAux (getBoolAt initBoolList evalMicroList)
open Slot3MicroEngineAux (allBelow allBelow_iff)
open Slot3Outer2344AndRelayWide
open Slot3Outer2344AndRelayWide.Slot3MidKickWidthWide
  (isBadA
   st0 st1)
open Slot3Outer2344AndRelayWide.Slot3UltraWidthWide
  (pStep1Ultra pStep1Ultra_disjoint_isBadA pStep1Ultra_clean_spec
   pStep1Ultra_evalBits_st0)

/- ## Section 1: Parametric `(K, D)` Normalized 1-Sided Arithmetic and `mu`-Invariance -/

/-- Supported `(K, D)` precision tiers for the 1-sided normalized Slot-3 radial test. -/
inductive Norm1sTier : Type
  | t26_18
  | t26_17
  | t26_16
  | t27_17
  | t28_17
  | t29_18
  | t29_17
  | t30_18
  deriving DecidableEq, Repr

/-- Number of retained MSB bits `K` of `u38` for a given `Norm1sTier`. -/
def Norm1sTier.kBits : Norm1sTier → ℕ
  | .t26_18 => 26
  | .t26_17 => 26
  | .t26_16 => 26
  | .t27_17 => 27
  | .t28_17 => 28
  | .t29_18 => 29
  | .t29_17 => 29
  | .t30_18 => 30

/-- Truncation cutoff `D` for a given `Norm1sTier`. -/
def Norm1sTier.dCut : Norm1sTier → ℕ
  | .t26_18 => 18
  | .t26_17 => 17
  | .t26_16 => 16
  | .t27_17 => 17
  | .t28_17 => 17
  | .t29_18 => 18
  | .t29_17 => 17
  | .t30_18 => 18

/-- Accumulator bit width `w_acc = 20 + K - D` (`<= 32`) for a given `Norm1sTier`. -/
def Norm1sTier.wAcc (t : Norm1sTier) : ℕ := 20 + t.kBits - t.dCut

theorem Norm1sTier.wAcc_le_32 (t : Norm1sTier) : t.wAcc ≤ 32 := by
  cases t <;> decide

/-- Structural helper returning the highest bit index `< k` with `2^idx <= s` (`0` when `s = 0`). -/
def clzLog2Aux (s : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => if 2 ^ k ≤ s then k else clzLog2Aux s k

/-- Highest set-bit index `e` in `[0..17]` for an `18`-bit integer `s` (`0` when `s = 0`). -/
def clz18Log2 (s : ℕ) : ℕ := clzLog2Aux s 18

/-- Left-normalized `18`-bit mantissa `m_s = s * 2 ^ (17 - clz18Log2 s)`. -/
def norm1sMant18 (s : ℕ) : ℕ := s * 2 ^ (17 - clz18Log2 s)

open Classical in
theorem clzLog2Aux_lt_succ (s k : ℕ) : clzLog2Aux s k < k + 1 := by
  induction k with
  | zero => simp [clzLog2Aux]
  | succ k ih =>
      dsimp [clzLog2Aux]
      split_ifs <;> omega

open Classical in
theorem clz18Log2_le_17 (s : ℕ) : clz18Log2 s ≤ 17 := by
  unfold clz18Log2
  rw [clzLog2Aux]
  split_ifs with h17
  · exact Nat.le_refl 17
  · have h := clzLog2Aux_lt_succ s 17
    omega

open Classical in
theorem clzLog2Aux_bounds (s : ℕ) (hs0 : 0 < s) :
    ∀ k : ℕ, s < 2 ^ k → 2 ^ clzLog2Aux s k ≤ s ∧ s < 2 ^ (clzLog2Aux s k + 1)
  | 0, hlt => by simp at hlt; omega
  | k + 1, hlt => by
      dsimp [clzLog2Aux]
      split_ifs with hge
      · exact ⟨hge, hlt⟩
      · exact clzLog2Aux_bounds s hs0 k (Nat.lt_of_not_ge hge)

theorem clz18Log2_bounds {s : ℕ} (hs0 : 0 < s) (hs18 : s < 2 ^ 18) : 2 ^ clz18Log2 s ≤ s ∧ s <
    2 ^ (clz18Log2 s + 1) := clzLog2Aux_bounds s hs0 18 hs18

theorem norm1sMant18_bounds {s : ℕ} (hs0 : 0 < s) (hs18 : s < 2 ^ 18) :
    2 ^ 17 ≤ norm1sMant18 s ∧ norm1sMant18 s < 2 ^ 18 := by
  obtain ⟨hlo, hhi⟩ := clz18Log2_bounds hs0 hs18
  have he : clz18Log2 s ≤ 17 := clz18Log2_le_17 s
  dsimp only [norm1sMant18]
  have hpow17 : 2 ^ 17 = 2 ^ clz18Log2 s * 2 ^ (17 - clz18Log2 s) := by
    rw [← pow_add]; congr 1; omega
  have hpow18 : 2 ^ 18 = 2 ^ (clz18Log2 s + 1) * 2 ^ (17 - clz18Log2 s) := by
    rw [← pow_add]; congr 1; omega
  refine ⟨?_, ?_⟩
  · rw [hpow17]
    exact Nat.mul_le_mul_right _ hlo
  · rw [hpow18]
    exact Nat.mul_lt_mul_of_pos_right hhi (Nat.two_pow_pos _)

/-- Per-bit unsigned row contribution at bit `m` of `u_K` in `norm1sHwProd`. -/
def norm1sRowVal (dCut m mS : ℕ) (uBit : Bool) : ℕ :=
  if m < dCut then
    let sh := dCut - m
    if sh = 18 then
      if uBit then 1 else 0
    else if sh < 18 then
      let w := 18 - sh
      let xm := mS / 2 ^ sh
      if uBit then 2 ^ w + xm else (2 ^ w - 1) - xm
    else 0
  else
    let off := m - dCut
    let row := if uBit then 2 ^ 18 + mS else 2 ^ 18 - mS
    row * 2 ^ off

/-- Structural prefix sum of `norm1sRowVal` over bits `0 .. m - 1` of `uK`. -/
def norm1sHwRowsAux (dCut mS uK : ℕ) : ℕ → ℕ
  | 0 => 0
  | m + 1 => norm1sHwRowsAux dCut mS uK m + norm1sRowVal dCut m mS (uK.testBit m)

/-- Exact unsigned hardware accumulator value for `(K, D)` on `(mS, uK)`. -/
def norm1sHwProd (kBits dCut mS uK : ℕ) : ℕ :=
  norm1sHwRowsAux dCut mS uK kBits + mS * 2 ^ (kBits - dCut)

/-- Structural sum of `(2 ^ (18 - sh) - 1)` over `sh` in `1 .. min dCut 17`. -/
def wc2TruncSum : ℕ → ℕ
  | 0 => 0
  | sh + 1 =>
      wc2TruncSum sh + (if sh + 1 ≤ 17 then 2 ^ (18 - (sh + 1)) - 1 else 0)

/-- Signed hardware offset constant `wc2_true(K, D)` matching `2 * P_hw - wc2_true`. -/
def wc2TrueNat (kBits dCut : ℕ) : ℕ :=
  2 * (((2 ^ (kBits - dCut) - 1) * 2 ^ 18) + wc2TruncSum dCut) + dCut

/-- Truncation error bound multiplier `E_D` (`22` at `D = 16`, `19` at `D = 17`, `18` at `D =
  18`). -/
def errBoundD (dCut : ℕ) : ℕ := if dCut = 16 then 22 else if dCut = 17 then 19 else 18

/-- Scaled `mu = 0` radial quotient `q19(K, D, d)` at `d = e - 2 * mu` in `[0..17]`. -/
def q19 (kBits dCut d : ℕ) : ℕ :=
  (cRad7Computable 0 + 2 ^ (18 + d + dCut - kBits)) / 2 ^ (19 + d + dCut - kBits)

/-- `mu`-independent 1D hardware comparator threshold `accThr(K, D, d)` for `d` in `[0..17]`. -/
def accThr (kBits dCut d : ℕ) : ℕ := (q19 kBits dCut d + wc2TrueNat kBits dCut + 2) / 2

theorem accThr_lt_wAcc_check (t : Norm1sTier) :
    allBelow 18 (fun d ↦ decide (accThr t.kBits t.dCut d < 2 ^ t.wAcc)) = true := by
  cases t <;> decide

theorem accThr_lt_two_pow_wAcc (t : Norm1sTier) {d : ℕ} (hd : d < 18) : accThr t.kBits t.dCut
    d < 2 ^ t.wAcc := of_decide_eq_true ((allBelow_iff 18 _).mp (accThr_lt_wAcc_check t) d hd)

/- ## Section 2: Verified `Slot3MicroEngine` Circuits (`clz18Ops`, `subDOh18Ops`, `projNe128Ops`) -/

/-- Exact 16-`TempAnd` 18-bit priority encoder computing `clz18Log2 s` onto 5 output slots. -/
def clz18Ops : List MicroOp := [ .zeroAlloc, .notW 18, .cnotW 17 18, .andAlloc 18 16, .cnotW
    19 18, .andAlloc 18 15, .cnotW 20 18, .andAlloc 18 14, .cnotW 21 18, .andAlloc 18 13,
    .cnotW 22 18, .andAlloc 18 12, .cnotW 23 18, .andAlloc 18 11, .cnotW 24 18, .andAlloc 18
    10, .cnotW 25 18, .andAlloc 18 9, .cnotW 26 18, .andAlloc 18 8, .cnotW 27 18, .andAlloc 18
    7, .cnotW 28 18, .andAlloc 18 6, .cnotW 29 18, .andAlloc 18 5, .cnotW 30 18, .andAlloc 18
    4, .cnotW 31 18, .andAlloc 18 3, .cnotW 32 18, .andAlloc 18 2, .cnotW 33 18, .andAlloc 18
    1, .cnotW 34 18, .zeroAlloc, .cnotW 34 35, .cnotW 32 35, .cnotW 30 35, .cnotW 28 35,
    .cnotW 26 35, .cnotW 24 35, .cnotW 22 35, .cnotW 20 35, .cnotW 17 35, .zeroAlloc, .cnotW
    33 36, .cnotW 32 36, .cnotW 29 36, .cnotW 28 36, .cnotW 25 36, .cnotW 24 36, .cnotW 21 36,
    .cnotW 20 36, .zeroAlloc, .cnotW 31 37, .cnotW 30 37, .cnotW 29 37, .cnotW 28 37, .cnotW
    23 37, .cnotW 22 37, .cnotW 21 37, .cnotW 20 37, .zeroAlloc, .cnotW 27 38, .cnotW 26 38,
    .cnotW 25 38, .cnotW 24 38, .cnotW 23 38, .cnotW 22 38, .cnotW 21 38, .cnotW 20 38,
    .zeroAlloc, .cnotW 19 39, .cnotW 17 39 ]

theorem clz18Ops_meta : microValid 18 clz18Ops = true ∧ microAllocs clz18Ops = 22 ∧ microAnds
    clz18Ops = 16 := by
  decide

/-- 7-`TempAnd` 8-bit inequality guard testing `p ≠ 128` for one projectile momentum axis. -/
def projNe128Ops : List MicroOp := [ .notW 0, .notW 1, .notW 2, .notW 3, .notW 4, .notW 5,
    .notW 6, .andAlloc 0 1, .andAlloc 2 3, .andAlloc 4 5, .andAlloc 6 7, .notW 0, .notW 1,
    .notW 2, .notW 3, .notW 4, .notW 5, .notW 6, .andAlloc 8 9, .andAlloc 10 11, .andAlloc 12
    13, .notW 14 ]

/-- Output slot index for `decide (p ≠ 128)` in `projNe128Ops`. -/
def projNe128OutSlot : ℕ := 14

theorem projNe128Ops_meta : microValid 8 projNe128Ops = true ∧ microAllocs projNe128Ops = 7 ∧
    microAnds projNe128Ops = 7 := by
  decide

theorem projNe128Ops_eval_check :
    allBelow 256 (fun m ↦
      let st := evalMicroList 8 projNe128Ops (initBoolList 8 (8 + 7) m)
      allBelow 8 (fun i ↦ getBoolAt st i == m.testBit i) &&
      (getBoolAt st projNe128OutSlot == decide (m ≠ 128))) = true := by
  decide

/-- Structural CNOT fanout XORing `accThr kBits dCut d` from `ohW d` into `thrW[0..wAcc)`. -/
def accLoadRowCliff {M : ℕ} (val : ℕ) (oh : Wire M) :
    ∀ (w : ℕ) (thrW : Fin w → Wire M), (∀ j : Fin w, oh ≠ thrW j) → CliffProg M
  | 0, _, _ => .nil
  | w + 1, thrW, hne =>
      let rest := accLoadRowCliff (val / 2) oh w (fun j ↦ thrW j.succ) (fun j ↦ hne j.succ)
      if val % 2 = 1 then
        .seq (.cnot oh (thrW 0) (hne 0)) rest
      else
        rest

/-- Structural CNOT table loader over all 18 entries `d` in `0 .. 17` (`0` `TempAnd`s). -/
def accLoadThrLoop {M : ℕ} (kBits dCut wAcc : ℕ) (thrW : Fin wAcc → Wire M) :
    ∀ (rem : ℕ) (_ : rem ≤ 18) (ohW : Fin 18 → Wire M),
      (∀ (d : Fin 18) (j : Fin wAcc), ohW d ≠ thrW j) → CliffProg M
  | 0, _, _, _ => .nil
  | rem + 1, hrem, ohW, hne =>
      let dIdx : Fin 18 := ⟨18 - (rem + 1), by omega⟩
      .seq
        (accLoadRowCliff (accThr kBits dCut dIdx.val) (ohW dIdx) wAcc thrW (fun j ↦ hne dIdx j))
        (accLoadThrLoop kBits dCut wAcc thrW rem (by omega) ohW hne)

/- ## Section 3: `M = 437` / `mWork = 262` `StepBundle` Bridges (`pStep1Ultra`, `MidKick36`, Relay
Revs) -/

theorem st0_clean_and_not_badA (α : BitAssignment 149) :
    cleanRem 437 (437 - 275) (st0 α) ∧ (∀ w : Wire 437, isBadA w = true → st0 α w = 0) := by
  refine ⟨cleanRem_anti (by decide) (padZeroBits149_clean α), fun w hw ↦ ?_⟩
  have h : 201 ≤ w.val ∧ w.val < 227 := of_decide_eq_true hw
  exact padZeroBits149_clean α w (by omega)

theorem st1_clean_and_not_badA (α : BitAssignment 149) :
    cleanRem 437 (437 - 275) (st1 α) ∧ (∀ w : Wire 437, isBadA w = true → st1 α w = 0) := by
  have h0 := st0_clean_and_not_badA α
  have hcl1 : cleanRem 437 (437 - 275) (st1 α) := by
    rw [← pStep1Ultra_evalBits_st0 α]
    exact pStep1Ultra_clean_spec.2.2 (st0 α) h0.1
  refine ⟨hcl1, fun w hw ↦ ?_⟩
  rw [← pStep1Ultra_evalBits_st0 α]
  have hpres := (Slot3Outer2344AndRelayWide.Slot3MidKickWidthWide.progDisjointBad_eval
    isBadA pStep1Ultra pStep1Ultra_disjoint_isBadA.1 (st0 α) (st0 α) (fun _ _ ↦ rfl)).2.2 w hw
  exact hpres.trans (h0.2 w hw)

end

set_option maxRecDepth 2000

end ConfigSlot3Norm1s36_161w

end Slot3Norm1s36_161w
end
end Slot3Norm1s36_161w

end QuantumComputation.Specs.StoppingPowerSolution
