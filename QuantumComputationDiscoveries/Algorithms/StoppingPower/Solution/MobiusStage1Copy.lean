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

public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.DualMuxGf8Table
public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.StageBMidKickQrom

@[expose] public section
set_option allowUnsafeReducibility true

namespace QuantumComputation.Specs.StoppingPowerSolution

noncomputable section D0aa33Width165Slot3Prep2356

section
namespace D0aa33Width165Slot3Prep2356
section ConfigK2
set_option maxRecDepth 200000
set_option exponentiation.threshold 512
set_option backward.isDefEq.respectTransparency true
local instance (priority := 1000000) instNeZeroTwoPowK13 (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩
noncomputable section
open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt HermitianMat Real
open LocalClassicalPerm
open scoped Matrix ComplexOrder MatrixOrder BigOperators Matrix.Norms.L2Operator Circuit.Notation
open SpecsAux SpecsAux.SpecMirror
open MeasureBranchHadamardSem
open MomSlot0CircuitHalf (padZeroBits phaseDiagUnitary)
open MomSlot1GeomPriority288 (RawSsa SsaProg b2z)
open MomSlots35Slot3ProjNuclear (predCoarseGood33)
open ShiftedMagS1 (bitsVal_eq_of_testBit testBit_div_two_powAux testBit_mod_two_powAux)
open Slot3PrepWideAndSwap3 (progNotZero33Cz)
open Leaf3Prep179Spec (padZeroBits_lt padZeroBits_ge MicroStep microEnd microAllocs microValid
  microValid_nW microValid_cW microValid_aW getBoolAt setBoolAt length_setBoolAt getBoolAt_setBoolAt
  evalMicroList length_mkBoolList getBoolAt_mkBoolList initBoolList microSlotWire
  microSlotWire_lt_in microSlotWire_ge_in ssaCastEnd ssaCastEnd_countAnd ssaCastEnd_eval ssaMicroRun
  ssaMicroRun_spec bitsVal_testBit_eq allBelow allBelow_iff nat_beq_iff fastBitSmall
  fastBitSmall_eq_testBit packPredLoop testBit_packPredLoop_zero testBit_colMaskFast testBit_allMask
  allMaskFast allMaskFast_eq PTree pconst pconst_hasDepth pget pset_hasDepth pget_pconst pget_pset
  psetNat_eq initColsFast_spec evalSIMD simdRun simdRun_testBit_eq getNatAt kcTable49168List
  s1Kc68Ops s1Kc68OutSlots s1Kc68_meta checkStage1Cert checkStage1Cert_true xorRightMapGen tblBits16
  phaseStage234_49 cQutrit3CoreGen)
open Slot3Norm1s36CoreWide
open MultiBankWStateRouter
attribute [local irreducible]
  wStateComputeUncondPow2 wStateUncomputeUncondPow2 xUnloadCzPairsSeqDyn progNotZero33Cz
  cQutrit3CoreGen phaseStage234_49
theorem dynCount_circuit {Var : Type} {n k : ℕ} (c : Circuit n) (g : PrimitiveGate k) :
    (DynamicCircuit.circuit c : DynamicCircuit Var n).count g = c.count g := rfl
theorem ket_basisOutcomeProjector_zero {k n : ℕ} (r : QRegister k n) (α : BitAssignment n) :
    (r.basisOutcomeProjector 0).mulVec (ket α) =
      if ∀ j : Fin k, α (r j) = 0 then ket α else 0 := by
  rw [← projZeroAll_eq_basisOutcomeProjector_zero r, ket_projZeroAll]
theorem embedUnitary_phaseDiagUnitary_mulVec_ket {kAct n : ℕ}
    (rAct : QRegister kAct n) (pred : BitAssignment kAct → ZMod 2) (β : BitAssignment n) :
    (rAct.embedUnitary (phaseDiagUnitary pred)).1.mulVec (ket β) =
      bitSign (pred (fun i ↦ β (rAct i))) • ket β := by
  let x : BitAssignment kAct := fun i ↦ β (rAct i)
  have hwAct : writeRegProg β rAct x = β := by
    funext w
    by_cases hmem : w ∈ Set.range rAct.wires
    · obtain ⟨i, rfl⟩ := hmem; rw [writeRegProg_apply_reg]
    · exact writeRegProg_apply_of_not_mem _ _ _ _ hmem
  rw [QRegister.embedUnitary_val, embedMatrix_mulVec_ket_prog]
  have hEvalAct : ∀ l : Fin (2 ^ kAct),
      (phaseDiagUnitary pred).1 l (localIdxProg rAct β) =
        if l = localIdxProg rAct β then ((-1 : ℂ) ^ (pred x).val) else 0 := by
    intro l
    by_cases hl : l = localIdxProg rAct β
    · subst hl
      have hb : basisBits kAct (localIdxProg rAct β) = x :=
        (basisBitsEquiv kAct).apply_symm_apply x
      simp [phaseDiagUnitary, hb]
    · simp [phaseDiagUnitary, hl]
  simp_rw [hEvalAct, ite_smul, zero_smul]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  have hbb : basisBits kAct (localIdxProg rAct β) = x :=
    (basisBitsEquiv kAct).apply_symm_apply x
  rw [hbb, hwAct, ← TempPhaseProg.bitSign_eq_neg_one_pow]
theorem subspaceStep_of_realizesCleanWorkspace
    {Var : Type} [Fintype Var] [DecidableEq Var] {n k m : ℕ}
    {rAct : QRegister k n} {rClean : QRegister m n}
    {U : Unitary (2 ^ k)} {d : DynamicCircuit Var n}
    (hr : DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace rAct rClean U d)
    (R : Operator (2 ^ n))
    (hPR : rClean.basisOutcomeProjector 0 * R = R) :
    SubspaceStep R ((rAct.embedUnitary U).1 * R) d := fun M ↦ by
  obtain ⟨N, hwp, hproj⟩ := hr M
  refine ⟨N, hwp, ?_⟩
  set P := rClean.basisOutcomeProjector 0
  have hP : Pᴴ = P := rClean.basisOutcomeProjector_conjTranspose 0
  have hRP : Rᴴ * P = Rᴴ := by
    simpa only [Matrix.conjTranspose_mul, hP] using congrArg Matrix.conjTranspose hPR
  calc ((rAct.embedUnitary U).1 * R)ᴴ * M.1.1 * ((rAct.embedUnitary U).1 * R)
      = Rᴴ * (P * ((rAct.embedUnitary U).1ᴴ * M.1.1 * (rAct.embedUnitary U).1) * P) * R := by
          rw [Matrix.conjTranspose_mul]
          simp only [Matrix.mul_assoc]
          rw [hPR, ← Matrix.mul_assoc Rᴴ P, hRP]
    _ = Rᴴ * (P * N.1.1 * P) * R := by rw [← hproj]
    _ = Rᴴ * N.1.1 * R := by
          simp only [Matrix.mul_assoc]
          rw [hPR, ← Matrix.mul_assoc Rᴴ P, hRP]
theorem realizesCleanWorkspace_of_subspaceStep
    {Var : Type} [Fintype Var] [DecidableEq Var] {n k m : ℕ}
    {rAct : QRegister k n} {rWork : QRegister m n}
    {U : Unitary (2 ^ k)} {d : DynamicCircuit Var n}
    (hs : SubspaceStep (rWork.basisOutcomeProjector 0)
      ((rAct.embedUnitary U).1 * rWork.basisOutcomeProjector 0) d) :
    DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace rAct rWork U d := fun M ↦ by
  obtain ⟨N, hwp, hm⟩ := hs M
  refine ⟨N, hwp, ?_⟩
  set P := rWork.basisOutcomeProjector 0
  have hP : Pᴴ = P := rWork.basisOutcomeProjector_conjTranspose 0
  calc P * N.1.1 * P
      = Pᴴ * N.1.1 * P := by rw [hP]
    _ = ((rAct.embedUnitary U).1 * P)ᴴ * M.1.1 * ((rAct.embedUnitary U).1 * P) := hm.symm
    _ = P * ((rAct.embedUnitary U).1ᴴ * M.1.1 * (rAct.embedUnitary U).1) * P := by
          simp only [Matrix.conjTranspose_mul, hP, Matrix.mul_assoc]
theorem subspaceStep_of_validCleanRem
    {Var : Type} [Fintype Var] [DecidableEq Var] {M n : ℕ}
    (v : Var) (rComb : QRegister M n) (p : TempPhaseProg M)
    (rem : ℕ) (hrem : rem ≤ M) (hValid : ValidCleanRem M rem p)
    (R : Operator (2 ^ n))
    (hPR : projZeroAll rem (tailScr rComb rem hrem) * R = R) :
    SubspaceStep R (((p.onRegister rComb).toToffCircuit).eval.1 * R)
      ((p.onRegister rComb).toDyn v) := fun M_obs ↦ by
  have hSmall := realizes_of_validCleanRem v rComb p rem hrem hValid
  set P := projZeroAll rem (tailScr rComb rem hrem)
  have hP : Pᴴ = P := projZeroAll_conjTranspose rem _
  obtain ⟨N, hN⟩ := PreservesStoreConst_toDyn v (p.onRegister rComb) M_obs
  refine ⟨N, hN, ?_⟩
  have hconj := hSmall.2 (fun _ ↦ M_obs) (fun _ _ ↦ rfl) default
  have hN_eq : wp ((p.onRegister rComb).toDyn v).compile (fun _ ↦ M_obs) default = N := by
    rw [hN]
  rw [hN_eq] at hconj
  have h0 : P * N.1.1 * P = P * (((p.onRegister rComb).toToffCircuit).eval.1ᴴ * M_obs.1.1 *
      ((p.onRegister rComb).toToffCircuit).eval.1) * P := by
    simpa [P, hP, wpQAssignCompat, qAssignObsMap, Observable.conj_coe, Unitary.coe_star,
      Matrix.star_eq_conjTranspose, HermitianMat.conj_apply_mat, Matrix.mul_assoc] using
      congrArg Subtype.val hconj
  have hRP : Rᴴ * P = Rᴴ := by
    simpa only [Matrix.conjTranspose_mul, hP] using congrArg Matrix.conjTranspose hPR
  calc (((p.onRegister rComb).toToffCircuit).eval.1 * R)ᴴ * M_obs.1.1 *
        (((p.onRegister rComb).toToffCircuit).eval.1 * R)
      = Rᴴ * (P * (((p.onRegister rComb).toToffCircuit).eval.1ᴴ * M_obs.1.1 *
          ((p.onRegister rComb).toToffCircuit).eval.1) * P) * R := by
          rw [Matrix.conjTranspose_mul]
          simp only [Matrix.mul_assoc]
          rw [hPR, ← Matrix.mul_assoc Rᴴ P, hRP]
    _ = Rᴴ * (P * N.1.1 * P) * R := by rw [h0]
    _ = Rᴴ * N.1.1 * R := by
          simp only [Matrix.mul_assoc]
          rw [hPR, ← Matrix.mul_assoc Rᴴ P, hRP]
theorem update_writeRegProg {k n : ℕ} (α : BitAssignment n) (r : QRegister k n)
    (γ : BitAssignment k) (j₀ : Fin k) (val : ZMod 2) : Function.update (writeRegProg α r γ)
    (r j₀) val = writeRegProg α r (Function.update γ j₀ val) := by
  funext w
  by_cases hmem : w ∈ Set.range r.wires
  · obtain ⟨j, rfl⟩ := hmem
    rw [writeRegProg_apply_reg]
    by_cases hj : j = j₀
    · subst hj
      rw [Function.update_self, Function.update_self]
    · rw [Function.update_of_ne (r.wires.injective.ne hj), Function.update_of_ne hj,
        writeRegProg_apply_reg]
  · rw [Function.update_of_ne (fun h ↦ hmem ⟨j₀, h.symm⟩),
      writeRegProg_apply_of_not_mem _ _ _ _ hmem, writeRegProg_apply_of_not_mem _ _ _ _ hmem]
theorem writeRegProg_compose {k M n : ℕ} (α : BitAssignment n) (rComb : QRegister M n)
    (sel : QRegister k M) (γ : BitAssignment M) (δ : BitAssignment k) : writeRegProg
    (writeRegProg α rComb γ) (rComb.compose sel) δ = writeRegProg α rComb
    (writeRegProg γ sel δ) := by
  funext w
  by_cases hmem : w ∈ Set.range (rComb.compose sel).wires
  · obtain ⟨i, rfl⟩ := hmem
    change writeRegProg (writeRegProg α rComb γ) (rComb.compose sel) δ ((rComb.compose sel) i) =
      writeRegProg α rComb (writeRegProg γ sel δ) (rComb (sel i))
    rw [writeRegProg_apply_reg, writeRegProg_apply_reg, writeRegProg_apply_reg]
  · rw [writeRegProg_apply_of_not_mem _ _ _ _ hmem]
    by_cases hComb : w ∈ Set.range rComb.wires
    · obtain ⟨j, rfl⟩ := hComb
      have hnotSel : j ∉ Set.range sel.wires := by
        rintro ⟨i, rfl⟩
        exact hmem ⟨i, rfl⟩
      rw [writeRegProg_apply_reg, writeRegProg_apply_reg,
        writeRegProg_apply_of_not_mem _ _ _ _ hnotSel]
    · rw [writeRegProg_apply_of_not_mem _ _ _ _ hComb,
        writeRegProg_apply_of_not_mem _ _ _ _ hComb]
theorem cliff_onRegister_compose_eval {k M n : ℕ} (α : BitAssignment n)
    (rComb : QRegister M n) (sel : QRegister k M)
    (γ : BitAssignment M) :
    ∀ c : CliffProg k,
      (c.onRegister (rComb.compose sel)).eval (writeRegProg α rComb γ) =
        writeRegProg α rComb ((c.onRegister sel).eval γ)
  | .nil => rfl
  | .x q => by
      dsimp only [CliffProg.onRegister, CliffProg.eval]
      change Function.update (writeRegProg α rComb γ) (rComb (sel q))
        (writeRegProg α rComb γ (rComb (sel q)) + 1) = _
      rw [writeRegProg_apply_reg, update_writeRegProg]
  | .cnot a b h => by
      dsimp only [CliffProg.onRegister, CliffProg.eval]
      change Function.update (writeRegProg α rComb γ) (rComb (sel b))
        (writeRegProg α rComb γ (rComb (sel b)) + writeRegProg α rComb γ (rComb (sel a))) = _
      rw [writeRegProg_apply_reg, writeRegProg_apply_reg, update_writeRegProg]
  | .seq c₁ c₂ => by
      dsimp only [CliffProg.onRegister, CliffProg.eval]
      rw [cliff_onRegister_compose_eval α rComb sel γ c₁,
        cliff_onRegister_compose_eval α rComb sel ((c₁.onRegister sel).eval γ) c₂]
/-! ## Section 2: Upward-Möbius CNOT Passes (`cMobius8`, `cMobius32`) & Stage-1 Rest
`pStage1Copy125` (`152 T`) -/
def cMobiusBit (K b : ℕ) : (m : ℕ) → CliffProg (2 ^ K)
  | 0 => .nil
  | m + 1 =>
      let prev := cMobiusBit K b m
      if hm : (m.testBit b = false) ∧ (m + 2 ^ b) < 2 ^ K ∧ m < 2 ^ K then
        .seq prev (.cnot ⟨m + 2 ^ b, hm.2.1⟩ ⟨m, hm.2.2⟩
          (wire_ne_of_gt (by dsimp; have : 0 < 2 ^ b := Nat.two_pow_pos b; omega)))
      else
        prev
def cMobiusBits (K : ℕ) : (b : ℕ) → CliffProg (2 ^ K)
  | 0 => .nil
  | b + 1 => .seq (cMobiusBits K b) (cMobiusBit K b (2 ^ K))
def cMobiusPow2 (K : ℕ) : CliffProg (2 ^ K) :=
  .seq (cMobiusBits K K) (.x ⟨0, Nat.two_pow_pos K⟩)
abbrev cMobius8 : CliffProg 8 := cMobiusPow2 3
abbrev cMobius32 : CliffProg 32 := cMobiusPow2 5
def oneHotBits {N : ℕ} (x₀ : Fin N) : BitAssignment N := fun m ↦ if m = x₀ then 1 else 0
def mobiusTargetBits {N : ℕ} (x₀ : Fin N) : BitAssignment N :=
  fun m ↦ if m.val = 0 then 0 else b2z (decide (Nat.land m.val x₀.val = m.val))
theorem cMobius8_eval_oneHot (r₀ : Fin 8) (m : Wire 8) :
    cMobius8.eval (oneHotBits r₀) m = mobiusTargetBits r₀ m := by
  revert r₀ m; decide +kernel
theorem cMobius32_eval_oneHot (q₀ : Fin 32) (m : Wire 32) :
    cMobius32.eval (oneHotBits q₀) m = mobiusTargetBits q₀ m := by
  revert q₀ m; decide +kernel
theorem cMobius8_eval_oneHot_eq (r₀ : Fin 8) : cMobius8.eval (oneHotBits r₀) =
    mobiusTargetBits r₀ := funext (cMobius8_eval_oneHot r₀)
theorem cMobius32_eval_oneHot_eq (q₀ : Fin 32) : cMobius32.eval (oneHotBits q₀) =
    mobiusTargetBits q₀ := funext (cMobius32_eval_oneHot q₀)
attribute [local irreducible] cMobius8 cMobius32
def inW38List : List ℕ := [25, 26, 27, 28, 29, 30, 31, 32, 51, 53, 54, 55, 58, 60, 61, 62, 64,
    65, 66, 67, 68, 69, 70, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86]
def inW38 : Fin 38 → Wire 125 :=
  fun i ↦ ⟨getNatAt inW38List i.val, by revert i; decide⟩
theorem inW38_inj : Function.Injective inW38 := by
  intro i j; revert i j; decide
theorem inW38_lt : ∀ i : Fin 38, (inW38 i).val < 87 := by
  decide
def s1Kc68RestOps : List MicroStep := s1Kc68Ops.drop 30
theorem s1Kc68Rest_meta :
    microValid 38 s1Kc68RestOps = true ∧ microAllocs s1Kc68RestOps = 38 ∧ 87 + 38 = 125 := by
  decide +kernel
theorem s1Kc68Rest_end : microEnd 87 s1Kc68RestOps = 125 := by decide +kernel
def ssaStage1Rest : SsaProg 125 87 125 :=
  ssaCastEnd s1Kc68Rest_end
    (ssaMicroRun inW38 inW38_inj 87 inW38_lt 38 87 ⟨by decide, le_rfl⟩
      s1Kc68RestOps s1Kc68Rest_meta.1 (by rw [s1Kc68Rest_end]))
theorem ssaStage1Rest_countAnd : ssaStage1Rest.countAnd = 38 := by
  unfold ssaStage1Rest
  rw [ssaCastEnd_countAnd,
    (ssaMicroRun_spec inW38 inW38_inj 87 inW38_lt s1Kc68RestOps 38 87 ⟨by decide, le_rfl⟩
      s1Kc68Rest_meta.1 (by rw [s1Kc68Rest_end])).1,
    s1Kc68Rest_meta.2.1]
def kcSrcWire125 (j : Fin 16) : Wire 125 :=
  microSlotWire inW38 87 (getNatAt s1Kc68OutSlots j.val)
    (fun _ ↦ by revert j; decide)
def kcDstWire125 (j : Fin 16) : Wire 125 :=
  ⟨33 + j.val, by omega⟩
theorem kcSrc_ne_dst (j : Fin 16) : kcSrcWire125 j ≠ kcDstWire125 j := by
  revert j; decide
def cCopyKc16Aux : (m : ℕ) → m ≤ 16 → CliffProg 125
  | 0, _ => .nil
  | m + 1, hm =>
      let j : Fin 16 := ⟨m, hm⟩
      .seq (cCopyKc16Aux m (Nat.le_of_succ_le hm))
        (.cnot (kcSrcWire125 j) (kcDstWire125 j) (kcSrc_ne_dst j))
def cCopyKc16 : CliffProg 125 := cCopyKc16Aux 16 le_rfl
def rawToTempPhase {M : ℕ} (body : TempPhaseProg M) : RawSsa M → TempPhaseProg M
  | .done => body
  | .x q rest => .seq (.cliff (.x q)) (.seq (rawToTempPhase body rest) (.cliff (.x q)))
  | .cnot c t hct rest =>
      .seq (.cliff (.cnot c t hct)) (.seq (rawToTempPhase body rest) (.cliff (.cnot c t hct)))
  | .skipZero rest => rawToTempPhase body rest
  | .andClean anc c₁ c₂ h₁₂ hc1a hc2a rest =>
      .tempAnd c₁ c₂ anc h₁₂ hc1a hc2a (rawToTempPhase body rest)
def pStage1Copy125 : TempPhaseProg 125 := rawToTempPhase (.cliff cCopyKc16) ssaStage1Rest.raw
theorem rawToTempPhase_countTempAnd {M : ℕ} (body : TempPhaseProg M) :
    ∀ p : RawSsa M, (rawToTempPhase body p).countTempAnd = p.countAnd + body.countTempAnd
  | .done => by simp [rawToTempPhase, RawSsa.countAnd]
  | .x _ rest => by
      simp [rawToTempPhase, RawSsa.countAnd, TempPhaseProg.countTempAnd,
        rawToTempPhase_countTempAnd body rest]
  | .cnot _ _ _ rest => by
      simp [rawToTempPhase, RawSsa.countAnd, TempPhaseProg.countTempAnd,
        rawToTempPhase_countTempAnd body rest]
  | .skipZero rest => rawToTempPhase_countTempAnd body rest
  | .andClean _ _ _ _ _ _ rest => by
      simp only [rawToTempPhase, RawSsa.countAnd, TempPhaseProg.countTempAnd,
        rawToTempPhase_countTempAnd body rest]
      omega
theorem rawToTempPhase_cliff_evalSign {M : ℕ} (c : CliffProg M) :
    ∀ (p : RawSsa M) (β : BitAssignment M),
      (rawToTempPhase (.cliff c) p).evalSign β = 0
  | .done, _ => rfl
  | .x _ rest, β => by
      dsimp only [rawToTempPhase, TempPhaseProg.evalSign, TempPhaseProg.evalBits, CliffProg.eval]
      rw [rawToTempPhase_cliff_evalSign c rest _, add_zero, add_zero]
  | .cnot _ _ _ rest, β => by
      dsimp only [rawToTempPhase, TempPhaseProg.evalSign, TempPhaseProg.evalBits, CliffProg.eval]
      rw [rawToTempPhase_cliff_evalSign c rest _, add_zero, add_zero]
  | .skipZero rest, β => rawToTempPhase_cliff_evalSign c rest β
  | .andClean _ _ _ _ _ _ rest, β => by
      dsimp only [rawToTempPhase, TempPhaseProg.evalSign]
      exact rawToTempPhase_cliff_evalSign c rest _
theorem validCleanRem_mono_shared {M : ℕ} :
    ∀ {p : TempPhaseProg M} {rem₁ rem₂ : ℕ}, rem₁ ≤ rem₂ →
      ValidCleanRem M rem₁ p → ValidCleanRem M rem₂ p
  | .nil, _, _, _, _ => trivial
  | .cliff _, _, _, _, _ => trivial
  | .z _, _, _, _, _ => trivial
  | .seq _ _, _, _, hle, ⟨remMid, hmid, h₁, h₂, hpres⟩ =>
      ⟨remMid, hmid, validCleanRem_mono_shared hle h₁, h₂,
        fun β hβ ↦ hpres β (cleanRem_anti hle hβ)⟩
  | .tempAnd _ _ _ _ _ _ _, _, _, hle, ⟨hanc, hbody, hpres⟩ =>
      ⟨by omega, hbody, hpres⟩
theorem pStage1Copy125_countTempAnd : pStage1Copy125.countTempAnd = 38 := by
  unfold pStage1Copy125
  rw [rawToTempPhase_countTempAnd, TempPhaseProg.countTempAnd, Nat.add_zero]
  exact ssaStage1Rest_countAnd
theorem cCopyKc16Aux_eval (β : BitAssignment 125) :
    ∀ (m : ℕ) (hm : m ≤ 16) (w : Wire 125),
      (cCopyKc16Aux m hm).eval β w =
        if h : 33 ≤ w.val ∧ w.val < 33 + m then
          β w + β (kcSrcWire125 ⟨w.val - 33, by omega⟩)
        else
          β w
  | 0, _, w => by
      have hnot : ¬ (33 ≤ w.val ∧ w.val < 33 + 0) := by omega
      simp [cCopyKc16Aux, CliffProg.eval, hnot]
  | m + 1, hm, w => by
      dsimp only [cCopyKc16Aux, CliffProg.eval]
      have ih := cCopyKc16Aux_eval β m (Nat.le_of_succ_le hm)
      have hSrcVal : ∀ j : Fin 16, ¬ (33 ≤ (kcSrcWire125 j).val ∧ (kcSrcWire125 j).val < 33 + m) :=
        by
        intro j; have hj : (kcSrcWire125 j).val < 33 ∨ 49 ≤ (kcSrcWire125 j).val := by
          revert j; decide
        omega
      by_cases hw : w = kcDstWire125 ⟨m, hm⟩
      · subst hw
        rw [Function.update_self]
        have hnot_m : ¬ (33 ≤ (kcDstWire125 ⟨m, hm⟩).val ∧ (kcDstWire125 ⟨m, hm⟩).val < 33 + m) :=
          by
          dsimp [kcDstWire125]; omega
        have hyes_m1 : 33 ≤ (kcDstWire125 ⟨m, hm⟩).val ∧ (kcDstWire125 ⟨m, hm⟩).val < 33 + (m +
          1) := by
          dsimp [kcDstWire125]; omega
        have hβ'dst : (cCopyKc16Aux m (Nat.le_of_succ_le hm)).eval β (kcDstWire125 ⟨m, hm⟩) =
            β (kcDstWire125 ⟨m, hm⟩) := by
          rw [ih, dite_eq_right hnot_m]
        have hβ'src : (cCopyKc16Aux m (Nat.le_of_succ_le hm)).eval β (kcSrcWire125 ⟨m, hm⟩) =
            β (kcSrcWire125 ⟨m, hm⟩) := by
          rw [ih, dite_eq_right (hSrcVal ⟨m, hm⟩)]
        rw [hβ'dst, hβ'src, dite_eq_left hyes_m1]
        have hidx : (⟨(kcDstWire125 ⟨m, hm⟩).val - 33, by omega⟩ : Fin 16) = ⟨m, hm⟩ := by
          ext; dsimp [kcDstWire125]; omega
        rw [hidx]
      · rw [Function.update_of_ne hw, ih w]
        have hw_ne : w.val ≠ 33 + m := fun heq ↦ hw (Fin.ext heq)
        have hiff : (33 ≤ w.val ∧ w.val < 33 + (m + 1)) ↔ (33 ≤ w.val ∧ w.val < 33 + m) := by omega
        by_cases hcond : 33 ≤ w.val ∧ w.val < 33 + m
        · have hcond' : 33 ≤ w.val ∧ w.val < 33 + (m + 1) := hiff.mpr hcond
          rw [dite_eq_left hcond, dite_eq_left hcond']
        · have hcond' : ¬ (33 ≤ w.val ∧ w.val < 33 + (m + 1)) := fun hc ↦ hcond (hiff.mp hc)
          rw [dite_eq_right hcond, dite_eq_right hcond']
def applyCopyKc (γ β : BitAssignment 125) : BitAssignment 125 :=
  fun w ↦
    if h : 33 ≤ w.val ∧ w.val < 49 then
      β w + γ (kcSrcWire125 ⟨w.val - 33, by omega⟩)
    else
      β w
theorem cCopyKc16_eval_eq_applyCopyKc (β : BitAssignment 125) :
    cCopyKc16.eval β = applyCopyKc β β := by
  funext w
  unfold cCopyKc16 applyCopyKc
  exact cCopyKc16Aux_eval β 16 le_rfl w
theorem applyCopyKc_not_kc (γ β : BitAssignment 125) (q : Wire 125)
    (hq : ¬ (33 ≤ q.val ∧ q.val < 49)) : applyCopyKc γ β q = β q := by
  dsimp [applyCopyKc]; rw [dite_eq_right hq]
theorem update_applyCopyKc (γ β : BitAssignment 125) (q : Wire 125)
    (hq : ¬ (33 ≤ q.val ∧ q.val < 49)) (v : ZMod 2) :
    Function.update (applyCopyKc γ β) q v = applyCopyKc γ (Function.update β q v) := by
  funext w
  by_cases hw : w = q
  · subst hw
    rw [Function.update_self, applyCopyKc_not_kc _ _ w hq, Function.update_self]
  · rw [Function.update_of_ne hw]
    dsimp [applyCopyKc]
    split_ifs <;> rw [Function.update_of_ne hw]
def noTouch33_49 : RawSsa 125 → Bool
  | .done => true
  | .x q rest => decide (¬ (33 ≤ q.val ∧ q.val < 49)) && noTouch33_49 rest
  | .cnot c t _ rest =>
      decide (¬ (33 ≤ c.val ∧ c.val < 49)) &&
      decide (¬ (33 ≤ t.val ∧ t.val < 49)) &&
      noTouch33_49 rest
  | .skipZero rest => noTouch33_49 rest
  | .andClean anc c₁ c₂ _ _ _ rest =>
      decide (¬ (33 ≤ anc.val ∧ anc.val < 49)) &&
      decide (¬ (33 ≤ c₁.val ∧ c₁.val < 49)) &&
      decide (¬ (33 ≤ c₂.val ∧ c₂.val < 49)) &&
      noTouch33_49 rest
theorem toTempCtx_cCopyKc16_spec :
    ∀ (p : RawSsa 125) {cur endCur : ℕ},
      RawSsa.Wf cur endCur p →
      endCur ≤ 125 →
      49 ≤ cur →
      noTouch33_49 p = true →
      (∀ β : BitAssignment 125, cleanRem 125 (125 - cur) β →
        (rawToTempPhase (.cliff cCopyKc16) p).evalBits β = applyCopyKc (p.eval β) β) ∧
      ValidCleanRem 125 (125 - cur) (rawToTempPhase (.cliff cCopyKc16) p)
  | .done, _, _, _, _, _, _ => ⟨fun β _ ↦ cCopyKc16_eval_eq_applyCopyKc β, trivial⟩
  | .x q rest, cur, _, ⟨hq, hwf⟩, hEnd, h49, hnt => by
      simp only [noTouch33_49, Bool.and_eq_true, decide_eq_true_eq] at hnt
      obtain ⟨hq_nk, hntR⟩ := hnt
      obtain ⟨ihBits, ihVal⟩ := toTempCtx_cCopyKc16_spec rest hwf hEnd h49 hntR
      have hPres : ∀ β : BitAssignment 125, cleanRem 125 (125 - cur) β →
          cleanRem 125 (125 - cur) (Function.update β q (β q + 1)) := by
        intro β hβ w hw
        have hne : w ≠ q := wire_ne_of_gt (by omega)
        rw [Function.update_of_ne hne]; exact hβ w hw
      refine ⟨fun β hβ ↦ ?_, ?_⟩
      · dsimp only [rawToTempPhase, TempPhaseProg.evalBits, CliffProg.eval, RawSsa.eval]
        let β' := Function.update β q (β q + 1)
        change Function.update ((rawToTempPhase (.cliff cCopyKc16) rest).evalBits β') q
          ((rawToTempPhase (.cliff cCopyKc16) rest).evalBits β' q + 1) =
          applyCopyKc (rest.eval β') β
        rw [ihBits β' (hPres β hβ), applyCopyKc_not_kc _ _ q hq_nk,
          update_applyCopyKc _ _ q hq_nk]
        congr 1; funext w
        by_cases hw : w = q
        · subst hw
          dsimp [β']; rw [Function.update_self, Function.update_self, add_assoc,
            CharTwo.add_self_eq_zero, add_zero]
        · dsimp [β']; rw [Function.update_of_ne hw, Function.update_of_ne hw]
      · dsimp only [rawToTempPhase, ValidCleanRem]
        refine ⟨125 - cur, Nat.sub_le 125 cur, trivial, ⟨125 - cur, Nat.sub_le 125 cur, ihVal,
          trivial, fun β₁ hβ₁ ↦ ?_⟩, fun β hβ ↦ hPres β hβ⟩
        rw [ihBits β₁ hβ₁]
        intro w hw
        rw [applyCopyKc_not_kc _ _ w (by omega)]
        exact hβ₁ w hw
  | .cnot c t hct rest, cur, _, ⟨hc, ht, hwf⟩, hEnd, h49, hnt => by
      simp only [noTouch33_49, Bool.and_eq_true, decide_eq_true_eq, and_assoc] at hnt
      obtain ⟨hc_nk, ht_nk, hntR⟩ := hnt
      obtain ⟨ihBits, ihVal⟩ := toTempCtx_cCopyKc16_spec rest hwf hEnd h49 hntR
      have hPres : ∀ β : BitAssignment 125, cleanRem 125 (125 - cur) β →
          cleanRem 125 (125 - cur) (Function.update β t (β t + β c)) := by
        intro β hβ w hw
        have hne : w ≠ t := wire_ne_of_gt (by omega)
        rw [Function.update_of_ne hne]; exact hβ w hw
      refine ⟨fun β hβ ↦ ?_, ?_⟩
      · dsimp only [rawToTempPhase, TempPhaseProg.evalBits, CliffProg.eval, RawSsa.eval]
        let β' := Function.update β t (β t + β c)
        change Function.update ((rawToTempPhase (.cliff cCopyKc16) rest).evalBits β') t
          ((rawToTempPhase (.cliff cCopyKc16) rest).evalBits β' t + (rawToTempPhase (.cliff
          cCopyKc16) rest).evalBits β' c) = applyCopyKc (rest.eval β') β
        rw [ihBits β' (hPres β hβ), applyCopyKc_not_kc _ _ t ht_nk,
          applyCopyKc_not_kc _ _ c hc_nk, update_applyCopyKc _ _ t ht_nk]
        congr 1; funext w
        by_cases hw : w = t
        · subst hw
          dsimp [β']; rw [Function.update_self, Function.update_self, Function.update_of_ne hct,
            add_assoc, CharTwo.add_self_eq_zero, add_zero]
        · dsimp [β']; rw [Function.update_of_ne hw, Function.update_of_ne hw]
      · dsimp only [rawToTempPhase, ValidCleanRem]
        refine ⟨125 - cur, Nat.sub_le 125 cur, trivial, ⟨125 - cur, Nat.sub_le 125 cur, ihVal,
          trivial, fun β₁ hβ₁ ↦ ?_⟩, fun β hβ ↦ hPres β hβ⟩
        rw [ihBits β₁ hβ₁]
        intro w hw
        rw [applyCopyKc_not_kc _ _ w (by omega)]
        exact hβ₁ w hw
  | .skipZero rest, cur, _, ⟨hcur, hwf⟩, hEnd, h49, hnt => by
      simp only [noTouch33_49] at hnt
      obtain ⟨ihBits, ihVal⟩ := toTempCtx_cCopyKc16_spec rest hwf hEnd (by omega) hnt
      have hCleanSub : ∀ β : BitAssignment 125, cleanRem 125 (125 - cur) β → cleanRem 125
          (125 - (cur + 1)) β := fun β hβ w hw ↦ hβ w (by omega)
      exact ⟨fun β hβ ↦ ihBits β (hCleanSub β hβ), validCleanRem_mono_shared (by omega) ihVal⟩
  | .andClean anc c₁ c₂ h₁₂ hc1a hc2a rest, cur, _, ⟨hanc_val, h₁, h₂, hwf⟩, hEnd, h49, hnt => by
      simp only [noTouch33_49, Bool.and_eq_true, decide_eq_true_eq, and_assoc] at hnt
      obtain ⟨hanc_nk, hc1_nk, hc2_nk, hntR⟩ := hnt
      obtain ⟨ihBits, ihVal⟩ := toTempCtx_cCopyKc16_spec rest hwf hEnd (by omega) hntR
      have hPres : ∀ β : BitAssignment 125, cleanRem 125 (125 - cur) β →
          cleanRem 125 (125 - (cur + 1)) (Function.update β anc (β anc + β c₁ * β c₂)) := by
        intro β hβ w hw
        have hne : w ≠ anc := wire_ne_of_gt (by omega)
        rw [Function.update_of_ne hne]; exact hβ w (by omega)
      refine ⟨fun β hβ ↦ ?_, ?_⟩
      · dsimp only [rawToTempPhase, TempPhaseProg.evalBits, RawSsa.eval]
        let β' := Function.update β anc (β anc + β c₁ * β c₂)
        change Function.update ((rawToTempPhase (.cliff cCopyKc16) rest).evalBits β') anc
          ((rawToTempPhase (.cliff cCopyKc16) rest).evalBits β' anc + (rawToTempPhase (.cliff
          cCopyKc16) rest).evalBits β' c₁ * (rawToTempPhase (.cliff cCopyKc16) rest).evalBits
          β' c₂) = applyCopyKc (rest.eval β') β
        rw [ihBits β' (hPres β hβ), applyCopyKc_not_kc _ _ anc hanc_nk,
          applyCopyKc_not_kc _ _ c₁ hc1_nk, applyCopyKc_not_kc _ _ c₂ hc2_nk,
          update_applyCopyKc _ _ anc hanc_nk]
        congr 1; funext w
        by_cases hw : w = anc
        · subst hw
          dsimp [β']
          rw [Function.update_self, Function.update_self, Function.update_of_ne hc1a,
            Function.update_of_ne hc2a, add_assoc, CharTwo.add_self_eq_zero, add_zero]
        · dsimp [β']; rw [Function.update_of_ne hw, Function.update_of_ne hw]
      · dsimp only [rawToTempPhase, ValidCleanRem]
        refine ⟨by omega, by simpa only [hanc_val] using ihVal, fun β₁ hβ₁ ↦ ?_⟩
        have hβ₁' : cleanRem 125 (125 - (cur + 1)) β₁ := by simpa only [hanc_val] using hβ₁
        rw [ihBits β₁ hβ₁']
        exact ⟨applyCopyKc_not_kc _ _ c₁ hc1_nk, applyCopyKc_not_kc _ _ c₂ hc2_nk,
          applyCopyKc_not_kc _ _ anc hanc_nk⟩
theorem ssaCastEnd_raw {M cur c₁ c₂ : ℕ} (h : c₁ = c₂) (P : SsaProg M cur c₁) :
    (ssaCastEnd h P).raw = P.raw := by
  subst h; rfl
theorem microSlotWire_not_33_49 {nIn : ℕ} (inW : Fin nIn → Wire 125) (cur₀ : ℕ)
    (hin_nt : ∀ i : Fin nIn, ¬ (33 ≤ (inW i).val ∧ (inW i).val < 49))
    (h49 : 49 ≤ cur₀) (s : ℕ) (hb : nIn ≤ s → cur₀ + (s - nIn) < 125) :
    ¬ (33 ≤ (microSlotWire inW cur₀ s hb).val ∧ (microSlotWire inW cur₀ s hb).val < 49) := by
  by_cases hs : s < nIn
  · rw [microSlotWire_lt_in inW cur₀ s hs]
    exact hin_nt ⟨s, hs⟩
  · rw [microSlotWire_ge_in inW cur₀ s (by omega)]
    dsimp; omega
theorem ssaMicroRun_noTouch33_49 {nIn : ℕ} (inW : Fin nIn → Wire 125)
    (hin_inj : Function.Injective inW) (cur₀ : ℕ) (hin_lt : ∀ i, (inW i).val < cur₀)
    (hin_nt : ∀ i : Fin nIn, ¬ (33 ≤ (inW i).val ∧ (inW i).val < 49))
    (h49 : 49 ≤ cur₀) :
    ∀ (ops : List MicroStep) (top cur : ℕ) (hrel : nIn + cur = cur₀ + top ∧ nIn ≤ top)
      (_hcur₀ : cur₀ ≤ cur)
      (hv : microValid top ops = true) (hM : microEnd cur ops ≤ 125),
      noTouch33_49 (ssaMicroRun inW hin_inj cur₀ hin_lt top cur hrel ops hv hM).raw = true
  | [], _, _, _, _, _, _ => rfl
  | .nW a :: rest, top, cur, hrel, hcur₀, hv, hM => by
      dsimp only [ssaMicroRun, SsaProg.x, noTouch33_49]
      rw [Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨microSlotWire_not_33_49 inW cur₀ hin_nt h49 a _, ssaMicroRun_noTouch33_49 inW
        hin_inj cur₀ hin_lt hin_nt h49 rest top cur hrel hcur₀ (microValid_nW hv).2 hM⟩
  | .cW a b :: rest, top, cur, hrel, hcur₀, hv, hM => by
      dsimp only [ssaMicroRun, SsaProg.cnot, noTouch33_49]
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨⟨microSlotWire_not_33_49 inW cur₀ hin_nt h49 a _, microSlotWire_not_33_49 inW
        cur₀ hin_nt h49 b _⟩, ssaMicroRun_noTouch33_49 inW hin_inj cur₀ hin_lt hin_nt h49 rest
        top cur hrel hcur₀ (microValid_cW hv).2.2.2 hM⟩
  | .aW a b :: rest, top, cur, hrel, hcur₀, hv, hM => by
      dsimp only [ssaMicroRun, SsaProg.andClean, noTouch33_49]
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      refine ⟨⟨⟨by omega, microSlotWire_not_33_49 inW cur₀ hin_nt h49 a _⟩,
        microSlotWire_not_33_49 inW cur₀ hin_nt h49 b _⟩,
        ssaMicroRun_noTouch33_49 inW hin_inj cur₀ hin_lt hin_nt h49 rest (top + 1) (cur + 1)
          _ (by omega) (microValid_aW hv).2.2.2 hM⟩
theorem inW38_not_33_49 : ∀ i : Fin 38, ¬ (33 ≤ (inW38 i).val ∧ (inW38 i).val < 49) := by
  decide
theorem ssaStage1Rest_noTouch33_49 : noTouch33_49 ssaStage1Rest.raw = true := by
  unfold ssaStage1Rest
  rw [ssaCastEnd_raw]
  exact ssaMicroRun_noTouch33_49 inW38 inW38_inj 87 inW38_lt inW38_not_33_49 (by decide)
    s1Kc68RestOps 38 87 ⟨by decide, le_rfl⟩ le_rfl s1Kc68Rest_meta.1 (by rw [s1Kc68Rest_end])
theorem pStage1Copy125_validCleanRem : ValidCleanRem 125 38 pStage1Copy125 := by
  unfold pStage1Copy125
  exact (toTempCtx_cCopyKc16_spec ssaStage1Rest.raw ssaStage1Rest.wf le_rfl (by decide)
    ssaStage1Rest_noTouch33_49).2
theorem pStage1Copy125_evalSign (β : BitAssignment 125) : pStage1Copy125.evalSign β = 0 :=
    rawToTempPhase_cliff_evalSign cCopyKc16 ssaStage1Rest.raw β
def s1Kc68Take30Ops : List MicroStep := s1Kc68Ops.take 30
def stateAfterTake30 (c8 : ℕ) : List Bool :=
  evalMicroList 8 s1Kc68Take30Ops (initBoolList 8 76 c8)
theorem length_evalMicroList :
    ∀ (ops : List MicroStep) (top : ℕ) (st : List Bool),
      (evalMicroList top ops st).length = st.length
  | [], _, _ => rfl
  | .nW a :: rest, top, st =>
      (length_evalMicroList rest top _).trans (length_setBoolAt st a _)
  | .cW _ b :: rest, top, st =>
      (length_evalMicroList rest top _).trans (length_setBoolAt st b _)
  | .aW _ _ :: rest, top, st =>
      (length_evalMicroList rest (top + 1) _).trans (length_setBoolAt st top _)

theorem evalMicroList_append :
    ∀ (ops₁ ops₂ : List MicroStep) (top : ℕ) (st : List Bool),
      evalMicroList top (ops₁ ++ ops₂) st =
        evalMicroList (top + microAllocs ops₁) ops₂ (evalMicroList top ops₁ st)
  | [], _, _, _ => by simp [evalMicroList, microAllocs]
  | .nW a :: rest, ops₂, top, st =>
      evalMicroList_append rest ops₂ top (setBoolAt st a (!getBoolAt st a))
  | .cW a b :: rest, ops₂, top, st =>
      evalMicroList_append rest ops₂ top (setBoolAt st b (xor (getBoolAt st b) (getBoolAt st a)))
  | .aW a b :: rest, ops₂, top, st => by
      dsimp only [List.cons_append, evalMicroList, microAllocs]
      rw [evalMicroList_append rest ops₂ (top + 1)]
      exact congrArg (fun k ↦ evalMicroList k ops₂ _) (by omega)
theorem evalSIMD_agree_le (nRows r : ℕ) (hr : r < nRows) (ops : List MicroStep) : ∀ (top : ℕ)
    (t : PTree ℕ) (st : List Bool), PTree.hasDepth 8 t → microValid top ops = true → top +
    microAllocs ops ≤ st.length → st.length ≤ 256 →
    (∀ i < st.length, (pget 0 8 t i).testBit r = getBoolAt st i) → ∀ i < st.length, (pget 0 8
    (evalSIMD (Nat.sub (Nat.pow 2 nRows) 1) top ops t) i).testBit r = getBoolAt
    (evalMicroList top ops st) i := by
  have h256 : (2 ^ 8 : ℕ) = 256 := by decide
  induction ops with
  | nil =>
      intro top t st _ _ _ _ hagree i hi
      exact hagree i hi
  | cons op rest ih =>
      intro top t st hPt hv halloc hlen hagree i hi
      cases op with
      | nW a =>
          obtain ⟨ha, hvR⟩ := microValid_nW hv
          dsimp only [microAllocs] at halloc
          dsimp only [evalSIMD, evalMicroList]
          rw [psetNat_eq, PTree.withVal_eq]
          have hlen' : (setBoolAt st a (!getBoolAt st a)).length = st.length := length_setBoolAt st
            a _
          refine ih top _ _ (pset_hasDepth 8 t hPt a (by rw [h256]; omega) _) hvR
            (by rw [hlen']; exact halloc) (by rw [hlen']; exact hlen) (fun j hj ↦ ?_) i (by
              rw [hlen']; exact hi)
          rw [hlen'] at hj
          rw [pget_pset 0 8 t hPt a (by rw [h256]; omega) j (by rw [h256]; omega),
            getBoolAt_setBoolAt st a j (by omega)]
          by_cases hja : j = a
          · subst hja
            simp only [↓reduceIte]
            change ((Nat.sub (Nat.pow 2 nRows) 1) ^^^ pget 0 8 t j).testBit r = !getBoolAt st j
            rw [Nat.testBit_xor, testBit_allMask, decide_eq_true hr, hagree j (by omega)]
            cases getBoolAt st j
            · rfl
            · rfl
          · simp [hja, hagree j hj]
      | cW a b =>
          obtain ⟨ha, hb, _, hvR⟩ := microValid_cW hv
          dsimp only [microAllocs] at halloc
          dsimp only [evalSIMD, evalMicroList]
          rw [psetNat_eq, PTree.withVal_eq]
          have hlen' : (setBoolAt st b (xor (getBoolAt st b) (getBoolAt st a))).length =
            st.length :=
            length_setBoolAt st b _
          refine ih top _ _ (pset_hasDepth 8 t hPt b (by rw [h256]; omega) _) hvR
            (by rw [hlen']; exact halloc) (by rw [hlen']; exact hlen) (fun j hj ↦ ?_) i (by
              rw [hlen']; exact hi)
          rw [hlen'] at hj
          rw [pget_pset 0 8 t hPt b (by rw [h256]; omega) j (by rw [h256]; omega),
            getBoolAt_setBoolAt st b j (by omega)]
          by_cases hjb : j = b
          · subst hjb
            simp only [↓reduceIte]
            change (pget 0 8 t j ^^^ pget 0 8 t a).testBit r = xor (getBoolAt st j) (getBoolAt st a)
            rw [Nat.testBit_xor, hagree j (by omega), hagree a (by omega)]
          · simp [hjb, hagree j hj]
      | aW a b =>
          obtain ⟨ha, hb, _, hvR⟩ := microValid_aW hv
          dsimp only [microAllocs] at halloc
          dsimp only [evalSIMD, evalMicroList]
          rw [psetNat_eq, PTree.withVal_eq]
          have hlen' : (setBoolAt st top (getBoolAt st a && getBoolAt st b)).length = st.length :=
            length_setBoolAt st top _
          refine ih (top + 1) _ _ (pset_hasDepth 8 t hPt top (by rw [h256]; omega) _) hvR
            (by rw [hlen']; omega) (by rw [hlen']; exact hlen) (fun j hj ↦ ?_) i (by
              rw [hlen']; exact hi)
          rw [hlen'] at hj
          rw [pget_pset 0 8 t hPt top (by rw [h256]; omega) j (by rw [h256]; omega),
            getBoolAt_setBoolAt st top j (by omega)]
          by_cases hjt : j = top
          · subst hjt
            simp only [↓reduceIte]
            change (pget 0 8 t a &&& pget 0 8 t b).testBit r = (getBoolAt st a && getBoolAt st b)
            rw [Nat.testBit_and, hagree a (by omega), hagree b (by omega)]
          · simp [hjt, hagree j hj]
theorem s1Kc68Take30_meta :
    microValid 8 s1Kc68Take30Ops = true ∧ microAllocs s1Kc68Take30Ops = 30 := by
  decide +kernel
theorem simdRun_take30_testBit_eq (c8 : Fin 256) (s : Fin 38) :
    (pget 0 8 (simdRun 256 8 s1Kc68Take30Ops) s.val).testBit c8.val =
      getBoolAt (stateAfterTake30 c8.val) s.val := by
  dsimp only [simdRun, stateAfterTake30]
  have hmask : allMaskFast 256 1 = Nat.sub (Nat.pow 2 256) 1 := by
    rw [allMaskFast_eq, one_mul]
    rfl
  rw [hmask]
  have h256 : (2 ^ 8 : ℕ) = 256 := by decide
  obtain ⟨hP0, hG0⟩ := initColsFast_spec 256 8 (by decide) (pconst 0 8) (pconst_hasDepth 0 8)
  have hlen_st : (initBoolList 8 76 c8.val).length = 76 := length_mkBoolList 8 c8.val 0 76
  refine evalSIMD_agree_le 256 c8.val c8.isLt s1Kc68Take30Ops 8 _ (initBoolList 8 76 c8.val)
    hP0 s1Kc68Take30_meta.1 (by rw [s1Kc68Take30_meta.2, hlen_st]; decide)
    (by rw [hlen_st]; decide) (fun i hi ↦ ?_) s.val (by rw [hlen_st]; omega)
  rw [hlen_st] at hi
  rw [hG0 i (by omega)]
  dsimp only [initBoolList]
  rw [getBoolAt_mkBoolList 8 c8.val 0 76 i hi]
  simp only [zero_add]
  by_cases hin : i < 8
  · simp only [hin, ↓reduceIte]; rw [testBit_colMaskFast, decide_eq_true c8.isLt]; simp
  · simp only [hin, ↓reduceIte]; rw [pget_pconst 0 8 i (by rw [h256]; omega)]; simp

def c8Of33 (x : BitAssignment 33) : Fin 256 :=
  ⟨bitsVal (fun d : Fin 8 ↦ x ⟨25 + d.val, by omega⟩), bitsVal_lt_two_pow _⟩
def lo5Of33 (x : BitAssignment 33) : Fin 32 := ⟨(c8Of33 x).val % 32, Nat.mod_lt _ (by decide)⟩
def hi3Of33 (x : BitAssignment 33) : Fin 8 :=
  ⟨(c8Of33 x).val / 32, by have := (c8Of33 x).isLt; omega⟩
theorem zmod2_ite_pow_eq (z : ZMod 2) (k : ℕ) :
    (if z = 1 then 2 ^ k else 0) = 2 ^ k * z.val := by
  rcases bit_cases z with rfl | rfl <;> simp
theorem idxValPrefix_eq_sum {D n : ℕ} (wBit : Fin D → Wire n) (β : BitAssignment n) :
    ∀ (k : ℕ) (hk : k ≤ D),
      idxValPrefix wBit β k hk =
        ∑ i : Fin k, 2 ^ i.val * (β (wBit ⟨i.val, lt_of_lt_of_le i.isLt hk⟩)).val
  | 0, _ => rfl
  | k + 1, hk => by
      dsimp only [idxValPrefix]
      rw [idxValPrefix_eq_sum wBit β k (Nat.le_of_succ_le hk), zmod2_ite_pow_eq,
        Fin.sum_univ_castSucc]
      rfl
theorem idxValD_eq_bitsVal {D n : ℕ} (wBit : Fin D → Wire n) (β : BitAssignment n) :
    idxValD wBit β = bitsVal (fun d : Fin D ↦ β (wBit d)) := by
  change idxValPrefix wBit β D le_rfl = ∑ i : Fin D, (β (wBit i)).val * 2 ^ i.val
  rw [idxValPrefix_eq_sum wBit β D le_rfl]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [show (⟨i.val, lt_of_lt_of_le i.isLt le_rfl⟩ : Fin D) = i from Fin.ext rfl, mul_comm]
theorem idxValD_lo5_eq (x : BitAssignment 33) :
    idxValD (fun d : Fin 5 ↦ ⟨25 + d.val, by omega⟩) x = (lo5Of33 x).val := by
  rw [idxValD_eq_bitsVal]
  refine bitsVal_eq_of_testBit _ (lo5Of33 x).val (lo5Of33 x).isLt fun d ↦ ?_
  have hmod : (lo5Of33 x).val.testBit d.val = (c8Of33 x).val.testBit d.val := by
    change ((c8Of33 x).val % 2 ^ 5).testBit d.val = _
    rw [testBit_mod_two_powAux 5 (c8Of33 x).val d.val, decide_eq_true d.isLt, Bool.true_and]
  have hbit := bitsVal_testBit_eq (fun i : Fin 8 ↦ x ⟨25 + i.val, by omega⟩) ⟨d.val, by omega⟩
  change (c8Of33 x).val.testBit d.val = _ at hbit
  rw [hmod, hbit]
  rcases bit_cases (x ⟨25 + d.val, by omega⟩) with hx | hx <;> simp [hx]
theorem idxValD_hi3_eq (x : BitAssignment 33) :
    idxValD (fun d : Fin 3 ↦ ⟨30 + d.val, by omega⟩) x = (hi3Of33 x).val := by
  rw [idxValD_eq_bitsVal]
  refine bitsVal_eq_of_testBit _ (hi3Of33 x).val (hi3Of33 x).isLt fun d ↦ ?_
  have hdiv : (hi3Of33 x).val.testBit d.val = (c8Of33 x).val.testBit (5 + d.val) :=
    testBit_div_two_powAux (c8Of33 x).val 5 d.val
  have hbit := bitsVal_testBit_eq (fun i : Fin 8 ↦ x ⟨25 + i.val, by omega⟩) ⟨5 + d.val, by omega⟩
  change (c8Of33 x).val.testBit (5 + d.val) = _ at hbit
  rw [hdiv, hbit]
  have hfin : (⟨25 + (5 + d.val), by omega⟩ : Wire 33) = ⟨30 + d.val, by omega⟩ := by
    ext; dsimp; omega
  rw [hfin]
  rcases bit_cases (x ⟨30 + d.val, by omega⟩) with hx | hx <;> simp [hx]
def γ2_125 (x : BitAssignment 33) : BitAssignment 125 :=
  fun w ↦
    if hw : w.val < 33 then x ⟨w.val, hw⟩
    else if w.val < 49 then 0
    else if hw8 : w.val < 56 then
      mobiusTargetBits (hi3Of33 x) ⟨w.val - 48, by omega⟩
    else if hw32 : w.val < 87 then
      mobiusTargetBits (lo5Of33 x) ⟨w.val - 55, by omega⟩
    else 0
def γ2SlotBool (c8 s : ℕ) : Bool :=
  if s < 8 then fastBitSmall c8 s
  else
    let w := getNatAt inW38List s
    let hi3 := c8 / 32
    let lo5 := c8 % 32
    if w < 49 then false
    else if w < 56 then
      let m := w - 48
      !Nat.beq m 0 && Nat.beq (Nat.land m hi3) m
    else if w < 87 then
      let m := w - 55
      !Nat.beq m 0 && Nat.beq (Nat.land m lo5) m
    else false
def checkTake30Cert : Bool := PTree.withVal (simdRun 256 8 s1Kc68Take30Ops) fun t ↦ allBelow
    38 fun s ↦ Nat.beq (pget 0 8 t s) (packPredLoop (fun c8 ↦ γ2SlotBool c8 s) 256 0 1 0)
theorem checkTake30Cert_true : checkTake30Cert = true := by decide +kernel
theorem stateAfterTake30_eq_γ2SlotBool (c8 : Fin 256) (s : Fin 38) :
    getBoolAt (stateAfterTake30 c8.val) s.val = γ2SlotBool c8.val s.val := by
  rw [← simdRun_take30_testBit_eq c8 s]
  have hcert := checkTake30Cert_true
  dsimp only [checkTake30Cert] at hcert
  rw [PTree.withVal_eq] at hcert
  have hs_eq := (nat_beq_iff _ _).mp ((allBelow_iff 38 _).mp hcert s.val s.isLt)
  rw [hs_eq, testBit_packPredLoop_zero _ 256 c8.val c8.isLt]

theorem γ2_125_eq_γ2SlotBool (c8 : Fin 256) (s : Fin 38) (hs : 8 ≤ s.val) :
    (let w := (inW38 s).val
     let hi3 : Fin 8 := ⟨c8.val / 32, by have := c8.isLt; omega⟩
     let lo5 : Fin 32 := ⟨c8.val % 32, Nat.mod_lt _ (by decide)⟩
     if w < 49 then (0 : ZMod 2)
     else if hw8 : w < 56 then
       mobiusTargetBits hi3 ⟨w - 48, by omega⟩
     else if hw32 : w < 87 then
       mobiusTargetBits lo5 ⟨w - 55, by omega⟩
     else 0) = b2z (γ2SlotBool c8.val s.val) := by
  revert c8 s hs; decide +kernel
theorem γ2_125_inW38_for_all (x : BitAssignment 33) (s : Fin 38) :
    γ2_125 x (inW38 s) = b2z (getBoolAt (stateAfterTake30 (c8Of33 x).val) s.val) := by
  rw [stateAfterTake30_eq_γ2SlotBool (c8Of33 x) s]
  by_cases hs8 : s.val < 8
  · have hw_eq : (inW38 s).val = 25 + s.val := by revert s hs8; decide
    have hw33 : (inW38 s).val < 33 := by omega
    dsimp [γ2_125, γ2SlotBool]
    rw [dite_eq_left hw33, ite_eq_left hs8, fastBitSmall_eq_testBit]
    have hbit := bitsVal_testBit_eq (fun i : Fin 8 ↦ x ⟨25 + i.val, by omega⟩) ⟨s.val, hs8⟩
    change (c8Of33 x).val.testBit s.val = _ at hbit
    rw [hbit]
    have hfin : (⟨(inW38 s).val, hw33⟩ : Wire 33) = ⟨25 + s.val, by omega⟩ :=
      Fin.ext hw_eq
    rw [hfin]
    rcases bit_cases (x ⟨25 + s.val, by omega⟩) with hx | hx <;> rw [hx] <;> rfl
  · have hs_ge : 8 ≤ s.val := Nat.le_of_not_lt hs8
    have hnot33 : ¬ (inW38 s).val < 33 := by revert s hs8; decide
    dsimp [γ2_125]
    rw [dite_eq_right hnot33]
    exact γ2_125_eq_γ2SlotBool (c8Of33 x) s hs_ge
theorem s1Kc68_split_eq : s1Kc68Take30Ops ++ s1Kc68RestOps = s1Kc68Ops :=
  List.take_append_drop 30 s1Kc68Ops
theorem ssaStage1Rest_spec_γ2 (x : BitAssignment 33) (j : Fin 16) :
    ssaStage1Rest.eval (γ2_125 x) (kcSrcWire125 j) =
      b2z ((getNatAt kcTable49168List (c8Of33 x).val).testBit j.val) := by
  have hs_bnd : getNatAt s1Kc68OutSlots j.val < 76 := by revert j; decide
  have hslot_lt : getNatAt s1Kc68OutSlots j.val < 38 + microAllocs s1Kc68RestOps := by
    rw [s1Kc68Rest_meta.2.1]
    exact hs_bnd
  let c8 := c8Of33 x
  have hlen_eq : (stateAfterTake30 c8.val).length = 38 + microAllocs s1Kc68RestOps := by
    dsimp [stateAfterTake30, initBoolList]
    rw [length_evalMicroList, length_mkBoolList, s1Kc68Rest_meta.2.1]
  have hcl : ∀ q : Wire 125, 87 ≤ q.val → γ2_125 x q = 0 := fun q hq ↦ by
    dsimp [γ2_125]
    rw [dite_eq_right (by omega), ite_eq_right (by omega),
        dite_eq_right (by omega), dite_eq_right (by omega)]
  have hst : ∀ (s : ℕ) (hs : s < 38),
      γ2_125 x (microSlotWire inW38 87 s (fun hle ↦ absurd hle (Nat.not_le_of_lt hs))) =
        b2z (getBoolAt (stateAfterTake30 c8.val) s) := fun s hs ↦ by
    rw [microSlotWire_lt_in inW38 87 s hs]
    exact γ2_125_inW38_for_all x ⟨s, hs⟩
  obtain ⟨_, hEv⟩ := ssaMicroRun_spec inW38 inW38_inj 87 inW38_lt s1Kc68RestOps
    38 87 ⟨by decide, le_rfl⟩ s1Kc68Rest_meta.1 (by rw [s1Kc68Rest_end])
  obtain ⟨_, _, hsO⟩ := hEv (γ2_125 x) (stateAfterTake30 c8.val) hcl hlen_eq hst
  unfold ssaStage1Rest
  simp only [ssaCastEnd_eval]
  have ho := hsO (getNatAt s1Kc68OutSlots j.val) hslot_lt
  have hev_full : evalMicroList 38 s1Kc68RestOps (stateAfterTake30 c8.val) =
      evalMicroList 8 s1Kc68Ops (initBoolList 8 76 c8.val) := by
    dsimp [stateAfterTake30]
    have happ := evalMicroList_append s1Kc68Take30Ops s1Kc68RestOps 8 (initBoolList 8 76 c8.val)
    rw [s1Kc68_split_eq, s1Kc68Take30_meta.2] at happ
    exact happ.symm
  rw [hev_full] at ho
  have hcert := checkStage1Cert_true
  dsimp only [checkStage1Cert] at hcert
  rw [PTree.withVal_eq] at hcert
  obtain ⟨_, hOut⟩ := Bool.and_eq_true_iff.mp hcert
  have hj_eq := (nat_beq_iff _ _).mp ((allBelow_iff 16 _).mp hOut j.val j.isLt)
  have hsimd := simdRun_testBit_eq 256 8 76 c8.val (getNatAt s1Kc68OutSlots j.val) s1Kc68Ops
    (by decide) c8.isLt hs_bnd s1Kc68_meta.1 (by rw [s1Kc68_meta.2.1])
  rw [hj_eq, testBit_packPredLoop_zero _ 256 c8.val c8.isLt, fastBitSmall_eq_testBit] at hsimd
  exact ho.trans (congrArg b2z hsimd.symm)
theorem pStage1Copy125_evalBits_γ2 (x : BitAssignment 33) (w : Wire 125) :
    pStage1Copy125.evalBits (γ2_125 x) w =
      if 33 ≤ w.val ∧ w.val < 49 then
        b2z ((getNatAt kcTable49168List (c8Of33 x).val).testBit (w.val - 33))
      else
        γ2_125 x w := by
  have hcl : cleanRem 125 (125 - 87) (γ2_125 x) := fun q hq ↦ by
    dsimp [γ2_125]
    rw [dite_eq_right (by omega), ite_eq_right (by omega),
        dite_eq_right (by omega), dite_eq_right (by omega)]
  have hBits := (toTempCtx_cCopyKc16_spec ssaStage1Rest.raw ssaStage1Rest.wf le_rfl (by decide)
    ssaStage1Rest_noTouch33_49).1 (γ2_125 x) hcl
  change (rawToTempPhase (.cliff cCopyKc16) ssaStage1Rest.raw).evalBits (γ2_125 x) w = _
  rw [hBits]
  dsimp [applyCopyKc]
  by_cases hkc : 33 ≤ w.val ∧ w.val < 49
  · rw [dite_eq_left hkc, ite_eq_left hkc]
    have h0 : γ2_125 x w = 0 := by
      dsimp [γ2_125]; rw [dite_eq_right (by omega), ite_eq_left hkc.2]
    rw [h0, zero_add]
    exact ssaStage1Rest_spec_γ2 x ⟨w.val - 33, by omega⟩
  · rw [dite_eq_right hkc, ite_eq_right hkc]

attribute [local irreducible] ssaStage1Rest pStage1Copy125
def pad125To198 (γ : BitAssignment 125) : BitAssignment 198 :=
  fun w ↦ if h : w.val < 125 then γ ⟨w.val, h⟩ else 0
def idxLo5Loc (d : Fin 5) : Wire 198 := ⟨25 + d.val, by omega⟩
def idxHi3Loc (d : Fin 3) : Wire 198 := ⟨30 + d.val, by omega⟩
def kc16Loc (j : Fin 16) : Wire 198 := ⟨33 + j.val, by omega⟩
def out8Loc (r : Fin 8) : Wire 198 :=
  if r.val = 0 then ⟨87, by decide⟩ else ⟨48 + r.val, by omega⟩
def out32Loc (q : Fin 32) : Wire 198 :=
  if q.val = 0 then ⟨88, by decide⟩ else ⟨55 + q.val, by omega⟩
def qEncLoc : Wire 198 := ⟨89, by decide⟩
theorem out8Loc_inj : Function.Injective out8Loc := by
  intro i j; revert i j; decide
theorem out32Loc_inj : Function.Injective out32Loc := by
  intro i j; revert i j; decide
def rOh8In198 : QRegister 8 198 := ⟨⟨out8Loc, out8Loc_inj⟩⟩
def rOh32In198 : QRegister 32 198 := ⟨⟨out32Loc, out32Loc_inj⟩⟩
def r125In198 : QRegister 125 198 := QRegister.block 0 125 (by decide)
def r49In198 : QRegister 49 198 := QRegister.block 0 49 (by decide)
@[simp] theorem r125In198_apply (i : Fin 125) : r125In198 i = ⟨i.val, by omega⟩ :=
  Fin.ext (Nat.zero_add i.val)
@[simp] theorem r49In198_apply (i : Fin 49) : r49In198 i = ⟨i.val, by omega⟩ :=
  Fin.ext (Nat.zero_add i.val)
theorem wUncondDisj8_198 : WUncondDisjProp idxHi3Loc out8Loc qEncLoc := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide
theorem wUncondDisj32_198 : WUncondDisjProp idxLo5Loc out32Loc qEncLoc := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide
theorem wUncondDisj8_lift {n : ℕ} (rComb : QRegister 198 n) :
    WUncondDisjProp (fun d ↦ rComb (idxHi3Loc d)) (fun r ↦ rComb (out8Loc r)) (rComb qEncLoc) := by
  obtain ⟨h1, h2, h3, h4⟩ := wUncondDisj8_198
  exact ⟨fun d r ↦ rComb.wires.injective.ne (h1 d r), fun d ↦ rComb.wires.injective.ne (h2 d),
    fun i j hij ↦ rComb.wires.injective.ne (h3 i j hij), fun j ↦ rComb.wires.injective.ne (h4
    j)⟩
theorem wUncondDisj32_lift {n : ℕ} (rComb : QRegister 198 n) :
    WUncondDisjProp (fun d ↦ rComb (idxLo5Loc d)) (fun q ↦ rComb (out32Loc q)) (rComb qEncLoc) := by
  obtain ⟨h1, h2, h3, h4⟩ := wUncondDisj32_198
  exact ⟨fun d q ↦ rComb.wires.injective.ne (h1 d q), fun d ↦ rComb.wires.injective.ne (h2 d),
    fun i j hij ↦ rComb.wires.injective.ne (h3 i j hij), fun j ↦ rComb.wires.injective.ne (h4
    j)⟩
theorem out32Loc_ne_out8Loc (q : Fin 32) (r : Fin 8) : out32Loc q ≠ out8Loc r := by
  revert q r; decide
theorem out32Loc_ne_kc16Loc (q : Fin 32) (j : Fin 16) : out32Loc q ≠ kc16Loc j := by
  revert q j; decide
theorem out8Loc_ne_kc16Loc (r : Fin 8) (j : Fin 16) : out8Loc r ≠ kc16Loc j := by
  revert r j; decide
noncomputable def combStateOp {n : ℕ} (rAct33 : QRegister 33 n) (rSub : QRegister 165 n)
    (hDisj : rAct33.DisjointWires rSub)
    (G : BitAssignment 33 → BitAssignment 198) (S : BitAssignment 33 → ℂ) : Operator (2 ^ n) :=
  let rComb := rAct33.concat rSub hDisj
  mkVecOp fun α ↦
    if ∀ j : Fin 165, α (rSub j) = 0 then
      let x : BitAssignment 33 := fun i ↦ α (rAct33 i)
      S x • ket (writeRegProg α rComb (G x))
    else 0
def G0 (x : BitAssignment 33) : BitAssignment 198 :=
  padZeroBits (kAct := 33) (mClean := 165) x
theorem G0_lt (x : BitAssignment 33) (w : Wire 198) (hw : w.val < 33) :
    G0 x w = x ⟨w.val, hw⟩ :=
  padZeroBits_lt (k := 33) (m := 165) x w hw
theorem G0_ge (x : BitAssignment 33) (w : Wire 198) (hw : 33 ≤ w.val) : G0 x w = 0 :=
  padZeroBits_ge (k := 33) (m := 165) x w hw
def G1a (x : BitAssignment 33) : BitAssignment 198 :=
  Function.update (G0 x) (out8Loc (hi3Of33 x)) 1
def G1 (x : BitAssignment 33) : BitAssignment 198 :=
  Function.update (G1a x) (out32Loc (lo5Of33 x)) 1
def G2 (x : BitAssignment 33) : BitAssignment 198 := pad125To198 (γ2_125 x)
def G3 (x : BitAssignment 33) : BitAssignment 198 :=
  pad125To198 (pStage1Copy125.evalBits (γ2_125 x))
def Gkc (m : ℕ) (x : BitAssignment 33) : BitAssignment 198 := fun w ↦ if 33 ≤ w.val ∧ w.val <
    33 + m ∧ m ≤ 16 then b2z ((getNatAt kcTable49168List (c8Of33 x).val).testBit (w.val - 33))
    else G1 x w
def G49 (x : BitAssignment 33) : BitAssignment 198 := fun w ↦ if 33 ≤ w.val ∧ w.val < 49 then
    b2z ((getNatAt kcTable49168List (c8Of33 x).val).testBit (w.val - 33)) else G0 x w
theorem combStateOp_G0_one {n : ℕ} (rAct33 : QRegister 33 n) (rSub : QRegister 165 n)
    (hDisj : rAct33.DisjointWires rSub) :
    combStateOp rAct33 rSub hDisj G0 (fun _ ↦ 1) = rSub.basisOutcomeProjector 0 := by
  let rComb := rAct33.concat rSub hDisj
  apply matrix_ext_ket; intro α
  rw [combStateOp, mkVecOp_mulVec_ket, ket_basisOutcomeProjector_zero]
  by_cases h0 : ∀ j : Fin 165, α (rSub j) = 0
  · rw [ite_eq_left h0, ite_eq_left h0, one_smul]
    congr 1
    funext w
    by_cases hmem : w ∈ Set.range rComb.wires
    · obtain ⟨idx, rfl⟩ := hmem
      rw [writeRegProg_apply_reg]
      refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) idx
      · simp only [rComb, QRegister.concat_apply_left, G0, padZeroBits, Fin.addCases_left]
      · simp only [rComb, QRegister.concat_apply_right, G0, padZeroBits, Fin.addCases_right]
        exact (h0 j).symm
    · exact writeRegProg_apply_of_not_mem _ _ _ _ hmem
  · rw [ite_eq_right h0, ite_eq_right h0]
theorem combStateOp_G0_phase_gen {n : ℕ} (rAct33 : QRegister 33 n) (rSub : QRegister 165 n)
    (hDisj : rAct33.DisjointWires rSub) (pred33 : BitAssignment 33 → ZMod 2) :
    combStateOp rAct33 rSub hDisj G0 (fun x ↦ bitSign (pred33 x)) =
      (rAct33.embedUnitary (phaseDiagUnitary pred33)).1 * rSub.basisOutcomeProjector 0 := by
  rw [← combStateOp_G0_one rAct33 rSub hDisj]
  apply matrix_ext_ket; intro α
  rw [← Matrix.mulVec_mulVec, combStateOp, combStateOp, mkVecOp_mulVec_ket, mkVecOp_mulVec_ket]
  by_cases h0 : ∀ j : Fin 165, α (rSub j) = 0
  · rw [ite_eq_left h0, ite_eq_left h0, one_smul]
    have hw : writeRegProg α (rAct33.concat rSub hDisj) (G0 (fun i ↦ α (rAct33 i))) = α := by
      funext w
      by_cases hmem : w ∈ Set.range (rAct33.concat rSub hDisj).wires
      · obtain ⟨idx, rfl⟩ := hmem
        rw [writeRegProg_apply_reg]
        refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) idx
        · simp only [QRegister.concat_apply_left, G0, padZeroBits, Fin.addCases_left]
        · simp only [QRegister.concat_apply_right, G0, padZeroBits, Fin.addCases_right]
          exact (h0 j).symm
      · exact writeRegProg_apply_of_not_mem _ _ _ _ hmem
    dsimp only
    rw [hw, embedUnitary_phaseDiagUnitary_mulVec_ket]
  · rw [ite_eq_right h0, ite_eq_right h0, Matrix.mulVec_zero]
theorem combStateOp_G0_phase {n : ℕ} (rAct33 : QRegister 33 n) (rSub : QRegister 165 n)
    (hDisj : rAct33.DisjointWires rSub) :
    combStateOp rAct33 rSub hDisj G0 (fun x ↦ bitSign (predCoarseGood33 x)) =
      (rAct33.embedUnitary (phaseDiagUnitary predCoarseGood33)).1 * rSub.basisOutcomeProjector 0 :=
  combStateOp_G0_phase_gen rAct33 rSub hDisj predCoarseGood33
theorem supportedOn_combStateOp {n : ℕ} (rAct33 : QRegister 33 n) (rSub : QRegister 165 n)
    (hDisj : rAct33.DisjointWires rSub) (G : BitAssignment 33 → BitAssignment 198)
    (S : BitAssignment 33 → ℂ) {Pred : BitAssignment n → Prop} (hPred : ∀ α : BitAssignment n,
    Pred (writeRegProg α (rAct33.concat rSub hDisj) (G (fun i ↦ α (rAct33 i))))) : SupportedOn
    Pred (combStateOp rAct33 rSub hDisj G S) := by
  intro A B hAB
  apply matrix_ext_ket; intro α
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, combStateOp, mkVecOp_mulVec_ket]
  by_cases h0 : ∀ j : Fin 165, α (rSub j) = 0
  · rw [ite_eq_left h0, Matrix.mulVec_smul, Matrix.mulVec_smul]
    exact congrArg (S (fun i ↦ α (rAct33 i)) • ·) (hAB _ (hPred α))
  · rw [ite_eq_right h0, Matrix.mulVec_zero, Matrix.mulVec_zero]
theorem idxValD_hi3_on_G {n : ℕ} (rComb : QRegister 198 n) (α : BitAssignment n)
    (γ : BitAssignment 198) (x : BitAssignment 33)
    (hγ : ∀ d : Fin 3, γ (idxHi3Loc d) = x ⟨30 + d.val, by omega⟩) :
    idxValD (fun d : Fin 3 ↦ rComb (idxHi3Loc d)) (writeRegProg α rComb γ) = (hi3Of33 x).val := by
  have h1 : idxValD (fun d : Fin 3 ↦ rComb (idxHi3Loc d)) (writeRegProg α rComb γ) =
      idxValD (fun d : Fin 3 ↦ ⟨30 + d.val, by omega⟩) x := by
    dsimp only [idxValD, idxValPrefix]
    simp only [writeRegProg_apply_reg, hγ]
  rw [h1]
  exact idxValD_hi3_eq x
theorem idxValD_lo5_on_G {n : ℕ} (rComb : QRegister 198 n) (α : BitAssignment n)
    (γ : BitAssignment 198) (x : BitAssignment 33)
    (hγ : ∀ d : Fin 5, γ (idxLo5Loc d) = x ⟨25 + d.val, by omega⟩) :
    idxValD (fun d : Fin 5 ↦ rComb (idxLo5Loc d)) (writeRegProg α rComb γ) = (lo5Of33 x).val := by
  have h1 : idxValD (fun d : Fin 5 ↦ rComb (idxLo5Loc d)) (writeRegProg α rComb γ) =
      idxValD (fun d : Fin 5 ↦ ⟨25 + d.val, by omega⟩) x := by
    dsimp only [idxValD, idxValPrefix]
    simp only [writeRegProg_apply_reg, hγ]
  rw [h1]
  exact idxValD_lo5_eq x
theorem step1a_subspaceStep {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    (v : Var) (rAct33 : QRegister 33 n) (rSub : QRegister 165 n)
    (hDisj : rAct33.DisjointWires rSub) (S : BitAssignment 33 → ℂ) :
    let rComb := rAct33.concat rSub hDisj
    SubspaceStep (Var := Var)
      (combStateOp rAct33 rSub hDisj G0 S)
      (combStateOp rAct33 rSub hDisj G1a S)
      (wStateComputeUncondPow2 2 v (fun d ↦ rComb (idxHi3Loc d))
        (fun r ↦ rComb (out8Loc r)) (rComb qEncLoc)) := by
  intro rComb
  have hd8 := wUncondDisj8_lift rComb
  have hSupp : SupportedOn (ValidWUncondIn (fun r ↦ rComb (out8Loc r)) (rComb qEncLoc))
      (combStateOp rAct33 rSub hDisj G0 S) :=
    supportedOn_combStateOp rAct33 rSub hDisj G0 S fun α ↦ by
      refine ⟨fun r ↦ ?_, ?_⟩
      · rw [writeRegProg_apply_reg]
        exact G0_ge _ (out8Loc r) (by revert r; decide)
      · rw [writeRegProg_apply_reg]
        exact G0_ge _ qEncLoc (by decide)
  have s := subspaceStep_wStateComputeUncondPow2 2 v
    (fun d ↦ rComb (idxHi3Loc d)) (fun r ↦ rComb (out8Loc r)) (rComb qEncLoc)
    hd8 (combStateOp rAct33 rSub hDisj G0 S) hSupp
  refine subspaceStep_congr_out s ?_
  apply matrix_ext_ket; intro α
  rw [← Matrix.mulVec_mulVec, combStateOp, combStateOp, mkVecOp_mulVec_ket, mkVecOp_mulVec_ket]
  by_cases h0 : ∀ j : Fin 165, α (rSub j) = 0
  · rw [ite_eq_left h0, ite_eq_left h0, Matrix.mulVec_smul, uOneHotUncond_mulVec_ket]
    congr 2
    let x : BitAssignment 33 := fun i ↦ α (rAct33 i)
    have hidx : (⟨idxValD (fun d ↦ rComb (idxHi3Loc d)) (writeRegProg α rComb (G0 x)),
        idxValD_lt_two_pow _ _⟩ : Fin 8) = hi3Of33 x := by
      apply Fin.ext
      exact idxValD_hi3_on_G rComb α (G0 x) x fun d ↦
        G0_lt x (idxHi3Loc d) (by revert d; decide)
    rw [hidx, writeRegProg_apply_reg,
      G0_ge x (out8Loc (hi3Of33 x)) (by generalize hi3Of33 x = r; revert r; decide),
      zero_add, update_writeRegProg]
    rfl
  · rw [ite_eq_right h0, ite_eq_right h0, Matrix.mulVec_zero]
theorem step1b_subspaceStep {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    (v : Var) (rAct33 : QRegister 33 n) (rSub : QRegister 165 n)
    (hDisj : rAct33.DisjointWires rSub) (S : BitAssignment 33 → ℂ) :
    let rComb := rAct33.concat rSub hDisj
    SubspaceStep (Var := Var)
      (combStateOp rAct33 rSub hDisj G1a S)
      (combStateOp rAct33 rSub hDisj G1 S)
      (wStateComputeUncondPow2 4 v (fun d ↦ rComb (idxLo5Loc d))
        (fun q ↦ rComb (out32Loc q)) (rComb qEncLoc)) := by
  intro rComb
  have hd32 := wUncondDisj32_lift rComb
  have hSupp : SupportedOn (ValidWUncondIn (fun q ↦ rComb (out32Loc q)) (rComb qEncLoc))
      (combStateOp rAct33 rSub hDisj G1a S) :=
    supportedOn_combStateOp rAct33 rSub hDisj G1a S fun α ↦ by
      let x : BitAssignment 33 := fun i ↦ α (rAct33 i)
      refine ⟨fun q ↦ ?_, ?_⟩
      · rw [writeRegProg_apply_reg]
        dsimp [G1a]
        rw [Function.update_of_ne (out32Loc_ne_out8Loc q (hi3Of33 x))]
        exact G0_ge x (out32Loc q) (by revert q; decide)
      · rw [writeRegProg_apply_reg]
        dsimp [G1a]
        have hne : qEncLoc ≠ out8Loc (hi3Of33 x) := (wUncondDisj8_198.2.2.2 (hi3Of33 x)).symm
        rw [Function.update_of_ne hne]
        exact G0_ge x qEncLoc (by decide)
  have s := subspaceStep_wStateComputeUncondPow2 4 v
    (fun d ↦ rComb (idxLo5Loc d)) (fun q ↦ rComb (out32Loc q)) (rComb qEncLoc)
    hd32 (combStateOp rAct33 rSub hDisj G1a S) hSupp
  refine subspaceStep_congr_out s ?_
  apply matrix_ext_ket; intro α
  rw [← Matrix.mulVec_mulVec, combStateOp, combStateOp, mkVecOp_mulVec_ket, mkVecOp_mulVec_ket]
  by_cases h0 : ∀ j : Fin 165, α (rSub j) = 0
  · rw [ite_eq_left h0, ite_eq_left h0, Matrix.mulVec_smul, uOneHotUncond_mulVec_ket]
    congr 2
    let x : BitAssignment 33 := fun i ↦ α (rAct33 i)
    have hidx : (⟨idxValD (fun d ↦ rComb (idxLo5Loc d)) (writeRegProg α rComb (G1a x)),
        idxValD_lt_two_pow _ _⟩ : Fin 32) = lo5Of33 x := by
      apply Fin.ext
      exact idxValD_lo5_on_G rComb α (G1a x) x fun d ↦ by
        dsimp [G1a]
        rw [Function.update_of_ne (by generalize hi3Of33 x = r; revert d r; decide)]
        exact G0_lt x (idxLo5Loc d) (by revert d; decide)
    have h0_32 : G1a x (out32Loc (lo5Of33 x)) = 0 := by
      dsimp [G1a]
      rw [Function.update_of_ne (out32Loc_ne_out8Loc (lo5Of33 x) (hi3Of33 x))]
      exact G0_ge x (out32Loc (lo5Of33 x)) (by generalize lo5Of33 x = q; revert q; decide)
    rw [hidx, writeRegProg_apply_reg, h0_32, zero_add, update_writeRegProg]
    rfl
  · rw [ite_eq_right h0, ite_eq_right h0, Matrix.mulVec_zero]
theorem cliff_onRegister_eval_at {k M : ℕ} (sel : QRegister k M) :
    ∀ (c : CliffProg k) (γ : BitAssignment M) (i : Fin k),
      (c.onRegister sel).eval γ (sel i) = c.eval (fun j ↦ γ (sel j)) i
  | .nil, _, _ => rfl
  | .x q, γ, i => by
      dsimp only [CliffProg.onRegister, CliffProg.eval]
      by_cases hi : i = q
      · subst hi; simp
      · rw [Function.update_of_ne (sel.wires.injective.ne hi), Function.update_of_ne hi]
  | .cnot ctrl t h, γ, i => by
      dsimp only [CliffProg.onRegister, CliffProg.eval]
      by_cases hi : i = t
      · subst hi; simp
      · rw [Function.update_of_ne (sel.wires.injective.ne hi), Function.update_of_ne hi]
  | .seq c₁ c₂, γ, i => by
      dsimp only [CliffProg.onRegister, CliffProg.eval]
      rw [cliff_onRegister_eval_at sel c₂ _ i]
      congr 1; funext j
      exact cliff_onRegister_eval_at sel c₁ γ j
theorem cliff_onRegister_eval_outside {k M : ℕ} (sel : QRegister k M) :
    ∀ (c : CliffProg k) (γ : BitAssignment M) (w : Wire M),
      w ∉ Set.range sel.wires → (c.onRegister sel).eval γ w = γ w
  | .nil, _, _, _ => rfl
  | .x q, γ, w, hw => by
      dsimp only [CliffProg.onRegister, CliffProg.eval]
      exact Function.update_of_ne (fun h ↦ hw ⟨q, h.symm⟩) _ _
  | .cnot ctrl t h, γ, w, hw => by
      dsimp only [CliffProg.onRegister, CliffProg.eval]
      exact Function.update_of_ne (fun h ↦ hw ⟨t, h.symm⟩) _ _
  | .seq c₁ c₂, γ, w, hw => by
      dsimp only [CliffProg.onRegister, CliffProg.eval]
      rw [cliff_onRegister_eval_outside sel c₂ _ w hw,
          cliff_onRegister_eval_outside sel c₁ _ w hw]
theorem cliff_onRegister_eval_eq_writeRegProg {k M : ℕ}
    (γ : BitAssignment M) (sel : QRegister k M) (c : CliffProg k) :
    (c.onRegister sel).eval γ = writeRegProg γ sel (c.eval (fun i ↦ γ (sel i))) := by
  funext w
  by_cases hmem : w ∈ Set.range sel.wires
  · obtain ⟨i, rfl⟩ := hmem
    rw [writeRegProg_apply_reg, cliff_onRegister_eval_at]
  · rw [writeRegProg_apply_of_not_mem _ _ _ _ hmem, cliff_onRegister_eval_outside _ _ _ _ hmem]
theorem out8Loc_ge_49 (r : Fin 8) : 49 ≤ (out8Loc r).val := by revert r; decide
theorem out32Loc_ge_56 (q : Fin 32) : 56 ≤ (out32Loc q).val := by revert q; decide
theorem rOh8In198_ge_49 (r : Fin 8) : 49 ≤ (rOh8In198 r).val := out8Loc_ge_49 r
theorem rOh32In198_ge_56 (q : Fin 32) : 56 ≤ (rOh32In198 q).val := out32Loc_ge_56 q
theorem rOh8In198_lt_88 (r : Fin 8) : (rOh8In198 r).val < 88 := by revert r; decide
theorem rOh32In198_lt_89 (q : Fin 32) : (rOh32In198 q).val < 89 := by revert q; decide
theorem out8Loc_val_pos (r : Fin 8) (hr0 : r.val ≠ 0) : (rOh8In198 r).val = 48 + r.val := by
  revert r hr0; decide
theorem out32Loc_val_pos (q : Fin 32) (hq0 : q.val ≠ 0) : (rOh32In198 q).val = 55 + q.val := by
  revert q hq0; decide
theorem cMobius_onRegister_G1_eq_G2 (x : BitAssignment 33) :
    (cMobius32.onRegister rOh32In198).eval ((cMobius8.onRegister rOh8In198).eval (G1 x)) = G2 x :=
      by
  have h8 : (cMobius8.onRegister rOh8In198).eval (G1 x) =
      writeRegProg (G1 x) rOh8In198 (cMobius8.eval (oneHotBits (hi3Of33 x))) := by
    rw [cliff_onRegister_eval_eq_writeRegProg]
    congr 2
    funext r
    change G1 x (out8Loc r) = oneHotBits (hi3Of33 x) r
    dsimp [G1, G1a, oneHotBits]
    rw [Function.update_of_ne (out32Loc_ne_out8Loc (lo5Of33 x) r).symm]
    by_cases hr : r = hi3Of33 x
    · subst hr; rw [Function.update_self, ite_eq_left rfl]
    · rw [Function.update_of_ne (out8Loc_inj.ne hr), ite_eq_right hr]
      exact G0_ge x (out8Loc r) (by have := out8Loc_ge_49 r; omega)
  rw [h8, cMobius8_eval_oneHot_eq]
  let γMid := writeRegProg (G1 x) rOh8In198 (mobiusTargetBits (hi3Of33 x))
  have h32 : (cMobius32.onRegister rOh32In198).eval γMid =
      writeRegProg γMid rOh32In198 (cMobius32.eval (oneHotBits (lo5Of33 x))) := by
    rw [cliff_onRegister_eval_eq_writeRegProg]
    congr 2
    funext q
    have hnot8 : rOh32In198 q ∉ Set.range rOh8In198.wires := by
      rintro ⟨r, hr⟩
      exact out32Loc_ne_out8Loc q r hr.symm
    dsimp [γMid]
    rw [writeRegProg_apply_of_not_mem _ _ _ _ hnot8]
    change G1 x (out32Loc q) = oneHotBits (lo5Of33 x) q
    dsimp [G1, G1a, oneHotBits]
    by_cases hq : q = lo5Of33 x
    · subst hq; rw [Function.update_self, ite_eq_left rfl]
    · rw [Function.update_of_ne (out32Loc_inj.ne hq), ite_eq_right hq,
        Function.update_of_ne (out32Loc_ne_out8Loc q (hi3Of33 x))]
      exact G0_ge x (out32Loc q) (by have := out32Loc_ge_56 q; omega)
  rw [h32, cMobius32_eval_oneHot_eq]
  funext w
  have h8ge : 49 ≤ (out8Loc (hi3Of33 x)).val := out8Loc_ge_49 (hi3Of33 x)
  have h32ge : 56 ≤ (out32Loc (lo5Of33 x)).val := out32Loc_ge_56 (lo5Of33 x)
  by_cases hw33 : w.val < 33
  · have hnot32 : w ∉ Set.range rOh32In198.wires := by
      rintro ⟨q, rfl⟩; have := rOh32In198_ge_56 q; omega
    have hnot8 : w ∉ Set.range rOh8In198.wires := by
      rintro ⟨r, rfl⟩; have := rOh8In198_ge_49 r; omega
    rw [writeRegProg_apply_of_not_mem _ _ _ _ hnot32]
    dsimp [γMid]
    rw [writeRegProg_apply_of_not_mem _ _ _ _ hnot8]
    dsimp [G1, G1a, G2, pad125To198, γ2_125]
    rw [Function.update_of_ne (fun h ↦ by have := congrArg Fin.val h; omega),
      Function.update_of_ne (fun h ↦ by have := congrArg Fin.val h; omega),
      G0_lt x w hw33, dite_eq_left (by omega), dite_eq_left hw33]
  · have hnot33 : ¬ w.val < 33 := hw33
    have hG2 : G2 x w =
        (if w.val < 49 then 0
         else if hw8 : w.val < 56 then mobiusTargetBits (hi3Of33 x) ⟨w.val - 48, by omega⟩
         else if hw32 : w.val < 87 then mobiusTargetBits (lo5Of33 x) ⟨w.val - 55, by omega⟩
         else 0) := by
      dsimp [G2, pad125To198, γ2_125]
      by_cases hw125 : w.val < 125
      · rw [dite_eq_left hw125, dite_eq_right hnot33]
      · rw [dite_eq_right hw125]
        have hnot49 : ¬ w.val < 49 := by omega
        have hnot56 : ¬ w.val < 56 := by omega
        have hnot87 : ¬ w.val < 87 := by omega
        rw [ite_eq_right hnot49, dite_eq_right hnot56, dite_eq_right hnot87]
    rw [hG2]
    by_cases hw49 : w.val < 49
    · have hnot32 : w ∉ Set.range rOh32In198.wires := by
        rintro ⟨q, rfl⟩; have := rOh32In198_ge_56 q; omega
      have hnot8 : w ∉ Set.range rOh8In198.wires := by
        rintro ⟨r, rfl⟩; have := rOh8In198_ge_49 r; omega
      rw [writeRegProg_apply_of_not_mem _ _ _ _ hnot32]
      dsimp [γMid]
      rw [writeRegProg_apply_of_not_mem _ _ _ _ hnot8, ite_eq_left hw49]
      dsimp [G1, G1a]
      rw [Function.update_of_ne (fun h ↦ by have := congrArg Fin.val h; omega),
        Function.update_of_ne (fun h ↦ by have := congrArg Fin.val h; omega),
        G0_ge x w (by omega)]
    · by_cases hw56 : w.val < 56
      · have hnot32 : w ∉ Set.range rOh32In198.wires := by
          rintro ⟨q, rfl⟩; have := rOh32In198_ge_56 q; omega
        rw [writeRegProg_apply_of_not_mem _ _ _ _ hnot32, ite_eq_right hw49, dite_eq_left hw56]
        let r : Fin 8 := ⟨w.val - 48, by omega⟩
        have hw_eq : w = rOh8In198 r := by
          apply Fin.ext
          rw [out8Loc_val_pos r (by dsimp [r]; omega)]
          dsimp [r]; omega
        have hlhs : γMid w = mobiusTargetBits (hi3Of33 x) r := by
          rw [hw_eq]; dsimp [γMid]; exact writeRegProg_apply_reg _ _ _ _
        exact hlhs
      · by_cases hw87 : w.val < 87
        · rw [ite_eq_right hw49, dite_eq_right hw56, dite_eq_left hw87]
          let q : Fin 32 := ⟨w.val - 55, by omega⟩
          have hw_eq : w = rOh32In198 q := by
            apply Fin.ext
            rw [out32Loc_val_pos q (by dsimp [q]; omega)]
            dsimp [q]; omega
          have hlhs : writeRegProg γMid rOh32In198 (mobiusTargetBits (lo5Of33 x)) w =
              mobiusTargetBits (lo5Of33 x) q := by
            rw [hw_eq]; exact writeRegProg_apply_reg _ _ _ _
          exact hlhs
        · rw [ite_eq_right hw49, dite_eq_right hw56, dite_eq_right hw87]
          by_cases hw87_eq : w = ⟨87, by decide⟩
          · subst hw87_eq
            have hnot32 : (⟨87, by decide⟩ : Wire 198) ∉ Set.range rOh32In198.wires := by
              rintro ⟨q, hq⟩; revert q hq; decide
            rw [writeRegProg_apply_of_not_mem _ _ _ _ hnot32]
            have hw0 : (⟨87, by decide⟩ : Wire 198) = rOh8In198 0 := rfl
            rw [hw0]; dsimp [γMid]; rw [writeRegProg_apply_reg]; rfl
          · by_cases hw88_eq : w = ⟨88, by decide⟩
            · subst hw88_eq
              have hw0 : (⟨88, by decide⟩ : Wire 198) = rOh32In198 0 := rfl
              rw [hw0, writeRegProg_apply_reg]; rfl
            · have h89 : 89 ≤ w.val := by
                have : w.val ≠ 87 := fun h ↦ hw87_eq (Fin.ext h)
                have : w.val ≠ 88 := fun h ↦ hw88_eq (Fin.ext h)
                omega
              have hnot32 : w ∉ Set.range rOh32In198.wires := by
                rintro ⟨q, rfl⟩; have := rOh32In198_lt_89 q; omega
              have hnot8 : w ∉ Set.range rOh8In198.wires := by
                rintro ⟨r, rfl⟩; have := rOh8In198_lt_88 r; omega
              rw [writeRegProg_apply_of_not_mem _ _ _ _ hnot32]
              dsimp [γMid]
              rw [writeRegProg_apply_of_not_mem _ _ _ _ hnot8]
              dsimp [G1, G1a]
              have hne32 : w ≠ out32Loc (lo5Of33 x) := fun h ↦ hnot32 ⟨lo5Of33 x, h.symm⟩
              have hne8 : w ≠ out8Loc (hi3Of33 x) := fun h ↦ hnot8 ⟨hi3Of33 x, h.symm⟩
              rw[Function.update_of_ne hne32, Function.update_of_ne hne8,
                  G0_ge x w (by omega)]
theorem step2_subspaceStep {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    (rAct33 : QRegister 33 n) (rSub : QRegister 165 n)
    (hDisj : rAct33.DisjointWires rSub) (S : BitAssignment 33 → ℂ) :
    let rComb := rAct33.concat rSub hDisj
    SubspaceStep (Var := Var)
      (combStateOp rAct33 rSub hDisj G1 S)
      (combStateOp rAct33 rSub hDisj G2 S)
      (.circuit (((cMobius8.onRegister (rComb.compose rOh8In198)).toCircuit) ;;ᶜ
        ((cMobius32.onRegister (rComb.compose rOh32In198)).toCircuit))) := by
  intro rComb
  refine subspaceStep_congr_out (subspaceStep_of_circuit _ _) ?_
  apply matrix_ext_ket; intro α
  rw [← Matrix.mulVec_mulVec, combStateOp, combStateOp, mkVecOp_mulVec_ket, mkVecOp_mulVec_ket]
  by_cases h0 : ∀ j : Fin 165, α (rSub j) = 0
  · rw [ite_eq_left h0, ite_eq_left h0, Matrix.mulVec_smul, eval_seq_mulVec,
      CliffProg.toCircuit_eval_ket, CliffProg.toCircuit_eval_ket,
      cliff_onRegister_compose_eval, cliff_onRegister_compose_eval,
      cMobius_onRegister_G1_eq_G2]
  · rw [ite_eq_right h0, ite_eq_right h0, Matrix.mulVec_zero]
theorem step3_subspaceStep {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    (v : Var) (rAct33 : QRegister 33 n) (rSub : QRegister 165 n)
    (hDisj : rAct33.DisjointWires rSub) (S : BitAssignment 33 → ℂ) :
    let rComb := rAct33.concat rSub hDisj
    SubspaceStep (Var := Var)
      (combStateOp rAct33 rSub hDisj G2 S)
      (combStateOp rAct33 rSub hDisj G3 S)
      ((pStage1Copy125.onRegister (rComb.compose r125In198)).toDyn v) := by
  intro rComb
  let r125 := rComb.compose r125In198
  have hPR : projZeroAll 38 (tailScr r125 38 (by decide)) *
      combStateOp rAct33 rSub hDisj G2 S = combStateOp rAct33 rSub hDisj G2 S := by
    apply matrix_ext_ket; intro α
    rw [← Matrix.mulVec_mulVec, combStateOp, mkVecOp_mulVec_ket]
    by_cases h0 : ∀ j : Fin 165, α (rSub j) = 0
    · rw [ite_eq_left h0, Matrix.mulVec_smul, ket_projZeroAll]
      have hz : ∀ j : Fin 38,
          writeRegProg α rComb (G2 (fun i ↦ α (rAct33 i))) (tailScr r125 38 (by decide) j) = 0 := by
        intro j
        have htail : tailScr r125 38 (by decide) j = rComb ⟨87 + j.val, by omega⟩ :=
          congrArg rComb (by revert j; decide)
        rw [htail, writeRegProg_apply_reg]
        dsimp [G2, pad125To198, γ2_125]
        rw [dite_eq_left (by omega), dite_eq_right (by omega), ite_eq_right (by omega),
            dite_eq_right (by omega), dite_eq_right (by omega)]
      rw [ite_eq_left hz]
    · rw [ite_eq_right h0, Matrix.mulVec_zero]
  have s := subspaceStep_of_validCleanRem v r125 pStage1Copy125 38 (by decide)
    pStage1Copy125_validCleanRem (combStateOp rAct33 rSub hDisj G2 S) hPR
  refine subspaceStep_congr_out s ?_
  apply matrix_ext_ket; intro α
  rw [← Matrix.mulVec_mulVec, combStateOp, combStateOp, mkVecOp_mulVec_ket, mkVecOp_mulVec_ket]
  by_cases h0 : ∀ j : Fin 165, α (rSub j) = 0
  · rw [ite_eq_left h0, ite_eq_left h0, Matrix.mulVec_smul, eval_onRegister_prog_ket]
    let x : BitAssignment 33 := fun i ↦ α (rAct33 i)
    have hγ125 : (fun idx : Fin 125 ↦ writeRegProg α rComb (G2 x) (r125 idx)) = γ2_125 x := by
      funext idx
      change writeRegProg α rComb (G2 x) (rComb (r125In198 idx)) = γ2_125 x idx
      rw [writeRegProg_apply_reg]
      simp only [r125In198_apply]
      dsimp [G2, pad125To198]
      rw [ite_eq_left idx.isLt]
    rw [hγ125, pStage1Copy125_evalSign, ZMod.val_zero, _root_.pow_zero, one_smul,
      writeRegProg_compose]
    refine congrArg (S x • ·) (congrArg ket (congrArg (writeRegProg α rComb) ?_))
    funext w
    by_cases hw125 : w.val < 125
    · have hw_eq : w = r125In198 ⟨w.val, hw125⟩ := (r125In198_apply ⟨w.val, hw125⟩).symm
      rw [hw_eq, writeRegProg_apply_reg]
      simp only [r125In198_apply]
      dsimp [G3, pad125To198]
      rw [dite_eq_left hw125]
    · have hnot : w ∉ Set.range r125In198.wires := by
        rintro ⟨idx, rfl⟩
        rw [r125In198_apply] at hw125
        exact hw125 idx.isLt
      rw [writeRegProg_apply_of_not_mem _ _ _ _ hnot]
      dsimp [G2, G3, pad125To198]
      rw [dite_eq_right hw125, dite_eq_right hw125]
  · rw [ite_eq_right h0, ite_eq_right h0, Matrix.mulVec_zero]
theorem wire198_ge_89_of_not_mem : ∀ w : Wire 198, ¬ (33 ≤ w.val ∧ w.val < 49) → ¬ w.val < 33
    → (∀ r : Fin 8, w ≠ out8Loc r) → (∀ q : Fin 32, w ≠ out32Loc q) → 89 ≤ w.val := by
  decide +kernel
theorem γ2_125_out32Loc (x : BitAssignment 33) (q : Fin 32) (hq125 : (out32Loc q).val < 125) :
    γ2_125 x ⟨(out32Loc q).val, hq125⟩ = mobiusTargetBits (lo5Of33 x) q := by
  have hnot56 : ¬ (out32Loc q).val < 56 := by revert q; decide
  dsimp [γ2_125]
  rw [dite_eq_right (by omega), ite_eq_right (by omega), dite_eq_right hnot56]
  generalize lo5Of33 x = q₀
  revert q q₀ hq125 hnot56; decide +kernel
theorem γ2_125_out8Loc (x : BitAssignment 33) (r : Fin 8) (hr125 : (out8Loc r).val < 125) :
    γ2_125 x ⟨(out8Loc r).val, hr125⟩ = mobiusTargetBits (hi3Of33 x) r := by
  have hnot49 : ¬ (out8Loc r).val < 49 := by revert r; decide
  have hnot32 : ¬ (56 ≤ (out8Loc r).val ∧ (out8Loc r).val < 87) := by revert r; decide
  dsimp [γ2_125]
  rw [dite_eq_right (by omega), ite_eq_right hnot49]
  by_cases hr56 : (out8Loc r).val < 56
  · rw [dite_eq_left hr56]
    generalize hi3Of33 x = r₀
    revert r r₀ hr125 hnot49 hnot32 hr56; decide +kernel
  · rw [dite_eq_right hr56, dite_eq_right (by omega)]
    generalize hi3Of33 x = r₀
    revert r r₀ hr125 hnot49 hnot32 hr56; decide +kernel
theorem step5_subspaceStep {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    (rAct33 : QRegister 33 n) (rSub : QRegister 165 n)
    (hDisj : rAct33.DisjointWires rSub) (S : BitAssignment 33 → ℂ) :
    let rComb := rAct33.concat rSub hDisj
    SubspaceStep (Var := Var)
      (combStateOp rAct33 rSub hDisj G3 S)
      (combStateOp rAct33 rSub hDisj (Gkc 16) S)
      (.circuit ((((cMobius32.inv).onRegister (rComb.compose rOh32In198)).toCircuit) ;;ᶜ
        (((cMobius8.inv).onRegister (rComb.compose rOh8In198)).toCircuit))) := by
  intro rComb
  refine subspaceStep_congr_out (subspaceStep_of_circuit _ _) ?_
  apply matrix_ext_ket; intro α
  rw [← Matrix.mulVec_mulVec, combStateOp, combStateOp, mkVecOp_mulVec_ket, mkVecOp_mulVec_ket]
  by_cases h0 : ∀ j : Fin 165, α (rSub j) = 0
  · rw [ite_eq_left h0, ite_eq_left h0, Matrix.mulVec_smul, eval_seq_mulVec,
      CliffProg.toCircuit_eval_ket, CliffProg.toCircuit_eval_ket,
      cliff_onRegister_compose_eval, cliff_onRegister_compose_eval]
    let x : BitAssignment 33 := fun i ↦ α (rAct33 i)
    refine congrArg (S x • ·) (congrArg ket (congrArg (writeRegProg α rComb) ?_))
    rw [cliff_onRegister_eval_eq_writeRegProg (G3 x) rOh32In198 cMobius32.inv]
    have h32_in : (fun q : Fin 32 ↦ G3 x (rOh32In198 q)) = cMobius32.eval (oneHotBits (lo5Of33
      x)) := by
      rw [cMobius32_eval_oneHot_eq]
      funext q
      change G3 x (out32Loc q) = mobiusTargetBits (lo5Of33 x) q
      have hq125 : (out32Loc q).val < 125 := by revert q; decide
      have hq_not_kc : ¬ (33 ≤ (out32Loc q).val ∧ (out32Loc q).val < 49) := by revert q; decide
      dsimp [G3, pad125To198]
      rw [dite_eq_left hq125, pStage1Copy125_evalBits_γ2 x ⟨(out32Loc q).val, hq125⟩,
        ite_eq_right hq_not_kc]
      exact γ2_125_out32Loc x q hq125
    rw [h32_in, CliffProg.inv_eval]
    let γMid := writeRegProg (G3 x) rOh32In198 (oneHotBits (lo5Of33 x))
    rw [cliff_onRegister_eval_eq_writeRegProg γMid rOh8In198 cMobius8.inv]
    have h8_in : (fun r : Fin 8 ↦ γMid (rOh8In198 r)) = cMobius8.eval (oneHotBits (hi3Of33 x)) := by
      rw [cMobius8_eval_oneHot_eq]
      funext r
      have hnot32 : rOh8In198 r ∉ Set.range rOh32In198.wires := by
        rintro ⟨q, hq⟩
        exact out32Loc_ne_out8Loc q r hq
      dsimp [γMid]
      rw [writeRegProg_apply_of_not_mem _ _ _ _ hnot32]
      change G3 x (out8Loc r) = mobiusTargetBits (hi3Of33 x) r
      have hr125 : (out8Loc r).val < 125 := by revert r; decide
      have hr_not_kc : ¬ (33 ≤ (out8Loc r).val ∧ (out8Loc r).val < 49) := by revert r; decide
      dsimp [G3, pad125To198]
      rw [dite_eq_left hr125, pStage1Copy125_evalBits_γ2 x ⟨(out8Loc r).val, hr125⟩,
        ite_eq_right hr_not_kc]
      exact γ2_125_out8Loc x r hr125
    rw [h8_in, CliffProg.inv_eval]
    funext w
    by_cases hkc : 33 ≤ w.val ∧ w.val < 49
    · have hnot8 : w ∉ Set.range rOh8In198.wires := by
        rintro ⟨r, rfl⟩; revert r hkc; decide
      have hnot32 : w ∉ Set.range rOh32In198.wires := by
        rintro ⟨q, rfl⟩; revert q hkc; decide
      rw [writeRegProg_apply_of_not_mem _ _ _ _ hnot8]
      dsimp [γMid]
      rw [writeRegProg_apply_of_not_mem _ _ _ _ hnot32]
      dsimp [Gkc, G3, pad125To198]
      have hw125 : w.val < 125 := by omega
      have hkc16 : 33 ≤ w.val ∧ w.val < 33 + 16 ∧ 16 ≤ 16 := ⟨hkc.1, hkc.2, le_rfl⟩
      rw [dite_eq_left hw125, pStage1Copy125_evalBits_γ2 x ⟨w.val, hw125⟩,
          ite_eq_left hkc, ite_eq_left hkc16]
    · have hnot_kc16 : ¬ (33 ≤ w.val ∧ w.val < 33 + 16 ∧ 16 ≤ 16) := fun h ↦ hkc ⟨h.1, h.2.1⟩
      dsimp [Gkc]
      rw [ite_eq_right hnot_kc16]
      by_cases hmem8 : w ∈ Set.range rOh8In198.wires
      · obtain ⟨r, rfl⟩ := hmem8
        rw [writeRegProg_apply_reg]
        change oneHotBits (hi3Of33 x) r = G1 x (out8Loc r)
        dsimp [G1, G1a, oneHotBits]
        rw [Function.update_of_ne (out32Loc_ne_out8Loc (lo5Of33 x) r).symm]
        by_cases hr : r = hi3Of33 x
        · subst hr; rw [ite_eq_left rfl, Function.update_self]
        · rw [ite_eq_right hr, Function.update_of_ne (out8Loc_inj.ne hr),
            G0_ge x (out8Loc r) (by have := out8Loc_ge_49 r; omega)]
      · rw [writeRegProg_apply_of_not_mem _ _ _ _ hmem8]
        dsimp [γMid]
        by_cases hmem32 : w ∈ Set.range rOh32In198.wires
        · obtain ⟨q, rfl⟩ := hmem32
          rw [writeRegProg_apply_reg]
          change oneHotBits (lo5Of33 x) q = G1 x (out32Loc q)
          dsimp [G1, G1a, oneHotBits]
          by_cases hq : q = lo5Of33 x
          · subst hq; rw [ite_eq_left rfl, Function.update_self]
          · rw [ite_eq_right hq, Function.update_of_ne (out32Loc_inj.ne hq),
              Function.update_of_ne (out32Loc_ne_out8Loc q (hi3Of33 x)),
              G0_ge x (out32Loc q) (by have := out32Loc_ge_56 q; omega)]
        · rw [writeRegProg_apply_of_not_mem _ _ _ _ hmem32]
          have hne32 : w ≠ out32Loc (lo5Of33 x) := fun h ↦ hmem32 ⟨lo5Of33 x, h.symm⟩
          have hne8 : w ≠ out8Loc (hi3Of33 x) := fun h ↦ hmem8 ⟨hi3Of33 x, h.symm⟩
          by_cases hw33 : w.val < 33
          · dsimp [G3, pad125To198, G1, G1a]
            have hw125 : w.val < 125 := by omega
            rw [dite_eq_left hw125, pStage1Copy125_evalBits_γ2 x ⟨w.val, hw125⟩, ite_eq_right hkc]
            dsimp [γ2_125]
            rw[dite_eq_left hw33, Function.update_of_ne hne32, Function.update_of_ne hne8,
                G0_lt x w hw33]
          · have hw89 : 89 ≤ w.val := wire198_ge_89_of_not_mem w hkc hw33
              (fun r h ↦ hmem8 ⟨r, h.symm⟩) (fun q h ↦ hmem32 ⟨q, h.symm⟩)
            dsimp [G3, pad125To198, G1, G1a]
            rw[Function.update_of_ne hne32, Function.update_of_ne hne8, G0_ge x w (by omega)]
            by_cases hw125 : w.val < 125
            · rw [dite_eq_left hw125, pStage1Copy125_evalBits_γ2 x ⟨w.val, hw125⟩, ite_eq_right hkc]
              dsimp [γ2_125]
              rw [dite_eq_right hw33, ite_eq_right (by omega),
                  dite_eq_right (by omega), dite_eq_right (by omega)]
            · rw [dite_eq_right hw125]
  · rw [ite_eq_right h0, ite_eq_right h0, Matrix.mulVec_zero]
theorem G49_lt33 (x : BitAssignment 33) (w : Wire 198) (hw : w.val < 33) :
    G49 x w = x ⟨w.val, hw⟩ := by
  dsimp [G49]
  rw [ite_eq_right (by omega), G0_lt x w hw]
theorem writeRegProg_G49_r49_eq {n : ℕ} (α : BitAssignment n) (rComb : QRegister 198 n)
    (x : BitAssignment 33) : (fun i : Fin 49 ↦ writeRegProg α rComb (G49 x) (rComb.compose
    r49In198 i)) = xorRightMapGen tblBits16 (padZeroBits x) := by
  funext i
  change writeRegProg α rComb (G49 x) (rComb (r49In198 i)) =
    xorRightMapGen tblBits16 (padZeroBits x) i
  rw [writeRegProg_apply_reg, r49In198_apply]
  dsimp [G49, xorRightMapGen, tblBits16, c8Of33]
  by_cases hi33 : i.val < 33
  · rw [ite_eq_right (by omega), ite_eq_left hi33, G0_lt x ⟨i.val, by omega⟩ hi33,
      padZeroBits_lt (k := 33) (m := 16) x i hi33]
  · have hkc : 33 ≤ i.val ∧ i.val < 49 := ⟨Nat.le_of_not_lt hi33, i.isLt⟩
    rw [ite_eq_left hkc, ite_eq_right hi33, padZeroBits_ge (k := 33) (m := 16) x i hkc.1, zero_add]
    have hc_eq : (fun d : Fin 8 ↦ padZeroBits (kAct := 33) (mClean := 16) x ⟨25 + d.val,
      by omega⟩) =
        (fun d : Fin 8 ↦ x ⟨25 + d.val, by omega⟩) := by
      funext d
      exact padZeroBits_lt (k := 33) (m := 16) x ⟨25 + d.val, by omega⟩ (by dsimp; omega)
    rw [hc_eq]
end
end ConfigK2
end D0aa33Width165Slot3Prep2356
end
end D0aa33Width165Slot3Prep2356

noncomputable section GqspSlot3OctantOneNegBaseAndLo

section
namespace GqspSlot3OctantOneNegBaseAndLo
set_option maxRecDepth 8192
open ModWrapCoarse8PureMomentum (max2Nat octWeight octShell natSum natSum_congr natSum_add_split)
open Slot3Norm1s36LatticeBase (n1sCbv n1sCbv2 n1sCbv_eq n1sCbv2_eq n1sMax2Fast_eq_max
  n1sMax2Fast_eq_max2Nat n1sShiftIdx n1sShiftIdx_eq n1sNatSumFast n1sNatSumFast_eq n1s_nat_add_eq
  n1s_nat_sub_eq n1s_nat_mul_eq)
private theorem max2Nat_eq_max (a b : ℕ) : max2Nat a b = max a b := by
  rw [← n1sMax2Fast_eq_max2Nat, n1sMax2Fast_eq_max]
/-- `2^20`-scaled ceiling division `⌈num * 2^20 / den⌉` for integer octant lattice certificates. -/
def ceilDiv20Den (num den : ℕ) : ℕ :=
  Nat.div (Nat.sub (Nat.add (Nat.mul 1048576 num) den) 1) den
theorem ceilDiv_antitone {A d1 d2 : ℕ} (hd1 : 0 < d1) (hle : d1 ≤ d2) :
    (A + d2 - 1) / d2 ≤ (A + d1 - 1) / d1 := by
  have hd2 : 0 < d2 := lt_of_lt_of_le hd1 hle
  set q := (A + d1 - 1) / d1
  have h1 := Nat.div_add_mod (A + d1 - 1) d1
  have h2 := Nat.mod_lt (A + d1 - 1) hd1
  have hAq : A ≤ d1 * q := by change d1 * q + _ = _ at h1; omega
  have hd2q : A ≤ d2 * q := le_trans hAq (Nat.mul_le_mul_right q hle)
  have h3 := Nat.div_add_mod (A + d2 - 1) d2
  by_contra hlt
  have hge : q + 1 ≤ (A + d2 - 1) / d2 := by omega
  have hmul : d2 * q + d2 ≤ d2 * ((A + d2 - 1) / d2) := by
    simpa [Nat.mul_add, Nat.mul_one] using Nat.mul_le_mul_left d2 hge
  omega
/-- Symmetric 5-branch `2^20`-scaled upper bound on `|d0 + d1 + d2| / (d0^2 + d1^2 + d2^2)`
over all 8 `modFold3D 127` preimages of `(-x, +y, +z)` (`x, y, z ≤ 127`). -/
def fOneNegSingle (x y z : ℕ) : ℕ :=
  let x0 := x * x
  let x1 := (255 - x) * (255 - x)
  let y0 := y * y
  let y1 := (255 - y) * (255 - y)
  let z0 := z * z
  let z1 := (255 - z) * (255 - z)
  let s0 := x0 + (y0 + z0)
  bif Nat.beq s0 0 then 0
  else
    max
      (max
        (ceilDiv20Den (((y + z) - x) + (x - (y + z))) s0)
        (bif Nat.beq x 0 then 0 else ceilDiv20Den ((255 - x) + (y + z)) (x1 + (y0 + z0))))
      (max
        (max
          (bif Nat.beq y 0 then 0 else ceilDiv20Den ((255 + x) - (y + z)) (x0 + (y1 + z0)))
          (bif Nat.beq z 0 then 0 else ceilDiv20Den ((255 + x) - (y + z)) (x0 + (y0 + z1))))
        (bif (Nat.beq y 0 || Nat.beq z 0) then 0
         else ceilDiv20Den (x + ((255 - y) + (255 - z))) (x0 + (y1 + z1))))
theorem fOneNegSingle_swap23 (x y z : ℕ) : fOneNegSingle x y z = fOneNegSingle x z y := by
  have hyz_sq : y * y + z * z = z * z + y * y := Nat.add_comm (y * y) (z * z)
  have hyz : y + z = z + y := Nat.add_comm y z
  have hd1 : (255 - y) * (255 - y) + z * z = z * z + (255 - y) * (255 - y) := Nat.add_comm _ _
  have hd2 : y * y + (255 - z) * (255 - z) = (255 - z) * (255 - z) + y * y := Nat.add_comm _ _
  have hn4 : (255 - y) + (255 - z) = (255 - z) + (255 - y) := Nat.add_comm _ _
  have hd4 : (255 - y) * (255 - y) + (255 - z) * (255 - z) =
      (255 - z) * (255 - z) + (255 - y) * (255 - y) := Nat.add_comm _ _
  have hb4 : (Nat.beq y 0 || Nat.beq z 0) = (Nat.beq z 0 || Nat.beq y 0) := Bool.or_comm _ _
  dsimp only [fOneNegSingle]
  rw [hyz_sq, hyz, hd1, hd2, hn4, hd4, hb4,
    max_comm
      (bif Nat.beq y 0 then 0 else ceilDiv20Den (255 + x - (z + y)) (x * x + (z * z + (255 - y) *
        (255 - y))))
      (bif Nat.beq z 0 then 0 else ceilDiv20Den (255 + x - (z + y)) (x * x + ((255 - z) * (255 -
        z) + y * y)))]
/-- Fully permutation-symmetric sum of the three single-negative-sign octant bounds at `(a, b,
c)`. -/
def fOneNeg3Sym (a b c : ℕ) : ℕ :=
  fOneNegSingle a b c + (fOneNegSingle b a c + fOneNegSingle c a b)
theorem fOneNeg3Sym_zero : fOneNeg3Sym 0 0 0 = 0 := by decide
theorem fOneNeg3Sym_swap12 (a b c : ℕ) : fOneNeg3Sym a b c = fOneNeg3Sym b a c := by
  unfold fOneNeg3Sym; rw [fOneNegSingle_swap23 c a b]; ring
theorem fOneNeg3Sym_swap23 (a b c : ℕ) : fOneNeg3Sym a b c = fOneNeg3Sym a c b := by
  unfold fOneNeg3Sym; rw [fOneNegSingle_swap23 a b c]; ring
/-- Ordered (`z ≤ y ≤ 127`) 4-branch literal evaluator using `max2Nat` + `ceilDiv20Den` directly. -/
def fOneNegOrdLit (x y z x0 x1 y0 y1 z0 z1 : ℕ) : ℕ := bif Nat.beq
    (Nat.add x0 (Nat.add y0 z0)) 0 then 0 else max2Nat (max2Nat (ceilDiv20Den (Nat.add
    (Nat.sub (Nat.add y z) x) (Nat.sub x (Nat.add y z))) (Nat.add x0 (Nat.add y0 z0))) (bif
    Nat.beq x 0 then 0 else ceilDiv20Den (Nat.add (Nat.sub 255 x) (Nat.add y z)) (Nat.add x1
    (Nat.add y0 z0)))) (max2Nat (bif Nat.beq y 0 then 0 else ceilDiv20Den (Nat.sub (Nat.add
    255 x) (Nat.add y z)) (Nat.add x0 (Nat.add y1 z0))) (bif Nat.beq z 0 then 0 else
    ceilDiv20Den (Nat.add x (Nat.add (Nat.sub 255 y) (Nat.sub 255 z))) (Nat.add x0 (Nat.add y1
    z1))))
/-- Ordered (`c ≤ b ≤ k ≤ 127`) literal evaluator for `fOneNeg3Sym k b c`. -/
def fOneNeg3OrdLit (k b c k0 k1 b0 b1 c0 c1 : ℕ) : ℕ := Nat.add
    (fOneNegOrdLit k b c k0 k1 b0 b1 c0 c1) (Nat.add (fOneNegOrdLit b k c b0 b1 k0 k1 c0 c1)
    (fOneNegOrdLit c k b c0 c1 k0 k1 b0 b1))
def oneNegCStepLit (k b k0 k1 b0 b1 c c0 c1 : ℕ) : ℕ := fOneNeg3OrdLit k b c k0 k1 b0 b1 c0 c1
def oneNegCStepC (k b k0 k1 b0 b1 c : ℕ) : ℕ := n1sCbv2 (oneNegCStepLit k b k0 k1 b0 b1 c)
    (Nat.mul c c) (Nat.mul (Nat.sub 255 c) (Nat.sub 255 c))
def oneNegCStep (k b k0 k1 b0 b1 j : ℕ) : ℕ :=
  n1sCbv (oneNegCStepC k b k0 k1 b0 b1) (Nat.add j 1)
def oneNegBPosBM1 (k b k0 k1 b0 b1 bm1 : ℕ) : ℕ := Nat.add
    (Nat.mul 8 (fOneNeg3OrdLit k b 0 k0 k1 b0 b1 0 65025)) (Nat.add (Nat.mul 8 (fOneNeg3OrdLit
    k b b k0 k1 b0 b1 b0 b1)) (Nat.mul 16 (n1sNatSumFast bm1 (oneNegCStep k b k0 k1 b0 b1))))
def oneNegBPosB01 (k b k0 k1 b0 b1 : ℕ) : ℕ :=
  n1sCbv (oneNegBPosBM1 k b k0 k1 b0 b1) (Nat.sub b 1)
def oneNegBStep (k k0 k1 b : ℕ) : ℕ := bif Nat.beq b 0 then Nat.mul 2
    (fOneNeg3OrdLit k 0 0 k0 k1 0 65025 0 65025) else n1sCbv2 (oneNegBPosB01 k b k0 k1)
    (Nat.mul b b) (Nat.mul (Nat.sub 255 b) (Nat.sub 255 b))
def oneNegKBPos (k b k0 k1 b0 b1 : ℕ) : ℕ :=
  Nat.mul 8 (fOneNeg3OrdLit k k b k0 k1 k0 k1 b0 b1)
def oneNegKBStep (k k0 k1 b : ℕ) : ℕ := bif Nat.beq b 0 then Nat.mul 4
    (fOneNeg3OrdLit k k 0 k0 k1 k0 k1 0 65025) else n1sCbv2 (oneNegKBPos k b k0 k1)
    (Nat.mul b b) (Nat.mul (Nat.sub 255 b) (Nat.sub 255 b))
def oneNegShellK01 (k k0 k1 : ℕ) : ℕ := Nat.add (Nat.add (Nat.mul 8 (fOneNeg3OrdLit k k k k0
    k1 k0 k1 k0 k1)) (Nat.mul 3 (n1sNatSumFast k (oneNegKBStep k k0 k1))))
    (Nat.mul 3 (n1sNatSumFast k (oneNegBStep k k0 k1)))
/-- Fast call-by-value shell evaluator for `octShell (... * fOneNeg3Sym)`. -/
def oneNegShellFast (k : ℕ) : ℕ := bif Nat.beq k 0 then 0 else n1sCbv2 (oneNegShellK01 k)
    (Nat.mul k k) (Nat.mul (Nat.sub 255 k) (Nat.sub 255 k))
theorem fOneNegOrdLit_eq_single {x y z : ℕ} (hy : y ≤ 127) (hzy : z ≤ y) : fOneNegOrdLit x y z
    (x * x) ((255 - x) * (255 - x)) (y * y) ((255 - y) * (255 - y)) (z * z)
    ((255 - z) * (255 - z)) = fOneNegSingle x y z := by
  unfold fOneNegOrdLit fOneNegSingle
  dsimp only
  simp only [max2Nat_eq_max, n1s_nat_add_eq, n1s_nat_sub_eq]
  have hb : (Nat.beq y 0 || Nat.beq z 0) = Nat.beq z 0 := by
    rcases y with _ | y'
    · have hz0 : z = 0 := by omega
      subst hz0; rfl
    · rfl
  have hm : max (bif Nat.beq y 0 then 0 else ceilDiv20Den (255 + x - (y + z)) (x * x + ((255 -
      y) * (255 - y) + z * z))) (bif Nat.beq z 0 then 0 else ceilDiv20Den (255 + x - (y + z))
      (x * x + (y * y + (255 - z) * (255 - z)))) = (bif Nat.beq y 0 then 0 else ceilDiv20Den
      (255 + x - (y + z)) (x * x + ((255 - y) * (255 - y) + z * z))) := by
    rcases z with _ | z'
    · exact Nat.max_zero _
    · rcases y with _ | y'
      · omega
      · change max (ceilDiv20Den _ _) (ceilDiv20Den _ _) = ceilDiv20Den _ _
        refine max_eq_left (ceilDiv_antitone (by positivity) ?_)
        zify [show y' + 1 ≤ 255 by omega, show z' + 1 ≤ 255 by omega]
        nlinarith
  rw [hb, hm]
section OpaqueOneNeg
attribute [local irreducible] fOneNegOrdLit fOneNegSingle fOneNeg3Sym
theorem fOneNeg3OrdLit_eq_sym {k b c : ℕ} (hk : k ≤ 127) (hbk : b ≤ k) (hcb : c ≤ b) :
    fOneNeg3OrdLit k b c (k * k) ((255 - k) * (255 - k)) (b * b) ((255 - b) * (255 - b))
    (c * c) ((255 - c) * (255 - c)) = fOneNeg3Sym k b c := by
  unfold fOneNeg3OrdLit
  rw[n1s_nat_add_eq, n1s_nat_add_eq, fOneNegOrdLit_eq_single (x := k) (by omega) hcb,
      fOneNegOrdLit_eq_single (x := b) hk (by omega), fOneNegOrdLit_eq_single (x := c) hk hbk]
  unfold fOneNeg3Sym
  rfl
attribute [local irreducible] fOneNeg3OrdLit
private theorem natSum_mul_left (c n : ℕ) (g : ℕ → ℕ) :
    natSum n (fun i ↦ c * g i) = c * natSum n g := by
  induction n with
  | zero => rfl
  | succ m ih =>
    change natSum m (fun i ↦ c * g i) + c * g m = c * (natSum m g + g m)
    rw [ih]; ring
private theorem bStep_zero_arith (x : ℕ) : 2 * x = 2 * 1 * 1 * x + 2 * 0 := by ring
private theorem bStep_pos_arith (x0 x1 x2 : ℕ) :
    8 * x0 + (8 * x1 + 16 * x2) = 2 * 2 * 2 * x1 + 2 * (4 * x0 + 8 * x2) := by ring
theorem oneNegShellFast_eq {k : ℕ} (hk : k ≤ 127) : oneNegShellFast k = octShell (fun a b c ↦
    octWeight a * octWeight b * octWeight c * fOneNeg3Sym a b c) k := by
  have hns0 (g : ℕ → ℕ) : natSum 0 g = 0 := rfl
  have hw0 : octWeight 0 = 1 := rfl
  rcases k with _ | k'
  · unfold oneNegShellFast octShell
    have hz0 : Nat.beq 0 0 = true := rfl
    rw [hz0]; dsimp only [cond]
    rw [hns0, hns0, fOneNeg3Sym_zero, hw0]
  · set k := k' + 1
    have hk_beq : Nat.beq k 0 = false := rfl
    have hwk : octWeight k = 2 := rfl
    unfold oneNegShellFast
    rw [hk_beq]; dsimp only [cond]
    rw [n1sCbv2_eq]
    unfold oneNegShellK01 octShell
    simp only [n1sNatSumFast_eq, n1s_nat_add_eq, n1s_nat_mul_eq, n1s_nat_sub_eq]
    have h1 : 8 * fOneNeg3OrdLit k k k (k * k) ((255 - k) * (255 - k))
        (k * k) ((255 - k) * (255 - k)) (k * k) ((255 - k) * (255 - k)) =
        octWeight k * octWeight k * octWeight k * fOneNeg3Sym k k k := by
      rw [fOneNeg3OrdLit_eq_sym hk (le_refl _) (le_refl _), hwk]
    have h2 : natSum k (oneNegKBStep k (k * k) ((255 - k) * (255 - k))) =
        natSum k (fun b ↦ octWeight k * octWeight k * octWeight b * fOneNeg3Sym k k b) := by
      refine natSum_congr fun b hb ↦ ?_
      rcases b with _ | b'
      · unfold oneNegKBStep
        have hz_beq : Nat.beq 0 0 = true := rfl
        rw [hz_beq]; dsimp only [cond]
        rw [n1s_nat_mul_eq, hwk, hw0]
        have heq0 : fOneNeg3OrdLit k k 0 (k * k) ((255 - k) * (255 - k))
            (k * k) ((255 - k) * (255 - k)) 0 65025 = fOneNeg3Sym k k 0 :=
          fOneNeg3OrdLit_eq_sym hk (le_refl _) (Nat.zero_le _)
        rw [heq0]
      · unfold oneNegKBStep
        have hb_beq : Nat.beq (b' + 1) 0 = false := rfl
        have hwb : octWeight (b' + 1) = 2 := rfl
        rw [hb_beq]; dsimp only [cond]
        rw [n1sCbv2_eq]; unfold oneNegKBPos
        simp only [n1s_nat_mul_eq, n1s_nat_sub_eq]
        rw [fOneNeg3OrdLit_eq_sym hk (le_refl _) (Nat.le_of_lt hb), hwk, hwb]
    have h3 : natSum k (oneNegBStep k (k * k) ((255 - k) * (255 - k))) =
        natSum k (fun b ↦ octWeight k * octWeight b * octWeight b * fOneNeg3Sym k b b +
          2 * natSum b (fun c ↦ octWeight k * octWeight b * octWeight c * fOneNeg3Sym k b c)) := by
      refine natSum_congr fun b hb ↦ ?_
      rcases b with _ | b'
      · unfold oneNegBStep
        have hz_beq : Nat.beq 0 0 = true := rfl
        rw [hz_beq]; dsimp only [cond]
        have heq00 : fOneNeg3OrdLit k 0 0 (k * k) ((255 - k) * (255 - k)) 0 65025 0 65025 =
            fOneNeg3Sym k 0 0 := fOneNeg3OrdLit_eq_sym hk (Nat.zero_le _) (le_refl _)
        rw [hns0, n1s_nat_mul_eq, hwk, hw0, heq00]
        exact bStep_zero_arith (fOneNeg3Sym k 0 0)
      · set b := b' + 1
        unfold oneNegBStep
        have hb_beq : Nat.beq b 0 = false := rfl
        have hwb : octWeight b = 2 := rfl
        rw [hb_beq]; dsimp only [cond]
        rw [n1sCbv2_eq]; unfold oneNegBPosB01; rw [n1sCbv_eq]; unfold oneNegBPosBM1
        simp only [n1sNatSumFast_eq, n1s_nat_add_eq, n1s_nat_mul_eq, n1s_nat_sub_eq]
        have hbm1 : b - 1 = b' := Nat.add_sub_cancel b' 1
        have hb0 : fOneNeg3OrdLit k b 0 (k * k) ((255 - k) * (255 - k))
            (b * b) ((255 - b) * (255 - b)) 0 65025 = fOneNeg3Sym k b 0 :=
          fOneNeg3OrdLit_eq_sym hk (Nat.le_of_lt hb) (Nat.zero_le _)
        have hbb : fOneNeg3OrdLit k b b (k * k) ((255 - k) * (255 - k)) (b * b)
            ((255 - b) * (255 - b)) (b * b) ((255 - b) * (255 - b)) = fOneNeg3Sym k b b :=
            fOneNeg3OrdLit_eq_sym hk (Nat.le_of_lt hb) (le_refl _)
        have hcsum : natSum b' (oneNegCStep k b (k * k) ((255 - k) * (255 - k)) (b * b) ((255
            - b) * (255 - b))) = natSum b' (fun j ↦ fOneNeg3Sym k b (j + 1)) := by
          refine natSum_congr fun j hj ↦ ?_
          unfold oneNegCStep; rw [n1sCbv_eq]; unfold oneNegCStepC; rw [n1sCbv2_eq]
          unfold oneNegCStepLit; simp only [n1s_nat_add_eq, n1s_nat_mul_eq, n1s_nat_sub_eq]
          exact fOneNeg3OrdLit_eq_sym hk (Nat.le_of_lt hb) (Nat.le_succ_of_le hj)
        have hsp : natSum b (fun c ↦ octWeight k * octWeight b * octWeight c * fOneNeg3Sym k b c) =
            4 * fOneNeg3Sym k b 0 + 8 * natSum b' (fun j ↦ fOneNeg3Sym k b (j + 1)) := by
          have hb_eq : b = 1 + b' := Nat.add_comm b' 1
          rw [hb_eq, natSum_add_split 1 b']
          have hhead : natSum 1 (fun c ↦ octWeight k * octWeight (1 + b') * octWeight c *
              fOneNeg3Sym k (1 + b') c) = 4 * fOneNeg3Sym k (1 + b') 0 := by
            have hns1 (g : ℕ → ℕ) : natSum 1 g = g 0 := Nat.zero_add (g 0)
            have hw1 : octWeight (1 + b') = 2 := by rw [Nat.add_comm]; rfl
            rw [hns1, hwk, hw1, hw0]
          have htail : natSum b' (fun i ↦ octWeight k * octWeight (1 + b') * octWeight (1 + i) *
              fOneNeg3Sym k (1 + b') (1 + i)) =
              8 * natSum b' (fun j ↦ fOneNeg3Sym k (1 + b') (j + 1)) := by
            rw [← natSum_mul_left 8 b']
            refine natSum_congr fun j _ ↦ ?_
            have hw1 : octWeight (1 + b') = 2 := by rw [Nat.add_comm]; rfl
            have hw2 : octWeight (1 + j) = 2 := by rw [Nat.add_comm]; rfl
            rw [hwk, hw1, hw2, Nat.add_comm 1 j]
          rw [hhead, htail]
        rw [hbm1, hb0, hbb, hcsum, hsp, hwk, hwb]
        exact bStep_pos_arith (fOneNeg3Sym k b 0) (fOneNeg3Sym k b b)
          (natSum b' (fun j ↦ fOneNeg3Sym k b (j + 1)))
    rw [h1, h2, h3]
end OpaqueOneNeg
theorem n1sShiftIdx_zero (g : ℕ → ℕ) : n1sShiftIdx 0 g = g := by
  rw [n1sShiftIdx_eq]; funext j; rw [Nat.zero_add]
theorem n1sShiftIdx_shift (c1 c2 : ℕ) (g : ℕ → ℕ) :
    (fun j ↦ g (c1 + (c2 + j))) = n1sShiftIdx (c1 + c2) g := by
  rw [n1sShiftIdx_eq]; funext j; rw [Nat.add_assoc]
theorem n1sNatSumFast_add_split (c a b : ℕ) (g : ℕ → ℕ) :
    n1sNatSumFast (a + b) (n1sShiftIdx c g) =
      n1sNatSumFast a (n1sShiftIdx c g) + n1sNatSumFast b (n1sShiftIdx (c + a) g) := by
  rw [n1sNatSumFast_eq, n1sNatSumFast_eq, n1sNatSumFast_eq,
    n1sShiftIdx_eq c g, natSum_add_split a b, ← n1sShiftIdx_shift c a g]
end GqspSlot3OctantOneNegBaseAndLo
end
end GqspSlot3OctantOneNegBaseAndLo

noncomputable section CoinPrepSub85AndAlphaOpt
set_option maxRecDepth 4096

section
/-!
# Jointly-Optimized 4-Wire `CleanPrepProg 4` 3-Coin Preparation & `Pruned1720` `PREPARE` Bundles
Jointly optimizes `(u0, mux2, mux3)` across the `(d0, d1)` `AffineLayer2` and `AnfLayer3`
move space and the `0`-`T`, `0`-`TOFF` 2-CNOT parity twist
`cParity2 = CNOT wCoin1 wCoin0 ;; CNOT wCoin2 wCoin0`
(shifting the active-coin partition on `wCoin0` to `(w0, w4, Z0)` at `u0` cost `15 T`)
for the constant-`α = 135,600` (`betaConst135600`) 3-coin preparation tiers (`.TOFF = 0`):
1. **Tier A (`err_w ≤ 15,854 / 10^9` and `≤ 18,000 / 10^9`)**:
   - `coinClean135600_c90` (`tCoin = 90`, `13,430 / 10^9 ≤ 15,854 / 10^9`,
     via `pCoinPrepParityGen` at `t0 = 15, L2 = 36, L3 = 35`),
     lifting to `prepBundlePruned1720_c90` (`tPrep = 90 + 1,720 = 1,810 T`).
   - `coinClean135600_c93` (`tCoin = 93`, `8,291 / 10^9 ≤ 15,854 / 10^9`,
     via `pCoinPrepGen` at `t0 = 18, L2 = 34, L3 = 37`),
     lifting to `prepBundlePruned1720_c93` (`tPrep = 93 + 1,720 = 1,813 T`).
2. **Tier B (`err_w ≤ 5,585 / 10^9` and `≤ 6,000 / 10^9`)**:
   - `coinClean135600_c94` (`tCoin = 94`, `5,194 / 10^9 ≤ 5,585 / 10^9`,
     via `pCoinPrepParityGen` at `t0 = 15, L2 = 36, L3 = 39`),
     lifting to `prepBundlePruned1720_c94` (`tPrep = 94 + 1,720 = 1,814 T`).
   - `coinClean135600_c95` (`tCoin = 95`, `3,066 / 10^9 ≤ 5,585 / 10^9`,
     via `pCoinPrepParityGen` at `t0 = 15, L2 = 36, L3 = 40`),
     lifting to `prepBundlePruned1720_c95` (`tPrep = 95 + 1,720 = 1,815 T`).
   - `coinClean135600_c96` (`tCoin = 96`, `5,822 / 10^9 ≤ 6,000 / 10^9`,
     via `pCoinPrepGen` at `t0 = 20, L2 = 35, L3 = 37`) and
     `coinClean135600_c97` (`tCoin = 97`, `5,478 / 10^9 ≤ 5,585 / 10^9`,
     via `pCoinPrepGen` at `t0 = 20, L2 = 35, L3 = 38`),
     lifting to `prepBundlePruned1720_c96` (`1,816 T`) and `prepBundlePruned1720_c97` (`1,817 T`).
3. **Tier C (`err_w ≤ 1,760 / 10^9` and `≤ 2,000 / 10^9`)**:
   - `coinClean135600_c101_tight` (`tCoin = 101`, `1,550 / 10^9 ≤ 1,760 / 10^9`,
     via `pCoinPrepGen` at `t0 = 19, L2 = 39, L3 = 39`),
     lifting to `prepBundlePruned1720_c101_tight` (`tPrep = 101 + 1,720 = 1,821 T`),
     plus `coinClean135600_c98` (`tCoin = 98`, `2,237 / 10^9`, lifting to `prepBundlePruned1720_c98`
     at `1,818 T`).
-/
namespace CoinPrepSub85AndAlphaOpt
section ConfigExt
set_option exponentiation.threshold 256
set_option backward.isDefEq.respectTransparency true
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
local instance (priority := 1000000) instNeZeroTwoPowK12 (k : ℕ) : NeZero (2 ^ k) :=
  ⟨Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos k)⟩
noncomputable section
open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt Real
open scoped Matrix BigOperators Matrix.Norms.L2Operator Circuit.Notation
open SpecsAux SpecsAux.SpecMirror
-- Root solution namespace already active.
open MeasureBranchHadamardSem (ket ket_CNOT)
open PosPostPrep80MergedVep (ket_eq_single_local)
open SegmentAndTopClosure (rCleanSubW cleanZeroEmbedIdx compressCleanUnitary)
open ZeroAncillaUSP (HSTGate hstWordTCount)
open ZeroSubwireCoinPrep80 (coinHwa wCoin0 wCoin1 wCoin2 wCoinAnc coin3Bit0 coin3Bit1 coin3Bit2
  basisBits_coin3_bits)
open Coin3PerHorizon5799 (CleanPrepProg PreservesWire preservesCleanSubW_of_preservesWire
  not_mem_support_seq_local not_mem_support_cnot_of_ne AffineLayer2 AnfLayer3 sCoinAnc4 pCoinPrepGen
  tBound_pCoinPrepGen_eq validDyn_pCoinPrepGen pCoinPrepGen_mulVec_zero bits4 bits4_0 bits4_1
  bits4_2 upd_bits4_0 cleanZeroEmbedIdx_coin4_eq_local cleanZeroEmbedIdx_coin4_zero_local
  coin3Col0AmpGen)
section SecParity2Combinator
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
/-- Zero-`.T`, zero-`.TOFF` 2-CNOT parity permutation on `(wCoin0, wCoin1, wCoin2)` mapping
`bits4 b0 b1 b2 0 ↦ bits4 (b0 + b1 + b2) b1 b2 0` (swapping coins `2 ↔ 3` and `4 ↔ 5`). -/
noncomputable def cParity2 : Circuit 4 :=
  Circuit.CNOT wCoin1 wCoin0 (by decide) ;;ᶜ
  Circuit.CNOT wCoin2 wCoin0 (by decide)
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
@[simp] theorem count_toff_cParity2 : cParity2.count PrimitiveGate.TOFF = 0 := rfl
@[simp] theorem count_t_cParity2 : cParity2.count PrimitiveGate.T = 0 := rfl
theorem not_mem_support_cParity2 : wCoinAnc ∉ cParity2.support := not_mem_support_seq_local
    (not_mem_support_cnot_of_ne _ (by decide) (by decide))
    (not_mem_support_cnot_of_ne _ (by decide) (by decide))
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem preservesWire_wCoinAnc_cParity2 : PreservesWire wCoinAnc cParity2.eval.1 :=
  PreservesWire.of_not_mem_support not_mem_support_cParity2
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
/-- 4-wire `CleanPrepProg 4` combining `pCoinPrepGen w0 ls2 ls3` with the 0-`T` parity twist
`cParity2`. -/
noncomputable def pCoinPrepParityGen
    (w0 : List HSTGate) (ls2 : List AffineLayer2) (ls3 : List AnfLayer3) : CleanPrepProg 4 :=
  CleanPrepProg.seq (pCoinPrepGen w0 ls2 ls3) (.circ cParity2)
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem tBound_pCoinPrepParityGen_eq
    (w0 : List HSTGate) (ls2 : List AffineLayer2) (ls3 : List AnfLayer3) :
    (pCoinPrepParityGen w0 ls2 ls3).tBound = (hstWordTCount w0 + ls2.length) + (4 + ls3.length) :=
      by
  have hc : (CleanPrepProg.circ cParity2).tBound = 0 := rfl
  change (pCoinPrepGen w0 ls2 ls3).tBound + (CleanPrepProg.circ cParity2).tBound = _
  rw [hc, add_zero, tBound_pCoinPrepGen_eq]
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem validDyn_pCoinPrepParityGen (w0 : List HSTGate) (ls2 : List AffineLayer2)
    (ls3 : List AnfLayer3) : CleanPrepProg.ValidDyn sCoinAnc4 (pCoinPrepParityGen w0 ls2 ls3)
    := ⟨validDyn_pCoinPrepGen w0 ls2 ls3, Finset.disjoint_singleton_right.mpr
    not_mem_support_cParity2⟩
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem pCoinPrepParityGen_preserves_clean (w0 : List HSTGate) (ls2 : List AffineLayer2)
    (ls3 : List AnfLayer3) : (rCleanSubW 3 1 4 coinHwa).basisOutcomeProjector 0 *
    (pCoinPrepParityGen w0 ls2 ls3).toCircuit.eval.1 *
    (rCleanSubW 3 1 4 coinHwa).basisOutcomeProjector 0 =
    (pCoinPrepParityGen w0 ls2 ls3).toCircuit.eval.1 *
    (rCleanSubW 3 1 4 coinHwa).basisOutcomeProjector 0 := by
  refine preservesCleanSubW_of_preservesWire coinHwa _ fun w hw ↦ ?_
  have hwEq : w = wCoinAnc := by ext; change w.val = 3; omega
  subst hwEq
  have hBase : PreservesWire wCoinAnc (pCoinPrepGen w0 ls2 ls3).toCircuit.eval.1 := by
    have h1 : PreservesWire wCoinAnc (Coin3PerHorizon5799.cStages1To2HGen w0 ls2).eval.1 :=
      PreservesWire.of_not_mem_support (Coin3PerHorizon5799.not_mem_support_cStages1To2HGen w0 ls2)
    have hToff : PreservesWire wCoinAnc ((Circuit.TOFF wCoin0 wCoin1 wCoinAnc (by decide)
        (by decide) (by decide)).eval.1 * (Coin3PerHorizon5799.cAnfMux3 ls3).eval.1 *
        (Circuit.TOFF wCoin0 wCoin1 wCoinAnc (by decide) (by decide) (by decide)).eval.1) :=
        PreservesWire.toff_sandwich_target (by decide) (by decide) (by decide)
        (Coin3PerHorizon5799.preservesWire_cAnfMux3_of_ne _ (by decide))
        (Coin3PerHorizon5799.preservesWire_cAnfMux3_of_ne _ (by decide))
        (Coin3PerHorizon5799.preservesWire_cAnfMux3_of_ne _ (by decide))
    simp only [pCoinPrepGen, Coin3PerHorizon5799.pStage3Gen, CleanPrepProg.toCircuit,
      Circuit.eval_seq, Submonoid.coe_mul]
    exact hToff.mul h1
  simp only [pCoinPrepParityGen, CleanPrepProg.toCircuit, Circuit.eval_seq, Submonoid.coe_mul]
  exact preservesWire_wCoinAnc_cParity2.mul hBase
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
/-- Compressed 3-coin unitary for `pCoinPrepParityGen w0 ls2 ls3`. -/
noncomputable def uCoin3ParityGen
    (w0 : List HSTGate) (ls2 : List AffineLayer2) (ls3 : List AnfLayer3) : Unitary (2 ^ 3) :=
  compressCleanUnitary coinHwa (pCoinPrepParityGen w0 ls2 ls3).toCircuit.eval
    (pCoinPrepParityGen_preserves_clean w0 ls2 ls3)
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem cParity2_mulVec_ket (b0 b1 b2 : ZMod 2) : cParity2.eval.1.mulVec
    (ket (bits4 b0 b1 b2 0)) = ket (bits4 (b0 + b1 + b2) b1 b2 0) := by
  dsimp only [cParity2]
  rw [MeasureBranchHadamardSem.eval_seq_mulVec, ket_CNOT, bits4_0, bits4_1, upd_bits4_0,
    ket_CNOT, bits4_0, bits4_2, upd_bits4_0]
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
/-- Column-0 amplitude map of `uCoin3ParityGen`, permuting `coin3Col0AmpGen` by `2 ↔ 3` and `4 ↔
5`. -/
noncomputable def coin3Col0AmpParityGen
    (w0 : List HSTGate) (ls2 : List AffineLayer2) (ls3 : List AnfLayer3) : Fin 8 → ℂ
  | ⟨0, _⟩ => coin3Col0AmpGen w0 ls2 ls3 0
  | ⟨1, _⟩ => coin3Col0AmpGen w0 ls2 ls3 1
  | ⟨2, _⟩ => coin3Col0AmpGen w0 ls2 ls3 3
  | ⟨3, _⟩ => coin3Col0AmpGen w0 ls2 ls3 2
  | ⟨4, _⟩ => coin3Col0AmpGen w0 ls2 ls3 5
  | ⟨5, _⟩ => coin3Col0AmpGen w0 ls2 ls3 4
  | ⟨6, _⟩ => coin3Col0AmpGen w0 ls2 ls3 6
  | ⟨7, _⟩ => coin3Col0AmpGen w0 ls2 ls3 7
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem pCoinPrepParityGen_mulVec_zero (w0 : List HSTGate) (ls2 : List AffineLayer2)
    (ls3 : List AnfLayer3) : (pCoinPrepParityGen w0 ls2 ls3).toCircuit.eval.1.mulVec
    (ket (bits4 0 0 0 0)) = coin3Col0AmpParityGen w0 ls2 ls3 0 • ket (bits4 0 0 0 0) +
    coin3Col0AmpParityGen w0 ls2 ls3 1 • ket (bits4 1 0 0 0) + coin3Col0AmpParityGen w0 ls2
    ls3 2 • ket (bits4 0 1 0 0) + coin3Col0AmpParityGen w0 ls2 ls3 3 • ket (bits4 1 1 0 0) +
    coin3Col0AmpParityGen w0 ls2 ls3 4 • ket (bits4 0 0 1 0) + coin3Col0AmpParityGen w0 ls2
    ls3 5 • ket (bits4 1 0 1 0) + coin3Col0AmpParityGen w0 ls2 ls3 6 • ket (bits4 0 1 1 0) +
    coin3Col0AmpParityGen w0 ls2 ls3 7 • ket (bits4 1 1 1 0) := by
  have hSeq : (pCoinPrepParityGen w0 ls2 ls3).toCircuit.eval.1 =
      cParity2.eval.1 * (pCoinPrepGen w0 ls2 ls3).toCircuit.eval.1 := rfl
  rw [hSeq, ← Matrix.mulVec_mulVec, pCoinPrepGen_mulVec_zero]
  simp only [Matrix.mulVec_add, Matrix.mulVec_smul, cParity2_mulVec_ket]
  have h000 : (0 + 0 + 0 : ZMod 2) = 0 := rfl
  have h100 : (1 + 0 + 0 : ZMod 2) = 1 := rfl
  have h010 : (0 + 1 + 0 : ZMod 2) = 1 := rfl
  have h110 : (1 + 1 + 0 : ZMod 2) = 0 := rfl
  have h001 : (0 + 0 + 1 : ZMod 2) = 1 := rfl
  have h101 : (1 + 0 + 1 : ZMod 2) = 0 := rfl
  have h011 : (0 + 1 + 1 : ZMod 2) = 0 := rfl
  have h111 : (1 + 1 + 1 : ZMod 2) = 1 := rfl
  rw [h000, h100, h010, h110, h001, h101, h011, h111]
  dsimp only [coin3Col0AmpParityGen]
  abel
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem uCoin3ParityGen_col0_eq
    (w0 : List HSTGate) (ls2 : List AffineLayer2) (ls3 : List AnfLayer3) (c : Fin 8) :
    (uCoin3ParityGen w0 ls2 ls3).1 c 0 = coin3Col0AmpParityGen w0 ls2 ls3 c := by
  change (pCoinPrepParityGen w0 ls2 ls3).toCircuit.eval.1 (cleanZeroEmbedIdx coinHwa c)
    (cleanZeroEmbedIdx coinHwa 0) = coin3Col0AmpParityGen w0 ls2 ls3 c
  have hket0 : ket (bits4 0 0 0 0) = Pi.single (cleanZeroEmbedIdx coinHwa 0) (1 : ℂ) := by
    rw [cleanZeroEmbedIdx_coin4_zero_local, ket_eq_single_local]
  have hCol : (pCoinPrepParityGen w0 ls2 ls3).toCircuit.eval.1 (cleanZeroEmbedIdx coinHwa c)
      (cleanZeroEmbedIdx coinHwa 0) = ((pCoinPrepParityGen w0 ls2 ls3).toCircuit.eval.1.mulVec
      (ket (bits4 0 0 0 0))) (cleanZeroEmbedIdx coinHwa c) := by
    rw [hket0]
    exact (congrFun (Matrix.mulVec_single_one (pCoinPrepParityGen w0 ls2 ls3).toCircuit.eval.1
      (cleanZeroEmbedIdx coinHwa 0)) (cleanZeroEmbedIdx coinHwa c)).symm
  rw [hCol, pCoinPrepParityGen_mulVec_zero w0 ls2 ls3]
  have hbits_inj {a0 a1 a2 b0 b1 b2 : ZMod 2} (h : (basisBitsEquiv 4).symm (bits4 a0 a1 a2 0)
      = (basisBitsEquiv 4).symm (bits4 b0 b1 b2 0)) : a0 = b0 ∧ a1 = b1 ∧ a2 = b2 := by
    have hf := (basisBitsEquiv 4).symm.injective h
    exact ⟨congrFun hf wCoin0, congrFun hf wCoin1, congrFun hf wCoin2⟩
  have hne {a0 a1 a2 b0 b1 b2 : ZMod 2} (hd : ¬ (a0 = b0 ∧ a1 = b1 ∧ a2 = b2)) :
      (basisBitsEquiv 4).symm (bits4 b0 b1 b2 0) ≠ (basisBitsEquiv 4).symm (bits4 a0 a1 a2 0)
      := fun h ↦ hd (hbits_inj h.symm)
  rcases basisBits_coin3_bits c with ⟨hb0, hb1, hb2⟩
  rw [cleanZeroEmbedIdx_coin4_eq_local c, hb0, hb1, hb2]
  simp only [Pi.add_apply, Pi.smul_apply, ket_eq_single_local, smul_eq_mul]
  fin_cases c <;>
  · dsimp only [coin3Bit0, coin3Bit1, coin3Bit2, coin3Col0AmpParityGen]
    repeat (first
      | rw [Pi.single_eq_same]
      | rw [Pi.single_eq_of_ne (hne (by decide))])
    ring
end SecParity2Combinator
end
end ConfigExt
end CoinPrepSub85AndAlphaOpt
end
end CoinPrepSub85AndAlphaOpt

noncomputable section Leaf2RedirectAndHeldOrbit
set_option maxRecDepth 20000

section
/-!
# `Pass 2` Mod-4 Position Phase Oracle: Packed-`12` `(v, w)` + `rOrbit16`-Held `u` Orbit Sandwich,
# Asymmetric Partner-2D Redirect, & W-State `MidK6`
Constructs the `190w` `dSelCtrl` and `196w` `dSelCat` `Pass 2` position phase oracles (`0` `.TOFF`):
1. **Packed-`12` `(v, w)` + `rOrbit16`-Held `u` Orbit-Rank Sandwich (`dOrbitSandPacked12_138`,
`1,416 + dMid.count .T` `.T`)**:
   - Compresses the canonical pair `(c.v, c.w)` (`0 ≤ c.v ≤ c.w ≤ 64`, avoiding `v_6 = w_6 = 1 ∧ v_5
   = 1`)
     losslessly into `12` bits (`packVWBits12`) on `rHold12 := rClean.slice 0 12`, and stores the
     `7`-bit `c.u` directly in `rOrbit16` (`dPack12`, `96` `TempAnd`s = `384 T`).
   - Adds `triNum c.v.val + tetNum c.w.val` mod `2^16` in-place into `rOrbit16`
   (`dAddTailFrom12_138`,
     `81` `TempAnd`s = `324 T`) and uncomputes after `dMid` via two's-complement modular subtraction
     (`dSubTailFrom12_138`, `81` `TempAnd`s = `324 T`) + `dPack12` (`384 T`), passing
     `rClean.slice 12 (mClean - 12)` (`126+` clean wires on `138 ≤ mClean`) to `dMid`.
2. **Combined `Pass 2` Oracles (Asymmetric Partner-2D + W-State `MidK6` +
   `dOrbitSandPacked12_138`)**:
   - `dPass2Mod4Ctrl190FromMid12Asym` (`190 ≤ mWB`, `34,597 + tMid` `.T`).
   - `dPass2Ctrl190Packed12AsymWState` (`190 ≤ mWB`):
     * `40,369 + 260 * B` `.T` for `B ≤ 24` (or `196 ≤ mWB`),
     * `40,385 + 260 * B` `.T` for `25 ≤ B ≤ 27` at `mWB = 190`.
   - `dPass2Cat196Packed18AsymWState` (`196 ≤ mWB`):
     * `40,329 + 260 * B` `.T` for `B ≤ 24` (or `202 ≤ mWB`),
     * `40,345 + 260 * B` `.T` for `25 ≤ B ≤ 27` at `mWB = 196`.
   - `leaf2SpecPacked12AsymWStateOfB`, `leaf2SpecPacked12AsymWStateOfB_le24`, and
     `leaf2SpecPacked12AsymWStateOfB_40385` (`Leaf2SpecOfTrunc`).
   - `dPass2Packed31And12AsymWState221` (`221 ≤ mWB`, `40,281 / 40,297 + 260 * B` `.T`)
     and `dPass2Packed31HeldKAsymWState` (`K ≤ 23`, `227 + K ≤ mWB`,
     down to `40,081 + 260 * B` `.T`).
-/
namespace OrbitSandPacked12
set_option maxRecDepth 4096
open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt HermitianMat Real
open scoped Matrix ComplexOrder MatrixOrder BigOperators Circuit.Notation
open Dyadic128CoulombMath
open MeasureBranchHadamardSem (ket eval_seq_mulVec ket_CNOT projZeroAll projZeroAll_conjTranspose
  bit_cases)
open PosSlots24BranchConcrete (posCoreWires wSlot0Core rCosetB0 rCosetB1 rElecSlot axisBitRev6)
open PosSlots24PartnerMux288 (rawOrbitCoord128)
open PosSlots24PartnerMuxZeroT123 (toDynWithDyn toDynWithDyn_count_toff toDynWithDyn_count_t)
open PosSlots24OrbitToggleFast288 hiding ite_pos ite_neg dite_pos dite_neg rawOrbitCoord128
  orbitRankFin16 matrix_ext_ket basisBits_symm_apply_at
open PosSlots24SpectatorPrunedPhase (p2t_ketPredProj p2t_ketPredProj_conjTranspose
  p2t_RealizesConstCleanUnitary p2t_RealizesConstCleanUnitary_circuit
  p2t_RealizesConstCleanUnitary_mono_proj)
open PosTailWithAnchor18_244 (castAssign castAssign_lt cleanRem_castAssign_iff progSupportsBelowB
  ctxSupportsBelowB truncateProgB truncateCtxB truncateCtxB_countTempAnd ctxSupportsBelowB_plug
  truncateCtxB_plug truncateCtxB_fwdBits truncateProgB_evalBits truncateProgB_validCleanRem
  constClean_toDynWithDyn_perm)
open OrbitSandPacked18
local instance (priority := 1000000) instNeZeroTwoPowAux (k : ℕ) : NeZero (2 ^ k) :=
  ⟨Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos k)⟩
local instance (priority := 1000000) instNeZero143 : NeZero 143 := ⟨by decide⟩
local instance (priority := 1000000) instNeZero163 : NeZero 163 := ⟨by decide⟩
theorem fin65Bits7_bit6_low015 :
    ∀ x : Fin 65, fin65Bits7 x 6 = 1 →
      fin65Bits7 x 0 = 0 ∧ fin65Bits7 x 1 = 0 ∧ fin65Bits7 x 5 = 0 := fun x hx ↦ by
  have h64 : x = ⟨64, by decide⟩ := Fin.ext ((fin65Bits7_bit6 x).mp hx)
  subst h64; decide
/-- `12`-bit encoding of `(V, W)` with `t_pack = V 5 * W 6`. -/
def packVWBits12 (V W : Fin 7 → ZMod 2) (t_pack : ZMod 2) (k : Fin 12) : ZMod 2 :=
  match k.val with
  | 0 => V 0
  | 1 => V 1
  | 2 => V 2
  | 3 => V 3
  | 4 => V 4
  | 5 => W 0 + t_pack
  | 6 => W 1 + V 6
  | 7 => W 2
  | 8 => W 3
  | 9 => W 4
  | 10 => V 5 + W 6 + t_pack
  | _ => W 5
/-- `12`-bit lossless encoding of `(c.v, c.w)` for `c : CanonicalTriple65`. -/
def packCanonVW12 (c : CanonicalTriple65) : Fin 12 → ZMod 2 :=
  packVWBits12 (fin65Bits7 c.v) (fin65Bits7 c.w) (fin65Bits7 c.v 5 * fin65Bits7 c.w 6)
theorem unpackVW6_algebra (v5 v6 w0 w1 w5 w6 : ZMod 2) :
    (v6 = 1 → v5 = 0 ∧ w6 = 1) →
    (w6 = 1 → w0 = 0 ∧ w1 = 0 ∧ w5 = 0) →
    (v5 = 1 → w5 = 1 ∨ w6 = 1) →
    let tp := v5 * w6
    let b5 := w0 + tp
    let b6 := w1 + v6
    let b10 := v5 + w6 + tp
    let b11 := w5
    let t1 := b10 * (b11 + 1)
    let t2 := t1 * b5
    let t3 := t1 * b6
    t1 = w6 ∧
    t2 = tp ∧
    t3 = v6 ∧
    b5 + t2 = w0 ∧
    b6 + t3 = w1 ∧
    b10 + t1 + t2 = v5 := by
  intro hv6 hw6 hv5
  dsimp only
  rcases bit_cases v6 with rfl | rfl
  · rcases bit_cases w6 with rfl | rfl
    · revert hv5
      rcases bit_cases v5 with rfl | rfl <;>
      rcases bit_cases w5 with rfl | rfl <;>
      rcases bit_cases w0 with rfl | rfl <;>
      rcases bit_cases w1 with rfl | rfl <;>
      decide
    · obtain ⟨rfl, rfl, rfl⟩ := hw6 rfl
      rcases bit_cases v5 with rfl | rfl <;> decide
  · obtain ⟨rfl, rfl⟩ := hv6 rfl
    obtain ⟨rfl, rfl, rfl⟩ := hw6 rfl
    decide
theorem unpackCanonVW12_algebra (c : CanonicalTriple65) :
    let V := fin65Bits7 c.v
    let W := fin65Bits7 c.w
    let b := packCanonVW12 c
    let t1 := b 10 * (b 11 + 1)
    let t2 := t1 * b 5
    let t3 := t1 * b 6
    t1 = W 6 ∧
    t2 = V 5 * W 6 ∧
    t3 = V 6 ∧
    b 5 + t2 = W 0 ∧
    b 6 + t3 = W 1 ∧
    b 10 + t1 + t2 = V 5 := by
  have hvw : c.v.val ≤ c.w.val := c.vw
  have hcw : c.w.val ≤ 64 := Nat.le_of_lt_succ c.w.isLt
  have h1 : fin65Bits7 c.v 6 = 1 → fin65Bits7 c.v 5 = 0 ∧ fin65Bits7 c.w 6 = 1 := fun hv6 ↦ by
    obtain ⟨_, _, hv5⟩ := fin65Bits7_bit6_low015 c.v hv6
    have hv64 : c.v.val = 64 := (fin65Bits7_bit6 c.v).mp hv6
    exact ⟨hv5, (fin65Bits7_bit6 c.w).mpr (by omega)⟩
  have h2 : fin65Bits7 c.w 6 = 1 → fin65Bits7 c.w 0 = 0 ∧ fin65Bits7 c.w 1 = 0 ∧ fin65Bits7
      c.w 5 = 0 := fin65Bits7_bit6_low015 c.w
  have h3 : fin65Bits7 c.v 5 = 1 → fin65Bits7 c.w 5 = 1 ∨ fin65Bits7 c.w 6 = 1 := fun hv5 ↦ by
    obtain ⟨h32, _⟩ := (fin65Bits7_bit5 c.v).mp hv5
    by_cases hw64 : c.w.val = 64
    · exact Or.inr ((fin65Bits7_bit6 c.w).mpr hw64)
    · exact Or.inl ((fin65Bits7_bit5 c.w).mpr ⟨by omega, by omega⟩)
  exact unpackVW6_algebra (fin65Bits7 c.v 5) (fin65Bits7 c.v 6) (fin65Bits7 c.w 0)
    (fin65Bits7 c.w 1) (fin65Bits7 c.w 5) (fin65Bits7 c.w 6) h1 h2 h3
theorem TempCtx.disjointFrom_false {M : ℕ} :
    ∀ K : TempCtx M, K.DisjointFrom (fun _ ↦ False)
  | .hole => trivial
  | .seqPre c K =>
      have hc : CliffDisjoint (fun _ ↦ False) c := by
        induction c with
        | nil => exact trivial
        | x _ => exact not_false
        | cnot _ _ _ => exact ⟨not_false, not_false⟩
        | seq _ _ ih1 ih2 => exact ⟨ih1, ih2⟩
      ⟨hc, TempCtx.disjointFrom_false K⟩
  | .seqPost K c =>
      have hc : CliffDisjoint (fun _ ↦ False) c := by
        induction c with
        | nil => exact trivial
        | x _ => exact not_false
        | cnot _ _ _ => exact ⟨not_false, not_false⟩
        | seq _ _ ih1 ih2 => exact ⟨ih1, ih2⟩
      ⟨TempCtx.disjointFrom_false K, hc⟩
  | .tempAnd _ _ _ _ _ _ K =>
      ⟨not_false, not_false, not_false, TempCtx.disjointFrom_false K⟩
theorem TempCtx.append_fwdBits {M : ℕ} :
    ∀ (F G : TempCtx M) (γ : BitAssignment M),
      (F.append G).fwdBits γ = G.fwdBits (F.fwdBits γ)
  | .hole, _, _ => rfl
  | .seqPre c K, G, γ => TempCtx.append_fwdBits K G (c.eval γ)
  | .seqPost K _, G, γ => TempCtx.append_fwdBits K G γ
  | .tempAnd c₁ c₂ anc _ _ _ K, G, γ =>
      TempCtx.append_fwdBits K G (Function.update γ anc (γ anc + γ c₁ * γ c₂))
theorem TempCtx.fwdBits_outside {M c : ℕ} :
    ∀ (K : TempCtx M), K.SupportsBelowCtx c →
      ∀ (γ : BitAssignment M) (w : Wire M), c ≤ w.val → K.fwdBits γ w = γ w
  | .hole, _, _, _, _ => rfl
  | .seqPre cl K, ⟨hcl, hK⟩, γ, w, hw =>
      (TempCtx.fwdBits_outside K hK (cl.eval γ) w hw).trans (cl.eval_outside hcl γ w hw)
  | .seqPost K _, ⟨hK, _⟩, _γ, w, hw =>
      TempCtx.fwdBits_outside K hK _γ w hw
  | .tempAnd _ _ _anc _ _ _ K, ⟨hanc, hK⟩, _γ, w, hw =>
      (TempCtx.fwdBits_outside K hK _ w hw).trans
        (Function.update_of_ne (wire_ne_of_gt (lt_of_lt_of_le hanc hw)) _ _)
theorem supportsBelow_of_cliffSupportsBelowB {M bound : ℕ} :
    ∀ {c : CliffProg M}, PosTailWithAnchor18_244.cliffSupportsBelowB bound c = true →
      c.SupportsBelow bound
  | .nil, _ => trivial
  | .x _, h => by dsimp [CliffProg.SupportsBelow]; exact of_decide_eq_true h
  | .cnot _ _ _, h => by
      dsimp [CliffProg.SupportsBelow]
      exact ⟨of_decide_eq_true (Bool.and_eq_true _ _ |>.mp h).1,
             of_decide_eq_true (Bool.and_eq_true _ _ |>.mp h).2⟩
  | .seq _ _, h =>
      ⟨supportsBelow_of_cliffSupportsBelowB (Bool.and_eq_true _ _ |>.mp h).1,
       supportsBelow_of_cliffSupportsBelowB (Bool.and_eq_true _ _ |>.mp h).2⟩
theorem supportsBelowCtx_of_ctxSupportsBelowB {M bound : ℕ} :
    ∀ {K : TempCtx M}, ctxSupportsBelowB bound K = true → K.SupportsBelowCtx bound
  | .hole, _ => trivial
  | .seqPre _ _, h =>
      ⟨supportsBelow_of_cliffSupportsBelowB (Bool.and_eq_true _ _ |>.mp h).1,
       supportsBelowCtx_of_ctxSupportsBelowB (Bool.and_eq_true _ _ |>.mp h).2⟩
  | .seqPost _ _, h =>
      ⟨supportsBelowCtx_of_ctxSupportsBelowB (Bool.and_eq_true _ _ |>.mp h).1,
       supportsBelow_of_cliffSupportsBelowB (Bool.and_eq_true _ _ |>.mp h).2⟩
  | .tempAnd _ _ anc _ _ _ _, h =>
      have h1 := Bool.and_eq_true _ _ |>.mp h
      have h2 := Bool.and_eq_true _ _ |>.mp h1.2
      have h3 := Bool.and_eq_true _ _ |>.mp h2.2
      ⟨of_decide_eq_true (h3.1 : decide (anc.val < bound) = true),
       supportsBelowCtx_of_ctxSupportsBelowB h3.2⟩
set_option maxRecDepth 20000 in
theorem packCtx303_supp163 (slot2SwappedTo0 : Bool) :
    ctxSupportsBelowB 163 (packCtx303 slot2SwappedTo0) = true := by
  cases slot2SwappedTo0 <;> decide
def packCtx163Pre (slot2SwappedTo0 : Bool) : TempCtx 163 :=
  truncateCtxB 163 (packCtx303 slot2SwappedTo0) (packCtx303_supp163 slot2SwappedTo0)
theorem packCtx163Pre_countTempAnd (slot2SwappedTo0 : Bool) :
    (packCtx163Pre slot2SwappedTo0).countTempAnd = 95 := by
  rw [packCtx163Pre, truncateCtxB_countTempAnd, packCtx303_countTempAnd]
set_option maxRecDepth 20000 in
theorem packCtx163Pre_supp162B (slot2SwappedTo0 : Bool) :
    ctxSupportsBelowB 162 (packCtx163Pre slot2SwappedTo0) = true := by
  cases slot2SwappedTo0 <;> decide
theorem packCtx163Pre_supp162 (slot2SwappedTo0 : Bool) :
    (packCtx163Pre slot2SwappedTo0).SupportsBelowCtx 162 :=
  supportsBelowCtx_of_ctxSupportsBelowB (packCtx163Pre_supp162B slot2SwappedTo0)
def wZero163 : Wire 163 := ⟨59, by decide⟩
def wTPack163 : Wire 163 := ⟨162, by decide⟩
theorem u7Wire_lt163 : ∀ k : Fin 7, (u7Wire k).val < 163 := by decide
theorem v7Wire_lt163 : ∀ k : Fin 7, (v7Wire k).val < 163 := by decide
theorem w7Wire_lt163 : ∀ k : Fin 7, (w7Wire k).val < 163 := by decide
def u7W163 (k : Fin 7) : Wire 163 := ⟨(u7Wire k).val, u7Wire_lt163 k⟩
def v7W163 (k : Fin 7) : Wire 163 := ⟨(v7Wire k).val, v7Wire_lt163 k⟩
def w7W163 (k : Fin 7) : Wire 163 := ⟨(w7Wire k).val, w7Wire_lt163 k⟩
theorem u7W163_ne_tPack (k : Fin 7) : u7W163 k ≠ wTPack163 := by
  fin_cases k <;> decide
theorem v7W163_ne_tPack (k : Fin 7) : v7W163 k ≠ wTPack163 := by
  fin_cases k <;> decide
theorem w7W163_ne_tPack (k : Fin 7) : w7W163 k ≠ wTPack163 := by
  fin_cases k <;> decide
def packCtx163 (slot2SwappedTo0 : Bool) : TempCtx 163 :=
  (packCtx163Pre slot2SwappedTo0).append
    (ctxTempBit (v7W163 5) (w7W163 6) wTPack163 (by decide) (by decide) (by decide))
theorem packCtx163_countTempAnd (slot2SwappedTo0 : Bool) :
    (packCtx163 slot2SwappedTo0).countTempAnd = 96 := by
  rw [packCtx163, tempCtx_append_count, packCtx163Pre_countTempAnd]
  rfl
theorem packCtx163_spec (slot2SwappedTo0 : Bool) :
    ValidCleanRem 163 104 ((packCtx163 slot2SwappedTo0).plug (.z wZero163)) ∧
    (∀ γ : BitAssignment 163, cleanRem 163 104 γ →
      ((packCtx163 slot2SwappedTo0).plug (.z wZero163)).evalBits γ = γ) ∧
    (∀ γ : BitAssignment 163, cleanRem 163 104 γ →
      let β := castAssign (M := 303) γ
      let c := canonTriple128 (rawOrbitCoord128 slot2SwappedTo0
        (coreViewOf303 β) (partnerViewOf303 β))
      (∀ k : Fin 7, (packCtx163 slot2SwappedTo0).fwdBits γ (u7W163 k) = fin65Bits7 c.u k) ∧
      (∀ k : Fin 7, (packCtx163 slot2SwappedTo0).fwdBits γ (v7W163 k) = fin65Bits7 c.v k) ∧
      (∀ k : Fin 7, (packCtx163 slot2SwappedTo0).fwdBits γ (w7W163 k) = fin65Bits7 c.w k) ∧
      (packCtx163 slot2SwappedTo0).fwdBits γ wTPack163 =
        fin65Bits7 c.v 5 * fin65Bits7 c.w 6) := by
  obtain ⟨hv303, hbits303, hfwd303⟩ := packCtx303_spec slot2SwappedTo0
  have hz_supp : progSupportsBelowB 163 (.z wZero) = true := by decide
  have hplugPre : (packCtx163Pre slot2SwappedTo0).plug (.z wZero163) = truncateProgB 163
      ((packCtx303 slot2SwappedTo0).plug (.z wZero)) (ctxSupportsBelowB_plug
      (packCtx303_supp163 slot2SwappedTo0) hz_supp) := truncateCtxB_plug
      (packCtx303 slot2SwappedTo0) (packCtx303_supp163 slot2SwappedTo0) (.z wZero) hz_supp
  have hvPre : ValidCleanRem 163 104
      ((packCtx163Pre slot2SwappedTo0).plug (.z wZero163)) := by
    rw [hplugPre]
    exact truncateProgB_validCleanRem (M' := 163) (M := 303) (by decide) _ _ 244 hv303
  have hbitsPre : ∀ γ : BitAssignment 163, cleanRem 163 104 γ →
      ((packCtx163Pre slot2SwappedTo0).plug (.z wZero163)).evalBits γ = γ := fun γ hγ ↦ by
    have hcl303 := (cleanRem_castAssign_iff (M' := 163) (M := 303) (by decide) 244 γ).mp hγ
    funext w
    let w303 : Wire 303 := ⟨w.val, lt_of_lt_of_le w.isLt (by decide)⟩
    have hev := congrFun (truncateProgB_evalBits (M' := 163) (M := 303) (by decide)
      ((packCtx303 slot2SwappedTo0).plug (.z wZero))
      (ctxSupportsBelowB_plug (packCtx303_supp163 slot2SwappedTo0) hz_supp) γ) w303
    rw [← hplugPre, castAssign_lt _ w303 w.isLt, hbits303 _ hcl303, castAssign_lt _ w303 w.isLt]
      at hev
    exact hev
  let leaf1 : TempPhaseProg 163 :=
    (ctxTempBit (v7W163 5) (w7W163 6) wTPack163 (by decide) (by decide) (by decide)).plug (.z
      wZero163)
  have hLeafValid : ValidCleanRem 163 (163 - 162) leaf1 :=
    ⟨by decide, trivial, fun _ _ ↦ ⟨rfl, rfl, rfl⟩⟩
  have hLeafBits : ∀ δ : BitAssignment 163, leaf1.evalBits δ = δ := fun δ ↦ by
    funext w
    dsimp only [leaf1, ctxTempBit, TempCtx.plug, TempPhaseProg.evalBits]
    by_cases hw : w = wTPack163
    · subst hw
      simp [Function.update_self, Function.update_of_ne (v7W163_ne_tPack 5),
        Function.update_of_ne (w7W163_ne_tPack 6), CharTwo.add_cancel_right]
    · simp [Function.update_of_ne hw]
  have hPlugFull : (packCtx163 slot2SwappedTo0).plug (.z wZero163) =
      (packCtx163Pre slot2SwappedTo0).plug leaf1 := TempCtx.append_plug _ _ _
  have hv163 : ValidCleanRem 163 104 ((packCtx163 slot2SwappedTo0).plug (.z wZero163)) := by
    rw [hPlugFull]
    exact TempCtx.plug_validCleanRem
      (TempCtx.disjointFrom_false (packCtx163Pre slot2SwappedTo0))
      (packCtx163Pre_supp162 slot2SwappedTo0)
      hLeafValid (fun γ w _ ↦ congrFun (hLeafBits γ) w) wZero163 (by decide) hvPre
  refine ⟨hv163, fun γ hγ ↦ ?_, fun γ hγ ↦ ?_⟩
  · rw [hPlugFull]
    have hEqPre : ((packCtx163Pre slot2SwappedTo0).plug leaf1).evalBits γ =
        ((packCtx163Pre slot2SwappedTo0).plug (.z wZero163)).evalBits γ := by
      funext w
      exact (TempCtx.plug_evalBits_split (TempCtx.disjointFrom_false (packCtx163Pre
        slot2SwappedTo0)) (fun δ u _ ↦ congrFun (hLeafBits δ) u) wZero163 γ).2 w not_false
    exact hEqPre.trans (hbitsPre γ hγ)
  · have hcl303 := (cleanRem_castAssign_iff (M' := 163) (M := 303) (by decide) 244 γ).mp hγ
    obtain ⟨hu, hv, hw⟩ := hfwd303 (castAssign (M := 303) γ) hcl303
    have hfc := truncateCtxB_fwdBits (M' := 163) (M := 303) (by decide)
      (packCtx303 slot2SwappedTo0) (packCtx303_supp163 slot2SwappedTo0) γ
    have hPreU : ∀ k : Fin 7, (packCtx163Pre slot2SwappedTo0).fwdBits γ (u7W163 k) = fin65Bits7 _
      k := fun k ↦ by
      have hk := congrFun hfc (u7Wire k)
      rw [castAssign_lt _ (u7Wire k) (u7Wire_lt163 k)] at hk
      exact hk.trans (hu k)
    have hPreV : ∀ k : Fin 7, (packCtx163Pre slot2SwappedTo0).fwdBits γ (v7W163 k) = fin65Bits7 _
      k := fun k ↦ by
      have hk := congrFun hfc (v7Wire k)
      rw [castAssign_lt _ (v7Wire k) (v7Wire_lt163 k)] at hk
      exact hk.trans (hv k)
    have hPreW : ∀ k : Fin 7, (packCtx163Pre slot2SwappedTo0).fwdBits γ (w7W163 k) = fin65Bits7 _
      k := fun k ↦ by
      have hk := congrFun hfc (w7Wire k)
      rw [castAssign_lt _ (w7Wire k) (w7Wire_lt163 k)] at hk
      exact hk.trans (hw k)
    have hPreT : (packCtx163Pre slot2SwappedTo0).fwdBits γ wTPack163 = 0 :=
        (TempCtx.fwdBits_outside (packCtx163Pre slot2SwappedTo0) (packCtx163Pre_supp162
        slot2SwappedTo0) γ wTPack163 le_rfl).trans (hγ wTPack163 (by decide))
    have hApp : (packCtx163 slot2SwappedTo0).fwdBits γ = Function.update
        ((packCtx163Pre slot2SwappedTo0).fwdBits γ) wTPack163 ((packCtx163Pre
        slot2SwappedTo0).fwdBits γ wTPack163 + (packCtx163Pre slot2SwappedTo0).fwdBits γ
        (v7W163 5) * (packCtx163Pre slot2SwappedTo0).fwdBits γ (w7W163 6)) :=
        TempCtx.append_fwdBits _ _ γ
    refine ⟨fun k ↦ ?_, fun k ↦ ?_, fun k ↦ ?_, ?_⟩
    · rw [hApp, Function.update_of_ne (u7W163_ne_tPack k), hPreU k]
    · rw [hApp, Function.update_of_ne (v7W163_ne_tPack k), hPreV k]
    · rw [hApp, Function.update_of_ne (w7W163_ne_tPack k), hPreW k]
    · rw [hApp, Function.update_self, hPreT, zero_add, hPreV 5, hPreW 6]
abbrev rHold12 {n mClean : ℕ} (hmClean : 138 ≤ mClean) (rClean : QRegister mClean n) :
    QRegister 12 n := rClean.slice 0 12 (by omega)
abbrev rCleanMid12 {n mClean : ℕ} (hmClean : 138 ≤ mClean) (rClean : QRegister mClean n) :
    QRegister (mClean - 12) n := rClean.slice 12 (mClean - 12) (by omega)
theorem rHold12_disj_orbit16 {n mClean : ℕ} (hmClean : 138 ≤ mClean)
    (rOrbit16 : QRegister 16 n) (rClean : QRegister mClean n)
    (hOW : rOrbit16.DisjointWires rClean) : (rHold12 hmClean rClean).DisjointWires rOrbit16 :=
  QRegister.disjoint_iff.mpr fun i j heq ↦ by
    dsimp only [rHold12] at heq
    rw [QRegister.slice_apply] at heq
    exact hOW.ne j _ heq.symm
def rTarget28 {n mClean : ℕ} (hmClean : 138 ≤ mClean) (rOrbit16 : QRegister 16 n)
    (rClean : QRegister mClean n) (hOW : rOrbit16.DisjointWires rClean) : QRegister 28 n :=
  (rHold12 hmClean rClean).concat rOrbit16 (rHold12_disj_orbit16 hmClean rOrbit16 rClean hOW)
theorem rTarget28_hold {n mClean : ℕ} (hmClean : 138 ≤ mClean) (rOrbit16 : QRegister 16 n)
    (rClean : QRegister mClean n) (hOW : rOrbit16.DisjointWires rClean) (k : Fin 12) :
    rTarget28 hmClean rOrbit16 rClean hOW (Fin.castAdd 16 k) = rHold12 hmClean rClean k :=
    QRegister.concat_apply_left (rHold12 hmClean rClean) rOrbit16
    (rHold12_disj_orbit16 hmClean rOrbit16 rClean hOW) k
theorem rTarget28_orb {n mClean : ℕ} (hmClean : 138 ≤ mClean) (rOrbit16 : QRegister 16 n)
    (rClean : QRegister mClean n) (hOW : rOrbit16.DisjointWires rClean) (j : Fin 16) :
    rTarget28 hmClean rOrbit16 rClean hOW (Fin.natAdd 12 j) = rOrbit16 j :=
    QRegister.concat_apply_right (rHold12 hmClean rClean) rOrbit16
    (rHold12_disj_orbit16 hmClean rOrbit16 rClean hOW) j
def rCombPack163 {n mClean : ℕ} (hmClean : 138 ≤ mClean) (rCore : QRegister posCoreWires n)
    (rPartner18 : QRegister 18 n) (rClean : QRegister mClean n)
    (hCP : rCore.DisjointWires rPartner18) (hCW : rCore.DisjointWires rClean)
    (hPW : rPartner18.DisjointWires rClean) : QRegister 163 n :=
  let rAct43 : QRegister 43 n := (rCore.concat rPartner18 hCP).compose sel43Reg
  let rDummy16 : QRegister 16 n := rClean.slice 12 16 (by omega)
  let rScr104 : QRegister 104 n := rClean.slice 28 104 (by omega)
  have hActClean : (rCore.concat rPartner18 hCP).DisjointWires rClean :=
    pk_disj_concat_left hCP hCW hPW
  have h43Clean : rAct43.DisjointWires rClean :=
    QRegister.disjoint_iff.mpr fun i j heq ↦ hActClean.ne (sel43Reg i) j heq
  have h43D16 : rAct43.DisjointWires rDummy16 := h43Clean.compose_right _
  have h43S104 : rAct43.DisjointWires rScr104 := h43Clean.compose_right _
  have hD16S104 : rDummy16.DisjointWires rScr104 :=
    pk_slice_disjoint rClean (by omega) (by omega) (Or.inl (by omega))
  (rAct43.concat rDummy16 h43D16).concat rScr104 (pk_disj_concat_left h43D16 h43S104 hD16S104)
theorem rCombPack163_lt43 {n mClean : ℕ} (hmClean : 138 ≤ mClean)
    (rCore : QRegister posCoreWires n) (rPartner18 : QRegister 18 n)
    (rClean : QRegister mClean n) (hCP : rCore.DisjointWires rPartner18)
    (hCW : rCore.DisjointWires rClean) (hPW : rPartner18.DisjointWires rClean) (i : Fin 43) :
    rCombPack163 hmClean rCore rPartner18 rClean hCP hCW hPW
    (Fin.castAdd 104 (Fin.castAdd 16 i)) = (rCore.concat rPartner18 hCP) (sel43Reg i) := by
  dsimp only [rCombPack163]
  rw [QRegister.concat_apply_left, QRegister.concat_apply_left]
  rfl
theorem rCombPack163_tailScr104 {n mClean : ℕ} (hmClean : 138 ≤ mClean)
    (rCore : QRegister posCoreWires n) (rPartner18 : QRegister 18 n)
    (rClean : QRegister mClean n)
    (hCP : rCore.DisjointWires rPartner18)
    (hCW : rCore.DisjointWires rClean)
    (hPW : rPartner18.DisjointWires rClean) (j : Fin 104) :
    tailScr (rCombPack163 hmClean rCore rPartner18 rClean hCP hCW hPW) 104 (by decide) j =
      rClean ⟨28 + j.val, by omega⟩ := by
  dsimp only [tailScr, rCombPack163]
  have he : (⟨(163 - 104) + j.val, by omega⟩ : Fin ((43 + 16) + 104)) = Fin.natAdd 59 j :=
    Fin.ext rfl
  change ((_ : QRegister (43 + 16) n).concat _ _) ⟨(163 - 104) + j.val, by omega⟩ = _
  rw [he, QRegister.concat_apply_right, QRegister.slice_apply]
theorem rCombPack163_disj_target28 {n mClean : ℕ} (hmClean : 138 ≤ mClean)
    (rCore : QRegister posCoreWires n) (rPartner18 : QRegister 18 n)
    (rOrbit16 : QRegister 16 n) (rClean : QRegister mClean n)
    (hCP : rCore.DisjointWires rPartner18) (hCO : rCore.DisjointWires rOrbit16)
    (hCW : rCore.DisjointWires rClean) (hPO : rPartner18.DisjointWires rOrbit16)
    (hPW : rPartner18.DisjointWires rClean) (hOW : rOrbit16.DisjointWires rClean) :
    (rCombPack163 hmClean rCore rPartner18 rClean hCP hCW hPW).DisjointWires
    (rTarget28 hmClean rOrbit16 rClean hOW) := by
  have hActClean : (rCore.concat rPartner18 hCP).DisjointWires rClean :=
    pk_disj_concat_left hCP hCW hPW
  have h43Clean : ((rCore.concat rPartner18 hCP).compose sel43Reg).DisjointWires rClean :=
    QRegister.disjoint_iff.mpr fun i j heq ↦ hActClean.ne (sel43Reg i) j heq
  have hActOrb : (rCore.concat rPartner18 hCP).DisjointWires rOrbit16 :=
    pk_disj_concat_left hCP hCO hPO
  have h43Orb : ((rCore.concat rPartner18 hCP).compose sel43Reg).DisjointWires rOrbit16 :=
    QRegister.disjoint_iff.mpr fun i j heq ↦ hActOrb.ne (sel43Reg i) j heq
  have hCombHold : (rCombPack163 hmClean rCore rPartner18 rClean hCP hCW hPW).DisjointWires
      (rHold12 hmClean rClean) := by
    dsimp only [rCombPack163, rHold12]
    exact pk_disj_concat_left _ (pk_disj_concat_left _ (h43Clean.compose_right _)
      (pk_slice_disjoint rClean (by omega) (by omega) (Or.inr (by omega))))
      (pk_slice_disjoint rClean (by omega) (by omega) (Or.inr (by omega)))
  have hCombOrb : (rCombPack163 hmClean rCore rPartner18 rClean hCP hCW hPW).DisjointWires
    rOrbit16 := by
    dsimp only [rCombPack163]
    exact pk_disj_concat_left _ (pk_disj_concat_left _ h43Orb (QRegister.disjoint_iff.mpr fun
      i j heq ↦ hOW.ne j _ heq.symm))
      (QRegister.disjoint_iff.mpr fun i j heq ↦ hOW.ne j _ heq.symm)
  exact (QRegExt.disjointWires_symm (pk_disj_concat_left _ (QRegExt.disjointWires_symm hCombHold)
    (QRegExt.disjointWires_symm hCombOrb)))
/-- `28`-bit combined `(packVWBits12 V W t_pack, U, 0)` vector. -/
def packBits28 (U V W : Fin 7 → ZMod 2) (t_pack : ZMod 2) (k : Fin 28) : ZMod 2 :=
  if hk : k.val < 12 then packVWBits12 V W t_pack ⟨k.val, hk⟩
  else if hu : k.val < 19 then U ⟨k.val - 12, by omega⟩
  else 0
def packCanon28 (c : CanonicalTriple65) : Fin 28 → ZMod 2 := packBits28 (fin65Bits7 c.u)
    (fin65Bits7 c.v) (fin65Bits7 c.w) (fin65Bits7 c.v 5 * fin65Bits7 c.w 6)
theorem packCanon28_hold (c : CanonicalTriple65) (k : Fin 12) :
    packCanon28 c (Fin.castAdd 16 k) = packCanonVW12 c k := by
  dsimp only [packCanon28, packBits28, packCanonVW12]
  have hk : (Fin.castAdd 16 k).val < 12 := k.isLt
  rw [pkDitePos hk]
  rfl
theorem packCanon28_orb (c : CanonicalTriple65) (j : Fin 16) : packCanon28 c (Fin.natAdd 12 j)
    = if hj : j.val < 7 then fin65Bits7 c.u ⟨j.val, hj⟩ else 0 := by
  dsimp only [packCanon28, packBits28]
  have hn12 : ¬ (Fin.natAdd 12 j).val < 12 := by dsimp; omega
  rw [pkDiteNeg hn12]
  by_cases hj : j.val < 7
  · have hu : (Fin.natAdd 12 j).val < 19 := by dsimp; omega
    rw [pkDitePos hu, pkDitePos hj]
    exact congrArg (fin65Bits7 c.u) (Fin.ext (by dsimp; omega))
  · have hnu : ¬ (Fin.natAdd 12 j).val < 19 := by dsimp; omega
    rw [pkDiteNeg hnu, pkDiteNeg hj]
theorem bitsVal_packCanon28_orb (c : CanonicalTriple65) :
    bitsVal (fun j : Fin 16 ↦ packCanon28 c (Fin.natAdd 12 j)) = c.u.val := by
  have hfn : (fun j : Fin (7 + 9) ↦ packCanon28 c (Fin.natAdd 12 j)) = fun j : Fin (7 + 9) ↦
      if hj : j.val < 7 then fin65Bits7 c.u ⟨j.val, hj⟩ else 0 := funext (packCanon28_orb c)
  change bitsVal (fun j : Fin (7 + 9) ↦ packCanon28 c (Fin.natAdd 12 j)) = c.u.val
  rw [hfn]
  exact (bitsVal_padZeroRight (W := 7) (K := 9) (fin65Bits7 c.u)).trans (fin65Bits7_val c.u)
def packSrcIdxs28 (k : Fin 28) : List (Wire 163) :=
  match k.val with
  | 0 => [v7W163 0]
  | 1 => [v7W163 1]
  | 2 => [v7W163 2]
  | 3 => [v7W163 3]
  | 4 => [v7W163 4]
  | 5 => [w7W163 0, wTPack163]
  | 6 => [w7W163 1, v7W163 6]
  | 7 => [w7W163 2]
  | 8 => [w7W163 3]
  | 9 => [w7W163 4]
  | 10 => [v7W163 5, w7W163 6, wTPack163]
  | 11 => [w7W163 5]
  | 12 => [u7W163 0]
  | 13 => [u7W163 1]
  | 14 => [u7W163 2]
  | 15 => [u7W163 3]
  | 16 => [u7W163 4]
  | 17 => [u7W163 5]
  | 18 => [u7W163 6]
  | _ => []
def xorListVal163 {n : ℕ} (rComb : QRegister 163 n) (δ : BitAssignment n) :
    List (Wire 163) → ZMod 2
  | [] => 0
  | w :: ws => δ (rComb w) + xorListVal163 rComb δ ws
theorem xorListVal163_congr {n : ℕ} (rComb : QRegister 163 n) {δ₁ δ₂ : BitAssignment n}
    (h : ∀ u : Wire 163, δ₁ (rComb u) = δ₂ (rComb u)) :
    ∀ ws : List (Wire 163), xorListVal163 rComb δ₁ ws = xorListVal163 rComb δ₂ ws
  | [] => rfl
  | w :: ws => by dsimp only [xorListVal163]; rw [h w, xorListVal163_congr rComb h ws]
theorem xorListVal163_packSrcIdxs28 {n : ℕ} (rComb : QRegister 163 n) (δ : BitAssignment n)
    (k : Fin 28) : xorListVal163 rComb δ (packSrcIdxs28 k) = packBits28
    (fun j ↦ δ (rComb (u7W163 j))) (fun j ↦ δ (rComb (v7W163 j)))
    (fun j ↦ δ (rComb (w7W163 j))) (δ (rComb wTPack163)) k := by
  fin_cases k <;> simp [packSrcIdxs28, xorListVal163, packBits28, packVWBits12, add_zero, add_assoc]
def cnotSingleTgt163 {n : ℕ} (rComb : QRegister 163 n) (t : Fin n)
    (ht : ∀ idx : Wire 163, rComb idx ≠ t) : List (Wire 163) → Circuit n
  | [] => .identity
  | w :: ws => Circuit.CNOT (rComb w) t (ht w) ;;ᶜ cnotSingleTgt163 rComb t ht ws
theorem count_cnotSingleTgt163_toff {n : ℕ} (rComb : QRegister 163 n) (t : Fin n)
    (ht : ∀ idx : Wire 163, rComb idx ≠ t) :
    ∀ ws : List (Wire 163), (cnotSingleTgt163 rComb t ht ws).count PrimitiveGate.TOFF = 0
  | [] => rfl
  | w :: ws => by
      simp [cnotSingleTgt163, Circuit.CNOT, count_cnotSingleTgt163_toff rComb t ht ws]
theorem count_cnotSingleTgt163_t {n : ℕ} (rComb : QRegister 163 n) (t : Fin n)
    (ht : ∀ idx : Wire 163, rComb idx ≠ t) :
    ∀ ws : List (Wire 163), (cnotSingleTgt163 rComb t ht ws).count PrimitiveGate.T = 0
  | [] => rfl
  | w :: ws => by
      simp [cnotSingleTgt163, Circuit.CNOT, count_cnotSingleTgt163_t rComb t ht ws]
theorem eval_cnotSingleTgt163_ket {n : ℕ} (rComb : QRegister 163 n) (t : Fin n)
    (ht : ∀ idx : Wire 163, rComb idx ≠ t) :
    ∀ (ws : List (Wire 163)) (δ : BitAssignment n),
      (cnotSingleTgt163 rComb t ht ws).eval.1.mulVec (ket δ) =
        ket (Function.update δ t (δ t + xorListVal163 rComb δ ws))
  | [], δ => by
      simp [cnotSingleTgt163, xorListVal163, add_zero]
  | w :: ws, δ => by
      dsimp only [cnotSingleTgt163, xorListVal163]
      rw [eval_seq_mulVec, ket_CNOT, eval_cnotSingleTgt163_ket rComb t ht ws]
      let δ₁ := Function.update δ t (δ t + δ (rComb w))
      have hcomb : ∀ u : Wire 163, δ₁ (rComb u) = δ (rComb u) :=
        fun u ↦ Function.update_of_ne (ht u) _ _
      rw [xorListVal163_congr rComb hcomb ws]
      congr 1; funext q
      by_cases hq : q = t
      · subst hq; simp only [Function.update_self, add_assoc]
      · simp only [Function.update_of_ne hq]
def cnotPack28Prefix {n : ℕ} (rComb : QRegister 163 n) (rT28 : QRegister 28 n)
    (hDisj : rComb.DisjointWires rT28) : (m : ℕ) → m ≤ 28 → Circuit n
  | 0, _ => .identity
  | m + 1, hm =>
      cnotPack28Prefix rComb rT28 hDisj m (by omega) ;;ᶜ
        cnotSingleTgt163 rComb (rT28 ⟨m, hm⟩) (fun idx ↦ hDisj.ne idx ⟨m, hm⟩) (packSrcIdxs28 ⟨m,
          hm⟩)
def cPackXor28 {n : ℕ} (rComb : QRegister 163 n) (rT28 : QRegister 28 n)
    (hDisj : rComb.DisjointWires rT28) : Circuit n :=
  cnotPack28Prefix rComb rT28 hDisj 28 le_rfl
theorem count_cPackXor28_toff {n : ℕ} (rComb : QRegister 163 n) (rT28 : QRegister 28 n)
    (hDisj : rComb.DisjointWires rT28) :
    (cPackXor28 rComb rT28 hDisj).count PrimitiveGate.TOFF = 0 := by
  have hgen : ∀ (m : ℕ) (hm : m ≤ 28),
      (cnotPack28Prefix rComb rT28 hDisj m hm).count PrimitiveGate.TOFF = 0 := by
    intro m; induction m with
    | zero => intro _; rfl
    | succ m ih => intro hm; simp [cnotPack28Prefix, ih (by omega), count_cnotSingleTgt163_toff]
  exact hgen 28 le_rfl
theorem count_cPackXor28_t {n : ℕ} (rComb : QRegister 163 n) (rT28 : QRegister 28 n)
    (hDisj : rComb.DisjointWires rT28) :
    (cPackXor28 rComb rT28 hDisj).count PrimitiveGate.T = 0 := by
  have hgen : ∀ (m : ℕ) (hm : m ≤ 28),
      (cnotPack28Prefix rComb rT28 hDisj m hm).count PrimitiveGate.T = 0 := by
    intro m; induction m with
    | zero => intro _; rfl
    | succ m ih => intro hm; simp [cnotPack28Prefix, ih (by omega), count_cnotSingleTgt163_t]
  exact hgen 28 le_rfl
noncomputable def packStep28_0 {n : ℕ} (rComb : QRegister 163 n) (rT28 : QRegister 28 n)
    (δ : BitAssignment n) : BitAssignment n := fun w ↦ if hk : ∃ k : Fin 28, w = rT28 k then δ
    w + packBits28 (fun j ↦ δ (rComb (u7W163 j))) (fun j ↦ δ (rComb (v7W163 j)))
    (fun j ↦ δ (rComb (w7W163 j))) (δ (rComb wTPack163)) hk.choose else δ w
theorem packStep28_0_fix_comb {n : ℕ} (rComb : QRegister 163 n) (rT28 : QRegister 28 n)
    (hDisj : rComb.DisjointWires rT28) (δ : BitAssignment n) (idx : Wire 163) : packStep28_0
    rComb rT28 δ (rComb idx) = δ (rComb idx) := pkDiteNeg fun ⟨k, hk⟩ ↦ hDisj.ne idx k hk
theorem eval_cPackXor28_ket {n : ℕ} (rComb : QRegister 163 n) (rT28 : QRegister 28 n)
    (hDisj : rComb.DisjointWires rT28) (δ : BitAssignment n) :
    (cPackXor28 rComb rT28 hDisj).eval.1.mulVec (ket δ) = ket (packStep28_0 rComb rT28 δ) := by
  let stepPfx : ℕ → BitAssignment n := fun m w ↦ if hk : ∃ k : Fin 28, k.val < m ∧ w = rT28 k
      then δ w + xorListVal163 rComb δ (packSrcIdxs28 hk.choose) else δ w
  have hgen : ∀ (m : ℕ) (hm : m ≤ 28),
      (cnotPack28Prefix rComb rT28 hDisj m hm).eval.1.mulVec (ket δ) = ket (stepPfx m) := by
    intro m; induction m with
    | zero =>
        intro _
        have h0 : stepPfx 0 = δ := by
          funext w; dsimp only [stepPfx]
          exact pkDiteNeg fun ⟨k, hlt, _⟩ ↦ Nat.not_lt_zero k.val hlt
        simp [cnotPack28Prefix, h0]
    | succ m ih =>
        intro hm
        dsimp only [cnotPack28Prefix]
        rw [eval_seq_mulVec, ih (by omega), eval_cnotSingleTgt163_ket]
        have hcomb : ∀ u : Wire 163, stepPfx m (rComb u) = δ (rComb u) :=
          fun u ↦ pkDiteNeg fun ⟨k, _, hk⟩ ↦ hDisj.ne u k hk
        rw [xorListVal163_congr rComb hcomb (packSrcIdxs28 ⟨m, hm⟩)]
        have hnot_m : ¬ ∃ k : Fin 28, k.val < m ∧ rT28 ⟨m, hm⟩ = rT28 k := by
          rintro ⟨k, hlt, heq⟩
          have hv := congrArg Fin.val (rT28.wires.injective heq)
          dsimp at hv; omega
        have hbase_m : stepPfx m (rT28 ⟨m, hm⟩) = δ (rT28 ⟨m, hm⟩) := pkDiteNeg hnot_m
        congr 1; funext w
        by_cases hw : w = rT28 ⟨m, hm⟩
        · subst hw
          have hex : ∃ k : Fin 28, k.val < m + 1 ∧ rT28 ⟨m, hm⟩ = rT28 k :=
            ⟨⟨m, hm⟩, Nat.lt_succ_self m, rfl⟩
          have hch : hex.choose = ⟨m, hm⟩ := (rT28.wires.injective hex.choose_spec.2).symm
          rw [Function.update_self, hbase_m]
          dsimp only [stepPfx]
          rw [pkDitePos hex, hch]
        · rw [Function.update_of_ne hw]
          by_cases hk : ∃ k : Fin 28, k.val < m ∧ w = rT28 k
          · have hk1 : ∃ k : Fin 28, k.val < m + 1 ∧ w = rT28 k :=
              ⟨hk.choose, Nat.lt_succ_of_lt hk.choose_spec.1, hk.choose_spec.2⟩
            have hch : hk1.choose = hk.choose :=
              rT28.wires.injective (hk1.choose_spec.2.symm.trans hk.choose_spec.2)
            dsimp only [stepPfx]
            rw [pkDitePos hk, pkDitePos hk1, hch]
          · have hnk1 : ¬ ∃ k : Fin 28, k.val < m + 1 ∧ w = rT28 k := by
              rintro ⟨k, hlt, heq⟩
              by_cases hkm : k.val = m
              · exact hw (heq.trans (congrArg rT28 (Fin.ext hkm)))
              · exact hk ⟨k, by omega, heq⟩
            dsimp only [stepPfx]
            rw [pkDiteNeg hk, pkDiteNeg hnk1]
  dsimp only [cPackXor28]
  rw [hgen 28 le_rfl]
  congr 1; funext w
  by_cases hk : ∃ k : Fin 28, w = rT28 k
  · have hk28 : ∃ k : Fin 28, k.val < 28 ∧ w = rT28 k := ⟨hk.choose, hk.choose.isLt, hk.choose_spec⟩
    have hch : hk28.choose = hk.choose :=
      rT28.wires.injective (hk28.choose_spec.2.symm.trans hk.choose_spec)
    dsimp only [stepPfx, packStep28_0]
    rw [pkDitePos hk28, pkDitePos hk, hch, xorListVal163_packSrcIdxs28]
  · have hnk28 : ¬ ∃ k : Fin 28, k.val < 28 ∧ w = rT28 k := fun ⟨k, _, heq⟩ ↦ hk ⟨k, heq⟩
    dsimp only [stepPfx, packStep28_0]
    rw [pkDiteNeg hnk28, pkDiteNeg hk]
/-- `384 T`, `0` `.TOFF` pack/unpack involution XORing `packCanon28` into `rHold12 ++ rOrbit16`. -/
def dPack12 {Var : Type} {n mClean : ℕ} (hmClean : 138 ≤ mClean) (slot2SwappedTo0 : Bool)
    (v : Var) (rCore : QRegister posCoreWires n) (rPartner18 : QRegister 18 n)
    (rOrbit16 : QRegister 16 n) (rClean : QRegister mClean n)
    (hCP : rCore.DisjointWires rPartner18) (hCO : rCore.DisjointWires rOrbit16)
    (hCW : rCore.DisjointWires rClean) (hPO : rPartner18.DisjointWires rOrbit16)
    (hPW : rPartner18.DisjointWires rClean) (hOW : rOrbit16.DisjointWires rClean) :
    DynamicCircuit Var n :=
  let rComb := rCombPack163 hmClean rCore rPartner18 rClean hCP hCW hPW
  let rT28 := rTarget28 hmClean rOrbit16 rClean hOW
  have hDisj := rCombPack163_disj_target28 hmClean rCore rPartner18 rOrbit16 rClean
    hCP hCO hCW hPO hPW hOW
  toDynWithDyn v rComb (.circuit (cPackXor28 rComb rT28 hDisj)) (packCtx163 slot2SwappedTo0)
theorem count_dPack12_toff {Var : Type} {n mClean : ℕ} (hmClean : 138 ≤ mClean)
    (slot2SwappedTo0 : Bool) (v : Var) (rCore : QRegister posCoreWires n)
    (rPartner18 : QRegister 18 n) (rOrbit16 : QRegister 16 n) (rClean : QRegister mClean n)
    (hCP : rCore.DisjointWires rPartner18) (hCO : rCore.DisjointWires rOrbit16)
    (hCW : rCore.DisjointWires rClean) (hPO : rPartner18.DisjointWires rOrbit16)
    (hPW : rPartner18.DisjointWires rClean) (hOW : rOrbit16.DisjointWires rClean) :
    (dPack12 hmClean slot2SwappedTo0 v rCore rPartner18 rOrbit16 rClean hCP hCO hCW hPO
    hPW hOW).count PrimitiveGate.TOFF = 0 := by
  dsimp only [dPack12]
  refine toDynWithDyn_count_toff v _ _ ?_ _
  simp [DynamicCircuit.count, count_cPackXor28_toff]
theorem count_dPack12_t {Var : Type} {n mClean : ℕ} (hmClean : 138 ≤ mClean)
    (slot2SwappedTo0 : Bool) (v : Var) (rCore : QRegister posCoreWires n)
    (rPartner18 : QRegister 18 n) (rOrbit16 : QRegister 16 n) (rClean : QRegister mClean n)
    (hCP : rCore.DisjointWires rPartner18) (hCO : rCore.DisjointWires rOrbit16)
    (hCW : rCore.DisjointWires rClean) (hPO : rPartner18.DisjointWires rOrbit16)
    (hPW : rPartner18.DisjointWires rClean) (hOW : rOrbit16.DisjointWires rClean) :
    (dPack12 hmClean slot2SwappedTo0 v rCore rPartner18 rOrbit16 rClean hCP hCO hCW hPO
    hPW hOW).count PrimitiveGate.T = 384 := by
  dsimp only [dPack12]
  rw [toDynWithDyn_count_t, packCtx163_countTempAnd]
  simp only [DynamicCircuit.count, count_cPackXor28_t]
theorem rawOrbitCoord128_rCombPack163 {n mClean : ℕ} (slot2SwappedTo0 : Bool)
    (hmClean : 138 ≤ mClean)
    (rCore : QRegister posCoreWires n) (rPartner18 : QRegister 18 n)
    (rClean : QRegister mClean n)
    (hCP : rCore.DisjointWires rPartner18)
    (hCW : rCore.DisjointWires rClean)
    (hPW : rPartner18.DisjointWires rClean) (β : BitAssignment n) :
    let rComb := rCombPack163 hmClean rCore rPartner18 rClean hCP hCW hPW
    let γ303 : BitAssignment 303 := castAssign (M := 303) (fun idx : Wire 163 ↦ β (rComb idx))
    rawOrbitCoord128 slot2SwappedTo0 (coreViewOf303 γ303) (partnerViewOf303 γ303) =
      rawOrbitCoord128 slot2SwappedTo0
        (fun i ↦ β (rCore i))
        (fun i ↦ β (rPartner18 i)) := by
  intro rComb γ303
  obtain ⟨hs0_r, hb0_r, hb1_r, hy0_r, hyp_r⟩ := coreViewOf303_reads γ303
  have hCombLt43 := rCombPack163_lt43 hmClean rCore rPartner18 rClean hCP hCW hPW
  funext ax
  have _hax := ax.isLt
  have hs0_eq : coreViewOf303 γ303 (wSlot0Core (QRegExt.ofFin posCoreWires)) =
      β (rCore (wSlot0Core (QRegExt.ofFin posCoreWires))) := by
    rw [hs0_r]
    dsimp only [γ303]
    rw [castAssign_lt _ wS0 (by decide)]
    have hw : (⟨wS0.val, by decide⟩ : Wire 163) =
        Fin.castAdd 104 (Fin.castAdd 16 ⟨0, by decide⟩) := rfl
    have hsel : sel43Reg ⟨0, by decide⟩ =
        Fin.castAdd 18 (wSlot0Core (QRegExt.ofFin posCoreWires)) :=
      Fin.ext (congrArg (Fin.val : Fin ((posCoreWires + 18) + 16) → ℕ) sel59Reg_s0)
    rw [hw, hCombLt43, hsel, QRegister.concat_apply_left]
  have hb0_eq : coreViewOf303 γ303 (rCosetB0 (QRegExt.ofFin posCoreWires) ax) =
      β (rCore (rCosetB0 (QRegExt.ofFin posCoreWires) ax)) := by
    rw [hb0_r ax]
    dsimp only [γ303]
    have hlt : (wB0 ax).val < 163 := by dsimp [wB0]; omega
    rw [castAssign_lt _ (wB0 ax) hlt]
    have hw : (⟨(wB0 ax).val, hlt⟩ : Wire 163) =
        Fin.castAdd 104 (Fin.castAdd 16 ⟨1 + ax.val, by omega⟩) := rfl
    have hsel : sel43Reg ⟨1 + ax.val, by omega⟩ =
        Fin.castAdd 18 (rCosetB0 (QRegExt.ofFin posCoreWires) ax) :=
      Fin.ext (congrArg (Fin.val : Fin ((posCoreWires + 18) + 16) → ℕ) (sel59Reg_b0 ax))
    rw [hw, hCombLt43, hsel, QRegister.concat_apply_left]
  have hb1_eq : coreViewOf303 γ303 (rCosetB1 (QRegExt.ofFin posCoreWires) ax) =
      β (rCore (rCosetB1 (QRegExt.ofFin posCoreWires) ax)) := by
    rw [hb1_r ax]
    dsimp only [γ303]
    have hlt : (wB1 ax).val < 163 := by dsimp [wB1]; omega
    rw [castAssign_lt _ (wB1 ax) hlt]
    have hw : (⟨(wB1 ax).val, hlt⟩ : Wire 163) =
        Fin.castAdd 104 (Fin.castAdd 16 ⟨4 + ax.val, by omega⟩) := rfl
    have hsel : sel43Reg ⟨4 + ax.val, by omega⟩ =
        Fin.castAdd 18 (rCosetB1 (QRegExt.ofFin posCoreWires) ax) :=
      Fin.ext (congrArg (Fin.val : Fin ((posCoreWires + 18) + 16) → ℕ) (sel59Reg_b1 ax))
    rw [hw, hCombLt43, hsel, QRegister.concat_apply_left]
  have hy0_eq : regVal (axisBitRev6 (rElecSlot (QRegExt.ofFin posCoreWires) 0) ax) (coreViewOf303
    γ303) =
      regVal (axisBitRev6 (rElecSlot (QRegExt.ofFin posCoreWires) 0) ax) (fun i ↦ β (rCore i)) := by
    dsimp only [regVal]; congr 1; funext j
    have _hj := j.isLt
    rw [hy0_r ax j]
    dsimp only [γ303]
    have hlt : (wY0 ax j).val < 163 := by dsimp [wY0]; omega
    rw [castAssign_lt _ (wY0 ax j) hlt]
    have hw : (⟨(wY0 ax j).val, hlt⟩ : Wire 163) =
        Fin.castAdd 104 (Fin.castAdd 16 ⟨7 + 6 * ax.val + j.val, by omega⟩) := rfl
    have hsel : sel43Reg ⟨7 + 6 * ax.val + j.val, by omega⟩ =
        Fin.castAdd 18 (axisBitRev6 (rElecSlot (QRegExt.ofFin posCoreWires) 0) ax j) :=
      Fin.ext (congrArg (Fin.val : Fin ((posCoreWires + 18) + 16) → ℕ) (sel59Reg_y0 ax j))
    rw [hw, hCombLt43, hsel, QRegister.concat_apply_left]
  have hyp_eq : regVal (axisBitRev6 (QRegExt.ofFin 18) ax) (partnerViewOf303 γ303) =
      regVal (axisBitRev6 (QRegExt.ofFin 18) ax) (fun i ↦ β (rPartner18 i)) := by
    dsimp only [regVal]; congr 1; funext j
    have _hj := j.isLt
    rw [hyp_r ax j]
    dsimp only [γ303]
    have hlt : (wYP ax j).val < 163 := by dsimp [wYP]; omega
    rw [castAssign_lt _ (wYP ax j) hlt]
    have hw : (⟨(wYP ax j).val, hlt⟩ : Wire 163) =
        Fin.castAdd 104 (Fin.castAdd 16 ⟨25 + 6 * ax.val + j.val, by omega⟩) := rfl
    have hsel : sel43Reg ⟨25 + 6 * ax.val + j.val, by omega⟩ =
        Fin.natAdd posCoreWires (axisBitRev6 (QRegExt.ofFin 18) ax j) :=
      Fin.ext (congrArg (Fin.val : Fin ((posCoreWires + 18) + 16) → ℕ) (sel59Reg_yp ax j))
    rw [hw, hCombLt43, hsel, QRegister.concat_apply_right]
  dsimp only [rawOrbitCoord128, PosSlots24PartnerMux288.rawOrbitCoord128]
  rw [hs0_eq]
  by_cases hc : Bool.not (β (rCore (wSlot0Core (QRegExt.ofFin posCoreWires))) == 1)
  · rw [pkItePos hc, pkItePos hc]; apply Fin.ext; dsimp only; rw [hy0_eq, hyp_eq, hb1_eq]
  · rw [pkIteNeg hc, pkIteNeg hc]; apply Fin.ext; dsimp only; rw [hy0_eq, hyp_eq, hb0_eq, hb1_eq]
def S_mid12 {n mClean : ℕ} (hmClean : 138 ≤ mClean) (rClean : QRegister mClean n)
    (β : BitAssignment n) : Prop :=
  ∀ j : Fin (mClean - 12), β (rCleanMid12 hmClean rClean j) = 0
noncomputable def packStep28 {n : ℕ} (slot2SwappedTo0 : Bool)
    (rCore : QRegister posCoreWires n) (rPartner18 : QRegister 18 n) (rT28 : QRegister 28 n)
    (β : BitAssignment n) : BitAssignment n := fun w ↦ if hk : ∃ k : Fin 28, w = rT28 k then β
    w + packCanon28 (canonTriple128 (rawOrbitCoord128 slot2SwappedTo0 (fun i ↦ β (rCore i))
    (fun i ↦ β (rPartner18 i)))) hk.choose else β w
theorem packStep28_apply_target {n : ℕ} (slot2SwappedTo0 : Bool)
    (rCore : QRegister posCoreWires n) (rPartner18 : QRegister 18 n) (rT28 : QRegister 28 n)
    (β : BitAssignment n) (k : Fin 28) : packStep28 slot2SwappedTo0 rCore rPartner18 rT28 β
    (rT28 k) = β (rT28 k) + packCanon28 (canonTriple128 (rawOrbitCoord128 slot2SwappedTo0 (fun
    i ↦ β (rCore i)) (fun i ↦ β (rPartner18 i)))) k := by
  have hk : ∃ j : Fin 28, rT28 k = rT28 j := ⟨k, rfl⟩
  have hch : hk.choose = k := (rT28.wires.injective hk.choose_spec).symm
  dsimp only [packStep28]
  rw [pkDitePos hk, hch]
theorem packStep28_apply_of_not_target {n : ℕ} (slot2SwappedTo0 : Bool)
    (rCore : QRegister posCoreWires n) (rPartner18 : QRegister 18 n) (rT28 : QRegister 28 n)
    (β : BitAssignment n) {w : Fin n} (hw : ∀ k : Fin 28, w ≠ rT28 k) : packStep28
    slot2SwappedTo0 rCore rPartner18 rT28 β w = β w := pkDiteNeg fun ⟨k, hk⟩ ↦ hw k hk
theorem packStep28_invol {n : ℕ} (slot2SwappedTo0 : Bool) (rCore : QRegister posCoreWires n)
    (rPartner18 : QRegister 18 n) (rT28 : QRegister 28 n) (hCT : rCore.DisjointWires rT28)
    (hPT : rPartner18.DisjointWires rT28) (β : BitAssignment n) : packStep28 slot2SwappedTo0
    rCore rPartner18 rT28 (packStep28 slot2SwappedTo0 rCore rPartner18 rT28 β) = β := by
  let β₁ := packStep28 slot2SwappedTo0 rCore rPartner18 rT28 β
  have hc_eq : (fun i ↦ β₁ (rCore i)) = fun i ↦ β (rCore i) :=
    funext fun i ↦ packStep28_apply_of_not_target _ _ _ _ _ (fun k ↦ hCT.ne i k)
  have hp_eq : (fun i ↦ β₁ (rPartner18 i)) = fun i ↦ β (rPartner18 i) :=
    funext fun i ↦ packStep28_apply_of_not_target _ _ _ _ _ (fun k ↦ hPT.ne i k)
  funext w
  by_cases hk : ∃ k : Fin 28, w = rT28 k
  · obtain ⟨k, rfl⟩ := hk
    rw [packStep28_apply_target, hc_eq, hp_eq, packStep28_apply_target]
    exact CharTwo.add_cancel_right _ _
  · have hnw : ∀ k : Fin 28, w ≠ rT28 k := fun k h ↦ hk ⟨k, h⟩
    rw [packStep28_apply_of_not_target _ _ _ _ _ hnw, packStep28_apply_of_not_target _ _ _ _ _ hnw]
theorem rCleanMid12_disj_target28 {n mClean : ℕ} (hmClean : 138 ≤ mClean)
    (rOrbit16 : QRegister 16 n) (rClean : QRegister mClean n)
    (hOW : rOrbit16.DisjointWires rClean) :
    (rCleanMid12 hmClean rClean).DisjointWires (rTarget28 hmClean rOrbit16 rClean hOW) := by
  have hMH : (rCleanMid12 hmClean rClean).DisjointWires (rHold12 hmClean rClean) :=
    pk_slice_disjoint rClean (by omega) (by omega) (Or.inr (by omega))
  have hMO : (rCleanMid12 hmClean rClean).DisjointWires rOrbit16 :=
    QRegister.disjoint_iff.mpr fun i j heq ↦ hOW.ne j _ heq.symm
  exact (QRegExt.disjointWires_symm (pk_disj_concat_left _ (QRegExt.disjointWires_symm hMH)
    (QRegExt.disjointWires_symm hMO)))
theorem packStep28_preserves_mid12 {n mClean : ℕ} (hmClean : 138 ≤ mClean)
    (slot2SwappedTo0 : Bool)
    (rCore : QRegister posCoreWires n) (rPartner18 : QRegister 18 n)
    (rOrbit16 : QRegister 16 n) (rClean : QRegister mClean n)
    (hOW : rOrbit16.DisjointWires rClean)
    {β : BitAssignment n} (hβ : S_mid12 hmClean rClean β) :
    S_mid12 hmClean rClean
      (packStep28 slot2SwappedTo0 rCore rPartner18 (rTarget28 hmClean rOrbit16 rClean hOW) β) :=
        fun j ↦ by
  have hdisj := rCleanMid12_disj_target28 hmClean rOrbit16 rClean hOW
  rw [packStep28_apply_of_not_target _ _ _ _ _ (fun k ↦ hdisj.ne j k)]
  exact hβ j
theorem dPack12_constClean {Var : Type} [Fintype Var] [DecidableEq Var] {n mClean : ℕ}
    (hmClean : 138 ≤ mClean) (slot2SwappedTo0 : Bool) (v : Var)
    (rCore : QRegister posCoreWires n) (rPartner18 : QRegister 18 n)
    (rOrbit16 : QRegister 16 n) (rClean : QRegister mClean n)
    (hCP : rCore.DisjointWires rPartner18) (hCO : rCore.DisjointWires rOrbit16)
    (hCW : rCore.DisjointWires rClean) (hPO : rPartner18.DisjointWires rOrbit16)
    (hPW : rPartner18.DisjointWires rClean) (hOW : rOrbit16.DisjointWires rClean) : ∃ U_pack :
    Unitary (2 ^ n), p2t_RealizesConstCleanUnitary (p2t_ketPredProj (S_mid12 hmClean rClean))
    (dPack12 hmClean slot2SwappedTo0 v rCore rPartner18 rOrbit16 rClean hCP hCO hCW hPO
    hPW hOW) U_pack ∧ ∀ β : BitAssignment n, S_mid12 hmClean rClean β → U_pack.1.mulVec
    (ket β) = ket (packStep28 slot2SwappedTo0 rCore rPartner18 (rTarget28 hmClean rOrbit16
    rClean hOW) β) := by
  let rComb := rCombPack163 hmClean rCore rPartner18 rClean hCP hCW hPW
  let rT28 := rTarget28 hmClean rOrbit16 rClean hOW
  have hDisj := rCombPack163_disj_target28 hmClean rCore rPartner18 rOrbit16 rClean
    hCP hCO hCW hPO hPW hOW
  let cXor := cPackXor28 rComb rT28 hDisj
  obtain ⟨hv163, hbits163, hfwd163⟩ := packCtx163_spec slot2SwappedTo0
  obtain ⟨U_pack, hReal104, hKet104⟩ := constClean_toDynWithDyn_perm v rComb 0
      (Nat.zero_le 163) (.z wZero163) (fun _ _ ↦ Nat.zero_le _) (fun _ ↦ rfl) (.circuit cXor)
      cXor.eval (p2t_RealizesConstCleanUnitary_circuit _ cXor) (packStep28_0 rComb rT28)
      (packStep28_0_fix_comb rComb rT28 hDisj) (eval_cPackXor28_ket rComb rT28 hDisj)
      (packCtx163 slot2SwappedTo0) 104 (by decide) hv163
  have hSubProj : projZeroAll 104 (tailScr rComb 104 (by decide)) *
      p2t_ketPredProj (S_mid12 hmClean rClean) = p2t_ketPredProj (S_mid12 hmClean rClean) :=
    pk_projZeroAll_mul_ketPredProj _ fun β hs j ↦ by
      rw [rCombPack163_tailScr104 hmClean rCore rPartner18 rClean hCP hCW hPW j]
      have hj : (⟨28 + j.val, by omega⟩ : Fin mClean) =
          ⟨12 + (16 + j.val), by omega⟩ := by ext; dsimp; omega
      rw [hj]
      exact hs ⟨16 + j.val, by omega⟩
  refine ⟨U_pack, p2t_RealizesConstCleanUnitary_mono_proj (projZeroAll_conjTranspose 104 _)
    (p2t_ketPredProj_conjTranspose _) hSubProj hReal104, fun β hs ↦ ?_⟩
  rw [hKet104 β]
  let γ : BitAssignment 163 := fun idx ↦ β (rComb idx)
  have hcl163 : cleanRem 163 104 γ := fun u hu ↦ by
    have hu_eq : u = ⟨(163 - 104) + (u.val - 59), by omega⟩ := by ext; dsimp; omega
    dsimp only [γ]
    rw [hu_eq]
    change β (tailScr rComb 104 (by decide) ⟨u.val - 59, by omega⟩) = 0
    rw [rCombPack163_tailScr104 hmClean rCore rPartner18 rClean hCP hCW hPW]
    have hj : (⟨28 + (u.val - 59), by omega⟩ : Fin mClean) =
        ⟨12 + (16 + (u.val - 59)), by omega⟩ := by ext; dsimp; omega
    rw [hj]
    exact hs ⟨16 + (u.val - 59), by omega⟩
  have hev : ((packCtx163 slot2SwappedTo0).plug (.z wZero163)).evalBits γ = γ :=
    hbits163 γ hcl163
  obtain ⟨hu7, hv7, hw7, htp⟩ := hfwd163 γ hcl163
  have hcoord := rawOrbitCoord128_rCombPack163 slot2SwappedTo0 hmClean
    rCore rPartner18 rClean hCP hCW hPW β
  let δ := writeRegProg β rComb ((packCtx163 slot2SwappedTo0).fwdBits γ)
  have hδ_u : (fun j ↦ δ (rComb (u7W163 j))) = fin65Bits7 (canonTriple128 (rawOrbitCoord128
      slot2SwappedTo0 (fun i ↦ β (rCore i)) (fun i ↦ β (rPartner18 i)))).u := by
    funext j; dsimp only [δ]
    rw [writeRegProg_apply_reg, hu7 j, hcoord]
  have hδ_v : (fun j ↦ δ (rComb (v7W163 j))) = fin65Bits7 (canonTriple128 (rawOrbitCoord128
      slot2SwappedTo0 (fun i ↦ β (rCore i)) (fun i ↦ β (rPartner18 i)))).v := by
    funext j; dsimp only [δ]
    rw [writeRegProg_apply_reg, hv7 j, hcoord]
  have hδ_w : (fun j ↦ δ (rComb (w7W163 j))) = fin65Bits7 (canonTriple128 (rawOrbitCoord128
      slot2SwappedTo0 (fun i ↦ β (rCore i)) (fun i ↦ β (rPartner18 i)))).w := by
    funext j; dsimp only [δ]
    rw [writeRegProg_apply_reg, hw7 j, hcoord]
  have hδ_tp : δ (rComb wTPack163) = fin65Bits7 (canonTriple128 (rawOrbitCoord128
      slot2SwappedTo0 (fun i ↦ β (rCore i)) (fun i ↦ β (rPartner18 i)))).v 5 * fin65Bits7
      (canonTriple128 (rawOrbitCoord128 slot2SwappedTo0 (fun i ↦ β (rCore i)) (fun i ↦ β
      (rPartner18 i)))).w 6 := by
    dsimp only [δ]
    rw [writeRegProg_apply_reg, htp, hcoord]
  rw [hev]
  congr 1; funext w
  by_cases hm : w ∈ Set.range rComb.wires
  · obtain ⟨idx, rfl⟩ := hm
    rw [writeRegProg_apply_reg,
      packStep28_apply_of_not_target _ _ _ _ _ (fun k ↦ hDisj.ne idx k)]
  · rw [writeRegProg_apply_of_not_mem _ _ _ _ hm]
    have hδw : δ w = β w := writeRegProg_apply_of_not_mem _ _ _ _ hm
    dsimp only [δ, γ] at hδw hδ_u hδ_v hδ_w hδ_tp
    dsimp only [packStep28_0, packStep28, packCanon28]
    by_cases hk : ∃ k : Fin 28, w = rT28 k
    · rw [pkDitePos hk, pkDitePos hk, hδw, hδ_u, hδ_v, hδ_w, hδ_tp]
    · rw [pkDiteNeg hk, pkDiteNeg hk, hδw]
attribute [local irreducible] packCtx163 dPack12
/-- In-place modular adder `acc ← (src + acc + cin) mod 2^(W+1)` using `W` clean carry wires `[cur
.. cur+W)`. -/
def progAddMod2Pow {M : ℕ} :
    (W : ℕ) → (cur : ℕ) → (hcur : cur + W ≤ M) →
    (src acc : Fin (W + 1) → Wire M) → (cin : Wire M) →
    (hsa : ∀ i j, src i ≠ acc j) →
    (hsc : ∀ i, src i ≠ cin) →
    (hac : ∀ i, acc i ≠ cin) →
    (hs_lt : ∀ i, (src i).val < cur) →
    (ha_lt : ∀ i, (acc i).val < cur) →
    (hc_lt : cin.val < cur) →
    TempPhaseProg M
  | 0, _, _, src, acc, cin, hsa, _, hac, _, _, _ =>
      .cliff (.seq (.cnot (src 0) (acc 0) (hsa 0 0)) (.cnot cin (acc 0) (hac 0).symm))
  | W + 1, cur, hcur, src, acc, cin, hsa, hsc, hac, hs_lt, ha_lt, hc_lt =>
      let cout : Wire M := ⟨cur, by omega⟩
      let cPre : CliffProg M :=
        .seq (.cnot cin (src 0) (hsc 0).symm) (.cnot cin (acc 0) (hac 0).symm)
      let cPost : CliffProg M :=
        .seq (.cnot cin (src 0) (hsc 0).symm) (.cnot (src 0) (acc 0) (hsa 0 0))
      let inner : TempPhaseProg M :=
        .seq (.cliff (.cnot cin cout (wire_ne_of_lt hc_lt)))
          (.seq
            (progAddMod2Pow W (cur + 1) (by omega)
              (fun j ↦ src j.succ) (fun j ↦ acc j.succ) cout
              (fun i j ↦ hsa i.succ j.succ)
              (fun i ↦ wire_ne_of_lt (hs_lt i.succ))
              (fun i ↦ wire_ne_of_lt (ha_lt i.succ))
              (fun i ↦ lt_trans (hs_lt i.succ) (by omega))
              (fun i ↦ lt_trans (ha_lt i.succ) (by omega))
              (by dsimp [cout]; omega))
            (.cliff (.cnot cin cout (wire_ne_of_lt hc_lt))))
      .seq (.cliff cPre)
        (.seq
          (.tempAnd (src 0) (acc 0) cout (hsa 0 0)
            (wire_ne_of_lt (hs_lt 0)) (wire_ne_of_lt (ha_lt 0)) inner)
          (.cliff cPost))
@[simp] theorem progAddMod2Pow_countTempAnd {M : ℕ} :
    ∀ (W cur : ℕ) (hcur : cur + W ≤ M)
      (src acc : Fin (W + 1) → Wire M) (cin : Wire M)
      (hsa : ∀ i j, src i ≠ acc j) (hsc : ∀ i, src i ≠ cin) (hac : ∀ i, acc i ≠ cin)
      (hs_lt : ∀ i, (src i).val < cur) (ha_lt : ∀ i, (acc i).val < cur) (hc_lt : cin.val < cur),
      (progAddMod2Pow W cur hcur src acc cin hsa hsc hac hs_lt ha_lt hc_lt).countTempAnd = W
  | 0, _, _, _, _, _, _, _, _, _, _, _ => rfl
  | W + 1, cur, hcur, src, acc, cin, hsa, hsc, hac, hs_lt, ha_lt, hc_lt => by
      simp only [progAddMod2Pow, TempPhaseProg.countTempAnd,
        progAddMod2Pow_countTempAnd W (cur + 1)]
      omega
@[simp] theorem progAddMod2Pow_evalSign {M : ℕ} :
    ∀ (W cur : ℕ) (hcur : cur + W ≤ M)
      (src acc : Fin (W + 1) → Wire M) (cin : Wire M)
      (hsa : ∀ i j, src i ≠ acc j) (hsc : ∀ i, src i ≠ cin) (hac : ∀ i, acc i ≠ cin)
      (hs_lt : ∀ i, (src i).val < cur) (ha_lt : ∀ i, (acc i).val < cur) (hc_lt : cin.val < cur)
      (γ : BitAssignment M),
      (progAddMod2Pow W cur hcur src acc cin hsa hsc hac hs_lt ha_lt hc_lt).evalSign γ = 0
  | 0, _, _, _, _, _, _, _, _, _, _, _, _ => rfl
  | W + 1, cur, hcur, src, acc, cin, hsa, hsc, hac, hs_lt, ha_lt, hc_lt, γ => by
      simp [progAddMod2Pow, TempPhaseProg.evalSign, progAddMod2Pow_evalSign W (cur + 1)]
theorem progAddMod2Pow_evalBits_other {M : ℕ} :
    ∀ (W cur : ℕ) (hcur : cur + W ≤ M)
      (src acc : Fin (W + 1) → Wire M) (cin : Wire M)
      (hsa : ∀ i j, src i ≠ acc j) (hsc : ∀ i, src i ≠ cin) (hac : ∀ i, acc i ≠ cin)
      (_hinjAcc : Function.Injective acc)
      (hs_lt : ∀ i, (src i).val < cur) (ha_lt : ∀ i, (acc i).val < cur) (hc_lt : cin.val < cur)
      (γ : BitAssignment M) (w : Wire M),
      (∀ j : Fin (W + 1), w ≠ acc j) →
      (progAddMod2Pow W cur hcur src acc cin hsa hsc hac hs_lt ha_lt hc_lt).evalBits γ w = γ w
  | 0, _, _, src, acc, cin, hsa, _, hac, _, _, _, _, γ, w, hne => by
      dsimp only [progAddMod2Pow, TempPhaseProg.evalBits, CliffProg.eval]
      rw [Function.update_of_ne (hne 0), Function.update_of_ne (hne 0)]
  | W + 1, cur, hcur, src, acc, cin, hsa, hsc, hac, hinjAcc, hs_lt, ha_lt, hc_lt, γ, w, hne => by
      let cout : Wire M := ⟨cur, by omega⟩
      let pRec := progAddMod2Pow W (cur + 1) (by omega)
        (fun j ↦ src j.succ) (fun j ↦ acc j.succ) cout
        (fun i j ↦ hsa i.succ j.succ)
        (fun i ↦ wire_ne_of_lt (hs_lt i.succ))
        (fun i ↦ wire_ne_of_lt (ha_lt i.succ))
        (fun i ↦ lt_trans (hs_lt i.succ) (by omega))
        (fun i ↦ lt_trans (ha_lt i.succ) (by omega))
        (by dsimp [cout]; omega)
      have ih : ∀ (δ : BitAssignment M) (u : Wire M), (∀ j : Fin (W + 1), u ≠ acc j.succ) →
          pRec.evalBits δ u = δ u := progAddMod2Pow_evalBits_other W (cur + 1) (by omega)
          (fun j ↦ src j.succ) (fun j ↦ acc j.succ) cout _ _ _
          (hinjAcc.comp (Fin.succ_injective (W + 1))) _ _ _
      let inner : TempPhaseProg M := .seq (.cliff (.cnot cin cout (wire_ne_of_lt hc_lt)))
          (.seq pRec (.cliff (.cnot cin cout (wire_ne_of_lt hc_lt))))
      have hInnerOther : ∀ (δ : BitAssignment M) (u : Wire M),
          (∀ j : Fin (W + 1), u ≠ acc j.succ) → inner.evalBits δ u = δ u := fun δ u hu ↦ by
        dsimp only [inner, TempPhaseProg.evalBits, CliffProg.eval]
        have hcin_ne : ∀ j : Fin (W + 1), cin ≠ acc j.succ := fun j ↦ (hac j.succ).symm
        have hcout_ne : ∀ j : Fin (W + 1), cout ≠ acc j.succ :=
          fun j ↦ wire_ne_of_gt (ha_lt j.succ)
        have hcin_cout : cin ≠ cout := wire_ne_of_lt hc_lt
        let δ₁ := Function.update δ cout (δ cout + δ cin)
        have hrec_cin : pRec.evalBits δ₁ cin = δ cin :=
          (ih δ₁ cin hcin_ne).trans (Function.update_of_ne hcin_cout _ _)
        by_cases huc : u = cout
        · subst huc
          rw [Function.update_self, ih δ₁ cout hcout_ne, hrec_cin]
          dsimp only [δ₁]
          rw [Function.update_self]
          exact CharTwo.add_cancel_right _ _
        · rw [Function.update_of_ne huc, ih δ₁ u hu]
          dsimp only [δ₁]
          exact Function.update_of_ne huc _ _
      have hs0_succ : ∀ j : Fin (W + 1), src 0 ≠ acc j.succ := fun j ↦ hsa 0 j.succ
      have ha0_succ : ∀ j : Fin (W + 1), acc 0 ≠ acc j.succ :=
        fun j h ↦ Fin.succ_ne_zero j (hinjAcc h.symm)
      have hcout_succ : ∀ j : Fin (W + 1), cout ≠ acc j.succ :=
        fun j ↦ wire_ne_of_gt (ha_lt j.succ)
      have hcin_succ : ∀ j : Fin (W + 1), cin ≠ acc j.succ := fun j ↦ (hac j.succ).symm
      have hs0_cout : src 0 ≠ cout := wire_ne_of_lt (hs_lt 0)
      have ha0_cout : acc 0 ≠ cout := wire_ne_of_lt (ha_lt 0)
      have hcin_cout : cin ≠ cout := wire_ne_of_lt hc_lt
      let cPre : CliffProg M :=
        .seq (.cnot cin (src 0) (hsc 0).symm) (.cnot cin (acc 0) (hac 0).symm)
      let cPost : CliffProg M :=
        .seq (.cnot cin (src 0) (hsc 0).symm) (.cnot (src 0) (acc 0) (hsa 0 0))
      let β₁ := cPre.eval γ
      let β₂ := Function.update β₁ cout (β₁ cout + β₁ (src 0) * β₁ (acc 0))
      let β₅ := inner.evalBits β₂
      let β₆ := Function.update β₅ cout (β₅ cout + β₅ (src 0) * β₅ (acc 0))
      change (cPost.eval β₆) w = γ w
      have hβ₁_s0 : β₁ (src 0) = γ (src 0) + γ cin := by
        dsimp only [β₁, cPre, CliffProg.eval]
        rw [Function.update_of_ne (hsa 0 0), Function.update_self]
      have hβ₁_cin : β₁ cin = γ cin := by
        dsimp only [β₁, cPre, CliffProg.eval]
        rw [Function.update_of_ne (hac 0).symm, Function.update_of_ne (hsc 0).symm]
      have hβ₁_cout : β₁ cout = γ cout := by
        dsimp only [β₁, cPre, CliffProg.eval]
        rw [Function.update_of_ne ha0_cout.symm, Function.update_of_ne hs0_cout.symm]
      have hβ₅_s0 : β₅ (src 0) = β₁ (src 0) :=
        (hInnerOther β₂ (src 0) hs0_succ).trans (Function.update_of_ne hs0_cout _ _)
      have hβ₅_a0 : β₅ (acc 0) = β₁ (acc 0) :=
        (hInnerOther β₂ (acc 0) ha0_succ).trans (Function.update_of_ne ha0_cout _ _)
      have hβ₅_cout : β₅ cout = β₂ cout := hInnerOther β₂ cout hcout_succ
      have hβ₆_cout : β₆ cout = γ cout := by
        dsimp only [β₆]
        rw [Function.update_self, hβ₅_cout, hβ₅_s0, hβ₅_a0]
        dsimp only [β₂]
        rw [Function.update_self, CharTwo.add_cancel_right, hβ₁_cout]
      have hβ₆_s0 : β₆ (src 0) = γ (src 0) + γ cin := by
        dsimp only [β₆]
        rw [Function.update_of_ne hs0_cout, hβ₅_s0, hβ₁_s0]
      have hβ₆_cin : β₆ cin = γ cin := by
        dsimp only [β₆, β₅]
        rw [Function.update_of_ne hcin_cout, hInnerOther β₂ cin hcin_succ]
        dsimp only [β₂]
        rw [Function.update_of_ne hcin_cout, hβ₁_cin]
      dsimp only [cPost, CliffProg.eval]
      rw [Function.update_of_ne (hne 0)]
      by_cases hws0 : w = src 0
      · subst hws0
        rw [Function.update_self, hβ₆_s0, hβ₆_cin]
        exact CharTwo.add_cancel_right _ _
      · rw [Function.update_of_ne hws0]
        by_cases hwc : w = cout
        · subst hwc; exact hβ₆_cout
        · dsimp only [β₆, β₅]
          rw [Function.update_of_ne hwc, hInnerOther β₂ w (fun j ↦ hne j.succ)]
          dsimp only [β₂, β₁, cPre, CliffProg.eval]
          rw [Function.update_of_ne hwc, Function.update_of_ne (hne 0), Function.update_of_ne hws0]
theorem progAddMod2Pow_valid_and_val {M : ℕ} :
    ∀ (W cur : ℕ) (hcur : cur + W ≤ M)
      (src acc : Fin (W + 1) → Wire M) (cin : Wire M)
      (hsa : ∀ i j, src i ≠ acc j) (hsc : ∀ i, src i ≠ cin) (hac : ∀ i, acc i ≠ cin)
      (_hinjSrc : Function.Injective src)
      (_hinjAcc : Function.Injective acc)
      (hs_lt : ∀ i, (src i).val < cur) (ha_lt : ∀ i, (acc i).val < cur) (hc_lt : cin.val < cur),
      let p := progAddMod2Pow W cur hcur src acc cin hsa hsc hac hs_lt ha_lt hc_lt
      ValidCleanRem M (M - cur) p ∧
        ∀ γ : BitAssignment M, cleanRem M (M - cur) γ →
          bitsVal (fun j ↦ p.evalBits γ (acc j)) =
            (bitsVal (fun j ↦ γ (src j)) + bitsVal (fun j ↦ γ (acc j)) + (γ cin).val) %
              (2 ^ (W + 1))
  | 0, cur, _hcur, src, acc, cin, hsa, _, hac, _hinjSrc, _hinjAcc, _hs_lt, _ha_lt, _hc_lt => by
      refine ⟨trivial, fun γ _ ↦ ?_⟩
      dsimp only [progAddMod2Pow, TempPhaseProg.evalBits, CliffProg.eval]
      have hc_in : Function.update γ (acc 0) (γ (acc 0) + γ (src 0)) cin = γ cin :=
        Function.update_of_ne (hac 0).symm _ _
      have hbits1 : ∀ g : Fin 1 → ZMod 2, bitsVal g = (g 0).val := fun g ↦ by simp [bitsVal]
      rw [hbits1, hbits1, hbits1, Function.update_self, Function.update_self, hc_in]
      have hsum : γ (acc 0) + γ (src 0) + γ cin = γ (src 0) + γ (acc 0) + γ cin := by ring
      rw [hsum, zmod2_sum3_mod2]
      rfl
  | W + 1, cur, hcur, src, acc, cin, hsa, hsc, hac, hinjSrc, hinjAcc, hs_lt, ha_lt, hc_lt => by
      let cout : Wire M := ⟨cur, by omega⟩
      let pRec := progAddMod2Pow W (cur + 1) (by omega)
        (fun j ↦ src j.succ) (fun j ↦ acc j.succ) cout
        (fun i j ↦ hsa i.succ j.succ)
        (fun i ↦ wire_ne_of_lt (hs_lt i.succ))
        (fun i ↦ wire_ne_of_lt (ha_lt i.succ))
        (fun i ↦ lt_trans (hs_lt i.succ) (by omega))
        (fun i ↦ lt_trans (ha_lt i.succ) (by omega))
        (by dsimp [cout]; omega)
      have hRecOther : ∀ (δ : BitAssignment M) (u : Wire M),
          (∀ j : Fin (W + 1), u ≠ acc j.succ) → pRec.evalBits δ u = δ u :=
          progAddMod2Pow_evalBits_other W (cur + 1) (by omega) (fun j ↦ src j.succ)
          (fun j ↦ acc j.succ) cout _ _ _ (hinjAcc.comp (Fin.succ_injective (W + 1))) _ _ _
      obtain ⟨hvRec, hvalRec⟩ := progAddMod2Pow_valid_and_val W (cur + 1) (by omega)
        (fun j ↦ src j.succ) (fun j ↦ acc j.succ) cout _ _ _
        (hinjSrc.comp (Fin.succ_injective (W + 1)))
        (hinjAcc.comp (Fin.succ_injective (W + 1))) _ _ _
      let inner : TempPhaseProg M := .seq (.cliff (.cnot cin cout (wire_ne_of_lt hc_lt)))
          (.seq pRec (.cliff (.cnot cin cout (wire_ne_of_lt hc_lt))))
      have hInnerOther : ∀ (δ : BitAssignment M) (u : Wire M),
          (∀ j : Fin (W + 1), u ≠ acc j.succ) → inner.evalBits δ u = δ u := fun δ u hu ↦ by
        dsimp only [inner, TempPhaseProg.evalBits, CliffProg.eval]
        have hcin_ne : ∀ j : Fin (W + 1), cin ≠ acc j.succ := fun j ↦ (hac j.succ).symm
        have hcout_ne : ∀ j : Fin (W + 1), cout ≠ acc j.succ :=
          fun j ↦ wire_ne_of_gt (ha_lt j.succ)
        have hcin_cout : cin ≠ cout := wire_ne_of_lt hc_lt
        let δ₁ := Function.update δ cout (δ cout + δ cin)
        have hrec_cin : pRec.evalBits δ₁ cin = δ cin :=
          (hRecOther δ₁ cin hcin_ne).trans (Function.update_of_ne hcin_cout _ _)
        by_cases huc : u = cout
        · subst huc
          rw [Function.update_self, hRecOther δ₁ cout hcout_ne, hrec_cin]
          dsimp only [δ₁]
          rw [Function.update_self]
          exact CharTwo.add_cancel_right _ _
        · rw [Function.update_of_ne huc, hRecOther δ₁ u hu]
          dsimp only [δ₁]
          exact Function.update_of_ne huc _ _
      have hvInner : ValidCleanRem M (M - (cur + 1)) inner := by
        refine ⟨M - (cur + 1), by omega, trivial,
          ⟨0, Nat.zero_le M, hvRec, trivial, fun _ _ _ hw ↦ absurd hw (by omega)⟩,
          fun δ hδ u hu ↦ ?_⟩
        dsimp only [TempPhaseProg.evalBits, CliffProg.eval]
        rw [Function.update_of_ne (wire_ne_of_gt (by dsimp [cout]; omega))]
        exact hδ u hu
      let cPre : CliffProg M :=
        .seq (.cnot cin (src 0) (hsc 0).symm) (.cnot cin (acc 0) (hac 0).symm)
      have hvTemp : ValidCleanRem M (M - cur) (.tempAnd (src 0) (acc 0) cout (hsa 0 0)
          (wire_ne_of_lt (hs_lt 0)) (wire_ne_of_lt (ha_lt 0)) inner) :=
        ⟨by dsimp [cout]; omega, hvInner, fun δ _ ↦
          ⟨hInnerOther δ (src 0) (fun j ↦ hsa 0 j.succ),
           hInnerOther δ (acc 0) (fun j h ↦ Fin.succ_ne_zero j (hinjAcc h.symm)),
           hInnerOther δ cout (fun j ↦ wire_ne_of_gt (ha_lt j.succ))⟩⟩
      have hvAll : ValidCleanRem M (M - cur)
          (progAddMod2Pow (W + 1) cur hcur src acc cin hsa hsc hac hs_lt ha_lt hc_lt) := by
        refine ⟨M - cur, by omega, trivial,
          ⟨0, Nat.zero_le M, hvTemp, trivial, fun _ _ _ hw ↦ absurd hw (by omega)⟩,
          fun δ hδ u hu ↦ ?_⟩
        dsimp only [cPre, TempPhaseProg.evalBits, CliffProg.eval]
        rw [Function.update_of_ne (wire_ne_of_gt (lt_of_lt_of_le (ha_lt 0) (by omega))),
          Function.update_of_ne (wire_ne_of_gt (lt_of_lt_of_le (hs_lt 0) (by omega)))]
        exact hδ u hu
      refine ⟨hvAll, fun γ hγ ↦ ?_⟩
      let cPost : CliffProg M :=
        .seq (.cnot cin (src 0) (hsc 0).symm) (.cnot (src 0) (acc 0) (hsa 0 0))
      let β₁ := cPre.eval γ
      let β₂ := Function.update β₁ cout (β₁ cout + β₁ (src 0) * β₁ (acc 0))
      let β₃ := Function.update β₂ cout (β₂ cout + β₂ cin)
      let β₄ := pRec.evalBits β₃
      let β₅ := inner.evalBits β₂
      let β₆ := Function.update β₅ cout (β₅ cout + β₅ (src 0) * β₅ (acc 0))
      let β₇ := cPost.eval β₆
      change bitsVal (fun j : Fin (W + 2) ↦ β₇ (acc j)) = _
      have hs0_cout : src 0 ≠ cout := wire_ne_of_lt (hs_lt 0)
      have ha0_cout : acc 0 ≠ cout := wire_ne_of_lt (ha_lt 0)
      have hcin_cout : cin ≠ cout := wire_ne_of_lt hc_lt
      have hβ₁_s0 : β₁ (src 0) = γ (src 0) + γ cin := by
        dsimp only [β₁, cPre, CliffProg.eval]
        rw [Function.update_of_ne (hsa 0 0), Function.update_self]
      have hβ₁_a0 : β₁ (acc 0) = γ (acc 0) + γ cin := by
        dsimp only [β₁, cPre, CliffProg.eval]
        rw [Function.update_self, Function.update_of_ne (hsc 0).symm, Function.update_of_ne (hsa 0
          0).symm]
      have hβ₁_cin : β₁ cin = γ cin := by
        dsimp only [β₁, cPre, CliffProg.eval]
        rw [Function.update_of_ne (hac 0).symm, Function.update_of_ne (hsc 0).symm]
      have hβ₁_cout : β₁ cout = γ cout := by
        dsimp only [β₁, cPre, CliffProg.eval]
        rw [Function.update_of_ne ha0_cout.symm, Function.update_of_ne hs0_cout.symm]
      have hβ₅_s0 : β₅ (src 0) = γ (src 0) + γ cin := by
        dsimp only [β₅]
        rw [hInnerOther β₂ (src 0) (fun j ↦ hsa 0 j.succ)]
        dsimp only [β₂]
        rw [Function.update_of_ne hs0_cout, hβ₁_s0]
      have hβ₅_a0 : β₅ (acc 0) = γ (acc 0) + γ cin := by
        dsimp only [β₅]
        rw [hInnerOther β₂ (acc 0) (fun j h ↦ Fin.succ_ne_zero j (hinjAcc h.symm))]
        dsimp only [β₂]
        rw [Function.update_of_ne ha0_cout, hβ₁_a0]
      have hβ₅_cin : β₅ cin = γ cin := by
        dsimp only [β₅]
        rw [hInnerOther β₂ cin (fun j ↦ (hac j.succ).symm)]
        dsimp only [β₂]
        rw [Function.update_of_ne hcin_cout, hβ₁_cin]
      have hβ₇_acc0 : β₇ (acc 0) = γ (src 0) + γ (acc 0) + γ cin := by
        dsimp only [β₇, cPost, CliffProg.eval, β₆]
        rw[Function.update_self, Function.update_of_ne (hsa 0 0).symm,
            Function.update_of_ne ha0_cout, Function.update_self,
            Function.update_of_ne hs0_cout, Function.update_of_ne hcin_cout, hβ₅_a0, hβ₅_s0,
            hβ₅_cin, CharTwo.add_cancel_right (γ (src 0)) (γ cin)]
        ring
      have hβ₇_succ : (fun j : Fin (W + 1) ↦ β₇ (acc j.succ)) = fun j ↦ β₄ (acc j.succ) := by
        funext j
        have ha_ne0 : acc j.succ ≠ acc 0 := fun h ↦ Fin.succ_ne_zero j (hinjAcc h)
        have ha_nes0 : acc j.succ ≠ src 0 := (hsa 0 j.succ).symm
        have ha_necout : acc j.succ ≠ cout := wire_ne_of_lt (ha_lt j.succ)
        dsimp only [β₇, cPost, CliffProg.eval, β₆, β₅, inner, TempPhaseProg.evalBits]
        rw [Function.update_of_ne ha_ne0, Function.update_of_ne ha_nes0,
          Function.update_of_ne ha_necout, Function.update_of_ne ha_necout]
      have hcl₃ : cleanRem M (M - (cur + 1)) β₃ := fun u hu ↦ by
        have hu_cout : u ≠ cout := wire_ne_of_gt (by dsimp [cout]; omega)
        have hu_a0 : u ≠ acc 0 := wire_ne_of_gt (lt_of_lt_of_le (ha_lt 0) (by omega))
        have hu_s0 : u ≠ src 0 := wire_ne_of_gt (lt_of_lt_of_le (hs_lt 0) (by omega))
        dsimp only [β₃, β₂, β₁, cPre, CliffProg.eval]
        rw [Function.update_of_ne hu_cout, Function.update_of_ne hu_cout,
          Function.update_of_ne hu_a0, Function.update_of_ne hu_s0]
        exact hγ u (by omega)
      have hβ₃_src : (fun j : Fin (W + 1) ↦ β₃ (src j.succ)) = fun j ↦ γ (src j.succ) := by
        funext j
        have hs_ne0 : src j.succ ≠ src 0 := fun h ↦ Fin.succ_ne_zero j (hinjSrc h)
        have hs_nea0 : src j.succ ≠ acc 0 := hsa j.succ 0
        have hs_necout : src j.succ ≠ cout := wire_ne_of_lt (hs_lt j.succ)
        dsimp only [β₃, β₂, β₁, cPre, CliffProg.eval]
        rw [Function.update_of_ne hs_necout, Function.update_of_ne hs_necout,
          Function.update_of_ne hs_nea0, Function.update_of_ne hs_ne0]
      have hβ₃_acc : (fun j : Fin (W + 1) ↦ β₃ (acc j.succ)) = fun j ↦ γ (acc j.succ) := by
        funext j
        have ha_ne0 : acc j.succ ≠ acc 0 := fun h ↦ Fin.succ_ne_zero j (hinjAcc h)
        have ha_nes0 : acc j.succ ≠ src 0 := (hsa 0 j.succ).symm
        have ha_necout : acc j.succ ≠ cout := wire_ne_of_lt (ha_lt j.succ)
        dsimp only [β₃, β₂, β₁, cPre, CliffProg.eval]
        rw [Function.update_of_ne ha_necout, Function.update_of_ne ha_necout,
          Function.update_of_ne ha_ne0, Function.update_of_ne ha_nes0]
      have hβ₃_cout : β₃ cout = γ cin + (γ (src 0) + γ cin) * (γ (acc 0) + γ cin) := by
        have hγ_cout : γ cout = 0 := hγ cout (by dsimp [cout]; omega)
        dsimp only [β₃]
        rw [Function.update_self]
        dsimp only [β₂]
        rw [Function.update_self, Function.update_of_ne hcin_cout,
          hβ₁_cout, hγ_cout, hβ₁_s0, hβ₁_a0, hβ₁_cin]
        ring
      rw[bitsVal_succ_split, hβ₇_acc0, hβ₇_succ, hvalRec β₃ hcl₃, hβ₃_src, hβ₃_acc, hβ₃_cout,
          bitsVal_succ_split (fun j ↦ γ (src j)), bitsVal_succ_split (fun j ↦ γ (acc j))]
      have hfa := fullAdd_val_eq (γ (src 0)) (γ (acc 0)) (γ cin)
      have hlt0 : (γ (src 0) + γ (acc 0) + γ cin).val < 2 := ZMod.val_lt _
      have hpow : 2 ^ (W + 2) = 2 * 2 ^ (W + 1) := by ring
      set M2 := 2 ^ (W + 1)
      set Q := bitsVal (fun j ↦ γ (src j.succ)) + bitsVal (fun j ↦ γ (acc j.succ)) +
        (γ cin + (γ (src 0) + γ cin) * (γ (acc 0) + γ cin)).val
      set R := (γ (src 0) + γ (acc 0) + γ cin).val
      have hmod : R + 2 * (Q % M2) = (R + 2 * Q) % (2 * M2) := by
        have hltQ : Q % M2 < M2 := Nat.mod_lt Q (by positivity)
        have hlt2 : R + 2 * (Q % M2) < 2 * M2 := by omega
        have hq : Q = M2 * (Q / M2) + Q % M2 := (Nat.div_add_mod Q M2).symm
        have h1 : R + 2 * Q = (R + 2 * (Q % M2)) + (2 * M2) * (Q / M2) := by
          nth_rw 1 [hq]; ring
        rw [h1, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt2]
      rw [hmod, hpow]
      congr 1
      omega
attribute [local irreducible] progAddMod2Pow
def wPack143 (k : Fin 12) : Wire 143 := ⟨k.val, by omega⟩
def wOrb143 (k : Fin 16) : Wire 143 := ⟨12 + k.val, by omega⟩
theorem wOrb143_injective : Function.Injective wOrb143 := fun i j h ↦ by
  have hv := congrArg Fin.val h
  dsimp only [wOrb143] at hv
  exact Fin.ext (by omega)
def mutOrb143 (w : Wire 143) : Prop := ∃ k : Fin 16, w = wOrb143 k
instance instDecidablePredMutOrb143 : DecidablePred mutOrb143 := fun w ↦
  decidable_of_iff (12 ≤ w.val ∧ w.val < 28)
    ⟨fun ⟨h12, h28⟩ ↦ ⟨⟨w.val - 12, by omega⟩, Fin.ext (by dsimp [wOrb143]; omega)⟩,
     fun ⟨k, hk⟩ ↦ by
       subst hk; exact ⟨by dsimp [wOrb143]; omega, by have := k.isLt; dsimp [wOrb143]; omega⟩⟩
theorem not_mutOrb143_of_lt12 {w : Wire 143} (hw : w.val < 12) : ¬ mutOrb143 w := by
  rintro ⟨k, rfl⟩; dsimp only [wOrb143] at hw; omega
theorem not_mutOrb143_of_ge28 {w : Wire 143} (hw : 28 ≤ w.val) : ¬ mutOrb143 w := by
  rintro ⟨k, rfl⟩; have _ := k.isLt; dsimp only [wOrb143] at hw; omega
def wZero143 : Wire 143 := ⟨28, by decide⟩
def wW6_143 : Wire 143 := ⟨29, by decide⟩
def wT2_143 : Wire 143 := ⟨30, by decide⟩
def wV6_143 : Wire 143 := ⟨31, by decide⟩
def v7W143 (k : Fin 7) : Wire 143 :=
  match k.val with
  | 0 => wPack143 0
  | 1 => wPack143 1
  | 2 => wPack143 2
  | 3 => wPack143 3
  | 4 => wPack143 4
  | 5 => wPack143 10
  | _ => wV6_143
def w7W143 (k : Fin 7) : Wire 143 :=
  match k.val with
  | 0 => wPack143 5
  | 1 => wPack143 6
  | 2 => wPack143 7
  | 3 => wPack143 8
  | 4 => wPack143 9
  | 5 => wPack143 11
  | _ => wW6_143
def cUnpack12Post : CliffProg 143 := .seq (.cnot wT2_143 (wPack143 5) (by decide)) (.seq
    (.cnot wV6_143 (wPack143 6) (by decide)) (.seq (.cnot wW6_143 (wPack143 10) (by decide))
    (.cnot wT2_143 (wPack143 10) (by decide))))
theorem cUnpack12Post_supp32 : cUnpack12Post.SupportsBelow 32 := by
  simp only [cUnpack12Post, CliffProg.SupportsBelow]
  decide
theorem cUnpack12Post_disj : CliffDisjoint mutOrb143 cUnpack12Post :=
  ⟨⟨not_mutOrb143_of_ge28 (by decide), not_mutOrb143_of_lt12 (by decide)⟩,
   ⟨⟨not_mutOrb143_of_ge28 (by decide), not_mutOrb143_of_lt12 (by decide)⟩,
    ⟨⟨not_mutOrb143_of_ge28 (by decide), not_mutOrb143_of_lt12 (by decide)⟩,
     ⟨not_mutOrb143_of_ge28 (by decide), not_mutOrb143_of_lt12 (by decide)⟩⟩⟩⟩
/-- `3`-`TempAnd` (`12 T`) `(v, w)` unpacker on `[29 .. 32)` from `wPack143`. -/
def ctxUnpack12_143 : TempCtx 143 := (ctxCliffAlloc (.x (wPack143 11))).append ((ctxTempBit
    (wPack143 10) (wPack143 11) wW6_143 (by decide) (by decide) (by decide)).append
    ((ctxCliffAlloc (.x (wPack143 11))).append ((ctxTempBit wW6_143 (wPack143 5) wT2_143
    (by decide) (by decide) (by decide)).append ((ctxTempBit wW6_143 (wPack143 6) wV6_143
    (by decide) (by decide) (by decide)).append (ctxCliffAlloc cUnpack12Post)))))
theorem ctxUnpack12_143_disj_supp :
    ctxUnpack12_143.DisjointFrom mutOrb143 ∧ ctxUnpack12_143.SupportsBelowCtx 32 :=
  ⟨TempCtx.disjointFrom_append
      (ctxCliffAlloc_disjoint (not_mutOrb143_of_lt12 (by decide)))
      (TempCtx.disjointFrom_append
        ⟨not_mutOrb143_of_lt12 (by decide), not_mutOrb143_of_lt12 (by decide),
          not_mutOrb143_of_ge28 (by decide), trivial⟩
        (TempCtx.disjointFrom_append
          (ctxCliffAlloc_disjoint (not_mutOrb143_of_lt12 (by decide)))
          (TempCtx.disjointFrom_append
            ⟨not_mutOrb143_of_ge28 (by decide), not_mutOrb143_of_lt12 (by decide),
              not_mutOrb143_of_ge28 (by decide), trivial⟩
            (TempCtx.disjointFrom_append
              ⟨not_mutOrb143_of_ge28 (by decide), not_mutOrb143_of_lt12 (by decide),
                not_mutOrb143_of_ge28 (by decide), trivial⟩
              (ctxCliffAlloc_disjoint cUnpack12Post_disj))))),
    TempCtx.supportsBelowCtx_append (c₁ := 32) le_rfl
      (ctxCliffAlloc_supports (show (wPack143 11).val < 32 by decide))
      (TempCtx.supportsBelowCtx_append (c₁ := 32) le_rfl ⟨by decide, trivial⟩
        (TempCtx.supportsBelowCtx_append (c₁ := 32) le_rfl
          (ctxCliffAlloc_supports (show (wPack143 11).val < 32 by decide))
          (TempCtx.supportsBelowCtx_append (c₁ := 32) le_rfl ⟨by decide, trivial⟩
            (TempCtx.supportsBelowCtx_append (c₁ := 32) le_rfl ⟨by decide, trivial⟩
              (ctxCliffAlloc_supports cUnpack12Post_supp32)))))⟩
def setupUnpack12 (β : BitAssignment 143) : BitAssignment 143 :=
  let γ₁ := (CliffProg.x (wPack143 11)).eval β
  let γ₂ := Function.update γ₁ wW6_143 (γ₁ (wPack143 10) * γ₁ (wPack143 11))
  let γ₃ := (CliffProg.x (wPack143 11)).eval γ₂
  let γ₄ := Function.update γ₃ wT2_143 (γ₃ wW6_143 * γ₃ (wPack143 5))
  let γ₅ := Function.update γ₄ wV6_143 (γ₄ wW6_143 * γ₄ (wPack143 6))
  cUnpack12Post.eval γ₅
theorem setupUnpack12_eval (β : BitAssignment 143) :
    let t1 := β (wPack143 10) * (β (wPack143 11) + 1)
    let t2 := t1 * β (wPack143 5)
    let t3 := t1 * β (wPack143 6)
    (∀ w : Wire 143, 32 ≤ w.val → setupUnpack12 β w = β w) ∧
    setupUnpack12 β wZero143 = β wZero143 ∧
    setupUnpack12 β wW6_143 = t1 ∧
    setupUnpack12 β wT2_143 = t2 ∧
    setupUnpack12 β wV6_143 = t3 ∧
    setupUnpack12 β (wPack143 5) = β (wPack143 5) + t2 ∧
    setupUnpack12 β (wPack143 6) = β (wPack143 6) + t3 ∧
    setupUnpack12 β (wPack143 10) = β (wPack143 10) + t1 + t2 ∧
    setupUnpack12 β (wPack143 11) = β (wPack143 11) ∧
    (∀ k : Fin 12, k ≠ 5 → k ≠ 6 → k ≠ 10 → k ≠ 11 →
      setupUnpack12 β (wPack143 k) = β (wPack143 k)) := by
  intro t1 t2 t3
  let γ₁ := (CliffProg.x (wPack143 11)).eval β
  let γ₂ := Function.update γ₁ wW6_143 (γ₁ (wPack143 10) * γ₁ (wPack143 11))
  let γ₃ := (CliffProg.x (wPack143 11)).eval γ₂
  let γ₄ := Function.update γ₃ wT2_143 (γ₃ wW6_143 * γ₃ (wPack143 5))
  let γ₅ := Function.update γ₄ wV6_143 (γ₄ wW6_143 * γ₄ (wPack143 6))
  have hγ₅_w6 : γ₅ wW6_143 = t1 := by
    simp [γ₅, γ₄, γ₃, γ₂, γ₁, t1, CliffProg.eval,
      Function.update_of_ne (by decide : wW6_143 ≠ wV6_143),
      Function.update_of_ne (by decide : wW6_143 ≠ wT2_143),
      Function.update_of_ne (by decide : wW6_143 ≠ wPack143 11),
      Function.update_of_ne (by decide : wPack143 10 ≠ wPack143 11)]
  have hγ₅_t2 : γ₅ wT2_143 = t2 := by
    simp [γ₅, γ₄, γ₃, γ₂, γ₁, t2, t1, CliffProg.eval,
      Function.update_of_ne (by decide : wT2_143 ≠ wV6_143),
      Function.update_of_ne (by decide : wW6_143 ≠ wPack143 11),
      Function.update_of_ne (by decide : wPack143 10 ≠ wPack143 11),
      Function.update_of_ne (by decide : wPack143 5 ≠ wPack143 11),
      Function.update_of_ne (by decide : wPack143 5 ≠ wW6_143)]
  have hγ₅s6Aux : γ₅ wV6_143 = t3 := by
    simp [γ₅, γ₄, γ₃, γ₂, γ₁, t3, t1, CliffProg.eval,
      Function.update_of_ne (by decide : wW6_143 ≠ wT2_143),
      Function.update_of_ne (by decide : wW6_143 ≠ wPack143 11),
      Function.update_of_ne (by decide : wPack143 10 ≠ wPack143 11),
      Function.update_of_ne (by decide : wPack143 6 ≠ wT2_143),
      Function.update_of_ne (by decide : wPack143 6 ≠ wPack143 11),
      Function.update_of_ne (by decide : wPack143 6 ≠ wW6_143)]
  have hγ₅_pack : ∀ k : Fin 12, γ₅ (wPack143 k) = β (wPack143 k) := fun k ↦ by
    have hnev : wPack143 k ≠ wV6_143 := wire_ne_of_lt (by
      have := k.isLt; dsimp [wPack143, wV6_143]; omega)
    have hnet : wPack143 k ≠ wT2_143 := wire_ne_of_lt (by
      have := k.isLt; dsimp [wPack143, wT2_143]; omega)
    have hnew : wPack143 k ≠ wW6_143 := wire_ne_of_lt (by
      have := k.isLt; dsimp [wPack143, wW6_143]; omega)
    dsimp only [γ₅, γ₄, γ₃, γ₂, γ₁, CliffProg.eval]
    rw [Function.update_of_ne hnev, Function.update_of_ne hnet]
    by_cases hk11 : wPack143 k = wPack143 11
    · rw [hk11, Function.update_self,
        Function.update_of_ne (by decide : wPack143 11 ≠ wW6_143),
        Function.update_self, CharTwo.add_cancel_right]
    · rw [Function.update_of_ne hk11, Function.update_of_ne hnew, Function.update_of_ne hk11]
  refine ⟨fun w hw ↦ ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun k h5 h6 h10 _ ↦ ?_⟩
  · change cUnpack12Post.eval γ₅ w = β w
    rw [cUnpack12Post.eval_outside cUnpack12Post_supp32 γ₅ w (by omega)]
    have hnev : w ≠ wV6_143 := wire_ne_of_gt (by dsimp [wV6_143]; omega)
    have hnet : w ≠ wT2_143 := wire_ne_of_gt (by dsimp [wT2_143]; omega)
    have hne11 : w ≠ wPack143 11 := wire_ne_of_gt (by dsimp [wPack143]; omega)
    have hnew : w ≠ wW6_143 := wire_ne_of_gt (by dsimp [wW6_143]; omega)
    simp[γ₅, γ₄, γ₃, γ₂, γ₁, CliffProg.eval, Function.update_of_ne hnev,
        Function.update_of_ne hnet, Function.update_of_ne hne11, Function.update_of_ne hnew]
  · change cUnpack12Post.eval γ₅ wZero143 = β wZero143
    dsimp only [cUnpack12Post, CliffProg.eval]
    simp [γ₅, γ₄, γ₃, γ₂, γ₁, CliffProg.eval,
      Function.update_of_ne (by decide : wZero143 ≠ wPack143 10),
      Function.update_of_ne (by decide : wZero143 ≠ wPack143 6),
      Function.update_of_ne (by decide : wZero143 ≠ wPack143 5),
      Function.update_of_ne (by decide : wZero143 ≠ wV6_143),
      Function.update_of_ne (by decide : wZero143 ≠ wT2_143),
      Function.update_of_ne (by decide : wZero143 ≠ wPack143 11),
      Function.update_of_ne (by decide : wZero143 ≠ wW6_143)]
  · change cUnpack12Post.eval γ₅ wW6_143 = t1
    dsimp only [cUnpack12Post, CliffProg.eval]
    simp[hγ₅_w6, Function.update_of_ne (by decide : wW6_143 ≠ wPack143 10),
        Function.update_of_ne (by decide : wW6_143 ≠ wPack143 6),
        Function.update_of_ne (by decide : wW6_143 ≠ wPack143 5)]
  · change cUnpack12Post.eval γ₅ wT2_143 = t2
    dsimp only [cUnpack12Post, CliffProg.eval]
    simp[hγ₅_t2, Function.update_of_ne (by decide : wT2_143 ≠ wPack143 10),
        Function.update_of_ne (by decide : wT2_143 ≠ wPack143 6),
        Function.update_of_ne (by decide : wT2_143 ≠ wPack143 5)]
  · change cUnpack12Post.eval γ₅ wV6_143 = t3
    dsimp only [cUnpack12Post, CliffProg.eval]
    simp[hγ₅s6Aux, Function.update_of_ne (by decide : wV6_143 ≠ wPack143 10),
        Function.update_of_ne (by decide : wV6_143 ≠ wPack143 6),
        Function.update_of_ne (by decide : wV6_143 ≠ wPack143 5)]
  · change cUnpack12Post.eval γ₅ (wPack143 5) = β (wPack143 5) + t2
    dsimp only [cUnpack12Post, CliffProg.eval]
    simp[hγ₅_pack 5, hγ₅_t2, Function.update_of_ne (by decide : wPack143 5 ≠ wPack143 10),
        Function.update_of_ne (by decide : wPack143 5 ≠ wPack143 6)]
  · change cUnpack12Post.eval γ₅ (wPack143 6) = β (wPack143 6) + t3
    dsimp only [cUnpack12Post, CliffProg.eval]
    simp[hγ₅_pack 6, hγ₅s6Aux, Function.update_of_ne (by decide : wPack143 6 ≠ wPack143 10),
        Function.update_of_ne (by decide : wPack143 6 ≠ wPack143 5),
        Function.update_of_ne (by decide : wV6_143 ≠ wPack143 5)]
  · change cUnpack12Post.eval γ₅ (wPack143 10) = β (wPack143 10) + t1 + t2
    dsimp only [cUnpack12Post, CliffProg.eval]
    simp [hγ₅_pack 10, hγ₅_w6, hγ₅_t2,
      Function.update_of_ne (by decide : wPack143 10 ≠ wPack143 6),
      Function.update_of_ne (by decide : wPack143 10 ≠ wPack143 5),
      Function.update_of_ne (by decide : wW6_143 ≠ wPack143 6),
      Function.update_of_ne (by decide : wW6_143 ≠ wPack143 5),
      Function.update_of_ne (by decide : wT2_143 ≠ wPack143 10),
      Function.update_of_ne (by decide : wT2_143 ≠ wPack143 6),
      Function.update_of_ne (by decide : wT2_143 ≠ wPack143 5)]
  · change cUnpack12Post.eval γ₅ (wPack143 11) = β (wPack143 11)
    dsimp only [cUnpack12Post, CliffProg.eval]
    simp[hγ₅_pack 11, Function.update_of_ne (by decide : wPack143 11 ≠ wPack143 10),
        Function.update_of_ne (by decide : wPack143 11 ≠ wPack143 6),
        Function.update_of_ne (by decide : wPack143 11 ≠ wPack143 5)]
  · change cUnpack12Post.eval γ₅ (wPack143 k) = β (wPack143 k)
    have hne10 : wPack143 k ≠ wPack143 10 := fun h ↦ h10 (Fin.ext (congrArg (Fin.val : Wire 143 →
      ℕ) h))
    have hne6 : wPack143 k ≠ wPack143 6 := fun h ↦ h6 (Fin.ext (congrArg (Fin.val : Wire 143 →
      ℕ) h))
    have hne5 : wPack143 k ≠ wPack143 5 := fun h ↦ h5 (Fin.ext (congrArg (Fin.val : Wire 143 →
      ℕ) h))
    dsimp only [cUnpack12Post, CliffProg.eval]
    simp [hγ₅_pack k, Function.update_of_ne hne10, Function.update_of_ne hne6, Function.update_of_ne
      hne5]
theorem ScopedBlock.ctxUnpack12_143_block (leaf body : TempPhaseProg 143)
    (sBody : BitAssignment 143 → BitAssignment 143)
    (hBody : ScopedBlock 143 (143 - 32) sBody leaf body) : ScopedBlock 143 (143 - 29)
    (fun β ↦ sBody (setupUnpack12 β)) leaf (ctxUnpack12_143.plug body) ∧ (∀ (β : BitAssignment
    143) (c : CanonicalTriple65), cleanRem 143 (143 - 29) β → (∀ k : Fin 12, β (wPack143 k) =
    packCanonVW12 c k) → cleanRem 143 (143 - 32) (setupUnpack12 β) ∧ setupUnpack12 β wZero143
    = β wZero143 ∧ bitsVal (fun k ↦ setupUnpack12 β (v7W143 k)) = c.v.val ∧ bitsVal (fun k ↦
    setupUnpack12 β (w7W143 k)) = c.w.val) := by
  have h6 := ScopedBlock.withCliffAlloc_block (M := 143) (rem := 143 - 32) (remIn := 143 - 32)
    (by decide) le_rfl cUnpack12Post cUnpack12Post_supp32 hBody
  have h5 := ScopedBlock.withTempBit_block (M := 143) 31 (by decide)
    wW6_143 (wPack143 6) (by decide) (by decide) (by decide) h6
  have h4 := ScopedBlock.withTempBit_block (M := 143) 30 (by decide)
    wW6_143 (wPack143 5) (by decide) (by decide) (by decide) h5
  have h3 := ScopedBlock.withCliffAlloc_block (M := 143) (rem := 143 - 30) (remIn := 143 - 30)
    (by decide) le_rfl (.x (wPack143 11)) (by decide : (wPack143 11).val < 30) h4
  have h2 := ScopedBlock.withTempBit_block (M := 143) 29 (by decide)
    (wPack143 10) (wPack143 11) (by decide) (by decide) (by decide) h3
  have h1 := ScopedBlock.withCliffAlloc_block (M := 143) (rem := 143 - 29) (remIn := 143 - 29)
    (by decide) le_rfl (.x (wPack143 11)) (by decide : (wPack143 11).val < 29) h2
  have hBlock : ScopedBlock 143 (143 - 29) (fun β ↦ sBody (setupUnpack12 β)) leaf
      (ctxUnpack12_143.plug body) :=
    ⟨by
      dsimp only [ctxUnpack12_143]
      rw[TempCtx.append_plug, TempCtx.append_plug, TempCtx.append_plug, TempCtx.append_plug,
          TempCtx.append_plug, ctxCliffAlloc_plug, ctxTempBit_plug, ctxCliffAlloc_plug,
          ctxTempBit_plug, ctxTempBit_plug, ctxCliffAlloc_plug]
      exact h1.valid,
     fun β hβ ↦ by
      dsimp only [ctxUnpack12_143]
      rw[TempCtx.append_plug, TempCtx.append_plug, TempCtx.append_plug, TempCtx.append_plug,
          TempCtx.append_plug, ctxCliffAlloc_plug, ctxTempBit_plug, ctxCliffAlloc_plug,
          ctxTempBit_plug, ctxTempBit_plug, ctxCliffAlloc_plug]
      exact h1.bits β hβ,
     fun β hβ ↦ by
      dsimp only [ctxUnpack12_143]
      rw[TempCtx.append_plug, TempCtx.append_plug, TempCtx.append_plug, TempCtx.append_plug,
          TempCtx.append_plug, ctxCliffAlloc_plug, ctxTempBit_plug, ctxCliffAlloc_plug,
          ctxTempBit_plug, ctxTempBit_plug, ctxCliffAlloc_plug]
      exact h1.sign β hβ⟩
  refine ⟨hBlock, fun β c hβ hpack ↦ ?_⟩
  obtain ⟨hge32, hz0, hw6, ht2, hv6, hp5, hp6, hp10, hp11, hpOth⟩ := setupUnpack12_eval β
  obtain ⟨ht1_alg, ht2_alg, ht3_alg, hb5_alg, hb6_alg, hb10_alg⟩ := unpackCanonVW12_algebra c
  have hcl32 : cleanRem 143 (143 - 32) (setupUnpack12 β) := fun w hw ↦
    (hge32 w hw).trans (hβ w (by omega))
  have hp5_eq : β (wPack143 5) = packCanonVW12 c 5 := hpack 5
  have hp6_eq : β (wPack143 6) = packCanonVW12 c 6 := hpack 6
  have hp10_eq : β (wPack143 10) = packCanonVW12 c 10 := hpack 10
  have hp11_eq : β (wPack143 11) = packCanonVW12 c 11 := hpack 11
  have hv_eq : (fun k : Fin 7 ↦ setupUnpack12 β (v7W143 k)) = fin65Bits7 c.v := by
    funext k; fin_cases k
    · change setupUnpack12 β (wPack143 0) = _
      rw [hpOth 0 (by decide) (by decide) (by decide) (by decide), hpack 0]; rfl
    · change setupUnpack12 β (wPack143 1) = _
      rw [hpOth 1 (by decide) (by decide) (by decide) (by decide), hpack 1]; rfl
    · change setupUnpack12 β (wPack143 2) = _
      rw [hpOth 2 (by decide) (by decide) (by decide) (by decide), hpack 2]; rfl
    · change setupUnpack12 β (wPack143 3) = _
      rw [hpOth 3 (by decide) (by decide) (by decide) (by decide), hpack 3]; rfl
    · change setupUnpack12 β (wPack143 4) = _
      rw [hpOth 4 (by decide) (by decide) (by decide) (by decide), hpack 4]; rfl
    · change setupUnpack12 β (wPack143 10) = _
      rw [hp10, hp10_eq, hp11_eq, hp5_eq]; exact hb10_alg
    · change setupUnpack12 β wV6_143 = _
      rw [hv6, hp10_eq, hp11_eq, hp6_eq]; exact ht3_alg
  have hw_eq : (fun k : Fin 7 ↦ setupUnpack12 β (w7W143 k)) = fin65Bits7 c.w := by
    funext k; fin_cases k
    · change setupUnpack12 β (wPack143 5) = _
      rw [hp5, hp5_eq, hp10_eq, hp11_eq]; exact hb5_alg
    · change setupUnpack12 β (wPack143 6) = _
      rw [hp6, hp6_eq, hp10_eq, hp11_eq]; exact hb6_alg
    · change setupUnpack12 β (wPack143 7) = _
      rw [hpOth 7 (by decide) (by decide) (by decide) (by decide), hpack 7]; rfl
    · change setupUnpack12 β (wPack143 8) = _
      rw [hpOth 8 (by decide) (by decide) (by decide) (by decide), hpack 8]; rfl
    · change setupUnpack12 β (wPack143 9) = _
      rw [hpOth 9 (by decide) (by decide) (by decide) (by decide), hpack 9]; rfl
    · change setupUnpack12 β (wPack143 11) = _; rw [hp11, hp11_eq]; rfl
    · change setupUnpack12 β wW6_143 = _
      rw [hw6, hp10_eq, hp11_eq]; exact ht1_alg
  exact ⟨hcl32, hz0, hv_eq ▸ fin65Bits7_val c.v, hw_eq ▸ fin65Bits7_val c.w⟩
def v7List143 : List (Wire 143) :=
  [v7W143 0, v7W143 1, v7W143 2, v7W143 3, v7W143 4, v7W143 5, v7W143 6]
def w7List143 : List (Wire 143) :=
  [w7W143 0, w7W143 1, w7W143 2, w7W143 3, w7W143 4, w7W143 5, w7W143 6]
theorem v7List143_lt32 : ∀ w ∈ v7List143, w.val < 32 := by decide
theorem w7List143_lt66 : ∀ w ∈ w7List143, w.val < 66 := by decide
theorem v7List143_not_mut : ∀ w ∈ v7List143, ¬ mutOrb143 w := by
  intro w hw
  simp only [v7List143, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact not_mutOrb143_of_lt12 (by decide)
  · exact not_mutOrb143_of_lt12 (by decide)
  · exact not_mutOrb143_of_lt12 (by decide)
  · exact not_mutOrb143_of_lt12 (by decide)
  · exact not_mutOrb143_of_lt12 (by decide)
  · exact not_mutOrb143_of_lt12 (by decide)
  · exact not_mutOrb143_of_ge28 (by decide)
theorem w7List143_not_mut : ∀ w ∈ w7List143, ¬ mutOrb143 w := by
  intro w hw
  simp only [w7List143, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact not_mutOrb143_of_lt12 (by decide)
  · exact not_mutOrb143_of_lt12 (by decide)
  · exact not_mutOrb143_of_lt12 (by decide)
  · exact not_mutOrb143_of_lt12 (by decide)
  · exact not_mutOrb143_of_lt12 (by decide)
  · exact not_mutOrb143_of_lt12 (by decide)
  · exact not_mutOrb143_of_ge28 (by decide)
def tri12W143 (j : Fin 12) : Wire 143 := ⟨54 + j.val, by omega⟩
def tet16W143 (j : Fin 16) : Wire 143 := ⟨97 + j.val, by omega⟩
def tet15HiW143 (j : Fin 15) : Wire 143 := tet16W143 j.succ
def cinZero143 : Wire 143 := ⟨113, by decide⟩
theorem tet15HiW143_injective : Function.Injective tet15HiW143 := fun i j h ↦ by
  have hv := congrArg Fin.val h; dsimp [tet15HiW143, tet16W143] at hv; exact Fin.ext (by omega)
def triPad15Hi143 (j : Fin 15) : Wire 143 :=
  if hj : j.val < 11 then tri12W143 ⟨j.val + 1, by omega⟩ else wZero143
theorem triPad15Hi143_le65 : ∀ j : Fin 15, (triPad15Hi143 j).val ≤ 65 := by decide
theorem triPad15Hi143_not_mut (j : Fin 15) : ¬ mutOrb143 (triPad15Hi143 j) :=
  not_mutOrb143_of_ge28 (by fin_cases j <;> decide)
def outVW16_143 (k : Fin 16) : Wire 143 := if k.val = 0 then tri12W143 0 else tet16W143 k
theorem outVW16_143_ge28 : ∀ k : Fin 16, 28 ≤ (outVW16_143 k).val := by decide
theorem outVW16_143_lt97_or_gt97 : ∀ k : Fin 16, (outVW16_143 k).val ≠ 97 := by decide
theorem outVW16_143_lt128 : ∀ k : Fin 16, (outVW16_143 k).val < 128 := by decide
theorem outVW16_143_injective : Function.Injective outVW16_143 := fun i j h ↦ by
  have hv := congrArg Fin.val h
  dsimp only [outVW16_143] at hv
  split_ifs at hv <;> (dsimp [tri12W143, tet16W143] at hv; exact Fin.ext (by omega))
def tetBit0 (c : CanonicalTriple65) : ZMod 2 :=
  basisBits 16 ⟨tetNum c.w.val, by
    have := (tetRank65 c).isLt
    have hp : (tetRank65 c).val = tetNum c.w.val + triNum c.v.val + c.u.val := rfl
    dsimp [orbitCount47905] at this; omega⟩ 0
theorem tetBit0_le_vw (c : CanonicalTriple65) : (tetBit0 c).val ≤ triNum c.v.val + tetNum
    c.w.val ∧ triNum c.v.val + tetNum c.w.val - (tetBit0 c).val < 2 ^ 16 := by
  let f16 := basisBits 16 ⟨tetNum c.w.val, by
    have := (tetRank65 c).isLt
    have hp : (tetRank65 c).val = tetNum c.w.val + triNum c.v.val + c.u.val := rfl
    dsimp [orbitCount47905] at this; omega⟩
  have hval : bitsVal f16 = tetNum c.w.val := bitsVal_basisBits _
  have hsplit := bitsVal_succ_split f16
  have hrk := (tetRank65 c).isLt
  have hp : (tetRank65 c).val = tetNum c.w.val + triNum c.v.val + c.u.val := rfl
  dsimp [orbitCount47905] at hrk
  change (f16 0).val ≤ _ ∧ _
  omega
def outVWVal (c : CanonicalTriple65) : Fin (2 ^ 16) :=
  ⟨triNum c.v.val + tetNum c.w.val - (tetBit0 c).val, (tetBit0_le_vw c).2⟩
def addOrbBody143 : TempPhaseProg 143 :=
  progAddMod2Pow 15 128 (by decide) outVW16_143 wOrb143 (tet16W143 0)
    (fun i j ↦ wire_ne_of_gt (lt_of_lt_of_le (by have := j.isLt; dsimp [wOrb143]; omega)
      (outVW16_143_ge28 i)))
    (fun i h ↦ outVW16_143_lt97_or_gt97 i (congrArg Fin.val h))
    (fun i ↦ wire_ne_of_lt (by have := i.isLt; dsimp [wOrb143, tet16W143]; omega))
    outVW16_143_lt128
    (fun i ↦ by have := i.isLt; dsimp [wOrb143]; omega)
    (by decide)
theorem addOrbBody143_spec : ValidCleanRem 143 (143 - 128) addOrbBody143 ∧
    addOrbBody143.countTempAnd = 15 ∧ (∀ γ : BitAssignment 143, addOrbBody143.evalSign γ = 0)
    ∧ (∀ (γ : BitAssignment 143) (w : Wire 143), ¬ mutOrb143 w → addOrbBody143.evalBits γ w =
    γ w) ∧ (∀ γ : BitAssignment 143, cleanRem 143 (143 - 128) γ → bitsVal (fun j : Fin 16 ↦
    addOrbBody143.evalBits γ (wOrb143 j)) = (bitsVal (fun j : Fin 16 ↦ γ (outVW16_143 j)) +
    bitsVal (fun j : Fin 16 ↦ γ (wOrb143 j)) + (γ (tet16W143 0)).val) % 65536) := by
  obtain ⟨hv, hval⟩ := progAddMod2Pow_valid_and_val (M := 143) 15 128 (by decide)
    outVW16_143 wOrb143 (tet16W143 0) _ _ _ outVW16_143_injective wOrb143_injective _ _ _
  refine ⟨hv, progAddMod2Pow_countTempAnd 15 128 _ _ _ _ _ _ _ _ _ _, progAddMod2Pow_evalSign
    15 128 _ _ _ _ _ _ _ _ _ _, fun γ w hnm ↦ progAddMod2Pow_evalBits_other 15 128 _ _ _ _ _ _
    _ wOrb143_injective _ _ _ γ w (fun j h ↦ hnm ⟨j, h⟩), fun γ hγ ↦ hval γ hγ⟩
attribute [irreducible] addOrbBody143
def cXOrbAux : (k : ℕ) → k ≤ 16 → CliffProg 143
  | 0, _ => .nil
  | k + 1, hk => .seq (cXOrbAux k (by omega)) (.x (wOrb143 ⟨k, hk⟩))
def cXOrb143 : CliffProg 143 := cXOrbAux 16 le_rfl
theorem cXOrbAux_eval :
    ∀ (k : ℕ) (hk : k ≤ 16) (γ : BitAssignment 143) (w : Wire 143),
      (cXOrbAux k hk).eval γ w =
        if ∃ j : Fin 16, j.val < k ∧ w = wOrb143 j then γ w + 1 else γ w
  | 0, _, γ, w => by
      dsimp only [cXOrbAux, CliffProg.eval]
      rw [pkIteNeg (fun ⟨j, hj, _⟩ ↦ Nat.not_lt_zero j.val hj)]
  | k + 1, hk, γ, w => by
      dsimp only [cXOrbAux, CliffProg.eval]
      by_cases hw : w = wOrb143 ⟨k, hk⟩
      · subst hw
        have hnot_lt : ¬ ∃ j : Fin 16, j.val < k ∧ wOrb143 ⟨k, hk⟩ = wOrb143 j := by
          rintro ⟨j, hlt, heq⟩
          have hv := congrArg Fin.val (wOrb143_injective heq)
          dsimp at hv; omega
        have hex_succ : ∃ j : Fin 16, j.val < k + 1 ∧ wOrb143 ⟨k, hk⟩ = wOrb143 j :=
          ⟨⟨k, hk⟩, Nat.lt_succ_self k, rfl⟩
        rw [Function.update_self, cXOrbAux_eval k (by omega), pkIteNeg hnot_lt, pkItePos hex_succ]
      · rw [Function.update_of_ne hw, cXOrbAux_eval k (by omega)]
        by_cases hex : ∃ j : Fin 16, j.val < k ∧ w = wOrb143 j
        · obtain ⟨j, hlt, heq⟩ := hex
          rw [pkItePos ⟨j, hlt, heq⟩, pkItePos ⟨j, Nat.lt_succ_of_lt hlt, heq⟩]
        · have hnot_succ : ¬ ∃ j : Fin 16, j.val < k + 1 ∧ w = wOrb143 j := by
            rintro ⟨j, hlt, heq⟩
            by_cases hjk : j.val = k
            · exact hw (heq.trans (congrArg wOrb143 (Fin.ext hjk)))
            · exact hex ⟨j, by omega, heq⟩
          rw [pkIteNeg hex, pkIteNeg hnot_succ]
theorem cXOrb143_eval (γ : BitAssignment 143) (w : Wire 143) :
    cXOrb143.eval γ w = if mutOrb143 w then γ w + 1 else γ w := by
  dsimp only [cXOrb143]
  rw [cXOrbAux_eval 16 le_rfl]
  by_cases hm : mutOrb143 w
  · obtain ⟨j, rfl⟩ := hm
    rw [pkItePos ⟨j, j.isLt, rfl⟩, pkItePos ⟨j, rfl⟩]
  · rw [pkIteNeg (fun ⟨j, _, hj⟩ ↦ hm ⟨j, hj⟩), pkIteNeg hm]
attribute [local irreducible] cXOrb143
def subOrbBody143 : TempPhaseProg 143 :=
  .seq (.cliff cXOrb143) (.seq addOrbBody143 (.cliff cXOrb143))
theorem subOrbBody143_spec : ValidCleanRem 143 (143 - 128) subOrbBody143 ∧
    subOrbBody143.countTempAnd = 15 ∧ (∀ γ : BitAssignment 143, subOrbBody143.evalSign γ = 0)
    ∧ (∀ (γ : BitAssignment 143) (w : Wire 143), ¬ mutOrb143 w → subOrbBody143.evalBits γ w =
    γ w) := by
  obtain ⟨hvA, hcntA, hsgnA, hnmA, _⟩ := addOrbBody143_spec
  have hvSub : ValidCleanRem 143 (143 - 128) subOrbBody143 := by
    refine ⟨143 - 128, by decide, trivial,
      ⟨0, Nat.zero_le 143, hvA, trivial, fun _ _ _ hw ↦ absurd hw (by omega)⟩,
      fun γ hγ u hu ↦ ?_⟩
    dsimp only [TempPhaseProg.evalBits]
    rw [cXOrb143_eval, pkIteNeg (not_mutOrb143_of_ge28 (by omega))]
    exact hγ u hu
  refine ⟨hvSub, by simp [subOrbBody143, TempPhaseProg.countTempAnd, hcntA],
    fun γ ↦ by simp [subOrbBody143, TempPhaseProg.evalSign, hsgnA],
    fun γ w hnm ↦ ?_⟩
  dsimp only [subOrbBody143, TempPhaseProg.evalBits]
  rw [cXOrb143_eval, pkIteNeg hnm, hnmA _ w hnm, cXOrb143_eval, pkIteNeg hnm]
theorem subOrbBody143_eval_orb (γ : BitAssignment 143) (j : Fin 16) : subOrbBody143.evalBits γ
    (wOrb143 j) = addOrbBody143.evalBits (cXOrb143.eval γ) (wOrb143 j) + 1 := by
  dsimp only [subOrbBody143, TempPhaseProg.evalBits]
  rw [cXOrb143_eval, pkItePos ⟨j, rfl⟩]
attribute [local irreducible] subOrbBody143
theorem zmod2_not_val_add (x : ZMod 2) : (x + 1).val + x.val = 1 := by
  rcases bit_cases x with rfl | rfl <;> rfl
theorem bitsVal_not_add_self :
    ∀ (W : ℕ) (f : Fin W → ZMod 2),
      bitsVal (fun j ↦ f j + 1) + bitsVal f = 2 ^ W - 1
  | 0, _ => rfl
  | W + 1, f => by
      rw [bitsVal_succ_split (fun j ↦ f j + 1), bitsVal_succ_split f]
      have ih := bitsVal_not_add_self W (fun j ↦ f j.succ)
      have h0 := zmod2_not_val_add (f 0)
      have hpow : 2 ^ (W + 1) = 2 * 2 ^ W := by ring
      have hpos : 1 ≤ 2 ^ W := Nat.one_le_two_pow
      omega
theorem mod65536_sub_cancel (b d : ℕ) (hb : b < 65536) :
    65535 - (d + (65535 - (d + b) % 65536)) % 65536 = b := by
  have hmod : (d + b) % 65536 < 65536 := Nat.mod_lt _ (by decide)
  have hdiv : d + b = 65536 * ((d + b) / 65536) + (d + b) % 65536 :=
    (Nat.div_add_mod (d + b) 65536).symm
  have heq : d + (65535 - (d + b) % 65536) =
      (65535 - b) + 65536 * ((d + b) / 65536) := by omega
  rw [heq, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
  omega
theorem subOrbBody143_addOrbBody143_cancel (γ₁ γ₂ : BitAssignment 143)
    (hcl₁ : cleanRem 143 (143 - 128) γ₁) (hcl₂ : cleanRem 143 (143 - 128) γ₂) (hOrb : ∀ j :
    Fin 16, γ₂ (wOrb143 j) = addOrbBody143.evalBits γ₁ (wOrb143 j))
    (hOut : ∀ j : Fin 16, γ₂ (outVW16_143 j) = γ₁ (outVW16_143 j))
    (hCin : γ₂ (tet16W143 0) = γ₁ (tet16W143 0)) : ∀ j : Fin 16, subOrbBody143.evalBits γ₂
    (wOrb143 j) = γ₁ (wOrb143 j) := by
  obtain ⟨_, _, _, hnmA, hvalA⟩ := addOrbBody143_spec
  let δ₂ := cXOrb143.eval γ₂
  have hclδ₂ : cleanRem 143 (143 - 128) δ₂ := fun u hu ↦ by
    dsimp only [δ₂]
    rw [cXOrb143_eval, pkIteNeg (not_mutOrb143_of_ge28 (by omega))]
    exact hcl₂ u hu
  have hδ₂_out : (fun j : Fin 16 ↦ δ₂ (outVW16_143 j)) = fun j ↦ γ₁ (outVW16_143 j) := by
    funext j; dsimp only [δ₂]
    rw [cXOrb143_eval, pkIteNeg (not_mutOrb143_of_ge28 (outVW16_143_ge28 j)), hOut j]
  have hδ₂_cin : δ₂ (tet16W143 0) = γ₁ (tet16W143 0) := by
    dsimp only [δ₂]
    rw [cXOrb143_eval, pkIteNeg (not_mutOrb143_of_ge28 (by decide)), hCin]
  let f₀ : Fin 16 → ZMod 2 := fun j ↦ γ₁ (wOrb143 j)
  let f₁ : Fin 16 → ZMod 2 := fun j ↦ addOrbBody143.evalBits γ₁ (wOrb143 j)
  let f₃ : Fin 16 → ZMod 2 := fun j ↦ addOrbBody143.evalBits δ₂ (wOrb143 j)
  let f₄ : Fin 16 → ZMod 2 := fun j ↦ subOrbBody143.evalBits γ₂ (wOrb143 j)
  have hδ₂_orb : (fun j : Fin 16 ↦ δ₂ (wOrb143 j)) = fun j ↦ f₁ j + 1 := by
    funext j; dsimp only [δ₂, f₁]
    rw [cXOrb143_eval, pkItePos ⟨j, rfl⟩, hOrb j]
  have hf₄_eq : f₄ = fun j ↦ f₃ j + 1 := funext fun j ↦ subOrbBody143_eval_orb γ₂ j
  set b := bitsVal f₀
  set d := bitsVal (fun j : Fin 16 ↦ γ₁ (outVW16_143 j)) + (γ₁ (tet16W143 0)).val
  have hb_lt : b < 65536 := bitsVal_lt_two_pow f₀
  have hf₁_val : bitsVal f₁ = (d + b) % 65536 := by
    dsimp only [f₁, f₀]
    rw [hvalA γ₁ hcl₁, Nat.add_right_comm]
  have hδ₂_val : bitsVal (fun j : Fin 16 ↦ δ₂ (wOrb143 j)) = 65535 - (d + b) % 65536 := by
    rw [hδ₂_orb]
    have hnot := bitsVal_not_add_self 16 f₁
    have h216 : (2 : ℕ) ^ 16 - 1 = 65535 := rfl
    rw [h216, hf₁_val] at hnot
    omega
  have hf₃_val : bitsVal f₃ = (d + (65535 - (d + b) % 65536)) % 65536 := by
    dsimp only [f₃]
    rw [hvalA δ₂ hclδ₂, hδ₂_out, hδ₂_cin, hδ₂_val, Nat.add_right_comm]
  have hf₄_val : bitsVal f₄ = b := by
    rw [hf₄_eq]
    have hnot := bitsVal_not_add_self 16 f₃
    have h216 : (2 : ℕ) ^ 16 - 1 = 65535 := rfl
    have hlt3 : bitsVal f₃ < 65536 := bitsVal_lt_two_pow f₃
    have h4 : bitsVal (fun j ↦ f₃ j + 1) = 65535 - bitsVal f₃ := by omega
    rw [h4, hf₃_val]
    exact mod65536_sub_cancel b d hb_lt
  have hfn_eq : f₄ = f₀ := bitsVal_injective hf₄_val
  exact congrFun hfn_eq
def rCombTail143 {n mClean : ℕ} (hmClean : 138 ≤ mClean) (rOrbit16 : QRegister 16 n)
    (rClean : QRegister mClean n) (hOW : rOrbit16.DisjointWires rClean) : QRegister 143 n :=
  let rT28 := rTarget28 hmClean rOrbit16 rClean hOW
  let rScr115 := rClean.slice 12 115 (by omega)
  have hH115 : (rHold12 hmClean rClean).DisjointWires rScr115 :=
    pk_slice_disjoint rClean (by omega) (by omega) (Or.inl (by omega))
  have hO115 : rOrbit16.DisjointWires rScr115 :=
    QRegister.disjoint_iff.mpr fun i j heq ↦ hOW.ne i ⟨12 + j.val, by omega⟩ heq
  rT28.concat rScr115 (pk_disj_concat_left _ hH115 hO115)
theorem rCombTail143_pack {n mClean : ℕ} (hmClean : 138 ≤ mClean) (rOrbit16 : QRegister 16 n)
    (rClean : QRegister mClean n) (hOW : rOrbit16.DisjointWires rClean) (k : Fin 12) :
    rCombTail143 hmClean rOrbit16 rClean hOW (wPack143 k) = rHold12 hmClean rClean k := by
  have he : (wPack143 k : Fin ((12 + 16) + 115)) = Fin.castAdd 115 (Fin.castAdd 16 k) := rfl
  dsimp only [rCombTail143, rTarget28]
  rw [he, QRegister.concat_apply_left, QRegister.concat_apply_left]
theorem rCombTail143_orb {n mClean : ℕ} (hmClean : 138 ≤ mClean) (rOrbit16 : QRegister 16 n)
    (rClean : QRegister mClean n) (hOW : rOrbit16.DisjointWires rClean) (k : Fin 16) :
    rCombTail143 hmClean rOrbit16 rClean hOW (wOrb143 k) = rOrbit16 k := by
  have he : (wOrb143 k : Fin ((12 + 16) + 115)) = Fin.castAdd 115 (Fin.natAdd 12 k) := rfl
  dsimp only [rCombTail143, rTarget28]
  rw [he, QRegister.concat_apply_left, QRegister.concat_apply_right]
theorem rCombTail143_scr {n mClean : ℕ} (hmClean : 138 ≤ mClean)
    (rOrbit16 : QRegister 16 n) (rClean : QRegister mClean n)
    (hOW : rOrbit16.DisjointWires rClean) (j : Fin 115) :
    rCombTail143 hmClean rOrbit16 rClean hOW ⟨28 + j.val, by omega⟩ =
      rCleanMid12 hmClean rClean ⟨j.val, by omega⟩ := by
  have he : (⟨28 + j.val, by omega⟩ : Fin ((12 + 16) + 115)) = Fin.natAdd 28 j :=
    Fin.ext rfl
  dsimp only [rCombTail143, rTarget28, rCleanMid12]
  rw [he, QRegister.concat_apply_right, QRegister.slice_apply, QRegister.slice_apply]
theorem cleanRem115_rCombTail143 {n mClean : ℕ} (hmClean : 138 ≤ mClean)
    (rOrbit16 : QRegister 16 n) (rClean : QRegister mClean n)
    (hOW : rOrbit16.DisjointWires rClean) {β : BitAssignment n}
    (hs : S_mid12 hmClean rClean β) :
    cleanRem 143 115 (fun u ↦ β (rCombTail143 hmClean rOrbit16 rClean hOW u)) := fun u hu ↦ by
  let j : Fin 115 := ⟨u.val - 28, by omega⟩
  have hu_eq : u = ⟨28 + j.val, by omega⟩ := by ext; dsimp [j]; omega
  change β (rCombTail143 hmClean rOrbit16 rClean hOW u) = 0
  rw [hu_eq, rCombTail143_scr hmClean rOrbit16 rClean hOW j]
  exact hs ⟨j.val, by omega⟩
end OrbitSandPacked12
end
end Leaf2RedirectAndHeldOrbit

noncomputable section Leaf2MidK6WState2350Bridge

noncomputable section
set_option backward.isDefEq.respectTransparency true
namespace MidK6WState2350
section ConfigMidK6WState2350
set_option maxRecDepth 4096
set_option exponentiation.threshold 256
local instance (priority := 1000000) instNeZeroTwoPowWState (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩
open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt HermitianMat
open scoped Matrix ComplexOrder MatrixOrder BigOperators Circuit.Notation
open SpecsAux SpecsAux.SpecMirror
open OctahedralOrbit
open Dyadic128CoulombMath
open Dyadic128OrbitTableCert
open MeasureBranchHadamardSem (bit_cases)
open PosSlots24BranchConcrete
open BchCubeDecoder hiding ket_diagonalSignUnitaryN
open StreamingBchComparator
open PosSlots24SemanticBridge
open PrunedQromLookup
open PosSlots24PartnerMuxZeroT123 hiding sandPhase18
open PosSlots24SpectatorPrunedPhase
open PosSlots24SpectatorPrunedPhase.MidK6Sub252
open MultiBankWStateRouter
open MidKickSub33 MidK6Sub126
open OrbitSandPacked18
open MidKickOpt MidK6UnbufOpt
attribute [local irreducible]
  k6SuperRow w128OrbitBiasedQ30 k6ReconTop6BitBool pos24TailMag30 pos24TailSign k6BitNat
  k6SubGatesPalBit k6Pal24Bit k6P0Bit k6P1Bit k6_oneHot4Val cKickZeroSub34
  cKickZeroSubSingle dKickZeroSubSingleDyn cKickZeroSub46Opt dKickZeroSub46OptDyn
  cKickZeroSub37Opt dKickZeroSub37OptDyn cKickZeroSub34Opt dKickZeroSub34OptDyn
  phaseLookupPrunedCircuit hadamardReg p2t_cPhaseMuxCol64 k6_cOneHot4Raw
  k6_cPhaseMux4All6Raw k6_cXorDiffTop6Raw k6_cCzCol64Raw k6_cCzSweep27Raw mkState
  recoverInit K6StageSpec DynCircuitExt.substToffoliCircuit signOf
noncomputable def p2t_withOneHot64SumCompDyn_wstate_loc {Var : Type} {n : ℕ} (v : Var)
    (rSel6 : QRegister 6 n) (rOH64 : QRegister 64 n) (qEnc : Wire n)
    (_hSelOH : rSel6.DisjointWires rOH64) (dInner : DynamicCircuit Var n) : DynamicCircuit Var
    n := .seq (wStateComputeUncondPow2 5 v rSel6.wires rOH64.wires qEnc) (.seq dInner
    (wStateUncomputeUncondPow2 5 v rSel6.wires rOH64.wires))
@[simp]
theorem p2t_count_withOneHot64SumCompDyn_wstate_loc_toff {Var : Type} {n : ℕ} (v : Var)
    (rSel6 : QRegister 6 n) (rOH64 : QRegister 64 n) (qEnc : Wire n)
    (hSelOH : rSel6.DisjointWires rOH64) (dInner : DynamicCircuit Var n) :
    (p2t_withOneHot64SumCompDyn_wstate_loc v rSel6 rOH64 qEnc hSelOH dInner).count
      PrimitiveGate.TOFF =
      dInner.count PrimitiveGate.TOFF := by
  obtain ⟨_, fc⟩ := count_wStateComputeUncondPow2 5 v rSel6.wires rOH64.wires qEnc
  obtain ⟨_, fu⟩ := count_wStateUncomputeUncondPow2 5 v rSel6.wires rOH64.wires
  simp [p2t_withOneHot64SumCompDyn_wstate_loc, DynamicCircuit.count, fc, fu]
@[simp] theorem p2t_count_withOneHot64SumCompDyn_wstate_loc_t {Var : Type} {n : ℕ} (v : Var)
    (rSel6 : QRegister 6 n) (rOH64 : QRegister 64 n) (qEnc : Wire n)
    (hSelOH : rSel6.DisjointWires rOH64) (dInner : DynamicCircuit Var n) :
    (p2t_withOneHot64SumCompDyn_wstate_loc v rSel6 rOH64 qEnc hSelOH dInner).count PrimitiveGate.T =
      124 + dInner.count PrimitiveGate.T := by
  obtain ⟨tc, _⟩ := count_wStateComputeUncondPow2 5 v rSel6.wires rOH64.wires qEnc
  obtain ⟨tu, _⟩ := count_wStateUncomputeUncondPow2 5 v rSel6.wires rOH64.wires
  dsimp only [p2t_withOneHot64SumCompDyn_wstate_loc, DynamicCircuit.count]
  rw [tc, tu]
  omega
theorem idxValD_rSel6_eq {n : ℕ} (rSel6 : QRegister 6 n) (γ : BitAssignment n) :
    idxValD rSel6.wires γ = (localIdx rSel6 γ).val := by
  have hi : ∀ d : Fin 6, (if γ (rSel6 d) = 1 then 1 else 0) = (γ (rSel6 d)).val := fun d ↦ by
    rcases bit_cases (γ (rSel6 d)) with hbit | hbit <;> simp [hbit]
  have hmul : ∀ (d : Fin 6) (m : ℕ),
      (if γ (rSel6.wires d) = 1 then m else 0) = (γ (rSel6 d)).val * m := fun d m ↦ by
    rw [← hi d]
    split_ifs <;> omega
  rw [localIdx_val]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero, Fin.val_succ]
  dsimp only [idxValD, idxValPrefix]
  simp only [hmul]
  have e0 : (0 : Fin 6) = ⟨0, by decide⟩ := rfl
  have e1 : (Fin.succ 0 : Fin 6) = ⟨1, by decide⟩ := rfl
  have e2 : ((Fin.succ 0).succ : Fin 6) = ⟨2, by decide⟩ := rfl
  have e3 : ((Fin.succ 0).succ.succ : Fin 6) = ⟨3, by decide⟩ := rfl
  have e4 : ((Fin.succ 0).succ.succ.succ : Fin 6) = ⟨4, by decide⟩ := rfl
  have e5 : ((Fin.succ 0).succ.succ.succ.succ : Fin 6) = ⟨5, by decide⟩ := rfl
  rw [e0, e1, e2, e3, e4, e5]
  omega
open Classical in
theorem p2t_withOneHot64SumCompDyn_wstate_loc_diag {Var : Type} [Fintype Var]
    [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)] (v : Var) (rSel6 : QRegister 6 n)
    (rOH64 : QRegister 64 n) (qEnc : Wire n) (hSelOH : rSel6.DisjointWires rOH64)
    (hSelq : ∀ a : Fin 6, rSel6 a ≠ qEnc) (hOHq : ∀ j : Fin 64, rOH64 j ≠ qEnc)
    {W : Wire n → Prop} (hWOH : ∀ j : Fin 64, W (rOH64 j)) {U_target : Unitary (2 ^ n)}
    (hDiag : p2t_DiagIndepOf W U_target) {S_ext : BitAssignment n → Prop} (hExtIndep : ∀ β₁ β₂
    : BitAssignment n, (∀ w : Wire n, w ∉ Set.range rOH64.wires → β₁ w = β₂ w) → S_ext β₁ →
    S_ext β₂) (hExtQ0 : ∀ β : BitAssignment n, S_ext β → β qEnc = 0)
    {dInner : DynamicCircuit Var n} (hdInner : p2t_RealizesConstCleanUnitary (p2t_ketPredProj
    (fun γ ↦ S_ext γ ∧ ∀ j : Fin 64, γ (rOH64 j) = if j = localIdx rSel6 γ then 1 else 0))
    dInner U_target) : p2t_RealizesConstCleanUnitary
    (p2t_ketPredProj (fun β ↦ S_ext β ∧ ∀ j : Fin 64, β (rOH64 j) = 0))
    (p2t_withOneHot64SumCompDyn_wstate_loc v rSel6 rOH64 qEnc hSelOH dInner) U_target := by
  classical
  let mket : BitAssignment n → Fin (2 ^ n) → ℂ := MeasureBranchHadamardSem.ket
  obtain ⟨φ, hφKetP, hφIndep⟩ := hDiag
  have hφKet : ∀ β : BitAssignment n, U_target.1.mulVec (mket β) = φ β • mket β := fun β ↦ by
    dsimp only [mket]; rw [mbh_ket_eq_ket, hφKetP β]
  let S_in : BitAssignment n → Prop := fun β ↦ S_ext β ∧ ∀ j : Fin 64, β (rOH64 j) = 0
  let S_mid : BitAssignment n → Prop := fun γ ↦
    S_ext γ ∧ ∀ j : Fin 64, γ (rOH64 j) = if j = localIdx rSel6 γ then 1 else 0
  let P_in := p2t_ketPredProj S_in
  let P_mid := p2t_ketPredProj S_mid
  have hPinH : P_inᴴ = P_in := p2t_ketPredProj_conjTranspose S_in
  have hPmidH : P_midᴴ = P_mid := p2t_ketPredProj_conjTranspose S_mid
  have hPinKet : ∀ β, P_in.mulVec (mket β) = if S_in β then mket β else 0 := fun β ↦ by
    dsimp only [mket]; rw [mbh_ket_eq_ket, p2t_ketPredProj_mul_ket]
  have hPmidKet : ∀ γ, P_mid.mulVec (mket γ) = if S_mid γ then mket γ else 0 := fun γ ↦ by
    dsimp only [mket]; rw [mbh_ket_eq_ket, p2t_ketPredProj_mul_ket]
  have hd : WUncondDisjProp rSel6.wires rOH64.wires qEnc :=
    ⟨fun d j ↦ hSelOH.ne d j, hSelq, fun _ _ hij ↦ rOH64.wires.injective.ne hij, hOHq⟩
  have hSuppIn : SupportedOn (ValidWUncondIn rOH64.wires qEnc) P_in := fun A B hAB ↦ by
    apply MeasureBranchHadamardSem.matrix_ext_ket; intro β
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hPinKet]
    by_cases hs : S_in β
    · rw [ite_eq_left hs]
      exact hAB β ⟨hs.2, hExtQ0 β hs.1⟩
    · simp only [ite_eq_right hs, Matrix.mulVec_zero]
  have hSuppOut : SupportedOn (ValidWUncondClean rOH64.wires) (U_target.1 * P_in) := fun A B hAB ↦
    by
    apply MeasureBranchHadamardSem.matrix_ext_ket; intro β
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      ← Matrix.mulVec_mulVec, hPinKet]
    by_cases hs : S_in β
    · rw [ite_eq_left hs, hφKet β, Matrix.mulVec_smul, Matrix.mulVec_smul, hAB β hs.2]
    · simp only [ite_eq_right hs, Matrix.mulVec_zero]
  have sComp := subspaceStep_wStateComputeUncondPow2 5 v rSel6.wires rOH64.wires qEnc hd P_in
    hSuppIn
  have sUnc := subspaceStep_wStateUncomputeUncondPow2 5 v rSel6.wires rOH64.wires ⟨hd.1, hd.2.2.1⟩
    (U_target.1 * P_in) hSuppOut
  have sInnerRaw : SubspaceStep P_mid (U_target.1 * P_mid) dInner := fun M ↦ by
    obtain ⟨N, hWp⟩ := hdInner.1 M
    refine ⟨N, hWp, ?_⟩
    have h0 := hdInner.2 M (fun _ ↦ 0)
    rw [congrFun hWp (fun _ ↦ 0)] at h0
    simpa only [Matrix.conjTranspose_mul, hPmidH, Matrix.mul_assoc] using h0.symm
  let U_oh := uOneHotUncond rSel6.wires rOH64.wires hd.1
  have hMidAbsorb : P_mid * (U_oh.1 * P_in) = U_oh.1 * P_in := by
    apply MeasureBranchHadamardSem.matrix_ext_ket; intro β
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hPinKet]
    by_cases hs : S_in β
    · rw [ite_eq_left hs, uOneHotUncond_mulVec_ket]
      let jStar : Fin 64 := ⟨idxValD rSel6.wires β, idxValD_lt_two_pow rSel6.wires β⟩
      have hjStar : jStar = localIdx rSel6 β := Fin.ext (idxValD_rSel6_eq rSel6 β)
      change P_mid.mulVec (mket (Function.update β (rOH64 jStar) (β (rOH64 jStar) + 1))) =
        mket (Function.update β (rOH64 jStar) (β (rOH64 jStar) + 1))
      rw [hjStar, hs.2 (localIdx rSel6 β), zero_add, hPmidKet]
      let γ := Function.update β (rOH64 (localIdx rSel6 β)) 1
      have hLocEq : localIdx rSel6 γ = localIdx rSel6 β := by
        apply Fin.ext
        rw [← idxValD_rSel6_eq, ← idxValD_rSel6_eq]
        exact idxValD_congr rSel6.wires fun d ↦
          Function.update_of_ne (hSelOH.ne d (localIdx rSel6 β)) 1 β
      have hSmid : S_mid γ := by
        refine ⟨hExtIndep β γ (fun w hw ↦ ?_) hs.1, fun j ↦ ?_⟩
        · exact (Function.update_of_ne (fun h ↦ hw ⟨localIdx rSel6 β, h.symm⟩) 1 β).symm
        · dsimp only [γ]
          rw [hLocEq]
          by_cases hj : j = localIdx rSel6 β
          · subst hj; rw [ite_eq_left rfl]; exact Function.update_self _ 1 β
          · rw [ite_eq_right hj, Function.update_of_ne (rOH64.wires.injective.ne hj), hs.2 j]
      exact ite_eq_left hSmid
    · simp only [ite_eq_right hs, Matrix.mulVec_zero]
  have hMidComm : U_target.1 * (U_oh.1 * P_in) = U_oh.1 * (U_target.1 * P_in) := by
    apply MeasureBranchHadamardSem.matrix_ext_ket; intro β
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      ← Matrix.mulVec_mulVec, hPinKet]
    by_cases hs : S_in β
    · rw [ite_eq_left hs, uOneHotUncond_mulVec_ket, hφKet, hφKet β, Matrix.mulVec_smul,
        uOneHotUncond_mulVec_ket, hφIndep β _ _ (hWOH _)]
    · simp only [ite_eq_right hs, Matrix.mulVec_zero]
  have sMid : SubspaceStep (U_oh.1 * P_in) (U_oh.1 * (U_target.1 * P_in)) dInner :=
    subspaceStep_congr_in hMidAbsorb.symm
      (subspaceStep_congr_out
        (by simpa only [Matrix.mul_assoc] using subspaceStep_mul_right (U_oh.1 * P_in) sInnerRaw)
        (by rw [hMidAbsorb, hMidComm]))
  have sAll : SubspaceStep P_in (U_target.1 * P_in) (p2t_withOneHot64SumCompDyn_wstate_loc v
      rSel6 rOH64 qEnc hSelOH dInner) := sComp.seq (sMid.seq sUnc)
  refine ⟨fun M ↦ ⟨(sAll M).choose, (sAll M).choose_spec.1⟩, fun M σ ↦ ?_⟩
  obtain ⟨N, hWp, hEq⟩ := sAll M
  rw [congrFun hWp σ]
  simpa only [Matrix.conjTranspose_mul, hPinH, Matrix.mul_assoc] using hEq.symm
attribute [local irreducible] p2t_withOneHot64SumCompDyn_wstate_loc
theorem l26_wTreeRoutingT_5_749 :
    l26_wTreeRoutingT 5 9 512 + l26_wTreeRoutingT 5 9 237 = 1782 := by decide
/-- All `(30 - B) + (mClean - 117)` clean wires `rClean[64 .. 64 + (30 - B)) ++ rClean[117 ..
mClean)`
available at `|0⟩` during Stage 3 (`vClean2`, in addition to `wPar = rClean[115]` and `qEnc =
rClean[116]`). -/
abbrev rPoolAllStage3 {n mClean : ℕ} (B : ℕ) (hB27 : B ≤ 27) (hmClean : 126 ≤ mClean)
    (rClean : QRegister mClean n) : QRegister ((30 - B) + (mClean - 117)) n :=
    (rClean.slice 64 (30 - B) (by omega)).concat (rClean.slice 117 (mClean - 117) (by omega))
    (slice_disjoint_slice rClean 64 (30 - B) 117 (mClean - 117) (by omega) (by omega)
    (Or.inl (by omega)))
theorem rPoolAllStage3_index {n mClean : ℕ} (B : ℕ) (hB27 : B ≤ 27) (hmClean : 126 ≤ mClean)
    (rClean : QRegister mClean n) (s : Fin ((30 - B) + (mClean - 117))) :
    ∃ k : Fin mClean,
      ((64 ≤ k.val ∧ k.val < 64 + (30 - B)) ∨ 117 ≤ k.val) ∧
      rPoolAllStage3 B hB27 hmClean rClean s = rClean k := by
  by_cases hs : s.val < 30 - B
  · have hsEq : s = Fin.castAdd (mClean - 117) ⟨s.val, hs⟩ := Fin.ext rfl
    refine ⟨⟨64 + s.val, by omega⟩, Or.inl ⟨by dsimp; omega, by dsimp; omega⟩, ?_⟩
    have h1 := QRegister.concat_apply_left (rClean.slice 64 (30 - B) (by omega))
        (rClean.slice 117 (mClean - 117) (by omega)) (slice_disjoint_slice rClean 64 (30 -
        B) 117 (mClean - 117) (by omega) (by omega) (Or.inl (by omega))) ⟨s.val, hs⟩
    rw [← hsEq, QRegister.slice_apply] at h1
    exact h1
  · have hsEq : s = Fin.natAdd (30 - B) ⟨s.val - (30 - B), by omega⟩ := by
      ext; dsimp [Fin.natAdd]; omega
    refine ⟨⟨117 + (s.val - (30 - B)), by omega⟩, Or.inr (by dsimp; omega), ?_⟩
    have h1 := QRegister.concat_apply_right (rClean.slice 64 (30 - B) (by omega))
      (rClean.slice 117 (mClean - 117) (by omega))
      (slice_disjoint_slice rClean 64 (30 - B) 117 (mClean - 117)
        (by omega) (by omega) (Or.inl (by omega)))
      ⟨s.val - (30 - B), by omega⟩
    rw [← hsEq, QRegister.slice_apply] at h1
    exact h1
/-- Generic Stages 5b, 5c, 5d, 6 (`dKick`), 7, and 8 (`dFix`) at `H = 0`. -/
noncomputable def dPost4dWStateGenOf {Var : Type} {n mClean : ℕ} (B : ℕ) (hB1 : 1 ≤ B)
    (hB27 : B ≤ 27) (hmClean : 126 ≤ mClean) (v : Var) (rClean : QRegister mClean n)
    (dKick : DynamicCircuit Var n) (dFix : (Fin 27 → Bool) → (Fin 30 → Bool) → (Fin (B + 1) →
    Bool) → DynamicCircuit Var n) (fStream : Fin 27 → Bool) : DynamicCircuit Var n :=
  let rP2 := rP2Of hmClean rClean
  let rOH4 := rOH4Of hmClean rClean
  let rPal18 := rPal18Of hmClean rClean
  let rDiff6 := rDiff6Of hmClean rClean
  let rOutBTop6 := rOutBTop6Of hmClean rClean
  let rOutTop := rOutTopOf B hB1 hB27 hmClean rClean
  let rMeas5c30 := rMeas5c30Of hmClean rClean
  let hPOH4 : rP2.DisjointWires rOH4 := disj_rP2_rOH4 hmClean rClean
  let hD0NotOH4 : rDiff6 0 ∉ (k6_cOneHot4Raw rP2 rOH4 hPOH4).support :=
    rDiff6_zero_not_mem_oneHot4 hmClean rClean hPOH4
  let hOHD : rOH4.DisjointWires rDiff6 := disj_rOH4_rDiff6 hmClean rClean
  let hPalD : rPal18.DisjointWires rDiff6 := disj_rPal18_rDiff6 hmClean rClean
  let hDT : rDiff6.DisjointWires rOutBTop6 := disj_rDiff6_rOutBTop6 hmClean rClean
  .seq
    (DynCircuitExt.substToffoliCircuit v (rDiff6 0)
      (k6_cOneHot4Raw rP2 rOH4 hPOH4) hD0NotOH4)
    (.seq
      (.circuit
        (k6_cPhaseMux4All6Raw rOH4 rPal18 rDiff6 hOHD hPalD 6 (le_refl 6) ;;ᶜ
         k6_cXorDiffTop6Raw rDiff6 rOutBTop6 hDT 6 (le_refl 6)))
      (DynCircuitExt.measureXResetAndBranch v 30 rMeas5c30 fun f5c ↦
        .seq
          dKick
          (DynCircuitExt.measureXResetAndBranch v (B + 1) rOutTop fun f7Top ↦
            dFix fStream f5c f7Top)))
/-- Generic Stage-4 streaming post-mux continuing into `dPost4dWStateGenOf`. -/
noncomputable def dStreamRemWStateGenDyn {Var : Type} {n mClean : ℕ}
    (B : ℕ) (hB1 : 1 ≤ B) (hB27 : B ≤ 27) (hmClean : 126 ≤ mClean) (v : Var)
    (rCore : QRegister posCoreWires n) (rClean : QRegister mClean n)
    (hCC : rCore.DisjointWires rClean)
    (dKick : DynamicCircuit Var n)
    (dFix : (Fin 27 → Bool) → (Fin 30 → Bool) → (Fin (B + 1) → Bool) → DynamicCircuit Var n) :
    (fAcc : Fin 27 → Bool) → (rem : ℕ) → (hrem : rem ≤ 27) → DynamicCircuit Var n
  | fAcc, 0, _ =>
      dPost4dWStateGenOf B hB1 hB27 hmClean v rClean dKick dFix fAcc
  | fAcc, rem + 1, hrem =>
      let idx : ℕ := 27 - (rem + 1)
      let col : Fin 27 := ⟨idx, sub_succ_lt_27 rem⟩
      if k6ActiveCol B col then
        let wStream := wStreamOf hmClean rClean
        let wParity3 := wParity3Of hmClean rClean
        let rOH64 := rOH64Of hmClean rClean
        let rTarget27 := rTarget27Of hmClean rClean
        let rDirty := rDirtyOf rCore
        .seq
          (.circuit (p2t_cPhaseMuxCol64 0 wStream wParity3 rOH64 (k6_rCol64 rDirty col)
            (wParity3_ne_wStream hmClean rClean)
            (rOH64_ne_wStream hmClean rClean)
            (rCol64_ne_wStream hmClean rCore rClean hCC col)
            (rOH64_ne_wParity3 hmClean rClean)))
          (.seq
            (.circuit (Circuit.CNOT wStream (rTarget27 col)
              (wStream_ne_rTarget27 hmClean rClean col)))
            (DynCircuitExt.measureXResetAndBranch v 1 (QRegister.singleton wStream) fun fBit ↦
              dStreamRemWStateGenDyn B hB1 hB27 hmClean v rCore rClean hCC dKick dFix
                (Function.update fAcc col (fBit 0)) rem (Nat.le_of_succ_le hrem)))
      else
        dStreamRemWStateGenDyn B hB1 hB27 hmClean v rCore rClean hCC dKick dFix
          fAcc rem (Nat.le_of_succ_le hrem)
/-- Generic inner unbuffered `MidK6` pipeline parameterized by `dLoad`, `dKick`, and `dFix`. -/
noncomputable def dInnerWStateGenOf {Var : Type} {n mClean : ℕ} (B : ℕ) (hB1 : 1 ≤ B)
    (hB27 : B ≤ 27) (hmClean : 126 ≤ mClean) (v : Var) (rCore : QRegister posCoreWires n)
    (rClean : QRegister mClean n) (hCC : rCore.DisjointWires rClean)
    (dLoad : DynamicCircuit Var n) (dKick : DynamicCircuit Var n) (dFix : (Fin 27 → Bool) →
    (Fin 30 → Bool) → (Fin (B + 1) → Bool) → DynamicCircuit Var n) : DynamicCircuit Var n :=
  let rOH64 := rOH64Of hmClean rClean
  let rTarget27 := rTarget27Of hmClean rClean
  let wParity2 := wParity2Of hmClean rClean
  let rDirty := rDirtyOf rCore
  let hP2Out : ∀ m : Fin 27, wParity2 ≠ rTarget27 m := wStream_ne_rTarget27 hmClean rClean
  let hOHOut : rOH64.DisjointWires rTarget27 := disj_rOH64_rTarget27 hmClean rClean
  let hBufOut : rDirty.DisjointWires rTarget27 := k6_disjoint_concat_right
      ((hCC.compose_left _).compose_right _) ((hCC.compose_left _).compose_right _) _
  let hOHP2 : ∀ sl : Fin 64, rOH64 sl ≠ wParity2 := rOH64_ne_wStream hmClean rClean
  .seq
    (.circuit (cPreMuxRaw B wParity2 rOH64 rTarget27 rDirty
      hP2Out hOHOut hBufOut hOHP2 27 (le_refl 27)))
    (.seq
      dLoad
      (dStreamRemWStateGenDyn B hB1 hB27 hmClean v rCore rClean hCC dKick dFix
        (fun _ ↦ false) 27 (le_refl 27)))
/-- Generic unsealed W-state `MidK6` dynamic circuit wrapped with
`p2t_withOneHot64SumCompDyn_wstate_loc` (`124 T`). -/
noncomputable def dMidK6WStateGenDynRaw {Var : Type} {n mClean : ℕ} (B : ℕ) (hB1 : 1 ≤ B)
    (hB27 : B ≤ 27) (hmClean : 126 ≤ mClean) (v : Var) (rCore : QRegister posCoreWires n)
    (rOrbit16 : QRegister 16 n) (rClean : QRegister mClean n)
    (hCC : rCore.DisjointWires rClean) (hOC : rOrbit16.DisjointWires rClean)
    (dLoad : DynamicCircuit Var n) (dKick : DynamicCircuit Var n) (dFix : (Fin 27 → Bool) →
    (Fin 30 → Bool) → (Fin (B + 1) → Bool) → DynamicCircuit Var n) : DynamicCircuit Var n :=
  p2t_withOneHot64SumCompDyn_wstate_loc v
    (k6_rSel6Of rOrbit16) (rOH64Of hmClean rClean) (rClean ⟨64, by omega⟩)
    ((hOC.compose_left _).compose_right _)
    (dInnerWStateGenOf B hB1 hB27 hmClean v rCore rClean hCC dLoad dKick dFix)
/-- Generic sealed W-state `MidK6` dynamic circuit parameterized by `dLoad`, `dKick`, and `dFix`. -/
noncomputable def dMidK6WStateGenDyn {Var : Type} {n mClean : ℕ} (B : ℕ) (hB1 : 1 ≤ B)
    (hB27 : B ≤ 27) (hmClean : 126 ≤ mClean) (v : Var) (rCore : QRegister posCoreWires n)
    (rOrbit16 : QRegister 16 n) (rClean : QRegister mClean n)
    (hCC : rCore.DisjointWires rClean) (hOC : rOrbit16.DisjointWires rClean)
    (dLoad : DynamicCircuit Var n) (dKick : DynamicCircuit Var n) (dFix : (Fin 27 → Bool) →
    (Fin 30 → Bool) → (Fin (B + 1) → Bool) → DynamicCircuit Var n) : DynamicCircuit Var n :=
    p2t_lockVal (dMidK6WStateGenDynRaw B hB1 hB27 hmClean v rCore rOrbit16 rClean hCC hOC
    dLoad dKick dFix)
theorem count_dPost4dWStateGenOf_toff {Var : Type} {n mClean : ℕ} (B : ℕ) (hB1 : 1 ≤ B)
    (hB27 : B ≤ 27) (hmClean : 126 ≤ mClean) (v : Var) (rClean : QRegister mClean n)
    (dKick : DynamicCircuit Var n) (hKickToff : dKick.count PrimitiveGate.TOFF = 0) (dFix :
    (Fin 27 → Bool) → (Fin 30 → Bool) → (Fin (B + 1) → Bool) → DynamicCircuit Var n) (hFixToff
    : ∀ fS f5c f7, (dFix fS f5c f7).count PrimitiveGate.TOFF = 0) (fStream : Fin 27 → Bool) :
    (dPost4dWStateGenOf B hB1 hB27 hmClean v rClean dKick dFix fStream).count
    PrimitiveGate.TOFF = 0 := by
  dsimp only [dPost4dWStateGenOf]
  simp only [DynamicCircuit.count, k6_count_substToffoliCircuit_toff,
    Circuit.count_seq, k6_cPhaseMux4All6Raw_count_toff, k6_cXorDiffTop6Raw_count_toff, zero_add]
  rw [← Nat.le_zero]
  refine DynCircuitExt.count_measureXResetAndBranch_TOFF_le v 30 _ _ 0 fun f5c ↦ ?_
  simp only [DynamicCircuit.count, hKickToff, zero_add]
  refine DynCircuitExt.count_measureXResetAndBranch_TOFF_le v (B + 1) _ _ 0 fun f7Top ↦ ?_
  rw [hFixToff]
theorem count_dPost4dWStateGenOf_t_le {Var : Type} {n mClean : ℕ} (B : ℕ) (hB1 : 1 ≤ B)
    (hB27 : B ≤ 27) (hmClean : 126 ≤ mClean) (v : Var) (rClean : QRegister mClean n)
    (dKick : DynamicCircuit Var n) (tKick : ℕ) (hKickT : dKick.count PrimitiveGate.T ≤ tKick)
    (dFix : (Fin 27 → Bool) → (Fin 30 → Bool) → (Fin (B + 1) → Bool) → DynamicCircuit Var n)
    (tFix : ℕ) (hFixT : ∀ fS f5c f7, (dFix fS f5c f7).count PrimitiveGate.T ≤ tFix)
    (fStream : Fin 27 → Bool) : (dPost4dWStateGenOf B hB1 hB27 hmClean v rClean dKick dFix
    fStream).count PrimitiveGate.T ≤ 52 + tKick + tFix := by
  dsimp only [dPost4dWStateGenOf]
  simp only [DynamicCircuit.count, k6_count_substToffoliCircuit_t,
    Circuit.count_seq, k6_cPhaseMux4All6Raw_count_t, k6_cXorDiffTop6Raw_count_t]
  obtain ⟨hOH4T, hOH4Toff⟩ := k6_cOneHot4Raw_counts (rP2Of hmClean rClean)
      (rOH4Of hmClean rClean) (disj_rP2_rOH4 hmClean rClean)
  rw [hOH4T, hOH4Toff]
  refine le_trans (Nat.add_le_add_left (Nat.add_le_add_left
    (DynCircuitExt.count_measureXResetAndBranch_T_le v 30 _ _ (tKick + tFix) fun f5c ↦ ?_) _) _)
    (by omega)
  simp only [DynamicCircuit.count]
  refine le_trans (Nat.add_le_add hKickT (DynCircuitExt.count_measureXResetAndBranch_T_le v
    (B + 1) _ _ tFix fun f7Top ↦ hFixT fStream f5c f7Top)) (by omega)
theorem count_dStreamRemWStateGenDyn_toff {Var : Type} {n mClean : ℕ}
    (B : ℕ) (hB1 : 1 ≤ B) (hB27 : B ≤ 27) (hmClean : 126 ≤ mClean) (v : Var)
    (rCore : QRegister posCoreWires n) (rClean : QRegister mClean n)
    (hCC : rCore.DisjointWires rClean)
    (dKick : DynamicCircuit Var n) (hKickToff : dKick.count PrimitiveGate.TOFF = 0)
    (dFix : (Fin 27 → Bool) → (Fin 30 → Bool) → (Fin (B + 1) → Bool) → DynamicCircuit Var n)
    (hFixToff : ∀ fS f5c f7, (dFix fS f5c f7).count PrimitiveGate.TOFF = 0) :
    ∀ (fAcc : Fin 27 → Bool) (rem : ℕ) (hrem : rem ≤ 27),
      (dStreamRemWStateGenDyn B hB1 hB27 hmClean v rCore rClean hCC dKick dFix
        fAcc rem hrem).count PrimitiveGate.TOFF = 0
  | fAcc, 0, _ =>
      count_dPost4dWStateGenOf_toff B hB1 hB27 hmClean v rClean
        dKick hKickToff dFix hFixToff fAcc
  | fAcc, rem + 1, hrem => by
      dsimp only [dStreamRemWStateGenDyn]
      split_ifs with hAct
      · simp only [DynamicCircuit.count, p2t_cPhaseMuxCol64_count_toff, k6_count_cnot_toff,
          zero_add]
        rw [← Nat.le_zero]
        refine DynCircuitExt.count_measureXResetAndBranch_TOFF_le v 1 _ _ 0 fun fBit ↦ ?_
        rw [count_dStreamRemWStateGenDyn_toff B hB1 hB27 hmClean v rCore rClean hCC
          dKick hKickToff dFix hFixToff _ rem (Nat.le_of_succ_le hrem)]
      · exact count_dStreamRemWStateGenDyn_toff B hB1 hB27 hmClean v rCore rClean hCC
          dKick hKickToff dFix hFixToff fAcc rem (Nat.le_of_succ_le hrem)
theorem count_dStreamRemWStateGenDyn_t_le {Var : Type} {n mClean : ℕ}
    (B : ℕ) (hB1 : 1 ≤ B) (hB27 : B ≤ 27) (hmClean : 126 ≤ mClean) (v : Var)
    (rCore : QRegister posCoreWires n) (rClean : QRegister mClean n)
    (hCC : rCore.DisjointWires rClean)
    (dKick : DynamicCircuit Var n) (tKick : ℕ) (hKickT : dKick.count PrimitiveGate.T ≤ tKick)
    (dFix : (Fin 27 → Bool) → (Fin 30 → Bool) → (Fin (B + 1) → Bool) → DynamicCircuit Var n)
    (tFix : ℕ) (hFixT : ∀ fS f5c f7, (dFix fS f5c f7).count PrimitiveGate.T ≤ tFix) :
    ∀ (fAcc : Fin 27 → Bool) (rem : ℕ) (hrem : rem ≤ 27),
      (dStreamRemWStateGenDyn B hB1 hB27 hmClean v rCore rClean hCC dKick dFix
        fAcc rem hrem).count PrimitiveGate.T ≤
        128 * streamRemActiveCount B rem hrem + (52 + tKick + tFix)
  | fAcc, 0, _ => by
      dsimp only [dStreamRemWStateGenDyn, streamRemActiveCount]
      simpa using count_dPost4dWStateGenOf_t_le B hB1 hB27 hmClean v rClean
        dKick tKick hKickT dFix tFix hFixT fAcc
  | fAcc, rem + 1, hrem => by
      dsimp only [dStreamRemWStateGenDyn, streamRemActiveCount]
      split_ifs with hAct
      · simp only [DynamicCircuit.count, p2t_cPhaseMuxCol64_count_t, k6_count_cnot_t, zero_add]
        have hCol0 : p2t_phaseMuxColT 0 = 128 := by decide
        rw [hCol0]
        refine le_trans (Nat.add_le_add_left
          (DynCircuitExt.count_measureXResetAndBranch_T_le v 1 _ _
            (128 * streamRemActiveCount B rem (Nat.le_of_succ_le hrem) + (52 + tKick + tFix))
            fun fBit ↦ count_dStreamRemWStateGenDyn_t_le B hB1 hB27 hmClean v rCore rClean hCC
              dKick tKick hKickT dFix tFix hFixT _ rem (Nat.le_of_succ_le hrem)) 128) (by omega)
      · refine le_trans
          (count_dStreamRemWStateGenDyn_t_le B hB1 hB27 hmClean v rCore rClean hCC
            dKick tKick hKickT dFix tFix hFixT fAcc rem (Nat.le_of_succ_le hrem)) (by omega)
theorem count_dMidK6WStateGenDyn_toff {Var : Type} {n mClean : ℕ}
    (B : ℕ) (hB1 : 1 ≤ B) (hB27 : B ≤ 27) (hmClean : 126 ≤ mClean) (v : Var)
    (rCore : QRegister posCoreWires n) (rOrbit16 : QRegister 16 n) (rClean : QRegister mClean n)
    (hCC : rCore.DisjointWires rClean) (hOC : rOrbit16.DisjointWires rClean)
    (dLoad : DynamicCircuit Var n) (hLoadToff : dLoad.count PrimitiveGate.TOFF = 0)
    (dKick : DynamicCircuit Var n) (hKickToff : dKick.count PrimitiveGate.TOFF = 0)
    (dFix : (Fin 27 → Bool) → (Fin 30 → Bool) → (Fin (B + 1) → Bool) → DynamicCircuit Var n)
    (hFixToff : ∀ fS f5c f7, (dFix fS f5c f7).count PrimitiveGate.TOFF = 0) :
    (dMidK6WStateGenDyn B hB1 hB27 hmClean v rCore rOrbit16 rClean hCC hOC dLoad dKick dFix).count
      PrimitiveGate.TOFF = 0 := by
  rw [dMidK6WStateGenDyn, p2t_lockVal_eq]
  dsimp only [dMidK6WStateGenDynRaw, dInnerWStateGenOf]
  rw [p2t_count_withOneHot64SumCompDyn_wstate_loc_toff]
  simp only [DynamicCircuit.count]
  exact Eq.trans (congrArg₂ (· + ·) (cPreMuxRaw_count_toff B _ _ _ _ _ _ _ _ 27 (le_refl
    27)) (congrArg₂ (· + ·) hLoadToff (count_dStreamRemWStateGenDyn_toff B hB1 hB27 hmClean
    v rCore rClean hCC dKick hKickToff dFix hFixToff _ 27 (le_refl 27)))) rfl
theorem count_dMidK6WStateGenDyn_t_le {Var : Type} {n mClean : ℕ}
    (B : ℕ) (hB6 : 6 ≤ B) (hB27 : B ≤ 27) (hmClean : 126 ≤ mClean) (v : Var)
    (rCore : QRegister posCoreWires n) (rOrbit16 : QRegister 16 n) (rClean : QRegister mClean n)
    (hCC : rCore.DisjointWires rClean) (hOC : rOrbit16.DisjointWires rClean)
    (dLoad : DynamicCircuit Var n) (tLoad : ℕ) (hLoadT : dLoad.count PrimitiveGate.T ≤ tLoad)
    (dKick : DynamicCircuit Var n) (tKick : ℕ) (hKickT : dKick.count PrimitiveGate.T ≤ tKick)
    (dFix : (Fin 27 → Bool) → (Fin 30 → Bool) → (Fin (B + 1) → Bool) → DynamicCircuit Var n)
    (tFix : ℕ) (hFixT : ∀ fS f5c f7, (dFix fS f5c f7).count PrimitiveGate.T ≤ tFix) :
    (dMidK6WStateGenDyn B (by omega) hB27 hmClean v rCore rOrbit16 rClean hCC hOC
      dLoad dKick dFix).count PrimitiveGate.T + 592 ≤ tLoad + tKick + tFix + 256 * B := by
  rw [dMidK6WStateGenDyn, p2t_lockVal_eq]
  dsimp only [dMidK6WStateGenDynRaw, dInnerWStateGenOf]
  rw [p2t_count_withOneHot64SumCompDyn_wstate_loc_t]
  simp only [DynamicCircuit.count]
  have h1 := cPreMuxRaw_count_t B (wParity2Of hmClean rClean)
      (rOH64Of hmClean rClean) (rTarget27Of hmClean rClean) (rDirtyOf rCore)
      (wStream_ne_rTarget27 hmClean rClean) (disj_rOH64_rTarget27 hmClean rClean)
      (k6_disjoint_concat_right ((hCC.compose_left _).compose_right _) ((hCC.compose_left
      _).compose_right _) _) (rOH64_ne_wStream hmClean rClean) 27 (le_refl 27)
  rw [k6ActiveCount_27 B hB6 hB27] at h1
  have h3 := count_dStreamRemWStateGenDyn_t_le B (by omega) hB27 hmClean v rCore rClean hCC
    dKick tKick hKickT dFix tFix hFixT (fun _ ↦ false) 27 (le_refl 27)
  rw [streamRemActiveCount_27 B hB6 hB27] at h3
  omega
private theorem neg_one_pow_cancel (sgn : ℂ) (sF sRest : ZMod 2) :
    ((-1 : ℂ) ^ sF.val) * (sgn * ((-1 : ℂ) ^ (sRest + sF).val)) = sgn * ((-1 : ℂ) ^ sRest.val) := by
  have hc : sF + (sRest + sF) = sRest := by
    calc sF + (sRest + sF) = sRest + (sF + sF) := by ring
      _ = sRest := by rw [CharTwo.add_self_eq_zero, add_zero]
  calc ((-1 : ℂ) ^ sF.val) * (sgn * ((-1 : ℂ) ^ (sRest + sF).val))
      = sgn * (((-1 : ℂ) ^ sF.val) * ((-1 : ℂ) ^ (sRest + sF).val)) := by ring
    _ = sgn * ((-1 : ℂ) ^ (sF + (sRest + sF)).val) := by rw [← neg_one_pow_zmod2_add]
    _ = sgn * ((-1 : ℂ) ^ sRest.val) := by rw [hc]
private theorem writeReg_slice_mkState {n mClean : ℕ}
    (rCore : QRegister posCoreWires n) (rClean : QRegister mClean n)
    (hCC : rCore.DisjointWires rClean) (γ₀ : BitAssignment n)
    (vc₁ vc₂ : Fin mClean → ZMod 2) (vd : Fin 1728 → ZMod 2)
    (off len : ℕ) (hOff : off + len ≤ mClean) (f : Fin len → ZMod 2)
    (hIn : ∀ k : Fin mClean, (hk : off ≤ k.val ∧ k.val < off + len) →
      f ⟨k.val - off, by omega⟩ = vc₂ k)
    (hOut : ∀ k : Fin mClean, ¬ (off ≤ k.val ∧ k.val < off + len) → vc₁ k = vc₂ k) :
    writeReg (mkState rCore rClean hCC γ₀ vc₁ vd) (rClean.slice off len hOff) f =
      mkState rCore rClean hCC γ₀ vc₂ vd := by
  apply eq_mkState rCore rClean hCC
  · intro k
    by_cases hk : off ≤ k.val ∧ k.val < off + len
    · have hEq : rClean k = rClean.slice off len hOff ⟨k.val - off, by omega⟩ := by
        rw [QRegister.slice_apply]
        exact congrArg rClean.wires (Fin.ext (by dsimp; omega))
      rw [hEq, writeReg_apply_reg, hIn k hk]
    · rw [writeReg_apply_of_not_mem _ (rClean.slice off len hOff) _ (rClean k) (fun ⟨b, hb⟩ ↦ by
          rw [QRegister.slice_apply] at hb
          have hv := congrArg Fin.val (rClean.wires.injective hb)
          dsimp at hv
          omega),
        mkState_clean, hOut k hk]
  · intro d
    rw [writeReg_apply_of_not_mem _ (rClean.slice off len hOff) _ _
          (fun ⟨b, hb⟩ ↦ ((hCC.compose_left _).compose_right _).ne d b hb.symm),
        mkState_dirty]
  · intro w hc hd
    rw [writeReg_apply_of_not_mem _ (rClean.slice off len hOff) _ w
          (fun ⟨b, hb⟩ ↦ hc ⟨⟨off + b.val, by omega⟩, hb⟩),
        mkState_other rCore rClean hCC γ₀ _ _ w hc hd]
private theorem update_clean_mkState {n mClean : ℕ} (rCore : QRegister posCoreWires n)
    (rClean : QRegister mClean n) (hCC : rCore.DisjointWires rClean) (γ₀ : BitAssignment n)
    (vc₁ vc₂ : Fin mClean → ZMod 2) (vd : Fin 1728 → ZMod 2) (k₀ : Fin mClean) (val : ZMod 2)
    (hEq0 : val = vc₂ k₀) (hNe : ∀ k : Fin mClean, k ≠ k₀ → vc₁ k = vc₂ k) : Function.update
    (mkState rCore rClean hCC γ₀ vc₁ vd) (rClean k₀) val = mkState rCore rClean hCC γ₀
    vc₂ vd := by
  apply eq_mkState rCore rClean hCC
  · intro k
    by_cases hk : k = k₀
    · subst hk
      rw [Function.update_self, hEq0]
    · rw [Function.update_of_ne (rClean.wires.injective.ne hk), mkState_clean, hNe k hk]
  · intro d
    rw [Function.update_of_ne ((hCC.compose_left _).ne d k₀), mkState_dirty]
  · intro w hc hd
    rw [Function.update_of_ne (fun h ↦ hc ⟨k₀, h.symm⟩),
        mkState_other rCore rClean hCC γ₀ _ _ w hc hd]
theorem dPost4dWStateGenOf_stageSpec {Var : Type} [Fintype Var] [DecidableEq Var]
    {n mClean : ℕ} [NeZero (2 ^ n)]
    (B : ℕ) (hB6 : 6 ≤ B) (hB27 : B ≤ 27) (hmClean : 126 ≤ mClean)
    (slot2SwappedTo0 : Bool) (v : Var)
    (rCore : QRegister posCoreWires n) (rOrbit16 : QRegister 16 n) (rClean : QRegister mClean n)
    (hCO : rCore.DisjointWires rOrbit16) (hCC : rCore.DisjointWires rClean)
    (hOC : rOrbit16.DisjointWires rClean)
    (dKick : DynamicCircuit Var n)
    (hStage6 : K6StageSpec
      (atStage hmClean rCore rOrbit16 rClean hCC
        (vClean5 B rOrbit16 rClean) (vDirty1 rCore rOrbit16))
      dKick (fun α ↦ α)
      (signOf B (by omega) (by omega) slot2SwappedTo0 rCore rOrbit16 hCO))
    (dFix : (Fin 27 → Bool) → (Fin 30 → Bool) → (Fin (B + 1) → Bool) → DynamicCircuit Var n)
    (hStageFix : ∀ fStream f5c f7Top,
      K6StageSpec
        (atStage hmClean rCore rOrbit16 rClean hCC (vClean7 rClean)
          (vDirty1 rCore rOrbit16))
        (dFix fStream f5c f7Top)
        (recoverInit rCore rOrbit16 rClean)
        (fun α ↦
          (-1 : ℂ) ^
            ((∑ m : Fin 27,
                if fStream m then gOf rCore rOrbit16 α m + k6_tStreamOf rOrbit16 α m
                else 0) +
             (∑ k : Fin 30,
                if f5c k then k6_meas5cTableBit (k6_qOf rOrbit16 α) (k6_selOf rOrbit16 α) k
                else 0) +
             (∑ j : Fin (B + 1),
                if f7Top j then
                  k6Table31 (k6_qOf rOrbit16 α) (k6_selOf rOrbit16 α) ⟨(30 - B) + j.val, by omega⟩
                else 0)).val))
    (fStream : Fin 27 → Bool) :
    K6StageSpec
      (atStage hmClean rCore rOrbit16 rClean hCC
        (vCleanStream B 27 rCore rOrbit16 rClean)
        (vDirty1 rCore rOrbit16))
      (dPost4dWStateGenOf B (by omega) hB27 hmClean v rClean dKick dFix fStream)
      (recoverInit rCore rOrbit16 rClean)
      (fun α ↦
        signOf B (by omega) (by omega) slot2SwappedTo0 rCore rOrbit16 hCO α *
        (-1 : ℂ) ^
          (∑ m : Fin 27,
            if fStream m then gOf rCore rOrbit16 α m + k6_tStreamOf rOrbit16 α m
            else 0).val) := by
  have hB1 : 1 ≤ B := by omega
  have hB29 : B ≤ 29 := by omega
  dsimp only [dPost4dWStateGenOf]
  let rP2 := rP2Of hmClean rClean
  let rOH4 := rOH4Of hmClean rClean
  let rPal18 := rPal18Of hmClean rClean
  let rDiff6 := rDiff6Of hmClean rClean
  let rOutBTop6 := rOutBTop6Of hmClean rClean
  let rOutTop := rOutTopOf B hB1 hB27 hmClean rClean
  let rMeas5c30 := rMeas5c30Of hmClean rClean
  let hPOH4 : rP2.DisjointWires rOH4 := disj_rP2_rOH4 hmClean rClean
  let hOHD : rOH4.DisjointWires rDiff6 := disj_rOH4_rDiff6 hmClean rClean
  let hPalD : rPal18.DisjointWires rDiff6 := disj_rPal18_rDiff6 hmClean rClean
  let hDT : rDiff6.DisjointWires rOutBTop6 := disj_rDiff6_rOutBTop6 hmClean rClean
  let hCOut : rCore.DisjointWires rOutTop := hCC.compose_right _
  let S_s27 := atStage hmClean rCore rOrbit16 rClean hCC
    (vCleanStream B 27 rCore rOrbit16 rClean) (vDirty1 rCore rOrbit16)
  let S_5a := atStage hmClean rCore rOrbit16 rClean hCC
    (vClean5a B rOrbit16 rClean) (vDirty1 rCore rOrbit16)
  let S_5b := atStage hmClean rCore rOrbit16 rClean hCC
    (vClean5b B rOrbit16 rClean) (vDirty1 rCore rOrbit16)
  let S_5c := atStage hmClean rCore rOrbit16 rClean hCC
    (vClean5c B rOrbit16 rClean) (vDirty1 rCore rOrbit16)
  let S_5 := atStage hmClean rCore rOrbit16 rClean hCC
    (vClean5 B rOrbit16 rClean) (vDirty1 rCore rOrbit16)
  let S_7 := atStage hmClean rCore rOrbit16 rClean hCC
    (vClean7 rClean) (vDirty1 rCore rOrbit16)
  have hW7Eq : ∀ γ₀,
      writeReg (mkState rCore rClean hCC γ₀
        (vClean5 B rOrbit16 rClean γ₀) (vDirty1 rCore rOrbit16 γ₀))
        rOutTop (fun _ ↦ 0) =
      mkState rCore rClean hCC γ₀
        (vClean7 rClean γ₀) (vDirty1 rCore rOrbit16 γ₀) := fun γ₀ ↦
    writeReg_slice_mkState rCore rClean hCC γ₀ _ _ _ (64 + (30 - B)) (B + 1) _ _
      (fun k hk ↦ by simp [vClean7, show ¬ (k.val < 64) by omega])
      (fun k hk ↦ by
        dsimp [vClean5, vClean7]
        by_cases hk64 : k.val < 64
        · simp [hk64]
        · by_cases hkSkip : k.val < 64 + (30 - B)
          · simp [hk64, hkSkip]
          · simp [hk64, hkSkip, show ¬ (k.val < 95) by omega])
  have hStage7 : ∀ f5c : Fin 30 → Bool, K6StageSpec S_5 (DynCircuitExt.measureXResetAndBranch
      v (B + 1) rOutTop fun f7Top ↦ dFix fStream f5c f7Top)
      (recoverInit rCore rOrbit16 rClean) (fun α ↦ (-1 : ℂ) ^ ((∑ m : Fin 27, if fStream m
      then gOf rCore rOrbit16 α m + k6_tStreamOf rOrbit16 α m else 0) + (∑ k : Fin 30, if
      f5c k then k6_meas5cTableBit (k6_qOf rOrbit16 α) (k6_selOf rOrbit16 α) k else 0)).val)
      := by
    intro f5c
    let ph7 : BitAssignment n → ℂ := fun α ↦ (-1 : ℂ) ^ ((∑ m : Fin 27, if fStream m then
        gOf rCore rOrbit16 α m + k6_tStreamOf rOrbit16 α m else 0) + (∑ k : Fin 30, if f5c
        k then k6_meas5cTableBit (k6_qOf rOrbit16 α) (k6_selOf rOrbit16 α) k else 0)).val
    have hM := K6StageSpec.measureXReset (S_pre := S_5) (S_post := S_7) (phase_total := ph7)
      v rOutTop
      (by rintro α ⟨γ₀, hγ₀, rfl⟩; rw [hW7Eq γ₀]; exact ⟨γ₀, hγ₀, rfl⟩)
      (fun f7Top ↦ hStageFix fStream f5c f7Top)
      (by
        rintro f7Top α ⟨γ₀, hγ₀, rfl⟩
        obtain ⟨hQ5, hSel5, _, hg5, ht5, _⟩ :=
          mkState_invariants hmClean B hB1 hB29 slot2SwappedTo0 rCore rOrbit16 rClean hCO hCC hOC γ₀
            hγ₀
            (vClean5 B rOrbit16 rClean γ₀) (fun k hk ↦ by dsimp [vClean5]; simp [hk])
        obtain ⟨hQ7, hSel7, _, hg7, ht7, _⟩ :=
          mkState_invariants hmClean B hB1 hB29 slot2SwappedTo0 rCore rOrbit16 rClean hCO hCC hOC γ₀
            hγ₀
            (vClean7 rClean γ₀) (fun k hk ↦ by dsimp [vClean7]; simp [hk])
        rw [hW7Eq γ₀, k6_prod_ite_neg_one_pow]
        dsimp only [ph7]
        rw [← neg_one_pow_zmod2_add]
        have hOutRead : ∀ b : Fin (B + 1),
            mkState rCore rClean hCC γ₀ (vClean5 B rOrbit16 rClean γ₀)
              (vDirty1 rCore rOrbit16 γ₀) (rOutTop b) =
            k6Table31 (k6_qOf rOrbit16 γ₀) (k6_selOf rOrbit16 γ₀) ⟨(30 - B) + b.val, by omega⟩ :=
              fun b ↦ by
          dsimp only [rOutTop, rOutTopOf]; rw [QRegister.slice_apply, mkState_clean]
          dsimp [vClean5]
          have h1 : ¬ ((64 + (30 - B)) + b.val < 64) := by omega
          have h2 : ¬ ((64 + (30 - B)) + b.val < 64 + (30 - B)) := by omega
          have h3 : (64 + (30 - B)) + b.val < 95 := by omega
          simp only [h1, h2, h3, ↓reduceIte, ↓reduceDIte]
          exact congrArg (k6Table31 _ _) (Fin.ext (by dsimp; omega))
        simp only [hOutRead, hQ7, hSel7, hQ5, hSel5]
        have hSumG : (∑ m : Fin 27, if fStream m then gOf rCore rOrbit16 (mkState rCore
            rClean hCC γ₀ (vClean7 rClean γ₀) (vDirty1 rCore rOrbit16 γ₀)) m +
            k6_tStreamOf rOrbit16 γ₀ m else 0) = (∑ m : Fin 27, if fStream m then gOf rCore
            rOrbit16 (mkState rCore rClean hCC γ₀ (vClean5 B rOrbit16 rClean γ₀)
            (vDirty1 rCore rOrbit16 γ₀)) m + k6_tStreamOf rOrbit16 γ₀ m else 0) := by
          refine Finset.sum_congr rfl fun m _ ↦ ?_
          rw [hg7 m, hg5 m]
        refine congrArg (fun e : ZMod 2 ↦ (-1 : ℂ) ^ e.val) ?_
        simp only [ht7, ht5] at hSumG ⊢
        rw [hSumG]
        set sF := ∑ b : Fin (B + 1), if f7Top b then
          k6Table31 (k6_qOf rOrbit16 γ₀) (k6_selOf rOrbit16 γ₀) ⟨(30 - B) + b.val, by omega⟩ else 0
        set sRest := (∑ m : Fin 27, if fStream m then
            gOf rCore rOrbit16
              (mkState rCore rClean hCC γ₀ (vClean5 B rOrbit16 rClean γ₀)
                (vDirty1 rCore rOrbit16 γ₀)) m +
              k6_tStreamOf rOrbit16 γ₀ m else 0) +
          (∑ k : Fin 30, if f5c k then
            k6_meas5cTableBit (k6_qOf rOrbit16 γ₀) (k6_selOf rOrbit16 γ₀) k else 0)
        calc sF + (sRest + sF) = sRest + (sF + sF) := by ring
          _ = sRest := by rw [CharTwo.add_self_eq_zero, add_zero])
    refine K6StageSpec.congr hM ?_ (fun _ _ ↦ rfl)
    rintro α ⟨γ₀, hγ₀, rfl⟩
    rw [hW7Eq γ₀,
        recoverInit_mkState hmClean rCore rOrbit16 rClean hCO hCC hOC γ₀ hγ₀ _
          (fun k hk ↦ by dsimp [vClean7]; simp [hk]),
        recoverInit_mkState hmClean rCore rOrbit16 rClean hCO hCC hOC γ₀ hγ₀ _
          (fun k hk ↦ by dsimp [vClean5]; simp [hk])]
  have hW5dEq : ∀ γ₀,
      writeReg (mkState rCore rClean hCC γ₀
        (vClean5c B rOrbit16 rClean γ₀) (vDirty1 rCore rOrbit16 γ₀))
        rMeas5c30 (fun _ ↦ 0) =
      mkState rCore rClean hCC γ₀
        (vClean5 B rOrbit16 rClean γ₀) (vDirty1 rCore rOrbit16 γ₀) := fun γ₀ ↦
    writeReg_slice_mkState rCore rClean hCC γ₀ _ _ _ 95 30 _ _
      (fun k hk ↦ by
        simp [vClean5, show ¬ (k.val < 64) by omega,
          show ¬ (k.val < 64 + (30 - B)) by omega, show ¬ (k.val < 95) by omega])
      (fun k hk ↦ by
        dsimp [vClean5c, vClean5]
        by_cases hk64 : k.val < 64
        · simp [hk64]
        · by_cases hkSkip : k.val < 64 + (30 - B)
          · simp [hk64, hkSkip]
          · by_cases hk95 : k.val < 95
            · simp [hk64, hkSkip, hk95]
            · simp [hk64, hkSkip, hk95, show ¬ (k.val < 125) by omega])
  let phTotal : BitAssignment n → ℂ := fun α ↦ signOf B hB1 hB29 slot2SwappedTo0 rCore
      rOrbit16 hCO α * (-1 : ℂ) ^ (∑ m : Fin 27, if fStream m then gOf rCore rOrbit16 α m +
      k6_tStreamOf rOrbit16 α m else 0).val
  have hStage5d : K6StageSpec S_5c (DynCircuitExt.measureXResetAndBranch v 30 rMeas5c30 fun
      f5c ↦ .seq dKick (DynCircuitExt.measureXResetAndBranch v (B + 1) rOutTop fun f7Top ↦
      dFix fStream f5c f7Top)) (recoverInit rCore rOrbit16 rClean) phTotal := by
    have h67 : ∀ f5c : Fin 30 → Bool, K6StageSpec S_5 (.seq dKick
        (DynCircuitExt.measureXResetAndBranch v (B + 1) rOutTop fun f7Top ↦ dFix fStream f5c
        f7Top)) (recoverInit rCore rOrbit16 rClean) (fun α ↦ signOf B hB1 hB29
        slot2SwappedTo0 rCore rOrbit16 hCO α * (-1 : ℂ) ^ ((∑ m : Fin 27, if fStream m then
        gOf rCore rOrbit16 α m + k6_tStreamOf rOrbit16 α m else 0) + (∑ k : Fin 30, if f5c
        k then k6_meas5cTableBit (k6_qOf rOrbit16 α) (k6_selOf rOrbit16 α) k else 0)).val) :=
        fun f5c ↦ K6StageSpec.seq hStage6 (hStage7 f5c) (fun _ h ↦ h)
    have hM := K6StageSpec.measureXReset (S_pre := S_5c) (S_post := S_5) (phase_total := phTotal)
      v rMeas5c30
      (by rintro α ⟨γ₀, hγ₀, rfl⟩; rw [hW5dEq γ₀]; exact ⟨γ₀, hγ₀, rfl⟩)
      h67
      (by
        rintro f5c α ⟨γ₀, hγ₀, rfl⟩
        obtain ⟨hQ5c, hSel5c, hSign5c, hg5c, ht5c, _⟩ :=
          mkState_invariants hmClean B hB1 hB29 slot2SwappedTo0 rCore rOrbit16 rClean hCO hCC hOC γ₀
            hγ₀
            (vClean5c B rOrbit16 rClean γ₀) (fun k hk ↦ by dsimp [vClean5c]; simp [hk])
        obtain ⟨hQ5, hSel5, hSign5, hg5, ht5, _⟩ :=
          mkState_invariants hmClean B hB1 hB29 slot2SwappedTo0 rCore rOrbit16 rClean hCO hCC hOC γ₀
            hγ₀
            (vClean5 B rOrbit16 rClean γ₀) (fun k hk ↦ by dsimp [vClean5]; simp [hk])
        rw [hW5dEq γ₀, k6_prod_ite_neg_one_pow]
        dsimp only [phTotal]
        have hMeasRead : ∀ k : Fin 30,
            mkState rCore rClean hCC γ₀ (vClean5c B rOrbit16 rClean γ₀)
              (vDirty1 rCore rOrbit16 γ₀) (rMeas5c30 k) =
            k6_meas5cTableBit (k6_qOf rOrbit16 γ₀) (k6_selOf rOrbit16 γ₀) k := fun k ↦ by
          dsimp only [rMeas5c30, rMeas5c30Of]; rw [QRegister.slice_apply, mkState_clean]
          dsimp [vClean5c]
          have h1 : ¬ (95 + k.val < 64) := by omega
          have h2 : ¬ (95 + k.val < 64 + (30 - B)) := by omega
          have h3 : ¬ (95 + k.val < 95) := by omega
          have h4 : 95 + k.val < 125 := by omega
          simp only [h1, h2, h3, h4, ↓reduceIte, ↓reduceDIte]
          exact congrArg (k6_meas5cTableBit _ _) (Fin.ext (by dsimp; omega))
        simp only [hMeasRead, hQ5, hSel5, hSign5, hSign5c]
        have hSumG : (∑ m : Fin 27, if fStream m then gOf rCore rOrbit16 (mkState rCore
            rClean hCC γ₀ (vClean5 B rOrbit16 rClean γ₀) (vDirty1 rCore rOrbit16 γ₀)) m
            + k6_tStreamOf rOrbit16 (mkState rCore rClean hCC γ₀ (vClean5 B rOrbit16
            rClean γ₀) (vDirty1 rCore rOrbit16 γ₀)) m else 0) = (∑ m : Fin 27, if fStream m
            then gOf rCore rOrbit16 (mkState rCore rClean hCC γ₀ (vClean5c B rOrbit16
            rClean γ₀) (vDirty1 rCore rOrbit16 γ₀)) m + k6_tStreamOf rOrbit16 (mkState
            rCore rClean hCC γ₀ (vClean5c B rOrbit16 rClean γ₀) (vDirty1 rCore rOrbit16
            γ₀)) m else 0) := by
          refine Finset.sum_congr rfl fun m _ ↦ ?_
          rw [hg5 m, hg5c m, ht5 m, ht5c m]
        rw [hSumG]
        set sF := ∑ k : Fin 30, if f5c k then
          k6_meas5cTableBit (k6_qOf rOrbit16 γ₀) (k6_selOf rOrbit16 γ₀) k else 0
        set sRest := ∑ m : Fin 27, if fStream m then
            gOf rCore rOrbit16
              (mkState rCore rClean hCC γ₀ (vClean5c B rOrbit16 rClean γ₀)
                (vDirty1 rCore rOrbit16 γ₀)) m +
              k6_tStreamOf rOrbit16
                (mkState rCore rClean hCC γ₀ (vClean5c B rOrbit16 rClean γ₀)
                  (vDirty1 rCore rOrbit16 γ₀)) m else 0
        exact neg_one_pow_cancel _ sF sRest)
    refine K6StageSpec.congr hM ?_ (fun _ _ ↦ rfl)
    rintro α ⟨γ₀, hγ₀, rfl⟩
    rw [hW5dEq γ₀,
        recoverInit_mkState hmClean rCore rOrbit16 rClean hCO hCC hOC γ₀ hγ₀ _
          (fun k hk ↦ by dsimp [vClean5]; simp [hk]),
        recoverInit_mkState hmClean rCore rOrbit16 rClean hCO hCC hOC γ₀ hγ₀ _
          (fun k hk ↦ by dsimp [vClean5c]; simp [hk])]
  let cStep5c :=
    k6_cPhaseMux4All6Raw rOH4 rPal18 rDiff6 hOHD hPalD 6 (le_refl 6) ;;ᶜ
    k6_cXorDiffTop6Raw rDiff6 rOutBTop6 hDT 6 (le_refl 6)
  let next5c : BitAssignment n → BitAssignment n := fun α ↦
    let p0 := α (rP2 0)
    let p1 := α (rP2 1)
    let β₁ := writeReg α rDiff6 (fun j ↦
      p0 * (1 + p1) * α (rPal18 ⟨j.val, by omega⟩) +
      (1 + p0) * p1 * α (rPal18 ⟨6 + j.val, by omega⟩) +
      p0 * p1 * α (rPal18 ⟨12 + j.val, by omega⟩))
    writeReg β₁ rOutBTop6 (fun j ↦ β₁ (rOutBTop6 j) + β₁ (rDiff6 j))
  have hP5b : ∀ γ₀,
      mkState rCore rClean hCC γ₀ (vClean5b B rOrbit16 rClean γ₀)
        (vDirty1 rCore rOrbit16 γ₀) (rP2 0) =
        k6P0Bit (k6_qOf rOrbit16 γ₀) (k6_selOf rOrbit16 γ₀) ∧
      mkState rCore rClean hCC γ₀ (vClean5b B rOrbit16 rClean γ₀)
        (vDirty1 rCore rOrbit16 γ₀) (rP2 1) =
        k6P1Bit (k6_qOf rOrbit16 γ₀) (k6_selOf rOrbit16 γ₀) := fun γ₀ ↦ by
    dsimp only [rP2, rP2Of]
    refine ⟨?_, ?_⟩
    · rw [QRegister.slice_apply]
      change mkState rCore rClean hCC γ₀ _ _ (rClean ⟨113, by omega⟩) = _
      rw [mkState_clean]
      simp [vClean5b, show ¬ (113 < 64 + (30 - B)) by omega]
    · rw [QRegister.slice_apply]
      change mkState rCore rClean hCC γ₀ _ _ (rClean ⟨114, by omega⟩) = _
      rw [mkState_clean]
      simp [vClean5b, show ¬ (114 < 64 + (30 - B)) by omega]
  have hNext5cEq : ∀ γ₀, next5c (mkState rCore rClean hCC γ₀ (vClean5b B rOrbit16 rClean
      γ₀) (vDirty1 rCore rOrbit16 γ₀)) = mkState rCore rClean hCC γ₀
      (vClean5c B rOrbit16 rClean γ₀) (vDirty1 rCore rOrbit16 γ₀) := by
    intro γ₀
    let q := k6_qOf rOrbit16 γ₀
    let sel := k6_selOf rOrbit16 γ₀
    let α_b := mkState rCore rClean hCC γ₀
      (vClean5b B rOrbit16 rClean γ₀) (vDirty1 rCore rOrbit16 γ₀)
    have hP0 : α_b (rP2 0) = k6P0Bit q sel := (hP5b γ₀).1
    have hP1 : α_b (rP2 1) = k6P1Bit q sel := (hP5b γ₀).2
    have hPal18 : ∀ i : Fin 18, α_b (rPal18 i) = k6Pal24Bit q sel ⟨6 + i.val, by omega⟩ := fun i ↦
      by
      dsimp only [α_b, rPal18, rPal18Of]; rw [QRegister.slice_apply, mkState_clean]
      dsimp [vClean5b, q, sel]
      have h1 : ¬ (95 + i.val < 64) := by omega
      have h2 : ¬ (95 + i.val < 64 + (30 - B)) := by omega
      have h3 : ¬ (95 + i.val < 89) := by omega
      have h4 : 95 + i.val < 113 := by omega
      simp only [h1, h2, h3, h4, ↓reduceIte, ↓reduceDIte]
      exact congrArg (k6Pal24Bit _ _) (Fin.ext (by dsimp; omega))
    have hTop6 : ∀ j : Fin 6, α_b (rOutBTop6 j) = k6Pal24Bit q sel ⟨j.val, by omega⟩ := fun j ↦ by
      dsimp only [α_b, rOutBTop6, rOutBTop6Of]; rw [QRegister.slice_apply, mkState_clean]
      dsimp [vClean5b, q, sel]
      have h1 : ¬ (89 + j.val < 64) := by omega
      have h2 : ¬ (89 + j.val < 64 + (30 - B)) := by omega
      have h3 : ¬ (89 + j.val < 89) := by omega
      have h4 : 89 + j.val < 113 := by omega
      simp only [h1, h2, h3, h4, ↓reduceIte, ↓reduceDIte]
      exact congrArg (k6Pal24Bit _ _) (Fin.ext (by dsimp; omega))
    have hDiffVal : ∀ j : Fin 6,
        α_b (rP2 0) * (1 + α_b (rP2 1)) * α_b (rPal18 ⟨j.val, by omega⟩) +
        (1 + α_b (rP2 0)) * α_b (rP2 1) * α_b (rPal18 ⟨6 + j.val, by omega⟩) +
        α_b (rP2 0) * α_b (rP2 1) * α_b (rPal18 ⟨12 + j.val, by omega⟩) =
        k6Diff6Bit q sel j := fun j ↦ by
      rw [hP0, hP1, hPal18 ⟨j.val, by omega⟩, hPal18 ⟨6 + j.val, by omega⟩,
          hPal18 ⟨12 + j.val, by omega⟩]
      dsimp only [k6Diff6Bit]
      have f1 : (⟨6 + (6 + j.val), by omega⟩ : Fin 24) = ⟨12 + j.val, by omega⟩ :=
        Fin.ext (by dsimp; omega)
      have f2 : (⟨6 + (12 + j.val), by omega⟩ : Fin 24) = ⟨18 + j.val, by omega⟩ :=
        Fin.ext (by dsimp; omega)
      rw [f1, f2]
    dsimp only [α_b] at hTop6 hDiffVal
    apply eq_mkState rCore rClean hCC
    · intro k
      by_cases hkTop : 89 ≤ k.val ∧ k.val < 95
      · have hEqT : rClean k = rOutBTop6 ⟨k.val - 89, by omega⟩ := by
          dsimp only [rOutBTop6, rOutBTop6Of]; rw [QRegister.slice_apply]
          exact congrArg rClean.wires (Fin.ext (by dsimp; omega))
        dsimp only [next5c]
        rw [hEqT, writeReg_apply_reg,
            writeReg_apply_of_not_mem _ rDiff6 _ (rOutBTop6 ⟨k.val - 89, by omega⟩)
              (fun ⟨j, hj⟩ ↦ hDT.ne j _ hj),
            writeReg_apply_reg, hTop6 ⟨k.val - 89, by omega⟩, hDiffVal ⟨k.val - 89, by omega⟩]
        dsimp [vClean5c, k6Table31, k6Top6Bit, q, sel]
        have h1 : ¬ (k.val < 64) := by omega
        have h2 : ¬ (k.val < 64 + (30 - B)) := by omega
        have h3 : k.val < 95 := by omega
        have h4 : ¬ (k.val - 64 < 25) := by omega
        simp only [h1, h2, h3, h4, ↓reduceIte, ↓reduceDIte]
        have hsub : k.val - 64 - 25 = k.val - 89 := by omega
        simp only [hsub]
      · dsimp only [next5c]
        rw [writeReg_apply_of_not_mem _ rOutBTop6 _ (rClean k) (fun ⟨j, hj⟩ ↦ by
          dsimp only [rOutBTop6, rOutBTop6Of] at hj; rw [QRegister.slice_apply] at hj
          have hv := congrArg Fin.val (rClean.wires.injective hj); dsimp at hv; omega)]
        by_cases hkDiff : 119 ≤ k.val ∧ k.val < 125
        · have hEqD : rClean k = rDiff6 ⟨k.val - 119, by omega⟩ := by
            dsimp only [rDiff6, rDiff6Of]; rw [QRegister.slice_apply]
            exact congrArg rClean.wires (Fin.ext (by dsimp; omega))
          rw [hEqD, writeReg_apply_reg, hDiffVal ⟨k.val - 119, by omega⟩]
          dsimp [vClean5c, k6_meas5cTableBit, q, sel]
          have h1 : ¬ (k.val < 64) := by omega
          have h2 : ¬ (k.val < 64 + (30 - B)) := by omega
          have h3 : ¬ (k.val < 95) := by omega
          have h4 : k.val < 125 := by omega
          have h5 : ¬ (k.val - 95 < 18) := by omega
          have h6 : k.val - 95 ≠ 18 := by omega
          have h7 : k.val - 95 ≠ 19 := by omega
          have h8 : ¬ (k.val - 95 < 24) := by omega
          simp only [h1, h2, h3, h4, h5, h6, h7, h8, ↓reduceIte, ↓reduceDIte]
          exact congrArg (k6Diff6Bit _ _) (Fin.ext (by dsimp; omega))
        · rw [writeReg_apply_of_not_mem _ rDiff6 _ (rClean k) (fun ⟨j, hj⟩ ↦ by
            dsimp only [rDiff6, rDiff6Of] at hj; rw [QRegister.slice_apply] at hj
            have hv := congrArg Fin.val (rClean.wires.injective hj); dsimp at hv; omega),
            mkState_clean]
          dsimp [vClean5b, vClean5c, k6Table31, k6_meas5cTableBit]
          by_cases hk64 : k.val < 64
          · simp [hk64]
          · by_cases hkSkip : k.val < 64 + (30 - B)
            · simp [hk64, hkSkip]
            · by_cases hk89 : k.val < 89
              · have hk95 : k.val < 95 := by omega
                have hlt25 : k.val - 64 < 25 := by omega
                simp [hk64, hkSkip, hk89, hk95, hlt25]
              · have hn95 : ¬ (k.val < 95) := by omega
                by_cases hk113 : k.val < 113
                · have hk125 : k.val < 125 := by omega
                  have hlt18 : k.val - 95 < 18 := by omega
                  simp only [hk64, hkSkip, hk89, hn95, hk113, hk125, hlt18, ↓reduceIte, ↓reduceDIte]
                  exact congrArg (k6Pal24Bit _ _) (Fin.ext (by dsimp; omega))
                · by_cases hkEq113 : k.val = 113
                  · simp [hkEq113]
                  · by_cases hkEq114 : k.val = 114
                    · simp [hkEq114]
                    · by_cases hk119 : k.val < 119
                      · have hk125 : k.val < 125 := by omega
                        have hn18 : ¬ (k.val - 95 < 18) := by omega
                        have hne18 : k.val - 95 ≠ 18 := by omega
                        have hne19 : k.val - 95 ≠ 19 := by omega
                        have hlt24 : k.val - 95 < 24 := by omega
                        simp only [hk64, hkSkip, hk89, hn95, hk113, hkEq113, hkEq114, hk119,
                          hk125, hn18, hne18, hne19, hlt24, ↓reduceIte, ↓reduceDIte]
                        exact congrArg (k6_oneHot4Val _ _) (Fin.ext (by dsimp; omega))
                      · have hn125 : ¬ (k.val < 125) := by omega
                        simp [hk64, hkSkip, hk89, hn95, hk113, hkEq113, hkEq114, hk119, hn125]
    · intro d
      dsimp only [next5c]
      rw [writeReg_apply_of_not_mem _ rOutBTop6 _ _
            (fun ⟨j, hj⟩ ↦ ((hCC.compose_left _).compose_right _).ne d j hj.symm),
          writeReg_apply_of_not_mem _ rDiff6 _ _
            (fun ⟨j, hj⟩ ↦ ((hCC.compose_left _).compose_right _).ne d j hj.symm),
          mkState_dirty]
    · intro w hc hd
      dsimp only [next5c]
      rw [writeReg_apply_of_not_mem _ rOutBTop6 _ w
            (fun ⟨j, hj⟩ ↦ hc ⟨⟨89 + j.val, by omega⟩, hj⟩),
          writeReg_apply_of_not_mem _ rDiff6 _ w
            (fun ⟨j, hj⟩ ↦ hc ⟨⟨119 + j.val, by omega⟩, hj⟩),
          mkState_other rCore rClean hCC γ₀ _ _ w hc hd]
  have hStage5c : K6StageSpec (Var := Var) S_5b (.circuit cStep5c) next5c (fun _ ↦ 1) := by
    refine K6StageSpec.ofCircuit S_5b cStep5c ?_
    rintro α ⟨γ₀, _, rfl⟩
    let α_b := mkState rCore rClean hCC γ₀
      (vClean5b B rOrbit16 rClean γ₀) (vDirty1 rCore rOrbit16 γ₀)
    have hD0 : ∀ j : Fin 6, α_b (rDiff6 j) = 0 := fun j ↦ by
      dsimp only [α_b, rDiff6, rDiff6Of]; rw [QRegister.slice_apply, mkState_clean]
      dsimp [vClean5b]
      have h1 : ¬ (119 + j.val < 64) := by omega
      have h2 : ¬ (119 + j.val < 64 + (30 - B)) := by omega
      have h3 : ¬ (119 + j.val < 89) := by omega
      have h4 : ¬ (119 + j.val < 113) := by omega
      have h5 : 119 + j.val ≠ 113 := by omega
      have h6 : 119 + j.val ≠ 114 := by omega
      have h7 : ¬ (119 + j.val < 119) := by omega
      simp [h1, h2, h3, h4, h5, h6, h7]
    have hOH4 : ∀ k : Fin 4, α_b (rOH4 k) = k6_oneHot4Val (α_b (rP2 0)) (α_b (rP2 1)) k := fun k ↦
      by
      obtain ⟨hp0, hp1⟩ := hP5b γ₀
      dsimp only [α_b, rOH4, rOH4Of]
      rw [hp0, hp1, QRegister.slice_apply, mkState_clean]
      dsimp [vClean5b]
      have h1 : ¬ (115 + k.val < 64) := by omega
      have h2 : ¬ (115 + k.val < 64 + (30 - B)) := by omega
      have h3 : ¬ (115 + k.val < 89) := by omega
      have h4 : ¬ (115 + k.val < 113) := by omega
      have h5 : 115 + k.val ≠ 113 := by omega
      have h6 : 115 + k.val ≠ 114 := by omega
      have h7 : 115 + k.val < 119 := by omega
      simp only [h1, h2, h3, h4, h5, h6, h7, ↓reduceIte, ↓reduceDIte]
      exact congrArg (k6_oneHot4Val _ _) (Fin.ext (by dsimp; omega))
    dsimp only [cStep5c]
    rw [p2t_eval_seq_mulVec,
        k6_cPhaseMux4All6Raw_ket rOH4 rPal18 rDiff6 hOHD hPalD
          (α_b (rP2 0)) (α_b (rP2 1)) α_b hD0 hOH4,
        k6_cXorDiffTop6Raw_ket rDiff6 rOutBTop6 hDT _,
        one_smul]
  let cOH4 := k6_cOneHot4Raw rP2 rOH4 hPOH4
  let hD0NotOH4 : rDiff6 0 ∉ cOH4.support := rDiff6_zero_not_mem_oneHot4 hmClean rClean hPOH4
  let next5b : BitAssignment n → BitAssignment n := fun α ↦
    writeReg α rOH4 (k6_oneHot4Val (α (rP2 0)) (α (rP2 1)))
  have hNext5bEq : ∀ γ₀,
      next5b (mkState rCore rClean hCC γ₀
        (vClean5a B rOrbit16 rClean γ₀) (vDirty1 rCore rOrbit16 γ₀)) =
      mkState rCore rClean hCC γ₀
        (vClean5b B rOrbit16 rClean γ₀) (vDirty1 rCore rOrbit16 γ₀) := by
    intro γ₀
    let α_a := mkState rCore rClean hCC γ₀
      (vClean5a B rOrbit16 rClean γ₀) (vDirty1 rCore rOrbit16 γ₀)
    have hP0 : α_a (rP2 0) = k6P0Bit (k6_qOf rOrbit16 γ₀) (k6_selOf rOrbit16 γ₀) := by
      dsimp only [α_a, rP2, rP2Of]; rw [QRegister.slice_apply]
      change mkState rCore rClean hCC γ₀ (vClean5a B rOrbit16 rClean γ₀)
        (vDirty1 rCore rOrbit16 γ₀) (rClean ⟨113, by omega⟩) = _
      rw [mkState_clean]
      dsimp [vClean5a]
      have a2 : ¬ (113 < 64 + (30 - B)) := by omega
      simp [a2]
    have hP1 : α_a (rP2 1) = k6P1Bit (k6_qOf rOrbit16 γ₀) (k6_selOf rOrbit16 γ₀) := by
      dsimp only [α_a, rP2, rP2Of]; rw [QRegister.slice_apply]
      change mkState rCore rClean hCC γ₀ (vClean5a B rOrbit16 rClean γ₀)
        (vDirty1 rCore rOrbit16 γ₀) (rClean ⟨114, by omega⟩) = _
      rw [mkState_clean]
      dsimp [vClean5a]
      have a2 : ¬ (114 < 64 + (30 - B)) := by omega
      simp [a2]
    dsimp only [α_a] at hP0 hP1
    apply eq_mkState rCore rClean hCC
    · intro k
      by_cases hkOH4 : 115 ≤ k.val ∧ k.val < 119
      · have hEq : rClean k = rOH4 ⟨k.val - 115, by omega⟩ := by
          dsimp only [rOH4, rOH4Of]; rw [QRegister.slice_apply]
          exact congrArg rClean.wires (Fin.ext (by dsimp; omega))
        dsimp only [next5b]
        rw [hEq, writeReg_apply_reg, hP0, hP1]
        dsimp [vClean5b]
        have h1 : ¬ (k.val < 64) := by omega
        have h2 : ¬ (k.val < 64 + (30 - B)) := by omega
        have h3 : ¬ (k.val < 89) := by omega
        have h4 : ¬ (k.val < 113) := by omega
        have h5 : k.val ≠ 113 := by omega
        have h6 : k.val ≠ 114 := by omega
        simp [h1, h2, h3, h4, h5, h6, hkOH4.2]
      · dsimp only [next5b]
        rw [writeReg_apply_of_not_mem _ rOH4 _ (rClean k) (fun ⟨j, hj⟩ ↦ by
          dsimp only [rOH4, rOH4Of] at hj; rw [QRegister.slice_apply] at hj
          have hv := congrArg Fin.val (rClean.wires.injective hj); dsimp at hv; omega),
          mkState_clean]
        dsimp [vClean5a, vClean5b]
        by_cases hk64 : k.val < 64
        · simp [hk64]
        · by_cases hkSkip : k.val < 64 + (30 - B)
          · simp [hk64, hkSkip]
          · by_cases hk89 : k.val < 89
            · simp [hk64, hkSkip, hk89]
            · by_cases hk113 : k.val < 113
              · simp [hk64, hkSkip, hk89, hk113]
              · by_cases hkEq113 : k.val = 113
                · simp [hkEq113]
                · by_cases hkEq114 : k.val = 114
                  · simp [hkEq114]
                  · have hn119 : ¬ (k.val < 119) := by omega
                    simp [hk64, hkSkip, hk89, hk113, hkEq113, hkEq114, hn119]
    · intro d
      dsimp only [next5b]
      rw [writeReg_apply_of_not_mem _ rOH4 _ _
            (fun ⟨j, hj⟩ ↦ ((hCC.compose_left _).compose_right _).ne d j hj.symm),
          mkState_dirty]
    · intro w hc hd
      dsimp only [next5b]
      rw [writeReg_apply_of_not_mem _ rOH4 _ w
            (fun ⟨j, hj⟩ ↦ hc ⟨⟨115 + j.val, by omega⟩, hj⟩),
          mkState_other rCore rClean hCC γ₀ _ _ w hc hd]
  have hStage5b : K6StageSpec S_5a
      (DynCircuitExt.substToffoliCircuit v (rDiff6 0) cOH4 hD0NotOH4)
      next5b (fun _ ↦ 1) := by
    refine K6StageSpec.ofCleanUnitary v
      (PreservesStoreConst.substToffoliCircuit v (rDiff6 0) cOH4 hD0NotOH4)
      (k6_realizesCleanUnitary_ofSubstToffoliCircuit v (QRegister.singleton (rDiff6 0)).wires
        ⟨0, by decide⟩ cOH4 hD0NotOH4)
      ?_ ?_
    · rintro α ⟨γ₀, _, rfl⟩ j
      fin_cases j
      change mkState _ _ _ _ _ _ (rDiff6 0) = 0
      dsimp only [rDiff6, rDiff6Of]
      rw [QRegister.slice_apply]
      change mkState rCore rClean hCC γ₀ (vClean5a B rOrbit16 rClean γ₀)
        (vDirty1 rCore rOrbit16 γ₀) (rClean ⟨119, by omega⟩) = 0
      rw [mkState_clean]
      dsimp [vClean5a]
      have h2 : ¬ (119 < 64 + (30 - B)) := by omega
      simp [h2]
    · rintro α ⟨γ₀, _, rfl⟩
      rw [one_smul]
      apply k6_cOneHot4Raw_ket rP2 rOH4 hPOH4
      intro k
      dsimp only [rOH4, rOH4Of]; rw [QRegister.slice_apply, mkState_clean]
      dsimp [vClean5a]
      have h1 : ¬ (115 + k.val < 64) := by omega
      have h2 : ¬ (115 + k.val < 64 + (30 - B)) := by omega
      have h3 : ¬ (115 + k.val < 89) := by omega
      have h4 : ¬ (115 + k.val < 113) := by omega
      have h5 : 115 + k.val ≠ 113 := by omega
      have h6 : 115 + k.val ≠ 114 := by omega
      simp [h1, h2, h3, h4, h5, h6]
  have hS27Eq : ∀ γ₀,
      vCleanStream B 27 rCore rOrbit16 rClean γ₀ = vClean5a B rOrbit16 rClean γ₀ := by
    intro γ₀; funext k
    dsimp [vCleanStream, vClean5a]
    by_cases hk64 : k.val < 64
    · simp [hk64]
    · by_cases hkSkip : k.val < 64 + (30 - B)
      · simp [hk64, hkSkip]
      · by_cases hk89 : k.val < 89
        · have hlt27 : 2 + (k.val - 64) < 27 := by omega
          simp [hk64, hkSkip, hk89, hlt27]
        · by_cases hk113 : k.val < 113
          · simp [hk64, hkSkip, hk89, hk113]
          · by_cases hkEq113 : k.val = 113
            · simp [hkEq113]
            · by_cases hkEq114 : k.val = 114
              · simp [hkEq114]
              · simp [hk64, hkSkip, hk89, hk113, hkEq113, hkEq114]
  have hStagePredEq : S_s27 = S_5a := by
    funext α
    simp only [S_s27, S_5a, atStage, hS27Eq]
  change K6StageSpec S_s27 _ _ _
  rw [hStagePredEq]
  have h5cd := K6StageSpec.seq hStage5c hStage5d (by
    rintro α ⟨γ₀, hγ₀, rfl⟩; rw [hNext5cEq γ₀]; exact ⟨γ₀, hγ₀, rfl⟩)
  have h5bcd := K6StageSpec.seq hStage5b h5cd (by
    rintro α ⟨γ₀, hγ₀, rfl⟩; rw [hNext5bEq γ₀]; exact ⟨γ₀, hγ₀, rfl⟩)
  refine K6StageSpec.congr h5bcd ?_ ?_
  · rintro α ⟨γ₀, hγ₀, rfl⟩
    rw [hNext5bEq γ₀, hNext5cEq γ₀,
        recoverInit_mkState hmClean rCore rOrbit16 rClean hCO hCC hOC γ₀ hγ₀ _
          (fun k hk ↦ by dsimp [vClean5c]; simp [hk]),
        recoverInit_mkState hmClean rCore rOrbit16 rClean hCO hCC hOC γ₀ hγ₀ _
          (fun k hk ↦ by dsimp [vClean5a]; simp [hk])]
  · rintro α ⟨γ₀, hγ₀, rfl⟩
    rw [one_mul, one_mul, hNext5bEq γ₀, hNext5cEq γ₀]
    obtain ⟨_, _, hSign5a, hg5a, ht5a, _⟩ :=
      mkState_invariants hmClean B hB1 hB29 slot2SwappedTo0 rCore rOrbit16 rClean
        hCO hCC hOC γ₀ hγ₀ (vClean5a B rOrbit16 rClean γ₀)
        (fun k hk ↦ by dsimp [vClean5a]; simp [hk])
    obtain ⟨_, _, hSign5c, hg5c, ht5c, _⟩ :=
      mkState_invariants hmClean B hB1 hB29 slot2SwappedTo0 rCore rOrbit16 rClean
        hCO hCC hOC γ₀ hγ₀ (vClean5c B rOrbit16 rClean γ₀)
        (fun k hk ↦ by dsimp [vClean5c]; simp [hk])
    dsimp only [phTotal]
    rw [hSign5c, hSign5a]
    refine congrArg (fun e : ZMod 2 ↦
      signOf B hB1 hB29 slot2SwappedTo0 rCore rOrbit16 hCO γ₀ * (-1 : ℂ) ^ e.val) ?_
    refine Finset.sum_congr rfl fun m _ ↦ ?_
    rw [hg5c m, hg5a m, ht5c m, ht5a m]
attribute [local irreducible] dPost4dWStateGenOf
theorem dStreamRemWStateGenDyn_stageSpec {Var : Type} [Fintype Var] [DecidableEq Var]
    {n mClean : ℕ} [NeZero (2 ^ n)]
    (B : ℕ) (hB1 : 1 ≤ B) (hB6 : 6 ≤ B) (hB27 : B ≤ 27) (hmClean : 126 ≤ mClean)
    (slot2SwappedTo0 : Bool) (v : Var)
    (rCore : QRegister posCoreWires n) (rOrbit16 : QRegister 16 n) (rClean : QRegister mClean n)
    (hCO : rCore.DisjointWires rOrbit16) (hCC : rCore.DisjointWires rClean)
    (hOC : rOrbit16.DisjointWires rClean)
    (dKick : DynamicCircuit Var n)
    (hStage6 : K6StageSpec
      (atStage hmClean rCore rOrbit16 rClean hCC
        (vClean5 B rOrbit16 rClean) (vDirty1 rCore rOrbit16))
      dKick (fun α ↦ α)
      (signOf B (by omega) (by omega) slot2SwappedTo0 rCore rOrbit16 hCO))
    (dFix : (Fin 27 → Bool) → (Fin 30 → Bool) → (Fin (B + 1) → Bool) → DynamicCircuit Var n)
    (hStageFix : ∀ fStream f5c f7Top,
      K6StageSpec
        (atStage hmClean rCore rOrbit16 rClean hCC (vClean7 rClean)
          (vDirty1 rCore rOrbit16))
        (dFix fStream f5c f7Top)
        (recoverInit rCore rOrbit16 rClean)
        (fun α ↦
          (-1 : ℂ) ^
            ((∑ m : Fin 27,
                if fStream m then gOf rCore rOrbit16 α m + k6_tStreamOf rOrbit16 α m
                else 0) +
             (∑ k : Fin 30,
                if f5c k then k6_meas5cTableBit (k6_qOf rOrbit16 α) (k6_selOf rOrbit16 α) k
                else 0) +
             (∑ j : Fin (B + 1),
                if f7Top j then
                  k6Table31 (k6_qOf rOrbit16 α) (k6_selOf rOrbit16 α) ⟨(30 - B) + j.val, by omega⟩
                else 0)).val)) :
    ∀ (rem : ℕ) (hrem : rem ≤ 27) (fAcc : Fin 27 → Bool)
      (_hfAcc : ∀ m : Fin 27, 27 - rem ≤ m.val → fAcc m = false),
      K6StageSpec
        (atStage hmClean rCore rOrbit16 rClean hCC
          (vCleanStream B (27 - rem) rCore rOrbit16 rClean)
          (vDirty1 rCore rOrbit16))
        (dStreamRemWStateGenDyn B hB1 hB27 hmClean v rCore rClean hCC dKick dFix
          fAcc rem hrem)
        (recoverInit rCore rOrbit16 rClean)
        (fun α ↦
          signOf B hB1 (by omega) slot2SwappedTo0 rCore rOrbit16 hCO α *
          (-1 : ℂ) ^
            (∑ m : Fin 27,
              if m.val < 27 - rem then
                (if fAcc m then
                  gOf rCore rOrbit16 α m + k6_tStreamOf rOrbit16 α m
                 else 0)
              else 0).val)
  | 0, _, fAcc, _ => by
      dsimp only [dStreamRemWStateGenDyn]
      have h0 := dPost4dWStateGenOf_stageSpec B hB6 hB27 hmClean slot2SwappedTo0 v
        rCore rOrbit16 rClean hCO hCC hOC dKick hStage6 dFix hStageFix fAcc
      refine K6StageSpec.congr h0 (fun _ _ ↦ rfl) fun α _ ↦ ?_
      refine congrArg (fun e : ZMod 2 ↦
        signOf B hB1 (by omega) slot2SwappedTo0 rCore rOrbit16 hCO α * (-1 : ℂ) ^ e.val) ?_
      refine Finset.sum_congr rfl fun m _ ↦ ?_
      simp [m.isLt]
  | rem + 1, hrem, fAcc, hfAcc => by
      let idx : ℕ := 27 - (rem + 1)
      have hidx : idx < 27 := by omega
      have hidx_succ : 27 - rem = idx + 1 := by omega
      let col : Fin 27 := ⟨idx, hidx⟩
      dsimp only [dStreamRemWStateGenDyn]
      by_cases hAct : k6ActiveCol B col = true
      · rw [ite_eq_left hAct]
        have hActOr : idx < 2 ∨ 2 + (30 - B) ≤ idx := of_decide_eq_true hAct
        let wStream := wStreamOf hmClean rClean
        let wParity3 := wParity3Of hmClean rClean
        let rOH64 := rOH64Of hmClean rClean
        let rTarget27 := rTarget27Of hmClean rClean
        let rDirty := rDirtyOf rCore
        let hP3Stream := wParity3_ne_wStream hmClean rClean
        let hOHStream := rOH64_ne_wStream hmClean rClean
        let hColStream := rCol64_ne_wStream hmClean rCore rClean hCC col
        let hOHP3 := rOH64_ne_wParity3 hmClean rClean
        let hColP3 : ∀ sl : Fin 64, k6_rCol64 rDirty col sl ≠ wParity3 := fun sl ↦ by
          rw [k6_rCol64_apply]
          exact (hCC.compose_left _).ne _ ⟨125, by omega⟩
        let hOHDirty : rOH64.DisjointWires rDirty := (QRegExt.disjointWires_symm ((hCC.compose_left
          _).compose_right _))
        let hOHCol : rOH64.DisjointWires (k6_rCol64 rDirty col) := by
          rw [QRegister.disjoint_iff]
          intro s₁ s₂
          rw [k6_rCol64_apply]
          exact hOHDirty.ne s₁ _
        let hStreamOut := wStream_ne_rTarget27 hmClean rClean col
        let S_pre := atStage hmClean rCore rOrbit16 rClean hCC
          (vCleanStream B idx rCore rOrbit16 rClean) (vDirty1 rCore rOrbit16)
        let S_mux := atStage hmClean rCore rOrbit16 rClean hCC
          (vCleanStreamMux B idx hidx rCore rOrbit16 rClean) (vDirty1 rCore rOrbit16)
        let S_cnot := atStage hmClean rCore rOrbit16 rClean hCC
          (vCleanStreamCnot B idx hidx rCore rOrbit16 rClean) (vDirty1 rCore rOrbit16)
        let S_post := atStage hmClean rCore rOrbit16 rClean hCC
          (vCleanStream B (idx + 1) rCore rOrbit16 rClean) (vDirty1 rCore rOrbit16)
        let nextMux : BitAssignment n → BitAssignment n := fun α ↦
          Function.update α wStream
            (α (rDirty ⟨idx * 64 + (k6_selOf rOrbit16 α).val, by omega⟩))
        have hMuxEq : ∀ γ₀, s_in hmClean rOrbit16 rClean γ₀ → nextMux (mkState rCore
            rClean hCC γ₀ (vCleanStream B idx rCore rOrbit16 rClean γ₀) (vDirty1 rCore
            rOrbit16 γ₀)) = mkState rCore rClean hCC γ₀
            (vCleanStreamMux B idx hidx rCore rOrbit16 rClean γ₀)
            (vDirty1 rCore rOrbit16 γ₀) := by
          intro γ₀ hγ₀
          let α₀ := mkState rCore rClean hCC γ₀
            (vCleanStream B idx rCore rOrbit16 rClean γ₀) (vDirty1 rCore rOrbit16 γ₀)
          obtain ⟨_, hSel0, _, _, _, _⟩ :=
            mkState_invariants hmClean B hB1 (by omega) slot2SwappedTo0 rCore rOrbit16 rClean
              hCO hCC hOC γ₀ hγ₀ (vCleanStream B idx rCore rOrbit16 rClean γ₀)
              (fun k hk ↦ by dsimp [vCleanStream]; simp [hk])
          have hBufVal : α₀ (rDirty ⟨idx * 64 + (k6_selOf rOrbit16 α₀).val, by omega⟩) =
              gBit rCore rOrbit16 γ₀ col +
                k6BufBit (k6_qOf rOrbit16 γ₀) (k6_selOf rOrbit16 γ₀) col := by
            dsimp only [α₀]
            simp only [hSel0]
            let flat : Fin 1728 := ⟨idx * 64 + (k6_selOf rOrbit16 γ₀).val, by omega⟩
            rw [mkState_dirty rCore rClean hCC γ₀ _ _ flat]
            dsimp only [vDirty1, gBit, col]
            have hdiv : flat.val / 64 = idx := by
              have := (k6_selOf rOrbit16 γ₀).isLt; dsimp [flat]; omega
            have hmod : flat.val % 64 = (k6_selOf rOrbit16 γ₀).val := by
              have := (k6_selOf rOrbit16 γ₀).isLt; dsimp [flat]; omega
            have hcolEq : (⟨flat.val / 64, by omega⟩ : Fin 27) = col := Fin.ext hdiv
            have hslEq : (⟨flat.val % 64, Nat.mod_lt _ (by decide)⟩ : Fin 64) =
                k6_selOf rOrbit16 γ₀ := Fin.ext hmod
            rw [hslEq, hcolEq]
          dsimp only [α₀] at hBufVal
          exact update_clean_mkState rCore rClean hCC γ₀ _ _ _ ⟨115, by omega⟩ _
            (by rw [hBufVal]; simp [vCleanStreamMux, col])
            (fun k hk ↦ by
              have hk115 : k.val ≠ 115 := Fin.val_ne_of_ne hk
              simp [vCleanStreamMux, hk115])
        have hStageMux : K6StageSpec (Var := Var) S_pre
            (.circuit (p2t_cPhaseMuxCol64 0 wStream wParity3 rOH64 (k6_rCol64 rDirty col)
              hP3Stream hOHStream hColStream hOHP3))
            nextMux (fun _ ↦ 1) := by
          refine K6StageSpec.ofCircuit S_pre _ ?_
          rintro α ⟨γ₀, hγ₀, rfl⟩
          obtain ⟨_, hSel0, _, _, _, hOH0⟩ :=
            mkState_invariants hmClean B hB1 (by omega) slot2SwappedTo0 rCore rOrbit16 rClean
              hCO hCC hOC γ₀ hγ₀ (vCleanStream B idx rCore rOrbit16 rClean γ₀)
              (fun k hk ↦ by dsimp [vCleanStream]; simp [hk])
          rw [one_smul,
              p2t_cPhaseMuxCol64_ket 0 wStream wParity3 rOH64 (k6_rCol64 rDirty col)
                hP3Stream hOHStream hColStream hOHP3 hColP3 hOHCol
                (k6_selOf rOrbit16 γ₀) _
                (by
                  dsimp only [wStream, wStreamOf]; rw [mkState_clean]
                  dsimp [vCleanStream]
                  have h2 : ¬ (115 < 64 + (30 - B)) := by omega
                  simp [h2])
                (by
                  dsimp only [wParity3, wParity3Of]; rw [mkState_clean]
                  dsimp [vCleanStream]
                  have h2 : ¬ (125 < 64 + (30 - B)) := by omega
                  simp [h2])
                hOH0 (fun _ hsl ↦ absurd hsl (Nat.not_lt_zero _)),
              k6_rCol64_apply]
          dsimp only [nextMux, col]
          simp only [hSel0]
        let nextCnot : BitAssignment n → BitAssignment n := fun α ↦
          Function.update α (rTarget27 col) (α (rTarget27 col) + α wStream)
        have hCnotEq : ∀ γ₀, nextCnot (mkState rCore rClean hCC γ₀ (vCleanStreamMux B
            idx hidx rCore rOrbit16 rClean γ₀) (vDirty1 rCore rOrbit16 γ₀)) = mkState
            rCore rClean hCC γ₀ (vCleanStreamCnot B idx hidx rCore rOrbit16 rClean γ₀)
            (vDirty1 rCore rOrbit16 γ₀) := by
          intro γ₀
          have hWVal : mkState rCore rClean hCC γ₀
              (vCleanStreamMux B idx hidx rCore rOrbit16 rClean γ₀)
              (vDirty1 rCore rOrbit16 γ₀) wStream = gBit rCore rOrbit16 γ₀ col +
              k6BufBit (k6_qOf rOrbit16 γ₀) (k6_selOf rOrbit16 γ₀) col := by
            dsimp [wStream, wStreamOf]; rw [mkState_clean]
            dsimp [vCleanStreamMux, col]
          obtain ⟨k, hHit⟩ := rTarget27Of_mem_clean hmClean rClean col
          dsimp only [nextCnot]
          rw [← hHit]
          refine update_clean_mkState rCore rClean hCC γ₀ _ _ _ k _ ?_ ?_
          · rw [hWVal]
            by_cases hlt2 : idx < 2
            · have hT := rTarget27Of_apply_lt2 hmClean rClean col hlt2
              dsimp only [col] at hT
              rw [hT] at hHit
              have hkEq : k.val = 113 + idx := congrArg Fin.val (rClean.wires.injective hHit)
              by_cases hidx0 : idx = 0
              · have hk113 : k.val = 113 := by omega
                have hcol0 : col = ⟨0, by decide⟩ := Fin.ext hidx0
                rw [mkState_clean, hcol0, k6BufBit_zero]
                dsimp only [vCleanStreamMux, vCleanStreamCnot, vCleanStream]
                have ha : k.val ≠ 115 := by omega
                have hb : ¬ (k.val < 64) := by omega
                have hb0 : ¬ (k.val < 64 + (30 - B)) := by omega
                have hc : ¬ (k.val < 89) := by omega
                have hd : ¬ (k.val < 113) := by omega
                have he : ¬ (0 < idx) := by omega
                have he' : 0 < idx + 1 := by omega
                simp only [ha, hb, hb0, hc, hd, ↓reduceIte, ↓reduceDIte]
                rw [ite_eq_left hk113, ite_eq_left hk113, ite_eq_right he, ite_eq_left he',
                    ← add_assoc, CharTwo.add_self_eq_zero, zero_add]
              · have hidx1 : idx = 1 := by omega
                have hk114 : k.val = 114 := by omega
                have hkne113 : k.val ≠ 113 := by omega
                have hcol1 : col = ⟨1, by decide⟩ := Fin.ext hidx1
                rw [mkState_clean, hcol1, k6BufBit_one]
                dsimp only [vCleanStreamMux, vCleanStreamCnot, vCleanStream]
                have ha : k.val ≠ 115 := by omega
                have hb : ¬ (k.val < 64) := by omega
                have hb0 : ¬ (k.val < 64 + (30 - B)) := by omega
                have hc : ¬ (k.val < 89) := by omega
                have hd : ¬ (k.val < 113) := by omega
                have he : ¬ (1 < idx) := by omega
                have he' : 1 < idx + 1 := by omega
                simp only [ha, hb, hb0, hc, hd, ↓reduceIte, ↓reduceDIte]
                rw [ite_eq_right hkne113, ite_eq_right hkne113, ite_eq_left hk114,
                    ite_eq_left hk114, ite_eq_right he, ite_eq_left he',
                    ← add_assoc, CharTwo.add_self_eq_zero, zero_add]
            · have hgeSkip : 2 + (30 - B) ≤ idx := hActOr.resolve_left hlt2
              have hT := rTarget27Of_apply_ge2 hmClean rClean col hlt2
              dsimp only [col] at hT
              rw [hT] at hHit
              have hkEq : k.val = 64 + (idx - 2) := congrArg Fin.val (rClean.wires.injective hHit)
              rw [mkState_clean]
              dsimp [vCleanStreamMux, vCleanStreamCnot, vCleanStream]
              have ha : k.val ≠ 115 := by omega
              have hb : ¬ (k.val < 64) := by omega
              have hb0 : ¬ (k.val < 64 + (30 - B)) := by omega
              have hc : k.val < 89 := by omega
              have hd : ¬ (2 + (k.val - 64) < idx) := by omega
              have hd' : 2 + (k.val - 64) < idx + 1 := by omega
              simp only [ha, hb, hb0, hc, hd, hd', ↓reduceIte, ↓reduceDIte]
              have hcolEq : (⟨2 + (k.val - 64), by omega⟩ : Fin 27) = col :=
                Fin.ext (by dsimp [col]; omega)
              rw [hcolEq, ← add_assoc, CharTwo.add_self_eq_zero, zero_add]
          · have hk₀ := hHit
            clear hHit
            intro k hk'
            have hHit : rClean k ≠ rTarget27 col :=
              fun heq ↦ hk' (rClean.wires.injective (heq.trans hk₀.symm))
            dsimp [vCleanStreamMux, vCleanStreamCnot]
            by_cases hk115 : k.val = 115
            · simp [hk115]
            · simp only [hk115, ↓reduceIte]
              dsimp [vCleanStream]
              by_cases hk64 : k.val < 64
              · simp [hk64]
              · by_cases hkSkip : k.val < 64 + (30 - B)
                · simp [hk64, hkSkip]
                · by_cases hk89 : k.val < 89
                  · have hneIdx : 2 + (k.val - 64) ≠ idx := fun heq ↦ hHit (by
                      have hge2 : ¬ (col.val < 2) := by dsimp [col]; omega
                      rw [rTarget27Of_apply_ge2 hmClean rClean col hge2]
                      exact congrArg rClean.wires (Fin.ext (by dsimp [col]; omega)))
                    have hiff : (2 + (k.val - 64) < idx) ↔ (2 + (k.val - 64) < idx + 1) := by
                      omega
                    simp [hk64, hkSkip, hk89, hiff]
                  · by_cases hk113 : k.val < 113
                    · simp [hk64, hkSkip, hk89, hk113]
                    · by_cases hkEq113 : k.val = 113
                      · have hne0 : idx ≠ 0 := fun h0 ↦ hHit (by
                          have hlt2 : col.val < 2 := by dsimp [col]; omega
                          rw [rTarget27Of_apply_lt2 hmClean rClean col hlt2]
                          exact congrArg rClean.wires (Fin.ext (by dsimp [col]; omega)))
                        have hiff0 : (0 < idx) ↔ (0 < idx + 1) := by omega
                        simp [hkEq113, hiff0]
                      · by_cases hkEq114 : k.val = 114
                        · have hne1 : idx ≠ 1 := fun h1 ↦ hHit (by
                            have hlt2 : col.val < 2 := by dsimp [col]; omega
                            rw [rTarget27Of_apply_lt2 hmClean rClean col hlt2]
                            exact congrArg rClean.wires (Fin.ext (by dsimp [col]; omega)))
                          have hiff1 : (1 < idx) ↔ (1 < idx + 1) := by omega
                          simp [hkEq114, hiff1]
                        · simp [hk64, hkSkip, hk89, hk113, hkEq113, hkEq114]
        have hStageCnot : K6StageSpec (Var := Var) S_mux
            (.circuit (Circuit.CNOT wStream (rTarget27 col) hStreamOut))
            nextCnot (fun _ ↦ 1) :=
          K6StageSpec.ofCircuit S_mux _ fun α _ ↦ by
            rw [one_smul, p2t_ket_CNOT]
        have hWStreamEq : ∀ γ₀, writeReg (mkState rCore rClean hCC γ₀ (vCleanStreamCnot
            B idx hidx rCore rOrbit16 rClean γ₀) (vDirty1 rCore rOrbit16 γ₀))
            (QRegister.singleton wStream) (fun _ ↦ 0) = mkState rCore rClean hCC γ₀
            (vCleanStream B (idx + 1) rCore rOrbit16 rClean γ₀)
            (vDirty1 rCore rOrbit16 γ₀) := by
          intro γ₀
          apply eq_mkState rCore rClean hCC
          · intro k
            by_cases hk115 : k.val = 115
            · have hEq : rClean k = (QRegister.singleton wStream) 0 :=
                congrArg rClean.wires (Fin.ext hk115)
              rw [hEq, writeReg_apply_reg]
              dsimp [vCleanStream]
              have h1 : ¬ (115 < 64) := by decide
              have h2 : ¬ (115 < 64 + (30 - B)) := by omega
              have h3 : ¬ (115 < 89) := by decide
              have h4 : ¬ (115 < 113) := by decide
              have h5 : (115 : ℕ) ≠ 113 := by decide
              have h6 : (115 : ℕ) ≠ 114 := by decide
              simp [hk115, h1, h2, h3, h4, h5, h6]
            · rw [writeReg_apply_of_not_mem _ (QRegister.singleton wStream) _ (rClean k)
                (fun ⟨j, hj⟩ ↦ by
                  fin_cases j
                  exact rClean.wires.injective.ne (fun h ↦ hk115 (congrArg Fin.val h).symm) hj),
                mkState_clean]
              dsimp [vCleanStreamCnot]; simp [hk115]
          · intro d
            rw [writeReg_apply_of_not_mem _ (QRegister.singleton wStream) _ _
                  (fun ⟨j, hj⟩ ↦ by
                    fin_cases j; exact (hCC.compose_left _).ne d ⟨115, by omega⟩ hj.symm),
                mkState_dirty]
          · intro w hc hd
            rw [writeReg_apply_of_not_mem _ (QRegister.singleton wStream) _ w
                  (fun ⟨j, hj⟩ ↦ by fin_cases j; exact hc ⟨⟨115, by omega⟩, hj⟩),
                mkState_other rCore rClean hCC γ₀ _ _ w hc hd]
        have hContIH : ∀ fBit : Fin 1 → Bool, K6StageSpec S_post (dStreamRemWStateGenDyn B
            hB1 hB27 hmClean v rCore rClean hCC dKick dFix (Function.update fAcc col (fBit 0))
            rem (Nat.le_of_succ_le hrem)) (recoverInit rCore rOrbit16 rClean) (fun α ↦
            signOf B hB1 (by omega) slot2SwappedTo0 rCore rOrbit16 hCO α * (-1 : ℂ) ^ (∑ m
            : Fin 27, if m.val < idx + 1 then (if Function.update fAcc col (fBit 0) m then
            gOf rCore rOrbit16 α m + k6_tStreamOf rOrbit16 α m else 0) else 0).val) := by
          intro fBit
          have ih := dStreamRemWStateGenDyn_stageSpec B hB1 hB6 hB27 hmClean slot2SwappedTo0 v
            rCore rOrbit16 rClean hCO hCC hOC dKick hStage6 dFix hStageFix rem (Nat.le_of_succ_le
              hrem)
            (Function.update fAcc col (fBit 0))
            (fun m hm ↦ by
              rw [hidx_succ] at hm
              have hne : m ≠ col := fun h ↦ by subst h; dsimp [col] at hm; omega
              rw [Function.update_of_ne hne]
              exact hfAcc m (by omega))
          simpa only [hidx_succ] using ih
        let phMeas : BitAssignment n → ℂ := fun α ↦ signOf B hB1 (by omega) slot2SwappedTo0
            rCore rOrbit16 hCO α * (-1 : ℂ) ^ (∑ m : Fin 27, if m.val < idx then (if fAcc m
            then gOf rCore rOrbit16 α m + k6_tStreamOf rOrbit16 α m else 0) else 0).val
        have hStageMeas : K6StageSpec S_cnot (DynCircuitExt.measureXResetAndBranch v 1
            (QRegister.singleton wStream) fun fBit ↦ dStreamRemWStateGenDyn B hB1 hB27
            hmClean v rCore rClean hCC dKick dFix (Function.update fAcc col (fBit 0)) rem
            (Nat.le_of_succ_le hrem)) (recoverInit rCore rOrbit16 rClean) phMeas := by
          have hM := K6StageSpec.measureXReset
            (S_pre := S_cnot) (S_post := S_post) (phase_total := phMeas)
            v (QRegister.singleton wStream)
            (by rintro α ⟨γ₀, hγ₀, rfl⟩; rw [hWStreamEq γ₀]; exact ⟨γ₀, hγ₀, rfl⟩)
            hContIH
            (by
              rintro fBit α ⟨γ₀, hγ₀, rfl⟩
              obtain ⟨_, _, hSignC, hgC, htC, _⟩ :=
                mkState_invariants hmClean B hB1 (by omega) slot2SwappedTo0
                  rCore rOrbit16 rClean hCO hCC hOC γ₀ hγ₀
                  (vCleanStreamCnot B idx hidx rCore rOrbit16 rClean γ₀)
                  (fun k hk ↦ by
                    dsimp [vCleanStreamCnot, vCleanStream]
                    have : k.val ≠ 115 := by omega
                    simp [this, hk])
              obtain ⟨_, _, hSignP, hgP, htP, _⟩ :=
                mkState_invariants hmClean B hB1 (by omega) slot2SwappedTo0
                  rCore rOrbit16 rClean hCO hCC hOC γ₀ hγ₀
                  (vCleanStream B (idx + 1) rCore rOrbit16 rClean γ₀)
                  (fun k hk ↦ by dsimp [vCleanStream]; simp [hk])
              rw [hWStreamEq γ₀, k6_prod_ite_neg_one_pow]
              dsimp only [phMeas]
              have hSing0 : mkState rCore rClean hCC γ₀
                  (vCleanStreamCnot B idx hidx rCore rOrbit16 rClean γ₀)
                  (vDirty1 rCore rOrbit16 γ₀) ((QRegister.singleton wStream) 0) = gBit
                  rCore rOrbit16 γ₀ col + k6_tStreamOf rOrbit16 γ₀ col := by
                change mkState _ _ _ _ _ _ wStream = _
                dsimp [wStream, wStreamOf]; rw [mkState_clean]
                dsimp [vCleanStreamCnot, k6_tStreamOf, col]
              have hSum1 : (∑ b : Fin 1, if fBit b then mkState rCore rClean hCC γ₀
                  (vCleanStreamCnot B idx hidx rCore rOrbit16 rClean γ₀) (vDirty1 rCore
                  rOrbit16 γ₀) ((QRegister.singleton wStream) b) else 0) = (if fBit 0 then
                  gBit rCore rOrbit16 γ₀ col + k6_tStreamOf rOrbit16 γ₀ col else 0) := by
                rw [Fin.sum_univ_one, hSing0]
              rw [hSum1, hSignP, hSignC]
              let zIdx : ZMod 2 := if fBit 0 then gBit rCore rOrbit16 γ₀ col + k6_tStreamOf
                  rOrbit16 γ₀ col else 0
              let sPre : ZMod 2 := ∑ m : Fin 27, if m.val < idx then (if fAcc m then gBit
                  rCore rOrbit16 γ₀ m + k6_tStreamOf rOrbit16 γ₀ m else 0) else 0
              have hSplitSum : (∑ m : Fin 27, if m.val < idx + 1 then (if Function.update fAcc
                  col (fBit 0) m then gOf rCore rOrbit16 (mkState rCore rClean hCC γ₀
                  (vCleanStream B (idx + 1) rCore rOrbit16 rClean γ₀) (vDirty1 rCore
                  rOrbit16 γ₀)) m + k6_tStreamOf rOrbit16 (mkState rCore rClean hCC γ₀
                  (vCleanStream B (idx + 1) rCore rOrbit16 rClean γ₀) (vDirty1 rCore
                  rOrbit16 γ₀)) m else 0) else 0) = sPre + zIdx := by
                have hCongr : (∑ m : Fin 27, if m.val < idx + 1 then (if Function.update fAcc
                    col (fBit 0) m then gOf rCore rOrbit16 (mkState rCore rClean hCC γ₀
                    (vCleanStream B (idx + 1) rCore rOrbit16 rClean γ₀) (vDirty1 rCore
                    rOrbit16 γ₀)) m + k6_tStreamOf rOrbit16 (mkState rCore rClean hCC γ₀
                    (vCleanStream B (idx + 1) rCore rOrbit16 rClean γ₀) (vDirty1 rCore
                    rOrbit16 γ₀)) m else 0) else 0) = (∑ m : Fin 27, ((if m.val < idx then (if
                    fAcc m then gBit rCore rOrbit16 γ₀ m + k6_tStreamOf rOrbit16 γ₀ m else
                    0) else 0) + (if m = col then zIdx else 0))) := by
                  refine Finset.sum_congr rfl fun m _ ↦ ?_
                  rw [hgP m, htP m]
                  by_cases hmb : m = col
                  · subst hmb
                    have hnlt : ¬ (col.val < idx) := by dsimp [col]; omega
                    have hlt1 : col.val < idx + 1 := by dsimp [col]; omega
                    simp [hnlt, hlt1, zIdx]
                  · have hneVal : m.val ≠ idx := fun h ↦ hmb (Fin.ext h)
                    have hiff : m.val < idx + 1 ↔ m.val < idx := by omega
                    simp [hmb, hiff]
                rw [hCongr, Finset.sum_add_distrib, Finset.sum_ite_eq',
                    ite_eq_left (Finset.mem_univ col)]
              have hPreC : (∑ m : Fin 27, if m.val < idx then (if fAcc m then gOf rCore
                  rOrbit16 (mkState rCore rClean hCC γ₀ (vCleanStreamCnot B idx hidx
                  rCore rOrbit16 rClean γ₀) (vDirty1 rCore rOrbit16 γ₀)) m + k6_tStreamOf
                  rOrbit16 (mkState rCore rClean hCC γ₀ (vCleanStreamCnot B idx hidx
                  rCore rOrbit16 rClean γ₀) (vDirty1 rCore rOrbit16 γ₀)) m else 0) else 0)
                  = sPre := by
                refine Finset.sum_congr rfl fun m _ ↦ ?_
                rw [hgC m, htC m]
              rw [hSplitSum, hPreC]
              exact neg_one_pow_cancel _ zIdx sPre)
          refine K6StageSpec.congr hM ?_ (fun _ _ ↦ rfl)
          rintro α ⟨γ₀, hγ₀, rfl⟩
          rw [hWStreamEq γ₀,
              recoverInit_mkState hmClean rCore rOrbit16 rClean hCO hCC hOC γ₀ hγ₀ _
                (fun k hk ↦ by dsimp [vCleanStream]; simp [hk]),
              recoverInit_mkState hmClean rCore rOrbit16 rClean hCO hCC hOC γ₀ hγ₀ _
                (fun k hk ↦ by
                  dsimp [vCleanStreamCnot, vCleanStream]
                  have : k.val ≠ 115 := by omega
                  simp [this, hk])]
        have hSeq2 := K6StageSpec.seq hStageCnot hStageMeas (by
          rintro α ⟨γ₀, hγ₀, rfl⟩
          rw [hCnotEq γ₀]; exact ⟨γ₀, hγ₀, rfl⟩)
        have hSeq1 := K6StageSpec.seq hStageMux hSeq2 (by
          rintro α ⟨γ₀, hγ₀, rfl⟩
          rw [hMuxEq γ₀ hγ₀]; exact ⟨γ₀, hγ₀, rfl⟩)
        refine K6StageSpec.congr hSeq1 ?_ ?_
        · rintro α ⟨γ₀, hγ₀, rfl⟩
          rw [hMuxEq γ₀ hγ₀, hCnotEq γ₀,
              recoverInit_mkState hmClean rCore rOrbit16 rClean hCO hCC hOC γ₀ hγ₀ _
                (fun k hk ↦ by
                  dsimp [vCleanStreamCnot, vCleanStream]
                  have : k.val ≠ 115 := by omega
                  simp [this, hk]),
              recoverInit_mkState hmClean rCore rOrbit16 rClean hCO hCC hOC γ₀ hγ₀ _
                (fun k hk ↦ by dsimp [vCleanStream]; simp [hk])]
        · rintro α ⟨γ₀, hγ₀, rfl⟩
          rw [one_mul, one_mul, hMuxEq γ₀ hγ₀, hCnotEq γ₀]
          obtain ⟨_, _, hSign0, hg0, ht0, _⟩ :=
            mkState_invariants hmClean B hB1 (by omega) slot2SwappedTo0
              rCore rOrbit16 rClean hCO hCC hOC γ₀ hγ₀
              (vCleanStream B idx rCore rOrbit16 rClean γ₀)
              (fun k hk ↦ by dsimp [vCleanStream]; simp [hk])
          obtain ⟨_, _, hSignC, hgC, htC, _⟩ :=
            mkState_invariants hmClean B hB1 (by omega) slot2SwappedTo0
              rCore rOrbit16 rClean hCO hCC hOC γ₀ hγ₀
              (vCleanStreamCnot B idx hidx rCore rOrbit16 rClean γ₀)
              (fun k hk ↦ by
                dsimp [vCleanStreamCnot, vCleanStream]
                have : k.val ≠ 115 := by omega
                simp [this, hk])
          dsimp only [phMeas, idx]
          rw [hSignC, hSign0]
          refine congrArg (fun e : ZMod 2 ↦
            signOf B hB1 (by omega) slot2SwappedTo0 rCore rOrbit16 hCO γ₀ * (-1 : ℂ) ^ e.val) ?_
          refine Finset.sum_congr rfl fun m _ ↦ ?_
          rw [hgC m, hg0 m, htC m, ht0 m]
      · rw [ite_eq_right hAct]
        have hNotAct : ¬ (idx < 2 ∨ 2 + (30 - B) ≤ idx) := fun h ↦ hAct (decide_eq_true h)
        have hStreamEq : vCleanStream B idx rCore rOrbit16 rClean = vCleanStream B
            (idx + 1) rCore rOrbit16 rClean := by
          funext γ₀ k
          dsimp [vCleanStream]
          by_cases hk64 : k.val < 64
          · simp [hk64]
          · by_cases hkSkip : k.val < 64 + (30 - B)
            · simp [hk64, hkSkip]
            · by_cases hk89 : k.val < 89
              · have hn1 : ¬ (2 + (k.val - 64) < idx) := by omega
                have hn2 : ¬ (2 + (k.val - 64) < idx + 1) := by omega
                simp [hk64, hkSkip, hk89, hn1, hn2]
              · by_cases hk113 : k.val < 113
                · simp [hk64, hkSkip, hk89, hk113]
                · by_cases hkEq113 : k.val = 113
                  · have hp1 : 0 < idx := by omega
                    simp [hkEq113, hp1]
                  · by_cases hkEq114 : k.val = 114
                    · have hp1 : 1 < idx := by omega
                      have hp2 : 1 < idx + 1 := by omega
                      simp [hkEq114, hp1, hp2]
                    · simp [hk64, hkSkip, hk89, hk113, hkEq113, hkEq114]
        have ih := dStreamRemWStateGenDyn_stageSpec B hB1 hB6 hB27 hmClean slot2SwappedTo0 v
          rCore rOrbit16 rClean hCO hCC hOC dKick hStage6 dFix hStageFix rem (Nat.le_of_succ_le
            hrem) fAcc
          (fun m hm ↦ hfAcc m (by omega))
        rw [hidx_succ, ← hStreamEq] at ih
        refine K6StageSpec.congr ih (fun _ _ ↦ rfl) fun α _ ↦ ?_
        refine congrArg (fun e : ZMod 2 ↦
          signOf B hB1 (by omega) slot2SwappedTo0 rCore rOrbit16 hCO α * (-1 : ℂ) ^ e.val) ?_
        change (∑ m : Fin 27, if m.val < idx + 1 then (if fAcc m then gOf rCore rOrbit16 α
          m + k6_tStreamOf rOrbit16 α m else 0) else 0) = ∑ m : Fin 27, if m.val < idx then
          (if fAcc m then gOf rCore rOrbit16 α m + k6_tStreamOf rOrbit16 α m else 0) else 0
        refine Finset.sum_congr rfl fun m _ ↦ ?_
        by_cases hmCol : m = col
        · subst hmCol
          have hf0 : fAcc col = false := hfAcc col (le_refl idx)
          simp [hf0]
        · have hne : m.val ≠ idx := fun h ↦ hmCol (Fin.ext h)
          have hiff : m.val < idx + 1 ↔ m.val < idx := by omega
          simp [hiff]
end ConfigMidK6WState2350
end MidK6WState2350
end
end Leaf2MidK6WState2350Bridge

noncomputable section Leaf2MidK6Fix6At131Opt

section
set_option exponentiation.threshold 256
set_option maxRecDepth 65536
noncomputable section
namespace Leaf2MidK6Fix6At131Opt
open Operator QProg Matrix Circuit Qubit HermitianMat PrimitiveGate Real _root_.DynamicCircuit
  DynCircuitExt
open scoped Matrix ComplexOrder MatrixOrder Circuit.Notation BigOperators
open SpecsAux SpecsAux.SpecMirror
-- Root solution namespace already active.
open OctahedralOrbit hiding ket_X ket_CNOT
open Dyadic128CoulombMath
open Dyadic128OrbitTableCert
open MeasureBranchHadamardSem (bit_cases ket_X ket_CNOT)
open PosSlots24BranchConcrete
open BchCubeDecoder hiding ket_diagonalSignUnitaryN
open StreamingBchComparator
open PosSlots24SpectatorPrunedPhase
open PosSlots24SpectatorPrunedPhase.MidK6Sub252
open PrunedQromLookup
open TempPhaseProg (neg_one_pow_zmod2_mul)
open MultiBankWStateRouter
open MidK6UnbufOpt
local instance (priority := 100000) instNeZeroTwoPowM2 {k : ℕ} : NeZero (2 ^ k) :=
  ⟨pow_ne_zero k two_ne_zero⟩
attribute [local irreducible] k6SuperRow w128OrbitBiasedQ30
def l26_uncomputeSandwichPosDyn {Var : Type} {n : ℕ} (v : Var) (c₁ c₂ anc : Wire n)
    (h₁₂ : c₁ ≠ c₂) (h₁a : c₁ ≠ anc) (h₂a : c₂ ≠ anc) (dBody : DynamicCircuit Var n) :
    DynamicCircuit Var n := .seq (DynamicCircuit.andUncompute v c₁ c₂ anc h₁₂)
    (.seq dBody (DynamicCircuit.andCompute c₁ c₂ anc h₁a h₂a))
theorem count_l26_uncomputeSandwichPosDyn {Var : Type} {n : ℕ} (v : Var) (c₁ c₂ anc : Wire n)
    (h₁₂ : c₁ ≠ c₂) (h₁a : c₁ ≠ anc) (h₂a : c₂ ≠ anc) (dBody : DynamicCircuit Var n) :
    (l26_uncomputeSandwichPosDyn v c₁ c₂ anc h₁₂ h₁a h₂a dBody).count .T = 4 + dBody.count .T
    ∧ (l26_uncomputeSandwichPosDyn v c₁ c₂ anc h₁₂ h₁a h₂a dBody).count .TOFF = dBody.count
    .TOFF := by
  dsimp only [l26_uncomputeSandwichPosDyn]
  simp only [DynamicCircuit.count, DynamicCircuit.count_andCompute_t,
    DynamicCircuit.count_andUncompute_t, DynamicCircuit.count_andCompute_toff,
    DynamicCircuit.count_andUncompute_toff]
  exact ⟨by omega, by omega⟩
theorem l26_uncomputeSandwichPosDyn_realizes {Var : Type} [Fintype Var] [DecidableEq Var]
    {n : ℕ} (v : Var) (c₁ c₂ anc : Wire n) (h₁₂ : c₁ ≠ c₂) (h₁a : c₁ ≠ anc) (h₂a : c₂ ≠ anc)
    {W : Wire n → Prop} (hWanc : W anc) {S_pre S_clean : BitAssignment n → Prop}
    {dBody : DynamicCircuit Var n} {U_target : Unitary (2 ^ n)}
    (hDiag : p2t_DiagIndepOf W U_target)
    (hAncEq : ∀ β : BitAssignment n, S_pre β → β anc = β c₁ * β c₂)
    (hClean0 : ∀ γ : BitAssignment n, S_clean γ → γ anc = 0) (hFwd : ∀ β : BitAssignment n,
    S_pre β → S_clean (Function.update β anc 0)) (hdBody : p2t_RealizesConstCleanUnitary
    (p2t_ketPredProj S_clean) dBody U_target) : p2t_RealizesConstCleanUnitary
    (p2t_ketPredProj S_pre) (l26_uncomputeSandwichPosDyn v c₁ c₂ anc h₁₂ h₁a h₂a dBody)
    U_target := by
  classical
  obtain ⟨φ, hφKet, hφIndep⟩ := hDiag
  let P_pre := p2t_ketPredProj S_pre
  let P_clean := p2t_ketPredProj S_clean
  let P₀ := (QRegister.singleton anc).basisOutcomeProjector 0
  let T_anc := (Circuit.TOFF c₁ c₂ anc h₁₂ h₁a h₂a).eval
  have hPreH : P_preᴴ = P_pre := p2t_ketPredProj_conjTranspose S_pre
  have hCleanH : P_cleanᴴ = P_clean := p2t_ketPredProj_conjTranspose S_clean
  have hP₀H : P₀ᴴ = P₀ := QRegister.basisOutcomeProjector_conjTranspose _ 0
  have hP₀_eq : P₀ = p2t_ketPredProj (fun β ↦ β anc = 0) := by
    apply MeasureBranchHadamardSem.matrix_ext_ket; intro β
    rw [mbh_ket_eq_ket, p2t_ket_projector_zero, p2t_ketPredProj_mul_ket]
  have hP₀_clean : P₀ * P_clean = P_clean := by
    rw [hP₀_eq]; exact p2t_ketPredProj_mul_imp hClean0
  have hClean_P₀ : P_clean * P₀ = P_clean := by
    rw [hP₀_eq]; exact p2t_ketPredProj_mul_imp_right hClean0
  have hT_self : T_anc.1 * T_anc.1 = 1 := by
    apply MeasureBranchHadamardSem.matrix_ext_ket; intro β
    rw [mbh_ket_eq_ket, ← Matrix.mulVec_mulVec, Matrix.one_mulVec]
    dsimp only [T_anc]
    rw [p2t_ket_TOFF, p2t_ket_TOFF, Function.update_self,
      Function.update_of_ne h₁a, Function.update_of_ne h₂a,
      add_assoc, CharTwo.add_self_eq_zero, add_zero, Function.update_idem, Function.update_eq_self]
  have hT_symm : T_anc.1ᴴ = T_anc.1 := by
    calc T_anc.1ᴴ = T_anc.1ᴴ * 1 := (Matrix.mul_one _).symm
      _ = T_anc.1ᴴ * (T_anc.1 * T_anc.1) := by rw [hT_self]
      _ = (T_anc.1ᴴ * T_anc.1) * T_anc.1 := (Matrix.mul_assoc _ _ _).symm
      _ = 1 * T_anc.1 := by
          have hu : T_anc.1ᴴ * T_anc.1 = 1 := T_anc.2.1
          rw [hu]
      _ = T_anc.1 := Matrix.one_mul _
  have hClean_T_pre : P_clean * (T_anc.1 * P_pre) = T_anc.1 * P_pre := by
    apply MeasureBranchHadamardSem.matrix_ext_ket; intro β
    rw [mbh_ket_eq_ket, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    dsimp only [P_pre, P_clean, T_anc]
    rw [p2t_ketPredProj_mul_ket]
    by_cases hs : S_pre β
    · have h0 : β anc + β c₁ * β c₂ = 0 := by
        rw [hAncEq β hs, CharTwo.add_self_eq_zero]
      rw [ite_eq_left hs, p2t_ket_TOFF, h0, p2t_ketPredProj_mul_ket, ite_eq_left (hFwd β hs)]
    · rw [ite_eq_right hs, Matrix.mulVec_zero, Matrix.mulVec_zero]
  have hP₀_T_pre : P₀ * (T_anc.1 * P_pre) = T_anc.1 * P_pre := by
    calc P₀ * (T_anc.1 * P_pre)
        = P₀ * (P_clean * (T_anc.1 * P_pre)) := by rw [hClean_T_pre]
      _ = (P₀ * P_clean) * (T_anc.1 * P_pre) := (Matrix.mul_assoc _ _ _).symm
      _ = T_anc.1 * P_pre := by rw [hP₀_clean, hClean_T_pre]
  have hPre_Tadj_P₀ : P_pre * T_anc.1ᴴ * P₀ = P_pre * T_anc.1ᴴ := by
    have h := congrArg conjTranspose hP₀_T_pre
    simpa only [Matrix.conjTranspose_mul, hP₀H, hPreH, Matrix.mul_assoc] using h
  have hPre_Tadj_Clean : P_pre * T_anc.1ᴴ * P_clean = P_pre * T_anc.1ᴴ := by
    have h := congrArg conjTranspose hClean_T_pre
    simpa only [Matrix.conjTranspose_mul, hCleanH, hPreH, Matrix.mul_assoc] using h
  have hTU_comm : U_target.1 * T_anc.1 = T_anc.1 * U_target.1 := by
    apply MeasureBranchHadamardSem.matrix_ext_ket; intro β
    rw [mbh_ket_eq_ket, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    dsimp only [T_anc]
    rw [p2t_ket_TOFF, hφKet, hφKet, hφIndep _ anc _ hWanc, Matrix.mulVec_smul, p2t_ket_TOFF]
  have hTU_adj_comm : T_anc.1ᴴ * U_target.1ᴴ = U_target.1ᴴ * T_anc.1ᴴ := by
    have h := congrArg conjTranspose hTU_comm
    simpa only [Matrix.conjTranspose_mul] using h
  have hP₀_U_clean : P₀ * (U_target.1 * P_clean) = U_target.1 * P_clean := by
    apply MeasureBranchHadamardSem.matrix_ext_ket; intro γ
    rw [mbh_ket_eq_ket, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    dsimp only [P_clean, P₀]
    rw [p2t_ketPredProj_mul_ket]
    by_cases hs : S_clean γ
    · rw [ite_eq_left hs, hφKet, Matrix.mulVec_smul, p2t_ket_projector_zero,
          ite_eq_left (hClean0 γ hs)]
    · rw [ite_eq_right hs, Matrix.mulVec_zero, Matrix.mulVec_zero]
  have hClean_Uadj_P₀ : P_clean * U_target.1ᴴ * P₀ = P_clean * U_target.1ᴴ := by
    have h := congrArg conjTranspose hP₀_U_clean
    simpa only [Matrix.conjTranspose_mul, hP₀H, hCleanH, Matrix.mul_assoc] using h
  let dUncomp : DynamicCircuit Var n := DynamicCircuit.andUncompute v c₁ c₂ anc h₁₂
  let dComp : DynamicCircuit Var n := DynamicCircuit.andCompute c₁ c₂ anc h₁a h₂a
  have hConstWrap : PreservesStoreConst
      (l26_uncomputeSandwichPosDyn v c₁ c₂ anc h₁₂ h₁a h₂a dBody) :=
    PreservesStoreConst.seq (PreservesStoreConst.andUncompute v c₁ c₂ anc h₁₂)
      (PreservesStoreConst.seq hdBody.1 (PreservesStoreConst.circuit _))
  refine ⟨hConstWrap, fun M σ ↦ ?_⟩
  obtain ⟨M₁, hComp_wp⟩ := (PreservesStoreConst.circuit _ : PreservesStoreConst dComp) M
  obtain ⟨M₂, hBody_wp⟩ := hdBody.1 M₁
  obtain ⟨M₃, hUncomp_wp⟩ := PreservesStoreConst.andUncompute v c₁ c₂ anc h₁₂ M₂
  have hAllWp : wp (l26_uncomputeSandwichPosDyn v c₁ c₂ anc h₁₂ h₁a h₂a dBody).compile
      (fun _ ↦ M) σ = M₃ := by
    change wp dUncomp.compile (wp dBody.compile (wp dComp.compile (fun _ ↦ M))) σ = M₃
    dsimp only [dComp, dUncomp, DynamicCircuit.andCompute]
    rw [hComp_wp, hBody_wp, congrFun hUncomp_wp σ]
  rw [hAllWp]
  have hStepUncompRaw := congrArg HermitianMat.mat (congrArg Subtype.val (congrFun
    (DynCircuitExt.restrictAssertionToZeroAncilla_wpQAssign_toffoli_wp_andUncompute_of_update_eq
      v c₁ c₂ anc h₁₂ h₁a h₂a (fun _ ↦ M₂) (fun _ _ ↦ rfl)) σ))
  rw [hUncomp_wp] at hStepUncompRaw
  have hStepUncomp : P₀ * (T_anc.1ᴴ * M₃.1.1 * T_anc.1) * P₀ = P₀ * M₂.1.1 * P₀ := by
    simp only [CQAssertion.restrictToZeroAncilla, CQAssertion.conj, T_anc, P₀,
      QRegister.basisOutcomeProjector_conjTranspose,
      HermitianMat.conj_apply_mat, wpQAssignCompat, qAssignObsMap, Observable.conj_coe,
      Unitary.coe_star, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose,
      Matrix.mul_assoc] at hStepUncompRaw ⊢
    exact hStepUncompRaw
  have hBodyConj : P_clean * M₂.1.1 * P_clean =
      P_clean * (U_target.1ᴴ * M₁.1.1 * U_target.1) * P_clean := by
    have hM2 : M₂ = wp dBody.compile (fun _ ↦ M₁) σ := (congrFun hBody_wp σ).symm
    rw [hM2]; exact hdBody.2 M₁ σ
  let dId : DynamicCircuit Var n := .circuit .identity
  have hIdWp : wp dId.compile (fun _ ↦ M) = fun _ ↦ M := rfl
  have hStepCompRaw := congrArg HermitianMat.mat (congrArg Subtype.val (congrFun
    (DynCircuitExt.restrictToZeroAncilla_wp_andCompute_seq_compat c₁ c₂ anc h₁₂ h₁a h₂a
      dId.compile (fun _ ↦ M)) σ))
  have hCompIdWp : wp (.qSeq dComp.compile dId.compile) (fun _ ↦ M) = fun _ ↦ M₁ := by
    funext τ
    change wp dComp.compile (wp dId.compile (fun _ ↦ M)) τ = M₁
    rw [hIdWp]
    exact congrFun hComp_wp τ
  rw [hCompIdWp, hIdWp] at hStepCompRaw
  have hStepComp : P₀ * M₁.1.1 * P₀ = P₀ * (T_anc.1ᴴ * M.1.1 * T_anc.1) * P₀ := by
    simp only [CQAssertion.restrictToZeroAncilla, CQAssertion.conj, T_anc, P₀,
      QRegister.basisOutcomeProjector_conjTranspose,
      HermitianMat.conj_apply_mat, wpQAssignCompat, qAssignObsMap, Observable.conj_coe,
      Unitary.coe_star, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose,
      Matrix.mul_assoc] at hStepCompRaw ⊢
    exact hStepCompRaw
  have hPre_T_T : P_pre * (T_anc.1ᴴ * T_anc.1ᴴ) = P_pre := by
    rw [hT_symm, hT_self, Matrix.mul_one]
  have hT_T_Pre : (T_anc.1 * T_anc.1) * P_pre = P_pre := by
    rw [hT_self, Matrix.one_mul]
  calc P_pre * M₃.1.1 * P_pre
      = (P_pre * (T_anc.1ᴴ * T_anc.1ᴴ)) * M₃.1.1 * ((T_anc.1 * T_anc.1) * P_pre) := by
          rw [hPre_T_T, hT_T_Pre]
    _ = (P_pre * T_anc.1ᴴ) * (T_anc.1ᴴ * M₃.1.1 * T_anc.1) * (T_anc.1 * P_pre) := by
          simp only [Matrix.mul_assoc]
    _ = (P_pre * T_anc.1ᴴ * P₀) * (T_anc.1ᴴ * M₃.1.1 * T_anc.1) * (P₀ * (T_anc.1 * P_pre)) := by
          rw [hPre_Tadj_P₀, hP₀_T_pre]
    _ = (P_pre * T_anc.1ᴴ) * (P₀ * (T_anc.1ᴴ * M₃.1.1 * T_anc.1) * P₀) * (T_anc.1 * P_pre) := by
          simp only [Matrix.mul_assoc]
    _ = (P_pre * T_anc.1ᴴ) * (P₀ * M₂.1.1 * P₀) * (T_anc.1 * P_pre) := by
          rw [hStepUncomp]
    _ = (P_pre * T_anc.1ᴴ * P₀) * M₂.1.1 * (P₀ * (T_anc.1 * P_pre)) := by
          simp only [Matrix.mul_assoc]
    _ = (P_pre * T_anc.1ᴴ) * M₂.1.1 * (T_anc.1 * P_pre) := by
          rw [hPre_Tadj_P₀, hP₀_T_pre]
    _ = (P_pre * T_anc.1ᴴ * P_clean) * M₂.1.1 * (P_clean * (T_anc.1 * P_pre)) := by
          rw [hPre_Tadj_Clean, hClean_T_pre]
    _ = (P_pre * T_anc.1ᴴ) * (P_clean * M₂.1.1 * P_clean) * (T_anc.1 * P_pre) := by
          simp only [Matrix.mul_assoc]
    _ = (P_pre * T_anc.1ᴴ) * (P_clean * (U_target.1ᴴ * M₁.1.1 * U_target.1) * P_clean) *
          (T_anc.1 * P_pre) := by rw [hBodyConj]
    _ = (P_pre * T_anc.1ᴴ) * (P_clean * U_target.1ᴴ) * M₁.1.1 *
          (U_target.1 * P_clean) * (T_anc.1 * P_pre) := by simp only [Matrix.mul_assoc]
    _ = (P_pre * T_anc.1ᴴ) * (P_clean * U_target.1ᴴ * P₀) * M₁.1.1 *
          (P₀ * (U_target.1 * P_clean)) * (T_anc.1 * P_pre) := by
          rw [hClean_Uadj_P₀, hP₀_U_clean]
    _ = (P_pre * T_anc.1ᴴ) * (P_clean * U_target.1ᴴ) * (P₀ * M₁.1.1 * P₀) *
          (U_target.1 * P_clean) * (T_anc.1 * P_pre) := by simp only [Matrix.mul_assoc]
    _ = (P_pre * T_anc.1ᴴ) * (P_clean * U_target.1ᴴ) * (P₀ * (T_anc.1ᴴ * M.1.1 * T_anc.1) * P₀) *
          (U_target.1 * P_clean) * (T_anc.1 * P_pre) := by rw [hStepComp]
    _ = (P_pre * T_anc.1ᴴ) * (P_clean * U_target.1ᴴ * P₀) * (T_anc.1ᴴ * M.1.1 * T_anc.1) *
          (P₀ * (U_target.1 * P_clean)) * (T_anc.1 * P_pre) := by simp only [Matrix.mul_assoc]
    _ = (P_pre * T_anc.1ᴴ * P_clean) * U_target.1ᴴ * (T_anc.1ᴴ * M.1.1 * T_anc.1) *
          U_target.1 * (P_clean * (T_anc.1 * P_pre)) := by
          rw [hClean_Uadj_P₀, hP₀_U_clean]; simp only [Matrix.mul_assoc]
    _ = P_pre * (T_anc.1ᴴ * U_target.1ᴴ) * T_anc.1ᴴ * M.1.1 *
          T_anc.1 * (U_target.1 * T_anc.1) * P_pre := by
          rw [hPre_Tadj_Clean, hClean_T_pre]; simp only [Matrix.mul_assoc]
    _ = P_pre * U_target.1ᴴ * (T_anc.1ᴴ * T_anc.1ᴴ) * M.1.1 *
          (T_anc.1 * T_anc.1) * U_target.1 * P_pre := by
          rw [hTU_adj_comm, hTU_comm]; simp only [Matrix.mul_assoc]
    _ = P_pre * (U_target.1ᴴ * M.1.1 * U_target.1) * P_pre := by
          rw [hT_symm, hT_self]; simp only [Matrix.mul_one, Matrix.mul_assoc]
def l26_uncomputeSandwichNegDyn {Var : Type} {n : ℕ} (v : Var) (c₁ c₂ anc : Wire n)
    (h₁₂ : c₁ ≠ c₂) (h₁a : c₁ ≠ anc) (h₂a : c₂ ≠ anc) (dBody : DynamicCircuit Var n) :
    DynamicCircuit Var n := .seq (.circuit (Circuit.CNOT c₁ anc h₁a)) (.seq
    (l26_uncomputeSandwichPosDyn v c₁ c₂ anc h₁₂ h₁a h₂a dBody) (.circuit (Circuit.CNOT c₁ anc
    h₁a)))
theorem count_l26_uncomputeSandwichNegDyn {Var : Type} {n : ℕ} (v : Var) (c₁ c₂ anc : Wire n)
    (h₁₂ : c₁ ≠ c₂) (h₁a : c₁ ≠ anc) (h₂a : c₂ ≠ anc) (dBody : DynamicCircuit Var n) :
    (l26_uncomputeSandwichNegDyn v c₁ c₂ anc h₁₂ h₁a h₂a dBody).count .T = 4 + dBody.count .T
    ∧ (l26_uncomputeSandwichNegDyn v c₁ c₂ anc h₁₂ h₁a h₂a dBody).count .TOFF = dBody.count
    .TOFF := by
  have hcnotT : (Circuit.CNOT c₁ anc h₁a).count .T = 0 := by simp [Circuit.CNOT]
  have hcnotF : (Circuit.CNOT c₁ anc h₁a).count .TOFF = 0 := by simp [Circuit.CNOT]
  obtain ⟨ht, hf⟩ := count_l26_uncomputeSandwichPosDyn v c₁ c₂ anc h₁₂ h₁a h₂a dBody
  dsimp only [l26_uncomputeSandwichNegDyn, DynamicCircuit.count]
  rw [hcnotT, hcnotF, ht, hf]
  exact ⟨by omega, by omega⟩
theorem l26_uncomputeSandwichNegDyn_realizes {Var : Type} [Fintype Var] [DecidableEq Var]
    {n : ℕ} (v : Var) (c₁ c₂ anc : Wire n) (h₁₂ : c₁ ≠ c₂) (h₁a : c₁ ≠ anc) (h₂a : c₂ ≠ anc)
    {W : Wire n → Prop} (hWanc : W anc) {S_pre S_clean : BitAssignment n → Prop}
    {dBody : DynamicCircuit Var n} {U_target : Unitary (2 ^ n)}
    (hDiag : p2t_DiagIndepOf W U_target) (hAncEq : ∀ β : BitAssignment n, S_pre β → β anc = β
    c₁ * (1 + β c₂)) (hClean0 : ∀ γ : BitAssignment n, S_clean γ → γ anc = 0) (hFwd : ∀ β :
    BitAssignment n, S_pre β → S_clean (Function.update β anc 0)) (hdBody :
    p2t_RealizesConstCleanUnitary (p2t_ketPredProj S_clean) dBody U_target) :
    p2t_RealizesConstCleanUnitary (p2t_ketPredProj S_pre)
    (l26_uncomputeSandwichNegDyn v c₁ c₂ anc h₁₂ h₁a h₂a dBody) U_target := by
  classical
  rcases hDiag with ⟨φ, hφKet, hφIndep⟩
  let cCnot := Circuit.CNOT c₁ anc h₁a
  let S_mid : BitAssignment n → Prop := fun γ ↦ S_pre (Function.update γ anc (γ anc + γ c₁))
  have hcInv : cCnot.eval * cCnot.eval = 1 := by
    apply Subtype.ext; apply MeasureBranchHadamardSem.matrix_ext_ket; intro γ
    rw [mbh_ket_eq_ket, Submonoid.coe_mul, Submonoid.coe_one, ← Matrix.mulVec_mulVec,
      Matrix.one_mulVec]
    dsimp only [cCnot]
    rw [p2t_ket_CNOT, p2t_ket_CNOT, Function.update_self, Function.update_of_ne h₁a]
    have hcancel : γ anc + γ c₁ + γ c₁ = γ anc := by
      rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
    rw [hcancel, Function.update_idem, Function.update_eq_self]
  have hcConjU : cCnot.eval * (U_target * cCnot.eval) = U_target := by
    apply Subtype.ext; apply MeasureBranchHadamardSem.matrix_ext_ket; intro γ
    rw [mbh_ket_eq_ket, Submonoid.coe_mul, Submonoid.coe_mul, ← Matrix.mulVec_mulVec,
      ← Matrix.mulVec_mulVec]
    dsimp only [cCnot]
    rw [p2t_ket_CNOT, hφKet, hφKet, hφIndep _ anc _ hWanc, Matrix.mulVec_smul, p2t_ket_CNOT,
      Function.update_self, Function.update_of_ne h₁a]
    have hcancel : γ anc + γ c₁ + γ c₁ = γ anc := by
      rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
    rw [hcancel, Function.update_idem, Function.update_eq_self]
  have hdPos : p2t_RealizesConstCleanUnitary (p2t_ketPredProj S_mid)
      (l26_uncomputeSandwichPosDyn v c₁ c₂ anc h₁₂ h₁a h₂a dBody) U_target := by
    refine l26_uncomputeSandwichPosDyn_realizes v c₁ c₂ anc h₁₂ h₁a h₂a hWanc
      ⟨φ, hφKet, hφIndep⟩ (fun γ hγ ↦ ?_) hClean0 (fun γ hγ ↦ ?_) hdBody
    · have h0 := hAncEq (Function.update γ anc (γ anc + γ c₁)) hγ
      rw [Function.update_self, Function.update_of_ne h₁a, Function.update_of_ne h₂a] at h0
      have h1 : (γ anc + γ c₁) + γ c₁ = γ anc := by
        rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
      have h2 : γ c₁ * (1 + γ c₂) + γ c₁ = γ c₁ * γ c₂ := by
        calc γ c₁ * (1 + γ c₂) + γ c₁ = γ c₁ * γ c₂ + (γ c₁ + γ c₁) := by ring
          _ = γ c₁ * γ c₂ := by rw [CharTwo.add_self_eq_zero, add_zero]
      rw [← h1, h0, h2]
    · have hup : Function.update (Function.update γ anc (γ anc + γ c₁)) anc 0 =
          Function.update γ anc 0 := Function.update_idem _ _ _
      rw [← hup]
      exact hFwd _ hγ
  refine p2t_RealizesConstCleanUnitary_withConjCircuit_diag hdPos hcInv hcConjU
    (fun γ hγ ↦ ⟨Function.update γ anc (γ anc + γ c₁), ?_, p2t_ket_CNOT c₁ anc h₁a γ⟩)
  dsimp only [S_mid]
  rw [Function.update_self, Function.update_of_ne h₁a, add_assoc,
    CharTwo.add_self_eq_zero, add_zero, Function.update_idem, Function.update_eq_self]
  exact hγ
theorem l26_branchSplitDyn_realizes_exact {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    (v : Var) (wCtrl wMsb wAnc : Wire n) (hCM : wCtrl ≠ wMsb) (hCA : wCtrl ≠ wAnc)
    (hMA : wMsb ≠ wAnc) (S_pre S_sub : BitAssignment n → Prop)
    (hPreAnc : ∀ β, S_pre β → β wAnc = 0)
    (hPreSub : ∀ β val, S_pre β → S_sub (Function.update β wAnc val))
    (hSubAnc : ∀ γ val, S_sub (Function.update γ wAnc val) ↔ S_sub γ)
    (dLeft dRight : DynamicCircuit Var n) (ψ_L ψ_R : BitAssignment n → ZMod 2)
    (hLAnc : ∀ γ val, ψ_L (Function.update γ wAnc val) = ψ_L γ)
    (hRAnc : ∀ γ val, ψ_R (Function.update γ wAnc val) = ψ_R γ) (hdLeft :
    p2t_RealizesConstCleanUnitary (p2t_ketPredProj (fun γ ↦ S_sub γ ∧ γ wAnc = γ wCtrl * (1 +
    γ wMsb))) dLeft (l26DiagUnitary (fun γ ↦ γ wAnc * ψ_L γ))) (hdRight :
    p2t_RealizesConstCleanUnitary (p2t_ketPredProj (fun γ ↦ S_sub γ ∧ γ wAnc = γ wCtrl * γ
    wMsb)) dRight (l26DiagUnitary (fun γ ↦ γ wAnc * ψ_R γ))) : p2t_RealizesConstCleanUnitary
    (p2t_ketPredProj S_pre) (l26_branchSplitDyn v wCtrl wMsb wAnc hCM hCA hMA dLeft dRight)
    (l26DiagUnitary (fun γ ↦ γ wCtrl * ((1 + γ wMsb) * ψ_L γ + γ wMsb * ψ_R γ))) := by
  classical
  let C := Circuit.CNOT wCtrl wAnc hCA
  let S_left : BitAssignment n → Prop := fun γ ↦ S_sub γ ∧ γ wAnc = γ wCtrl * (1 + γ wMsb)
  let S_post : BitAssignment n → Prop := fun γ ↦ S_sub γ ∧ γ wAnc = γ wCtrl * γ wMsb
  let P_left := p2t_ketPredProj S_left
  let P_post := p2t_ketPredProj S_post
  have hPleftH : P_leftᴴ = P_left := p2t_ketPredProj_conjTranspose S_left
  have hPpostH : P_postᴴ = P_post := p2t_ketPredProj_conjTranspose S_post
  have hC_post_to_left : P_left * (C.eval.1 * P_post) = C.eval.1 * P_post := by
    apply MeasureBranchHadamardSem.matrix_ext_ket; intro γ
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, mbh_ket_eq_ket,
        p2t_ketPredProj_mul_ket]
    by_cases hp : S_post γ
    · rw [ite_eq_left hp, p2t_ket_CNOT, p2t_ketPredProj_mul_ket, ite_eq_left]
      refine ⟨(hSubAnc γ _).mpr hp.1, ?_⟩
      rw [Function.update_self, Function.update_of_ne hCA, Function.update_of_ne hMA, hp.2]
      ring
    · rw [ite_eq_right hp, Matrix.mulVec_zero, Matrix.mulVec_zero]
  have hC_left_to_post : P_post * (C.eval.1 * P_left) = C.eval.1 * P_left := by
    apply MeasureBranchHadamardSem.matrix_ext_ket; intro γ
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, mbh_ket_eq_ket,
        p2t_ketPredProj_mul_ket]
    by_cases hl : S_left γ
    · rw [ite_eq_left hl, p2t_ket_CNOT, p2t_ketPredProj_mul_ket, ite_eq_left]
      refine ⟨(hSubAnc γ _).mpr hl.1, ?_⟩
      rw [Function.update_self, Function.update_of_ne hCA, Function.update_of_ne hMA, hl.2]
      calc γ wCtrl * (1 + γ wMsb) + γ wCtrl
          = γ wCtrl * γ wMsb + (γ wCtrl + γ wCtrl) := by ring
        _ = γ wCtrl * γ wMsb := by rw [CharTwo.add_self_eq_zero, add_zero]
    · rw [ite_eq_right hl, Matrix.mulVec_zero, Matrix.mulVec_zero]
  let U_L := l26DiagUnitary (fun γ ↦ γ wAnc * ψ_L γ)
  let U_R := l26DiagUnitary (fun γ ↦ γ wAnc * ψ_R γ)
  have hAbsUL : P_left * (U_L.1 * P_left) = U_L.1 * P_left := by
    rw [← Matrix.mul_assoc, ketPredProj_comm_l26DiagUnitary S_left, Matrix.mul_assoc,
        ketPredProj_mul_self]
  have hd34 := p2t_RealizesConstCleanUnitary_seq_proj hPleftH hPpostH
    (p2t_RealizesConstCleanUnitary_circuit P_left C) hdRight hC_left_to_post
  have hd234 := p2t_RealizesConstCleanUnitary_seq_proj hPleftH hPleftH hdLeft hd34 hAbsUL
  have hd1234 := p2t_RealizesConstCleanUnitary_seq_proj hPpostH hPleftH
    (p2t_RealizesConstCleanUnitary_circuit P_post C) hd234 hC_post_to_left
  let U_body := l26DiagUnitary (fun γ ↦ (γ wAnc + γ wCtrl) * ψ_L γ + γ wAnc * ψ_R γ)
  have hBodyEq : ((U_R * C.eval) * U_L * C.eval) = U_body := by
    apply Subtype.ext; apply MeasureBranchHadamardSem.matrix_ext_ket; intro γ
    dsimp only [C, U_L, U_R, U_body]
    simp only [Submonoid.coe_mul, Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ket_CNOT,
      l26DiagUnitary_mulVec_ket, Matrix.mulVec_smul, smul_smul, neg_one_pow_zmod2_mul]
    have hRet : Function.update (Function.update γ wAnc (γ wAnc + γ wCtrl)) wAnc
        (Function.update γ wAnc (γ wAnc + γ wCtrl) wAnc +
          Function.update γ wAnc (γ wAnc + γ wCtrl) wCtrl) = γ := by
      rw [Function.update_self, Function.update_of_ne hCA, Function.update_idem]
      have hcancel : γ wAnc + γ wCtrl + γ wCtrl = γ wAnc := by
        rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
      rw [hcancel, Function.update_eq_self]
    rw [hRet, Function.update_self, hLAnc γ (γ wAnc + γ wCtrl)]
  have hdBodySub : p2t_RealizesConstCleanUnitary P_post
      (.seq (.circuit C) (.seq dLeft (.seq (.circuit C) dRight))) U_body :=
    p2t_RealizesConstCleanUnitary_congr_unitary hPpostH hd1234 (by
      dsimp only [U_L, U_R, U_body] at hBodyEq ⊢
      simp only [← hBodyEq, Submonoid.coe_mul, Matrix.mul_assoc])
  let U_target := l26DiagUnitary (fun γ ↦ γ wCtrl * ((1 + γ wMsb) * ψ_L γ + γ wMsb * ψ_R γ))
  have hdBodyPost : p2t_RealizesConstCleanUnitary P_post
      (.seq (.circuit C) (.seq dLeft (.seq (.circuit C) dRight))) U_target := by
    refine p2t_RealizesConstCleanUnitary_congr_unitary hPpostH hdBodySub ?_
    apply MeasureBranchHadamardSem.matrix_ext_ket; intro γ
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, mbh_ket_eq_ket, p2t_ketPredProj_mul_ket]
    by_cases hp : S_post γ
    · rw [ite_eq_left hp, ← mbh_ket_eq_ket, l26DiagUnitary_mulVec_ket, l26DiagUnitary_mulVec_ket]
      refine congrArg (fun e : ZMod 2 ↦ ((-1 : ℂ) ^ e.val) • ket γ) ?_
      rw [hp.2]; ring
    · rw [ite_eq_right hp, Matrix.mulVec_zero, Matrix.mulVec_zero]
  dsimp only [l26_branchSplitDyn]
  refine p2t_RealizesConstCleanUnitary_withTempAnd_diag v wCtrl wMsb wAnc hCM hCA hMA
    (W := fun w ↦ w = wAnc) rfl ?_ hPreAnc ?_ hdBodyPost
  · refine l26DiagUnitary_diagIndepOf fun β w val hw ↦ ?_
    subst hw
    rw [Function.update_of_ne hCA, Function.update_of_ne hMA, hLAnc β val, hRAnc β val]
  · intro β hs
    refine ⟨hPreSub β _ hs, ?_⟩
    rw [Function.update_self, Function.update_of_ne hCA, Function.update_of_ne hMA]
def l26_pebbledSplit2Dyn {Var : Type} {n : ℕ} (v : Var) (wCtrl u_a u_b wTmp wAnc : Wire n)
    (hCa : wCtrl ≠ u_a) (hCT : wCtrl ≠ wTmp) (haT : u_a ≠ wTmp) (hTb : wTmp ≠ u_b)
    (hTA : wTmp ≠ wAnc) (hbA : u_b ≠ wAnc) (d00 d01 d10 d11 : DynamicCircuit Var n) :
    DynamicCircuit Var n := l26_branchSplitDyn v wCtrl u_a wTmp hCa hCT haT
    (l26_branchSplitDyn v wTmp u_b wAnc hTb hTA hbA (l26_uncomputeSandwichNegDyn v wCtrl u_a
    wTmp hCa hCT haT d00) (l26_uncomputeSandwichNegDyn v wCtrl u_a wTmp hCa hCT haT d01))
    (l26_branchSplitDyn v wTmp u_b wAnc hTb hTA hbA (l26_uncomputeSandwichPosDyn v wCtrl u_a
    wTmp hCa hCT haT d10) (l26_uncomputeSandwichPosDyn v wCtrl u_a wTmp hCa hCT haT d11))
theorem count_l26_pebbledSplit2Dyn {Var : Type} {n : ℕ} (v : Var)
    (wCtrl u_a u_b wTmp wAnc : Wire n) (hCa : wCtrl ≠ u_a) (hCT : wCtrl ≠ wTmp)
    (haT : u_a ≠ wTmp) (hTb : wTmp ≠ u_b) (hTA : wTmp ≠ wAnc) (hbA : u_b ≠ wAnc)
    (d00 d01 d10 d11 : DynamicCircuit Var n) : (l26_pebbledSplit2Dyn v wCtrl u_a u_b wTmp wAnc
    hCa hCT haT hTb hTA hbA d00 d01 d10 d11).count .T = 28 + d00.count .T + d01.count .T +
    d10.count .T + d11.count .T ∧ (l26_pebbledSplit2Dyn v wCtrl u_a u_b wTmp wAnc hCa hCT haT
    hTb hTA hbA d00 d01 d10 d11).count .TOFF = d00.count .TOFF + d01.count .TOFF + d10.count
    .TOFF + d11.count .TOFF := by
  obtain ⟨t00, f00⟩ := count_l26_uncomputeSandwichNegDyn v wCtrl u_a wTmp hCa hCT haT d00
  obtain ⟨t01, f01⟩ := count_l26_uncomputeSandwichNegDyn v wCtrl u_a wTmp hCa hCT haT d01
  obtain ⟨t10, f10⟩ := count_l26_uncomputeSandwichPosDyn v wCtrl u_a wTmp hCa hCT haT d10
  obtain ⟨t11, f11⟩ := count_l26_uncomputeSandwichPosDyn v wCtrl u_a wTmp hCa hCT haT d11
  obtain ⟨tL, fL⟩ := count_l26_branchSplitDyn v wTmp u_b wAnc hTb hTA hbA
    (l26_uncomputeSandwichNegDyn v wCtrl u_a wTmp hCa hCT haT d00)
    (l26_uncomputeSandwichNegDyn v wCtrl u_a wTmp hCa hCT haT d01)
  obtain ⟨tR, fR⟩ := count_l26_branchSplitDyn v wTmp u_b wAnc hTb hTA hbA
    (l26_uncomputeSandwichPosDyn v wCtrl u_a wTmp hCa hCT haT d10)
    (l26_uncomputeSandwichPosDyn v wCtrl u_a wTmp hCa hCT haT d11)
  obtain ⟨tTop, fTop⟩ := count_l26_branchSplitDyn v wCtrl u_a wTmp hCa hCT haT _ _
  dsimp only [l26_pebbledSplit2Dyn]
  rw [tTop, fTop, tL, fL, tR, fR, t00, f00, t01, f01, t10, f10, t11, f11]
  exact ⟨by omega, by omega⟩
theorem l26_pebbledSplit2Dyn_realizes {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    (v : Var) (wCtrl u_a u_b wTmp wAnc : Wire n)
    (hCa : wCtrl ≠ u_a) (hCT : wCtrl ≠ wTmp) (haT : u_a ≠ wTmp)
    (hTb : wTmp ≠ u_b) (hTA : wTmp ≠ wAnc) (hbA : u_b ≠ wAnc)
    (hCA : wCtrl ≠ wAnc) (haA : u_a ≠ wAnc)
    (S_raw : BitAssignment n → Prop)
    (hRawTmp : ∀ γ val, S_raw (Function.update γ wTmp val) ↔ S_raw γ)
    (hRawAnc : ∀ γ val, S_raw (Function.update γ wAnc val) ↔ S_raw γ)
    (d00 d01 d10 d11 : DynamicCircuit Var n)
    (ψ00 ψ01 ψ10 ψ11 : BitAssignment n → ZMod 2)
    (h00Tmp : ∀ γ val, ψ00 (Function.update γ wTmp val) = ψ00 γ)
    (h01Tmp : ∀ γ val, ψ01 (Function.update γ wTmp val) = ψ01 γ)
    (h10Tmp : ∀ γ val, ψ10 (Function.update γ wTmp val) = ψ10 γ)
    (h11Tmp : ∀ γ val, ψ11 (Function.update γ wTmp val) = ψ11 γ)
    (h00Anc : ∀ γ val, ψ00 (Function.update γ wAnc val) = ψ00 γ)
    (h01Anc : ∀ γ val, ψ01 (Function.update γ wAnc val) = ψ01 γ)
    (h10Anc : ∀ γ val, ψ10 (Function.update γ wAnc val) = ψ10 γ)
    (h11Anc : ∀ γ val, ψ11 (Function.update γ wAnc val) = ψ11 γ)
    (hd00 : p2t_RealizesConstCleanUnitary
      (p2t_ketPredProj (fun γ ↦ S_raw γ ∧ γ wTmp = 0)) d00
      (l26DiagUnitary (fun γ ↦ γ wAnc * ψ00 γ)))
    (hd01 : p2t_RealizesConstCleanUnitary
      (p2t_ketPredProj (fun γ ↦ S_raw γ ∧ γ wTmp = 0)) d01
      (l26DiagUnitary (fun γ ↦ γ wAnc * ψ01 γ)))
    (hd10 : p2t_RealizesConstCleanUnitary
      (p2t_ketPredProj (fun γ ↦ S_raw γ ∧ γ wTmp = 0)) d10
      (l26DiagUnitary (fun γ ↦ γ wAnc * ψ10 γ)))
    (hd11 : p2t_RealizesConstCleanUnitary
      (p2t_ketPredProj (fun γ ↦ S_raw γ ∧ γ wTmp = 0)) d11
      (l26DiagUnitary (fun γ ↦ γ wAnc * ψ11 γ))) :
    p2t_RealizesConstCleanUnitary
      (p2t_ketPredProj (fun β ↦ S_raw β ∧ β wTmp = 0 ∧ β wAnc = 0))
      (l26_pebbledSplit2Dyn v wCtrl u_a u_b wTmp wAnc hCa hCT haT hTb hTA hbA
        d00 d01 d10 d11)
      (l26DiagUnitary (fun γ ↦
        γ wCtrl *
          ((1 + γ u_a) * ((1 + γ u_b) * ψ00 γ + γ u_b * ψ01 γ) +
           γ u_a * ((1 + γ u_b) * ψ10 γ + γ u_b * ψ11 γ)))) := by
  let S_neg : BitAssignment n → Prop := fun γ ↦ S_raw γ ∧ γ wTmp = γ wCtrl * (1 + γ u_a)
  let S_pos : BitAssignment n → Prop := fun γ ↦ S_raw γ ∧ γ wTmp = γ wCtrl * γ u_a
  have hNegAnc : ∀ γ val, S_neg (Function.update γ wAnc val) ↔ S_neg γ := fun γ val ↦ by
    dsimp only [S_neg]
    rw [hRawAnc, Function.update_of_ne hTA, Function.update_of_ne hCA, Function.update_of_ne haA]
  have hPosAnc : ∀ γ val, S_pos (Function.update γ wAnc val) ↔ S_pos γ := fun γ val ↦ by
    dsimp only [S_pos]
    rw [hRawAnc, Function.update_of_ne hTA, Function.update_of_ne hCA, Function.update_of_ne haA]
  have hd00' : p2t_RealizesConstCleanUnitary (p2t_ketPredProj S_neg)
      (l26_uncomputeSandwichNegDyn v wCtrl u_a wTmp hCa hCT haT d00)
      (l26DiagUnitary (fun γ ↦ γ wAnc * ψ00 γ)) :=
    l26_uncomputeSandwichNegDyn_realizes v wCtrl u_a wTmp hCa hCT haT
      (W := fun w ↦ w = wTmp) rfl
      (l26DiagUnitary_diagIndepOf fun β w val hw ↦ by
        subst hw; rw [Function.update_of_ne hTA.symm, h00Tmp])
      (fun _ h ↦ h.2) (fun _ h ↦ h.2)
      (fun β h ↦ ⟨(hRawTmp β 0).mpr h.1, Function.update_self _ _ _⟩)
      hd00
  have hd01' : p2t_RealizesConstCleanUnitary (p2t_ketPredProj S_neg)
      (l26_uncomputeSandwichNegDyn v wCtrl u_a wTmp hCa hCT haT d01)
      (l26DiagUnitary (fun γ ↦ γ wAnc * ψ01 γ)) :=
    l26_uncomputeSandwichNegDyn_realizes v wCtrl u_a wTmp hCa hCT haT
      (W := fun w ↦ w = wTmp) rfl
      (l26DiagUnitary_diagIndepOf fun β w val hw ↦ by
        subst hw; rw [Function.update_of_ne hTA.symm, h01Tmp])
      (fun _ h ↦ h.2) (fun _ h ↦ h.2)
      (fun β h ↦ ⟨(hRawTmp β 0).mpr h.1, Function.update_self _ _ _⟩)
      hd01
  have hd10' : p2t_RealizesConstCleanUnitary (p2t_ketPredProj S_pos)
      (l26_uncomputeSandwichPosDyn v wCtrl u_a wTmp hCa hCT haT d10)
      (l26DiagUnitary (fun γ ↦ γ wAnc * ψ10 γ)) :=
    l26_uncomputeSandwichPosDyn_realizes v wCtrl u_a wTmp hCa hCT haT
      (W := fun w ↦ w = wTmp) rfl
      (l26DiagUnitary_diagIndepOf fun β w val hw ↦ by
        subst hw; rw [Function.update_of_ne hTA.symm, h10Tmp])
      (fun _ h ↦ h.2) (fun _ h ↦ h.2)
      (fun β h ↦ ⟨(hRawTmp β 0).mpr h.1, Function.update_self _ _ _⟩)
      hd10
  have hd11' : p2t_RealizesConstCleanUnitary (p2t_ketPredProj S_pos)
      (l26_uncomputeSandwichPosDyn v wCtrl u_a wTmp hCa hCT haT d11)
      (l26DiagUnitary (fun γ ↦ γ wAnc * ψ11 γ)) :=
    l26_uncomputeSandwichPosDyn_realizes v wCtrl u_a wTmp hCa hCT haT
      (W := fun w ↦ w = wTmp) rfl
      (l26DiagUnitary_diagIndepOf fun β w val hw ↦ by
        subst hw; rw [Function.update_of_ne hTA.symm, h11Tmp])
      (fun _ h ↦ h.2) (fun _ h ↦ h.2)
      (fun β h ↦ ⟨(hRawTmp β 0).mpr h.1, Function.update_self _ _ _⟩)
      hd11
  have hdLeft := l26_branchSplitDyn_realizes v wTmp u_b wAnc hTb hTA hbA
      (fun γ ↦ (S_raw γ ∧ γ wAnc = 0) ∧ γ wTmp = γ wCtrl * (1 + γ u_a)) S_neg
      (fun _ h ↦ h.1.2) (fun β val h ↦ (hNegAnc β val).mpr ⟨h.1.1, h.2⟩) hNegAnc _ _ ψ00 ψ01
      h00Anc h01Anc hd00' hd01'
  have hdRight := l26_branchSplitDyn_realizes v wTmp u_b wAnc hTb hTA hbA
      (fun γ ↦ (S_raw γ ∧ γ wAnc = 0) ∧ γ wTmp = γ wCtrl * γ u_a) S_pos (fun _ h ↦ h.1.2)
      (fun β val h ↦ (hPosAnc β val).mpr ⟨h.1.1, h.2⟩) hPosAnc _ _ ψ10 ψ11 h10Anc h11Anc hd10'
      hd11'
  exact l26_branchSplitDyn_realizes_exact v wCtrl u_a wTmp hCa hCT haT
    (fun β ↦ S_raw β ∧ β wTmp = 0 ∧ β wAnc = 0)
    (fun γ ↦ S_raw γ ∧ γ wAnc = 0)
    (fun _ h ↦ h.2.1)
    (fun β val h ↦ ⟨(hRawTmp β val).mpr h.1, by rw [Function.update_of_ne hTA.symm]; exact h.2.2⟩)
    (fun γ val ↦ by
      refine and_congr (hRawTmp γ val) ?_
      rw [Function.update_of_ne hTA.symm])
    _ _
    (fun γ ↦ (1 + γ u_b) * ψ00 γ + γ u_b * ψ01 γ)
    (fun γ ↦ (1 + γ u_b) * ψ10 γ + γ u_b * ψ11 γ)
    (fun γ val ↦ by rw [Function.update_of_ne hTb.symm, h00Tmp, h01Tmp])
    (fun γ val ↦ by rw [Function.update_of_ne hTb.symm, h10Tmp, h11Tmp])
    hdLeft hdRight
theorem l26_pool_idx_lt {B_max j : ℕ} (hBm : B_max ≤ 7) (hj : j ≤ 2) :
    j < (9 - B_max) + 2 ^ B_max := by
  have : 1 ≤ 2 ^ B_max := Nat.one_le_two_pow
  omega
theorem l26_pool_idx2_lt {B_max j : ℕ} (hBm : B_max ≤ 6) (hB1 : 1 ≤ B_max) (hj : j ≤ 4) :
    j < (9 - B_max) + 2 ^ B_max := by
  have : 2 ≤ 2 ^ B_max := by
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ B_max := Nat.pow_le_pow_right (by decide) hB1
  omega
theorem l26_split1_index_eq {n : ℕ} (rIdx9 : QRegister 9 n) (γ : BitAssignment n)
    (m : ℕ) (hm : m + 1 ≤ 9) (base Q : ℕ) (hQ : 2 ^ m < Q)
    (f : ℕ → ZMod 2) :
    let hm_le : m ≤ 9 := Nat.le_of_succ_le hm
    (1 + γ (rIdx9 ⟨m, hm⟩)) *
      f (base + prunedEffIdx m (2 ^ m) (idxValPrefix rIdx9.wires γ m hm_le)) +
    γ (rIdx9 ⟨m, hm⟩) *
      f ((base + 2 ^ m) + prunedEffIdx m (Q - 2 ^ m) (idxValPrefix rIdx9.wires γ m hm_le)) =
    f (base + prunedEffIdx (m + 1) Q (idxValPrefix rIdx9.wires γ (m + 1) hm)) := by
  intro hm_le
  have hle : ¬ (Q ≤ 2 ^ m) := by omega
  have hlt_sub : idxValPrefix rIdx9.wires γ m hm_le < 2 ^ m :=
    idxValPrefix_lt_two_pow rIdx9.wires γ m hm_le
  have hstep_idx : idxValPrefix rIdx9.wires γ (m + 1) hm =
      idxValPrefix rIdx9.wires γ m hm_le + (γ (rIdx9 ⟨m, hm⟩)).val * 2 ^ m := by
    change idxValPrefix rIdx9.wires γ m hm_le +
      (if γ (rIdx9 ⟨m, hm⟩) = 1 then 2 ^ m else 0) = _
    rw [l26_ite_eq_zmod2_val_mul]
  rcases bit_cases (γ (rIdx9 ⟨m, hm⟩)) with hb | hb
  · have h10 : (1 : ZMod 2) + 0 = 1 := by decide
    have hidx0 : idxValPrefix rIdx9.wires γ (m + 1) hm =
        idxValPrefix rIdx9.wires γ m hm_le := by
      rw [hstep_idx, hb, ZMod.val_zero, zero_mul, add_zero]
    have heff0 : prunedEffIdx (m + 1) Q (idxValPrefix rIdx9.wires γ (m + 1) hm) =
        prunedEffIdx m (2 ^ m) (idxValPrefix rIdx9.wires γ m hm_le) := by
      rw [hidx0, prunedEffIdx_eq_self m (2 ^ m) _ le_rfl hlt_sub]
      unfold prunedEffIdx
      simp only [hle, hlt_sub, ↓reduceIte]
    rw [hb, h10, one_mul, zero_mul, add_zero, heff0]
  · have h11 : (1 : ZMod 2) + 1 = 0 := by decide
    have hidx1 : idxValPrefix rIdx9.wires γ (m + 1) hm =
        idxValPrefix rIdx9.wires γ m hm_le + 2 ^ m := by
      rw [hstep_idx, hb, ZMod.val_one, one_mul]
    have hnlt : ¬ (idxValPrefix rIdx9.wires γ m hm_le + 2 ^ m < 2 ^ m) := by omega
    have heff1 : base + prunedEffIdx (m + 1) Q (idxValPrefix rIdx9.wires γ (m + 1) hm) =
        (base + 2 ^ m) + prunedEffIdx m (Q - 2 ^ m) (idxValPrefix rIdx9.wires γ m hm_le) := by
      rw [hidx1]
      conv_lhs => unfold prunedEffIdx
      simp only [hle, hnlt, ↓reduceIte, Nat.add_mod_right, Nat.mod_eq_of_lt hlt_sub]
      omega
    rw [hb, h11, zero_mul, one_mul, zero_add, heff1]
theorem l26_split2_index_eq {n : ℕ} (rIdx9 : QRegister 9 n) (γ : BitAssignment n)
    (k : ℕ) (hk : k + 2 ≤ 9) (base Q : ℕ) (hQ : 2 ^ (k + 1) + 2 ^ k < Q)
    (f : ℕ → ZMod 2) :
    let u_a := rIdx9 ⟨k + 1, by omega⟩
    let u_b := rIdx9 ⟨k, by omega⟩
    let idx_k := idxValPrefix rIdx9.wires γ k (by omega)
    let idx_k2 := idxValPrefix rIdx9.wires γ (k + 2) hk
    (1 + γ u_a) *
      ((1 + γ u_b) * f (base + prunedEffIdx k (2 ^ k) idx_k) +
       γ u_b * f ((base + 2 ^ k) + prunedEffIdx k (2 ^ k) idx_k)) +
    γ u_a *
      ((1 + γ u_b) * f ((base + 2 ^ (k + 1)) + prunedEffIdx k (2 ^ k) idx_k) +
       γ u_b * f ((base + 2 ^ (k + 1) + 2 ^ k) + prunedEffIdx k (Q - 2 ^ (k + 1) - 2 ^ k) idx_k)) =
    f (base + prunedEffIdx (k + 2) Q idx_k2) := by
  intro u_a u_b idx_k idx_k2
  have hpos : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  have hpow1 : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by ring
  have hsubL : 2 ^ (k + 1) - 2 ^ k = 2 ^ k := by omega
  have hL := l26_split1_index_eq rIdx9 γ k (by omega) base (2 ^ (k + 1)) (by omega) f
  dsimp only at hL
  rw [hsubL] at hL
  have hR := l26_split1_index_eq rIdx9 γ k (by omega) (base + 2 ^ (k + 1)) (Q - 2 ^ (k +
    1)) (by omega) f
  dsimp only at hR
  have hTop := l26_split1_index_eq rIdx9 γ (k + 1) hk base Q (by omega) f
  dsimp only at hTop
  dsimp only [u_a, u_b, idx_k, idx_k2]
  rw [hL, hR, hTop]
def wRoot749Pebbled1Dyn {Var : Type} {n B_max : ℕ} (hBm : B_max ≤ 7) (v : Var)
    (rIdx9 : QRegister 9 n) (wRootCtrl wDum qEnc : Wire n)
    (rPool : QRegister ((9 - B_max) + 2 ^ B_max) n) (hIdxPool : rIdx9.DisjointWires rPool)
    (hRootIdx : ∀ d : Fin 9, wRootCtrl ≠ rIdx9 d) (hRootPool : ∀ j, wRootCtrl ≠ rPool j)
    (hRootDum : wRootCtrl ≠ wDum) (hRootEnc : wRootCtrl ≠ qEnc)
    (hDumIdx : ∀ d : Fin 9, wDum ≠ rIdx9 d) (hEncIdx : ∀ d : Fin 9, qEnc ≠ rIdx9 d)
    (hDumPool : ∀ j, wDum ≠ rPool j) (hEncPool : ∀ j, qEnc ≠ rPool j) (hDumEnc : wDum ≠ qEnc)
    (dLeaf : (q : ℕ) → (wCtrlLeaf : Wire n) → IsTreeCtrlWire wRootCtrl rPool wCtrlLeaf →
    DynamicCircuit Var n) : DynamicCircuit Var n :=
  have hBm9 : B_max ≤ 9 := Nat.le_trans hBm (by decide)
  let j1 : Fin ((9 - B_max) + 2 ^ B_max) := ⟨1, l26_pool_idx_lt hBm (by decide)⟩
  let j2 : Fin ((9 - B_max) + 2 ^ B_max) := ⟨2, l26_pool_idx_lt hBm (by decide)⟩
  let wAnc := rPool j1
  let wTmp := rPool j2
  let u8 := rIdx9 ⟨8, by decide⟩
  let u7 := rIdx9 ⟨7, by decide⟩
  have hc1 : IsTreeCtrlAt wRootCtrl rPool 7 wAnc :=
    Or.inr ⟨j1, by dsimp [j1]; decide, rfl⟩
  have hTA : wTmp ≠ wAnc := rPool.wires.injective.ne (fun h ↦ by
    have hv := congrArg Fin.val h; dsimp [j1, j2] at hv; omega)
  let dSub (base : ℕ) := wPrunedSubtreeDyn hBm9 v rIdx9 wRootCtrl wDum qEnc rPool hIdxPool
      hRootIdx hRootPool hRootDum hRootEnc hDumIdx hEncIdx hDumPool hEncPool hDumEnc dLeaf 7
      (by decide) base 128 wAnc hc1
  let dLeft512 :=
    l26_pebbledSplit2Dyn v wRootCtrl u8 u7 wTmp wAnc
      (hRootIdx ⟨8, by decide⟩) (hRootPool j2) (hIdxPool.ne ⟨8, by decide⟩ j2)
      (hIdxPool.ne ⟨7, by decide⟩ j2).symm hTA (hIdxPool.ne ⟨7, by decide⟩ j1)
      (dSub 0) (dSub 128) (dSub 256) (dSub 384)
  let dRight237 := wPrunedSubtreeDyn hBm9 v rIdx9 wRootCtrl wDum qEnc rPool hIdxPool hRootIdx
      hRootPool hRootDum hRootEnc hDumIdx hEncIdx hDumPool hEncPool hDumEnc dLeaf 8
      (by decide) 512 237 wRootCtrl (Or.inl rfl)
  .seq (.circuit (Circuit.X wRootCtrl))
    (.seq dLeft512
      (.seq (.circuit (Circuit.X wRootCtrl)) dRight237))
theorem l26_wTreeRoutingT_pebbled1_eq {B_max : ℕ} (hBm : B_max ≤ 7) :
    28 + 4 * l26_wTreeRoutingT B_max 7 128 + l26_wTreeRoutingT B_max 8 237 =
      16 + (l26_wTreeRoutingT B_max 9 512 + l26_wTreeRoutingT B_max 9 237) := by
  interval_cases B_max <;> rfl
theorem l26_treeLeafCostSum_512_split4 (leafCost : ℕ → ℕ) : (l26_treeLeafCostSum leafCost 7 0
    128 + l26_treeLeafCostSum leafCost 7 128 128) + (l26_treeLeafCostSum leafCost 7 256 128 +
    l26_treeLeafCostSum leafCost 7 384 128) = l26_treeLeafCostSum leafCost 9 0 512 := by
  conv_rhs =>
    dsimp only [l26_treeLeafCostSum]
    simp only [show ¬ (512 ≤ 2 ^ 8) by decide, show ¬ (2 ^ 8 ≤ 2 ^ 7) by decide,
      show ¬ (512 - 2 ^ 8 ≤ 2 ^ 7) by decide, ↓reduceIte]
  rfl
theorem count_wRoot749Pebbled1Dyn {Var : Type} {n B_max : ℕ} (hBm : B_max ≤ 7) (v : Var)
    (rIdx9 : QRegister 9 n) (wRootCtrl wDum qEnc : Wire n)
    (rPool : QRegister ((9 - B_max) + 2 ^ B_max) n) (hIdxPool : rIdx9.DisjointWires rPool)
    (hRootIdx : ∀ d : Fin 9, wRootCtrl ≠ rIdx9 d) (hRootPool : ∀ j, wRootCtrl ≠ rPool j)
    (hRootDum : wRootCtrl ≠ wDum) (hRootEnc : wRootCtrl ≠ qEnc)
    (hDumIdx : ∀ d : Fin 9, wDum ≠ rIdx9 d) (hEncIdx : ∀ d : Fin 9, qEnc ≠ rIdx9 d)
    (hDumPool : ∀ j, wDum ≠ rPool j) (hEncPool : ∀ j, qEnc ≠ rPool j) (hDumEnc : wDum ≠ qEnc)
    (dLeaf : (q : ℕ) → (wCtrlLeaf : Wire n) → IsTreeCtrlWire wRootCtrl rPool wCtrlLeaf →
    DynamicCircuit Var n) (leafCost : ℕ → ℕ) (hLeafT : ∀ q wCtrlL hcL, (dLeaf q wCtrlL
    hcL).count .T = leafCost q)
    (hLeafToff : ∀ q wCtrlL hcL, (dLeaf q wCtrlL hcL).count .TOFF = 0) : (wRoot749Pebbled1Dyn
    hBm v rIdx9 wRootCtrl wDum qEnc rPool hIdxPool hRootIdx hRootPool hRootDum hRootEnc
    hDumIdx hEncIdx hDumPool hEncPool hDumEnc dLeaf).count .T = 16 +
    (l26_wTreeRoutingT B_max 9 512 + l26_wTreeRoutingT B_max 9 237) + (l26_treeLeafCostSum
    leafCost 9 0 512 + l26_treeLeafCostSum leafCost 9 512 237) ∧ (wRoot749Pebbled1Dyn hBm v
    rIdx9 wRootCtrl wDum qEnc rPool hIdxPool hRootIdx hRootPool hRootDum hRootEnc hDumIdx
    hEncIdx hDumPool hEncPool hDumEnc dLeaf).count .TOFF = 0 := by
  have hBm9 : B_max ≤ 9 := Nat.le_trans hBm (by decide)
  let j1 : Fin ((9 - B_max) + 2 ^ B_max) := ⟨1, l26_pool_idx_lt hBm (by decide)⟩
  let j2 : Fin ((9 - B_max) + 2 ^ B_max) := ⟨2, l26_pool_idx_lt hBm (by decide)⟩
  let wAnc := rPool j1
  let wTmp := rPool j2
  have hc1 : IsTreeCtrlAt wRootCtrl rPool 7 wAnc :=
    Or.inr ⟨j1, by dsimp [j1]; decide, rfl⟩
  have hTA : wTmp ≠ wAnc := rPool.wires.injective.ne (fun h ↦ by
    have hv := congrArg Fin.val h; dsimp [j1, j2] at hv; omega)
  have hXt : (Circuit.X wRootCtrl).count .T = 0 := rfl
  have hXf : (Circuit.X wRootCtrl).count .TOFF = 0 := rfl
  have hSub := fun base ↦ count_wPrunedSubtreeDyn hBm9 v rIdx9 wRootCtrl wDum qEnc rPool
    hIdxPool hRootIdx hRootPool hRootDum hRootEnc hDumIdx hEncIdx hDumPool hEncPool hDumEnc
    dLeaf leafCost hLeafT hLeafToff 7 (by decide) base 128 wAnc hc1 (by decide) (by decide)
  obtain ⟨t00, f00⟩ := hSub 0
  obtain ⟨t01, f01⟩ := hSub 128
  obtain ⟨t10, f10⟩ := hSub 256
  obtain ⟨t11, f11⟩ := hSub 384
  obtain ⟨tL, fL⟩ := count_l26_pebbledSplit2Dyn v wRootCtrl (rIdx9 ⟨8, by decide⟩) (rIdx9 ⟨7,
    by decide⟩)
    wTmp wAnc (hRootIdx ⟨8, by decide⟩) (hRootPool j2) (hIdxPool.ne ⟨8, by decide⟩ j2)
    (hIdxPool.ne ⟨7, by decide⟩ j2).symm hTA (hIdxPool.ne ⟨7, by decide⟩ j1) _ _ _ _
  obtain ⟨tR, fR⟩ := count_wPrunedSubtreeDyn hBm9 v rIdx9 wRootCtrl wDum qEnc rPool
    hIdxPool hRootIdx hRootPool hRootDum hRootEnc hDumIdx hEncIdx hDumPool hEncPool hDumEnc
    dLeaf leafCost hLeafT hLeafToff 8 (by decide) 512 237 wRootCtrl (Or.inl rfl)
    (by decide) (by decide)
  have hLeaf237 : l26_treeLeafCostSum leafCost 8 512 237 =
      l26_treeLeafCostSum leafCost 9 512 237 := by
    conv_rhs => unfold l26_treeLeafCostSum
    simp
  have hRout := l26_wTreeRoutingT_pebbled1_eq hBm
  have hLeaf512 := l26_treeLeafCostSum_512_split4 leafCost
  dsimp only [wRoot749Pebbled1Dyn, DynamicCircuit.count]
  rw [hXt, hXf, tL, fL, tR, fR, t00, f00, t01, f01, t10, f10, t11, f11, hLeaf237]
  exact ⟨by omega, rfl⟩
theorem subtreeCleanPred_step {n M : ℕ} (P_ext : BitAssignment n → Prop) (wDum qEnc : Wire n)
    (rPool : QRegister M n) (k : ℕ) (hk : k < 9) (j_k : Fin M) (hj_k : j_k.val = 8 - k)
    (γ : BitAssignment n) : (SubtreeCleanPred P_ext wDum qEnc rPool k γ ∧ γ (rPool j_k) = 0) ↔
    SubtreeCleanPred P_ext wDum qEnc rPool (k + 1) γ := by
  dsimp only [SubtreeCleanPred]
  refine ⟨fun ⟨⟨he, hd, hq, hp⟩, hj0⟩ ↦ ⟨he, hd, hq, fun j hj ↦ ?_⟩,
    fun ⟨he, hd, hq, hp⟩ ↦ ⟨⟨he, hd, hq, fun j hj ↦ hp j (by omega)⟩, hp j_k (by omega)⟩⟩
  by_cases hjk : j = j_k
  · subst hjk; exact hj0
  · have hne : j.val ≠ 8 - k := fun h ↦ hjk (Fin.ext (h.trans hj_k.symm))
    exact hp j (by omega)
theorem subtreeCleanPred_upd_lt {n M : ℕ} (P_ext : BitAssignment n → Prop)
    (wDum qEnc : Wire n) (rPool : QRegister M n) (k : ℕ) (j₀ : Fin M) (hj₀ : j₀.val < 9 - k)
    (hExtPool : ∀ j β val, P_ext (Function.update β (rPool j) val) ↔ P_ext β)
    (hDumPool : ∀ j, wDum ≠ rPool j) (hEncPool : ∀ j, qEnc ≠ rPool j) (γ : BitAssignment n)
    (val : ZMod 2) : SubtreeCleanPred P_ext wDum qEnc rPool k
    (Function.update γ (rPool j₀) val) ↔ SubtreeCleanPred P_ext wDum qEnc rPool k γ := by
  dsimp only [SubtreeCleanPred]
  refine and_congr (hExtPool j₀ γ val) (and_congr ?_ (and_congr ?_ ?_))
  · rw [Function.update_of_ne (hDumPool j₀)]
  · rw [Function.update_of_ne (hEncPool j₀)]
  · refine forall_congr' fun j ↦ imp_congr_right fun hj ↦ ?_
    have hne : rPool j ≠ rPool j₀ := rPool.wires.injective.ne (fun h ↦ by
      have hv := congrArg Fin.val h; omega)
    rw [Function.update_of_ne hne]
private theorem leafPhase_pruned_upd_pool {n M : ℕ} (rIdx9 : QRegister 9 n)
    (rPool : QRegister M n) (hIdxPool : rIdx9.DisjointWires rPool)
    (leafPhase : ℕ → BitAssignment n → ZMod 2) (hPhasePool : ∀ q j β val, leafPhase q
    (Function.update β (rPool j) val) = leafPhase q β) (K : ℕ) (hk : K ≤ 9) (base Q : ℕ)
    (j : Fin M) (γ : BitAssignment n) (val : ZMod 2) : leafPhase (base + prunedEffIdx K Q
    (idxValPrefix rIdx9.wires (Function.update γ (rPool j) val) K hk))
    (Function.update γ (rPool j) val) = leafPhase
    (base + prunedEffIdx K Q (idxValPrefix rIdx9.wires γ K hk)) γ := by
  rw [idxValPrefix_upd_ne9 rIdx9 γ (rPool j) val (fun d ↦ hIdxPool.ne d j), hPhasePool]
private theorem prunedEffIdx_9_237_eq_8 {n : ℕ} (rIdx9 : QRegister 9 n) (β : BitAssignment n)
    : prunedEffIdx 9 237 (idxValPrefix rIdx9.wires β 9 le_rfl) = prunedEffIdx 8 237
    (idxValPrefix rIdx9.wires β 8 (by decide)) := by
  have hlt8 : idxValPrefix rIdx9.wires β 8 (by decide) < 2 ^ 8 :=
    idxValPrefix_lt_two_pow rIdx9.wires β 8 (by decide)
  have hstep8 : idxValPrefix rIdx9.wires β 9 le_rfl =
      idxValPrefix rIdx9.wires β 8 (by decide) + (β (rIdx9 ⟨8, by decide⟩)).val * 2 ^ 8 := by
    change idxValPrefix rIdx9.wires β 8 (by decide) +
      (if β (rIdx9 ⟨8, by decide⟩) = 1 then 2 ^ 8 else 0) = _
    rw [l26_ite_eq_zmod2_val_mul]
  have hmod8 : idxValPrefix rIdx9.wires β 9 le_rfl % 2 ^ 8 =
      idxValPrefix rIdx9.wires β 8 (by decide) := by
    rw [hstep8]
    rcases bit_cases (β (rIdx9 ⟨8, by decide⟩)) with hb | hb <;> rw [hb]
    · rw [ZMod.val_zero, zero_mul, add_zero, Nat.mod_eq_of_lt hlt8]
    · rw [ZMod.val_one, one_mul, Nat.add_mod_right, Nat.mod_eq_of_lt hlt8]
  conv_lhs => unfold prunedEffIdx
  simp only [show 237 ≤ 2 ^ 8 by decide, ↓reduceIte, hmod8]
private theorem wRoot749_xSandwich_realizes {Var : Type} [Fintype Var] [DecidableEq Var]
    {n M : ℕ} (P_ext : BitAssignment n → Prop) (rIdx9 : QRegister 9 n)
    (wRootCtrl wDum qEnc : Wire n) (rPool : QRegister M n) (k_root : ℕ)
    (hRootIdx : ∀ d : Fin 9, wRootCtrl ≠ rIdx9 d) (hRootPool : ∀ j, wRootCtrl ≠ rPool j)
    (hRootDum : wRootCtrl ≠ wDum) (hRootEnc : wRootCtrl ≠ qEnc) (hExtRoot : ∀ β val, P_ext
    (Function.update β wRootCtrl val) ↔ P_ext β) (leafPhase : ℕ → BitAssignment n → ZMod 2)
    (hPhaseRoot : ∀ q β val, leafPhase q (Function.update β wRootCtrl val) = leafPhase q β)
    {dLeft dRight : DynamicCircuit Var n} (hdL : p2t_RealizesConstCleanUnitary
    (p2t_ketPredProj (SubtreeCleanPred P_ext wDum qEnc rPool k_root)) dLeft (l26DiagUnitary
    (fun γ ↦ γ wRootCtrl * leafPhase (0 + prunedEffIdx 9 512 (idxValPrefix rIdx9.wires γ 9
    le_rfl)) γ))) (hdR : p2t_RealizesConstCleanUnitary (p2t_ketPredProj (SubtreeCleanPred
    P_ext wDum qEnc rPool k_root)) dRight (l26DiagUnitary (fun γ ↦ γ wRootCtrl * leafPhase
    (512 + prunedEffIdx 9 237 (idxValPrefix rIdx9.wires γ 9 le_rfl)) γ))) :
    p2t_RealizesConstCleanUnitary
    (p2t_ketPredProj (SubtreeCleanPred P_ext wDum qEnc rPool k_root)) (.seq (.circuit
    (Circuit.X wRootCtrl)) (.seq dLeft (.seq (.circuit (Circuit.X wRootCtrl)) dRight)))
    (l26DiagUnitary (fun β ↦ leafPhase (prunedEffIdx 10 749 (idxValPrefix rIdx9.wires β 9
    le_rfl + (β wRootCtrl).val * 512)) β)) := by
  classical
  let S_root := SubtreeCleanPred P_ext wDum qEnc rPool k_root
  let P_root := p2t_ketPredProj S_root
  have hPh : P_rootᴴ = P_root := p2t_ketPredProj_conjTranspose S_root
  let cx := Circuit.X wRootCtrl
  have hSRootX : ∀ β val, S_root (Function.update β wRootCtrl val) ↔ S_root β := fun β val ↦ by
    dsimp only [S_root, SubtreeCleanPred]
    refine and_congr (hExtRoot β val) (and_congr ?_ (and_congr ?_ ?_))
    · rw [Function.update_of_ne hRootDum.symm]
    · rw [Function.update_of_ne hRootEnc.symm]
    · refine forall_congr' fun j ↦ imp_congr_right fun _ ↦ ?_
      rw [Function.update_of_ne (hRootPool j).symm]
  have hCommX : P_root * cx.eval.1 = cx.eval.1 * P_root := by
    apply MeasureBranchHadamardSem.matrix_ext_ket; intro β
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, mbh_ket_eq_ket,
        p2t_ketPredProj_mul_ket, ← mbh_ket_eq_ket, ket_X]
    by_cases hs : S_root β
    · rw [ite_eq_left hs, ket_X, mbh_ket_eq_ket, p2t_ketPredProj_mul_ket,
          ite_eq_left ((hSRootX β _).mpr hs)]
    · rw [ite_eq_right hs, mbh_ket_eq_ket, p2t_ketPredProj_mul_ket,
          ite_eq_right (mt (hSRootX β _).mp hs), Matrix.mulVec_zero]
  have hAbs : ∀ U : Operator (2 ^ n), P_root * U = U * P_root → P_root * (U * P_root) = U *
    P_root :=
    fun U hc ↦ by rw [← Matrix.mul_assoc, hc, Matrix.mul_assoc, ketPredProj_mul_self]
  have h34 := p2t_RealizesConstCleanUnitary_seq_proj hPh hPh
    (p2t_RealizesConstCleanUnitary_circuit (Var := Var) P_root cx) hdR (hAbs cx.eval.1 hCommX)
  have h234 := p2t_RealizesConstCleanUnitary_seq_proj hPh hPh
    hdL h34 (hAbs _ (ketPredProj_comm_l26DiagUnitary S_root _))
  have h1234 := p2t_RealizesConstCleanUnitary_seq_proj hPh hPh
    (p2t_RealizesConstCleanUnitary_circuit (Var := Var) P_root cx) h234 (hAbs cx.eval.1 hCommX)
  refine p2t_RealizesConstCleanUnitary_congr_unitary hPh h1234 ?_
  apply congrArg (· * P_root)
  apply MeasureBranchHadamardSem.matrix_ext_ket; intro β
  dsimp only [cx]
  simp only [Submonoid.coe_mul, Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ket_X,
    l26DiagUnitary_mulVec_ket, Matrix.mulVec_smul, smul_smul, neg_one_pow_zmod2_mul]
  have hRet : Function.update (Function.update β wRootCtrl (β wRootCtrl + 1)) wRootCtrl
      (Function.update β wRootCtrl (β wRootCtrl + 1) wRootCtrl + 1) = β := by
    rw [Function.update_self, Function.update_idem]
    have hcanc : β wRootCtrl + 1 + 1 = β wRootCtrl := by
      rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
    rw [hcanc, Function.update_eq_self]
  rw [hRet, Function.update_self,
      idxValPrefix_upd_ne9 rIdx9 β wRootCtrl (β wRootCtrl + 1)
        (fun d ↦ (hRootIdx d).symm) 9 le_rfl,
      hPhaseRoot _ β (β wRootCtrl + 1), Nat.zero_add]
  refine congrArg (fun e : ZMod 2 ↦ ((-1 : ℂ) ^ e.val) • ket β) ?_
  have hlt9 : idxValPrefix rIdx9.wires β 9 le_rfl < 512 :=
    idxValPrefix_lt_two_pow rIdx9.wires β 9 le_rfl
  have hnle749 : ¬ (749 ≤ 2 ^ 9) := by decide
  rcases bit_cases (β wRootCtrl) with hb | hb
  · have h01 : (0 : ZMod 2) + 1 = 1 := by decide
    have heff0 : prunedEffIdx 10 749 (idxValPrefix rIdx9.wires β 9 le_rfl + 0 * 512) =
        prunedEffIdx 9 512 (idxValPrefix rIdx9.wires β 9 le_rfl) := by
      rw [zero_mul, add_zero, prunedEffIdx_eq_self 9 512 _ le_rfl hlt9]
      unfold prunedEffIdx
      simp only [hnle749, show idxValPrefix rIdx9.wires β 9 le_rfl < 2 ^ 9 from hlt9, ↓reduceIte]
    rw [hb, h01, zero_mul, one_mul, add_zero, ZMod.val_zero, heff0]
  · have h11 : (1 : ZMod 2) + 1 = 0 := by decide
    have hnlt : ¬ (idxValPrefix rIdx9.wires β 9 le_rfl + 2 ^ 9 < 2 ^ 9) := by omega
    have heff1 : prunedEffIdx 10 749 (idxValPrefix rIdx9.wires β 9 le_rfl + 1 * 512) =
        512 + prunedEffIdx 9 237 (idxValPrefix rIdx9.wires β 9 le_rfl) := by
      rw [one_mul, show (512 : ℕ) = 2 ^ 9 by rfl]
      conv_lhs => unfold prunedEffIdx
      simp only [hnle749, hnlt, ↓reduceIte, Nat.add_mod_right,
        Nat.mod_eq_of_lt (show idxValPrefix rIdx9.wires β 9 le_rfl < 2 ^ 9 from hlt9)]
      rfl
    rw [hb, h11, one_mul, zero_mul, zero_add, ZMod.val_one, heff1]
theorem wRoot749Pebbled1Dyn_realizes {Var : Type} [Fintype Var] [DecidableEq Var]
    {n B_max : ℕ}
    (hBm : B_max ≤ 7) (v : Var)
    (P_ext : BitAssignment n → Prop)
    (rIdx9 : QRegister 9 n) (wRootCtrl wDum qEnc : Wire n)
    (rPool : QRegister ((9 - B_max) + 2 ^ B_max) n)
    (hIdxPool : rIdx9.DisjointWires rPool)
    (hRootIdx : ∀ d : Fin 9, wRootCtrl ≠ rIdx9 d)
    (hRootPool : ∀ j, wRootCtrl ≠ rPool j)
    (hRootDum : wRootCtrl ≠ wDum) (hRootEnc : wRootCtrl ≠ qEnc)
    (hDumIdx : ∀ d : Fin 9, wDum ≠ rIdx9 d)
    (hEncIdx : ∀ d : Fin 9, qEnc ≠ rIdx9 d)
    (hDumPool : ∀ j, wDum ≠ rPool j)
    (hEncPool : ∀ j, qEnc ≠ rPool j)
    (hDumEnc : wDum ≠ qEnc)
    (hExtRoot : ∀ β val, P_ext (Function.update β wRootCtrl val) ↔ P_ext β)
    (hExtPool : ∀ j β val, P_ext (Function.update β (rPool j) val) ↔ P_ext β)
    (dLeaf : (q : ℕ) → (wCtrlLeaf : Wire n) →
      IsTreeCtrlWire wRootCtrl rPool wCtrlLeaf → DynamicCircuit Var n)
    (leafPhase : ℕ → BitAssignment n → ZMod 2)
    (hPhaseRoot : ∀ q β val, leafPhase q (Function.update β wRootCtrl val) = leafPhase q β)
    (hPhasePool : ∀ q j β val, leafPhase q (Function.update β (rPool j) val) = leafPhase q β)
    (hLeafReal : ∀ q wCtrlL hcL,
      p2t_RealizesConstCleanUnitary
        (p2t_ketPredProj (fun β ↦ P_ext β ∧ β wDum = 0 ∧ β qEnc = 0))
        (dLeaf q wCtrlL hcL)
        (l26DiagUnitary (fun β ↦ β wCtrlL * leafPhase q β))) :
    p2t_RealizesConstCleanUnitary
      (p2t_ketPredProj (SubtreeCleanPred P_ext wDum qEnc rPool 8))
      (wRoot749Pebbled1Dyn hBm v rIdx9 wRootCtrl wDum qEnc rPool
        hIdxPool hRootIdx hRootPool hRootDum hRootEnc hDumIdx hEncIdx hDumPool hEncPool hDumEnc
        dLeaf)
      (l26DiagUnitary (fun β ↦
        leafPhase (prunedEffIdx 10 749
          (idxValPrefix rIdx9.wires β 9 le_rfl + (β wRootCtrl).val * 512)) β)) := by
  classical
  have hBm9 : B_max ≤ 9 := Nat.le_trans hBm (by decide)
  let j1 : Fin ((9 - B_max) + 2 ^ B_max) := ⟨1, l26_pool_idx_lt hBm (by decide)⟩
  let j2 : Fin ((9 - B_max) + 2 ^ B_max) := ⟨2, l26_pool_idx_lt hBm (by decide)⟩
  let wAnc := rPool j1
  let wTmp := rPool j2
  let u8 := rIdx9 ⟨8, by decide⟩
  let u7 := rIdx9 ⟨7, by decide⟩
  have hc1 : IsTreeCtrlAt wRootCtrl rPool 7 wAnc :=
    Or.inr ⟨j1, by dsimp [j1]; decide, rfl⟩
  have hTA : wTmp ≠ wAnc := rPool.wires.injective.ne (fun h ↦ by
    have hv := congrArg Fin.val h; dsimp [j1, j2] at hv; omega)
  let S_raw6 := SubtreeCleanPred P_ext wDum qEnc rPool 6
  let S_sub7 := SubtreeCleanPred P_ext wDum qEnc rPool 7
  let S_root := SubtreeCleanPred P_ext wDum qEnc rPool 8
  let P_root := p2t_ketPredProj S_root
  have hPh : P_rootᴴ = P_root := p2t_ketPredProj_conjTranspose S_root
  have hSub7_iff : ∀ γ, (S_raw6 γ ∧ γ wTmp = 0) ↔ S_sub7 γ :=
    subtreeCleanPred_step P_ext wDum qEnc rPool 6 (by decide) j2 rfl
  have hRoot_iff : ∀ β, (S_raw6 β ∧ β wTmp = 0 ∧ β wAnc = 0) ↔ S_root β := fun β ↦ by
    rw [← and_assoc, hSub7_iff]
    exact subtreeCleanPred_step P_ext wDum qEnc rPool 7 (by decide) j1 rfl β
  have hSubReal := fun base ↦ by
    have h0 := wPrunedSubtreeDyn_realizes hBm9 v P_ext rIdx9 wRootCtrl wDum qEnc rPool
        hIdxPool hRootIdx hRootPool hRootDum hRootEnc hDumIdx hEncIdx hDumPool hEncPool
        hDumEnc hExtRoot hExtPool dLeaf leafPhase hPhaseRoot hPhasePool hLeafReal 7
        (by decide) base 128 wAnc hc1 (by decide) (by decide)
    exact p2t_RealizesConstCleanUnitary_mono_proj
      (p2t_ketPredProj_conjTranspose _) (p2t_ketPredProj_conjTranspose _)
      (p2t_ketPredProj_mul_imp fun γ hγ ↦ (hSub7_iff γ).mp hγ) h0
  have hdL0 := l26_pebbledSplit2Dyn_realizes v wRootCtrl u8 u7 wTmp wAnc
    (hRootIdx ⟨8, by decide⟩) (hRootPool j2) (hIdxPool.ne ⟨8, by decide⟩ j2)
    (hIdxPool.ne ⟨7, by decide⟩ j2).symm hTA (hIdxPool.ne ⟨7, by decide⟩ j1)
    (hRootPool j1) (hIdxPool.ne ⟨8, by decide⟩ j1)
    S_raw6
    (subtreeCleanPred_upd_lt P_ext wDum qEnc rPool 6 j2 (by dsimp [j2]; decide)
      hExtPool hDumPool hEncPool)
    (subtreeCleanPred_upd_lt P_ext wDum qEnc rPool 6 j1 (by dsimp [j1]; decide)
      hExtPool hDumPool hEncPool)
    _ _ _ _
    (fun γ ↦ leafPhase (0 + prunedEffIdx 7 128 (idxValPrefix rIdx9.wires γ 7 (by decide))) γ)
    (fun γ ↦ leafPhase (128 + prunedEffIdx 7 128 (idxValPrefix rIdx9.wires γ 7 (by decide))) γ)
    (fun γ ↦ leafPhase (256 + prunedEffIdx 7 128 (idxValPrefix rIdx9.wires γ 7 (by decide))) γ)
    (fun γ ↦ leafPhase (384 + prunedEffIdx 7 128 (idxValPrefix rIdx9.wires γ 7 (by decide))) γ)
    (leafPhase_pruned_upd_pool rIdx9 rPool hIdxPool leafPhase hPhasePool 7 (by decide) 0 128 j2)
    (leafPhase_pruned_upd_pool rIdx9 rPool hIdxPool leafPhase hPhasePool 7 (by decide) 128 128 j2)
    (leafPhase_pruned_upd_pool rIdx9 rPool hIdxPool leafPhase hPhasePool 7 (by decide) 256 128 j2)
    (leafPhase_pruned_upd_pool rIdx9 rPool hIdxPool leafPhase hPhasePool 7 (by decide) 384 128 j2)
    (leafPhase_pruned_upd_pool rIdx9 rPool hIdxPool leafPhase hPhasePool 7 (by decide) 0 128 j1)
    (leafPhase_pruned_upd_pool rIdx9 rPool hIdxPool leafPhase hPhasePool 7 (by decide) 128 128 j1)
    (leafPhase_pruned_upd_pool rIdx9 rPool hIdxPool leafPhase hPhasePool 7 (by decide) 256 128 j1)
    (leafPhase_pruned_upd_pool rIdx9 rPool hIdxPool leafPhase hPhasePool 7 (by decide) 384 128 j1)
    (hSubReal 0) (hSubReal 128) (hSubReal 256) (hSubReal 384)
  have hdL1 := p2t_RealizesConstCleanUnitary_mono_proj (p2t_ketPredProj_conjTranspose _) hPh
      (p2t_ketPredProj_mul_imp fun β hβ ↦ (hRoot_iff β).mpr hβ) hdL0
  have hdL := p2t_RealizesConstCleanUnitary_congr_unitary
    (U₂ := l26DiagUnitary (fun γ ↦
      γ wRootCtrl * leafPhase (0 + prunedEffIdx 9 512 (idxValPrefix rIdx9.wires γ 9 le_rfl)) γ))
    hPh hdL1 (by
      rw [l26DiagUnitary_congr (fun γ ↦ ?_)]
      congr 1
      exact l26_split2_index_eq rIdx9 γ 7 (by decide) 0 512 (by decide) (fun q ↦ leafPhase q γ))
  have hdR0 := wPrunedSubtreeDyn_realizes hBm9 v P_ext rIdx9 wRootCtrl wDum qEnc rPool
      hIdxPool hRootIdx hRootPool hRootDum hRootEnc hDumIdx hEncIdx hDumPool hEncPool hDumEnc
      hExtRoot hExtPool dLeaf leafPhase hPhaseRoot hPhasePool hLeafReal 8 (by decide) 512 237
      wRootCtrl (Or.inl rfl) (by decide) (by decide)
  have hdR := p2t_RealizesConstCleanUnitary_congr_unitary
    (U₂ := l26DiagUnitary (fun γ ↦
      γ wRootCtrl * leafPhase (512 + prunedEffIdx 9 237 (idxValPrefix rIdx9.wires γ 9 le_rfl)) γ))
    hPh hdR0 (by
      rw [l26DiagUnitary_congr (fun β ↦ ?_)]
      rw [prunedEffIdx_9_237_eq_8 rIdx9 β])
  exact wRoot749_xSandwich_realizes P_ext rIdx9 wRootCtrl wDum qEnc rPool 8
    hRootIdx hRootPool hRootDum hRootEnc hExtRoot leafPhase hPhaseRoot hdL hdR
def wRoot749Pebbled2Dyn {Var : Type} {n B_max : ℕ} (hBm : B_max ≤ 6) (hB1 : 1 ≤ B_max)
    (v : Var) (rIdx9 : QRegister 9 n) (wRootCtrl wDum qEnc : Wire n)
    (rPool : QRegister ((9 - B_max) + 2 ^ B_max) n) (hIdxPool : rIdx9.DisjointWires rPool)
    (hRootIdx : ∀ d : Fin 9, wRootCtrl ≠ rIdx9 d) (hRootPool : ∀ j, wRootCtrl ≠ rPool j)
    (hRootDum : wRootCtrl ≠ wDum) (hRootEnc : wRootCtrl ≠ qEnc)
    (hDumIdx : ∀ d : Fin 9, wDum ≠ rIdx9 d) (hEncIdx : ∀ d : Fin 9, qEnc ≠ rIdx9 d)
    (hDumPool : ∀ j, wDum ≠ rPool j) (hEncPool : ∀ j, qEnc ≠ rPool j) (hDumEnc : wDum ≠ qEnc)
    (dLeaf : (q : ℕ) → (wCtrlLeaf : Wire n) → IsTreeCtrlWire wRootCtrl rPool wCtrlLeaf →
    DynamicCircuit Var n) : DynamicCircuit Var n :=
  have hBm9 : B_max ≤ 9 := Nat.le_trans hBm (by decide)
  let j2 : Fin ((9 - B_max) + 2 ^ B_max) := ⟨2, l26_pool_idx2_lt hBm hB1 (by decide)⟩
  let j3 : Fin ((9 - B_max) + 2 ^ B_max) := ⟨3, l26_pool_idx2_lt hBm hB1 (by decide)⟩
  let j4 : Fin ((9 - B_max) + 2 ^ B_max) := ⟨4, l26_pool_idx2_lt hBm hB1 (by decide)⟩
  let wAnc6 := rPool j2
  let wTmp7 := rPool j3
  let wTmp8 := rPool j4
  let u8 := rIdx9 ⟨8, by decide⟩
  let u7 := rIdx9 ⟨7, by decide⟩
  let u6 := rIdx9 ⟨6, by decide⟩
  have hc2 : IsTreeCtrlAt wRootCtrl rPool 6 wAnc6 :=
    Or.inr ⟨j2, by dsimp [j2]; decide, rfl⟩
  have h32 : wTmp7 ≠ wAnc6 := rPool.wires.injective.ne (fun h ↦ by
    have hv := congrArg Fin.val h; dsimp [j2, j3] at hv; omega)
  have h43 : wTmp8 ≠ wTmp7 := rPool.wires.injective.ne (fun h ↦ by
    have hv := congrArg Fin.val h; dsimp [j3, j4] at hv; omega)
  let dSub6 (base Q : ℕ) := wPrunedSubtreeDyn hBm9 v rIdx9 wRootCtrl wDum qEnc rPool hIdxPool
      hRootIdx hRootPool hRootDum hRootEnc hDumIdx hEncIdx hDumPool hEncPool hDumEnc dLeaf 6
      (by decide) base Q wAnc6 hc2
  let dSub6Neg (base : ℕ) :=
    l26_uncomputeSandwichNegDyn v wRootCtrl u8 wTmp8
      (hRootIdx ⟨8, by decide⟩) (hRootPool j4) (hIdxPool.ne ⟨8, by decide⟩ j4)
      (dSub6 base 64)
  let dSub6Pos (base : ℕ) :=
    l26_uncomputeSandwichPosDyn v wRootCtrl u8 wTmp8
      (hRootIdx ⟨8, by decide⟩) (hRootPool j4) (hIdxPool.ne ⟨8, by decide⟩ j4)
      (dSub6 base 64)
  let dLeft256_0 :=
    l26_pebbledSplit2Dyn v wTmp8 u7 u6 wTmp7 wAnc6
      (hIdxPool.ne ⟨7, by decide⟩ j4).symm h43 (hIdxPool.ne ⟨7, by decide⟩ j3)
      (hIdxPool.ne ⟨6, by decide⟩ j3).symm h32 (hIdxPool.ne ⟨6, by decide⟩ j2)
      (dSub6Neg 0) (dSub6Neg 64) (dSub6Neg 128) (dSub6Neg 192)
  let dLeft256_1 :=
    l26_pebbledSplit2Dyn v wTmp8 u7 u6 wTmp7 wAnc6
      (hIdxPool.ne ⟨7, by decide⟩ j4).symm h43 (hIdxPool.ne ⟨7, by decide⟩ j3)
      (hIdxPool.ne ⟨6, by decide⟩ j3).symm h32 (hIdxPool.ne ⟨6, by decide⟩ j2)
      (dSub6Pos 256) (dSub6Pos 320) (dSub6Pos 384) (dSub6Pos 448)
  let dLeft512 :=
    l26_branchSplitDyn v wRootCtrl u8 wTmp8
      (hRootIdx ⟨8, by decide⟩) (hRootPool j4) (hIdxPool.ne ⟨8, by decide⟩ j4)
      dLeft256_0 dLeft256_1
  let dRight237 :=
    l26_pebbledSplit2Dyn v wRootCtrl u7 u6 wTmp7 wAnc6
      (hRootIdx ⟨7, by decide⟩) (hRootPool j3) (hIdxPool.ne ⟨7, by decide⟩ j3)
      (hIdxPool.ne ⟨6, by decide⟩ j3).symm h32 (hIdxPool.ne ⟨6, by decide⟩ j2)
      (dSub6 512 64) (dSub6 576 64) (dSub6 640 64) (dSub6 704 45)
  .seq (.circuit (Circuit.X wRootCtrl))
    (.seq dLeft512
      (.seq (.circuit (Circuit.X wRootCtrl)) dRight237))
theorem l26_wTreeRoutingT_pebbled2_eq {B_max : ℕ} (hBm : B_max ≤ 6) : (4 + (28 + 4 * (4 +
    l26_wTreeRoutingT B_max 6 64)) + (28 + 4 * (4 + l26_wTreeRoutingT B_max 6 64))) + (28 + 3
    * l26_wTreeRoutingT B_max 6 64 + l26_wTreeRoutingT B_max 6 45) = 80 +
    (l26_wTreeRoutingT B_max 9 512 + l26_wTreeRoutingT B_max 9 237) := by
  interval_cases B_max <;> rfl
theorem l26_treeLeafCostSum_512_split8 (leafCost : ℕ → ℕ) : ((l26_treeLeafCostSum leafCost 6 0
    64 + l26_treeLeafCostSum leafCost 6 64 64) + (l26_treeLeafCostSum leafCost 6 128 64 +
    l26_treeLeafCostSum leafCost 6 192 64)) + ((l26_treeLeafCostSum leafCost 6 256 64 +
    l26_treeLeafCostSum leafCost 6 320 64) + (l26_treeLeafCostSum leafCost 6 384 64 +
    l26_treeLeafCostSum leafCost 6 448 64)) = l26_treeLeafCostSum leafCost 9 0 512 := by
  conv_rhs =>
    dsimp only [l26_treeLeafCostSum]
    simp only [show ¬ (512 ≤ 2 ^ 8) by decide, show ¬ (2 ^ 8 ≤ 2 ^ 7) by decide,
      show ¬ (512 - 2 ^ 8 ≤ 2 ^ 7) by decide, show ¬ (2 ^ 7 ≤ 2 ^ 6) by decide,
      show ¬ (2 ^ 8 - 2 ^ 7 ≤ 2 ^ 6) by decide,
      show ¬ (512 - 2 ^ 8 - 2 ^ 7 ≤ 2 ^ 6) by decide, ↓reduceIte]
  rfl
theorem l26_treeLeafCostSum_237_split4 (leafCost : ℕ → ℕ) : (l26_treeLeafCostSum leafCost 6
    512 64 + l26_treeLeafCostSum leafCost 6 576 64) + (l26_treeLeafCostSum leafCost 6 640 64 +
    l26_treeLeafCostSum leafCost 6 704 45) = l26_treeLeafCostSum leafCost 9 512 237 := by
  conv_rhs =>
    dsimp only [l26_treeLeafCostSum]
    simp only [show (237 ≤ 2 ^ 8) by decide, show ¬ (237 ≤ 2 ^ 7) by decide,
      show ¬ (2 ^ 7 ≤ 2 ^ 6) by decide, show ¬ (237 - 2 ^ 7 ≤ 2 ^ 6) by decide, ↓reduceIte]
  rfl
theorem count_wRoot749Pebbled2Dyn {Var : Type} {n B_max : ℕ} (hBm : B_max ≤ 6)
    (hB1 : 1 ≤ B_max) (v : Var) (rIdx9 : QRegister 9 n) (wRootCtrl wDum qEnc : Wire n)
    (rPool : QRegister ((9 - B_max) + 2 ^ B_max) n) (hIdxPool : rIdx9.DisjointWires rPool)
    (hRootIdx : ∀ d : Fin 9, wRootCtrl ≠ rIdx9 d) (hRootPool : ∀ j, wRootCtrl ≠ rPool j)
    (hRootDum : wRootCtrl ≠ wDum) (hRootEnc : wRootCtrl ≠ qEnc)
    (hDumIdx : ∀ d : Fin 9, wDum ≠ rIdx9 d) (hEncIdx : ∀ d : Fin 9, qEnc ≠ rIdx9 d)
    (hDumPool : ∀ j, wDum ≠ rPool j) (hEncPool : ∀ j, qEnc ≠ rPool j) (hDumEnc : wDum ≠ qEnc)
    (dLeaf : (q : ℕ) → (wCtrlLeaf : Wire n) → IsTreeCtrlWire wRootCtrl rPool wCtrlLeaf →
    DynamicCircuit Var n) (leafCost : ℕ → ℕ) (hLeafT : ∀ q wCtrlL hcL, (dLeaf q wCtrlL
    hcL).count .T = leafCost q)
    (hLeafToff : ∀ q wCtrlL hcL, (dLeaf q wCtrlL hcL).count .TOFF = 0) : (wRoot749Pebbled2Dyn
    hBm hB1 v rIdx9 wRootCtrl wDum qEnc rPool hIdxPool hRootIdx hRootPool hRootDum hRootEnc
    hDumIdx hEncIdx hDumPool hEncPool hDumEnc dLeaf).count .T = 80 +
    (l26_wTreeRoutingT B_max 9 512 + l26_wTreeRoutingT B_max 9 237) + (l26_treeLeafCostSum
    leafCost 9 0 512 + l26_treeLeafCostSum leafCost 9 512 237) ∧ (wRoot749Pebbled2Dyn hBm hB1
    v rIdx9 wRootCtrl wDum qEnc rPool hIdxPool hRootIdx hRootPool hRootDum hRootEnc hDumIdx
    hEncIdx hDumPool hEncPool hDumEnc dLeaf).count .TOFF = 0 := by
  have hBm9 : B_max ≤ 9 := Nat.le_trans hBm (by decide)
  let j2 : Fin ((9 - B_max) + 2 ^ B_max) := ⟨2, l26_pool_idx2_lt hBm hB1 (by decide)⟩
  let j3 : Fin ((9 - B_max) + 2 ^ B_max) := ⟨3, l26_pool_idx2_lt hBm hB1 (by decide)⟩
  let j4 : Fin ((9 - B_max) + 2 ^ B_max) := ⟨4, l26_pool_idx2_lt hBm hB1 (by decide)⟩
  let wAnc6 := rPool j2
  let wTmp7 := rPool j3
  let wTmp8 := rPool j4
  let u8 := rIdx9 ⟨8, by decide⟩
  let u7 := rIdx9 ⟨7, by decide⟩
  let u6 := rIdx9 ⟨6, by decide⟩
  have hc2 : IsTreeCtrlAt wRootCtrl rPool 6 wAnc6 :=
    Or.inr ⟨j2, by dsimp [j2]; decide, rfl⟩
  have h32 : wTmp7 ≠ wAnc6 := rPool.wires.injective.ne (fun h ↦ by
    have hv := congrArg Fin.val h; dsimp [j2, j3] at hv; omega)
  have h43 : wTmp8 ≠ wTmp7 := rPool.wires.injective.ne (fun h ↦ by
    have hv := congrArg Fin.val h; dsimp [j3, j4] at hv; omega)
  let dSub6 (base Q : ℕ) := wPrunedSubtreeDyn hBm9 v rIdx9 wRootCtrl wDum qEnc rPool hIdxPool
      hRootIdx hRootPool hRootDum hRootEnc hDumIdx hEncIdx hDumPool hEncPool hDumEnc dLeaf 6
      (by decide) base Q wAnc6 hc2
  let dSub6Neg (base : ℕ) :=
    l26_uncomputeSandwichNegDyn v wRootCtrl u8 wTmp8
      (hRootIdx ⟨8, by decide⟩) (hRootPool j4) (hIdxPool.ne ⟨8, by decide⟩ j4)
      (dSub6 base 64)
  let dSub6Pos (base : ℕ) :=
    l26_uncomputeSandwichPosDyn v wRootCtrl u8 wTmp8
      (hRootIdx ⟨8, by decide⟩) (hRootPool j4) (hIdxPool.ne ⟨8, by decide⟩ j4)
      (dSub6 base 64)
  let dLeft256_0 :=
    l26_pebbledSplit2Dyn v wTmp8 u7 u6 wTmp7 wAnc6
      (hIdxPool.ne ⟨7, by decide⟩ j4).symm h43 (hIdxPool.ne ⟨7, by decide⟩ j3)
      (hIdxPool.ne ⟨6, by decide⟩ j3).symm h32 (hIdxPool.ne ⟨6, by decide⟩ j2)
      (dSub6Neg 0) (dSub6Neg 64) (dSub6Neg 128) (dSub6Neg 192)
  let dLeft256_1 :=
    l26_pebbledSplit2Dyn v wTmp8 u7 u6 wTmp7 wAnc6
      (hIdxPool.ne ⟨7, by decide⟩ j4).symm h43 (hIdxPool.ne ⟨7, by decide⟩ j3)
      (hIdxPool.ne ⟨6, by decide⟩ j3).symm h32 (hIdxPool.ne ⟨6, by decide⟩ j2)
      (dSub6Pos 256) (dSub6Pos 320) (dSub6Pos 384) (dSub6Pos 448)
  have hXt : (Circuit.X wRootCtrl).count .T = 0 := rfl
  have hXf : (Circuit.X wRootCtrl).count .TOFF = 0 := rfl
  have hSub6 := fun base Q hQ1 hQk ↦ count_wPrunedSubtreeDyn hBm9 v rIdx9 wRootCtrl wDum qEnc rPool
    hIdxPool hRootIdx hRootPool hRootDum hRootEnc hDumIdx hEncIdx hDumPool hEncPool hDumEnc
    dLeaf leafCost hLeafT hLeafToff 6 (by decide) base Q wAnc6 hc2 hQ1 hQk
  have h64T := fun base ↦ (hSub6 base 64 (by decide) (by decide)).1
  have h64F := fun base ↦ (hSub6 base 64 (by decide) (by decide)).2
  obtain ⟨tR3, fR3⟩ := hSub6 704 45 (by decide) (by decide)
  have hNeg := fun base ↦ count_l26_uncomputeSandwichNegDyn v wRootCtrl u8 wTmp8
    (hRootIdx ⟨8, by decide⟩) (hRootPool j4) (hIdxPool.ne ⟨8, by decide⟩ j4) (dSub6 base 64)
  have hPos := fun base ↦ count_l26_uncomputeSandwichPosDyn v wRootCtrl u8 wTmp8
    (hRootIdx ⟨8, by decide⟩) (hRootPool j4) (hIdxPool.ne ⟨8, by decide⟩ j4) (dSub6 base 64)
  obtain ⟨tL0, fL0⟩ := count_l26_pebbledSplit2Dyn v wTmp8 u7 u6 wTmp7 wAnc6
    (hIdxPool.ne ⟨7, by decide⟩ j4).symm h43 (hIdxPool.ne ⟨7, by decide⟩ j3)
    (hIdxPool.ne ⟨6, by decide⟩ j3).symm h32 (hIdxPool.ne ⟨6, by decide⟩ j2)
    (dSub6Neg 0) (dSub6Neg 64) (dSub6Neg 128) (dSub6Neg 192)
  obtain ⟨tL1, fL1⟩ := count_l26_pebbledSplit2Dyn v wTmp8 u7 u6 wTmp7 wAnc6
    (hIdxPool.ne ⟨7, by decide⟩ j4).symm h43 (hIdxPool.ne ⟨7, by decide⟩ j3)
    (hIdxPool.ne ⟨6, by decide⟩ j3).symm h32 (hIdxPool.ne ⟨6, by decide⟩ j2)
    (dSub6Pos 256) (dSub6Pos 320) (dSub6Pos 384) (dSub6Pos 448)
  obtain ⟨tL, fL⟩ := count_l26_branchSplitDyn v wRootCtrl u8 wTmp8
    (hRootIdx ⟨8, by decide⟩) (hRootPool j4) (hIdxPool.ne ⟨8, by decide⟩ j4) dLeft256_0 dLeft256_1
  obtain ⟨tR, fR⟩ := count_l26_pebbledSplit2Dyn v wRootCtrl u7 u6 wTmp7 wAnc6
    (hRootIdx ⟨7, by decide⟩) (hRootPool j3) (hIdxPool.ne ⟨7, by decide⟩ j3)
    (hIdxPool.ne ⟨6, by decide⟩ j3).symm h32 (hIdxPool.ne ⟨6, by decide⟩ j2)
    (dSub6 512 64) (dSub6 576 64) (dSub6 640 64) (dSub6 704 45)
  have hRout := l26_wTreeRoutingT_pebbled2_eq hBm
  have hLeaf512 := l26_treeLeafCostSum_512_split8 leafCost
  have hLeaf237 := l26_treeLeafCostSum_237_split4 leafCost
  dsimp only [wRoot749Pebbled2Dyn, DynamicCircuit.count]
  rw[hXt, hXf, tL, fL, tL0, fL0, tL1, fL1, (hNeg 0).1, (hNeg 0).2, (hNeg 64).1, (hNeg 64).2,
      (hNeg 128).1, (hNeg 128).2, (hNeg 192).1, (hNeg 192).2, (hPos 256).1, (hPos 256).2,
      (hPos 320).1, (hPos 320).2, (hPos 384).1, (hPos 384).2, (hPos 448).1, (hPos 448).2,
      h64T 0, h64F 0, h64T 64, h64F 64, h64T 128, h64F 128, h64T 192, h64F 192, h64T 256,
      h64F 256, h64T 320, h64F 320, h64T 384, h64F 384, h64T 448, h64F 448, tR, fR, h64T 512,
      h64F 512, h64T 576, h64F 576, h64T 640, h64F 640, tR3, fR3]
  exact ⟨by omega, rfl⟩
theorem wRoot749Pebbled2Dyn_realizes {Var : Type} [Fintype Var] [DecidableEq Var]
    {n B_max : ℕ}
    (hBm : B_max ≤ 6) (hB1 : 1 ≤ B_max) (v : Var)
    (P_ext : BitAssignment n → Prop)
    (rIdx9 : QRegister 9 n) (wRootCtrl wDum qEnc : Wire n)
    (rPool : QRegister ((9 - B_max) + 2 ^ B_max) n)
    (hIdxPool : rIdx9.DisjointWires rPool)
    (hRootIdx : ∀ d : Fin 9, wRootCtrl ≠ rIdx9 d)
    (hRootPool : ∀ j, wRootCtrl ≠ rPool j)
    (hRootDum : wRootCtrl ≠ wDum) (hRootEnc : wRootCtrl ≠ qEnc)
    (hDumIdx : ∀ d : Fin 9, wDum ≠ rIdx9 d)
    (hEncIdx : ∀ d : Fin 9, qEnc ≠ rIdx9 d)
    (hDumPool : ∀ j, wDum ≠ rPool j)
    (hEncPool : ∀ j, qEnc ≠ rPool j)
    (hDumEnc : wDum ≠ qEnc)
    (hExtRoot : ∀ β val, P_ext (Function.update β wRootCtrl val) ↔ P_ext β)
    (hExtPool : ∀ j β val, P_ext (Function.update β (rPool j) val) ↔ P_ext β)
    (dLeaf : (q : ℕ) → (wCtrlLeaf : Wire n) →
      IsTreeCtrlWire wRootCtrl rPool wCtrlLeaf → DynamicCircuit Var n)
    (leafPhase : ℕ → BitAssignment n → ZMod 2)
    (hPhaseRoot : ∀ q β val, leafPhase q (Function.update β wRootCtrl val) = leafPhase q β)
    (hPhasePool : ∀ q j β val, leafPhase q (Function.update β (rPool j) val) = leafPhase q β)
    (hLeafReal : ∀ q wCtrlL hcL,
      p2t_RealizesConstCleanUnitary
        (p2t_ketPredProj (fun β ↦ P_ext β ∧ β wDum = 0 ∧ β qEnc = 0))
        (dLeaf q wCtrlL hcL)
        (l26DiagUnitary (fun β ↦ β wCtrlL * leafPhase q β))) :
    p2t_RealizesConstCleanUnitary
      (p2t_ketPredProj (SubtreeCleanPred P_ext wDum qEnc rPool 7))
      (wRoot749Pebbled2Dyn hBm hB1 v rIdx9 wRootCtrl wDum qEnc rPool
        hIdxPool hRootIdx hRootPool hRootDum hRootEnc hDumIdx hEncIdx hDumPool hEncPool hDumEnc
        dLeaf)
      (l26DiagUnitary (fun β ↦
        leafPhase (prunedEffIdx 10 749
          (idxValPrefix rIdx9.wires β 9 le_rfl + (β wRootCtrl).val * 512)) β)) := by
  classical
  have hBm9 : B_max ≤ 9 := Nat.le_trans hBm (by decide)
  let j2 : Fin ((9 - B_max) + 2 ^ B_max) := ⟨2, l26_pool_idx2_lt hBm hB1 (by decide)⟩
  let j3 : Fin ((9 - B_max) + 2 ^ B_max) := ⟨3, l26_pool_idx2_lt hBm hB1 (by decide)⟩
  let j4 : Fin ((9 - B_max) + 2 ^ B_max) := ⟨4, l26_pool_idx2_lt hBm hB1 (by decide)⟩
  let wAnc6 := rPool j2
  let wTmp7 := rPool j3
  let wTmp8 := rPool j4
  let u8 := rIdx9 ⟨8, by decide⟩
  let u7 := rIdx9 ⟨7, by decide⟩
  let u6 := rIdx9 ⟨6, by decide⟩
  have hc2 : IsTreeCtrlAt wRootCtrl rPool 6 wAnc6 :=
    Or.inr ⟨j2, by dsimp [j2]; decide, rfl⟩
  have h32 : wTmp7 ≠ wAnc6 := rPool.wires.injective.ne (fun h ↦ by
    have hv := congrArg Fin.val h; dsimp [j2, j3] at hv; omega)
  have h43 : wTmp8 ≠ wTmp7 := rPool.wires.injective.ne (fun h ↦ by
    have hv := congrArg Fin.val h; dsimp [j3, j4] at hv; omega)
  have h42 : wTmp8 ≠ wAnc6 := rPool.wires.injective.ne (fun h ↦ by
    have hv := congrArg Fin.val h; dsimp [j2, j4] at hv; omega)
  let S_raw4 := SubtreeCleanPred P_ext wDum qEnc rPool 4
  let S_raw5 := SubtreeCleanPred P_ext wDum qEnc rPool 5
  let S_sub6 := SubtreeCleanPred P_ext wDum qEnc rPool 6
  let S_root := SubtreeCleanPred P_ext wDum qEnc rPool 7
  let P_root := p2t_ketPredProj S_root
  have hPh : P_rootᴴ = P_root := p2t_ketPredProj_conjTranspose S_root
  have hRaw5_iff4 : ∀ γ, (S_raw4 γ ∧ γ wTmp8 = 0) ↔ S_raw5 γ :=
    subtreeCleanPred_step P_ext wDum qEnc rPool 4 (by decide) j4 rfl
  have hSub6_iff5 : ∀ γ, (S_raw5 γ ∧ γ wTmp7 = 0) ↔ S_sub6 γ :=
    subtreeCleanPred_step P_ext wDum qEnc rPool 5 (by decide) j3 rfl
  have hRoot_iff5 : ∀ β, (S_raw5 β ∧ β wTmp7 = 0 ∧ β wAnc6 = 0) ↔ S_root β := fun β ↦ by
    rw [← and_assoc, hSub6_iff5]
    exact subtreeCleanPred_step P_ext wDum qEnc rPool 6 (by decide) j2 rfl β
  have hSub6_iff4 : ∀ γ, ((S_raw4 γ ∧ γ wTmp7 = 0) ∧ γ wTmp8 = 0) ↔ S_sub6 γ := fun γ ↦ by
    rw [and_right_comm, hRaw5_iff4, hSub6_iff5]
  have hRaw4_upd2 := subtreeCleanPred_upd_lt P_ext wDum qEnc rPool 4 j2 (by dsimp [j2]; decide)
    hExtPool hDumPool hEncPool
  have hRaw4_upd3 := subtreeCleanPred_upd_lt P_ext wDum qEnc rPool 4 j3 (by dsimp [j3]; decide)
    hExtPool hDumPool hEncPool
  have hRaw4_upd4 := subtreeCleanPred_upd_lt P_ext wDum qEnc rPool 4 j4 (by dsimp [j4]; decide)
    hExtPool hDumPool hEncPool
  have hRaw5_upd2 := subtreeCleanPred_upd_lt P_ext wDum qEnc rPool 5 j2 (by dsimp [j2]; decide)
    hExtPool hDumPool hEncPool
  have hRaw5_upd3 := subtreeCleanPred_upd_lt P_ext wDum qEnc rPool 5 j3 (by dsimp [j3]; decide)
    hExtPool hDumPool hEncPool
  have hSub6_4 := fun base ↦ by
    have h0 := wPrunedSubtreeDyn_realizes hBm9 v P_ext rIdx9 wRootCtrl wDum qEnc rPool
        hIdxPool hRootIdx hRootPool hRootDum hRootEnc hDumIdx hEncIdx hDumPool hEncPool
        hDumEnc hExtRoot hExtPool dLeaf leafPhase hPhaseRoot hPhasePool hLeafReal 6
        (by decide) base 64 wAnc6 hc2 (by decide) (by decide)
    exact p2t_RealizesConstCleanUnitary_mono_proj
      (p2t_ketPredProj_conjTranspose _) (p2t_ketPredProj_conjTranspose _)
      (p2t_ketPredProj_mul_imp fun γ hγ ↦ (hSub6_iff4 γ).mp hγ) h0
  let S_neg4 : BitAssignment n → Prop := fun γ ↦ S_raw4 γ ∧ γ wTmp8 = γ wRootCtrl * (1 + γ u8)
  let S_pos4 : BitAssignment n → Prop := fun γ ↦ S_raw4 γ ∧ γ wTmp8 = γ wRootCtrl * γ u8
  have hCond4_upd : ∀ (f : BitAssignment n → ZMod 2) (j : Fin ((9 - B_max) + 2 ^ B_max)),
      wTmp8 ≠ rPool j → (∀ γ val, S_raw4 (Function.update γ (rPool j) val) ↔ S_raw4 γ) →
      (∀ γ val, f (Function.update γ (rPool j) val) = f γ) →
      ∀ γ val, (S_raw4 (Function.update γ (rPool j) val) ∧
          Function.update γ (rPool j) val wTmp8 = f (Function.update γ (rPool j) val)) ↔
        (S_raw4 γ ∧ γ wTmp8 = f γ) := fun _ j h4j hR hf γ val ↦ by
    rw [hR, Function.update_of_ne h4j, hf]
  have hNeg4_upd3 : ∀ γ val, S_neg4 (Function.update γ wTmp7 val) ↔ S_neg4 γ :=
    hCond4_upd (fun γ ↦ γ wRootCtrl * (1 + γ u8)) j3 h43 hRaw4_upd3 fun γ val ↦ by
      rw [Function.update_of_ne (hRootPool j3), Function.update_of_ne (hIdxPool.ne ⟨8,
        by decide⟩ j3)]
  have hNeg4_upd2 : ∀ γ val, S_neg4 (Function.update γ wAnc6 val) ↔ S_neg4 γ :=
    hCond4_upd (fun γ ↦ γ wRootCtrl * (1 + γ u8)) j2 h42 hRaw4_upd2 fun γ val ↦ by
      rw [Function.update_of_ne (hRootPool j2), Function.update_of_ne (hIdxPool.ne ⟨8,
        by decide⟩ j2)]
  have hPos4_upd3 : ∀ γ val, S_pos4 (Function.update γ wTmp7 val) ↔ S_pos4 γ :=
    hCond4_upd (fun γ ↦ γ wRootCtrl * γ u8) j3 h43 hRaw4_upd3 fun γ val ↦ by
      rw [Function.update_of_ne (hRootPool j3), Function.update_of_ne (hIdxPool.ne ⟨8,
        by decide⟩ j3)]
  have hPos4_upd2 : ∀ γ val, S_pos4 (Function.update γ wAnc6 val) ↔ S_pos4 γ :=
    hCond4_upd (fun γ ↦ γ wRootCtrl * γ u8) j2 h42 hRaw4_upd2 fun γ val ↦ by
      rw [Function.update_of_ne (hRootPool j2), Function.update_of_ne (hIdxPool.ne ⟨8,
        by decide⟩ j2)]
  have hdNeg := fun base ↦
    l26_uncomputeSandwichNegDyn_realizes v wRootCtrl u8 wTmp8
      (hRootIdx ⟨8, by decide⟩) (hRootPool j4) (hIdxPool.ne ⟨8, by decide⟩ j4)
      (W := fun w ↦ w = wTmp8) rfl
      (S_pre := fun γ ↦ S_neg4 γ ∧ γ wTmp7 = 0)
      (l26DiagUnitary_diagIndepOf fun β w val hw ↦ by
        subst hw
        rw [Function.update_of_ne h42.symm,
            idxValPrefix_upd_ne9 rIdx9 β wTmp8 val (fun d ↦ hIdxPool.ne d j4), hPhasePool])
      (fun _ h ↦ h.1.2) (fun _ h ↦ h.2)
      (fun β h ↦ ⟨⟨(hRaw4_upd4 β 0).mpr h.1.1, by rw [Function.update_of_ne h43.symm]; exact h.2⟩,
        Function.update_self _ _ _⟩)
      (hSub6_4 base)
  have hdPos := fun base ↦
    l26_uncomputeSandwichPosDyn_realizes v wRootCtrl u8 wTmp8
      (hRootIdx ⟨8, by decide⟩) (hRootPool j4) (hIdxPool.ne ⟨8, by decide⟩ j4)
      (W := fun w ↦ w = wTmp8) rfl
      (S_pre := fun γ ↦ S_pos4 γ ∧ γ wTmp7 = 0)
      (l26DiagUnitary_diagIndepOf fun β w val hw ↦ by
        subst hw
        rw [Function.update_of_ne h42.symm,
            idxValPrefix_upd_ne9 rIdx9 β wTmp8 val (fun d ↦ hIdxPool.ne d j4), hPhasePool])
      (fun _ h ↦ h.1.2) (fun _ h ↦ h.2)
      (fun β h ↦ ⟨⟨(hRaw4_upd4 β 0).mpr h.1.1, by rw [Function.update_of_ne h43.symm]; exact h.2⟩,
        Function.update_self _ _ _⟩)
      (hSub6_4 base)
  have hLP := leafPhase_pruned_upd_pool rIdx9 rPool hIdxPool leafPhase hPhasePool
  have hdL256_0_raw := l26_pebbledSplit2Dyn_realizes v wTmp8 u7 u6 wTmp7 wAnc6
    (hIdxPool.ne ⟨7, by decide⟩ j4).symm h43 (hIdxPool.ne ⟨7, by decide⟩ j3)
    (hIdxPool.ne ⟨6, by decide⟩ j3).symm h32 (hIdxPool.ne ⟨6, by decide⟩ j2)
    h42 (hIdxPool.ne ⟨7, by decide⟩ j2)
    S_neg4 hNeg4_upd3 hNeg4_upd2
    _ _ _ _
    (fun γ ↦ leafPhase (0 + prunedEffIdx 6 64 (idxValPrefix rIdx9.wires γ 6 (by decide))) γ)
    (fun γ ↦ leafPhase (64 + prunedEffIdx 6 64 (idxValPrefix rIdx9.wires γ 6 (by decide))) γ)
    (fun γ ↦ leafPhase (128 + prunedEffIdx 6 64 (idxValPrefix rIdx9.wires γ 6 (by decide))) γ)
    (fun γ ↦ leafPhase (192 + prunedEffIdx 6 64 (idxValPrefix rIdx9.wires γ 6 (by decide))) γ)
    (hLP 6 (by decide) 0 64 j3) (hLP 6 (by decide) 64 64 j3)
    (hLP 6 (by decide) 128 64 j3) (hLP 6 (by decide) 192 64 j3)
    (hLP 6 (by decide) 0 64 j2) (hLP 6 (by decide) 64 64 j2)
    (hLP 6 (by decide) 128 64 j2) (hLP 6 (by decide) 192 64 j2)
    (hdNeg 0) (hdNeg 64) (hdNeg 128) (hdNeg 192)
  have hdL256_1_raw := l26_pebbledSplit2Dyn_realizes v wTmp8 u7 u6 wTmp7 wAnc6
    (hIdxPool.ne ⟨7, by decide⟩ j4).symm h43 (hIdxPool.ne ⟨7, by decide⟩ j3)
    (hIdxPool.ne ⟨6, by decide⟩ j3).symm h32 (hIdxPool.ne ⟨6, by decide⟩ j2)
    h42 (hIdxPool.ne ⟨7, by decide⟩ j2)
    S_pos4 hPos4_upd3 hPos4_upd2
    _ _ _ _
    (fun γ ↦ leafPhase (256 + prunedEffIdx 6 64 (idxValPrefix rIdx9.wires γ 6 (by decide))) γ)
    (fun γ ↦ leafPhase (320 + prunedEffIdx 6 64 (idxValPrefix rIdx9.wires γ 6 (by decide))) γ)
    (fun γ ↦ leafPhase (384 + prunedEffIdx 6 64 (idxValPrefix rIdx9.wires γ 6 (by decide))) γ)
    (fun γ ↦ leafPhase (448 + prunedEffIdx 6 64 (idxValPrefix rIdx9.wires γ 6 (by decide))) γ)
    (hLP 6 (by decide) 256 64 j3) (hLP 6 (by decide) 320 64 j3)
    (hLP 6 (by decide) 384 64 j3) (hLP 6 (by decide) 448 64 j3)
    (hLP 6 (by decide) 256 64 j2) (hLP 6 (by decide) 320 64 j2)
    (hLP 6 (by decide) 384 64 j2) (hLP 6 (by decide) 448 64 j2)
    (hdPos 256) (hdPos 320) (hdPos 384) (hdPos 448)
  let S_sub4_76 : BitAssignment n → Prop := fun γ ↦ S_raw4 γ ∧ γ wTmp7 = 0 ∧ γ wAnc6 = 0
  have hdL256_0_m := p2t_RealizesConstCleanUnitary_mono_proj (p2t_ketPredProj_conjTranspose _)
      (p2t_ketPredProj_conjTranspose (fun γ ↦ S_sub4_76 γ ∧ γ wTmp8 = γ wRootCtrl * (1 + γ
      u8))) (p2t_ketPredProj_mul_imp fun _ h ↦ ⟨⟨h.1.1, h.2⟩, h.1.2⟩) hdL256_0_raw
  have hdL256_0 := p2t_RealizesConstCleanUnitary_congr_unitary
    (U₂ := l26DiagUnitary (fun γ ↦
      γ wTmp8 * leafPhase (0 + prunedEffIdx 8 256 (idxValPrefix rIdx9.wires γ 8 (by decide))) γ))
    (p2t_ketPredProj_conjTranspose _) hdL256_0_m (by
      rw [l26DiagUnitary_congr (fun γ ↦ ?_)]
      congr 1
      exact l26_split2_index_eq rIdx9 γ 6 (by decide) 0 256 (by decide) (fun q ↦ leafPhase q γ))
  have hdL256_1_m := p2t_RealizesConstCleanUnitary_mono_proj (p2t_ketPredProj_conjTranspose _)
      (p2t_ketPredProj_conjTranspose (fun γ ↦ S_sub4_76 γ ∧ γ wTmp8 = γ wRootCtrl * γ u8))
      (p2t_ketPredProj_mul_imp fun _ h ↦ ⟨⟨h.1.1, h.2⟩, h.1.2⟩) hdL256_1_raw
  have hdL256_1 := p2t_RealizesConstCleanUnitary_congr_unitary
    (U₂ := l26DiagUnitary (fun γ ↦
      γ wTmp8 * leafPhase (256 + prunedEffIdx 8 256 (idxValPrefix rIdx9.wires γ 8 (by decide))) γ))
    (p2t_ketPredProj_conjTranspose _) hdL256_1_m (by
      rw [l26DiagUnitary_congr (fun γ ↦ ?_)]
      congr 1
      exact l26_split2_index_eq rIdx9 γ 6 (by decide) 256 256 (by decide) (fun q ↦ leafPhase q γ))
  have hdL0 := l26_branchSplitDyn_realizes_exact v wRootCtrl u8 wTmp8
    (hRootIdx ⟨8, by decide⟩) (hRootPool j4) (hIdxPool.ne ⟨8, by decide⟩ j4)
    S_root S_sub4_76
    (fun β hβ ↦ ((hRaw5_iff4 β).mpr ((hRoot_iff5 β).mpr hβ).1).2)
    (fun β val hβ ↦ by
      obtain ⟨h5, h30, h20⟩ := (hRoot_iff5 β).mpr hβ
      obtain ⟨h4, _⟩ := (hRaw5_iff4 β).mpr h5
      refine ⟨(hRaw4_upd4 β val).mpr h4, ?_, ?_⟩
      · rw [Function.update_of_ne h43.symm]; exact h30
      · rw [Function.update_of_ne h42.symm]; exact h20)
    (fun γ val ↦ by
      dsimp only [S_sub4_76]
      refine and_congr (hRaw4_upd4 γ val) (and_congr ?_ ?_)
      · rw [Function.update_of_ne h43.symm]
      · rw [Function.update_of_ne h42.symm])
    _ _
    (fun γ ↦ leafPhase (0 + prunedEffIdx 8 256 (idxValPrefix rIdx9.wires γ 8 (by decide))) γ)
    (fun γ ↦ leafPhase (256 + prunedEffIdx 8 256 (idxValPrefix rIdx9.wires γ 8 (by decide))) γ)
    (hLP 8 (by decide) 0 256 j4) (hLP 8 (by decide) 256 256 j4)
    hdL256_0 hdL256_1
  have hdL := p2t_RealizesConstCleanUnitary_congr_unitary
    (U₂ := l26DiagUnitary (fun γ ↦
      γ wRootCtrl * leafPhase (0 + prunedEffIdx 9 512 (idxValPrefix rIdx9.wires γ 9 le_rfl)) γ))
    hPh hdL0 (by
      rw [l26DiagUnitary_congr (fun γ ↦ ?_)]
      congr 1
      exact l26_split1_index_eq rIdx9 γ 8 le_rfl 0 512 (by decide) (fun q ↦ leafPhase q γ))
  have hSub6_5 := fun base Q hQ1 hQk ↦ by
    have h0 := wPrunedSubtreeDyn_realizes hBm9 v P_ext rIdx9 wRootCtrl wDum qEnc rPool
        hIdxPool hRootIdx hRootPool hRootDum hRootEnc hDumIdx hEncIdx hDumPool hEncPool
        hDumEnc hExtRoot hExtPool dLeaf leafPhase hPhaseRoot hPhasePool hLeafReal 6
        (by decide) base Q wAnc6 hc2 hQ1 hQk
    exact p2t_RealizesConstCleanUnitary_mono_proj
      (p2t_ketPredProj_conjTranspose _) (p2t_ketPredProj_conjTranspose _)
      (p2t_ketPredProj_mul_imp fun γ hγ ↦ (hSub6_iff5 γ).mp hγ) h0
  have hdR0 := l26_pebbledSplit2Dyn_realizes v wRootCtrl u7 u6 wTmp7 wAnc6
    (hRootIdx ⟨7, by decide⟩) (hRootPool j3) (hIdxPool.ne ⟨7, by decide⟩ j3)
    (hIdxPool.ne ⟨6, by decide⟩ j3).symm h32 (hIdxPool.ne ⟨6, by decide⟩ j2)
    (hRootPool j2) (hIdxPool.ne ⟨7, by decide⟩ j2)
    S_raw5 hRaw5_upd3 hRaw5_upd2
    _ _ _ _
    (fun γ ↦ leafPhase (512 + prunedEffIdx 6 64 (idxValPrefix rIdx9.wires γ 6 (by decide))) γ)
    (fun γ ↦ leafPhase (576 + prunedEffIdx 6 64 (idxValPrefix rIdx9.wires γ 6 (by decide))) γ)
    (fun γ ↦ leafPhase (640 + prunedEffIdx 6 64 (idxValPrefix rIdx9.wires γ 6 (by decide))) γ)
    (fun γ ↦ leafPhase (704 + prunedEffIdx 6 45 (idxValPrefix rIdx9.wires γ 6 (by decide))) γ)
    (hLP 6 (by decide) 512 64 j3) (hLP 6 (by decide) 576 64 j3)
    (hLP 6 (by decide) 640 64 j3) (hLP 6 (by decide) 704 45 j3)
    (hLP 6 (by decide) 512 64 j2) (hLP 6 (by decide) 576 64 j2)
    (hLP 6 (by decide) 640 64 j2) (hLP 6 (by decide) 704 45 j2)
    (hSub6_5 512 64 (by decide) (by decide))
    (hSub6_5 576 64 (by decide) (by decide))
    (hSub6_5 640 64 (by decide) (by decide))
    (hSub6_5 704 45 (by decide) (by decide))
  have hdR1 := p2t_RealizesConstCleanUnitary_mono_proj (p2t_ketPredProj_conjTranspose _) hPh
      (p2t_ketPredProj_mul_imp fun β hβ ↦ (hRoot_iff5 β).mpr hβ) hdR0
  have hdR := p2t_RealizesConstCleanUnitary_congr_unitary
    (U₂ := l26DiagUnitary (fun γ ↦
      γ wRootCtrl * leafPhase (512 + prunedEffIdx 9 237 (idxValPrefix rIdx9.wires γ 9 le_rfl)) γ))
    hPh hdR1 (by
      rw [l26DiagUnitary_congr (fun β ↦ ?_)]
      have hsp := l26_split2_index_eq rIdx9 β 6 (by decide) 512 237 (by decide) (fun q ↦ leafPhase q
        β)
      dsimp only at hsp
      rw [prunedEffIdx_9_237_eq_8 rIdx9 β]
      congr 1)
  exact wRoot749_xSandwich_realizes P_ext rIdx9 wRootCtrl wDum qEnc rPool 7
    hRootIdx hRootPool hRootDum hRootEnc hExtRoot leafPhase hPhaseRoot hdL hdR
/-! ## Part 2: Pebbled Stage-7 Unbuffered Fixup (`1,672 T` at `133w`, `1,688 T` at `132w`, `1,752 T`
at `131w`, `1,782 T` at `126w`) -/
end Leaf2MidK6Fix6At131Opt
end
end
end Leaf2MidK6Fix6At131Opt

noncomputable section CachedSwap0Split133

section
namespace AnchorSwap0Split133
section ConfigCached115
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 65536
set_option exponentiation.threshold 5000
local instance (priority := 1000000) instNeZeroTwoPowCached115 (k : ℕ) : NeZero (2 ^ k) :=
  ⟨Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos k)⟩
open Operator QProg Matrix HermitianMat
open _root_.DynamicCircuit
open DynCircuitExt hiding czCircuit
open scoped Matrix ComplexOrder MatrixOrder BigOperators Circuit.Notation
open OctahedralOrbit hiding ket eval_seq_mulVec ket_X ket_CNOT ket_TOFF matrix_ext_ket
  ket_projector_zero
open Dyadic128CoulombMath
open CanonRank7Circuit hiding count_copyXorRegCircuit_toff
open MeasureBranchHadamardSem (ket matrix_ext_ket)
open BchCubeDecoder
open PosSlots24PartnerMux288 hiding ite_pos ite_neg
open PosSlots24PartnerMuxZeroT123 hiding ite_pos ite_neg dite_pos dite_neg
open PosSlots24Barrel3Pass
attribute [local irreducible]
  DynCircuitExt.measureXResetAndBranch cXorE0217Locked
theorem single_eq_ket_basisBits {n : ℕ} (g : Fin (2 ^ n)) :
    (Pi.single g (1 : ℂ) : Fin (2 ^ n) → ℂ) = ket (basisBits n g) := by
  rw [p2d_ket_eq_single (basisBits n g)]
  exact congrArg (fun idx ↦ (Pi.single idx (1 : ℂ) : Fin (2 ^ n) → ℂ))
    ((basisBitsEquiv n).symm_apply_apply g).symm
theorem comm_embedUnitary_of_update_outside {n kData : ℕ} (rData : QRegister kData n)
    (V : Unitary (2 ^ kData)) (C : Circuit n) (w : Wire n) (hw : w ∉ Set.range rData.wires)
    (ctrl : BitAssignment n → ZMod 2) (hKet : ∀ β : BitAssignment n, C.eval.1.mulVec (ket β) =
    ket (Function.update β w (β w + ctrl β))) (hCtrl : ∀ (g : Fin (2 ^ n)) (y : Fin (2 ^
    kData)), V.1 y (rData.extractIndex g) ≠ 0 → ctrl (basisBits n (rData.replaceIndex g y)) =
    ctrl (basisBits n g)) : C.eval * rData.embedUnitary V = rData.embedUnitary V * C.eval
    := by
  apply Subtype.ext; apply matrix_ext_ket; intro β
  simp only [Submonoid.coe_mul, ← Matrix.mulVec_mulVec]
  let g := (basisBitsEquiv n).symm β
  have hgβ : basisBits n g = β := (basisBitsEquiv n).apply_symm_apply β
  let b := β w + ctrl β
  let β' := Function.update β w b
  let g' := (basisBitsEquiv n).symm β'
  have hg'β' : basisBits n g' = β' := (basisBitsEquiv n).apply_symm_apply β'
  have hExEq : rData.extractIndex g' = rData.extractIndex g := by
    apply (basisBitsEquiv kData).injective
    funext i
    change basisBits kData (rData.extractIndex g') i = basisBits kData (rData.extractIndex g) i
    rw [QRegister.basisBits_extractIndex, QRegister.basisBits_extractIndex, hg'β', hgβ]
    dsimp only [β']
    exact Function.update_of_ne (fun h ↦ hw ⟨i, h⟩) _ _
  rw [hKet β]
  conv_rhs =>
    rw [p2d_ket_eq_single β', QRegister.embedUnitary_val,
        embedMatrix_mulVec_single_sum rData V.1 g', hExEq]
  conv_lhs =>
    rw [p2d_ket_eq_single β, QRegister.embedUnitary_val,
        embedMatrix_mulVec_single_sum rData V.1 g, Matrix.mulVec_sum]
  refine Finset.sum_congr rfl fun y _ ↦ ?_
  by_cases hnz : V.1 y (rData.extractIndex g) = 0
  · simp [hnz]
  · rw [Matrix.mulVec_smul]
    refine congrArg (V.1 y (rData.extractIndex g) • ·) ?_
    let gy := rData.replaceIndex g y
    rw [single_eq_ket_basisBits gy, hKet (basisBits n gy), p2d_ket_eq_single]
    refine congrArg (fun idx ↦ (Pi.single idx (1 : ℂ) : Fin (2 ^ n) → ℂ)) ?_
    apply eq_of_basisBits_eq; intro q
    rw [basisBits_symm_apply_at]
    by_cases hqw : q = w
    · subst hqw
      rw[Function.update_self, rData.basisBits_replaceIndex_of_not_mem g' y q hw,
          rData.basisBits_replaceIndex_of_not_mem g y q hw, hCtrl g y hnz, hg'β']
      dsimp only [β', b]
      rw [Function.update_self, hgβ]
    · rw [Function.update_of_ne hqw]
      by_cases hqD : q ∈ Set.range rData.wires
      · obtain ⟨i, rfl⟩ := hqD
        rw [QRegister.basisBits_replaceIndex_apply, QRegister.basisBits_replaceIndex_apply]
      · rw[rData.basisBits_replaceIndex_of_not_mem g y q hqD,
          rData.basisBits_replaceIndex_of_not_mem g' y q hqD, hg'β']
        dsimp only [β']
        rw [Function.update_of_ne hqw, hgβ]
theorem singleton_proj_zero_mulVec_of_preserves {n : ℕ} (w : Wire n) (U₀ : Unitary (2 ^ n))
    (hPres : ∀ g' g : Fin (2 ^ n), U₀.1 g' g ≠ 0 → basisBits n g' w = basisBits n g w)
    (α : BitAssignment n) (hα0 : α w = 0) :
    ((QRegister.singleton w).basisOutcomeProjector 0).mulVec (U₀.1.mulVec (ket α)) =
    U₀.1.mulVec (ket α) := by
  let g := (basisBitsEquiv n).symm α
  have hgα : basisBits n g = α := (basisBitsEquiv n).apply_symm_apply α
  have hgw0 : basisBits n g w = 0 := by rw [hgα]; exact hα0
  rw [p2d_ket_eq_single α]
  funext i
  rw [QRegister.basisOutcomeProjector_eq_diagonal, Matrix.mulVec_diagonal,
      Matrix.mulVec_single_one]
  change (if (QRegister.singleton w).extractIndex i = 0 then (1 : ℂ) else 0) * U₀.1 i g = U₀.1 i g
  by_cases hnz : U₀.1 i g = 0
  · simp [hnz]
  · have hi0 : (QRegister.singleton w).extractIndex i = 0 := by
      apply (QRegExt.extractIndex_eq_zero_iff (QRegister.singleton w) i).mpr
      intro _
      change basisBits n i w = 0
      rw [hPres i g hnz]
      exact hgw0
    simp [hi0]
end ConfigCached115
end AnchorSwap0Split133
end
end CachedSwap0Split133

end QuantumComputation.Specs.StoppingPowerSolution
end
