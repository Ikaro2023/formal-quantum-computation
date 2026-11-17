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

public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.ChiralMod4TopCap
public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.SpectatorSum217
set_option Elab.async false
set_option compiler.extract_closed false

@[expose] public section
set_option allowUnsafeReducibility true

namespace QuantumComputation.Specs.StoppingPowerSolution

noncomputable section MidK6UnbufOptAndPackedSand
set_option maxRecDepth 4096

section
namespace MidK6UnbufOpt
open Operator QProg Matrix _root_.DynamicCircuit DynCircuitExt HermitianMat
open scoped Matrix ComplexOrder MatrixOrder BigOperators Circuit.Notation
open OctahedralOrbit
open Dyadic128OrbitTableCert
open MeasureBranchHadamardSem (projZeroAll ket_projZeroAll projZeroAll_conjTranspose
  RealizesCleanUnitary)
open StreamingBchComparator
open PosSlots24BranchConcrete
open PosSlots24SemanticBridge
open PosSlots24SpectatorPrunedPhase
open PrunedQromLookup MidKickSub33
set_option backward.isDefEq.respectTransparency true
set_option exponentiation.threshold 256
set_option maxRecDepth 4096
local instance (priority := 1000000) instNeZeroTwoPowK18 (k : ℕ) :
    NeZero (2 ^ k) := ⟨(Nat.two_pow_pos k).ne'⟩
/-!
## Section 1: Nested `TempCtx` Clean-Unitary Combinator (`mk34_ctxToDynNested`)
-/
/-- Compiles a `TempCtx M` around a dynamic leaf circuit `dLeaf : DynamicCircuit Var n`
using `0`-`.TOFF` measurement-based uncomputation (`DynamicCircuit.andCompute` / `andUncompute`). -/
def mk34_ctxToDynNested {Var : Type} {M n : ℕ} (v : Var) (rComb : QRegister M n)
    (dLeaf : DynamicCircuit Var n) : TempCtx M → DynamicCircuit Var n
  | .hole => dLeaf
  | .seqPre c K =>
      .seq (.circuit (c.onRegister rComb).toCircuit) (mk34_ctxToDynNested v rComb dLeaf K)
  | .seqPost K c =>
      .seq (mk34_ctxToDynNested v rComb dLeaf K) (.circuit (c.onRegister rComb).toCircuit)
  | .tempAnd c₁ c₂ anc h₁₂ h₁a h₂a K =>
      .seq
        (DynamicCircuit.andCompute (rComb c₁) (rComb c₂) (rComb anc)
          (rComb.wires.injective.ne h₁a) (rComb.wires.injective.ne h₂a))
        (.seq (mk34_ctxToDynNested v rComb dLeaf K)
          (DynamicCircuit.andUncompute v (rComb c₁) (rComb c₂) (rComb anc)
            (rComb.wires.injective.ne h₁₂)))
@[scoped simp] theorem mk34_ctxToDynNested_count_toff {Var : Type} {M n : ℕ} (v : Var)
    (rComb : QRegister M n) (dLeaf : DynamicCircuit Var n) :
    ∀ K : TempCtx M,
      (mk34_ctxToDynNested v rComb dLeaf K).count PrimitiveGate.TOFF =
        dLeaf.count PrimitiveGate.TOFF
  | .hole => rfl
  | .seqPre _ K => by simp [mk34_ctxToDynNested, mk34_ctxToDynNested_count_toff v rComb dLeaf K]
  | .seqPost K _ => by simp [mk34_ctxToDynNested, mk34_ctxToDynNested_count_toff v rComb dLeaf K]
  | .tempAnd _ _ _ _ _ _ K => by
      simp [mk34_ctxToDynNested, DynamicCircuit.count_andCompute_toff,
        DynamicCircuit.count_andUncompute_toff, mk34_ctxToDynNested_count_toff v rComb dLeaf K]
@[scoped simp] theorem mk34_ctxToDynNested_count_t {Var : Type} {M n : ℕ} (v : Var)
    (rComb : QRegister M n) (dLeaf : DynamicCircuit Var n) :
    ∀ K : TempCtx M,
      (mk34_ctxToDynNested v rComb dLeaf K).count PrimitiveGate.T =
        4 * K.countTempAnd + dLeaf.count PrimitiveGate.T
  | .hole => by simp [mk34_ctxToDynNested, TempCtx.countTempAnd]
  | .seqPre _ K => by
      simp [mk34_ctxToDynNested, TempCtx.countTempAnd, mk34_ctxToDynNested_count_t v rComb dLeaf K]
  | .seqPost K _ => by
      simp [mk34_ctxToDynNested, TempCtx.countTempAnd, mk34_ctxToDynNested_count_t v rComb dLeaf K]
  | .tempAnd _ _ _ _ _ _ K => by
      simp only [mk34_ctxToDynNested, DynamicCircuit.count, DynamicCircuit.count_andCompute_t,
        DynamicCircuit.count_andUncompute_t, TempCtx.countTempAnd,
        mk34_ctxToDynNested_count_t v rComb dLeaf K]
      ring
theorem mk34_ctxToDynNested_preservesStoreConst {Var : Type} [Fintype Var] [DecidableEq Var]
    {M n : ℕ} (v : Var) (rComb : QRegister M n) (dLeaf : DynamicCircuit Var n)
    (hLeaf : PreservesStoreConst dLeaf) :
    ∀ K : TempCtx M, PreservesStoreConst (mk34_ctxToDynNested v rComb dLeaf K)
  | .hole => hLeaf
  | .seqPre _ K =>
      PreservesStoreConst.seq (PreservesStoreConst.circuit _)
        (mk34_ctxToDynNested_preservesStoreConst v rComb dLeaf hLeaf K)
  | .seqPost K _ =>
      PreservesStoreConst.seq (mk34_ctxToDynNested_preservesStoreConst v rComb dLeaf hLeaf K)
        (PreservesStoreConst.circuit _)
  | .tempAnd c₁ c₂ anc h₁₂ _ _ K =>
      PreservesStoreConst.seq (PreservesStoreConst.circuit _)
        (PreservesStoreConst.seq (mk34_ctxToDynNested_preservesStoreConst v rComb dLeaf hLeaf K)
          (PreservesStoreConst.andUncompute v (rComb c₁) (rComb c₂) (rComb anc)
            (rComb.wires.injective.ne h₁₂)))
theorem mk34_writeRegProg_leafScr_eq {M L n : ℕ} (rComb : QRegister M n)
    (rLeafScr : QRegister L n) (hDisj : rComb.DisjointWires rLeafScr) (β : BitAssignment n)
    (γ : BitAssignment M) (j : Fin L) : writeRegProg β rComb γ (rLeafScr j) = β (rLeafScr j)
    := writeRegProg_apply_of_not_mem β rComb γ (rLeafScr j) fun ⟨i, hi⟩ ↦ hDisj.ne i j hi
theorem mk34_ctxToToff_eval_ket_of_leafScr {M L n : ℕ}
    (rComb : QRegister M n) (rLeafScr : QRegister L n)
    (hDisj : rComb.DisjointWires rLeafScr)
    (cLeaf : Circuit n) (fLeaf : BitAssignment M → BitAssignment n → ZMod 2)
    (hfLeaf : ∀ (γ γ' : BitAssignment M) (β : BitAssignment n),
      fLeaf γ (writeRegProg β rComb γ') = fLeaf γ β)
    (hLeaf : ∀ β : BitAssignment n,
      (∀ j : Fin L, β (rLeafScr j) = 0) →
      cLeaf.eval.1.mulVec (MeasureBranchHadamardSem.ket β) =
        ((-1 : ℂ) ^ (fLeaf (fun idx ↦ β (rComb idx)) β).val) •
          MeasureBranchHadamardSem.ket β)
    (q₀ : Wire M) :
    ∀ (K : TempCtx M) (β : BitAssignment n),
      (∀ j : Fin L, β (rLeafScr j) = 0) →
      let γ : BitAssignment M := fun idx ↦ β (rComb idx)
      (mk34_ctxToToff rComb cLeaf K).eval.1.mulVec (MeasureBranchHadamardSem.ket β) =
        ((-1 : ℂ) ^ (fLeaf (K.fwdBits γ) β).val) •
          MeasureBranchHadamardSem.ket (writeRegProg β rComb ((K.plug (.z q₀)).evalBits γ))
  | .hole, β, hL0 => by
      dsimp only [mk34_ctxToToff, TempCtx.fwdBits, TempCtx.plug, TempPhaseProg.evalBits]
      rw [hLeaf β hL0, mk34_writeRegProg_self]
  | .seqPre c K₁, β, hL0 => by
      dsimp only [mk34_ctxToToff, TempCtx.fwdBits, TempCtx.plug, TempPhaseProg.evalBits]
      rw [MeasureBranchHadamardSem.eval_seq_mulVec, mk34_cliff_onRegister_eval_ket]
      let β₁ := writeRegProg β rComb (c.eval (fun idx ↦ β (rComb idx)))
      have hL1 : ∀ j : Fin L, β₁ (rLeafScr j) = 0 := fun j ↦
        (mk34_writeRegProg_leafScr_eq rComb rLeafScr hDisj β _ j).trans (hL0 j)
      have hγ₁ : (fun idx ↦ β₁ (rComb idx)) = c.eval (fun idx ↦ β (rComb idx)) :=
        funext fun idx ↦ writeRegProg_apply_reg β rComb _ idx
      rw [mk34_ctxToToff_eval_ket_of_leafScr rComb rLeafScr hDisj cLeaf fLeaf hfLeaf hLeaf q₀ K₁ β₁
        hL1,
          hγ₁, hfLeaf _ _ β, mk34_writeRegProg_idem]
  | .seqPost K₁ c, β, hL0 => by
      dsimp only [mk34_ctxToToff, TempCtx.fwdBits, TempCtx.plug, TempPhaseProg.evalBits]
      rw [MeasureBranchHadamardSem.eval_seq_mulVec,
          mk34_ctxToToff_eval_ket_of_leafScr rComb rLeafScr hDisj cLeaf fLeaf hfLeaf hLeaf q₀ K₁ β
            hL0,
          Matrix.mulVec_smul, mk34_cliff_onRegister_eval_ket]
      have hγ₁ : (fun idx ↦ writeRegProg β rComb ((K₁.plug (.z q₀)).evalBits (fun idx ↦ β
          (rComb idx))) (rComb idx)) = (K₁.plug (.z q₀)).evalBits (fun idx ↦ β (rComb idx)) :=
          funext fun idx ↦ writeRegProg_apply_reg β rComb _ idx
      rw [hγ₁, mk34_writeRegProg_idem]
  | .tempAnd c₁ c₂ anc h₁₂ h₁a h₂a K₁, β, hL0 => by
      dsimp only [mk34_ctxToToff, TempCtx.fwdBits, TempCtx.plug, TempPhaseProg.evalBits]
      let γ : BitAssignment M := fun idx ↦ β (rComb idx)
      let γ₁ : BitAssignment M := Function.update γ anc (γ anc + γ c₁ * γ c₂)
      rw [MeasureBranchHadamardSem.eval_seq_mulVec, MeasureBranchHadamardSem.eval_seq_mulVec,
          MeasureBranchHadamardSem.ket_TOFF]
      have hβ₁ : Function.update β (rComb anc) (β (rComb anc) + β (rComb c₁) * β (rComb c₂)) =
          writeRegProg β rComb γ₁ := by
        have h := mk34_writeRegProg_update β rComb γ anc (γ anc + γ c₁ * γ c₂)
        rw [mk34_writeRegProg_self] at h
        exact h
      have hL1 : ∀ j : Fin L, writeRegProg β rComb γ₁ (rLeafScr j) = 0 := fun j ↦
        (mk34_writeRegProg_leafScr_eq rComb rLeafScr hDisj β γ₁ j).trans (hL0 j)
      rw [hβ₁, mk34_ctxToToff_eval_ket_of_leafScr rComb rLeafScr hDisj cLeaf fLeaf hfLeaf hLeaf q₀
            K₁ (writeRegProg β rComb γ₁) hL1]
      have hγ₁_read : (fun idx ↦ writeRegProg β rComb γ₁ (rComb idx)) = γ₁ :=
        funext fun idx ↦ writeRegProg_apply_reg β rComb γ₁ idx
      rw [hγ₁_read, hfLeaf _ _ β, mk34_writeRegProg_idem, Matrix.mulVec_smul,
          MeasureBranchHadamardSem.ket_TOFF]
      let γ₂ := (K₁.plug (.z q₀)).evalBits γ₁
      have hUpd₂ : Function.update (writeRegProg β rComb γ₂) (rComb anc) (writeRegProg β rComb
          γ₂ (rComb anc) + writeRegProg β rComb γ₂ (rComb c₁) * writeRegProg β rComb γ₂ (rComb
          c₂)) = writeRegProg β rComb (Function.update γ₂ anc (γ₂ anc + γ₂ c₁ * γ₂ c₂)) := by
        rw [writeRegProg_apply_reg, writeRegProg_apply_reg, writeRegProg_apply_reg]
        exact mk34_writeRegProg_update β rComb γ₂ anc (γ₂ anc + γ₂ c₁ * γ₂ c₂)
      rw [hUpd₂]
theorem mk34_tailScr_concat_zero {M L n : ℕ} (rComb : QRegister M n)
    (rLeafScr : QRegister L n) (hDisj : rComb.DisjointWires rLeafScr) : projZeroAll (0 + L)
    (tailScr (rComb.concat rLeafScr hDisj) (0 + L) (by omega)) = projZeroAll L rLeafScr.wires
    := by
  apply MeasureBranchHadamardSem.matrix_ext_ket
  intro β
  rw [ket_projZeroAll, ket_projZeroAll]
  have hiff : (∀ j : Fin (0 + L), β (tailScr (rComb.concat rLeafScr hDisj) (0 + L) (by omega)
      j) = 0) ↔ (∀ i : Fin L, β (rLeafScr i) = 0) := by
    constructor
    · intro h i
      have hi := h ⟨i.val, by omega⟩
      dsimp only [tailScr] at hi
      have hidx : (⟨M + L - (0 + L) + i.val, by omega⟩ : Fin (M + L)) = Fin.natAdd M i := by
        ext; dsimp; omega
      rw [hidx, QRegister.concat_apply_right] at hi
      exact hi
    · intro h j
      dsimp only [tailScr]
      have hidx : (⟨M + L - (0 + L) + j.val, by omega⟩ : Fin (M + L)) =
          Fin.natAdd M ⟨j.val, by omega⟩ := by
        ext; dsimp; omega
      rw [hidx, QRegister.concat_apply_right]
      exact h ⟨j.val, by omega⟩
  by_cases h : ∀ i : Fin L, β (rLeafScr i) = 0
  · rw [ite_eq_left (hiff.mpr h), ite_eq_left h]
  · rw [ite_eq_right (fun hc ↦ h (hiff.mp hc)), ite_eq_right h]
theorem mk34_tailScr_concat_split {M L n : ℕ} (rComb : QRegister M n)
    (rLeafScr : QRegister L n) (hDisj : rComb.DisjointWires rLeafScr) (rem : ℕ)
    (hrem : rem ≤ M) (β : BitAssignment n) : (∀ j : Fin (rem + L), β (tailScr (rComb.concat
    rLeafScr hDisj) (rem + L) (by omega) j) = 0) ↔ (cleanRem M rem (fun idx ↦ β (rComb idx)) ∧
    ∀ j : Fin L, β (rLeafScr j) = 0) := by
  let rFull := rComb.concat rLeafScr hDisj
  constructor
  · intro hz
    refine ⟨fun w hw ↦ ?_, fun j ↦ ?_⟩
    · let k : Fin (rem + L) := ⟨w.val - (M - rem), by omega⟩
      have hk := hz k
      dsimp only [tailScr, rFull, k] at hk
      have hidx : (⟨M + L - (rem + L) + (w.val - (M - rem)), by omega⟩ : Fin (M + L)) =
          Fin.castAdd L w := by
        ext; dsimp; omega
      rw [hidx, QRegister.concat_apply_left] at hk
      exact hk
    · let k : Fin (rem + L) := ⟨rem + j.val, by omega⟩
      have hk := hz k
      dsimp only [tailScr, rFull, k] at hk
      have hidx : (⟨M + L - (rem + L) + (rem + j.val), by omega⟩ : Fin (M + L)) =
          Fin.natAdd M j := by
        ext; dsimp; omega
      rw [hidx, QRegister.concat_apply_right] at hk
      exact hk
  · rintro ⟨hcr, hL0⟩ j
    dsimp only [tailScr, rFull]
    by_cases hj : j.val < rem
    · let w : Wire M := ⟨(M - rem) + j.val, by omega⟩
      have hidx : (⟨M + L - (rem + L) + j.val, by omega⟩ : Fin (M + L)) =
          Fin.castAdd L w := by
        ext; dsimp [w]; omega
      rw [hidx, QRegister.concat_apply_left]
      exact hcr w (by dsimp [w]; omega)
    · let i : Fin L := ⟨j.val - rem, by omega⟩
      have hidx : (⟨M + L - (rem + L) + j.val, by omega⟩ : Fin (M + L)) =
          Fin.natAdd M i := by
        ext; dsimp [i]; omega
      rw [hidx, QRegister.concat_apply_right]
      exact hL0 i
theorem mk34_realizesCleanUnitary_ctxToDynNested
    {Var : Type} [Fintype Var] [DecidableEq Var] {M L n : ℕ} [NeZero (2 ^ n)]
    (v : Var) (rComb : QRegister M n) (rLeafScr : QRegister L n)
    (hDisj : rComb.DisjointWires rLeafScr)
    (cLeaf : Circuit n) (dLeaf : DynamicCircuit Var n)
    (fLeaf : BitAssignment M → BitAssignment n → ZMod 2)
    (hfLeaf : ∀ (γ γ' : BitAssignment M) (β : BitAssignment n),
      fLeaf γ (writeRegProg β rComb γ') = fLeaf γ β)
    (hLeafKet : ∀ β : BitAssignment n,
      (∀ j : Fin L, β (rLeafScr j) = 0) →
      cLeaf.eval.1.mulVec (MeasureBranchHadamardSem.ket β) =
        ((-1 : ℂ) ^ (fLeaf (fun idx ↦ β (rComb idx)) β).val) •
          MeasureBranchHadamardSem.ket β)
    (hLeafReal : RealizesCleanUnitary v (projZeroAll L rLeafScr.wires) dLeaf cLeaf.eval)
    (q₀ : Wire M) :
    ∀ (K : TempCtx M) (rem : ℕ) (hrem : rem ≤ M),
      ValidCleanRem M rem (K.plug (.z q₀)) →
      RealizesCleanUnitary v
        (projZeroAll (rem + L) (tailScr (rComb.concat rLeafScr hDisj) (rem + L) (by omega)))
        (mk34_ctxToDynNested v rComb dLeaf K) ((mk34_ctxToToff rComb cLeaf K).eval)
  | .hole, rem, hrem, _ => by
      dsimp only [mk34_ctxToDynNested, mk34_ctxToToff]
      have h0 := mk34_tailScr_concat_zero rComb rLeafScr hDisj
      have hLeaf0 : RealizesCleanUnitary v (projZeroAll (0 + L) (tailScr (rComb.concat
          rLeafScr hDisj) (0 + L) (by omega))) dLeaf cLeaf.eval := by
        rwa [h0]
      exact RealizesCleanUnitary.mono_proj (projZeroAll_conjTranspose (0 + L) _)
        (projZeroAll_conjTranspose (rem + L) _) (projZeroAll_tailScr_sub (rComb.concat
        rLeafScr hDisj) (by omega) (by omega) (by omega)) hLeaf0
  | .seqPre c K₁, rem, hrem, ⟨remMid, hmid, _, hv₂, hpres⟩ => by
      let rFull := rComb.concat rLeafScr hDisj
      let P₁ := projZeroAll (rem + L) (tailScr rFull (rem + L) (by omega))
      let P₂ := projZeroAll (remMid + L) (tailScr rFull (remMid + L) (by omega))
      have hP₁ : P₁ᴴ = P₁ := projZeroAll_conjTranspose (rem + L) _
      have hP₂ : P₂ᴴ = P₂ := projZeroAll_conjTranspose (remMid + L) _
      have ih₁ : RealizesCleanUnitary v P₁ (.circuit (c.onRegister rComb).toCircuit)
          ((c.onRegister rComb).toCircuit).eval := RealizesCleanUnitary.circuit v P₁ _
      have ih₂ := mk34_realizesCleanUnitary_ctxToDynNested v rComb rLeafScr hDisj cLeaf dLeaf
        fLeaf hfLeaf hLeafKet hLeafReal q₀ K₁ remMid hmid hv₂
      have hclean : P₂ * (((c.onRegister rComb).toCircuit).eval.1 * P₁) =
          ((c.onRegister rComb).toCircuit).eval.1 * P₁ := by
        apply MeasureBranchHadamardSem.matrix_ext_ket
        intro β
        dsimp only [P₁, P₂, rFull]
        rw [mul_mulVec_prog, mul_mulVec_prog, ket_projZeroAll]
        by_cases hz : ∀ j : Fin (rem + L),
            β (tailScr (rComb.concat rLeafScr hDisj) (rem + L) (by omega) j) = 0
        · rw [ite_eq_left hz, mk34_cliff_onRegister_eval_ket, ket_projZeroAll]
          obtain ⟨hcr, hL0⟩ := (mk34_tailScr_concat_split rComb rLeafScr hDisj rem hrem β).mp hz
          let β₁ := writeRegProg β rComb (c.eval (fun idx ↦ β (rComb idx)))
          have hout : ∀ j : Fin (remMid + L),
              β₁ (tailScr (rComb.concat rLeafScr hDisj) (remMid + L) (by omega) j) = 0 := by
            rw [mk34_tailScr_concat_split rComb rLeafScr hDisj remMid hmid β₁]
            refine ⟨?_, fun j ↦ (mk34_writeRegProg_leafScr_eq rComb rLeafScr hDisj β _ j).trans (hL0
              j)⟩
            have hγ₁ : (fun idx ↦ β₁ (rComb idx)) = c.eval (fun idx ↦ β (rComb idx)) :=
              funext fun idx ↦ writeRegProg_apply_reg β rComb _ idx
            rw [hγ₁]
            exact hpres _ hcr
          rw [ite_eq_left hout]
        · rw [ite_eq_right hz, Matrix.mulVec_zero, Matrix.mulVec_zero]
      have hseq := RealizesCleanUnitary_seq_asym hP₁ hP₂ ih₁ ih₂ hclean
      have heq : (mk34_ctxToToff rComb cLeaf K₁).eval * ((c.onRegister rComb).toCircuit).eval
          = (mk34_ctxToToff rComb cLeaf (.seqPre c K₁)).eval := by
        simp [mk34_ctxToToff, Circuit.eval_seq]
      simpa [mk34_ctxToDynNested, heq] using hseq
  | .seqPost K₁ c, rem, hrem, ⟨remMid, hmid, hv₁, _, hpres⟩ => by
      let rFull := rComb.concat rLeafScr hDisj
      let P₁ := projZeroAll (rem + L) (tailScr rFull (rem + L) (by omega))
      let P₂ := projZeroAll (remMid + L) (tailScr rFull (remMid + L) (by omega))
      have hP₁ : P₁ᴴ = P₁ := projZeroAll_conjTranspose (rem + L) _
      have hP₂ : P₂ᴴ = P₂ := projZeroAll_conjTranspose (remMid + L) _
      have ih₁ := mk34_realizesCleanUnitary_ctxToDynNested v rComb rLeafScr hDisj cLeaf dLeaf
        fLeaf hfLeaf hLeafKet hLeafReal q₀ K₁ rem hrem hv₁
      have ih₂ : RealizesCleanUnitary v P₂ (.circuit (c.onRegister rComb).toCircuit)
          ((c.onRegister rComb).toCircuit).eval := RealizesCleanUnitary.circuit v P₂ _
      have hclean : P₂ * ((mk34_ctxToToff rComb cLeaf K₁).eval.1 * P₁) =
          (mk34_ctxToToff rComb cLeaf K₁).eval.1 * P₁ := by
        apply MeasureBranchHadamardSem.matrix_ext_ket
        intro β
        dsimp only [P₁, P₂, rFull]
        rw [mul_mulVec_prog, mul_mulVec_prog, ket_projZeroAll]
        by_cases hz : ∀ j : Fin (rem + L),
            β (tailScr (rComb.concat rLeafScr hDisj) (rem + L) (by omega) j) = 0
        · obtain ⟨hcr, hL0⟩ := (mk34_tailScr_concat_split rComb rLeafScr hDisj rem hrem β).mp hz
          rw [ite_eq_left hz,
              mk34_ctxToToff_eval_ket_of_leafScr rComb rLeafScr hDisj cLeaf fLeaf hfLeaf hLeafKet
                q₀ K₁ β hL0,
              Matrix.mulVec_smul, ket_projZeroAll]
          let β₁ := writeRegProg β rComb ((K₁.plug (.z q₀)).evalBits (fun idx ↦ β (rComb idx)))
          have hout : ∀ j : Fin (remMid + L),
              β₁ (tailScr (rComb.concat rLeafScr hDisj) (remMid + L) (by omega) j) = 0 := by
            rw [mk34_tailScr_concat_split rComb rLeafScr hDisj remMid hmid β₁]
            refine ⟨?_, fun j ↦ (mk34_writeRegProg_leafScr_eq rComb rLeafScr hDisj β _ j).trans (hL0
              j)⟩
            have hγ₁ : (fun idx ↦ β₁ (rComb idx)) =
                (K₁.plug (.z q₀)).evalBits (fun idx ↦ β (rComb idx)) :=
              funext fun idx ↦ writeRegProg_apply_reg β rComb _ idx
            rw [hγ₁]
            exact hpres _ hcr
          rw [ite_eq_left hout]
        · rw [ite_eq_right hz, Matrix.mulVec_zero, Matrix.mulVec_zero]
      have hseq := RealizesCleanUnitary_seq_asym hP₁ hP₂ ih₁ ih₂ hclean
      have heq : ((c.onRegister rComb).toCircuit).eval * (mk34_ctxToToff rComb cLeaf K₁).eval
          = (mk34_ctxToToff rComb cLeaf (.seqPost K₁ c)).eval := by
        simp [mk34_ctxToToff, Circuit.eval_seq]
      simpa [mk34_ctxToDynNested, heq] using hseq
  | .tempAnd c₁ c₂ anc h₁₂ h₁a h₂a K₁, rem, hrem, ⟨hanc_lo, hvBody, hpresBody⟩ => by
      let rFull := rComb.concat rLeafScr hDisj
      have hanc_lt : anc.val < M := anc.isLt
      let rem' := M - (anc.val + 1)
      have hrem' : rem' ≤ M := by omega
      have hrem1 : (rem' + L) + 1 ≤ M + L := by omega
      have hrem_le : (rem' + L) + 1 ≤ rem + L := by omega
      have ihBody := mk34_realizesCleanUnitary_ctxToDynNested v rComb rLeafScr hDisj cLeaf dLeaf
        fLeaf hfLeaf hLeafKet hLeafReal q₀ K₁ rem' hrem' hvBody
      have hanc_eq : rComb anc = rFull ⟨(M + L) - ((rem' + L) + 1), by omega⟩ := by
        have hidx : (⟨(M + L) - ((rem' + L) + 1), by omega⟩ : Fin (M + L)) = Fin.castAdd L anc := by
          ext; dsimp [rem']; omega
        rw [hidx, QRegister.concat_apply_left]
      have hdisj : ∀ j : Fin (rem' + L),
          rComb anc ≠ tailScr rFull (rem' + L) (by omega) j := by
        intro j h
        rw [hanc_eq] at h
        have hinj := congrArg Fin.val (rFull.wires.injective h)
        dsimp [tailScr, rem'] at hinj
        omega
      let U_body := (mk34_ctxToToff rComb cLeaf K₁).eval
      let U_clean := (mk34_ctxToToff rComb cLeaf (.tempAnd c₁ c₂ anc h₁₂ h₁a h₂a K₁)).eval
      have hstep := RealizesCleanUnitary.withTempAnd_projZeroAll
        v (rComb c₁) (rComb c₂) (rComb anc)
        (rComb.wires.injective.ne h₁₂) (rComb.wires.injective.ne h₁a) (rComb.wires.injective.ne h₂a)
        (rem' + L) (tailScr rFull (rem' + L) (by omega)) hdisj
        (mk34_ctxToDynNested v rComb dLeaf K₁) U_body U_clean ihBody
        (by
          intro β hanc0 _
          simp only [U_clean, U_body, mk34_ctxToToff,
            MeasureBranchHadamardSem.eval_seq_mulVec, MeasureBranchHadamardSem.ket_TOFF,
            hanc0, zero_add])
        (by
          intro β hanc0 hscr0
          obtain ⟨hcr', hL0⟩ := (mk34_tailScr_concat_split rComb rLeafScr hDisj rem' hrem' β).mp
            hscr0
          let γ : BitAssignment M := fun idx ↦ β (rComb idx)
          have hγ_anc : γ anc = 0 := hanc0
          let β₁ : BitAssignment M := Function.update γ anc (γ anc + γ c₁ * γ c₂)
          have hγ₁_clean : cleanRem M rem' β₁ := by
            intro w hw
            have hw_ne : w ≠ anc := wire_ne_of_gt (by dsimp [rem'] at hw; omega)
            dsimp only [β₁]
            rw [Function.update_of_ne hw_ne]
            exact hcr' w hw
          obtain ⟨hc₁, hc₂, ha⟩ := hpresBody β₁ hγ₁_clean
          have hfinal_anc :
              ((TempCtx.tempAnd c₁ c₂ anc h₁₂ h₁a h₂a K₁).plug (.z q₀)).evalBits γ anc = 0 := by
            dsimp only [TempCtx.plug, TempPhaseProg.evalBits]
            change Function.update ((K₁.plug (.z q₀)).evalBits β₁) anc
              ((K₁.plug (.z q₀)).evalBits β₁ anc +
                (K₁.plug (.z q₀)).evalBits β₁ c₁ * (K₁.plug (.z q₀)).evalBits β₁ c₂) anc = 0
            rw [Function.update_self, ha, hc₁, hc₂]
            simp [β₁, hγ_anc, Function.update_self, Function.update_of_ne h₁a,
              Function.update_of_ne h₂a, CharTwo.add_self_eq_zero]
          rw [show U_clean.1.mulVec (MeasureBranchHadamardSem.ket β) = _ from
              mk34_ctxToToff_eval_ket_of_leafScr rComb rLeafScr hDisj cLeaf fLeaf hfLeaf hLeafKet q₀
                (.tempAnd c₁ c₂ anc h₁₂ h₁a h₂a K₁) β hL0,
            Matrix.mulVec_smul, MeasureBranchHadamardSem.ket_projector_zero]
          rw [writeRegProg_apply_reg, hfinal_anc]
          simp)
      have hscr_eq : projZeroAll ((rem' + L) + 1)
          (Fin.cons (rComb anc) (tailScr rFull (rem' + L) (by omega))) = projZeroAll
          ((rem' + L) + 1) (tailScr rFull ((rem' + L) + 1) hrem1) := by
        rw [hanc_eq, ← tailScr_succ rFull (rem' + L) hrem1]
      have hstep' : RealizesCleanUnitary v
          (projZeroAll ((rem' + L) + 1) (tailScr rFull ((rem' + L) + 1) hrem1))
          (mk34_ctxToDynNested v rComb dLeaf (.tempAnd c₁ c₂ anc h₁₂ h₁a h₂a K₁)) U_clean := by
        simpa [mk34_ctxToDynNested, hscr_eq] using hstep
      exact RealizesCleanUnitary.mono_proj (projZeroAll_conjTranspose ((rem' + L) + 1) _)
        (projZeroAll_conjTranspose (rem + L) _)
        (projZeroAll_tailScr_sub rFull hrem1 (by omega) hrem_le) hstep'
/-!
## Section 2: Direct `(B + 4)`-Wire Inner Mid-Kick & Single-Stage `104 + 4 * B` `T` Oracle
-/
/-- Combined `(mk34_mB B)`-wire register `(rCoreHi86 ++ rHold3 ++ rOutTop) ++ rSubB`
taking `rHold3 : QRegister 3 n` and `rSubB : QRegister (B + 4) n` directly. -/
def mk34_rCombBDirect {n : ℕ} (B : ℕ) (rCore : QRegister posCoreWires n)
    (rHold3 : QRegister 3 n) (rOutTop : QRegister (B + 1) n) (rSubB : QRegister (B + 4) n)
    (hCHold : (mk34_rCoreHi86 rCore).DisjointWires rHold3)
    (hCOut : (mk34_rCoreHi86 rCore).DisjointWires rOutTop)
    (hHOut : rHold3.DisjointWires rOutTop)
    (hCSub : (mk34_rCoreHi86 rCore).DisjointWires rSubB) (hHSub : rHold3.DisjointWires rSubB)
    (hOutSub : rOutTop.DisjointWires rSubB) : QRegister (mk34_mB B) n :=
  let rAct89 := (mk34_rCoreHi86 rCore).concat rHold3 hCHold
  have hAct89Out : rAct89.DisjointWires rOutTop :=
    QRegister.disjoint_iff.mpr fun a b heq ↦
      Fin.addCases (m := 86) (n := 3)
        (motive := fun a ↦ rAct89 a = rOutTop b → False)
        (fun i hi ↦ hCOut.ne i b ((QRegister.concat_apply_left _ _ _ i).symm.trans hi))
        (fun j hj ↦ hHOut.ne j b ((QRegister.concat_apply_right _ _ _ j).symm.trans hj))
        a heq
  let rActB := rAct89.concat rOutTop hAct89Out
  have hAct89Sub : rAct89.DisjointWires rSubB :=
    QRegister.disjoint_iff.mpr fun a b heq ↦
      Fin.addCases (m := 86) (n := 3)
        (motive := fun a ↦ rAct89 a = rSubB b → False)
        (fun i hi ↦ hCSub.ne i b ((QRegister.concat_apply_left _ _ _ i).symm.trans hi))
        (fun j hj ↦ hHSub.ne j b ((QRegister.concat_apply_right _ _ _ j).symm.trans hj))
        a heq
  have hActBSub : rActB.DisjointWires rSubB :=
    QRegister.disjoint_iff.mpr fun a b heq ↦
      Fin.addCases (m := 89) (n := B + 1)
        (motive := fun a ↦ rActB a = rSubB b → False)
        (fun i hi ↦ hAct89Sub.ne i b ((QRegister.concat_apply_left _ _ _ i).symm.trans hi))
        (fun j hj ↦ hOutSub.ne j b ((QRegister.concat_apply_right _ _ _ j).symm.trans hj))
        a heq
  rActB.concat rSubB hActBSub
theorem mk34_rCombBDirect_core {n : ℕ} (B : ℕ)
    (rCore : QRegister posCoreWires n) (rHold3 : QRegister 3 n)
    (rOutTop : QRegister (B + 1) n) (rSubB : QRegister (B + 4) n)
    (hCHold : (mk34_rCoreHi86 rCore).DisjointWires rHold3)
    (hCOut : (mk34_rCoreHi86 rCore).DisjointWires rOutTop)
    (hHOut : rHold3.DisjointWires rOutTop)
    (hCSub : (mk34_rCoreHi86 rCore).DisjointWires rSubB)
    (hHSub : rHold3.DisjointWires rSubB)
    (hOutSub : rOutTop.DisjointWires rSubB) (i : Fin 86) :
    mk34_rCombBDirect B rCore rHold3 rOutTop rSubB hCHold hCOut hHOut hCSub hHSub hOutSub
        ⟨i.val, by dsimp [mk34_mB]; omega⟩ =
      rCore ⟨3948 + i.val, by dsimp [posCoreWires]; omega⟩ := by
  dsimp only [mk34_rCombBDirect]
  have h1 : (⟨i.val, by omega⟩ : Fin ((89 + (B + 1)) + (B + 4))) =
      Fin.castAdd (B + 4) (Fin.castAdd (B + 1) (Fin.castAdd 3 i)) := by ext; rfl
  rw [h1, QRegister.concat_apply_left, QRegister.concat_apply_left, QRegister.concat_apply_left]
  simp [mk34_rCoreHi86]
theorem mk34_rCombBDirect_hold {n : ℕ} (B : ℕ)
    (rCore : QRegister posCoreWires n) (rHold3 : QRegister 3 n)
    (rOutTop : QRegister (B + 1) n) (rSubB : QRegister (B + 4) n)
    (hCHold : (mk34_rCoreHi86 rCore).DisjointWires rHold3)
    (hCOut : (mk34_rCoreHi86 rCore).DisjointWires rOutTop)
    (hHOut : rHold3.DisjointWires rOutTop)
    (hCSub : (mk34_rCoreHi86 rCore).DisjointWires rSubB)
    (hHSub : rHold3.DisjointWires rSubB)
    (hOutSub : rOutTop.DisjointWires rSubB) (i : Fin 3) :
    mk34_rCombBDirect B rCore rHold3 rOutTop rSubB hCHold hCOut hHOut hCSub hHSub hOutSub
        ⟨86 + i.val, by dsimp [mk34_mB]; omega⟩ =
      rHold3 i := by
  dsimp only [mk34_rCombBDirect]
  have h1 : (⟨86 + i.val, by omega⟩ : Fin ((89 + (B + 1)) + (B + 4))) =
      Fin.castAdd (B + 4) (Fin.castAdd (B + 1) (Fin.natAdd 86 i)) := by ext; rfl
  rw [h1, QRegister.concat_apply_left, QRegister.concat_apply_left, QRegister.concat_apply_right]
theorem mk34_rCombBDirect_out {n : ℕ} (B : ℕ)
    (rCore : QRegister posCoreWires n) (rHold3 : QRegister 3 n)
    (rOutTop : QRegister (B + 1) n) (rSubB : QRegister (B + 4) n)
    (hCHold : (mk34_rCoreHi86 rCore).DisjointWires rHold3)
    (hCOut : (mk34_rCoreHi86 rCore).DisjointWires rOutTop)
    (hHOut : rHold3.DisjointWires rOutTop)
    (hCSub : (mk34_rCoreHi86 rCore).DisjointWires rSubB)
    (hHSub : rHold3.DisjointWires rSubB)
    (hOutSub : rOutTop.DisjointWires rSubB) (i : Fin (B + 1)) :
    mk34_rCombBDirect B rCore rHold3 rOutTop rSubB hCHold hCOut hHOut hCSub hHSub hOutSub
        ⟨89 + i.val, by dsimp [mk34_mB]; omega⟩ =
      rOutTop i := by
  dsimp only [mk34_rCombBDirect]
  have h1 : (⟨89 + i.val, by omega⟩ : Fin ((89 + (B + 1)) + (B + 4))) =
      Fin.castAdd (B + 4) (Fin.natAdd 89 i) := by ext; rfl
  rw [h1, QRegister.concat_apply_left, QRegister.concat_apply_right]
theorem mk34_tailScr_rCombBDirect {n : ℕ} (B : ℕ)
    (rCore : QRegister posCoreWires n) (rHold3 : QRegister 3 n)
    (rOutTop : QRegister (B + 1) n) (rSubB : QRegister (B + 4) n)
    (hCHold : (mk34_rCoreHi86 rCore).DisjointWires rHold3)
    (hCOut : (mk34_rCoreHi86 rCore).DisjointWires rOutTop)
    (hHOut : rHold3.DisjointWires rOutTop)
    (hCSub : (mk34_rCoreHi86 rCore).DisjointWires rSubB)
    (hHSub : rHold3.DisjointWires rSubB)
    (hOutSub : rOutTop.DisjointWires rSubB) :
    tailScr (mk34_rCombBDirect B rCore rHold3 rOutTop rSubB hCHold hCOut hHOut hCSub hHSub hOutSub)
        (B + 4) (by dsimp [mk34_mB]; omega) =
      rSubB.wires := by
  funext j
  dsimp only [tailScr, mk34_rCombBDirect]
  have h1 : (⟨(mk34_mB B - (B + 4)) + j.val, by dsimp [mk34_mB]; omega⟩ :
      Fin ((89 + (B + 1)) + (B + 4))) = Fin.natAdd (89 + (B + 1)) j := by
    ext; dsimp [mk34_mB]; omega
  rw [h1, QRegister.concat_apply_right]
/-- Direct `(B + 4)`-wire inner reversible circuit for `mk34_ctxMidB`. -/
def mk34_cMidKickBDirect {n : ℕ} (B : ℕ) (hB1 : 1 ≤ B) (hB27 : B ≤ 27)
    (rCore : QRegister posCoreWires n) (rHold3 : QRegister 3 n)
    (rOutTop : QRegister (B + 1) n) (rSubB : QRegister (B + 4) n)
    (hCHold : (mk34_rCoreHi86 rCore).DisjointWires rHold3)
    (hCOut : (mk34_rCoreHi86 rCore).DisjointWires rOutTop)
    (hHOut : rHold3.DisjointWires rOutTop)
    (hCSub : (mk34_rCoreHi86 rCore).DisjointWires rSubB) (hHSub : rHold3.DisjointWires rSubB)
    (hOutSub : rOutTop.DisjointWires rSubB) : Circuit n :=
  let rComb := mk34_rCombBDirect B rCore rHold3 rOutTop rSubB
    hCHold hCOut hHOut hCSub hHSub hOutSub
  mk34_ctxToToff rComb (mk34_cLeafMidBOn B rComb) (mk34_ctxMidB B hB1 hB27)
/-- Direct `(B + 4)`-wire inner `0`-`.TOFF` dynamic circuit (`4 * B + 12` `T`). -/
def mk34_dMidKickBDirect {Var : Type} {n : ℕ} (B : ℕ) (hB1 : 1 ≤ B) (hB27 : B ≤ 27) (v : Var)
    (rCore : QRegister posCoreWires n) (rHold3 : QRegister 3 n)
    (rOutTop : QRegister (B + 1) n) (rSubB : QRegister (B + 4) n)
    (hCHold : (mk34_rCoreHi86 rCore).DisjointWires rHold3)
    (hCOut : (mk34_rCoreHi86 rCore).DisjointWires rOutTop)
    (hHOut : rHold3.DisjointWires rOutTop)
    (hCSub : (mk34_rCoreHi86 rCore).DisjointWires rSubB) (hHSub : rHold3.DisjointWires rSubB)
    (hOutSub : rOutTop.DisjointWires rSubB) : DynamicCircuit Var n :=
  let rComb := mk34_rCombBDirect B rCore rHold3 rOutTop rSubB
    hCHold hCOut hHOut hCSub hHSub hOutSub
  mk34_ctxToDyn v rComb (mk34_cLeafMidBOn B rComb) (mk34_ctxMidB B hB1 hB27)
@[scoped simp] theorem mk34_count_dMidKickBDirect_toff {Var : Type} {n : ℕ} (B : ℕ)
    (hB1 : 1 ≤ B) (hB27 : B ≤ 27) (v : Var) (rCore : QRegister posCoreWires n)
    (rHold3 : QRegister 3 n) (rOutTop : QRegister (B + 1) n) (rSubB : QRegister (B + 4) n)
    (hCHold : (mk34_rCoreHi86 rCore).DisjointWires rHold3)
    (hCOut : (mk34_rCoreHi86 rCore).DisjointWires rOutTop)
    (hHOut : rHold3.DisjointWires rOutTop)
    (hCSub : (mk34_rCoreHi86 rCore).DisjointWires rSubB) (hHSub : rHold3.DisjointWires rSubB)
    (hOutSub : rOutTop.DisjointWires rSubB) : (mk34_dMidKickBDirect B hB1 hB27 v rCore rHold3
    rOutTop rSubB hCHold hCOut hHOut hCSub hHSub hOutSub).count PrimitiveGate.TOFF = 0 := by
  simp [mk34_dMidKickBDirect, mk34_ctxToDyn_count_toff, mk34_cLeafMidBOn_count_toff]
@[scoped simp] theorem mk34_count_dMidKickBDirect_t {Var : Type} {n : ℕ} (B : ℕ) (hB1 : 1 ≤ B)
    (hB27 : B ≤ 27) (v : Var) (rCore : QRegister posCoreWires n) (rHold3 : QRegister 3 n)
    (rOutTop : QRegister (B + 1) n) (rSubB : QRegister (B + 4) n)
    (hCHold : (mk34_rCoreHi86 rCore).DisjointWires rHold3)
    (hCOut : (mk34_rCoreHi86 rCore).DisjointWires rOutTop)
    (hHOut : rHold3.DisjointWires rOutTop)
    (hCSub : (mk34_rCoreHi86 rCore).DisjointWires rSubB) (hHSub : rHold3.DisjointWires rSubB)
    (hOutSub : rOutTop.DisjointWires rSubB) : (mk34_dMidKickBDirect B hB1 hB27 v rCore rHold3
    rOutTop rSubB hCHold hCOut hHOut hCSub hHSub hOutSub).count PrimitiveGate.T = 4 * B + 12
    := by
  simp only [mk34_dMidKickBDirect, mk34_ctxToDyn_count_t, mk34_ctxMidB_countTempAnd,
    mk34_cLeafMidBOn_count_t]
  ring
theorem mk34_dMidKickBDirect_preservesStoreConst {Var : Type} [Fintype Var] [DecidableEq Var]
    {n : ℕ} (B : ℕ) (hB1 : 1 ≤ B) (hB27 : B ≤ 27) (v : Var) (rCore : QRegister posCoreWires n)
    (rHold3 : QRegister 3 n) (rOutTop : QRegister (B + 1) n) (rSubB : QRegister (B + 4) n)
    (hCHold : (mk34_rCoreHi86 rCore).DisjointWires rHold3)
    (hCOut : (mk34_rCoreHi86 rCore).DisjointWires rOutTop)
    (hHOut : rHold3.DisjointWires rOutTop)
    (hCSub : (mk34_rCoreHi86 rCore).DisjointWires rSubB) (hHSub : rHold3.DisjointWires rSubB)
    (hOutSub : rOutTop.DisjointWires rSubB) : PreservesStoreConst (mk34_dMidKickBDirect B hB1
    hB27 v rCore rHold3 rOutTop rSubB hCHold hCOut hHOut hCSub hHSub hOutSub) :=
    mk34_ctxToDyn_preservesStoreConst v _ _ (mk34_ctxMidB B hB1 hB27)
theorem mk34_cleanRem_of_subBDirect {n : ℕ} (B : ℕ) (rCore : QRegister posCoreWires n)
    (rHold3 : QRegister 3 n) (rOutTop : QRegister (B + 1) n) (rSubB : QRegister (B + 4) n)
    (hCHold : (mk34_rCoreHi86 rCore).DisjointWires rHold3)
    (hCOut : (mk34_rCoreHi86 rCore).DisjointWires rOutTop)
    (hHOut : rHold3.DisjointWires rOutTop)
    (hCSub : (mk34_rCoreHi86 rCore).DisjointWires rSubB) (hHSub : rHold3.DisjointWires rSubB)
    (hOutSub : rOutTop.DisjointWires rSubB) (β : BitAssignment n)
    (hSubB : ∀ j : Fin (B + 4), β (rSubB j) = 0) : cleanRem (mk34_mB B) (B + 4) (fun idx ↦ β
    (mk34_rCombBDirect B rCore rHold3 rOutTop rSubB hCHold hCOut hHOut hCSub hHSub hOutSub
    idx)) :=
  fun w hw ↦ by
    let rComb := mk34_rCombBDirect B rCore rHold3 rOutTop rSubB
      hCHold hCOut hHOut hCSub hHSub hOutSub
    let j : Fin (B + 4) := ⟨w.val - (mk34_mB B - (B + 4)), by dsimp [mk34_mB] at hw ⊢; omega⟩
    have hwEq : rComb w = tailScr rComb (B + 4) (by dsimp [mk34_mB]; omega) j := by
      dsimp only [tailScr, j]
      congr 1; ext; dsimp [mk34_mB] at hw ⊢; omega
    change β (rComb w) = 0
    rw [hwEq, congrFun (mk34_tailScr_rCombBDirect B rCore rHold3 rOutTop rSubB
      hCHold hCOut hHOut hCSub hHSub hOutSub) j]
    exact hSubB j
theorem mk34_cMidKickBDirect_eval_ket_raw {n : ℕ} (B : ℕ) (hB1 : 1 ≤ B) (hB27 : B ≤ 27)
    (rCore : QRegister posCoreWires n) (rHold3 : QRegister 3 n)
    (rOutTop : QRegister (B + 1) n) (rSubB : QRegister (B + 4) n)
    (hCHold : (mk34_rCoreHi86 rCore).DisjointWires rHold3)
    (hCOut : (mk34_rCoreHi86 rCore).DisjointWires rOutTop)
    (hHOut : rHold3.DisjointWires rOutTop)
    (hCSub : (mk34_rCoreHi86 rCore).DisjointWires rSubB)
    (hHSub : rHold3.DisjointWires rSubB)
    (hOutSub : rOutTop.DisjointWires rSubB) (β : BitAssignment n)
    (hSubB : ∀ j : Fin (B + 4), β (rSubB j) = 0) :
    let rComb := mk34_rCombBDirect B rCore rHold3 rOutTop rSubB
      hCHold hCOut hHOut hCSub hHSub hOutSub
    (mk34_cMidKickBDirect B hB1 hB27 rCore rHold3 rOutTop rSubB
      hCHold hCOut hHOut hCSub hHSub hOutSub).eval.1.mulVec (ket β) =
      ((-1 : ℂ) ^ (mk34_fLeafMidB B
        ((mk34_ctxMidB B hB1 hB27).fwdBits (fun idx ↦ β (rComb idx)))).val) • ket β := by
  intro rComb
  have hcr := mk34_cleanRem_of_subBDirect B rCore rHold3 rOutTop rSubB
    hCHold hCOut hHOut hCSub hHSub hOutSub β hSubB
  rw [mk34_cMidKickBDirect, ← mbh_ket_eq_ket,
      mk34_ctxToToff_eval_ket rComb _ _ (mk34_cLeafMidBOn_eval_mbh_ket B rComb)
        ⟨0, by dsimp [mk34_mB]; omega⟩ (mk34_ctxMidB B hB1 hB27) β]
  rw [mk34_pMidB_eq, (mk34_pMidB_valid_and_bits B hB1 hB27).2 _ hcr,
      mk34_writeRegProg_self, mbh_ket_eq_ket]
theorem mk34_realizesCleanUnitary_dMidKickBDirect {Var : Type} [Fintype Var] [DecidableEq Var]
    {n : ℕ} [NeZero (2 ^ n)] (B : ℕ) (hB1 : 1 ≤ B) (hB27 : B ≤ 27) (v : Var)
    (rCore : QRegister posCoreWires n) (rHold3 : QRegister 3 n)
    (rOutTop : QRegister (B + 1) n) (rSubB : QRegister (B + 4) n)
    (hCHold : (mk34_rCoreHi86 rCore).DisjointWires rHold3)
    (hCOut : (mk34_rCoreHi86 rCore).DisjointWires rOutTop)
    (hHOut : rHold3.DisjointWires rOutTop)
    (hCSub : (mk34_rCoreHi86 rCore).DisjointWires rSubB) (hHSub : rHold3.DisjointWires rSubB)
    (hOutSub : rOutTop.DisjointWires rSubB) : RealizesCleanUnitary v
    (projZeroAll (B + 4) rSubB.wires) (mk34_dMidKickBDirect B hB1 hB27 v rCore rHold3 rOutTop
    rSubB hCHold hCOut hHOut hCSub hHSub hOutSub) (mk34_cMidKickBDirect B hB1 hB27 rCore
    rHold3 rOutTop rSubB hCHold hCOut hHOut hCSub hHSub hOutSub).eval := by
  let rComb := mk34_rCombBDirect B rCore rHold3 rOutTop rSubB
    hCHold hCOut hHOut hCSub hHSub hOutSub
  have hpv : ValidCleanRem (mk34_mB B) (B + 4)
      ((mk34_ctxMidB B hB1 hB27).plug (.z ⟨0, by dsimp [mk34_mB]; omega⟩)) := by
    rw [mk34_pMidB_eq]
    exact (mk34_pMidB_valid_and_bits B hB1 hB27).1
  have hTail := mk34_tailScr_rCombBDirect B rCore rHold3 rOutTop rSubB
    hCHold hCOut hHOut hCSub hHSub hOutSub
  have h0 := mk34_realizesCleanUnitary_ctxToDyn v rComb (mk34_cLeafMidBOn B rComb)
    (mk34_fLeafMidB B) (mk34_cLeafMidBOn_eval_mbh_ket B rComb)
    ⟨0, by dsimp [mk34_mB]; omega⟩ (mk34_ctxMidB B hB1 hB27) (B + 4)
    (by dsimp [mk34_mB]; omega) hpv
  rw [hTail] at h0
  exact h0
/-- Dummy `3`-wire slice `rCore[0..3)` (disjoint from `rCoreHi86 = rCore[3948..4034)` and never
touched by `mk34_ctxComp23`). -/
abbrev mk34_rCoreLo3 {n : ℕ} (rCore : QRegister posCoreWires n) : QRegister 3 n :=
  rCore.slice 0 3 (by dsimp [posCoreWires]; omega)
theorem mk34_rCoreHi86_disjoint_rCoreLo3 {n : ℕ} (rCore : QRegister posCoreWires n) :
    (mk34_rCoreHi86 rCore).DisjointWires (mk34_rCoreLo3 rCore) :=
  QRegister.disjoint_iff.mpr fun a b h ↦ by
    dsimp only [mk34_rCoreHi86, mk34_rCoreLo3] at h
    rw [QRegister.slice_apply, QRegister.slice_apply] at h
    have hv := congrArg Fin.val (rCore.wires.injective h)
    dsimp at hv; omega
/-- `112`-wire outer register `(rCoreHi86 ++ rCoreLo3) ++ rSub23` for single-stage
`mk34_ctxComp23`. -/
def mk34_rComb112Direct {n : ℕ} (rCore : QRegister posCoreWires n) (rSub23 : QRegister 23 n)
    (hCS23 : rCore.DisjointWires rSub23) : QRegister 112 n :=
  let rAct89 := (mk34_rCoreHi86 rCore).concat (mk34_rCoreLo3 rCore)
    (mk34_rCoreHi86_disjoint_rCoreLo3 rCore)
  have hAct89Sub : rAct89.DisjointWires rSub23 :=
    QRegister.disjoint_iff.mpr fun a b heq ↦
      Fin.addCases (m := 86) (n := 3)
        (motive := fun a ↦ rAct89 a = rSub23 b → False)
        (fun i hi ↦ (hCS23.compose_left _).ne i b ((QRegister.concat_apply_left _ _ _ i).symm.trans
          hi))
        (fun j hj ↦ (hCS23.compose_left _).ne j b ((QRegister.concat_apply_right _ _ _ j).symm.trans
          hj))
        a heq
  rAct89.concat rSub23 hAct89Sub
theorem mk34_rComb112Direct_core {n : ℕ} (rCore : QRegister posCoreWires n)
    (rSub23 : QRegister 23 n) (hCS23 : rCore.DisjointWires rSub23) (i : Fin 86) :
    mk34_rComb112Direct rCore rSub23 hCS23 ⟨i.val, by omega⟩ =
      rCore ⟨3948 + i.val, by dsimp [posCoreWires]; omega⟩ := by
  dsimp only [mk34_rComb112Direct]
  have h1 : (⟨i.val, by omega⟩ : Fin ((86 + 3) + 23)) =
      Fin.castAdd 23 (Fin.castAdd 3 i) := by ext; rfl
  rw [h1, QRegister.concat_apply_left, QRegister.concat_apply_left]
  simp [mk34_rCoreHi86]
theorem mk34_rComb112Direct_sub23 {n : ℕ} (rCore : QRegister posCoreWires n)
    (rSub23 : QRegister 23 n) (hCS23 : rCore.DisjointWires rSub23) (j : Fin 23) :
    mk34_rComb112Direct rCore rSub23 hCS23 ⟨89 + j.val, by omega⟩ = rSub23 j := by
  dsimp only [mk34_rComb112Direct]
  have h1 : (⟨89 + j.val, by omega⟩ : Fin ((86 + 3) + 23)) = Fin.natAdd 89 j := by ext; rfl
  rw [h1, QRegister.concat_apply_right]
/-- Embedding `Fin 3 ↪ Fin 23` selecting indices `17, 21, 22` (`u1, vL, d3` in `rSub23`). -/
def mk34_holdIdx3From23 : Fin 3 ↪ Fin 23 where
  toFun i := if i.val = 0 then ⟨17, by decide⟩ else if i.val = 1 then ⟨21, by decide⟩ else ⟨22,
    by decide⟩
  inj' a b h := by fin_cases a <;> fin_cases b <;> revert h <;> decide
/-- `3`-wire hold register `(rSub23 17, rSub23 21, rSub23 22)` (`= (rComb112 106, 110, 111)`). -/
def mk34_rHold3FromSub23 {n : ℕ} (rSub23 : QRegister 23 n) : QRegister 3 n :=
  ⟨mk34_holdIdx3From23.trans rSub23.wires⟩
@[scoped simp] theorem mk34_append_fwdBits {M : ℕ} (F G : TempCtx M) (γ : BitAssignment M) :
    (F.append G).fwdBits γ = G.fwdBits (F.fwdBits γ) := by
  induction F generalizing γ with
  | hole => rfl
  | seqPre _ _ ih => exact ih _
  | seqPost _ _ ih => exact ih _
  | tempAnd _ _ _ _ _ _ _ ih => exact ih _
theorem mk34_ctxLitAnd_fwdBits_of_ne {M : ℕ} (cur : ℕ) (hcur : cur + 1 ≤ M) (c₁ : Wire M)
    (neg₁ : Bool) (c₂ : Wire M) (neg₂ : Bool) (h₁₂ : c₁ ≠ c₂) (hc₁ : c₁.val < cur)
    (hc₂ : c₂.val < cur) (γ : BitAssignment M) (w : Wire M) (hw : w.val ≠ cur) :
    (ctxLitAnd cur hcur c₁ neg₁ c₂ neg₂ h₁₂ hc₁ hc₂).fwdBits γ w = γ w := by
  dsimp only [ctxLitAnd, flipPair]
  cases neg₁ <;> cases neg₂ <;>
    simp only [Bool.false_eq_true, ↓reduceIte, mk34_append_fwdBits,
      TempCtx.fwdBits, ctxCliffAlloc, ctxTempBit, CliffProg.eval]
  · exact Function.update_of_ne (fun h ↦ hw (congrArg Fin.val h)) _ _
  · by_cases hw2 : w = c₂
    · subst hw2
      rw [Function.update_self, Function.update_of_ne (wire_ne_of_lt hc₂),
          Function.update_self, add_assoc, CharTwo.add_self_eq_zero, add_zero]
    · rw[Function.update_of_ne hw2, Function.update_of_ne (fun h ↦ hw (congrArg Fin.val h)),
        Function.update_of_ne hw2]
  · by_cases hw1 : w = c₁
    · subst hw1
      rw [Function.update_self, Function.update_of_ne (wire_ne_of_lt hc₁),
          Function.update_self, add_assoc, CharTwo.add_self_eq_zero, add_zero]
    · rw[Function.update_of_ne hw1, Function.update_of_ne (fun h ↦ hw (congrArg Fin.val h)),
        Function.update_of_ne hw1]
  · by_cases hw2 : w = c₂
    · subst hw2
      rw[Function.update_self, Function.update_of_ne h₁₂.symm,
          Function.update_of_ne (wire_ne_of_lt hc₂), Function.update_of_ne h₁₂.symm,
          Function.update_self, add_assoc, CharTwo.add_self_eq_zero, add_zero]
    · by_cases hw1 : w = c₁
      · subst hw1
        rw[Function.update_of_ne h₁₂, Function.update_self,
            Function.update_of_ne (wire_ne_of_lt hc₁), Function.update_of_ne h₁₂,
            Function.update_self, add_assoc, CharTwo.add_self_eq_zero, add_zero]
      · rw [Function.update_of_ne hw2, Function.update_of_ne hw1,
            Function.update_of_ne (fun h ↦ hw (congrArg Fin.val h)),
            Function.update_of_ne hw2, Function.update_of_ne hw1]
theorem mk34_ctxComp23_fwdBits_below (γ : BitAssignment 112) (w : Wire 112) (hw : w.val < 89) :
    mk34_ctxComp23.fwdBits γ w = γ w := by
  simp only [mk34_ctxComp23, mk34_append_fwdBits]
  repeat rw [mk34_ctxLitAnd_fwdBits_of_ne _ _ _ _ _ _ _ _ _ _ w (by omega)]
/-- Clean `23`-wire prefix `rScr[0..23)` for single-stage `mk34_ctxComp23`. -/
abbrev mk34_rSub23OfScr {n mScr : ℕ} (B : ℕ) (hmScr : B + 27 ≤ mScr) (rScr : QRegister mScr n)
    : QRegister 23 n := rScr.slice 0 23 (by omega)
/-- Clean `(B + 4)`-wire slice `rScr[23..23+B+4)` for single-stage `mk34_ctxMidB`. -/
abbrev mk34_rSubBOfScr {n mScr : ℕ} (B : ℕ) (hmScr : B + 27 ≤ mScr) (rScr : QRegister mScr n)
    : QRegister (B + 4) n := rScr.slice 23 (B + 4) (by omega)
theorem mk34_rSub23OfScr_disjoint_rSubBOfScr {n mScr : ℕ} (B : ℕ) (hmScr : B + 27 ≤ mScr)
    (rScr : QRegister mScr n) :
    (mk34_rSub23OfScr B hmScr rScr).DisjointWires (mk34_rSubBOfScr B hmScr rScr) :=
  QRegister.disjoint_iff.mpr fun a b h ↦ by
    dsimp only [mk34_rSub23OfScr, mk34_rSubBOfScr] at h
    rw [QRegister.slice_apply, QRegister.slice_apply] at h
    have hv := congrArg Fin.val (rScr.wires.injective h)
    dsimp at hv; omega
theorem mk34_rHold3FromSub23_disjoint_rSubBOfScr {n mScr : ℕ} (B : ℕ) (hmScr : B + 27 ≤ mScr)
    (rScr : QRegister mScr n) :
    (mk34_rHold3FromSub23 (mk34_rSub23OfScr B hmScr rScr)).DisjointWires
    (mk34_rSubBOfScr B hmScr rScr) := QRegister.disjoint_iff.mpr fun i j h ↦
    (mk34_rSub23OfScr_disjoint_rSubBOfScr B hmScr rScr).ne (mk34_holdIdx3From23 i) j h
theorem mk34_rCoreHi86_disjoint_rHold3FromSub23 {n mScr : ℕ} (B : ℕ) (hmScr : B + 27 ≤ mScr)
    (rCore : QRegister posCoreWires n) (rScr : QRegister mScr n)
    (hCS : rCore.DisjointWires rScr) : (mk34_rCoreHi86 rCore).DisjointWires
    (mk34_rHold3FromSub23 (mk34_rSub23OfScr B hmScr rScr)) := QRegister.disjoint_iff.mpr fun i
    j h ↦ ((hCS.compose_left _).compose_right _).ne i (mk34_holdIdx3From23 j) h
theorem mk34_rHold3FromSub23_disjoint_rOutTop {n mScr : ℕ} (B : ℕ) (hmScr : B + 27 ≤ mScr)
    (rOutTop : QRegister (B + 1) n) (rScr : QRegister mScr n)
    (hOutS : rOutTop.DisjointWires rScr) :
    (mk34_rHold3FromSub23 (mk34_rSub23OfScr B hmScr rScr)).DisjointWires rOutTop :=
  QRegister.disjoint_iff.mpr fun i j h ↦
    (hOutS.compose_right _).ne j (mk34_holdIdx3From23 i) h.symm
theorem mk34_rComb112Direct_disjoint_rSubBOfScr {n mScr : ℕ} (B : ℕ) (hmScr : B + 27 ≤ mScr)
    (rCore : QRegister posCoreWires n) (rScr : QRegister mScr n)
    (hCS : rCore.DisjointWires rScr) : (mk34_rComb112Direct rCore (mk34_rSub23OfScr B hmScr
    rScr) (hCS.compose_right _)).DisjointWires (mk34_rSubBOfScr B hmScr rScr) := by
  have h1 : (mk34_rCoreHi86 rCore).DisjointWires (mk34_rSubBOfScr B hmScr rScr) :=
    (hCS.compose_left _).compose_right _
  have h2 : (mk34_rCoreLo3 rCore).DisjointWires (mk34_rSubBOfScr B hmScr rScr) :=
    (hCS.compose_left _).compose_right _
  have h3 := mk34_rSub23OfScr_disjoint_rSubBOfScr B hmScr rScr
  refine QRegister.disjoint_iff.mpr fun a b heq ↦
    Fin.addCases (m := 89) (n := 23)
      (motive := fun a ↦
        mk34_rComb112Direct rCore (mk34_rSub23OfScr B hmScr rScr) (hCS.compose_right _) a =
          mk34_rSubBOfScr B hmScr rScr b → False)
      (fun i hi ↦ ?_)
      (fun j hj ↦ h3.ne j b
        ((mk34_rComb112Direct_sub23 rCore (mk34_rSub23OfScr B hmScr rScr)
          (hCS.compose_right _) j).symm.trans hj))
      a heq
  dsimp only [mk34_rComb112Direct] at hi
  rw [QRegister.concat_apply_left] at hi
  exact Fin.addCases (m := 86) (n := 3)
    (motive := fun i ↦
      ((mk34_rCoreHi86 rCore).concat (mk34_rCoreLo3 rCore)
        (mk34_rCoreHi86_disjoint_rCoreLo3 rCore)) i =
        mk34_rSubBOfScr B hmScr rScr b → False)
    (fun i₀ hi₀ ↦ h1.ne i₀ b ((QRegister.concat_apply_left _ _ _ i₀).symm.trans hi₀))
    (fun j₀ hj₀ ↦ h2.ne j₀ b ((QRegister.concat_apply_right _ _ _ j₀).symm.trans hj₀))
    i hi
theorem mk34_rComb112Direct_disjoint_rOutTop {n mScr : ℕ} (B : ℕ) (hmScr : B + 27 ≤ mScr)
    (rCore : QRegister posCoreWires n) (rOutTop : QRegister (B + 1) n) (rScr : QRegister mScr n)
    (hCOut : rCore.DisjointWires rOutTop) (hCS : rCore.DisjointWires rScr)
    (hOutS : rOutTop.DisjointWires rScr) :
    (mk34_rComb112Direct rCore (mk34_rSub23OfScr B hmScr rScr) (hCS.compose_right _)).DisjointWires
      rOutTop := by
  have h1 : (mk34_rCoreHi86 rCore).DisjointWires rOutTop := hCOut.compose_left _
  have h2 : (mk34_rCoreLo3 rCore).DisjointWires rOutTop := hCOut.compose_left _
  have h3 : (mk34_rSub23OfScr B hmScr rScr).DisjointWires rOutTop :=
    (QRegExt.disjointWires_symm (hOutS.compose_right _))
  refine QRegister.disjoint_iff.mpr fun a b heq ↦
    Fin.addCases (m := 89) (n := 23)
      (motive := fun a ↦
        mk34_rComb112Direct rCore (mk34_rSub23OfScr B hmScr rScr) (hCS.compose_right _) a =
          rOutTop b → False)
      (fun i hi ↦ ?_)
      (fun j hj ↦ h3.ne j b
        ((mk34_rComb112Direct_sub23 rCore (mk34_rSub23OfScr B hmScr rScr)
          (hCS.compose_right _) j).symm.trans hj))
      a heq
  dsimp only [mk34_rComb112Direct] at hi
  rw [QRegister.concat_apply_left] at hi
  exact Fin.addCases (m := 86) (n := 3)
    (motive := fun i ↦
      ((mk34_rCoreHi86 rCore).concat (mk34_rCoreLo3 rCore)
        (mk34_rCoreHi86_disjoint_rCoreLo3 rCore)) i =
        rOutTop b → False)
    (fun i₀ hi₀ ↦ h1.ne i₀ b ((QRegister.concat_apply_left _ _ _ i₀).symm.trans hi₀))
    (fun j₀ hj₀ ↦ h2.ne j₀ b ((QRegister.concat_apply_right _ _ _ j₀).symm.trans hj₀))
    i hi
/-- Maps a `112`-wire outer bit assignment `γ` and ambient `β` to the `(mk34_mB B)`-wire input
of `mk34_ctxMidB`. -/
def mk34_map112ToMB {n : ℕ} (B : ℕ)
    (rOutTop : QRegister (B + 1) n) (rSubB : QRegister (B + 4) n)
    (γ : BitAssignment 112) (β : BitAssignment n) : BitAssignment (mk34_mB B) :=
  fun idx ↦
    if h1 : idx.val < 86 then γ ⟨idx.val, by omega⟩
    else if idx.val = 86 then γ ⟨106, by decide⟩
    else if idx.val = 87 then γ ⟨110, by decide⟩
    else if idx.val = 88 then γ ⟨111, by decide⟩
    else if h2 : idx.val < 89 + (B + 1) then β (rOutTop ⟨idx.val - 89, by omega⟩)
    else β (rSubB ⟨idx.val - (89 + (B + 1)), by
      have hlt := idx.isLt; dsimp [mk34_mB] at hlt; omega⟩)
theorem mk34_map112ToMB_writeRegProg {n mScr : ℕ} (B : ℕ) (hmScr : B + 27 ≤ mScr)
    (rCore : QRegister posCoreWires n) (rOutTop : QRegister (B + 1) n) (rScr : QRegister mScr n)
    (hCOut : rCore.DisjointWires rOutTop) (hCS : rCore.DisjointWires rScr)
    (hOutS : rOutTop.DisjointWires rScr)
    (γ γ' : BitAssignment 112) (β : BitAssignment n) :
    let rComb112 := mk34_rComb112Direct rCore (mk34_rSub23OfScr B hmScr rScr) (hCS.compose_right _)
    let rSubB := mk34_rSubBOfScr B hmScr rScr
    mk34_map112ToMB B rOutTop rSubB γ (writeRegProg β rComb112 γ') =
      mk34_map112ToMB B rOutTop rSubB γ β := by
  intro rComb112 rSubB
  have hDisjOut := mk34_rComb112Direct_disjoint_rOutTop B hmScr rCore rOutTop rScr hCOut hCS hOutS
  have hDisjSub := mk34_rComb112Direct_disjoint_rSubBOfScr B hmScr rCore rScr hCS
  funext idx
  dsimp only [mk34_map112ToMB]
  split_ifs with h1 h2 h3 h4 h5
  · rfl
  · rfl
  · rfl
  · rfl
  · exact mk34_writeRegProg_leafScr_eq rComb112 rOutTop hDisjOut β γ' _
  · exact mk34_writeRegProg_leafScr_eq rComb112 rSubB hDisjSub β γ' _
theorem mk34_map112ToMB_eq_rCombBDirect {n mScr : ℕ} (B : ℕ) (hmScr : B + 27 ≤ mScr)
    (rCore : QRegister posCoreWires n) (rOutTop : QRegister (B + 1) n) (rScr : QRegister mScr n)
    (hCOut : rCore.DisjointWires rOutTop) (hCS : rCore.DisjointWires rScr)
    (hOutS : rOutTop.DisjointWires rScr) (β : BitAssignment n) :
    let rSub23 := mk34_rSub23OfScr B hmScr rScr
    let rSubB := mk34_rSubBOfScr B hmScr rScr
    let rComb112 := mk34_rComb112Direct rCore rSub23 (hCS.compose_right _)
    let rHold3 := mk34_rHold3FromSub23 rSub23
    let rCombB := mk34_rCombBDirect B rCore rHold3 rOutTop rSubB
        (mk34_rCoreHi86_disjoint_rHold3FromSub23 B hmScr rCore rScr hCS)
        (hCOut.compose_left _)
        (mk34_rHold3FromSub23_disjoint_rOutTop B hmScr rOutTop rScr hOutS)
        ((hCS.compose_left _).compose_right _)
        (mk34_rHold3FromSub23_disjoint_rSubBOfScr B hmScr rScr) (hOutS.compose_right _)
    mk34_map112ToMB B rOutTop rSubB (fun idx ↦ β (rComb112 idx)) β =
      (fun idx ↦ β (rCombB idx)) := by
  intro rSub23 rSubB rComb112 rHold3 rCombB
  funext idx
  dsimp only [mk34_map112ToMB]
  by_cases h1 : idx.val < 86
  · rw [dite_eq_left h1]
    have hidx : idx = ⟨(⟨idx.val, h1⟩ : Fin 86).val, by dsimp [mk34_mB]; omega⟩ := Fin.ext rfl
    rw [mk34_rComb112Direct_core rCore rSub23 (hCS.compose_right _) ⟨idx.val, h1⟩]
    conv_rhs => rw [hidx]
    exact congrArg β (mk34_rCombBDirect_core B rCore rHold3 rOutTop rSubB _ _ _ _ _ _ ⟨idx.val,
      h1⟩).symm
  · rw [dite_eq_right h1]
    by_cases h86 : idx.val = 86
    · rw [ite_eq_left h86]
      have h106 : (⟨106, by decide⟩ : Fin 112) = ⟨89 + (⟨17, by decide⟩ : Fin 23).val, by omega⟩ :=
        rfl
      have hidx : idx = ⟨86 + (0 : Fin 3).val, by dsimp [mk34_mB]; omega⟩ := Fin.ext h86
      rw [h106, mk34_rComb112Direct_sub23 rCore rSub23 (hCS.compose_right _) ⟨17, by decide⟩,
          hidx, mk34_rCombBDirect_hold B rCore rHold3 rOutTop rSubB _ _ _ _ _ _ 0]
      rfl
    · rw [ite_eq_right h86]
      by_cases h87 : idx.val = 87
      · rw [ite_eq_left h87]
        have h110 : (⟨110, by decide⟩ : Fin 112) = ⟨89 + (⟨21, by decide⟩ : Fin 23).val,
          by omega⟩ := rfl
        have hidx : idx = ⟨86 + (1 : Fin 3).val, by dsimp [mk34_mB]; omega⟩ := Fin.ext h87
        rw [h110, mk34_rComb112Direct_sub23 rCore rSub23 (hCS.compose_right _) ⟨21, by decide⟩,
            hidx, mk34_rCombBDirect_hold B rCore rHold3 rOutTop rSubB _ _ _ _ _ _ 1]
        rfl
      · rw [ite_eq_right h87]
        by_cases h88 : idx.val = 88
        · rw [ite_eq_left h88]
          have h111 : (⟨111, by decide⟩ : Fin 112) = ⟨89 + (⟨22, by decide⟩ : Fin 23).val,
            by omega⟩ := rfl
          have hidx : idx = ⟨86 + (2 : Fin 3).val, by dsimp [mk34_mB]; omega⟩ := Fin.ext h88
          rw [h111, mk34_rComb112Direct_sub23 rCore rSub23 (hCS.compose_right _) ⟨22, by decide⟩,
              hidx, mk34_rCombBDirect_hold B rCore rHold3 rOutTop rSubB _ _ _ _ _ _ 2]
          rfl
        · rw [ite_eq_right h88]
          by_cases hOut : idx.val < 89 + (B + 1)
          · rw [dite_eq_left hOut]
            let jOut : Fin (B + 1) := ⟨idx.val - 89, by omega⟩
            have hidx : idx = ⟨89 + jOut.val, by dsimp [mk34_mB]; omega⟩ :=
              Fin.ext (by dsimp [jOut]; omega)
            conv_rhs => rw [hidx]
            exact congrArg β (mk34_rCombBDirect_out B rCore rHold3 rOutTop rSubB _ _ _ _ _ _
              jOut).symm
          · rw [dite_eq_right hOut]
            have hlt := idx.isLt
            dsimp [mk34_mB] at hlt
            let j : Fin (B + 4) := ⟨idx.val - (89 + (B + 1)), by omega⟩
            have hidx : rCombB idx = tailScr rCombB (B + 4) (by dsimp [mk34_mB]; omega) j := by
              dsimp only [tailScr, j]
              congr 1; ext; dsimp [mk34_mB]; omega
            rw [hidx, congrFun (mk34_tailScr_rCombBDirect B rCore rHold3 rOutTop rSubB _ _ _ _ _ _)
              j]
/-- Single-stage `(B + 27)`-clean-wire reversible `Circuit n` for the mid-phase kickback. -/
def cKickZeroSubSingle {n mScr : ℕ} (B : ℕ) (hB1 : 1 ≤ B) (hB27 : B ≤ 27)
    (hmScr : B + 27 ≤ mScr) (rCore : QRegister posCoreWires n) (rOutTop : QRegister (B + 1) n)
    (rScr : QRegister mScr n) (hCOut : rCore.DisjointWires rOutTop)
    (hCS : rCore.DisjointWires rScr) (hOutS : rOutTop.DisjointWires rScr) : Circuit n :=
  let rSub23 := mk34_rSub23OfScr B hmScr rScr
  let rSubB := mk34_rSubBOfScr B hmScr rScr
  let rComb112 := mk34_rComb112Direct rCore rSub23 (hCS.compose_right _)
  let rHold3 := mk34_rHold3FromSub23 rSub23
  let cLeaf := mk34_cMidKickBDirect B hB1 hB27 rCore rHold3 rOutTop rSubB
      (mk34_rCoreHi86_disjoint_rHold3FromSub23 B hmScr rCore rScr hCS) (hCOut.compose_left _)
      (mk34_rHold3FromSub23_disjoint_rOutTop B hmScr rOutTop rScr hOutS)
      ((hCS.compose_left _).compose_right _)
      (mk34_rHold3FromSub23_disjoint_rSubBOfScr B hmScr rScr) (hOutS.compose_right _)
  mk34_ctxToToff rComb112 cLeaf mk34_ctxComp23
/-- Single-stage `(B + 27)`-clean-wire `0`-`.TOFF` `DynamicCircuit Var n` (`104 + 4 * B` `T`). -/
def dKickZeroSubSingleDyn {Var : Type} {n mScr : ℕ}
    (B : ℕ) (hB1 : 1 ≤ B) (hB27 : B ≤ 27) (hmScr : B + 27 ≤ mScr) (v : Var)
    (rCore : QRegister posCoreWires n) (rOutTop : QRegister (B + 1) n) (rScr : QRegister mScr n)
    (hCOut : rCore.DisjointWires rOutTop) (hCS : rCore.DisjointWires rScr)
    (hOutS : rOutTop.DisjointWires rScr) : DynamicCircuit Var n :=
  let rSub23 := mk34_rSub23OfScr B hmScr rScr
  let rSubB := mk34_rSubBOfScr B hmScr rScr
  let rComb112 := mk34_rComb112Direct rCore rSub23 (hCS.compose_right _)
  let rHold3 := mk34_rHold3FromSub23 rSub23
  let dLeaf := mk34_dMidKickBDirect B hB1 hB27 v rCore rHold3 rOutTop rSubB
      (mk34_rCoreHi86_disjoint_rHold3FromSub23 B hmScr rCore rScr hCS) (hCOut.compose_left _)
      (mk34_rHold3FromSub23_disjoint_rOutTop B hmScr rOutTop rScr hOutS)
      ((hCS.compose_left _).compose_right _)
      (mk34_rHold3FromSub23_disjoint_rSubBOfScr B hmScr rScr) (hOutS.compose_right _)
  mk34_ctxToDynNested v rComb112 dLeaf mk34_ctxComp23
@[scoped simp] theorem count_dKickZeroSubSingleDyn_toff {Var : Type} {n mScr : ℕ}
    (B : ℕ) (hB1 : 1 ≤ B) (hB27 : B ≤ 27) (hmScr : B + 27 ≤ mScr) (v : Var)
    (rCore : QRegister posCoreWires n) (rOutTop : QRegister (B + 1) n) (rScr : QRegister mScr n)
    (hCOut : rCore.DisjointWires rOutTop) (hCS : rCore.DisjointWires rScr)
    (hOutS : rOutTop.DisjointWires rScr) :
    (dKickZeroSubSingleDyn B hB1 hB27 hmScr v rCore rOutTop rScr hCOut hCS hOutS).count
      PrimitiveGate.TOFF = 0 := by
  simp [dKickZeroSubSingleDyn, mk34_ctxToDynNested_count_toff, mk34_count_dMidKickBDirect_toff]
@[scoped simp] theorem count_dKickZeroSubSingleDyn_t {Var : Type} {n mScr : ℕ}
    (B : ℕ) (hB1 : 1 ≤ B) (hB27 : B ≤ 27) (hmScr : B + 27 ≤ mScr) (v : Var)
    (rCore : QRegister posCoreWires n) (rOutTop : QRegister (B + 1) n) (rScr : QRegister mScr n)
    (hCOut : rCore.DisjointWires rOutTop) (hCS : rCore.DisjointWires rScr)
    (hOutS : rOutTop.DisjointWires rScr) :
    (dKickZeroSubSingleDyn B hB1 hB27 hmScr v rCore rOutTop rScr hCOut hCS hOutS).count
      PrimitiveGate.T = 104 + 4 * B := by
  simp only [dKickZeroSubSingleDyn, mk34_ctxToDynNested_count_t, mk34_ctxComp23_countTempAnd,
    mk34_count_dMidKickBDirect_t]
  ring
theorem dKickZeroSubSingleDyn_preservesStoreConst {Var : Type} [Fintype Var] [DecidableEq Var]
    {n mScr : ℕ} (B : ℕ) (hB1 : 1 ≤ B) (hB27 : B ≤ 27) (hmScr : B + 27 ≤ mScr) (v : Var)
    (rCore : QRegister posCoreWires n) (rOutTop : QRegister (B + 1) n)
    (rScr : QRegister mScr n) (hCOut : rCore.DisjointWires rOutTop)
    (hCS : rCore.DisjointWires rScr) (hOutS : rOutTop.DisjointWires rScr) :
    PreservesStoreConst (dKickZeroSubSingleDyn B hB1 hB27 hmScr v rCore rOutTop rScr hCOut hCS
    hOutS) := mk34_ctxToDynNested_preservesStoreConst v _ _
    (mk34_dMidKickBDirect_preservesStoreConst B hB1 hB27 v _ _ _ _ _ _ _ _ _ _) mk34_ctxComp23
theorem mk34_projZeroAll_tailScr_single_scr {n mScr : ℕ}
    (B : ℕ) (hmScr : B + 27 ≤ mScr)
    (rCore : QRegister posCoreWires n) (rScr : QRegister mScr n)
    (hCS : rCore.DisjointWires rScr) :
    let rComb112 := mk34_rComb112Direct rCore (mk34_rSub23OfScr B hmScr rScr) (hCS.compose_right _)
    let rSubB := mk34_rSubBOfScr B hmScr rScr
    let hDisj := mk34_rComb112Direct_disjoint_rSubBOfScr B hmScr rCore rScr hCS
    projZeroAll (23 + (B + 4))
        (tailScr (rComb112.concat rSubB hDisj) (23 + (B + 4)) (by omega)) *
      projZeroAll mScr rScr.wires =
      projZeroAll mScr rScr.wires := by
  intro rComb112 rSubB hDisj
  apply MeasureBranchHadamardSem.matrix_ext_ket
  intro β
  rw [mul_mulVec_prog, ket_projZeroAll]
  by_cases hz : ∀ s : Fin mScr, β (rScr s) = 0
  · rw [ite_eq_left hz, ket_projZeroAll, ite_eq_left]
    rw [mk34_tailScr_concat_split rComb112 rSubB hDisj 23 (by decide) β]
    refine ⟨fun w hw ↦ ?_, fun j ↦ ?_⟩
    · have hwEq := mk34_rComb112Direct_sub23 rCore (mk34_rSub23OfScr B hmScr rScr)
        (hCS.compose_right _) ⟨w.val - 89, by omega⟩
      have hfin : (⟨89 + (w.val - 89), by omega⟩ : Wire 112) = w := Fin.ext (by dsimp; omega)
      rw [hfin] at hwEq
      change β (rComb112 w) = 0
      rw [hwEq]
      dsimp only [mk34_rSub23OfScr]; rw [QRegister.slice_apply]
      exact hz ⟨0 + (w.val - 89), by omega⟩
    · dsimp only [rSubB, mk34_rSubBOfScr]; rw [QRegister.slice_apply]
      exact hz ⟨23 + j.val, by omega⟩
  · rw [ite_eq_right hz, Matrix.mulVec_zero]
theorem realizesCleanUnitary_dKickZeroSubSingleDyn_scr
    {Var : Type} [Fintype Var] [DecidableEq Var] {n mScr : ℕ} [NeZero (2 ^ n)]
    (B : ℕ) (hB1 : 1 ≤ B) (hB27 : B ≤ 27) (hmScr : B + 27 ≤ mScr) (v : Var)
    (rCore : QRegister posCoreWires n) (rOutTop : QRegister (B + 1) n) (rScr : QRegister mScr n)
    (hCOut : rCore.DisjointWires rOutTop) (hCS : rCore.DisjointWires rScr)
    (hOutS : rOutTop.DisjointWires rScr) :
    RealizesCleanUnitary v (projZeroAll mScr rScr.wires)
      (dKickZeroSubSingleDyn B hB1 hB27 hmScr v rCore rOutTop rScr hCOut hCS hOutS)
      (cKickZeroSubSingle B hB1 hB27 hmScr rCore rOutTop rScr hCOut hCS hOutS).eval := by
  let rSub23 := mk34_rSub23OfScr B hmScr rScr
  let rSubB := mk34_rSubBOfScr B hmScr rScr
  let rComb112 := mk34_rComb112Direct rCore rSub23 (hCS.compose_right _)
  let rHold3 := mk34_rHold3FromSub23 rSub23
  let hDisj := mk34_rComb112Direct_disjoint_rSubBOfScr B hmScr rCore rScr hCS
  let fLeaf : BitAssignment 112 → BitAssignment n → ZMod 2 := fun γ β ↦
    mk34_fLeafMidB B ((mk34_ctxMidB B hB1 hB27).fwdBits (mk34_map112ToMB B rOutTop rSubB γ β))
  have hfLeaf : ∀ (γ γ' : BitAssignment 112) (β : BitAssignment n),
      fLeaf γ (writeRegProg β rComb112 γ') = fLeaf γ β := fun γ γ' β ↦ by
    dsimp only [fLeaf]
    rw [mk34_map112ToMB_writeRegProg B hmScr rCore rOutTop rScr hCOut hCS hOutS γ γ' β]
  have hLeafKet : ∀ β : BitAssignment n,
      (∀ j : Fin (B + 4), β (rSubB j) = 0) →
      (mk34_cMidKickBDirect B hB1 hB27 rCore rHold3 rOutTop rSubB
        (mk34_rCoreHi86_disjoint_rHold3FromSub23 B hmScr rCore rScr hCS)
        (hCOut.compose_left _)
        (mk34_rHold3FromSub23_disjoint_rOutTop B hmScr rOutTop rScr hOutS)
        ((hCS.compose_left _).compose_right _)
        (mk34_rHold3FromSub23_disjoint_rSubBOfScr B hmScr rScr)
        (hOutS.compose_right _)).eval.1.mulVec (MeasureBranchHadamardSem.ket β) =
      ((-1 : ℂ) ^ (fLeaf (fun idx ↦ β (rComb112 idx)) β).val) •
        MeasureBranchHadamardSem.ket β := fun β hSubB ↦ by
    rw [mbh_ket_eq_ket,
        mk34_cMidKickBDirect_eval_ket_raw B hB1 hB27 rCore rHold3 rOutTop rSubB _ _ _ _ _ _ β hSubB]
    dsimp only [fLeaf]
    rw [mk34_map112ToMB_eq_rCombBDirect B hmScr rCore rOutTop rScr hCOut hCS hOutS β]
  have hLeafReal := mk34_realizesCleanUnitary_dMidKickBDirect B hB1 hB27 v rCore rHold3
      rOutTop rSubB (mk34_rCoreHi86_disjoint_rHold3FromSub23 B hmScr rCore rScr hCS)
      (hCOut.compose_left _)
      (mk34_rHold3FromSub23_disjoint_rOutTop B hmScr rOutTop rScr hOutS)
      ((hCS.compose_left _).compose_right _)
      (mk34_rHold3FromSub23_disjoint_rSubBOfScr B hmScr rScr) (hOutS.compose_right _)
  have hpv : ValidCleanRem 112 23 (mk34_ctxComp23.plug (.z ⟨0, by decide⟩)) := by
    rw [mk34_pComp23_eq]
    exact mk34_pComp23_valid_and_bits.1
  have hNested := mk34_realizesCleanUnitary_ctxToDynNested v rComb112 rSubB hDisj
    _ _ fLeaf hfLeaf hLeafKet hLeafReal ⟨0, by decide⟩ mk34_ctxComp23 23 (by decide) hpv
  exact RealizesCleanUnitary.mono_proj (projZeroAll_conjTranspose (23 + (B + 4)) _)
    (projZeroAll_conjTranspose mScr _)
    (mk34_projZeroAll_tailScr_single_scr B hmScr rCore rScr hCS) hNested
theorem cKickZeroSubSingle_eval_mulVec_ket {n mScr : ℕ} (B : ℕ) (hB1 : 1 ≤ B) (hB27 : B ≤ 27)
    (hmScr : B + 27 ≤ mScr) (rCore : QRegister posCoreWires n) (rOutTop : QRegister (B + 1) n)
    (rScr : QRegister mScr n) (hCOut : rCore.DisjointWires rOutTop)
    (hCS : rCore.DisjointWires rScr) (hOutS : rOutTop.DisjointWires rScr)
    (δ : BitAssignment n) (hScr0 : ∀ s : Fin mScr, δ (rScr s) = 0) : (cKickZeroSubSingle B hB1
    hB27 hmScr rCore rOutTop rScr hCOut hCS hOutS).eval.1.mulVec (ket δ) =
    ((-1 : ℂ) ^ (midKickPhaseBitB B rCore rOutTop δ).val) • ket δ := by
  let rSub23 := mk34_rSub23OfScr B hmScr rScr
  let rSubB := mk34_rSubBOfScr B hmScr rScr
  let rComb112 := mk34_rComb112Direct rCore rSub23 (hCS.compose_right _)
  let rHold3 := mk34_rHold3FromSub23 rSub23
  let hDisj := mk34_rComb112Direct_disjoint_rSubBOfScr B hmScr rCore rScr hCS
  let fLeaf : BitAssignment 112 → BitAssignment n → ZMod 2 := fun γ β ↦
    mk34_fLeafMidB B ((mk34_ctxMidB B hB1 hB27).fwdBits (mk34_map112ToMB B rOutTop rSubB γ β))
  have hfLeaf : ∀ (γ γ' : BitAssignment 112) (β : BitAssignment n),
      fLeaf γ (writeRegProg β rComb112 γ') = fLeaf γ β := fun γ γ' β ↦ by
    dsimp only [fLeaf]
    rw [mk34_map112ToMB_writeRegProg B hmScr rCore rOutTop rScr hCOut hCS hOutS γ γ' β]
  have hLeafKet : ∀ β : BitAssignment n,
      (∀ j : Fin (B + 4), β (rSubB j) = 0) →
      (mk34_cMidKickBDirect B hB1 hB27 rCore rHold3 rOutTop rSubB
        (mk34_rCoreHi86_disjoint_rHold3FromSub23 B hmScr rCore rScr hCS)
        (hCOut.compose_left _)
        (mk34_rHold3FromSub23_disjoint_rOutTop B hmScr rOutTop rScr hOutS)
        ((hCS.compose_left _).compose_right _)
        (mk34_rHold3FromSub23_disjoint_rSubBOfScr B hmScr rScr)
        (hOutS.compose_right _)).eval.1.mulVec (MeasureBranchHadamardSem.ket β) =
      ((-1 : ℂ) ^ (fLeaf (fun idx ↦ β (rComb112 idx)) β).val) •
        MeasureBranchHadamardSem.ket β := fun β hSubB ↦ by
    rw [mbh_ket_eq_ket,
        mk34_cMidKickBDirect_eval_ket_raw B hB1 hB27 rCore rHold3 rOutTop rSubB _ _ _ _ _ _ β hSubB]
    dsimp only [fLeaf]
    rw [mk34_map112ToMB_eq_rCombBDirect B hmScr rCore rOutTop rScr hCOut hCS hOutS β]
  have hSubB0 : ∀ j : Fin (B + 4), δ (rSubB j) = 0 := fun j ↦ by
    dsimp only [rSubB, mk34_rSubBOfScr]; rw [QRegister.slice_apply]
    exact hScr0 ⟨23 + j.val, by omega⟩
  let γ : BitAssignment 112 := fun idx ↦ δ (rComb112 idx)
  have hcr : cleanRem 112 23 γ := fun w hw ↦ by
    have hwEq := mk34_rComb112Direct_sub23 rCore rSub23 (hCS.compose_right _) ⟨w.val - 89, by omega⟩
    have hfin : (⟨89 + (w.val - 89), by omega⟩ : Wire 112) = w := Fin.ext (by dsimp; omega)
    rw [hfin] at hwEq
    change δ (rComb112 w) = 0
    rw [hwEq]
    dsimp only [rSub23, mk34_rSub23OfScr]; rw [QRegister.slice_apply]
    exact hScr0 ⟨0 + (w.val - 89), by omega⟩
  rw [cKickZeroSubSingle, ← mbh_ket_eq_ket,
      mk34_ctxToToff_eval_ket_of_leafScr rComb112 rSubB hDisj _ fLeaf hfLeaf hLeafKet
        ⟨0, by decide⟩ mk34_ctxComp23 δ hSubB0,
      mk34_pComp23_eq, mk34_pComp23_valid_and_bits.2 γ hcr,
      mk34_writeRegProg_self, mbh_ket_eq_ket]
  congr 3
  dsimp only [fLeaf]
  let γB := mk34_map112ToMB B rOutTop rSubB (mk34_ctxComp23.fwdBits γ) δ
  have hcrB : cleanRem (mk34_mB B) (B + 4) γB := fun w hw ↦ by
    dsimp only [γB, mk34_map112ToMB]
    have h1 : ¬ (w.val < 86) := by dsimp [mk34_mB] at hw; omega
    have h2 : w.val ≠ 86 := by dsimp [mk34_mB] at hw; omega
    have h3 : w.val ≠ 87 := by dsimp [mk34_mB] at hw; omega
    have h4 : w.val ≠ 88 := by dsimp [mk34_mB] at hw; omega
    have h5 : ¬ (w.val < 89 + (B + 1)) := by dsimp [mk34_mB] at hw; omega
    simp only [h1, h2, h3, h4, h5, ↓reduceDIte, ↓reduceIte]
    exact hSubB0 _
  have hc (k : Fin 86) : γ ⟨k.val, by omega⟩ =
      δ (rCore ⟨3948 + k.val, by dsimp [posCoreWires]; omega⟩) :=
    congrArg δ (mk34_rComb112Direct_core rCore rSub23 (hCS.compose_right _) k)
  have hcB (k : Fin 86) : γB ⟨k.val, by dsimp [mk34_mB]; omega⟩ =
      δ (rCore ⟨3948 + k.val, by dsimp [posCoreWires]; omega⟩) := by
    dsimp only [γB, mk34_map112ToMB]
    rw [dite_eq_left k.isLt, mk34_ctxComp23_fwdBits_below γ ⟨k.val, by omega⟩ (by dsimp; omega)]
    exact hc k
  obtain ⟨_, he106, hw106⟩ := mk34_ctxComp23_fwdBits_wire ⟨106, by decide⟩ γ hcr
  obtain ⟨_, he110, hw110⟩ := mk34_ctxComp23_fwdBits_wire ⟨110, by decide⟩ γ hcr
  obtain ⟨_, he111, hw111⟩ := mk34_ctxComp23_fwdBits_wire ⟨111, by decide⟩ γ hcr
  let ge216 := ge216Bit (δ (rCore ⟨3963, by decide⟩)) (δ (rCore ⟨3964, by decide⟩))
    (δ (rCore ⟨3965, by decide⟩)) (δ (rCore ⟨3966, by decide⟩)) (δ (rCore ⟨3967, by decide⟩))
  let ge218 := ge218Bit (δ (rCore ⟨3969, by decide⟩)) (δ (rCore ⟨3970, by decide⟩))
    (δ (rCore ⟨3971, by decide⟩)) (δ (rCore ⟨3972, by decide⟩)) (δ (rCore ⟨3973, by decide⟩))
    (δ (rCore ⟨3974, by decide⟩)) (δ (rCore ⟨3975, by decide⟩))
  let ge217 := ge217Bit (δ (rCore ⟨3976, by decide⟩)) (δ (rCore ⟨3977, by decide⟩))
    (δ (rCore ⟨3978, by decide⟩)) (δ (rCore ⟨3979, by decide⟩)) (δ (rCore ⟨3980, by decide⟩))
    (δ (rCore ⟨3981, by decide⟩)) (δ (rCore ⟨3982, by decide⟩)) (δ (rCore ⟨3983, by decide⟩))
  have hu1 : γB ⟨86, by dsimp [mk34_mB]; omega⟩ =
      (1 + γB ⟨2, by dsimp [mk34_mB]; omega⟩) * (1 + δ (rCore ⟨3949, by decide⟩)) := by
    have h86 : γB ⟨86, by dsimp [mk34_mB]; omega⟩ = mk34_ctxComp23.fwdBits γ ⟨106, by decide⟩ := by
      dsimp only [γB, mk34_map112ToMB]; simp
    rw [h86, he106.trans hw106.2.2.2.1, hcB ⟨2, by decide⟩, hc ⟨2, by decide⟩, hc ⟨1, by decide⟩]
    rfl
  have hvL : γB ⟨87, by dsimp [mk34_mB]; omega⟩ =
      ((1 + γB ⟨2, by dsimp [mk34_mB]; omega⟩) * (1 + δ (rCore ⟨3949, by decide⟩))) *
        (((1 + δ (rCore ⟨4016, by decide⟩)) * (1 + ge218)) *
          (1 + (1 + γB ⟨0, by dsimp [mk34_mB]; omega⟩) * ge216)) := by
    have h87 : γB ⟨87, by dsimp [mk34_mB]; omega⟩ = mk34_ctxComp23.fwdBits γ ⟨110, by decide⟩ := by
      dsimp only [γB, mk34_map112ToMB]; simp
    rw [h87, he110.trans hw110.2.2.2.2.1, hcB ⟨2, by decide⟩, hcB ⟨0, by decide⟩,
        hc ⟨2, by decide⟩, hc ⟨1, by decide⟩, hc ⟨0, by decide⟩, hc ⟨68, by decide⟩,
        hc ⟨15, by decide⟩, hc ⟨16, by decide⟩, hc ⟨17, by decide⟩, hc ⟨18, by decide⟩,
        hc ⟨19, by decide⟩,
        hc ⟨21, by decide⟩, hc ⟨22, by decide⟩, hc ⟨23, by decide⟩, hc ⟨24, by decide⟩,
        hc ⟨25, by decide⟩, hc ⟨26, by decide⟩, hc ⟨27, by decide⟩]
    rfl
  have hd3 : γB ⟨88, by dsimp [mk34_mB]; omega⟩ =
      γB ⟨0, by dsimp [mk34_mB]; omega⟩ * ge217 := by
    have h88 : γB ⟨88, by dsimp [mk34_mB]; omega⟩ = mk34_ctxComp23.fwdBits γ ⟨111, by decide⟩ := by
      dsimp only [γB, mk34_map112ToMB]; simp
    rw [h88, he111.trans hw111.2.2.2.2.2, hcB ⟨0, by decide⟩, hc ⟨0, by decide⟩,
        hc ⟨28, by decide⟩, hc ⟨29, by decide⟩, hc ⟨30, by decide⟩, hc ⟨31, by decide⟩,
        hc ⟨32, by decide⟩, hc ⟨33, by decide⟩, hc ⟨34, by decide⟩, hc ⟨35, by decide⟩]
    rfl
  have hKeep : (fun k : Fin 30 ↦ γB ⟨38 + k.val, by dsimp [mk34_mB]; omega⟩) =
      (fun k : Fin 30 ↦ δ (rCore ⟨3986 + k.val, by dsimp [posCoreWires]; omega⟩)) :=
    funext fun k ↦ (hcB ⟨38 + k.val, by omega⟩).trans
      (congrArg (fun idx ↦ δ (rCore idx)) (Fin.ext (by dsimp; omega)))
  have hOut : (fun j : Fin B ↦ γB ⟨89 + j.val, by dsimp [mk34_mB]; omega⟩) =
      (fun j : Fin B ↦ δ (rOutTop ⟨j.val, by omega⟩)) := by
    funext j
    dsimp only [γB, mk34_map112ToMB]
    have h1 : ¬ (89 + j.val < 86) := by omega
    have h2 : 89 + j.val ≠ 86 := by omega
    have h3 : 89 + j.val ≠ 87 := by omega
    have h4 : 89 + j.val ≠ 88 := by omega
    have h5 : 89 + j.val < 89 + (B + 1) := by omega
    simp only [h1, h2, h3, h4, h5, ↓reduceDIte, ↓reduceIte]
    exact congrArg (fun idx ↦ δ (rOutTop idx)) (Fin.ext (by dsimp; omega))
  have hSign : γB ⟨89 + B, by dsimp [mk34_mB]; omega⟩ = δ (rOutTop ⟨B, by omega⟩) := by
    dsimp only [γB, mk34_map112ToMB]
    have h1 : ¬ (89 + B < 86) := by omega
    have h2 : 89 + B ≠ 86 := by omega
    have h3 : 89 + B ≠ 87 := by omega
    have h4 : 89 + B ≠ 88 := by omega
    have h5 : 89 + B < 89 + (B + 1) := by omega
    simp only [h1, h2, h3, h4, h5, ↓reduceDIte, ↓reduceIte]
    exact congrArg (fun idx ↦ δ (rOutTop idx)) (Fin.ext (by dsimp; omega))
  change mk34_fLeafMidB B ((mk34_ctxMidB B hB1 hB27).fwdBits γB) = _
  rw [mk34_ctxMidB_fwdBits_fLeaf B hB1 hB27 γB hcrB
        (δ (rCore ⟨3949, by decide⟩)) (δ (rCore ⟨4016, by decide⟩))
        ge216 ge218 ge217 hu1 hvL hd3,
      hcB ⟨2, by decide⟩, hcB ⟨0, by decide⟩, hcB ⟨36, by decide⟩, hcB ⟨85, by decide⟩,
      hKeep, hOut, hSign]
  rfl
/-!
## Section 3: In-Place `prev0` `(B + 3)`-Wire Inner Mid-Kick (`mk34_dMidKickBInPlace`)
-/
/-- In-place Stage-B context on `mk34_mB B` wires requiring only `B + 3` clean wires (`90 + B + 1
..`),
where wire `90 + B` already holds `keep[29 - B]` and is flipped in place by `.x ⟨90 + B, _⟩`. -/
def mk34_ctxMidBInPlace (B : ℕ) (_hB1 : 1 ≤ B) (_hB27 : B ≤ 27) : TempCtx (mk34_mB B) :=
  (ctxCliffAlloc (.x ⟨90 + B, by dsimp [mk34_mB]; omega⟩)).append <|
  (mk34_ctxLtCompLoop B (90 + B) (by dsimp [mk34_mB]; omega)
    (fun j ↦ ⟨38 + (30 - B) + j.val, by dsimp [mk34_mB]; omega⟩)
    (fun j ↦ ⟨89 + j.val, by dsimp [mk34_mB]; omega⟩)
    (fun j ↦ wire_ne_of_lt (by dsimp; omega))
    (fun j ↦ by dsimp; omega)
    (fun j ↦ by dsimp; omega)).append <|
  mk34_ctxTail3 B
@[scoped simp]
theorem mk34_ctxMidBInPlace_countTempAnd (B : ℕ) (hB1 : 1 ≤ B) (hB27 : B ≤ 27) :
    (mk34_ctxMidBInPlace B hB1 hB27).countTempAnd = B + 3 := by
  simp [mk34_ctxMidBInPlace, mk34_ctxTail3]
/-- Effective `30`-bit `keep` vector when `keep[29 - B]` is placed at wire `90 + B` and all other
`keep[k]` (`k ≠ 29 - B`) sit at wire `38 + k`. -/
def mk34_keepInPlaceVec (B : ℕ) (γ : BitAssignment (mk34_mB B)) (k : Fin 30) : ZMod 2 :=
  if k.val = 29 - B then γ ⟨90 + B, by dsimp [mk34_mB]; omega⟩
  else γ ⟨38 + k.val, by dsimp [mk34_mB]; omega⟩
theorem mk34_ctxMidBInPlace_scoped_of_wire (B : ℕ) (hB1 : 1 ≤ B) (hB27 : B ≤ 27)
    (q : Wire (mk34_mB B)) :
    ∃ sMid : BitAssignment (mk34_mB B) → BitAssignment (mk34_mB B),
      ScopedBlock (mk34_mB B) (B + 3) sMid (.z q) ((mk34_ctxMidBInPlace B hB1 hB27).plug (.z q)) ∧
      ∀ γ : BitAssignment (mk34_mB B), cleanRem (mk34_mB B) (B + 3) γ →
        mk34_midBSpec B (sMid γ) γ
          (if bitsVal (mk34_keepInPlaceVec B γ) <
              2 ^ (29 - B) + 2 ^ (30 - B) *
                bitsVal (fun j : Fin B ↦ γ ⟨89 + j.val, by dsimp [mk34_mB]; omega⟩)
           then 1 else 0) := by
  obtain ⟨sTail, hTail, hTailBelow, hTailD6, hTailD7⟩ := mk34_ctxTail3_spec B q
  obtain ⟨setupLt, hLt, hSpecLt⟩ :=
    ScopedBlock.withLtCompLoop_block (M := mk34_mB B) B (90 + B) (by dsimp [mk34_mB]; omega)
      (fun j ↦ ⟨38 + (30 - B) + j.val, by dsimp [mk34_mB]; omega⟩)
      (fun j ↦ ⟨89 + j.val, by dsimp [mk34_mB]; omega⟩)
      (fun j ↦ wire_ne_of_lt (by dsimp; omega))
      (fun j ↦ by dsimp; omega)
      (fun j ↦ by dsimp; omega)
      (.z q) ((mk34_ctxTail3 B).plug (.z q)) sTail
      (hTail.cast_rem (by dsimp [mk34_mB]; omega))
  have hPlug : (mk34_ctxMidBInPlace B hB1 hB27).plug (.z q) =
      withCliffAlloc (.x ⟨90 + B, by dsimp [mk34_mB]; omega⟩)
        (withLtCompLoop B (90 + B) (by dsimp [mk34_mB]; omega)
          (fun j ↦ ⟨38 + (30 - B) + j.val, by dsimp [mk34_mB]; omega⟩)
          (fun j ↦ ⟨89 + j.val, by dsimp [mk34_mB]; omega⟩)
          (fun j ↦ wire_ne_of_lt (by dsimp; omega))
          (fun j ↦ by dsimp; omega)
          (fun j ↦ by dsimp; omega)
          ((mk34_ctxTail3 B).plug (.z q))) := by
    simp only [mk34_ctxMidBInPlace, TempCtx.append_plug, ctxCliffAlloc_plug,
      mk34_ctxLtCompLoop_plug]
  have hSuppInit : (CliffProg.x (M := mk34_mB B) ⟨90 + B, by dsimp [mk34_mB]; omega⟩).SupportsBelow
      (mk34_mB B - (B + 3)) := by
    dsimp [CliffProg.SupportsBelow, mk34_mB]
    omega
  have hBlock := ScopedBlock.withCliffAlloc_block (M := mk34_mB B)
    (rem := B + 3) (remIn := B + 3)
    (by dsimp [mk34_mB]; omega) (le_refl (B + 3))
    (.x ⟨90 + B, by dsimp [mk34_mB]; omega⟩) hSuppInit
    (hLt.cast_rem (by dsimp [mk34_mB]; omega))
  rw [← hPlug] at hBlock
  refine ⟨_, hBlock, fun γ hγ ↦ ?_⟩
  let γ₁ := (CliffProg.x (M := mk34_mB B) ⟨90 + B, by dsimp [mk34_mB]; omega⟩).eval γ
  have hγ₁_ne : ∀ w : Wire (mk34_mB B), w.val ≠ 90 + B → γ₁ w = γ w := fun w hw ↦ by
    dsimp only [γ₁, CliffProg.eval]
    exact Function.update_of_ne (fun h ↦ hw (congrArg Fin.val h)) _ _
  have hγ₁_prev : γ₁ ⟨90 + B, by dsimp [mk34_mB]; omega⟩ =
      1 + mk34_keepInPlaceVec B γ ⟨29 - B, by omega⟩ := by
    dsimp only [γ₁, CliffProg.eval, mk34_keepInPlaceVec]
    rw [Function.update_self, ite_eq_left rfl, add_comm]
  have hγ₁_clean : cleanRem (mk34_mB B) (mk34_mB B - ((90 + B) + 1)) γ₁ := fun w hw ↦ by
    rw [hγ₁_ne w (by dsimp [mk34_mB] at hw; omega)]
    exact hγ w (by dsimp [mk34_mB] at hw ⊢; omega)
  obtain ⟨_, hLtBelow, hLtCarry⟩ := hSpecLt γ₁ hγ₁_clean
  have hBelowAll : ∀ w : Wire (mk34_mB B), w.val < 90 + B → sTail (setupLt γ₁) w = γ w := fun
      w hw ↦ (hTailBelow (setupLt γ₁) w (by omega)).trans
      ((hLtBelow w hw).trans (hγ₁_ne w (by omega)))
  have hCarryWire : (⟨90 + 2 * B, by dsimp [mk34_mB]; omega⟩ : Wire (mk34_mB B)) =
      ⟨(90 + B) + B, by dsimp [mk34_mB]; omega⟩ := Fin.ext (by dsimp; omega)
  have hA_eq : (fun j : Fin B ↦ γ₁ ⟨38 + (30 - B) + j.val, by dsimp [mk34_mB]; omega⟩) =
      (fun j : Fin B ↦ mk34_keepInPlaceVec B γ ⟨(30 - B) + j.val, by omega⟩) := by
    funext j
    rw [hγ₁_ne _ (by dsimp; omega)]
    dsimp only [mk34_keepInPlaceVec]
    rw [ite_eq_right (by omega)]
    exact congrArg γ (Fin.ext (by dsimp; omega))
  have hB_eq : (fun j : Fin B ↦ γ₁ ⟨89 + j.val, by dsimp [mk34_mB]; omega⟩) =
      (fun j : Fin B ↦ γ ⟨89 + j.val, by dsimp [mk34_mB]; omega⟩) :=
    funext fun j ↦ hγ₁_ne _ (by dsimp; omega)
  have hIff : setupLt γ₁ ⟨90 + 2 * B, by dsimp [mk34_mB]; omega⟩ = 1 ↔
      bitsVal (mk34_keepInPlaceVec B γ) <
        2 ^ (29 - B) + 2 ^ (30 - B) *
          bitsVal (fun j : Fin B ↦ γ ⟨89 + j.val, by dsimp [mk34_mB]; omega⟩) := by
    rw [hCarryWire, hLtCarry, hA_eq, hB_eq, hγ₁_prev]
    exact mk34_midpoint_lt_iff B hB1 hB27
      (mk34_keepInPlaceVec B γ)
      (fun j : Fin B ↦ γ ⟨89 + j.val, by dsimp [mk34_mB]; omega⟩)
  have hKeepEq : setupLt γ₁ ⟨90 + 2 * B, by dsimp [mk34_mB]; omega⟩ =
      (if bitsVal (mk34_keepInPlaceVec B γ) <
          2 ^ (29 - B) + 2 ^ (30 - B) *
            bitsVal (fun j : Fin B ↦ γ ⟨89 + j.val, by dsimp [mk34_mB]; omega⟩)
       then 1 else 0) := by
    rcases zmod2_eq_zero_or_one (setupLt γ₁ ⟨90 + 2 * B, by dsimp [mk34_mB]; omega⟩) with hs | hs
    · have hnot : ¬ bitsVal (mk34_keepInPlaceVec B γ) <
          2 ^ (29 - B) + 2 ^ (30 - B) *
            bitsVal (fun j : Fin B ↦ γ ⟨89 + j.val, by dsimp [mk34_mB]; omega⟩) := by
        rw [← hIff, hs]; decide
      simp only [hs, hnot, ↓reduceIte]
    · have hyes := hIff.mp hs
      simp only [hs, hyes, ↓reduceIte]
  have hs0 : setupLt γ₁ ⟨0, by dsimp [mk34_mB]; omega⟩ = γ ⟨0, by dsimp [mk34_mB]; omega⟩ :=
    (hLtBelow _ (by dsimp; omega)).trans (hγ₁_ne _ (by dsimp; omega))
  have hrz : setupLt γ₁ ⟨85, by dsimp [mk34_mB]; omega⟩ = γ ⟨85, by dsimp [mk34_mB]; omega⟩ :=
    (hLtBelow _ (by dsimp; omega)).trans (hγ₁_ne _ (by dsimp; omega))
  have hih : setupLt γ₁ ⟨36, by dsimp [mk34_mB]; omega⟩ = γ ⟨36, by dsimp [mk34_mB]; omega⟩ :=
    (hLtBelow _ (by dsimp; omega)).trans (hγ₁_ne _ (by dsimp; omega))
  have hd3 : setupLt γ₁ ⟨88, by dsimp [mk34_mB]; omega⟩ = γ ⟨88, by dsimp [mk34_mB]; omega⟩ :=
    (hLtBelow _ (by dsimp; omega)).trans (hγ₁_ne _ (by dsimp; omega))
  have hts : setupLt γ₁ ⟨89 + B, by dsimp [mk34_mB]; omega⟩ =
      γ ⟨89 + B, by dsimp [mk34_mB]; omega⟩ :=
    (hLtBelow _ (by dsimp; omega)).trans (hγ₁_ne _ (by dsimp; omega))
  dsimp only [Function.comp_apply, mk34_midBSpec]
  refine ⟨hBelowAll, ?_, ?_⟩
  · rw [hTailD6 (setupLt γ₁), hKeepEq, hd3, hts, hrz, hs0]
  · rw [hTailD7 (setupLt γ₁), hih, hrz, hKeepEq, hd3, hts, hs0]
theorem mk34_ctxMidBInPlace_fwdBits_wire (B : ℕ) (hB1 : 1 ≤ B) (hB27 : B ≤ 27)
    (q : Wire (mk34_mB B)) (γ : BitAssignment (mk34_mB B))
    (hγ : cleanRem (mk34_mB B) (B + 3) γ) :
    ∃ sMid : BitAssignment (mk34_mB B) → BitAssignment (mk34_mB B),
      (mk34_ctxMidBInPlace B hB1 hB27).fwdBits γ q = sMid γ q ∧
      mk34_midBSpec B (sMid γ) γ
        (if bitsVal (mk34_keepInPlaceVec B γ) <
            2 ^ (29 - B) + 2 ^ (30 - B) *
              bitsVal (fun j : Fin B ↦ γ ⟨89 + j.val, by dsimp [mk34_mB]; omega⟩)
         then 1 else 0) := by
  obtain ⟨sMid, hB, hSpec⟩ := mk34_ctxMidBInPlace_scoped_of_wire B hB1 hB27 q
  have h₁ := (mk34_ctxMidBInPlace B hB1 hB27).plug_evalSign (.z q) γ
  have h₂ := hB.sign γ hγ
  dsimp [TempPhaseProg.evalSign] at h₁ h₂
  exact ⟨sMid, h₁.symm.trans h₂, hSpec γ hγ⟩
theorem mk34_ctxMidBInPlace_fwdBits_fLeaf (B : ℕ) (hB1 : 1 ≤ B) (hB27 : B ≤ 27)
    (γ : BitAssignment (mk34_mB B)) (hγ : cleanRem (mk34_mB B) (B + 3) γ)
    (b1 sr ge216 ge218 ge217 : ZMod 2)
    (hu1 : γ ⟨86, by dsimp [mk34_mB]; omega⟩ =
      (1 + γ ⟨2, by dsimp [mk34_mB]; omega⟩) * (1 + b1))
    (hvL : γ ⟨87, by dsimp [mk34_mB]; omega⟩ =
      ((1 + γ ⟨2, by dsimp [mk34_mB]; omega⟩) * (1 + b1)) *
        (((1 + sr) * (1 + ge218)) * (1 + (1 + γ ⟨0, by dsimp [mk34_mB]; omega⟩) * ge216)))
    (hd3 : γ ⟨88, by dsimp [mk34_mB]; omega⟩ =
      γ ⟨0, by dsimp [mk34_mB]; omega⟩ * ge217) :
    mk34_fLeafMidB B ((mk34_ctxMidBInPlace B hB1 hB27).fwdBits γ) =
      tailDecision11Bit
        (γ ⟨2, by dsimp [mk34_mB]; omega⟩) b1 (γ ⟨0, by dsimp [mk34_mB]; omega⟩)
        sr (γ ⟨36, by dsimp [mk34_mB]; omega⟩) (γ ⟨85, by dsimp [mk34_mB]; omega⟩)
        ge216 ge218 ge217 1
        (if bitsVal (mk34_keepInPlaceVec B γ) <
            2 ^ (29 - B) + 2 ^ (30 - B) *
              bitsVal (fun j : Fin B ↦ γ ⟨89 + j.val, by dsimp [mk34_mB]; omega⟩)
         then 1 else 0)
        (γ ⟨89 + B, by dsimp [mk34_mB]; omega⟩) := by
  obtain ⟨_, he0, hw0⟩ := mk34_ctxMidBInPlace_fwdBits_wire B hB1 hB27 ⟨0, by dsimp [mk34_mB]; omega⟩
    γ hγ
  obtain ⟨_, he2, hw2⟩ := mk34_ctxMidBInPlace_fwdBits_wire B hB1 hB27 ⟨2, by dsimp [mk34_mB]; omega⟩
    γ hγ
  obtain ⟨_, he85, hw85⟩ := mk34_ctxMidBInPlace_fwdBits_wire B hB1 hB27 ⟨85, by
    dsimp [mk34_mB]; omega⟩ γ hγ
  obtain ⟨_, he86, hw86⟩ := mk34_ctxMidBInPlace_fwdBits_wire B hB1 hB27 ⟨86, by
    dsimp [mk34_mB]; omega⟩ γ hγ
  obtain ⟨_, he87, hw87⟩ := mk34_ctxMidBInPlace_fwdBits_wire B hB1 hB27 ⟨87, by
    dsimp [mk34_mB]; omega⟩ γ hγ
  obtain ⟨_, hed6, hwd6⟩ :=
    mk34_ctxMidBInPlace_fwdBits_wire B hB1 hB27 ⟨90 + 2 * B + 2, by dsimp [mk34_mB]; omega⟩ γ hγ
  obtain ⟨_, hed7, hwd7⟩ :=
    mk34_ctxMidBInPlace_fwdBits_wire B hB1 hB27 ⟨90 + 2 * B + 3, by dsimp [mk34_mB]; omega⟩ γ hγ
  apply mk34_fLeafMidB_eq_tailDecision B ((mk34_ctxMidBInPlace B hB1 hB27).fwdBits γ)
  · exact he0.trans (hw0.1 _ (by dsimp; omega))
  · exact he2.trans (hw2.1 _ (by dsimp; omega))
  · exact he85.trans (hw85.1 _ (by dsimp; omega))
  · exact (he86.trans (hw86.1 _ (by dsimp; omega))).trans hu1
  · exact (he87.trans (hw87.1 _ (by dsimp; omega))).trans hvL
  · have h := hed6.trans hwd6.2.1
    rwa [hd3] at h
  · have h := hed7.trans hwd7.2.2
    rwa [hd3] at h
/-- Plugged `TempPhaseProg (mk34_mB B)` witness for `mk34_ctxMidBInPlace`. -/
def mk34_pMidBInPlace (B : ℕ) (hB1 : 1 ≤ B) (hB27 : B ≤ 27) : TempPhaseProg (mk34_mB B) :=
  (mk34_ctxMidBInPlace B hB1 hB27).plug (.z ⟨0, by dsimp [mk34_mB]; omega⟩)
theorem mk34_pMidBInPlace_eq (B : ℕ) (hB1 : 1 ≤ B) (hB27 : B ≤ 27) :
    (mk34_ctxMidBInPlace B hB1 hB27).plug (.z ⟨0, by dsimp [mk34_mB]; omega⟩) =
      mk34_pMidBInPlace B hB1 hB27 := rfl
theorem mk34_pMidBInPlace_valid_and_bits (B : ℕ) (hB1 : 1 ≤ B) (hB27 : B ≤ 27) : ValidCleanRem
    (mk34_mB B) (B + 3) (mk34_pMidBInPlace B hB1 hB27) ∧ (∀ γ : BitAssignment (mk34_mB B),
    cleanRem (mk34_mB B) (B + 3) γ → (mk34_pMidBInPlace B hB1 hB27).evalBits γ = γ) := by
  obtain ⟨_, hB, _⟩ := mk34_ctxMidBInPlace_scoped_of_wire B hB1 hB27 ⟨0, by dsimp [mk34_mB]; omega⟩
  exact ⟨hB.valid, hB.bits⟩
/-- Embedding `Fin 86 ↪ Fin posCoreWires` replacing index `38 + (29 - B)` by `⟨3, _⟩` so that
`rCore ⟨3948 + 38 + (29 - B), _⟩` (`keep[29 - B]`) can occupy wire `90 + B`. -/
def mk34_coreHi86SwapIdx (B : ℕ) (_hB1 : 1 ≤ B) (_hB27 : B ≤ 27) : Fin 86 ↪ Fin posCoreWires where
  toFun i :=
    if i.val = 38 + (29 - B) then ⟨3, by decide⟩
    else ⟨3948 + i.val, by dsimp [posCoreWires]; omega⟩
  inj' a b h := by
    dsimp only at h
    by_cases ha : a.val = 38 + (29 - B) <;> by_cases hb : b.val = 38 + (29 - B)
    · exact Fin.ext (ha.trans hb.symm)
    · simp only [ha, hb, ↓reduceIte] at h
      have hv := congrArg Fin.val h; dsimp at hv; omega
    · simp only [ha, hb, ↓reduceIte] at h
      have hv := congrArg Fin.val h; dsimp at hv; omega
    · simp only [ha, hb, ↓reduceIte] at h
      have hv := congrArg Fin.val h; dsimp at hv; exact Fin.ext (by omega)
/-- `86`-wire core register with `keep[29 - B]` swapped out to `rCore ⟨3, _⟩`. -/
def mk34_rCoreHi86Swap {n : ℕ} (B : ℕ) (hB1 : 1 ≤ B) (hB27 : B ≤ 27)
    (rCore : QRegister posCoreWires n) : QRegister 86 n :=
  ⟨(mk34_coreHi86SwapIdx B hB1 hB27).trans rCore.wires⟩
theorem mk34_rCoreHi86Swap_apply_of_ne {n : ℕ} (B : ℕ) (hB1 : 1 ≤ B) (hB27 : B ≤ 27)
    (rCore : QRegister posCoreWires n) (i : Fin 86) (hne : i.val ≠ 38 + (29 - B)) :
    mk34_rCoreHi86Swap B hB1 hB27 rCore i =
      rCore ⟨3948 + i.val, by dsimp [posCoreWires]; omega⟩ := by
  change rCore (if i.val = 38 + (29 - B) then _ else _) = _
  rw [ite_eq_right hne]
/-- `(B + 4)`-wire register `(keep[29 - B]) ++ rSubB3` placing `keep[29 - B]` at index `0` (`90 +
B`)
and the `B + 3` clean wires `rSubB3` at indices `1 .. B + 3` (`90 + B + 1 .. 90 + 2 * B + 3`). -/
def mk34_rSubB4InPlace {n : ℕ} (B : ℕ) (_hB1 : 1 ≤ B) (_hB27 : B ≤ 27)
    (rCore : QRegister posCoreWires n) (rSubB3 : QRegister (B + 3) n)
    (hCSub : rCore.DisjointWires rSubB3) : QRegister (B + 4) n where
  wires :=
    { toFun := fun j ↦
        if hj : j.val = 0 then
          rCore ⟨3948 + 38 + (29 - B), by dsimp [posCoreWires]; omega⟩
        else
          rSubB3 ⟨j.val - 1, by omega⟩
      inj' := fun a b h ↦ by
        dsimp only at h
        by_cases ha : a.val = 0 <;> by_cases hb : b.val = 0
        · exact Fin.ext (ha.trans hb.symm)
        · simp only [ha, hb, ↓reduceDIte] at h
          exact False.elim (hCSub.ne _ _ h)
        · simp only [ha, hb, ↓reduceDIte] at h
          exact False.elim (hCSub.ne _ _ h.symm)
        · simp only [ha, hb, ↓reduceDIte] at h
          have hv := congrArg Fin.val (rSubB3.wires.injective h)
          dsimp at hv; exact Fin.ext (by omega) }
theorem mk34_rSubB4InPlace_succ {n : ℕ} (B : ℕ) (hB1 : 1 ≤ B) (hB27 : B ≤ 27)
    (rCore : QRegister posCoreWires n) (rSubB3 : QRegister (B + 3) n)
    (hCSub : rCore.DisjointWires rSubB3) (j : Fin (B + 3)) :
    mk34_rSubB4InPlace B hB1 hB27 rCore rSubB3 hCSub ⟨1 + j.val, by omega⟩ = rSubB3 j := by
  change (if hj : (1 + j.val : ℕ) = 0 then _ else _) = _
  rw [dite_eq_right (by omega)]
  exact congrArg rSubB3.wires (Fin.ext (by dsimp; omega))
theorem mk34_rCoreHi86Swap_disjoint_rSubB4InPlace {n : ℕ} (B : ℕ) (hB1 : 1 ≤ B)
    (hB27 : B ≤ 27) (rCore : QRegister posCoreWires n) (rSubB3 : QRegister (B + 3) n)
    (hCSub : rCore.DisjointWires rSubB3) : (mk34_rCoreHi86Swap B hB1 hB27 rCore).DisjointWires
    (mk34_rSubB4InPlace B hB1 hB27 rCore rSubB3 hCSub) :=
  QRegister.disjoint_iff.mpr fun i j h ↦ by
    change rCore (if i.val = 38 + (29 - B) then _ else _) =
      (if hj : j.val = 0 then _ else _) at h
    by_cases hj : j.val = 0
    · simp only [hj, ↓reduceDIte] at h
      have hinj := congrArg Fin.val (rCore.wires.injective h)
      by_cases hi : i.val = 38 + (29 - B)
      · simp [hi] at hinj; omega
      · simp [hi] at hinj; omega
    · simp only [hj, ↓reduceDIte] at h
      exact hCSub.ne _ _ h
theorem mk34_rCoreHi86Swap_disjoint_of_core {n k : ℕ} (B : ℕ) (hB1 : 1 ≤ B) (hB27 : B ≤ 27)
    {rCore : QRegister posCoreWires n} {rOther : QRegister k n}
    (hDisj : rCore.DisjointWires rOther) :
    (mk34_rCoreHi86Swap B hB1 hB27 rCore).DisjointWires rOther :=
  QRegister.disjoint_iff.mpr fun i j h ↦ hDisj.ne (mk34_coreHi86SwapIdx B hB1 hB27 i) j h
theorem mk34_rSubB4InPlace_disjoint_left {n k : ℕ} (B : ℕ) (hB1 : 1 ≤ B) (hB27 : B ≤ 27)
    {rOther : QRegister k n} {rCore : QRegister posCoreWires n} {rSubB3 : QRegister (B + 3) n}
    (hOC : rOther.DisjointWires rCore) (hOS : rOther.DisjointWires rSubB3)
    (hCSub : rCore.DisjointWires rSubB3) :
    rOther.DisjointWires (mk34_rSubB4InPlace B hB1 hB27 rCore rSubB3 hCSub) :=
  QRegister.disjoint_iff.mpr fun i j h ↦ by
    change rOther i = (if hj : j.val = 0 then _ else _) at h
    by_cases hj : j.val = 0
    · simp only [hj, ↓reduceDIte] at h
      exact hOC.ne i _ h
    · simp only [hj, ↓reduceDIte] at h
      exact hOS.ne i _ h
/-- Combined `(mk34_mB B)`-wire register for `mk34_ctxMidBInPlace`, requiring only `B + 3` clean
wires `rSubB3`. -/
def mk34_rCombBInPlace {n : ℕ} (B : ℕ) (hB1 : 1 ≤ B) (hB27 : B ≤ 27)
    (rCore : QRegister posCoreWires n) (rHold3 : QRegister 3 n)
    (rOutTop : QRegister (B + 1) n) (rSubB3 : QRegister (B + 3) n)
    (hCHold : rCore.DisjointWires rHold3) (hCOut : rCore.DisjointWires rOutTop)
    (hHOut : rHold3.DisjointWires rOutTop) (hCSub : rCore.DisjointWires rSubB3)
    (hHSub : rHold3.DisjointWires rSubB3) (hOutSub : rOutTop.DisjointWires rSubB3) : QRegister
    (mk34_mB B) n :=
  let rCoreSw := mk34_rCoreHi86Swap B hB1 hB27 rCore
  let rSubB4 := mk34_rSubB4InPlace B hB1 hB27 rCore rSubB3 hCSub
  let hCSwHold := mk34_rCoreHi86Swap_disjoint_of_core B hB1 hB27 hCHold
  let hCSwOut := mk34_rCoreHi86Swap_disjoint_of_core B hB1 hB27 hCOut
  let hCSwSub4 := mk34_rCoreHi86Swap_disjoint_rSubB4InPlace B hB1 hB27 rCore rSubB3 hCSub
  let hHSub4 := mk34_rSubB4InPlace_disjoint_left B hB1 hB27 (QRegExt.disjointWires_symm hCHold)
    hHSub hCSub
  let hOutSub4 := mk34_rSubB4InPlace_disjoint_left B hB1 hB27 (QRegExt.disjointWires_symm hCOut)
    hOutSub hCSub
  let rAct89 := rCoreSw.concat rHold3 hCSwHold
  have hAct89Out : rAct89.DisjointWires rOutTop :=
    QRegister.disjoint_iff.mpr fun a b heq ↦
      Fin.addCases (m := 86) (n := 3)
        (motive := fun a ↦ rAct89 a = rOutTop b → False)
        (fun i hi ↦ hCSwOut.ne i b ((QRegister.concat_apply_left _ _ _ i).symm.trans hi))
        (fun j hj ↦ hHOut.ne j b ((QRegister.concat_apply_right _ _ _ j).symm.trans hj))
        a heq
  let rActB := rAct89.concat rOutTop hAct89Out
  have hAct89Sub : rAct89.DisjointWires rSubB4 :=
    QRegister.disjoint_iff.mpr fun a b heq ↦
      Fin.addCases (m := 86) (n := 3)
        (motive := fun a ↦ rAct89 a = rSubB4 b → False)
        (fun i hi ↦ hCSwSub4.ne i b ((QRegister.concat_apply_left _ _ _ i).symm.trans hi))
        (fun j hj ↦ hHSub4.ne j b ((QRegister.concat_apply_right _ _ _ j).symm.trans hj))
        a heq
  have hActBSub : rActB.DisjointWires rSubB4 :=
    QRegister.disjoint_iff.mpr fun a b heq ↦
      Fin.addCases (m := 89) (n := B + 1)
        (motive := fun a ↦ rActB a = rSubB4 b → False)
        (fun i hi ↦ hAct89Sub.ne i b ((QRegister.concat_apply_left _ _ _ i).symm.trans hi))
        (fun j hj ↦ hOutSub4.ne j b ((QRegister.concat_apply_right _ _ _ j).symm.trans hj))
        a heq
  rActB.concat rSubB4 hActBSub
theorem mk34_rCombBInPlace_core_ne {n : ℕ} (B : ℕ) (hB1 : 1 ≤ B) (hB27 : B ≤ 27)
    (rCore : QRegister posCoreWires n) (rHold3 : QRegister 3 n)
    (rOutTop : QRegister (B + 1) n) (rSubB3 : QRegister (B + 3) n)
    (hCHold : rCore.DisjointWires rHold3)
    (hCOut : rCore.DisjointWires rOutTop)
    (hHOut : rHold3.DisjointWires rOutTop)
    (hCSub : rCore.DisjointWires rSubB3)
    (hHSub : rHold3.DisjointWires rSubB3)
    (hOutSub : rOutTop.DisjointWires rSubB3)
    (i : Fin 86) (hne : i.val ≠ 38 + (29 - B)) :
    mk34_rCombBInPlace B hB1 hB27 rCore rHold3 rOutTop rSubB3 hCHold hCOut hHOut hCSub hHSub hOutSub
        ⟨i.val, by dsimp [mk34_mB]; omega⟩ =
      rCore ⟨3948 + i.val, by dsimp [posCoreWires]; omega⟩ := by
  dsimp only [mk34_rCombBInPlace]
  have h1 : (⟨i.val, by omega⟩ : Fin ((89 + (B + 1)) + (B + 4))) =
      Fin.castAdd (B + 4) (Fin.castAdd (B + 1) (Fin.castAdd 3 i)) := by ext; rfl
  rw [h1, QRegister.concat_apply_left, QRegister.concat_apply_left, QRegister.concat_apply_left]
  exact mk34_rCoreHi86Swap_apply_of_ne B hB1 hB27 rCore i hne
theorem mk34_rCombBInPlace_hold {n : ℕ} (B : ℕ) (hB1 : 1 ≤ B) (hB27 : B ≤ 27)
    (rCore : QRegister posCoreWires n) (rHold3 : QRegister 3 n)
    (rOutTop : QRegister (B + 1) n) (rSubB3 : QRegister (B + 3) n)
    (hCHold : rCore.DisjointWires rHold3)
    (hCOut : rCore.DisjointWires rOutTop)
    (hHOut : rHold3.DisjointWires rOutTop)
    (hCSub : rCore.DisjointWires rSubB3)
    (hHSub : rHold3.DisjointWires rSubB3)
    (hOutSub : rOutTop.DisjointWires rSubB3) (i : Fin 3) :
    mk34_rCombBInPlace B hB1 hB27 rCore rHold3 rOutTop rSubB3 hCHold hCOut hHOut hCSub hHSub hOutSub
        ⟨86 + i.val, by dsimp [mk34_mB]; omega⟩ =
      rHold3 i := by
  dsimp only [mk34_rCombBInPlace]
  have h1 : (⟨86 + i.val, by omega⟩ : Fin ((89 + (B + 1)) + (B + 4))) =
      Fin.castAdd (B + 4) (Fin.castAdd (B + 1) (Fin.natAdd 86 i)) := by ext; rfl
  rw [h1, QRegister.concat_apply_left, QRegister.concat_apply_left, QRegister.concat_apply_right]
theorem mk34_rCombBInPlace_out {n : ℕ} (B : ℕ) (hB1 : 1 ≤ B) (hB27 : B ≤ 27)
    (rCore : QRegister posCoreWires n) (rHold3 : QRegister 3 n)
    (rOutTop : QRegister (B + 1) n) (rSubB3 : QRegister (B + 3) n)
    (hCHold : rCore.DisjointWires rHold3)
    (hCOut : rCore.DisjointWires rOutTop)
    (hHOut : rHold3.DisjointWires rOutTop)
    (hCSub : rCore.DisjointWires rSubB3)
    (hHSub : rHold3.DisjointWires rSubB3)
    (hOutSub : rOutTop.DisjointWires rSubB3) (i : Fin (B + 1)) :
    mk34_rCombBInPlace B hB1 hB27 rCore rHold3 rOutTop rSubB3 hCHold hCOut hHOut hCSub hHSub hOutSub
        ⟨89 + i.val, by dsimp [mk34_mB]; omega⟩ =
      rOutTop i := by
  dsimp only [mk34_rCombBInPlace]
  have h1 : (⟨89 + i.val, by omega⟩ : Fin ((89 + (B + 1)) + (B + 4))) =
      Fin.castAdd (B + 4) (Fin.natAdd 89 i) := by ext; rfl
  rw [h1, QRegister.concat_apply_left, QRegister.concat_apply_right]
theorem mk34_rCombBInPlace_prev {n : ℕ} (B : ℕ) (hB1 : 1 ≤ B) (hB27 : B ≤ 27)
    (rCore : QRegister posCoreWires n) (rHold3 : QRegister 3 n)
    (rOutTop : QRegister (B + 1) n) (rSubB3 : QRegister (B + 3) n)
    (hCHold : rCore.DisjointWires rHold3)
    (hCOut : rCore.DisjointWires rOutTop)
    (hHOut : rHold3.DisjointWires rOutTop)
    (hCSub : rCore.DisjointWires rSubB3)
    (hHSub : rHold3.DisjointWires rSubB3)
    (hOutSub : rOutTop.DisjointWires rSubB3) :
    mk34_rCombBInPlace B hB1 hB27 rCore rHold3 rOutTop rSubB3 hCHold hCOut hHOut hCSub hHSub hOutSub
        ⟨90 + B, by dsimp [mk34_mB]; omega⟩ =
      rCore ⟨3948 + (38 + (29 - B)), by dsimp [posCoreWires]; omega⟩ := by
  dsimp only [mk34_rCombBInPlace]
  have h1 : (⟨90 + B, by omega⟩ : Fin ((89 + (B + 1)) + (B + 4))) =
      Fin.natAdd (89 + (B + 1)) ⟨0, by omega⟩ :=
    Fin.ext (by change 90 + B = (89 + (B + 1)) + 0; omega)
  rw [h1, QRegister.concat_apply_right]
  exact congrArg rCore.wires (Fin.ext (by dsimp; omega))
theorem mk34_tailScr_rCombBInPlace {n : ℕ} (B : ℕ) (hB1 : 1 ≤ B) (hB27 : B ≤ 27)
    (rCore : QRegister posCoreWires n) (rHold3 : QRegister 3 n)
    (rOutTop : QRegister (B + 1) n) (rSubB3 : QRegister (B + 3) n)
    (hCHold : rCore.DisjointWires rHold3)
    (hCOut : rCore.DisjointWires rOutTop)
    (hHOut : rHold3.DisjointWires rOutTop)
    (hCSub : rCore.DisjointWires rSubB3)
    (hHSub : rHold3.DisjointWires rSubB3)
    (hOutSub : rOutTop.DisjointWires rSubB3) :
    tailScr (mk34_rCombBInPlace B hB1 hB27 rCore rHold3 rOutTop rSubB3
        hCHold hCOut hHOut hCSub hHSub hOutSub)
        (B + 3) (by dsimp [mk34_mB]; omega) =
      rSubB3.wires := by
  funext j
  dsimp only [tailScr, mk34_rCombBInPlace]
  have h1 : (⟨(mk34_mB B - (B + 3)) + j.val, by dsimp [mk34_mB]; omega⟩ :
      Fin ((89 + (B + 1)) + (B + 4))) = Fin.natAdd (89 + (B + 1)) ⟨1 + j.val, by omega⟩ := by
    ext; dsimp [mk34_mB]; omega
  rw [h1, QRegister.concat_apply_right, mk34_rSubB4InPlace_succ]
/-- In-place `(B + 3)`-wire inner reversible circuit for `mk34_ctxMidBInPlace`. -/
def mk34_cMidKickBInPlace {n : ℕ} (B : ℕ) (hB1 : 1 ≤ B) (hB27 : B ≤ 27)
    (rCore : QRegister posCoreWires n) (rHold3 : QRegister 3 n)
    (rOutTop : QRegister (B + 1) n) (rSubB3 : QRegister (B + 3) n)
    (hCHold : rCore.DisjointWires rHold3) (hCOut : rCore.DisjointWires rOutTop)
    (hHOut : rHold3.DisjointWires rOutTop) (hCSub : rCore.DisjointWires rSubB3)
    (hHSub : rHold3.DisjointWires rSubB3) (hOutSub : rOutTop.DisjointWires rSubB3) : Circuit n
    :=
  let rComb := mk34_rCombBInPlace B hB1 hB27 rCore rHold3 rOutTop rSubB3
    hCHold hCOut hHOut hCSub hHSub hOutSub
  mk34_ctxToToff rComb (mk34_cLeafMidBOn B rComb) (mk34_ctxMidBInPlace B hB1 hB27)
/-- In-place `(B + 3)`-wire inner `0`-`.TOFF` dynamic circuit (`4 * B + 12` `T`). -/
def mk34_dMidKickBInPlace {Var : Type} {n : ℕ} (B : ℕ) (hB1 : 1 ≤ B) (hB27 : B ≤ 27) (v : Var)
    (rCore : QRegister posCoreWires n) (rHold3 : QRegister 3 n)
    (rOutTop : QRegister (B + 1) n) (rSubB3 : QRegister (B + 3) n)
    (hCHold : rCore.DisjointWires rHold3) (hCOut : rCore.DisjointWires rOutTop)
    (hHOut : rHold3.DisjointWires rOutTop) (hCSub : rCore.DisjointWires rSubB3)
    (hHSub : rHold3.DisjointWires rSubB3) (hOutSub : rOutTop.DisjointWires rSubB3) :
    DynamicCircuit Var n :=
  let rComb := mk34_rCombBInPlace B hB1 hB27 rCore rHold3 rOutTop rSubB3
    hCHold hCOut hHOut hCSub hHSub hOutSub
  mk34_ctxToDyn v rComb (mk34_cLeafMidBOn B rComb) (mk34_ctxMidBInPlace B hB1 hB27)
@[scoped simp] theorem mk34_count_dMidKickBInPlace_toff {Var : Type} {n : ℕ} (B : ℕ)
    (hB1 : 1 ≤ B) (hB27 : B ≤ 27) (v : Var) (rCore : QRegister posCoreWires n)
    (rHold3 : QRegister 3 n) (rOutTop : QRegister (B + 1) n) (rSubB3 : QRegister (B + 3) n)
    (hCHold : rCore.DisjointWires rHold3) (hCOut : rCore.DisjointWires rOutTop)
    (hHOut : rHold3.DisjointWires rOutTop) (hCSub : rCore.DisjointWires rSubB3)
    (hHSub : rHold3.DisjointWires rSubB3) (hOutSub : rOutTop.DisjointWires rSubB3) :
    (mk34_dMidKickBInPlace B hB1 hB27 v rCore rHold3 rOutTop rSubB3 hCHold hCOut hHOut hCSub
    hHSub hOutSub).count PrimitiveGate.TOFF = 0 := by
  simp [mk34_dMidKickBInPlace, mk34_ctxToDyn_count_toff, mk34_cLeafMidBOn_count_toff]
@[scoped simp] theorem mk34_count_dMidKickBInPlace_t {Var : Type} {n : ℕ} (B : ℕ)
    (hB1 : 1 ≤ B) (hB27 : B ≤ 27) (v : Var) (rCore : QRegister posCoreWires n)
    (rHold3 : QRegister 3 n) (rOutTop : QRegister (B + 1) n) (rSubB3 : QRegister (B + 3) n)
    (hCHold : rCore.DisjointWires rHold3) (hCOut : rCore.DisjointWires rOutTop)
    (hHOut : rHold3.DisjointWires rOutTop) (hCSub : rCore.DisjointWires rSubB3)
    (hHSub : rHold3.DisjointWires rSubB3) (hOutSub : rOutTop.DisjointWires rSubB3) :
    (mk34_dMidKickBInPlace B hB1 hB27 v rCore rHold3 rOutTop rSubB3 hCHold hCOut hHOut hCSub
    hHSub hOutSub).count PrimitiveGate.T = 4 * B + 12 := by
  simp only [mk34_dMidKickBInPlace, mk34_ctxToDyn_count_t, mk34_ctxMidBInPlace_countTempAnd,
    mk34_cLeafMidBOn_count_t]
  ring
theorem mk34_dMidKickBInPlace_preservesStoreConst {Var : Type} [Fintype Var] [DecidableEq Var]
    {n : ℕ} (B : ℕ) (hB1 : 1 ≤ B) (hB27 : B ≤ 27) (v : Var) (rCore : QRegister posCoreWires n)
    (rHold3 : QRegister 3 n) (rOutTop : QRegister (B + 1) n) (rSubB3 : QRegister (B + 3) n)
    (hCHold : rCore.DisjointWires rHold3) (hCOut : rCore.DisjointWires rOutTop)
    (hHOut : rHold3.DisjointWires rOutTop) (hCSub : rCore.DisjointWires rSubB3)
    (hHSub : rHold3.DisjointWires rSubB3) (hOutSub : rOutTop.DisjointWires rSubB3) :
    PreservesStoreConst (mk34_dMidKickBInPlace B hB1 hB27 v rCore rHold3 rOutTop rSubB3 hCHold
    hCOut hHOut hCSub hHSub hOutSub) := mk34_ctxToDyn_preservesStoreConst v _ _
    (mk34_ctxMidBInPlace B hB1 hB27)
attribute [local irreducible] mk34_ctxMidBInPlace
theorem mk34_cleanRem_of_subB3InPlace {n : ℕ} (B : ℕ) (hB1 : 1 ≤ B) (hB27 : B ≤ 27)
    (rCore : QRegister posCoreWires n) (rHold3 : QRegister 3 n)
    (rOutTop : QRegister (B + 1) n) (rSubB3 : QRegister (B + 3) n)
    (hCHold : rCore.DisjointWires rHold3) (hCOut : rCore.DisjointWires rOutTop)
    (hHOut : rHold3.DisjointWires rOutTop) (hCSub : rCore.DisjointWires rSubB3)
    (hHSub : rHold3.DisjointWires rSubB3) (hOutSub : rOutTop.DisjointWires rSubB3)
    (β : BitAssignment n) (hSubB3 : ∀ j : Fin (B + 3), β (rSubB3 j) = 0) : cleanRem
    (mk34_mB B) (B + 3) (fun idx ↦ β (mk34_rCombBInPlace B hB1 hB27 rCore rHold3 rOutTop
    rSubB3 hCHold hCOut hHOut hCSub hHSub hOutSub idx)) :=
  fun w hw ↦ by
    let rComb := mk34_rCombBInPlace B hB1 hB27 rCore rHold3 rOutTop rSubB3
      hCHold hCOut hHOut hCSub hHSub hOutSub
    let j : Fin (B + 3) := ⟨w.val - (mk34_mB B - (B + 3)), by dsimp [mk34_mB] at hw ⊢; omega⟩
    have hwEq : rComb w = tailScr rComb (B + 3) (by dsimp [mk34_mB]; omega) j := by
      dsimp only [tailScr, j]
      congr 1; ext; dsimp [mk34_mB] at hw ⊢; omega
    change β (rComb w) = 0
    rw [hwEq, congrFun (mk34_tailScr_rCombBInPlace B hB1 hB27 rCore rHold3 rOutTop rSubB3
      hCHold hCOut hHOut hCSub hHSub hOutSub) j]
    exact hSubB3 j
theorem mk34_cMidKickBInPlace_eval_ket_raw {n : ℕ} (B : ℕ) (hB1 : 1 ≤ B) (hB27 : B ≤ 27)
    (rCore : QRegister posCoreWires n) (rHold3 : QRegister 3 n)
    (rOutTop : QRegister (B + 1) n) (rSubB3 : QRegister (B + 3) n)
    (hCHold : rCore.DisjointWires rHold3)
    (hCOut : rCore.DisjointWires rOutTop)
    (hHOut : rHold3.DisjointWires rOutTop)
    (hCSub : rCore.DisjointWires rSubB3)
    (hHSub : rHold3.DisjointWires rSubB3)
    (hOutSub : rOutTop.DisjointWires rSubB3) (β : BitAssignment n)
    (hSubB3 : ∀ j : Fin (B + 3), β (rSubB3 j) = 0) :
    let rComb := mk34_rCombBInPlace B hB1 hB27 rCore rHold3 rOutTop rSubB3
      hCHold hCOut hHOut hCSub hHSub hOutSub
    (mk34_cMidKickBInPlace B hB1 hB27 rCore rHold3 rOutTop rSubB3
      hCHold hCOut hHOut hCSub hHSub hOutSub).eval.1.mulVec (ket β) =
      ((-1 : ℂ) ^ (mk34_fLeafMidB B
        ((mk34_ctxMidBInPlace B hB1 hB27).fwdBits (fun idx ↦ β (rComb idx)))).val) • ket β := by
  intro rComb
  have hcr := mk34_cleanRem_of_subB3InPlace B hB1 hB27 rCore rHold3 rOutTop rSubB3
    hCHold hCOut hHOut hCSub hHSub hOutSub β hSubB3
  rw [mk34_cMidKickBInPlace, ← mbh_ket_eq_ket,
      mk34_ctxToToff_eval_ket rComb _ _ (mk34_cLeafMidBOn_eval_mbh_ket B rComb)
        ⟨0, by dsimp [mk34_mB]; omega⟩ (mk34_ctxMidBInPlace B hB1 hB27) β]
  rw [mk34_pMidBInPlace_eq, (mk34_pMidBInPlace_valid_and_bits B hB1 hB27).2 _ hcr,
      mk34_writeRegProg_self, mbh_ket_eq_ket]
theorem mk34_realizesCleanUnitary_dMidKickBInPlace {Var : Type} [Fintype Var]
    [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)] (B : ℕ) (hB1 : 1 ≤ B) (hB27 : B ≤ 27) (v : Var)
    (rCore : QRegister posCoreWires n) (rHold3 : QRegister 3 n)
    (rOutTop : QRegister (B + 1) n) (rSubB3 : QRegister (B + 3) n)
    (hCHold : rCore.DisjointWires rHold3) (hCOut : rCore.DisjointWires rOutTop)
    (hHOut : rHold3.DisjointWires rOutTop) (hCSub : rCore.DisjointWires rSubB3)
    (hHSub : rHold3.DisjointWires rSubB3) (hOutSub : rOutTop.DisjointWires rSubB3) :
    RealizesCleanUnitary v (projZeroAll (B + 3) rSubB3.wires) (mk34_dMidKickBInPlace B hB1
    hB27 v rCore rHold3 rOutTop rSubB3 hCHold hCOut hHOut hCSub hHSub hOutSub)
    (mk34_cMidKickBInPlace B hB1 hB27 rCore rHold3 rOutTop rSubB3 hCHold hCOut hHOut hCSub
    hHSub hOutSub).eval := by
  let rComb := mk34_rCombBInPlace B hB1 hB27 rCore rHold3 rOutTop rSubB3
    hCHold hCOut hHOut hCSub hHSub hOutSub
  have hpv : ValidCleanRem (mk34_mB B) (B + 3)
      ((mk34_ctxMidBInPlace B hB1 hB27).plug (.z ⟨0, by dsimp [mk34_mB]; omega⟩)) := by
    rw [mk34_pMidBInPlace_eq]
    exact (mk34_pMidBInPlace_valid_and_bits B hB1 hB27).1
  have hTail := mk34_tailScr_rCombBInPlace B hB1 hB27 rCore rHold3 rOutTop rSubB3
    hCHold hCOut hHOut hCSub hHSub hOutSub
  have h0 := mk34_realizesCleanUnitary_ctxToDyn v rComb (mk34_cLeafMidBOn B rComb)
    (mk34_fLeafMidB B) (mk34_cLeafMidBOn_eval_mbh_ket B rComb)
    ⟨0, by dsimp [mk34_mB]; omega⟩ (mk34_ctxMidBInPlace B hB1 hB27) (B + 3)
    (by dsimp [mk34_mB]; omega) hpv
  rw [hTail] at h0
  exact h0
/-  `1`-wire hold slice `rScr[0..1)` holding `d3` across Stage B in `dKickZeroSub46OptDyn`. -/
/-  `(B + 18)`-wire clean workspace slice `rScr[1..B+19)` shared across Stages A, B, and C. -/
/- `8`-wire clean prefix `rRest[0..8)` (`rScr[1..9)`) used by Stages A and C of
`dKickZeroSub46OptDyn`. -/
/- `15`-wire clean prefix `rRest[0..15)` (`rScr[1..16)`) used by outer Stage B of
`dKickZeroSub46OptDyn`. -/
/- `(B + 3)`-wire clean suffix `rRest[15..B+18)` (`rScr[16..B+19)`) used by inner Stage B of
`dKickZeroSub46OptDyn`. -/
/-  Active `87`-wire register `rCoreHi86 ++ rHold1` for `dKickZeroSub46OptDyn`. -/
theorem mk34_stepLitAnd_mk {M cur w : ℕ} (hcur : cur + 1 ≤ M) (hw : w < M)
    (c₁ : Wire M) (neg₁ : Bool) (c₂ : Wire M) (neg₂ : Bool) (β : BitAssignment M) :
    stepLitAnd cur hcur c₁ neg₁ c₂ neg₂ β ⟨w, hw⟩ =
      if w = cur then litVal (β c₁) neg₁ * litVal (β c₂) neg₂ else β ⟨w, hw⟩ := by
  obtain ⟨hne, heq⟩ := eval_stepLitAnd (rfl : stepLitAnd cur hcur c₁ neg₁ c₂ neg₂ β = _)
  by_cases h : w = cur
  · rw [ite_eq_left h]
    exact heq ⟨w, hw⟩ h
  · rw [ite_eq_right h]
    exact hne ⟨w, hw⟩ h
abbrev mk34_rHoldGen {n mScr : ℕ} (mHold mRest : ℕ) (hmScr : mHold + mRest ≤ mScr)
    (rScr : QRegister mScr n) : QRegister mHold n :=
  rScr.slice 0 mHold (by omega)
abbrev mk34_rRestGen {n mScr : ℕ} (mHold mRest : ℕ) (hmScr : mHold + mRest ≤ mScr)
    (rScr : QRegister mScr n) : QRegister mRest n :=
  rScr.slice mHold mRest (by omega)
abbrev mk34_rSubRestGen {n mScr : ℕ} (mHold mRest : ℕ) (hmScr : mHold + mRest ≤ mScr)
    (off len : ℕ) (hsub : off + len ≤ mRest) (rScr : QRegister mScr n) : QRegister len n :=
  (mk34_rRestGen mHold mRest hmScr rScr).slice off len hsub
theorem mk34_rHoldGen_disjoint_rRestGen {n mScr : ℕ} (mHold mRest : ℕ)
    (hmScr : mHold + mRest ≤ mScr) (rScr : QRegister mScr n) :
    (mk34_rHoldGen mHold mRest hmScr rScr).DisjointWires
      (mk34_rRestGen mHold mRest hmScr rScr) :=
  QRegister.disjoint_iff.mpr fun a b h ↦ by
    dsimp only [mk34_rHoldGen, mk34_rRestGen] at h
    rw [QRegister.slice_apply, QRegister.slice_apply] at h
    have hv := congrArg Fin.val (rScr.wires.injective h)
    dsimp at hv
    omega
theorem mk34_rSubRestGen_disjoint {n mScr : ℕ} (mHold mRest : ℕ) (hmScr : mHold + mRest ≤ mScr)
    (o1 l1 o2 l2 : ℕ) (hs1 : o1 + l1 ≤ mRest) (hs2 : o2 + l2 ≤ mRest) (hsep : o1 + l1 ≤ o2)
    (rScr : QRegister mScr n) :
    (mk34_rSubRestGen mHold mRest hmScr o1 l1 hs1 rScr).DisjointWires
      (mk34_rSubRestGen mHold mRest hmScr o2 l2 hs2 rScr) :=
  QRegister.disjoint_iff.mpr fun a b h ↦ by
    dsimp only [mk34_rSubRestGen] at h
    rw [QRegister.slice_apply, QRegister.slice_apply] at h
    have hv := congrArg Fin.val ((mk34_rRestGen mHold mRest hmScr rScr).wires.injective h)
    dsimp at hv
    omega
theorem mk34_projZeroAll_slice_restGen {n mScr : ℕ} (mHold mRest : ℕ)
    (hmScr : mHold + mRest ≤ mScr) (rScr : QRegister mScr n) (k : ℕ) (hk : k ≤ mRest) :
    projZeroAll k (mk34_rSubRestGen mHold mRest hmScr 0 k (by omega) rScr).wires *
      projZeroAll mRest (mk34_rRestGen mHold mRest hmScr rScr).wires =
        projZeroAll mRest (mk34_rRestGen mHold mRest hmScr rScr).wires := by
  apply MeasureBranchHadamardSem.matrix_ext_ket
  intro β
  rw [mul_mulVec_prog, ket_projZeroAll]
  by_cases hz : ∀ j : Fin mRest, β (mk34_rRestGen mHold mRest hmScr rScr j) = 0
  · rw [ite_eq_left hz, ket_projZeroAll, ite_eq_left]
    intro i
    dsimp only [mk34_rSubRestGen]
    rw [QRegister.slice_apply]
    exact hz ⟨0 + i.val, by omega⟩
  · rw [ite_eq_right hz, Matrix.mulVec_zero]
theorem mk34_projZeroAll_restGen_scr {n mScr : ℕ} (mHold mRest : ℕ)
    (hmScr : mHold + mRest ≤ mScr) (rScr : QRegister mScr n) :
    projZeroAll mRest (mk34_rRestGen mHold mRest hmScr rScr).wires *
      projZeroAll mScr rScr.wires = projZeroAll mScr rScr.wires := by
  apply MeasureBranchHadamardSem.matrix_ext_ket
  intro β
  rw [mul_mulVec_prog, ket_projZeroAll]
  by_cases hz : ∀ s : Fin mScr, β (rScr s) = 0
  · rw [ite_eq_left hz, ket_projZeroAll, ite_eq_left]
    intro j
    dsimp only [mk34_rRestGen]
    rw [QRegister.slice_apply]
    exact hz ⟨mHold + j.val, by omega⟩
  · rw [ite_eq_right hz, Matrix.mulVec_zero]
/-  Combined `95`-wire register `rAct87 ++ rSub8` for Stages A and C of `dKickZeroSub46OptDyn`. -/
abbrev mk34_rActGen {n mScr : ℕ} (mHold mRest : ℕ) (hmScr : mHold + mRest ≤ mScr)
    (rCore : QRegister posCoreWires n) (rScr : QRegister mScr n)
    (hCS : rCore.DisjointWires rScr) : QRegister (86 + mHold) n :=
  (mk34_rCoreHi86 rCore).concat (mk34_rHoldGen mHold mRest hmScr rScr)
    ((hCS.compose_left _).compose_right _)
theorem mk34_rActGen_disjoint_sub {n mScr : ℕ} (mHold mRest off len : ℕ)
    (hmScr : mHold + mRest ≤ mScr) (hsub : off + len ≤ mRest)
    (rCore : QRegister posCoreWires n) (rScr : QRegister mScr n)
    (hCS : rCore.DisjointWires rScr) :
    (mk34_rActGen mHold mRest hmScr rCore rScr hCS).DisjointWires
      (mk34_rSubRestGen mHold mRest hmScr off len hsub rScr) := by
  have h1 : (mk34_rCoreHi86 rCore).DisjointWires
      (mk34_rSubRestGen mHold mRest hmScr off len hsub rScr) :=
    ((hCS.compose_left _).compose_right _).compose_right _
  have h2 : (mk34_rHoldGen mHold mRest hmScr rScr).DisjointWires
      (mk34_rSubRestGen mHold mRest hmScr off len hsub rScr) :=
    (mk34_rHoldGen_disjoint_rRestGen mHold mRest hmScr rScr).compose_right _
  exact QRegister.disjoint_iff.mpr fun a b heq ↦
    Fin.addCases (m := 86) (n := mHold)
      (motive := fun a ↦ mk34_rActGen mHold mRest hmScr rCore rScr hCS a =
        mk34_rSubRestGen mHold mRest hmScr off len hsub rScr b → False)
      (fun i hi ↦ h1.ne i b ((QRegister.concat_apply_left _ _ _ i).symm.trans hi))
      (fun j hj ↦ h2.ne j b ((QRegister.concat_apply_right _ _ _ j).symm.trans hj)) a heq
def mk34_rCombGen {n mScr : ℕ} (mHold mRest mSub : ℕ) (hmScr : mHold + mRest ≤ mScr)
    (hmSub : mSub ≤ mRest) (rCore : QRegister posCoreWires n) (rScr : QRegister mScr n)
    (hCS : rCore.DisjointWires rScr) : QRegister ((86 + mHold) + mSub) n :=
  (mk34_rActGen mHold mRest hmScr rCore rScr hCS).concat
    (mk34_rSubRestGen mHold mRest hmScr 0 mSub (by omega) rScr)
    (mk34_rActGen_disjoint_sub mHold mRest 0 mSub hmScr (by omega) rCore rScr hCS)
theorem mk34_rCombGen_core {n mScr : ℕ} (mHold mRest mSub : ℕ) (hmScr : mHold + mRest ≤ mScr)
    (hmSub : mSub ≤ mRest) (rCore : QRegister posCoreWires n) (rScr : QRegister mScr n)
    (hCS : rCore.DisjointWires rScr) (i : Fin 86) :
    mk34_rCombGen mHold mRest mSub hmScr hmSub rCore rScr hCS ⟨i.val, by omega⟩ =
      rCore ⟨3948 + i.val, by
        dsimp [posCoreWires]
        omega⟩ := by
  dsimp only [mk34_rCombGen, mk34_rActGen]
  have h1 : (⟨i.val, by omega⟩ : Fin ((86 + mHold) + mSub)) =
      Fin.castAdd mSub (Fin.castAdd mHold i) := Fin.ext rfl
  rw [h1, QRegister.concat_apply_left, QRegister.concat_apply_left]
  simp [mk34_rCoreHi86]
theorem mk34_rCombGen_hold {n mScr : ℕ} (mHold mRest mSub : ℕ) (hmScr : mHold + mRest ≤ mScr)
    (hmSub : mSub ≤ mRest) (rCore : QRegister posCoreWires n) (rScr : QRegister mScr n)
    (hCS : rCore.DisjointWires rScr) (i : Fin mHold) :
    mk34_rCombGen mHold mRest mSub hmScr hmSub rCore rScr hCS ⟨86 + i.val, by omega⟩ =
      mk34_rHoldGen mHold mRest hmScr rScr i := by
  dsimp only [mk34_rCombGen, mk34_rActGen]
  have h1 : (⟨86 + i.val, by omega⟩ : Fin ((86 + mHold) + mSub)) =
      Fin.castAdd mSub (Fin.natAdd 86 i) := Fin.ext rfl
  rw [h1, QRegister.concat_apply_left, QRegister.concat_apply_right]
theorem mk34_rCombGen_sub {n mScr : ℕ} (mHold mRest mSub : ℕ) (hmScr : mHold + mRest ≤ mScr)
    (hmSub : mSub ≤ mRest) (rCore : QRegister posCoreWires n) (rScr : QRegister mScr n)
    (hCS : rCore.DisjointWires rScr) (j : Fin mSub) :
    mk34_rCombGen mHold mRest mSub hmScr hmSub rCore rScr hCS
        ⟨(86 + mHold) + j.val, by omega⟩ =
      mk34_rSubRestGen mHold mRest hmScr 0 mSub (by omega) rScr j := by
  dsimp only [mk34_rCombGen]
  have h1 : (⟨(86 + mHold) + j.val, by omega⟩ : Fin ((86 + mHold) + mSub)) =
      Fin.natAdd (86 + mHold) j := Fin.ext rfl
  rw [h1, QRegister.concat_apply_right]
theorem mk34_tailScr_rCombGen {n mScr : ℕ} (mHold mRest mSub : ℕ) (hmScr : mHold + mRest ≤ mScr)
    (hmSub : mSub ≤ mRest) (rCore : QRegister posCoreWires n) (rScr : QRegister mScr n)
    (hCS : rCore.DisjointWires rScr) :
    tailScr (mk34_rCombGen mHold mRest mSub hmScr hmSub rCore rScr hCS) mSub (by omega) =
      (mk34_rSubRestGen mHold mRest hmScr 0 mSub (by omega) rScr).wires := by
  funext j
  dsimp only [tailScr, mk34_rCombGen]
  have h1 : (⟨((86 + mHold) + mSub - mSub) + j.val, by omega⟩ : Fin ((86 + mHold) + mSub)) =
      Fin.natAdd (86 + mHold) j := by
    apply Fin.ext
    dsimp
    omega
  rw [h1, QRegister.concat_apply_right]
/-- `8`-`TempAnd` context (`32 T`, `8` clean wires `87..94`) computing `d3 = s0 * ge217Bit` on wire
`94`. -/
def mk34_ctxCompD3_8 : TempCtx 95 :=
  (ctxLitAnd 87 (by decide) ⟨35, by decide⟩ false ⟨34, by decide⟩ false
    (by decide) (by decide) (by decide)).append <|
  (ctxLitAnd 88 (by decide) ⟨32, by decide⟩ false ⟨31, by decide⟩ false
    (by decide) (by decide) (by decide)).append <|
  (ctxLitAnd 89 (by decide) ⟨30, by decide⟩ true ⟨29, by decide⟩ true
    (by decide) (by decide) (by decide)).append <|
  (ctxLitAnd 90 (by decide) ⟨89, by decide⟩ false ⟨28, by decide⟩ true
    (by decide) (by decide) (by decide)).append <|
  (ctxLitAnd 91 (by decide) ⟨88, by decide⟩ false ⟨90, by decide⟩ true
    (by decide) (by decide) (by decide)).append <|
  (ctxLitAnd 92 (by decide) ⟨33, by decide⟩ true ⟨91, by decide⟩ true
    (by decide) (by decide) (by decide)).append <|
  (ctxLitAnd 93 (by decide) ⟨87, by decide⟩ false ⟨92, by decide⟩ true
    (by decide) (by decide) (by decide)).append <|
  ctxLitAnd 94 (by decide) ⟨0, by decide⟩ false ⟨93, by decide⟩ false
    (by decide) (by decide) (by decide)
@[scoped simp] theorem mk34_ctxCompD3_8_countTempAnd : mk34_ctxCompD3_8.countTempAnd = 8 := by
  simp [mk34_ctxCompD3_8]
theorem mk34_ctxCompD3_8_scoped_of_wire (q : Wire 95) :
    ∃ s8 : BitAssignment 95 → BitAssignment 95,
      ScopedBlock 95 8 s8 (.z q) (mk34_ctxCompD3_8.plug (.z q)) ∧
      ∀ γ : BitAssignment 95,
        s8 γ ⟨86, by decide⟩ = γ ⟨86, by decide⟩ ∧
        s8 γ ⟨94, by decide⟩ =
          γ ⟨0, by decide⟩ *
            ge217Bit (γ ⟨28, by decide⟩) (γ ⟨29, by decide⟩) (γ ⟨30, by decide⟩)
              (γ ⟨31, by decide⟩) (γ ⟨32, by decide⟩) (γ ⟨33, by decide⟩)
              (γ ⟨34, by decide⟩) (γ ⟨35, by decide⟩) := by
  simp only [mk34_ctxCompD3_8, TempCtx.append_plug, mk34_ctxLitAnd_plug]
  change ∃ s8, ScopedBlock 95 (95 - 87) s8 (.z q) _ ∧ _
  repeat refine ScopedBlock.exists_withLitAnd ?_
  refine ⟨fun γ ↦ γ, ScopedBlock.z_kick q, fun γ ↦ ?_⟩
  simp only [Function.comp_apply, mk34_stepLitAnd_mk, eq_self, Nat.reduceEqDiff, ↓reduceIte,
    litVal_false, litVal_true]
  exact ⟨trivial, rfl⟩
theorem mk34_ctxCompD3_8_fwdBits_wire (q : Wire 95)
    (γ : BitAssignment 95) (hγ : cleanRem 95 8 γ) :
    ∃ s8 : BitAssignment 95 → BitAssignment 95,
      mk34_ctxCompD3_8.fwdBits γ q = s8 γ q ∧
      s8 γ ⟨86, by decide⟩ = γ ⟨86, by decide⟩ ∧
      s8 γ ⟨94, by decide⟩ =
        γ ⟨0, by decide⟩ *
          ge217Bit (γ ⟨28, by decide⟩) (γ ⟨29, by decide⟩) (γ ⟨30, by decide⟩)
            (γ ⟨31, by decide⟩) (γ ⟨32, by decide⟩) (γ ⟨33, by decide⟩)
            (γ ⟨34, by decide⟩) (γ ⟨35, by decide⟩) := by
  obtain ⟨s8, hB, hSpec⟩ := mk34_ctxCompD3_8_scoped_of_wire q
  have h₁ := mk34_ctxCompD3_8.plug_evalSign (.z q) γ
  have h₂ := hB.sign γ hγ
  dsimp [TempPhaseProg.evalSign] at h₁ h₂
  exact ⟨s8, h₁.symm.trans h₂, hSpec γ⟩
/-- Diagonal leaf phase polynomial `γ[86] * γ[94]` for `mk34_ctxCompD3_8`. -/
def mk34_fLeafComp1 (γ : BitAssignment 95) : ZMod 2 :=
  γ ⟨86, by decide⟩ * γ ⟨94, by decide⟩
/-- `0`-`T`, `0`-`.TOFF` single-`CZ` leaf circuit for `mk34_ctxCompD3_8`. -/
def mk34_cLeafComp1On {n : ℕ} (rComb : QRegister 95 n) : Circuit n :=
  asymMid_czCircuit (rComb ⟨86, by decide⟩) (rComb ⟨94, by decide⟩)
    (rComb.wires.injective.ne (by decide))
@[scoped simp] theorem mk34_cLeafComp1On_count_toff {n : ℕ} (rComb : QRegister 95 n) :
    (mk34_cLeafComp1On rComb).count PrimitiveGate.TOFF = 0 := by
  simp [mk34_cLeafComp1On, asymMid_czCircuit_count_toff]
@[scoped simp] theorem mk34_cLeafComp1On_count_t {n : ℕ} (rComb : QRegister 95 n) :
    (mk34_cLeafComp1On rComb).count PrimitiveGate.T = 0 := by
  simp [mk34_cLeafComp1On, asymMid_czCircuit_count_t]
theorem mk34_cLeafComp1On_eval_mbh_ket {n : ℕ} (rComb : QRegister 95 n) (β : BitAssignment n) :
    (mk34_cLeafComp1On rComb).eval.1.mulVec (MeasureBranchHadamardSem.ket β) =
      ((-1 : ℂ) ^ (mk34_fLeafComp1 (fun idx ↦ β (rComb idx))).val) •
        MeasureBranchHadamardSem.ket β := by
  rw [mbh_ket_eq_ket, mk34_cLeafComp1On, asymMid_ket_czCircuit]
  rfl
/-- Plugged `TempPhaseProg 95` witness for `mk34_ctxCompD3_8`. -/
def mk34_pCompD3_8 : TempPhaseProg 95 :=
  mk34_ctxCompD3_8.plug (.z ⟨0, by decide⟩)
theorem mk34_pCompD3_8_eq : mk34_ctxCompD3_8.plug (.z ⟨0, by decide⟩) = mk34_pCompD3_8 := rfl
theorem mk34_pCompD3_8_valid_and_bits : ValidCleanRem 95 8 mk34_pCompD3_8 ∧ (∀ γ :
    BitAssignment 95, cleanRem 95 8 γ → mk34_pCompD3_8.evalBits γ = γ) := by
  obtain ⟨_, hB, _⟩ := mk34_ctxCompD3_8_scoped_of_wire ⟨0, by decide⟩
  exact ⟨hB.valid, hB.bits⟩
/-  Inner diagonal phase `Circuit n` for Stages A and C of `dKickZeroSub46OptDyn`. -/
/-  Inner diagonal phase `DynamicCircuit Var n` (`32 T`, `0` `.TOFF`). -/
/-  Stage A / Stage C reversible `Circuit n` XORing `d3` onto `rHold1`. -/
/-  Stage A / Stage C `0`-`.TOFF` `DynamicCircuit Var n` (`32 T`) XORing `d3` onto `rHold1`. -/
/-  Target `1`-bit vector `(d3)` XORed onto `rHold1` by `mk34_cComp1`. -/
attribute [local irreducible] mk34_ctxCompD3_8
def mk34_hold1Vec {n : ℕ} (rCore : QRegister posCoreWires n) (β : BitAssignment n) :
    BitAssignment 1 := fun _ ↦ mk34_holdVec rCore β 2
def mk34_cCompGenInner {n mScr : ℕ} (mHold mRest mSub : ℕ) (hmScr : mHold + mRest ≤ mScr)
    (hmSub : mSub ≤ mRest) (cLeafOn : QRegister ((86 + mHold) + mSub) n → Circuit n)
    (ctx : TempCtx ((86 + mHold) + mSub)) (rCore : QRegister posCoreWires n)
    (rScr : QRegister mScr n) (hCS : rCore.DisjointWires rScr) : Circuit n :=
  let rComb := mk34_rCombGen mHold mRest mSub hmScr hmSub rCore rScr hCS
  mk34_ctxToToff rComb (cLeafOn rComb) ctx
def mk34_dCompGenInner {Var : Type} {n mScr : ℕ} (mHold mRest mSub : ℕ)
    (hmScr : mHold + mRest ≤ mScr) (hmSub : mSub ≤ mRest) (v : Var)
    (cLeafOn : QRegister ((86 + mHold) + mSub) n → Circuit n)
    (ctx : TempCtx ((86 + mHold) + mSub)) (rCore : QRegister posCoreWires n)
    (rScr : QRegister mScr n) (hCS : rCore.DisjointWires rScr) : DynamicCircuit Var n :=
  let rComb := mk34_rCombGen mHold mRest mSub hmScr hmSub rCore rScr hCS
  mk34_ctxToDyn v rComb (cLeafOn rComb) ctx
def mk34_cCompGen {n mScr : ℕ} (mHold mRest mSub : ℕ) (hmScr : mHold + mRest ≤ mScr)
    (hmSub : mSub ≤ mRest) (cLeafOn : QRegister ((86 + mHold) + mSub) n → Circuit n)
    (ctx : TempCtx ((86 + mHold) + mSub)) (rCore : QRegister posCoreWires n)
    (rScr : QRegister mScr n) (hCS : rCore.DisjointWires rScr) : Circuit n :=
  hadamardReg (mk34_rHoldGen mHold mRest hmScr rScr) ;;ᶜ
    mk34_cCompGenInner mHold mRest mSub hmScr hmSub cLeafOn ctx rCore rScr hCS ;;ᶜ
    hadamardReg (mk34_rHoldGen mHold mRest hmScr rScr)
def mk34_dCompGen {Var : Type} {n mScr : ℕ} (mHold mRest mSub : ℕ)
    (hmScr : mHold + mRest ≤ mScr) (hmSub : mSub ≤ mRest) (v : Var)
    (cLeafOn : QRegister ((86 + mHold) + mSub) n → Circuit n)
    (ctx : TempCtx ((86 + mHold) + mSub)) (rCore : QRegister posCoreWires n)
    (rScr : QRegister mScr n) (hCS : rCore.DisjointWires rScr) : DynamicCircuit Var n :=
  .seq (.circuit (hadamardReg (mk34_rHoldGen mHold mRest hmScr rScr)))
    (.seq (mk34_dCompGenInner mHold mRest mSub hmScr hmSub v cLeafOn ctx rCore rScr hCS)
      (.circuit (hadamardReg (mk34_rHoldGen mHold mRest hmScr rScr))))
theorem mk34_dCompGen_preservesStoreConst {Var : Type} [Fintype Var] [DecidableEq Var]
    {n mScr : ℕ} (mHold mRest mSub : ℕ) (hmScr : mHold + mRest ≤ mScr) (hmSub : mSub ≤ mRest)
    (v : Var) (cLeafOn : QRegister ((86 + mHold) + mSub) n → Circuit n)
    (ctx : TempCtx ((86 + mHold) + mSub)) (rCore : QRegister posCoreWires n)
    (rScr : QRegister mScr n) (hCS : rCore.DisjointWires rScr) :
    PreservesStoreConst (mk34_dCompGen mHold mRest mSub hmScr hmSub v cLeafOn ctx rCore rScr hCS) :=
  PreservesStoreConst.seq (PreservesStoreConst.circuit _)
    (PreservesStoreConst.seq (mk34_ctxToDyn_preservesStoreConst v _ _ ctx)
      (PreservesStoreConst.circuit _))
/-  Combined `102`-wire register `rAct87 ++ rSub15` for outer Stage B of `dKickZeroSub46OptDyn`. -/
theorem mk34_cCompGenInner_eval_ket {n mScr : ℕ} (mHold mRest mSub : ℕ)
    (hmScr : mHold + mRest ≤ mScr) (hmSub : mSub ≤ mRest)
    (cLeafOn : QRegister ((86 + mHold) + mSub) n → Circuit n)
    (fLeaf : BitAssignment ((86 + mHold) + mSub) → ZMod 2)
    (ctx : TempCtx ((86 + mHold) + mSub)) (q0 : Wire ((86 + mHold) + mSub))
    (holdVec : QRegister posCoreWires n → BitAssignment n → BitAssignment mHold)
    (rCore : QRegister posCoreWires n) (rScr : QRegister mScr n) (hCS : rCore.DisjointWires rScr)
    (hLeafKet : ∀ β : BitAssignment n,
      (cLeafOn (mk34_rCombGen mHold mRest mSub hmScr hmSub rCore rScr hCS)).eval.1.mulVec
        (MeasureBranchHadamardSem.ket β) =
      ((-1 : ℂ) ^ (fLeaf (fun idx ↦
        β (mk34_rCombGen mHold mRest mSub hmScr hmSub rCore rScr hCS idx))).val) •
        MeasureBranchHadamardSem.ket β)
    (hpBits : ∀ γ : BitAssignment ((86 + mHold) + mSub),
      cleanRem ((86 + mHold) + mSub) mSub γ → (ctx.plug (.z q0)).evalBits γ = γ)
    (hfSpec : ∀ δ : BitAssignment n,
      cleanRem ((86 + mHold) + mSub) mSub
        (fun idx ↦ δ (mk34_rCombGen mHold mRest mSub hmScr hmSub rCore rScr hCS idx)) →
      fLeaf (ctx.fwdBits (fun idx ↦
        δ (mk34_rCombGen mHold mRest mSub hmScr hmSub rCore rScr hCS idx))) =
      ∑ i : Fin mHold, δ (mk34_rHoldGen mHold mRest hmScr rScr i) * holdVec rCore δ i)
    (β : BitAssignment n)
    (hSub0 : ∀ j : Fin mSub, β (mk34_rSubRestGen mHold mRest hmScr 0 mSub (by omega) rScr j) = 0) :
    (mk34_cCompGenInner mHold mRest mSub hmScr hmSub cLeafOn ctx rCore rScr hCS).eval.1.mulVec
        (ket β) =
      ((-1 : ℂ) ^ (∑ i : Fin mHold,
        β (mk34_rHoldGen mHold mRest hmScr rScr i) * holdVec rCore β i).val) • ket β := by
  let rComb := mk34_rCombGen mHold mRest mSub hmScr hmSub rCore rScr hCS
  have hcr : cleanRem ((86 + mHold) + mSub) mSub (fun idx ↦ β (rComb idx)) := fun w hw ↦ by
    let j : Fin mSub := ⟨w.val - (86 + mHold), by omega⟩
    have hwEq : rComb w = tailScr rComb mSub (by omega) j := by
      dsimp only [tailScr, j]
      congr 1
      apply Fin.ext
      dsimp
      omega
    change β (rComb w) = 0
    rw [hwEq, congrFun (mk34_tailScr_rCombGen mHold mRest mSub hmScr hmSub rCore rScr hCS) j]
    exact hSub0 j
  rw [mk34_cCompGenInner, ← mbh_ket_eq_ket,
      mk34_ctxToToff_eval_ket rComb _ _ hLeafKet q0 ctx β,
      hpBits _ hcr, mk34_writeRegProg_self, mbh_ket_eq_ket, hfSpec β hcr]
/-- `15`-`TempAnd` context (`60 T`, `15` clean wires `87..101`) computing `u1` (`97`) and `vL`
(`101`). -/
def mk34_ctxStageB15 : TempCtx 102 :=
  (ctxLitAnd 87 (by decide) ⟨16, by decide⟩ false ⟨15, by decide⟩ false
    (by decide) (by decide) (by decide)).append <|
  (ctxLitAnd 88 (by decide) ⟨17, by decide⟩ true ⟨87, by decide⟩ true
    (by decide) (by decide) (by decide)).append <|
  (ctxLitAnd 89 (by decide) ⟨19, by decide⟩ false ⟨18, by decide⟩ false
    (by decide) (by decide) (by decide)).append <|
  (ctxLitAnd 90 (by decide) ⟨89, by decide⟩ false ⟨88, by decide⟩ true
    (by decide) (by decide) (by decide)).append <|
  (ctxLitAnd 91 (by decide) ⟨27, by decide⟩ false ⟨26, by decide⟩ false
    (by decide) (by decide) (by decide)).append <|
  (ctxLitAnd 92 (by decide) ⟨24, by decide⟩ false ⟨23, by decide⟩ false
    (by decide) (by decide) (by decide)).append <|
  (ctxLitAnd 93 (by decide) ⟨22, by decide⟩ true ⟨21, by decide⟩ true
    (by decide) (by decide) (by decide)).append <|
  (ctxLitAnd 94 (by decide) ⟨92, by decide⟩ false ⟨93, by decide⟩ true
    (by decide) (by decide) (by decide)).append <|
  (ctxLitAnd 95 (by decide) ⟨25, by decide⟩ true ⟨94, by decide⟩ true
    (by decide) (by decide) (by decide)).append <|
  (ctxLitAnd 96 (by decide) ⟨91, by decide⟩ false ⟨95, by decide⟩ true
    (by decide) (by decide) (by decide)).append <|
  (ctxLitAnd 97 (by decide) ⟨2, by decide⟩ true ⟨1, by decide⟩ true
    (by decide) (by decide) (by decide)).append <|
  (ctxLitAnd 98 (by decide) ⟨0, by decide⟩ true ⟨90, by decide⟩ false
    (by decide) (by decide) (by decide)).append <|
  (ctxLitAnd 99 (by decide) ⟨68, by decide⟩ true ⟨96, by decide⟩ true
    (by decide) (by decide) (by decide)).append <|
  (ctxLitAnd 100 (by decide) ⟨99, by decide⟩ false ⟨98, by decide⟩ true
    (by decide) (by decide) (by decide)).append <|
  ctxLitAnd 101 (by decide) ⟨97, by decide⟩ false ⟨100, by decide⟩ false
    (by decide) (by decide) (by decide)
@[scoped simp]
theorem mk34_ctxStageB15_countTempAnd : mk34_ctxStageB15.countTempAnd = 15 := by
  simp [mk34_ctxStageB15]
theorem mk34_ctxStageB15_fwdBits_below (γ : BitAssignment 102) (w : Wire 102) (hw : w.val < 87) :
    mk34_ctxStageB15.fwdBits γ w = γ w := by
  simp only [mk34_ctxStageB15, mk34_append_fwdBits]
  repeat rw [mk34_ctxLitAnd_fwdBits_of_ne _ _ _ _ _ _ _ _ _ _ w (by omega)]
/-- Leaf wire specification for `mk34_ctxStageB15` on `u1` (`97`) and `vL` (`101`). -/
def mk34_stageB15Spec (φ : BitAssignment 102) (b2 b1 s0 sr ge216 ge218 : ZMod 2) : Prop :=
  let u1 := (1 + b2) * (1 + b1)
  let d0 := (1 + s0) * ge216
  let u2 := (1 + sr) * (1 + ge218)
  let u3 := u2 * (1 + d0)
  let vL := u1 * u3
  φ ⟨97, by decide⟩ = u1 ∧
  φ ⟨101, by decide⟩ = vL
theorem mk34_ctxStageB15_scoped_of_wire (q : Wire 102) :
    ∃ s15 : BitAssignment 102 → BitAssignment 102,
      ScopedBlock 102 15 s15 (.z q) (mk34_ctxStageB15.plug (.z q)) ∧
      ∀ γ : BitAssignment 102,
        mk34_stageB15Spec (s15 γ)
          (γ ⟨2, by decide⟩) (γ ⟨1, by decide⟩) (γ ⟨0, by decide⟩) (γ ⟨68, by decide⟩)
          (ge216Bit (γ ⟨15, by decide⟩) (γ ⟨16, by decide⟩) (γ ⟨17, by decide⟩)
            (γ ⟨18, by decide⟩) (γ ⟨19, by decide⟩))
          (ge218Bit (γ ⟨21, by decide⟩) (γ ⟨22, by decide⟩) (γ ⟨23, by decide⟩)
            (γ ⟨24, by decide⟩) (γ ⟨25, by decide⟩) (γ ⟨26, by decide⟩) (γ ⟨27, by decide⟩)) := by
  simp only [mk34_ctxStageB15, TempCtx.append_plug, mk34_ctxLitAnd_plug]
  change ∃ s15, ScopedBlock 102 (102 - 87) s15 (.z q) _ ∧ _
  repeat refine ScopedBlock.exists_withLitAnd ?_
  refine ⟨fun γ ↦ γ, ScopedBlock.z_kick q, fun γ ↦ ?_⟩
  dsimp only [mk34_stageB15Spec]
  simp only [Function.comp_apply, mk34_stepLitAnd_mk, eq_self, Nat.reduceEqDiff, ↓reduceIte,
    litVal_false, litVal_true]
  exact ⟨trivial, rfl⟩
theorem mk34_ctxStageB15_fwdBits_wire (q : Wire 102)
    (γ : BitAssignment 102) (hγ : cleanRem 102 15 γ) :
    ∃ s15 : BitAssignment 102 → BitAssignment 102,
      mk34_ctxStageB15.fwdBits γ q = s15 γ q ∧
      mk34_stageB15Spec (s15 γ)
        (γ ⟨2, by decide⟩) (γ ⟨1, by decide⟩) (γ ⟨0, by decide⟩) (γ ⟨68, by decide⟩)
        (ge216Bit (γ ⟨15, by decide⟩) (γ ⟨16, by decide⟩) (γ ⟨17, by decide⟩)
          (γ ⟨18, by decide⟩) (γ ⟨19, by decide⟩))
        (ge218Bit (γ ⟨21, by decide⟩) (γ ⟨22, by decide⟩) (γ ⟨23, by decide⟩)
          (γ ⟨24, by decide⟩) (γ ⟨25, by decide⟩) (γ ⟨26, by decide⟩) (γ ⟨27, by decide⟩)) := by
  obtain ⟨s15, hB, hSpec⟩ := mk34_ctxStageB15_scoped_of_wire q
  have h₁ := mk34_ctxStageB15.plug_evalSign (.z q) γ
  have h₂ := hB.sign γ hγ
  dsimp [TempPhaseProg.evalSign] at h₁ h₂
  exact ⟨s15, h₁.symm.trans h₂, hSpec γ⟩
/-- Plugged `TempPhaseProg 102` witness for `mk34_ctxStageB15`. -/
def mk34_pStageB15 : TempPhaseProg 102 :=
  mk34_ctxStageB15.plug (.z ⟨0, by decide⟩)
theorem mk34_pStageB15_eq : mk34_ctxStageB15.plug (.z ⟨0, by decide⟩) = mk34_pStageB15 := rfl
theorem mk34_pStageB15_valid_and_bits : ValidCleanRem 102 15 mk34_pStageB15 ∧ (∀ γ :
    BitAssignment 102, cleanRem 102 15 γ → mk34_pStageB15.evalBits γ = γ) := by
  obtain ⟨_, hB, _⟩ := mk34_ctxStageB15_scoped_of_wire ⟨0, by decide⟩
  exact ⟨hB.valid, hB.bits⟩
attribute [local irreducible] mk34_ctxStageB15
/- `3`-wire hold register `(rSub15 10, rSub15 14, rHold1 0)` (`= (u1, vL, d3)`) for
`dKickZeroSub46OptDyn`. -/
theorem mk34_cCompGen_eval_ket {n mScr : ℕ} (mHold mRest mSub : ℕ)
    (hmScr : mHold + mRest ≤ mScr) (hmSub : mSub ≤ mRest)
    (cLeafOn : QRegister ((86 + mHold) + mSub) n → Circuit n)
    (fLeaf : BitAssignment ((86 + mHold) + mSub) → ZMod 2)
    (ctx : TempCtx ((86 + mHold) + mSub)) (q0 : Wire ((86 + mHold) + mSub))
    (holdVec : QRegister posCoreWires n → BitAssignment n → BitAssignment mHold)
    (hHoldCongr : ∀ (rCore : QRegister posCoreWires n) (β₁ β₂ : BitAssignment n),
      (∀ idx, β₁ (rCore idx) = β₂ (rCore idx)) → holdVec rCore β₁ = holdVec rCore β₂)
    (rCore : QRegister posCoreWires n) (rScr : QRegister mScr n) (hCS : rCore.DisjointWires rScr)
    (hLeafKet : ∀ β : BitAssignment n,
      (cLeafOn (mk34_rCombGen mHold mRest mSub hmScr hmSub rCore rScr hCS)).eval.1.mulVec
        (MeasureBranchHadamardSem.ket β) =
      ((-1 : ℂ) ^ (fLeaf (fun idx ↦
        β (mk34_rCombGen mHold mRest mSub hmScr hmSub rCore rScr hCS idx))).val) •
        MeasureBranchHadamardSem.ket β)
    (hpBits : ∀ γ : BitAssignment ((86 + mHold) + mSub),
      cleanRem ((86 + mHold) + mSub) mSub γ → (ctx.plug (.z q0)).evalBits γ = γ)
    (hfSpec : ∀ δ : BitAssignment n,
      cleanRem ((86 + mHold) + mSub) mSub
        (fun idx ↦ δ (mk34_rCombGen mHold mRest mSub hmScr hmSub rCore rScr hCS idx)) →
      fLeaf (ctx.fwdBits (fun idx ↦
        δ (mk34_rCombGen mHold mRest mSub hmScr hmSub rCore rScr hCS idx))) =
      ∑ i : Fin mHold, δ (mk34_rHoldGen mHold mRest hmScr rScr i) * holdVec rCore δ i)
    (β : BitAssignment n)
    (hSub0 : ∀ j : Fin mSub, β (mk34_rSubRestGen mHold mRest hmScr 0 mSub (by omega) rScr j) = 0) :
    (mk34_cCompGen mHold mRest mSub hmScr hmSub cLeafOn ctx rCore rScr hCS).eval.1.mulVec (ket β) =
      ket (writeReg β (mk34_rHoldGen mHold mRest hmScr rScr)
        (fun i ↦ β (mk34_rHoldGen mHold mRest hmScr rScr i) + holdVec rCore β i)) := by
  dsimp only [mk34_cCompGen]
  simp only [Circuit.eval_seq, Submonoid.coe_mul]
  refine hadamardReg_conj_phase_mulVec_ket (mk34_rHoldGen mHold mRest hmScr rScr)
    (mk34_cCompGenInner mHold mRest mSub hmScr hmSub cLeafOn ctx rCore rScr hCS).eval.1
    (holdVec rCore β) β (fun γHold ↦ ?_)
  let rHold := mk34_rHoldGen mHold mRest hmScr rScr
  let β' := writeReg β rHold γHold
  have hSub0' : ∀ j : Fin mSub,
      β' (mk34_rSubRestGen mHold mRest hmScr 0 mSub (by omega) rScr j) = 0 := fun j ↦ by
    have hdisj : rHold.DisjointWires
        (mk34_rSubRestGen mHold mRest hmScr 0 mSub (by omega) rScr) :=
      (mk34_rHoldGen_disjoint_rRestGen mHold mRest hmScr rScr).compose_right _
    exact (writeReg_apply_of_not_mem β rHold γHold _
      (fun ⟨i, hi⟩ ↦ hdisj.ne i j hi)).trans (hSub0 j)
  have hCoreEq : ∀ idx : Fin posCoreWires, β' (rCore idx) = β (rCore idx) := fun idx ↦
    writeReg_apply_of_not_mem β rHold γHold _
      (fun ⟨i, hi⟩ ↦ (hCS.compose_right _).ne idx i hi.symm)
  rw [mk34_cCompGenInner_eval_ket mHold mRest mSub hmScr hmSub cLeafOn fLeaf ctx q0 holdVec
        rCore rScr hCS hLeafKet hpBits hfSpec β' hSub0',
      hHoldCongr rCore β' β hCoreEq]
  congr 3
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [show β' (rHold i) = γHold i from writeReg_apply_reg β rHold γHold i]
/-  Maps a `102`-wire Stage-B bit assignment `γ` and ambient `β` to the `(mk34_mB B)`-wire input
of `mk34_ctxMidBInPlace`. -/
theorem mk34_realizesCleanUnitary_dCompGen_rest {Var : Type} [Fintype Var] [DecidableEq Var]
    {n mScr : ℕ} [NeZero (2 ^ n)] (mHold mRest mSub : ℕ) (hmScr : mHold + mRest ≤ mScr)
    (hmSub : mSub ≤ mRest) (v : Var)
    (cLeafOn : QRegister ((86 + mHold) + mSub) n → Circuit n)
    (fLeaf : BitAssignment ((86 + mHold) + mSub) → ZMod 2)
    (ctx : TempCtx ((86 + mHold) + mSub)) (q0 : Wire ((86 + mHold) + mSub))
    (holdVec : QRegister posCoreWires n → BitAssignment n → BitAssignment mHold)
    (rCore : QRegister posCoreWires n) (rScr : QRegister mScr n) (hCS : rCore.DisjointWires rScr)
    (hLeafKet : ∀ β : BitAssignment n,
      (cLeafOn (mk34_rCombGen mHold mRest mSub hmScr hmSub rCore rScr hCS)).eval.1.mulVec
        (MeasureBranchHadamardSem.ket β) =
      ((-1 : ℂ) ^ (fLeaf (fun idx ↦
        β (mk34_rCombGen mHold mRest mSub hmScr hmSub rCore rScr hCS idx))).val) •
        MeasureBranchHadamardSem.ket β)
    (hpv : ValidCleanRem ((86 + mHold) + mSub) mSub (ctx.plug (.z q0)))
    (hpBits : ∀ γ : BitAssignment ((86 + mHold) + mSub),
      cleanRem ((86 + mHold) + mSub) mSub γ → (ctx.plug (.z q0)).evalBits γ = γ)
    (hfSpec : ∀ δ : BitAssignment n,
      cleanRem ((86 + mHold) + mSub) mSub
        (fun idx ↦ δ (mk34_rCombGen mHold mRest mSub hmScr hmSub rCore rScr hCS idx)) →
      fLeaf (ctx.fwdBits (fun idx ↦
        δ (mk34_rCombGen mHold mRest mSub hmScr hmSub rCore rScr hCS idx))) =
      ∑ i : Fin mHold, δ (mk34_rHoldGen mHold mRest hmScr rScr i) * holdVec rCore δ i) :
    RealizesCleanUnitary v (projZeroAll mRest (mk34_rRestGen mHold mRest hmScr rScr).wires)
      (mk34_dCompGen mHold mRest mSub hmScr hmSub v cLeafOn ctx rCore rScr hCS)
      (mk34_cCompGen mHold mRest mSub hmScr hmSub cLeafOn ctx rCore rScr hCS).eval := by
  let P := projZeroAll mRest (mk34_rRestGen mHold mRest hmScr rScr).wires
  have hP : Pᴴ = P := projZeroAll_conjTranspose mRest _
  let rComb := mk34_rCombGen mHold mRest mSub hmScr hmSub rCore rScr hCS
  have hInnerSub : RealizesCleanUnitary v
      (projZeroAll mSub (mk34_rSubRestGen mHold mRest hmScr 0 mSub (by omega) rScr).wires)
      (mk34_dCompGenInner mHold mRest mSub hmScr hmSub v cLeafOn ctx rCore rScr hCS)
      (mk34_cCompGenInner mHold mRest mSub hmScr hmSub cLeafOn ctx rCore rScr hCS).eval := by
    have h0 := mk34_realizesCleanUnitary_ctxToDyn v rComb (cLeafOn rComb) fLeaf hLeafKet
      q0 ctx mSub (by omega) hpv
    rwa [mk34_tailScr_rCombGen mHold mRest mSub hmScr hmSub rCore rScr hCS] at h0
  have hInnerRest := RealizesCleanUnitary.mono_proj (projZeroAll_conjTranspose mSub _) hP
    (mk34_projZeroAll_slice_restGen mHold mRest hmScr rScr mSub hmSub) hInnerSub
  have hH_real := RealizesCleanUnitary.circuit v P (hadamardReg (mk34_rHoldGen mHold mRest hmScr
    rScr))
  have hH_pres := mk34_hadamardReg_preserves_projZeroAll (mk34_rHoldGen mHold mRest hmScr rScr)
    (mk34_rRestGen mHold mRest hmScr rScr).wires
    (fun i j ↦ (mk34_rHoldGen_disjoint_rRestGen mHold mRest hmScr rScr).ne i j)
  have hInner_pres : P * ((mk34_cCompGenInner mHold mRest mSub hmScr hmSub cLeafOn ctx rCore rScr
    hCS).eval.1 * P) =
      (mk34_cCompGenInner mHold mRest mSub hmScr hmSub cLeafOn ctx rCore rScr hCS).eval.1 * P := by
    apply MeasureBranchHadamardSem.matrix_ext_ket
    intro β
    dsimp only [P]
    rw [mul_mulVec_prog, mul_mulVec_prog, ket_projZeroAll]
    by_cases hz : ∀ j : Fin mRest, β (mk34_rRestGen mHold mRest hmScr rScr j) = 0
    · have hSub0 : ∀ j : Fin mSub,
          β (mk34_rSubRestGen mHold mRest hmScr 0 mSub (by omega) rScr j) = 0 := fun j ↦ by
        dsimp only [mk34_rSubRestGen]
        rw [QRegister.slice_apply]
        exact hz ⟨0 + j.val, by omega⟩
      have hk := mk34_cCompGenInner_eval_ket mHold mRest mSub hmScr hmSub cLeafOn fLeaf ctx q0
        holdVec rCore rScr hCS hLeafKet hpBits hfSpec β hSub0
      rw [← mbh_ket_eq_ket] at hk
      rw [ite_eq_left hz, hk, Matrix.mulVec_smul, ket_projZeroAll, ite_eq_left hz]
    · rw [ite_eq_right hz, Matrix.mulVec_zero, Matrix.mulVec_zero]
  have h123 := RealizesCleanUnitary.seq hP hH_real
    (RealizesCleanUnitary.seq hP hInnerRest hH_real hInner_pres) hH_pres
  have hU_eq : ((hadamardReg (mk34_rHoldGen mHold mRest hmScr rScr)).eval *
      (mk34_cCompGenInner mHold mRest mSub hmScr hmSub cLeafOn ctx rCore rScr hCS).eval) *
      (hadamardReg (mk34_rHoldGen mHold mRest hmScr rScr)).eval =
      (mk34_cCompGen mHold mRest mSub hmScr hmSub cLeafOn ctx rCore rScr hCS).eval := by
    simp [mk34_cCompGen, Circuit.eval_seq, mul_assoc]
  dsimp only [mk34_dCompGen]
  rwa [hU_eq] at h123
/-  Stage B reversible `Circuit n` for `dKickZeroSub46OptDyn` (`15 + B + 3` Toffoli pairs). -/
/-  Stage B `0`-`.TOFF` `DynamicCircuit Var n` (`4 * B + 72` `T`) for `dKickZeroSub46OptDyn`. -/
theorem mk34_cCompGen_preserves_rest {n mScr : ℕ} (mHold mRest mSub : ℕ)
    (hmScr : mHold + mRest ≤ mScr) (hmSub : mSub ≤ mRest)
    (cLeafOn : QRegister ((86 + mHold) + mSub) n → Circuit n)
    (ctx : TempCtx ((86 + mHold) + mSub))
    (holdVec : QRegister posCoreWires n → BitAssignment n → BitAssignment mHold)
    (rCore : QRegister posCoreWires n) (rScr : QRegister mScr n) (hCS : rCore.DisjointWires rScr)
    (hEval : ∀ β : BitAssignment n,
      (∀ j : Fin mSub, β (mk34_rSubRestGen mHold mRest hmScr 0 mSub (by omega) rScr j) = 0) →
      (mk34_cCompGen mHold mRest mSub hmScr hmSub cLeafOn ctx rCore rScr hCS).eval.1.mulVec (ket
        β) =
        ket (writeReg β (mk34_rHoldGen mHold mRest hmScr rScr)
          (fun i ↦ β (mk34_rHoldGen mHold mRest hmScr rScr i) + holdVec rCore β i))) :
    let P := projZeroAll mRest (mk34_rRestGen mHold mRest hmScr rScr).wires
    P * ((mk34_cCompGen mHold mRest mSub hmScr hmSub cLeafOn ctx rCore rScr hCS).eval.1 * P) =
      (mk34_cCompGen mHold mRest mSub hmScr hmSub cLeafOn ctx rCore rScr hCS).eval.1 * P := by
  intro P
  apply MeasureBranchHadamardSem.matrix_ext_ket
  intro β
  dsimp only [P]
  rw [mul_mulVec_prog, mul_mulVec_prog, ket_projZeroAll]
  by_cases hz : ∀ j : Fin mRest, β (mk34_rRestGen mHold mRest hmScr rScr j) = 0
  · have hSub0 : ∀ j : Fin mSub,
        β (mk34_rSubRestGen mHold mRest hmScr 0 mSub (by omega) rScr j) = 0 := fun j ↦ by
      dsimp only [mk34_rSubRestGen]
      rw [QRegister.slice_apply]
      exact hz ⟨0 + j.val, by omega⟩
    have hk := hEval β hSub0
    rw [← mbh_ket_eq_ket, ← mbh_ket_eq_ket] at hk
    have hz' : ∀ j : Fin mRest, writeReg β (mk34_rHoldGen mHold mRest hmScr rScr)
        (fun i ↦ β (mk34_rHoldGen mHold mRest hmScr rScr i) + holdVec rCore β i)
        (mk34_rRestGen mHold mRest hmScr rScr j) = 0 := fun j ↦
      (writeReg_apply_of_not_mem β (mk34_rHoldGen mHold mRest hmScr rScr) _ _
        (fun ⟨i, hi⟩ ↦ (mk34_rHoldGen_disjoint_rRestGen mHold mRest hmScr rScr).ne i j hi)).trans
          (hz j)
    rw [ite_eq_left hz, hk, ket_projZeroAll, ite_eq_left hz']
  · rw [ite_eq_right hz, Matrix.mulVec_zero, Matrix.mulVec_zero]
theorem mk34_rCombGen_disjoint_subAfter {n mScr : ℕ} (mHold mRest mSub len : ℕ)
    (hmScr : mHold + mRest ≤ mScr) (hmSub : mSub ≤ mRest) (hsub : mSub + len ≤ mRest)
    (rCore : QRegister posCoreWires n) (rScr : QRegister mScr n) (hCS : rCore.DisjointWires rScr) :
    (mk34_rCombGen mHold mRest mSub hmScr hmSub rCore rScr hCS).DisjointWires
      (mk34_rSubRestGen mHold mRest hmScr mSub len hsub rScr) := by
  have hAct := mk34_rActGen_disjoint_sub mHold mRest mSub len hmScr hsub rCore rScr hCS
  have hSub := mk34_rSubRestGen_disjoint mHold mRest hmScr 0 mSub mSub len (by omega) hsub (by
    omega) rScr
  exact QRegister.disjoint_iff.mpr fun a b heq ↦
    Fin.addCases (m := 86 + mHold) (n := mSub)
      (motive := fun a ↦ mk34_rCombGen mHold mRest mSub hmScr hmSub rCore rScr hCS a =
        mk34_rSubRestGen mHold mRest hmScr mSub len hsub rScr b → False)
      (fun i hi ↦ hAct.ne i b ((QRegister.concat_apply_left _ _ _ i).symm.trans hi))
      (fun j hj ↦ hSub.ne j b ((QRegister.concat_apply_right _ _ _ j).symm.trans hj)) a heq
theorem mk34_rCombGen_disjoint_rOutTop {n mScr : ℕ} (mHold mRest mSub kOut : ℕ)
    (hmScr : mHold + mRest ≤ mScr) (hmSub : mSub ≤ mRest)
    (rCore : QRegister posCoreWires n) (rOutTop : QRegister kOut n) (rScr : QRegister mScr n)
    (hCOut : rCore.DisjointWires rOutTop) (hCS : rCore.DisjointWires rScr)
    (hOutS : rOutTop.DisjointWires rScr) :
    (mk34_rCombGen mHold mRest mSub hmScr hmSub rCore rScr hCS).DisjointWires rOutTop := by
  have h1 : (mk34_rCoreHi86 rCore).DisjointWires rOutTop := hCOut.compose_left _
  have h2 : (mk34_rHoldGen mHold mRest hmScr rScr).DisjointWires rOutTop :=
    (QRegExt.disjointWires_symm (hOutS.compose_right _))
  have h3 : (mk34_rSubRestGen mHold mRest hmScr 0 mSub (by omega) rScr).DisjointWires rOutTop :=
    (QRegExt.disjointWires_symm ((hOutS.compose_right _).compose_right _))
  refine QRegister.disjoint_iff.mpr fun a b heq ↦
    Fin.addCases (m := 86 + mHold) (n := mSub)
      (motive := fun a ↦ mk34_rCombGen mHold mRest mSub hmScr hmSub rCore rScr hCS a = rOutTop b →
        False)
      (fun i hi ↦ ?_)
      (fun j hj ↦ h3.ne j b ((QRegister.concat_apply_right _ _ _ j).symm.trans hj)) a heq
  dsimp only [mk34_rCombGen] at hi
  rw [QRegister.concat_apply_left] at hi
  exact Fin.addCases (m := 86) (n := mHold)
    (motive := fun i ↦ mk34_rActGen mHold mRest hmScr rCore rScr hCS i = rOutTop b → False)
    (fun i₀ hi₀ ↦ h1.ne i₀ b ((QRegister.concat_apply_left _ _ _ i₀).symm.trans hi₀))
    (fun j₀ hj₀ ↦ h2.ne j₀ b ((QRegister.concat_apply_right _ _ _ j₀).symm.trans hj₀)) i hi
def mk34_hold3IdxGen {mScr : ℕ} (mHold mRest mSubB : ℕ) (hmScr : mHold + mRest ≤ mScr)
    (hmSubB : mSubB ≤ mRest) (jU1 jVL : Fin mSubB) (hjNe : jU1 ≠ jVL) (iD3 : Fin mHold) :
    Fin 3 ↪ Fin mScr where
  toFun k :=
    if k.val = 0 then ⟨mHold + jU1.val, by omega⟩
    else if k.val = 1 then ⟨mHold + jVL.val, by omega⟩
    else ⟨iD3.val, by omega⟩
  inj' a b h := by
    have hv := congrArg Fin.val h
    fin_cases a
    · fin_cases b
      · rfl
      · dsimp at hv
        exact False.elim (hjNe (Fin.ext (by omega)))
      · dsimp at hv
        omega
    · fin_cases b
      · dsimp at hv
        exact False.elim (hjNe (Fin.ext (by omega)))
      · rfl
      · dsimp at hv
        omega
    · fin_cases b
      · dsimp at hv
        omega
      · dsimp at hv
        omega
      · rfl
def mk34_rHold3Gen {n mScr : ℕ} (mHold mRest mSubB : ℕ) (hmScr : mHold + mRest ≤ mScr)
    (hmSubB : mSubB ≤ mRest) (jU1 jVL : Fin mSubB) (hjNe : jU1 ≠ jVL) (iD3 : Fin mHold)
    (rScr : QRegister mScr n) : QRegister 3 n :=
  ⟨(mk34_hold3IdxGen mHold mRest mSubB hmScr hmSubB jU1 jVL hjNe iD3).trans rScr.wires⟩
theorem mk34_rCore_disjoint_rHold3Gen {n mScr : ℕ} (mHold mRest mSubB : ℕ)
    (hmScr : mHold + mRest ≤ mScr) (hmSubB : mSubB ≤ mRest) (jU1 jVL : Fin mSubB)
    (hjNe : jU1 ≠ jVL) (iD3 : Fin mHold) (rCore : QRegister posCoreWires n)
    (rScr : QRegister mScr n) (hCS : rCore.DisjointWires rScr) :
    rCore.DisjointWires (mk34_rHold3Gen mHold mRest mSubB hmScr hmSubB jU1 jVL hjNe iD3 rScr) :=
  QRegister.disjoint_iff.mpr fun c _k h ↦ hCS.ne c _ h
theorem mk34_rHold3Gen_disjoint_rOutTop {n mScr : ℕ} (mHold mRest mSubB kOut : ℕ)
    (hmScr : mHold + mRest ≤ mScr) (hmSubB : mSubB ≤ mRest) (jU1 jVL : Fin mSubB)
    (hjNe : jU1 ≠ jVL) (iD3 : Fin mHold) (rOutTop : QRegister kOut n)
    (rScr : QRegister mScr n) (hOutS : rOutTop.DisjointWires rScr) :
    (mk34_rHold3Gen mHold mRest mSubB hmScr hmSubB jU1 jVL hjNe iD3 rScr).DisjointWires rOutTop :=
  QRegister.disjoint_iff.mpr fun _k j h ↦ hOutS.ne j _ h.symm
theorem mk34_rHold3Gen_disjoint_subAfter {n mScr : ℕ} (mHold mRest mSubB len : ℕ)
    (hmScr : mHold + mRest ≤ mScr) (hmSubB : mSubB ≤ mRest) (hsub : mSubB + len ≤ mRest)
    (jU1 jVL : Fin mSubB) (hjNe : jU1 ≠ jVL) (iD3 : Fin mHold) (rScr : QRegister mScr n) :
    (mk34_rHold3Gen mHold mRest mSubB hmScr hmSubB jU1 jVL hjNe iD3 rScr).DisjointWires
      (mk34_rSubRestGen mHold mRest hmScr mSubB len hsub rScr) :=
  QRegister.disjoint_iff.mpr fun k j h ↦ by
    change rScr (mk34_hold3IdxGen mHold mRest mSubB hmScr hmSubB jU1 jVL hjNe iD3 k) = _ at h
    dsimp only [mk34_rSubRestGen, mk34_rRestGen] at h
    rw [QRegister.slice_apply, QRegister.slice_apply] at h
    have hv := congrArg Fin.val (rScr.wires.injective h)
    fin_cases k
    · dsimp [mk34_hold3IdxGen] at hv
      omega
    · dsimp [mk34_hold3IdxGen] at hv
      omega
    · dsimp [mk34_hold3IdxGen] at hv
      omega
def mk34_mapGenToMBInPlace {n : ℕ} (B mHold mSubB : ℕ) (jU1 jVL : Fin mSubB) (iD3 : Fin mHold)
    (rCore : QRegister posCoreWires n) (rOutTop : QRegister (B + 1) n)
    (rSubB3 : QRegister (B + 3) n) (γ : BitAssignment ((86 + mHold) + mSubB))
    (β : BitAssignment n) : BitAssignment (mk34_mB B) :=
  fun idx ↦
    if h1 : idx.val < 86 then
      if idx.val = 38 + (29 - B) then β (rCore ⟨3, by decide⟩)
      else γ ⟨idx.val, by omega⟩
    else if idx.val = 86 then γ ⟨(86 + mHold) + jU1.val, by omega⟩
    else if idx.val = 87 then γ ⟨(86 + mHold) + jVL.val, by omega⟩
    else if idx.val = 88 then γ ⟨86 + iD3.val, by omega⟩
    else if h2 : idx.val < 89 + (B + 1) then β (rOutTop ⟨idx.val - 89, by omega⟩)
    else if idx.val = 90 + B then γ ⟨38 + (29 - B), by omega⟩
    else β (rSubB3 ⟨idx.val - (90 + B + 1), by
      have hlt := idx.isLt
      dsimp [mk34_mB] at hlt
      omega⟩)
theorem mk34_mapGenToMBInPlace_writeRegProg {n mScr : ℕ} (B mHold mRest mSubB : ℕ)
    (hmScr : mHold + mRest ≤ mScr) (hsub : mSubB + (B + 3) ≤ mRest)
    (jU1 jVL : Fin mSubB) (iD3 : Fin mHold)
    (rCore : QRegister posCoreWires n) (rOutTop : QRegister (B + 1) n) (rScr : QRegister mScr n)
    (hCOut : rCore.DisjointWires rOutTop) (hCS : rCore.DisjointWires rScr)
    (hOutS : rOutTop.DisjointWires rScr)
    (γ γ' : BitAssignment ((86 + mHold) + mSubB)) (β : BitAssignment n) :
    let rCombB := mk34_rCombGen mHold mRest mSubB hmScr (by omega) rCore rScr hCS
    let rSubB3 := mk34_rSubRestGen mHold mRest hmScr mSubB (B + 3) hsub rScr
    mk34_mapGenToMBInPlace B mHold mSubB jU1 jVL iD3 rCore rOutTop rSubB3 γ
        (writeRegProg β rCombB γ') =
      mk34_mapGenToMBInPlace B mHold mSubB jU1 jVL iD3 rCore rOutTop rSubB3 γ β := by
  intro rCombB rSubB3
  have hDisjOut := mk34_rCombGen_disjoint_rOutTop mHold mRest mSubB (B + 1) hmScr (by omega)
    rCore rOutTop rScr hCOut hCS hOutS
  have hDisjSub := mk34_rCombGen_disjoint_subAfter mHold mRest mSubB (B + 3) hmScr (by omega)
    hsub rCore rScr hCS
  have hCore3Not : rCore ⟨3, by decide⟩ ∉ Set.range rCombB.wires := by
    rintro ⟨a, ha⟩
    refine Fin.addCases (m := 86 + mHold) (n := mSubB)
      (motive := fun a ↦ rCombB a = rCore ⟨3, by decide⟩ → False)
      (fun i hi ↦ ?_)
      (fun j hj ↦ ((hCS.compose_right _).compose_right _).ne ⟨3, by decide⟩ j
        (((QRegister.concat_apply_right _ _ _ j).symm.trans hj).symm)) a ha
    dsimp only [rCombB, mk34_rCombGen] at hi
    rw [QRegister.concat_apply_left] at hi
    exact Fin.addCases (m := 86) (n := mHold)
      (motive := fun i ↦ mk34_rActGen mHold mRest hmScr rCore rScr hCS i =
        rCore ⟨3, by decide⟩ → False)
      (fun i₀ hi₀ ↦ by
        rw [QRegister.concat_apply_left] at hi₀
        dsimp only [mk34_rCoreHi86] at hi₀
        rw [QRegister.slice_apply] at hi₀
        have hv := congrArg Fin.val (rCore.wires.injective hi₀)
        dsimp at hv
        omega)
      (fun j₀ hj₀ ↦ by
        rw [QRegister.concat_apply_right] at hj₀
        exact (hCS.compose_right _).ne ⟨3, by decide⟩ j₀ hj₀.symm) i hi
  funext idx
  dsimp only [mk34_mapGenToMBInPlace]
  split_ifs with h1 h1a h2 h3 h4 h5 h6
  · exact writeRegProg_apply_of_not_mem β rCombB γ' _ hCore3Not
  · rfl
  · rfl
  · rfl
  · rfl
  · exact mk34_writeRegProg_leafScr_eq rCombB rOutTop hDisjOut β γ' _
  · rfl
  · exact mk34_writeRegProg_leafScr_eq rCombB rSubB3 hDisjSub β γ' _
theorem mk34_mapGenToMBInPlace_eq_rCombBInPlace {n mScr : ℕ}
    (B : ℕ) (hB1 : 1 ≤ B) (hB27 : B ≤ 27) (mHold mRest mSubB : ℕ)
    (hmScr : mHold + mRest ≤ mScr) (hsub : mSubB + (B + 3) ≤ mRest)
    (jU1 jVL : Fin mSubB) (hjNe : jU1 ≠ jVL) (iD3 : Fin mHold)
    (rCore : QRegister posCoreWires n) (rOutTop : QRegister (B + 1) n) (rScr : QRegister mScr n)
    (hCOut : rCore.DisjointWires rOutTop) (hCS : rCore.DisjointWires rScr)
    (hOutS : rOutTop.DisjointWires rScr) (β : BitAssignment n) :
    let rCombOuter := mk34_rCombGen mHold mRest mSubB hmScr (by omega) rCore rScr hCS
    let rHold3 := mk34_rHold3Gen mHold mRest mSubB hmScr (by omega) jU1 jVL hjNe iD3 rScr
    let rSubB3 := mk34_rSubRestGen mHold mRest hmScr mSubB (B + 3) hsub rScr
    let rCombB := mk34_rCombBInPlace B hB1 hB27 rCore rHold3 rOutTop rSubB3
      (mk34_rCore_disjoint_rHold3Gen mHold mRest mSubB hmScr (by omega) jU1 jVL hjNe iD3 rCore rScr
        hCS)
      hCOut
      (mk34_rHold3Gen_disjoint_rOutTop mHold mRest mSubB (B + 1) hmScr (by omega) jU1 jVL hjNe iD3
        rOutTop rScr hOutS)
      ((hCS.compose_right _).compose_right _)
      (mk34_rHold3Gen_disjoint_subAfter mHold mRest mSubB (B + 3) hmScr (by omega) hsub jU1 jVL hjNe
        iD3 rScr)
      ((hOutS.compose_right _).compose_right _)
    mk34_mapGenToMBInPlace B mHold mSubB jU1 jVL iD3 rCore rOutTop rSubB3
        (fun idx ↦ β (rCombOuter idx)) β =
      (fun idx ↦ β (rCombB idx)) := by
  intro rCombOuter rHold3 rSubB3 rCombB
  funext idx
  dsimp only [mk34_mapGenToMBInPlace]
  by_cases h1 : idx.val < 86
  · rw [dite_eq_left h1]
    by_cases h1a : idx.val = 38 + (29 - B)
    · rw [ite_eq_left h1a]
      have hidx : idx = Fin.castAdd (B + 4) (Fin.castAdd (B + 1) (Fin.castAdd 3 ⟨idx.val, h1⟩)) :=
        Fin.ext rfl
      conv_rhs =>
        rw [hidx]
        dsimp only [rCombB, mk34_rCombBInPlace]
        rw [QRegister.concat_apply_left, QRegister.concat_apply_left, QRegister.concat_apply_left]
      change β (rCore ⟨3, by decide⟩) =
        β (rCore (if idx.val = 38 + (29 - B) then ⟨3, by decide⟩ else _))
      rw [ite_eq_left h1a]
    · rw [ite_eq_right h1a]
      have hidx : idx = ⟨(⟨idx.val, h1⟩ : Fin 86).val, by
        dsimp [mk34_mB]
        omega⟩ := Fin.ext rfl
      rw [mk34_rCombGen_core mHold mRest mSubB hmScr (by omega) rCore rScr hCS ⟨idx.val, h1⟩]
      conv_rhs => rw [hidx]
      exact congrArg β (mk34_rCombBInPlace_core_ne B hB1 hB27 rCore rHold3 rOutTop rSubB3
        _ _ _ _ _ _ ⟨idx.val, h1⟩ h1a).symm
  · rw [dite_eq_right h1]
    by_cases h86 : idx.val = 86
    · rw [ite_eq_left h86]
      have hidx : idx = ⟨86 + (0 : Fin 3).val, by
        dsimp [mk34_mB]
        omega⟩ := Fin.ext h86
      rw [mk34_rCombGen_sub mHold mRest mSubB hmScr (by omega) rCore rScr hCS jU1,
          hidx, mk34_rCombBInPlace_hold B hB1 hB27 rCore rHold3 rOutTop rSubB3 _ _ _ _ _ _ 0]
      change β ((mk34_rSubRestGen mHold mRest hmScr 0 mSubB (by omega) rScr) jU1) =
        β (rScr (mk34_hold3IdxGen mHold mRest mSubB hmScr (by omega) jU1 jVL hjNe iD3 0))
      dsimp only [mk34_rSubRestGen, mk34_rRestGen]
      rw [QRegister.slice_apply, QRegister.slice_apply]
      exact congrArg (fun x ↦ β (rScr x)) (Fin.ext (by
        dsimp [mk34_hold3IdxGen]
        omega))
    · rw [ite_eq_right h86]
      by_cases h87 : idx.val = 87
      · rw [ite_eq_left h87]
        have hidx : idx = ⟨86 + (1 : Fin 3).val, by
          dsimp [mk34_mB]
          omega⟩ := Fin.ext h87
        rw [mk34_rCombGen_sub mHold mRest mSubB hmScr (by omega) rCore rScr hCS jVL,
            hidx, mk34_rCombBInPlace_hold B hB1 hB27 rCore rHold3 rOutTop rSubB3 _ _ _ _ _ _ 1]
        change β ((mk34_rSubRestGen mHold mRest hmScr 0 mSubB (by omega) rScr) jVL) =
          β (rScr (mk34_hold3IdxGen mHold mRest mSubB hmScr (by omega) jU1 jVL hjNe iD3 1))
        dsimp only [mk34_rSubRestGen, mk34_rRestGen]
        rw [QRegister.slice_apply, QRegister.slice_apply]
        exact congrArg (fun x ↦ β (rScr x)) (Fin.ext (by
          dsimp [mk34_hold3IdxGen]
          omega))
      · rw [ite_eq_right h87]
        by_cases h88 : idx.val = 88
        · rw [ite_eq_left h88]
          have hidx : idx = ⟨86 + (2 : Fin 3).val, by
            dsimp [mk34_mB]
            omega⟩ := Fin.ext h88
          rw [mk34_rCombGen_hold mHold mRest mSubB hmScr (by omega) rCore rScr hCS iD3,
              hidx, mk34_rCombBInPlace_hold B hB1 hB27 rCore rHold3 rOutTop rSubB3 _ _ _ _ _ _ 2]
          change β ((mk34_rHoldGen mHold mRest hmScr rScr) iD3) =
            β (rScr (mk34_hold3IdxGen mHold mRest mSubB hmScr (by omega) jU1 jVL hjNe iD3 2))
          dsimp only [mk34_rHoldGen]
          rw [QRegister.slice_apply]
          exact congrArg (fun x ↦ β (rScr x)) (Fin.ext (by
            dsimp [mk34_hold3IdxGen]
            omega))
        · rw [ite_eq_right h88]
          by_cases hOut : idx.val < 89 + (B + 1)
          · rw [dite_eq_left hOut]
            let jOut : Fin (B + 1) := ⟨idx.val - 89, by omega⟩
            have hidx : idx = ⟨89 + jOut.val, by
              dsimp [mk34_mB]
              omega⟩ := by
              apply Fin.ext
              dsimp [jOut]
              omega
            conv_rhs => rw [hidx]
            exact congrArg β (mk34_rCombBInPlace_out B hB1 hB27 rCore rHold3 rOutTop rSubB3
              _ _ _ _ _ _ jOut).symm
          · rw [dite_eq_right hOut]
            by_cases hPrev : idx.val = 90 + B
            · rw [ite_eq_left hPrev]
              have hidx : idx = ⟨90 + B, by
                dsimp [mk34_mB]
                omega⟩ := Fin.ext hPrev
              rw [mk34_rCombGen_core mHold mRest mSubB hmScr (by omega) rCore rScr hCS
                    ⟨38 + (29 - B), by omega⟩]
              conv_rhs => rw [hidx]
              exact congrArg β (mk34_rCombBInPlace_prev B hB1 hB27 rCore rHold3 rOutTop rSubB3
                _ _ _ _ _ _).symm
            · rw [ite_eq_right hPrev]
              have hlt := idx.isLt
              dsimp [mk34_mB] at hlt
              let j : Fin (B + 3) := ⟨idx.val - (90 + B + 1), by omega⟩
              have hidx : rCombB idx = tailScr rCombB (B + 3) (by
                  dsimp [mk34_mB]
                  omega) j := by
                dsimp only [tailScr, j]
                congr 1
                apply Fin.ext
                dsimp [mk34_mB]
                omega
              rw [hidx, congrFun (mk34_tailScr_rCombBInPlace B hB1 hB27 rCore rHold3 rOutTop rSubB3
                _ _ _ _ _ _) j]
/-  Top-level `(B + 19)`-clean-wire (`≤ 46` for `B ≤ 27`) reversible `Circuit n` for the 3-stage
mid-phase kickback. -/
/-  Top-level `(B + 19)`-clean-wire (`≤ 46` for `B ≤ 27`) `0`-`.TOFF` `DynamicCircuit Var n`
(`136 + 4 * B` `T`). -/
def mk34_cStageBGen {n mScr : ℕ} (B : ℕ) (hB1 : 1 ≤ B) (hB27 : B ≤ 27)
    (mHold mRest mSubB : ℕ) (hmScr : mHold + mRest ≤ mScr) (hsub : mSubB + (B + 3) ≤ mRest)
    (jU1 jVL : Fin mSubB) (hjNe : jU1 ≠ jVL) (iD3 : Fin mHold)
    (ctxB : TempCtx ((86 + mHold) + mSubB))
    (rCore : QRegister posCoreWires n) (rOutTop : QRegister (B + 1) n) (rScr : QRegister mScr n)
    (hCOut : rCore.DisjointWires rOutTop) (hCS : rCore.DisjointWires rScr)
    (hOutS : rOutTop.DisjointWires rScr) : Circuit n :=
  let rCombOuter := mk34_rCombGen mHold mRest mSubB hmScr (by omega) rCore rScr hCS
  let rHold3 := mk34_rHold3Gen mHold mRest mSubB hmScr (by omega) jU1 jVL hjNe iD3 rScr
  let rSubB3 := mk34_rSubRestGen mHold mRest hmScr mSubB (B + 3) hsub rScr
  let cLeaf := mk34_cMidKickBInPlace B hB1 hB27 rCore rHold3 rOutTop rSubB3
    (mk34_rCore_disjoint_rHold3Gen mHold mRest mSubB hmScr (by omega) jU1 jVL hjNe iD3 rCore rScr
      hCS)
    hCOut
    (mk34_rHold3Gen_disjoint_rOutTop mHold mRest mSubB (B + 1) hmScr (by omega) jU1 jVL hjNe iD3
      rOutTop rScr hOutS)
    ((hCS.compose_right _).compose_right _)
    (mk34_rHold3Gen_disjoint_subAfter mHold mRest mSubB (B + 3) hmScr (by omega) hsub jU1 jVL hjNe
      iD3 rScr)
    ((hOutS.compose_right _).compose_right _)
  mk34_ctxToToff rCombOuter cLeaf ctxB
def mk34_dStageBGen {Var : Type} {n mScr : ℕ} (B : ℕ) (hB1 : 1 ≤ B) (hB27 : B ≤ 27)
    (mHold mRest mSubB : ℕ) (hmScr : mHold + mRest ≤ mScr) (hsub : mSubB + (B + 3) ≤ mRest)
    (jU1 jVL : Fin mSubB) (hjNe : jU1 ≠ jVL) (iD3 : Fin mHold)
    (ctxB : TempCtx ((86 + mHold) + mSubB)) (v : Var)
    (rCore : QRegister posCoreWires n) (rOutTop : QRegister (B + 1) n) (rScr : QRegister mScr n)
    (hCOut : rCore.DisjointWires rOutTop) (hCS : rCore.DisjointWires rScr)
    (hOutS : rOutTop.DisjointWires rScr) : DynamicCircuit Var n :=
  let rCombOuter := mk34_rCombGen mHold mRest mSubB hmScr (by omega) rCore rScr hCS
  let rHold3 := mk34_rHold3Gen mHold mRest mSubB hmScr (by omega) jU1 jVL hjNe iD3 rScr
  let rSubB3 := mk34_rSubRestGen mHold mRest hmScr mSubB (B + 3) hsub rScr
  let dLeaf := mk34_dMidKickBInPlace B hB1 hB27 v rCore rHold3 rOutTop rSubB3
    (mk34_rCore_disjoint_rHold3Gen mHold mRest mSubB hmScr (by omega) jU1 jVL hjNe iD3 rCore rScr
      hCS)
    hCOut
    (mk34_rHold3Gen_disjoint_rOutTop mHold mRest mSubB (B + 1) hmScr (by omega) jU1 jVL hjNe iD3
      rOutTop rScr hOutS)
    ((hCS.compose_right _).compose_right _)
    (mk34_rHold3Gen_disjoint_subAfter mHold mRest mSubB (B + 3) hmScr (by omega) hsub jU1 jVL hjNe
      iD3 rScr)
    ((hOutS.compose_right _).compose_right _)
  mk34_ctxToDynNested v rCombOuter dLeaf ctxB
theorem mk34_dStageBGen_preservesStoreConst {Var : Type} [Fintype Var] [DecidableEq Var]
    {n mScr : ℕ} (B : ℕ) (hB1 : 1 ≤ B) (hB27 : B ≤ 27) (mHold mRest mSubB : ℕ)
    (hmScr : mHold + mRest ≤ mScr) (hsub : mSubB + (B + 3) ≤ mRest)
    (jU1 jVL : Fin mSubB) (hjNe : jU1 ≠ jVL) (iD3 : Fin mHold)
    (ctxB : TempCtx ((86 + mHold) + mSubB)) (v : Var)
    (rCore : QRegister posCoreWires n) (rOutTop : QRegister (B + 1) n) (rScr : QRegister mScr n)
    (hCOut : rCore.DisjointWires rOutTop) (hCS : rCore.DisjointWires rScr)
    (hOutS : rOutTop.DisjointWires rScr) :
    PreservesStoreConst (mk34_dStageBGen B hB1 hB27 mHold mRest mSubB hmScr hsub jU1 jVL hjNe
      iD3 ctxB v rCore rOutTop rScr hCOut hCS hOutS) :=
  mk34_ctxToDynNested_preservesStoreConst v _ _
    (mk34_dMidKickBInPlace_preservesStoreConst B hB1 hB27 v _ _ _ _ _ _ _ _ _ _) ctxB
theorem mk34_projZeroAll_tailScr_stageBGen {n mScr : ℕ} (B mHold mRest mSubB : ℕ)
    (hmScr : mHold + mRest ≤ mScr) (hsub : mSubB + (B + 3) ≤ mRest)
    (rCore : QRegister posCoreWires n) (rScr : QRegister mScr n) (hCS : rCore.DisjointWires rScr) :
    let rCombOuter := mk34_rCombGen mHold mRest mSubB hmScr (by omega) rCore rScr hCS
    let rSubB3 := mk34_rSubRestGen mHold mRest hmScr mSubB (B + 3) hsub rScr
    let hDisj := mk34_rCombGen_disjoint_subAfter mHold mRest mSubB (B + 3) hmScr (by omega) hsub
      rCore rScr hCS
    projZeroAll (mSubB + (B + 3))
        (tailScr (rCombOuter.concat rSubB3 hDisj) (mSubB + (B + 3)) (by omega)) *
      projZeroAll mRest (mk34_rRestGen mHold mRest hmScr rScr).wires =
      projZeroAll mRest (mk34_rRestGen mHold mRest hmScr rScr).wires := by
  intro rCombOuter rSubB3 hDisj
  apply MeasureBranchHadamardSem.matrix_ext_ket
  intro β
  rw [mul_mulVec_prog, ket_projZeroAll]
  by_cases hz : ∀ s : Fin mRest, β (mk34_rRestGen mHold mRest hmScr rScr s) = 0
  · rw [ite_eq_left hz, ket_projZeroAll, ite_eq_left]
    rw [mk34_tailScr_concat_split rCombOuter rSubB3 hDisj mSubB (by omega) β]
    refine ⟨fun w hw ↦ ?_, fun j ↦ ?_⟩
    · have hwEq := mk34_rCombGen_sub mHold mRest mSubB hmScr (by omega) rCore rScr hCS
        ⟨w.val - (86 + mHold), by omega⟩
      have hfin : (⟨(86 + mHold) + (w.val - (86 + mHold)), by omega⟩ :
          Wire ((86 + mHold) + mSubB)) = w := by
        apply Fin.ext
        dsimp
        omega
      rw [hfin] at hwEq
      change β (rCombOuter w) = 0
      rw [hwEq]
      dsimp only [mk34_rSubRestGen]
      rw [QRegister.slice_apply]
      exact hz ⟨0 + (w.val - (86 + mHold)), by omega⟩
    · dsimp only [rSubB3, mk34_rSubRestGen]
      rw [QRegister.slice_apply]
      exact hz ⟨mSubB + j.val, by omega⟩
  · rw [ite_eq_right hz, Matrix.mulVec_zero]
theorem mk34_lt_mB {B k : ℕ} (hk : k < 94 + 2 * B) : k < mk34_mB B := by
  dsimp [mk34_mB]
  omega
theorem mk34_lt_posCore {k : ℕ} (hk : k < 4034) : k < posCoreWires := by
  dsimp [posCoreWires]
  omega
theorem mk34_count_dCompGen_toff {Var : Type} {n mScr : ℕ} (mHold mRest mSub : ℕ)
    (hmScr : mHold + mRest ≤ mScr) (hmSub : mSub ≤ mRest) (v : Var)
    (cLeafOn : QRegister ((86 + mHold) + mSub) n → Circuit n)
    (ctx : TempCtx ((86 + mHold) + mSub)) (rCore : QRegister posCoreWires n)
    (rScr : QRegister mScr n) (hCS : rCore.DisjointWires rScr)
    (hLeaf : ∀ rComb, (cLeafOn rComb).count PrimitiveGate.TOFF = 0) :
    (mk34_dCompGen mHold mRest mSub hmScr hmSub v cLeafOn ctx rCore rScr hCS).count
      PrimitiveGate.TOFF = 0 := by
  simp [mk34_dCompGen, mk34_dCompGenInner, mk34_ctxToDyn_count_toff, hLeaf]
theorem mk34_count_dCompGen_t {Var : Type} {n mScr : ℕ} (mHold mRest mSub : ℕ)
    (hmScr : mHold + mRest ≤ mScr) (hmSub : mSub ≤ mRest) (v : Var)
    (cLeafOn : QRegister ((86 + mHold) + mSub) n → Circuit n)
    (ctx : TempCtx ((86 + mHold) + mSub)) (rCore : QRegister posCoreWires n)
    (rScr : QRegister mScr n) (hCS : rCore.DisjointWires rScr)
    (hLeaf : ∀ rComb, (cLeafOn rComb).count PrimitiveGate.T = 0) :
    (mk34_dCompGen mHold mRest mSub hmScr hmSub v cLeafOn ctx rCore rScr hCS).count
      PrimitiveGate.T = 4 * ctx.countTempAnd := by
  simp [mk34_dCompGen, mk34_dCompGenInner, mk34_ctxToDyn_count_t, hLeaf]
theorem mk34_count_dStageBGen_toff {Var : Type} {n mScr : ℕ} (B : ℕ) (hB1 : 1 ≤ B) (hB27 : B ≤ 27)
    (mHold mRest mSubB : ℕ) (hmScr : mHold + mRest ≤ mScr) (hsub : mSubB + (B + 3) ≤ mRest)
    (jU1 jVL : Fin mSubB) (hjNe : jU1 ≠ jVL) (iD3 : Fin mHold)
    (ctxB : TempCtx ((86 + mHold) + mSubB)) (v : Var)
    (rCore : QRegister posCoreWires n) (rOutTop : QRegister (B + 1) n) (rScr : QRegister mScr n)
    (hCOut : rCore.DisjointWires rOutTop) (hCS : rCore.DisjointWires rScr)
    (hOutS : rOutTop.DisjointWires rScr) :
    (mk34_dStageBGen B hB1 hB27 mHold mRest mSubB hmScr hsub jU1 jVL hjNe iD3 ctxB v
      rCore rOutTop rScr hCOut hCS hOutS).count PrimitiveGate.TOFF = 0 := by
  simp [mk34_dStageBGen, mk34_ctxToDynNested_count_toff, mk34_count_dMidKickBInPlace_toff]
theorem mk34_count_dStageBGen_t {Var : Type} {n mScr : ℕ} (B : ℕ) (hB1 : 1 ≤ B) (hB27 : B ≤ 27)
    (mHold mRest mSubB : ℕ) (hmScr : mHold + mRest ≤ mScr) (hsub : mSubB + (B + 3) ≤ mRest)
    (jU1 jVL : Fin mSubB) (hjNe : jU1 ≠ jVL) (iD3 : Fin mHold)
    (ctxB : TempCtx ((86 + mHold) + mSubB)) (v : Var)
    (rCore : QRegister posCoreWires n) (rOutTop : QRegister (B + 1) n) (rScr : QRegister mScr n)
    (hCOut : rCore.DisjointWires rOutTop) (hCS : rCore.DisjointWires rScr)
    (hOutS : rOutTop.DisjointWires rScr) :
    (mk34_dStageBGen B hB1 hB27 mHold mRest mSubB hmScr hsub jU1 jVL hjNe iD3 ctxB v
      rCore rOutTop rScr hCOut hCS hOutS).count PrimitiveGate.T =
      4 * ctxB.countTempAnd + (4 * B + 12) := by
  simp only [mk34_dStageBGen, mk34_ctxToDynNested_count_t, mk34_count_dMidKickBInPlace_t]
/-
## Section 5: `34`-Wire 3-Stage Mid-Kick Oracle (`dKickZeroSub34OptDyn`, `188 + 4 * B` `T`)
-/
/-  `2`-wire hold slice `rScr[0..2)` holding `(u3, d3)` across Stage B in `dKickZeroSub34OptDyn`. -/
/- `max 21 (B + 5)`-wire clean workspace slice `rScr[2..2+max 21 (B + 5))` shared across Stages A,
B, and C. -/
theorem mk34_realizesCleanUnitary_dStageBGen_rest
    {Var : Type} [Fintype Var] [DecidableEq Var] {n mScr : ℕ} [NeZero (2 ^ n)]
    (B : ℕ) (hB1 : 1 ≤ B) (hB27 : B ≤ 27) (mHold mRest mSubB : ℕ)
    (hmScr : mHold + mRest ≤ mScr) (hsub : mSubB + (B + 3) ≤ mRest)
    (jU1 jVL : Fin mSubB) (hjNe : jU1 ≠ jVL) (iD3 : Fin mHold)
    (ctxB : TempCtx ((86 + mHold) + mSubB)) (q0B : Wire ((86 + mHold) + mSubB))
    (hpvB : ValidCleanRem ((86 + mHold) + mSubB) mSubB (ctxB.plug (.z q0B))) (v : Var)
    (rCore : QRegister posCoreWires n) (rOutTop : QRegister (B + 1) n) (rScr : QRegister mScr n)
    (hCOut : rCore.DisjointWires rOutTop) (hCS : rCore.DisjointWires rScr)
    (hOutS : rOutTop.DisjointWires rScr) :
    RealizesCleanUnitary v (projZeroAll mRest (mk34_rRestGen mHold mRest hmScr rScr).wires)
      (mk34_dStageBGen B hB1 hB27 mHold mRest mSubB hmScr hsub jU1 jVL hjNe iD3 ctxB v
        rCore rOutTop rScr hCOut hCS hOutS)
      (mk34_cStageBGen B hB1 hB27 mHold mRest mSubB hmScr hsub jU1 jVL hjNe iD3 ctxB
        rCore rOutTop rScr hCOut hCS hOutS).eval := by
  let rCombOuter := mk34_rCombGen mHold mRest mSubB hmScr (by omega) rCore rScr hCS
  let rHold3 := mk34_rHold3Gen mHold mRest mSubB hmScr (by omega) jU1 jVL hjNe iD3 rScr
  let rSubB3 := mk34_rSubRestGen mHold mRest hmScr mSubB (B + 3) hsub rScr
  let hDisj := mk34_rCombGen_disjoint_subAfter mHold mRest mSubB (B + 3) hmScr (by omega) hsub rCore
    rScr hCS
  let fLeaf : BitAssignment ((86 + mHold) + mSubB) → BitAssignment n → ZMod 2 := fun γ β ↦
    mk34_fLeafMidB B ((mk34_ctxMidBInPlace B hB1 hB27).fwdBits
      (mk34_mapGenToMBInPlace B mHold mSubB jU1 jVL iD3 rCore rOutTop rSubB3 γ β))
  have hfLeaf : ∀ (γ γ' : BitAssignment ((86 + mHold) + mSubB)) (β : BitAssignment n),
      fLeaf γ (writeRegProg β rCombOuter γ') = fLeaf γ β := fun γ γ' β ↦ by
    dsimp only [fLeaf]
    rw [mk34_mapGenToMBInPlace_writeRegProg B mHold mRest mSubB hmScr hsub jU1 jVL iD3
          rCore rOutTop rScr hCOut hCS hOutS γ γ' β]
  have hLeafKet : ∀ β : BitAssignment n,
      (∀ j : Fin (B + 3), β (rSubB3 j) = 0) →
      (mk34_cMidKickBInPlace B hB1 hB27 rCore rHold3 rOutTop rSubB3
        (mk34_rCore_disjoint_rHold3Gen mHold mRest mSubB hmScr (by omega) jU1 jVL hjNe iD3 rCore
          rScr hCS)
        hCOut
        (mk34_rHold3Gen_disjoint_rOutTop mHold mRest mSubB (B + 1) hmScr (by omega) jU1 jVL hjNe iD3
          rOutTop rScr hOutS)
        ((hCS.compose_right _).compose_right _)
        (mk34_rHold3Gen_disjoint_subAfter mHold mRest mSubB (B + 3) hmScr (by omega) hsub jU1 jVL
          hjNe iD3 rScr)
        ((hOutS.compose_right _).compose_right _)).eval.1.mulVec
          (MeasureBranchHadamardSem.ket β) =
      ((-1 : ℂ) ^ (fLeaf (fun idx ↦ β (rCombOuter idx)) β).val) •
        MeasureBranchHadamardSem.ket β := fun β hSubB3 ↦ by
    rw [mbh_ket_eq_ket,
        mk34_cMidKickBInPlace_eval_ket_raw B hB1 hB27 rCore rHold3 rOutTop rSubB3 _ _ _ _ _ _ β
          hSubB3]
    dsimp only [fLeaf]
    rw [mk34_mapGenToMBInPlace_eq_rCombBInPlace B hB1 hB27 mHold mRest mSubB hmScr hsub
          jU1 jVL hjNe iD3 rCore rOutTop rScr hCOut hCS hOutS β]
  have hLeafReal := mk34_realizesCleanUnitary_dMidKickBInPlace B hB1 hB27 v rCore rHold3
    rOutTop rSubB3
    (mk34_rCore_disjoint_rHold3Gen mHold mRest mSubB hmScr (by omega) jU1 jVL hjNe iD3 rCore rScr
      hCS)
    hCOut
    (mk34_rHold3Gen_disjoint_rOutTop mHold mRest mSubB (B + 1) hmScr (by omega) jU1 jVL hjNe iD3
      rOutTop rScr hOutS)
    ((hCS.compose_right _).compose_right _)
    (mk34_rHold3Gen_disjoint_subAfter mHold mRest mSubB (B + 3) hmScr (by omega) hsub jU1 jVL hjNe
      iD3 rScr)
    ((hOutS.compose_right _).compose_right _)
  have hNested := mk34_realizesCleanUnitary_ctxToDynNested v rCombOuter rSubB3 hDisj
    _ _ fLeaf hfLeaf hLeafKet hLeafReal q0B ctxB mSubB (by omega) hpvB
  exact RealizesCleanUnitary.mono_proj (projZeroAll_conjTranspose (mSubB + (B + 3)) _)
    (projZeroAll_conjTranspose mRest _)
    (mk34_projZeroAll_tailScr_stageBGen B mHold mRest mSubB hmScr hsub rCore rScr hCS) hNested
/- `21`-wire clean prefix `rRest[0..21)` (`rScr[2..23)`) used by Stages A and C of
`dKickZeroSub34OptDyn`. -/
/- `2`-wire clean prefix `rRest[0..2)` (`rScr[2..4)`) used by outer Stage B of
`dKickZeroSub34OptDyn`. -/
/- `(B + 3)`-wire clean slice `rRest[2..B+5)` (`rScr[4..B+7)`) used by inner Stage B of
`dKickZeroSub34OptDyn`. -/
theorem mk34_cStageBGen_eval_ket_raw {n mScr : ℕ}
    (B : ℕ) (hB1 : 1 ≤ B) (hB27 : B ≤ 27) (mHold mRest mSubB : ℕ)
    (hmScr : mHold + mRest ≤ mScr) (hsub : mSubB + (B + 3) ≤ mRest)
    (jU1 jVL : Fin mSubB) (hjNe : jU1 ≠ jVL) (iD3 : Fin mHold)
    (ctxB : TempCtx ((86 + mHold) + mSubB)) (q0B : Wire ((86 + mHold) + mSubB))
    (hpBitsB : ∀ γ : BitAssignment ((86 + mHold) + mSubB),
      cleanRem ((86 + mHold) + mSubB) mSubB γ → (ctxB.plug (.z q0B)).evalBits γ = γ)
    (rCore : QRegister posCoreWires n) (rOutTop : QRegister (B + 1) n) (rScr : QRegister mScr n)
    (hCOut : rCore.DisjointWires rOutTop) (hCS : rCore.DisjointWires rScr)
    (hOutS : rOutTop.DisjointWires rScr) (δ : BitAssignment n)
    (hRest0 : ∀ s : Fin mRest, δ (mk34_rRestGen mHold mRest hmScr rScr s) = 0) :
    let rCombOuter := mk34_rCombGen mHold mRest mSubB hmScr (by omega) rCore rScr hCS
    let rSubB3 := mk34_rSubRestGen mHold mRest hmScr mSubB (B + 3) hsub rScr
    let γ : BitAssignment ((86 + mHold) + mSubB) := fun idx ↦ δ (rCombOuter idx)
    (mk34_cStageBGen B hB1 hB27 mHold mRest mSubB hmScr hsub jU1 jVL hjNe iD3 ctxB
      rCore rOutTop rScr hCOut hCS hOutS).eval.1.mulVec (ket δ) =
      ((-1 : ℂ) ^ (mk34_fLeafMidB B
        ((mk34_ctxMidBInPlace B hB1 hB27).fwdBits
          (mk34_mapGenToMBInPlace B mHold mSubB jU1 jVL iD3 rCore rOutTop rSubB3
            (ctxB.fwdBits γ) δ))).val) • ket δ := by
  intro rCombOuter rSubB3 γ
  let rHold3 := mk34_rHold3Gen mHold mRest mSubB hmScr (by omega) jU1 jVL hjNe iD3 rScr
  let hDisj := mk34_rCombGen_disjoint_subAfter mHold mRest mSubB (B + 3) hmScr (by omega) hsub rCore
    rScr hCS
  let fLeaf : BitAssignment ((86 + mHold) + mSubB) → BitAssignment n → ZMod 2 := fun γ' β ↦
    mk34_fLeafMidB B ((mk34_ctxMidBInPlace B hB1 hB27).fwdBits
      (mk34_mapGenToMBInPlace B mHold mSubB jU1 jVL iD3 rCore rOutTop rSubB3 γ' β))
  have hfLeaf : ∀ (γ₁ γ₂ : BitAssignment ((86 + mHold) + mSubB)) (β : BitAssignment n),
      fLeaf γ₁ (writeRegProg β rCombOuter γ₂) = fLeaf γ₁ β := fun γ₁ γ₂ β ↦ by
    dsimp only [fLeaf]
    rw [mk34_mapGenToMBInPlace_writeRegProg B mHold mRest mSubB hmScr hsub jU1 jVL iD3
          rCore rOutTop rScr hCOut hCS hOutS γ₁ γ₂ β]
  have hLeafKet : ∀ β : BitAssignment n,
      (∀ j : Fin (B + 3), β (rSubB3 j) = 0) →
      (mk34_cMidKickBInPlace B hB1 hB27 rCore rHold3 rOutTop rSubB3
        (mk34_rCore_disjoint_rHold3Gen mHold mRest mSubB hmScr (by omega) jU1 jVL hjNe iD3 rCore
          rScr hCS)
        hCOut
        (mk34_rHold3Gen_disjoint_rOutTop mHold mRest mSubB (B + 1) hmScr (by omega) jU1 jVL hjNe iD3
          rOutTop rScr hOutS)
        ((hCS.compose_right _).compose_right _)
        (mk34_rHold3Gen_disjoint_subAfter mHold mRest mSubB (B + 3) hmScr (by omega) hsub jU1 jVL
          hjNe iD3 rScr)
        ((hOutS.compose_right _).compose_right _)).eval.1.mulVec
          (MeasureBranchHadamardSem.ket β) =
      ((-1 : ℂ) ^ (fLeaf (fun idx ↦ β (rCombOuter idx)) β).val) •
        MeasureBranchHadamardSem.ket β := fun β hSubB3 ↦ by
    rw [mbh_ket_eq_ket,
        mk34_cMidKickBInPlace_eval_ket_raw B hB1 hB27 rCore rHold3 rOutTop rSubB3 _ _ _ _ _ _ β
          hSubB3]
    dsimp only [fLeaf]
    rw [mk34_mapGenToMBInPlace_eq_rCombBInPlace B hB1 hB27 mHold mRest mSubB hmScr hsub
          jU1 jVL hjNe iD3 rCore rOutTop rScr hCOut hCS hOutS β]
  have hSubB3 : ∀ j : Fin (B + 3), δ (rSubB3 j) = 0 := fun j ↦ by
    dsimp only [rSubB3, mk34_rSubRestGen]
    rw [QRegister.slice_apply]
    exact hRest0 ⟨mSubB + j.val, by omega⟩
  have hcr : cleanRem ((86 + mHold) + mSubB) mSubB γ := fun w hw ↦ by
    have hwEq := mk34_rCombGen_sub mHold mRest mSubB hmScr (by omega) rCore rScr hCS
      ⟨w.val - (86 + mHold), by omega⟩
    have hfin : (⟨(86 + mHold) + (w.val - (86 + mHold)), by omega⟩ :
        Wire ((86 + mHold) + mSubB)) = w := by
      apply Fin.ext
      dsimp
      omega
    rw [hfin] at hwEq
    change δ (rCombOuter w) = 0
    rw [hwEq]
    dsimp only [mk34_rSubRestGen]
    rw [QRegister.slice_apply]
    exact hRest0 ⟨0 + (w.val - (86 + mHold)), by omega⟩
  rw [mk34_cStageBGen, ← mbh_ket_eq_ket,
      mk34_ctxToToff_eval_ket_of_leafScr rCombOuter rSubB3 hDisj _ fLeaf hfLeaf hLeafKet
        q0B ctxB δ hSubB3,
      hpBitsB γ hcr, mk34_writeRegProg_self, mbh_ket_eq_ket]
theorem mk34_cStageBGen_preserves_rest {n mScr : ℕ}
    (B : ℕ) (hB1 : 1 ≤ B) (hB27 : B ≤ 27) (mHold mRest mSubB : ℕ)
    (hmScr : mHold + mRest ≤ mScr) (hsub : mSubB + (B + 3) ≤ mRest)
    (jU1 jVL : Fin mSubB) (hjNe : jU1 ≠ jVL) (iD3 : Fin mHold)
    (ctxB : TempCtx ((86 + mHold) + mSubB)) (q0B : Wire ((86 + mHold) + mSubB))
    (hpBitsB : ∀ γ : BitAssignment ((86 + mHold) + mSubB),
      cleanRem ((86 + mHold) + mSubB) mSubB γ → (ctxB.plug (.z q0B)).evalBits γ = γ)
    (rCore : QRegister posCoreWires n) (rOutTop : QRegister (B + 1) n) (rScr : QRegister mScr n)
    (hCOut : rCore.DisjointWires rOutTop) (hCS : rCore.DisjointWires rScr)
    (hOutS : rOutTop.DisjointWires rScr) :
    let P := projZeroAll mRest (mk34_rRestGen mHold mRest hmScr rScr).wires
    P * ((mk34_cStageBGen B hB1 hB27 mHold mRest mSubB hmScr hsub jU1 jVL hjNe iD3 ctxB
          rCore rOutTop rScr hCOut hCS hOutS).eval.1 * P) =
      (mk34_cStageBGen B hB1 hB27 mHold mRest mSubB hmScr hsub jU1 jVL hjNe iD3 ctxB
        rCore rOutTop rScr hCOut hCS hOutS).eval.1 * P := by
  intro P
  apply MeasureBranchHadamardSem.matrix_ext_ket
  intro β
  dsimp only [P]
  rw [mul_mulVec_prog, mul_mulVec_prog, ket_projZeroAll]
  by_cases hz : ∀ j : Fin mRest, β (mk34_rRestGen mHold mRest hmScr rScr j) = 0
  · have hk := mk34_cStageBGen_eval_ket_raw B hB1 hB27 mHold mRest mSubB hmScr hsub
      jU1 jVL hjNe iD3 ctxB q0B hpBitsB rCore rOutTop rScr hCOut hCS hOutS β hz
    dsimp only at hk
    rw [← mbh_ket_eq_ket] at hk
    rw [ite_eq_left hz, hk, Matrix.mulVec_smul, ket_projZeroAll, ite_eq_left hz]
  · rw [ite_eq_right hz, Matrix.mulVec_zero, Matrix.mulVec_zero]
/-  Active `88`-wire register `rCoreHi86 ++ rHold2` for `dKickZeroSub34OptDyn`. -/
theorem mk34_mapGenToMBInPlace_props {n mScr : ℕ}
    (B mHold mRest mSubB : ℕ) (hmScr : mHold + mRest ≤ mScr) (hsub : mSubB + (B + 3) ≤ mRest)
    (jU1 jVL : Fin mSubB) (iD3 : Fin mHold) (ctxB : TempCtx ((86 + mHold) + mSubB))
    (hBelow : ∀ (γ : BitAssignment ((86 + mHold) + mSubB)) (w : Wire ((86 + mHold) + mSubB)),
      w.val < 86 + mHold → ctxB.fwdBits γ w = γ w)
    (rCore : QRegister posCoreWires n) (rOutTop : QRegister (B + 1) n) (rScr : QRegister mScr n)
    (hCS : rCore.DisjointWires rScr) (δ : BitAssignment n)
    (hRest0 : ∀ s : Fin mRest, δ (mk34_rRestGen mHold mRest hmScr rScr s) = 0) :
    let rCombOuter := mk34_rCombGen mHold mRest mSubB hmScr (by omega) rCore rScr hCS
    let rSubB3 := mk34_rSubRestGen mHold mRest hmScr mSubB (B + 3) hsub rScr
    let γ : BitAssignment ((86 + mHold) + mSubB) := fun idx ↦ δ (rCombOuter idx)
    let γB := mk34_mapGenToMBInPlace B mHold mSubB jU1 jVL iD3 rCore rOutTop rSubB3
      (ctxB.fwdBits γ) δ
    cleanRem (mk34_mB B) (B + 3) γB ∧
    (∀ k : Fin 86, k.val ≠ 38 + (29 - B) →
      γB ⟨k.val, mk34_lt_mB (by omega)⟩ =
        δ (rCore ⟨3948 + k.val, mk34_lt_posCore (by omega)⟩)) ∧
    mk34_keepInPlaceVec B γB =
      (fun k : Fin 30 ↦ δ (rCore ⟨3986 + k.val, mk34_lt_posCore (by omega)⟩)) ∧
    (fun j : Fin B ↦ γB ⟨89 + j.val, mk34_lt_mB (by omega)⟩) =
      (fun j : Fin B ↦ δ (rOutTop ⟨j.val, by omega⟩)) ∧
    γB ⟨89 + B, mk34_lt_mB (by omega)⟩ = δ (rOutTop ⟨B, by omega⟩) := by
  intro rCombOuter rSubB3 γ γB
  have hc (k : Fin 86) : γ ⟨k.val, by omega⟩ =
      δ (rCore ⟨3948 + k.val, mk34_lt_posCore (by omega)⟩) :=
    congrArg δ (mk34_rCombGen_core mHold mRest mSubB hmScr (by omega) rCore rScr hCS k)
  have hcBNe (k : Fin 86) (hne : k.val ≠ 38 + (29 - B)) :
      γB ⟨k.val, mk34_lt_mB (by omega)⟩ =
        δ (rCore ⟨3948 + k.val, mk34_lt_posCore (by omega)⟩) := by
    dsimp only [γB, mk34_mapGenToMBInPlace]
    rw [dite_eq_left k.isLt, ite_eq_right hne, hBelow γ ⟨k.val, by omega⟩ (by
      dsimp
      omega)]
    exact hc k
  refine ⟨fun w hw ↦ ?_, hcBNe, ?_, ?_, ?_⟩
  · dsimp only [γB, mk34_mapGenToMBInPlace]
    have hlt : 90 + B + 1 ≤ w.val := by
      dsimp [mk34_mB] at hw
      omega
    simp only [show ¬ w.val < 86 by omega, show w.val ≠ 86 by omega, show w.val ≠ 87 by omega,
      show w.val ≠ 88 by omega, show ¬ w.val < 89 + (B + 1) by omega,
      show w.val ≠ 90 + B by omega, ↓reduceDIte, ↓reduceIte]
    dsimp only [rSubB3, mk34_rSubRestGen]
    rw [QRegister.slice_apply]
    exact hRest0 ⟨mSubB + _, by omega⟩
  · funext k
    dsimp only [mk34_keepInPlaceVec]
    by_cases hk : k.val = 29 - B
    · rw [ite_eq_left hk]
      dsimp only [γB, mk34_mapGenToMBInPlace]
      simp only [show ¬ 90 + B < 86 by omega, show 90 + B ≠ 86 by omega,
        show 90 + B ≠ 87 by omega, show 90 + B ≠ 88 by omega,
        show ¬ 90 + B < 89 + (B + 1) by omega, ↓reduceDIte, ↓reduceIte]
      rw [hBelow γ ⟨38 + (29 - B), by omega⟩ (by
        dsimp
        omega)]
      exact (hc ⟨38 + (29 - B), by omega⟩).trans (congrArg (fun idx ↦ δ (rCore idx)) (Fin.ext (by
        dsimp
        omega)))
    · rw [ite_eq_right hk, hcBNe ⟨38 + k.val, by omega⟩ (by
        dsimp
        omega)]
      exact congrArg (fun idx ↦ δ (rCore idx)) (Fin.ext (by
        dsimp
        omega))
  · funext j
    dsimp only [γB, mk34_mapGenToMBInPlace]
    simp only [show ¬ 89 + j.val < 86 by omega, show 89 + j.val ≠ 86 by omega,
      show 89 + j.val ≠ 87 by omega, show 89 + j.val ≠ 88 by omega,
      show 89 + j.val < 89 + (B + 1) by omega, ↓reduceDIte, ↓reduceIte]
    exact congrArg (fun idx ↦ δ (rOutTop idx)) (Fin.ext (by
      dsimp
      omega))
  · dsimp only [γB, mk34_mapGenToMBInPlace]
    simp only [show ¬ 89 + B < 86 by omega, show 89 + B ≠ 86 by omega,
      show 89 + B ≠ 87 by omega, show 89 + B ≠ 88 by omega,
      show 89 + B < 89 + (B + 1) by omega, ↓reduceDIte, ↓reduceIte]
    exact congrArg (fun idx ↦ δ (rOutTop idx)) (Fin.ext (by
      dsimp
      omega))
theorem mk34_cStageBGen_eval_ket {n mScr : ℕ}
    (B : ℕ) (hB1 : 1 ≤ B) (hB27 : B ≤ 27) (mHold mRest mSubB : ℕ)
    (hmScr : mHold + mRest ≤ mScr) (hsub : mSubB + (B + 3) ≤ mRest)
    (jU1 jVL : Fin mSubB) (hjNe : jU1 ≠ jVL) (iD3 : Fin mHold)
    (ctxB : TempCtx ((86 + mHold) + mSubB)) (q0B : Wire ((86 + mHold) + mSubB))
    (hpBitsB : ∀ γ : BitAssignment ((86 + mHold) + mSubB),
      cleanRem ((86 + mHold) + mSubB) mSubB γ → (ctxB.plug (.z q0B)).evalBits γ = γ)
    (hBelow : ∀ (γ : BitAssignment ((86 + mHold) + mSubB)) (w : Wire ((86 + mHold) + mSubB)),
      w.val < 86 + mHold → ctxB.fwdBits γ w = γ w)
    (holdVec : QRegister posCoreWires n → BitAssignment n → BitAssignment mHold)
    (rCore : QRegister posCoreWires n) (rOutTop : QRegister (B + 1) n) (rScr : QRegister mScr n)
    (hCOut : rCore.DisjointWires rOutTop) (hCS : rCore.DisjointWires rScr)
    (hOutS : rOutTop.DisjointWires rScr) (δ : BitAssignment n)
    (hHold : ∀ i : Fin mHold, δ (mk34_rHoldGen mHold mRest hmScr rScr i) = holdVec rCore δ i)
    (hRest0 : ∀ s : Fin mRest, δ (mk34_rRestGen mHold mRest hmScr rScr s) = 0)
    (hHoldD3 : holdVec rCore δ iD3 =
      δ (rCore ⟨3948, by decide⟩) *
        ge217Bit (δ (rCore ⟨3976, by decide⟩)) (δ (rCore ⟨3977, by decide⟩))
          (δ (rCore ⟨3978, by decide⟩)) (δ (rCore ⟨3979, by decide⟩))
          (δ (rCore ⟨3980, by decide⟩)) (δ (rCore ⟨3981, by decide⟩))
          (δ (rCore ⟨3982, by decide⟩)) (δ (rCore ⟨3983, by decide⟩)))
    (hWires : ∀ γ : BitAssignment ((86 + mHold) + mSubB),
      cleanRem ((86 + mHold) + mSubB) mSubB γ →
      (∀ k : Fin 86, γ ⟨k.val, by omega⟩ =
        δ (rCore ⟨3948 + k.val, mk34_lt_posCore (by omega)⟩)) →
      (∀ i : Fin mHold, γ ⟨86 + i.val, by omega⟩ = holdVec rCore δ i) →
      ctxB.fwdBits γ ⟨(86 + mHold) + jU1.val, by omega⟩ =
        (1 + δ (rCore ⟨3950, by decide⟩)) * (1 + δ (rCore ⟨3949, by decide⟩)) ∧
      ctxB.fwdBits γ ⟨(86 + mHold) + jVL.val, by omega⟩ =
        ((1 + δ (rCore ⟨3950, by decide⟩)) * (1 + δ (rCore ⟨3949, by decide⟩))) *
          (((1 + δ (rCore ⟨4016, by decide⟩)) *
            (1 + ge218Bit (δ (rCore ⟨3969, by decide⟩)) (δ (rCore ⟨3970, by decide⟩))
              (δ (rCore ⟨3971, by decide⟩)) (δ (rCore ⟨3972, by decide⟩))
              (δ (rCore ⟨3973, by decide⟩)) (δ (rCore ⟨3974, by decide⟩))
              (δ (rCore ⟨3975, by decide⟩)))) *
            (1 + (1 + δ (rCore ⟨3948, by decide⟩)) *
              ge216Bit (δ (rCore ⟨3963, by decide⟩)) (δ (rCore ⟨3964, by decide⟩))
                (δ (rCore ⟨3965, by decide⟩)) (δ (rCore ⟨3966, by decide⟩))
                (δ (rCore ⟨3967, by decide⟩))))) :
    (mk34_cStageBGen B hB1 hB27 mHold mRest mSubB hmScr hsub jU1 jVL hjNe iD3 ctxB
      rCore rOutTop rScr hCOut hCS hOutS).eval.1.mulVec (ket δ) =
      ((-1 : ℂ) ^ (midKickPhaseBitB B rCore rOutTop δ).val) • ket δ := by
  rw [mk34_cStageBGen_eval_ket_raw B hB1 hB27 mHold mRest mSubB hmScr hsub jU1 jVL hjNe iD3
        ctxB q0B hpBitsB rCore rOutTop rScr hCOut hCS hOutS δ hRest0]
  congr 3
  let rCombOuter := mk34_rCombGen mHold mRest mSubB hmScr (by omega) rCore rScr hCS
  let rSubB3 := mk34_rSubRestGen mHold mRest hmScr mSubB (B + 3) hsub rScr
  let γ : BitAssignment ((86 + mHold) + mSubB) := fun idx ↦ δ (rCombOuter idx)
  let γB := mk34_mapGenToMBInPlace B mHold mSubB jU1 jVL iD3 rCore rOutTop rSubB3
    (ctxB.fwdBits γ) δ
  obtain ⟨hcrB, hcBNe, hKeep, hOut, hSign⟩ := mk34_mapGenToMBInPlace_props B mHold mRest mSubB
    hmScr hsub jU1 jVL iD3 ctxB hBelow rCore rOutTop rScr hCS δ hRest0
  have hcr : cleanRem ((86 + mHold) + mSubB) mSubB γ := fun w hw ↦ by
    have hwEq := mk34_rCombGen_sub mHold mRest mSubB hmScr (by omega) rCore rScr hCS
      ⟨w.val - (86 + mHold), by omega⟩
    have hfin : (⟨(86 + mHold) + (w.val - (86 + mHold)), by omega⟩ :
        Wire ((86 + mHold) + mSubB)) = w := Fin.ext (by
      dsimp
      omega)
    rw [hfin] at hwEq
    change δ (rCombOuter w) = 0
    rw [hwEq]
    dsimp only [mk34_rSubRestGen]
    rw [QRegister.slice_apply]
    exact hRest0 ⟨0 + (w.val - (86 + mHold)), by omega⟩
  have hc (k : Fin 86) : γ ⟨k.val, by omega⟩ =
      δ (rCore ⟨3948 + k.val, mk34_lt_posCore (by omega)⟩) :=
    congrArg δ (mk34_rCombGen_core mHold mRest mSubB hmScr (by omega) rCore rScr hCS k)
  have hh (i : Fin mHold) : γ ⟨86 + i.val, by omega⟩ = holdVec rCore δ i :=
    (congrArg δ (mk34_rCombGen_hold mHold mRest mSubB hmScr (by omega) rCore rScr hCS i)).trans
      (hHold i)
  obtain ⟨hU1W, hVLW⟩ := hWires γ hcr hc hh
  have hcB0 : γB ⟨0, mk34_lt_mB (by omega)⟩ = δ (rCore ⟨3948, by decide⟩) :=
    hcBNe ⟨0, by decide⟩ (by
      dsimp
      omega)
  have hcB2 : γB ⟨2, mk34_lt_mB (by omega)⟩ = δ (rCore ⟨3950, by decide⟩) :=
    hcBNe ⟨2, by decide⟩ (by
      dsimp
      omega)
  have hcB36 : γB ⟨36, mk34_lt_mB (by omega)⟩ = δ (rCore ⟨3984, by decide⟩) :=
    hcBNe ⟨36, by decide⟩ (by
      dsimp
      omega)
  have hcB85 : γB ⟨85, mk34_lt_mB (by omega)⟩ = δ (rCore ⟨4033, by decide⟩) :=
    hcBNe ⟨85, by decide⟩ (by
      dsimp
      omega)
  have hu1 : γB ⟨86, mk34_lt_mB (by omega)⟩ =
      (1 + γB ⟨2, mk34_lt_mB (by omega)⟩) * (1 + δ (rCore ⟨3949, by decide⟩)) := by
    have h86 : γB ⟨86, mk34_lt_mB (by omega)⟩ =
        ctxB.fwdBits γ ⟨(86 + mHold) + jU1.val, by omega⟩ := by
      dsimp only [γB, mk34_mapGenToMBInPlace]
      simp
    rw [h86, hU1W, ← hcB2]
  have hvL : γB ⟨87, mk34_lt_mB (by omega)⟩ =
      ((1 + γB ⟨2, mk34_lt_mB (by omega)⟩) * (1 + δ (rCore ⟨3949, by decide⟩))) *
        (((1 + δ (rCore ⟨4016, by decide⟩)) *
          (1 + ge218Bit (δ (rCore ⟨3969, by decide⟩)) (δ (rCore ⟨3970, by decide⟩))
            (δ (rCore ⟨3971, by decide⟩)) (δ (rCore ⟨3972, by decide⟩))
            (δ (rCore ⟨3973, by decide⟩)) (δ (rCore ⟨3974, by decide⟩))
            (δ (rCore ⟨3975, by decide⟩)))) *
          (1 + (1 + γB ⟨0, mk34_lt_mB (by omega)⟩) *
            ge216Bit (δ (rCore ⟨3963, by decide⟩)) (δ (rCore ⟨3964, by decide⟩))
              (δ (rCore ⟨3965, by decide⟩)) (δ (rCore ⟨3966, by decide⟩))
              (δ (rCore ⟨3967, by decide⟩)))) := by
    have h87 : γB ⟨87, mk34_lt_mB (by omega)⟩ =
        ctxB.fwdBits γ ⟨(86 + mHold) + jVL.val, by omega⟩ := by
      dsimp only [γB, mk34_mapGenToMBInPlace]
      simp
    rw [h87, hVLW, ← hcB2, ← hcB0]
  have hd3 : γB ⟨88, mk34_lt_mB (by omega)⟩ =
      γB ⟨0, mk34_lt_mB (by omega)⟩ *
        ge217Bit (δ (rCore ⟨3976, by decide⟩)) (δ (rCore ⟨3977, by decide⟩))
          (δ (rCore ⟨3978, by decide⟩)) (δ (rCore ⟨3979, by decide⟩))
          (δ (rCore ⟨3980, by decide⟩)) (δ (rCore ⟨3981, by decide⟩))
          (δ (rCore ⟨3982, by decide⟩)) (δ (rCore ⟨3983, by decide⟩)) := by
    have h88 : γB ⟨88, mk34_lt_mB (by omega)⟩ = ctxB.fwdBits γ ⟨86 + iD3.val, by omega⟩ := by
      dsimp only [γB, mk34_mapGenToMBInPlace]
      simp
    rw [h88, hBelow γ ⟨86 + iD3.val, by omega⟩ (by
      dsimp
      omega), hh iD3, hHoldD3, ← hcB0]
  have hSign' : γB ⟨89 + B, mk34_lt_mB (by omega)⟩ = δ (rOutTop ⟨B, by omega⟩) := hSign
  change mk34_fLeafMidB B ((mk34_ctxMidBInPlace B hB1 hB27).fwdBits γB) = _
  rw [mk34_ctxMidBInPlace_fwdBits_fLeaf B hB1 hB27 γB hcrB
        (δ (rCore ⟨3949, by decide⟩)) (δ (rCore ⟨4016, by decide⟩)) _ _ _ hu1 hvL hd3,
      hcB2, hcB0, hcB36, hcB85, hKeep, hOut, hSign']
  rfl
/-  Combined `109`-wire register `rAct88 ++ rSub21` for Stages A and C of `dKickZeroSub34OptDyn`. -/
theorem mk34_realizesCleanUnitary_kick3StageGen
    {Var : Type} [Fintype Var] [DecidableEq Var] {n mScr : ℕ} [NeZero (2 ^ n)]
    (mHold mRest : ℕ) (hmScr : mHold + mRest ≤ mScr) (v : Var) (rScr : QRegister mScr n)
    (cA cB : Circuit n) (dA dB : DynamicCircuit Var n)
    (hRealAC : RealizesCleanUnitary v (projZeroAll mRest (mk34_rRestGen mHold mRest hmScr
      rScr).wires)
      dA cA.eval)
    (hRealB : RealizesCleanUnitary v (projZeroAll mRest (mk34_rRestGen mHold mRest hmScr
      rScr).wires)
      dB cB.eval)
    (hPresA : let P := projZeroAll mRest (mk34_rRestGen mHold mRest hmScr rScr).wires
      P * (cA.eval.1 * P) = cA.eval.1 * P)
    (hPresB : let P := projZeroAll mRest (mk34_rRestGen mHold mRest hmScr rScr).wires
      P * (cB.eval.1 * P) = cB.eval.1 * P) :
    RealizesCleanUnitary v (projZeroAll mScr rScr.wires)
      (.seq dA (.seq dB dA)) (cA ;;ᶜ cB ;;ᶜ cA).eval := by
  let PRest := projZeroAll mRest (mk34_rRestGen mHold mRest hmScr rScr).wires
  have hPRest : PRestᴴ = PRest := projZeroAll_conjTranspose mRest _
  have hBC := RealizesCleanUnitary.seq hPRest hRealB hRealAC hPresB
  have hABC := RealizesCleanUnitary.seq hPRest hRealAC hBC hPresA
  have hU_eq : (cA.eval * cB.eval) * cA.eval = (cA ;;ᶜ cB ;;ᶜ cA).eval := by
    simp [Circuit.eval_seq, mul_assoc]
  rw [hU_eq] at hABC
  exact RealizesCleanUnitary.mono_proj hPRest (projZeroAll_conjTranspose mScr _)
    (mk34_projZeroAll_restGen_scr mHold mRest hmScr rScr) hABC
theorem mk34_kick3StageGen_eval_mulVec_ket {n mScr : ℕ}
    (B mHold mRest mSubA : ℕ) (hmScr : mHold + mRest ≤ mScr) (hmSubA : mSubA ≤ mRest)
    (cA cB : Circuit n)
    (holdVec : QRegister posCoreWires n → BitAssignment n → BitAssignment mHold)
    (hHoldCongr : ∀ (rCore : QRegister posCoreWires n) (β₁ β₂ : BitAssignment n),
      (∀ idx, β₁ (rCore idx) = β₂ (rCore idx)) → holdVec rCore β₁ = holdVec rCore β₂)
    (rCore : QRegister posCoreWires n) (rOutTop : QRegister (B + 1) n) (rScr : QRegister mScr n)
    (hCS : rCore.DisjointWires rScr) (hOutS : rOutTop.DisjointWires rScr)
    (hEvalA : ∀ β : BitAssignment n,
      (∀ j : Fin mSubA, β (mk34_rSubRestGen mHold mRest hmScr 0 mSubA (by omega) rScr j) = 0) →
      cA.eval.1.mulVec (ket β) = ket (writeReg β (mk34_rHoldGen mHold mRest hmScr rScr)
        (fun i ↦ β (mk34_rHoldGen mHold mRest hmScr rScr i) + holdVec rCore β i)))
    (hEvalB : ∀ β : BitAssignment n,
      (∀ i : Fin mHold, β (mk34_rHoldGen mHold mRest hmScr rScr i) = holdVec rCore β i) →
      (∀ s : Fin mRest, β (mk34_rRestGen mHold mRest hmScr rScr s) = 0) →
      cB.eval.1.mulVec (ket β) = ((-1 : ℂ) ^ (midKickPhaseBitB B rCore rOutTop β).val) • ket β)
    (δ : BitAssignment n) (hScr0 : ∀ s : Fin mScr, δ (rScr s) = 0) :
    (cA ;;ᶜ cB ;;ᶜ cA).eval.1.mulVec (ket δ) =
      ((-1 : ℂ) ^ (midKickPhaseBitB B rCore rOutTop δ).val) • ket δ := by
  let rHold := mk34_rHoldGen mHold mRest hmScr rScr
  let rRest := mk34_rRestGen mHold mRest hmScr rScr
  let δ₁ := writeReg δ rHold (holdVec rCore δ)
  have hHold0 : ∀ i : Fin mHold, δ (rHold i) = 0 := fun i ↦ by
    dsimp only [rHold, mk34_rHoldGen]
    rw [QRegister.slice_apply]
    exact hScr0 ⟨0 + i.val, by omega⟩
  have hRest0 : ∀ j : Fin mRest, δ (rRest j) = 0 := fun j ↦ by
    dsimp only [rRest, mk34_rRestGen]
    rw [QRegister.slice_apply]
    exact hScr0 ⟨mHold + j.val, by omega⟩
  have hSubA_δ : ∀ j : Fin mSubA,
      δ (mk34_rSubRestGen mHold mRest hmScr 0 mSubA (by omega) rScr j) = 0 := fun j ↦ by
    dsimp only [mk34_rSubRestGen]
    rw [QRegister.slice_apply]
    exact hRest0 ⟨0 + j.val, by omega⟩
  have hStageA : cA.eval.1.mulVec (ket δ) = ket δ₁ := by
    rw [hEvalA δ hSubA_δ]
    congr 1
    have hfun : (fun i ↦ δ (rHold i) + holdVec rCore δ i) = holdVec rCore δ :=
      funext fun i ↦ by rw [hHold0 i, zero_add]
    rw [hfun]
  have hCore_δ₁ : ∀ idx : Fin posCoreWires, δ₁ (rCore idx) = δ (rCore idx) := fun idx ↦
    writeReg_apply_of_not_mem δ rHold _ (rCore idx)
      (fun ⟨i, hi⟩ ↦ (hCS.compose_right _).ne idx i hi.symm)
  have hOut_δ₁ : ∀ idx : Fin (B + 1), δ₁ (rOutTop idx) = δ (rOutTop idx) := fun idx ↦
    writeReg_apply_of_not_mem δ rHold _ (rOutTop idx)
      (fun ⟨i, hi⟩ ↦ (hOutS.compose_right _).ne idx i hi.symm)
  have hRest_δ₁ : ∀ j : Fin mRest, δ₁ (rRest j) = 0 := fun j ↦
    (writeReg_apply_of_not_mem δ rHold _ (rRest j)
      (fun ⟨i, hi⟩ ↦ (mk34_rHoldGen_disjoint_rRestGen mHold mRest hmScr rScr).ne i j hi)).trans
      (hRest0 j)
  have hHoldVec_δ₁ : holdVec rCore δ₁ = holdVec rCore δ := hHoldCongr rCore δ₁ δ hCore_δ₁
  have hHold_δ₁ : ∀ i : Fin mHold, δ₁ (rHold i) = holdVec rCore δ₁ i := fun i ↦ by
    rw [hHoldVec_δ₁]
    exact writeReg_apply_reg δ rHold _ i
  have hMidBit_δ₁ : midKickPhaseBitB B rCore rOutTop δ₁ = midKickPhaseBitB B rCore rOutTop δ := by
    simp only [midKickPhaseBitB, hCore_δ₁, hOut_δ₁]
  have hStageB : cB.eval.1.mulVec (ket δ₁) =
      ((-1 : ℂ) ^ (midKickPhaseBitB B rCore rOutTop δ).val) • ket δ₁ := by
    rw [hEvalB δ₁ hHold_δ₁ hRest_δ₁, hMidBit_δ₁]
  have hSubA_δ₁ : ∀ j : Fin mSubA,
      δ₁ (mk34_rSubRestGen mHold mRest hmScr 0 mSubA (by omega) rScr j) = 0 := fun j ↦ by
    dsimp only [mk34_rSubRestGen]
    rw [QRegister.slice_apply]
    exact hRest_δ₁ ⟨0 + j.val, by omega⟩
  have hStageC : cA.eval.1.mulVec (ket δ₁) = ket δ := by
    rw [hEvalA δ₁ hSubA_δ₁]
    congr 1
    funext q
    by_cases hq : q ∈ Set.range rHold.wires
    · obtain ⟨i, rfl⟩ := hq
      rw [writeReg_apply_reg, hHold_δ₁ i, CharTwo.add_self_eq_zero, hHold0 i]
    · exact (writeReg_apply_of_not_mem δ₁ rHold _ q hq).trans
        (writeReg_apply_of_not_mem δ rHold _ q hq)
  simp only [Circuit.eval_seq, Submonoid.coe_mul, ← Matrix.mulVec_mulVec]
  rw [hStageA, hStageB, Matrix.mulVec_smul, hStageC]
theorem mk34_fLeafComp1_spec {n mScr : ℕ} (B : ℕ) (hmScr : 1 + (B + 18) ≤ mScr)
    (rCore : QRegister posCoreWires n) (rScr : QRegister mScr n) (hCS : rCore.DisjointWires rScr)
    (δ : BitAssignment n)
    (hcr : cleanRem 95 8
      (fun idx ↦ δ (mk34_rCombGen 1 (B + 18) 8 hmScr (by omega) rCore rScr hCS idx))) :
    mk34_fLeafComp1 (mk34_ctxCompD3_8.fwdBits (fun idx ↦
      δ (mk34_rCombGen 1 (B + 18) 8 hmScr (by omega) rCore rScr hCS idx))) =
      ∑ i : Fin 1, δ (mk34_rHoldGen 1 (B + 18) hmScr rScr i) * mk34_hold1Vec rCore δ i := by
  rw [Fin.sum_univ_one]
  let γ : BitAssignment 95 := fun idx ↦
    δ (mk34_rCombGen 1 (B + 18) 8 hmScr (by omega) rCore rScr hCS idx)
  obtain ⟨_, he86, hw86⟩ := mk34_ctxCompD3_8_fwdBits_wire ⟨86, by decide⟩ γ hcr
  obtain ⟨_, he94, hw94⟩ := mk34_ctxCompD3_8_fwdBits_wire ⟨94, by decide⟩ γ hcr
  have hc (k : Fin 86) : γ ⟨k.val, by omega⟩ =
      δ (rCore ⟨3948 + k.val, mk34_lt_posCore (by omega)⟩) :=
    congrArg δ (mk34_rCombGen_core 1 (B + 18) 8 hmScr (by omega) rCore rScr hCS k)
  have hh0 : γ ⟨86, by decide⟩ = δ (mk34_rHoldGen 1 (B + 18) hmScr rScr 0) :=
    congrArg δ (mk34_rCombGen_hold 1 (B + 18) 8 hmScr (by omega) rCore rScr hCS 0)
  dsimp only [mk34_fLeafComp1, mk34_hold1Vec, mk34_holdVec]
  rw [he86.trans hw86.1, he94.trans hw94.2, hh0,
      hc ⟨0, by decide⟩,
      hc ⟨28, by decide⟩, hc ⟨29, by decide⟩, hc ⟨30, by decide⟩, hc ⟨31, by decide⟩,
      hc ⟨32, by decide⟩, hc ⟨33, by decide⟩, hc ⟨34, by decide⟩, hc ⟨35, by decide⟩]
  rfl
/-- Top-level `(B + 19)`-clean-wire (`≤ 46` for `B ≤ 27`) reversible `Circuit n` for the 3-stage
mid-phase kickback. -/
def cKickZeroSub46Opt {n mScr : ℕ} (B : ℕ) (hB1 : 1 ≤ B) (hB27 : B ≤ 27)
    (hmScr : B + 19 ≤ mScr) (rCore : QRegister posCoreWires n) (rOutTop : QRegister (B + 1) n)
    (rScr : QRegister mScr n) (hCOut : rCore.DisjointWires rOutTop)
    (hCS : rCore.DisjointWires rScr) (hOutS : rOutTop.DisjointWires rScr) : Circuit n :=
  let cA := mk34_cCompGen 1 (B + 18) 8 (by omega) (by omega) mk34_cLeafComp1On
    mk34_ctxCompD3_8 rCore rScr hCS
  let cB := mk34_cStageBGen B hB1 hB27 1 (B + 18) 15 (by omega) (by omega)
    ⟨10, by decide⟩ ⟨14, by decide⟩ (by decide) 0 mk34_ctxStageB15
    rCore rOutTop rScr hCOut hCS hOutS
  cA ;;ᶜ cB ;;ᶜ cA
/-- Top-level `(B + 19)`-clean-wire (`≤ 46` for `B ≤ 27`) `0`-`.TOFF` `DynamicCircuit Var n`
(`136 + 4 * B` `T`). -/
def dKickZeroSub46OptDyn {Var : Type} {n mScr : ℕ} (B : ℕ) (hB1 : 1 ≤ B) (hB27 : B ≤ 27)
    (hmScr : B + 19 ≤ mScr) (v : Var) (rCore : QRegister posCoreWires n)
    (rOutTop : QRegister (B + 1) n) (rScr : QRegister mScr n)
    (hCOut : rCore.DisjointWires rOutTop) (hCS : rCore.DisjointWires rScr)
    (hOutS : rOutTop.DisjointWires rScr) : DynamicCircuit Var n :=
  let dA := mk34_dCompGen 1 (B + 18) 8 (by omega) (by omega) v mk34_cLeafComp1On
    mk34_ctxCompD3_8 rCore rScr hCS
  let dB := mk34_dStageBGen B hB1 hB27 1 (B + 18) 15 (by omega) (by omega)
    ⟨10, by decide⟩ ⟨14, by decide⟩ (by decide) 0 mk34_ctxStageB15 v
    rCore rOutTop rScr hCOut hCS hOutS
  .seq dA (.seq dB dA)
@[scoped simp] theorem count_dKickZeroSub46OptDyn_toff {Var : Type} {n mScr : ℕ}
    (B : ℕ) (hB1 : 1 ≤ B) (hB27 : B ≤ 27) (hmScr : B + 19 ≤ mScr) (v : Var)
    (rCore : QRegister posCoreWires n) (rOutTop : QRegister (B + 1) n) (rScr : QRegister mScr n)
    (hCOut : rCore.DisjointWires rOutTop) (hCS : rCore.DisjointWires rScr)
    (hOutS : rOutTop.DisjointWires rScr) :
    (dKickZeroSub46OptDyn B hB1 hB27 hmScr v rCore rOutTop rScr hCOut hCS hOutS).count
      PrimitiveGate.TOFF = 0 := by
  simp [dKickZeroSub46OptDyn, mk34_count_dCompGen_toff, mk34_cLeafComp1On_count_toff,
    mk34_count_dStageBGen_toff]
@[scoped simp] theorem count_dKickZeroSub46OptDyn_t {Var : Type} {n mScr : ℕ}
    (B : ℕ) (hB1 : 1 ≤ B) (hB27 : B ≤ 27) (hmScr : B + 19 ≤ mScr) (v : Var)
    (rCore : QRegister posCoreWires n) (rOutTop : QRegister (B + 1) n) (rScr : QRegister mScr n)
    (hCOut : rCore.DisjointWires rOutTop) (hCS : rCore.DisjointWires rScr)
    (hOutS : rOutTop.DisjointWires rScr) :
    (dKickZeroSub46OptDyn B hB1 hB27 hmScr v rCore rOutTop rScr hCOut hCS hOutS).count
      PrimitiveGate.T = 136 + 4 * B := by
  simp only [dKickZeroSub46OptDyn, DynamicCircuit.count,
    mk34_count_dCompGen_t 1 (B + 18) 8 (by omega) (by omega) v mk34_cLeafComp1On mk34_ctxCompD3_8
      rCore rScr hCS mk34_cLeafComp1On_count_t,
    mk34_count_dStageBGen_t, mk34_ctxCompD3_8_countTempAnd, mk34_ctxStageB15_countTempAnd]
  ring
theorem dKickZeroSub46OptDyn_preservesStoreConst {Var : Type} [Fintype Var] [DecidableEq Var]
    {n mScr : ℕ} (B : ℕ) (hB1 : 1 ≤ B) (hB27 : B ≤ 27) (hmScr : B + 19 ≤ mScr) (v : Var)
    (rCore : QRegister posCoreWires n) (rOutTop : QRegister (B + 1) n)
    (rScr : QRegister mScr n) (hCOut : rCore.DisjointWires rOutTop)
    (hCS : rCore.DisjointWires rScr) (hOutS : rOutTop.DisjointWires rScr) :
    PreservesStoreConst
      (dKickZeroSub46OptDyn B hB1 hB27 hmScr v rCore rOutTop rScr hCOut hCS hOutS) :=
  PreservesStoreConst.seq (mk34_dCompGen_preservesStoreConst _ _ _ _ _ _ _ _ _ _ _)
    (PreservesStoreConst.seq (mk34_dStageBGen_preservesStoreConst _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      _ _ _)
      (mk34_dCompGen_preservesStoreConst _ _ _ _ _ _ _ _ _ _ _))
theorem realizesCleanUnitary_dKickZeroSub46OptDyn_scr
    {Var : Type} [Fintype Var] [DecidableEq Var] {n mScr : ℕ} [NeZero (2 ^ n)]
    (B : ℕ) (hB1 : 1 ≤ B) (hB27 : B ≤ 27) (hmScr : B + 19 ≤ mScr) (v : Var)
    (rCore : QRegister posCoreWires n) (rOutTop : QRegister (B + 1) n) (rScr : QRegister mScr n)
    (hCOut : rCore.DisjointWires rOutTop) (hCS : rCore.DisjointWires rScr)
    (hOutS : rOutTop.DisjointWires rScr) :
    RealizesCleanUnitary v (projZeroAll mScr rScr.wires)
      (dKickZeroSub46OptDyn B hB1 hB27 hmScr v rCore rOutTop rScr hCOut hCS hOutS)
      (cKickZeroSub46Opt B hB1 hB27 hmScr rCore rOutTop rScr hCOut hCS hOutS).eval := by
  have hpvA : ValidCleanRem 95 8 (mk34_ctxCompD3_8.plug (.z ⟨0, by decide⟩)) := by
    rw [mk34_pCompD3_8_eq]
    exact mk34_pCompD3_8_valid_and_bits.1
  have hpBitsA : ∀ γ : BitAssignment 95, cleanRem 95 8 γ →
      (mk34_ctxCompD3_8.plug (.z ⟨0, by decide⟩)).evalBits γ = γ := by
    rw [mk34_pCompD3_8_eq]
    exact mk34_pCompD3_8_valid_and_bits.2
  have hpvB : ValidCleanRem 102 15 (mk34_ctxStageB15.plug (.z ⟨0, by decide⟩)) := by
    rw [mk34_pStageB15_eq]
    exact mk34_pStageB15_valid_and_bits.1
  have hpBitsB : ∀ γ : BitAssignment 102, cleanRem 102 15 γ →
      (mk34_ctxStageB15.plug (.z ⟨0, by decide⟩)).evalBits γ = γ := by
    rw [mk34_pStageB15_eq]
    exact mk34_pStageB15_valid_and_bits.2
  have hCongr1 : ∀ (rC : QRegister posCoreWires n) (β₁ β₂ : BitAssignment n),
      (∀ idx, β₁ (rC idx) = β₂ (rC idx)) → mk34_hold1Vec rC β₁ = mk34_hold1Vec rC β₂ :=
    fun rC β₁ β₂ hEq ↦ by
      funext i
      simp only [mk34_hold1Vec, mk34_holdVec, hEq]
  exact mk34_realizesCleanUnitary_kick3StageGen 1 (B + 18) (by omega) v rScr _ _ _ _
    (mk34_realizesCleanUnitary_dCompGen_rest 1 (B + 18) 8 (by omega) (by omega) v
      mk34_cLeafComp1On mk34_fLeafComp1 mk34_ctxCompD3_8 ⟨0, by decide⟩ mk34_hold1Vec
      rCore rScr hCS (mk34_cLeafComp1On_eval_mbh_ket _) hpvA hpBitsA
      (mk34_fLeafComp1_spec B (by omega) rCore rScr hCS))
    (mk34_realizesCleanUnitary_dStageBGen_rest B hB1 hB27 1 (B + 18) 15 (by omega) (by omega)
      ⟨10, by decide⟩ ⟨14, by decide⟩ (by decide) 0 mk34_ctxStageB15 ⟨0, by decide⟩ hpvB v
      rCore rOutTop rScr hCOut hCS hOutS)
    (mk34_cCompGen_preserves_rest 1 (B + 18) 8 (by omega) (by omega) mk34_cLeafComp1On
      mk34_ctxCompD3_8 mk34_hold1Vec rCore rScr hCS
      (mk34_cCompGen_eval_ket 1 (B + 18) 8 (by omega) (by omega) mk34_cLeafComp1On
        mk34_fLeafComp1 mk34_ctxCompD3_8 ⟨0, by decide⟩ mk34_hold1Vec hCongr1 rCore rScr hCS
        (mk34_cLeafComp1On_eval_mbh_ket _) hpBitsA
        (mk34_fLeafComp1_spec B (by omega) rCore rScr hCS)))
    (mk34_cStageBGen_preserves_rest B hB1 hB27 1 (B + 18) 15 (by omega) (by omega)
      ⟨10, by decide⟩ ⟨14, by decide⟩ (by decide) 0 mk34_ctxStageB15 ⟨0, by decide⟩ hpBitsB
      rCore rOutTop rScr hCOut hCS hOutS)
theorem cKickZeroSub46Opt_eval_mulVec_ket {n mScr : ℕ} (B : ℕ) (hB1 : 1 ≤ B) (hB27 : B ≤ 27)
    (hmScr : B + 19 ≤ mScr) (rCore : QRegister posCoreWires n) (rOutTop : QRegister (B + 1) n)
    (rScr : QRegister mScr n) (hCOut : rCore.DisjointWires rOutTop)
    (hCS : rCore.DisjointWires rScr) (hOutS : rOutTop.DisjointWires rScr)
    (δ : BitAssignment n) (hScr0 : ∀ s : Fin mScr, δ (rScr s) = 0) :
    (cKickZeroSub46Opt B hB1 hB27 hmScr rCore rOutTop rScr hCOut hCS hOutS).eval.1.mulVec (ket δ) =
      ((-1 : ℂ) ^ (midKickPhaseBitB B rCore rOutTop δ).val) • ket δ := by
  have hpBitsA : ∀ γ : BitAssignment 95, cleanRem 95 8 γ →
      (mk34_ctxCompD3_8.plug (.z ⟨0, by decide⟩)).evalBits γ = γ := by
    rw [mk34_pCompD3_8_eq]
    exact mk34_pCompD3_8_valid_and_bits.2
  have hpBitsB : ∀ γ : BitAssignment 102, cleanRem 102 15 γ →
      (mk34_ctxStageB15.plug (.z ⟨0, by decide⟩)).evalBits γ = γ := by
    rw [mk34_pStageB15_eq]
    exact mk34_pStageB15_valid_and_bits.2
  have hCongr1 : ∀ (rC : QRegister posCoreWires n) (β₁ β₂ : BitAssignment n),
      (∀ idx, β₁ (rC idx) = β₂ (rC idx)) → mk34_hold1Vec rC β₁ = mk34_hold1Vec rC β₂ :=
    fun rC β₁ β₂ hEq ↦ by
      funext i
      simp only [mk34_hold1Vec, mk34_holdVec, hEq]
  refine mk34_kick3StageGen_eval_mulVec_ket B 1 (B + 18) 8 (by omega) (by omega) _ _
    mk34_hold1Vec hCongr1 rCore rOutTop rScr hCS hOutS
    (mk34_cCompGen_eval_ket 1 (B + 18) 8 (by omega) (by omega) mk34_cLeafComp1On
      mk34_fLeafComp1 mk34_ctxCompD3_8 ⟨0, by decide⟩ mk34_hold1Vec hCongr1 rCore rScr hCS
      (mk34_cLeafComp1On_eval_mbh_ket _) hpBitsA
      (mk34_fLeafComp1_spec B (by omega) rCore rScr hCS))
    (fun β hHold hRest0 ↦ mk34_cStageBGen_eval_ket B hB1 hB27 1 (B + 18) 15 (by omega) (by omega)
      ⟨10, by decide⟩ ⟨14, by decide⟩ (by decide) 0 mk34_ctxStageB15 ⟨0, by decide⟩ hpBitsB
      mk34_ctxStageB15_fwdBits_below mk34_hold1Vec rCore rOutTop rScr hCOut hCS hOutS
      β hHold hRest0 rfl (fun γ hcr hc _ ↦ ?_)) δ hScr0
  obtain ⟨_, he97, hw97⟩ := mk34_ctxStageB15_fwdBits_wire ⟨97, by decide⟩ γ hcr
  obtain ⟨_, he101, hw101⟩ := mk34_ctxStageB15_fwdBits_wire ⟨101, by decide⟩ γ hcr
  refine ⟨?_, ?_⟩
  · change mk34_ctxStageB15.fwdBits γ ⟨97, by decide⟩ = _
    rw [he97.trans hw97.1, hc ⟨2, by decide⟩, hc ⟨1, by decide⟩]
    rfl
  · change mk34_ctxStageB15.fwdBits γ ⟨101, by decide⟩ = _
    rw [he101.trans hw101.2, hc ⟨2, by decide⟩, hc ⟨1, by decide⟩, hc ⟨0, by decide⟩,
        hc ⟨68, by decide⟩,
        hc ⟨15, by decide⟩, hc ⟨16, by decide⟩, hc ⟨17, by decide⟩, hc ⟨18, by decide⟩,
        hc ⟨19, by decide⟩,
        hc ⟨21, by decide⟩, hc ⟨22, by decide⟩, hc ⟨23, by decide⟩, hc ⟨24, by decide⟩,
        hc ⟨25, by decide⟩, hc ⟨26, by decide⟩, hc ⟨27, by decide⟩]
    rfl
/-- `21`-`TempAnd` context (`84 T`, `21` clean wires `88..108`) computing `u3` (`107`) and `d3`
(`108`). -/
def mk34_ctxComp21 : TempCtx 109 :=
  (ctxLitAnd 88 (by decide) ⟨16, by decide⟩ false ⟨15, by decide⟩ false
    (by decide) (by decide) (by decide)).append <|
  (ctxLitAnd 89 (by decide) ⟨17, by decide⟩ true ⟨88, by decide⟩ true
    (by decide) (by decide) (by decide)).append <|
  (ctxLitAnd 90 (by decide) ⟨19, by decide⟩ false ⟨18, by decide⟩ false
    (by decide) (by decide) (by decide)).append <|
  (ctxLitAnd 91 (by decide) ⟨90, by decide⟩ false ⟨89, by decide⟩ true
    (by decide) (by decide) (by decide)).append <|
  (ctxLitAnd 92 (by decide) ⟨27, by decide⟩ false ⟨26, by decide⟩ false
    (by decide) (by decide) (by decide)).append <|
  (ctxLitAnd 93 (by decide) ⟨24, by decide⟩ false ⟨23, by decide⟩ false
    (by decide) (by decide) (by decide)).append <|
  (ctxLitAnd 94 (by decide) ⟨22, by decide⟩ true ⟨21, by decide⟩ true
    (by decide) (by decide) (by decide)).append <|
  (ctxLitAnd 95 (by decide) ⟨93, by decide⟩ false ⟨94, by decide⟩ true
    (by decide) (by decide) (by decide)).append <|
  (ctxLitAnd 96 (by decide) ⟨25, by decide⟩ true ⟨95, by decide⟩ true
    (by decide) (by decide) (by decide)).append <|
  (ctxLitAnd 97 (by decide) ⟨92, by decide⟩ false ⟨96, by decide⟩ true
    (by decide) (by decide) (by decide)).append <|
  (ctxLitAnd 98 (by decide) ⟨35, by decide⟩ false ⟨34, by decide⟩ false
    (by decide) (by decide) (by decide)).append <|
  (ctxLitAnd 99 (by decide) ⟨32, by decide⟩ false ⟨31, by decide⟩ false
    (by decide) (by decide) (by decide)).append <|
  (ctxLitAnd 100 (by decide) ⟨30, by decide⟩ true ⟨29, by decide⟩ true
    (by decide) (by decide) (by decide)).append <|
  (ctxLitAnd 101 (by decide) ⟨100, by decide⟩ false ⟨28, by decide⟩ true
    (by decide) (by decide) (by decide)).append <|
  (ctxLitAnd 102 (by decide) ⟨99, by decide⟩ false ⟨101, by decide⟩ true
    (by decide) (by decide) (by decide)).append <|
  (ctxLitAnd 103 (by decide) ⟨33, by decide⟩ true ⟨102, by decide⟩ true
    (by decide) (by decide) (by decide)).append <|
  (ctxLitAnd 104 (by decide) ⟨98, by decide⟩ false ⟨103, by decide⟩ true
    (by decide) (by decide) (by decide)).append <|
  (ctxLitAnd 105 (by decide) ⟨0, by decide⟩ true ⟨91, by decide⟩ false
    (by decide) (by decide) (by decide)).append <|
  (ctxLitAnd 106 (by decide) ⟨68, by decide⟩ true ⟨97, by decide⟩ true
    (by decide) (by decide) (by decide)).append <|
  (ctxLitAnd 107 (by decide) ⟨106, by decide⟩ false ⟨105, by decide⟩ true
    (by decide) (by decide) (by decide)).append <|
  ctxLitAnd 108 (by decide) ⟨0, by decide⟩ false ⟨104, by decide⟩ false
    (by decide) (by decide) (by decide)
@[scoped simp] theorem mk34_ctxComp21_countTempAnd : mk34_ctxComp21.countTempAnd = 21 := by
  simp [mk34_ctxComp21]
/-- Leaf wire specification for `mk34_ctxComp21` on `86, 87, 107, 108`. -/
def mk34_comp21Spec (φ : BitAssignment 109) (s0 sr ge216 ge218 ge217 h0 h1 : ZMod 2) : Prop :=
  let d0 := (1 + s0) * ge216
  let u2 := (1 + sr) * (1 + ge218)
  let u3 := u2 * (1 + d0)
  let d3 := s0 * ge217
  φ ⟨86, by decide⟩ = h0 ∧
  φ ⟨87, by decide⟩ = h1 ∧
  φ ⟨107, by decide⟩ = u3 ∧
  φ ⟨108, by decide⟩ = d3
theorem mk34_ctxComp21_scoped_of_wire (q : Wire 109) :
    ∃ s21 : BitAssignment 109 → BitAssignment 109,
      ScopedBlock 109 21 s21 (.z q) (mk34_ctxComp21.plug (.z q)) ∧
      ∀ γ : BitAssignment 109,
        mk34_comp21Spec (s21 γ)
          (γ ⟨0, by decide⟩) (γ ⟨68, by decide⟩)
          (ge216Bit (γ ⟨15, by decide⟩) (γ ⟨16, by decide⟩) (γ ⟨17, by decide⟩)
            (γ ⟨18, by decide⟩) (γ ⟨19, by decide⟩))
          (ge218Bit (γ ⟨21, by decide⟩) (γ ⟨22, by decide⟩) (γ ⟨23, by decide⟩)
            (γ ⟨24, by decide⟩) (γ ⟨25, by decide⟩) (γ ⟨26, by decide⟩) (γ ⟨27, by decide⟩))
          (ge217Bit (γ ⟨28, by decide⟩) (γ ⟨29, by decide⟩) (γ ⟨30, by decide⟩) (γ ⟨31, by decide⟩)
            (γ ⟨32, by decide⟩) (γ ⟨33, by decide⟩) (γ ⟨34, by decide⟩) (γ ⟨35, by decide⟩))
          (γ ⟨86, by decide⟩) (γ ⟨87, by decide⟩) := by
  simp only [mk34_ctxComp21, TempCtx.append_plug, mk34_ctxLitAnd_plug]
  change ∃ s21, ScopedBlock 109 (109 - 88) s21 (.z q) _ ∧ _
  repeat refine ScopedBlock.exists_withLitAnd ?_
  refine ⟨fun γ ↦ γ, ScopedBlock.z_kick q, fun γ ↦ ?_⟩
  dsimp only [mk34_comp21Spec]
  simp only [Function.comp_apply, mk34_stepLitAnd_mk, eq_self, Nat.reduceEqDiff, ↓reduceIte,
    litVal_false, litVal_true]
  exact ⟨trivial, trivial, rfl, rfl⟩
theorem mk34_ctxComp21_fwdBits_wire (q : Wire 109)
    (γ : BitAssignment 109) (hγ : cleanRem 109 21 γ) :
    ∃ s21 : BitAssignment 109 → BitAssignment 109,
      mk34_ctxComp21.fwdBits γ q = s21 γ q ∧
      mk34_comp21Spec (s21 γ)
        (γ ⟨0, by decide⟩) (γ ⟨68, by decide⟩)
        (ge216Bit (γ ⟨15, by decide⟩) (γ ⟨16, by decide⟩) (γ ⟨17, by decide⟩)
          (γ ⟨18, by decide⟩) (γ ⟨19, by decide⟩))
        (ge218Bit (γ ⟨21, by decide⟩) (γ ⟨22, by decide⟩) (γ ⟨23, by decide⟩)
          (γ ⟨24, by decide⟩) (γ ⟨25, by decide⟩) (γ ⟨26, by decide⟩) (γ ⟨27, by decide⟩))
        (ge217Bit (γ ⟨28, by decide⟩) (γ ⟨29, by decide⟩) (γ ⟨30, by decide⟩) (γ ⟨31, by decide⟩)
          (γ ⟨32, by decide⟩) (γ ⟨33, by decide⟩) (γ ⟨34, by decide⟩) (γ ⟨35, by decide⟩))
        (γ ⟨86, by decide⟩) (γ ⟨87, by decide⟩) := by
  obtain ⟨s21, hB, hSpec⟩ := mk34_ctxComp21_scoped_of_wire q
  have h₁ := mk34_ctxComp21.plug_evalSign (.z q) γ
  have h₂ := hB.sign γ hγ
  dsimp [TempPhaseProg.evalSign] at h₁ h₂
  exact ⟨s21, h₁.symm.trans h₂, hSpec γ⟩
/-- Diagonal leaf phase polynomial `γ[86] * γ[107] + γ[87] * γ[108]` for `mk34_ctxComp21`. -/
def mk34_fLeafComp2 (γ : BitAssignment 109) : ZMod 2 :=
  γ ⟨86, by decide⟩ * γ ⟨107, by decide⟩ +
  γ ⟨87, by decide⟩ * γ ⟨108, by decide⟩
/-- `0`-`T`, `0`-`.TOFF` two-`CZ` leaf circuit for `mk34_ctxComp21`. -/
def mk34_cLeafComp2On {n : ℕ} (rComb : QRegister 109 n) : Circuit n :=
  asymMid_czCircuit (rComb ⟨86, by decide⟩) (rComb ⟨107, by decide⟩)
    (rComb.wires.injective.ne (by decide)) ;;ᶜ
  asymMid_czCircuit (rComb ⟨87, by decide⟩) (rComb ⟨108, by decide⟩)
    (rComb.wires.injective.ne (by decide))
@[scoped simp] theorem mk34_cLeafComp2On_count_toff {n : ℕ} (rComb : QRegister 109 n) :
    (mk34_cLeafComp2On rComb).count PrimitiveGate.TOFF = 0 := by
  simp [mk34_cLeafComp2On, asymMid_czCircuit_count_toff]
@[scoped simp] theorem mk34_cLeafComp2On_count_t {n : ℕ} (rComb : QRegister 109 n) :
    (mk34_cLeafComp2On rComb).count PrimitiveGate.T = 0 := by
  simp [mk34_cLeafComp2On, asymMid_czCircuit_count_t]
theorem mk34_cLeafComp2On_eval_mbh_ket {n : ℕ} (rComb : QRegister 109 n) (β : BitAssignment n) :
    (mk34_cLeafComp2On rComb).eval.1.mulVec (MeasureBranchHadamardSem.ket β) =
      ((-1 : ℂ) ^ (mk34_fLeafComp2 (fun idx ↦ β (rComb idx))).val) •
        MeasureBranchHadamardSem.ket β := by
  rw [mbh_ket_eq_ket, mk34_cLeafComp2On]
  simp only [asymMid_eval_seq_mulVec, Matrix.mulVec_smul, asymMid_ket_czCircuit,
    smul_smul, TempPhaseProg.neg_one_pow_zmod2_mul, mk34_fLeafComp2]
/-- Plugged `TempPhaseProg 109` witness for `mk34_ctxComp21`. -/
def mk34_pComp21 : TempPhaseProg 109 :=
  mk34_ctxComp21.plug (.z ⟨0, by decide⟩)
theorem mk34_pComp21_eq : mk34_ctxComp21.plug (.z ⟨0, by decide⟩) = mk34_pComp21 := rfl
theorem mk34_pComp21_valid_and_bits : ValidCleanRem 109 21 mk34_pComp21 ∧ (∀ γ : BitAssignment
    109, cleanRem 109 21 γ → mk34_pComp21.evalBits γ = γ) := by
  obtain ⟨_, hB, _⟩ := mk34_ctxComp21_scoped_of_wire ⟨0, by decide⟩
  exact ⟨hB.valid, hB.bits⟩
/-  Inner diagonal phase `Circuit n` for Stages A and C of `dKickZeroSub34OptDyn`. -/
/-  Inner diagonal phase `DynamicCircuit Var n` (`84 T`, `0` `.TOFF`). -/
/-  Stage A / Stage C reversible `Circuit n` XORing `(u3, d3)` onto `rHold2`. -/
/- Stage A / Stage C `0`-`.TOFF` `DynamicCircuit Var n` (`84 T`) XORing `(u3, d3)` onto `rHold2`. -/
/-  Target `2`-bit vector `(u3, d3)` XORed onto `rHold2` by `mk34_cComp2`. -/
/-  Combined `90`-wire register `rAct88 ++ rSub2` for outer Stage B of `dKickZeroSub34OptDyn`. -/
attribute [local irreducible] mk34_ctxComp21
/-- Target `2`-bit vector `(u3, d3)` XORed onto `rHold2` by `cKickZeroSub34Opt` Stage A/C. -/
def mk34_hold2Vec {n : ℕ} (rCore : QRegister posCoreWires n) (β : BitAssignment n) :
    BitAssignment 2 :=
  let s0 := β (rCore ⟨3948, by decide⟩)
  let sr := β (rCore ⟨4016, by decide⟩)
  let ge216 := ge216Bit (β (rCore ⟨3963, by decide⟩)) (β (rCore ⟨3964, by decide⟩))
    (β (rCore ⟨3965, by decide⟩)) (β (rCore ⟨3966, by decide⟩)) (β (rCore ⟨3967, by decide⟩))
  let ge218 := ge218Bit (β (rCore ⟨3969, by decide⟩)) (β (rCore ⟨3970, by decide⟩))
    (β (rCore ⟨3971, by decide⟩)) (β (rCore ⟨3972, by decide⟩)) (β (rCore ⟨3973, by decide⟩))
    (β (rCore ⟨3974, by decide⟩)) (β (rCore ⟨3975, by decide⟩))
  let ge217 := ge217Bit (β (rCore ⟨3976, by decide⟩)) (β (rCore ⟨3977, by decide⟩))
    (β (rCore ⟨3978, by decide⟩)) (β (rCore ⟨3979, by decide⟩)) (β (rCore ⟨3980, by decide⟩))
    (β (rCore ⟨3981, by decide⟩)) (β (rCore ⟨3982, by decide⟩)) (β (rCore ⟨3983, by decide⟩))
  let d0 := (1 + s0) * ge216
  let u2 := (1 + sr) * (1 + ge218)
  let u3 := u2 * (1 + d0)
  let d3 := s0 * ge217
  fun i ↦ if i.val = 0 then u3 else d3
theorem mk34_fLeafComp2_spec {n mScr : ℕ} (B : ℕ) (hmScr : 2 + max 21 (B + 5) ≤ mScr)
    (rCore : QRegister posCoreWires n) (rScr : QRegister mScr n) (hCS : rCore.DisjointWires rScr)
    (δ : BitAssignment n)
    (hcr : cleanRem 109 21
      (fun idx ↦ δ (mk34_rCombGen 2 (max 21 (B + 5)) 21 hmScr (by omega) rCore rScr hCS idx))) :
    mk34_fLeafComp2 (mk34_ctxComp21.fwdBits (fun idx ↦
      δ (mk34_rCombGen 2 (max 21 (B + 5)) 21 hmScr (by omega) rCore rScr hCS idx))) =
      ∑ i : Fin 2,
        δ (mk34_rHoldGen 2 (max 21 (B + 5)) hmScr rScr i) * mk34_hold2Vec rCore δ i := by
  rw [Fin.sum_univ_two]
  let γ : BitAssignment 109 := fun idx ↦
    δ (mk34_rCombGen 2 (max 21 (B + 5)) 21 hmScr (by omega) rCore rScr hCS idx)
  obtain ⟨_, he86, hw86⟩ := mk34_ctxComp21_fwdBits_wire ⟨86, by decide⟩ γ hcr
  obtain ⟨_, he87, hw87⟩ := mk34_ctxComp21_fwdBits_wire ⟨87, by decide⟩ γ hcr
  obtain ⟨_, he107, hw107⟩ := mk34_ctxComp21_fwdBits_wire ⟨107, by decide⟩ γ hcr
  obtain ⟨_, he108, hw108⟩ := mk34_ctxComp21_fwdBits_wire ⟨108, by decide⟩ γ hcr
  have hc (k : Fin 86) : γ ⟨k.val, by omega⟩ =
      δ (rCore ⟨3948 + k.val, mk34_lt_posCore (by omega)⟩) :=
    congrArg δ (mk34_rCombGen_core 2 (max 21 (B + 5)) 21 hmScr (by omega) rCore rScr hCS k)
  have hh0 : γ ⟨86, by decide⟩ = δ (mk34_rHoldGen 2 (max 21 (B + 5)) hmScr rScr 0) :=
    congrArg δ (mk34_rCombGen_hold 2 (max 21 (B + 5)) 21 hmScr (by omega) rCore rScr hCS 0)
  have hh1 : γ ⟨87, by decide⟩ = δ (mk34_rHoldGen 2 (max 21 (B + 5)) hmScr rScr 1) :=
    congrArg δ (mk34_rCombGen_hold 2 (max 21 (B + 5)) 21 hmScr (by omega) rCore rScr hCS 1)
  dsimp only [mk34_fLeafComp2, mk34_hold2Vec, Fin.val_zero, Fin.val_one, ↓reduceIte,
    (by decide : (1 : ℕ) ≠ 0)]
  rw [he86.trans hw86.1, he87.trans hw87.2.1, he107.trans hw107.2.2.1, he108.trans hw108.2.2.2,
      hh0, hh1,
      hc ⟨0, by decide⟩, hc ⟨68, by decide⟩,
      hc ⟨15, by decide⟩, hc ⟨16, by decide⟩, hc ⟨17, by decide⟩, hc ⟨18, by decide⟩, hc ⟨19,
        by decide⟩,
      hc ⟨21, by decide⟩, hc ⟨22, by decide⟩, hc ⟨23, by decide⟩, hc ⟨24, by decide⟩,
      hc ⟨25, by decide⟩, hc ⟨26, by decide⟩, hc ⟨27, by decide⟩,
      hc ⟨28, by decide⟩, hc ⟨29, by decide⟩, hc ⟨30, by decide⟩, hc ⟨31, by decide⟩,
      hc ⟨32, by decide⟩, hc ⟨33, by decide⟩, hc ⟨34, by decide⟩, hc ⟨35, by decide⟩]
  rfl
/-- `2`-`TempAnd` context (`8 T`, `2` clean wires `88..89`) computing `u1` (`88`) and `vL = u1 * u3`
(`89`). -/
def mk34_ctxStageB2 : TempCtx 90 :=
  (ctxLitAnd 88 (by decide) ⟨2, by decide⟩ true ⟨1, by decide⟩ true
    (by decide) (by decide) (by decide)).append <|
  ctxLitAnd 89 (by decide) ⟨88, by decide⟩ false ⟨86, by decide⟩ false
    (by decide) (by decide) (by decide)
@[scoped simp] theorem mk34_ctxStageB2_countTempAnd : mk34_ctxStageB2.countTempAnd = 2 := by
  simp [mk34_ctxStageB2]
theorem mk34_ctxStageB2_fwdBits_below (γ : BitAssignment 90) (w : Wire 90) (hw : w.val < 88) :
    mk34_ctxStageB2.fwdBits γ w = γ w := by
  simp only [mk34_ctxStageB2, mk34_append_fwdBits]
  repeat rw [mk34_ctxLitAnd_fwdBits_of_ne _ _ _ _ _ _ _ _ _ _ w (by omega)]
theorem mk34_ctxStageB2_scoped_of_wire (q : Wire 90) :
    ∃ s2 : BitAssignment 90 → BitAssignment 90,
      ScopedBlock 90 2 s2 (.z q) (mk34_ctxStageB2.plug (.z q)) ∧
      ∀ γ : BitAssignment 90,
        s2 γ ⟨88, by decide⟩ = (1 + γ ⟨2, by decide⟩) * (1 + γ ⟨1, by decide⟩) ∧
        s2 γ ⟨89, by decide⟩ =
          ((1 + γ ⟨2, by decide⟩) * (1 + γ ⟨1, by decide⟩)) * γ ⟨86, by decide⟩ := by
  simp only [mk34_ctxStageB2, TempCtx.append_plug, mk34_ctxLitAnd_plug]
  change ∃ s2, ScopedBlock 90 (90 - 88) s2 (.z q) _ ∧ _
  repeat refine ScopedBlock.exists_withLitAnd ?_
  refine ⟨fun γ ↦ γ, ScopedBlock.z_kick q, fun γ ↦ ?_⟩
  simp only [Function.comp_apply, mk34_stepLitAnd_mk, eq_self, Nat.reduceEqDiff, ↓reduceIte,
    litVal_false, litVal_true]
  exact ⟨trivial, trivial⟩
theorem mk34_ctxStageB2_fwdBits_wire (q : Wire 90)
    (γ : BitAssignment 90) (hγ : cleanRem 90 2 γ) :
    ∃ s2 : BitAssignment 90 → BitAssignment 90,
      mk34_ctxStageB2.fwdBits γ q = s2 γ q ∧
      s2 γ ⟨88, by decide⟩ = (1 + γ ⟨2, by decide⟩) * (1 + γ ⟨1, by decide⟩) ∧
      s2 γ ⟨89, by decide⟩ =
        ((1 + γ ⟨2, by decide⟩) * (1 + γ ⟨1, by decide⟩)) * γ ⟨86, by decide⟩ := by
  obtain ⟨s2, hB, hSpec⟩ := mk34_ctxStageB2_scoped_of_wire q
  have h₁ := mk34_ctxStageB2.plug_evalSign (.z q) γ
  have h₂ := hB.sign γ hγ
  dsimp [TempPhaseProg.evalSign] at h₁ h₂
  exact ⟨s2, h₁.symm.trans h₂, hSpec γ⟩
/-- Plugged `TempPhaseProg 90` witness for `mk34_ctxStageB2`. -/
def mk34_pStageB2 : TempPhaseProg 90 :=
  mk34_ctxStageB2.plug (.z ⟨0, by decide⟩)
theorem mk34_pStageB2_eq : mk34_ctxStageB2.plug (.z ⟨0, by decide⟩) = mk34_pStageB2 := rfl
theorem mk34_pStageB2_valid_and_bits : ValidCleanRem 90 2 mk34_pStageB2 ∧ (∀ γ : BitAssignment
    90, cleanRem 90 2 γ → mk34_pStageB2.evalBits γ = γ) := by
  obtain ⟨_, hB, _⟩ := mk34_ctxStageB2_scoped_of_wire ⟨0, by decide⟩
  exact ⟨hB.valid, hB.bits⟩
attribute [local irreducible] mk34_ctxStageB2
/- `3`-wire hold register `(rSub2 0, rSub2 1, rHold2 1)` (`= (u1, vL, d3)`) for
`dKickZeroSub34OptDyn`. -/
/-  Maps a `90`-wire Stage-B bit assignment `γ` and ambient `β` to the `(mk34_mB B)`-wire input
of `mk34_ctxMidBInPlace`. -/
/-  Stage B reversible `Circuit n` for `dKickZeroSub34OptDyn` (`2 + B + 3` Toffoli pairs). -/
/-  Stage B `0`-`.TOFF` `DynamicCircuit Var n` (`4 * B + 20` `T`) for `dKickZeroSub34OptDyn`. -/
/-- Top-level `max 23 (B + 7)`-clean-wire (`B + 7 ≤ 34` for `16 ≤ B ≤ 27`, `≤ 34` for `1 ≤ B ≤ 27`)
reversible `Circuit n` for the 3-stage mid-phase kickback. -/
def cKickZeroSub34Opt {n mScr : ℕ} (B : ℕ) (hB1 : 1 ≤ B) (hB27 : B ≤ 27)
    (hmScr : max 23 (B + 7) ≤ mScr)
    (rCore : QRegister posCoreWires n) (rOutTop : QRegister (B + 1) n) (rScr : QRegister mScr n)
    (hCOut : rCore.DisjointWires rOutTop) (hCS : rCore.DisjointWires rScr)
    (hOutS : rOutTop.DisjointWires rScr) : Circuit n :=
  let cA := mk34_cCompGen 2 (max 21 (B + 5)) 21 (by omega) (by omega) mk34_cLeafComp2On
    mk34_ctxComp21 rCore rScr hCS
  let cB := mk34_cStageBGen B hB1 hB27 2 (max 21 (B + 5)) 2 (by omega) (by omega)
    0 1 (by decide) 1 mk34_ctxStageB2 rCore rOutTop rScr hCOut hCS hOutS
  cA ;;ᶜ cB ;;ᶜ cA
/-- Top-level `max 23 (B + 7)`-clean-wire (`B + 7 ≤ 34` for `16 ≤ B ≤ 27`, `≤ 34` for `1 ≤ B ≤ 27`)
`0`-`.TOFF` `DynamicCircuit Var n` (`188 + 4 * B` `T`). -/
def dKickZeroSub34OptDyn {Var : Type} {n mScr : ℕ} (B : ℕ) (hB1 : 1 ≤ B) (hB27 : B ≤ 27)
    (hmScr : max 23 (B + 7) ≤ mScr) (v : Var) (rCore : QRegister posCoreWires n)
    (rOutTop : QRegister (B + 1) n) (rScr : QRegister mScr n)
    (hCOut : rCore.DisjointWires rOutTop) (hCS : rCore.DisjointWires rScr)
    (hOutS : rOutTop.DisjointWires rScr) : DynamicCircuit Var n :=
  let dA := mk34_dCompGen 2 (max 21 (B + 5)) 21 (by omega) (by omega) v mk34_cLeafComp2On
    mk34_ctxComp21 rCore rScr hCS
  let dB := mk34_dStageBGen B hB1 hB27 2 (max 21 (B + 5)) 2 (by omega) (by omega)
    0 1 (by decide) 1 mk34_ctxStageB2 v rCore rOutTop rScr hCOut hCS hOutS
  .seq dA (.seq dB dA)
@[scoped simp] theorem count_dKickZeroSub34OptDyn_toff {Var : Type} {n mScr : ℕ}
    (B : ℕ) (hB1 : 1 ≤ B) (hB27 : B ≤ 27) (hmScr : max 23 (B + 7) ≤ mScr) (v : Var)
    (rCore : QRegister posCoreWires n) (rOutTop : QRegister (B + 1) n) (rScr : QRegister mScr n)
    (hCOut : rCore.DisjointWires rOutTop) (hCS : rCore.DisjointWires rScr)
    (hOutS : rOutTop.DisjointWires rScr) :
    (dKickZeroSub34OptDyn B hB1 hB27 hmScr v rCore rOutTop rScr hCOut hCS hOutS).count
      PrimitiveGate.TOFF = 0 := by
  simp [dKickZeroSub34OptDyn, mk34_count_dCompGen_toff, mk34_cLeafComp2On_count_toff,
    mk34_count_dStageBGen_toff]
@[scoped simp] theorem count_dKickZeroSub34OptDyn_t {Var : Type} {n mScr : ℕ}
    (B : ℕ) (hB1 : 1 ≤ B) (hB27 : B ≤ 27) (hmScr : max 23 (B + 7) ≤ mScr) (v : Var)
    (rCore : QRegister posCoreWires n) (rOutTop : QRegister (B + 1) n) (rScr : QRegister mScr n)
    (hCOut : rCore.DisjointWires rOutTop) (hCS : rCore.DisjointWires rScr)
    (hOutS : rOutTop.DisjointWires rScr) :
    (dKickZeroSub34OptDyn B hB1 hB27 hmScr v rCore rOutTop rScr hCOut hCS hOutS).count
      PrimitiveGate.T = 188 + 4 * B := by
  simp only [dKickZeroSub34OptDyn, DynamicCircuit.count,
    mk34_count_dCompGen_t 2 (max 21 (B + 5)) 21 (by omega) (by omega) v mk34_cLeafComp2On
      mk34_ctxComp21 rCore rScr hCS mk34_cLeafComp2On_count_t,
    mk34_count_dStageBGen_t, mk34_ctxComp21_countTempAnd, mk34_ctxStageB2_countTempAnd]
  ring
theorem dKickZeroSub34OptDyn_preservesStoreConst {Var : Type} [Fintype Var] [DecidableEq Var]
    {n mScr : ℕ} (B : ℕ) (hB1 : 1 ≤ B) (hB27 : B ≤ 27) (hmScr : max 23 (B + 7) ≤ mScr)
    (v : Var) (rCore : QRegister posCoreWires n) (rOutTop : QRegister (B + 1) n)
    (rScr : QRegister mScr n) (hCOut : rCore.DisjointWires rOutTop)
    (hCS : rCore.DisjointWires rScr) (hOutS : rOutTop.DisjointWires rScr) :
    PreservesStoreConst
      (dKickZeroSub34OptDyn B hB1 hB27 hmScr v rCore rOutTop rScr hCOut hCS hOutS) :=
  PreservesStoreConst.seq (mk34_dCompGen_preservesStoreConst _ _ _ _ _ _ _ _ _ _ _)
    (PreservesStoreConst.seq (mk34_dStageBGen_preservesStoreConst _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      _ _ _)
      (mk34_dCompGen_preservesStoreConst _ _ _ _ _ _ _ _ _ _ _))
theorem realizesCleanUnitary_dKickZeroSub34OptDyn_scr
    {Var : Type} [Fintype Var] [DecidableEq Var] {n mScr : ℕ} [NeZero (2 ^ n)]
    (B : ℕ) (hB1 : 1 ≤ B) (hB27 : B ≤ 27) (hmScr : max 23 (B + 7) ≤ mScr) (v : Var)
    (rCore : QRegister posCoreWires n) (rOutTop : QRegister (B + 1) n) (rScr : QRegister mScr n)
    (hCOut : rCore.DisjointWires rOutTop) (hCS : rCore.DisjointWires rScr)
    (hOutS : rOutTop.DisjointWires rScr) :
    RealizesCleanUnitary v (projZeroAll mScr rScr.wires)
      (dKickZeroSub34OptDyn B hB1 hB27 hmScr v rCore rOutTop rScr hCOut hCS hOutS)
      (cKickZeroSub34Opt B hB1 hB27 hmScr rCore rOutTop rScr hCOut hCS hOutS).eval := by
  have hpvA : ValidCleanRem 109 21 (mk34_ctxComp21.plug (.z ⟨0, by decide⟩)) := by
    rw [mk34_pComp21_eq]
    exact mk34_pComp21_valid_and_bits.1
  have hpBitsA : ∀ γ : BitAssignment 109, cleanRem 109 21 γ →
      (mk34_ctxComp21.plug (.z ⟨0, by decide⟩)).evalBits γ = γ := by
    rw [mk34_pComp21_eq]
    exact mk34_pComp21_valid_and_bits.2
  have hpvB : ValidCleanRem 90 2 (mk34_ctxStageB2.plug (.z ⟨0, by decide⟩)) := by
    rw [mk34_pStageB2_eq]
    exact mk34_pStageB2_valid_and_bits.1
  have hpBitsB : ∀ γ : BitAssignment 90, cleanRem 90 2 γ →
      (mk34_ctxStageB2.plug (.z ⟨0, by decide⟩)).evalBits γ = γ := by
    rw [mk34_pStageB2_eq]
    exact mk34_pStageB2_valid_and_bits.2
  have hCongr2 : ∀ (rC : QRegister posCoreWires n) (β₁ β₂ : BitAssignment n),
      (∀ idx, β₁ (rC idx) = β₂ (rC idx)) → mk34_hold2Vec rC β₁ = mk34_hold2Vec rC β₂ :=
    fun rC β₁ β₂ hEq ↦ by
      funext i
      simp only [mk34_hold2Vec, hEq]
  exact mk34_realizesCleanUnitary_kick3StageGen 2 (max 21 (B + 5)) (by omega) v rScr _ _ _ _
    (mk34_realizesCleanUnitary_dCompGen_rest 2 (max 21 (B + 5)) 21 (by omega) (by omega) v
      mk34_cLeafComp2On mk34_fLeafComp2 mk34_ctxComp21 ⟨0, by decide⟩ mk34_hold2Vec
      rCore rScr hCS (mk34_cLeafComp2On_eval_mbh_ket _) hpvA hpBitsA
      (mk34_fLeafComp2_spec B (by omega) rCore rScr hCS))
    (mk34_realizesCleanUnitary_dStageBGen_rest B hB1 hB27 2 (max 21 (B + 5)) 2 (by omega) (by omega)
      0 1 (by decide) 1 mk34_ctxStageB2 ⟨0, by decide⟩ hpvB v rCore rOutTop rScr hCOut hCS hOutS)
    (mk34_cCompGen_preserves_rest 2 (max 21 (B + 5)) 21 (by omega) (by omega) mk34_cLeafComp2On
      mk34_ctxComp21 mk34_hold2Vec rCore rScr hCS
      (mk34_cCompGen_eval_ket 2 (max 21 (B + 5)) 21 (by omega) (by omega) mk34_cLeafComp2On
        mk34_fLeafComp2 mk34_ctxComp21 ⟨0, by decide⟩ mk34_hold2Vec hCongr2 rCore rScr hCS
        (mk34_cLeafComp2On_eval_mbh_ket _) hpBitsA
        (mk34_fLeafComp2_spec B (by omega) rCore rScr hCS)))
    (mk34_cStageBGen_preserves_rest B hB1 hB27 2 (max 21 (B + 5)) 2 (by omega) (by omega)
      0 1 (by decide) 1 mk34_ctxStageB2 ⟨0, by decide⟩ hpBitsB rCore rOutTop rScr hCOut hCS hOutS)
theorem cKickZeroSub34Opt_eval_mulVec_ket {n mScr : ℕ}
    (B : ℕ) (hB1 : 1 ≤ B) (hB27 : B ≤ 27) (hmScr : max 23 (B + 7) ≤ mScr)
    (rCore : QRegister posCoreWires n) (rOutTop : QRegister (B + 1) n) (rScr : QRegister mScr n)
    (hCOut : rCore.DisjointWires rOutTop) (hCS : rCore.DisjointWires rScr)
    (hOutS : rOutTop.DisjointWires rScr) (δ : BitAssignment n)
    (hScr0 : ∀ s : Fin mScr, δ (rScr s) = 0) :
    (cKickZeroSub34Opt B hB1 hB27 hmScr rCore rOutTop rScr hCOut hCS hOutS).eval.1.mulVec (ket δ) =
      ((-1 : ℂ) ^ (midKickPhaseBitB B rCore rOutTop δ).val) • ket δ := by
  have hpBitsA : ∀ γ : BitAssignment 109, cleanRem 109 21 γ →
      (mk34_ctxComp21.plug (.z ⟨0, by decide⟩)).evalBits γ = γ := by
    rw [mk34_pComp21_eq]
    exact mk34_pComp21_valid_and_bits.2
  have hpBitsB : ∀ γ : BitAssignment 90, cleanRem 90 2 γ →
      (mk34_ctxStageB2.plug (.z ⟨0, by decide⟩)).evalBits γ = γ := by
    rw [mk34_pStageB2_eq]
    exact mk34_pStageB2_valid_and_bits.2
  have hCongr2 : ∀ (rC : QRegister posCoreWires n) (β₁ β₂ : BitAssignment n),
      (∀ idx, β₁ (rC idx) = β₂ (rC idx)) → mk34_hold2Vec rC β₁ = mk34_hold2Vec rC β₂ :=
    fun rC β₁ β₂ hEq ↦ by
      funext i
      simp only [mk34_hold2Vec, hEq]
  refine mk34_kick3StageGen_eval_mulVec_ket B 2 (max 21 (B + 5)) 21 (by omega) (by omega) _ _
    mk34_hold2Vec hCongr2 rCore rOutTop rScr hCS hOutS
    (mk34_cCompGen_eval_ket 2 (max 21 (B + 5)) 21 (by omega) (by omega) mk34_cLeafComp2On
      mk34_fLeafComp2 mk34_ctxComp21 ⟨0, by decide⟩ mk34_hold2Vec hCongr2 rCore rScr hCS
      (mk34_cLeafComp2On_eval_mbh_ket _) hpBitsA
      (mk34_fLeafComp2_spec B (by omega) rCore rScr hCS))
    (fun β hHold hRest0 ↦ mk34_cStageBGen_eval_ket B hB1 hB27 2 (max 21 (B + 5)) 2
      (by omega) (by omega) 0 1 (by decide) 1 mk34_ctxStageB2 ⟨0, by decide⟩ hpBitsB
      mk34_ctxStageB2_fwdBits_below mk34_hold2Vec rCore rOutTop rScr hCOut hCS hOutS
      β hHold hRest0 rfl (fun γ hcr hc hh ↦ ?_)) δ hScr0
  obtain ⟨_, he88, hw88⟩ := mk34_ctxStageB2_fwdBits_wire ⟨88, by decide⟩ γ hcr
  obtain ⟨_, he89, hw89⟩ := mk34_ctxStageB2_fwdBits_wire ⟨89, by decide⟩ γ hcr
  have hh0 : γ ⟨86, by decide⟩ = mk34_hold2Vec rCore β 0 := hh 0
  refine ⟨?_, ?_⟩
  · change mk34_ctxStageB2.fwdBits γ ⟨88, by decide⟩ = _
    rw [he88.trans hw88.1, hc ⟨2, by decide⟩, hc ⟨1, by decide⟩]
    rfl
  · change mk34_ctxStageB2.fwdBits γ ⟨89, by decide⟩ = _
    rw [he89.trans hw89.2, hh0, hc ⟨2, by decide⟩, hc ⟨1, by decide⟩]
    rfl
/-!
## Section 6: Generic `dMidK6SubGenDyn` & Optimized `dMidK6Sub` Oracles
-/
section MidK6Gen
open SpecsAux SpecsAux.SpecMirror
open BchCubeDecoder hiding ket_diagonalSignUnitaryN
open PosSlots24SpectatorPrunedPhase.MidK6Sub252
open MidK6Sub126
attribute [local irreducible]
  k6SuperRow w128OrbitBiasedQ30 k6ReconTop6BitBool pos24TailMag30 pos24TailSign k6BitNat
  k6SubGatesPalBit k6Pal24Bit k6P0Bit k6P1Bit k6_oneHot4Val prunedEffIdx cKickZeroSub34
  cKickZeroSubSingle dKickZeroSubSingleDyn cKickZeroSub46Opt
  dKickZeroSub46OptDyn cKickZeroSub34Opt dKickZeroSub34OptDyn
  phaseLookupPrunedCircuit hadamardReg p2t_cPhaseMuxCol64
  k6LoadTreeCircuit k6_cOneHot4Raw k6_cPhaseMux4All6Raw k6_cXorDiffTop6Raw
  k6_cCzCol64Raw k6_cCzSweep27Raw mkState recoverInit K6StageSpec
  DynCircuitExt.substToffoliCircuit
/-- Combined `((30 - B) + (mClean - 95))`-wire clean scratch register
`rClean[64 .. 64 + (30 - B)) ++ rClean[95 .. mClean)` available at `|0⟩` during Stage 6. -/
abbrev rScrStage6Of {n mClean : ℕ} (B : ℕ) (_hB1 : 1 ≤ B) (hB27 : B ≤ 27)
    (hmClean : 126 ≤ mClean) (rClean : QRegister mClean n) : QRegister
    ((30 - B) + (mClean - 95)) n := (rClean.slice 64 (30 - B) (by omega)).concat
    (rClean.slice 95 (mClean - 95) (by omega)) (slice_disjoint_slice rClean 64 (30 - B) 95
    (mClean - 95) (by omega) (by omega) (Or.inl (by omega)))
theorem disj_rOutTop_rScrStage6 {n mClean : ℕ} (B : ℕ) (hB1 : 1 ≤ B) (hB27 : B ≤ 27)
    (hmClean : 126 ≤ mClean) (rClean : QRegister mClean n) :
    (rOutTopOf B hB1 hB27 hmClean rClean).DisjointWires
    (rScrStage6Of B hB1 hB27 hmClean rClean) := k6_disjoint_concat_right
    (slice_disjoint_slice rClean (64 + (30 - B)) (B + 1) 64 (30 - B) (by omega) (by omega)
    (Or.inr (by omega))) (slice_disjoint_slice rClean (64 + (30 - B)) (B + 1) 95 (mClean -
    95) (by omega) (by omega) (Or.inl (by omega))) _
theorem disj_rCore_rScrStage6 {n mClean : ℕ} (B : ℕ) (hB1 : 1 ≤ B) (hB27 : B ≤ 27)
    (hmClean : 126 ≤ mClean) (rCore : QRegister posCoreWires n) (rClean : QRegister mClean n)
    (hCC : rCore.DisjointWires rClean) : rCore.DisjointWires
    (rScrStage6Of B hB1 hB27 hmClean rClean) := k6_disjoint_concat_right
    (hCC.compose_right _) (hCC.compose_right _) _
theorem rScrStage6Of_zero {n mClean : ℕ} (B : ℕ) (hB1 : 1 ≤ B) (hB27 : B ≤ 27)
    (hmClean : 126 ≤ mClean) (rCore : QRegister posCoreWires n) (rOrbit16 : QRegister 16 n)
    (rClean : QRegister mClean n) (hCC : rCore.DisjointWires rClean) (γ₀ : BitAssignment n)
    (s : Fin ((30 - B) + (mClean - 95))) : mkState rCore rClean hCC γ₀
    (vClean5 B rOrbit16 rClean γ₀) (vDirty1 rCore rOrbit16 γ₀)
    (rScrStage6Of B hB1 hB27 hmClean rClean s) = 0 := by
  by_cases hs : s.val < 30 - B
  · have hsEq : s = Fin.castAdd (mClean - 95) ⟨s.val, hs⟩ := Fin.ext rfl
    dsimp only [rScrStage6Of]
    rw [hsEq, QRegister.concat_apply_left, QRegister.slice_apply, mkState_clean]
    dsimp [vClean5]
    have h1 : ¬ (64 + s.val < 64) := by omega
    have h2 : 64 + s.val < 64 + (30 - B) := by omega
    simp [h1, h2]
  · have hsEq : s = Fin.natAdd (30 - B) (⟨s.val - (30 - B), by omega⟩ : Fin (mClean - 95)) := by
      ext; dsimp [Fin.natAdd]; omega
    dsimp only [rScrStage6Of]
    rw [hsEq, QRegister.concat_apply_right, QRegister.slice_apply, mkState_clean]
    dsimp [vClean5]
    have h1 : ¬ (95 + (s.val - (30 - B)) < 64) := by omega
    have h2 : ¬ (95 + (s.val - (30 - B)) < 64 + (30 - B)) := by omega
    have h3 : ¬ (95 + (s.val - (30 - B)) < 95) := by omega
    simp [h1, h2, h3]
theorem rScr34Of_zero {n mClean : ℕ} (B : ℕ) (_hB1 : 1 ≤ B) (hB27 : B ≤ 27)
    (hmClean : 126 ≤ mClean) (rCore : QRegister posCoreWires n) (rOrbit16 : QRegister 16 n)
    (rClean : QRegister mClean n) (hCC : rCore.DisjointWires rClean) (γ₀ : BitAssignment n)
    (s : Fin 34) : mkState rCore rClean hCC γ₀ (vClean5 B rOrbit16 rClean γ₀)
    (vDirty1 rCore rOrbit16 γ₀) (rScr34Of hmClean rClean s) = 0 := by
  by_cases hs : s.val < 3
  · have hsEq : s = Fin.castAdd 31 ⟨s.val, hs⟩ := Fin.ext rfl
    dsimp only [rScr34Of]
    rw [hsEq, QRegister.concat_apply_left]
    dsimp only [rHold3Of]
    rw [QRegister.slice_apply, mkState_clean]
    dsimp [vClean5]
    have h1 : ¬ (64 + s.val < 64) := by omega
    have h2 : 64 + s.val < 64 + (30 - B) := by omega
    simp [h1, h2]
  · have hsEq : s = Fin.natAdd 3 (⟨s.val - 3, by omega⟩ : Fin 31) := by
      ext; dsimp [Fin.natAdd]; omega
    dsimp only [rScr34Of]
    rw [hsEq, QRegister.concat_apply_right]
    dsimp only [rSub31Of]
    rw [QRegister.slice_apply, mkState_clean]
    dsimp [vClean5]
    have h1 : ¬ (95 + (s.val - 3) < 64) := by omega
    have h2 : ¬ (95 + (s.val - 3) < 64 + (30 - B)) := by omega
    have h3 : ¬ (95 + (s.val - 3) < 95) := by omega
    simp [h1, h2, h3]
end MidK6Gen
end MidK6UnbufOpt
end
end MidK6UnbufOptAndPackedSand

noncomputable section Twist558AndShared108
set_option maxRecDepth 4096

section
namespace Twist558AndShared108
noncomputable section
open QuantumComputation Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt
open HermitianMat Real
open scoped Matrix BigOperators ComplexOrder MatrixOrder Circuit.Notation
open SpecsAux SpecsAux.SpecMirror
open SpecsAux.DyadicSubgridToeplitz512AndShift
open SpecsAux.PhaseGradCatalystCore
open DyadicQft64 hiding dyadicTurn phaseGradKet xAllCircuit count_xAllCircuit_toff
  count_xAllCircuit_t
open NuclearTwistAndXor654Concrete
open NuclearTwistRealizes
open NuclearTwistMulKickAndBridge288
open ProjZ512QftAndTwist288 hiding basisBits_symm_apply fullSysCoreWires_eq_add
open FusedVepCore288 JunctionApexCSA288
open InterWalkRSum42Hoist
open Proj3DCut.WhHelper
open Proj3DCut
open ProjZ512QftAndTwist288 (vepLockVal vepLockVal_eq)
open JunctionUncondHadTailCut
local instance (priority := 1000000) instNeZeroTwoPowK21 (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩
set_option backward.isDefEq.respectTransparency true
set_option exponentiation.threshold 8192
set_option maxRecDepth 4096
/-!
## Section 1: `45`-Wire HadCut Helpers & Fused `dWhStg0Rem_3D_Pos45` (`179 T`, `.TOFF = 0`)
-/
/-- Internal `45`-wire Hadamard-tail-cut helper `dWhStg7_3D_Pos45`. -/
noncomputable def dWhStg7_3D_Pos45 {mPayload : ℕ} (isInv : Bool) (hm : 22 ≤ mPayload)
    {Var : Type} {n : ℕ} (v : Var) (rCore : QRegister (fullSysCoreWires mPayload) n)
    (rWork : QRegister JunctionPrefixPruned220.mWork45 n) (hCW : rCore.DisjointWires rWork) :
    DynamicCircuit Var n :=
  let wf := rWork 6
  let rW38 := rWork.slice 7 38 (by decide)
  let rP := rW38.slice 0 3 (by decide)
  have hCW38 : rCore.DisjointWires rW38 := (QRegExt.disjointWires_mono_right hCW)
    (QRegister.image_compose_subset rWork _)
  have hCW_P : rCore.DisjointWires rP := (QRegExt.disjointWires_mono_right hCW38)
    (QRegister.image_compose_subset rW38 _)
  have hB0_7 : ∀ w : Fin 3, rCosetB0 hm rCore w ≠ rProjAxis rCore w 7 :=
    fun w ↦ disj_wire_ne (rCosetB0_disj_rProjAxis hm rCore w) w 7
  have hB0_P : ∀ w : Fin 3, rCosetB0 hm rCore w ≠ rP w :=
    fun w ↦ disj_wire_ne ((QRegExt.disjointWires_mono_left hCW_P) (rCosetB0_sub_rCore hm rCore)) w w
  have hp7_P : ∀ w : Fin 3, rProjAxis rCore w 7 ≠ rP w :=
    fun w ↦ disj_wire_ne ((QRegExt.disjointWires_mono_left hCW_P) (rProjAxis_sub_rCore rCore w)) 7 w
  have hwfP : ∀ w : Fin 3, wf ≠ rP w := fun w hEq ↦
    reg_not_mem_slice rWork (by decide) 6 (by decide)
      ((QRegister.image_compose_subset rW38 _) ((QRegister.mem_image rP _).mpr ⟨w, hEq.symm⟩))
  dGenBoolWrap false false false v (rCosetB0 hm rCore 0) (rProjAxis rCore 0 7) (rP 0)
    (hB0_7 0) (hB0_P 0) (hp7_P 0)
    (dGenBoolWrap false false false v (rCosetB0 hm rCore 1) (rProjAxis rCore 1 7) (rP 1)
      (hB0_7 1) (hB0_P 1) (hp7_P 1)
      (dGenBoolWrap false false false v (rCosetB0 hm rCore 2) (rProjAxis rCore 2 7) (rP 2)
        (hB0_7 2) (hB0_P 2) (hp7_P 2)
        (.circuit (cSharedWf3CsCore isInv.not wf (rP 0) (rP 1) (rP 2) (hwfP 0) (hwfP 1) (hwfP 2)))))
@[local simp] lemma count_dWhStg7_3D_toff {mPayload : ℕ} (isInv : Bool) (hm : 22 ≤ mPayload)
    {Var : Type} {n : ℕ} (v : Var) (rCore : QRegister (fullSysCoreWires mPayload) n)
    (rWork : QRegister JunctionPrefixPruned220.mWork45 n) (hCW : rCore.DisjointWires rWork) :
    (dWhStg7_3D_Pos45 isInv hm v rCore rWork hCW).count .TOFF = 0 := by
  unfold dWhStg7_3D_Pos45
  simp [count_dGenBoolWrap_toff, DynamicCircuit.count]
@[local simp] lemma count_dWhStg7_3D_t {mPayload : ℕ} (isInv : Bool) (hm : 22 ≤ mPayload)
    {Var : Type} {n : ℕ} (v : Var) (rCore : QRegister (fullSysCoreWires mPayload) n)
    (rWork : QRegister JunctionPrefixPruned220.mWork45 n) (hCW : rCore.DisjointWires rWork) :
    (dWhStg7_3D_Pos45 isInv hm v rCore rWork hCW).count .T = 19 := by
  unfold dWhStg7_3D_Pos45
  simp [count_dGenBoolWrap_t, count_cSharedWf3CsCore_t, DynamicCircuit.count]
theorem dWhStg7_3D_spec_Pos45 {mPayload : ℕ} (isInv : Bool) (hm : 22 ≤ mPayload) {Var : Type}
    [Fintype Var] [DecidableEq Var] {n : ℕ} (v : Var)
    (rCore : QRegister (fullSysCoreWires mPayload) n) (rPGTwist : QRegister 48 n)
    (rWork : QRegister JunctionPrefixPruned220.mWork45 n) (hCP : rCore.DisjointWires rPGTwist)
    (hCW : rCore.DisjointWires rWork) (hPW : rPGTwist.DisjointWires rWork) : CondStageSpec
    (rCore.concat rPGTwist hCP) (rWork.slice 7 38 (by decide))
    ((rHigh rCore).image ∪ (rWork.slice 0 7 (by decide)).image)
    (JunctionPrefixPruned220.HProjFlag hm rCore rWork) (uWhStg7Cat hm isInv)
    (dWhStg7_3D_Pos45 isInv hm v rCore rWork hCW) := by
  let rAct := rCore.concat rPGTwist hCP
  let wf := rWork 6
  let rW07 := rWork.slice 0 7 (by decide)
  let rW38 := rWork.slice 7 38 (by decide)
  let S_core7 : Finset (Wire n) := rCore.image ∪ rW07.image
  apply CondStageSpec.anti_S (S₂ := S_core7)
    (Finset.union_subset_union_left (rHigh_sub_rCore rCore))
  have hCW38 : rCore.DisjointWires rW38 := (QRegExt.disjointWires_mono_right hCW)
    (QRegister.image_compose_subset rWork _)
  have hPW38 : rPGTwist.DisjointWires rW38 := (QRegExt.disjointWires_mono_right hPW)
    (QRegister.image_compose_subset rWork _)
  have hActW38 : rAct.DisjointWires rW38 := QRegExt.disjointWires_concat_left hCW38 hPW38
  have hwf_S : wf ∈ S_core7 := Finset.mem_union_right _ (reg_mem_slice rWork (by decide) 6 (by
    decide) (by decide))
  unfold dWhStg7_3D_Pos45 uWhStg7Cat
  let rP := rW38.slice 0 3 (by decide)
  let rW35 := rW38.slice 3 35 (by decide)
  have hCW_P : rCore.DisjointWires rP := (QRegExt.disjointWires_mono_right hCW38)
    (QRegister.image_compose_subset rW38 _)
  have hwfP : ∀ w : Fin 3, wf ≠ rP w := fun w hEq ↦
    reg_not_mem_slice rWork (by decide) 6 (by decide)
      ((QRegister.image_compose_subset rW38 _) ((QRegister.mem_image rP _).mpr ⟨w, hEq.symm⟩))
  let H3 : BitAssignment n → Prop := fun η ↦
    ((JunctionPrefixPruned220.HProjFlag hm rCore rWork η ∧
        η (rP 0) = genBoolBit false false false (η (rCosetB0 hm rCore 0)) (η (rProjAxis rCore 0 7)))
          ∧
      η (rP 1) = genBoolBit false false false (η (rCosetB0 hm rCore 1)) (η (rProjAxis rCore 1 7))) ∧
    η (rP 2) = genBoolBit false false false (η (rCosetB0 hm rCore 2)) (η (rProjAxis rCore 2 7))
  have hsCore : CondStageSpec rAct rW35 (S_core7 ∪ rP.image) H3 ((rCoreBlock48
      mPayload).embedUnitary (DyadicQft64.dyadicDiagUnitary (fullSysCoreWires mPayload) 48
      (whStg7Exp hm isInv))) (.circuit (cSharedWf3CsCore isInv.not wf (rP 0) (rP 1) (rP 2)
      (hwfP 0) (hwfP 1) (hwfP 2)) : DynamicCircuit Var n) := by
    refine CondStageSpec.of_diag_circuit rCore rPGTwist hCP rW35 (S_core7 ∪ rP.image) H3 _ _
      (whStg7Exp hm isInv) (cSharedWf3CsCore_evolve isInv.not wf _ _ _ _ _ _)
      (fun η _ ⟨⟨⟨hHp, hp0⟩, hp1⟩, hp2⟩ ↦ ?_)
    have hmul : ∀ w : Fin 3, η (rP w) = η (rCosetB0 hm rCore w) * η (rProjAxis rCore w 7) →
        ((η (rP w)).val : ℤ) = ((η (rCosetB0 hm rCore w)).val : ℤ) * ((η (rProjAxis rCore w
          7)).val : ℤ) :=
      fun w hw ↦ by rw [hw]; exact zmod2_mul_val_int _ _
    have hsgn_not : (if isInv.not then (-1 : ℤ) else 1) = -(if isInv then (-1 : ℤ) else 1) := by
      cases isInv <;> rfl
    rw [hsgn_not, JunctionPrefixPruned220.wfBitVal_of_HProjFlag hm rCore rWork hHp,
      hmul 0 (by simpa [genBoolBit] using hp0),
      hmul 1 (by simpa [genBoolBit] using hp1),
      hmul 2 (by simpa [genBoolBit] using hp2)]
    unfold whStg7Exp
    dsimp only
    rw [Fin.sum_univ_three]
    have hrB : ∀ w : Fin 3, (fun q ↦ η (rCore q)) (rCosetB0 hm (QRegExt.idReg _) w) = η
        (rCosetB0 hm rCore w) := fun _ ↦ rfl
    have hrP : ∀ w : Fin 3, (fun q ↦ η (rCore q)) (rProjAxis (QRegExt.idReg _) w 7) = η
        (rProjAxis rCore w 7) := fun _ ↦ rfl
    simp only [hrB, hrP]; ring
  let rW36 := rW38.slice 2 36 (by decide)
  let rW37 := rW38.slice 1 37 (by decide)
  have hHp_notP : ∀ (w : Fin 3) (ξ₁ ξ₂ : BitAssignment n),
      (∀ u, u ≠ rP w → ξ₁ u = ξ₂ u) → JunctionPrefixPruned220.HProjFlag hm rCore rWork ξ₁ →
        JunctionPrefixPruned220.HProjFlag hm rCore rWork ξ₂ := by
    intro w ξ₁ ξ₂ hOut h1
    refine (JunctionPrefixPruned220.HProjFlag_congr_S hm rCore rWork
      (Finset.Subset.trans (rHigh_sub_rCore rCore) Finset.subset_union_left) hwf_S ξ₁ ξ₂ fun u hu ↦
        hOut u fun hEq ↦ ?_).mp h1
    subst hEq
    rcases Finset.mem_union.mp hu with hC | h07
    · exact (disj_symm hCW_P).apply_not_mem_right w hC
    · exact Finset.disjoint_left.mp
        (QRegExt.disjointWires_to_finset (slice_disjoint_of_le rWork 0 7 7 38 (by decide) (by
          decide) (by decide)))
        h07 ((QRegister.image_compose_subset rW38 _) ((QRegister.mem_image rP _).mpr ⟨w, rfl⟩))
  have hs2 := CondStageSpec.dGenBoolWrap false false false v
    (rCosetB0 hm rCore 2) (rProjAxis rCore 2 7) (rP 2)
    (disj_wire_ne (rCosetB0_disj_rProjAxis hm rCore 2) 2 7)
    (disj_wire_ne ((QRegExt.disjointWires_mono_left hCW_P) (rCosetB0_sub_rCore hm rCore)) 2 2)
    (disj_wire_ne ((QRegExt.disjointWires_mono_left hCW_P) (rProjAxis_sub_rCore rCore 2)) 7 2)
    rW35 rW36
    (slice_sub_slice rW38 (by decide) (by decide) (by decide) (by decide))
    (reg_mem_slice rW38 (by decide) 2 (by decide) (by decide))
    ((QRegExt.disjointWires_mono_right ((QRegExt.disjointWires_mono_left hCW38) (rCosetB0_sub_rCore
      hm rCore))) (QRegister.image_compose_subset rW38 _) |>.apply_not_mem_right 2)
    ((QRegExt.disjointWires_mono_right ((QRegExt.disjointWires_mono_left hCW38) (rProjAxis_sub_rCore
      rCore 2))) (QRegister.image_compose_subset rW38 _) |>.apply_not_mem_right 7)
    (reg_not_mem_slice rW38 (by decide) 2 (by decide))
    ((disj_symm ((QRegExt.disjointWires_mono_right hActW38) (QRegister.image_compose_subset rW38
      _))).apply_not_mem_right 2)
    (Finset.mem_union_left _ (Finset.mem_union_left _ (rCosetB0_sub_rCore hm rCore
      ((QRegister.mem_image _ _).mpr ⟨2, rfl⟩))))
    (Finset.mem_union_left _ (Finset.mem_union_left _ (rProjAxis_sub_rCore rCore 2
      ((QRegister.mem_image _ _).mpr ⟨7, rfl⟩))))
    (by
      intro u hu
      rcases Finset.mem_union.mp hu with hS | h36
      · exact Finset.mem_union_left _ (Finset.union_subset_union_right (slice_sub_slice rW38 (by
          decide) (by decide) (by decide) (by decide)) hS)
      · rcases (QRegister.mem_image rW36 u).mp h36 with ⟨k, rfl⟩
        rw [slice_apply_eq]
        by_cases hk0 : k.val = 0
        · exact Finset.mem_union_left _ (Finset.mem_union_right _ (by
            have : (⟨2 + k.val, by have := k.isLt; omega⟩ : Fin 38) = 2 := Fin.ext (by dsimp; omega)
            rw [this]; exact reg_mem_slice rW38 (by decide) 2 (by decide) (by decide)))
        · exact Finset.mem_union_right _ (reg_mem_slice rW38 (by decide) ⟨2 + k.val, by
            have := k.isLt; omega⟩
            (by dsimp; omega) (by have := k.isLt; dsimp; omega)))
    (fun ξ₁ ξ₂ hOut ⟨⟨hHp1, hp01⟩, hp11⟩ ↦ ⟨⟨hHp_notP 2 ξ₁ ξ₂ hOut hHp1, by
      rw [← hOut (rP 0) (reg_ne_of_ne rP (by decide)),
        ← hOut (rCosetB0 hm rCore 0) (disj_wire_ne ((QRegExt.disjointWires_mono_left hCW_P)
          (rCosetB0_sub_rCore hm rCore)) 0 2),
        ← hOut (rProjAxis rCore 0 7) (disj_wire_ne ((QRegExt.disjointWires_mono_left hCW_P)
          (rProjAxis_sub_rCore rCore 0)) 7 2)]
      exact hp01⟩, by
      rw [← hOut (rP 1) (reg_ne_of_ne rP (by decide)),
        ← hOut (rCosetB0 hm rCore 1) (disj_wire_ne ((QRegExt.disjointWires_mono_left hCW_P)
          (rCosetB0_sub_rCore hm rCore)) 1 2),
        ← hOut (rProjAxis rCore 1 7) (disj_wire_ne ((QRegExt.disjointWires_mono_left hCW_P)
          (rProjAxis_sub_rCore rCore 1)) 7 2)]
      exact hp11⟩)
    (S_outer := S_core7 ∪ (rW38.slice 0 2 (by decide)).image)
    hsCore
  have hs1 := CondStageSpec.dGenBoolWrap false false false v
    (rCosetB0 hm rCore 1) (rProjAxis rCore 1 7) (rP 1)
    (disj_wire_ne (rCosetB0_disj_rProjAxis hm rCore 1) 1 7)
    (disj_wire_ne ((QRegExt.disjointWires_mono_left hCW_P) (rCosetB0_sub_rCore hm rCore)) 1 1)
    (disj_wire_ne ((QRegExt.disjointWires_mono_left hCW_P) (rProjAxis_sub_rCore rCore 1)) 7 1)
    rW36 rW37
    (slice_sub_slice rW38 (by decide) (by decide) (by decide) (by decide))
    (reg_mem_slice rW38 (by decide) 1 (by decide) (by decide))
    ((QRegExt.disjointWires_mono_right ((QRegExt.disjointWires_mono_left hCW38) (rCosetB0_sub_rCore
      hm rCore))) (QRegister.image_compose_subset rW38 _) |>.apply_not_mem_right 1)
    ((QRegExt.disjointWires_mono_right ((QRegExt.disjointWires_mono_left hCW38) (rProjAxis_sub_rCore
      rCore 1))) (QRegister.image_compose_subset rW38 _) |>.apply_not_mem_right 7)
    (reg_not_mem_slice rW38 (by decide) 1 (by decide))
    ((disj_symm ((QRegExt.disjointWires_mono_right hActW38) (QRegister.image_compose_subset rW38
      _))).apply_not_mem_right 1)
    (Finset.mem_union_left _ (Finset.mem_union_left _ (rCosetB0_sub_rCore hm rCore
      ((QRegister.mem_image _ _).mpr ⟨1, rfl⟩))))
    (Finset.mem_union_left _ (Finset.mem_union_left _ (rProjAxis_sub_rCore rCore 1
      ((QRegister.mem_image _ _).mpr ⟨7, rfl⟩))))
    (by
      intro u hu
      rcases Finset.mem_union.mp hu with hS | h37
      · exact Finset.mem_union_left _ (Finset.union_subset_union_right (slice_sub_slice rW38 (by
          decide) (by decide) (by decide) (by decide)) hS)
      · rcases (QRegister.mem_image rW37 u).mp h37 with ⟨k, rfl⟩
        rw [slice_apply_eq]
        by_cases hk0 : k.val = 0
        · exact Finset.mem_union_left _ (Finset.mem_union_right _ (by
            have : (⟨1 + k.val, by have := k.isLt; omega⟩ : Fin 38) = 1 := Fin.ext (by dsimp; omega)
            rw [this]; exact reg_mem_slice rW38 (by decide) 1 (by decide) (by decide)))
        · exact Finset.mem_union_right _ (reg_mem_slice rW38 (by decide) ⟨1 + k.val, by
            have := k.isLt; omega⟩
            (by dsimp; omega) (by have := k.isLt; dsimp; omega)))
    (fun ξ₁ ξ₂ hOut ⟨hHp1, hp01⟩ ↦ ⟨hHp_notP 1 ξ₁ ξ₂ hOut hHp1, by
      rw [← hOut (rP 0) (reg_ne_of_ne rP (by decide)),
        ← hOut (rCosetB0 hm rCore 0) (disj_wire_ne ((QRegExt.disjointWires_mono_left hCW_P)
          (rCosetB0_sub_rCore hm rCore)) 0 1),
        ← hOut (rProjAxis rCore 0 7) (disj_wire_ne ((QRegExt.disjointWires_mono_left hCW_P)
          (rProjAxis_sub_rCore rCore 0)) 7 1)]
      exact hp01⟩)
    (S_outer := S_core7 ∪ (rW38.slice 0 1 (by decide)).image)
    hs2
  exact CondStageSpec.dGenBoolWrap false false false v
    (rCosetB0 hm rCore 0) (rProjAxis rCore 0 7) (rP 0)
    (disj_wire_ne (rCosetB0_disj_rProjAxis hm rCore 0) 0 7)
    (disj_wire_ne ((QRegExt.disjointWires_mono_left hCW_P) (rCosetB0_sub_rCore hm rCore)) 0 0)
    (disj_wire_ne ((QRegExt.disjointWires_mono_left hCW_P) (rProjAxis_sub_rCore rCore 0)) 7 0)
    rW37 rW38
    (QRegister.image_compose_subset rW38 _)
    ((QRegister.mem_image rW38 _).mpr ⟨0, rfl⟩)
    (((QRegExt.disjointWires_mono_left hCW38) (rCosetB0_sub_rCore hm rCore)).apply_not_mem_right 0)
    (((QRegExt.disjointWires_mono_left hCW38) (rProjAxis_sub_rCore rCore 0)).apply_not_mem_right 7)
    (reg_not_mem_slice rW38 (by decide) 0 (by decide))
    ((disj_symm hActW38).apply_not_mem_right 0)
    (Finset.mem_union_left _ (rCosetB0_sub_rCore hm rCore ((QRegister.mem_image _ _).mpr ⟨0, rfl⟩)))
    (Finset.mem_union_left _ (rProjAxis_sub_rCore rCore 0 ((QRegister.mem_image _ _).mpr ⟨7, rfl⟩)))
    (by
      intro u hu
      rcases Finset.mem_union.mp hu with hS | h38
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ hS)
      · rcases (QRegister.mem_image rW38 u).mp h38 with ⟨k, rfl⟩
        by_cases hk0 : k.val = 0
        · exact Finset.mem_union_left _ (Finset.mem_union_right _ (by
            have : k = 0 := Fin.ext hk0
            rw [this]; exact reg_mem_slice rW38 (by decide) 0 (by decide) (by decide)))
        · exact Finset.mem_union_right _ (reg_mem_slice rW38 (by decide) k (by omega) k.isLt))
    (hHp_notP 0)
    hs1
theorem whStg_k8_lt_Pos45 (k : Fin 7) : k.val < 8 := by have := k.isLt; omega
theorem whStg_scr_le_Pos45 (k : Fin 7) : 1 + (3 * (6 - k.val) + 2) ≤ 35 := by have := k.isLt; omega
theorem whStg_low_le_Pos45 (k : Fin 7) : 0 + (6 - k.val + 1) ≤ 8 := by have := k.isLt; omega
theorem whStg_top_lt_Pos45 (k : Fin 7) : 6 - k.val + 1 < 8 := by have := k.isLt; omega
theorem whStg_rT_le_Pos45 (k : Fin 7) : 45 - (6 - k.val + 1) + (6 - k.val + 1) ≤ 48 := by
  have := k.isLt; omega
/-- Internal `45`-wire Hadamard-tail-cut helper `dWhStg_3D_Pos45`. -/
noncomputable def dWhStg_3D_Pos45 {mPayload : ℕ} (isInv : Bool) (hm : 22 ≤ mPayload)
    {Var : Type} {n : ℕ} (v : Var) (k : Fin 7)
    (rCore : QRegister (fullSysCoreWires mPayload) n) (rPGTwist : QRegister 48 n)
    (rWork : QRegister JunctionPrefixPruned220.mWork45 n) (hCP : rCore.DisjointWires rPGTwist)
    (hCW : rCore.DisjointWires rWork) (hPW : rPGTwist.DisjointWires rWork) : DynamicCircuit
    Var n :=
  let wf := rWork 6
  let rW38 := rWork.slice 7 38 (by decide)
  let rQ := rW38.slice 0 3 (by decide)
  let rW35 := rW38.slice 3 35 (by decide)
  let m : ℕ := 6 - k.val
  let k8 : Fin 8 := ⟨k.val, whStg_k8_lt_Pos45 k⟩
  let wQc := rW35 0
  let rScr := rW35.slice 1 (3 * m + 2) (whStg_scr_le_Pos45 k)
  have hCW38 : rCore.DisjointWires rW38 := (QRegExt.disjointWires_mono_right hCW)
    (QRegister.image_compose_subset rWork _)
  have hPW38 : rPGTwist.DisjointWires rW38 := (QRegExt.disjointWires_mono_right hPW)
    (QRegister.image_compose_subset rWork _)
  have hCW_Q : rCore.DisjointWires rQ := (QRegExt.disjointWires_mono_right hCW38)
    (QRegister.image_compose_subset rW38 _)
  have hCW35 : rCore.DisjointWires rW35 := (QRegExt.disjointWires_mono_right hCW38)
    (QRegister.image_compose_subset rW38 _)
  have hPW35 : rPGTwist.DisjointWires rW35 := (QRegExt.disjointWires_mono_right hPW38)
    (QRegister.image_compose_subset rW38 _)
  have hQ35 : rQ.DisjointWires rW35 := slice_disjoint_of_le rW38 0 3 3 35 (by decide) (by decide)
    (by decide)
  let rPk : QRegister 3 n :=
    ⟨⟨(Matrix.vecCons (rProjAxis rCore 0 k8) (Matrix.vecCons (rProjAxis rCore 1 k8) (Matrix.vecCons
      (rProjAxis rCore 2 k8) Matrix.vecEmpty))), fun i j hij ↦ by
      fin_cases i <;> fin_cases j
      · rfl
      · exact False.elim (disj_wire_ne (rProjAxis_disjoint_of_ne rCore (by
          decide : (0 : Fin 3) ≠ 1)) k8 k8 hij)
      · exact False.elim (disj_wire_ne (rProjAxis_disjoint_of_ne rCore (by
          decide : (0 : Fin 3) ≠ 2)) k8 k8 hij)
      · exact False.elim (disj_wire_ne (rProjAxis_disjoint_of_ne rCore (by
          decide : (1 : Fin 3) ≠ 0)) k8 k8 hij)
      · rfl
      · exact False.elim (disj_wire_ne (rProjAxis_disjoint_of_ne rCore (by
          decide : (1 : Fin 3) ≠ 2)) k8 k8 hij)
      · exact False.elim (disj_wire_ne (rProjAxis_disjoint_of_ne rCore (by
          decide : (2 : Fin 3) ≠ 0)) k8 k8 hij)
      · exact False.elim (disj_wire_ne (rProjAxis_disjoint_of_ne rCore (by
          decide : (2 : Fin 3) ≠ 1)) k8 k8 hij)
      · rfl⟩⟩
  have hPk_sub : rPk.image ⊆ rCore.image := by
    intro u hu
    rcases (QRegister.mem_image rPk u).mp hu with ⟨w, rfl⟩
    fin_cases w <;> exact rProjAxis_sub_rCore rCore _ ((QRegister.mem_image _ _).mpr ⟨k8, rfl⟩)
  have hwf_Pk : ∀ w : Fin 3, wf ≠ rPk w :=
    fun w ↦ (disj_wire_ne ((QRegExt.disjointWires_mono_left hCW) hPk_sub) w 6).symm
  have hwf_Q : ∀ w : Fin 3, wf ≠ rQ w := fun w hEq ↦
    reg_not_mem_slice rWork (by decide) 6 (by decide)
      ((QRegister.image_compose_subset rW38 _) ((QRegister.mem_image rQ _).mpr ⟨w, hEq.symm⟩))
  have hPk_Q : rPk.DisjointWires rQ := (QRegExt.disjointWires_mono_left hCW_Q) hPk_sub
  let low : Fin 3 → QRegister (m + 1) n :=
    fun w ↦ (rWhFull hm rCore w).slice 0 (m + 1) (whStg_low_le_Pos45 k)
  let top : Fin 3 → Wire n := fun w ↦ rWhFull hm rCore w ⟨m + 1, whStg_top_lt_Pos45 k⟩
  let rT : QRegister (m + 1) n := rPGTwist.slice (45 - (m + 1)) (m + 1) (whStg_rT_le_Pos45 k)
  have hLow_sub : ∀ w : Fin 3, (low w).image ⊆ rCore.image := fun w ↦
    Finset.Subset.trans (QRegister.image_compose_subset _ _) (rWhFull_sub_rCore hm rCore w)
  have hq_top : ∀ w : Fin 3, rQ w ≠ top w := fun w ↦
    (disj_wire_ne ((QRegExt.disjointWires_mono_left hCW_Q) (rWhFull_sub_rCore hm rCore w)) ⟨m + 1,
      _⟩ w).symm
  have hq_low : ∀ (w : Fin 3) (i : Fin (m + 1)), rQ w ≠ low w i := fun w i ↦
    (disj_wire_ne ((QRegExt.disjointWires_mono_left hCW_Q) (hLow_sub w)) i w).symm
  let cTop : Circuit n :=
    cWhTopAxis isInv (rQ 0) (top 0) (hq_top 0) ;;ᶜ
      cWhTopAxis isInv (rQ 1) (top 1) (hq_top 1) ;;ᶜ
      cWhTopAxis isInv (rQ 2) (top 2) (hq_top 2)
  let cFlip3 : Circuit n :=
    cnotAllCircuit (rQ 0) (low 0) (hq_low 0) ;;ᶜ
      (cnotAllCircuit (rQ 1) (low 1) (hq_low 1) ;;ᶜ
        cnotAllCircuit (rQ 2) (low 2) (hq_low 2))
  have h01 : (low 0).DisjointWires (low 1) :=
    (QRegExt.disjointWires_mono_right ((QRegExt.disjointWires_mono_left (rWhFull_disjoint_of_ne hm
      rCore (by decide : (0 : Fin 3) ≠ 1)))
      (QRegister.image_compose_subset _ _))) (QRegister.image_compose_subset _ _)
  have h02 : (low 0).DisjointWires (low 2) :=
    (QRegExt.disjointWires_mono_right ((QRegExt.disjointWires_mono_left (rWhFull_disjoint_of_ne hm
      rCore (by decide : (0 : Fin 3) ≠ 2)))
      (QRegister.image_compose_subset _ _))) (QRegister.image_compose_subset _ _)
  have h12 : (low 1).DisjointWires (low 2) :=
    (QRegExt.disjointWires_mono_right ((QRegExt.disjointWires_mono_left (rWhFull_disjoint_of_ne hm
      rCore (by decide : (1 : Fin 3) ≠ 2)))
      (QRegister.image_compose_subset _ _))) (QRegister.image_compose_subset _ _)
  have h1Q : (low 1).DisjointWires rQ := (QRegExt.disjointWires_mono_left hCW_Q) (hLow_sub 1)
  have h1Qc : wQc ∉ (low 1).image := (disj_symm ((QRegExt.disjointWires_mono_left hCW35) (hLow_sub
    1))).apply_not_mem_right 0
  have hQQc : wQc ∉ rQ.image := (disj_symm hQ35).apply_not_mem_right 0
  have h1T : (low 1).DisjointWires rT :=
    (QRegExt.disjointWires_mono_right ((QRegExt.disjointWires_mono_left hCP) (hLow_sub 1)))
      (QRegister.image_compose_subset rPGTwist _)
  have hQT : rQ.DisjointWires rT :=
    (QRegExt.disjointWires_mono_right ((QRegExt.disjointWires_mono_left (disj_symm hPW38))
      (QRegister.image_compose_subset rW38 _)))
      (QRegister.image_compose_subset rPGTwist _)
  have hScr_sub35 : rScr.image ⊆ rW35.image := QRegister.image_compose_subset rW35 _
  have h0S : (low 0).DisjointWires rScr := (QRegExt.disjointWires_mono_right
    ((QRegExt.disjointWires_mono_left hCW35) (hLow_sub 0))) hScr_sub35
  have h1S : (low 1).DisjointWires rScr := (QRegExt.disjointWires_mono_right
    ((QRegExt.disjointWires_mono_left hCW35) (hLow_sub 1))) hScr_sub35
  have h2S : (low 2).DisjointWires rScr := (QRegExt.disjointWires_mono_right
    ((QRegExt.disjointWires_mono_left hCW35) (hLow_sub 2))) hScr_sub35
  have hQS : rQ.DisjointWires rScr := (QRegExt.disjointWires_mono_right hQ35) hScr_sub35
  have hQcS : wQc ∉ rScr.image := reg_not_mem_slice rW35 _ 0 (Or.inl (by decide))
  have hTS : rT.DisjointWires rScr :=
    (QRegExt.disjointWires_mono_right ((QRegExt.disjointWires_mono_left hPW35)
      (QRegister.image_compose_subset rPGTwist _))) hScr_sub35
  let dCsa := dCsa3AxisApexWithQ isInv.not m v (low 0) (low 1) (low 2) rQ wQc rT rScr
    h01 h02 h12 h1Q h1Qc hQQc h1T hQT h0S h1S h2S hQS hQcS hTS
  dMaskRegWrap 3 v wf rPk rQ hwf_Pk hwf_Q hPk_Q (.seq (.circuit cTop) (dPureConj cFlip3 dCsa))
@[local simp] lemma count_dWhStg_3D_toff {mPayload : ℕ} (isInv : Bool) (hm : 22 ≤ mPayload)
    {Var : Type} {n : ℕ} (v : Var) (k : Fin 7)
    (rCore : QRegister (fullSysCoreWires mPayload) n) (rPGTwist : QRegister 48 n)
    (rWork : QRegister JunctionPrefixPruned220.mWork45 n) (hCP : rCore.DisjointWires rPGTwist)
    (hCW : rCore.DisjointWires rWork) (hPW : rPGTwist.DisjointWires rWork) : (dWhStg_3D_Pos45
    isInv hm v k rCore rPGTwist rWork hCP hCW hPW).count .TOFF = 0 := by
  unfold dWhStg_3D_Pos45
  dsimp only
  rw [count_dMaskRegWrap_toff, count_dyn_seq,
    count_dPureConj_toff _ (by simp [Circuit.count_seq, count_cnotAllCircuit_toff]),
    count_dCsa3AxisApexWithQ_toff]
  cases isInv <;> rfl
@[local simp] lemma count_dWhStg_3D_t {mPayload : ℕ} (isInv : Bool) (hm : 22 ≤ mPayload)
    {Var : Type} {n : ℕ} (v : Var) (k : Fin 7)
    (rCore : QRegister (fullSysCoreWires mPayload) n) (rPGTwist : QRegister 48 n)
    (rWork : QRegister JunctionPrefixPruned220.mWork45 n) (hCP : rCore.DisjointWires rPGTwist)
    (hCW : rCore.DisjointWires rWork) (hPW : rPGTwist.DisjointWires rWork) : (dWhStg_3D_Pos45
    isInv hm v k rCore rPGTwist rWork hCP hCW hPW).count .T = 12 * (7 - k.val) + 18 := by
  unfold dWhStg_3D_Pos45
  dsimp only
  rw [count_dMaskRegWrap_t, count_dyn_seq,
    count_dPureConj_t _ (by simp [Circuit.count_seq, count_cnotAllCircuit_t]),
    count_dCsa3AxisApexWithQ_t]
  have hcTop : ∀ (q0 t0 q1 t1 q2 t2 : Wire n) h0 h1 h2,
      (DynamicCircuit.circuit
        (cWhTopAxis isInv q0 t0 h0 ;;ᶜ cWhTopAxis isInv q1 t1 h1 ;;ᶜ cWhTopAxis isInv q2 t2 h2) :
        DynamicCircuit Var n).count .T = 3 := by
    intros; cases isInv <;> rfl
  rw [hcTop]
  have := k.isLt
  omega
theorem dWhStg_3D_spec_Pos45 {mPayload : ℕ} (isInv : Bool) (hm : 22 ≤ mPayload) {Var : Type}
    [Fintype Var] [DecidableEq Var] {n : ℕ} (v : Var) (k : Fin 7)
    (rCore : QRegister (fullSysCoreWires mPayload) n) (rPGTwist : QRegister 48 n)
    (rWork : QRegister JunctionPrefixPruned220.mWork45 n) (hCP : rCore.DisjointWires rPGTwist)
    (hCW : rCore.DisjointWires rWork) (hPW : rPGTwist.DisjointWires rWork) : CondStageSpec
    (rCore.concat rPGTwist hCP) (rWork.slice 7 38 (by decide))
    ((rHigh rCore).image ∪ (rWork.slice 0 7 (by decide)).image)
    (JunctionPrefixPruned220.HProjFlag hm rCore rWork) (uWhStgCat hm k isInv)
    (dWhStg_3D_Pos45 isInv hm v k rCore rPGTwist rWork hCP hCW hPW) := by
  let rAct := rCore.concat rPGTwist hCP
  let wf := rWork 6
  let rW07 := rWork.slice 0 7 (by decide)
  let rW38 := rWork.slice 7 38 (by decide)
  let rQ := rW38.slice 0 3 (by decide)
  let rW35 := rW38.slice 3 35 (by decide)
  let S_core7 : Finset (Wire n) := rCore.image ∪ rW07.image
  apply CondStageSpec.anti_S (S₂ := S_core7)
    (Finset.union_subset_union_left (rHigh_sub_rCore rCore))
  let m : ℕ := 6 - k.val
  have hm1_eq : m + 1 = 7 - k.val := by have := k.isLt; dsimp [m]; omega
  let k8 : Fin 8 := ⟨k.val, whStg_k8_lt_Pos45 k⟩
  let wQc := rW35 0
  let rScr := rW35.slice 1 (3 * m + 2) (whStg_scr_le_Pos45 k)
  have hCW38 : rCore.DisjointWires rW38 := (QRegExt.disjointWires_mono_right hCW)
    (QRegister.image_compose_subset rWork _)
  have hPW38 : rPGTwist.DisjointWires rW38 := (QRegExt.disjointWires_mono_right hPW)
    (QRegister.image_compose_subset rWork _)
  have hActW38 : rAct.DisjointWires rW38 := QRegExt.disjointWires_concat_left hCW38 hPW38
  have hActW35 : rAct.DisjointWires rW35 := (QRegExt.disjointWires_mono_right hActW38)
    (QRegister.image_compose_subset rW38 _)
  have hCW_Q : rCore.DisjointWires rQ := (QRegExt.disjointWires_mono_right hCW38)
    (QRegister.image_compose_subset rW38 _)
  have hCW35 : rCore.DisjointWires rW35 := (QRegExt.disjointWires_mono_right hCW38)
    (QRegister.image_compose_subset rW38 _)
  have hPW35 : rPGTwist.DisjointWires rW35 := (QRegExt.disjointWires_mono_right hPW38)
    (QRegister.image_compose_subset rW38 _)
  have hQ35 : rQ.DisjointWires rW35 := slice_disjoint_of_le rW38 0 3 3 35 (by decide) (by decide)
    (by decide)
  have hwf_S : wf ∈ S_core7 := Finset.mem_union_right _ (reg_mem_slice rWork (by decide) 6 (by
    decide) (by decide))
  have hwf_not35 : wf ∉ rW35.image := fun hm' ↦
    reg_not_mem_slice rWork (by decide) 6 (by decide) ((QRegister.image_compose_subset rW38 _) hm')
  let rPk : QRegister 3 n :=
    ⟨⟨(Matrix.vecCons (rProjAxis rCore 0 k8) (Matrix.vecCons (rProjAxis rCore 1 k8) (Matrix.vecCons
      (rProjAxis rCore 2 k8) Matrix.vecEmpty))), fun i j hij ↦ by
      fin_cases i <;> fin_cases j
      · rfl
      · exact False.elim (disj_wire_ne (rProjAxis_disjoint_of_ne rCore (by
          decide : (0 : Fin 3) ≠ 1)) k8 k8 hij)
      · exact False.elim (disj_wire_ne (rProjAxis_disjoint_of_ne rCore (by
          decide : (0 : Fin 3) ≠ 2)) k8 k8 hij)
      · exact False.elim (disj_wire_ne (rProjAxis_disjoint_of_ne rCore (by
          decide : (1 : Fin 3) ≠ 0)) k8 k8 hij)
      · rfl
      · exact False.elim (disj_wire_ne (rProjAxis_disjoint_of_ne rCore (by
          decide : (1 : Fin 3) ≠ 2)) k8 k8 hij)
      · exact False.elim (disj_wire_ne (rProjAxis_disjoint_of_ne rCore (by
          decide : (2 : Fin 3) ≠ 0)) k8 k8 hij)
      · exact False.elim (disj_wire_ne (rProjAxis_disjoint_of_ne rCore (by
          decide : (2 : Fin 3) ≠ 1)) k8 k8 hij)
      · rfl⟩⟩
  have hPk_sub : rPk.image ⊆ rCore.image := by
    intro u hu
    rcases (QRegister.mem_image rPk u).mp hu with ⟨w, rfl⟩
    fin_cases w <;> exact rProjAxis_sub_rCore rCore _ ((QRegister.mem_image _ _).mpr ⟨k8, rfl⟩)
  let H_q : BitAssignment n → Prop := fun η ↦
    JunctionPrefixPruned220.HProjFlag hm rCore rWork η ∧ ∀ w : Fin 3, η (rQ w) = η wf * η (rPk w)
  have hHq_congr : ∀ ξ₁ ξ₂, (∀ u ∈ S_core7 ∪ rQ.image, ξ₁ u = ξ₂ u) → (H_q ξ₁ ↔ H_q ξ₂) := by
    intro ξ₁ ξ₂ hEq
    have h1 := JunctionPrefixPruned220.HProjFlag_congr_S hm rCore rWork
      (Finset.Subset.trans (rHigh_sub_rCore rCore) (Finset.Subset.trans Finset.subset_union_left
        Finset.subset_union_left))
      (Finset.mem_union_left _ hwf_S) ξ₁ ξ₂ hEq
    refine and_congr h1 (forall_congr' fun w ↦ ?_)
    rw [hEq (rQ w) (Finset.mem_union_right _ ((QRegister.mem_image rQ _).mpr ⟨w, rfl⟩)),
      hEq wf (Finset.mem_union_left _ hwf_S),
      hEq (rPk w) (Finset.mem_union_left _ (Finset.mem_union_left _
        (hPk_sub ((QRegister.mem_image rPk _).mpr ⟨w, rfl⟩))))]
  have hq_val : ∀ (η : BitAssignment n) (w : Fin 3), H_q η → ((η (rQ w)).val : ℤ) = wfBitVal
      hm (fun q ↦ η (rCore q)) * (((fun q ↦ η (rCore q)) (rProjAxis (QRegExt.idReg _) w
      k8)).val : ℤ) := by
    intro η w ⟨hHp, hQEq⟩
    rw [hQEq w, zmod2_mul_val_int, JunctionPrefixPruned220.wfBitVal_of_HProjFlag hm rCore rWork hHp]
    fin_cases w <;> rfl
  let low : Fin 3 → QRegister (m + 1) n :=
    fun w ↦ (rWhFull hm rCore w).slice 0 (m + 1) (whStg_low_le_Pos45 k)
  let top : Fin 3 → Wire n := fun w ↦ rWhFull hm rCore w ⟨m + 1, whStg_top_lt_Pos45 k⟩
  let rT : QRegister (m + 1) n := rPGTwist.slice (45 - (m + 1)) (m + 1) (whStg_rT_le_Pos45 k)
  have hLow_sub : ∀ w : Fin 3, (low w).image ⊆ rCore.image := fun w ↦
    Finset.Subset.trans (QRegister.image_compose_subset _ _) (rWhFull_sub_rCore hm rCore w)
  have hq_top : ∀ w : Fin 3, rQ w ≠ top w := fun w ↦
    (disj_wire_ne ((QRegExt.disjointWires_mono_left hCW_Q) (rWhFull_sub_rCore hm rCore w)) ⟨m + 1,
      _⟩ w).symm
  have hq_low : ∀ (w : Fin 3) (i : Fin (m + 1)), rQ w ≠ low w i := fun w i ↦
    (disj_wire_ne ((QRegExt.disjointWires_mono_left hCW_Q) (hLow_sub w)) i w).symm
  let cTop : Circuit n :=
    cWhTopAxis isInv (rQ 0) (top 0) (hq_top 0) ;;ᶜ
      cWhTopAxis isInv (rQ 1) (top 1) (hq_top 1) ;;ᶜ
      cWhTopAxis isInv (rQ 2) (top 2) (hq_top 2)
  have hsTop : CondStageSpec rAct rW35 (S_core7 ∪ rQ.image) H_q ((rCoreBlock48
      mPayload).embedUnitary (DyadicQft64.dyadicDiagUnitary (fullSysCoreWires mPayload) 48
      (whStgTopExp hm k isInv))) (.circuit cTop : DynamicCircuit Var n) := by
    refine CondStageSpec.of_diag_circuit rCore rPGTwist hCP rW35 (S_core7 ∪ rQ.image) H_q cTop
      (fun η ↦ (if isInv then (-1 : ℤ) else 1) * (2 ^ 45 : ℤ) * ∑ w : Fin 3, ((2 * ((η (rQ
      w)).val : ℤ) - 1) * ((η (top w)).val : ℤ) + ((η (rQ w)).val : ℤ)))
      (whStgTopExp hm k isInv) (fun η ↦ ?_) (fun η _ hHq ↦ ?_)
    · dsimp only [cTop]
      simp only [Circuit.eval_seq, Submonoid.coe_mul, ← Matrix.mulVec_mulVec,
        cWhTopAxis_evolve, Matrix.mulVec_smul, smul_smul, DyadicQft64.dyadicTurn_add]
      refine congrArg (fun x ↦ DyadicQft64.dyadicTurn 48 x • basisKet η) ?_
      rw [Fin.sum_univ_three]
      ring
    · rw [Fin.sum_univ_three, hq_val η 0 hHq, hq_val η 1 hHq, hq_val η 2 hHq]
      unfold whStgTopExp
      dsimp only
      rw [Fin.sum_univ_three]
      have hTopEq : ∀ w : Fin 3,
          η (top w) =
            (fun q ↦ η (rCore q)) (rWhFull hm (QRegExt.idReg _) w ⟨7 - k.val, by
              have := k.isLt; omega⟩) := by
        intro w
        dsimp only [top]
        rw [← rWhFull_idReg_apply hm rCore w ⟨m + 1, _⟩]
        exact congrArg (fun idx ↦ η (rCore (rWhFull hm (QRegExt.idReg _) w idx))) (Fin.ext hm1_eq)
      rw [hTopEq 0, hTopEq 1, hTopEq 2]
  let cFlip3 : Circuit n :=
    cnotAllCircuit (rQ 0) (low 0) (hq_low 0) ;;ᶜ
      (cnotAllCircuit (rQ 1) (low 1) (hq_low 1) ;;ᶜ
        cnotAllCircuit (rQ 2) (low 2) (hq_low 2))
  have h01 : (low 0).DisjointWires (low 1) :=
    (QRegExt.disjointWires_mono_right ((QRegExt.disjointWires_mono_left (rWhFull_disjoint_of_ne hm
      rCore (by decide : (0 : Fin 3) ≠ 1)))
      (QRegister.image_compose_subset _ _))) (QRegister.image_compose_subset _ _)
  have h02 : (low 0).DisjointWires (low 2) :=
    (QRegExt.disjointWires_mono_right ((QRegExt.disjointWires_mono_left (rWhFull_disjoint_of_ne hm
      rCore (by decide : (0 : Fin 3) ≠ 2)))
      (QRegister.image_compose_subset _ _))) (QRegister.image_compose_subset _ _)
  have h12 : (low 1).DisjointWires (low 2) :=
    (QRegExt.disjointWires_mono_right ((QRegExt.disjointWires_mono_left (rWhFull_disjoint_of_ne hm
      rCore (by decide : (1 : Fin 3) ≠ 2)))
      (QRegister.image_compose_subset _ _))) (QRegister.image_compose_subset _ _)
  have h0Q : (low 0).DisjointWires rQ := (QRegExt.disjointWires_mono_left hCW_Q) (hLow_sub 0)
  have h1Q : (low 1).DisjointWires rQ := (QRegExt.disjointWires_mono_left hCW_Q) (hLow_sub 1)
  have h2Q : (low 2).DisjointWires rQ := (QRegExt.disjointWires_mono_left hCW_Q) (hLow_sub 2)
  have h0Qc : wQc ∉ (low 0).image := (disj_symm ((QRegExt.disjointWires_mono_left hCW35) (hLow_sub
    0))).apply_not_mem_right 0
  have h1Qc : wQc ∉ (low 1).image := (disj_symm ((QRegExt.disjointWires_mono_left hCW35) (hLow_sub
    1))).apply_not_mem_right 0
  have h2Qc : wQc ∉ (low 2).image := (disj_symm ((QRegExt.disjointWires_mono_left hCW35) (hLow_sub
    2))).apply_not_mem_right 0
  have hQQc : wQc ∉ rQ.image := (disj_symm hQ35).apply_not_mem_right 0
  have hT_subP : rT.image ⊆ rPGTwist.image := QRegister.image_compose_subset rPGTwist _
  have h0T : (low 0).DisjointWires rT := (QRegExt.disjointWires_mono_right
    ((QRegExt.disjointWires_mono_left hCP) (hLow_sub 0))) hT_subP
  have h1T : (low 1).DisjointWires rT := (QRegExt.disjointWires_mono_right
    ((QRegExt.disjointWires_mono_left hCP) (hLow_sub 1))) hT_subP
  have h2T : (low 2).DisjointWires rT := (QRegExt.disjointWires_mono_right
    ((QRegExt.disjointWires_mono_left hCP) (hLow_sub 2))) hT_subP
  have hQT : rQ.DisjointWires rT :=
    (QRegExt.disjointWires_mono_right ((QRegExt.disjointWires_mono_left (disj_symm hPW38))
      (QRegister.image_compose_subset rW38 _))) hT_subP
  have hQcT : wQc ∉ rT.image := ((QRegExt.disjointWires_mono_right (disj_symm hPW35))
    hT_subP).apply_not_mem_right 0
  have hScr_sub35 : rScr.image ⊆ rW35.image := QRegister.image_compose_subset rW35 _
  have h0S : (low 0).DisjointWires rScr := (QRegExt.disjointWires_mono_right
    ((QRegExt.disjointWires_mono_left hCW35) (hLow_sub 0))) hScr_sub35
  have h1S : (low 1).DisjointWires rScr := (QRegExt.disjointWires_mono_right
    ((QRegExt.disjointWires_mono_left hCW35) (hLow_sub 1))) hScr_sub35
  have h2S : (low 2).DisjointWires rScr := (QRegExt.disjointWires_mono_right
    ((QRegExt.disjointWires_mono_left hCW35) (hLow_sub 2))) hScr_sub35
  have hQS : rQ.DisjointWires rScr := (QRegExt.disjointWires_mono_right hQ35) hScr_sub35
  have hQcS : wQc ∉ rScr.image := reg_not_mem_slice rW35 _ 0 (Or.inl (by decide))
  have hTS : rT.DisjointWires rScr := (QRegExt.disjointWires_mono_right
    ((QRegExt.disjointWires_mono_left hPW35) hT_subP)) hScr_sub35
  obtain ⟨uCsa, hwCsa, hDiagCsa, hKetCsa⟩ :=
    dCsa3AxisApexWithQ_spec isInv.not m v (low 0) (low 1) (low 2) rQ wQc rT rScr
      h01 h02 h12 h0Q h1Q h2Q h0Qc h1Qc h2Qc hQQc h0T h1T h2T hQT hQcT h0S h1S h2S hQS hQcS hTS
  have hQcScr : (QRegister.singleton wQc).DisjointWires rScr := by
    refine QRegExt.disjointWires_of_finset ?_
    rw [qreg_singleton_image, Finset.disjoint_singleton_left]
    exact hQcS
  let rTot := (QRegister.singleton wQc).concat rScr hQcScr
  have hTotSubW35 : rTot.image ⊆ rW35.image := by
    rw [qreg_image_concat, qreg_singleton_image]
    refine Finset.union_subset ?_ hScr_sub35
    rw [Finset.singleton_subset_iff]
    exact (QRegister.mem_image rW35 _).mpr ⟨0, rfl⟩
  have hFlipSub : cFlip3.support ⊆ rCore.image ∪ rQ.image := by
    have hSubW : ∀ w : Fin 3,
        (cnotAllCircuit (rQ w) (low w) (hq_low w)).support ⊆ rCore.image ∪ rQ.image := by
      intro w
      refine Finset.Subset.trans (support_cnotAllCircuit_sub (rQ w) (low w) (hq_low w)) ?_
      rw [Finset.insert_subset_iff]
      exact ⟨Finset.mem_union_right _ ((QRegister.mem_image rQ _).mpr ⟨w, rfl⟩),
        Finset.Subset.trans (hLow_sub w) Finset.subset_union_left⟩
    exact JunctionApexCSA288.support_seq_sub (hSubW 0) (JunctionApexCSA288.support_seq_sub (hSubW 1)
      (hSubW 2))
  have hDisjFlipTot : Disjoint cFlip3.support rTot.image := Finset.disjoint_of_subset_left
      hFlipSub (Finset.disjoint_of_subset_right hTotSubW35 (Finset.disjoint_union_left.mpr
      ⟨(QRegExt.disjointWires_to_finset hCW35), (QRegExt.disjointWires_to_finset hQ35)⟩))
  have hwLow : CleanUnitaryWp rW35 (cFlip3.inverse.eval * uCsa * cFlip3.eval)
      (dPureConj cFlip3 (dCsa3AxisApexWithQ isInv.not m v (low 0) (low 1) (low 2) rQ wQc rT rScr
        h01 h02 h12 h1Q h1Qc hQQc h1T hQT h0S h1S h2S hQS hQcS hTS)) :=
    (CleanUnitaryWp.dPureConj cFlip3 rTot hDisjFlipTot hwCsa).mono_workspace hTotSubW35
  let S_diag : Finset (Wire n) := (S_core7 ∪ rQ.image) ∪ rW35.image
  have hSubDiag : S_diag ⊆ Finset.univ \ rT.image := by
    intro u hu
    rw [Finset.mem_sdiff]
    refine ⟨Finset.mem_univ u, fun huT ↦ ?_⟩
    have huP : u ∈ rPGTwist.image := hT_subP huT
    rcases Finset.mem_union.mp hu with hSQ | h35
    · rcases Finset.mem_union.mp hSQ with hS7 | hQ'
      · rcases Finset.mem_union.mp hS7 with hC | h07
        · exact Finset.disjoint_left.mp (QRegExt.disjointWires_to_finset hCP) hC huP
        · exact Finset.disjoint_left.mp (QRegExt.disjointWires_to_finset hPW) huP
            ((QRegister.image_compose_subset rWork _) h07)
      · exact Finset.disjoint_left.mp (QRegExt.disjointWires_to_finset hPW38) huP
          ((QRegister.image_compose_subset rW38 _) hQ')
    · exact Finset.disjoint_left.mp (QRegExt.disjointWires_to_finset hPW35) huP h35
  have hDiagLow : DiagOn S_diag (cFlip3.inverse.eval * uCsa * cFlip3.eval).1 := by
    have hEqMat : (cFlip3.inverse.eval * uCsa * cFlip3.eval).1 =
        (cnotAllCircuit (rQ 0) (low 0) (hq_low 0)).inverse.eval.1 * ((cnotAllCircuit (rQ 1)
        (low 1) (hq_low 1)).inverse.eval.1 * ((cnotAllCircuit (rQ 2) (low 2) (hq_low
        2)).inverse.eval.1 * uCsa.1 * (cnotAllCircuit (rQ 2) (low 2) (hq_low 2)).eval.1) *
        (cnotAllCircuit (rQ 1) (low 1) (hq_low 1)).eval.1) *
        (cnotAllCircuit (rQ 0) (low 0) (hq_low 0)).eval.1 := by
      simp only [cFlip3, Circuit.inverse_seq, Circuit.eval_seq, Submonoid.coe_mul, Matrix.mul_assoc]
    rw [hEqMat]
    have hqMem : ∀ w : Fin 3, rQ w ∈ S_diag := fun w ↦
      Finset.mem_union_left _ (Finset.mem_union_right _ ((QRegister.mem_image rQ _).mpr ⟨w, rfl⟩))
    exact DiagOn.conj_cnotAllCircuit_of_mem (rQ 0) (low 0) (hq_low 0) (hqMem 0)
      (DiagOn.conj_cnotAllCircuit_of_mem (rQ 1) (low 1) (hq_low 1) (hqMem 1)
        (DiagOn.conj_cnotAllCircuit_of_mem (rQ 2) (low 2) (hq_low 2) (hqMem 2)
          (DiagOn.anti hSubDiag hDiagCsa)))
  have hsLow_m : CondStageSpec rAct rW35 (S_core7 ∪ rQ.image) H_q
      (uApexShift45 (fullSysCoreWires mPayload) (m + 1)
        (by have := k.isLt; dsimp [m]; omega) (whStgLowShift hm k isInv))
      (dPureConj cFlip3 (dCsa3AxisApexWithQ isInv.not m v (low 0) (low 1) (low 2) rQ wQc rT rScr
        h01 h02 h12 h1Q h1Qc hQQc h1T hQT h0S h1S h2S hQS hQcS hTS)) := by
    refine ⟨⟨cFlip3.inverse.eval * uCsa * cFlip3.eval, hwLow, hDiagLow, fun ξ hz35 hHq ↦ ?_⟩⟩
    have hp0 := PreservesReg.of_cnotAllCircuit (rT := rT) (rQ 0) (low 0) (hq_low 0)
      (hQT.apply_not_mem_right 0) h0T
    have hp1 := PreservesReg.of_cnotAllCircuit (rT := rT) (rQ 1) (low 1) (hq_low 1)
      (hQT.apply_not_mem_right 1) h1T
    have hp2 := PreservesReg.of_cnotAllCircuit (rT := rT) (rQ 2) (low 2) (hq_low 2)
      (hQT.apply_not_mem_right 2) h2T
    have hpAll := hp0.seq (hp1.seq hp2)
    let fStep : Fin 3 → BitAssignment n → BitAssignment n :=
      fun w β ↦ if β (rQ w) = 1 then flipRegBits (low w) β else β
    let η : BitAssignment n := ((fStep 2 ∘ fStep 1) ∘ fStep 0) ξ
    have hfStep_out : ∀ (w : Fin 3) (β : BitAssignment n) (u : Wire n),
        u ∉ (low w).image → fStep w β u = β u := by
      intro w β u hu; dsimp [fStep]; split_ifs <;> simp [flipRegBits_outside (low w) β hu]
    have hη_out_core : ∀ u : Wire n, u ∉ rCore.image → η u = ξ u := by
      intro u hu
      dsimp [η]
      rw [hfStep_out 2 _ u (fun h ↦ hu (hLow_sub 2 h)),
        hfStep_out 1 _ u (fun h ↦ hu (hLow_sub 1 h)),
        hfStep_out 0 _ u (fun h ↦ hu (hLow_sub 0 h))]
    have hzQc_η : η wQc = 0 := by
      rw [hη_out_core wQc ((disj_symm hCW35).apply_not_mem_right 0)]
      exact hz35 0
    have hzScr_η : ∀ i : Fin (3 * m + 2), η (rScr i) = 0 := fun i ↦ by
      have hin35 : rScr i ∈ rW35.image := hScr_sub35 ((QRegister.mem_image rScr _).mpr ⟨i, rfl⟩)
      rw [hη_out_core (rScr i) (fun hC ↦ Finset.disjoint_left.mp (QRegExt.disjointWires_to_finset
        hCW35) hC hin35)]
      rcases (QRegister.mem_image rW35 _).mp hin35 with ⟨j, hj⟩
      rw [← hj]; exact hz35 j
    have hη_Q : ∀ w : Fin 3, η (rQ w) = ξ (rQ w) := fun w ↦
      hη_out_core (rQ w) ((disj_symm hCW_Q).apply_not_mem_right w)
    have hη_T : regVal rT η = regVal rT ξ := hpAll.regVal_eq ξ
    have hLow0_η : regVal (low 0) η = regVal (low 0) (fStep 0 ξ) := by
      unfold regVal; congr 1; funext j
      dsimp [η]
      rw [hfStep_out 2 _ _ (h02.apply_not_mem_right j),
        hfStep_out 1 _ _ (h01.apply_not_mem_right j)]
    have hLow1_η : regVal (low 1) η = regVal (low 1) (fStep 1 ξ) := by
      unfold regVal; congr 1; funext j
      dsimp [η]
      rw [hfStep_out 2 _ _ (h12.apply_not_mem_right j)]
      have hq1_f0 : fStep 0 ξ (rQ 1) = ξ (rQ 1) :=
        hfStep_out 0 ξ (rQ 1) ((disj_symm h0Q).apply_not_mem_right 1)
      have hj_f0 : fStep 0 ξ (low 1 j) = ξ (low 1 j) :=
        hfStep_out 0 ξ (low 1 j) ((disj_symm h01).apply_not_mem_right j)
      change (if fStep 0 ξ (rQ 1) = 1 then flipRegBits (low 1) (fStep 0 ξ) else fStep 0 ξ) (low 1
        j) =
        (if ξ (rQ 1) = 1 then flipRegBits (low 1) ξ else ξ) (low 1 j)
      rw [hq1_f0]
      split_ifs <;> simp [flipRegBits, (QRegister.mem_image (low 1) _).mpr ⟨j, rfl⟩, hj_f0]
    have hLow2_η : regVal (low 2) η = regVal (low 2) (fStep 2 ξ) := by
      unfold regVal; congr 1; funext j
      dsimp [η]
      have hq2_f10 : fStep 1 (fStep 0 ξ) (rQ 2) = ξ (rQ 2) := by
        rw [hfStep_out 1 _ _ ((disj_symm h1Q).apply_not_mem_right 2),
          hfStep_out 0 _ _ ((disj_symm h0Q).apply_not_mem_right 2)]
      have hj_f10 : fStep 1 (fStep 0 ξ) (low 2 j) = ξ (low 2 j) := by
        rw [hfStep_out 1 _ _ ((disj_symm h12).apply_not_mem_right j),
          hfStep_out 0 _ _ ((disj_symm h02).apply_not_mem_right j)]
      change (if fStep 1 (fStep 0 ξ) (rQ 2) = 1 then flipRegBits (low 2) (fStep 1 (fStep 0 ξ))
        else fStep 1 (fStep 0 ξ)) (low 2 j) =
        (if ξ (rQ 2) = 1 then flipRegBits (low 2) ξ else ξ) (low 2 j)
      rw [hq2_f10]
      split_ifs <;> simp [flipRegBits, (QRegister.mem_image (low 2) _).mpr ⟨j, rfl⟩, hj_f10]
    have hAt := hKetCsa η hzQc_η hzScr_η
    dsimp only at hAt
    have hPhaseEq : ∀ d : ℤ, apexCarryPhase rT η d = apexCarryPhase rT ξ d := by
      intro d; unfold apexCarryPhase; rw [hη_T]
    rw [hPhaseEq] at hAt
    have hConj := hpAll.conj_shift hAt
    rw [hConj,
      embed_uApexShift45_mulVec_basisKet (by have := k.isLt; dsimp [m]; omega) rCore rPGTwist hCP
        (whStgLowShift hm k isInv) ξ]
    have hDeltaEq : (if isInv.not then (-1 : ℤ) else 1) * (((regVal (low 0) η + (η (rQ
        0)).val) + (regVal (low 1) η + (η (rQ 1)).val) + (regVal (low 2) η + (η (rQ 2)).val) :
        ℕ) : ℤ) = whStgLowShift hm k isInv (fun q ↦ ξ (rCore q)) := by
      have hsgn_not : (if isInv.not then (-1 : ℤ) else 1) = -(if isInv then (-1 : ℤ) else 1) := by
        cases isInv <;> rfl
      have hf0_q : fStep 0 ξ (rQ 0) = ξ (rQ 0) :=
        hfStep_out 0 ξ (rQ 0) ((disj_symm h0Q).apply_not_mem_right 0)
      have hf1_q : fStep 1 ξ (rQ 1) = ξ (rQ 1) :=
        hfStep_out 1 ξ (rQ 1) ((disj_symm h1Q).apply_not_mem_right 1)
      have hf2_q : fStep 2 ξ (rQ 2) = ξ (rQ 2) :=
        hfStep_out 2 ξ (rQ 2) ((disj_symm h2Q).apply_not_mem_right 2)
      have hv0 := regVal_flip_plus_bit_eq (low 0) (rQ 0) ((disj_symm h0Q).apply_not_mem_right 0) ξ
      have hv1 := regVal_flip_plus_bit_eq (low 1) (rQ 1) ((disj_symm h1Q).apply_not_mem_right 1) ξ
      have hv2 := regVal_flip_plus_bit_eq (low 2) (rQ 2) ((disj_symm h2Q).apply_not_mem_right 2) ξ
      dsimp only at hv0 hv1 hv2
      change ((regVal (low 0) (fStep 0 ξ) + (fStep 0 ξ (rQ 0)).val : ℕ) : ℤ) = _ at hv0
      change ((regVal (low 1) (fStep 1 ξ) + (fStep 1 ξ (rQ 1)).val : ℕ) : ℤ) = _ at hv1
      change ((regVal (low 2) (fStep 2 ξ) + (fStep 2 ξ (rQ 2)).val : ℕ) : ℤ) = _ at hv2
      rw [hf0_q] at hv0; rw [hf1_q] at hv1; rw [hf2_q] at hv2
      rw [hsgn_not, hLow0_η, hLow1_η, hLow2_η, hη_Q 0, hη_Q 1, hη_Q 2]
      have hSplitCast : (((regVal (low 0) (fStep 0 ξ) + (ξ (rQ 0)).val) + (regVal (low 1)
          (fStep 1 ξ) + (ξ (rQ 1)).val) + (regVal (low 2) (fStep 2 ξ) + (ξ (rQ 2)).val) : ℕ) :
          ℤ) = ((regVal (low 0) (fStep 0 ξ) + (ξ (rQ 0)).val : ℕ) : ℤ) +
          ((regVal (low 1) (fStep 1 ξ) + (ξ (rQ 1)).val : ℕ) : ℤ) +
          ((regVal (low 2) (fStep 2 ξ) + (ξ (rQ 2)).val : ℕ) : ℤ) := by
        push_cast; ring
      rw [hSplitCast, hv0, hv1, hv2, hq_val ξ 0 hHq, hq_val ξ 1 hHq, hq_val ξ 2 hHq]
      have hRegEq : ∀ w : Fin 3,
          regVal (low w) ξ =
            regVal ((rWhFull hm (QRegExt.idReg _) w).slice 0 (7 - k.val) (by have := k.isLt; omega))
              (fun q ↦ ξ (rCore q)) := by
        intro w
        dsimp only [low]
        rw [regVal_rWhFull_slice_idReg hm rCore w 0 (m + 1) _ ξ]
        exact regVal_slice_congr (rWhFull hm (QRegExt.idReg _) w) _ _ hm1_eq _
      rw [hRegEq 0, hRegEq 1, hRegEq 2, hm1_eq]
      unfold whStgLowShift
      dsimp only
      rw [Fin.sum_univ_three]
    rw [hDeltaEq]
  have hsLow : CondStageSpec rAct rW35 (S_core7 ∪ rQ.image) H_q
      (uApexShift45 (fullSysCoreWires mPayload) (7 - k.val)
        (by have := k.isLt; omega) (whStgLowShift hm k isInv))
      (dPureConj cFlip3 (dCsa3AxisApexWithQ isInv.not m v (low 0) (low 1) (low 2) rQ wQc rT rScr
        h01 h02 h12 h1Q h1Qc hQQc h1T hQT h0S h1S h2S hQS hQcS hTS)) :=
    hsLow_m.congr_unitary (uApexShift45_congr _ _ hm1_eq (fun _ ↦ rfl))
  have hsBody : CondStageSpec rAct rW35 (S_core7 ∪ rQ.image) H_q (uWhStgCat hm k isInv) _ :=
      hsTop.seq hActW35 hHq_congr hsLow
  have hsOuter := CondStageSpec.dMaskRegWrap 3 v wf rPk rQ
    (fun w ↦ (disj_wire_ne ((QRegExt.disjointWires_mono_left hCW) hPk_sub) w 6).symm)
    (fun w hEq ↦ reg_not_mem_slice rWork (by decide) 6 (by decide)
      ((QRegister.image_compose_subset rW38 _) ((QRegister.mem_image rQ _).mpr ⟨w, hEq.symm⟩)))
    ((QRegExt.disjointWires_mono_left hCW_Q) hPk_sub)
    rW35 hQ35
    hwf_not35
    ((QRegExt.disjointWires_mono_left hCW35) hPk_sub)
    ((QRegExt.disjointWires_mono_right hActW38) (QRegister.image_compose_subset rW38 _))
    hwf_S
    (Finset.Subset.trans hPk_sub Finset.subset_union_left)
    (fun ξ₁ ξ₂ hOut hHp1 ↦ (JunctionPrefixPruned220.HProjFlag_congr_S hm rCore rWork
      (Finset.Subset.trans (rHigh_sub_rCore rCore) Finset.subset_union_left) hwf_S ξ₁ ξ₂ fun u hu ↦
        hOut u fun hm' ↦ by
          rcases Finset.mem_union.mp hu with hC | h07
          · exact Finset.disjoint_left.mp (QRegExt.disjointWires_to_finset hCW_Q) hC hm'
          · exact Finset.disjoint_left.mp
              (QRegExt.disjointWires_to_finset (slice_disjoint_of_le rWork 0 7 7 38 (by decide) (by
                decide) (by decide)))
              h07 ((QRegister.image_compose_subset rW38 _) hm')).mp hHp1)
    hsBody
  have hQ35_eq : (rQ.concat rW35 hQ35).image = rW38.image := by
    rw [slice_concat_image_eq rW38 (by decide) (by decide) (by decide) hQ35]
    ext u; simp only [QRegister.mem_image]
    constructor
    · rintro ⟨i, rfl⟩; rw [slice_apply_eq]; exact ⟨⟨0 + i.val, by have := i.isLt; omega⟩, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨i, by rw [slice_apply_eq]; apply congrArg rW38; apply Fin.ext; dsimp; omega⟩
  exact hsOuter.widen_workspace (by rw [hQ35_eq]) (by rw [hQ35_eq])
theorem dWhStg7_3D_biSpec_Pos45 {mPayload : ℕ} (isInv : Bool) (hm : 22 ≤ mPayload)
    {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ} (v : Var)
    (rCore : QRegister (fullSysCoreWires mPayload) n)
    (rPGTwist : QRegister 48 n) (rWork : QRegister JunctionPrefixPruned220.mWork45 n)
    (hCP : rCore.DisjointWires rPGTwist)
    (hCW : rCore.DisjointWires rWork) (hPW : rPGTwist.DisjointWires rWork) :
    CondStageSpec (rCore.concat rPGTwist hCP)
      (rWork.slice 7 38 (by have := JunctionPrefixPruned220.mw45_b2; omega))
      ((rHigh rCore).image ∪ (rWork.slice 0 7 (by
        have := JunctionPrefixPruned220.mw45_b2; omega)).image)
      (JunctionPrefixPruned220.HProjFlag hm rCore rWork)
      (if isInv then (uWhStg7Cat hm false)⁻¹ else uWhStg7Cat hm false)
      (dWhStg7_3D_Pos45 isInv hm v rCore rWork hCW) := by
  cases isInv
  · exact dWhStg7_3D_spec_Pos45 false hm v rCore rPGTwist rWork hCP hCW hPW
  · exact (dWhStg7_3D_spec_Pos45 true hm v rCore rPGTwist rWork hCP hCW hPW).congr_unitary
      (uWhStg7Cat_inv_eq hm).symm
theorem dWhStg_3D_biSpec_Pos45 {mPayload : ℕ} (isInv : Bool) (hm : 22 ≤ mPayload)
    {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ} (v : Var)
    (k : Fin 7)
    (rCore : QRegister (fullSysCoreWires mPayload) n)
    (rPGTwist : QRegister 48 n) (rWork : QRegister JunctionPrefixPruned220.mWork45 n)
    (hCP : rCore.DisjointWires rPGTwist)
    (hCW : rCore.DisjointWires rWork) (hPW : rPGTwist.DisjointWires rWork) :
    CondStageSpec (rCore.concat rPGTwist hCP)
      (rWork.slice 7 38 (by have := JunctionPrefixPruned220.mw45_b2; omega))
      ((rHigh rCore).image ∪ (rWork.slice 0 7 (by
        have := JunctionPrefixPruned220.mw45_b2; omega)).image)
      (JunctionPrefixPruned220.HProjFlag hm rCore rWork)
      (if isInv then (uWhStgCat hm k false)⁻¹ else uWhStgCat hm k false)
      (dWhStg_3D_Pos45 isInv hm v k rCore rPGTwist rWork hCP hCW hPW) := by
  cases isInv
  · exact dWhStg_3D_spec_Pos45 false hm v k rCore rPGTwist rWork hCP hCW hPW
  · exact (dWhStg_3D_spec_Pos45 true hm v k rCore rPGTwist rWork hCP hCW hPW).congr_unitary
      (uWhStgCat_inv_eq hm k).symm
/-- Internal `45`-wire Hadamard-tail-cut helper `HPosBranchFlag_Pos45`. -/
def HPosBranchFlag_Pos45 {mPayload n : ℕ} (rCore : QRegister (fullSysCoreWires mPayload) n)
    (rWork : QRegister JunctionPrefixPruned220.mWork45 n) (ξ : BitAssignment n) : Prop := ξ
    (rWork 1) = if posBranchActive (fun q ↦ ξ (rCore q)) then 1 else 0
theorem HPosBranchFlag_congr_S_Pos45 {mPayload n : ℕ} {S : Finset (Wire n)}
    (rCore : QRegister (fullSysCoreWires mPayload) n)
    (rWork : QRegister JunctionPrefixPruned220.mWork45 n) (hHighSub : (rHigh rCore).image ⊆ S)
    (hw1 : rWork 1 ∈ S) : ∀ ξ₁ ξ₂ : BitAssignment n, (∀ w ∈ S, ξ₁ w = ξ₂ w) →
    (HPosBranchFlag_Pos45 rCore rWork ξ₁ ↔ HPosBranchFlag_Pos45 rCore rWork ξ₂) := by
  intro ξ₁ ξ₂ hEq
  unfold HPosBranchFlag_Pos45 posBranchActive
  dsimp only
  have hs2 : rCore (wSlot2 (QRegExt.idReg _)) = wSlot2 rCore := by
    unfold wSlot2; simp [QRegExt.idReg]
  simp only [hs2, hEq (rWork 1) hw1, hEq (wSlot2 rCore) (hHighSub (wSlot2_mem_rHigh rCore))]
/-- Internal `45`-wire Hadamard-tail-cut helper `rCoreSwap_Pos45`. -/
def rCoreSwap_Pos45 {mPayload n : ℕ} (hm : 22 ≤ mPayload)
    (rCore : QRegister (fullSysCoreWires mPayload) n)
    (rWork : QRegister JunctionPrefixPruned220.mWork45 n)
    (hCW : rCore.DisjointWires rWork) : QRegister (fullSysCoreWires mPayload) n where
  wires :=
    ⟨fun q ↦
      let rId := QRegExt.idReg (fullSysCoreWires mPayload)
      if q = wSlot0 rId then rWork 5
      else if q = wSlot1 rId then rWork 6
      else if q = rNucIdx hm rId 5 then rWork 2
      else if q = rNucIdx hm rId 6 then rWork 3
      else if q = rNucIdx hm rId 7 then rWork 4
      else rCore q,
     by
      intro q₁ q₂ hEq
      dsimp only at hEq
      have hCwNe : ∀ (q : Fin (fullSysCoreWires mPayload)) (k : Fin
        JunctionPrefixPruned220.mWork45), rCore q ≠ rWork k :=
        fun q k h ↦ Finset.disjoint_left.mp (QRegExt.disjointWires_to_finset hCW)
          ((QRegister.mem_image rCore _).mpr ⟨q, rfl⟩)
          ((QRegister.mem_image rWork _).mpr ⟨k, h.symm⟩)
      have hWkNe : ∀ {i j : Fin JunctionPrefixPruned220.mWork45}, i.val ≠ j.val → rWork i ≠ rWork
        j :=
        fun hij h ↦ hij (congrArg Fin.val (rWork.wires.injective h))
      split_ifs at hEq <;>
        first
        | (subst q₁; subst q₂; rfl)
        | exact False.elim (hWkNe (by dsimp [JunctionPrefixPruned220.mWork45]; omega) hEq)
        | exact False.elim (hCwNe _ _ hEq.symm)
        | exact False.elim (hCwNe _ _ hEq)
        | exact rCore.wires.injective hEq⟩
/-- Internal `45`-wire Hadamard-tail-cut helper `rWorkSwap_Pos45`. -/
def rWorkSwap_Pos45 {mPayload n : ℕ} (hm : 22 ≤ mPayload)
    (rCore : QRegister (fullSysCoreWires mPayload) n)
    (rWork : QRegister JunctionPrefixPruned220.mWork45 n)
    (hCW : rCore.DisjointWires rWork) : QRegister JunctionPrefixPruned220.mWork45 n where
  wires :=
    ⟨fun k ↦
      let rId := QRegExt.idReg (fullSysCoreWires mPayload)
      if k.val = 1 then rCore (wSlot0 rId)
      else if k.val = 2 then rCore (rNucIdx hm rId 5)
      else if k.val = 3 then rCore (rNucIdx hm rId 6)
      else if k.val = 4 then rCore (rNucIdx hm rId 7)
      else if k.val = 5 then rCore (wSlot1 rId)
      else if k.val = 6 then rWork 1
      else rWork k,
     by
      intro k₁ k₂ hEq
      dsimp only at hEq
      have hCwNe : ∀ (q : Fin (fullSysCoreWires mPayload)) (k : Fin
        JunctionPrefixPruned220.mWork45), rCore q ≠ rWork k :=
        fun q k h ↦ Finset.disjoint_left.mp (QRegExt.disjointWires_to_finset hCW)
          ((QRegister.mem_image rCore _).mpr ⟨q, rfl⟩)
          ((QRegister.mem_image rWork _).mpr ⟨k, h.symm⟩)
      have hWkNe : ∀ {i j : Fin JunctionPrefixPruned220.mWork45}, i.val ≠ j.val → rWork i ≠ rWork
        j :=
        fun hij h ↦ hij (congrArg Fin.val (rWork.wires.injective h))
      have hCoreValNe : ∀ {a b : Wire (fullSysCoreWires mPayload)}, a.val ≠ b.val → rCore a ≠
          rCore b := fun hab h ↦ hab (congrArg Fin.val (rCore.wires.injective h))
      split_ifs at hEq <;>
        try { exact Fin.ext (by omega) } <;>
        try { exact False.elim (hCwNe _ _ hEq) } <;>
        try { exact False.elim (hCwNe _ _ hEq.symm) } <;>
        try { exact False.elim (hCoreValNe (by
          simp only [wSlot0_val_eq, wSlot1_val_eq, rNucIdx_val_eq]; decide) hEq) } <;>
        try { exact False.elim (hWkNe (by dsimp [JunctionPrefixPruned220.mWork45] at *; omega) hEq)
          }
      exact rWork.wires.injective hEq⟩
theorem rCoreSwap_disj_rPGTwist_Pos45 {mPayload n : ℕ} (hm : 22 ≤ mPayload)
    (rCore : QRegister (fullSysCoreWires mPayload) n) (rPGTwist : QRegister 48 n)
    (rWork : QRegister JunctionPrefixPruned220.mWork45 n) (hCP : rCore.DisjointWires rPGTwist)
    (hCW : rCore.DisjointWires rWork) (hPW : rPGTwist.DisjointWires rWork) :
    (rCoreSwap_Pos45 hm rCore rWork hCW).DisjointWires rPGTwist := by
  rw [QRegister.DisjointWires, Set.disjoint_left]
  rintro _ ⟨q, rfl⟩ ⟨p, hEq⟩
  dsimp [rCoreSwap_Pos45] at hEq
  split_ifs at hEq <;>
    first
    | exact Finset.disjoint_left.mp (QRegExt.disjointWires_to_finset hPW)
        ((QRegister.mem_image rPGTwist _).mpr ⟨p, rfl⟩)
        ((QRegister.mem_image rWork _).mpr ⟨_, hEq.symm⟩)
    | exact Finset.disjoint_left.mp (QRegExt.disjointWires_to_finset hCP)
        ((QRegister.mem_image rCore _).mpr ⟨q, rfl⟩)
        ((QRegister.mem_image rPGTwist _).mpr ⟨p, hEq⟩)
theorem rCoreSwap_disj_rWorkSwap_Pos45 {mPayload n : ℕ} (hm : 22 ≤ mPayload)
    (rCore : QRegister (fullSysCoreWires mPayload) n)
    (rWork : QRegister JunctionPrefixPruned220.mWork45 n)
    (hCW : rCore.DisjointWires rWork) :
    (rCoreSwap_Pos45 hm rCore rWork hCW).DisjointWires (rWorkSwap_Pos45 hm rCore rWork hCW) := by
  rw [QRegister.DisjointWires, Set.disjoint_left]
  rintro _ ⟨q, rfl⟩ ⟨k, hEq⟩
  dsimp [rCoreSwap_Pos45, rWorkSwap_Pos45] at hEq
  have hCwNe : ∀ (a : Fin (fullSysCoreWires mPayload)) (b : Fin JunctionPrefixPruned220.mWork45),
    rCore a ≠ rWork b :=
    fun a b h ↦ Finset.disjoint_left.mp (QRegExt.disjointWires_to_finset hCW)
      ((QRegister.mem_image rCore _).mpr ⟨a, rfl⟩)
      ((QRegister.mem_image rWork _).mpr ⟨b, h.symm⟩)
  have hWkNe : ∀ {i j : Fin JunctionPrefixPruned220.mWork45}, i.val ≠ j.val → rWork i ≠ rWork j :=
    fun hij h ↦ hij (congrArg Fin.val (rWork.wires.injective h))
  split_ifs at hEq <;>
    try { exact hWkNe (by dsimp [JunctionPrefixPruned220.mWork45] at *; omega) hEq.symm } <;>
    try { exact hCwNe _ _ hEq } <;>
    try { exact hCwNe _ _ hEq.symm } <;>
    (have hq := rCore.wires.injective hEq.symm; contradiction)
theorem rPGTwist_disj_rWorkSwap_Pos45 {mPayload n : ℕ} (hm : 22 ≤ mPayload)
    (rCore : QRegister (fullSysCoreWires mPayload) n) (rPGTwist : QRegister 48 n)
    (rWork : QRegister JunctionPrefixPruned220.mWork45 n) (hCP : rCore.DisjointWires rPGTwist)
    (hCW : rCore.DisjointWires rWork) (hPW : rPGTwist.DisjointWires rWork) :
    rPGTwist.DisjointWires (rWorkSwap_Pos45 hm rCore rWork hCW) := by
  rw [QRegister.DisjointWires, Set.disjoint_left]
  rintro _ ⟨p, rfl⟩ ⟨k, hEq⟩
  dsimp [rWorkSwap_Pos45] at hEq
  split_ifs at hEq <;>
    first
    | exact Finset.disjoint_left.mp (QRegExt.disjointWires_to_finset hPW)
        ((QRegister.mem_image rPGTwist _).mpr ⟨p, rfl⟩)
        ((QRegister.mem_image rWork _).mpr ⟨_, hEq⟩)
    | exact Finset.disjoint_left.mp (QRegExt.disjointWires_to_finset hCP)
        ((QRegister.mem_image rCore _).mpr ⟨_, rfl⟩)
        ((QRegister.mem_image rPGTwist _).mpr ⟨p, hEq.symm⟩)
theorem rWorkSwap_slice7_38_eq_Pos45 {mPayload n : ℕ} (hm : 22 ≤ mPayload)
    (rCore : QRegister (fullSysCoreWires mPayload) n)
    (rWork : QRegister JunctionPrefixPruned220.mWork45 n) (hCW : rCore.DisjointWires rWork) :
    (rWorkSwap_Pos45 hm rCore rWork hCW).slice 7 38 (by
      have := JunctionPrefixPruned220.mw45_b2; omega) =
      rWork.slice 7 38 (by have := JunctionPrefixPruned220.mw45_b2; omega) := by
  apply qreg_ext; intro j
  rw [QRegister.slice_apply, QRegister.slice_apply]
  dsimp [rWorkSwap_Pos45]
  split_ifs <;> first | rfl | omega
theorem rCoreSwap_wSlot0_Pos45 {mPayload n : ℕ} (hm : 22 ≤ mPayload)
    (rCore : QRegister (fullSysCoreWires mPayload) n)
    (rWork : QRegister JunctionPrefixPruned220.mWork45 n) (hCW : rCore.DisjointWires rWork) :
    rCoreSwap_Pos45 hm rCore rWork hCW (wSlot0 (QRegExt.idReg _)) = rWork 5 := by
  simp [rCoreSwap_Pos45]
theorem rCoreSwap_wSlot1_Pos45 {mPayload n : ℕ} (hm : 22 ≤ mPayload)
    (rCore : QRegister (fullSysCoreWires mPayload) n)
    (rWork : QRegister JunctionPrefixPruned220.mWork45 n) (hCW : rCore.DisjointWires rWork) :
    rCoreSwap_Pos45 hm rCore rWork hCW (wSlot1 (QRegExt.idReg _)) = rWork 6 := by
  have hne : wSlot1 (QRegExt.idReg (fullSysCoreWires mPayload)) ≠
      wSlot0 (QRegExt.idReg (fullSysCoreWires mPayload)) := fun h ↦ by
    have hv := congrArg Fin.val h; rw [wSlot1_val_eq, wSlot0_val_eq] at hv; omega
  dsimp [rCoreSwap_Pos45]; simp only [hne, ↓reduceIte]
theorem rCoreSwap_rNuc5_Pos45 {mPayload n : ℕ} (hm : 22 ≤ mPayload)
    (rCore : QRegister (fullSysCoreWires mPayload) n)
    (rWork : QRegister JunctionPrefixPruned220.mWork45 n) (hCW : rCore.DisjointWires rWork) :
    rCoreSwap_Pos45 hm rCore rWork hCW (rNucIdx hm (QRegExt.idReg _) 5) = rWork 2 := by
  have hs0 : rNucIdx hm (QRegExt.idReg (fullSysCoreWires mPayload)) 5 ≠
      wSlot0 (QRegExt.idReg _) := fun h ↦ by
    have hv := congrArg Fin.val h; rw [rNucIdx_val_eq, wSlot0_val_eq] at hv; omega
  have hs1 : rNucIdx hm (QRegExt.idReg (fullSysCoreWires mPayload)) 5 ≠
      wSlot1 (QRegExt.idReg _) := fun h ↦ by
    have hv := congrArg Fin.val h; rw [rNucIdx_val_eq, wSlot1_val_eq] at hv; omega
  dsimp [rCoreSwap_Pos45]; simp only [hs0, hs1, ↓reduceIte]
theorem rCoreSwap_rNuc6_Pos45 {mPayload n : ℕ} (hm : 22 ≤ mPayload)
    (rCore : QRegister (fullSysCoreWires mPayload) n)
    (rWork : QRegister JunctionPrefixPruned220.mWork45 n) (hCW : rCore.DisjointWires rWork) :
    rCoreSwap_Pos45 hm rCore rWork hCW (rNucIdx hm (QRegExt.idReg _) 6) = rWork 3 := by
  have hs0 : rNucIdx hm (QRegExt.idReg (fullSysCoreWires mPayload)) 6 ≠
      wSlot0 (QRegExt.idReg _) := fun h ↦ by
    have hv := congrArg Fin.val h; rw [rNucIdx_val_eq, wSlot0_val_eq] at hv; omega
  have hs1 : rNucIdx hm (QRegExt.idReg (fullSysCoreWires mPayload)) 6 ≠
      wSlot1 (QRegExt.idReg _) := fun h ↦ by
    have hv := congrArg Fin.val h; rw [rNucIdx_val_eq, wSlot1_val_eq] at hv; omega
  dsimp [rCoreSwap_Pos45]; simp only [hs0, hs1, ↓reduceIte]
theorem rCoreSwap_rNuc7_Pos45 {mPayload n : ℕ} (hm : 22 ≤ mPayload)
    (rCore : QRegister (fullSysCoreWires mPayload) n)
    (rWork : QRegister JunctionPrefixPruned220.mWork45 n) (hCW : rCore.DisjointWires rWork) :
    rCoreSwap_Pos45 hm rCore rWork hCW (rNucIdx hm (QRegExt.idReg _) 7) = rWork 4 := by
  have hs0 : rNucIdx hm (QRegExt.idReg (fullSysCoreWires mPayload)) 7 ≠
      wSlot0 (QRegExt.idReg _) := fun h ↦ by
    have hv := congrArg Fin.val h; rw [rNucIdx_val_eq, wSlot0_val_eq] at hv; omega
  have hs1 : rNucIdx hm (QRegExt.idReg (fullSysCoreWires mPayload)) 7 ≠
      wSlot1 (QRegExt.idReg _) := fun h ↦ by
    have hv := congrArg Fin.val h; rw [rNucIdx_val_eq, wSlot1_val_eq] at hv; omega
  dsimp [rCoreSwap_Pos45]; simp only [hs0, hs1, ↓reduceIte]
/-- Internal `45`-wire Hadamard-tail-cut helper `SwapWorkBits_Pos45`. -/
def SwapWorkBits_Pos45 {n : ℕ} (rWork : QRegister JunctionPrefixPruned220.mWork45 n) (η :
    BitAssignment n) : Prop :=
  η (rWork 2) = 1 ∧ η (rWork 3) = 1 ∧ η (rWork 4) = 1 ∧
    η (rWork 5) = 0 ∧ η (rWork 6) = 0
theorem rCoreSwap_bits_eq_setHighNucBits_Pos45 {mPayload n : ℕ} (hm : 22 ≤ mPayload)
    (rCore : QRegister (fullSysCoreWires mPayload) n)
    (rWork : QRegister JunctionPrefixPruned220.mWork45 n) (hCW : rCore.DisjointWires rWork)
    {η : BitAssignment n} (hw : SwapWorkBits_Pos45 rWork η) :
    (fun q ↦ η (rCoreSwap_Pos45 hm rCore rWork hCW q)) = setHighNucBits hm (fun q ↦ η (rCore q)) :=
      by
  rcases hw with ⟨hw2, hw3, hw4, hw5, hw6⟩
  funext q
  let rId := QRegExt.idReg (fullSysCoreWires mPayload)
  let rN := rNucIdx hm rId
  have hs0_s1 : wSlot0 rId ≠ wSlot1 rId := fun h ↦ by
    have hv := congrArg Fin.val h; rw [wSlot0_val_eq, wSlot1_val_eq] at hv; omega
  have hs0_5 : wSlot0 rId ≠ rN 5 := fun h ↦ by
    have hv := congrArg Fin.val h; rw [wSlot0_val_eq, rNucIdx_val_eq] at hv; omega
  have hs0_6 : wSlot0 rId ≠ rN 6 := fun h ↦ by
    have hv := congrArg Fin.val h; rw [wSlot0_val_eq, rNucIdx_val_eq] at hv; omega
  have hs0_7 : wSlot0 rId ≠ rN 7 := fun h ↦ by
    have hv := congrArg Fin.val h; rw [wSlot0_val_eq, rNucIdx_val_eq] at hv; omega
  have hs1_5 : wSlot1 rId ≠ rN 5 := fun h ↦ by
    have hv := congrArg Fin.val h; rw [wSlot1_val_eq, rNucIdx_val_eq] at hv; omega
  have hs1_6 : wSlot1 rId ≠ rN 6 := fun h ↦ by
    have hv := congrArg Fin.val h; rw [wSlot1_val_eq, rNucIdx_val_eq] at hv; omega
  have hs1_7 : wSlot1 rId ≠ rN 7 := fun h ↦ by
    have hv := congrArg Fin.val h; rw [wSlot1_val_eq, rNucIdx_val_eq] at hv; omega
  have h56 : rN 5 ≠ rN 6 := fun h ↦ by
    have hv := congrArg Fin.val h; rw [rNucIdx_val_eq, rNucIdx_val_eq] at hv; omega
  have h57 : rN 5 ≠ rN 7 := fun h ↦ by
    have hv := congrArg Fin.val h; rw [rNucIdx_val_eq, rNucIdx_val_eq] at hv; omega
  have h67 : rN 6 ≠ rN 7 := fun h ↦ by
    have hv := congrArg Fin.val h; rw [rNucIdx_val_eq, rNucIdx_val_eq] at hv; omega
  dsimp only [rId, rN] at hs0_s1 hs0_5 hs0_6 hs0_7 hs1_5 hs1_6 hs1_7 h56 h57 h67
  by_cases hs0 : q = wSlot0 (QRegExt.idReg (fullSysCoreWires mPayload))
  · subst hs0; rw [rCoreSwap_wSlot0_Pos45, hw5]; unfold setHighNucBits
    rw [Function.update_of_ne hs0_7, Function.update_of_ne hs0_6, Function.update_of_ne hs0_5,
        Function.update_of_ne hs0_s1, Function.update_self]
  · by_cases hs1 : q = wSlot1 (QRegExt.idReg (fullSysCoreWires mPayload))
    · subst hs1; rw [rCoreSwap_wSlot1_Pos45, hw6]; unfold setHighNucBits
      rw [Function.update_of_ne hs1_7, Function.update_of_ne hs1_6, Function.update_of_ne hs1_5,
          Function.update_self]
    · by_cases h5 : q = rNucIdx hm (QRegExt.idReg (fullSysCoreWires mPayload)) 5
      · subst h5; rw [rCoreSwap_rNuc5_Pos45, hw2]; unfold setHighNucBits
        rw [Function.update_of_ne h57, Function.update_of_ne h56, Function.update_self]
      · by_cases h6 : q = rNucIdx hm (QRegExt.idReg (fullSysCoreWires mPayload)) 6
        · subst h6; rw [rCoreSwap_rNuc6_Pos45, hw3]; unfold setHighNucBits
          rw [Function.update_of_ne h67, Function.update_self]
        · by_cases h7 : q = rNucIdx hm (QRegExt.idReg (fullSysCoreWires mPayload)) 7
          · subst h7; rw [rCoreSwap_rNuc7_Pos45, hw4]; unfold setHighNucBits
            rw [Function.update_self]
          · have hcs : rCoreSwap_Pos45 hm rCore rWork hCW q = rCore q := by
              dsimp [rCoreSwap_Pos45]; simp only [hs0, hs1, h5, h6, h7, ↓reduceIte]
            rw [hcs]
            exact (setHighNucBits_apply_of_ne hm (fun q ↦ η (rCore q)) hs0 hs1 h5 h6 h7).symm
theorem rProjAxis_rCoreSwap_eq_Pos45 {mPayload n : ℕ} (hm : 22 ≤ mPayload)
    (rCore : QRegister (fullSysCoreWires mPayload) n)
    (rWork : QRegister JunctionPrefixPruned220.mWork45 n) (hCW : rCore.DisjointWires rWork) (w : Fin
      3) :
    rProjAxis (rCoreSwap_Pos45 hm rCore rWork hCW) w = rProjAxis rCore w := by
  ext m
  have hlt := rProjAxis_wire_lt_3948 (mPayload := mPayload) w m
  have hs0 : rProjAxis (QRegExt.idReg _) w m ≠ wSlot0 (QRegExt.idReg _) :=
    fun h ↦ by rw [h, wSlot0_val_eq] at hlt; omega
  have hs1 : rProjAxis (QRegExt.idReg _) w m ≠ wSlot1 (QRegExt.idReg _) :=
    fun h ↦ by rw [h, wSlot1_val_eq] at hlt; omega
  have h5 : rProjAxis (QRegExt.idReg _) w m ≠ rNucIdx hm (QRegExt.idReg _) 5 :=
    fun h ↦ by rw [h, rNucIdx_val_eq] at hlt; omega
  have h6 : rProjAxis (QRegExt.idReg _) w m ≠ rNucIdx hm (QRegExt.idReg _) 6 :=
    fun h ↦ by rw [h, rNucIdx_val_eq] at hlt; omega
  have h7 : rProjAxis (QRegExt.idReg _) w m ≠ rNucIdx hm (QRegExt.idReg _) 7 :=
    fun h ↦ by rw [h, rNucIdx_val_eq] at hlt; omega
  change (rCoreSwap_Pos45 hm rCore rWork hCW (rProjAxis (QRegExt.idReg _) w m)).val =
    (rCore (rProjAxis (QRegExt.idReg _) w m)).val
  dsimp [rCoreSwap_Pos45]
  simp only [hs0, hs1, h5, h6, h7, ↓reduceIte]
theorem embed_uApexShift45_rCoreSwap_ket_Pos45 {mPayload n : ℕ} (hm : 22 ≤ mPayload) (W : ℕ)
    (hW : W ≤ 45) (δ : BitAssignment (fullSysCoreWires mPayload) → ℤ)
    (rCore : QRegister (fullSysCoreWires mPayload) n) (rPGTwist : QRegister 48 n)
    (rWork : QRegister JunctionPrefixPruned220.mWork45 n) (hCP : rCore.DisjointWires rPGTwist)
    (hCW : rCore.DisjointWires rWork) (hPW : rPGTwist.DisjointWires rWork)
    {η : BitAssignment n} (hw : SwapWorkBits_Pos45 rWork η) : (((rCoreSwap_Pos45 hm rCore
    rWork hCW).concat rPGTwist (rCoreSwap_disj_rPGTwist_Pos45 hm rCore rPGTwist rWork hCP hCW
    hPW)).embedUnitary (uApexShift45 (fullSysCoreWires mPayload) W hW δ)).1.mulVec
    (basisKet η) = ((rCore.concat rPGTwist hCP).embedUnitary (uApexShift45 (fullSysCoreWires
    mPayload) W hW (fun γ ↦ δ (setHighNucBits hm γ)))).1.mulVec (basisKet η) := by
  unfold uApexShift45
  rw [embed_uApexShiftA_mulVec_basisKet hW, embed_uApexShiftA_mulVec_basisKet hW,
      rCoreSwap_bits_eq_setHighNucBits_Pos45 hm rCore rWork hCW hw]
theorem embed_dyadicDiag_rCoreSwap_ket_Pos45 {mPayload n : ℕ} (hm : 22 ≤ mPayload)
    (e : BitAssignment (fullSysCoreWires mPayload) → ℤ)
    (rCore : QRegister (fullSysCoreWires mPayload) n) (rPGTwist : QRegister 48 n)
    (rWork : QRegister JunctionPrefixPruned220.mWork45 n) (hCP : rCore.DisjointWires rPGTwist)
    (hCW : rCore.DisjointWires rWork) (hPW : rPGTwist.DisjointWires rWork)
    {η : BitAssignment n} (hw : SwapWorkBits_Pos45 rWork η) : (((rCoreSwap_Pos45 hm rCore
    rWork hCW).concat rPGTwist (rCoreSwap_disj_rPGTwist_Pos45 hm rCore rPGTwist rWork hCP hCW
    hPW)).embedUnitary ((rCoreBlock48 mPayload).embedUnitary (DyadicQft64.dyadicDiagUnitary
    (fullSysCoreWires mPayload) 48 e))).1.mulVec (basisKet η) = ((rCore.concat rPGTwist
    hCP).embedUnitary ((rCoreBlock48 mPayload).embedUnitary (DyadicQft64.dyadicDiagUnitary
    (fullSysCoreWires mPayload) 48 (fun γ ↦ e (setHighNucBits hm γ))))).1.mulVec (basisKet η)
    := by
  let rCS := rCoreSwap_Pos45 hm rCore rWork hCW
  let hCSP := rCoreSwap_disj_rPGTwist_Pos45 hm rCore rPGTwist rWork hCP hCW hPW
  have hbits := rCoreSwap_bits_eq_setHighNucBits_Pos45 hm rCore rWork hCW hw
  rw [← QRegister.embedUnitary_compose, ← QRegister.embedUnitary_compose,
    compose_rCoreBlock48_eq rCS rPGTwist hCSP, compose_rCoreBlock48_eq rCore rPGTwist hCP,
    embedUnitary_dyadicDiagUnitary_mulVec_basisKet,
    embedUnitary_dyadicDiagUnitary_mulVec_basisKet]
  dsimp only [rCS]
  rw [hbits]
theorem mw_slice_7_38_le_Pos45 : 7 + 38 ≤ JunctionPrefixPruned220.mWork45 := by
  have := JunctionPrefixPruned220.mw45_b2; omega
theorem mw_slice_0_7_le_Pos45 : 0 + 7 ≤ JunctionPrefixPruned220.mWork45 := by
  have := JunctionPrefixPruned220.mw45_b2; omega
theorem mw_slice_2_43_le_Pos45 : 2 + 43 ≤ JunctionPrefixPruned220.mWork45 := by
  have := JunctionPrefixPruned220.mw45_b2; omega
theorem mw_slice_0_2_le_Pos45 : 0 + 2 ≤ JunctionPrefixPruned220.mWork45 := by
  have := JunctionPrefixPruned220.mw45_b2; omega
theorem mw_slice_0_45_le_Pos45 : 0 + 45 ≤ JunctionPrefixPruned220.mWork45 := by
  have := JunctionPrefixPruned220.mw45_b2; omega
theorem mw_slice_0_0_le_Pos45 : 0 + 0 ≤ JunctionPrefixPruned220.mWork45 := by
  have := JunctionPrefixPruned220.mw45_b2; omega
theorem mw_idx_1_lt_Pos45 : 1 < JunctionPrefixPruned220.mWork45 := by
  have := JunctionPrefixPruned220.mw45_b2; omega
/-- Internal `45`-wire Hadamard-tail-cut helper `cX234_Pos45`. -/
def cX234_Pos45 {n : ℕ} (rWork : QRegister JunctionPrefixPruned220.mWork45 n) : Circuit n :=
  Circuit.X (rWork 2) ;;ᶜ (Circuit.X (rWork 3) ;;ᶜ Circuit.X (rWork 4))
@[local simp]
theorem count_cX234_toff_Pos45 {n : ℕ} (rWork : QRegister JunctionPrefixPruned220.mWork45 n) :
    (cX234_Pos45 rWork).count .TOFF = 0 := rfl
@[local simp]
theorem count_cX234_t_Pos45 {n : ℕ} (rWork : QRegister JunctionPrefixPruned220.mWork45 n) :
    (cX234_Pos45 rWork).count .T = 0 := rfl
theorem mulVec_chain_rCoreSwap_step_Pos45 {mPayload n : ℕ} (hm : 22 ≤ mPayload)
    (rCore : QRegister (fullSysCoreWires mPayload) n) (rPGTwist : QRegister 48 n)
    (rWork : QRegister JunctionPrefixPruned220.mWork45 n) (hCP : rCore.DisjointWires rPGTwist)
    (hCW : rCore.DisjointWires rWork) (hPW : rPGTwist.DisjointWires rWork)
    {V W : Unitary (2 ^ (fullSysCoreWires mPayload + 48))} (h1 : ∀ ζ : BitAssignment n,
    SwapWorkBits_Pos45 rWork ζ → (((rCoreSwap_Pos45 hm rCore rWork hCW).concat rPGTwist
    (rCoreSwap_disj_rPGTwist_Pos45 hm rCore rPGTwist rWork hCP hCW hPW)).embedUnitary
    V).1.mulVec (basisKet ζ) = ((rCore.concat rPGTwist hCP).embedUnitary W).1.mulVec (basisKet
    ζ)) {ψ₁ ψ₂ : Fin (2 ^ n) → ℂ} (hψ : ψ₁ = ψ₂) (hSupp : ∀ k : Fin (2 ^ n), ψ₂ k ≠ 0 →
    SwapWorkBits_Pos45 rWork (basisBits n k)) : (((rCoreSwap_Pos45 hm rCore rWork hCW).concat
    rPGTwist (rCoreSwap_disj_rPGTwist_Pos45 hm rCore rPGTwist rWork hCP hCW hPW)).embedUnitary
    V).1.mulVec ψ₁ = ((rCore.concat rPGTwist hCP).embedUnitary W).1.mulVec ψ₂ ∧ (∀ k : Fin (2
    ^ n), (((rCore.concat rPGTwist hCP).embedUnitary W).1.mulVec ψ₂) k ≠ 0 →
    SwapWorkBits_Pos45 rWork (basisBits n k)) := by
  subst hψ
  refine ⟨?_, ?_⟩
  · rw [vec_decomp_basisKet ψ₁, Matrix.mulVec_sum, Matrix.mulVec_sum]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    by_cases h0 : ψ₁ k = 0
    · simp [h0]
    · rw [Matrix.mulVec_smul, Matrix.mulVec_smul]
      rw [h1 (basisBits n k) (hSupp k h0)]
  · intro k hne
    rw [vec_decomp_basisKet ψ₁, Matrix.mulVec_sum, Finset.sum_apply] at hne
    obtain ⟨m, _, hm_ne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
    rw [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul] at hm_ne
    obtain ⟨hm2, hm3, hm4, hm5, hm6⟩ := hSupp m (left_ne_zero_of_mul hm_ne)
    have hmR := right_ne_zero_of_mul hm_ne
    rw [mulVec_basisKet_apply, QRegister.embedUnitary_val,
      QRegister.embedMatrix_apply_of_agreeOutside] at hmR
    have hsymm : (basisBitsEquiv n).symm (basisBits n m) = m :=
      (basisBitsEquiv n).symm_apply_apply m
    rw [hsymm] at hmR
    have hag : (rCore.concat rPGTwist hCP).AgreeOutside k m := by
      by_contra hna
      simp only [hna, ↓reduceIte, mul_zero, ne_eq, not_true_eq_false] at hmR
    have hnot : ∀ idx : Fin JunctionPrefixPruned220.mWork45, rWork idx ∉ Set.range (rCore.concat
      rPGTwist hCP).wires := by
      intro idx hm_in
      have hm_img : rWork idx ∈ (rCore.concat rPGTwist hCP).image := by
        rcases hm_in with ⟨j, hj⟩; exact (QRegister.mem_image _ _).mpr ⟨j, hj⟩
      rw [qreg_image_concat] at hm_img
      rcases Finset.mem_union.mp hm_img with hC | hP
      · exact Finset.disjoint_left.mp (QRegExt.disjointWires_to_finset hCW) hC ((QRegister.mem_image
          rWork _).mpr ⟨idx, rfl⟩)
      · exact Finset.disjoint_left.mp (QRegExt.disjointWires_to_finset hPW) hP ((QRegister.mem_image
          rWork _).mpr ⟨idx, rfl⟩)
    exact ⟨(hag _ (hnot 2)).trans hm2, (hag _ (hnot 3)).trans hm3, (hag _ (hnot 4)).trans hm4,
      (hag _ (hnot 5)).trans hm5, (hag _ (hnot 6)).trans hm6⟩
theorem condStageSpec_projAxis3D_pos45 {mPayload : ℕ} (isInv : Bool)
    {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    (o1 l1 o2 l2 : ℕ) (hw1 : o1 + l1 ≤ JunctionPrefixPruned220.mWork45)
    (hw2 : o2 + l2 ≤ JunctionPrefixPruned220.mWork45)
    (rCore : QRegister (fullSysCoreWires mPayload) n)
    (rPGTwist : QRegister 48 n) (rWork : QRegister JunctionPrefixPruned220.mWork45 n)
    (hCP : rCore.DisjointWires rPGTwist) (hCW : rCore.DisjointWires rWork)
    (H : BitAssignment n → Prop) (uCore : Unitary (2 ^ fullSysCoreWires mPayload))
    (uLoc : Unitary 256) (d3D : DynamicCircuit Var n)
    (huCore : rCore.embedUnitary uCore =
      (rProjAxis rCore 0).embedUnitary uLoc *
        ((rProjAxis rCore 1).embedUnitary uLoc * (rProjAxis rCore 2).embedUnitary uLoc))
    (hwWp : CleanUnitaryWp (rWork.slice o2 l2 hw2)
      (if isInv then (rCore.embedUnitary uCore)⁻¹ else rCore.embedUnitary uCore) d3D) :
    CondStageSpec (rCore.concat rPGTwist hCP) (rWork.slice o2 l2 hw2)
      ((rHigh rCore).image ∪ (rWork.slice o1 l1 hw1).image) H
      (if isInv then ((rCoreBlock48 mPayload).embedUnitary uCore)⁻¹
       else (rCoreBlock48 mPayload).embedUnitary uCore) d3D := by
  let U_act := if isInv then (rCore.embedUnitary uCore)⁻¹ else rCore.embedUnitary uCore
  let S_all := ((rHigh rCore).image ∪ (rWork.slice o1 l1 hw1).image) ∪ (rWork.slice o2 l2 hw2).image
  have hNotAx : ∀ u ∈ S_all, ∀ w : Fin 3, u ∉ Set.range (rProjAxis rCore w).wires := by
    rintro u hu w ⟨i, rfl⟩
    have hAx : rProjAxis rCore w i ∈ rCore.image :=
      rProjAxis_sub_rCore rCore w ((QRegister.mem_image _ _).mpr ⟨i, rfl⟩)
    rcases Finset.mem_union.mp hu with hH1 | hW2
    · rcases Finset.mem_union.mp hH1 with hH | hW1
      · rcases (QRegister.mem_image (rHigh rCore) _).mp hH with ⟨j, hj⟩
        have hv := congrArg Fin.val (rCore.wires.injective hj)
        have hlt := rProjAxis_wire_lt_3948 (mPayload := mPayload) w i
        change 3948 + j.val = (rProjAxis (QRegExt.idReg _) w i).val at hv
        omega
      · exact Finset.disjoint_left.mp (QRegExt.disjointWires_to_finset hCW) hAx
          (QRegister.image_compose_subset rWork _ hW1)
    · exact Finset.disjoint_left.mp (QRegExt.disjointWires_to_finset hCW) hAx
        (QRegister.image_compose_subset rWork _ hW2)
  have hD1 : ∀ (w : Fin 3) (V : Unitary 256), DiagOn S_all ((rProjAxis rCore w).embedUnitary V).1 :=
    by
    intro w V i j hne s hs
    rw [QRegister.embedUnitary_val, QRegister.embedMatrix_apply_of_agreeOutside] at hne
    have hag : (rProjAxis rCore w).AgreeOutside i j := by
      by_contra hna
      simp only [hna, ↓reduceIte, mul_zero, ne_eq, not_true_eq_false] at hne
    exact hag s (hNotAx s hs w)
  have hDiagU : DiagOn S_all U_act.1 := by
    cases isInv
    · dsimp only [U_act, Bool.false_eq_true, ↓reduceIte]
      rw [huCore]
      exact (hD1 0 uLoc).mul ((hD1 1 uLoc).mul (hD1 2 uLoc))
    · have heq : (rCore.embedUnitary uCore)⁻¹ =
          (rProjAxis rCore 2).embedUnitary uLoc⁻¹ *
            ((rProjAxis rCore 1).embedUnitary uLoc⁻¹ * (rProjAxis rCore 0).embedUnitary uLoc⁻¹) :=
              by
        rw [huCore]
        simp only [_root_.mul_inv_rev, ← QRegister.embedUnitary_inv, mul_assoc]
      dsimp only [U_act, ↓reduceIte]
      rw [heq]
      exact (hD1 2 uLoc⁻¹).mul ((hD1 1 uLoc⁻¹).mul (hD1 0 uLoc⁻¹))
  refine ⟨⟨U_act, hwWp, hDiagU, fun ξ _ _ ↦ ?_⟩⟩
  cases isInv
  · simp only [U_act, Bool.false_eq_true, ↓reduceIte, ← QRegister.embedUnitary_compose,
      compose_rCoreBlock48_eq rCore rPGTwist hCP]
  · simp only [U_act, ↓reduceIte, ← QRegister.embedUnitary_inv, ← QRegister.embedUnitary_compose,
      compose_rCoreBlock48_eq rCore rPGTwist hCP]
theorem dTail_3D_spec_Pos45 {mPayload : ℕ} (isInv : Bool)
    {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    (rCore : QRegister (fullSysCoreWires mPayload) n)
    (rPGTwist : QRegister 48 n) (rWork : QRegister JunctionPrefixPruned220.mWork45 n)
    (hCP : rCore.DisjointWires rPGTwist) (hCW : rCore.DisjointWires rWork) :
    CondStageSpec (rCore.concat rPGTwist hCP) (rWork.slice 2 43 mw_slice_2_43_le_Pos45)
      ((rHigh rCore).image ∪ (rWork.slice 0 2 mw_slice_0_2_le_Pos45).image)
      (HPosBranchFlag_Pos45 rCore rWork)
      (if isInv then ((rCoreBlock48 mPayload).embedUnitary uTail3DCore)⁻¹
       else (rCoreBlock48 mPayload).embedUnitary uTail3DCore)
      (dTail_3D isInv (Var := Var) rCore) :=
  condStageSpec_projAxis3D_pos45 isInv 0 2 2 43 mw_slice_0_2_le_Pos45 mw_slice_2_43_le_Pos45
    rCore rPGTwist rWork hCP hCW _ uTail3DCore uTailLocal8 (dTail_3D isInv rCore)
    (by
      unfold uTail3DCore
      simp only [QRegister.embedUnitary_mul, ← QRegister.embedUnitary_compose]
      rfl)
    (by
      cases isInv
      · dsimp only [dTail_3D, Bool.false_eq_true, ↓reduceIte]
        rw [← cTail_3D_eval]
        exact FusedVepCore288.CleanUnitaryWp.circuit _ (cTail_3D rCore)
      · dsimp only [dTail_3D, ↓reduceIte]
        rw [← cTail_3D_eval, ← Circuit.eval_inverse]
        exact FusedVepCore288.CleanUnitaryWp.circuit _ (cTail_3D rCore).inverse)
theorem embed_uWhStg7Cat_rCoreSwap_ket_Pos45 {mPayload n : ℕ} (hm : 22 ≤ mPayload)
    (isInv : Bool) (rCore : QRegister (fullSysCoreWires mPayload) n)
    (rPGTwist : QRegister 48 n) (rWork : QRegister JunctionPrefixPruned220.mWork45 n)
    (hCP : rCore.DisjointWires rPGTwist) (hCW : rCore.DisjointWires rWork)
    (hPW : rPGTwist.DisjointWires rWork) {η : BitAssignment n}
    (hw : SwapWorkBits_Pos45 rWork η) : (((rCoreSwap_Pos45 hm rCore rWork hCW).concat rPGTwist
    (rCoreSwap_disj_rPGTwist_Pos45 hm rCore rPGTwist rWork hCP hCW hPW)).embedUnitary
    (uWhStg7Cat hm isInv)).1.mulVec (basisKet η) = ((rCore.concat rPGTwist hCP).embedUnitary
    (uWhStg7CutCat hm isInv)).1.mulVec (basisKet η) := by
  unfold uWhStg7Cat uWhStg7CutCat
  exact embed_dyadicDiag_rCoreSwap_ket_Pos45 hm (whStg7Exp hm isInv) rCore rPGTwist rWork hCP hCW
    hPW hw
theorem embed_uWhStgCat_rCoreSwap_ket_Pos45 {mPayload n : ℕ} (hm : 22 ≤ mPayload) (k : Fin 7)
    (isInv : Bool) (rCore : QRegister (fullSysCoreWires mPayload) n)
    (rPGTwist : QRegister 48 n) (rWork : QRegister JunctionPrefixPruned220.mWork45 n)
    (hCP : rCore.DisjointWires rPGTwist) (hCW : rCore.DisjointWires rWork)
    (hPW : rPGTwist.DisjointWires rWork) {η : BitAssignment n}
    (hw : SwapWorkBits_Pos45 rWork η) : (((rCoreSwap_Pos45 hm rCore rWork hCW).concat rPGTwist
    (rCoreSwap_disj_rPGTwist_Pos45 hm rCore rPGTwist rWork hCP hCW hPW)).embedUnitary
    (uWhStgCat hm k isInv)).1.mulVec (basisKet η) = ((rCore.concat rPGTwist hCP).embedUnitary
    (uWhStgCutCat hm k isInv)).1.mulVec (basisKet η) := by
  unfold uWhStgCat uWhStgCutCat
  simp only [QRegister.embedUnitary_mul, Submonoid.coe_mul, ← Matrix.mulVec_mulVec]
  rw [embed_dyadicDiag_rCoreSwap_ket_Pos45 hm (whStgTopExp hm k isInv) rCore rPGTwist rWork hCP hCW
    hPW hw]
  change (((rCoreSwap_Pos45 hm rCore rWork hCW).concat rPGTwist _).embedUnitary _).1.mulVec
    (((rCore.concat rPGTwist hCP).embedUnitary
      ((rCoreBlock48 mPayload).embedUnitary
        (DyadicQft64.dyadicDiagUnitary _ 48 (whStgTopExpCoin0 hm k isInv)))).1.mulVec (basisKet
          η)) = _
  rw [← QRegister.embedUnitary_compose, compose_rCoreBlock48_eq rCore rPGTwist hCP,
    embedUnitary_diagonal_mulVec_basisKet rCore _ _ rfl η,
    Matrix.mulVec_smul, Matrix.mulVec_smul]
  exact congrArg (_ • ·) (embed_uApexShift45_rCoreSwap_ket_Pos45 hm (7 - k.val) (by omega)
    (whStgLowShift hm k isInv) rCore rPGTwist rWork hCP hCW hPW hw)
theorem embed_uWhRemCat_rCoreSwap_ket_Pos45 {mPayload n : ℕ} (hm : 22 ≤ mPayload)
    (isInv : Bool) (rCore : QRegister (fullSysCoreWires mPayload) n)
    (rPGTwist : QRegister 48 n) (rWork : QRegister JunctionPrefixPruned220.mWork45 n)
    (hCP : rCore.DisjointWires rPGTwist) (hCW : rCore.DisjointWires rWork)
    (hPW : rPGTwist.DisjointWires rWork) {η : BitAssignment n}
    (hw : SwapWorkBits_Pos45 rWork η) : (((rCoreSwap_Pos45 hm rCore rWork hCW).concat rPGTwist
    (rCoreSwap_disj_rPGTwist_Pos45 hm rCore rPGTwist rWork hCP hCW hPW)).embedUnitary
    (uWhRemCat hm isInv)).1.mulVec (basisKet η) = ((rCore.concat rPGTwist hCP).embedUnitary
    (uWhRemCat hm isInv)).1.mulVec (basisKet η) := by
  have hTopEq : (fun γ ↦ whRemTopExp hm isInv (setHighNucBits hm γ)) = whRemTopExp hm isInv :=
    funext (whRemTopExp_setHighNucBits hm isInv)
  have hLowEq : (fun γ ↦ whRemLowShift hm isInv (setHighNucBits hm γ)) = whRemLowShift hm isInv :=
    funext (whRemLowShift_setHighNucBits hm isInv)
  unfold uWhRemCat
  simp only [QRegister.embedUnitary_mul, Submonoid.coe_mul, ← Matrix.mulVec_mulVec]
  rw [embed_dyadicDiag_rCoreSwap_ket_Pos45 hm (whRemTopExp hm isInv) rCore rPGTwist rWork hCP hCW
    hPW hw,
    hTopEq]
  change (((rCoreSwap_Pos45 hm rCore rWork hCW).concat rPGTwist _).embedUnitary _).1.mulVec
    (((rCore.concat rPGTwist hCP).embedUnitary ((rCoreBlock48 mPayload).embedUnitary
    (DyadicQft64.dyadicDiagUnitary _ 48 (whRemTopExp hm isInv)))).1.mulVec (basisKet η)) = _
  rw [← QRegister.embedUnitary_compose, compose_rCoreBlock48_eq rCore rPGTwist hCP,
    embedUnitary_diagonal_mulVec_basisKet rCore _ _ rfl η,
    Matrix.mulVec_smul, Matrix.mulVec_smul]
  rw [embed_uApexShift45_rCoreSwap_ket_Pos45 hm 7 (by decide) (whRemLowShift hm isInv)
    rCore rPGTwist rWork hCP hCW hPW hw, hLowEq]
theorem hslot_ne_work_idx_Pos45 {mPayload n : ℕ} {u : Wire n}
    (rCore : QRegister (fullSysCoreWires mPayload) n) (hu : u ∈ (rHigh rCore).image)
    (rWork : QRegister JunctionPrefixPruned220.mWork45 n) (hCW : rCore.DisjointWires rWork)
    (i : Fin JunctionPrefixPruned220.mWork45) : u ≠ rWork i := fun h ↦ Finset.disjoint_left.mp
    (QRegExt.disjointWires_to_finset hCW) (rHigh_sub_rCore rCore hu) ((QRegister.mem_image rWork
      _).mpr ⟨i, h.symm⟩)
theorem dHUncond_3D_spec_Pos45 {mPayload : ℕ} (isInv : Bool) (hm : 22 ≤ mPayload) (m : Fin 8)
    {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    (rCore : QRegister (fullSysCoreWires mPayload) n)
    (rPGTwist : QRegister 48 n) (rWork : QRegister JunctionPrefixPruned220.mWork45 n)
    (hCP : rCore.DisjointWires rPGTwist) (hCW : rCore.DisjointWires rWork) :
    CondStageSpec (rCore.concat rPGTwist hCP) (rWork.slice 7 38 mw_slice_7_38_le_Pos45)
      ((rHigh rCore).image ∪ (rWork.slice 0 7 mw_slice_0_7_le_Pos45).image)
      (JunctionPrefixPruned220.HProjFlag hm rCore rWork)
      (if isInv then ((rCoreBlock48 mPayload).embedUnitary (uHad3DCore m))⁻¹
       else (rCoreBlock48 mPayload).embedUnitary (uHad3DCore m))
      (dHUncond_3D isInv m (Var := Var) rCore) :=
  condStageSpec_projAxis3D_pos45 isInv 0 7 7 38 mw_slice_0_7_le_Pos45 mw_slice_7_38_le_Pos45
    rCore rPGTwist rWork hCP hCW _ (uHad3DCore m) (wireHadamard8 m) (dHUncond_3D isInv m rCore)
    (by
      unfold uHad3DCore
      simp only [QRegister.embedUnitary_mul, ← QRegister.embedUnitary_compose]
      rfl)
    (by
      cases isInv
      · dsimp only [dHUncond_3D, Bool.false_eq_true, ↓reduceIte]
        rw [← cH_3D_eval]
        exact FusedVepCore288.CleanUnitaryWp.circuit _ (cH_3D rCore m)
      · dsimp only [dHUncond_3D, ↓reduceIte]
        rw [← cH_3D_eval, ← Circuit.eval_inverse]
        exact FusedVepCore288.CleanUnitaryWp.circuit _ (cH_3D rCore m).inverse)
theorem embed_uHad3DCore_rCoreSwap_eq_Pos45 {mPayload n : ℕ} (hm : 22 ≤ mPayload) (m : Fin 8)
    (rCore : QRegister (fullSysCoreWires mPayload) n) (rPGTwist : QRegister 48 n)
    (rWork : QRegister JunctionPrefixPruned220.mWork45 n) (hCP : rCore.DisjointWires rPGTwist)
    (hCW : rCore.DisjointWires rWork) (hPW : rPGTwist.DisjointWires rWork) : ((rCoreSwap_Pos45
    hm rCore rWork hCW).concat rPGTwist (rCoreSwap_disj_rPGTwist_Pos45 hm rCore rPGTwist rWork
    hCP hCW hPW)).embedUnitary ((rCoreBlock48 mPayload).embedUnitary (uHad3DCore m)) =
    (rCore.concat rPGTwist hCP).embedUnitary
    ((rCoreBlock48 mPayload).embedUnitary (uHad3DCore m)) := by
  let rCS := rCoreSwap_Pos45 hm rCore rWork hCW
  let hCSP := rCoreSwap_disj_rPGTwist_Pos45 hm rCore rPGTwist rWork hCP hCW hPW
  rw [← QRegister.embedUnitary_compose, ← QRegister.embedUnitary_compose,
    compose_rCoreBlock48_eq rCS rPGTwist hCSP, compose_rCoreBlock48_eq rCore rPGTwist hCP]
  unfold uHad3DCore
  simp only [QRegister.embedUnitary_mul, ← QRegister.embedUnitary_compose]
  have hAx : ∀ w : Fin 3,
      rCS.compose (rProjAxis (QRegExt.idReg (fullSysCoreWires mPayload)) w) =
        rCore.compose (rProjAxis (QRegExt.idReg (fullSysCoreWires mPayload)) w) := by
    intro w
    ext i
    change (rProjAxis rCS w i).val = (rProjAxis rCore w i).val
    rw [rProjAxis_rCoreSwap_eq_Pos45 hm rCore rWork hCW w]
  rw [hAx 0, hAx 1, hAx 2]
theorem embed_uHad3DCore_rCoreSwap_ket_Pos45 {mPayload n : ℕ} (hm : 22 ≤ mPayload) (m : Fin 8)
    (rCore : QRegister (fullSysCoreWires mPayload) n) (rPGTwist : QRegister 48 n)
    (rWork : QRegister JunctionPrefixPruned220.mWork45 n) (hCP : rCore.DisjointWires rPGTwist)
    (hCW : rCore.DisjointWires rWork) (hPW : rPGTwist.DisjointWires rWork)
    (η : BitAssignment n) : (((rCoreSwap_Pos45 hm rCore rWork hCW).concat rPGTwist
    (rCoreSwap_disj_rPGTwist_Pos45 hm rCore rPGTwist rWork hCP hCW hPW)).embedUnitary
    ((rCoreBlock48 mPayload).embedUnitary (uHad3DCore m))).1.mulVec (basisKet η) =
    ((rCore.concat rPGTwist hCP).embedUnitary ((rCoreBlock48 mPayload).embedUnitary
    (uHad3DCore m))).1.mulVec (basisKet η) := by
  rw [embed_uHad3DCore_rCoreSwap_eq_Pos45 hm m rCore rPGTwist rWork hCP hCW hPW]
theorem embed_uProj3DVepHadPre16Cat_rCoreSwap_ket_Pos45 {mPayload n : ℕ} (isInv : Bool)
    (hm : 22 ≤ mPayload) (rCore : QRegister (fullSysCoreWires mPayload) n)
    (rPGTwist : QRegister 48 n) (rWork : QRegister JunctionPrefixPruned220.mWork45 n)
    (hCP : rCore.DisjointWires rPGTwist) (hCW : rCore.DisjointWires rWork)
    (hPW : rPGTwist.DisjointWires rWork) {η : BitAssignment n}
    (hw : SwapWorkBits_Pos45 rWork η) : (((rCoreSwap_Pos45 hm rCore rWork hCW).concat rPGTwist
    (rCoreSwap_disj_rPGTwist_Pos45 hm rCore rPGTwist rWork hCP hCW hPW)).embedUnitary (if
    isInv then (uProj3DVepHadPre16Cat hm)⁻¹ else uProj3DVepHadPre16Cat hm)).1.mulVec
    (basisKet η) = ((rCore.concat rPGTwist hCP).embedUnitary (if isInv then
    (uProj3DHadCutPre16Cat hm)⁻¹ else uProj3DHadCutPre16Cat hm)).1.mulVec (basisKet η) := by
  have hSupp0 : ∀ k : Fin (2 ^ n), (basisKet η) k ≠ 0 → SwapWorkBits_Pos45 rWork (basisBits n k) :=
    by
    intro k hne
    rw [Proj3DCut.basisKet_eq_single] at hne
    have hk : k = (basisBitsEquiv n).symm η := by by_contra h; simp [h] at hne
    subst hk
    rw [basisBits_basisBitsEquiv_symm_eq]
    exact hw
  have h7Step (b : Bool) (ζ : BitAssignment n) (hζ : SwapWorkBits_Pos45 rWork ζ) :=
    embed_uWhStg7Cat_rCoreSwap_ket_Pos45 hm b rCore rPGTwist rWork hCP hCW hPW (η := ζ) hζ
  have hStgStep (k : Fin 7) (b : Bool) (ζ : BitAssignment n) (hζ : SwapWorkBits_Pos45 rWork ζ) :=
    embed_uWhStgCat_rCoreSwap_ket_Pos45 hm k b rCore rPGTwist rWork hCP hCW hPW (η := ζ) hζ
  have hRemStep (b : Bool) (ζ : BitAssignment n) (hζ : SwapWorkBits_Pos45 rWork ζ) :=
    embed_uWhRemCat_rCoreSwap_ket_Pos45 hm b rCore rPGTwist rWork hCP hCW hPW (η := ζ) hζ
  have hHStep (m : Fin 8) (ζ : BitAssignment n) (_ : SwapWorkBits_Pos45 rWork ζ) :=
    embed_uHad3DCore_rCoreSwap_ket_Pos45 hm m rCore rPGTwist rWork hCP hCW hPW ζ
  cases isInv
  · simp only [Bool.false_eq_true, ↓reduceIte, uProj3DVepHadPre16Cat, uProj3DHadCutPre16Cat,
      QRegister.embedUnitary_mul, Submonoid.coe_mul, ← Matrix.mulVec_mulVec]
    obtain ⟨e1, s1⟩ := mulVec_chain_rCoreSwap_step_Pos45 hm rCore rPGTwist rWork hCP hCW hPW (h7Step
      false) rfl hSupp0
    obtain ⟨e2, s2⟩ := mulVec_chain_rCoreSwap_step_Pos45 hm rCore rPGTwist rWork hCP hCW hPW (hHStep
      7) e1 s1
    obtain ⟨e3, s3⟩ := mulVec_chain_rCoreSwap_step_Pos45 hm rCore rPGTwist rWork hCP hCW hPW
      (hStgStep 6 false) e2 s2
    obtain ⟨e4, s4⟩ := mulVec_chain_rCoreSwap_step_Pos45 hm rCore rPGTwist rWork hCP hCW hPW (hHStep
      6) e3 s3
    obtain ⟨e5, s5⟩ := mulVec_chain_rCoreSwap_step_Pos45 hm rCore rPGTwist rWork hCP hCW hPW
      (hStgStep 5 false) e4 s4
    obtain ⟨e6, s6⟩ := mulVec_chain_rCoreSwap_step_Pos45 hm rCore rPGTwist rWork hCP hCW hPW (hHStep
      5) e5 s5
    obtain ⟨e7, s7⟩ := mulVec_chain_rCoreSwap_step_Pos45 hm rCore rPGTwist rWork hCP hCW hPW
      (hStgStep 4 false) e6 s6
    obtain ⟨e8, s8⟩ := mulVec_chain_rCoreSwap_step_Pos45 hm rCore rPGTwist rWork hCP hCW hPW (hHStep
      4) e7 s7
    obtain ⟨e9, s9⟩ := mulVec_chain_rCoreSwap_step_Pos45 hm rCore rPGTwist rWork hCP hCW hPW
      (hStgStep 3 false) e8 s8
    obtain ⟨e10, s10⟩ := mulVec_chain_rCoreSwap_step_Pos45 hm rCore rPGTwist rWork hCP hCW hPW
      (hHStep 3) e9 s9
    obtain ⟨e11, s11⟩ := mulVec_chain_rCoreSwap_step_Pos45 hm rCore rPGTwist rWork hCP hCW hPW
      (hStgStep 2 false) e10 s10
    obtain ⟨e12, s12⟩ := mulVec_chain_rCoreSwap_step_Pos45 hm rCore rPGTwist rWork hCP hCW hPW
      (hHStep 2) e11 s11
    obtain ⟨e13, s13⟩ := mulVec_chain_rCoreSwap_step_Pos45 hm rCore rPGTwist rWork hCP hCW hPW
      (hStgStep 1 false) e12 s12
    obtain ⟨e14, s14⟩ := mulVec_chain_rCoreSwap_step_Pos45 hm rCore rPGTwist rWork hCP hCW hPW
      (hHStep 1) e13 s13
    obtain ⟨e15, s15⟩ := mulVec_chain_rCoreSwap_step_Pos45 hm rCore rPGTwist rWork hCP hCW hPW
      (hStgStep 0 false) e14 s14
    exact (mulVec_chain_rCoreSwap_step_Pos45 hm rCore rPGTwist rWork hCP hCW hPW (hRemStep false)
      e15 s15).1
  · have hH_inv : ∀ m : Fin 8, ((rCoreBlock48 mPayload).embedUnitary (uHad3DCore m))⁻¹ =
      (rCoreBlock48 mPayload).embedUnitary (uHad3DCore m) := by
      intro m
      rw [← QRegister.embedUnitary_inv, uHad3DCore_inv hm m]
    simp only [↓reduceIte, uProj3DVepHadPre16Cat, uProj3DHadCutPre16Cat, _root_.mul_inv_rev,
      uWhStg7Cat_inv_eq, uWhStg7CutCat_inv_eq, uWhStgCat_inv_eq, uWhStgCutCat_inv_eq,
      uWhRemCat_inv_eq, hH_inv,
      QRegister.embedUnitary_mul, Submonoid.coe_mul, ← Matrix.mulVec_mulVec]
    obtain ⟨e1, s1⟩ := mulVec_chain_rCoreSwap_step_Pos45 hm rCore rPGTwist rWork hCP hCW hPW
      (hRemStep true) rfl hSupp0
    obtain ⟨e2, s2⟩ := mulVec_chain_rCoreSwap_step_Pos45 hm rCore rPGTwist rWork hCP hCW hPW
      (hStgStep 0 true) e1 s1
    obtain ⟨e3, s3⟩ := mulVec_chain_rCoreSwap_step_Pos45 hm rCore rPGTwist rWork hCP hCW hPW (hHStep
      1) e2 s2
    obtain ⟨e4, s4⟩ := mulVec_chain_rCoreSwap_step_Pos45 hm rCore rPGTwist rWork hCP hCW hPW
      (hStgStep 1 true) e3 s3
    obtain ⟨e5, s5⟩ := mulVec_chain_rCoreSwap_step_Pos45 hm rCore rPGTwist rWork hCP hCW hPW (hHStep
      2) e4 s4
    obtain ⟨e6, s6⟩ := mulVec_chain_rCoreSwap_step_Pos45 hm rCore rPGTwist rWork hCP hCW hPW
      (hStgStep 2 true) e5 s5
    obtain ⟨e7, s7⟩ := mulVec_chain_rCoreSwap_step_Pos45 hm rCore rPGTwist rWork hCP hCW hPW (hHStep
      3) e6 s6
    obtain ⟨e8, s8⟩ := mulVec_chain_rCoreSwap_step_Pos45 hm rCore rPGTwist rWork hCP hCW hPW
      (hStgStep 3 true) e7 s7
    obtain ⟨e9, s9⟩ := mulVec_chain_rCoreSwap_step_Pos45 hm rCore rPGTwist rWork hCP hCW hPW (hHStep
      4) e8 s8
    obtain ⟨e10, s10⟩ := mulVec_chain_rCoreSwap_step_Pos45 hm rCore rPGTwist rWork hCP hCW hPW
      (hStgStep 4 true) e9 s9
    obtain ⟨e11, s11⟩ := mulVec_chain_rCoreSwap_step_Pos45 hm rCore rPGTwist rWork hCP hCW hPW
      (hHStep 5) e10 s10
    obtain ⟨e12, s12⟩ := mulVec_chain_rCoreSwap_step_Pos45 hm rCore rPGTwist rWork hCP hCW hPW
      (hStgStep 5 true) e11 s11
    obtain ⟨e13, s13⟩ := mulVec_chain_rCoreSwap_step_Pos45 hm rCore rPGTwist rWork hCP hCW hPW
      (hHStep 6) e12 s12
    obtain ⟨e14, s14⟩ := mulVec_chain_rCoreSwap_step_Pos45 hm rCore rPGTwist rWork hCP hCW hPW
      (hStgStep 6 true) e13 s13
    obtain ⟨e15, s15⟩ := mulVec_chain_rCoreSwap_step_Pos45 hm rCore rPGTwist rWork hCP hCW hPW
      (hHStep 7) e14 s14
    exact (mulVec_chain_rCoreSwap_step_Pos45 hm rCore rPGTwist rWork hCP hCW hPW (h7Step true) e15
      s15).1
lemma genBoolBit_true_true_true_val_int (q p : ZMod 2) :
    ((genBoolBit true true true q p).val : ℤ) =
      (1 - (q.val : ℤ)) * (p.val : ℤ) + (q.val : ℤ) := by
  rcases JunctionApexCSA288.zmod2_eq_zero_or_one q with rfl | rfl <;>
    rcases JunctionApexCSA288.zmod2_eq_zero_or_one p with rfl | rfl <;> decide
lemma zmod2_add_one_val_int (b : ZMod 2) : ((b + 1).val : ℤ) = 1 - (b.val : ℤ) := by
  rcases JunctionApexCSA288.zmod2_eq_zero_or_one b with rfl | rfl <;> decide
lemma apexCarryPhase_seven_even {n : ℕ} (rT7 : QRegister 7 n) (ξ : BitAssignment n) (d₆ e : ℤ)
    : apexCarryPhase rT7 ξ (2 * d₆ + 128 * e) = apexCarryPhase (rT7.slice 1 6 (by decide)) ξ
    d₆ * DyadicQft64.dyadicTurn 48 ((2 ^ 45 : ℤ) * e) := by
  let rT6 := rT7.slice 1 6 (by decide)
  have hsp : regVal rT7 ξ = (ξ (rT7 0)).val + 2 * regVal rT6 ξ := regVal_succ rT7 ξ
  have hb0 : (ξ (rT7 0)).val < 2 := ZMod.val_lt _
  have hdiv : ((regVal rT7 ξ : ℤ) + (2 * d₆ + 128 * e)) / (2 ^ 7 : ℤ) =
      ((regVal rT6 ξ : ℤ) + d₆) / (2 ^ 6 : ℤ) + e := by
    rw [hsp]
    push_cast
    omega
  have h48 : DyadicQft64.dyadicTurn 48 ((2 ^ 45 : ℤ) * e) = DyadicQft64.dyadicTurn 3 e :=
    JunctionApexCSA288.dyadicTurn_scale_pow 45 3 e
  unfold apexCarryPhase
  rw [hdiv, h48, DyadicQft64.dyadicTurn_add]
lemma shiftRegInt_seven_even {n : ℕ} (rT7 : QRegister 7 n) (ξ : BitAssignment n) (d₆ e : ℤ) :
    shiftRegInt rT7 ξ (2 * d₆ + 128 * e) = shiftRegInt (rT7.slice 1 6 (by decide)) ξ d₆ := by
  let rT6 := rT7.slice 1 6 (by decide)
  have hT6_sub : rT6.image ⊆ rT7.image := QRegister.image_compose_subset rT7 _
  have h0_not : rT7 0 ∉ rT6.image := qreg_zero_not_mem_tail rT7
  symm
  apply eq_shiftRegInt_of_outside_and_regVal rT7 (shiftRegInt rT6 ξ d₆) ξ (2 * d₆ + 128 * e)
  · intro w hw
    exact shiftRegInt_outside rT6 ξ d₆ (fun hm ↦ hw (hT6_sub hm))
  · rw [regVal_succ rT7 (shiftRegInt rT6 ξ d₆), shiftRegInt_outside rT6 ξ d₆ h0_not]
    have hT6_eq : (rT7.slice 1 6 (by decide)) = rT6 := rfl
    rw [hT6_eq, regVal_shiftRegInt rT6 ξ d₆]
    have hsp : regVal rT7 ξ = (ξ (rT7 0)).val + 2 * regVal rT6 ξ := regVal_succ rT7 ξ
    have hb0 : (ξ (rT7 0)).val < 2 := ZMod.val_lt _
    zify
    rw [intModFinPow2_coe, intModFinPow2_coe, hsp]
    push_cast
    omega
theorem uApexShift45_seven_of_two_mul_add {mPayload : ℕ}
    (δ₆ e : BitAssignment (fullSysCoreWires mPayload) → ℤ) :
    uApexShift45 (fullSysCoreWires mPayload) 7 (by decide) (fun γ ↦ 2 * δ₆ γ + 128 * e γ) =
      uApexShift45 (fullSysCoreWires mPayload) 6 (by decide) δ₆ *
        (rCoreBlock48 mPayload).embedUnitary
          (DyadicQft64.dyadicDiagUnitary (fullSysCoreWires mPayload) 48 (fun γ ↦ (2 ^ 45 : ℤ) *
            e γ)) := by
  let kSys := fullSysCoreWires mPayload
  let rSys0 : QRegister kSys (kSys + 48) := rCoreBlock48 mPayload
  let rCat0 : QRegister 48 (kSys + 48) := QRegister.block kSys 48 le_rfl
  have hdisj : rSys0.DisjointWires rCat0 :=
    QRegister.block_disjoint_of_le 0 kSys kSys 48 (by omega) le_rfl (by omega)
  have hconcat : rSys0.concat rCat0 hdisj = QRegExt.idReg (kSys + 48) := by
    apply qreg_ext; intro i
    by_cases hi : i.val < kSys
    · have h1 : i = Fin.castAdd 48 ⟨i.val, hi⟩ := Fin.ext rfl
      rw [h1, QRegister.concat_apply_left]
      exact Fin.ext (by simp [rSys0, rCoreBlock48, QRegExt.idReg])
    · have h2 : i = Fin.natAdd kSys ⟨i.val - kSys, by have := i.isLt; omega⟩ :=
        Fin.ext (by dsimp; omega)
      rw [h2, QRegister.concat_apply_right]
      exact Fin.ext (by simp [rCat0, QRegExt.idReg])
  apply Subtype.ext; apply matrix_ext_basisKet; intro ξ
  have hL := embed_uApexShift45_mulVec_basisKet (by decide : 7 ≤ 45) rSys0 rCat0 hdisj
    (fun γ ↦ 2 * δ₆ γ + 128 * e γ) ξ
  have hR6 := embed_uApexShift45_mulVec_basisKet (by decide : 6 ≤ 45) rSys0 rCat0 hdisj δ₆ ξ
  rw [hconcat, embedUnitary_idReg_eq] at hL hR6
  rw [hL, Submonoid.coe_mul, ← Matrix.mulVec_mulVec,
    embedUnitary_dyadicDiagUnitary_mulVec_basisKet, Matrix.mulVec_smul, hR6, smul_smul]
  have hSl : (rCat0.slice (45 - 7) 7 (by decide)).slice 1 6 (by decide) =
      rCat0.slice (45 - 6) 6 (by decide) := by
    apply QRegister.ext; apply Function.Embedding.ext; intro j
    rw [slice_apply_eq, slice_apply_eq, slice_apply_eq]
    congr 1; ext; dsimp; omega
  rw [apexCarryPhase_seven_even (rCat0.slice (45 - 7) 7 (by decide)) ξ,
    shiftRegInt_seven_even (rCat0.slice (45 - 7) 7 (by decide)) ξ, hSl, mul_comm]
def whStg0RemOrVal {mPayload : ℕ} (hm : 22 ≤ mPayload) (w : Fin 3)
    (γ : BitAssignment (fullSysCoreWires mPayload)) : ℤ :=
  let rId := QRegExt.idReg (fullSysCoreWires mPayload)
  let q_w : ℤ := wfBitVal hm γ * ((γ (rProjAxis rId w 0)).val : ℤ)
  (1 - q_w) * ((γ (rProjAxis rId w 2)).val : ℤ) + q_w
def whStg0RemLowShift6 {mPayload : ℕ} (hm : 22 ≤ mPayload) (isInv : Bool)
    (γ : BitAssignment (fullSysCoreWires mPayload)) : ℤ :=
  let sgn : ℤ := if isInv then -1 else 1
  let rId := QRegExt.idReg (fullSysCoreWires mPayload)
  (-sgn) *
    ∑ w : Fin 3,
      (1 - wfBitVal hm γ * ((γ (rProjAxis rId w 0)).val : ℤ)) *
        (regVal ((rWhFull hm rId w).slice 0 6 (by decide)) γ : ℤ)
lemma whStg0_add_whRem_lowShift_eq {mPayload : ℕ} (hm : 22 ≤ mPayload) (isInv : Bool)
    (γ : BitAssignment (fullSysCoreWires mPayload)) : whStgLowShift hm 0 isInv γ +
    whRemLowShift hm isInv γ = 2 * whStg0RemLowShift6 hm isInv γ + 128 * ((if (!isInv) then
    (-1 : ℤ) else 1) * (whStg0RemOrVal hm 0 γ + whStg0RemOrVal hm 1 γ + whStg0RemOrVal hm 2
    γ)) := by
  let rId := QRegExt.idReg (fullSysCoreWires mPayload)
  have hsp0 := regVal_rWhFull_split_top hm rId 0 1 γ
  have hsp1 := regVal_rWhFull_split_top hm rId 1 1 γ
  have hsp2 := regVal_rWhFull_split_top hm rId 2 1 γ
  have htop : ∀ w : Fin 3,
      rWhFull hm rId w ⟨7 - (1 : Fin 7).val, by decide⟩ = rProjAxis rId w 2 :=
    fun w ↦ rWhFull_apply_pos hm rId w 6 (by decide)
  have hsgn_not : (if (!isInv) then (-1 : ℤ) else 1) = -(if isInv then (-1 : ℤ) else 1) := by
    cases isInv <;> rfl
  rw [htop 0] at hsp0
  rw [htop 1] at hsp1
  rw [htop 2] at hsp2
  change (regVal ((rWhFull hm rId 0).slice 0 7 (by decide)) γ : ℤ) =
    (regVal ((rWhFull hm rId 0).slice 0 6 (by decide)) γ : ℤ) +
      64 * ((γ (rProjAxis rId 0 2)).val : ℤ) at hsp0
  change (regVal ((rWhFull hm rId 1).slice 0 7 (by decide)) γ : ℤ) =
    (regVal ((rWhFull hm rId 1).slice 0 6 (by decide)) γ : ℤ) +
      64 * ((γ (rProjAxis rId 1 2)).val : ℤ) at hsp1
  change (regVal ((rWhFull hm rId 2).slice 0 7 (by decide)) γ : ℤ) =
    (regVal ((rWhFull hm rId 2).slice 0 6 (by decide)) γ : ℤ) +
      64 * ((γ (rProjAxis rId 2 2)).val : ℤ) at hsp2
  have hStg0 : whStgLowShift hm 0 isInv γ = (-(if isInv then (-1 : ℤ) else 1)) * (((1 - 2 *
      (wfBitVal hm γ * ((γ (rProjAxis rId 0 0)).val : ℤ))) * (regVal ((rWhFull hm rId 0).slice
      0 7 (by decide)) γ : ℤ) + (wfBitVal hm γ * ((γ (rProjAxis rId 0 0)).val : ℤ)) * 128) +
      ((1 - 2 * (wfBitVal hm γ * ((γ (rProjAxis rId 1 0)).val : ℤ))) * (regVal ((rWhFull hm
      rId 1).slice 0 7 (by decide)) γ : ℤ) + (wfBitVal hm γ * ((γ (rProjAxis rId 1 0)).val :
      ℤ)) * 128) + ((1 - 2 * (wfBitVal hm γ * ((γ (rProjAxis rId 2 0)).val : ℤ))) * (regVal
      ((rWhFull hm rId 2).slice 0 7 (by decide)) γ : ℤ) + (wfBitVal hm γ * ((γ (rProjAxis rId
      2 0)).val : ℤ)) * 128)) := by
    unfold whStgLowShift
    dsimp only
    rw [Fin.sum_univ_three]
    rfl
  rw [hStg0]
  unfold whRemLowShift whStg0RemLowShift6 whStg0RemOrVal
  dsimp only [rId] at hsp0 hsp1 hsp2 ⊢
  rw [Fin.sum_univ_three, Fin.sum_univ_three, hsp0, hsp1, hsp2, hsgn_not]
  ring
theorem uWhRemCat_mul_uWhStgCat0_eq {mPayload : ℕ} (hm : 22 ≤ mPayload) (isInv : Bool) :
    uWhRemCat hm isInv * uWhStgCat hm 0 isInv = uApexShift45 (fullSysCoreWires mPayload) 6
    (by decide) (whStg0RemLowShift6 hm isInv) * ((rCoreBlock48 mPayload).embedUnitary
    (DyadicQft64.dyadicDiagUnitary (fullSysCoreWires mPayload) 48 (fun γ ↦ (if (!isInv) then
    (-1 : ℤ) else 1) * (2 ^ 39 : ℤ) * 64 * whStg0RemOrVal hm 2 γ)) * ((rCoreBlock48
    mPayload).embedUnitary (DyadicQft64.dyadicDiagUnitary (fullSysCoreWires mPayload) 48 (fun
    γ ↦ (if (!isInv) then (-1 : ℤ) else 1) * (2 ^ 39 : ℤ) * 64 * whStg0RemOrVal hm 1 γ)) *
    ((rCoreBlock48 mPayload).embedUnitary (DyadicQft64.dyadicDiagUnitary (fullSysCoreWires
    mPayload) 48 (fun γ ↦ (if (!isInv) then (-1 : ℤ) else 1) * (2 ^ 39 : ℤ) * 64 *
    whStg0RemOrVal hm 0 γ)) * ((rCoreBlock48 mPayload).embedUnitary
    (DyadicQft64.dyadicDiagUnitary (fullSysCoreWires mPayload) 48 (whRemTopExp hm isInv)) *
    (rCoreBlock48 mPayload).embedUnitary (DyadicQft64.dyadicDiagUnitary (fullSysCoreWires
    mPayload) 48 (whStgTopExp hm 0 isInv)))))) := by
  let kSys := fullSysCoreWires mPayload
  let rCB := rCoreBlock48 mPayload
  have hComm : rCB.embedUnitary (DyadicQft64.dyadicDiagUnitary kSys 48 (whRemTopExp hm isInv))
      * uApexShift45 kSys 7 (by decide) (whStgLowShift hm 0 isInv) = uApexShift45 kSys 7
      (by decide) (whStgLowShift hm 0 isInv) * rCB.embedUnitary
      (DyadicQft64.dyadicDiagUnitary kSys 48 (whRemTopExp hm isInv)) :=
    uApexShift45_comm_coreDiag kSys 7 (by decide) 48 (whRemTopExp hm isInv) (whStgLowShift hm 0
      isInv)
  have hMul7 : uApexShift45 kSys 7 (by decide) (whRemLowShift hm isInv) * uApexShift45 kSys 7
      (by decide) (whStgLowShift hm 0 isInv) = uApexShift45 kSys 7 (by decide) (fun γ ↦ 2 *
      whStg0RemLowShift6 hm isInv γ + 128 * ((if (!isInv) then (-1 : ℤ) else 1) *
      (whStg0RemOrVal hm 0 γ + whStg0RemOrVal hm 1 γ + whStg0RemOrVal hm 2 γ))) := by
    rw [uApexShiftA_mul]
    exact uApexShift45_congr (by decide) (by decide) rfl (whStg0_add_whRem_lowShift_eq hm isInv)
  have hOrDiag : rCB.embedUnitary (DyadicQft64.dyadicDiagUnitary kSys 48 (fun γ ↦ (2 ^ 45 : ℤ)
      * ((if (!isInv) then (-1 : ℤ) else 1) * (whStg0RemOrVal hm 0 γ + whStg0RemOrVal hm 1 γ +
      whStg0RemOrVal hm 2 γ)))) = rCB.embedUnitary (DyadicQft64.dyadicDiagUnitary kSys 48 (fun
      γ ↦ (if (!isInv) then (-1 : ℤ) else 1) * (2 ^ 39 : ℤ) * 64 * whStg0RemOrVal hm 2 γ)) *
      (rCB.embedUnitary (DyadicQft64.dyadicDiagUnitary kSys 48 (fun γ ↦ (if (!isInv) then (-1
      : ℤ) else 1) * (2 ^ 39 : ℤ) * 64 * whStg0RemOrVal hm 1 γ)) * rCB.embedUnitary
      (DyadicQft64.dyadicDiagUnitary kSys 48 (fun γ ↦ (if (!isInv) then (-1 : ℤ) else 1) * (2
      ^ 39 : ℤ) * 64 * whStg0RemOrVal hm 0 γ))) := by
    have hD : DyadicQft64.dyadicDiagUnitary kSys 48 (fun γ ↦ (2 ^ 45 : ℤ) * ((if (!isInv) then
        (-1 : ℤ) else 1) * (whStg0RemOrVal hm 0 γ + whStg0RemOrVal hm 1 γ + whStg0RemOrVal hm
        2 γ))) = DyadicQft64.dyadicDiagUnitary kSys 48 (fun γ ↦ (if (!isInv) then (-1 : ℤ)
        else 1) * (2 ^ 39 : ℤ) * 64 * whStg0RemOrVal hm 2 γ) * (DyadicQft64.dyadicDiagUnitary
        kSys 48 (fun γ ↦ (if (!isInv) then (-1 : ℤ) else 1) * (2 ^ 39 : ℤ) * 64 *
        whStg0RemOrVal hm 1 γ) * DyadicQft64.dyadicDiagUnitary kSys 48 (fun γ ↦ (if (!isInv)
        then (-1 : ℤ) else 1) * (2 ^ 39 : ℤ) * 64 * whStg0RemOrVal hm 0 γ)) := by
      rw [dyadicDiagUnitary_mul, dyadicDiagUnitary_mul]
      apply dyadicDiagUnitary_congr
      intro γ
      ring
    rw [hD, rCB.embedUnitary_mul, rCB.embedUnitary_mul]
  unfold uWhRemCat uWhStgCat
  dsimp only [Fin.val_zero, Nat.sub_zero]
  calc
    (uApexShift45 kSys 7 (by decide) (whRemLowShift hm isInv) *
        rCB.embedUnitary (DyadicQft64.dyadicDiagUnitary kSys 48 (whRemTopExp hm isInv))) *
      (uApexShift45 kSys 7 (by decide) (whStgLowShift hm 0 isInv) *
        rCB.embedUnitary (DyadicQft64.dyadicDiagUnitary kSys 48 (whStgTopExp hm 0 isInv)))
      = (uApexShift45 kSys 7 (by decide) (whRemLowShift hm isInv) *
          uApexShift45 kSys 7 (by decide) (whStgLowShift hm 0 isInv)) *
        (rCB.embedUnitary (DyadicQft64.dyadicDiagUnitary kSys 48 (whRemTopExp hm isInv)) *
          rCB.embedUnitary (DyadicQft64.dyadicDiagUnitary kSys 48 (whStgTopExp hm 0 isInv))) := by
        rw [mul_assoc (uApexShift45 kSys 7 _ (whRemLowShift hm isInv)),
          ← mul_assoc (rCB.embedUnitary _), hComm]
        simp only [mul_assoc]
    _ = _ := by
        rw [hMul7, uApexShift45_seven_of_two_mul_add]
        dsimp only [kSys, rCB] at hOrDiag ⊢
        rw [hOrDiag]
        simp only [mul_assoc]
def dOrTBit {Var : Type} {n : ℕ} (isInv : Bool) (v : Var) (c₁ c₂ anc : Wire n) (h₁₂ : c₁ ≠ c₂)
    (h₁a : c₁ ≠ anc) (h₂a : c₂ ≠ anc) : DynamicCircuit Var n := dGenBoolWrap true true true v
    c₁ c₂ anc h₁₂ h₁a h₂a (.circuit (cApexSign isInv anc))
@[simp] lemma count_dOrTBit_toff {Var : Type} {n : ℕ} (isInv : Bool) (v : Var)
    (c₁ c₂ anc : Wire n) (h₁₂ : c₁ ≠ c₂) (h₁a : c₁ ≠ anc) (h₂a : c₂ ≠ anc) :
    (dOrTBit isInv v c₁ c₂ anc h₁₂ h₁a h₂a).count .TOFF = 0 := by
  unfold dOrTBit
  rw [count_dGenBoolWrap_toff]
  exact count_cApexSign_toff isInv anc
@[simp] lemma count_dOrTBit_t {Var : Type} {n : ℕ} (isInv : Bool) (v : Var)
    (c₁ c₂ anc : Wire n) (h₁₂ : c₁ ≠ c₂) (h₁a : c₁ ≠ anc) (h₂a : c₂ ≠ anc) :
    (dOrTBit isInv v c₁ c₂ anc h₁₂ h₁a h₂a).count .T = 5 := by
  unfold dOrTBit
  rw [count_dGenBoolWrap_t]
  have h1 : (DynamicCircuit.circuit (cApexSign isInv anc) : DynamicCircuit Var n).count .T = 1 :=
    count_cApexSign_t isInv anc
  rw [h1]
lemma CondStageSpec_of_dOrTBit {Var : Type} [Fintype Var] [DecidableEq Var]
    {mPayload mW n : ℕ} (isInv : Bool) (v : Var) (c₁ c₂ anc : Wire n) (h₁₂ : c₁ ≠ c₂)
    (h₁a : c₁ ≠ anc) (h₂a : c₂ ≠ anc) (rCore : QRegister (fullSysCoreWires mPayload) n)
    (rPGTwist : QRegister 48 n) (hCP : rCore.DisjointWires rPGTwist) (rW : QRegister mW n)
    (S_outer : Finset (Wire n)) (H_outer : BitAssignment n → Prop)
    (f_core : BitAssignment (fullSysCoreWires mPayload) → ℤ) (hAncW : anc ∈ rW.image)
    (hc1W : c₁ ∉ rW.image) (hc2W : c₂ ∉ rW.image)
    (hancAct : anc ∉ (rCore.concat rPGTwist hCP).image) (hc1S : c₁ ∈ S_outer)
    (hc2S : c₂ ∈ S_outer) (hH_anc : ∀ ξ₁ ξ₂, (∀ w, w ≠ anc → ξ₁ w = ξ₂ w) → H_outer ξ₁ →
    H_outer ξ₂) (hEq : ∀ η : BitAssignment n, H_outer η → (1 - ((η c₁).val : ℤ)) * ((η c₂).val
    : ℤ) + ((η c₁).val : ℤ) = f_core (fun i ↦ η (rCore i))) : CondStageSpec
    (rCore.concat rPGTwist hCP) rW S_outer H_outer ((rCoreBlock48 mPayload).embedUnitary
    (DyadicQft64.dyadicDiagUnitary (fullSysCoreWires mPayload) 48 (fun γ ↦ (if isInv then (-1
    : ℤ) else 1) * (2 ^ 39 : ℤ) * 64 * f_core γ))) (dOrTBit isInv v c₁ c₂ anc h₁₂ h₁a h₂a)
    := by
  let r0 : QRegister 0 n := rW.slice 0 0 (Nat.zero_le _)
  have hanc0 : anc ∉ r0.image := by
    intro hm; rcases (QRegister.mem_image r0 anc).mp hm with ⟨i, _⟩; exact Fin.elim0 i
  have hsSign : CondStageSpec (rCore.concat rPGTwist hCP) r0 (S_outer ∪ rW.image) (fun η ↦
      H_outer η ∧ η anc = genBoolBit true true true (η c₁) (η c₂)) ((rCoreBlock48
      mPayload).embedUnitary (DyadicQft64.dyadicDiagUnitary (fullSysCoreWires mPayload) 48
      (fun γ ↦ (if isInv then (-1 : ℤ) else 1) * (2 ^ 39 : ℤ) * 64 * f_core γ)))
      (.circuit (cApexSign isInv anc) : DynamicCircuit Var n) := by
    refine CondStageSpec.of_diag_circuit rCore rPGTwist hCP r0 (S_outer ∪ rW.image) _ _
      (fun η ↦ (if isInv then (-1 : ℤ) else 1) * (2 ^ 45 : ℤ) * ((η anc).val : ℤ))
      (fun γ ↦ (if isInv then (-1 : ℤ) else 1) * (2 ^ 39 : ℤ) * 64 * f_core γ)
      (fun η ↦ ?_) (fun η _ ⟨hHη, hancη⟩ ↦ ?_)
    · rw [cApexSign_evolve]
      refine congrArg (· • basisKet η) ?_
      have hEq45 : (if isInv then (-1 : ℤ) else 1) * (2 ^ 45 : ℤ) * ((η anc).val : ℤ) =
          (2 ^ 45 : ℤ) * ((if isInv then (-1 : ℤ) else 1) * ((η anc).val : ℤ)) := by ring
      rw [hEq45, JunctionApexCSA288.dyadicTurn_scale_pow 45 3]
    · have hor : ((η anc).val : ℤ) =
          (1 - ((η c₁).val : ℤ)) * ((η c₂).val : ℤ) + ((η c₁).val : ℤ) := by
        rw [hancη]; exact genBoolBit_true_true_true_val_int (η c₁) (η c₂)
      rw [hor, hEq η hHη]; ring
  exact CondStageSpec.dGenBoolWrap true true true v c₁ c₂ anc h₁₂ h₁a h₂a
    r0 rW (QRegister.image_compose_subset rW _) hAncW hc1W hc2W hanc0 hancAct hc1S hc2S
    Finset.subset_union_left hH_anc hsSign
/-- Fused `k = 0` + remainder stage `dWhStg0Rem_3D_Pos45` (`179 T`, `.TOFF = 0`) on `45` wires. -/
noncomputable def dWhStg0Rem_3D_Pos45 {mPayload : ℕ} (isInv : Bool) (hm : 22 ≤ mPayload)
    {Var : Type} {n : ℕ} (v : Var) (rCore : QRegister (fullSysCoreWires mPayload) n)
    (rPGTwist : QRegister 48 n) (rWork : QRegister JunctionPrefixPruned220.mWork45 n)
    (_hCP : rCore.DisjointWires rPGTwist) (hCW : rCore.DisjointWires rWork)
    (hPW : rPGTwist.DisjointWires rWork) : DynamicCircuit Var n :=
  let wf := rWork 6
  let rW38 := rWork.slice 7 38 (by decide)
  let rQ := rW38.slice 0 3 (by decide)
  let rW35 := rW38.slice 3 35 (by decide)
  let rM0 := rW35.slice 0 6 (by decide)
  let rM1 := rW35.slice 6 6 (by decide)
  let rM2 := rW35.slice 12 6 (by decide)
  let rScr17 := rW35.slice 18 17 (by decide)
  have hCW38 : rCore.DisjointWires rW38 := (QRegExt.disjointWires_mono_right hCW)
    (QRegister.image_compose_subset rWork _)
  have hPW38 : rPGTwist.DisjointWires rW38 := (QRegExt.disjointWires_mono_right hPW)
    (QRegister.image_compose_subset rWork _)
  have hCW_Q : rCore.DisjointWires rQ := (QRegExt.disjointWires_mono_right hCW38)
    (QRegister.image_compose_subset rW38 _)
  have hCW35 : rCore.DisjointWires rW35 := (QRegExt.disjointWires_mono_right hCW38)
    (QRegister.image_compose_subset rW38 _)
  have hPW35 : rPGTwist.DisjointWires rW35 := (QRegExt.disjointWires_mono_right hPW38)
    (QRegister.image_compose_subset rW38 _)
  have hQ35 : rQ.DisjointWires rW35 :=
    slice_disjoint_of_le rW38 0 3 3 35 (by decide) (by decide) (by decide)
  let rP0 : QRegister 3 n :=
    ⟨⟨![rProjAxis rCore 0 0, rProjAxis rCore 1 0, rProjAxis rCore 2 0], fun i j hij ↦ by
      fin_cases i <;> fin_cases j
      · rfl
      · exact False.elim (disj_wire_ne (rProjAxis_disjoint_of_ne rCore (by
          decide : (0 : Fin 3) ≠ 1)) 0 0 hij)
      · exact False.elim (disj_wire_ne (rProjAxis_disjoint_of_ne rCore (by
          decide : (0 : Fin 3) ≠ 2)) 0 0 hij)
      · exact False.elim (disj_wire_ne (rProjAxis_disjoint_of_ne rCore (by
          decide : (1 : Fin 3) ≠ 0)) 0 0 hij)
      · rfl
      · exact False.elim (disj_wire_ne (rProjAxis_disjoint_of_ne rCore (by
          decide : (1 : Fin 3) ≠ 2)) 0 0 hij)
      · exact False.elim (disj_wire_ne (rProjAxis_disjoint_of_ne rCore (by
          decide : (2 : Fin 3) ≠ 0)) 0 0 hij)
      · exact False.elim (disj_wire_ne (rProjAxis_disjoint_of_ne rCore (by
          decide : (2 : Fin 3) ≠ 1)) 0 0 hij)
      · rfl⟩⟩
  have hP0_sub : rP0.image ⊆ rCore.image := by
    intro u hu
    rcases (QRegister.mem_image rP0 u).mp hu with ⟨w, rfl⟩
    fin_cases w <;> exact rProjAxis_sub_rCore rCore _ ((QRegister.mem_image _ _).mpr ⟨0, rfl⟩)
  have hwf_P0 : ∀ w : Fin 3, wf ≠ rP0 w :=
    fun w ↦ (disj_wire_ne ((QRegExt.disjointWires_mono_left hCW) hP0_sub) w 6).symm
  have hwf_Q : ∀ w : Fin 3, wf ≠ rQ w := fun w hEq ↦
    reg_not_mem_slice rWork (by decide) 6 (by decide)
      ((QRegister.image_compose_subset rW38 _) ((QRegister.mem_image rQ _).mpr ⟨w, hEq.symm⟩))
  have hP0_Q : rP0.DisjointWires rQ := (QRegExt.disjointWires_mono_left hCW_Q) hP0_sub
  let low6 : Fin 3 → QRegister 6 n := fun w ↦ (rWhFull hm rCore w).slice 0 6 (by decide)
  let top0 : Fin 3 → Wire n := fun w ↦ rWhFull hm rCore w 7
  let rT6 : QRegister 6 n := rPGTwist.slice 39 6 (by decide)
  have hLow6_sub : ∀ w : Fin 3, (low6 w).image ⊆ rCore.image := fun w ↦
    Finset.Subset.trans (QRegister.image_compose_subset _ _) (rWhFull_sub_rCore hm rCore w)
  have hq_top0 : ∀ w : Fin 3, rQ w ≠ top0 w := fun w ↦
    (disj_wire_ne ((QRegExt.disjointWires_mono_left hCW_Q) (rWhFull_sub_rCore hm rCore w)) 7 w).symm
  have hq_p2 : ∀ w : Fin 3, rQ w ≠ rProjAxis rCore w 2 := fun w ↦
    (disj_wire_ne ((QRegExt.disjointWires_mono_left hCW_Q) (rProjAxis_sub_rCore rCore w)) 2 w).symm
  have hq_w35_0 : ∀ w : Fin 3, rQ w ≠ rW35 0 := fun w ↦ disj_wire_ne hQ35 w 0
  have hp2_w35_0 : ∀ w : Fin 3, rProjAxis rCore w 2 ≠ rW35 0 := fun w ↦
    disj_wire_ne ((QRegExt.disjointWires_mono_left hCW35) (rProjAxis_sub_rCore rCore w)) 2 0
  let cTop : Circuit n :=
    cWhTopAxis isInv (rQ 0) (top0 0) (hq_top0 0) ;;ᶜ
      cWhTopAxis isInv (rQ 1) (top0 1) (hq_top0 1) ;;ᶜ
      cWhTopAxis isInv (rQ 2) (top0 2) (hq_top0 2)
  have hq_low6 : ∀ (w : Fin 3) (i : Fin 6), rQ w ≠ low6 w i := fun w i ↦
    (disj_wire_ne ((QRegExt.disjointWires_mono_left hCW_Q) (hLow6_sub w)) i w).symm
  have hQ_M0 : ∀ (w : Fin 3) (i : Fin 6), rQ w ≠ rM0 i := fun w i ↦
    disj_wire_ne ((QRegExt.disjointWires_mono_right hQ35) (QRegister.image_compose_subset rW35 _)) w
      i
  have hQ_M1 : ∀ (w : Fin 3) (i : Fin 6), rQ w ≠ rM1 i := fun w i ↦
    disj_wire_ne ((QRegExt.disjointWires_mono_right hQ35) (QRegister.image_compose_subset rW35 _)) w
      i
  have hQ_M2 : ∀ (w : Fin 3) (i : Fin 6), rQ w ≠ rM2 i := fun w i ↦
    disj_wire_ne ((QRegExt.disjointWires_mono_right hQ35) (QRegister.image_compose_subset rW35 _)) w
      i
  have hLow0_M0 : (low6 0).DisjointWires rM0 :=
    (QRegExt.disjointWires_mono_right ((QRegExt.disjointWires_mono_left hCW35) (hLow6_sub 0)))
      (QRegister.image_compose_subset rW35 _)
  have hLow1_M1 : (low6 1).DisjointWires rM1 :=
    (QRegExt.disjointWires_mono_right ((QRegExt.disjointWires_mono_left hCW35) (hLow6_sub 1)))
      (QRegister.image_compose_subset rW35 _)
  have hLow2_M2 : (low6 2).DisjointWires rM2 :=
    (QRegExt.disjointWires_mono_right ((QRegExt.disjointWires_mono_left hCW35) (hLow6_sub 2)))
      (QRegister.image_compose_subset rW35 _)
  have hM01 : rM0.DisjointWires rM1 :=
    slice_disjoint_of_le rW35 0 6 6 6 (by decide) (by decide) (by decide)
  have hM02 : rM0.DisjointWires rM2 :=
    slice_disjoint_of_le rW35 0 6 12 6 (by decide) (by decide) (by decide)
  have hM12 : rM1.DisjointWires rM2 :=
    slice_disjoint_of_le rW35 6 6 12 6 (by decide) (by decide) (by decide)
  have hM1_T6 : rM1.DisjointWires rT6 :=
    (QRegExt.disjointWires_mono_right ((QRegExt.disjointWires_mono_left (disj_symm hPW35))
      (QRegister.image_compose_subset rW35 _)))
      (QRegister.image_compose_subset rPGTwist _)
  have hM0_Scr : rM0.DisjointWires rScr17 :=
    slice_disjoint_of_le rW35 0 6 18 17 (by decide) (by decide) (by decide)
  have hM1_Scr : rM1.DisjointWires rScr17 :=
    slice_disjoint_of_le rW35 6 6 18 17 (by decide) (by decide) (by decide)
  have hM2_Scr : rM2.DisjointWires rScr17 :=
    slice_disjoint_of_le rW35 12 6 18 17 (by decide) (by decide) (by decide)
  have hT6_Scr : rT6.DisjointWires rScr17 := (QRegExt.disjointWires_mono_right
    ((QRegExt.disjointWires_mono_left hPW35) (QRegister.image_compose_subset
      rPGTwist _))) (QRegister.image_compose_subset rW35 _)
  let dCsa5 := dCsa3AxisApex (!isInv) 5 v rM0 rM1 rM2 rT6 rScr17
    hM01 hM02 hM12 hM1_T6 hM0_Scr hM1_Scr hM2_Scr hT6_Scr
  let dLow6 := FusedVepCore288.dPureConj (Circuit.X (rQ 0)) (FusedVepCore288.dPureConj
      (Circuit.X (rQ 1)) (FusedVepCore288.dPureConj (Circuit.X (rQ 2)) (dMaskRegWrap 6 v
      (rQ 0) (low6 0) rM0 (hq_low6 0) (hQ_M0 0) hLow0_M0 (dMaskRegWrap 6 v (rQ 1) (low6 1) rM1
      (hq_low6 1) (hQ_M1 1) hLow1_M1 (dMaskRegWrap 6 v (rQ 2) (low6 2) rM2 (hq_low6 2) (hQ_M2
      2) hLow2_M2 dCsa5)))))
  dMaskRegWrap 3 v wf rP0 rQ hwf_P0 hwf_Q hP0_Q
    (.seq (.circuit cTop)
      (.seq (.circuit (cWhRemTop isInv hm rCore))
        (.seq (dOrTBit (!isInv) v (rQ 0) (rProjAxis rCore 0 2) (rW35 0) (hq_p2 0) (hq_w35_0 0)
          (hp2_w35_0 0))
          (.seq (dOrTBit (!isInv) v (rQ 1) (rProjAxis rCore 1 2) (rW35 0) (hq_p2 1) (hq_w35_0 1)
            (hp2_w35_0 1))
            (.seq (dOrTBit (!isInv) v (rQ 2) (rProjAxis rCore 2 2) (rW35 0) (hq_p2 2) (hq_w35_0 2)
              (hp2_w35_0 2))
              dLow6)))))
@[simp] lemma count_dWhStg0Rem_3D_toff_Pos45 {mPayload : ℕ} (isInv : Bool)
    (hm : 22 ≤ mPayload) {Var : Type} {n : ℕ} (v : Var)
    (rCore : QRegister (fullSysCoreWires mPayload) n) (rPGTwist : QRegister 48 n)
    (rWork : QRegister JunctionPrefixPruned220.mWork45 n) (hCP : rCore.DisjointWires rPGTwist)
    (hCW : rCore.DisjointWires rWork) (hPW : rPGTwist.DisjointWires rWork) :
    (dWhStg0Rem_3D_Pos45 isInv hm v rCore rPGTwist rWork hCP hCW hPW).count .TOFF = 0 := by
  unfold dWhStg0Rem_3D_Pos45
  dsimp only
  rw [count_dMaskRegWrap_toff, count_dyn_seq, count_dyn_seq, count_dyn_seq,
    count_dyn_seq, count_dyn_seq,
    count_dOrTBit_toff, count_dOrTBit_toff, count_dOrTBit_toff,
    FusedVepCore288.count_dPureConj_toff _ (by simp [Circuit.X]),
    FusedVepCore288.count_dPureConj_toff _ (by simp [Circuit.X]),
    FusedVepCore288.count_dPureConj_toff _ (by simp [Circuit.X]),
    count_dMaskRegWrap_toff, count_dMaskRegWrap_toff, count_dMaskRegWrap_toff,
    count_dCsa3AxisApex_toff]
  cases isInv <;> rfl
@[simp] lemma count_dWhStg0Rem_3D_t_Pos45 {mPayload : ℕ} (isInv : Bool) (hm : 22 ≤ mPayload)
    {Var : Type} {n : ℕ} (v : Var) (rCore : QRegister (fullSysCoreWires mPayload) n)
    (rPGTwist : QRegister 48 n) (rWork : QRegister JunctionPrefixPruned220.mWork45 n)
    (hCP : rCore.DisjointWires rPGTwist) (hCW : rCore.DisjointWires rWork)
    (hPW : rPGTwist.DisjointWires rWork) : (dWhStg0Rem_3D_Pos45 isInv hm v rCore rPGTwist
    rWork hCP hCW hPW).count .T = 179 := by
  unfold dWhStg0Rem_3D_Pos45
  dsimp only
  rw [count_dMaskRegWrap_t, count_dyn_seq, count_dyn_seq, count_dyn_seq,
    count_dyn_seq, count_dyn_seq,
    count_dOrTBit_t, count_dOrTBit_t, count_dOrTBit_t,
    FusedVepCore288.count_dPureConj_t _ (by simp [Circuit.X]),
    FusedVepCore288.count_dPureConj_t _ (by simp [Circuit.X]),
    FusedVepCore288.count_dPureConj_t _ (by simp [Circuit.X]),
    count_dMaskRegWrap_t, count_dMaskRegWrap_t, count_dMaskRegWrap_t,
    count_dCsa3AxisApex_t]
  have hcTop : ∀ (q0 t0 q1 t1 q2 t2 : Wire n) h0 h1 h2,
      (DynamicCircuit.circuit
        (cWhTopAxis isInv q0 t0 h0 ;;ᶜ cWhTopAxis isInv q1 t1 h1 ;;ᶜ cWhTopAxis isInv q2 t2 h2) :
        DynamicCircuit Var n).count .T = 3 := by
    intros; cases isInv <;> rfl
  have hcRem : (DynamicCircuit.circuit (cWhRemTop isInv hm rCore) : DynamicCircuit Var n).count .T =
    6 :=
    count_cWhRemTop_t isInv hm rCore
  rw [hcTop, hcRem]
  decide
theorem dWhStg0Rem_3D_spec_Pos45 {mPayload : ℕ} (isInv : Bool) (hm : 22 ≤ mPayload)
    {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ} (v : Var)
    (rCore : QRegister (fullSysCoreWires mPayload) n) (rPGTwist : QRegister 48 n)
    (rWork : QRegister JunctionPrefixPruned220.mWork45 n) (hCP : rCore.DisjointWires rPGTwist)
    (hCW : rCore.DisjointWires rWork) (hPW : rPGTwist.DisjointWires rWork) : CondStageSpec
    (rCore.concat rPGTwist hCP) (rWork.slice 7 38 (by decide))
    ((rHigh rCore).image ∪ (rWork.slice 0 7 (by decide)).image)
    (JunctionPrefixPruned220.HProjFlag hm rCore rWork)
    (uWhRemCat hm isInv * uWhStgCat hm 0 isInv)
    (dWhStg0Rem_3D_Pos45 isInv hm v rCore rPGTwist rWork hCP hCW hPW) := by
  let rAct := rCore.concat rPGTwist hCP
  let wf := rWork 6
  let rW07 := rWork.slice 0 7 (by decide)
  let rW38 := rWork.slice 7 38 (by decide)
  let rQ := rW38.slice 0 3 (by decide)
  let rW35 := rW38.slice 3 35 (by decide)
  let rM0 := rW35.slice 0 6 (by decide)
  let rW29 := rW35.slice 6 29 (by decide)
  let rM1 := rW35.slice 6 6 (by decide)
  let rW23 := rW35.slice 12 23 (by decide)
  let rM2 := rW35.slice 12 6 (by decide)
  let rScr17 := rW35.slice 18 17 (by decide)
  let S_core7 : Finset (Wire n) := rCore.image ∪ rW07.image
  let S_q : Finset (Wire n) := S_core7 ∪ rQ.image
  apply CondStageSpec.anti_S (S₂ := S_core7)
    (Finset.union_subset_union_left (rHigh_sub_rCore rCore))
  unfold dWhStg0Rem_3D_Pos45
  have hCW38 : rCore.DisjointWires rW38 := (QRegExt.disjointWires_mono_right hCW)
    (QRegister.image_compose_subset rWork _)
  have hPW38 : rPGTwist.DisjointWires rW38 := (QRegExt.disjointWires_mono_right hPW)
    (QRegister.image_compose_subset rWork _)
  have hActW38 : rAct.DisjointWires rW38 := QRegExt.disjointWires_concat_left hCW38 hPW38
  have hActW35 : rAct.DisjointWires rW35 := (QRegExt.disjointWires_mono_right hActW38)
    (QRegister.image_compose_subset rW38 _)
  have hCW_Q : rCore.DisjointWires rQ := (QRegExt.disjointWires_mono_right hCW38)
    (QRegister.image_compose_subset rW38 _)
  have hCW35 : rCore.DisjointWires rW35 := (QRegExt.disjointWires_mono_right hCW38)
    (QRegister.image_compose_subset rW38 _)
  have hPW35 : rPGTwist.DisjointWires rW35 := (QRegExt.disjointWires_mono_right hPW38)
    (QRegister.image_compose_subset rW38 _)
  have hQ35 : rQ.DisjointWires rW35 :=
    slice_disjoint_of_le rW38 0 3 3 35 (by decide) (by decide) (by decide)
  have hwf_S : wf ∈ S_core7 :=
    Finset.mem_union_right _ (reg_mem_slice rWork (by decide) 6 (by decide) (by decide))
  have hwf_not35 : wf ∉ rW35.image := fun hm' ↦
    reg_not_mem_slice rWork (by decide) 6 (by decide) ((QRegister.image_compose_subset rW38 _) hm')
  let rP0 : QRegister 3 n :=
    ⟨⟨![rProjAxis rCore 0 0, rProjAxis rCore 1 0, rProjAxis rCore 2 0], fun i j hij ↦ by
      fin_cases i <;> fin_cases j
      · rfl
      · exact False.elim (disj_wire_ne (rProjAxis_disjoint_of_ne rCore (by
          decide : (0 : Fin 3) ≠ 1)) 0 0 hij)
      · exact False.elim (disj_wire_ne (rProjAxis_disjoint_of_ne rCore (by
          decide : (0 : Fin 3) ≠ 2)) 0 0 hij)
      · exact False.elim (disj_wire_ne (rProjAxis_disjoint_of_ne rCore (by
          decide : (1 : Fin 3) ≠ 0)) 0 0 hij)
      · rfl
      · exact False.elim (disj_wire_ne (rProjAxis_disjoint_of_ne rCore (by
          decide : (1 : Fin 3) ≠ 2)) 0 0 hij)
      · exact False.elim (disj_wire_ne (rProjAxis_disjoint_of_ne rCore (by
          decide : (2 : Fin 3) ≠ 0)) 0 0 hij)
      · exact False.elim (disj_wire_ne (rProjAxis_disjoint_of_ne rCore (by
          decide : (2 : Fin 3) ≠ 1)) 0 0 hij)
      · rfl⟩⟩
  have hP0_sub : rP0.image ⊆ rCore.image := by
    intro u hu
    rcases (QRegister.mem_image rP0 u).mp hu with ⟨w, rfl⟩
    fin_cases w <;> exact rProjAxis_sub_rCore rCore _ ((QRegister.mem_image _ _).mpr ⟨0, rfl⟩)
  have hwf_Q : ∀ w : Fin 3, wf ≠ rQ w := fun w hEq ↦
    reg_not_mem_slice rWork (by decide) 6 (by decide)
      ((QRegister.image_compose_subset rW38 _) ((QRegister.mem_image rQ _).mpr ⟨w, hEq.symm⟩))
  let H_q : BitAssignment n → Prop := fun η ↦
    JunctionPrefixPruned220.HProjFlag hm rCore rWork η ∧ ∀ w : Fin 3, η (rQ w) = η wf * η (rP0 w)
  have hHq_congr : ∀ ξ₁ ξ₂, (∀ u ∈ S_q, ξ₁ u = ξ₂ u) → (H_q ξ₁ ↔ H_q ξ₂) := by
    intro ξ₁ ξ₂ hEq
    have h1 := JunctionPrefixPruned220.HProjFlag_congr_S hm rCore rWork
      (Finset.Subset.trans (rHigh_sub_rCore rCore) (Finset.Subset.trans Finset.subset_union_left
        Finset.subset_union_left))
      (Finset.mem_union_left _ hwf_S) ξ₁ ξ₂ hEq
    refine and_congr h1 (forall_congr' fun w ↦ ?_)
    rw [hEq (rQ w) (Finset.mem_union_right _ ((QRegister.mem_image rQ _).mpr ⟨w, rfl⟩)),
      hEq wf (Finset.mem_union_left _ hwf_S),
      hEq (rP0 w) (Finset.mem_union_left _ (Finset.mem_union_left _
        (hP0_sub ((QRegister.mem_image rP0 _).mpr ⟨w, rfl⟩))))]
  have hq_val : ∀ (η : BitAssignment n) (w : Fin 3), H_q η → ((η (rQ w)).val : ℤ) = wfBitVal
      hm (fun q ↦ η (rCore q)) * (((fun q ↦ η (rCore q)) (rProjAxis (QRegExt.idReg _) w
      0)).val : ℤ) := by
    intro η w ⟨hHp, hQEq⟩
    rw [hQEq w, zmod2_mul_val_int, JunctionPrefixPruned220.wfBitVal_of_HProjFlag hm rCore rWork hHp]
    fin_cases w <;> rfl
  let low6 : Fin 3 → QRegister 6 n := fun w ↦ (rWhFull hm rCore w).slice 0 6 (by decide)
  let top0 : Fin 3 → Wire n := fun w ↦ rWhFull hm rCore w 7
  let rT6 : QRegister 6 n := rPGTwist.slice 39 6 (by decide)
  have hLow6_sub : ∀ w : Fin 3, (low6 w).image ⊆ rCore.image := fun w ↦
    Finset.Subset.trans (QRegister.image_compose_subset _ _) (rWhFull_sub_rCore hm rCore w)
  have hq_top0 : ∀ w : Fin 3, rQ w ≠ top0 w := fun w ↦
    (disj_wire_ne ((QRegExt.disjointWires_mono_left hCW_Q) (rWhFull_sub_rCore hm rCore w)) 7 w).symm
  have hq_p2 : ∀ w : Fin 3, rQ w ≠ rProjAxis rCore w 2 := fun w ↦
    (disj_wire_ne ((QRegExt.disjointWires_mono_left hCW_Q) (rProjAxis_sub_rCore rCore w)) 2 w).symm
  have hq_w35_0 : ∀ w : Fin 3, rQ w ≠ rW35 0 := fun w ↦ disj_wire_ne hQ35 w 0
  have hp2_w35_0 : ∀ w : Fin 3, rProjAxis rCore w 2 ≠ rW35 0 := fun w ↦
    disj_wire_ne ((QRegExt.disjointWires_mono_left hCW35) (rProjAxis_sub_rCore rCore w)) 2 0
  let cTop : Circuit n :=
    cWhTopAxis isInv (rQ 0) (top0 0) (hq_top0 0) ;;ᶜ
      cWhTopAxis isInv (rQ 1) (top0 1) (hq_top0 1) ;;ᶜ
      cWhTopAxis isInv (rQ 2) (top0 2) (hq_top0 2)
  have hsTop0 : CondStageSpec rAct rW35 S_q H_q ((rCoreBlock48 mPayload).embedUnitary
      (DyadicQft64.dyadicDiagUnitary (fullSysCoreWires mPayload) 48 (whStgTopExp hm 0
      isInv))) (.circuit cTop : DynamicCircuit Var n) := by
    refine CondStageSpec.of_diag_circuit rCore rPGTwist hCP rW35 S_q H_q cTop (fun η ↦ (if
      isInv then (-1 : ℤ) else 1) * (2 ^ 45 : ℤ) * ∑ w : Fin 3, ((2 * ((η (rQ w)).val : ℤ) -
      1) * ((η (top0 w)).val : ℤ) + ((η (rQ w)).val : ℤ))) (whStgTopExp hm 0 isInv)
      (fun η ↦ ?_) (fun η _ hHq ↦ ?_)
    · dsimp only [cTop]
      simp only [Circuit.eval_seq, Submonoid.coe_mul, ← Matrix.mulVec_mulVec,
        cWhTopAxis_evolve, Matrix.mulVec_smul, smul_smul, DyadicQft64.dyadicTurn_add]
      refine congrArg (fun x ↦ DyadicQft64.dyadicTurn 48 x • basisKet η) ?_
      rw [Fin.sum_univ_three]
      ring
    · rw [Fin.sum_univ_three, hq_val η 0 hHq, hq_val η 1 hHq, hq_val η 2 hHq]
      unfold whStgTopExp
      dsimp only
      rw [Fin.sum_univ_three]
      have hTopEq : ∀ w : Fin 3, η (top0 w) = (fun q ↦ η (rCore q))
          (rWhFull hm (QRegExt.idReg _) w 7) := by
        intro w; dsimp only [top0]; rw [← rWhFull_idReg_apply hm rCore w 7]
      rw [hTopEq 0, hTopEq 1, hTopEq 2]
      rfl
  have hsRemTop : CondStageSpec rAct rW35 S_q H_q ((rCoreBlock48 mPayload).embedUnitary
      (DyadicQft64.dyadicDiagUnitary (fullSysCoreWires mPayload) 48 (whRemTopExp hm isInv)))
      (.circuit (cWhRemTop isInv hm rCore) : DynamicCircuit Var n) :=
      CondStageSpec.of_diag_circuit rCore rPGTwist hCP rW35 S_q H_q (cWhRemTop isInv hm rCore)
      _ (whRemTopExp hm isInv) (cWhRemTop_evolve isInv hm rCore) (fun _ _ _ ↦ rfl)
  have hw35_0_not_Sq : rW35 0 ∉ S_q := by
    intro hm'
    rcases Finset.mem_union.mp hm' with hS7 | hQ'
    · rcases Finset.mem_union.mp hS7 with hC | h07
      · exact (disj_symm hCW35).apply_not_mem_right 0 hC
      · exact Finset.disjoint_left.mp
          (QRegExt.disjointWires_to_finset (slice_disjoint_of_le rWork 0 7 7 38 (by decide) (by
            decide) (by decide)))
          h07 ((QRegister.image_compose_subset rW38 _) ((QRegister.mem_image rW35 _).mpr ⟨0, rfl⟩))
    · exact (disj_symm hQ35).apply_not_mem_right 0 hQ'
  have hsOr : ∀ w : Fin 3, CondStageSpec rAct rW35 S_q H_q ((rCoreBlock48
      mPayload).embedUnitary (DyadicQft64.dyadicDiagUnitary (fullSysCoreWires mPayload) 48
      (fun γ ↦ (if (!isInv) then (-1 : ℤ) else 1) * (2 ^ 39 : ℤ) * 64 * whStg0RemOrVal hm w
      γ))) (dOrTBit (!isInv) v (rQ w) (rProjAxis rCore w 2) (rW35 0) (hq_p2 w) (hq_w35_0 w)
      (hp2_w35_0 w)) := by
    intro w
    refine CondStageSpec_of_dOrTBit (!isInv) v (rQ w) (rProjAxis rCore w 2) (rW35 0) (hq_p2 w)
      (hq_w35_0 w) (hp2_w35_0 w) rCore rPGTwist hCP rW35 S_q H_q (whStg0RemOrVal hm w)
      ((QRegister.mem_image rW35 _).mpr ⟨0, rfl⟩) (hQ35.apply_not_mem_right w)
      (((QRegExt.disjointWires_mono_left hCW35) (rProjAxis_sub_rCore rCore w)).apply_not_mem_right
        2)
      ((disj_symm hActW35).apply_not_mem_right 0)
      (Finset.mem_union_right _ ((QRegister.mem_image rQ _).mpr ⟨w, rfl⟩))
      (Finset.mem_union_left _ (Finset.mem_union_left _ (rProjAxis_sub_rCore rCore w
      ((QRegister.mem_image _ _).mpr ⟨2, rfl⟩)))) (fun ξ₁ ξ₂ hOut hHq1 ↦ (hHq_congr ξ₁ ξ₂ fun
      u hu ↦ hOut u fun hEq ↦ hw35_0_not_Sq (hEq ▸ hu)).mp hHq1) (fun η hHq ↦ ?_)
    rw [hq_val η w hHq]
    rfl
  let H_qb2 : BitAssignment n → Prop := fun η ↦ JunctionPrefixPruned220.HProjFlag hm rCore rWork
      η ∧ η (rQ 0) = η wf * η (rP0 0) + 1 ∧ η (rQ 1) = η wf * η (rP0 1) ∧ η (rQ 2) = η wf * η
      (rP0 2)
  let H_qb1 : BitAssignment n → Prop := fun η ↦ JunctionPrefixPruned220.HProjFlag hm rCore rWork
      η ∧ η (rQ 0) = η wf * η (rP0 0) + 1 ∧ η (rQ 1) = η wf * η (rP0 1) + 1 ∧ η (rQ 2) = η wf
      * η (rP0 2)
  let H_qb0 : BitAssignment n → Prop := fun η ↦ JunctionPrefixPruned220.HProjFlag hm rCore rWork
      η ∧ η (rQ 0) = η wf * η (rP0 0) + 1 ∧ η (rQ 1) = η wf * η (rP0 1) + 1 ∧ η (rQ 2) = η wf
      * η (rP0 2) + 1
  let H_m0 : BitAssignment n → Prop := fun η ↦
    H_qb0 η ∧ ∀ i : Fin 6, η (rM0 i) = η (rQ 0) * η (low6 0 i)
  let H_m1 : BitAssignment n → Prop := fun η ↦
    H_m0 η ∧ ∀ i : Fin 6, η (rM1 i) = η (rQ 1) * η (low6 1 i)
  let H_m2 : BitAssignment n → Prop := fun η ↦
    H_m1 η ∧ ∀ i : Fin 6, η (rM2 i) = η (rQ 2) * η (low6 2 i)
  let S_m0 : Finset (Wire n) := S_q ∪ rM0.image
  let S_m1 : Finset (Wire n) := S_m0 ∪ rM1.image
  let S_m2 : Finset (Wire n) := S_m1 ∪ rM2.image
  have hq_low6 : ∀ (w : Fin 3) (i : Fin 6), rQ w ≠ low6 w i := fun w i ↦
    (disj_wire_ne ((QRegExt.disjointWires_mono_left hCW_Q) (hLow6_sub w)) i w).symm
  have hQ_M0 : ∀ (w : Fin 3) (i : Fin 6), rQ w ≠ rM0 i := fun w i ↦
    disj_wire_ne ((QRegExt.disjointWires_mono_right hQ35) (QRegister.image_compose_subset rW35 _)) w
      i
  have hQ_M1 : ∀ (w : Fin 3) (i : Fin 6), rQ w ≠ rM1 i := fun w i ↦
    disj_wire_ne ((QRegExt.disjointWires_mono_right hQ35) (QRegister.image_compose_subset rW35 _)) w
      i
  have hQ_M2 : ∀ (w : Fin 3) (i : Fin 6), rQ w ≠ rM2 i := fun w i ↦
    disj_wire_ne ((QRegExt.disjointWires_mono_right hQ35) (QRegister.image_compose_subset rW35 _)) w
      i
  have hLow0_M0 : (low6 0).DisjointWires rM0 :=
    (QRegExt.disjointWires_mono_right ((QRegExt.disjointWires_mono_left hCW35) (hLow6_sub 0)))
      (QRegister.image_compose_subset rW35 _)
  have hLow1_M1 : (low6 1).DisjointWires rM1 :=
    (QRegExt.disjointWires_mono_right ((QRegExt.disjointWires_mono_left hCW35) (hLow6_sub 1)))
      (QRegister.image_compose_subset rW35 _)
  have hLow2_M2 : (low6 2).DisjointWires rM2 :=
    (QRegExt.disjointWires_mono_right ((QRegExt.disjointWires_mono_left hCW35) (hLow6_sub 2)))
      (QRegister.image_compose_subset rW35 _)
  have hM01 : rM0.DisjointWires rM1 :=
    slice_disjoint_of_le rW35 0 6 6 6 (by decide) (by decide) (by decide)
  have hM02 : rM0.DisjointWires rM2 :=
    slice_disjoint_of_le rW35 0 6 12 6 (by decide) (by decide) (by decide)
  have hM12 : rM1.DisjointWires rM2 :=
    slice_disjoint_of_le rW35 6 6 12 6 (by decide) (by decide) (by decide)
  have hT6_subP : rT6.image ⊆ rPGTwist.image := QRegister.image_compose_subset rPGTwist _
  have hM0_T6 : rM0.DisjointWires rT6 :=
    (QRegExt.disjointWires_mono_right ((QRegExt.disjointWires_mono_left (disj_symm hPW35))
      (QRegister.image_compose_subset rW35 _))) hT6_subP
  have hM1_T6 : rM1.DisjointWires rT6 :=
    (QRegExt.disjointWires_mono_right ((QRegExt.disjointWires_mono_left (disj_symm hPW35))
      (QRegister.image_compose_subset rW35 _))) hT6_subP
  have hM2_T6 : rM2.DisjointWires rT6 :=
    (QRegExt.disjointWires_mono_right ((QRegExt.disjointWires_mono_left (disj_symm hPW35))
      (QRegister.image_compose_subset rW35 _))) hT6_subP
  have hM0_Scr : rM0.DisjointWires rScr17 :=
    slice_disjoint_of_le rW35 0 6 18 17 (by decide) (by decide) (by decide)
  have hM1_Scr : rM1.DisjointWires rScr17 :=
    slice_disjoint_of_le rW35 6 6 18 17 (by decide) (by decide) (by decide)
  have hM2_Scr : rM2.DisjointWires rScr17 :=
    slice_disjoint_of_le rW35 12 6 18 17 (by decide) (by decide) (by decide)
  have hT6_Scr : rT6.DisjointWires rScr17 :=
    (QRegExt.disjointWires_mono_right ((QRegExt.disjointWires_mono_left hPW35) hT6_subP))
      (QRegister.image_compose_subset rW35 _)
  have hDisjSm2_T6 : Disjoint S_m2 rT6.image := by
    refine Finset.disjoint_of_subset_right hT6_subP ?_
    have hDisj38 : Disjoint rW38.image rPGTwist.image := (QRegExt.disjointWires_to_finset (disj_symm
      hPW38))
    have hDisj35 : Disjoint rW35.image rPGTwist.image := (QRegExt.disjointWires_to_finset (disj_symm
      hPW35))
    have hDisjC7 : Disjoint S_core7 rPGTwist.image :=
      Finset.disjoint_union_left.mpr
        ⟨(QRegExt.disjointWires_to_finset hCP), (QRegExt.disjointWires_to_finset (disj_symm
          ((QRegExt.disjointWires_mono_right hPW) (QRegister.image_compose_subset rWork _))))⟩
    have hDisjSq : Disjoint S_q rPGTwist.image := Finset.disjoint_union_left.mpr ⟨hDisjC7,
        Finset.disjoint_of_subset_left (QRegister.image_compose_subset rW38 _) hDisj38⟩
    have hDisjSm0 : Disjoint S_m0 rPGTwist.image := Finset.disjoint_union_left.mpr ⟨hDisjSq,
        Finset.disjoint_of_subset_left (QRegister.image_compose_subset rW35 _) hDisj35⟩
    have hDisjSm1 : Disjoint S_m1 rPGTwist.image := Finset.disjoint_union_left.mpr ⟨hDisjSm0,
        Finset.disjoint_of_subset_left (QRegister.image_compose_subset rW35 _) hDisj35⟩
    exact Finset.disjoint_union_left.mpr
      ⟨hDisjSm1, Finset.disjoint_of_subset_left (QRegister.image_compose_subset rW35 _) hDisj35⟩
  let dCsa5 := dCsa3AxisApex (!isInv) 5 v rM0 rM1 rM2 rT6 rScr17
    hM01 hM02 hM12 hM1_T6 hM0_Scr hM1_Scr hM2_Scr hT6_Scr
  let dM2 := dMaskRegWrap 6 v (rQ 2) (low6 2) rM2 (hq_low6 2) (hQ_M2 2) hLow2_M2 dCsa5
  let dM1 := dMaskRegWrap 6 v (rQ 1) (low6 1) rM1 (hq_low6 1) (hQ_M1 1) hLow1_M1 dM2
  let dM0 := dMaskRegWrap 6 v (rQ 0) (low6 0) rM0 (hq_low6 0) (hQ_M0 0) hLow0_M0 dM1
  let dX2 := FusedVepCore288.dPureConj (Circuit.X (rQ 2)) dM0
  let dX1 := FusedVepCore288.dPureConj (Circuit.X (rQ 1)) dX2
  let dLow6 := FusedVepCore288.dPureConj (Circuit.X (rQ 0)) dX1
  have hsCsa5 : CondStageSpec rAct rScr17 S_m2 H_m2 (uApexShift45 (fullSysCoreWires mPayload)
      6 (by decide) (whStg0RemLowShift6 hm isInv)) dCsa5 := by
    refine CondStageSpec.of_dCsa3AxisApex (!isInv) 5 (by decide) v rCore rPGTwist hCP
      rM0 rM1 rM2 rScr17 S_m2 H_m2 (whStg0RemLowShift6 hm isInv)
      hM01 hM02 hM12 hM0_T6 hM1_T6 hM2_T6 hM0_Scr hM1_Scr hM2_Scr hT6_Scr hDisjSm2_T6
      (fun ξ _ ⟨⟨⟨⟨hHp, hQb⟩, hM0_eq⟩, hM1_eq⟩, hM2_eq⟩ ↦ ?_)
    have hsgn_not : (if (!isInv) then (-1 : ℤ) else 1) = -(if isInv then (-1 : ℤ) else 1) := by
      cases isInv <;> rfl
    have hSplitCast : ((regVal rM0 ξ + regVal rM1 ξ + regVal rM2 ξ : ℕ) : ℤ) =
        (regVal rM0 ξ : ℤ) + (regVal rM1 ξ : ℤ) + (regVal rM2 ξ : ℤ) := by
      push_cast; ring
    have hqb_val : ∀ w : Fin 3, ((ξ (rQ w)).val : ℤ) = 1 - wfBitVal hm (fun q ↦ ξ (rCore q)) *
        (((fun q ↦ ξ (rCore q)) (rProjAxis (QRegExt.idReg _) w 0)).val : ℤ) := by
      rcases hQb with ⟨hqb0, hqb1, hqb2⟩
      intro w
      fin_cases w
      · change ((ξ (rQ 0)).val : ℤ) = _
        rw [hqb0, zmod2_add_one_val_int, zmod2_mul_val_int,
          JunctionPrefixPruned220.wfBitVal_of_HProjFlag hm rCore rWork hHp]; rfl
      · change ((ξ (rQ 1)).val : ℤ) = _
        rw [hqb1, zmod2_add_one_val_int, zmod2_mul_val_int,
          JunctionPrefixPruned220.wfBitVal_of_HProjFlag hm rCore rWork hHp]; rfl
      · change ((ξ (rQ 2)).val : ℤ) = _
        rw [hqb2, zmod2_add_one_val_int, zmod2_mul_val_int,
          JunctionPrefixPruned220.wfBitVal_of_HProjFlag hm rCore rWork hHp]; rfl
    rw[hsgn_not, hSplitCast, regVal_masked_eq (rQ 0) (low6 0) rM0 ξ hM0_eq,
        regVal_masked_eq (rQ 1) (low6 1) rM1 ξ hM1_eq,
        regVal_masked_eq (rQ 2) (low6 2) rM2 ξ hM2_eq, hqb_val 0, hqb_val 1, hqb_val 2]
    dsimp only [low6]
    rw [regVal_rWhFull_slice_idReg hm rCore 0 0 6 (by decide) ξ,
      regVal_rWhFull_slice_idReg hm rCore 1 0 6 (by decide) ξ,
      regVal_rWhFull_slice_idReg hm rCore 2 0 6 (by decide) ξ]
    unfold whStg0RemLowShift6
    dsimp only
    rw [Fin.sum_univ_three]
  have hHqb_not35 : ∀ ξ₁ ξ₂ : BitAssignment n,
      (∀ u, u ∉ rW35.image → ξ₁ u = ξ₂ u) → H_qb0 ξ₁ → H_qb0 ξ₂ := by
    intro ξ₁ ξ₂ hOut ⟨hHp1, hQb1⟩
    have hEqSq : ∀ u ∈ S_q, ξ₁ u = ξ₂ u := by
      intro u hu
      refine hOut u fun hm35 ↦ ?_
      rcases Finset.mem_union.mp hu with hS7 | hQ'
      · rcases Finset.mem_union.mp hS7 with hC | h07
        · exact Finset.disjoint_left.mp (QRegExt.disjointWires_to_finset hCW35) hC hm35
        · exact Finset.disjoint_left.mp
            (QRegExt.disjointWires_to_finset (slice_disjoint_of_le rWork 0 7 7 38 (by decide) (by
              decide) (by decide)))
            h07 ((QRegister.image_compose_subset rW38 _) hm35)
      · exact Finset.disjoint_left.mp (QRegExt.disjointWires_to_finset hQ35) hQ' hm35
    refine ⟨(JunctionPrefixPruned220.HProjFlag_congr_S hm rCore rWork
      (Finset.Subset.trans (rHigh_sub_rCore rCore) (Finset.Subset.trans Finset.subset_union_left
        Finset.subset_union_left))
      (Finset.mem_union_left _ hwf_S) ξ₁ ξ₂ hEqSq).mp hHp1, ?_, ?_, ?_⟩
    · rw [← hEqSq (rQ 0) (Finset.mem_union_right _ ((QRegister.mem_image rQ _).mpr ⟨0, rfl⟩)),
        ← hEqSq wf (Finset.mem_union_left _ hwf_S),
        ← hEqSq (rP0 0) (Finset.mem_union_left _ (Finset.mem_union_left _
          (hP0_sub ((QRegister.mem_image rP0 _).mpr ⟨0, rfl⟩))))]
      exact hQb1.1
    · rw [← hEqSq (rQ 1) (Finset.mem_union_right _ ((QRegister.mem_image rQ _).mpr ⟨1, rfl⟩)),
        ← hEqSq wf (Finset.mem_union_left _ hwf_S),
        ← hEqSq (rP0 1) (Finset.mem_union_left _ (Finset.mem_union_left _
          (hP0_sub ((QRegister.mem_image rP0 _).mpr ⟨1, rfl⟩))))]
      exact hQb1.2.1
    · rw [← hEqSq (rQ 2) (Finset.mem_union_right _ ((QRegister.mem_image rQ _).mpr ⟨2, rfl⟩)),
        ← hEqSq wf (Finset.mem_union_left _ hwf_S),
        ← hEqSq (rP0 2) (Finset.mem_union_left _ (Finset.mem_union_left _
          (hP0_sub ((QRegister.mem_image rP0 _).mpr ⟨2, rfl⟩))))]
      exact hQb1.2.2
  have hsM2_raw := CondStageSpec.dMaskRegWrap 6 v (rQ 2) (low6 2) rM2
    (hq_low6 2) (hQ_M2 2) hLow2_M2 rScr17 hM2_Scr
    (((QRegExt.disjointWires_mono_right hQ35) (QRegister.image_compose_subset rW35
      _)).apply_not_mem_right 2)
    ((QRegExt.disjointWires_mono_right ((QRegExt.disjointWires_mono_left hCW35) (hLow6_sub 2)))
      (QRegister.image_compose_subset rW35 _))
    ((QRegExt.disjointWires_mono_right hActW35) (QRegister.image_compose_subset rW35 _))
    (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _
      ((QRegister.mem_image rQ _).mpr ⟨2, rfl⟩))))
    (Finset.Subset.trans (hLow6_sub 2)
      (Finset.Subset.trans Finset.subset_union_left
        (Finset.Subset.trans Finset.subset_union_left
          (Finset.Subset.trans Finset.subset_union_left Finset.subset_union_left))))
    (fun ξ₁ ξ₂ hOut ⟨⟨hQb1, hm01⟩, hm11⟩ ↦ by
      refine ⟨⟨hHqb_not35 ξ₁ ξ₂ (fun u hu ↦ hOut u (fun hm ↦ hu (QRegister.image_compose_subset rW35
        _ hm))) hQb1,
        fun i ↦ ?_⟩, fun i ↦ ?_⟩
      · rw [← hOut (rM0 i) (hM02.apply_not_mem_right i),
          ← hOut (rQ 0) (((QRegExt.disjointWires_mono_right hQ35) (QRegister.image_compose_subset
            rW35 _)).apply_not_mem_right 0),
          ← hOut (low6 0 i) (((QRegExt.disjointWires_mono_right ((QRegExt.disjointWires_mono_left
            hCW35) (hLow6_sub 0)))
            (QRegister.image_compose_subset rW35 _)).apply_not_mem_right i)]
        exact hm01 i
      · rw [← hOut (rM1 i) (hM12.apply_not_mem_right i),
          ← hOut (rQ 1) (((QRegExt.disjointWires_mono_right hQ35) (QRegister.image_compose_subset
            rW35 _)).apply_not_mem_right 1),
          ← hOut (low6 1 i) (((QRegExt.disjointWires_mono_right ((QRegExt.disjointWires_mono_left
            hCW35) (hLow6_sub 1)))
            (QRegister.image_compose_subset rW35 _)).apply_not_mem_right i)]
        exact hm11 i)
    hsCsa5
  have hM2_Scr_eq : (rM2.concat rScr17 hM2_Scr).image = rW23.image :=
    slice_concat_image_eq rW35 (by decide) (by decide) (by decide) hM2_Scr
  have hsM2 : CondStageSpec rAct rW23 S_m1 H_m1
      (uApexShift45 (fullSysCoreWires mPayload) 6 (by decide) (whStg0RemLowShift6 hm isInv)) dM2 :=
    hsM2_raw.widen_workspace (by rw [hM2_Scr_eq]) (by rw [hM2_Scr_eq])
  have hM1_W23 : rM1.DisjointWires rW23 :=
    slice_disjoint_of_le rW35 6 6 12 23 (by decide) (by decide) (by decide)
  have hsM1_raw := CondStageSpec.dMaskRegWrap 6 v (rQ 1) (low6 1) rM1
    (hq_low6 1) (hQ_M1 1) hLow1_M1 rW23 hM1_W23
    (((QRegExt.disjointWires_mono_right hQ35) (QRegister.image_compose_subset rW35
      _)).apply_not_mem_right 1)
    ((QRegExt.disjointWires_mono_right ((QRegExt.disjointWires_mono_left hCW35) (hLow6_sub 1)))
      (QRegister.image_compose_subset rW35 _))
    ((QRegExt.disjointWires_mono_right hActW35) (QRegister.image_compose_subset rW35 _))
    (Finset.mem_union_left _ (Finset.mem_union_right _
      ((QRegister.mem_image rQ _).mpr ⟨1, rfl⟩)))
    (Finset.Subset.trans (hLow6_sub 1)
      (Finset.Subset.trans Finset.subset_union_left
        (Finset.Subset.trans Finset.subset_union_left Finset.subset_union_left)))
    (fun ξ₁ ξ₂ hOut ⟨hQb1, hm01⟩ ↦
      ⟨hHqb_not35 ξ₁ ξ₂ (fun u hu ↦ hOut u (fun hm ↦ hu (QRegister.image_compose_subset rW35 _ hm)))
        hQb1,
       fun i ↦ by
        rw [← hOut (rM0 i) (hM01.apply_not_mem_right i),
          ← hOut (rQ 0) (((QRegExt.disjointWires_mono_right hQ35) (QRegister.image_compose_subset
            rW35 _)).apply_not_mem_right 0),
          ← hOut (low6 0 i) (((QRegExt.disjointWires_mono_right ((QRegExt.disjointWires_mono_left
            hCW35) (hLow6_sub 0)))
            (QRegister.image_compose_subset rW35 _)).apply_not_mem_right i)]
        exact hm01 i⟩)
    hsM2
  have hM1_W23_eq : (rM1.concat rW23 hM1_W23).image = rW29.image :=
    slice_concat_image_eq rW35 (by decide) (by decide) (by decide) hM1_W23
  have hsM1 : CondStageSpec rAct rW29 S_m0 H_m0
      (uApexShift45 (fullSysCoreWires mPayload) 6 (by decide) (whStg0RemLowShift6 hm isInv)) dM1 :=
    hsM1_raw.widen_workspace (by rw [hM1_W23_eq]) (by rw [hM1_W23_eq])
  have hM0_W29 : rM0.DisjointWires rW29 :=
    slice_disjoint_of_le rW35 0 6 6 29 (by decide) (by decide) (by decide)
  have hsM0_raw := CondStageSpec.dMaskRegWrap 6 v (rQ 0) (low6 0) rM0 (hq_low6 0) (hQ_M0 0)
      hLow0_M0 rW29 hM0_W29 (((QRegExt.disjointWires_mono_right hQ35)
        (QRegister.image_compose_subset rW35
      _)).apply_not_mem_right 0) ((QRegExt.disjointWires_mono_right
        ((QRegExt.disjointWires_mono_left hCW35) (hLow6_sub 0)))
      (QRegister.image_compose_subset rW35 _))
      ((QRegExt.disjointWires_mono_right hActW35) (QRegister.image_compose_subset rW35 _))
      (Finset.mem_union_right _ ((QRegister.mem_image rQ _).mpr ⟨0, rfl⟩))
      (Finset.Subset.trans (hLow6_sub 0) (Finset.Subset.trans Finset.subset_union_left
      Finset.subset_union_left)) (fun ξ₁ ξ₂ hOut hQb1 ↦ hHqb_not35 ξ₁ ξ₂ (fun u hu ↦ hOut u
      (fun hm ↦ hu (QRegister.image_compose_subset rW35 _ hm))) hQb1) hsM1
  have hM0_W29_eq : (rM0.concat rW29 hM0_W29).image = rW35.image := by
    rw [slice_concat_image_eq rW35 (by decide) (by decide) (by decide) hM0_W29]
    ext u; simp only [QRegister.mem_image]
    constructor
    · rintro ⟨i, rfl⟩; rw [slice_apply_eq]; exact ⟨⟨0 + i.val, by have := i.isLt; omega⟩, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨i, by rw [slice_apply_eq]; apply congrArg rW35; apply Fin.ext; dsimp; omega⟩
  have hsM0 : CondStageSpec rAct rW35 S_q H_qb0
      (uApexShift45 (fullSysCoreWires mPayload) 6 (by decide) (whStg0RemLowShift6 hm isInv)) dM0 :=
    hsM0_raw.widen_workspace (by rw [hM0_W29_eq]) (by rw [hM0_W29_eq])
  have hq01 : rQ 0 ≠ rQ 1 := reg_ne_of_ne rQ (by decide)
  have hq02 : rQ 0 ≠ rQ 2 := reg_ne_of_ne rQ (by decide)
  have hq12 : rQ 1 ≠ rQ 2 := reg_ne_of_ne rQ (by decide)
  have hHp_notQ : ∀ (w : Fin 3) (ξ₁ ξ₂ : BitAssignment n), (∀ u, u ≠ rQ w → ξ₁ u = ξ₂ u) →
      JunctionPrefixPruned220.HProjFlag hm rCore rWork ξ₁ → JunctionPrefixPruned220.HProjFlag hm
      rCore rWork ξ₂ := by
    intro w ξ₁ ξ₂ hOut h1
    refine (JunctionPrefixPruned220.HProjFlag_congr_S hm rCore rWork
      (Finset.Subset.trans (rHigh_sub_rCore rCore) Finset.subset_union_left) hwf_S ξ₁ ξ₂ fun u hu ↦
        hOut u fun hEq ↦ ?_).mp h1
    subst hEq
    rcases Finset.mem_union.mp hu with hC | h07
    · exact (disj_symm hCW_Q).apply_not_mem_right w hC
    · exact Finset.disjoint_left.mp
        (QRegExt.disjointWires_to_finset (slice_disjoint_of_le rWork 0 7 7 38 (by decide) (by
          decide) (by decide)))
        h07 ((QRegister.image_compose_subset rW38 _) ((QRegister.mem_image rQ _).mpr ⟨w, rfl⟩))
  have hsX2 : CondStageSpec rAct rW35 S_q H_qb1
      (uApexShift45 (fullSysCoreWires mPayload) 6 (by decide) (whStg0RemLowShift6 hm isInv)) dX2 :=
    CondStageSpec_dPureConjX (rQ 2)
      (hQ35.apply_not_mem_right 2)
      ((disj_symm ((QRegExt.disjointWires_mono_right hActW38) (QRegister.image_compose_subset rW38
        _))).apply_not_mem_right 2)
      (Finset.mem_union_right _ ((QRegister.mem_image rQ _).mpr ⟨2, rfl⟩))
      (H_outer := H_qb1)
      (fun ξ ⟨hHp, h0, h1, h2⟩ ↦ ⟨hHp_notQ 2 ξ _ (fun u hu ↦ (Function.update_of_ne hu _ ξ).symm)
        hHp,
        by rw [Function.update_of_ne hq02, Function.update_of_ne (hwf_Q 2),
            Function.update_of_ne (disj_wire_ne ((QRegExt.disjointWires_mono_left hCW_Q) hP0_sub) 0
              2), h0],
        by rw [Function.update_of_ne hq12, Function.update_of_ne (hwf_Q 2),
            Function.update_of_ne (disj_wire_ne ((QRegExt.disjointWires_mono_left hCW_Q) hP0_sub) 1
              2), h1],
        by rw [Function.update_self, Function.update_of_ne (hwf_Q 2),
            Function.update_of_ne (disj_wire_ne ((QRegExt.disjointWires_mono_left hCW_Q) hP0_sub) 2
              2), h2]⟩)
      hsM0
  have hsX1 : CondStageSpec rAct rW35 S_q H_qb2
      (uApexShift45 (fullSysCoreWires mPayload) 6 (by decide) (whStg0RemLowShift6 hm isInv)) dX1 :=
    CondStageSpec_dPureConjX (rQ 1)
      (hQ35.apply_not_mem_right 1)
      ((disj_symm ((QRegExt.disjointWires_mono_right hActW38) (QRegister.image_compose_subset rW38
        _))).apply_not_mem_right 1)
      (Finset.mem_union_right _ ((QRegister.mem_image rQ _).mpr ⟨1, rfl⟩))
      (H_outer := H_qb2)
      (fun ξ ⟨hHp, h0, h1, h2⟩ ↦ ⟨hHp_notQ 1 ξ _ (fun u hu ↦ (Function.update_of_ne hu _ ξ).symm)
        hHp,
        by rw [Function.update_of_ne hq01, Function.update_of_ne (hwf_Q 1),
            Function.update_of_ne (disj_wire_ne ((QRegExt.disjointWires_mono_left hCW_Q) hP0_sub) 0
              1), h0],
        by rw [Function.update_self, Function.update_of_ne (hwf_Q 1),
            Function.update_of_ne (disj_wire_ne ((QRegExt.disjointWires_mono_left hCW_Q) hP0_sub) 1
              1), h1],
        by rw [Function.update_of_ne hq12.symm, Function.update_of_ne (hwf_Q 1),
            Function.update_of_ne (disj_wire_ne ((QRegExt.disjointWires_mono_left hCW_Q) hP0_sub) 2
              1), h2]⟩)
      hsX2
  have hsLow6 : CondStageSpec rAct rW35 S_q H_q
      (uApexShift45 (fullSysCoreWires mPayload) 6 (by decide) (whStg0RemLowShift6 hm isInv))
        dLow6 :=
    CondStageSpec_dPureConjX (rQ 0)
      (hQ35.apply_not_mem_right 0)
      ((disj_symm ((QRegExt.disjointWires_mono_right hActW38) (QRegister.image_compose_subset rW38
        _))).apply_not_mem_right 0)
      (Finset.mem_union_right _ ((QRegister.mem_image rQ _).mpr ⟨0, rfl⟩))
      (H_outer := H_q)
      (fun ξ ⟨hHp, hQ⟩ ↦ ⟨hHp_notQ 0 ξ _ (fun u hu ↦ (Function.update_of_ne hu _ ξ).symm) hHp,
        by rw [Function.update_self, Function.update_of_ne (hwf_Q 0),
            Function.update_of_ne (disj_wire_ne ((QRegExt.disjointWires_mono_left hCW_Q) hP0_sub) 0
              0), hQ 0],
        by rw [Function.update_of_ne hq01.symm, Function.update_of_ne (hwf_Q 0),
            Function.update_of_ne (disj_wire_ne ((QRegExt.disjointWires_mono_left hCW_Q) hP0_sub) 1
              0), hQ 1],
        by rw [Function.update_of_ne hq02.symm, Function.update_of_ne (hwf_Q 0),
            Function.update_of_ne (disj_wire_ne ((QRegExt.disjointWires_mono_left hCW_Q) hP0_sub) 2
              0), hQ 2]⟩)
      hsX1
  have hsBody_raw := hsTop0.seq hActW35 hHq_congr (hsRemTop.seq hActW35 hHq_congr ((hsOr
      0).seq hActW35 hHq_congr ((hsOr 1).seq hActW35 hHq_congr ((hsOr 2).seq hActW35 hHq_congr
      hsLow6))))
  have hsBody : CondStageSpec rAct rW35 S_q H_q
      (uWhRemCat hm isInv * uWhStgCat hm 0 isInv) _ :=
    hsBody_raw.congr_unitary (by
      rw [uWhRemCat_mul_uWhStgCat0_eq hm isInv]
      simp only [mul_assoc])
  have hsOuter := CondStageSpec.dMaskRegWrap 3 v wf rP0 rQ
    (fun w ↦ (disj_wire_ne ((QRegExt.disjointWires_mono_left hCW) hP0_sub) w 6).symm)
    hwf_Q
    ((QRegExt.disjointWires_mono_left hCW_Q) hP0_sub)
    rW35 hQ35
    hwf_not35
    ((QRegExt.disjointWires_mono_left hCW35) hP0_sub)
    ((QRegExt.disjointWires_mono_right hActW38) (QRegister.image_compose_subset rW38 _))
    hwf_S
    (Finset.Subset.trans hP0_sub Finset.subset_union_left)
    (fun ξ₁ ξ₂ hOut hHp1 ↦ (JunctionPrefixPruned220.HProjFlag_congr_S hm rCore rWork
      (Finset.Subset.trans (rHigh_sub_rCore rCore) Finset.subset_union_left) hwf_S ξ₁ ξ₂ fun u hu ↦
        hOut u fun hm' ↦ by
          rcases Finset.mem_union.mp hu with hC | h07
          · exact Finset.disjoint_left.mp (QRegExt.disjointWires_to_finset hCW_Q) hC hm'
          · exact Finset.disjoint_left.mp
              (QRegExt.disjointWires_to_finset (slice_disjoint_of_le rWork 0 7 7 38 (by decide) (by
                decide) (by decide)))
              h07 ((QRegister.image_compose_subset rW38 _) hm')).mp hHp1)
    hsBody
  have hQ35_eq : (rQ.concat rW35 hQ35).image = rW38.image := by
    rw [slice_concat_image_eq rW38 (by decide) (by decide) (by decide) hQ35]
    ext u; simp only [QRegister.mem_image]
    constructor
    · rintro ⟨i, rfl⟩; rw [slice_apply_eq]; exact ⟨⟨0 + i.val, by have := i.isLt; omega⟩, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨i, by rw [slice_apply_eq]; apply congrArg rW38; apply Fin.ext; dsimp; omega⟩
  exact hsOuter.widen_workspace (by rw [hQ35_eq]) (by rw [hQ35_eq])
lemma dWhStg0Rem_3D_biSpec_Pos45 {mPayload : ℕ} (isInv : Bool) (hm : 22 ≤ mPayload)
    {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ} (v : Var)
    (rCore : QRegister (fullSysCoreWires mPayload) n) (rPGTwist : QRegister 48 n)
    (rWork : QRegister JunctionPrefixPruned220.mWork45 n) (hCP : rCore.DisjointWires rPGTwist)
    (hCW : rCore.DisjointWires rWork) (hPW : rPGTwist.DisjointWires rWork) : CondStageSpec
    (rCore.concat rPGTwist hCP) (rWork.slice 7 38 mw_slice_7_38_le_Pos45) ((rHigh rCore).image
    ∪ (rWork.slice 0 7 mw_slice_0_7_le_Pos45).image)
    (JunctionPrefixPruned220.HProjFlag hm rCore rWork) (if isInv then (uWhRemCat hm false *
    uWhStgCat hm 0 false)⁻¹ else uWhRemCat hm false * uWhStgCat hm 0 false)
    (dWhStg0Rem_3D_Pos45 isInv hm v rCore rPGTwist rWork hCP hCW hPW) := by
  cases isInv
  · exact dWhStg0Rem_3D_spec_Pos45 false hm v rCore rPGTwist rWork hCP hCW hPW
  · refine (dWhStg0Rem_3D_spec_Pos45 true hm v rCore rPGTwist rWork hCP hCW hPW).congr_unitary ?_
    simp only [↓reduceIte, _root_.mul_inv_rev, uWhStgCat_inv_eq, uWhRemCat_inv_eq]
    let kSys := fullSysCoreWires mPayload
    let rCB := rCoreBlock48 mPayload
    unfold uWhStgCat uWhRemCat
    dsimp only [Fin.val_zero, Nat.sub_zero]
    have hComm1 :
        rCB.embedUnitary (DyadicQft64.dyadicDiagUnitary kSys 48 (whRemTopExp hm true)) *
          uApexShift45 kSys 7 (by decide) (whStgLowShift hm 0 true) =
        uApexShift45 kSys 7 (by decide) (whStgLowShift hm 0 true) *
          rCB.embedUnitary (DyadicQft64.dyadicDiagUnitary kSys 48 (whRemTopExp hm true)) :=
      uApexShift45_comm_coreDiag kSys 7 (by decide) 48
        (whRemTopExp hm true) (whStgLowShift hm 0 true)
    have hComm2 :
        rCB.embedUnitary (DyadicQft64.dyadicDiagUnitary kSys 48 (whStgTopExp hm 0 true)) *
          uApexShift45 kSys 7 (by decide) (whRemLowShift hm true) =
        uApexShift45 kSys 7 (by decide) (whRemLowShift hm true) *
          rCB.embedUnitary (DyadicQft64.dyadicDiagUnitary kSys 48 (whStgTopExp hm 0 true)) :=
      uApexShift45_comm_coreDiag kSys 7 (by decide) 48
        (whStgTopExp hm 0 true) (whRemLowShift hm true)
    have hShiftComm : uApexShift45 kSys 7 (by decide) (whStgLowShift hm 0 true) * uApexShift45
        kSys 7 (by decide) (whRemLowShift hm true) = uApexShift45 kSys 7 (by decide)
        (whRemLowShift hm true) * uApexShift45 kSys 7 (by decide) (whStgLowShift hm 0 true)
        := by
      rw [uApexShiftA_mul, uApexShiftA_mul]
      exact uApexShift45_congr (by decide) (by decide) rfl (fun γ ↦ add_comm _ _)
    have hDiagComm :
        rCB.embedUnitary (DyadicQft64.dyadicDiagUnitary kSys 48 (whStgTopExp hm 0 true)) *
          rCB.embedUnitary (DyadicQft64.dyadicDiagUnitary kSys 48 (whRemTopExp hm true)) =
        rCB.embedUnitary (DyadicQft64.dyadicDiagUnitary kSys 48 (whRemTopExp hm true)) *
          rCB.embedUnitary (DyadicQft64.dyadicDiagUnitary kSys 48 (whStgTopExp hm 0 true)) := by
      have hD : DyadicQft64.dyadicDiagUnitary kSys 48 (whStgTopExp hm 0 true) *
          DyadicQft64.dyadicDiagUnitary kSys 48 (whRemTopExp hm true) =
          DyadicQft64.dyadicDiagUnitary kSys 48 (whRemTopExp hm true) *
          DyadicQft64.dyadicDiagUnitary kSys 48 (whStgTopExp hm 0 true) := by
        rw [dyadicDiagUnitary_mul, dyadicDiagUnitary_mul]
        apply dyadicDiagUnitary_congr
        intro γ
        exact add_comm _ _
      rw [← rCB.embedUnitary_mul, hD, rCB.embedUnitary_mul]
    calc
      (uApexShift45 kSys 7 (by decide) (whRemLowShift hm true) *
          rCB.embedUnitary (DyadicQft64.dyadicDiagUnitary kSys 48 (whRemTopExp hm true))) *
        (uApexShift45 kSys 7 (by decide) (whStgLowShift hm 0 true) *
          rCB.embedUnitary (DyadicQft64.dyadicDiagUnitary kSys 48 (whStgTopExp hm 0 true)))
        = (uApexShift45 kSys 7 (by decide) (whRemLowShift hm true) *
            uApexShift45 kSys 7 (by decide) (whStgLowShift hm 0 true)) *
          (rCB.embedUnitary (DyadicQft64.dyadicDiagUnitary kSys 48 (whRemTopExp hm true)) *
            rCB.embedUnitary (DyadicQft64.dyadicDiagUnitary kSys 48 (whStgTopExp hm 0 true))) := by
          rw [mul_assoc (uApexShift45 kSys 7 _ (whRemLowShift hm true)),
            ← mul_assoc (rCB.embedUnitary _), hComm1]
          simp only [mul_assoc]
      _ = (uApexShift45 kSys 7 (by decide) (whStgLowShift hm 0 true) *
            uApexShift45 kSys 7 (by decide) (whRemLowShift hm true)) *
          (rCB.embedUnitary (DyadicQft64.dyadicDiagUnitary kSys 48 (whStgTopExp hm 0 true)) *
            rCB.embedUnitary (DyadicQft64.dyadicDiagUnitary kSys 48 (whRemTopExp hm true))) := by
          rw [hShiftComm, hDiagComm]
      _ = (uApexShift45 kSys 7 (by decide) (whStgLowShift hm 0 true) *
            rCB.embedUnitary (DyadicQft64.dyadicDiagUnitary kSys 48 (whStgTopExp hm 0 true))) *
          (uApexShift45 kSys 7 (by decide) (whRemLowShift hm true) *
            rCB.embedUnitary (DyadicQft64.dyadicDiagUnitary kSys 48 (whRemTopExp hm true))) := by
          rw [mul_assoc (uApexShift45 kSys 7 _ (whStgLowShift hm 0 true)),
            ← mul_assoc (uApexShift45 kSys 7 _ (whRemLowShift hm true)), ← hComm2]
          simp only [mul_assoc]
/-- `45`-wire inner `558-T` Hadamard-tail-cut projectile QFT circuit
`dProj3DHadCut558_16Inner_Pos45`. -/
noncomputable def dProj3DHadCut558_16Inner_Pos45 {mPayload : ℕ} (isInv : Bool) (hm : 22 ≤ mPayload)
    {Var : Type} {n : ℕ} (v : Var)
    (rCore : QRegister (fullSysCoreWires mPayload) n)
    (rPGTwist : QRegister 48 n) (rWork : QRegister JunctionPrefixPruned220.mWork45 n)
    (hCW : rCore.DisjointWires rWork) (hPW : rPGTwist.DisjointWires rWork)
    (hCP : rCore.DisjointWires rPGTwist) : DynamicCircuit Var n :=
  let rCS := rCoreSwap_Pos45 hm rCore rWork hCW
  let rWS := rWorkSwap_Pos45 hm rCore rWork hCW
  let hCSP := rCoreSwap_disj_rPGTwist_Pos45 hm rCore rPGTwist rWork hCP hCW hPW
  let hCSWS := rCoreSwap_disj_rWorkSwap_Pos45 hm rCore rWork hCW
  let hPWS := rPGTwist_disj_rWorkSwap_Pos45 hm rCore rPGTwist rWork hCP hCW hPW
  let c7 := dWhStg7_3D_Pos45 isInv hm v rCS rWS hCSWS
  let cH (m : Fin 8) := dHUncond_3D isInv m (Var := Var) rCS
  let cS (k : Fin 7) := dWhStg_3D_Pos45 isInv hm v k rCS rPGTwist rWS hCSP hCSWS hPWS
  let c0Rem := dWhStg0Rem_3D_Pos45 isInv hm v rCS rPGTwist rWS hCSP hCSWS hPWS
  dBiSeq isInv (dBiSeq isInv (dBiSeq isInv (dBiSeq isInv
  (dBiSeq isInv (dBiSeq isInv (dBiSeq isInv (dBiSeq isInv
  (dBiSeq isInv (dBiSeq isInv (dBiSeq isInv (dBiSeq isInv
  (dBiSeq isInv (dBiSeq isInv
    c7 (cH 7)) (cS 6)) (cH 6)) (cS 5)) (cH 5)) (cS 4)) (cH 4)) (cS 3))
    (cH 3)) (cS 2)) (cH 2)) (cS 1)) (cH 1)) c0Rem
/-- `45`-wire `558-T` Hadamard-tail-cut projectile QFT pre-tail circuit
`dProj3DHadCut558_16_Pos45`. -/
noncomputable def dProj3DHadCut558_16_Pos45 {mPayload : ℕ} (isInv : Bool) (hm : 22 ≤ mPayload)
    {Var : Type} {n : ℕ} (v : Var) (rCore : QRegister (fullSysCoreWires mPayload) n)
    (rPGTwist : QRegister 48 n) (rWork : QRegister JunctionPrefixPruned220.mWork45 n)
    (hCP : rCore.DisjointWires rPGTwist) (hCW : rCore.DisjointWires rWork)
    (hPW : rPGTwist.DisjointWires rWork) : DynamicCircuit Var n :=
    FusedVepCore288.dPureConj (cX234_Pos45 rWork) (dProj3DHadCut558_16Inner_Pos45 isInv hm
    v rCore rPGTwist rWork hCW hPW hCP)
/-- `45`-wire `558-T` Hadamard-tail-cut projectile QFT circuit `dProj3DHadCut558_Pos45`. -/
noncomputable def dProj3DHadCut558_Pos45 {mPayload : ℕ} (isInv : Bool) (hm : 22 ≤ mPayload)
    {Var : Type} {n : ℕ} (v : Var) (rCore : QRegister (fullSysCoreWires mPayload) n)
    (rPGTwist : QRegister 48 n) (rWork : QRegister JunctionPrefixPruned220.mWork45 n)
    (hCP : rCore.DisjointWires rPGTwist) (hCW : rCore.DisjointWires rWork)
    (hPW : rPGTwist.DisjointWires rWork) : DynamicCircuit Var n := dBiSeq isInv
    (dProj3DHadCut558_16_Pos45 isInv hm v rCore rPGTwist rWork hCP hCW hPW)
    (dTail_3D isInv rCore)
@[simp]
theorem count_dProj3DHadCut558_toff_Pos45 {mPayload : ℕ} (isInv : Bool) (hm : 22 ≤ mPayload)
    {Var : Type} {n : ℕ} (v : Var)
    (rCore : QRegister (fullSysCoreWires mPayload) n)
    (rPGTwist : QRegister 48 n) (rWork : QRegister JunctionPrefixPruned220.mWork45 n)
    (hCP : rCore.DisjointWires rPGTwist)
    (hCW : rCore.DisjointWires rWork) (hPW : rPGTwist.DisjointWires rWork) :
    (dProj3DHadCut558_Pos45 isInv hm (Var := Var) v rCore rPGTwist rWork hCP hCW hPW).count .TOFF =
      0 := by
  unfold dProj3DHadCut558_Pos45 dProj3DHadCut558_16_Pos45 dProj3DHadCut558_16Inner_Pos45
  rw [count_dBiSeq_toff isInv ?_ (count_dTail_3D_toff ..)]
  rw [FusedVepCore288.count_dPureConj_toff _ (by simp [cX234_Pos45, Circuit.count_seq])]
  exact count_dBiSeq_toff isInv (count_dBiSeq_toff isInv (count_dBiSeq_toff isInv
    (count_dBiSeq_toff isInv (count_dBiSeq_toff isInv (count_dBiSeq_toff isInv
    (count_dBiSeq_toff isInv (count_dBiSeq_toff isInv (count_dBiSeq_toff isInv
    (count_dBiSeq_toff isInv (count_dBiSeq_toff isInv (count_dBiSeq_toff isInv
    (count_dBiSeq_toff isInv (count_dBiSeq_toff isInv (count_dWhStg7_3D_toff ..)
    (count_dHUncond_3D_toff ..)) (count_dWhStg_3D_toff ..)) (count_dHUncond_3D_toff ..))
    (count_dWhStg_3D_toff ..)) (count_dHUncond_3D_toff ..)) (count_dWhStg_3D_toff ..))
    (count_dHUncond_3D_toff ..)) (count_dWhStg_3D_toff ..)) (count_dHUncond_3D_toff ..))
    (count_dWhStg_3D_toff ..)) (count_dHUncond_3D_toff ..)) (count_dWhStg_3D_toff ..))
    (count_dHUncond_3D_toff ..)) (count_dWhStg0Rem_3D_toff_Pos45 ..)
@[simp]
theorem count_dProj3DHadCut558_t_Pos45 {mPayload : ℕ} (isInv : Bool) (hm : 22 ≤ mPayload)
    {Var : Type} {n : ℕ} (v : Var)
    (rCore : QRegister (fullSysCoreWires mPayload) n)
    (rPGTwist : QRegister 48 n) (rWork : QRegister JunctionPrefixPruned220.mWork45 n)
    (hCP : rCore.DisjointWires rPGTwist)
    (hCW : rCore.DisjointWires rWork) (hPW : rPGTwist.DisjointWires rWork) :
    (dProj3DHadCut558_Pos45 isInv hm (Var := Var) v rCore rPGTwist rWork hCP hCW hPW).count .T =
      558 := by
  unfold dProj3DHadCut558_Pos45 dProj3DHadCut558_16_Pos45 dProj3DHadCut558_16Inner_Pos45
  rw [count_dBiSeq_t, count_dTail_3D_t,
    FusedVepCore288.count_dPureConj_t _ (by simp [cX234_Pos45, Circuit.count_seq])]
  simp only [count_dBiSeq_t, count_dWhStg7_3D_t, count_dHUncond_3D_t,
    count_dWhStg_3D_t, count_dWhStg0Rem_3D_t_Pos45]
  rfl
theorem dProj3DHadCut558_16_spec_Pos45 {mPayload : ℕ} (isInv : Bool) (hm : 22 ≤ mPayload)
    {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ} (v : Var)
    (rCore : QRegister (fullSysCoreWires mPayload) n)
    (rPGTwist : QRegister 48 n) (rWork : QRegister JunctionPrefixPruned220.mWork45 n)
    (hCP : rCore.DisjointWires rPGTwist)
    (hCW : rCore.DisjointWires rWork) (hPW : rPGTwist.DisjointWires rWork) :
    CondStageSpec (rCore.concat rPGTwist hCP)
      (rWork.slice 2 43 mw_slice_2_43_le_Pos45)
      ((rHigh rCore).image ∪ (rWork.slice 0 2 mw_slice_0_2_le_Pos45).image)
      (HPosBranchFlag_Pos45 rCore rWork)
      (if isInv then (uProj3DHadCutPre16Cat hm)⁻¹ else uProj3DHadCutPre16Cat hm)
      (dProj3DHadCut558_16_Pos45 isInv hm (Var := Var) v rCore rPGTwist rWork hCP hCW hPW) := by
  let rCS := rCoreSwap_Pos45 hm rCore rWork hCW
  let rWS := rWorkSwap_Pos45 hm rCore rWork hCW
  let hCSP := rCoreSwap_disj_rPGTwist_Pos45 hm rCore rPGTwist rWork hCP hCW hPW
  let hCSWS := rCoreSwap_disj_rWorkSwap_Pos45 hm rCore rWork hCW
  let hPWS := rPGTwist_disj_rWorkSwap_Pos45 hm rCore rPGTwist rWork hCP hCW hPW
  have hActW_in : (rCS.concat rPGTwist hCSP).DisjointWires
      (rWS.slice 7 38 mw_slice_7_38_le_Pos45) := QRegExt.disjointWires_concat_left
      ((QRegExt.disjointWires_mono_right hCSWS) (QRegister.image_compose_subset rWS _))
      ((QRegExt.disjointWires_mono_right hPWS) (QRegister.image_compose_subset rWS _))
  have hH_in := JunctionPrefixPruned220.HProjFlag_congr_S
    (S := (rHigh rCS).image ∪ (rWS.slice 0 7 mw_slice_0_7_le_Pos45).image)
    hm rCS rWS Finset.subset_union_left
    (Finset.mem_union_right _ (reg_mem_slice_b2 rWS 0 7 mw_slice_0_7_le_Pos45 6
      (by dsimp [JunctionPrefixPruned220.mWork45]; omega) (by
        dsimp [JunctionPrefixPruned220.mWork45]; omega)))
  have hs7 := dWhStg7_3D_biSpec_Pos45 isInv hm (Var := Var) v rCS rPGTwist rWS hCSP hCSWS hPWS
  have hsH (m : Fin 8) := dHUncond_3D_spec_Pos45 isInv hm m (Var := Var) rCS rPGTwist rWS hCSP hCSWS
  have hsS (k : Fin 7) := dWhStg_3D_biSpec_Pos45 isInv hm (Var := Var) v k rCS rPGTwist rWS hCSP
    hCSWS hPWS
  have hs0Rem := dWhStg0Rem_3D_biSpec_Pos45 isInv hm (Var := Var) v rCS rPGTwist rWS hCSP hCSWS hPWS
  have hs16_raw := CondStageSpec.dBiSeq hActW_in hH_in isInv (CondStageSpec.dBiSeq hActW_in
      hH_in isInv (CondStageSpec.dBiSeq hActW_in hH_in isInv (CondStageSpec.dBiSeq hActW_in
      hH_in isInv (CondStageSpec.dBiSeq hActW_in hH_in isInv (CondStageSpec.dBiSeq hActW_in
      hH_in isInv (CondStageSpec.dBiSeq hActW_in hH_in isInv (CondStageSpec.dBiSeq hActW_in
      hH_in isInv (CondStageSpec.dBiSeq hActW_in hH_in isInv (CondStageSpec.dBiSeq hActW_in
      hH_in isInv (CondStageSpec.dBiSeq hActW_in hH_in isInv (CondStageSpec.dBiSeq hActW_in
      hH_in isInv (CondStageSpec.dBiSeq hActW_in hH_in isInv (CondStageSpec.dBiSeq hActW_in
      hH_in isInv hs7 (hsH 7)) (hsS 6)) (hsH 6)) (hsS 5)) (hsH 5)) (hsS 4)) (hsH 4)) (hsS 3))
      (hsH 3)) (hsS 2)) (hsH 2)) (hsS 1)) (hsH 1)) hs0Rem
  have hs16 : CondStageSpec (rCS.concat rPGTwist hCSP) (rWS.slice 7 38 mw_slice_7_38_le_Pos45)
      ((rHigh rCS).image ∪ (rWS.slice 0 7 mw_slice_0_7_le_Pos45).image)
      (JunctionPrefixPruned220.HProjFlag hm rCS rWS) (if isInv then (uProj3DVepHadPre16Cat hm)⁻¹
      else uProj3DVepHadPre16Cat hm) (dProj3DHadCut558_16Inner_Pos45 isInv hm v rCore rPGTwist
      rWork hCW hPW hCP) :=
    hs16_raw.congr_unitary (by
      cases isInv <;> simp only [↓reduceIte, Bool.false_eq_true, uProj3DVepHadPre16Cat, mul_assoc])
  obtain ⟨u_in, hw_in0, hD_in, hK_in⟩ := hs16.exists_u
  have hSlEq := rWorkSwap_slice7_38_eq_Pos45 hm rCore rWork hCW
  have hw_in : CleanUnitaryWp (rWork.slice 7 38 mw_slice_7_38_le_Pos45) u_in
      (dProj3DHadCut558_16Inner_Pos45 isInv hm v rCore rPGTwist rWork hCW hPW hCP) := hSlEq ▸ hw_in0
  have hDisjX : Disjoint (cX234_Pos45 rWork).support (rWork.slice 7 38 mw_slice_7_38_le_Pos45).image
    := by
    unfold cX234_Pos45
    refine disj_support_seq (disj_support_X _ (reg_not_mem_slice_b2 rWork 7 38
      mw_slice_7_38_le_Pos45 2 (Or.inl (by dsimp [JunctionPrefixPruned220.mWork45]; omega))))
      (disj_support_seq
        (disj_support_X _ (reg_not_mem_slice_b2 rWork 7 38 mw_slice_7_38_le_Pos45 3 (Or.inl (by
          dsimp [JunctionPrefixPruned220.mWork45]; omega))))
        (disj_support_X _ (reg_not_mem_slice_b2 rWork 7 38 mw_slice_7_38_le_Pos45 4 (Or.inl (by
          dsimp [JunctionPrefixPruned220.mWork45]; omega)))))
  have hw_conj := CleanUnitaryWp.dPureConj (cX234_Pos45 rWork)
    (rWork.slice 7 38 mw_slice_7_38_le_Pos45) hDisjX hw_in
  have hSub38_43 : (rWork.slice 7 38 mw_slice_7_38_le_Pos45).image ⊆
      (rWork.slice 2 43 mw_slice_2_43_le_Pos45).image := by
    intro w hw; rcases (QRegister.mem_image _ w).mp hw with ⟨j, rfl⟩
    exact (QRegister.mem_image _ _).mpr ⟨⟨5 + j.val, by omega⟩,
      congrArg rWork (Fin.ext (by dsimp [QRegister.slice]; omega))⟩
  let S_in := ((rHigh rCS).image ∪ (rWS.slice 0 7 mw_slice_0_7_le_Pos45).image) ∪
    (rWS.slice 7 38 mw_slice_7_38_le_Pos45).image
  have hXinv : (cX234_Pos45 rWork).inverse.eval = (cX234_Pos45 rWork).eval := by
    have h23 : rWork 2 ≠ rWork 3 := fun h ↦ by
      have hv := congrArg Fin.val (rWork.wires.injective h)
      dsimp [JunctionPrefixPruned220.mWork45] at hv; omega
    have h24 : rWork 2 ≠ rWork 4 := fun h ↦ by
      have hv := congrArg Fin.val (rWork.wires.injective h)
      dsimp [JunctionPrefixPruned220.mWork45] at hv; omega
    have h34 : rWork 3 ≠ rWork 4 := fun h ↦ by
      have hv := congrArg Fin.val (rWork.wires.injective h)
      dsimp [JunctionPrefixPruned220.mWork45] at hv; omega
    rw [Circuit.eval_inverse]
    apply inv_eq_of_mul_eq_one_right
    apply Subtype.ext; apply matrix_ext_basisKet; intro ζ
    unfold cX234_Pos45
    simp only [Circuit.eval_seq, Submonoid.coe_mul, ← Matrix.mulVec_mulVec,
      evolve_X_basisKet, OneMemClass.coe_one, Matrix.one_mulVec]
    congr 1; funext u
    by_cases hu4 : u = rWork 4
    · subst hu4
      rw [Function.update_self, Function.update_of_ne h34.symm, Function.update_of_ne h24.symm,
          Function.update_self, Function.update_of_ne h34.symm, Function.update_of_ne h24.symm,
          zmod2_add_cancel_right]
    · by_cases hu3 : u = rWork 3
      · subst hu3
        rw [Function.update_of_ne h34, Function.update_self, Function.update_of_ne h23.symm,
            Function.update_of_ne h34, Function.update_self, Function.update_of_ne h23.symm,
            zmod2_add_cancel_right]
      · by_cases hu2 : u = rWork 2
        · subst hu2
          rw [Function.update_of_ne h24, Function.update_of_ne h23, Function.update_self,
              Function.update_of_ne h24, Function.update_of_ne h23, Function.update_self,
              zmod2_add_cancel_right]
        · rw [Function.update_of_ne hu4, Function.update_of_ne hu3, Function.update_of_ne hu2,
              Function.update_of_ne hu4, Function.update_of_ne hu3, Function.update_of_ne hu2]
  have hD_conj_in : DiagOn S_in
      ((cX234_Pos45 rWork).inverse.eval * u_in * (cX234_Pos45 rWork).eval).1 := by
    rw [hXinv]
    have hEqU : (cX234_Pos45 rWork).eval * u_in * (cX234_Pos45 rWork).eval =
        (Circuit.X (rWork 4)).eval * ((Circuit.X (rWork 3)).eval * ((Circuit.X (rWork 2)).eval
        * u_in * (Circuit.X (rWork 2)).eval) * (Circuit.X (rWork 3)).eval) *
        (Circuit.X (rWork 4)).eval := by
      have hc23 : (cX234_Pos45 rWork).eval =
          (Circuit.X (rWork 2)).eval * (Circuit.X (rWork 3)).eval * (Circuit.X (rWork 4)).eval := by
        apply Subtype.ext; apply matrix_ext_basisKet; intro ζ
        unfold cX234_Pos45
        simp only [Circuit.eval_seq, Submonoid.coe_mul, ← Matrix.mulVec_mulVec, evolve_X_basisKet]
        congr 1; funext u
        by_cases h2 : u = rWork 2 <;> by_cases h3 : u = rWork 3 <;> by_cases h4 : u = rWork 4 <;>
          simp [h2, h3, h4]
      conv_lhs =>
        arg 2
        rw [hc23]
      unfold cX234_Pos45
      simp only [Circuit.eval_seq, mul_assoc]
    rw [hEqU]
    have h1 := DiagOn.conj_X (rWork 2) hD_in
    have h2 := DiagOn.conj_X (rWork 3) h1
    exact DiagOn.conj_X (rWork 4) h2
  have hCov : (((rHigh rCore).image ∪ (rWork.slice 0 2 mw_slice_0_2_le_Pos45).image) ∪
      (rWork.slice 2 43 mw_slice_2_43_le_Pos45).image) ⊆ S_in := by
    intro u hu
    simp only [Finset.mem_union] at hu
    rcases hu with (hH0 | hW02) | hW243
    · rcases (QRegister.mem_image (rHigh rCore) u).mp hH0 with ⟨j, hj⟩
      let q : Fin (fullSysCoreWires mPayload) := ⟨3948 + j.val, by
        have := j.isLt
        dsimp [NuclearTwistAndXor654Concrete.fullSysCoreWires,
          FullSysCatSegmentBridge.fullSysCoreWires, systemQubits,
          numElectrons, electronBits, projectileBits]
        omega⟩
      have hqj : rCore q = u := by
        simpa [rHigh, QRegister.slice, q] using hj
      have hInWS (idx : Fin 7) (hx : (rWS.slice 0 7 mw_slice_0_7_le_Pos45) idx = u) : u ∈ S_in :=
        Finset.mem_union_left _ (Finset.mem_union_right _ ((QRegister.mem_image _ _).mpr ⟨idx, hx⟩))
      by_cases hs0 : q = wSlot0 (QRegExt.idReg _)
      · exact hInWS ⟨1, by decide⟩ (by simp [rWS, rWorkSwap_Pos45, ← hqj, hs0])
      · by_cases hs1 : q = wSlot1 (QRegExt.idReg _)
        · exact hInWS ⟨5, by decide⟩ (by simp [rWS, rWorkSwap_Pos45, ← hqj, hs1])
        · by_cases h5 : q = rNucIdx hm (QRegExt.idReg _) 5
          · exact hInWS ⟨2, by decide⟩ (by simp [rWS, rWorkSwap_Pos45, ← hqj, h5])
          · by_cases h6 : q = rNucIdx hm (QRegExt.idReg _) 6
            · exact hInWS ⟨3, by decide⟩ (by simp [rWS, rWorkSwap_Pos45, ← hqj, h6])
            · by_cases h7 : q = rNucIdx hm (QRegExt.idReg _) 7
              · exact hInWS ⟨4, by decide⟩ (by simp [rWS, rWorkSwap_Pos45, ← hqj, h7])
              · refine Finset.mem_union_left _ (Finset.mem_union_left _ ((QRegister.mem_image (rHigh
                  rCS) u).mpr ⟨j, ?_⟩))
                have hcsq : rCS q = rCore q := by simp [rCS, rCoreSwap_Pos45, hs0, hs1, h5, h6, h7]
                simpa [rHigh, QRegister.slice, q, hcsq] using hj
    · rcases (QRegister.mem_image _ u).mp hW02 with ⟨⟨k, hk⟩, rfl⟩
      interval_cases k
      · exact Finset.mem_union_left _ (Finset.mem_union_right _
          ((QRegister.mem_image _ _).mpr ⟨⟨0, by decide⟩, by
            simp [rWS, rWorkSwap_Pos45, QRegister.slice]⟩))
      · exact Finset.mem_union_left _ (Finset.mem_union_right _
          ((QRegister.mem_image _ _).mpr ⟨⟨6, by decide⟩, by
            simp [rWS, rWorkSwap_Pos45, QRegister.slice]⟩))
    · rcases (QRegister.mem_image _ u).mp hW243 with ⟨⟨k, hk⟩, rfl⟩
      by_cases hk5 : k < 5
      · have hwSl (m : ℕ) (hm43 : m < 43) (hm45 : 2 + m < JunctionPrefixPruned220.mWork45) :
            (rWork.slice 2 43 mw_slice_2_43_le_Pos45) ⟨m, hm43⟩ = rWork ⟨2 + m, hm45⟩ :=
          congrArg rWork (Fin.ext (by dsimp [QRegister.slice]))
        have hInH (q' : Fin (fullSysCoreWires mPayload)) (hq' : 3948 ≤ q'.val) : rCS q' ∈ S_in :=
          Finset.mem_union_left _ (Finset.mem_union_left _ (rCore_mem_rHigh rCS q' hq'))
        interval_cases k
        · rw [hwSl 0 hk (by decide), show rWork ⟨2, by decide⟩ = rWork 2 from rfl,
            ← rCoreSwap_rNuc5_Pos45 hm rCore rWork hCW]
          exact hInH _ (by
            rw [rNucIdx_val_eq]
            omega)
        · rw [hwSl 1 hk (by decide), show rWork ⟨3, by decide⟩ = rWork 3 from rfl,
            ← rCoreSwap_rNuc6_Pos45 hm rCore rWork hCW]
          exact hInH _ (by
            rw [rNucIdx_val_eq]
            omega)
        · rw [hwSl 2 hk (by decide), show rWork ⟨4, by decide⟩ = rWork 4 from rfl,
            ← rCoreSwap_rNuc7_Pos45 hm rCore rWork hCW]
          exact hInH _ (by
            rw [rNucIdx_val_eq]
            omega)
        · rw [hwSl 3 hk (by decide), show rWork ⟨5, by decide⟩ = rWork 5 from rfl,
            ← rCoreSwap_wSlot0_Pos45 hm rCore rWork hCW]
          exact hInH _ (by rw [wSlot0_val_eq])
        · rw [hwSl 4 hk (by decide), show rWork ⟨6, by decide⟩ = rWork 6 from rfl,
            ← rCoreSwap_wSlot1_Pos45 hm rCore rWork hCW]
          exact hInH _ (by
            rw [wSlot1_val_eq]
            omega)
      · refine Finset.mem_union_right _ ?_
        rw [hSlEq]
        refine (QRegister.mem_image _ _).mpr ⟨⟨k - 5, by omega⟩, congrArg rWork (Fin.ext ?_)⟩
        dsimp [QRegister.slice]
        omega
  refine ⟨⟨(cX234_Pos45 rWork).inverse.eval * u_in * (cX234_Pos45 rWork).eval,
    hw_conj.mono_workspace hSub38_43, DiagOn.anti hCov hD_conj_in, ?_⟩⟩
  intro ξ hz43 hCoin0
  rw [hXinv]
  have hWkIdxNe {i j : Fin JunctionPrefixPruned220.mWork45} (hij : i.val ≠ j.val) : rWork i ≠ rWork
    j :=
    fun h ↦ hij (congrArg Fin.val (rWork.wires.injective h))
  have hzAt (m : ℕ) (hm43 : m < 43) (wIdx : Fin JunctionPrefixPruned220.mWork45) (hwIdx : wIdx.val =
    2 + m) :
      ξ (rWork wIdx) = 0 := by
    have h := hz43 ⟨m, hm43⟩
    rwa [show rWork.slice 2 43 mw_slice_2_43_le_Pos45 ⟨m, hm43⟩ = rWork wIdx from
      congrArg rWork (Fin.ext (hwIdx.symm))] at h
  let ξ' := Function.update (Function.update (Function.update ξ (rWork 2) 1) (rWork 3) 1) (rWork 4)
    1
  have hXξ : (cX234_Pos45 rWork).eval.1.mulVec (basisKet ξ) = basisKet ξ' := by
    unfold cX234_Pos45
    simp only [Circuit.eval_seq, Submonoid.coe_mul, ← Matrix.mulVec_mulVec, evolve_X_basisKet]
    congr 1
    rw [hzAt 0 (by decide) 2 rfl, zero_add, Function.update_of_ne (hWkIdxNe (by decide)),
      hzAt 1 (by decide) 3 rfl, zero_add, Function.update_of_ne (hWkIdxNe (by decide)),
      Function.update_of_ne (hWkIdxNe (by decide)), hzAt 2 (by decide) 4 rfl, zero_add]
  have hw' : SwapWorkBits_Pos45 rWork ξ' := by
    refine ⟨?_, ?_, Function.update_self _ _ _, ?_, ?_⟩
    · dsimp only [ξ']
      rw [Function.update_of_ne (hWkIdxNe (by decide)), Function.update_of_ne (hWkIdxNe (by
        decide)), Function.update_self]
    · dsimp only [ξ']
      rw [Function.update_of_ne (hWkIdxNe (by decide)), Function.update_self]
    · dsimp only [ξ']
      rw [Function.update_of_ne (hWkIdxNe (by decide)), Function.update_of_ne (hWkIdxNe (by
        decide)),
        Function.update_of_ne (hWkIdxNe (by decide)), hzAt 3 (by decide) 5 rfl]
    · dsimp only [ξ']
      rw [Function.update_of_ne (hWkIdxNe (by decide)), Function.update_of_ne (hWkIdxNe (by
        decide)),
        Function.update_of_ne (hWkIdxNe (by decide)), hzAt 4 (by decide) 6 rfl]
  have hz38' : ∀ i : Fin 38, ξ' (rWS.slice 7 38 mw_slice_7_38_le_Pos45 i) = 0 := by
    rw [hSlEq]
    intro i
    have hne (c : Fin JunctionPrefixPruned220.mWork45) (hc : c.val < 7) :
        rWork.slice 7 38 mw_slice_7_38_le_Pos45 i ≠ rWork c := fun h ↦ by
      have hv := congrArg Fin.val (rWork.wires.injective h)
      dsimp [QRegister.slice] at hv
      omega
    dsimp only [ξ']
    rw [Function.update_of_ne (hne 4 (by decide)), Function.update_of_ne (hne 3 (by decide)),
      Function.update_of_ne (hne 2 (by decide))]
    have h := hz43 ⟨5 + i.val, by omega⟩
    rwa [show rWork.slice 2 43 mw_slice_2_43_le_Pos45 ⟨5 + i.val, by omega⟩ =
        rWork.slice 7 38 mw_slice_7_38_le_Pos45 i from
      congrArg rWork (Fin.ext (by
        dsimp [QRegister.slice]
        omega))] at h
  have hNeWork (q : Fin (fullSysCoreWires mPayload)) (k : Fin JunctionPrefixPruned220.mWork45) :
      rCore q ≠ rWork k := fun h ↦
    Finset.disjoint_left.mp (QRegExt.disjointWires_to_finset hCW) ((QRegister.mem_image rCore _).mpr
      ⟨q, rfl⟩)
      ((QRegister.mem_image rWork _).mpr ⟨k, h.symm⟩)
  have hCoreEq : (fun q ↦ ξ' (rCore q)) = (fun q ↦ ξ (rCore q)) := funext fun q ↦ by
    dsimp only [ξ']
    rw [Function.update_of_ne (hNeWork q 4), Function.update_of_ne (hNeWork q 3),
      Function.update_of_ne (hNeWork q 2)]
  have hH' : JunctionPrefixPruned220.HProjFlag hm rCS rWS ξ' := by
    unfold JunctionPrefixPruned220.HProjFlag
    have hw6 : rWS 6 = rWork 1 := by
      simp [rWS, rWorkSwap_Pos45]
      rfl
    have hξ1 : ξ' (rWork 1) = ξ (rWork 1) := by
      dsimp only [ξ']
      rw [Function.update_of_ne (hWkIdxNe (by decide)), Function.update_of_ne (hWkIdxNe (by
        decide)),
        Function.update_of_ne (hWkIdxNe (by decide))]
    rw [hw6, hξ1, rCoreSwap_bits_eq_setHighNucBits_Pos45 hm rCore rWork hCW hw',
      vepHighNuc_setHighNucBits, hCoreEq]
    exact hCoin0
  have hComm : (cX234_Pos45 rWork).eval * (rCore.concat rPGTwist hCP).embedUnitary (if isInv
      then (uProj3DHadCutPre16Cat hm)⁻¹ else uProj3DHadCutPre16Cat hm) =
      (rCore.concat rPGTwist hCP).embedUnitary (if isInv then (uProj3DHadCutPre16Cat hm)⁻¹
      else uProj3DHadCutPre16Cat hm) * (cX234_Pos45 rWork).eval := by
    have hDisjAct : Disjoint (cX234_Pos45 rWork).support (rCore.concat rPGTwist hCP).image := by
      have hnot : ∀ idx : Fin JunctionPrefixPruned220.mWork45, rWork idx ∉ (rCore.concat rPGTwist
        hCP).image := by
        intro idx hm_in; rw [qreg_image_concat] at hm_in
        rcases Finset.mem_union.mp hm_in with hC | hP
        · exact Finset.disjoint_left.mp (QRegExt.disjointWires_to_finset hCW) hC
            ((QRegister.mem_image rWork _).mpr ⟨idx, rfl⟩)
        · exact Finset.disjoint_left.mp (QRegExt.disjointWires_to_finset hPW) hP
            ((QRegister.mem_image rWork _).mpr ⟨idx, rfl⟩)
      unfold cX234_Pos45
      exact disj_support_seq (disj_support_X (rWork 2) (hnot 2))
        (disj_support_seq (disj_support_X (rWork 3) (hnot 3)) (disj_support_X (rWork 4) (hnot 4)))
    apply Subtype.ext
    exact CatalyzedLaurentGQSP.eval_comm_embedMatrix_of_disjoint_support
      (cX234_Pos45 rWork) (rCore.concat rPGTwist hCP) hDisjAct _
  rw [Submonoid.coe_mul, Submonoid.coe_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      hXξ, hK_in ξ' hz38' hH',
      embed_uProj3DVepHadPre16Cat_rCoreSwap_ket_Pos45 isInv hm rCore rPGTwist rWork hCP hCW hPW hw',
      ← hXξ, Matrix.mulVec_mulVec, ← Submonoid.coe_mul, hComm, Submonoid.coe_mul,
        ← Matrix.mulVec_mulVec]
  have hXsq : (cX234_Pos45 rWork).eval * (cX234_Pos45 rWork).eval = 1 := by
    calc (cX234_Pos45 rWork).eval * (cX234_Pos45 rWork).eval
        = (cX234_Pos45 rWork).inverse.eval * (cX234_Pos45 rWork).eval := by rw [hXinv]
      _ = ((cX234_Pos45 rWork).eval)⁻¹ * (cX234_Pos45 rWork).eval := by rw [Circuit.eval_inverse]
      _ = 1 := inv_mul_cancel _
  congr 1
  rw [Matrix.mulVec_mulVec, ← Submonoid.coe_mul, hXsq, OneMemClass.coe_one, Matrix.one_mulVec]
theorem dProj3DHadCut558_spec_Pos45 {mPayload : ℕ} (isInv : Bool) (hm : 22 ≤ mPayload)
    {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ} (v : Var)
    (rCore : QRegister (fullSysCoreWires mPayload) n)
    (rPGTwist : QRegister 48 n) (rWork : QRegister JunctionPrefixPruned220.mWork45 n)
    (hCP : rCore.DisjointWires rPGTwist)
    (hCW : rCore.DisjointWires rWork) (hPW : rPGTwist.DisjointWires rWork) :
    CondStageSpec (rCore.concat rPGTwist hCP)
      (rWork.slice 2 43 mw_slice_2_43_le_Pos45)
      ((rHigh rCore).image ∪ (rWork.slice 0 2 mw_slice_0_2_le_Pos45).image)
      (HPosBranchFlag_Pos45 rCore rWork)
      (if isInv then (uProj3DHadCutApexCat hm)⁻¹ else uProj3DHadCutApexCat hm)
      (dProj3DHadCut558_Pos45 isInv hm (Var := Var) v rCore rPGTwist rWork hCP hCW hPW) := by
  have hActW : (rCore.concat rPGTwist hCP).DisjointWires
      (rWork.slice 2 43 mw_slice_2_43_le_Pos45) := QRegExt.disjointWires_concat_left
      ((QRegExt.disjointWires_mono_right hCW) (QRegister.image_compose_subset rWork _))
      ((QRegExt.disjointWires_mono_right hPW) (QRegister.image_compose_subset rWork _))
  have hHC0 := HPosBranchFlag_congr_S_Pos45 rCore rWork Finset.subset_union_left
    (Finset.mem_union_right _ (reg_mem_slice_b2 rWork 0 2 mw_slice_0_2_le_Pos45 1
      (by dsimp [JunctionPrefixPruned220.mWork45]; omega) (by
        dsimp [JunctionPrefixPruned220.mWork45]; omega)))
  have hs := CondStageSpec.dBiSeq hActW hHC0 isInv
    (dProj3DHadCut558_16_spec_Pos45 isInv hm (Var := Var) v rCore rPGTwist rWork hCP hCW hPW)
    (dTail_3D_spec_Pos45 isInv (Var := Var) rCore rPGTwist rWork hCP hCW)
  exact hs.congr_unitary (by cases isInv <;> rfl)
/-- Internal `45`-wire `558-T` Hadamard-tail-cut prefix helper
`dPrefixProjHadCutAndXor558Body_Pos45`. -/
noncomputable def dPrefixProjHadCutAndXor558Body_Pos45 {mPayload : ℕ} (isInv : Bool)
    (hm : 22 ≤ mPayload) {Var : Type} {n : ℕ} (v : Var)
    (rCore : QRegister (fullSysCoreWires mPayload) n) (rPGTwist : QRegister 48 n)
    (rWork : QRegister JunctionPrefixPruned220.mWork45 n) (hCP : rCore.DisjointWires rPGTwist)
    (hCW : rCore.DisjointWires rWork) (hPW : rPGTwist.DisjointWires rWork) : DynamicCircuit
    Var n :=
  FusedVepCore288.dPureConj
    (Circuit.CNOT (wSlot2 rCore) (rWork ⟨1, mw_idx_1_lt_Pos45⟩)
      (hslot_ne_work_idx_Pos45 rCore (wSlot2_mem_rHigh rCore) rWork hCW _))
    (FusedVepCore288.dPureConj (Circuit.X (rWork ⟨1, mw_idx_1_lt_Pos45⟩))
      (dBiSeq isInv
        (dProj3DHadCut558_Pos45 isInv hm v rCore rPGTwist rWork hCP hCW hPW)
        (dXor32All654 (Var := Var) rCore)))
@[simp]
theorem count_dPrefixProjHadCutAndXor558Body_toff_Pos45 {mPayload : ℕ} (isInv : Bool) (hm : 22 ≤
    mPayload)
    {Var : Type} {n : ℕ} (v : Var)
    (rCore : QRegister (fullSysCoreWires mPayload) n)
    (rPGTwist : QRegister 48 n) (rWork : QRegister JunctionPrefixPruned220.mWork45 n)
    (hCP : rCore.DisjointWires rPGTwist)
    (hCW : rCore.DisjointWires rWork) (hPW : rPGTwist.DisjointWires rWork) :
    (dPrefixProjHadCutAndXor558Body_Pos45 isInv hm (Var := Var) v rCore rPGTwist rWork hCP hCW
      hPW).count .TOFF = 0 := by
  unfold dPrefixProjHadCutAndXor558Body_Pos45
  rw [FusedVepCore288.count_dPureConj_toff _ (by simp [Circuit.CNOT]),
      FusedVepCore288.count_dPureConj_toff _ (by simp [Circuit.X])]
  exact count_dBiSeq_toff isInv (count_dProj3DHadCut558_toff_Pos45 ..) (count_dXor32All654_toff ..)
@[simp]
theorem count_dPrefixProjHadCutAndXor558Body_t_Pos45 {mPayload : ℕ} (isInv : Bool) (hm : 22 ≤
    mPayload)
    {Var : Type} {n : ℕ} (v : Var)
    (rCore : QRegister (fullSysCoreWires mPayload) n)
    (rPGTwist : QRegister 48 n) (rWork : QRegister JunctionPrefixPruned220.mWork45 n)
    (hCP : rCore.DisjointWires rPGTwist)
    (hCW : rCore.DisjointWires rWork) (hPW : rPGTwist.DisjointWires rWork) :
    (dPrefixProjHadCutAndXor558Body_Pos45 isInv hm (Var := Var) v rCore rPGTwist rWork hCP hCW
      hPW).count .T = 558 := by
  unfold dPrefixProjHadCutAndXor558Body_Pos45
  rw [FusedVepCore288.count_dPureConj_t _ (by simp [Circuit.CNOT]),
      FusedVepCore288.count_dPureConj_t _ (by simp [Circuit.X])]
  simp only [count_dBiSeq_t, count_dProj3DHadCut558_t_Pos45, count_dXor32All654_t]
theorem dPrefixProjHadCutAndXor558Body_spec_Pos45 {mPayload : ℕ} (isInv : Bool) (hm : 22 ≤ mPayload)
    {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ} (v : Var)
    (rCore : QRegister (fullSysCoreWires mPayload) n)
    (rPGTwist : QRegister 48 n) (rWork : QRegister JunctionPrefixPruned220.mWork45 n)
    (hCP : rCore.DisjointWires rPGTwist)
    (hCW : rCore.DisjointWires rWork) (hPW : rPGTwist.DisjointWires rWork) :
    CondStageSpec (rCore.concat rPGTwist hCP)
      (rWork.slice 0 45 mw_slice_0_45_le_Pos45)
      ((rHigh rCore).image ∪ (rWork.slice 0 0 mw_slice_0_0_le_Pos45).image)
      (fun _ ↦ True)
      (if isInv then (uPrefixProjHadCutAndXorCat hm)⁻¹ else uPrefixProjHadCutAndXorCat hm)
      (dPrefixProjHadCutAndXor558Body_Pos45 isInv hm (Var := Var) v rCore rPGTwist rWork hCP hCW
        hPW) := by
  have hActW43 : (rCore.concat rPGTwist hCP).DisjointWires
      (rWork.slice 2 43 mw_slice_2_43_le_Pos45) := QRegExt.disjointWires_concat_left
      ((QRegExt.disjointWires_mono_right hCW) (QRegister.image_compose_subset rWork _))
      ((QRegExt.disjointWires_mono_right hPW) (QRegister.image_compose_subset rWork _))
  have hH_pos := HPosBranchFlag_congr_S_Pos45 rCore rWork Finset.subset_union_left
    (Finset.mem_union_right _
      (reg_mem_slice_b2 rWork 0 2 mw_slice_0_2_le_Pos45 1
        (by dsimp [JunctionPrefixPruned220.mWork45]; omega) (by
          dsimp [JunctionPrefixPruned220.mWork45]; omega)))
  have hsProjXor := CondStageSpec.dBiSeq hActW43 hH_pos isInv
    (dProj3DHadCut558_spec_Pos45 isInv hm (Var := Var) v rCore rPGTwist rWork hCP hCW hPW)
    (JunctionPrefixPruned220.dXor32_spec isInv (Var := Var) rCore rPGTwist rWork hCP hCW (H :=
      HPosBranchFlag_Pos45 rCore rWork))
  have hU558 : (if isInv then ((rCoreBlock48 mPayload).embedUnitary (uXor32Core mPayload) *
      uProj3DHadCutApexCat hm)⁻¹ else (rCoreBlock48 mPayload).embedUnitary (uXor32Core
      mPayload) * uProj3DHadCutApexCat hm) = (if isInv then (uPrefixProjHadCutAndXorCat hm)⁻¹
      else uPrefixProjHadCutAndXorCat hm) := rfl
  let w1 := rWork ⟨1, mw_idx_1_lt_Pos45⟩
  have hCoreNotW43 : wSlot2 rCore ∉ (rWork.slice 2 43 mw_slice_2_43_le_Pos45).image :=
    fun hm_in ↦ Finset.disjoint_left.mp (QRegExt.disjointWires_to_finset hCW) (rHigh_sub_rCore rCore
      (wSlot2_mem_rHigh rCore))
      (QRegister.image_compose_subset rWork _ hm_in)
  have hw1NotW43 : w1 ∉ (rWork.slice 2 43 mw_slice_2_43_le_Pos45).image :=
    reg_not_mem_slice_b2 rWork 2 43 mw_slice_2_43_le_Pos45 1 (Or.inl (by
      dsimp [JunctionPrefixPruned220.mWork45]; omega))
  have hw1NotAct : w1 ∉ (rCore.concat rPGTwist hCP).image := by
    intro hm_in; rw [qreg_image_concat] at hm_in
    rcases Finset.mem_union.mp hm_in with hC | hP
    · exact Finset.disjoint_left.mp (QRegExt.disjointWires_to_finset hCW) hC ((QRegister.mem_image
        rWork _).mpr ⟨_, rfl⟩)
    · exact Finset.disjoint_left.mp (QRegExt.disjointWires_to_finset hPW) hP ((QRegister.mem_image
        rWork _).mpr ⟨_, rfl⟩)
  have hs2InS : wSlot2 rCore ∈ (rHigh rCore).image ∪ (rWork.slice 0 2 mw_slice_0_2_le_Pos45).image
    :=
    Finset.mem_union_left _ (wSlot2_mem_rHigh rCore)
  have hw1InS : w1 ∈ (rHigh rCore).image ∪ (rWork.slice 0 2 mw_slice_0_2_le_Pos45).image :=
    Finset.mem_union_right _
      (reg_mem_slice_b2 rWork 0 2 mw_slice_0_2_le_Pos45 1
        (by dsimp [JunctionPrefixPruned220.mWork45]; omega) (by
          dsimp [JunctionPrefixPruned220.mWork45]; omega))
  have hsX := CondStageSpec_dPureConjX w1 hw1NotW43 hw1NotAct hw1InS
    (H_outer := fun ξ ↦ ξ w1 = ξ (wSlot2 rCore))
    (fun ξ hm1 ↦ by
      unfold HPosBranchFlag_Pos45 posBranchActive
      dsimp only
      have hw1_eq : rWork 1 = w1 := congrArg rWork (Fin.ext (by
        dsimp [JunctionPrefixPruned220.mWork45]))
      have hs2_eq : rCore (wSlot2 (QRegExt.idReg _)) = wSlot2 rCore := by
        unfold wSlot2; simp [QRegExt.idReg]
      have hne_s2 : wSlot2 rCore ≠ w1 :=
        hslot_ne_work_idx_Pos45 rCore (wSlot2_mem_rHigh rCore) rWork hCW _
      simp only [hw1_eq, hs2_eq, Function.update_self, Function.update_of_ne hne_s2, hm1]
      rcases JunctionApexCSA288.zmod2_eq_zero_or_one (ξ (wSlot2 rCore)) with h0 | h1
      · rw [h0]; decide
      · rw [h1]; decide)
    (hsProjXor.congr_unitary hU558)
  have hsConj := CondStageSpec.dPureConjCNOT (wSlot2 rCore) w1
    (hslot_ne_work_idx_Pos45 rCore (wSlot2_mem_rHigh rCore) rWork hCW _)
    hCoreNotW43 hw1NotW43 hw1NotAct hs2InS hw1InS
    (H_outer := fun ξ ↦ ξ w1 = 0)
    (fun ξ hz1 ↦ by
      have hne_s2 : wSlot2 rCore ≠ w1 :=
        hslot_ne_work_idx_Pos45 rCore (wSlot2_mem_rHigh rCore) rWork hCW _
      rw [Function.update_self, Function.update_of_ne hne_s2, hz1, zero_add])
    hsX
  have hSub : (rWork.slice 2 43 mw_slice_2_43_le_Pos45).image ⊆
      (rWork.slice 0 45 mw_slice_0_45_le_Pos45).image := by
    intro w hw
    rcases (QRegister.mem_image _ w).mp hw with ⟨j, rfl⟩
    exact (QRegister.mem_image _ _).mpr ⟨⟨2 + j.val, by omega⟩,
      congrArg rWork (Fin.ext (by dsimp [QRegister.slice]; omega))⟩
  have hCov45 : ((rHigh rCore).image ∪ (rWork.slice 0 0 mw_slice_0_0_le_Pos45).image) ∪
      (rWork.slice 0 45 mw_slice_0_45_le_Pos45).image ⊆ ((rHigh rCore).image ∪ (rWork.slice 0
      2 mw_slice_0_2_le_Pos45).image) ∪ (rWork.slice 2 43 mw_slice_2_43_le_Pos45).image := by
    intro w hw
    simp only [Finset.mem_union] at hw ⊢
    rcases hw with (hH | hW0) | hW45
    · exact Or.inl (Or.inl hH)
    · rcases (QRegister.mem_image _ w).mp hW0 with ⟨j, _⟩
      exact Fin.elim0 j
    · rcases (QRegister.mem_image _ w).mp hW45 with ⟨j, rfl⟩
      by_cases hj2 : j.val < 2
      · refine Or.inl (Or.inr ((QRegister.mem_image _ _).mpr ⟨⟨j.val, hj2⟩, ?_⟩))
        exact congrArg rWork (Fin.ext (by dsimp [QRegister.slice]))
      · refine Or.inr ((QRegister.mem_image _ _).mpr ⟨⟨j.val - 2, by omega⟩, ?_⟩)
        exact congrArg rWork (Fin.ext (by dsimp [QRegister.slice]; omega))
  rcases hsConj.exists_u with ⟨u, hw, hD, hK⟩
  refine ⟨⟨u, hw.mono_workspace hSub, DiagOn.anti hCov45 hD, fun ξ hz45 _ ↦ ?_⟩⟩
  apply hK ξ
  · intro j
    have h := hz45 ⟨2 + j.val, by omega⟩
    rwa [show rWork.slice 0 45 mw_slice_0_45_le_Pos45 ⟨2 + j.val, by omega⟩ =
        rWork.slice 2 43 mw_slice_2_43_le_Pos45 j from
      congrArg rWork (Fin.ext (by dsimp [QRegister.slice]; omega))] at h
  · have h := hz45 ⟨1, by decide⟩
    rwa [show rWork.slice 0 45 mw_slice_0_45_le_Pos45 ⟨1, by decide⟩ = w1 from
      congrArg rWork (Fin.ext (by dsimp [QRegister.slice, JunctionPrefixPruned220.mWork45]))] at h
/-  Forward `558 T`, `0 .TOFF`, `45`-wire `Proj3DCut + Xor32` circuit. -/
/-  Inverse `558 T`, `0 .TOFF`, `45`-wire `(Proj3DCut + Xor32)⁻¹` circuit. -/
/-  Forward `558 T`, `0 .TOFF` prefix circuit polymorphic over any `45 ≤ mWork`. -/
/-  Inverse `558 T`, `0 .TOFF` prefix circuit polymorphic over any `45 ≤ mWork`. -/
/-- Width-polymorphic `558 T`, `0 .TOFF` prefix (`45 ≤ mWork`, `0` `rSum42` gates)
matching `Barrel3PassCommuteHelpers.ProjPrefixSpec`. -/
noncomputable def dPrefixProjHadCutAndXor558Pruned {mWork : ℕ} (hmWork : 45 ≤ mWork)
    (isInv : Bool) {Var : Type} {n : ℕ} (v : Var) (rCore : QRegister (fullSysCoreWires 80) n)
    (rSum42 : QRegister 42 n) (rPGTwist : QRegister 48 n) (rWork : QRegister mWork n)
    (_hCS42 : rCore.DisjointWires rSum42) (hCP : rCore.DisjointWires rPGTwist)
    (_hSP : rSum42.DisjointWires rPGTwist) (hCW : rCore.DisjointWires rWork)
    (_hSW42 : rSum42.DisjointWires rWork) (hPW : rPGTwist.DisjointWires rWork) :
    DynamicCircuit Var n :=
  vepLockVal <|
    dPrefixProjHadCutAndXor558Body_Pos45 isInv (by decide : 22 ≤ 80) (Var := Var) v rCore
      rPGTwist (rWork.slice 0 45 hmWork) hCP
      ((QRegExt.disjointWires_mono_right hCW) (QRegister.image_compose_subset rWork _))
      ((QRegExt.disjointWires_mono_right hPW) (QRegister.image_compose_subset rWork _))
@[simp] theorem count_dPrefixProjHadCutAndXor558Pruned_toff {mWork : ℕ} (hmWork : 45 ≤ mWork)
    (isInv : Bool) {Var : Type} {n : ℕ} (v : Var) (rCore : QRegister (fullSysCoreWires 80) n)
    (rSum42 : QRegister 42 n) (rPGTwist : QRegister 48 n) (rWork : QRegister mWork n)
    (hCS42 : rCore.DisjointWires rSum42) (hCP : rCore.DisjointWires rPGTwist)
    (hSP : rSum42.DisjointWires rPGTwist) (hCW : rCore.DisjointWires rWork)
    (hSW42 : rSum42.DisjointWires rWork) (hPW : rPGTwist.DisjointWires rWork) :
    (dPrefixProjHadCutAndXor558Pruned hmWork isInv v rCore rSum42 rPGTwist rWork hCS42 hCP hSP
    hCW hSW42 hPW).count .TOFF = 0 := by
  rw [dPrefixProjHadCutAndXor558Pruned, vepLockVal_eq]
  exact count_dPrefixProjHadCutAndXor558Body_toff_Pos45 isInv (by decide : 22 ≤ 80) v rCore
    rPGTwist _ hCP _ _
@[simp] theorem count_dPrefixProjHadCutAndXor558Pruned_t {mWork : ℕ} (hmWork : 45 ≤ mWork)
    (isInv : Bool) {Var : Type} {n : ℕ} (v : Var) (rCore : QRegister (fullSysCoreWires 80) n)
    (rSum42 : QRegister 42 n) (rPGTwist : QRegister 48 n) (rWork : QRegister mWork n)
    (hCS42 : rCore.DisjointWires rSum42) (hCP : rCore.DisjointWires rPGTwist)
    (hSP : rSum42.DisjointWires rPGTwist) (hCW : rCore.DisjointWires rWork)
    (hSW42 : rSum42.DisjointWires rWork) (hPW : rPGTwist.DisjointWires rWork) :
    (dPrefixProjHadCutAndXor558Pruned hmWork isInv v rCore rSum42 rPGTwist rWork hCS42 hCP hSP
    hCW hSW42 hPW).count .T = 558 := by
  rw [dPrefixProjHadCutAndXor558Pruned, vepLockVal_eq]
  exact count_dPrefixProjHadCutAndXor558Body_t_Pos45 isInv (by decide : 22 ≤ 80) v rCore
    rPGTwist _ hCP _ _
theorem dPrefixProjHadCutAndXor558Pruned_realizesPair {mWork n : ℕ}
    {Var : Type} [Fintype Var] [DecidableEq Var] (hmWork : 45 ≤ mWork) (v : Var)
    (rCore : QRegister (fullSysCoreWires 80) n)
    (rSum42 : QRegister 42 n) (rPGTwist : QRegister 48 n) (rWork : QRegister mWork n)
    (hCS42 : rCore.DisjointWires rSum42) (hCP : rCore.DisjointWires rPGTwist)
    (hSP : rSum42.DisjointWires rPGTwist) (hCW : rCore.DisjointWires rWork)
    (hSW42 : rSum42.DisjointWires rWork) (hPW : rPGTwist.DisjointWires rWork) :
    RealizesCleanPair (rCore.concat rPGTwist hCP) rWork
      (JunctionUncondHadTailCut.uPrefixProjHadCutAndXorCat (by decide : 22 ≤ 80))
      (dPrefixProjHadCutAndXor558Pruned hmWork false v rCore rSum42 rPGTwist rWork hCS42 hCP hSP hCW
        hSW42 hPW)
      (dPrefixProjHadCutAndXor558Pruned hmWork true v rCore rSum42 rPGTwist rWork hCS42 hCP hSP hCW
        hSW42 hPW) := by
  let rW45 := rWork.slice 0 45 hmWork
  have hCW45 : rCore.DisjointWires rW45 := (QRegExt.disjointWires_mono_right hCW)
    (QRegister.image_compose_subset rWork _)
  have hPW45 : rPGTwist.DisjointWires rW45 := (QRegExt.disjointWires_mono_right hPW)
    (QRegister.image_compose_subset rWork _)
  have hPairSl : RealizesCleanPair (rCore.concat rPGTwist hCP)
      (rW45.slice 0 45 mw_slice_0_45_le_Pos45)
      (JunctionUncondHadTailCut.uPrefixProjHadCutAndXorCat (by decide : 22 ≤ 80))
      (dPrefixProjHadCutAndXor558Pruned hmWork false v rCore rSum42 rPGTwist rWork hCS42 hCP hSP hCW
        hSW42 hPW)
      (dPrefixProjHadCutAndXor558Pruned hmWork true v rCore rSum42 rPGTwist rWork hCS42 hCP hSP hCW
        hSW42 hPW) :=
    { fwd := by
        rw [dPrefixProjHadCutAndXor558Pruned, vepLockVal_eq]
        exact (dPrefixProjHadCutAndXor558Body_spec_Pos45 false (by decide : 22 ≤ 80) v rCore
          rPGTwist rW45 hCP hCW45 hPW45).to_realizesClean
      inv := by
        rw [dPrefixProjHadCutAndXor558Pruned, vepLockVal_eq]
        exact (dPrefixProjHadCutAndXor558Body_spec_Pos45 true (by decide : 22 ≤ 80) v rCore rPGTwist
          rW45 hCP hCW45 hPW45).to_realizesClean }
  exact hPairSl.widenWorkspace.widenWorkspace
end
end Twist558AndShared108
end
end Twist558AndShared108

noncomputable section MultiBankWStateRouter

set_option exponentiation.threshold 8192
section
noncomputable section
namespace MultiBankWStateRouter
open Operator QProg Matrix Circuit Qubit HermitianMat PrimitiveGate _root_.DynamicCircuit
  DynCircuitExt
open MeasureBranchHadamardSem
open PosSlots24PartnerMuxZeroT123
open PosSlots24SpectatorPrunedPhase
open scoped Matrix ComplexOrder MatrixOrder Circuit.Notation BigOperators
local instance (priority := 100000) {k : ℕ} : NeZero (2 ^ k) := ⟨pow_ne_zero k two_ne_zero⟩
/-! ## Section 0: Self-Contained StoppingPower Base Preamble & SubspaceStep Bridges -/
/-- Subspace transformer predicate matching `p2t_RealizesConstCleanUnitary` on arbitrary operators
`R_in, R_out`. -/
def SubspaceStep {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)]
    (R_in R_out : Operator (2 ^ n)) (p : DynamicCircuit Var n) : Prop := ∀ M : Observable
    (Fin (2 ^ n)), ∃ N : Observable (Fin (2 ^ n)), wp p.compile (fun _ ↦ M) = (fun _ ↦ N) ∧ R_outᴴ *
      M.1.1
    * R_out = R_inᴴ * N.1.1 * R_in
theorem SubspaceStep.seq {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)]
    {R₀ R₁ R₂ : Operator (2 ^ n)} {p₁ p₂ : DynamicCircuit Var n}
    (h₁ : SubspaceStep R₀ R₁ p₁) (h₂ : SubspaceStep R₁ R₂ p₂) :
    SubspaceStep R₀ R₂ (.seq p₁ p₂) := fun M ↦
  let ⟨N₂, hw₂, hm₂⟩ := h₂ M
  let ⟨N₁, hw₁, hm₁⟩ := h₁ N₂
  ⟨N₁, by change wp p₁.compile (wp p₂.compile (fun _ ↦ M)) = _; rw [hw₂, hw₁], hm₂.trans hm₁⟩
@[simp] theorem qAssign_obs_map_val {d : ℕ} (U : Unitary d) (A : Observable (Fin d)) :
    (qAssignObsMap U A).1 = A.1.conj U.1ᴴ := by
  simp [qAssignObsMap, Observable.conj_coe, Unitary.coe_star, Matrix.star_eq_conjTranspose]
theorem wp_circuit_compile_loc {Var : Type} [DecidableEq Var] {n : ℕ}
    (c : Circuit n) (M : Observable (Fin (2 ^ n))) :
    wp (DynamicCircuit.circuit c : DynamicCircuit Var n).compile (fun _ ↦ M) =
      fun _ ↦ qAssignObsMap c.eval M := by
  funext σ
  simp [DynamicCircuit.compile_circuit]
theorem subspaceStep_of_circuit {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ} [NeZero (2 ^
    n)]
    (R : Operator (2 ^ n)) (c : Circuit n) :
    SubspaceStep (Var := Var) R (c.eval.1 * R) (.circuit c) := fun M ↦
  ⟨qAssignObsMap c.eval M, wp_circuit_compile_loc c M, by
    have h1 : (qAssignObsMap c.eval M).1.1 = c.eval.1ᴴ * M.1.1 * c.eval.1 := by
      simp [qAssignObsMap, Observable.conj_coe, HermitianMat.conj_apply_mat,
        Unitary.coe_star, Matrix.star_eq_conjTranspose, Matrix.mul_assoc]
    change (c.eval.1 * R)ᴴ * M.1.1 * (c.eval.1 * R) = Rᴴ * (qAssignObsMap c.eval M).1.1 * R
    rw [h1]
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]⟩
theorem subspaceStep_congr_out {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)]
    {R_in R₁ R₂ : Operator (2 ^ n)} {p : DynamicCircuit Var n}
    (hp : SubspaceStep (Var := Var) R_in R₁ p) (heq : R₁ = R₂) :
    SubspaceStep (Var := Var) R_in R₂ p := heq ▸ hp
theorem subspaceStep_congr_in {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)]
    {R₁ R₂ R_out : Operator (2 ^ n)} {p : DynamicCircuit Var n}
    (heq : R₁ = R₂) (hp : SubspaceStep (Var := Var) R₂ R_out p) :
    SubspaceStep (Var := Var) R₁ R_out p := heq ▸ hp
/-- Convert `SubspaceStep P (U.1 * P) d` directly into `p2t_RealizesConstCleanUnitary P d U`. -/
theorem SubspaceStep.toConstCleanUnitary {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    [NeZero (2 ^ n)] {P : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ} {d : DynamicCircuit Var n}
    {U : Unitary (2 ^ n)} (hP : Pᴴ = P) (hs : SubspaceStep P (U.1 * P) d) :
    p2t_RealizesConstCleanUnitary P d U := by
  refine ⟨fun M ↦ let ⟨N, hN, _⟩ := hs M; ⟨N, hN⟩, fun M σ ↦ ?_⟩
  obtain ⟨N, hN, hm⟩ := hs M
  have hσ : wp d.compile (fun _ ↦ M) σ = N := congrFun hN σ
  rw [hσ]
  calc P * N.1.1 * P
      = Pᴴ * N.1.1 * P := by rw [hP]
    _ = (U.1 * P)ᴴ * M.1.1 * (U.1 * P) := hm.symm
    _ = P * (U.1ᴴ * M.1.1 * U.1) * P := by
        simp only [Matrix.conjTranspose_mul, hP, Matrix.mul_assoc]
/-- Lift `p2t_RealizesConstCleanUnitary P d U` onto any operator `R` satisfying `P * R = R`. -/
theorem SubspaceStep.ofConstCleanUnitary {Var : Type} [Fintype Var] [DecidableEq Var]
    {n : ℕ} [NeZero (2 ^ n)]
    {P R : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ}
    {d : DynamicCircuit Var n} {U : Unitary (2 ^ n)}
    (hP : Pᴴ = P)
    (hr : p2t_RealizesConstCleanUnitary P d U)
    (hPR : P * R = R) :
    SubspaceStep R (U.1 * R) d := fun M ↦ by
  obtain ⟨N, hN⟩ := hr.1 M
  refine ⟨N, hN, ?_⟩
  have hRP : Rᴴ * P = Rᴴ := by
    simpa only [Matrix.conjTranspose_mul, hP] using congrArg Matrix.conjTranspose hPR
  have h0 : P * N.1.1 * P = P * (U.1ᴴ * M.1.1 * U.1) * P := by
    have hσ := hr.2 M (fun _ ↦ 0)
    have hN0 : wp d.compile (fun _ ↦ M) (fun _ ↦ 0) = N := congrFun hN (fun _ ↦ 0)
    rwa [hN0] at hσ
  calc (U.1 * R)ᴴ * M.1.1 * (U.1 * R)
      = Rᴴ * (P * (U.1ᴴ * M.1.1 * U.1) * P) * R := by
          rw [Matrix.conjTranspose_mul]
          simp only [Matrix.mul_assoc]
          rw [hPR, ← Matrix.mul_assoc Rᴴ P, hRP]
    _ = Rᴴ * (P * N.1.1 * P) * R := by rw [h0]
    _ = Rᴴ * N.1.1 * R := by
          simp only [Matrix.mul_assoc]
          rw [hPR, ← Matrix.mul_assoc Rᴴ P, hRP]
/-- Structural wire-support predicate on `Circuit n`. -/
def CircWires {n : ℕ} (P : Wire n → Prop) : Circuit n → Prop
  | .identity => True
  | .gate _ r => ∀ i, P (r i)
  | .seq c₁ c₂ => CircWires P c₁ ∧ CircWires P c₂
theorem cw_1 {n : ℕ} {S : Wire n → Prop} {g : PrimitiveGate 1} {q : Wire n} (hq : S q) :
    CircWires S (Circuit.single g q) := fun _ ↦ hq
theorem cw_cnot {n : ℕ} {S : Wire n → Prop} {c t : Wire n} {h : c ≠ t}
    (hc : S c) (ht : S t) : CircWires S (Circuit.CNOT c t h) := by
  intro i; fin_cases i <;> assumption
noncomputable abbrev projBit_dqmu {n : ℕ} (w : Wire n) (b : Fin (2 ^ 1)) : Operator (2 ^ n) :=
  (QRegister.singleton w).basisOutcomeProjector b
def remeasureIf_dqmu {Var : Type} {n : ℕ} (v : Var) (w : Wire n) (c : Circuit n) :
    DynamicCircuit Var n :=
  .seq (.measure v (QRegister.singleton w)) (dynQIfVar v (.circuit c) .identity)
def zResetFixupDyn {Var : Type} {n : ℕ} (v : Var) (q : Wire n) (cFix : Circuit n) :
    DynamicCircuit Var n :=
  .seq (.measure v (QRegister.singleton q))
    (dynQIfVar v (.circuit (Circuit.X q ;;ᶜ cFix)) .identity)
@[simp] theorem count_zResetFixupDyn_t {Var : Type} {n : ℕ} (v : Var) (q : Wire n) (cFix : Circuit
    n) :
    (zResetFixupDyn v q cFix).count .T = cFix.count .T := by
  simp [zResetFixupDyn, DynamicCircuit.count, Circuit.X]
@[simp] theorem count_zResetFixupDyn_toff {Var : Type} {n : ℕ} (v : Var) (q : Wire n) (cFix :
    Circuit n) :
    (zResetFixupDyn v q cFix).count .TOFF = cFix.count .TOFF := by
  simp [zResetFixupDyn, DynamicCircuit.count, Circuit.X]
def SupportedOn {n : ℕ} (Pred : BitAssignment n → Prop) (R : Operator (2 ^ n)) : Prop := ∀
    (A B : Operator (2 ^ n)), (∀ β : BitAssignment n, Pred β → A.mulVec (ket β) = B.mulVec
    (ket β)) → A * R = B * R
@[simp] theorem basisBits_basisBitsEquiv_symm {q : ℕ} (β : BitAssignment q) : basisBits q
    ((basisBitsEquiv q).symm β) = β := (basisBitsEquiv q).apply_symm_apply β
theorem bitSign_add (a b : ZMod 2) : bitSign (a + b) = bitSign a * bitSign b := by
  rcases bit_cases a with rfl | rfl <;> rcases bit_cases b with rfl | rfl <;>
    simp [bitSign, show (1 : ZMod 2) + 1 = 0 from rfl]
def xorWirePerm {n : ℕ} (q : Wire n) (f : BitAssignment n → ZMod 2)
    (hf : ∀ β a, f (Function.update β q a) = f β) : Equiv.Perm (BitAssignment n) where
  toFun β := Function.update β q (β q + f β)
  invFun β := Function.update β q (β q + f β)
  left_inv β := by
    dsimp
    rw [Function.update_idem, Function.update_self, hf, add_assoc, CharTwo.add_self_eq_zero,
      add_zero, Function.update_eq_self]
  right_inv β := by
    dsimp
    rw [Function.update_idem, Function.update_self, hf, add_assoc, CharTwo.add_self_eq_zero,
      add_zero, Function.update_eq_self]
noncomputable def permUnitary {n : ℕ} (e : Equiv.Perm (BitAssignment n)) : Unitary (2 ^ n) :=
  let idxPerm : Equiv.Perm (Fin (2 ^ n)) :=
    ((basisBitsEquiv n).trans (e.trans (basisBitsEquiv n).symm)).symm
  ⟨Equiv.Perm.permMatrix ℂ idxPerm, by
    rw [Matrix.mem_unitaryGroup_iff']
    ext i j
    rw [Matrix.mul_apply, Matrix.one_apply, Finset.sum_eq_single (idxPerm.symm i)]
    · by_cases hij : i = j
      · subst hij; simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]
      · simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, hij]
    · intro k _ hk
      have hki : idxPerm k ≠ i := fun h ↦ hk (by rw [← h, Equiv.symm_apply_apply])
      simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, hki]
    · simp⟩
theorem permUnitary_mulVec_ket {n : ℕ} (e : Equiv.Perm (BitAssignment n)) (β : BitAssignment n) :
    (permUnitary e).1.mulVec (ket β) = ket (e β) := by
  let idxPerm : Equiv.Perm (Fin (2 ^ n)) :=
    ((basisBitsEquiv n).trans (e.trans (basisBitsEquiv n).symm)).symm
  change (Equiv.Perm.permMatrix ℂ idxPerm).mulVec (ket β) = ket (e β)
  have h1 : (Equiv.Perm.permMatrix ℂ idxPerm).mulVec (ket β) =
      basisState (idxPerm.symm ((basisBitsEquiv n).symm β)) := by
    rw [ket, basisState]
    funext i
    simp only [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Matrix.mulVec, dotProduct,
      Pi.single_apply]
    rw [Finset.sum_eq_single ((basisBitsEquiv n).symm β)]
    · by_cases hi : idxPerm i = (basisBitsEquiv n).symm β
      · have hi' : i = idxPerm.symm ((basisBitsEquiv n).symm β) := (idxPerm.eq_symm_apply).mpr hi
        simp [hi']
      · have hi' : i ≠ idxPerm.symm ((basisBitsEquiv n).symm β) :=
          fun h ↦ hi ((idxPerm.eq_symm_apply).mp h)
        simp [hi, hi']
    · intro k _ hk; simp [hk]
    · simp
  rw [h1]
  simp [idxPerm, ket]
noncomputable def xorWireUnitary {n : ℕ} (q : Wire n) (f : BitAssignment n → ZMod 2)
    (hf : ∀ β a, f (Function.update β q a) = f β) : Unitary (2 ^ n) :=
  permUnitary (xorWirePerm q f hf)
@[simp] theorem xorWireUnitary_mulVec_ket {n : ℕ} (q : Wire n) (f : BitAssignment n → ZMod 2)
    (hf : ∀ β a, f (Function.update β q a) = f β) (β : BitAssignment n) :
    (xorWireUnitary q f hf).1.mulVec (ket β) = ket (Function.update β q (β q + f β)) :=
    permUnitary_mulVec_ket (xorWirePerm q f hf) β
/-- A pair of distinct wires `(w₁, w₂)` in an `n`-qubit circuit. -/
abbrev WirePair (n : ℕ) := Σ w₁ : Wire n, { w₂ : Wire n // w₁ ≠ w₂ }
/-- `0-T` circuit applying `CZ(w₁, w₂) = H w₂ ;; CNOT w₁ w₂ ;; H w₂` across `pairs`. -/
def czPairsCircuit {n : ℕ} : List (WirePair n) → Circuit n
  | [] => .identity
  | p :: ps =>
      (Circuit.H p.2.1 ;;ᶜ Circuit.CNOT p.1 p.2.1 p.2.2 ;;ᶜ Circuit.H p.2.1) ;;ᶜ
        czPairsCircuit ps
/-- `GF(2)` parity `∑_{(w₁, w₂) ∈ pairs} β w₁ * β w₂` kicked back in phase by `czPairsCircuit`. -/
def czPairsParity {n : ℕ} : List (WirePair n) → BitAssignment n → ZMod 2
  | [], _ => 0
  | p :: ps, β => β p.1 * β p.2.1 + czPairsParity ps β
theorem count_czPairsCircuit {n : ℕ} :
    ∀ pairs : List (WirePair n),
      (czPairsCircuit pairs).count .T = 0 ∧ (czPairsCircuit pairs).count .TOFF = 0
  | [] => ⟨rfl, rfl⟩
  | _ :: ps => by
      obtain ⟨ht, hf⟩ := count_czPairsCircuit ps
      dsimp only [czPairsCircuit]
      exact ⟨by simpa [Circuit.count_seq, Circuit.H, Circuit.CNOT] using ht,
             by simpa [Circuit.count_seq, Circuit.H, Circuit.CNOT] using hf⟩
private theorem ket_CZ_circuit_loc {n : ℕ} (w₁ w₂ : Wire n) (hne : w₁ ≠ w₂) (β : BitAssignment n) :
    (Circuit.H w₂ ;;ᶜ Circuit.CNOT w₁ w₂ hne ;;ᶜ Circuit.H w₂).eval.1.mulVec (ket β) =
      bitSign (β w₁ * β w₂) • ket β := by
  rw [show (Circuit.H w₂ ;;ᶜ Circuit.CNOT w₁ w₂ hne ;;ᶜ Circuit.H w₂) =
        PosSlots24PartnerMuxZeroT123.czCircuit w₁ w₂ hne from rfl,
      PosSlots24PartnerMuxZeroT123.ket_czCircuit]
  rcases bit_cases (β w₁ * β w₂) with h | h <;> simp [h, bitSign, ZMod.val_zero]
theorem czPairsCircuit_mulVec_ket {n : ℕ} :
    ∀ (pairs : List (WirePair n)) (β : BitAssignment n),
      (czPairsCircuit pairs).eval.1.mulVec (ket β) =
        bitSign (czPairsParity pairs β) • ket β
  | [], β => by
      simp [czPairsCircuit, czPairsParity, bitSign, Circuit.eval_identity]
  | p :: ps, β => by
      rw [czPairsCircuit, eval_seq_mulVec, ket_CZ_circuit_loc p.1 p.2.1 p.2.2 β, Matrix.mulVec_smul,
        czPairsCircuit_mulVec_ket ps β, smul_smul, ← bitSign_add]
      rfl
/-- Sequential `0-T` single-`Var` X-measurement unloader on wire `q`, continuing with `rest`. -/
def xUnloadCzPairsSeqDyn {Var : Type} {n : ℕ} (v : Var) (q : Wire n)
    (pairs : List (WirePair n)) (rest : DynamicCircuit Var n) : DynamicCircuit Var n :=
  .seq (.circuit (.H q))
    (.seq (remeasureIf_dqmu v q (.X q ;;ᶜ czPairsCircuit pairs)) rest)
theorem count_xUnloadCzPairsSeqDyn {Var : Type} {n : ℕ} (v : Var) (q : Wire n)
    (pairs : List (WirePair n)) (rest : DynamicCircuit Var n) :
    (xUnloadCzPairsSeqDyn v q pairs rest).count .T = rest.count .T ∧
    (xUnloadCzPairsSeqDyn v q pairs rest).count .TOFF = rest.count .TOFF := by
  obtain ⟨htc, hfc⟩ := count_czPairsCircuit pairs
  simp [xUnloadCzPairsSeqDyn, remeasureIf_dqmu, DynamicCircuit.count, Circuit.count_seq,
    Circuit.H, Circuit.X, htc, hfc]
/-- Prefix integer value `∑_{d < k} 2^d * [β (wBit d) = 1]`. -/
def idxValPrefix {D n : ℕ} (wBit : Fin D → Wire n) (β : BitAssignment n) : ∀ k : ℕ, k ≤ D → ℕ
  | 0, _ => 0
  | k + 1, hk =>
      idxValPrefix wBit β k (Nat.le_of_succ_le hk) + if β (wBit ⟨k, hk⟩) = 1 then 2 ^ k else 0
/-- Unsigned `D`-bit integer encoded on `wBit : Fin D → Wire n`. -/
def idxValD {D n : ℕ} (wBit : Fin D → Wire n) (β : BitAssignment n) : ℕ :=
  idxValPrefix wBit β D le_rfl
theorem idxValPrefix_lt_two_pow {D n : ℕ} (wBit : Fin D → Wire n) (β : BitAssignment n) :
    ∀ (k : ℕ) (hk : k ≤ D), idxValPrefix wBit β k hk < 2 ^ k
  | 0, _ => by simp [idxValPrefix]
  | k + 1, hk => by
      have ih := idxValPrefix_lt_two_pow wBit β k (Nat.le_of_succ_le hk)
      have hpow : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by ring
      dsimp only [idxValPrefix]
      split_ifs <;> omega
theorem idxValD_lt_two_pow {D n : ℕ} (wBit : Fin D → Wire n) (β : BitAssignment n) : idxValD
    wBit β < 2 ^ D := idxValPrefix_lt_two_pow wBit β D le_rfl
/-- `2-T` controlled-Hadamard `S_q ;; H_q ;; T_q ;; CNOT_{c,q} ;; T_q⁻¹ ;; H_q ;; Z_q ;; S_q`. -/
def chGateCirc {n : ℕ} (c q : Wire n) (hne : c ≠ q) : Circuit n :=
  Circuit.S q ;;ᶜ
  Circuit.H q ;;ᶜ
  Circuit.T q ;;ᶜ
  Circuit.CNOT c q hne ;;ᶜ
  (Circuit.T q).inverse ;;ᶜ
  Circuit.H q ;;ᶜ
  Circuit.Z q ;;ᶜ
  Circuit.S q
theorem count_chGateCirc {n : ℕ} (c q : Wire n) (hne : c ≠ q) : (chGateCirc c q hne).count .T
    = 2 ∧ (chGateCirc c q hne).count .TOFF = 0 := by
  constructor
  · simp [chGateCirc, Circuit.Z, Circuit.H, Circuit.T, Circuit.S, Circuit.CNOT,
      Circuit.inverse, Circuit.inverseGate, Circuit.sequence]
  · simp [chGateCirc, Circuit.Z, Circuit.H, Circuit.T, Circuit.S, Circuit.CNOT,
      Circuit.inverse, Circuit.inverseGate, Circuit.sequence]
private theorem sqrtHalf_mul_sqrtTwo_loc : sqrtHalf * (√2 : ℂ) = 1 := by
  dsimp [sqrtHalf]
  rw [← Complex.ofReal_mul, ← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  norm_num
private theorem omega8P_eq_sqrtHalf : omega8P = (1 + Complex.I) * sqrtHalf := by
  have hne : (√2 : ℂ) ≠ 0 := by
    exact_mod_cast Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 2)
  dsimp [omega8P]
  rw [div_eq_iff hne, mul_assoc, sqrtHalf_mul_sqrtTwo_loc, mul_one]
private theorem ket_S_mbh {n : ℕ} (q : Wire n) (δ : BitAssignment n) :
    (Circuit.S q).eval.1.mulVec (ket δ) =
      (if δ q = 0 then (1 : ℂ) else Complex.I) • ket δ := by
  have hk : OctahedralOrbit.ket δ = ket δ := rfl
  simpa only [hk] using p2t_ket_S q δ
private theorem ket_T_mbh {n : ℕ} (q : Wire n) (δ : BitAssignment n) :
    (Circuit.T q).eval.1.mulVec (ket δ) = (if δ q = 0 then (1 : ℂ) else omega8P) • ket δ := by
  have hk : OctahedralOrbit.ket δ = ket δ := rfl
  have hw : p2t_omega8 = omega8P := rfl
  simpa only [hk, hw] using p2t_ket_T q δ
private theorem ket_Tinv_mbh {n : ℕ} (q : Wire n) (δ : BitAssignment n) :
    (Circuit.T q).inverse.eval.1.mulVec (ket δ) =
      (if δ q = 0 then (1 : ℂ) else -omega8P ^ 3) • ket δ := by
  have hk : OctahedralOrbit.ket δ = ket δ := rfl
  have hw : p2t_omega8 = omega8P := rfl
  simpa only [hk, hw] using p2t_ket_Tinv q δ
theorem chGateCirc_mulVec_ket_zero {n : ℕ} (c q : Wire n) (hne : c ≠ q) (δ : BitAssignment n)
    (hc0 : δ c = 0) : (chGateCirc c q hne).eval.1.mulVec (ket δ) = ket δ := by
  have hs2 : sqrtHalf ^ 2 = 1 / 2 := by rw [sq, sqrtHalf_mul_sqrtHalf]
  have hs3 : sqrtHalf ^ 3 = (1 / 2 : ℂ) * sqrtHalf := by linear_combination sqrtHalf * hs2
  have hs4 : sqrtHalf ^ 4 = 1 / 4 := by linear_combination (sqrtHalf ^ 2 + 1 / 2) * hs2
  have hs5 : sqrtHalf ^ 5 = (1 / 4 : ℂ) * sqrtHalf := by linear_combination sqrtHalf * hs4
  have hs6 : sqrtHalf ^ 6 = 1 / 8 := by linear_combination sqrtHalf ^ 2 * hs4 + (1 / 4 : ℂ) * hs2
  have hi2 : Complex.I ^ 2 = -1 := Complex.I_sq
  have hi3 : Complex.I ^ 3 = -Complex.I := by linear_combination Complex.I * hi2
  have hi4 : Complex.I ^ 4 = 1 := by linear_combination (Complex.I ^ 2 - 1) * hi2
  have hi5 : Complex.I ^ 5 = Complex.I := by linear_combination Complex.I * hi4
  have hi6 : Complex.I ^ 6 = -1 := by linear_combination Complex.I * hi5 + hi2
  have hc_u : ∀ b : ZMod 2, Function.update δ q b c = 0 :=
    fun b ↦ (Function.update_of_ne hne b δ).trans hc0
  rcases bit_cases (δ q) with hq | hq
  · have hself : Function.update δ q 0 = δ := hq ▸ Function.update_eq_self q δ
    dsimp only [chGateCirc]
    simp only [eval_seq_mulVec, ket_S_mbh, ket_Z, ket_T_mbh, ket_Tinv_mbh, ket_H, ket_CNOT,
      Matrix.mulVec_smul, Matrix.mulVec_add, hq, hc0, hc_u, Function.update_self,
      Function.update_idem, add_zero, bitSign,
      one_ne_zero, ↓reduceIte, omega8P_eq_sqrtHalf, hself]
    ext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring_nf; simp only [hs2, hs6, hi2, hi3, hi4, hi5]; ring
  · have hself : Function.update δ q 1 = δ := hq ▸ Function.update_eq_self q δ
    dsimp only [chGateCirc]
    simp only [eval_seq_mulVec, ket_S_mbh, ket_Z, ket_T_mbh, ket_Tinv_mbh, ket_H, ket_CNOT,
      Matrix.mulVec_smul, Matrix.mulVec_add, hq, hc0, hc_u, Function.update_self,
      Function.update_idem, add_zero, bitSign,
      one_ne_zero, ↓reduceIte, omega8P_eq_sqrtHalf, hself]
    ext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring_nf; simp only [hs2, hs6, hi2, hi3, hi4, hi5, hi6]; ring
theorem chGateCirc_mulVec_ket_one {n : ℕ} (c q : Wire n) (hne : c ≠ q) (δ : BitAssignment n)
    (hc1 : δ c = 1) :
    (chGateCirc c q hne).eval.1.mulVec (ket δ) = (Circuit.H q).eval.1.mulVec (ket δ) := by
  have hs2 : sqrtHalf ^ 2 = 1 / 2 := by rw [sq, sqrtHalf_mul_sqrtHalf]
  have hs3 : sqrtHalf ^ 3 = (1 / 2 : ℂ) * sqrtHalf := by linear_combination sqrtHalf * hs2
  have hs4 : sqrtHalf ^ 4 = 1 / 4 := by linear_combination (sqrtHalf ^ 2 + 1 / 2) * hs2
  have hs5 : sqrtHalf ^ 5 = (1 / 4 : ℂ) * sqrtHalf := by linear_combination sqrtHalf * hs4
  have hs6 : sqrtHalf ^ 6 = 1 / 8 := by linear_combination sqrtHalf ^ 2 * hs4 + (1 / 4 : ℂ) * hs2
  have hi2 : Complex.I ^ 2 = -1 := Complex.I_sq
  have hi3 : Complex.I ^ 3 = -Complex.I := by linear_combination Complex.I * hi2
  have hi4 : Complex.I ^ 4 = 1 := by linear_combination (Complex.I ^ 2 - 1) * hi2
  have hi5 : Complex.I ^ 5 = Complex.I := by linear_combination Complex.I * hi4
  have hi6 : Complex.I ^ 6 = -1 := by linear_combination Complex.I * hi5 + hi2
  have hc_u : ∀ b : ZMod 2, Function.update δ q b c = 1 :=
    fun b ↦ (Function.update_of_ne hne b δ).trans hc1
  have h11 : (1 : ZMod 2) + 1 = 0 := rfl
  have h01 : (0 : ZMod 2) + 1 = 1 := rfl
  rcases bit_cases (δ q) with hq | hq
  · dsimp only [chGateCirc]
    simp only [eval_seq_mulVec, ket_S_mbh, ket_Z, ket_T_mbh, ket_Tinv_mbh, ket_H, ket_CNOT,
      Matrix.mulVec_smul, Matrix.mulVec_add, hq, hc_u, Function.update_self,
      Function.update_idem, h01, h11, bitSign,
      one_ne_zero, ↓reduceIte, omega8P_eq_sqrtHalf]
    ext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring_nf; simp only [hs3, hs5, hi2, hi3, hi4]; ring
  · dsimp only [chGateCirc]
    simp only [eval_seq_mulVec, ket_S_mbh, ket_Z, ket_T_mbh, ket_Tinv_mbh, ket_H, ket_CNOT,
      Matrix.mulVec_smul, Matrix.mulVec_add, hq, hc_u, Function.update_self,
      Function.update_idem, h01, h11, bitSign,
      one_ne_zero, ↓reduceIte, omega8P_eq_sqrtHalf]
    ext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring_nf; simp only [hs3, hs5, hi2, hi3, hi4, hi5]; ring
attribute [local semireducible] projBit_dqmu
theorem subspaceStep_remeasureIf_balanced {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    (v : Var) (q : Wire n) (c₁ : Circuit n) (R_pre R_mid : Operator (2 ^ n))
    (h0 : projBit_dqmu q 0 * R_pre = sqrtHalf • R_mid)
    (h1 : c₁.eval.1 * (projBit_dqmu q 1 * R_pre) = sqrtHalf • R_mid) :
    SubspaceStep R_pre R_mid (remeasureIf_dqmu v q c₁) := fun M ↦ by
  let P₀ := projBit_dqmu q 0
  let P₁ := projBit_dqmu q 1
  have hp0h : P₀ᴴ = P₀ := (QRegister.singleton q).basisOutcomeProjector_conjTranspose 0
  have hp1h : P₁ᴴ = P₁ := (QRegister.singleton q).basisOutcomeProjector_conjTranspose 1
  let N_mid := wp (remeasureIf_dqmu v q c₁).compile (fun _ ↦ M) (fun _ ↦ 0)
  have hwp : wp (remeasureIf_dqmu v q c₁).compile (fun _ ↦ M) = (fun _ ↦ N_mid) :=
    funext fun _ ↦ by
      simp [N_mid, remeasureIf_dqmu, DynamicCircuit.compile, wpQAssignCompat,
        QProg.measureRegister, qMeasure_obs_map, Circuit.compile]
  have hmeas : N_mid.1 = M.1.conj P₀ + (M.1.conj (star c₁.eval.1)).conj P₁ := by
    simp only [N_mid, remeasureIf_dqmu, DynamicCircuit.compile, wp_qSeq, wp_qIf,
      QProg.measureRegister,
      wp_qMeasure_apply, qMeasure_obs_map_coe, CQAssertionCompat.subst_apply]
    change ∑ o : Fin 2, _ = _
    rw [Fin.sum_univ_two]
    simp [qMeasure_outcome_herm_eq_conj, wpQAssignCompat, Matrix.star_eq_conjTranspose,
      QRegister.computationalBasisMeasurement_apply, projBit_dqmu, P₀, P₁]
  have hm := congrArg HermitianMat.mat hmeas
  rw [HermitianMat.mat_add, conj_apply_mat, conj_apply_mat, conj_apply_mat,
    Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose, hp0h, hp1h] at hm
  change N_mid.1.1 = P₀ * M.1.1 * P₀ + P₁ * (c₁.eval.1ᴴ * M.1.1 * c₁.eval.1) * P₁ at hm
  have h0_t : R_preᴴ * (P₀ * M.1.1 * P₀) * R_pre =
      (sqrtHalf * sqrtHalf) • (R_midᴴ * M.1.1 * R_mid) := by
    rw [show R_preᴴ * (P₀ * M.1.1 * P₀) * R_pre = (P₀ * R_pre)ᴴ * M.1.1 * (P₀ * R_pre) by
      simp only [Matrix.conjTranspose_mul, hp0h, Matrix.mul_assoc], h0]
    simp only [Matrix.conjTranspose_smul, star_sqrtHalf, Matrix.smul_mul, Matrix.mul_smul,
      smul_smul, Matrix.mul_assoc]
  have h1_t : R_preᴴ * (P₁ * (c₁.eval.1ᴴ * M.1.1 * c₁.eval.1) * P₁) * R_pre =
      (sqrtHalf * sqrtHalf) • (R_midᴴ * M.1.1 * R_mid) := by
    rw [show R_preᴴ * (P₁ * (c₁.eval.1ᴴ * M.1.1 * c₁.eval.1) * P₁) * R_pre =
        (c₁.eval.1 * (P₁ * R_pre))ᴴ * M.1.1 * (c₁.eval.1 * (P₁ * R_pre)) by
      simp only [Matrix.conjTranspose_mul, hp1h, Matrix.mul_assoc], h1]
    simp only [Matrix.conjTranspose_smul, star_sqrtHalf, Matrix.smul_mul, Matrix.mul_smul,
      smul_smul, Matrix.mul_assoc]
  refine ⟨N_mid, hwp, ?_⟩
  rw [hm, Matrix.mul_add, Matrix.add_mul, h0_t, h1_t, ← add_smul,
    show sqrtHalf * sqrtHalf + sqrtHalf * sqrtHalf = (1 : ℂ) by
      linear_combination 2 * sqrtHalf_mul_sqrtHalf,
    one_smul]
/-! ## Balanced Z-Reset & X-Unload SubspaceStep Bridges -/
theorem subspaceStep_seq_zResetFixup {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    (v : Var) (q : Wire n) (cFix : Circuit n)
    {R₀ R₁ R₂ : Operator (2 ^ n)} {p : DynamicCircuit Var n}
    (hp : SubspaceStep (Var := Var) R₀ R₁ p)
    (hK₀ : (QRegister.singleton q).basisOutcomeProjector 0 * R₁ = sqrtHalf • R₂)
    (hK₁ : (cFix.eval.1 * (Circuit.X q).eval.1 *
      (QRegister.singleton q).basisOutcomeProjector 1) * R₁ = sqrtHalf • R₂) :
    SubspaceStep (Var := Var) R₀ R₂ (.seq p (zResetFixupDyn v q cFix)) := by
  have h1' : (Circuit.X q ;;ᶜ cFix).eval.1 * (projBit_dqmu q 1 * R₁) = sqrtHalf • R₂ := by
    simpa only [Circuit.eval_seq, Submonoid.coe_mul, projBit_dqmu, Matrix.mul_assoc] using hK₁
  exact hp.seq (subspaceStep_remeasureIf_balanced v q (Circuit.X q ;;ᶜ cFix) R₁ R₂ hK₀ h1')
theorem subspaceStep_xUnloadCzPairsSeqDyn {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    (v : Var) (q : Wire n) (pairs : List (WirePair n)) (rest : DynamicCircuit Var n)
    (f : BitAssignment n → ZMod 2) (hf : ∀ β a, f (Function.update β q a) = f β)
    (hf_eq : ∀ β, f β = czPairsParity pairs β) (R R_out : Operator (2 ^ n))
    (hq0 : projBit_dqmu q 0 * R = R) (hRest : SubspaceStep R R_out rest) : SubspaceStep
    ((xorWireUnitary q f hf).1 * R) R_out (xUnloadCzPairsSeqDyn v q pairs rest) := by
  let R_H := (Circuit.H q).eval.1 * ((xorWireUnitary q f hf).1 * R)
  have h0_mat : projBit_dqmu q 0 * ((Circuit.H q).eval.1 * ((xorWireUnitary q f hf).1 *
      projBit_dqmu q 0)) = sqrtHalf • projBit_dqmu q 0 := by
    apply matrix_ext_ket; intro β
    simp only [← Matrix.mulVec_mulVec, Matrix.smul_mulVec, projBit_dqmu, ket_projector_zero]
    by_cases hβ : β q = 0
    · have hself : Function.update β q 0 = β := hβ ▸ Function.update_eq_self q β
      simp only [hβ, ↓reduceIte, xorWireUnitary_mulVec_ket, ket_H, Matrix.mulVec_smul,
        Matrix.mulVec_add, Function.update_idem, Function.update_self, ket_projector_zero, hself]
      simp [one_ne_zero]
    · simp [hβ, Matrix.mulVec_zero]
  have h1_mat :
      (Circuit.X q ;;ᶜ czPairsCircuit pairs).eval.1 *
        (projBit_dqmu q 1 * ((Circuit.H q).eval.1 * ((xorWireUnitary q f hf).1 * projBit_dqmu q
          0))) =
        sqrtHalf • projBit_dqmu q 0 := by
    apply matrix_ext_ket; intro β
    simp only [← Matrix.mulVec_mulVec, Matrix.smul_mulVec, projBit_dqmu, ket_projector_zero]
    by_cases hβ : β q = 0
    · have hself : Function.update β q 0 = β := hβ ▸ Function.update_eq_self q β
      have h11 : (1 : ZMod 2) + 1 = 0 := rfl
      simp only [hβ, ↓reduceIte, xorWireUnitary_mulVec_ket, ket_H, Matrix.mulVec_smul,
        Matrix.mulVec_add, Function.update_idem, Function.update_self, ket_projector_one,
        zero_add, eval_seq_mulVec, ket_X, h11, hself,
        czPairsCircuit_mulVec_ket, ← hf_eq, smul_smul, bitSign_mul_self, one_smul]
      simp [zero_ne_one]
    · simp [hβ, Matrix.mulVec_zero]
  have h0 : projBit_dqmu q 0 * R_H = sqrtHalf • R := by
    calc projBit_dqmu q 0 * R_H
        = projBit_dqmu q 0 * ((Circuit.H q).eval.1 *
            ((xorWireUnitary q f hf).1 * (projBit_dqmu q 0 * R))) := by
            dsimp only [R_H]; rw [hq0]
      _ = (projBit_dqmu q 0 * ((Circuit.H q).eval.1 *
            ((xorWireUnitary q f hf).1 * projBit_dqmu q 0))) * R := by
            simp only [Matrix.mul_assoc]
      _ = (sqrtHalf • projBit_dqmu q 0) * R := by rw [h0_mat]
      _ = sqrtHalf • (projBit_dqmu q 0 * R) := Matrix.smul_mul _ _ _
      _ = sqrtHalf • R := by rw [hq0]
  have h1 : (Circuit.X q ;;ᶜ czPairsCircuit pairs).eval.1 * (projBit_dqmu q 1 * R_H) =
      sqrtHalf • R := by
    calc (Circuit.X q ;;ᶜ czPairsCircuit pairs).eval.1 * (projBit_dqmu q 1 * R_H)
        = (Circuit.X q ;;ᶜ czPairsCircuit pairs).eval.1 *
            (projBit_dqmu q 1 * ((Circuit.H q).eval.1 *
              ((xorWireUnitary q f hf).1 * (projBit_dqmu q 0 * R)))) := by
            dsimp only [R_H]; rw [hq0]
      _ = ((Circuit.X q ;;ᶜ czPairsCircuit pairs).eval.1 *
            (projBit_dqmu q 1 * ((Circuit.H q).eval.1 *
              ((xorWireUnitary q f hf).1 * projBit_dqmu q 0)))) * R := by
            simp only [Matrix.mul_assoc]
      _ = (sqrtHalf • projBit_dqmu q 0) * R := by rw [h1_mat]
      _ = sqrtHalf • (projBit_dqmu q 0 * R) := Matrix.smul_mul _ _ _
      _ = sqrtHalf • R := by rw [hq0]
  exact (subspaceStep_of_circuit _ (.H q)).seq
    ((subspaceStep_remeasureIf_balanced v q (.X q ;;ᶜ czPairsCircuit pairs) R_H R h0 h1).seq hRest)
/-- Operator sending each computational basis ket `ket δ` to `f δ`. -/
def mkVecOp {n : ℕ} (f : BitAssignment n → Fin (2 ^ n) → ℂ) : Operator (2 ^ n) :=
  Matrix.of fun row col ↦ f (basisBits n col) row
theorem mkVecOp_mulVec_ket {n : ℕ} (f : BitAssignment n → Fin (2 ^ n) → ℂ) (δ : BitAssignment n) :
    (mkVecOp f).mulVec (ket δ) = f δ := by
  ext row
  simp only [mkVecOp, Matrix.mulVec, dotProduct, Matrix.of_apply, ket, basisState]
  rw [Finset.sum_eq_single ((basisBitsEquiv n).symm δ)]
  · simp
  · intro col _ hne; simp [hne.symm]
  · intro habs; exact (habs (Finset.mem_univ _)).elim
/-- Pairwise disjointness bundle for a zero-gated W-state one-hot router. -/
structure WRouterDisj {D N n : ℕ} (wHas : Wire n) (wIdx : Fin D → Wire n)
    (wOut : Fin N → Wire n) (qEnc : Wire n) : Prop where
  has_ne_out : ∀ j, wHas ≠ wOut j
  has_ne_q : wHas ≠ qEnc
  idx_ne_out : ∀ d j, wIdx d ≠ wOut j
  idx_ne_q : ∀ d, wIdx d ≠ qEnc
  out_inj : ∀ i j, i ≠ j → wOut i ≠ wOut j
  out_ne_q : ∀ j, wOut j ≠ qEnc
theorem idxValPrefix_congr {D n : ℕ} (wIdx : Fin D → Wire n) (δ₁ δ₂ : BitAssignment n)
    (h : ∀ d : Fin D, δ₁ (wIdx d) = δ₂ (wIdx d)) :
    ∀ (m : ℕ) (hm : m ≤ D), idxValPrefix wIdx δ₁ m hm = idxValPrefix wIdx δ₂ m hm
  | 0, _ => rfl
  | m + 1, hm => by
      dsimp only [idxValPrefix]
      rw [idxValPrefix_congr wIdx δ₁ δ₂ h m (Nat.le_of_succ_le hm), h ⟨m, hm⟩]
theorem idxValD_congr {D n : ℕ} (wIdx : Fin D → Wire n) {δ₁ δ₂ : BitAssignment n}
    (h : ∀ d : Fin D, δ₁ (wIdx d) = δ₂ (wIdx d)) : idxValD wIdx δ₁ = idxValD wIdx δ₂ :=
    idxValPrefix_congr wIdx δ₁ δ₂ h D le_rfl
/-- Involutive bit-map toggling `wOut (idxValD wIdx δ)` by `δ wHas` when `idxValD wIdx δ < N`. -/
def toggleOneHotBits {D N n : ℕ} (wHas : Wire n) (wIdx : Fin D → Wire n)
    (wOut : Fin N → Wire n) (δ : BitAssignment n) : BitAssignment n :=
  if h : idxValD wIdx δ < N then
    let t := wOut ⟨idxValD wIdx δ, h⟩
    Function.update δ t (δ t + δ wHas)
  else δ
theorem toggleOneHotBits_invol {D N n : ℕ} (wHas : Wire n) (wIdx : Fin D → Wire n)
    (wOut : Fin N → Wire n) (hHasOut : ∀ j, wHas ≠ wOut j) (hIdxOut : ∀ d j, wIdx d ≠ wOut j)
    (δ : BitAssignment n) :
    toggleOneHotBits wHas wIdx wOut (toggleOneHotBits wHas wIdx wOut δ) = δ := by
  let δ' := toggleOneHotBits wHas wIdx wOut δ
  change toggleOneHotBits wHas wIdx wOut δ' = δ
  by_cases h : idxValD wIdx δ < N
  · have h1 : δ' = Function.update δ (wOut ⟨idxValD wIdx δ, h⟩)
        (δ (wOut ⟨idxValD wIdx δ, h⟩) + δ wHas) := by
      dsimp only [δ', toggleOneHotBits]; rw [dite_eq_left h]
    have hIdx : idxValD wIdx δ' = idxValD wIdx δ :=
      idxValD_congr wIdx fun d ↦ by rw [h1, Function.update_of_ne (hIdxOut d _)]
    have h2 : idxValD wIdx δ' < N := hIdx.symm ▸ h
    dsimp only [toggleOneHotBits]
    rw [dite_eq_left h2]
    have hFin : (⟨idxValD wIdx δ', h2⟩ : Fin N) = ⟨idxValD wIdx δ, h⟩ := Fin.ext hIdx
    rw [hFin, h1, Function.update_self, Function.update_of_ne (hHasOut _),
      Function.update_idem, add_assoc, CharTwo.add_self_eq_zero, add_zero, Function.update_eq_self]
  · have h1 : δ' = δ := by dsimp only [δ', toggleOneHotBits]; rw [dite_eq_right h]
    rw [h1]; dsimp only [toggleOneHotBits]; rw [dite_eq_right h]
/-- Permutation unitary for `toggleOneHotBits`. -/
def uOneHotToggle {D N n : ℕ} (wHas : Wire n) (wIdx : Fin D → Wire n) (wOut : Fin N → Wire n)
    (hHasOut : ∀ j, wHas ≠ wOut j) (hIdxOut : ∀ d j, wIdx d ≠ wOut j) : Unitary (2 ^ n) :=
  permUnitary
    { toFun := toggleOneHotBits wHas wIdx wOut
      invFun := toggleOneHotBits wHas wIdx wOut
      left_inv := toggleOneHotBits_invol wHas wIdx wOut hHasOut hIdxOut
      right_inv := toggleOneHotBits_invol wHas wIdx wOut hHasOut hIdxOut }
theorem uOneHotToggle_mulVec_ket {D N n : ℕ} (wHas : Wire n) (wIdx : Fin D → Wire n)
    (wOut : Fin N → Wire n) (hHasOut : ∀ j, wHas ≠ wOut j) (hIdxOut : ∀ d j, wIdx d ≠ wOut j)
    (δ : BitAssignment n) : (uOneHotToggle wHas wIdx wOut hHasOut hIdxOut).1.mulVec (ket δ) =
    ket (toggleOneHotBits wHas wIdx wOut δ) := permUnitary_mulVec_ket _ δ
/-- Left-to-right sequential composition of `m` circuits `f 0 ;;ᶜ ... ;;ᶜ f (m - 1)`. -/
def seqNat {n : ℕ} : (m : ℕ) → ((i : ℕ) → i < m → Circuit n) → Circuit n
  | 0, _ => .identity
  | m + 1, f => seqNat m (fun i hi ↦ f i (Nat.lt_succ_of_lt hi)) ;;ᶜ f m (Nat.lt_succ_self m)
theorem count_seqNat_T {n : ℕ} (c : ℕ) :
    ∀ (m : ℕ) (f : (i : ℕ) → i < m → Circuit n),
      (∀ i hi, (f i hi).count .T = c) → (seqNat m f).count .T = m * c
  | 0, _, _ => by simp [seqNat]
  | m + 1, f, hc => by
      simp only [seqNat, Circuit.count_seq,
        count_seqNat_T c m _ (fun i hi ↦ hc i (Nat.lt_succ_of_lt hi)), hc m (Nat.lt_succ_self m)]
      ring
theorem count_seqNat_TOFF_zero {n : ℕ} :
    ∀ (m : ℕ) (f : (i : ℕ) → i < m → Circuit n),
      (∀ i hi, (f i hi).count .TOFF = 0) → (seqNat m f).count .TOFF = 0
  | 0, _, _ => rfl
  | m + 1, f, hc => by
      simp [seqNat, Circuit.count_seq,
        count_seqNat_TOFF_zero m _ (fun i hi ↦ hc i (Nat.lt_succ_of_lt hi)),
        hc m (Nat.lt_succ_self m)]
theorem seqNat_mulVec_fixed {n : ℕ} (ψ : Fin (2 ^ n) → ℂ) :
    ∀ (m : ℕ) (f : (i : ℕ) → i < m → Circuit n),
      (∀ i hi, (f i hi).eval.1.mulVec ψ = ψ) → (seqNat m f).eval.1.mulVec ψ = ψ
  | 0, _, _ => by simp [seqNat, Circuit.eval_identity]
  | m + 1, f, hc => by
      rw [seqNat, eval_seq_mulVec,
        seqNat_mulVec_fixed ψ m _ (fun i hi ↦ hc i (Nat.lt_succ_of_lt hi)),
        hc m (Nat.lt_succ_self m)]
theorem seqNat_mulVec_single {n : ℕ} (ψ ψ' : Fin (2 ^ n) → ℂ) (i₀ : ℕ) :
    ∀ (m : ℕ) (f : (i : ℕ) → i < m → Circuit n),
      (∀ i (hi : i < m), i < i₀ → (f i hi).eval.1.mulVec ψ = ψ) →
      (∀ hi₀ : i₀ < m, (f i₀ hi₀).eval.1.mulVec ψ = ψ') →
      (∀ i (hi : i < m), i₀ < i → (f i hi).eval.1.mulVec ψ' = ψ') →
      (seqNat m f).eval.1.mulVec ψ = if i₀ < m then ψ' else ψ
  | 0, _, _, _, _ => by simp [seqNat, Circuit.eval_identity]
  | m + 1, f, hlt, heq, hgt => by
      rw [seqNat, eval_seq_mulVec,
        seqNat_mulVec_single ψ ψ' i₀ m _
          (fun i hi ↦ hlt i (Nat.lt_succ_of_lt hi))
          (fun hi₀ ↦ heq (Nat.lt_succ_of_lt hi₀))
          (fun i hi ↦ hgt i (Nat.lt_succ_of_lt hi))]
      by_cases hm : i₀ < m
      · rw [ite_eq_left hm, ite_eq_left (Nat.lt_succ_of_lt hm)]
        exact hgt m (Nat.lt_succ_self m) hm
      · rw [ite_eq_right hm]
        by_cases hme : i₀ = m
        · subst hme
          rw [ite_eq_left (Nat.lt_succ_self i₀)]
          exact heq (Nat.lt_succ_self i₀)
        · have hnot : ¬ i₀ < m + 1 := by omega
          rw [ite_eq_right hnot]
          exact hlt m (Nat.lt_succ_self m) (by omega)
/- Section 3: R-block CH-tree expansion and barrel-shift primitives -/
theorem w_ne_of_pair_ne {n R k : ℕ} {w : Fin R → Fin (2 ^ k) → Wire n}
    (hw : ∀ b₁ p₁ b₂ p₂, w b₁ p₁ = w b₂ p₂ → b₁ = b₂ ∧ p₁ = p₂)
    {b₁ b₂ : Fin R} {p₁ p₂ : Fin (2 ^ k)} (h : b₁ ≠ b₂ ∨ p₁ ≠ p₂) :
    w b₁ p₁ ≠ w b₂ p₂ := fun e ↦ by
  obtain ⟨hb, hp⟩ := hw b₁ p₁ b₂ p₂ e
  exact h.elim (fun hne ↦ hne hb) (fun hne ↦ hne hp)
/-- Single `2-T` W-state splitter `chGateCirc a b ;;ᶜ CNOT b a`. -/
def wSplitPair {n : ℕ} (a b : Wire n) (hab : a ≠ b) : Circuit n :=
  chGateCirc a b hab ;;ᶜ Circuit.CNOT b a hab.symm
theorem count_wSplitPair {n : ℕ} (a b : Wire n) (hab : a ≠ b) :
    (wSplitPair a b hab).count .T = 2 ∧ (wSplitPair a b hab).count .TOFF = 0 := by
  obtain ⟨ht, hf⟩ := count_chGateCirc a b hab
  exact ⟨by simpa [wSplitPair, Circuit.count_seq, Circuit.CNOT] using ht,
    by simpa [wSplitPair, Circuit.count_seq, Circuit.CNOT] using hf⟩
theorem wSplitPair_mulVec_ket_zero {n : ℕ} (a b : Wire n) (hab : a ≠ b) (δ : BitAssignment n)
    (ha0 : δ a = 0) (hb0 : δ b = 0) : (wSplitPair a b hab).eval.1.mulVec (ket δ) = ket δ := by
  rw [wSplitPair, eval_seq_mulVec, chGateCirc_mulVec_ket_zero a b hab δ ha0,
    ket_CNOT b a hab.symm δ, ha0, hb0, add_zero,
    show Function.update δ a 0 = δ from ha0 ▸ Function.update_eq_self a δ]
theorem wSplitPair_mulVec_ket_one {n : ℕ} (a b : Wire n) (hab : a ≠ b)
    (δ : BitAssignment n) (ha0 : δ a = 0) (hb0 : δ b = 0) :
    (wSplitPair a b hab).eval.1.mulVec (ket (Function.update δ a 1)) =
      sqrtHalf • (ket (Function.update δ a 1) + ket (Function.update δ b 1)) := by
  have ha1 : Function.update δ a 1 a = 1 := Function.update_self a 1 δ
  have hb0' : Function.update δ a 1 b = 0 := (Function.update_of_ne hab.symm 1 δ).trans hb0
  rw [wSplitPair, eval_seq_mulVec, chGateCirc_mulVec_ket_one a b hab _ ha1,
    ket_H b (Function.update δ a 1), hb0',
    show bitSign (0 : ZMod 2) = (1 : ℂ) from rfl, one_smul,
    show Function.update (Function.update δ a 1) b 0 = Function.update δ a 1 from
      hb0' ▸ Function.update_eq_self b _,
    Matrix.mulVec_smul, Matrix.mulVec_add, ket_CNOT, ket_CNOT]
  have hu1 : Function.update (Function.update δ a 1) a
      (Function.update δ a 1 a + Function.update δ a 1 b) = Function.update δ a 1 := by
    rw [ha1, hb0', add_zero, Function.update_idem]
  have hu2 : Function.update (Function.update (Function.update δ a 1) b 1) a
      (Function.update (Function.update δ a 1) b 1 a +
        Function.update (Function.update δ a 1) b 1 b) = Function.update δ b 1 := by
    rw [Function.update_of_ne hab 1 _, ha1, Function.update_self,
      show (1 : ZMod 2) + 1 = 0 from rfl]
    funext u
    by_cases hua : u = a
    · subst hua; rw [Function.update_self, Function.update_of_ne hab, ha0]
    · rw [Function.update_of_ne hua]
      by_cases hub : u = b
      · subst hub; rw [Function.update_self, Function.update_self]
      · rw [Function.update_of_ne hub, Function.update_of_ne hua, Function.update_of_ne hub]
  rw [hu1, hu2]
theorem div_lt_of_lt_mul_right {i A B : ℕ} (hB : 0 < B) (hi : i < A * B) : i / B < A :=
  (Nat.div_lt_iff_lt_mul hB).mpr hi
theorem pair_lo_lt {r k j : ℕ} (hr : r < k) (hj : j < 2 ^ r) : j < 2 ^ k :=
  Nat.lt_of_lt_of_le hj (Nat.pow_le_pow_right (by omega) (Nat.le_of_lt hr))
theorem pair_hi_lt {r k j : ℕ} (hr : r < k) (hj : j < 2 ^ r) : j + 2 ^ r < 2 ^ k := by
  have h1 : 2 ^ (r + 1) ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) hr
  have h2 : 2 ^ (r + 1) = 2 ^ r + 2 ^ r := by ring
  omega
/-- Round `r < k` of `wSplitPair` across all `R` blocks and `j < 2^r`. -/
def wTreeRound {n : ℕ} (R k : ℕ) (w : Fin R → Fin (2 ^ k) → Wire n)
    (hw : ∀ b₁ p₁ b₂ p₂, w b₁ p₁ = w b₂ p₂ → b₁ = b₂ ∧ p₁ = p₂)
    (r : ℕ) (hr : r < k) : Circuit n :=
  seqNat (R * 2 ^ r) fun i hi ↦
    let hB : 0 < 2 ^ r := Nat.two_pow_pos r
    let blk : Fin R := ⟨i / 2 ^ r, div_lt_of_lt_mul_right hB hi⟩
    let j := i % 2 ^ r
    let hj : j < 2 ^ r := Nat.mod_lt i hB
    let p0 : Fin (2 ^ k) := ⟨j, pair_lo_lt hr hj⟩
    let p1 : Fin (2 ^ k) := ⟨j + 2 ^ r, pair_hi_lt hr hj⟩
    wSplitPair (w blk p0) (w blk p1)
      (w_ne_of_pair_ne hw (Or.inr fun e ↦ by
        have hv := congrArg Fin.val e; dsimp [p0, p1] at hv; omega))
/-- First `m ≤ k` rounds of `wTreeRound`. -/
def wTreePrefix {n : ℕ} (R k : ℕ) (w : Fin R → Fin (2 ^ k) → Wire n)
    (hw : ∀ b₁ p₁ b₂ p₂, w b₁ p₁ = w b₂ p₂ → b₁ = b₂ ∧ p₁ = p₂) :
    (m : ℕ) → m ≤ k → Circuit n
  | 0, _ => .identity
  | r + 1, hr => wTreePrefix R k w hw r (Nat.le_of_succ_le hr) ;;ᶜ wTreeRound R k w hw r hr
theorem count_wTreePrefix {n : ℕ} (R k : ℕ) (w : Fin R → Fin (2 ^ k) → Wire n)
    (hw : ∀ b₁ p₁ b₂ p₂, w b₁ p₁ = w b₂ p₂ → b₁ = b₂ ∧ p₁ = p₂) :
    ∀ (m : ℕ) (hm : m ≤ k),
      (wTreePrefix R k w hw m hm).count .T = 2 * R * (2 ^ m - 1) ∧
      (wTreePrefix R k w hw m hm).count .TOFF = 0
  | 0, _ => ⟨by simp [wTreePrefix], rfl⟩
  | r + 1, hr => by
      obtain ⟨ht, hf⟩ := count_wTreePrefix R k w hw r (Nat.le_of_succ_le hr)
      have hrt : (wTreeRound R k w hw r hr).count .T = (R * 2 ^ r) * 2 :=
        count_seqNat_T 2 (R * 2 ^ r) _ fun _ _ ↦ (count_wSplitPair _ _ _).1
      have hrf : (wTreeRound R k w hw r hr).count .TOFF = 0 :=
        count_seqNat_TOFF_zero (R * 2 ^ r) _ fun _ _ ↦ (count_wSplitPair _ _ _).2
      refine ⟨?_, by simp [wTreePrefix, Circuit.count_seq, hf, hrf]⟩
      rw [wTreePrefix, Circuit.count_seq, ht, hrt]
      have hp1 : 1 ≤ 2 ^ r := Nat.one_le_two_pow
      have hp2 : 2 ^ (r + 1) = 2 * 2 ^ r := by ring
      rw [Nat.mul_sub_left_distrib, Nat.mul_sub_left_distrib, hp2]
      have hle : 2 * R * 1 ≤ 2 * R * 2 ^ r := Nat.mul_le_mul_left (2 * R) hp1
      have heq1 : R * 2 ^ r * 2 = 2 * R * 2 ^ r := by ring
      have heq2 : 2 * R * (2 * 2 ^ r) = 2 * R * 2 ^ r + 2 * R * 2 ^ r := by ring
      omega
theorem enc_div_mod {A B a b : ℕ} (ha : a < A) (hb : b < B) :
    a * B + b < A * B ∧ (a * B + b) / B = a ∧ (a * B + b) % B = b := by
  have hB : 0 < B := by omega
  refine ⟨by nlinarith, ?_, ?_⟩
  · rw [Nat.mul_comm a B, Nat.mul_add_div hB, Nat.div_eq_of_lt hb, add_zero]
  · rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hb]
theorem enc_ne_iff {B i a b : ℕ} (hne : i ≠ a * B + b) : i / B ≠ a ∨ i % B ≠ b := by
  by_cases h1 : i / B = a
  · refine Or.inr fun h2 ↦ hne ?_
    have hd := Nat.div_add_mod i B
    rw [h1, h2, Nat.mul_comm] at hd
    exact hd.symm
  · exact Or.inl h1
theorem wTreeRound_mulVec_ket {n R k : ℕ} (w : Fin R → Fin (2 ^ k) → Wire n)
    (hw : ∀ b₁ p₁ b₂ p₂, w b₁ p₁ = w b₂ p₂ → b₁ = b₂ ∧ p₁ = p₂) (r : ℕ) (hr : r < k)
    (δ : BitAssignment n) (h0 : ∀ b p, δ (w b p) = 0) (bStar : Fin R) (s : Fin (2 ^ r)) :
    (wTreeRound R k w hw r hr).eval.1.mulVec
    (ket (Function.update δ (w bStar ⟨s.val, pair_lo_lt hr s.isLt⟩) 1)) = sqrtHalf • (ket
    (Function.update δ (w bStar ⟨s.val, pair_lo_lt hr s.isLt⟩) 1) + ket (Function.update δ (w
    bStar ⟨s.val + 2 ^ r, pair_hi_lt hr s.isLt⟩) 1)) := by
  let pS0 : Fin (2 ^ k) := ⟨s.val, pair_lo_lt hr s.isLt⟩
  let pS1 : Fin (2 ^ k) := ⟨s.val + 2 ^ r, pair_hi_lt hr s.isLt⟩
  let i₀ := bStar.val * 2 ^ r + s.val
  obtain ⟨hi₀, hdiv₀, hmod₀⟩ := enc_div_mod bStar.isLt s.isLt
  have hFixKet : ∀ (pX : Fin (2 ^ k)), (pX = pS0 ∨ pX = pS1) →
      ∀ i (hi : i < R * 2 ^ r), i ≠ i₀ →
        let hB : 0 < 2 ^ r := Nat.two_pow_pos r
        let blk : Fin R := ⟨i / 2 ^ r, div_lt_of_lt_mul_right hB hi⟩
        let hj : i % 2 ^ r < 2 ^ r := Nat.mod_lt i hB
        let p0 : Fin (2 ^ k) := ⟨i % 2 ^ r, pair_lo_lt hr hj⟩
        let p1 : Fin (2 ^ k) := ⟨i % 2 ^ r + 2 ^ r, pair_hi_lt hr hj⟩
        (wSplitPair (w blk p0) (w blk p1)
          (w_ne_of_pair_ne hw (Or.inr fun e ↦ by
            have hv := congrArg Fin.val e; dsimp [p0, p1] at hv; omega))).eval.1.mulVec
          (ket (Function.update δ (w bStar pX) 1)) =
          ket (Function.update δ (w bStar pX) 1) := by
    intro pX hpX i hi hne hB blk hj p0 p1
    have hdisj := enc_ne_iff hne
    have hne0 : w blk p0 ≠ w bStar pX := w_ne_of_pair_ne hw (by
      rcases hdisj with hdb | hdm
      · exact Or.inl fun e ↦ hdb (congrArg Fin.val e)
      · refine Or.inr fun e ↦ ?_
        have hv := congrArg Fin.val e
        rcases hpX with rfl | rfl <;> dsimp [p0, pS0, pS1] at hv <;> omega)
    have hne1 : w blk p1 ≠ w bStar pX := w_ne_of_pair_ne hw (by
      rcases hdisj with hdb | hdm
      · exact Or.inl fun e ↦ hdb (congrArg Fin.val e)
      · refine Or.inr fun e ↦ ?_
        have hv := congrArg Fin.val e; have hs := s.isLt
        rcases hpX with rfl | rfl <;> dsimp [p1, pS0, pS1] at hv <;> omega)
    exact wSplitPair_mulVec_ket_zero _ _ _ _
      ((Function.update_of_ne hne0 _ _).trans (h0 blk p0))
      ((Function.update_of_ne hne1 _ _).trans (h0 blk p1))
  have hSeq := seqNat_mulVec_single
    (ket (Function.update δ (w bStar pS0) 1))
    (sqrtHalf • (ket (Function.update δ (w bStar pS0) 1) + ket (Function.update δ (w bStar pS1) 1)))
    i₀ (R * 2 ^ r) _
    (fun i hi hlt ↦ hFixKet pS0 (Or.inl rfl) i hi (Nat.ne_of_lt hlt))
    (fun hi₀' ↦ by
      have hbEq : (⟨i₀ / 2 ^ r, div_lt_of_lt_mul_right (Nat.two_pow_pos r) hi₀'⟩ : Fin R) = bStar :=
        Fin.ext hdiv₀
      have hp0Eq : (⟨i₀ % 2 ^ r, pair_lo_lt hr (Nat.mod_lt i₀ (Nat.two_pow_pos r))⟩ : Fin (2 ^ k)) =
        pS0 :=
        Fin.ext hmod₀
      have hp1Eq : (⟨i₀ % 2 ^ r + 2 ^ r, pair_hi_lt hr (Nat.mod_lt i₀ (Nat.two_pow_pos r))⟩ : Fin (2
        ^ k)) = pS1 :=
        Fin.ext (by dsimp [pS1]; rw [hmod₀])
      simp only [hbEq, hp0Eq, hp1Eq]
      exact wSplitPair_mulVec_ket_one _ _ _ δ (h0 bStar pS0) (h0 bStar pS1))
    (fun i hi hgt ↦ by
      rw [Matrix.mulVec_smul, Matrix.mulVec_add,
        hFixKet pS0 (Or.inl rfl) i hi (Nat.ne_of_gt hgt),
        hFixKet pS1 (Or.inr rfl) i hi (Nat.ne_of_gt hgt)])
  have hi₀_lt : i₀ < R * 2 ^ r := hi₀
  rw [ite_eq_left hi₀_lt] at hSeq
  exact hSeq
theorem wTreePrefix_mulVec_ket {n R k : ℕ} (w : Fin R → Fin (2 ^ k) → Wire n)
    (hw : ∀ b₁ p₁ b₂ p₂, w b₁ p₁ = w b₂ p₂ → b₁ = b₂ ∧ p₁ = p₂)
    (δ : BitAssignment n) (h0 : ∀ b p, δ (w b p) = 0) (bStar : Fin R) :
    ∀ (m : ℕ) (hm : m ≤ k),
      (wTreePrefix R k w hw m hm).eval.1.mulVec
          (ket (Function.update δ (w bStar ⟨0, Nat.two_pow_pos k⟩) 1)) =
        (sqrtHalf ^ m) •
          ∑ s : Fin (2 ^ m),
            ket (Function.update δ
              (w bStar ⟨s.val, Nat.lt_of_lt_of_le s.isLt (Nat.pow_le_pow_right (by omega) hm)⟩) 1)
  | 0, _ => by
      simp only [wTreePrefix, Circuit.eval_identity, Submonoid.coe_one, Matrix.one_mulVec,
        _root_.pow_zero, one_smul]
      rw [Finset.sum_eq_single ⟨0, Nat.two_pow_pos 0⟩]
      · intro s _ hne; exfalso; apply hne; apply Fin.ext; have := s.isLt; dsimp at *; omega
      · intro habs; exact (habs (Finset.mem_univ _)).elim
  | r + 1, hr => by
      rw [wTreePrefix, eval_seq_mulVec,
        wTreePrefix_mulVec_ket w hw δ h0 bStar r (Nat.le_of_succ_le hr),
        Matrix.mulVec_smul, Matrix.mulVec_sum]
      simp_rw [wTreeRound_mulVec_ket w hw r hr δ h0 bStar]
      rw [← Finset.smul_sum, smul_smul, ← _root_.pow_succ]
      congr 1
      rw [Finset.sum_add_distrib]
      let e : Fin (2 ^ r + 2 ^ r) ≃ Fin (2 ^ (r + 1)) :=
        finCongr (by ring : 2 ^ r + 2 ^ r = 2 ^ (r + 1))
      rw [← e.sum_comp, Fin.sum_univ_add]
      congr 1
      refine Finset.sum_congr rfl fun s _ ↦ ?_
      congr 3; apply Fin.ext; dsimp [e]; omega
/- Section 1: Binary stride arithmetic and 3-CNOT swap -/
theorem shift_pos_lt {d k lo hi : ℕ} (hd : d ≤ k) (hlo : lo < 2 ^ d) (hhi : hi < 2 ^ (k - d)) :
    lo + 2 ^ d * hi < 2 ^ k := by
  have h1 : 2 ^ d * (hi + 1) ≤ 2 ^ d * 2 ^ (k - d) := Nat.mul_le_mul_left (2 ^ d) hhi
  have h2 : 2 ^ d * 2 ^ (k - d) = 2 ^ k := by rw [← Nat.pow_add, Nat.add_sub_of_le hd]
  have h3 : 2 ^ d * (hi + 1) = 2 ^ d * hi + 2 ^ d := by ring
  omega
theorem testBit_lo_add_mul_two_pow {d lo m : ℕ} (hlo : lo < 2 ^ d) :
    (lo + 2 ^ d * m).testBit d = decide (m % 2 = 1) := by
  rw [Nat.testBit_eq_decide_div_mod_eq, Nat.add_comm,
    Nat.mul_add_div (Nat.two_pow_pos d), Nat.div_eq_of_lt hlo, add_zero]
theorem testBit_add_two_pow_self {p0 d : ℕ} (h : p0.testBit d = false) :
    (p0 + 2 ^ d).testBit d = true := by
  rw [Nat.testBit_eq_decide_div_mod_eq] at h ⊢
  rw [Nat.add_div_right p0 (Nat.two_pow_pos d)]
  simp only [decide_eq_false_iff_not, decide_eq_true_eq] at h ⊢
  omega
/-- Even/odd decomposition `Fin M ⊕ Fin M ≃ Fin (2 * M)`. -/
def finTwoMulEquiv (M : ℕ) : Fin M ⊕ Fin M ≃ Fin (2 * M) where
  toFun
    | .inl q => ⟨2 * q.val, by omega⟩
    | .inr q => ⟨2 * q.val + 1, by omega⟩
  invFun x :=
    if x.val % 2 = 0 then .inl ⟨x.val / 2, by omega⟩ else .inr ⟨x.val / 2, by omega⟩
  left_inv
    | .inl q => by
        dsimp only
        rw [ite_eq_left (by omega)]
        exact congrArg Sum.inl (Fin.ext (by dsimp; omega))
    | .inr q => by
        dsimp only
        rw [ite_eq_right (by omega)]
        exact congrArg Sum.inr (Fin.ext (by dsimp; omega))
  right_inv x := by
    dsimp only
    split_ifs with h
    · exact Fin.ext (by dsimp; omega)
    · exact Fin.ext (by dsimp; omega)
/-- 3-CNOT wire swap (`0 T`, `0 TOFF`). -/
def swap3Cnot {n : ℕ} (a b : Wire n) (hab : a ≠ b) : Circuit n :=
  Circuit.CNOT a b hab ;;ᶜ Circuit.CNOT b a hab.symm ;;ᶜ Circuit.CNOT a b hab
theorem count_swap3Cnot {n : ℕ} (a b : Wire n) (hab : a ≠ b) :
    (swap3Cnot a b hab).count .T = 0 ∧ (swap3Cnot a b hab).count .TOFF = 0 := by
  simp [swap3Cnot, Circuit.count_seq, Circuit.CNOT]
theorem swap3Cnot_mulVec_ket_zero {n : ℕ} (a b : Wire n) (hab : a ≠ b) (δ : BitAssignment n)
    (ha : δ a = 0) (hb : δ b = 0) : (swap3Cnot a b hab).eval.1.mulVec (ket δ) = ket δ := by
  have ub : Function.update δ b 0 = δ := hb ▸ Function.update_eq_self b δ
  have ua : Function.update δ a 0 = δ := ha ▸ Function.update_eq_self a δ
  rw [swap3Cnot, eval_seq_mulVec, ket_CNOT, ha, hb, add_zero, ub,
    eval_seq_mulVec, ket_CNOT, ha, hb, add_zero, ua, ket_CNOT, ha, hb, add_zero, ub]
theorem swap3Cnot_mulVec_ket_dir {n : ℕ} (a b : Wire n) (hab : a ≠ b)
    (δ : BitAssignment n) (ha : δ a = 0) (hb : δ b = 0) (dir : Bool) :
    (swap3Cnot a b hab).eval.1.mulVec (ket (Function.update δ (if dir then b else a) 1)) =
      ket (Function.update δ (if dir then a else b) 1) := by
  cases dir
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [swap3Cnot, eval_seq_mulVec, ket_CNOT, Function.update_of_ne hab.symm, hb,
      Function.update_self, zero_add, eval_seq_mulVec, ket_CNOT, Function.update_of_ne hab,
      Function.update_self, Function.update_self, CharTwo.add_self_eq_zero,
      ket_CNOT, Function.update_of_ne hab.symm, Function.update_self, Function.update_self,
        add_zero]
    congr 1; funext u
    by_cases hua : u = a
    · subst hua; rw [Function.update_of_ne hab, Function.update_self, Function.update_of_ne hab, ha]
    · by_cases hub : u = b
      · subst hub; rw [Function.update_self, Function.update_self]
      · simp only [Function.update_of_ne hua, Function.update_of_ne hub]
  · simp only [↓reduceIte]
    rw [swap3Cnot, eval_seq_mulVec, ket_CNOT, Function.update_self,
      Function.update_of_ne hab, ha, add_zero, Function.update_idem,
      eval_seq_mulVec, ket_CNOT, Function.update_of_ne hab, ha, Function.update_self, zero_add,
      ket_CNOT, Function.update_of_ne hab.symm, Function.update_self, Function.update_self,
      CharTwo.add_self_eq_zero]
    congr 1; funext u
    by_cases hua : u = a
    · subst hua; rw [Function.update_of_ne hab, Function.update_self, Function.update_self]
    · by_cases hub : u = b
      · subst hub; rw [Function.update_self, Function.update_of_ne hab.symm, hb]
      · simp only [Function.update_of_ne hua, Function.update_of_ne hub]
/- Section 2: Odd-block parity gather and stride-`2^d` barrel swap -/
/-- CNOT from every `w blk p` with `p.val.testBit d = true` onto `qEnc`. -/
def cnotOddToEnc {n : ℕ} (R k : ℕ) (w : Fin R → Fin (2 ^ k) → Wire n) (qEnc : Wire n)
    (hwq : ∀ b p, w b p ≠ qEnc) (d : ℕ) : Circuit n :=
  seqNat (R * 2 ^ k) fun i hi ↦
    let hB : 0 < 2 ^ k := Nat.two_pow_pos k
    let blk : Fin R := ⟨i / 2 ^ k, div_lt_of_lt_mul_right hB hi⟩
    let p : Fin (2 ^ k) := ⟨i % 2 ^ k, Nat.mod_lt i hB⟩
    if (i % 2 ^ k).testBit d then Circuit.CNOT (w blk p) qEnc (hwq blk p) else .identity
theorem count_cnotOddToEnc {n : ℕ} (R k : ℕ) (w : Fin R → Fin (2 ^ k) → Wire n) (qEnc : Wire n)
    (hwq : ∀ b p, w b p ≠ qEnc) (d : ℕ) :
    (cnotOddToEnc R k w qEnc hwq d).count .T = 0 ∧
      (cnotOddToEnc R k w qEnc hwq d).count .TOFF = 0 :=
  ⟨(count_seqNat_T 0 (R * 2 ^ k) _ fun _ _ ↦ by
      dsimp only
      split_ifs
      · simp [Circuit.CNOT]
      · rfl).trans (Nat.mul_zero _),
   count_seqNat_TOFF_zero (R * 2 ^ k) _ fun _ _ ↦ by
      dsimp only
      split_ifs
      · simp [Circuit.CNOT]
      · rfl⟩
theorem cnotOddToEnc_mulVec_ket {n R k : ℕ} (w : Fin R → Fin (2 ^ k) → Wire n) (qEnc : Wire n)
    (hw : ∀ b₁ p₁ b₂ p₂, w b₁ p₁ = w b₂ p₂ → b₁ = b₂ ∧ p₁ = p₂) (hwq : ∀ b p, w b p ≠ qEnc)
    (d : ℕ) (δ : BitAssignment n) (hw0 : ∀ b p, δ (w b p) = 0) (hq0 : δ qEnc = 0)
    (bStar : Fin R) (pStar : Fin (2 ^ k)) : (cnotOddToEnc R k w qEnc hwq d).eval.1.mulVec
    (ket (Function.update δ (w bStar pStar) 1)) = ket (Function.update (Function.update δ (w
    bStar pStar) 1) qEnc (if pStar.val.testBit d then 1 else 0)) := by
  let δ₁ := Function.update δ (w bStar pStar) 1
  have hq1 : δ₁ qEnc = 0 := (Function.update_of_ne (hwq bStar pStar).symm 1 δ).trans hq0
  have hFix : ∀ (z : ZMod 2) (i : ℕ) (hi : i < R * 2 ^ k),
      i ≠ bStar.val * 2 ^ k + pStar.val →
        let hB : 0 < 2 ^ k := Nat.two_pow_pos k
        let blk : Fin R := ⟨i / 2 ^ k, div_lt_of_lt_mul_right hB hi⟩
        let p : Fin (2 ^ k) := ⟨i % 2 ^ k, Nat.mod_lt i hB⟩
        (if (i % 2 ^ k).testBit d then Circuit.CNOT (w blk p) qEnc (hwq blk p) else
          .identity).eval.1.mulVec
          (ket (Function.update δ₁ qEnc z)) = ket (Function.update δ₁ qEnc z) := by
    intro z i hi hne hB blk p
    split_ifs with htb
    · have hneW : w blk p ≠ w bStar pStar := w_ne_of_pair_ne hw (by
        rcases enc_ne_iff hne with hdb | hdm
        · exact Or.inl fun e ↦ hdb (congrArg Fin.val e)
        · exact Or.inr fun e ↦ hdm (congrArg Fin.val e))
      have hc0 : Function.update δ₁ qEnc z (w blk p) = 0 := by
        dsimp only [δ₁]
        rw [Function.update_of_ne (hwq blk p), Function.update_of_ne hneW, hw0]
      rw [ket_CNOT, hc0, add_zero, Function.update_idem, Function.update_self]
    · rw [Circuit.eval_identity, Submonoid.coe_one, Matrix.one_mulVec]
  by_cases htbS : pStar.val.testBit d
  · rw [ite_eq_left htbS]
    let i₀ := bStar.val * 2 ^ k + pStar.val
    obtain ⟨hi₀, hdiv₀, hmod₀⟩ := enc_div_mod bStar.isLt pStar.isLt
    have hz0 : Function.update δ₁ qEnc 0 = δ₁ := hq1 ▸ Function.update_eq_self qEnc δ₁
    have hSeq := seqNat_mulVec_single (ket δ₁) (ket (Function.update δ₁ qEnc 1))
      i₀ (R * 2 ^ k) _
      (fun i hi hlt ↦ by simpa [hz0] using hFix 0 i hi (Nat.ne_of_lt hlt))
      (fun hi₀' ↦ by
        have hbEq : (⟨i₀ / 2 ^ k, div_lt_of_lt_mul_right (Nat.two_pow_pos k) hi₀'⟩ : Fin R) =
          bStar :=
          Fin.ext hdiv₀
        have hpEq : (⟨i₀ % 2 ^ k, Nat.mod_lt i₀ (Nat.two_pow_pos k)⟩ : Fin (2 ^ k)) = pStar :=
          Fin.ext hmod₀
        have htb0 : (i₀ % 2 ^ k).testBit d = true := by rw [hmod₀]; exact htbS
        rw [ite_eq_left htb0]
        simp only [hbEq, hpEq]
        rw [ket_CNOT, hq1, show δ₁ (w bStar pStar) = 1 from Function.update_self _ 1 δ, zero_add])
      (fun i hi hgt ↦ hFix 1 i hi (Nat.ne_of_gt hgt))
    rw [ite_eq_left hi₀] at hSeq; exact hSeq
  · rw [ite_eq_right htbS, show Function.update δ₁ qEnc 0 = δ₁ from
      hq1 ▸ Function.update_eq_self qEnc δ₁]
    refine seqNat_mulVec_fixed (ket δ₁) (R * 2 ^ k) _ fun i hi ↦ ?_
    by_cases he : i = bStar.val * 2 ^ k + pStar.val
    · subst he
      obtain ⟨_, _, hmod₀⟩ := enc_div_mod bStar.isLt pStar.isLt
      have htb0 : ¬ ((bStar.val * 2 ^ k + pStar.val) % 2 ^ k).testBit d = true := by
        rw [hmod₀]; exact htbS
      dsimp only
      rw [ite_eq_right htb0, Circuit.eval_identity, Submonoid.coe_one, Matrix.one_mulVec]
    · have hz0 : Function.update δ₁ qEnc 0 = δ₁ := hq1 ▸ Function.update_eq_self qEnc δ₁
      simpa [hz0] using hFix 0 i hi he
/-- Stride-`2^d` barrel swap across all `R` blocks (`0 T`, `0 TOFF`). -/
def barrelSwap {n : ℕ} (R k : ℕ) (w : Fin R → Fin (2 ^ k) → Wire n)
    (hw : ∀ b₁ p₁ b₂ p₂, w b₁ p₁ = w b₂ p₂ → b₁ = b₂ ∧ p₁ = p₂) (d : ℕ) : Circuit n :=
  seqNat (R * 2 ^ k) fun i hi ↦
    let hB : 0 < 2 ^ k := Nat.two_pow_pos k
    let blk : Fin R := ⟨i / 2 ^ k, div_lt_of_lt_mul_right hB hi⟩
    let p0 := i % 2 ^ k
    let hp0 : p0 < 2 ^ k := Nat.mod_lt i hB
    if hp : p0.testBit d = false ∧ p0 + 2 ^ d < 2 ^ k then
      swap3Cnot (w blk ⟨p0, hp0⟩) (w blk ⟨p0 + 2 ^ d, hp.2⟩)
        (w_ne_of_pair_ne hw (Or.inr fun e ↦ by
          have hv := congrArg Fin.val e; have hpd := Nat.two_pow_pos d; dsimp at hv; omega))
    else .identity
theorem count_barrelSwap {n : ℕ} (R k : ℕ) (w : Fin R → Fin (2 ^ k) → Wire n)
    (hw : ∀ b₁ p₁ b₂ p₂, w b₁ p₁ = w b₂ p₂ → b₁ = b₂ ∧ p₁ = p₂) (d : ℕ) :
    (barrelSwap R k w hw d).count .T = 0 ∧ (barrelSwap R k w hw d).count .TOFF = 0 :=
  ⟨(count_seqNat_T 0 (R * 2 ^ k) _ fun _ _ ↦ by
      dsimp only
      split_ifs
      · exact (count_swap3Cnot _ _ _).1
      · rfl).trans (Nat.mul_zero _),
   count_seqNat_TOFF_zero (R * 2 ^ k) _ fun _ _ ↦ by
      dsimp only
      split_ifs
      · exact (count_swap3Cnot _ _ _).2
      · rfl⟩
theorem barrelSwap_mulVec_ket_pair {n R k : ℕ} (w : Fin R → Fin (2 ^ k) → Wire n)
    (hw : ∀ b₁ p₁ b₂ p₂, w b₁ p₁ = w b₂ p₂ → b₁ = b₂ ∧ p₁ = p₂) (d : ℕ) (δ : BitAssignment n)
    (hw0 : ∀ b p, δ (w b p) = 0) (bStar : Fin R) {pLo : ℕ} (hpLo : pLo < 2 ^ k)
    (htbLo : pLo.testBit d = false) (hpHi : pLo + 2 ^ d < 2 ^ k) (dir : Bool) :
    (barrelSwap R k w hw d).eval.1.mulVec (ket (Function.update δ (w bStar (if dir then ⟨pLo +
    2 ^ d, hpHi⟩ else ⟨pLo, hpLo⟩)) 1)) = ket (Function.update δ (w bStar (if dir then ⟨pLo,
    hpLo⟩ else ⟨pLo + 2 ^ d, hpHi⟩)) 1) := by
  let i₀ := bStar.val * 2 ^ k + pLo
  obtain ⟨hi₀, hdiv₀, hmod₀⟩ := enc_div_mod bStar.isLt hpLo
  have hFix : ∀ (pX : Fin (2 ^ k)), (pX = ⟨pLo, hpLo⟩ ∨ pX = ⟨pLo + 2 ^ d, hpHi⟩) →
      ∀ (i : ℕ) (hi : i < R * 2 ^ k), i ≠ i₀ →
        let hB : 0 < 2 ^ k := Nat.two_pow_pos k
        let blk : Fin R := ⟨i / 2 ^ k, div_lt_of_lt_mul_right hB hi⟩
        let p0 := i % 2 ^ k
        let hp0 : p0 < 2 ^ k := Nat.mod_lt i hB
        (if hp : p0.testBit d = false ∧ p0 + 2 ^ d < 2 ^ k then
          swap3Cnot (w blk ⟨p0, hp0⟩) (w blk ⟨p0 + 2 ^ d, hp.2⟩)
            (w_ne_of_pair_ne hw (Or.inr fun e ↦ by
              have hv := congrArg Fin.val e; have hpd := Nat.two_pow_pos d; dsimp at hv; omega))
        else .identity).eval.1.mulVec (ket (Function.update δ (w bStar pX) 1)) =
          ket (Function.update δ (w bStar pX) 1) := by
    intro pX hpX i hi hne hB blk p0 hp0
    split_ifs with hp
    · have htbHi : (pLo + 2 ^ d).testBit d = true := testBit_add_two_pow_self htbLo
      have htb0Hi : (p0 + 2 ^ d).testBit d = true := testBit_add_two_pow_self hp.1
      have hdisj := enc_ne_iff hne
      have hneA : w blk ⟨p0, hp0⟩ ≠ w bStar pX := w_ne_of_pair_ne hw (by
        rcases hdisj with hdb | hdm
        · exact Or.inl fun e ↦ hdb (congrArg Fin.val e)
        · refine Or.inr fun e ↦ ?_; have hv := congrArg Fin.val e
          rcases hpX with rfl | rfl <;> dsimp at hv
          · exact hdm hv
          · rw [hv] at hp; exact Bool.false_ne_true (hp.1.symm.trans htbHi))
      have hneB : w blk ⟨p0 + 2 ^ d, hp.2⟩ ≠ w bStar pX := w_ne_of_pair_ne hw (by
        rcases hdisj with hdb | hdm
        · exact Or.inl fun e ↦ hdb (congrArg Fin.val e)
        · refine Or.inr fun e ↦ ?_; have hv := congrArg Fin.val e
          rcases hpX with rfl | rfl <;> dsimp at hv
          · rw [hv] at htb0Hi; exact Bool.false_ne_true (htbLo.symm.trans htb0Hi)
          · exact hdm (by omega))
      exact swap3Cnot_mulVec_ket_zero _ _ _ _
        ((Function.update_of_ne hneA _ _).trans (hw0 _ _))
        ((Function.update_of_ne hneB _ _).trans (hw0 _ _))
    · rw [Circuit.eval_identity, Submonoid.coe_one, Matrix.one_mulVec]
  have hpIn : (if dir then (⟨pLo + 2 ^ d, hpHi⟩ : Fin (2 ^ k)) else ⟨pLo, hpLo⟩) = ⟨pLo, hpLo⟩ ∨
      (if dir then (⟨pLo + 2 ^ d, hpHi⟩ : Fin (2 ^ k)) else ⟨pLo, hpLo⟩) = ⟨pLo + 2 ^ d, hpHi⟩ := by
    cases dir <;> simp
  have hpOut : (if dir then (⟨pLo, hpLo⟩ : Fin (2 ^ k)) else ⟨pLo + 2 ^ d, hpHi⟩) = ⟨pLo, hpLo⟩ ∨
      (if dir then (⟨pLo, hpLo⟩ : Fin (2 ^ k)) else ⟨pLo + 2 ^ d, hpHi⟩) = ⟨pLo + 2 ^ d, hpHi⟩ := by
    cases dir <;> simp
  have hSeq := seqNat_mulVec_single
    (ket (Function.update δ (w bStar (if dir then ⟨pLo + 2 ^ d, hpHi⟩ else ⟨pLo, hpLo⟩)) 1))
    (ket (Function.update δ (w bStar (if dir then ⟨pLo, hpLo⟩ else ⟨pLo + 2 ^ d, hpHi⟩)) 1))
    i₀ (R * 2 ^ k) _
    (fun i hi hlt ↦ hFix _ hpIn i hi (Nat.ne_of_lt hlt))
    (fun hi₀' ↦ by
      have hpCond : (i₀ % 2 ^ k).testBit d = false ∧ i₀ % 2 ^ k + 2 ^ d < 2 ^ k := by
        rw [hmod₀]; exact ⟨htbLo, hpHi⟩
      rw [dite_eq_left hpCond]
      have hbEq : (⟨i₀ / 2 ^ k, div_lt_of_lt_mul_right (Nat.two_pow_pos k) hi₀'⟩ : Fin R) = bStar :=
        Fin.ext hdiv₀
      have hp0Eq : (⟨i₀ % 2 ^ k, Nat.mod_lt i₀ (Nat.two_pow_pos k)⟩ : Fin (2 ^ k)) = ⟨pLo, hpLo⟩ :=
        Fin.ext hmod₀
      have hp1Eq : (⟨i₀ % 2 ^ k + 2 ^ d, hpCond.2⟩ : Fin (2 ^ k)) = ⟨pLo + 2 ^ d, hpHi⟩ :=
        Fin.ext (congrArg (· + 2 ^ d) hmod₀)
      simp only [hbEq, hp0Eq, hp1Eq]
      simpa [apply_ite (w bStar)] using swap3Cnot_mulVec_ket_dir _ _ _ δ (hw0 _ _) (hw0 _ _) dir)
    (fun i hi hgt ↦ hFix _ hpOut i hi (Nat.ne_of_gt hgt))
  rw [ite_eq_left hi₀] at hSeq; exact hSeq
/-- Block-position wire injectivity predicate. -/
abbrev WInj {n R k : ℕ} (w : Fin R → Fin (2 ^ k) → Wire n) : Prop :=
  ∀ b₁ p₁ b₂ p₂, w b₁ p₁ = w b₂ p₂ → b₁ = b₂ ∧ p₁ = p₂
/-- Level `d < k` Z-measurement shift step; resets `qEnc` to `|0⟩` on both outcomes (`0 T`). -/
def wShiftLevel {Var : Type} {n : ℕ} (v : Var) (R k : ℕ) (uLo : Fin k → Wire n)
    (w : Fin R → Fin (2 ^ k) → Wire n) (qEnc : Wire n)
    (hw : WInj w) (hwq : ∀ b p, w b p ≠ qEnc) (huq : ∀ d, uLo d ≠ qEnc)
    (d : ℕ) (hd : d < k) : DynamicCircuit Var n :=
  .seq (.circuit (cnotOddToEnc R k w qEnc hwq d ;;ᶜ Circuit.CNOT (uLo ⟨d, hd⟩) qEnc (huq ⟨d, hd⟩)))
    (zResetFixupDyn v qEnc (barrelSwap R k w hw d))
/-- First `m ≤ k` levels of `wShiftLevel`. -/
def wShiftLevels {Var : Type} {n : ℕ} (v : Var) (R k : ℕ) (uLo : Fin k → Wire n)
    (w : Fin R → Fin (2 ^ k) → Wire n) (qEnc : Wire n)
    (hw : WInj w) (hwq : ∀ b p, w b p ≠ qEnc) (huq : ∀ d, uLo d ≠ qEnc) :
    (m : ℕ) → m ≤ k → DynamicCircuit Var n
  | 0, _ => .circuit .identity
  | d + 1, hd =>
      .seq (wShiftLevels v R k uLo w qEnc hw hwq huq d (Nat.le_of_succ_le hd))
        (wShiftLevel v R k uLo w qEnc hw hwq huq d hd)
theorem count_wShiftLevels {Var : Type} {n : ℕ} (v : Var) (R k : ℕ) (uLo : Fin k → Wire n)
    (w : Fin R → Fin (2 ^ k) → Wire n) (qEnc : Wire n)
    (hw : WInj w) (hwq : ∀ b p, w b p ≠ qEnc) (huq : ∀ d, uLo d ≠ qEnc) :
    ∀ (m : ℕ) (hm : m ≤ k),
      (wShiftLevels v R k uLo w qEnc hw hwq huq m hm).count .T = 0 ∧
      (wShiftLevels v R k uLo w qEnc hw hwq huq m hm).count .TOFF = 0
  | 0, _ => ⟨rfl, rfl⟩
  | d + 1, hd => by
      obtain ⟨ht, hf⟩ := count_wShiftLevels v R k uLo w qEnc hw hwq huq d (Nat.le_of_succ_le hd)
      obtain ⟨hto, hfo⟩ := count_cnotOddToEnc R k w qEnc hwq d
      obtain ⟨htb, hfb⟩ := count_barrelSwap R k w hw d
      refine ⟨?_, ?_⟩ <;>
        simp [wShiftLevels, wShiftLevel, DynamicCircuit.count, Circuit.count_seq,
          Circuit.CNOT, ht, hf, hto, hfo, htb, hfb]
theorem subspaceStep_mul_right {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    {R₀ R₁ : Operator (2 ^ n)} (G : Operator (2 ^ n)) {p : DynamicCircuit Var n}
    (h : SubspaceStep R₀ R₁ p) :
    SubspaceStep (R₀ * G) (R₁ * G) p := fun M ↦ by
  obtain ⟨N, hwp, hobs⟩ := h M
  refine ⟨N, hwp, ?_⟩
  calc
    (R₁ * G)ᴴ * M.1.1 * (R₁ * G) = Gᴴ * (R₁ᴴ * M.1.1 * R₁) * G := by
      simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = Gᴴ * (R₀ᴴ * N.1.1 * R₀) * G := by rw [hobs]
    _ = (R₀ * G)ᴴ * N.1.1 * (R₀ * G) := by
      simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
/-- Shifted W-state superposition vector at level `d ≤ k`. -/
def wSuperVec {n R k : ℕ} (bStarFn : BitAssignment n → Fin R) (uLo : Fin k → Wire n)
    (w : Fin R → Fin (2 ^ k) → Wire n) (qEnc : Wire n) (δ : BitAssignment n) (d : ℕ)
    (hd : d ≤ k) : Fin (2 ^ n) → ℂ := if (∀ b p, δ (w b p) = 0) ∧ δ qEnc = 0 then
    (sqrtHalf ^ (k - d)) • ∑ hi : Fin (2 ^ (k - d)), ket (Function.update δ (w (bStarFn δ)
    ⟨idxValPrefix uLo δ d hd + 2 ^ d * hi.val, shift_pos_lt hd (idxValPrefix_lt_two_pow uLo δ
    d hd) hi.isLt⟩) 1) else 0
/-- Operator mapping valid clean `ket δ` to `wSuperVec ... d hd`. -/
def wSuperOp {n R k : ℕ} (bStarFn : BitAssignment n → Fin R) (uLo : Fin k → Wire n)
    (w : Fin R → Fin (2 ^ k) → Wire n) (qEnc : Wire n) (d : ℕ) (hd : d ≤ k) : Operator (2 ^ n)
    := mkVecOp fun δ ↦ wSuperVec bStarFn uLo w qEnc δ d hd
theorem cnotOddAndIdx_mulVec_ket {n R k : ℕ} (uLo : Fin k → Wire n)
    (w : Fin R → Fin (2 ^ k) → Wire n) (qEnc : Wire n)
    (hw : WInj w) (hwq : ∀ b p, w b p ≠ qEnc) (huq : ∀ d, uLo d ≠ qEnc) (huw : ∀ d b p, uLo d ≠ w b
      p)
    (d : ℕ) (hd : d < k) (δ : BitAssignment n) (hw0 : ∀ b p, δ (w b p) = 0) (hq0 : δ qEnc = 0)
    (bStar : Fin R) {hi : ℕ} (hhi : hi < 2 ^ (k - d)) :
    let lo := idxValPrefix uLo δ d (Nat.le_of_lt hd)
    let pS : Fin (2 ^ k) := ⟨lo + 2 ^ d * hi,
      shift_pos_lt (Nat.le_of_lt hd) (idxValPrefix_lt_two_pow uLo δ d (Nat.le_of_lt hd)) hhi⟩
    (cnotOddToEnc R k w qEnc hwq d ;;ᶜ Circuit.CNOT (uLo ⟨d, hd⟩) qEnc (huq ⟨d, hd⟩)).eval.1.mulVec
        (ket (Function.update δ (w bStar pS) 1)) =
      ket (Function.update (Function.update δ (w bStar pS) 1) qEnc
        ((if decide (hi % 2 = 1) then (1 : ZMod 2) else 0) + δ (uLo ⟨d, hd⟩))) := by
  intro lo pS
  have hlo : lo < 2 ^ d := idxValPrefix_lt_two_pow uLo δ d (Nat.le_of_lt hd)
  rw [eval_seq_mulVec, cnotOddToEnc_mulVec_ket w qEnc hw hwq d δ hw0 hq0 bStar pS,
    ket_CNOT, Function.update_self, Function.update_of_ne (huq ⟨d, hd⟩),
    Function.update_of_ne (huw ⟨d, hd⟩ _ _), Function.update_idem]
  dsimp only [pS]; rw [testBit_lo_add_mul_two_pow hlo]
private theorem mul2_lt {k d b : ℕ} (hd : d < k) (hb : b < 2) (q : Fin (2 ^ (k - (d + 1)))) :
    2 * q.val + b < 2 ^ (k - d) := by
  have h : 2 ^ (k - d) = 2 * 2 ^ (k - (d + 1)) := by
    rw [show k - d = k - (d + 1) + 1 by omega, Nat.pow_succ]; ring
  have hq := q.isLt; omega
theorem subspaceStep_wShiftLevel {Var : Type} [Fintype Var] [DecidableEq Var] {n R k : ℕ}
    (v : Var) (bStarFn : BitAssignment n → Fin R) (uLo : Fin k → Wire n)
    (w : Fin R → Fin (2 ^ k) → Wire n) (qEnc : Wire n) (hw : WInj w)
    (hwq : ∀ b p, w b p ≠ qEnc) (huq : ∀ d, uLo d ≠ qEnc) (huw : ∀ d b p, uLo d ≠ w b p)
    (d : ℕ) (hd : d < k) : SubspaceStep (wSuperOp bStarFn uLo w qEnc d (Nat.le_of_lt hd))
    (wSuperOp bStarFn uLo w qEnc (d + 1) hd) (wShiftLevel v R k uLo w qEnc hw hwq huq d hd)
    := by
  let cPre := cnotOddToEnc R k w qEnc hwq d ;;ᶜ Circuit.CNOT (uLo ⟨d, hd⟩) qEnc (huq ⟨d, hd⟩)
  let cB := barrelSwap R k w hw d
  have hev (q : Fin (2 ^ (k - (d + 1)))) : ¬ decide (2 * q.val % 2 = 1) = true := by
    simp only [decide_eq_true_eq]; omega
  have hod (q : Fin (2 ^ (k - (d + 1)))) : decide ((2 * q.val + 1) % 2 = 1) = true := by
    simp only [decide_eq_true_eq]; omega
  have hEv (q : Fin (2 ^ (k - (d + 1)))) : 2 * q.val < 2 ^ (k - d) := by
    simpa using mul2_lt hd (b := 0) (by omega) q
  have hOd (q : Fin (2 ^ (k - (d + 1)))) : 2 * q.val + 1 < 2 ^ (k - d) :=
    mul2_lt hd (by omega) q
  have stepSplit (F : Operator (2 ^ n))
      (hSum : ∀ (δ : BitAssignment n) (hw0 : ∀ b p, δ (w b p) = 0) (hq0 : δ qEnc = 0),
        let lo := idxValPrefix uLo δ d (Nat.le_of_lt hd)
        let hlo : lo < 2 ^ d := idxValPrefix_lt_two_pow uLo δ d (Nat.le_of_lt hd)
        let kIn (hi : ℕ) (hhi : hi < 2 ^ (k - d)) := ket (Function.update δ (w (bStarFn δ) ⟨lo
            + 2 ^ d * hi, shift_pos_lt (Nat.le_of_lt hd) hlo hhi⟩) 1)
        let kOut (q : Fin (2 ^ (k - (d + 1)))) := ket (Function.update δ (w (bStarFn δ)
          ⟨idxValPrefix uLo δ (d + 1) hd + 2 ^ (d + 1) * q.val,
            shift_pos_lt hd (idxValPrefix_lt_two_pow uLo δ (d + 1) hd) q.isLt⟩) 1)
        (∑ q : Fin (2 ^ (k - (d + 1))), F.mulVec (cPre.eval.1.mulVec (kIn (2 * q.val) (hEv q)))) +
          (∑ q : Fin (2 ^ (k - (d + 1))), F.mulVec (cPre.eval.1.mulVec (kIn (2 * q.val +
            1) (hOd q)))) =
          ∑ q : Fin (2 ^ (k - (d + 1))), kOut q) :
      F * (cPre.eval.1 * wSuperOp bStarFn uLo w qEnc d (Nat.le_of_lt hd)) =
        sqrtHalf • wSuperOp bStarFn uLo w qEnc (d + 1) hd := by
    apply matrix_ext_ket; intro δ
    simp only [← Matrix.mulVec_mulVec, Matrix.smul_mulVec, wSuperOp, mkVecOp_mulVec_ket, wSuperVec]
    by_cases hV : (∀ b p, δ (w b p) = 0) ∧ δ qEnc = 0
    · obtain ⟨hw0, hq0⟩ := hV
      rw [ite_eq_left ⟨hw0, hq0⟩, ite_eq_left ⟨hw0, hq0⟩, Matrix.mulVec_smul, Matrix.mulVec_smul,
        Matrix.mulVec_sum, Matrix.mulVec_sum]
      have hkd : k - d = k - (d + 1) + 1 := by omega
      have hpow : sqrtHalf ^ (k - d) = sqrtHalf * sqrtHalf ^ (k - (d + 1)) := by
        rw [hkd, _root_.pow_succ']
      rw [hpow, smul_smul]; congr 1
      let e : Fin (2 ^ (k - (d + 1))) ⊕ Fin (2 ^ (k - (d + 1))) ≃ Fin (2 ^ (k - d)) :=
        (finTwoMulEquiv (2 ^ (k - (d + 1)))).trans (finCongr (by rw [hkd, Nat.pow_succ]; ring))
      rw [← e.sum_comp, Fintype.sum_sum_type]
      exact hSum δ hw0 hq0
    · rw [ite_eq_right hV, ite_eq_right hV, Matrix.mulVec_zero, Matrix.mulVec_zero, smul_zero]
  refine subspaceStep_seq_zResetFixup v qEnc cB (subspaceStep_of_circuit (wSuperOp bStarFn uLo
    w qEnc d (Nat.le_of_lt hd)) cPre)
    (stepSplit ((QRegister.singleton qEnc).basisOutcomeProjector 0) ?_) (stepSplit (cB.eval.1
    * (Circuit.X qEnc).eval.1 * (QRegister.singleton qEnc).basisOutcomeProjector 1) ?_)
  · intro δ hw0 hq0 lo hlo kIn kOut
    let P₀ := (QRegister.singleton qEnc).basisOutcomeProjector 0
    have hPre {hi : ℕ} (hhi : hi < 2 ^ (k - d)) :=
      cnotOddAndIdx_mulVec_ket uLo w qEnc hw hwq huq huw d hd δ hw0 hq0 (bStarFn δ) hhi
    have hqId (p : Fin (2 ^ k)) : Function.update (Function.update δ (w (bStarFn δ) p) 1) qEnc
        0 = Function.update δ (w (bStarFn δ) p) 1 :=
      ((Function.update_of_ne (hwq _ _).symm 1 δ).trans hq0) ▸ Function.update_eq_self qEnc _
    have ketEq {a b : ℕ} {ha : a < 2 ^ k} {hb : b < 2 ^ k} (h : a = b) :
        ket (Function.update δ (w (bStarFn δ) ⟨a, ha⟩) 1) =
          ket (Function.update δ (w (bStarFn δ) ⟨b, hb⟩) 1) :=
      congrArg (fun p ↦ ket (Function.update δ (w (bStarFn δ) p) 1)) (Fin.ext h)
    rcases bit_cases (δ (uLo ⟨d, hd⟩)) with hu0 | hu1
    · have hs1 : (∑ q, P₀.mulVec (cPre.eval.1.mulVec (kIn (2 * q.val) (hEv q)))) = ∑ q, kOut q :=
        Finset.sum_congr rfl fun q _ ↦ by
          dsimp only [P₀]; rw [hPre (hEv q), ite_eq_right (hev q), hu0, add_zero,
            ket_projector_zero, Function.update_self, ite_eq_left rfl, hqId]
          exact ketEq (by dsimp [idxValPrefix, lo]; rw [ite_eq_right (by rw [hu0]; decide)]; ring)
      have hs0 : (∑ q, P₀.mulVec (cPre.eval.1.mulVec (kIn (2 * q.val + 1) (hOd q)))) = 0 :=
        Finset.sum_eq_zero fun q _ ↦ by
          dsimp only [P₀]; rw [hPre (hOd q), ite_eq_left (hod q), hu0, add_zero,
            ket_projector_zero, Function.update_self, ite_eq_right one_ne_zero]
      rw [hs1, hs0, add_zero]
    · have hs0 : (∑ q, P₀.mulVec (cPre.eval.1.mulVec (kIn (2 * q.val) (hEv q)))) = 0 :=
        Finset.sum_eq_zero fun q _ ↦ by
          dsimp only [P₀]; rw [hPre (hEv q), ite_eq_right (hev q), hu1, zero_add,
            ket_projector_zero, Function.update_self, ite_eq_right one_ne_zero]
      have hs1 : (∑ q, P₀.mulVec (cPre.eval.1.mulVec (kIn (2 * q.val + 1) (hOd q)))) = ∑ q,
        kOut q :=
        Finset.sum_congr rfl fun q _ ↦ by
          dsimp only [P₀]; rw [hPre (hOd q), ite_eq_left (hod q), hu1, CharTwo.add_self_eq_zero,
            ket_projector_zero, Function.update_self, ite_eq_left rfl, hqId]
          exact ketEq (by dsimp [idxValPrefix, lo]; rw [ite_eq_left hu1]; ring)
      rw [hs0, hs1, zero_add]
  · intro δ hw0 hq0 lo hlo kIn kOut
    let F₁ := cB.eval.1 * (Circuit.X qEnc).eval.1 *
      (QRegister.singleton qEnc).basisOutcomeProjector 1
    have hPre {hi : ℕ} (hhi : hi < 2 ^ (k - d)) :=
      cnotOddAndIdx_mulVec_ket uLo w qEnc hw hwq huq huw d hd δ hw0 hq0 (bStarFn δ) hhi
    have hqId (p : Fin (2 ^ k)) : Function.update (Function.update δ (w (bStarFn δ) p) 1) qEnc
        0 = Function.update δ (w (bStarFn δ) p) 1 :=
      ((Function.update_of_ne (hwq _ _).symm 1 δ).trans hq0) ▸ Function.update_eq_self qEnc _
    have ketEq {a b : ℕ} {ha : a < 2 ^ k} {hb : b < 2 ^ k} (h : a = b) :
        ket (Function.update δ (w (bStarFn δ) ⟨a, ha⟩) 1) =
          ket (Function.update δ (w (bStarFn δ) ⟨b, hb⟩) 1) :=
      congrArg (fun p ↦ ket (Function.update δ (w (bStarFn δ) p) 1)) (Fin.ext h)
    have hpLo (q : Fin (2 ^ (k - (d + 1)))) : lo + 2 ^ d * (2 * q.val) < 2 ^ k :=
      shift_pos_lt (Nat.le_of_lt hd) hlo (hEv q)
    have htbLo (q : Fin (2 ^ (k - (d + 1)))) : (lo + 2 ^ d * (2 * q.val)).testBit d = false := by
      rw [testBit_lo_add_mul_two_pow hlo]; simp only [decide_eq_false_iff_not]; omega
    have hpHi (q : Fin (2 ^ (k - (d + 1)))) : (lo + 2 ^ d * (2 * q.val)) + 2 ^ d < 2 ^ k := by
      have heq : (lo + 2 ^ d * (2 * q.val)) + 2 ^ d = lo + 2 ^ d * (2 * q.val + 1) := by ring
      rw [heq]; exact shift_pos_lt (Nat.le_of_lt hd) hlo (hOd q)
    rcases bit_cases (δ (uLo ⟨d, hd⟩)) with hu0 | hu1
    · have hs0 : (∑ q, F₁.mulVec (cPre.eval.1.mulVec (kIn (2 * q.val) (hEv q)))) = 0 :=
        Finset.sum_eq_zero fun q _ ↦ by
          dsimp only [F₁]; rw [← Matrix.mulVec_mulVec, hPre (hEv q), ite_eq_right (hev q),
            hu0, add_zero, ket_projector_one, Function.update_self, ite_eq_right zero_ne_one,
            Matrix.mulVec_zero]
      have hs1 : (∑ q, F₁.mulVec (cPre.eval.1.mulVec (kIn (2 * q.val + 1) (hOd q)))) = ∑ q,
        kOut q :=
        Finset.sum_congr rfl fun q _ ↦ by
          dsimp only [F₁]; rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
            hPre (hOd q), ite_eq_left (hod q), hu0, add_zero, ket_projector_one,
            Function.update_self, ite_eq_left rfl, ket_X, Function.update_self,
            CharTwo.add_self_eq_zero, Function.update_idem, hqId]
          have hFin1 : (⟨lo + 2 ^ d * (2 * q.val + 1), shift_pos_lt (Nat.le_of_lt hd) hlo (hOd q)⟩ :
              Fin (2 ^ k)) =
              if true then ⟨(lo + 2 ^ d * (2 * q.val)) + 2 ^ d, hpHi q⟩ else ⟨lo + 2 ^ d * (2 *
                q.val), hpLo q⟩ :=
            Fin.ext (by dsimp; ring)
          rw [hFin1, barrelSwap_mulVec_ket_pair w hw d δ hw0 (bStarFn δ) (hpLo q) (htbLo q) (hpHi q)
            true]
          exact ketEq (by dsimp [idxValPrefix, lo]; rw [ite_eq_right (by rw [hu0]; decide)]; ring)
      rw [hs0, hs1, zero_add]
    · have hs1 : (∑ q, F₁.mulVec (cPre.eval.1.mulVec (kIn (2 * q.val) (hEv q)))) = ∑ q, kOut q :=
        Finset.sum_congr rfl fun q _ ↦ by
          dsimp only [F₁]; rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
            hPre (hEv q), ite_eq_right (hev q), hu1, zero_add, ket_projector_one,
            Function.update_self, ite_eq_left rfl, ket_X, Function.update_self,
            CharTwo.add_self_eq_zero, Function.update_idem, hqId]
          have hFin0 : (⟨lo + 2 ^ d * (2 * q.val), hpLo q⟩ : Fin (2 ^ k)) =
              if false then ⟨(lo + 2 ^ d * (2 * q.val)) + 2 ^ d, hpHi q⟩ else ⟨lo + 2 ^ d * (2 *
                q.val), hpLo q⟩ := rfl
          rw [hFin0, barrelSwap_mulVec_ket_pair w hw d δ hw0 (bStarFn δ) (hpLo q) (htbLo q) (hpHi q)
            false]
          exact ketEq (by dsimp [idxValPrefix, lo]; rw [ite_eq_left hu1]; ring)
      have hs0 : (∑ q, F₁.mulVec (cPre.eval.1.mulVec (kIn (2 * q.val + 1) (hOd q)))) = 0 :=
        Finset.sum_eq_zero fun q _ ↦ by
          dsimp only [F₁]; rw [← Matrix.mulVec_mulVec, hPre (hOd q), ite_eq_left (hod q),
            hu1, CharTwo.add_self_eq_zero, ket_projector_one, Function.update_self,
            ite_eq_right zero_ne_one, Matrix.mulVec_zero]
      rw [hs1, hs0, add_zero]
theorem subspaceStep_wShiftLevels {Var : Type} [Fintype Var] [DecidableEq Var] {n R k : ℕ}
    (v : Var) (bStarFn : BitAssignment n → Fin R) (uLo : Fin k → Wire n)
    (w : Fin R → Fin (2 ^ k) → Wire n) (qEnc : Wire n)
    (hw : WInj w) (hwq : ∀ b p, w b p ≠ qEnc) (huq : ∀ d, uLo d ≠ qEnc) (huw : ∀ d b p, uLo d ≠ w b
      p) :
    ∀ (m : ℕ) (hm : m ≤ k),
      SubspaceStep (wSuperOp bStarFn uLo w qEnc 0 (Nat.zero_le k))
        (wSuperOp bStarFn uLo w qEnc m hm)
        (wShiftLevels v R k uLo w qEnc hw hwq huq m hm)
  | 0, _ => by
      simpa only [wShiftLevels, Circuit.eval_identity, Submonoid.coe_one, Matrix.one_mul] using
        subspaceStep_of_circuit (Var := Var)
          (wSuperOp bStarFn uLo w qEnc 0 (Nat.zero_le k)) (.identity : Circuit n)
  | d + 1, hd =>
      (subspaceStep_wShiftLevels v bStarFn uLo w qEnc hw hwq huq huw d (Nat.le_of_succ_le hd)).seq
        (subspaceStep_wShiftLevel v bStarFn uLo w qEnc hw hwq huq huw d hd)
attribute [local semireducible] projBit_dqmu
private theorem eval_X_mul_self_loc {n : ℕ} (q : Wire n) :
    (Circuit.X q).eval.1 * (Circuit.X q).eval.1 = 1 := by
  apply matrix_ext_ket; intro δ
  rw [← Matrix.mulVec_mulVec, ket_X, ket_X, Function.update_idem, Function.update_self,
    add_assoc, CharTwo.add_self_eq_zero, add_zero, Function.update_eq_self, Matrix.one_mulVec]
theorem mulVec_X_invol {n : ℕ} (q : Wire n) (v : Fin (2 ^ n) → ℂ) :
    (Circuit.X q).eval.1.mulVec ((Circuit.X q).eval.1.mulVec v) = v := by
  rw [Matrix.mulVec_mulVec, eval_X_mul_self_loc, Matrix.one_mulVec]
private theorem eval_CNOT_mul_self_loc {n : ℕ} (c t : Wire n) (h : c ≠ t) :
    (Circuit.CNOT c t h).eval.1 * (Circuit.CNOT c t h).eval.1 = 1 := by
  apply matrix_ext_ket; intro δ
  rw [← Matrix.mulVec_mulVec, ket_CNOT, ket_CNOT, Function.update_idem, Function.update_self,
    Function.update_of_ne h, add_assoc, CharTwo.add_self_eq_zero, add_zero,
    Function.update_eq_self, Matrix.one_mulVec]
theorem mulVec_CNOT_invol {n : ℕ} (c t : Wire n) (h : c ≠ t) (v : Fin (2 ^ n) → ℂ) :
    (Circuit.CNOT c t h).eval.1.mulVec ((Circuit.CNOT c t h).eval.1.mulVec v) = v := by
  rw [Matrix.mulVec_mulVec, eval_CNOT_mul_self_loc, Matrix.one_mulVec]
theorem ket_CNOT_of_ctrl_zero {n : ℕ} {c t : Wire n} (h : c ≠ t) {β : BitAssignment n}
    (hc : β c = 0) : (Circuit.CNOT c t h).eval.1.mulVec (ket β) = ket β := by
  rw [ket_CNOT, hc, add_zero, Function.update_eq_self]
theorem projBit_zero_mulVec_ket {n : ℕ} (q : Wire n) (δ : BitAssignment n) :
    (projBit_dqmu q 0).mulVec (ket δ) = if δ q = 0 then ket δ else 0 := ket_projector_zero q δ
/-- Decidable disjointness proposition equivalent to `WRouterDisj`. -/
def WRouterDisjProp {D N n : ℕ} (wHas : Wire n) (wIdx : Fin D → Wire n)
    (wOut : Fin N → Wire n) (qEnc : Wire n) : Prop := (∀ j, wHas ≠ wOut j) ∧ wHas ≠ qEnc ∧
    (∀ d j, wIdx d ≠ wOut j) ∧ (∀ d, wIdx d ≠ qEnc) ∧ (∀ i j, i ≠ j → wOut i ≠ wOut j) ∧
    (∀ j, wOut j ≠ qEnc)
instance instDecidableWRouterDisjProp {D N n : ℕ} (wHas : Wire n) (wIdx : Fin D → Wire n)
    (wOut : Fin N → Wire n) (qEnc : Wire n) :
    Decidable (WRouterDisjProp wHas wIdx wOut qEnc) := by
  unfold WRouterDisjProp; infer_instance
/-- Output-only disjointness proposition for `0-T` MBU uncomputation (independent of `qEnc`). -/
def WRouterOutDisj {D N n : ℕ} (wHas : Wire n) (wIdx : Fin D → Wire n)
    (wOut : Fin N → Wire n) : Prop :=
  (∀ j, wHas ≠ wOut j) ∧ (∀ d j, wIdx d ≠ wOut j) ∧ (∀ i j, i ≠ j → wOut i ≠ wOut j)
instance instDecidableWRouterOutDisj {D N n : ℕ} (wHas : Wire n) (wIdx : Fin D → Wire n)
    (wOut : Fin N → Wire n) : Decidable (WRouterOutDisj wHas wIdx wOut) := by
  unfold WRouterOutDisj; infer_instance
theorem WRouterDisj.disjProp {D N n : ℕ} {wHas : Wire n} {wIdx : Fin D → Wire n}
    {wOut : Fin N → Wire n} {qEnc : Wire n} (hd : WRouterDisj wHas wIdx wOut qEnc) :
    WRouterDisjProp wHas wIdx wOut qEnc :=
  ⟨hd.has_ne_out, hd.has_ne_q, hd.idx_ne_out, hd.idx_ne_q, hd.out_inj, hd.out_ne_q⟩
theorem blockIdx_lt {R k N : ℕ} (hRN : R * 2 ^ k = N) (b : Fin R) (p : Fin (2 ^ k)) :
    b.val * 2 ^ k + p.val < N := by
  rw [← hRN]; exact (enc_div_mod b.isLt p.isLt).1
/-- Reshape `wOut : Fin N → Wire n` (`R * 2^k = N`) into `R` blocks of `2^k` wires. -/
abbrev blockWires {R k N n : ℕ} (hRN : R * 2 ^ k = N) (wOut : Fin N → Wire n) (b : Fin R)
    (p : Fin (2 ^ k)) : Wire n := wOut ⟨b.val * 2 ^ k + p.val, blockIdx_lt hRN b p⟩
theorem wInj_blockWires {R k N n : ℕ} (hRN : R * 2 ^ k = N) {wOut : Fin N → Wire n}
    (hInj : ∀ i j, i ≠ j → wOut i ≠ wOut j) :
    WInj (blockWires hRN wOut) := fun b₁ p₁ b₂ p₂ heq ↦ by
  have hFin : (⟨b₁.val * 2 ^ k + p₁.val, blockIdx_lt hRN b₁ p₁⟩ : Fin N) =
      ⟨b₂.val * 2 ^ k + p₂.val, blockIdx_lt hRN b₂ p₂⟩ :=
    Decidable.byContradiction fun hne ↦ hInj _ _ hne heq
  have hv : b₁.val * 2 ^ k + p₁.val = b₂.val * 2 ^ k + p₂.val := congrArg Fin.val hFin
  obtain ⟨_, hd₁, hm₁⟩ := enc_div_mod b₁.isLt p₁.isLt
  obtain ⟨_, hd₂, hm₂⟩ := enc_div_mod b₂.isLt p₂.isLt
  exact ⟨Fin.ext (by rw [← hd₁, hv, hd₂]), Fin.ext (by rw [← hm₁, hv, hm₂])⟩
/-- Prefix slice of the lower `k ≤ D` index wires. -/
abbrev uLoOf {k D n : ℕ} (hk : k ≤ D) (wIdx : Fin D → Wire n) (d : Fin k) : Wire n :=
  wIdx ⟨d.val, Nat.lt_of_lt_of_le d.isLt hk⟩
theorem idxValPrefix_uLoOf {k D n : ℕ} (hk : k ≤ D) (wIdx : Fin D → Wire n) (δ : BitAssignment n) :
    ∀ (m : ℕ) (hm : m ≤ k),
      idxValPrefix (uLoOf hk wIdx) δ m hm = idxValPrefix wIdx δ m (Nat.le_trans hm hk)
  | 0, _ => rfl
  | m + 1, hm => by
      dsimp only [idxValPrefix, uLoOf]
      rw [idxValPrefix_uLoOf hk wIdx δ m (Nat.le_of_succ_le hm)]
/- Section 2: Zero-gating and `0-T` MBU reverse CH-tree uncomputation -/
private theorem wSuperVec_bot {n R k : ℕ} (bStarFn : BitAssignment n → Fin R)
    (uLo : Fin k → Wire n) (w : Fin R → Fin (2 ^ k) → Wire n) (hw : WInj w)
    (qEnc : Wire n) (δ : BitAssignment n) (hw0 : ∀ b p, δ (w b p) = 0) (hq0 : δ qEnc = 0) :
    (wTreePrefix R k w hw k le_rfl).eval.1.mulVec
        (ket (Function.update δ (w (bStarFn δ) ⟨0, Nat.two_pow_pos k⟩) 1)) =
      wSuperVec bStarFn uLo w qEnc δ 0 (Nat.zero_le k) := by
  rw [wTreePrefix_mulVec_ket w hw δ hw0 (bStarFn δ) k le_rfl]
  dsimp only [wSuperVec]
  rw [ite_eq_left ⟨hw0, hq0⟩]
  have hk0 : k - 0 = k := Nat.sub_zero k
  let e : Fin (2 ^ k) ≃ Fin (2 ^ (k - 0)) := finCongr (by rw [hk0])
  rw [← e.sum_comp]
  simp only [hk0]
  congr 1
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  exact congrArg (fun p ↦ ket (Function.update δ (w (bStarFn δ) p) 1))
    (Fin.ext (by dsimp [e, idxValPrefix]; omega))
private theorem wSuperVec_top {n R k : ℕ} (bStarFn : BitAssignment n → Fin R)
    (uLo : Fin k → Wire n) (w : Fin R → Fin (2 ^ k) → Wire n) (qEnc : Wire n)
    (δ : BitAssignment n) (hw0 : ∀ b p, δ (w b p) = 0) (hq0 : δ qEnc = 0) : wSuperVec bStarFn
    uLo w qEnc δ k le_rfl = ket (Function.update δ (w (bStarFn δ) ⟨idxValPrefix uLo δ k
    le_rfl, idxValPrefix_lt_two_pow uLo δ k le_rfl⟩) 1) := by
  dsimp only [wSuperVec]
  rw [ite_eq_left ⟨hw0, hq0⟩, show sqrtHalf ^ (k - k) = 1 by rw [Nat.sub_self, _root_.pow_zero],
    one_smul]
  rw [Finset.sum_eq_single ⟨0, Nat.two_pow_pos (k - k)⟩]
  · exact congrArg (fun p ↦ ket (Function.update δ (w (bStarFn δ) p) 1))
      (Fin.ext (by dsimp))
  · intro hi _ hne; exfalso; apply hne; apply Fin.ext
    have hv : hi.val < 2 ^ (k - k) := hi.isLt
    have hp : 2 ^ (k - k) = 1 := by simp
    dsimp; omega
  · intro habs; exact (habs (Finset.mem_univ _)).elim
/-- Lower partner wire in reverse CH-tree round `r < k` at flat index `i < R * 2^r`. -/
def qLo {n : ℕ} (R k : ℕ) (w : Fin R → Fin (2 ^ k) → Wire n)
    (r : ℕ) (hr : r < k) (i : ℕ) (hi : i < R * 2 ^ r) : Wire n :=
  w ⟨i / 2 ^ r, div_lt_of_lt_mul_right (Nat.two_pow_pos r) hi⟩
    ⟨i % 2 ^ r, pair_lo_lt hr (Nat.mod_lt i (Nat.two_pow_pos r))⟩
/-- Upper partner wire in reverse CH-tree round `r < k` at flat index `i < R * 2^r`. -/
def qUp {n : ℕ} (R k : ℕ) (w : Fin R → Fin (2 ^ k) → Wire n)
    (r : ℕ) (hr : r < k) (i : ℕ) (hi : i < R * 2 ^ r) : Wire n :=
  w ⟨i / 2 ^ r, div_lt_of_lt_mul_right (Nat.two_pow_pos r) hi⟩
    ⟨i % 2 ^ r + 2 ^ r, pair_hi_lt hr (Nat.mod_lt i (Nat.two_pow_pos r))⟩
theorem qLo_ne_qUp {n R k : ℕ} {w : Fin R → Fin (2 ^ k) → Wire n} (hw : WInj w)
    {r : ℕ} (hr : r < k) {i₁ i₂ : ℕ} (hi₁ : i₁ < R * 2 ^ r) (hi₂ : i₂ < R * 2 ^ r) :
    qLo R k w r hr i₁ hi₁ ≠ qUp R k w r hr i₂ hi₂ :=
  w_ne_of_pair_ne hw (Or.inr fun e ↦ by
    have hv := congrArg Fin.val e
    have hm₁ := Nat.mod_lt i₁ (Nat.two_pow_pos r)
    dsimp at hv; omega)
private theorem qUp_ne_of_ne {n R k : ℕ} {w : Fin R → Fin (2 ^ k) → Wire n} (hw : WInj w)
    {r : ℕ} (hr : r < k) {i₁ i₂ : ℕ} (hi₁ : i₁ < R * 2 ^ r) (hi₂ : i₂ < R * 2 ^ r)
    (hne : i₁ ≠ i₂) : qUp R k w r hr i₁ hi₁ ≠ qUp R k w r hr i₂ hi₂ := fun e ↦ by
  obtain ⟨hb, hp⟩ := hw _ _ _ _ e
  have hdiv : i₁ / 2 ^ r = i₂ / 2 ^ r := congrArg Fin.val hb
  have hmod : i₁ % 2 ^ r + 2 ^ r = i₂ % 2 ^ r + 2 ^ r := congrArg Fin.val hp
  have hmod' : i₁ % 2 ^ r = i₂ % 2 ^ r := by omega
  have hd₁ := Nat.div_add_mod i₁ (2 ^ r)
  have hd₂ := Nat.div_add_mod i₂ (2 ^ r)
  rw [hdiv, hmod'] at hd₁
  exact hne (hd₁.symm.trans hd₂)
/-- Single-pair CZ target list `[(qLo, uLo r)]` for X-measurement uncomputation of `qUp`. -/
def pairOf {n : ℕ} (R k : ℕ) (uLo : Fin k → Wire n) (w : Fin R → Fin (2 ^ k) → Wire n)
    (huw : ∀ d b p, uLo d ≠ w b p) (r : ℕ) (hr : r < k) (i : ℕ) (hi : i < R * 2 ^ r) : List
    (WirePair n) := [⟨qLo R k w r hr i hi, ⟨uLo ⟨r, hr⟩, (huw ⟨r, hr⟩ _ _).symm⟩⟩]
private def fPair {n : ℕ} (R k : ℕ) (uLo : Fin k → Wire n) (w : Fin R → Fin (2 ^ k) → Wire n)
    (huw : ∀ d b p, uLo d ≠ w b p) (r : ℕ) (hr : r < k) (i : ℕ) (hi : i < R * 2 ^ r)
    (β : BitAssignment n) : ZMod 2 := czPairsParity (pairOf R k uLo w huw r hr i hi) β
private theorem fPair_indep {n : ℕ} (R k : ℕ) (uLo : Fin k → Wire n)
    (w : Fin R → Fin (2 ^ k) → Wire n) (hw : WInj w) (huw : ∀ d b p, uLo d ≠ w b p)
    (r : ℕ) (hr : r < k) (i : ℕ) (hi : i < R * 2 ^ r) (β : BitAssignment n) (a : ZMod 2) :
    fPair R k uLo w huw r hr i hi (Function.update β (qUp R k w r hr i hi) a) =
      fPair R k uLo w huw r hr i hi β := by
  have huw' : uLo ⟨r, hr⟩ ≠ qUp R k w r hr i hi := huw ⟨r, hr⟩ _ _
  dsimp only [fPair, pairOf, czPairsParity]
  rw [Function.update_of_ne (qLo_ne_qUp hw hr hi hi), Function.update_of_ne huw']
/-- Reverse CNOT gather round `r < k` folding `qUp` into `qLo` across all `R * 2^r` pairs. -/
def wUncompCnotRound {n : ℕ} (R k : ℕ) (w : Fin R → Fin (2 ^ k) → Wire n) (hw : WInj w)
    (r : ℕ) (hr : r < k) : Circuit n := seqNat (R * 2 ^ r) fun i hi ↦ Circuit.CNOT
    (qUp R k w r hr i hi) (qLo R k w r hr i hi) (qLo_ne_qUp hw hr hi hi).symm
private def upperXorBits {n : ℕ} (R k : ℕ) (uLo : Fin k → Wire n)
    (w : Fin R → Fin (2 ^ k) → Wire n) (huw : ∀ d b p, uLo d ≠ w b p)
    (r : ℕ) (hr : r < k) : (m : ℕ) → m ≤ R * 2 ^ r → BitAssignment n → BitAssignment n
  | 0, _, β => β
  | m + 1, hm, β =>
      let β' := upperXorBits R k uLo w huw r hr m (Nat.le_of_succ_le hm) β
      Function.update β' (qUp R k w r hr m hm)
        (β' (qUp R k w r hr m hm) + fPair R k uLo w huw r hr m hm β')
private theorem upperXorBits_of_ne {n : ℕ} (R k : ℕ) (uLo : Fin k → Wire n)
    (w : Fin R → Fin (2 ^ k) → Wire n) (huw : ∀ d b p, uLo d ≠ w b p)
    (r : ℕ) (hr : r < k) (β : BitAssignment n) (u : Wire n) :
    ∀ (m : ℕ) (hm : m ≤ R * 2 ^ r),
      (∀ i (hi : i < m), u ≠ qUp R k w r hr i (Nat.lt_of_lt_of_le hi hm)) →
      upperXorBits R k uLo w huw r hr m hm β u = β u
  | 0, _, _ => rfl
  | m + 1, hm, hne => by
      dsimp only [upperXorBits]
      rw [Function.update_of_ne (hne m (Nat.lt_succ_self m)),
        upperXorBits_of_ne R k uLo w huw r hr β u m (Nat.le_of_succ_le hm)
          (fun i hi ↦ hne i (Nat.lt_succ_of_lt hi))]
private theorem upperXorBits_qUp_lt {n : ℕ} (R k : ℕ) (uLo : Fin k → Wire n)
    (w : Fin R → Fin (2 ^ k) → Wire n) (hw : WInj w) (huw : ∀ d b p, uLo d ≠ w b p)
    (r : ℕ) (hr : r < k) (β : BitAssignment n) :
    ∀ (m : ℕ) (hm : m ≤ R * 2 ^ r) (i : ℕ) (hi : i < m),
      let hiR := Nat.lt_of_lt_of_le hi hm
      upperXorBits R k uLo w huw r hr m hm β (qUp R k w r hr i hiR) =
        β (qUp R k w r hr i hiR) + β (qLo R k w r hr i hiR) * β (uLo ⟨r, hr⟩)
  | 0, _, _, hi => absurd hi (Nat.not_lt_zero _)
  | m + 1, hm, i, hi => by
      dsimp only [upperXorBits]
      by_cases him : i = m
      · subst him
        rw [Function.update_self]
        have hUp := upperXorBits_of_ne R k uLo w huw r hr β (qUp R k w r hr i hm) i
          (Nat.le_of_succ_le hm) (fun j hj ↦ qUp_ne_of_ne hw hr hm _ (Nat.ne_of_gt hj))
        have hLo := upperXorBits_of_ne R k uLo w huw r hr β (qLo R k w r hr i hm) i
          (Nat.le_of_succ_le hm) (fun j _ ↦ qLo_ne_qUp hw hr hm _)
        have hIdx := upperXorBits_of_ne R k uLo w huw r hr β (uLo ⟨r, hr⟩) i
          (Nat.le_of_succ_le hm) (fun _ _ ↦ huw ⟨r, hr⟩ _ _)
        dsimp only [fPair, pairOf, czPairsParity]
        rw [hUp, hLo, hIdx, add_zero]
      · have hilt : i < m := by omega
        rw [Function.update_of_ne (qUp_ne_of_ne hw hr _ hm him),
          upperXorBits_qUp_lt R k uLo w hw huw r hr β m (Nat.le_of_succ_le hm) i hilt]
private def uUpperXorPrefix {n : ℕ} (R k : ℕ) (uLo : Fin k → Wire n)
    (w : Fin R → Fin (2 ^ k) → Wire n) (hw : WInj w) (huw : ∀ d b p, uLo d ≠ w b p)
    (r : ℕ) (hr : r < k) : (m : ℕ) → m ≤ R * 2 ^ r → Operator (2 ^ n)
  | 0, _ => 1
  | m + 1, hm =>
      (xorWireUnitary (qUp R k w r hr m hm) (fPair R k uLo w huw r hr m hm)
        (fPair_indep R k uLo w hw huw r hr m hm)).1 *
      uUpperXorPrefix R k uLo w hw huw r hr m (Nat.le_of_succ_le hm)
private theorem uUpperXorPrefix_mulVec_ket {n : ℕ} (R k : ℕ) (uLo : Fin k → Wire n)
    (w : Fin R → Fin (2 ^ k) → Wire n) (hw : WInj w) (huw : ∀ d b p, uLo d ≠ w b p)
    (r : ℕ) (hr : r < k) (β : BitAssignment n) :
    ∀ (m : ℕ) (hm : m ≤ R * 2 ^ r),
      (uUpperXorPrefix R k uLo w hw huw r hr m hm).mulVec (ket β) =
        ket (upperXorBits R k uLo w huw r hr m hm β)
  | 0, _ => Matrix.one_mulVec _
  | m + 1, hm => by
      rw [uUpperXorPrefix, ← Matrix.mulVec_mulVec,
        uUpperXorPrefix_mulVec_ket R k uLo w hw huw r hr β m (Nat.le_of_succ_le hm),
        xorWireUnitary_mulVec_ket]
      rfl
/-- Sequential `0-T` X-measurement + conditional CZ unloader for the `m` upper wires of round
`r`. -/
def wUncompMeasPrefix {Var : Type} {n : ℕ} (v : Var) (R k : ℕ) (uLo : Fin k → Wire n)
    (w : Fin R → Fin (2 ^ k) → Wire n) (huw : ∀ d b p, uLo d ≠ w b p)
    (r : ℕ) (hr : r < k) (rest : DynamicCircuit Var n) :
    (m : ℕ) → m ≤ R * 2 ^ r → DynamicCircuit Var n
  | 0, _ => rest
  | m + 1, hm =>
      xUnloadCzPairsSeqDyn v (qUp R k w r hr m hm) (pairOf R k uLo w huw r hr m hm)
        (wUncompMeasPrefix v R k uLo w huw r hr rest m (Nat.le_of_succ_le hm))
private theorem count_wUncompMeasPrefix {Var : Type} {n : ℕ} (v : Var) (R k : ℕ)
    (uLo : Fin k → Wire n) (w : Fin R → Fin (2 ^ k) → Wire n) (huw : ∀ d b p, uLo d ≠ w b p)
    (r : ℕ) (hr : r < k) (rest : DynamicCircuit Var n) :
    ∀ (m : ℕ) (hm : m ≤ R * 2 ^ r),
      (wUncompMeasPrefix v R k uLo w huw r hr rest m hm).count .T = rest.count .T ∧
      (wUncompMeasPrefix v R k uLo w huw r hr rest m hm).count .TOFF = rest.count .TOFF
  | 0, _ => ⟨rfl, rfl⟩
  | m + 1, hm => by
      obtain ⟨ht, hf⟩ := count_wUncompMeasPrefix v R k uLo w huw r hr rest m (Nat.le_of_succ_le hm)
      obtain ⟨xt, xf⟩ := count_xUnloadCzPairsSeqDyn v (qUp R k w r hr m hm)
        (pairOf R k uLo w huw r hr m hm)
        (wUncompMeasPrefix v R k uLo w huw r hr rest m (Nat.le_of_succ_le hm))
      dsimp only [wUncompMeasPrefix]
      exact ⟨xt.trans ht, xf.trans hf⟩
/-- Pre-shift one-hot vector at tree level `m ≤ k` on kets satisfying `P δ ∧ ∀ b p, δ (w b p) =
0`. -/
def oneHotPreVec {n R k : ℕ} (P : BitAssignment n → Prop) [DecidablePred P]
    (bStarFn : BitAssignment n → Fin R) (uLo : Fin k → Wire n)
    (w : Fin R → Fin (2 ^ k) → Wire n) (δ : BitAssignment n) (m : ℕ) (hm : m ≤ k) : Fin
    (2 ^ n) → ℂ := if P δ ∧ ∀ b p, δ (w b p) = 0 then ket (Function.update δ (w (bStarFn δ)
    ⟨idxValPrefix uLo δ m hm, Nat.lt_of_lt_of_le (idxValPrefix_lt_two_pow uLo δ m hm)
    (Nat.pow_le_pow_right (by omega) hm)⟩) 1) else 0
/-- Operator mapping computational basis kets via `oneHotPreVec`. -/
def oneHotPreOp {n R k : ℕ} (P : BitAssignment n → Prop) [DecidablePred P]
    (bStarFn : BitAssignment n → Fin R) (uLo : Fin k → Wire n)
    (w : Fin R → Fin (2 ^ k) → Wire n) (m : ℕ) (hm : m ≤ k) : Operator (2 ^ n) :=
  mkVecOp fun δ ↦ oneHotPreVec P bStarFn uLo w δ m hm
private theorem oneHotPreOp_mulVec_ket {n R k : ℕ} (P : BitAssignment n → Prop) [DecidablePred P]
    (bStarFn : BitAssignment n → Fin R) (uLo : Fin k → Wire n)
    (w : Fin R → Fin (2 ^ k) → Wire n) (m : ℕ) (hm : m ≤ k) (δ : BitAssignment n) :
    (oneHotPreOp P bStarFn uLo w m hm).mulVec (ket δ) = oneHotPreVec P bStarFn uLo w δ m hm :=
  mkVecOp_mulVec_ket _ δ
attribute [local irreducible] oneHotPreOp
private theorem projBit_zero_uUpperXorPrefix_oneHotPreOp {n R k : ℕ}
    (P : BitAssignment n → Prop) [DecidablePred P] (bStarFn : BitAssignment n → Fin R)
    (uLo : Fin k → Wire n) (w : Fin R → Fin (2 ^ k) → Wire n) (hw : WInj w)
    (huw : ∀ d b p, uLo d ≠ w b p) (r : ℕ) (hr : r < k) (m : ℕ) (hm : m < R * 2 ^ r) :
    projBit_dqmu (qUp R k w r hr m hm) 0 * (uUpperXorPrefix R k uLo w hw huw r hr m
    (Nat.le_of_succ_le hm) * oneHotPreOp P bStarFn uLo w r (Nat.le_of_lt hr)) =
    uUpperXorPrefix R k uLo w hw huw r hr m (Nat.le_of_succ_le hm) * oneHotPreOp P bStarFn uLo
    w r (Nat.le_of_lt hr) := by
  apply matrix_ext_ket; intro δ
  simp only [← Matrix.mulVec_mulVec, oneHotPreOp_mulVec_ket, oneHotPreVec]
  by_cases hV : P δ ∧ ∀ b p, δ (w b p) = 0
  · rw [ite_eq_left hV, uUpperXorPrefix_mulVec_ket, projBit_zero_mulVec_ket]
    let pLo : Fin (2 ^ k) := ⟨idxValPrefix uLo δ r (Nat.le_of_lt hr),
      Nat.lt_of_lt_of_le (idxValPrefix_lt_two_pow uLo δ r (Nat.le_of_lt hr))
        (Nat.pow_le_pow_right (by omega) (Nat.le_of_lt hr))⟩
    have hneLo : w (bStarFn δ) pLo ≠ qUp R k w r hr m hm :=
      w_ne_of_pair_ne hw (Or.inr fun e ↦ by
        have hv := congrArg Fin.val e
        have hs := idxValPrefix_lt_two_pow uLo δ r (Nat.le_of_lt hr)
        dsimp [pLo, qUp] at hv; omega)
    have hq0 : upperXorBits R k uLo w huw r hr m (Nat.le_of_succ_le hm)
        (Function.update δ (w (bStarFn δ) pLo) 1) (qUp R k w r hr m hm) = 0 := by
      rw [upperXorBits_of_ne R k uLo w huw r hr _ _ m (Nat.le_of_succ_le hm)
        (fun i hi ↦ qUp_ne_of_ne hw hr hm _ (Nat.ne_of_gt hi)),
        Function.update_of_ne hneLo.symm]
      exact hV.2 _ _
    rw [ite_eq_left hq0]
  · rw [ite_eq_right hV, Matrix.mulVec_zero, Matrix.mulVec_zero]
private theorem subspaceStep_wUncompMeasPrefix {Var : Type} [Fintype Var] [DecidableEq Var]
    {n R k : ℕ} (v : Var) (P : BitAssignment n → Prop) [DecidablePred P]
    (bStarFn : BitAssignment n → Fin R) (uLo : Fin k → Wire n)
    (w : Fin R → Fin (2 ^ k) → Wire n) (hw : WInj w) (huw : ∀ d b p, uLo d ≠ w b p)
    (r : ℕ) (hr : r < k) {rest : DynamicCircuit Var n} {R_out : Operator (2 ^ n)}
    (hRest : SubspaceStep (oneHotPreOp P bStarFn uLo w r (Nat.le_of_lt hr)) R_out rest) :
    ∀ (m : ℕ) (hm : m ≤ R * 2 ^ r),
      SubspaceStep
        (uUpperXorPrefix R k uLo w hw huw r hr m hm *
          oneHotPreOp P bStarFn uLo w r (Nat.le_of_lt hr))
        R_out
        (wUncompMeasPrefix v R k uLo w huw r hr rest m hm)
  | 0, _ => by simpa only [uUpperXorPrefix, Matrix.one_mul, wUncompMeasPrefix] using hRest
  | m + 1, hm => by
      dsimp only [uUpperXorPrefix, wUncompMeasPrefix]
      rw [Matrix.mul_assoc]
      exact subspaceStep_xUnloadCzPairsSeqDyn v (qUp R k w r hr m hm)
        (pairOf R k uLo w huw r hr m hm) (wUncompMeasPrefix v R k uLo w huw r hr rest m
        (Nat.le_of_succ_le hm)) (fPair R k uLo w huw r hr m hm)
        (fPair_indep R k uLo w hw huw r hr m hm) (fun _ ↦ rfl) (uUpperXorPrefix R k uLo w hw
        huw r hr m (Nat.le_of_succ_le hm) * oneHotPreOp P bStarFn uLo w r (Nat.le_of_lt hr))
        R_out (projBit_zero_uUpperXorPrefix_oneHotPreOp P bStarFn uLo w hw huw r hr m hm)
        (subspaceStep_wUncompMeasPrefix v P bStarFn uLo w hw huw r hr hRest m
        (Nat.le_of_succ_le hm))
private theorem wUncompCnotRound_mul_oneHotPreOp {n R k : ℕ} (P : BitAssignment n → Prop)
    [DecidablePred P] (bStarFn : BitAssignment n → Fin R) (uLo : Fin k → Wire n)
    (w : Fin R → Fin (2 ^ k) → Wire n) (hw : WInj w) (huw : ∀ d b p, uLo d ≠ w b p) (r : ℕ)
    (hr : r < k) : (wUncompCnotRound R k w hw r hr).eval.1 * oneHotPreOp P bStarFn uLo w
    (r + 1) hr = uUpperXorPrefix R k uLo w hw huw r hr (R * 2 ^ r) le_rfl * oneHotPreOp P
    bStarFn uLo w r (Nat.le_of_lt hr) := by
  apply matrix_ext_ket; intro δ
  simp only [← Matrix.mulVec_mulVec, oneHotPreOp_mulVec_ket, oneHotPreVec]
  by_cases hV : P δ ∧ ∀ b p, δ (w b p) = 0
  · have hw0 := hV.2
    rw [ite_eq_left hV, ite_eq_left hV, uUpperXorPrefix_mulVec_ket]
    let bStar := bStarFn δ
    let sLo := idxValPrefix uLo δ r (Nat.le_of_lt hr)
    have hsLo : sLo < 2 ^ r := idxValPrefix_lt_two_pow uLo δ r (Nat.le_of_lt hr)
    let pLo : Fin (2 ^ k) := ⟨sLo, pair_lo_lt hr hsLo⟩
    let pHi : Fin (2 ^ k) := ⟨sLo + 2 ^ r, pair_hi_lt hr hsLo⟩
    let δMid := Function.update δ (w bStar pLo) 1
    let δAfter := Function.update δMid (w bStar pHi) (δ (uLo ⟨r, hr⟩))
    let i₀ := bStar.val * 2 ^ r + sLo
    obtain ⟨hi₀, hdiv₀, hmod₀⟩ := enc_div_mod bStar.isLt hsLo
    have hqUp₀ : qUp R k w r hr i₀ hi₀ = w bStar pHi := by
      dsimp only [qUp]
      exact congrArg₂ w (Fin.ext hdiv₀) (Fin.ext (by dsimp [pHi]; rw [hmod₀]))
    have hqLo₀ : qLo R k w r hr i₀ hi₀ = w bStar pLo := by
      dsimp only [qLo]
      exact congrArg₂ w (Fin.ext hdiv₀) (Fin.ext hmod₀)
    have hMidUp0 (i : ℕ) (hi : i < R * 2 ^ r) : δMid (qUp R k w r hr i hi) = 0 := by
      have hne : qUp R k w r hr i hi ≠ w bStar pLo :=
        w_ne_of_pair_ne hw (Or.inr fun e ↦ by
          have hv := congrArg Fin.val e; dsimp [pLo] at hv; omega)
      exact (Function.update_of_ne hne 1 δ).trans (hw0 _ _)
    have hneLoHi : w bStar pLo ≠ w bStar pHi :=
      w_ne_of_pair_ne hw (Or.inr fun e ↦ by
        have hv := congrArg Fin.val e; dsimp [pLo, pHi] at hv; omega)
    have hLHS : (wUncompCnotRound R k w hw r hr).eval.1.mulVec (ket (Function.update δ (w
        bStar ⟨idxValPrefix uLo δ (r + 1) hr, Nat.lt_of_lt_of_le (idxValPrefix_lt_two_pow uLo
        δ (r + 1) hr) (Nat.pow_le_pow_right (by omega) hr)⟩) 1)) = ket δAfter := by
      let fGate (i : ℕ) (hi : i < R * 2 ^ r) :=
        Circuit.CNOT (qUp R k w r hr i hi) (qLo R k w r hr i hi) (qLo_ne_qUp hw hr hi hi).symm
      dsimp only [wUncompCnotRound]
      rcases bit_cases (δ (uLo ⟨r, hr⟩)) with hu0 | hu1
      · have hpEq : (⟨idxValPrefix uLo δ (r + 1) hr,
            Nat.lt_of_lt_of_le (idxValPrefix_lt_two_pow uLo δ (r + 1) hr)
              (Nat.pow_le_pow_right (by omega) hr)⟩ : Fin (2 ^ k)) = pLo :=
          Fin.ext (by
            dsimp [idxValPrefix, pLo, sLo]; rw [ite_eq_right (by rw [hu0]; decide)]; omega)
        have hAfterEq : δAfter = δMid := by
          dsimp only [δAfter]
          rw [hu0]
          exact ((Function.update_of_ne hneLoHi.symm 1 δ).trans (hw0 bStar pHi)) ▸
            Function.update_eq_self (w bStar pHi) δMid
        rw [hpEq, hAfterEq]
        exact seqNat_mulVec_fixed (ket δMid) (R * 2 ^ r) fGate fun i hi ↦
          ket_CNOT_of_ctrl_zero _ (hMidUp0 i hi)
      · have hpEq : (⟨idxValPrefix uLo δ (r + 1) hr,
            Nat.lt_of_lt_of_le (idxValPrefix_lt_two_pow uLo δ (r + 1) hr)
              (Nat.pow_le_pow_right (by omega) hr)⟩ : Fin (2 ^ k)) = pHi :=
          Fin.ext (by dsimp [idxValPrefix, pHi, sLo]; rw [ite_eq_left hu1])
        rw [hpEq]
        have hSeq := seqNat_mulVec_single
          (ket (Function.update δ (w bStar pHi) 1))
          (ket δAfter) i₀ (R * 2 ^ r) fGate
          (fun i hi hlt ↦ by
            have hne : qUp R k w r hr i hi ≠ w bStar pHi := by
              rw [← hqUp₀]; exact qUp_ne_of_ne hw hr hi hi₀ (Nat.ne_of_lt hlt)
            exact ket_CNOT_of_ctrl_zero _ ((Function.update_of_ne hne 1 δ).trans (hw0 _ _)))
          (fun hi₀' ↦ by
            have hqUpE : qUp R k w r hr i₀ hi₀' = w bStar pHi := hqUp₀
            have hqLoE : qLo R k w r hr i₀ hi₀' = w bStar pLo := hqLo₀
            dsimp only [fGate]
            rw [ket_CNOT, hqUpE, hqLoE, Function.update_of_ne hneLoHi, hw0 bStar pLo,
              Function.update_self, zero_add, Function.update_comm hneLoHi.symm]
            dsimp only [δAfter, δMid]
            rw [hu1])
          (fun i hi hgt ↦ by
            have hne : qUp R k w r hr i hi ≠ w bStar pHi := by
              rw [← hqUp₀]; exact qUp_ne_of_ne hw hr hi hi₀ (Nat.ne_of_gt hgt)
            exact ket_CNOT_of_ctrl_zero _
              ((Function.update_of_ne hne (δ (uLo ⟨r, hr⟩)) δMid).trans (hMidUp0 i hi)))
        rw [ite_eq_left hi₀] at hSeq
        exact hSeq
    rw [hLHS]; congr 1; funext u
    by_cases hU : ∃ idx : Fin (R * 2 ^ r), u = qUp R k w r hr idx.val idx.isLt
    · obtain ⟨⟨i, hi⟩, rfl⟩ := hU
      have hBits := upperXorBits_qUp_lt R k uLo w hw huw r hr δMid (R * 2 ^ r) le_rfl i hi
      dsimp only at hBits
      rw [show upperXorBits R k uLo w huw r hr (R * 2 ^ r) le_rfl δMid (qUp R k w r hr i hi) =
          δMid (qUp R k w r hr i hi) + δMid (qLo R k w r hr i hi) * δMid (uLo ⟨r, hr⟩) from hBits,
        hMidUp0 i hi, zero_add,
        show δMid (uLo ⟨r, hr⟩) = δ (uLo ⟨r, hr⟩) from Function.update_of_ne (huw ⟨r, hr⟩ _ _) 1 δ]
      by_cases hii₀ : i = i₀
      · subst hii₀
        dsimp only [δAfter, δMid]
        rw [hqUp₀, hqLo₀, Function.update_self, Function.update_self, one_mul]
      · have hneUp : qUp R k w r hr i hi ≠ w bStar pHi := by
          rw [← hqUp₀]; exact qUp_ne_of_ne hw hr hi hi₀ hii₀
        have hneLo : qLo R k w r hr i hi ≠ w bStar pLo := by
          have hdisj := enc_ne_iff hii₀
          exact w_ne_of_pair_ne hw (by
            rcases hdisj with hdb | hdm
            · exact Or.inl fun e ↦ hdb (congrArg Fin.val e)
            · exact Or.inr fun e ↦ hdm (congrArg Fin.val e))
        have hw0_qLo : δ (qLo R k w r hr i hi) = 0 := hw0 _ _
        dsimp only [δAfter, δMid]
        rw [Function.update_of_ne hneUp, Function.update_of_ne hneLo, hw0_qLo, zero_mul]
        exact hMidUp0 i hi
    · have hneAll : ∀ i (hi : i < R * 2 ^ r), u ≠ qUp R k w r hr i hi :=
        fun i hi e ↦ hU ⟨⟨i, hi⟩, e⟩
      have hneHi : u ≠ w bStar pHi := by rw [← hqUp₀]; exact hneAll i₀ hi₀
      dsimp only [δAfter]
      rw [Function.update_of_ne hneHi,
        upperXorBits_of_ne R k uLo w huw r hr δMid u (R * 2 ^ r) le_rfl hneAll]
  · rw [ite_eq_right hV, ite_eq_right hV, Matrix.mulVec_zero, Matrix.mulVec_zero]
/-- Single `0-T` reverse tree round `r < k`: `wUncompCnotRound` followed by `wUncompMeasPrefix`. -/
def wUncompRoundDyn {Var : Type} {n : ℕ} (v : Var) (R k : ℕ) (uLo : Fin k → Wire n)
    (w : Fin R → Fin (2 ^ k) → Wire n) (hw : WInj w) (huw : ∀ d b p, uLo d ≠ w b p)
    (r : ℕ) (hr : r < k) (rest : DynamicCircuit Var n) : DynamicCircuit Var n :=
  .seq (.circuit (wUncompCnotRound R k w hw r hr))
    (wUncompMeasPrefix v R k uLo w huw r hr rest (R * 2 ^ r) le_rfl)
/-- Full `0-T` reverse CH-tree uncomputation across levels `m - 1, ..., 0`, continuing with
`rest`. -/
def wUncompTreeDyn {Var : Type} {n : ℕ} (v : Var) (R k : ℕ) (uLo : Fin k → Wire n)
    (w : Fin R → Fin (2 ^ k) → Wire n) (hw : WInj w) (huw : ∀ d b p, uLo d ≠ w b p)
    (rest : DynamicCircuit Var n) : (m : ℕ) → m ≤ k → DynamicCircuit Var n
  | 0, _ => rest
  | r + 1, hr =>
      wUncompRoundDyn v R k uLo w hw huw r hr
        (wUncompTreeDyn v R k uLo w hw huw rest r (Nat.le_of_succ_le hr))
private theorem count_wUncompTreeDyn {Var : Type} {n : ℕ} (v : Var) (R k : ℕ)
    (uLo : Fin k → Wire n) (w : Fin R → Fin (2 ^ k) → Wire n)
    (hw : WInj w) (huw : ∀ d b p, uLo d ≠ w b p) (rest : DynamicCircuit Var n) :
    ∀ (m : ℕ) (hm : m ≤ k),
      (wUncompTreeDyn v R k uLo w hw huw rest m hm).count .T = rest.count .T ∧
      (wUncompTreeDyn v R k uLo w hw huw rest m hm).count .TOFF = rest.count .TOFF
  | 0, _ => ⟨rfl, rfl⟩
  | r + 1, hr => by
      obtain ⟨ht, hf⟩ := count_wUncompTreeDyn v R k uLo w hw huw rest r (Nat.le_of_succ_le hr)
      obtain ⟨mt, mf⟩ := count_wUncompMeasPrefix v R k uLo w huw r hr
        (wUncompTreeDyn v R k uLo w hw huw rest r (Nat.le_of_succ_le hr)) (R * 2 ^ r) le_rfl
      have hct : (wUncompCnotRound R k w hw r hr).count .T = 0 := by
        rw [wUncompCnotRound, count_seqNat_T 0 (R * 2 ^ r) _ (fun _ _ ↦ by simp [Circuit.CNOT]),
          Nat.mul_zero]
      have hcf : (wUncompCnotRound R k w hw r hr).count .TOFF = 0 :=
        count_seqNat_TOFF_zero (R * 2 ^ r) _ (fun _ _ ↦ by simp [Circuit.CNOT])
      dsimp only [wUncompTreeDyn, wUncompRoundDyn, DynamicCircuit.count]
      rw [hct, hcf, mt, mf, ht, hf, Nat.zero_add, Nat.zero_add]
      exact ⟨rfl, rfl⟩
private theorem subspaceStep_wUncompTreeDyn {Var : Type} [Fintype Var] [DecidableEq Var]
    {n R k : ℕ} (v : Var) (P : BitAssignment n → Prop) [DecidablePred P]
    (bStarFn : BitAssignment n → Fin R) (uLo : Fin k → Wire n)
    (w : Fin R → Fin (2 ^ k) → Wire n) (hw : WInj w) (huw : ∀ d b p, uLo d ≠ w b p)
    {rest : DynamicCircuit Var n} {R_out : Operator (2 ^ n)}
    (hRest : SubspaceStep (oneHotPreOp P bStarFn uLo w 0 (Nat.zero_le k)) R_out rest) :
    ∀ (m : ℕ) (hm : m ≤ k),
      SubspaceStep (oneHotPreOp P bStarFn uLo w m hm) R_out
        (wUncompTreeDyn v R k uLo w hw huw rest m hm)
  | 0, _ => hRest
  | r + 1, hr =>
      (subspaceStep_congr_out
        (subspaceStep_of_circuit (Var := Var) (oneHotPreOp P bStarFn uLo w (r + 1) hr)
          (wUncompCnotRound R k w hw r hr))
        (wUncompCnotRound_mul_oneHotPreOp P bStarFn uLo w hw huw r hr)).seq
        (subspaceStep_wUncompMeasPrefix v P bStarFn uLo w hw huw r hr
          (subspaceStep_wUncompTreeDyn v P bStarFn uLo w hw huw hRest r (Nat.le_of_succ_le hr))
          (R * 2 ^ r) le_rfl)
/- Section 3: Generic `R`-block root specification, `wComputeCore`, `wUncomputeCore`, and
`WRouterBracket` -/
/-- Root-initialization specification for an `R`-block W-state router (`N = R * 2^k`). -/
structure WRootSpec (R k D N n : ℕ) (hRN : R * 2 ^ k = N) (hk : k ≤ D)
    (wIdx : Fin D → Wire n) (wOut : Fin N → Wire n) : Type where
  bStarFn : BitAssignment n → Fin R
  cRootInit : Circuit n
  cRootUninit : Circuit n
  count_init : cRootInit.count .T = 0 ∧ cRootInit.count .TOFF = 0
  count_uninit : cRootUninit.count .T = 0 ∧ cRootUninit.count .TOFF = 0
  cw_init : ∀ {S : Wire n → Prop}, (∀ d, S (wIdx d)) → (∀ j, S (wOut j)) → CircWires S cRootInit
  cw_uninit : ∀ {S : Wire n → Prop}, (∀ d, S (wIdx d)) → (∀ j, S (wOut j)) → CircWires S cRootUninit
  idx_decomp : ∀ δ : BitAssignment n, idxValD wIdx δ < N →
    (bStarFn δ).val * 2 ^ k + idxValPrefix (uLoOf hk wIdx) δ k le_rfl = idxValD wIdx δ
  init_ket : ∀ δ : BitAssignment n, (∀ j, δ (wOut j) = 0) → idxValD wIdx δ < N →
    cRootInit.eval.1.mulVec (ket δ) =
      ket (Function.update δ (blockWires hRN wOut (bStarFn δ) ⟨0, Nat.two_pow_pos k⟩) 1)
  uninit_init : ∀ v : Fin (2 ^ n) → ℂ, cRootUninit.eval.1.mulVec (cRootInit.eval.1.mulVec v) = v
theorem two_mul_pow_eq (k : ℕ) : 2 * 2 ^ k = 2 ^ (k + 1) := by ring
/-- Block selector for `Pow2` (`R = 2`) from MSB `u0`. -/
def bStarPow2 {n : ℕ} (u0 : Wire n) (δ : BitAssignment n) : Fin 2 :=
  if δ u0 = 1 then ⟨1, by omega⟩ else ⟨0, by omega⟩
/-- Root initialization/uninitialization bundle for `Pow2` (`N = 2^(k+1)`). -/
def wRootSpecPow2 {k n : ℕ} (wIdx : Fin (k + 1) → Wire n) (wOut : Fin (2 ^ (k + 1)) → Wire n)
    (hIdxOut : ∀ d j, wIdx d ≠ wOut j) :
    WRootSpec 2 k (k + 1) (2 ^ (k + 1)) n (two_mul_pow_eq k) (Nat.le_succ k) wIdx wOut :=
  let u0 := wIdx ⟨k, Nat.lt_succ_self k⟩
  let w := blockWires (two_mul_pow_eq k) wOut
  let p00 : Fin (2 ^ k) := ⟨0, Nat.two_pow_pos k⟩
  let w00 := w ⟨0, by omega⟩ p00
  let w10 := w ⟨1, by omega⟩ p00
  let hu00 : u0 ≠ w00 := hIdxOut ⟨k, Nat.lt_succ_self k⟩ _
  let hu10 : u0 ≠ w10 := hIdxOut ⟨k, Nat.lt_succ_self k⟩ _
  { bStarFn := bStarPow2 u0
    cRootInit := Circuit.X w00 ;;ᶜ Circuit.CNOT u0 w00 hu00 ;;ᶜ Circuit.CNOT u0 w10 hu10
    cRootUninit := Circuit.CNOT u0 w10 hu10 ;;ᶜ Circuit.CNOT u0 w00 hu00 ;;ᶜ Circuit.X w00
    count_init := ⟨by simp [Circuit.count_seq, Circuit.X, Circuit.CNOT],
      by simp [Circuit.count_seq, Circuit.X, Circuit.CNOT]⟩
    count_uninit := ⟨by simp [Circuit.count_seq, Circuit.X, Circuit.CNOT],
      by simp [Circuit.count_seq, Circuit.X, Circuit.CNOT]⟩
    cw_init := fun hI hO ↦ ⟨cw_1 (hO _), cw_cnot (hI _) (hO _), cw_cnot (hI _) (hO _)⟩
    cw_uninit := fun hI hO ↦ ⟨cw_cnot (hI _) (hO _), cw_cnot (hI _) (hO _), cw_1 (hO _)⟩
    idx_decomp := fun δ _ ↦ by
      rw [idxValPrefix_uLoOf (Nat.le_succ k) wIdx δ k le_rfl]
      dsimp only [idxValD, idxValPrefix, bStarPow2, u0]
      split_ifs <;> dsimp <;> omega
    init_ket := fun δ hOut0 _ ↦ by
      have hw00 : δ w00 = 0 := hOut0 _
      have hw10 : δ w10 = 0 := hOut0 _
      rcases bit_cases (δ u0) with hu0 | hu1
      · have hb : bStarPow2 u0 δ = ⟨0, by omega⟩ := by
          dsimp [bStarPow2]; rw [ite_eq_right (by rw [hu0]; decide)]
        have hc0 : Function.update δ w00 1 u0 = 0 :=
          (Function.update_of_ne hu00 1 δ).trans hu0
        rw [hb, eval_seq_mulVec, eval_seq_mulVec, ket_X, hw00, zero_add,
          ket_CNOT_of_ctrl_zero hu00 hc0, ket_CNOT_of_ctrl_zero hu10 hc0]
      · have hb : bStarPow2 u0 δ = ⟨1, by omega⟩ := by
          dsimp [bStarPow2]; rw [ite_eq_left hu1]
        have hw00_0 : Function.update δ w00 0 = δ := hw00 ▸ Function.update_eq_self w00 δ
        rw[hb, eval_seq_mulVec, eval_seq_mulVec, ket_X, hw00, zero_add, ket_CNOT,
            Function.update_of_ne hu00, hu1, Function.update_self, CharTwo.add_self_eq_zero,
            Function.update_idem, hw00_0, ket_CNOT, hw10, hu1, zero_add]
    uninit_init := fun v ↦ by
      simp only [eval_seq_mulVec, mulVec_CNOT_invol, mulVec_X_invol] }
attribute [local semireducible] projBit_dqmu
/-- Pairwise disjointness bundle for a dummy-assisted W-shift round on `w : Fin R → Fin (2^k) → Wire
n`. -/
structure WOptInj {n : ℕ} (R k : ℕ) (uLo : Fin k → Wire n)
    (w : Fin R → Fin (2 ^ k) → Wire n) (rDum wDum qEnc : Wire n) : Prop where
  w_inj : WInj w
  uLo_ne_w : ∀ d b p, uLo d ≠ w b p
  uLo_ne_rDum : ∀ d, uLo d ≠ rDum
  uLo_ne_wDum : ∀ d, uLo d ≠ wDum
  uLo_ne_qEnc : ∀ d, uLo d ≠ qEnc
  w_ne_rDum : ∀ b p, w b p ≠ rDum
  w_ne_wDum : ∀ b p, w b p ≠ wDum
  w_ne_qEnc : ∀ b p, w b p ≠ qEnc
  rDum_ne_wDum : rDum ≠ wDum
  rDum_ne_qEnc : rDum ≠ qEnc
  wDum_ne_qEnc : wDum ≠ qEnc
theorem update_eq_self_of_zero {n : ℕ} {δ : BitAssignment n} {q : Wire n} (h0 : δ q = 0) :
    Function.update δ q 0 = δ := h0 ▸ Function.update_eq_self q δ
theorem ket_CNOT_ctrl_zero {n : ℕ} {c t : Wire n} (h : c ≠ t) {δ : BitAssignment n}
    (hc0 : δ c = 0) : (Circuit.CNOT c t h).eval.1.mulVec (ket δ) = ket δ := by
  rw [ket_CNOT c t h δ, hc0, add_zero, Function.update_eq_self]
theorem cnotOddToEnc_mulVec_ket_zero {n R k : ℕ} (w : Fin R → Fin (2 ^ k) → Wire n) (qEnc : Wire n)
    (hwq : ∀ b p, w b p ≠ qEnc) (d : ℕ)
    (δ : BitAssignment n) (hw0 : ∀ b p, δ (w b p) = 0) :
    (cnotOddToEnc R k w qEnc hwq d).eval.1.mulVec (ket δ) = ket δ :=
  seqNat_mulVec_fixed (ket δ) (R * 2 ^ k) _ fun _ _ ↦ by
    dsimp only
    split_ifs
    · exact ket_CNOT_ctrl_zero _ (hw0 _ _)
    · rw [Circuit.eval_identity, Submonoid.coe_one, Matrix.one_mulVec]
theorem barrelSwap_mulVec_ket_zero {n R k : ℕ} (w : Fin R → Fin (2 ^ k) → Wire n)
    (hw : WInj w) (d : ℕ) (δ : BitAssignment n) (hw0 : ∀ b p, δ (w b p) = 0) :
    (barrelSwap R k w hw d).eval.1.mulVec (ket δ) = ket δ :=
  seqNat_mulVec_fixed (ket δ) (R * 2 ^ k) _ fun _ _ ↦ by
    dsimp only
    split_ifs
    · exact swap3Cnot_mulVec_ket_zero _ _ _ δ (hw0 _ _) (hw0 _ _)
    · rw [Circuit.eval_identity, Submonoid.coe_one, Matrix.one_mulVec]
/-- Pre-measurement circuit of `wShiftDummyLevel`. -/
def wShiftDummyPre {n : ℕ} (R k : ℕ) (uLo : Fin k → Wire n)
    (w : Fin R → Fin (2 ^ k) → Wire n) (rDum wDum qEnc : Wire n)
    (hInj : WOptInj R k uLo w rDum wDum qEnc) (d : ℕ) (hd : d < k) : Circuit n :=
  chGateCirc rDum wDum hInj.rDum_ne_wDum ;;ᶜ
  cnotOddToEnc R k w qEnc hInj.w_ne_qEnc d ;;ᶜ
  Circuit.CNOT wDum qEnc hInj.wDum_ne_qEnc ;;ᶜ
  Circuit.CNOT (uLo ⟨d, hd⟩) qEnc (hInj.uLo_ne_qEnc ⟨d, hd⟩)
/-- Outcome-1 fixup circuit of `wShiftDummyLevel`. -/
def wShiftDummyFix {n : ℕ} (R k : ℕ) (uLo : Fin k → Wire n) (w : Fin R → Fin (2 ^ k) → Wire n)
    (rDum wDum qEnc : Wire n) (hInj : WOptInj R k uLo w rDum wDum qEnc) (d : ℕ) : Circuit n :=
  Circuit.CNOT rDum wDum hInj.rDum_ne_wDum ;;ᶜ
  barrelSwap R k w hInj.w_inj d
/-- Single `2-T` (`0 .TOFF`) dummy-assisted barrel-shift round at bit `d < k`. -/
def wShiftDummyLevel {Var : Type} {n : ℕ} (v : Var) (R k : ℕ) (uLo : Fin k → Wire n)
    (w : Fin R → Fin (2 ^ k) → Wire n) (rDum wDum qEnc : Wire n)
    (hInj : WOptInj R k uLo w rDum wDum qEnc) (d : ℕ) (hd : d < k) : DynamicCircuit Var n :=
    .seq (.circuit (wShiftDummyPre R k uLo w rDum wDum qEnc hInj d hd)) (.seq (zResetFixupDyn
    v qEnc (wShiftDummyFix R k uLo w rDum wDum qEnc hInj d)) (xUnloadCzPairsSeqDyn v wDum
    [⟨rDum, ⟨uLo ⟨d, hd⟩, (hInj.uLo_ne_rDum ⟨d, hd⟩).symm⟩⟩] (.circuit .identity)))
theorem count_wShiftDummyLevel {Var : Type} {n : ℕ} (v : Var) (R k : ℕ) (uLo : Fin k → Wire n)
    (w : Fin R → Fin (2 ^ k) → Wire n) (rDum wDum qEnc : Wire n)
    (hInj : WOptInj R k uLo w rDum wDum qEnc) (d : ℕ) (hd : d < k) :
    (wShiftDummyLevel v R k uLo w rDum wDum qEnc hInj d hd).count .T = 2 ∧
    (wShiftDummyLevel v R k uLo w rDum wDum qEnc hInj d hd).count .TOFF = 0 := by
  obtain ⟨tc, fc⟩ := count_chGateCirc rDum wDum hInj.rDum_ne_wDum
  obtain ⟨to_, fo_⟩ := count_cnotOddToEnc R k w qEnc hInj.w_ne_qEnc d
  obtain ⟨tb, fb⟩ := count_barrelSwap R k w hInj.w_inj d
  obtain ⟨tx, fx⟩ := count_xUnloadCzPairsSeqDyn v wDum
    [⟨rDum, ⟨uLo ⟨d, hd⟩, (hInj.uLo_ne_rDum ⟨d, hd⟩).symm⟩⟩] (.circuit .identity)
  refine ⟨?_, ?_⟩ <;>
    simp [wShiftDummyLevel, wShiftDummyPre, wShiftDummyFix, zResetFixupDyn,
      DynamicCircuit.count, Circuit.count_seq,
      Circuit.CNOT, Circuit.X, tc, fc, to_, fo_, tb, fb, tx, fx]
/-- Optional shifted W-superposition vector at level `d ≤ k` (`wSuperVec` on `activePred`, `ket δ`
otherwise). -/
def wOptSuperVec {n R k : ℕ} (P activePred : BitAssignment n → Prop) [DecidablePred P]
    [DecidablePred activePred] (bStarFn : BitAssignment n → Fin R) (uLo : Fin k → Wire n)
    (w : Fin R → Fin (2 ^ k) → Wire n) (wDum qEnc : Wire n) (δ : BitAssignment n) (d : ℕ)
    (hd : d ≤ k) : Fin (2 ^ n) → ℂ := if P δ ∧ (∀ b p, δ (w b p) = 0) ∧ δ wDum = 0 ∧ δ qEnc =
    0 then if activePred δ then wSuperVec bStarFn uLo w qEnc δ d hd else ket δ else 0
/-- Operator mapping computational basis kets via `wOptSuperVec`. -/
def wOptSuperOp {n R k : ℕ} (P activePred : BitAssignment n → Prop) [DecidablePred P]
    [DecidablePred activePred] (bStarFn : BitAssignment n → Fin R) (uLo : Fin k → Wire n)
    (w : Fin R → Fin (2 ^ k) → Wire n) (wDum qEnc : Wire n) (d : ℕ) (hd : d ≤ k) : Operator
    (2 ^ n) := mkVecOp fun δ ↦ wOptSuperVec P activePred bStarFn uLo w wDum qEnc δ d hd
theorem fDum_indep {n k : ℕ} (uLo : Fin k → Wire n) (rDum wDum qEnc : Wire n) {R : ℕ}
    {w : Fin R → Fin (2 ^ k) → Wire n} (hInj : WOptInj R k uLo w rDum wDum qEnc) (d : ℕ)
    (hd : d < k) (β : BitAssignment n) (a : ZMod 2) : czPairsParity
    [⟨rDum, ⟨uLo ⟨d, hd⟩, (hInj.uLo_ne_rDum ⟨d, hd⟩).symm⟩⟩] (Function.update β wDum a) =
    czPairsParity [⟨rDum, ⟨uLo ⟨d, hd⟩, (hInj.uLo_ne_rDum ⟨d, hd⟩).symm⟩⟩] β := by
  dsimp only [czPairsParity]
  rw [Function.update_of_ne hInj.rDum_ne_wDum, Function.update_of_ne (hInj.uLo_ne_wDum ⟨d, hd⟩)]
theorem wShiftDummy_pre_act {n R k : ℕ} (uLo : Fin k → Wire n)
    (w : Fin R → Fin (2 ^ k) → Wire n) (rDum wDum qEnc : Wire n)
    (hInj : WOptInj R k uLo w rDum wDum qEnc) (d : ℕ) (hd : d < k)
    (δ : BitAssignment n) (hr0 : δ rDum = 0) (hw0 : ∀ b p, δ (w b p) = 0)
    (hwd0 : δ wDum = 0) (hq0 : δ qEnc = 0) (b : Fin R) (p : Fin (2 ^ k)) :
    (wShiftDummyPre R k uLo w rDum wDum qEnc hInj d hd).eval.1.mulVec
        (ket (Function.update δ (w b p) 1)) =
    (cnotOddToEnc R k w qEnc hInj.w_ne_qEnc d ;;ᶜ
      Circuit.CNOT (uLo ⟨d, hd⟩) qEnc (hInj.uLo_ne_qEnc ⟨d, hd⟩)).eval.1.mulVec
        (ket (Function.update δ (w b p) 1)) := by
  let δ₁ := Function.update δ (w b p) 1
  have hr1 : δ₁ rDum = 0 := (Function.update_of_ne (hInj.w_ne_rDum b p).symm 1 δ).trans hr0
  have hwd1 : δ₁ wDum = 0 := (Function.update_of_ne (hInj.w_ne_wDum b p).symm 1 δ).trans hwd0
  dsimp only [wShiftDummyPre]
  simp only [eval_seq_mulVec]
  rw [chGateCirc_mulVec_ket_zero rDum wDum hInj.rDum_ne_wDum δ₁ hr1,
    cnotOddToEnc_mulVec_ket w qEnc hInj.w_inj hInj.w_ne_qEnc d δ hw0 hq0 b p,
    ket_CNOT_ctrl_zero _ ((Function.update_of_ne hInj.wDum_ne_qEnc _ δ₁).trans hwd1)]
theorem wShiftDummy_pre_inact {n R k : ℕ} (uLo : Fin k → Wire n)
    (w : Fin R → Fin (2 ^ k) → Wire n) (rDum wDum qEnc : Wire n)
    (hInj : WOptInj R k uLo w rDum wDum qEnc) (d : ℕ) (hd : d < k) (δ : BitAssignment n)
    (hr1 : δ rDum = 1) (hw0 : ∀ b p, δ (w b p) = 0) (hwd0 : δ wDum = 0) (hq0 : δ qEnc = 0) :
    (wShiftDummyPre R k uLo w rDum wDum qEnc hInj d hd).eval.1.mulVec (ket δ) = sqrtHalf •
    (ket (Function.update δ qEnc (δ (uLo ⟨d, hd⟩))) + ket (Function.update (Function.update δ
    wDum 1) qEnc (1 + δ (uLo ⟨d, hd⟩)))) := by
  dsimp only [wShiftDummyPre]
  simp only [eval_seq_mulVec]
  rw [chGateCirc_mulVec_ket_one rDum wDum hInj.rDum_ne_wDum δ hr1,
    ket_H wDum δ, hwd0, show bitSign (0 : ZMod 2) = (1 : ℂ) from rfl, one_smul,
    update_eq_self_of_zero hwd0]
  simp only [Matrix.mulVec_smul, Matrix.mulVec_add]
  congr 1; congr 1
  · rw [cnotOddToEnc_mulVec_ket_zero w qEnc hInj.w_ne_qEnc d δ hw0,
      ket_CNOT_ctrl_zero _ hwd0, ket_CNOT, hq0, zero_add]
  · let δw := Function.update δ wDum 1
    have hw0w : ∀ b p, δw (w b p) = 0 := fun b p ↦
      (Function.update_of_ne (hInj.w_ne_wDum b p) 1 δ).trans (hw0 b p)
    have hq0w : δw qEnc = 0 := (Function.update_of_ne hInj.wDum_ne_qEnc.symm 1 δ).trans hq0
    have huw : δw (uLo ⟨d, hd⟩) = δ (uLo ⟨d, hd⟩) :=
      Function.update_of_ne (hInj.uLo_ne_wDum ⟨d, hd⟩) 1 δ
    rw [cnotOddToEnc_mulVec_ket_zero w qEnc hInj.w_ne_qEnc d δw hw0w,
      ket_CNOT, hq0w, show δw wDum = 1 from Function.update_self wDum 1 δ, zero_add,
      ket_CNOT, Function.update_self, Function.update_of_ne (hInj.uLo_ne_qEnc ⟨d, hd⟩),
      huw, Function.update_idem]
/- Section 2b1: Dummy parity unitary and outcome-0 branch identity for `wShiftDummyLevel` -/
/-- Dummy-ancilla parity unitary toggled by `rDum * uLo[d]` before X-measurement unload. -/
def uDumShift {n R k : ℕ} (uLo : Fin k → Wire n) (w : Fin R → Fin (2 ^ k) → Wire n)
    (rDum wDum qEnc : Wire n) (hInj : WOptInj R k uLo w rDum wDum qEnc) (d : ℕ) (hd : d < k) :
    unitaryGroup (Fin (2 ^ n)) ℂ := xorWireUnitary wDum (czPairsParity [⟨rDum, ⟨uLo ⟨d, hd⟩,
    (hInj.uLo_ne_rDum ⟨d, hd⟩).symm⟩⟩]) (fDum_indep uLo rDum wDum qEnc hInj d hd)
theorem uDumShift_act {n R k : ℕ} (uLo : Fin k → Wire n) (w : Fin R → Fin (2 ^ k) → Wire n)
    (rDum wDum qEnc : Wire n) (hInj : WOptInj R k uLo w rDum wDum qEnc) (d : ℕ) (hd : d < k)
    (δ : BitAssignment n) (hr0 : δ rDum = 0) (hwd0 : δ wDum = 0) (b : Fin R) (p : Fin (2 ^ k))
    : (uDumShift uLo w rDum wDum qEnc hInj d hd).1.mulVec (ket (Function.update δ (w b p) 1))
    = ket (Function.update δ (w b p) 1) := by
  dsimp only [uDumShift]
  rw [xorWireUnitary_mulVec_ket]
  have h1 : czPairsParity [⟨rDum, ⟨uLo ⟨d, hd⟩, (hInj.uLo_ne_rDum ⟨d, hd⟩).symm⟩⟩]
      (Function.update δ (w b p) 1) = 0 := by
    dsimp only [czPairsParity]
    rw [Function.update_of_ne (hInj.w_ne_rDum b p).symm, hr0, zero_mul, add_zero]
  have h2 : Function.update δ (w b p) 1 wDum = 0 :=
    (Function.update_of_ne (hInj.w_ne_wDum b p).symm 1 δ).trans hwd0
  rw [h1, h2, add_zero, update_eq_self_of_zero h2]
theorem uDumShift_inact {n R k : ℕ} (uLo : Fin k → Wire n) (w : Fin R → Fin (2 ^ k) → Wire n)
    (rDum wDum qEnc : Wire n) (hInj : WOptInj R k uLo w rDum wDum qEnc)
    (d : ℕ) (hd : d < k) (δ : BitAssignment n) (hr1 : δ rDum = 1) (hwd0 : δ wDum = 0) :
    (uDumShift uLo w rDum wDum qEnc hInj d hd).1.mulVec (ket δ) =
      ket (Function.update δ wDum (δ (uLo ⟨d, hd⟩))) := by
  dsimp only [uDumShift]
  rw [xorWireUnitary_mulVec_ket]
  have h1 : czPairsParity [⟨rDum, ⟨uLo ⟨d, hd⟩, (hInj.uLo_ne_rDum ⟨d, hd⟩).symm⟩⟩] δ =
      δ (uLo ⟨d, hd⟩) := by
    dsimp only [czPairsParity]; rw [hr1, one_mul, add_zero]
  rw [h1, hwd0, zero_add]
theorem wShiftDummy_branch0 {n R k : ℕ} (P activePred : BitAssignment n → Prop)
    [DecidablePred P] [DecidablePred activePred] (bStarFn : BitAssignment n → Fin R)
    (uLo : Fin k → Wire n) (w : Fin R → Fin (2 ^ k) → Wire n) (rDum wDum qEnc : Wire n)
    (hInj : WOptInj R k uLo w rDum wDum qEnc)
    (hDumBit : ∀ δ, P δ → δ rDum = (if activePred δ then 0 else 1)) (d : ℕ) (hd : d < k) :
    (QRegister.singleton qEnc).basisOutcomeProjector 0 * ((wShiftDummyPre R k uLo w rDum wDum
    qEnc hInj d hd).eval.1 * wOptSuperOp P activePred bStarFn uLo w wDum qEnc d (Nat.le_of_lt
    hd)) = sqrtHalf • ((uDumShift uLo w rDum wDum qEnc hInj d hd).1 * wOptSuperOp P activePred
    bStarFn uLo w wDum qEnc (d + 1) hd) := by
  let P₀ := (QRegister.singleton qEnc).basisOutcomeProjector 0
  let cPreFull := wShiftDummyPre R k uLo w rDum wDum qEnc hInj d hd
  let UDum := uDumShift uLo w rDum wDum qEnc hInj d hd
  have hev (q : Fin (2 ^ (k - (d + 1)))) : ¬ decide (2 * q.val % 2 = 1) = true := by
    simp only [decide_eq_true_eq]; omega
  have hod (q : Fin (2 ^ (k - (d + 1)))) : decide ((2 * q.val + 1) % 2 = 1) = true := by
    simp only [decide_eq_true_eq]; omega
  have hEv (q : Fin (2 ^ (k - (d + 1)))) : 2 * q.val < 2 ^ (k - d) := by
    have h : 2 ^ (k - d) = 2 * 2 ^ (k - (d + 1)) := by
      rw [show k - d = k - (d + 1) + 1 by omega, Nat.pow_succ]; ring
    have := q.isLt; omega
  have hOd (q : Fin (2 ^ (k - (d + 1)))) : 2 * q.val + 1 < 2 ^ (k - d) := by
    have h : 2 ^ (k - d) = 2 * 2 ^ (k - (d + 1)) := by
      rw [show k - d = k - (d + 1) + 1 by omega, Nat.pow_succ]; ring
    have := q.isLt; omega
  apply matrix_ext_ket; intro δ
  simp only [← Matrix.mulVec_mulVec, Matrix.smul_mulVec, wOptSuperOp,
    mkVecOp_mulVec_ket, wOptSuperVec]
  by_cases hV : P δ ∧ (∀ b p, δ (w b p) = 0) ∧ δ wDum = 0 ∧ δ qEnc = 0
  · have ⟨hP, hw0, hwd0, hq0⟩ := hV
    rw [ite_eq_left hV, ite_eq_left hV]
    by_cases hAct : activePred δ
    · have hr0 : δ rDum = 0 := (hDumBit δ hP).trans (ite_eq_left hAct)
      rw [ite_eq_left hAct, ite_eq_left hAct]
      dsimp only [wSuperVec]
      rw [ite_eq_left ⟨hw0, hq0⟩, ite_eq_left ⟨hw0, hq0⟩,
        Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.mulVec_smul,
        Matrix.mulVec_sum, Matrix.mulVec_sum, Matrix.mulVec_sum]
      have hkd : k - d = k - (d + 1) + 1 := by omega
      rw [show sqrtHalf ^ (k - d) = sqrtHalf * sqrtHalf ^ (k - (d + 1)) by
        rw [hkd, _root_.pow_succ'], smul_smul]
      congr 1
      have hRhs : (∑ hi : Fin (2 ^ (k - (d + 1))), UDum.1.mulVec (ket (Function.update δ (w
          (bStarFn δ) ⟨idxValPrefix uLo δ (d + 1) hd + 2 ^ (d + 1) * hi.val, shift_pos_lt hd
          (idxValPrefix_lt_two_pow uLo δ (d + 1) hd) hi.isLt⟩) 1))) = ∑ hi : Fin
          (2 ^ (k - (d + 1))), ket (Function.update δ (w (bStarFn δ) ⟨idxValPrefix uLo δ (d +
          1) hd + 2 ^ (d + 1) * hi.val, shift_pos_lt hd (idxValPrefix_lt_two_pow uLo δ (d + 1)
          hd) hi.isLt⟩) 1) := Finset.sum_congr rfl fun _ _ ↦ uDumShift_act uLo w rDum wDum
          qEnc hInj d hd δ hr0 hwd0 _ _
      rw [hRhs]
      let e : Fin (2 ^ (k - (d + 1))) ⊕ Fin (2 ^ (k - (d + 1))) ≃ Fin (2 ^ (k - d)) :=
        (finTwoMulEquiv (2 ^ (k - (d + 1)))).trans (finCongr (by rw [hkd, Nat.pow_succ]; ring))
      rw [← e.sum_comp, Fintype.sum_sum_type]
      let lo := idxValPrefix uLo δ d (Nat.le_of_lt hd)
      have hlo : lo < 2 ^ d := idxValPrefix_lt_two_pow uLo δ d (Nat.le_of_lt hd)
      let kIn (hi : ℕ) (hhi : hi < 2 ^ (k - d)) := ket (Function.update δ (w (bStarFn δ) ⟨lo +
          2 ^ d * hi, shift_pos_lt (Nat.le_of_lt hd) hlo hhi⟩) 1)
      let kOut (q : Fin (2 ^ (k - (d + 1)))) := ket (Function.update δ (w (bStarFn δ)
          ⟨idxValPrefix uLo δ (d + 1) hd + 2 ^ (d + 1) * q.val, shift_pos_lt hd
          (idxValPrefix_lt_two_pow uLo δ (d + 1) hd) q.isLt⟩) 1)
      change (∑ q : Fin (2 ^ (k - (d + 1))), P₀.mulVec (cPreFull.eval.1.mulVec (kIn (2 * q.val) (hEv
        q)))) +
        (∑ q : Fin (2 ^ (k - (d + 1))), P₀.mulVec (cPreFull.eval.1.mulVec (kIn (2 * q.val +
          1) (hOd q)))) =
        ∑ q : Fin (2 ^ (k - (d + 1))), kOut q
      have hPre {hi : ℕ} (hhi : hi < 2 ^ (k - d)) :=
        cnotOddAndIdx_mulVec_ket uLo w qEnc hInj.w_inj hInj.w_ne_qEnc hInj.uLo_ne_qEnc
          hInj.uLo_ne_w d hd δ hw0 hq0 (bStarFn δ) hhi
      have hqId (p : Fin (2 ^ k)) : Function.update (Function.update δ (w (bStarFn δ) p) 1)
          qEnc 0 = Function.update δ (w (bStarFn δ) p) 1 := update_eq_self_of_zero
          ((Function.update_of_ne (hInj.w_ne_qEnc _ _).symm 1 δ).trans hq0)
      have ketEq {a b : ℕ} {ha : a < 2 ^ k} {hb : b < 2 ^ k} (h : a = b) :
          ket (Function.update δ (w (bStarFn δ) ⟨a, ha⟩) 1) =
            ket (Function.update δ (w (bStarFn δ) ⟨b, hb⟩) 1) :=
        congrArg (fun p ↦ ket (Function.update δ (w (bStarFn δ) p) 1)) (Fin.ext h)
      rcases bit_cases (δ (uLo ⟨d, hd⟩)) with hu0 | hu1
      · have hs1 : (∑ q, P₀.mulVec (cPreFull.eval.1.mulVec (kIn (2 * q.val) (hEv q)))) = ∑ q,
          kOut q :=
          Finset.sum_congr rfl fun q _ ↦ by
            dsimp only [P₀, cPreFull, kIn, kOut]
            rw [wShiftDummy_pre_act uLo w rDum wDum qEnc hInj d hd δ hr0 hw0 hwd0 hq0 _ _,
              hPre (hEv q), ite_eq_right (hev q), hu0,
              add_zero, ket_projector_zero, Function.update_self, ite_eq_left rfl, hqId]
            exact ketEq (by dsimp [idxValPrefix, lo]; rw [ite_eq_right (by rw [hu0]; decide)]; ring)
        have hs0 : (∑ q, P₀.mulVec (cPreFull.eval.1.mulVec (kIn (2 * q.val + 1) (hOd q)))) = 0 :=
          Finset.sum_eq_zero fun q _ ↦ by
            dsimp only [P₀, cPreFull, kIn]
            rw [wShiftDummy_pre_act uLo w rDum wDum qEnc hInj d hd δ hr0 hw0 hwd0 hq0 _ _,
              hPre (hOd q), ite_eq_left (hod q), hu0,
              add_zero, ket_projector_zero, Function.update_self, ite_eq_right one_ne_zero]
        rw [hs1, hs0, add_zero]
      · have hs0 : (∑ q, P₀.mulVec (cPreFull.eval.1.mulVec (kIn (2 * q.val) (hEv q)))) = 0 :=
          Finset.sum_eq_zero fun q _ ↦ by
            dsimp only [P₀, cPreFull, kIn]
            rw [wShiftDummy_pre_act uLo w rDum wDum qEnc hInj d hd δ hr0 hw0 hwd0 hq0 _ _,
              hPre (hEv q), ite_eq_right (hev q), hu1,
              zero_add, ket_projector_zero, Function.update_self, ite_eq_right one_ne_zero]
        have hs1 : (∑ q, P₀.mulVec (cPreFull.eval.1.mulVec (kIn (2 * q.val + 1) (hOd q)))) = ∑ q,
          kOut q :=
          Finset.sum_congr rfl fun q _ ↦ by
            dsimp only [P₀, cPreFull, kIn, kOut]
            rw [wShiftDummy_pre_act uLo w rDum wDum qEnc hInj d hd δ hr0 hw0 hwd0 hq0 _ _,
              hPre (hOd q), ite_eq_left (hod q), hu1,
              CharTwo.add_self_eq_zero, ket_projector_zero, Function.update_self, ite_eq_left rfl,
                hqId]
            exact ketEq (by dsimp [idxValPrefix, lo]; rw [ite_eq_left hu1]; ring)
        rw [hs0, hs1, zero_add]
    · have hr1 : δ rDum = 1 := (hDumBit δ hP).trans (ite_eq_right hAct)
      rw [ite_eq_right hAct, ite_eq_right hAct,
        uDumShift_inact uLo w rDum wDum qEnc hInj d hd δ hr1 hwd0,
        wShiftDummy_pre_inact uLo w rDum wDum qEnc hInj d hd δ hr1 hw0 hwd0 hq0,
        Matrix.mulVec_smul, Matrix.mulVec_add]
      congr 1
      rcases bit_cases (δ (uLo ⟨d, hd⟩)) with hu0 | hu1
      · rw [hu0, add_zero, ket_projector_zero, Function.update_self, ite_eq_left rfl,
          ket_projector_zero, Function.update_self, ite_eq_right one_ne_zero, add_zero,
          update_eq_self_of_zero hq0, update_eq_self_of_zero hwd0]
      · have hq0w : Function.update δ wDum 1 qEnc = 0 :=
          (Function.update_of_ne hInj.wDum_ne_qEnc.symm 1 δ).trans hq0
        rw [hu1, CharTwo.add_self_eq_zero, ket_projector_zero, Function.update_self,
          ite_eq_right one_ne_zero, ket_projector_zero, Function.update_self, ite_eq_left rfl,
          zero_add, update_eq_self_of_zero hq0w]
  · simp only [ite_eq_right hV, Matrix.mulVec_zero, smul_zero]
attribute [local semireducible] projBit_dqmu
attribute [local irreducible] wShiftDummyFix wShiftDummyPre uDumShift barrelSwap
theorem wShiftDummy_branch1 {n R k : ℕ} (P activePred : BitAssignment n → Prop)
    [DecidablePred P] [DecidablePred activePred] (bStarFn : BitAssignment n → Fin R)
    (uLo : Fin k → Wire n) (w : Fin R → Fin (2 ^ k) → Wire n) (rDum wDum qEnc : Wire n)
    (hInj : WOptInj R k uLo w rDum wDum qEnc)
    (hDumBit : ∀ δ, P δ → δ rDum = (if activePred δ then 0 else 1)) (d : ℕ) (hd : d < k) :
    (wShiftDummyFix R k uLo w rDum wDum qEnc hInj d).eval.1 * (Circuit.X qEnc).eval.1 *
    (QRegister.singleton qEnc).basisOutcomeProjector 1 * ((wShiftDummyPre R k uLo w rDum wDum
    qEnc hInj d hd).eval.1 * wOptSuperOp P activePred bStarFn uLo w wDum qEnc d (Nat.le_of_lt
    hd)) = sqrtHalf • ((uDumShift uLo w rDum wDum qEnc hInj d hd).1 * wOptSuperOp P activePred
    bStarFn uLo w wDum qEnc (d + 1) hd) := by
  let F₁ := (wShiftDummyFix R k uLo w rDum wDum qEnc hInj d).eval.1 * (Circuit.X qEnc).eval.1 *
    (QRegister.singleton qEnc).basisOutcomeProjector 1
  let cPreFull := wShiftDummyPre R k uLo w rDum wDum qEnc hInj d hd
  let cFixFull := wShiftDummyFix R k uLo w rDum wDum qEnc hInj d
  let cB := barrelSwap R k w hInj.w_inj d
  let UDum := uDumShift uLo w rDum wDum qEnc hInj d hd
  have hev (q : Fin (2 ^ (k - (d + 1)))) : ¬ decide (2 * q.val % 2 = 1) = true := by
    simp only [decide_eq_true_eq]; omega
  have hod (q : Fin (2 ^ (k - (d + 1)))) : decide ((2 * q.val + 1) % 2 = 1) = true := by
    simp only [decide_eq_true_eq]; omega
  have hEv (q : Fin (2 ^ (k - (d + 1)))) : 2 * q.val < 2 ^ (k - d) := by
    have h : 2 ^ (k - d) = 2 * 2 ^ (k - (d + 1)) := by
      rw [show k - d = k - (d + 1) + 1 by omega, Nat.pow_succ]; ring
    have := q.isLt; omega
  have hOd (q : Fin (2 ^ (k - (d + 1)))) : 2 * q.val + 1 < 2 ^ (k - d) := by
    have h : 2 ^ (k - d) = 2 * 2 ^ (k - (d + 1)) := by
      rw [show k - d = k - (d + 1) + 1 by omega, Nat.pow_succ]; ring
    have := q.isLt; omega
  apply matrix_ext_ket; intro δ
  have hMulL (A B C : Operator (2 ^ n)) :
      (A * (B * C)).mulVec (ket δ) = A.mulVec (B.mulVec (C.mulVec (ket δ))) := by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  have hMulR (A B : Operator (2 ^ n)) :
      (sqrtHalf • (A * B)).mulVec (ket δ) = sqrtHalf • A.mulVec (B.mulVec (ket δ)) := by
    rw [Matrix.smul_mulVec, ← Matrix.mulVec_mulVec]
  rw [hMulL F₁ cPreFull.eval.1 _, hMulR UDum.1 _]
  simp only [wOptSuperOp, mkVecOp_mulVec_ket, wOptSuperVec]
  by_cases hV : P δ ∧ (∀ b p, δ (w b p) = 0) ∧ δ wDum = 0 ∧ δ qEnc = 0
  · have ⟨hP, hw0, hwd0, hq0⟩ := hV
    rw [ite_eq_left hV, ite_eq_left hV]
    by_cases hAct : activePred δ
    · have hr0 : δ rDum = 0 := (hDumBit δ hP).trans (ite_eq_left hAct)
      rw [ite_eq_left hAct, ite_eq_left hAct]
      dsimp only [wSuperVec]
      rw [ite_eq_left ⟨hw0, hq0⟩, ite_eq_left ⟨hw0, hq0⟩,
        Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.mulVec_smul,
        Matrix.mulVec_sum, Matrix.mulVec_sum, Matrix.mulVec_sum]
      have hkd : k - d = k - (d + 1) + 1 := by omega
      rw [show sqrtHalf ^ (k - d) = sqrtHalf * sqrtHalf ^ (k - (d + 1)) by
        rw [hkd, _root_.pow_succ'], smul_smul]
      congr 1
      have hRhs : (∑ hi : Fin (2 ^ (k - (d + 1))), UDum.1.mulVec (ket (Function.update δ (w
          (bStarFn δ) ⟨idxValPrefix uLo δ (d + 1) hd + 2 ^ (d + 1) * hi.val, shift_pos_lt hd
          (idxValPrefix_lt_two_pow uLo δ (d + 1) hd) hi.isLt⟩) 1))) = ∑ hi : Fin
          (2 ^ (k - (d + 1))), ket (Function.update δ (w (bStarFn δ) ⟨idxValPrefix uLo δ (d +
          1) hd + 2 ^ (d + 1) * hi.val, shift_pos_lt hd (idxValPrefix_lt_two_pow uLo δ (d + 1)
          hd) hi.isLt⟩) 1) := Finset.sum_congr rfl fun _ _ ↦ uDumShift_act uLo w rDum wDum
          qEnc hInj d hd δ hr0 hwd0 _ _
      rw [hRhs]
      let e : Fin (2 ^ (k - (d + 1))) ⊕ Fin (2 ^ (k - (d + 1))) ≃ Fin (2 ^ (k - d)) :=
        (finTwoMulEquiv (2 ^ (k - (d + 1)))).trans (finCongr (by rw [hkd, Nat.pow_succ]; ring))
      rw [← e.sum_comp, Fintype.sum_sum_type]
      let lo := idxValPrefix uLo δ d (Nat.le_of_lt hd)
      have hlo : lo < 2 ^ d := idxValPrefix_lt_two_pow uLo δ d (Nat.le_of_lt hd)
      let kIn (hi : ℕ) (hhi : hi < 2 ^ (k - d)) := ket (Function.update δ (w (bStarFn δ) ⟨lo +
          2 ^ d * hi, shift_pos_lt (Nat.le_of_lt hd) hlo hhi⟩) 1)
      let kOut (q : Fin (2 ^ (k - (d + 1)))) := ket (Function.update δ (w (bStarFn δ)
          ⟨idxValPrefix uLo δ (d + 1) hd + 2 ^ (d + 1) * q.val, shift_pos_lt hd
          (idxValPrefix_lt_two_pow uLo δ (d + 1) hd) q.isLt⟩) 1)
      change (∑ q : Fin (2 ^ (k - (d + 1))), F₁.mulVec (cPreFull.eval.1.mulVec (kIn (2 * q.val) (hEv
        q)))) +
        (∑ q : Fin (2 ^ (k - (d + 1))), F₁.mulVec (cPreFull.eval.1.mulVec (kIn (2 * q.val +
          1) (hOd q)))) =
        ∑ q : Fin (2 ^ (k - (d + 1))), kOut q
      have hPre {hi : ℕ} (hhi : hi < 2 ^ (k - d)) :=
        cnotOddAndIdx_mulVec_ket uLo w qEnc hInj.w_inj hInj.w_ne_qEnc hInj.uLo_ne_qEnc
          hInj.uLo_ne_w d hd δ hw0 hq0 (bStarFn δ) hhi
      have hqId (p : Fin (2 ^ k)) : Function.update (Function.update δ (w (bStarFn δ) p) 1)
          qEnc 0 = Function.update δ (w (bStarFn δ) p) 1 := update_eq_self_of_zero
          ((Function.update_of_ne (hInj.w_ne_qEnc _ _).symm 1 δ).trans hq0)
      have ketEq {a b : ℕ} {ha : a < 2 ^ k} {hb : b < 2 ^ k} (h : a = b) :
          ket (Function.update δ (w (bStarFn δ) ⟨a, ha⟩) 1) =
            ket (Function.update δ (w (bStarFn δ) ⟨b, hb⟩) 1) :=
        congrArg (fun p ↦ ket (Function.update δ (w (bStarFn δ) p) 1)) (Fin.ext h)
      have hpLo (q : Fin (2 ^ (k - (d + 1)))) : lo + 2 ^ d * (2 * q.val) < 2 ^ k :=
        shift_pos_lt (Nat.le_of_lt hd) hlo (hEv q)
      have htbLo (q : Fin (2 ^ (k - (d + 1)))) : (lo + 2 ^ d * (2 * q.val)).testBit d = false := by
        rw [testBit_lo_add_mul_two_pow hlo]; simp only [decide_eq_false_iff_not]; omega
      have hpHi (q : Fin (2 ^ (k - (d + 1)))) : (lo + 2 ^ d * (2 * q.val)) + 2 ^ d < 2 ^ k := by
        have heq : (lo + 2 ^ d * (2 * q.val)) + 2 ^ d = lo + 2 ^ d * (2 * q.val + 1) := by ring
        rw [heq]; exact shift_pos_lt (Nat.le_of_lt hd) hlo (hOd q)
      have hFixEq (p : Fin (2 ^ k)) :
          cFixFull.eval.1.mulVec (ket (Function.update δ (w (bStarFn δ) p) 1)) =
            cB.eval.1.mulVec (ket (Function.update δ (w (bStarFn δ) p) 1)) := by
        change (wShiftDummyFix R k uLo w rDum wDum qEnc hInj d).eval.1.mulVec _ = _
        unfold wShiftDummyFix
        rw [eval_seq_mulVec,
          ket_CNOT_ctrl_zero _ ((Function.update_of_ne (hInj.w_ne_rDum _ p).symm 1 δ).trans hr0)]
      rcases bit_cases (δ (uLo ⟨d, hd⟩)) with hu0 | hu1
      · have hs0 : (∑ q, F₁.mulVec (cPreFull.eval.1.mulVec (kIn (2 * q.val) (hEv q)))) = 0 :=
          Finset.sum_eq_zero fun q _ ↦ by
            dsimp only [kIn]
            rw[← Matrix.mulVec_mulVec,
                wShiftDummy_pre_act uLo w rDum wDum qEnc hInj d hd δ hr0 hw0 hwd0 hq0 _ _,
                hPre (hEv q), ite_eq_right (hev q), hu0, add_zero, ket_projector_one,
                Function.update_self, ite_eq_right zero_ne_one, Matrix.mulVec_zero]
        have hs1 : (∑ q, F₁.mulVec (cPreFull.eval.1.mulVec (kIn (2 * q.val + 1) (hOd q)))) = ∑ q,
          kOut q :=
          Finset.sum_congr rfl fun q _ ↦ by
            dsimp only [kIn, kOut]
            rw[← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
                wShiftDummy_pre_act uLo w rDum wDum qEnc hInj d hd δ hr0 hw0 hwd0 hq0 _ _,
                hPre (hOd q), ite_eq_left (hod q), hu0, add_zero, ket_projector_one,
                Function.update_self, ite_eq_left rfl, ket_X, Function.update_self,
                CharTwo.add_self_eq_zero, Function.update_idem, hqId, hFixEq]
            have hFin1 : (⟨lo + 2 ^ d * (2 * q.val + 1), shift_pos_lt (Nat.le_of_lt hd) hlo (hOd
              q)⟩ :
                Fin (2 ^ k)) =
                if true then ⟨(lo + 2 ^ d * (2 * q.val)) + 2 ^ d, hpHi q⟩ else ⟨lo + 2 ^ d * (2 *
                  q.val), hpLo q⟩ := by
              rw [ite_eq_left rfl]; exact Fin.ext (by dsimp only; ring)
            rw [hFin1, barrelSwap_mulVec_ket_pair w hInj.w_inj d δ hw0 (bStarFn δ) (hpLo q) (htbLo
              q) (hpHi q) true]
            exact ketEq (by dsimp [idxValPrefix, lo]; rw [ite_eq_right (by rw [hu0]; decide)]; ring)
        rw [hs0, hs1, zero_add]
      · have hs1 : (∑ q, F₁.mulVec (cPreFull.eval.1.mulVec (kIn (2 * q.val) (hEv q)))) = ∑ q,
          kOut q :=
          Finset.sum_congr rfl fun q _ ↦ by
            dsimp only [kIn, kOut]
            rw[← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
                wShiftDummy_pre_act uLo w rDum wDum qEnc hInj d hd δ hr0 hw0 hwd0 hq0 _ _,
                hPre (hEv q), ite_eq_right (hev q), hu1, zero_add, ket_projector_one,
                Function.update_self, ite_eq_left rfl, ket_X, Function.update_self,
                CharTwo.add_self_eq_zero, Function.update_idem, hqId, hFixEq]
            have hFin0 : (⟨lo + 2 ^ d * (2 * q.val), hpLo q⟩ : Fin (2 ^ k)) =
                if false then ⟨(lo + 2 ^ d * (2 * q.val)) + 2 ^ d, hpHi q⟩ else ⟨lo + 2 ^ d * (2 *
                  q.val), hpLo q⟩ := rfl
            rw [hFin0, barrelSwap_mulVec_ket_pair w hInj.w_inj d δ hw0 (bStarFn δ) (hpLo q) (htbLo
              q) (hpHi q) false]
            exact ketEq (by dsimp [idxValPrefix, lo]; rw [ite_eq_left hu1]; ring)
        have hs0 : (∑ q, F₁.mulVec (cPreFull.eval.1.mulVec (kIn (2 * q.val + 1) (hOd q)))) = 0 :=
          Finset.sum_eq_zero fun q _ ↦ by
            dsimp only [kIn]
            rw [← Matrix.mulVec_mulVec,
              wShiftDummy_pre_act uLo w rDum wDum qEnc hInj d hd δ hr0 hw0 hwd0 hq0 _ _,
              hPre (hOd q), ite_eq_left (hod q), hu1,
              CharTwo.add_self_eq_zero, ket_projector_one, Function.update_self,
              ite_eq_right zero_ne_one, Matrix.mulVec_zero]
        rw [hs1, hs0, add_zero]
    · have hr1 : δ rDum = 1 := (hDumBit δ hP).trans (ite_eq_right hAct)
      rw[ite_eq_right hAct, ite_eq_right hAct, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
          uDumShift_inact uLo w rDum wDum qEnc hInj d hd δ hr1 hwd0,
          wShiftDummy_pre_inact uLo w rDum wDum qEnc hInj d hd δ hr1 hw0 hwd0 hq0,
          Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.mulVec_add,
          Matrix.mulVec_add, Matrix.mulVec_add]
      congr 1
      rcases bit_cases (δ (uLo ⟨d, hd⟩)) with hu0 | hu1
      · have hq0w : Function.update δ wDum 1 qEnc = 0 :=
          (Function.update_of_ne hInj.wDum_ne_qEnc.symm 1 δ).trans hq0
        rw[hu0, add_zero, ket_projector_one, Function.update_self, ite_eq_right zero_ne_one,
            Matrix.mulVec_zero, Matrix.mulVec_zero, zero_add, ket_projector_one,
            Function.update_self, ite_eq_left rfl, ket_X, Function.update_self,
            CharTwo.add_self_eq_zero, Function.update_idem, update_eq_self_of_zero hq0w]
        unfold wShiftDummyFix; rw [eval_seq_mulVec, ket_CNOT, Function.update_self,
          Function.update_of_ne hInj.rDum_ne_wDum, hr1, CharTwo.add_self_eq_zero,
          Function.update_idem, update_eq_self_of_zero hwd0,
          barrelSwap_mulVec_ket_zero w hInj.w_inj d δ hw0]
      · rw[hu1, CharTwo.add_self_eq_zero, ket_projector_one, Function.update_self,
          ite_eq_left rfl, ket_projector_one, Function.update_self, ite_eq_right zero_ne_one,
          Matrix.mulVec_zero, Matrix.mulVec_zero, add_zero, ket_X, Function.update_self,
          CharTwo.add_self_eq_zero, Function.update_idem, update_eq_self_of_zero hq0]
        unfold wShiftDummyFix; rw [eval_seq_mulVec, ket_CNOT, hr1, hwd0, zero_add]
        exact barrelSwap_mulVec_ket_zero w hInj.w_inj d (Function.update δ wDum 1)
          fun b p ↦ (Function.update_of_ne (hInj.w_ne_wDum b p) 1 δ).trans (hw0 b p)
  · simp only [ite_eq_right hV, Matrix.mulVec_zero, smul_zero]
theorem subspaceStep_wShiftDummyLevel {Var : Type} [Fintype Var] [DecidableEq Var] {n R k : ℕ}
    (v : Var) (P activePred : BitAssignment n → Prop) [DecidablePred P]
    [DecidablePred activePred] (bStarFn : BitAssignment n → Fin R) (uLo : Fin k → Wire n)
    (w : Fin R → Fin (2 ^ k) → Wire n) (rDum wDum qEnc : Wire n)
    (hInj : WOptInj R k uLo w rDum wDum qEnc)
    (hDumBit : ∀ δ, P δ → δ rDum = (if activePred δ then 0 else 1)) (d : ℕ) (hd : d < k) :
    SubspaceStep (wOptSuperOp P activePred bStarFn uLo w wDum qEnc d (Nat.le_of_lt hd))
    (wOptSuperOp P activePred bStarFn uLo w wDum qEnc (d + 1) hd)
    (wShiftDummyLevel v R k uLo w rDum wDum qEnc hInj d hd) := by
  let pairs : List (WirePair n) := [⟨rDum, ⟨uLo ⟨d, hd⟩, (hInj.uLo_ne_rDum ⟨d, hd⟩).symm⟩⟩]
  let R_in := wOptSuperOp P activePred bStarFn uLo w wDum qEnc d (Nat.le_of_lt hd)
  let R_out := wOptSuperOp P activePred bStarFn uLo w wDum qEnc (d + 1) hd
  let UDum := uDumShift uLo w rDum wDum qEnc hInj d hd
  have hProjWDum0 : projBit_dqmu wDum 0 * R_out = R_out := by
    apply matrix_ext_ket; intro δ
    simp only [← Matrix.mulVec_mulVec, R_out, wOptSuperOp, mkVecOp_mulVec_ket, wOptSuperVec]
    by_cases hV : P δ ∧ (∀ b p, δ (w b p) = 0) ∧ δ wDum = 0 ∧ δ qEnc = 0
    · have ⟨_, hw0, hwd0, hq0⟩ := hV
      rw [ite_eq_left hV]
      by_cases hAct : activePred δ
      · rw [ite_eq_left hAct]
        dsimp only [wSuperVec]; rw [ite_eq_left ⟨hw0, hq0⟩, Matrix.mulVec_smul, Matrix.mulVec_sum]
        congr 1; refine Finset.sum_congr rfl fun hi _ ↦ ?_
        rw [projBit_zero_mulVec_ket,
          ite_eq_left ((Function.update_of_ne (hInj.w_ne_wDum _ _).symm 1 δ).trans hwd0)]
      · rw [ite_eq_right hAct, projBit_zero_mulVec_ket, ite_eq_left hwd0]
    · rw [ite_eq_right hV, Matrix.mulVec_zero]
  have hUnload : SubspaceStep (UDum.1 * R_out) R_out
      (xUnloadCzPairsSeqDyn v wDum pairs (.circuit .identity)) := by
    dsimp only [UDum]; unfold uDumShift
    exact subspaceStep_xUnloadCzPairsSeqDyn v wDum pairs (.circuit .identity)
      (czPairsParity pairs) (fDum_indep uLo rDum wDum qEnc hInj d hd) (fun _ ↦ rfl)
      R_out R_out hProjWDum0
      (by simpa only [Circuit.eval_identity, Submonoid.coe_one, Matrix.one_mul] using
        subspaceStep_of_circuit (Var := Var) R_out (.identity : Circuit n))
  have hShift : SubspaceStep R_in (UDum.1 * R_out) (.seq (.circuit (wShiftDummyPre R k uLo w
      rDum wDum qEnc hInj d hd)) (zResetFixupDyn v qEnc (wShiftDummyFix R k uLo w rDum wDum
      qEnc hInj d))) := subspaceStep_seq_zResetFixup v qEnc _ (subspaceStep_of_circuit R_in _)
      (wShiftDummy_branch0 P activePred bStarFn uLo w rDum wDum qEnc hInj hDumBit d hd)
      (wShiftDummy_branch1 P activePred bStarFn uLo w rDum wDum qEnc hInj hDumBit d hd)
  dsimp only [wShiftDummyLevel]
  exact hShift.seq hUnload
attribute [local semireducible] projBit_dqmu
theorem qUp_ne_of_ne_opt {n R k : ℕ} {w : Fin R → Fin (2 ^ k) → Wire n} (hw : WInj w)
    {r : ℕ} (hr : r < k) {i₁ i₂ : ℕ} (hi₁ : i₁ < R * 2 ^ r) (hi₂ : i₂ < R * 2 ^ r)
    (hne : i₁ ≠ i₂) : qUp R k w r hr i₁ hi₁ ≠ qUp R k w r hr i₂ hi₂ := fun e ↦ by
  obtain ⟨hb, hp⟩ := hw _ _ _ _ e
  have hdiv : i₁ / 2 ^ r = i₂ / 2 ^ r := congrArg Fin.val hb
  have hmod : i₁ % 2 ^ r + 2 ^ r = i₂ % 2 ^ r + 2 ^ r := congrArg Fin.val hp
  have hmod' : i₁ % 2 ^ r = i₂ % 2 ^ r := by omega
  have hd₁ := Nat.div_add_mod i₁ (2 ^ r)
  have hd₂ := Nat.div_add_mod i₂ (2 ^ r)
  rw [hdiv, hmod'] at hd₁
  exact hne (hd₁.symm.trans hd₂)
def fPairOpt {n : ℕ} (R k : ℕ) (uLo : Fin k → Wire n) (w : Fin R → Fin (2 ^ k) → Wire n)
    (huw : ∀ d b p, uLo d ≠ w b p) (r : ℕ) (hr : r < k) (i : ℕ) (hi : i < R * 2 ^ r)
    (β : BitAssignment n) : ZMod 2 := czPairsParity (pairOf R k uLo w huw r hr i hi) β
theorem fPairOpt_indep {n : ℕ} (R k : ℕ) (uLo : Fin k → Wire n)
    (w : Fin R → Fin (2 ^ k) → Wire n) (hw : WInj w) (huw : ∀ d b p, uLo d ≠ w b p)
    (r : ℕ) (hr : r < k) (i : ℕ) (hi : i < R * 2 ^ r) (β : BitAssignment n) (a : ZMod 2) :
    fPairOpt R k uLo w huw r hr i hi (Function.update β (qUp R k w r hr i hi) a) =
      fPairOpt R k uLo w huw r hr i hi β := by
  have huw' : uLo ⟨r, hr⟩ ≠ qUp R k w r hr i hi := huw ⟨r, hr⟩ _ _
  dsimp only [fPairOpt, pairOf, czPairsParity]
  rw [Function.update_of_ne (qLo_ne_qUp hw hr hi hi), Function.update_of_ne huw']
def upperXorBitsOpt {n : ℕ} (R k : ℕ) (uLo : Fin k → Wire n)
    (w : Fin R → Fin (2 ^ k) → Wire n) (huw : ∀ d b p, uLo d ≠ w b p)
    (r : ℕ) (hr : r < k) : (m : ℕ) → m ≤ R * 2 ^ r → BitAssignment n → BitAssignment n
  | 0, _, β => β
  | m + 1, hm, β =>
      let β' := upperXorBitsOpt R k uLo w huw r hr m (Nat.le_of_succ_le hm) β
      Function.update β' (qUp R k w r hr m hm)
        (β' (qUp R k w r hr m hm) + fPairOpt R k uLo w huw r hr m hm β')
theorem upperXorBitsOpt_of_ne {n : ℕ} (R k : ℕ) (uLo : Fin k → Wire n)
    (w : Fin R → Fin (2 ^ k) → Wire n) (huw : ∀ d b p, uLo d ≠ w b p)
    (r : ℕ) (hr : r < k) (β : BitAssignment n) (u : Wire n) :
    ∀ (m : ℕ) (hm : m ≤ R * 2 ^ r),
      (∀ i (hi : i < m), u ≠ qUp R k w r hr i (Nat.lt_of_lt_of_le hi hm)) →
      upperXorBitsOpt R k uLo w huw r hr m hm β u = β u
  | 0, _, _ => rfl
  | m + 1, hm, hne => by
      dsimp only [upperXorBitsOpt]
      rw [Function.update_of_ne (hne m (Nat.lt_succ_self m)),
        upperXorBitsOpt_of_ne R k uLo w huw r hr β u m (Nat.le_of_succ_le hm)
          (fun i hi ↦ hne i (Nat.lt_succ_of_lt hi))]
theorem upperXorBitsOpt_qUp_lt {n : ℕ} (R k : ℕ) (uLo : Fin k → Wire n)
    (w : Fin R → Fin (2 ^ k) → Wire n) (hw : WInj w) (huw : ∀ d b p, uLo d ≠ w b p)
    (r : ℕ) (hr : r < k) (β : BitAssignment n) :
    ∀ (m : ℕ) (hm : m ≤ R * 2 ^ r) (i : ℕ) (hi : i < m),
      let hiR := Nat.lt_of_lt_of_le hi hm
      upperXorBitsOpt R k uLo w huw r hr m hm β (qUp R k w r hr i hiR) =
        β (qUp R k w r hr i hiR) + β (qLo R k w r hr i hiR) * β (uLo ⟨r, hr⟩)
  | 0, _, _, hi => absurd hi (Nat.not_lt_zero _)
  | m + 1, hm, i, hi => by
      dsimp only [upperXorBitsOpt]
      by_cases him : i = m
      · subst him
        rw [Function.update_self]
        have hUp := upperXorBitsOpt_of_ne R k uLo w huw r hr β (qUp R k w r hr i hm) i
          (Nat.le_of_succ_le hm) (fun j hj ↦ qUp_ne_of_ne_opt hw hr hm _ (Nat.ne_of_gt hj))
        have hLo := upperXorBitsOpt_of_ne R k uLo w huw r hr β (qLo R k w r hr i hm) i
          (Nat.le_of_succ_le hm) (fun _ _ ↦ qLo_ne_qUp hw hr hm _)
        have hIdx := upperXorBitsOpt_of_ne R k uLo w huw r hr β (uLo ⟨r, hr⟩) i
          (Nat.le_of_succ_le hm) (fun _ _ ↦ huw ⟨r, hr⟩ _ _)
        dsimp only [fPairOpt, pairOf, czPairsParity]
        rw [hUp, hLo, hIdx, add_zero]
      · have hilt : i < m := by omega
        rw [Function.update_of_ne (qUp_ne_of_ne_opt hw hr _ hm him),
          upperXorBitsOpt_qUp_lt R k uLo w hw huw r hr β m (Nat.le_of_succ_le hm) i hilt]
def uUpperXorPrefixOpt {n : ℕ} (R k : ℕ) (uLo : Fin k → Wire n)
    (w : Fin R → Fin (2 ^ k) → Wire n) (hw : WInj w) (huw : ∀ d b p, uLo d ≠ w b p)
    (r : ℕ) (hr : r < k) : (m : ℕ) → m ≤ R * 2 ^ r → Operator (2 ^ n)
  | 0, _ => 1
  | m + 1, hm =>
      (xorWireUnitary (qUp R k w r hr m hm) (fPairOpt R k uLo w huw r hr m hm)
        (fPairOpt_indep R k uLo w hw huw r hr m hm)).1 *
      uUpperXorPrefixOpt R k uLo w hw huw r hr m (Nat.le_of_succ_le hm)
theorem uUpperXorPrefixOpt_mulVec_ket {n : ℕ} (R k : ℕ) (uLo : Fin k → Wire n)
    (w : Fin R → Fin (2 ^ k) → Wire n) (hw : WInj w) (huw : ∀ d b p, uLo d ≠ w b p)
    (r : ℕ) (hr : r < k) (β : BitAssignment n) :
    ∀ (m : ℕ) (hm : m ≤ R * 2 ^ r),
      (uUpperXorPrefixOpt R k uLo w hw huw r hr m hm).mulVec (ket β) =
        ket (upperXorBitsOpt R k uLo w huw r hr m hm β)
  | 0, _ => Matrix.one_mulVec _
  | m + 1, hm => by
      rw [uUpperXorPrefixOpt, ← Matrix.mulVec_mulVec,
        uUpperXorPrefixOpt_mulVec_ket R k uLo w hw huw r hr β m (Nat.le_of_succ_le hm),
        xorWireUnitary_mulVec_ket]
      rfl
theorem count_wUncompMeasPrefix_opt {Var : Type} {n : ℕ} (v : Var) (R k : ℕ)
    (uLo : Fin k → Wire n) (w : Fin R → Fin (2 ^ k) → Wire n) (huw : ∀ d b p, uLo d ≠ w b p)
    (r : ℕ) (hr : r < k) (rest : DynamicCircuit Var n) :
    ∀ (m : ℕ) (hm : m ≤ R * 2 ^ r),
      (wUncompMeasPrefix v R k uLo w huw r hr rest m hm).count .T = rest.count .T ∧
      (wUncompMeasPrefix v R k uLo w huw r hr rest m hm).count .TOFF = rest.count .TOFF
  | 0, _ => ⟨rfl, rfl⟩
  | m + 1, hm => by
      obtain ⟨ht, hf⟩ := count_wUncompMeasPrefix_opt v R k uLo w huw r hr rest m (Nat.le_of_succ_le
        hm)
      obtain ⟨xt, xf⟩ := count_xUnloadCzPairsSeqDyn v (qUp R k w r hr m hm)
        (pairOf R k uLo w huw r hr m hm)
        (wUncompMeasPrefix v R k uLo w huw r hr rest m (Nat.le_of_succ_le hm))
      dsimp only [wUncompMeasPrefix]
      exact ⟨xt.trans ht, xf.trans hf⟩
theorem count_wUncompRoundDyn_opt {Var : Type} {n : ℕ} (v : Var) (R k : ℕ)
    (uLo : Fin k → Wire n) (w : Fin R → Fin (2 ^ k) → Wire n) (hw : WInj w)
    (huw : ∀ d b p, uLo d ≠ w b p) (r : ℕ) (hr : r < k) (rest : DynamicCircuit Var n) :
    (wUncompRoundDyn v R k uLo w hw huw r hr rest).count .T = rest.count .T ∧
    (wUncompRoundDyn v R k uLo w hw huw r hr rest).count .TOFF = rest.count .TOFF := by
  obtain ⟨mt, mf⟩ := count_wUncompMeasPrefix_opt v R k uLo w huw r hr rest (R * 2 ^ r) le_rfl
  have hct : (wUncompCnotRound R k w hw r hr).count .T = 0 := by
    rw [wUncompCnotRound, count_seqNat_T 0 (R * 2 ^ r) _ (fun _ _ ↦ by simp [Circuit.CNOT]),
      Nat.mul_zero]
  have hcf : (wUncompCnotRound R k w hw r hr).count .TOFF = 0 :=
    count_seqNat_TOFF_zero (R * 2 ^ r) _ (fun _ _ ↦ by simp [Circuit.CNOT])
  dsimp only [wUncompRoundDyn, DynamicCircuit.count]
  rw [hct, hcf, mt, mf, Nat.zero_add, Nat.zero_add]
  exact ⟨rfl, rfl⟩
theorem count_wUncompTreeDyn_opt {Var : Type} {n : ℕ} (v : Var) (R k : ℕ)
    (uLo : Fin k → Wire n) (w : Fin R → Fin (2 ^ k) → Wire n)
    (hw : WInj w) (huw : ∀ d b p, uLo d ≠ w b p) (rest : DynamicCircuit Var n) :
    ∀ (m : ℕ) (hm : m ≤ k),
      (wUncompTreeDyn v R k uLo w hw huw rest m hm).count .T = rest.count .T ∧
      (wUncompTreeDyn v R k uLo w hw huw rest m hm).count .TOFF = rest.count .TOFF
  | 0, _ => ⟨rfl, rfl⟩
  | r + 1, hr => by
      obtain ⟨ht, hf⟩ := count_wUncompTreeDyn_opt v R k uLo w hw huw rest r (Nat.le_of_succ_le hr)
      obtain ⟨rt, rf⟩ := count_wUncompRoundDyn_opt v R k uLo w hw huw r hr
        (wUncompTreeDyn v R k uLo w hw huw rest r (Nat.le_of_succ_le hr))
      dsimp only [wUncompTreeDyn]
      exact ⟨rt.trans ht, rf.trans hf⟩
/-- Optional pre-shift one-hot vector at tree level `m ≤ k` (`1`-hot on `activePred`, `ket δ`
otherwise). -/
def oneHotOptPreVec {n R k : ℕ} (P activePred : BitAssignment n → Prop) [DecidablePred P]
    [DecidablePred activePred] (bStarFn : BitAssignment n → Fin R) (uLo : Fin k → Wire n)
    (w : Fin R → Fin (2 ^ k) → Wire n) (δ : BitAssignment n) (m : ℕ) (hm : m ≤ k) : Fin
    (2 ^ n) → ℂ := if P δ ∧ ∀ b p, δ (w b p) = 0 then if activePred δ then ket
    (Function.update δ (w (bStarFn δ) ⟨idxValPrefix uLo δ m hm, Nat.lt_of_lt_of_le
    (idxValPrefix_lt_two_pow uLo δ m hm) (Nat.pow_le_pow_right (by omega) hm)⟩) 1) else ket δ
    else 0
/-- Operator mapping computational basis kets via `oneHotOptPreVec`. -/
def oneHotOptPreOp {n R k : ℕ} (P activePred : BitAssignment n → Prop) [DecidablePred P]
    [DecidablePred activePred] (bStarFn : BitAssignment n → Fin R) (uLo : Fin k → Wire n)
    (w : Fin R → Fin (2 ^ k) → Wire n) (m : ℕ) (hm : m ≤ k) : Operator (2 ^ n) := mkVecOp fun
    δ ↦ oneHotOptPreVec P activePred bStarFn uLo w δ m hm
theorem upperXorBitsOpt_all_zero {n : ℕ} (R k : ℕ) (uLo : Fin k → Wire n)
    (w : Fin R → Fin (2 ^ k) → Wire n) (huw : ∀ d b p, uLo d ≠ w b p)
    (r : ℕ) (hr : r < k) (δ : BitAssignment n) (hw0 : ∀ b p, δ (w b p) = 0) :
    ∀ (m : ℕ) (hm : m ≤ R * 2 ^ r), upperXorBitsOpt R k uLo w huw r hr m hm δ = δ
  | 0, _ => rfl
  | m + 1, hm => by
      dsimp only [upperXorBitsOpt]
      rw [upperXorBitsOpt_all_zero R k uLo w huw r hr δ hw0 m (Nat.le_of_succ_le hm)]
      have hLo0 : δ (qLo R k w r hr m hm) = 0 := hw0 _ _
      have hUp0 : δ (qUp R k w r hr m hm) = 0 := hw0 _ _
      have h0 : fPairOpt R k uLo w huw r hr m hm δ = 0 := by
        dsimp only [fPairOpt, pairOf, czPairsParity]; rw [hLo0, zero_mul, add_zero]
      rw [h0, hUp0, add_zero, update_eq_self_of_zero hUp0]
attribute [local semireducible] projBit_dqmu
theorem projBit_zero_uUpperXorPrefixOpt {n R k : ℕ} (P activePred : BitAssignment n → Prop)
    [DecidablePred P] [DecidablePred activePred] (bStarFn : BitAssignment n → Fin R)
    (uLo : Fin k → Wire n) (w : Fin R → Fin (2 ^ k) → Wire n) (hw : WInj w)
    (huw : ∀ d b p, uLo d ≠ w b p) (r : ℕ) (hr : r < k) (m : ℕ) (hm : m < R * 2 ^ r) :
    projBit_dqmu (qUp R k w r hr m hm) 0 * (uUpperXorPrefixOpt R k uLo w hw huw r hr m
    (Nat.le_of_succ_le hm) * oneHotOptPreOp P activePred bStarFn uLo w r (Nat.le_of_lt hr)) =
    uUpperXorPrefixOpt R k uLo w hw huw r hr m (Nat.le_of_succ_le hm) * oneHotOptPreOp P
    activePred bStarFn uLo w r (Nat.le_of_lt hr) := by
  apply matrix_ext_ket; intro δ
  simp only [← Matrix.mulVec_mulVec, oneHotOptPreOp, mkVecOp_mulVec_ket, oneHotOptPreVec]
  by_cases hV : P δ ∧ ∀ b p, δ (w b p) = 0
  · rw [ite_eq_left hV]
    by_cases hAct : activePred δ
    · rw [ite_eq_left hAct, uUpperXorPrefixOpt_mulVec_ket, projBit_zero_mulVec_ket]
      let pLo : Fin (2 ^ k) := ⟨idxValPrefix uLo δ r (Nat.le_of_lt hr),
        Nat.lt_of_lt_of_le (idxValPrefix_lt_two_pow uLo δ r (Nat.le_of_lt hr))
          (Nat.pow_le_pow_right (by omega) (Nat.le_of_lt hr))⟩
      have hneLo : w (bStarFn δ) pLo ≠ qUp R k w r hr m hm :=
        w_ne_of_pair_ne hw (Or.inr fun e ↦ by
          have hv := congrArg Fin.val e
          have hs := idxValPrefix_lt_two_pow uLo δ r (Nat.le_of_lt hr)
          dsimp [pLo, qUp] at hv; omega)
      have hq0 : upperXorBitsOpt R k uLo w huw r hr m (Nat.le_of_succ_le hm)
          (Function.update δ (w (bStarFn δ) pLo) 1) (qUp R k w r hr m hm) = 0 := by
        rw [upperXorBitsOpt_of_ne R k uLo w huw r hr _ _ m (Nat.le_of_succ_le hm)
          (fun i hi ↦ qUp_ne_of_ne_opt hw hr hm _ (Nat.ne_of_gt hi)),
          Function.update_of_ne hneLo.symm]
        exact hV.2 _ _
      rw [ite_eq_left hq0]
    · have hUp0 : δ (qUp R k w r hr m hm) = 0 := hV.2 _ _
      rw [ite_eq_right hAct, uUpperXorPrefixOpt_mulVec_ket,
        upperXorBitsOpt_all_zero R k uLo w huw r hr δ hV.2 m (Nat.le_of_succ_le hm),
        projBit_zero_mulVec_ket, ite_eq_left hUp0]
  · rw [ite_eq_right hV, Matrix.mulVec_zero, Matrix.mulVec_zero]
theorem subspaceStep_wUncompMeasPrefix_opt {Var : Type} [Fintype Var] [DecidableEq Var]
    {n R k : ℕ} (v : Var) (P activePred : BitAssignment n → Prop)
    [DecidablePred P] [DecidablePred activePred]
    (bStarFn : BitAssignment n → Fin R) (uLo : Fin k → Wire n)
    (w : Fin R → Fin (2 ^ k) → Wire n) (hw : WInj w) (huw : ∀ d b p, uLo d ≠ w b p)
    (r : ℕ) (hr : r < k) {rest : DynamicCircuit Var n} {R_out : Operator (2 ^ n)}
    (hRest : SubspaceStep (oneHotOptPreOp P activePred bStarFn uLo w r (Nat.le_of_lt hr)) R_out
      rest) :
    ∀ (m : ℕ) (hm : m ≤ R * 2 ^ r),
      SubspaceStep
        (uUpperXorPrefixOpt R k uLo w hw huw r hr m hm *
          oneHotOptPreOp P activePred bStarFn uLo w r (Nat.le_of_lt hr))
        R_out
        (wUncompMeasPrefix v R k uLo w huw r hr rest m hm)
  | 0, _ => by simpa only [uUpperXorPrefixOpt, Matrix.one_mul, wUncompMeasPrefix] using hRest
  | m + 1, hm => by
      dsimp only [uUpperXorPrefixOpt, wUncompMeasPrefix]
      rw [Matrix.mul_assoc]
      exact subspaceStep_xUnloadCzPairsSeqDyn v (qUp R k w r hr m hm)
        (pairOf R k uLo w huw r hr m hm) (wUncompMeasPrefix v R k uLo w huw r hr rest m
        (Nat.le_of_succ_le hm)) (fPairOpt R k uLo w huw r hr m hm)
        (fPairOpt_indep R k uLo w hw huw r hr m hm) (fun _ ↦ rfl) (uUpperXorPrefixOpt R k uLo
        w hw huw r hr m (Nat.le_of_succ_le hm) * oneHotOptPreOp P activePred bStarFn uLo w r
        (Nat.le_of_lt hr)) R_out (projBit_zero_uUpperXorPrefixOpt P activePred bStarFn uLo w
        hw huw r hr m hm) (subspaceStep_wUncompMeasPrefix_opt v P activePred bStarFn uLo w hw
        huw r hr hRest m (Nat.le_of_succ_le hm))
theorem wUncompCnotRound_mul_oneHotOptPreOp {n R k : ℕ}
    (P activePred : BitAssignment n → Prop) [DecidablePred P] [DecidablePred activePred]
    (bStarFn : BitAssignment n → Fin R) (uLo : Fin k → Wire n)
    (w : Fin R → Fin (2 ^ k) → Wire n) (hw : WInj w) (huw : ∀ d b p, uLo d ≠ w b p) (r : ℕ)
    (hr : r < k) : (wUncompCnotRound R k w hw r hr).eval.1 * oneHotOptPreOp P activePred
    bStarFn uLo w (r + 1) hr = uUpperXorPrefixOpt R k uLo w hw huw r hr (R * 2 ^ r) le_rfl *
    oneHotOptPreOp P activePred bStarFn uLo w r (Nat.le_of_lt hr) := by
  apply matrix_ext_ket; intro δ
  simp only [← Matrix.mulVec_mulVec, oneHotOptPreOp, mkVecOp_mulVec_ket, oneHotOptPreVec]
  by_cases hV : P δ ∧ ∀ b p, δ (w b p) = 0
  · have hw0 := hV.2
    rw [ite_eq_left hV, ite_eq_left hV]
    by_cases hAct : activePred δ
    · rw [ite_eq_left hAct, ite_eq_left hAct, uUpperXorPrefixOpt_mulVec_ket]
      let bStar := bStarFn δ
      let sLo := idxValPrefix uLo δ r (Nat.le_of_lt hr)
      have hsLo : sLo < 2 ^ r := idxValPrefix_lt_two_pow uLo δ r (Nat.le_of_lt hr)
      let pLo : Fin (2 ^ k) := ⟨sLo, pair_lo_lt hr hsLo⟩
      let pHi : Fin (2 ^ k) := ⟨sLo + 2 ^ r, pair_hi_lt hr hsLo⟩
      let δMid := Function.update δ (w bStar pLo) 1
      let δAfter := Function.update δMid (w bStar pHi) (δ (uLo ⟨r, hr⟩))
      let i₀ := bStar.val * 2 ^ r + sLo
      obtain ⟨hi₀, hdiv₀, hmod₀⟩ := enc_div_mod bStar.isLt hsLo
      have hqUp₀ : qUp R k w r hr i₀ hi₀ = w bStar pHi := by
        dsimp only [qUp]
        exact congrArg₂ w (Fin.ext hdiv₀) (Fin.ext (by dsimp [pHi]; rw [hmod₀]))
      have hqLo₀ : qLo R k w r hr i₀ hi₀ = w bStar pLo := by
        dsimp only [qLo]
        exact congrArg₂ w (Fin.ext hdiv₀) (Fin.ext hmod₀)
      have hMidUp0 (i : ℕ) (hi : i < R * 2 ^ r) : δMid (qUp R k w r hr i hi) = 0 := by
        have hne : qUp R k w r hr i hi ≠ w bStar pLo :=
          w_ne_of_pair_ne hw (Or.inr fun e ↦ by
            have hv := congrArg Fin.val e; dsimp [pLo] at hv; omega)
        exact (Function.update_of_ne hne 1 δ).trans (hw0 _ _)
      have hneLoHi : w bStar pLo ≠ w bStar pHi :=
        w_ne_of_pair_ne hw (Or.inr fun e ↦ by
          have hv := congrArg Fin.val e; dsimp [pLo, pHi] at hv; omega)
      have hLHS : (wUncompCnotRound R k w hw r hr).eval.1.mulVec (ket (Function.update δ (w
          bStar ⟨idxValPrefix uLo δ (r + 1) hr, Nat.lt_of_lt_of_le (idxValPrefix_lt_two_pow
          uLo δ (r + 1) hr) (Nat.pow_le_pow_right (by omega) hr)⟩) 1)) = ket δAfter := by
        let fGate (i : ℕ) (hi : i < R * 2 ^ r) :=
          Circuit.CNOT (qUp R k w r hr i hi) (qLo R k w r hr i hi) (qLo_ne_qUp hw hr hi hi).symm
        dsimp only [wUncompCnotRound]
        rcases bit_cases (δ (uLo ⟨r, hr⟩)) with hu0 | hu1
        · have hpEq : (⟨idxValPrefix uLo δ (r + 1) hr,
              Nat.lt_of_lt_of_le (idxValPrefix_lt_two_pow uLo δ (r + 1) hr)
                (Nat.pow_le_pow_right (by omega) hr)⟩ : Fin (2 ^ k)) = pLo :=
            Fin.ext (by
              dsimp [idxValPrefix, pLo, sLo]; rw [ite_eq_right (by rw [hu0]; decide)]; omega)
          have hMidHi0 : δMid (w bStar pHi) = 0 :=
            (Function.update_of_ne hneLoHi.symm 1 δ).trans (hw0 bStar pHi)
          have hAfterEq : δAfter = δMid := by
            dsimp only [δAfter]; rw [hu0]; exact update_eq_self_of_zero hMidHi0
          rw [hpEq, hAfterEq]
          exact seqNat_mulVec_fixed (ket δMid) (R * 2 ^ r) fGate fun i hi ↦
            ket_CNOT_ctrl_zero _ (hMidUp0 i hi)
        · have hpEq : (⟨idxValPrefix uLo δ (r + 1) hr,
              Nat.lt_of_lt_of_le (idxValPrefix_lt_two_pow uLo δ (r + 1) hr)
                (Nat.pow_le_pow_right (by omega) hr)⟩ : Fin (2 ^ k)) = pHi :=
            Fin.ext (by dsimp [idxValPrefix, pHi, sLo]; rw [ite_eq_left hu1])
          rw [hpEq]
          have hSeq := seqNat_mulVec_single
            (ket (Function.update δ (w bStar pHi) 1))
            (ket δAfter) i₀ (R * 2 ^ r) fGate
            (fun i hi hlt ↦ by
              have hne : qUp R k w r hr i hi ≠ w bStar pHi := by
                rw [← hqUp₀]; exact qUp_ne_of_ne_opt hw hr hi hi₀ (Nat.ne_of_lt hlt)
              exact ket_CNOT_ctrl_zero _ ((Function.update_of_ne hne 1 δ).trans (hw0 _ _)))
            (fun hi₀' ↦ by
              have hqUpE : qUp R k w r hr i₀ hi₀' = w bStar pHi := hqUp₀
              have hqLoE : qLo R k w r hr i₀ hi₀' = w bStar pLo := hqLo₀
              dsimp only [fGate]
              rw [ket_CNOT, hqUpE, hqLoE, Function.update_of_ne hneLoHi, hw0 bStar pLo,
                Function.update_self, zero_add, Function.update_comm hneLoHi.symm]
              dsimp only [δAfter, δMid]; rw [hu1])
            (fun i hi hgt ↦ by
              have hne : qUp R k w r hr i hi ≠ w bStar pHi := by
                rw [← hqUp₀]; exact qUp_ne_of_ne_opt hw hr hi hi₀ (Nat.ne_of_gt hgt)
              exact ket_CNOT_ctrl_zero _
                ((Function.update_of_ne hne (δ (uLo ⟨r, hr⟩)) δMid).trans (hMidUp0 i hi)))
          rw [ite_eq_left hi₀] at hSeq; exact hSeq
      rw [hLHS]; congr 1; funext u
      by_cases hU : ∃ idx : Fin (R * 2 ^ r), u = qUp R k w r hr idx.val idx.isLt
      · obtain ⟨⟨i, hi⟩, rfl⟩ := hU
        have hBits := upperXorBitsOpt_qUp_lt R k uLo w hw huw r hr δMid (R * 2 ^ r) le_rfl i hi
        dsimp only at hBits
        have hMidIdx : δMid (uLo ⟨r, hr⟩) = δ (uLo ⟨r, hr⟩) :=
          Function.update_of_ne (huw ⟨r, hr⟩ _ _) 1 δ
        rw [show upperXorBitsOpt R k uLo w huw r hr (R * 2 ^ r) le_rfl δMid (qUp R k w r hr i hi) =
            δMid (qUp R k w r hr i hi) + δMid (qLo R k w r hr i hi) * δMid (uLo ⟨r, hr⟩) from hBits,
          hMidUp0 i hi, zero_add, hMidIdx]
        by_cases hii₀ : i = i₀
        · subst hii₀; dsimp only [δAfter, δMid]
          rw [hqUp₀, hqLo₀, Function.update_self, Function.update_self, one_mul]
        · have hneUp : qUp R k w r hr i hi ≠ w bStar pHi := by
            rw [← hqUp₀]; exact qUp_ne_of_ne_opt hw hr hi hi₀ hii₀
          have hneLo : qLo R k w r hr i hi ≠ w bStar pLo := by
            have hdisj := enc_ne_iff hii₀
            exact w_ne_of_pair_ne hw (by
              rcases hdisj with hdb | hdm
              · exact Or.inl fun e ↦ hdb (congrArg Fin.val e)
              · exact Or.inr fun e ↦ hdm (congrArg Fin.val e))
          have hLo0 : δ (qLo R k w r hr i hi) = 0 := hw0 _ _
          have hAfterUp0 : δAfter (qUp R k w r hr i hi) = 0 :=
            (Function.update_of_ne hneUp _ δMid).trans (hMidUp0 i hi)
          rw [hAfterUp0]
          dsimp only [δMid]
          rw [Function.update_of_ne hneLo, hLo0, zero_mul]
      · have hneAll : ∀ i (hi : i < R * 2 ^ r), u ≠ qUp R k w r hr i hi :=
          fun i hi e ↦ hU ⟨⟨i, hi⟩, e⟩
        have hneHi : u ≠ w bStar pHi := by rw [← hqUp₀]; exact hneAll i₀ hi₀
        dsimp only [δAfter]
        rw [Function.update_of_ne hneHi,
          upperXorBitsOpt_of_ne R k uLo w huw r hr δMid u (R * 2 ^ r) le_rfl hneAll]
    · rw [ite_eq_right hAct, ite_eq_right hAct, uUpperXorPrefixOpt_mulVec_ket,
        upperXorBitsOpt_all_zero R k uLo w huw r hr δ hw0 (R * 2 ^ r) le_rfl]
      exact seqNat_mulVec_fixed (ket δ) (R * 2 ^ r) _ fun _ _ ↦ ket_CNOT_ctrl_zero _ (hw0 _ _)
  · rw [ite_eq_right hV, ite_eq_right hV, Matrix.mulVec_zero, Matrix.mulVec_zero]
theorem subspaceStep_wUncompRoundDyn_opt {Var : Type} [Fintype Var] [DecidableEq Var]
    {n R k : ℕ} (v : Var) (P activePred : BitAssignment n → Prop) [DecidablePred P]
    [DecidablePred activePred] (bStarFn : BitAssignment n → Fin R) (uLo : Fin k → Wire n)
    (w : Fin R → Fin (2 ^ k) → Wire n) (hw : WInj w) (huw : ∀ d b p, uLo d ≠ w b p) (r : ℕ)
    (hr : r < k) {rest : DynamicCircuit Var n} {R_out : Operator (2 ^ n)} (hRest :
    SubspaceStep (oneHotOptPreOp P activePred bStarFn uLo w r (Nat.le_of_lt hr)) R_out rest) :
    SubspaceStep (oneHotOptPreOp P activePred bStarFn uLo w (r + 1) hr) R_out
    (wUncompRoundDyn v R k uLo w hw huw r hr rest) :=
  (subspaceStep_congr_out
    (subspaceStep_of_circuit (Var := Var) (oneHotOptPreOp P activePred bStarFn uLo w (r + 1) hr)
      (wUncompCnotRound R k w hw r hr))
    (wUncompCnotRound_mul_oneHotOptPreOp P activePred bStarFn uLo w hw huw r hr)).seq
    (subspaceStep_wUncompMeasPrefix_opt v P activePred bStarFn uLo w hw huw r hr hRest
      (R * 2 ^ r) le_rfl)
theorem subspaceStep_wUncompTreeDyn_opt {Var : Type} [Fintype Var] [DecidableEq Var]
    {n R k : ℕ} (v : Var) (P activePred : BitAssignment n → Prop)
    [DecidablePred P] [DecidablePred activePred]
    (bStarFn : BitAssignment n → Fin R) (uLo : Fin k → Wire n)
    (w : Fin R → Fin (2 ^ k) → Wire n) (hw : WInj w) (huw : ∀ d b p, uLo d ≠ w b p)
    {rest : DynamicCircuit Var n} {R_out : Operator (2 ^ n)}
    (hRest : SubspaceStep (oneHotOptPreOp P activePred bStarFn uLo w 0 (Nat.zero_le k)) R_out
      rest) :
    ∀ (m : ℕ) (hm : m ≤ k),
      SubspaceStep (oneHotOptPreOp P activePred bStarFn uLo w m hm) R_out
        (wUncompTreeDyn v R k uLo w hw huw rest m hm)
  | 0, _ => hRest
  | r + 1, hr =>
      subspaceStep_wUncompRoundDyn_opt v P activePred bStarFn uLo w hw huw r hr
        (subspaceStep_wUncompTreeDyn_opt v P activePred bStarFn uLo w hw huw hRest r
          (Nat.le_of_succ_le hr))
/- Section 3a: Generic optional W-expansion, last-round split-shift, and 8-bit 3+5 index split -/
theorem eval_X_mul_self_opt {n : ℕ} (q : Wire n) :
    (Circuit.X q).eval.1 * (Circuit.X q).eval.1 = 1 := by
  apply matrix_ext_ket; intro δ
  rw [← Matrix.mulVec_mulVec, ket_X, ket_X, Function.update_idem, Function.update_self,
    add_assoc, CharTwo.add_self_eq_zero, add_zero, Function.update_eq_self, Matrix.one_mulVec]
theorem eval_CNOT_mul_self_opt {n : ℕ} (c t : Wire n) (h : c ≠ t) :
    (Circuit.CNOT c t h).eval.1 * (Circuit.CNOT c t h).eval.1 = 1 := by
  apply matrix_ext_ket; intro δ
  rw [← Matrix.mulVec_mulVec, ket_CNOT, ket_CNOT, Function.update_idem, Function.update_self,
    Function.update_of_ne h, add_assoc, CharTwo.add_self_eq_zero, add_zero,
    Function.update_eq_self, Matrix.one_mulVec]
theorem wSuperVec_bot_pub {n R k : ℕ} (bStarFn : BitAssignment n → Fin R)
    (uLo : Fin k → Wire n) (w : Fin R → Fin (2 ^ k) → Wire n) (hw : WInj w)
    (qEnc : Wire n) (δ : BitAssignment n) (hw0 : ∀ b p, δ (w b p) = 0) (hq0 : δ qEnc = 0) :
    (wTreePrefix R k w hw k le_rfl).eval.1.mulVec
        (ket (Function.update δ (w (bStarFn δ) ⟨0, Nat.two_pow_pos k⟩) 1)) =
      wSuperVec bStarFn uLo w qEnc δ 0 (Nat.zero_le k) := by
  rw [wTreePrefix_mulVec_ket w hw δ hw0 (bStarFn δ) k le_rfl]
  dsimp only [wSuperVec]
  rw [ite_eq_left ⟨hw0, hq0⟩]
  have hk0 : k - 0 = k := Nat.sub_zero k
  let e : Fin (2 ^ k) ≃ Fin (2 ^ (k - 0)) := finCongr (by rw [hk0])
  rw [← e.sum_comp]
  simp only [hk0]
  congr 1
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  exact congrArg (fun p ↦ ket (Function.update δ (w (bStarFn δ) p) 1))
    (Fin.ext (by dsimp [e, idxValPrefix]; omega))
theorem wSuperVec_top_pub {n R k : ℕ} (bStarFn : BitAssignment n → Fin R)
    (uLo : Fin k → Wire n) (w : Fin R → Fin (2 ^ k) → Wire n) (qEnc : Wire n)
    (δ : BitAssignment n) (hw0 : ∀ b p, δ (w b p) = 0) (hq0 : δ qEnc = 0) : wSuperVec bStarFn
    uLo w qEnc δ k le_rfl = ket (Function.update δ (w (bStarFn δ) ⟨idxValPrefix uLo δ k
    le_rfl, idxValPrefix_lt_two_pow uLo δ k le_rfl⟩) 1) := by
  dsimp only [wSuperVec]
  rw [ite_eq_left ⟨hw0, hq0⟩, show sqrtHalf ^ (k - k) = 1 by rw [Nat.sub_self, _root_.pow_zero],
    one_smul]
  rw [Finset.sum_eq_single ⟨0, Nat.two_pow_pos (k - k)⟩]
  · exact congrArg (fun p ↦ ket (Function.update δ (w (bStarFn δ) p) 1)) (Fin.ext (by dsimp))
  · intro hi _ hne; exfalso; apply hne; apply Fin.ext
    have hv : hi.val < 2 ^ (k - k) := hi.isLt
    have hp : 2 ^ (k - k) = 1 := by simp
    dsimp; omega
  · intro habs; exact (habs (Finset.mem_univ _)).elim
theorem wTreeRound_mulVec_ket_zero {n R k : ℕ} (w : Fin R → Fin (2 ^ k) → Wire n)
    (hw : WInj w) (r : ℕ) (hr : r < k) (δ : BitAssignment n) (h0 : ∀ b p, δ (w b p) = 0) :
    (wTreeRound R k w hw r hr).eval.1.mulVec (ket δ) = ket δ := seqNat_mulVec_fixed (ket δ)
    (R * 2 ^ r) _ fun _ _ ↦ wSplitPair_mulVec_ket_zero _ _ _ δ (h0 _ _) (h0 _ _)
theorem wTreePrefix_mulVec_ket_zero {n R k : ℕ} (w : Fin R → Fin (2 ^ k) → Wire n)
    (hw : WInj w) (δ : BitAssignment n) (h0 : ∀ b p, δ (w b p) = 0) :
    ∀ (m : ℕ) (hm : m ≤ k), (wTreePrefix R k w hw m hm).eval.1.mulVec (ket δ) = ket δ
  | 0, _ => by rw [wTreePrefix, Circuit.eval_identity, Submonoid.coe_one, Matrix.one_mulVec]
  | r + 1, hr => by
      rw [wTreePrefix, eval_seq_mulVec,
        wTreePrefix_mulVec_ket_zero w hw δ h0 r (Nat.le_of_succ_le hr),
        wTreeRound_mulVec_ket_zero w hw r hr δ h0]
/-- Prefix of `m ≤ k` dummy-assisted W-shift rounds (`2 * m` `T`s, `0 .TOFF`). -/
def wShiftDummyLevels {Var : Type} {n : ℕ} (v : Var) (R k : ℕ) (uLo : Fin k → Wire n)
    (w : Fin R → Fin (2 ^ k) → Wire n) (rDum wDum qEnc : Wire n)
    (hInj : WOptInj R k uLo w rDum wDum qEnc) : (m : ℕ) → m ≤ k → DynamicCircuit Var n
  | 0, _ => .circuit .identity
  | d + 1, hd =>
      .seq (wShiftDummyLevels v R k uLo w rDum wDum qEnc hInj d (Nat.le_of_succ_le hd))
        (wShiftDummyLevel v R k uLo w rDum wDum qEnc hInj d hd)
theorem count_wShiftDummyLevels {Var : Type} {n : ℕ} (v : Var) (R k : ℕ) (uLo : Fin k → Wire n)
    (w : Fin R → Fin (2 ^ k) → Wire n) (rDum wDum qEnc : Wire n)
    (hInj : WOptInj R k uLo w rDum wDum qEnc) :
    ∀ (m : ℕ) (hm : m ≤ k),
      (wShiftDummyLevels v R k uLo w rDum wDum qEnc hInj m hm).count .T = 2 * m ∧
      (wShiftDummyLevels v R k uLo w rDum wDum qEnc hInj m hm).count .TOFF = 0
  | 0, _ => ⟨rfl, rfl⟩
  | d + 1, hd => by
      obtain ⟨t0, f0⟩ := count_wShiftDummyLevels v R k uLo w rDum wDum qEnc hInj d
        (Nat.le_of_succ_le hd)
      obtain ⟨t1, f1⟩ := count_wShiftDummyLevel v R k uLo w rDum wDum qEnc hInj d hd
      dsimp only [wShiftDummyLevels, DynamicCircuit.count]
      rw [t0, f0, t1, f1]; exact ⟨by omega, rfl⟩
theorem subspaceStep_wShiftDummyLevels {Var : Type} [Fintype Var] [DecidableEq Var] {n R k : ℕ}
    (v : Var) (P activePred : BitAssignment n → Prop)
    [DecidablePred P] [DecidablePred activePred]
    (bStarFn : BitAssignment n → Fin R) (uLo : Fin k → Wire n)
    (w : Fin R → Fin (2 ^ k) → Wire n) (rDum wDum qEnc : Wire n)
    (hInj : WOptInj R k uLo w rDum wDum qEnc)
    (hDumBit : ∀ δ, P δ → δ rDum = (if activePred δ then 0 else 1)) :
    ∀ (m : ℕ) (hm : m ≤ k),
      SubspaceStep
        (wOptSuperOp P activePred bStarFn uLo w wDum qEnc 0 (Nat.zero_le k))
        (wOptSuperOp P activePred bStarFn uLo w wDum qEnc m hm)
        (wShiftDummyLevels v R k uLo w rDum wDum qEnc hInj m hm)
  | 0, _ => by
      simpa only [wShiftDummyLevels, Circuit.eval_identity, Submonoid.coe_one, Matrix.one_mul] using
        subspaceStep_of_circuit (Var := Var)
          (wOptSuperOp P activePred bStarFn uLo w wDum qEnc 0 (Nat.zero_le k)) (.identity : Circuit
            n)
  | d + 1, hd =>
      (subspaceStep_wShiftDummyLevels v P activePred bStarFn uLo w rDum wDum qEnc hInj hDumBit d
          (Nat.le_of_succ_le hd)).seq
        (subspaceStep_wShiftDummyLevel v P activePred bStarFn uLo w rDum wDum qEnc hInj hDumBit d
          hd)
/-- Combined base + clean-ancilla predicate `P δ ∧ δ wDum = 0 ∧ δ qEnc = 0` for `oneHotOptPreOp`. -/
def OptBasePred {n : ℕ} (P : BitAssignment n → Prop) (wDum qEnc : Wire n) (δ : BitAssignment n) :
    Prop :=
  P δ ∧ δ wDum = 0 ∧ δ qEnc = 0
instance instDecidableOptBasePred {n : ℕ} (P : BitAssignment n → Prop) [DecidablePred P]
    (wDum qEnc : Wire n) : DecidablePred (OptBasePred P wDum qEnc) := fun δ ↦ by
  unfold OptBasePred; infer_instance
/-- Optional `k`-round CH-tree + dummy-assisted shift (`2 * R * (2^k - 1) + 2 * k` `T`s, `0
.TOFF`). -/
def wOptExpandDyn {Var : Type} {n : ℕ} (v : Var) (R k : ℕ) (uLo : Fin k → Wire n)
    (w : Fin R → Fin (2 ^ k) → Wire n) (rDum wDum qEnc : Wire n)
    (hInj : WOptInj R k uLo w rDum wDum qEnc) : DynamicCircuit Var n :=
  .seq (.circuit (wTreePrefix R k w hInj.w_inj k le_rfl))
    (wShiftDummyLevels v R k uLo w rDum wDum qEnc hInj k le_rfl)
theorem count_wOptExpandDyn {Var : Type} {n : ℕ} (v : Var) (R k : ℕ) (uLo : Fin k → Wire n)
    (w : Fin R → Fin (2 ^ k) → Wire n) (rDum wDum qEnc : Wire n)
    (hInj : WOptInj R k uLo w rDum wDum qEnc) :
    (wOptExpandDyn v R k uLo w rDum wDum qEnc hInj).count .T = 2 * R * (2 ^ k - 1) + 2 * k ∧
    (wOptExpandDyn v R k uLo w rDum wDum qEnc hInj).count .TOFF = 0 := by
  obtain ⟨t1, f1⟩ := count_wTreePrefix R k w hInj.w_inj k le_rfl
  obtain ⟨t2, f2⟩ := count_wShiftDummyLevels v R k uLo w rDum wDum qEnc hInj k le_rfl
  dsimp only [wOptExpandDyn, DynamicCircuit.count]
  rw [t1, f1, t2, f2]; exact ⟨rfl, rfl⟩
theorem wOptSuperOp_top_eq_oneHotOptPreOp {n R k : ℕ} (P activePred : BitAssignment n → Prop)
    [DecidablePred P] [DecidablePred activePred] (bStarFn : BitAssignment n → Fin R)
    (uLo : Fin k → Wire n) (w : Fin R → Fin (2 ^ k) → Wire n) (wDum qEnc : Wire n) :
    wOptSuperOp P activePred bStarFn uLo w wDum qEnc k le_rfl = oneHotOptPreOp
    (OptBasePred P wDum qEnc) activePred bStarFn uLo w k le_rfl := by
  apply matrix_ext_ket; intro δ
  simp only [wOptSuperOp, oneHotOptPreOp, mkVecOp_mulVec_ket, wOptSuperVec, oneHotOptPreVec]
  by_cases hV : P δ ∧ (∀ b p, δ (w b p) = 0) ∧ δ wDum = 0 ∧ δ qEnc = 0
  · have hV' : OptBasePred P wDum qEnc δ ∧ ∀ b p, δ (w b p) = 0 := ⟨⟨hV.1, hV.2.2.1, hV.2.2.2⟩,
      hV.2.1⟩
    rw [ite_eq_left hV, ite_eq_left hV']
    by_cases hAct : activePred δ
    · rw [ite_eq_left hAct, ite_eq_left hAct, wSuperVec_top_pub bStarFn uLo w qEnc δ hV.2.1
        hV.2.2.2]
    · rw [ite_eq_right hAct, ite_eq_right hAct]
  · have hV' : ¬ (OptBasePred P wDum qEnc δ ∧ ∀ b p, δ (w b p) = 0) :=
      fun ⟨⟨hp, hwd, hq⟩, hw⟩ ↦ hV ⟨hp, hw, hwd, hq⟩
    rw [ite_eq_right hV, ite_eq_right hV']
theorem subspaceStep_wOptExpandDyn {Var : Type} [Fintype Var] [DecidableEq Var] {n R k : ℕ}
    (v : Var) (P activePred : BitAssignment n → Prop) [DecidablePred P]
    [DecidablePred activePred] (bStarFn : BitAssignment n → Fin R) (uLo : Fin k → Wire n)
    (w : Fin R → Fin (2 ^ k) → Wire n) (rDum wDum qEnc : Wire n)
    (hInj : WOptInj R k uLo w rDum wDum qEnc)
    (hDumBit : ∀ δ, P δ → δ rDum = (if activePred δ then 0 else 1)) : SubspaceStep
    (oneHotOptPreOp (OptBasePred P wDum qEnc) activePred bStarFn uLo w 0 (Nat.zero_le k))
    (oneHotOptPreOp (OptBasePred P wDum qEnc) activePred bStarFn uLo w k le_rfl)
    (wOptExpandDyn v R k uLo w rDum wDum qEnc hInj) := by
  have hTree : (wTreePrefix R k w hInj.w_inj k le_rfl).eval.1 *
      oneHotOptPreOp (OptBasePred P wDum qEnc) activePred bStarFn uLo w 0 (Nat.zero_le k) =
      wOptSuperOp P activePred bStarFn uLo w wDum qEnc 0 (Nat.zero_le k) := by
    apply matrix_ext_ket; intro δ
    simp only [← Matrix.mulVec_mulVec, oneHotOptPreOp, wOptSuperOp, mkVecOp_mulVec_ket,
      oneHotOptPreVec, wOptSuperVec]
    by_cases hV : P δ ∧ (∀ b p, δ (w b p) = 0) ∧ δ wDum = 0 ∧ δ qEnc = 0
    · have hV' : OptBasePred P wDum qEnc δ ∧ ∀ b p, δ (w b p) = 0 := ⟨⟨hV.1, hV.2.2.1, hV.2.2.2⟩,
        hV.2.1⟩
      rw [ite_eq_left hV', ite_eq_left hV]
      by_cases hAct : activePred δ
      · rw [ite_eq_left hAct, ite_eq_left hAct]
        have hp0 : (⟨idxValPrefix uLo δ 0 (Nat.zero_le k), Nat.lt_of_lt_of_le
            (idxValPrefix_lt_two_pow uLo δ 0 (Nat.zero_le k)) (Nat.pow_le_pow_right (by omega)
            (Nat.zero_le k))⟩ : Fin (2 ^ k)) = ⟨0, Nat.two_pow_pos k⟩ := Fin.ext rfl
        rw [hp0, wSuperVec_bot_pub bStarFn uLo w hInj.w_inj qEnc δ hV.2.1 hV.2.2.2]
      · rw [ite_eq_right hAct, ite_eq_right hAct,
          wTreePrefix_mulVec_ket_zero w hInj.w_inj δ hV.2.1 k le_rfl]
    · have hV' : ¬ (OptBasePred P wDum qEnc δ ∧ ∀ b p, δ (w b p) = 0) :=
        fun ⟨⟨hp, hwd, hq⟩, hw⟩ ↦ hV ⟨hp, hw, hwd, hq⟩
      rw [ite_eq_right hV', ite_eq_right hV, Matrix.mulVec_zero]
  exact (subspaceStep_congr_out (subspaceStep_of_circuit _ _) hTree).seq
    (subspaceStep_congr_out
      (subspaceStep_wShiftDummyLevels v P activePred bStarFn uLo w rDum wDum qEnc hInj hDumBit k
        le_rfl)
      (wOptSuperOp_top_eq_oneHotOptPreOp P activePred bStarFn uLo w wDum qEnc))
/-- Decidable pairwise disjointness for an unconditional `N`-output W-state router (no `wHas`
wire). -/
abbrev WUncondDisjProp {D N n : ℕ} (wIdx : Fin D → Wire n) (wOut : Fin N → Wire n)
    (qEnc : Wire n) : Prop := (∀ d j, wIdx d ≠ wOut j) ∧ (∀ d, wIdx d ≠ qEnc) ∧
    (∀ i j, i ≠ j → wOut i ≠ wOut j) ∧ (∀ j, wOut j ≠ qEnc)
abbrev WUncondOutDisj {D N n : ℕ} (wIdx : Fin D → Wire n) (wOut : Fin N → Wire n) : Prop :=
  (∀ d j, wIdx d ≠ wOut j) ∧ (∀ i j, i ≠ j → wOut i ≠ wOut j)
/-- Clean-input predicate `(∀ j, δ (wOut j) = 0) ∧ δ qEnc = 0` for unconditional `Pow2` routing. -/
def ValidWUncondIn {N n : ℕ} (wOut : Fin N → Wire n) (qEnc : Wire n) (δ : BitAssignment n) :
    Prop := (∀ j, δ (wOut j) = 0) ∧ δ qEnc = 0
/-- Clean-output predicate `∀ j, δ (wOut j) = 0` after unconditional `Pow2` uncomputation. -/
def ValidWUncondClean {N n : ℕ} (wOut : Fin N → Wire n) (δ : BitAssignment n) : Prop :=
  ∀ j, δ (wOut j) = 0
/-- Basis-permutation toggling `wOut ⟨idxValD wIdx δ, _⟩` unconditionally (`N = 2^D`). -/
def oneHotUncondPerm {D n : ℕ} (wIdx : Fin D → Wire n) (wOut : Fin (2 ^ D) → Wire n)
    (hIdxOut : ∀ d j, wIdx d ≠ wOut j) : Equiv.Perm (BitAssignment n) where
  toFun δ :=
    let j : Fin (2 ^ D) := ⟨idxValD wIdx δ, idxValD_lt_two_pow wIdx δ⟩
    Function.update δ (wOut j) (δ (wOut j) + 1)
  invFun δ :=
    let j : Fin (2 ^ D) := ⟨idxValD wIdx δ, idxValD_lt_two_pow wIdx δ⟩
    Function.update δ (wOut j) (δ (wOut j) + 1)
  left_inv δ := by
    dsimp only
    let j : Fin (2 ^ D) := ⟨idxValD wIdx δ, idxValD_lt_two_pow wIdx δ⟩
    let δ' := Function.update δ (wOut j) (δ (wOut j) + 1)
    have hIdxEq : idxValD wIdx δ' = idxValD wIdx δ :=
      idxValD_congr wIdx (fun d ↦ Function.update_of_ne (hIdxOut d j) _ δ)
    have hjEq : (⟨idxValD wIdx δ', idxValD_lt_two_pow wIdx δ'⟩ : Fin (2 ^ D)) = j :=
      Fin.ext hIdxEq
    change Function.update δ' (wOut ⟨idxValD wIdx δ', _⟩) _ = δ
    rw [hjEq]
    dsimp only [δ']
    rw [Function.update_idem, Function.update_self, add_assoc, CharTwo.add_self_eq_zero,
      add_zero, Function.update_eq_self]
  right_inv δ := by
    dsimp only
    let j : Fin (2 ^ D) := ⟨idxValD wIdx δ, idxValD_lt_two_pow wIdx δ⟩
    let δ' := Function.update δ (wOut j) (δ (wOut j) + 1)
    have hIdxEq : idxValD wIdx δ' = idxValD wIdx δ :=
      idxValD_congr wIdx (fun d ↦ Function.update_of_ne (hIdxOut d j) _ δ)
    have hjEq : (⟨idxValD wIdx δ', idxValD_lt_two_pow wIdx δ'⟩ : Fin (2 ^ D)) = j :=
      Fin.ext hIdxEq
    change Function.update δ' (wOut ⟨idxValD wIdx δ', _⟩) _ = δ
    rw [hjEq]
    dsimp only [δ']
    rw [Function.update_idem, Function.update_self, add_assoc, CharTwo.add_self_eq_zero,
      add_zero, Function.update_eq_self]
noncomputable def uOneHotUncond {D n : ℕ} (wIdx : Fin D → Wire n) (wOut : Fin (2 ^ D) → Wire n)
    (hIdxOut : ∀ d j, wIdx d ≠ wOut j) : Unitary (2 ^ n) :=
  permUnitary (oneHotUncondPerm wIdx wOut hIdxOut)
theorem uOneHotUncond_mulVec_ket {D n : ℕ} (wIdx : Fin D → Wire n)
    (wOut : Fin (2 ^ D) → Wire n) (hIdxOut : ∀ d j, wIdx d ≠ wOut j) (δ : BitAssignment n) :
    (uOneHotUncond wIdx wOut hIdxOut).1.mulVec (ket δ) = ket (Function.update δ (wOut ⟨idxValD
    wIdx δ, idxValD_lt_two_pow wIdx δ⟩) (δ (wOut ⟨idxValD wIdx δ, idxValD_lt_two_pow wIdx δ⟩)
    + 1)) := permUnitary_mulVec_ket (oneHotUncondPerm wIdx wOut hIdxOut) δ
/-- Unconditional `4*(2^k - 1)`-`T` forward W-state one-hot loader for `N = 2^(k+1)` (`0 .TOFF`, no
`wHas`). -/
def wStateComputeUncondPow2 {Var : Type} {n : ℕ} (k : ℕ) (v : Var)
    (wIdx : Fin (k + 1) → Wire n) (wOut : Fin (2 ^ (k + 1)) → Wire n) (qEnc : Wire n) :
    DynamicCircuit Var n :=
  if h : WUncondDisjProp wIdx wOut qEnc then
    let root := wRootSpecPow2 wIdx wOut h.1
    let w := blockWires (two_mul_pow_eq k) wOut
    let hw : WInj w := wInj_blockWires (two_mul_pow_eq k) h.2.2.1
    let uLo := uLoOf (Nat.le_succ k) wIdx
    let hwq : ∀ b p, w b p ≠ qEnc := fun _ _ ↦ h.2.2.2 _
    let huq : ∀ d, uLo d ≠ qEnc := fun _ ↦ h.2.1 _
    .seq (.circuit (root.cRootInit ;;ᶜ wTreePrefix 2 k w hw k le_rfl))
      (wShiftLevels v 2 k uLo w qEnc hw hwq huq k le_rfl)
  else
    .circuit (seqNat (4 * (2 ^ k - 1)) fun _ _ ↦ Circuit.T qEnc)
/-- Unconditional `0-T` MBU uncomputer for `N = 2^(k+1)` W-state one-hot loader (`0 .TOFF`, no
`wHas`, no `qEnc`). -/
def wStateUncomputeUncondPow2 {Var : Type} {n : ℕ} (k : ℕ) (v : Var)
    (wIdx : Fin (k + 1) → Wire n) (wOut : Fin (2 ^ (k + 1)) → Wire n) :
    DynamicCircuit Var n :=
  if h : WUncondOutDisj wIdx wOut then
    let root := wRootSpecPow2 wIdx wOut h.1
    let w := blockWires (two_mul_pow_eq k) wOut
    let hw : WInj w := wInj_blockWires (two_mul_pow_eq k) h.2
    let uLo := uLoOf (Nat.le_succ k) wIdx
    let huw : ∀ d b p, uLo d ≠ w b p := fun _ _ _ ↦ h.1 _ _
    wUncompTreeDyn v 2 k uLo w hw huw (.circuit root.cRootUninit) k le_rfl
  else
    .circuit .identity
theorem count_wStateComputeUncondPow2 {Var : Type} {n : ℕ} (k : ℕ) (v : Var)
    (wIdx : Fin (k + 1) → Wire n) (wOut : Fin (2 ^ (k + 1)) → Wire n) (qEnc : Wire n) :
    (wStateComputeUncondPow2 k v wIdx wOut qEnc).count .T = 4 * (2 ^ k - 1) ∧
    (wStateComputeUncondPow2 k v wIdx wOut qEnc).count .TOFF = 0 := by
  dsimp only [wStateComputeUncondPow2]
  split_ifs with h
  · obtain ⟨ri_t, ri_f⟩ := (wRootSpecPow2 wIdx wOut h.1).count_init
    obtain ⟨tr_t, tr_f⟩ := count_wTreePrefix 2 k (blockWires (two_mul_pow_eq k) wOut)
      (wInj_blockWires (two_mul_pow_eq k) h.2.2.1) k le_rfl
    obtain ⟨sh_t, sh_f⟩ := count_wShiftLevels v 2 k (uLoOf (Nat.le_succ k) wIdx)
        (blockWires (two_mul_pow_eq k) wOut) qEnc (wInj_blockWires (two_mul_pow_eq k) h.2.2.1)
        (fun _ _ ↦ h.2.2.2 _) (fun _ ↦ h.2.1 _) k le_rfl
    refine ⟨?_, ?_⟩ <;>
      simp [DynamicCircuit.count, Circuit.count_seq, ri_t, ri_f, tr_t, tr_f, sh_t, sh_f]
  · refine ⟨?_, ?_⟩
    · simpa [DynamicCircuit.count] using
        count_seqNat_T 1 (4 * (2 ^ k - 1)) _ (fun _ _ ↦ by simp [Circuit.T])
    · exact count_seqNat_TOFF_zero (4 * (2 ^ k - 1)) _ (fun _ _ ↦ by simp [Circuit.T])
theorem count_wStateUncomputeUncondPow2 {Var : Type} {n : ℕ} (k : ℕ) (v : Var)
    (wIdx : Fin (k + 1) → Wire n) (wOut : Fin (2 ^ (k + 1)) → Wire n) :
    (wStateUncomputeUncondPow2 k v wIdx wOut).count .T = 0 ∧
    (wStateUncomputeUncondPow2 k v wIdx wOut).count .TOFF = 0 := by
  dsimp only [wStateUncomputeUncondPow2]
  split_ifs with h
  · obtain ⟨ru_t, ru_f⟩ := (wRootSpecPow2 wIdx wOut h.1).count_uninit
    obtain ⟨ut, uf⟩ := count_wUncompTreeDyn v 2 k (uLoOf (Nat.le_succ k) wIdx)
      (blockWires (two_mul_pow_eq k) wOut) (wInj_blockWires (two_mul_pow_eq k) h.2)
      (fun _ _ _ ↦ h.1 _ _) (.circuit (wRootSpecPow2 wIdx wOut h.1).cRootUninit) k le_rfl
    exact ⟨ut.trans ru_t, uf.trans ru_f⟩
  · exact ⟨rfl, rfl⟩
theorem subspaceStep_wStateComputeUncondPow2 {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    (k : ℕ) (v : Var) (wIdx : Fin (k + 1) → Wire n)
    (wOut : Fin (2 ^ (k + 1)) → Wire n) (qEnc : Wire n)
    (hd : WUncondDisjProp wIdx wOut qEnc)
    (G : Operator (2 ^ n)) (hSupp : SupportedOn (ValidWUncondIn wOut qEnc) G) :
    SubspaceStep (Var := Var) G ((uOneHotUncond wIdx wOut hd.1).1 * G)
      (wStateComputeUncondPow2 k v wIdx wOut qEnc) := by
  dsimp only [wStateComputeUncondPow2]
  rw [dite_eq_left hd]
  let root := wRootSpecPow2 wIdx wOut hd.1
  let w := blockWires (two_mul_pow_eq k) wOut
  let hw : WInj w := wInj_blockWires (two_mul_pow_eq k) hd.2.2.1
  let uLo := uLoOf (Nat.le_succ k) wIdx
  let hwq : ∀ b p, w b p ≠ qEnc := fun _ _ ↦ hd.2.2.2 _
  let huq : ∀ d, uLo d ≠ qEnc := fun _ ↦ hd.2.1 _
  let huw : ∀ d b p, uLo d ≠ w b p := fun _ _ _ ↦ hd.1 _ _
  have hStage1Eq : (root.cRootInit ;;ᶜ wTreePrefix 2 k w hw k le_rfl).eval.1 * G =
      wSuperOp root.bStarFn uLo w qEnc 0 (Nat.zero_le k) * G :=
    hSupp _ _ fun δ hP ↦ by
      rw[eval_seq_mulVec, root.init_ket δ hP.1 (idxValD_lt_two_pow wIdx δ),
          wSuperVec_bot root.bStarFn uLo w hw qEnc δ (fun _ _ ↦ hP.1 _) hP.2, wSuperOp,
          mkVecOp_mulVec_ket]
  have s1 : SubspaceStep (Var := Var) G (wSuperOp root.bStarFn uLo w qEnc 0 (Nat.zero_le k) * G)
      (.circuit (root.cRootInit ;;ᶜ wTreePrefix 2 k w hw k le_rfl)) :=
    subspaceStep_congr_out (subspaceStep_of_circuit G _) hStage1Eq
  have s2 : SubspaceStep (Var := Var)
      (wSuperOp root.bStarFn uLo w qEnc 0 (Nat.zero_le k) * G)
      (wSuperOp root.bStarFn uLo w qEnc k le_rfl * G)
      (wShiftLevels v 2 k uLo w qEnc hw hwq huq k le_rfl) :=
    subspaceStep_mul_right G
      (subspaceStep_wShiftLevels v root.bStarFn uLo w qEnc hw hwq huq huw k le_rfl)
  have hTopEq : wSuperOp root.bStarFn uLo w qEnc k le_rfl * G =
      (uOneHotUncond wIdx wOut hd.1).1 * G :=
    hSupp _ _ fun δ hP ↦ by
      rw [wSuperOp, mkVecOp_mulVec_ket,
        wSuperVec_top root.bStarFn uLo w qEnc δ (fun _ _ ↦ hP.1 _) hP.2,
        uOneHotUncond_mulVec_ket wIdx wOut hd.1 δ, hP.1 _, zero_add]
      have hWire : w (root.bStarFn δ) ⟨idxValPrefix uLo δ k le_rfl, idxValPrefix_lt_two_pow
          uLo δ k le_rfl⟩ = wOut ⟨idxValD wIdx δ, idxValD_lt_two_pow wIdx δ⟩ := by
        dsimp only [w, blockWires]
        congr 1; apply Fin.ext
        exact root.idx_decomp δ (idxValD_lt_two_pow wIdx δ)
      rw [hWire]
  exact s1.seq (subspaceStep_congr_out s2 hTopEq)
theorem subspaceStep_wStateUncomputeUncondPow2 {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    (k : ℕ) (v : Var) (wIdx : Fin (k + 1) → Wire n)
    (wOut : Fin (2 ^ (k + 1)) → Wire n) (ho : WUncondOutDisj wIdx wOut)
    (G : Operator (2 ^ n)) (hSupp : SupportedOn (ValidWUncondClean wOut) G) :
    SubspaceStep (Var := Var) ((uOneHotUncond wIdx wOut ho.1).1 * G) G
      (wStateUncomputeUncondPow2 k v wIdx wOut) := by
  dsimp only [wStateUncomputeUncondPow2]
  rw [dite_eq_left ho]
  let root := wRootSpecPow2 wIdx wOut ho.1
  let w := blockWires (two_mul_pow_eq k) wOut
  let hw : WInj w := wInj_blockWires (two_mul_pow_eq k) ho.2
  let uLo := uLoOf (Nat.le_succ k) wIdx
  let huw : ∀ d b p, uLo d ≠ w b p := fun _ _ _ ↦ ho.1 _ _
  let P : BitAssignment n → Prop := fun δ ↦ ∀ j, δ (wOut j) = 0
  let _ : DecidablePred P := fun _ ↦ Classical.propDecidable _
  have hStartEq : (uOneHotUncond wIdx wOut ho.1).1 * G =
      oneHotPreOp P root.bStarFn uLo w k le_rfl * G :=
    hSupp _ _ fun δ hP ↦ by
      simp only [oneHotPreOp, mkVecOp_mulVec_ket, oneHotPreVec]
      rw [ite_eq_left ⟨hP, fun _ _ ↦ hP _⟩, uOneHotUncond_mulVec_ket wIdx wOut ho.1 δ,
        hP _, zero_add]
      have hWire : w (root.bStarFn δ) ⟨idxValPrefix uLo δ k le_rfl, Nat.lt_of_lt_of_le
          (idxValPrefix_lt_two_pow uLo δ k le_rfl) (Nat.pow_le_pow_right (by omega) le_rfl)⟩ =
          wOut ⟨idxValD wIdx δ, idxValD_lt_two_pow wIdx δ⟩ := by
        dsimp only [w, blockWires]
        congr 1; apply Fin.ext
        exact root.idx_decomp δ (idxValD_lt_two_pow wIdx δ)
      rw [hWire]
  let idOnP : Operator (2 ^ n) :=
    mkVecOp fun δ ↦ if P δ ∧ ∀ b p, δ (w b p) = 0 then ket δ else 0
  have hBaseEq : root.cRootUninit.eval.1 * oneHotPreOp P root.bStarFn uLo w 0 (Nat.zero_le k) =
      idOnP := by
    apply matrix_ext_ket; intro δ
    rw [← Matrix.mulVec_mulVec]
    simp only [oneHotPreOp, idOnP, mkVecOp_mulVec_ket, oneHotPreVec]
    by_cases hV : P δ ∧ ∀ b p, δ (w b p) = 0
    · rw [ite_eq_left hV, ite_eq_left hV]
      have hp0Eq : (⟨idxValPrefix uLo δ 0 (Nat.zero_le k), Nat.lt_of_lt_of_le
          (idxValPrefix_lt_two_pow uLo δ 0 (Nat.zero_le k)) (Nat.pow_le_pow_right (by omega)
          (Nat.zero_le k))⟩ : Fin (2 ^ k)) = ⟨0, Nat.two_pow_pos k⟩ := Fin.ext rfl
      rw [hp0Eq, ← root.init_ket δ hV.1 (idxValD_lt_two_pow wIdx δ), root.uninit_init]
    · rw [ite_eq_right hV, ite_eq_right hV, Matrix.mulVec_zero]
  have sTreeOp : SubspaceStep (Var := Var)
      (oneHotPreOp P root.bStarFn uLo w k le_rfl) idOnP
      (wUncompTreeDyn v 2 k uLo w hw huw (.circuit root.cRootUninit) k le_rfl) :=
    subspaceStep_wUncompTreeDyn v P root.bStarFn uLo w hw huw
      (subspaceStep_congr_out (subspaceStep_of_circuit _ root.cRootUninit) hBaseEq) k le_rfl
  have hIdG : idOnP * G = G := by
    have h1 : idOnP * G = (1 : Operator (2 ^ n)) * G :=
      hSupp _ _ fun δ hP ↦ by
        simp only [idOnP, mkVecOp_mulVec_ket, Matrix.one_mulVec]
        exact ite_eq_left ⟨hP, fun _ _ ↦ hP _⟩
    exact h1.trans (Matrix.one_mul G)
  exact subspaceStep_congr_in hStartEq
    (subspaceStep_congr_out (subspaceStep_mul_right G sTreeOp) hIdG)
end MultiBankWStateRouter
end
end
end MultiBankWStateRouter

noncomputable section TwistShared108AndLeaf3Bk

section
namespace TwistShared108AndLeaf3Bk
section Config13
set_option maxRecDepth 65536
set_option exponentiation.threshold 5000
local instance (priority := 1000000) instNeZeroTwoPowNestedRouter (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩
noncomputable section
open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt HermitianMat Real
open scoped Matrix ComplexOrder MatrixOrder BigOperators Matrix.Norms.L2Operator Circuit.Notation
section TightZeroMuxSkipAndTwistCaps
set_option maxRecDepth 65536
set_option exponentiation.threshold 256
open SpecsAux SpecsAux.SpecMirror
open SpecsAux.PhaseGradCatalystCore
open DyadicQft64 hiding dyadicTurn phaseGradKet andSymStep andSymStep_stepFwd
open DyadicQft64WalkCircuit
open NuclearTwistAndXor654Concrete hiding fullSysCoreWires IntertwinesLocalCat
open NuclearTwistRealizes
open NuclearTwistMulKickAndBridge288
open WindowedSlot2MulKick288
open WindowedSlot2FusedTwist288
open Slot2ZeroMuxSignedMul46
open HeldMsbInc7ApexWrap288 (ApexKoffMulKickSpec apexKoffDelta mEffBits)
/-- Per-axis `.T` count of `dSlot2ZeroMuxTruncSkip_koffScr` (`(4 * (46 - skip) + 2) + ∑_{i < 13} (4
* (45 - skip - i) + 2)`). -/
def tZeroMuxSkip (skip : ℕ) : ℕ :=
  (4 * (46 - skip) + 2) + ∑ i : Fin 13, (4 * (45 - skip - i.val) + 2)
theorem mEffBits_of_ge {skip : ℕ} (M : Fin 48 → ZMod 2) {i : ℕ} (hi : skip ≤ i)
    (hi48 : i < 48) : mEffBits skip M ⟨i, hi48⟩ = M ⟨i, hi48⟩ :=
  ite_eq_right (by change ¬ (i < skip); omega)
theorem bitsVal_mEffBits_prefix {skip m : ℕ} (hsk : skip ≤ m) (hm48 : m ≤ 48)
    (M : Fin 48 → ZMod 2) :
    bitsVal (fun j : Fin m ↦ mEffBits skip M ⟨j.val, by omega⟩) =
      2 ^ skip * bitsVal (fun j : Fin (m - skip) ↦ M ⟨j.val + skip, by omega⟩) := by
  have hSplit : skip + (m - skip) = m := by omega
  have h0 := regVal_split_at_shift hSplit (QRegExt.idReg m)
    (fun j : Fin m ↦ mEffBits skip M ⟨j.val, by omega⟩)
  change bitsVal (fun j : Fin m ↦ mEffBits skip M ⟨j.val, by omega⟩) =
    bitsVal (fun j : Fin skip ↦ mEffBits skip M ⟨j.val, by omega⟩) +
      2 ^ skip * bitsVal (fun j : Fin (m - skip) ↦ mEffBits skip M ⟨skip + j.val, by omega⟩) at h0
  have hLo : bitsVal (fun j : Fin skip ↦ mEffBits skip M ⟨j.val, by omega⟩) = 0 := by
    have hfn : (fun j : Fin skip ↦ mEffBits skip M ⟨j.val, by omega⟩) = (fun _ ↦ 0) :=
      funext fun j ↦ ite_eq_left j.isLt
    rw [hfn]
    unfold bitsVal
    simp [show (0 : ZMod 2).val = 0 from rfl]
  have hHi : (fun j : Fin (m - skip) ↦ mEffBits skip M ⟨skip + j.val, by omega⟩) =
      (fun j : Fin (m - skip) ↦ M ⟨j.val + skip, by omega⟩) :=
    funext fun j ↦ by
      dsimp only [mEffBits]
      rw [ite_eq_right (by omega)]
      exact congrArg M (Fin.ext (by dsimp; omega))
  rw [h0, hLo, zero_add, hHi]
theorem bitsVal_mEffBits_eq {skip : ℕ} (hsk48 : skip ≤ 48) (M : Fin 48 → ZMod 2) :
    bitsVal (mEffBits skip M) =
      2 ^ skip * bitsVal (fun j : Fin (48 - skip) ↦ M ⟨j.val + skip, by omega⟩) :=
  bitsVal_mEffBits_prefix hsk48 le_rfl M
theorem bitsVal_47_mEffBits_eq {skip : ℕ} (hsk1 : 1 ≤ skip) (hsk48 : skip ≤ 48)
    (M : Fin 48 → ZMod 2) :
    bitsVal (fun j : Fin 47 ↦ mEffBits skip M j.succ) =
      2 ^ (skip - 1) * bitsVal (fun j : Fin (48 - skip) ↦ M ⟨j.val + skip, by omega⟩) := by
  have hSplit : (skip - 1) + (48 - skip) = 47 := by omega
  have h0 := regVal_split_at_shift hSplit (QRegExt.idReg 47)
    (fun j : Fin 47 ↦ mEffBits skip M j.succ)
  change bitsVal (fun j : Fin 47 ↦ mEffBits skip M j.succ) =
    bitsVal (fun j : Fin (skip - 1) ↦ mEffBits skip M (⟨j.val, by omega⟩ : Fin 47).succ) +
      2 ^ (skip - 1) * bitsVal (fun j : Fin (48 - skip) ↦
        mEffBits skip M (⟨(skip - 1) + j.val, by omega⟩ : Fin 47).succ) at h0
  have hLo : bitsVal (fun j : Fin (skip - 1) ↦
      mEffBits skip M (⟨j.val, by omega⟩ : Fin 47).succ) = 0 := by
    have hfn : (fun j : Fin (skip - 1) ↦
        mEffBits skip M (⟨j.val, by omega⟩ : Fin 47).succ) = (fun _ ↦ 0) :=
      funext fun j ↦ ite_eq_left (by change j.val + 1 < skip; omega)
    rw [hfn]
    unfold bitsVal
    simp [show (0 : ZMod 2).val = 0 from rfl]
  have hHi : (fun j : Fin (48 - skip) ↦
      mEffBits skip M (⟨(skip - 1) + j.val, by omega⟩ : Fin 47).succ) =
      (fun j : Fin (48 - skip) ↦ M ⟨j.val + skip, by omega⟩) :=
    funext fun j ↦ by
      dsimp only [mEffBits]
      rw [ite_eq_right (by change ¬ ((skip - 1) + j.val + 1 < skip); omega)]
      exact congrArg M (Fin.ext (by change (skip - 1) + j.val + 1 = j.val + skip; omega))
  rw [h0, hLo, zero_add, hHi]
theorem bitsVal_W_split {skip : ℕ} (hsk1 : 1 ≤ skip) (hsk46 : skip ≤ 46)
    (M : Fin 48 → ZMod 2) :
    (2 ^ (skip - 1) : ℤ) *
        (bitsVal (fun j : Fin (48 - skip) ↦ M ⟨j.val + skip, by omega⟩) : ℤ) =
      (2 ^ (skip - 1) : ℤ) *
          (bitsVal (fun j : Fin (46 - skip) ↦ M ⟨j.val + skip, by omega⟩) : ℤ) +
        (2 ^ 45 : ℤ) * ((M ⟨46, by decide⟩).val : ℤ) +
        (2 ^ 46 : ℤ) * ((M ⟨47, by decide⟩).val : ℤ) := by
  let w0 : ℕ := 46 - skip
  have hReidx :
      bitsVal (fun j : Fin (48 - skip) ↦ M ⟨j.val + skip, by omega⟩) =
        bitsVal (fun j : Fin (w0 + 1 + 1) ↦ M ⟨j.val + skip, by omega⟩) := by
    unfold bitsVal
    exact Finset.sum_bij (fun i _ ↦ ⟨i.val, by omega⟩) (fun _ _ ↦ Finset.mem_univ _)
      (fun a b _ _ h ↦ Fin.ext (congrArg (fun x : Fin (w0 + 1 + 1) ↦ x.val) h))
      (fun j _ ↦ ⟨⟨j.val, by omega⟩, Finset.mem_univ _, rfl⟩)
      (fun _ _ ↦ rfl)
  have hNat :
      bitsVal (fun j : Fin (w0 + 1 + 1) ↦ M ⟨j.val + skip, by omega⟩) =
        bitsVal (fun j : Fin w0 ↦ M ⟨j.val + skip, by omega⟩) +
          (M ⟨46, by decide⟩).val * 2 ^ w0 +
          (M ⟨47, by decide⟩).val * 2 ^ (w0 + 1) := by
    unfold bitsVal
    rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
    have h46 : (⟨w0 + skip, by omega⟩ : Fin 48) = ⟨46, by decide⟩ :=
      Fin.ext (by dsimp [w0]; omega)
    have h47 : (⟨w0 + 1 + skip, by omega⟩ : Fin 48) = ⟨47, by decide⟩ :=
      Fin.ext (by dsimp [w0]; omega)
    dsimp only [Fin.val_castSucc, Fin.val_last]
    rw [h46, h47]
  have hp45 : (2 ^ (skip - 1) : ℤ) * (2 ^ w0 : ℤ) = (2 ^ 45 : ℤ) := by
    have he : (skip - 1) + w0 = 45 := by omega
    rw [← pow_add, he]
  have hp46 : (2 ^ (skip - 1) : ℤ) * (2 ^ (w0 + 1) : ℤ) = (2 ^ 46 : ℤ) := by
    have he : (skip - 1) + (w0 + 1) = 46 := by omega
    rw [← pow_add, he]
  have hNatZ :
      (bitsVal (fun j : Fin (48 - skip) ↦ M ⟨j.val + skip, by omega⟩) : ℤ) =
        (bitsVal (fun j : Fin w0 ↦ M ⟨j.val + skip, by omega⟩) : ℤ) +
          ((M ⟨46, by decide⟩).val : ℤ) * (2 : ℤ) ^ w0 +
          ((M ⟨47, by decide⟩).val : ℤ) * (2 : ℤ) ^ (w0 + 1) := by
    rw [hReidx, hNat]; push_cast; rfl
  rw [hNatZ]
  calc (2 ^ (skip - 1) : ℤ) *
        ((bitsVal (fun j : Fin w0 ↦ M ⟨j.val + skip, by omega⟩) : ℤ) +
          ((M ⟨46, by decide⟩).val : ℤ) * (2 : ℤ) ^ w0 +
          ((M ⟨47, by decide⟩).val : ℤ) * (2 : ℤ) ^ (w0 + 1))
      = (2 ^ (skip - 1) : ℤ) * (bitsVal (fun j : Fin w0 ↦ M ⟨j.val + skip, by omega⟩) : ℤ) +
          ((2 ^ (skip - 1) : ℤ) * (2 ^ w0 : ℤ)) * ((M ⟨46, by decide⟩).val : ℤ) +
          ((2 ^ (skip - 1) : ℤ) * (2 ^ (w0 + 1) : ℤ)) * ((M ⟨47, by decide⟩).val : ℤ) := by ring
    _ = _ := by rw [hp45, hp46]
theorem zero_of_mem_scr {mScr n : ℕ} {rScr : QRegister mScr n} {β : BitAssignment n}
    (hz : ∀ i : Fin mScr, β (rScr i) = 0) {w : Wire n} (hw : w ∈ rScr.image) : β w = 0 := by
  obtain ⟨i, rfl⟩ := (QRegister.mem_image rScr w).mp hw
  exact hz i
def ApexZeroMuxStepSpecScr {Var : Type} [Fintype Var] [DecidableEq Var] {mScr n : ℕ}
    [NeZero (2 ^ n)] (v : Var) (rSum14 : QRegister 14 n) (rM48 : QRegister 48 n)
    (rPGTwist : QRegister 48 n) (rScr : QRegister mScr n) (d : DynamicCircuit Var n)
    (Δ : (Fin 14 → ZMod 2) → (Fin 48 → ZMod 2) → ℤ) : Prop := ∃ (c : Circuit n)
    (f : BitAssignment n → BitAssignment n) (φ : BitAssignment n → ℂ), CleanPhasePermEquiv v
    rScr (rPGTwist.slice 0 45 (by decide)).image d c φ f ∧ ∀ β : BitAssignment n,
    (∀ i : Fin mScr, β (rScr i) = 0) → ((regVal (rPGTwist.slice 0 45 (by decide)) (f β) : ℤ) -
    ((regVal (rPGTwist.slice 0 45 (by decide)) β : ℤ) + Δ (fun s ↦ β (rSum14 s)) (fun j ↦ β
    (rM48 j)))) % (2 ^ 45 : ℤ) = 0 ∧ φ β = DyadicQft64.dyadicTurn 48 (Δ (fun s ↦ β (rSum14 s))
    (fun j ↦ β (rM48 j)) - ((regVal (rPGTwist.slice 0 45 (by decide)) (f β) : ℤ) - (regVal
    (rPGTwist.slice 0 45 (by decide)) β : ℤ)))
theorem ApexZeroMuxStepSpecScr.identity {Var : Type} [Fintype Var] [DecidableEq Var]
    {mScr n : ℕ} [NeZero (2 ^ n)] (v : Var) (rSum14 : QRegister 14 n) (rM48 : QRegister 48 n)
    (rPGTwist : QRegister 48 n) (rScr : QRegister mScr n) : ApexZeroMuxStepSpecScr v rSum14
    rM48 rPGTwist rScr .identity (fun _ _ ↦ 0) := by
  let rPG45 := rPGTwist.slice 0 45 (by decide)
  refine ⟨.identity, id, fun _ ↦ 1, CleanPhasePermEquiv.identity v rScr rPG45.image, fun β _ ↦
    ⟨?_, ?_⟩⟩
  · simp only [id_eq, add_zero, sub_self, Int.zero_emod]
  · simp only [id_eq, sub_self, DyadicQft64.dyadicTurn, Int.cast_zero, mul_zero, zero_div,
      Complex.exp_zero]
theorem ApexZeroMuxStepSpecScr.seq {Var : Type} [Fintype Var] [DecidableEq Var] {mScr n : ℕ}
    [NeZero (2 ^ n)] {v : Var} {rSum14 : QRegister 14 n} {rM48 : QRegister 48 n}
    {rPGTwist : QRegister 48 n} {rScr : QRegister mScr n}
    (hSP : rSum14.DisjointWires rPGTwist) (hMP : rM48.DisjointWires rPGTwist)
    (hScrP : rScr.DisjointWires rPGTwist) {d₁ d₂ : DynamicCircuit Var n}
    {Δ₁ Δ₂ : (Fin 14 → ZMod 2) → (Fin 48 → ZMod 2) → ℤ}
    (h₁ : ApexZeroMuxStepSpecScr v rSum14 rM48 rPGTwist rScr d₁ Δ₁)
    (h₂ : ApexZeroMuxStepSpecScr v rSum14 rM48 rPGTwist rScr d₂ Δ₂) : ApexZeroMuxStepSpecScr v
    rSum14 rM48 rPGTwist rScr (.seq d₁ d₂) (fun B M ↦ Δ₁ B M + Δ₂ B M) := by
  let rPG45 := rPGTwist.slice 0 45 (by decide)
  have hSub45 : rPG45.image ⊆ rPGTwist.image := QRegister.image_compose_subset rPGTwist _
  have hDisj45 : Disjoint rPG45.image rScr.image := Finset.disjoint_of_subset_left hSub45
      ((QRegExt.disjointWires_iff_disjoint_image rPGTwist rScr).mp
      (QRegister.disjoint_comm.mp hScrP))
  obtain ⟨c₁, f₁, φ₁, hEq₁, hVal₁⟩ := h₁
  obtain ⟨c₂, f₂, φ₂, hEq₂, hVal₂⟩ := h₂
  refine ⟨c₁ ;;ᶜ c₂, f₂ ∘ f₁, fun β ↦ φ₁ β * φ₂ (f₁ β),
    CleanPhasePermEquiv.seq hDisj45 hEq₁ hEq₂, fun β hz ↦ ?_⟩
  have hz₁ : ∀ i : Fin mScr, f₁ β (rScr i) = 0 := fun i ↦ (hEq₁.phasePerm.outside β (rScr i)
      (fun hm ↦ hScrP.apply_not_mem_right i (hSub45 hm))).trans (hz i)
  have hB : (fun s ↦ f₁ β (rSum14 s)) = (fun s ↦ β (rSum14 s)) := funext fun s ↦
      hEq₁.phasePerm.outside β (rSum14 s) (fun hm ↦ hSP.apply_not_mem_right s (hSub45 hm))
  have hM : (fun j ↦ f₁ β (rM48 j)) = (fun j ↦ β (rM48 j)) := funext fun j ↦
      hEq₁.phasePerm.outside β (rM48 j) (fun hm ↦ hMP.apply_not_mem_right j (hSub45 hm))
  obtain ⟨eMod₁, ePhi₁⟩ := hVal₁ β hz
  obtain ⟨eMod₂, ePhi₂⟩ := hVal₂ (f₁ β) hz₁
  rw [hB, hM] at eMod₂ ePhi₂
  refine ⟨?_, ?_⟩
  · have hSplit : (regVal rPG45 (f₂ (f₁ β)) : ℤ) - ((regVal rPG45 β : ℤ) + (Δ₁ (fun s ↦ β
      (rSum14 s)) (fun j ↦ β (rM48 j)) + Δ₂ (fun s ↦ β (rSum14 s)) (fun j ↦ β (rM48 j)))) =
      ((regVal rPG45 (f₁ β) : ℤ) - ((regVal rPG45 β : ℤ) + Δ₁ (fun s ↦ β (rSum14 s)) (fun j ↦
      β (rM48 j)))) + ((regVal rPG45 (f₂ (f₁ β)) : ℤ) - ((regVal rPG45 (f₁ β) : ℤ) + Δ₂ (fun s
      ↦ β (rSum14 s)) (fun j ↦ β (rM48 j)))) := by
      ring
    rw [Function.comp_apply, hSplit, Int.add_emod, eMod₁, eMod₂, add_zero, Int.zero_emod]
  · dsimp only [Function.comp_apply]
    rw [ePhi₁, ePhi₂, DyadicQft64.dyadicTurn_add]
    refine congrArg (DyadicQft64.dyadicTurn 48) ?_; ring
theorem ApexZeroMuxStepSpecScr.toRealizesCleanPair_widenAnc {Var : Type} [Fintype Var]
    [DecidableEq Var] {mScr mAnc n : ℕ} [NeZero (2 ^ n)] (v : Var) (rSum14 : QRegister 14 n)
    (rM48 : QRegister 48 n) (rPGTwist : QRegister 48 n) (rScr : QRegister mScr n)
    (rAnc : QRegister mAnc n) (hSP : rSum14.DisjointWires rPGTwist)
    (hMP : rM48.DisjointWires rPGTwist) (hSM : rSum14.DisjointWires rM48)
    (hSubAnc : rScr.image ⊆ rAnc.image) {dFwd dInv : DynamicCircuit Var n}
    {Δ₀ : (Fin 14 → ZMod 2) → (Fin 48 → ZMod 2) → ℤ}
    (hFwd : ApexZeroMuxStepSpecScr v rSum14 rM48 rPGTwist rScr dFwd Δ₀) (hInv :
    ApexZeroMuxStepSpecScr v rSum14 rM48 rPGTwist rScr dInv (fun B M ↦ -Δ₀ B M)) :
    RealizesCleanPair ((rSum14.concat rM48 hSM).concat rPGTwist
    (QRegExt.disjointWires_concat_left hSP hMP)) rAnc (apexCatModAddZ (14 + 48) (fun γ ↦ Δ₀
    (fun s ↦ γ (Fin.castAdd 48 s)) (fun j ↦ γ (Fin.natAdd 14 j)))) dFwd dInv := by
  let rSys := rSum14.concat rM48 hSM
  let Δ_sys : BitAssignment (14 + 48) → ℤ := fun γ ↦
    Δ₀ (fun s ↦ γ (Fin.castAdd 48 s)) (fun j ↦ γ (Fin.natAdd 14 j))
  have hSysEq : ∀ β : BitAssignment n,
      Δ_sys (fun i ↦ β (rSys i)) = Δ₀ (fun s ↦ β (rSum14 s)) (fun j ↦ β (rM48 j)) := fun β ↦ by
    dsimp only [Δ_sys, rSys]
    have h1 : (fun s : Fin 14 ↦ β ((rSum14.concat rM48 hSM) (Fin.castAdd 48 s))) =
        (fun s ↦ β (rSum14 s)) :=
      funext fun s ↦ congrArg β (QRegister.concat_apply_left rSum14 rM48 hSM s)
    have h2 : (fun j : Fin 48 ↦ β ((rSum14.concat rM48 hSM) (Fin.natAdd 14 j))) =
        (fun j ↦ β (rM48 j)) :=
      funext fun j ↦ congrArg β (QRegister.concat_apply_right rSum14 rM48 hSM j)
    rw [h1, h2]
  obtain ⟨cF, fF, φF, hEqF, hValF⟩ := hFwd
  obtain ⟨cI, fI, φI, hEqI, hValI⟩ := hInv
  exact realizesCleanPair_apexCatModAddZ_of_cleanPhasePerm v rSys rPGTwist rScr rAnc
    (QRegExt.disjointWires_concat_left hSP hMP) hSubAnc Δ_sys hEqF
    (fun β hz ↦ by
      rw [hSysEq β]
      exact hValF β hz)
    hEqI
    (fun β hz ↦ by
      rw [hSysEq β]
      exact hValI β hz)
noncomputable def dApexTruncSkipShiftCore {Var : Type} {mScr n : ℕ}
    (skip sh k : ℕ) (hsk : k + 2 + skip ≤ 48) (hmC : k + 2 ≤ mScr) (hs45 : sh + (k + 2) = 45)
    (isInv : Bool) (v : Var) (bIdx : Fin 14) (cHigh : Circuit n)
    (rSum14 : QRegister 14 n) (rM48 : QRegister 48 n) (rPGTwist : QRegister 48 n)
    (rScr : QRegister mScr n) (hSP : rSum14.DisjointWires rPGTwist)
    (hMP : rM48.DisjointWires rPGTwist) (hScrP : rScr.DisjointWires rPGTwist)
    (hScrM : rScr.DisjointWires rM48) : DynamicCircuit Var n :=
  let rPG45 := rPGTwist.slice 0 45 (by decide)
  let wB := rSum14 bIdx
  let rC : QRegister (k + 2) n := rScr.slice 0 (k + 2) (by omega)
  let cPrep := cOptX (!isInv) wB
  .seq (.circuit cPrep)
    (.seq
      (.seq (.circuit cHigh)
        (ctrlSignApexShiftDyn v sh k hs45 wB
          (fun j : Fin (k + 2) ↦ rM48 ⟨j.val + skip, by omega⟩) rPG45 rC
          (fun hm_in ↦ hSP.apply_not_mem_right bIdx
            (QRegister.image_compose_subset rPGTwist _
              (QRegister.image_compose_subset rPG45 _ hm_in)))
          (fun j hm_in ↦ hMP.apply_not_mem_right ⟨j.val + skip, by omega⟩
            (QRegister.image_compose_subset rPGTwist _
              (QRegister.image_compose_subset rPG45 _ hm_in)))
          (fun j hm_in ↦ hScrM.apply_not_mem_left ⟨j.val + skip, by omega⟩
            (QRegister.image_compose_subset rScr _ hm_in))
          (QRegister.disjoint_comm.mp
            (QRegExt.disjointWires_mono_right
              (QRegExt.disjointWires_mono_left hScrP (QRegister.image_compose_subset rScr _))
              ((QRegister.image_compose_subset rPG45 _).trans
                (QRegister.image_compose_subset rPGTwist _))))))
      (.circuit cPrep))
noncomputable def dApexTruncSkipShiftNeg1Scr {Var : Type} {mScr n : ℕ} (skip : ℕ)
    (hsk12 : 12 ≤ skip) (hsk20 : skip ≤ 20) (hmScr : 46 - skip ≤ mScr) (isInv : Bool)
    (v : Var) (rSum14 : QRegister 14 n) (rM48 : QRegister 48 n) (rPGTwist : QRegister 48 n)
    (rScr : QRegister mScr n) (hSP : rSum14.DisjointWires rPGTwist)
    (hMP : rM48.DisjointWires rPGTwist) (hSM : rSum14.DisjointWires rM48)
    (hScrP : rScr.DisjointWires rPGTwist) (_hScrS : rScr.DisjointWires rSum14)
    (hScrM : rScr.DisjointWires rM48) : DynamicCircuit Var n :=
  dApexTruncSkipShiftCore skip (skip - 1) (44 - skip) (by omega) (by omega) (by omega)
    isInv v 0
    (cQuantumQuarterTurn (rSum14 0) (rM48 ⟨47, by decide⟩) (hSM.ne 0 ⟨47, by decide⟩) ;;ᶜ
      ((Circuit.S (rSum14 0)).inverse ;;ᶜ
        cQuantumEighthTurn (rSum14 0) (rM48 ⟨46, by decide⟩) (hSM.ne 0 ⟨46, by decide⟩)))
    rSum14 rM48 rPGTwist rScr hSP hMP hScrP hScrM
@[local simp] theorem count_dApexTruncSkipShiftNeg1Scr_toff {Var : Type} {mScr n : ℕ}
    (skip : ℕ) (hsk12 : 12 ≤ skip) (hsk20 : skip ≤ 20) (hmScr : 46 - skip ≤ mScr)
    (isInv : Bool) (v : Var) (rSum14 : QRegister 14 n) (rM48 : QRegister 48 n)
    (rPGTwist : QRegister 48 n) (rScr : QRegister mScr n)
    (hSP : rSum14.DisjointWires rPGTwist) (hMP : rM48.DisjointWires rPGTwist)
    (hSM : rSum14.DisjointWires rM48) (hScrP : rScr.DisjointWires rPGTwist)
    (hScrS : rScr.DisjointWires rSum14) (hScrM : rScr.DisjointWires rM48) :
    (dApexTruncSkipShiftNeg1Scr skip hsk12 hsk20 hmScr isInv v rSum14 rM48 rPGTwist rScr hSP
    hMP hSM hScrP hScrS hScrM).count .TOFF = 0 := by
  rw [dApexTruncSkipShiftNeg1Scr, dApexTruncSkipShiftCore]
  simp only [NuclearTwistMulKickAndBridge288.count_dyn_seq, dyn_count_circuit,
    count_cOptX_toff, Circuit.count_seq, count_cQuantumQuarterTurn_toff,
    count_cQuantumEighthTurn_toff, count_ctrlSignApexShiftDyn_toff]
  rfl
@[local simp] theorem count_dApexTruncSkipShiftNeg1Scr_t {Var : Type} {mScr n : ℕ} (skip : ℕ)
    (hsk12 : 12 ≤ skip) (hsk20 : skip ≤ 20) (hmScr : 46 - skip ≤ mScr) (isInv : Bool)
    (v : Var) (rSum14 : QRegister 14 n) (rM48 : QRegister 48 n) (rPGTwist : QRegister 48 n)
    (rScr : QRegister mScr n) (hSP : rSum14.DisjointWires rPGTwist)
    (hMP : rM48.DisjointWires rPGTwist) (hSM : rSum14.DisjointWires rM48)
    (hScrP : rScr.DisjointWires rPGTwist) (hScrS : rScr.DisjointWires rSum14)
    (hScrM : rScr.DisjointWires rM48) : (dApexTruncSkipShiftNeg1Scr skip hsk12 hsk20 hmScr
    isInv v rSum14 rM48 rPGTwist rScr hSP hMP hSM hScrP hScrS hScrM).count .T = 4 *
    (46 - skip) + 2 := by
  rw [dApexTruncSkipShiftNeg1Scr, dApexTruncSkipShiftCore]
  simp only [NuclearTwistMulKickAndBridge288.count_dyn_seq, dyn_count_circuit,
    count_cOptX_t, Circuit.count_seq, count_cQuantumQuarterTurn_t,
    count_cQuantumEighthTurn_t, count_ctrlSignApexShiftDyn_t]
  have hSD : ((Circuit.S (rSum14 0)).inverse).count .T = 0 := rfl
  rw [hSD]
  omega
theorem apexTruncSkipShiftCore_step {Var : Type} [Fintype Var] [DecidableEq Var]
    {mScr n : ℕ} [NeZero (2 ^ n)]
    (skip sh k : ℕ) (hsk : k + 2 + skip ≤ 48) (hmC : k + 2 ≤ mScr) (hs45 : sh + (k + 2) = 45)
    (isInv : Bool) (v : Var) (bIdx : Fin 14) (cHigh : Circuit n) (φHigh : BitAssignment n → ℂ)
    (rSum14 : QRegister 14 n) (rM48 : QRegister 48 n) (rPGTwist : QRegister 48 n)
    (rScr : QRegister mScr n) (hSP : rSum14.DisjointWires rPGTwist)
    (hMP : rM48.DisjointWires rPGTwist) (hSM : rSum14.DisjointWires rM48)
    (hScrP : rScr.DisjointWires rPGTwist) (hScrS : rScr.DisjointWires rSum14)
    (hScrM : rScr.DisjointWires rM48)
    (hPPHigh : PhasePerm (rPGTwist.slice 0 45 (by decide)).image cHigh φHigh id)
    (Δ : (Fin 14 → ZMod 2) → (Fin 48 → ZMod 2) → ℤ)
    (hGoal : ∀ β : BitAssignment n,
      let β₁ := fOptX (!isInv) (rSum14 bIdx) β
      let M : Fin 48 → ZMod 2 := fun j ↦ β (rM48 j)
      let sgn : ℤ := (if isInv then -1 else 1) * (2 * ((β (rSum14 bIdx)).val : ℤ) - 1)
      let Lo : ℤ := sgn * (2 ^ sh : ℤ) * (bitsVal (fun j : Fin (k + 2) ↦ M ⟨j.val + skip,
        by omega⟩) : ℤ)
      (∀ j : Fin 48, β₁ (rM48 j) = M j) →
      1 - 2 * ((β₁ (rSum14 bIdx)).val : ℤ) = sgn →
      (Lo - Δ (fun s ↦ β (rSum14 s)) M) % (2 ^ 45 : ℤ) = 0 ∧
      ∃ E : ℤ, φHigh β₁ = DyadicQft64.dyadicTurn 48 E ∧
        ((E + Lo + (2 ^ 45 : ℤ) * ((β₁ (rSum14 bIdx)).val : ℤ)) -
          Δ (fun s ↦ β (rSum14 s)) M) % (2 ^ 48 : ℤ) = 0) :
    ApexZeroMuxStepSpecScr v rSum14 rM48 rPGTwist rScr
      (dApexTruncSkipShiftCore skip sh k hsk hmC hs45 isInv v bIdx cHigh rSum14 rM48
        rPGTwist rScr hSP hMP hScrP hScrM) Δ := by
  let rPG45 := rPGTwist.slice 0 45 (by decide)
  let wB := rSum14 bIdx
  let rC : QRegister (k + 2) n := rScr.slice 0 (k + 2) (by omega)
  have hwB_PG45 : wB ∉ rPG45.image := fun hm_in ↦
    hSP.apply_not_mem_right bIdx (QRegister.image_compose_subset rPGTwist _ hm_in)
  have hwB_C : wB ∉ rC.image := fun hm_in ↦
    hScrS.apply_not_mem_left bIdx (QRegister.image_compose_subset rScr _ hm_in)
  obtain ⟨cSh, fSh, φSh, hEqSh, hValSh⟩ :=
    ctrlSignApexShift_spec v sh k hs45 wB
      (fun j : Fin (k + 2) ↦ rM48 ⟨j.val + skip, by omega⟩) rPG45 rC
      (fun hm_in ↦ hwB_PG45 (QRegister.image_compose_subset rPG45 _ hm_in)) hwB_C
      (fun j hm_in ↦ hMP.apply_not_mem_right ⟨j.val + skip, by omega⟩
        (QRegister.image_compose_subset rPGTwist _ (QRegister.image_compose_subset rPG45 _ hm_in)))
      (fun j hm_in ↦ hScrM.apply_not_mem_left ⟨j.val + skip, by omega⟩
        (QRegister.image_compose_subset rScr _ hm_in))
      (QRegister.disjoint_comm.mp
        (QRegExt.disjointWires_mono_right
          (QRegExt.disjointWires_mono_left hScrP (QRegister.image_compose_subset rScr _))
          ((QRegister.image_compose_subset rPG45 _).trans (QRegister.image_compose_subset rPGTwist
            _))))
  have hDisjPC : Disjoint rPG45.image rC.image := Finset.disjoint_of_subset_left
    (QRegister.image_compose_subset rPGTwist _) (Finset.disjoint_of_subset_right
      (QRegister.image_compose_subset rScr _) ((QRegExt.disjointWires_iff_disjoint_image
      rPGTwist rScr).mp (QRegister.disjoint_comm.mp hScrP)))
  have hConj := CleanPhasePermEquiv.widenAnc (QRegister.image_compose_subset rScr _)
    (CleanPhasePermEquiv.conjLocalPerm (localPerm_cOptX (!isInv) wB) (localPerm_cOptX (!isInv) wB)
      (fOptX_self_inv (!isInv) wB) (Finset.disjoint_singleton_left.mpr hwB_PG45)
      (Finset.disjoint_singleton_left.mpr hwB_C)
      (CleanPhasePermEquiv.seq hDisjPC (CleanPhasePermEquiv.ofCircuit v rC hPPHigh) hEqSh))
  refine ⟨_, _, _, hConj, fun β hz ↦ ?_⟩
  let β₁ := fOptX (!isInv) wB β
  have hOutPG : regVal rPG45 (fun w ↦ if w ∈ rPG45.image then fSh β₁ w else β w) = regVal rPG45 (fSh
    β₁) :=
    regVal_congr rPG45 fun q ↦ by simp [(QRegister.mem_image rPG45 _).mpr ⟨q, rfl⟩]
  have hInPG : regVal rPG45 β₁ = regVal rPG45 β := regVal_congr rPG45 fun q ↦ by
    have hqP : rPG45 q ∈ rPG45.image := (QRegister.mem_image rPG45 _).mpr ⟨q, rfl⟩
    have hneB : rPG45 q ≠ wB := fun h ↦ hwB_PG45 (h ▸ hqP)
    dsimp only [β₁, fOptX]
    exact Function.update_of_ne hneB _ _
  have hz₁ : ∀ i : Fin (k + 2), β₁ (rC i) = 0 := fun i ↦ by
    have hiC : rC i ∈ rC.image := (QRegister.mem_image rC _).mpr ⟨i, rfl⟩
    have hneB : rC i ≠ wB := fun h ↦ hwB_C (h ▸ hiC)
    dsimp only [β₁, fOptX]
    rw [Function.update_of_ne hneB]
    exact zero_of_mem_scr hz (QRegister.image_compose_subset rScr _ hiC)
  have hM₁ : ∀ j : Fin 48, β₁ (rM48 j) = β (rM48 j) := fun j ↦ by
    have hneB : rM48 j ≠ wB := (hSM.ne bIdx j).symm
    dsimp only [β₁, fOptX]
    exact Function.update_of_ne hneB _ _
  have hM_lo : (fun j : Fin (k + 2) ↦ β₁ (rM48 ⟨j.val + skip, by omega⟩)) =
      (fun j : Fin (k + 2) ↦ β (rM48 ⟨j.val + skip, by omega⟩)) :=
    funext fun j ↦ hM₁ ⟨j.val + skip, by omega⟩
  obtain ⟨hModLo, hPhiLo⟩ := hValSh β₁ hz₁
  rw [hInPG, hM_lo] at hModLo hPhiLo
  have hSgnEq : 1 - 2 * ((β₁ wB).val : ℤ) = (if isInv then -1 else 1) * (2 * ((β wB).val : ℤ) -
    1) := by
    have hwB₁ : β₁ wB = β wB + if !isInv then 1 else 0 := by
      dsimp only [β₁, fOptX]
      exact Function.update_self _ _ _
    rw [hwB₁]
    exact quantum_sign_bit_eq isInv (β wB)
  rw [hSgnEq] at hModLo hPhiLo
  obtain ⟨hModDiff, E, hE, hMod48⟩ := hGoal β hM₁ hSgnEq
  have hβ₁_def : fOptX (!isInv) wB β = β₁ := rfl
  refine ⟨?_, ?_⟩
  · dsimp only [Function.comp_apply, id_eq]
    rw [hβ₁_def, hOutPG]
    have hSplit : (regVal rPG45 (fSh β₁) : ℤ) - ((regVal rPG45 β : ℤ) + Δ (fun s ↦ β (rSum14 s))
      (fun j ↦ β (rM48 j))) =
        ((regVal rPG45 (fSh β₁) : ℤ) - ((regVal rPG45 β : ℤ) +
          ((if isInv then -1 else 1) * (2 * ((β wB).val : ℤ) - 1)) * (2 ^ sh : ℤ) *
            (bitsVal (fun j : Fin (k + 2) ↦ β (rM48 ⟨j.val + skip, by omega⟩)) : ℤ))) +
        (((if isInv then -1 else 1) * (2 * ((β wB).val : ℤ) - 1)) * (2 ^ sh : ℤ) *
            (bitsVal (fun j : Fin (k + 2) ↦ β (rM48 ⟨j.val + skip, by omega⟩)) : ℤ) -
          Δ (fun s ↦ β (rSum14 s)) (fun j ↦ β (rM48 j))) := by
      ring
    rw [hSplit, Int.add_emod, hModLo, hModDiff, add_zero, Int.zero_emod]
  · dsimp only [Function.comp_apply, id_eq]
    rw [hβ₁_def, hOutPG, hE, hPhiLo, DyadicQft64.dyadicTurn_add]
    apply DyadicQft64.dyadicTurn_eq_of_emod_eq 48
    apply Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr
    refine Eq.trans (congrArg (· % (2 ^ 48 : ℤ)) ?_) hMod48
    ring
theorem dApexTruncSkipShiftNeg1Scr_spec {Var : Type} [Fintype Var] [DecidableEq Var]
    {mScr n : ℕ} [NeZero (2 ^ n)] (skip : ℕ) (hsk12 : 12 ≤ skip) (hsk20 : skip ≤ 20)
    (hmScr : 46 - skip ≤ mScr) (isInv : Bool) (v : Var) (rSum14 : QRegister 14 n)
    (rM48 : QRegister 48 n) (rPGTwist : QRegister 48 n) (rScr : QRegister mScr n)
    (hSP : rSum14.DisjointWires rPGTwist) (hMP : rM48.DisjointWires rPGTwist)
    (hSM : rSum14.DisjointWires rM48) (hScrP : rScr.DisjointWires rPGTwist)
    (hScrS : rScr.DisjointWires rSum14) (hScrM : rScr.DisjointWires rM48) :
    ApexZeroMuxStepSpecScr v rSum14 rM48 rPGTwist rScr (dApexTruncSkipShiftNeg1Scr skip hsk12
    hsk20 hmScr isInv v rSum14 rM48 rPGTwist rScr hSP hMP hSM hScrP hScrS hScrM) (fun B M ↦
    (if isInv then -1 else 1) * (((B 0).val : ℤ) * (bitsVal (mEffBits skip M) : ℤ) - (bitsVal
    (fun j : Fin 47 ↦ mEffBits skip M j.succ) : ℤ))) := by
  rw [dApexTruncSkipShiftNeg1Scr]
  refine apexTruncSkipShiftCore_step skip (skip - 1) (44 - skip) (by omega) (by omega)
    (by omega) isInv v 0 _ _ rSum14 rM48 rPGTwist rScr hSP hMP hSM hScrP hScrS hScrM
    (((phasePerm_cQuantumQuarterTurn (rSum14 0) (rM48 ⟨47, by decide⟩)
        (hSM.ne 0 ⟨47, by decide⟩)).seq
      ((phasePerm_SDag48 (rSum14 0)).seq
        (phasePerm_cQuantumEighthTurn (rSum14 0) (rM48 ⟨46, by decide⟩)
          (hSM.ne 0 ⟨46, by decide⟩)))).mono (Finset.empty_subset _)) _
    (fun β hM₁ hSgnEq ↦ ?_)
  let k0 : ℕ := 44 - skip
  let M : Fin 48 → ZMod 2 := fun j ↦ β (rM48 j)
  let sgn : ℤ := (if isInv then -1 else 1) * (2 * ((β (rSum14 0)).val : ℤ) - 1)
  have hk0_eq : bitsVal (fun j : Fin (46 - skip) ↦ M ⟨j.val + skip, by omega⟩) =
      bitsVal (fun j : Fin (k0 + 2) ↦ M ⟨j.val + skip, by omega⟩) := by
    unfold bitsVal
    exact Finset.sum_bij (fun i _ ↦ ⟨i.val, by omega⟩) (fun _ _ ↦ Finset.mem_univ _)
      (fun a b _ _ h ↦ Fin.ext (congrArg (fun x : Fin (k0 + 2) ↦ x.val) h))
      (fun j _ ↦ ⟨⟨j.val, by omega⟩, Finset.mem_univ _, rfl⟩) (fun _ _ ↦ rfl)
  have hTargetEq : (if isInv then -1 else 1) *
      (((β (rSum14 0)).val : ℤ) * (bitsVal (mEffBits skip M) : ℤ) -
        (bitsVal (fun j : Fin 47 ↦ mEffBits skip M j.succ) : ℤ)) =
      sgn * (2 ^ (skip - 1) : ℤ) * (bitsVal (fun j : Fin (k0 + 2) ↦ M ⟨j.val + skip, by omega⟩) : ℤ)
        +
        sgn * (2 ^ 45 : ℤ) * ((M ⟨46, by decide⟩).val : ℤ) +
        sgn * (2 ^ 46 : ℤ) * ((M ⟨47, by decide⟩).val : ℤ) := by
    have hSp := bitsVal_W_split (skip := skip) (by omega) (by omega) M
    rw [hk0_eq] at hSp
    have h2sk : ((2 ^ skip : ℕ) : ℤ) = 2 * (2 ^ (skip - 1) : ℤ) := by
      conv_lhs => rw [show skip = (skip - 1) + 1 by omega, pow_add, pow_one]
      push_cast
      ring
    have h2sk1 : ((2 ^ (skip - 1) : ℕ) : ℤ) = (2 ^ (skip - 1) : ℤ) := by
      push_cast
      rfl
    rw [bitsVal_mEffBits_eq (skip := skip) (by omega) M,
      bitsVal_47_mEffBits_eq (skip := skip) (by omega) (by omega) M,
      Nat.cast_mul, Nat.cast_mul, h2sk, h2sk1]
    dsimp only [sgn]
    calc _ = ((if isInv then (-1 : ℤ) else 1) * (2 * ((β (rSum14 0)).val : ℤ) - 1)) *
        ((2 ^ (skip - 1) : ℤ) * (bitsVal (fun j : Fin (48 - skip) ↦ M ⟨j.val + skip, by omega⟩) :
          ℤ)) := by ring
      _ = _ := by
        rw [hSp]
        ring
  let β₁ := fOptX (!isInv) (rSum14 0) β
  let E : ℤ := sgn * (2 ^ 46 : ℤ) * ((M ⟨47, by decide⟩).val : ℤ) +
    (-(2 ^ 46 : ℤ) * ((β₁ (rSum14 0)).val : ℤ) +
      (sgn * (2 ^ 45 : ℤ) * ((M ⟨46, by decide⟩).val : ℤ) +
        (2 ^ 45 : ℤ) * ((β₁ (rSum14 0)).val : ℤ)))
  refine ⟨?_, E, ?_, ?_⟩
  · dsimp only
    rw [hTargetEq]
    exact Int.emod_eq_zero_of_dvd
      ⟨-(sgn * ((M ⟨46, by decide⟩).val : ℤ)) - 2 * sgn * ((M ⟨47, by decide⟩).val : ℤ), by ring⟩
  · dsimp only [Function.comp_apply, id_eq]
    rw [hM₁ ⟨47, by decide⟩, hM₁ ⟨46, by decide⟩, hSgnEq,
      DyadicQft64.dyadicTurn_add, DyadicQft64.dyadicTurn_add]
  · dsimp only [Function.comp_apply, id_eq]
    rw [hTargetEq]
    exact Int.emod_eq_zero_of_dvd ⟨0, by ring⟩
attribute [irreducible] dApexTruncSkipShiftNeg1Scr
noncomputable def dApexTruncSkipShiftStepScr {Var : Type} {mScr n : ℕ} (skip : ℕ)
    (hsk12 : 12 ≤ skip) (hsk20 : skip ≤ 20) (hmScr : 46 - skip ≤ mScr) (isInv : Bool)
    (v : Var) (rSum14 : QRegister 14 n) (rM48 : QRegister 48 n) (rPGTwist : QRegister 48 n)
    (rScr : QRegister mScr n) (hSP : rSum14.DisjointWires rPGTwist)
    (hMP : rM48.DisjointWires rPGTwist) (hSM : rSum14.DisjointWires rM48)
    (hScrP : rScr.DisjointWires rPGTwist) (hScrM : rScr.DisjointWires rM48) (s : ℕ)
    (hs : s < 13) : DynamicCircuit Var n :=
  let k : ℕ := 43 - skip - s
  let wBs := rSum14 ⟨s + 1, by omega⟩
  dApexTruncSkipShiftCore skip (s + skip) k (by omega) (by omega) (by omega)
    isInv v ⟨s + 1, by omega⟩
    (Circuit.Z (rM48 ⟨k + skip + 4, by omega⟩) ;;ᶜ
      (cQuantumQuarterTurn wBs (rM48 ⟨k + skip + 3, by omega⟩)
          (hSM.ne ⟨s + 1, by omega⟩ ⟨k + skip + 3, by omega⟩) ;;ᶜ
        ((Circuit.S wBs).inverse ;;ᶜ
          cQuantumEighthTurn wBs (rM48 ⟨k + skip + 2, by omega⟩)
            (hSM.ne ⟨s + 1, by omega⟩ ⟨k + skip + 2, by omega⟩))))
    rSum14 rM48 rPGTwist rScr hSP hMP hScrP hScrM
@[local simp] theorem count_dApexTruncSkipShiftStepScr_toff {Var : Type} {mScr n : ℕ}
    (skip : ℕ) (hsk12 : 12 ≤ skip) (hsk20 : skip ≤ 20) (hmScr : 46 - skip ≤ mScr)
    (isInv : Bool) (v : Var) (rSum14 : QRegister 14 n) (rM48 : QRegister 48 n)
    (rPGTwist : QRegister 48 n) (rScr : QRegister mScr n)
    (hSP : rSum14.DisjointWires rPGTwist) (hMP : rM48.DisjointWires rPGTwist)
    (hSM : rSum14.DisjointWires rM48) (hScrP : rScr.DisjointWires rPGTwist)
    (hScrM : rScr.DisjointWires rM48) (s : ℕ) (hs : s < 13) : (dApexTruncSkipShiftStepScr skip
    hsk12 hsk20 hmScr isInv v rSum14 rM48 rPGTwist rScr hSP hMP hSM hScrP hScrM s hs).count
    .TOFF = 0 := by
  rw [dApexTruncSkipShiftStepScr, dApexTruncSkipShiftCore]
  simp only [NuclearTwistMulKickAndBridge288.count_dyn_seq, dyn_count_circuit,
    count_cOptX_toff, Circuit.count_seq, count_cQuantumQuarterTurn_toff,
    count_cQuantumEighthTurn_toff, count_ctrlSignApexShiftDyn_toff]
  rfl
@[local simp] theorem count_dApexTruncSkipShiftStepScr_t {Var : Type} {mScr n : ℕ} (skip : ℕ)
    (hsk12 : 12 ≤ skip) (hsk20 : skip ≤ 20) (hmScr : 46 - skip ≤ mScr) (isInv : Bool)
    (v : Var) (rSum14 : QRegister 14 n) (rM48 : QRegister 48 n) (rPGTwist : QRegister 48 n)
    (rScr : QRegister mScr n) (hSP : rSum14.DisjointWires rPGTwist)
    (hMP : rM48.DisjointWires rPGTwist) (hSM : rSum14.DisjointWires rM48)
    (hScrP : rScr.DisjointWires rPGTwist) (hScrM : rScr.DisjointWires rM48) (s : ℕ)
    (hs : s < 13) : (dApexTruncSkipShiftStepScr skip hsk12 hsk20 hmScr isInv v rSum14 rM48
    rPGTwist rScr hSP hMP hSM hScrP hScrM s hs).count .T = 4 * (45 - skip - s) + 2 := by
  rw [dApexTruncSkipShiftStepScr, dApexTruncSkipShiftCore]
  simp only [NuclearTwistMulKickAndBridge288.count_dyn_seq, dyn_count_circuit,
    count_cOptX_t, Circuit.count_seq, count_cQuantumQuarterTurn_t,
    count_cQuantumEighthTurn_t, count_ctrlSignApexShiftDyn_t]
  have hZ : (Circuit.Z (rM48 ⟨43 - skip - s + skip + 4, by omega⟩)).count .T = 0 := rfl
  have hSD : ((Circuit.S (rSum14 ⟨s + 1, by omega⟩)).inverse).count .T = 0 := rfl
  rw [hZ, hSD]
  omega
theorem dApexTruncSkipShiftStepScr_spec {Var : Type} [Fintype Var] [DecidableEq Var]
    {mScr n : ℕ} [NeZero (2 ^ n)] (skip : ℕ) (hsk12 : 12 ≤ skip) (hsk20 : skip ≤ 20)
    (hmScr : 46 - skip ≤ mScr) (isInv : Bool) (v : Var) (rSum14 : QRegister 14 n)
    (rM48 : QRegister 48 n) (rPGTwist : QRegister 48 n) (rScr : QRegister mScr n)
    (hSP : rSum14.DisjointWires rPGTwist) (hMP : rM48.DisjointWires rPGTwist)
    (hSM : rSum14.DisjointWires rM48) (hScrP : rScr.DisjointWires rPGTwist)
    (hScrS : rScr.DisjointWires rSum14) (hScrM : rScr.DisjointWires rM48)
    (s : ℕ) (hs : s < 13) :
    ApexZeroMuxStepSpecScr v rSum14 rM48 rPGTwist rScr
      (dApexTruncSkipShiftStepScr skip hsk12 hsk20 hmScr isInv v rSum14 rM48 rPGTwist rScr
        hSP hMP hSM hScrP hScrM s hs)
      (fun B M ↦ (if isInv then -1 else 1) * (2 * ((B ⟨s + 1, by omega⟩).val : ℤ) - 1) *
        (2 ^ s : ℤ) * (bitsVal (mEffBits skip M) : ℤ)) := by
  let k : ℕ := 43 - skip - s
  let wBs := rSum14 ⟨s + 1, by omega⟩
  rw [dApexTruncSkipShiftStepScr]
  refine apexTruncSkipShiftCore_step skip (s + skip) k (by omega) (by omega) (by omega)
    isInv v ⟨s + 1, by omega⟩ _ _ rSum14 rM48 rPGTwist rScr hSP hMP hSM hScrP hScrS hScrM
    (((phasePerm_Z48 (rM48 ⟨k + skip + 4, by omega⟩)).seq
      ((phasePerm_cQuantumQuarterTurn wBs (rM48 ⟨k + skip + 3, by omega⟩)
          (hSM.ne ⟨s + 1, by omega⟩ ⟨k + skip + 3, by omega⟩)).seq
        ((phasePerm_SDag48 wBs).seq
          (phasePerm_cQuantumEighthTurn wBs (rM48 ⟨k + skip + 2, by omega⟩)
            (hSM.ne ⟨s + 1, by omega⟩ ⟨k + skip + 2, by omega⟩))))).mono
      (Finset.empty_subset _)) _ (fun β hM₁ hSgnEq ↦ ?_)
  let M : Fin 48 → ZMod 2 := fun j ↦ β (rM48 j)
  let sgn : ℤ := (if isInv then -1 else 1) * (2 * ((β wBs).val : ℤ) - 1)
  have hsgn_pm : sgn = 1 ∨ sgn = -1 := by
    dsimp only [sgn]
    rcases bit_cases (β wBs) with hb | hb
    · cases isInv
      · simp [hb, show (0 : ZMod 2).val = 0 from rfl]
      · simp [hb, show (0 : ZMod 2).val = 0 from rfl]
    · cases isInv
      · simp [hb, show (1 : ZMod 2).val = 1 from rfl]
      · simp [hb, show (1 : ZMod 2).val = 1 from rfl]
  let k48 : ℕ := 43 - s
  have hMod48_raw := bitsVal_48_shift_mod48 (show s + (k48 + 2) = 45 by omega) sgn hsgn_pm (mEffBits
    skip M)
  have hLo_k : (2 ^ s : ℤ) * (bitsVal (fun j : Fin (k48 + 2) ↦ mEffBits skip M ⟨j.val, by omega⟩) :
    ℤ) =
      (2 ^ (s + skip) : ℤ) * (bitsVal (fun j : Fin (k + 2) ↦ M ⟨j.val + skip, by omega⟩) : ℤ) := by
    rw [bitsVal_mEffBits_prefix (skip := skip) (m := k48 + 2) (by omega) (by omega) M]
    have hCast : bitsVal (fun j : Fin ((k48 + 2) - skip) ↦ M ⟨j.val + skip, by omega⟩) =
        bitsVal (fun j : Fin (k + 2) ↦ M ⟨j.val + skip, by omega⟩) := by
      unfold bitsVal
      exact Finset.sum_bij (fun i _ ↦ ⟨i.val, by omega⟩) (fun _ _ ↦ Finset.mem_univ _)
        (fun a b _ _ h ↦ Fin.ext (congrArg (fun x : Fin (k + 2) ↦ x.val) h))
        (fun j _ ↦ ⟨⟨j.val, by omega⟩, Finset.mem_univ _, rfl⟩) (fun _ _ ↦ rfl)
    rw [hCast, pow_add]
    push_cast
    ring
  have hkOff (d : ℕ) (hd1 : k48 + d < 48) (hd2 : k + skip + d < 48) (hdge : skip ≤ k48 + d) :
      mEffBits skip M ⟨k48 + d, hd1⟩ = M ⟨k + skip + d, hd2⟩ := by
    rw [mEffBits_of_ge M hdge hd1]
    apply congrArg M
    apply Fin.ext
    dsimp [k48, k]
    omega
  rw [show sgn * (2 ^ s : ℤ) * (bitsVal (fun j : Fin (k48 + 2) ↦ mEffBits skip M ⟨j.val,
    by omega⟩) : ℤ) =
      sgn * (2 ^ (s + skip) : ℤ) * (bitsVal (fun j : Fin (k + 2) ↦ M ⟨j.val + skip, by omega⟩) : ℤ)
        by
      rw [mul_assoc, hLo_k, ← mul_assoc],
    hkOff 2 (by omega) (by omega) (by omega), hkOff 3 (by omega) (by omega) (by omega),
    hkOff 4 (by omega) (by omega) (by omega)] at hMod48_raw
  let β₁ := fOptX (!isInv) wBs β
  let E : ℤ := (2 ^ 47 : ℤ) * ((M ⟨k + skip + 4, by omega⟩).val : ℤ) +
    (sgn * (2 ^ 46 : ℤ) * ((M ⟨k + skip + 3, by omega⟩).val : ℤ) +
      (-(2 ^ 46 : ℤ) * ((β₁ wBs).val : ℤ) +
        (sgn * (2 ^ 45 : ℤ) * ((M ⟨k + skip + 2, by omega⟩).val : ℤ) +
          (2 ^ 45 : ℤ) * ((β₁ wBs).val : ℤ))))
  refine ⟨?_, E, ?_, ?_⟩
  · dsimp only
    obtain ⟨q48, hq48⟩ := Int.dvd_of_emod_eq_zero hMod48_raw
    exact Int.emod_eq_zero_of_dvd ⟨8 * q48 - (sgn * ((M ⟨k + skip + 2, by omega⟩).val : ℤ) +
      2 * sgn * ((M ⟨k + skip + 3, by omega⟩).val : ℤ) + 4 * ((M ⟨k + skip + 4, by omega⟩).val :
        ℤ)),
      by linear_combination hq48⟩
  · dsimp only [Function.comp_apply, id_eq]
    rw [hM₁ ⟨k + skip + 4, by omega⟩, hM₁ ⟨k + skip + 3, by omega⟩, hM₁ ⟨k + skip + 2, by omega⟩,
      hSgnEq, DyadicQft64.dyadicTurn_add, DyadicQft64.dyadicTurn_add, DyadicQft64.dyadicTurn_add]
  · dsimp only [Function.comp_apply, id_eq]
    refine Eq.trans (congrArg (· % (2 ^ 48 : ℤ)) ?_) hMod48_raw
    ring
attribute [irreducible] dApexTruncSkipShiftStepScr
noncomputable def dApexTruncSkipShiftPrefixScr {Var : Type} {mScr n : ℕ}
    (skip : ℕ) (hsk12 : 12 ≤ skip) (hsk20 : skip ≤ 20) (hmScr : 46 - skip ≤ mScr)
    (isInv : Bool) (v : Var)
    (rSum14 : QRegister 14 n) (rM48 : QRegister 48 n)
    (rPGTwist : QRegister 48 n) (rScr : QRegister mScr n)
    (hSP : rSum14.DisjointWires rPGTwist)
    (hMP : rM48.DisjointWires rPGTwist)
    (hSM : rSum14.DisjointWires rM48)
    (hScrP : rScr.DisjointWires rPGTwist)
    (hScrM : rScr.DisjointWires rM48) :
    (m : ℕ) → m ≤ 13 → DynamicCircuit Var n
  | 0, _ => .identity
  | m + 1, hm =>
      .seq
        (dApexTruncSkipShiftPrefixScr skip hsk12 hsk20 hmScr isInv v rSum14 rM48 rPGTwist rScr
          hSP hMP hSM hScrP hScrM m (Nat.le_of_succ_le hm))
        (dApexTruncSkipShiftStepScr skip hsk12 hsk20 hmScr isInv v rSum14 rM48 rPGTwist rScr
          hSP hMP hSM hScrP hScrM m hm)
@[local simp] theorem count_dApexTruncSkipShiftPrefixScr_toff {Var : Type} {mScr n : ℕ}
    (skip : ℕ) (hsk12 : 12 ≤ skip) (hsk20 : skip ≤ 20) (hmScr : 46 - skip ≤ mScr)
    (isInv : Bool) (v : Var) (rSum14 : QRegister 14 n) (rM48 : QRegister 48 n)
    (rPGTwist : QRegister 48 n) (rScr : QRegister mScr n)
    (hSP : rSum14.DisjointWires rPGTwist) (hMP : rM48.DisjointWires rPGTwist)
    (hSM : rSum14.DisjointWires rM48) (hScrP : rScr.DisjointWires rPGTwist)
    (hScrM : rScr.DisjointWires rM48) (m : ℕ) (hm : m ≤ 13) : (dApexTruncSkipShiftPrefixScr
    skip hsk12 hsk20 hmScr isInv v rSum14 rM48 rPGTwist rScr hSP hMP hSM hScrP hScrM m
    hm).count .TOFF = 0 := by
  induction m with
  | zero => rfl
  | succ m ih =>
      simp only [dApexTruncSkipShiftPrefixScr, NuclearTwistMulKickAndBridge288.count_dyn_seq,
        ih (Nat.le_of_succ_le hm), count_dApexTruncSkipShiftStepScr_toff]
theorem count_dApexTruncSkipShiftPrefixScr_t {Var : Type} {mScr n : ℕ} (skip : ℕ)
    (hsk12 : 12 ≤ skip) (hsk20 : skip ≤ 20) (hmScr : 46 - skip ≤ mScr) (isInv : Bool)
    (v : Var) (rSum14 : QRegister 14 n) (rM48 : QRegister 48 n) (rPGTwist : QRegister 48 n)
    (rScr : QRegister mScr n) (hSP : rSum14.DisjointWires rPGTwist)
    (hMP : rM48.DisjointWires rPGTwist) (hSM : rSum14.DisjointWires rM48)
    (hScrP : rScr.DisjointWires rPGTwist) (hScrM : rScr.DisjointWires rM48) (m : ℕ)
    (hm : m ≤ 13) : (dApexTruncSkipShiftPrefixScr skip hsk12 hsk20 hmScr isInv v rSum14 rM48
    rPGTwist rScr hSP hMP hSM hScrP hScrM m hm).count .T = ∑ i : Fin m,
    (4 * (45 - skip - i.val) + 2) := by
  induction m with
  | zero => rfl
  | succ m ih =>
      simp only [dApexTruncSkipShiftPrefixScr, NuclearTwistMulKickAndBridge288.count_dyn_seq,
        ih (Nat.le_of_succ_le hm), count_dApexTruncSkipShiftStepScr_t, Fin.sum_univ_castSucc,
        Fin.val_castSucc, Fin.val_last]
theorem dApexTruncSkipShiftPrefixScr_spec {Var : Type} [Fintype Var] [DecidableEq Var]
    {mScr n : ℕ} [NeZero (2 ^ n)]
    (skip : ℕ) (hsk12 : 12 ≤ skip) (hsk20 : skip ≤ 20) (hmScr : 46 - skip ≤ mScr)
    (isInv : Bool) (v : Var)
    (rSum14 : QRegister 14 n) (rM48 : QRegister 48 n)
    (rPGTwist : QRegister 48 n) (rScr : QRegister mScr n)
    (hSP : rSum14.DisjointWires rPGTwist)
    (hMP : rM48.DisjointWires rPGTwist)
    (hSM : rSum14.DisjointWires rM48)
    (hScrP : rScr.DisjointWires rPGTwist)
    (hScrS : rScr.DisjointWires rSum14)
    (hScrM : rScr.DisjointWires rM48)
    (m : ℕ) (hm : m ≤ 13) :
    ApexZeroMuxStepSpecScr v rSum14 rM48 rPGTwist rScr
      (dApexTruncSkipShiftPrefixScr skip hsk12 hsk20 hmScr isInv v rSum14 rM48 rPGTwist rScr
        hSP hMP hSM hScrP hScrM m hm)
      (fun B M ↦ ∑ i : Fin m,
        (if isInv then -1 else 1) *
          (2 * ((B ⟨i.val + 1, by omega⟩).val : ℤ) - 1) *
          (2 ^ i.val : ℤ) * (bitsVal (mEffBits skip M) : ℤ)) := by
  induction m with
  | zero =>
      rw [dApexTruncSkipShiftPrefixScr]
      have h0 :
          (fun (B : Fin 14 → ZMod 2) (M : Fin 48 → ZMod 2) ↦
            ∑ i : Fin 0,
              (if isInv then -1 else 1) *
                (2 * ((B ⟨i.val + 1, by omega⟩).val : ℤ) - 1) *
                (2 ^ i.val : ℤ) * (bitsVal (mEffBits skip M) : ℤ)) =
          (fun _ _ ↦ 0) := by
        funext B M
        simp only [Finset.univ_eq_empty, Finset.sum_empty]
      rw [h0]
      exact ApexZeroMuxStepSpecScr.identity v rSum14 rM48 rPGTwist rScr
  | succ m ih =>
      rw [dApexTruncSkipShiftPrefixScr]
      have hSeq := ApexZeroMuxStepSpecScr.seq hSP hMP hScrP (ih (Nat.le_of_succ_le hm))
          (dApexTruncSkipShiftStepScr_spec skip hsk12 hsk20 hmScr isInv v rSum14 rM48 rPGTwist
          rScr hSP hMP hSM hScrP hScrS hScrM m hm)
      have hSum :
          (fun (B : Fin 14 → ZMod 2) (M : Fin 48 → ZMod 2) ↦
            (∑ i : Fin m,
              (if isInv then -1 else 1) *
                (2 * ((B ⟨i.val + 1, by omega⟩).val : ℤ) - 1) *
                (2 ^ i.val : ℤ) * (bitsVal (mEffBits skip M) : ℤ)) +
            (if isInv then -1 else 1) *
              (2 * ((B ⟨m + 1, by omega⟩).val : ℤ) - 1) *
              (2 ^ m : ℤ) * (bitsVal (mEffBits skip M) : ℤ)) =
          (fun (B : Fin 14 → ZMod 2) (M : Fin 48 → ZMod 2) ↦
            ∑ i : Fin (m + 1),
              (if isInv then -1 else 1) *
                (2 * ((B ⟨i.val + 1, by omega⟩).val : ℤ) - 1) *
                (2 ^ i.val : ℤ) * (bitsVal (mEffBits skip M) : ℤ)) := by
        funext B M
        rw [Fin.sum_univ_castSucc]
        rfl
      rw [← hSum]
      exact hSeq
attribute [irreducible] dApexTruncSkipShiftPrefixScr
noncomputable def dSlot2ZeroMuxTruncSkip_koffScr {Var : Type} {mScr n : ℕ} (skip : ℕ)
    (hsk12 : 12 ≤ skip) (hsk20 : skip ≤ 20) (hmScr : 46 - skip ≤ mScr) (isInv : Bool)
    (v : Var) (rSum14 : QRegister 14 n) (rM48 : QRegister 48 n) (rPGTwist : QRegister 48 n)
    (rScr : QRegister mScr n) (hSP : rSum14.DisjointWires rPGTwist)
    (hMP : rM48.DisjointWires rPGTwist) (hSM : rSum14.DisjointWires rM48)
    (hScrP : rScr.DisjointWires rPGTwist) (hScrS : rScr.DisjointWires rSum14)
    (hScrM : rScr.DisjointWires rM48) : DynamicCircuit Var n :=
  lockVal <|
    .seq
      (dApexTruncSkipShiftNeg1Scr skip hsk12 hsk20 hmScr isInv v rSum14 rM48 rPGTwist rScr
        hSP hMP hSM hScrP hScrS hScrM)
      (dApexTruncSkipShiftPrefixScr skip hsk12 hsk20 hmScr isInv v rSum14 rM48 rPGTwist rScr
        hSP hMP hSM hScrP hScrM 13 (by decide))
@[local simp] theorem count_dSlot2ZeroMuxTruncSkip_koffScr_toff {Var : Type} {mScr n : ℕ}
    (skip : ℕ) (hsk12 : 12 ≤ skip) (hsk20 : skip ≤ 20) (hmScr : 46 - skip ≤ mScr)
    (isInv : Bool) (v : Var) (rSum14 : QRegister 14 n) (rM48 : QRegister 48 n)
    (rPGTwist : QRegister 48 n) (rScr : QRegister mScr n)
    (hSP : rSum14.DisjointWires rPGTwist) (hMP : rM48.DisjointWires rPGTwist)
    (hSM : rSum14.DisjointWires rM48) (hScrP : rScr.DisjointWires rPGTwist)
    (hScrS : rScr.DisjointWires rSum14) (hScrM : rScr.DisjointWires rM48) :
    (dSlot2ZeroMuxTruncSkip_koffScr skip hsk12 hsk20 hmScr isInv v rSum14 rM48 rPGTwist rScr
    hSP hMP hSM hScrP hScrS hScrM).count .TOFF = 0 := by
  rw [dSlot2ZeroMuxTruncSkip_koffScr, lockVal_eq]
  simp
theorem count_dSlot2ZeroMuxTruncSkip_koffScr_t {Var : Type} {mScr n : ℕ} (skip : ℕ)
    (hsk12 : 12 ≤ skip) (hsk20 : skip ≤ 20) (hmScr : 46 - skip ≤ mScr) (isInv : Bool)
    (v : Var) (rSum14 : QRegister 14 n) (rM48 : QRegister 48 n) (rPGTwist : QRegister 48 n)
    (rScr : QRegister mScr n) (hSP : rSum14.DisjointWires rPGTwist)
    (hMP : rM48.DisjointWires rPGTwist) (hSM : rSum14.DisjointWires rM48)
    (hScrP : rScr.DisjointWires rPGTwist) (hScrS : rScr.DisjointWires rSum14)
    (hScrM : rScr.DisjointWires rM48) : (dSlot2ZeroMuxTruncSkip_koffScr skip hsk12 hsk20 hmScr
    isInv v rSum14 rM48 rPGTwist rScr hSP hMP hSM hScrP hScrS hScrM).count .T =
    (4 * (46 - skip) + 2) + ∑ i : Fin 13, (4 * (45 - skip - i.val) + 2) := by
  rw [dSlot2ZeroMuxTruncSkip_koffScr, lockVal_eq]
  simp [count_dApexTruncSkipShiftPrefixScr_t]
theorem dSlot2ZeroMuxTruncSkip_koffScr_spec {Var : Type} [Fintype Var] [DecidableEq Var]
    {mScr n : ℕ} [NeZero (2 ^ n)] (skip : ℕ) (hsk12 : 12 ≤ skip) (hsk20 : skip ≤ 20)
    (hmScr : 46 - skip ≤ mScr) (isInv : Bool) (v : Var) (rSum14 : QRegister 14 n)
    (rM48 : QRegister 48 n) (rPGTwist : QRegister 48 n) (rScr : QRegister mScr n)
    (hSP : rSum14.DisjointWires rPGTwist) (hMP : rM48.DisjointWires rPGTwist)
    (hSM : rSum14.DisjointWires rM48) (hScrP : rScr.DisjointWires rPGTwist)
    (hScrS : rScr.DisjointWires rSum14) (hScrM : rScr.DisjointWires rM48) :
    ApexZeroMuxStepSpecScr v rSum14 rM48 rPGTwist rScr (dSlot2ZeroMuxTruncSkip_koffScr skip
    hsk12 hsk20 hmScr isInv v rSum14 rM48 rPGTwist rScr hSP hMP hSM hScrP hScrS hScrM)
    (fun B M ↦ (if isInv then -1 else 1) * apexKoffDelta skip B M) := by
  rw [dSlot2ZeroMuxTruncSkip_koffScr, lockVal_eq]
  have hSeq := ApexZeroMuxStepSpecScr.seq hSP hMP hScrP (dApexTruncSkipShiftNeg1Scr_spec skip
      hsk12 hsk20 hmScr isInv v rSum14 rM48 rPGTwist rScr hSP hMP hSM hScrP hScrS hScrM)
      (dApexTruncSkipShiftPrefixScr_spec skip hsk12 hsk20 hmScr isInv v rSum14 rM48 rPGTwist
      rScr hSP hMP hSM hScrP hScrS hScrM 13 (by decide))
  have hDelta :
      (fun (B : Fin 14 → ZMod 2) (M : Fin 48 → ZMod 2) ↦
        (if isInv then -1 else 1) *
          (((B 0).val : ℤ) * (bitsVal (mEffBits skip M) : ℤ) -
            (bitsVal (fun j : Fin 47 ↦ mEffBits skip M j.succ) : ℤ)) +
        ∑ i : Fin 13,
          (if isInv then -1 else 1) *
            (2 * ((B ⟨i.val + 1, by omega⟩).val : ℤ) - 1) *
            (2 ^ i.val : ℤ) * (bitsVal (mEffBits skip M) : ℤ)) =
      (fun (B : Fin 14 → ZMod 2) (M : Fin 48 → ZMod 2) ↦
        (if isInv then -1 else 1) * apexKoffDelta skip B M) := by
    funext B M
    dsimp only [apexKoffDelta]
    exact zeroMux_koff_sum_identity isInv B (mEffBits skip M)
  rw [← hDelta]
  exact hSeq
attribute [irreducible] dSlot2ZeroMuxTruncSkip_koffScr
noncomputable def mkApexKoffMulKickSkipSpecScr (skip mScr tKick : ℕ)
    (hsk12 : 12 ≤ skip) (hsk20 : skip ≤ 20) (hmScr : 46 - skip ≤ mScr)
    (ht : (4 * (46 - skip) + 2) + (∑ i : Fin 13, (4 * (45 - skip - i.val) + 2)) ≤ tKick) :
    ApexKoffMulKickSpec skip mScr tKick where
  dKick := fun isInv _ _ v rSum14 rM48 rPGTwist rScr hSM hSP hMP hSScr hMScr hPScr ↦
    dSlot2ZeroMuxTruncSkip_koffScr skip hsk12 hsk20 hmScr isInv v rSum14 rM48 rPGTwist rScr
      hSP hMP hSM hPScr.symm hSScr.symm hMScr.symm
  hToff := fun isInv _ _ v rSum14 rM48 rPGTwist rScr hSM hSP hMP hSScr hMScr hPScr ↦
    count_dSlot2ZeroMuxTruncSkip_koffScr_toff skip hsk12 hsk20 hmScr isInv v rSum14 rM48 rPGTwist
      rScr
      hSP hMP hSM hPScr.symm hSScr.symm hMScr.symm
  hT := fun isInv _ _ v rSum14 rM48 rPGTwist rScr hSM hSP hMP hSScr hMScr hPScr ↦
    (le_of_eq (count_dSlot2ZeroMuxTruncSkip_koffScr_t skip hsk12 hsk20 hmScr isInv v rSum14 rM48
      rPGTwist rScr
      hSP hMP hSM hPScr.symm hSScr.symm hMScr.symm)).trans ht
  hRealizesPair := fun v rSum14 rM48 rPGTwist rScr hSM hSP hMP hSScr hMScr hPScr ↦ by
    have hFwd0 := dSlot2ZeroMuxTruncSkip_koffScr_spec skip hsk12 hsk20 hmScr false v rSum14 rM48
      rPGTwist rScr
      hSP hMP hSM hPScr.symm hSScr.symm hMScr.symm
    have hInv0 := dSlot2ZeroMuxTruncSkip_koffScr_spec skip hsk12 hsk20 hmScr true v rSum14 rM48
      rPGTwist rScr
      hSP hMP hSM hPScr.symm hSScr.symm hMScr.symm
    have hEqF : (fun B M ↦ (if false then -1 else 1) * apexKoffDelta skip B M) = apexKoffDelta
        skip := by
      funext B M; simp only [Bool.false_eq_true, ↓reduceIte, one_mul]
    have hEqI : (fun B M ↦ (if true then -1 else 1) * apexKoffDelta skip B M) =
        (fun B M ↦ -apexKoffDelta skip B M) := by
      funext B M; simp only [↓reduceIte, neg_one_mul]
    rw [hEqF] at hFwd0; rw [hEqI] at hInv0
    exact ApexZeroMuxStepSpecScr.toRealizesCleanPair_widenAnc v rSum14 rM48 rPGTwist rScr rScr
      hSP hMP hSM (Finset.Subset.refl _) hFwd0 hInv0
/-- Tight `(K - 2)`-scratch `ApexKoffMulKickSpec (48 - K) (K - 2) (tZeroMuxSkip (48 - K))`
for `28 ≤ K ≤ 36`. -/
noncomputable def kickSkipKoffSpecTight (K : ℕ) (hK28 : 28 ≤ K) (hK36 : K ≤ 36) :
    ApexKoffMulKickSpec (48 - K) (K - 2) (tZeroMuxSkip (48 - K)) :=
  mkApexKoffMulKickSkipSpecScr (48 - K) (K - 2) (tZeroMuxSkip (48 - K))
    (by omega) (by omega) (by omega) le_rfl
end TightZeroMuxSkipAndTwistCaps
end
end Config13
end TwistShared108AndLeaf3Bk
end
end TwistShared108AndLeaf3Bk

noncomputable section Slot3NuclearTruncBkPhysics

section
namespace Slot3NuclearTruncBkPhysics
set_option maxRecDepth 65536
set_option exponentiation.threshold 8192
local instance (priority := 1000000) instNeZeroTwoPowSCNucBk (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩
noncomputable section
open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt Real
open scoped Matrix NNReal ComplexOrder MatrixOrder BigOperators Matrix.Norms.L2Operator
open SpecsAux SpecsAux.SpecMirror
open SpecsAux.BridgeFermionicComm
open SpecsAux.BridgeFermionicComm.SpecInner
open SpecsAux.FullScaleBESector
open SpecsAux.SpecMirror.SixChannelHamiltonianSplit
-- Root solution namespace already active.
open PosSlots24MergedVepBound (cellLength_ne_zero)
open ModWrapCoarse8PureMomentum (nearestProtonCoord thetaProtonNearest
  quantizedStructureFactorNearest modWrapProjNucOp modFold3D nonzeroBox3D box3D
  dampedModWrapKernelApprox)
open SubvoxelNuclearTrunc36Physics (trunc36Cfg)
open Slot3MidKick36_161w (modWrapProjNucOp_42_trunc36Cfg)
open MomSlots35Coulomb
open MomSlots35Slot3ProjNuclear.Slot3CleanPrim
open Slot3Exact216Oracle80
attribute [local irreducible] box3D nonzeroBox3D
/-- `bk`-bit nearest-grid nuclear coordinate mantissa in `[0, 2 ^ bk)`. -/
noncomputable def nuclearMBk (bk : ℕ) (c : SpecsAux.SpecMirror.Configuration)
    (l : Fin 216) (w : Fin 3) : ℕ :=
  ⌊(2 ^ bk : ℝ) * Int.fract (c.nuclei l w / cellVolume ^ ((1 : ℝ) / 3)) + 1 / 2⌋₊ % 2 ^ bk
/-- `bk`-bit nearest-grid nuclear coordinate truncation (`truncBkNucCfg bk c`). -/
noncomputable def truncBkNucCfg (bk : ℕ) (c : SpecsAux.SpecMirror.Configuration) :
    SpecsAux.SpecMirror.Configuration where
  nuclei := fun l w ↦
    (nuclearMBk bk c l w : ℝ) * (cellVolume ^ ((1 : ℝ) / 3) / (2 ^ bk : ℝ))
  projectileMomentum := c.projectileMomentum
  momentum_le := c.momentum_le
theorem nearestProtonCoord_36_truncBkNucCfg (bk : ℕ) (hbk36 : bk ≤ 36)
    (c : SpecsAux.SpecMirror.Configuration) (l : Fin 216) (w : Fin 3) : nearestProtonCoord 36
    (SpecsAux.SpecMirror.cellVolume ^ (1 / 3 : ℝ)) ((truncBkNucCfg bk c).nuclei l w) =
    (2 ^ (36 - bk) : ℤ) * (nuclearMBk bk c l w : ℤ) := by
  have hpow : ((1 : ℝ) / 3) = (1 / 3 : ℝ) := rfl
  have hL : SpecsAux.SpecMirror.cellVolume ^ (1 / 3 : ℝ) ≠ 0 := by
    simpa [one_div] using cellLength_ne_zero
  have hp36 : (2 : ℝ) ^ 36 = (2 : ℝ) ^ (36 - bk) * (2 : ℝ) ^ bk := by
    rw [← pow_add]; congr 1; omega
  have hp_ne : (2 : ℝ) ^ bk ≠ 0 := by positivity
  unfold nearestProtonCoord truncBkNucCfg
  dsimp only
  rw [hpow]
  have hval : (2 : ℝ) ^ 36 * ((nuclearMBk bk c l w : ℝ) * (SpecsAux.SpecMirror.cellVolume ^ (1 / 3 :
      ℝ) / (2 ^ bk : ℝ)) / SpecsAux.SpecMirror.cellVolume ^ (1 / 3 : ℝ)) + 1 / 2 =
      (((2 ^ (36 - bk) : ℤ) * (nuclearMBk bk c l w : ℤ) : ℤ) : ℝ) + 1 / 2 := by
    rw [hp36]
    field_simp [hL, hp_ne]
    push_cast
    ring
  rw [hval]
  exact Int.floor_eq_iff.mpr ⟨by linarith, by linarith⟩
theorem nearestProtonCoord_bk_eq_nuclearMBk_add_mul (bk : ℕ) (c : SpecsAux.SpecMirror.Configuration)
    (l : Fin 216) (w : Fin 3) : ∃ k : ℤ, nearestProtonCoord bk
    (SpecsAux.SpecMirror.cellVolume ^ (1 / 3 : ℝ)) (c.nuclei l w) = (nuclearMBk bk c l w : ℤ) +
    (2 ^ bk : ℤ) * k := by
  let L : ℝ := SpecsAux.SpecMirror.cellVolume ^ (1 / 3 : ℝ)
  let x : ℝ := c.nuclei l w / L
  have hx_eq : c.nuclei l w / SpecsAux.SpecMirror.cellVolume ^ ((1 : ℝ) / 3) = x := rfl
  have hx_sp : x = (⌊x⌋ : ℝ) + Int.fract x := (Int.floor_add_fract x).symm
  have hfr_nn : 0 ≤ Int.fract x := Int.fract_nonneg x
  let y : ℝ := (2 ^ bk : ℝ) * Int.fract x + 1 / 2
  have hy_nn : 0 ≤ y := by positivity
  have hy_fl : ⌊y⌋ = (⌊y⌋₊ : ℤ) :=
    Int.floor_eq_iff.mpr ⟨Nat.floor_le hy_nn, by exact_mod_cast Nat.lt_floor_add_one y⟩
  set qy : ℕ := ⌊y⌋₊ / 2 ^ bk
  have hmod : ⌊y⌋₊ = nuclearMBk bk c l w + 2 ^ bk * qy := by
    have hm : nuclearMBk bk c l w = ⌊y⌋₊ % 2 ^ bk := by
      unfold nuclearMBk; rw [hx_eq]
    rw [hm]
    exact (Nat.mod_add_div ⌊y⌋₊ (2 ^ bk)).symm
  refine ⟨⌊x⌋ + (qy : ℤ), ?_⟩
  change ⌊(2 : ℝ) ^ bk * x + 1 / 2⌋ = _
  have hsplit : (2 : ℝ) ^ bk * x + 1 / 2 = y + ((2 ^ bk * ⌊x⌋ : ℤ) : ℝ) := by
    dsimp only [y]
    conv_lhs => rw [hx_sp]
    push_cast
    ring
  rw [hsplit, Int.floor_add_intCast, hy_fl, hmod]
  push_cast
  ring
theorem exp_thetaProtonNearest_36_truncBkNucCfg (bk : ℕ) (hbk36 : bk ≤ 36)
    (c : SpecsAux.SpecMirror.Configuration) (l : Fin 216) (ν : Fin 3 → ℤ) :
    Complex.exp ((thetaProtonNearest 36 (truncBkNucCfg bk c) l ν : ℂ) * Complex.I) =
      Complex.exp ((thetaProtonNearest bk c l ν : ℂ) * Complex.I) := by
  choose k hk using fun w ↦ nearestProtonCoord_bk_eq_nuclearMBk_add_mul bk c l w
  have hp36 : (2 : ℝ) ^ 36 = (2 : ℝ) ^ (36 - bk) * (2 : ℝ) ^ bk := by
    rw [← pow_add]; congr 1; omega
  have hp_ne : (2 : ℝ) ^ (36 - bk) ≠ 0 := by positivity
  have hbk_ne : (2 : ℝ) ^ bk ≠ 0 := by positivity
  have htheta : thetaProtonNearest bk c l ν = thetaProtonNearest 36 (truncBkNucCfg bk c) l ν +
      ((- ∑ w : Fin 3, ν w * k w : ℤ) : ℝ) * (2 * π) := by
    unfold thetaProtonNearest
    have hsum : (∑ w : Fin 3, (ν w : ℝ) * ((nearestProtonCoord bk (SpecsAux.SpecMirror.cellVolume ^
        (1 / 3 : ℝ)) (c.nuclei l w) : ℝ) / (2 : ℝ) ^ bk)) = (∑ w : Fin 3, (ν w : ℝ) *
        ((nearestProtonCoord 36 (SpecsAux.SpecMirror.cellVolume ^ (1 / 3 : ℝ)) ((truncBkNucCfg bk
        c).nuclei l w) : ℝ) / (2 : ℝ) ^ 36)) + ∑ w : Fin 3, (ν w : ℝ) * (k w : ℝ) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun w _ ↦ ?_
      rw [hk w, nearestProtonCoord_36_truncBkNucCfg bk hbk36 c l w, hp36]
      push_cast
      field_simp [hp_ne, hbk_ne]
    rw [hsum]
    push_cast
    ring
  rw [htheta]
  have hcast : ((thetaProtonNearest 36 (truncBkNucCfg bk c) l ν + ((- ∑ w : Fin 3, ν w * k w :
      ℤ) : ℝ) * (2 * π) : ℝ) : ℂ) * Complex.I =
      (thetaProtonNearest 36 (truncBkNucCfg bk c) l ν : ℂ) * Complex.I +
      ((- ∑ w : Fin 3, ν w * k w : ℤ) : ℂ) * (2 * ↑π * Complex.I) := by
    push_cast
    ring
  rw [hcast, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
theorem quantizedStructureFactorNearest_36_truncBkNucCfg (bk : ℕ) (hbk36 : bk ≤ 36)
    (c : SpecsAux.SpecMirror.Configuration) (ν : Fin 3 → ℤ) : quantizedStructureFactorNearest 36
    (truncBkNucCfg bk c) ν = quantizedStructureFactorNearest bk c ν := by
  unfold quantizedStructureFactorNearest
  exact Finset.sum_congr rfl fun l _ ↦ exp_thetaProtonNearest_36_truncBkNucCfg bk hbk36 c l ν
theorem modWrapProjNucOp_36_truncBkNucCfg (bk : ℕ) (hbk36 : bk ≤ 36)
    (c : SpecsAux.SpecMirror.Configuration) (B_rad B_damp : ℕ) (R_3 wt_3 : ℝ) :
    modWrapProjNucOp (truncBkNucCfg bk c) B_rad B_damp 36 R_3 wt_3 =
      modWrapProjNucOp c B_rad B_damp bk R_3 wt_3 := by
  unfold modWrapProjNucOp
  ext x y
  simp only [Matrix.of_apply, quantizedStructureFactorNearest_36_truncBkNucCfg bk hbk36]
/-- For `bk ≤ 36`, `modWrapProjNucOp` on `trunc36Cfg (truncBkNucCfg bk c)` at `Bk = 42`
reduces directly to `modWrapProjNucOp c 38 36 bk (2 / 42) 1`. -/
theorem modWrapProjNucOp_trunc36Cfg_truncBkNucCfg (bk : ℕ) (hbk36 : bk ≤ 36)
    (c : SpecsAux.SpecMirror.Configuration) : modWrapProjNucOp (trunc36Cfg (truncBkNucCfg bk c)) 38
    36 42 (2 / 42) 1 = modWrapProjNucOp c 38 36 bk (2 / 42) 1 := by
  rw [modWrapProjNucOp_42_trunc36Cfg (truncBkNucCfg bk c)]
  exact modWrapProjNucOp_36_truncBkNucCfg bk hbk36 c 38 36 (2 / 42) 1
/-!
## Section 2: `epsNucSlot3Bk` & `s3MomOracleNorm1sBk_errIntrSm`
-/
open Classical in
/-- Per-coset (`ν ∈ nonzeroBox3D 127`) operator slice of `modWrapProjNucOp c 38 36 bk (2 / 42) 1 -
projNucOp c`. -/
noncomputable def slot3ModWrapPieceBk (bk : ℕ) (c : SpecsAux.SpecMirror.Configuration)
    (ν : Fin 3 → ℤ) : Operator (2 ^ SpecsAux.SpecMirror.systemQubits) := Matrix.of fun x y ↦ if
    IsGridState x ∧ IsGridState y ∧ (∀ b ≠ SpecsAux.SpecMirror.Particle.projectile,
    SpecsAux.SpecMirror.momentum x b = SpecsAux.SpecMirror.momentum y b) ∧ modFold3D 127
    (SpecsAux.SpecMirror.momentum x .projectile - SpecsAux.SpecMirror.momentum y .projectile) =
      ν then
    (1 : ℂ) * quantizedStructureFactorNearest bk c (SpecsAux.SpecMirror.momentum x .projectile -
    SpecsAux.SpecMirror.momentum y .projectile) * (dampedModWrapKernelApprox 38 36 127 (2 / 42) 2
    (SpecsAux.SpecMirror.momentum x .projectile - SpecsAux.SpecMirror.momentum y .projectile) : ℂ) -
    (SpecsAux.SpecMirror.charge SpecsAux.SpecMirror.Particle.projectile : ℂ) * structureFactor c
    (SpecsAux.SpecMirror.momentum x .projectile - SpecsAux.SpecMirror.momentum y .projectile) *
    (coulombKernel (SpecsAux.SpecMirror.momentum x .projectile - SpecsAux.SpecMirror.momentum y
    .projectile) : ℂ) else 0
end
end Slot3NuclearTruncBkPhysics
end
end Slot3NuclearTruncBkPhysics

end QuantumComputation.Specs.StoppingPowerSolution
end
