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

public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.Slot2ApexGidney46
public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.K6SuperRowTable

set_option Elab.async false

@[expose] public section
set_option allowUnsafeReducibility true

namespace QuantumComputation.Specs.StoppingPowerSolution
open SpecsAux

section PosSlots24MidK6Sub252
local instance (priority := 1000000) instNeZeroTwoPow_MidK6 (k : ℕ) :
    NeZero (2 ^ k) := ⟨(Nat.two_pow_pos k).ne'⟩

public section
set_option maxRecDepth 4000
set_option exponentiation.threshold 256
namespace PosSlots24SpectatorPrunedPhase
open Operator QProg Matrix HermitianMat Real
open scoped Matrix ComplexOrder MatrixOrder BigOperators Circuit.Notation
open SpecsAux.SpecMirror
open OctahedralOrbit Dyadic128CoulombMath
open Dyadic128OrbitTableCert
open PosSlots24BranchConcrete
open StreamingBchComparator
open PosSlots24SemanticBridge
open PrunedQromLookup
open MeasureBranchHadamardSem (projZeroAll projZeroAll_conjTranspose)
open MeasureBranchHadamardSem (RealizesCleanUnitary)
open BchCubeDecoder hiding ket_diagonalSignUnitaryN
namespace MidK6Sub252
section MidK6P3Sec
attribute [local irreducible] k6SuperRow w128OrbitBiasedQ30
  k6ReconTop6BitBool pos24TailMag30 pos24TailSign k6BitNat k6SubGatesPalBit k6Pal24Bit k6P0Bit
  k6P1Bit k6Diff6Bit k6Top6Bit prunedEffIdx
  phaseLookupPrunedCircuit hadamardReg p2t_cPhaseMuxCol64
  k6LoadTreeCircuit k6_cOneHot4Raw
  k6_cPhaseMux4All6Raw k6_cXorDiffTop6Raw

def k6_cCzCol64Raw {n : ℕ} (rOH64 rCol64 : QRegister 64 n)
    (hDisj : rOH64.DisjointWires rCol64) : (k : ℕ) → (hk : k ≤ 64) → Circuit n
  | 0, _ => .identity
  | k + 1, _ =>
      let sl : Fin 64 := ⟨k, by omega⟩
      k6_cCzCol64Raw rOH64 rCol64 hDisj k (by omega) ;;ᶜ
        p2t_czCircuit (rOH64 sl) (rCol64 sl) (hDisj.ne sl sl)

def k6_cCzSweep27Raw {n : ℕ} (fStream : Fin 27 → Bool)
    (rOH64 : QRegister 64 n) (rBuf1728 : QRegister 1728 n)
    (hOHBuf : rOH64.DisjointWires rBuf1728) : (m : ℕ) → (hm : m ≤ 27) → Circuit n
  | 0, _ => .identity
  | m + 1, _ =>
      let col : Fin 27 := ⟨m, by omega⟩
      let hOHCol : rOH64.DisjointWires (k6_rCol64 rBuf1728 col) :=
        QRegister.disjoint_iff.mpr fun s₁ s₂ ↦ by
          simpa only [k6_rCol64_apply] using hOHBuf.ne s₁ _
      k6_cCzSweep27Raw fStream rOH64 rBuf1728 hOHBuf m (by omega) ;;ᶜ
        if fStream col then
          k6_cCzCol64Raw rOH64 (k6_rCol64 rBuf1728 col) hOHCol 64 (le_refl 64)
        else .identity

private theorem k6_cCzSweep27Raw_count_zero {n a : ℕ} (g : PrimitiveGate a)
    (hg : ∀ (x y : Wire n) (h : x ≠ y), (p2t_czCircuit x y h).count g = 0)
    (fStream : Fin 27 → Bool) (rOH64 : QRegister 64 n) (rBuf1728 : QRegister 1728 n)
    (hOHBuf : rOH64.DisjointWires rBuf1728) :
    ∀ (m : ℕ) (hm : m ≤ 27), (k6_cCzSweep27Raw fStream rOH64 rBuf1728 hOHBuf m hm).count g = 0
  | 0, _ => rfl
  | m + 1, _ => by
      have hcol (rC : QRegister 64 n) (hD : rOH64.DisjointWires rC) :
          ∀ k (hk : k ≤ 64), (k6_cCzCol64Raw rOH64 rC hD k hk).count g = 0 := fun k ↦ by
        induction k with
        | zero => exact fun _ ↦ rfl
        | succ k ih => exact fun _ ↦ by simp [k6_cCzCol64Raw, Circuit.count_seq, hg, ih (by omega)]
      dsimp only [k6_cCzSweep27Raw]
      rw [Circuit.count_seq,
        k6_cCzSweep27Raw_count_zero g hg fStream rOH64 rBuf1728 hOHBuf m (by omega)]
      split_ifs <;> simp [hcol]

theorem k6_cCzSweep27Raw_count_toff {n : ℕ} (fStream : Fin 27 → Bool) (rOH64 : QRegister 64 n)
    (rBuf1728 : QRegister 1728 n)
    (hOHBuf : rOH64.DisjointWires rBuf1728) (m : ℕ) (hm : m ≤ 27) : (k6_cCzSweep27Raw fStream rOH64
      rBuf1728 hOHBuf m hm).count PrimitiveGate.TOFF = 0 :=
  k6_cCzSweep27Raw_count_zero .TOFF p2t_czCircuit_count_toff fStream rOH64 rBuf1728 hOHBuf
    m hm

theorem k6_cCzSweep27Raw_count_t {n : ℕ} (fStream : Fin 27 → Bool) (rOH64 : QRegister 64 n)
    (rBuf1728 : QRegister 1728 n)
    (hOHBuf : rOH64.DisjointWires rBuf1728) (m : ℕ) (hm : m ≤ 27) : (k6_cCzSweep27Raw fStream rOH64
      rBuf1728 hOHBuf m hm).count PrimitiveGate.T = 0 :=
  k6_cCzSweep27Raw_count_zero .T p2t_czCircuit_count_t fStream rOH64 rBuf1728 hOHBuf m hm

theorem k6_cCzSweep27Raw_ket {n : ℕ} (fStream : Fin 27 → Bool) (rOH64 : QRegister 64 n) (rBuf1728 :
    QRegister 1728 n)
    (hOHBuf : rOH64.DisjointWires rBuf1728) (sel : Fin 64) (α : BitAssignment n) (hOH : ∀ sl : Fin
      64, α (rOH64 sl) = if sl = sel then 1 else 0) :
    (k6_cCzSweep27Raw fStream rOH64 rBuf1728 hOHBuf 27 (le_refl 27)).eval.1.mulVec (ket α) =
      ((-1 : ℂ) ^ (∑ m : Fin 27,
    if fStream m then α (rBuf1728 ⟨m.val * 64 + sel.val, by omega⟩) else 0).val) • ket α := by
  have hcol (rC : QRegister 64 n) (hD : rOH64.DisjointWires rC) : (k6_cCzCol64Raw rOH64 rC hD 64
    (le_refl 64)).eval.1.mulVec (ket α) =
      ((-1 : ℂ) ^ (α (rC sel)).val) • ket α := by
    have haux : ∀ k (hk : k ≤ 64), (k6_cCzCol64Raw rOH64 rC hD k hk).eval.1.mulVec (ket α) =
        (if sel.val < k then (-1 : ℂ) ^ (α (rC sel)).val else 1) • ket α := fun k ↦ by
      induction k with
      | zero => exact fun _ ↦ by simp [k6_cCzCol64Raw]
      | succ k ih =>
          intro hk
          rw [k6_cCzCol64Raw, p2t_eval_seq_mulVec, ih (by omega), Matrix.mulVec_smul,
            p2t_ket_czCircuit, smul_smul, hOH ⟨k, by omega⟩]
          by_cases hsk : (⟨k, by omega⟩ : Fin 64) = sel
          · simp [← hsk]
          · simp [hsk, show sel.val < k ↔ sel.val < k + 1 by
              have : sel.val ≠ k := fun h ↦ hsk (Fin.ext h.symm); omega]
    simpa [sel.isLt] using haux 64 (le_refl 64)
  rw [← k6_prod_ite_neg_one_pow]
  have haux : ∀ j (hj : j ≤ 27),
      (k6_cCzSweep27Raw fStream rOH64 rBuf1728 hOHBuf j hj).eval.1.mulVec (ket α) =
        (∏ m : Fin j, if fStream ⟨m.val, by omega⟩ then
          (-1 : ℂ) ^ (α (rBuf1728 ⟨m.val * 64 + sel.val, by omega⟩)).val else 1) • ket α :=
    fun j ↦ by
      induction j with
      | zero => exact fun _ ↦ by simp [k6_cCzSweep27Raw]
      | succ j ih =>
          intro hj
          rw [k6_cCzSweep27Raw, p2t_eval_seq_mulVec, ih (by omega), Matrix.mulVec_smul,
            Fin.prod_univ_castSucc]
          by_cases hf : fStream ⟨j, by omega⟩ <;>
            simp [hf, hcol, smul_smul, Fin.val_castSucc, Fin.val_last]
  simpa only [Fin.eta] using haux 27 (le_refl 27)

attribute [local irreducible] k6_cCzCol64Raw k6_cCzSweep27Raw

noncomputable def k6_meas5cTableBit (q : ℕ) (sl : Fin 64) (idx : Fin 30) : ZMod 2 :=
  if h18 : idx.val < 18 then k6Pal24Bit q sl ⟨6 + idx.val, by omega⟩
  else if idx.val = 18 then k6P0Bit q sl
  else if idx.val = 19 then k6P1Bit q sl
  else if h24 : idx.val < 24 then
    k6_oneHot4Val (k6P0Bit q sl) (k6P1Bit q sl) ⟨idx.val - 20, by omega⟩
  else k6Diff6Bit q sl ⟨idx.val - 24, by omega⟩

noncomputable def k6_fixTable (H : ℕ) (hH : H ≤ 1728) (fStream : Fin 27 → Bool) (fBuf : Fin H →
    Bool) (f5c : Fin 30 → Bool) (f7 : Fin 31 → Bool)
    (q : ℕ) : BitAssignment ((1728 - H) + 64) := fun idx ↦
  if hd : idx.val < 1728 - H then
    k6BufBit q ⟨(H + idx.val) % 64, Nat.mod_lt _ (by decide)⟩ ⟨(H + idx.val) / 64, by omega⟩
  else
    let sl : Fin 64 := ⟨idx.val - (1728 - H), by omega⟩
    (∑ m : Fin 27, if fStream m then k6BufBit q sl m else 0) +
    (∑ c : Fin H, if fBuf c then k6_bufWord1728 q ⟨c.val, by omega⟩ else 0) +
    (∑ k : Fin 30, if f5c k then k6_meas5cTableBit q sl k else 0) +
    (∑ b : Fin 31, if f7 b then k6Table31 q sl b else 0)

noncomputable def k6_fixUnbufCircuit {n : ℕ} (H : ℕ) (hH : H ≤ 1728)
    (rDirty : QRegister (1728 - H) n) (rOH64 : QRegister 64 n) (rHi10 rWalk10 : QRegister 10 n)
    (hDirtyOH : rDirty.DisjointWires rOH64) (hHiW : rHi10.DisjointWires rWalk10)
    (hWP2 : rWalk10.DisjointWires (rDirty.concat rOH64 hDirtyOH)) (fStream : Fin 27 → Bool)
    (fBuf : Fin H → Bool) (f5c : Fin 30 → Bool) (f7 : Fin 31 → Bool) : Circuit n :=
  hadamardReg rDirty ;;ᶜ
    phaseLookupPrunedCircuit (rDirty.concat rOH64 hDirtyOH) none 749 rHi10 rWalk10 hHiW hWP2
      (fun _ ↦ CtrlNe.none _) (fun _ ↦ CtrlNe.none _) (fun _ ↦ CtrlNe.none _)
      (k6_fixTable H hH fStream fBuf f5c f7) ;;ᶜ
    hadamardReg rDirty

section FixUnbufEvalShield
attribute [local irreducible] k6BufBit k6_bufWord1728 k6_meas5cTableBit k6Table31

theorem k6_fixUnbufCircuit_eval_ket {n : ℕ} (H : ℕ) (hH : H ≤ 1728)
    (rDirty : QRegister (1728 - H) n) (rOH64 : QRegister 64 n)
    (rHi10 rWalk10 : QRegister 10 n) (hDirtyOH : rDirty.DisjointWires rOH64)
    (hHiW : rHi10.DisjointWires rWalk10)
    (hWP2 : rWalk10.DisjointWires (rDirty.concat rOH64 hDirtyOH))
    (hHiDirty : rHi10.DisjointWires rDirty) (hWDirty : rWalk10.DisjointWires rDirty)
    (fStream : Fin 27 → Bool) (fBuf : Fin H → Bool) (f5c : Fin 30 → Bool) (f7 : Fin 31 → Bool)
    (sel : Fin 64) (α : BitAssignment n) (hW0 : ∀ i : Fin 10, α (rWalk10 i) = 0)
    (hOH : ∀ sl : Fin 64, α (rOH64 sl) = if sl = sel then 1 else 0) :
    let q_eff := prunedEffIdx 10 749 (localIdx rHi10 α).val
    let phaseBit : ZMod 2 :=
      (∑ m : Fin 27, if fStream m then k6BufBit q_eff sel m else 0) +
      (∑ c : Fin H, if fBuf c then k6_bufWord1728 q_eff ⟨c.val, by omega⟩ else 0) +
      (∑ k : Fin 30, if f5c k then k6_meas5cTableBit q_eff sel k else 0) +
      (∑ b : Fin 31, if f7 b then k6Table31 q_eff sel b else 0)
    (k6_fixUnbufCircuit H hH rDirty rOH64 rHi10 rWalk10 hDirtyOH hHiW hWP2
      fStream fBuf f5c f7).eval.1.mulVec (ket α) =
      ((-1 : ℂ) ^ phaseBit.val) • ket (writeReg α rDirty (fun d ↦ α (rDirty d) +
        k6BufBit q_eff ⟨(H + d.val) % 64, Nat.mod_lt _ (by decide)⟩
          ⟨(H + d.val) / 64, by omega⟩)) := by
  intro q_eff phaseBit
  let rP2 := rDirty.concat rOH64 hDirtyOH
  let tbl := k6_fixTable H hH fStream fBuf f5c f7
  let A := (phaseLookupPrunedCircuit rP2 none 749 rHi10 rWalk10 hHiW hWP2
    (fun _ ↦ CtrlNe.none _) (fun _ ↦ CtrlNe.none _) (fun _ ↦ CtrlNe.none _) tbl).eval.1
  let dDirty : BitAssignment (1728 - H) := fun d ↦
    k6BufBit q_eff ⟨(H + d.val) % 64, Nat.mod_lt _ (by decide)⟩ ⟨(H + d.val) / 64, by omega⟩
  let c₀ : ℂ := (-1 : ℂ) ^ phaseBit.val
  have hc₀_sq : c₀ * c₀ = 1 := k6_neg_one_pow_mul_self phaseBit
  have hScaled : ((hadamardReg rDirty).eval.1 * (c₀ • A) * (hadamardReg rDirty).eval.1).mulVec
      (ket α) = ket (writeReg α rDirty (fun d ↦ α (rDirty d) + dDirty d)) := by
    apply hadamardReg_conj_phase_mulVec_ket rDirty (c₀ • A) dDirty α fun γ ↦ ?_
    have hCleanγ (i : Fin 10) : writeReg α rDirty γ (rWalk10 i) = 0 := by
      rw [writeReg_apply_of_not_mem α rDirty γ _ fun ⟨d, hd⟩ ↦ hWDirty.ne i d hd.symm, hW0 i]
    have hHiγ : localIdx rHi10 (writeReg α rDirty γ) = localIdx rHi10 α :=
      localIdx_eq_of_apply_eq_loc rHi10 _ _ fun i ↦
        writeReg_apply_of_not_mem α rDirty γ _ (fun ⟨d, hd⟩ ↦ hHiDirty.ne i d hd.symm)
    rw [Matrix.smul_mulVec, phaseLookupPrunedCircuit_eval_mulVec_ket rP2 none 749 rHi10 rWalk10 hHiW
      hWP2 _ _ _ tbl _ hCleanγ, hHiγ, smul_smul]
    simp only [ctrlVal, one_mul]
    have hSplit : (∑ i : Fin ((1728 - H) + 64), (writeReg α rDirty γ) (rP2 i) * tbl q_eff i) =
      (∑ d : Fin (1728 - H), γ d * dDirty d) + phaseBit := by
      rw [Fin.sum_univ_add]
      refine congrArg₂ (· + ·) (Finset.sum_congr rfl fun d _ ↦ ?_) ?_
      · rw [QRegister.concat_apply_left, writeReg_apply_reg]
        simp [tbl, k6_fixTable, dDirty, d.isLt]
      · rw [Finset.sum_eq_single sel
          (fun sl _ hsl ↦ by
            rw [QRegister.concat_apply_right,
              writeReg_apply_of_not_mem α rDirty γ _ fun ⟨d, hd⟩ ↦ hDirtyOH.ne d sl hd,
              hOH sl, ite_eq_right hsl, zero_mul])
          (fun h ↦ False.elim (h (Finset.mem_univ _))),
          QRegister.concat_apply_right,
          writeReg_apply_of_not_mem α rDirty γ _ fun ⟨d, hd⟩ ↦ hDirtyOH.ne d sel hd,
          hOH sel, ite_eq_left rfl, one_mul]
        simp only [tbl, k6_fixTable, phaseBit,
          show ¬ ((1728 - H) + sel.val < 1728 - H) by omega,
          ↓reduceDIte, Fin.val_natAdd,
          show (⟨(1728 - H) + sel.val - (1728 - H), by omega⟩ : Fin 64) = sel from
            Fin.ext (Nat.add_sub_cancel_left _ _)]
    rw [hSplit, neg_one_pow_zmod2_add, mul_comm ((-1 : ℂ) ^ (∑ d, γ d * dDirty d).val), ← mul_assoc,
      hc₀_sq, one_mul]
  rw [mul_smul_comm, smul_mul_assoc, Matrix.smul_mulVec] at hScaled
  rw [show (k6_fixUnbufCircuit H hH rDirty rOH64 rHi10 rWalk10 hDirtyOH hHiW hWP2
        fStream fBuf f5c f7).eval.1 =
      (hadamardReg rDirty).eval.1 * A * (hadamardReg rDirty).eval.1 by
      simp only [k6_fixUnbufCircuit, A, rP2, tbl, Circuit.eval_seq, Submonoid.coe_mul,
        Matrix.mul_assoc],
    ← hScaled, ← mul_smul, hc₀_sq, one_smul]

end FixUnbufEvalShield

theorem k6_count_substToffoliCircuit_toff {Var : Type} {n : ℕ} (v : Var) (wAnc : Wire n) (c :
    Circuit n) (hc : wAnc ∉ c.support) :
    (DynCircuitExt.substToffoliCircuit v wAnc c hc).count PrimitiveGate.TOFF = 0 := by
  induction c with
  | identity => rfl
  | gate g r => cases g <;> simp [DynCircuitExt.substToffoliCircuit]
  | seq c₁ c₂ ih₁ ih₂ =>
      simp only [DynCircuitExt.substToffoliCircuit, DynamicCircuit.count,
        ih₁ (fun h ↦ hc (Finset.mem_union_left _ h)),
        ih₂ (fun h ↦ hc (Finset.mem_union_right _ h)), add_zero]

theorem k6_count_substToffoliCircuit_t {Var : Type} {n : ℕ} (v : Var) (wAnc : Wire n) (c : Circuit
    n) (hc : wAnc ∉ c.support) :
    (DynCircuitExt.substToffoliCircuit v wAnc c hc).count PrimitiveGate.T = c.count PrimitiveGate.T
      + 4 * c.count PrimitiveGate.TOFF := by
  induction c with
  | identity => rfl
  | gate g r => cases g <;> simp [DynCircuitExt.substToffoliCircuit]
  | seq c₁ c₂ ih₁ ih₂ =>
      simp only [DynCircuitExt.substToffoliCircuit, DynamicCircuit.count, Circuit.count_seq,
        ih₁ (fun h ↦ hc (Finset.mem_union_left _ h)),
        ih₂ (fun h ↦ hc (Finset.mem_union_right _ h))]
      omega

theorem k6_count_cnot_toff {n : ℕ} (c t : Wire n) (h : c ≠ t) :
    (Circuit.CNOT c t h).count PrimitiveGate.TOFF = 0 := by simp [Circuit.CNOT]

theorem k6_count_cnot_t {n : ℕ} (c t : Wire n) (h : c ≠ t) :
    (Circuit.CNOT c t h).count PrimitiveGate.T = 0 := by simp [Circuit.CNOT]

theorem k6_realizesCleanUnitary_ofSubstToffoliCircuit {Var : Type} [Fintype Var]
    [DecidableEq Var] {n mWork : ℕ} [NeZero (2 ^ n)] (v : Var) (f : Fin mWork → Wire n)
    (j₀ : Fin mWork) (c : Circuit n) (hanc : f j₀ ∉ c.support) : RealizesCleanUnitary v
    (projZeroAll mWork f) (DynCircuitExt.substToffoliCircuit v (f j₀) c hanc) c.eval := by
  have hwp : ∀ (c' : Circuit n) (hc' : f j₀ ∉ c'.support) (Θ : CQAssertionCompat Var (2 ^ n)),
      (∀ σ val, Θ (Function.update σ v val) = Θ σ) → ∀ (σ : Store Var) (val : ℤ),
        wp (DynCircuitExt.substToffoliCircuit v (f j₀) c' hc').compile Θ
      (Function.update σ v val) = wp (DynCircuitExt.substToffoliCircuit v (f j₀) c' hc').compile Θ
        σ := by
    intro c' hc' Θ hΘ σ val
    induction c' generalizing Θ σ val with
    | identity =>
        simpa only [DynCircuitExt.substToffoliCircuit, DynamicCircuit.compile_circuit,
          Circuit.compile_identity, wp_qSeq, wp_qIf, wp_skip, wp_abort, wp_assign_eq_compat,
          wp_qAssign_eq_compat, wp_qMeasure_eq_compat] using hΘ σ val
    | gate g r =>
        cases g with
        | toffoli =>
            simpa only [DynCircuitExt.substToffoliCircuit] using
              DynamicCircuit.wp_jonesToffoli_update_self v (r 0) (r 1) (r 2) (f j₀) _ _ _ _
                Θ σ val
        | x | y | z | h | s | t | cnot | swap =>
            simp only [DynCircuitExt.substToffoliCircuit, DynamicCircuit.compile_circuit,
              DynCircuitExt.wp_circuit_compile_compat, wpQAssignCompat, hΘ σ val]
    | seq c₁ c₂ ih₁ ih₂ =>
        simp only [DynCircuitExt.substToffoliCircuit, DynamicCircuit.compile_seq, wp_qSeq]
        exact ih₁ (fun h ↦ hc' (Finset.mem_union_left _ h)) _
          (fun σ' val' ↦ ih₂ (fun h ↦ hc' (Finset.mem_union_right _ h)) Θ hΘ σ' val') σ val
  refine ⟨hwp c hanc, fun Θ hΘ σ ↦ ?_⟩
  let rAnc := QRegister.singleton (f j₀)
  let hJ := @DynCircuitExt.restrictToZeroAncilla_wp_jonesToffoli_of_update_eq_compat
  have hstep : ∀ (c' : Circuit n) (hc' : f j₀ ∉ c'.support) (Ψ : CQAssertionCompat Var (2 ^ n)),
    (∀ σ' val, Ψ (Function.update σ' v val) = Ψ σ') →
      CQAssertion.restrictToZeroAncilla (wp (DynCircuitExt.substToffoliCircuit v (f j₀) c'
        hc').compile Ψ) rAnc =
      CQAssertion.restrictToZeroAncilla (wpQAssignCompat c'.eval Ψ) rAnc := by
    intro c' hc' Ψ hΨ
    induction c' generalizing Ψ with
    | identity =>
        exact funext fun σ' ↦ Subtype.ext (by
          simp [DynCircuitExt.substToffoliCircuit, Circuit.compile_identity, wp_skip])
    | gate g r =>
        cases g with
        | toffoli =>
            have hne {a b : Fin 3} (hab : a ≠ b) : r a ≠ r b :=
              fun h ↦ hab (r.wires.injective h)
            have ha (a : Fin 3) : r a ≠ f j₀ := fun h ↦
              hc' (by simpa only [Circuit.support_gate, QRegister.mem_image] using ⟨a, h⟩)
            have htr : QRegister.triple (r 0) (r 1) (r 2) (hne (by decide)) (hne (by decide)) (hne
              (by decide)) = r :=
              QRegister.ext (Function.Embedding.ext fun i ↦ by fin_cases i <;> rfl)
            dsimp only [DynCircuitExt.substToffoliCircuit, rAnc]
            rw [hJ v (r 0) (r 1) (r 2) (f j₀) (hne (by decide)) (hne (by decide))
              (hne (by decide)) (ha 0) (ha 1) (ha 2) Ψ hΨ]
            simp only [Circuit.TOFF, htr]
        | x | y | z | h | s | t | cnot | swap =>
            simp only [DynCircuitExt.substToffoliCircuit, DynamicCircuit.compile_circuit,
              DynCircuitExt.wp_circuit_compile_compat]
    | seq c₁ c₂ ih₁ ih₂ =>
        have hc₁ : f j₀ ∉ c₁.support := fun h ↦ hc' (Finset.mem_union_left _ h)
        have hc₂ : f j₀ ∉ c₂.support := fun h ↦ hc' (Finset.mem_union_right _ h)
        simp only [DynCircuitExt.substToffoliCircuit, DynamicCircuit.compile_seq, wp_qSeq,
          Circuit.eval_seq]
        let Ψ₂ := wp (DynCircuitExt.substToffoliCircuit v (f j₀) c₂ hc₂).compile Ψ
        have hcomm₁ :=
          DynCircuitExt.circuit_eval_comm_basisOutcomeProjector_of_not_mem_support c₁ rAnc 0
            fun i ↦ by
              fin_cases i
              exact hc₁
        rw [ih₁ hc₁ Ψ₂ (hwp c₂ hc₂ Ψ hΨ),
          ← DynCircuitExt.wp_qAssign_restrictAssertionToZeroAncilla_comm c₁.eval rAnc hcomm₁ Ψ₂,
          ih₂ hc₂ Ψ hΨ,
          DynCircuitExt.wp_qAssign_restrictAssertionToZeroAncilla_comm c₁.eval rAnc hcomm₁,
            wpQAssignCompat_comp]
  have hm := congrArg HermitianMat.mat (congrArg Subtype.val (congrFun (hstep c hanc Θ hΘ) σ))
  rw [CQAssertion.restrictToZeroAncilla_coe, CQAssertion.restrictToZeroAncilla_coe,
    HermitianMat.conj_apply_mat, HermitianMat.conj_apply_mat,
    QRegister.basisOutcomeProjector_conjTranspose] at hm
  have hP_absorb : projZeroAll mWork f * rAnc.basisOutcomeProjector 0 = projZeroAll mWork f := by
    rw [projZeroAll_eq_diagonal, QRegister.basisOutcomeProjector_eq_diagonal,
      Matrix.diagonal_mul_diagonal]
    refine congrArg Matrix.diagonal (funext fun g ↦ ?_)
    by_cases h₁ : ∀ j : Fin mWork, basisBits n g (f j) = 0
    · simp [h₁, (QRegExt.extractIndex_eq_zero_iff rAnc g).mpr fun i ↦ by
        fin_cases i; exact h₁ j₀]
    · simp [h₁]
  have hP_absorb_l : rAnc.basisOutcomeProjector 0 * projZeroAll mWork f = projZeroAll mWork f := by
    simpa only [conjTranspose_mul, projZeroAll_conjTranspose,
      QRegister.basisOutcomeProjector_conjTranspose] using congrArg conjTranspose hP_absorb
  have hwrap (M : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) :
      projZeroAll mWork f * (rAnc.basisOutcomeProjector 0 * M * rAnc.basisOutcomeProjector 0) *
        projZeroAll mWork f = projZeroAll mWork f * M * projZeroAll mWork f := by
    rw [← Matrix.mul_assoc (projZeroAll mWork f) _ (rAnc.basisOutcomeProjector 0),
      ← Matrix.mul_assoc (projZeroAll mWork f) (rAnc.basisOutcomeProjector 0) M,
      hP_absorb, Matrix.mul_assoc (projZeroAll mWork f * M), hP_absorb_l]
  ext1
  rw [HermitianMat.conj_apply_mat, HermitianMat.conj_apply_mat, projZeroAll_conjTranspose]
  exact ((hwrap _).symm.trans
    (congrArg (fun X ↦ projZeroAll mWork f * X * projZeroAll mWork f) hm)).trans (hwrap _)

noncomputable def k6_qOf {n : ℕ} (rOrbit16 : QRegister 16 n) (α : BitAssignment n) : ℕ :=
  prunedEffIdx 10 749 (localIdx (k6_rHi10Of rOrbit16) α).val
noncomputable def k6_selOf {n : ℕ} (rOrbit16 : QRegister 16 n) (α : BitAssignment n) : Fin 64 :=
  localIdx (k6_rSel6Of rOrbit16) α
noncomputable def k6_tStreamOf {n : ℕ} (rOrbit16 : QRegister 16 n) (α : BitAssignment n)
    (m : Fin 27) : ZMod 2 := k6BufBit (k6_qOf rOrbit16 α) (k6_selOf rOrbit16 α) m
end MidK6P3Sec

end MidK6Sub252
set_option maxRecDepth 512
end PosSlots24SpectatorPrunedPhase
end
set_option exponentiation.threshold 256
end PosSlots24MidK6Sub252

section Pass1BarrelIdxLoad273
local instance (priority := 1000000) instNeZeroTwoPow_Pass1BarrelIdxLoad273 (k : ℕ) :
    NeZero (2 ^ k) := ⟨(Nat.two_pow_pos k).ne'⟩

/-
# Pass-1 `8`-Wire `coinBarrelIdxFast` Clean-Workspace Loader & F2-Linearized `MX` Unloader (`273`
Wires)

Implements the Pass-1 barrel index load/unload bracket on `mWB >= 220` clean
workspace wires (`mWB = 273`, splitting `rWB` into `rIdx8 := rWB.slice 0 8` and
`rScr := rWB.slice 8 (mWB - 8)`):
1. `dLoadBarrelIdxFast` (`84` `TempAnd`s = `336 T`, `0` `.TOFF`, `212 <= mScr` clean wires):
   XOR-loads `coinBarrelIdxFast hmPay` into `rIdx8` while returning all `mScr` scratch wires to
   `|0^{mScr}>` so Pass-1 `AnchorMux218` (`236 <= 265` wires) and `dSlot0LocalXorBit5Dyn`
   (`208 <= 265` wires) reuse `rScr`.
2. `dUnloadBarrelIdxFastCont` (`<= 70` `TempAnd`s = `<= 280 T`, `0` `.TOFF`, `105 <= mWB` clean
   wires): F2-linearized phase-fixup continuation for `measureXResetAndBranch` on `rIdx8`, stopping
   before `progOutMux76` (`68` `TempAnd`s) and computing `en && (P_u ^^ (c2 && P_d))` with `2`
   `TempAnd`s (`0 T` on outcome `f = 0`).
3. `dWrapPass1BarrelIdx` (`<= 616 + tBody` `.T`, `0` `.TOFF`, `220 <= mWB`): wrapper
   applying `DynamicCircuit.realizesCleanTableXUncompute` over `rCore.concat rExt`.
-/

public section
section ConfigPass1BarrelIdxLoad273
set_option maxRecDepth 65536
set_option exponentiation.threshold 256

namespace Pass1BarrelIdxLoad273

open Operator Matrix _root_.DynamicCircuit DynCircuitExt QProg HermitianMat
open CoinDispatchedBarrel288
open FullSysCatSegmentBridge FastCoinBarrelDecoder279
open StreamingBchComparator
open MeasureBranchHadamardSem (ket matrix_ext_ket)
open MomSlot0CircuitHalf (padZeroBits)
open scoped Matrix ComplexOrder MatrixOrder Circuit.Notation BigOperators

local instance (priority := 100000) instLoc_Pass1BarrelIdxLoad273_1InstNeZeroTwoPowP1
    (k : ℕ) : NeZero (2 ^ k) := ⟨(Nat.two_pow_pos k).ne'⟩

noncomputable def lockValP1 {α : Sort _} (x : α) : α :=
  Classical.choose (⟨x, rfl⟩ : ∃ y : α, y = x)

theorem lockValP1_eq {α : Sort _} (x : α) : lockValP1 x = x :=
  Classical.choose_spec (⟨x, rfl⟩ : ∃ y : α, y = x)

/- ## Section 1: Generalized Offset/Width `DecStep` to `TempCtx` Compiler (`listToCtxGen`) -/

def decWireNumGen (C off w : ℕ) : ℕ :=
  if w < 3 then 3948 + w else if w < 40 then 3951 + w
  else if w < 61 then 3971 + w else C + off + (w - 61)

theorem decWireNumGen_lt_61 {C off w : ℕ} (hw : w < 61) : decWireNumGen C off w = decWireNum C w :=
  by
  dsimp [decWireNumGen, decWireNum]
  split_ifs <;> omega

theorem decWireNumGen_lt_cur {C off cur w : ℕ} (hC : 4034 ≤ C) (h61 : 61 ≤ cur) (hw : w < cur) :
    decWireNumGen C off w < C + off + (cur - 61) := by
  dsimp [decWireNumGen]
  split_ifs <;> omega

def decWireGen {mPayload : ℕ} (hmPay : 80 ≤ mPayload) (off mClean w : ℕ) (hw : w < 61 +
    mClean) : Wire (fullSysCoreWires mPayload + off + mClean) :=
  ⟨decWireNumGen (fullSysCoreWires mPayload) off w, by
    have := core_lo_4034 hmPay
    dsimp [decWireNumGen]
    split_ifs <;> omega⟩

theorem decWireGen_inj {mPayload off mClean w₁ w₂ : ℕ} (hmPay : 80 ≤ mPayload) {h₁ : w₁ < 61 +
    mClean} {h₂ : w₂ < 61 + mClean}
    (heq : decWireGen hmPay off mClean w₁ h₁ = decWireGen hmPay off mClean w₂ h₂) : w₁ = w₂ := by
  have := core_lo_4034 hmPay
  have hv := congrArg Fin.val heq
  dsimp [decWireGen, decWireNumGen] at hv
  split_ifs at hv <;> omega

def mutIdxWindow (C off : ℕ) {M : ℕ} (q : Wire M) : Prop := C ≤ q.val ∧ q.val < C + off

local instance instLoc_Pass1BarrelIdxLoad273_2_instDecidablePredMut (C off M : ℕ) :
    DecidablePred (mutIdxWindow C off (M := M)) := fun _ ↦ inferInstanceAs (Decidable (_ ∧ _))

theorem decWireGen_nonMut {mPayload off mClean w : ℕ} (hmPay : 80 ≤ mPayload) (hw : w < 61 +
    mClean) :
    ¬ mutIdxWindow (fullSysCoreWires mPayload) off (decWireGen hmPay off mClean w hw) := by
  have := core_lo_4034 hmPay
  dsimp [mutIdxWindow, decWireGen, decWireNumGen]
  split_ifs <;> omega

def bitsOfAssignGen {mPayload : ℕ} (hmPay : 80 ≤ mPayload) (off mClean : ℕ)
    (β : BitAssignment (fullSysCoreWires mPayload + off + mClean)) (w : ℕ) : Bool :=
  if hw : w < 61 + mClean then decide (β (decWireGen hmPay off mClean w hw) = 1) else false

noncomputable def stepToCtxGen {mPayload : ℕ} (hmPay : 80 ≤ mPayload) (off mClean cur : ℕ)
    (h61 : 61 ≤ cur) (hcur : cur ≤ 61 + mClean) :
    (s : DecStep) → s.wellFormed cur = true → s.nextCur cur ≤ 61 + mClean →
    Internal.TempCtx (fullSysCoreWires mPayload + off + mClean)
  | .allocZero, _, _ => .hole
  | .x w, hwf, _ =>
      have hw : w < 61 + mClean := by
        simp only [DecStep.wellFormed, decide_eq_true_eq] at hwf; omega
      Internal.ctxCliffAlloc (.x (decWireGen hmPay off mClean w hw))
  | .cnot src dst, hwf, _ =>
      have h : src ≠ dst ∧ src < cur ∧ dst < cur := by
        simpa only [DecStep.wellFormed, decide_eq_true_eq] using hwf
      Internal.ctxCliffAlloc (.cnot
        (decWireGen hmPay off mClean src (lt_of_lt_of_le h.2.1 hcur))
        (decWireGen hmPay off mClean dst (lt_of_lt_of_le h.2.2 hcur))
        (fun heq ↦ h.1 (decWireGen_inj hmPay heq)))
  | .andAlloc a b, hwf, hnext =>
      have h : a ≠ b ∧ a < cur ∧ b < cur ∧ cur + 1 ≤ 337 := by
        simpa only [DecStep.wellFormed, decide_eq_true_eq] using hwf
      let pos := fullSysCoreWires mPayload + off + (cur - 61)
      have hpos : pos + 1 ≤ fullSysCoreWires mPayload + off + mClean := by
        dsimp [pos, DecStep.nextCur] at hnext ⊢; omega
      Internal.ctxTempBit
        (decWireGen hmPay off mClean a (lt_of_lt_of_le h.2.1 hcur))
        (decWireGen hmPay off mClean b (lt_of_lt_of_le h.2.2.1 hcur))
        ⟨pos, hpos⟩ (fun heq ↦ h.1 (decWireGen_inj hmPay heq))
        (Internal.wire_ne_of_lt (decWireNumGen_lt_cur (core_lo_4034 hmPay) h61 h.2.1))
        (Internal.wire_ne_of_lt (decWireNumGen_lt_cur (core_lo_4034 hmPay) h61 h.2.2.1))

theorem stepToCtxGen_correct {mPayload off mClean cur : ℕ} (hmPay : 80 ≤ mPayload)
    (h61 : 61 ≤ cur) (hcur : cur ≤ 61 + mClean)
    (s : DecStep) (hwf : s.wellFormed cur = true) (hnext : s.nextCur cur ≤ 61 + mClean) :
    let M := fullSysCoreWires mPayload + off + mClean
    let C := fullSysCoreWires mPayload
    let K := stepToCtxGen hmPay off mClean cur h61 hcur s hwf hnext
    61 ≤ s.nextCur cur ∧ K.countTempAnd = s.numAnd ∧
    Internal.CtxSpec (mutIdxWindow C off) (C + off + (cur - 61))
      (C + off + (s.nextCur cur - 61)) K ∧
    (∀ (β : BitAssignment M), Internal.cleanRem M (M - (C + off + (cur - 61))) β →
      ∀ (w : ℕ) (hw : w < 61 + mClean),
        decide (K.fwdBits β (decWireGen hmPay off mClean w hw) = 1) =
          s.stepBool cur (bitsOfAssignGen hmPay off mClean β) w) := by
  have hC := core_lo_4034 hmPay
  let C := fullSysCoreWires mPayload
  let d1 (z : ZMod 2) : Bool := decide (z = 1)
  cases s with
  | allocZero =>
      refine ⟨by simp [DecStep.nextCur]; omega, rfl,
        { disj := trivial, supp := trivial,
          sym := .castOut (by dsimp [DecStep.nextCur]; omega) (.hole _) },
        fun β _ w hw ↦ by
          simp [stepToCtxGen, Internal.TempCtx.fwdBits, DecStep.stepBool,
            bitsOfAssignGen, hw]⟩
  | x q =>
      have hq : q < cur := by simpa [DecStep.wellFormed] using hwf
      have hqB : q < 61 + mClean := lt_of_lt_of_le hq hcur
      have hsp := Internal.CtxSpec.cliff (mutW := mutIdxWindow C off)
        (C + off + (cur - 61)) (by dsimp [C]; omega) (.x (decWireGen hmPay off mClean q hqB))
        (decWireGen_nonMut hmPay hqB) (decWireNumGen_lt_cur hC h61 hq)
      refine ⟨h61, rfl, hsp.1, fun β _ w hw ↦ (congrArg d1 (congrFun (hsp.2 β) _)).trans ?_⟩
      by_cases hwq : w = q
      · subst hwq
        obtain rfl : hw = hqB := Subsingleton.elim _ _
        simp [d1, Internal.CliffProg.eval, zmod2_add_one_decide, DecStep.stepBool,
          bitsOfAssignGen, hw]
      · simp [d1, Internal.CliffProg.eval, DecStep.stepBool,
          Function.update_of_ne (fun h ↦ hwq (decWireGen_inj hmPay h)),
          hwq, bitsOfAssignGen, hw]
  | cnot src dst =>
      have h : src ≠ dst ∧ src < cur ∧ dst < cur := by
        simpa only [DecStep.wellFormed, decide_eq_true_eq] using hwf
      have hs : src < 61 + mClean := lt_of_lt_of_le h.2.1 hcur
      have hd : dst < 61 + mClean := lt_of_lt_of_le h.2.2 hcur
      have hsp := Internal.CtxSpec.cliff (mutW := mutIdxWindow C off)
        (C + off + (cur - 61)) (by dsimp [C]; omega)
        (.cnot (decWireGen hmPay off mClean src hs) (decWireGen hmPay off mClean dst hd)
          (fun heq ↦ h.1 (decWireGen_inj hmPay heq)))
        ⟨decWireGen_nonMut hmPay hs, decWireGen_nonMut hmPay hd⟩
        ⟨decWireNumGen_lt_cur hC h61 h.2.1, decWireNumGen_lt_cur hC h61 h.2.2⟩
      refine ⟨h61, rfl, hsp.1, fun β _ w hw ↦ (congrArg d1 (congrFun (hsp.2 β) _)).trans ?_⟩
      dsimp only [d1, Internal.CliffProg.eval, DecStep.stepBool]
      by_cases hwd : w = dst
      · subst hwd
        simp [Function.update_self, zmod2_add_decide, bitsOfAssignGen, hw, hs]
      · simp [Function.update_of_ne (fun he ↦ hwd (decWireGen_inj hmPay he)), hwd,
          bitsOfAssignGen, hw]
  | andAlloc a b =>
      have h : a ≠ b ∧ a < cur ∧ b < cur ∧ cur + 1 ≤ 337 := by
        simpa only [DecStep.wellFormed, decide_eq_true_eq] using hwf
      have ha : a < 61 + mClean := lt_of_lt_of_le h.2.1 hcur
      have hb : b < 61 + mClean := lt_of_lt_of_le h.2.2.1 hcur
      let pos := C + off + (cur - 61)
      have hpos : pos + 1 ≤ C + off + mClean := by
        dsimp [pos, C, DecStep.nextCur] at hnext ⊢; omega
      have hsp := Internal.CtxSpec.tempBit (mutW := mutIdxWindow C off) pos hpos
        (decWireGen hmPay off mClean a ha) (decWireGen hmPay off mClean b hb)
        (fun heq ↦ h.1 (decWireGen_inj hmPay heq))
        (decWireNumGen_lt_cur hC h61 h.2.1) (decWireNumGen_lt_cur hC h61 h.2.2.1)
        (decWireGen_nonMut hmPay ha) (decWireGen_nonMut hmPay hb)
        (by dsimp [mutIdxWindow, pos]; omega)
      refine ⟨by simp [DecStep.nextCur]; omega, rfl, ?_,
        fun β hβ w hw ↦ (congrArg d1 (congrFun (hsp.2 β hβ) _)).trans ?_⟩
      · dsimp only [stepToCtxGen, DecStep.nextCur]
        rw [show C + off + (cur + 1 - 61) = pos + 1 by dsimp [pos]; omega]
        exact hsp.1
      · have hcurB : cur < 61 + mClean := by dsimp [DecStep.nextCur] at hnext; omega
        have hcur_wire : decWireGen hmPay off mClean cur hcurB = ⟨pos, hpos⟩ := by
          apply Fin.ext
          dsimp [decWireGen, decWireNumGen, pos, C]
          split_ifs <;> omega
        dsimp only [d1, DecStep.stepBool]
        rw [← hcur_wire]
        by_cases hwc : w = cur
        · subst hwc
          simp [Function.update_self, bitsOfAssignGen, ha, hb]
        · simp [Function.update_of_ne (fun he ↦ hwc (decWireGen_inj hmPay he)), hwc,
            bitsOfAssignGen, hw]

noncomputable def listToCtxGen {mPayload : ℕ} (hmPay : 80 ≤ mPayload) (off mClean : ℕ) :
    (p : List DecStep) → (cur : ℕ) → 61 ≤ cur → progEndCur cur p ≤ 61 + mClean →
    progWellFormed cur p = true →
    Internal.TempCtx (fullSysCoreWires mPayload + off + mClean)
  | [], _, _, _, _ => .hole
  | s :: rest, cur, h61, hend, hwf =>
      have hw : s.wellFormed cur = true ∧ progWellFormed (s.nextCur cur) rest = true := by
        simpa only [progWellFormed, Bool.and_eq_true] using hwf
      have hnext_le : s.nextCur cur ≤ 61 + mClean :=
        le_trans (progEndCur_mono rest (s.nextCur cur)) hend
      have hcur_le : cur ≤ 61 + mClean :=
        le_trans (by cases s <;> simp [DecStep.nextCur]) hnext_le
      have h61' : 61 ≤ s.nextCur cur := by
        cases s <;> simp [DecStep.nextCur] <;> omega
      (stepToCtxGen hmPay off mClean cur h61 hcur_le s hw.1 hnext_le).append
        (listToCtxGen hmPay off mClean rest (s.nextCur cur) h61' hend hw.2)

theorem listToCtxGen_correct {mPayload off mClean : ℕ} (hmPay : 80 ≤ mPayload) :
    ∀ (p : List DecStep) (cur : ℕ) (h61 : 61 ≤ cur) (hend : progEndCur cur p ≤ 61 + mClean)
      (hwf : progWellFormed cur p = true),
      let M := fullSysCoreWires mPayload + off + mClean
      let C := fullSysCoreWires mPayload
      let K := listToCtxGen hmPay off mClean p cur h61 hend hwf
      K.countTempAnd = progNumAnd p ∧
      Internal.CtxSpec (mutIdxWindow C off) (C + off + (cur - 61))
        (C + off + (progEndCur cur p - 61)) K ∧
      (∀ (β : BitAssignment M), Internal.cleanRem M (M - (C + off + (cur - 61))) β →
        ∀ (w : ℕ) (hw : w < 61 + mClean),
          decide (K.fwdBits β (decWireGen hmPay off mClean w hw) = 1) =
            evalBool p cur (bitsOfAssignGen hmPay off mClean β) w)
  | [], _, _, _, _ =>
      ⟨rfl, { disj := trivial, supp := trivial, sym := .hole _ }, fun _ _ w hw ↦ by
        simp [listToCtxGen, Internal.TempCtx.fwdBits, evalBool, bitsOfAssignGen, hw]⟩
  | s :: rest, cur, h61, hend, hwf => by
      have hw : s.wellFormed cur = true ∧ progWellFormed (s.nextCur cur) rest = true := by
        simpa only [progWellFormed, Bool.and_eq_true] using hwf
      have hnext_le : s.nextCur cur ≤ 61 + mClean :=
        le_trans (progEndCur_mono rest (s.nextCur cur)) hend
      have hcur_le : cur ≤ 61 + mClean :=
        le_trans (by cases s <;> simp [DecStep.nextCur]) hnext_le
      have hstep := stepToCtxGen_correct (off := off) hmPay h61 hcur_le s hw.1 hnext_le
      obtain ⟨h61', hcnt1, hsp1, hsem1⟩ := hstep
      have hrest := listToCtxGen_correct (off := off) (mClean := mClean) hmPay rest (s.nextCur cur)
        h61' hend hw.2
      obtain ⟨hcnt2, hsp2, hsem2⟩ := hrest
      have hmono : fullSysCoreWires mPayload + off + (s.nextCur cur - 61) ≤ fullSysCoreWires
        mPayload + off + (progEndCur (s.nextCur cur) rest - 61) := by
        have := progEndCur_mono rest (s.nextCur cur); omega
      refine ⟨by dsimp [listToCtxGen]; rw [tempCtx_append_countTempAnd, hcnt1, hcnt2]; rfl,
        by dsimp [listToCtxGen, progEndCur]; exact Internal.CtxSpec.comp hmono hsp1 hsp2,
        fun β hβ w hlt ↦ ?_⟩
      have happ := congrFun (Internal.TempCtx.append_fwdBits
        (stepToCtxGen hmPay off mClean cur h61 hcur_le s hw.1 hnext_le)
        (listToCtxGen hmPay off mClean rest (s.nextCur cur) h61' hend hw.2) β)
        (decWireGen hmPay off mClean w hlt)
      refine (congrArg (fun z : ZMod 2 ↦ decide (z = 1)) happ).trans
        ((hsem2 _ (hsp1.fwd_clean hβ) w hlt).trans ?_)
      dsimp only [evalBool]
      refine congrFun (congrArg (evalBool rest (s.nextCur cur)) (funext fun q ↦ ?_)) w
      by_cases hq : q < 61 + mClean
      · simp only [bitsOfAssignGen, hq, ↓reduceDIte]
        exact hsem1 β hβ q hq
      · have hrhs : s.stepBool cur (bitsOfAssignGen hmPay off mClean β) q = false := by
          have hw1 := hw.1
          cases s with
          | allocZero => simp [DecStep.stepBool, bitsOfAssignGen, hq]
          | x q0 =>
              simp only [DecStep.wellFormed, decide_eq_true_eq] at hw1
              simp [DecStep.stepBool, show q ≠ q0 by omega, bitsOfAssignGen, hq]
          | cnot c0 d0 =>
              simp only [DecStep.wellFormed, decide_eq_true_eq] at hw1
              simp [DecStep.stepBool, show q ≠ d0 by omega, bitsOfAssignGen, hq]
          | andAlloc _ _ =>
              simp [DecStep.stepBool, show q ≠ cur by dsimp [DecStep.nextCur] at hnext_le; omega,
                bitsOfAssignGen, hq]
        simp [bitsOfAssignGen, hq, hrhs]

theorem coinBarrelIdxFastPure_eq_core {mPayload : ℕ} (hmPay : 80 ≤ mPayload)
    (α : BitAssignment (fullSysCoreWires mPayload)) (st₀ : ℕ → Bool)
    (hlow : ∀ (q : ℕ) (_ : q < 61),
      st₀ q = decide (α ⟨decWireNum (fullSysCoreWires mPayload) q,
        by have := core_lo_4034 hmPay; dsimp [decWireNum]; split_ifs <;> omega⟩ = 1)) :
    coinBarrelIdxFastPure st₀ = (coinBarrelIdxFast hmPay α).val := by
  have hC := core_lo_4034 hmPay
  have hu8 : regValList st₀ u8Wires = Internal.bitsVal (fun i : Fin 8 ↦ α ⟨3968 + i.val,
    by omega⟩) := by
    have heq := bitsVal_eq_regValList_ofFn 8 17 st₀ (fun i : Fin 8 ↦ α ⟨3968 + i.val, by omega⟩)
      fun i ↦ by
        rw [zmod2_val_eq_ite_decide, hlow (17 + i.val) (by omega),
          show (⟨decWireNum (fullSysCoreWires mPayload) (17 + i.val), _⟩ :
            Wire (fullSysCoreWires mPayload)) = ⟨3968 + i.val, by omega⟩ from
            Fin.ext (decWireNum_u8_eq (fullSysCoreWires mPayload) i)]
    rw [← show List.ofFn (fun i : Fin 8 ↦ 17 + i.val) = u8Wires by decide, ← heq]
  have hu36 : regValList st₀ u36Wires = Internal.bitsVal (fun i : Fin 36 ↦ α ⟨3954 + i.val,
    by omega⟩) := by
    have heq := bitsVal_eq_regValList_ofFn 36 3 st₀ (fun i : Fin 36 ↦ α ⟨3954 + i.val, by omega⟩)
      fun i ↦ by
        rw [zmod2_val_eq_ite_decide, hlow (3 + i.val) (by omega),
          show (⟨decWireNum (fullSysCoreWires mPayload) (3 + i.val), _⟩ :
            Wire (fullSysCoreWires mPayload)) = ⟨3954 + i.val, by omega⟩ from
            Fin.ext (decWireNum_u36_eq (fullSysCoreWires mPayload) i)]
    rw [← show List.ofFn (fun i : Fin 36 ↦ 3 + i.val) = u36Wires by decide, ← heq]
  have hc1 : st₀ 1 = decide (α (iSlot1 mPayload) = 1) := hlow 1 (by omega)
  have hc2 : st₀ 2 = decide (α (iSlot2 mPayload) = 1) := hlow 2 (by omega)
  dsimp only [coinBarrelIdxFastPure, coinBarrelIdxFast]
  rw [hc1, hc2, hu8, hu36,
    show (if st₀ 39 then 1 else 0) = (α ⟨3990, by omega⟩).val by
      rw [hlow 39 (by omega), ← zmod2_val_eq_ite_decide]
      exact rfl]
  generalize hb1 : decide (α (iSlot1 mPayload) = 1) = b1
  generalize hb2 : decide (α (iSlot2 mPayload) = 1) = b2
  simp only [show (α (iSlot1 mPayload) = 1) ↔ b1 = true from hb1 ▸ zmod2_one_iff _, show (α (iSlot2
    mPayload) = 0) ↔ b2 = false from hb2 ▸ zmod2_zero_iff _]
  cases b1 <;> cases b2 <;> simp
  split_ifs <;> simp

/- ## Section 2: `coinBarrelIdxFastTbl` & `84`-`TempAnd` (`336 T`) Clean Loader
`dLoadBarrelIdxFast` -/

theorem qreg_disjoint_concat_left {k₁ k₂ m n : ℕ} {r₁ : QRegister k₁ n} {r₂ : QRegister k₂ n}
    {r₃ : QRegister m n} {h₁₂ : r₁.DisjointWires r₂} (h₁₃ : r₁.DisjointWires r₃) (h₂₃ :
      r₂.DisjointWires r₃) : (r₁.concat r₂ h₁₂).DisjointWires r₃ :=
  QRegister.disjoint_iff.mpr fun u j ↦ Fin.addCases
    (fun i₁ ↦ by rw [QRegister.concat_apply_left]; exact h₁₃.ne i₁ j)
    (fun i₂ ↦ by rw [QRegister.concat_apply_right]; exact h₂₃.ne i₂ j) u

/-- `8`-bit table value `coinBarrelIdxFast hmPay` read from the `fullSysCoreWires mPayload` prefix
of `fullSysCoreWires mPayload + kExt`. -/
noncomputable def coinBarrelIdxFastTbl {mPayload kExt : ℕ} (hmPay : 80 ≤ mPayload) (x : Fin (2 ^
    (fullSysCoreWires mPayload + kExt))) : Fin (2 ^ 8) :=
  let α : BitAssignment (fullSysCoreWires mPayload) :=
    fun i ↦ basisBits (fullSysCoreWires mPayload + kExt) x (Fin.castAdd kExt i)
  ⟨(coinBarrelIdxFast hmPay α).val, lt_trans (coinBarrelIdxFast hmPay α).isLt (by decide)⟩

theorem coinBarrelIdxFastTbl_val {mPayload kExt : ℕ} (hmPay : 80 ≤ mPayload)
    (x : Fin (2 ^ (fullSysCoreWires mPayload + kExt))) : (coinBarrelIdxFastTbl hmPay x).val =
    (coinBarrelIdxFast hmPay (fun i ↦ basisBits (fullSysCoreWires mPayload + kExt) x (Fin.castAdd
      kExt i))).val := rfl

/-- Involutive computational-basis XOR-load map on `fullSysCoreWires mPayload + 8`. -/
def loadBarrelIdxBitFn {mPayload : ℕ} (hmPay : 80 ≤ mPayload) (γ : BitAssignment (fullSysCoreWires
    mPayload + 8)) :
    BitAssignment (fullSysCoreWires mPayload + 8) :=
  let α : BitAssignment (fullSysCoreWires mPayload) := fun i ↦ γ (Fin.castAdd 8 i)
  let e := (coinBarrelIdxFast hmPay α).val
  fun w ↦
    if w.val < fullSysCoreWires mPayload then γ w
    else γ w + (if e.testBit (w.val - fullSysCoreWires mPayload) then 1 else 0)

theorem loadBarrelIdxBitFn_involutive {mPayload : ℕ} (hmPay : 80 ≤ mPayload) :
    Function.Involutive (loadBarrelIdxBitFn hmPay) := fun γ ↦ by
  let γ' := loadBarrelIdxBitFn hmPay γ
  have hpre : (fun i : Wire (fullSysCoreWires mPayload) ↦ γ' (Fin.castAdd 8 i)) =
      fun i ↦ γ (Fin.castAdd 8 i) := funext fun i ↦ by simp [γ', loadBarrelIdxBitFn, i.isLt]
  funext w
  change (if w.val < fullSysCoreWires mPayload then γ' w else γ' w +
    (if (coinBarrelIdxFast hmPay (fun i ↦ γ' (Fin.castAdd 8 i))).val.testBit
      (w.val - fullSysCoreWires mPayload) then 1 else 0)) = γ w
  rw [hpre]
  dsimp only [γ', loadBarrelIdxBitFn]
  by_cases hw : w.val < fullSysCoreWires mPayload <;> simp only [hw, ↓reduceIte]
  rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]

noncomputable def loadBarrelIdxPerm {mPayload : ℕ} (hmPay : 80 ≤ mPayload) : Equiv.Perm (Fin (2 ^
    (fullSysCoreWires mPayload + 8))) :=
  (basisBitsEquiv (fullSysCoreWires mPayload + 8)).trans
    ((Equiv.ofBijective (loadBarrelIdxBitFn hmPay)
      (loadBarrelIdxBitFn_involutive hmPay).bijective).trans
      (basisBitsEquiv (fullSysCoreWires mPayload + 8)).symm)

/-- Involutive unitary on `fullSysCoreWires mPayload + 8` XOR-loading `coinBarrelIdxFast hmPay`. -/
noncomputable def uLoadBarrelIdxFast {mPayload : ℕ} (hmPay : 80 ≤ mPayload) : Unitary (2 ^
    (fullSysCoreWires mPayload + 8)) :=
  Operator.permutationUnitary (loadBarrelIdxPerm hmPay)

theorem uLoadBarrelIdxFast_mulVec_ket {mPayload : ℕ} (hmPay : 80 ≤ mPayload) (γ : BitAssignment
    (fullSysCoreWires mPayload + 8)) :
    (uLoadBarrelIdxFast hmPay).1.mulVec (ket γ) = ket (loadBarrelIdxBitFn hmPay γ) := by
  have hid := NuclearTwistRealizes.embedUnitary_perm_mulVec_basisKet
    (QRegExt.idReg (fullSysCoreWires mPayload + 8))
    (loadBarrelIdxPerm hmPay) γ (loadBarrelIdxBitFn hmPay γ)
    (fun q ↦ (NuclearTwistRealizes.basisBits_perm_ofBijective (loadBarrelIdxBitFn hmPay)
      (loadBarrelIdxBitFn_involutive hmPay).bijective γ q).symm)
    (fun z hz ↦ False.elim (hz ((QRegister.mem_image _ z).mpr ⟨z, rfl⟩)))
  rwa [NuclearTwistRealizes.embedUnitary_idReg_eq] at hid

def loadEnWire {mPayload : ℕ} (hmPay : 80 ≤ mPayload) : Wire (fullSysCoreWires mPayload + 8 +
    212) := decWireGen hmPay 8 212 271 (by decide)

def loadIdxWire {mPayload : ℕ} (hmPay : 80 ≤ mPayload) (j : Fin 8) : Wire (fullSysCoreWires mPayload
    + 8 + 212) :=
  decWireGen hmPay 8 212 (69 + j.val) (by have := j.isLt; omega)

def loadDstWire (mPayload : ℕ) (j : Fin 8) : Wire (fullSysCoreWires mPayload + 8 + 212) :=
  ⟨fullSysCoreWires mPayload + j.val, by have := j.isLt; omega⟩

def loadAncWire (mPayload : ℕ) : Wire (fullSysCoreWires mPayload + 8 + 212) :=
  ⟨fullSysCoreWires mPayload + 8 + 211, by omega⟩

theorem loadWire_bounds {mPayload : ℕ} (hmPay : 80 ≤ mPayload) (j : Fin 8) : (loadDstWire mPayload
    j).val < (loadIdxWire hmPay j).val ∧
    (loadIdxWire hmPay j).val < (loadEnWire hmPay).val ∧ (loadEnWire hmPay).val < (loadAncWire
      mPayload).val := by
  have := core_lo_4034 hmPay
  have := j.isLt
  dsimp [loadDstWire, loadIdxWire, loadEnWire, loadAncWire, decWireGen, decWireNumGen]
  split_ifs <;> omega

def loadFanoutStep {mPayload : ℕ} (hmPay : 80 ≤ mPayload) (j : Fin 8) : Internal.TempPhaseProg
    (fullSysCoreWires mPayload + 8 + 212) :=
  let hb := loadWire_bounds hmPay j
  Internal.andXor (loadEnWire hmPay) (loadIdxWire hmPay j)
    (loadDstWire mPayload j) (loadAncWire mPayload)
    (Internal.wire_ne_of_gt hb.2.1) (Internal.wire_ne_of_lt hb.2.2)
    (Internal.wire_ne_of_lt (lt_trans hb.2.1 hb.2.2))
    (Internal.wire_ne_of_gt (lt_trans hb.1 (lt_trans hb.2.1 hb.2.2)))

def loadFanoutAux {mPayload : ℕ} (hmPay : 80 ≤ mPayload) :
    (k : ℕ) → k ≤ 8 → Internal.TempPhaseProg (fullSysCoreWires mPayload + 8 + 212)
  | 0, _ => .nil
  | k + 1, hk =>
      .seq (loadFanoutAux hmPay k (Nat.le_of_succ_le hk)) (loadFanoutStep hmPay ⟨k, hk⟩)

private theorem loadFanoutAux_spec {mPayload : ℕ} (hmPay : 80 ≤ mPayload) :
    ∀ (k : ℕ) (hk : k ≤ 8),
      let C := fullSysCoreWires mPayload
      let M := C + 8 + 212
      let p := loadFanoutAux hmPay k hk
      p.countTempAnd = k ∧ (∀ γ, p.evalSign γ = 0) ∧
      (∀ γ w, ¬ mutIdxWindow C 8 w → p.evalBits γ w = γ w) ∧
      Internal.ValidCleanRem M 1 p ∧
      (∀ β, Internal.cleanRem M 1 β → ∀ w : Wire M,
        p.evalBits β w = if h : C ≤ w.val ∧ w.val < C + k then
          β w + β (loadEnWire hmPay) * β (loadIdxWire hmPay ⟨w.val - C, by omega⟩) else β w)
  | 0, _ =>
      ⟨rfl, fun _ ↦ rfl, fun _ _ _ ↦ rfl, trivial,
        fun _ _ _ ↦ by simp [loadFanoutAux, Internal.TempPhaseProg.evalBits]⟩
  | k + 1, hk => by
      obtain ⟨hcnt, hsgn, hnm, hval, hev⟩ := loadFanoutAux_spec hmPay k (Nat.le_of_succ_le hk)
      let C := fullSysCoreWires mPayload
      let M := C + 8 + 212
      let jk : Fin 8 := ⟨k, hk⟩
      have hb := loadWire_bounds hmPay jk
      have h1t := Internal.wire_ne_of_gt (lt_trans hb.1 hb.2.1)
      have h2t := Internal.wire_ne_of_gt hb.1
      have h1a := Internal.wire_ne_of_lt hb.2.2
      have h2a := Internal.wire_ne_of_lt (lt_trans hb.2.1 hb.2.2)
      have hat := Internal.wire_ne_of_gt (lt_trans hb.1 (lt_trans hb.2.1 hb.2.2))
      obtain ⟨hvStep, hevStep⟩ := Internal.andXor_valid_and_eval (M := M) (rem := 1)
        (loadEnWire hmPay) (loadIdxWire hmPay jk)
        (loadDstWire mPayload jk) (loadAncWire mPayload)
        (Internal.wire_ne_of_gt hb.2.1) h1t h2t hb.2.2 (lt_trans hb.2.1 hb.2.2)
        (lt_trans hb.1 (lt_trans hb.2.1 hb.2.2)) (by dsimp [M, loadAncWire]; omega)
      have hcl_mid (β : BitAssignment M) (hβ : Internal.cleanRem M 1 β) :
          Internal.cleanRem M 1 ((loadFanoutAux hmPay k (Nat.le_of_succ_le hk)).evalBits β) :=
        fun w hw ↦ (hnm β w (by dsimp [mutIdxWindow, M] at hw ⊢; omega)).trans (hβ w hw)
      have hStepNm (δ : BitAssignment M) (w : Wire M) (hne : w ≠ loadDstWire mPayload jk) :
        (loadFanoutStep hmPay jk).evalBits δ w = δ w := by
        dsimp only [loadFanoutStep, Internal.andXor, Internal.TempPhaseProg.cnot,
          Internal.TempPhaseProg.evalBits, Internal.CliffProg.eval]
        by_cases hwa : w = loadAncWire mPayload
        · subst hwa
          simp [Function.update_self, Function.update_of_ne h1t, Function.update_of_ne h2t,
            Function.update_of_ne hat, Function.update_of_ne h1a, Function.update_of_ne h2a,
            add_assoc, CharTwo.add_self_eq_zero]
        · simp [Function.update_of_ne hwa, Function.update_of_ne hne]
      refine ⟨by simp [loadFanoutAux, Internal.TempPhaseProg.countTempAnd, loadFanoutStep, hcnt],
        fun γ ↦ by simp [loadFanoutAux, Internal.TempPhaseProg.evalSign, loadFanoutStep, hsgn],
        fun γ w hw ↦ (hStepNm _ w fun heq ↦ hw (by
          rw [heq]; dsimp [mutIdxWindow, loadDstWire]; omega)).trans (hnm γ w hw),
        ⟨1, by have := core_lo_4034 hmPay; omega, hval, hvStep, hcl_mid⟩, fun β hβ w ↦ ?_⟩
      dsimp only [loadFanoutAux, Internal.TempPhaseProg.evalBits, loadFanoutStep]
      let β₁ := (loadFanoutAux hmPay k (Nat.le_of_succ_le hk)).evalBits β
      rw [hevStep β₁ (hcl_mid β hβ)]
      have hen₁ : β₁ (loadEnWire hmPay) = β (loadEnWire hmPay) :=
        hnm β (loadEnWire hmPay) (decWireGen_nonMut hmPay (by decide : 271 < 61 + 212))
      have hidx₁ : β₁ (loadIdxWire hmPay jk) = β (loadIdxWire hmPay jk) :=
        hnm β (loadIdxWire hmPay jk)
          (decWireGen_nonMut hmPay (by have := jk.isLt; omega : 69 + jk.val < 61 + 212))
      by_cases hwk : w = loadDstWire mPayload jk
      · subst hwk
        rw [Function.update_self, show β₁ (loadDstWire mPayload jk) = _ from hev β hβ _,
          dite_eq_right (by dsimp [loadDstWire, jk, C]; omega), hen₁, hidx₁,
          dite_eq_left ⟨by dsimp [loadDstWire, jk]; omega, by dsimp [loadDstWire, jk]; omega⟩]
        exact congrArg (fun j ↦ _ + _ * β (loadIdxWire hmPay j))
          (Fin.ext (by dsimp [loadDstWire]; omega))
      · rw [Function.update_of_ne hwk, show β₁ w = _ from hev β hβ w]
        have hw_ne : w.val ≠ fullSysCoreWires mPayload + k := fun heq ↦
          hwk (Fin.ext (by dsimp [loadDstWire, jk] at heq ⊢; omega))
        by_cases hlt1 : fullSysCoreWires mPayload ≤ w.val ∧ w.val < fullSysCoreWires mPayload + k
        · simp only [hlt1.1, hlt1.2, show w.val < fullSysCoreWires mPayload + (k + 1) by omega,
            and_self, ↓reduceDIte]
        · simp only [hlt1, show ¬ (fullSysCoreWires mPayload ≤ w.val ∧
            w.val < fullSysCoreWires mPayload + (k + 1)) by omega, ↓reduceDIte]

theorem decWireNum_lt_core {C q : ℕ} (hC : 4034 ≤ C) (hq : q < 61) : decWireNum C q < C := by
  unfold decWireNum
  split_ifs <;> omega

private theorem bitsOfAssignGen_padZeroBits_spec {mPayload : ℕ} (hmPay : 80 ≤ mPayload)
    (off mClean : ℕ) (γ : BitAssignment (fullSysCoreWires mPayload + off)) : (∀ q, 61 ≤ q →
      bitsOfAssignGen hmPay off mClean (padZeroBits γ) q = false) ∧
    coinBarrelIdxFastPure (bitsOfAssignGen hmPay off mClean (padZeroBits γ)) = (coinBarrelIdxFast
      hmPay (fun i ↦ γ (Fin.castAdd off i))).val := by
  have hC := core_lo_4034 hmPay
  refine ⟨fun q hq ↦ ?_, coinBarrelIdxFastPure_eq_core hmPay _ _ fun q hq ↦ ?_⟩
  · by_cases hlt : q < 61 + mClean
    · have hz := padZeroBits_ge γ (decWireGen hmPay off mClean q hlt)
        (by dsimp [decWireGen, decWireNumGen]; split_ifs <;> omega)
      simp [bitsOfAssignGen, hlt, hz]
    · simp [bitsOfAssignGen, hlt]
  · have hqB : q < 61 + mClean := lt_of_lt_of_le hq (Nat.le_add_right 61 mClean)
    have hl : padZeroBits γ (decWireGen hmPay off mClean q hqB) = γ (Fin.castAdd off ⟨decWireNum _
      q, decWireNum_lt_core hC hq⟩) := by
      rw [padZeroBits_lt γ _ (by
        simpa only [decWireGen, decWireNumGen_lt_61 hq] using
          lt_of_lt_of_le (decWireNum_lt_core hC hq) (Nat.le_add_right _ off))]
      exact congrArg γ (Fin.ext (decWireNumGen_lt_61 hq))
    simp [bitsOfAssignGen, hqB, hl]

noncomputable def pLoadBarrelIdxFast {mPayload : ℕ} (hmPay : 80 ≤ mPayload) : Internal.TempPhaseProg
    (fullSysCoreWires mPayload + 8 + 212) :=
  lockValP1 ((listToCtxGen hmPay 8 212 progAll145 61 le_rfl
    (by
      rw [progAll145_endCur]
      decide) progAll145_wellFormed).plug (loadFanoutAux hmPay 8 le_rfl))

private theorem pLoadBarrelIdxFast_valid_and_eval {mPayload : ℕ} (hmPay : 80 ≤ mPayload) :
    let C := fullSysCoreWires mPayload
    let M := (C + 8) + 212
    let p := pLoadBarrelIdxFast hmPay
    p.countTempAnd = 84 ∧ Internal.ValidCleanRem M 212 p ∧
    (∀ γ : BitAssignment (C + 8), p.evalBits (padZeroBits γ) =
      padZeroBits (loadBarrelIdxBitFn hmPay γ)) ∧
    (∀ γ : BitAssignment (C + 8), p.evalSign (padZeroBits γ) = 0) := by
  let C := fullSysCoreWires mPayload
  let M := (C + 8) + 212
  have hend145 : progEndCur 61 progAll145 ≤ 61 + 212 := by
    rw [progAll145_endCur]
    decide
  let K := listToCtxGen hmPay 8 212 progAll145 61 le_rfl hend145 progAll145_wellFormed
  obtain ⟨hcntK, hspK_raw, hsemK⟩ := listToCtxGen_correct (off := 8) (mClean := 212)
    hmPay progAll145 61 le_rfl hend145 progAll145_wellFormed
  have hspK : Internal.CtxSpec (M := M) (mutIdxWindow C 8) (C + 8) (C + 8 + 211) K := by
    rwa [progAll145_endCur] at hspK_raw
  obtain ⟨hcntB, hsgnB, hnmB, hvB_1, hevB⟩ := loadFanoutAux_spec hmPay 8 le_rfl
  have hremHole : M - (C + 8 + 211) = 1 := by dsimp [M]; omega
  have hremOuter : M - (C + 8) = 212 := by dsimp [M]; omega
  have : NeZero M := ⟨by dsimp [M]; omega⟩
  obtain ⟨hV_raw, hcntAll, hS, hB⟩ :=
    Internal.ScopedBlock.graft_mutating_body (M := M) (rem := M - (C + 8))
      (curHole := C + 8 + 211) (mutIdxWindow C 8) K hspK.disj hspK.supp
      (by dsimp [M]; omega) _
      (Internal.CtxSpec.probe (by dsimp [M]; omega) hspK) (loadFanoutAux hmPay 8 le_rfl)
      (Eq.mpr (congrArg (fun r ↦ Internal.ValidCleanRem M r _) hremHole) hvB_1) hnmB
  have hp_eq : pLoadBarrelIdxFast hmPay = K.plug (loadFanoutAux hmPay 8 le_rfl) := lockValP1_eq _
  have hPadClean (γ : BitAssignment (C + 8)) : Internal.cleanRem M (M - (C + 8)) (padZeroBits γ) :=
    fun w hw ↦ padZeroBits_ge γ w (by dsimp [M] at hw ⊢; omega)
  refine ⟨by rw [hp_eq, hcntAll, hcntK, progAll145_numAnd, hcntB], by
    rw [hp_eq]
    exact Eq.mp (congrArg (fun r ↦ Internal.ValidCleanRem M r _) hremOuter) hV_raw,
    fun γ ↦ ?_, fun γ ↦ by rw [hp_eq, hS _ (hPadClean γ), hsgnB]⟩
  let β₀ : BitAssignment M := padZeroBits γ
  have hcl₀ := hPadClean γ
  let β₁ := K.fwdBits β₀
  have hcl₁ : Internal.cleanRem M 1 β₁ :=
    Eq.mp (congrArg (fun r ↦ Internal.cleanRem M r β₁) hremHole) (hspK.fwd_clean hcl₀)
  let α : BitAssignment C := fun i ↦ γ (Fin.castAdd 8 i)
  obtain ⟨hcl_st₀, hpure⟩ := bitsOfAssignGen_padZeroBits_spec hmPay 8 212 γ
  obtain ⟨_, hsp_en0, hsp_en1⟩ := evalBool_progAll145_spec _ hcl_st₀
  have hfwd_en := hsemK β₀ hcl₀ 271 (by decide)
  have hprod (j : Fin 8) : β₁ (loadEnWire hmPay) * β₁ (loadIdxWire hmPay j) = if (coinBarrelIdxFast
    hmPay α).val.testBit j.val then 1 else 0 := by
    by_cases hen : β₁ (loadEnWire hmPay) = 1
    · have hj_eq := hsp_en1 (hfwd_en.symm.trans (decide_eq_true hen)) j
      have hfwd_j : decide (β₁ (loadIdxWire hmPay j) = 1) = evalBool progAll145 61 (bitsOfAssignGen
        hmPay 8 212 β₀)
          (idxOutLocal145[j.val]'(by simp [idxOutLocal145])) := by
        rw [idxOutLocal145_get_eq j]
        exact hsemK β₀ hcl₀ (69 + j.val) (by have := j.isLt; omega)
      rw [hpure, ← hfwd_j] at hj_eq
      rw [hen, one_mul, zmod2_eq_ite_decide (β₁ (loadIdxWire hmPay j)), hj_eq]
    · have hen0 : β₁ (loadEnWire hmPay) = 0 := by
        generalize β₁ (loadEnWire hmPay) = z at hen ⊢; revert z hen; decide
      have hez : (coinBarrelIdxFast hmPay α).val = 0 :=
        hpure ▸ hsp_en0 (hfwd_en.symm.trans (decide_eq_false hen))
      simp [hen0, hez]
  funext w
  rw [hp_eq, hB β₀ hcl₀ w]
  by_cases hmut : mutIdxWindow C 8 w
  · have hmut_c : fullSysCoreWires mPayload ≤ w.val ∧ w.val < fullSysCoreWires mPayload + 8 := hmut
    simp only [hmut, ↓reduceIte]
    rw [hevB β₁ hcl₁ w]
    simp only [hmut_c.1, hmut_c.2, and_self, ↓reduceDIte]
    have hmut_fwd : ∀ (K' : Internal.TempCtx M), K'.DisjointFrom (mutIdxWindow C 8) →
        ∀ (β : BitAssignment M), K'.fwdBits β w = β w := by
      intro K' hD
      induction K' with
      | hole => exact fun _ ↦ rfl
      | seqPre _ _ ih => exact fun β ↦ (ih hD.2 _).trans (hD.1.eval_mut β hmut)
      | seqPost _ _ ih => exact ih hD.1
      | tempAnd _ _ anc _ _ _ _ ih =>
          exact fun β ↦ (ih hD.2.2.2 _).trans
            (Function.update_of_ne (fun heq : w = anc ↦ hD.2.2.1 (heq ▸ hmut)) _ _)
    have hβ₁_w : β₁ w = γ ⟨w.val, hmut.2⟩ :=
      (hmut_fwd _ hspK.disj β₀).trans (padZeroBits_lt γ w hmut.2)
    rw [hβ₁_w, hprod ⟨w.val - C, by omega⟩, padZeroBits_lt (loadBarrelIdxBitFn hmPay γ) w hmut.2]
    unfold loadBarrelIdxBitFn
    exact (ite_eq_right_iff.mpr fun hlt ↦ absurd hlt (Nat.not_lt.mpr hmut_c.1)).symm
  · simp only [hmut, ↓reduceIte]
    dsimp only [β₀]
    by_cases hw8 : w.val < C + 8
    · have hwC : w.val < C := by
        dsimp [mutIdxWindow] at hmut
        omega
      rw [padZeroBits_lt γ w hw8, padZeroBits_lt (loadBarrelIdxBitFn hmPay γ) w hw8]
      unfold loadBarrelIdxBitFn
      exact (ite_eq_left_iff.mpr fun hnot ↦ absurd hwC hnot).symm
    · rw [padZeroBits_ge γ w (by omega),
        padZeroBits_ge (loadBarrelIdxBitFn hmPay γ) w (by omega)]

/-- `336 T` (`84` `TempAnd`s), `0` `.TOFF`, clean-workspace loader XORing `coinBarrelIdxFast hmPay`
into `rIdx8 : QRegister 8 n` using `212 <= mScr` clean scratch wires `rScr` and returning `rScr`
to `|0^{mScr}>`. -/
noncomputable def dLoadBarrelIdxFast {Var : Type} {n mPayload mScr : ℕ} (hmPay : 80 ≤ mPayload)
    (hScr : 212 ≤ mScr) (v : Var)
    (rCore : QRegister (fullSysCoreWires mPayload) n) (rIdx8 : QRegister 8 n) (rScr : QRegister mScr
      n) (hCI : rCore.DisjointWires rIdx8)
    (hCS : rCore.DisjointWires rScr) (hIS : rIdx8.DisjointWires rScr) : DynamicCircuit Var n :=
  let rAct := rCore.concat rIdx8 hCI
  let hAS : rAct.DisjointWires rScr := qreg_disjoint_concat_left hCS hIS
  lockValP1 (((pLoadBarrelIdxFast hmPay).onRegister
    (rAct.concat (rScr.slice 0 212 hScr) (hAS.compose_right _))).toDyn v)

@[simp] theorem count_dLoadBarrelIdxFast_toff {Var : Type} {n mPayload mScr : ℕ} (hmPay : 80 ≤
    mPayload) (hScr : 212 ≤ mScr) (v : Var)
    (rCore : QRegister (fullSysCoreWires mPayload) n) (rIdx8 : QRegister 8 n) (rScr : QRegister mScr
      n) (hCI : rCore.DisjointWires rIdx8)
    (hCS : rCore.DisjointWires rScr) (hIS : rIdx8.DisjointWires rScr) : (dLoadBarrelIdxFast hmPay
      hScr v rCore rIdx8 rScr hCI hCS hIS).count .TOFF = 0 := by
  simpa only [dLoadBarrelIdxFast, lockValP1_eq] using
    Internal.TempPhaseProg.toDyn_count_toff v _

@[simp] theorem count_dLoadBarrelIdxFast_t {Var : Type} {n mPayload mScr : ℕ} (hmPay : 80 ≤
    mPayload) (hScr : 212 ≤ mScr) (v : Var)
    (rCore : QRegister (fullSysCoreWires mPayload) n) (rIdx8 : QRegister 8 n) (rScr : QRegister mScr
      n) (hCI : rCore.DisjointWires rIdx8)
    (hCS : rCore.DisjointWires rScr) (hIS : rIdx8.DisjointWires rScr) : (dLoadBarrelIdxFast hmPay
      hScr v rCore rIdx8 rScr hCI hCS hIS).count .T = 336 := by
  rw [dLoadBarrelIdxFast, lockValP1_eq, Internal.TempPhaseProg.toDyn_count_t,
    Internal.TempPhaseProg.onRegister_countTempAnd, (pLoadBarrelIdxFast_valid_and_eval hmPay).1]

/- ## Section 3: `<= 280 T` (`70` `TempAnd`s) F2-Linearized `MX` Unloader
`dUnloadBarrelIdxFastCont` -/

def progPrefix68 : List DecStep :=
  progCtrl145 ++ (progU8Copy145 ++ (progCSA1_76 ++ (progCPA19_76 ++ (progFlip76 ++
    progSub109B_76))))

def cnotXorProg (srcs : List ℕ) (dst : ℕ) : List DecStep := srcs.map (fun s ↦ .cnot s dst)

theorem foldr_xor_init {α : Type*} (g : α → Bool) :
    ∀ (l : List α) (x b : Bool),
      l.foldr (fun r acc ↦ Bool.xor (g r) acc) (Bool.xor b x) =
        Bool.xor x (l.foldr (fun r acc ↦ Bool.xor (g r) acc) b)
  | [], x, b => by cases x <;> cases b <;> rfl
  | r :: tl, x, b => by
      simp only [List.foldr_cons, foldr_xor_init g tl x b]
      generalize tl.foldr (fun r acc ↦ Bool.xor (g r) acc) b = rest
      cases g r <;> cases x <;> cases b <;> cases rest <;> rfl

private theorem foldr_xor_congr {α : Type*} {g₁ g₂ : α → Bool} {l : List α} (hg : ∀ x ∈ l, g₁ x =
    g₂ x) (b : Bool) :
    l.foldr (fun x acc ↦ Bool.xor (g₁ x) acc) b = l.foldr (fun x acc ↦ Bool.xor (g₂ x) acc) b := by
  induction l with
  | nil => rfl
  | cons x tl ih =>
      simp only [List.foldr_cons, hg x (List.mem_cons_self ..),
        ih (fun y hy ↦ hg y (List.mem_cons_of_mem _ hy))]

theorem cnotXorProg_spec (dst cur : ℕ) (hdst : dst < cur) (hcur : cur ≤ 337) :
    ∀ (srcs : List ℕ), (∀ s ∈ srcs, s < dst) →
      progWellFormed cur (cnotXorProg srcs dst) = true ∧
      progEndCur cur (cnotXorProg srcs dst) = cur ∧
      progNumAnd (cnotXorProg srcs dst) = 0 ∧
      (∀ (st : ℕ → Bool) (w : ℕ),
        evalBool (cnotXorProg srcs dst) cur st w =
          if w = dst then srcs.foldr (fun s acc ↦ Bool.xor (st s) acc) (st dst) else st w)
  | [], _ =>
      ⟨rfl, rfl, rfl, fun st w ↦ by by_cases hw : w = dst <;> simp [cnotXorProg, evalBool, hw]⟩
  | s :: rest, hlt => by
      have hs : s < dst := hlt s (List.mem_cons_self ..)
      have hwf_s : (DecStep.cnot s dst).wellFormed cur = true := by
        simp only [DecStep.wellFormed, decide_eq_true_eq]; omega
      have hcons : cnotXorProg (s :: rest) dst = DecStep.cnot s dst :: cnotXorProg rest dst := rfl
      obtain ⟨hwf_r, hend_r, hnum_r, hev_r⟩ :=
        cnotXorProg_spec dst cur hdst hcur rest (fun r hr ↦ hlt r (List.mem_cons_of_mem _ hr))
      refine ⟨by rw [hcons]; simp [progWellFormed, DecStep.nextCur, hwf_s, hwf_r],
        by rw [hcons]; simp [progEndCur, DecStep.nextCur, hend_r],
        by rw [hcons]; simp [progNumAnd, DecStep.numAnd, hnum_r], fun st w ↦ ?_⟩
      rw [hcons, show evalBool (DecStep.cnot s dst :: cnotXorProg rest dst) cur st w =
        evalBool (cnotXorProg rest dst) cur ((DecStep.cnot s dst).stepBool cur st) w from rfl,
        hev_r]
      by_cases hwd : w = dst
      · subst hwd
        simp only [↓reduceIte,
          show (DecStep.cnot s w).stepBool cur st w = Bool.xor (st w) (st s) by
            simp [DecStep.stepBool],
          foldr_xor_congr (g₁ := (DecStep.cnot s w).stepBool cur st) (g₂ := st) (l := rest)
            (fun r hr ↦ by
              simp [DecStep.stepBool,
                beq_eq_false_iff_ne.mpr (Nat.ne_of_lt (hlt r (List.mem_cons_of_mem _ hr)))]),
          foldr_xor_init]
        rfl
      · simp [hwd, DecStep.stepBool, beq_eq_false_iff_ne.mpr hwd]

def srcsUAux (f : Fin 8 → Bool) : List (Fin 8) → List ℕ
  | [] => []
  | j :: tl => if f j then (69 + j.val) :: srcsUAux f tl else srcsUAux f tl

def srcsDAux (f : Fin 8 → Bool) : List (Fin 8) → List ℕ
  | [] => []
  | j :: tl =>
      if f j then (69 + j.val) :: muxSrcWire76 j.val :: srcsDAux f tl else srcsDAux f tl

theorem srcsUAux_spec (f : Fin 8 → Bool) (st : ℕ → Bool) :
    ∀ l : List (Fin 8), (∀ s ∈ srcsUAux f l, s < 162) ∧
      (srcsUAux f l).foldr (fun s acc ↦ Bool.xor (st s) acc) false =
        l.foldr (fun i acc ↦ Bool.xor (f i && st (69 + i.val)) acc) false
  | [] => ⟨fun _ h ↦ False.elim (List.not_mem_nil h), rfl⟩
  | j :: tl => by
      obtain ⟨hlt, hfold⟩ := srcsUAux_spec f st tl
      dsimp only [srcsUAux]
      cases hfj : f j
      · exact ⟨hlt, by simp [List.foldr_cons, hfj, hfold]⟩
      · exact ⟨List.forall_mem_cons.mpr ⟨by have := j.isLt; omega, hlt⟩,
          by simp [List.foldr_cons, hfj, hfold]⟩

theorem srcsDAux_spec (f : Fin 8 → Bool) (st : ℕ → Bool) :
    ∀ l : List (Fin 8), (∀ s ∈ srcsDAux f l, s < 162) ∧
      (srcsDAux f l).foldr (fun s acc ↦ Bool.xor (st s) acc) false =
        l.foldr (fun i acc ↦
          Bool.xor (f i && Bool.xor (st (69 + i.val)) (st (muxSrcWire76 i.val))) acc) false
  | [] => ⟨fun _ h ↦ False.elim (List.not_mem_nil h), rfl⟩
  | j :: tl => by
      obtain ⟨hlt, hfold⟩ := srcsDAux_spec f st tl
      dsimp only [srcsDAux]
      cases hfj : f j
      · exact ⟨hlt, by simp [List.foldr_cons, hfj, hfold]⟩
      · refine ⟨List.forall_mem_cons.mpr ⟨by have := j.isLt; omega,
          List.forall_mem_cons.mpr ⟨by dsimp [muxSrcWire76]; split_ifs <;> omega, hlt⟩⟩, ?_⟩
        simp only [↓reduceIte, List.foldr_cons, hfold, hfj, Bool.true_and]
        generalize tl.foldr _ false = r
        cases st (69 + j.val) <;> cases st (muxSrcWire76 j.val) <;> cases r <;> rfl

def progParTail (f : Fin 8 → Bool) : List DecStep :=
  (.allocZero :: cnotXorProg (srcsUAux f (List.finRange 8)) 162) ++
  ((.allocZero :: cnotXorProg (srcsDAux f (List.finRange 8)) 163) ++
    [.andAlloc 2 163, .cnot 164 162, .andAlloc 68 162])

def progUnload70 (f : Fin 8 → Bool) : List DecStep := progPrefix68 ++ progParTail f

theorem mux_parity_distribute (en c2 : Bool) (u q : Fin 8 → Bool) (f : Fin 8 → Bool) :
    ∀ l : List (Fin 8),
      (en && Bool.xor (l.foldr (fun j acc ↦ Bool.xor (f j && u j) acc) false)
        (c2 && l.foldr (fun j acc ↦ Bool.xor (f j && Bool.xor (u j) (q j)) acc) false)) =
      l.foldr (fun j acc ↦
        Bool.xor (f j && (en && Bool.xor (u j) (c2 && Bool.xor (u j) (q j)))) acc) false
  | [] => by cases en <;> cases c2 <;> rfl
  | j :: tl => by
      simp only [List.foldr_cons, ← mux_parity_distribute en c2 u q f tl]
      generalize tl.foldr (fun i acc ↦ Bool.xor (f i && u i) acc) false = ru
      generalize tl.foldr (fun i acc ↦ Bool.xor (f i && Bool.xor (u i) (q i)) acc) false = rd
      cases en <;> cases c2 <;> cases f j <;> cases u j <;> cases q j <;>
        cases ru <;> cases rd <;> rfl

theorem progUnload70_spec (f : Fin 8 → Bool) : progWellFormed 61 (progUnload70 f) = true ∧
    progEndCur 61 (progUnload70 f) = 166 ∧ progNumAnd (progUnload70 f) = 70 ∧
    ∀ (st₀ : ℕ → Bool), (∀ q, 61 ≤ q → st₀ q = false) → evalBool (progUnload70 f) 61 st₀ 165 =
      (List.finRange 8).foldr (fun j acc ↦
    Bool.xor (f j && (coinBarrelIdxFastPure st₀).testBit j.val) acc) false := by
  have ⟨hwfP, hendP, hnumP⟩ : progWellFormed 61 progPrefix68 = true ∧
      progEndCur 61 progPrefix68 = 162 ∧ progNumAnd progPrefix68 = 68 := by decide
  obtain ⟨hwfCU, hendCU, hnumCU, hevCU⟩ := cnotXorProg_spec 162 163 (by omega) (by omega) _
    (srcsUAux_spec f (fun _ ↦ false) (List.finRange 8)).1
  obtain ⟨hwfCD, hendCD, hnumCD, hevCD⟩ := cnotXorProg_spec 163 164 (by omega) (by omega) _
    (fun s hs ↦ Nat.lt_trans ((srcsDAux_spec f (fun _ ↦ false) (List.finRange 8)).1 s hs)
      (by decide))
  let cU := cnotXorProg (srcsUAux f (List.finRange 8)) 162
  let cD := cnotXorProg (srcsDAux f (List.finRange 8)) 163
  have hwfTail : progWellFormed 162 (progParTail f) = true := by
    dsimp only [progParTail]
    rw [progWellFormed_append, show progWellFormed 162 (.allocZero :: cU) = true by
        simp [progWellFormed, DecStep.wellFormed, DecStep.nextCur, cU, hwfCU],
      show progEndCur 162 (.allocZero :: cU) = 163 from hendCU, progWellFormed_append,
      show progWellFormed 163 (.allocZero :: cD) = true by
        simp [progWellFormed, DecStep.wellFormed, DecStep.nextCur, cD, hwfCD],
      show progEndCur 163 (.allocZero :: cD) = 164 from hendCD]
    decide
  have hendTail : progEndCur 162 (progParTail f) = 166 := by
    dsimp only [progParTail]
    rw [progEndCur_append, show progEndCur 162 (.allocZero :: cU) = 163 from hendCU,
      progEndCur_append, show progEndCur 163 (.allocZero :: cD) = 164 from hendCD]; rfl
  have hnumTail : progNumAnd (progParTail f) = 2 := by
    dsimp only [progParTail]
    simp [progNumAnd_append, progNumAnd, DecStep.numAnd, hnumCU, hnumCD]
  refine ⟨by rw [progUnload70, progWellFormed_append, hwfP, hendP, hwfTail]; rfl,
    by rw [progUnload70, progEndCur_append, hendP, hendTail],
    by rw [progUnload70, progNumAnd_append, hnumP, hnumTail], fun st₀ hcl₀ ↦ ?_⟩
  generalize hst₁ : evalBool progCtrl145 61 st₀ = st₁
  generalize hst₂ : evalBool progU8Copy145 69 st₁ = st₂
  generalize hst₃ : evalBool progCSA1_76 77 st₂ = st₃
  generalize hst₄ : evalBool progCPA19_76 144 st₃ = st₄
  generalize hst₅ : evalBool progFlip76 152 st₄ = st₅
  generalize hst₆ : evalBool progSub109B_76 152 st₅ = st₆
  rw [progUnload70, evalBool_append, hendP, show evalBool progPrefix68 61 st₀ = st₆ by
    dsimp only [progPrefix68]
    rw [evalBool_append, progCtrl145_end, hst₁, evalBool_append, progU8Copy145_end, hst₂,
      evalBool_append, progCSA1_76_end, hst₃, evalBool_append, progCPA19_76_end, hst₄,
      evalBool_append, progFlip76_end, hst₅, hst₆]]
  obtain ⟨hcl₂, hst₁_low, hst₂_low, hst₁_68, hst₂_u8copy⟩ :=
    evalBool_stage145_to_st2 st₀ st₁ st₂ hcl₀ hst₁ hst₂
  obtain ⟨hcl₆, hq8_val, hst₆_2, hst₆_68, hst₆_u8⟩ := evalBool_stage76_st2_to_st6 st₀ st₁ st₂
    st₃ st₄ st₅ st₆ hcl₂ hst₁_low hst₂_low hst₂_u8copy hst₃ hst₄ hst₅ hst₆
  dsimp only [progParTail]
  rw [evalBool_append, show progEndCur 162 (.allocZero :: cU) = 163 from hendCU, evalBool_append,
    show progEndCur 163 (.allocZero :: cD) = 164 from hendCD]
  let stU := evalBool cU 163 st₆
  let stD := evalBool cD 164 stU
  have hfin3 : evalBool [.andAlloc 2 163, .cnot 164 162, .andAlloc 68 162] 164 stD 165 =
    (stD 68 && Bool.xor (stD 162) (stD 2 && stD 163)) := by
    dsimp only [evalBool, DecStep.stepBool, DecStep.nextCur]
    cases stD 68 <;> cases stD 162 <;> cases stD 2 <;> cases stD 163 <;> rfl
  change evalBool [.andAlloc 2 163, .cnot 164 162, .andAlloc 68 162] 164 stD 165 = _
  rw [hfin3]
  have hstU_ne (w) (hw : w ≠ 162) : stU w = st₆ w := by
    simp only [stU, cU, hevCU st₆ w, ite_eq_right hw]
  have hstD_ne (w) (hw : w ≠ 163) : stD w = stU w := by
    simp only [stD, cD, hevCD stU w, ite_eq_right hw]
  have hstD_162 : stD 162 = (List.finRange 8).foldr (fun i acc ↦ Bool.xor (f i && st₆ (69 +
    i.val)) acc) false := by
    rw [hstD_ne 162 (by decide), show stU 162 = evalBool cU 163 st₆ 162 from rfl,
      hevCU st₆ 162, ite_eq_left rfl, hcl₆ 162 le_rfl, (srcsUAux_spec f st₆ (List.finRange 8)).2]
  have hstD_163 : stD 163 = (List.finRange 8).foldr (fun i acc ↦ Bool.xor (f i && Bool.xor (st₆ (69
    + i.val)) (st₆ (muxSrcWire76 i.val))) acc) false := by
    rw [show stD 163 = evalBool cD 164 stU 163 from rfl, hevCD stU 163, ite_eq_left rfl,
      (hstU_ne 163 (by decide)).trans (hcl₆ 163 (by decide)),
      foldr_xor_congr (fun s hs ↦ hstU_ne s (by
        have := (srcsDAux_spec f st₆ (List.finRange 8)).1 s hs
        omega)),
      (srcsDAux_spec f st₆ (List.finRange 8)).2]
  rw [hstD_ne 68 (by decide), hstU_ne 68 (by decide), hstD_162,
    hstD_ne 2 (by decide), hstU_ne 2 (by decide), hstD_163, hst₆_2,
    mux_parity_distribute (st₆ 68) (st₀ 2) (fun j ↦ st₆ (69 + j.val))
      (fun j ↦ st₆ (muxSrcWire76 j.val)) f (List.finRange 8)]
  refine foldr_xor_congr (fun j _ ↦ congrArg (f j && ·) ?_) false
  rw [hst₆_u8 j.val j.isLt,
    show st₀ (17 + j.val) = (regValList st₀ u8Wires).testBit j.val by
      rw [regValList_testBit u8Wires j.val (by simp [u8Wires]) st₀, u8Wires145_get_eq j],
    show st₆ (muxSrcWire76 j.val) = (regValList st₆ q8SrcWires76).testBit j.val by
      rw [regValList_testBit q8SrcWires76 j.val (by simp [q8SrcWires76]) st₆,
        q8SrcWires76_get_eq j], hq8_val]
  have hen_eq := hst₆_68.trans hst₁_68
  cases hen : st₆ 68
  · rw [Bool.false_and, coinBarrelIdxFastPure_of_en_false st₀ (hen_eq ▸ hen),
      Nat.zero_testBit]
  · rw [Bool.true_and]
    exact coinBarrelIdxFastPure_mux_bit st₀ j (hen_eq ▸ hen)

theorem f2Parity_eq_foldr_testBit {b : ℕ} (f : Fin b → Bool) (v : Fin (2 ^ b)) : f2Parity b f v =
    (List.finRange b).foldr (fun j acc ↦ Bool.xor (f j && v.val.testBit j.val) acc) false := by
  unfold f2Parity
  refine congrArg (fun fn ↦ (List.finRange b).foldr fn false)
    (funext fun j ↦ funext fun _ ↦ ?_)
  rw [show decide (basisBits b v j ≠ 0) = v.val.testBit j.val by
    rw [basisBits_eq_testBit]
    cases v.val.testBit j.val <;> decide]

noncomputable def pUnloadBarrelIdxFast {mPayload : ℕ} (hmPay : 80 ≤ mPayload)
    (f : Fin 8 → Bool) : Internal.TempPhaseProg (fullSysCoreWires mPayload + 105) :=
  lockValP1 ((listToCtxGen hmPay 0 105 (progUnload70 f) 61 le_rfl
    (by rw [(progUnload70_spec f).2.1]) (progUnload70_spec f).1).plug
    (.z (decWireGen hmPay 0 105 165 (by decide))))

/-- `<= 280 T` (`70` `TempAnd`s; `0 T` when `f = 0`), `0` `.TOFF` F2-linearized `MX` phase-fixup
continuation on `rCore` using `105 <= mWB` clean workspace wires `rWB`. -/
noncomputable def dUnloadBarrelIdxFastCont {Var : Type} {n mPayload mWB : ℕ} (hmPay : 80 ≤ mPayload)
    (hWB : 105 ≤ mWB) (v : Var)
    (rCore : QRegister (fullSysCoreWires mPayload) n) (rWB : QRegister mWB n) (hCW :
      rCore.DisjointWires rWB) (f : Fin 8 → Bool) : DynamicCircuit Var n :=
  if ∀ j : Fin 8, f j = false then .identity
  else lockValP1 (((pUnloadBarrelIdxFast hmPay f).onRegister
    (rCore.concat (rWB.slice 0 105 hWB) (hCW.compose_right _))).toDyn v)

@[simp] theorem count_dUnloadBarrelIdxFastCont_toff {Var : Type} {n mPayload mWB : ℕ} (hmPay : 80 ≤
    mPayload) (hWB : 105 ≤ mWB) (v : Var)
    (rCore : QRegister (fullSysCoreWires mPayload) n) (rWB : QRegister mWB n) (hCW :
      rCore.DisjointWires rWB) (f : Fin 8 → Bool) :
    (dUnloadBarrelIdxFastCont hmPay hWB v rCore rWB hCW f).count .TOFF = 0 := by
  unfold dUnloadBarrelIdxFastCont
  split_ifs
  · rfl
  · simpa only [lockValP1_eq] using Internal.TempPhaseProg.toDyn_count_toff v _

theorem unitary_eq_of_mulVec_single {d : ℕ} {U V : Unitary d} (h : ∀ x : Fin d,
    U.1.mulVec (Pi.single x 1) = V.1.mulVec (Pi.single x 1)) : U = V :=
  Subtype.ext (Matrix.ext fun i x ↦ by
    simpa only [Matrix.mulVec_single_one, Matrix.col_apply] using congrFun (h x) i)

/- ## Section 4: Turnkey Pass-1 Load/Body/`MX`-Unload Wrapper (`dWrapPass1BarrelIdx`) -/

abbrev pass1Idx8Reg {n mWB : ℕ} (rWB : QRegister mWB n) (hWB : 220 ≤ mWB) : QRegister 8 n :=
  rWB.slice 0 8 (by omega)

abbrev pass1ScrReg {n mWB : ℕ} (rWB : QRegister mWB n) (hWB : 220 ≤ mWB) : QRegister (mWB - 8) n :=
  rWB.slice 8 (mWB - 8) (by omega)

/-- Subregister embedding `fullSysCoreWires mPayload + 8` into
`(fullSysCoreWires mPayload + kExt) + 8` skipping the `kExt` middle wires. -/
def selLoadExt (mPayload kExt : ℕ) : QRegister (fullSysCoreWires mPayload + 8) ((fullSysCoreWires
    mPayload + kExt) + 8) where
  wires :=
    { toFun := fun u ↦
        if u.val < fullSysCoreWires mPayload then ⟨u.val, by omega⟩
        else
          ⟨(fullSysCoreWires mPayload + kExt) + (u.val - fullSysCoreWires mPayload),
            by omega⟩
      inj' := fun u₁ u₂ heq ↦ by
        have hv := congrArg Fin.val heq
        dsimp at hv
        apply Fin.ext
        split_ifs at hv <;> simp only at hv <;> omega }

/-- `uLoadBarrelIdxFast hmPay` lifted across `kExt` untouched extension wires. -/
noncomputable def uLoadBarrelIdxFastExt {mPayload : ℕ} (hmPay : 80 ≤ mPayload) (kExt : ℕ) : Unitary
    (2 ^ ((fullSysCoreWires mPayload + kExt) + 8)) :=
  (selLoadExt mPayload kExt).embedUnitary (uLoadBarrelIdxFast hmPay)

theorem comp_selLoadExt_eq {n mPayload kExt : ℕ} (rCore : QRegister (fullSysCoreWires mPayload) n)
    (rExt : QRegister kExt n)
    (rIdx8 : QRegister 8 n) (hCE : rCore.DisjointWires rExt) (hCI : rCore.DisjointWires rIdx8)
      (hDI : (rCore.concat rExt hCE).DisjointWires rIdx8) :
    ((rCore.concat rExt hCE).concat rIdx8 hDI).compose (selLoadExt mPayload kExt) = rCore.concat
      rIdx8 hCI := by
  let C := fullSysCoreWires mPayload
  apply QRegister.ext (Function.Embedding.ext fun u ↦ ?_)
  refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) u
  · change ((rCore.concat rExt hCE).concat rIdx8 hDI)
        (selLoadExt mPayload kExt (Fin.castAdd 8 i)) =
      (rCore.concat rIdx8 hCI) (Fin.castAdd 8 i)
    rw [show selLoadExt mPayload kExt (Fin.castAdd 8 i) =
        Fin.castAdd 8 (Fin.castAdd kExt i) from Fin.ext (by simp [selLoadExt, i.isLt]),
      QRegister.concat_apply_left, QRegister.concat_apply_left, QRegister.concat_apply_left]
  · change ((rCore.concat rExt hCE).concat rIdx8 hDI)
        (selLoadExt mPayload kExt (Fin.natAdd C j)) =
      (rCore.concat rIdx8 hCI) (Fin.natAdd C j)
    rw [show selLoadExt mPayload kExt (Fin.natAdd C j) = Fin.natAdd (C + kExt) j from
        Fin.ext (by simp [selLoadExt, C]),
      QRegister.concat_apply_right, QRegister.concat_apply_right]

theorem proj0_mulVec_single {n w : ℕ} (r : QRegister w n) (g : Fin (2 ^ n)) :
    (r.basisOutcomeProjector 0).mulVec (Pi.single g 1) =
    if r.extractIndex g = 0 then Pi.single g 1 else 0 :=
  funext fun i ↦ by
    rw [Matrix.mulVec_single_one]
    change (r.basisOutcomeProjector 0) i g =
      (if r.extractIndex g = 0 then (Pi.single g (1 : ℂ) : Fin (2 ^ n) → ℂ) else 0) i
    rw [QRegister.basisOutcomeProjector_eq_diagonal]
    by_cases hig : i = g <;> by_cases hz : r.extractIndex g = 0 <;>
      simp [Matrix.diagonal, hig, hz]

theorem embedUnitary_uLoadBarrelIdxFast_mul_zeroIdx8 {n mPayload kExt : ℕ} (hmPay : 80 ≤ mPayload)
    (rCore : QRegister (fullSysCoreWires mPayload) n)
    (rExt : QRegister kExt n) (rIdx8 : QRegister 8 n) (hCE : rCore.DisjointWires rExt) (hCI :
      rCore.DisjointWires rIdx8) :
    ((rCore.concat rIdx8 hCI).embedUnitary (uLoadBarrelIdxFast hmPay)).1 *
      rIdx8.basisOutcomeProjector 0 = setTableOp (rCore.concat rExt hCE) rIdx8
    (coinBarrelIdxFastTbl hmPay) * rIdx8.basisOutcomeProjector 0 := by
  let C := fullSysCoreWires mPayload
  let rCI := rCore.concat rIdx8 hCI
  let rData := rCore.concat rExt hCE
  apply matrix_ext_ket fun β ↦ ?_
  let g : Fin (2 ^ n) := (basisBitsEquiv n).symm β
  have hbg : basisBits n g = β := (basisBitsEquiv n).apply_symm_apply β
  rw [mul_mulVec_prog, mul_mulVec_prog, show ket β = Pi.single g 1 from rfl, proj0_mulVec_single
    rIdx8 g]
  by_cases hg0 : rIdx8.extractIndex g = 0
  · simp only [hg0, ↓reduceIte, setTableOp_mulVec_single]
    rw [show (Pi.single g 1 : Fin (2 ^ n) → ℂ) = ket β from rfl, QRegister.embedUnitary_val,
      embedMatrix_mulVec_ket_prog]
    let γ : BitAssignment (C + 8) := fun u ↦ β (rCI u)
    rw [show localIdxProg rCI β = (basisBitsEquiv (C + 8)).symm γ from rfl]
    have hEval (l : Fin (2 ^ (C + 8))) : (uLoadBarrelIdxFast hmPay).1 l ((basisBitsEquiv (C +
      8)).symm γ) =
        if l = (basisBitsEquiv (C + 8)).symm (loadBarrelIdxBitFn hmPay γ) then 1 else 0 := by
      simpa [ket, basisState, Matrix.mulVec_single_one, Pi.single_apply, eq_comm] using
        congrFun (uLoadBarrelIdxFast_mulVec_ket hmPay γ) l
    simp_rw [hEval, ite_smul, one_smul, zero_smul]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    have hsymm : basisBits (fullSysCoreWires mPayload + 8) ((basisBitsEquiv (C +
      8)).symm (loadBarrelIdxBitFn hmPay γ)) = loadBarrelIdxBitFn hmPay γ :=
      (basisBitsEquiv (C + 8)).apply_symm_apply (loadBarrelIdxBitFn hmPay γ)
    rw [hsymm]
    let v := coinBarrelIdxFastTbl hmPay (rData.extractIndex g)
    have hv_val : v.val = (coinBarrelIdxFast hmPay (fun i ↦ γ (Fin.castAdd 8 i))).val := by
      rw [coinBarrelIdxFastTbl_val]
      refine congrArg (fun δ ↦ (coinBarrelIdxFast hmPay δ).val) (funext fun i ↦ ?_)
      rw [QRegister.basisBits_extractIndex, QRegister.concat_apply_left, hbg]
      exact (congrArg β (QRegister.concat_apply_left rCore rIdx8 hCI i)).symm
    have hidx_eq : (basisBitsEquiv n).symm (writeRegProg β rCI (loadBarrelIdxBitFn hmPay γ)) =
      rIdx8.replaceIndex g v := by
      apply (basisBitsEquiv n).injective
      rw [(basisBitsEquiv n).apply_symm_apply]
      change writeRegProg β rCI (loadBarrelIdxBitFn hmPay γ) =
        basisBits n (rIdx8.replaceIndex g v)
      funext w
      by_cases hwI : w ∈ Set.range rIdx8.wires
      · obtain ⟨j, rfl⟩ := hwI
        have hmemCI : rIdx8 j = rCI (Fin.natAdd C j) :=
          (QRegister.concat_apply_right rCore rIdx8 hCI j).symm
        rw [QRegister.basisBits_replaceIndex_apply, basisBits_eq_testBit, hmemCI,
          writeRegProg_apply_reg]
        have hβj : β (rIdx8 j) = 0 := by
          rw [← hbg]
          have hex : basisBits 8 (rIdx8.extractIndex g) j = 0 := by
            rw [hg0]
            simp [-Nat.reducePow, basisBits_eq_div_mod]
          simpa only [QRegister.basisBits_extractIndex] using hex
        unfold loadBarrelIdxBitFn
        rw [ite_eq_right_iff.mpr fun h ↦ absurd h (by dsimp [C]; omega),
          show γ (Fin.natAdd C j) = 0 by simpa only [γ, ← hmemCI] using hβj, zero_add,
          show (Fin.natAdd C j).val - fullSysCoreWires mPayload = j.val by dsimp [C]; omega,
          ← hv_val]
      · rw [QRegister.basisBits_replaceIndex_of_not_mem _ _ _ _ hwI, hbg]
        by_cases hwCI : w ∈ Set.range rCI.wires
        · obtain ⟨u, rfl⟩ := hwCI
          rw [writeRegProg_apply_reg]
          revert hwI
          refine Fin.addCases (fun i _ ↦ by simp [loadBarrelIdxBitFn, γ, i.isLt])
            (fun j hwI ↦
              False.elim (hwI ⟨j, (QRegister.concat_apply_right rCore rIdx8 hCI j).symm⟩)) u
        · exact writeRegProg_apply_of_not_mem _ _ _ _ hwCI
    change (Pi.single ((basisBitsEquiv n).symm (writeRegProg β rCI
        (loadBarrelIdxBitFn hmPay γ))) (1 : ℂ) : Fin (2 ^ n) → ℂ) =
      Pi.single (rIdx8.replaceIndex g v) (1 : ℂ)
    exact congrArg (fun idx ↦ (Pi.single idx (1 : ℂ) : Fin (2 ^ n) → ℂ)) hidx_eq
  · simp [hg0]

/-- Turnkey Pass-1 bracket (`<= 616 + dBody.count .T` `.T`, `dBody.count .TOFF` `.TOFF`):
loads `coinBarrelIdxFast hmPay` into `pass1Idx8Reg rWB hWB` (`336 T`), runs `dBody`, and uncomputes
`pass1Idx8Reg rWB hWB` via Hadamard measurement + F2-linearized `dUnloadBarrelIdxFastCont` (`<= 280
T`). -/
noncomputable def dWrapPass1BarrelIdx {Var : Type} {n mPayload mWB : ℕ} (hmPay : 80 ≤ mPayload)
    (hWB : 220 ≤ mWB) (v : Var)
    (rCore : QRegister (fullSysCoreWires mPayload) n) (rWB : QRegister mWB n)
    (hCW : rCore.DisjointWires rWB) (dBody : DynamicCircuit Var n) : DynamicCircuit Var n :=
  let rIdx8 := pass1Idx8Reg rWB hWB
  let rScr := pass1ScrReg rWB hWB
  let hIS : rIdx8.DisjointWires rScr :=
    rWB.slice_disjoint_of_le 0 8 8 (mWB - 8) (by omega) (by omega) le_rfl
  let dLoad := dLoadBarrelIdxFast hmPay (by omega) v rCore rIdx8 rScr
    (hCW.compose_right _) (hCW.compose_right _) hIS
  let dUnload := DynCircuitExt.measureXResetAndBranch v 8 rIdx8
    (fun f ↦ dUnloadBarrelIdxFastCont hmPay (by omega) v rCore rWB hCW f)
  DynamicCircuit.seq (DynamicCircuit.seq dLoad dBody) dUnload

@[simp] theorem count_dWrapPass1BarrelIdx_toff {Var : Type} {n mPayload mWB : ℕ} (hmPay : 80 ≤
    mPayload) (hWB : 220 ≤ mWB) (v : Var)
    (rCore : QRegister (fullSysCoreWires mPayload) n) (rWB : QRegister mWB n) (hCW :
      rCore.DisjointWires rWB) (dBody : DynamicCircuit Var n) :
    (dWrapPass1BarrelIdx hmPay hWB v rCore rWB hCW dBody).count .TOFF = dBody.count .TOFF := by
  unfold dWrapPass1BarrelIdx
  have hU := DynCircuitExt.count_measureXResetAndBranch_TOFF_le v 8 (pass1Idx8Reg rWB hWB)
    (fun f ↦ dUnloadBarrelIdxFastCont hmPay (by omega) v rCore rWB hCW f) 0 fun f ↦
      le_of_eq (count_dUnloadBarrelIdxFastCont_toff hmPay (by omega) v rCore rWB hCW f)
  simp only [DynamicCircuit.count, count_dLoadBarrelIdxFast_toff]
  omega

theorem count_dWrapPass1BarrelIdx_t {Var : Type} {n mPayload mWB : ℕ} (hmPay : 80 ≤ mPayload)
    (hWB : 220 ≤ mWB) (v : Var) (rCore : QRegister (fullSysCoreWires mPayload) n)
    (rWB : QRegister mWB n) (hCW : rCore.DisjointWires rWB) (dBody : DynamicCircuit Var n) :
    (dWrapPass1BarrelIdx hmPay hWB v rCore rWB hCW dBody).count .T ≤ 616 + dBody.count .T := by
  unfold dWrapPass1BarrelIdx
  have hU := DynCircuitExt.count_measureXResetAndBranch_T_le v 8 (pass1Idx8Reg rWB hWB)
    (fun f ↦ dUnloadBarrelIdxFastCont hmPay (by omega) v rCore rWB hCW f) 280 fun f ↦ by
      unfold dUnloadBarrelIdxFastCont
      split_ifs
      · simp [DynamicCircuit.count]
      · obtain ⟨hwfU, hendU, hnumU, _⟩ := progUnload70_spec f
        have hcnt := (listToCtxGen_correct (off := 0) (mClean := 105) hmPay (progUnload70 f)
          61 le_rfl (by rw [hendU]) hwfU).1
        simp [lockValP1_eq, Internal.TempPhaseProg.toDyn_count_t,
          Internal.TempPhaseProg.onRegister_countTempAnd, pUnloadBarrelIdxFast,
          Internal.TempCtx.plug_countTempAnd, Internal.TempPhaseProg.countTempAnd, hcnt, hnumU]
  simp only [DynamicCircuit.count, count_dLoadBarrelIdxFast_t]
  omega

theorem dWrapPass1BarrelIdx_realizes {Var : Type} [Fintype Var] [DecidableEq Var]
    {n mPayload kExt mWB : ℕ} [NeZero (2 ^ n)] (hmPay : 80 ≤ mPayload) (hWB : 220 ≤ mWB)
    (v : Var) (rCore : QRegister (fullSysCoreWires mPayload) n) (rExt : QRegister kExt n)
    (rWB : QRegister mWB n) (hCE : rCore.DisjointWires rExt) (hCW : rCore.DisjointWires rWB) (hEW :
      rExt.DisjointWires rWB)
    {uBody : Unitary (2 ^ ((fullSysCoreWires mPayload + kExt) + 8))} {uTarget : Unitary (2 ^
      (fullSysCoreWires mPayload + kExt))}
    {dBody : DynamicCircuit Var n} (hBody : DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace
      ((rCore.concat rExt hCE).concat
    (pass1Idx8Reg rWB hWB) ((qreg_disjoint_concat_left hCW hEW).compose_right _)) (pass1ScrReg
    rWB hWB) uBody dBody) (hBodyTarget : (((rCore.concat rExt hCE).concat (pass1Idx8Reg rWB
    hWB) ((qreg_disjoint_concat_left hCW hEW).compose_right _)).embedUnitary uBody).1 *
    setTableOp (rCore.concat rExt hCE) (pass1Idx8Reg rWB hWB) (coinBarrelIdxFastTbl hmPay) *
    rWB.basisOutcomeProjector 0 = setTableOp (rCore.concat rExt hCE) (pass1Idx8Reg rWB hWB)
    (coinBarrelIdxFastTbl hmPay) * ((rCore.concat rExt hCE).embedUnitary uTarget).1 *
    rWB.basisOutcomeProjector 0) : DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace
      (rCore.concat rExt hCE) rWB uTarget
    (dWrapPass1BarrelIdx hmPay hWB v rCore rWB hCW dBody) := by
  let C := fullSysCoreWires mPayload
  let rData := rCore.concat rExt hCE
  let rIdx8 := pass1Idx8Reg rWB hWB
  let rScr := pass1ScrReg rWB hWB
  have hDW : rData.DisjointWires rWB := qreg_disjoint_concat_left hCW hEW
  have hDI : rData.DisjointWires rIdx8 := hDW.compose_right _
  have hDS : rData.DisjointWires rScr := hDW.compose_right _
  have hCI : rCore.DisjointWires rIdx8 := hCW.compose_right _
  have hIS : rIdx8.DisjointWires rScr :=
    rWB.slice_disjoint_of_le 0 8 8 (mWB - 8) (by omega) (by omega) le_rfl
  have hLoad : DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace (rData.concat rIdx8 hDI) rScr
    (uLoadBarrelIdxFastExt hmPay kExt)
      (dLoadBarrelIdxFast hmPay (by omega) v rCore rIdx8 rScr hCI (hCW.compose_right _) hIS) := by
    have hbase : DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace ((rData.concat rIdx8
      hDI).compose (selLoadExt mPayload kExt)) rScr
        (uLoadBarrelIdxFast hmPay) (dLoadBarrelIdxFast hmPay (by omega) v rCore rIdx8 rScr hCI
          (hCW.compose_right _) hIS) := by
      rw [comp_selLoadExt_eq rCore rExt rIdx8 hCE hCI hDI, dLoadBarrelIdxFast, lockValP1_eq]
      obtain ⟨_, hv, hbits, hsign⟩ := pLoadBarrelIdxFast_valid_and_eval hmPay
      exact (Internal.realizes_signedPerm_cleanWorkspace v (rCore.concat rIdx8 hCI) rScr
        (qreg_disjoint_concat_left (hCW.compose_right _) hIS) (by omega)
        (uLoadBarrelIdxFast hmPay) (loadBarrelIdxBitFn hmPay) (fun _ ↦ 0)
        (fun γ ↦ by simp [uLoadBarrelIdxFast_mulVec_ket])
        (pLoadBarrelIdxFast hmPay) hv hbits hsign).1
    exact hbase.widenActive
  have hProjEq : (rIdx8.concat rScr hIS).basisOutcomeProjector 0 = rWB.basisOutcomeProjector 0 := by
    let rC := rIdx8.concat rScr hIS
    let selF : QRegister (8 + (mWB - 8)) mWB := QRegister.block 0 (8 + (mWB - 8)) (by omega)
    let selB : QRegister mWB (8 + (mWB - 8)) := QRegister.block 0 mWB (by omega)
    have hCF : rWB.compose selF = rC := QRegister.ext (Function.Embedding.ext fun idx ↦
      Fin.addCases (fun i ↦ by
        change rWB ⟨0 + i.val, _⟩ = rC (Fin.castAdd (mWB - 8) i)
        rw [QRegister.concat_apply_left]
        exact congrArg rWB (Fin.ext (by simp))) (fun j ↦ by
        change rWB ⟨0 + (8 + j.val), _⟩ = rC (Fin.natAdd 8 j)
        rw [QRegister.concat_apply_right]
        exact congrArg rWB (Fin.ext (by
          dsimp [rScr, pass1ScrReg, QRegister.slice]
          omega))) idx)
    have hCB : rC.compose selB = rWB := QRegister.ext (Function.Embedding.ext fun k ↦ by
      change rC (selB k) = rWB k
      rw [← hCF]
      exact congrArg rWB (Fin.ext (by simp [selF, selB, QRegister.block])))
    trans rWB.basisOutcomeProjector 0 * rC.basisOutcomeProjector 0
    · nth_rw 1 [← hCB]
      exact ((QRegExt.compose_zero_mul_basisOutcomeProjector_zero rC) selB).symm
    · rw [← hCF]
      exact (QRegExt.basisOutcomeProjector_zero_mul_compose_zero rWB) selF
  have hSplitWB : rWB.basisOutcomeProjector 0 = rIdx8.basisOutcomeProjector 0 *
    rScr.basisOutcomeProjector 0 :=
    hProjEq.symm.trans (QRegExt.concat_basisOutcomeProjector_zero rIdx8 rScr hIS)
  have hLoadMat : ((rData.concat rIdx8 hDI).embedUnitary (uLoadBarrelIdxFastExt hmPay kExt)).1 *
    rWB.basisOutcomeProjector 0 =
      setTableOp rData rIdx8 (coinBarrelIdxFastTbl hmPay) * rWB.basisOutcomeProjector 0 := by
    rw [show ((rData.concat rIdx8 hDI).embedUnitary (uLoadBarrelIdxFastExt hmPay kExt)).1 =
        ((rCore.concat rIdx8 hCI).embedUnitary (uLoadBarrelIdxFast hmPay)).1 by
      rw [uLoadBarrelIdxFastExt, ← QRegister.embedUnitary_compose, comp_selLoadExt_eq rCore rExt
        rIdx8 hCE hCI hDI],
      hSplitWB, ← Matrix.mul_assoc,
      embedUnitary_uLoadBarrelIdxFast_mul_zeroIdx8 hmPay rCore rExt rIdx8 hCE hCI,
      Matrix.mul_assoc, ← hSplitWB]
  have hComp : ((rData.concat rIdx8 hDI).embedUnitary (uBody * uLoadBarrelIdxFastExt hmPay kExt)).1
    * (rIdx8.concat rScr hIS).basisOutcomeProjector 0 =
      setTableOp rData rIdx8 (coinBarrelIdxFastTbl hmPay) * (rData.embedUnitary uTarget).1 *
        (rIdx8.concat rScr hIS).basisOutcomeProjector 0 := by
    rw [hProjEq, show ((rData.concat rIdx8 hDI).embedUnitary
      (uBody * uLoadBarrelIdxFastExt hmPay kExt)).1 = ((rData.concat rIdx8 hDI).embedUnitary
      uBody).1 * ((rData.concat rIdx8 hDI).embedUnitary (uLoadBarrelIdxFastExt hmPay kExt)).1
      by simp, Matrix.mul_assoc, hLoadMat, ← Matrix.mul_assoc]
    exact hBodyTarget
  have hdiag_ket {K : ℕ} (p : Fin (2 ^ K) → Bool) (x : Fin (2 ^ K)) : (diagSignUnitary p).1.mulVec
    (Pi.single x 1) =
      (if p x then (-1 : ℂ) else 1) • Pi.single x 1 :=
    funext fun y ↦ by
      rw [Matrix.mulVec_single_one, Matrix.col_apply]
      by_cases hyx : y = x <;> simp [diagSignUnitary, Matrix.diagonal, hyx]
  have hCont (f : Fin 8 → Bool) : DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace rData
    (rIdx8.concat rScr hIS)
      (diagSignUnitary (fun x ↦ f2Parity 8 f (coinBarrelIdxFastTbl hmPay x)))
        (dUnloadBarrelIdxFastCont hmPay (by omega) v rCore rWB hCW f) := by
    let selCore : QRegister C (C + kExt) := QRegister.block 0 C (by omega)
    have hcomp : rData.compose selCore = rCore :=
      QRegister.ext (Function.Embedding.ext fun i ↦ by
        change rData (selCore i) = rCore i
        rw [show selCore i = Fin.castAdd kExt i from Fin.ext (Nat.zero_add i.val),
          QRegister.concat_apply_left])
    let p₀ : Fin (2 ^ C) → Bool :=
      fun x ↦ f2Parity 8 f (coinBarrelIdxFastTbl (kExt := 0) hmPay x)
    have hCore : DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace (rData.compose selCore) rWB
      (diagSignUnitary p₀)
        (dUnloadBarrelIdxFastCont hmPay (by omega) v rCore rWB hCW f) := by
      rw [hcomp]
      unfold dUnloadBarrelIdxFastCont
      split_ifs with hf
      · rw [show p₀ = fun _ ↦ false from funext fun x ↦ by
            rw [show p₀ x = _ from f2Parity_eq_foldr_testBit f _,
              show (fun (j : Fin 8) (acc : Bool) ↦ Bool.xor (f j &&
                (coinBarrelIdxFastTbl (kExt := 0) hmPay x).val.testBit j.val) acc) =
                fun _ acc ↦ acc from funext fun j ↦ funext fun acc ↦ by simp [hf j]]
            decide, diagSignUnitary_false]
        exact DynCircuitExt.realizesEmbeddedUnitaryWithCleanWorkspace_identity rCore rWB
      · rw [lockValP1_eq]
        obtain ⟨hwfU, hendU, _, hevU⟩ := progUnload70_spec f
        have hendU_le : progEndCur 61 (progUnload70 f) ≤ 61 + 105 := by rw [hendU]
        let K := listToCtxGen hmPay 0 105 (progUnload70 f) 61 le_rfl hendU_le hwfU
        obtain ⟨_, hspK_raw, hsemK⟩ := listToCtxGen_correct (off := 0) (mClean := 105)
          hmPay (progUnload70 f) 61 le_rfl hendU_le hwfU
        have hspK : Internal.CtxSpec (M := C + 105) (mutIdxWindow C 0) C (C + 105) K := by
          rwa [hendU] at hspK_raw
        let w165 := decWireGen hmPay 0 105 165 (by decide)
        have hBlk := Internal.CtxSpec.probe (le_refl (C + 105)) hspK w165
        have hp_eq : pUnloadBarrelIdxFast hmPay f = K.plug (.z w165) := lockValP1_eq _
        have hPadClean (α : BitAssignment C) : Internal.cleanRem (C + 105) ((C + 105) -
          C) (padZeroBits α) :=
          fun w hw ↦ padZeroBits_ge α w (by have := Nat.add_sub_cancel_left C 105; omega)
        exact (Internal.realizes_signedPerm_cleanWorkspace v rCore rWB hCW (by omega)
          (diagSignUnitary p₀) id (fun α ↦ if p₀ ((basisBitsEquiv C).symm α) then 1 else 0)
          (fun α ↦ by
            let x := (basisBitsEquiv C).symm α
            change (diagSignUnitary p₀).1.mulVec (Pi.single x 1) =
              ((-1 : ℂ) ^ (if p₀ x then (1 : ZMod 2) else 0).val) • Pi.single x 1
            rw [hdiag_ket p₀ x]
            rcases Bool.eq_false_or_eq_true (p₀ x) with hp | hp <;>
              simp [hp, show (1 : ZMod 2).val = 1 from rfl])
          (pUnloadBarrelIdxFast hmPay f)
          (by
            rw [hp_eq]
            exact Eq.mp (congrArg (fun r ↦ Internal.ValidCleanRem (C + 105) r _)
              (Nat.add_sub_cancel_left C 105)) hBlk.valid)
          (fun α ↦ by rw [hp_eq]; exact hBlk.bits (padZeroBits α) (hPadClean α))
          (fun α ↦ by
            rw [hp_eq, hBlk.sign (padZeroBits α) (hPadClean α)]
            dsimp only [Internal.TempPhaseProg.evalSign]
            obtain ⟨hcl_st₀, hpure⟩ := bitsOfAssignGen_padZeroBits_spec hmPay 0 105 α
            rw [show (fun i : Wire C ↦ α (Fin.castAdd 0 i)) = α from
              funext fun i ↦ congrArg α (Fin.ext rfl)] at hpure
            have hfwd := hsemK (padZeroBits α) (hPadClean α) 165 (by decide)
            rw [hevU _ hcl_st₀, hpure] at hfwd
            have htbl_val : (coinBarrelIdxFastTbl (kExt := 0) hmPay
                ((basisBitsEquiv C).symm α)).val = (coinBarrelIdxFast hmPay α).val := by
              rw [coinBarrelIdxFastTbl_val]
              exact congrArg (fun β ↦ (coinBarrelIdxFast hmPay β).val) (funext fun i ↦
                (congrArg (basisBits C ((basisBitsEquiv C).symm α)) (Fin.ext rfl)).trans
                  (congrFun ((basisBitsEquiv C).apply_symm_apply α) i))
            have hpar := f2Parity_eq_foldr_testBit f
              (coinBarrelIdxFastTbl (kExt := 0) hmPay ((basisBitsEquiv C).symm α))
            rw [htbl_val, ← hfwd] at hpar
            exact (zmod2_eq_ite_decide _).trans
              (congrArg (fun b : Bool ↦ if b then (1 : ZMod 2) else 0)
                (hpar : p₀ ((basisBitsEquiv C).symm α) = _).symm))).1
    have hu : selCore.embedUnitary (diagSignUnitary p₀) = diagSignUnitary (fun x ↦ f2Parity 8 f
      (coinBarrelIdxFastTbl hmPay x)) :=
      unitary_eq_of_mulVec_single fun x ↦ by
        rw [embedUnitary_diagSignUnitary_mulVec_single, hdiag_ket]
        refine congrArg (fun c ↦ (if f2Parity 8 f c then (-1 : ℂ) else 1) • Pi.single x 1)
          (Fin.ext ?_)
        rw [coinBarrelIdxFastTbl_val, coinBarrelIdxFastTbl_val]
        refine congrArg (fun β ↦ (coinBarrelIdxFast hmPay β).val) (funext fun i ↦ ?_)
        rw [show (Fin.castAdd 0 i : Wire C) = i from Fin.ext rfl, QRegister.basisBits_extractIndex,
          show selCore i = Fin.castAdd kExt i from Fin.ext (Nat.zero_add i.val)]
    have hwid := hCore.widenActive
    rw [hu] at hwid
    exact fun M ↦ (hwid M).imp fun _ ⟨hwp, hproj⟩ ↦ ⟨hwp, by rwa [hProjEq]⟩
  have hOut := DynCircuitExt.realizesCleanTableXUncompute v rData rIdx8 rScr hDI hDS hIS
    (coinBarrelIdxFastTbl hmPay)
    (hLoad.seq (qreg_disjoint_concat_left hDS hIS) hBody) hComp hCont
  exact fun M ↦ (hOut M).imp fun _ ⟨hwp, hproj⟩ ↦ ⟨hwp, by rwa [hProjEq] at hproj⟩

end Pass1BarrelIdxLoad273
end ConfigPass1BarrelIdxLoad273
end
set_option exponentiation.threshold 256
end Pass1BarrelIdxLoad273

section PosPostPrep80S2MergedVep
local instance (priority := 1000000) instNeZeroTwoPow_PosPostPrep80S2MergedVep (k : ℕ) :
    NeZero (2 ^ k) := ⟨(Nat.two_pow_pos k).ne'⟩

public section

/-!
# Zero-Ancilla `80`-Wire Post-Hadamard Position Sub-State Preparation (`PosPostPrep80MergedVep`)

Unified, zero-`.TOFF` hardware and semantic closure for both:
- **`isMerged218 = false`** (`216` host nuclei on `Slot 2`, `218` electrons on `Slot 4`, `Q = 4,431`
  single-catalyst `D3WholeClosure`), and
- **`isMerged218 = true`** (`218`-center `U_en + V_ep` merged `Slot 2` eliminating `MomSlot 5` with
  `qRatio = 108 / 109` exact scaling, `0` sub-rejection waste `p80 62 = 0`, `0` clean-scratch waste
  `p80[75..79) = 0`, `mWorkPost = 43 ≤ 288`, and `tPosPost = 30392 ≤ 30500` one-way `.T` gates).

## Main Exports

1. **Section 1 (`wrapPosDataMergedVep80`, `mergedVepFastPosData80`)**:
   - Wraps any `PosSlots24Data80 mWorkPos` with `0`-`.T`, `0`-`.TOFF` `Circuit.SWAP` on core wires
     `3967 ↔ 4029` (`rNucIdx[7] ↔ p80[75]`) around `.dPosPhase`, proving exact self-adjointness,
     `hPos_on_P1`, `posSlack2Prop` (`c = 2`), `posSlack3Prop` (`c = 3`), exact `s0 = true` phase
     identity, and routed `nuc % 128 < 216` phase identity whenever `p80 75 = 0`.
2. **Section 2 (`cPosPostLocal`, `uPosPostAnc86`, `posPostPrepCert80Gen`, `posPostPrep80Cert`,
   `posPostPrep80MergedVepCert`)**:
   - Constructs the complete `128`-wire reversible circuit (`86` ancilla wires + `42` clean work
     wires + `1` clean `SplitLifetimeKX2Mux` wire = `mWorkPost = 43 ≤ 288`), proves clean-workspace
     preservation across all `2 ^ 86` basis inputs, proves strict identity on all non-position coins
     `2 ≤ c.val` (`hPosPost_nonPos`), and proves `tPosPost = 30392 ≤ 30500` (`0` `.TOFF`).
3. **Section 3 (`uPosPostEff86`, `uPosPostEff86_mulVec_ket`, `uPosPostEff86_supp`,
   `uPosPostEff86_norm_sq`)**:
   - Evaluates `(uPosPostAnc86 isMerged218 * hadamardPayloadAnc86)` cleanly on `coin = 0` (`s0 =
   false`)
     and `coin = 1` (`s0 = true`), proving support inside `Set.range (ancIdx86 s0)`, exact zero bits
     on
     `wSubReject` (`p80 62 = 0`) and clean payload scratch (`p80 75 = p80 76 = p80 77 = p80 78 =
     0`),
     and closed-form squared amplitude `‖(uPosPostEff86 isMerged218).1 (ancIdx86 s0 p80) a_c‖ ^ 2`.
4. **Section 4 (`muSlot2Ideal80`, `muSlot4Ideal80`, `muSlot2Ideal80_merged_ratio`,
   `posPostPrep80_slot2_l1_err`, `posPostPrep80_slot4_l1_err`)**:
   - Defines exact zero-rejection ideal distributions `muSlot2Ideal80 (isMerged218 : Bool)` and
     `muSlot4Ideal80`, proves exact `(108 / 109)` host scaling + uniform `(1 / 218) * (1 / 8)` on
     `nuc ∈ {216, 217}` and `bP = p80[3..6)`, and proves both `< 100 / 2 ^ 47` and `≤ 1 / 10 ^ 12`
     `L₁` bounds over `BitAssignment 80` via finite fiber bijections.
-/

namespace PosPostPrep80S2MergedVep
section ConfigPosPostPrep80S2MergedVep
set_option backward.isDefEq.respectTransparency true

local instance (priority := 1000000)
    instLoc_PosPostPrep80S2MergedVep_1InstNeZeroTwoPowPo (k : ℕ) :
    NeZero (2 ^ k) := ⟨Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos k)⟩

open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt Real
open scoped Matrix BigOperators Matrix.Norms.L2Operator Circuit.Notation
open MeasureBranchHadamardSem (bit_cases)
open ZeroAncillaUSP hiding ket

@[scoped simp] theorem circuit_inverse_count_T {n : ℕ} (c : Circuit n) :
    c.inverse.count PrimitiveGate.T = c.count PrimitiveGate.T := by
  induction c with
  | identity => rfl
  | gate g _ =>
      cases g <;> simp only [Circuit.inverse_gate, Circuit.inverseGate, Circuit.sequence,
        Circuit.count_seq, Circuit.count_gate, Circuit.count_identity, Nat.add_comm] <;> rfl
  | seq _ _ ih₁ ih₂ => simp only [Circuit.inverse_seq, Circuit.count_seq, ih₁, ih₂, Nat.add_comm]

@[scoped simp] theorem circuit_inverse_count_TOFF {n : ℕ} (c : Circuit n) :
    c.inverse.count PrimitiveGate.TOFF = c.count PrimitiveGate.TOFF := by
  induction c with
  | identity => rfl
  | gate g _ =>
      cases g <;> simp only [Circuit.inverse_gate, Circuit.inverseGate, Circuit.sequence,
        Circuit.count_seq, Circuit.count_gate, Circuit.count_identity] <;> rfl
  | seq _ _ ih₁ ih₂ => simp only [Circuit.inverse_seq, Circuit.count_seq, ih₁, ih₂, Nat.add_comm]

set_option maxRecDepth 2000000
set_option exponentiation.threshold 256

def mThresh4 : Fin 4 → ℕ := ![771830103, 814177451, 796552300, 784365019]

/-- Complementary `30`-bit addition constants `2^30 - mThresh4 k`:
`fine + kAdd4 k ≥ 2^30 ↔ fine ≥ mThresh4 k`, so carry-out `c_30 = 0 ↔ fine < mThresh4 k`. -/
def kAdd4 (k : Fin 4) : ℕ := 2 ^ 30 - mThresh4 k

theorem mThresh4_pos (k : Fin 4) : 0 < mThresh4 k := by fin_cases k <;> decide
theorem mThresh4_le_pow30 (k : Fin 4) : mThresh4 k ≤ 2 ^ 30 := by fin_cases k <;> decide
theorem kAdd4_lt_pow30 (k : Fin 4) : kAdd4 k < 2 ^ 30 := by fin_cases k <;> decide

/-- `i`-th binary bit `(x / 2^i) % 2 ∈ {0, 1}` of `x : ℕ`. -/
def natBit (x i : ℕ) : ℕ := (x / 2 ^ i) % 2

/-- `ZMod 2` projection of `natBit x i`. -/
def z2Bit (x i : ℕ) : ZMod 2 := ((natBit x i : ℕ) : ZMod 2)

theorem natBit_zero_or_one (x i : ℕ) : natBit x i = 0 ∨ natBit x i = 1 := by
  dsimp [natBit]; omega

def natCarry (a b : ℕ) : ℕ → ℕ
  | 0 => 0
  | i + 1 => (natBit a i + natBit b i + natCarry a b i) / 2

theorem mod_pow_succ_two (x n : ℕ) : x % 2 ^ (n + 1) = x % 2 ^ n + 2 ^ n * natBit x n := by
  have hlt := Nat.mod_lt x (Nat.two_pow_pos n)
  have hx : x = (x % 2 ^ n + 2 ^ n * natBit x n) + (x / 2 ^ n / 2) * 2 ^ (n + 1) := by
    conv_lhs => rw [← Nat.div_add_mod x (2 ^ n), ← Nat.div_add_mod (x / 2 ^ n) 2]
    dsimp [natBit]
    rw [pow_succ]
    ring
  conv_lhs => rw [hx]
  rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by
    rcases natBit_zero_or_one x n with h | h <;>
      simp only [h, pow_succ] <;> omega)]

/-- Fundamental inductive ripple-carry identity: `c_n = ((a % 2^n) + (b % 2^n)) / 2^n`. -/
theorem natCarry_eq_div_pow (a b : ℕ) :
    ∀ n : ℕ, natCarry a b n = ((a % 2 ^ n) + (b % 2 ^ n)) / 2 ^ n
  | 0 => by simp [natCarry, Nat.mod_one]
  | n + 1 => by
      have hp := Nat.two_pow_pos n
      rw [natCarry, natCarry_eq_div_pow a b n,
        ← show (a % 2 ^ (n + 1) + b % 2 ^ (n + 1)) / 2 ^ n =
        natBit a n + natBit b n + (a % 2 ^ n + b % 2 ^ n) / 2 ^ n by
          rw [mod_pow_succ_two a n, mod_pow_succ_two b n,
            show (a % 2 ^ n + 2 ^ n * natBit a n) + (b % 2 ^ n + 2 ^ n * natBit b n) =
              (a % 2 ^ n + b % 2 ^ n) + (natBit a n + natBit b n) * 2 ^ n by ring,
            Nat.add_mul_div_right _ _ hp]
          omega,
        Nat.div_div_eq_div_mul, ← pow_succ]

theorem natCarry_zero_or_one (a b n : ℕ) : natCarry a b n = 0 ∨ natCarry a b n = 1 := by
  rw [natCarry_eq_div_pow]
  have hp := Nat.two_pow_pos n
  have ha := Nat.mod_lt a hp
  have hb := Nat.mod_lt b hp
  by_cases hge : 2 ^ n ≤ a % 2 ^ n + b % 2 ^ n
  · exact Or.inr (Nat.le_antisymm
      (Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul hp).mpr (by omega)))
      ((Nat.le_div_iff_mul_le hp).mpr (by omega)))
  · exact Or.inl (Nat.div_eq_of_lt (by omega))

/-- Exact threshold comparator theorem: for `fine < 2^30` and `k : Fin 4`,
`natCarry fine (kAdd4 k) 30 = 0 ↔ fine < mThresh4 k`. -/
theorem natCarry_kAdd4_eq_zero_iff {fine : ℕ} (hfine : fine < 2 ^ 30) (k : Fin 4) : natCarry fine
    (kAdd4 k) 30 = 0 ↔ fine < mThresh4 k := by
  rw [natCarry_eq_div_pow, Nat.mod_eq_of_lt hfine, Nat.mod_eq_of_lt (kAdd4_lt_pow30 k)]
  have := mThresh4_pos k
  have := mThresh4_le_pow30 k
  dsimp [kAdd4]
  refine ⟨fun h0 ↦ by
    by_contra hge
    have := Nat.div_pos (by omega : 2 ^ 30 ≤ fine + (2 ^ 30 - mThresh4 k))
      (Nat.two_pow_pos 30)
    omega, fun hlt ↦ Nat.div_eq_of_lt (by omega)⟩

theorem z2_maj_eq_nat_carry {a b c : ℕ} (ha : a = 0 ∨ a = 1) (hb : b = 0 ∨ b = 1)
    (hc : c = 0 ∨ c = 1) : (((a + b + c) / 2 : ℕ) : ZMod 2) = ((a : ZMod 2) + (c : ZMod 2)) *
      ((b : ZMod 2) + (c : ZMod 2)) + (c : ZMod 2) := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> rcases hc with rfl | rfl <;> decide

structure Anf4 where
  c0 : ZMod 2
  cd : ZMod 2
  cm : ZMod 2
  cmp : ZMod 2
  deriving DecidableEq

def anfZero : Anf4 := ⟨0, 0, 0, 0⟩
def anfOne : Anf4 := ⟨1, 0, 0, 0⟩
def anfXor (a b : Anf4) : Anf4 := ⟨a.c0 + b.c0, a.cd + b.cd, a.cm + b.cm, a.cmp + b.cmp⟩

def evalAnf4 (a : Anf4) (par maj : ZMod 2) : ZMod 2 :=
  a.c0 + a.cd * par + a.cm * maj + a.cmp * (maj * par)

theorem evalAnf4_zero (par maj : ZMod 2) : evalAnf4 anfZero par maj = 0 := by
  simp [evalAnf4, anfZero]

theorem evalAnf4_one (par maj : ZMod 2) : evalAnf4 anfOne par maj = 1 := by
  simp [evalAnf4, anfOne]

theorem evalAnf4_anfXor (a b : Anf4) (par maj : ZMod 2) : evalAnf4 (anfXor a b) par maj =
    evalAnf4 a par maj + evalAnf4 b par maj := by
  dsimp [evalAnf4, anfXor]; ring

theorem zmod2_add_self (x : ZMod 2) : x + x = 0 := CharTwo.add_self_eq_zero x

/-- Popcount index `0 .. 3` of `(d0, d1, d2 : ZMod 2)`. -/
def pop3Idx (d0 d1 d2 : ZMod 2) : Fin 4 :=
  ⟨d0.val + d1.val + d2.val, by
    have := ZMod.val_lt d0; have := ZMod.val_lt d1; have := ZMod.val_lt d2; omega⟩

/-- 4-point Boolean interpolation of `i`-th bit of `kAdd4` over `(par, maj)`. -/
def anfOfStage (i : ℕ) : Anf4 :=
  let b0 := z2Bit (kAdd4 0) i
  let b1 := z2Bit (kAdd4 1) i
  let b2 := z2Bit (kAdd4 2) i
  let b3 := z2Bit (kAdd4 3) i
  ⟨b0, b0 + b1, b0 + b2, b0 + b1 + b2 + b3⟩

theorem evalAnf4_anfOfStage (i : ℕ) (d0 d1 d2 : ZMod 2) : evalAnf4 (anfOfStage i)
    (d0 + d1 + d2) (d0 * d1 + (d0 + d1) * d2) = z2Bit (kAdd4 (pop3Idx d0 d1 d2)) i := by
  let b0 := z2Bit (kAdd4 0) i
  let b1 := z2Bit (kAdd4 1) i
  let b2 := z2Bit (kAdd4 2) i
  let b3 := z2Bit (kAdd4 3) i
  change b0 + (b0 + b1) * (d0 + d1 + d2) + (b0 + b2) * (d0 * d1 + (d0 + d1) * d2) +
    (b0 + b1 + b2 + b3) * ((d0 * d1 + (d0 + d1) * d2) * (d0 + d1 + d2)) =
    z2Bit (kAdd4 (pop3Idx d0 d1 d2)) i
  rcases bit_cases d0 with rfl | rfl <;> rcases bit_cases d1 with rfl | rfl <;>
    rcases bit_cases d2 with rfl | rfl
  · simp [pop3Idx]; ring
  · rw [show pop3Idx 0 0 1 = 1 from rfl]; simp [b1, ← add_assoc]
  · rw [show pop3Idx 0 1 0 = 1 from rfl]; simp [b1, ← add_assoc]
  · rw [show pop3Idx 0 1 1 = 2 from rfl]; simp [b2, ← add_assoc]
  · rw [show pop3Idx 1 0 0 = 1 from rfl]; simp [b1, ← add_assoc]
  · rw [show pop3Idx 1 0 1 = 2 from rfl]; simp [b2, ← add_assoc]
  · rw [show pop3Idx 1 1 0 = 2 from rfl]; simp [b2, ← add_assoc]
  · rw [show pop3Idx 1 1 1 = 3 from rfl]
    change b0 + (b0 + b1) * 1 + (b0 + b2) * 1 + (b0 + b1 + b2 + b3) * 1 = b3
    rw [show b0 + (b0 + b1) * 1 + (b0 + b2) * 1 + (b0 + b1 + b2 + b3) * 1 =
      (2 : ZMod 2) * (2 * b0 + b1 + b2) + b3 by ring, show (2 : ZMod 2) = 0 from rfl,
      zero_mul, zero_add]

set_option maxRecDepth 2000
end ConfigPosPostPrep80S2MergedVep
end PosPostPrep80S2MergedVep
end
set_option exponentiation.threshold 256
end PosPostPrep80S2MergedVep

set_option exponentiation.threshold 256

end QuantumComputation.Specs.StoppingPowerSolution
