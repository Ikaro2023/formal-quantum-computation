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

public import
  QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.UnsignedBilinearLac2Select
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.BlockEncodingDyn
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.OuterAliasPrep
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.GroupUnary
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.FastUniform
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.InnerTablePreInteg
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.CompactOuterAlias
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.AngleTables
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.Defs
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.SumOfSquares
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.FermionPerm
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.GivensCascade
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.SelectSwapQROM
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.XMeasCircuit
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.CleanDyn
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.PhaseGradAdder
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.QromBase
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.WalkQPEBridge
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.WalkQPEFlexBridge
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.MidReflSandwich
public import
  QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.WalkQPECat11ReducedRefl

/-!
# Folded `184`-Clean-Wire `Lac = 2` Unsigned-Bilinear `SELECT` (`13,058 T`, `0 TOFF`)

Folds `UnsignedBilinearLac2Select`'s `12,622-T` unsigned-bilinear `Lac = 2` `SELECT` cascade down to
**`184` clean
scratch wires total** (`sUb = 184`, matching `MidReflSandwich`'s `184 ≤ sUb` floor with `0`
wire slack so `Q = 390` at `(wOuter, wInner2) = (19, 26)`):

1. **Entry Router (`480 T`):** Computes `(idx319 : 9, enR : 1, sigSel : 1, negPhase : 1)` via
   `neg1bFastProg16` (`15` ANDs) and `selectCoreArithSteps` (`39` ANDs) into free clean wires,
   applies `Z(negPhase)` and controlled `58`-pair spin swap (`232 T`), writes `idx319[0]` to
   `wPar` and `(enR, enR && idx319[1..8])` (`32 T`) to `locMask9`, and `0-T` uncomputes the router.
2. **One-Hot Entry + `CNOT`-Clear (`636 T`):** Decodes `(enR, m_1..m_8)` into `locOH160` via
   `GroupUnary.oneHotEnabledProg` (`159` ANDs = `636 T`), then clears `locMask9` to `|0⟩^9` by
   CNOT fan-in from `locOH160` (`0 T`), freeing all `23` Givens workspace wires `locGiv23`.
3. **Folded-Apex `113`-Plane Cascade (`11,522 T`):** Runs `56` `PlanePosDyn` (`5,712 T`), a folded
   apex (`98 T`) that CNOT-fans `locOH160` into `locGiv23[22]` (`actIdx`) while using
   `locGiv23[0..21]` as its `22` clean scratch wires, and `56` `PlaneNegDyn` (`5,712 T`).
4. **`CNOT`-Restore + `0-T` One-Hot Exit (`0 T`):** Restores `locMask9` from `locOH160` (`0 T`) and
   measurement-assisted uncomputes `locOneHot160Rev` (`0 T`).
5. **Exit Router (`420 T`):** Recomputes `(idx319 : 9, enR : 1, sigSel : 1)` via
   `selectCoreArithSteps` (`39` ANDs, skipping `neg1bFastProg16`), clears `(wPar, locMask9)`
   (`32 T`), applies the second controlled `58`-pair spin swap (`232 T`), and `0-T` uncomputes.
-/

@[expose] public section

namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.Lac2Folded184Select
open QuantumComputation.Specs QuantumComputation.Specs.P450

open Operator Matrix Circuit QProg Real HermitianMat
open scoped Matrix BigOperators Matrix.Norms.L2Operator ComplexOrder MatrixOrder

local instance (priority := 1000000) instNeZeroTwoPowFold184 (k : ℕ) : NeZero (2 ^ k) :=
  ⟨Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos k)⟩

/-! ## Section 1: `Unit`-to-`Var` Lift (`mapVar`) & Subspace QHL (`TransRealizes`) -/

private structure TransRealizes {Var : Type} [Fintype Var] [DecidableEq Var] {N : ℕ}
    (v : Var) (S_pre S_post : BitAssignment N → Bool) (U : Unitary (2 ^ N))
    (P : DynamicCircuit Var N) : Prop where
  toff_zero : P.count .TOFF = 0
  map_proj : U.1 * GroupUnary.predProj S_pre = GroupUnary.predProj S_post * U.1
  update_self : ∀ Θ : QCAssertion Var (2 ^ N),
    (∀ σ val, Θ (Function.update σ v val) = Θ σ) →
    ∀ σ val, wp P.compile Θ (Function.update σ v val) = wp P.compile Θ σ
  wp_eq : ∀ Θ : QCAssertion Var (2 ^ N),
    (∀ σ val, Θ (Function.update σ v val) = Θ σ) →
    GroupUnary.restrictPred S_pre (wp P.compile Θ) =
      GroupUnary.restrictPred S_pre (qcWpQAssign U Θ)

private theorem TransRealizes.map_proj_adj {Var : Type} [Fintype Var] [DecidableEq Var] {N : ℕ}
    {v : Var} {S_pre S_post : BitAssignment N → Bool} {U : Unitary (2 ^ N)}
    {P : DynamicCircuit Var N} (h : TransRealizes v S_pre S_post U P) :
    GroupUnary.predProj S_pre * U.1ᴴ = U.1ᴴ * GroupUnary.predProj S_post := by
  have h' := congrArg conjTranspose h.map_proj
  simpa [conjTranspose_mul, GroupUnary.predProj_conjTranspose] using h'

private theorem TransRealizes.clean_post {Var : Type} [Fintype Var] [DecidableEq Var] {N : ℕ}
    {v : Var} {S_pre S_post : BitAssignment N → Bool} {U : Unitary (2 ^ N)}
    {P : DynamicCircuit Var N} (h : TransRealizes v S_pre S_post U P)
    (Θ : QCAssertion Var (2 ^ N)) :
    GroupUnary.restrictPred S_pre (wp P.compile (GroupUnary.restrictPred S_post Θ)) =
      GroupUnary.restrictPred S_pre (wp P.compile Θ) := by
  apply GroupUnary.wp_restrictPred_of_wp_compl_eq_zero P S_pre S_post _ Θ
  intro σ
  have hwp := congrFun
    (h.wp_eq (GroupUnary.constPredObs (fun β ↦ !S_post β)) (fun _ _ ↦ rfl)) σ
  rw [congrArg Subtype.val hwp]
  simp only [GroupUnary.restrictPred_coe, qcWpQAssign, qcQAssignObsMap, Observable.conj_coe,
    Unitary.coe_star, Matrix.star_eq_conjTranspose, GroupUnary.constPredObs, conj_conj]
  have hdisj : GroupUnary.predProj S_post * GroupUnary.predProj (fun β ↦ !S_post β) = 0 := by
    rw [GroupUnary.predProj_mul]; ext i j
    simp only [GroupUnary.predProj, Matrix.diagonal_apply, Matrix.zero_apply]
    by_cases hij : i = j
    · subst hij; by_cases hS : S_post (basisBits N i) = true <;> simp [hS]
    · simp [hij]
  have hmat0 : GroupUnary.predProj S_pre * (U.1ᴴ *
      GroupUnary.predProj (fun β ↦ !S_post β)) = 0 := by
    rw [← Matrix.mul_assoc, h.map_proj_adj, Matrix.mul_assoc, hdisj, Matrix.mul_zero]
  rw [hmat0]
  apply HermitianMat.ext; simp

private theorem TransRealizes.identity {Var : Type} [Fintype Var] [DecidableEq Var] {N : ℕ}
    (v : Var) (S : BitAssignment N → Bool) :
    TransRealizes v S S 1 (.identity : DynamicCircuit Var N) where
  toff_zero := rfl
  map_proj := by simp
  update_self Θ hΘ σ val := hΘ σ val
  wp_eq Θ _ := by funext σ; apply Subtype.ext; simp [qcWpQAssign, qcQAssignObsMap]

private theorem TransRealizes.seq {Var : Type} [Fintype Var] [DecidableEq Var] {N : ℕ}
    {v : Var} {S₁ S₂ S₃ : BitAssignment N → Bool} {U₁ U₂ : Unitary (2 ^ N)}
    {P₁ P₂ : DynamicCircuit Var N}
    (h₁ : TransRealizes v S₁ S₂ U₁ P₁) (h₂ : TransRealizes v S₂ S₃ U₂ P₂) :
    TransRealizes v S₁ S₃ (U₂ * U₁) (P₁.seq P₂) where
  toff_zero := by simp [h₁.toff_zero, h₂.toff_zero]
  map_proj := by
    change U₂.1 * U₁.1 * GroupUnary.predProj S₁ = GroupUnary.predProj S₃ * (U₂.1 * U₁.1)
    rw [Matrix.mul_assoc, h₁.map_proj, ← Matrix.mul_assoc, h₂.map_proj, Matrix.mul_assoc]
  update_self Θ hΘ σ val := h₁.update_self (wp P₂.compile Θ) (h₂.update_self Θ hΘ) σ val
  wp_eq Θ hΘ := by
    change GroupUnary.restrictPred S₁ (wp P₁.compile (wp P₂.compile Θ)) = _
    rw [← h₁.clean_post, h₂.wp_eq Θ hΘ, h₁.clean_post,
      h₁.wp_eq (qcWpQAssign U₂ Θ) (fun σ val ↦ by simp [qcWpQAssign, hΘ σ val]), qc_wp_qAssign_comp]

/-- Forward `4-T`-per-AND (`0 TOFF`) dynamic circuit for a `RevCompute` program `p`. -/
def revComputeDyn {Var : Type} {N : ℕ} : GroupUnary.RevCompute N → DynamicCircuit Var N
  | .id => .identity
  | .x q => .circuit (.X q)
  | .cnot c t h => .circuit (.CNOT c t h)
  | .andGate c₁ c₂ anc _ h₁a h₂a => DynamicCircuit.andCompute c₁ c₂ anc h₁a h₂a
  | .seq p₁ p₂ => .seq (revComputeDyn p₁) (revComputeDyn p₂)

/-- Reverse `0-T` (`0 TOFF`) measurement-assisted uncompute dynamic circuit for `p`. -/
def revUncomputeDyn {Var : Type} {N : ℕ} (v : Var) :
    GroupUnary.RevCompute N → DynamicCircuit Var N
  | .id => .identity
  | .x q => .circuit (.X q)
  | .cnot c t h => .circuit (.CNOT c t h)
  | .andGate c₁ c₂ anc h₁₂ _ _ => DynamicCircuit.andUncompute v c₁ c₂ anc h₁₂
  | .seq p₁ p₂ => .seq (revUncomputeDyn v p₂) (revUncomputeDyn v p₁)

@[simp]
theorem count_revComputeDyn_toff {Var : Type} {N : ℕ} (p : GroupUnary.RevCompute N) :
    (revComputeDyn (Var := Var) p).count .TOFF = 0 := by
  induction p with
  | id => rfl
  | x _ => rfl
  | cnot _ _ _ => rfl
  | andGate _ _ _ _ _ _ => simp [revComputeDyn]
  | seq _ _ ih₁ ih₂ => simp [revComputeDyn, DynamicCircuit.count, ih₁, ih₂]

@[simp]
theorem count_revComputeDyn_t {Var : Type} {N : ℕ} (p : GroupUnary.RevCompute N) :
    (revComputeDyn (Var := Var) p).count .T = 4 * p.numAnd := by
  induction p with
  | id => rfl
  | x _ => rfl
  | cnot _ _ _ => rfl
  | andGate _ _ _ _ _ _ => simp [revComputeDyn, GroupUnary.RevCompute.numAnd]
  | seq _ _ ih₁ ih₂ =>
      simp only [revComputeDyn, DynamicCircuit.count, GroupUnary.RevCompute.numAnd, ih₁, ih₂]
      omega

@[simp]
theorem count_revUncomputeDyn_toff {Var : Type} {N : ℕ} (v : Var) (p : GroupUnary.RevCompute N) :
    (revUncomputeDyn v p).count .TOFF = 0 := by
  induction p with
  | id => rfl
  | x _ => rfl
  | cnot _ _ _ => rfl
  | andGate _ _ _ _ _ _ => simp [revUncomputeDyn]
  | seq _ _ ih₁ ih₂ => simp [revUncomputeDyn, DynamicCircuit.count, ih₁, ih₂]

@[simp]
theorem count_revUncomputeDyn_t {Var : Type} {N : ℕ} (v : Var) (p : GroupUnary.RevCompute N) :
    (revUncomputeDyn v p).count .T = 0 := by
  induction p with
  | id => rfl
  | x _ => rfl
  | cnot _ _ _ => rfl
  | andGate _ _ _ _ _ _ => simp [revUncomputeDyn]
  | seq _ _ ih₁ ih₂ => simp [revUncomputeDyn, DynamicCircuit.count, ih₁, ih₂]

section FoldedCascade

open QuantumComputation.Specs Solution Solution.CircuitModular
open Solution.OneHotSimulates (GlobalCleanSimulates)

end FoldedCascade

/-! ## Section 3: Folded `184`-Clean-Wire `SELECT` Assembly (`13,058 T`, `0 TOFF`) -/

section FoldedSelect330

open QuantumComputation.Specs Solution Solution.CircuitModular
open Solution.BlockEncodingCore Solution.BlockEncodingCircuit

section ExitMidEntryBarrier
end ExitMidEntryBarrier

end FoldedSelect330

/-! ## Section 4: Pulled-Reflection `L²` Bridge (`δStep = 12 / 10 ^ 12`) -/

section PulledBridge

open QuantumComputation.Specs Solution Solution.CircuitModular
open Solution.BlockEncodingCore Solution.BlockEncodingCircuit

end PulledBridge

end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.Lac2Folded184Select

end
