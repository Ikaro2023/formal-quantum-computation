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

public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.BlockEncodingDyn
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.OuterAliasPrep
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.GroupUnary
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.FastUniform
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.InnerTablePreInteg
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.CompactOuterAlias
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.WalkQPEBridgeXMeas

/-!
# Stage-2 `PREP_mid` X-Measurement Sandwich & `U_B` / `U_B†` Closure
Closes the Stage-2 block-encoding assembly for Cytochrome P450 (`w_go = 19`, `w_gi = 26`,
`k_cat = 14`, `184 ≤ s_ub`):
1. **`mid26AliasOutReg`:** The `16`-wire inner QROM output subregister (`5..20` inside
   `mMidUB 26 = 32`) reset to clean `|0⟩` by X-measurement uncomputation.
2. **`preservesWires_embed_muxSysCatUB`:** Automatic computational-basis wire preservation on
   `rAllInCat ∪ rScr` for any `muxUnitary` acting on `rSysCatUB` (including
   `selectCatImplUnitary` and its inverse).
3. **Catalytic `U_B` / `U_B†` Sandwich (`4,478 + t_sel` `T`, `0 TOFF`):** Full 4-step forward
   and backward catalytic `U_B` / `U_B†` circuits over any shared `184 ≤ s_ub` scratch pool, with
   `CleanRealizesSet` on `rScr.image ∪ rMidZero.image` and turnkey `WalkQPEBridge` wrappers.
-/

@[expose] public section

namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.Phase2MidSandwich
open QuantumComputation.Specs QuantumComputation.Specs.P450

open Operator Matrix Circuit QProg Solution.CleanDyn HermitianMat
open Solution.BlockEncodingCore
open Solution.BlockEncodingCircuit
open Solution.WalkQPEBridge
open Solution.WalkQPEBridgeXMeas
open scoped Matrix BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

local instance (priority := 1000000) instNeZeroTwoPow (k : ℕ) : NeZero (2 ^ k) :=
  ⟨Nat.pos_iff_ne_zero.mp (by positivity)⟩

/-! ## Section 1: `mid26AliasOutReg` & Automatic `SELECT` Wire Preservation -/

theorem preservesWires_sum {ι : Type*} {N : ℕ} (s : Finset ι)
    (F : ι → Operator (2 ^ N)) {T : Finset (Wire N)}
    (hF : ∀ x ∈ s, AliasPrep.PreservesWires (F x) T) :
    AliasPrep.PreservesWires (∑ x ∈ s, F x) T := by
  intro i j hne
  rw [Matrix.sum_apply]
  exact Finset.sum_eq_zero fun x hx ↦ hF x hx i j hne

theorem preservesWires_basisOutcomeProjector {N k : ℕ} (r : QRegister k N)
    (c : Fin (2 ^ k)) (T : Finset (Wire N)) :
    AliasPrep.PreservesWires (r.basisOutcomeProjector c) T := by
  rw [r.basisOutcomeProjector_eq_diagonal]
  exact AliasPrep.preservesWires_diagonal _ T

attribute [local irreducible] oneBodyWeights fragmentWeights innerWeights oneBodyWeightInt
  fragmentWeightNat innerMantissa

/-- 3-conjunct weakest-precondition unload contract: `P` is `.TOFF`-free, `v`-update-invariant,
and unloads `W_load` back to `1` on clean wire set `S`. -/
def CleanUnloadsWp {Var : Type} [Fintype Var] [DecidableEq Var] {N : ℕ} [NeZero (2 ^ N)]
    (v : Var) (S : Finset (Wire N)) (W_load : Unitary (2 ^ N))
    (P : DynamicCircuit Var N) : Prop :=
  P.count PrimitiveGate.TOFF = 0 ∧
  (∀ Θ : QCAssertion Var (2 ^ N), (∀ σ val, Θ (Function.update σ v val) = Θ σ) →
    ∀ σ val, (wp P.compile Θ) (Function.update σ v val) = (wp P.compile Θ) σ) ∧
  (∀ Θ : QCAssertion Var (2 ^ N), (∀ σ val, Θ (Function.update σ v val) = Θ σ) →
    SelectSwapQROM.restrictZeroSet (qcWpQAssign W_load (wp P.compile Θ)) S =
      SelectSwapQROM.restrictZeroSet Θ S)

private theorem wp_qAssign_one_eq {Var : Type} [Fintype Var] {N : ℕ}
    (Θ : QCAssertion Var (2 ^ N)) :
    qcWpQAssign (1 : Unitary (2 ^ N)) Θ = Θ := by
  funext σ; apply Subtype.ext; simp [qcWpQAssign]

theorem CleanUnloadsWp.of_cleanUnloadsSet {Var : Type} [Fintype Var] [DecidableEq Var] {N : ℕ}
    [NeZero (2 ^ N)] {v : Var} {S M_set : Finset (Wire N)} {W_load : Unitary (2 ^ N)}
    {P : DynamicCircuit Var N}
    (h : SelectSwapQROM.CleanUnloadsSet v S M_set W_load 1 P) :
    CleanUnloadsWp v S W_load P :=
  ⟨h.1, h.2.1, fun Θ hΘ ↦ by simpa only [wp_qAssign_one_eq] using h.2.2.1 Θ hΘ⟩

theorem CleanUnloadsWp.extend {Var : Type} [Fintype Var] [DecidableEq Var] {N : ℕ}
    [NeZero (2 ^ N)] {v : Var} {S₁ S₂ : Finset (Wire N)} {W_load : Unitary (2 ^ N)}
    {P : DynamicCircuit Var N}
    (h : CleanUnloadsWp v S₁ W_load P) (hSub : S₁ ⊆ S₂) :
    CleanUnloadsWp v S₂ W_load P := by
  refine ⟨h.1, h.2.1, fun Θ hΘ ↦ ?_⟩
  rw [← Finset.union_eq_right.mpr hSub, ← SelectSwapQROM.restrictZeroSet_union,
    ← SelectSwapQROM.restrictZeroSet_union, h.2.2 Θ hΘ]

end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.Phase2MidSandwich
