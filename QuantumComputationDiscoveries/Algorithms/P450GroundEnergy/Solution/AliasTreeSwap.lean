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

public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.AliasBase

/-!
# Binary-Tree Tail Subroutine, Relocation Helpers, & `unif15`
Provides the shared `6`-wire binary-tree tail subroutine (`tailTreeLocal` / `tailTreeDagLocal`),
generic scratch-prefix register relocation (`placeWithScr`), and the `D = 15` uniform-superposition
primitive (`unif15Prog` / `unif15DagProg`).
-/

@[expose] public section

namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution
open QuantumComputation.Specs QuantumComputation.Specs.P450
namespace CoherentAlias

open Operator QProg Matrix HermitianMat Real QuantumComputation.Specs Solution Solution.CleanDyn
open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator Circuit.Notation

/-! ### Shared `6`-Wire Binary-Tree Tail Subroutine (`tailTreeLocal` & `tailTreeDagLocal`) -/

/-- Relocate a local `(k + s₀)`-wire dynamic circuit onto arbitrary disjoint active and scratch
registers `rAct : QRegister k N` and `rScr : QRegister s N` (`s₀ ≤ s`). -/
def placeWithScr {Var : Type} {k s₀ s N : ℕ} (rAct : QRegister k N) (rScr : QRegister s N)
    (hs : s₀ ≤ s) (hdisj : rAct.DisjointWires rScr) (P_loc : DynamicCircuit Var (k + s₀)) :
    DynamicCircuit Var N :=
  let subScr : QRegister s₀ s := QRegister.block 0 s₀ (by omega)
  P_loc.onRegister (rAct.concat (rScr.compose subScr) (hdisj.compose_right subScr))

@[simp]
theorem count_placeWithScr {Var : Type} {k s₀ s N a : ℕ} (rAct : QRegister k N)
    (rScr : QRegister s N) (hs : s₀ ≤ s) (hdisj : rAct.DisjointWires rScr)
    (P_loc : DynamicCircuit Var (k + s₀)) (g : PrimitiveGate a) :
    (placeWithScr rAct rScr hs hdisj P_loc).count g = P_loc.count g := by
  simp [placeWithScr]

theorem cleanRealizes_placeWithScr {Var : Type} [Fintype Var] [DecidableEq Var]
    {k s₀ s N : ℕ} [NeZero (2 ^ N)]
    (v : Var) (rAct : QRegister k N) (rScr : QRegister s N)
    (hs : s₀ ≤ s) (hdisj : rAct.DisjointWires rScr)
    (U : Unitary (2 ^ k)) (P_loc : DynamicCircuit Var (k + s₀))
    (hloc : CleanRealizes v (QRegister.block 0 k (by omega))
      (QRegister.block k s₀ (by omega)) U P_loc) :
    CleanRealizes v rAct rScr U (placeWithScr rAct rScr hs hdisj P_loc) := by
  let subScr : QRegister s₀ s := QRegister.block 0 s₀ (by omega)
  let rScr₀ : QRegister s₀ N := rScr.compose subScr
  let hdisj₀ : rAct.DisjointWires rScr₀ := hdisj.compose_right subScr
  let pl : QRegister (k + s₀) N := rAct.concat rScr₀ hdisj₀
  have hAct_eq : pl.compose (QRegister.block 0 k (by omega)) = rAct := by
    ext i
    have hi : (QRegister.block 0 k (by omega)) i = Fin.castAdd s₀ i := by ext; simp
    rw [QRegister.compose_apply, hi, QRegister.concat_apply_left]
  have hScr_eq : pl.compose (QRegister.block k s₀ (by omega)) = rScr₀ := by
    ext i
    have hi : (QRegister.block k s₀ (by omega)) i = Fin.natAdd k i := by ext; simp
    rw [QRegister.compose_apply, hi, QRegister.concat_apply_right]
  have hsub : rScr₀.image ⊆ rScr.image := by
    intro w hw
    obtain ⟨i, rfl⟩ := (QRegister.mem_image rScr₀ w).mp hw
    exact (QRegister.mem_image rScr _).mpr ⟨subScr i, rfl⟩
  have hrel := hloc.onRegister pl
  rw [hAct_eq, hScr_eq] at hrel
  exact hrel.extend_scr hdisj hsub

/-! ### Exact Action of `tailTreeIdeal` on Even-Low-Bits Basis States -/

/-! ### Uniform Superposition `unif15` (`D = 15`, `4` Active + `2` Scratch) -/

end CoherentAlias
end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution
