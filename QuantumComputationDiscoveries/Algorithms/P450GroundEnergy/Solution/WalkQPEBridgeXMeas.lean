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

public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.WalkQPEBridge
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.SelectSwapQROM
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.XMeasCircuit

/-!
# X-Measurement Clean-Reset Master QPE + Walk + Catalyst Closure

Extends `WalkQPEBridge.p450MasterProg_correctness` to catalytic `(pFwd, pBwd)` block-encoding
programs that borrow and X-measurement-reset a clean-zero subregister
`rMidZero : QRegister kMid (BlockEncodingCore.mMidUB wInner2)` of the inner state-preparation
register `rMid` (such as the `wInner2`-bit inner QROM garbage subregister `g_in`):

- **Zero Circuit or Gate-Count Duplication:** Reuses `WalkQPEBridge.p450MasterProg`,
  `p450TotalQubits`, `p450Ancillas`, `rWalkCatLoc`, `rScrUbLoc`, `rScrLoc`, `rActLoc`, `inAllCat`,
  `inMidCat`, `p450MasterProg_count_toff`, and `p450MasterProg_count_t_le` directly.
- **Overlapping Reflection Support via `absorbCleanActive`:** Although `reflMidDyn` and `reflInDyn`
  act nontrivially on `rMidZeroLoc ⊆ inMidCat ⊆ inAllCat`, their realized unitaries are diagonal in
  the computational basis and therefore commute with `(rFullZeroLoc ...).basisOutcomeProjector 0`,
  allowing `XMeasCircuit.CleanRealizes.absorbCleanActive` to thread clean-zero restoration across
  the entire `M`-step reflection-reversed walk without support-disjointness restrictions.
- **Symmetric and Asymmetric Catalytic `SELECT` Wrappers:** Provides both the symmetric
  `p450MasterProg_correctness_of_ubCat_xmeas` wrapper and the asymmetric
  `p450MasterProg_correctness_of_ubCat_asym_xmeas` wrapper supporting distinct `(selectCatFwd,
  selectCatBwd)` unitaries and error budgets `(δSelFwd, δSelBwd)`.
-/

@[expose] public section

namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.WalkQPEBridgeXMeas
open QuantumComputation.Specs QuantumComputation.Specs.P450

open Operator Matrix Real WalkQPEBridge
open scoped Matrix BigOperators Matrix.Norms.L2Operator

local instance (priority := 1000000) instNeZeroTwoPow (k : ℕ) : NeZero (2 ^ k) :=
  ⟨Nat.pos_iff_ne_zero.mp (by positivity)⟩

/-! ## Section 1: Clean-Zero Mid-Subregister Layout & Disjointness -/

/-- Local clean-zero subregister inside `p450TotalQubits wOuter wInner2 sUb` induced by a
subregister `rMidZero` of `BlockEncodingCore.mMidUB wInner2` (e.g., X-measured inner QROM garbage
wires). -/
abbrev rMidZeroLoc (wOuter wInner2 sUb : ℕ) {kMid : ℕ}
    (rMidZero : QRegister kMid (BlockEncodingCore.mMidUB wInner2)) :
    QRegister kMid (p450TotalQubits wOuter wInner2 sUb) :=
  (rWalkCatLoc wOuter wInner2 sUb).compose ((inMidCat wOuter wInner2).compose rMidZero)

theorem rScrLoc_disjoint_rMidZeroLoc (wOuter wInner2 sUb : ℕ) {kMid : ℕ}
    (rMidZero : QRegister kMid (BlockEncodingCore.mMidUB wInner2)) :
    (rScrLoc wOuter wInner2 sUb).DisjointWires (rMidZeroLoc wOuter wInner2 sUb rMidZero) :=
  QRegister.disjoint_comm.mp
    (QubitisedWalk.disjointWires_compose_left (rWalkCatLoc_disjoint_rScrLoc wOuter wInner2 sUb))

/-- Combined `(p450ScrAncillas wOuter wInner2 sUb + kMid)`-wire clean-zero register maintained
across the entire local master circuit `p450MasterLocalProg`. -/
abbrev rFullZeroLoc (wOuter wInner2 sUb : ℕ) {kMid : ℕ}
    (rMidZero : QRegister kMid (BlockEncodingCore.mMidUB wInner2)) :
    QRegister (p450ScrAncillas wOuter wInner2 sUb + kMid) (p450TotalQubits wOuter wInner2 sUb) :=
  (rScrLoc wOuter wInner2 sUb).concat (rMidZeroLoc wOuter wInner2 sUb rMidZero)
    (rScrLoc_disjoint_rMidZeroLoc wOuter wInner2 sUb rMidZero)

private theorem image_concat_eq_union {N k₁ k₂ : ℕ}
    (r₁ : QRegister k₁ N) (r₂ : QRegister k₂ N) (h : r₁.DisjointWires r₂) :
    (r₁.concat r₂ h).image = r₁.image ∪ r₂.image := by
  ext w
  simp only [QRegister.mem_image, Finset.mem_union]
  constructor
  · rintro ⟨i, rfl⟩
    obtain ⟨a | b, rfl⟩ := finSumFinEquiv.surjective i
    · exact Or.inl ⟨a, by simp⟩
    · exact Or.inr ⟨b, by simp⟩
  · rintro (⟨a, rfl⟩ | ⟨b, rfl⟩)
    · exact ⟨finSumFinEquiv (.inl a), by simp⟩
    · exact ⟨finSumFinEquiv (.inr b), by simp⟩

theorem image_rFullZeroLoc (wOuter wInner2 sUb : ℕ) {kMid : ℕ}
    (rMidZero : QRegister kMid (BlockEncodingCore.mMidUB wInner2)) :
    (rFullZeroLoc wOuter wInner2 sUb rMidZero).image =
      (rScrLoc wOuter wInner2 sUb).image ∪ (rMidZeroLoc wOuter wInner2 sUb rMidZero).image :=
  image_concat_eq_union _ _ _

section CleanZeroLifting

open QProg HermitianMat
open scoped ComplexOrder MatrixOrder

end CleanZeroLifting

/-! ## Section 3: Product-State Evolution, Catalytic Walk Perturbation & RMSE Budget -/

section Proofs

attribute [local irreducible] thcHamiltonian BlockEncodingCore.p450HBlocked dfthcLowerBound
  CliffordT.exactPhaseGrad14Unitary

end Proofs

end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.WalkQPEBridgeXMeas
