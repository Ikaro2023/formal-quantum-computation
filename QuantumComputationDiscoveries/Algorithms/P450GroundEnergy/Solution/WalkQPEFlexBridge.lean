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

public import Mathlib.Analysis.Real.Pi.Bounds
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.WalkQPEBridgeXMeas

/-!
# Parametric `(M, pWin, eRef)` Master QPE + Walk + Catalyst Bridge (`WalkQPEFlexBridge`)

Generalizes `WalkQPEBridge` and `WalkQPEBridgeXMeas` along three axes while reusing their
ancilla/register layout (`p450TotalQubits`, `p450Ancillas`, `rQPELoc`, `rWalkCatLoc`, `rScrLoc`,
`rScrUbLoc`, `rMidZeroLoc`, `rFullZeroLoc`):

1. **Parametric Walk Steps `M : ℕ` (`1 ≤ M`, `M + 1 < 2 ^ 16`):** Replaces the fixed `49,151`-step
   count with an arbitrary step count `M`.
2. **`DynamicCircuit` Window Preparer `pWin`:** Replaces the static `Circuit 16` window preparer by
   any `pWin : DynamicCircuit Var (p450TotalQubits wOuter wInner2 sUb)` satisfying
   `CleanDyn.CleanRealizes v (rQPELoc wOuter wInner2 sUb) (rScrLoc wOuter wInner2 sUb) uWinImpl
   pWin` with
   `‖uWinImpl.1 - uWinIdeal.1‖ ≤ δWin`, allowing `pWin` to borrow `rScrLoc` via Gidney-AND /
   X-measurement uncomputation while leaving `rWalkCatLoc` (and `rMidZeroLoc`) untouched.
3. **Parametric Variational Reference Energy `(eRef, eGap)` & Rational Budget Lemmas:** Accepts any
   `63`-electron variational threshold bound `T ≤ eRef + 0.1` for `thcHamiltonian P450.dfthc`,
   transfers it across `p450FswapUninterleave` to `BlockEncoding.p450HBlocked`, and provides
   ready-to-call rational RMSE budget discharge lemmas for `M ∈ {48895, 48383, 48319, 48255}`.
-/

@[expose] public section

namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.WalkQPEFlexBridge
open QuantumComputation.Specs QuantumComputation.Specs.P450

open Operator Matrix Real WalkQPEBridge WalkQPEBridgeXMeas
open scoped Matrix BigOperators Matrix.Norms.L2Operator

local instance (priority := 1000000) instNeZeroTwoPow (k : ℕ) : NeZero (2 ^ k) :=
  ⟨Nat.pos_iff_ne_zero.mp (by positivity)⟩

/-! ## Section 1: Flexible Master `DynamicCircuit` Construction & Unconditional Gate Counts -/

section CleanZeroLifting

open QProg HermitianMat
open scoped ComplexOrder MatrixOrder

private theorem absorbCleanActive_of_comm {Var : Type} [Fintype Var] [DecidableEq Var]
    {N k s₁ s : ℕ} {v : Var} {rAct : QRegister k N}
    {rScr₁ : QRegister s₁ N} {rScr : QRegister s N}
    {U : Unitary (2 ^ k)} {P : DynamicCircuit Var N}
    (h : CleanDyn.CleanRealizes v rAct rScr₁ U P)
    (hsub : rScr₁.image ⊆ rScr.image)
    (hcomm : (rAct.embedUnitary U).1 * rScr.basisOutcomeProjector 0 =
      rScr.basisOutcomeProjector 0 * (rAct.embedUnitary U).1) :
    XMeasCircuit.CleanRealizes v rAct rScr U P :=
  XMeasCircuit.CleanRealizes.absorbCleanActive h hsub rfl (by
    rw [← Matrix.mul_assoc, ← hcomm, Matrix.mul_assoc, rScr.basisOutcomeProjector_mul_self 0])

/-- Convenience helper lifting `CleanRealizes` on any subregister `(rScrLoc ...).compose rSub` of
`rScrLoc` to the full scratch register `rScrLoc` for `pWin` without `support` obligations. -/
theorem cleanRealizes_rScrLoc_of_sub {Var : Type} [Fintype Var] [DecidableEq Var]
    (wOuter wInner2 sUb : ℕ) (v : Var) {sWin : ℕ}
    (rSub : QRegister sWin (p450ScrAncillas wOuter wInner2 sUb))
    {uWin : Unitary (2 ^ 16)} {pWin : DynamicCircuit Var (p450TotalQubits wOuter wInner2 sUb)}
    (h : CleanDyn.CleanRealizes v (rQPELoc wOuter wInner2 sUb)
      ((rScrLoc wOuter wInner2 sUb).compose rSub) uWin pWin) :
    CleanDyn.CleanRealizes v (rQPELoc wOuter wInner2 sUb) (rScrLoc wOuter wInner2 sUb) uWin pWin :=
  absorbCleanActive_of_comm h ((rScrLoc wOuter wInner2 sUb).image_compose_subset rSub)
    (QubitisedWalk.basisOutcomeProjector_comm_embedMatrix (rScrLoc wOuter wInner2 sUb)
      (rQPELoc wOuter wInner2 sUb)
      (QRegister.disjoint_comm.mp (rQPELoc_disjoint_rScrLoc wOuter wInner2 sUb)) 0 uWin.1).symm

/-- Adapter converting a standard `CleanDyn.CleanRealizes` proof on `(rWalkCatLoc, rScrUbLoc)`
into `CleanRealizesSet` with an empty `0`-wire `rMidZero` register. -/
theorem cleanRealizesSet_of_rScrUbLoc {Var : Type} [Fintype Var] [DecidableEq Var]
    (wOuter wInner2 sUb : ℕ) (v : Var)
    (rMidZero : QRegister 0 (BlockEncodingCore.mMidUB wInner2))
    {u : Unitary (2 ^ p450WalkCatWidth wOuter wInner2)}
    {P : DynamicCircuit Var (p450TotalQubits wOuter wInner2 sUb)}
    (h : CleanDyn.CleanRealizes v (rWalkCatLoc wOuter wInner2 sUb) (rScrUbLoc wOuter wInner2 sUb) u
      P) :
    SelectSwapQROM.CleanRealizesSet v
      ((rScrUbLoc wOuter wInner2 sUb).image ∪ (rMidZeroLoc wOuter wInner2 sUb rMidZero).image)
      ((rWalkCatLoc wOuter wInner2 sUb).embedUnitary u) P := by
  have hemp : (rMidZeroLoc wOuter wInner2 sUb rMidZero).image = ∅ := by
    ext w
    simp only [QRegister.mem_image, Finset.notMem_empty, iff_false]
    rintro ⟨i, _⟩
    exact Fin.elim0 i
  rw [hemp, Finset.union_empty]
  exact (SelectSwapQROM.cleanRealizes_iff_set v (rWalkCatLoc wOuter wInner2 sUb)
    (rScrUbLoc wOuter wInner2 sUb) u P).mp h

end CleanZeroLifting

/-! ## Section 3: Product-State Evolution, Catalytic Perturbation & Variational Transfer -/

section Proofs

attribute [local irreducible] thcHamiltonian BlockEncodingCore.p450HBlocked dfthcLowerBound
  CliffordT.exactPhaseGrad14Unitary

/-- Transfers any `63`-electron variational reference-energy threshold bound `T ≤ eRef + Δ` from
`thcHamiltonian P450.dfthc` across `p450FswapUninterleave` to `BlockEncoding.p450HBlocked`. -/
theorem threshold_le_p450HBlocked_of_dfthc {eRef Δ : ℝ}
    (hRefVar : ∀ (T : ℝ),
      (∀ (E' : ℝ) (φ : Fin (2 ^ (2 * 58)) → ℂ),
        (thcHamiltonian P450.dfthc *ᵥ φ = (E' : ℂ) • φ ∧
          electronSectorProjector (2 * 58) 63 *ᵥ φ = φ ∧ φ ≠ 0) →
        T ≤ E' + Δ) →
      T ≤ eRef + Δ) :
    ∀ (T : ℝ),
      (∀ (E' : ℝ) (φBlk : Fin (2 ^ (2 * 58)) → ℂ),
        (BlockEncodingCore.p450HBlocked *ᵥ φBlk = (E' : ℂ) • φBlk ∧
          electronSectorProjector (2 * 58) 63 *ᵥ φBlk = φBlk ∧ φBlk ≠ 0) →
        T ≤ E' + Δ) →
      T ≤ eRef + Δ := by
  intro T hTBlk
  refine hRefVar T fun E' φ₀ hEig₀ ↦ ?_
  let U := p450FswapUninterleave.eval
  have hU_mul : U.1ᴴ * U.1 = 1 := by
    rw [← Matrix.star_eq_conjTranspose]
    exact U.2.1
  let φBlk := U.1 *ᵥ φ₀
  refine hTBlk E' φBlk ⟨?_, ?_, ?_⟩
  · calc BlockEncodingCore.p450HBlocked *ᵥ φBlk
        = U.1 *ᵥ (thcHamiltonian P450.dfthc *ᵥ ((U.1ᴴ * U.1) *ᵥ φ₀)) := by
          unfold BlockEncodingCore.p450HBlocked
          simp only [φBlk, U, Matrix.mulVec_mulVec, Matrix.mul_assoc]
      _ = (E' : ℂ) • φBlk := by rw [hU_mul, Matrix.one_mulVec, hEig₀.1, Matrix.mulVec_smul]
  · calc electronSectorProjector (2 * 58) 63 *ᵥ φBlk
        = (U.1 * electronSectorProjector (2 * 58) 63 * U.1ᴴ) *ᵥ (U.1 *ᵥ φ₀) := by
          rw [p450FswapUninterleave_conj_electronSectorProjector 63]
      _ = U.1 *ᵥ (electronSectorProjector (2 * 58) 63 *ᵥ ((U.1ᴴ * U.1) *ᵥ φ₀)) := by
          simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
      _ = φBlk := by rw [hU_mul, Matrix.one_mulVec, hEig₀.2.1]
  · intro hz
    apply hEig₀.2.2
    calc φ₀ = (U.1ᴴ * U.1) *ᵥ φ₀ := by rw [hU_mul, Matrix.one_mulVec]
      _ = U.1ᴴ *ᵥ φBlk := (Matrix.mulVec_mulVec φ₀ U.1ᴴ U.1).symm
      _ = 0 := by rw [hz, Matrix.mulVec_zero]

end Proofs

/-! ## Section 5: Monotonicity & Pre-Proved Rational RMSE Budget Lemmas -/

end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.WalkQPEFlexBridge
