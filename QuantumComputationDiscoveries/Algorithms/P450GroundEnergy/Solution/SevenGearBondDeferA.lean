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

public import QuantumComputationSpecs.Algorithms.P450DFTHCData
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.DihedralWalkQPE46687
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.TailShiftWindow46847
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.TailShiftThreeGear

/-!
# Seven-Gear Bond-Deferred Dihedral Engine — Part A
Local coarse dihedral gear circuits, universal recursive peel-from-bottom schedule identities,
and parametric single-bit Möttönen window step cascades for `5`-, `6`-, and `7`-Gear (`m2 ≤ 14`)
Bond-Deferred Tail-Shifted QPE.

Refs:
- Luis & Peřina, Phys. Rev. A 54, 4564 (1996), DOI: 10.1103/PhysRevA.54.4564
- Möttönen et al., Phys. Rev. Lett. 93, 130502 (2004), DOI: 10.1103/PhysRevLett.93.130502
- Babbush et al., Phys. Rev. X 8, 041015 (2018), DOI: 10.1103/PhysRevX.8.041015
- Lee et al., PRX Quantum 2, 030305 (2021), DOI: 10.1103/PRXQuantum.2.030305
-/

@[expose] public section

namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.SevenGearBondDefer
open QuantumComputation.Specs QuantumComputation.Specs.P450

open Operator QProg Matrix HermitianMat Circuit Real QuantumComputation.Specs Solution
open QuantumComputation.Specs.P450 Solution Solution.BlockEncodingCore
open Solution.BlockEncodingCircuit Solution.TopIntegrationBridge
open Solution.WalkQPEBridge hiding
  rActLoc rActLoc_disjoint_rScrLoc rCatInAct rCatLoc rQPEInAct rQPEInAct_disjoint_rWalkCatInAct
  rQPEInAnc rQPELoc rQPELoc_disjoint_rScrLoc rQPELoc_disjoint_rWalkCatLoc rScrLoc rScrUbLoc
  rWalkCatInAct rWalkCatLoc rWalkCatLoc_disjoint_rScrLoc
open Solution.WalkQPEBridgeXMeas hiding image_rFullZeroLoc rFullZeroLoc
open Solution.WalkQPEFlexBridge hiding
  cleanRealizesSet_of_rScrUbLoc cleanRealizes_rScrLoc_of_sub
open Solution.Cat11CompactPhase2Bridge
open Solution.DihedralWalkQPE BlockReflection ApproxIqft16 SineWindowFlexM
open Solution.DihedralWalkQPE.MultiGearQPE (
  outRemWidth outZeroPrefixReg combARem combAncillas combQubits combWalkCatReg
  combWalkReflRegs combWalkReflCovers comb_hbScr16 CleanWalkRefl2 WalkRefl2ErrLe
  P450RefVarBound ReordSosHyp RealizesP450GroundQPE tensorWalkCat_smul_right approxPhaseGrad11Ray
  exactPhaseGrad11RayUnitary norm_phaseGrad11RayScalar exactPhaseGrad11RayUnitary_mulVec_zero
  approxPhaseGrad11Ray_count_toff approxPhaseGrad11Ray_count_t norm_approxPhaseGrad11Ray_sub_le)
open Solution.TwoGearBox hiding m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11
open Solution.TailShiftBox Solution.TwoGearQPEPhase5
open Solution.TwoGearBondDefer
open Solution.TailShiftWindow46847
open Solution.TailShiftThreeGear
open scoped Matrix BigOperators Matrix.Norms.L2Operator

/-! ## Section 1: Shared Type Aliases, Invariant-Subspace Predicates, & Pattern `R₀` -/

/-- Subset of `combQubitsAt b` circuits with `0` clean extra ancillas. -/
abbrev FGCircAt (Var : Type) (b wOuter wInner2 ko km sUb : ℕ) :=
  DynamicCircuit Var (combQubitsAt b wOuter wInner2 ko km 0 sUb)

/-- Subset of `combQubitsB` circuits on the unborrowed layout. -/
abbrev FGCircB (Var : Type) (wOuter wInner2 ko km sRem : ℕ) :=
  DynamicCircuit Var (combQubitsB wOuter wInner2 ko km sRem)

/-- Combined walk-and-catalyst unitary type at `(wOuter, wInner2)`. -/
abbrev FGWalkCatU (wOuter wInner2 : ℕ) :=
  Unitary (2 ^ walkCatWidth 11 (mOutUB wOuter) (mMidUB wInner2))

/-- Combined walk-and-catalyst unitary type at `(mOut, mMid)`. -/
abbrev FGWalkU (mOut mMid : ℕ) := Unitary (2 ^ walkCatWidth 11 mOut mMid)

/-- System `QRegister` alias on `n` total wires. -/
abbrev FGSysReg (n : ℕ) := QRegister systemQubits_local n

/-- Ancilla `QRegister` alias on `n` total wires. -/
abbrev FGAncReg (wOuter wInner2 ko km sRem n : ℕ) :=
  QRegister (combAncillasB wOuter wInner2 ko km sRem) n

/-- Invariant-subspace predicate type on `walkWidth mOut mMid`. -/
abbrev FGInvPred (mOut mMid : ℕ) := (Fin (2 ^ walkWidth mOut mMid) → ℂ) → Prop

/-- Pointwise `L²` bound on `tensorWalkCat v (uCatIdeal *ᵥ |0⟩)` for `K`-step super-reflection. -/
noncomputable abbrev InvCatKStepErr (mOut mMid : ℕ) (P_inv : FGInvPred mOut mMid)
    (uCatIdeal : Unitary (2 ^ 11)) (uB : Unitary (2 ^ walkWidth mOut mMid)) (K : ℕ)
    (uImpl : FGWalkU mOut mMid) (δ : ℝ) : Prop :=
  ∀ v, P_inv v →
    let R₁ := QubitisedWalk.reflInUnitary (rAllInWalk mOut mMid)
    let R₂ := QubitisedWalk.reflPulledUnitary (rMidInWalk mOut mMid) uB
    ‖WithLp.toLp 2 (uImpl.1 *ᵥ tensorWalkCat v (uCatIdeal.1 *ᵥ basisState 0) -
        tensorWalkCat ((R₁ * (R₁ * R₂) ^ K).1 *ᵥ v) (uCatIdeal.1 *ᵥ basisState 0))‖ ≤
      δ * ‖WithLp.toLp 2 (tensorWalkCat v (uCatIdeal.1 *ᵥ basisState 0))‖

/-- Pointwise `L²` bound on `tensorWalkCat v (uCatIdeal *ᵥ |0⟩)` for single reflection `R₂`. -/
noncomputable abbrev InvCatRefl2Err (mOut mMid : ℕ) (P_inv : FGInvPred mOut mMid)
    (uCatIdeal : Unitary (2 ^ 11)) (uB : Unitary (2 ^ walkWidth mOut mMid))
    (uImpl : FGWalkU mOut mMid) (δ : ℝ) : Prop :=
  ∀ v, P_inv v →
    ‖WithLp.toLp 2 (uImpl.1 *ᵥ tensorWalkCat v (uCatIdeal.1 *ᵥ basisState 0) -
        tensorWalkCat ((QubitisedWalk.reflPulledUnitary (rMidInWalk mOut mMid) uB).1 *ᵥ v)
          (uCatIdeal.1 *ᵥ basisState 0))‖ ≤
      δ * ‖WithLp.toLp 2 (tensorWalkCat v (uCatIdeal.1 *ᵥ basisState 0))‖

theorem fg_hbScr (bGear aRem mRem sUb : ℕ) :
    (bGear - 1) + (aRem - 1) ≤ scrAncillas bGear 0 aRem mRem sUb := by
  have hc := scr_ge_chunked bGear 0 aRem mRem sUb
  dsimp [chunkedCtrlScrNeed] at hc
  omega

theorem invCatRel_cond_refl {mOut mMid : ℕ} {P_inv : FGInvPred mOut mMid} {cat : Fin (2 ^ 11) → ℂ}
    {R₁c : FGWalkU mOut mMid} {R₁ : Unitary (2 ^ walkWidth mOut mMid)}
    (hRelR₁ : InvCatRel P_inv cat R₁c R₁ 0) (b : Bool) :
    InvCatRel P_inv cat (if b then R₁c else 1) (if b then R₁ else 1) 0 := by
  cases b
  · exact invCatRel_one P_inv cat
  · exact hRelR₁

/-- Walk-subspace invariance predicate closed under initial states, `R₁`, and `R₂(uB)`. -/
def WalkSubspaceClosed (wOuter wInner2 : ℕ) (uB : Unitary (2 ^ nUB wOuter wInner2))
    (P : FGInvPred (mOutUB wOuter) (mMidUB wInner2)) : Prop :=
  (∀ ψ : Fin (2 ^ systemQubits_local) → ℂ,
    P ((rSysInWalk (mOutUB wOuter) (mMidUB wInner2)).tensorState ψ (Pi.single 0 1))) ∧
  (∀ x, P x → P ((QubitisedWalk.reflInUnitary (rAllInWalk (mOutUB wOuter) (mMidUB wInner2))).1 *ᵥ
    x)) ∧
  (∀ x,
    P x → P ((QubitisedWalk.reflPulledUnitary (rMidInWalk (mOutUB wOuter) (mMidUB wInner2)) uB).1 *ᵥ
    x))

theorem walkSubspaceClosed_true (wOuter wInner2 : ℕ) (uB : Unitary (2 ^ nUB wOuter wInner2)) :
    WalkSubspaceClosed wOuter wInner2 uB (fun _ ↦ True) :=
  ⟨fun _ ↦ trivial, fun _ _ ↦ trivial, fun _ _ ↦ trivial⟩

theorem walkSubspaceClosed_inter {wOuter wInner2 : ℕ} {uB : Unitary (2 ^ nUB wOuter wInner2)}
    {P Q : FGInvPred (mOutUB wOuter) (mMidUB wInner2)}
    (hP : WalkSubspaceClosed wOuter wInner2 uB P) (hQ : WalkSubspaceClosed wOuter wInner2 uB Q) :
    WalkSubspaceClosed wOuter wInner2 uB (fun x ↦ P x ∧ Q x) :=
  ⟨fun ψ ↦ ⟨hP.1 ψ, hQ.1 ψ⟩,
   fun x hx ↦ ⟨hP.2.1 x hx.1, hQ.2.1 x hx.2⟩,
   fun x hx ↦ ⟨hP.2.2 x hx.1, hQ.2.2 x hx.2⟩⟩

theorem walkSubspaceClosed_pow {wOuter wInner2 : ℕ} {uB : Unitary (2 ^ nUB wOuter wInner2)}
    {P : FGInvPred (mOutUB wOuter) (mMidUB wInner2)} (hCl :
      WalkSubspaceClosed wOuter wInner2 uB P) (k : ℕ) :
    let R₁ := QubitisedWalk.reflInUnitary (rAllInWalk (mOutUB wOuter) (mMidUB wInner2))
    let R₂ := QubitisedWalk.reflPulledUnitary (rMidInWalk (mOutUB wOuter) (mMidUB wInner2)) uB
    ∀ x, P x → P (((R₁ * R₂) ^ k).1 *ᵥ x) := by
  intro R₁ R₂ x hx
  induction k with
  | zero => simpa using hx
  | succ n ih =>
    rw [pow_succ', Submonoid.coe_mul, Submonoid.coe_mul, Matrix.mul_assoc,
      ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    exact hCl.2.1 _ (hCl.2.2 _ ih)

theorem walkSubspaceClosed_refl_pow {wOuter wInner2 : ℕ} {uB : Unitary (2 ^ nUB wOuter wInner2)}
    {P : FGInvPred (mOutUB wOuter) (mMidUB wInner2)} (hCl :
      WalkSubspaceClosed wOuter wInner2 uB P) (k : ℕ) :
    let R₁ := QubitisedWalk.reflInUnitary (rAllInWalk (mOutUB wOuter) (mMidUB wInner2))
    let R₂ := QubitisedWalk.reflPulledUnitary (rMidInWalk (mOutUB wOuter) (mMidUB wInner2)) uB
    ∀ x, P x → P (((R₁ * (R₁ * R₂) ^ k).1) *ᵥ x) := by
  intro R₁ R₂ x hx
  rw [Submonoid.coe_mul, ← Matrix.mulVec_mulVec]
  exact hCl.2.1 _ (walkSubspaceClosed_pow hCl k x hx)

theorem walkSubspaceClosed_zpow {wOuter wInner2 : ℕ} {uB : Unitary (2 ^ nUB wOuter wInner2)}
    {P : FGInvPred (mOutUB wOuter) (mMidUB wInner2)} (hCl :
      WalkSubspaceClosed wOuter wInner2 uB P) (z : ℤ) :
    let R₁ := QubitisedWalk.reflInUnitary (rAllInWalk (mOutUB wOuter) (mMidUB wInner2))
    let R₂ := QubitisedWalk.reflPulledUnitary (rMidInWalk (mOutUB wOuter) (mMidUB wInner2)) uB
    ∀ x, P x → P (((R₁ * R₂) ^ z).1 *ᵥ x) := by
  intro R₁ R₂ x hx
  let W := R₁ * R₂
  have hR₁ : R₁ * R₁ = 1 := QubitisedWalk.reflInUnitary_mul_self _
  have hR₂ : R₂ * R₂ = 1 := QubitisedWalk.reflPulledUnitary_mul_self _ _
  have hWinv : W⁻¹ = R₂ * R₁ := inv_eq_of_mul_eq_one_left (calc
    (R₂ * R₁) * (R₁ * R₂) = R₂ * (R₁ * R₁) * R₂ := by simp only [mul_assoc]
    _ = 1 := by rw [hR₁, mul_one, hR₂])
  have hNeg (k : ℕ) : P (((W⁻¹) ^ k).1 *ᵥ x) := by
    induction k with
    | zero => simpa using hx
    | succ n ih =>
      have hstep : (W⁻¹) ^ (n + 1) = (R₂ * R₁) * (W⁻¹) ^ n :=
        (pow_succ' W⁻¹ n).trans (congrArg (· * (W⁻¹) ^ n) hWinv)
      rw [hstep, Submonoid.coe_mul, Submonoid.coe_mul, Matrix.mul_assoc,
        ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
      exact hCl.2.2 _ (hCl.2.1 _ ih)
  cases z with
  | ofNat k =>
    rw [Int.ofNat_eq_natCast, _root_.zpow_natCast]
    exact walkSubspaceClosed_pow hCl k x hx
  | negSucc k =>
    rw [_root_.zpow_negSucc, ← inv_pow]
    exact hNeg (k + 1)

theorem invCatRel_mono_err {mOut mMid : ℕ} {P : FGInvPred mOut mMid} {cat : Fin (2 ^ 11) → ℂ}
    {uImpl : FGWalkU mOut mMid} {uId : Unitary (2 ^ walkWidth mOut mMid)} {δ₁ δ₂ : ℝ}
    (hle : δ₁ ≤ δ₂) (h : InvCatRel P cat uImpl uId δ₁) : InvCatRel P cat uImpl uId δ₂ :=
  ⟨h.1, fun x hx ↦ (h.2 x hx).trans (mul_le_mul_of_nonneg_right hle (norm_nonneg _))⟩

theorem invCatRel_restrict_closed {mOut mMid : ℕ} {P P_sub : FGInvPred mOut mMid}
    {cat : Fin (2 ^ 11) → ℂ} {uImpl : FGWalkU mOut mMid}
    {uId : Unitary (2 ^ walkWidth mOut mMid)} {δ : ℝ}
    (hSub : ∀ x, P x → P_sub x) (huId : ∀ x, P x → P (uId.1 *ᵥ x))
    (h : InvCatRel P_sub cat uImpl uId δ) : InvCatRel P cat uImpl uId δ :=
  ⟨huId, fun x hx ↦ h.2 x (hSub x hx)⟩

theorem invCatRel_lift_smul_cat {mOut mMid : ℕ} {P : FGInvPred mOut mMid}
    {cat : Fin (2 ^ 11) → ℂ} {α : ℂ} (hα : ‖α‖ = 1)
    {uImpl : FGWalkU mOut mMid} {uId : Unitary (2 ^ walkWidth mOut mMid)} {δ : ℝ}
    (h : InvCatRel P cat uImpl uId δ) : InvCatRel P (α • cat) uImpl uId δ := by
  refine ⟨h.1, fun x hx ↦ ?_⟩
  have hsm (a b : Fin (2 ^ walkCatWidth 11 mOut mMid) → ℂ) :
      WithLp.toLp 2 (α • a - α • b) = α • WithLp.toLp 2 (a - b) := by
    ext g
    simp [mul_sub]
  have hsr (a : Fin (2 ^ walkCatWidth 11 mOut mMid) → ℂ) :
      WithLp.toLp 2 (α • a) = α • WithLp.toLp 2 a := by
    ext g
    rfl
  rw [tensorWalkCat_smul_right, tensorWalkCat_smul_right, Matrix.mulVec_smul,
    hsm, hsr, norm_smul, norm_smul, hα, one_mul, one_mul]
  exact h.2 x hx

/-- Pattern-controlled reflection `R₀` on `inAllWalkCat` (`4 * ((bGear - 1) + (aRem - 1))` `T`). -/
def patCtrlR0Dyn {Var : Type} (bGear bCat mOut mMid sUb : ℕ) (hbGear1 : 1 ≤ bGear) (v : Var)
    {aRem mRem : ℕ} (refl : WalkReflRegs bCat mOut mMid aRem mRem) (invertEq : Bool)
    (pat : Fin (2 ^ bGear)) :
    DynamicCircuit Var (totalQubits bGear bCat mOut mMid 0 aRem mRem sUb) :=
  QubitisedWalk.qpePatReflInDyn v invertEq pat (rQPELoc bGear bCat mOut mMid 0 aRem mRem sUb)
    ((rWalkCatLoc bGear bCat mOut mMid 0 aRem mRem sUb).compose refl.inAll)
    (rScrLoc bGear bCat mOut mMid 0 aRem mRem sUb) hbGear1 refl.haPos
    (fg_hbScr bGear aRem mRem sUb)
    (QubitisedWalk.disjointWires_compose_right
      (rQPELoc_disjoint_rWalkCatLoc bGear bCat mOut mMid 0 aRem
      mRem sUb))
    (rQPELoc_disjoint_rScrLoc bGear bCat mOut mMid 0 aRem mRem sUb)
    (QubitisedWalk.disjointWires_compose_left
      (rWalkCatLoc_disjoint_rScrLoc bGear bCat mOut mMid 0 aRem
      mRem sUb))

@[simp] theorem patCtrlR0Dyn_count_toff {Var : Type} (bGear bCat mOut mMid sUb : ℕ)
    (hbGear1 : 1 ≤ bGear) (v : Var) {aRem mRem : ℕ}
    (refl : WalkReflRegs bCat mOut mMid aRem mRem) (invertEq : Bool) (pat : Fin (2 ^ bGear)) :
    (patCtrlR0Dyn bGear bCat mOut mMid sUb hbGear1 v refl invertEq pat).count .TOFF = 0 :=
  QubitisedWalk.qpePatReflInDyn_count_toff v invertEq _ _ _ _ _ _ _ _ _ _

@[simp] theorem patCtrlR0Dyn_count_t {Var : Type} (bGear bCat mOut mMid sUb : ℕ)
    (hbGear1 : 1 ≤ bGear) (v : Var) {aRem mRem : ℕ}
    (refl : WalkReflRegs bCat mOut mMid aRem mRem) (invertEq : Bool) (pat : Fin (2 ^ bGear)) :
    (patCtrlR0Dyn bGear bCat mOut mMid sUb hbGear1 v refl invertEq pat).count .T =
      4 * ((bGear - 1) + (aRem - 1)) :=
  QubitisedWalk.qpePatReflInDyn_count_t v invertEq _ _ _ _ _ _ _ _ _ _

theorem patCtrlR0Dyn_cleanRealizes {Var : Type} [Fintype Var] [DecidableEq Var]
    (bGear bCat mOut mMid sUb : ℕ) (hbGear1 : 1 ≤ bGear) (v : Var) {aRem mRem kZero : ℕ}
    {refl : WalkReflRegs bCat mOut mMid aRem mRem} {rAncZero : QRegister kZero (mOut + mMid)}
    (hCov : WalkReflCovers bGear bCat mOut mMid 0 sUb refl rAncZero) (invertEq : Bool)
    (pat : Fin (2 ^ bGear)) :
    let rClock := rQPELoc bGear bCat mOut mMid 0 aRem mRem sUb
    let rWC := rWalkCatLoc bGear bCat mOut mMid 0 aRem mRem sUb
    let R₀ := QubitisedWalk.reflInUnitary (inAllWalkCat bCat mOut mMid)
    Solution.XMeasCircuit.CleanRealizes v
      (rClock.concat rWC (rQPELoc_disjoint_rWalkCatLoc bGear bCat mOut mMid 0 aRem mRem sUb))
      (rFullZeroLoc bGear bCat mOut mMid 0 aRem mRem sUb rAncZero)
      (QubitisedWalk.qpeMuxUnitary fun y : Fin (2 ^ bGear) ↦
        if (if invertEq then decide (y ≠ pat) else decide (y = pat)) then R₀ else 1)
      (patCtrlR0Dyn bGear bCat mOut mMid sUb hbGear1 v refl invertEq pat) := by
  intro rClock rWC R₀
  let rScr := rScrLoc bGear bCat mOut mMid 0 aRem mRem sUb
  let rFull := rFullZeroLoc bGear bCat mOut mMid 0 aRem mRem sUb rAncZero
  have hWhole := QubitisedWalk.qpePatReflInDyn_cleanRealizes_whole v invertEq pat rClock
    (rWC.compose refl.inAll) rScr hbGear1 refl.haPos (fg_hbScr bGear aRem mRem sUb)
    (QubitisedWalk.disjointWires_compose_right
      (rQPELoc_disjoint_rWalkCatLoc bGear bCat mOut mMid 0 aRem
      mRem sUb))
    (rQPELoc_disjoint_rScrLoc bGear bCat mOut mMid 0 aRem mRem sUb)
    (QubitisedWalk.disjointWires_compose_left
      (rWalkCatLoc_disjoint_rScrLoc bGear bCat mOut mMid 0 aRem
      mRem sUb))
  have hEqDiag := QubitisedWalk.diagSignUnitary_eq_embed_qpeMux_reflIn invertEq pat rClock rWC
    (rQPELoc_disjoint_rWalkCatLoc bGear bCat mOut mMid 0 aRem mRem sUb) refl.inAll
  let pred : Fin (2 ^ bGear) → Bool :=
    fun y ↦ if invertEq then decide (y ≠ pat) else decide (y = pat)
  have hEqBool :
      (QubitisedWalk.qpeMuxUnitary fun m : Fin (2 ^ bGear) ↦
        if (if invertEq then m ≠ pat else m =
          pat) then QubitisedWalk.reflInUnitary refl.inAll else 1) =
      QubitisedWalk.qpeMuxUnitary fun m : Fin (2 ^ bGear) ↦
        if pred m then QubitisedWalk.reflInUnitary refl.inAll else 1 :=
    congrArg QubitisedWalk.qpeMuxUnitary (funext fun m ↦ by
      cases invertEq
      · by_cases hm : m = pat
        · simp [pred, hm]
        · simp [pred, hm]
      · by_cases hm : m = pat
        · simp [pred, hm]
        · simp [pred, hm])
  have hComb := Solution.CleanDyn.CleanRealizes.of_whole
    (cleanRealizes_of_eq hWhole (hEqDiag.trans (congrArg _ hEqBool)))
  have hsub : rScr.image ⊆ rFull.image := by
    rw [image_rFullZeroLoc]
    exact Finset.subset_union_left
  exact absorbCleanActive_of_comm2 hComb hsub (embed_qpeMux_reflIn_mul_rFullZero hCov pred)
    (embed_qpeMux_reflIn_comm_rFullZero rAncZero pred)

/-- Identity (`0`-gate) local gear dynamic circuit for unused top gears in `5`- and `6`-Gear QPE. -/
def noopGearLocalDyn {Var : Type} (bGear bCat mOut mMid aRem mRem sUb : ℕ) :
    DynamicCircuit Var (totalQubits bGear bCat mOut mMid 0 aRem mRem sUb) :=
  .identity

@[simp] theorem noopGearLocalDyn_count {Var : Type} {dg : ℕ}
    (bGear bCat mOut mMid aRem mRem sUb : ℕ) (g : PrimitiveGate dg) :
    (noopGearLocalDyn (Var := Var) bGear bCat mOut mMid aRem mRem sUb).count g = 0 :=
  rfl

theorem noopGearLocalDyn_cleanRealizes {Var : Type} [Fintype Var] [DecidableEq Var]
    (bGear bCat mOut mMid aRem mRem sUb : ℕ) (v : Var) {kZero : ℕ}
    (rAncZero : QRegister kZero (mOut + mMid)) :
    Solution.XMeasCircuit.CleanRealizes v
      ((rQPELoc bGear bCat mOut mMid 0 aRem mRem sUb).concat
        (rWalkCatLoc bGear bCat mOut mMid 0 aRem mRem sUb)
        (rQPELoc_disjoint_rWalkCatLoc bGear bCat mOut mMid 0 aRem mRem sUb))
      (rFullZeroLoc bGear bCat mOut mMid 0 aRem mRem sUb rAncZero)
      (QubitisedWalk.qpeMuxUnitary fun _ : Fin (2 ^ bGear) ↦
        (1 : Unitary (2 ^ walkCatWidth bCat mOut mMid)))
      (noopGearLocalDyn bGear bCat mOut mMid aRem mRem sUb) := by
  rw [QubitisedWalk.qpeMuxUnitary_one]
  exact Solution.CleanDyn.CleanRealizes.identity v _ _

/-! ## Section 2: Local Coarse Dihedral Gear Primitives (`G0`..`G4`) -/

/-- `2`-bit top coarse gear `G0` (`14..15`) circuit (`12 * (aRem - 1) + 4` `T` + `pA + pB`). -/
def topG0LocalDyn {Var : Type} (bCat mOut mMid sUb : ℕ) (v : Var) {aRem mRem : ℕ}
    (refl : WalkReflRegs bCat mOut mMid aRem mRem)
    (pA pB : DynamicCircuit Var (totalQubits 2 bCat mOut mMid 0 aRem mRem sUb)) :
    DynamicCircuit Var (totalQubits 2 bCat mOut mMid 0 aRem mRem sUb) :=
  .seq (patCtrlR0Dyn 2 bCat mOut mMid sUb (by decide) v refl false ⟨0, by decide⟩)
    (.seq pA
      (.seq (bitCtrlR0Dyn 2 bCat mOut mMid 0 sUb v refl false ⟨0, by decide⟩)
        (.seq pB (bitCtrlR0Dyn 2 bCat mOut mMid 0 sUb v refl true ⟨1, by decide⟩))))

/-- `2`-bit top coarse gear `G0` fiber realized by `topG0LocalDyn`. -/
noncomputable def topG0Fiber {d : ℕ} (uA uB R₀ : Unitary d) (x : Fin (2 ^ 2)) : Unitary d :=
  (if x.val.testBit 1 == true then R₀ else 1) *
    (uB * ((if x.val.testBit 0 == false then R₀ else 1) *
      (uA * (if decide (x = ⟨0, by decide⟩) then R₀ else 1))))

theorem topG0LocalDyn_count_toff {Var : Type} (bCat mOut mMid sUb : ℕ) (v : Var) {aRem mRem : ℕ}
    (refl : WalkReflRegs bCat mOut mMid aRem mRem)
    {pA pB : DynamicCircuit Var (totalQubits 2 bCat mOut mMid 0 aRem mRem sUb)}
    (hA : pA.count .TOFF = 0) (hB : pB.count .TOFF = 0) :
    (topG0LocalDyn bCat mOut mMid sUb v refl pA pB).count .TOFF = 0 := by
  simp [topG0LocalDyn, hA, hB]

theorem topG0LocalDyn_count_t {Var : Type} (bCat mOut mMid sUb : ℕ) (v : Var) {aRem mRem : ℕ}
    (refl : WalkReflRegs bCat mOut mMid aRem mRem)
    (pA pB : DynamicCircuit Var (totalQubits 2 bCat mOut mMid 0 aRem mRem sUb)) :
    (topG0LocalDyn bCat mOut mMid sUb v refl pA pB).count .T =
      pA.count .T + pB.count .T + 12 * (aRem - 1) + 4 := by
  simp only [topG0LocalDyn, DynamicCircuit.count, bitCtrlR0Dyn_count_t, patCtrlR0Dyn_count_t]
  omega

theorem topG0LocalDyn_cleanRealizes {Var : Type} [Fintype Var] [DecidableEq Var]
    (bCat mOut mMid sUb : ℕ) (v : Var) {aRem mRem kZero : ℕ}
    {refl : WalkReflRegs bCat mOut mMid aRem mRem} {rAncZero : QRegister kZero (mOut + mMid)}
    (hCov : WalkReflCovers 2 bCat mOut mMid 0 sUb refl rAncZero)
    {uA uB : Unitary (2 ^ walkCatWidth bCat mOut mMid)}
    {pA pB : DynamicCircuit Var (totalQubits 2 bCat mOut mMid 0 aRem mRem sUb)}
    (hA : Solution.XMeasCircuit.CleanRealizes v (rWalkCatLoc 2 bCat mOut mMid 0 aRem mRem sUb)
      (rFullZeroLoc 2 bCat mOut mMid 0 aRem mRem sUb rAncZero) uA pA)
    (hB : Solution.XMeasCircuit.CleanRealizes v (rWalkCatLoc 2 bCat mOut mMid 0 aRem mRem sUb)
      (rFullZeroLoc 2 bCat mOut mMid 0 aRem mRem sUb rAncZero) uB pB) :
    let R₀ := QubitisedWalk.reflInUnitary (inAllWalkCat bCat mOut mMid)
    Solution.XMeasCircuit.CleanRealizes v
      ((rQPELoc 2 bCat mOut mMid 0 aRem mRem sUb).concat
        (rWalkCatLoc 2 bCat mOut mMid 0 aRem mRem sUb)
        (rQPELoc_disjoint_rWalkCatLoc 2 bCat mOut mMid 0 aRem mRem sUb))
      (rFullZeroLoc 2 bCat mOut mMid 0 aRem mRem sUb rAncZero)
      (QubitisedWalk.qpeMuxUnitary (topG0Fiber uA uB R₀))
      (topG0LocalDyn bCat mOut mMid sUb v refl pA pB) := by
  intro R₀
  have hsA := cleanRealizes_walkOnCombined2
    (rQPELoc_disjoint_rWalkCatLoc 2 bCat mOut mMid 0 aRem mRem sUb) hA
  have hsB := cleanRealizes_walkOnCombined2
    (rQPELoc_disjoint_rWalkCatLoc 2 bCat mOut mMid 0 aRem mRem sUb) hB
  refine cleanRealizes_of_eq
    ((patCtrlR0Dyn_cleanRealizes 2 bCat mOut mMid sUb (by decide) v hCov false
      ⟨0, by decide⟩).seq
      (hsA.seq ((bitCtrlR0Dyn_cleanRealizes 2 bCat mOut mMid 0 sUb v hCov false
        ⟨0, by decide⟩).seq
        (hsB.seq (bitCtrlR0Dyn_cleanRealizes 2 bCat mOut mMid 0 sUb v hCov true
          ⟨1, by decide⟩))))) ?_
  simp only [← QubitisedWalk.qpeMuxUnitary_mul, Bool.false_eq_true, ↓reduceIte]
  exact congrArg QubitisedWalk.qpeMuxUnitary (funext fun x ↦ by
    dsimp only [R₀, topG0Fiber, Fin.val_zero, Fin.val_one]
    simp only [mul_assoc])

theorem invCatRelTopG0Fiber {mOut mMid : ℕ} {P_inv : FGInvPred mOut mMid}
    {cat : Fin (2 ^ 11) → ℂ} {R₁c uA uB : FGWalkU mOut mMid}
    {R₁ RA RB : Unitary (2 ^ walkWidth mOut mMid)} {δA δB : ℝ}
    (hRelR₁ : InvCatRel P_inv cat R₁c R₁ 0)
    (hRelA : InvCatRel P_inv cat uA RA δA) (hRelB : InvCatRel P_inv cat uB RB δB)
    (x : Fin (2 ^ 2)) :
    InvCatRel P_inv cat (topG0Fiber uA uB R₁c x) (topG0Fiber RA RB R₁ x) (δA + δB) := by
  have hm := invCatRel_mul (invCatRel_cond_refl hRelR₁ (x.val.testBit 1 == true))
    (invCatRel_mul hRelB (invCatRel_mul (invCatRel_cond_refl hRelR₁ (x.val.testBit 0 == false))
      (invCatRel_mul hRelA (invCatRel_cond_refl hRelR₁ (decide (x = ⟨0, by decide⟩))))))
  refine ⟨hm.1, fun v hv ↦ (hm.2 v hv).trans_eq ?_⟩
  ring

/-- Odd-peel `bGear`-bit two-step local circuit (`16 * (aRem - 1) + 8 * (bGear - 1)` `T`). -/
def patFlipTwoStepLocalDyn {Var : Type} (bGear bCat mOut mMid sUb : ℕ) (hbGear1 : 1 ≤ bGear)
    (pat : Fin (2 ^ bGear)) (v : Var) {aRem mRem : ℕ}
    (refl : WalkReflRegs bCat mOut mMid aRem mRem)
    (pA pB : DynamicCircuit Var (totalQubits bGear bCat mOut mMid 0 aRem mRem sUb)) :
    DynamicCircuit Var (totalQubits bGear bCat mOut mMid 0 aRem mRem sUb) :=
  .seq (bitCtrlR0Dyn bGear bCat mOut mMid 0 sUb v refl false ⟨0, hbGear1⟩)
    (.seq (patCtrlR0Dyn bGear bCat mOut mMid sUb hbGear1 v refl false pat)
      (.seq pA
        (.seq (patCtrlR0Dyn bGear bCat mOut mMid sUb hbGear1 v refl true pat)
          (.seq pB (bitCtrlR0Dyn bGear bCat mOut mMid 0 sUb v refl true ⟨0, hbGear1⟩)))))

/-- `bGear`-bit two-step fiber realized by `patFlipTwoStepLocalDyn`. -/
noncomputable def patFlipTwoStepFiber {bGear d : ℕ} (uA uB R₀ : Unitary d)
    (pat : Fin (2 ^ bGear)) (x : Fin (2 ^ bGear)) : Unitary d :=
  (if x.val.testBit 0 == true then R₀ else 1) *
    (uB * ((if decide (x ≠ pat) then R₀ else 1) *
      (uA * ((if decide (x = pat) then R₀ else 1) *
        (if x.val.testBit 0 == false then R₀ else 1)))))

theorem patFlipTwoStepLocalDyn_count_toff {Var : Type} (bGear bCat mOut mMid sUb : ℕ)
    (hbGear1 : 1 ≤ bGear) (pat : Fin (2 ^ bGear)) (v : Var) {aRem mRem : ℕ}
    (refl : WalkReflRegs bCat mOut mMid aRem mRem)
    {pA pB : DynamicCircuit Var (totalQubits bGear bCat mOut mMid 0 aRem mRem sUb)}
    (hA : pA.count .TOFF = 0) (hB : pB.count .TOFF = 0) :
    (patFlipTwoStepLocalDyn bGear bCat mOut mMid sUb hbGear1 pat v refl pA pB).count .TOFF = 0 :=
  by simp [patFlipTwoStepLocalDyn, hA, hB]

theorem patFlipTwoStepLocalDyn_count_t {Var : Type} (bGear bCat mOut mMid sUb : ℕ)
    (hbGear1 : 1 ≤ bGear) (pat : Fin (2 ^ bGear)) (v : Var) {aRem mRem : ℕ}
    (refl : WalkReflRegs bCat mOut mMid aRem mRem)
    (pA pB : DynamicCircuit Var (totalQubits bGear bCat mOut mMid 0 aRem mRem sUb)) :
    (patFlipTwoStepLocalDyn bGear bCat mOut mMid sUb hbGear1 pat v refl pA pB).count .T =
      pA.count .T + pB.count .T + 16 * (aRem - 1) + 8 * (bGear - 1) := by
  simp only [patFlipTwoStepLocalDyn, DynamicCircuit.count, bitCtrlR0Dyn_count_t,
    patCtrlR0Dyn_count_t]
  omega

theorem patFlipTwoStepLocalDyn_cleanRealizes {Var : Type} [Fintype Var] [DecidableEq Var]
    (bGear bCat mOut mMid sUb : ℕ) (hbGear1 : 1 ≤ bGear) (pat : Fin (2 ^ bGear)) (v : Var)
    {aRem mRem kZero : ℕ} {refl : WalkReflRegs bCat mOut mMid aRem mRem}
    {rAncZero : QRegister kZero (mOut + mMid)}
    (hCov : WalkReflCovers bGear bCat mOut mMid 0 sUb refl rAncZero)
    {uA uB : Unitary (2 ^ walkCatWidth bCat mOut mMid)}
    {pA pB : DynamicCircuit Var (totalQubits bGear bCat mOut mMid 0 aRem mRem sUb)}
    (hA : Solution.XMeasCircuit.CleanRealizes v (rWalkCatLoc bGear bCat mOut mMid 0 aRem mRem sUb)
      (rFullZeroLoc bGear bCat mOut mMid 0 aRem mRem sUb rAncZero) uA pA)
    (hB : Solution.XMeasCircuit.CleanRealizes v (rWalkCatLoc bGear bCat mOut mMid 0 aRem mRem sUb)
      (rFullZeroLoc bGear bCat mOut mMid 0 aRem mRem sUb rAncZero) uB pB) :
    let R₀ := QubitisedWalk.reflInUnitary (inAllWalkCat bCat mOut mMid)
    Solution.XMeasCircuit.CleanRealizes v
      ((rQPELoc bGear bCat mOut mMid 0 aRem mRem sUb).concat
        (rWalkCatLoc bGear bCat mOut mMid 0 aRem mRem sUb)
        (rQPELoc_disjoint_rWalkCatLoc bGear bCat mOut mMid 0 aRem mRem sUb))
      (rFullZeroLoc bGear bCat mOut mMid 0 aRem mRem sUb rAncZero)
      (QubitisedWalk.qpeMuxUnitary (patFlipTwoStepFiber uA uB R₀ pat))
      (patFlipTwoStepLocalDyn bGear bCat mOut mMid sUb hbGear1 pat v refl pA pB) := by
  intro R₀
  have hsA := cleanRealizes_walkOnCombined2
    (rQPELoc_disjoint_rWalkCatLoc bGear bCat mOut mMid 0 aRem mRem sUb) hA
  have hsB := cleanRealizes_walkOnCombined2
    (rQPELoc_disjoint_rWalkCatLoc bGear bCat mOut mMid 0 aRem mRem sUb) hB
  refine cleanRealizes_of_eq
    ((bitCtrlR0Dyn_cleanRealizes bGear bCat mOut mMid 0 sUb v hCov false ⟨0, hbGear1⟩).seq
      ((patCtrlR0Dyn_cleanRealizes bGear bCat mOut mMid sUb hbGear1 v hCov false pat).seq
        (hsA.seq ((patCtrlR0Dyn_cleanRealizes bGear bCat mOut mMid sUb hbGear1 v hCov true
          pat).seq
          (hsB.seq (bitCtrlR0Dyn_cleanRealizes bGear bCat mOut mMid 0 sUb v hCov true
            ⟨0, hbGear1⟩)))))) ?_
  simp only [← QubitisedWalk.qpeMuxUnitary_mul, Bool.false_eq_true, ↓reduceIte]
  exact congrArg QubitisedWalk.qpeMuxUnitary (funext fun x ↦ by
    dsimp only [R₀, patFlipTwoStepFiber]
    simp only [mul_assoc])

theorem invCatRelPatFlipTwoStepFiber {bGear mOut mMid : ℕ} {P_inv : FGInvPred mOut mMid}
    {cat : Fin (2 ^ 11) → ℂ} {R₁c uA uB : FGWalkU mOut mMid}
    {R₁ RA RB : Unitary (2 ^ walkWidth mOut mMid)} {δA δB : ℝ}
    (hRelR₁ : InvCatRel P_inv cat R₁c R₁ 0)
    (hRelA : InvCatRel P_inv cat uA RA δA) (hRelB : InvCatRel P_inv cat uB RB δB)
    (pat x : Fin (2 ^ bGear)) :
    InvCatRel P_inv cat (patFlipTwoStepFiber uA uB R₁c pat x)
      (patFlipTwoStepFiber RA RB R₁ pat x) (δA + δB) := by
  have hm := invCatRel_mul (invCatRel_cond_refl hRelR₁ (x.val.testBit 0 == true))
    (invCatRel_mul hRelB (invCatRel_mul (invCatRel_cond_refl hRelR₁ (decide (x ≠ pat)))
      (invCatRel_mul hRelA (invCatRel_mul (invCatRel_cond_refl hRelR₁ (decide (x = pat)))
        (invCatRel_cond_refl hRelR₁ (x.val.testBit 0 == false))))))
  refine ⟨hm.1, fun v hv ↦ (hm.2 v hv).trans_eq ?_⟩
  ring

theorem patFlipTwoStep_ideal_eq_zpow {bGear d : ℕ} {R₁ R₂ : Unitary d}
    (hR₁ : R₁ * R₁ = 1) (hR₂ : R₂ * R₂ = 1) (kA kB : ℕ)
    (pat : Fin (2 ^ bGear)) (hEven : pat.val.testBit 0 = false) (x : Fin (2 ^ bGear)) :
    let W := R₁ * R₂
    patFlipTwoStepFiber (R₁ * W ^ kA) (R₁ * W ^ kB) R₁ pat x =
      W ^ (if x = pat then (kA : ℤ) - (kB : ℤ)
           else if x.val.testBit 0 then ((kA : ℤ) + (kB : ℤ))
           else -((kA : ℤ) + (kB : ℤ))) := by
  intro W
  have hnegA : (R₁ * W ^ kA) * R₁ = W ^ (-(kA : ℤ)) := refl_conj_walk_pow_eq_zpow_neg hR₁ hR₂ kA
  have hnegB : (R₁ * W ^ kB) * R₁ = W ^ (-(kB : ℤ)) := refl_conj_walk_pow_eq_zpow_neg hR₁ hR₂ kB
  have hpos (k : ℕ) : R₁ * (R₁ * W ^ k) = W ^ (k : ℤ) := by
    rw [← mul_assoc, hR₁, one_mul, ← _root_.zpow_natCast]
  have ⟨hft, hff, htt, htf⟩ :
      (false == true) = false ∧ (false == false) = true ∧
      (true == true) = true ∧ (true == false) = false := ⟨rfl, rfl, rfl, rfl⟩
  by_cases hxp : x = pat
  · have hb0 : x.val.testBit 0 = false := hxp ▸ hEven
    rw [patFlipTwoStepFiber, ite_eq_left hxp, hb0, hft, hff, decide_eq_true hxp,
      decide_eq_false (not_not.mpr hxp)]
    simp only [Bool.false_eq_true, ↓reduceIte, one_mul, hR₁, mul_one]
    rw [← mul_assoc (R₁ * W ^ kB) R₁, hnegB, ← _root_.zpow_natCast W kA, ← _root_.zpow_add]
    congr 1
    ring
  · rw [patFlipTwoStepFiber, ite_eq_right hxp, decide_eq_false hxp, decide_eq_true hxp]
    cases hb0 : x.val.testBit 0
    · rw [hft, hff]
      simp only [Bool.false_eq_true, ↓reduceIte, one_mul]
      rw [← mul_assoc (R₁ * W ^ kB) R₁, hnegB, hnegA, ← _root_.zpow_add]
      congr 1
      ring
    · rw [htt, htf]
      simp only [Bool.false_eq_true, ↓reduceIte, mul_one]
      rw [← mul_assoc R₁ (R₁ * W ^ kB), hpos kB, hpos kA, ← _root_.zpow_add]
      congr 1
      ring

/-- Even-peel `bGear`-bit single-step local circuit (`16 * (aRem - 1) + 8 * (bGear - 1)` `T`). -/
def singleSignedLocalDyn {Var : Type} (bGear bCat mOut mMid sUb : ℕ) (hbGear1 : 1 ≤ bGear)
    (pat : Fin (2 ^ bGear)) (v : Var) {aRem mRem : ℕ}
    (refl : WalkReflRegs bCat mOut mMid aRem mRem)
    (pK : DynamicCircuit Var (totalQubits bGear bCat mOut mMid 0 aRem mRem sUb)) :
    DynamicCircuit Var (totalQubits bGear bCat mOut mMid 0 aRem mRem sUb) :=
  .seq (bitCtrlR0Dyn bGear bCat mOut mMid 0 sUb v refl false ⟨0, hbGear1⟩)
    (.seq (patCtrlR0Dyn bGear bCat mOut mMid sUb hbGear1 v refl false pat)
      (.seq pK
        (.seq (patCtrlR0Dyn bGear bCat mOut mMid sUb hbGear1 v refl false pat)
          (bitCtrlR0Dyn bGear bCat mOut mMid 0 sUb v refl true ⟨0, hbGear1⟩))))

/-- `bGear`-bit single-primitive fiber realized by `singleSignedLocalDyn`. -/
noncomputable def singleSignedFiber {bGear d : ℕ} (uK R₀ : Unitary d)
    (pat : Fin (2 ^ bGear)) (x : Fin (2 ^ bGear)) : Unitary d :=
  (if x.val.testBit 0 == true then R₀ else 1) *
    ((if decide (x = pat) then R₀ else 1) *
      (uK * ((if decide (x = pat) then R₀ else 1) *
        (if x.val.testBit 0 == false then R₀ else 1))))

theorem singleSignedLocalDyn_count_toff {Var : Type} (bGear bCat mOut mMid sUb : ℕ)
    (hbGear1 : 1 ≤ bGear) (pat : Fin (2 ^ bGear)) (v : Var) {aRem mRem : ℕ}
    (refl : WalkReflRegs bCat mOut mMid aRem mRem)
    {pK : DynamicCircuit Var (totalQubits bGear bCat mOut mMid 0 aRem mRem sUb)}
    (hK : pK.count .TOFF = 0) :
    (singleSignedLocalDyn bGear bCat mOut mMid sUb hbGear1 pat v refl pK).count .TOFF = 0 := by
  simp [singleSignedLocalDyn, hK]

theorem singleSignedLocalDyn_count_t {Var : Type} (bGear bCat mOut mMid sUb : ℕ)
    (hbGear1 : 1 ≤ bGear) (pat : Fin (2 ^ bGear)) (v : Var) {aRem mRem : ℕ}
    (refl : WalkReflRegs bCat mOut mMid aRem mRem)
    (pK : DynamicCircuit Var (totalQubits bGear bCat mOut mMid 0 aRem mRem sUb)) :
    (singleSignedLocalDyn bGear bCat mOut mMid sUb hbGear1 pat v refl pK).count .T =
      pK.count .T + 16 * (aRem - 1) + 8 * (bGear - 1) := by
  simp only [singleSignedLocalDyn, DynamicCircuit.count, bitCtrlR0Dyn_count_t,
    patCtrlR0Dyn_count_t]
  omega

theorem singleSignedLocalDyn_cleanRealizes {Var : Type} [Fintype Var] [DecidableEq Var]
    (bGear bCat mOut mMid sUb : ℕ) (hbGear1 : 1 ≤ bGear) (pat : Fin (2 ^ bGear)) (v : Var)
    {aRem mRem kZero : ℕ} {refl : WalkReflRegs bCat mOut mMid aRem mRem}
    {rAncZero : QRegister kZero (mOut + mMid)}
    (hCov : WalkReflCovers bGear bCat mOut mMid 0 sUb refl rAncZero)
    {uK : Unitary (2 ^ walkCatWidth bCat mOut mMid)}
    {pK : DynamicCircuit Var (totalQubits bGear bCat mOut mMid 0 aRem mRem sUb)}
    (hK : Solution.XMeasCircuit.CleanRealizes v (rWalkCatLoc bGear bCat mOut mMid 0 aRem mRem sUb)
      (rFullZeroLoc bGear bCat mOut mMid 0 aRem mRem sUb rAncZero) uK pK) :
    let R₀ := QubitisedWalk.reflInUnitary (inAllWalkCat bCat mOut mMid)
    Solution.XMeasCircuit.CleanRealizes v
      ((rQPELoc bGear bCat mOut mMid 0 aRem mRem sUb).concat
        (rWalkCatLoc bGear bCat mOut mMid 0 aRem mRem sUb)
        (rQPELoc_disjoint_rWalkCatLoc bGear bCat mOut mMid 0 aRem mRem sUb))
      (rFullZeroLoc bGear bCat mOut mMid 0 aRem mRem sUb rAncZero)
      (QubitisedWalk.qpeMuxUnitary (singleSignedFiber uK R₀ pat))
      (singleSignedLocalDyn bGear bCat mOut mMid sUb hbGear1 pat v refl pK) := by
  intro R₀
  have hsK := cleanRealizes_walkOnCombined2
    (rQPELoc_disjoint_rWalkCatLoc bGear bCat mOut mMid 0 aRem mRem sUb) hK
  refine cleanRealizes_of_eq
    ((bitCtrlR0Dyn_cleanRealizes bGear bCat mOut mMid 0 sUb v hCov false ⟨0, hbGear1⟩).seq
      ((patCtrlR0Dyn_cleanRealizes bGear bCat mOut mMid sUb hbGear1 v hCov false pat).seq
        (hsK.seq ((patCtrlR0Dyn_cleanRealizes bGear bCat mOut mMid sUb hbGear1 v hCov false
          pat).seq
          (bitCtrlR0Dyn_cleanRealizes bGear bCat mOut mMid 0 sUb v hCov true ⟨0, hbGear1⟩)))))
    ?_
  simp only [← QubitisedWalk.qpeMuxUnitary_mul, Bool.false_eq_true, ↓reduceIte]
  exact congrArg QubitisedWalk.qpeMuxUnitary (funext fun x ↦ by
    dsimp only [R₀, singleSignedFiber]
    simp only [mul_assoc])

theorem invCatRelSingleSignedFiber {bGear mOut mMid : ℕ} {P_inv : FGInvPred mOut mMid}
    {cat : Fin (2 ^ 11) → ℂ} {R₁c uK : FGWalkU mOut mMid}
    {R₁ RK : Unitary (2 ^ walkWidth mOut mMid)} {δK : ℝ}
    (hRelR₁ : InvCatRel P_inv cat R₁c R₁ 0) (hRelK : InvCatRel P_inv cat uK RK δK)
    (pat x : Fin (2 ^ bGear)) :
    InvCatRel P_inv cat (singleSignedFiber uK R₁c pat x)
      (singleSignedFiber RK R₁ pat x) δK := by
  have hm := invCatRel_mul (invCatRel_cond_refl hRelR₁ (x.val.testBit 0 == true))
    (invCatRel_mul (invCatRel_cond_refl hRelR₁ (decide (x = pat)))
      (invCatRel_mul hRelK (invCatRel_mul (invCatRel_cond_refl hRelR₁ (decide (x = pat)))
        (invCatRel_cond_refl hRelR₁ (x.val.testBit 0 == false)))))
  refine ⟨hm.1, fun v hv ↦ (hm.2 v hv).trans_eq ?_⟩
  ring

theorem singleSigned_ideal_eq_zpow {bGear d : ℕ} {R₁ R₂ : Unitary d}
    (hR₁ : R₁ * R₁ = 1) (hR₂ : R₂ * R₂ = 1) (K : ℕ)
    (pat : Fin (2 ^ bGear)) (hEven : pat.val.testBit 0 = false) (x : Fin (2 ^ bGear)) :
    let W := R₁ * R₂
    singleSignedFiber (R₁ * W ^ K) R₁ pat x =
      W ^ (if x = pat then (K : ℤ) else if x.val.testBit 0 then (K : ℤ) else -(K : ℤ)) := by
  intro W
  have hnegK : (R₁ * W ^ K) * R₁ = W ^ (-(K : ℤ)) := refl_conj_walk_pow_eq_zpow_neg hR₁ hR₂ K
  have hposK : R₁ * (R₁ * W ^ K) = W ^ (K : ℤ) := by
    rw [← mul_assoc, hR₁, one_mul, ← _root_.zpow_natCast]
  have ⟨hft, hff, htt, htf⟩ :
      (false == true) = false ∧ (false == false) = true ∧
      (true == true) = true ∧ (true == false) = false := ⟨rfl, rfl, rfl, rfl⟩
  by_cases hxp : x = pat
  · have hb0 : x.val.testBit 0 = false := hxp ▸ hEven
    rw [singleSignedFiber, ite_eq_left hxp, hb0, hft, hff, decide_eq_true hxp]
    simp only [Bool.false_eq_true, ↓reduceIte, one_mul, hR₁, mul_one, hposK]
  · rw [singleSignedFiber, ite_eq_right hxp, decide_eq_false hxp]
    cases hb0 : x.val.testBit 0
    · rw [hft, hff]
      simp only [Bool.false_eq_true, ↓reduceIte, one_mul, hnegK]
    · rw [htt, htf]
      simp only [Bool.false_eq_true, ↓reduceIte, one_mul, mul_one, hposK]

/-- Unified symbolic peel gear on `bGear` bits (`top` odd -> `patFlipTwoStepLocalDyn` on `top-1`,
`top` even -> `singleSignedLocalDyn` on `top`). -/
def peelGearLocalDyn {Var : Type} (bGear bCat mOut mMid sUb top : ℕ)
    (hbGear1 : 1 ≤ bGear) (htop_lt : top < 2 ^ bGear) (v : Var) {aRem mRem : ℕ}
    (refl : WalkReflRegs bCat mOut mMid aRem mRem)
    (pA pB : DynamicCircuit Var (totalQubits bGear bCat mOut mMid 0 aRem mRem sUb)) :
    DynamicCircuit Var (totalQubits bGear bCat mOut mMid 0 aRem mRem sUb) :=
  if top % 2 = 1 then
    patFlipTwoStepLocalDyn bGear bCat mOut mMid sUb hbGear1 ⟨top - 1, by omega⟩ v refl pA pB
  else
    singleSignedLocalDyn bGear bCat mOut mMid sUb hbGear1 ⟨top, htop_lt⟩ v refl pA

/-- Unified symbolic peel fiber realized by `peelGearLocalDyn`. -/
noncomputable def peelGearFiber {bGear d : ℕ} (top : ℕ) (htop_lt : top < 2 ^ bGear)
    (uA uB R₀ : Unitary d) (x : Fin (2 ^ bGear)) : Unitary d :=
  if top % 2 = 1 then
    patFlipTwoStepFiber uA uB R₀ ⟨top - 1, by omega⟩ x
  else
    singleSignedFiber uA R₀ ⟨top, htop_lt⟩ x

theorem peelGearLocalDyn_count_toff {Var : Type} (bGear bCat mOut mMid sUb top : ℕ)
    (hbGear1 : 1 ≤ bGear) (htop_lt : top < 2 ^ bGear) (v : Var) {aRem mRem : ℕ}
    (refl : WalkReflRegs bCat mOut mMid aRem mRem)
    {pA pB : DynamicCircuit Var (totalQubits bGear bCat mOut mMid 0 aRem mRem sUb)}
    (hA : pA.count .TOFF = 0) (hB : pB.count .TOFF = 0) :
    (peelGearLocalDyn bGear bCat mOut mMid sUb top hbGear1 htop_lt v refl pA pB).count .TOFF =
      0 := by
  dsimp only [peelGearLocalDyn]
  split_ifs
  · exact patFlipTwoStepLocalDyn_count_toff _ _ _ _ _ _ _ _ _ hA hB
  · exact singleSignedLocalDyn_count_toff _ _ _ _ _ _ _ _ _ hA

theorem peelGearLocalDyn_count_t_le {Var : Type} (bGear bCat mOut mMid sUb top tA tB : ℕ)
    (hbGear1 : 1 ≤ bGear) (htop_lt : top < 2 ^ bGear) (v : Var) {aRem mRem : ℕ}
    (refl : WalkReflRegs bCat mOut mMid aRem mRem)
    {pA pB : DynamicCircuit Var (totalQubits bGear bCat mOut mMid 0 aRem mRem sUb)}
    (hA : pA.count .T ≤ tA) (hB : pB.count .T ≤ tB) :
    (peelGearLocalDyn bGear bCat mOut mMid sUb top hbGear1 htop_lt v refl pA pB).count .T ≤
      tA + tB + 16 * (aRem - 1) + 8 * (bGear - 1) := by
  dsimp only [peelGearLocalDyn]
  split_ifs
  · rw [patFlipTwoStepLocalDyn_count_t]
    omega
  · rw [singleSignedLocalDyn_count_t]
    omega

/-- `3`-bit `G1` local circuit (`20 * (aRem - 1) + 16` `T` gates) for `24,576`-top `SevenGear`. -/
def oddPairG1LocalDyn {Var : Type} (bCat mOut mMid sUb : ℕ) (v : Var) {aRem mRem : ℕ}
    (refl : WalkReflRegs bCat mOut mMid aRem mRem)
    (pA pB : DynamicCircuit Var (totalQubits 3 bCat mOut mMid 0 aRem mRem sUb)) :
    DynamicCircuit Var (totalQubits 3 bCat mOut mMid 0 aRem mRem sUb) :=
  .seq (patCtrlR0Dyn 3 bCat mOut mMid sUb (by decide) v refl false ⟨4, by decide⟩)
    (.seq (bitCtrlR0Dyn 3 bCat mOut mMid 0 sUb v refl false ⟨0, by decide⟩)
      (.seq pA
        (.seq (bitCtrlR0Dyn 3 bCat mOut mMid 0 sUb v refl true ⟨2, by decide⟩)
          (.seq (bitCtrlR0Dyn 3 bCat mOut mMid 0 sUb v refl false ⟨0, by decide⟩)
            (.seq pB
              (patCtrlR0Dyn 3 bCat mOut mMid sUb (by decide) v refl false ⟨5, by decide⟩))))))

/-- `3`-bit `G1` fiber realized by `oddPairG1LocalDyn`. -/
noncomputable def oddPairG1Fiber {d : ℕ} (uA uB R₀ : Unitary d) (x : Fin (2 ^ 3)) : Unitary d :=
  (if decide (x = ⟨5, by decide⟩) then R₀ else 1) *
    (uB * ((if x.val.testBit 0 == false then R₀ else 1) *
      ((if x.val.testBit 2 == true then R₀ else 1) *
        (uA * ((if x.val.testBit 0 == false then R₀ else 1) *
          (if decide (x = ⟨4, by decide⟩) then R₀ else 1))))))

theorem oddPairG1LocalDyn_count_toff {Var : Type} (bCat mOut mMid sUb : ℕ) (v : Var)
    {aRem mRem : ℕ} (refl : WalkReflRegs bCat mOut mMid aRem mRem)
    {pA pB : DynamicCircuit Var (totalQubits 3 bCat mOut mMid 0 aRem mRem sUb)}
    (hA : pA.count .TOFF = 0) (hB : pB.count .TOFF = 0) :
    (oddPairG1LocalDyn bCat mOut mMid sUb v refl pA pB).count .TOFF = 0 := by
  simp [oddPairG1LocalDyn, hA, hB]

theorem oddPairG1LocalDyn_count_t {Var : Type} (bCat mOut mMid sUb : ℕ) (v : Var)
    {aRem mRem : ℕ} (refl : WalkReflRegs bCat mOut mMid aRem mRem)
    (pA pB : DynamicCircuit Var (totalQubits 3 bCat mOut mMid 0 aRem mRem sUb)) :
    (oddPairG1LocalDyn bCat mOut mMid sUb v refl pA pB).count .T =
      pA.count .T + pB.count .T + 20 * (aRem - 1) + 16 := by
  simp only [oddPairG1LocalDyn, DynamicCircuit.count, bitCtrlR0Dyn_count_t,
    patCtrlR0Dyn_count_t]
  omega

theorem oddPairG1LocalDyn_cleanRealizes {Var : Type} [Fintype Var] [DecidableEq Var]
    (bCat mOut mMid sUb : ℕ) (v : Var) {aRem mRem kZero : ℕ}
    {refl : WalkReflRegs bCat mOut mMid aRem mRem} {rAncZero : QRegister kZero (mOut + mMid)}
    (hCov : WalkReflCovers 3 bCat mOut mMid 0 sUb refl rAncZero)
    {uA uB : Unitary (2 ^ walkCatWidth bCat mOut mMid)}
    {pA pB : DynamicCircuit Var (totalQubits 3 bCat mOut mMid 0 aRem mRem sUb)}
    (hA : Solution.XMeasCircuit.CleanRealizes v (rWalkCatLoc 3 bCat mOut mMid 0 aRem mRem sUb)
      (rFullZeroLoc 3 bCat mOut mMid 0 aRem mRem sUb rAncZero) uA pA)
    (hB : Solution.XMeasCircuit.CleanRealizes v (rWalkCatLoc 3 bCat mOut mMid 0 aRem mRem sUb)
      (rFullZeroLoc 3 bCat mOut mMid 0 aRem mRem sUb rAncZero) uB pB) :
    let R₀ := QubitisedWalk.reflInUnitary (inAllWalkCat bCat mOut mMid)
    Solution.XMeasCircuit.CleanRealizes v
      ((rQPELoc 3 bCat mOut mMid 0 aRem mRem sUb).concat
        (rWalkCatLoc 3 bCat mOut mMid 0 aRem mRem sUb)
        (rQPELoc_disjoint_rWalkCatLoc 3 bCat mOut mMid 0 aRem mRem sUb))
      (rFullZeroLoc 3 bCat mOut mMid 0 aRem mRem sUb rAncZero)
      (QubitisedWalk.qpeMuxUnitary (oddPairG1Fiber uA uB R₀))
      (oddPairG1LocalDyn bCat mOut mMid sUb v refl pA pB) := by
  intro R₀
  have hsA := cleanRealizes_walkOnCombined2
    (rQPELoc_disjoint_rWalkCatLoc 3 bCat mOut mMid 0 aRem mRem sUb) hA
  have hsB := cleanRealizes_walkOnCombined2
    (rQPELoc_disjoint_rWalkCatLoc 3 bCat mOut mMid 0 aRem mRem sUb) hB
  refine cleanRealizes_of_eq
    ((patCtrlR0Dyn_cleanRealizes 3 bCat mOut mMid sUb (by decide) v hCov false
      ⟨4, by decide⟩).seq
      ((bitCtrlR0Dyn_cleanRealizes 3 bCat mOut mMid 0 sUb v hCov false ⟨0, by decide⟩).seq
        (hsA.seq ((bitCtrlR0Dyn_cleanRealizes 3 bCat mOut mMid 0 sUb v hCov true
          ⟨2, by decide⟩).seq
          ((bitCtrlR0Dyn_cleanRealizes 3 bCat mOut mMid 0 sUb v hCov false
            ⟨0, by decide⟩).seq
            (hsB.seq (patCtrlR0Dyn_cleanRealizes 3 bCat mOut mMid sUb (by decide) v hCov false
              ⟨5, by decide⟩))))))) ?_
  simp only [← QubitisedWalk.qpeMuxUnitary_mul, Bool.false_eq_true, ↓reduceIte]
  exact congrArg QubitisedWalk.qpeMuxUnitary (funext fun x ↦ by
    dsimp only [R₀, oddPairG1Fiber, Fin.val_zero]
    simp only [mul_assoc])

theorem invCatRelOddPairG1Fiber {mOut mMid : ℕ} {P_inv : FGInvPred mOut mMid}
    {cat : Fin (2 ^ 11) → ℂ} {R₁c uA uB : FGWalkU mOut mMid}
    {R₁ RA RB : Unitary (2 ^ walkWidth mOut mMid)} {δA δB : ℝ}
    (hRelR₁ : InvCatRel P_inv cat R₁c R₁ 0)
    (hRelA : InvCatRel P_inv cat uA RA δA) (hRelB : InvCatRel P_inv cat uB RB δB)
    (x : Fin (2 ^ 3)) :
    InvCatRel P_inv cat (oddPairG1Fiber uA uB R₁c x) (oddPairG1Fiber RA RB R₁ x) (δA + δB) :=
  by
  have hm := invCatRel_mul (invCatRel_cond_refl hRelR₁ (decide (x = ⟨5, by decide⟩)))
    (invCatRel_mul hRelB (invCatRel_mul (invCatRel_cond_refl hRelR₁ (x.val.testBit 0 == false))
      (invCatRel_mul (invCatRel_cond_refl hRelR₁ (x.val.testBit 2 == true))
        (invCatRel_mul hRelA (invCatRel_mul (invCatRel_cond_refl hRelR₁ (x.val.testBit 0 == false))
          (invCatRel_cond_refl hRelR₁ (decide (x = ⟨4, by decide⟩))))))))
  refine ⟨hm.1, fun v hv ↦ (hm.2 v hv).trans_eq ?_⟩
  ring

/-- `4`-bit `G2` local circuit (`24 * (aRem - 1) + 48` `T` gates) for `24,576`-top `SevenGear`. -/
def oddPairG2LocalDyn {Var : Type} (bCat mOut mMid sUb : ℕ) (v : Var) {aRem mRem : ℕ}
    (refl : WalkReflRegs bCat mOut mMid aRem mRem)
    (pA pB : DynamicCircuit Var (totalQubits 4 bCat mOut mMid 0 aRem mRem sUb)) :
    DynamicCircuit Var (totalQubits 4 bCat mOut mMid 0 aRem mRem sUb) :=
  .seq (patCtrlR0Dyn 4 bCat mOut mMid sUb (by decide) v refl false ⟨10, by decide⟩)
    (.seq (bitCtrlR0Dyn 4 bCat mOut mMid 0 sUb v refl false ⟨0, by decide⟩)
      (.seq pA
        (.seq (patCtrlR0Dyn 4 bCat mOut mMid sUb (by decide) v refl false ⟨11, by decide⟩)
          (.seq (patCtrlR0Dyn 4 bCat mOut mMid sUb (by decide) v refl false ⟨10, by decide⟩)
            (.seq (bitCtrlR0Dyn 4 bCat mOut mMid 0 sUb v refl false ⟨0, by decide⟩)
              (.seq pB
                (patCtrlR0Dyn 4 bCat mOut mMid sUb (by decide) v refl false
                  ⟨11, by decide⟩)))))))

/-- `4`-bit `G2` fiber realized by `oddPairG2LocalDyn`. -/
noncomputable def oddPairG2Fiber {d : ℕ} (uA uB R₀ : Unitary d) (x : Fin (2 ^ 4)) : Unitary d :=
  (if decide (x = ⟨11, by decide⟩) then R₀ else 1) *
    (uB * ((if x.val.testBit 0 == false then R₀ else 1) *
      ((if decide (x = ⟨10, by decide⟩) then R₀ else 1) *
        ((if decide (x = ⟨11, by decide⟩) then R₀ else 1) *
          (uA * ((if x.val.testBit 0 == false then R₀ else 1) *
            (if decide (x = ⟨10, by decide⟩) then R₀ else 1)))))))

theorem oddPairG2LocalDyn_count_toff {Var : Type} (bCat mOut mMid sUb : ℕ) (v : Var)
    {aRem mRem : ℕ} (refl : WalkReflRegs bCat mOut mMid aRem mRem)
    {pA pB : DynamicCircuit Var (totalQubits 4 bCat mOut mMid 0 aRem mRem sUb)}
    (hA : pA.count .TOFF = 0) (hB : pB.count .TOFF = 0) :
    (oddPairG2LocalDyn bCat mOut mMid sUb v refl pA pB).count .TOFF = 0 := by
  simp [oddPairG2LocalDyn, hA, hB]

theorem oddPairG2LocalDyn_count_t {Var : Type} (bCat mOut mMid sUb : ℕ) (v : Var)
    {aRem mRem : ℕ} (refl : WalkReflRegs bCat mOut mMid aRem mRem)
    (pA pB : DynamicCircuit Var (totalQubits 4 bCat mOut mMid 0 aRem mRem sUb)) :
    (oddPairG2LocalDyn bCat mOut mMid sUb v refl pA pB).count .T =
      pA.count .T + pB.count .T + 24 * (aRem - 1) + 48 := by
  simp only [oddPairG2LocalDyn, DynamicCircuit.count, bitCtrlR0Dyn_count_t,
    patCtrlR0Dyn_count_t]
  omega

theorem oddPairG2LocalDyn_cleanRealizes {Var : Type} [Fintype Var] [DecidableEq Var]
    (bCat mOut mMid sUb : ℕ) (v : Var) {aRem mRem kZero : ℕ}
    {refl : WalkReflRegs bCat mOut mMid aRem mRem} {rAncZero : QRegister kZero (mOut + mMid)}
    (hCov : WalkReflCovers 4 bCat mOut mMid 0 sUb refl rAncZero)
    {uA uB : Unitary (2 ^ walkCatWidth bCat mOut mMid)}
    {pA pB : DynamicCircuit Var (totalQubits 4 bCat mOut mMid 0 aRem mRem sUb)}
    (hA : Solution.XMeasCircuit.CleanRealizes v (rWalkCatLoc 4 bCat mOut mMid 0 aRem mRem sUb)
      (rFullZeroLoc 4 bCat mOut mMid 0 aRem mRem sUb rAncZero) uA pA)
    (hB : Solution.XMeasCircuit.CleanRealizes v (rWalkCatLoc 4 bCat mOut mMid 0 aRem mRem sUb)
      (rFullZeroLoc 4 bCat mOut mMid 0 aRem mRem sUb rAncZero) uB pB) :
    let R₀ := QubitisedWalk.reflInUnitary (inAllWalkCat bCat mOut mMid)
    Solution.XMeasCircuit.CleanRealizes v
      ((rQPELoc 4 bCat mOut mMid 0 aRem mRem sUb).concat
        (rWalkCatLoc 4 bCat mOut mMid 0 aRem mRem sUb)
        (rQPELoc_disjoint_rWalkCatLoc 4 bCat mOut mMid 0 aRem mRem sUb))
      (rFullZeroLoc 4 bCat mOut mMid 0 aRem mRem sUb rAncZero)
      (QubitisedWalk.qpeMuxUnitary (oddPairG2Fiber uA uB R₀))
      (oddPairG2LocalDyn bCat mOut mMid sUb v refl pA pB) := by
  intro R₀
  have hsA := cleanRealizes_walkOnCombined2
    (rQPELoc_disjoint_rWalkCatLoc 4 bCat mOut mMid 0 aRem mRem sUb) hA
  have hsB := cleanRealizes_walkOnCombined2
    (rQPELoc_disjoint_rWalkCatLoc 4 bCat mOut mMid 0 aRem mRem sUb) hB
  refine cleanRealizes_of_eq
    ((patCtrlR0Dyn_cleanRealizes 4 bCat mOut mMid sUb (by decide) v hCov false
      ⟨10, by decide⟩).seq
      ((bitCtrlR0Dyn_cleanRealizes 4 bCat mOut mMid 0 sUb v hCov false ⟨0, by decide⟩).seq
        (hsA.seq ((patCtrlR0Dyn_cleanRealizes 4 bCat mOut mMid sUb (by decide) v hCov false
          ⟨11, by decide⟩).seq
          ((patCtrlR0Dyn_cleanRealizes 4 bCat mOut mMid sUb (by decide) v hCov false
            ⟨10, by decide⟩).seq
            ((bitCtrlR0Dyn_cleanRealizes 4 bCat mOut mMid 0 sUb v hCov false
              ⟨0, by decide⟩).seq
              (hsB.seq (patCtrlR0Dyn_cleanRealizes 4 bCat mOut mMid sUb (by decide) v hCov false
                ⟨11, by decide⟩)))))))) ?_
  simp only [← QubitisedWalk.qpeMuxUnitary_mul, Bool.false_eq_true, ↓reduceIte]
  exact congrArg QubitisedWalk.qpeMuxUnitary (funext fun x ↦ by
    dsimp only [R₀, oddPairG2Fiber, Fin.val_zero]
    simp only [mul_assoc])

theorem invCatRelOddPairG2Fiber {mOut mMid : ℕ} {P_inv : FGInvPred mOut mMid}
    {cat : Fin (2 ^ 11) → ℂ} {R₁c uA uB : FGWalkU mOut mMid}
    {R₁ RA RB : Unitary (2 ^ walkWidth mOut mMid)} {δA δB : ℝ}
    (hRelR₁ : InvCatRel P_inv cat R₁c R₁ 0)
    (hRelA : InvCatRel P_inv cat uA RA δA) (hRelB : InvCatRel P_inv cat uB RB δB)
    (x : Fin (2 ^ 4)) :
    InvCatRel P_inv cat (oddPairG2Fiber uA uB R₁c x) (oddPairG2Fiber RA RB R₁ x) (δA + δB) :=
  by
  have hm := invCatRel_mul (invCatRel_cond_refl hRelR₁ (decide (x = ⟨11, by decide⟩)))
    (invCatRel_mul hRelB (invCatRel_mul (invCatRel_cond_refl hRelR₁ (x.val.testBit 0 == false))
      (invCatRel_mul (invCatRel_cond_refl hRelR₁ (decide (x = ⟨10, by decide⟩)))
        (invCatRel_mul (invCatRel_cond_refl hRelR₁ (decide (x = ⟨11, by decide⟩)))
          (invCatRel_mul hRelA
            (invCatRel_mul (invCatRel_cond_refl hRelR₁ (x.val.testBit 0 == false))
              (invCatRel_cond_refl hRelR₁ (decide (x = ⟨10, by decide⟩)))))))))
  refine ⟨hm.1, fun v hv ↦ (hm.2 v hv).trans_eq ?_⟩
  ring

end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.SevenGearBondDefer

end
