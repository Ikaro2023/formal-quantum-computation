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

public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.NoNegSOSWalkAux

/-!
# `(wOuter, wInner2)`-Polymorphic `NoNeg + D_neg` `SiZero` SOS & `K ≥ 1` Walk

Proves wire-preservation and kernel invariance (`PostOutInv`, `kernel_step`),
`walkRefl2InvErrLe_noNegDNeg_gen` (`ideal` and `bal184`), `walkSuperRefl2InvErrLe_noNegDNeg_*`,
and QHL turnaround `D_neg` sandwich lemmas (`cleanTurnaroundWp_dNeg_sandwich`).
-/

@[expose] public section

namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.NoNegDNegSOSAndSuperWalk
open QuantumComputation.Specs QuantumComputation.Specs.P450
open Operator QProg Matrix Circuit Real HermitianMat CoherentAlias Solution.CleanDyn AliasPrep
open SelectSwapQROM QuantumComputation.Specs Solution QuantumComputation.Specs.P450 Solution
open Solution.BlockEncodingCore Solution.BlockEncodingCircuit
open Solution.TopIntegrationBridge Solution.Phase2MidSandwich Solution.MidReflCtxRetain
open Solution.Cat11CompactPhase2Bridge
open Solution.ReordOuter13Bridge Solution.ZeroRcHotPrepMid21Fast Solution.MobiusOptSubcube163Walk
open Solution.CompactTuned162StepZeroCmp20 Solution.Pi145SOSPermBridge Solution.LowBitPi145Select
open Solution.CompactOuter9Bound50Core Solution.CompactOuter9Bound50Select Solution.OneHotSimulates
open Solution.QuantizedFactoredMag30 Solution.BellSingletCSwap58 Solution.BellPersistCore
open Solution.CompactStepFast176Select (pack16)
open Solution.BellPersistSuperWalk Solution.BellRouter57 Solution.BellRouter57Pure
open Solution.NoNegSelect57Pure Solution.CompactCore145Bundle Solution.Select57Slices
open Solution.BellSelectNoNegPair Solution.BellSuperNoNegWalk Solution.TwoGearSuperPhase5
open Solution.ThreeGearBellSuper Solution.TwoGearQPEPhase5 Solution.Phase2FlexBridge
open scoped Matrix BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator Circuit.Notation
local instance (priority := 1000000) instNeZeroTwoPowNoNegSuper (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩
theorem asymHalfStep_eq_symHalfStep_of_lt126 {wOuter wInner2 : ℕ}
    {prepMid : Fin (2 ^ 7) → Unitary (2 ^ mMidUB wInner2)}
    (hB30 : ∀ (rc : Fin 126) (m : Fin (2 ^ mMidUB wInner2)),
      30 ≤ ((rBLoc wInner2).extractIndex m).val → (prepMid ⟨rc.val, by omega⟩).1 m 0 = 0)
    {dBit : Fin (2 ^ 8) → Fin (2 ^ 5) → Bool} (hd : IsValidDNegBit dBit)
    (ψ : Fin (2 ^ (2 * 58)) → ℂ) (o' : Fin (2 ^ mOutUB wOuter))
    (hxo' : ((rXoLoc wOuter).extractIndex o').val < 126) :
    let M_s := prepMidDirectXo7MuxUnitary wOuter wInner2 (fun rc ↦ prepMid (pi128Equiv rc))
    let M_a := asymMidMux wOuter wInner2 prepMid
    let U_I := M_s⁻¹ * idealPi145SelectPure wOuter wInner2 * M_s
    let sF := select57NoNegFwdPureUnitary wOuter wInner2
    let sB := select57NoNegBwdPureUnitary wOuter wInner2
    let F_mid := M_a⁻¹ * (dNegUB wOuter wInner2 dBit * sF) * M_a
    let B_mid := M_a⁻¹ * (sB * dNegUB wOuter wInner2 dBit) * M_a
    (F_mid.1 *ᵥ embedKet ψ o' 0 = U_I.1 *ᵥ embedKet ψ o' 0) ∧
      (B_mid.1 *ᵥ embedKet ψ o' 0 = U_I.1 *ᵥ embedKet ψ o' 0) ∧
      (B_mid.1 *ᵥ (U_I.1 *ᵥ embedKet ψ o' 0) = embedKet ψ o' 0) ∧
      (F_mid.1 *ᵥ (U_I.1 *ᵥ embedKet ψ o' 0) = embedKet ψ o' 0) := by
  intro M_s M_a U_I sF sB F_mid B_mid
  have hMsMulInv : M_s.1 * (M_s⁻¹).1 = 1 := congrArg Subtype.val (mul_inv_cancel M_s)
  have hInvMsMul : (M_s⁻¹).1 * M_s.1 = 1 := congrArg Subtype.val (inv_mul_cancel M_s)
  have hrc126 : ((rXo7Loc wOuter).extractIndex o').val < 126 := by
    rwa [extract_rXo7Loc_of_lt128 o' (by omega)]
  have hpi126 := pi128Equiv_lt126_of_lt126 _ hrc126
  have hb30 (m' : Fin (2 ^ mMidUB wInner2))
      (hnz : (prepMid (pi128Equiv ((rXo7Loc wOuter).extractIndex o'))).1 m' 0 ≠ 0) :
      ((rBLoc wInner2).extractIndex m').val < 30 :=
    by_contra fun hge ↦ hnz (hB30 ⟨_, hpi126⟩ m' (by omega))
  have hHalf (S_mid : Unitary (2 ^ nUB wOuter wInner2))
      (hSm : ∀ (ξ : Fin (2 ^ (2 * 58)) → ℂ) (m' : Fin (2 ^ mMidUB wInner2)),
        ((rBLoc wInner2).extractIndex m').val < 30 →
        S_mid.1 *ᵥ embedKet ξ o' m' = (idealPi145SelectPure wOuter wInner2).1 *ᵥ embedKet ξ o' m') :
      ((M_a⁻¹ * S_mid * M_a).1 *ᵥ embedKet ψ o' 0 = U_I.1 *ᵥ embedKet ψ o' 0) ∧
        ((M_a⁻¹ * S_mid * M_a).1 *ᵥ (U_I.1 *ᵥ embedKet ψ o' 0) = embedKet ψ o' 0) := by
    have hMa (ξ : Fin (2 ^ (2 * 58)) → ℂ) (m : Fin (2 ^ mMidUB wInner2)) :
        M_a.1 *ᵥ embedKet ξ o' m = M_s.1 *ᵥ embedKet ξ o' m := by
      rw [asymMidMux_mulVec_embedKet, asymMidBranch_of_lt126 prepMid o' hxo',
        embedMatrix_rMidUB_mulVec_embedKet, prepMidDirectXo7Mux_mulVec_embedKet_loc]
    have hMaInv (ξ : Fin (2 ^ (2 * 58)) → ℂ) (m : Fin (2 ^ mMidUB wInner2)) :
        (M_a⁻¹).1 *ᵥ embedKet ξ o' m = (M_s⁻¹).1 *ᵥ embedKet ξ o' m := by
      rw [asymMidMux_inv_mulVec_embedKet, asymMidBranch_of_lt126 prepMid o' hxo',
        embedMatrix_rMidUB_mulVec_embedKet,
        show M_s⁻¹ = prepMidDirectXo7MuxUnitary wOuter wInner2 (fun rc ↦
          (prepMid (pi128Equiv rc))⁻¹)
          from muxUnitary_inv _ _ _ _, prepMidDirectXo7Mux_mulVec_embedKet_loc]
    have h1 : (M_a⁻¹ * S_mid * M_a).1 *ᵥ embedKet ψ o' 0 = U_I.1 *ᵥ embedKet ψ o' 0 := by
      simp only [U_I, Submonoid.coe_mul, ← Matrix.mulVec_mulVec]
      rw [hMa, prepMidDirectXo7Mux_mulVec_embedKet_loc, Matrix.mulVec_sum, Matrix.mulVec_sum,
        Matrix.mulVec_sum, Matrix.mulVec_sum]
      refine Finset.sum_congr rfl fun m' _ ↦ ?_
      by_cases hnz : (prepMid (pi128Equiv ((rXo7Loc wOuter).extractIndex o'))).1 m' 0 = 0
      · simp only [hnz, zero_smul, Matrix.mulVec_zero]
      · rw [Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.mulVec_smul,
          hSm ψ m' (hb30 m' hnz), idealPi145SelectPure_mulVec_embedKet, hMaInv]
    refine ⟨h1, ?_⟩
    have hMsEq (f : Fin (2 ^ mMidUB wInner2) → Fin (2 ^ (2 * 58)) → ℂ) :
        M_a.1 *ᵥ ((M_s⁻¹).1 *ᵥ ∑ m', embedKet (f m') o' m') = ∑ m', embedKet (f m') o' m' := by
      rw [Matrix.mulVec_sum, Matrix.mulVec_sum]
      refine Finset.sum_congr rfl fun m' _ ↦ ?_
      have hInvMux := prepMidDirectXo7Mux_mulVec_embedKet_loc (wOuter := wOuter) (wInner2 :=
        wInner2)
        (fun rc ↦ (prepMid (pi128Equiv rc))⁻¹) (f m') o' m'
      have hInvEq : M_s⁻¹ = prepMidDirectXo7MuxUnitary wOuter wInner2
          (fun rc ↦ (prepMid (pi128Equiv rc))⁻¹) := muxUnitary_inv _ _ _ _
      rw [hInvEq, hInvMux, Matrix.mulVec_sum]
      have hs (x : Fin (2 ^ mMidUB wInner2)) :
          M_a.1 *ᵥ ((((prepMid (pi128Equiv ((rXo7Loc wOuter).extractIndex o')))⁻¹).1 x m') •
            embedKet (f m') o' x) =
          M_s.1 *ᵥ ((((prepMid (pi128Equiv ((rXo7Loc wOuter).extractIndex o')))⁻¹).1 x m') •
            embedKet (f m') o' x) := by rw [Matrix.mulVec_smul, hMa, Matrix.mulVec_smul]
      rw [Finset.sum_congr rfl fun x _ ↦ hs x, ← Matrix.mulVec_sum, ← hInvMux, ← hInvEq,
        Matrix.mulVec_mulVec, hMsMulInv, Matrix.one_mulVec]
    have hMaUI : M_a.1 *ᵥ (U_I.1 *ᵥ embedKet ψ o' 0) =
        (idealPi145SelectPure wOuter wInner2).1 *ᵥ (M_s.1 *ᵥ embedKet ψ o' 0) := by
      simp only [U_I, Submonoid.coe_mul, ← Matrix.mulVec_mulVec]
      have hSum : (idealPi145SelectPure wOuter wInner2).1 *ᵥ (M_s.1 *ᵥ embedKet ψ o' 0) =
          ∑ m', embedKet (((prepMid (pi128Equiv ((rXo7Loc wOuter).extractIndex o'))).1 m' 0) •
            ((idealPi145Branch wOuter wInner2 o' m').1 *ᵥ ψ)) o' m' := by
        rw [prepMidDirectXo7Mux_mulVec_embedKet_loc, Matrix.mulVec_sum]
        exact Finset.sum_congr rfl fun m' _ ↦ by
          rw [Matrix.mulVec_smul, idealPi145SelectPure_mulVec_embedKet, embedKet_smul]
      rw [hSum, hMsEq]
    simp only [Submonoid.coe_mul, ← Matrix.mulVec_mulVec]
    have hFwdMux := prepMidDirectXo7Mux_mulVec_embedKet_loc (wOuter := wOuter) (wInner2 := wInner2)
      (fun rc ↦ prepMid (pi128Equiv rc)) ψ o' 0
    rw [hMaUI, hFwdMux, Matrix.mulVec_sum, Matrix.mulVec_sum, Matrix.mulVec_sum]
    have hterm (m' : Fin (2 ^ mMidUB wInner2)) :
        (M_a⁻¹).1 *ᵥ (S_mid.1 *ᵥ ((idealPi145SelectPure wOuter wInner2).1 *ᵥ
          (((prepMid (pi128Equiv ((rXo7Loc wOuter).extractIndex o'))).1 m' 0) •
            embedKet ψ o' m'))) =
        (M_s⁻¹).1 *ᵥ
          (((prepMid (pi128Equiv ((rXo7Loc wOuter).extractIndex o'))).1 m' 0) •
              embedKet ψ o' m') := by
      by_cases hnz : (prepMid (pi128Equiv ((rXo7Loc wOuter).extractIndex o'))).1 m' 0 = 0
      · simp only [hnz, zero_smul, Matrix.mulVec_zero]
      · rw [Matrix.mulVec_smul, idealPi145SelectPure_mulVec_embedKet, Matrix.mulVec_smul,
          hSm _ m' (hb30 m' hnz), idealPi145SelectPure_mulVec_embedKet, Matrix.mulVec_mulVec,
          ← Submonoid.coe_mul, idealPi145Branch_mul_self, Submonoid.coe_one, Matrix.one_mulVec,
          Matrix.mulVec_smul, hMaInv, ← Matrix.mulVec_smul]
    rw [Finset.sum_congr rfl fun m' _ ↦ hterm m', ← Matrix.mulVec_sum, ← hFwdMux,
      Matrix.mulVec_mulVec, hInvMsMul, Matrix.one_mulVec]
  obtain ⟨hF1, hF2⟩ := hHalf (dNegUB wOuter wInner2 dBit * sF) fun ξ m' hb ↦ by
    rw [(dNegUB_mulSelect57NoNegPureUnitary_twoBody hd false ξ o' m' hxo' hb).1,
      selectOnLt184IdealPi145SelectPure wOuter wInner2 ξ o' m' (by omega)]
  obtain ⟨hB1, hB2⟩ := hHalf (sB * dNegUB wOuter wInner2 dBit) fun ξ m' hb ↦ by
    rw [(dNegUB_mulSelect57NoNegPureUnitary_twoBody hd true ξ o' m' hxo' hb).2,
      selectOnLt184IdealPi145SelectPure wOuter wInner2 ξ o' m' (by omega)]
  exact ⟨hF1, hB1, hB2, hF2⟩
theorem preservesWiresSpinCancelUBMux {N wOuter wInner2 : ℕ} (rUB :
    QRegister (nUB wOuter wInner2) N)
    {S : Finset (Wire N)} (hNot : rUB ((rMidUB wOuter wInner2) (rSigInLoc wInner2 0)) ∉ S) :
    AliasPrep.PreservesWires (rUB.embedUnitary (spinCancelUBMux wOuter wInner2)).1 S := by
  let rC := rUB.compose ((rOutUB wOuter wInner2).compose (rXoLoc wOuter))
  let rT := rUB.compose ((rMidUB wOuter wInner2).compose (rSigInLoc wInner2))
  have hDisjT : Disjoint rT.image S := Finset.disjoint_left.mpr fun w hw hS ↦ by
    obtain ⟨i, rfl⟩ := (QRegister.mem_image rT w).mp hw
    fin_cases i
    exact hNot hS
  rw [spinCancelUBMux, embedUnitary_muxUnitary]
  dsimp only [muxUnitary]
  exact preservesWires_sum Finset.univ _ fun c _ ↦ AliasPrep.preservesWires_mul
    (preservesWires_basisOutcomeProjector rC c S)
    (AliasPrep.preservesWires_embedMatrix_of_disjoint rT _ S hDisjT)
theorem spinCancelUBMux_comm_prepMidDirectXo7Mux {wOuter wInner2 : ℕ}
    {prepMid : Fin (2 ^ 7) → Unitary (2 ^ mMidUB wInner2)} (hSpin : PrepMidSpinFactored prepMid) :
    spinCancelUBMux wOuter wInner2 *
      prepMidDirectXo7MuxUnitary wOuter wInner2 (fun rc ↦ prepMid (pi128Equiv rc)) =
      prepMidDirectXo7MuxUnitary wOuter wInner2 (fun rc ↦ prepMid (pi128Equiv rc)) *
        spinCancelUBMux wOuter wInner2 := by
  obtain ⟨core, hcore⟩ := hSpin
  let rCore : QRegister (5 + wInner2) (mMidUB wInner2) :=
    QRegister.block 0 (5 + wInner2) (by
      dsimp [mMidUB]
      omega)
  have hDisj : rCore.DisjointWires (rSigInLoc wInner2) := QRegister.disjoint_iff.mpr fun i _ h ↦ by
    have hv := congrArg Fin.val h
    have := i.isLt
    dsimp only [rCore, rSigInLoc, QRegister.block_apply_val] at hv
    omega
  have hBrComm (b : Bool) (rc : Fin (2 ^ 7)) :
      (if b then (rSigInLoc wInner2).embedUnitary (Circuit.H 0).eval else 1) * prepMid rc =
        prepMid rc * (if b then (rSigInLoc wInner2).embedUnitary (Circuit.H 0).eval else 1) := by
    cases b
    · rw [ite_eq_right Bool.false_ne_true, one_mul, mul_one]
    · rw [ite_eq_left rfl, hcore, mul_assoc]
      exact congrArg ((rSigInLoc wInner2).embedUnitary (Circuit.H 0).eval * ·) (Subtype.ext
        (rCore.embedMatrix_comm_of_disjoint (rSigInLoc wInner2) hDisj (core rc).1 _).symm)
  refine Subtype.ext <| matrix_eq_of_mulVec_single fun g ↦ ?_
  rw [single_eq_embedKet g]
  set ψ := (Pi.single ((rSysUB wOuter wInner2).extractIndex g) (1 : ℂ) : Fin (2 ^ (2 * 58)) → ℂ)
  set o' := (rOutUB wOuter wInner2).extractIndex g
  set m := (rMidUB wOuter wInner2).extractIndex g
  let S_c : Unitary (2 ^ mMidUB wInner2) :=
    if is1BBool ((rXoLoc wOuter).extractIndex o') then
      (rSigInLoc wInner2).embedUnitary (Circuit.H 0).eval else 1
  have hRhs : (prepMidDirectXo7MuxUnitary wOuter wInner2 (fun rc ↦ prepMid (pi128Equiv rc)) *
      spinCancelUBMux wOuter wInner2).1 *ᵥ embedKet ψ o' m =
      (rMidUB wOuter wInner2).embedMatrix (asymMidBranch prepMid o').1 *ᵥ embedKet ψ o' m := by
    rw [Submonoid.coe_mul, ← Matrix.mulVec_mulVec, spinCancelUBMux_mulVec_embedKet,
      embedMatrix_rMidUB_mulVec_embedKet, Matrix.mulVec_sum]
    have hs (x : Fin (2 ^ mMidUB wInner2)) :
        (prepMidDirectXo7MuxUnitary wOuter wInner2 fun rc ↦ prepMid (pi128Equiv rc)).1 *ᵥ
          (S_c.1 x m • embedKet ψ o' x) =
        S_c.1 x m • ((rMidUB wOuter wInner2).embedMatrix
          (prepMid (pi128Equiv ((rXo7Loc wOuter).extractIndex o'))).1 *ᵥ embedKet ψ o' x) := by
      rw [Matrix.mulVec_smul, prepMidDirectXo7Mux_mulVec_embedKet_loc,
        embedMatrix_rMidUB_mulVec_embedKet]
    rw [Finset.sum_congr rfl fun x _ ↦ hs x, sum_smul_embedMatrix_rMidUB_embedKet,
      asymMidBranch, ← Submonoid.coe_mul, hBrComm]
  exact (asymMidMux_mulVec_embedKet prepMid ψ o' m).trans hRhs.symm
theorem preservesWiresAsymMidSandwich {N wOuter wInner2 : ℕ}
    (rMain : QRegister (nUB wOuter wInner2 + 11) N) {S : Finset (Wire N)}
    {prepMid : Fin (2 ^ 7) → Unitary (2 ^ mMidUB wInner2)} (hSpin : PrepMidSpinFactored prepMid)
    (hNot :
      (rMain.compose (rUBInCat wOuter wInner2 11)) ((rMidUB wOuter wInner2)
      (rSigInLoc wInner2 0)) ∉ S)
    {V : Unitary (2 ^ (nUB wOuter wInner2 + 11))}
    (hSym : AliasPrep.PreservesWires (rMain.embedUnitary
      ((rUBInCat wOuter wInner2 11).embedUnitary
          (prepMidDirectXo7MuxUnitary wOuter wInner2 (fun rc ↦ prepMid (pi128Equiv rc)))⁻¹ * V *
        (rUBInCat wOuter wInner2 11).embedUnitary
          (prepMidDirectXo7MuxUnitary wOuter wInner2 (fun rc ↦ prepMid (pi128Equiv rc))))).1 S) :
    AliasPrep.PreservesWires (rMain.embedUnitary
      ((rUBInCat wOuter wInner2 11).embedUnitary (asymMidMux wOuter wInner2 prepMid)⁻¹ * V *
        (rUBInCat wOuter wInner2 11).embedUnitary (asymMidMux wOuter wInner2 prepMid))).1 S := by
  let C_ub := spinCancelUBMux wOuter wInner2
  let M_s := prepMidDirectXo7MuxUnitary wOuter wInner2 (fun rc ↦ prepMid (pi128Equiv rc))
  have hCInv : C_ub⁻¹ = C_ub := spinCancelUBMux_inv wOuter wInner2
  have hEq : (rUBInCat wOuter wInner2 11).embedUnitary (asymMidMux wOuter wInner2 prepMid)⁻¹ * V *
      (rUBInCat wOuter wInner2 11).embedUnitary (asymMidMux wOuter wInner2 prepMid) =
      (rUBInCat wOuter wInner2 11).embedUnitary C_ub *
        ((rUBInCat wOuter wInner2 11).embedUnitary M_s⁻¹ * V *
          (rUBInCat wOuter wInner2 11).embedUnitary M_s) *
        (rUBInCat wOuter wInner2 11).embedUnitary C_ub := by
    have hAs : asymMidMux wOuter wInner2 prepMid = M_s * C_ub :=
      spinCancelUBMux_comm_prepMidDirectXo7Mux (wOuter := wOuter) hSpin
    rw [hAs, _root_.mul_inv_rev, hCInv, QRegister.embedUnitary_mul,
      QRegister.embedUnitary_mul]
    simp only [mul_assoc]
  have hPC : AliasPrep.PreservesWires
      (rMain.embedUnitary ((rUBInCat wOuter wInner2 11).embedUnitary C_ub)).1 S := by
    rw [← QRegister.embedUnitary_compose]
    exact preservesWiresSpinCancelUBMux (rMain.compose (rUBInCat wOuter wInner2 11)) hNot
  rw [hEq, rMain.embedUnitary_mul, rMain.embedUnitary_mul]
  exact AliasPrep.preservesWires_mul (AliasPrep.preservesWires_mul hPC hSym) hPC
theorem circuitH0_mul_z_mul_circuitH0 :
    (Circuit.H (0 : Wire 1)).eval * (Circuit.Z 0).eval * (Circuit.H 0).eval =
      (Circuit.X 0).eval := by
  apply Subtype.ext
  refine QubitisedWalk.matrix_ext_ket fun β ↦ ?_
  have hup (v : ZMod 2) : Function.update β (0 : Wire 1) v 0 = v := by simp
  have hu (x y : ZMod 2) :
      Function.update (Function.update β (0 : Wire 1) x) 0 y = Function.update β 0 y := by
    funext w
    fin_cases w
    simp
  have hZH : (Circuit.Z (0 : Wire 1)).eval.1 *ᵥ ((Circuit.H 0).eval.1 *ᵥ QubitisedWalk.ket β) =
      ((√(1 / 2) : ℝ) : ℂ) • (QubitisedWalk.bitSign 0 • QubitisedWalk.ket (Function.update β 0 0) +
        QubitisedWalk.bitSign (β 0) • (QubitisedWalk.bitSign 1 •
            QubitisedWalk.ket (Function.update β 0 1))) := by
    rw [QubitisedWalk.ket_H, Matrix.mulVec_smul, Matrix.mulVec_add, Matrix.mulVec_smul,
      QubitisedWalk.ket_Z, QubitisedWalk.ket_Z, hup 0, hup 1]
  rw [Submonoid.coe_mul, Submonoid.coe_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hZH,
    Matrix.mulVec_smul, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
    Matrix.mulVec_smul, QubitisedWalk.ket_H, QubitisedWalk.ket_H, QubitisedWalk.ket_X]
  simp only [hu, hup, smul_add, smul_smul]
  have hsq : ((√(1 / 2) : ℝ) : ℂ) * ((√(1 / 2) : ℝ) : ℂ) = (1 / 2 : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    push_cast
    rfl
  rcases QubitisedWalk.zmod2_eq_zero_or_one (β 0) with hb | hb
  · rw [hb, zero_add]
    simp only [QubitisedWalk.bitSign, one_ne_zero, ↓reduceIte, mul_one, one_mul, mul_neg, neg_mul,
      neg_neg, hsq]
    module
  · rw [hb, CharTwo.add_self_eq_zero 1]
    simp only [QubitisedWalk.bitSign, one_ne_zero, ↓reduceIte, mul_one, one_mul, mul_neg, neg_mul,
      neg_neg, hsq]
    module
theorem sigIn_embedUnitary_z_eq_diagonal (wInner2 : ℕ) :
    ((rSigInLoc wInner2).embedUnitary (Circuit.Z (0 : Wire 1)).eval).1 = Matrix.diagonal fun m' ↦
      if (rSigInLoc wInner2).extractIndex m' = 0 then (1 : ℂ) else -1 := by
  have hZ : (rSigInLoc wInner2).embedUnitary (Circuit.Z (0 : Wire 1)).eval =
      (Circuit.Z (rSigInLoc wInner2 0)).eval := by
    rw [Circuit.eval_single, Circuit.eval_single, ← QRegister.embedUnitary_compose]
    exact congrArg (QRegister.embedUnitary · _) (CoherentAlias.qreg_ext fun i ↦ by
      fin_cases i
      rfl)
  rw [hZ]
  refine QubitisedWalk.matrix_ext_ket fun β ↦ ?_
  let m' : Fin (2 ^ mMidUB wInner2) := (basisBitsEquiv (mMidUB wInner2)).symm β
  have hket : QubitisedWalk.ket β = Pi.single m' 1 := by
    rw [QubitisedWalk.single_eq_ket m']
    exact congrArg QubitisedWalk.ket (basisBits_symm2 β).symm
  rw [QubitisedWalk.ket_Z, hket, Matrix.diagonal_mulVec_single]
  have hbit : β (rSigInLoc wInner2 0) = basisBits 1 ((rSigInLoc wInner2).extractIndex m') 0 := by
    rw [(rSigInLoc wInner2).basisBits_extractIndex]
    change _ = (basisBitsEquiv (mMidUB wInner2) m') (rSigInLoc wInner2 0)
    dsimp only [m']
    rw [Equiv.apply_symm_apply]
  have hsign : QubitisedWalk.bitSign (β (rSigInLoc wInner2 0)) =
      if (rSigInLoc wInner2).extractIndex m' = 0 then (1 : ℂ) else -1 := by
    rw [hbit]
    generalize (rSigInLoc wInner2).extractIndex m' = si
    rcases (show si = 0 ∨ si = 1 by fin_cases si <;> simp) with rfl | rfl <;>
      simp [show basisBits 1 (0 : Fin 2) 0 = 0 by decide,
        show basisBits 1 (1 : Fin 2) 0 = 1 by decide, QubitisedWalk.bitSign]
  ext k
  simp only [Pi.smul_apply, Pi.single_apply, smul_eq_mul, hsign]
  split_ifs <;> ring
theorem sigIn_embedUnitary_x_zero_zero (wInner2 : ℕ) :
    ((rSigInLoc wInner2).embedUnitary (Circuit.X (0 : Wire 1)).eval).1 0 0 = 0 := by
  have hX : (rSigInLoc wInner2).embedUnitary (Circuit.X (0 : Wire 1)).eval =
      (Circuit.X (rSigInLoc wInner2 0)).eval := by
    rw [Circuit.eval_single, Circuit.eval_single, ← QRegister.embedUnitary_compose]
    exact congrArg (QRegister.embedUnitary · _) (CoherentAlias.qreg_ext fun i ↦ by
      fin_cases i
      rfl)
  have hv := congrFun (QubitisedWalk.ket_X (rSigInLoc wInner2 0) (basisBits (mMidUB wInner2) 0)) 0
  rw [← QubitisedWalk.single_eq_ket (0 : Fin (2 ^ mMidUB wInner2)), Matrix.mulVec_single_one,
    Matrix.col_apply, ← hX] at hv
  have hne : (0 : Fin (2 ^ mMidUB wInner2)) ≠ (basisBitsEquiv (mMidUB wInner2)).symm
      (Function.update (basisBits (mMidUB wInner2) 0) (rSigInLoc wInner2 0)
        (basisBits (mMidUB wInner2) 0 (rSigInLoc wInner2 0) + 1)) := fun heq ↦ by
    have hq := congrFun (congrArg (basisBitsEquiv (mMidUB wInner2)) heq) (rSigInLoc wInner2 0)
    rw [Equiv.apply_symm_apply] at hq
    change basisBits (mMidUB wInner2) 0 (rSigInLoc wInner2 0) = _ at hq
    rw [Function.update_self, CoherentAlias.basisBits_zero_apply, zero_add] at hq
    exact zero_ne_one hq
  have hket1 :
    QubitisedWalk.ket (Function.update (basisBits (mMidUB wInner2) 0) (rSigInLoc wInner2 0)
      (basisBits (mMidUB wInner2) 0 (rSigInLoc wInner2 0) + 1)) =
      (Pi.single ((basisBitsEquiv (mMidUB wInner2)).symm
        (Function.update (basisBits (mMidUB wInner2) 0) (rSigInLoc wInner2 0)
          (basisBits (mMidUB wInner2) 0 (rSigInLoc wInner2 0) + 1))) (1 : ℂ)) := by
    rw [QubitisedWalk.single_eq_ket]
    exact congrArg QubitisedWalk.ket (basisBits_symm2 _).symm
  rw [hv, hket1, Pi.single_apply, ite_eq_right hne]
theorem prepMid_conj_sigInZ_eq_sigInX {wInner2 : ℕ}
    {prepMid : Fin (2 ^ 7) → Unitary (2 ^ mMidUB wInner2)} (hSpin : PrepMidSpinFactored prepMid)
    (rc : Fin (2 ^ 7)) :
    (prepMid rc)⁻¹ * (rSigInLoc wInner2).embedUnitary (Circuit.Z 0).eval * prepMid rc =
      (rSigInLoc wInner2).embedUnitary (Circuit.X 0).eval := by
  obtain ⟨core, hcore⟩ := hSpin
  let rCore : QRegister (5 + wInner2) (mMidUB wInner2) :=
    QRegister.block 0 (5 + wInner2) (by
      dsimp [mMidUB]
      omega)
  have hDisj : rCore.DisjointWires (rSigInLoc wInner2) := QRegister.disjoint_iff.mpr fun i _ h ↦ by
    have hv := congrArg Fin.val h
    have := i.isLt
    dsimp only [rCore, rSigInLoc, QRegister.block_apply_val] at hv
    omega
  have hHInv : ((Circuit.H (0 : Wire 1)).eval)⁻¹ = (Circuit.H 0).eval := by
    rw [← Circuit.eval_inverse]
    rfl
  have hComm : (rSigInLoc wInner2).embedUnitary (Circuit.X 0).eval * rCore.embedUnitary (core rc) =
      rCore.embedUnitary (core rc) * (rSigInLoc wInner2).embedUnitary (Circuit.X 0).eval :=
    Subtype.ext (rCore.embedMatrix_comm_of_disjoint (rSigInLoc wInner2) hDisj (core rc).1 _).symm
  rw [hcore, _root_.mul_inv_rev, ← (rSigInLoc wInner2).embedUnitary_inv, hHInv,
    show (rCore.embedUnitary (core rc))⁻¹ * (rSigInLoc wInner2).embedUnitary (Circuit.H 0).eval *
      (rSigInLoc wInner2).embedUnitary (Circuit.Z 0).eval *
      ((rSigInLoc wInner2).embedUnitary (Circuit.H 0).eval * rCore.embedUnitary (core rc)) =
      (rCore.embedUnitary (core rc))⁻¹ * ((rSigInLoc wInner2).embedUnitary
        ((Circuit.H 0).eval * (Circuit.Z 0).eval * (Circuit.H 0).eval) *
        rCore.embedUnitary (core rc)) by
      rw [QRegister.embedUnitary_mul, QRegister.embedUnitary_mul]
      simp only [mul_assoc],
    circuitH0_mul_z_mul_circuitH0, hComm, ← mul_assoc, inv_mul_cancel, one_mul]
/-- Post-`prepOut` invariant walk subspace generated by `|ψ, o', 0⟩` and `U_I |ψ, o', 0⟩`. -/
inductive PostOutInv (wOuter wInner2 : ℕ) (prepMid : Fin (2 ^ 7) → Unitary (2 ^ mMidUB wInner2))
    (bound184 : Bool) : (Fin (2 ^ nUB wOuter wInner2) → ℂ) → Prop
  | zero : PostOutInv wOuter wInner2 prepMid bound184 0
  | add {x y} : PostOutInv wOuter wInner2 prepMid bound184 x →
      PostOutInv wOuter wInner2 prepMid bound184 y → PostOutInv wOuter wInner2 prepMid bound184 (x +
        y)
  | smul (c : ℂ) {x} : PostOutInv wOuter wInner2 prepMid bound184 x →
      PostOutInv wOuter wInner2 prepMid bound184 (c • x)
  | midZero (ψ : Fin (2 ^ (2 * 58)) → ℂ) (o' : Fin (2 ^ mOutUB wOuter))
      (hb : bound184 = true → ((rXoLoc wOuter).extractIndex o').val < 184) :
      PostOutInv wOuter wInner2 prepMid bound184 (embedKet ψ o' 0)
  | twoBodyU (ψ : Fin (2 ^ (2 * 58)) → ℂ) (o' : Fin (2 ^ mOutUB wOuter))
      (h126 : ((rXoLoc wOuter).extractIndex o').val < 126) :
      PostOutInv wOuter wInner2 prepMid bound184
        (((prepMidDirectXo7MuxUnitary wOuter wInner2 (fun rc ↦ prepMid (pi128Equiv rc)))⁻¹ *
          idealPi145SelectPure wOuter wInner2 *
          prepMidDirectXo7MuxUnitary wOuter wInner2 (fun rc ↦ prepMid (pi128Equiv rc))).1 *ᵥ
          embedKet ψ o' 0)
theorem PostOutInv.sum {ι : Type*} {wOuter wInner2 : ℕ}
    {prepMid : Fin (2 ^ 7) → Unitary (2 ^ mMidUB wInner2)} {bound184 : Bool} (s : Finset ι)
    (f : ι → Fin (2 ^ nUB wOuter wInner2) → ℂ)
    (hf : ∀ i ∈ s, PostOutInv wOuter wInner2 prepMid bound184 (f i)) :
    PostOutInv wOuter wInner2 prepMid bound184 (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using PostOutInv.zero
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact .add (hf a (Finset.mem_insert_self a s))
      (ih fun i hi ↦ hf i (Finset.mem_insert_of_mem hi))
theorem kernel_step {wOuter wInner2 : ℕ} {prepMid : Fin (2 ^ 7) → Unitary (2 ^ mMidUB wInner2)}
    (hSpin : PrepMidSpinFactored prepMid)
    (hB30 : ∀ (rc : Fin 126) (m : Fin (2 ^ mMidUB wInner2)),
      30 ≤ ((rBLoc wInner2).extractIndex m).val → (prepMid ⟨rc.val, by omega⟩).1 m 0 = 0)
    {dBit : Fin (2 ^ 8) → Fin (2 ^ 5) → Bool} (hd : IsValidDNegBit dBit)
    {bound184 : Bool} {x : Fin (2 ^ nUB wOuter wInner2) → ℂ}
    (hx : PostOutInv wOuter wInner2 prepMid bound184 x) :
    let M_s := prepMidDirectXo7MuxUnitary wOuter wInner2 (fun rc ↦ prepMid (pi128Equiv rc))
    let M_a := asymMidMux wOuter wInner2 prepMid
    let R_mid := QubitisedWalk.reflMidUnitary (rMidUB wOuter wInner2)
    let U_I := M_s⁻¹ * idealPi145SelectPure wOuter wInner2 * M_s
    let U_bal := M_s⁻¹ * balRefSelectPureUnitary pi145XoEquiv wOuter wInner2 * M_s
    let K_ideal := U_I * R_mid * U_I
    let K_bal := U_bal * R_mid * U_bal
    let K_asym :=
      (M_a⁻¹ * (select57NoNegBwdPureUnitary wOuter wInner2 * dNegUB wOuter wInner2 dBit) * M_a) *
        R_mid *
        (M_a⁻¹ * (dNegUB wOuter wInner2 dBit * select57NoNegFwdPureUnitary wOuter wInner2) * M_a)
    PostOutInv wOuter wInner2 prepMid bound184 (K_ideal.1 *ᵥ x) ∧ K_asym.1 *ᵥ x = K_ideal.1 *ᵥ x ∧
      (bound184 = true → K_bal.1 *ᵥ x = K_ideal.1 *ᵥ x) := by
  intro M_s M_a R_mid U_I U_bal K_ideal K_bal K_asym
  have hConjSq (S : Unitary (2 ^ nUB wOuter wInner2)) (hS : S * S = 1) :
      (M_s⁻¹ * S * M_s) * (M_s⁻¹ * S * M_s) = 1 := by
    rw [show (M_s⁻¹ * S * M_s) * (M_s⁻¹ * S * M_s) = M_s⁻¹ * S * (M_s * M_s⁻¹) * S * M_s by
      simp only [mul_assoc], mul_inv_cancel, mul_one, mul_assoc (M_s⁻¹), hS, mul_one,
      inv_mul_cancel]
  have hUI_sq : U_I * U_I = 1 := hConjSq _ (idealPi145SelectPure_mul_self wOuter wInner2)
  have hUbal_sq : U_bal * U_bal = 1 :=
    hConjSq _ (balRefSelectPureUnitary_mul_self pi145XoEquiv wOuter wInner2)
  have hRmid0 (ξ : Fin (2 ^ (2 * 58)) → ℂ) (o' : Fin (2 ^ mOutUB wOuter)) :
      R_mid.1 *ᵥ embedKet ξ o' 0 = (-1 : ℂ) • embedKet ξ o' 0 := by
    change (1 - (2 : ℂ) • (rMidUB wOuter wInner2).basisOutcomeProjector 0) *ᵥ embedKet ξ o' 0 = _
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, projMid_mulVec_embedKet,
      ite_eq_left rfl]
    module
  induction hx with
  | zero => simp only [Matrix.mulVec_zero, implies_true, and_self, PostOutInv.zero]
  | add _ _ ihx ihy =>
    rw [Matrix.mulVec_add, Matrix.mulVec_add]
    exact ⟨.add ihx.1 ihy.1, by rw [ihx.2.1, ihy.2.1],
      fun hb ↦ by rw [Matrix.mulVec_add, ihx.2.2 hb, ihy.2.2 hb]⟩
  | smul c _ ih =>
    rw [Matrix.mulVec_smul, Matrix.mulVec_smul]
    exact ⟨.smul c ih.1, by rw [ih.2.1],
      fun hb ↦ by rw [Matrix.mulVec_smul, ih.2.2 hb]⟩
  | twoBodyU ψ o' h126 =>
    let v₀ := U_I.1 *ᵥ embedKet ψ o' 0
    have hId : K_ideal.1 *ᵥ v₀ = (-1 : ℂ) • v₀ := by
      rw [show K_ideal.1 = U_I.1 * R_mid.1 * U_I.1 from rfl, ← Matrix.mulVec_mulVec,
        ← Matrix.mulVec_mulVec]
      dsimp only [v₀]
      rw [Matrix.mulVec_mulVec _ U_I.1 U_I.1, ← Submonoid.coe_mul, hUI_sq,
        Submonoid.coe_one, Matrix.one_mulVec, hRmid0, Matrix.mulVec_smul]
    have hAs := asymHalfStep_eq_symHalfStep_of_lt126 hB30 hd ψ o' h126
    have hAsEq : K_asym.1 *ᵥ v₀ = (-1 : ℂ) • v₀ := by
      dsimp only [K_asym, v₀]
      rw [Submonoid.coe_mul, Submonoid.coe_mul, ← Matrix.mulVec_mulVec,
        ← Matrix.mulVec_mulVec, hAs.2.2.2, hRmid0, Matrix.mulVec_smul, hAs.2.1]
    have hBalEq : K_bal.1 *ᵥ v₀ = (-1 : ℂ) • v₀ := by
      rw [show K_bal.1 = U_bal.1 * R_mid.1 * U_bal.1 from rfl, ← Matrix.mulVec_mulVec,
        ← Matrix.mulVec_mulVec]
      dsimp only [v₀]
      rw [symHalfStep_ideal_eq_balRef_of_lt184 prepMid ψ o' 0 (by omega),
        Matrix.mulVec_mulVec _ U_bal.1 U_bal.1, ← Submonoid.coe_mul, hUbal_sq, Submonoid.coe_one,
        Matrix.one_mulVec, hRmid0, Matrix.mulVec_smul,
        ← symHalfStep_ideal_eq_balRef_of_lt184 prepMid ψ o' 0 (by omega)]
    rw [hId]
    exact ⟨.smul (-1) (.twoBodyU ψ o' h126), hAsEq, fun _ ↦ hBalEq⟩
  | midZero ψ o' hb =>
    let xo' := (rXoLoc wOuter).extractIndex o'
    let P_m := prepMid (pi128Equiv ((rXo7Loc wOuter).extractIndex o'))
    let fUI : Fin (2 ^ mMidUB wInner2) → Fin (2 ^ (2 * 58)) → ℂ := fun m'' ↦
      ∑ m', P_m.1 m' 0 • ((P_m⁻¹).1 m'' m' • ((idealPi145Branch wOuter wInner2 o' m').1 *ᵥ ψ))
    have hUISum : U_I.1 *ᵥ embedKet ψ o' 0 = ∑ m'', embedKet (fUI m'') o' m'' := by
      have hMsInv : M_s⁻¹ = prepMidDirectXo7MuxUnitary wOuter wInner2
          (fun rc ↦ (prepMid (pi128Equiv rc))⁻¹) := muxUnitary_inv _ _ _ _
      rw [show U_I.1 = (M_s⁻¹).1 * (idealPi145SelectPure wOuter wInner2).1 * M_s.1 from rfl,
        ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hMsInv,
        prepMidDirectXo7Mux_mulVec_embedKet_loc, Matrix.mulVec_sum, Matrix.mulVec_sum]
      have ht (m' : Fin (2 ^ mMidUB wInner2)) :
          (prepMidDirectXo7MuxUnitary wOuter wInner2 fun rc ↦ (prepMid (pi128Equiv rc))⁻¹).1 *ᵥ
            ((idealPi145SelectPure wOuter wInner2).1 *ᵥ (P_m.1 m' 0 • embedKet ψ o' m')) =
          ∑ m'', embedKet (P_m.1 m' 0 •
            ((P_m⁻¹).1 m'' m' • ((idealPi145Branch wOuter wInner2 o' m').1 *ᵥ ψ))) o' m'' := by
        rw [Matrix.mulVec_smul, idealPi145SelectPure_mulVec_embedKet, Matrix.mulVec_smul,
          prepMidDirectXo7Mux_mulVec_embedKet_loc, Finset.smul_sum]
        exact Finset.sum_congr rfl fun m'' _ ↦ by rw [← embedKet_smul, ← embedKet_smul]
      rw [Finset.sum_congr rfl fun m' _ ↦ ht m', Finset.sum_comm]
      exact Finset.sum_congr rfl fun m'' _ ↦ (embedKet_sum Finset.univ _ o' m'').symm
    have hBal184 (h184 : xo'.val < 184) :
        K_bal.1 *ᵥ embedKet ψ o' 0 = K_ideal.1 *ᵥ embedKet ψ o' 0 := by
      have hOutEq (g : Fin (2 ^ mMidUB wInner2) → Fin (2 ^ (2 * 58)) → ℂ) :
          U_bal.1 *ᵥ ∑ m'', embedKet (g m'') o' m'' = U_I.1 *ᵥ ∑ m'', embedKet (g m'') o' m'' := by
        rw [Matrix.mulVec_sum, Matrix.mulVec_sum]
        exact Finset.sum_congr rfl fun m'' _ ↦
          (symHalfStep_ideal_eq_balRef_of_lt184 prepMid (g m'') o' m'' h184).symm
      rw [show K_bal.1 = U_bal.1 * R_mid.1 * U_bal.1 from rfl,
        show K_ideal.1 = U_I.1 * R_mid.1 * U_I.1 from rfl, ← Matrix.mulVec_mulVec,
        ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
        (symHalfStep_ideal_eq_balRef_of_lt184 prepMid ψ o' 0 h184).symm, hUISum]
      have hRm : R_mid.1 *ᵥ ∑ m'', embedKet (fUI m'') o' m'' =
          ∑ m'', embedKet ((if m'' = 0 then (-1 : ℂ) else 1) • fUI m'') o' m'' := by
        change (1 - (2 : ℂ) • (rMidUB wOuter wInner2).basisOutcomeProjector 0) *ᵥ _ = _
        rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, Matrix.mulVec_sum,
          Finset.smul_sum, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun m'' _ ↦ ?_
        rw [projMid_mulVec_embedKet, embedKet_smul]
        by_cases hm0 : m'' = 0
        · subst hm0
          rw [ite_eq_left rfl, ite_eq_left rfl]
          module
        · rw [ite_eq_right hm0, ite_eq_right hm0, smul_zero, sub_zero, one_smul]
      rw [hRm]
      exact hOutEq _
    by_cases h126 : xo'.val < 126
    · have hφ : (rMidUB wOuter wInner2).basisOutcomeProjector 0 *ᵥ (U_I.1 *ᵥ embedKet ψ o' 0) =
          embedKet (fUI 0) o' 0 := by
        rw [hUISum, Matrix.mulVec_sum, Finset.sum_eq_single 0
          (fun m'' _ hm ↦ by rw [projMid_mulVec_embedKet, ite_eq_right hm])
          (fun h0 ↦ absurd (Finset.mem_univ 0) h0), projMid_mulVec_embedKet, ite_eq_left rfl]
      have hRmidUI : R_mid.1 *ᵥ (U_I.1 *ᵥ embedKet ψ o' 0) =
          U_I.1 *ᵥ embedKet ψ o' 0 + (-2 : ℂ) • embedKet (fUI 0) o' 0 := by
        change (1 - (2 : ℂ) • (rMidUB wOuter wInner2).basisOutcomeProjector 0) *ᵥ _ = _
        rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, hφ]
        module
      have hId : K_ideal.1 *ᵥ embedKet ψ o' 0 =
          embedKet ψ o' 0 + (-2 : ℂ) • (U_I.1 *ᵥ embedKet (fUI 0) o' 0) := by
        rw [show K_ideal.1 = U_I.1 * R_mid.1 * U_I.1 from rfl, ← Matrix.mulVec_mulVec,
          ← Matrix.mulVec_mulVec, hRmidUI, Matrix.mulVec_add, Matrix.mulVec_smul,
          Matrix.mulVec_mulVec _ U_I.1 U_I.1, ← Submonoid.coe_mul, hUI_sq, Submonoid.coe_one,
          Matrix.one_mulVec]
      have hAsψ := asymHalfStep_eq_symHalfStep_of_lt126 hB30 hd ψ o' h126
      have hAsφ := asymHalfStep_eq_symHalfStep_of_lt126 hB30 hd (fUI 0) o' h126
      have hAsEq : K_asym.1 *ᵥ embedKet ψ o' 0 =
          embedKet ψ o' 0 + (-2 : ℂ) • (U_I.1 *ᵥ embedKet (fUI 0) o' 0) := by
        dsimp only [K_asym]
        rw [Submonoid.coe_mul, Submonoid.coe_mul, ← Matrix.mulVec_mulVec,
          ← Matrix.mulVec_mulVec, hAsψ.1, hRmidUI, Matrix.mulVec_add, Matrix.mulVec_smul,
          hAsψ.2.2.1, hAsφ.2.1]
      rw [hId]
      exact ⟨.add (.midZero ψ o' hb) (.smul (-2) (.twoBodyU (fUI 0) o' h126)),
        hAsEq, fun _ ↦ (hBal184 (by omega)).trans hId⟩
    · have hMaConj (S_mid : Unitary (2 ^ nUB wOuter wInner2)) (V : Unitary (2 ^ (2 * 58)))
          (ξ : Fin (2 ^ (2 * 58)) → ℂ) (hBr : ∀ m', (asymMidBranch prepMid o').1 m' 0 ≠ 0 →
            S_mid.1 *ᵥ embedKet ξ o' m' = embedKet (V.1 *ᵥ ξ) o' m') :
          (M_a⁻¹ * S_mid * M_a).1 *ᵥ embedKet ξ o' 0 = embedKet (V.1 *ᵥ ξ) o' 0 := by
        rw [Submonoid.coe_mul, Submonoid.coe_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
          asymMidMux_mulVec_embedKet]
        have hMid : S_mid.1 *ᵥ ((rMidUB wOuter wInner2).embedMatrix (asymMidBranch prepMid o').1 *ᵥ
            embedKet ξ o' 0) =
            ∑ m', embedKet (((asymMidBranch prepMid o').1 m' 0) • (V.1 *ᵥ ξ)) o' m' := by
          rw [embedMatrix_rMidUB_mulVec_embedKet, Matrix.mulVec_sum]
          refine Finset.sum_congr rfl fun m' _ ↦ ?_
          by_cases hz : (asymMidBranch prepMid o').1 m' 0 = 0
          · simp only [hz, zero_smul, Matrix.mulVec_zero, embedKet_zero]
          · rw [Matrix.mulVec_smul, hBr m' hz, embedKet_smul]
        have hInvSum (g : Fin (2 ^ mMidUB wInner2) → (Fin (2 ^ (2 * 58)) → ℂ)) :
            (M_a⁻¹).1 *ᵥ ∑ m', embedKet (g m') o' m' =
              (rMidUB wOuter wInner2).embedMatrix ((asymMidBranch prepMid o')⁻¹).1 *ᵥ
                ∑ m', embedKet (g m') o' m' := by
          rw [Matrix.mulVec_sum, Matrix.mulVec_sum]
          exact Finset.sum_congr rfl fun m' _ ↦
            asymMidMux_inv_mulVec_embedKet prepMid (g m') o' m'
        rw [hMid, hInvSum, ← hMid]
        exact conj_rMidUB_mulVec_embedKet_const_branch _ S_mid V ξ o' hBr
      have hUIConst (ξ : Fin (2 ^ (2 * 58)) → ℂ)
          (hS : ∀ m', (idealPi145SelectPure wOuter wInner2).1 *ᵥ embedKet ξ o' m' =
            embedKet ξ o' m') :
          U_I.1 *ᵥ embedKet ξ o' 0 = embedKet ξ o' 0 := by
        have hInvMsMul : (M_s⁻¹).1 * M_s.1 = 1 := congrArg Subtype.val (inv_mul_cancel M_s)
        have hMux0 := prepMidDirectXo7Mux_mulVec_embedKet_loc (wOuter := wOuter) (wInner2 :=
          wInner2)
          (fun rc ↦ prepMid (pi128Equiv rc)) ξ o' 0
        rw [show U_I.1 = (M_s⁻¹).1 * (idealPi145SelectPure wOuter wInner2).1 * M_s.1 from rfl,
          ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hMux0, Matrix.mulVec_sum,
          Matrix.mulVec_sum]
        have hs (m' : Fin (2 ^ mMidUB wInner2)) :
            (M_s⁻¹).1 *ᵥ ((idealPi145SelectPure wOuter wInner2).1 *ᵥ (P_m.1 m' 0 •
              embedKet ξ o' m')) =
            (M_s⁻¹).1 *ᵥ (P_m.1 m' 0 • embedKet ξ o' m') := by rw [Matrix.mulVec_smul, hS]
        rw [Finset.sum_congr rfl fun m' _ ↦ hs m', ← Matrix.mulVec_sum, ← hMux0,
          Matrix.mulVec_mulVec, hInvMsMul, Matrix.one_mulVec]
      by_cases h184 : xo'.val < 184
      · have hge126 : 126 ≤ xo'.val := by omega
        have h1B : (pi145XoEquiv xo').val < 58 := pi145XoEquiv_h1B xo' hge126 h184
        let so := (rSigOutLoc wOuter).extractIndex o'
        let br1 := selectBranchUnitary (pi145XoEquiv xo') so 0 1
        have hbr1_sq : br1 * br1 = 1 := selectBranchUnitary_mul_self _ _ _ _
        let VF : Unitary (2 ^ (2 * 58)) := if inPass1Pi145Xo xo' then br1 else 1
        let VB : Unitary (2 ^ (2 * 58)) := if !inPass1Pi145Xo xo' then br1 else 1
        have hVB_VF : VB * VF = br1 := by
          dsimp only [VB, VF]
          cases inPass1Pi145Xo xo' <;> simp [one_mul, mul_one]
        have hAsF (ξ : Fin (2 ^ (2 * 58)) → ℂ) := hMaConj
          (dNegUB wOuter wInner2 dBit *
              select57NoNegFwdPureUnitary wOuter wInner2) VF ξ fun m' hnz ↦ by
            have hsi0 := asymMidBranchZero_of_oneBody hSpin o' hge126 h184 m' hnz
            have h1s :=
              (select57NoNegPureUnitary_mulVec_oneBodyZero ξ o' m' hge126 h184 hsi0).1
            rw [Submonoid.coe_mul, ← Matrix.mulVec_mulVec, h1s,
              selectBranchUnitary_oneBody1 h1B so ((rBLoc wInner2).extractIndex m')]
            dsimp only [VF, br1, xo', so]
            cases inPass1Pi145Xo ((rXoLoc wOuter).extractIndex o') <;>
              simp only [Bool.false_eq_true, ↓reduceIte, Submonoid.coe_one, Matrix.one_mulVec,
                dNegUB_mulVec_embedKet, hd.2 ((rXoLoc wOuter).extractIndex o') _ hge126, one_smul]
        have hAsB (ξ : Fin (2 ^ (2 * 58)) → ℂ) := hMaConj
          (select57NoNegBwdPureUnitary wOuter wInner2 *
              dNegUB wOuter wInner2 dBit) VB ξ fun m' hnz ↦ by
            have hsi0 := asymMidBranchZero_of_oneBody hSpin o' hge126 h184 m' hnz
            have h2s :=
              (select57NoNegPureUnitary_mulVec_oneBodyZero ξ o' m' hge126 h184 hsi0).2
            rw [Submonoid.coe_mul, ← Matrix.mulVec_mulVec, dNegUB_mulVec_embedKet,
              hd.2 ((rXoLoc wOuter).extractIndex o') _ hge126, ite_eq_right Bool.false_ne_true,
              one_smul, h2s, selectBranchUnitary_oneBody1 h1B so ((rBLoc wInner2).extractIndex m')]
            dsimp only [VB, br1, xo', so]
            cases inPass1Pi145Xo ((rXoLoc wOuter).extractIndex o') <;>
              simp only [Bool.not_true, Bool.not_false, Bool.false_eq_true, ↓reduceIte,
                Submonoid.coe_one, Matrix.one_mulVec]
        have hAsEq : K_asym.1 *ᵥ embedKet ψ o' 0 = (-1 : ℂ) • embedKet (br1.1 *ᵥ ψ) o' 0 := by
          dsimp only [K_asym]
          rw [Submonoid.coe_mul, Submonoid.coe_mul, ← Matrix.mulVec_mulVec,
            ← Matrix.mulVec_mulVec, hAsF, hRmid0, Matrix.mulVec_smul, hAsB, Matrix.mulVec_mulVec,
            ← Submonoid.coe_mul, hVB_VF]
        let φp := ψ + br1.1 *ᵥ ψ
        let φm := ψ - br1.1 *ᵥ ψ
        have hbr1_φp : br1.1 *ᵥ φp = φp := by
          dsimp only [φp]
          rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, ← Submonoid.coe_mul,
            hbr1_sq, Submonoid.coe_one, Matrix.one_mulVec, add_comm]
        have hbr1_φm : br1.1 *ᵥ φm = (-1 : ℂ) • φm := by
          dsimp only [φm]
          rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, ← Submonoid.coe_mul,
            hbr1_sq, Submonoid.coe_one, Matrix.one_mulVec]
          module
        have hUI_φp : U_I.1 *ᵥ embedKet φp o' 0 = embedKet φp o' 0 := hUIConst φp fun m' ↦ by
          rw [selectOnLt184IdealPi145SelectPure wOuter wInner2 φp o' m' h184]
          generalize (rSigInLoc wInner2).extractIndex m' = si
          rcases (show si = 0 ∨ si = 1 by fin_cases si <;> simp) with rfl | rfl
          · rw [selectBranchUnitary_oneBody0 h1B, Submonoid.coe_one, Matrix.one_mulVec]
          · rw [selectBranchUnitary_oneBody1 h1B, hbr1_φp]
        have hPmid_φm :
            (rMidUB wOuter wInner2).basisOutcomeProjector 0 *ᵥ (U_I.1 *ᵥ embedKet φm o' 0) = 0 := by
          let Z_s := (rSigInLoc wInner2).embedUnitary (Circuit.Z 0).eval
          have hSelφm (m' : Fin (2 ^ mMidUB wInner2)) :
              (idealPi145SelectPure wOuter wInner2).1 *ᵥ embedKet φm o' m' =
                (rMidUB wOuter wInner2).embedMatrix Z_s.1 *ᵥ embedKet φm o' m' := by
            rw [selectOnLt184IdealPi145SelectPure wOuter wInner2 φm o' m' h184]
            dsimp only [Z_s]
            rw [sigIn_embedUnitary_z_eq_diagonal, embedMatrix_rMidUB_mulVec_embedKet]
            have hdiag (m'' : Fin (2 ^ mMidUB wInner2)) : Matrix.diagonal (fun k ↦
                if (rSigInLoc wInner2).extractIndex k = 0 then (1 : ℂ) else -1) m'' m' =
                if m'' = m' then (if (rSigInLoc wInner2).extractIndex m' = 0 then (1 : ℂ) else -1)
                else 0 := by by_cases h : m'' = m' <;> simp [h]
            simp_rw [hdiag]
            rw [Finset.sum_eq_single m' (fun m'' _ hm ↦ by rw [ite_eq_right hm, zero_smul])
              (fun hm ↦ absurd (Finset.mem_univ m') hm), ite_eq_left rfl]
            generalize (rSigInLoc wInner2).extractIndex m' = si
            rcases (show si = 0 ∨ si = 1 by fin_cases si <;> simp) with rfl | rfl
            · rw [selectBranchUnitary_oneBody0 h1B, Submonoid.coe_one, Matrix.one_mulVec]
              simp
            · rw [selectBranchUnitary_oneBody1 h1B, hbr1_φm, embedKet_smul]
              simp
          have hStepA : (idealPi145SelectPure wOuter wInner2).1 *ᵥ (M_s.1 *ᵥ embedKet φm o' 0) =
              (rMidUB wOuter wInner2).embedMatrix (Z_s * P_m).1 *ᵥ embedKet φm o' 0 := by
            rw [prepMidDirectXo7Mux_mulVec_embedKet_loc, Matrix.mulVec_sum]
            have hs (x : Fin (2 ^ mMidUB wInner2)) :
                (idealPi145SelectPure wOuter wInner2).1 *ᵥ (P_m.1 x 0 • embedKet φm o' x) =
                P_m.1 x 0 • ((rMidUB wOuter wInner2).embedMatrix Z_s.1 *ᵥ embedKet φm o' x) := by
              rw [Matrix.mulVec_smul, hSelφm]
            rw [Finset.sum_congr rfl fun x _ ↦ hs x, sum_smul_embedMatrix_rMidUB_embedKet]
            rfl
          have hUI_X : U_I.1 *ᵥ embedKet φm o' 0 = (rMidUB wOuter wInner2).embedMatrix
              ((rSigInLoc wInner2).embedUnitary (Circuit.X 0).eval).1 *ᵥ embedKet φm o' 0 := by
            rw [show U_I.1 = (M_s⁻¹).1 * (idealPi145SelectPure wOuter wInner2).1 * M_s.1 from rfl,
              ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hStepA,
              embedMatrix_rMidUB_mulVec_embedKet, Matrix.mulVec_sum]
            have hs (x : Fin (2 ^ mMidUB wInner2)) :
                (M_s⁻¹).1 *ᵥ ((Z_s * P_m).1 x 0 • embedKet φm o' x) =
                (Z_s * P_m).1 x 0 •
                  ((rMidUB wOuter wInner2).embedMatrix (P_m⁻¹).1 *ᵥ embedKet φm o' x) := by
              rw [Matrix.mulVec_smul,
                show M_s⁻¹ = prepMidDirectXo7MuxUnitary wOuter wInner2
                    (fun rc ↦ (prepMid (pi128Equiv rc))⁻¹)
                  from muxUnitary_inv _ _ _ _,
                prepMidDirectXo7Mux_mulVec_embedKet_loc, embedMatrix_rMidUB_mulVec_embedKet]
            rw [Finset.sum_congr rfl fun x _ ↦ hs x, sum_smul_embedMatrix_rMidUB_embedKet,
              ← Submonoid.coe_mul, ← mul_assoc, prepMid_conj_sigInZ_eq_sigInX hSpin]
          rw [hUI_X, embedMatrix_rMidUB_mulVec_embedKet, Matrix.mulVec_sum]
          refine Finset.sum_eq_zero fun m' _ ↦ ?_
          rw [Matrix.mulVec_smul, projMid_mulVec_embedKet]
          by_cases hm0 : m' = 0
          · subst hm0
            rw [ite_eq_left rfl, sigIn_embedUnitary_x_zero_zero, zero_smul]
          · rw [ite_eq_right hm0, smul_zero]
        have hSplit : embedKet (w_gi := wInner2) ψ o' 0 =
            (1 / 2 : ℂ) • embedKet (w_gi := wInner2) φp o' 0 +
              (1 / 2 : ℂ) • embedKet (w_gi := wInner2) φm o' 0 := by
          have hψ : ψ = (1 / 2 : ℂ) • φp + (1 / 2 : ℂ) • φm := by
            dsimp only [φp, φm]
            module
          conv_lhs => rw [hψ]
          rw [embedKet_add, embedKet_smul, embedKet_smul]
        have hPmid_ψ : (rMidUB wOuter wInner2).basisOutcomeProjector 0 *ᵥ (U_I.1 *ᵥ
          embedKet ψ o' 0) =
            (1 / 2 : ℂ) • embedKet φp o' 0 := by
          rw [hSplit, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hUI_φp,
            Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, projMid_mulVec_embedKet,
            ite_eq_left rfl, hPmid_φm, smul_zero, add_zero]
        have hId : K_ideal.1 *ᵥ embedKet ψ o' 0 = (-1 : ℂ) • embedKet (br1.1 *ᵥ ψ) o' 0 := by
          rw [show K_ideal.1 = U_I.1 * R_mid.1 * U_I.1 from rfl, ← Matrix.mulVec_mulVec,
            ← Matrix.mulVec_mulVec]
          change U_I.1 *ᵥ ((1 - (2 : ℂ) •
              (rMidUB wOuter wInner2).basisOutcomeProjector 0) *ᵥ (U_I.1 *ᵥ embedKet ψ o' 0)) = _
          rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, hPmid_ψ, smul_smul,
            Matrix.mulVec_sub, Matrix.mulVec_smul, hUI_φp, Matrix.mulVec_mulVec _ U_I.1 U_I.1,
            ← Submonoid.coe_mul, hUI_sq, Submonoid.coe_one, Matrix.one_mulVec,
            show (2 : ℂ) * (1 / 2 : ℂ) = 1 by norm_num, one_smul, embedKet_add ψ (br1.1 *ᵥ ψ) o' 0]
          module
        rw [hId]
        exact ⟨.smul (-1) (.midZero (br1.1 *ᵥ ψ) o' hb), hAsEq, fun _ ↦ (hBal184 h184).trans hId⟩
      · have hge184 : 184 ≤ xo'.val := by omega
        have hUI_pad : U_I.1 *ᵥ embedKet ψ o' 0 = embedKet ψ o' 0 := hUIConst ψ fun m' ↦ by
          rw [idealPi145SelectPure_mulVec_embedKet, idealPi145Branch, ite_eq_right h184,
            Submonoid.coe_one, Matrix.one_mulVec]
        have hId : K_ideal.1 *ᵥ embedKet ψ o' 0 = (-1 : ℂ) • embedKet ψ o' 0 := by
          rw [show K_ideal.1 = U_I.1 * R_mid.1 * U_I.1 from rfl, ← Matrix.mulVec_mulVec,
            ← Matrix.mulVec_mulVec, hUI_pad, hRmid0, Matrix.mulVec_smul, hUI_pad]
        have hAsF :=
          hMaConj (dNegUB wOuter wInner2 dBit * select57NoNegFwdPureUnitary wOuter wInner2) 1 ψ
          fun m' _ ↦ by
            rw [Submonoid.coe_mul, ← Matrix.mulVec_mulVec,
              select57NoNegPureUnitary_mulVec_ge184 false ψ o' m' hge184,
              dNegUB_mulVec_embedKet, hd.2 ((rXoLoc wOuter).extractIndex o') _ (by omega),
              ite_eq_right Bool.false_ne_true, one_smul, Submonoid.coe_one, Matrix.one_mulVec]
        have hAsB :=
          hMaConj (select57NoNegBwdPureUnitary wOuter wInner2 * dNegUB wOuter wInner2 dBit) 1 ψ
          fun m' _ ↦ by
            rw [Submonoid.coe_mul, ← Matrix.mulVec_mulVec, dNegUB_mulVec_embedKet,
              hd.2 ((rXoLoc wOuter).extractIndex o') _ (by omega), ite_eq_right Bool.false_ne_true,
              one_smul, select57NoNegPureUnitary_mulVec_ge184 true ψ o' m' hge184,
              Submonoid.coe_one, Matrix.one_mulVec]
        have hAsEq : K_asym.1 *ᵥ embedKet ψ o' 0 = (-1 : ℂ) • embedKet ψ o' 0 := by
          dsimp only [K_asym]
          rw [Submonoid.coe_mul, Submonoid.coe_mul, ← Matrix.mulVec_mulVec,
            ← Matrix.mulVec_mulVec, hAsF, Submonoid.coe_one, Matrix.one_mulVec, hRmid0,
            Matrix.mulVec_smul, hAsB, Submonoid.coe_one, Matrix.one_mulVec]
        rw [hId]
        exact ⟨.smul (-1) (.midZero ψ o' hb), hAsEq, fun hbt ↦ absurd (hb hbt) h184⟩
theorem uRefl2_noNegDNeg_mulVec_walkCat {wOuter wInner2 : ℕ} (prepOutImpl :
    Unitary (2 ^ mOutUB wOuter))
    (prepMid : Fin (2 ^ 7) → Unitary (2 ^ mMidUB wInner2)) (dBit : Fin (2 ^ 8) → Fin (2 ^ 5) → Bool)
    {sF sB : Unitary (2 ^ (nUB wOuter wInner2 + 11))}
    (hsF : SelCatEqOuterInner wOuter wInner2 sF (select57NoNegFwdPureUnitary wOuter wInner2))
    (hsB : SelCatEqOuterInner wOuter wInner2 sB (select57NoNegBwdPureUnitary wOuter wInner2))
    (v : Fin (2 ^ nUB wOuter wInner2) → ℂ) :
    let M_a := asymMidMux wOuter wInner2 prepMid
    let Out := (rOutUB wOuter wInner2).embedUnitary prepOutImpl
    let K_asym :=
      M_a⁻¹ * (select57NoNegBwdPureUnitary wOuter wInner2 * dNegUB wOuter wInner2 dBit) * M_a *
      QubitisedWalk.reflMidUnitary (rMidUB wOuter wInner2) *
      (M_a⁻¹ * (dNegUB wOuter wInner2 dBit * select57NoNegFwdPureUnitary wOuter wInner2) * M_a)
    let cat := Solution.CircuitModular.phaseGradientLowFactor 11 3
    (asymURefl2 prepOutImpl prepMid dBit sF sB).1 *ᵥ tensorWalkCat v cat =
      tensorWalkCat ((Out⁻¹ * K_asym * Out).1 *ᵥ v) cat := by
  intro M_a Out K_asym cat
  let rMidCat := inMidWalkCat 11 (mOutUB wOuter) (mMidUB wInner2)
  have hemb (A : Unitary (2 ^ nUB wOuter wInner2)) (x : Fin (2 ^ nUB wOuter wInner2) → ℂ) :
      ((rUBInCat wOuter wInner2 11).embedUnitary A).1 *ᵥ tensorUBCat x cat = tensorUBCat (A.1 *ᵥ
        x) cat :=
    embedMatrix_rUBInCat_mulVec_tensorUBCat A.1 x cat
  have hRmidCat (u : Fin (2 ^ nUB wOuter wInner2) → ℂ) : (QubitisedWalk.reflMidUnitary rMidCat).1 *ᵥ
      tensorUBCat u cat = tensorUBCat ((QubitisedWalk.reflMidUnitary (rMidUB wOuter wInner2)).1 *ᵥ
          u) cat := by
    have hrMid : rMidCat = (rUBInCat wOuter wInner2 11).compose (rMidUB wOuter wInner2) :=
      CoherentAlias.qreg_ext fun i ↦ by
        simp [rMidCat, inMidWalkCat, rUBInCat, rMidUB, rWalkInWalkCat, rMidInWalk]
    have hP : QubitisedWalk.projMid rMidCat =
        (rUBInCat wOuter wInner2 11).embedMatrix (QubitisedWalk.projMid
            (rMidUB wOuter wInner2)) := by
      dsimp only [QubitisedWalk.projMid, QRegister.basisOutcomeProjector]
      rw [hrMid, QRegister.embedMatrix_compose]
    rw [QubitisedWalk.reflMidUnitary_val, QubitisedWalk.reflMidUnitary_val, Matrix.sub_mulVec,
      Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec,
      Matrix.smul_mulVec, hP, embedMatrix_rUBInCat_mulVec_tensorUBCat]
    ext g
    dsimp only [tensorUBCat, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hBwdInv : (ubCustomMuxCatUnitary M_a prepOutImpl (sB * dNegCat wOuter wInner2 dBit)⁻¹)⁻¹ =
      (rUBInCat wOuter wInner2 11).embedUnitary Out⁻¹ *
        (rUBInCat wOuter wInner2 11).embedUnitary M_a⁻¹ * sB *
        dNegCat wOuter wInner2 dBit * (rUBInCat wOuter wInner2 11).embedUnitary M_a := by
    dsimp only [ubCustomMuxCatUnitary, Out]
    rw [QRegister.embedUnitary_compose]
    simp only [_root_.mul_inv_rev, inv_inv, QRegister.embedUnitary_inv, mul_assoc]
  rw [tensorWalkCat_eq_tensorUBCat, tensorWalkCat_eq_tensorUBCat]
  dsimp only [asymURefl2, QubitisedWalk.reflPulledPair]
  change (_ * QubitisedWalk.reflMidUnitary rMidCat *
    ubCustomMuxCatUnitary M_a prepOutImpl (dNegCat wOuter wInner2 dBit * sF)).1 *ᵥ _ = _
  rw [hBwdInv]
  dsimp only [ubCustomMuxCatUnitary, dNegCat, Out]
  rw [QRegister.embedUnitary_compose]
  simp only [Submonoid.coe_mul, ← Matrix.mulVec_mulVec]
  rw [hemb, hemb, hsF, hemb, hemb, hRmidCat, hemb, hemb, hsB, hemb, hemb]
  dsimp only [K_asym]
  simp only [Submonoid.coe_mul, ← Matrix.mulVec_mulVec]
theorem walkRefl2InvErrLe_noNegDNeg_gen {wOuter wInner2 : ℕ} (prepOutImpl :
    Unitary (2 ^ mOutUB wOuter))
    {prepMid : Fin (2 ^ 7) → Unitary (2 ^ mMidUB wInner2)} (hSpin : PrepMidSpinFactored prepMid)
    (hB30 : ∀ (rc : Fin 126) (m : Fin (2 ^ mMidUB wInner2)),
      30 ≤ ((rBLoc wInner2).extractIndex m).val → (prepMid ⟨rc.val, by omega⟩).1 m 0 = 0)
    {dBit : Fin (2 ^ 8) → Fin (2 ^ 5) → Bool} (hd : IsValidDNegBit dBit)
    {sF sB : Unitary (2 ^ (nUB wOuter wInner2 + 11))}
    (hsF : SelCatEqOuterInner wOuter wInner2 sF (select57NoNegFwdPureUnitary wOuter wInner2))
    (hsB : SelCatEqOuterInner wOuter wInner2 sB (select57NoNegBwdPureUnitary wOuter wInner2))
    (bound184 : Bool)
    (hOut184 : bound184 = true → ∀ o' : Fin (2 ^ mOutUB wOuter),
      184 ≤ ((rXoLoc wOuter).extractIndex o').val → prepOutImpl.1 o' 0 = 0) :
    let selRef := if bound184 then balRefSelectPureUnitary pi145XoEquiv wOuter wInner2
      else idealPi145SelectPure wOuter wInner2
    WalkRefl2InvErrLe wOuter wInner2
      (ubDirectXo7PureUnitary prepOutImpl (fun rc ↦ prepMid (pi128Equiv rc)) selRef)
      (asymURefl2 prepOutImpl prepMid dBit sF sB) 0 := by
  intro selRef
  let Out := (rOutUB wOuter wInner2).embedUnitary prepOutImpl
  let M_s := prepMidDirectXo7MuxUnitary wOuter wInner2 (fun rc ↦ prepMid (pi128Equiv rc))
  let U_ref := M_s⁻¹ * selRef * M_s
  let K_ref := U_ref * QubitisedWalk.reflMidUnitary (rMidUB wOuter wInner2) * U_ref
  let P_inv : (Fin (2 ^ nUB wOuter wInner2) → ℂ) → Prop := fun v ↦
    PostOutInv wOuter wInner2 prepMid bound184 (Out.1 *ᵥ v)
  have hZ0 (ξ : Fin (2 ^ (2 * 58)) → ℂ) : P_inv (embedKet ξ 0 0) := by
    dsimp only [P_inv, Out]
    rw [QRegister.embedUnitary_val, embedMatrix_rOutUB_mulVec_embedKet]
    refine PostOutInv.sum Finset.univ _ fun o' _ ↦ ?_
    by_cases h184 : ((rXoLoc wOuter).extractIndex o').val < 184
    · exact .smul _ (.midZero ξ o' fun _ ↦ h184)
    · cases hb : bound184
      · exact .smul _ (.midZero ξ o' fun h ↦ Bool.noConfusion h)
      · rw [hOut184 hb o' (by omega), zero_smul]
        exact .zero
  have hUref_sq : U_ref * U_ref = 1 := by
    have hSelSq : selRef * selRef = 1 := by
      dsimp only [selRef]
      cases bound184 <;> simp
    have hAssoc : U_ref * U_ref = M_s⁻¹ * selRef * (M_s * M_s⁻¹) * selRef * M_s := by
      dsimp only [U_ref]
      simp only [mul_assoc]
    rw [hAssoc, mul_inv_cancel, mul_one, mul_assoc (M_s⁻¹), hSelSq, mul_one, inv_mul_cancel]
  have hR2Eq : QubitisedWalk.reflPulledUnitary (rMidInWalk (mOutUB wOuter) (mMidUB wInner2))
      (ubDirectXo7PureUnitary prepOutImpl (fun rc ↦ prepMid (pi128Equiv rc)) selRef) =
      Out⁻¹ * K_ref * Out := by
    have hrM : rMidInWalk (mOutUB wOuter) (mMidUB wInner2) = rMidUB wOuter wInner2 :=
      CoherentAlias.qreg_ext fun _ ↦ rfl
    have huB : ubDirectXo7PureUnitary prepOutImpl (fun rc ↦ prepMid (pi128Equiv rc)) selRef =
        U_ref * Out := by dsimp only [ubDirectXo7PureUnitary, U_ref, M_s, Out]
    rw [QubitisedWalk.reflPulledUnitary, QubitisedWalk.reflPulledPair, hrM, huB, _root_.mul_inv_rev,
      inv_eq_of_mul_eq_one_right hUref_sq]
    simp only [K_ref, mul_assoc]
  refine ⟨P_inv, fun ψ ↦ ?_, fun v hv ↦ ?_, fun v hv ↦ ?_, fun v hv ↦ ?_⟩
  · rw [show rSysInWalk (mOutUB wOuter) (mMidUB wInner2) = rSysUB wOuter wInner2 from
      CoherentAlias.qreg_ext fun _ ↦ rfl, ← embedKet_zero_zero_eq_tensorState]
    exact hZ0 ψ
  · dsimp only [P_inv]
    rw [show rAllInWalk (mOutUB wOuter) (mMidUB wInner2) = rAllUB wOuter wInner2 from
        CoherentAlias.qreg_ext fun _ ↦ rfl, QubitisedWalk.reflInUnitary_val, Matrix.sub_mulVec,
      Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_add_neg, Matrix.mulVec_add,
      Matrix.mulVec_smul, ← neg_one_smul ℂ v, Matrix.mulVec_smul]
    refine .add (.smul 2 ?_) (.smul (-1) hv)
    have hv_sum : v = ∑ g : Fin (2 ^ nUB wOuter wInner2), v g • Pi.single g 1 := by
      ext i
      simp [Pi.single_apply]
    rw [hv_sum, Matrix.mulVec_sum, Matrix.mulVec_sum]
    refine PostOutInv.sum Finset.univ _ fun g _ ↦ ?_
    rw [Matrix.mulVec_smul, Matrix.mulVec_smul, single_eq_embedKet g]
    change PostOutInv _ _ _ _ (v g • (Out.1 *ᵥ ((rAllUB wOuter wInner2).basisOutcomeProjector 0 *ᵥ
      _)))
    rw [projAll_mulVec_embedKet]
    by_cases hc : (rOutUB wOuter wInner2).extractIndex g = 0 ∧
      (rMidUB wOuter wInner2).extractIndex g = 0
    · rw [ite_eq_left hc]
      exact .smul (v g) (hZ0 _)
    · rw [ite_eq_right hc, Matrix.mulVec_zero, smul_zero]
      exact .zero
  · obtain ⟨hKId, _, hKBal⟩ := kernel_step hSpin hB30 hd hv
    have hOutMulInv : Out.1 * (Out⁻¹).1 = 1 := congrArg Subtype.val (mul_inv_cancel Out)
    dsimp only [P_inv]
    rw [hR2Eq, Submonoid.coe_mul, Submonoid.coe_mul, ← Matrix.mulVec_mulVec,
      ← Matrix.mulVec_mulVec, Matrix.mulVec_mulVec _ Out.1 (Out⁻¹).1, hOutMulInv,
      Matrix.one_mulVec]
    dsimp only [K_ref, U_ref, selRef, M_s]
    cases hb : bound184
    · rw [hb] at hKId
      simpa only [Bool.false_eq_true, ↓reduceIte] using hKId
    · rw [hb] at hKId
      simp only [↓reduceIte]
      rw [hKBal hb]
      exact hKId
  · obtain ⟨_, hKAs, hKBal⟩ := kernel_step hSpin hB30 hd hv
    have hKRef : K_ref.1 *ᵥ (Out.1 *ᵥ v) = (M_s⁻¹ * idealPi145SelectPure wOuter wInner2 * M_s *
        QubitisedWalk.reflMidUnitary (rMidUB wOuter wInner2) *
        (M_s⁻¹ * idealPi145SelectPure wOuter wInner2 * M_s)).1 *ᵥ (Out.1 *ᵥ v) := by
      dsimp only [K_ref, U_ref, selRef]
      cases hb : bound184
      · simp only [Bool.false_eq_true, ↓reduceIte]
      · simp only [↓reduceIte]
        exact hKBal hb
    rw [zero_mul, uRefl2_noNegDNeg_mulVec_walkCat prepOutImpl prepMid dBit hsF hsB v, hR2Eq]
    let M_a := asymMidMux wOuter wInner2 prepMid
    let K_asym :=
      M_a⁻¹ * (select57NoNegBwdPureUnitary wOuter wInner2 * dNegUB wOuter wInner2 dBit) * M_a *
      QubitisedWalk.reflMidUnitary (rMidUB wOuter wInner2) *
      (M_a⁻¹ * (dNegUB wOuter wInner2 dBit * select57NoNegFwdPureUnitary wOuter wInner2) * M_a)
    have hVecEq : (Out⁻¹ * K_asym * Out).1 *ᵥ v = (Out⁻¹ * K_ref * Out).1 *ᵥ v := by
      simp only [Submonoid.coe_mul, ← Matrix.mulVec_mulVec]
      rw [hKAs, hKRef]
    rw [hVecEq, sub_self, WithLp.toLp_zero, norm_zero]
end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.NoNegDNegSOSAndSuperWalk
end
