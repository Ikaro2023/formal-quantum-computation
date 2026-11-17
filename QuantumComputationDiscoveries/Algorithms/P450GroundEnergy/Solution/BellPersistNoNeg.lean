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

public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.BellRouter57Pure
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.CompactCore145Spec

/-!
# `15`-Bit `wNegIn`-Free `SELECT` Unitaries & Inner-Register Commutation

Defines `15`-bit `wNegIn`-free pure and catalytic `SELECT` unitaries (`selectNoNegGenPureUnitary`,
`selectNoNegCat11Unitary`) and proves unconditional inner-register commutation, one-body middle-core
commutation, and self-inverse involution.

## References
- C. Jones, "Low-overhead constructions for the fault-tolerant Toffoli gate," *Phys. Rev. A* **87**,
  022328 (2013), DOI: `10.1103/PhysRevA.87.022328`.
- C. Gidney, "Halving the cost of quantum addition," *Quantum* **2**, 74 (2018),
  DOI: `10.22331/q-2018-06-18-74`.
- R. Babbush, C. Gidney, D. W. Berry, N. Wiebe, J. McClean, A. Paler, A. Fowler, and H. Neven,
  "Encoding Electronic Spectra in Quantum Circuits with Linear T Complexity," *Phys. Rev. X* **8**,
  041015 (2018), DOI: `10.1103/PhysRevX.8.041015`.
- D. W. Berry, C. Gidney, M. Motta, J. R. McClean, and R. Babbush, "Qubitization of Arbitrary
  Basis Quantum Chemistry Leveraging Sparsity and Low Rank Factorization," *Quantum* **3**, 208
  (2019), DOI: `10.22331/q-2019-12-02-208`.
- J. Lee, D. W. Berry, C. Gidney, W. J. Huggins, J. R. McClean, N. Wiebe, and R. Babbush,
  "Even More Efficient Quantum Computations of Chemistry Through Tensor Hypercontraction,"
  *PRX Quantum* **2**, 030305 (2021), DOI: `10.1103/PRXQuantum.2.030305`.
-/

@[expose] public section

namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.NoNegSelect57Pure
open QuantumComputation.Specs QuantumComputation.Specs.P450

open Operator QProg Matrix HermitianMat Real CoherentAlias Solution.CleanDyn
open QuantumComputation.Specs Solution QuantumComputation.Specs.P450 Solution
open Solution.CircuitModular Solution.GivensOps
open Solution.BlockEncodingCore Solution.BlockEncodingCircuit
open Solution.SelectSwapQROM Solution.GivensCascade
open Solution.SelectRouter10 Solution.TopIntegrationBridge
open Solution.Lac2Fused184Select Solution.Lac2Fused184SelectWrap Solution.Router10Lac2Select
open Solution.Phase2MidSandwich Solution.PolymorphicFused184Select Solution.Lac2ZeroPar183Select
open Solution.CompactFoldedSelect Solution.ReordOuter13Bridge Solution.CompactStepFast176Select
open Solution.StepEncK Solution.StepDecK Solution.CompactStepFast175Core
open Solution.CompactOuter9Bound50Core Solution.CompactOuter9Bound50Select
open Solution.MobiusOptSubcube163Walk
open Solution.CompactTuned162StepWalk Solution.CompactTuned162StepZeroCmp20
open Solution.CompactZeroCmp20OuterParam Solution.CompactStepZeroCmp20OuterParam
open Solution.Balanced160Select Solution.Pi145SOSPermBridge Solution.OneHotSimulates
open Solution.LowBitPi145Select
open Solution.ZeroRcHotPrepMid21Fast WalkQPEBridge WalkQPEBridgeXMeas WalkQPEFlexBridge
open scoped Matrix BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator Circuit.Notation
open Solution.BellRouter57 Solution.BellRouter57Pure

/-! ## Section 1: Control Registers & General Disjoint-`muxUnitary` Commutation -/

/-- `15`-wire `(xo : 8, so : 1, b : 5, si : 1)` `SELECT` control register inside
`nUB wOuter wInner2 + kCat`. -/
def rSelCtrl15InCat (wOuter wInner2 kCat : ℕ) : QRegister 15 (nUB wOuter wInner2 + kCat) :=
  (rAllInCat wOuter wInner2 kCat).compose (selCtrlInAnc wOuter wInner2)

theorem disjoint_rSelCtrlUB_rSysUB (wOuter wInner2 : ℕ) :
    (rSelCtrlUB wOuter wInner2).DisjointWires (rSysUB wOuter wInner2) := by
  rw [QRegister.disjoint_iff]; intro i j h
  have hv := congrArg Fin.val h
  simp [rSelCtrlUB, rAllUB, rSysUB] at hv; omega

theorem disjoint_rSelCtrl15InCat_rSysCatUB (wOuter wInner2 kCat : ℕ) :
    (rSelCtrl15InCat wOuter wInner2 kCat).DisjointWires (rSysCatUB wOuter wInner2 kCat) := by
  rw [QRegister.disjoint_iff]; intro i j h
  exact (disjoint_rAllInCat_rSysCatUB wOuter wInner2 kCat).ne _ j h

/-- Pad a `15`-bit `(xo', so, b, si)` control vector to `16` bits by setting bit `15` to `false`. -/
def pad15False (x15 : Fin 15 → Bool) (i : Fin 16) : Bool :=
  if h : i.val < 15 then x15 ⟨i.val, h⟩ else false

/-- Pack `(xo' : Fin (2 ^ 8), so : Bool, b : Fin (2 ^ 5), si : Bool)` into `Fin 15 → Bool`. -/
def pack15 (xo' : Fin (2 ^ 8)) (so : Bool) (b : Fin (2 ^ 5)) (si : Bool) (i : Fin 15) : Bool :=
  pack16 xo' so b si false ⟨i.val, by omega⟩

@[simp] theorem pad15False_pack15 (xo' : Fin (2 ^ 8)) (so : Bool) (b : Fin (2 ^ 5)) (si : Bool) :
    pad15False (pack15 xo' so b si) = pack16 xo' so b si false := by
  funext k; dsimp only [pad15False, pack15]
  by_cases hk : k.val < 15
  · exact dite_eq_left hk
  · rw [dite_eq_right hk]
    have hk15 : k.val = 15 := by omega
    simp [pack16, hk15]

/-- `12`-bit Stage-2 control/sign vector with `signBit` (`j = 11`) identically set to `false`. -/
def y12NoNegOfState24 (specA : (Fin 16 → Bool) → State24) (specB : State24 → State24)
    (x16 : Fin 16 → Bool) (j : Fin 12) : Bool :=
  if h : j.val < 10 then ctrl10OfState24 (specB (specA x16)) ⟨j.val, h⟩
  else if j.val = 10 then sigSelOfState24 (specB (specA x16))
  else false

/-- `15`-bit `wNegIn`-free `12`-bit Stage-2 control vector (`x16 15 := false`). -/
def y12NoNegOf15 (specA : (Fin 16 → Bool) → State24) (specB : State24 → State24)
    (x15 : Fin 15 → Bool) : Fin 12 → Bool :=
  y12NoNegOfState24 specA specB (pad15False x15)

/-- Branch-polymorphic `wNegIn`-free pure `SELECT` unitary on `nUB wOuter wInner2`
(reads only the `15` `(xo, so, b, si)` wires of `rSelCtrlUB wOuter wInner2`; no `wNegIn` parameter).
-/
noncomputable def selectNoNegGenPureUnitary (branch10 : Fin (2 ^ 10) → Unitary (2 ^ 58))
    (specA : (Fin 16 → Bool) → State24) (specB : State24 → State24) (wOuter wInner2 : ℕ) :
    Unitary (2 ^ nUB wOuter wInner2) :=
  muxUnitary (rSelCtrlUB wOuter wInner2) (rSysUB wOuter wInner2)
    (disjoint_rSelCtrlUB_rSysUB wOuter wInner2)
    (fun c15 ↦ selectGenCoreBranch 0 (fun m10 ↦ branch10 (finOfBits 10 m10))
      (y12NoNegOf15 specA specB (bitsOfFin 15 c15)))

/-- `11`-qubit phase-gradient catalytic `wNegIn`-free `SELECT` unitary on `nUB wOuter wInner2 + 11`
(reads only the `15` `(xo, so, b, si)` wires of `rSelCtrl15InCat wOuter wInner2 11`). -/
noncomputable def selectNoNegCat11Unitary (specA : (Fin 16 → Bool) → State24)
    (specB : State24 → State24) (wOuter wInner2 : ℕ)
    (WPhased : Fin (2 ^ 10) → Unitary (2 ^ (58 + 11))) : Unitary (2 ^ (nUB wOuter wInner2 + 11)) :=
  muxUnitary (rSelCtrl15InCat wOuter wInner2 11) (rSysCatUB wOuter wInner2 11)
    (disjoint_rSelCtrl15InCat_rSysCatUB wOuter wInner2 11)
    (fun c15 ↦ selectGenCoreBranch 11 (fun m10 ↦ WPhased (finOfBits 10 m10))
      (y12NoNegOf15 specA specB (bitsOfFin 15 c15)))

theorem selectNoNegGenPureUnitary_mulVec_embedKet_eq_of_branch {wOuter wInner2 : ℕ}
    (branch10 : Fin (2 ^ 10) → Unitary (2 ^ 58))
    (specA : (Fin 16 → Bool) → State24) (specB : State24 → State24)
    (ψ : Fin (2 ^ (2 * 58)) → ℂ) (o' : Fin (2 ^ mOutUB wOuter)) (m : Fin (2 ^ mMidUB wInner2))
    (U : Unitary (2 ^ (2 * 58)))
    (hBr : selectGenCoreBranch 0 (fun m10 ↦ branch10 (finOfBits 10 m10))
        (y12NoNegOf15 specA specB (pack15 ((rXoLoc wOuter).extractIndex o')
          (decide ((rSigOutLoc wOuter).extractIndex o' = 1)) ((rBLoc wInner2).extractIndex m)
          (decide ((rSigInLoc wInner2).extractIndex m = 1)))) = U) :
    (selectNoNegGenPureUnitary branch10 specA specB wOuter wInner2).1 *ᵥ embedKet ψ o' m =
      embedKet (U.1 *ᵥ ψ) o' m := by
  let xo' := (rXoLoc wOuter).extractIndex o'; let so := (rSigOutLoc wOuter).extractIndex o'
  let b := (rBLoc wInner2).extractIndex m; let si := (rSigInLoc wInner2).extractIndex m
  let a' : Fin (2 ^ mAncUB wOuter wInner2) :=
    (BlockEncodingCore.splitBlockEquiv (mOutUB wOuter) (mMidUB wInner2)).symm (o', m)
  let c' : Fin (2 ^ 15) := (selCtrlInAnc wOuter wInner2).extractIndex a'
  let bOut : QRegister (mOutUB wOuter) (mAncUB wOuter wInner2) :=
    QRegister.block 0 (mOutUB wOuter) (by dsimp [mAncUB]; omega)
  let bMid := bMidPolyInAnc wOuter wInner2
  have hc' (g : Fin (2 ^ nUB wOuter wInner2)) (h : (rSelCtrlUB wOuter wInner2).extractIndex g ≠
    c') :
      embedKet ψ o' m g = 0 := by
    dsimp [embedKet]; by_contra hnz
    have hc : (rOutUB wOuter wInner2).extractIndex g = o' ∧ (rMidUB wOuter wInner2).extractIndex g =
        m := by
      by_contra hc; simp [hc] at hnz
    apply h; dsimp only [rSelCtrlUB, c']; rw [QRegister.extractIndex_compose]
    congr 1; apply (BlockEncodingCore.splitBlockEquiv (mOutUB wOuter) (mMidUB wInner2)).injective
    rw [Equiv.apply_symm_apply]; apply Prod.ext
    · rw [splitBlockEquiv_fst, ← QRegister.extractIndex_compose,
        show (rAllUB wOuter wInner2).compose bOut = rOutUB wOuter wInner2 from
          CoherentAlias.qreg_ext fun i ↦ by simp [rAllUB, rOutUB, bOut], hc.1]
    · rw [splitBlockEquiv_snd, ← QRegister.extractIndex_compose,
        show (rAllUB wOuter wInner2).compose (QRegister.block (mOutUB wOuter) (mMidUB wInner2) _) =
          rMidUB wOuter wInner2 from
          CoherentAlias.qreg_ext fun j ↦ by simp [rAllUB, rMidUB]; omega, hc.2]
  have hbo' : bOut.extractIndex a' = o' := (splitBlockEquiv_fst _ _ a').symm.trans (congrArg
    Prod.fst ((BlockEncodingCore.splitBlockEquiv _ _).apply_symm_apply (o', m)))
  have hbm' : bMid.extractIndex a' = m := (splitBlockEquiv_snd _ _ a').symm.trans (congrArg
    Prod.snd ((BlockEncodingCore.splitBlockEquiv _ _).apply_symm_apply (o', m)))
  have hbs1 (s : Fin 2) : bitsOfFin 1 s 0 = decide (s = 1) := by fin_cases s <;> decide
  have hx15 : bitsOfFin 15 c' = pack15 xo' (decide (so = 1)) b (decide (si = 1)) := by
    funext k; dsimp only [pack15, pack16, c']; rw [bitsOfFin_extractIndex]
    by_cases hk8 : k.val < 8
    · rw [ite_eq_left hk8, ← bitsOfFin_eq_div_mod_b xo' ⟨k.val, hk8⟩]
      dsimp only [xo']; rw [← hbo', bitsOfFin_extractIndex, bitsOfFin_extractIndex]
      refine congrArg (bitsOfFin _ a') ((congrArg (selCtrlInAnc wOuter wInner2)
        (show k = Fin.castAdd (5 + 1) (Fin.castAdd 1 ⟨k.val, hk8⟩) by ext; simp)).trans ?_)
      rw [selCtrlInAnc, QRegister.concat_apply_left, QRegister.compose_apply,
        selOutCtrlLoc, QRegister.concat_apply_left]
    · by_cases hkEq8 : k.val = 8
      · rw [ite_eq_right hk8, ite_eq_left hkEq8, ← hbs1 so]; dsimp only [so]
        rw [← hbo', bitsOfFin_extractIndex, bitsOfFin_extractIndex]
        refine congrArg (bitsOfFin _ a') ?_
        rw [show k = Fin.castAdd (5 + 1) (Fin.natAdd 8 (0 : Fin 1)) by ext; simp [hkEq8],
          selCtrlInAnc, QRegister.concat_apply_left, QRegister.compose_apply,
          selOutCtrlLoc, QRegister.concat_apply_right]
      · by_cases hk14 : k.val < 14
        · rw [ite_eq_right hk8, ite_eq_right hkEq8, ite_eq_left hk14,
            ← bitsOfFin_eq_div_mod_b b ⟨k.val - 9, by omega⟩]; dsimp only [b]
          rw [← hbm', bitsOfFin_extractIndex, bitsOfFin_extractIndex]
          refine congrArg (bitsOfFin _ a') ((congrArg (selCtrlInAnc wOuter wInner2)
            (show k = Fin.natAdd (8 + 1) (Fin.castAdd 1 (⟨k.val - 9, by omega⟩ : Fin 5)) by
              ext; simp; omega)).trans ?_)
          rw [selCtrlInAnc, QRegister.concat_apply_right, QRegister.compose_apply,
            selMidCtrlLoc, QRegister.concat_apply_left]; rfl
        · have hkEq14 : k.val = 14 := by omega
          rw [ite_eq_right hk8, ite_eq_right hkEq8, ite_eq_right hk14, ite_eq_left hkEq14,
            ← hbs1 si]
          dsimp only [si]; rw [← hbm', bitsOfFin_extractIndex, bitsOfFin_extractIndex]
          refine congrArg (bitsOfFin _ a') ?_
          rw [show k = Fin.natAdd (8 + 1) (Fin.natAdd 5 (0 : Fin 1)) by ext; simp [hkEq14],
            selCtrlInAnc, QRegister.concat_apply_right, QRegister.compose_apply,
            selMidCtrlLoc, QRegister.concat_apply_right]
          ext; simp [bMid, bMidPolyInAnc]
  rw [selectNoNegGenPureUnitary, muxUnitary_mulVec_of_proj _ _ _ _ c' _ hc', hx15, hBr,
    embedMatrix_rSysUB_mulVec_embedKet]

@[simp] theorem selectNoNegGenPureUnitary_inv {branch10 : Fin (2 ^ 10) → Unitary (2 ^ 58)}
    (hBrInv : ∀ c10, (branch10 c10)⁻¹ = branch10 c10)
    (specA : (Fin 16 → Bool) → State24) (specB : State24 → State24) (wOuter wInner2 : ℕ) :
    (selectNoNegGenPureUnitary branch10 specA specB wOuter wInner2)⁻¹ =
      selectNoNegGenPureUnitary branch10 specA specB wOuter wInner2 := by
  unfold selectNoNegGenPureUnitary; rw [muxUnitary_inv]
  refine congrArg (muxUnitary _ _ _) (funext fun c15 ↦ ?_)
  let y := y12NoNegOf15 specA specB (bitsOfFin 15 c15)
  dsimp only [selectGenCoreBranch]
  set sSw : Unitary (2 ^ (2 * 58 + 0)) :=
    (QRegister.block 0 (2 * 58) (by omega)).embedUnitary
      (if y 10 then permutationUnitary (spinSwapEquiv 58) else 1)
  set uRf : Unitary (2 ^ (2 * 58 + 0)) :=
    (spinCatSub 0).embedUnitary (branch10 (finOfBits 10 fun j ↦ y ⟨j.val, by omega⟩))
  set uPh : Unitary (2 ^ (2 * 58 + 0)) := if y 11 then negOneUnitary (2 * 58 + 0) else 1
  have hS : sSw⁻¹ = sSw := by
    apply unitary_self_inv_b; dsimp only [sSw]; rw [← QRegister.embedUnitary_mul]
    by_cases hy10 : y 10 = true
    · simp only [hy10, ↓reduceIte, spinSwapPermUnitary_mul_self_bal145, QRegister.embedUnitary_one]
    · simp only [Bool.not_eq_true] at hy10
      simp only [hy10, Bool.false_eq_true, ↓reduceIte, mul_one, QRegister.embedUnitary_one]
  have hRf : uRf⁻¹ = uRf := by
    dsimp only [uRf]; rw [← QRegister.embedUnitary_inv, hBrInv]
  have hM : (sSw * (uRf * sSw))⁻¹ = sSw * (uRf * sSw) := by
    rw [_root_.mul_inv_rev, _root_.mul_inv_rev, hS, hRf, mul_assoc]
  change (uPh * (sSw * (uRf * sSw)))⁻¹ = uPh * (sSw * (uRf * sSw))
  dsimp only [uPh]; cases y 11
  · simp only [Bool.false_eq_true, ↓reduceIte, one_mul, hM]
  · simp only [↓reduceIte]; exact negOneUnitary_mul_self_inv hM

end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.NoNegSelect57Pure
end

/-!
# `GenCore145Bundle` & Single-Pass `wNegIn`-Free `SELECT` Slice (`0 < wInner2`)

Packages branch-polymorphic Stage-2 `145`-channel cores (`GenCore145Bundle`, `Core145Bundle.toGen`)
and
constructs the `wNegIn`-free single-pass `SELECT` slice (`selectLowBitNoNegCoreSliceDyn`) using
`wDummy := ⟨0, hGiPos⟩` and omitting `cEntrySign23`.

## References
- C. Jones, "Low-overhead constructions for the fault-tolerant Toffoli gate," *Phys. Rev. A* **87**,
  022328 (2013), DOI: `10.1103/PhysRevA.87.022328`.
- C. Gidney, "Halving the cost of quantum addition," *Quantum* **2**, 74 (2018),
  DOI: `10.22331/q-2018-06-18-74`.
- R. Babbush, C. Gidney, D. W. Berry, N. Wiebe, J. McClean, A. Paler, A. Fowler, and H. Neven,
  "Encoding Electronic Spectra in Quantum Circuits with Linear T Complexity," *Phys. Rev. X* **8**,
  041015 (2018), DOI: `10.1103/PhysRevX.8.041015`.
- D. W. Berry, C. Gidney, M. Motta, J. R. McClean, and R. Babbush, "Qubitization of Arbitrary
  Basis Quantum Chemistry Leveraging Sparsity and Low Rank Factorization," *Quantum* **3**, 208
  (2019), DOI: `10.22331/q-2019-12-02-208`.
- J. Lee, D. W. Berry, C. Gidney, W. J. Huggins, J. R. McClean, N. Wiebe, and R. Babbush,
  "Even More Efficient Quantum Computations of Chemistry Through Tensor Hypercontraction,"
  *PRX Quantum* **2**, 030305 (2021), DOI: `10.1103/PRXQuantum.2.030305`.
-/

@[expose] public section

open QuantumComputationSpecs.Algorithms.P450GroundEnergy
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution
open QuantumComputation.Specs QuantumComputation.Specs.P450

open Operator QProg Matrix HermitianMat Real CoherentAlias Solution.CleanDyn AliasPrep
open QuantumComputation.Specs Solution QuantumComputation.Specs.P450 Solution
open Solution.CircuitModular Solution.GivensOps
open Solution.BlockEncodingCore Solution.BlockEncodingCircuit
open Solution.SelectSwapQROM Solution.GivensCascade
open Solution.SelectRouter10 Solution.TopIntegrationBridge
open Solution.Lac2Fused184Select Solution.Lac2Fused184SelectWrap Solution.Router10Lac2Select
open Solution.Phase2MidSandwich Solution.PolymorphicFused184Select Solution.Lac2ZeroPar183Select
open Solution.CompactFoldedSelect Solution.ReordOuter13Bridge
open Solution.CompactStepFast176Select hiding midRemWidth
  combARem
open Solution.StepEncK Solution.StepDecK Solution.CompactStepFast175Core
open Solution.CompactOuter9Bound50Core Solution.CompactOuter9Bound50Select
open Solution.MobiusOptSubcube163Walk
open Solution.CompactTuned162StepWalk Solution.CompactTuned162StepZeroCmp20
open Solution.CompactZeroCmp20OuterParam Solution.CompactStepZeroCmp20OuterParam
open Solution.Balanced160Select Solution.Pi145SOSPermBridge Solution.OneHotSimulates
open Solution.LowBitPi145Select
open Solution.ZeroRcHotPrepMid21Fast Solution.TwoGearQPEPhase5
open Solution.WalkQPEBridge hiding
  rActLoc rActLoc_disjoint_rScrLoc rCatInAct rCatLoc rQPEInAct rQPEInAct_disjoint_rWalkCatInAct
  rQPEInAnc rQPELoc rQPELoc_disjoint_rScrLoc rQPELoc_disjoint_rWalkCatLoc rScrLoc rScrUbLoc
  rWalkCatInAct rWalkCatLoc rWalkCatLoc_disjoint_rScrLoc
open Solution.WalkQPEBridgeXMeas hiding
  image_rFullZeroLoc rFullZeroLoc
open Solution.WalkQPEFlexBridge hiding
  cleanRealizesSet_of_rScrUbLoc cleanRealizes_rScrLoc_of_sub
open scoped Matrix BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator Circuit.Notation
open Solution.BellRouter57 Solution.BellRouter57Pure Solution.NoNegSelect57Pure
open Solution.CompactCore145Bundle
open Solution.BellPersistCore

namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.BellPersistNoNeg

/-! ## Section 2: `GenCore145Bundle` & Single-Pass `wNegIn`-Free `SELECT` Slice (`0 ≤ d ≤ 10`) -/

/-- Branch-polymorphic `145`-leaf Stage-2 core package on `kInner` inner scratch wires. -/
structure GenCore145Bundle (kInner tCore : ℕ) (branch10 : Fin (2 ^ 10) → Unitary (2 ^ 58)) where
  /-- At least `6` inner clean scratch wires for Stage-B borrows and `cswapBlockDyn`. -/
  hk6 : 6 ≤ kInner
  /-- Core circuit polymorphic in ambient layout `L : Core145Layout kInner n`. -/
  coreUnitDyn : ∀ {n : ℕ}, Core145Layout kInner n → DynamicCircuit Unit n
  /-- Zero `TOFF` gates in `coreUnitDyn`. -/
  count_toff : ∀ {n : ℕ} (L : Core145Layout kInner n), (coreUnitDyn L).count .TOFF = 0
  /-- Exact `T` count `tCore` of `coreUnitDyn`. -/
  count_t : ∀ {n : ℕ} (L : Core145Layout kInner n), (coreUnitDyn L).count .T = tCore
  /-- Subspace simulation on `sValidCore L` with exact `11`-qubit phase-gradient catalyst action. -/
  simCore : ∀ {n : ℕ} (L : Core145Layout kInner n),
    ∃ wPhased : Fin (2 ^ 10) → Unitary (2 ^ (58 + 11)),
      DiagProjSimulates (ketPredProj (sValidCore L))
        (((L.rSpin.concat L.rCat11 (OneHotMux.disj_sys_cat_of L.hsc L.hac)).concat
          L.rCtrl10 (OneHotMux.disj_sysCat_ctrl_of L.hsc L.hac)).embedUnitary
          (UnsignedGivens.muxCtrlUnitary wPhased))
        (coreUnitDyn L) ∧
      ∀ (c10 : Fin (2 ^ 10)) (ψ : Fin (2 ^ 58) → ℂ),
        (wPhased c10).1 *ᵥ prodState ψ (phaseGradientLowFactor 11 3) =
          prodState ((branch10 c10).1 *ᵥ ψ) (phaseGradientLowFactor 11 3)

end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.BellPersistNoNeg

namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.LowBitPi145Select
open Solution.BellPersistNoNeg

/-- Lift an orbital-parameterized `Core145Bundle` to a branch-polymorphic
  `GenCore145Bundle`. -/
noncomputable def Core145Bundle.toGen
    {kInner tCore : ℕ} {actFlipMask : Fin 145 → Bool}
    {orbitalOf : Fin 145 → Bool → Fin 319} {negMask : Fin 145 → Bool}
    (P : Core145Bundle kInner tCore actFlipMask orbitalOf negMask) :
    GenCore145Bundle kInner tCore
      (phase2Bal145PhasedBranch actFlipMask orbitalOf negMask) where
  hk6 := P.hk6
  coreUnitDyn := P.coreUnitDyn
  count_toff := P.count_toff
  count_t := P.count_t
  simCore := P.simCore

end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.LowBitPi145Select

namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.BellPersistNoNeg

/-- Inner `stepsB`-conjugated Stage-2 body (`dSwap ;; coreUnitDyn ;; dSwap`) without `wNegIn`. -/
noncomputable def selectLowBitNoNegInnerBUnitDyn {N kInner tCore : ℕ}
    {branch10 : Fin (2 ^ 10) → Unitary (2 ^ 58)}
    (P : GenCore145Bundle kInner tCore branch10) (stepsB : List (RouterStep 23))
    (wOuter wInner2 : ℕ) (hGiPos : 0 < wInner2)
    (rMain : QRegister (nUB wOuter wInner2 + 11) N) (rScr : QRegister (1 + kInner) N) :
    DynamicCircuit Unit N :=
  if hdisj : rMain.DisjointWires rScr then
    let wDummy : Wire wInner2 := ⟨0, hGiPos⟩
    let rRouter23 := lowBitRouter23 P.hk6 wOuter wInner2 wDummy rMain rScr hdisj
    let L := lowBitCoreLayout wOuter wInner2 wDummy rMain rScr hdisj
    let dSwap := cswapBlockDyn () 58 (rSwap117LowBit wOuter wInner2 wDummy rMain)
      (L.rInner ⟨0, by have := P.hk6; omega⟩)
    routerStepsProg () (LowBitPi145Select.liftRouterStepsN rRouter23 stepsB)
      (.seq dSwap (.seq (P.coreUnitDyn L) dSwap))
  else .identity

/-- `wNegIn`-free two-stage `23`-wire `SELECT` `DynamicCircuit Unit` (omitting `cEntrySign23`). -/
noncomputable def selectLowBitNoNegCoreUnitDyn {N kInner tCore : ℕ}
    {branch10 : Fin (2 ^ 10) → Unitary (2 ^ 58)}
    (P : GenCore145Bundle kInner tCore branch10) (stepsA stepsB : List (RouterStep 23))
    (wOuter wInner2 : ℕ) (hGiPos : 0 < wInner2)
    (rMain : QRegister (nUB wOuter wInner2 + 11) N) (rScr : QRegister (1 + kInner) N) :
    DynamicCircuit Unit N :=
  if hdisj : rMain.DisjointWires rScr then
    let rRouter23 := lowBitRouter23 P.hk6 wOuter wInner2 ⟨0, hGiPos⟩ rMain rScr hdisj
    routerStepsProg () (LowBitPi145Select.liftRouterStepsN rRouter23 stepsA)
      (selectLowBitNoNegInnerBUnitDyn P stepsB wOuter wInner2 hGiPos rMain rScr)
  else .identity

@[simp] theorem count_selectLowBitNoNegInnerBUnitDyn_toff {N kInner tCore : ℕ}
    {branch10 : Fin (2 ^ 10) → Unitary (2 ^ 58)}
    (P : GenCore145Bundle kInner tCore branch10) (stepsB : List (RouterStep 23))
    (wOuter wInner2 : ℕ) (hGiPos : 0 < wInner2)
    (rMain : QRegister (nUB wOuter wInner2 + 11) N) (rScr : QRegister (1 + kInner) N) :
    (selectLowBitNoNegInnerBUnitDyn P stepsB wOuter wInner2 hGiPos rMain rScr).count .TOFF = 0 := by
  dsimp only [selectLowBitNoNegInnerBUnitDyn]; split_ifs
  · rw [count_routerStepsProg_toff]; simp [cswapBlockDyn_count_toff, P.count_toff]
  · rfl

@[simp] theorem count_selectLowBitNoNegCoreUnitDyn_toff {N kInner tCore : ℕ}
    {branch10 : Fin (2 ^ 10) → Unitary (2 ^ 58)}
    (P : GenCore145Bundle kInner tCore branch10) (stepsA stepsB : List (RouterStep 23))
    (wOuter wInner2 : ℕ) (hGiPos : 0 < wInner2)
    (rMain : QRegister (nUB wOuter wInner2 + 11) N) (rScr : QRegister (1 + kInner) N) :
    (selectLowBitNoNegCoreUnitDyn P stepsA stepsB wOuter wInner2 hGiPos rMain rScr).count .TOFF =
        0 := by
  dsimp only [selectLowBitNoNegCoreUnitDyn]; split_ifs
  · rw [count_routerStepsProg_toff, count_selectLowBitNoNegInnerBUnitDyn_toff]
  · rfl

/-- `Var`-polymorphic `1 + kInner`-scratch `wNegIn`-free `SELECT` `DynamicCircuit`. -/
noncomputable def selectLowBitNoNegCoreDyn {Var : Type} {N kInner tCore : ℕ}
    {branch10 : Fin (2 ^ 10) → Unitary (2 ^ 58)}
    (P : GenCore145Bundle kInner tCore branch10) (stepsA stepsB : List (RouterStep 23))
    (v : Var) (wOuter wInner2 : ℕ) (hGiPos : 0 < wInner2)
    (rMain : QRegister (nUB wOuter wInner2 + 11) N) (rScr : QRegister (1 + kInner) N) :
    DynamicCircuit Var N :=
  liftUnitVar v (selectLowBitNoNegCoreUnitDyn P stepsA stepsB wOuter wInner2 hGiPos rMain rScr)

/-- Scratch-sliced `1 + kInner ≤ sUb` `wNegIn`-free single-pass `SELECT` `DynamicCircuit`. -/
noncomputable def selectLowBitNoNegCoreSliceDyn {Var : Type} {N kInner tCore sUb : ℕ}
    {branch10 : Fin (2 ^ 10) → Unitary (2 ^ 58)}
    (P : GenCore145Bundle kInner tCore branch10) (stepsA stepsB : List (RouterStep 23))
    (hs : 1 + kInner ≤ sUb) (v : Var) (wOuter wInner2 : ℕ) (hGiPos : 0 < wInner2)
    (rMain : QRegister (nUB wOuter wInner2 + 11) N) (rScrUb : QRegister sUb N) :
      DynamicCircuit Var N :=
  selectLowBitNoNegCoreDyn P stepsA stepsB v wOuter wInner2 hGiPos rMain
    (rScrUb.compose (QRegister.block 0 (1 + kInner) (by omega)))

@[simp] theorem count_selectLowBitNoNegCoreDyn_toff {Var : Type} {N kInner tCore : ℕ}
    {branch10 : Fin (2 ^ 10) → Unitary (2 ^ 58)}
    (P : GenCore145Bundle kInner tCore branch10) (stepsA stepsB : List (RouterStep 23))
    (v : Var) (wOuter wInner2 : ℕ) (hGiPos : 0 < wInner2)
    (rMain : QRegister (nUB wOuter wInner2 + 11) N) (rScr : QRegister (1 + kInner) N) :
    (selectLowBitNoNegCoreDyn P stepsA stepsB v wOuter wInner2 hGiPos rMain rScr).count .TOFF =
        0 := by
  rw [selectLowBitNoNegCoreDyn, count_liftUnitVar, count_selectLowBitNoNegCoreUnitDyn_toff]

@[simp] theorem count_selectLowBitNoNegCoreSliceDyn_toff {Var : Type} {N kInner tCore sUb : ℕ}
    {branch10 : Fin (2 ^ 10) → Unitary (2 ^ 58)}
    (P : GenCore145Bundle kInner tCore branch10) (stepsA stepsB : List (RouterStep 23))
    (hs : 1 + kInner ≤ sUb) (v : Var) (wOuter wInner2 : ℕ) (hGiPos : 0 < wInner2)
    (rMain : QRegister (nUB wOuter wInner2 + 11) N) (rScrUb : QRegister sUb N) :
    (selectLowBitNoNegCoreSliceDyn P stepsA stepsB hs v wOuter wInner2 hGiPos rMain
      rScrUb).count .TOFF = 0 :=
  count_selectLowBitNoNegCoreDyn_toff P stepsA stepsB v wOuter wInner2 hGiPos rMain _

end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.BellPersistNoNeg
end
