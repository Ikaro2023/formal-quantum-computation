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

public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.ThreeGearBellSuper
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.Inner18Symp14Walk

/-!
# `(wOuter, wInner2)`-Polymorphic `NoNeg + D_neg` Asymmetric `SiZero` SOS & `K ≥ 1` Bell Super-Walk

Establishes `(wOuter, wInner2)`-polymorphic `wNegIn`-free `57`-AND `SELECT` + `D_neg` turnaround SOS
and
`K ≥ 1` Bell-persistent super-walk (`IsValidDNegBit`, `uRefl2_noNegDNeg_congr`, `directDNeg13Dyn`,
`idealPi145SelectPure`, `walkRefl2InvErrLe_noNegDNeg_*`, `cleanTurnaroundWp_dNeg_sandwich`).

## References
- C. Gidney, *Quantum* **2**, 74 (2018), DOI: `10.22331/q-2018-06-18-74`.
- R. Babbush et al., *Phys. Rev. X* **8**, 041015 (2018), DOI: `10.1103/PhysRevX.8.041015`.
- D. W. Berry et al., *Quantum* **3**, 208 (2019), DOI: `10.22331/q-2019-12-02-208`.
- J. Lee et al., *PRX Quantum* **2**, 030305 (2021), DOI: `10.1103/PRXQuantum.2.030305`.
- G. H. Low, V. Kliuchnikov, and L. Schaeffer, *Quantum* **8**, 1375 (2024),
  DOI: `10.22331/q-2024-06-17-1375`.
-/

@[expose] public section

namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.NoNegDNegSOSAndSuperWalk
open QuantumComputation.Specs QuantumComputation.Specs.P450
open Operator QProg Matrix Circuit Real HermitianMat CoherentAlias CleanDyn AliasPrep
open SelectSwapQROM QuantumComputation.Specs QuantumComputation.Specs.P450
open BlockEncodingCore BlockEncodingCircuit
open TopIntegrationBridge Phase2MidSandwich MidReflCtxRetain Cat11CompactPhase2Bridge
open ReordOuter13Bridge ZeroRcHotPrepMid21Fast MobiusOptSubcube163Walk
open CompactTuned162StepZeroCmp20 Pi145SOSPermBridge LowBitPi145Select
open CompactOuter9Bound50Core CompactOuter9Bound50Select OneHotSimulates
open QuantizedFactoredMag30 BellSingletCSwap58 BellPersistCore
open _root_.QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.CompactStepFast176Select
  (pack16)
open BellPersistSuperWalk BellRouter57 BellRouter57Pure
open NoNegSelect57Pure CompactCore145Bundle Select57Slices
open BellSelectNoNegPair BellSuperNoNegWalk TwoGearSuperPhase5
open ThreeGearBellSuper TwoGearQPEPhase5 Phase2FlexBridge
open scoped Matrix BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator Circuit.Notation
local instance (priority := 1000000) instNeZeroTwoPowNoNeg (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩

theorem matrix_eq_of_mulVec_single {n : Type*} [Fintype n] [DecidableEq n]
    {A B : Matrix n n ℂ} (h : ∀ g, A *ᵥ Pi.single g 1 = B *ᵥ Pi.single g 1) : A = B := by
  ext i g
  simpa only [Matrix.mulVec_single_one, Matrix.col_apply] using congrFun (h g) i

/-- Equivalence between `Fin (2 ^ q)` and `BitAssignment q`. -/
abbrev basisBitsEquiv (q : ℕ) : Fin (2 ^ q) ≃ BitAssignment q :=
  (finFunctionFinEquiv (m := 2) (n := q)).symm.trans
    (Equiv.piCongrRight fun _ ↦ ZMod.finEquiv 2)

@[simp] theorem basisBits_symm2 {q : ℕ} (β : BitAssignment q) :
    basisBits q ((basisBitsEquiv q).symm β) = β :=
  (basisBitsEquiv q).apply_symm_apply β

/-! ## Section 1: `D_neg` Diagonal Phase Algebra, `< 149`-Scratch `480-T` Fixup & Spin-Cancel -/
/-- Validity contract for a two-body `D_neg` sign table `dBit xo' b` (`< 126, < 30` & `≥ 126`). -/
def IsValidDNegBit (dBit : Fin (2 ^ 8) → Fin (2 ^ 5) → Bool) : Prop :=
  (∀ (xo' : Fin (2 ^ 8)) (b : Fin (2 ^ 5)), xo'.val < 126 → b.val < 30 →
    dBit xo' b = negInPadded (rcBitsOfXo (pi145XoEquiv xo')) b) ∧
  (∀ (xo' : Fin (2 ^ 8)) (b : Fin (2 ^ 5)), 126 ≤ xo'.val → dBit xo' b = false)
/-- One-hot `128` `D_neg` sign table matching `negInPadded (pi128Equiv ⟨xo', _⟩) b` on `< 126`. -/
def hot128NegBit (xo' : Fin (2 ^ 8)) (b : Fin (2 ^ 5)) : Bool :=
  if h : xo'.val < 126 then negInPadded (pi128Equiv ⟨xo'.val, by omega⟩) b else false
/-- Alias of `hot128NegBit` for downstream `HadW` / one-hot `128` modules. -/
abbrev hot128NegBit2 : Fin (2 ^ 8) → Fin (2 ^ 5) → Bool := hot128NegBit
/-- Flat `13`-bit (`5` `b`-LSBs + `8` `xo'`-MSBs, `idx = 32 * xo' + b`) Boolean phase table. -/
def dNeg13Table (dBit : Fin (2 ^ 8) → Fin (2 ^ 5) → Bool) (idx : ℕ) : Bool :=
  dBit ⟨(idx / 32) % 256, by omega⟩ ⟨idx % 32, by omega⟩
/-- `13`-wire diagonal `D_neg` phase unitary on `(b : 5) ++ (xo' : 8)`. -/
noncomputable def dNeg13Unitary (dBit : Fin (2 ^ 8) → Fin (2 ^ 5) → Bool) : Unitary (2 ^ 13) :=
  SelectSwapQROM.diagPhaseUnitary 13 8192 (dNeg13Table dBit)
@[simp] theorem dNeg13Unitary_mul_self (dBit : Fin (2 ^ 8) → Fin (2 ^ 5) → Bool) :
    dNeg13Unitary dBit * dNeg13Unitary dBit = 1 :=
  SelectSwapQROM.diagPhaseUnitary_mul_self 13 8192 (dNeg13Table dBit)
@[simp] theorem dNeg13Unitary_inv (dBit : Fin (2 ^ 8) → Fin (2 ^ 5) → Bool) :
    (dNeg13Unitary dBit)⁻¹ = dNeg13Unitary dBit :=
  inv_eq_of_mul_eq_one_right (dNeg13Unitary_mul_self dBit)
theorem disjoint_rBUB_rXoUB (wOuter wInner2 : ℕ) :
    ((rMidUB wOuter wInner2).compose (rBLoc wInner2)).DisjointWires ((rOutUB wOuter wInner2).compose
      (rXoLoc wOuter)) :=
  QRegister.disjoint_iff.mpr fun i j h ↦ by
    have hv := congrArg Fin.val h
    have hi := (rBLoc wInner2 i).isLt
    have hj := (rXoLoc wOuter j).isLt
    dsimp [rMidUB, rOutUB, mOutUB, mMidUB] at hv hi hj
    omega
/-- `13`-wire `(b : 5) ++ (xo' : 8)` address register inside `nUB wOuter wInner2`. -/
def rBXo13UB (wOuter wInner2 : ℕ) : QRegister 13 (nUB wOuter wInner2) :=
  ((rMidUB wOuter wInner2).compose (rBLoc wInner2)).concat
    ((rOutUB wOuter wInner2).compose (rXoLoc wOuter)) (disjoint_rBUB_rXoUB wOuter wInner2)
/-- Walk-space `D_neg` unitary on `nUB wOuter wInner2`. -/
noncomputable def dNegUB (wOuter wInner2 : ℕ) (dBit : Fin (2 ^ 8) → Fin (2 ^ 5) → Bool) :
    Unitary (2 ^ nUB wOuter wInner2) := (rBXo13UB wOuter wInner2).embedUnitary (dNeg13Unitary dBit)
/-- Catalyzed walk-space `D_neg` unitary on `nUB wOuter wInner2 + 11`. -/
noncomputable def dNegCat (wOuter wInner2 : ℕ) (dBit : Fin (2 ^ 8) → Fin (2 ^ 5) → Bool) :
    Unitary (2 ^ (nUB wOuter wInner2 + 11)) :=
      (rUBInCat wOuter wInner2 11).embedUnitary (dNegUB wOuter wInner2 dBit)
@[simp] theorem dNegUB_mul_self (wOuter wInner2 : ℕ) (dBit : Fin (2 ^ 8) → Fin (2 ^ 5) → Bool) :
    dNegUB wOuter wInner2 dBit * dNegUB wOuter wInner2 dBit = 1 := by
  rw [dNegUB, ← QRegister.embedUnitary_mul, dNeg13Unitary_mul_self, QRegister.embedUnitary_one]
@[simp] theorem dNegUB_inv (wOuter wInner2 : ℕ) (dBit : Fin (2 ^ 8) → Fin (2 ^ 5) → Bool) :
    (dNegUB wOuter wInner2 dBit)⁻¹ = dNegUB wOuter wInner2 dBit :=
  inv_eq_of_mul_eq_one_right (dNegUB_mul_self wOuter wInner2 dBit)
@[simp] theorem dNegCat_mul_self (wOuter wInner2 : ℕ) (dBit : Fin (2 ^ 8) → Fin (2 ^ 5) → Bool) :
    dNegCat wOuter wInner2 dBit * dNegCat wOuter wInner2 dBit = 1 := by
  rw [dNegCat, ← QRegister.embedUnitary_mul, dNegUB_mul_self, QRegister.embedUnitary_one]
@[simp] theorem dNegCat_inv (wOuter wInner2 : ℕ) (dBit : Fin (2 ^ 8) → Fin (2 ^ 5) → Bool) :
    (dNegCat wOuter wInner2 dBit)⁻¹ = dNegCat wOuter wInner2 dBit :=
  inv_eq_of_mul_eq_one_right (dNegCat_mul_self wOuter wInner2 dBit)
theorem extractIndex_rBXo13UB_val {wOuter wInner2 : ℕ} (k : Fin (2 ^ nUB wOuter wInner2)) :
    ((rBXo13UB wOuter wInner2).extractIndex k).val =
      32 * ((rXoLoc wOuter).extractIndex ((rOutUB wOuter wInner2).extractIndex k)).val +
        ((rBLoc wInner2).extractIndex ((rMidUB wOuter wInner2).extractIndex k)).val := by
  let β := basisBits (nUB wOuter wInner2) k
  have hSplit : ((rBXo13UB wOuter wInner2).extractIndex k).val =
      2 ^ 5 * ((basisBitsEquiv 8).symm
          (fun i ↦ β ((rBXo13UB wOuter wInner2).slice 5 8 (by decide) i))).val +
        ((basisBitsEquiv 5).symm
          (fun i ↦ β ((rBXo13UB wOuter wInner2).slice 0 5 (by decide) i))).val :=
    SelectSwapQROM.localIdx_split_add (s := 5) (k := 8) (rBXo13UB wOuter wInner2) β
  have hOff : (rBXo13UB wOuter wInner2).slice 0 5 (by decide) =
      (rMidUB wOuter wInner2).compose (rBLoc wInner2) :=
    CoherentAlias.qreg_ext fun i ↦ congrArg Fin.val
      ((congrArg (rBXo13UB wOuter wInner2) (Fin.ext (by
        dsimp [QRegister.slice]
        omega))).trans
        (QRegister.concat_apply_left _ _ _ i))
  have hHi : (rBXo13UB wOuter wInner2).slice 5 8 (by decide) =
      (rOutUB wOuter wInner2).compose (rXoLoc wOuter) :=
    CoherentAlias.qreg_ext fun i ↦ congrArg Fin.val
      ((congrArg (rBXo13UB wOuter wInner2) (Fin.ext (by dsimp [QRegister.slice]))).trans
        (QRegister.concat_apply_right _ _ _ i))
  rw [hOff, hHi] at hSplit
  have hB : (basisBitsEquiv 5).symm (fun i ↦ β (((rMidUB wOuter wInner2).compose (rBLoc wInner2))
      i)) =
      (rBLoc wInner2).extractIndex ((rMidUB wOuter wInner2).extractIndex k) :=
    (basisBitsEquiv 5).injective <| funext fun i ↦ by
      rw [Equiv.apply_symm_apply]
      change β (((rMidUB wOuter wInner2).compose (rBLoc wInner2)) i) =
        basisBits 5 ((rBLoc wInner2).extractIndex ((rMidUB wOuter wInner2).extractIndex k)) i
      rw [QRegister.basisBits_extractIndex, QRegister.basisBits_extractIndex]
      rfl
  have hXo : (basisBitsEquiv 8).symm (fun i ↦ β (((rOutUB wOuter wInner2).compose (rXoLoc wOuter))
      i)) =
      (rXoLoc wOuter).extractIndex ((rOutUB wOuter wInner2).extractIndex k) :=
    (basisBitsEquiv 8).injective <| funext fun i ↦ by
      rw [Equiv.apply_symm_apply]
      change β (((rOutUB wOuter wInner2).compose (rXoLoc wOuter)) i) =
        basisBits 8 ((rXoLoc wOuter).extractIndex ((rOutUB wOuter wInner2).extractIndex k)) i
      rw [QRegister.basisBits_extractIndex, QRegister.basisBits_extractIndex]
      rfl
  rw [hB, hXo] at hSplit
  simpa using hSplit
theorem dNegUB_apply_diagonal {wOuter wInner2 : ℕ} (dBit : Fin (2 ^ 8) → Fin (2 ^ 5) → Bool)
    (v : Fin (2 ^ nUB wOuter wInner2) → ℂ) (k : Fin (2 ^ nUB wOuter wInner2)) :
    ((dNegUB wOuter wInner2 dBit).1 *ᵥ v) k =
      (if dBit ((rXoLoc wOuter).extractIndex ((rOutUB wOuter wInner2).extractIndex k))
          ((rBLoc wInner2).extractIndex ((rMidUB wOuter wInner2).extractIndex k))
        then (-1 : ℂ) else 1) * v k := by
  rw [dNegUB, QRegister.embedUnitary_val]
  dsimp only [dNeg13Unitary, SelectSwapQROM.diagPhaseUnitary]
  rw [QRegister.embedMatrix_diagonal_mulVec (rBXo13UB wOuter wInner2) _ v k]
  set xo' := (rXoLoc wOuter).extractIndex ((rOutUB wOuter wInner2).extractIndex k)
  set b := (rBLoc wInner2).extractIndex ((rMidUB wOuter wInner2).extractIndex k)
  have hlt : ((rBXo13UB wOuter wInner2).extractIndex k).val < 8192 :=
    ((rBXo13UB wOuter wInner2).extractIndex k).isLt
  have hTab : dNeg13Table dBit ((rBXo13UB wOuter wInner2).extractIndex k).val = dBit xo' b := by
    dsimp only [dNeg13Table]
    rw [extractIndex_rBXo13UB_val k]
    have hb := b.isLt
    have hxo := xo'.isLt
    exact congrArg₂ dBit
      (Fin.ext (by
        change ((32 * xo'.val + b.val) / 32) % 256 = xo'.val
        omega))
      (Fin.ext (by
        change (32 * xo'.val + b.val) % 32 = b.val
        omega))
  simp only [hlt, true_and, hTab]
theorem dNegUB_mulVec_embedKet {wOuter wInner2 : ℕ} (dBit : Fin (2 ^ 8) → Fin (2 ^ 5) → Bool)
    (ψ : Fin (2 ^ (2 * 58)) → ℂ) (o' : Fin (2 ^ mOutUB wOuter)) (m : Fin (2 ^ mMidUB wInner2)) :
    (dNegUB wOuter wInner2 dBit).1 *ᵥ embedKet ψ o' m =
      (if dBit ((rXoLoc wOuter).extractIndex o') ((rBLoc wInner2).extractIndex m)
        then (-1 : ℂ) else 1) • embedKet ψ o' m := by
  funext k
  rw [dNegUB_apply_diagonal, Pi.smul_apply, smul_eq_mul]
  dsimp [embedKet]
  by_cases h : (rOutUB wOuter wInner2).extractIndex k =
      o' ∧ (rMidUB wOuter wInner2).extractIndex k = m
  · rcases h with ⟨hOut, hMid⟩
    simp only [hOut, hMid, and_self, ↓reduceIte]
  · simp only [h, ↓reduceIte, mul_zero]
theorem embedUnitary_diagPhaseUnitary_comm_muxUnitary {N c t k L : ℕ}
    (rCtrl : QRegister c N) (rTgt : QRegister t N) (hDisj : rCtrl.DisjointWires rTgt)
    (F : Fin (2 ^ c) → Unitary (2 ^ t)) (rIdx : QRegister k N) (P : ℕ → Bool)
    (hIdxTgt : rIdx.DisjointWires rTgt) :
    muxUnitary rCtrl rTgt hDisj F * rIdx.embedUnitary (SelectSwapQROM.diagPhaseUnitary k L P) =
      rIdx.embedUnitary (SelectSwapQROM.diagPhaseUnitary k L P) *
        muxUnitary rCtrl rTgt hDisj F := by
  let d : Fin (2 ^ k) → ℂ := fun idx ↦ if idx.val < L ∧ P idx.val then (-1 : ℂ) else 1
  let D : Operator (2 ^ N) := rIdx.embedMatrix (Matrix.diagonal d)
  have hD (v : Fin (2 ^ N) → ℂ) (g : Fin (2 ^ N)) : (D *ᵥ v) g = d (rIdx.extractIndex g) * v g :=
    QRegister.embedMatrix_diagonal_mulVec rIdx d v g
  have hTerm (x : Fin (2 ^ c)) (v : Fin (2 ^ N) → ℂ) :
      (rCtrl.basisOutcomeProjector x * (rTgt.embedMatrix (F x).1 * D)) *ᵥ v =
        (D * (rCtrl.basisOutcomeProjector x * rTgt.embedMatrix (F x).1)) *ᵥ v := by
    funext g
    simp only [← Matrix.mulVec_mulVec]
    rw [rCtrl.basisOutcomeProjector_mulVec, hD, rCtrl.basisOutcomeProjector_mulVec]
    by_cases hx : rCtrl.extractIndex g = x
    · simp only [hx, ↓reduceIte]
      rw [rTgt.embedMatrix_mulVec_apply, rTgt.embedMatrix_mulVec_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun t' _ ↦ ?_
      change (F x).1 (rTgt.extractIndex g) t' * (D *ᵥ v) (rTgt.replaceIndex g t') =
        d (rIdx.extractIndex g) * ((F x).1 (rTgt.extractIndex g) t' * v (rTgt.replaceIndex g t'))
      rw [hD, rIdx.extractIndex_replaceIndex_of_disjoint rTgt hIdxTgt g t']
      ring
    · simp only [hx, ↓reduceIte, mul_zero]
  apply Subtype.ext
  rw [Submonoid.coe_mul, Submonoid.coe_mul, QRegister.embedUnitary_val]
  dsimp only [SelectSwapQROM.diagPhaseUnitary, muxUnitary]
  refine matrix_eq_of_mulVec_single fun j ↦ ?_
  rw [Matrix.sum_mul, Matrix.mul_sum, Matrix.sum_mulVec, Matrix.sum_mulVec]
  exact Finset.sum_congr rfl fun x _ ↦ by
    simpa only [Matrix.mul_assoc] using hTerm x (Pi.single j 1)
theorem disjoint_rBXo13UB_rSysUB (wOuter wInner2 : ℕ) :
    (rBXo13UB wOuter wInner2).DisjointWires (rSysUB wOuter wInner2) :=
  QRegister.disjoint_iff.mpr fun i j h ↦ by
    by_cases hi : i.val < 5
    · rw [show i = Fin.castAdd 8 ⟨i.val, hi⟩ from Fin.ext rfl,
        rBXo13UB, QRegister.concat_apply_left] at h
      exact (disjoint_rSysUB_rMidUB wOuter wInner2).ne j _ h.symm
    · have hiLt := i.isLt
      rw [show i = Fin.natAdd 5 (⟨i.val - 5, by omega⟩ : Fin 8) from
          Fin.ext (by
            dsimp
            omega),
        rBXo13UB, QRegister.concat_apply_right] at h
      exact (disjoint_rSysUB_rOutUB wOuter wInner2).ne j _ h.symm
theorem selectNoNegGenPureUnitary_commDNegUB (branch10 : Fin (2 ^ 10) → Unitary (2 ^ 58))
    (specA : (Fin 16 → Bool) → State24) (specB : State24 → State24) (wOuter wInner2 : ℕ)
    (dBit : Fin (2 ^ 8) → Fin (2 ^ 5) → Bool) :
    selectNoNegGenPureUnitary branch10 specA specB wOuter wInner2 * dNegUB wOuter wInner2 dBit =
      dNegUB wOuter wInner2 dBit * selectNoNegGenPureUnitary branch10 specA specB wOuter wInner2 :=
  embedUnitary_diagPhaseUnitary_comm_muxUnitary _ _ _ _ _ _ (disjoint_rBXo13UB_rSysUB wOuter
    wInner2)
theorem preservesWiresDNegCat {N : ℕ} (wOuter wInner2 : ℕ) (dBit : Fin (2 ^ 8) → Fin (2 ^ 5) → Bool)
    (rMain : QRegister (nUB wOuter wInner2 + 11) N) (S : Finset (Wire N)) :
    AliasPrep.PreservesWires (rMain.embedUnitary (dNegCat wOuter wInner2 dBit)).1 S := by
  intro i j ⟨w, _, hw⟩
  have hij : i ≠ j := fun h ↦ hw (h ▸ rfl)
  dsimp only [dNegCat, dNegUB]
  rw [← QRegister.embedUnitary_compose, ← QRegister.embedUnitary_compose,
    QRegister.embedUnitary_val]
  dsimp only [dNeg13Unitary, SelectSwapQROM.diagPhaseUnitary]
  have hv := QRegister.embedMatrix_diagonal_mulVec
    ((rMain.compose (rUBInCat wOuter wInner2 11)).compose (rBXo13UB wOuter wInner2))
    (fun idx : Fin (2 ^ 13) ↦ if idx.val < 8192 ∧ dNeg13Table dBit idx.val then (-1 : ℂ) else 1)
    (Pi.single j 1) i
  simpa only [Matrix.mulVec_single_one, Matrix.col_apply, Pi.single_eq_of_ne hij, mul_zero] using hv
/-- Boolean indicator of `126 ≤ xo < 254` (active on `126 ≤ xo < 184` and avoiding `254, 255`). -/
def is1BBool (xo : Fin (2 ^ 8)) : Bool := decide (126 ≤ xo.val ∧ xo.val < 254)
theorem is1BBool_of_lt126 {xo : Fin (2 ^ 8)} (h : xo.val < 126) : is1BBool xo = false :=
  decide_eq_false (by omega)
theorem is1BBool_of_oneBody {xo : Fin (2 ^ 8)} (h126 : 126 ≤ xo.val) (h184 : xo.val < 184) :
    is1BBool xo = true := decide_eq_true ⟨h126, by omega⟩
/-- Walk-space `rXoLoc`-controlled `H` spin-cancellation mux on `sig_in` for `is1BBool`. -/
noncomputable def spinCancelUBMux (wOuter wInner2 : ℕ) : Unitary (2 ^ nUB wOuter wInner2) :=
  muxUnitary ((rOutUB wOuter wInner2).compose (rXoLoc wOuter)) ((rMidUB wOuter wInner2).compose
    (rSigInLoc wInner2))
    (QRegister.disjoint_iff.mpr fun _ _ h ↦ (disjoint_rOutUB_rMidUB wOuter wInner2).ne _ _ h)
    (fun xo' ↦ if is1BBool xo' then (Circuit.H 0).eval else 1)
@[simp] theorem spinCancelUBMux_inv (wOuter wInner2 : ℕ) :
    (spinCancelUBMux wOuter wInner2)⁻¹ = spinCancelUBMux wOuter wInner2 := by
  unfold spinCancelUBMux
  rw [muxUnitary_inv]
  refine congrArg (muxUnitary _ _ _) (funext fun x ↦ ?_)
  cases is1BBool x
  · simp only [Bool.false_eq_true, ↓reduceIte, inv_one]
  · simp only [↓reduceIte, ← Circuit.eval_inverse]
    rfl
@[simp] theorem spinCancelUBMux_mul_self (wOuter wInner2 : ℕ) :
    spinCancelUBMux wOuter wInner2 * spinCancelUBMux wOuter wInner2 = 1 :=
  mul_eq_one_iff_eq_inv.mpr (spinCancelUBMux_inv wOuter wInner2).symm
/-! ## Section 2: `uRefl2` Full-Space Congruence & Invariant-Subspace `WalkRefl2InvErrLe` `δ = 0` -/

open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.StepOuter8Pi145L1
/-- `< 184`-supported `π145` system branch unitary (`1` on `184 ≤ xo'`). -/
noncomputable def idealPi145Branch (wOuter wInner2 : ℕ) (o' : Fin (2 ^ mOutUB wOuter))
    (m : Fin (2 ^ mMidUB wInner2)) : Unitary (2 ^ (2 * 58)) :=
  if ((rXoLoc wOuter).extractIndex o').val < 184 then
    selectBranchUnitary (pi145XoEquiv ((rXoLoc wOuter).extractIndex o'))
      ((rSigOutLoc wOuter).extractIndex o') ((rBLoc wInner2).extractIndex m)
      ((rSigInLoc wInner2).extractIndex m)
  else 1
/-- `< 184`-supported `π145` reference `SELECT` unitary on `nUB wOuter wInner2` (`1` on `184 ≤
xo'`). -/
noncomputable def idealPi145SelectPure (wOuter wInner2 : ℕ) : Unitary (2 ^ nUB wOuter wInner2) :=
  muxUnitary (rAllUB wOuter wInner2) (rSysUB wOuter wInner2) (disjoint_rAllUB_rSysUB wOuter wInner2)
    fun a ↦
    let ⟨xo', so, b, si⟩ := decodeSelectCtrl a
    if xo'.val < 184 then selectBranchUnitary (pi145XoEquiv xo') so b si else 1
theorem selectBranchUnitary_mul_self (xo : Fin (2 ^ 8)) (so : Fin 2)
    (b : Fin (2 ^ 5)) (si : Fin 2) :
    selectBranchUnitary xo so b si * selectBranchUnitary xo so b si = 1 := by
  apply Subtype.ext
  have hInv : (selectBranchUnitary xo so b si).1 * (selectBranchUnitary xo so b si).1ᴴ = 1 := by
    rw [← Matrix.star_eq_conjTranspose]
    exact (selectBranchUnitary xo so b si).2.2
  simpa only [Submonoid.coe_mul, Submonoid.coe_one, selectBranchUnitary_conjTranspose] using hInv
@[simp] theorem idealPi145Branch_mul_self (wOuter wInner2 : ℕ) (o' : Fin (2 ^ mOutUB wOuter))
    (m : Fin (2 ^ mMidUB wInner2)) :
    idealPi145Branch wOuter wInner2 o' m * idealPi145Branch wOuter wInner2 o' m = 1 := by
  dsimp only [idealPi145Branch]
  split_ifs
  · exact selectBranchUnitary_mul_self _ _ _ _
  · exact mul_one 1
theorem idealPi145SelectPure_mulVec_embedKet {wOuter wInner2 : ℕ}
    (ψ : Fin (2 ^ (2 * 58)) → ℂ) (o' : Fin (2 ^ mOutUB wOuter)) (m : Fin (2 ^ mMidUB wInner2)) :
    (idealPi145SelectPure wOuter wInner2).1 *ᵥ embedKet ψ o' m =
      embedKet ((idealPi145Branch wOuter wInner2 o' m).1 *ᵥ ψ) o' m := by
  let a₀ : Fin (2 ^ mAncUB wOuter wInner2) :=
      (splitBlockEquiv (mOutUB wOuter) (mMidUB wInner2)).symm (o', m)
  have ha₀ (g : Fin (2 ^ nUB wOuter wInner2)) (h : (rAllUB wOuter wInner2).extractIndex g ≠ a₀) :
      embedKet ψ o' m g = 0 := by
    dsimp [embedKet]
    by_contra hnz
    have hc : (rOutUB wOuter wInner2).extractIndex g = o' ∧ (rMidUB wOuter wInner2).extractIndex g =
        m := by
      by_contra hc
      rw [ite_eq_right hc] at hnz
      exact hnz rfl
    apply h
    apply (splitBlockEquiv (mOutUB wOuter) (mMidUB wInner2)).injective
    rw [Equiv.apply_symm_apply]
    apply Prod.ext
    · rw [splitBlockEquiv_fst, ← QRegister.extractIndex_compose,
        show (rAllUB wOuter wInner2).compose
          (QRegister.block 0 (mOutUB wOuter) (by
            dsimp [mAncUB]
            omega)) = rOutUB wOuter wInner2 from
          CoherentAlias.qreg_ext fun i ↦ by simp [rAllUB, rOutUB], hc.1]
    · rw [splitBlockEquiv_snd, ← QRegister.extractIndex_compose,
        show (rAllUB wOuter wInner2).compose
          (QRegister.block (mOutUB wOuter) (mMidUB wInner2) (by
            dsimp [mAncUB]
            omega)) = rMidUB wOuter wInner2 from
          CoherentAlias.qreg_ext fun j ↦ by
            dsimp [rAllUB, rMidUB]
            omega, hc.2]
  unfold idealPi145SelectPure
  rw [muxUnitary_mulVec_of_proj _ _ _ _ a₀ _ ha₀, embedMatrix_rSysUB_mulVec_embedKet,
    show decodeSelectCtrl a₀ =
      ((rXoLoc wOuter).extractIndex o', (rSigOutLoc wOuter).extractIndex o',
       (rBLoc wInner2).extractIndex m, (rSigInLoc wInner2).extractIndex m) by simp
         [decodeSelectCtrl, a₀]]
  rfl
theorem selectOnLt184IdealPi145SelectPure (wOuter wInner2 : ℕ) :
    SelectOnLt184 pi145XoEquiv (idealPi145SelectPure wOuter wInner2) := fun ψ o' m hlt ↦ by
  rw [idealPi145SelectPure_mulVec_embedKet, idealPi145Branch, ite_eq_left hlt]
theorem selectBranchUnitary_comm_electronSectorProjector (xo : Fin (2 ^ 8)) (so : Fin 2)
    (b : Fin (2 ^ 5)) (si : Fin 2) (η : ℕ) :
    (selectBranchUnitary xo so b si).1 * electronSectorProjector (2 * 58) η =
      electronSectorProjector (2 * 58) η * (selectBranchUnitary xo so b si).1 := by
  dsimp only [selectBranchUnitary, blockedRowReflectionUnitary]
  rw [smul_mul_assoc, mul_smul_comm]
  refine congrArg (_ • ·) ?_
  split_ifs
  · exact blockedOrbitalReflection_comm_electronSectorProjector2 _ _ η
  · rw [one_mul, mul_one]
theorem idealPi145Branch_comm_electronSectorProjector (wOuter wInner2 : ℕ)
    (o' : Fin (2 ^ mOutUB wOuter)) (m : Fin (2 ^ mMidUB wInner2)) (η : ℕ) :
    (idealPi145Branch wOuter wInner2 o' m).1 * electronSectorProjector (2 * 58) η =
      electronSectorProjector (2 * 58) η * (idealPi145Branch wOuter wInner2 o' m).1 := by
  dsimp only [idealPi145Branch]
  split_ifs
  · exact selectBranchUnitary_comm_electronSectorProjector _ _ _ _ η
  · simp only [Submonoid.coe_one, one_mul, mul_one]
theorem pulledSOSBlockEncodingIdealPi145_fullQuant {wOuter wInner2 : ℕ}
    (prepOutImpl : Unitary (2 ^ mOutUB wOuter))
    (prepMid : Fin (2 ^ 7) → Unitary (2 ^ mMidUB wInner2)) :
    PulledSOSBlockEncoding (mOutUB wOuter) (mMidUB wInner2)
      (fullQuantP450HBlocked prepOutImpl (fun rc ↦ prepMid (pi128Equiv rc))
        (idealPi145Branch wOuter wInner2))
      dfthcLowerBound 97.3864
      (ubDirectXo7PureUnitary prepOutImpl (fun rc ↦ prepMid (pi128Equiv rc))
        (idealPi145SelectPure wOuter wInner2)) :=
  pulledSOSBlockEncoding_ubDirectXo7Pure_fullQuant prepOutImpl
    (fun rc ↦ prepMid (pi128Equiv rc)) (idealPi145SelectPure wOuter wInner2)
    (idealPi145Branch wOuter wInner2) (fun ψ o' m ↦ idealPi145SelectPure_mulVec_embedKet ψ o' m)
theorem agreesOnElectronSectorIdealPi145_fullQuant {wOuter wInner2 : ℕ}
    {H₁ : Operator (2 ^ (2 * 58))} (hH₁ : H₁.IsHermitian)
    (prepOutIdeal prepOutImpl : Unitary (2 ^ mOutUB wOuter))
    (prepMid : Fin (2 ^ 7) → Unitary (2 ^ mMidUB wInner2))
    (hSOS₁ : PulledSOSBlockEncoding (mOutUB wOuter) (mMidUB wInner2) H₁ dfthcLowerBound 97.3864
      (ubDirectXo7PureUnitary prepOutIdeal (fun rc ↦ prepMid (pi128Equiv rc))
        (idealPi145SelectPure wOuter wInner2)))
    {εOut δIn δ_H : ℝ}
    (hL1 : (∑ o' : Fin (2 ^ mOutUB wOuter),
      |Complex.normSq (prepOutImpl.1 o' 0) - Complex.normSq (prepOutIdeal.1 o' 0)|) ≤ εOut)
    (hInner : AgreesOnElectronSector 58 63 H₁ BlockEncodingCore.p450HBlocked δIn)
    (hδ : 2 * 97.3864 * εOut + δIn ≤ δ_H) :
    AgreesOnElectronSector 58 63
      (fullQuantP450HBlocked prepOutImpl (fun rc ↦ prepMid (pi128Equiv rc))
        (idealPi145Branch wOuter wInner2)) BlockEncodingCore.p450HBlocked δ_H :=
  agreesOnElectronSector_fullQuant_of_pulledSOS_and_l1 hH₁ prepOutIdeal prepOutImpl
    (fun rc ↦ prepMid (pi128Equiv rc)) (idealPi145SelectPure wOuter wInner2)
    (idealPi145Branch wOuter wInner2) (fun ψ o' m ↦ idealPi145SelectPure_mulVec_embedKet ψ o' m)
    (fun o' m ↦ idealPi145Branch_comm_electronSectorProjector wOuter wInner2 o' m 63) hSOS₁ hL1
      hInner hδ
theorem selectGenCoreBranch_zero_sign_flip (rBits : (Fin 10 → Bool) → Unitary (2 ^ 58))
    (y₀ y₁ : Fin 12 → Bool) (h10 : ∀ j : Fin 10, y₀ ⟨j.val, by omega⟩ = y₁ ⟨j.val, by omega⟩)
    (hsw : y₀ 10 = y₁ 10) (hy0 : y₀ 11 = false) :
    selectGenCoreBranch 0 rBits y₀ =
      (if y₁ 11 then negOneUnitary (2 * 58) else 1) * selectGenCoreBranch 0 rBits y₁ := by
  have hf : (fun j : Fin 10 ↦ y₀ ⟨j.val, by omega⟩) = fun j : Fin 10 ↦ y₁ ⟨j.val, by omega⟩ :=
    funext h10
  dsimp only [selectGenCoreBranch]
  rw [hf, hsw, hy0]
  generalize (QRegister.block 0 (2 * 58) _).embedUnitary _ *
    ((spinCatSub 0).embedUnitary _ * (QRegister.block 0 (2 * 58) _).embedUnitary _) = core
  cases y₁ 11
  · simp only [Bool.false_eq_true, ↓reduceIte, one_mul]
  · simp only [Bool.false_eq_true, ↓reduceIte, one_mul]
    have hnn : negOneUnitary (2 * 58) * negOneUnitary (2 * 58) = 1 := by
      simpa only [↓reduceIte, Bool.xor_self, Bool.false_eq_true] using
        (ite_negOneUnitary_mul_b (n := 2 * 58) true true)
    rw [← mul_assoc, hnn, one_mul]
theorem select57NoNegPureUnitary_mulVec_twoBody_full {wOuter wInner2 : ℕ} (oddPass : Bool)
    (ψ : Fin (2 ^ (2 * 58)) → ℂ) (o' : Fin (2 ^ mOutUB wOuter)) (m : Fin (2 ^ mMidUB wInner2))
    (hxo' : ((rXoLoc wOuter).extractIndex o').val < 126)
    (hb : ((rBLoc wInner2).extractIndex m).val < 30) :
    let xo' := (rXoLoc wOuter).extractIndex o'
    let b := (rBLoc wInner2).extractIndex m
    let br := selectBranchUnitary (pi145XoEquiv xo')
      ((rSigOutLoc wOuter).extractIndex o') b ((rSigInLoc wInner2).extractIndex m)
    (select57NoNegPureUnitary oddPass wOuter wInner2).1 *ᵥ embedKet ψ o' m =
      (if negInPadded (rcBitsOfXo (pi145XoEquiv xo')) b then (-1 : ℂ) else 1) •
        embedKet (br.1 *ᵥ ψ) o' m := by
  intro xo' b br
  let so := (rSigOutLoc wOuter).extractIndex o'
  let si := (rSigInLoc wInner2).extractIndex m
  set negP := negInPadded (rcBitsOfXo (pi145XoEquiv xo')) b
  have hEq : (select57NoNegPureUnitary oddPass wOuter wInner2).1 *ᵥ embedKet ψ o' m =
      embedKet (((if negP then negOneUnitary (2 * 58) else 1) * br).1 *ᵥ ψ) o' m := by
    refine selectNoNegGenPureUnitary_mulVec_embedKet_eq_of_branch _ _ _ ψ o' m _ ?_
    rw [y12NoNegOf1557_pack15]
    obtain ⟨hf0, hs0, hp0⟩ :=
      y12OfState2457_lt126_parts oddPass xo' (decide (so = 1)) b (decide (si = 1)) false hxo'
    obtain ⟨hfN, hsN, hpN⟩ :=
      y12OfState2457_lt126_parts oddPass xo' (decide (so = 1)) b (decide (si = 1)) negP hxo'
    rw [selectGenCoreBranch_zero_sign_flip _ _
      (y12OfState24 specA57 (specB57 oddPass)
        (pack16 xo' (decide (so = 1)) b (decide (si = 1)) negP))
      (fun j ↦ (congrFun hf0 j).trans (congrFun hfN j).symm) (hs0.trans hsN.symm) hp0,
      hpN, r57Branch_twoBody oddPass xo' so b si negP hxo' hb rfl]
  rw [hEq]
  cases negP
  · simp only [Bool.false_eq_true, ↓reduceIte, one_mul, one_smul]
  · simp only [↓reduceIte, Submonoid.coe_mul]
    rw [show (negOneUnitary (2 * 58)).1 = (-1 : ℂ) • (1 : Operator (2 ^ (2 * 58))) from rfl,
      smul_mul_assoc, one_mul, Matrix.smul_mulVec, embedKet_smul]
theorem dNegUB_mulSelect57NoNegPureUnitary_twoBody {wOuter wInner2 : ℕ}
    {dBit : Fin (2 ^ 8) → Fin (2 ^ 5) → Bool} (hd : IsValidDNegBit dBit) (oddPass : Bool)
    (ψ : Fin (2 ^ (2 * 58)) → ℂ) (o' : Fin (2 ^ mOutUB wOuter)) (m : Fin (2 ^ mMidUB wInner2))
    (hxo' : ((rXoLoc wOuter).extractIndex o').val < 126)
    (hb : ((rBLoc wInner2).extractIndex m).val < 30) :
    let br := selectBranchUnitary (pi145XoEquiv ((rXoLoc wOuter).extractIndex o'))
      ((rSigOutLoc wOuter).extractIndex o') ((rBLoc wInner2).extractIndex m)
      ((rSigInLoc wInner2).extractIndex m)
    ((dNegUB wOuter wInner2 dBit * select57NoNegPureUnitary oddPass wOuter wInner2).1 *ᵥ embedKet ψ
        o' m =
        embedKet (br.1 *ᵥ ψ) o' m) ∧
      ((select57NoNegPureUnitary oddPass wOuter wInner2 * dNegUB wOuter wInner2 dBit).1 *ᵥ embedKet
        ψ o' m =
        embedKet (br.1 *ᵥ ψ) o' m) := by
  intro br
  have h1 : (dNegUB wOuter wInner2 dBit * select57NoNegPureUnitary oddPass wOuter wInner2).1 *ᵥ
      embedKet ψ o' m = embedKet (br.1 *ᵥ ψ) o' m := by
    rw [Submonoid.coe_mul, ← Matrix.mulVec_mulVec,
      select57NoNegPureUnitary_mulVec_twoBody_full oddPass ψ o' m hxo' hb,
      Matrix.mulVec_smul, dNegUB_mulVec_embedKet, smul_smul, hd.1 _ _ hxo' hb]
    dsimp only [br]
    cases negInPadded (rcBitsOfXo (pi145XoEquiv ((rXoLoc wOuter).extractIndex o')))
      ((rBLoc wInner2).extractIndex m) <;>
      simp only [Bool.false_eq_true, ↓reduceIte, mul_one, neg_mul_neg, one_smul]
  refine ⟨h1, ?_⟩
  rw [select57NoNegPureUnitary, selectNoNegGenPureUnitary_commDNegUB _ _ _ wOuter wInner2 dBit]
  exact h1
/-- Spin-factored inner preparation: `prepMid rc` factors into `H` on `rSigInLoc wInner2` times
core. -/
def PrepMidSpinFactored {wInner2 : ℕ} (prepMid : Fin (2 ^ 7) → Unitary (2 ^ mMidUB wInner2))
    : Prop :=
  ∃ core : Fin (2 ^ 7) → Unitary (2 ^ (5 + wInner2)), ∀ rc,
    prepMid rc = (rSigInLoc wInner2).embedUnitary (Circuit.H 0).eval *
      (QRegister.block 0 (5 + wInner2) (by
        dsimp [mMidUB]
        omega)).embedUnitary (core rc)
/-- Asymmetric `SiZero` inner preparation mux (`spinCancelUBMux * prepMidDirectXo7MuxUnitary`). -/
noncomputable abbrev asymMidMux (wOuter wInner2 : ℕ)
    (prepMid : Fin (2 ^ 7) → Unitary (2 ^ mMidUB wInner2)) : Unitary (2 ^ nUB wOuter wInner2) :=
  spinCancelUBMux wOuter wInner2 *
    prepMidDirectXo7MuxUnitary wOuter wInner2 (fun rc ↦ prepMid (pi128Equiv rc))
/-- Effective `mMidUB wInner2` branch unitary applied by `asymMidMux wOuter wInner2 prepMid` at
`o'`. -/
noncomputable def asymMidBranch {wOuter wInner2 : ℕ}
    (prepMid : Fin (2 ^ 7) → Unitary (2 ^ mMidUB wInner2)) (o' : Fin (2 ^ mOutUB wOuter)) :
    Unitary (2 ^ mMidUB wInner2) :=
  (if is1BBool ((rXoLoc wOuter).extractIndex o') then (rSigInLoc wInner2).embedUnitary (Circuit.H
   0).eval
   else 1) * prepMid (pi128Equiv ((rXo7Loc wOuter).extractIndex o'))
theorem pi128Equiv_lt126_of_lt126 (rc : Fin (2 ^ 7)) (hrc : rc.val < 126) :
    (pi128Equiv rc).val < 126 := by
  by_contra hge
  have h128 := (pi128Equiv rc).isLt
  rcases (show (pi128Equiv rc).val = 126 ∨ (pi128Equiv rc).val = 127 by omega) with h | h
  · exact absurd (congrArg Fin.val (pi128Equiv.injective
      ((Fin.ext h).trans pi128Equiv_hfix126.1.symm))) (by
      dsimp
      omega)
  · exact absurd (congrArg Fin.val (pi128Equiv.injective
      ((Fin.ext h).trans pi128Equiv_hfix126.2.symm))) (by
      dsimp
      omega)
theorem sum_smul_embedMatrix_rMidUB_embedKet {wOuter wInner2 : ℕ}
    (A B : Operator (2 ^ mMidUB wInner2))
    (ψ : Fin (2 ^ (2 * 58)) → ℂ) (o' : Fin (2 ^ mOutUB wOuter)) (m : Fin (2 ^ mMidUB wInner2)) :
    (∑ x, B x m • ((rMidUB wOuter wInner2).embedMatrix A *ᵥ embedKet ψ o' x)) =
      (rMidUB wOuter wInner2).embedMatrix (A * B) *ᵥ embedKet ψ o' m := by
  have hs (x : Fin (2 ^ mMidUB wInner2)) :
      B x m • ((rMidUB wOuter wInner2).embedMatrix A *ᵥ embedKet ψ o' x) =
        (rMidUB wOuter wInner2).embedMatrix A *ᵥ (B x m • embedKet ψ o' x) :=
    (Matrix.mulVec_smul _ _ _).symm
  rw [Finset.sum_congr rfl fun x _ ↦ hs x, ← Matrix.mulVec_sum,
    ← embedMatrix_rMidUB_mulVec_embedKet, Matrix.mulVec_mulVec, ← QRegister.embedMatrix_mul]
theorem spinCancelUBMux_mulVec_embedKet {wOuter wInner2 : ℕ}
    (ψ : Fin (2 ^ (2 * 58)) → ℂ) (o' : Fin (2 ^ mOutUB wOuter)) (m : Fin (2 ^ mMidUB wInner2)) :
    (spinCancelUBMux wOuter wInner2).1 *ᵥ embedKet ψ o' m = (rMidUB wOuter wInner2).embedMatrix
      (if is1BBool ((rXoLoc wOuter).extractIndex o') then
        (rSigInLoc wInner2).embedUnitary (Circuit.H 0).eval else 1).1 *ᵥ embedKet ψ o' m := by
  have hxo (g : Fin (2 ^ nUB wOuter wInner2)) (hne : ((rOutUB wOuter wInner2).compose (rXoLoc
      wOuter)).extractIndex g
      ≠ (rXoLoc wOuter).extractIndex o') : embedKet ψ o' m g = 0 := by
    dsimp [embedKet]
    by_cases hc : (rOutUB wOuter wInner2).extractIndex g =
        o' ∧ (rMidUB wOuter wInner2).extractIndex g = m
    · exact absurd (by rw [QRegister.extractIndex_compose, hc.1]) hne
    · rw [ite_eq_right hc]
  unfold spinCancelUBMux
  rw [muxUnitary_mulVec_of_proj _ _ _ _ ((rXoLoc wOuter).extractIndex o') _ hxo]
  cases is1BBool ((rXoLoc wOuter).extractIndex o')
  · simp only [Bool.false_eq_true, ↓reduceIte, Submonoid.coe_one, QRegister.embedMatrix_one]
  · simp only [↓reduceIte, QRegister.embedUnitary_val, QRegister.embedMatrix_compose]
theorem asymMidMux_mulVec_embedKet {wOuter wInner2 : ℕ}
    (prepMid : Fin (2 ^ 7) → Unitary (2 ^ mMidUB wInner2))
    (ψ : Fin (2 ^ (2 * 58)) → ℂ) (o' : Fin (2 ^ mOutUB wOuter)) (m : Fin (2 ^ mMidUB wInner2)) :
    (asymMidMux wOuter wInner2 prepMid).1 *ᵥ embedKet ψ o' m =
      (rMidUB wOuter wInner2).embedMatrix (asymMidBranch prepMid o').1 *ᵥ embedKet ψ o' m := by
  rw [asymMidMux, Submonoid.coe_mul, ← Matrix.mulVec_mulVec,
    prepMidDirectXo7Mux_mulVec_embedKet_loc, Matrix.mulVec_sum]
  have hs (x : Fin (2 ^ mMidUB wInner2)) :
      (spinCancelUBMux wOuter wInner2).1 *ᵥ
        (((prepMid (pi128Equiv ((rXo7Loc wOuter).extractIndex o'))).1 x m) • embedKet ψ o' x) =
      ((prepMid (pi128Equiv ((rXo7Loc wOuter).extractIndex o'))).1 x m) •
        ((rMidUB wOuter wInner2).embedMatrix
          (if is1BBool ((rXoLoc wOuter).extractIndex o') then
            (rSigInLoc wInner2).embedUnitary (Circuit.H 0).eval else 1).1 *ᵥ embedKet ψ o' x) := by
    rw [Matrix.mulVec_smul, spinCancelUBMux_mulVec_embedKet]
  rw [Finset.sum_congr rfl fun x _ ↦ hs x, sum_smul_embedMatrix_rMidUB_embedKet]
  rfl
theorem asymMidMux_inv_mulVec_embedKet {wOuter wInner2 : ℕ}
    (prepMid : Fin (2 ^ 7) → Unitary (2 ^ mMidUB wInner2))
    (ψ : Fin (2 ^ (2 * 58)) → ℂ) (o' : Fin (2 ^ mOutUB wOuter)) (m : Fin (2 ^ mMidUB wInner2)) :
    ((asymMidMux wOuter wInner2 prepMid)⁻¹).1 *ᵥ embedKet ψ o' m =
      (rMidUB wOuter wInner2).embedMatrix ((asymMidBranch prepMid o')⁻¹).1 *ᵥ embedKet ψ o' m := by
  rw [asymMidMux, _root_.mul_inv_rev, spinCancelUBMux_inv,
    show (prepMidDirectXo7MuxUnitary wOuter wInner2 fun rc ↦ prepMid (pi128Equiv rc))⁻¹ =
      prepMidDirectXo7MuxUnitary wOuter wInner2 (fun rc ↦ (prepMid (pi128Equiv rc))⁻¹) from
      muxUnitary_inv _ _ _ _, Submonoid.coe_mul, ← Matrix.mulVec_mulVec,
    spinCancelUBMux_mulVec_embedKet, embedMatrix_rMidUB_mulVec_embedKet, Matrix.mulVec_sum]
  let S_c : Unitary (2 ^ mMidUB wInner2) :=
    if is1BBool ((rXoLoc wOuter).extractIndex o') then
      (rSigInLoc wInner2).embedUnitary (Circuit.H 0).eval else 1
  have hs (x : Fin (2 ^ mMidUB wInner2)) :
      (prepMidDirectXo7MuxUnitary wOuter wInner2 fun rc ↦ (prepMid (pi128Equiv rc))⁻¹).1 *ᵥ
        (S_c.1 x m • embedKet ψ o' x) =
      S_c.1 x m • ((rMidUB wOuter wInner2).embedMatrix
        ((prepMid (pi128Equiv ((rXo7Loc wOuter).extractIndex o')))⁻¹).1 *ᵥ embedKet ψ o' x) := by
    rw [Matrix.mulVec_smul, prepMidDirectXo7Mux_mulVec_embedKet_loc,
      embedMatrix_rMidUB_mulVec_embedKet]
  have hInv_3 : S_c⁻¹ = S_c := by
    dsimp only [S_c]
    cases is1BBool ((rXoLoc wOuter).extractIndex o')
    · simp only [Bool.false_eq_true, ↓reduceIte, inv_one]
    · simp only [↓reduceIte, ← QRegister.embedUnitary_inv, ← Circuit.eval_inverse]
      rfl
  rw [Finset.sum_congr rfl fun x _ ↦ hs x, sum_smul_embedMatrix_rMidUB_embedKet,
    asymMidBranch, _root_.mul_inv_rev]
  change _ = (rMidUB wOuter wInner2).embedMatrix
      ((prepMid (pi128Equiv ((rXo7Loc wOuter).extractIndex o')))⁻¹ * S_c⁻¹).1 *ᵥ _
  rw [hInv_3]
  rfl
theorem asymMidBranch_of_lt126 {wOuter wInner2 : ℕ}
    (prepMid : Fin (2 ^ 7) → Unitary (2 ^ mMidUB wInner2))
    (o' : Fin (2 ^ mOutUB wOuter)) (hxo' : ((rXoLoc wOuter).extractIndex o').val < 126) :
    asymMidBranch prepMid o' = prepMid (pi128Equiv ((rXo7Loc wOuter).extractIndex o')) := by
  rw [asymMidBranch, is1BBool_of_lt126 hxo', ite_eq_right Bool.false_ne_true, one_mul]
theorem asymMidBranchZero_of_oneBody {wOuter wInner2 : ℕ}
    {prepMid : Fin (2 ^ 7) → Unitary (2 ^ mMidUB wInner2)} (hSpin : PrepMidSpinFactored prepMid)
    (o' : Fin (2 ^ mOutUB wOuter)) (h126 : 126 ≤ ((rXoLoc wOuter).extractIndex o').val)
    (h184 : ((rXoLoc wOuter).extractIndex o').val < 184)
    (m' : Fin (2 ^ mMidUB wInner2)) (hnz : (asymMidBranch prepMid o').1 m' 0 ≠ 0) :
    (rSigInLoc wInner2).extractIndex m' = 0 := by
  obtain ⟨core, hcore⟩ := hSpin
  have hHH : (Circuit.H (0 : Wire 1)).eval * (Circuit.H 0).eval = 1 :=
    mul_eq_one_iff_eq_inv.mpr (Circuit.eval_inverse (Circuit.H 0))
  let rCore : QRegister (5 + wInner2) (mMidUB wInner2) :=
    QRegister.block 0 (5 + wInner2) (by
      dsimp [mMidUB]
      omega)
  have hBr : asymMidBranch prepMid o' =
      rCore.embedUnitary (core (pi128Equiv ((rXo7Loc wOuter).extractIndex o'))) := by
    rw [asymMidBranch, is1BBool_of_oneBody h126 h184, ite_eq_left rfl, hcore, ← mul_assoc,
      ← QRegister.embedUnitary_mul, hHH, QRegister.embedUnitary_one, one_mul]
  rw [hBr] at hnz
  have hDisj : rCore.DisjointWires (rSigInLoc wInner2) := QRegister.disjoint_iff.mpr fun i _ h ↦ by
    have hv := congrArg Fin.val h
    have := i.isLt
    dsimp only [rCore, rSigInLoc, QRegister.block_apply_val] at hv
    omega
  have hComm := rCore.embedMatrix_comm_of_disjoint (rSigInLoc wInner2) hDisj
    (core (pi128Equiv ((rXo7Loc wOuter).extractIndex o'))).1 (compProj 0)
  by_contra hne
  have hProj0 : ((rSigInLoc wInner2).basisOutcomeProjector 0 *ᵥ
      ((rCore.embedUnitary (core (pi128Equiv ((rXo7Loc wOuter).extractIndex o')))).1 *ᵥ
        Pi.single 0 1)) m' = 0 := by
    rw [(rSigInLoc wInner2).basisOutcomeProjector_mulVec, ite_eq_right hne]
  have h00 : (rSigInLoc wInner2).basisOutcomeProjector 0 *ᵥ
      (Pi.single 0 1 : Fin (2 ^ mMidUB wInner2) → ℂ) =
      Pi.single 0 1 := by
    ext g
    rw [(rSigInLoc wInner2).basisOutcomeProjector_mulVec]
    by_cases hg : g = 0
    · subst hg
      have hex0 : (rSigInLoc wInner2).extractIndex 0 = 0 :=
        (basisBitsEquiv 1).injective <| funext fun i ↦ by
          change basisBits 1 _ i = basisBits 1 0 i
          rw [(rSigInLoc wInner2).basisBits_extractIndex, CoherentAlias.basisBits_zero_apply,
            CoherentAlias.basisBits_zero_apply]
      rw [ite_eq_left hex0]
    · rw [Pi.single_eq_of_ne hg, ite_self]
  dsimp only [QRegister.basisOutcomeProjector] at hProj0 h00
  rw [QRegister.embedUnitary_val, Matrix.mulVec_mulVec _ _ _, ← hComm, ← Matrix.mulVec_mulVec, h00,
    Matrix.mulVec_single_one, Matrix.col_apply] at hProj0
  exact hnz hProj0
theorem single_eq_embedKet {wOuter wInner2 : ℕ} (g : Fin (2 ^ nUB wOuter wInner2)) :
    (Pi.single g 1 : Fin (2 ^ nUB wOuter wInner2) → ℂ) =
      embedKet (Pi.single ((rSysUB wOuter wInner2).extractIndex g) (1 : ℂ) : Fin (2 ^ (2 * 58)) → ℂ)
        ((rOutUB wOuter wInner2).extractIndex g) ((rMidUB wOuter wInner2).extractIndex g) := by
  ext g'
  dsimp only [embedKet]
  by_cases h : g' = g
  · subst h
    simp only [and_self, ↓reduceIte, Pi.single_eq_same]
  · rw [Pi.single_eq_of_ne h]
    by_cases hc : (rOutUB wOuter wInner2).extractIndex g' = (rOutUB wOuter wInner2).extractIndex g ∧
        (rMidUB wOuter wInner2).extractIndex g' = (rMidUB wOuter wInner2).extractIndex g
    · rw [ite_eq_left hc]
      have hne : (rSysUB wOuter wInner2).extractIndex g' ≠ (rSysUB wOuter wInner2).extractIndex g :=
          fun hs ↦
        h <| (basisBitsEquiv (nUB wOuter wInner2)).injective <| funext fun q ↦ by
          change basisBits (nUB wOuter wInner2) g' q = basisBits (nUB wOuter wInner2) g q
          by_cases hq1 : q.val < 2 * 58
          · rw [show q = (rSysUB wOuter wInner2) ⟨q.val, hq1⟩ from Fin.ext (by simp [rSysUB]),
              ← QRegister.basisBits_extractIndex, ← QRegister.basisBits_extractIndex, hs]
          · by_cases hq2 : q.val < 2 * 58 + mOutUB wOuter
            · rw [show q = (rOutUB wOuter wInner2) ⟨q.val - 2 * 58, by omega⟩ from
                Fin.ext (by
                  dsimp [rOutUB]
                  omega),
                ← QRegister.basisBits_extractIndex, ← QRegister.basisBits_extractIndex, hc.1]
            · have hqLt := q.isLt
              rw [show q = (rMidUB wOuter wInner2)
                  ⟨q.val - (2 * 58 + mOutUB wOuter), by
                    dsimp [nUB, mAncUB] at hqLt
                    omega⟩
                from Fin.ext (by
                  dsimp [rMidUB, mAncUB]
                  omega),
                ← QRegister.basisBits_extractIndex, ← QRegister.basisBits_extractIndex, hc.2]
      rw [Pi.single_apply, ite_eq_right hne]
    · rw [ite_eq_right hc]
/-- Catalyzed single-step asymmetric `NoNeg + D_neg` reflection `uRefl2` on `nUB wOuter wInner2 +
11`. -/
noncomputable abbrev asymURefl2 {wOuter wInner2 : ℕ} (prepOutImpl : Unitary (2 ^ mOutUB wOuter))
    (prepMid : Fin (2 ^ 7) → Unitary (2 ^ mMidUB wInner2)) (dBit : Fin (2 ^ 8) → Fin (2 ^ 5) → Bool)
    (sF sB : Unitary (2 ^ (nUB wOuter wInner2 + 11))) :
    Unitary (2 ^ walkCatWidth 11 (mOutUB wOuter) (mMidUB wInner2)) :=
  QubitisedWalk.reflPulledPair (inMidWalkCat 11 (mOutUB wOuter) (mMidUB wInner2))
    (ubCustomMuxCatUnitary (asymMidMux wOuter wInner2 prepMid) prepOutImpl (dNegCat wOuter wInner2
      dBit * sF))
    (ubCustomMuxCatUnitary (asymMidMux wOuter wInner2 prepMid) prepOutImpl
      (sB * dNegCat wOuter wInner2 dBit)⁻¹)⁻¹
theorem conj_rMidUB_mulVec_embedKet_const_branch {wOuter wInner2 : ℕ}
    (B_mid : Unitary (2 ^ mMidUB wInner2)) (S : Unitary (2 ^ nUB wOuter wInner2))
    (V : Unitary (2 ^ (2 * 58)))
    (ψ : Fin (2 ^ (2 * 58)) → ℂ) (o' : Fin (2 ^ mOutUB wOuter))
    (hS : ∀ m', B_mid.1 m' 0 ≠ 0 → S.1 *ᵥ embedKet ψ o' m' = embedKet (V.1 *ᵥ ψ) o' m') :
    (rMidUB wOuter wInner2).embedMatrix (B_mid⁻¹).1 *ᵥ
      (S.1 *ᵥ ((rMidUB wOuter wInner2).embedMatrix B_mid.1 *ᵥ embedKet ψ o' 0)) =
      embedKet (V.1 *ᵥ ψ) o' 0 := by
  have hBB : (B_mid⁻¹).1 * B_mid.1 = 1 := congrArg Subtype.val (inv_mul_cancel B_mid)
  rw [embedMatrix_rMidUB_mulVec_embedKet, Matrix.mulVec_sum, Matrix.mulVec_sum]
  have hterm (m' : Fin (2 ^ mMidUB wInner2)) :
      (rMidUB wOuter wInner2).embedMatrix (B_mid⁻¹).1 *ᵥ
        (S.1 *ᵥ (B_mid.1 m' 0 • embedKet ψ o' m')) =
      (rMidUB wOuter wInner2).embedMatrix (B_mid⁻¹).1 *ᵥ
        (B_mid.1 m' 0 • embedKet (V.1 *ᵥ ψ) o' m') := by
    by_cases hnz : B_mid.1 m' 0 = 0
    · simp only [hnz, zero_smul, Matrix.mulVec_zero]
    · rw [Matrix.mulVec_smul, hS m' hnz]
  rw [Finset.sum_congr rfl fun m' _ ↦ hterm m', ← Matrix.mulVec_sum,
    ← embedMatrix_rMidUB_mulVec_embedKet, Matrix.mulVec_mulVec, ← QRegister.embedMatrix_mul,
    hBB, QRegister.embedMatrix_one, Matrix.one_mulVec]
theorem selectBranchUnitary_oneBody0 {xo : Fin (2 ^ 8)} (hxo : xo.val < 58)
    (so : Fin 2) (b : Fin (2 ^ 5)) : selectBranchUnitary xo so b 0 = 1 := by
  apply Subtype.ext
  have his1 : isOneBodyXo xo = true := decide_eq_true hxo
  have hneg : negPhaseOf xo b 0 = false := by simp [negPhaseOf, his1]
  have hen : enROf xo b 0 = false := by simp [enROf, his1]
  change (if negPhaseOf xo b 0 then (-1 : ℂ) else 1) • (if enROf xo b 0 then
    (blockedRowReflectionUnitary (rowIdxOf xo b) (sigSelOf xo so 0)).1 else 1) = 1
  rw [hneg, hen, ite_eq_right Bool.false_ne_true, ite_eq_right Bool.false_ne_true, one_smul]
theorem selectBranchUnitary_oneBody1 {xo : Fin (2 ^ 8)} (hxo : xo.val < 58)
    (so : Fin 2) (b : Fin (2 ^ 5)) :
    selectBranchUnitary xo so b 1 = selectBranchUnitary xo so 0 1 := by
  apply Subtype.ext
  have his1 : isOneBodyXo xo = true := decide_eq_true hxo
  have hneg : negPhaseOf xo b 1 = negPhaseOf xo 0 1 := by simp [negPhaseOf, his1]
  have hen : enROf xo b 1 = enROf xo 0 1 := by simp [enROf, his1]
  have hrow : rowIdxOf xo b = rowIdxOf xo 0 := by
    dsimp only [rowIdxOf]
    rw [dite_eq_left hxo, dite_eq_left hxo]
  change (if negPhaseOf xo b 1 then (-1 : ℂ) else 1) • (if enROf xo b 1 then
    (blockedRowReflectionUnitary (rowIdxOf xo b) (sigSelOf xo so 1)).1 else 1) = _
  rw [hneg, hen, hrow]
  rfl
@[simp] theorem idealPi145SelectPure_mul_self (wOuter wInner2 : ℕ) :
    idealPi145SelectPure wOuter wInner2 * idealPi145SelectPure wOuter wInner2 = 1 :=
  Subtype.ext <| matrix_eq_of_mulVec_single fun g ↦ by
    rw [single_eq_embedKet g, Submonoid.coe_mul, ← Matrix.mulVec_mulVec,
      idealPi145SelectPure_mulVec_embedKet, idealPi145SelectPure_mulVec_embedKet,
      Matrix.mulVec_mulVec, ← Submonoid.coe_mul, idealPi145Branch_mul_self]
    simp only [Submonoid.coe_one, Matrix.one_mulVec]
@[simp]
theorem balRefSelectPureUnitary_mul_self (σ : Equiv.Perm (Fin (2 ^ 8))) (wOuter wInner2 : ℕ) :
    balRefSelectPureUnitary σ wOuter wInner2 * balRefSelectPureUnitary σ wOuter wInner2 = 1 :=
  Subtype.ext <| matrix_eq_of_mulVec_single fun g ↦ by
    rw [single_eq_embedKet g, Submonoid.coe_mul, ← Matrix.mulVec_mulVec,
      balRefSelectPureUnitary_mulVec_embedKet, balRefSelectPureUnitary_mulVec_embedKet,
      Matrix.mulVec_mulVec, ← Submonoid.coe_mul, selectBranchUnitary_mul_self]
    simp only [Submonoid.coe_one, Matrix.one_mulVec]
theorem symHalfStep_ideal_eq_balRef_of_lt184 {wOuter wInner2 : ℕ}
    (prepMid : Fin (2 ^ 7) → Unitary (2 ^ mMidUB wInner2)) (ψ : Fin (2 ^ (2 * 58)) → ℂ)
    (o' : Fin (2 ^ mOutUB wOuter)) (m : Fin (2 ^ mMidUB wInner2))
    (h184 : ((rXoLoc wOuter).extractIndex o').val < 184) :
    let M_s := prepMidDirectXo7MuxUnitary wOuter wInner2 (fun rc ↦ prepMid (pi128Equiv rc))
    (M_s⁻¹ * idealPi145SelectPure wOuter wInner2 * M_s).1 *ᵥ embedKet ψ o' m =
      (M_s⁻¹ * balRefSelectPureUnitary pi145XoEquiv wOuter wInner2 * M_s).1 *ᵥ embedKet ψ o' m := by
  intro M_s
  simp only [Submonoid.coe_mul, ← Matrix.mulVec_mulVec]
  refine congrArg (M_s⁻¹).1.mulVec ?_
  rw [prepMidDirectXo7Mux_mulVec_embedKet_loc, Matrix.mulVec_sum, Matrix.mulVec_sum]
  refine Finset.sum_congr rfl fun m' _ ↦ ?_
  rw [Matrix.mulVec_smul, Matrix.mulVec_smul,
    selectOnLt184IdealPi145SelectPure wOuter wInner2 ψ o' m' h184,
    balRefSelectPureUnitary_mulVec_embedKet]
end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.NoNegDNegSOSAndSuperWalk
end
