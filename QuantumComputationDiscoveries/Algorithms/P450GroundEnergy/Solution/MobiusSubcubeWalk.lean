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

public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.ReordOuter13Bridge
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.ZeroRcHotPrepMid21Fast
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.Mobius126OneHot
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.SympAnfQrom21
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.XMeasUnload21

/-!
# `162`-Step Symplectic Subcube Walk (`MobiusSubcubeWalk`)

Consolidates the `wOuter = 13` outer-`PREP` helpers (`OptU2Grover184PrepOut13`), the `162`-step
symplectic inner `PREP_mid` helpers (`MobiusOptSubcube163Walk`, `744 T` forward load via
`SympAnfQrom21`), and QROM-unloader walk reflection helpers (`0 TOFF`, `155 ≤ sUb`),
supporting both `ReordSelectSpec` and `ReordActiveSelectSpec`.

## References
- R. Babbush *et al.*, *Phys. Rev. X* **8**, 041015 (2018), DOI: 10.1103/PhysRevX.8.041015.
- C. Gidney, *Quantum* **2**, 74 (2018), DOI: 10.22331/q-2018-06-18-74.
- D. W. Berry *et al.*, *Quantum* **3**, 208 (2019), DOI: 10.22331/q-2019-12-02-208.
- G. H. Low, V. Kliuchnikov, and L. Schaeffer, *Quantum* **8**, 1375 (2024), arXiv:1812.00954.
-/

set_option exponentiation.threshold 512

@[expose] public section

namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.OptU2Grover184PrepOut13
open QuantumComputation.Specs QuantumComputation.Specs.P450
open Operator QProg Matrix HermitianMat Real QuantumComputation.Specs
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution
open QuantumComputation.Specs.P450 QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution
open CoherentAlias
open BlockEncodingCore BlockEncodingCircuit
open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator BigOperators Circuit.Notation
local instance (priority := 1000000) instNeZeroTwoPow (k : ℕ) : NeZero (2 ^ k) :=
  ⟨Nat.pos_iff_ne_zero.mp (by positivity)⟩

private theorem cond_blt_eq {α : Type*} (a b : ℕ) (t f : α) :
    cond (Nat.blt a b) t f = if a < b then t else f := by
  cases h : Nat.blt a b
  · have hnl : ¬ a < b := fun hlt ↦ Bool.false_ne_true (h.symm.trans (Nat.blt_eq.mpr hlt))
    rw [Bool.cond_false, ite_eq_right hnl]
  · rw [Bool.cond_true, ite_eq_left (Nat.blt_eq.mp h)]

private theorem cond_beq_eq {α : Type*} (a b : ℕ) (t f : α) :
    cond (Nat.beq a b) t f = if a = b then t else f := by
  cases h : Nat.beq a b
  · have hne : ¬ a = b := fun heq ↦ Bool.false_ne_true (h.symm.trans (Nat.beq_eq.mpr heq))
    rw [Bool.cond_false, ite_eq_right hne]
  · rw [Bool.cond_true, ite_eq_left (Nat.beq_eq.mp h)]

private theorem sumAltPairs_unpackOuter_eq (x : ℕ) (xs : List ℕ) (j : ℕ) :
    OuterWeights.sumAltPairs x (OuterWeights.unpackAltPairs 256 184 1024 xs j) =
      OuterWeights.sumWithIdx (OuterWeights.outerAltTerm x) xs j := by
  induction xs generalizing j with
  | nil => rfl
  | cons raw rest ih =>
      simp only [OuterWeights.unpackAltPairs, OuterWeights.sumAltPairs, OuterWeights.sumWithIdx,
        OuterWeights.outerAltTerm, ih]
      cases Nat.beq (cond (Nat.blt (raw % 256) 184) (raw % 256) j) x <;> simp

/-- Single-pass kernel check that `pList` has length `184` and unpacks via
`OuterWeights.unpackOuterEntry`
to an exact `184`-item `10`-bit alias table for `wFast`. -/
def checkOuterPackedWeights (wFast : ℕ → ℕ) (pList : List ℕ) : Bool :=
  let pairs := OuterWeights.unpackAltPairs 256 184 1024 pList 0
  Nat.beq pList.length 184 &&
  OuterWeights.allWithIdx (fun x raw ↦
    Nat.beq ((raw / 256) % 1024 + OuterWeights.sumAltPairs x pairs) (wFast x)) pList 0

/-- Generic soundness bridge from `checkOuterPackedWeights wFast arr.toList = true` to
`CoherentAlias.IsValidAliasTable 184 10 wOut`. -/
theorem isValidAliasTable_of_checkOuterPacked (arr : Array ℕ) (wFast : ℕ → ℕ)
    (wOut : Fin 184 → ℕ) (hw : ∀ x : Fin 184, wFast x.val = wOut x)
    (hchk : checkOuterPackedWeights wFast arr.toList = true) :
    let tbl : Fin 184 → OuterWeights.AliasEntry 184 := fun i ↦ OuterWeights.unpackOuterEntry
      (arr.getD i.val 0) i
    CoherentAlias.IsValidAliasTable 184 10 wOut (fun i ↦ (tbl i).alt) (fun i ↦ (tbl i).keep) := by
  intro tbl
  unfold checkOuterPackedWeights at hchk
  simp only [Bool.and_eq_true, Nat.beq_eq] at hchk
  have hsize : arr.size = 184 := by simpa [Array.length_toList] using hchk.1
  refine ⟨fun i ↦ Nat.le_of_lt (Nat.mod_lt _ (by decide)), fun x ↦ ?_⟩
  have hx : x.val < arr.size := by rw [hsize]; exact x.isLt
  have hall : OuterWeights.allWithIdx (fun y raw ↦
      Nat.beq ((raw / 256) % 1024 +
        OuterWeights.sumAltPairs y (OuterWeights.unpackAltPairs 256 184 1024 arr.toList 0))
          (wFast y))
      arr.toList 0 = true := hchk.2
  have h := OuterWeights.allWithIdx_array_getD hall hx 0
  simp only [Nat.beq_eq, sumAltPairs_unpackOuter_eq, hw x] at h
  have h1 : (∑ i : Fin 184, if i = x then (tbl i).keep else 0) =
      ((arr.getD x.val 0) / 256) % 1024 := by
    simp [Finset.sum_ite_eq', tbl, OuterWeights.unpackOuterEntry]
  have h2 : OuterWeights.sumWithIdx (OuterWeights.outerAltTerm x.val) arr.toList 0 =
      ∑ i : Fin 184, if (tbl i).alt = x then 1024 - (tbl i).keep else 0 := by
    rw [OuterWeights.sumWithIdx_array_eq_fin_sum (OuterWeights.outerAltTerm x.val) arr 0 hsize]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    simp only [OuterWeights.outerAltTerm, cond_blt_eq, cond_beq_eq, tbl, Fin.ext_iff,
      OuterWeights.unpackOuterEntry_alt_val]
    unfold OuterWeights.unpackOuterEntry
    simp
  rw [Finset.sum_add_distrib, show (2 ^ 10 : ℕ) = 1024 by decide, h1, ← h2]
  exact h

/-- Bridge `OuterWeights.outerWeightFast x.val = outerWeightNat x` for standard P450 outer
ordering. -/
theorem outerWeightFast_eq_outerWeightNat (x : Fin 184) :
    OuterWeights.outerWeightFast x.val = outerWeightNat x := by
  have hfast : OuterWeights.outerWeightFast x.val = OuterWeights.outerTargetWeight x := by
    unfold OuterWeights.outerWeightFast OuterWeights.outerTargetWeight
    rw [cond_blt_eq]
    by_cases hx : x.val < 58
    · simp only [hx, ↓reduceIte, ↓reduceDIte, OuterWeights.natAbsOffset_eq]
    · simp only [hx, ↓reduceIte, ↓reduceDIte]
  have htgt : OuterWeights.outerTargetWeight x = outerWeightNat x := by
    by_cases h : x.val < 58
    · let ℓ : Fin 58 := ⟨x.val, h⟩
      have h1 : OuterWeights.outerTargetWeight x = (oneBodyWeightInt ℓ).natAbs := by
        rw [show x = OuterWeights.outerOneBodyIdx ℓ from Fin.ext rfl,
          OuterWeights.outerTargetWeight_oneBody,
          oneBodyWeightInt, DataArrays.oneBodyWeightsArr_getD]
      rw [h1]; simp [outerWeightNat, h, ℓ]
    · let r : Fin 9 := ⟨(x.val - 58) / 14, by omega⟩
      let c : Fin 14 := ⟨(x.val - 58) % 14, by omega⟩
      have h1 : OuterWeights.outerTargetWeight x = fragmentWeightNat r c := by
        rw [show x = OuterWeights.outerFragIdx r c from
          Fin.ext (by dsimp [OuterWeights.outerFragIdx, r, c]; omega),
            OuterWeights.outerTargetWeight_frag,
          fragmentWeightNat, DataArrays.fragmentWeightsArr_getD]
      rw [h1]; simp [outerWeightNat, h, r, c]
  exact hfast.trans htgt

attribute [local irreducible] oneBodyWeights fragmentWeights DataArrays.oneBodyWeightsArr
  DataArrays.fragmentWeightsArr oneBodyWeightInt fragmentWeightNat

/-! ### `2`-AND (`8 T`) `96`-Wire `alt` Subcircuit (`alt2Sub96Dyn`) -/

/-- `9`-wire Grover-`184` unitary synthesized from any single-qubit `Clifford+T` word `rotWord`. -/
noncomputable abbrev prepUnif184WordImpl (rotWord : List OuterWeights.GroverUniform.Gate1) :
    Unitary (2 ^ 9) :=
  OuterWeights.GroverUniform.prepGroverUnitary 3 5 23 (OuterWeights.GroverUniform.wordToCircuit1
    rotWord).eval

/-- Fixed-width `13`-wire forward Grover-`184` circuit parameterized by `rotWord`. -/
def prepUnif184WordLocDyn {Var : Type} (rotWord : List OuterWeights.GroverUniform.Gate1) (v : Var) :
    DynamicCircuit Var 13 :=
  OuterWeights.GroverUniform.prepGroverLocDyn 3 5 4
    (OuterWeights.GroverUniform.groverStepFwdLocDyn 5 4 rotWord
      (OuterWeights.GroverUniform.rGood23LocDyn v) (OuterWeights.GroverUniform.sZero6LocDyn v))

/-- Fixed-width `13`-wire inverse Grover-`184` circuit parameterized by `rotWord`. -/
def unprepUnif184WordLocDyn {Var : Type} (rotWord : List OuterWeights.GroverUniform.Gate1)
    (v : Var) :
    DynamicCircuit Var 13 :=
  OuterWeights.GroverUniform.unprepGroverLocDyn 3 5 4
    (OuterWeights.GroverUniform.groverStepInvLocDyn 5 4 rotWord
      (OuterWeights.GroverUniform.rGood23LocDyn v) (OuterWeights.GroverUniform.sZero6LocDyn v))

@[simp]
theorem wordCountTMag8To23Word :
    OuterWeights.GroverUniform.wordCountT FastCleanUnif184.mag8To23Word = 40 := by decide

end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.OptU2Grover184PrepOut13

namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.MobiusOptSubcube163Walk
open QuantumComputation.Specs QuantumComputation.Specs.P450
open Operator QProg Matrix Circuit HermitianMat Real
open QuantumComputation.Specs QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution
open QuantumComputation.Specs.P450
open BlockEncodingCore BlockEncodingCircuit
open FastUniform
open CoherentAlias
open AliasPrep
open Phase2MidSandwich
open CompactBilinearPrep
open DyadicPacketInnerPrep
open RankReducedPrepMid
open MidReflCtxRetain
open OptFactoredMag30AndCoin9
open Cat11CompactPhase2Bridge
open ReordOuter13Bridge
open ZeroRcHotPrepMid21Fast
open OptXMeasUnload21
open Tuned162ScheduledSympQrom21
open OptU2Grover184PrepOut13
open TopIntegrationBridge
open scoped Matrix BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator Circuit.Notation
local instance (priority := 1000000) instNeZeroTwoPowOpt163Compact64Walk (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩

/-- Remaining active outer width `(8 + wOuter + 1) - kZeroOut` (`14` at
`wOuter = 13, kZeroOut = 8`). -/
abbrev outRemWidth (wOuter kZeroOut : ℕ) : ℕ := blockRemWidth (mOutUB wOuter) 8 kZeroOut

/-- Zero-restored outer prefix sub-register `[8 .. 8 + kZeroOut)` inside `mOutUB wOuter`. -/
abbrev outZeroPrefixReg (wOuter kZeroOut : ℕ) (hk : kZeroOut ≤ wOuter) :
    QRegister kZeroOut (mOutUB wOuter) :=
  blockZeroReg (mOutUB wOuter) 8 kZeroOut (by dsimp [mOutUB]; omega)

/-- Combined active reflection control width (`25` at `(13, 21, 8, 16)`). -/
abbrev combARem (wOuter wInner2 kZeroOut kZeroMid : ℕ) : ℕ :=
  outRemWidth wOuter kZeroOut + midRemWidth wInner2 kZeroMid

/-- Total qubit count (`192 + sUb` at `(13, 21, 8, 16, mLow = 0, sUb ≥ 25)`). -/
abbrev combQubits (wOuter wInner2 kZeroOut kZeroMid mLow sUb : ℕ) : ℕ :=
  cat11TotalQubits 16 (mOutUB wOuter) (mMidUB wInner2) mLow
    (combARem wOuter wInner2 kZeroOut kZeroMid) (midRemWidth wInner2 kZeroMid) sUb

/-- Walk + `11`-catalyst register inside `combQubits`. -/
abbrev combWalkCatReg (wOuter wInner2 kZeroOut kZeroMid mLow sUb : ℕ) :
    QRegister (walkCatWidth 11 (mOutUB wOuter) (mMidUB wInner2))
      (combQubits wOuter wInner2 kZeroOut kZeroMid mLow sUb) :=
  rWalkCatLoc 16 11 (mOutUB wOuter) (mMidUB wInner2) mLow
    (combARem wOuter wInner2 kZeroOut kZeroMid) (midRemWidth wInner2 kZeroMid) sUb

/-- `combQubits2` alias (`rfl`-identical to `combQubits`). -/
abbrev combQubits2 := combQubits

/-- Clean two-reflection realization on `combWalkCatReg` with zeroed `rFullZeroLoc`. -/
abbrev CleanWalkRefl2 {Var : Type} [Fintype Var] [DecidableEq Var]
    (wOuter wInner2 kZeroOut kZeroMid mLow sUb : ℕ) (hkOut : kZeroOut ≤ wOuter) (hkMid : kZeroMid ≤
      wInner2)
    (v : Var) (uRefl2 : Unitary (2 ^ walkCatWidth 11 (mOutUB wOuter) (mMidUB wInner2)))
    (pRefl2 : DynamicCircuit Var (combQubits wOuter wInner2 kZeroOut kZeroMid mLow sUb)) : Prop :=
  XMeasCircuit.CleanRealizes v (combWalkCatReg wOuter wInner2 kZeroOut kZeroMid mLow sUb)
    (rFullZeroLoc 16 11 (mOutUB wOuter) (mMidUB wInner2) mLow
      (combARem wOuter wInner2 kZeroOut kZeroMid) (midRemWidth wInner2 kZeroMid) sUb
      (liftOutMidZeroToAnc (mOutUB wOuter) (mMidUB wInner2)
        (outZeroPrefixReg wOuter kZeroOut hkOut) (midZeroPrefixReg wInner2 kZeroMid hkMid)))
    uRefl2 pRefl2

attribute [local irreducible] thcHamiltonian BlockEncodingCore.p450HBlocked dfthcLowerBound

/-- Outer `8`-bit bijection mapping `0..125 ↦ 58..183` without `rcOnly` wires. -/
structure IsZeroRcOuterPerm (σ : Equiv.Perm (Fin (2 ^ 8))) : Prop where
  /-- Maps two-body indices `xo' < 126` to `xo'.val + 58`. -/
  lt126 : ∀ xo' : Fin (2 ^ 8), xo'.val < 126 → (σ xo').val = xo'.val + 58
  /-- Maps `126 ≤ xo'` into one-body `< 58` or padding `184 ≤ ·`. -/
  ge126 : ∀ xo' : Fin (2 ^ 8), 126 ≤ xo'.val → (σ xo').val < 58 ∨ 184 ≤ (σ xo').val
  /-- Preserves the active `xo < 184` support. -/
  lt184_iff : ∀ xo' : Fin (2 ^ 8), (σ xo').val < 184 ↔ xo'.val < 184

theorem extract_rXo7_eq_rcBitsOfXo_of_isZeroRcOuterPerm {σ : Equiv.Perm (Fin (2 ^ 8))}
    (hσ : IsZeroRcOuterPerm σ) (xo' : Fin (2 ^ 8))
    (h184 : xo'.val < 184) (h58 : 58 ≤ (σ xo').val) :
    (QRegister.block 0 7 (by decide) : QRegister 7 8).extractIndex xo' = rcBitsOfXo (σ xo') := by
  have hlt126 : xo'.val < 126 := by
    by_contra hge; rcases hσ.ge126 xo' (by omega) with _ | _
    · omega
    · have := (hσ.lt184_iff xo').mpr h184; omega
  have hex7 : (QRegister.block 0 7 (by decide) : QRegister 7 8).extractIndex xo' =
      ⟨xo'.val, by omega⟩ := by
    apply (basisBits 7).injective; funext i
    rw [QRegister.basisBits_extractIndex, basisBits_eq_testBit, basisBits_eq_testBit]
    simp only [QRegister.block_apply_val, Nat.zero_add]
  ext; rw [hex7]; dsimp only [rcBitsOfXo]; rw [hσ.lt126 xo' hlt126, ite_eq_right (by omega)]; omega

/-- Direct `0`-`rcOnly` multiplexed `PREP_mid` unitary controlled by `rXo7UB wOuter wInner2`. -/
noncomputable abbrev prepMidDirectXo7MuxUnitary (wOuter wInner2 : ℕ)
    (prepMid : Fin (2 ^ 7) → Unitary (2 ^ mMidUB wInner2)) : Unitary (2 ^ nUB wOuter wInner2) :=
  muxUnitary (rXo7UB wOuter wInner2) (rMidUB wOuter wInner2) (disjoint_rXo7UB_rMidUB wOuter wInner2)
    prepMid

/-- Catalyzed 4-step `U_B` unitary on `nUB wOuter wInner2 + kCat` for any inner mux `M_impl`. -/
noncomputable def ubCustomMuxCatUnitary {wOuter wInner2 kCat : ℕ} (M_impl : Unitary (2 ^ nUB wOuter
    wInner2))
    (prepOutImpl : Unitary (2 ^ mOutUB wOuter)) (selectCat : Unitary (2 ^ (nUB wOuter wInner2 +
      kCat))) :
    Unitary (2 ^ (nUB wOuter wInner2 + kCat)) :=
  (rUBInCat wOuter wInner2 kCat).embedUnitary M_impl⁻¹ * selectCat *
    (rUBInCat wOuter wInner2 kCat).embedUnitary M_impl *
    ((rUBInCat wOuter wInner2 kCat).compose (rOutUB wOuter wInner2)).embedUnitary prepOutImpl

/-- Pure 4-step `0`-`rcOnly` `U_B` unitary built from a pure `selectPure` unitary. -/
noncomputable def ubDirectXo7PureUnitary {wOuter wInner2 : ℕ} (prepOutPerm : Unitary
    (2 ^ mOutUB wOuter))
    (prepMid : Fin (2 ^ 7) → Unitary (2 ^ mMidUB wInner2)) (selectPure : Unitary (2 ^ nUB wOuter
      wInner2)) :
    Unitary (2 ^ nUB wOuter wInner2) :=
  (prepMidDirectXo7MuxUnitary wOuter wInner2 prepMid)⁻¹ * selectPure *
    prepMidDirectXo7MuxUnitary wOuter wInner2 prepMid * (rOutUB wOuter wInner2).embedUnitary
      prepOutPerm

theorem outerSandwich_eq_reflPulledPair_customMux {N wOuter wInner2 bCat : ℕ}
    (rMain : QRegister (nUB wOuter wInner2 + bCat) N) (M_fwd M_bwd : Unitary (2 ^ nUB wOuter
      wInner2))
    (prepOutImpl : Unitary (2 ^ mOutUB wOuter))
    (selectCatFwd selectCatBwdImpl : Unitary (2 ^ (nUB wOuter wInner2 + bCat))) :
    let rOut := (rMain.compose (rUBInCat wOuter wInner2 bCat)).compose (rOutUB wOuter wInner2)
    (rOut.embedUnitary prepOutImpl)⁻¹ *
      rMain.embedUnitary
        (((rUBInCat wOuter wInner2 bCat).embedUnitary M_bwd⁻¹ * selectCatBwdImpl *
            (rUBInCat wOuter wInner2 bCat).embedUnitary M_bwd) *
          QubitisedWalk.reflMidUnitary (inMidWalkCat bCat (mOutUB wOuter) (mMidUB wInner2)) *
          ((rUBInCat wOuter wInner2 bCat).embedUnitary M_fwd⁻¹ * selectCatFwd *
            (rUBInCat wOuter wInner2 bCat).embedUnitary M_fwd)) *
      rOut.embedUnitary prepOutImpl =
    rMain.embedUnitary
      (QubitisedWalk.reflPulledPair (inMidWalkCat bCat (mOutUB wOuter) (mMidUB wInner2))
        (ubCustomMuxCatUnitary M_fwd prepOutImpl selectCatFwd)
        (ubCustomMuxCatUnitary M_bwd prepOutImpl selectCatBwdImpl⁻¹)⁻¹) := by
  intro rOut
  have hOutAssoc : rOut = rMain.compose ((rUBInCat wOuter wInner2 bCat).compose (rOutUB wOuter
    wInner2)) :=
    CoherentAlias.qreg_ext fun _ ↦ rfl
  have hBwdInv : (ubCustomMuxCatUnitary M_bwd prepOutImpl selectCatBwdImpl⁻¹)⁻¹ =
      (((rUBInCat wOuter wInner2 bCat).compose (rOutUB wOuter wInner2)).embedUnitary prepOutImpl)⁻¹
        *
        (rUBInCat wOuter wInner2 bCat).embedUnitary M_bwd⁻¹ * selectCatBwdImpl *
        (rUBInCat wOuter wInner2 bCat).embedUnitary M_bwd := by
    dsimp only [ubCustomMuxCatUnitary]; simp [_root_.mul_inv_rev, mul_assoc]
  rw [QubitisedWalk.reflPulledPair, hBwdInv, hOutAssoc]
  dsimp only [ubCustomMuxCatUnitary]
  simp only [QRegister.embedUnitary_compose, rMain.embedUnitary_mul, QRegister.embedUnitary_inv,
    mul_assoc]

private theorem dotProduct_star_mulVec_loc {d : ℕ} (A : Operator d) (x y : Fin d → ℂ) :
    dotProduct (star (A *ᵥ x)) y = dotProduct (star x) (Aᴴ *ᵥ y) := by
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec]

private theorem dotProduct_proj_conj_proj_eq_loc {d : ℕ} (P_in P_mid : Operator d)
    (hPin : P_inᴴ = P_in) (hPmid : P_midᴴ = P_mid) (hIdem : P_mid * P_mid = P_mid)
    (U : Operator d) (e_φ e_ψ : Fin d → ℂ) (he : P_in *ᵥ e_φ = e_φ) :
    dotProduct (star e_φ) (P_in *ᵥ (Uᴴ *ᵥ (P_mid *ᵥ (U *ᵥ e_ψ)))) =
      dotProduct (star (P_mid *ᵥ (U *ᵥ e_φ))) (P_mid *ᵥ (U *ᵥ e_ψ)) := by
  calc dotProduct (star e_φ) (P_in *ᵥ (Uᴴ *ᵥ (P_mid *ᵥ (U *ᵥ e_ψ))))
      = dotProduct (star (P_in *ᵥ e_φ)) (Uᴴ *ᵥ (P_mid *ᵥ (U *ᵥ e_ψ))) := by
        rw [dotProduct_star_mulVec_loc P_in, hPin]
    _ = dotProduct (star (U *ᵥ e_φ)) ((P_mid * P_mid) *ᵥ (U *ᵥ e_ψ)) := by
        rw [he, ← dotProduct_star_mulVec_loc U, hIdem]
    _ = dotProduct (star (P_mid *ᵥ (U *ᵥ e_φ))) (P_mid *ᵥ (U *ᵥ e_ψ)) := by
        rw [← Matrix.mulVec_mulVec]; conv_rhs => rw [dotProduct_star_mulVec_loc P_mid, hPmid]

private theorem rSysInWalk_basisSplitEquiv_snd_ne_zero {mOut mMid : ℕ}
    {g : Fin (2 ^ walkWidth mOut mMid)} (hg : (rAllInWalk mOut mMid).extractIndex g ≠ 0) :
    ((rSysInWalk mOut mMid).basisSplitEquiv g).2 ≠ 0 := by
  intro heq; apply hg
  apply (basisBits (mOut + mMid)).injective; funext j
  have hnot : rAllInWalk mOut mMid j ∉ Set.range (rSysInWalk mOut mMid).wires := by
    rintro ⟨i, hi⟩; have hv := congrArg Fin.val hi
    simp only [rSysInWalk, rAllInWalk, QRegister.block_apply_val] at hv
    have := i.isLt; omega
  have hv := congrFun heq ⟨rAllInWalk mOut mMid j, hnot⟩
  change basisBits _ g (rAllInWalk mOut mMid j) = 0 at hv
  change basisBits _ ((rAllInWalk mOut mMid).extractIndex g) j = basisBits _ 0 j
  rw [(rAllInWalk mOut mMid).basisBits_extractIndex, hv]
  exact (congrFun (CoherentAlias.basisBits_zero_apply (mOut + mMid)) j).symm

private theorem eq_of_projIn_and_dotProduct_loc {mOut mMid : ℕ}
    (v₁ v₂ : Fin (2 ^ walkWidth mOut mMid) → ℂ)
    (hv₁ : QubitisedWalk.projIn (rAllInWalk mOut mMid) *ᵥ v₁ = v₁)
    (hv₂ : QubitisedWalk.projIn (rAllInWalk mOut mMid) *ᵥ v₂ = v₂)
    (hdot : ∀ φ : Fin (2 ^ systemQubits_local) → ℂ,
      dotProduct (star ((rSysInWalk mOut mMid).tensorState φ (Pi.single 0 1))) v₁ =
        dotProduct (star ((rSysInWalk mOut mMid).tensorState φ (Pi.single 0 1))) v₂) :
    v₁ = v₂ := by
  let rSys := rSysInWalk mOut mMid; let rAll := rAllInWalk mOut mMid
  let d := v₁ - v₂
  let φ : Fin (2 ^ systemQubits_local) → ℂ := fun s ↦
    ∑ g : Fin (2 ^ walkWidth mOut mMid),
      if rSys.extractIndex g = s ∧ rAll.extractIndex g = 0 then d g else 0
  have hPin_d : QubitisedWalk.projIn rAll *ᵥ d = d := by
    dsimp only [d]; rw [Matrix.mulVec_sub, hv₁, hv₂]
  have hd_eq : rSys.tensorState φ (Pi.single 0 1) = d := by
    funext g; by_cases hg : rAll.extractIndex g = 0
    · have hex_env : (rSys.basisSplitEquiv g).2 = 0 := by
        funext ⟨w, hw⟩
        have hw_ge : systemQubits_local ≤ w.val := by
          by_contra hlt
          exact hw ⟨⟨w.val, Nat.lt_of_not_ge hlt⟩, Fin.ext (by simp [rSys, rSysInWalk])⟩
        let j : Fin (mOut + mMid) :=
          ⟨w.val - systemQubits_local,
            by have := w.isLt; dsimp [walkWidth, walkAncillas] at this; omega⟩
        have hw_all : rAll j = w := Fin.ext (by simp [rAll, rAllInWalk, j]; omega)
        have hb0 : basisBits (mOut + mMid) (rAll.extractIndex g) j = 0 := by
          rw [hg]; exact congrFun (CoherentAlias.basisBits_zero_apply (mOut + mMid)) j
        rw [rAll.basisBits_extractIndex, hw_all] at hb0; exact hb0
      dsimp only [QRegister.tensorState]; rw [hex_env, Pi.single_eq_same, mul_one]; dsimp only [φ]
      rw [Finset.sum_eq_single g]
      · simp [hg]
      · intro g' _ hg'ne
        by_cases hc : rSys.extractIndex g' = rSys.extractIndex g ∧ rAll.extractIndex g' = 0
        · exfalso; apply hg'ne
          apply (basisBits (walkWidth mOut mMid)).injective; funext w
          by_cases hlt : w.val < systemQubits_local
          · let i : Fin systemQubits_local := ⟨w.val, hlt⟩
            have hwi : rSys i = w := Fin.ext (by simp [rSys, rSysInWalk, i])
            have h1 := rSys.basisBits_extractIndex g' i; have h2 := rSys.basisBits_extractIndex g i
            rw [hc.1, hwi] at h1; rw [hwi] at h2; exact h1.symm.trans h2
          · let j : Fin (mOut + mMid) := ⟨w.val - systemQubits_local,
              by have := w.isLt; dsimp [walkWidth, walkAncillas] at this; omega⟩
            have hwj : rAll j = w := Fin.ext (by simp [rAll, rAllInWalk, j]; omega)
            have h1 := rAll.basisBits_extractIndex g' j; have h2 := rAll.basisBits_extractIndex g j
            rw [hc.2, hwj] at h1; rw [hg, hwj] at h2; exact h1.symm.trans h2
        · simp [hc]
      · intro h0; exact (h0 (Finset.mem_univ g)).elim
    · have hd0 : d g = 0 := by
        rw [← hPin_d]; dsimp only [QubitisedWalk.projIn]
        rw [rAll.basisOutcomeProjector_mulVec, ite_eq_right hg]
      dsimp only [QRegister.tensorState]
      rw [Pi.single_eq_of_ne (rSysInWalk_basisSplitEquiv_snd_ne_zero hg), mul_zero, hd0]
  have hzero : dotProduct (star d) d = 0 := by
    calc dotProduct (star d) d
        = dotProduct (star (rSys.tensorState φ (Pi.single 0 1))) d :=
            congrArg (fun x ↦ dotProduct (star x) d) hd_eq.symm
      _ = dotProduct (star (rSys.tensorState φ (Pi.single 0 1))) v₁ -
            dotProduct (star (rSys.tensorState φ (Pi.single 0 1))) v₂ := dotProduct_sub _ _ _
      _ = 0 := sub_eq_zero.mpr (hdot φ)
  have hsum0 : (∑ g : Fin (2 ^ walkWidth mOut mMid), Complex.normSq (d g)) = 0 := by
    have hc : dotProduct (star d) d =
        ((∑ g : Fin (2 ^ walkWidth mOut mMid), Complex.normSq (d g) : ℝ) : ℂ) := by
      simp only [dotProduct, Pi.star_apply, Complex.star_def, Complex.ofReal_sum]
      exact Finset.sum_congr rfl fun g _ ↦ by rw [mul_comm, Complex.mul_conj]
    simpa [hc] using congrArg Complex.re hzero
  funext g
  exact sub_eq_zero.mp (Complex.normSq_eq_zero.mp
    ((Finset.sum_eq_zero_iff_of_nonneg fun i _ ↦ Complex.normSq_nonneg (d i)).mp hsum0 g
      (Finset.mem_univ g)))

theorem pulledSOSBlockEncoding_of_halfStep_unitary_eq {mOut mMid : ℕ}
    {H_tilde_blk : Operator (2 ^ systemQubits_local)} {eLB lam : ℝ}
    {uB uB' U_walk : Unitary (2 ^ walkWidth mOut mMid)}
    (hSOS : PulledSOSBlockEncoding mOut mMid H_tilde_blk eLB lam uB)
    (hHalf : ∀ φ : Fin (2 ^ systemQubits_local) → ℂ,
      U_walk.1 *ᵥ
          (QubitisedWalk.projMid (rMidInWalk mOut mMid) *ᵥ
            (uB'.1 *ᵥ (rSysInWalk mOut mMid).tensorState φ (Pi.single 0 1))) =
        QubitisedWalk.projMid (rMidInWalk mOut mMid) *ᵥ
          (uB.1 *ᵥ (rSysInWalk mOut mMid).tensorState φ (Pi.single 0 1))) :
    PulledSOSBlockEncoding mOut mMid H_tilde_blk eLB lam uB' := by
  refine ⟨hSOS.hLamPos, fun ψ E hEig hnorm ↦ ?_⟩
  obtain ⟨hPin1, hNorm1, heLB, heUB, hJordan⟩ := hSOS.jordanRelation ψ E hEig hnorm
  refine ⟨hPin1, hNorm1, heLB, heUB, ?_⟩
  rw [← hJordan]
  let rAll := rAllInWalk mOut mMid; let rMid := rMidInWalk mOut mMid
  let rSys := rSysInWalk mOut mMid
  have hPin_idem (w : Fin (2 ^ walkWidth mOut mMid) → ℂ) :
      QubitisedWalk.projIn rAll *ᵥ (QubitisedWalk.projIn rAll *ᵥ w) = QubitisedWalk.projIn rAll *ᵥ
        w := by
    rw [Matrix.mulVec_mulVec, QubitisedWalk.projIn, rAll.basisOutcomeProjector_mul_self]
  refine eq_of_projIn_and_dotProduct_loc _ _ (hPin_idem _) (hPin_idem _) fun φ ↦ ?_
  have hPin_φ : QubitisedWalk.projIn rAll *ᵥ rSys.tensorState φ (Pi.single 0 1) =
      rSys.tensorState φ (Pi.single 0 1) := by
    dsimp only [QubitisedWalk.projIn]; funext g; rw [rAll.basisOutcomeProjector_mulVec]
    by_cases hg : rAll.extractIndex g = 0
    · simp [hg]
    · rw [ite_eq_right hg]; symm; dsimp only [QRegister.tensorState]
      rw [Pi.single_eq_of_ne (rSysInWalk_basisSplitEquiv_snd_ne_zero hg), mul_zero]
  have hUu : U_walk.1ᴴ * U_walk.1 = 1 := by rw [← Matrix.star_eq_conjTranspose]; exact U_walk.2.1
  have hExp (V : Unitary (2 ^ walkWidth mOut mMid)) :
      QubitisedWalk.pulledProjMid rMid V *ᵥ rSys.tensorState ψ (Pi.single 0 1) =
        V.1ᴴ *ᵥ (QubitisedWalk.projMid rMid *ᵥ (V.1 *ᵥ rSys.tensorState ψ (Pi.single 0 1))) := by
    rw [QubitisedWalk.pulledProjMid, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  rw [hExp uB', hExp uB,
    dotProduct_proj_conj_proj_eq_loc _ _ (QubitisedWalk.projIn_conjTranspose rAll)
      (QubitisedWalk.projMid_conjTranspose rMid) (rMid.basisOutcomeProjector_mul_self 0) _ _ _
        hPin_φ,
    dotProduct_proj_conj_proj_eq_loc _ _ (QubitisedWalk.projIn_conjTranspose rAll)
      (QubitisedWalk.projMid_conjTranspose rMid) (rMid.basisOutcomeProjector_mul_self 0) _ _ _
        hPin_φ,
    ← hHalf φ, ← hHalf ψ]
  conv_rhs =>
    rw [dotProduct_star_mulVec_loc U_walk.1, Matrix.mulVec_mulVec _ U_walk.1ᴴ U_walk.1,
      hUu, Matrix.one_mulVec]

attribute [local irreducible] selectBranchUnitary blockedOrbitalReflection

/-! ## Section 1A: Ancilla-Free `16 T` Subcube Packet Coin -/

attribute [local irreducible] DataArrays.leafAngleTableArr oneBodyWeightInt
  DataArrays.oneBodyAngleTableArr DataArrays.oneBodyWeightsArr fragmentWeightNat
  DataArrays.fragmentWeightsArr DataArrays.innerWeightsArr innerMantissa negIn

theorem compose_disjoint_opt163 {N M m₁ m₂ : ℕ} (r : QRegister M N)
    {r₁ : QRegister m₁ M} {r₂ : QRegister m₂ M} (hd : r₁.DisjointWires r₂) :
    (r.compose r₁).DisjointWires (r.compose r₂) :=
  QRegister.disjoint_iff.mpr fun i j h ↦ hd.ne i j (r.wires.injective h)

/-- Permutation of the `10` `keep` wires aligning the subcube coin weights with `pktMux10Dyn`. -/
def keepPerm10 : Fin 10 → Fin 10 := ![0, 2, 5, 3, 1, 4, 9, 8, 6, 7]

/-- `0`-`T` `10`-wire register permutation for `pktMux10Dyn`. -/
def keepPerm10Reg : QRegister 10 10 := ⟨⟨keepPerm10, by decide⟩⟩

/-! ## Copied Private Helpers for `base40Prog` and `alt2PhaseFixCircuit` -/

@[simp] private theorem wordCountTMag8To23Word_loc :
    OuterWeights.GroverUniform.wordCountT FastCleanUnif184.mag8To23Word = 40 := rfl

end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.MobiusOptSubcube163Walk

namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.CompactTuned162StepWalk
open QuantumComputation.Specs QuantumComputation.Specs.P450

section StepQromUnloaders

export QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.OptStepSympAnfQrom21 (
  ext24InnerBoolTable oneHotPred
)

end StepQromUnloaders

section StepWalk

open Operator QProg Matrix Circuit HermitianMat Real
open QuantumComputation.Specs QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution
open QuantumComputation.Specs.P450
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.BlockEncodingCore
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.BlockEncodingCircuit
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.FastUniform
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.CoherentAlias
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.AliasPrep
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.Phase2MidSandwich
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.CompactBilinearPrep
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.DyadicPacketInnerPrep
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.RankReducedPrepMid
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.MidReflCtxRetain
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.OptFactoredMag30AndCoin9
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.Cat11CompactPhase2Bridge
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.ReordOuter13Bridge
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.ZeroRcHotPrepMid21Fast
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.OptXMeasUnload21
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.Tuned162ScheduledSympQrom21
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.OptU2Grover184PrepOut13
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.TopIntegrationBridge
open scoped Matrix BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator Circuit.Notation

local instance (priority := 1000000) instNeZeroTwoPowStepWalk (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.OptStepSympAnfQrom21
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.MobiusOptSubcube163Walk

/-! ## Section 2: Hot `12`-AND (`48 T`) Unloader & Turnaround Helpers -/

@[simp] private theorem wordCountTMag8To23Word_loc :
    OuterWeights.GroverUniform.wordCountT FastCleanUnif184.mag8To23Word = 40 := rfl

section ConcreteRefl2Sos

variable {Var : Type} [Fintype Var] [DecidableEq Var] {mLow sUb : ℕ} (hUb : 155 ≤ sUb) {v : Var}
  {selectPure : Unitary (2 ^ nUB 13 21)} {selFwdImpl selBwdImpl : Unitary (2 ^ (nUB 13 21 + 11))}
  {pSelFwd pSelBwd : DynamicCircuit Var (combQubits2 13 21 8 16 mLow sUb)}
  {δSelFwd δSelBwd δStep eRef : ℝ}

/-! ### Tier 1: `Clean100 + 932 T` (`4,452 T/step`, `δBase = 298 / 10 ^ 15`) -/

/-! ### Tier 2: `Clean98 + 932 T` (`4,444 T/step`, `δBase = 1066 / 10 ^ 15`) -/

/-! ### Tier 3: `Tight97 + 932 T` (`4,440 T/step`, `δBase = 1446 / 10 ^ 15`) -/

/-! ### Tier 4: `Med96 + 932 T` (`4,436 T/step`, `δBase = 2190 / 10 ^ 15`) -/

end ConcreteRefl2Sos

/-! ### Active-`b < 30` `SELECT` Contract (`ReordActiveSelectSpec`) & Step-Reflection Closures -/

section ActiveStepRefl2
variable {Var : Type} [Fintype Var] [DecidableEq Var] {mLow sUb : ℕ} (hUb : 155 ≤ sUb) {v : Var}
  {sP : Unitary (2 ^ nUB 13 21)} {sF sB : Unitary (2 ^ (nUB 13 21 + 11))}
  {p1 p2 : DynamicCircuit Var (combQubits2 13 21 8 16 mLow sUb)} {δ1 δ2 δStep : ℝ}

end ActiveStepRefl2

end StepWalk

end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.CompactTuned162StepWalk

end
