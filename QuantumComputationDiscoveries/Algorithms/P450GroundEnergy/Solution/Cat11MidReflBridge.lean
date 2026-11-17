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

public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.TopIntegrationBridge
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.MidReflSandwich
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.WalkQPEFlexBridge
public import
  QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.WalkQPECat11ReducedRefl

/-!
# `11`-Catalyst & Stage-2 `TopIntegrationBridge` Integration

Connects quantized state preparation and Stage-2 X-measurement / custom-`SELECT` walks directly to
`TopIntegrationBridge` (`bCat = 11` `1,130 T` exact-floor phase-gradient catalyst, arbitrary
`bQPE`, arbitrary `(wOuter, wInner2)`, and tightened `sUb` including `sUb = 183`):

1. **Section 1 — Clean-Zero Reflection Partitions & `TopIntegrationBridge` Wire Bridges:**
   - Generic contiguous block complement `blockZeroReg` / `blockComplementReg` /
     `blockComplementReg_cover` covering any offset (`off = 5` standard `aliasOutReg` or `off = 15`
     low-keep in `mMidUB wInner2`, and `off = 8` or `off = 18` in `mOutUB wOuter`).
   - Combined `(out, mid)` reduced-reflection bundle `liftOutMidZeroToAnc`,
     `reducedOutMidWalkReflRegs`, and `reducedOutMidWalkReflCovers` (`aRem = oRem + mRem`).
   - Register bridges `rWalkCatLoc_disjoint_rScrUbLoc` and
     `rMidZero_compose_eq_rAncZeroLoc`.
2. **Section 2 — General `CleanUnloadsWp` Sandwich & `TopIntegrationBridge` Stage-2 Adapters:**
   - Reusable `Finset`-level X-measurement sandwich `cleanRealizesSet_sandwich_of_cleanUnloadsWp`.
   - Direct `TopIntegrationBridge` Stage-2 forward/backward `CleanRealizesSet` and `reflPulledDyn`
     adapters supporting asymmetric `(prepOutFwdImpl, prepMidFwdImpl, selectCatFwd)` vs
     `(prepOutBwdImpl, prepMidBwdImpl, selectCatBwdImpl)`, plus 1-call `Bilinear183` wrappers.
3. **Section 3 — Parametric `14 → 11` Catalyst Projection & Custom-`SELECT` Perturbation Bounds:**
   - Parametric `{mOut mMid : ℕ}` single-operator `cat11_l2_of_cat14_locLeft` and pulled-pair
     `pulled_cat11_of_cat14_sd` projecting `14`-cat `phaseGradientState 14` bounds down to
     `CircuitModular.phaseGradientLowFactor 11 3` with zero error loss.
   - `ubCustomIdealUnitary`, `ubCat_l2_perturbation_custom_le`, and
     `ubCat_pulled_l2_custom_asym_le` for arbitrary `selectIdeal` (exact `dfthc`, refitted Givens,
     or BLISS-shifted Hamiltonians).
4. **Section 4 — `bCat = 11` `TopIntegrationBridge` Master Wrappers (`1,130 T`, `δCat = 10⁻⁸`):**
   - `masterCat11TopRefl2Prog` and `masterCat11TopProg` specializing `TopIntegrationBridge` at
     `bCat = 11` and `ChunkedPulledMaster11.approxPhaseGradLow11` (`1,130 T`, `0 TOFF`), with
     unconditional `.TOFF = 0`, `.T` bounds, and both fused `pRefl2` and paired `(pFwd, pBwd)`
     correctness closures.
-/

@[expose] public section

namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.Cat11CompactPhase2Bridge
open QuantumComputation.Specs QuantumComputation.Specs.P450

open Operator Matrix Real HermitianMat QProg
open QuantumComputation.Specs.P450 QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.TopIntegrationBridge
open scoped Matrix BigOperators Matrix.Norms.L2Operator

local instance (priority := 1000000) instNeZeroTwoPow (k : ℕ) : NeZero (2 ^ k) :=
  ⟨Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos k)⟩

/-! ## Section 1: Clean-Zero Reflection Partitions & `TopIntegrationBridge` Wire Bridges -/

/-- Remaining active wire count `off + (m - (off + kZero))` after excising a contiguous
`kZero`-wire clean-zero block starting at `off` inside an `m`-wire register. -/
abbrev blockRemWidth (m off kZero : ℕ) : ℕ :=
  off + (m - (off + kZero))

/-- Contiguous `kZero`-wire clean-zero subregister `[off .. off + kZero)` inside `Fin m`. -/
def blockZeroReg (m off kZero : ℕ) (h : off + kZero ≤ m) : QRegister kZero m :=
  QRegister.block off kZero h

/-- Complement subregister `[0 .. off) ++ [off + kZero .. m)` of `blockZeroReg m off kZero h`. -/
def blockComplementReg (m off kZero : ℕ) (h : off + kZero ≤ m) :
    QRegister (blockRemWidth m off kZero) m :=
  have hDisj : (QRegister.block 0 off (by omega) : QRegister off m).DisjointWires
      (QRegister.block (off + kZero) (m - (off + kZero)) (by omega)) := by
    rw [QRegister.disjoint_iff]
    intro i j hij
    have hv := congrArg Fin.val hij
    simp only [QRegister.block_apply_val] at hv
    omega
  (QRegister.block 0 off (by omega)).concat
    (QRegister.block (off + kZero) (m - (off + kZero)) (by omega)) hDisj

/-- Every wire in `Fin m` lies in either `blockComplementReg` or `blockZeroReg`. -/
theorem blockComplementReg_cover (m off kZero : ℕ) (h : off + kZero ≤ m) (u : Fin m) :
    u ∈ (blockComplementReg m off kZero h).image ∨ u ∈ (blockZeroReg m off kZero h).image := by
  rcases lt_or_ge u.val off with hlo | hge
  · left
    rw [QRegister.mem_image]
    refine ⟨Fin.castAdd (m - (off + kZero)) ⟨u.val, hlo⟩, ?_⟩
    ext
    simp only [blockComplementReg, QRegister.concat_apply_left, QRegister.block_apply_val]
    omega
  · rcases lt_or_ge u.val (off + kZero) with hmid | hhi
    · right
      rw [QRegister.mem_image]
      refine ⟨⟨u.val - off, by omega⟩, ?_⟩
      ext
      simp only [blockZeroReg, QRegister.block_apply_val]
      omega
    · left
      rw [QRegister.mem_image]
      refine ⟨Fin.natAdd off ⟨u.val - (off + kZero), by omega⟩, ?_⟩
      ext
      simp only [blockComplementReg, QRegister.concat_apply_right, QRegister.block_apply_val]
      omega

/-- Remaining active `mid` width `5 + (wInner2 - kZeroMid + 1)` when `kZeroMid` QROM wires in
`mMidUB wInner2` are clean `|0⟩`. -/
abbrev midRemWidth (wInner2 kZeroMid : ℕ) : ℕ :=
  blockRemWidth (BlockEncodingCore.mMidUB wInner2) 5 kZeroMid

/-- Standard Stage-2 clean-zero `mid` prefix `[5 .. 5 + kZeroMid)` inside `mMidUB wInner2`
(definitionally equal to `mid26AliasOutReg` at `(wInner2, kZeroMid) = (26, 16)`). -/
abbrev midZeroPrefixReg (wInner2 kZeroMid : ℕ) (hk : kZeroMid ≤ wInner2) :
    QRegister kZeroMid (BlockEncodingCore.mMidUB wInner2) :=
  blockZeroReg (BlockEncodingCore.mMidUB wInner2) 5 kZeroMid
    (by dsimp [BlockEncodingCore.mMidUB]; omega)

/-- Active `mid` complement `[0 .. 5) ++ [5 + kZeroMid .. mMidUB wInner2)` paired with
`midZeroPrefixReg`. -/
abbrev midRemComplementReg (wInner2 kZeroMid : ℕ) (hk : kZeroMid ≤ wInner2) :
    QRegister (midRemWidth wInner2 kZeroMid) (BlockEncodingCore.mMidUB wInner2) :=
  blockComplementReg (BlockEncodingCore.mMidUB wInner2) 5 kZeroMid
    (by dsimp [BlockEncodingCore.mMidUB]; omega)

/-- Embeds a pair of clean-zero subregisters `(rOutZero, rMidZero)` into `mOut + mMid`. -/
def liftOutMidZeroToAnc (mOut mMid : ℕ) {kZeroOut kZeroMid : ℕ}
    (rOutZero : QRegister kZeroOut mOut) (rMidZero : QRegister kZeroMid mMid) :
    QRegister (kZeroOut + kZeroMid) (mOut + mMid) :=
  have hDisj : ((QRegister.block 0 mOut (by omega) : QRegister mOut (mOut + mMid)).compose
        rOutZero).DisjointWires
      ((QRegister.block mOut mMid (by omega)).compose rMidZero) := by
    rw [QRegister.disjoint_iff]
    intro i j hij
    have hv := congrArg Fin.val hij
    simp only [QRegister.compose_apply, QRegister.block_apply_val] at hv
    have := (rOutZero i).isLt
    omega
  ((QRegister.block 0 mOut (by omega)).compose rOutZero).concat
    ((QRegister.block mOut mMid (by omega)).compose rMidZero) hDisj

/-- Combined `(out, mid)` reduced-reflection bundle (`aRem = oRem + mRem`, `mRem`) when both
`out` and `mid` have clean-zero subregisters. -/
def reducedOutMidWalkReflRegs (bCat mOut mMid : ℕ) {oRem mRem : ℕ}
    (rOutRem : QRegister oRem mOut) (rMidRem : QRegister mRem mMid)
    (haPos : 1 ≤ oRem + mRem) (hmPos : 1 ≤ mRem) :
    WalkReflRegs bCat mOut mMid (oRem + mRem) mRem :=
  have hDisj : ((rOutInWalk mOut mMid).compose rOutRem).DisjointWires
      ((rMidInWalk mOut mMid).compose rMidRem) := by
    rw [QRegister.disjoint_iff]
    intro i j hij
    have hv := congrArg Fin.val hij
    simp only [rOutInWalk, rMidInWalk, QRegister.compose_apply, QRegister.block_apply_val] at hv
    have := (rOutRem i).isLt
    omega
  ⟨(rWalkInWalkCat bCat mOut mMid).compose
      (((rOutInWalk mOut mMid).compose rOutRem).concat
        ((rMidInWalk mOut mMid).compose rMidRem) hDisj),
   (inMidWalkCat bCat mOut mMid).compose rMidRem,
   haPos, hmPos⟩

/-- Coverage proof for `reducedOutMidWalkReflRegs` paired with `liftOutMidZeroToAnc`. -/
theorem reducedOutMidWalkReflCovers (bQPE bCat mOut mMid mLow sUb : ℕ)
    {oRem mRem kZeroOut kZeroMid : ℕ}
    (rOutRem : QRegister oRem mOut) (rMidRem : QRegister mRem mMid)
    (haPos : 1 ≤ oRem + mRem) (hmPos : 1 ≤ mRem)
    (rOutZero : QRegister kZeroOut mOut) (rMidZero : QRegister kZeroMid mMid)
    (hOutCover : ∀ u : Fin mOut, u ∈ rOutRem.image ∨ u ∈ rOutZero.image)
    (hMidCover : ∀ v : Fin mMid, v ∈ rMidRem.image ∨ v ∈ rMidZero.image) :
    WalkReflCovers bQPE bCat mOut mMid mLow sUb
      (reducedOutMidWalkReflRegs bCat mOut mMid rOutRem rMidRem haPos hmPos)
      (liftOutMidZeroToAnc mOut mMid rOutZero rMidZero) := by
  let rAncZ := liftOutMidZeroToAnc mOut mMid rOutZero rMidZero
  let rWC := rWalkCatLoc bQPE bCat mOut mMid mLow (oRem + mRem) mRem sUb
  let rFull := rFullZeroLoc bQPE bCat mOut mMid mLow (oRem + mRem) mRem sUb rAncZ
  have hOutZeroMem (i : Fin kZeroOut) :
      (rWC.compose ((rWalkInWalkCat bCat mOut mMid).compose (rOutInWalk mOut mMid)))
        (rOutZero i) ∈ rFull.image := by
    have hEq : (rWC.compose ((rWalkInWalkCat bCat mOut mMid).compose (rOutInWalk mOut mMid)))
        (rOutZero i) =
        (rAncZeroLoc bQPE bCat mOut mMid mLow (oRem + mRem) mRem sUb rAncZ)
          (Fin.castAdd kZeroMid i) := by
      ext
      simp [rWC, rAncZeroLoc, rAncZ, liftOutMidZeroToAnc, inAllWalkCat,
        rOutInWalk, rAllInWalk]
    rw [hEq, image_rFullZeroLoc]
    exact Finset.mem_union_right _ ((QRegister.mem_image _ _).mpr ⟨Fin.castAdd kZeroMid i, rfl⟩)
  have hMidZeroMem (j : Fin kZeroMid) :
      ((rWC.compose (inMidWalkCat bCat mOut mMid)).compose rMidZero) j ∈ rFull.image := by
    have hEq : ((rWC.compose (inMidWalkCat bCat mOut mMid)).compose rMidZero) j =
        (rAncZeroLoc bQPE bCat mOut mMid mLow (oRem + mRem) mRem sUb rAncZ)
          (Fin.natAdd kZeroOut j) := by
      ext
      simp [rWC, rAncZeroLoc, rAncZ, liftOutMidZeroToAnc, inAllWalkCat, inMidWalkCat,
        rMidInWalk, rAllInWalk, add_assoc]
    rw [hEq, image_rFullZeroLoc]
    exact Finset.mem_union_right _ ((QRegister.mem_image _ _).mpr ⟨Fin.natAdd kZeroOut j, rfl⟩)
  constructor
  · ext w; simp only [Finset.mem_union, QRegister.mem_image]
    constructor
    · rintro (⟨i, rfl⟩ | hw)
      · exact Or.inl ⟨rMidRem i, rfl⟩
      · exact Or.inr hw
    · rintro (⟨u, rfl⟩ | hw)
      · rcases hMidCover u with hu | hu
        · obtain ⟨i, rfl⟩ := (QRegister.mem_image _ _).mp hu
          exact Or.inl ⟨i, rfl⟩
        · obtain ⟨j, rfl⟩ := (QRegister.mem_image _ _).mp hu
          exact Or.inr ((QRegister.mem_image _ _).mp (hMidZeroMem j))
      · exact Or.inr hw
  · ext w; simp only [Finset.mem_union, QRegister.mem_image]
    constructor
    · rintro (⟨p, rfl⟩ | hw)
      · rcases Comparators.fin_eq_castAdd_or_natAdd p with ⟨a, rfl⟩ | ⟨i, rfl⟩
        · refine Or.inl ⟨Fin.castAdd mMid (rOutRem a), ?_⟩
          ext
          simp [reducedOutMidWalkReflRegs, inAllWalkCat, rOutInWalk, rAllInWalk]
        · refine Or.inl ⟨Fin.natAdd mOut (rMidRem i), ?_⟩
          ext
          simp [reducedOutMidWalkReflRegs, inAllWalkCat, rMidInWalk, rAllInWalk, add_assoc]
      · exact Or.inr hw
    · rintro (⟨q, rfl⟩ | hw)
      · rcases Comparators.fin_eq_castAdd_or_natAdd q with ⟨a, rfl⟩ | ⟨u, rfl⟩
        · rcases hOutCover a with ha | ha
          · obtain ⟨i, rfl⟩ := (QRegister.mem_image _ _).mp ha
            refine Or.inl ⟨Fin.castAdd mRem i, ?_⟩
            ext
            simp [reducedOutMidWalkReflRegs, inAllWalkCat, rOutInWalk, rAllInWalk]
          · obtain ⟨i, rfl⟩ := (QRegister.mem_image _ _).mp ha
            have hEqW : (rWC.compose (inAllWalkCat bCat mOut mMid))
                  (Fin.castAdd mMid (rOutZero i)) =
                (rWC.compose ((rWalkInWalkCat bCat mOut mMid).compose (rOutInWalk mOut mMid)))
                  (rOutZero i) := by
              ext
              simp [inAllWalkCat, rOutInWalk, rAllInWalk]
            rw [hEqW]
            exact Or.inr ((QRegister.mem_image _ _).mp (hOutZeroMem i))
        · rcases hMidCover u with hu | hu
          · obtain ⟨i, rfl⟩ := (QRegister.mem_image _ _).mp hu
            refine Or.inl ⟨Fin.natAdd oRem i, ?_⟩
            ext
            simp [reducedOutMidWalkReflRegs, inAllWalkCat, rMidInWalk, rAllInWalk, add_assoc]
          · obtain ⟨j, rfl⟩ := (QRegister.mem_image _ _).mp hu
            have hEqW : (rWC.compose (inAllWalkCat bCat mOut mMid))
                  (Fin.natAdd mOut (rMidZero j)) =
                ((rWC.compose (inMidWalkCat bCat mOut mMid)).compose rMidZero) j := by
              ext
              simp [inAllWalkCat, inMidWalkCat, rMidInWalk, rAllInWalk, add_assoc]
            rw [hEqW]
            exact Or.inr ((QRegister.mem_image _ _).mp (hMidZeroMem j))
      · exact Or.inr hw

/-- Total ancilla count for `TopIntegrationBridge` specialized at `bCat = 11`. -/
abbrev cat11TotalAncillas (bQPE mOut mMid mLow aRem mRem sUb : ℕ) : ℕ :=
  totalAncillas bQPE 11 mOut mMid mLow aRem mRem sUb

/-- Total qubit count for `TopIntegrationBridge` specialized at `bCat = 11`. -/
abbrev cat11TotalQubits (bQPE mOut mMid mLow aRem mRem sUb : ℕ) : ℕ :=
  totalQubits bQPE 11 mOut mMid mLow aRem mRem sUb

end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.Cat11CompactPhase2Bridge
