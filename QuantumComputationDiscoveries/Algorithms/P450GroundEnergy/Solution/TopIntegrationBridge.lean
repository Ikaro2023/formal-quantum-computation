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
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.ChunkedPulledMaster11
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.Defs
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.FermionPerm
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.CatalystAndQFT
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.PerturbedQPEClosure
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.FastUniform

/-!
# Parametric Top-Level Integration & Perturbed QPE Bridge (`TopIntegrationBridge`)

This module provides the guard-free top-level register layout, in-place chunked dihedral walk
schedule, clean-zero ancilla lifting, and perturbed + scalar-shifted master correctness theorems for
`P450GroundEnergy`:

1. **Fully Parametric Register & Tightened Scratch Layout (`totalQubits`):**
   Parameterized directly by `(bQPE, bCat, mOut, mMid, mLow, aRem, mRem, sUb)` with **zero**
   lower-bound guards on `sUb` (`sUb` may be `0`, `42..105`, `183`, `184`, `193`, `194`, etc.),
   arbitrary QPE clock width `bQPE` (`15`, `16`, ...), arbitrary phase-gradient catalyst width
   `bCat` (`0`, `8..14`, ...), and arbitrary outer/inner ancilla widths `(mOut, mMid)`
   (supporting `(wOuter, wInner2) ∈ {(19, 26), (19, 10), (0, 10), (0, 0)}` as well as reduced-rank
   or
   BLISS block encodings). Tightens the top-chunk controlled-reflection scratch
   floor from `(1 + (16 - mLow - 2)) + (mAncUB - 1)` to
   `chunkedCtrlScrNeed bQPE mLow aRem = (1 + (bQPE - mLow - 2)) + (aRem - 1)`.
2. **Parametric In-Place Chunked Dihedral Schedule & Master Program:**
   Supports arbitrary `bQPE`, `cCat : Circuit bCat`, `pWin`, `cIqft : Circuit bQPE` (both standard
   `iqftCircuit` with `perm = Equiv.refl _` and `0`-SWAP `aqftOuterInv` with `perm = bitRevEquiv`),
   and clean-zero subregisters `rAncZero : QRegister kZero (mOut + mMid)` spanning any clean-zero
   wires in `(out, mid)`. Proves unconditional `.count .TOFF = 0` and explicit `T`-count bounds.
3. **Perturbed & Scalar-Shifted Master Correctness Theorems:**
   Connects any Hermitian blocked-basis effective Hamiltonian `H_tilde_blk` and optional real scalar
   shift `c_shift : ℝ` satisfying
   `AgreesOnElectronSector 58 63 (U_fswap⁻¹ * H_tilde_blk * U_fswap + (c_shift : ℂ) • 1)`
   `(thcHamiltonian P450.dfthc) δ_H` directly to
   `MeasuresLowEnergies_local (thcHamiltonian P450.dfthc) 63 0.1 0.001 W` and
   `RealizesUnitaryFromBasisOutcomesAndZeroWorkspace`, with **zero `M`-step amplification**
   of `δ_H`, covering both Luis–Peřina `OuterWeights.sineWindow (2 ^ bQPE) M` (`M + 2 ≤ 2 ^ bQPE`)
   and general QPE windows (including `0`-ancilla `SineQPE.sineWindowCoeff (M + 1)`).
-/

@[expose] public section

namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.TopIntegrationBridge
open QuantumComputation.Specs QuantumComputation.Specs.P450

open Operator Matrix Real WalkQPEBridge WalkQPEBridgeXMeas WalkQPEFlexBridge
open QuantumComputation.Specs.P450 QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution
open scoped Matrix BigOperators Matrix.Norms.L2Operator

local instance (priority := 1000000) instNeZeroTwoPow (k : ℕ) : NeZero (2 ^ k) :=
  ⟨Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos k)⟩

/-! ## Section 1: Parametric Register & Tightened Scratch Layout -/

/-- Combined `(out, mid)` block-encoding ancilla width `mOut + mMid`. -/
abbrev walkAncillas (mOut mMid : ℕ) : ℕ := mOut + mMid

/-- Uncatalyzed walk register width `systemQubits_local + (mOut + mMid)`. -/
abbrev walkWidth (mOut mMid : ℕ) : ℕ :=
  systemQubits_local + walkAncillas mOut mMid

/-- Catalyzed walk register width `(systemQubits_local + (mOut + mMid)) + bCat`. -/
abbrev walkCatWidth (bCat mOut mMid : ℕ) : ℕ :=
  walkWidth mOut mMid + bCat

/-- Active (non-scratch) ancilla count `(mOut + mMid) + bCat + bQPE`. -/
abbrev actAncillas (bQPE bCat mOut mMid : ℕ) : ℕ :=
  walkAncillas mOut mMid + bCat + bQPE

/-- Active qubit width `systemQubits_local + ((mOut + mMid) + bCat + bQPE)`. -/
abbrev actWidth (bQPE bCat mOut mMid : ℕ) : ℕ :=
  systemQubits_local + actAncillas bQPE bCat mOut mMid

/-- Tightened scratch wires required by in-place `< r` top-chunk controlled `R₀`:
`1` comparator flag + `(bQPE - mLow - 2)` comparator carries + `(aRem - 1)` `qpePatReflInDyn`
controls, using `aRem - 1` instead of `mOut + mMid - 1`. -/
abbrev chunkedCtrlScrNeed (bQPE mLow aRem : ℕ) : ℕ :=
  (1 + (bQPE - mLow - 2)) + (aRem - 1)

/-- Guard-free clean scratch ancilla count:
`max sUb (max (mRem - 2) (chunkedCtrlScrNeed bQPE mLow aRem))`. -/
abbrev scrAncillas (bQPE mLow aRem mRem sUb : ℕ) : ℕ :=
  max sUb (max (mRem - 2) (chunkedCtrlScrNeed bQPE mLow aRem))

/-- Total top-level ancilla count `actAncillas + scrAncillas`. -/
abbrev totalAncillas (bQPE bCat mOut mMid mLow aRem mRem sUb : ℕ) : ℕ :=
  actAncillas bQPE bCat mOut mMid + scrAncillas bQPE mLow aRem mRem sUb

/-- Total top-level qubit count `systemQubits_local + totalAncillas`. -/
abbrev totalQubits (bQPE bCat mOut mMid mLow aRem mRem sUb : ℕ) : ℕ :=
  systemQubits_local + totalAncillas bQPE bCat mOut mMid mLow aRem mRem sUb

theorem actWidth_eq (bQPE bCat mOut mMid : ℕ) :
    actWidth bQPE bCat mOut mMid = walkCatWidth bCat mOut mMid + bQPE := by
  dsimp [actWidth, actAncillas, walkCatWidth, walkWidth, walkAncillas]
  omega

theorem scr_ge_sUb (bQPE mLow aRem mRem sUb : ℕ) :
    sUb ≤ scrAncillas bQPE mLow aRem mRem sUb :=
  le_max_left _ _

theorem scr_ge_chunked (bQPE mLow aRem mRem sUb : ℕ) :
    chunkedCtrlScrNeed bQPE mLow aRem ≤ scrAncillas bQPE mLow aRem mRem sUb :=
  (le_max_right _ _).trans (le_max_right _ _)

theorem scr_ge_reflIn (bQPE mLow aRem mRem sUb : ℕ) :
    aRem - 2 ≤ scrAncillas bQPE mLow aRem mRem sUb := by
  have h : aRem - 2 ≤ chunkedCtrlScrNeed bQPE mLow aRem := by
    dsimp [chunkedCtrlScrNeed]; omega
  exact h.trans (scr_ge_chunked bQPE mLow aRem mRem sUb)

theorem scr_ge_lowCtrl (bQPE mLow aRem mRem sUb : ℕ) :
    (1 - 1) + (aRem - 1) ≤ scrAncillas bQPE mLow aRem mRem sUb := by
  have h : (1 - 1) + (aRem - 1) ≤ chunkedCtrlScrNeed bQPE mLow aRem := by
    dsimp [chunkedCtrlScrNeed]; omega
  exact h.trans (scr_ge_chunked bQPE mLow aRem mRem sUb)

/-- System `116`-qubit register inside `walkWidth mOut mMid`. -/
abbrev rSysInWalk (mOut mMid : ℕ) : QRegister systemQubits_local (walkWidth mOut mMid) :=
  .block 0 systemQubits_local (by dsimp [walkWidth]; omega)

/-- Outer ancilla register `mOut` inside `walkWidth mOut mMid`. -/
abbrev rOutInWalk (mOut mMid : ℕ) : QRegister mOut (walkWidth mOut mMid) :=
  .block systemQubits_local mOut (by dsimp [walkWidth, walkAncillas]; omega)

/-- Inner/mid ancilla register `mMid` inside `walkWidth mOut mMid`. -/
abbrev rMidInWalk (mOut mMid : ℕ) : QRegister mMid (walkWidth mOut mMid) :=
  .block (systemQubits_local + mOut) mMid (by dsimp [walkWidth, walkAncillas]; omega)

/-- Full `(mOut + mMid)` walk ancilla register inside `walkWidth mOut mMid`. -/
abbrev rAllInWalk (mOut mMid : ℕ) : QRegister (mOut + mMid) (walkWidth mOut mMid) :=
  .block systemQubits_local (mOut + mMid) le_rfl

/-- Uncatalyzed walk subregister inside `walkCatWidth bCat mOut mMid`. -/
abbrev rWalkInWalkCat (bCat mOut mMid : ℕ) :
    QRegister (walkWidth mOut mMid) (walkCatWidth bCat mOut mMid) :=
  .block 0 (walkWidth mOut mMid) (by dsimp [walkCatWidth]; omega)

/-- Phase-gradient catalyst subregister inside `walkCatWidth bCat mOut mMid`. -/
abbrev rCatInWalkCat (bCat mOut mMid : ℕ) :
    QRegister bCat (walkCatWidth bCat mOut mMid) :=
  .block (walkWidth mOut mMid) bCat (by dsimp [walkCatWidth]; omega)

/-- Mid ancilla subregister inside `walkCatWidth bCat mOut mMid`. -/
abbrev inMidWalkCat (bCat mOut mMid : ℕ) : QRegister mMid (walkCatWidth bCat mOut mMid) :=
  (rWalkInWalkCat bCat mOut mMid).compose (rMidInWalk mOut mMid)

/-- Full `(mOut + mMid)` ancilla subregister inside `walkCatWidth bCat mOut mMid`. -/
abbrev inAllWalkCat (bCat mOut mMid : ℕ) :
    QRegister (mOut + mMid) (walkCatWidth bCat mOut mMid) :=
  (rWalkInWalkCat bCat mOut mMid).compose (rAllInWalk mOut mMid)

/-- Catalyzed walk subregister inside `actWidth bQPE bCat mOut mMid`. -/
abbrev rWalkCatInAct (bQPE bCat mOut mMid : ℕ) :
    QRegister (walkCatWidth bCat mOut mMid) (actWidth bQPE bCat mOut mMid) :=
  .block 0 (walkCatWidth bCat mOut mMid) (by
    dsimp [actWidth, actAncillas, walkCatWidth, walkWidth, walkAncillas]; omega)

/-- Catalyst subregister inside `actWidth bQPE bCat mOut mMid`. -/
abbrev rCatInAct (bQPE bCat mOut mMid : ℕ) :
    QRegister bCat (actWidth bQPE bCat mOut mMid) :=
  .block (walkWidth mOut mMid) bCat (by
    dsimp [actWidth, actAncillas, walkWidth, walkAncillas]; omega)

/-- `bQPE`-qubit QPE phase subregister inside `actWidth bQPE bCat mOut mMid`. -/
abbrev rQPEInAct (bQPE bCat mOut mMid : ℕ) :
    QRegister bQPE (actWidth bQPE bCat mOut mMid) :=
  .block (walkCatWidth bCat mOut mMid) bQPE (by
    dsimp [actWidth, actAncillas, walkCatWidth, walkWidth, walkAncillas]; omega)

/-- `bQPE`-qubit QPE phase subregister inside `actAncillas bQPE bCat mOut mMid`. -/
abbrev rQPEInAnc (bQPE bCat mOut mMid : ℕ) :
    QRegister bQPE (actAncillas bQPE bCat mOut mMid) :=
  .block (walkAncillas mOut mMid + bCat) bQPE (by dsimp [actAncillas]; omega)

/-- Active register block `0 .. actWidth - 1` inside `totalQubits`. -/
abbrev rActLoc (bQPE bCat mOut mMid mLow aRem mRem sUb : ℕ) :
    QRegister (actWidth bQPE bCat mOut mMid)
      (totalQubits bQPE bCat mOut mMid mLow aRem mRem sUb) :=
  .block 0 (actWidth bQPE bCat mOut mMid) (by
    dsimp [totalQubits, totalAncillas, actWidth]; omega)

/-- Clean scratch register block inside `totalQubits`. -/
abbrev rScrLoc (bQPE bCat mOut mMid mLow aRem mRem sUb : ℕ) :
    QRegister (scrAncillas bQPE mLow aRem mRem sUb)
      (totalQubits bQPE bCat mOut mMid mLow aRem mRem sUb) :=
  .block (actWidth bQPE bCat mOut mMid) (scrAncillas bQPE mLow aRem mRem sUb) (by
    dsimp [totalQubits, totalAncillas, actWidth]; omega)

/-- First `sUb` clean scratch wires inside `rScrLoc` passed to `pFwd` and `pBwd` (with zero
lower-bound guards on `sUb`). -/
abbrev rScrUbLoc (bQPE bCat mOut mMid mLow aRem mRem sUb : ℕ) :
    QRegister sUb (totalQubits bQPE bCat mOut mMid mLow aRem mRem sUb) :=
  (rScrLoc bQPE bCat mOut mMid mLow aRem mRem sUb).compose
    (.block 0 sUb (by have := scr_ge_sUb bQPE mLow aRem mRem sUb; omega))

/-- Catalyzed walk register inside `totalQubits`. -/
abbrev rWalkCatLoc (bQPE bCat mOut mMid mLow aRem mRem sUb : ℕ) :
    QRegister (walkCatWidth bCat mOut mMid)
      (totalQubits bQPE bCat mOut mMid mLow aRem mRem sUb) :=
  (rActLoc bQPE bCat mOut mMid mLow aRem mRem sUb).compose (rWalkCatInAct bQPE bCat mOut mMid)

/-- Catalyst register inside `totalQubits`. -/
abbrev rCatLoc (bQPE bCat mOut mMid mLow aRem mRem sUb : ℕ) :
    QRegister bCat (totalQubits bQPE bCat mOut mMid mLow aRem mRem sUb) :=
  (rActLoc bQPE bCat mOut mMid mLow aRem mRem sUb).compose (rCatInAct bQPE bCat mOut mMid)

/-- QPE phase register inside `totalQubits`. -/
abbrev rQPELoc (bQPE bCat mOut mMid mLow aRem mRem sUb : ℕ) :
    QRegister bQPE (totalQubits bQPE bCat mOut mMid mLow aRem mRem sUb) :=
  (rActLoc bQPE bCat mOut mMid mLow aRem mRem sUb).compose (rQPEInAct bQPE bCat mOut mMid)

/-- Local embedding of any clean-zero ancilla subregister `rAncZero : QRegister kZero (mOut + mMid)`
inside `inAllWalkCat`. -/
abbrev rAncZeroLoc (bQPE bCat mOut mMid mLow aRem mRem sUb : ℕ) {kZero : ℕ}
    (rAncZero : QRegister kZero (mOut + mMid)) :
    QRegister kZero (totalQubits bQPE bCat mOut mMid mLow aRem mRem sUb) :=
  ((rWalkCatLoc bQPE bCat mOut mMid mLow aRem mRem sUb).compose
    (inAllWalkCat bCat mOut mMid)).compose rAncZero

theorem rQPEInAct_disjoint_rWalkCatInAct (bQPE bCat mOut mMid : ℕ) :
    (rQPEInAct bQPE bCat mOut mMid).DisjointWires (rWalkCatInAct bQPE bCat mOut mMid) := by
  rw [QRegister.disjoint_iff]; intro i j hij
  have hv := congrArg Fin.val hij
  simp [rQPEInAct, rWalkCatInAct] at hv; omega

theorem rWalkInWalkCat_disjoint_rCatInWalkCat (bCat mOut mMid : ℕ) :
    (rWalkInWalkCat bCat mOut mMid).DisjointWires (rCatInWalkCat bCat mOut mMid) := by
  rw [QRegister.disjoint_iff]; intro i j hij
  have hv := congrArg Fin.val hij
  simp [rWalkInWalkCat, rCatInWalkCat] at hv; omega

theorem rActLoc_disjoint_rScrLoc (bQPE bCat mOut mMid mLow aRem mRem sUb : ℕ) :
    (rActLoc bQPE bCat mOut mMid mLow aRem mRem sUb).DisjointWires
      (rScrLoc bQPE bCat mOut mMid mLow aRem mRem sUb) := by
  rw [QRegister.disjoint_iff]; intro i j hij
  have hv := congrArg Fin.val hij
  simp [rActLoc, rScrLoc] at hv; omega

theorem rQPELoc_disjoint_rWalkCatLoc (bQPE bCat mOut mMid mLow aRem mRem sUb : ℕ) :
    (rQPELoc bQPE bCat mOut mMid mLow aRem mRem sUb).DisjointWires
      (rWalkCatLoc bQPE bCat mOut mMid mLow aRem mRem sUb) := by
  rw [QRegister.disjoint_iff]; intro i j
  exact (rActLoc bQPE bCat mOut mMid mLow aRem mRem sUb).wires.injective.ne
    ((rQPEInAct_disjoint_rWalkCatInAct bQPE bCat mOut mMid).ne i j)

theorem rQPELoc_disjoint_rScrLoc (bQPE bCat mOut mMid mLow aRem mRem sUb : ℕ) :
    (rQPELoc bQPE bCat mOut mMid mLow aRem mRem sUb).DisjointWires
      (rScrLoc bQPE bCat mOut mMid mLow aRem mRem sUb) :=
  QubitisedWalk.disjointWires_compose_left
    (rActLoc_disjoint_rScrLoc bQPE bCat mOut mMid mLow aRem mRem sUb)

theorem rWalkCatLoc_disjoint_rScrLoc (bQPE bCat mOut mMid mLow aRem mRem sUb : ℕ) :
    (rWalkCatLoc bQPE bCat mOut mMid mLow aRem mRem sUb).DisjointWires
      (rScrLoc bQPE bCat mOut mMid mLow aRem mRem sUb) :=
  QubitisedWalk.disjointWires_compose_left
    (rActLoc_disjoint_rScrLoc bQPE bCat mOut mMid mLow aRem mRem sUb)

theorem rAncZeroLoc_val_bounds (bQPE bCat mOut mMid mLow aRem mRem sUb : ℕ) {kZero : ℕ}
    (rAncZero : QRegister kZero (mOut + mMid)) (j : Fin kZero) :
    systemQubits_local ≤ (rAncZeroLoc bQPE bCat mOut mMid mLow aRem mRem sUb rAncZero j).val ∧
      (rAncZeroLoc bQPE bCat mOut mMid mLow aRem mRem sUb rAncZero j).val <
        walkWidth mOut mMid := by
  have hj := (rAncZero j).isLt
  simp only [rAncZeroLoc, rWalkCatLoc, rActLoc, rWalkCatInAct, inAllWalkCat, rWalkInWalkCat,
    rAllInWalk, walkWidth, walkAncillas, QRegister.compose_apply, QRegister.block_apply_val]
  omega

theorem rScrLoc_disjoint_rAncZeroLoc (bQPE bCat mOut mMid mLow aRem mRem sUb : ℕ) {kZero : ℕ}
    (rAncZero : QRegister kZero (mOut + mMid)) :
    (rScrLoc bQPE bCat mOut mMid mLow aRem mRem sUb).DisjointWires
      (rAncZeroLoc bQPE bCat mOut mMid mLow aRem mRem sUb rAncZero) :=
  QRegister.disjoint_comm.mp
    (QubitisedWalk.disjointWires_compose_left
      (QubitisedWalk.disjointWires_compose_left
        (rWalkCatLoc_disjoint_rScrLoc bQPE bCat mOut mMid mLow aRem mRem sUb)))

theorem rScrUbLoc_disjoint_rAncZeroLoc (bQPE bCat mOut mMid mLow aRem mRem sUb : ℕ) {kZero : ℕ}
    (rAncZero : QRegister kZero (mOut + mMid)) :
    (rScrUbLoc bQPE bCat mOut mMid mLow aRem mRem sUb).DisjointWires
      (rAncZeroLoc bQPE bCat mOut mMid mLow aRem mRem sUb rAncZero) :=
  (rScrLoc_disjoint_rAncZeroLoc bQPE bCat mOut mMid mLow aRem mRem sUb rAncZero).compose_left _

/-- Combined `(sUb + kZero)`-wire clean-zero register for `pFwd` and `pBwd`. -/
abbrev rUbZeroLoc (bQPE bCat mOut mMid mLow aRem mRem sUb : ℕ) {kZero : ℕ}
    (rAncZero : QRegister kZero (mOut + mMid)) :
    QRegister (sUb + kZero) (totalQubits bQPE bCat mOut mMid mLow aRem mRem sUb) :=
  (rScrUbLoc bQPE bCat mOut mMid mLow aRem mRem sUb).concat
    (rAncZeroLoc bQPE bCat mOut mMid mLow aRem mRem sUb rAncZero)
    (rScrUbLoc_disjoint_rAncZeroLoc bQPE bCat mOut mMid mLow aRem mRem sUb rAncZero)

/-- Combined `(scrAncillas + kZero)`-wire clean-zero register maintained across the local
master circuit. -/
abbrev rFullZeroLoc (bQPE bCat mOut mMid mLow aRem mRem sUb : ℕ) {kZero : ℕ}
    (rAncZero : QRegister kZero (mOut + mMid)) :
    QRegister (scrAncillas bQPE mLow aRem mRem sUb + kZero)
      (totalQubits bQPE bCat mOut mMid mLow aRem mRem sUb) :=
  (rScrLoc bQPE bCat mOut mMid mLow aRem mRem sUb).concat
    (rAncZeroLoc bQPE bCat mOut mMid mLow aRem mRem sUb rAncZero)
    (rScrLoc_disjoint_rAncZeroLoc bQPE bCat mOut mMid mLow aRem mRem sUb rAncZero)

theorem image_rUbZeroLoc (bQPE bCat mOut mMid mLow aRem mRem sUb : ℕ) {kZero : ℕ}
    (rAncZero : QRegister kZero (mOut + mMid)) :
    (rUbZeroLoc bQPE bCat mOut mMid mLow aRem mRem sUb rAncZero).image =
      (rScrUbLoc bQPE bCat mOut mMid mLow aRem mRem sUb).image ∪
        (rAncZeroLoc bQPE bCat mOut mMid mLow aRem mRem sUb rAncZero).image :=
  QRegister.image_concat _ _ _

theorem image_rFullZeroLoc (bQPE bCat mOut mMid mLow aRem mRem sUb : ℕ) {kZero : ℕ}
    (rAncZero : QRegister kZero (mOut + mMid)) :
    (rFullZeroLoc bQPE bCat mOut mMid mLow aRem mRem sUb rAncZero).image =
      (rScrLoc bQPE bCat mOut mMid mLow aRem mRem sUb).image ∪
        (rAncZeroLoc bQPE bCat mOut mMid mLow aRem mRem sUb rAncZero).image :=
  QRegister.image_concat _ _ _

/-! ## Section 2: Reflection Register Bundles & Coin-Width Presets -/

/-- Active reflection subregisters inside `walkCatWidth bCat mOut mMid` (`aRem` wires for `R₀`,
`mRem` wires for `R_mid`). -/
structure WalkReflRegs (bCat mOut mMid aRem mRem : ℕ) where
  /-- Active `(out, mid)` reflection subregister for `reflIn` and `ctrlR0`. -/
  inAll : QRegister aRem (walkCatWidth bCat mOut mMid)
  /-- Active `mid` reflection subregister for `reflMid`. -/
  inMid : QRegister mRem (walkCatWidth bCat mOut mMid)
  /-- Nonempty `inAll` width (`1 ≤ aRem`). -/
  haPos : 1 ≤ aRem
  /-- Nonempty `inMid` width (`1 ≤ mRem`). -/
  hmPos : 1 ≤ mRem

/-- Coverage predicate ensuring that `refl.inMid` and `refl.inAll` agree with `inMidWalkCat` and
`inAllWalkCat` whenever `rFullZeroLoc` is in `|0⟩`. -/
def WalkReflCovers (bQPE bCat mOut mMid mLow sUb : ℕ) {aRem mRem kZero : ℕ}
    (refl : WalkReflRegs bCat mOut mMid aRem mRem)
    (rAncZero : QRegister kZero (mOut + mMid)) : Prop :=
  ((rWalkCatLoc bQPE bCat mOut mMid mLow aRem mRem sUb).compose refl.inMid).image ∪
      (rFullZeroLoc bQPE bCat mOut mMid mLow aRem mRem sUb rAncZero).image =
    ((rWalkCatLoc bQPE bCat mOut mMid mLow aRem mRem sUb).compose
      (inMidWalkCat bCat mOut mMid)).image ∪
      (rFullZeroLoc bQPE bCat mOut mMid mLow aRem mRem sUb rAncZero).image ∧
  ((rWalkCatLoc bQPE bCat mOut mMid mLow aRem mRem sUb).compose refl.inAll).image ∪
      (rFullZeroLoc bQPE bCat mOut mMid mLow aRem mRem sUb rAncZero).image =
    ((rWalkCatLoc bQPE bCat mOut mMid mLow aRem mRem sUb).compose
      (inAllWalkCat bCat mOut mMid)).image ∪
      (rFullZeroLoc bQPE bCat mOut mMid mLow aRem mRem sUb rAncZero).image

/-- Uncontrolled walk step `R₀ * R₂` on `rWalkCatLoc` built from an arbitrary fused inner-reflection
circuit `pRefl2` (such as keeping `rHotCtx : 126` unary wires live across `reflMidDyn`). -/
def wStepRefl2Dyn {Var : Type} (bQPE bCat mOut mMid mLow sUb : ℕ) (v : Var)
    {aRem mRem : ℕ} (refl : WalkReflRegs bCat mOut mMid aRem mRem)
    (pRefl2 : DynamicCircuit Var (totalQubits bQPE bCat mOut mMid mLow aRem mRem sUb)) :
    DynamicCircuit Var (totalQubits bQPE bCat mOut mMid mLow aRem mRem sUb) :=
  .seq pRefl2
    (QubitisedWalk.reflInDyn v
      ((rWalkCatLoc bQPE bCat mOut mMid mLow aRem mRem sUb).compose refl.inAll)
      (rScrLoc bQPE bCat mOut mMid mLow aRem mRem sUb)
      refl.haPos (scr_ge_reflIn bQPE mLow aRem mRem sUb)
      (QubitisedWalk.disjointWires_compose_left
        (rWalkCatLoc_disjoint_rScrLoc bQPE bCat mOut mMid mLow aRem mRem sUb)))

/-- Zero-controlled reflection `R₀` on `rWalkCatLoc` when `rQPELoc idx = 0` (`0` `X` gates). -/
def lowBitCtrlR0Dyn {Var : Type} (bQPE bCat mOut mMid mLow sUb : ℕ) (v : Var)
    {aRem mRem : ℕ} (refl : WalkReflRegs bCat mOut mMid aRem mRem) (idx : Fin bQPE) :
    DynamicCircuit Var (totalQubits bQPE bCat mOut mMid mLow aRem mRem sUb) :=
  QubitisedWalk.reflInOnlyAtZeroDyn v
    (QRegister.singleton ((rQPELoc bQPE bCat mOut mMid mLow aRem mRem sUb) idx))
    ((rWalkCatLoc bQPE bCat mOut mMid mLow aRem mRem sUb).compose refl.inAll)
    (rScrLoc bQPE bCat mOut mMid mLow aRem mRem sUb)
    (by decide) refl.haPos (scr_ge_lowCtrl bQPE mLow aRem mRem sUb)
    (QRegister.disjoint_iff.mpr fun _ j ↦
      (QubitisedWalk.disjointWires_compose_right
        (rQPELoc_disjoint_rWalkCatLoc bQPE bCat mOut mMid mLow aRem mRem sUb)).ne idx j)
    (QRegister.disjoint_iff.mpr fun _ j ↦
      (rQPELoc_disjoint_rScrLoc bQPE bCat mOut mMid mLow aRem mRem sUb).ne idx j)
    (QubitisedWalk.disjointWires_compose_left
      (rWalkCatLoc_disjoint_rScrLoc bQPE bCat mOut mMid mLow aRem mRem sUb))

theorem wStepRefl2Dyn_count_toff {Var : Type} (bQPE bCat mOut mMid mLow sUb : ℕ) (v : Var)
    {aRem mRem : ℕ} (refl : WalkReflRegs bCat mOut mMid aRem mRem)
    (pRefl2 : DynamicCircuit Var (totalQubits bQPE bCat mOut mMid mLow aRem mRem sUb)) :
    (wStepRefl2Dyn bQPE bCat mOut mMid mLow sUb v refl pRefl2).count .TOFF =
      pRefl2.count .TOFF := by
  simp [wStepRefl2Dyn]

theorem wStepRefl2Dyn_count_t {Var : Type} (bQPE bCat mOut mMid mLow sUb : ℕ) (v : Var)
    {aRem mRem : ℕ} (refl : WalkReflRegs bCat mOut mMid aRem mRem)
    (pRefl2 : DynamicCircuit Var (totalQubits bQPE bCat mOut mMid mLow aRem mRem sUb)) :
    (wStepRefl2Dyn bQPE bCat mOut mMid mLow sUb v refl pRefl2).count .T =
      pRefl2.count .T + 4 * (aRem - 2) := by
  simp [wStepRefl2Dyn]

@[simp]
theorem lowBitCtrlR0Dyn_count_toff {Var : Type} (bQPE bCat mOut mMid mLow sUb : ℕ) (v : Var)
    {aRem mRem : ℕ} (refl : WalkReflRegs bCat mOut mMid aRem mRem) (idx : Fin bQPE) :
    (lowBitCtrlR0Dyn bQPE bCat mOut mMid mLow sUb v refl idx).count .TOFF = 0 := by
  simp [lowBitCtrlR0Dyn]

@[simp]
theorem lowBitCtrlR0Dyn_count_t {Var : Type} (bQPE bCat mOut mMid mLow sUb : ℕ) (v : Var)
    {aRem mRem : ℕ} (refl : WalkReflRegs bCat mOut mMid aRem mRem) (idx : Fin bQPE) :
    (lowBitCtrlR0Dyn bQPE bCat mOut mMid mLow sUb v refl idx).count .T = 4 * (aRem - 1) := by
  simp [lowBitCtrlR0Dyn]

/-- Clock-fiber unitary on `Fin (2 ^ bQPE)` for one dihedral chunk step of length `m` gated on
`pred`. -/
noncomputable def chunkFiberStep {bQPE d : ℕ} (pred : Fin (2 ^ bQPE) → Bool) (m : ℕ)
    (U R₀ : Unitary d) (x : Fin (2 ^ bQPE)) : Unitary d :=
  if pred x then (R₀ * U ^ m) * R₀ else U ^ m

section CleanZeroLifting

private theorem basisOutcomeProjector_comm2 {N k₁ k₂ : ℕ}
    (r₁ : QRegister k₁ N) (m₁ : Fin (2 ^ k₁))
    (r₂ : QRegister k₂ N) (m₂ : Fin (2 ^ k₂)) :
    r₁.basisOutcomeProjector m₁ * r₂.basisOutcomeProjector m₂ =
      r₂.basisOutcomeProjector m₂ * r₁.basisOutcomeProjector m₁ := by
  rw [r₁.basisOutcomeProjector_eq_diagonal, r₂.basisOutcomeProjector_eq_diagonal,
    Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1; funext g; ring

private theorem absorbCleanActive_of_comm2 {Var : Type} [Fintype Var] [DecidableEq Var]
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

/-- Lifts `CleanRealizes` on any subregister `(rScrLoc ...).compose rSub` to the full scratch
register `rScrLoc` for `pWin`. -/
theorem cleanRealizes_rScrLoc_of_sub {Var : Type} [Fintype Var] [DecidableEq Var]
    (bQPE bCat mOut mMid mLow aRem mRem sUb : ℕ) (v : Var) {sWin : ℕ}
    (rSub : QRegister sWin (scrAncillas bQPE mLow aRem mRem sUb))
    {uWin : Unitary (2 ^ bQPE)}
    {pWin : DynamicCircuit Var (totalQubits bQPE bCat mOut mMid mLow aRem mRem sUb)}
    (h : CleanDyn.CleanRealizes v (rQPELoc bQPE bCat mOut mMid mLow aRem mRem sUb)
      ((rScrLoc bQPE bCat mOut mMid mLow aRem mRem sUb).compose rSub) uWin pWin) :
    CleanDyn.CleanRealizes v (rQPELoc bQPE bCat mOut mMid mLow aRem mRem sUb)
      (rScrLoc bQPE bCat mOut mMid mLow aRem mRem sUb) uWin pWin :=
  absorbCleanActive_of_comm2 h
    ((rScrLoc bQPE bCat mOut mMid mLow aRem mRem sUb).image_compose_subset rSub)
    (QubitisedWalk.basisOutcomeProjector_comm_embedMatrix
      (rScrLoc bQPE bCat mOut mMid mLow aRem mRem sUb)
      (rQPELoc bQPE bCat mOut mMid mLow aRem mRem sUb)
      (QRegister.disjoint_comm.mp
        (rQPELoc_disjoint_rScrLoc bQPE bCat mOut mMid mLow aRem mRem sUb))
      0 uWin.1).symm

/-- Adapter converting a standard `CleanDyn.CleanRealizes` proof on `(rWalkCatLoc, rScrUbLoc)`
into `CleanRealizesSet` with a `0`-wire `rAncZero` (`emptyAncZeroReg`). -/
theorem cleanRealizesSet_of_rScrUbLoc {Var : Type} [Fintype Var] [DecidableEq Var]
    (bQPE bCat mOut mMid mLow aRem mRem sUb : ℕ) (v : Var)
    (rAncZero : QRegister 0 (mOut + mMid))
    {u : Unitary (2 ^ walkCatWidth bCat mOut mMid)}
    {P : DynamicCircuit Var (totalQubits bQPE bCat mOut mMid mLow aRem mRem sUb)}
    (h : CleanDyn.CleanRealizes v (rWalkCatLoc bQPE bCat mOut mMid mLow aRem mRem sUb)
      (rScrUbLoc bQPE bCat mOut mMid mLow aRem mRem sUb) u P) :
    SelectSwapQROM.CleanRealizesSet v
      ((rScrUbLoc bQPE bCat mOut mMid mLow aRem mRem sUb).image ∪
        (rAncZeroLoc bQPE bCat mOut mMid mLow aRem mRem sUb rAncZero).image)
      ((rWalkCatLoc bQPE bCat mOut mMid mLow aRem mRem sUb).embedUnitary u) P := by
  have hemp : (rAncZeroLoc bQPE bCat mOut mMid mLow aRem mRem sUb rAncZero).image = ∅ := by
    ext w
    simp only [QRegister.mem_image, Finset.notMem_empty, iff_false]
    rintro ⟨i, _⟩
    exact Fin.elim0 i
  rw [hemp, Finset.union_empty]
  exact (SelectSwapQROM.cleanRealizes_iff_set v
    (rWalkCatLoc bQPE bCat mOut mMid mLow aRem mRem sUb)
    (rScrUbLoc bQPE bCat mOut mMid mLow aRem mRem sUb) u P).mp h

private theorem preserves_basisOutcomeProjector_of_cleanRealizes
    {Var : Type} [Fintype Var] [DecidableEq Var] {N k s : ℕ}
    {v : Var} {rAct : QRegister k N} {rScr : QRegister s N}
    {U : Unitary (2 ^ k)} {P : DynamicCircuit Var N}
    (h : CleanDyn.CleanRealizes v rAct rScr U P) :
    rScr.basisOutcomeProjector 0 * ((rAct.embedUnitary U).1 * rScr.basisOutcomeProjector 0) =
      (rAct.embedUnitary U).1 * rScr.basisOutcomeProjector 0 := by
  let P₀ := rScr.basisOutcomeProjector 0
  let W := (rAct.embedUnitary U).1
  let Θ : QCAssertion Var (2 ^ N) := fun _ ↦ XMeasCircuit.CleanRealizes.dirtyObservable rScr
  have hP₀_herm : P₀ᴴ = P₀ := rScr.basisOutcomeProjector_conjTranspose 0
  have hP₀_idem : P₀ * P₀ = P₀ := rScr.basisOutcomeProjector_mul_self 0
  have heq : restrictAssertionToZeroAncilla
      (qcWpQAssign (rAct.embedUnitary U) (restrictAssertionToZeroAncilla Θ rScr)) rScr =
      restrictAssertionToZeroAncilla (qcWpQAssign (rAct.embedUnitary U) Θ) rScr := by
    rw [← h.2.2.1 (restrictAssertionToZeroAncilla Θ rScr) (fun _ _ ↦ rfl), h.2.2.2 Θ,
      h.2.2.1 Θ (fun _ _ ↦ rfl)]
  have hmat := congrArg (fun A : QCAssertion Var (2 ^ N) ↦ (A (fun _ ↦ 0)).1.mat) heq
  simp only [Θ, restrictAssertionToZeroAncilla_coe, qcWpQAssign, qcQAssignObsMap,
    Observable.conj_coe, Unitary.coe_star, Matrix.star_eq_conjTranspose,
    HermitianMat.conj_apply_mat, XMeasCircuit.CleanRealizes.dirtyObservable_mat] at hmat
  change P₀ * (Wᴴ * (P₀ * (1 - P₀) * P₀ᴴ) * Wᴴᴴ) * P₀ᴴ =
    P₀ * (Wᴴ * (1 - P₀) * Wᴴᴴ) * P₀ᴴ at hmat
  rw [hP₀_herm, Matrix.conjTranspose_conjTranspose] at hmat
  have hmid0 : P₀ * (1 - P₀) * P₀ = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, hP₀_idem, sub_self, Matrix.zero_mul]
  rw [hmid0, Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_zero, Matrix.zero_mul] at hmat
  have hidem : (1 - P₀) * (1 - P₀) = 1 - P₀ := by
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hP₀_idem,
      sub_self, sub_zero]
  let B : Matrix (Fin (2 ^ N)) (Fin (2 ^ N)) ℂ := (1 - P₀) * W * P₀
  have hBsq : Bᴴ * B = 0 := by
    dsimp only [B]
    calc ((1 - P₀) * W * P₀)ᴴ * ((1 - P₀) * W * P₀)
        = P₀ * (Wᴴ * ((1 - P₀) * (1 - P₀)) * W) * P₀ := by
          simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_sub,
            Matrix.conjTranspose_one, hP₀_herm, Matrix.mul_assoc]
      _ = P₀ * (Wᴴ * (1 - P₀) * W) * P₀ := by rw [hidem]
      _ = 0 := hmat.symm
  have hB0 : B = 0 := by
    ext i j
    have hdiag : (Bᴴ * B) j j = 0 := by rw [hBsq]; rfl
    have hre : ∑ k, Complex.normSq (B k j) = 0 := by
      have hsum : (∑ k, (Complex.normSq (B k j) : ℂ)) = 0 := by
        simpa only [Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.star_def,
          Complex.normSq_eq_conj_mul_self] using hdiag
      exact_mod_cast hsum
    have ht := (Finset.sum_eq_zero_iff_of_nonneg fun k _ ↦
      Complex.normSq_nonneg (B k j)).mp hre i (Finset.mem_univ i)
    exact Complex.normSq_eq_zero.mp ht
  exact (sub_eq_zero.mp (by
    simpa only [B, Matrix.mul_assoc, Matrix.sub_mul, Matrix.one_mul] using hB0)).symm

/-- Lifts `CleanRealizesSet` on `(rScrUbLoc ...).image ∪ (rAncZeroLoc ...).image` to
`XMeasCircuit.CleanRealizes` on `(rWalkCatLoc, rFullZeroLoc)`. -/
theorem cleanRealizes_rFullZeroLoc_of_set {Var : Type} [Fintype Var] [DecidableEq Var]
    (bQPE bCat mOut mMid mLow aRem mRem sUb : ℕ) (v : Var) {kZero : ℕ}
    (rAncZero : QRegister kZero (mOut + mMid))
    {u : Unitary (2 ^ walkCatWidth bCat mOut mMid)}
    {P : DynamicCircuit Var (totalQubits bQPE bCat mOut mMid mLow aRem mRem sUb)}
    (hSet : SelectSwapQROM.CleanRealizesSet v
      ((rScrUbLoc bQPE bCat mOut mMid mLow aRem mRem sUb).image ∪
        (rAncZeroLoc bQPE bCat mOut mMid mLow aRem mRem sUb rAncZero).image)
      ((rWalkCatLoc bQPE bCat mOut mMid mLow aRem mRem sUb).embedUnitary u) P) :
    XMeasCircuit.CleanRealizes v (rWalkCatLoc bQPE bCat mOut mMid mLow aRem mRem sUb)
      (rFullZeroLoc bQPE bCat mOut mMid mLow aRem mRem sUb rAncZero) u P := by
  let rUbZero := rUbZeroLoc bQPE bCat mOut mMid mLow aRem mRem sUb rAncZero
  let rFull := rFullZeroLoc bQPE bCat mOut mMid mLow aRem mRem sUb rAncZero
  let rWC := rWalkCatLoc bQPE bCat mOut mMid mLow aRem mRem sUb
  let rScr := rScrLoc bQPE bCat mOut mMid mLow aRem mRem sUb
  have hSet' : SelectSwapQROM.CleanRealizesSet v rUbZero.image (rWC.embedUnitary u) P := by
    rwa [image_rUbZeroLoc]
  have hClean₁ : CleanDyn.CleanRealizes v rWC rUbZero u P :=
    (SelectSwapQROM.cleanRealizes_iff_set v rWC rUbZero u P).mpr hSet'
  have hPres₁ := preserves_basisOutcomeProjector_of_cleanRealizes hClean₁
  let P_scr := rScr.basisOutcomeProjector 0
  let P₁ := rUbZero.basisOutcomeProjector 0
  let P₀ := rFull.basisOutcomeProjector 0
  let W := (rWC.embedUnitary u).1
  have hsub_ub : (rScrUbLoc bQPE bCat mOut mMid mLow aRem mRem sUb).image ⊆ rScr.image :=
    rScr.image_compose_subset _
  have hP₀_eq : P₀ = P_scr * P₁ := by
    dsimp only [P₀, P_scr, P₁]
    rw [SelectSwapQROM.basisOutcomeProjector_zero_eq_zeroProjOn,
      SelectSwapQROM.basisOutcomeProjector_zero_eq_zeroProjOn,
      SelectSwapQROM.basisOutcomeProjector_zero_eq_zeroProjOn,
      SelectSwapQROM.zeroProjOn_mul_union, image_rFullZeroLoc, image_rUbZeroLoc]
    congr 1; ext w; simp only [Finset.mem_union]; tauto
  have hWP₀ : W * P₀ = P_scr * (W * P₁) := by
    have hcomm_W : P_scr * W = W * P_scr :=
      QubitisedWalk.basisOutcomeProjector_comm_embedMatrix rScr rWC
        (QRegister.disjoint_comm.mp
          (rWalkCatLoc_disjoint_rScrLoc bQPE bCat mOut mMid mLow aRem mRem sUb)) 0 u.1
    rw [hP₀_eq, ← Matrix.mul_assoc, ← hcomm_W, Matrix.mul_assoc]
  refine XMeasCircuit.CleanRealizes.absorbCleanActive hClean₁
    (by rw [image_rUbZeroLoc, image_rFullZeroLoc]
        exact Finset.union_subset_union_left hsub_ub) rfl ?_
  change P₀ * (W * P₀) = W * P₀
  have hcomm_p : P_scr * P₁ = P₁ * P_scr := basisOutcomeProjector_comm2 rScr 0 rUbZero 0
  have hidem_scr : P_scr * P_scr = P_scr := rScr.basisOutcomeProjector_mul_self 0
  calc P₀ * (W * P₀)
      = (P_scr * P₁) * (P_scr * (W * P₁)) := by rw [hWP₀, hP₀_eq]
    _ = P₁ * (P_scr * P_scr) * (W * P₁) := by rw [hcomm_p]; simp only [Matrix.mul_assoc]
    _ = P_scr * (P₁ * (W * P₁)) := by rw [hidem_scr, ← hcomm_p]; simp only [Matrix.mul_assoc]
    _ = W * P₀ := by rw [hPres₁, ← hWP₀]

/-- Canonical `QRegister S.card N` enumerating a `Finset (Fin N)` in ascending order. -/
noncomputable def qregOfFinset {N : ℕ} (S : Finset (Fin N)) : QRegister S.card N where
  wires := (S.orderEmbOfFin rfl).toEmbedding

@[simp]
theorem image_qregOfFinset {N : ℕ} (S : Finset (Fin N)) :
    (qregOfFinset S).image = S := by
  ext w
  rw [QRegister.mem_image]
  change (∃ i, S.orderEmbOfFin rfl i = w) ↔ w ∈ S
  rw [← Set.mem_range, Finset.range_orderEmbOfFin, Finset.mem_coe]

theorem basisOutcomeProjector_zero_qregOfFinset {N : ℕ} (S : Finset (Fin N)) :
    (qregOfFinset S).basisOutcomeProjector 0 = SelectSwapQROM.zeroProjOn S := by
  rw [SelectSwapQROM.basisOutcomeProjector_zero_eq_zeroProjOn, image_qregOfFinset]

end CleanZeroLifting

private theorem basisOutcomeProjector_mul_of_union_eq {N k₁ k₂ s : ℕ}
    {r₁ : QRegister k₁ N} {r₂ : QRegister k₂ N} {rFull : QRegister s N}
    (h : r₁.image ∪ rFull.image = r₂.image ∪ rFull.image) :
    r₁.basisOutcomeProjector 0 * rFull.basisOutcomeProjector 0 =
      r₂.basisOutcomeProjector 0 * rFull.basisOutcomeProjector 0 := by
  rw [SelectSwapQROM.basisOutcomeProjector_zero_eq_zeroProjOn,
    SelectSwapQROM.basisOutcomeProjector_zero_eq_zeroProjOn,
    SelectSwapQROM.basisOutcomeProjector_zero_eq_zeroProjOn,
    SelectSwapQROM.zeroProjOn_mul_union, SelectSwapQROM.zeroProjOn_mul_union, h]

private theorem embed_reflInUnitary_comm {N k w s : ℕ}
    (rWalk : QRegister k N) (inAll : QRegister w k) (rScr : QRegister s N) :
    (rWalk.embedUnitary (QubitisedWalk.reflInUnitary inAll)).1 * rScr.basisOutcomeProjector 0 =
      rScr.basisOutcomeProjector 0 * (rWalk.embedUnitary (QubitisedWalk.reflInUnitary
        inAll)).1 := by
  have hemb : (rWalk.embedUnitary (QubitisedWalk.reflInUnitary inAll)).1 =
      (2 : ℂ) • (rWalk.compose inAll).basisOutcomeProjector 0 - 1 := by
    change rWalk.embedMatrix ((2 : ℂ) • inAll.basisOutcomeProjector 0 - 1) = _
    rw [QubitisedWalk.embedMatrix_sub_local, QRegister.embedMatrix_smul, QRegister.embedMatrix_one,
      CleanDyn.compose_basisOutcomeProjector]
  rw [hemb, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, smul_mul_assoc,
    mul_smul_comm, basisOutcomeProjector_comm2]

private theorem embed_reflInUnitary_mul_rFullZero
    {bQPE bCat mOut mMid mLow sUb aRem mRem kZero : ℕ}
    {refl : WalkReflRegs bCat mOut mMid aRem mRem}
    {rAncZero : QRegister kZero (mOut + mMid)}
    (hCov : WalkReflCovers bQPE bCat mOut mMid mLow sUb refl rAncZero) :
    ((rWalkCatLoc bQPE bCat mOut mMid mLow aRem mRem sUb).embedUnitary
        (QubitisedWalk.reflInUnitary refl.inAll)).1 *
      (rFullZeroLoc bQPE bCat mOut mMid mLow aRem mRem sUb rAncZero).basisOutcomeProjector 0 =
    ((rWalkCatLoc bQPE bCat mOut mMid mLow aRem mRem sUb).embedUnitary
        (QubitisedWalk.reflInUnitary (inAllWalkCat bCat mOut mMid))).1 *
      (rFullZeroLoc bQPE bCat mOut mMid mLow aRem mRem sUb rAncZero).basisOutcomeProjector 0 := by
  let rW := rWalkCatLoc bQPE bCat mOut mMid mLow aRem mRem sUb
  have hemb {w : ℕ} (sub : QRegister w (walkCatWidth bCat mOut mMid)) :
      (rW.embedUnitary (QubitisedWalk.reflInUnitary sub)).1 =
        (2 : ℂ) • (rW.compose sub).basisOutcomeProjector 0 - 1 := by
    change rW.embedMatrix ((2 : ℂ) • sub.basisOutcomeProjector 0 - 1) = _
    rw [QubitisedWalk.embedMatrix_sub_local, QRegister.embedMatrix_smul, QRegister.embedMatrix_one,
      CleanDyn.compose_basisOutcomeProjector]
  rw [hemb, hemb, Matrix.sub_mul, Matrix.sub_mul, Matrix.one_mul, smul_mul_assoc, smul_mul_assoc,
    basisOutcomeProjector_mul_of_union_eq hCov.2]

/-- `CleanRealizes` theorem for `wStepRefl2Dyn` given any fused inner-reflection circuit
`pRefl2`. -/
theorem wStepRefl2Dyn_cleanRealizes {Var : Type} [Fintype Var] [DecidableEq Var]
    (bQPE bCat mOut mMid mLow sUb : ℕ) (v : Var) {aRem mRem kZero : ℕ}
    {refl : WalkReflRegs bCat mOut mMid aRem mRem}
    {rAncZero : QRegister kZero (mOut + mMid)}
    (hCov : WalkReflCovers bQPE bCat mOut mMid mLow sUb refl rAncZero)
    {uRefl2 : Unitary (2 ^ walkCatWidth bCat mOut mMid)}
    {pRefl2 : DynamicCircuit Var (totalQubits bQPE bCat mOut mMid mLow aRem mRem sUb)}
    (hRefl2 :
      QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.XMeasCircuit.CleanRealizes v
      (rWalkCatLoc bQPE bCat mOut mMid mLow aRem mRem sUb)
      (rFullZeroLoc bQPE bCat mOut mMid mLow aRem mRem sUb rAncZero) uRefl2 pRefl2) :
    QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.XMeasCircuit.CleanRealizes v
      (rWalkCatLoc bQPE bCat mOut mMid mLow aRem mRem sUb)
      (rFullZeroLoc bQPE bCat mOut mMid mLow aRem mRem sUb rAncZero)
      (QubitisedWalk.reflInUnitary (inAllWalkCat bCat mOut mMid) * uRefl2)
      (wStepRefl2Dyn bQPE bCat mOut mMid mLow sUb v refl pRefl2) := by
  let rWalk := rWalkCatLoc bQPE bCat mOut mMid mLow aRem mRem sUb
  let rScr := rScrLoc bQPE bCat mOut mMid mLow aRem mRem sUb
  let rFull := rFullZeroLoc bQPE bCat mOut mMid mLow aRem mRem sUb rAncZero
  have hsub : rScr.image ⊆ rFull.image := by
    rw [image_rFullZeroLoc]; exact Finset.subset_union_left
  have hin := (absorbCleanActive_of_comm2
    (QubitisedWalk.reflInDyn_cleanRealizes v rWalk refl.inAll rScr refl.haPos
      (scr_ge_reflIn bQPE mLow aRem mRem sUb)
      (QubitisedWalk.disjointWires_compose_left
        (rWalkCatLoc_disjoint_rScrLoc bQPE bCat mOut mMid mLow aRem mRem sUb)))
    hsub (embed_reflInUnitary_comm rWalk refl.inAll rFull)).congrUnitary
    (embed_reflInUnitary_mul_rFullZero hCov)
  exact hRefl2.seq hin

/-- Product state on `walkCatWidth bCat mOut mMid` factoring walk and catalyst amplitudes. -/
noncomputable def tensorWalkCat {bCat mOut mMid : ℕ}
    (u : Fin (2 ^ walkWidth mOut mMid) → ℂ) (cat : Fin (2 ^ bCat) → ℂ) :
    Fin (2 ^ walkCatWidth bCat mOut mMid) → ℂ :=
  fun x ↦ u ((rWalkInWalkCat bCat mOut mMid).extractIndex x) *
    cat ((rCatInWalkCat bCat mOut mMid).extractIndex x)

@[simp]
theorem tensorWalkCat_eq_tensorUBCat {bCat wOuter wInner2 : ℕ}
    (u : Fin (2 ^ BlockEncodingCore.nUB wOuter wInner2) → ℂ) (cat : Fin (2 ^ bCat) → ℂ) :
    tensorWalkCat (bCat := bCat) (mOut := BlockEncodingCore.mOutUB wOuter)
      (mMid := BlockEncodingCore.mMidUB wInner2) u cat =
      BlockEncodingCore.tensorUBCat u cat :=
  rfl

private theorem embedMatrix_mulVec_apply_replaceIndex_3 {k n : ℕ} (r : QRegister k n)
    (A : Operator (2 ^ k)) (state : Fin (2 ^ n) → ℂ) (output : Fin (2 ^ n)) :
    (r.embedMatrix A *ᵥ state) output =
      ∑ a : Fin (2 ^ k), A (r.extractIndex output) a * state (r.replaceIndex output a) :=
  r.embedMatrix_mulVec_apply A state output

theorem embedMatrix_rWalkInWalkCat_mulVec {bCat mOut mMid : ℕ}
    (A : Operator (2 ^ walkWidth mOut mMid))
    (u : Fin (2 ^ walkWidth mOut mMid) → ℂ) (cat : Fin (2 ^ bCat) → ℂ) :
    ((rWalkInWalkCat bCat mOut mMid).embedMatrix A) *ᵥ tensorWalkCat u cat =
      tensorWalkCat (A *ᵥ u) cat := by
  funext g
  rw [embedMatrix_mulVec_apply_replaceIndex_3]
  have hstep :
      (∑ a : Fin (2 ^ walkWidth mOut mMid),
        A ((rWalkInWalkCat bCat mOut mMid).extractIndex g) a *
          tensorWalkCat u cat ((rWalkInWalkCat bCat mOut mMid).replaceIndex g a)) =
      ∑ a : Fin (2 ^ walkWidth mOut mMid),
        (A ((rWalkInWalkCat bCat mOut mMid).extractIndex g) a * u a) *
          cat ((rCatInWalkCat bCat mOut mMid).extractIndex g) := by
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    dsimp only [tensorWalkCat]
    have hc :
        (rCatInWalkCat bCat mOut mMid).extractIndex
            ((rWalkInWalkCat bCat mOut mMid).replaceIndex g a) =
          (rCatInWalkCat bCat mOut mMid).extractIndex g :=
      (rCatInWalkCat bCat mOut mMid).extractIndex_replaceIndex_of_disjoint _
        (QRegister.disjoint_comm.mp (rWalkInWalkCat_disjoint_rCatInWalkCat bCat mOut mMid)) g a
    rw [hc, QRegister.extractIndex_replaceIndex, mul_assoc]
  rw [hstep, ← Finset.sum_mul]
  rfl

theorem embedMatrix_rCatInWalkCat_mulVec {bCat mOut mMid : ℕ}
    (C : Operator (2 ^ bCat))
    (u : Fin (2 ^ walkWidth mOut mMid) → ℂ) (cat : Fin (2 ^ bCat) → ℂ) :
    ((rCatInWalkCat bCat mOut mMid).embedMatrix C) *ᵥ tensorWalkCat u cat =
      tensorWalkCat u (C *ᵥ cat) := by
  funext g
  rw [embedMatrix_mulVec_apply_replaceIndex_3]
  have hstep :
      (∑ c : Fin (2 ^ bCat),
        C ((rCatInWalkCat bCat mOut mMid).extractIndex g) c *
          tensorWalkCat u cat ((rCatInWalkCat bCat mOut mMid).replaceIndex g c)) =
      u ((rWalkInWalkCat bCat mOut mMid).extractIndex g) *
        ∑ c : Fin (2 ^ bCat),
          C ((rCatInWalkCat bCat mOut mMid).extractIndex g) c * cat c := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ ↦ ?_
    dsimp only [tensorWalkCat]
    have hw :
        (rWalkInWalkCat bCat mOut mMid).extractIndex
            ((rCatInWalkCat bCat mOut mMid).replaceIndex g c) =
          (rWalkInWalkCat bCat mOut mMid).extractIndex g :=
      (rWalkInWalkCat bCat mOut mMid).extractIndex_replaceIndex_of_disjoint _
        (rWalkInWalkCat_disjoint_rCatInWalkCat bCat mOut mMid) g c
    rw [hw, QRegister.extractIndex_replaceIndex]
    ring
  rw [hstep]
  rfl

theorem sum_normSq_tensorWalkCat {bCat mOut mMid : ℕ}
    (u : Fin (2 ^ walkWidth mOut mMid) → ℂ) (cat : Fin (2 ^ bCat) → ℂ) :
    (∑ x : Fin (2 ^ walkCatWidth bCat mOut mMid),
      Complex.normSq (tensorWalkCat u cat x)) =
      (∑ a, Complex.normSq (u a)) * (∑ c, Complex.normSq (cat c)) := by
  let f : Fin (2 ^ walkCatWidth bCat mOut mMid) → ℝ :=
    fun x ↦ Complex.normSq (tensorWalkCat u cat x)
  rw [show (∑ x, Complex.normSq (tensorWalkCat u cat x)) = ∑ x, f x from rfl,
    ← (BlockEncodingCore.splitBlockEquiv (walkWidth mOut mMid) bCat).symm.sum_comp f,
    Fintype.sum_prod_type, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ ↦ ?_
  let x := (BlockEncodingCore.splitBlockEquiv (walkWidth mOut mMid) bCat).symm (a, c)
  have hfst : (rWalkInWalkCat bCat mOut mMid).extractIndex x = a := by
    rw [← BlockEncodingCore.splitBlockEquiv_fst, Equiv.apply_symm_apply]
  have hsnd : (rCatInWalkCat bCat mOut mMid).extractIndex x = c := by
    rw [← BlockEncodingCore.splitBlockEquiv_snd, Equiv.apply_symm_apply]
  dsimp [f, tensorWalkCat]
  change Complex.normSq (u ((rWalkInWalkCat bCat mOut mMid).extractIndex x) *
    cat ((rCatInWalkCat bCat mOut mMid).extractIndex x)) = _
  rw [hfst, hsnd, map_mul]

/-- Abstract pulled-reflection SOS block-encoding contract on `(mOut, mMid)` walk ancillas
for a blocked effective Hamiltonian `H_tilde_blk` on `systemQubits_local = 2 * 58` qubits
with lower bound `eLB` and walk scale `lam > 0`. -/
structure PulledSOSBlockEncoding (mOut mMid : ℕ)
    (H_tilde_blk : Operator (2 ^ systemQubits_local))
    (eLB lam : ℝ) (uB : Unitary (2 ^ walkWidth mOut mMid)) : Prop where
  /-- Strictly positive walk rescaling factor `Λ > 0`. -/
  hLamPos : 0 < lam
  /-- Every normalized eigenstate `(ψ, E)` of `H_tilde_blk` embeds via `|ψ⟩|0⟩` into the
  `projIn = 1` subspace with `eLB ≤ E ≤ eLB + 2 * lam` and pulled-reflection Jordan
  cross-projection `P₁ (P₂ e₁) = ((E - eLB) / (2 * lam)) • e₁`. -/
  jordanRelation : ∀ (ψ : Fin (2 ^ systemQubits_local) → ℂ) (E : ℝ),
    H_tilde_blk *ᵥ ψ = (E : ℂ) • ψ →
    ∑ x : Fin (2 ^ systemQubits_local), Complex.normSq (ψ x) = 1 →
    let e₁ := (rSysInWalk mOut mMid).tensorState ψ (Pi.single 0 1)
    QubitisedWalk.projIn (rAllInWalk mOut mMid) *ᵥ e₁ = e₁ ∧
      (∑ x, Complex.normSq (e₁ x) = 1) ∧
      eLB ≤ E ∧ E ≤ eLB + 2 * lam ∧
      QubitisedWalk.projIn (rAllInWalk mOut mMid) *ᵥ
        (QubitisedWalk.pulledProjMid (rMidInWalk mOut mMid) uB *ᵥ e₁) =
        (((E - eLB) / (2 * lam) : ℝ) : ℂ) • e₁

section Proofs

attribute [local irreducible] thcHamiltonian

attribute [local irreducible] BlockEncodingCore.p450HBlocked

end Proofs

section FastUniformMed

open FastUniform

end FastUniformMed

end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.TopIntegrationBridge
