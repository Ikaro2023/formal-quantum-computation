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

public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.ProjZ512QftTwist

set_option Elab.async false

@[expose] public section
set_option allowUnsafeReducibility true

namespace QuantumComputation.Specs.StoppingPowerSolution
open SpecsAux

section ModWeighted3ASingleCatClosure
@[expose] public section
namespace SingleCatClosureAlt
theorem qreg_ext {k n : ℕ} {r s : QRegister k n} (h : ∀ i, r i = s i) : r = s :=
  QRegister.ext (Function.Embedding.ext h)
theorem qreg_block_apply {n : ℕ} (offset width : ℕ) (h : offset + width ≤ n) (i : Fin width) :
    QRegister.block offset width h i = ⟨offset + i.val, by omega⟩ := rfl
theorem qreg_block_wires_apply {n : ℕ} (offset width : ℕ) (h : offset + width ≤ n) (i : Fin width) :
    (QRegister.block offset width h).wires i = ⟨offset + i.val, by omega⟩ := rfl
theorem qreg_compose_wires {m k n : ℕ} (outer : QRegister k n) (inner : QRegister m k) (i : Fin m) :
    (outer.compose inner).wires i = outer.wires (inner.wires i) := rfl
end SingleCatClosureAlt
namespace SingleCatClosure
set_option exponentiation.threshold 256
open Operator Matrix Circuit _root_.DynamicCircuit DynCircuitExt
open scoped Matrix Matrix.Norms.L2Operator BigOperators
open SpecsAux.SpecMirror
open SpecsAux.BridgeFermionicComm
open SpecsAux.BridgeFermionicComm.SpecInner
open SpecsAux.FullScaleBESector
open SpecsAux.PhaseGradCatalystCore
open SpecsAux.BridgeDuhamel
open PhaseGradSignalRot hiding IntertwinesCat
open TFreeLaurentGQSP CatalyzedLaurentGQSP
open BidirectionalCatalyzedGQSP
open BidirectionalCatalyzedGQSPBridge
open PosMomSelectSandwich
open PosMomSelectDynamic (unitaryConj)
open FullSysWalkStepEndpoint
open FullSysCatSegmentBridge
open HoistedSwapSelectBridge
open CatalystPrep
open PolymorphicTopClosure
open SingleCatSpine
set_option exponentiation.threshold 3936
theorem intertwinesCat_congr_ops {d : ℕ} {U P C₁ C₂ E₁ E₂ : Operator d}
    (h : IntertwinesCat U P C₁ E₁) (hC : C₁ = C₂) (hE : E₁ = E₂) : IntertwinesCat U P C₂ E₂ :=
    hC ▸ hE ▸ h
abbrev mZeroScratchSingleCat (kWorkConst : ℕ) : ℕ := max 3 (42 - kWorkConst)
abbrev mCatScratchSingleCat (B_tot kWorkConst : ℕ) : ℕ :=
  B_tot + mZeroScratchSingleCat kWorkConst
abbrev mActSingleCatClosure (mPayload B_tot kWorkConst : ℕ) : ℕ :=
  mSegAncPoly mPayload + mCatScratchSingleCat B_tot kWorkConst
abbrev kActSingleCatClosure (mPayload B_tot kWorkConst : ℕ) : ℕ :=
  SpecsAux.SpecMirror.systemQubits + mActSingleCatClosure mPayload B_tot kWorkConst
theorem singleCat_beWires_le_kAct (mPayload B_tot kWorkConst : ℕ) :
    0 + fullSysBEWires mPayload ≤ kActSingleCatClosure mPayload B_tot kWorkConst := by
  dsimp [kActSingleCatClosure, mActSingleCatClosure, mSegAncPoly, fullSysBEWires]; omega
theorem singleCat_beWires_lt_kAct (mPayload B_tot kWorkConst : ℕ) :
    fullSysBEWires mPayload < kActSingleCatClosure mPayload B_tot kWorkConst := by
  dsimp [kActSingleCatClosure, mActSingleCatClosure, mSegAncPoly, fullSysBEWires]; omega
theorem singleCat_physSeg_le_kAct (mPayload B_tot kWorkConst : ℕ) :
    0 + (SpecsAux.SpecMirror.systemQubits + (fullSysRawAncWires mPayload + 1)) ≤
      kActSingleCatClosure mPayload B_tot kWorkConst := by
  dsimp [kActSingleCatClosure, mActSingleCatClosure, mSegAncPoly]; omega
theorem singleCat_catScratch_le_mAct (mPayload B_tot kWorkConst : ℕ) :
    mSegAncPoly mPayload + mCatScratchSingleCat B_tot kWorkConst ≤
      mActSingleCatClosure mPayload B_tot kWorkConst := le_rfl
theorem singleCat_catTot_le_scratch (B_tot kWorkConst : ℕ) :
    0 + B_tot ≤ mCatScratchSingleCat B_tot kWorkConst := by
  dsimp [mCatScratchSingleCat]; omega
theorem singleCat_slack3_le_scratch (B_tot kWorkConst : ℕ) :
    B_tot + 3 ≤ mCatScratchSingleCat B_tot kWorkConst := by
  dsimp [mCatScratchSingleCat, mZeroScratchSingleCat]; omega
abbrev rAncInSingleCat (mPayload B_tot kWorkConst : ℕ) : QRegister
    (mActSingleCatClosure mPayload B_tot kWorkConst)
    (kActSingleCatClosure mPayload B_tot kWorkConst) := QRegister.block
    SpecsAux.SpecMirror.systemQubits (mActSingleCatClosure mPayload B_tot kWorkConst) le_rfl
abbrev rBEInSingleCat (mPayload B_tot kWorkConst : ℕ) : QRegister (fullSysBEWires mPayload)
    (kActSingleCatClosure mPayload B_tot kWorkConst) := QRegister.block 0
    (fullSysBEWires mPayload) (singleCat_beWires_le_kAct mPayload B_tot kWorkConst)
abbrev qSigInSingleCat (mPayload B_tot kWorkConst : ℕ) :
    Wire (kActSingleCatClosure mPayload B_tot kWorkConst) :=
  ⟨fullSysBEWires mPayload, singleCat_beWires_lt_kAct mPayload B_tot kWorkConst⟩
abbrev rPhysSegInSingleCat (mPayload B_tot kWorkConst : ℕ) :
    QRegister (SpecsAux.SpecMirror.systemQubits + (fullSysRawAncWires mPayload + 1))
      (kActSingleCatClosure mPayload B_tot kWorkConst) :=
  QRegister.block 0 (SpecsAux.SpecMirror.systemQubits + (fullSysRawAncWires mPayload + 1))
    (singleCat_physSeg_le_kAct mPayload B_tot kWorkConst)
abbrev inCatScratchSingleCat (mPayload B_tot kWorkConst : ℕ) : QRegister
    (mCatScratchSingleCat B_tot kWorkConst) (mActSingleCatClosure mPayload B_tot kWorkConst)
    := QRegister.block (mSegAncPoly mPayload) (mCatScratchSingleCat B_tot kWorkConst)
    (singleCat_catScratch_le_mAct mPayload B_tot kWorkConst)
abbrev rCatScratchInSingleCat (mPayload B_tot kWorkConst : ℕ) : QRegister
    (mCatScratchSingleCat B_tot kWorkConst) (kActSingleCatClosure mPayload B_tot kWorkConst)
    := (rAncInSingleCat mPayload B_tot kWorkConst).compose
    (inCatScratchSingleCat mPayload B_tot kWorkConst)
abbrev inCatTotSingleCat (B_tot kWorkConst : ℕ) :
    QRegister B_tot (mCatScratchSingleCat B_tot kWorkConst) :=
  QRegister.block 0 B_tot (singleCat_catTot_le_scratch B_tot kWorkConst)
abbrev inSlack3SingleCat (B_tot kWorkConst : ℕ) :
    QRegister 3 (mCatScratchSingleCat B_tot kWorkConst) :=
  QRegister.block B_tot 3 (singleCat_slack3_le_scratch B_tot kWorkConst)
abbrev rCatTotInSingleCat (mPayload B_tot kWorkConst : ℕ) :
    QRegister B_tot (kActSingleCatClosure mPayload B_tot kWorkConst) :=
  (rCatScratchInSingleCat mPayload B_tot kWorkConst).compose (inCatTotSingleCat B_tot kWorkConst)
abbrev rSlackSave3InSingleCat (mPayload B_tot kWorkConst : ℕ) :
    QRegister 3 (kActSingleCatClosure mPayload B_tot kWorkConst) :=
  (rCatScratchInSingleCat mPayload B_tot kWorkConst).compose (inSlack3SingleCat B_tot kWorkConst)
abbrev qCoin0InSingleCat (mPayload B_tot kWorkConst : ℕ) :
    Wire (kActSingleCatClosure mPayload B_tot kWorkConst) :=
  ⟨SpecsAux.SpecMirror.systemQubits + 0, by
    dsimp [kActSingleCatClosure, mActSingleCatClosure, mSegAncPoly, fullSysRawAncWires]; omega⟩
abbrev qCoin1InSingleCat (mPayload B_tot kWorkConst : ℕ) :
    Wire (kActSingleCatClosure mPayload B_tot kWorkConst) :=
  ⟨SpecsAux.SpecMirror.systemQubits + 1, by
    dsimp [kActSingleCatClosure, mActSingleCatClosure, mSegAncPoly, fullSysRawAncWires]; omega⟩
abbrev qCoin2InSingleCat (mPayload B_tot kWorkConst : ℕ) :
    Wire (kActSingleCatClosure mPayload B_tot kWorkConst) :=
  ⟨SpecsAux.SpecMirror.systemQubits + 2, by
    dsimp [kActSingleCatClosure, mActSingleCatClosure, mSegAncPoly, fullSysRawAncWires]; omega⟩
abbrev qSlack2InSingleCat (mPayload B_tot kWorkConst : ℕ) :
    Wire (kActSingleCatClosure mPayload B_tot kWorkConst) :=
  rSlackSave3InSingleCat mPayload B_tot kWorkConst ⟨0, by decide⟩
abbrev qSlack1InSingleCat (mPayload B_tot kWorkConst : ℕ) :
    Wire (kActSingleCatClosure mPayload B_tot kWorkConst) :=
  rSlackSave3InSingleCat mPayload B_tot kWorkConst ⟨1, by decide⟩
abbrev qSlack0InSingleCat (mPayload B_tot kWorkConst : ℕ) :
    Wire (kActSingleCatClosure mPayload B_tot kWorkConst) :=
  rSlackSave3InSingleCat mPayload B_tot kWorkConst ⟨2, by decide⟩
theorem rBEInSingleCat_disj_qSig (mPayload B_tot kWorkConst : ℕ) :
    (rBEInSingleCat mPayload B_tot kWorkConst).DisjointWires
      (QRegister.singleton (qSigInSingleCat mPayload B_tot kWorkConst)) := by
  rw [QRegister.disjoint_iff]; intro i j h; fin_cases j
  have hv := congrArg Fin.val h
  simp [rBEInSingleCat, qSigInSingleCat, QRegister.singleton] at hv; omega
theorem rBEInSingleCat_disj_catScratch (mPayload B_tot kWorkConst : ℕ) :
    (rBEInSingleCat mPayload B_tot kWorkConst).DisjointWires
      (rCatScratchInSingleCat mPayload B_tot kWorkConst) := by
  rw [QRegister.disjoint_iff]; intro i j h
  have hv := congrArg Fin.val h
  simp [rBEInSingleCat, rCatScratchInSingleCat, rAncInSingleCat, inCatScratchSingleCat,
    mSegAncPoly, fullSysBEWires] at hv
  omega
theorem rBEInSingleCat_disj_catTot (mPayload B_tot kWorkConst : ℕ) :
    (rBEInSingleCat mPayload B_tot kWorkConst).DisjointWires
      (rCatTotInSingleCat mPayload B_tot kWorkConst) :=
  (rBEInSingleCat_disj_catScratch mPayload B_tot kWorkConst).compose_right _
theorem qSigInSingleCat_disj_catScratch (mPayload B_tot kWorkConst : ℕ) :
    (QRegister.singleton (qSigInSingleCat mPayload B_tot kWorkConst)).DisjointWires
      (rCatScratchInSingleCat mPayload B_tot kWorkConst) := by
  rw [QRegister.disjoint_iff]; intro i j h; fin_cases i
  have hv := congrArg Fin.val h
  simp [qSigInSingleCat, rCatScratchInSingleCat, rAncInSingleCat, inCatScratchSingleCat,
    QRegister.singleton, mSegAncPoly, fullSysBEWires] at hv
  omega
abbrev rBECatSingleCatInAct (mPayload B_tot kWorkConst : ℕ) : QRegister
    (fullSysBEWires mPayload + B_tot) (kActSingleCatClosure mPayload B_tot kWorkConst) :=
    (rBEInSingleCat mPayload B_tot kWorkConst).concat
    (rCatTotInSingleCat mPayload B_tot kWorkConst)
    (rBEInSingleCat_disj_catTot mPayload B_tot kWorkConst)
namespace ZeroAncCatPrep1q
section ConfigZeroAncCatPrep1q
set_option exponentiation.threshold 256
open MeasureBranchHadamardSem (sqrtHalf)
open ZeroAncillaUSP
open CatalyzedLaurentGQSPBridge (cosTaylor cos_sin_taylor_alternating)
def catPrepWord : ℕ → List HSTGate
  | 0 => [.H, .S, .S]
  | 1 => [.H, .S, .S, .S]
  | 2 => [.H, .T, .S, .S, .S]
  | 3 =>
    [.H, .S, .S, .S, .T, .S, .H, .T, .H, .T, .S, .H, .T, .H, .T, .S, .H, .T, .S, .H, .T, .H, .T, .H,
    .T, .S, .H, .T, .S, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .S, .H, .T, .S, .H, .T, .H,
    .T, .S, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .S, .H, .T, .H, .T, .S, .H, .T, .S, .H, .T, .S,
    .H, .T, .H, .T, .H, .T, .S, .H, .T, .S, .H, .T, .S, .H, .T, .S, .H, .T, .S, .H, .T, .H, .T, .S,
    .H, .T]
  | 4 =>
    [.H, .S, .S, .S, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .S, .H, .T, .H, .T, .S, .H,
    .T, .H, .T, .S, .H, .T, .H, .T, .S, .H, .T, .H, .T, .H, .T, .H, .T, .S, .H, .T, .S, .H, .T, .H,
    .T, .H, .T, .S, .H, .T, .S, .H, .T, .H, .T, .H, .T, .H, .T, .S, .H, .T, .H, .T, .H, .T, .S, .H,
    .T, .H, .T, .H, .T, .S, .H, .T, .S, .H, .T, .H, .T, .S, .H, .T, .S, .H, .T, .H, .T, .S, .H, .T,
    .S, .H, .T, .S, .H, .T, .S, .S, .S, .H, .S, .S, .H]
  | 5 =>
    [.H, .S, .T, .H, .T, .H, .T, .S, .H, .T, .H, .T, .S, .H, .T, .H, .T, .H, .T, .S, .H, .T, .S, .H,
    .T, .H, .T, .S, .H, .T, .S, .H, .T, .S, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .S, .H, .T, .H,
    .T, .S, .H, .T, .S, .H, .T, .S, .H, .T, .S, .H, .T, .H, .T, .H, .T, .S, .H, .T, .H, .T, .S, .H,
    .T, .S, .H, .T, .H, .T, .S, .H, .T, .H, .T, .H, .T, .S, .H, .T, .H, .T, .S, .H, .T, .H, .T]
  | 6 =>
    [.H, .S, .T, .H, .T, .H, .T, .H, .T, .H, .T, .S, .H, .T, .S, .H, .T, .S, .H, .T, .H, .T, .H, .T,
    .H, .T, .H, .T, .H, .T, .S, .H, .T, .H, .T, .H, .T, .S, .H, .T, .S, .H, .T, .S, .H, .T, .H, .T,
    .S, .H, .T, .S, .H, .T, .S, .H, .T, .H, .T, .H, .T, .H, .T, .S, .H, .T, .S, .H, .T, .S, .H, .T,
    .H, .T, .H, .T, .S, .H, .T, .S, .H, .T, .H, .T, .S]
  | 7 =>
    [.H, .S, .S, .S, .T, .S, .H, .T, .H, .T, .S, .H, .T, .H, .T, .H, .T, .S, .H, .T, .S, .H, .T, .H,
    .T, .H, .T, .H, .T, .S, .H, .T, .H, .T, .S, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .S, .H, .T,
    .H, .T, .H, .T, .S, .H, .T, .H, .T, .S, .H, .T, .S, .H, .T, .S, .H, .T, .H, .T, .S, .H, .T, .H,
    .T, .S, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .S, .H, .T, .H, .T, .H, .S, .S, .H]
  | 8 =>
    [.H, .S, .S, .S, .T, .H, .T, .S, .H, .T, .S, .H, .T, .H, .T, .S, .H, .T, .S, .H, .T, .H, .T, .H,
    .T, .S, .H, .T, .H, .T, .H, .T, .S, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H,
    .T, .H, .T, .H, .T, .S, .H, .T, .H, .T, .H, .T, .H, .T, .S, .H, .T, .H, .T, .S, .H, .T, .S, .H,
    .T, .H, .T, .S, .H, .T, .H, .T, .S, .H, .T, .H, .T, .H, .T, .H, .T, .S, .H, .T, .S, .H, .T, .H,
    .T, .S, .H, .S, .S, .H]
  | 9 =>
    [.H, .S, .S, .T, .H, .T, .H, .T, .S, .H, .T, .S, .H, .T, .H, .T, .H, .T, .S, .H, .T, .S, .H, .T,
    .S, .H, .T, .S, .H, .T, .S, .H, .T, .H, .T, .S, .H, .T, .S, .H, .T, .H, .T, .S, .H, .T, .S, .H,
    .T, .H, .T, .H, .T, .H, .T, .H, .T, .S, .H, .T, .S, .H, .T, .H, .T, .H, .T, .S, .H, .T, .S, .H,
    .T, .S, .H, .T, .S, .H, .T, .H, .T, .S, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .S, .H, .T, .S,
    .H, .T, .H, .T, .H, .T, .H, .T]
  | 10 =>
    [.H, .S, .S, .T, .H, .T, .H, .T, .H, .T, .S, .H, .T, .H, .T, .H, .T, .S, .H, .T, .S, .H, .T, .S,
    .H, .T, .H, .T, .S, .H, .T, .S, .H, .T, .H, .T, .H, .T, .S, .H, .T, .H, .T, .H, .T, .S, .H, .T,
    .H, .T, .H, .T, .S, .H, .T, .S, .H, .T, .H, .T, .H, .T, .H, .T, .S, .H, .T, .H, .T, .H, .T, .H,
    .T, .H, .T, .H, .T, .H, .T, .S, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .S, .H, .T, .H,
    .T]
  | 11 =>
    [.H, .S, .S, .S, .T, .H, .T, .S, .H, .T, .H, .T, .S, .H, .T, .H, .T, .S, .H, .T, .S, .H, .T, .H,
    .T, .S, .H, .T, .S, .H, .T, .S, .H, .T, .S, .H, .T, .S, .H, .T, .H, .T, .H, .T, .S, .H, .T, .H,
    .T, .S, .H, .T, .S, .H, .T, .S, .H, .T, .S, .H, .T, .H, .T, .S, .H, .T, .S, .H, .T, .S, .H, .T,
    .H, .T, .S, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .S, .H, .T, .H, .T, .H, .T, .H, .T,
    .H, .T, .S, .H, .T, .H, .T]
  | 12 =>
    [.H, .S, .S, .T, .H, .T, .H, .T, .S, .H, .T, .H, .T, .S, .H, .T, .S, .H, .T, .H, .T, .H, .T, .S,
    .H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .S, .H, .T, .S, .H, .T, .S, .H, .T, .H, .T, .S,
    .H, .T, .H, .T, .S, .H, .T, .H, .T, .S, .H, .T, .S, .H, .T, .S, .H, .T, .S, .H, .T, .H, .T, .H,
    .T, .H, .T, .S, .H, .T, .S, .H, .T, .S, .H, .T, .H, .T, .H, .T, .S, .H, .T, .S, .H, .T, .H, .T,
    .H, .T, .H, .T, .S, .S, .S, .H, .S, .S, .H]
  | 13 =>
    [.H, .S, .T, .H, .T, .S, .H, .T, .H, .T, .S, .H, .T, .S, .H, .T, .S, .H, .T, .S, .H, .T, .H, .T,
    .S, .H, .T, .H, .T, .S, .H, .T, .H, .T, .H, .T, .S, .H, .T, .H, .T, .S, .H, .T, .S, .H, .T, .S,
    .H, .T, .S, .H, .T, .H, .T, .S, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .S, .H, .T, .S, .H, .T,
    .S, .H, .T, .S, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .S, .H, .T, .H, .T, .S, .H, .T, .S, .S,
    .H, .S, .S, .H]
  | 14 =>
    [.H, .S, .S, .T, .H, .T, .H, .T, .H, .T, .S, .H, .T, .H, .T, .S, .H, .T, .H, .T, .S, .H, .T, .H,
    .T, .H, .T, .S, .H, .T, .S, .H, .T, .H, .T, .S, .H, .T, .H, .T, .H, .T, .S, .H, .T, .S, .H, .T,
    .H, .T, .H, .T, .S, .H, .T, .H, .T, .H, .T, .H, .T, .S, .H, .T, .H, .T, .H, .T, .H, .T, .S, .H,
    .T, .S, .H, .T, .H, .T, .H, .T, .H, .T, .S, .H, .T, .H, .T]
  | 15 =>
    [.H, .S, .S, .S, .T, .S, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .S, .H, .T, .S, .H, .T, .S, .H,
    .T, .H, .T, .H, .T, .S, .H, .T, .S, .H, .T, .S, .H, .T, .H, .T, .H, .T, .H, .T, .S, .H, .T, .H,
    .T, .S, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .S, .H, .T, .S, .H, .T,
    .H, .T, .H, .T, .H, .T, .H, .T, .S, .H, .T, .H, .T, .S, .H, .T, .H, .T, .S, .H, .T, .S]
  | 16 =>
    [.H, .S, .S, .T, .H, .T, .S, .H, .T, .S, .H, .T, .H, .T, .S, .H, .T, .H, .T, .H, .T, .S, .H, .T,
    .S, .H, .T, .S, .H, .T, .S, .H, .T, .S, .H, .T, .S, .H, .T, .H, .T, .S, .H, .T, .S, .H, .T, .S,
    .H, .T, .S, .H, .T, .S, .H, .T, .H, .T, .S, .H, .T, .H, .T, .S, .H, .T, .S, .H, .T, .S, .H, .T,
    .H, .T, .H, .T, .S, .H, .T, .S, .H, .T, .S, .H, .T, .H, .T, .H, .T, .H, .T, .S, .H, .T, .S, .H,
    .T, .S, .H, .T, .S, .H, .T, .H, .T, .H, .T, .H, .S, .S, .H]
  | 17 =>
    [.H, .S, .T, .H, .T, .S, .H, .T, .H, .T, .H, .T, .H, .T, .S, .H, .T, .S, .H, .T, .S, .H, .T, .H,
    .T, .S, .H, .T, .S, .H, .T, .H, .T, .H, .T, .H, .T, .S, .H, .T, .S, .H, .T, .S, .H, .T, .H, .T,
    .H, .T, .H, .T, .H, .T, .H, .T, .S, .H, .T, .S, .H, .T, .H, .T, .S, .H, .T, .H, .T, .S, .H, .T,
    .H, .T, .H, .T, .H, .T, .H, .T, .S, .H, .T, .S, .H, .T, .S, .H, .T, .S, .H, .T, .S, .H, .T, .H,
    .T, .S, .H, .T, .H, .T, .S, .S, .H, .S, .S, .H]
  | 18 =>
    [.H, .S, .T, .H, .T, .S, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T,
    .H, .T, .H, .T, .H, .T, .S, .H, .T, .H, .T, .H, .T, .H, .T, .S, .H, .T, .H, .T, .H, .T, .H, .T,
    .H, .T, .H, .T, .S, .H, .T, .S, .H, .T, .S, .H, .T, .S, .H, .T, .H, .T, .S, .H, .T, .S, .H, .T,
    .S, .H, .T, .H, .T, .H, .T, .H, .T, .S, .H, .T, .S, .H, .T, .H, .S, .S, .H]
  | 19 =>
    [.H, .S, .S, .S, .T, .S, .H, .T, .S, .H, .T, .S, .H, .T, .S, .H, .T, .H, .T, .S, .H, .T, .S, .H,
    .T, .S, .H, .T, .S, .H, .T, .H, .T, .H, .T, .H, .T, .S, .H, .T, .S, .H, .T, .S, .H, .T, .S, .H,
    .T, .H, .T, .H, .T, .S, .H, .T, .H, .T, .S, .H, .T, .S, .H, .T, .H, .T, .S, .H, .T, .S, .H, .T,
    .S, .H, .T, .H, .T, .S, .H, .T, .H, .T, .S, .H, .T, .S, .H, .T, .S, .H, .T, .S, .H, .T, .H, .T,
    .H, .T, .H, .T, .S, .H, .T, .H, .T, .S, .H, .T]
  | _ => [.H]
theorem catPrepWord_of_ge20 {idx : ℕ} (h : 20 ≤ idx) : catPrepWord idx = [.H] := by
  match idx with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15 | 16 | 17 | 18 | 19 => omega
  | _ + 20 => rfl
noncomputable def pythPhase (zp zq zr : ℤ) : ℂ :=
  (((zp : ℝ) / (zr : ℝ) : ℝ) : ℂ) + (((zq : ℝ) / (zr : ℝ) : ℝ) : ℂ) * Complex.I
theorem pythPhase_re (zp zq zr : ℤ) : (pythPhase zp zq zr).re = (zp : ℝ) / (zr : ℝ) := by
  simp [pythPhase]
theorem pythPhase_im (zp zq zr : ℤ) : (pythPhase zp zq zr).im = (zq : ℝ) / (zr : ℝ) := by
  simp [pythPhase]
theorem norm_pythPhase (zp zq zr : ℤ) (hzr : (0 : ℝ) < (zr : ℝ))
    (hpyth : (zp : ℝ) ^ 2 + (zq : ℝ) ^ 2 = (zr : ℝ) ^ 2) : ‖pythPhase zp zq zr‖ = 1 := by
  have hsq : ‖pythPhase zp zq zr‖ ^ 2 = 1 := by
    rw [Complex.sq_norm, Complex.normSq_apply, pythPhase_re, pythPhase_im]
    have hzr_ne : (zr : ℝ) ≠ 0 := hzr.ne'
    field_simp [hzr_ne]
    linarith [hpyth]
  nlinarith [norm_nonneg (pythPhase zp zq zr)]
noncomputable def zCatBit : ℕ → ℂ
  | 0 => 1
  | 1 => 1
  | 2 => Complex.exp (-(phaseGradAngle 2 * Complex.I))
  | 3 => pythPhase (-1403114000) (-34539042) 1403539042
  | 4 => pythPhase (-408100523) (-2681203236) 2712083485
  | 5 => pythPhase (-106289359) 12703440 107045809
  | 6 => pythPhase (-1149242455) (-131817192) 1156777417
  | 7 => pythPhase (-71186513) 79077816 106399345
  | 8 => pythPhase (-897240107) 1108953924 1426470685
  | 9 => pythPhase (-937919957) 3269799876 3401659165
  | 10 => pythPhase (-1423706480) 3119248782 3428797618
  | 11 => pythPhase (-479817219) (-69619540) 484841669
  | 12 => pythPhase (-34966371) (-2184398980) 2184678821
  | 13 => pythPhase 439770695 (-828208152) 937724377
  | 14 => pythPhase (-202224757) 82307676 218333245
  | 15 => pythPhase (-736977384) 706488010 1020911834
  | 16 => pythPhase (-547071393) 345189424 646871585
  | 17 => pythPhase (-327630365) 1858698708 1887353317
  | 18 => pythPhase (-576117971) 454120140 733578229
  | 19 => pythPhase (-558705565) (-285514572) 627431653
  | _ => 1
theorem zCatBit_of_ge20 {idx : ℕ} (h : 20 ≤ idx) : zCatBit idx = 1 := by
  match idx with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15 | 16 | 17 | 18 | 19 => omega
  | _ + 20 => rfl
noncomputable abbrev p0Mat2 : Operator 2 := (QRegister.whole 1).basisOutcomeProjector 0
theorem singleton_embed_p0Mat2 {n : ℕ} (q : Wire n) : (QRegister.singleton q).embedMatrix
    p0Mat2 = (QRegister.singleton q).basisOutcomeProjector 0 := by
  rw [p0Mat2, QRegister.basisOutcomeProjector, ← QRegister.embedMatrix_compose,
    (show (QRegister.singleton q).compose (QRegister.whole 1) = QRegister.singleton q from
      SingleCatClosureAlt.qreg_ext fun _ ↦ rfl),
    ← QRegister.basisOutcomeProjector]
theorem p0Mat2_eq_single : p0Mat2 = !![(1 : ℂ), 0; 0,0] := by
  ext i j
  have h1 : (QRegister.whole 1).extractIndex i = i := by
    apply (basisBitsEquiv 1).injective
    funext u; exact (QRegister.whole 1).basisBits_extractIndex i u
  fin_cases i <;> fin_cases j <;>
    simp [p0Mat2, QRegister.basisOutcomeProjector_apply]
theorem mul_p0Mat2_decomp (D : Operator 2) :
    D * p0Mat2 = D 0 0 • p0Mat2 + D 1 0 • (Qubit.X.1 * p0Mat2) := by
  rw [p0Mat2_eq_single]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Qubit.X]
theorem norm_p0Mat2_le_one : ‖p0Mat2‖ ≤ 1 :=
  BridgeDuhamel.norm_basisOutcomeProjector_le_one (QRegister.whole 1) 0
theorem norm_qubitX_le_one : ‖Qubit.X.1‖ ≤ 1 :=
  BridgeDuhamel.norm_of_mem_unitaryGroup_le_one Qubit.X.2
theorem norm_mul_p0Mat2_le (D : Operator 2) : ‖D * p0Mat2‖ ≤ ‖D 0 0‖ + ‖D 1 0‖ := by
  have hX0 : ‖Qubit.X.1 * p0Mat2‖ ≤ 1 := (norm_mul_le _ _).trans
    ((mul_le_mul norm_qubitX_le_one norm_p0Mat2_le_one (norm_nonneg _) zero_le_one).trans
      (one_mul 1).le)
  have hAdd := norm_add_le (D 0 0 • p0Mat2) (D 1 0 • (Qubit.X.1 * p0Mat2))
  rw [← mul_p0Mat2_decomp D, norm_smul, norm_smul] at hAdd
  nlinarith [hAdd, norm_nonneg (D 0 0), norm_nonneg (D 1 0), norm_p0Mat2_le_one, hX0]
theorem seqProd_smul {d : Type*} [Fintype d] [DecidableEq d] :
    ∀ {K : ℕ} (z : Fin K → ℂ) (A : Fin K → Matrix d d ℂ),
      seqProd (fun i : Fin K ↦ z i • A i) = (∏ i : Fin K, z i) • seqProd A
  | 0, _, _ => by simp [seqProd]
  | _ + 1, z, A => by
    dsimp only [seqProd]
    rw [seqProd_smul (fun j ↦ z j.succ) (fun j ↦ A j.succ),
      Matrix.smul_mul, Matrix.mul_smul, smul_smul, Fin.prod_univ_succ, mul_comm]
theorem seqProd_comm_of_comm {M : Type*} [Monoid M] :
    ∀ {K : ℕ} (P : Fin K → M) (x : M),(∀ i, x * P i = P i * x) →
      x * seqProd P = seqProd P * x
  | 0, _, _, _ => by simp [seqProd]
  | _ + 1, P, x, hcomm => by
    dsimp only [seqProd]
    rw [← mul_assoc, seqProd_comm_of_comm (fun j ↦ P j.succ) x (fun j ↦ hcomm j.succ),
      mul_assoc, hcomm 0, ← mul_assoc]
theorem norm_seqProd_sub_mul_seqProd_proj_le {A : Type*} [NormedRing A] [NormOneClass A] :
    ∀ {K : ℕ} (W U P : Fin K → A), (∀ i, ‖W i‖ ≤ 1) → (∀ i, ‖U i‖ ≤ 1) → (∀ i, ‖P i‖ ≤ 1) →
      (∀ i j : Fin K, i ≠ j → W i * P j = P j * W i) →
      (∀ i j : Fin K, i ≠ j → U i * P j = P j * U i) →
      ‖(seqProd W - seqProd U) * seqProd P‖ ≤ ∑ i : Fin K, ‖(W i - U i) * P i‖
  | 0, _, _, _, _, _, _, _, _ => by simp [seqProd]
  | K + 1, W, U, P, hW, hU, hP, hCW, hCU => by
    dsimp only [seqProd]
    let Wt := seqProd (fun j : Fin K ↦ W j.succ)
    let Ut := seqProd (fun j : Fin K ↦ U j.succ)
    let Pt := seqProd (fun j : Fin K ↦ P j.succ)
    have hW0Pt := seqProd_comm_of_comm (fun j : Fin K ↦ P j.succ) (W 0)
      (fun j ↦ hCW 0 j.succ (Fin.succ_ne_zero j).symm)
    have hU0Pt := seqProd_comm_of_comm (fun j : Fin K ↦ P j.succ) (U 0)
      (fun j ↦ hCU 0 j.succ (Fin.succ_ne_zero j).symm)
    have hDecomp : (Wt * W 0 - Ut * U 0) * (Pt * P 0) =
        (Wt * Pt) * ((W 0 - U 0) * P 0) + ((Wt - Ut) * Pt) * (U 0 * P 0) := by
      rw [sub_mul, mul_assoc Wt, ← mul_assoc (W 0), hW0Pt, mul_assoc Pt, ← mul_assoc Wt,
        mul_assoc Ut, ← mul_assoc (U 0), hU0Pt, mul_assoc Pt, ← mul_assoc Ut]
      simp only [sub_mul, mul_sub]
      abel
    have hWtPt : ‖Wt * Pt‖ ≤ 1 := (norm_mul_le _ _).trans
      ((mul_le_mul (norm_seqProd_le_one _ fun j ↦ hW j.succ)
        (norm_seqProd_le_one _ fun j ↦ hP j.succ) (norm_nonneg _) zero_le_one).trans (one_mul 1).le)
    have hU0P0 : ‖U 0 * P 0‖ ≤ 1 := (norm_mul_le _ _).trans
      ((mul_le_mul (hU 0) (hP 0) (norm_nonneg _) zero_le_one).trans (one_mul 1).le)
    have ht1 : ‖(Wt * Pt) * ((W 0 - U 0) * P 0)‖ ≤ ‖(W 0 - U 0) * P 0‖ :=
      (norm_mul_le _ _).trans
        ((mul_le_mul_of_nonneg_right hWtPt (norm_nonneg _)).trans (one_mul _).le)
    have ht2 :
        ‖((Wt - Ut) * Pt) * (U 0 * P 0)‖ ≤ ∑ j : Fin K, ‖(W j.succ - U j.succ) * P j.succ‖ :=
      ((norm_mul_le _ _).trans ((mul_le_mul_of_nonneg_left hU0P0 (norm_nonneg _)).trans
        (mul_one _).le)).trans (norm_seqProd_sub_mul_seqProd_proj_le (fun j ↦ W j.succ)
        (fun j ↦ U j.succ) (fun j ↦ P j.succ) (fun j ↦ hW j.succ) (fun j ↦ hU j.succ)
        (fun j ↦ hP j.succ) (fun i j hij ↦ hCW i.succ j.succ (hij ∘ Fin.succ_inj.mp))
        (fun i j hij ↦ hCU i.succ j.succ (hij ∘ Fin.succ_inj.mp)))
    rw [hDecomp, Fin.sum_univ_succ]
    exact (norm_add_le _ _).trans (add_le_add ht1 ht2)
theorem seqProd_mul_absorb {M : Type*} [Monoid M] :
    ∀ {K : ℕ} (P : Fin K → M) (Q : M),(∀ i, P i * Q = Q) → seqProd P * Q = Q
  | 0, _, Q, _ => by simp [seqProd]
  | _ + 1, P, Q, h => by
    dsimp only [seqProd]
    rw [mul_assoc, h 0, seqProd_mul_absorb (fun j ↦ P j.succ) Q (fun j ↦ h j.succ)]
theorem inv_sqrt_two_eq_sqrtHalf : ((√2 : ℂ)⁻¹) = sqrtHalf := by
  unfold sqrtHalf
  have h : (√2 : ℝ)⁻¹ = √(1 / 2) := by
    rw [Real.sqrt_div (by norm_num), Real.sqrt_one, one_div]
  exact_mod_cast h
theorem sqrtHalf_eq_real : sqrtHalf = ((Real.sqrt 2 / 2 : ℝ) : ℂ) := by
  unfold sqrtHalf
  congr 1
  rw [Real.sqrt_div zero_le_one, Real.sqrt_one, div_eq_iff (Real.sqrt_ne_zero'.mpr two_pos)]
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
theorem omega8_cube_eq : omega8 ^ 3 = (-1 + Complex.I) / (√2 : ℂ) := by
  rw [pow_succ, omega8_sq]
  dsimp [omega8]
  linear_combination (1 / (√2 : ℂ)) * Complex.I_sq
theorem omega8_re_im : omega8.re = Real.sqrt 2 / 2 ∧ omega8.im = Real.sqrt 2 / 2 := by
  dsimp [omega8]
  rw [div_eq_mul_inv, inv_sqrt_two_eq_sqrtHalf, sqrtHalf_eq_real]
  simp [Complex.mul_re, Complex.mul_im]
theorem omega8_cube_re_im :
    (omega8 ^ 3).re = -(Real.sqrt 2 / 2) ∧ (omega8 ^ 3).im = Real.sqrt 2 / 2 := by
  rw [pow_succ, omega8_sq]
  simp [Complex.mul_re, Complex.mul_im, omega8_re_im.1, omega8_re_im.2]
theorem zw_toComplex_re (z : Zw) :
    (z.toComplex).re = (z.c0 : ℝ) + ((z.c1 : ℝ) - (z.c3 : ℝ)) * (Real.sqrt 2 / 2) := by
  rw [Zw.toComplex, omega8_sq]
  simp only [Complex.add_re, Complex.mul_re, Complex.intCast_re, Complex.intCast_im,
    Complex.I_re, Complex.I_im, omega8_re_im.1, omega8_cube_re_im.1, zero_mul, sub_zero, mul_zero]
  ring
theorem zw_toComplex_im (z : Zw) :
    (z.toComplex).im = (z.c2 : ℝ) + ((z.c1 : ℝ) + (z.c3 : ℝ)) * (Real.sqrt 2 / 2) := by
  rw [Zw.toComplex, omega8_sq]
  simp only [Complex.add_im, Complex.mul_im, Complex.intCast_re, Complex.intCast_im,
    Complex.I_re, Complex.I_im, omega8_re_im.2, omega8_cube_re_im.2, zero_mul, add_zero, mul_one]
  ring
theorem sqrtHalf_pow_even (k : ℕ) : sqrtHalf ^ (2 * k) = (((1 / 2 : ℝ) ^ k : ℝ) : ℂ) := by
  rw [sqrtHalf_eq_real, ← Complex.ofReal_pow, pow_mul]
  congr 2
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
theorem sqrtHalf_pow_odd (k : ℕ) :
    sqrtHalf ^ (2 * k + 1) = ((((1 / 2 : ℝ) ^ k * (Real.sqrt 2 / 2)) : ℝ) : ℂ) := by
  rw [pow_succ, sqrtHalf_pow_even k, sqrtHalf_eq_real, ← Complex.ofReal_mul]
theorem eq_add_mul_sqrt2 {x a1 b1 a2 b2 : ℝ} (hx : x = a1 + b1 * Real.sqrt 2) (ha : a1 = a2)
    (hb : b1 = b2) : x = a2 + b2 * Real.sqrt 2 := by
  rw [hx, ha, hb]
private theorem mat2Zw_col0_eq (m : Mat2Zw) (y : Fin 2) :
    m.toMatrix y 0 = sqrtHalf ^ m.h * (if y = 0 then m.m00 else m.m10).toComplex := by
  fin_cases y <;> simp [Mat2Zw.toMatrix]
theorem mat2Zw_entry_even_re (m : Mat2Zw) (k : ℕ) (hk : m.h = 2 * k) (y : Fin 2) :
    (m.toMatrix y 0).re = ((if y = 0 then m.m00 else m.m10).c0 : ℝ) / (2 : ℝ) ^ k + (((if y =
    0 then m.m00 else m.m10).c1 : ℝ) - ((if y = 0 then m.m00 else m.m10).c3 : ℝ)) / (2 : ℝ) ^
    (k + 1) * Real.sqrt 2 := by
  rw [mat2Zw_col0_eq, hk, sqrtHalf_pow_even k]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    zw_toComplex_re]
  rw [pow_succ, _root_.one_div_pow]
  field_simp [show (2 : ℝ) ^ k ≠ 0 by positivity]
theorem mat2Zw_entry_even_im (m : Mat2Zw) (k : ℕ) (hk : m.h = 2 * k) (y : Fin 2) :
    (m.toMatrix y 0).im = ((if y = 0 then m.m00 else m.m10).c2 : ℝ) / (2 : ℝ) ^ k + (((if y =
    0 then m.m00 else m.m10).c1 : ℝ) + ((if y = 0 then m.m00 else m.m10).c3 : ℝ)) / (2 : ℝ) ^
    (k + 1) * Real.sqrt 2 := by
  rw [mat2Zw_col0_eq, hk, sqrtHalf_pow_even k]
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero,
    zw_toComplex_im]
  rw [pow_succ, _root_.one_div_pow]
  field_simp [show (2 : ℝ) ^ k ≠ 0 by positivity]
theorem mat2Zw_entry_odd_re (m : Mat2Zw) (k : ℕ) (hk : m.h = 2 * k + 1) (y : Fin 2) :
    (m.toMatrix y 0).re = (((if y = 0 then m.m00 else m.m10).c1 : ℝ) -
      ((if y = 0 then m.m00 else m.m10).c3 : ℝ)) / (2 : ℝ) ^ (k + 1) +
      ((if y = 0 then m.m00 else m.m10).c0 : ℝ) / (2 : ℝ) ^ (k + 1) * Real.sqrt 2 := by
  rw [mat2Zw_col0_eq, hk, sqrtHalf_pow_odd k]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    zw_toComplex_re]
  rw [pow_succ, _root_.one_div_pow]
  field_simp [show (2 : ℝ) ^ k ≠ 0 by positivity]
  ring_nf
  rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  ring
theorem mat2Zw_entry_odd_im (m : Mat2Zw) (k : ℕ) (hk : m.h = 2 * k + 1) (y : Fin 2) :
    (m.toMatrix y 0).im = (((if y = 0 then m.m00 else m.m10).c1 : ℝ) +
      ((if y = 0 then m.m00 else m.m10).c3 : ℝ)) / (2 : ℝ) ^ (k + 1) +
      ((if y = 0 then m.m00 else m.m10).c2 : ℝ) / (2 : ℝ) ^ (k + 1) * Real.sqrt 2 := by
  rw [mat2Zw_col0_eq, hk, sqrtHalf_pow_odd k]
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero,
    zw_toComplex_im]
  rw [pow_succ, _root_.one_div_pow]
  field_simp [show (2 : ℝ) ^ k ≠ 0 by positivity]
  ring_nf
  rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  ring
theorem qubit_H_col_zero_eq (y : Fin 2) : Qubit.H.1 y 0 = ((Real.sqrt 2 / 2 : ℝ) : ℂ) := by
  have h : Qubit.H.1 y 0 = sqrtHalf := by
    fin_cases y <;> simp [Qubit.H, inv_sqrt_two_eq_sqrtHalf]
  rw [h, sqrtHalf_eq_real]
theorem ideal_col0_of_ge2 {idx : ℕ} (h2 : 2 ≤ idx) (zp zq zr : ℤ) : (((pythPhase zp zq zr •
    (idealPhaseGradDiagBit idx * Qubit.H).1) 0 0).re = (((zp : ℝ) / (zr : ℝ) * Real.cos
    (phaseGradAngle idx) - (zq : ℝ) / (zr : ℝ) * Real.sin (phaseGradAngle idx)) / 2) *
    Real.sqrt 2) ∧ (((pythPhase zp zq zr • (idealPhaseGradDiagBit idx * Qubit.H).1) 0 0).im =
    (((zq : ℝ) / (zr : ℝ) * Real.cos (phaseGradAngle idx) + (zp : ℝ) / (zr : ℝ) * Real.sin
    (phaseGradAngle idx)) / 2) * Real.sqrt 2) ∧ (((pythPhase zp zq zr • (idealPhaseGradDiagBit
    idx * Qubit.H).1) 1 0).re = (((zp : ℝ) / (zr : ℝ) * Real.cos (phaseGradAngle idx) + (zq :
    ℝ) / (zr : ℝ) * Real.sin (phaseGradAngle idx)) / 2) * Real.sqrt 2) ∧ (((pythPhase zp zq zr
    • (idealPhaseGradDiagBit idx * Qubit.H).1) 1 0).im = (((zq : ℝ) / (zr : ℝ) * Real.cos
    (phaseGradAngle idx) - (zp : ℝ) / (zr : ℝ) * Real.sin (phaseGradAngle idx)) / 2) *
    Real.sqrt 2) := by
  let θ := phaseGradAngle idx
  have hU (y : Fin 2) : (pythPhase zp zq zr • (idealPhaseGradDiagBit idx * Qubit.H).1) y 0 =
      pythPhase zp zq zr * ((CatalystPrep.rzDiagMatrix θ * Qubit.H.1) y 0) := by
    rw [Submonoid.coe_mul, Matrix.smul_apply, smul_eq_mul, idealPhaseGradDiagBit,
      ite_eq_right (by omega), ite_eq_right (by omega)]
    rfl
  have hexp_pos : Complex.exp (θ * Complex.I) = (Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I :=
    Complex.exp_mul_I (θ : ℂ) ▸ by simp
  have hexp_neg :
      Complex.exp (-(θ * Complex.I)) = (Real.cos θ : ℂ) - (Real.sin θ : ℂ) * Complex.I := by
    rw [show -(θ * Complex.I) = ((-θ : ℝ) : ℂ) * Complex.I by rw [Complex.ofReal_neg, neg_mul],
      Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg, Real.sin_neg,
      Complex.ofReal_neg]
    ring
  simp only [hU 0, hU 1, CatalystPrep.rzDiagMatrix, Matrix.diagonal_mul,
    Matrix.cons_val_one, Matrix.cons_val_zero, qubit_H_col_zero_eq 0, qubit_H_col_zero_eq 1,
    hexp_pos, hexp_neg]
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
      Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, pythPhase_re, pythPhase_im, θ] <;>
    ring
theorem wire_err_zero_0 :
    (wordMatrix2 (catPrepWord 0) - zCatBit 0 • (idealPhaseGradDiagBit 0 * Qubit.H).1) * p0Mat2 =
      0 := by
  have hy (y : Fin 2) :
      (wordMatrix2 (catPrepWord 0) - zCatBit 0 • (idealPhaseGradDiagBit 0 * Qubit.H).1) y 0 =
        0 := by
    unfold catPrepWord zCatBit idealPhaseGradDiagBit
    simp only [↓reduceIte, one_smul, Submonoid.coe_mul]
    dsimp [wordMatrix2, evalList, matId, Mat2Zw.toMatrix, zwAdd, zwSub, zwMulI, Zw.toComplex]
    fin_cases y <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Qubit.Z, Qubit.H, inv_sqrt_two_eq_sqrtHalf]
  rw [mul_p0Mat2_decomp, hy 0, hy 1, zero_smul, zero_smul, add_zero]
theorem wire_err_zero_1 :
    (wordMatrix2 (catPrepWord 1) - zCatBit 1 • (idealPhaseGradDiagBit 1 * Qubit.H).1) * p0Mat2 =
      0 := by
  have hs_inv : (Qubit.S⁻¹).1 = Matrix.diagonal ![1, -Complex.I] := by
    change star Qubit.S.1 = _
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Qubit.S]
  have hy (y : Fin 2) :
      (wordMatrix2 (catPrepWord 1) - zCatBit 1 • (idealPhaseGradDiagBit 1 * Qubit.H).1) y 0 =
        0 := by
    rw [Matrix.sub_apply]
    unfold catPrepWord zCatBit idealPhaseGradDiagBit
    simp only [Nat.one_ne_zero, ↓reduceIte, Submonoid.coe_mul, one_smul]
    rw [hs_inv, Matrix.diagonal_mul, qubit_H_col_zero_eq y, ← sqrtHalf_eq_real]
    fin_cases y <;>
      dsimp [wordMatrix2, evalList, matId, Mat2Zw.toMatrix, zwAdd, zwSub, zwMulI, Zw.toComplex] <;>
      simp only [omega8_sq] <;> ring
  rw [mul_p0Mat2_decomp, hy 0, hy 1, zero_smul, zero_smul, add_zero]
theorem wire_err_zero_2 :
    (wordMatrix2 (catPrepWord 2) - zCatBit 2 • (idealPhaseGradDiagBit 2 * Qubit.H).1) * p0Mat2 =
      0 := by
  have hU (y : Fin 2) : (zCatBit 2 • (idealPhaseGradDiagBit 2 * Qubit.H).1) y 0 =
      Complex.exp (-(phaseGradAngle 2 * Complex.I)) *
        ((CatalystPrep.rzDiagMatrix (phaseGradAngle 2) * Qubit.H.1) y 0) := by
    rw [Submonoid.coe_mul, Matrix.smul_apply, smul_eq_mul, idealPhaseGradDiagBit,
      ite_eq_right (by decide), ite_eq_right (by decide)]
    rfl
  have hexp0 : Complex.exp (-(phaseGradAngle 2 * Complex.I)) *
      Complex.exp (phaseGradAngle 2 * Complex.I) = 1 := by
    rw [← Complex.exp_add, neg_add_cancel, Complex.exp_zero]
  have hexp1 : Complex.exp (-(phaseGradAngle 2 * Complex.I)) *
      Complex.exp (-(phaseGradAngle 2 * Complex.I)) = -omega8 ^ 3 := by
    have hang : -(phaseGradAngle 2 * Complex.I) + -(phaseGradAngle 2 * Complex.I) =
        ((-(Real.pi / 4) : ℝ) : ℂ) * Complex.I := by
      unfold phaseGradAngle
      push_cast
      ring
    rw [omega8_cube_eq, div_eq_mul_inv, inv_sqrt_two_eq_sqrtHalf, sqrtHalf_eq_real,
      ← Complex.exp_add, hang, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
      Real.cos_neg, Real.sin_neg, Real.cos_pi_div_four, Real.sin_pi_div_four, Complex.ofReal_neg]
    ring
  have hev2 : evalList (catPrepWord 2) matId =
      ⟨⟨1, 0, 0, 0⟩, ⟨1, 0, 0, 0⟩, ⟨0, 0, 0, -1⟩, ⟨0, 0, 0, 1⟩, 1⟩ := rfl
  have h00 : (wordMatrix2 (catPrepWord 2) - zCatBit 2 • (idealPhaseGradDiagBit 2 * Qubit.H).1) 0 0 =
      0 := by
    rw [Matrix.sub_apply, hU 0, CatalystPrep.rzDiagMatrix, Matrix.diagonal_mul,
      Matrix.cons_val_zero, ← mul_assoc, hexp0, one_mul, qubit_H_col_zero_eq 0, ← sqrtHalf_eq_real,
      wordMatrix2, hev2]
    dsimp [Mat2Zw.toMatrix, Zw.toComplex]
    ring
  have h10 : (wordMatrix2 (catPrepWord 2) - zCatBit 2 • (idealPhaseGradDiagBit 2 * Qubit.H).1) 1 0 =
      0 := by
    rw [Matrix.sub_apply, hU 1, CatalystPrep.rzDiagMatrix, Matrix.diagonal_mul,
      Matrix.cons_val_one, Matrix.cons_val_zero, ← mul_assoc, hexp1, qubit_H_col_zero_eq 1,
      ← sqrtHalf_eq_real, wordMatrix2, hev2]
    dsimp [Mat2Zw.toMatrix, Zw.toComplex]
    ring
  rw [mul_p0Mat2_decomp, h00, h10, zero_smul, zero_smul, add_zero]
theorem pi_bounds_2pow64 : (0x3243f6a8885a308d2 : ℝ) / 2 ^ 64 ≤ Real.pi ∧ Real.pi ≤
    (0x3243f6a8885a308d4 : ℝ) / 2 ^ 64 := by
  have hgt := Real.pi_gt_d20
  have hlt := Real.pi_lt_d20
  constructor <;> linarith
theorem sqrt2_bounds_1e15 : (0x50638410593e7 / 0x38d7ea4c68000 : ℝ) ≤ Real.sqrt 2 ∧ Real.sqrt
    2 ≤ (0x50638410593e8 / 0x38d7ea4c68000 : ℝ) := by
  constructor
  · rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 0x50638410593e7 / 0x38d7ea4c68000)]
    exact Real.sqrt_le_sqrt (by norm_num)
  · rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 0x50638410593e8 / 0x38d7ea4c68000)]
    exact Real.sqrt_le_sqrt (by norm_num)
theorem complex_norm_le_of_re_im {z : ℂ} {er ei c : ℝ}
    (hc : 0 ≤ c) (hr : |z.re| ≤ er) (hi : |z.im| ≤ ei) (hsq : er ^ 2 + ei ^ 2 ≤ c ^ 2) :
    ‖z‖ ≤ c := by
  have hz2 : ‖z‖ ^ 2 ≤ c ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    nlinarith [sq_le_sq.mpr (hr.trans (le_abs_self er)), sq_le_sq.mpr (hi.trans (le_abs_self ei))]
  nlinarith [norm_nonneg z]
theorem lin_comb_bounds {c s c_lo c_hi s_lo s_hi a b : ℝ}
    (hclo : c_lo ≤ c) (hchi : c ≤ c_hi) (hslo : s_lo ≤ s) (hshi : s ≤ s_hi) :
    (if 0 ≤ a then a * c_lo else a * c_hi) + (if 0 ≤ b then b * s_lo else b * s_hi) ≤ a * c + b *
      s ∧
    a * c + b * s ≤ (if 0 ≤ a then a * c_hi else a * c_lo) + (if 0 ≤ b then b * s_hi else b *
      s_lo) := by
  have ha : (if 0 ≤ a then a * c_lo else a * c_hi) ≤ a * c ∧
      a * c ≤ (if 0 ≤ a then a * c_hi else a * c_lo) := by
    by_cases h : 0 ≤ a <;> simp only [h, ↓reduceIte] <;> constructor <;> nlinarith
  have hb : (if 0 ≤ b then b * s_lo else b * s_hi) ≤ b * s ∧
      b * s ≤ (if 0 ≤ b then b * s_hi else b * s_lo) := by
    by_cases h : 0 ≤ b <;> simp only [h, ↓reduceIte] <;> constructor <;> nlinarith
  exact ⟨add_le_add ha.1 hb.1, add_le_add ha.2 hb.2⟩
theorem norm_one_sub_exp_I_le (θ : ℝ) :
    ‖(1 : ℂ) - Complex.exp (θ * Complex.I)‖ ≤ |θ| := by
  have hcos : 1 - Real.cos θ ≤ θ ^ 2 / 2 := by
    have ha := (cos_sin_taylor_alternating 1 |θ| (abs_nonneg θ)).1
    dsimp [cosTaylor, Nat.factorial] at ha
    rw [Real.cos_abs, sq_abs] at ha
    norm_num at ha
    linarith
  have hsq : ‖(1 : ℂ) - Complex.exp (θ * Complex.I)‖ ^ 2 ≤ |θ| ^ 2 := by
    have hexp : Complex.exp (θ * Complex.I) = (Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I :=
      Complex.exp_mul_I (θ : ℂ) ▸ by simp
    rw [hexp, Complex.sq_norm, Complex.normSq_apply, sq_abs]
    simp only [Complex.sub_re, Complex.add_re, Complex.one_re, Complex.ofReal_re,
      Complex.mul_re, Complex.I_re, Complex.ofReal_im, Complex.I_im,
      Complex.sub_im, Complex.add_im, Complex.one_im, Complex.mul_im]
    have hcs := Real.cos_sq_add_sin_sq θ
    nlinarith
  nlinarith [norm_nonneg ((1 : ℂ) - Complex.exp (θ * Complex.I)), abs_nonneg θ]
theorem wire_err_le_tail {idx : ℕ} (h20 : 20 ≤ idx) :
    ‖(wordMatrix2 (catPrepWord idx) - zCatBit idx • (idealPhaseGradDiagBit idx * Qubit.H).1) *
      p0Mat2‖ ≤ (4442885 / 1000000 : ℝ) * (1 / 2 : ℝ) ^ (idx + 1) := by
  rw [catPrepWord_of_ge20 h20, zCatBit_of_ge20 h20, one_smul]
  have hwH : wordMatrix2 [.H] = Qubit.H.1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      dsimp [wordMatrix2, evalList, matId, Mat2Zw.toMatrix, zwAdd, zwSub, Zw.toComplex,
        Pi.smul_apply, smul_eq_mul] <;>
      simp [Qubit.H, inv_sqrt_two_eq_sqrtHalf]
  rw [hwH, idealPhaseGradDiagBit, ite_eq_right (by
    omega), ite_eq_right (by omega), Submonoid.coe_mul]
  let D := Qubit.H.1 - CatalystPrep.rzDiagMatrix (phaseGradAngle idx) * Qubit.H.1
  change ‖D * p0Mat2‖ ≤ _
  have hD0 : D 0 0 =
      ((1 : ℂ) - Complex.exp (phaseGradAngle idx * Complex.I)) * ((Real.sqrt 2 / 2 : ℝ) : ℂ) := by
    dsimp [D]
    rw [CatalystPrep.rzDiagMatrix, Matrix.diagonal_mul, Matrix.cons_val_zero,
      qubit_H_col_zero_eq 0]
    ring
  have hD1 : D 1 0 = ((1 : ℂ) - Complex.exp ((-phaseGradAngle idx : ℝ) * Complex.I)) *
      ((Real.sqrt 2 / 2 : ℝ) : ℂ) := by
    dsimp [D]
    rw [CatalystPrep.rzDiagMatrix, Matrix.diagonal_mul, Matrix.cons_val_one,
      Matrix.cons_val_zero, qubit_H_col_zero_eq 1]
    push_cast
    ring
  have hθ0 : 0 ≤ phaseGradAngle idx := by
    unfold phaseGradAngle
    positivity
  have hn0 : ‖D 0 0‖ ≤ phaseGradAngle idx * (Real.sqrt 2 / 2) := by
    rw [hD0, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ Real.sqrt 2 / 2)]
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    simpa [abs_of_nonneg hθ0] using norm_one_sub_exp_I_le (phaseGradAngle idx)
  have hn1 : ‖D 1 0‖ ≤ phaseGradAngle idx * (Real.sqrt 2 / 2) := by
    rw [hD1, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ Real.sqrt 2 / 2)]
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    simpa [abs_neg, abs_of_nonneg hθ0] using norm_one_sub_exp_I_le (-phaseGradAngle idx)
  refine (norm_mul_p0Mat2_le D).trans ((add_le_add hn0 hn1).trans ?_)
  have hprod : Real.sqrt 2 * Real.pi ≤ 4442885 / 1000000 := by
    nlinarith [pi_bounds_2pow64.2, sqrt2_bounds_1e15.2, Real.pi_pos, Real.sqrt_nonneg 2]
  unfold phaseGradAngle
  have heq : (Real.pi / (2 : ℝ) ^ (idx + 1)) * (Real.sqrt 2 / 2) +
      (Real.pi / (2 : ℝ) ^ (idx + 1)) * (Real.sqrt 2 / 2) =
      (Real.sqrt 2 * Real.pi) * ((1 / 2 : ℝ) ^ (idx + 1)) := by
    rw [_root_.one_div_pow]
    field_simp [show (2 : ℝ) ^ (idx + 1) ≠ 0 by positivity]
    ring
  rw [heq]
  exact mul_le_mul_of_nonneg_right hprod (by positivity)
end ConfigZeroAncCatPrep1q
end ZeroAncCatPrep1q
def substActiveSingleCat {Var : Type} {mPayload B_tot kWorkConst mWork n : ℕ}
    (hm1 : 1 ≤ mWork) (v : Var) (rAct : QRegister (kActSingleCatClosure mPayload B_tot
    kWorkConst) n) (rWork : QRegister mWork n)
    (c : Circuit (kActSingleCatClosure mPayload B_tot kWorkConst)) : DynamicCircuit Var n :=
  substCircuit v (rWork ⟨0, by omega⟩) (Circuit.onRegister rAct c)
@[simp]
theorem substActiveSingleCat_count_TOFF {Var : Type} {mPayload B_tot kWorkConst mWork n : ℕ}
    (hm1 : 1 ≤ mWork) (v : Var) (rAct : QRegister (kActSingleCatClosure mPayload B_tot
    kWorkConst) n) (rWork : QRegister mWork n)
    (c : Circuit (kActSingleCatClosure mPayload B_tot kWorkConst)) :
    (substActiveSingleCat hm1 v rAct rWork c).count PrimitiveGate.TOFF = 0 :=
    count_substCircuit_toff _ _ _
theorem substActiveSingleCat_count_T_le {Var : Type} {mPayload B_tot kWorkConst mWork n : ℕ}
    (hm1 : 1 ≤ mWork) (v : Var) (rAct : QRegister (kActSingleCatClosure mPayload B_tot
    kWorkConst) n) (rWork : QRegister mWork n)
    (c : Circuit (kActSingleCatClosure mPayload B_tot kWorkConst)) :
    (substActiveSingleCat hm1 v rAct rWork c).count PrimitiveGate.T ≤ c.count PrimitiveGate.T
    + 4 * c.count PrimitiveGate.TOFF := by
  refine (count_substCircuit_t_le _ _ _).trans ?_
  simp [Circuit.count_onRegister]
theorem realizesCleanWorkspace_substActiveSingleCat {Var : Type} [Fintype Var]
    [DecidableEq Var] {mPayload B_tot kWorkConst mWork n : ℕ} (hm1 : 1 ≤ mWork) (v : Var)
    (rAct : QRegister (kActSingleCatClosure mPayload B_tot kWorkConst) n)
    (rWork : QRegister mWork n) (hDisj : rAct.DisjointWires rWork)
    (c : Circuit (kActSingleCatClosure mPayload B_tot kWorkConst)) :
    DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace rAct rWork c.eval
    (substActiveSingleCat hm1 v rAct rWork c) := by
  let qToff : Wire n := rWork ⟨0, by omega⟩
  have hSub : QRegister.singleton qToff = rWork.compose (QRegister.block 0 1 hm1) := by
    apply SingleCatClosureAlt.qreg_ext; intro i; fin_cases i; rfl
  have hDisj1 : rAct.DisjointWires (QRegister.singleton qToff) := by
    rw [hSub]; exact hDisj.compose_right _
  have h0 := realizesCleanWorkspace_substCircuit_active (Nat.le_refl 1) v
    rAct (QRegister.singleton qToff) hDisj1 c
  rw [hSub] at h0
  exact h0.widenWorkspace
noncomputable abbrev pCat0SingleCat (mPayload B_tot kWorkConst : ℕ) :
    Operator (2 ^ (kActSingleCatClosure mPayload B_tot kWorkConst)) :=
  (rCatScratchInSingleCat mPayload B_tot kWorkConst).basisOutcomeProjector 0
noncomputable def uCatNormSingleCat (mPayload B_tot kWorkConst : ℕ) :
    Unitary (2 ^ (kActSingleCatClosure mPayload B_tot kWorkConst)) :=
  (rCatTotInSingleCat mPayload B_tot kWorkConst).embedUnitary (U_cat_B_normalized B_tot)
structure SingleCatSelectImpl (mPayload B_tot : ℕ) (qft : FullSysQft654Bundle)
    (sel : FullSysSelectOracleBundle mPayload 48) where
  uSelCat : SpecsAux.SpecMirror.Configuration → Unitary (2 ^ (fullSysBEWires mPayload + B_tot))
  hIntertwinesSel : ∀ c,
    let rBE0 : QRegister (fullSysBEWires mPayload) (fullSysBEWires mPayload + B_tot) :=
      QRegister.block 0 (fullSysBEWires mPayload)
        (FullSysWalkStepEndpoint.fullSys_zero_add_le (fullSysBEWires mPayload) B_tot)
    let rCat0 : QRegister B_tot (fullSysBEWires mPayload + B_tot) :=
      QRegister.block (fullSysBEWires mPayload) B_tot le_rfl
    IntertwinesCat
      (rCat0.embedUnitary (U_cat_B_normalized B_tot)).1
      (rCat0.basisOutcomeProjector 0)
      (uSelCat c).1
      (rBE0.embedUnitary ((beCoreBlock mPayload).embedUnitary
        (fullSysSelectEffUnitary qft sel c))).1
abbrev rBESelLoc (mPayload B_tot : ℕ) : QRegister (fullSysBEWires mPayload)
    (fullSysBEWires mPayload + B_tot) := QRegister.block 0 (fullSysBEWires mPayload)
    (FullSysWalkStepEndpoint.fullSys_zero_add_le (fullSysBEWires mPayload) B_tot)
abbrev rCatSelLoc (mPayload B_tot : ℕ) : QRegister B_tot (fullSysBEWires mPayload + B_tot) :=
    QRegister.block (fullSysBEWires mPayload) B_tot le_rfl
theorem rBESelLoc_disj_rCatSelLoc (mPayload B_tot : ℕ) :
    (rBESelLoc mPayload B_tot).DisjointWires (rCatSelLoc mPayload B_tot) :=
  QRegister.block_disjoint_of_le 0 (fullSysBEWires mPayload) (fullSysBEWires mPayload) B_tot
    (FullSysWalkStepEndpoint.fullSys_zero_add_le (fullSysBEWires mPayload) B_tot) le_rfl
    (FullSysCatSegmentBridge.fullSys_zero_add_le_self (fullSysBEWires mPayload))
theorem singleCat_seven_le_of_48 {B_tot : ℕ} (hB48 : 48 ≤ B_tot) : 7 ≤ B_tot :=
  Nat.le_trans (by decide : 7 ≤ 48) hB48
theorem compose_concat_eq_singleCat {a b M N : ℕ} (rOuter : QRegister M N)
    (r1 : QRegister a M) (r2 : QRegister b M) (h12 : r1.DisjointWires r2) :
    (rOuter.compose r1).concat (rOuter.compose r2)
    (disjointWires_compose_of_disjoint rOuter h12) = rOuter.compose (r1.concat r2 h12) :=
  SingleCatClosureAlt.qreg_ext fun idx ↦
    Fin.addCases
      (fun i ↦ by
        rw [QRegister.concat_apply_left, QRegister.compose_apply, QRegister.compose_apply,
          QRegister.concat_apply_left])
      (fun j ↦ by
        rw [QRegister.concat_apply_right, QRegister.compose_apply, QRegister.compose_apply,
          QRegister.concat_apply_right]) idx
set_option maxHeartbeats 800000 in
-- Intertwining induction over concatenated catalyst registers.
theorem intertwinesCat_topCatSlice_of_localCat {n m_sub B B_tot : ℕ} (hB : B ≤ B_tot)
    (rSub : QRegister m_sub n) (rCatTot : QRegister B_tot n)
    (hDisj : rSub.DisjointWires rCatTot) (W_cat : Unitary (2 ^ (m_sub + B)))
    (U_eff : Unitary (2 ^ m_sub))
    (hLocal : IntertwinesLocalCat (U_cat_B_normalized B) W_cat U_eff) : IntertwinesCat
    (rCatTot.embedUnitary (U_cat_B_normalized B_tot)).1 (rCatTot.basisOutcomeProjector 0)
    ((rSub.concat (rCatTot.compose (rTopCatSlice B B_tot hB)) (hDisj.compose_right
    _)).embedMatrix W_cat.1) (rSub.embedMatrix U_eff.1) := by
  let rSubTop := rSub.concat (rCatTot.compose (rTopCatSlice B B_tot hB)) (hDisj.compose_right _)
  let rAct0 : QRegister m_sub (m_sub + B) :=
    .block 0 m_sub (FullSysWalkStepEndpoint.fullSys_zero_add_le m_sub B)
  let rCat0 : QRegister B (m_sub + B) := .block m_sub B le_rfl
  have hJointAct : rSubTop.compose rAct0 = rSub :=
    SingleCatClosureAlt.qreg_ext fun i ↦ by
      rw [QRegister.compose_apply, show rAct0 i = Fin.castAdd B i from Fin.ext (Nat.zero_add i.val),
        QRegister.concat_apply_left]
  have hJointCat : rSubTop.compose rCat0 = rCatTot.compose (rTopCatSlice B B_tot hB) :=
    SingleCatClosureAlt.qreg_ext fun i ↦ by
      rw [QRegister.compose_apply, show rCat0 i = Fin.natAdd m_sub i from Fin.ext rfl,
        QRegister.concat_apply_right]
  have hEmbLocal := IntertwinesCat.embedMatrix rSubTop hLocal
  have hSubCatEq : rSubTop.embedMatrix (rCat0.embedUnitary (U_cat_B_normalized B)).1 =
      ((rCatTot.compose (rTopCatSlice B B_tot hB)).embedUnitary (U_cat_B_normalized B)).1 := by
    rw [QRegister.embedUnitary_val, QRegister.embedUnitary_val, ← QRegister.embedMatrix_compose,
      hJointCat]
  have hSubProjEq : rSubTop.embedMatrix (rCat0.basisOutcomeProjector 0) =
      (rCatTot.compose (rTopCatSlice B B_tot hB)).basisOutcomeProjector 0 := by
    rw [QRegister.basisOutcomeProjector, ← QRegister.embedMatrix_compose, hJointCat,
      ← QRegister.basisOutcomeProjector]
  have hSubEffEq : rSubTop.embedMatrix (rAct0.embedUnitary U_eff).1 = rSub.embedMatrix U_eff.1 := by
    rw [QRegister.embedUnitary_val, ← QRegister.embedMatrix_compose, hJointAct]
  rw [hSubCatEq, hSubProjEq, hSubEffEq] at hEmbLocal
  exact intertwinesCat_topCatSlice_of_embed hB rSub rCatTot hDisj W_cat.1 U_eff.1 hEmbLocal
set_option exponentiation.threshold 256
def slackParkStepsSingleCat (mPayload B_tot kWorkConst : ℕ) : List
    (RevStep (kActSingleCatClosure mPayload B_tot kWorkConst)) := [RevStep.x (qSigInSingleCat
    mPayload B_tot kWorkConst), RevStep.toff (qSigInSingleCat mPayload B_tot kWorkConst)
    (qCoin2InSingleCat mPayload B_tot kWorkConst) (qSlack2InSingleCat mPayload B_tot
    kWorkConst), RevStep.cnot (qSlack2InSingleCat mPayload B_tot kWorkConst)
    (qCoin2InSingleCat mPayload B_tot kWorkConst), RevStep.x (qCoin1InSingleCat mPayload B_tot
    kWorkConst), RevStep.toff (qSigInSingleCat mPayload B_tot kWorkConst) (qCoin1InSingleCat
    mPayload B_tot kWorkConst) (qSlack1InSingleCat mPayload B_tot kWorkConst), RevStep.x
    (qCoin1InSingleCat mPayload B_tot kWorkConst), RevStep.cnot (qSlack1InSingleCat mPayload
    B_tot kWorkConst) (qCoin1InSingleCat mPayload B_tot kWorkConst), RevStep.toff
    (qSigInSingleCat mPayload B_tot kWorkConst) (qCoin0InSingleCat mPayload B_tot kWorkConst)
    (qSlack0InSingleCat mPayload B_tot kWorkConst), RevStep.cnot (qSlack0InSingleCat mPayload
    B_tot kWorkConst) (qCoin0InSingleCat mPayload B_tot kWorkConst), RevStep.x
    (qSigInSingleCat mPayload B_tot kWorkConst)]
def cSlackParkSingleCat (mPayload B_tot kWorkConst : ℕ) :
    Circuit (kActSingleCatClosure mPayload B_tot kWorkConst) :=
  compileRevList (slackParkStepsSingleCat mPayload B_tot kWorkConst)
def cSlackUnparkSingleCat (mPayload B_tot kWorkConst : ℕ) :
    Circuit (kActSingleCatClosure mPayload B_tot kWorkConst) :=
  compileRevList (slackParkStepsSingleCat mPayload B_tot kWorkConst).reverse
@[simp] theorem cSlackParkSingleCat_count_T (mPayload B_tot kWorkConst : ℕ) :
    (cSlackParkSingleCat mPayload B_tot kWorkConst).count PrimitiveGate.T = 0 :=
  compileRevList_count_T _
@[simp] theorem cSlackUnparkSingleCat_count_T (mPayload B_tot kWorkConst : ℕ) :
    (cSlackUnparkSingleCat mPayload B_tot kWorkConst).count PrimitiveGate.T = 0 :=
  compileRevList_count_T _
theorem cSlackParkSingleCat_count_TOFF_le (mPayload B_tot kWorkConst : ℕ) :
    (cSlackParkSingleCat mPayload B_tot kWorkConst).count PrimitiveGate.TOFF ≤ 3 := by
  rw [cSlackParkSingleCat, compileRevList_count_TOFF]
  have h2 := RevStep.toffCount_le
    (RevStep.toff (qSigInSingleCat mPayload B_tot kWorkConst)
      (qCoin2InSingleCat mPayload B_tot kWorkConst) (qSlack2InSingleCat mPayload B_tot kWorkConst))
  have h1 := RevStep.toffCount_le
    (RevStep.toff (qSigInSingleCat mPayload B_tot kWorkConst)
      (qCoin1InSingleCat mPayload B_tot kWorkConst) (qSlack1InSingleCat mPayload B_tot kWorkConst))
  have h0 := RevStep.toffCount_le
    (RevStep.toff (qSigInSingleCat mPayload B_tot kWorkConst)
      (qCoin0InSingleCat mPayload B_tot kWorkConst) (qSlack0InSingleCat mPayload B_tot kWorkConst))
  simp only [slackParkStepsSingleCat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  dsimp [RevStep.toffCount] at h2 h1 h0 ⊢
  omega
theorem cSlackUnparkSingleCat_count_TOFF_le (mPayload B_tot kWorkConst : ℕ) :
    (cSlackUnparkSingleCat mPayload B_tot kWorkConst).count PrimitiveGate.TOFF ≤ 3 := by
  rw [cSlackUnparkSingleCat, compileRevList_count_TOFF, List.map_reverse, List.sum_reverse,
    ← compileRevList_count_TOFF]
  exact cSlackParkSingleCat_count_TOFF_le mPayload B_tot kWorkConst
def slackParkWireSingleCat (mPayload B_tot kWorkConst : ℕ) :
    Fin 7 → Wire (kActSingleCatClosure mPayload B_tot kWorkConst)
  | ⟨0, _⟩ => qSigInSingleCat mPayload B_tot kWorkConst
  | ⟨1, _⟩ => qCoin2InSingleCat mPayload B_tot kWorkConst
  | ⟨2, _⟩ => qCoin1InSingleCat mPayload B_tot kWorkConst
  | ⟨3, _⟩ => qCoin0InSingleCat mPayload B_tot kWorkConst
  | ⟨4, _⟩ => qSlack2InSingleCat mPayload B_tot kWorkConst
  | ⟨5, _⟩ => qSlack1InSingleCat mPayload B_tot kWorkConst
  | ⟨6, _⟩ => qSlack0InSingleCat mPayload B_tot kWorkConst
def slackParkWireOffsetSingleCat (mPayload B_tot : ℕ) : Fin 7 → ℕ
  | ⟨0, _⟩ => 6 + mPayload
  | ⟨1, _⟩ => 2
  | ⟨2, _⟩ => 1
  | ⟨3, _⟩ => 0
  | ⟨4, _⟩ => 1 + (6 + mPayload) + (B_tot + 0)
  | ⟨5, _⟩ => 1 + (6 + mPayload) + (B_tot + 1)
  | ⟨6, _⟩ => 1 + (6 + mPayload) + (B_tot + 2)
theorem slackParkWireSingleCat_val (mPayload B_tot kWorkConst : ℕ) (a : Fin 7) :
    (slackParkWireSingleCat mPayload B_tot kWorkConst a).val =
      SpecsAux.SpecMirror.systemQubits + slackParkWireOffsetSingleCat mPayload B_tot a := by
  fin_cases a <;>
    simp [slackParkWireSingleCat, slackParkWireOffsetSingleCat,
      qSigInSingleCat, qCoin2InSingleCat, qCoin1InSingleCat, qCoin0InSingleCat,
      qSlack2InSingleCat, qSlack1InSingleCat, qSlack0InSingleCat,
      rSlackSave3InSingleCat, rCatScratchInSingleCat, rAncInSingleCat,
      inCatScratchSingleCat, inSlack3SingleCat,
      mSegAncPoly, fullSysBEWires, fullSysRawAncWires]
theorem slackParkSingleCat_all_distinct (mPayload B_tot kWorkConst : ℕ) :
    Function.Injective (slackParkWireSingleCat mPayload B_tot kWorkConst) := by
  intro a b hab
  have hv : SpecsAux.SpecMirror.systemQubits + slackParkWireOffsetSingleCat mPayload B_tot a =
      SpecsAux.SpecMirror.systemQubits + slackParkWireOffsetSingleCat mPayload B_tot b := by
    rw [← slackParkWireSingleCat_val, ← slackParkWireSingleCat_val, hab]
  have hoff : slackParkWireOffsetSingleCat mPayload B_tot a = slackParkWireOffsetSingleCat
      mPayload B_tot b := Nat.add_left_cancel hv
  fin_cases a <;> fin_cases b <;> dsimp [slackParkWireOffsetSingleCat] at hoff <;>
    first | rfl | omega
theorem slackParkSingleCat_wires_disj_catTot (mPayload B_tot kWorkConst : ℕ) : qSigInSingleCat
    mPayload B_tot kWorkConst ∉ Set.range (rCatTotInSingleCat mPayload B_tot kWorkConst).wires
    ∧ qCoin2InSingleCat mPayload B_tot kWorkConst ∉ Set.range
    (rCatTotInSingleCat mPayload B_tot kWorkConst).wires ∧ qCoin1InSingleCat mPayload B_tot
    kWorkConst ∉ Set.range (rCatTotInSingleCat mPayload B_tot kWorkConst).wires ∧
    qCoin0InSingleCat mPayload B_tot kWorkConst ∉ Set.range
    (rCatTotInSingleCat mPayload B_tot kWorkConst).wires ∧ qSlack2InSingleCat mPayload B_tot
    kWorkConst ∉ Set.range (rCatTotInSingleCat mPayload B_tot kWorkConst).wires ∧
    qSlack1InSingleCat mPayload B_tot kWorkConst ∉ Set.range
    (rCatTotInSingleCat mPayload B_tot kWorkConst).wires ∧ qSlack0InSingleCat mPayload B_tot
    kWorkConst ∉ Set.range (rCatTotInSingleCat mPayload B_tot kWorkConst).wires := by
  have hcat : ∀ i : Fin B_tot, (rCatTotInSingleCat mPayload B_tot kWorkConst i).val =
      SpecsAux.SpecMirror.systemQubits + (1 + (6 + mPayload) + i.val) := by
    intro i
    simp [rCatTotInSingleCat, rCatScratchInSingleCat, rAncInSingleCat,
      inCatScratchSingleCat, inCatTotSingleCat,
      mSegAncPoly, fullSysRawAncWires]
  have hall : ∀ a : Fin 7, slackParkWireSingleCat mPayload B_tot kWorkConst a ∉ Set.range
      (rCatTotInSingleCat mPayload B_tot kWorkConst).wires := by
    intro a ⟨i, hi⟩
    have hv := congrArg Fin.val hi
    rw [hcat i, slackParkWireSingleCat_val mPayload B_tot kWorkConst a] at hv
    have hiB : i.val < B_tot := i.isLt
    fin_cases a <;> dsimp [slackParkWireOffsetSingleCat] at hv <;> omega
  exact ⟨hall 0, hall 1, hall 2, hall 3, hall 4, hall 5, hall 6⟩
theorem cSlackUnparkSingleCat_mul_cSlackParkSingleCat (mPayload B_tot kWorkConst : ℕ) :
    (cSlackUnparkSingleCat mPayload B_tot kWorkConst).eval.1 *
      (cSlackParkSingleCat mPayload B_tot kWorkConst).eval.1 = 1 := by
  apply matrix_ext_ket; intro β
  rw [← Matrix.mulVec_mulVec, cSlackParkSingleCat, cSlackUnparkSingleCat, compileRevList_mulVec_ket,
    compileRevList_mulVec_ket, runRevList_reverse, Matrix.one_mulVec]
theorem cSlackParkSingleCat_on_sig1_save3 (mPayload B_tot kWorkConst : ℕ) :
    (cSlackParkSingleCat mPayload B_tot kWorkConst).eval.1 *
      ((QRegister.singleton (qSigInSingleCat mPayload B_tot kWorkConst)).basisOutcomeProjector 1 *
        (rSlackSave3InSingleCat mPayload B_tot kWorkConst).basisOutcomeProjector 0) =
    (QRegister.singleton (qSigInSingleCat mPayload B_tot kWorkConst)).basisOutcomeProjector 1 *
      (rSlackSave3InSingleCat mPayload B_tot kWorkConst).basisOutcomeProjector 0 := by
  apply matrix_ext_ket; intro β
  have hinj := slackParkSingleCat_all_distinct mPayload B_tot kWorkConst
  have hne : ∀ (a b : Fin 7), a ≠ b → slackParkWireSingleCat mPayload B_tot kWorkConst a ≠
      slackParkWireSingleCat mPayload B_tot kWorkConst b := fun a b h heq ↦ h (hinj heq)
  have h01 := hne 0 1 (by decide); have h04 := hne 0 4 (by decide); have h14 := hne 1 4 (by decide)
  have h02 := hne 0 2 (by decide); have h05 := hne 0 5 (by decide); have h25 := hne 2 5 (by decide)
  have h03 := hne 0 3 (by decide); have h06 := hne 0 6 (by decide); have h36 := hne 3 6 (by decide)
  dsimp only [slackParkWireSingleCat] at h01 h04 h14 h02 h05 h25 h03 h06 h36
  simp only [← Matrix.mulVec_mulVec]
  rw [basisOutcomeProjector_zero_mulVec_ket]
  by_cases hv : localIdx (rSlackSave3InSingleCat mPayload B_tot kWorkConst) β = 0
  · rw [ite_eq_left hv, singleton_proj_one_mulVec_ket]
    by_cases hs1 : β (qSigInSingleCat mPayload B_tot kWorkConst) = 1
    · rw [ite_eq_left hs1, cSlackParkSingleCat, compileRevList_mulVec_ket]
      congr 1
      dsimp only [slackParkStepsSingleCat]
      let β₁ := (RevStep.x (qSigInSingleCat mPayload B_tot kWorkConst)).run β
      have hs0 : β₁ (qSigInSingleCat mPayload B_tot kWorkConst) = 0 := by
        dsimp only [β₁]
        rw [revStep_run_x, Function.update_self, hs1, one_add_one_zmod2]
      have hv2_1 : β₁ (qSlack2InSingleCat mPayload B_tot kWorkConst) = 0 := by
        dsimp only [β₁]
        rw [revStep_run_x, Function.update_of_ne h04.symm]
        exact apply_eq_zero_of_localIdx_eq_zero _ β hv ⟨0, by decide⟩
      have hv1_1 : β₁ (qSlack1InSingleCat mPayload B_tot kWorkConst) = 0 := by
        dsimp only [β₁]
        rw [revStep_run_x, Function.update_of_ne h05.symm]
        exact apply_eq_zero_of_localIdx_eq_zero _ β hv ⟨1, by decide⟩
      have hv0_1 : β₁ (qSlack0InSingleCat mPayload B_tot kWorkConst) = 0 := by
        dsimp only [β₁]
        rw [revStep_run_x, Function.update_of_ne h06.symm]
        exact apply_eq_zero_of_localIdx_eq_zero _ β hv ⟨2, by decide⟩
      change runRevList _ β₁ = β
      rw [parkZero_on_zero h01 h04 h14 _ β₁ hs0 hv2_1,
        parkOne_on_zero h02 h05 h25 _ β₁ hs0 hv1_1,
        parkZero_on_zero h03 h06 h36 _ β₁ hs0 hv0_1]
      change (RevStep.x (qSigInSingleCat mPayload B_tot kWorkConst)).run β₁ = β
      dsimp only [β₁]
      rw [revStep_run_x, revStep_run_x, Function.update_self,
        PolymorphicTopClosure.zmod2_add_one_add_one,
        update_idem_val, update_eq_self_of_eq β _ rfl]
    · simp only [ite_eq_right hs1, Matrix.mulVec_zero]
  · simp only [ite_eq_right hv, Matrix.mulVec_zero]
theorem cSlackUnparkSingleCat_on_sig1_save3 (mPayload B_tot kWorkConst : ℕ) :
    (cSlackUnparkSingleCat mPayload B_tot kWorkConst).eval.1 *
      ((QRegister.singleton (qSigInSingleCat mPayload B_tot kWorkConst)).basisOutcomeProjector 1 *
        (rSlackSave3InSingleCat mPayload B_tot kWorkConst).basisOutcomeProjector 0) =
    (QRegister.singleton (qSigInSingleCat mPayload B_tot kWorkConst)).basisOutcomeProjector 1 *
      (rSlackSave3InSingleCat mPayload B_tot kWorkConst).basisOutcomeProjector 0 := by
  conv_rhs =>
    rw [← Matrix.one_mul (_ * _),
      ← cSlackUnparkSingleCat_mul_cSlackParkSingleCat mPayload B_tot kWorkConst,
      Matrix.mul_assoc, cSlackParkSingleCat_on_sig1_save3]
theorem slack010_mul_cSlackParkSingleCat_sig0_save3 (mPayload B_tot kWorkConst : ℕ) :
    let P_slack010 :=
      (QRegister.singleton (qCoin2InSingleCat mPayload B_tot kWorkConst)).basisOutcomeProjector 0 *
      (QRegister.singleton (qCoin1InSingleCat mPayload B_tot kWorkConst)).basisOutcomeProjector 1 *
      (QRegister.singleton (qCoin0InSingleCat mPayload B_tot kWorkConst)).basisOutcomeProjector 0
    P_slack010 * ((cSlackParkSingleCat mPayload B_tot kWorkConst).eval.1 *
      ((QRegister.singleton (qSigInSingleCat mPayload B_tot kWorkConst)).basisOutcomeProjector 0 *
        (rSlackSave3InSingleCat mPayload B_tot kWorkConst).basisOutcomeProjector 0)) =
    (cSlackParkSingleCat mPayload B_tot kWorkConst).eval.1 *
      ((QRegister.singleton (qSigInSingleCat mPayload B_tot kWorkConst)).basisOutcomeProjector 0 *
        (rSlackSave3InSingleCat mPayload B_tot kWorkConst).basisOutcomeProjector 0) := by
  intro P_slack010
  apply matrix_ext_ket; intro β
  have hinj := slackParkSingleCat_all_distinct mPayload B_tot kWorkConst
  have hne : ∀ (a b : Fin 7), a ≠ b → slackParkWireSingleCat mPayload B_tot kWorkConst a ≠
      slackParkWireSingleCat mPayload B_tot kWorkConst b := fun a b h heq ↦ h (hinj heq)
  have h01 := hne 0 1 (by decide); have h04 := hne 0 4 (by decide); have h14 := hne 1 4 (by decide)
  have h02 := hne 0 2 (by decide); have h05 := hne 0 5 (by decide); have h25 := hne 2 5 (by decide)
  have h03 := hne 0 3 (by decide); have h06 := hne 0 6 (by decide); have h36 := hne 3 6 (by decide)
  have h12 := hne 1 2 (by decide); have h13 := hne 1 3 (by decide); have h15 := hne 1 5 (by decide)
  have h16 := hne 1 6 (by decide); have h23 := hne 2 3 (by decide)
  have h26 := hne 2 6 (by decide); have h45 := hne 4 5 (by decide); have h46 := hne 4 6 (by decide)
  have h56 := hne 5 6 (by decide)
  dsimp only [slackParkWireSingleCat] at h01 h04 h14 h02 h05 h25 h03 h06 h36 h12 h13 h15 h16 h23 h26
  dsimp only [slackParkWireSingleCat] at h45 h46 h56
  simp only [P_slack010, ← Matrix.mulVec_mulVec]
  rw [basisOutcomeProjector_zero_mulVec_ket]
  by_cases hv : localIdx (rSlackSave3InSingleCat mPayload B_tot kWorkConst) β = 0
  · rw [ite_eq_left hv, singleton_proj_zero_mulVec_ket]
    by_cases hs0 : β (qSigInSingleCat mPayload B_tot kWorkConst) = 0
    · rw [ite_eq_left hs0, cSlackParkSingleCat, compileRevList_mulVec_ket]
      let β₁ := (RevStep.x (qSigInSingleCat mPayload B_tot kWorkConst)).run β
      have hs1_1 : β₁ (qSigInSingleCat mPayload B_tot kWorkConst) = 1 := by
        dsimp only [β₁]
        rw [revStep_run_x, Function.update_self, hs0, zero_add]
      have hv2_1 : β₁ (qSlack2InSingleCat mPayload B_tot kWorkConst) = 0 := by
        dsimp only [β₁]
        rw [revStep_run_x, Function.update_of_ne h04.symm]
        exact apply_eq_zero_of_localIdx_eq_zero _ β hv ⟨0, by decide⟩
      let β₂ := Function.update (Function.update β₁ (qSlack2InSingleCat mPayload B_tot
          kWorkConst) (β₁ (qCoin2InSingleCat mPayload B_tot kWorkConst)))
          (qCoin2InSingleCat mPayload B_tot kWorkConst) 0
      have hs1_2 : β₂ (qSigInSingleCat mPayload B_tot kWorkConst) = 1 := by
        dsimp only [β₂]
        rw [Function.update_of_ne h01, Function.update_of_ne h04, hs1_1]
      have hv1_2 : β₂ (qSlack1InSingleCat mPayload B_tot kWorkConst) = 0 := by
        dsimp only [β₂, β₁]
        rw [Function.update_of_ne h15.symm, Function.update_of_ne h45.symm, revStep_run_x,
          Function.update_of_ne h05.symm]
        exact apply_eq_zero_of_localIdx_eq_zero _ β hv ⟨1, by decide⟩
      let β₃ := Function.update (Function.update β₂ (qSlack1InSingleCat mPayload B_tot
          kWorkConst) (β₂ (qCoin1InSingleCat mPayload B_tot kWorkConst) + 1))
          (qCoin1InSingleCat mPayload B_tot kWorkConst) 1
      have hs1_3 : β₃ (qSigInSingleCat mPayload B_tot kWorkConst) = 1 := by
        dsimp only [β₃]
        rw [Function.update_of_ne h02, Function.update_of_ne h05, hs1_2]
      have hv0_3 : β₃ (qSlack0InSingleCat mPayload B_tot kWorkConst) = 0 := by
        dsimp only [β₃, β₂, β₁]
        rw [Function.update_of_ne h26.symm, Function.update_of_ne h56.symm,
          Function.update_of_ne h16.symm, Function.update_of_ne h46.symm, revStep_run_x,
          Function.update_of_ne h06.symm]
        exact apply_eq_zero_of_localIdx_eq_zero _ β hv ⟨2, by decide⟩
      let β₄ := Function.update (Function.update β₃ (qSlack0InSingleCat mPayload B_tot
          kWorkConst) (β₃ (qCoin0InSingleCat mPayload B_tot kWorkConst)))
          (qCoin0InSingleCat mPayload B_tot kWorkConst) 0
      have hRun : runRevList (slackParkStepsSingleCat mPayload B_tot kWorkConst) β =
          (RevStep.x (qSigInSingleCat mPayload B_tot kWorkConst)).run β₄ := by
        dsimp only [slackParkStepsSingleCat]
        change runRevList _ β₁ = (RevStep.x (qSigInSingleCat mPayload B_tot kWorkConst)).run β₄
        rw [parkZero_on_one h01 h04 h14 _ β₁ hs1_1 hv2_1,
          parkOne_on_one h02 h05 h25 _ β₂ hs1_2 hv1_2,
          parkZero_on_one h03 h06 h36 _ β₃ hs1_3 hv0_3]
        rfl
      have hγ0 : ((RevStep.x (qSigInSingleCat mPayload B_tot kWorkConst)).run β₄)
          (qCoin0InSingleCat mPayload B_tot kWorkConst) = 0 := by
        dsimp only [β₄]
        rw [revStep_run_x, Function.update_of_ne h03.symm, Function.update_self]
      have hγ1 : ((RevStep.x (qSigInSingleCat mPayload B_tot kWorkConst)).run β₄)
          (qCoin1InSingleCat mPayload B_tot kWorkConst) = 1 := by
        dsimp only [β₄, β₃]
        rw [revStep_run_x, Function.update_of_ne h02.symm, Function.update_of_ne h23,
          Function.update_of_ne h26, Function.update_self]
      have hγ2 : ((RevStep.x (qSigInSingleCat mPayload B_tot kWorkConst)).run β₄)
          (qCoin2InSingleCat mPayload B_tot kWorkConst) = 0 := by
        dsimp only [β₄, β₃, β₂]
        rw [revStep_run_x, Function.update_of_ne h01.symm, Function.update_of_ne h13,
          Function.update_of_ne h16, Function.update_of_ne h12, Function.update_of_ne h15,
          Function.update_self]
      rw [hRun, singleton_proj_zero_mulVec_ket, ite_eq_left hγ0, singleton_proj_one_mulVec_ket,
        ite_eq_left hγ1, singleton_proj_zero_mulVec_ket, ite_eq_left hγ2]
    · simp only [ite_eq_right hs0, Matrix.mulVec_zero]
  · simp only [ite_eq_right hv, Matrix.mulVec_zero]
theorem embed_slotBitProj_eq_singleton_singleCat {mPayload B_tot kWorkConst : ℕ}
    (wCore : Wire (fullSysCoreWires mPayload))
    (wAct : Wire (kActSingleCatClosure mPayload B_tot kWorkConst)) (hw : ((rBEInSingleCat
    mPayload B_tot kWorkConst).compose (beCoreBlock mPayload)) wCore = wAct) (b : Fin 2) :
    ((rBEInSingleCat mPayload B_tot kWorkConst).compose (beCoreBlock mPayload)).embedMatrix
    (slotBitProj wCore b) = (QRegister.singleton wAct).basisOutcomeProjector b := by
  apply matrix_ext_ket; intro β
  let rC := (rBEInSingleCat mPayload B_tot kWorkConst).compose (beCoreBlock mPayload)
  rw [slotBitProj, embedMatrix_diagonal_mulVec_ket]
  have hbit : basisBits (fullSysCoreWires mPayload) (localIdx rC β) wCore = β wAct := by
    have h1 : basisBits (fullSysCoreWires mPayload) (localIdx rC β) = fun j ↦ β (rC j) :=
      Equiv.apply_symm_apply (basisBitsEquiv (fullSysCoreWires mPayload)) (fun j ↦ β (rC j))
    exact (congrFun h1 wCore).trans (congrArg β hw)
  fin_cases b
  · change _ = ((QRegister.singleton wAct).basisOutcomeProjector 0).mulVec (ket β)
    rw [singleton_proj_zero_mulVec_ket]
    dsimp only [rC] at hbit
    rcases bit_cases (β wAct) with hb | hb <;> simp [hbit, hb]
  · change _ = ((QRegister.singleton wAct).basisOutcomeProjector 1).mulVec (ket β)
    rw [singleton_proj_one_mulVec_ket]
    dsimp only [rC] at hbit
    rcases bit_cases (β wAct) with hb | hb <;> simp [hbit, hb]
theorem fullSysSelectEff_on_slack010_singleCat {mPayload B_tot kWorkConst : ℕ}
    (qft : FullSysQft654Bundle)
    (sel : FullSysSelectOracleBundle mPayload 48)
    (c : SpecsAux.SpecMirror.Configuration)
    (hTwist_s2 : (sel.uTwist c).1 * slotBitProj (iSlot2 mPayload) 0 =
      slotBitProj (iSlot2 mPayload) 0 * (sel.uTwist c).1)
    (hTwist_s1 : (sel.uTwist c).1 * slotBitProj (iSlot1 mPayload) 1 =
      slotBitProj (iSlot1 mPayload) 1 * (sel.uTwist c).1)
    (hTwist_s0 : (sel.uTwist c).1 * slotBitProj (iSlot0 mPayload) 0 =
      slotBitProj (iSlot0 mPayload) 0 * (sel.uTwist c).1)
    (hPos_slack :
      let P_slack := slotBitProj (iSlot2 mPayload) 0 * slotBitProj (iSlot1 mPayload) 1 *
          slotBitProj (iSlot0 mPayload) 0
      (sel.uPosPhase c).1 * P_slack = P_slack) :
    let P_slack010 :=
      (QRegister.singleton (qCoin2InSingleCat mPayload B_tot kWorkConst)).basisOutcomeProjector 0 *
      (QRegister.singleton (qCoin1InSingleCat mPayload B_tot kWorkConst)).basisOutcomeProjector 1 *
      (QRegister.singleton (qCoin0InSingleCat mPayload B_tot kWorkConst)).basisOutcomeProjector 0
    ((rBEInSingleCat mPayload B_tot kWorkConst).compose (beCoreBlock mPayload)).embedMatrix
      (fullSysSelectEffUnitary qft sel c).1 * P_slack010 = P_slack010 := by
  intro P_slack010
  let rC := (rBEInSingleCat mPayload B_tot kWorkConst).compose (beCoreBlock mPayload)
  have hCore : (fullSysSelectEffUnitary qft sel c).1 * (slotBitProj (iSlot2 mPayload) 0 *
      slotBitProj (iSlot1 mPayload) 1 * slotBitProj (iSlot0 mPayload) 0) = slotBitProj
      (iSlot2 mPayload) 0 * slotBitProj (iSlot1 mPayload) 1 * slotBitProj (iSlot0 mPayload) 0 :=
    (fullSysSelectEffUnitary_on_slackCoin qft sel c 0 hTwist_s2 hTwist_s1 hTwist_s0
      (hPos_slack.trans (one_smul ℂ _).symm)).trans (one_smul ℂ _)
  have hEmb := congrArg rC.embedMatrix hCore
  have hw2 : rC (iSlot2 mPayload) = qCoin2InSingleCat mPayload B_tot kWorkConst :=
    Fin.ext (by simp [rC, rBEInSingleCat, beCoreBlock, iSlot2,
      SpecsAux.SpecMirror.systemQubits,
      SpecsAux.SpecMirror.numElectrons, SpecsAux.SpecMirror.electronBits,
        SpecsAux.SpecMirror.projectileBits])
  have hw1 : rC (iSlot1 mPayload) = qCoin1InSingleCat mPayload B_tot kWorkConst :=
    Fin.ext (by simp [rC, rBEInSingleCat, beCoreBlock, iSlot1,
      SpecsAux.SpecMirror.systemQubits,
      SpecsAux.SpecMirror.numElectrons, SpecsAux.SpecMirror.electronBits,
        SpecsAux.SpecMirror.projectileBits])
  have hw0 : rC (iSlot0 mPayload) = qCoin0InSingleCat mPayload B_tot kWorkConst :=
    Fin.ext (by simp [rC, rBEInSingleCat, beCoreBlock, iSlot0,
      SpecsAux.SpecMirror.systemQubits,
      SpecsAux.SpecMirror.numElectrons, SpecsAux.SpecMirror.electronBits,
        SpecsAux.SpecMirror.projectileBits])
  dsimp only [rC, P_slack010] at hEmb hw2 hw1 hw0 ⊢
  simp only [QRegister.embedMatrix_mul, embed_slotBitProj_eq_singleton_singleCat _ _ hw2 0,
    embed_slotBitProj_eq_singleton_singleCat _ _ hw1 1,
    embed_slotBitProj_eq_singleton_singleCat _ _ hw0 0] at hEmb
  exact hEmb
noncomputable def uCatRawBESingleCat {mPayload B_tot kWorkConst : ℕ}
    {qft : FullSysQft654Bundle} {sel : FullSysSelectOracleBundle mPayload 48}
    (prep : FullSysPrepareBundle mPayload)
    (selImpl : SingleCatSelectImpl mPayload B_tot qft sel) (c : SpecsAux.SpecMirror.Configuration) :
    Unitary (2 ^ (kActSingleCatClosure mPayload B_tot kWorkConst)) :=
    (rBEInSingleCat mPayload B_tot kWorkConst).embedUnitary (prep.uPrep c)⁻¹ *
    ((rBECatSingleCatInAct mPayload B_tot kWorkConst).embedUnitary (selImpl.uSelCat c) *
    (rBEInSingleCat mPayload B_tot kWorkConst).embedUnitary (prep.uPrep c))
noncomputable def uCtrlRawBESingleCat {mPayload B_tot kWorkConst : ℕ}
    {qft : FullSysQft654Bundle} {sel : FullSysSelectOracleBundle mPayload 48}
    (prep : FullSysPrepareBundle mPayload)
    (selImpl : SingleCatSelectImpl mPayload B_tot qft sel) (c : SpecsAux.SpecMirror.Configuration) :
    Unitary (2 ^ (kActSingleCatClosure mPayload B_tot kWorkConst)) :=
    (rBEInSingleCat mPayload B_tot kWorkConst).embedUnitary (prep.uPrep c)⁻¹ *
    ((cSlackUnparkSingleCat mPayload B_tot kWorkConst).eval * ((rBECatSingleCatInAct mPayload
    B_tot kWorkConst).embedUnitary (selImpl.uSelCat c) * ((cSlackParkSingleCat mPayload B_tot
    kWorkConst).eval * (rBEInSingleCat mPayload B_tot kWorkConst).embedUnitary (prep.uPrep
    c))))
theorem intertwinesCat_selectSingleCat_on_catTot {mPayload B_tot kWorkConst : ℕ}
    {qft : FullSysQft654Bundle} {sel : FullSysSelectOracleBundle mPayload 48}
    (selImpl : SingleCatSelectImpl mPayload B_tot qft sel) (c : SpecsAux.SpecMirror.Configuration) :
    IntertwinesCat (uCatNormSingleCat mPayload B_tot kWorkConst).1 ((rCatTotInSingleCat
    mPayload B_tot kWorkConst).basisOutcomeProjector 0) ((rBECatSingleCatInAct mPayload B_tot
    kWorkConst).embedUnitary (selImpl.uSelCat c)).1 (((rBEInSingleCat mPayload B_tot
    kWorkConst).compose (beCoreBlock mPayload)).embedUnitary (fullSysSelectEffUnitary qft sel
    c)).1 := by
  let rBE0 := rBESelLoc mPayload B_tot
  let rCat0 := rCatSelLoc mPayload B_tot
  have hPush := embedMatrix_intertwinesCat (rBECatSingleCatInAct mPayload B_tot kWorkConst)
    (selImpl.hIntertwinesSel c)
  have hCompBE : (rBECatSingleCatInAct mPayload B_tot kWorkConst).compose rBE0 =
      rBEInSingleCat mPayload B_tot kWorkConst :=
    SingleCatClosureAlt.qreg_ext fun i ↦ by
      rw [QRegister.compose_apply,
        show rBE0 i = Fin.castAdd B_tot i from Fin.ext (Nat.zero_add i.val),
        QRegister.concat_apply_left]
  have hCompCat : (rBECatSingleCatInAct mPayload B_tot kWorkConst).compose rCat0 =
      rCatTotInSingleCat mPayload B_tot kWorkConst :=
    SingleCatClosureAlt.qreg_ext fun i ↦ by
      rw [QRegister.compose_apply,
        show rCat0 i = Fin.natAdd (fullSysBEWires mPayload) i from Fin.ext rfl,
        QRegister.concat_apply_right]
  have h1 : (rBECatSingleCatInAct mPayload B_tot kWorkConst).embedMatrix
      (rCat0.embedUnitary (U_cat_B_normalized B_tot)).1 =
      (uCatNormSingleCat mPayload B_tot kWorkConst).1 := by
    unfold uCatNormSingleCat
    rw [QRegister.embedUnitary_val, QRegister.embedUnitary_val, ← QRegister.embedMatrix_compose,
      hCompCat]
  have h2 : (rBECatSingleCatInAct mPayload B_tot kWorkConst).embedMatrix
      (rCat0.basisOutcomeProjector 0) =
      (rCatTotInSingleCat mPayload B_tot kWorkConst).basisOutcomeProjector 0 := by
    rw [QRegister.basisOutcomeProjector, ← QRegister.embedMatrix_compose, hCompCat,
      ← QRegister.basisOutcomeProjector]
  have h0 : (rBECatSingleCatInAct mPayload B_tot kWorkConst).embedMatrix (selImpl.uSelCat c).1 =
      ((rBECatSingleCatInAct mPayload B_tot kWorkConst).embedUnitary (selImpl.uSelCat c)).1 :=
    (QRegister.embedUnitary_val _ _).symm
  have h3 : (rBECatSingleCatInAct mPayload B_tot kWorkConst).embedMatrix (rBE0.embedUnitary
      ((beCoreBlock mPayload).embedUnitary (fullSysSelectEffUnitary qft sel c))).1 =
      (((rBEInSingleCat mPayload B_tot kWorkConst).compose (beCoreBlock
      mPayload)).embedUnitary (fullSysSelectEffUnitary qft sel c)).1 := by
    rw [QRegister.embedUnitary_val, ← QRegister.embedMatrix_compose, hCompBE,
      ← QRegister.embedUnitary_val, QRegister.embedUnitary_compose]
  change IntertwinesCat _ _ _ _ at hPush
  rw [h1, h2, h0, h3] at hPush
  exact hPush
theorem intertwinesCat_lift_catTot_to_scratch {mPayload B_tot kWorkConst : ℕ} {M E : Operator
    (2 ^ (kActSingleCatClosure mPayload B_tot kWorkConst))} (hTot : IntertwinesCat
    (uCatNormSingleCat mPayload B_tot kWorkConst).1 ((rCatTotInSingleCat mPayload B_tot
    kWorkConst).basisOutcomeProjector 0) M E) (hEP : E * pCat0SingleCat mPayload B_tot
    kWorkConst = pCat0SingleCat mPayload B_tot kWorkConst * E) : IntertwinesCat
    (uCatNormSingleCat mPayload B_tot kWorkConst).1 (pCat0SingleCat mPayload B_tot kWorkConst)
    M E := by
  have hAbsorb : (rCatTotInSingleCat mPayload B_tot kWorkConst).basisOutcomeProjector 0 *
      pCat0SingleCat mPayload B_tot kWorkConst = pCat0SingleCat mPayload B_tot kWorkConst :=
    TFreeLaurentGQSP.basisOutcomeProjector_zero_compose_mul
      (rCatScratchInSingleCat mPayload B_tot kWorkConst) (inCatTotSingleCat B_tot kWorkConst)
  refine ⟨?_, hTot.2.1, hEP⟩
  rw [← hAbsorb, ← Matrix.mul_assoc (M * _), hTot.1, Matrix.mul_assoc (_ * E)]
theorem intertwinesCat_catRawBESingleCat {mPayload B_tot kWorkConst : ℕ}
    {qft : FullSysQft654Bundle} {sel : FullSysSelectOracleBundle mPayload 48}
    (prep : FullSysPrepareBundle mPayload)
    (selImpl : SingleCatSelectImpl mPayload B_tot qft sel) (c : SpecsAux.SpecMirror.Configuration) :
    IntertwinesCat (uCatNormSingleCat mPayload B_tot kWorkConst).1
    (pCat0SingleCat mPayload B_tot kWorkConst) (uCatRawBESingleCat prep selImpl c).1
    ((rBEInSingleCat mPayload B_tot kWorkConst).embedUnitary (fullSysRawBEUnitary qft prep
    sel c)).1 := by
  have hDisjBE : ∀ X : Operator (2 ^ (fullSysBEWires mPayload)),
      IntertwinesCat (uCatNormSingleCat mPayload B_tot kWorkConst).1
        ((rCatTotInSingleCat mPayload B_tot kWorkConst).basisOutcomeProjector 0)
        ((rBEInSingleCat mPayload B_tot kWorkConst).embedMatrix X)
        ((rBEInSingleCat mPayload B_tot kWorkConst).embedMatrix X) := fun X ↦
    PhaseGradCatalystCore.intertwinesCat_of_disjoint
      (rBEInSingleCat mPayload B_tot kWorkConst)
      (rCatTotInSingleCat mPayload B_tot kWorkConst)
      (rBEInSingleCat_disj_catTot mPayload B_tot kWorkConst) _ X
  have iSel := intertwinesCat_selectSingleCat_on_catTot (kWorkConst := kWorkConst) selImpl c
  have iProd := intertwinesCat_mul_gen (hDisjBE ((prep.uPrep c)⁻¹).1)
    (intertwinesCat_mul_gen iSel (hDisjBE (prep.uPrep c).1))
  have hEff : ((rBEInSingleCat mPayload B_tot kWorkConst).embedMatrix ((prep.uPrep c)⁻¹).1) *
      ((((rBEInSingleCat mPayload B_tot kWorkConst).compose (beCoreBlock
      mPayload)).embedUnitary (fullSysSelectEffUnitary qft sel c)).1 * ((rBEInSingleCat
      mPayload B_tot kWorkConst).embedMatrix (prep.uPrep c).1)) = ((rBEInSingleCat mPayload
      B_tot kWorkConst).embedUnitary (fullSysRawBEUnitary qft prep sel c)).1 := by
    unfold fullSysRawBEUnitary PosMomSelectDynamic.unitaryConj
    simp only [QRegister.embedUnitary_mul, Submonoid.coe_mul, QRegister.embedUnitary_val,
      QRegister.embedMatrix_compose, Matrix.mul_assoc]
  rw [hEff] at iProd
  refine intertwinesCat_lift_catTot_to_scratch iProd ?_
  rw [QRegister.embedUnitary_val]
  exact (QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint (rBEInSingleCat mPayload B_tot
    kWorkConst))
    (rCatScratchInSingleCat mPayload B_tot kWorkConst)
    (rBEInSingleCat_disj_catScratch mPayload B_tot kWorkConst) _ 0
theorem intertwinesCat_ctrlRawBESingleCat {mPayload B_tot kWorkConst : ℕ}
    {qft : FullSysQft654Bundle}
    {sel : FullSysSelectOracleBundle mPayload 48}
    (prep : FullSysPrepareBundle mPayload)
    (selImpl : SingleCatSelectImpl mPayload B_tot qft sel)
    (c : SpecsAux.SpecMirror.Configuration)
    (hTwist_s2 : (sel.uTwist c).1 * slotBitProj (iSlot2 mPayload) 0 =
      slotBitProj (iSlot2 mPayload) 0 * (sel.uTwist c).1)
    (hTwist_s1 : (sel.uTwist c).1 * slotBitProj (iSlot1 mPayload) 1 =
      slotBitProj (iSlot1 mPayload) 1 * (sel.uTwist c).1)
    (hTwist_s0 : (sel.uTwist c).1 * slotBitProj (iSlot0 mPayload) 0 =
      slotBitProj (iSlot0 mPayload) 0 * (sel.uTwist c).1)
    (hPos_slack :
      let P_slack := slotBitProj (iSlot2 mPayload) 0 * slotBitProj (iSlot1 mPayload) 1 *
          slotBitProj (iSlot0 mPayload) 0
      (sel.uPosPhase c).1 * P_slack = P_slack) :
    let P_sig0 :=
      (QRegister.singleton (qSigInSingleCat mPayload B_tot kWorkConst)).basisOutcomeProjector 0
    let P_sig1 :=
      (QRegister.singleton (qSigInSingleCat mPayload B_tot kWorkConst)).basisOutcomeProjector 1
    let U_raw_emb := ((rBEInSingleCat mPayload B_tot kWorkConst).embedUnitary
        (fullSysRawBEUnitary qft prep sel c)).1
    IntertwinesCat
      (uCatNormSingleCat mPayload B_tot kWorkConst).1
      (pCat0SingleCat mPayload B_tot kWorkConst)
      (uCtrlRawBESingleCat prep selImpl c).1
      (P_sig0 + U_raw_emb * P_sig1) := by
  intro P_sig0 P_sig1 U_raw_emb
  let P_catTot := (rCatTotInSingleCat mPayload B_tot kWorkConst).basisOutcomeProjector 0
  let P_save3 := (rSlackSave3InSingleCat mPayload B_tot kWorkConst).basisOutcomeProjector 0
  let P_prep := (rBEInSingleCat mPayload B_tot kWorkConst).embedMatrix (prep.uPrep c).1
  let P_inv := (rBEInSingleCat mPayload B_tot kWorkConst).embedMatrix ((prep.uPrep c)⁻¹).1
  let E_sel := (((rBEInSingleCat mPayload B_tot kWorkConst).compose
    (beCoreBlock mPayload)).embedUnitary (fullSysSelectEffUnitary qft sel c)).1
  rcases slackParkSingleCat_wires_disj_catTot mPayload B_tot kWorkConst with
    ⟨d0, d1, d2, d3, d4, d5, d6⟩
  have hParkStepsDisj : ∀ s ∈ slackParkStepsSingleCat mPayload B_tot kWorkConst,
      revStepDisjointFromReg (rCatTotInSingleCat mPayload B_tot kWorkConst) s := by
    intro s hs
    simp only [slackParkStepsSingleCat, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [d0, ⟨d0, d1, d4⟩, ⟨d4, d1⟩, d2, ⟨d0, d2, d5⟩, d2, ⟨d5, d2⟩, ⟨d0, d3, d6⟩,
      ⟨d6, d3⟩, d0]
  have hParkComm (X : Operator (2 ^ B_tot)) :
      (cSlackParkSingleCat mPayload B_tot kWorkConst).eval.1 *
        (rCatTotInSingleCat mPayload B_tot kWorkConst).embedMatrix X =
      (rCatTotInSingleCat mPayload B_tot kWorkConst).embedMatrix X *
        (cSlackParkSingleCat mPayload B_tot kWorkConst).eval.1 :=
    compileRevList_comm_embedMatrix _ X _ hParkStepsDisj
  have hUnparkComm (X : Operator (2 ^ B_tot)) :
      (cSlackUnparkSingleCat mPayload B_tot kWorkConst).eval.1 *
        (rCatTotInSingleCat mPayload B_tot kWorkConst).embedMatrix X =
      (rCatTotInSingleCat mPayload B_tot kWorkConst).embedMatrix X *
        (cSlackUnparkSingleCat mPayload B_tot kWorkConst).eval.1 :=
    compileRevList_comm_embedMatrix _ X _ fun s hs ↦ hParkStepsDisj s (List.mem_reverse.mp hs)
  have iOfComm {C : Operator (2 ^ kActSingleCatClosure mPayload B_tot kWorkConst)}
      (hC : ∀ X, C * (rCatTotInSingleCat mPayload B_tot kWorkConst).embedMatrix X =
        (rCatTotInSingleCat mPayload B_tot kWorkConst).embedMatrix X * C) :
      IntertwinesCat (uCatNormSingleCat mPayload B_tot kWorkConst).1 P_catTot C C := by
    refine intertwinesCat_refl_of_comm_gen ?_ (hC (compProj 0))
    unfold uCatNormSingleCat
    rw [QRegister.embedUnitary_val]
    exact hC _
  have hDisjBE (X : Operator (2 ^ (fullSysBEWires mPayload))) :
      IntertwinesCat (uCatNormSingleCat mPayload B_tot kWorkConst).1 P_catTot
        ((rBEInSingleCat mPayload B_tot kWorkConst).embedMatrix X)
        ((rBEInSingleCat mPayload B_tot kWorkConst).embedMatrix X) :=
    PhaseGradCatalystCore.intertwinesCat_of_disjoint
      (rBEInSingleCat mPayload B_tot kWorkConst) (rCatTotInSingleCat mPayload B_tot kWorkConst)
      (rBEInSingleCat_disj_catTot mPayload B_tot kWorkConst) _ X
  have i5 := intertwinesCat_mul_gen (hDisjBE ((prep.uPrep c)⁻¹).1)
    (intertwinesCat_mul_gen (iOfComm hUnparkComm)
      (intertwinesCat_mul_gen
        (intertwinesCat_selectSingleCat_on_catTot (kWorkConst := kWorkConst) selImpl c)
        (intertwinesCat_mul_gen (iOfComm hParkComm) (hDisjBE (prep.uPrep c).1))))
  set E_mid := P_inv * ((cSlackUnparkSingleCat mPayload B_tot kWorkConst).eval.1 *
    (E_sel * ((cSlackParkSingleCat mPayload B_tot kWorkConst).eval.1 * P_prep)))
  have hOnSave3 : E_mid * P_save3 = (P_sig0 + U_raw_emb * P_sig1) * P_save3 := by
    have hBEComm (M : Operator (2 ^ fullSysBEWires mPayload)) (b : Fin 2) :
        (rBEInSingleCat mPayload B_tot kWorkConst).embedMatrix M *
          ((QRegister.singleton (qSigInSingleCat mPayload B_tot kWorkConst)).basisOutcomeProjector
            b * P_save3) =
        ((QRegister.singleton (qSigInSingleCat mPayload B_tot kWorkConst)).basisOutcomeProjector b *
          P_save3) * (rBEInSingleCat mPayload B_tot kWorkConst).embedMatrix M := by
      rw [← Matrix.mul_assoc ((rBEInSingleCat mPayload B_tot kWorkConst).embedMatrix M),
        (QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint (rBEInSingleCat mPayload B_tot
          kWorkConst)) _
          (rBEInSingleCat_disj_qSig mPayload B_tot kWorkConst) M b,
        Matrix.mul_assoc,
        (QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint (rBEInSingleCat mPayload B_tot
          kWorkConst)) _
          ((rBEInSingleCat_disj_catScratch mPayload B_tot kWorkConst).compose_right _) M 0,
        Matrix.mul_assoc]
    have hEselEq : E_sel = (rBEInSingleCat mPayload B_tot kWorkConst).embedMatrix
        ((beCoreBlock mPayload).embedMatrix (fullSysSelectEffUnitary qft sel c).1) := by
      dsimp only [E_sel]
      rw [QRegister.embedUnitary_val, ← QRegister.embedMatrix_compose]
    have hPinvP : P_inv * P_prep = 1 := by
      dsimp only [P_inv, P_prep]
      rw [← (rBEInSingleCat mPayload B_tot kWorkConst).embedMatrix_mul,
        inv_mul_cancel_val_gen (prep.uPrep c),
        (rBEInSingleCat mPayload B_tot kWorkConst).embedMatrix_one]
    have hSelPk : E_sel * ((cSlackParkSingleCat mPayload B_tot kWorkConst).eval.1 *
        (P_sig0 * P_save3)) =
        (cSlackParkSingleCat mPayload B_tot kWorkConst).eval.1 * (P_sig0 * P_save3) := by
      rw [← slack010_mul_cSlackParkSingleCat_sig0_save3 mPayload B_tot kWorkConst,
        ← Matrix.mul_assoc E_sel]
      dsimp only [E_sel]
      rw [QRegister.embedUnitary_val,
        fullSysSelectEff_on_slack010_singleCat qft sel c hTwist_s2 hTwist_s1 hTwist_s0 hPos_slack]
    have hB0 : E_mid * (P_sig0 * P_save3) = P_sig0 * P_save3 := by
      dsimp only [E_mid]
      simp only [Matrix.mul_assoc]
      rw [hBEComm (prep.uPrep c).1 0, ← Matrix.mul_assoc _ _ P_prep,
        ← Matrix.mul_assoc E_sel _ P_prep, hSelPk, ← Matrix.mul_assoc _ _ P_prep,
        ← Matrix.mul_assoc (cSlackUnparkSingleCat mPayload B_tot kWorkConst).eval.1,
        cSlackUnparkSingleCat_mul_cSlackParkSingleCat mPayload B_tot kWorkConst, Matrix.one_mul,
        ← Matrix.mul_assoc P_inv _ P_prep, hBEComm ((prep.uPrep c)⁻¹).1 0,
        Matrix.mul_assoc (P_sig0 * P_save3) P_inv P_prep, hPinvP, Matrix.mul_one]
    have hCommS1 : E_sel * (P_sig1 * P_save3) = (P_sig1 * P_save3) * E_sel :=
      hEselEq ▸ hBEComm _ 1
    have hUrawEq : P_inv * (E_sel * P_prep) = U_raw_emb := by
      dsimp only [P_inv, E_sel, P_prep, U_raw_emb]
      unfold fullSysRawBEUnitary PosMomSelectDynamic.unitaryConj
      simp only [QRegister.embedUnitary_mul, Submonoid.coe_mul, QRegister.embedUnitary_val,
        QRegister.embedMatrix_compose, Matrix.mul_assoc]
    have hB1 : E_mid * (P_sig1 * P_save3) = U_raw_emb * (P_sig1 * P_save3) := by
      dsimp only [E_mid]
      simp only [Matrix.mul_assoc]
      rw [hBEComm (prep.uPrep c).1 1, ← Matrix.mul_assoc _ _ P_prep,
        cSlackParkSingleCat_on_sig1_save3 mPayload B_tot kWorkConst,
        ← Matrix.mul_assoc E_sel _ P_prep, hCommS1,
        Matrix.mul_assoc (P_sig1 * P_save3) E_sel P_prep,
        ← Matrix.mul_assoc (cSlackUnparkSingleCat mPayload B_tot kWorkConst).eval.1
          (P_sig1 * P_save3),
        cSlackUnparkSingleCat_on_sig1_save3 mPayload B_tot kWorkConst,
        ← Matrix.mul_assoc (P_sig1 * P_save3) E_sel P_prep, ← hCommS1,
        Matrix.mul_assoc E_sel (P_sig1 * P_save3) P_prep, ← hBEComm (prep.uPrep c).1 1,
        ← Matrix.mul_assoc E_sel P_prep (P_sig1 * P_save3),
        ← Matrix.mul_assoc P_inv (E_sel * P_prep) (P_sig1 * P_save3), hUrawEq]
    conv_lhs =>
      rw [← Matrix.one_mul P_save3,
        ← singleton_proj_zero_add_one (qSigInSingleCat mPayload B_tot kWorkConst),
        Matrix.add_mul, Matrix.mul_add, hB0, hB1]
    rw [← Matrix.mul_assoc U_raw_emb, ← Matrix.add_mul]
  have hAbsTot : P_catTot * pCat0SingleCat mPayload B_tot kWorkConst = pCat0SingleCat mPayload
      B_tot kWorkConst := TFreeLaurentGQSP.basisOutcomeProjector_zero_compose_mul
      (rCatScratchInSingleCat mPayload B_tot kWorkConst) (inCatTotSingleCat B_tot kWorkConst)
  have hAbsS3 : P_save3 * pCat0SingleCat mPayload B_tot kWorkConst = pCat0SingleCat mPayload
      B_tot kWorkConst := TFreeLaurentGQSP.basisOutcomeProjector_zero_compose_mul
      (rCatScratchInSingleCat mPayload B_tot kWorkConst) (inSlack3SingleCat B_tot kWorkConst)
  have hSigDisjTot : (QRegister.singleton (qSigInSingleCat mPayload B_tot
      kWorkConst)).DisjointWires (rCatTotInSingleCat mPayload B_tot kWorkConst) :=
      (qSigInSingleCat_disj_catScratch mPayload B_tot kWorkConst).compose_right _
  have hEffComm {M : Operator (2 ^ kActSingleCatClosure mPayload B_tot kWorkConst)}
      (h0 : P_sig0 * M = M * P_sig0) (h1 : P_sig1 * M = M * P_sig1)
      (hU : U_raw_emb * M = M * U_raw_emb) :
      (P_sig0 + U_raw_emb * P_sig1) * M = M * (P_sig0 + U_raw_emb * P_sig1) := by
    rw [Matrix.add_mul, Matrix.mul_add, h0, Matrix.mul_assoc, h1, ← Matrix.mul_assoc U_raw_emb,
      hU, Matrix.mul_assoc]
  have hSigU : ∀ b : Fin 2,
      (QRegister.singleton (qSigInSingleCat mPayload B_tot kWorkConst)).basisOutcomeProjector b *
        (uCatNormSingleCat mPayload B_tot kWorkConst).1 =
      (uCatNormSingleCat mPayload B_tot kWorkConst).1 *
        (QRegister.singleton (qSigInSingleCat mPayload B_tot kWorkConst)).basisOutcomeProjector b :=
    fun b ↦ by
      unfold uCatNormSingleCat
      rw [QRegister.embedUnitary_val]
      exact ((QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint (rCatTotInSingleCat
        mPayload B_tot kWorkConst))
        _ hSigDisjTot.symm _ b).symm
  have hEffCommU := hEffComm (hSigU 0) (hSigU 1) (by
    dsimp only [U_raw_emb]
    unfold uCatNormSingleCat
    rw [QRegister.embedUnitary_val, QRegister.embedUnitary_val]
    exact (rBEInSingleCat mPayload B_tot kWorkConst).embedMatrix_comm_of_disjoint
      (rCatTotInSingleCat mPayload B_tot kWorkConst)
      (rBEInSingleCat_disj_catTot mPayload B_tot kWorkConst) _ _)
  have hEffCommP := hEffComm
    (BidirectionalCatalyzedGQSP.basisOutcomeProjector_comm _ _ 0 0)
    (BidirectionalCatalyzedGQSP.basisOutcomeProjector_comm _ _ 1 0)
    ((QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint (rBEInSingleCat mPayload B_tot
      kWorkConst))
      (rCatScratchInSingleCat mPayload B_tot kWorkConst)
      (rBEInSingleCat_disj_catScratch mPayload B_tot kWorkConst) _ 0)
  have hCtrlVal : (uCtrlRawBESingleCat prep selImpl c).1 =
      P_inv * ((cSlackUnparkSingleCat mPayload B_tot kWorkConst).eval.1 *
        (((rBECatSingleCatInAct mPayload B_tot kWorkConst).embedUnitary (selImpl.uSelCat c)).1 *
          ((cSlackParkSingleCat mPayload B_tot kWorkConst).eval.1 * P_prep))) := by
    unfold uCtrlRawBESingleCat
    simp only [Submonoid.coe_mul, QRegister.embedUnitary_val]
    rfl
  refine ⟨?_, hEffCommU, hEffCommP⟩
  conv_lhs =>
    rw [← hAbsTot, ← Matrix.mul_assoc (_ * _) P_catTot, hCtrlVal, i5.1, Matrix.mul_assoc (_ * _),
      hAbsTot, ← hAbsS3, ← Matrix.mul_assoc (_ * E_mid) P_save3,
      Matrix.mul_assoc (uCatNormSingleCat mPayload B_tot kWorkConst).1 E_mid P_save3, hOnSave3,
      ← Matrix.mul_assoc (uCatNormSingleCat mPayload B_tot kWorkConst).1,
      Matrix.mul_assoc (_ * _) P_save3, hAbsS3]
open Classical in
noncomputable def optXSingleCat (mPayload B_tot kWorkConst : ℕ) (b : Bool) :
    Unitary (2 ^ (kActSingleCatClosure mPayload B_tot kWorkConst)) :=
  if b then (Circuit.X (qSigInSingleCat mPayload B_tot kWorkConst)).eval else 1
theorem optXSingleCat_false_mul {mPayload B_tot kWorkConst : ℕ} (M : Operator (2 ^
    (kActSingleCatClosure mPayload B_tot kWorkConst))) :
    (optXSingleCat mPayload B_tot kWorkConst false).1 * M = M := Matrix.one_mul M
theorem optXSingleCat_true_val (mPayload B_tot kWorkConst : ℕ) :
    (optXSingleCat mPayload B_tot kWorkConst true).1 =
      (Circuit.X (qSigInSingleCat mPayload B_tot kWorkConst)).eval.1 := rfl
theorem single_qSig_gate_intertwines_singleCat (mPayload B_tot kWorkConst : ℕ)
    (g : PrimitiveGate 1) : IntertwinesCat (uCatNormSingleCat mPayload B_tot kWorkConst).1
    (pCat0SingleCat mPayload B_tot kWorkConst) (Circuit.single g (qSigInSingleCat mPayload
    B_tot kWorkConst)).eval.1 (Circuit.single g (qSigInSingleCat mPayload B_tot
    kWorkConst)).eval.1 := by
  have hSigDisjTot : (QRegister.singleton (qSigInSingleCat mPayload B_tot
      kWorkConst)).DisjointWires (rCatTotInSingleCat mPayload B_tot kWorkConst) :=
      (qSigInSingleCat_disj_catScratch mPayload B_tot kWorkConst).compose_right _
  refine intertwinesCat_refl_of_comm_gen ?_ ?_
  · rw [Circuit.eval_single, QRegister.embedUnitary_val]
    unfold uCatNormSingleCat
    rw [QRegister.embedUnitary_val]
    exact (QRegister.singleton (qSigInSingleCat mPayload B_tot
      kWorkConst)).embedMatrix_comm_of_disjoint
      (rCatTotInSingleCat mPayload B_tot kWorkConst) hSigDisjTot _ _
  · rw [Circuit.eval_single, QRegister.embedUnitary_val]
    exact (QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint (QRegister.singleton
      (qSigInSingleCat mPayload B_tot kWorkConst)))
      (rCatScratchInSingleCat mPayload B_tot kWorkConst)
      (qSigInSingleCat_disj_catScratch mPayload B_tot kWorkConst) _ 0
theorem intertwinesCat_optXSingleCat (mPayload B_tot kWorkConst : ℕ) (b : Bool) :
    IntertwinesCat (uCatNormSingleCat mPayload B_tot kWorkConst).1
    (pCat0SingleCat mPayload B_tot kWorkConst) (optXSingleCat mPayload B_tot kWorkConst b).1
    (optXSingleCat mPayload B_tot kWorkConst b).1 := by
  cases b
  · exact intertwinesCat_refl_of_comm_gen (by simp [optXSingleCat]) (by simp [optXSingleCat])
  · exact single_qSig_gate_intertwines_singleCat mPayload B_tot kWorkConst PrimitiveGate.X
theorem op_catStep_of_smul_norm {d : ℕ} (z : ℂ) (uSeg uPrep uNorm uEff P : Operator d)
    (hPrep : uPrep = z • uNorm) (hInter : uSeg * uNorm * P = uNorm * uEff * P) : uSeg * uPrep
    * P = uPrep * uEff * P := by
  rw [hPrep, Matrix.mul_smul, Matrix.smul_mul, hInter, Matrix.smul_mul, Matrix.smul_mul]
theorem op_pin_of_comm_and_abs {d : ℕ} (P_cat P_sys P_anc : Operator d)
    (hComm : P_cat * P_sys = P_sys * P_cat) (hAbs : P_cat * P_anc = P_anc) : P_cat *
    (P_sys * P_anc) = P_sys * P_anc := by
  rw [← Matrix.mul_assoc P_cat P_sys P_anc, hComm, Matrix.mul_assoc P_sys P_cat P_anc, hAbs]
theorem op_conj_herm_and_comm {d : ℕ} (U H P : Operator d) (hU : Uᴴ = U) (hH : H.IsHermitian)
    (hUP : U * P = P * U) (hHP : H * P = P * H) : (U * H * Uᴴ).IsHermitian ∧ (U * H * Uᴴ) * P
    = P * (U * H * Uᴴ) := by
  refine ⟨?_, ?_⟩
  · rw [Matrix.IsHermitian, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, hH.eq, Matrix.mul_assoc]
  · rw [hU]
    simp only [Matrix.mul_assoc]
    rw [hUP, ← Matrix.mul_assoc H P U, hHP, Matrix.mul_assoc P H U, ← Matrix.mul_assoc U P (H * U),
      hUP, Matrix.mul_assoc P U (H * U)]
theorem singleCat_pCat0_pin {mPayload B_tot kWorkConst : ℕ}
    (P : Operator (2 ^ SpecsAux.SpecMirror.systemQubits)) :
    let sys : QRegister SpecsAux.SpecMirror.systemQubits
        (SpecsAux.SpecMirror.systemQubits + mActSingleCatClosure mPayload B_tot kWorkConst) :=
      .block 0 SpecsAux.SpecMirror.systemQubits
        (FullSysWalkStepEndpoint.fullSys_zero_add_le SpecsAux.SpecMirror.systemQubits
          (mActSingleCatClosure mPayload B_tot kWorkConst))
    let anc : QRegister (mActSingleCatClosure mPayload B_tot kWorkConst)
        (SpecsAux.SpecMirror.systemQubits + mActSingleCatClosure mPayload B_tot kWorkConst) :=
      .block SpecsAux.SpecMirror.systemQubits (mActSingleCatClosure mPayload B_tot kWorkConst)
        le_rfl
    pCat0SingleCat mPayload B_tot kWorkConst *
      (sys.embedMatrix P * anc.basisOutcomeProjector 0) =
      sys.embedMatrix P * anc.basisOutcomeProjector 0 := by
  intro sys anc
  exact op_pin_of_comm_and_abs _ _ _
    (((QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint sys)
      (rCatScratchInSingleCat mPayload B_tot kWorkConst)
      ((QRegister.block_disjoint_of_le 0 _ _ _ _ le_rfl
        (FullSysCatSegmentBridge.fullSys_zero_add_le_self _)).compose_right
        (inCatScratchSingleCat mPayload B_tot kWorkConst)) P 0).symm)
    (TFreeLaurentGQSP.basisOutcomeProjector_zero_compose_mul anc
      (inCatScratchSingleCat mPayload B_tot kWorkConst))
open scoped Matrix.Norms.L2Operator in
theorem catalyst_sandwich_of_smul_norm {k m : ℕ}
    (A P : Operator (2 ^ k)) (t ε_evol δ_prep : ℝ) (R_j : ℕ) (z : ℂ)
    (V_inv V_prep U_cat U_norm W_seg W_eff : Unitary (2 ^ (k + m)))
    (P_Cat0 : Operator (2 ^ (k + m)))
    (hV_inv : V_inv.1 * V_prep.1 = 1)
    (hAHerm : A.IsHermitian)
    (hPHerm : P.IsHermitian) (hPIdem : P * P = P)
    (hPCatPin :
      let sys : QRegister k (k + m) := .block 0 k (by omega)
      let anc : QRegister m (k + m) := .block k m le_rfl
      P_Cat0 * (sys.embedMatrix P * anc.basisOutcomeProjector 0) =
        sys.embedMatrix P * anc.basisOutcomeProjector 0)
    (hSmul : U_cat.1 = z • U_norm.1)
    (hInter : W_seg.1 * U_norm.1 * P_Cat0 = U_norm.1 * W_eff.1 * P_Cat0)
    (hCommCat : W_eff.1 * P_Cat0 = P_Cat0 * W_eff.1)
    (hPrepErr :
      let anc : QRegister m (k + m) := .block k m le_rfl
      ‖(V_prep.1 - U_cat.1) * anc.basisOutcomeProjector 0‖ ≤ δ_prep)
    (hPow : ApproximatesTimeEvolution A t ε_evol P (W_eff ^ R_j)) :
    ApproximatesTimeEvolution A t (ε_evol + 2 * δ_prep) P
      (unitarySandwichPow V_inv W_seg V_prep R_j) :=
  approximatesTimeEvolution_of_catalyst_sandwich A P t ε_evol δ_prep R_j
    V_inv V_prep U_cat W_seg W_eff P_Cat0 hV_inv hAHerm hPHerm hPIdem hPCatPin
    (op_catStep_of_smul_norm z W_seg.1 U_cat.1 U_norm.1 W_eff.1 P_Cat0 hSmul hInter)
    hCommCat hPrepErr hPow
end SingleCatClosure
end
end ModWeighted3ASingleCatClosure

section ModWeighted3A80CoherentEndpoint
@[expose] public section
namespace CoherentEndpoint
open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt Real
open scoped Matrix BigOperators Matrix.Norms.L2Operator
open SpecsAux.SpecMirror
open SpecsAux.BridgeFermionicComm
open SpecsAux.BridgeFermionicComm.SpecInner
open SpecsAux.FullScaleBESector
open SpecsAux.PhaseGradCatalystCore
open SpecsAux.BridgeDuhamel
open PhaseGradSignalRot hiding IntertwinesCat
open TFreeLaurentGQSP CatalyzedLaurentGQSP
open BidirectionalCatalyzedGQSP
open BidirectionalCatalyzedGQSPBridge
open SpecsAux.SpecMirror.SixChannelHamiltonianSplit
open HoistedSwapSelectBridge hiding unitaryConj unitaryConj_val
section Config80CoherentEndpoint
set_option exponentiation.threshold 256
instance (priority := 1000000) instNeZeroTwoPowCoherent80 (k : ℕ) : NeZero (2 ^ k) :=
  ⟨Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos k)⟩
theorem commute_gridProjector_of_sandwiched
    {A B_sum : Operator (2 ^ SpecsAux.SpecMirror.systemQubits)}
    (hAEq : A = (SpecsAux.gridProjector * B_sum) *
      SpecsAux.gridProjector) :
    Commute A SpecsAux.gridProjector := by
  change A * SpecsAux.gridProjector =
    SpecsAux.gridProjector * A
  rw [hAEq, Matrix.mul_assoc, SpecsAux.gridProjector_mul_self]
  conv_rhs =>
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc,
      SpecsAux.gridProjector_mul_self]
end Config80CoherentEndpoint
set_option maxRecDepth 2000
set_option exponentiation.threshold 256
set_option backward.isDefEq.respectTransparency true
end CoherentEndpoint
end
end ModWeighted3A80CoherentEndpoint

section ModPosPostPrep80MergedVep
@[expose] public section
namespace PosPostPrep80MergedVep
section ConfigPosPostPrep80MergedVep
set_option backward.isDefEq.respectTransparency true
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup
instance (priority := 1000000) instNeZeroTwoPowPosPost80 (k : ℕ) : NeZero (2 ^ k) :=
  ⟨Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos k)⟩
open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt Real
open scoped Matrix BigOperators Matrix.Norms.L2Operator Circuit.Notation
open MeasureBranchHadamardSem (ket)
open ZeroAncillaUSP hiding ket
open Pos24HeadCoordXor80 (bitsVal3_lt8)
theorem itePosLocal {α : Type*} {p : Prop} [Decidable p] (hp : p) (a b : α) :
    (if p then a else b) = a := by split_ifs; rfl
theorem iteNegLocal {α : Type*} {p : Prop} [Decidable p] (hp : ¬ p) (a b : α) :
    (if p then a else b) = b := by split_ifs; rfl
theorem ket_eq_single_local {N : ℕ} (β : BitAssignment N) :
    ket β = (Pi.single ((basisBitsEquiv N).symm β) (1 : ℂ) : Fin (2 ^ N) → ℂ) := by
  funext x
  simp [MeasureBranchHadamardSem.ket]
theorem basisBits_symm_local {N : ℕ} (β : BitAssignment N) : basisBits N
    ((basisBitsEquiv N).symm β) = β := (basisBitsEquiv N).apply_symm_apply β
noncomputable def lockPosPostVal {α : Sort*} (x : α) : α :=
  Classical.choose (⟨x, rfl⟩ : ∃ y : α, y = x)
theorem lockPosPostVal_eq {α : Sort*} (x : α) : lockPosPostVal x = x :=
  Classical.choose_spec (⟨x, rfl⟩ : ∃ y : α, y = x)
theorem wCore3967_lt : 3967 < FullSysCatSegmentBridge.fullSysCoreWires 80 := by
  dsimp [FullSysCatSegmentBridge.fullSysCoreWires, SpecsAux.SpecMirror.systemQubits,
    SpecsAux.SpecMirror.numElectrons, SpecsAux.SpecMirror.electronBits,
      SpecsAux.SpecMirror.projectileBits]
  omega
theorem wCore4029_lt : 4029 < FullSysCatSegmentBridge.fullSysCoreWires 80 := by
  dsimp [FullSysCatSegmentBridge.fullSysCoreWires, SpecsAux.SpecMirror.systemQubits,
    SpecsAux.SpecMirror.numElectrons, SpecsAux.SpecMirror.electronBits,
      SpecsAux.SpecMirror.projectileBits]
  omega
def wCore3967 : Wire (FullSysCatSegmentBridge.fullSysCoreWires 80) := ⟨3967, wCore3967_lt⟩
def wCore4029 : Wire (FullSysCatSegmentBridge.fullSysCoreWires 80) := ⟨4029, wCore4029_lt⟩
theorem wCore3967_ne_4029 : wCore3967 ≠ wCore4029 := by
  intro h
  have hv := congrArg Fin.val h
  dsimp [wCore3967, wCore4029] at hv
  omega
def swapCore3967Fn (β : BitAssignment (FullSysCatSegmentBridge.fullSysCoreWires 80)) :
    BitAssignment (FullSysCatSegmentBridge.fullSysCoreWires 80) :=
  fun q ↦ β (Equiv.swap wCore3967 wCore4029 q)
@[simp] theorem swapCore3967Fn_involutive
    (β : BitAssignment (FullSysCatSegmentBridge.fullSysCoreWires 80)) :
    swapCore3967Fn (swapCore3967Fn β) = β := by
  funext q
  simp [swapCore3967Fn]
def cSwap2 {n : ℕ} (a b : Wire n) (hne : a ≠ b) : Circuit n := .seq (Circuit.CNOT a b hne)
    (.seq (Circuit.CNOT b a hne.symm) (Circuit.CNOT a b hne))
def cSwapCore3967 : Circuit (FullSysCatSegmentBridge.fullSysCoreWires 80) :=
  cSwap2 wCore3967 wCore4029 wCore3967_ne_4029
theorem zmod2_swap_a (x y : ZMod 2) : x + (y + x) = y := by decide +revert
theorem zmod2_swap_b (x y : ZMod 2) : y + x + (x + (y + x)) = x := by decide +revert
noncomputable def uSwapCore3967 : Unitary (2 ^ (FullSysCatSegmentBridge.fullSysCoreWires 80)) :=
  lockPosPostVal cSwapCore3967.eval
theorem uSwapCore3967_mulVec_ket
    (β : BitAssignment (FullSysCatSegmentBridge.fullSysCoreWires 80)) :
    uSwapCore3967.1.mulVec (ket β) = ket (swapCore3967Fn β) := by
  rw [uSwapCore3967, lockPosPostVal_eq]
  unfold cSwapCore3967 cSwap2
  rw [MeasureBranchHadamardSem.eval_seq_mulVec, MeasureBranchHadamardSem.ket_CNOT,
    MeasureBranchHadamardSem.eval_seq_mulVec, MeasureBranchHadamardSem.ket_CNOT,
    MeasureBranchHadamardSem.ket_CNOT]
  congr 1
  funext q
  unfold swapCore3967Fn
  by_cases h1 : q = wCore3967
  · subst h1
    simp [wCore3967_ne_4029, wCore3967_ne_4029.symm, zmod2_swap_a]
  · by_cases h2 : q = wCore4029
    · subst h2
      simp [wCore3967_ne_4029, wCore3967_ne_4029.symm, zmod2_swap_b]
    · simp [h1, h2, Equiv.swap_apply_of_ne_of_ne h1 h2]
@[simp] theorem uSwapCore3967_mul_self : uSwapCore3967 * uSwapCore3967 = 1 := by
  apply Subtype.ext
  apply MeasureBranchHadamardSem.matrix_ext_ket
  intro β
  rw [Submonoid.coe_mul, OneMemClass.coe_one, Matrix.one_mulVec, ← Matrix.mulVec_mulVec,
    uSwapCore3967_mulVec_ket, uSwapCore3967_mulVec_ket, swapCore3967Fn_involutive]
theorem unitary_conjTranspose_of_mul_self {K : ℕ} (U : Unitary K) (h : U * U = 1) :
    U.1ᴴ = U.1 := by
  have hmul : U.1 * U.1 = 1 := by
    simpa only [Submonoid.coe_mul, OneMemClass.coe_one] using congrArg Subtype.val h
  rw [← Matrix.mul_one U.1ᴴ, ← hmul, ← Matrix.mul_assoc,
    (show U.1ᴴ * U.1 = 1 from Unitary.coe_star_mul_self U), Matrix.one_mul]
@[simp] theorem uSwapCore3967_conjTranspose : uSwapCore3967.1ᴴ = uSwapCore3967.1 :=
  unitary_conjTranspose_of_mul_self uSwapCore3967 uSwapCore3967_mul_self
noncomputable def conjSwapCore3967
    (U : Unitary (2 ^ (FullSysCatSegmentBridge.fullSysCoreWires 80))) : Unitary
    (2 ^ (FullSysCatSegmentBridge.fullSysCoreWires 80)) := uSwapCore3967 * U * uSwapCore3967
theorem perm_comm_diagonal_of_ket {n : ℕ} (S : Operator (2 ^ n))
    (perm : BitAssignment n → BitAssignment n) (hS : ∀ β, S.mulVec (ket β) = ket (perm β))
    (d : Fin (2 ^ n) → ℂ) (hd : ∀ β, d ((basisBitsEquiv n).symm (perm β)) = d ((basisBitsEquiv
    n).symm β)) : S * Matrix.diagonal d = Matrix.diagonal d * S := by
  refine MeasureBranchHadamardSem.matrix_ext_ket fun β ↦ ?_
  have hdiag : ∀ γ : BitAssignment n,
      (Matrix.diagonal d).mulVec (ket γ) = d ((basisBitsEquiv n).symm γ) • ket γ := fun γ ↦ by
    rw [ket_eq_single_local γ, Matrix.diagonal_mulVec_single]
    funext y; simp [Pi.single_apply]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hdiag β, Matrix.mulVec_smul,
    hS β, hdiag (perm β), hd β]
theorem op_comm_mul3 {K : ℕ} (S A B C : Matrix (Fin K) (Fin K) ℂ) (hA : S * A = A * S)
    (hB : S * B = B * S) (hC : S * C = C * S) : S * (A * B * C) = (A * B * C) * S := by
  rw [← Matrix.mul_assoc S (A * B) C, ← Matrix.mul_assoc S A B, hA, Matrix.mul_assoc A S B, hB,
    ← Matrix.mul_assoc A B S, Matrix.mul_assoc (A * B) S C, hC, ← Matrix.mul_assoc (A * B) C S]
theorem unitary_conj_mul_eq {K : ℕ} (S U : Unitary K) (P : Matrix (Fin K) (Fin K) ℂ)
    (hS2 : S * S = 1) (hComm : S.1 * P = P * S.1) (hUP : U.1 * P = P) :
    (S * U * S).1 * P = P := by
  rw [Submonoid.coe_mul, Submonoid.coe_mul, Matrix.mul_assoc (S.1 * U.1) S.1 P, hComm,
    Matrix.mul_assoc S.1 U.1 (P * S.1), ← Matrix.mul_assoc U.1 P S.1, hUP,
    ← Matrix.mul_assoc S.1 P S.1, hComm, Matrix.mul_assoc P S.1 S.1, ← Submonoid.coe_mul, hS2,
    OneMemClass.coe_one, Matrix.mul_one]
theorem unitary_conj_mul_neg_eq {K : ℕ} (S U : Unitary K) (P : Matrix (Fin K) (Fin K) ℂ)
    (hS2 : S * S = 1) (hComm : S.1 * P = P * S.1) (hUP : U.1 * P = -P) :
    (S * U * S).1 * P = -P := by
  rw [Submonoid.coe_mul, Submonoid.coe_mul, Matrix.mul_assoc (S.1 * U.1) S.1 P, hComm,
    Matrix.mul_assoc S.1 U.1 (P * S.1), ← Matrix.mul_assoc U.1 P S.1, hUP, Matrix.neg_mul,
    Matrix.mul_neg, ← Matrix.mul_assoc S.1 P S.1, hComm, Matrix.mul_assoc P S.1 S.1,
    ← Submonoid.coe_mul, hS2, OneMemClass.coe_one, Matrix.mul_one]
theorem uSwapCore3967_comm_slotBitProj
    (w : Wire (FullSysCatSegmentBridge.fullSysCoreWires 80)) (b : Fin 2)
    (h1 : w ≠ wCore3967) (h2 : w ≠ wCore4029) :
    uSwapCore3967.1 * PosMomSelectSandwich.slotBitProj w b =
      PosMomSelectSandwich.slotBitProj w b * uSwapCore3967.1 := by
  unfold PosMomSelectSandwich.slotBitProj
  refine perm_comm_diagonal_of_ket uSwapCore3967.1 swapCore3967Fn uSwapCore3967_mulVec_ket _
    fun β ↦ ?_
  have hsw : swapCore3967Fn β w = β w := congrArg β (Equiv.swap_apply_of_ne_of_ne h1 h2)
  rw [basisBits_symm_local, basisBits_symm_local, hsw]
private theorem uSwapCore3967_comm_of_val_ne
    (w : Wire (FullSysCatSegmentBridge.fullSysCoreWires 80)) (b : Fin 2)
    (h1 : w.val ≠ 3967) (h2 : w.val ≠ 4029) :
    uSwapCore3967.1 * PosMomSelectSandwich.slotBitProj w b =
      PosMomSelectSandwich.slotBitProj w b * uSwapCore3967.1 :=
  uSwapCore3967_comm_slotBitProj w b (fun h ↦ h1 (congrArg Fin.val h))
    (fun h ↦ h2 (congrArg Fin.val h))
theorem conjSwapCore3967_on_P1
    (U : Unitary (2 ^ (FullSysCatSegmentBridge.fullSysCoreWires 80)))
    (hP1 : U.1 * PosMomSelectSandwich.slotBitProj (FullSysCatSegmentBridge.iSlot2 80) 1 =
      PosMomSelectSandwich.slotBitProj (FullSysCatSegmentBridge.iSlot2 80) 1) :
    (conjSwapCore3967 U).1 *
      PosMomSelectSandwich.slotBitProj (FullSysCatSegmentBridge.iSlot2 80) 1 =
    PosMomSelectSandwich.slotBitProj (FullSysCatSegmentBridge.iSlot2 80) 1 :=
  unitary_conj_mul_eq uSwapCore3967 U _ uSwapCore3967_mul_self
    (uSwapCore3967_comm_of_val_ne _ 1 (by decide) (by decide)) hP1
theorem conjSwapCore3967_slack2
    (U : Unitary (2 ^ FullSysCatSegmentBridge.fullSysCoreWires 80))
    (hSlack2 : OraAndPrepBundle.posSlack2Prop U) :
    OraAndPrepBundle.posSlack2Prop (conjSwapCore3967 U) :=
  unitary_conj_mul_eq uSwapCore3967 U _ uSwapCore3967_mul_self
    (op_comm_mul3 _ _ _ _
      (uSwapCore3967_comm_of_val_ne _ 0 (by decide) (by decide))
      (uSwapCore3967_comm_of_val_ne _ 1 (by decide) (by decide))
      (uSwapCore3967_comm_of_val_ne _ 0 (by decide) (by decide))) hSlack2
theorem conjSwapCore3967_slack3
    (U : Unitary (2 ^ FullSysCatSegmentBridge.fullSysCoreWires 80))
    (hSlack3 : OraAndPrepBundle.posSlack3Prop U) :
    OraAndPrepBundle.posSlack3Prop (conjSwapCore3967 U) :=
  unitary_conj_mul_neg_eq uSwapCore3967 U _ uSwapCore3967_mul_self
    (op_comm_mul3 _ _ _ _
      (uSwapCore3967_comm_of_val_ne _ 0 (by decide) (by decide))
      (uSwapCore3967_comm_of_val_ne _ 1 (by decide) (by decide))
      (uSwapCore3967_comm_of_val_ne _ 1 (by decide) (by decide))) hSlack3
def cHalfH {n : ℕ} (q : Wire n) : Circuit n :=
  .seq (Circuit.S q) (.seq (Circuit.H q) (Circuit.T q))
def chCircuit {n : ℕ} (ctrl targ : Wire n) (hne : ctrl ≠ targ) : Circuit n :=
  .seq (cHalfH targ) (.seq (Circuit.CNOT ctrl targ hne) (cHalfH targ).inverse)
@[simp] theorem chCircuit_count_toff {n : ℕ} (ctrl targ : Wire n) (hne : ctrl ≠ targ) :
    (chCircuit ctrl targ hne).count PrimitiveGate.TOFF = 0 := by
  simp [chCircuit, cHalfH, Circuit.inverse, inverseGate]
@[simp] theorem chCircuit_count_t {n : ℕ} (ctrl targ : Wire n) (hne : ctrl ≠ targ) :
    (chCircuit ctrl targ hne).count PrimitiveGate.T = 2 := by
  simp [chCircuit, cHalfH, Circuit.inverse, inverseGate]
theorem halfH_conj_x_mul_h : (PrimitiveGate.eval .s)⁻¹ * (PrimitiveGate.eval .h)⁻¹ *
    (PrimitiveGate.eval .t)⁻¹ * PrimitiveGate.eval .x * PrimitiveGate.eval .t *
    PrimitiveGate.eval .h * PrimitiveGate.eval .s * PrimitiveGate.eval .h = (1 : Unitary 2)
    := by
  apply Subtype.ext
  have hsq2 : ((√(2 : ℝ) : ℂ) ^ 2) = 2 := by
    norm_cast
    exact Real.sq_sqrt (by norm_num)
  have hsq4 : ((√(2 : ℝ) : ℂ) ^ 4) = 4 := by
    have h4 : (4 : ℕ) = 2 * 2 := rfl
    rw [h4, pow_mul, hsq2]
    norm_num
  have h2nz : (√(2 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast Real.sqrt_ne_zero'.mpr (by norm_num)
  ext i j
  change (((PrimitiveGate.eval .s).1ᴴ * (PrimitiveGate.eval .h).1ᴴ * (PrimitiveGate.eval .t).1ᴴ *
      (PrimitiveGate.eval .x).1 *
      (PrimitiveGate.eval .t).1 * (PrimitiveGate.eval .h).1 * (PrimitiveGate.eval .s).1 *
      (PrimitiveGate.eval .h).1) i j) = (1 : Matrix (Fin 2) (Fin 2) ℂ) i j
  rw [PrimitiveGate.eval_s_val, PrimitiveGate.eval_t_val]
  fin_cases i <;> fin_cases j <;>
    simp [PrimitiveGate.eval, Qubit.H, Qubit.X, Matrix.mul_apply, Fin.sum_univ_two]
  · field_simp [h2nz]; ring_nf; rw [hsq4]; norm_num [Complex.I_sq]
  · field_simp [h2nz]; ring_nf; rw [Complex.I_sq]; ring
  · field_simp [h2nz]; ring
  · field_simp [h2nz]; ring_nf; rw [hsq4]; norm_num [Complex.I_sq]
theorem eval_h_mul_h : PrimitiveGate.eval .h * PrimitiveGate.eval .h = (1 : Unitary 2) := by
  apply Subtype.ext
  ext i j
  change (((PrimitiveGate.eval .h).1 * (PrimitiveGate.eval .h).1) i j) =
    (1 : Matrix (Fin 2) (Fin 2) ℂ) i j
  rw [Matrix.one_apply]
  fin_cases i <;> fin_cases j <;>
    simp [PrimitiveGate.eval, Qubit.H, Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num
theorem halfH_conj_x_eq_h : (PrimitiveGate.eval .s)⁻¹ * (PrimitiveGate.eval .h)⁻¹ *
    (PrimitiveGate.eval .t)⁻¹ * PrimitiveGate.eval .x * PrimitiveGate.eval .t *
    PrimitiveGate.eval .h * PrimitiveGate.eval .s = PrimitiveGate.eval .h := by
  have hmul := congrArg (· * PrimitiveGate.eval .h) halfH_conj_x_mul_h
  rw [mul_assoc _ (PrimitiveGate.eval .h) (PrimitiveGate.eval .h), eval_h_mul_h,
    mul_one, one_mul] at hmul
  exact hmul
theorem cHalfH_eval_eq_singleton {n : ℕ} (q : Wire n) : (cHalfH q).eval =
    (QRegister.singleton q).embedUnitary (PrimitiveGate.eval .t * PrimitiveGate.eval .h *
    PrimitiveGate.eval .s) := by
  change (Circuit.single .t q).eval * (Circuit.single .h q).eval * (Circuit.single .s q).eval = _
  rw [Circuit.eval_single, Circuit.eval_single, Circuit.eval_single,
    ← QRegister.embedUnitary_mul, ← QRegister.embedUnitary_mul]
theorem cHalfH_inv_eval_eq_singleton {n : ℕ} (q : Wire n) : (cHalfH q).inverse.eval =
    (QRegister.singleton q).embedUnitary ((PrimitiveGate.eval .s)⁻¹ * (PrimitiveGate.eval
    .h)⁻¹ * (PrimitiveGate.eval .t)⁻¹) := by
  rw [Circuit.eval_inverse, cHalfH_eval_eq_singleton]
  refine mul_eq_one_iff_inv_eq.mp ?_
  rw [← (QRegister.singleton q).embedUnitary_mul, show (PrimitiveGate.eval .t *
    PrimitiveGate.eval .h * PrimitiveGate.eval .s) * ((PrimitiveGate.eval .s)⁻¹ *
    (PrimitiveGate.eval .h)⁻¹ * (PrimitiveGate.eval .t)⁻¹) = 1 by group,
    QRegister.embedUnitary_one]
private theorem cHalfH_comm_singleton_proj {n : ℕ} (ctrl targ : Wire n) (hne : ctrl ≠ targ)
    (b : Fin (2 ^ 1)) : (cHalfH targ).eval.1 * (QRegister.singleton ctrl).basisOutcomeProjector b =
      (QRegister.singleton ctrl).basisOutcomeProjector b * (cHalfH targ).eval.1 := by
  rw [cHalfH_eval_eq_singleton]
  exact QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint _ _
    (QRegister.disjoint_iff.mpr fun _ _ h ↦ hne h.symm) _ b
theorem chCircuit_mulVec_ket_ctrl_zero {n : ℕ} (ctrl targ : Wire n) (hne : ctrl ≠ targ)
    (β : BitAssignment n) (hc : β ctrl = 0) :
    (chCircuit ctrl targ hne).eval.1.mulVec (ket β) = ket β := by
  let P₀ := (QRegister.singleton ctrl).basisOutcomeProjector 0
  have hcomm := cHalfH_comm_singleton_proj ctrl targ hne 0
  have hcnot_P₀ : (Circuit.CNOT ctrl targ hne).eval.1 * P₀ = P₀ := by
    apply MeasureBranchHadamardSem.matrix_ext_ket
    intro γ
    rw [← Matrix.mulVec_mulVec, show ket γ = MeasureBranchHadamardSem.ket γ from rfl,
      MeasureBranchHadamardSem.ket_projector_zero]
    by_cases hγ : γ ctrl = 0
    · rw [itePosLocal hγ, MeasureBranchHadamardSem.ket_CNOT, hγ, add_zero, Function.update_eq_self]
    · rw [iteNegLocal hγ, Matrix.mulVec_zero]
  have hP₀_β : P₀.mulVec (ket β) = ket β := by
    rw [show ket β = MeasureBranchHadamardSem.ket β from rfl,
      MeasureBranchHadamardSem.ket_projector_zero, itePosLocal hc]
  have hMat : (((cHalfH targ).inverse.eval.1 * (Circuit.CNOT ctrl targ hne).eval.1) *
      (cHalfH targ).eval.1) * P₀ = P₀ := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, hcomm, ← Matrix.mul_assoc (Circuit.CNOT _ _ _).eval.1,
      hcnot_P₀, ← hcomm, ← Matrix.mul_assoc, ← Submonoid.coe_mul, Circuit.eval_inverse,
      inv_mul_cancel, OneMemClass.coe_one, Matrix.one_mul]
  rw [← hP₀_β, Matrix.mulVec_mulVec]
  exact congrArg (fun M ↦ M.mulVec (ket β)) hMat
private theorem singleton_proj_one_ket {n : ℕ} (ctrl : Wire n) (γ : BitAssignment n) :
    ((QRegister.singleton ctrl).basisOutcomeProjector 1).mulVec (ket γ) =
      if γ ctrl = 1 then ket γ else 0 := by
  have hb11 : basisBits 1 1 0 = 1 := by decide
  rw [QRegister.basisOutcomeProjector_eq_diagonal, ket_eq_single_local γ,
    Matrix.diagonal_mulVec_single]
  by_cases hγ : γ ctrl = 1
  · have hex : (QRegister.singleton ctrl).extractIndex ((basisBitsEquiv n).symm γ) = 1 :=
      (basisBitsEquiv 1).injective (funext fun i ↦ by
        rcases Subsingleton.elim i 0 with rfl
        change basisBits 1 ((QRegister.singleton ctrl).extractIndex _) 0 = basisBits 1 1 0
        rw [QRegister.basisBits_extractIndex, basisBits_symm_local, hb11]
        exact hγ)
    rw [itePosLocal hex, itePosLocal hγ, mul_one, ← ket_eq_single_local γ]
  · have hex : (QRegister.singleton ctrl).extractIndex ((basisBitsEquiv n).symm γ) ≠ 1 := fun h1 ↦
      hγ (by
        have hb := congrFun (congrArg (basisBits 1) h1) 0
        rwa [QRegister.basisBits_extractIndex, basisBits_symm_local, hb11] at hb)
    rw [iteNegLocal hex, iteNegLocal hγ, zero_mul, Pi.single_zero]
theorem cnot_eq_x_on_ctrl_one {n : ℕ} (ctrl targ : Wire n) (hne : ctrl ≠ targ) :
    let P₁ : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ :=
      (QRegister.singleton ctrl).basisOutcomeProjector 1
    (Circuit.CNOT ctrl targ hne).eval.1 * P₁ = (Circuit.X targ).eval.1 * P₁ := by
  intro P₁
  apply MeasureBranchHadamardSem.matrix_ext_ket
  intro γ
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  change (Circuit.CNOT ctrl targ hne).eval.1.mulVec (P₁.mulVec (ket γ)) =
    (Circuit.X targ).eval.1.mulVec (P₁.mulVec (ket γ))
  rw [show P₁ = (QRegister.singleton ctrl).basisOutcomeProjector 1 from rfl,
    singleton_proj_one_ket ctrl γ]
  by_cases hγ : γ ctrl = 1
  · rw [itePosLocal hγ]
    rw [MeasureBranchHadamardSem.ket_CNOT, MeasureBranchHadamardSem.ket_X, hγ]
  · rw [iteNegLocal hγ, Matrix.mulVec_zero, Matrix.mulVec_zero]
theorem chCircuit_mulVec_ket_ctrl_one {n : ℕ} (ctrl targ : Wire n) (hne : ctrl ≠ targ)
    (β : BitAssignment n) (hc1 : β ctrl = 1) : (chCircuit ctrl targ hne).eval.1.mulVec (ket β)
    = (Circuit.H targ).eval.1.mulVec (ket β) := by
  let P₁ := (QRegister.singleton ctrl).basisOutcomeProjector 1
  have hcommW := cHalfH_comm_singleton_proj ctrl targ hne 1
  have hEqH : (cHalfH targ).inverse.eval * (Circuit.X targ).eval * (cHalfH targ).eval =
      (Circuit.H targ).eval := by
    rw [cHalfH_inv_eval_eq_singleton, cHalfH_eval_eq_singleton, Circuit.eval_single,
      Circuit.eval_single, ← QRegister.embedUnitary_mul, ← QRegister.embedUnitary_mul]
    congr 1
    rw [← mul_assoc, ← mul_assoc, halfH_conj_x_eq_h]
  have hP₁_β : P₁.mulVec (ket β) = ket β := by
    rw [show P₁ = (QRegister.singleton ctrl).basisOutcomeProjector 1 from rfl,
      singleton_proj_one_ket ctrl β, itePosLocal hc1]
  have hMat : (chCircuit ctrl targ hne).eval.1 * P₁ = (Circuit.H targ).eval.1 * P₁ := by
    change (((cHalfH targ).inverse.eval.1 * (Circuit.CNOT ctrl targ hne).eval.1) *
      (cHalfH targ).eval.1) * P₁ = _
    rw [Matrix.mul_assoc, Matrix.mul_assoc, hcommW, ← Matrix.mul_assoc (Circuit.CNOT _ _ _).eval.1,
      cnot_eq_x_on_ctrl_one ctrl targ hne,
      show (QRegister.singleton ctrl).basisOutcomeProjector 1 = P₁ from rfl,
      Matrix.mul_assoc (Circuit.X targ).eval.1 P₁, ← hcommW,
      ← Matrix.mul_assoc (Circuit.X targ).eval.1,
      ← Matrix.mul_assoc (cHalfH targ).inverse.eval.1,
      ← Matrix.mul_assoc (cHalfH targ).inverse.eval.1 (Circuit.X targ).eval.1,
      ← Submonoid.coe_mul, ← Submonoid.coe_mul, hEqH]
  rw [← hP₁_β, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hMat]
@[simp] theorem circuit_inverse_count_T {n : ℕ} (c : Circuit n) :
    c.inverse.count PrimitiveGate.T = c.count PrimitiveGate.T := by
  induction c with
  | identity => rfl
  | gate g r =>
    cases g <;>
      simp only [Circuit.inverse_gate, Circuit.inverseGate, Circuit.sequence,
        Circuit.count_seq, Circuit.count_gate, Circuit.count_identity, Nat.add_comm] <;>
      rfl
  | seq c₁ c₂ ih₁ ih₂ => simp only [Circuit.inverse_seq, Circuit.count_seq, ih₁, ih₂, Nat.add_comm]
@[simp] theorem circuit_inverse_count_TOFF {n : ℕ} (c : Circuit n) :
    c.inverse.count PrimitiveGate.TOFF = c.count PrimitiveGate.TOFF := by
  induction c with
  | identity => rfl
  | gate g r =>
    cases g <;>
      simp only [Circuit.inverse_gate, Circuit.inverseGate, Circuit.sequence,
        Circuit.count_seq, Circuit.count_gate, Circuit.count_identity] <;>
      rfl
  | seq c₁ c₂ ih₁ ih₂ => simp only [Circuit.inverse_seq, Circuit.count_seq, ih₁, ih₂, Nat.add_comm]
def chIf {n : ℕ} (ctrl targ : Wire n) : Circuit n :=
  if hne : ctrl = targ then Circuit.identity else chCircuit ctrl targ hne
@[simp] theorem count_toff_chIf {n : ℕ} (ctrl targ : Wire n) :
    (chIf ctrl targ).count PrimitiveGate.TOFF = 0 := by
  unfold chIf; split_ifs <;> simp
def unHadamardList {n : ℕ} (ctrl : Wire n) : List (Wire n) → Circuit n
  | [] => Circuit.identity
  | q :: qs => unHadamardList ctrl qs ;;ᶜ chIf ctrl q
@[simp] theorem count_toff_unHadamardList {n : ℕ} (ctrl : Wire n) (qs : List (Wire n)) :
    (unHadamardList ctrl qs).count PrimitiveGate.TOFF = 0 := by
  induction qs with
  | nil => rfl
  | cons q qs ih => simp [unHadamardList, ih]
set_option maxRecDepth 2000000
set_option exponentiation.threshold 256
def z2BitOfNat (x i : ℕ) : ZMod 2 := if ((x / 2 ^ i) % 2) == 1 then 1 else 0
def headWitnessPayload80 (b0Val nuc anc : ℕ) (k : Fin 56) (pid : Fin 6) (sm : Fin 8)
    (thresh rej0 : Bool) : BitAssignment 80 :=
  let dH := PosSlots24SemanticBridge.pos24OhPoint (PosSlots24SemanticBridge.pos24HeadU56 k)
      (PosSlots24SemanticBridge.pos24HeadV56 k) (PosSlots24SemanticBridge.pos24HeadW56 k) pid
      sm
  let dpH := ((dH 0).val % 2) + 2 * ((dH 1).val % 2) + 4 * ((dH 2).val % 2)
  let fineH := (dH 0).val + 128 * (dH 1).val + 16384 * (dH 2).val
  let b1Val := Nat.xor b0Val dpH
  fun q ↦
    let i := q.val
    if i < 3 then z2BitOfNat b1Val i
    else if i < 6 then z2BitOfNat b0Val (i - 3)
    else if i < 14 then z2BitOfNat nuc (i - 6)
    else if i < 22 then z2BitOfNat anc (i - 14)
    else if i < 30 then 0
    else if i == 30 then 1
    else if i == 31 then (if thresh then 1 else 0)
    else if i < 62 then z2BitOfNat fineH (i - 32)
    else if i == 62 then 0
    else if i < 69 then z2BitOfNat k.val (i - 63)
    else if i < 72 then z2BitOfNat pid.val (i - 69)
    else if i < 75 then z2BitOfNat sm.val (i - 72)
    else if i < 79 then 0
    else (if rej0 then 1 else 0)
def tailWitnessPayload80 (b0Val nuc anc part : ℕ) (dp : Fin 8) (keep : ℕ)
    (thresh rej0 : Bool) : BitAssignment 80 :=
  let b1Val := Nat.xor b0Val dp.val
  fun q ↦
    let i := q.val
    if i < 3 then z2BitOfNat b1Val i
    else if i < 6 then z2BitOfNat b0Val (i - 3)
    else if i < 14 then z2BitOfNat nuc (i - 6)
    else if i < 22 then z2BitOfNat anc (i - 14)
    else if i < 30 then z2BitOfNat part (i - 22)
    else if i == 30 then 0
    else if i == 31 then (if thresh then 1 else 0)
    else if i < 62 then z2BitOfNat keep (i - 32)
    else if i == 62 then 0
    else if i < 75 then 0
    else if i < 78 then z2BitOfNat dp.val (i - 75)
    else if i == 78 then 0
    else (if rej0 then 1 else 0)
def pos80SubIdx (off m : ℕ) (h : off + m ≤ 80) (j : Fin m) : Fin 80 :=
  ⟨off + j.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left j.isLt off) h⟩
open Classical in
noncomputable def pos80IdealDist (s0 : Bool) (p80 : BitAssignment 80) : ℝ :=
  let _b1Val := Pos24HeadCoordXor80.bitsVal (fun j : Fin 3 ↦ p80 ⟨j.val, Nat.lt_trans j.isLt (by
    decide)⟩)
  let b0Val := Pos24HeadCoordXor80.bitsVal (fun j : Fin 3 ↦ p80 (pos80SubIdx 3 3 (by decide) j))
  let nuc := Pos24HeadCoordXor80.bitsVal (fun j : Fin 8 ↦ p80 (pos80SubIdx 6 8 (by decide) j))
  let anc := Pos24HeadCoordXor80.bitsVal (fun j : Fin 8 ↦ p80 (pos80SubIdx 14 8 (by decide) j))
  let part := Pos24HeadCoordXor80.bitsVal (fun j : Fin 8 ↦ p80 (pos80SubIdx 22 8 (by decide) j))
  let fine30 := Pos24HeadCoordXor80.bitsVal (fun j : Fin 30 ↦ p80 (pos80SubIdx 32 30 (by decide) j))
  if p80 62 != 0 then 0
  else if p80 30 == 1 then
    let kVal := Pos24HeadCoordXor80.bitsVal (fun j : Fin 6 ↦ p80 (pos80SubIdx 63 6 (by decide) j))
    let pidVal := Pos24HeadCoordXor80.bitsVal (fun j : Fin 3 ↦ p80 (pos80SubIdx 69 3 (by decide) j))
    let smVal := Pos24HeadCoordXor80.bitsVal (fun j : Fin 3 ↦ p80 (pos80SubIdx 72 3 (by decide) j))
    let remZero := (p80 75 == 0) && (p80 76 == 0) && (p80 77 == 0) && (p80 78 == 0)
    let metaOk := if s0 then (nuc == 0) && decide (anc < 218)
      else decide (b0Val == 0) && decide (nuc < 216) && (anc == 0)
    if hk : kVal < 56 then
      if hp : pidVal < 6 then
        let k : Fin 56 := ⟨kVal, hk⟩
        let pid : Fin 6 := ⟨pidVal, hp⟩
        let sm : Fin 8 := ⟨smVal, Pos24HeadCoordXor80.bitsVal3_lt8 _⟩
        if remZero && metaOk && (part == 0) &&
            (p80 == headWitnessPayload80 b0Val nuc anc k pid sm (p80 31 == 1) (p80 79 == 1)) then
          if s0 then
            (PosSlots24SemanticBridge.pos24HeadWeight56 k : ℝ) /
              (8 * 218 * 48 * 2 * 2 * PosSlots24SemanticOracleConcrete80.pos80Slot4TotNat)
          else
            (PosSlots24SemanticBridge.pos24HeadWeight56 k : ℝ) /
              (216 * 48 * 2 * 2 * PosSlots24SemanticOracleConcrete80.pos80Slot2TotNat)
        else 0
      else 0
    else 0
  else
    let scratchZero := decide (∀ j : Fin 12, p80 (pos80SubIdx 63 12 (by
      decide) j) = 0) && (p80 78 == 0)
    let dpVal := Pos24HeadCoordXor80.bitsVal (fun j : Fin 3 ↦ p80 (pos80SubIdx 75 3 (by decide) j))
    let dp : Fin 8 := ⟨dpVal, Pos24HeadCoordXor80.bitsVal3_lt8 _⟩
    let metaOk := if s0 then (nuc == 0) && decide (anc < 218) && decide (part < 217)
      else (b0Val == 0) && decide (nuc < 216) && decide (anc < 218) && (part == 0)
    if scratchZero && metaOk && decide (fine30 < PosSlots24SemanticBridge.pos24TailSpan8 dp) &&
        (p80 == tailWitnessPayload80 b0Val nuc anc part dp fine30 (p80 31 == 1) (p80 79 == 1)) then
      if s0 then
        (1 : ℝ) / (8 * 218 * 2 * 2 * PosSlots24SemanticOracleConcrete80.pos80Slot4TotNat)
      else
        (1 : ℝ) / (216 * 2 * 2 * PosSlots24SemanticOracleConcrete80.pos80Slot2TotNat)
    else 0
def flipTailDpScratch80 (p : BitAssignment 80) : BitAssignment 80 := if p 30 == 1 then p else
    fun q ↦ if q.val == 75 then p 75 + p 0 else if q.val == 76 then p 76 + p 1 else if q.val
    == 77 then p 77 + p 2 else p q
def p80ClearCosetAndNucLocal (p : BitAssignment 80) : BitAssignment 80 :=
  fun q ↦ if 3 ≤ q.val ∧ q.val < 14 then 0 else p q
noncomputable def muSlot2Ideal216 (p : BitAssignment 80) : ℝ :=
  pos80IdealDist false (flipTailDpScratch80 p)
open Classical in
noncomputable def muSlot2Ideal218 (p : BitAssignment 80) : ℝ :=
  let nuc := Pos24HeadCoordXor80.bitsVal (fun j : Fin 8 ↦ p (pos80SubIdx 6 8 (by decide) j))
  if nuc < 216 then
    (108 / 109 : ℝ) * muSlot2Ideal216 p
  else if nuc < 218 then
    (27 / 218 : ℝ) * muSlot2Ideal216 (p80ClearCosetAndNucLocal p)
  else 0
set_option maxRecDepth 2000
end ConfigPosPostPrep80MergedVep
end PosPostPrep80MergedVep
end
end ModPosPostPrep80MergedVep

end QuantumComputation.Specs.StoppingPowerSolution
