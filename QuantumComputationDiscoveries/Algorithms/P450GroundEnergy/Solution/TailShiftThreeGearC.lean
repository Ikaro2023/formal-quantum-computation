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
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.TailShiftThreeGearA
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.TailShiftThreeGearB

@[expose] public section

/-!
# Tail-Shifted Three-Gear Dihedral QPE Engine (`TailShiftThreeGear`)

Assembles Tail-Shifted Three-Gear Bond-Deferred QPE (`StageC + StageM + StageF`) polymorphically
over `(wOuter, wInner2, ko, km, M, m2, m1, nDirtyLo, nStd, kTail, tShift, sRem, sUbC, sUbM)` for any
`w : ThreeGearBondDeferSpec M m2 m1 nDirtyLo` and `ts : TailShiftParams M m2 m1 nStd kTail tShift`:
1. Relocated tail-fused coarse `StageC` (`tailShiftStageCSuperDyn`) and clock-shifted middle
   `StageM` (`tailShiftPhaseMSuperDyn`).
2. `K`-step super-reflection invariant-subspace contract `WalkKStepRefl2InvErrLe` with single-step
   bridge `walkKStepRefl2InvErrLe_of_walkRefl2InvErrLe`.
3. Exact `16`-bit dihedral schedule identity `tailShiftThreeGear_ideal_fiber_mul_eq` on `0 .. M`,
   3-stage clean-ancilla `wp` composition `tailShiftTopLevelSuper_realizes`, and turnkey
   `Hi14247` / `Fast12603` closures consuming `TailShiftRayQuantSuperBox`.
-/

namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.TailShiftThreeGear
open QuantumComputation.Specs QuantumComputation.Specs.P450

open Operator QProg Matrix HermitianMat Circuit Real QuantumComputation.Specs
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution
open QuantumComputation.Specs.P450 QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution
open BlockEncodingCore
open BlockEncodingCircuit
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.WalkQPEBridge hiding
  rActLoc rActLoc_disjoint_rScrLoc rCatInAct rCatLoc rQPEInAct rQPEInAct_disjoint_rWalkCatInAct
  rQPEInAnc rQPELoc rQPELoc_disjoint_rScrLoc rQPELoc_disjoint_rWalkCatLoc rScrLoc rScrUbLoc
  rWalkCatInAct rWalkCatLoc rWalkCatLoc_disjoint_rScrLoc
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.WalkQPEBridgeXMeas hiding
  image_rFullZeroLoc rFullZeroLoc
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.WalkQPEFlexBridge hiding
  cleanRealizesSet_of_rScrUbLoc cleanRealizes_rScrLoc_of_sub
open TopIntegrationBridge Cat11CompactPhase2Bridge
open DihedralWalkQPE
open DihedralWalkQPE.BlockReflection
open DihedralWalkQPE.SineWindowFlexM
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.DihedralWalkQPE.MultiGearQPE (
  outZeroPrefixReg combARem combWalkReflRegs combWalkReflCovers CleanWalkRefl2)
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.TwoGearBox hiding
  m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11
open TailShiftBox TwoGearQPEPhase5
open TwoGearBondDefer
open TailShiftWindow46847
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.Comparators hiding CleanRealizes
open Comparators.ComparatorProofs
open scoped Matrix BigOperators Matrix.Norms.L2Operator

/-! ## Section 1: Relocated `StageC`, Clock-Shifted `StageM`, & Mux Sub-Slice Lifting -/

/-- `CleanRealizes` for `tailShiftClockPermDyn` on `rHi1` (`m1 .. 15`) with clean workspace
`rExtZeroDeferLocB ... m1 ...`. -/
theorem cleanRealizes_tailShiftClockPermDyn {Var : Type} [Fintype Var] [DecidableEq Var]
    {M m2 m1 nStd kTail tShift : ℕ} (wOuter wInner2 ko km nDirtyLo sRem : ℕ)
    (hkOut : ko ≤ wOuter) (hkMid : km ≤ wInner2) (hDirty1 : nDirtyLo ≤ m1)
    (ts : TailShiftParams M m2 m1 nStd kTail tShift) (v : Var) (invert : Bool) :
    let mOut := mOutUB wOuter
    let mMid := mMidUB wInner2
    let aRem := combARem wOuter wInner2 ko km
    let mRem := midRemWidth wInner2 km
    let rHi1 := (rActLoc 16 11 mOut mMid 0 aRem mRem sRem).compose
      ((rQPEInAct 16 11 mOut mMid).compose (rHiInQPE16 m1 ts.hm1_le16))
    XMeasCircuit.CleanRealizes v rHi1
      (rExtZeroDeferLocB wOuter wInner2 ko km m1 nDirtyLo sRem hkOut hkMid ts.hm1_le14 hDirty1)
      (permutationUnitary (if invert then (tailShiftClockPerm ts).symm else tailShiftClockPerm ts))
      (tailShiftClockPermDyn wOuter wInner2 ko km sRem ts v invert) := by
  intro mOut mMid aRem mRem rHi1
  let N := combQubitsB wOuter wInner2 ko km sRem
  have : NeZero (2 ^ N) := ⟨(Nat.two_pow_pos N).ne'⟩
  let rTopIn : QRegister (16 - m2) (16 - m1) := QRegister.block (m2 - m1) (16 - m2) ts.hSubM_le
  let rIn2 : QRegister ts.mode.wShift (16 - m1) :=
    QRegister.block (ts.mShift - m1) ts.mode.wShift ts.hShift_le
  have hTopSh : rTopIn.DisjointWires rIn2 := QRegister.disjoint_iff.mpr fun i j hij ↦ by
    have hv := congrArg Fin.val hij
    have hj := j.isLt
    have hsh := ts.hShift_eq
    simp only [rTopIn, rIn2, QRegister.block_apply_val] at hv
    omega
  let rTopC := rHi1.compose rTopIn
  let rShift := rHi1.compose rIn2
  let rScr := rScrLoc 16 11 mOut mMid 0 aRem mRem sRem
  let hscr := ts.scr_need_le aRem mRem sRem
  let wFlag := rScr ⟨0, by omega⟩
  let rCarry := rScr.compose (QRegister.block 1 (16 - m2 - 2) (by omega))
  let rBodyScr := rScr.compose (QRegister.block (1 + (16 - m2 - 2)) ts.mode.sBody hscr)
  have hHiEq : rHi1 =
      (rQPELoc 16 11 mOut mMid 0 aRem mRem sRem).compose (rHiInQPE16 m1 ts.hm1_le16) := by
    ext i
    rfl
  have hHiScr : rHi1.DisjointWires rScr := hHiEq ▸ QubitisedWalk.disjointWires_compose_left
    (rQPELoc_disjoint_rScrLoc 16 11 mOut mMid 0 aRem mRem sRem)
  have hFT : (QRegister.singleton wFlag).DisjointWires rShift := by
    rw [QRegister.disjoint_iff]
    intro a j
    fin_cases a
    exact ((QubitisedWalk.disjointWires_compose_left hHiScr).ne j ⟨0, by omega⟩).symm
  have hFBS : ((QRegister.singleton wFlag).concat rShift hFT).DisjointWires rBodyScr := by
    rw [QRegister.disjoint_iff]
    intro p j
    rcases finSumFinEquiv.surjective p with ⟨a | i, rfl⟩
    · fin_cases a
      simp only [finSumFinEquiv_apply_left, QRegister.concat_apply_left,
        QRegister.singleton_apply, wFlag, rBodyScr, QRegister.compose_apply]
      intro h
      have hv := congrArg Fin.val (rScr.wires.injective h)
      simp only [QRegister.block_apply_val] at hv
      omega
    · simp only [finSumFinEquiv_apply_right, QRegister.concat_apply_right]
      exact (QubitisedWalk.disjointWires_compose_left (QubitisedWalk.disjointWires_compose_right
        hHiScr)).ne i j
  let rBodyLoc := ((QRegister.singleton wFlag).concat rShift hFT).concat rBodyScr hFBS
  have hBodyOn := CleanDyn.CleanRealizes.onRegister rBodyLoc
    (cleanRealizes_tailShiftBodyLocalDyn ts.mode v invert)
  have hrBAct : rBodyLoc.compose
      (QRegister.block 0 (1 + ts.mode.wShift) (by cases ts.mode <;> decide)) =
      (QRegister.singleton wFlag).concat rShift hFT := by
    ext idx
    have hp : Fin.castAdd ts.mode.sBody idx =
        QRegister.block 0 (1 + ts.mode.wShift) (by cases ts.mode <;> decide) idx :=
      Fin.ext (by simp)
    simp only [rBodyLoc, QRegister.compose_apply, ← hp, QRegister.concat_apply_left]
  have hrBScr : rBodyLoc.compose
      (QRegister.block (1 + ts.mode.wShift) ts.mode.sBody (by cases ts.mode <;> decide)) =
      rBodyScr := by
    ext idx
    have hp : Fin.natAdd (1 + ts.mode.wShift) idx =
        QRegister.block (1 + ts.mode.wShift) ts.mode.sBody (by cases ts.mode <;> decide) idx :=
      Fin.ext (by simp)
    simp only [rBodyLoc, QRegister.compose_apply, ← hp, QRegister.concat_apply_right]
  let uSh := permutationUnitary
    (if invert then
      addConstModPerm ts.mode.wShift ts.mode.cBwd ts.mode.cFwd ts.mode.cBwd_add_cFwd_mod
     else
      addConstModPerm ts.mode.wShift ts.mode.cFwd ts.mode.cBwd ts.mode.cFwd_add_cBwd_mod)
  have hBody : Comparators.CleanRealizes v
      ((QRegister.singleton wFlag).concat rShift hFT) rBodyScr (muxBitLocalUnitary 1 uSh)
      ((tailShiftBodyLocalDyn ts.mode v invert).onRegister rBodyLoc) := by
    rw [← hrBAct, ← hrBScr]
    exact hBodyOn
  have hAT : rTopC.DisjointWires rShift := QRegister.disjoint_iff.mpr fun i j hij ↦
    hTopSh.ne i j (rHi1.wires.injective hij)
  have hFlag := cleanRealizes_withEqConstFlagDyn v rTopC (nStd + 1) rCarry wFlag rShift rBodyScr
    ts.hbC_ge1
    (QubitisedWalk.disjointWires_compose_left (QubitisedWalk.disjointWires_compose_right hHiScr))
    (fun i ↦ (QubitisedWalk.disjointWires_compose_left hHiScr).ne i ⟨0, by omega⟩)
    (fun j h ↦ by
      have hv := congrArg Fin.val (rScr.wires.injective h)
      simp only [QRegister.block_apply_val] at hv
      omega)
    hAT
    (QubitisedWalk.disjointWires_compose_right
      (QubitisedWalk.disjointWires_compose_left hHiScr.symm))
    hFT
    (QubitisedWalk.disjointWires_compose_left (QubitisedWalk.disjointWires_compose_right hHiScr))
    (QRegister.disjoint_iff.mpr fun i j h ↦ by
      have hv := congrArg Fin.val (rScr.wires.injective h)
      simp only [QRegister.block_apply_val] at hv
      omega)
    (fun j h ↦ by
      have hv := congrArg Fin.val (rScr.wires.injective h)
      simp only [QRegister.block_apply_val] at hv
      omega)
    (QubitisedWalk.disjointWires_compose_left (QubitisedWalk.disjointWires_compose_right hHiScr))
    hBody
  dsimp only at hFlag
  have hFlag' : XMeasCircuit.CleanRealizes v _ _ _ _ := hFlag
  have hCompEq : rTopC.concat rShift hAT = rHi1.compose (rTopIn.concat rIn2 hTopSh) := by
    ext idx
    rcases finSumFinEquiv.surjective idx with ⟨i | j, rfl⟩ <;>
      simp [rTopC, rShift, finSumFinEquiv_apply_left,
        finSumFinEquiv_apply_right, QRegister.concat_apply_left, QRegister.concat_apply_right]
  have hMuxEq := embed_subClockMux_eq_tailShiftClockPerm ts invert
  dsimp only at hMuxEq
  have hLifted := cleanRealizes_of_eq
    (XMeasCircuit.CleanRealizes.liftActiveOfEq (rAct := rHi1)
      (inner := rTopIn.concat rIn2 hTopSh) hCompEq hFlag')
    hMuxEq
  let rExt := rExtZeroDeferLocB wOuter wInner2 ko km m1 nDirtyLo sRem hkOut hkMid ts.hm1_le14
    hDirty1
  have hScrSubExt : rScr.image ⊆ rExt.image := by
    intro q hq
    have hmemF : q ∈ (rFullZeroLocB wOuter wInner2 ko km sRem hkOut hkMid).image := by
      rw [rFullZeroLocB, image_rFullZeroLoc, Finset.mem_union]
      exact Or.inl hq
    obtain ⟨ifull, rfl⟩ := (QRegister.mem_image _ _).mp hmemF
    exact (QRegister.mem_image _ _).mpr ⟨Fin.castAdd _ ifull, by
      simp [rExt, rExtZeroDeferLocB, rExtZeroLocB]⟩
  have hTotSubScr {h1 h2} :
      ∀ q ∈ (((QRegister.singleton wFlag).concat rCarry h1).concat rBodyScr h2).image,
        q ∈ rScr.image := by
    intro q hq
    obtain ⟨p, rfl⟩ := (QRegister.mem_image _ _).mp hq
    rcases finSumFinEquiv.surjective p with ⟨u | j, rfl⟩
    · simp only [finSumFinEquiv_apply_left, QRegister.concat_apply_left]
      rcases finSumFinEquiv.surjective u with ⟨a | i, rfl⟩
      · fin_cases a
        exact (QRegister.mem_image rScr _).mpr ⟨⟨0, by omega⟩, rfl⟩
      · simp only [finSumFinEquiv_apply_right, QRegister.concat_apply_right, rCarry,
          QRegister.compose_apply]
        exact (QRegister.mem_image rScr _).mpr ⟨_, rfl⟩
    · simp only [finSumFinEquiv_apply_right, QRegister.concat_apply_right, rBodyScr,
        QRegister.compose_apply]
      exact (QRegister.mem_image rScr _).mpr ⟨_, rfl⟩
  let rAncZ := liftOutMidZeroToAnc mOut mMid
    (outZeroPrefixReg wOuter ko hkOut) (midZeroPrefixReg wInner2 km hkMid)
  have hHiDisjExt : rHi1.DisjointWires rExt := QRegister.disjoint_iff.mpr fun i j hij ↦ by
    rcases finSumFinEquiv.surjective j with ⟨ifull | ibor, rfl⟩
    · simp only [finSumFinEquiv_apply_left, rExt, rExtZeroDeferLocB, rExtZeroLocB,
        QRegister.concat_apply_left] at hij
      have hmem : rFullZeroLocB wOuter wInner2 ko km sRem hkOut hkMid ifull ∈
          (rFullZeroLoc 16 11 mOut mMid 0 aRem mRem sRem rAncZ).image :=
        (QRegister.mem_image _ _).mpr ⟨ifull, rfl⟩
      rw [image_rFullZeroLoc, Finset.mem_union] at hmem
      rcases hmem with hscrB | hancB
      · obtain ⟨is, his⟩ := (QRegister.mem_image _ _).mp hscrB
        exact hHiScr.ne i is (hij.trans his.symm)
      · obtain ⟨ia, hia⟩ := (QRegister.mem_image _ _).mp hancB
        rw [hHiEq] at hij
        exact (QubitisedWalk.disjointWires_compose_left
          (QubitisedWalk.disjointWires_compose_right
            (QubitisedWalk.disjointWires_compose_right
              (rQPELoc_disjoint_rWalkCatLoc 16 11 mOut mMid 0 aRem mRem sRem)))).ne i ia
          (hij.trans hia.symm)
    · rw [hHiEq] at hij
      simp only [finSumFinEquiv_apply_right, rExt, rExtZeroDeferLocB, rExtZeroLocB,
        QRegister.concat_apply_right, rBorrowLocB, QRegister.compose_apply] at hij
      have hq := congrArg Fin.val ((rQPELoc 16 11 mOut mMid 0 aRem mRem sRem).wires.injective hij)
      have hib := ibor.isLt
      simp only [rHiInQPE16, rBorrowInQPE16, QRegister.block_apply_val] at hq
      omega
  dsimp only [tailShiftClockPermDyn]
  exact absorbCleanActive_of_comm2 hLifted (fun q hq ↦ hScrSubExt (hTotSubScr q hq)) rfl
    (QRegister.embedMatrix_comm_basisOutcomeProjector_of_disjoint rHi1 rExt hHiDisjExt _ 0)
theorem TailShiftParams.hM_lt {M m2 m1 nStd kTail tShift : ℕ}
    (ts : TailShiftParams M m2 m1 nStd kTail tShift) : M < 2 ^ 16 := by
  have hp : 2 ^ (16 - m2) * 2 ^ m2 = 2 ^ 16 := by
    rw [← pow_add]
    have := ts.hm2_le14
    congr 1
    omega
  have hle : (nStd + 2) * 2 ^ m2 ≤ 2 ^ 16 := by
    rw [← hp]
    exact Nat.mul_le_mul_right _ ts.hnStd_hi
  have hlt : (nStd + 1) * 2 ^ m2 + kTail < (nStd + 2) * 2 ^ m2 := by
    have := ts.hkTail_lt
    linarith
  have hMeq := ts.hM_eq
  omega

/-- Smart constructor for concrete `TailShiftParams` instances given `mode`, `mShift`, and the
coarse affine-fold wraparound proofs. -/
def mkTailShiftParams (M m2 m1 nStd kTail tShift : ℕ)
    (mode : TailShiftMode) (mShift : ℕ) (hm1 : m1 ≤ mShift)
    (hFoldTop : affineFoldVal (16 - m2 - 1) (nStd + 1 - 2 ^ (16 - m2 - 1)) (nStd + 1) =
      2 ^ (16 - m2) - 1)
    (hFoldStd : ∀ q : Fin (2 ^ (16 - m2)), q.val ≤ nStd →
      affineFoldVal (16 - m2 - 1) (nStd + 1 - 2 ^ (16 - m2 - 1)) q.val < 2 ^ (16 - m2) - 1)
    (hmShift_eq : mShift + mode.wShift = m2 := by decide) (hm2_le14 : m2 ≤ 14 := by decide)
    (hnStd_lo : 2 ^ (16 - m2 - 1) ≤ nStd := by decide)
    (hnStd_hi : nStd + 1 < 2 ^ (16 - m2) := by decide)
    (hM_eq : M + 1 = (nStd + 1) * 2 ^ m2 + kTail := by decide) (hkTail_pos : 1 ≤ kTail := by decide)
    (hkTail_lt : kTail < 2 ^ m2 := by decide)
    (hqShift_base : mode.cFwd * 2 ^ mShift = 2 ^ m2 - kTail := by decide)
    (htShift : 2 * (eqConstTCount (16 - m2) (nStd + 1) + mode.tBody) ≤ tShift := by decide) :
    TailShiftParams M m2 m1 nStd kTail tShift :=
  { mode := mode, mShift := mShift, hm1_le := hm1, hmShift_eq := hmShift_eq,
    hm2_le14 := hm2_le14, hnStd_lo := hnStd_lo, hnStd_hi := hnStd_hi,
    hFoldTop := hFoldTop, hFoldStd := hFoldStd, hM_eq := hM_eq,
    hkTail_pos := hkTail_pos, hkTail_lt := hkTail_lt, htShift := htShift,
    hqShift_eq := by
      rw [mul_assoc, ← pow_add, Nat.sub_add_cancel hm1]
      exact hqShift_base }

/-- `TailShiftParams` for `(M = 46719, m2 = 10, nStd = 44, kTail = 640, tShift = 56)` (`m1 ≤ 7`). -/
def tailShiftParams_46719_10 (m1 : ℕ) (hm1 : m1 ≤ 7 := by decide) :
    TailShiftParams 46719 10 m1 44 640 56 :=
  mkTailShiftParams 46719 10 m1 44 640 56 .mod8Add3 7 hm1
    affineFoldVal_5_13_45_eq_63 affineFoldVal_5_13_lt_63_of_le_44

theorem affineFoldVal_5_14_46_eq_63 : affineFoldVal 5 14 46 = 63 := by decide

theorem affineFoldVal_5_14_lt_63_of_le_45 (q : Fin 64) (hq : q.val ≤ 45) :
    affineFoldVal 5 14 q.val < 63 := by
  revert hq
  revert q
  decide

/-- `TailShiftParams` for `(M = 47487, m2 = 10, nStd = 45, kTail = 384, tShift = 56)`.
-/
def tailShiftParams_47487_10 (m1 : ℕ) (hm1 : m1 ≤ 7 := by decide) :
    TailShiftParams 47487 10 m1 45 384 56 :=
  mkTailShiftParams 47487 10 m1 45 384 56 .mod8Add5 7 hm1
    affineFoldVal_5_14_46_eq_63 affineFoldVal_5_14_lt_63_of_le_45

theorem spec_hm1_15 {M m2 m1 nDirtyLo : ℕ}
    (w : ThreeGearBondDeferSpec M m2 m1 nDirtyLo) : m1 ≤ 15 :=
  le_trans w.hm12 (le_trans w.hm2_14 (by decide))

theorem spec_hm1_16 {M m2 m1 nDirtyLo : ℕ}
    (w : ThreeGearBondDeferSpec M m2 m1 nDirtyLo) : m1 ≤ 16 :=
  le_trans (spec_hm1_15 w) (by decide)

theorem embed_rCombSubInAct_eq_rCombHiInAct (mOut mMid m1 mCut bGear : ℕ)
    (hm1Cut : m1 ≤ mCut) (hbCut : mCut + bGear ≤ 16) :
    let hm1_16 : m1 ≤ 16 := by omega
    let rSlice : QRegister bGear (16 - m1) := QRegister.block (mCut - m1) bGear (by omega)
    ∀ F : Fin (2 ^ bGear) → Unitary (2 ^ walkCatWidth 11 mOut mMid),
      (rCombSubInAct mOut mMid mCut bGear hbCut).embedUnitary (QubitisedWalk.qpeMuxUnitary F) =
        (rCombHiInAct mOut mMid m1 hm1_16).embedUnitary
          (QubitisedWalk.qpeMuxUnitary (fun x : Fin (2 ^ (16 - m1)) ↦ F (rSlice.extractIndex
            x))) := by
  intro hm1_16 rSlice F
  let k := walkCatWidth 11 mOut mMid
  let rQ := QubitisedWalk.qpeInCombined (16 - m1) k
  let rW := QubitisedWalk.walkInCombined (16 - m1) k
  have hSubEq : rCombSubInAct mOut mMid mCut bGear hbCut =
      (rCombHiInAct mOut mMid m1 hm1_16).compose ((rQ.compose rSlice).concat rW
        (QubitisedWalk.disjointWires_compose_left
          (QubitisedWalk.qpeInCombined_disjoint_walkInCombined (16 - m1) k))) := by
    ext idx
    rcases finSumFinEquiv.surjective idx with ⟨i | j, rfl⟩
    · have hi := i.isLt
      simp only [finSumFinEquiv_apply_left, QRegister.compose_apply]
      have hinner : ((rQ.compose rSlice).concat rW (QubitisedWalk.disjointWires_compose_left
          (QubitisedWalk.qpeInCombined_disjoint_walkInCombined (16 - m1) k))) (Fin.castAdd k i) =
          Fin.castAdd k ⟨(mCut - m1) + i.val, by omega⟩ := by
        simp only [QRegister.concat_apply_left, QRegister.compose_apply, rQ,
          QubitisedWalk.qpeInCombined, rSlice]
        ext
        simp only [Fin.val_castAdd, QRegister.block_apply_val]
        omega
      rw [hinner]
      simp only [k, rCombSubInAct, rCombHiInAct, QRegister.concat_apply_left,
        QRegister.compose_apply, rQPEInAct, rHiInQPE16, QRegister.block_apply_val]
      omega
    · simp only [finSumFinEquiv_apply_right, QRegister.compose_apply]
      have hinner : ((rQ.compose rSlice).concat rW (QubitisedWalk.disjointWires_compose_left
          (QubitisedWalk.qpeInCombined_disjoint_walkInCombined (16 - m1) k))) (Fin.natAdd bGear j) =
          Fin.natAdd (16 - m1) j := by
        simp only [QRegister.concat_apply_right, rW, QubitisedWalk.walkInCombined]
        ext
        simp only [Fin.val_natAdd, QRegister.block_apply_val]
      rw [hinner]
      simp only [rCombSubInAct, rCombHiInAct, QRegister.concat_apply_right]
  rw [hSubEq, QRegister.embedUnitary_compose, embed_slice_qpeMuxUnitary]

/-- Clock-shifted middle `StageM`: conjugates `threeGearDeferPhaseMSuperDyn` by
`tailShiftClockPermDyn` (`false` before, `true` after). -/
def tailShiftPhaseMSuperDyn {Var : Type} {M m2 m1 nStd kTail tShift : ℕ}
    (wOuter wInner2 ko km nDirtyLo sRem sUbM : ℕ)
    (hkOut : ko ≤ wOuter) (hkMid : km ≤ wInner2) (hDirty1 : nDirtyLo ≤ m1)
    (hsUbM : sUbM ≤ sRem + (m1 - nDirtyLo))
    (ts : TailShiftParams M m2 m1 nStd kTail tShift) (v : Var)
    (pSuperM : DynamicCircuit Var (combQubitsAt (m2 - m1) wOuter wInner2 ko km 0 sUbM)) :
    DynamicCircuit Var (combQubitsB wOuter wInner2 ko km sRem) :=
  .seq (tailShiftClockPermDyn wOuter wInner2 ko km sRem ts v false)
    (.seq (threeGearDeferPhaseMSuperDyn wOuter wInner2 ko km m2 m1 nDirtyLo sRem sUbM
        hkOut hkMid ts.hm2_le14 hDirty1 hsUbM v pSuperM)
      (tailShiftClockPermDyn wOuter wInner2 ko km sRem ts v true))

theorem tailShiftPhaseMSuperDyn_count_toff {Var : Type} {M m2 m1 nStd kTail tShift : ℕ}
    (wOuter wInner2 ko km nDirtyLo sRem sUbM : ℕ)
    (hkOut : ko ≤ wOuter) (hkMid : km ≤ wInner2) (hDirty1 : nDirtyLo ≤ m1)
    (hsUbM : sUbM ≤ sRem + (m1 - nDirtyLo))
    (ts : TailShiftParams M m2 m1 nStd kTail tShift) (v : Var)
    {pSuperM : DynamicCircuit Var (combQubitsAt (m2 - m1) wOuter wInner2 ko km 0 sUbM)}
    (hMToff : pSuperM.count .TOFF = 0) :
    (tailShiftPhaseMSuperDyn wOuter wInner2 ko km nDirtyLo sRem sUbM hkOut hkMid hDirty1 hsUbM
      ts v pSuperM).count .TOFF = 0 := by
  have hm12 := ts.hm1_lt_m2
  simp only [tailShiftPhaseMSuperDyn, DynamicCircuit.count, tailShiftClockPermDyn_count_toff,
    threeGearDeferPhaseMSuperDyn, dite_eq_left hm12, DynamicCircuit.count_onRegister,
    zero_add, add_zero]
  exact affineDihedralRefl2Dyn_count_toff _ _ _ _ _ _ _ _ _ _ _ _ _ _ hMToff

theorem two_pow_pred_le_two_pow_sub_one {k : ℕ} (hk : 1 ≤ k) : 2 ^ (k - 1) ≤ 2 ^ k - 1 := by
  have heq : k = (k - 1) + 1 := by omega
  have hp : 1 ≤ 2 ^ (k - 1) := Nat.one_le_two_pow
  conv_rhs => rw [heq, pow_succ]
  omega

theorem tailShiftPhaseMSuperDyn_count_t_le {Var : Type} {M m2 m1 nStd kTail tShift : ℕ}
    (wOuter wInner2 ko km nDirtyLo sRem sUbM : ℕ)
    (hkOut : ko ≤ wOuter) (hkMid : km ≤ wInner2) (hDirty1 : nDirtyLo ≤ m1)
    (hsUbM : sUbM ≤ sRem + (m1 - nDirtyLo))
    (ts : TailShiftParams M m2 m1 nStd kTail tShift) (v : Var)
    (pSuperM : DynamicCircuit Var (combQubitsAt (m2 - m1) wOuter wInner2 ko km 0 sUbM)) :
    (tailShiftPhaseMSuperDyn wOuter wInner2 ko km nDirtyLo sRem sUbM hkOut hkMid hDirty1 hsUbM
      ts v pSuperM).count .T ≤
      tShift + walkCtrlTCount (m2 - m1) (2 ^ (m2 - m1) - 1)
        (combARem wOuter wInner2 ko km) (pSuperM.count .T) := by
  have hm12 := ts.hm1_lt_m2
  have hMlo : 2 ^ ((m2 - m1) - 1) ≤ 2 ^ (m2 - m1) - 1 :=
    two_pow_pred_le_two_pow_sub_one (by omega)
  have hpair := tailShiftClockPermDyn_pair_count_t_le wOuter wInner2 ko km sRem ts v
  simp only [tailShiftPhaseMSuperDyn, DynamicCircuit.count, threeGearDeferPhaseMSuperDyn,
    dite_eq_left hm12, DynamicCircuit.count_onRegister]
  rw [affineDihedralRefl2Dyn_count_t _ _ _ _ _ _ _ _ _ _ _ _ hMlo]
  omega

theorem tailShiftPhaseMSuperDyn_cleanRealizes {Var : Type} [Fintype Var] [DecidableEq Var]
    {M m2 m1 nStd kTail tShift : ℕ}
    (wOuter wInner2 ko km nDirtyLo sRem sUbM : ℕ)
    (hkOut : ko ≤ wOuter) (hkMid : km ≤ wInner2) (hDirty1 : nDirtyLo ≤ m1)
    (hsUbM : sUbM ≤ sRem + (m1 - nDirtyLo))
    (ts : TailShiftParams M m2 m1 nStd kTail tShift) (v : Var)
    {uSuperM : Unitary (2 ^ walkCatWidth 11 (mOutUB wOuter) (mMidUB wInner2))}
    {pSuperM : DynamicCircuit Var (combQubitsAt (m2 - m1) wOuter wInner2 ko km 0 sUbM)}
    (hCleanM : CleanWalkRefl2At (m2 - m1) wOuter wInner2 ko km 0 sUbM hkOut hkMid v uSuperM
      pSuperM) :
    let mOut := mOutUB wOuter
    let mMid := mMidUB wInner2
    let aRem := combARem wOuter wInner2 ko km
    let mRem := midRemWidth wInner2 km
    let R₁c := QubitisedWalk.reflInUnitary (inAllWalkCat 11 mOut mMid)
    let rSliceM : QRegister (m2 - m1) (16 - m1) := QRegister.block 0 (m2 - m1) ts.hBlock0SubM_le
    let FM_shifted : Fin (2 ^ (16 - m1)) → Unitary (2 ^ walkCatWidth 11 mOut mMid) :=
      fun x ↦ affineScheduleFiber (m2 - m1) (2 ^ (m2 - m1) - 1) (R₁c * uSuperM) R₁c
        (rSliceM.extractIndex (tailShiftClockPerm ts x))
    XMeasCircuit.CleanRealizes v (rActLoc 16 11 mOut mMid 0 aRem mRem sRem)
      (rExtZeroDeferLocB wOuter wInner2 ko km m1 nDirtyLo sRem hkOut hkMid ts.hm1_le14 hDirty1)
      ((rCombHiInAct mOut mMid m1 ts.hm1_le16).embedUnitary (QubitisedWalk.qpeMuxUnitary
        FM_shifted))
      (tailShiftPhaseMSuperDyn wOuter wInner2 ko km nDirtyLo sRem sUbM hkOut hkMid hDirty1 hsUbM
        ts v pSuperM) := by
  intro mOut mMid aRem mRem R₁c rSliceM FM_shifted
  have hm12 := ts.hm1_lt_m2
  have hm2_14 := ts.hm2_le14
  have hMlo : 2 ^ ((m2 - m1) - 1) ≤ 2 ^ (m2 - m1) - 1 :=
    two_pow_pred_le_two_pow_sub_one (by omega)
  have hCovM := combWalkReflCovers (m2 - m1) 11 wOuter wInner2 0 sUbM ko km hkOut hkMid
  have hMLoc := affineDihedralRefl2Dyn_cleanRealizes (m2 - m1) 11 mOut mMid 0 sUbM v hCovM
    (m2 - m1) (2 ^ (m2 - m1) - 1) (by omega) le_rfl hMlo
    (hbScr_gearDefer (m2 - m1) wOuter wInner2 ko km sUbM hkOut hkMid (by omega)) hCleanM
  have hMRel := cleanRealizes_gearDefer_relocated (m2 - m1) m1 wOuter wInner2 ko km nDirtyLo sRem
    sUbM
    hkOut hkMid ts.hm1_le14 (by omega) hDirty1 hsUbM v hMLoc
  dsimp only at hMRel
  have hMidEq : threeGearDeferPhaseMSuperDyn wOuter wInner2 ko km m2 m1 nDirtyLo sRem sUbM
      hkOut hkMid hm2_14 hDirty1 hsUbM v pSuperM =
      (affineDihedralRefl2Dyn (m2 - m1) 11 (mOutUB wOuter) (mMidUB wInner2) 0 sUbM v
        (combWalkReflRegs 11 wOuter wInner2 ko km hkOut hkMid) (m2 - m1) (2 ^ (m2 - m1) - 1)
        (by omega) le_rfl (hbScr_gearDefer (m2 - m1) wOuter wInner2 ko km sUbM hkOut hkMid
          (by omega))
        pSuperM).onRegister
        (rGearDeferInB (m2 - m1) m1 wOuter wInner2 ko km nDirtyLo sRem sUbM (by omega) hDirty1
          hsUbM) :=
    dite_eq_left hm12
  rw [← hMidEq] at hMRel
  have hLiftM := embed_rCombSubInAct_eq_rCombHiInAct mOut mMid m1 m1 (m2 - m1) le_rfl (by omega)
    (affineScheduleFiber (m2 - m1) (2 ^ (m2 - m1) - 1) (R₁c * uSuperM) R₁c)
  have hSlice0 : (QRegister.block (m1 - m1) (m2 - m1) (by omega) :
      QRegister (m2 - m1) (16 - m1)) = rSliceM := by
    ext i
    simp [rSliceM]
  rw [hSlice0] at hLiftM
  have hMidAct := cleanRealizes_of_eq hMRel hLiftM
  let rAct := rActLoc 16 11 mOut mMid 0 aRem mRem sRem
  have hCF := cleanRealizes_tailShiftClockPermDyn wOuter wInner2 ko km nDirtyLo sRem hkOut hkMid
    hDirty1 ts v false
  dsimp only at hCF
  have hCB := cleanRealizes_tailShiftClockPermDyn wOuter wInner2 ko km nDirtyLo sRem hkOut hkMid
    hDirty1 ts v true
  dsimp only at hCB
  have hPF := XMeasCircuit.CleanRealizes.liftActiveOfEq (rAct := rAct)
    (inner := (rQPEInAct 16 11 mOut mMid).compose (rHiInQPE16 m1 ts.hm1_le16)) rfl hCF
  have hPB := XMeasCircuit.CleanRealizes.liftActiveOfEq (rAct := rAct)
    (inner := (rQPEInAct 16 11 mOut mMid).compose (rHiInQPE16 m1 ts.hm1_le16)) rfl hCB
  refine cleanRealizes_of_eq (hPF.seq (hMidAct.seq hPB)) ?_
  have hHiSub : (rQPEInAct 16 11 mOut mMid).compose (rHiInQPE16 m1 ts.hm1_le16) =
      (rCombHiInAct mOut mMid m1 ts.hm1_le16).compose
        (QubitisedWalk.qpeInCombined (16 - m1) (walkCatWidth 11 mOut mMid)) := by
    ext i
    simp [rCombHiInAct, QubitisedWalk.qpeInCombined]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [hHiSub, QRegister.embedUnitary_compose, QRegister.embedUnitary_compose,
    ← QRegister.embedUnitary_mul, ← QRegister.embedUnitary_mul]
  exact congrArg (rCombHiInAct mOut mMid m1 ts.hm1_le16).embedUnitary
    (qpeMuxUnitary_conj_perm_gen (tailShiftClockPerm ts) _)

/-! ## Section 2: Master Programs, Closed-Form `T`-Counts & 3-Stage `wp` Realization -/

/-- Blocked Part 2 (`w.cWinM ; tailShiftPhaseMSuperDyn`), keeping `nDirtyLo .. m1 - 1` clean. -/
def tailShiftBlockedPart2SuperProg {Var : Type} {M m2 m1 nStd kTail tShift : ℕ}
    (wOuter wInner2 ko km nDirtyLo sRem sUbM : ℕ)
    (hkOut : ko ≤ wOuter) (hkMid : km ≤ wInner2) (hDirty1 : nDirtyLo ≤ m1)
    (hsUbM : sUbM ≤ sRem + (m1 - nDirtyLo))
    (ts : TailShiftParams M m2 m1 nStd kTail tShift) (v : Var)
    (w : ThreeGearBondDeferSpec M m2 m1 nDirtyLo)
    (pSuperM : DynamicCircuit Var (combQubitsAt (m2 - m1) wOuter wInner2 ko km 0 sUbM)) :
    DynamicCircuit Var (combQubitsB wOuter wInner2 ko km sRem) :=
  let mOut := mOutUB wOuter
  let mMid := mMidUB wInner2
  let aRem := combARem wOuter wInner2 ko km
  let mRem := midRemWidth wInner2 km
  let rWinM := (rQPELoc 16 11 mOut mMid 0 aRem mRem sRem).compose
    (rWinHiDeferInQPE m1 nDirtyLo (spec_hm1_16 w) hDirty1)
  .seq (.circuit (w.cWinM.onRegister rWinM))
    (tailShiftPhaseMSuperDyn wOuter wInner2 ko km nDirtyLo sRem sUbM hkOut hkMid hDirty1 hsUbM
      ts v pSuperM)

theorem restrictZero_castLen {V : Type} {n k₁ k₂ : ℕ} (hk : k₁ = k₂)
    (Θ : QCAssertion V (2 ^ n)) (r₁ : QRegister k₁ n) (r₂ : QRegister k₂ n)
    (hr : ∀ i : Fin k₁, r₁ i = r₂ (i.cast hk)) :
    restrictAssertionToZeroAncilla Θ r₁ = restrictAssertionToZeroAncilla Θ r₂ := by
  subst hk
  have heq : r₁ = r₂ := by
    ext i
    exact congrArg Fin.val (hr i)
  rw [heq]

theorem cleanRealizes_winHiDefer_on_rExtZeroDefer {Var : Type} [Fintype Var] [DecidableEq Var]
    (wOuter wInner2 ko km mCut nDirtyLo sRem : ℕ)
    (hkOut : ko ≤ wOuter) (hkMid : km ≤ wInner2) (hmCut14 : mCut ≤ 14) (hDirty : nDirtyLo ≤ mCut)
    (v : Var) (cWin : Circuit (nDirtyLo + (16 - mCut))) (hToff : cWin.count .TOFF = 0) :
    let mOut := mOutUB wOuter
    let mMid := mMidUB wInner2
    let aRem := combARem wOuter wInner2 ko km
    let mRem := midRemWidth wInner2 km
    let hmCut16 : mCut ≤ 16 := by omega
    let rWin := rWinHiDeferInQPE mCut nDirtyLo hmCut16 hDirty
    XMeasCircuit.CleanRealizes v (rActLoc 16 11 mOut mMid 0 aRem mRem sRem)
      (rExtZeroDeferLocB wOuter wInner2 ko km mCut nDirtyLo sRem hkOut hkMid hmCut14 hDirty)
      (((rQPEInAct 16 11 mOut mMid).compose rWin).embedUnitary cWin.eval)
      (.circuit (cWin.onRegister ((rQPELoc 16 11 mOut mMid 0 aRem mRem sRem).compose rWin))) := by
  intro mOut mMid aRem mRem hmCut16 rWin
  have hWin := cleanRealizes_subcircuit_rExtZeroB wOuter wInner2 ko km (mCut + 1) nDirtyLo sRem
    hkOut hkMid (by omega) (by omega) (by omega) v
    ((rQPEInAct 16 11 mOut mMid).compose rWin)
    (fun j ↦ by
      right
      rcases finSumFinEquiv.surjective j with ⟨il | ih, rfl⟩
      · have hil := il.isLt
        simp only [QRegister.compose_apply, finSumFinEquiv_apply_left, rWin, rWinHiDeferInQPE,
          QRegister.concat_apply_left, rQPEInAct, QRegister.block_apply_val]
        dsimp only [mOut, mMid, walkCatWidth, walkWidth]
        exact ⟨by omega, Or.inl (by omega)⟩
      · simp only [QRegister.compose_apply, finSumFinEquiv_apply_right, rWin, rWinHiDeferInQPE,
          QRegister.concat_apply_right, rQPEInAct, rHiInQPE16, QRegister.block_apply_val]
        dsimp only [mOut, mMid, walkCatWidth, walkWidth]
        exact ⟨by omega, Or.inr (by omega)⟩)
    cWin hToff
  dsimp only at hWin
  have hrWin : (rActLoc 16 11 (mOutUB wOuter) (mMidUB wInner2) 0 aRem mRem sRem).compose
      ((rQPEInAct 16 11 mOut mMid).compose rWin) =
      (rQPELoc 16 11 mOut mMid 0 aRem mRem sRem).compose rWin := by
    ext i
    rfl
  rwa [hrWin] at hWin

theorem tailShiftBlockedPart2SuperProg_cleanRealizes {Var : Type} [Fintype Var] [DecidableEq Var]
    {M m2 m1 nStd kTail tShift : ℕ} (wOuter wInner2 ko km nDirtyLo sRem sUbM : ℕ)
    (hkOut : ko ≤ wOuter) (hkMid : km ≤ wInner2) (hDirty1 : nDirtyLo ≤ m1)
    (hsUbM : sUbM ≤ sRem + (m1 - nDirtyLo))
    (ts : TailShiftParams M m2 m1 nStd kTail tShift) (v : Var)
    (w : ThreeGearBondDeferSpec M m2 m1 nDirtyLo)
    {uSuperM : Unitary (2 ^ walkCatWidth 11 (mOutUB wOuter) (mMidUB wInner2))}
    {pSuperM : DynamicCircuit Var (combQubitsAt (m2 - m1) wOuter wInner2 ko km 0 sUbM)}
    (hCleanM : CleanWalkRefl2At (m2 - m1) wOuter wInner2 ko km 0 sUbM hkOut hkMid v uSuperM
      pSuperM) :
    let mOut := mOutUB wOuter
    let mMid := mMidUB wInner2
    let aRem := combARem wOuter wInner2 ko km
    let mRem := midRemWidth wInner2 km
    let rQPE := rQPEInAct 16 11 mOut mMid
    let R₁c := QubitisedWalk.reflInUnitary (inAllWalkCat 11 mOut mMid)
    let rSliceM : QRegister (m2 - m1) (16 - m1) := QRegister.block 0 (m2 - m1) ts.hBlock0SubM_le
    let FM2 := fun x ↦ affineScheduleFiber (m2 - m1) (2 ^ (m2 - m1) - 1) (R₁c * uSuperM) R₁c
      (rSliceM.extractIndex (tailShiftClockPerm ts x))
    XMeasCircuit.CleanRealizes v (rActLoc 16 11 mOut mMid 0 aRem mRem sRem)
      (rExtZeroDeferLocB wOuter wInner2 ko km m1 nDirtyLo sRem hkOut hkMid ts.hm1_le14 hDirty1)
      ((rCombHiInAct mOut mMid m1 ts.hm1_le16).embedUnitary (QubitisedWalk.qpeMuxUnitary FM2) *
        (rQPE.compose (rWinHiDeferInQPE m1 nDirtyLo ts.hm1_le16 hDirty1)).embedUnitary
          w.cWinM.eval)
      (tailShiftBlockedPart2SuperProg wOuter wInner2 ko km nDirtyLo sRem sUbM
        hkOut hkMid hDirty1 hsUbM ts v w pSuperM) := by
  intro mOut mMid aRem mRem rQPE R₁c rSliceM FM2
  have hWinM := cleanRealizes_winHiDefer_on_rExtZeroDefer wOuter wInner2 ko km m1 nDirtyLo sRem
    hkOut hkMid ts.hm1_le14 hDirty1 v w.cWinM w.count_m_toff
  dsimp only at hWinM
  have hSM := tailShiftPhaseMSuperDyn_cleanRealizes wOuter wInner2 ko km nDirtyLo sRem sUbM
    hkOut hkMid hDirty1 hsUbM ts v hCleanM
  dsimp only at hSM
  exact hWinM.seq hSM

end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.TailShiftThreeGear
end
