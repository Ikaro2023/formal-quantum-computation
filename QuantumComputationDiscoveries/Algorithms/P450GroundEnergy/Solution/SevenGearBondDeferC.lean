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

public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.SevenGearBondDeferB

/-!
# Seven-Gear Bond-Deferred Dihedral Engine — Part C (`SevenGearBondDeferC`)

Parametric `5`-coarse-gear (`G0..G4`, `mCut = 14..10`) + `M` (`mCut = 7`) + `F`
Bond-Deferred Tail-Shifted QPE circuit assembly (`genLocalCircProg`, `genTopCircProg`),
gate-count theorems (`genTopCircProg_count_toff`, `genTopCircProg_count_t_le`), active-space
unitary equivalence (`genActiveUnitary_eq`), and 7-gear clean-ancilla `wp` realization
(`genTopLevel_realizes`).

## References
- A. Luis and J. Peřina, *Phys. Rev. A* **54**, 4564 (1996), DOI: 10.1103/PhysRevA.54.4564.
- M. Möttönen et al., *Phys. Rev. Lett.* **93**, 130502 (2004), DOI: 10.1103/PhysRevLett.93.130502.
- R. Babbush et al., *Phys. Rev. X* **8**, 041015 (2018), DOI: 10.1103/PhysRevX.8.041015.
- J. Lee et al., *PRX Quantum* **2**, 030305 (2021), DOI: 10.1103/PRXQuantum.2.030305.
-/

@[expose] public section

namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.SevenGearBondDefer
open QuantumComputation.Specs QuantumComputation.Specs.P450

open Operator QProg Matrix HermitianMat Circuit Real QuantumComputation.Specs
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution
open QuantumComputation.Specs.P450 QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution
open BlockEncodingCore
open BlockEncodingCircuit TopIntegrationBridge
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.WalkQPEBridge hiding
  rActLoc rActLoc_disjoint_rScrLoc rCatInAct rCatLoc rQPEInAct rQPEInAct_disjoint_rWalkCatInAct
  rQPEInAnc rQPELoc rQPELoc_disjoint_rScrLoc rQPELoc_disjoint_rWalkCatLoc rScrLoc rScrUbLoc
  rWalkCatInAct rWalkCatLoc rWalkCatLoc_disjoint_rScrLoc
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.WalkQPEBridgeXMeas hiding
  image_rFullZeroLoc rFullZeroLoc
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.WalkQPEFlexBridge hiding
  cleanRealizesSet_of_rScrUbLoc cleanRealizes_rScrLoc_of_sub
open Cat11CompactPhase2Bridge
open DihedralWalkQPE BlockReflection ApproxIqft16 SineWindowFlexM
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.DihedralWalkQPE.MultiGearQPE (
  outRemWidth outZeroPrefixReg combARem combAncillas combQubits combWalkCatReg
  combWalkReflRegs combWalkReflCovers comb_hbScr16 CleanWalkRefl2 WalkRefl2ErrLe
  P450RefVarBound ReordSosHyp RealizesP450GroundQPE tensorWalkCat_smul_right approxPhaseGrad11Ray
  exactPhaseGrad11RayUnitary norm_phaseGrad11RayScalar exactPhaseGrad11RayUnitary_mulVec_zero
  approxPhaseGrad11Ray_count_toff approxPhaseGrad11Ray_count_t norm_approxPhaseGrad11Ray_sub_le)
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.TwoGearBox hiding
  m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11
open TailShiftBox TwoGearQPEPhase5
open TwoGearBondDefer
open TailShiftWindow46847
open TailShiftThreeGear
open scoped Matrix BigOperators Matrix.Norms.L2Operator

/-! ## Section 1: Relocated Coarse Stages (`G0..G4`), Computable Parts 2–3, & Generic Top Program -/

/-- Blocked `Stage G0` (`cCat`, `cWinPrefixAt d 14`, and `pLocG0` at `mCut = 14`). -/
def blockedPhaseG0Prog {Var : Type} (wOuter wInner2 ko km sRem sUbG0 : ℕ)
    (_hkOut : ko ≤ wOuter) (_hkMid : km ≤ wInner2) (hsUbG0 : sUbG0 ≤ sRem + 14) (_v : Var)
    (cCat : Circuit 11) (cWindow14 : Circuit (0 + 2))
    (pLocG0 : FGCircAt Var 2 wOuter wInner2 ko km sUbG0) : FGCircB Var wOuter wInner2 ko km sRem :=
  let rCat := rCatLoc 16 11 (mOutUB wOuter) (mMidUB wInner2) 0 (combARem wOuter wInner2 ko km)
    (midRemWidth wInner2 km) sRem
  let rWindow14 := (rQPELoc 16 11 (mOutUB wOuter) (mMidUB wInner2) 0 (combARem wOuter wInner2 ko km)
    (midRemWidth wInner2 km) sRem).compose (rWinHiDeferInQPE 14 0 (by decide) (Nat.zero_le _))
  .seq (.circuit (cCat.onRegister rCat))
    (.seq (.circuit (cWindow14.onRegister rWindow14))
      (pLocG0.onRegister
        (rGearDeferInB 2 14 wOuter wInner2 ko km 0 sRem sUbG0 (by decide) (Nat.zero_le _) hsUbG0)))

/-- Blocked `Stage G_{14-m}` (`cWinStep` then `pLocGear` at `mCut = m ∈ 10..13`). -/
def blockedPhaseStepProg {Var : Type} (m wOuter wInner2 ko km sRem sUb : ℕ)
    (_hkOut : ko ≤ wOuter) (_hkMid : km ≤ wInner2) (hm14 : m ≤ 14) (hsUb : sUb ≤ sRem + (m - 0))
    (_v : Var) (cWinStep : Circuit (0 + (16 - m)))
    (pLocGear : FGCircAt Var (16 - m) wOuter wInner2 ko km sUb) : FGCircB Var wOuter wInner2 ko km
      sRem :=
  let rWin := (rQPELoc 16 11 (mOutUB wOuter) (mMidUB wInner2) 0 (combARem wOuter wInner2 ko km)
    (midRemWidth wInner2 km) sRem).compose
    (rWinHiDeferInQPE m 0 (le_trans hm14 (by decide)) (Nat.zero_le _))
  .seq (.circuit (cWinStep.onRegister rWin))
    (pLocGear.onRegister
      (rGearDeferInB (16 - m) m wOuter wInner2 ko km 0 sRem sUb (by omega) (Nat.zero_le _) hsUb))

/-- Computable Part 2 (`wc.cWinLo, StageB, cIqft`) from `TwoGearWindowCirc`. -/
def twoGearBlockedPart2CircProg {Var : Type} (wOuter wInner2 ko km mLow nDirtyLo sRem : ℕ)
    (hkOut : ko ≤ wOuter) (hkMid : km ≤ wInner2) (hmLow1 : 1 ≤ mLow) (hmLow15 : mLow ≤ 15)
    (v : Var) (cIqft : Circuit 16) (wc : TwoGearWindowCirc mLow nDirtyLo)
    (pRefl2B : FGCircB Var wOuter wInner2 ko km sRem) : FGCircB Var wOuter wInner2 ko km sRem :=
  let rQPE := rQPELoc 16 11 (mOutUB wOuter) (mMidUB wInner2) 0 (combARem wOuter wInner2 ko km)
    (midRemWidth wInner2 km) sRem
  .seq (.circuit (wc.cWinLo.onRegister (rQPE.compose (rLoInQPE16 mLow (by omega)))))
    (.seq (twoGearPhaseBDyn wOuter wInner2 ko km mLow sRem hkOut hkMid hmLow1 hmLow15 v pRefl2B)
      (.circuit (cIqft.onRegister rQPE)))

/-- Computable Part 3 (`wc.cBond, wc.cWinLo, StageF, cIqft`) from `ThreeGearWindowCirc`. -/
def threeGearDeferBlockedPart3CircProg {Var : Type} (wOuter wInner2 ko km m2 m1 nDirtyLo sRem : ℕ)
    (hkOut : ko ≤ wOuter) (hkMid : km ≤ wInner2) (hm1_1 : 1 ≤ m1) (_hDirty : nDirtyLo ≤ m1 - 1)
    (v : Var) (cIqft : Circuit 16) (wc : ThreeGearWindowCirc m2 m1 nDirtyLo)
    (pRefl2F : FGCircB Var wOuter wInner2 ko km sRem) : FGCircB Var wOuter wInner2 ko km sRem :=
  let hm1_15 : m1 ≤ 15 := le_trans (le_trans wc.hm12 wc.hm2_14) (by decide)
  .seq (.circuit (wc.cBond.onRegister ((rQPELoc 16 11 (mOutUB wOuter) (mMidUB wInner2) 0
      (combARem wOuter wInner2 ko km) (midRemWidth wInner2 km) sRem).compose
      (rBondHiInQPE16 m1 hm1_1 hm1_15))))
    (twoGearBlockedPart2CircProg wOuter wInner2 ko km m1 nDirtyLo sRem hkOut hkMid hm1_1 hm1_15 v
      cIqft
      ⟨.identity, wc.cWinLo⟩ pRefl2F)

@[simp] theorem threeGearDeferBlockedPart3CircProg_toCirc {Var : Type}
    (wOuter wInner2 ko km M m2 m1 nDirtyLo sRem : ℕ) (hkOut : ko ≤ wOuter) (hkMid : km ≤ wInner2)
    (hm1_1 : 1 ≤ m1) (hDirty : nDirtyLo ≤ m1 - 1) (v : Var) (cIqft : Circuit 16)
    (w : ThreeGearBondDeferSpec M m2 m1 nDirtyLo) (pRefl2F : FGCircB Var wOuter wInner2 ko km
      sRem) :
    threeGearDeferBlockedPart3CircProg wOuter wInner2 ko km m2 m1 nDirtyLo sRem hkOut hkMid hm1_1
      hDirty
      v cIqft w.toCirc pRefl2F =
    threeGearDeferBlockedPart3Prog wOuter wInner2 ko km M m2 m1 nDirtyLo sRem hkOut hkMid hm1_1
      hDirty
      v cIqft w pRefl2F :=
  rfl

/-- Computable Blocked `Stage M` (`wc10.cWinM` then `tailShiftPhaseMSuperDyn`)
for arbitrary `ts`. -/
def blockedPart2CircProg {Var : Type} {M nStd kTail tShift : ℕ}
    (wOuter wInner2 ko km sRem sUbM : ℕ) (hkOut : ko ≤ wOuter) (hkMid : km ≤ wInner2)
    (hsUbM : sUbM ≤ sRem + (7 - 0)) (ts : TailShiftParams M 10 7 nStd kTail tShift) (v : Var)
    (wc10 : ThreeGearWindowCirc 10 7 0) (p128 : FGCircAt Var 3 wOuter wInner2 ko km sUbM) :
    FGCircB Var wOuter wInner2 ko km sRem :=
  .seq (.circuit (wc10.cWinM.onRegister ((rQPELoc 16 11 (mOutUB wOuter) (mMidUB wInner2) 0
      (combARem wOuter wInner2 ko km) (midRemWidth wInner2 km) sRem).compose
      (rWinHiDeferInQPE 7 0 (le_trans (le_trans wc10.hm12 wc10.hm2_14) (by decide))
        (Nat.zero_le _)))))
    (tailShiftPhaseMSuperDyn wOuter wInner2 ko km 0 sRem sUbM hkOut hkMid (Nat.zero_le _) hsUbM ts v
      p128)

@[simp] theorem blockedPart2CircProg_toCirc {Var : Type} {M nStd kTail tShift : ℕ}
    (wOuter wInner2 ko km sRem sUbM : ℕ) (hkOut : ko ≤ wOuter) (hkMid : km ≤ wInner2)
    (hsUbM : sUbM ≤ sRem + (7 - 0)) (ts : TailShiftParams M 10 7 nStd kTail tShift) (v : Var)
    (w10 : ThreeGearBondDeferSpec M 10 7 0) (p128 : FGCircAt Var 3 wOuter wInner2 ko km sUbM) :
    blockedPart2CircProg wOuter wInner2 ko km sRem sUbM hkOut hkMid hsUbM ts v w10.toCirc p128 =
      tailShiftBlockedPart2SuperProg wOuter wInner2 ko km 0 sRem sUbM hkOut hkMid (Nat.zero_le _)
        hsUbM
        ts v w10 p128 :=
  rfl

/-- Generic `5`-coarse-stage (`G0..G4`) + `Stage M` + `Stage F` local circuit on `combQubitsB`. -/
def genLocalCircProg {Var : Type} {M nStd kTail tShift : ℕ}
    (wOuter wInner2 ko km sRem sUbG0 sUbG1 sUbG2 sUbG3 sUbG4 sUbM : ℕ)
    (hkOut : ko ≤ wOuter) (hkMid : km ≤ wInner2)
    (hsUbG0 : sUbG0 ≤ sRem + 14) (hsUbG1 : sUbG1 ≤ sRem + (13 - 0))
    (hsUbG2 : sUbG2 ≤ sRem + (12 - 0)) (hsUbG3 : sUbG3 ≤ sRem + (11 - 0))
    (hsUbG4 : sUbG4 ≤ sRem + (10 - 0)) (hsUbM : sUbM ≤ sRem + (7 - 0))
    (d : TwoGearRegimeData) (wc10 : ThreeGearWindowCirc 10 7 0)
    (ts : TailShiftParams M 10 7 nStd kTail tShift) (v : Var)
    (cCat : Circuit 11) (cIqft : Circuit 16)
    (pLocG0 : FGCircAt Var 2 wOuter wInner2 ko km sUbG0)
    (pLocG1 : FGCircAt Var 3 wOuter wInner2 ko km sUbG1)
    (pLocG2 : FGCircAt Var 4 wOuter wInner2 ko km sUbG2)
    (pLocG3 : FGCircAt Var 5 wOuter wInner2 ko km sUbG3)
    (pLocG4 : FGCircAt Var 6 wOuter wInner2 ko km sUbG4)
    (pSuperM : FGCircAt Var 3 wOuter wInner2 ko km sUbM)
    (pRefl2F : FGCircB Var wOuter wInner2 ko km sRem) : FGCircB Var wOuter wInner2 ko km sRem :=
  p450FswapConjProg
    (rActLoc 16 11 (mOutUB wOuter) (mMidUB wInner2) 0 (combARem wOuter wInner2 ko km) (midRemWidth
      wInner2 km)
      sRem)
    (.seq (blockedPhaseG0Prog wOuter wInner2 ko km sRem sUbG0 hkOut hkMid hsUbG0 v cCat
        (cWinPrefixAt d 14) pLocG0)
      (.seq (blockedPhaseStepProg 13 wOuter wInner2 ko km sRem sUbG1 hkOut hkMid (by decide) hsUbG1
        v
          (cWinStepAt d 13) pLocG1)
        (.seq (blockedPhaseStepProg 12 wOuter wInner2 ko km sRem sUbG2 hkOut hkMid
          (by decide) hsUbG2 v
            (cWinStepAt d 12) pLocG2)
          (.seq (blockedPhaseStepProg 11 wOuter wInner2 ko km sRem sUbG3 hkOut hkMid
            (by decide) hsUbG3
              v (cWinStepAt d 11) pLocG3)
            (.seq (blockedPhaseStepProg 10 wOuter wInner2 ko km sRem sUbG4 hkOut hkMid (by decide)
                hsUbG4 v (cWinStepAt d 10) pLocG4)
              (.seq (blockedPart2CircProg wOuter wInner2 ko km sRem sUbM hkOut hkMid hsUbM ts v wc10
                  pSuperM)
                (threeGearDeferBlockedPart3CircProg wOuter wInner2 ko km 10 7 0 sRem hkOut hkMid
                  (by decide) (Nat.zero_le _) v cIqft wc10 pRefl2F)))))))

/-- Generic `5`-coarse-stage top-level dynamic circuit on `(rSys, rAnc)`. -/
def genTopCircProg {Var : Type} {n M nStd kTail tShift : ℕ}
    (wOuter wInner2 ko km sRem sUbG0 sUbG1 sUbG2 sUbG3 sUbG4 sUbM : ℕ)
    (hkOut : ko ≤ wOuter) (hkMid : km ≤ wInner2)
    (hsUbG0 : sUbG0 ≤ sRem + 14) (hsUbG1 : sUbG1 ≤ sRem + (13 - 0))
    (hsUbG2 : sUbG2 ≤ sRem + (12 - 0)) (hsUbG3 : sUbG3 ≤ sRem + (11 - 0))
    (hsUbG4 : sUbG4 ≤ sRem + (10 - 0)) (hsUbM : sUbM ≤ sRem + (7 - 0))
    (d : TwoGearRegimeData) (wc10 : ThreeGearWindowCirc 10 7 0)
    (ts : TailShiftParams M 10 7 nStd kTail tShift) (v : Var)
    (cCat : Circuit 11) (cIqft : Circuit 16)
    (pLocG0 : FGCircAt Var 2 wOuter wInner2 ko km sUbG0)
    (pLocG1 : FGCircAt Var 3 wOuter wInner2 ko km sUbG1)
    (pLocG2 : FGCircAt Var 4 wOuter wInner2 ko km sUbG2)
    (pLocG3 : FGCircAt Var 5 wOuter wInner2 ko km sUbG3)
    (pLocG4 : FGCircAt Var 6 wOuter wInner2 ko km sUbG4)
    (pSuperM : FGCircAt Var 3 wOuter wInner2 ko km sUbM)
    (pRefl2F : FGCircB Var wOuter wInner2 ko km sRem)
    (rSys : FGSysReg n) (rAnc : FGAncReg wOuter wInner2 ko km sRem n) : DynamicCircuit Var n :=
  CleanDyn.topProg
    (genLocalCircProg wOuter wInner2 ko km sRem sUbG0 sUbG1 sUbG2 sUbG3 sUbG4 sUbM
      hkOut hkMid hsUbG0 hsUbG1 hsUbG2 hsUbG3 hsUbG4 hsUbM d wc10 ts v cCat cIqft
      pLocG0 pLocG1 pLocG2 pLocG3 pLocG4 pSuperM pRefl2F)
    rSys rAnc

theorem cWinPrefix_steps_toff_zero (d : TwoGearRegimeData)
    (h10 : (cWinPrefixAt d 10).count .TOFF = 0) :
    (cWinPrefixAt d 14).count .TOFF = 0 ∧
      (cWinStepAt d 13).count .TOFF = 0 ∧
      (cWinStepAt d 12).count .TOFF = 0 ∧
      (cWinStepAt d 11).count .TOFF = 0 ∧
      (cWinStepAt d 10).count .TOFF = 0 := by
  have s10 := cWinStepAt_add_count d (m := 10) (by decide) .TOFF
  have s11 := cWinStepAt_add_count d (m := 11) (by decide) .TOFF
  have s12 := cWinStepAt_add_count d (m := 12) (by decide) .TOFF
  have s13 := cWinStepAt_add_count d (m := 13) (by decide) .TOFF
  simp only [Nat.reduceAdd] at s10 s11 s12 s13
  omega

theorem genTopCircProg_count_toff {Var : Type} {n M nStd kTail tShift : ℕ}
    (wOuter wInner2 ko km sRem sUbG0 sUbG1 sUbG2 sUbG3 sUbG4 sUbM : ℕ)
    (hkOut : ko ≤ wOuter) (hkMid : km ≤ wInner2)
    (hsUbG0 : sUbG0 ≤ sRem + 14) (hsUbG1 : sUbG1 ≤ sRem + (13 - 0))
    (hsUbG2 : sUbG2 ≤ sRem + (12 - 0)) (hsUbG3 : sUbG3 ≤ sRem + (11 - 0))
    (hsUbG4 : sUbG4 ≤ sRem + (10 - 0)) (hsUbM : sUbM ≤ sRem + (7 - 0))
    (d : TwoGearRegimeData) (wc10 : ThreeGearWindowCirc 10 7 0)
    (w10 : ThreeGearBondDeferSpec M 10 7 0) (hw10_circ : w10.toCirc = wc10)
    (hw10_c : w10.cWinC = cWinPrefixAt d 10)
    (ts : TailShiftParams M 10 7 nStd kTail tShift) (v : Var)
    {cCat : Circuit 11} (hCat : cCat.count .TOFF = 0)
    {cIqft : Circuit 16} (hIqft : cIqft.count .TOFF = 0)
    {pLocG0 : FGCircAt Var 2 wOuter wInner2 ko km sUbG0}
    {pLocG1 : FGCircAt Var 3 wOuter wInner2 ko km sUbG1}
    {pLocG2 : FGCircAt Var 4 wOuter wInner2 ko km sUbG2}
    {pLocG3 : FGCircAt Var 5 wOuter wInner2 ko km sUbG3}
    {pLocG4 : FGCircAt Var 6 wOuter wInner2 ko km sUbG4}
    {pSuperM : FGCircAt Var 3 wOuter wInner2 ko km sUbM}
    {pRefl2F : FGCircB Var wOuter wInner2 ko km sRem}
    (hG0 : pLocG0.count .TOFF = 0) (hG1 : pLocG1.count .TOFF = 0)
    (hG2 : pLocG2.count .TOFF = 0) (hG3 : pLocG3.count .TOFF = 0)
    (hG4 : pLocG4.count .TOFF = 0) (hM : pSuperM.count .TOFF = 0)
    (hF : pRefl2F.count .TOFF = 0)
    (rSys : FGSysReg n) (rAnc : FGAncReg wOuter wInner2 ko km sRem n) :
    (genTopCircProg wOuter wInner2 ko km sRem sUbG0 sUbG1 sUbG2 sUbG3 sUbG4 sUbM
      hkOut hkMid hsUbG0 hsUbG1 hsUbG2 hsUbG3 hsUbG4 hsUbM d wc10 ts v cCat cIqft
      pLocG0 pLocG1 pLocG2 pLocG3 pLocG4 pSuperM pRefl2F rSys rAnc).count .TOFF = 0 := by
  refine CleanDyn.count_topProg_toff _ rSys rAnc ?_
  dsimp only [genLocalCircProg]
  rw [← hw10_circ, blockedPart2CircProg_toCirc,
    threeGearDeferBlockedPart3CircProg_toCirc (M := M)]
  obtain ⟨hw14, hs13, hs12, hs11, hs10⟩ :=
    cWinPrefix_steps_toff_zero d (hw10_c ▸ w10.count_c_toff)
  have h2 := tailShiftPhaseMSuperDyn_count_toff wOuter wInner2 ko km 0 sRem sUbM hkOut hkMid
    (Nat.zero_le _) hsUbM ts v hM
  have h3 := affineDihedralRefl2Dyn_count_toff 16 11 (mOutUB wOuter) (mMidUB wInner2) 0 sRem v
    (combWalkReflRegs 11 wOuter wInner2 ko km hkOut hkMid) 7 (2 ^ 7 - 1) (by decide) (by decide)
    (hbScr_phaseB wOuter wInner2 ko km 7 sRem (by decide)) pRefl2F hF
  have hg0 : (pLocG0.onRegister (rGearDeferInB 2 14 wOuter wInner2 ko km 0 sRem sUbG0 (by decide)
      (Nat.zero_le _) hsUbG0)).count .TOFF = 0 := (DynamicCircuit.count_onRegister _ _ _).trans hG0
  have hg1 : (pLocG1.onRegister (rGearDeferInB 3 13 wOuter wInner2 ko km 0 sRem sUbG1 (by decide)
      (Nat.zero_le _) hsUbG1)).count .TOFF = 0 := (DynamicCircuit.count_onRegister _ _ _).trans hG1
  have hg2 : (pLocG2.onRegister (rGearDeferInB 4 12 wOuter wInner2 ko km 0 sRem sUbG2 (by decide)
      (Nat.zero_le _) hsUbG2)).count .TOFF = 0 := (DynamicCircuit.count_onRegister _ _ _).trans hG2
  have hg3 : (pLocG3.onRegister (rGearDeferInB 5 11 wOuter wInner2 ko km 0 sRem sUbG3 (by decide)
      (Nat.zero_le _) hsUbG3)).count .TOFF = 0 := (DynamicCircuit.count_onRegister _ _ _).trans hG3
  have hg4 : (pLocG4.onRegister (rGearDeferInB 6 10 wOuter wInner2 ko km 0 sRem sUbG4 (by decide)
      (Nat.zero_le _) hsUbG4)).count .TOFF = 0 := (DynamicCircuit.count_onRegister _ _ _).trans hG4
  refine count_p450FswapConjProg_toff _ ?_
  simp only [blockedPhaseG0Prog, blockedPhaseStepProg, tailShiftBlockedPart2SuperProg,
    threeGearDeferBlockedPart3Prog, twoGearBlockedPart2Prog, twoGearPhaseBDyn,
    DynamicCircuit.count, Circuit.count_onRegister, hCat, hIqft, hw14, hs13, hs12, hs11, hs10,
    w10.count_m_toff, w10.count_bond_toff, w10.base.count_lo_toff,
    hg0, hg1, hg2, hg3, hg4, h2, h3, add_zero]

theorem genTopCircProg_count_t_le {Var : Type} {n M nStd kTail tShift : ℕ}
    (wOuter wInner2 ko km sRem sUbG0 sUbG1 sUbG2 sUbG3 sUbG4 sUbM : ℕ)
    (tCat tWin tIqft tG0 tG1 tG2 tG3 tG4 tM t1 : ℕ)
    (hkOut : ko ≤ wOuter) (hkMid : km ≤ wInner2)
    (hsUbG0 : sUbG0 ≤ sRem + 14) (hsUbG1 : sUbG1 ≤ sRem + (13 - 0))
    (hsUbG2 : sUbG2 ≤ sRem + (12 - 0)) (hsUbG3 : sUbG3 ≤ sRem + (11 - 0))
    (hsUbG4 : sUbG4 ≤ sRem + (10 - 0)) (hsUbM : sUbM ≤ sRem + (7 - 0))
    (d : TwoGearRegimeData) (wc10 : ThreeGearWindowCirc 10 7 0)
    (w10 : ThreeGearBondDeferSpec M 10 7 0) (hw10_circ : w10.toCirc = wc10)
    (hw10_c : w10.cWinC = cWinPrefixAt d 10)
    (hw10_t : w10.base.cWinHi.count .T + w10.base.cWinLo.count .T ≤ tWin)
    (ts : TailShiftParams M 10 7 nStd kTail tShift) (v : Var)
    {cCat : Circuit 11} (hCat : cCat.count .T ≤ tCat)
    {cIqft : Circuit 16} (hIqft : cIqft.count .T ≤ tIqft)
    {pLocG0 : FGCircAt Var 2 wOuter wInner2 ko km sUbG0}
    {pLocG1 : FGCircAt Var 3 wOuter wInner2 ko km sUbG1}
    {pLocG2 : FGCircAt Var 4 wOuter wInner2 ko km sUbG2}
    {pLocG3 : FGCircAt Var 5 wOuter wInner2 ko km sUbG3}
    {pLocG4 : FGCircAt Var 6 wOuter wInner2 ko km sUbG4}
    {pSuperM : FGCircAt Var 3 wOuter wInner2 ko km sUbM}
    {pRefl2F : FGCircB Var wOuter wInner2 ko km sRem}
    (hG0 : pLocG0.count .T ≤ tG0) (hG1 : pLocG1.count .T ≤ tG1)
    (hG2 : pLocG2.count .T ≤ tG2) (hG3 : pLocG3.count .T ≤ tG3)
    (hG4 : pLocG4.count .T ≤ tG4) (hM : pSuperM.count .T ≤ tM)
    (hF : pRefl2F.count .T ≤ t1)
    (rSys : FGSysReg n) (rAnc : FGAncReg wOuter wInner2 ko km sRem n) :
    (genTopCircProg wOuter wInner2 ko km sRem sUbG0 sUbG1 sUbG2 sUbG3 sUbG4 sUbM
      hkOut hkMid hsUbG0 hsUbG1 hsUbG2 hsUbG3 hsUbG4 hsUbM d wc10 ts v cCat cIqft
      pLocG0 pLocG1 pLocG2 pLocG3 pLocG4 pSuperM pRefl2F rSys rAnc).count .T ≤
      tCat + tWin + tIqft + tG0 + tG1 + tG2 + tG3 + tG4 + tShift +
        walkCtrlTCount 3 7 (combARem wOuter wInner2 ko km) tM +
        walkCtrlTCount 7 127 (combARem wOuter wInner2 ko km) t1 := by
  refine (CleanDyn.count_topProg_t_le _ rSys rAnc).trans ?_
  dsimp only [genLocalCircProg]
  rw [← hw10_circ, blockedPart2CircProg_toCirc,
    threeGearDeferBlockedPart3CircProg_toCirc (M := M)]
  have s10 := cWinStepAt_add_count d (m := 10) (by decide) .T
  have s11 := cWinStepAt_add_count d (m := 11) (by decide) .T
  have s12 := cWinStepAt_add_count d (m := 12) (by decide) .T
  have s13 := cWinStepAt_add_count d (m := 13) (by decide) .T
  simp only [Nat.reduceAdd] at s10 s11 s12 s13
  have hWinSplit := w10.count_split_t
  rw [hw10_c] at hWinSplit
  have hc2 := tailShiftPhaseMSuperDyn_count_t_le wOuter wInner2 ko km 0 sRem sUbM hkOut hkMid
    (Nat.zero_le _) hsUbM ts v pSuperM
  have hc3 := affineDihedralRefl2Dyn_count_t 16 11 (mOutUB wOuter) (mMidUB wInner2) 0 sRem v
    (combWalkReflRegs 11 wOuter wInner2 ko km hkOut hkMid) 7 (2 ^ 7 - 1) (by decide) (by decide)
    (by decide) (hbScr_phaseB wOuter wInner2 ko km 7 sRem (by decide)) pRefl2F
  have hmM := walkCtrlTCount_mono 3 7 (combARem wOuter wInner2 ko km) hM
  have hm1 := walkCtrlTCount_mono 7 127 (combARem wOuter wInner2 ko km) hF
  simp only [Nat.reducePow, Nat.reduceSub] at hc2 hc3
  simp only [count_p450FswapConjProg_t, blockedPhaseG0Prog, blockedPhaseStepProg,
    tailShiftBlockedPart2SuperProg, threeGearDeferBlockedPart3Prog, twoGearBlockedPart2Prog,
    twoGearPhaseBDyn, DynamicCircuit.count, DynamicCircuit.count_onRegister,
    Circuit.count_onRegister, hc3, Nat.reducePow, Nat.reduceSub]
  omega

/-! ## Section 2: Active-Space Unitary Equivalence & 7-Stage Clean-Ancilla `wp` Realization -/

/-- Combined `6`-bit coarse fiber `FG4 * (FG3 * (FG2 * (FG1 * FG0)))` on `10..15`. -/
noncomputable def genCoarseFiber (mOut mMid : ℕ)
    (FG0 : Fin (2 ^ 2) → FGWalkU mOut mMid)
    (FG1 : Fin (2 ^ 3) → FGWalkU mOut mMid)
    (FG2 : Fin (2 ^ 4) → FGWalkU mOut mMid)
    (FG3 : Fin (2 ^ 5) → FGWalkU mOut mMid)
    (FG4 : Fin (2 ^ 6) → FGWalkU mOut mMid) (xc : Fin (2 ^ 6)) : FGWalkU mOut mMid :=
  FG4 xc *
    (FG3 ((QRegister.block 1 5 (by decide) : QRegister 5 6).extractIndex xc) *
      (FG2 ((QRegister.block 2 4 (by decide) : QRegister 4 6).extractIndex xc) *
        (FG1 ((QRegister.block 3 3 (by decide) : QRegister 3 6).extractIndex xc) *
          FG0 ((QRegister.block 4 2 (by decide) : QRegister 2 6).extractIndex xc))))

/-- Combined `9`-bit `(7..15)` fiber `Stage M * genCoarseFiber` for arbitrary `ts`. -/
noncomputable def genCombinedHiFiber {M nStd kTail tShift : ℕ} (mOut mMid : ℕ)
    (ts : TailShiftParams M 10 7 nStd kTail tShift)
    (FG0 : Fin (2 ^ 2) → FGWalkU mOut mMid)
    (FG1 : Fin (2 ^ 3) → FGWalkU mOut mMid)
    (FG2 : Fin (2 ^ 4) → FGWalkU mOut mMid)
    (FG3 : Fin (2 ^ 5) → FGWalkU mOut mMid)
    (FG4 : Fin (2 ^ 6) → FGWalkU mOut mMid)
    (uSuperM : FGWalkU mOut mMid) : Fin (2 ^ 9) → FGWalkU mOut mMid :=
  let R₁c := QubitisedWalk.reflInUnitary (inAllWalkCat 11 mOut mMid)
  let rSliceC : QRegister 6 9 := QRegister.block 3 6 (by decide)
  let rSliceM : QRegister 3 9 := QRegister.block 0 3 (by decide)
  fun x ↦
    affineScheduleFiber 3 7 (R₁c * uSuperM) R₁c (rSliceM.extractIndex (tailShiftClockPerm ts x)) *
      genCoarseFiber mOut mMid FG0 FG1 FG2 FG3 FG4 (rSliceC.extractIndex x)

/-- Factored active-space blocked implementation unitary of the generic `5`-coarse-stage engine. -/
noncomputable def genBlockedImplUnitary {M nStd kTail tShift : ℕ} (mOut mMid : ℕ)
    (ts : TailShiftParams M 10 7 nStd kTail tShift)
    (uCat : Unitary (2 ^ 11)) (uWinHi : Unitary (2 ^ (0 + 10))) (uWinLo : Unitary (2 ^ 7))
    (uIqft : Unitary (2 ^ 16))
    (FG0 : Fin (2 ^ 2) → FGWalkU mOut mMid)
    (FG1 : Fin (2 ^ 3) → FGWalkU mOut mMid)
    (FG2 : Fin (2 ^ 4) → FGWalkU mOut mMid)
    (FG3 : Fin (2 ^ 5) → FGWalkU mOut mMid)
    (FG4 : Fin (2 ^ 6) → FGWalkU mOut mMid)
    (uSuperM uRefl2F : FGWalkU mOut mMid) : Unitary (2 ^ actWidth 16 11 mOut mMid) :=
  let rCat := rCatInAct 16 11 mOut mMid
  let rQPE := rQPEInAct 16 11 mOut mMid
  let rCombFull := rQPE.concat (rWalkCatInAct 16 11 mOut mMid)
    (rQPEInAct_disjoint_rWalkCatInAct 16 11 mOut mMid)
  let R₁c := QubitisedWalk.reflInUnitary (inAllWalkCat 11 mOut mMid)
  let FB := affineScheduleFiber (bQPE := 16) 7 127 (R₁c * uRefl2F) R₁c
  let FA := genCombinedHiFiber mOut mMid ts FG0 FG1 FG2 FG3 FG4 uSuperM
  rQPE.embedUnitary uIqft *
    (rCombFull.embedUnitary (QubitisedWalk.qpeMuxUnitary FB) *
      (rCombHiInAct mOut mMid 7 (by decide)).embedUnitary (QubitisedWalk.qpeMuxUnitary FA)) *
    ((rQPE.compose (rLoInQPE16 7 (by decide))).embedUnitary uWinLo *
      (rQPE.compose (rWinHiInQPE 7 0 (by decide) (by decide) (Nat.zero_le _))).embedUnitary
        uWinHi) *
    rCat.embedUnitary uCat

theorem mergeGearWinStep (d : TwoGearRegimeData) {m : ℕ} (hm15 : m < 15)
    (mOut mMid : ℕ) (FPrev : Fin (2 ^ (16 - (m + 1))) → FGWalkU mOut mMid)
    (FCur : Fin (2 ^ (16 - m)) → FGWalkU mOut mMid) :
    let rQPE := rQPEInAct 16 11 mOut mMid
    let rHi1 : QRegister (16 - (m + 1)) (16 - m) := QRegister.block ((m + 1) - m) (16 - (m + 1))
      (by omega)
    let uPrev := (rCombSubInAct mOut mMid (m + 1) (16 - (m + 1)) (by omega)).embedUnitary
      (QubitisedWalk.qpeMuxUnitary FPrev)
    let uCur := (rCombSubInAct mOut mMid m (16 - m) (by omega)).embedUnitary
      (QubitisedWalk.qpeMuxUnitary FCur)
    let uWinPrev := (rQPE.compose (rWinHiDeferInQPE (m + 1) 0 (by omega)
      (Nat.zero_le _))).embedUnitary (cWinPrefixAt d (m + 1)).eval
    let uWinStep := (rQPE.compose (rWinHiDeferInQPE m 0 (by omega) (Nat.zero_le _))).embedUnitary
      (cWinStepAt d m (by omega)).eval
    let uMerged := (rCombSubInAct mOut mMid m (16 - m) (by omega)).embedUnitary
      (QubitisedWalk.qpeMuxUnitary (fun x : Fin (2 ^ (16 - m)) ↦ FCur x * FPrev (rHi1.extractIndex
        x)))
    let uWinMerged := (rQPE.compose (rWinHiDeferInQPE m 0 (by omega) (Nat.zero_le _))).embedUnitary
      (cWinPrefixAt d m).eval
    (uCur * uWinStep) * (uPrev * uWinPrev) = uMerged * uWinMerged := by
  intro rQPE rHi1 uPrev uCur uWinPrev uWinStep uMerged uWinMerged
  have hComm : uWinStep * uPrev = uPrev * uWinStep := comm_cWinStepAt_mux d hm15 mOut mMid FPrev
  have hLift : uPrev = (rCombSubInAct mOut mMid m (16 - m) (by omega)).embedUnitary
      (QubitisedWalk.qpeMuxUnitary (fun x : Fin (2 ^ (16 - m)) ↦ FPrev (rHi1.extractIndex x))) :=
    embed_rCombSubInAct_eq_rCombHiInAct mOut mMid m (m + 1) (16 - (m + 1)) (by omega) (by omega)
      FPrev
  have hMuxMerge : uCur * uPrev = uMerged :=
    Eq.trans (congrArg (uCur * ·) hLift)
      (Eq.trans (QRegister.embedUnitary_mul _ _ _).symm
        (congrArg _ (QubitisedWalk.qpeMuxUnitary_mul _ _).symm))
  have hWinMerge : uWinStep * uWinPrev = uWinMerged := by
    dsimp only [uWinStep, uWinPrev, uWinMerged]
    rw [QRegister.embedUnitary_compose, QRegister.embedUnitary_compose,
      QRegister.embedUnitary_compose, ← QRegister.embedUnitary_mul,
      cWinStepAt_mul_prefix_eval d hm15]
  calc (uCur * uWinStep) * (uPrev * uWinPrev)
      = uCur * (uWinStep * uPrev) * uWinPrev := by simp only [mul_assoc]
    _ = (uCur * uPrev) * (uWinStep * uWinPrev) := by
        rw [hComm]
        simp only [mul_assoc]
    _ = uMerged * uWinMerged := by rw [hMuxMerge, hWinMerge]

theorem extract_compose_block_hi {a b c : ℕ} (s1 s2 : ℕ)
    (h1 : s1 + b ≤ c) (h2 : s2 + a ≤ b)
    (heq1 : s1 + b = c := by omega) (heq2 : s2 + a = b := by omega) (x : Fin (2 ^ c)) :
    (QRegister.block s2 a h2 : QRegister a b).extractIndex
      ((QRegister.block s1 b h1 : QRegister b c).extractIndex x) =
      (QRegister.block (s1 + s2) a (by omega) : QRegister a c).extractIndex x := by
  apply Fin.ext
  rw [qpeBlockHi_extract_val b a s2 h2 heq2, qpeBlockHi_extract_val c b s1 h1 heq1,
    qpeBlockHi_extract_val c a (s1 + s2) _ (by omega), Nat.div_div_eq_div_mul, ← pow_add]

theorem genActiveUnitary_eq {M nStd kTail tShift : ℕ} (mOut mMid : ℕ)
    (d : TwoGearRegimeData) (w10 : ThreeGearBondDeferSpec M 10 7 0)
    (hw10_c : w10.cWinC = cWinPrefixAt d 10)
    (ts : TailShiftParams M 10 7 nStd kTail tShift)
    (cCat : Circuit 11) (cIqft : Circuit 16)
    (FG0 : Fin (2 ^ 2) → FGWalkU mOut mMid)
    (FG1 : Fin (2 ^ 3) → FGWalkU mOut mMid)
    (FG2 : Fin (2 ^ 4) → FGWalkU mOut mMid)
    (FG3 : Fin (2 ^ 5) → FGWalkU mOut mMid)
    (FG4 : Fin (2 ^ 6) → FGWalkU mOut mMid)
    (uSuperM uRefl2F : FGWalkU mOut mMid) :
    let rCat := rCatInAct 16 11 mOut mMid
    let rQPE := rQPEInAct 16 11 mOut mMid
    let rCombFull := rQPE.concat (rWalkCatInAct 16 11 mOut mMid)
      (rQPEInAct_disjoint_rWalkCatInAct 16 11 mOut mMid)
    let R₁c := QubitisedWalk.reflInUnitary (inAllWalkCat 11 mOut mMid)
    let uG0 := (rCombSubInAct mOut mMid 14 2 (by decide)).embedUnitary (QubitisedWalk.qpeMuxUnitary
      FG0)
    let uG1 := (rCombSubInAct mOut mMid 13 3 (by decide)).embedUnitary (QubitisedWalk.qpeMuxUnitary
      FG1)
    let uG2 := (rCombSubInAct mOut mMid 12 4 (by decide)).embedUnitary (QubitisedWalk.qpeMuxUnitary
      FG2)
    let uG3 := (rCombSubInAct mOut mMid 11 5 (by decide)).embedUnitary (QubitisedWalk.qpeMuxUnitary
      FG3)
    let uG4 := (rCombSubInAct mOut mMid 10 6 (by decide)).embedUnitary (QubitisedWalk.qpeMuxUnitary
      FG4)
    let rSliceM : QRegister 3 9 := QRegister.block 0 3 (by decide)
    let FM2 := fun x ↦ affineScheduleFiber 3 7 (R₁c * uSuperM) R₁c
      (rSliceM.extractIndex (tailShiftClockPerm ts x))
    let uM := (rCombHiInAct mOut mMid 7 (by decide)).embedUnitary (QubitisedWalk.qpeMuxUnitary FM2)
    let uF := rCombFull.embedUnitary (QubitisedWalk.qpeMuxUnitary
      (affineScheduleFiber (bQPE := 16) 7 127 (R₁c * uRefl2F) R₁c))
    let uWindow14 := (rQPE.compose (rWinHiDeferInQPE 14 0 (by decide) (Nat.zero_le _))).embedUnitary
      (cWinPrefixAt d 14).eval
    let uWinS13 := (rQPE.compose (rWinHiDeferInQPE 13 0 (by decide) (Nat.zero_le _))).embedUnitary
      (cWinStepAt d 13).eval
    let uWinS12 := (rQPE.compose (rWinHiDeferInQPE 12 0 (by decide) (Nat.zero_le _))).embedUnitary
      (cWinStepAt d 12).eval
    let uWinS11 := (rQPE.compose (rWinHiDeferInQPE 11 0 (by decide) (Nat.zero_le _))).embedUnitary
      (cWinStepAt d 11).eval
    let uWinS10 := (rQPE.compose (rWinHiDeferInQPE 10 0 (by decide) (Nat.zero_le _))).embedUnitary
      (cWinStepAt d 10).eval
    let uWinM := (rQPE.compose (rWinHiDeferInQPE 7 0 (by decide) (Nat.zero_le _))).embedUnitary
      w10.cWinM.eval
    let uBond := (rQPE.compose (rBondHiInQPE16 7 (by decide) (by decide))).embedUnitary
      w10.cBond.eval
    let uWinLo := (rQPE.compose (rLoInQPE16 7 (by decide))).embedUnitary w10.base.cWinLo.eval
    (rQPE.embedUnitary cIqft.eval * uF * uWinLo * uBond) * (uM * uWinM) *
        (uG4 * uWinS10) * (uG3 * uWinS11) * (uG2 * uWinS12) * (uG1 * uWinS13) *
        (uG0 * uWindow14 * rCat.embedUnitary cCat.eval) =
      genBlockedImplUnitary mOut mMid ts cCat.eval w10.base.cWinHi.eval w10.base.cWinLo.eval
        cIqft.eval FG0 FG1 FG2 FG3 FG4 uSuperM uRefl2F := by
  intro rCat rQPE rCombFull R₁c uG0 uG1 uG2 uG3 uG4 rSliceM FM2 uM uF
    uWindow14 uWinS13 uWinS12 uWinS11 uWinS10 uWinM uBond uWinLo
  have hm13 := mergeGearWinStep d (m := 13) (by decide) mOut mMid FG0 FG1
  let F01 : Fin (2 ^ 3) → FGWalkU mOut mMid :=
    fun x ↦ FG1 x * FG0 ((QRegister.block 1 2 (by decide) : QRegister 2 3).extractIndex x)
  have hm12 := mergeGearWinStep d (m := 12) (by decide) mOut mMid F01 FG2
  let F012 : Fin (2 ^ 4) → FGWalkU mOut mMid :=
    fun x ↦ FG2 x * F01 ((QRegister.block 1 3 (by decide) : QRegister 3 4).extractIndex x)
  have hm11 := mergeGearWinStep d (m := 11) (by decide) mOut mMid F012 FG3
  let F0123 : Fin (2 ^ 5) → FGWalkU mOut mMid :=
    fun x ↦ FG3 x * F012 ((QRegister.block 1 4 (by decide) : QRegister 4 5).extractIndex x)
  have hm10 := mergeGearWinStep d (m := 10) (by decide) mOut mMid F0123 FG4
  let FC := genCoarseFiber mOut mMid FG0 FG1 FG2 FG3 FG4
  have hFC_eq :
      (fun x : Fin (2 ^ (16 - 10)) ↦
        FG4 x * F0123 ((QRegister.block (10 + 1 - 10) (16 - (10 + 1))
          (by omega)).extractIndex x)) = FC := by
    funext xc
    dsimp only [F0123, F012, F01, FC, genCoarseFiber]
    rw [extract_compose_block_hi 1 1 (by decide) (by decide),
      extract_compose_block_hi 2 1 (by decide) (by decide),
      extract_compose_block_hi 3 1 (by decide) (by decide)]
  dsimp only at hm13 hm12 hm11 hm10
  let uC := (rCombSubInAct mOut mMid 10 6 (by decide)).embedUnitary (QubitisedWalk.qpeMuxUnitary FC)
  let uWinC10 := (rQPE.compose (rWinHiDeferInQPE 10 0 (by decide) (Nat.zero_le _))).embedUnitary
    w10.cWinC.eval
  have hCoarseAll :
      (uG4 * uWinS10) * ((uG3 * uWinS11) * ((uG2 * uWinS12) * ((uG1 * uWinS13) * (uG0 *
        uWindow14)))) =
        uC * uWinC10 := by
    rw [hm13, hm12, hm11, hm10, hFC_eq, ← hw10_c]
  have hWinM_C : uWinM * uC = uC * uWinM := w10.comm_winM_phaseC mOut mMid FC
  have hCLift : uC = (rCombHiInAct mOut mMid 7 (by decide)).embedUnitary
      (QubitisedWalk.qpeMuxUnitary (fun x : Fin (2 ^ 9) ↦
        FC ((QRegister.block 3 6 (by decide) : QRegister 6 9).extractIndex x))) :=
    embed_rCombSubInAct_eq_rCombHiInAct mOut mMid 7 10 6 (by decide) (by decide) FC
  let FA := genCombinedHiFiber mOut mMid ts FG0 FG1 FG2 FG3 FG4 uSuperM
  let uMC := (rCombHiInAct mOut mMid 7 (by decide)).embedUnitary (QubitisedWalk.qpeMuxUnitary FA)
  have hMC_eq : uM * uC = uMC :=
    Eq.trans (congrArg (uM * ·) hCLift)
      (Eq.trans (QRegister.embedUnitary_mul _ _ _).symm
        (congrArg _ (QubitisedWalk.qpeMuxUnitary_mul _ _).symm))
  have hBond_MC : uBond * uMC = uMC * uBond :=
    w10.comm_bond_mux 9 mOut mMid (rHiInQPE16 7 (by decide)) (fun j ↦ by simp [rHiInQPE16]) FA
  have hLo_MC : uWinLo * uMC = uMC * uWinLo :=
    embedUnitary_comm_of_disjoint_tg _ _ (rLoInAct_disjoint_rCombHiInAct mOut mMid 7 (by decide))
      _ _
  have hSplitQPE : uBond * uWinM * uWinC10 =
      (rQPE.compose (rWinHiInQPE 7 0 (by decide) (by decide) (Nat.zero_le _))).embedUnitary
        w10.base.cWinHi.eval := by
    dsimp only [uBond, uWinM, uWinC10]
    rw [QRegister.embedUnitary_compose, QRegister.embedUnitary_compose,
      QRegister.embedUnitary_compose, ← QRegister.embedUnitary_mul, ← QRegister.embedUnitary_mul,
      w10.eval_split_eq, ← QRegister.embedUnitary_compose]
  dsimp only [genBlockedImplUnitary]
  let uIqft := rQPE.embedUnitary cIqft.eval
  let uCat := rCat.embedUnitary cCat.eval
  change (uIqft * uF * uWinLo * uBond) * (uM * uWinM) * (uG4 * uWinS10) * (uG3 * uWinS11) *
    (uG2 * uWinS12) * (uG1 * uWinS13) * (uG0 * uWindow14 * uCat) = _
  calc (uIqft * uF * uWinLo * uBond) * (uM * uWinM) * (uG4 * uWinS10) * (uG3 * uWinS11) *
          (uG2 * uWinS12) * (uG1 * uWinS13) * (uG0 * uWindow14 * uCat)
      = uIqft * uF * uWinLo * uBond * uM * uWinM *
          ((uG4 * uWinS10) * ((uG3 * uWinS11) * ((uG2 * uWinS12) *
            ((uG1 * uWinS13) * (uG0 * uWindow14))))) * uCat := by simp only [mul_assoc]
    _ = uIqft * uF * uWinLo * uBond * uM * (uWinM * uC) * uWinC10 * uCat := by
        rw [hCoarseAll]
        simp only [mul_assoc]
    _ = uIqft * uF * uWinLo * uBond * (uM * uC) * uWinM * uWinC10 * uCat := by
        rw [hWinM_C]
        simp only [mul_assoc]
    _ = uIqft * uF * uWinLo * (uBond * uMC) * uWinM * uWinC10 * uCat := by
        rw [hMC_eq]
        simp only [mul_assoc]
    _ = uIqft * uF * (uWinLo * uMC) * (uBond * uWinM * uWinC10) * uCat := by
        rw [hBond_MC]
        simp only [mul_assoc]
    _ = _ := by
        rw [hLo_MC, hSplitQPE]
        dsimp only [uIqft, uCat, uMC, FA, uF, uWinLo, rQPE, rCombFull, R₁c, rCat,
          Nat.reducePow, Nat.reduceSub]
        simp only [mul_assoc]

/-- Clean local realization of a `b`-bit QPE mux `QubitisedWalk.qpeMuxUnitary FG` at scratch bound
`sUb`. -/
abbrev CleanGearMuxAt {Var : Type} [Fintype Var] [DecidableEq Var]
    (b wOuter wInner2 ko km sUb : ℕ) (hkOut : ko ≤ wOuter) (hkMid : km ≤ wInner2) (v : Var)
    (FG : Fin (2 ^ b) → FGWalkCatU wOuter wInner2) (pLoc : FGCircAt Var b wOuter wInner2 ko km
      sUb) : Prop :=
  XMeasCircuit.CleanRealizes v
    ((rQPELoc b 11 (mOutUB wOuter) (mMidUB wInner2) 0 (combARem wOuter wInner2 ko km) (midRemWidth
      wInner2 km)
        sUb).concat
      (rWalkCatLoc b 11 (mOutUB wOuter) (mMidUB wInner2) 0 (combARem wOuter wInner2 ko km)
        (midRemWidth wInner2 km) sUb)
      (rQPELoc_disjoint_rWalkCatLoc b 11 (mOutUB wOuter) (mMidUB wInner2) 0 (combARem wOuter wInner2
        ko km)
        (midRemWidth wInner2 km) sUb))
    (rFullZeroLoc b 11 (mOutUB wOuter) (mMidUB wInner2) 0 (combARem wOuter wInner2 ko km)
      (midRemWidth wInner2 km) sUb
      (liftOutMidZeroToAnc (mOutUB wOuter) (mMidUB wInner2) (outZeroPrefixReg wOuter ko hkOut)
        (midZeroPrefixReg wInner2 km hkMid)))
    (QubitisedWalk.qpeMuxUnitary FG) pLoc

theorem blockedPhaseG0Prog_cleanRealizes {Var : Type} [Fintype Var] [DecidableEq Var]
    (wOuter wInner2 ko km sRem sUbG0 : ℕ) (hkOut : ko ≤ wOuter) (hkMid : km ≤ wInner2)
    (hsUbG0 : sUbG0 ≤ sRem + 14) (v : Var)
    (cCat : Circuit 11) (hCatToff : cCat.count .TOFF = 0)
    (cWindow14 : Circuit (0 + 2)) (hWinToff : cWindow14.count .TOFF = 0)
    {FG0 : Fin (2 ^ 2) → FGWalkCatU wOuter wInner2} {pLocG0 : FGCircAt Var 2 wOuter wInner2 ko km
      sUbG0}
    (hLoc : CleanGearMuxAt 2 wOuter wInner2 ko km sUbG0 hkOut hkMid v FG0 pLocG0) :
    let mOut := mOutUB wOuter
    let mMid := mMidUB wInner2
    let aRem := combARem wOuter wInner2 ko km
    let mRem := midRemWidth wInner2 km
    XMeasCircuit.CleanRealizes v (rActLoc 16 11 mOut mMid 0 aRem mRem sRem)
      (rExtZeroDeferLocB wOuter wInner2 ko km 14 0 sRem hkOut hkMid (by decide) (Nat.zero_le _))
      ((rCombSubInAct mOut mMid 14 2 (by decide)).embedUnitary (QubitisedWalk.qpeMuxUnitary FG0) *
        ((rQPEInAct 16 11 mOut mMid).compose
          (rWinHiDeferInQPE 14 0 (by decide) (Nat.zero_le _))).embedUnitary cWindow14.eval *
        (rCatInAct 16 11 mOut mMid).embedUnitary cCat.eval)
      (blockedPhaseG0Prog wOuter wInner2 ko km sRem sUbG0 hkOut hkMid hsUbG0 v cCat cWindow14
        pLocG0) := by
  intro mOut mMid aRem mRem
  have hCat := cleanRealizes_subcircuit_rExtZeroB wOuter wInner2 ko km 15 0 sRem hkOut hkMid
    (by decide) (by decide) (Nat.zero_le _) v (rCatInAct 16 11 mOut mMid)
    (fun j ↦ Or.inr (by
      have hj := j.isLt
      simp only [rCatInAct, QRegister.block_apply_val]
      dsimp only [mOut, mMid, walkCatWidth, walkWidth]
      exact ⟨by omega, Or.inl (by omega)⟩))
    cCat hCatToff
  dsimp only at hCat
  have hrCat : (rActLoc 16 11 mOut mMid 0 aRem mRem sRem).compose (rCatInAct 16 11 mOut mMid) =
      rCatLoc 16 11 mOut mMid 0 aRem mRem sRem :=
    BlockEncodingCircuit.qreg_ext fun _ ↦ rfl
  rw [hrCat] at hCat
  have hWin := cleanRealizes_winHiDefer_on_rExtZeroDefer wOuter wInner2 ko km 14 0 sRem hkOut hkMid
    (by decide) (Nat.zero_le _) v cWindow14 hWinToff
  have hRel := cleanRealizes_gearDefer_relocated 2 14 wOuter wInner2 ko km 0 sRem sUbG0 hkOut hkMid
    (by decide) (by decide) (Nat.zero_le _) hsUbG0 v hLoc
  dsimp only at hWin hRel
  refine cleanRealizes_of_eq (hCat.seq (hWin.seq hRel)) ?_
  dsimp only [mOut, mMid]

theorem blockedPhaseStepProg_cleanRealizes {Var : Type} [Fintype Var] [DecidableEq Var]
    (m wOuter wInner2 ko km sRem sUb : ℕ) (hkOut : ko ≤ wOuter) (hkMid : km ≤ wInner2)
    (hm14 : m ≤ 14) (hsUb : sUb ≤ sRem + (m - 0)) (v : Var)
    (cWinStep : Circuit (0 + (16 - m))) (hWinToff : cWinStep.count .TOFF = 0)
    {FG : Fin (2 ^ (16 - m)) → FGWalkCatU wOuter wInner2}
    {pLocGear : FGCircAt Var (16 - m) wOuter wInner2 ko km sUb}
    (hLoc : CleanGearMuxAt (16 - m) wOuter wInner2 ko km sUb hkOut hkMid v FG pLocGear) :
    let mOut := mOutUB wOuter
    let mMid := mMidUB wInner2
    let aRem := combARem wOuter wInner2 ko km
    let mRem := midRemWidth wInner2 km
    XMeasCircuit.CleanRealizes v (rActLoc 16 11 mOut mMid 0 aRem mRem sRem)
      (rExtZeroDeferLocB wOuter wInner2 ko km m 0 sRem hkOut hkMid hm14 (Nat.zero_le _))
      ((rCombSubInAct mOut mMid m (16 - m) (by omega)).embedUnitary (QubitisedWalk.qpeMuxUnitary FG)
        *
        ((rQPEInAct 16 11 mOut mMid).compose
          (rWinHiDeferInQPE m 0 (le_trans hm14 (by decide)) (Nat.zero_le _))).embedUnitary
            cWinStep.eval)
      (blockedPhaseStepProg m wOuter wInner2 ko km sRem sUb hkOut hkMid hm14 hsUb v cWinStep
        pLocGear) := by
  intro mOut mMid aRem mRem
  have hWin := cleanRealizes_winHiDefer_on_rExtZeroDefer wOuter wInner2 ko km m 0 sRem hkOut hkMid
    hm14 (Nat.zero_le _) v cWinStep hWinToff
  have hRel := cleanRealizes_gearDefer_relocated (16 - m) m wOuter wInner2 ko km 0 sRem sUb hkOut
    hkMid
    hm14 (by omega) (Nat.zero_le _) hsUb v hLoc
  dsimp only at hWin hRel
  exact hWin.seq hRel

theorem chainCleanWp_lift {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)]
    (wOuter wInner2 ko km m1 m2 sRem : ℕ) (hkOut : ko ≤ wOuter) (hkMid : km ≤ wInner2)
    (hm12 : m1 ≤ m2) (hm2_14 : m2 ≤ 14) (v : Var)
    (rSys : FGSysReg n) (rAnc : FGAncReg wOuter wInner2 ko km sRem n) (hdisj : rSys.DisjointWires
      rAnc)
    {UA UPost : Unitary (2 ^ actWidth 16 11 (mOutUB wOuter) (mMidUB wInner2))}
    {PA : DynamicCircuit Var n} {ΘPost : Store Var → Observable (Fin (2 ^ n))}
    {M_obs : Observable (Fin (2 ^ n))}
    (honA : CleanDyn.CleanRealizes v
      ((rSys.concat rAnc hdisj).compose
        (rActLoc 16 11 (mOutUB wOuter) (mMidUB wInner2) 0 (combARem wOuter wInner2 ko km)
          (midRemWidth wInner2 km) sRem))
      ((rSys.concat rAnc hdisj).compose
        (rExtZeroDeferLocB wOuter wInner2 ko km m2 0 sRem hkOut hkMid hm2_14 (Nat.zero_le _)))
      UA PA)
    (hPost : restrictAssertionToZeroAncilla ΘPost
        ((rSys.concat rAnc hdisj).compose
          (rExtZeroDeferLocB wOuter wInner2 ko km m1 0 sRem hkOut hkMid (le_trans hm12 hm2_14)
            (Nat.zero_le _))) =
      restrictAssertionToZeroAncilla
        (qcWpQAssign (((rSys.concat rAnc hdisj).compose
            (rActLoc 16 11 (mOutUB wOuter) (mMidUB wInner2) 0 (combARem wOuter wInner2 ko km)
              (midRemWidth wInner2 km) sRem)).embedUnitary UPost) (fun _ ↦ M_obs))
        ((rSys.concat rAnc hdisj).compose
          (rExtZeroDeferLocB wOuter wInner2 ko km m1 0 sRem hkOut hkMid (le_trans hm12 hm2_14)
            (Nat.zero_le _)))) :
    restrictAssertionToZeroAncilla (wp PA.compile ΘPost)
        ((rSys.concat rAnc hdisj).compose
          (rExtZeroDeferLocB wOuter wInner2 ko km m2 0 sRem hkOut hkMid hm2_14 (Nat.zero_le _))) =
      restrictAssertionToZeroAncilla
        (qcWpQAssign (((rSys.concat rAnc hdisj).compose
            (rActLoc 16 11 (mOutUB wOuter) (mMidUB wInner2) 0 (combARem wOuter wInner2 ko km)
              (midRemWidth wInner2 km) sRem)).embedUnitary (UPost * UA)) (fun _ ↦ M_obs))
        ((rSys.concat rAnc hdisj).compose
          (rExtZeroDeferLocB wOuter wInner2 ko km m2 0 sRem hkOut hkMid hm2_14 (Nat.zero_le
            _))) := by
  rw [← honA.2.2.2 ΘPost,
    rExtZeroDefer0_wp_lift wOuter wInner2 ko km m1 m2 sRem hkOut hkMid hm12 hm2_14 rSys rAnc hdisj
      hPost,
    honA.2.2.2 _, honA.2.2.1 _ (fun _ _ ↦ rfl), qc_wp_qAssign_comp,
    ← QRegister.embedUnitary_mul]

theorem genTopLevel_realizes {Var : Type} [Fintype Var] [DecidableEq Var]
    {n M nStd kTail tShift : ℕ} [NeZero (2 ^ n)]
    (wOuter wInner2 ko km sRem sUbG0 sUbG1 sUbG2 sUbG3 sUbG4 sUbM : ℕ)
    (hkOut : ko ≤ wOuter) (hkMid : km ≤ wInner2)
    (hsUbG0 : sUbG0 ≤ sRem + 14) (hsUbG1 : sUbG1 ≤ sRem + (13 - 0))
    (hsUbG2 : sUbG2 ≤ sRem + (12 - 0)) (hsUbG3 : sUbG3 ≤ sRem + (11 - 0))
    (hsUbG4 : sUbG4 ≤ sRem + (10 - 0)) (hsUbM : sUbM ≤ sRem + (7 - 0))
    (d : TwoGearRegimeData) (wc10 : ThreeGearWindowCirc 10 7 0)
    (w10 : ThreeGearBondDeferSpec M 10 7 0) (hw10_circ : w10.toCirc = wc10)
    (hw10_c : w10.cWinC = cWinPrefixAt d 10)
    (ts : TailShiftParams M 10 7 nStd kTail tShift) (v : Var)
    (cCat : Circuit 11) (hCatToff : cCat.count .TOFF = 0)
    (cIqft : Circuit 16) (hIqftToff : cIqft.count .TOFF = 0)
    {FG0 : Fin (2 ^ 2) → FGWalkCatU wOuter wInner2}
    {FG1 : Fin (2 ^ 3) → FGWalkCatU wOuter wInner2}
    {FG2 : Fin (2 ^ 4) → FGWalkCatU wOuter wInner2}
    {FG3 : Fin (2 ^ 5) → FGWalkCatU wOuter wInner2}
    {FG4 : Fin (2 ^ 6) → FGWalkCatU wOuter wInner2}
    {uSuperM uRefl2F : FGWalkCatU wOuter wInner2}
    {pLocG0 : FGCircAt Var 2 wOuter wInner2 ko km sUbG0}
    {pLocG1 : FGCircAt Var 3 wOuter wInner2 ko km sUbG1}
    {pLocG2 : FGCircAt Var 4 wOuter wInner2 ko km sUbG2}
    {pLocG3 : FGCircAt Var 5 wOuter wInner2 ko km sUbG3}
    {pLocG4 : FGCircAt Var 6 wOuter wInner2 ko km sUbG4}
    {pSuperM : FGCircAt Var 3 wOuter wInner2 ko km sUbM}
    {pRefl2F : FGCircB Var wOuter wInner2 ko km sRem}
    (hLoc0 : CleanGearMuxAt 2 wOuter wInner2 ko km sUbG0 hkOut hkMid v FG0 pLocG0)
    (hLoc1 : CleanGearMuxAt 3 wOuter wInner2 ko km sUbG1 hkOut hkMid v FG1 pLocG1)
    (hLoc2 : CleanGearMuxAt 4 wOuter wInner2 ko km sUbG2 hkOut hkMid v FG2 pLocG2)
    (hLoc3 : CleanGearMuxAt 5 wOuter wInner2 ko km sUbG3 hkOut hkMid v FG3 pLocG3)
    (hLoc4 : CleanGearMuxAt 6 wOuter wInner2 ko km sUbG4 hkOut hkMid v FG4 pLocG4)
    (hM : CleanWalkRefl2At 3 wOuter wInner2 ko km 0 sUbM hkOut hkMid v uSuperM pSuperM)
    (hCleanF : CleanWalkRefl2 wOuter wInner2 ko km 0 sRem hkOut hkMid v uRefl2F pRefl2F)
    (rSys : FGSysReg n) (rAnc : FGAncReg wOuter wInner2 ko km sRem n) (hdisj : rSys.DisjointWires
      rAnc) :
    let mOut := mOutUB wOuter
    let mMid := mMidUB wInner2
    let aRem := combARem wOuter wInner2 ko km
    let mRem := midRemWidth wInner2 km
    let sys : QRegister (2 * 58) (actWidth 16 11 mOut mMid) :=
      .block 0 (2 * 58) (sys_le_actWidth mOut mMid)
    let wBlk := genBlockedImplUnitary mOut mMid ts cCat.eval w10.base.cWinHi.eval
      w10.base.cWinLo.eval cIqft.eval FG0 FG1 FG2 FG3 FG4 uSuperM uRefl2F
    RealizesUnitaryFromBasisOutcomesAndZeroWorkspace rSys Finset.univ rAnc hdisj
      ((rActLoc 16 11 mOut mMid 0 aRem mRem sRem).embedUnitary
        (sys.embedUnitary p450FswapUninterleave.eval⁻¹ * wBlk *
          sys.embedUnitary p450FswapUninterleave.eval))
      (genTopCircProg wOuter wInner2 ko km sRem sUbG0 sUbG1 sUbG2 sUbG3 sUbG4 sUbM
        hkOut hkMid hsUbG0 hsUbG1 hsUbG2 hsUbG3 hsUbG4 hsUbM d wc10 ts v cCat cIqft
        pLocG0 pLocG1 pLocG2 pLocG3 pLocG4 pSuperM pRefl2F rSys rAnc).compile := by
  intro mOut mMid aRem mRem sys wBlk
  rw [qc_realizesUnitaryFromBasisOutcomesAndZeroWorkspace_iff, genTopCircProg,
    CleanDyn.topProg_of_disjoint _ rSys rAnc hdisj]
  let rAct := rActLoc 16 11 mOut mMid 0 aRem mRem sRem
  have hConj (P : FGCircB Var wOuter wInner2 ko km sRem) :
      p450FswapConjProg rAct P =
        .seq (.circuit (p450FswapUninterleave.onRegister (rAct.compose sys)))
          (.seq P (.circuit (p450FswapUninterleave.inverse.onRegister (rAct.compose sys)))) := rfl
  have hfToff : p450FswapUninterleave.count .TOFF = 0 := p450FswapUninterleave_count_toff
  have hfiToff : p450FswapUninterleave.inverse.count .TOFF = 0 :=
    fswapUninterleave_inverse_count_toff 58
  have hfiEval : p450FswapUninterleave.inverse.eval = p450FswapUninterleave.eval⁻¹ :=
    Circuit.eval_inverse p450FswapUninterleave
  generalize p450FswapUninterleave.inverse = cFswapInv at hConj hfiToff hfiEval
  generalize p450FswapUninterleave = cFswap at hConj hfToff hfiEval ⊢
  obtain ⟨hw14, hs13, hs12, hs11, hs10⟩ :=
    cWinPrefix_steps_toff_zero d (hw10_c ▸ w10.count_c_toff)
  let rFull := rFullZeroLocB wOuter wInner2 ko km sRem hkOut hkMid
  let rExt7 := rExtZeroDeferLocB wOuter wInner2 ko km 7 0 sRem hkOut hkMid (by decide) (Nat.zero_le
    _)
  let rExt14 := rExtZeroDeferLocB wOuter wInner2 ko km 14 0 sRem hkOut hkMid (by decide)
    (Nat.zero_le _)
  have hSysDisj : ∀ j, (sys j).val < 2 * 58 := fun j ↦ by
    have hj := j.isLt
    simp only [sys, QRegister.block_apply_val, zero_add]
    omega
  have hf1 := cleanRealizes_subcircuit_rExtZeroB wOuter wInner2 ko km 15 0 sRem hkOut hkMid
    (by decide) (by decide) (Nat.zero_le _) v sys (fun j ↦ Or.inl (hSysDisj j))
    cFswap hfToff
  have hG0 := blockedPhaseG0Prog_cleanRealizes wOuter wInner2 ko km sRem sUbG0 hkOut hkMid hsUbG0 v
    cCat hCatToff (cWinPrefixAt d 14) hw14 hLoc0
  have hG1 := blockedPhaseStepProg_cleanRealizes 13 wOuter wInner2 ko km sRem sUbG1 hkOut hkMid
    (by decide) hsUbG1 v (cWinStepAt d 13) hs13 hLoc1
  have hG2 := blockedPhaseStepProg_cleanRealizes 12 wOuter wInner2 ko km sRem sUbG2 hkOut hkMid
    (by decide) hsUbG2 v (cWinStepAt d 12) hs12 hLoc2
  have hG3 := blockedPhaseStepProg_cleanRealizes 11 wOuter wInner2 ko km sRem sUbG3 hkOut hkMid
    (by decide) hsUbG3 v (cWinStepAt d 11) hs11 hLoc3
  have hG4 := blockedPhaseStepProg_cleanRealizes 10 wOuter wInner2 ko km sRem sUbG4 hkOut hkMid
    (by decide) hsUbG4 v (cWinStepAt d 10) hs10 hLoc4
  have hPart2 := tailShiftBlockedPart2SuperProg_cleanRealizes wOuter wInner2 ko km 0 sRem sUbM hkOut
    hkMid
    (Nat.zero_le _) hsUbM ts v w10 hM
  have hf3 := tgCleanRealizes_subcircuit 16 11 mOut mMid 0 aRem mRem sRem v
    (liftOutMidZeroToAnc mOut mMid (outZeroPrefixReg wOuter ko hkOut) (midZeroPrefixReg wInner2 km
      hkMid))
    sys (fun j ↦ Or.inl (hSysDisj j)) cFswapInv hfiToff
  rw [hfiEval] at hf3
  have hPart3 := threeGearDeferBlockedPart3Prog_cleanRealizes wOuter wInner2 ko km M 10 7 0 sRem
    hkOut hkMid (by decide) (Nat.zero_le _) v cIqft hIqftToff w10 hCleanF
  dsimp only at hf1 hG0 hG1 hG2 hG3 hG4 hPart2 hf3 hPart3
  have h0Full : CleanDyn.CleanRealizes v rAct rExt14 _ _ := hf1.seq hG0
  have h3Full : CleanDyn.CleanRealizes v rAct rFull _ _ := hPart3.seq hf3
  let combined := rSys.concat rAnc hdisj
  let P₀ := (DynamicCircuit.seq (.circuit (cFswap.onRegister (rAct.compose sys)))
    (blockedPhaseG0Prog wOuter wInner2 ko km sRem sUbG0 hkOut hkMid hsUbG0 v cCat (cWinPrefixAt d
      14)
      pLocG0)).onRegister combined
  let P₁ := (blockedPhaseStepProg 13 wOuter wInner2 ko km sRem sUbG1 hkOut hkMid (by decide) hsUbG1
    v
    (cWinStepAt d 13) pLocG1).onRegister combined
  let P₂ := (blockedPhaseStepProg 12 wOuter wInner2 ko km sRem sUbG2 hkOut hkMid (by decide) hsUbG2
    v
    (cWinStepAt d 12) pLocG2).onRegister combined
  let P₃ := (blockedPhaseStepProg 11 wOuter wInner2 ko km sRem sUbG3 hkOut hkMid (by decide) hsUbG3
    v
    (cWinStepAt d 11) pLocG3).onRegister combined
  let P₄ := (blockedPhaseStepProg 10 wOuter wInner2 ko km sRem sUbG4 hkOut hkMid (by decide) hsUbG4
    v
    (cWinStepAt d 10) pLocG4).onRegister combined
  let PM := (tailShiftBlockedPart2SuperProg wOuter wInner2 ko km 0 sRem sUbM hkOut hkMid
    (Nat.zero_le _)
    hsUbM ts v w10 pSuperM).onRegister combined
  let PF := (DynamicCircuit.seq (threeGearDeferBlockedPart3Prog wOuter wInner2 ko km M 10 7 0 sRem
    hkOut hkMid (by decide) (Nat.zero_le _) v cIqft w10 pRefl2F)
    (.circuit (cFswapInv.onRegister (rAct.compose sys)))).onRegister combined
  have hon0 : CleanDyn.CleanRealizes v (combined.compose rAct) _ _ P₀ :=
    h0Full.onRegister combined
  have hon1 : CleanDyn.CleanRealizes v (combined.compose rAct) _ _ P₁ :=
    hG1.onRegister combined
  have hon2 : CleanDyn.CleanRealizes v (combined.compose rAct) _ _ P₂ :=
    hG2.onRegister combined
  have hon3 : CleanDyn.CleanRealizes v (combined.compose rAct) _ _ P₃ :=
    hG3.onRegister combined
  have hon4 : CleanDyn.CleanRealizes v (combined.compose rAct) _ _ P₄ :=
    hG4.onRegister combined
  have honM : CleanDyn.CleanRealizes v (combined.compose rAct) _ _ PM :=
    hPart2.onRegister combined
  have honF : CleanDyn.CleanRealizes v (combined.compose rAct) _ _ PF :=
    h3Full.onRegister combined
  let rExt7_emb := combined.compose rExt7
  let rExt14_emb := combined.compose rExt14
  let rBor7 := rBorrowLocB wOuter wInner2 ko km 8 0 sRem (by decide) (by decide) (Nat.zero_le _)
  let rFull_emb := combined.compose rFull
  let rBor7_emb := combined.compose rBor7
  have hdisj_fb7 : rFull_emb.DisjointWires rBor7_emb :=
    QRegister.disjoint_iff.mpr fun i j hij ↦
      (rFullZeroLocB_disjoint_rBorrowLocB wOuter wInner2 ko km 8 0 sRem hkOut hkMid
        (by decide) (by decide) (Nat.zero_le _)).ne i j (combined.wires.injective hij)
  have hExt7_eq_fb7 : rExt7_emb = rFull_emb.concat rBor7_emb hdisj_fb7 := by
    apply BlockEncodingCircuit.qreg_ext
    intro idx
    rcases finSumFinEquiv.surjective idx with ⟨ifull | ibor, rfl⟩
    · simp [rExt7_emb, rFull_emb, rExt7, rFull, rExtZeroDeferLocB, rExtZeroLocB,
        finSumFinEquiv_apply_left, QRegister.concat_apply_left]
    · simp [rExt7_emb, rBor7_emb, rExt7, rBor7, rExtZeroDeferLocB, rExtZeroLocB,
        finSumFinEquiv_apply_right, QRegister.concat_apply_right]
  have hsub : rExt14_emb.image ⊆ rAnc.image :=
    rExtZeroLocB_emb_subset_rAnc wOuter wInner2 ko km 15 0 sRem hkOut hkMid
      (by decide) (by decide) (Nat.zero_le _) rSys rAnc hdisj
  intro M_obs
  apply le_of_eq
  rw [tgRestrictZero_basisUniv_absorb (Var := Var) (rSys := rSys) hsub (qcWpQAssign _ _),
    tgRestrictZero_basisUniv_absorb (Var := Var) (rSys := rSys) hsub (wp _ _)]
  have hwp_eq :
      wp ((genLocalCircProg wOuter wInner2 ko km sRem sUbG0 sUbG1 sUbG2 sUbG3 sUbG4 sUbM
          hkOut hkMid hsUbG0 hsUbG1 hsUbG2 hsUbG3 hsUbG4 hsUbM d wc10 ts v cCat cIqft
          pLocG0 pLocG1 pLocG2 pLocG3 pLocG4 pSuperM pRefl2F).onRegister combined).compile
        (fun _ ↦ M_obs) =
      wp P₀.compile (wp P₁.compile (wp P₂.compile (wp P₃.compile
        (wp P₄.compile (wp PM.compile (wp PF.compile (fun _ ↦ M_obs))))))) := by
    dsimp only [genLocalCircProg]
    rw [hConj, ← hw10_circ, blockedPart2CircProg_toCirc,
      threeGearDeferBlockedPart3CircProg_toCirc (M := M)]
    dsimp only [P₀, P₁, P₂, P₃, P₄, PM, PF, rAct, sys, mOut, mMid, aRem, mRem]
    simp only [DynamicCircuit.onRegister_seq, DynamicCircuit.compile_seq, wp_qSeq]
  rw [hwp_eq]
  have hPF_e7 :=
    (congrArg (restrictAssertionToZeroAncilla (wp PF.compile (fun _ ↦ M_obs))) hExt7_eq_fb7)
      |>.trans (restrictAssertionToZeroAncilla_concat _ rFull_emb rBor7_emb hdisj_fb7)
      |>.trans (congrArg (restrictAssertionToZeroAncilla · rBor7_emb)
        (honF.2.2.1 (fun _ ↦ M_obs) (fun _ _ ↦ rfl)))
      |>.trans (restrictAssertionToZeroAncilla_concat _ rFull_emb rBor7_emb hdisj_fb7).symm
      |>.trans (congrArg (restrictAssertionToZeroAncilla _) hExt7_eq_fb7.symm)
  have hMF_e7 := chainCleanWp_lift wOuter wInner2 ko km 7 7 sRem hkOut hkMid le_rfl (by decide) v
    rSys rAnc hdisj honM hPF_e7
  have h4_e10 := chainCleanWp_lift wOuter wInner2 ko km 7 10 sRem hkOut hkMid (by decide)
    (by decide) v
    rSys rAnc hdisj hon4 hMF_e7
  have h3_e11 := chainCleanWp_lift wOuter wInner2 ko km 10 11 sRem hkOut hkMid (by decide)
    (by decide) v
    rSys rAnc hdisj hon3 h4_e10
  have h2_e12 := chainCleanWp_lift wOuter wInner2 ko km 11 12 sRem hkOut hkMid (by decide)
    (by decide) v
    rSys rAnc hdisj hon2 h3_e11
  have h1_e13 := chainCleanWp_lift wOuter wInner2 ko km 12 13 sRem hkOut hkMid (by decide)
    (by decide) v
    rSys rAnc hdisj hon1 h2_e12
  have h0_e14 := chainCleanWp_lift wOuter wInner2 ko km 13 14 sRem hkOut hkMid (by decide)
    (by decide) v
    rSys rAnc hdisj hon0 h1_e13
  have hstep :
      restrictAssertionToZeroAncilla
          (wp P₀.compile (wp P₁.compile (wp P₂.compile (wp P₃.compile
            (wp P₄.compile (wp PM.compile (wp PF.compile (fun _ ↦ M_obs))))))))
          rExt14_emb =
        restrictAssertionToZeroAncilla
          (qcWpQAssign (combined.embedUnitary (rAct.embedUnitary
            (sys.embedUnitary cFswap.eval⁻¹ * wBlk *
              sys.embedUnitary cFswap.eval))) (fun _ ↦ M_obs))
          rExt14_emb := by
    dsimp only [combined, rAct, mOut, mMid, aRem, mRem, rExt14_emb, rExt14] at h0_e14 ⊢
    rw [h0_e14, QRegister.embedUnitary_compose (rSys.concat rAnc hdisj)
      (rActLoc 16 11 (mOutUB wOuter) (mMidUB wInner2) 0 (combARem wOuter wInner2 ko km)
        (midRemWidth wInner2 km) sRem)]
    refine congrArg (fun u ↦ restrictAssertionToZeroAncilla
      (qcWpQAssign ((rSys.concat rAnc hdisj).embedUnitary
        ((rActLoc 16 11 (mOutUB wOuter) (mMidUB wInner2) 0 (combARem wOuter wInner2 ko km)
          (midRemWidth wInner2 km) sRem).embedUnitary u)) (fun _ ↦ M_obs)) _) ?_
    have hActEq := genActiveUnitary_eq mOut mMid d w10 hw10_c ts cCat cIqft
      FG0 FG1 FG2 FG3 FG4 uSuperM uRefl2F
    dsimp only at hActEq
    dsimp only [wBlk, sys, mOut, mMid, Nat.reducePow, Nat.reduceSub] at hActEq ⊢
    rw [← hActEq]
    simp only [mul_assoc]
  dsimp only [combined, rAct] at hstep ⊢
  rw [hstep]

theorem ts_qpeAffinePerm_fold {M nStd kTail tShift : ℕ}
    (ts : TailShiftParams M 10 7 nStd kTail tShift) :
    (∀ q : Fin (2 ^ 6), q.val ≤ nStd → (qpeAffinePerm 6 6 nStd q).val < 63) ∧
      (∀ q : Fin (2 ^ 6), q.val = nStd + 1 → (qpeAffinePerm 6 6 nStd q).val = 63) := by
  refine ⟨fun q hq ↦ ?_, fun q hq ↦ ?_⟩
  · rw [qpeAffinePerm_self_val (by decide)]
    exact ts.hFoldStd q hq
  · rw [qpeAffinePerm_self_val (by decide), hq]
    exact ts.hFoldTop

/-- Invariant-subspace coarse fiber approximation on `xc.val ≤ nStd + 1` against
`tailFusedScheduleFiber nStd (R₁ * W ^ 1024) (R₁ * W ^ kTail) R₁`. -/
def CoarseGearInvRel (wOuter wInner2 nStd kTail : ℕ) (uB : Unitary (2 ^ nUB wOuter wInner2))
    (FG0 : Fin (2 ^ 2) → FGWalkCatU wOuter wInner2) (FG1 : Fin (2 ^ 3) → FGWalkCatU wOuter wInner2)
    (FG2 : Fin (2 ^ 4) → FGWalkCatU wOuter wInner2) (FG3 : Fin (2 ^ 5) → FGWalkCatU wOuter wInner2)
    (FG4 : Fin (2 ^ 6) → FGWalkCatU wOuter wInner2) (δCoarse : ℝ) : Prop :=
  ∃ P_C : FGInvPred (mOutUB wOuter) (mMidUB wInner2),
    WalkSubspaceClosed wOuter wInner2 uB P_C ∧
    ∀ xc : Fin (2 ^ 6), xc.val ≤ nStd + 1 →
      let mOut := mOutUB wOuter
      let mMid := mMidUB wInner2
      let R₁ := QubitisedWalk.reflInUnitary (rAllInWalk mOut mMid)
      let R₂ := QubitisedWalk.reflPulledUnitary (rMidInWalk mOut mMid) uB
      let W := R₁ * R₂
      InvCatRel P_C (CircuitModular.phaseGradientLowFactor 11 3)
        (genCoarseFiber mOut mMid FG0 FG1 FG2 FG3 FG4 xc)
        (tailFusedScheduleFiber nStd (R₁ * W ^ 1024) (R₁ * W ^ kTail) R₁ xc) δCoarse

/-- Collision-free explicit-estimator energy-measurement predicate (`rfl` to
`MeasuresLowEnergiesTS`). -/
abbrev MeasuresLowEnergiesFG {k m : ℕ} (H : Operator (2 ^ k)) (η : ℕ) (Δ ε : ℝ)
    (estimate : Fin (2 ^ m) → ℝ) (W : Unitary (2 ^ (k + m))) : Prop :=
  MeasuresLowEnergiesTS H η Δ ε estimate W

/-- Collision-free explicit-estimator + zero-workspace QPE realization predicate (`rfl` to
`RealizesP450GroundQPETS`). -/
noncomputable abbrev RealizesP450GroundQPEFG {Var : Type} [Fintype Var] [DecidableEq Var]
    {n m : ℕ} [NeZero (2 ^ n)] (rSys : QRegister systemQubits_local n) (rAnc : QRegister m n)
    (hdisj : rSys.DisjointWires rAnc) (estimate : Fin (2 ^ m) → ℝ)
    (prog : DynamicCircuit Var n) : Prop :=
  RealizesP450GroundQPETS rSys rAnc hdisj estimate prog

/-- Explicit ancilla energy estimator on `combAncillasB` (`rfl` to `p450TailShiftEst`). -/
noncomputable abbrev p450SevenGearEst (wOuter wInner2 ko km sRem : ℕ) :
    Fin (2 ^ combAncillasB wOuter wInner2 ko km sRem) → ℝ :=
  p450TailShiftEst wOuter wInner2 ko km sRem

end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.SevenGearBondDefer

end
