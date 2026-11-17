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
public import QuantumComputationDiscoveries.Algorithms.Grover.Solution.BaselineRouter
import QuantumComputationDiscoveries.Algorithms.Grover.Solution.PulseM1MultiPulseQHL
import QuantumComputationDiscoveries.Algorithms.Grover.Solution.PulseM1Grover1Step
import QuantumComputationDiscoveries.Algorithms.Grover.Solution.GroverM1PulseTable
import QuantumComputationDiscoveries.Algorithms.Grover.Solution.GroverM1PulsePt1
import QuantumComputationDiscoveries.Algorithms.Grover.Solution.GroverM1PulsePt2
import QuantumComputationDiscoveries.Algorithms.Grover.Solution.GroverM1PulsePt2Sub12
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.Interval.Finset.SuccPred
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import QuantumComputation.Algorithms.Grover.Amplitude
import QuantumComputation.Algorithms.Grover.EarlyStoppingAnalysis
import QuantumComputation.Algorithms.Grover.Operators
import QuantumComputation.Circuits.DynamicCircuit
import QuantumComputation.Maths.Trigonometry
import QuantumComputation.Maths.Tsum
import QuantumComputation.QuantumHoareLogic.CleanAncilla
import QuantumComputation.QuantumHoareLogic.ResourceCounting.CostBounds
import QuantumComputation.QuantumHoareLogic.ResourceCounting.Loops
import QuantumComputation.QuantumHoareLogic.ResourceCounting.PowerLawCost
import QuantumComputation.QuantumHoareLogic.Semantics
import QuantumComputation.QuantumHoareLogic.WP
import QuantumComputation.Registers.Reset

/-!
# Standalone Zero-Cold 39-Stage `m = 1` Multi-pulse Conveyor Companion
-/
@[expose] public section
namespace QuantumComputation.Specs.GroverFindAll
open scoped NNRat
/-- Supported `m = 1` grid cells (`10 / 10` cells `k ∈ {2..1024}`). -/
def isGroverM1PulseCell (m k : ℕ) : Bool :=
  (m == 1) && (
    (k == 2) || (k == 4) || (k == 8) || (k == 16) || (k == 32) ||
    (k == 64) || (k == 128) || (k == 256) || (k == 512) || (k == 1024)
  )
/-- Certified relative cost `ℚ≥0` across all `10 / 10` `m = 1` grid cells. -/
def relCostGroverM1Pulse (m k : ℕ) : ℚ≥0 :=
  if (m == 1 && k == 2) then (23729247939 / 31250000000)
  else if (m == 1 && k == 4) then (179936242757 / 250000000000)
  else if (m == 1 && k == 8) then (693944177707 / 1000000000000)
  else if (m == 1 && k == 16) then (135807791521 / 200000000000)
  else if (m == 1 && k == 32) then (26885301129 / 40000000000)
  else if (m == 1 && k == 64) then (1325132303543193 / 2000000000000000)
  else if (m == 1 && k == 128) then (6564251612151231 / 10000000000000000)
  else if (m == 1 && k == 256) then (409036472074287 / 625000000000000)
  else if (m == 1 && k == 512) then (261102099301103 / 400000000000000)
  else if (m == 1 && k == 1024) then (3256773370679057 / 5000000000000000)
  else 1
/-- Cellwise cost profile for the standalone 39-stage `m = 1` Multi-pulse conveyor (`n₀ =
  1152`). -/
def groverM1PulseProfile : FindAllCostProfile where
  validCell := isGroverM1PulseCell
  relCost := relCostGroverM1Pulse
  n0 _ _ := 1152
end QuantumComputation.Specs.GroverFindAll
end
namespace QuantumComputation.Specs.GroverFindAll
open Operator Matrix Real QProg QProg.Notation ResourceCounting
open scoped Matrix ComplexOrder MatrixOrder NNReal NNRat ENNReal
open scoped InnerProductSpace QHLExpectation
section InternalBundle
/-- Stage router across all `2 ≤ r ≤ 1024` for the refined `m = 1` Multi-pulse cascade. -/
def pulseM1StageSpecOfR : ℕ → PulseM1.PulseM1StageSpec
  | 3 => GroverM1PulsePt0.solStage_r3
  | 4 => GroverM1PulsePt0.solStage_r4
  | 5 => GroverM1PulsePt0.solStage_r5
  | 6 => GroverM1PulsePt0.solStage_r6
  | 7 => GroverM1PulsePt0.solStage_r7
  | 8 => GroverM1PulsePt0.solStage_r8
  | 9 => GroverM1PulsePt0.solStage_r9
  | 10 => GroverM1PulsePt0.solStage_r10
  | 11 => GroverM1PulsePt0.solStage_r11
  | 12 => GroverM1PulsePt0.solStage_r12
  | 13 => GroverM1PulsePt0.solStage_r13
  | 14 => GroverM1PulsePt0.solStage_r14
  | 15 => GroverM1PulsePt0.solStage_r15
  | 16 => GroverM1PulsePt0.solStage_r16
  | 32 => GroverM1PulsePt2.solStage_ref_r32
  | 64 => GroverM1PulsePt2.solStage_ref_r64
  | 128 => GroverM1PulsePt2.solStage_ref_r128
  | 256 => GroverM1PulsePt2.solStage_ref_r256
  | 512 => GroverM1PulsePt1.solStage_r512
  | 1024 => GroverM1PulseTable.solStage_r1024
  | 33 | 65 | 129 | 257 | 513 => PulseM1.solGrover1Stage
  | _ => GroverM1PulseTable.solStage_r2
/-- Stage-level Bellman soundness goal for `pulseM1CertBundle` with opaque `s`. -/
private def SolStageBundleProp (n r : ℕ) (s : PulseM1.PulseM1StageSpec) : Prop :=
  ∃ (hL2 : 2 ≤ s.L),
    s.L ≤ 1024 ∧ s.L ≤ r ∧
    s.pulses.all SchurWeylLCert.swLPulseValid = true ∧
    ∀ (M : Fin (2 * s.L) → Fin (2 * s.L) → ℝ),
      SchurWeylLCert.IsValidSwLOverlap M →
      let K_blk := hdistLKBlk n r s.tauNum s.tauDen
      let cs : Fin s.L → ℝ × ℝ := fun w ↦
        (Real.cos ((K_blk : ℝ) * SchurWeylLCert.swLThetaShiftReal (2 ^ n) r w.1),
         Real.sin ((K_blk : ℝ) * SchurWeylLCert.swLThetaShiftReal (2 ^ n) r w.1))
      let out := hdistLEvolutionReal s.L hL2 cs s.pulses
      let p : ℕ → ℝ := SchurWeylLCert.swLAttemptProbReal s.L hL2 M out.1 out.2.1
      let pSucc : ℝ := ∑ h ∈ Finset.Icc 1 s.L, p h
      let V : ℕ → ℝ := fun j ↦
        ((GroverM1PulsePt2.solM1VTable16_ref j : ℝ) /
          (SchurWeylLCert.multiUnitScale : ℝ)) * √(2 ^ n : ℝ)
      0 < pSucc ∧
      (out.2.2 * (K_blk : ℝ) + (s.L : ℝ) +
        ∑ h ∈ Finset.Icc 1 s.L, p h * V (r - h)) / pSucc ≤ V r
private theorem solStageSound_of_eq {n r : ℕ} (s s' : PulseM1.PulseM1StageSpec) (hs : s = s') (h
  : GroverM1PulseTable.PulseStageTableProp n r s' GroverM1PulsePt2.solM1VTable16_ref) :
  SolStageBundleProp n r s := by subst hs; exact h
private theorem solStageSound_explicit_le31 {L n r tauNum tauDen uvDen : ℕ} {ratios : List
  SchurWeylLCert.IvInt} {trigIvs : List (SchurWeylLCert.IvInt × SchurWeylLCert.IvInt)} {sps : List
  PulseM1.SolSparsePulse} {p0Lb : ℤ} {tailLbs : List ℤ} {survUb : ℤ} {s :
  PulseM1.PulseM1StageSpec} (hn96 : 96 ≤ n) (hr31 : r ≤ 31) (hchk :
  GroverM1PulseTable.checkPulseExplicitStageTable L r tauNum tauDen uvDen ratios trigIvs sps
  p0Lb tailLbs survUb GroverM1PulseTable.solM1VTable16 = true) (hs : s = ⟨L, tauNum, tauDen,
  PulseM1.solToSwLPulses L uvDen sps⟩) : SolStageBundleProp n r s :=
  solStageSound_of_eq s _ hs
    (GroverM1PulsePt2.pulseStageTableProp_of_le_31 hr31
      (GroverM1PulseTable.checkPulseExplicitStageTable_sound hn96 hchk))
private theorem solStageSound_l2Bucket_le31 {n r rMin rMax len tauNum tauDen uvDen : ℕ} {ratios :
  List SchurWeylLCert.IvInt} {trigIvs : List (SchurWeylLCert.IvInt × SchurWeylLCert.IvInt)} {sps :
  List PulseM1.SolSparsePulse} {p0Lb : ℤ} {tailLbs : List ℤ} {survUb : ℤ} {s :
  PulseM1.PulseM1StageSpec} (hn96 : 96 ≤ n) (hmin : rMin ≤ r) (hmax : r ≤ rMax) (hlt : r < rMin
  + len) (hr31 : r ≤ 31) (hchk : GroverM1PulseTable.checkPulseL2RangeBucketTable rMin rMax len
  tauNum tauDen uvDen ratios trigIvs sps p0Lb tailLbs survUb GroverM1PulseTable.solM1VTable16 =
  true) (hs : s = ⟨2, tauNum, tauDen, PulseM1.solToSwLPulses 2 uvDen sps⟩) : SolStageBundleProp n
  r s :=
  solStageSound_of_eq s _ hs
    (GroverM1PulsePt2.pulseStageTableProp_of_le_31 hr31
      (GroverM1PulseTable.checkPulseL2RangeBucketTable_sound hn96 hmin hmax hlt hchk))
private theorem solStageSound_l2Bucket {n r rMin rMax len tauNum tauDen uvDen : ℕ} {ratios : List
  SchurWeylLCert.IvInt} {trigIvs : List (SchurWeylLCert.IvInt × SchurWeylLCert.IvInt)} {sps : List
  PulseM1.SolSparsePulse} {p0Lb : ℤ} {tailLbs : List ℤ} {survUb : ℤ} {s :
  PulseM1.PulseM1StageSpec} (hn96 : 96 ≤ n) (hmin : rMin ≤ r) (hmax : r ≤ rMax) (hlt : r < rMin
  + len) (hbkt : GroverM1PulseTable.checkPulseL2RangeBucketTable rMin rMax len tauNum tauDen
  uvDen ratios trigIvs sps p0Lb tailLbs survUb GroverM1PulseTable.solM1VTable16 = true) (hstep :
  GroverM1PulseTable.solAllBelow len rMin (fun r' ↦ PulseM1.checkPulseCascadeStepTable 2 r'
  tauNum tauDen survUb p0Lb tailLbs GroverM1PulsePt2.solM1VTable16_ref) = true) (hs : s = ⟨2,
  tauNum, tauDen, PulseM1.solToSwLPulses 2 uvDen sps⟩) : SolStageBundleProp n r s :=
  solStageSound_of_eq s _ hs
    (GroverM1PulsePt2.checkPulseL2RangeBucket_sound hn96 hmin hmax hlt hbkt hstep)
private theorem solStageSound_wkbTable {n r : ℕ} {q : PulseM1.SolWkbSched} {ratios : List
  SchurWeylLCert.IvInt} {trigIvs : List (SchurWeylLCert.IvInt × SchurWeylLCert.IvInt)} {cEnd : List
  ℤ} {hEnd rhoEnd : ℕ} {survEnd p0Lb : ℤ} {tailLbs : List ℤ} {survUb : ℤ} {s :
  PulseM1.PulseM1StageSpec} (hn96 : 96 ≤ n) (hrun : PulseM1.SolWkbRunPrefix q trigIvs q.K cEnd
  hEnd rhoEnd survEnd) (hterm : GroverM1PulseTable.checkPulseWkbTerminalTable r q ratios trigIvs
  cEnd rhoEnd survEnd p0Lb tailLbs survUb GroverM1PulsePt2.solM1VTable16_ref = true) (hs : s =
  ⟨q.L, q.tauNum, q.tauDen, PulseM1.solWkbToSwLPulses q⟩) : SolStageBundleProp n r s :=
  solStageSound_of_eq s _ hs
    (GroverM1PulseTable.checkPulseWkbTerminalTable_sound hn96 hrun hterm)
private theorem solStageSound_wkbEnv {n r : ℕ} {q : PulseM1.SolWkbSched} {ratios : List
  SchurWeylLCert.IvInt} {trigIvs : List (SchurWeylLCert.IvInt × SchurWeylLCert.IvInt)} {cEnd : List
  ℤ} {hEnd rhoEnd : ℕ} {survEnd p0Lb : ℤ} {tailLbs : List ℤ} {survUb : ℤ} {s :
  PulseM1.PulseM1StageSpec} (hn96 : 96 ≤ n) (hrun : PulseM1.SolWkbRunPrefix q trigIvs q.K cEnd
  hEnd rhoEnd survEnd) (hterm : GroverM1PulseTable.checkPulseWkbTerminalEnv r q ratios trigIvs
  cEnd rhoEnd survEnd p0Lb tailLbs survUb GroverM1PulsePt2.solM1VTable16_ref = true) (hs : s =
  ⟨q.L, q.tauNum, q.tauDen, PulseM1.solWkbToSwLPulses q⟩) : SolStageBundleProp n r s :=
  solStageSound_of_eq s _ hs
    (GroverM1PulseTable.checkPulseWkbTerminalEnv_sound hn96 hrun hterm)
private theorem solStageSound_wkbStep {n r : ℕ} {q : PulseM1.SolWkbSched} {ratios : List
  SchurWeylLCert.IvInt} {trigIvs : List (SchurWeylLCert.IvInt × SchurWeylLCert.IvInt)} {cEnd : List
  ℤ} {hEnd rhoEnd : ℕ} {survEnd p0Lb : ℤ} {tailLbs : List ℤ} {survUb : ℤ} {s :
  PulseM1.PulseM1StageSpec} (hn96 : 96 ≤ n) (hrun : PulseM1.SolWkbRunPrefix q trigIvs q.K cEnd
  hEnd rhoEnd survEnd) (hterm : GroverM1PulseTable.checkPulseWkbTerminalTable r q ratios trigIvs
  cEnd rhoEnd survEnd p0Lb tailLbs survUb GroverM1PulseTable.solM1VTable16 = true) (hstep :
  PulseM1.checkPulseCascadeStepTable q.L r q.tauNum q.tauDen survUb p0Lb tailLbs
  GroverM1PulsePt2.solM1VTable16_ref = true) (hs : s = ⟨q.L, q.tauNum, q.tauDen,
  PulseM1.solWkbToSwLPulses q⟩) : SolStageBundleProp n r s :=
  solStageSound_of_eq s _ hs
    (GroverM1PulsePt2.checkPulseWkbStep_sound hn96 hrun hterm hstep)
private theorem solStageSound_grover1 {n r : ℕ} {s : PulseM1.PulseM1StageSpec} (hn96 : 96 ≤
  n) (hstep : PulseM1.checkPulseGrover1StepTable r GroverM1PulsePt2.solM1VTable16_ref =
  true) (hs : s = PulseM1.solGrover1Stage) : SolStageBundleProp n r s :=
  solStageSound_of_eq s _ hs (PulseM1.checkPulseGrover1StepTable_sound hn96 hstep)
/-- Certified `kMax = 1024` standalone 39-stage `m = 1` Multi-pulse conveyor bundle. -/
def pulseM1CertBundle : PulseM1.PulseM1CertBundle where
  kMax := 1024
  vScale := SchurWeylLCert.multiUnitScale
  vTable := GroverM1PulsePt2.solM1VTable16_ref
  usePulse r := decide (2 ≤ r)
  stageOfR := pulseM1StageSpecOfR
  hKMax := le_rfl
  hScalePos := by unfold SchurWeylLCert.multiUnitScale; decide
  hV0 := by decide
  hNonneg r _hr := by
    have h := GroverM1PulseTable.solAllBelow_true
      GroverM1PulsePt2.cert_solVTableNonneg_ref r (Nat.zero_le r) (by omega)
    rwa [PulseM1.solBleZ_eq_decide, decide_eq_true_eq] at h
  hStageSound {n r} _hn1152 _hr1 _hrMax huse := by
    have hn96 : 96 ≤ n := by omega
    have _hr2 : 2 ≤ r := of_decide_eq_true huse
    change SolStageBundleProp n r (pulseM1StageSpecOfR r)
    if hr_3 : r = 3 then
      subst hr_3
      exact solStageSound_explicit_le31 hn96 (by decide)
        GroverM1PulsePt0.cert_solExplicit_r3 rfl
    else if hr_4 : r = 4 then
      subst hr_4
      exact solStageSound_explicit_le31 hn96 (by decide)
        GroverM1PulsePt0.cert_solExplicit_r4 rfl
    else if hr_5 : r = 5 then
      subst hr_5
      exact solStageSound_explicit_le31 hn96 (by decide)
        GroverM1PulsePt0.cert_solExplicit_r5 rfl
    else if hr_6 : r = 6 then
      subst hr_6
      exact solStageSound_explicit_le31 hn96 (by decide)
        GroverM1PulsePt0.cert_solExplicit_r6 rfl
    else if hr_7 : r = 7 then
      subst hr_7
      exact solStageSound_explicit_le31 hn96 (by decide)
        GroverM1PulsePt0.cert_solExplicit_r7 rfl
    else if hr_8 : r = 8 then
      subst hr_8
      exact solStageSound_explicit_le31 hn96 (by decide)
        GroverM1PulsePt0.cert_solExplicit_r8 rfl
    else if hr_9 : r = 9 then
      subst hr_9
      exact solStageSound_explicit_le31 hn96 (by decide)
        GroverM1PulsePt0.cert_solExplicit_r9 rfl
    else if hr_10 : r = 10 then
      subst hr_10
      exact solStageSound_explicit_le31 hn96 (by decide)
        GroverM1PulsePt0.cert_solExplicit_r10 rfl
    else if hr_11 : r = 11 then
      subst hr_11
      exact solStageSound_explicit_le31 hn96 (by decide)
        GroverM1PulsePt0.cert_solExplicit_r11 rfl
    else if hr_12 : r = 12 then
      subst hr_12
      exact solStageSound_explicit_le31 hn96 (by decide)
        GroverM1PulsePt0.cert_solExplicit_r12 rfl
    else if hr_13 : r = 13 then
      subst hr_13
      exact solStageSound_explicit_le31 hn96 (by decide)
        GroverM1PulsePt0.cert_solExplicit_r13 rfl
    else if hr_14 : r = 14 then
      subst hr_14
      exact solStageSound_explicit_le31 hn96 (by decide)
        GroverM1PulsePt0.cert_solExplicit_r14 rfl
    else if hr_15 : r = 15 then
      subst hr_15
      exact solStageSound_explicit_le31 hn96 (by decide)
        GroverM1PulsePt0.cert_solExplicit_r15 rfl
    else if hr_16 : r = 16 then
      subst hr_16
      exact solStageSound_explicit_le31 hn96 (by decide)
        GroverM1PulsePt0.cert_solExplicit_r16 rfl
    else if hr_32 : r = 32 then
      subst hr_32
      exact solStageSound_wkbTable hn96 GroverM1PulsePt2.runPrefix_solWkb_ref_r32
        GroverM1PulsePt2.cert_solWkbTerm_ref_r32 rfl
    else if hr_64 : r = 64 then
      subst hr_64
      exact solStageSound_wkbEnv hn96 GroverM1PulsePt2.runPrefix_solWkb_ref_r64
        GroverM1PulsePt2.cert_solWkbTerm_ref_r64 rfl
    else if hr_128 : r = 128 then
      subst hr_128
      exact solStageSound_wkbEnv hn96 GroverM1PulsePt2.runPrefix_solWkb_ref_r128
        GroverM1PulsePt2.cert_solWkbTerm_ref_r128 rfl
    else if hr_256 : r = 256 then
      subst hr_256
      exact solStageSound_wkbTable hn96 GroverM1PulsePt2.runPrefix_solWkb_ref_r256
        GroverM1PulsePt2.cert_solWkbTerm_ref_r256 rfl
    else if hr_512 : r = 512 then
      subst hr_512
      exact solStageSound_wkbStep hn96 GroverM1PulsePt1.runPrefix_solWkb_r512
        GroverM1PulsePt1.cert_solWkbTerm_r512
        GroverM1PulsePt2.cert_solWkbStep_r512 rfl
    else if hr_1024 : r = 1024 then
      subst hr_1024
      exact solStageSound_wkbStep hn96
        (GroverM1PulsePt2.runSuffix_solWkb_r1024
          GroverM1PulsePt1.runPrefixMid_solWkb_r1024)
        GroverM1PulsePt2.cert_solWkbTerm_r1024
        GroverM1PulsePt2.cert_solWkbStep_r1024 rfl
    else if hr_33 : r = 33 then
      subst hr_33
      exact solStageSound_grover1 hn96 GroverM1PulsePt2.cert_solGrover1_ref_r33 rfl
    else if hr_65 : r = 65 then
      subst hr_65
      exact solStageSound_grover1 hn96 GroverM1PulsePt2.cert_solGrover1_ref_r65 rfl
    else if hr_129 : r = 129 then
      subst hr_129
      exact solStageSound_grover1 hn96 GroverM1PulsePt2.cert_solGrover1_ref_r129 rfl
    else if hr_257 : r = 257 then
      subst hr_257
      exact solStageSound_grover1 hn96 GroverM1PulsePt2.cert_solGrover1_ref_r257 rfl
    else if hr_513 : r = 513 then
      subst hr_513
      exact solStageSound_grover1 hn96 GroverM1PulsePt2.cert_solGrover1_ref_r513 rfl
    else
      have hspec : pulseM1StageSpecOfR r =
          ⟨2, 8201211, 100000000,
            PulseM1.solToSwLPulses 2 65536
              GroverM1PulseTable.solExplicitPulses_r2⟩ := by
        unfold pulseM1StageSpecOfR; split <;> first | omega | rfl
      if hr_2 : r = 2 then
        subst hr_2
        exact solStageSound_explicit_le31 hn96 (by decide)
          GroverM1PulseTable.cert_solExplicit_r2 hspec
      else if hb_17 : r ≤ 20 then
        have ha : 17 ≤ r := by omega
        have hlt : r < 17 + 4 := by omega
        exact solStageSound_l2Bucket_le31 hn96 ha hb_17 hlt (by omega)
          GroverM1PulseTable.cert_solL2_b17_20 hspec
      else if hb_21 : r ≤ 25 then
        have ha : 21 ≤ r := by omega
        have hlt : r < 21 + 5 := by omega
        exact solStageSound_l2Bucket_le31 hn96 ha hb_21 hlt (by omega)
          GroverM1PulseTable.cert_solL2_b21_25 hspec
      else if hb_26 : r ≤ 31 then
        have ha : 26 ≤ r := by omega
        have hlt : r < 26 + 6 := by omega
        exact solStageSound_l2Bucket_le31 hn96 ha hb_26 hlt (by omega)
          GroverM1PulseTable.cert_solL2_b26_31 hspec
      else if hb_34 : r ≤ 45 then
        have ha : 34 ≤ r := by omega
        have hlt : r < 34 + 12 := by omega
        exact solStageSound_l2Bucket hn96 ha hb_34 hlt
          GroverM1PulseTable.cert_solL2_b34_45
          GroverM1PulsePt2.cert_solL2Step_b34_45 hspec
      else if hb_46 : r ≤ 63 then
        have ha : 46 ≤ r := by omega
        have hlt : r < 46 + 18 := by omega
        exact solStageSound_l2Bucket hn96 ha hb_46 hlt
          GroverM1PulseTable.cert_solL2_b46_63
          GroverM1PulsePt2.cert_solL2Step_b46_63 hspec
      else if hb_66 : r ≤ 95 then
        have ha : 66 ≤ r := by omega
        have hlt : r < 66 + 30 := by omega
        exact solStageSound_l2Bucket hn96 ha hb_66 hlt
          GroverM1PulseTable.cert_solL2_b66_95
          GroverM1PulsePt2.cert_solL2Step_b66_95 hspec
      else if hb_96 : r ≤ 127 then
        have ha : 96 ≤ r := by omega
        have hlt : r < 96 + 32 := by omega
        exact solStageSound_l2Bucket hn96 ha hb_96 hlt
          GroverM1PulseTable.cert_solL2_b96_127
          GroverM1PulsePt2.cert_solL2Step_b96_127 hspec
      else if hb_130 : r ≤ 190 then
        have ha : 130 ≤ r := by omega
        have hlt : r < 130 + 61 := by omega
        exact solStageSound_l2Bucket hn96 ha hb_130 hlt
          GroverM1PulseTable.cert_solL2_b130_190
          GroverM1PulsePt2.cert_solL2Step_b130_190 hspec
      else if hb_191 : r ≤ 255 then
        have ha : 191 ≤ r := by omega
        have hlt : r < 191 + 65 := by omega
        exact solStageSound_l2Bucket hn96 ha hb_191 hlt
          GroverM1PulseTable.cert_solL2_b191_255
          GroverM1PulsePt2.cert_solL2Step_b191_255 hspec
      else if hb_258 : r ≤ 380 then
        have ha : 258 ≤ r := by omega
        have hlt : r < 258 + 123 := by omega
        exact solStageSound_l2Bucket hn96 ha hb_258 hlt
          GroverM1PulseTable.cert_solL2_b258_380
          GroverM1PulsePt2.cert_solL2Step_b258_380 hspec
      else if hb_381 : r ≤ 511 then
        have ha : 381 ≤ r := by omega
        have hlt : r < 381 + 131 := by omega
        exact solStageSound_l2Bucket hn96 ha hb_381 hlt
          GroverM1PulseTable.cert_solL2_b381_511
          GroverM1PulsePt2.cert_solL2Step_b381_511 hspec
      else if hb_514 : r ≤ 760 then
        have ha : 514 ≤ r := by omega
        have hlt : r < 514 + 247 := by omega
        exact solStageSound_l2Bucket hn96 ha hb_514 hlt
          GroverM1PulseTable.cert_solL2_b514_760
          GroverM1PulsePt2.cert_solL2Step_b514_760 hspec
      else
        have ha : 761 ≤ r := by omega
        have hb : r ≤ 1023 := by omega
        have hlt : r < 761 + 263 := by omega
        exact solStageSound_l2Bucket hn96 ha hb hlt
          GroverM1PulseTable.cert_solL2_b761_1023
          GroverM1PulsePt2.cert_solL2Step_b761_1023 hspec
end InternalBundle
section InternalLtM1K2
open QuantumComputation.Specs.GroverFindAll.SchurWeylLCert
open QuantumComputation.Specs.GroverFindAll.PipeFuseCert
open QuantumComputation.Specs.GroverFindAll.TensorConveyorCert
open scoped BigOperators
private def ltM1K2Div91 : ℤ := Int.ofNat (Nat.pow 10 91)
private theorem ltM1K2_scale_yHi_aux : (0 : ℤ) < ltM1K2Div91 ∧ tcAmpScale = swScale * ltM1K2Div91 ∧
  (-((-((464764000001000000000 : ℤ) * tcAmpScale)) / (((2 : ℤ) ^ tcTrigHalvings) *
  (50000000000000000000000 : ℤ))) ≤ tcAmpScale) ∧ (-((-((32863777605210212626118657000000000 : ℤ) *
  tcAmpScale)) / (((2 : ℤ) ^ tcTrigHalvings) * (5000000000000000000000000000000000000 : ℤ))) ≤
  tcAmpScale) :=
  by
  unfold tcAmpScale swScale ltM1K2Div91 tcTrigHalvings; decide +kernel
private theorem ltM1K2Div91_pos : (0 : ℤ) < ltM1K2Div91 := ltM1K2_scale_yHi_aux.1
private theorem ltM1K2_tcAmpScale_eq : tcAmpScale = swScale * ltM1K2Div91 :=
  ltM1K2_scale_yHi_aux.2.1
private def ltM1K2Iv100To9 (iv : TcIv) : IvInt :=
  tcWithForcedInt ltM1K2Div91 fun d91 ↦
    (Int.ediv iv.1 d91, Int.neg (Int.ediv (Int.neg iv.2) d91))
private theorem ltM1K2_memIvInt_of_tcMemAmpIv {x : ℝ} {iv : TcIv} (hx : tcMemAmpIv x iv) : memIvInt
  x (ltM1K2Iv100To9 iv) := by
  have hS : (0 : ℝ) < (swScale : ℝ) := (by unfold swScale; norm_num); have hD_pos : (0 : ℤ) <
    ltM1K2Div91 := ltM1K2Div91_pos; have hD_r : (0 : ℝ) < (ltM1K2Div91 : ℝ) := Int.cast_pos.2 hD_pos
  have hmul_r : (tcAmpScale : ℝ) = (swScale : ℝ) * (ltM1K2Div91 : ℝ) :=
    (by exact_mod_cast ltM1K2_tcAmpScale_eq)
  unfold ltM1K2Iv100To9 memIvInt; unfold tcMemAmpIv at hx; simp only [tcWithForcedInt_eq,
    tcInt_ediv_eq, tcInt_neg_eq]; constructor
  · have h1 := div_le_div_of_nonneg_right (tc_ediv_pos_le_real iv.1 ltM1K2Div91 hD_pos) hS.le
    have h2 : (iv.1 : ℝ) / (ltM1K2Div91 : ℝ) / (swScale : ℝ) = (iv.1 : ℝ) / (tcAmpScale : ℝ) :=
      (by rw [hmul_r]; field_simp [hS.ne', hD_r.ne']); exact (h1.trans_eq h2).trans hx.1
  · have h1 := div_le_div_of_nonneg_right (tc_real_le_neg_ediv_neg_pos iv.2 ltM1K2Div91 hD_pos)
      hS.le; have h2 : (iv.2 : ℝ) / (tcAmpScale : ℝ) = (iv.2 : ℝ) / (ltM1K2Div91 : ℝ) / (swScale :
      ℝ) := (by rw [hmul_r]; field_simp [hS.ne', hD_r.ne']); exact hx.2.trans (h2.trans_le h1)
private theorem ltM1K2_tcMemAmpIv_one : tcMemAmpIv 1 (tcAmpScale, tcAmpScale) := by
  have hS : (tcAmpScale : ℝ) ≠ 0 := tcAmpScale_pos_real.ne'
  unfold tcMemAmpIv; dsimp only; rw [div_self hS]; exact ⟨le_rfl, le_rfl⟩
private theorem ltM1K2_tcMemAmpIv_zero : tcMemAmpIv 0 (Int.ofNat 0, Int.ofNat 0) := by
  unfold tcMemAmpIv; simp only [tcInt_ofNat_eq, Nat.cast_zero, Int.cast_zero, zero_div]
  exact ⟨le_rfl, le_rfl⟩
private def ltM1K2IvPythag100 {α : Type*} (num den : ℤ) (k : TcIv → TcIv → α) : α :=
  tcWithForcedInt tcAmpScale fun ampS ↦
    tcWithForcedInt (Int.mul den den) fun d2 ↦
      tcWithForcedInt (Int.mul num num) fun n2 ↦
        tcWithForcedInt (Int.add d2 n2) fun sumSq ↦
          tcWithForcedInt (Int.mul (Int.sub d2 n2) ampS) fun cSc ↦
            tcWithForcedInt (Int.mul (Int.mul (Int.mul (Int.ofNat 2) num) den) ampS) fun sSc ↦
              tcWithForcedIv (Int.ediv cSc sumSq, Int.neg (Int.ediv (Int.neg cSc) sumSq))
                fun cIv ↦
                tcWithForcedIv (Int.ediv sSc sumSq, Int.neg (Int.ediv (Int.neg sSc) sumSq))
                  fun sIv ↦ k cIv sIv
private def ltM1K2PythagCosIv100 (num den : ℤ) : TcIv :=
  let sumSq := den * den + num * num
  let cSc := (den * den - num * num) * tcAmpScale
  (cSc / sumSq, -((-cSc) / sumSq))
private def ltM1K2PythagSinIv100 (num den : ℤ) : TcIv :=
  let sumSq := den * den + num * num
  let sSc := 2 * num * den * tcAmpScale
  (sSc / sumSq, -((-sSc) / sumSq))
private theorem ltM1K2IvPythag100_eq {α : Type*} (num den : ℤ) (k : TcIv → TcIv → α) :
  ltM1K2IvPythag100 num den k = k (ltM1K2PythagCosIv100 num den) (ltM1K2PythagSinIv100 num den) :=
  by
  unfold ltM1K2IvPythag100 ltM1K2PythagCosIv100 ltM1K2PythagSinIv100; simp only [tcWithForcedInt_eq,
    tcWithForcedIv_eq, tcInt_mul_eq, tcInt_add_eq, tcInt_sub_eq, tcInt_ediv_eq, tcInt_neg_eq,
    tcInt_ofNat_eq, Nat.cast_ofNat]
private theorem ltM1K2_pythag100_sound (num : ℤ) {den : ℕ} (hden : 0 < den) : tcMemAmpIv
  (swLCayleyCos num den) (ltM1K2PythagCosIv100 num (Int.ofNat den)) ∧ tcMemAmpIv (swLCayleySin num
  den) (ltM1K2PythagSinIv100 num (Int.ofNat den)) := by
  unfold ltM1K2PythagCosIv100 ltM1K2PythagSinIv100; simp only [tcInt_ofNat_eq]; have hd_z : (den :
    ℤ) ≠ 0 := (by exact_mod_cast hden.ne'); rcases tcMemAmpIv_pythag_ratDiv num (den : ℤ) hd_z with
    ⟨hc, hs⟩; have hc_eq : (tcRatCos ((num : ℚ) / ((den : ℤ) : ℚ)) : ℝ) = swLCayleyCos num den :=
    (by rw [tcRatCos_ratDiv_eq num (den : ℤ) hd_z]; unfold swLCayleyCos; push_cast; ring)
  have hs_eq : (tcRatSin ((num : ℚ) / ((den : ℤ) : ℚ)) : ℝ) = swLCayleySin num den :=
    (by rw [tcRatSin_ratDiv_eq num (den : ℤ) hd_z]; unfold swLCayleySin; push_cast; ring)
  rw [hc_eq] at hc; rw [hs_eq] at hs; exact ⟨hc, hs⟩
private def ltM1K2MkPulse (uv : ℤ × ℤ) : SwLPulseRat 2 :=
  ⟨fun _ ↦ uv.1, uv.2, 1000000000⟩
private def ltM1K2PulseStep100 {α : Type*} (cs0 cs1 : TcIv × TcIv)
    (s0 s1 s2 s3 cum surv : TcIv) (uv : ℤ × ℤ)
    (k : TcIv → TcIv → TcIv → TcIv → TcIv → TcIv → α) : α :=
  tcWithForcedIv (tcIvSub (tcIvMul cs0.1 s0) (tcIvMul cs0.2 s1)) fun na0 ↦
    tcWithForcedIv (tcIvAdd (tcIvMul cs0.2 s0) (tcIvMul cs0.1 s1)) fun na1 ↦
      tcWithForcedIv (tcIvSub (tcIvMul cs1.1 s2) (tcIvMul cs1.2 s3)) fun na2 ↦
        tcWithForcedIv (tcIvAdd (tcIvMul cs1.2 s2) (tcIvMul cs1.1 s3)) fun na3 ↦
          ltM1K2IvPythag100 uv.1 (Int.ofNat 1000000000) fun cu su ↦
            ltM1K2IvPythag100 uv.2 (Int.ofNat 1000000000) fun cv sv ↦
              tcWithForcedIv (tcIvSub (tcIvMul cu na1) (tcIvMul su na2)) fun nxt1 ↦
                tcWithForcedIv (tcIvAdd (tcIvMul su na1) (tcIvMul cu na2)) fun nxt2 ↦
                  tcWithForcedIv (tcIvMul cv na3) fun nxt3 ↦
                    tcWithForcedIv (tcIvAdd cum (tcIvSq (tcIvMul sv na3))) fun ncum ↦
                      tcWithForcedIv
                        (tcIvAdd surv (tcIvSub (tcAmpScale, tcAmpScale) cum)) fun nsurv ↦
                        k na0 nxt1 nxt2 nxt3 ncum nsurv
private def ltM1K2Evol100Aux (cs0 cs1 : TcIv × TcIv) :
    TcIv → TcIv → TcIv → TcIv → TcIv → TcIv → List (ℤ × ℤ) →
      TcIv × TcIv × TcIv × TcIv × TcIv × TcIv
  | s0, s1, s2, s3, cum, surv, [] => (s0, s1, s2, s3, cum, surv)
  | s0, s1, s2, s3, cum, surv, uv :: ps =>
      ltM1K2PulseStep100 cs0 cs1 s0 s1 s2 s3 cum surv uv fun ns0 ns1 ns2 ns3 ncum nsurv ↦
        ltM1K2Evol100Aux cs0 cs1 ns0 ns1 ns2 ns3 ncum nsurv ps
private def ltM1K2Evol100Chunks (cs0 cs1 : TcIv × TcIv) :
    TcIv → TcIv → TcIv → TcIv → TcIv → TcIv → List (List (ℤ × ℤ)) →
      TcIv × TcIv × TcIv × TcIv × TcIv × TcIv
  | s0, s1, s2, s3, cum, surv, [] => (s0, s1, s2, s3, cum, surv)
  | s0, s1, s2, s3, cum, surv, ch :: chs =>
      match ltM1K2Evol100Aux cs0 cs1 s0 s1 s2 s3 cum surv ch with
      | (ns0, ns1, ns2, ns3, ncum, nsurv) =>
          ltM1K2Evol100Chunks cs0 cs1 ns0 ns1 ns2 ns3 ncum nsurv chs
private def ltM1K2Flatten : List (List (ℤ × ℤ)) → List (ℤ × ℤ)
  | [] => []
  | ch :: chs => List.append ch (ltM1K2Flatten chs)
private theorem ltM1K2Evol100Aux_append (cs0 cs1 : TcIv × TcIv)
    (xs ys : List (ℤ × ℤ)) (s0 s1 s2 s3 cum surv : TcIv) :
    ltM1K2Evol100Aux cs0 cs1 s0 s1 s2 s3 cum surv (List.append xs ys) =
      match ltM1K2Evol100Aux cs0 cs1 s0 s1 s2 s3 cum surv xs with
      | (ns0, ns1, ns2, ns3, ncum, nsurv) =>
          ltM1K2Evol100Aux cs0 cs1 ns0 ns1 ns2 ns3 ncum nsurv ys := by
  induction xs generalizing s0 s1 s2 s3 cum surv with
  | nil => rfl
  | cons uv rest ih =>
      change ltM1K2Evol100Aux cs0 cs1 s0 s1 s2 s3 cum surv (uv :: List.append rest ys) = _
      simp only [ltM1K2Evol100Aux]; unfold ltM1K2PulseStep100 ltM1K2IvPythag100
      simp only [tcWithForcedInt_eq, tcWithForcedIv_eq]; exact ih _ _ _ _ _ _
private theorem ltM1K2Evol100Chunks_eq (cs0 cs1 : TcIv × TcIv) (chs : List (List (ℤ × ℤ))) (s0 s1 s2
  s3 cum surv : TcIv) : ltM1K2Evol100Chunks cs0 cs1 s0 s1 s2 s3 cum surv chs = ltM1K2Evol100Aux cs0
  cs1 s0 s1 s2 s3 cum surv (ltM1K2Flatten chs) := by
  induction chs generalizing s0 s1 s2 s3 cum surv with
  | nil => rfl
  | cons ch rest ih =>
    simp only [ltM1K2Flatten, ltM1K2Evol100Chunks, ltM1K2Evol100Aux_append]
    rcases ltM1K2Evol100Aux cs0 cs1 s0 s1 s2 s3 cum surv ch with ⟨ns0, ns1, ns2, ns3, ncum, nsurv⟩
    exact ih ns0 ns1 ns2 ns3 ncum nsurv
private theorem ltM1K2PulseStep100_sound {cs : Fin 2 → ℝ × ℝ} {cs0 cs1 : TcIv × TcIv} (hcs0 :
  tcMemAmpIv (cs ⟨0, by omega⟩).1 cs0.1 ∧ tcMemAmpIv (cs ⟨0, by omega⟩).2 cs0.2) (hcs1 : tcMemAmpIv
  (cs ⟨1, by omega⟩).1 cs1.1 ∧ tcMemAmpIv (cs ⟨1, by omega⟩).2 cs1.2) {st : Fin 4 → ℝ} {s0 s1 s2 s3
  cum surv : TcIv} {cumR survR : ℝ} (uv : ℤ × ℤ) (hst0 : tcMemAmpIv (st ⟨0, by omega⟩) s0) (hst1 :
  tcMemAmpIv (st ⟨1, by omega⟩) s1) (hst2 : tcMemAmpIv (st ⟨2, by omega⟩) s2) (hst3 : tcMemAmpIv (st
  ⟨3, by omega⟩) s3) (hcum : tcMemAmpIv cumR cum) (hsurv : tcMemAmpIv survR surv) :
    let outR := swLPulseStepReal 2 (by omega) cs st cumR survR (ltM1K2MkPulse uv)
    ltM1K2PulseStep100 cs0 cs1 s0 s1 s2 s3 cum surv uv fun ns0 ns1 ns2 ns3 ncum nsurv ↦ tcMemAmpIv
      (outR.1 ⟨0, by omega⟩) ns0 ∧ tcMemAmpIv (outR.1 ⟨1, by omega⟩) ns1 ∧ tcMemAmpIv (outR.1 ⟨2,
      by omega⟩) ns2 ∧ tcMemAmpIv (outR.1 ⟨3, by omega⟩) ns3 ∧ tcMemAmpIv outR.2.1 ncum ∧ tcMemAmpIv
      outR.2.2 nsurv := by
  intro outR; unfold ltM1K2PulseStep100; simp only [tcWithForcedIv_eq, ltM1K2IvPythag100_eq]
  rcases ltM1K2_pythag100_sound uv.1 (by omega : 0 < 1000000000) with ⟨hcu, hsu⟩
  rcases ltM1K2_pythag100_sound uv.2 (by omega : 0 < 1000000000) with ⟨hcv, hsv⟩
  have hna0 : tcMemAmpIv (swLGroverRotVec 2 cs st ⟨0, by omega⟩) (tcIvSub (tcIvMul cs0.1 s0)
    (tcIvMul cs0.2 s1)) := by
    change tcMemAmpIv ((cs ⟨0, by omega⟩).1 * st ⟨0, by omega⟩ - (cs ⟨0, by omega⟩).2 * st ⟨1,
      by omega⟩) _; exact tcMemAmpIv_sub (tcMemAmpIv_mul hcs0.1 hst0) (tcMemAmpIv_mul hcs0.2 hst1)
  have hna1 : tcMemAmpIv (swLGroverRotVec 2 cs st ⟨1, by omega⟩) (tcIvAdd (tcIvMul cs0.2 s0)
    (tcIvMul cs0.1 s1)) := by
    change tcMemAmpIv ((cs ⟨0, by omega⟩).2 * st ⟨0, by omega⟩ + (cs ⟨0, by omega⟩).1 * st ⟨1,
      by omega⟩) _; exact tcMemAmpIv_add (tcMemAmpIv_mul hcs0.2 hst0) (tcMemAmpIv_mul hcs0.1 hst1)
  have hna2 : tcMemAmpIv (swLGroverRotVec 2 cs st ⟨2, by omega⟩) (tcIvSub (tcIvMul cs1.1 s2)
    (tcIvMul cs1.2 s3)) := by
    change tcMemAmpIv ((cs ⟨1, by omega⟩).1 * st ⟨2, by omega⟩ - (cs ⟨1, by omega⟩).2 * st ⟨3,
      by omega⟩) _; exact tcMemAmpIv_sub (tcMemAmpIv_mul hcs1.1 hst2) (tcMemAmpIv_mul hcs1.2 hst3)
  have hna3 : tcMemAmpIv (swLGroverRotVec 2 cs st ⟨3, by omega⟩) (tcIvAdd (tcIvMul cs1.2 s2)
    (tcIvMul cs1.1 s3)) := by
    change tcMemAmpIv ((cs ⟨1, by omega⟩).2 * st ⟨2, by omega⟩ + (cs ⟨1, by omega⟩).1 * st ⟨3,
      by omega⟩) _; exact tcMemAmpIv_add (tcMemAmpIv_mul hcs1.2 hst2) (tcMemAmpIv_mul hcs1.1 hst3)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · change tcMemAmpIv (swLGroverRotVec 2 cs st ⟨0, by omega⟩) _; exact hna0
  · change tcMemAmpIv (swLCayleyCos uv.1 1000000000 * swLGroverRotVec 2 cs st ⟨1, by omega⟩ -
      swLCayleySin uv.1 1000000000 * swLGroverRotVec 2 cs st ⟨2, by omega⟩) _
    exact tcMemAmpIv_sub (tcMemAmpIv_mul hcu hna1) (tcMemAmpIv_mul hsu hna2)
  · change tcMemAmpIv (swLCayleySin uv.1 1000000000 * swLGroverRotVec 2 cs st ⟨1, by omega⟩ +
      swLCayleyCos uv.1 1000000000 * swLGroverRotVec 2 cs st ⟨2, by omega⟩) _
    exact tcMemAmpIv_add (tcMemAmpIv_mul hsu hna1) (tcMemAmpIv_mul hcu hna2)
  · change tcMemAmpIv (swLCayleyCos uv.2 1000000000 * swLGroverRotVec 2 cs st ⟨3, by omega⟩) _
    exact tcMemAmpIv_mul hcv hna3
  · change tcMemAmpIv (cumR + (swLCayleySin uv.2 1000000000 * swLGroverRotVec 2 cs st ⟨3, by omega⟩)
      ^ 2) _; exact tcMemAmpIv_add hcum (tcMemAmpIv_sq (tcMemAmpIv_mul hsv hna3))
  · change tcMemAmpIv (survR + (1 - cumR)) _; exact tcMemAmpIv_add hsurv (tcMemAmpIv_sub
      ltM1K2_tcMemAmpIv_one hcum)
private theorem ltM1K2Evol100Aux_sound {cs : Fin 2 → ℝ × ℝ} {cs0 cs1 : TcIv × TcIv} (hcs0 :
  tcMemAmpIv (cs ⟨0, by omega⟩).1 cs0.1 ∧ tcMemAmpIv (cs ⟨0, by omega⟩).2 cs0.2) (hcs1 : tcMemAmpIv
  (cs ⟨1, by omega⟩).1 cs1.1 ∧ tcMemAmpIv (cs ⟨1, by omega⟩).2 cs1.2) (ps : List (ℤ × ℤ)) {st : Fin
  4 → ℝ} {s0 s1 s2 s3 cum surv : TcIv} {cumR survR : ℝ} (hst0 : tcMemAmpIv (st ⟨0, by omega⟩) s0)
  (hst1 : tcMemAmpIv (st ⟨1, by omega⟩) s1) (hst2 : tcMemAmpIv (st ⟨2, by omega⟩) s2) (hst3 :
  tcMemAmpIv (st ⟨3, by omega⟩) s3) (hcum : tcMemAmpIv cumR cum) (hsurv : tcMemAmpIv survR surv) :
    let outR := swLEvolutionRealAux 2 (by omega) cs st cumR survR (ps.map ltM1K2MkPulse)
    let outIv := ltM1K2Evol100Aux cs0 cs1 s0 s1 s2 s3 cum surv ps
    tcMemAmpIv (outR.1 ⟨0, by omega⟩) outIv.1 ∧ tcMemAmpIv (outR.1 ⟨1, by omega⟩) outIv.2.1 ∧
      tcMemAmpIv (outR.1 ⟨2, by omega⟩) outIv.2.2.1 ∧ tcMemAmpIv (outR.1 ⟨3, by omega⟩)
      outIv.2.2.2.1 ∧ tcMemAmpIv outR.2.1 outIv.2.2.2.2.1 ∧ tcMemAmpIv outR.2.2 outIv.2.2.2.2.2 :=
      by
  induction ps generalizing st s0 s1 s2 s3 cum surv cumR survR with
  | nil => exact ⟨hst0, hst1, hst2, hst3, hcum, hsurv⟩
  | cons uv rest ih =>
    simp only [List.map_cons, swLEvolutionRealAux, ltM1K2Evol100Aux]; have hstep :=
      ltM1K2PulseStep100_sound hcs0 hcs1 uv hst0 hst1 hst2 hst3 hcum hsurv
    unfold ltM1K2PulseStep100 at hstep ⊢; simp only [tcWithForcedIv_eq] at hstep ⊢
    unfold ltM1K2IvPythag100 at hstep ⊢
    simp only [tcWithForcedInt_eq, tcWithForcedIv_eq] at hstep ⊢; rcases hstep with ⟨h0, h1, h2, h3,
      hc, hs⟩; exact ih h0 h1 h2 h3 hc hs
private theorem ltM1K2_arcsin_bounds {x : ℝ} (hx0 : 0 < x) (hx_ub : x ≤ 1 / 199000000000000) : 0 <
  Real.arcsin x ∧ Real.arcsin x ≤ 1 / 190000000000000 ∧ x ≤ Real.arcsin x ∧ (1 - 1 /
  100000000000000000000) * Real.arcsin x ≤ x := by
  have hx1 : x ≤ 1 := (by linarith)
  have hsin_x : Real.sin (Real.arcsin x) = x := Real.sin_arcsin (by linarith) hx1; have hα_pos : 0 <
    Real.arcsin x := Real.arcsin_pos.2 hx0
  have hα_lb : x ≤ Real.arcsin x := self_le_arcsin hx0.le hx1; set u : ℝ := 1 / 190000000000000
  have hu_pos : 0 < u := (by dsimp [u]; norm_num)
  have hx_le_sinu : x ≤ Real.sin u := by
    have hcube := (Real.sin_gt_sub_cube hu_pos).le
    have hnum : (1 : ℝ) / 199000000000000 ≤ u - u ^ 3 / 6 := (by dsimp [u]; norm_num); linarith
  have hα_le : Real.arcsin x ≤ u := by
    have h1 := Real.arcsin_le_arcsin hx_le_sinu
    have h2 : Real.arcsin (Real.sin u) = u := Real.arcsin_sin
      (by dsimp [u]; linarith [Real.pi_gt_three]) (by dsimp [u]; linarith [Real.pi_gt_three])
    linarith
  have hα_ub : (1 - 1 / 100000000000000000000) * Real.arcsin x ≤ x := by
    have hcube := (Real.sin_gt_sub_cube hα_pos).le; rw [hsin_x] at hcube
    have hsq : (Real.arcsin x) ^ 2 ≤ u ^ 2 := pow_le_pow_left₀ hα_pos.le hα_le 2
    have hu_sq : u ^ 2 / 6 ≤ 1 / 100000000000000000000 := (by dsimp [u]; norm_num)
    have hmul : (Real.arcsin x) ^ 3 / 6 ≤ (1 / 100000000000000000000) * Real.arcsin x := by
      have h1 : (Real.arcsin x) ^ 3 / 6 = ((Real.arcsin x) ^ 2 / 6) * Real.arcsin x := (by ring)
      rw [h1]; exact mul_le_mul_of_nonneg_right
        ((div_le_div_of_nonneg_right hsq (by norm_num)).trans hu_sq) hα_pos.le
    linarith
  exact ⟨hα_pos, hα_le, hα_lb, hα_ub⟩
private def ltM1K2TrigPair100 : (TcIv × TcIv) × (TcIv × TcIv) :=
  (tcTrigIv100 (Int.ofNat 9295280) (Int.ofNat 1000000000) (Int.ofNat 464764000001000000000)
  (Int.ofNat 50000000000000000000000), tcTrigIv100 (Int.ofNat 657275552102752857840) (Int.ofNat
  100000000000000000000000) (Int.ofNat 32863777605210212626118657000000000) (Int.ofNat
  5000000000000000000000000000000000000))
private theorem ltM1K2_yHi0_le : -((-((464764000001000000000 : ℤ) * tcAmpScale)) / (((2 : ℤ) ^
  tcTrigHalvings) * (50000000000000000000000 : ℤ))) ≤ tcAmpScale := ltM1K2_scale_yHi_aux.2.2.1
private theorem ltM1K2_yHi1_le : -((-((32863777605210212626118657000000000 : ℤ) * tcAmpScale)) /
  (((2 : ℤ) ^ tcTrigHalvings) * (5000000000000000000000000000000000000 : ℤ))) ≤ tcAmpScale :=
  ltM1K2_scale_yHi_aux.2.2.2
private theorem ltM1K2TrigPair100_sound {n : ℕ} (hn96 : 96 ≤ n) :
    let K_blk := swLKBlk n 2 9295280 1000000000; let N : ℕ := 2 ^ n
    let cs : Fin 2 → ℝ × ℝ := fun w ↦ (Real.cos ((K_blk : ℝ) * swLThetaShiftReal N 2 w.1), Real.sin
      ((K_blk : ℝ) * swLThetaShiftReal N 2 w.1))
    (tcMemAmpIv (cs ⟨0, by omega⟩).1 ltM1K2TrigPair100.1.1 ∧ tcMemAmpIv (cs ⟨0, by omega⟩).2
      ltM1K2TrigPair100.1.2) ∧ (tcMemAmpIv (cs ⟨1, by omega⟩).1 ltM1K2TrigPair100.2.1 ∧ tcMemAmpIv
      (cs ⟨1, by omega⟩).2 ltM1K2TrigPair100.2.2) := by
  intro K_blk N cs; unfold ltM1K2TrigPair100; simp only [tcInt_ofNat_eq, Nat.cast_ofNat]
  have hN96 : (79228162514264337593543950336 : ℝ) ≤ (N : ℝ) := by
    have hpow : 2 ^ 96 ≤ 2 ^ n := Nat.pow_le_pow_right (by omega) hn96; have hpow_r : ((2 ^ 96 : ℕ)
      : ℝ) ≤ (N : ℝ) := (by dsimp [N]; exact_mod_cast hpow); have hval : ((2 ^ 96 : ℕ) : ℝ) =
      79228162514264337593543950336 := (by norm_num); linarith
  have hN_pos : (0 : ℝ) < (N : ℝ) := (by linarith); set c₁ : ℝ := (N : ℝ) / (2 : ℕ)
  have hc1_ge : (199000000000000 : ℝ) ^ 2 ≤ c₁ := (by dsimp [c₁]; norm_num; linarith)
  have hsqrt_c1_ge : (199000000000000 : ℝ) ≤ √c₁ := by
    rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 199000000000000)]; exact Real.sqrt_le_sqrt hc1_ge
  have hx0_pos : 0 < 1 / √c₁ := (by positivity); have hx0_ub : 1 / √c₁ ≤ 1 / 199000000000000 :=
    one_div_le_one_div_of_le (by norm_num) hsqrt_c1_ge
  rcases ltM1K2_arcsin_bounds hx0_pos hx0_ub with ⟨hα_pos, hα_le, hα_lb, hα_ub⟩; set α₀ : ℝ :=
    Real.arcsin (1 / √c₁); set tauR : ℝ := (9295280 : ℝ) / (1000000000 : ℝ)
  have htau_nn : 0 ≤ tauR := (by dsimp [tauR]; norm_num)
  have hK_eq : K_blk = (round (tauR / (2 * α₀))).toNat + 1 :=
    (by simp only [K_blk, swLKBlk, tauR, α₀, c₁, N, Nat.cast_pow, Nat.cast_ofNat])
  rcases odd_round_div_sub_mem_Icc hα_pos htau_nn with ⟨hodd_lo, hodd_hi⟩; have hφ0_lo : tauR ≤ 2 *
    (K_blk : ℝ) * α₀ := (by rw [hK_eq, Nat.cast_add, Nat.cast_one]; linarith); have hφ0_hi : 2 *
    (K_blk : ℝ) * α₀ ≤ tauR + 3 * α₀ := (by rw [hK_eq, Nat.cast_add, Nat.cast_one]; linarith)
  have hφ0_hi_q1 : 2 * (K_blk : ℝ) * α₀ ≤ ((464764000001000000000 : ℤ) : ℝ) /
    ((50000000000000000000000 : ℤ) : ℝ) := by
    have hq1 : ((464764000001000000000 : ℤ) : ℝ) / ((50000000000000000000000 : ℤ) : ℝ) = tauR + 1 /
      (50000000000000 : ℝ) := (by dsimp [tauR]; norm_num); rw [hq1]; have hnum : (3 : ℝ) * (1 /
      190000000000000) ≤ 1 / (50000000000000 : ℝ) := (by norm_num); have h3α : 3 * α₀ ≤ 1 /
      (50000000000000 : ℝ) := le_trans (mul_le_mul_of_nonneg_left hα_le (by norm_num)) hnum
    exact le_trans hφ0_hi (add_le_add (le_refl tauR) h3α)
  have hθ0_eq : swLThetaShiftReal N 2 0 = 2 * α₀ := by
    unfold swLThetaShiftReal; simp only [Nat.cast_zero, mul_zero, sub_zero, Nat.cast_ofNat, α₀, c₁]
    congr 2; rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_div hN_pos.le, one_div_div]
  have hφ0_eq : (K_blk : ℝ) * swLThetaShiftReal N 2 0 = 2 * (K_blk : ℝ) * α₀ := by rw [hθ0_eq]; ring
  constructor
  · dsimp only [cs]; rw [hφ0_eq]; exact tcTrigIv100_sound (a := 9295280) (d := 1000000000)
      (b := 464764000001000000000) (e := 50000000000000000000000)
      (by omega) (by omega) (by omega)
      (by simpa [tauR] using hφ0_lo) hφ0_hi_q1 ltM1K2_yHi0_le
  · have hN2_pos : (0 : ℝ) < (N : ℝ) - 2 := (by linarith); set x1 : ℝ := √(1 / ((N : ℝ) - 2))
    have hx1_pos : 0 < x1 := Real.sqrt_pos.2 (div_pos one_pos hN2_pos); have hx1_sq : x1 ^ 2 = 1 /
      ((N : ℝ) - 2) := Real.sq_sqrt (div_nonneg zero_le_one hN2_pos.le)
    have hx1_ub : x1 ≤ 1 / 199000000000000 := by
      have hsq : x1 ^ 2 ≤ (1 / 199000000000000 : ℝ) ^ 2 :=
        (by rw [hx1_sq, div_le_iff₀ hN2_pos]; linarith); rw [← Real.sqrt_sq hx1_pos.le, ←
        Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 1 / 199000000000000)]; exact Real.sqrt_le_sqrt hsq
    rcases ltM1K2_arcsin_bounds hx1_pos hx1_ub with ⟨_, _, hβ_lb, hβ_ub⟩
    set β : ℝ := Real.arcsin x1; have hθ1_eq : swLThetaShiftReal N 2 1 = 2 * β :=
      (by unfold swLThetaShiftReal; dsimp only [β, x1]; norm_num); have hx0_sq : (1 / √c₁) ^ 2 = 2 /
      (N : ℝ) := (by dsimp [c₁]; rw [div_pow, one_pow, Real.sq_sqrt (by positivity), one_div_div])
    have hlo_sq : ((70710678118654 : ℝ) / (100000000000000 : ℝ)) ^ 2 * (1 / √c₁) ^ 2 ≤ x1 ^ 2 := by
      rw [hx0_sq, hx1_sq]; have h1 :
          ((70710678118654 : ℝ) / (100000000000000 : ℝ)) ^ 2 * (2 / (N : ℝ)) ≤ 1 / (N : ℝ) := by
        have hnum : ((70710678118654 : ℝ) / (100000000000000 : ℝ)) ^ 2 * 2 ≤ 1 := (by norm_num)
        rw [mul_div_assoc', div_le_div_iff₀ hN_pos hN_pos]; nlinarith
      exact h1.trans (one_div_le_one_div_of_le hN2_pos (by linarith))
    have hxk_ge : ((70710678118654 : ℝ) / (100000000000000 : ℝ)) * (1 / √c₁) ≤ x1 := by
      have hnn : (0 : ℝ) ≤ ((70710678118654 : ℝ) / (100000000000000 : ℝ)) * (1 / √c₁) :=
        (by positivity)
      rw [← Real.sqrt_sq hnn, ← Real.sqrt_sq hx1_pos.le]; exact Real.sqrt_le_sqrt (by rwa [mul_pow])
    have hβ_ge : ((70710678118653 : ℝ) / (100000000000000 : ℝ)) * α₀ ≤ β := by
      have hrat : ((70710678118653 : ℝ) / (100000000000000 : ℝ)) ≤ ((70710678118654 : ℝ) /
        (100000000000000 : ℝ)) * (1 - 1 / 100000000000000000000) := (by norm_num)
      have h1 : ((70710678118653 : ℝ) / (100000000000000 : ℝ)) * α₀ ≤ ((70710678118654 : ℝ) /
        (100000000000000 : ℝ)) * ((1 - 1 / 100000000000000000000) * α₀) :=
        (by rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right hrat hα_pos.le)
      have h2 : ((70710678118654 : ℝ) / (100000000000000 : ℝ)) * ((1 - 1 / 100000000000000000000) *
        α₀) ≤ ((70710678118654 : ℝ) / (100000000000000 : ℝ)) * (1 / √c₁) :=
        mul_le_mul_of_nonneg_left hα_ub (by norm_num)
      exact ((h1.trans h2).trans hxk_ge).trans hβ_lb
    have hhi_sq : x1 ^ 2 ≤ ((70710678118656 : ℝ) / (100000000000000 : ℝ)) ^ 2 * (1 / √c₁) ^ 2 :=
      (by rw [hx0_sq, hx1_sq, mul_div_assoc', div_le_div_iff₀ hN2_pos hN_pos]; nlinarith)
    have hxk_le : x1 ≤ ((70710678118656 : ℝ) / (100000000000000 : ℝ)) * (1 / √c₁) := by
      have hnn : (0 : ℝ) ≤ ((70710678118656 : ℝ) / (100000000000000 : ℝ)) * (1 / √c₁) :=
        (by positivity)
      rw [← Real.sqrt_sq hx1_pos.le, ← Real.sqrt_sq hnn]; exact Real.sqrt_le_sqrt (by rwa [mul_pow])
    have hβ_le : β ≤ ((70710678118657 : ℝ) / (100000000000000 : ℝ)) * α₀ := by
      have h1 : x1 ≤ ((70710678118656 : ℝ) / (100000000000000 : ℝ)) * α₀ := hxk_le.trans
        (mul_le_mul_of_nonneg_left hα_lb (by norm_num)); have hrat : ((70710678118656 : ℝ) /
        (100000000000000 : ℝ)) ≤ (1 - 1 / 100000000000000000000) * ((70710678118657 : ℝ) /
        (100000000000000 : ℝ)) := (by norm_num); have h2 : ((70710678118656 : ℝ) / (100000000000000
        : ℝ)) * α₀ ≤ (1 - 1 / 100000000000000000000) * (((70710678118657 : ℝ) / (100000000000000 :
        ℝ)) * α₀) := (by rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right hrat hα_pos.le)
      exact le_of_mul_le_mul_left ((hβ_ub.trans h1).trans h2) (by norm_num)
    have hφ1_lo : (((657275552102752857840 : ℤ) : ℝ) / ((100000000000000000000000 : ℤ) : ℝ)) ≤
      (K_blk : ℝ) * swLThetaShiftReal N 2 1 := by
      rw [hθ1_eq]
      have hm1 : (K_blk : ℝ) * (((70710678118653 : ℝ) / (100000000000000 : ℝ)) * (2 * α₀)) ≤ (K_blk
        : ℝ) * (2 * β) := mul_le_mul_of_nonneg_left (by linarith [hβ_ge]) (Nat.cast_nonneg K_blk)
      have hm2 : ((70710678118653 : ℝ) / (100000000000000 : ℝ)) * tauR ≤ ((70710678118653 : ℝ) /
        (100000000000000 : ℝ)) * (2 * (K_blk : ℝ) * α₀) := mul_le_mul_of_nonneg_left hφ0_lo
        (by norm_num); have hval : (((657275552102752857840 : ℤ) : ℝ) / ((100000000000000000000000 :
        ℤ) : ℝ)) = ((70710678118653 : ℝ) / (100000000000000 : ℝ)) * tauR :=
        (by dsimp [tauR]; norm_num); linarith
    have hφ1_hi : (K_blk : ℝ) * swLThetaShiftReal N 2 1 ≤ (((32863777605210212626118657000000000 :
      ℤ) : ℝ) / ((5000000000000000000000000000000000000 : ℤ) : ℝ)) := by
      rw [hθ1_eq]
      have hm1 : (K_blk : ℝ) * (2 * β) ≤ (K_blk : ℝ) * (((70710678118657 : ℝ) / (100000000000000 :
        ℝ)) * (2 * α₀)) := mul_le_mul_of_nonneg_left (by linarith [hβ_le]) (Nat.cast_nonneg K_blk)
      have hm2 : ((70710678118657 : ℝ) / (100000000000000 : ℝ)) * (2 * (K_blk : ℝ) * α₀) ≤
        ((70710678118657 : ℝ) / (100000000000000 : ℝ)) * (((464764000001000000000 : ℤ) : ℝ) /
        ((50000000000000000000000 : ℤ) : ℝ)) := mul_le_mul_of_nonneg_left hφ0_hi_q1 (by norm_num)
      have hval : (((32863777605210212626118657000000000 : ℤ) : ℝ) /
        ((5000000000000000000000000000000000000 : ℤ) : ℝ)) = ((70710678118657 : ℝ) /
        (100000000000000 : ℝ)) * (((464764000001000000000 : ℤ) : ℝ) / ((50000000000000000000000 : ℤ)
        : ℝ)) := (by norm_num); linarith
    dsimp only [cs]
    exact tcTrigIv100_sound (a := 657275552102752857840) (d := 100000000000000000000000) (b :=
      32863777605210212626118657000000000) (e := 5000000000000000000000000000000000000) (by omega)
      (by omega) (by omega) hφ1_lo hφ1_hi ltM1K2_yHi1_le
/-- Pulse chunk 0 (`90` `(u0, v)` pairs over `10^9`) for `(m = 1, k = 2)`. -/
private def ltM1K2RawChunk0 : List (ℤ × ℤ) := [
  (7459786, 0), (7460319, 0), (7461084, 0),
  (7460240, 0), (7458351, 0), (7456797, 0),
  (7455262, 0), (7453508, 0), (7450945, 0),
  (7448035, 0), (7444601, 0), (7440966, 0),
  (7437048, 0), (7432801, 0), (7428095, 0),
  (7422983, 0), (7417482, 0), (7411752, 0),
  (7405745, 0), (7399417, 0), (7392756, 0),
  (7385818, 0), (7378606, 0), (7371096, 0),
  (7363236, 0), (7355070, 0), (7346635, 0),
  (7337908, 0), (7328842, 0), (7319444, 0),
  (7309764, 0), (7299826, 0), (7289587, 0),
  (7278995, 0), (7268122, 0), (7257031, 0),
  (7245706, 0), (7234064, 0), (7222122, 0),
  (7209972, 0), (7197655, 0), (7185086, 0),
  (7172257, 0), (7159197, 0), (7145980, 0),
  (7132564, 0), (7118930, 0), (7105098, 0),
  (7091064, 0), (7076833, 0), (7062409, 0),
  (7047807, 0), (7033003, 0), (7017980, 0),
  (7002733, 0), (6987306, 0), (6971685, 0),
  (6955852, 0), (6939781, 0), (6923505, 0),
  (6907027, 0), (6890340, 0), (6873439, 0),
  (6856329, 0), (6839014, 0), (6821498, 0),
  (6803786, 0), (6785882, 0), (6767793, 0),
  (6749522, 0), (6731072, 0), (6712449, 0),
  (6693661, 0), (6674721, 0), (6655643, 0),
  (6636421, 0), (6617028, 0), (6597511, 0),
  (6577897, 0), (6558175, 0), (6538312, 0),
  (6518340, 0), (6498288, 0), (6478144, 0),
  (6457914, 0), (6437611, 0), (6417232, 0),
  (6396778, 0), (6376263, 0), (6355701, 0)
]
/-- Pulse chunk 1 (`90` `(u0, v)` pairs over `10^9`) for `(m = 1, k = 2)`. -/
private def ltM1K2RawChunk1 : List (ℤ × ℤ) := [
  (6335091, 0), (6314430, 0), (6293725, 0),
  (6272981, 0), (6252202, 0), (6231387, 0),
  (6210535, 0), (6189654, 0), (6168753, 0),
  (6147830, 0), (6126857, 0), (6105832, 0),
  (6084784, 0), (6063742, 0), (6042650, 0),
  (6021486, 0), (6000272, 0), (5979042, 0),
  (5957770, 0), (5936442, 0), (5915072, 0),
  (5893641, 0), (5872138, 0), (5850588, 0),
  (5829026, 0), (5807416, 0), (5785723, 0),
  (5763974, 0), (5742210, 0), (5720428, 0),
  (5698603, 0), (5676745, 0), (5654870, 0),
  (5632992, 0), (5611115, 0), (5589246, 0),
  (5567394, 0), (5545565, 0), (5523769, 0),
  (5502018, 0), (5480320, 0), (5458687, 0),
  (5437130, 0), (5415652, 0), (5394252, 0),
  (5372933, 0), (5351731, 0), (5330661, 0),
  (5309694, 0), (5288815, 0), (5268056, 0),
  (5247447, 0), (5226963, 0), (5206605, 0),
  (5186385, 0), (5166283, 0), (5146280, 0),
  (5126411, 0), (5106715, 0), (5087124, 0),
  (5067621, 0), (5048223, 0), (5028941, 0),
  (5009740, 0), (4990644, 0), (4971664, 0),
  (4952726, 0), (4933816, 0), (4914972, 0),
  (4896206, 0), (4877467, 0), (4858754, 0),
  (4840078, 0), (4821389, 0), (4802696, 0),
  (4784032, 0), (4765428, 0), (4746819, 0),
  (4728171, 0), (4709540, 0), (4691000, 0),
  (4672543, 0), (4654114, 0), (4635717, 0),
  (4617452, 0), (4599385, 0), (4581444, 0),
  (4563642, 0), (4546022, 0), (4528685, 0)
]
/-- Pulse chunk 2 (`90` `(u0, v)` pairs over `10^9`) for `(m = 1, k = 2)`. -/
private def ltM1K2RawChunk2 : List (ℤ × ℤ) := [
  (4511599, 0), (4494741, 0), (4478098, 0),
  (4461769, 0), (4445751, 0), (4430003, 0),
  (4414425, 0), (4399078, 0), (4384003, 0),
  (4369159, 0), (4354400, 0), (4339719, 0),
  (4325141, 0), (4310695, 0), (4296268, 0),
  (4281830, 0), (4267412, 0), (4253010, 0),
  (4238645, 0), (4224326, 0), (4210099, 0),
  (4195966, 0), (4181947, 0), (4168112, 0),
  (4154513, 0), (4141116, 0), (4127878, 0),
  (4114799, 0), (4101918, 0), (4089225, 0),
  (4076681, 0), (4064190, 0), (4051845, 0),
  (4039524, 0), (4026953, 0), (4013784, 0),
  (4000252, 0), (3987029, 0), (3975483, 0),
  (3964726, 0), (3952247, 0), (3935808, 0),
  (3920437, 1640774), (3894732, 9091883), (3700427, 28451394),
  (2796050, 67442301), (2352903, 79057399), (2249730, 81378002),
  (2283726, 80423180), (2329419, 79045451), (2352489, 78153314),
  (2364284, 77574606), (2369647, 77229800), (2367839, 77086383),
  (2362913, 77026557), (2355433, 77024260), (2346361, 77063703),
  (2336552, 77129418), (2326826, 77205335), (2317105, 77278142),
  (2307163, 77358420), (2297247, 77430722), (2287805, 77494061),
  (2278563, 77550442), (2269190, 77602141), (2259749, 77650463),
  (2250351, 77689078), (2241147, 77720603), (2231865, 77748973),
  (2222567, 77775255), (2213236, 77799714), (2203861, 77822521),
  (2194539, 77843838), (2185360, 77862928), (2176317, 77881055),
  (2167342, 77900112), (2158424, 77919978), (2149686, 77939554),
  (2141279, 77957573), (2133080, 77973229), (2125049, 77991831),
  (2117049, 78012648), (2109306, 78032500), (2101815, 78051512),
  (2094480, 78070998), (2087258, 78091570), (2080212, 78112582),
  (2073426, 78130083), (2066688, 78148811), (2059963, 78169148)
]
/-- Pulse chunk 3 (`90` `(u0, v)` pairs over `10^9`) for `(m = 1, k = 2)`. -/
private def ltM1K2RawChunk3 : List (ℤ × ℤ) := [
  (2053267, 78190424), (2046677, 78211892), (2040195, 78233368),
  (2033637, 78255046), (2027226, 78275377), (2020685, 78295464),
  (2014197, 78315349), (2007747, 78335340), (2001262, 78355848),
  (1994682, 78376815), (1987986, 78397444), (1981377, 78416519),
  (1974694, 78435844), (1968018, 78455522), (1961301, 78475349),
  (1954503, 78495209), (1947625, 78515038), (1940567, 78534840),
  (1933707, 78554578), (1926761, 78574281), (1919862, 78593896),
  (1912972, 78613372), (1906009, 78632698), (1898997, 78651886),
  (1891910, 78670947), (1885078, 78689923), (1878189, 78708843),
  (1871391, 78726925), (1864724, 78743428), (1858065, 78758511),
  (1851399, 78774482), (1844642, 78794747), (1838004, 78814518),
  (1831515, 78832095), (1825141, 78848091), (1818836, 78863666),
  (1812582, 78879107), (1806349, 78895422), (1800127, 78913390),
  (1793994, 78929748), (1787962, 78944043), (1781983, 78958104),
  (1776025, 78973683), (1770131, 78989869), (1764262, 79005866),
  (1758285, 79021226), (1752470, 79034358), (1746795, 79045924),
  (1741144, 79057742), (1735287, 79071145), (1729398, 79084936),
  (1723607, 79098188), (1717941, 79111004), (1712015, 79123447),
  (1706200, 79135516), (1700525, 79147203), (1694709, 79158517),
  (1688799, 79169428), (1682931, 79180039), (1677104, 79190939),
  (1670993, 79203931), (1664940, 79217026), (1659116, 79228417),
  (1653333, 79238479), (1647501, 79248016), (1641556, 79257540),
  (1635487, 79267032), (1629689, 79276477), (1623894, 79285904),
  (1617906, 79295347), (1612078, 79304804), (1606365, 79314274),
  (1600701, 79323765), (1595027, 79333293), (1589365, 79342883),
  (1583745, 79352565), (1578194, 79362148), (1572736, 79371019),
  (1567393, 79378149), (1562133, 79384927), (1556912, 79393288),
  (1551729, 79402931), (1546602, 79413141), (1541555, 79423122),
  (1536607, 79431901), (1531758, 79439088), (1526965, 79446561),
  (1522198, 79455924), (1517484, 79465810), (1512864, 79474469)
]
/-- Pulse chunk 4 (`90` `(u0, v)` pairs over `10^9`) for `(m = 1, k = 2)`. -/
private def ltM1K2RawChunk4 : List (ℤ × ℤ) := [
  (1508349, 79481687), (1503912, 79490678), (1499537, 79501123),
  (1495184, 79511037), (1490741, 79519212), (1486301, 79526594),
  (1482077, 79534100), (1478243, 79542087), (1473863, 79552698),
  (1469535, 79564124), (1465375, 79574668), (1461118, 79583843),
  (1456964, 79592437), (1453130, 79601258), (1449466, 79610312),
  (1445044, 79619609), (1440749, 79629122), (1436712, 79638821),
  (1432751, 79648703), (1428673, 79658779), (1424414, 79669068),
  (1420193, 79679585), (1416304, 79690353), (1412328, 79699944),
  (1408189, 79708302), (1403871, 79716246), (1399714, 79725570),
  (1395970, 79737166), (1391804, 79748851), (1387527, 79760669),
  (1383284, 79770855), (1379099, 79779734), (1374941, 79788698),
  (1370774, 79799158), (1366581, 79811492), (1362374, 79823913),
  (1358170, 79836142), (1353979, 79846697), (1349792, 79856179),
  (1345587, 79866206), (1341356, 79877872), (1337115, 79890480),
  (1332904, 79900049), (1328712, 79909046), (1324523, 79917958),
  (1320323, 79927446), (1316102, 79938291), (1311860, 79950559),
  (1307613, 79962977), (1303380, 79972119), (1299120, 79982383),
  (1294816, 79994062), (1290473, 80006057), (1286118, 80016792),
  (1281794, 80025775), (1277599, 80034422), (1273771, 80043002),
  (1269369, 80053507), (1264675, 80065141), (1260059, 80076615),
  (1255984, 80086574), (1252444, 80094742), (1248184, 80102818),
  (1242987, 80110763), (1238850, 80121030), (1234983, 80132026),
  (1230890, 80142378), (1226258, 80151183), (1221275, 80158463),
  (1217401, 80165591), (1214026, 80172940), (1209757, 80182548),
  (1205254, 80192504), (1200748, 80201441), (1196205, 80208817),
  (1191717, 80214970), (1188553, 80220927), (1184982, 80227876),
  (1180798, 80236558), (1176541, 80245112), (1172466, 80252356),
  (1168570, 80258107), (1164643, 80263016), (1160424, 80267721),
  (1156806, 80274120), (1153706, 80281809), (1150348, 80288906),
  (1146436, 80294375), (1142225, 80298375), (1138504, 80301960)
]
/-- Pulse chunk 5 (`90` `(u0, v)` pairs over `10^9`) for `(m = 1, k = 2)`. -/
private def ltM1K2RawChunk5 : List (ℤ × ℤ) := [
  (1136244, 80305344), (1132681, 80308527), (1128770, 80311725),
  (1125290, 80315998), (1122468, 80321509), (1119910, 80327220),
  (1116645, 80331246), (1112269, 80333178), (1109478, 80334908),
  (1106928, 80337102), (1104467, 80340431), (1102036, 80344725),
  (1099394, 80348820), (1096044, 80350856), (1092266, 80351560),
  (1089985, 80352105), (1087806, 80352483), (1085408, 80352689),
  (1082777, 80353120), (1079919, 80354621), (1076816, 80358282),
  (1074011, 80361006), (1072346, 80361306), (1070321, 80360780),
  (1067708, 80360046), (1064737, 80359217), (1061609, 80358288),
  (1058449, 80357254), (1056114, 80356112), (1054527, 80354863),
  (1052200, 80353513), (1049101, 80352360), (1045919, 80351916),
  (1043332, 80352747), (1041752, 80355272), (1038666, 80355146),
  (1035140, 80353893), (1032355, 80352256), (1030175, 80350561),
  (1027748, 80348877), (1024427, 80347211), (1020243, 80345573),
  (1017731, 80343964), (1015344, 80342391), (1012948, 80340863),
  (1010307, 80339393), (1007038, 80337992), (1002984, 80336670),
  (998672, 80335439), (996049, 80334298), (993543, 80331891),
  (991027, 80328038), (988263, 80323850), (984751, 80320975),
  (980483, 80320024), (976800, 80319502), (974547, 80319096),
  (971505, 80318826), (967639, 80318555), (963773, 80317629),
  (960670, 80315212), (958297, 80311724), (954912, 80310141),
  (950543, 80310418), (947310, 80311299), (944929, 80311959),
  (942376, 80311780), (939223, 80310336), (935519, 80308470),
  (932099, 80308993), (928869, 80310528), (925769, 80310397),
  (922749, 80308839), (919777, 80307245), (916831, 80305964),
  (913906, 80305979), (910999, 80308767), (908130, 80311485),
  (905320, 80312694), (902589, 80312790), (899963, 80312918),
  (897486, 80313306), (895235, 80313956), (893177, 80315024),
  (890536, 80317810), (887136, 80322526), (883863, 80327589),
  (881784, 80331054), (880214, 80333570), (877911, 80336150)
]
/-- Pulse chunk 6 (`90` `(u0, v)` pairs over `10^9`) for `(m = 1, k = 2)`. -/
private def ltM1K2RawChunk6 : List (ℤ × ℤ) := [
  (874617, 80339021), (872346, 80342181), (870949, 80345628),
  (869334, 80349368), (866651, 80353398), (863921, 80357721),
  (862362, 80362334), (861602, 80366985), (859699, 80369517),
  (856999, 80371315), (854264, 80374453), (851601, 80379570),
  (849698, 80385845), (848850, 80392380), (848258, 80399178),
  (846395, 80406245), (843678, 80412743), (840991, 80417917),
  (838312, 80422102), (836601, 80427633), (835825, 80435446),
  (834662, 80443948), (832263, 80452783), (829697, 80460779),
  (828284, 80467124), (827283, 80473002), (825279, 80480659),
  (822408, 80489868), (820170, 80498221), (818896, 80505148),
  (817347, 80512583), (814259, 80522474), (811091, 80532467),
  (808808, 80540896), (807174, 80548115), (805483, 80555282),
  (803607, 80562843), (801587, 80571939), (799465, 80583426),
  (797271, 80594239), (795019, 80603433), (792730, 80611788),
  (790411, 80620126), (788056, 80629224), (785657, 80639935),
  (783213, 80652504), (780717, 80663703), (778144, 80673424),
  (775483, 80682621), (772705, 80691768), (769760, 80701014),
  (766600, 80710349), (763336, 80719766), (761393, 80729254),
  (759747, 80739387), (757321, 80750807), (753718, 80763897),
  (750096, 80776756), (747562, 80787629), (745408, 80797632),
  (743192, 80807505), (740868, 80817412), (738489, 80827352),
  (736096, 80837317), (733716, 80847301), (731223, 80857294),
  (728127, 80867291), (723573, 80877278), (719166, 80887256),
  (715594, 80897217), (712784, 80907156), (711106, 80917064),
  (710723, 80926935), (709237, 80936765), (706618, 80946542),
  (703649, 80956272), (700645, 80965949), (697676, 80975565),
  (694714, 80985114), (691731, 80994589), (688701, 81003982),
  (685782, 81013286), (683843, 81022503), (682782, 81031628),
  (681604, 81040659), (679439, 81049589), (676322, 81058411),
  (673241, 81067119), (670705, 81075706), (669156, 81084175)
]
/-- Pulse chunk 7 (`90` `(u0, v)` pairs over `10^9`) for `(m = 1, k = 2)`. -/
private def ltM1K2RawChunk7 : List (ℤ × ℤ) := [
  (668274, 81092523), (667043, 81100746), (664765, 81108839),
  (661937, 81116796), (659165, 81124608), (657294, 81132275),
  (656412, 81139797), (655980, 81147172), (654944, 81154397),
  (652728, 81161466), (650408, 81168375), (648183, 81175116),
  (646010, 81181691), (643957, 81188098), (642393, 81194335),
  (641912, 81200400), (642488, 81206289), (642018, 81211999),
  (640438, 81217520), (638821, 81222861), (637292, 81228018),
  (635880, 81232989), (634573, 81237771), (633368, 81242363),
  (632281, 81246760), (631313, 81250956), (630444, 81254957),
  (629680, 81258762), (629026, 81262367), (628453, 81265772),
  (627633, 81268976), (624687, 81271974), (622312, 81274764),
  (621114, 81277348), (620715, 81279725), (620619, 81281896),
  (620454, 81283858), (619912, 81285611), (617130, 81287151),
  (615576, 81288481), (615067, 81289599), (614550, 81290506),
  (613280, 81291202), (611383, 81291686), (610061, 81291960),
  (610739, 81292018), (609966, 81291864), (608440, 81291499),
  (606575, 81290925), (604645, 81290138), (602785, 81289139),
  (600980, 81287931), (599255, 81286509), (597569, 81284879),
  (595915, 81283039), (594288, 81280990), (592687, 81278986),
  (591113, 81277682), (589569, 81278260), (588085, 81279486),
  (586644, 81277721), (585249, 81274681), (583910, 81271213),
  (582442, 81267548), (580337, 81263696), (576527, 81259704),
  (573304, 81256760), (571492, 81255792), (570289, 81254305),
  (569184, 81251257), (567833, 81246831), (565754, 81241655),
  (561923, 81236301), (559435, 81230769), (558030, 81225060),
  (556128, 81220682), (553332, 81217694), (550328, 81214890),
  (548073, 81210792), (547259, 81204229), (544699, 81197504),
  (541562, 81190891), (539170, 81185684), (537663, 81181750),
  (536141, 81177606), (533658, 81171799), (530189, 81164306),
  (528921, 81160017), (527727, 81155667), (525673, 81149820)
]
/-- Pulse chunk 8 (`90` `(u0, v)` pairs over `10^9`) for `(m = 1, k = 2)`. -/
private def ltM1K2RawChunk8 : List (ℤ × ℤ) := [
  (522686, 81142827), (519223, 81136187), (515824, 81131107),
  (512727, 81126426), (511713, 81118401), (510345, 81109518),
  (507948, 81100510), (505090, 81091918), (502858, 81084775),
  (501983, 81079630), (501295, 81074706), (500603, 81069689),
  (498838, 81062929), (496072, 81054535), (493150, 81045806),
  (491060, 81038218), (490317, 81032145), (489547, 81024294),
  (488753, 81014558), (486640, 81006166), (483529, 80999529),
  (480613, 80993419), (478591, 80987307), (477613, 80980414),
  (476568, 80971241), (475452, 80961089), (474272, 80952485),
  (473032, 80945625), (471732, 80939125), (470367, 80932558),
  (468912, 80925935), (467382, 80919216), (465757, 80911530),
  (464036, 80902009), (462671, 80891645), (462258, 80882508),
  (462609, 80874793), (462562, 80867815), (460715, 80860796),
  (458398, 80853741), (455964, 80846650), (453934, 80839524),
  (453107, 80832366), (453119, 80825179), (453150, 80817971),
  (453015, 80810663), (451473, 80801396), (448798, 80790594),
  (446145, 80780024), (444603, 80771352), (443793, 80764031),
  (442811, 80756703), (441670, 80749364), (440358, 80742020),
  (438876, 80734671), (437227, 80727319), (435405, 80719963),
  (433397, 80712613), (431262, 80705268), (429169, 80697927),
  (428425, 80690594), (428942, 80684693), (429390, 80678737),
  (429775, 80672729), (430102, 80666670), (430376, 80660561),
  (430601, 80654406), (430781, 80648204), (430919, 80641960),
  (431020, 80635673), (431085, 80629345), (431119, 80622979),
  (431124, 80616576), (431101, 80610137), (431055, 80603664),
  (430985, 80597159), (430895, 80590623), (430785, 80584057),
  (430658, 80577463), (430515, 80570842), (430356, 80564196),
  (430183, 80557526), (429997, 80550833), (429798, 80544119),
  (429587, 80537385), (429365, 80530633), (429133, 80523862),
  (428890, 80517076), (428637, 80510274), (428374, 80503458)
]
/-- Pulse chunk 9 (`90` `(u0, v)` pairs over `10^9`) for `(m = 1, k = 2)`. -/
private def ltM1K2RawChunk9 : List (ℤ × ℤ) := [
  (428101, 80496630), (427818, 80489789), (427526, 80482938),
  (427224, 80476078), (426912, 80469209), (426591, 80462333),
  (426259, 80455450), (425916, 80448562), (425564, 80441670),
  (425200, 80434774), (424825, 80427875), (424439, 80420975),
  (424040, 80414074), (423630, 80407174), (423206, 80400274),
  (422770, 80393377), (422320, 80386482), (421856, 80379591),
  (421377, 80372704), (420884, 80365822), (420376, 80358946),
  (419852, 80352077), (419312, 80345215), (418755, 80338362),
  (418181, 80331517), (417590, 80324682), (416981, 80317857),
  (416353, 80311043), (415707, 80304240), (415042, 80297450),
  (414358, 80290672), (413653, 80283907), (412929, 80277157),
  (412184, 80270421), (411419, 80263701), (410632, 80256995),
  (409824, 80250307), (408995, 80243634), (408143, 80236979),
  (407270, 80230342), (406374, 80223723), (405456, 80217123),
  (404515, 80210542), (403551, 80203980), (402565, 80197439),
  (401555, 80190918), (400522, 80184418), (399466, 80177939),
  (398387, 80171482), (397284, 80165048), (396158, 80158635),
  (395009, 80152246), (393837, 80145879), (392641, 80139537),
  (391423, 80133218), (390181, 80126923), (388917, 80120653),
  (387629, 80114408), (386319, 80108188), (384987, 80101993),
  (383632, 80095825), (382255, 80089682), (380857, 80083565),
  (379436, 80077475), (377995, 80071412), (376532, 80065375),
  (375049, 80059366), (373546, 80053385), (372022, 80047431),
  (370478, 80041505), (368915, 80035607), (367333, 80029737),
  (365733, 80023896), (364114, 80018083), (362478, 80012300),
  (360824, 80006545), (359153, 80000819), (357466, 79995123),
  (355763, 79989456), (354044, 79983818), (352311, 79978211),
  (350563, 79972633), (348801, 79967085), (347025, 79961567),
  (345237, 79956079), (343436, 79950621), (341624, 79945194),
  (339800, 79939797), (337965, 79934431), (336121, 79929095)
]
/-- Pulse chunk 10 (`90` `(u0, v)` pairs over `10^9`) for `(m = 1, k = 2)`. -/
private def ltM1K2RawChunk10 : List (ℤ × ℤ) := [
  (334267, 79923790), (332404, 79918516), (330533, 79913272),
  (328654, 79908060), (326768, 79902878), (324875, 79897727),
  (322976, 79892607), (321072, 79887518), (319164, 79882460),
  (317251, 79877433), (315335, 79872438), (313417, 79867473),
  (311496, 79862539), (309573, 79857637), (307650, 79852766),
  (305726, 79847926), (303802, 79843116), (301880, 79838339),
  (299959, 79833592), (298040, 79828876), (296125, 79824191),
  (294212, 79819538), (292304, 79814915), (290400, 79810324),
  (288502, 79805763), (286609, 79801233), (284724, 79796735),
  (282845, 79792267), (280974, 79787829), (279111, 79783423),
  (277257, 79779047), (275412, 79774702), (273578, 79770388),
  (271754, 79766104), (269942, 79761850), (268141, 79757627),
  (266352, 79753434), (264576, 79749271), (262814, 79745139),
  (261065, 79741037), (259331, 79736964), (257612, 79732922),
  (255908, 79728910), (254220, 79724927), (252548, 79720974),
  (250894, 79717050), (249256, 79713156), (247637, 79709292),
  (246036, 79705457), (244453, 79701651), (242890, 79697874),
  (241346, 79694126), (239823, 79690407), (238319, 79686717),
  (236837, 79683056), (235376, 79679423), (233936, 79675818),
  (232518, 79672242), (231123, 79668695), (229750, 79665175),
  (228400, 79661684), (227074, 79658220), (225771, 79654784),
  (224492, 79651376), (223238, 79647995), (222007, 79644642),
  (220802, 79641317), (219622, 79638018), (218467, 79634746),
  (217338, 79631502), (216234, 79628284), (215157, 79625093),
  (214106, 79621928), (213081, 79618790), (212083, 79615679),
  (211112, 79612593), (210168, 79609533), (209251, 79606500),
  (208361, 79603492), (207499, 79600510), (206664, 79597553),
  (205857, 79594622), (205078, 79591716), (204327, 79588835),
  (203604, 79585979), (202909, 79583147), (202243, 79580341),
  (201604, 79577559), (200994, 79574802), (200412, 79572068)
]
/-- Pulse chunk 11 (`90` `(u0, v)` pairs over `10^9`) for `(m = 1, k = 2)`. -/
private def ltM1K2RawChunk11 : List (ℤ × ℤ) := [
  (199859, 79569359), (199334, 79566674), (198838, 79564013),
  (198370, 79561376), (197930, 79558762), (197519, 79556171),
  (197136, 79553604), (196782, 79551060), (196456, 79548539),
  (196158, 79546041), (195889, 79543566), (195647, 79541113),
  (195434, 79538683), (195249, 79536275), (195092, 79533889),
  (194963, 79531525), (194862, 79529183), (194788, 79526863),
  (194742, 79524565), (194723, 79522288), (194732, 79520032),
  (194767, 79517798), (194830, 79515584), (194920, 79513392),
  (195036, 79511220), (195179, 79509069), (195348, 79506939),
  (195544, 79504828), (195765, 79502738), (196013, 79500668),
  (196286, 79498618), (196584, 79496588), (196908, 79494578),
  (197256, 79492587), (197630, 79490615), (198028, 79488663),
  (198451, 79486729), (198897, 79484815), (199368, 79482919),
  (199862, 79481043), (200380, 79479184), (200920, 79477345),
  (201484, 79475523), (202071, 79473720), (202679, 79471935),
  (203310, 79470167), (203963, 79468417), (204638, 79466685),
  (205333, 79464971), (206050, 79463274), (206788, 79461594),
  (207546, 79459931), (208324, 79458285), (209123, 79456656),
  (209941, 79455044), (210778, 79453448), (211634, 79451869),
  (212509, 79450306), (213402, 79448759), (214314, 79447228),
  (215243, 79445713), (216190, 79444214), (217154, 79442731),
  (218136, 79441263), (219133, 79439811), (220147, 79438374),
  (221177, 79436952), (222223, 79435546), (223284, 79434154),
  (224360, 79432777), (225450, 79431415), (226556, 79430067),
  (227675, 79428734), (228808, 79427415), (229954, 79426111),
  (231114, 79424821), (232286, 79423544), (233471, 79422282),
  (234668, 79421033), (235877, 79419798), (237098, 79418576),
  (238330, 79417368), (239573, 79416173), (240826, 79414991),
  (242089, 79413823), (243363, 79412667), (244646, 79411524),
  (245939, 79410394), (247241, 79409277), (248551, 79408172)
]
/-- Pulse chunk 12 (`90` `(u0, v)` pairs over `10^9`) for `(m = 1, k = 2)`. -/
private def ltM1K2RawChunk12 : List (ℤ × ℤ) := [
  (249870, 79407080), (251197, 79406000), (252532, 79404932),
  (253874, 79403876), (255223, 79402832), (256580, 79401800),
  (257943, 79400780), (259312, 79399772), (260687, 79398775),
  (262068, 79397790), (263455, 79396816), (264846, 79395853),
  (266242, 79394902), (267643, 79393961), (269049, 79393032),
  (270458, 79392113), (271871, 79391205), (273287, 79390308),
  (274706, 79389422), (276128, 79388546), (277553, 79387680),
  (278981, 79386825), (280410, 79385979), (281841, 79385144),
  (283273, 79384319), (284707, 79383504), (286142, 79382699),
  (287578, 79381903), (289014, 79381118), (290450, 79380341),
  (291887, 79379575), (293323, 79378817), (294758, 79378069),
  (296193, 79377330), (297627, 79376600), (299060, 79375880),
  (300492, 79375168), (301921, 79374465), (303349, 79373771),
  (304775, 79373085), (306199, 79372408), (307620, 79371740),
  (309038, 79371080), (310453, 79370429), (311866, 79369786),
  (313274, 79369151), (314680, 79368524), (316081, 79367905),
  (317479, 79367295), (318872, 79366692), (320262, 79366097),
  (321646, 79365510), (323026, 79364930), (324401, 79364358),
  (325771, 79363794), (327136, 79363237), (328496, 79362687),
  (329850, 79362145), (331198, 79361610), (332540, 79361082),
  (333877, 79360561), (335207, 79360047), (336531, 79359540),
  (337848, 79359040), (339159, 79358547), (340463, 79358061),
  (341760, 79357581), (343050, 79357108), (344333, 79356641),
  (345608, 79356181), (346876, 79355728), (348137, 79355280),
  (349390, 79354839), (350635, 79354404), (351872, 79353976),
  (353101, 79353553), (354322, 79353137), (355535, 79352726),
  (356739, 79352321), (357935, 79351923), (359123, 79351530),
  (360302, 79351142), (361472, 79350761), (362633, 79350385),
  (363785, 79350014), (364929, 79349649), (366063, 79349290),
  (367188, 79348936), (368305, 79348587), (369411, 79348243)
]
/-- Pulse chunk 13 (`90` `(u0, v)` pairs over `10^9`) for `(m = 1, k = 2)`. -/
private def ltM1K2RawChunk13 : List (ℤ × ℤ) := [
  (370509, 79347905), (371597, 79347572), (372675, 79347244),
  (373744, 79346921), (374804, 79346603), (375853, 79346290),
  (376893, 79345981), (377923, 79345678), (378944, 79345379),
  (379954, 79345086), (380955, 79344797), (381946, 79344512),
  (382926, 79344232), (383897, 79343957), (384858, 79343686),
  (385808, 79343419), (386749, 79343157), (387679, 79342900),
  (388599, 79342646), (389509, 79342397), (390409, 79342152),
  (391298, 79341911), (392178, 79341674), (393047, 79341442),
  (393905, 79341213), (394754, 79340988), (395592, 79340768),
  (396420, 79340551), (397237, 79340338), (398044, 79340129),
  (398841, 79339923), (399628, 79339721), (400404, 79339523),
  (401170, 79339329), (401926, 79339138), (402672, 79338951),
  (403407, 79338767), (404132, 79338587), (404846, 79338410),
  (405551, 79338236), (406245, 79338066), (406929, 79337899),
  (407603, 79337736), (408267, 79337575), (408921, 79337418),
  (409564, 79337264), (410198, 79337114), (410821, 79336966),
  (411435, 79336821), (412038, 79336680), (412632, 79336541),
  (413215, 79336405), (413789, 79336272), (414353, 79336142),
  (414907, 79336015), (415452, 79335891), (415986, 79335770),
  (416511, 79335651), (417027, 79335535), (417532, 79335421),
  (418029, 79335311), (418515, 79335203), (418993, 79335097),
  (419461, 79334994), (419919, 79334894), (420368, 79334796),
  (420808, 79334700), (421239, 79334607), (421661, 79334516),
  (422073, 79334428), (422477, 79334342), (422871, 79334258),
  (423257, 79334177), (423634, 79334098), (424002, 79334021),
  (424361, 79333946), (424712, 79333874), (425054, 79333803),
  (425387, 79333735), (425712, 79333669), (426028, 79333604),
  (426337, 79333542), (426636, 79333482), (426928, 79333424),
  (427211, 79333368), (427487, 79333313), (427754, 79333261),
  (428013, 79333211), (428264, 79333162), (428508, 79333115)
]
private def ltM1K2RawChunks : List (List (ℤ × ℤ)) := [
  ltM1K2RawChunk0, ltM1K2RawChunk1, ltM1K2RawChunk2, ltM1K2RawChunk3,
  ltM1K2RawChunk4, ltM1K2RawChunk5, ltM1K2RawChunk6, ltM1K2RawChunk7,
  ltM1K2RawChunk8, ltM1K2RawChunk9, ltM1K2RawChunk10, ltM1K2RawChunk11,
  ltM1K2RawChunk12, ltM1K2RawChunk13
]
private theorem ltM1K2MapPulses_valid (ps : List (ℤ × ℤ)) : (ps.map ltM1K2MkPulse).all swLPulseValid
  = true := by
  rw [List.all_map]; refine List.all_eq_true.2 fun uv _ ↦ ?_; simp [ltM1K2MkPulse, swLPulseValid]
private def ltM1K2St0Iv9 : IvInt := (25273, 25607)
private def ltM1K2St1Iv9 : IvInt := (-39815, -39481)
private def ltM1K2St2Iv9 : IvInt := (703473, 703507)
private def ltM1K2St3Iv9 : IvInt := (883179, 883189)
private abbrev ltM1K2CertStIvs9 : List IvInt :=
  [ltM1K2St0Iv9, ltM1K2St1Iv9, ltM1K2St2Iv9, ltM1K2St3Iv9]
private def ltM1K2CertCumIv9 : IvInt := (999998722, 999998724)
private def ltM1K2CertSurvIv9 : IvInt := (309789647500, 309789647649)
private def ltM1K2TailLbs : List ℤ := [999999998, 999999499]
private def ltM1K2SurvUb : ℤ := 309789647649
private def ltM1K2V2_16 : ℤ := 10180861312157662
private def ltM1K2RelNum : ℕ := 23729247939
private def ltM1K2RelDen : ℕ := 31250000000
private def ltM1K2BeqIv (a b : IvInt) : Bool :=
  TensorConveyorCert.beqZ a.1 b.1 && TensorConveyorCert.beqZ a.2 b.2
private theorem ltM1K2BeqIv_eq_true_iff (a b : IvInt) : ltM1K2BeqIv a b = true ↔ a = b := by
  unfold ltM1K2BeqIv; rw [Bool.and_eq_true, TensorConveyorCert.beqZ_eq_true_iff,
    TensorConveyorCert.beqZ_eq_true_iff]; cases a; cases b; simp
private def ltM1K2CheckEvol9Chunks (csPair : (TcIv × TcIv) × (TcIv × TcIv))
    (chs : List (List (ℤ × ℤ))) (i0 i1 i2 i3 icum isurv : IvInt) : Bool :=
  tcWithForcedIv csPair.1.1 fun c0 ↦
    tcWithForcedIv csPair.1.2 fun s0t ↦
      tcWithForcedIv csPair.2.1 fun c1 ↦
        tcWithForcedIv csPair.2.2 fun s1t ↦
          tcWithForcedIv (tcAmpScale, tcAmpScale) fun initOne ↦
            tcWithForcedIv (Int.ofNat 0, Int.ofNat 0) fun initZero ↦
              match ltM1K2Evol100Chunks (c0, s0t) (c1, s1t) initOne
                  initZero initZero initZero initZero initZero chs with
  | (s0, s1, s2, s3, cum, surv) =>
      ltM1K2BeqIv (ltM1K2Iv100To9 s0) i0 &&
      ltM1K2BeqIv (ltM1K2Iv100To9 s1) i1 &&
      ltM1K2BeqIv (ltM1K2Iv100To9 s2) i2 &&
      ltM1K2BeqIv (ltM1K2Iv100To9 s3) i3 &&
      ltM1K2BeqIv (ltM1K2Iv100To9 cum) icum &&
      ltM1K2BeqIv (ltM1K2Iv100To9 surv) isurv
private theorem ltM1K2CheckEvol9Chunks_sound {cs : Fin 2 → ℝ × ℝ} {csPair : (TcIv × TcIv) × (TcIv ×
  TcIv)} (hcs : (tcMemAmpIv (cs ⟨0, by omega⟩).1 csPair.1.1 ∧ tcMemAmpIv (cs ⟨0, by omega⟩).2
  csPair.1.2) ∧ (tcMemAmpIv (cs ⟨1, by omega⟩).1 csPair.2.1 ∧ tcMemAmpIv (cs ⟨1, by omega⟩).2
  csPair.2.2)) (chs : List (List (ℤ × ℤ))) {i0 i1 i2 i3 icum isurv : IvInt} (hchk :
  ltM1K2CheckEvol9Chunks csPair chs i0 i1 i2 i3 icum isurv = true) :
    let out := swLEvolutionReal 2 (by omega) cs ((ltM1K2Flatten chs).map ltM1K2MkPulse)
    memIvIntVec out.1 [i0, i1, i2, i3] ∧ memIvInt out.2.1 icum ∧ memIvInt out.2.2 isurv := by
  intro out; have hevol := ltM1K2Evol100Aux_sound (cs := cs) hcs.1 hcs.2 (ltM1K2Flatten chs)
    (st := fun j : Fin 4 ↦ if j.1 = 0 then 1 else 0) (cumR := 0) (survR := 0)
    ltM1K2_tcMemAmpIv_one ltM1K2_tcMemAmpIv_zero
    ltM1K2_tcMemAmpIv_zero ltM1K2_tcMemAmpIv_zero
    ltM1K2_tcMemAmpIv_zero ltM1K2_tcMemAmpIv_zero; rcases hevol with ⟨h0, h1, h2, h3, hcum, hsurv⟩
  unfold ltM1K2CheckEvol9Chunks at hchk; simp only [tcWithForcedIv_eq] at hchk
  rw [ltM1K2Evol100Chunks_eq] at hchk; simp only [Bool.and_eq_true, ltM1K2BeqIv_eq_true_iff] at hchk
  rcases hchk with ⟨⟨⟨⟨⟨hs0, hs1⟩, hs2⟩, hs3⟩, hcum_eq⟩, hsurv_eq⟩; have hm0 : memIvInt (out.1 ⟨0,
    by omega⟩) i0 := hs0 ▸ ltM1K2_memIvInt_of_tcMemAmpIv h0; have hm1 : memIvInt (out.1 ⟨1,
    by omega⟩) i1 := hs1 ▸ ltM1K2_memIvInt_of_tcMemAmpIv h1; have hm2 : memIvInt (out.1 ⟨2,
    by omega⟩) i2 := hs2 ▸ ltM1K2_memIvInt_of_tcMemAmpIv h2; have hm3 : memIvInt (out.1 ⟨3,
    by omega⟩) i3 := hs3 ▸ ltM1K2_memIvInt_of_tcMemAmpIv h3; have hmcum : memIvInt out.2.1 icum :=
    hcum_eq ▸ ltM1K2_memIvInt_of_tcMemAmpIv hcum
  have hmsurv : memIvInt out.2.2 isurv := hsurv_eq ▸ ltM1K2_memIvInt_of_tcMemAmpIv hsurv
  refine ⟨⟨rfl, fun j ↦ ?_⟩, hmcum, hmsurv⟩
  fin_cases j <;> first | exact hm0 | exact hm1 | exact hm2 | exact hm3
private def ltM1K2VTable : ℕ → ℤ
  | 0 => 0
  | 1 => 6426990820000000
  | _ => ltM1K2V2_16
private def ltM1K2CheckClamp : Bool :=
  let p0Iv := ivAddInt (swLOrbSqIv ltM1K2CertStIvs9 0)
    (ivMulInt ltM1K2CertCumIv9 (0, swOrbPad))
  let t1Iv := ivSubInt (swScale, swScale) p0Iv
  let tailIvs := t1Iv :: swLTailSuffixIvs 2 ltM1K2CertStIvs9 ltM1K2CertCumIv9 1
  let certLbs := swLClampTailLbs tailIvs
  PulseM1.solBleZ ltM1K2CertSurvIv9.2 ltM1K2SurvUb &&
    (List.range 2).all fun i ↦
      PulseM1.solBleZ (ltM1K2TailLbs.getD i 0) (certLbs.getD i 0)
private theorem ltM1K2_all_cert : ltM1K2CheckEvol9Chunks ltM1K2TrigPair100 ltM1K2RawChunks
  ltM1K2St0Iv9 ltM1K2St1Iv9 ltM1K2St2Iv9 ltM1K2St3Iv9 ltM1K2CertCumIv9 ltM1K2CertSurvIv9 = true ∧
  ltM1K2CheckClamp = true ∧ checkSwLM1StepTable 2 2 9295280 1000000000 2 ltM1K2TailLbs ltM1K2SurvUb
  SchurWeylLCert.multiUnitScale ltM1K2VTable = true ∧ checkSwLRelCostScaled 0 1 ltM1K2V2_16
  SchurWeylLCert.multiUnitScale ltM1K2RelNum ltM1K2RelDen = true := by decide +kernel
private theorem ltM1K2_traj100_cert : ltM1K2CheckEvol9Chunks ltM1K2TrigPair100 ltM1K2RawChunks
  ltM1K2St0Iv9 ltM1K2St1Iv9 ltM1K2St2Iv9 ltM1K2St3Iv9 ltM1K2CertCumIv9 ltM1K2CertSurvIv9 = true :=
  ltM1K2_all_cert.1
private theorem ltM1K2_clamp_cert : ltM1K2CheckClamp = true := ltM1K2_all_cert.2.1
private theorem ltM1K2_step_cert : checkSwLM1StepTable 2 2 9295280 1000000000 2 ltM1K2TailLbs
  ltM1K2SurvUb SchurWeylLCert.multiUnitScale ltM1K2VTable = true := ltM1K2_all_cert.2.2.1
private theorem ltM1K2_relCost_cert : checkSwLRelCostScaled 0 1 ltM1K2V2_16
  SchurWeylLCert.multiUnitScale ltM1K2RelNum ltM1K2RelDen = true := ltM1K2_all_cert.2.2.2
private theorem ltM1K2_bellman_of_enclosure {n : ℕ} (hn96 : 96 ≤ n) (M : Fin (2 * 2) → Fin (2 * 2) →
  ℝ) (hM : IsValidSwLOverlap M) (out : (Fin (2 * 2) → ℝ) × ℝ × ℝ) (hcons : swLNormSq out.1 + out.2.1
  = 1) (hcum0 : 0 ≤ out.2.1) (hst_mem : memIvIntVec out.1 ltM1K2CertStIvs9) (hcum_mem : memIvInt
  out.2.1 ltM1K2CertCumIv9) (hsurv_mem : memIvInt out.2.2 ltM1K2CertSurvIv9) :
    let K_blk := hdistLKBlk n 2 9295280 1000000000
    let p : ℕ → ℝ := swLAttemptProbReal 2 (Nat.le_refl 2) M out.1 out.2.1
    let pSucc : ℝ := ∑ h ∈ Finset.Icc 1 2, p h
    let V : ℕ → ℝ :=
      fun j ↦ ((ltM1K2VTable j : ℝ) / (SchurWeylLCert.multiUnitScale : ℝ)) * √(2 ^ n : ℝ)
    0 < pSucc ∧ (out.2.2 * (K_blk : ℝ) + (2 : ℝ) + ∑ h ∈ Finset.Icc 1 2, p h * V (2 - h)) / pSucc
      ≤ V 2 := by
  intro K_blk p pSucc V; have hS : (0 : ℝ) < (swScale : ℝ) := (by unfold swScale; norm_num)
  have hcl_cert := ltM1K2_clamp_cert; unfold ltM1K2CheckClamp at hcl_cert
  simp only [Bool.and_eq_true, PulseM1.solBleZ_eq_decide, decide_eq_true_eq,
    List.all_eq_true, List.mem_range] at hcl_cert
  rcases hcl_cert with ⟨hsurv_ub, htl_le⟩
  have hsurv_le : out.2.2 ≤ (ltM1K2SurvUb : ℝ) / (swScale : ℝ) :=
    le_trans hsurv_mem.2 (div_le_div_of_nonneg_right (Int.cast_le.2 hsurv_ub) hS.le)
  have hp_nn : ∀ h : ℕ, 0 ≤ p h := fun h ↦ swLAttemptProbReal_nonneg (by omega) M out.1 hcum0 h
  have hp_sum1 : ∑ h ∈ Finset.range 3, p h = 1 := swLAttemptProbReal_sum_one (by omega) hM hcons
  have hp0_mem : memIvInt (p 0)
      (ivAddInt (swLOrbSqIv ltM1K2CertStIvs9 0) (ivMulInt ltM1K2CertCumIv9 (0, swOrbPad))) := by
    dsimp [p]; unfold swLAttemptProbReal; simp only [↓reduceIte]
    have ho0 : memIvInt ((swLOrbitProj M out.1 ⟨0, by omega⟩) ^ 2) (swLOrbSqIv ltM1K2CertStIvs9 0)
      := memIvInt_swLOrbSqIv hM hst_mem ⟨0, by omega⟩
    have hoff0 : |M ⟨0, by omega⟩ ⟨2 * 2 - 1, by omega⟩| ≤ (1 : ℝ) / 10 ^ 9 :=
      hM.2.2.2 _ _ (Fin.ne_of_val_ne (by change (0 : ℕ) ≠ 3; omega))
    have hsq0 : (M ⟨0, by omega⟩ ⟨2 * 2 - 1, by omega⟩) ^ 2 ≤ (1 : ℝ) / 10 ^ 18 := by
      rw [← sq_abs]; exact (pow_le_pow_left₀ (abs_nonneg _) hoff0 2).trans_eq (by norm_num)
    have hpad0 : memIvInt ((M ⟨0, by omega⟩ ⟨2 * 2 - 1, by omega⟩) ^ 2) (0, swOrbPad) := by
      unfold memIvInt swScale swOrbPad; dsimp only
      exact ⟨by linarith [sq_nonneg (M ⟨0, by omega⟩ ⟨2 * 2 - 1, by omega⟩)], by linarith⟩
    exact memIvInt_ivAddInt ho0 (memIvInt_ivMulInt hcum_mem hpad0)
  have ht1_eq : ∑ h ∈ Finset.Icc 1 2, p h = 1 - p 0 := by
    have hsplit : ∑ h ∈ Finset.range 3, p h = p 0 + ∑ h ∈ Finset.Icc 1 2, p h := by
      rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega : 0 < 3),
        show Finset.Ico (0 + 1) 3 = Finset.Icc 1 2 from Finset.Ico_add_one_right_eq_Icc 1 2]
    linarith [hp_sum1, hsplit]
  have ht1_mem : memIvInt (∑ h ∈ Finset.Icc 1 2, p h) (ivSubInt (swScale, swScale) (ivAddInt
    (swLOrbSqIv ltM1K2CertStIvs9 0) (ivMulInt ltM1K2CertCumIv9 (0, swOrbPad)))) := by
    rw [ht1_eq]; exact memIvInt_ivSubInt memIvInt_one hp0_mem
  rcases memIvInt_swLTailSuffixIvs (L := 2) (by omega) hM hst_mem hcum_mem 1 le_rfl with
    ⟨hsfx_len, hsfx⟩
  set tailIvs := ivSubInt (swScale, swScale) (ivAddInt (swLOrbSqIv ltM1K2CertStIvs9 0) (ivMulInt
    ltM1K2CertCumIv9 (0, swOrbPad))) :: swLTailSuffixIvs 2 ltM1K2CertStIvs9 ltM1K2CertCumIv9 1
  have htailIvs_len : tailIvs.length = 2 := (by dsimp [tailIvs]; simp [hsfx_len])
  set tReal : ℕ → ℝ := fun c ↦ ∑ h ∈ Finset.Icc c 2, p h
  have hclamp := swLClampTailLbs_sound tailIvs tReal 1
    (fun i hi ↦ by
      rw [htailIvs_len] at hi; have ht0 : 0 ≤ tReal (1 + i) := Finset.sum_nonneg fun h _ ↦ hp_nn h
      have ht1 : tReal (1 + i) ≤ 1 := by
        have hsub : Finset.Icc (1 + i) 2 ⊆ Finset.range 3 := fun h hh ↦ by
          rw [Finset.mem_Icc] at hh; rw [Finset.mem_range]; omega
        exact (Finset.sum_le_sum_of_subset_of_nonneg hsub fun h _ _ ↦ hp_nn h).trans_eq hp_sum1
      refine ⟨ht0, ht1, ?_⟩
      rcases i with _ | i'
      · simpa [tailIvs, tReal] using ht1_mem.1
      · have hi' : i' < 1 := (by omega); have hmem := hsfx i' hi'
        have hcc_eq : 2 + 1 - 1 + i' = 1 + (i' + 1) := (by omega); rw [hcc_eq] at hmem
        simpa [tailIvs, tReal] using hmem.1)
    (fun i hi ↦ by
      rw [htailIvs_len] at hi; dsimp [tReal]; exact Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.Icc_subset_Icc_left (by omega)) fun h _ _ ↦ hp_nn h)
  have htail_lbs : ∀ c ∈ Finset.Icc 1 2,
      ((ltM1K2TailLbs.getD (c - 1) 0 : ℤ) : ℝ) / (swScale : ℝ) ≤ ∑ h ∈ Finset.Icc c 2, p h := by
    intro c hc; rw [Finset.mem_Icc] at hc; have hidx : c - 1 < 2 := (by omega)
    have hle_cert := htl_le (c - 1) hidx
    have hcert_real := hclamp.2 (c - 1) (by rw [htailIvs_len]; exact hidx)
    rw [show 1 + (c - 1) = c by omega] at hcert_real
    exact (div_le_div_of_nonneg_right (by exact_mod_cast hle_cert) hS.le).trans hcert_real
  have hstep := ltM1K2_step_cert; unfold checkSwLM1StepTable checkSwLM1Step at hstep
  simp only [withForcedInt_eq, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range] at hstep
  rcases hstep with ⟨⟨⟨_, _, _, _, htau, hden, _, _, hsurv0, hvsc_pos, htl0_pos, _, _, _,
    hrem0, hsq_ineq⟩, _⟩, hchain_mono⟩
  have hvsc_r : (0 : ℝ) < (SchurWeylLCert.multiUnitScale : ℝ) := (by exact_mod_cast hvsc_pos)
  have hbden_r : (0 : ℝ) < (swBden49 : ℝ) := (by unfold swBden49; norm_num)
  set N : ℝ := (2 ^ n : ℝ); have hsqrtN_pos : 0 < √N := (by dsimp [N]; positivity)
  have hsqrtN_ge : (swBden49 : ℝ) / 2 ≤ √N := by
    have hpow : 2 ^ 96 ≤ 2 ^ n := Nat.pow_le_pow_right (by omega) hn96
    have hpow_r : ((2 ^ 96 : ℕ) : ℝ) ≤ N := (by dsimp [N]; exact_mod_cast hpow)
    have h1 : (281474976710656 : ℝ) ^ 2 ≤ N := by
      have : ((2 ^ 96 : ℕ) : ℝ) = (281474976710656 : ℝ) ^ 2 := (by norm_num); linarith
    have h2 : (281474976710656 : ℝ) ≤ √N := by
      rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 281474976710656)]; exact Real.sqrt_le_sqrt h1
    have h3 : (swBden49 : ℝ) / 2 = 281474976710656 := (by unfold swBden49; norm_num); linarith
  have hpSucc_pos : 0 < pSucc := by
    have hlb1 := htail_lbs 1 (by rw [Finset.mem_Icc]; omega)
    have hpos : 0 < ((ltM1K2TailLbs.getD 0 0 : ℤ) : ℝ) / (swScale : ℝ) :=
      div_pos (by exact_mod_cast htl0_pos) hS
    exact hpos.trans_le hlb1
  refine ⟨hpSucc_pos, ?_⟩
  set chain : List ℤ := ltM1K2VTable 2 :: (List.range 2).map fun i ↦ ltM1K2VTable (2 - (i + 1))
  have hchain_eq : ∀ c ≤ 2, chain.getD c 0 = ltM1K2VTable (2 - c) := by
    intro c hc; rcases c with _ | c'
    · simp [chain]
    · have hc' : c' < 2 := (by omega); simp [chain, List.getD_eq_getElem?_getD, hc']
  set rhsInt : ℤ := ∑ c ∈ Finset.range 2,
    ltM1K2TailLbs.getD c 0 * (chain.getD c 0 - chain.getD (c + 1) 0)
  have hfold_eq : (List.range 2).foldl (fun acc c ↦ acc + ltM1K2TailLbs.getD c 0 * (chain.getD c
    0 - chain.getD (c + 1) 0)) 0 = rhsInt := foldl_range_add_eq_sum 2 _
  rw [hfold_eq] at hrem0 hsq_ineq
  have hgain_ge : ((rhsInt : ℝ) / ((swScale : ℝ) * (SchurWeylLCert.multiUnitScale : ℝ))) * √N ≤ ∑
    h ∈ Finset.Icc 1 2, p h * (V 2 - V (2 - h)) := by
    have habel := sum_Icc_abel 2 p (fun k ↦ V (2 - k)); simp only [Nat.sub_zero] at habel
    rw [habel, show ((rhsInt : ℝ) / ((swScale : ℝ) * (SchurWeylLCert.multiUnitScale : ℝ))) * √N =
      ∑ c ∈ Finset.range 2, (((ltM1K2TailLbs.getD c 0 : ℤ) : ℝ) / (swScale : ℝ)) *
          ((((chain.getD c 0 - chain.getD (c + 1) 0 : ℤ) : ℝ) /
            (SchurWeylLCert.multiUnitScale : ℝ)) * √N) by
      dsimp [rhsInt]; push_cast; rw [sum_div_const, Finset.sum_mul]
      exact Finset.sum_congr rfl fun _ _ ↦ by ring]
    refine Finset.sum_le_sum fun c hc ↦ ?_
    rw [Finset.mem_range] at hc; have hmono_c := hchain_mono c hc
    have hdiff_nn : 0 ≤ (((chain.getD c 0 - chain.getD (c + 1) 0 : ℤ) : ℝ) /
          (SchurWeylLCert.multiUnitScale : ℝ)) * √N :=
      mul_nonneg (div_nonneg (by exact_mod_cast sub_nonneg.2 hmono_c) hvsc_r.le) hsqrtN_pos.le
    have hV_eq : (((chain.getD c 0 - chain.getD (c + 1) 0 : ℤ) : ℝ) /
      (SchurWeylLCert.multiUnitScale : ℝ)) * √N = V (2 - c) - V (2 - (c + 1)) := by
      rw [hchain_eq c (by omega), hchain_eq (c + 1) (by omega)]; dsimp [V]; push_cast; ring
    have htl_c := htail_lbs (c + 1) (by rw [Finset.mem_Icc]; omega)
    simp only [Nat.add_sub_cancel] at htl_c; rw [← hV_eq]
    exact mul_le_mul_of_nonneg_right htl_c hdiff_nn
  have hK_ub := kBlk_le_main_add_three_halves (r := 2) (tauNum := 9295280) (tauDen := 1000000000)
    hn96 (by omega) (by omega) htau hden
  set bNum : ℤ := 3 * ltM1K2SurvUb + 2 * swScale * (2 : ℤ)
  have hcost_ub : out.2.2 * (K_blk : ℝ) + (2 : ℝ) ≤ (((ltM1K2SurvUb : ℝ) * (9295280 : ℝ)) /
        (2 * (swScale : ℝ) * (1000000000 : ℝ) * √(2 : ℝ)) +
        (bNum : ℝ) / ((swScale : ℝ) * (swBden49 : ℝ))) * √N := by
    have h1 : out.2.2 * (K_blk : ℝ) ≤ ((ltM1K2SurvUb : ℝ) / (swScale : ℝ)) * (((9295280 : ℝ) /
      (2 * (1000000000 : ℝ) * √(2 : ℝ))) * √N + 3 / 2) := mul_le_mul hsurv_le hK_ub
      (Nat.cast_nonneg K_blk) (div_nonneg (by exact_mod_cast hsurv0) hS.le)
    have hbNum_nn : 0 ≤ (bNum : ℝ) := (by dsimp [bNum]; unfold swScale ltM1K2SurvUb; norm_num)
    have hoverh : (bNum : ℝ) / (2 * (swScale : ℝ)) ≤
        ((bNum : ℝ) / ((swScale : ℝ) * (swBden49 : ℝ))) * √N := by
      have hmul := mul_le_mul_of_nonneg_left hsqrtN_ge
        (div_nonneg hbNum_nn (mul_pos hS hbden_r).le)
      refine (?_ : (bNum : ℝ) / (2 * (swScale : ℝ)) =
        ((bNum : ℝ) / ((swScale : ℝ) * (swBden49 : ℝ))) * ((swBden49 : ℝ) / 2)).trans_le hmul
      field_simp [hS.ne', hbden_r.ne']
    have halg : ((ltM1K2SurvUb : ℝ) / (swScale : ℝ)) * (((9295280 : ℝ) / (2 * (1000000000 : ℝ) *
      √(2 : ℝ))) * √N + 3 / 2) + (2 : ℝ) = (((ltM1K2SurvUb : ℝ) * (9295280 : ℝ)) / (2 * (swScale :
      ℝ) * (1000000000 : ℝ) * √(2 : ℝ))) * √N + (bNum : ℝ) / (2 * (swScale : ℝ)) := by
      dsimp [bNum]; push_cast; field_simp [hS.ne']; ring
    linarith
  set rem : ℤ := rhsInt * swBden49 - SchurWeylLCert.multiUnitScale * bNum
  have hcoef_le : ((ltM1K2SurvUb : ℝ) * (9295280 : ℝ)) / (2 * (swScale : ℝ) * (1000000000 : ℝ) *
    √(2 : ℝ)) + (bNum : ℝ) / ((swScale : ℝ) * (swBden49 : ℝ)) ≤ (rhsInt : ℝ) / ((swScale : ℝ) *
    (SchurWeylLCert.multiUnitScale : ℝ)) := by
    have hr_pos : (0 : ℝ) < (2 : ℝ) := (by norm_num)
    have hsqrt_r_pos : 0 < √(2 : ℝ) := Real.sqrt_pos.2 hr_pos
    have hden_r : (0 : ℝ) < (1000000000 : ℝ) := (by norm_num)
    have hrem_r : (0 : ℝ) ≤ (rem : ℝ) := (by exact_mod_cast hrem0)
    have hlhs_nn : 0 ≤ (ltM1K2SurvUb : ℝ) * (9295280 : ℝ) *
          (SchurWeylLCert.multiUnitScale : ℝ) * (swBden49 : ℝ) := by
      have : (0 : ℝ) ≤ (ltM1K2SurvUb : ℝ) := (by exact_mod_cast hsurv0); positivity
    have hrhs_nn : 0 ≤ 2 * (1000000000 : ℝ) * √(2 : ℝ) * (rem : ℝ) := (by positivity)
    have hsq_r : ((ltM1K2SurvUb : ℝ) * (9295280 : ℝ) * (SchurWeylLCert.multiUnitScale : ℝ) *
      (swBden49 : ℝ)) ^ 2 ≤ (2 * (1000000000 : ℝ) * √(2 : ℝ) * (rem : ℝ)) ^ 2 := by
      have hcast : ((ltM1K2SurvUb * (9295280 : ℤ) * SchurWeylLCert.multiUnitScale * swBden49) ^ 2
        : ℝ) ≤ ((4 * ((1000000000 : ℤ) ^ 2) * (2 : ℤ) * (rem ^ 2) : ℤ) : ℝ) := by
        exact_mod_cast hsq_ineq
      push_cast at hcast; have hsq_rhs : (2 * (1000000000 : ℝ) * √(2 : ℝ) * (rem : ℝ)) ^ 2 =
          4 * (1000000000 : ℝ) ^ 2 * (2 : ℝ) * (rem : ℝ) ^ 2 := by
        calc (2 * (1000000000 : ℝ) * √(2 : ℝ) * (rem : ℝ)) ^ 2
          _ = 4 * (1000000000 : ℝ) ^ 2 * (√(2 : ℝ)) ^ 2 * (rem : ℝ) ^ 2 := by ring
          _ = 4 * (1000000000 : ℝ) ^ 2 * (2 : ℝ) * (rem : ℝ) ^ 2 := by rw [Real.sq_sqrt hr_pos.le]
      linarith
    have hroot : (ltM1K2SurvUb : ℝ) * (9295280 : ℝ) * (SchurWeylLCert.multiUnitScale : ℝ) *
      (swBden49 : ℝ) ≤ 2 * (1000000000 : ℝ) * √(2 : ℝ) * (rem : ℝ) := by
      rw [← Real.sqrt_sq hlhs_nn, ← Real.sqrt_sq hrhs_nn]; exact Real.sqrt_le_sqrt hsq_r
    have hrem_def : (rem : ℝ) = (rhsInt : ℝ) * (swBden49 : ℝ) - (SchurWeylLCert.multiUnitScale :
      ℝ) * (bNum : ℝ) := by
      dsimp [rem]; push_cast; rfl
    rw [hrem_def] at hroot; have hpos_prod : 0 < 2 * (swScale : ℝ) * (1000000000 : ℝ) * √(2 : ℝ) *
        (SchurWeylLCert.multiUnitScale : ℝ) * (swBden49 : ℝ) := by positivity
    rw [← sub_nonneg]
    have hdiff : (rhsInt : ℝ) / ((swScale : ℝ) * (SchurWeylLCert.multiUnitScale : ℝ)) -
      (((ltM1K2SurvUb : ℝ) * (9295280 : ℝ)) / (2 * (swScale : ℝ) * (1000000000 : ℝ) * √(2 : ℝ)) +
      (bNum : ℝ) / ((swScale : ℝ) * (swBden49 : ℝ))) = (2 * (1000000000 : ℝ) * √(2 : ℝ) * ((rhsInt
      : ℝ) * (swBden49 : ℝ) - (SchurWeylLCert.multiUnitScale : ℝ) * (bNum : ℝ)) - (ltM1K2SurvUb :
      ℝ) * (9295280 : ℝ) * (SchurWeylLCert.multiUnitScale : ℝ) * (swBden49 : ℝ)) / (2 * (swScale :
      ℝ) * (1000000000 : ℝ) * √(2 : ℝ) * (SchurWeylLCert.multiUnitScale : ℝ) * (swBden49 :
      ℝ)) := by
      field_simp [hS.ne', hden_r.ne', hsqrt_r_pos.ne', hvsc_r.ne', hbden_r.ne']; ring
    rw [hdiff]; exact div_nonneg (by linarith) hpos_prod.le
  have hnet : out.2.2 * (K_blk : ℝ) + (2 : ℝ) ≤ ∑ h ∈ Finset.Icc 1 2, p h * (V 2 - V (2 - h)) :=
    (hcost_ub.trans (mul_le_mul_of_nonneg_right hcoef_le hsqrtN_pos.le)).trans hgain_ge
  have hexpand : ∑ h ∈ Finset.Icc 1 2, p h * (V 2 - V (2 - h)) =
      pSucc * V 2 - ∑ h ∈ Finset.Icc 1 2, p h * V (2 - h) := by
    dsimp [pSucc]; rw [Finset.sum_mul]; have hsub : ∀ h ∈ Finset.Icc 1 2, p h * (V 2 - V (2 - h)) =
        p h * V 2 - p h * V (2 - h) := fun _ _ ↦ mul_sub _ _ _
    rw [Finset.sum_congr rfl hsub, Finset.sum_sub_distrib]
  rw [div_le_iff₀ hpSucc_pos]; linarith [hnet, hexpand]
private theorem ltM1K2_stage2_of_chunks {n : ℕ} (hn96 : 96 ≤ n) (chs : List (List (ℤ × ℤ))) (htraj :
  ltM1K2CheckEvol9Chunks ltM1K2TrigPair100 chs ltM1K2St0Iv9 ltM1K2St1Iv9 ltM1K2St2Iv9 ltM1K2St3Iv9
  ltM1K2CertCumIv9 ltM1K2CertSurvIv9 = true) : ∀ (M : Fin (2 * 2) → Fin (2 * 2) → ℝ),
  IsValidSwLOverlap M →
      let K_blk := hdistLKBlk n 2 9295280 1000000000
      let cs : Fin 2 → ℝ × ℝ := fun w ↦ (Real.cos ((K_blk : ℝ) * swLThetaShiftReal (2 ^ n) 2 w.1),
        Real.sin ((K_blk : ℝ) * swLThetaShiftReal (2 ^ n) 2 w.1))
      let out := hdistLEvolutionReal 2 (Nat.le_refl 2) cs ((ltM1K2Flatten chs).map ltM1K2MkPulse)
      let p : ℕ → ℝ := swLAttemptProbReal 2 (Nat.le_refl 2) M out.1 out.2.1
      let pSucc : ℝ := ∑ h ∈ Finset.Icc 1 2, p h
      let V : ℕ → ℝ :=
        fun j ↦ ((ltM1K2VTable j : ℝ) / (SchurWeylLCert.multiUnitScale : ℝ)) * √(2 ^ n : ℝ)
      0 < pSucc ∧ (out.2.2 * (K_blk : ℝ) + (2 : ℝ) + ∑ h ∈ Finset.Icc 1 2, p h * V (2 - h)) /
        pSucc ≤ V 2 := by
  intro M hM K_blk cs out p pSucc V
  have hcs_unit : ∀ w : Fin 2, (cs w).1 ^ 2 + (cs w).2 ^ 2 = 1 := fun w ↦ Real.cos_sq_add_sin_sq _
  rcases swLEvolutionReal_normSq_add_cum (Nat.le_refl 2) hcs_unit
    ((ltM1K2Flatten chs).map ltM1K2MkPulse)
    (ltM1K2MapPulses_valid (ltM1K2Flatten chs)) with ⟨hcons, hcum0, _, _⟩
  have hcs_mem := ltM1K2TrigPair100_sound hn96
  rcases ltM1K2CheckEvol9Chunks_sound (cs := cs) hcs_mem chs htraj with
    ⟨hst_mem, hcum_mem, hsurv_mem⟩
  exact ltM1K2_bellman_of_enclosure hn96 M hM (swLEvolutionReal 2 (Nat.le_refl 2) cs
    ((ltM1K2Flatten chs).map ltM1K2MkPulse)) hcons hcum0 hst_mem hcum_mem hsurv_mem
private def LtM1K2StageBundleProp (n r : ℕ) (s : SwLM1StageSpec) : Prop :=
  ∃ (hL2 : 2 ≤ s.L),
    s.L ≤ 8 ∧ s.L ≤ r ∧
    s.pulses.all swLPulseValid = true ∧
    ∀ (M : Fin (2 * s.L) → Fin (2 * s.L) → ℝ),
      IsValidSwLOverlap M →
      let K_blk := hdistLKBlk n r s.tauNum s.tauDen
      let cs : Fin s.L → ℝ × ℝ := fun w ↦
        (Real.cos ((K_blk : ℝ) * swLThetaShiftReal (2 ^ n) r w.1),
         Real.sin ((K_blk : ℝ) * swLThetaShiftReal (2 ^ n) r w.1))
      let out := hdistLEvolutionReal s.L hL2 cs s.pulses
      let p : ℕ → ℝ := swLAttemptProbReal s.L hL2 M out.1 out.2.1
      let pSucc : ℝ := ∑ h ∈ Finset.Icc 1 s.L, p h
      let V : ℕ → ℝ :=
        fun j ↦ ((ltM1K2VTable j : ℝ) / (SchurWeylLCert.multiUnitScale : ℝ)) * √(2 ^ n : ℝ)
      0 < pSucc ∧
      (out.2.2 * (K_blk : ℝ) + (s.L : ℝ) +
        ∑ h ∈ Finset.Icc 1 s.L, p h * V (r - h)) / pSucc ≤ V r
private theorem ltM1K2_stage2_spec {n : ℕ} (hn96 : 96 ≤ n) (s : SwLM1StageSpec) (chs : List (List (ℤ
  × ℤ))) (hs : s = ⟨2, 9295280, 1000000000, (ltM1K2Flatten chs).map ltM1K2MkPulse⟩) (htraj :
  ltM1K2CheckEvol9Chunks ltM1K2TrigPair100 chs ltM1K2St0Iv9 ltM1K2St1Iv9 ltM1K2St2Iv9 ltM1K2St3Iv9
  ltM1K2CertCumIv9 ltM1K2CertSurvIv9 = true) : LtM1K2StageBundleProp n 2 s := by
  subst hs
  exact ⟨Nat.le_refl 2, by change 2 ≤ 8; omega, Nat.le_refl 2,
    ltM1K2MapPulses_valid (ltM1K2Flatten chs),
    ltM1K2_stage2_of_chunks hn96 chs htraj⟩
private def ltM1K2Bundle : SwLM1CertBundle where
  kMax := 2
  vScale := SchurWeylLCert.multiUnitScale
  vTable := ltM1K2VTable
  useSwL := fun r ↦ r == 2
  stageOfR := fun _ ↦ ⟨2, 9295280, 1000000000, (ltM1K2Flatten ltM1K2RawChunks).map ltM1K2MkPulse⟩
  hKMax := by omega
  hScalePos := by unfold SchurWeylLCert.multiUnitScale; omega
  hV0 := rfl
  hMono := by
    intro r hr
    rcases r with _ | _ | r
    · change (0 : ℤ) ≤ 6426990820000000; omega
    · change (6426990820000000 : ℤ) ≤ 10180861312157662; omega
    · omega
  hStageSound := by
    intro n r hn96 _ _ huse
    have hr2 : r = 2 := by simpa using huse
    subst hr2
    intro s
    have hs : s = ⟨2, 9295280, 1000000000,
      (ltM1K2Flatten ltM1K2RawChunks).map ltM1K2MkPulse⟩ := rfl
    clear_value s
    change LtM1K2StageBundleProp n 2 s
    exact ltM1K2_stage2_spec hn96 s ltM1K2RawChunks hs ltM1K2_traj100_cert
private theorem ltM1K2_useSwL (r : ℕ) (h2 : 2 ≤ r) (hle : r ≤ ltM1K2Bundle.kMax) :
  ltM1K2Bundle.useSwL r = true := by
  change (r == 2) = true; have hr2 : r = 2 := (by change r ≤ 2 at hle; omega); subst hr2; rfl
private def groverM1PulseKGe4Profile : FindAllCostProfile where
  validCell m k :=
    (m == 1) && (
      (k == 4) || (k == 8) || (k == 16) || (k == 32) ||
      (k == 64) || (k == 128) || (k == 256) || (k == 512) || (k == 1024)
    )
  relCost := relCostGroverM1Pulse
  n0 _ _ := 1152
private theorem solBoolAnd1 {a b : Bool} (h : (a && b) = true) : a = true :=
  ((Bool.and_eq_true a b).mp h).1
private theorem solBoolAnd2 {a b : Bool} (h : (a && b) = true) : b = true :=
  ((Bool.and_eq_true a b).mp h).2
private def solRelCost_1e16_bool : Bool :=
  ((((PulseM1.checkPulseRelCostM1 6 (GroverM1PulsePt2.solM1VTable16_ref 64)
        1325132303543193 2000000000000000 &&
      PulseM1.checkPulseRelCostM1 7 (GroverM1PulsePt2.solM1VTable16_ref 128)
        6564251612151231 10000000000000000) &&
     PulseM1.checkPulseRelCostM1 8 (GroverM1PulsePt2.solM1VTable16_ref 256)
        409036472074287 625000000000000) &&
    PulseM1.checkPulseRelCostM1 9 (GroverM1PulsePt2.solM1VTable16_ref 512)
        261102099301103 400000000000000) &&
   PulseM1.checkPulseRelCostM1 10 (GroverM1PulsePt2.solM1VTable16_ref 1024)
        3256773370679057 5000000000000000)
private theorem cert_solRelCost_1e16_all : solRelCost_1e16_bool = true := by
  decide +kernel
private theorem cert_solRelCost_1e16_k64 :
    PulseM1.checkPulseRelCostM1 6 (GroverM1PulsePt2.solM1VTable16_ref 64)
      1325132303543193 2000000000000000 = true :=
  solBoolAnd1 (solBoolAnd1 (solBoolAnd1 (solBoolAnd1 cert_solRelCost_1e16_all)))
private theorem cert_solRelCost_1e16_k128 :
    PulseM1.checkPulseRelCostM1 7 (GroverM1PulsePt2.solM1VTable16_ref 128)
      6564251612151231 10000000000000000 = true :=
  solBoolAnd2 (solBoolAnd1 (solBoolAnd1 (solBoolAnd1 cert_solRelCost_1e16_all)))
private theorem cert_solRelCost_1e16_k256 :
    PulseM1.checkPulseRelCostM1 8 (GroverM1PulsePt2.solM1VTable16_ref 256)
      409036472074287 625000000000000 = true :=
  solBoolAnd2 (solBoolAnd1 (solBoolAnd1 cert_solRelCost_1e16_all))
private theorem cert_solRelCost_1e16_k512 :
    PulseM1.checkPulseRelCostM1 9 (GroverM1PulsePt2.solM1VTable16_ref 512)
      261102099301103 400000000000000 = true :=
  solBoolAnd2 (solBoolAnd1 cert_solRelCost_1e16_all)
private theorem cert_solRelCost_1e16_k1024 :
    PulseM1.checkPulseRelCostM1 10 (GroverM1PulsePt2.solM1VTable16_ref 1024)
      3256773370679057 5000000000000000 = true :=
  solBoolAnd2 cert_solRelCost_1e16_all
private theorem validFamily_groverM1Pulse_kGe4 {Var : Type} [DecidableEq Var] (res : Var) :
  ValidFindAllFamily res groverM1PulseKGe4Profile (PulseM1.pulseStandaloneM1Circuit res
  pulseM1CertBundle) := by
  refine PulseM1.validFamily_pulseStandaloneM1 res pulseM1CertBundle rfl (fun r hr2 _ ↦
    decide_eq_true hr2) ?_ groverM1PulseKGe4Profile ?_
  · have h1 := GroverM1PulseTable.cert_solVTable_r1; rw [PulseM1.solBleZ_eq_decide,
      decide_eq_true_eq] at h1; change (6426990820000000 : ℤ) ≤
      GroverM1PulsePt2.solM1VTable16_ref 1
    rwa [GroverM1PulsePt2.solM1VTable16_eq_of_le_31 (by omega)]
  · intro m k _hgrid hvalid; dsimp only [groverM1PulseKGe4Profile] at hvalid
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hvalid; rcases hvalid with ⟨rfl,
      hk⟩; refine ⟨rfl, ?_⟩; rcases hk with ((((((((hk | hk) | hk) | hk) | hk) | hk) | hk) | hk) |
      hk)
    · subst hk
      exact ⟨by omega, by change _ ≤ 1024; omega, le_rfl,
        ⟨2, 179936242757, 250000000000,
          rfl, rfl, by
            change PulseM1.checkPulseRelCostM1 2 (GroverM1PulsePt2.solM1VTable16_ref 4) _ _
              = true; rw [GroverM1PulsePt2.solM1VTable16_eq_of_le_31 (by omega)]
            exact GroverM1PulseTable.cert_solRelCost_k4⟩⟩
    · subst hk
      exact ⟨by omega, by change _ ≤ 1024; omega, le_rfl,
        ⟨3, 693944177707, 1000000000000,
          rfl, rfl, by
            change PulseM1.checkPulseRelCostM1 3 (GroverM1PulsePt2.solM1VTable16_ref 8) _ _
              = true; rw [GroverM1PulsePt2.solM1VTable16_eq_of_le_31 (by omega)]
            exact GroverM1PulseTable.cert_solRelCost_k8⟩⟩
    · subst hk
      exact ⟨by omega, by change _ ≤ 1024; omega, le_rfl,
        ⟨4, 135807791521, 200000000000,
          rfl, rfl, by
            change PulseM1.checkPulseRelCostM1 4 (GroverM1PulsePt2.solM1VTable16_ref 16) _ _
              = true; rw [GroverM1PulsePt2.solM1VTable16_eq_of_le_31 (by omega)]
            exact GroverM1PulseTable.cert_solRelCost_k16⟩⟩
    · subst hk
      exact ⟨by omega, by change _ ≤ 1024; omega, le_rfl,
        ⟨5, 26885301129, 40000000000, rfl, rfl, GroverM1PulsePt2.cert_solRelCost_ref_k32⟩⟩
    · subst hk
      exact ⟨by omega, by change _ ≤ 1024; omega, le_rfl,
        ⟨6, 1325132303543193, 2000000000000000, rfl, rfl,
          cert_solRelCost_1e16_k64⟩⟩
    · subst hk
      exact ⟨by omega, by change _ ≤ 1024; omega, le_rfl,
        ⟨7, 6564251612151231, 10000000000000000, rfl, rfl,
          cert_solRelCost_1e16_k128⟩⟩
    · subst hk
      exact ⟨by omega, by change _ ≤ 1024; omega, le_rfl,
        ⟨8, 409036472074287, 625000000000000, rfl, rfl,
          cert_solRelCost_1e16_k256⟩⟩
    · subst hk
      exact ⟨by omega, by change _ ≤ 1024; omega, le_rfl,
        ⟨9, 261102099301103, 400000000000000, rfl, rfl,
          cert_solRelCost_1e16_k512⟩⟩
    · subst hk
      exact ⟨by omega, by change _ ≤ 1024; omega, le_rfl,
        ⟨10, 3256773370679057, 5000000000000000, rfl, rfl,
          cert_solRelCost_1e16_k1024⟩⟩
end InternalLtM1K2
public section
/-- Complete standalone `m = 1` Multi-pulse conveyor circuit family (`1152 ≤ n`). -/
noncomputable def groverM1PulseCircuit {Var : Type} (res : Var) : ∀ (n m k : ℕ),
    OracleDynamicCircuit (Unitary (2 ^ findAllQubits n m k)) Var
      (findAllQubits n m k) ((n + 1) * m)
  | n, 1, 2 =>
      if 100 ≤ n then
        hdistLM1FromSetCircuit res ltM1K2Bundle n 2 2 ∅
      else
        findAllCircuit res (fun _ _ _ ↦ 0) n 1 2
  | n, m, k =>
      PulseM1.pulseStandaloneM1Circuit res pulseM1CertBundle n m k
private theorem groverM1PulseCircuit_m1_2 {Var : Type} (res : Var) (n : ℕ) :
  groverM1PulseCircuit res n 1 2 = if 100 ≤ n then hdistLM1FromSetCircuit res ltM1K2Bundle n 2 2 ∅
  else findAllCircuit res (fun _ _ _ ↦ 0) n 1 2 := by rfl
private theorem groverM1PulseCircuit_m1_ne2 {Var : Type} (res : Var) (n k : ℕ) (hk2 : k ≠ 2) :
  groverM1PulseCircuit res n 1 k = PulseM1.pulseStandaloneM1Circuit res pulseM1CertBundle n
  1 k := by
  rcases k with _ | _ | _ | k
  · rfl
  · rfl
  · exact absurd rfl hk2
  · rfl
private theorem groverM1Pulse_valid_split {m k : ℕ} (hvalid : groverM1PulseProfile.validCell m k
  = true) : (m = 1 ∧ k = 2) ∨ (m = 1 ∧ k ≠ 2 ∧ groverM1PulseKGe4Profile.validCell 1 k = true) :=
  by
  dsimp only [groverM1PulseProfile, isGroverM1PulseCell] at hvalid; simp only [Bool.and_eq_true,
    Bool.or_eq_true, beq_iff_eq] at hvalid; rcases hvalid with ⟨rfl, hk⟩; rcases hk with (((((((((hk
    | hk) | hk) | hk) | hk) | hk) | hk) | hk) | hk) | hk)
  · subst hk; exact Or.inl ⟨rfl, rfl⟩
  all_goals subst hk; exact Or.inr ⟨rfl, by omega, rfl⟩
/-- End-to-end `ValidFindAllFamily` theorem across all `10 / 10` `m = 1` grid cells. -/
theorem validFamily_groverM1Pulse {Var : Type} [DecidableEq Var] (res : Var) :
    ValidFindAllFamily res groverM1PulseProfile (groverM1PulseCircuit res) where
  correctness {n m k S} hn hmk hvalid hkN hS := by
    rcases groverM1Pulse_valid_split hvalid with ⟨rfl, rfl⟩ | ⟨rfl, hk_ne2, hv4⟩
    · have hScard : S.card = 2 := (Finset.mem_powersetCard.1 hS).2; by_cases hn100 : 100 ≤ n
      · intro Δ; rw [groverM1PulseCircuit_m1_2 res n, ite_eq_left hn100, expect_top, interp_qSeq,
          QMonad.Q.toStateFun_bind, interp_qSet, QMonad.Q.toStateFun_qSet]
        have hsupp : SupportedOn (· = (0 : Fin (2 ^ findAllQubits n 1 2))) Δ.qSet :=
          supportedOn_qSet (pred := (· = (0 : Fin (2 ^ findAllQubits n 1 2)))) rfl Δ
        have hcorr := (hdistLM1FromSet_correct_and_cost res ltM1K2Bundle rfl ltM1K2_useSwL le_rfl
          hn100 le_rfl le_rfl le_rfl hScard (Finset.empty_subset S) (by simpa using hScard) hsupp).1
        exact (hcorr.trans (congrArg ((↑) : ℝ≥0 → ℝ) (CQState.trace_qSet Δ))).symm.le
      · rw [groverM1PulseCircuit_m1_2 res n, ite_eq_right hn100]
        exact findAllProgram_correctness res (fun _ _ _ ↦ 0) le_rfl hScard hkN (fun r hr1 hrk ↦
          p_succ_set_zero_pos hr1 (hrk.trans hkN))
    · rw [groverM1PulseCircuit_m1_ne2 res n k hk_ne2]; exact (validFamily_groverM1Pulse_kGe4
        res).correctness hn hmk hv4 hkN hS
  costBound_uniform {m k} hmk hvalid n hn0 hkN := by
    rcases groverM1Pulse_valid_split hvalid with ⟨rfl, rfl⟩ | ⟨rfl, hk_ne2, hv4⟩
    · change 1152 ≤ n at hn0; have hn100 : 100 ≤ n := (by omega); set cVal : ℝ := ((ltM1K2V2_16 : ℝ)
        / (SchurWeylLCert.multiUnitScale : ℝ)) * √(2 ^ n : ℝ); have hcVal_nn : 0 ≤ cVal :=
        (by dsimp [cVal]; unfold ltM1K2V2_16 SchurWeylLCert.multiUnitScale; positivity)
      let cNN : ℝ≥0 := ⟨cVal, hcVal_nn⟩; refine ⟨fun _ ↦ cNN, ?_, ?_⟩
      · intro S hS Δ; have hScard : S.card = 2 := (Finset.mem_powersetCard.1 hS).2
        rw [groverM1PulseCircuit_m1_2 res n, ite_eq_left hn100, expectedCost_qSeq,
          expectedCost_qSet, CostModel.ofEmbeddedOracle_resetCost, Nat.cast_zero, mul_zero,
          zero_add, interp_qSet, QMonad.Q.toStateFun_qSet]
        have hsupp : SupportedOn (· = (0 : Fin (2 ^ findAllQubits n 1 2))) Δ.qSet :=
          supportedOn_qSet (pred := (· = (0 : Fin (2 ^ findAllQubits n 1 2)))) rfl Δ
        have hmass_eq : stateMass Δ.qSet = stateMass Δ :=
          congrArg ENNReal.ofNNReal (CQState.trace_qSet Δ)
        have hcb := (hdistLM1FromSet_correct_and_cost res ltM1K2Bundle rfl ltM1K2_useSwL le_rfl
          hn100 le_rfl le_rfl le_rfl hScard (Finset.empty_subset S) (by simpa using hScard) hsupp).2
        have hcNN : (cNN : ℝ≥0∞) = ENNReal.ofReal cVal := ENNReal.ofReal_coe_nnreal.symm
        rw [hmass_eq] at hcb; refine hcb.trans ?_; rw [hcNN]; exact le_rfl
      · have hcard_pos : 0 < ((Finset.univ : Finset (Fin (2 ^ n))).powersetCard 2).card := by
          rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
          exact Nat.choose_pos hkN
        have hcard_r : (0 : ℝ) < (((Finset.univ : Finset (Fin (2 ^ n))).powersetCard 2).card : ℝ) :=
          Nat.cast_pos.2 hcard_pos; rw [Finset.sum_const, nsmul_eq_mul, mul_div_cancel_left₀ _
          hcard_r.ne']
        have hrel_eq : ((groverM1PulseProfile.relCost 1 2 : ℚ≥0) : ℝ) = (ltM1K2RelNum : ℝ) /
          (ltM1K2RelDen : ℝ) := by
          unfold groverM1PulseProfile relCostGroverM1Pulse ltM1K2RelNum ltM1K2RelDen
          simp only [beq_self_eq_true, Bool.and_self, ↓reduceIte]; push_cast; norm_num
        rw [hrel_eq]; change cVal ≤ _; have hsound := SchurWeylLCert.checkSwLRelCostScaled_sound (n
          := n) ltM1K2_relCost_cert; have hpow0 : (2 ^ 0 : ℝ) = ((1 : ℕ) : ℝ) := (by norm_num)
        rw [show (2 ^ 1 : ℕ) = 2 from rfl, hpow0] at hsound; exact hsound
    · obtain ⟨c, hc1, hc2⟩ := (validFamily_groverM1Pulse_kGe4 res).costBound_uniform hmk hv4 n hn0
        hkN; refine ⟨c, fun S hS Δ ↦ ?_, hc2⟩; rw [groverM1PulseCircuit_m1_ne2 res n k hk_ne2];
        exact hc1 S hS Δ
end
end QuantumComputation.Specs.GroverFindAll
