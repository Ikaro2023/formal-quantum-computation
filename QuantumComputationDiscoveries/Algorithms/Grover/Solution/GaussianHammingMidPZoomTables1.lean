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
public import QuantumComputationDiscoveries.Algorithms.Grover.Solution.WeakDickeCore
public import QuantumComputationDiscoveries.Algorithms.Grover.Solution.GaussianHammingZoomK2Base
public import QuantumComputationDiscoveries.Algorithms.Grover.Solution.GaussianHammingMidPZoomEval
/-
 Middle-`p` Unpadded Multi-Collision Evaluators & `m = 512` Slice Bounds (`dk = 15`).
-/
@[expose] public section
namespace QuantumComputation.Specs.DickeSol
open QuantumComputation.Specs.GroverFindAll.GaussianHammingZoomK2
private lemma cond_eq_ite_s1 {α : Type*} (b : Bool) (P : Prop) [Decidable P] (hb : b = true ↔ P) (x
    y : α) : cond b x y = (if P then x else y) := by
  cases b with
  | true => exact (ite_eq_left (hb.mp rfl)).symm
  | false => exact (ite_eq_right (mt hb.mpr Bool.false_ne_true)).symm
private lemma cond_eq_ite_congr_s1 {α : Type*} (b : Bool) (P : Prop) [Decidable P] (hb : b = true ↔
P) {x x' y : α} (hx : x = x') : cond b x y = (if P then x' else y) := by
  rw [hx]; exact cond_eq_ite_s1 b P hb x' y
/-- Constructor-level `Bool` equality on `ℤ` (`0` kernel typeclass synthesis). -/
def fastBeqZS1 (a b : ℤ) : Bool := midPBleZ a b && midPBleZ b a
private lemma fastBeqZ_iff_s1 (a b : ℤ) : fastBeqZS1 a b = true ↔ a = b := by
  unfold fastBeqZS1; simp only [Bool.and_eq_true, midPBleZ_iff]; omega
/-- Primitive `10 ^ 15`-scaled rational interval (`rfl`-equal to `wdRat`). -/
def fastRatS1 (num : ℤ) (den : ℕ) : WDIVal :=
  (Int.ediv (Int.mul num midPScaleZ) (Int.ofNat den),
    Int.neg (Int.ediv (Int.neg (Int.mul num midPScaleZ)) (Int.ofNat den)))
/-- Atomic-literal binomial coefficient replacing `ghForceNat` in `ghBinom`. -/
def fastBinomS1 (r w : ℕ) : ℕ := midPLitNat (r.descFactorial w / w.factorial) id
private lemma fastBinom_eq_s1 (r w : ℕ) : fastBinomS1 r w = ghBinom r w := by
  conv_lhs => unfold fastBinomS1; rw [midPLitNat_eq]
  (conv_rhs => unfold ghBinom; rw [ghForceNat_eq]); rfl
/-- CPS bare-literal-forced base trig enclosure replacing `ghSeqIV` with `midPSeqIV`. -/
def fastTrigBaseCPSS1 {α : Type*} (u : WDIVal) (k : WDIVal → WDIVal → α) : α :=
  let B : ℤ := midPScaleZ; let uh2 := Int.neg (Int.ediv (Int.neg (Int.mul u.2 u.2)) B)
  let ul2 := Int.ediv (Int.mul u.1 u.1) B
  let uh4 := Int.neg (Int.ediv (Int.neg (Int.mul uh2 uh2)) B)
  let cLo := Int.sub B (Int.neg (Int.ediv (Int.neg (Int.mul u.2 u.2)) (Int.mul 2 B)))
  let cHi := Int.add (Int.sub B (Int.ediv (Int.mul u.1 u.1) (Int.mul 2 B)))
    (Int.neg (Int.ediv (Int.neg uh4) 24))
  let uh3 := Int.neg (Int.ediv (Int.neg (Int.mul uh2 u.2)) B)
  let ul3 := Int.ediv (Int.mul ul2 u.1) B
  let uh5 := Int.neg (Int.ediv (Int.neg (Int.mul uh4 u.2)) B)
  let sLo := ghMaxZ 0 (Int.sub u.1 (Int.neg (Int.ediv (Int.neg uh3) 6)))
  let sHi := Int.add (Int.sub u.2 (Int.ediv ul3 6)) (Int.neg (Int.ediv (Int.neg uh5) 120))
  midPSeqIV (cLo, cHi) fun c ↦ midPSeqIV (sLo, sHi) fun s ↦ k c s
private lemma fastTrigBaseCPS_eq_s1 {α : Type*} (u : WDIVal) (k : WDIVal → WDIVal → α) :
    fastTrigBaseCPSS1 u k = ghTrigBaseCPS u k := by
  conv_lhs => unfold fastTrigBaseCPSS1; rw [midPSeqIV_eq]; rw [midPSeqIV_eq]
  (conv_rhs => unfold ghTrigBaseCPS; rw [ghSeqIV_eq]; rw [ghSeqIV_eq]); rfl
/-- CPS bare-literal-forced trig enclosure (`0` `ghForceInt`). -/
def fastTrigCPSS1 {α : Type*} (x : WDIVal) (k : WDIVal → WDIVal → α) : α :=
  midPSeqIV (Int.ediv x.1 1024, Int.neg (Int.ediv (Int.neg x.2) 1024)) fun u ↦
    fastTrigBaseCPSS1 u fun c0 s0 ↦ midPSeqIV c0 fun c0F ↦ midPSeqIV s0 fun s0F ↦
          midPDoubleAngleIterCPS 10 c0F s0F k
private lemma fastTrigCPS_eq_s1 {α : Type*} (x : WDIVal) (k : WDIVal → WDIVal → α) : fastTrigCPSS1
    x k = midPTrigCPS x k := by
  conv_lhs => unfold fastTrigCPSS1; rw [midPSeqIV_eq]; rw [fastTrigBaseCPS_eq_s1]
  (conv_rhs => unfold midPTrigCPS; rw [midPSeqIV_eq]); rfl
/-- `Bool`-guarded Gaussian-rational phase enclosure (`= evalMidPPhaseIV`). -/
def fastEvalPhaseIVS1 (ph : MidPPhaseSpec) : Option WDCVal := cond
  (Nat.ble 1 ph.gd && fastBeqZS1 (Int.add (Int.mul ph.ga ph.ga) (Int.mul ph.gb ph.gb))
    (Int.mul (Int.ofNat ph.gd) (Int.ofNat ph.gd)))
  (midPSeqCIV (fastRatS1 ph.ga ph.gd, fastRatS1 ph.gb ph.gd) some) none
private lemma fastEvalPhaseIV_eq_s1 (ph : MidPPhaseSpec) : fastEvalPhaseIVS1 ph = evalMidPPhaseIV
    ph := by
  unfold fastEvalPhaseIVS1 evalMidPPhaseIV
  have hrat : (fastRatS1 ph.ga ph.gd, fastRatS1 ph.gb ph.gd) =
      wdCGaussRat ph.ga ph.gb ph.gd := rfl
  rw [hrat]; refine cond_eq_ite_s1 _ _ ?_ _ _
  simp only [Bool.and_eq_true, Nat.ble_eq, fastBeqZ_iff_s1]
  have h1 : Int.add (Int.mul ph.ga ph.ga) (Int.mul ph.gb ph.gb) = ph.ga ^ 2 + ph.gb ^ 2 := by
    change ph.ga * ph.ga + ph.gb * ph.gb = ph.ga ^ 2 + ph.gb ^ 2; ring
  have h2 : Int.mul (Int.ofNat ph.gd) (Int.ofNat ph.gd) = (ph.gd : ℤ) ^ 2 := by
    change (ph.gd : ℤ) * (ph.gd : ℤ) = (ph.gd : ℤ) ^ 2; ring
  rw [h1, h2]; omega
/-- `Bool`-guarded `List MidPPhaseSpec` evaluator (`= evalMidPPhasesIV`). -/
def fastEvalPhasesIVS1 : List MidPPhaseSpec → Option (List WDCVal)
  | [] => some []
  | ph :: rest =>
      match fastEvalPhaseIVS1 ph, fastEvalPhasesIVS1 rest with
      | some gIV, some tl => some (gIV :: tl)
      | _, _ => none
private lemma fastEvalPhasesIV_eq_s1 : ∀ ps : List MidPPhaseSpec, fastEvalPhasesIVS1 ps =
    evalMidPPhasesIV ps
  | [] => rfl
  | ph :: rest => by
      dsimp only [fastEvalPhasesIVS1, evalMidPPhasesIV]
      rw [fastEvalPhaseIV_eq_s1 ph, fastEvalPhasesIV_eq_s1 rest]
      cases evalMidPPhaseIV ph <;> cases evalMidPPhasesIV rest <;> rfl
/-- Single-probe WHNF-forced stepper (`0` `ghForceInt`, `0` `ghForceNat`, `0` `dite`). -/
def fastProbeStepS1 (r : ℕ) (p : MidPProbeSpec) (st : MidPProbeState) : Option MidPProbeState :=
  cond
    (Nat.ble p.phases.length r && Nat.ble r p.phases.length &&
      Nat.ble 1 p.daDen && Nat.ble 1 p.cDen && fastBeqZS1
        (Int.add (Int.mul p.cNum p.cNum) (Int.mul (Int.ofNat p.sNum) (Int.ofNat p.sNum)))
        (Int.mul (Int.ofNat p.cDen) (Int.ofNat p.cDen)))
    (match fastEvalPhasesIVS1 p.phases with
     | none => none
     | some gIVs =>
         let daIV := fastRatS1 (Int.ofNat p.daNum) p.daDen
         let dphi1 : WDIVal := (ghMaxZ 0 (Int.sub daIV.1 2), daIV.2)
         let dphi2 : WDIVal := midPFastMulIV dphi1 (midPSqrtRatioIv 2)
         let dphi3 : WDIVal := midPFastMulIV dphi1 (midPSqrtRatioIv 3)
         let dphi4 : WDIVal := midPFastMulIV dphi1 (midPSqrtRatioIv 4)
         let maxAng : ℤ := Int.mul 1024 midPScaleZ
         if midPBleZ 0 dphi1.1 && midPBleZ dphi4.2 maxAng then
           let cTop := fastRatS1 p.cNum p.cDen
           midPSeqCIVList (midPFastDampU r gIVs cTop st.uVec) fun uD ↦
           let sHi := midPSumRangeZ (Nat.add r 1) fun w ↦
             Int.mul (Int.ofNat (fastBinomS1 r w)) (wdCAbs2Hi (uD.getD w wdCZero))
           let qdaHi := Int.neg (Int.ediv
             (Int.neg (Int.mul (Int.add daIV.2 4) wdPi4InvHi)) (Int.mul 2 midPScaleZ))
           let stepQ := Int.neg (Int.ediv (Int.neg (Int.mul sHi qdaHi)) midPScaleZ)
           midPSeqInt (Int.add st.qExtraHi stepQ) fun qExNext ↦
           midPSeqInt (Int.add st.qCollAddHi qdaHi) fun qCollNext ↦ fastTrigCPSS1 dphi1 fun c1 s1 ↦
           fastTrigCPSS1 dphi2 fun c2 s2 ↦ fastTrigCPSS1 dphi3 fun c3 s3 ↦
           midPSeqCIVList (midPFastDickeStepVec r c1 s1 uD) fun uNext ↦
           midPFastStep2RowCPS (r - 2) gIVs c1 s1 c2 s2 st.sp0 st.sp1 fun sp0N sp1N ↦
           midPFastStep2RowCPS (r - 3) gIVs c1 s1 c3 s3 st.st0 st.st1 fun st0N st1N ↦
           if Nat.ble 4 r then
             midPFastStepTwoPairCPS (r - 4) gIVs c1 s1 c2 s2 st.tp0 st.tp1 st.tp2
               fun tp0N tp1N tp2N ↦ some ⟨qExNext, qCollNext, uNext, sp0N, sp1N, st0N, st1N,
                   tp0N, tp1N, tp2N, [], []⟩
           else
             some ⟨qExNext, qCollNext, uNext, sp0N, sp1N, st0N, st1N, [], [], [], [], []⟩
         else
           none)
    none
private lemma fastProbeStep_eq_s1 (r : ℕ) (p : MidPProbeSpec) (st : MidPProbeState) :
    fastProbeStepS1 r p st = evalMidPProbeStep r false p st := by
  unfold fastProbeStepS1 evalMidPProbeStep; rw [fastEvalPhasesIV_eq_s1]
  refine cond_eq_ite_congr_s1 _ _ ?_ ?_
  · simp only [Bool.and_eq_true, Nat.ble_eq, fastBeqZ_iff_s1]
    have h1 :
        Int.add (Int.mul p.cNum p.cNum) (Int.mul (Int.ofNat p.sNum) (Int.ofNat p.sNum)) =
          p.cNum ^ 2 + (p.sNum : ℤ) ^ 2 := by
      change p.cNum * p.cNum + (p.sNum : ℤ) * (p.sNum : ℤ) = p.cNum ^ 2 + (p.sNum : ℤ) ^ 2; ring
    have h2 : Int.mul (Int.ofNat p.cDen) (Int.ofNat p.cDen) = (p.cDen : ℤ) ^ 2 := by
      change (p.cDen : ℤ) * (p.cDen : ℤ) = (p.cDen : ℤ) ^ 2; ring
    rw [h1, h2]; omega
  · cases evalMidPPhasesIV p.phases with
    | none => rfl
    | some gIVs =>
        have hnf : ¬(false = true) := Bool.false_ne_true
        have hda : fastRatS1 (Int.ofNat p.daNum) p.daDen = wdRat (p.daNum : ℤ) p.daDen := rfl
        have hct : fastRatS1 p.cNum p.cDen = wdRat p.cNum p.cDen := rfl
        have hdc : ∀ a b : ℤ, Int.neg (Int.ediv (Int.neg a) b) = wdDivCeil a b := fun _ _ ↦ rfl
        conv_lhs => dsimp only; rw [hda, hct]; simp only [fastBinom_eq_s1, fastTrigCPS_eq_s1, hdc]
        conv_rhs => dsimp only; simp only [ite_eq_right hnf]
/-- Multi-probe WHNF-forced chain evaluator (`= evalMidPProbes r false`). -/
def fastEvalProbesS1 (r : ℕ) : List MidPProbeSpec → MidPProbeState → Option MidPProbeState
  | [], st => some st
  | p :: rest, st =>
      match fastProbeStepS1 r p st with
      | none => none
      | some st' => fastEvalProbesS1 r rest st'
theorem fastEvalProbes_eq_s1 (r : ℕ) : ∀ (ps : List MidPProbeSpec) (st : MidPProbeState),
    fastEvalProbesS1 r ps st = evalMidPProbes r false ps st
  | [], _ => rfl
  | p :: rest, st => by
      dsimp only [fastEvalProbesS1, evalMidPProbes]; rw [fastProbeStep_eq_s1 r p st]
      cases evalMidPProbeStep r false p st with
      | none => rfl
      | some st' => exact fastEvalProbes_eq_s1 r rest st'
/-- Evaluates initial row state and first probe slice `ps0` (`includeRm3 = false`). -/
def evalMidPRowInitProbesS1 (m r : ℕ) (spec : MidPRowSpec) (ps0 : List MidPProbeSpec) : Option
    MidPProbeState :=
  let p := Stage2CertInternals.gridExp m
  if 3 ≤ r ∧ r ≤ 16 ∧ r - 1 < m ∧ 2 ≤ p ∧ p ≤ 10 ∧ m = 2 ^ p ∧
      0 < spec.a0Den ∧ 0 < spec.kzDen then
    let a0IV := wdRat (spec.a0Num : ℤ) spec.a0Den
    let phi01 : WDIVal := (ghMaxZ 0 (Int.sub a0IV.1 1), Int.add a0IV.2 1)
    let phi02 : WDIVal := midPFastMulIV phi01 (midPSqrtRatioIv 2)
    let phi03 : WDIVal := midPFastMulIV phi01 (midPSqrtRatioIv 3)
    let phi04 : WDIVal := midPFastMulIV phi01 (midPSqrtRatioIv 4)
    let maxAng : ℤ := Int.mul 1024 midPScaleZ
    if midPBleZ 0 phi01.1 && midPBleZ phi04.2 maxAng then
      midPTrigCPS phi01 fun c01 s01 ↦ midPTrigCPS phi02 fun c02 s02 ↦
      midPTrigCPS phi03 fun c03 s03 ↦
      midPSeqCIVList (midPFastDickeStepVec r c01 s01 (midPOneHot0 (Nat.add r 1))) fun u0 ↦
      midPSeqCIVList (midPFastDickeStepVec (r - 2) c01 s01 (midPOneHot0 (r - 1))) fun uRm2 ↦
      midPSeqCIVList (uRm2.map (midPFastCRMul c02)) fun sp0Init ↦
      midPSeqCIVList (uRm2.map (midPFastCRMul s02)) fun sp1Init ↦
      midPSeqCIVList (midPFastDickeStepVec (r - 3) c01 s01 (midPOneHot0 (r - 2))) fun uRm3 ↦
      midPSeqCIVList (uRm3.map (midPFastCRMul c03)) fun st0Init ↦
      midPSeqCIVList (uRm3.map (midPFastCRMul s03)) fun st1Init ↦
      let runInit (tp0I tp1I tp2I : List WDCVal) : Option MidPProbeState :=
        fastEvalProbesS1 r ps0
          ⟨0, 0, u0, sp0Init, sp1Init, st0Init, st1Init, tp0I, tp1I, tp2I, [], []⟩
      if Nat.ble 4 r then
        midPSeqCIVList (midPFastDickeStepVec (r - 4) c01 s01 (midPOneHot0 (r - 3))) fun uRm4 ↦
        midPSeqCIVList (midPFastDickeStepVec 2 c02 s02 (midPOneHot0 3)) fun uP2 ↦
        let p20 := uP2.getD 0 wdCZero; let p21 := uP2.getD 1 wdCZero; let p22 := uP2.getD 2 wdCZero
        midPSeqCIVList (uRm4.map (midPFastCMul p20)) fun tp0I ↦
        midPSeqCIVList (uRm4.map (midPFastCMul p21)) fun tp1I ↦
        midPSeqCIVList (uRm4.map (midPFastCMul p22)) fun tp2I ↦ runInit tp0I tp1I tp2I
      else runInit [] [] []
    else none
  else none
/-- Finishes `MidPSummary` from terminal `MidPProbeState` (`includeRm3 = false`). -/
def midPRowFinishS1 (m r : ℕ) (spec : MidPRowSpec) (fin : MidPProbeState) : Option MidPSummary :=
  let a0IV := wdRat (spec.a0Num : ℤ) spec.a0Den; let maxAng : ℤ := Int.mul 1024 midPScaleZ
  let q0Hi := wdDivCeil (Int.mul (Int.add a0IV.2 2) wdPi4InvHi) (Int.mul 2 midPScaleZ)
  let qDistHi := Int.add q0Hi fin.qExtraHi; let qCollHi := Int.add q0Hi fin.qCollAddHi
  let kzIV := wdRat (spec.kzNum : ℤ) spec.kzDen
  let azIV : WDIVal := (ghMaxZ 0 (Int.sub kzIV.1 1), Int.add kzIV.2 1)
  if midPBleZ 0 azIV.1 && midPBleZ azIV.2 maxAng then
    midPTrigCPS azIV fun _ sAz ↦
    let zHitLo := (ghSqIV sAz).1
    let qzSub := wdDivCeil (Int.mul (Int.add kzIV.2 2) wdPi4InvHi) (Int.mul 2 midPScaleZ)
    let uScale := midPUnpaddedZoomScaleHi15 (r - 1) m
    let qZoomHi := wdDivCeil (Int.mul qzSub uScale) midPScaleZ
    if midPBleZ 0 zHitLo && midPBleZ zHitLo midPScaleZ &&
        midPBleZ (Int.add qCollHi qZoomHi) (Int.mul 12 midPScaleZ) then
      midPSeqInt qDistHi fun qdF ↦ midPSeqInt qCollHi fun qcF ↦ midPSeqInt qZoomHi fun qzF ↦
      midPSeqInt zHitLo fun zhF ↦ midPSeqZList (fin.uVec.map wdCAbs2Hi) fun uAbs ↦
      midPSeqZList (fin.sp0.map wdCAbs2Hi) fun z0Abs ↦
      midPSeqZList (fin.sp1.map wdCAbs2Hi) fun z1Abs ↦
      let tpWt :=if Nat.ble 4 r then midPCollapseTwoPairWt (r - 4) r fin.tp0 fin.tp1 fin.tp2
        else List.replicate (Nat.add r 1) 0
      let stWt := midPCollapse2RowWt (r - 3) r fin.st0 fin.st1
      let q1Wt :=if Nat.ble 4 r && false then midPCollapse2RowWt (r - 4) r fin.q10 fin.q11
        else List.replicate (Nat.add r 1) 0
      midPSeqZList tpWt fun tpF ↦ midPSeqZList stWt fun stF ↦ midPSeqZList q1Wt fun q1F ↦
        some ⟨qdF, qcF, qzF, zhF, uAbs, z0Abs, z1Abs, tpF, stF, q1F⟩
    else none
  else none
/-- Total `Option`-to-`Bool` binder avoiding per-def `.match_1` elaborator auxiliaries. -/
def midPOptBoolS1 {α : Type*} (mx : Option α) (f : α → Bool) : Bool :=
  match mx with
  | none => false
  | some x => f x
private lemma midPOptBool_eq_true_s1 {α : Type*} {mx : Option α} {f : α → Bool} (h : midPOptBoolS1
mx f = true) : ∃ x : α, mx = some x ∧ f x = true := by
  cases mx with
  | none => cases h
  | some x => exact ⟨x, rfl, h⟩
/-- Checks `W` Bellman passes at `r` from a forced `MidPSummary` `s`. -/
def checkGHMidPSummaryPassesS1 (m W r : ℕ) (vSeq : List (List ℕ)) (s : MidPSummary) : Bool :=
  (List.range W).all (fun i ↦
    match evalMidPStepFromSummary m r false s (vSeq.getD (i + 1) []) with
    | some hir => Nat.ble hir ((vSeq.getD i []).getD r 0)
    | none => false)
/-- Evaluates final probe slice `psLast` from `stPrev` and checks `W` Bellman passes at `r`. -/
def checkGHMidPRowProbeTailS1 (m W r : ℕ) (vSeq : List (List ℕ)) (spec : MidPRowSpec) (psLast :
    List MidPProbeSpec) (stPrev : MidPProbeState) : Bool :=
  midPOptBoolS1 (fastEvalProbesS1 r psLast stPrev) fun fin ↦
    midPOptBoolS1 (midPRowFinishS1 m r spec fin)
      (checkGHMidPSummaryPassesS1 m W r vSeq)
/-- Monoidal composition of `evalMidPProbes` across concatenated probe lists. -/
theorem evalMidPProbes_append_s1 (r : ℕ) (includeRm3 : Bool) : ∀ (xs ys : List MidPProbeSpec) (st :
MidPProbeState), evalMidPProbes r includeRm3 (xs ++ ys) st = match evalMidPProbes r includeRm3 xs
    st with
        | none => none
        | some st' => evalMidPProbes r includeRm3 ys st'
  | [], _, _ => by
      rw [List.nil_append]; rfl
  | p :: xs, ys, st => by
      rw [List.cons_append]; dsimp only [evalMidPProbes]
      cases evalMidPProbeStep r includeRm3 p st with
      | none => rfl
      | some st1 => exact evalMidPProbes_append_s1 r includeRm3 xs ys st1
private lemma evalMidPProbes_append_of_eq_some_s1 {r : ℕ} {xs ys : List MidPProbeSpec} {st st1 :
MidPProbeState} (hx : evalMidPProbes r false xs st = some st1) : evalMidPProbes r false (xs ++ ys)
    st = evalMidPProbes r false ys st1 := by
  rw [evalMidPProbes_append_s1, hx]
private lemma midPTrigCPS_congr_of_some_s1 {α β : Type*} {x : WDIVal} {k₁ : WDIVal → WDIVal →
Option α} {k₂ : WDIVal → WDIVal → β} {v : α} {rhs : β} (h0 : midPTrigCPS x k₁ = some v) (hk : ∀ c s
: WDIVal, k₁ c s = some v → k₂ c s = rhs) : midPTrigCPS x k₂ = rhs := by
  rw [midPTrigCPS_eq] at h0 ⊢; exact hk (wdTrig x).1 (wdTrig x).2 h0
/-- Factorizes `evalMidPRowSummary` through `evalMidPRowInitProbesS1` and `midPRowFinishS1`. -/
theorem evalMidPRowSummary_of_initProbes_s1 {m r : ℕ} {spec : MidPRowSpec} {ps0 psRest : List
MidPProbeSpec} {st0 fin : MidPProbeState} (h0 : evalMidPRowInitProbesS1 m r spec ps0 = some st0)
(hrest : evalMidPProbes r false psRest st0 = some fin) (hpr : spec.probes = ps0 ++ psRest) :
    evalMidPRowSummary m r false spec = midPRowFinishS1 m r spec fin := by
  unfold evalMidPRowInitProbesS1 at h0; unfold evalMidPRowSummary; dsimp only at h0 ⊢
  split at h0
  · next hg1 =>
      rw [ite_eq_left hg1]
      split at h0
      · next hg2 =>
          rw [ite_eq_left hg2]; refine midPTrigCPS_congr_of_some_s1 h0 fun c01 s01 h0 ↦ ?_
          refine midPTrigCPS_congr_of_some_s1 h0 fun c02 s02 h0 ↦ ?_
          refine midPTrigCPS_congr_of_some_s1 h0 fun c03 s03 h0 ↦ ?_
          conv at h0 => lhs; simp only [midPSeqCIVList_eq]
          conv_lhs => simp only [midPSeqCIVList_eq]
          by_cases hr4 : Nat.ble 4 r = true
          · rw [ite_eq_left hr4] at h0 ⊢
            have hnf : ¬(false = true) := Bool.false_ne_true
            rw [ite_eq_right hnf]; rw [fastEvalProbes_eq_s1] at h0
            rw [hpr, evalMidPProbes_append_s1, h0]; dsimp only; rw [hrest]; unfold midPRowFinishS1
            rfl
          · rw [ite_eq_right hr4] at h0 ⊢
            rw [fastEvalProbes_eq_s1] at h0; rw [hpr, evalMidPProbes_append_s1, h0]; dsimp only
            rw [hrest]; unfold midPRowFinishS1; rfl
      · cases h0
  · cases h0
/-- Prepends an intermediate probe slice onto `checkGHMidPRowProbeTailS1`. -/
lemma checkGHMidPRowProbeTail_cons_s1 {m W r : ℕ} {vSeq : List (List ℕ)} {spec : MidPRowSpec}
{psMid psLast : List MidPProbeSpec} {stPrev stNext : MidPProbeState} (hmid : fastEvalProbesS1 r
psMid stPrev = some stNext) (htail : checkGHMidPRowProbeTailS1 m W r vSeq spec psLast stNext =
true) : checkGHMidPRowProbeTailS1 m W r vSeq spec (psMid ++ psLast) stPrev = true := by
  unfold checkGHMidPRowProbeTailS1 at htail ⊢; rw [fastEvalProbes_eq_s1] at hmid htail ⊢
  rw [evalMidPProbes_append_of_eq_some_s1 hmid]; exact htail
private lemma checkGHMidPRowsSlice_of_summary_s1 {m W r : ℕ} {vSeq : List (List ℕ)} {spec :
MidPRowSpec} {s : MidPSummary} (hsum : evalMidPRowSummary m r false spec = some s) (hp :
checkGHMidPSummaryPassesS1 m W r vSeq s = true) : checkGHMidPRowsSlice false m W vSeq r [spec] =
    true := by
  simp only [checkGHMidPRowsSlice]; rw [hsum]; dsimp only [checkGHMidPSummaryPassesS1] at hp ⊢
  rw [Bool.and_true]; simp only [List.all_eq_true] at hp ⊢; intro i hi; have hpi := hp i hi
  cases hst : evalMidPStepFromSummary m r false s (vSeq.getD (i + 1) []) with
  | none =>
      rw [hst] at hpi; cases hpi
  | some _ =>
      rw [hst] at hpi; exact hpi
/-- Certifies a single-row `checkGHMidPRowsSlice` from `2` probe slices (`ps0, ps1`). -/
theorem checkGHMidPRowsSlice_of_probes2_s1 {m W r : ℕ} {vSeq : List (List ℕ)} {spec : MidPRowSpec}
{ps0 ps1 : List MidPProbeSpec} {st0 : MidPProbeState} (h0 : evalMidPRowInitProbesS1 m r spec ps0 =
some st0) (htail : checkGHMidPRowProbeTailS1 m W r vSeq spec ps1 st0 = true) (hpr : spec.probes =
ps0 ++ ps1) : checkGHMidPRowsSlice false m W vSeq r [spec] = true := by
  unfold checkGHMidPRowProbeTailS1 at htail
  obtain ⟨fin, hfin, htail1⟩ := midPOptBool_eq_true_s1 htail; rw [fastEvalProbes_eq_s1] at hfin
  obtain ⟨s, hms, hp⟩ := midPOptBool_eq_true_s1 htail1
  have hsum : evalMidPRowSummary m r false spec = some s :=
    (evalMidPRowSummary_of_initProbes_s1 h0 hfin hpr).trans hms
  exact checkGHMidPRowsSlice_of_summary_s1 hsum hp
/-- Certifies a single-row `checkGHMidPRowsSlice` from `3` probe slices (`ps0.. ps2`). -/
theorem checkGHMidPRowsSlice_of_probes3_s1 {m W r : ℕ} {vSeq : List (List ℕ)} {spec : MidPRowSpec}
{ps0 ps1 ps2 : List MidPProbeSpec} {st0 st1 : MidPProbeState} (h0 : evalMidPRowInitProbesS1 m r
spec ps0 = some st0) (h1 : fastEvalProbesS1 r ps1 st0 = some st1) (h2 : checkGHMidPRowProbeTailS1 m
W r vSeq spec ps2 st1 = true) (hpr : spec.probes = ps0 ++ (ps1 ++ ps2)) : checkGHMidPRowsSlice
    false m W vSeq r [spec] = true :=
  checkGHMidPRowsSlice_of_probes2_s1 h0 (checkGHMidPRowProbeTail_cons_s1 h1 h2) hpr
/-- Certifies a single-row `checkGHMidPRowsSlice` from `4` probe slices (`ps0.. ps3`). -/
theorem checkGHMidPRowsSlice_of_probes4_s1 {m W r : ℕ} {vSeq : List (List ℕ)} {spec : MidPRowSpec}
{ps0 ps1 ps2 ps3 : List MidPProbeSpec} {st0 st1 st2 : MidPProbeState} (h0 : evalMidPRowInitProbesS1
m r spec ps0 = some st0) (h1 : fastEvalProbesS1 r ps1 st0 = some st1) (h2 : fastEvalProbesS1 r ps2
st1 = some st2) (h3 : checkGHMidPRowProbeTailS1 m W r vSeq spec ps3 st2 = true) (hpr : spec.probes
= ps0 ++ (ps1 ++ (ps2 ++ ps3))) : checkGHMidPRowsSlice false m W vSeq r [spec] = true :=
  checkGHMidPRowsSlice_of_probes3_s1 h0 h1 (checkGHMidPRowProbeTail_cons_s1 h2 h3) hpr
/-- Fast 2-multiply interval evaluator helper `uMinZS1`. -/
def uMinZS1 (a b : ℤ) : ℤ := ghMinZ a b
/-- Fast 2-multiply interval evaluator helper `uMaxZS1`. -/
def uMaxZS1 (a b : ℤ) : ℤ := ghMaxZ a b
/-- Fast 2-multiply interval evaluator helper `uDivScalePairS1`. -/
def uDivScalePairS1 (lo hi : ℤ) : WDIVal :=
  (Int.ediv lo midPScaleZ, Int.neg (Int.ediv (Int.neg hi) midPScaleZ))
/-- Fast 2-multiply interval evaluator helper `uMulIVFallbackS1`. -/
def uMulIVFallbackS1 (x y : WDIVal) : WDIVal := midPFastMulIV x y
/-- Fast 2-multiply interval evaluator helper `uMulIVS1`. -/
def uMulIVS1 (x y : WDIVal) : WDIVal := midPFastMulIV x y
/-- Fast 2-multiply interval evaluator helper `uSqIVS1`. -/
def uSqIVS1 (x : WDIVal) : WDIVal := ghSqIV x
/-- Fast 2-multiply interval evaluator helper `uCAbs2HiS1`. -/
def uCAbs2HiS1 (z : WDCVal) : ℤ := wdCAbs2Hi z
/-- Fast 2-multiply interval evaluator helper `uDoubleAngleIterCPSS1`. -/
def uDoubleAngleIterCPSS1 {α : Type*} : ℕ → WDIVal → WDIVal → (WDIVal → WDIVal → α) → α :=
  midPDoubleAngleIterCPS
/-- Fast 2-multiply interval evaluator helper `uTrigCPSS1`. -/
def uTrigCPSS1 {α : Type*} (x : WDIVal) (k : WDIVal → WDIVal → α) : α := fastTrigCPSS1 x k
/-- Fast 2-multiply interval evaluator helper `uCRMulS1`. -/
def uCRMulS1 (rIV : WDIVal) (z : WDCVal) : WDCVal := midPFastCRMul rIV z
/-- Fast 2-multiply interval evaluator helper `uCMulS1`. -/
def uCMulS1 (a b : WDCVal) : WDCVal := midPFastCMul a b
/-- Fast 2-multiply interval evaluator helper `uCombineZipS1`. -/
def uCombineZipS1 : ℕ → WDIVal → WDIVal → List WDCVal → List WDCVal → List WDCVal := midPCombineZip
/-- Fast 2-multiply interval evaluator helper `uAdvanceZipS1`. -/
def uAdvanceZipS1 : ℕ → ℕ → WDIVal → WDIVal → List (List WDCVal) → List (List WDCVal) :=
  midPAdvanceZip
/-- Fast 2-multiply interval evaluator helper `uIterLayersCIVS1`. -/
def uIterLayersCIVS1 : ℕ → ℕ → WDIVal → WDIVal → List (List WDCVal) → List (List WDCVal) :=
  midPFastIterLayersCIV
/-- Fast 2-multiply interval evaluator helper `uDickeStepVecS1`. -/
def uDickeStepVecS1 (deg : ℕ) (cIV sIV : WDIVal) (uList : List WDCVal) : List WDCVal :=
  midPFastDickeStepVec deg cIV sIV uList
/-- Fast 2-multiply interval evaluator helper `uZipRotSubS1`. -/
def uZipRotSubS1 : ℕ → WDIVal → WDIVal → List WDCVal → List WDCVal → List WDCVal := midPZipRotSub
/-- Fast 2-multiply interval evaluator helper `uZipRotAddS1`. -/
def uZipRotAddS1 : ℕ → WDIVal → WDIVal → List WDCVal → List WDCVal → List WDCVal := midPZipRotAdd
/-- Fast 2-multiply interval evaluator helper `uDampShift0AuxS1`. -/
def uDampShift0AuxS1 : ℕ → List WDCVal → List WDCVal → List WDCVal := midPDampShift0Aux
/-- Fast 2-multiply interval evaluator helper `uDamp2Rogrd`. -/
def uDamp2Rogrd (deg1 : ℕ) (gIVs r0 : List WDCVal) : List WDCVal := midPFastDamp2Row0 deg1 gIVs r0
/-- Fast 2-multiply interval evaluator helper `uDamp2Rogrd2`. -/
def uDamp2Rogrd2 (deg1 : ℕ) (gs r1 : List WDCVal) : List WDCVal := midPFastDamp2Row1 deg1 gs r1
/-- Fast 2-multiply interval evaluator helper `uDampUTailS1`. -/
def uDampUTailS1 : ℕ → WDIVal → List WDCVal → List WDCVal → List WDCVal := midPFastDampUTail
/-- Fast 2-multiply interval evaluator helper `uDampUAuxS1`. -/
def uDampUAuxS1 : ℕ → WDIVal → List WDCVal → List WDCVal → List WDCVal := midPFastDampUAux
/-- Fast 2-multiply interval evaluator helper `uDampUS1`. -/
def uDampUS1 (r : ℕ) (gIVs : List WDCVal) (cTop : WDIVal) (uVec : List WDCVal) : List WDCVal :=
  midPFastDampU r gIVs cTop uVec
/-- Fast 2-multiply interval evaluator helper `uStep2RowCPSS1`. -/
def uStep2RowCPSS1 {α : Type*} (deg1 : ℕ) (gIVs : List WDCVal) (c1 s1 cC sC : WDIVal) (r0 r1 : List
    WDCVal) (k : List WDCVal → List WDCVal → α) : α :=
  midPFastStep2RowCPS deg1 gIVs c1 s1 cC sC r0 r1 k
/-- Fast 2-multiply interval evaluator helper `uDicke2ColsS1`. -/
def uDicke2ColsS1 : ℕ → WDIVal → WDIVal → List WDCVal → List WDCVal → List WDCVal → List WDCVal ×
    List WDCVal × List WDCVal := midPDicke2Cols
/-- Fast 2-multiply interval evaluator helper `uStepTwoPairCPSS1`. -/
def uStepTwoPairCPSS1 {α : Type*} (deg1 : ℕ) (gIVs : List WDCVal) (c1 s1 c2 s2 : WDIVal) (tp0 tp1
    tp2 : List WDCVal) (k : List WDCVal → List WDCVal → List WDCVal → α) : α :=
  midPFastStepTwoPairCPS deg1 gIVs c1 s1 c2 s2 tp0 tp1 tp2 k
/-- Fast 2-multiply interval evaluator helper `uProbeStepS1`. -/
def uProbeStepS1 (r : ℕ) (p : MidPProbeSpec) (st : MidPProbeState) : Option MidPProbeState :=
  fastProbeStepS1 r p st
/-- Fast 2-multiply interval evaluator helper `uEvalProbesS1`. -/
def uEvalProbesS1 (r : ℕ) : List MidPProbeSpec → MidPProbeState → Option MidPProbeState :=
  fastEvalProbesS1 r
/-- Fast 2-multiply initial state and probe-prefix evaluator `uInitProbesS1`. -/
def uInitProbesS1 (m r : ℕ) (spec : MidPRowSpec) (ps0 : List MidPProbeSpec) : Option MidPProbeState
    := evalMidPRowInitProbesS1 m r spec ps0
/-- Fast 2-multiply interval evaluator helper `uCheckProbeTailS1`. -/
def uCheckProbeTailS1 (m W r : ℕ) (vSeq : List (List ℕ)) (spec : MidPRowSpec) (psLast : List
    MidPProbeSpec) (stPrev : MidPProbeState) : Bool :=
  checkGHMidPRowProbeTailS1 m W r vSeq spec psLast stPrev
private lemma uBeqZ_eq_of_true_s1 {a b : ℤ} (h : fastBeqZS1 a b = true) : a = b := by
  unfold fastBeqZS1 at h; simp only [Bool.and_eq_true, midPBleZ_iff] at h; omega
/-- Fast 2-multiply interval evaluator helper `uBeqIVS1`. -/
def uBeqIVS1 (a b : WDIVal) : Bool := fastBeqZS1 a.1 b.1 && fastBeqZS1 a.2 b.2
private lemma uBeqIV_eq_of_true_s1 {a b : WDIVal} (h : uBeqIVS1 a b = true) : a = b := by
  rcases a with ⟨a1, a2⟩; rcases b with ⟨b1, b2⟩; unfold uBeqIVS1 at h
  simp only [Bool.and_eq_true] at h; rw [uBeqZ_eq_of_true_s1 h.1, uBeqZ_eq_of_true_s1 h.2]
/-- Fast 2-multiply interval evaluator helper `uBeqCIVS1`. -/
def uBeqCIVS1 (a b : WDCVal) : Bool := uBeqIVS1 a.1 b.1 && uBeqIVS1 a.2 b.2
private lemma uBeqCIV_eq_of_true_s1 {a b : WDCVal} (h : uBeqCIVS1 a b = true) : a = b := by
  rcases a with ⟨ar, ai⟩; rcases b with ⟨br, bi⟩; unfold uBeqCIVS1 at h
  simp only [Bool.and_eq_true] at h; rw [uBeqIV_eq_of_true_s1 h.1, uBeqIV_eq_of_true_s1 h.2]
/-- Fast 2-multiply interval evaluator helper `uBeqCIVListS1`. -/
def uBeqCIVListS1 : List WDCVal → List WDCVal → Bool
  | [], [] => true
  | x :: xs, y :: ys => uBeqCIVS1 x y && uBeqCIVListS1 xs ys
  | _, _ => false
private lemma uBeqCIVList_eq_of_true_s1 : ∀ {xs ys : List WDCVal}, uBeqCIVListS1 xs ys = true → xs
    = ys
  | [], [], _ => rfl
  | [], _ :: _, h => by cases h
  | _ :: _, [], h => by cases h
  | x :: xs, y :: ys, h => by
      dsimp only [uBeqCIVListS1] at h; simp only [Bool.and_eq_true] at h
      rw [uBeqCIV_eq_of_true_s1 h.1, uBeqCIVList_eq_of_true_s1 h.2]
/-- Fast 2-multiply interval evaluator helper `uBeqStateS1`. -/
def uBeqStateS1 (a b : MidPProbeState) : Bool :=
  fastBeqZS1 a.qExtraHi b.qExtraHi && (fastBeqZS1 a.qCollAddHi b.qCollAddHi && (uBeqCIVListS1
  a.uVec b.uVec && (uBeqCIVListS1 a.sp0 b.sp0 && (uBeqCIVListS1 a.sp1 b.sp1 && (uBeqCIVListS1
  a.st0 b.st0 && (uBeqCIVListS1 a.st1 b.st1 && (uBeqCIVListS1 a.tp0 b.tp0 && (uBeqCIVListS1 a.tp1
  b.tp1 && (uBeqCIVListS1 a.tp2 b.tp2 && (uBeqCIVListS1 a.q10 b.q10 && (uBeqCIVListS1 a.q11
  b.q11)))))))))))
private lemma uBeqState_eq_of_true_s1 {a b : MidPProbeState} (h : uBeqStateS1 a b = true) : a = b
    := by
  rcases a with ⟨_, _, _, _, _, _, _, _, _, _, _, _⟩
  rcases b with ⟨_, _, _, _, _, _, _, _, _, _, _, _⟩
  unfold uBeqStateS1 at h; simp only [Bool.and_eq_true] at h
  rcases h with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩
  rw [uBeqZ_eq_of_true_s1 h1, uBeqZ_eq_of_true_s1 h2, uBeqCIVList_eq_of_true_s1 h3,
    uBeqCIVList_eq_of_true_s1 h4, uBeqCIVList_eq_of_true_s1 h5, uBeqCIVList_eq_of_true_s1 h6,
    uBeqCIVList_eq_of_true_s1 h7, uBeqCIVList_eq_of_true_s1 h8, uBeqCIVList_eq_of_true_s1 h9,
    uBeqCIVList_eq_of_true_s1 h10, uBeqCIVList_eq_of_true_s1 h11, uBeqCIVList_eq_of_true_s1 h12]
/-- Fast 2-multiply interval evaluator helper `uCheckOptStateS1`. -/
def uCheckOptStateS1 (mx : Option MidPProbeState) (target : MidPProbeState) : Bool :=
  match mx with
  | none => false
  | some st => uBeqStateS1 st target
private lemma uCheckOptState_sound_s1 {mx : Option MidPProbeState} {target : MidPProbeState} (h :
    uCheckOptStateS1 mx target = true) : mx = some target := by
  cases mx with
  | none => cases h
  | some st =>
      dsimp only [uCheckOptStateS1] at h; rw [uBeqState_eq_of_true_s1 h]
/-- Soundness bridge `uInitProbes_sound_s1` for `S1` sub-parts. -/
theorem uInitProbes_sound_s1 {m r : ℕ} {spec : MidPRowSpec} {ps0 : List MidPProbeSpec} {target :
MidPProbeState} (h : uCheckOptStateS1 (uInitProbesS1 m r spec ps0) target = true) :
    evalMidPRowInitProbesS1 m r spec ps0 = some target := by
  exact uCheckOptState_sound_s1 h
/-- Soundness bridge `uEvalProbes_sound_s1` for `S1` sub-parts. -/
theorem uEvalProbes_sound_s1 {r : ℕ} {ps : List MidPProbeSpec} {stPrev target : MidPProbeState} (h
: uCheckOptStateS1 (uEvalProbesS1 r ps stPrev) target = true) : fastEvalProbesS1 r ps stPrev = some
    target := by
  exact uCheckOptState_sound_s1 h
/-- Soundness bridge `uCheckProbeTail_sound_s1` for `S1` sub-parts. -/
theorem uCheckProbeTail_sound_s1 {m W r : ℕ} {vSeq : List (List ℕ)} {spec : MidPRowSpec} {psLast :
List MidPProbeSpec} {stPrev : MidPProbeState} (h : uCheckProbeTailS1 m W r vSeq spec psLast stPrev
= true) : checkGHMidPRowProbeTailS1 m W r vSeq spec psLast stPrev = true := by exact h
/-- Evaluates a full row `spec` via `uInitProbesS1` and checks `W` Bellman passes at `r`. -/
def uCheckFullRowS1 (m W r : ℕ) (vSeq : List (List ℕ)) (spec : MidPRowSpec) : Bool :=
  midPOptBoolS1 (uInitProbesS1 m r spec spec.probes) fun fin ↦
    midPOptBoolS1 (midPRowFinishS1 m r spec fin)
      (checkGHMidPSummaryPassesS1 m W r vSeq)
/-- Soundness bridge certifying a single-row slice from `uCheckFullRowS1`. -/
theorem uCheckFullRow_sound_s1 {m W r : ℕ} {vSeq : List (List ℕ)} {spec : MidPRowSpec} (h :
uCheckFullRowS1 m W r vSeq spec = true) : checkGHMidPRowsSlice false m W vSeq r [spec] = true := by
  unfold uCheckFullRowS1 at h; obtain ⟨fin, h0, h1⟩ := midPOptBool_eq_true_s1 h
  obtain ⟨s, hms, hp⟩ := midPOptBool_eq_true_s1 h1
  have h0' : evalMidPRowInitProbesS1 m r spec spec.probes = some fin := h0
  have hsum : evalMidPRowSummary m r false spec = some s :=
    (evalMidPRowSummary_of_initProbes_s1 h0' rfl (List.append_nil spec.probes).symm).trans hms
  exact checkGHMidPRowsSlice_of_summary_s1 hsum hp
/-- Evaluates a two-row slice `[spec0, spec1]` at `r` and `r + 1` via `uCheckFullRowS1`. -/
def uCheckRows2S1 (m W r : ℕ) (vSeq : List (List ℕ)) (spec0 spec1 : MidPRowSpec) : Bool :=
  uCheckFullRowS1 m W r vSeq spec0 && uCheckFullRowS1 m W (r + 1) vSeq spec1
/-- Soundness bridge certifying `[spec0, spec1]` from `uCheckRows2S1`. -/
theorem uCheckRows2_sound_s1 {m W r : ℕ} {vSeq : List (List ℕ)} {spec0 spec1 : MidPRowSpec} (h :
uCheckRows2S1 m W r vSeq spec0 spec1 = true) : checkGHMidPRowsSlice false m W vSeq r [spec0, spec1]
    = true := by
  unfold uCheckRows2S1 at h; simp only [Bool.and_eq_true] at h
  exact checkGHMidPRowsSlice_append false m W vSeq r [spec0] [spec1]
    (uCheckFullRow_sound_s1 h.1) (uCheckFullRow_sound_s1 h.2)
/-- Evaluates `r = 2` spine header and first two-row slice `[spec3, spec4]`. -/
def uCheckHdrAndRows2S1 (m kMax W rowsLen : ℕ) (row2 : GHZoomRowSpec) (vSeq : List (List ℕ)) (spec3
    spec4 : GHMidPRowSpec) : Bool :=
  checkGHMidPSpineHeaderAndR2 m kMax W rowsLen row2 vSeq &&
    uCheckRows2S1 m W 3 vSeq spec3 spec4
/-- Certifies `kMax = 4` `checkGHMidPSpine` from a single `uCheckHdrAndRows2S1` check. -/
theorem uCheckSpineK4_sound_s1 {m W : ℕ} {row2 : GHZoomRowSpec} {vSeq : List (List ℕ)} {spec3 spec4
: GHMidPRowSpec} (h : uCheckHdrAndRows2S1 m 4 W 2 row2 vSeq spec3 spec4 = true) : checkGHMidPSpine
    false m 4 W row2 [spec3, spec4] vSeq = true := by
  unfold uCheckHdrAndRows2S1 at h; simp only [Bool.and_eq_true] at h
  exact checkGHMidPSpine_of_slices (rowsMidP := [spec3, spec4]) h.1 (uCheckRows2_sound_s1 h.2)
/-- Certifies `kMax = 8` `checkGHMidPSpine` from `uCheckHdrAndRows2S1` and two slices. -/
theorem uCheckSpineK8_sound_s1 {m W : ℕ} {row2 : GHZoomRowSpec} {vSeq : List (List ℕ)} {s3 s4 s5 s6
s7 s8 : GHMidPRowSpec} (h0 : uCheckHdrAndRows2S1 m 8 W 6 row2 vSeq s3 s4 = true) (h1 :
uCheckRows2S1 m W 5 vSeq s5 s6 = true) (h2 : uCheckRows2S1 m W 7 vSeq s7 s8 = true) :
    checkGHMidPSpine false m 8 W row2 ([s3, s4] ++ ([s5, s6] ++ [s7, s8])) vSeq = true := by
  unfold uCheckHdrAndRows2S1 at h0; simp only [Bool.and_eq_true] at h0
  have ht1 : checkGHMidPRowsSlice false m W vSeq 5 ([s5, s6] ++ [s7, s8]) = true :=
    checkGHMidPRowsSlice_append false m W vSeq 5 [s5, s6] [s7, s8]
      (uCheckRows2_sound_s1 h1) (uCheckRows2_sound_s1 h2)
  have hall :
      checkGHMidPRowsSlice false m W vSeq 3 ([s3, s4] ++ ([s5, s6] ++ [s7, s8])) = true :=
    checkGHMidPRowsSlice_append false m W vSeq 3 [s3, s4] ([s5, s6] ++ [s7, s8])
      (uCheckRows2_sound_s1 h0.2) ht1
  exact checkGHMidPSpine_of_slices (rowsMidP := [s3, s4] ++ ([s5, s6] ++ [s7, s8])) h0.1 hall
end QuantumComputation.Specs.DickeSol
namespace QuantumComputation.Specs.DickeSol.HmzLowK
open QuantumComputation.Specs.DickeSol QuantumComputation.Specs.GroverFindAll.GaussianHammingZoomK2
abbrev hmzRep := @List.replicate (List ℕ)
abbrev hmzP := Int.ofNat
abbrev hmzN := Int.negSucc
abbrev hmzC (a b c d : ℤ) : WDCVal := ((a, b), (c, d))
abbrev hmzAbs : ℤ → ℕ
  | Int.ofNat x => x
  | Int.negSucc x => Nat.add x 1
/-- Structural integer Newton square root for high-m zoom Pythagorean triples. -/
def hmzIsqrt : ℕ → ℕ → ℕ → ℕ
  | 0, _, x => x
  | k + 1, n, x =>
    let y := Nat.div (Nat.add x (Nat.div n x)) 2
    match Nat.ble x y with
    | true => x
    | false => hmzIsqrt k n y
abbrev hmzHyp (a b : ℤ) : ℕ :=
  let aa := hmzAbs a; let bb := hmzAbs b; let n := Nat.add (Nat.mul aa aa) (Nat.mul bb bb)
  match Nat.ble n 0 with
  | true => 0
  | false => hmzIsqrt 8 n (Nat.add aa bb)
abbrev hmzUNat (u : ℕ) : ℕ := Nat.sub u 536870912
abbrev hmzUInt (u : ℕ) : ℤ :=
  match Nat.ble 536870912 u with
  | true => Int.ofNat (hmzUNat u)
  | false => Int.negSucc (Nat.sub 536870911 u)
/-- Unpacks forward `< 2^60` `2`-lane words into bare GMP literals. -/
def hmzUnpk2 : List ℕ → List ℕ
  | [] => []
  | w :: ws => midPLitNat (Nat.div w 1073741824) fun hi ↦
    midPLitNat (Nat.mod w 1073741824) fun lo ↦ hi :: lo :: hmzUnpk2 ws
/-- Reconstructs `k` `MidPPhaseSpec` records (`2` lanes each) with forced GMP literals. -/
def hmzTPh : ℕ → List ℕ → List MidPPhaseSpec × List ℕ
  | k + 1, a :: b :: u =>
    midPSeqInt (hmzUInt a) fun ga ↦ midPSeqInt (hmzUInt b) fun gb ↦
    midPLitNat (hmzHyp ga gb) fun gd ↦
    Prod.casesOn (hmzTPh k u) fun ps rest ↦ (⟨ga, gb, gd⟩ :: ps, rest)
  | _, u => ([], u)
/-- Reconstructs `k` `MidPProbeSpec` records (`r` phases each) with forced GMP literals. -/
def hmzTPr (r : ℕ) : ℕ → List ℕ → List MidPProbeSpec
  | k + 1, d :: c :: s :: u =>
    midPLitNat (hmzUNat d) fun dn ↦ midPSeqInt (hmzUInt c) fun cz ↦
    midPLitNat (hmzUNat s) fun sn ↦ midPLitNat (hmzHyp cz (Int.ofNat sn)) fun cd ↦
    Prod.casesOn (hmzTPh r u) fun ps rest ↦ ⟨dn, 1000000000, cz, sn, cd, ps⟩ :: hmzTPr r k rest
  | _, _ => []
abbrev hmzPrSlice (r k : ℕ) (ws : List ℕ) : List MidPProbeSpec := hmzTPr r k (hmzUnpk2 ws)
abbrev hmzRowMP2 (a0 kz : ℕ) (p0 p1 : List MidPProbeSpec) : GHMidPRowSpec :=
  ⟨a0, 1000000000, kz, 1000000000, p0 ++ p1⟩
abbrev hmzRowMP3 (a0 kz : ℕ) (p0 p1 p2 : List MidPProbeSpec) : GHMidPRowSpec :=
  ⟨a0, 1000000000, kz, 1000000000, p0 ++ (p1 ++ p2)⟩
lemma hmzRowsCons {m W r : ℕ} {vSeq : List (List ℕ)} {x : GHMidPRowSpec}
    {xs : List GHMidPRowSpec} (hx : checkGHMidPRowsSlice false m W vSeq r [x] = true)
    (hxs : checkGHMidPRowsSlice false m W vSeq (r + 1) xs = true) :
    checkGHMidPRowsSlice false m W vSeq r (x :: xs) = true :=
  checkGHMidPRowsSlice_append false m W vSeq r [x] xs hx hxs
/-- Probe slice `mpfMP512_r3_p0` (`len = 40`). -/
def mpfMP512_r3_p0 := hmzPrSlice 3 40 [600045920464411223,588111178153145060,576009649586288957,
  575201060411801488,576444491041616158,921316462183356092,1059817524456941816,857288215985820627,
  577258521540688701,598628259149479079,593237436292217533,576438079841714516,576337810993296579,
  575629775472930886,1082590624479241368,1095489910056368604,687080310239718884,1023133905986577224,
  598126665974114340,576878152001325891,576496723291878895,576267015980786929,576854498282668426,
  695018189376033152,585358335939710951,584563865774198573,624891498780910232,597655654093697685,
  577899622786745673,576390066530620453,576808409067883356,576657974536537713,731495374549646156,
  878936005431578144,577263765695759559,576460753914036224,596129842332637719,600771985952645440,
  576207392146848465,578191324126499228,576833045992741906,1045483000386217344,576911620253418768,
  579832283914046936,579954489692265957,595766008480106759,720861461775576616,576556495178531071,
  576462917525920363,576511240199110522,578232604017831372,907100073086369528,603757154423305772,
  1039486826463033492,594477453771420555,689855479112618971,577326983434315576,576997959968485797,
  577109494781963858,775009338577253861,1051922056012187852,1125855187107669576,882950199977924564,
  593533895426220979,619437136568247295,577406118450540119,577314893379837187,577184837098073266,
  640103814473557341,678421103193923967,1105214482667895588,757030685948323088,593145250335773421,
  641665498995583551,572812496464617705,537460732147055569,551052413527107374,646954432266495788,
  798373840348239317,1134520350180155444,874674100783016088,589462495519753147,765215851143091864,
  613024255381820323,775012061604582524,620135342203884487,664521927617739201,1033306426485058136,
  576487215207547508,1045656538405764212,592400627797276519,737485046949374139,600857992894895919,
  270465850999929376,432166079166474136,576923062046387736,630453286004170688,698421297019400337,
  861030575625997139,607092267767476735,743220116510596096,414798148357347972,741102125377762108,
  833355179691797640,755663667722752359,570480585368426232,946030936358804648,627013600218831647,
  597073537862925647,583976129569263612,577328116362017044,553597700661601861,540361574215211886,
  843402677012623071,426703651753855344,612551985845438789,687200063732499699,603117963436636021,
  578745413448792787,576476777798174097,488841573332296488,542923613477309834,779860895001345489,
  542941526848875957,1141168177787382588,598778939430857624,601439584953269663,689435160744918883,
  651657963887779593,568845664227290935,573636768910652022,796708531294405607,552527421417904707,
  761359094929549631,650189399466162368,592301220494673985,590947944102736287,579687725421886823,
  579580754885231233,580547628985785089,776351250673689636,713029352861555549,616278806227239843,
  738530781097485867,593442616810656671,606550177199374128,583589169333748740,581398665345596391,
  588247594825086731,600566902118020704,543436660275807164,769430120202778487,898097211807445472,
  602121448500223747,649090715757937224,587161648050873443,643970771310767156,629668075793153089,
  1025482114936963044,969307082627233752,699965780130755739,705219281047378619,605809820500701115,
  705923286437106320,800073854164351784,508914087145002075,463265588394293167,928427753397219828,
  1125149444641977068,576630364320055628,820410823647641327,593554628200591271,577123620938877779,
  576909615846367255,590375544963529232,577882070292248393,589519253017132917,579748074692302244,
  1136888307282766136,641053603509538419]
/-- Probe slice `mpfMP512_r3_p1` (`len = 40`). -/
def mpfMP512_r3_p1 := hmzPrSlice 3 40 [608711583133131281,742019690727313647,709386486033442568,
  566283932068434320,564964698453641158,626494462202028588,670994068781995164,589413114699845084,
  581810478202347599,610190855646296127,680606992688617117,682479164823508565,604502023612845157,
  608338932135475108,606023605457451383,571468700545108316,754259227351204436,654621783189175523,
  594042036557393601,596809552215565140,582426062141928832,581585655080862316,579825940273108124,
  740109525263564957,680707138193291723,578968718462297468,686285832564062967,586817951704505903,
  588887081514619919,538806559865369195,574458039754634299,572965255067000329,645295992935426028,
  283576735727754776,581718966412053908,1086694315410498852,603257438355613267,593407160820678329,
  555582272569381233,576459095153586233,568603625588105455,725929222587001721,652692986379280521,
  1072631892279929648,986524564710516252,589648953734896233,597460927060928075,581136619839850171,
  606350783661338913,605858446784515299,614866295655262836,320766855378467324,882989930755199408,
  804086443341152289,601757879398526087,580814020477807587,566881949273489572,576505030932650148,
  596254346950732157,623164313138550719,577394954398258556,862053867688009812,602374519626082731,
  576761248433050849,627764970578200424,680376457185076221,518846648696827124,539538985967914392,
  585635579303278116,765424321352751572,585476756775907047,843906502283674959,598591419199330348,
  592937101291665129,593546863093440060,570565125598569683,568699923069058610,600325797688128488,
  1030535569046426112,773831795897822717,767855924431541789,576460758444858856,684946926954617467,
  670128393267590348,552155830408673883,537707593653632572,576501111574235804,616754881859581343,
  648651043092251424,929239632953072048,601363659343529448,576460812266158421,511386479302141207,
  572587705981181480,572728579823352919,1073018564078537756,859721675766114363,718752670346560788,
  786241905216304716,596845795178520520,579200340016134245,569066945276288500,567547653097904640,
  576450695125500026,621300579723756656,741513332103027008,612392896979531952,580106020432510959,
  594327853362915209,578110638869626044,588694268706989317,576955125500934227,576141855830690445,
  581750719105944792,631102366170035447,598524413234125848,615771438529404816,595639830892042719,
  583828700517139885,576461547473306880,578879763356341235,580615553879789891,597735610282297628,
  431610634431305768,736726183432383828,613610102642361917,593365609950659845,580544480931577499,
  607731288754934932,581486127711633892,594806195634205981,722607809415444468,756685916044687196,
  653351463915629408,744201964385501712,599589849039662711,773315863459409979,725038579587327501,
  628302111912231008,577374585529373237,684564037097755676,736338196022590623,582011117602693931,
  965680173608679648,590676187487461115,580530333218123705,572757735283782945,583675138608807153,
  593235245852467785,868128199242155084,780274994186654699,602277689591457801,711459637702311516,
  604141919068858497,576471215559608241,566344352536348456,577587545095019944,579513769164092785,
  642308581187154176,890384354578553672,658374919942936496,984167720723291976,604075829688675987,
  590672864297674996,574706616321337137,576877656726994713,576470210386484825,733397791681642992,
  814236954171068439,691751338432504988,1025375369973038252,591958895460716004,595939818064535547,
  581564621673618767,579019832056016192,578745803231609661,585710733711529971,806212855745940231,
  578077297999867092,626168873594238792]
/-- Schedule `mpfMidPRow_m512_r3` (`L = 80`). -/
def mpfMidPRow_m512_r3 : GHMidPRowSpec :=
  hmzRowMP2 1044214884 1540345538 mpfMP512_r3_p0 mpfMP512_r3_p1
/-- Probe slice `mpfMP512_r4_p0` (`len = 40`). -/
def mpfMP512_r4_p0 := hmzPrSlice 4 40 [597128372799881224,587178662276302023,576712395142373779,
  579775243787115769,582139773615248768,582251211661511964,870761482309001096,712819491972499643,
  724805155483956444,1141805892484038404,686999132136466367,597756704019892896,604557405857775833,
  579674556635370372,576859904590855981,576968087300383764,576901774060115866,709946226537926052,
  963551196931803996,585868448131716896,591764215237176101,761288656395671936,597262000344786559,
  710048615302817481,576438994625236839,575912938577298364,575525475544501152,576105875817686700,
  1019363038659755832,1037927441949165528,1033619042143235388,813559083771898667,674532286259079848,
  593543754812638535,712654346672308023,550523960758385440,575299223158943619,565725082748710144,
  571306808209496572,752614859397583407,971105855396825756,585308094485330576,691879808408723853,
  576501513153672144,591567068068817793,723095008007288493,616071891916369987,599002532220189259,
  583391580353627445,677352176047198800,854432272194168984,997055573100376484,582458091625371192,
  830975060109232161,674282567164412159,591355763015613139,665606918072773888,576790169649241325,
  577480460083427897,576633127252210620,577032484939991484,609285930539907596,722605690920153849,
  1028711176569138996,576603018263264552,691636907615231768,593547661756965264,578202077539946504,
  576458254305385163,576375991868817315,576491732936333543,575838420682713153,629197088619370061,
  773035019362055733,797285873593653389,782221297278129999,686818858400623212,590678649440970973,
  601877145420081283,574077342602009244,573605609994433453,576377796064439175,573187738666386643,
  840128210028307992,716446987546716204,630596522974902752,582551703639397199,685724315665068416,
  596453039928661045,690765384664240176,576407528787895384,563505498474058483,567580388517031453,
  563837435951208460,1072420077511713308,1048704180580931412,951386159462212488,816342994585957524,
  1013637061106051612,594985024575811159,761808262783418005,568438943705271675,563145877929323625,
  304119067459359099,318595146946255975,584563006783397013,586734609893073572,594218266129862316,
  945255085050699104,841620729324400023,591422712729580685,578608215182504955,836183279414578669,
  237183612775834563,252911628358155913,279876768393885428,602970394806627467,1085736133908763676,
  582937786858099097,707542859435787348,919036624721589708,590346877351914884,679582347686524736,
  441720884720327151,423925556225181072,726741195650904771,991751418560821257,577905198660662628,
  598004021034658683,876165019231224276,896736138756202032,739589231779072748,592100278174797295,
  576597100893442096,583540105808719823,828594273869695940,560184489982229160,566406757326248558,
  721733477584984697,862911573715408371,898994112592747976,1143317134704000768,1054584581397318828,
  591338045091366059,629496989362131029,353971315139846048,535926123854777173,597603326290407564,
  622213204434993566,669888857557223568,910103066942903156,1087899704207466144,581803786645663247,
  859012177197532809,587241693561734027,745603664538346443,576276469180663135,724931570637936001,
  522642716884313295,540540463886380714,692642634371642216,633343554126827004,605812917144609948,
  510777862011069384,522109400928825816,592914843636930832,653278116791536765,580351593783618943,
  576572379045555937,576303454317419681,565712219241919836,616962251505059249,458181004102974041,
  497834533535747612,600777174000518433,774498135059422628,595451771222148464,633756577688049820,
  592355298385563771,553478842443236752,571245203496002484,556362441584408257,670999335315462171,
  668955026331486348,396682192956000576,625661170821972461,681244785297993992,598643326935193757,
  584362182847842360,597134286937878627,575884261365999115,483458446368993995,480018331665720230,
  596715174370600601,756857093815851728,565880165307058061,682926432609421404,588890852050302543,
  586812986816511296,588896746270716455,576232862113623116,571376417217203537,580077295694502905,
  576473921225436674,896701630956148496,596105525239056579,716281253803592036,847028105973594653,
  742765725120157472,594788681206675113,753301220914282083,581927821083590841,567159838039350069,
  559578786931303500,567138651964230381,590292287000552339,580126378568899121,393384110957585624,
  784793066776405004,625773162148950999]
/-- Probe slice `mpfMP512_r4_p1` (`len = 40`). -/
def mpfMP512_r4_p1 := hmzPrSlice 4 40 [584431375928244464,595441234669093784,587910105999019740,
  576497761778558005,569216865357316892,575093453231936934,1075430722733541924,942791788267057028,
  621490144523578256,672580621973433549,814803773865108387,594489774647052328,580081727174273560,
  647075256255325729,519234789052679829,574630018807385164,574644133079371639,624449023736032751,
  761280491681077748,687075857425003089,591407557931636432,578032453172590929,602331005314269196,
  646762062749821783,560253358627015356,458632924159497783,704627430399115693,644795920213087569,
  1103411582285903868,670966740762559599,615185213087440563,742575407637005337,665899924898572001,
  596996744903032051,576523266444905143,425861143400664329,576823050594590112,569357805761607473,
  572773970113788759,754141445405778561,943255567175786244,1020490899132990276,578076339148476953,
  587240967208503144,593623691365856548,623172719375739005,435765290684038715,514278100559796844,
  686252440265429193,578968893494883062,576777237169187436,859535008939335212,682040446359999543,
  1147117908043105244,576472040014348433,593333925927576212,577251298713018919,581285607713161415,
  445486627158025977,582613139211969403,609271017341009925,1039586495484904956,888160396885887612,
  740462489883754569,728967413667379401,1077213067597677512,601744768275240793,743827408057060648,
  585724927686168440,391897288339105347,591555394010026397,595758646504539096,798764453756731728,
  771394436334923541,644325772648727232,782175972509428907,812666051648028912,594622196510548373,
  593680251921788556,583224550187655680,568126395773361811,582109859148005792,588056622309777855,
  935802708304625652,576053397740417924,143773490416852368,915539675424941352,744683557010887128,
  588290020659061168,580152122061265945,574693382580016969,582056811762760764,576579219984777277,
  580607711290188450,1063062181294375592,1041044044066469892,1112451272922662744,593175360027765804,
  1032281286516610776,576490166926120388,577443779989858987,467026742914863276,676450603621303165,
  528590477655155449,564400613535969554,830499730797030428,750080943541702076,714911690840497779,
  849150515647725803,619640881928975756,592298116237980121,577842710108039579,576465945552373457,
  582035431943243035,575025267781242333,575027260286428313,788919560850886629,752126555919045537,
  585278320699197209,748582245850818153,828822366775885587,611147548708349495,593675496837880201,
  306124000481559613,497906363838774371,742453452468121059,916422794606407320,652326774914746916,
  747444885864571248,639183878626041128,728162005301768504,1134329134016849352,593678138616782376,
  604496434510330241,616193023018882055,513199183137527156,582650450379761536,586221992680513102,
  943594871918567108,862265443134751559,866181247484467004,610690990429211456,614169845219595896,
  583568325806983012,585522168806214980,609234502619846184,576811206310803796,568921080827656605,
  568517335380393984,986211521697579044,656980592123617289,931473617455075472,605886399484828296,
  598086931077101597,576460753177409785,729299749749349837,609794110193868231,764237582052029084,
  556263279651881859,419434708391928233,1004506209858865332,752057904137719184,683774815440232896,
  714152606809368413,1029267073984703636,601269901385881393,580328388235569892,598666630626951645,
  589158381328857489,573011963071910984,562675985531855948,749234659959027351,1122856662139768572,
  730357768657454292,818674135348765064,742371372011618712,583341681567794875,724305273923831680,
  576467486290946321,576392737758348104,574871348012943813,540917901312598083,837478044411437207,
  1087810609459237592,1084545351961467744,609421362663179849,1130856382337290028,596011242222917749,
  584330271130624003,576447563248791484,540218896542064660,583553576846094827,586487117791619203,
  683469037315567104,686619191812125704,650998302869847368,719494442383482593,875754181993153584,
  590185883720937931,716748845885203108,576279766402630252,534161916688588669,576722363745395857,
  579957328680128073,611716849810890056,646457032085033348,831985300929091461,734368559445321792,
  953544784271675144,593195338239129379,593104846355302565,576438707175429315,586841641959366049,
  571421046972024503,574601805113398647,1015986663819954876,581657662194716976,684989949658403964,
  770696461207278141,808891511954627996]
/-- Schedule `mpfMidPRow_m512_r4` (`L = 80`). -/
def mpfMidPRow_m512_r4 : GHMidPRowSpec :=
  hmzRowMP2 1104123542 1535807244 mpfMP512_r4_p0 mpfMP512_r4_p1
/-- Probe slice `mpfMP512_r5_p0` (`len = 36`). -/
def mpfMP512_r5_p0 := hmzPrSlice 5 36 [589976678915541708,607822592558794781,561459218075913053,
  575603636454142908,569342775688596160,566380180175570200,570406482126617949,997675283371162184,
  593129090345591096,860538050236815959,886297620178611996,621085205347815161,1062005655677131976,
  589124725253213969,714122597959398896,576558086466914143,576490878086459401,576141396311923849,
  577059050607879673,579347400370970234,1146999349814254452,846731688884290583,735417947731770569,
  644444694952096691,673452045075890571,638722359699798681,592873967562577103,736605686958457031,
  570636416512661260,574441857499386044,572807929465129220,573898853216876611,575501536334304692,
  976589923109465256,1085575491304288976,959768273488327332,1120815609920859752,1149023331622445768,
  981908473417447568,599133359215502495,650266081220775679,575377880370745745,573712532495058595,
  578507833327903463,575107443155590928,575696902590175080,886370800059468288,1031882357088294924,
  807287021695776108,966533418211239416,740097891199941744,648817707172429688,587562418666965813,
  576559867877274044,590137727708036235,664594328317780867,658791294777761845,634021779987298060,
  576472635951342851,1089268199000741544,841596354329993244,800939942648394872,626960844088701228,
  1047099024634251024,949131683900949804,588256421388636743,735188949083947503,576065392642518140,
  576373602698868127,575384417192329851,576578894582622676,576474070470793621,855768760732218468,
  851665588401641981,1071367576278975024,862964586497943977,685463775817398881,947413286813062116,
  589924041001241197,668204926805652481,573359958471823525,578182936049048769,577617534062093557,
  580014542006603603,576906961300063871,623851018261015119,862270146122556299,828080746156068891,
  594564645583387013,887721966624789212,579509343175566764,588538173027032729,606827348448830224,
  576557002080368607,580368443383366595,596058676261851651,597869081894108081,582304442404799926,
  703579733132793431,770944959426497603,579704143564770708,614244240494463752,682699780752710508,
  580098379686611499,589323370318224645,589051685919160873,568816595929457852,578025026318103556,
  579351097266844063,576660254429755087,580649222138948131,914154604136916092,869459488656055872,
  760462954302103043,782683135112135399,580159508882394752,825191318719208264,589394166682346533,
  718662915314096232,580611691895842172,589679267637302788,590622846451096631,601373985522289400,
  576654920807357333,1000824669057649688,582547929458249828,576460753914036224,782049842185082591,
  822854934893450159,874197660070804968,588971598988134759,803289082870571845,468337678917939843,
  594735886230190941,578620894016754512,563067712818013489,546865275675702543,873740374920846288,
  822348231830838399,814495597098730583,828918423692751567,1056583974573875868,658305842906312291,
  588586887624584568,611288564593457945,518584247647117561,685402203317529608,603118628215283860,
  590487485743972712,576602496435382482,794340771580561541,1152897868864899836,1143264875720267252,
  1149854611800407772,1140037218500343708,1095915932149331112,590167579476449176,616185877087023639,
  564015784473046516,810940870632456637,569061318766389344,574501939992193619,482523242496126475,
  716087044043744652,711079643670658523,648725209684958169,581048092518718956,1124101474646150064,
  839710202258697372,597359148920954508,600383631558413631,575910284199817073,457816189702829237,
  560595612044595124,647315536180461479,651200682823129582,698143400862945732,701430625977428913,
  587303526629829081,923524562605778184,707036661047693484,817674993911499317,597484857582355777,
  754820874507200547,438576854001850551,871506735372477303,307934475480873120,581891387971632421,
  605237098168015029,982573403231856336,746118781438671633,716051105935285832,602958248621567171,
  589428907301111832,612294695784109209,597708201271647245,764348431127642833,325553401977921135,
  570584498787087944,311604311552186385,583067125584879328,579358669289021064,972263480256383912,
  576584898869979989,576680284724974128,1082787952153103024,933168486627947172,584871843920800736,
  592056066140997463,587746303902073807,574963948357895531,587080450847318363,548240279466798184,
  576559838896528931,576801219208188026,827052737261369133,576323319255449988,1112290157820933044,
  557400693665741904,577176845221324496,1136528230200712148,591834436071243876,600740163602550547,
  577406217120992668,586847990847201712,559330670220498611,580172038633590435,578702231864281678,
  603983839589292393,576824377656479763,756259224017290512,709172484774024663,764904676377305129,
  1108306365316399088]
/-- Probe slice `mpfMP512_r5_p1` (`len = 36`). -/
def mpfMP512_r5_p1 := hmzPrSlice 5 36 [594736193184272411,594480395543203916,576865163815483532,
  579753847418126013,559321192266690835,575546900131042761,575637708278580318,730622857333122417,
  637523823401954847,231766298211310488,424726476450861756,729317775499727957,962683632571626704,
  590103915110366531,582070388629682889,585108325922192005,570604921417913928,577033359030341028,
  579102412235491456,577693682270612016,829678040204303217,749036305479086187,1147255757167384416,
  851738358035935167,606871091611763748,581558648166084512,593433729442028353,707332186005943180,
  390235071530971775,516121143875246245,642314898030294021,553845134721211521,430268991030182014,
  727813514918563589,743104580913927096,768496745417032328,579802696958115507,610692243482830601,
  1112393316460432992,600245793401751209,581787586231651248,580199119596500085,562008089522916627,
  626100151059765728,570307773532331213,551674775758635997,871584793220409584,170683608389964912,
  698475028145118416,486066662938655856,857620418770584473,775975093016715656,586976876627678833,
  589145809909398544,576325830102669737,569623285297135764,577739103693046188,576542336949540917,
  578087433058339500,843589172990629967,613759549140637724,591013625675384876,792745233134879676,
  681108983924922981,582758390372040243,579761098239981476,682756087955402632,583846867176953469,
  561470737276524615,604531035647756772,585106405074129192,591999359344862507,598513458916623048,
  690236810555845484,966180017480914076,666180488289103968,879554779229991516,863306595827429136,
  592542347357670663,576928655641466935,580715459351251575,578483339087907703,583944149751286717,
  563129136233418329,564344624340499196,780869255631316076,899943590160715836,616769171288602131,
  485759939769378732,971417882542458644,861363679231789512,590538637963945528,582206089205188737,
  582919026560527399,578989707100661667,577418723916893283,573745350463361571,569582547411780783,
  832983529721853668,846097159012951553,603487211431091904,680527068470909756,614637502733031756,
  1089488129206958712,588765772194929123,752680997957572243,597038014171573068,575947206942029292,
  581637059501830780,592368628217529111,600194870978225257,579258636270886643,580195193618229536,
  1063697496981651596,882115904726438256,806780706252325613,590661164556296963,588814024753012215,
  576909791785496156,580960518592345479,529272608812385819,610905561638250967,575870762146666707,
  556813927469867634,633118936010955572,712639034631210357,564764414451782991,359364485443752512,
  760992058746266604,1078458380191430516,588687833494435559,589115797107599075,595858753654057516,
  586687977336236956,571215570514673503,556406606178315089,553589235956772929,852133966400039504,
  988219732442567448,792326020666151924,578148138116669621,576922821528126752,909289823506686812,
  595843921040733908,638727793912219995,576836111632475268,624392883382701980,507469167381194680,
  576457839852694412,575951415909033943,1062301907501291732,1121484563957337756,628053124065751229,
  590624694915192416,1100459739122855988,1113627980006422748,577982360073754563,583835284706515015,
  576327978376536081,602546417364758524,596911534909962075,575127050060627997,512394508115707419,
  582404230592443088,596986821355155944,572767175622233847,576440827413292508,636621962721154308,
  687629207894065773,594264389823687124,577245910678207123,572541118441942171,576438810244931191,
  591312286124881956,578285945648864909,577838969207345933,755354451539544581,1126436914654579152,
  749025924525748119,1084318154619193296,1065446010410645256,1105206006583287704,576501120454184173,
  706592116067416636,587431608057918715,549793657530400756,410590313090935379,576475720937975800,
  651774431385426823,949487494026782592,587327514020453931,703597912635088844,656640932103495324,
  633136789099143383,755880902828471987,588300634656398883,581138964555379352,576734495997073320,
  566599277104339655,575363912697859633,577141247911083491,595420263214560613,617098505035417761,
  587240764270991237,967331586327334424,836392153191563844,834779598064192803,606119708559242928,
  593421173330356285,587060169705561099,576810693945866872,575704872116105073,581847457892652184,
  576320343161317327,575273374787117690,749827404179773317,666612932428662761,607343623916048388,
  810383388173804784,1060489392629217056,761823403445581964,594167039192134284,581803901602254705,
  576530580950993595,581068999566640804,586052569350632039,569281414708792697,567280749897198246,
  768381963467481611,632832713996298191,778037944379243396,1070348429941495856,803360637748931072,
  590800325791220177]
/-- Schedule `mpfMidPRow_m512_r5` (`L = 72`). -/
def mpfMidPRow_m512_r5 : GHMidPRowSpec :=
  hmzRowMP2 1154764608 1532298398 mpfMP512_r5_p0 mpfMP512_r5_p1
/-- Probe slice `mpfMP512_r6_p0` (`len = 24`). -/
def mpfMP512_r6_p0 := hmzPrSlice 6 24 [590905959575052563,629692736642717243,558946370129849827,
  576341047830303336,574168298384122175,539183194306791804,557352062509429689,546818563614000987,
  856346119208155961,576460753914036224,576460753914036224,576460753914036224,576460753914036224,
  576460753914036224,576460753914036224,591979651877937188,579753836336387427,576460594018319236,
  576388001467306125,576558691216519483,575502060345581388,576296817437586747,575780743567673709,
  856346119208155961,576460753914036224,576460753914036224,576460753914036224,576460753914036224,
  576460753914036224,576460753914036224,590594196382237229,588483289732295680,577068266536136275,
  575636870995515460,570547540004291133,573178388679712735,575983530656080665,575564882805053739,
  856346119208155961,576460753914036224,576460753914036224,576460753914036224,576460753914036224,
  576460753914036224,576460753914036224,590091129354092913,756251640122004913,576354529986416623,
  578141468419526625,576291763065988089,576409436745380744,575358004385591421,573469673203544836,
  856346119208155961,576460753914036224,576460753914036224,576460753914036224,576460753914036224,
  576460753914036224,576460753914036224,593101291302403240,632032844235664309,556589618685541669,
  575093282783666257,577622455607948080,576555361390954349,576737619319474828,576463094685980806,
  742417451678687139,824014658746875044,604662527087087876,898591702073392832,611728198186703417,
  1037816773520796612,627535439845627056,586912435526968648,589385949257635143,585283612359957252,
  575503511359372513,584110716845199727,576957981299365843,577948568211598423,577110924999296768,
  856346119208155961,576460753914036224,576460753914036224,576460753914036224,576460753914036224,
  576460753914036224,576460753914036224,586148863525625008,652858367713557805,574989292826659096,
  576074479588977247,576476927937528932,584559339953240033,576476438134215164,577956469841440036,
  856346119208155961,576460753914036224,576460753914036224,576460753914036224,576460753914036224,
  576460753914036224,576460753914036224,587042289538555508,577024204687307003,557239318376516836,
  572002084078627885,565563497645845136,557519724972205728,569831306670175613,571542444065578856,
  856346119208155961,576460753914036224,576460753914036224,576460753914036224,576460753914036224,
  576460753914036224,576460753914036224,587766423457766485,704225228561607975,596358443182278153,
  571448010687328132,579282551757539363,577465427410250221,582497325563835051,601649013759977930,
  856346119208155961,576460753914036224,576460753914036224,576460753914036224,576460753914036224,
  576460753914036224,576460753914036224,586655318384945307,590986310951232424,676446138917604349,
  631385976147565911,662308473372437435,602388538675507451,638680823160135572,596454335640035229,
  856346119208155961,576460753914036224,576460753914036224,576460753914036224,576460753914036224,
  576460753914036224,576460753914036224,586967790239902473,636346469768781220,610528874980276897,
  642353222174948607,612483288043720527,620909653041436152,577852014086325716,576501773008982113,
  856346119208155961,576460753914036224,576460753914036224,576460753914036224,576460753914036224,
  576460753914036224,576460753914036224,587719486019918317,769123601329842672,564169603522992969,
  275190229135082615,875556357086541116,690429001834903596,560844635423785621,512561951702777608,
  856346119208155961,576460753914036224,576460753914036224,576460753914036224,576460753914036224,
  576460753914036224,576460753914036224]
/-- Probe slice `mpfMP512_r6_p1` (`len = 24`). -/
def mpfMP512_r6_p1 := hmzPrSlice 6 24 [589029508915176005,722470292076595267,576470635554573021,
  364130081140698989,659262675743793788,536272276774593580,576444658670886252,573572177965784286,
  856346119208155961,576460753914036224,576460753914036224,576460753914036224,576460753914036224,
  576460753914036224,576460753914036224,590646281502111339,620215684926489508,545096456793428128,
  428765785938146828,542109446573549668,528558764952599783,596764987597259593,589453149182989991,
  856346119208155961,576460753914036224,576460753914036224,576460753914036224,576460753914036224,
  576460753914036224,576460753914036224,592954667720427267,734812112540521928,609022127325753136,
  416758296483012513,612421534889613063,246934927584631476,578627217074946913,581815838336105684,
  1055078695980420632,585050800175502768,697129041210950604,1131813515800131188,854151627138449339,
  793133409012707441,820703212106884221,590362613907595599,601460512337556135,373227229629306427,
  330079717734153157,574631436199492925,117931440292129240,579512661196524532,582104989490809602,
  888012332221970316,783679626579609672,679013830155663851,696982573174319933,693725153991806903,
  626480225436299759,578525017201922001,586948721787889928,579819547188527105,576460752840294401,
  576460752840294401,576460752840294401,576460752840294401,576460752840294401,576460752853547577,
  826954480222306728,298892589056581376,728441833278403364,877650375503297432,538293315382602843,
  834428339487439572,1006795897573857828,590691243546732808,579819547188527105,576460752840294401,
  576460752840294401,576460752840294401,576460752840294401,576460752840294401,576460752850468534,
  984417410967896892,638329426027003923,971672748202434276,979160755329018068,970074281462650692,
  607756689172602323,1123330150065537168,587385146299738376,579819547188527105,576460752840294401,
  576460752840294401,576460752840294401,576460752840294401,576460752840294401,576460752857952151,
  964427722550724332,546881579523422577,999167638625562248,572291828872511172,335301155450201088,
  661142131959057351,1047497692225666608,587635310899723755,685819386356619100,574908522730144575,
  576308994725772247,547165468357946256,618828139112205615,563442896033999804,572168651371629774,
  856346119208155961,576460753914036224,576460753914036224,576460753914036224,576460753914036224,
  576460753914036224,576460753914036224,583765560533598423,600648557044857168,581382288446857389,
  583527498791022324,577373559474745533,567928486789169735,576286136652206431,576437963759610698,
  697258367026266312,529089471272316327,554871764718581577,580458496582855676,544308283158102336,
  845706574608509223,1048539631701238652,593413927468624136,579819547188527105,576460752840294401,
  576460752840294401,576460752840294401,576460752840294401,576460752840294401,576460752850735119,
  750235407823139516,737270749359269789,766640130862576427,687921208969375896,772775491732752837,
  1046143514639085696,765701096403158949,587671389763889416,579819547188527105,576460752840294401,
  576460752840294401,576460752840294401,576460752840294401,576460752840294401,576460752853494032,
  628182614117364872,575702281961340276,575105715354896616,592548029383153539,543201526806488453,
  709367961850748579,591429049957491896,594279964491797201,615662800595101101,576550522395498311,
  546181568621039933,568428678794084772,574032487141858363,614587542932156621,618466971816293299,
  810640859672348051,826058181637222481,1115307559171764092,1065164501057785736,893978600060724116,
  702578736240263412,918154097000972852]
/-- Probe slice `mpfMP512_r6_p2` (`len = 24`). -/
def mpfMP512_r6_p2 := hmzPrSlice 6 24 [582504342209482443,607213599217194536,574653680846640599,
  570283705122749707,579143436734176143,544733632183387793,606006434380002352,594402318377304285,
  617186642077085901,1127650264402768508,697516231429099461,1113166365559384268,611701191427929671,
  712355892129289764,828997043072965437,586330206768818440,579819547188527105,576460752840294401,
  576460752840294401,576460752840294401,576460752840294401,576460752840294401,576460752849486045,
  856346119208155961,576460753914036224,576460753914036224,576460753914036224,576460753914036224,
  576460753914036224,576460753914036224,586330206768818440,579819547188527105,576460752840294401,
  576460752840294401,576460752840294401,576460752840294401,576460752840294401,576460752841527765,
  655993717057502652,828438074554266887,825446508493813608,860097499332228408,952657929358728716,
  579112920915469319,577260403810117748,589444478831940853,640034287389900175,694869805768836081,
  641533965249491159,200617441800177192,504742986440273660,634619228429874680,668000858637107845,
  856346119208155961,576460753914036224,576460753914036224,576460753914036224,576460753914036224,
  576460753914036224,576460753914036224,593080452078663699,619388792215261564,571131328972675705,
  560933862081595248,572606338820824067,649289332305370944,557351817445700823,563994215142141469,
  856346119208155961,576460753914036224,576460753914036224,576460753914036224,576460753914036224,
  576460753914036224,576460753914036224,591347097060611243,790818898552681089,573693290699126936,
  574573949261676945,583532090547881663,638878696602800943,573324413427361289,562976780337777716,
  856346119208155961,576460753914036224,576460753914036224,576460753914036224,576460753914036224,
  576460753914036224,576460753914036224,582191718913868687,612476038177062391,581209440549557715,
  578605517934916351,583408807603758345,573359047788555423,578316101557298204,581652643534888182,
  1016978633773490424,559147396072456449,576658226846614713,575812835548890389,311903013481380452,
  622383281900326847,713167221105041021,586619405170469128,579819547188527105,576460752840294401,
  576460752840294401,576460752840294401,576460752840294401,576460752840294401,576460752846564488,
  1057349415192240164,1105309796582128476,668437516139402891,977993939299993904,854712847289262744,
  922924280939519312,582353426495559981,587651286100463684,594504102760496640,576795080655870881,
  576979731110371212,581824302754963540,578609459725094913,582106556268284021,580267584228624108,
  856346119208155961,576460753914036224,576460753914036224,576460753914036224,576460753914036224,
  576460753914036224,576460753914036224,582182818864219395,649494889815538335,580811546159911835,
  573211786590573961,535066854679496809,620653621306307795,574993742830496409,556205944788033088,
  1024906930901242616,841397140860017256,807625808705222132,823174295749190883,812173560651977036,
  617971122127566639,1043766404869427976,594479108115385785,576550002356558557,578605406108088913,
  576336989068347029,576082697003574403,583328512930080491,576113612506303361,563268631951814937,
  607320264672684431,732137938116101084,887410048924785836,818898753510212936,642520520623786568,
  620936606995100264,675347020078567428,587416588681570568,579819547188527105,576460752840294401,
  576460752840294401,576460752840294401,576460752840294401,576460752840294401,576460752856436896,
  807698699690258769,716781719563209803,852015122508724172,595593063690142968,627400997706712319,
  637199278398332399,629613643524956504]
/-- Schedule `mpfMidPRow_m512_r6` (`L = 72`). -/
def mpfMidPRow_m512_r6 : GHMidPRowSpec :=
  hmzRowMP3 1186954151 1527996854 mpfMP512_r6_p0 mpfMP512_r6_p1 mpfMP512_r6_p2
/-- Probe slice `mpfMP512_r7_p0` (`len = 24`). -/
def mpfMP512_r7_p0 := hmzPrSlice 7 24 [589404051384864896,625337840900944129,628855102267234155,
  621800459168202401,580050297538966632,577903826424013792,577296030564293359,576529790171811016,
  580469530371288946,856346119208155961,576460753914036224,576460753914036224,576460753914036224,
  576460753914036224,576460753914036224,576460753914036224,576460753914036224,587138675216363609,
  639026829931810735,576447146438717487,575681654382646140,576968981704458515,576536400217874164,
  576245775835136255,576057515555618493,576377924405935630,856346119208155961,576460753914036224,
  576460753914036224,576460753914036224,576460753914036224,576460753914036224,576460753914036224,
  576460753914036224,592255967781712739,677965369044853369,574472440685711268,576648265796156435,
  578591387597555887,588475958212165235,576479603541833861,577316787464385571,579842580030673297,
  835770478168031184,761802013438634589,603024920482400816,1024314843753999008,593890358266300512,
  611536960472897513,955115610577938752,846971906404033623,594808101815918813,698504057030266825,
  554248255796122128,572210813152673268,564692762663130145,575108491112657824,574427403054974867,
  573791555483196357,575275947471819184,644399181200270703,858522211636811243,586650790383560723,
  906359472542031468,946396242843946616,787271913598925856,592309314232555916,1059612418287696876,
  587491998384863735,577243880260418077,444609745589520419,384621507378204737,575173706042804873,
  500543065647759627,548808400518282112,564860674452676996,539676416323404656,856346119208155961,
  576460753914036224,576460753914036224,576460753914036224,576460753914036224,576460753914036224,
  576460753914036224,576460753914036224,586522851983146492,612152881450303020,571446229288868445,
  576794923124002683,590549323978159251,586667257593798749,577136785479378365,579603702849237067,
  578483729690721716,856346119208155961,576460753914036224,576460753914036224,576460753914036224,
  576460753914036224,576460753914036224,576460753914036224,576460753914036224,586627099402515612,
  600398378434976084,481567757415226595,479548960791289001,502242300668874328,568646344623674903,
  532305723328515721,527772239469023533,499238722631399668,856346119208155961,576460753914036224,
  576460753914036224,576460753914036224,576460753914036224,576460753914036224,576460753914036224,
  576460753914036224,587087658712217993,733684181139649197,576899496663378941,577915677361878001,
  575376780609680157,579108192404682683,572027706721616087,578102847766044581,578030627821388917,
  856346119208155961,576460753914036224,576460753914036224,576460753914036224,576460753914036224,
  576460753914036224,576460753914036224,576460753914036224,587128229879978928,664336867149856769,
  617830840150245853,533739765937785643,541597038932903639,598398896286892503,617510375290429945,
  584427753986575919,578754420005115918,856346119208155961,576460753914036224,576460753914036224,
  576460753914036224,576460753914036224,576460753914036224,576460753914036224,576460753914036224,
  586551159330781109,742533691004940379,597106089602972223,568382048218754692,575770471142659493,
  579372015077703541,566690763225744236,577675416196961199,581518875704648879,856346119208155961,
  576460753914036224,576460753914036224,576460753914036224,576460753914036224,576460753914036224,
  576460753914036224,576460753914036224,585749882465308433,633276513420695337,472139665250489497,
  799497099180122993,735420215500700556,572605767717679251,532007003845737481,571442899631182952,
  572134190699774376,856346119208155961,576460753914036224,576460753914036224,576460753914036224,
  576460753914036224,576460753914036224,576460753914036224,576460753914036224,586297176066810477,
  578568821528958700,858408127637617139,782633291906531987,738114049127333564,629311705183181253,
  578374070878181677,484763927072740680,530115228563392691,856346119208155961,576460753914036224,
  576460753914036224,576460753914036224,576460753914036224,576460753914036224,576460753914036224,
  576460753914036224]
/-- Probe slice `mpfMP512_r7_p1` (`len = 24`). -/
def mpfMP512_r7_p1 := hmzPrSlice 7 24 [587341756190759532,604669382100703875,599693686953780589,
  612654214716356664,652307325182954500,603960463648822707,395853465446247201,518433141934593705,
  569912946358657244,856346119208155961,576460753914036224,576460753914036224,576460753914036224,
  576460753914036224,576460753914036224,576460753914036224,576460753914036224,587572021242925039,
  627756320363633860,621915142536326213,576529596893209693,518205298419858555,410175239938970013,
  80085734749879107,603984410825693536,579302001492223631,856346119208155961,576460753914036224,
  576460753914036224,576460753914036224,576460753914036224,576460753914036224,576460753914036224,
  576460753914036224,588201709834106973,733799814553860816,596401617280290973,660871390081805229,
  575848956420899984,671643721105045549,514803340695709393,526182465576495685,560006024470649178,
  856346119208155961,576460753914036224,576460753914036224,576460753914036224,576460753914036224,
  576460753914036224,576460753914036224,576460753914036224,588649231177811717,590872940872892008,
  403862072623031125,827709472197220951,332046886225498949,494867760268680336,365008518823857467,
  581364965734724057,693198350503982445,856346119208155961,576460753914036224,576460753914036224,
  576460753914036224,576460753914036224,576460753914036224,576460753914036224,576460753914036224,
  589389912499449325,719199992375899299,609126826481519140,754224429542875996,577592044011376428,
  590531861472823712,558978502104121943,674344878604096313,585023800950372200,810111493151483336,
  636790887135964497,581996962463440332,781266651674283492,691979473146681513,596387871011781672,
  636292044936319536,934240007920648824,585013108774534505,664215928359126079,576012005620208017,
  573963401167088203,586721769205146044,468476361945102301,383238450610545369,580972332760688891,
  652441047894691552,851561053219197359,617866062933667061,759700692093756333,601997447265938459,
  693732222454745664,1011982976881871976,635049764302666356,768266255966310588,588110869071227144,
  579819547188527105,576460752840294401,576460752840294401,576460752840294401,576460752840294401,
  576460752840294401,576460752840294401,576460752853927364,582259521333170283,230503873852495716,
  632164451477684343,608239966416334076,823939833533217488,578488620555979736,582594508381311632,
  611292293381301209,591099036732844296,579819547188527105,576460752840294401,576460752840294401,
  576460752840294401,576460752840294401,576460752840294401,576460752840294401,576460752852672271,
  990061728162914172,887246795050401192,1110851519870698088,963502773319417884,1085813361441418448,
  698032066686886956,1139855462046028244,653882392752850904,592432642075221364,576683125967198809,
  842780516588995345,594784689665573011,569916807472184864,501650068831520345,163743687581842604,
  755400243618940781,804987024836451503,768763764655387191,701655288197888424,671487186656493696,
  805289802842497491,796420638464663544,620187204992036663,810816144787009652,862049643577264964,
  593858305166006344,584963215123924491,576550152633769624,574127364776084188,576339749684292288,
  576044002521216409,574912683675198823,580421013800342049,587395095341664950,589257710982857751,
  383258122495672356,344141337649363379,731612047623720768,711998965144899524,576200134216013201,
  595239908948414963,828176209548986072,588109724462442760,579819547188527105,576460752840294401,
  576460752840294401,576460752840294401,576460752840294401,576460752840294401,576460752840294401,
  576460752843464852,1124197701317502128,814969150525007472,589693044567326883,586819531058714309,
  863245409716398648,618423939457150296,595617403270028604,605091736052455584,578251576025226153,
  580437016429732615,577561123508752845,574660074926721805,577379579546814071,584929732996049303,
  542978940223227095,571276014350269613,576410222560311317,1016528583626767128,948559547008759344,
  841862988039383508,668210917958316071,657970754931415968,693945292549616699,704215843547334329,
  735054889847181429]
/-- Probe slice `mpfMP512_r7_p2` (`len = 24`). -/
def mpfMP512_r7_p2 := hmzPrSlice 7 24 [587471285090085128,579819547188527105,576460752840294401,
  576460752840294401,576460752840294401,576460752840294401,576460752840294401,576460752840294401,
  576460752848815714,636743024024637071,619204108456876443,1080533719385922548,605881626708386219,
  715617702905674656,618664175231576961,589477196692176267,880471441219734264,588986858604922948,
  610402843215579481,202664852736238085,635149561213886244,620111221560048449,497796236308268008,
  529562389211168200,657266492224777655,658855963804172725,856346119208155961,576460753914036224,
  576460753914036224,576460753914036224,576460753914036224,576460753914036224,576460753914036224,
  576460753914036224,578283378256049453,610782494149723125,588083703156999545,576132703349413135,
  561919016180523923,586497047761737616,583965152914927156,546137763033820960,565770741390222417,
  1037979112735277652,714558615500327144,587175919928488284,963159139422329904,1144663772350478756,
  797214771522627704,716105214957955569,783114095337183716,592198150002403592,579819547188527105,
  576460752840294401,576460752840294401,576460752840294401,576460752840294401,576460752840294401,
  576460752840294401,576460752848367691,661205058611778212,675526373622990296,671556405425144817,
  712473725623329113,709336638589616793,594325408388563692,580422599251506644,619835365568667477,
  588693621976808825,599490049707729760,700542709118072172,568221402471383533,576860111279688977,
  519696746594028609,579036058479036643,730009866828864207,670837702789027563,856346119208155961,
  576460753914036224,576460753914036224,576460753914036224,576460753914036224,576460753914036224,
  576460753914036224,576460753914036224,584946387602174675,651494600672299739,586274396658701047,
  576123460583091360,566199544728640191,599816098145769647,532412882562379743,579145811988689279,
  586541693927874486,582732902962651908,1149932157456107712,910369593321906944,988725737558654904,
  773390904658015001,746864099996377829,793079291353022568,686572685905839776,585951658015025416,
  579819547188527105,576460752840294401,576460752840294401,576460752840294401,576460752840294401,
  576460752840294401,576460752840294401,576460752841235072,582115829980757604,823417370518328216,
  858684084647125409,737907893800351464,589802746622087981,602779539349799049,1048770436859219304,
  637315370281235976,578524413781396971,576572392358023869,606767266362797427,572134170555757153,
  534480411309566031,543388473882739040,583263756720247944,550955743464582901,575683634351970312,
  1089100010209598528,899341463762099328,599250314243043336,718110556655288469,827619922940022788,
  810839582551473248,680061646463379884,602582190952429188,586459720433887496,579819547188527105,
  576460752840294401,576460752840294401,576460752840294401,576460752840294401,576460752840294401,
  576460752840294401,576460752849606664,856346119208155961,576460753914036224,576460753914036224,
  576460753914036224,576460753914036224,576460753914036224,576460753914036224,576460753914036224,
  586459720433887496,579819547188527105,576460752840294401,576460752840294401,576460752840294401,
  576460752840294401,576460752840294401,576460752840294401,576460752846013353,702577798909539363,
  871977277945677204,779561320945770489,617822762147380116,694480605429068768,701551696818018101,
  656112429959085948,853487904392284191,585656579791980431,580768802811282143,576982952386245893,
  570243594461319580,576879371747391623,518882361365469357,588380081881715011,597694749115045032,
  584277523534360121,856346119208155961,576460753914036224,576460753914036224,576460753914036224,
  576460753914036224,576460753914036224,576460753914036224,576460753914036224,585656579803146504,
  579819547188527105,576460752840294401,576460752840294401,576460752840294401,576460752840294401,
  576460752840294401,576460752840294401,576460752848858681,856346119208155961,576460753914036224,
  576460753914036224,576460753914036224,576460753914036224,576460753914036224,576460753914036224,
  576460753914036224]
/-- Schedule `mpfMidPRow_m512_r7` (`L = 72`). -/
def mpfMidPRow_m512_r7 : GHMidPRowSpec :=
  hmzRowMP3 1212462803 1524616190 mpfMP512_r7_p0 mpfMP512_r7_p1 mpfMP512_r7_p2
/-- Probe slice `mpfMP512_r8_p0` (`len = 24`). -/
def mpfMP512_r8_p0 := hmzPrSlice 8 24 [586421652174953635,720686643738138816,576067315715250612,
  568212763256540652,575248847762854015,577538093856729021,576555066083786979,576961773714633740,
  577188487100267765,581335467716461996,602390925329144708,891644321884271316,1032423033338189268,
  757217475149192247,687307412003956307,969691600005289212,581766876770616696,690550914397992408,
  1126973882206014152,585411723540225188,603805095014377552,578241917857533644,583981450213276048,
  569020479010436501,576155316424796368,574093511990833003,575874580527639121,569743716487528523,
  571908976573527446,661905536605252311,768198307439278496,846394572605946171,601366039829131311,
  1009572821627447624,793297214775593093,576715616199638351,659177026556772348,598261992876209772,
  585037135147392141,737401746060199765,572265372983373977,576265211763612067,579364954252084741,
  576705501609828025,576591783893829547,576134056310224699,577403433753978464,576516637888960176,
  742033585722811652,601065925768079976,758202314371394876,591120572511929924,838175723188144971,
  662060043754998113,666022646081077028,764460138629937033,854232212538088664,584665360569377209,
  718400265531740899,593586698818568675,580065489076656628,578691880192349893,579458043378977985,
  577940841813767581,580066871841892213,576537379736451791,577850595674953975,845359984788832532,
  1127314286280377244,699896150127052683,776460517773468207,734786545663538928,822778530646549244,
  764855699749655652,836613299985823181,1142200101762242412,584417913618182247,749496490010575125,
  579021966926461883,539289120928920615,574495453158812736,576993130273799975,579730477207292933,
  578615559663051307,582880401890443647,578570397833891843,618679438474361088,1042390076177967632,
  960336364517450216,807287537092320812,616565697161574119,681882627791476853,932595686148690968,
  1006945682473841148,1018415918772309888,584319675483046956,602024489614478652,526241412904847413,
  575475011032376393,568612473322650032,569942769578001855,573550191133307540,564192570912209696,
  561417278909557024,567727564990192642,775996970551012929,990803453766598824,627654134488521833,
  1048763627256099576,774599641588212579,641151931431257828,676184318585932337,1152897868864992516,
  585666946519781241,584578996370688347,750186669534916297,576362750480120137,580628125432787517,
  583879565823540792,576537107762757600,576623078016316280,576381741965231923,574750372753509303,
  574785483674233618,724060517682336408,614858188889510216,599290325084622257,580394861279049069,
  789537483083258136,704463727587785219,576460753914036224,1130090396374430928,1125176122711320284,
  584226902244621179,673686936845745811,576416708039420732,580023348129349723,575143095595990835,
  576866262236956416,577713173139742667,582412954886834372,578925425515536833,582488541878955109,
  800384297369426453,957863947266873732,631383779935418592,697493666754766308,615451061880227292,
  757281587200051908,1145557271539553532,737037099936318384,612059829791350833,589968686274416141,
  708300379161173715,576692582562562297,572064605240729311,569251564361189576,575936233369798897,
  573978785774462852,575776381184911663,572664491536793328,573791713066612622,644983223742937269,
  1068919921641832644,678559992743223312,991804131654542568,764252764698517091,580668649337464796,
  662131341274021776,951234736059510624,951481277920267344,583542085629468460,580275050481953283,
  576410995667365088,576424186997450767,576774268476871372,576742591819419647,576456492636143989,
  576547017551323547,576571008945750017,576460752855309294,817909356364047912,934918939200011424,
  801531770882724689,1135662961823444424,607514091166611132,807692129456256024,1066030125933861176,
  613329933225272531,928150906100108996,588862862833264304,580158271950291093,576368432524916820,
  576355023064587947,575444353582075615,567963632836405499,577218449622715696,575725204495667077,
  573477189424812900,575905210632820001,673895473606252148,645588052828284272,886818692058412548,
  965381623957075404,585827561116865889,857244331083249812,584513730620882639,846917919737327768,
  618918244022591309,583242212221765204,661852239462927896,478079277663962928,554284094140639489,
  538347814464215757,554945590992331896,571393154526662723,555747392769823663,562777657283437268,
  558380996746052055,870429146253591224,576460753914036224,606930244049284292,596680784559966243,
  810813087841975251,587628321718691016,1061823557650994472,689976820077618581,696179964034288893]
/-- Probe slice `mpfMP512_r8_p1` (`len = 24`). -/
def mpfMP512_r8_p1 := hmzPrSlice 8 24 [592073974921767933,653257151805434208,576405847152584768,
  577937121005446140,576472165653246956,576678356526299701,580400410455836632,577257262308640804,
  589294677132836087,599528884760037330,581246269827554859,952202076740964984,604078364312577992,
  763896521979936596,583991287577509092,659823223705179824,1008942384820204244,770854825275531147,
  955399926737924144,583799111908945471,762744531114718713,593120544049599731,597109388080247512,
  452120778532504251,576443766716530041,413598255866350188,575592820659744705,638306813080129348,
  595844218350724035,719271880401151212,576460753914036224,600463159320369936,685019230596074384,
  632430403336748216,766174298717761437,874136570616694376,788501902045649156,773973989409308241,
  591651661327062132,577538666239508413,576985207423576177,568345824547735821,576924553609432952,
  575983067911091244,515088879748812943,612465489475647152,576292597530499335,574722691250134035,
  834157935991139499,669582515591858399,410105857938980244,581492683912059144,576447768080422644,
  508343950470752579,456028894002062804,777508338210494108,786968336530834872,586676751494180563,
  584581887456968705,576460753330119799,576223112462112852,576364024838958920,577043012414491389,
  629388309498911551,563784629442533845,571122422102260620,573114721000269968,901958973739048344,
  650638437067287033,595186884390408716,560752183821718232,220600358321828484,1141991686408428572,
  822350562525477924,597625659107912772,831347549779096797,589118844160692312,636899903070535681,
  576460753129702519,576278087940994793,576527178819970163,576655061566460897,587953613095461740,
  563848722040559909,576300924268583788,575293409728970888,888032175059645436,384261103753650257,
  612285724779371252,699773736462183092,691561811951999448,724896500657334228,576742503753069984,
  759004722748123161,731105074749112227,584748159710756221,580943655020265473,576460752933332840,
  576446106042214144,576541868667018907,576455637755356435,578791868095616957,572215998453679407,
  578957159967737225,578666184195193314,627947545198916253,697408503998348604,856190078737534787,
  1060738904492539392,580709140142462276,616072023969435744,610324955053277807,800900343059180744,
  702587836201528961,586413411946438899,580232820752908289,576460752840294401,576460752957538300,
  576674501777154748,572012063308248421,576535721998660511,552971534231495999,588964648209020485,
  577418174076829557,748217100655512363,816019613201672,560685101758469531,783241549748811383,
  702954905339663981,639204380721802692,719920793979687728,606100610992779716,789102736874117519,
  588776107803964444,612511887090480364,578681780692947205,576720345388000459,584515281224461041,
  576083861279499643,640456053347211760,574140885396337703,571920697643290408,570411694067917345,
  975928676485364688,535373687024714007,858430070350856184,419635089863819361,590869578872154512,
  744750649590067971,575346341944579733,768263236600557936,614922987059835924,584955152807170377,
  607336310658564097,576460752840294401,576460753196295703,576015047126782088,574081539641817756,
  581708383854001800,559763869020143516,573008762002609731,576298982903841437,1090222083477511028,
  777417291535096304,855079918833547296,577888902480666587,1061284311680074788,605773620105025248,
  696918688705363692,1011777263007165908,994483972333312844,592658917220320531,589107073589968897,
  576460752840294401,576460753026671279,576020991549363145,574546305779986796,598493586597268287,
  554630490642161173,576370262238276412,575210029379644197,652993951938150257,320899766237517603,
  208953811486504176,610258392727277792,590561174478038744,580706302240810281,688556451568646088,
  682929686103212024,696085753978392159,582691509475382061,585647159605460993,576460752840294401,
  576460752870742699,576401503915962924,574251134977095767,576508547348398468,575641038020211859,
  576602929314873608,577516800490519859,744896429511757467,611761003145223279,884468022077969588,
  595238706339597323,606208216021787429,852504047614220273,963680535509674932,577408566223318311,
  900321605423349516,579842135724879872,598825636930822459,583261133475200332,576409405478506501,
  575499655296602868,542705792571082707,596635017415273252,577867847924666967,601771253074736756,
  591604810755787692,577915779312739596,591524324133772389,861291698064814416,483453962052843867,
  328407321902260791,770946118878901763,578177339595664257,636579686437181009,691499049945341028]
/-- Probe slice `mpfMP512_r8_p2` (`len = 24`). -/
def mpfMP512_r8_p2 := hmzPrSlice 8 24 [584164346934077099,578535578526547969,576460753019485780,
  576440425859492808,576376125918420729,574504824845771068,571363619988233907,583737582825219621,
  577026180995227375,576575342585000002,826287102398633216,617810898317774883,882006683628995088,
  725297282591592411,519150126402231321,790613399865638868,975980627895015416,790473519745253144,
  1030840318728440924,576471226270903159,643927155168087359,480546161692690504,599845078910379047,
  1042647524146866556,506008148531298076,369525780930741723,371248199106414285,702845555788182660,
  658693505589379862,608504349563704788,1093914389357643276,644129762177634731,577674009160699436,
  1053240271638522176,887756873937270552,804865722068271993,846030359406668219,977490633590786564,
  586584236687273516,577951996623978497,576460753377143299,576410995898157533,575570917325859973,
  577120653090488321,576460752876902404,575734900205831200,576942148921839947,576831490127712914,
  915371815052216916,576460753914036224,576460753914036224,1135415586736340288,676229304075490143,
  592893860355899019,858896410659726849,692949166150460096,620413171813724199,581012760212772308,
  583956856972509185,576460752840294401,576460753286263699,575326989344961373,590148990143848131,
  595915292543817121,576479934554100039,561660183886475940,575847187771031553,751766205015134748,
  948590545700113484,524320214911365429,681561592765681128,863757983833338732,529713990699322692,
  72942908787078968,673308969998395164,929095523841679188,588110172073855119,594677900066359239,
  559576076787552147,577305096613514179,583683784282834564,649839810652483772,597901207258763897,
  523925529096888163,530328041165051837,519446457858602124,816758147225225267,576460753914036224,
  576460753914036224,1064384384657187956,1091217549333742368,593501086053414624,606323368392464057,
  946079287137878628,772393257825096308,586402022761806511,579482829268713473,576460752840294401,
  576460753210895385,576295388010345513,576468818798081443,576454237776845053,583091207723534837,
  571974552129959755,576410531798590426,651498942542039271,1152029368524634052,580296373383925721,
  686423639806064816,692449544423393891,725380103430426776,593121974656156853,577085504151907148,
  577351354037607572,587689932092269501,589090254903529133,580179726419221376,575485914463607231,
  577050821506360643,567075085542966524,585666004856994276,575410739755623060,579787219340142289,
  587539045463671572,585226140067955876,576460753914036224,1152897868864899836,600891492113832636,
  803373213413871632,1148722501386004868,638263963209849588,778609140660881844,576460753914036224,
  590085525291740575,648291134749118549,857826478418482292,678596291417020247,91762148614794272,
  576998386895972643,229132481042019267,173497390721596680,791162353034057577,697701237168235621,
  632746278854872764,576460753914036224,1152897868864899836,717206398412213532,652017228024630564,
  923500414305160184,580729206229542044,794024185232625537,1098839913677505488,582004471152148129,
  577799365598885215,554711305051890945,578125937488057235,577614961390747907,518776769385995137,
  574475318514651568,625676466433713325,577199586525282265,579021438119755190,576460930007695412,
  577061463072450792,577686338938102871,589689306872758284,584071842909911381,645171537623431032,
  657269639111594811,585058258386138804,723642608772618792,584733759901279179,580664284577529857,
  576460752840294401,576460752989092900,576479276164214672,574878589106938140,573557386110200349,
  577147737156500891,576451102301844023,575538374261026970,577814552302148433,797352674293858248,
  690392775850564272,787008629965471224,1028869948560178232,780138694365961472,576558616891396808,
  793323044719325667,988027225583185332,584117777782881440,591195249537168187,565920323475673081,
  580351649823410989,568175052465047140,574334678542321764,566367145247583143,714584736430281220,
  578699722667113729,600200566098975648,823000066202374227,901396788167299032,863126668896546056,
  843415475914009799,778772186198385668,1095696424772191368,580852146447431949,982256161813421552,
  743309508852442796,587416302964909384,589062177611613597,587721422672296685,576282361795767103,
  561943136604081985,571637547580015127,564561056675576137,571928188419262045,618488094912077233,
  617481607538506598,582056761293366456,576460753914036224,576460753914036224,576460753914036224,
  776046057724679939,826479324646026531,1127391599981054792,1133674495051353104,1004218011027606224]
/-- Schedule `mpfMidPRow_m512_r8` (`L = 72`). -/
def mpfMidPRow_m512_r8 : GHMidPRowSpec :=
  hmzRowMP3 1235874657 1522033601 mpfMP512_r8_p0 mpfMP512_r8_p1 mpfMP512_r8_p2
abbrev mpfMidPRows512 : List GHMidPRowSpec := [mpfMidPRow_m512_r3, mpfMidPRow_m512_r4,
  mpfMidPRow_m512_r5, mpfMidPRow_m512_r6, mpfMidPRow_m512_r7, mpfMidPRow_m512_r8]
abbrev mpfMidPVSeq_512 := hmzRep 13
  [0,818310000,870037186,896807881,915469722,930640992,944098466,956696945,968953235] ++ [
  [0,818310000,870037186,896807881,915469722,930640992,944098466,956696945,968953236],
  [0,818310000,870037189,896807904,915469804,930641174,944098788,956697436,968953948],
  [0,818310000,870061967,897019549,916039862,931761548,945952293,959477148,972864741],
  [0,818310000,1115040245,1211365880,1265142884,1304774362,1335135512,1365636662,1396277812]]
private def _mpfSt_512_r3_s0 : MidPProbeState :=
  ⟨hmzP 208257453817115, hmzP 478120630401918,
  [hmzC (hmzP 4534119813019) (hmzP 4534127316552)
      (hmzN 97588103231) (hmzN 97580913333),
   hmzC (hmzP 6109994937047) (hmzP 6110015965314)
      (hmzN 2018349579094) (hmzN 2018328548007),
   hmzC (hmzP 5378186565902) (hmzP 5378202104921)
      (hmzP 125369262558730) (hmzP 125369278116725),
   hmzC (hmzP 10136426189454) (hmzP 10136434460438)
      (hmzP 243098161446057) (hmzP 243098169743841)],
  [hmzC (hmzN 67976569328738) (hmzN 67976561224205)
      (hmzN 8431114671085) (hmzN 8431107101556),
   hmzC (hmzN 230970621460966) (hmzN 230970593034490)
      (hmzN 333797896427487) (hmzN 333797867996653)],
  [hmzC (hmzP 119211636833400) (hmzP 119211661594476)
      (hmzP 88133459131671) (hmzP 88133483899902),
   hmzC (hmzP 20839891463641) (hmzP 20839913663706)
      (hmzP 898958512739887) (hmzP 898958534977311)],
  [hmzC (hmzN 824139926746115) (hmzN 824139918750767)
      (hmzP 70262379624363) (hmzP 70262386333336)],
  [hmzC (hmzP 405150444536665) (hmzP 405150474289655)
      (hmzP 389499266443187) (hmzP 389499296234702)],
  [],
  [],
  [],
  [], []⟩
private theorem _mpf_512_r3_k0 :
    uCheckOptStateS1 (uInitProbesS1 512 3 mpfMidPRow_m512_r3 mpfMP512_r3_p0)
      _mpfSt_512_r3_s0 = true := by
  decide +kernel
private theorem _mpf_512_r3_k1 :
    uCheckProbeTailS1 512 16 3 mpfMidPVSeq_512 mpfMidPRow_m512_r3
      mpfMP512_r3_p1 _mpfSt_512_r3_s0 = true := by
  decide +kernel
private lemma _mpf_512_r3_ok :
    checkGHMidPRowsSlice false 512 16 mpfMidPVSeq_512
      3 [mpfMidPRow_m512_r3] = true :=
  checkGHMidPRowsSlice_of_probes2_s1 (uInitProbes_sound_s1 _mpf_512_r3_k0)
    (uCheckProbeTail_sound_s1 _mpf_512_r3_k1) rfl
private def _mpfSt_512_r4_s0 : MidPProbeState :=
  ⟨hmzP 184325916998480, hmzP 394404227608743,
  [hmzC (hmzN 1358265585309) (hmzN 1358238895590)
      (hmzP 287019118820) (hmzP 287045712853),
   hmzC (hmzP 2273214607680) (hmzP 2273320801095)
      (hmzP 348017429902) (hmzP 348123623901),
   hmzC (hmzP 4447790236023) (hmzP 4447894714822)
      (hmzP 190765584916) (hmzP 190870064172),
   hmzC (hmzP 64975426453552) (hmzP 64975494318891)
      (hmzN 96805882385367) (hmzN 96805814523009),
   hmzC (hmzP 142095915971055) (hmzP 142095951401729)
      (hmzN 213046948667294) (hmzN 213046913240488)],
  [hmzC (hmzP 812833738355) (hmzP 812866093074)
      (hmzN 975662631184) (hmzN 975630455368),
   hmzC (hmzN 97223671672598) (hmzN 97223519045474)
      (hmzN 359851486151) (hmzN 359698863173),
   hmzC (hmzN 384316355063365) (hmzN 384316192733457)
      (hmzP 2394753736460) (hmzP 2394916060864)],
  [hmzC (hmzP 34064869794413) (hmzP 34065004421790)
      (hmzN 3068276866816) (hmzN 3068142240907),
   hmzC (hmzP 152799583332731) (hmzP 152799737247428)
      (hmzP 4431270735482) (hmzP 4431424647491),
   hmzC (hmzP 488491152711391) (hmzP 488491264315067)
      (hmzN 739500088995590) (hmzN 739499977395939)],
  [hmzC (hmzN 72857357282043) (hmzN 72857313843268)
      (hmzN 25371636911530) (hmzN 25371594176823),
   hmzC (hmzN 670642621282057) (hmzN 670642341606951)
      (hmzN 9734767848286) (hmzN 9734488180449)],
  [hmzC (hmzP 142414419272834) (hmzP 142414614050703)
      (hmzN 23377616321292) (hmzN 23377421541790),
   hmzC (hmzP 723435614677347) (hmzP 723435884430074)
      (hmzP 2073937977682) (hmzP 2074207717695)],
  [hmzC (hmzP 254564974039596) (hmzP 254565005722554)
      (hmzN 52671392120457) (hmzN 52671360666912)],
  [hmzC (hmzN 249985973916602) (hmzN 249985811663857)
      (hmzN 14236137251031) (hmzN 14235975004744)],
  [hmzC (hmzP 898317226319966) (hmzP 898317414666567)
      (hmzN 7560494384791) (hmzN 7560306050897)],
  [], []⟩
private theorem _mpf_512_r4_k0 :
    uCheckOptStateS1 (uInitProbesS1 512 4 mpfMidPRow_m512_r4 mpfMP512_r4_p0)
      _mpfSt_512_r4_s0 = true := by
  decide +kernel
private theorem _mpf_512_r4_k1 :
    uCheckProbeTailS1 512 16 4 mpfMidPVSeq_512 mpfMidPRow_m512_r4
      mpfMP512_r4_p1 _mpfSt_512_r4_s0 = true := by
  decide +kernel
private lemma _mpf_512_r4_ok :
    checkGHMidPRowsSlice false 512 16 mpfMidPVSeq_512
      4 [mpfMidPRow_m512_r4] = true :=
  checkGHMidPRowsSlice_of_probes2_s1 (uInitProbes_sound_s1 _mpf_512_r4_k0)
    (uCheckProbeTail_sound_s1 _mpf_512_r4_k1) rfl
private def _mpfSt_512_r5_s0 : MidPProbeState :=
  ⟨hmzP 159583812407456, hmzP 315599139457949,
  [hmzC (hmzP 254266973820) (hmzP 254268912564)
      (hmzP 230391518552) (hmzP 230393315686),
   hmzC (hmzP 152770395170) (hmzP 152775188667)
      (hmzN 590493888149) (hmzN 590489103958),
   hmzC (hmzN 2287996902339) (hmzN 2287987949241)
      (hmzP 670817003824) (hmzP 670825956040),
   hmzC (hmzN 4105166753378) (hmzN 4105156441642)
      (hmzP 659392169197) (hmzP 659402476021),
   hmzC (hmzP 63544898072515) (hmzP 63544904437171)
      (hmzP 98741772007107) (hmzP 98741778242404),
   hmzC (hmzP 162622604060155) (hmzP 162622607689738)
      (hmzP 250424140716107) (hmzP 250424144215400)],
  [hmzC (hmzN 1598278405905) (hmzN 1598275617228)
      (hmzN 24605359188) (hmzN 24602826890),
   hmzC (hmzP 6222112231168) (hmzP 6222119685490)
      (hmzN 2762713840308) (hmzN 2762706402432),
   hmzC (hmzP 59082623511666) (hmzP 59082638568534)
      (hmzN 26072108211708) (hmzN 26072093157396),
   hmzC (hmzP 331554921577022) (hmzP 331554940185571)
      (hmzN 270180640311202) (hmzN 270180621708808)],
  [hmzC (hmzN 1800242996330) (hmzN 1800236351407)
      (hmzN 129948944812) (hmzN 129942322689),
   hmzC (hmzN 7079557532855) (hmzN 7079543790062)
      (hmzP 8189329183224) (hmzP 8189342923822),
   hmzC (hmzN 104512561399329) (hmzN 104512544102388)
      (hmzP 63624234932552) (hmzP 63624252225014),
   hmzC (hmzP 481145781508600) (hmzP 481145793078747)
      (hmzP 726396432752482) (hmzP 726396444111604)],
  [hmzC (hmzN 18149541064790) (hmzN 18149535721953)
      (hmzN 1670647954699) (hmzN 1670643431403),
   hmzC (hmzP 76810739268137) (hmzP 76810754981650)
      (hmzN 62742708960050) (hmzN 62742693298984),
   hmzC (hmzP 756021749420458) (hmzP 756021783644254)
      (hmzN 221798076367349) (hmzN 221798042151537)],
  [hmzC (hmzN 9520489066165) (hmzN 9520477958899)
      (hmzP 2442937945320) (hmzP 2442948965254),
   hmzC (hmzN 65461190361671) (hmzN 65461164514921)
      (hmzP 43140958288772) (hmzP 43140984129660),
   hmzC (hmzN 484614444173879) (hmzN 484614409291606)
      (hmzP 334650649361973) (hmzP 334650684236409)],
  [hmzC (hmzP 25933543023509) (hmzP 25933546584266)
      (hmzP 707440331965) (hmzP 707443504994),
   hmzC (hmzN 125940720438839) (hmzN 125940710303817)
      (hmzP 165710642378397) (hmzP 165710652491635)],
  [hmzC (hmzP 38904263730559) (hmzP 38904273102154)
      (hmzN 35866396921184) (hmzN 35866387583944),
   hmzC (hmzP 383612356048590) (hmzP 383612376669163)
      (hmzN 105877920790408) (hmzN 105877900173536)],
  [hmzC (hmzN 88327996163843) (hmzN 88327976811475)
      (hmzP 54971890430598) (hmzP 54971909779327),
   hmzC (hmzN 642238350583430) (hmzN 642238324829112)
      (hmzP 458666535943821) (hmzP 458666561691673)],
  [], []⟩
private theorem _mpf_512_r5_k0 :
    uCheckOptStateS1 (uInitProbesS1 512 5 mpfMidPRow_m512_r5 mpfMP512_r5_p0)
      _mpfSt_512_r5_s0 = true := by
  decide +kernel
private theorem _mpf_512_r5_k1 :
    uCheckProbeTailS1 512 16 5 mpfMidPVSeq_512 mpfMidPRow_m512_r5
      mpfMP512_r5_p1 _mpfSt_512_r5_s0 = true := by
  decide +kernel
private lemma _mpf_512_r5_ok :
    checkGHMidPRowsSlice false 512 16 mpfMidPVSeq_512
      5 [mpfMidPRow_m512_r5] = true :=
  checkGHMidPRowsSlice_of_probes2_s1 (uInitProbes_sound_s1 _mpf_512_r5_k0)
    (uCheckProbeTail_sound_s1 _mpf_512_r5_k1) rfl
private def _mpfSt_512_r6_s0 : MidPProbeState :=
  ⟨hmzP 119775896884444, hmzP 175455440847936,
  [hmzC (hmzN 10225922109) (hmzN 10225800136)
      (hmzP 173734037091) (hmzP 173734095145),
   hmzC (hmzP 100416130987) (hmzP 100416355045)
      (hmzP 119955558697) (hmzP 119955752491),
   hmzC (hmzN 221510794296) (hmzN 221510463844)
      (hmzN 220186224380) (hmzN 220185864512),
   hmzC (hmzP 1381828025605) (hmzP 1381828540351)
      (hmzP 3444915449168) (hmzP 3444915986070),
   hmzC (hmzN 2853715997150) (hmzN 2853715133922)
      (hmzP 4858843360289) (hmzP 4858844053650),
   hmzC (hmzP 171695958954629) (hmzP 171695960146036)
      (hmzN 2136234994991) (hmzN 2136234329890),
   hmzC (hmzP 476764240239480) (hmzP 476764241464838)
      (hmzN 6276772803888) (hmzN 6276772174294)],
  [hmzC (hmzN 144132186922) (hmzN 144131955400)
      (hmzP 93502456905) (hmzP 93502562671),
   hmzC (hmzN 267250264084) (hmzN 267249823490)
      (hmzN 1148441456918) (hmzN 1148441076433),
   hmzC (hmzN 5437192993943) (hmzN 5437192324971)
      (hmzP 5763325460587) (hmzP 5763326190834),
   hmzC (hmzN 17662968164652) (hmzN 17662967074175)
      (hmzN 47950380481229) (hmzN 47950379336864),
   hmzC (hmzN 353753732100051) (hmzN 353753730167810)
      (hmzN 292634255741089) (hmzN 292634254183786)],
  [hmzC (hmzP 53805173208) (hmzP 53805594237)
      (hmzP 362537240805) (hmzP 362537602847),
   hmzC (hmzP 1282184098723) (hmzP 1282184724032)
      (hmzN 1930038532062) (hmzN 1930037851372),
   hmzC (hmzP 2135986184272) (hmzP 2135987173052)
      (hmzP 10491167861995) (hmzP 10491168901669),
   hmzC (hmzP 64952539841114) (hmzP 64952541547638)
      (hmzP 74805553412664) (hmzP 74805554797916),
   hmzC (hmzP 859175778488850) (hmzP 859175781000285)
      (hmzN 15656970869637) (hmzN 15656969467161)],
  [hmzC (hmzN 1749596148632) (hmzN 1749595424408)
      (hmzP 384717551415) (hmzP 384717841423),
   hmzC (hmzN 5963513362389) (hmzN 5963511944073)
      (hmzN 12867170410270) (hmzN 12867169186216),
   hmzC (hmzN 78381230816392) (hmzN 78381228701715)
      (hmzP 69014303264441) (hmzP 69014305578938),
   hmzC (hmzN 326775025159336) (hmzN 326775021773568)
      (hmzN 726622557451685) (hmzN 726622553853684)],
  [hmzC (hmzP 651154694397) (hmzP 651155640836)
      (hmzP 1259489897982) (hmzP 1259490699227),
   hmzC (hmzP 6659534275041) (hmzP 6659535702921)
      (hmzN 9400852032065) (hmzN 9400850483933),
   hmzC (hmzP 17739851880821) (hmzP 17739854126613)
      (hmzP 64287697313932) (hmzP 64287699695601),
   hmzC (hmzP 428351169767651) (hmzP 428351173611964)
      (hmzP 366992688366175) (hmzP 366992691569406)],
  [hmzC (hmzP 2932369274645) (hmzP 2932369668613)
      (hmzN 1088544898438) (hmzN 1088544721362),
   hmzC (hmzP 19687386253112) (hmzP 19687387023611)
      (hmzP 15974974561169) (hmzP 15974975223187),
   hmzC (hmzP 173445221256457) (hmzP 173445222459778)
      (hmzN 92892538103991) (hmzN 92892536786815)],
  [hmzC (hmzN 3250063477027) (hmzN 3250062682551)
      (hmzN 6251311774937) (hmzN 6251311091757),
   hmzC (hmzN 39269143323356) (hmzN 39269142119606)
      (hmzP 34987098485429) (hmzP 34987099800938),
   hmzC (hmzN 170327330886231) (hmzN 170327328930625)
      (hmzN 380605297744795) (hmzN 380605295670367)],
  [hmzC (hmzP 9191895360247) (hmzP 9191896515234)
      (hmzN 11927575164413) (hmzN 11927573906864),
   hmzC (hmzP 24858937823586) (hmzP 24858939655781)
      (hmzP 84916494226070) (hmzP 84916496169848),
   hmzC (hmzP 577354072149018) (hmzP 577354075275639)
      (hmzP 501859345594268) (hmzP 501859348188857)],
  [], []⟩
private theorem _mpf_512_r6_k0 :
    uCheckOptStateS1 (uInitProbesS1 512 6 mpfMidPRow_m512_r6 mpfMP512_r6_p0)
      _mpfSt_512_r6_s0 = true := by
  decide +kernel
private def _mpfSt_512_r6_s1 : MidPProbeState :=
  ⟨hmzP 158040397659663, hmzP 360845677018342,
  [hmzC (hmzP 109807315304) (hmzP 109814160155)
      (hmzP 138463355138) (hmzP 138470133086),
   hmzC (hmzN 90039828675) (hmzN 90025996009)
      (hmzP 200964056870) (hmzP 200977891879),
   hmzC (hmzN 248290899154) (hmzN 248267121157)
      (hmzN 177449404555) (hmzN 177425626386),
   hmzC (hmzN 413736189514) (hmzN 413701770042)
      (hmzP 210306834541) (hmzP 210341252290),
   hmzC (hmzN 1331796648967) (hmzN 1331748863430)
      (hmzP 1859182324085) (hmzP 1859230104568),
   hmzC (hmzP 60547031764223) (hmzP 60547066731153)
      (hmzP 41998197137004) (hmzP 41998232050699),
   hmzC (hmzP 212221810376279) (hmzP 212221829690798)
      (hmzP 146838612570001) (hmzP 146838631807437)],
  [hmzC (hmzN 68794056072) (hmzN 68784341640)
      (hmzN 17765564998) (hmzN 17755981607),
   hmzC (hmzN 369202054134) (hmzN 369181197322)
      (hmzP 226901282694) (hmzP 226922144136),
   hmzC (hmzN 234562523876) (hmzN 234524961834)
      (hmzP 1565009114885) (hmzP 1565046677372),
   hmzC (hmzP 39156249029644) (hmzP 39156307503001)
      (hmzN 31371312801357) (hmzN 31371254340879),
   hmzC (hmzP 458023518850083) (hmzP 458023607986480)
      (hmzN 13359795551079) (hmzN 13359706450351)],
  [hmzC (hmzN 250995672448) (hmzN 250977267139)
      (hmzP 102003133186) (hmzP 102021543875),
   hmzC (hmzN 505192417746) (hmzN 505158897327)
      (hmzN 832790542023) (hmzN 832757021511),
   hmzC (hmzP 2970314649396) (hmzP 2970367200204)
      (hmzN 3297144026154) (hmzN 3297091480210),
   hmzC (hmzN 100961004400096) (hmzN 100960922271876)
      (hmzP 14847560561863) (hmzP 14847642676506),
   hmzC (hmzP 708494549888214) (hmzP 708494616097047)
      (hmzP 486014152441584) (hmzP 486014218527657)],
  [hmzC (hmzN 925927327084) (hmzN 925909870614)
      (hmzP 320456105007) (hmzP 320473114174),
   hmzC (hmzN 8874104678921) (hmzN 8874063985647)
      (hmzP 5898799035606) (hmzP 5898839742124),
   hmzC (hmzN 38419421272833) (hmzN 38419346090844)
      (hmzN 51332092166834) (hmzN 51332016970301),
   hmzC (hmzP 640525437655806) (hmzP 640525560956122)
      (hmzN 557259604828237) (hmzN 557259481541402)],
  [hmzC (hmzP 488821277766) (hmzP 488850621059)
      (hmzP 404385216137) (hmzP 404414577489),
   hmzC (hmzN 2440584783254) (hmzN 2440528115265)
      (hmzN 1027198840602) (hmzN 1027142170763),
   hmzC (hmzN 26607008503655) (hmzN 26606914304534)
      (hmzP 24421504508362) (hmzP 24421598695228),
   hmzC (hmzN 511193681090100) (hmzN 511193516451111)
      (hmzP 35508268084890) (hmzP 35508432700850)],
  [hmzC (hmzP 6295817477074) (hmzP 6295830019854)
      (hmzN 4238075016047) (hmzN 4238062701151),
   hmzC (hmzP 5391540341877) (hmzP 5391568816717)
      (hmzP 15288101358177) (hmzP 15288129840970),
   hmzC (hmzP 157235756705054) (hmzP 157235809655022)
      (hmzP 215573030485907) (hmzP 215573083457478)],
  [hmzC (hmzN 4995628387292) (hmzN 4995602836407)
      (hmzP 2074570326077) (hmzP 2074595885735),
   hmzC (hmzN 18939524602382) (hmzN 18939476615402)
      (hmzN 32993376189431) (hmzN 32993328194264),
   hmzC (hmzP 334502531106177) (hmzP 334502610655844)
      (hmzN 287932324523915) (hmzN 287932244985470)],
  [hmzC (hmzN 2834249274452) (hmzN 2834206031225)
      (hmzN 1996417741040) (hmzN 1996374496691),
   hmzC (hmzN 38747840898460) (hmzN 38747768888265)
      (hmzP 32815277852689) (hmzP 32815349847469),
   hmzC (hmzN 724762147331923) (hmzN 724762021067500)
      (hmzP 48289472976806) (hmzP 48289599209888)],
  [], []⟩
private theorem _mpf_512_r6_k1 :
    uCheckOptStateS1 (uEvalProbesS1 6 mpfMP512_r6_p1 _mpfSt_512_r6_s0)
      _mpfSt_512_r6_s1 = true := by
  decide +kernel
private theorem _mpf_512_r6_k2 :
    uCheckProbeTailS1 512 16 6 mpfMidPVSeq_512 mpfMidPRow_m512_r6
      mpfMP512_r6_p2 _mpfSt_512_r6_s1 = true := by
  decide +kernel
private lemma _mpf_512_r6_ok :
    checkGHMidPRowsSlice false 512 16 mpfMidPVSeq_512
      6 [mpfMidPRow_m512_r6] = true :=
  checkGHMidPRowsSlice_of_probes3_s1 (uInitProbes_sound_s1 _mpf_512_r6_k0)
    (uEvalProbes_sound_s1 _mpf_512_r6_k1)
    (uCheckProbeTail_sound_s1 _mpf_512_r6_k2) rfl
private def _mpfSt_512_r7_s0 : MidPProbeState :=
  ⟨hmzP 111242273515097, hmzP 158655745973524,
  [hmzC (hmzP 33725725247) (hmzP 33725806724)
      (hmzP 29182790938) (hmzP 29182862670),
   hmzC (hmzP 497636713) (hmzP 497815738)
      (hmzP 1948332039) (hmzP 1948512458),
   hmzC (hmzP 42068049859) (hmzP 42068307113)
      (hmzP 68333153581) (hmzP 68333406151),
   hmzC (hmzP 98855525437) (hmzP 98855985481)
      (hmzP 222257133273) (hmzP 222257597787),
   hmzC (hmzP 2945353312548) (hmzP 2945353980589)
      (hmzP 540661416129) (hmzP 540662014931),
   hmzC (hmzP 3149337217106) (hmzP 3149338256227)
      (hmzP 2692874796768) (hmzP 2692875639709),
   hmzC (hmzP 136823019646427) (hmzP 136823021286534)
      (hmzN 86214713894826) (hmzN 86214712586287),
   hmzC (hmzP 418881257694217) (hmzP 418881259506929)
      (hmzN 264190445244098) (hmzN 264190443830736)],
  [hmzC (hmzN 93068624707) (hmzN 93068460734)
      (hmzN 192491022985) (hmzN 192490880758),
   hmzC (hmzN 117221394506) (hmzN 117221017028)
      (hmzN 137937910405) (hmzN 137937530286),
   hmzC (hmzN 561332060118) (hmzN 561331505786)
      (hmzN 813115558975) (hmzN 813115015333),
   hmzC (hmzP 4639942293553) (hmzP 4639943313517)
      (hmzN 6494008864747) (hmzN 6494007833601),
   hmzC (hmzN 48931946023816) (hmzN 48931944487567)
      (hmzN 11217584872542) (hmzN 11217583505658),
   hmzC (hmzN 457703855101769) (hmzN 457703852590045)
      (hmzP 38453411082335) (hmzP 38453413081497)],
  [hmzC (hmzP 84992799890) (hmzP 84993157683)
      (hmzP 45664622973) (hmzP 45664983021),
   hmzC (hmzP 342951851533) (hmzP 342952372326)
      (hmzP 163433797007) (hmzP 163434307662),
   hmzC (hmzN 667213098595) (hmzN 667212161326)
      (hmzP 2136757115874) (hmzP 2136758063902),
   hmzC (hmzP 10030411560101) (hmzP 10030412926089)
      (hmzP 3308366337170) (hmzP 3308367563823),
   hmzC (hmzP 95722843292027) (hmzP 95722845455835)
      (hmzP 972730730335) (hmzP 972732479222),
   hmzC (hmzP 720866124669199) (hmzP 720866128302102)
      (hmzN 457326233627024) (hmzN 457326230746501)],
  [hmzC (hmzN 870222872400) (hmzN 870222344766)
      (hmzN 1407496670982) (hmzN 1407496240637),
   hmzC (hmzN 1121295492643) (hmzN 1121294181792)
      (hmzN 1724971128989) (hmzN 1724969811144),
   hmzC (hmzN 3455505782981) (hmzN 3455503862258)
      (hmzN 11356201302623) (hmzN 11356199421424),
   hmzC (hmzP 61670015803699) (hmzP 61670019323444)
      (hmzN 85951183677670) (hmzN 85951180111312),
   hmzC (hmzN 776086266952658) (hmzN 776086261795225)
      (hmzN 141701740601073) (hmzN 141701735990431)],
  [hmzC (hmzP 649303614394) (hmzP 649304433500)
      (hmzP 116964336316) (hmzP 116965160497),
   hmzC (hmzP 1042247604404) (hmzP 1042248851201)
      (hmzP 1077778565236) (hmzP 1077779788226),
   hmzC (hmzN 6424250438105) (hmzN 6424248176124)
      (hmzP 8596089360418) (hmzP 8596091649709),
   hmzC (hmzP 63649532976025) (hmzP 63649536240686)
      (hmzP 16697105575337) (hmzP 16697108532873),
   hmzC (hmzP 558765776869676) (hmzP 558765781966879)
      (hmzN 41744645002817) (hmzN 41744640848100)],
  [hmzC (hmzP 523060195481) (hmzP 523060501129)
      (hmzP 112482125895) (hmzP 112482388644),
   hmzC (hmzP 1091355010784) (hmzP 1091355737044)
      (hmzP 2992434636970) (hmzP 2992435369263),
   hmzC (hmzN 5893470720997) (hmzN 5893469636566)
      (hmzP 24204177207190) (hmzP 24204178272708),
   hmzC (hmzN 97781595942904) (hmzN 97781593897495)
      (hmzP 164064999074757) (hmzP 164065001146192)],
  [hmzC (hmzN 799373051726) (hmzN 799372316410)
      (hmzN 825689458660) (hmzN 825688718919),
   hmzC (hmzN 1116790450691) (hmzN 1116789363983)
      (hmzN 5873007548813) (hmzN 5873006483663),
   hmzC (hmzP 32566387397289) (hmzP 32566389401401)
      (hmzN 41626294707847) (hmzN 41626292678696),
   hmzC (hmzN 408944651291278) (hmzN 408944648305054)
      (hmzN 67775853376434) (hmzN 67775850715352)],
  [hmzC (hmzP 1301304749971) (hmzP 1301305793272)
      (hmzP 1393878750058) (hmzP 1393879772035),
   hmzC (hmzN 8044652644186) (hmzN 8044650761080)
      (hmzP 11862135139729) (hmzP 11862137047127),
   hmzC (hmzP 84507722284464) (hmzP 84507725009860)
      (hmzP 21497522418683) (hmzP 21497524871102),
   hmzC (hmzP 758036961509109) (hmzP 758036965773340)
      (hmzN 54243554390243) (hmzN 54243550954904)],
  [], []⟩
private theorem _mpf_512_r7_k0 :
    uCheckOptStateS1 (uInitProbesS1 512 7 mpfMidPRow_m512_r7 mpfMP512_r7_p0)
      _mpfSt_512_r7_s0 = true := by
  decide +kernel
private def _mpfSt_512_r7_s1 : MidPProbeState :=
  ⟨hmzP 147729786373868, hmzP 318475950998037,
  [hmzC (hmzP 26814898525) (hmzP 26823336561)
      (hmzP 27980419707) (hmzP 27988848094),
   hmzC (hmzP 22944135721) (hmzP 22963679791)
      (hmzP 17432703424) (hmzP 17452247101),
   hmzC (hmzN 97180322311) (hmzN 97151585353)
      (hmzP 27890575443) (hmzP 27919312391),
   hmzC (hmzP 67351556208) (hmzP 67392676906)
      (hmzN 244312491092) (hmzN 244271370425),
   hmzC (hmzN 227811677107) (hmzN 227741449259)
      (hmzN 49647652601) (hmzN 49577425145),
   hmzC (hmzN 943809770508) (hmzN 943756601069)
      (hmzN 1402441644966) (hmzN 1402388477235),
   hmzC (hmzN 28766283658439) (hmzN 28766207180478)
      (hmzP 65061160136742) (hmzP 65061236621530),
   hmzC (hmzN 111132573575576) (hmzN 111132512070876)
      (hmzP 250818912054642) (hmzP 250818973579896)],
  [hmzC (hmzN 92813532830) (hmzN 92800345902)
      (hmzN 153811603559) (hmzN 153798438140),
   hmzC (hmzP 63841931286) (hmzP 63874382687)
      (hmzN 11589605743) (hmzN 11557155208),
   hmzC (hmzN 208422781155) (hmzN 208373944280)
      (hmzN 27887817928) (hmzN 27838981264),
   hmzC (hmzN 1802954323069) (hmzN 1802882174082)
      (hmzN 917883133410) (hmzN 917810987136),
   hmzC (hmzP 21558587460971) (hmzP 21558720376073)
      (hmzP 2430035074571) (hmzP 2430167969372),
   hmzC (hmzP 486005496640485) (hmzP 486005596608763)
      (hmzN 68579111881767) (hmzN 68579012015149)],
  [hmzC (hmzN 199629996625) (hmzN 199601173270)
      (hmzP 52963128612) (hmzP 52991950771),
   hmzC (hmzP 36931736587) (hmzP 36975611399)
      (hmzN 510884151700) (hmzN 510840277043),
   hmzC (hmzP 768008919365) (hmzP 768073332464)
      (hmzN 400150198617) (hmzN 400085786832),
   hmzC (hmzP 13710668050546) (hmzP 13710788693039)
      (hmzP 1097418262793) (hmzP 1097538898354),
   hmzC (hmzN 81152547301558) (hmzN 81152455789651)
      (hmzN 1865977136644) (hmzN 1865885646936),
   hmzC (hmzN 325812645239769) (hmzN 325812504494506)
      (hmzP 784665505825568) (hmzP 784665646586280)],
  [hmzC (hmzN 865411841877) (hmzN 865385027575)
      (hmzN 981649847752) (hmzN 981623129879),
   hmzC (hmzN 364075608758) (hmzN 364002981449)
      (hmzP 707092647214) (hmzP 707165271176),
   hmzC (hmzN 6437430312970) (hmzN 6437320167721)
      (hmzN 7041984482272) (hmzN 7041874335276),
   hmzC (hmzP 18610572786711) (hmzP 18610738442075)
      (hmzN 59546570566920) (hmzN 59546404930797),
   hmzC (hmzP 899872205228163) (hmzP 899872543550330)
      (hmzP 62572169204351) (hmzP 62572507438721)],
  [hmzC (hmzN 299452588876) (hmzN 299401431364)
      (hmzP 353108267445) (hmzP 353159418280),
   hmzC (hmzP 334988706899) (hmzP 335070516520)
      (hmzN 802708248) (hmzN 720899020),
   hmzC (hmzN 972574561422) (hmzN 972452872075)
      (hmzN 1496115807863) (hmzN 1495994119639),
   hmzC (hmzN 4595892500005) (hmzN 4595638583542)
      (hmzN 485484801786) (hmzN 485230899787),
   hmzC (hmzN 409866910979815) (hmzN 409866719904765)
      (hmzP 45819492110529) (hmzP 45819683070553)],
  [hmzC (hmzP 622047789106) (hmzP 622067028344)
      (hmzN 296270276690) (hmzN 296251079920),
   hmzC (hmzP 817409521118) (hmzP 817459770672)
      (hmzN 365416602424) (hmzN 365366353132),
   hmzC (hmzN 890402446297) (hmzN 890325493934)
      (hmzP 19507140208868) (hmzP 19507217167853),
   hmzC (hmzN 98523998128216) (hmzN 98523881613740)
      (hmzP 247502636521136) (hmzP 247502753034521)],
  [hmzC (hmzN 389965111083) (hmzN 389919571245)
      (hmzP 248162283881) (hmzP 248207821677),
   hmzC (hmzN 3763905057795) (hmzN 3763834695972)
      (hmzN 4995682258538) (hmzN 4995611895847),
   hmzC (hmzP 17796902767339) (hmzP 17797008486101)
      (hmzN 32514645968037) (hmzN 32514540260957),
   hmzC (hmzP 505656620576190) (hmzP 505656835230881)
      (hmzP 38198333307368) (hmzP 38198547905723)],
  [hmzC (hmzP 231219261783) (hmzP 231283162650)
      (hmzN 389450453621) (hmzN 389386552936),
   hmzC (hmzP 347644570086) (hmzP 347739654708)
      (hmzN 1316561071817) (hmzN 1316465988769),
   hmzC (hmzN 3958754835367) (hmzN 3958556590079)
      (hmzN 699317914894) (hmzN 699119690468),
   hmzC (hmzN 632206935060288) (hmzN 632206788765787)
      (hmzP 73310184606640) (hmzP 73310330751174)],
  [], []⟩
private theorem _mpf_512_r7_k1 :
    uCheckOptStateS1 (uEvalProbesS1 7 mpfMP512_r7_p1 _mpfSt_512_r7_s0)
      _mpfSt_512_r7_s1 = true := by
  decide +kernel
private theorem _mpf_512_r7_k2 :
    uCheckProbeTailS1 512 16 7 mpfMidPVSeq_512 mpfMidPRow_m512_r7
      mpfMP512_r7_p2 _mpfSt_512_r7_s1 = true := by
  decide +kernel
private lemma _mpf_512_r7_ok :
    checkGHMidPRowsSlice false 512 16 mpfMidPVSeq_512
      7 [mpfMidPRow_m512_r7] = true :=
  checkGHMidPRowsSlice_of_probes3_s1 (uInitProbes_sound_s1 _mpf_512_r7_k0)
    (uEvalProbes_sound_s1 _mpf_512_r7_k1)
    (uCheckProbeTail_sound_s1 _mpf_512_r7_k2) rfl
private def _mpfSt_512_r8_s0 : MidPProbeState :=
  ⟨hmzP 92840557825586, hmzP 122589067541956,
  [hmzC (hmzN 645301824) (hmzN 645286757)
      (hmzN 1495973274) (hmzN 1495966771),
   hmzC (hmzN 382436361) (hmzN 382406024)
      (hmzN 5609480365) (hmzN 5609457826),
   hmzC (hmzP 11944512567) (hmzP 11944566336)
      (hmzP 13449910086) (hmzP 13449940212),
   hmzC (hmzP 47169696730) (hmzP 47169797772)
      (hmzN 63207785744) (hmzN 63207726137),
   hmzC (hmzP 230463268306) (hmzP 230463453886)
      (hmzN 196407772021) (hmzN 196407684324),
   hmzC (hmzP 3288552201229) (hmzP 3288552542467)
      (hmzN 785064282747) (hmzN 785064160293),
   hmzC (hmzP 14031121249751) (hmzP 14031121899897)
      (hmzN 3162046832429) (hmzN 3162046600409),
   hmzC (hmzP 161968795536724) (hmzP 161968796733405)
      (hmzN 44535385004930) (hmzN 44535384567376),
   hmzC (hmzP 524240280771431) (hmzP 524240282369130)
      (hmzN 143664399054725) (hmzN 143664398480003)],
  [hmzC (hmzN 8066663807) (hmzN 8066630675)
      (hmzN 28841445669) (hmzN 28841432499),
   hmzC (hmzN 14262584222) (hmzN 14262515249)
      (hmzP 25988429137) (hmzP 25988480022),
   hmzC (hmzN 146290804014) (hmzN 146290677139)
      (hmzP 92699832686) (hmzP 92699903276),
   hmzC (hmzN 931018414181) (hmzN 931018168397)
      (hmzP 810240320218) (hmzP 810240464778),
   hmzC (hmzN 7736130497852) (hmzN 7736130030919)
      (hmzP 3321418621164) (hmzP 3321418839728),
   hmzC (hmzN 57334481841855) (hmzN 57334480948558)
      (hmzP 11930134692452) (hmzP 11930135006701),
   hmzC (hmzN 396507739162582) (hmzN 396507737391384)
      (hmzP 98779802907948) (hmzP 98779803527653)],
  [hmzC (hmzP 1619389084) (hmzP 1619453333)
      (hmzN 18231173634) (hmzN 18231126101),
   hmzC (hmzP 63176412869) (hmzP 63176529382)
      (hmzP 14938643105) (hmzP 14938708625),
   hmzC (hmzP 231389211798) (hmzP 231389433174)
      (hmzN 315033040947) (hmzN 315032909590),
   hmzC (hmzP 2218944642129) (hmzP 2218945052770)
      (hmzN 1222842179666) (hmzN 1222841985629),
   hmzC (hmzP 17049173123413) (hmzP 17049173887684)
      (hmzN 3534212427748) (hmzN 3534212156276),
   hmzC (hmzP 118103480403929) (hmzP 118103481880278)
      (hmzN 28410393887229) (hmzN 28410393366544),
   hmzC (hmzP 817076227698781) (hmzP 817076230546046)
      (hmzN 224782983844039) (hmzN 224782982809684)],
  [hmzC (hmzN 78538161081) (hmzN 78538037704)
      (hmzN 216055432554) (hmzN 216055388324),
   hmzC (hmzN 185668788847) (hmzN 185668526948)
      (hmzP 313301468882) (hmzP 313301664110),
   hmzC (hmzN 1903949304934) (hmzN 1903948818087)
      (hmzP 1110749951717) (hmzP 1110750228671),
   hmzC (hmzN 12358379854957) (hmzN 12358378912008)
      (hmzP 9426294729355) (hmzP 9426295292572),
   hmzC (hmzN 99681385733808) (hmzN 99681383948633)
      (hmzP 39013265991998) (hmzP 39013266830589),
   hmzC (hmzN 729768843482764) (hmzN 729768840127144)
      (hmzP 156320742110171) (hmzP 156320743283874)],
  [hmzC (hmzP 4145057658) (hmzP 4145210522)
      (hmzN 78149212055) (hmzN 78149099158),
   hmzC (hmzP 251679462218) (hmzP 251679745659)
      (hmzN 45988745699) (hmzN 45988582863),
   hmzC (hmzP 1248625656660) (hmzP 1248626200760)
      (hmzN 1331704536882) (hmzN 1331704207734),
   hmzC (hmzP 11154185482233) (hmzP 11154186495710)
      (hmzN 4847158151432) (hmzN 4847157665634),
   hmzC (hmzP 82832858574325) (hmzP 82832860465975)
      (hmzN 16055714288735) (hmzN 16055713614382),
   hmzC (hmzP 571026600562220) (hmzP 571026604182583)
      (hmzN 141649409865216) (hmzN 141649408587491)],
  [hmzC (hmzP 92790907677) (hmzP 92790978194)
      (hmzP 84501877600) (hmzP 84501904501),
   hmzC (hmzP 362381973742) (hmzP 362382123819)
      (hmzN 410805718227) (hmzN 410805607552),
   hmzC (hmzP 3251590433515) (hmzP 3251590716251)
      (hmzN 1840461135967) (hmzN 1840460979044),
   hmzC (hmzP 22476628872423) (hmzP 22476629433887)
      (hmzN 13021502683231) (hmzN 13021502354557),
   hmzC (hmzP 171573630760561) (hmzP 171573631856473)
      (hmzN 57568006883488) (hmzN 57568006377082)],
  [hmzC (hmzN 78172497085) (hmzN 78172350447)
      (hmzP 174211178225) (hmzP 174211286952),
   hmzC (hmzN 950316847789) (hmzN 950316574985)
      (hmzP 584248753323) (hmzP 584248907249),
   hmzC (hmzN 6321604867714) (hmzN 6321604336882)
      (hmzP 4580356472466) (hmzP 4580356787752),
   hmzC (hmzN 50529101474684) (hmzN 50529100462462)
      (hmzP 18665551904877) (hmzP 18665552379402),
   hmzC (hmzN 367433668719421) (hmzN 367433666789570)
      (hmzP 77975498447010) (hmzP 77975499120181)],
  [hmzC (hmzP 329443835038) (hmzP 329444088786)
      (hmzN 68993218119) (hmzN 68993073174),
   hmzC (hmzP 1665348158355) (hmzP 1665348642758)
      (hmzN 1735321641772) (hmzN 1735321350812),
   hmzC (hmzP 14708099648326) (hmzP 14708100549711)
      (hmzN 6540861019919) (hmzN 6540860592265),
   hmzC (hmzP 109528787385077) (hmzP 109528789065877)
      (hmzN 21843429895726) (hmzN 21843429302932),
   hmzC (hmzP 756126503783402) (hmzP 756126506984690)
      (hmzN 187443301749532) (hmzN 187443300631071)],
  [], []⟩
private theorem _mpf_512_r8_k0 :
    uCheckOptStateS1 (uInitProbesS1 512 8 mpfMidPRow_m512_r8 mpfMP512_r8_p0)
      _mpfSt_512_r8_s0 = true := by
  decide +kernel
private def _mpfSt_512_r8_s1 : MidPProbeState :=
  ⟨hmzP 135986197141011, hmzP 269890068348490,
  [hmzC (hmzN 6038241386) (hmzN 6037002272)
      (hmzP 763539742) (hmzP 764769205),
   hmzC (hmzP 3070112095) (hmzP 3072914315)
      (hmzN 14229820080) (hmzN 14227018373),
   hmzC (hmzN 20457000902) (hmzN 20449848969)
      (hmzN 16576363757) (hmzN 16569211833),
   hmzC (hmzN 62331411707) (hmzN 62321113878)
      (hmzP 16488028842) (hmzP 16498326607),
   hmzC (hmzP 155962015656) (hmzP 155982701773)
      (hmzN 7746457447) (hmzN 7725771339),
   hmzC (hmzP 359094586427) (hmzP 359133605385)
      (hmzP 182385275946) (hmzP 182424294943),
   hmzC (hmzN 132940634965) (hmzN 132897568834)
      (hmzP 1682651964008) (hmzP 1682695031062),
   hmzC (hmzP 55338648140318) (hmzP 55338687440284)
      (hmzP 50822138493142) (hmzP 50822177779204),
   hmzC (hmzP 236878033408852) (hmzP 236878062854881)
      (hmzP 215755151615998) (hmzP 215755181025405)],
  [hmzC (hmzN 3517977225) (hmzN 3515834691)
      (hmzN 32133154832) (hmzN 32131034561),
   hmzC (hmzP 15056235388) (hmzP 15061234767)
      (hmzP 20945032044) (hmzP 20950030207),
   hmzC (hmzP 105790024777) (hmzP 105803208802)
      (hmzN 45055387805) (hmzN 45042203815),
   hmzC (hmzN 459496816664) (hmzN 459477909820)
      (hmzP 48308701827) (hmzP 48327608468),
   hmzC (hmzP 1397942471898) (hmzP 1397981485587)
      (hmzN 2093389045275) (hmzN 2093350031429),
   hmzC (hmzN 22427658256936) (hmzN 22427578265052)
      (hmzN 10836506421021) (hmzN 10836426432195),
   hmzC (hmzN 496745977615318) (hmzN 496745885086806)
      (hmzP 101991390164147) (hmzP 101991482672159)],
  [hmzC (hmzN 14155904267) (hmzN 14151539444)
      (hmzN 55711146855) (hmzN 55706783648),
   hmzC (hmzN 83259863380) (hmzN 83248278477)
      (hmzP 45735362078) (hmzP 45746946948),
   hmzC (hmzP 70024124611) (hmzP 70040571537)
      (hmzN 80116118988) (hmzN 80099672192),
   hmzC (hmzN 233684891110) (hmzN 233651612011)
      (hmzN 68834245594) (hmzN 68800966459),
   hmzC (hmzN 5834539649489) (hmzN 5834471274218)
      (hmzN 6497570144327) (hmzN 6497501769776),
   hmzC (hmzP 69995780154701) (hmzP 69995860197823)
      (hmzN 589128301274) (hmzN 589048258720),
   hmzC (hmzP 629050281307543) (hmzP 629050359531199)
      (hmzP 559259258215622) (hmzP 559259336378955)],
  [hmzC (hmzN 16405620339) (hmzN 16400693497)
      (hmzN 273289635591) (hmzN 273284794982),
   hmzC (hmzP 236931191780) (hmzP 236943157157)
      (hmzP 383388079457) (hmzP 383400040141),
   hmzC (hmzP 937401455983) (hmzP 937434133667)
      (hmzN 834118122573) (hmzN 834085445017),
   hmzC (hmzN 4797454513491) (hmzN 4797409158546)
      (hmzP 2212627460481) (hmzP 2212672814439),
   hmzC (hmzP 61218256489652) (hmzP 61218348230740)
      (hmzN 32015636223237) (hmzN 32015544480641),
   hmzC (hmzN 761354266844223) (hmzN 761354060101057)
      (hmzN 445855143847328) (hmzN 445854937117138)],
  [hmzC (hmzN 81990940093) (hmzN 81982874877)
      (hmzN 145146038610) (hmzN 145137980573),
   hmzC (hmzN 305016601993) (hmzN 304994063432)
      (hmzP 171484571089) (hmzP 171507109505),
   hmzC (hmzP 699853539013) (hmzP 699885008136)
      (hmzP 237502085190) (hmzP 237533553861),
   hmzC (hmzN 1910460376335) (hmzN 1910398098931)
      (hmzP 475036039040) (hmzP 475098315699),
   hmzC (hmzP 16561014522249) (hmzP 16561152580677)
      (hmzN 741317933157) (hmzN 741179877700),
   hmzC (hmzP 437236245726789) (hmzP 437236415041925)
      (hmzN 69276487994678) (hmzN 69276318709815)],
  [hmzC (hmzP 54766610136) (hmzP 54770190928)
      (hmzP 115325774091) (hmzP 115329306692),
   hmzC (hmzN 444015065558) (hmzN 444006465390)
      (hmzN 551981064329) (hmzN 551972466511),
   hmzC (hmzP 491400350424) (hmzP 491423741116)
      (hmzP 1654462848740) (hmzP 1654486239301),
   hmzC (hmzN 17346759858805) (hmzN 17346726677726)
      (hmzN 5773818795854) (hmzN 5773785616722),
   hmzC (hmzN 256888620512122) (hmzN 256888551117710)
      (hmzP 51387297911045) (hmzP 51387367295442)],
  [hmzC (hmzP 162278024341) (hmzP 162285649752)
      (hmzP 174165752021) (hmzP 174173373920),
   hmzC (hmzP 404659133346) (hmzP 404680037866)
      (hmzN 472427185272) (hmzN 472406280838),
   hmzC (hmzN 2219333769488) (hmzN 2219304440110)
      (hmzP 921143032397) (hmzP 921172361144),
   hmzC (hmzP 32090178036971) (hmzP 32090237780903)
      (hmzN 16347509626651) (hmzN 16347449881344),
   hmzC (hmzN 415921830847546) (hmzN 415921697438716)
      (hmzN 259142615994928) (hmzN 259142482595741)],
  [hmzC (hmzN 371353333637) (hmzN 371334753874)
      (hmzP 214197994939) (hmzP 214216574596),
   hmzC (hmzP 868010473782) (hmzP 868036336983)
      (hmzP 152643792332) (hmzP 152669655112),
   hmzC (hmzN 2382973823652) (hmzN 2382922398535)
      (hmzP 1231005524004) (hmzP 1231056948365),
   hmzC (hmzP 21171586814067) (hmzP 21171701905592)
      (hmzN 93826913684) (hmzN 93711826233),
   hmzC (hmzP 651880425319089) (hmzP 651880564960970)
      (hmzN 111726851270366) (hmzN 111726711668097)],
  [], []⟩
private theorem _mpf_512_r8_k1 :
    uCheckOptStateS1 (uEvalProbesS1 8 mpfMP512_r8_p1 _mpfSt_512_r8_s0)
      _mpfSt_512_r8_s1 = true := by
  decide +kernel
private theorem _mpf_512_r8_k2 :
    uCheckProbeTailS1 512 16 8 mpfMidPVSeq_512 mpfMidPRow_m512_r8
      mpfMP512_r8_p2 _mpfSt_512_r8_s1 = true := by
  decide +kernel
private lemma _mpf_512_r8_ok :
    checkGHMidPRowsSlice false 512 16 mpfMidPVSeq_512
      8 [mpfMidPRow_m512_r8] = true :=
  checkGHMidPRowsSlice_of_probes3_s1 (uInitProbes_sound_s1 _mpf_512_r8_k0)
    (uEvalProbes_sound_s1 _mpf_512_r8_k1)
    (uCheckProbeTail_sound_s1 _mpf_512_r8_k2) rfl
theorem mpfMidPSpine512_rows_b :
    checkGHMidPRowsSlice false 512 16 mpfMidPVSeq_512 3 mpfMidPRows512 = true :=
  hmzRowsCons _mpf_512_r3_ok (hmzRowsCons _mpf_512_r4_ok
    (hmzRowsCons _mpf_512_r5_ok (hmzRowsCons _mpf_512_r6_ok
      (hmzRowsCons _mpf_512_r7_ok _mpf_512_r8_ok))))
end QuantumComputation.Specs.DickeSol.HmzLowK
end
