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
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.TwoGearQPE
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.TwoGearBondDefer

/-!
# Tail-Shifted Three-Gear Bond-Deferred Sine-Window QPE (`TailShiftWindow46847`)

Provides reusable window, relocation, and pure rational QPE error-budget infrastructure for
Tail-Shifted Three-Gear Bond-Deferred QPE (`M = 46,847, mCut = 10, m1 ∈ {7, 8}`) and general
Three-Gear Bond-Deferred QPE (`StageC + StageM + StageF`).

## References
- A. Luis and J. Peřina, *Phys. Rev. A* **54**, 4564 (1996), DOI: 10.1103/PhysRevA.54.4564.
- M. Möttönen et al., *Phys. Rev. Lett.* **93**, 130502 (2004), DOI: 10.1103/PhysRevLett.93.130502.
- R. Babbush et al., *Phys. Rev. X* **8**, 041015 (2018), DOI: 10.1103/PhysRevX.8.041015.
- J. Lee et al., *PRX Quantum* **2**, 030305 (2021), DOI: 10.1103/PRXQuantum.2.030305.
-/

@[expose] public section

namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.TailShiftBox
open QuantumComputation.Specs QuantumComputation.Specs.P450
open TwoGearBox

/-- Coarse super-step count `⌊M / 2 ^ m2⌋`. -/
abbrev mcSteps (M m2 : ℕ) : ℕ := M / 2 ^ m2

/-- Pure rational QPE error-budget box for Tail-Shifted Three-Gear QPE with `nStd` standard
coarse super-steps, `1` tail coarse super-step (`dSuperTailUb`), `2 ^ (m2 - m1) - 1` middle
super-steps (`dSuperMUb`), and `2 ^ m1 - 1` fine steps (`dStepFUb`). -/
def TailShiftRayQuantSuperBox (M nStd m2 m1 : ℕ)
    (ci wUb dSuperStdUb dSuperTailUb dSuperMUb dStepFUb δH eUb gUb effUb kp : ℝ) : Prop :=
  46368 ≤ M ∧ M ≤ 47488 ∧ 440 / 100 ≤ gUb ∧ gUb ≤ 496 / 100 ∧
    ((M ≤ 46752 ∧ gUb ≤ 4715 / 1000 ∧ 99475 / 10 ^ 5 ≤ kp) ∨
      (M ≤ 47008 ∧ gUb ≤ 475 / 100 ∧ 99478 / 10 ^ 5 ≤ kp) ∨
      99487 / 10 ^ 5 ≤ kp) ∧
    0 ≤ δH ∧ 0 ≤ gUb ∧ 0 ≤ kp ∧ 0 ≤ effUb ∧
    eUb + 134987442 / 10 ^ 6 ≤ gUb ∧ gUb + δH ≤ 11 ∧
    gUb * (2 * (973864 / 10000) - gUb) ≤ effUb ^ 2 ∧
    kp * (effUb / 2) * ((314159265358979323847 / 10 ^ 20) / ((M : ℝ) + 1)) + δH +
      gUb * ((ci + wUb) +
        ((nStd : ℝ) * dSuperStdUb + dSuperTailUb +
          ((2 ^ (m2 - m1) - 1 : ℕ) : ℝ) * dSuperMUb +
          ((2 ^ m1 - 1 : ℕ) : ℝ) * dStepFUb)) ≤ 1 / 1000

/-- Upgrades any `BaseRayQuantBox M` into `TailShiftRayQuantSuperBox M nStd m2 m1` whenever
`nStd * lStd + lTail + (2 ^ (m2 - m1) - 1) * 2 ^ m1 + (2 ^ m1 - 1) = M`. -/
theorem tailShiftRayQuantSuperBox_of_baseBox {M nStd lStd lTail m2 m1 : ℕ}
    (hSteps : nStd * lStd + lTail + (2 ^ (m2 - m1) - 1) * 2 ^ m1 + (2 ^ m1 - 1) = M)
    {ci wUb dStepUb dStd dTail dM dF δH eUb gUb effUb kp : ℝ}
    (hbox : BaseRayQuantBox M ci wUb dStepUb δH eUb gUb effUb kp)
    (hStd : dStd ≤ (lStd : ℝ) * dStepUb) (hTail : dTail ≤ (lTail : ℝ) * dStepUb)
    (hM : dM ≤ (2 ^ m1 : ℝ) * dStepUb) (hF : dF ≤ dStepUb) :
    TailShiftRayQuantSuperBox M nStd m2 m1 ci wUb dStd dTail dM dF δH eUb gUb effUb kp := by
  obtain ⟨h1, h2, h3, h4, h5, h6, hg0, h8, h9, h10, h11, h12, h13⟩ := hbox
  refine ⟨h1, h2, h3, h4, h5, h6, hg0, h8, h9, h10, h11, h12, ?_⟩
  have hsum_real : (nStd : ℝ) * (lStd : ℝ) + (lTail : ℝ) +
      ((2 ^ (m2 - m1) - 1 : ℕ) : ℝ) * (2 ^ m1 : ℝ) + ((2 ^ m1 - 1 : ℕ) : ℝ) = (M : ℝ) := by
    exact_mod_cast hSteps
  have hStd' := mul_le_mul_of_nonneg_left hStd (Nat.cast_nonneg nStd)
  have hM' := mul_le_mul_of_nonneg_left hM (Nat.cast_nonneg (2 ^ (m2 - m1) - 1))
  have hF' := mul_le_mul_of_nonneg_left hF (Nat.cast_nonneg (2 ^ m1 - 1))
  have htot_step :
      (nStd : ℝ) * dStd + dTail + ((2 ^ (m2 - m1) - 1 : ℕ) : ℝ) * dM +
        ((2 ^ m1 - 1 : ℕ) : ℝ) * dF ≤ (M : ℝ) * dStepUb := by
    calc (nStd : ℝ) * dStd + dTail + ((2 ^ (m2 - m1) - 1 : ℕ) : ℝ) * dM +
            ((2 ^ m1 - 1 : ℕ) : ℝ) * dF
        ≤ (nStd : ℝ) * ((lStd : ℝ) * dStepUb) + (lTail : ℝ) * dStepUb +
            ((2 ^ (m2 - m1) - 1 : ℕ) : ℝ) * ((2 ^ m1 : ℝ) * dStepUb) +
            ((2 ^ m1 - 1 : ℕ) : ℝ) * dStepUb := by linarith [hStd', hTail, hM', hF']
      _ = ((nStd : ℝ) * (lStd : ℝ) + (lTail : ℝ) +
            ((2 ^ (m2 - m1) - 1 : ℕ) : ℝ) * (2 ^ m1 : ℝ) +
            ((2 ^ m1 - 1 : ℕ) : ℝ)) * dStepUb := by ring
      _ = (M : ℝ) * dStepUb := by rw [hsum_real]
  have hg_step :
      gUb * ((ci + wUb) +
          ((nStd : ℝ) * dStd + dTail +
            ((2 ^ (m2 - m1) - 1 : ℕ) : ℝ) * dM +
            ((2 ^ m1 - 1 : ℕ) : ℝ) * dF)) ≤
        gUb * ((ci + wUb) + (M : ℝ) * dStepUb) :=
    mul_le_mul_of_nonneg_left (by linarith [htot_step]) hg0
  linarith [h13, hg_step]

end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.TailShiftBox

namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.TailShiftWindow46847
open QuantumComputation.Specs QuantumComputation.Specs.P450

open Operator QProg Matrix HermitianMat Circuit Real
open QuantumComputation.Specs QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution
open QuantumComputation.Specs.P450
open BlockEncodingCore BlockEncodingCircuit
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.WalkQPEBridge hiding
  rActLoc rActLoc_disjoint_rScrLoc rCatInAct rCatLoc rQPEInAct rQPEInAct_disjoint_rWalkCatInAct
  rQPEInAnc rQPELoc rQPELoc_disjoint_rScrLoc rQPELoc_disjoint_rWalkCatLoc rScrLoc rScrUbLoc
  rWalkCatInAct rWalkCatLoc rWalkCatLoc_disjoint_rScrLoc
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.WalkQPEBridgeXMeas hiding
  image_rFullZeroLoc rFullZeroLoc
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.WalkQPEFlexBridge hiding
  cleanRealizesSet_of_rScrUbLoc cleanRealizes_rScrLoc_of_sub
open TopIntegrationBridge
open Cat11CompactPhase2Bridge
open FastUniform
open UpperBound
open DihedralWalkQPE
open DihedralWalkQPE.BlockReflection
open DihedralWalkQPE.ApproxIqft16
open DihedralWalkQPE.PhaseSwar
open DihedralWalkQPE.SineWindowFlexM
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.DihedralWalkQPE.MultiGearQPE (
  outRemWidth outZeroPrefixReg combARem combAncillas combQubits combWalkCatReg
  combWalkReflRegs combWalkReflCovers comb_hbScr16
  CleanWalkRefl2 WalkRefl2ErrLe P450RefVarBound ReordSosHyp RealizesP450GroundQPE
  tensorWalkCat_smul_right
  approxPhaseGrad11Ray exactPhaseGrad11RayUnitary norm_phaseGrad11RayScalar
  exactPhaseGrad11RayUnitary_mulVec_zero approxPhaseGrad11Ray_count_toff
  approxPhaseGrad11Ray_count_t norm_approxPhaseGrad11Ray_sub_le
)
open CoherentAlias
open TwoGearBox
open TailShiftBox
open TwoGearQPEPhase5
open TwoGearBondDefer
open scoped Matrix BigOperators Matrix.Norms.L2Operator

local instance (priority := 1000000) instNeZeroTwoPowTailShiftWin (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩

/-! ## Section 1: Multi-Layer `mottonenCascade` Split & Commutation -/

theorem mottonenCascade_congr_tot {n t₁ t₂ : ℕ} (ht : t₁ = t₂)
    (h₁ : t₁ ≤ n) (h₂ : t₂ ≤ n) (trs : List WordPairTree) :
    mottonenCascade n t₁ h₁ trs = mottonenCascade n t₂ h₂ trs := by
  subst ht
  rfl

/-- Splitting `mottonenCascade (r + q) (r + s)` into top `s` layers on `q` wires followed by
bottom `r` layers on `r + q` wires preserves primitive gate counts and unitary evaluation. -/
theorem mottonenCascade_split_gen (r q : ℕ) : ∀ (s : ℕ) (hs : s ≤ q) (trs : List WordPairTree),
    (∀ {d : ℕ} (g : PrimitiveGate d),
      (mottonenCascade q s hs (trs.take s)).count g +
        (mottonenCascade (r + q) r (by omega) (trs.drop s)).count g =
      (mottonenCascade (r + q) (r + s) (by omega) trs).count g) ∧
    (mottonenCascade (r + q) r (by omega) (trs.drop s)).eval *
      (QRegister.block r q (by omega)).embedUnitary
        (mottonenCascade q s hs (trs.take s)).eval =
    (mottonenCascade (r + q) (r + s) (by omega) trs).eval
  | 0, _, _ => ⟨fun _ ↦ by simp [mottonenCascade], by simp [mottonenCascade]⟩
  | s' + 1, _, [] => ⟨fun g ↦ by
      have h0 : (mottonenCascade (r + q) r (by omega) []).count g = 0 := by
        cases r <;> simp [mottonenCascade]
      rw [mottonenCascade_congr_tot (Nat.add_assoc r s' 1).symm _ (by omega)]
      simp [mottonenCascade, h0],
    by
      have h0 : (mottonenCascade (r + q) r (by omega) []).eval = 1 := by
        cases r <;> simp [mottonenCascade]
      rw [mottonenCascade_congr_tot (Nat.add_assoc r s' 1).symm _ (by omega)]
      simp [mottonenCascade, h0]⟩
  | s' + 1, hs, tr :: trs => by
      obtain ⟨ihCnt, ihEval⟩ := mottonenCascade_split_gen r q s' (by omega) trs
      let rHi : QRegister q (r + q) := QRegister.block r q (by omega)
      have hBlk {a b c d : ℕ} (hab : a + b ≤ c) (hd : d < a) :
          (QRegister.block a b hab).DisjointWires (QRegister.singleton ⟨d, by omega⟩) := by
        rw [QRegister.disjoint_iff]
        intro i j hij
        have hv := congrArg Fin.val hij
        simp only [QRegister.block_apply_val, QRegister.singleton_apply] at hv
        omega
      have hD₁ := hBlk (a := s' + 1) (b := q - (s' + 1)) (c := q) (by omega) (Nat.lt_succ_self s')
      have hD₂ := hBlk (a := (r + s') + 1) (b := (r + q) - ((r + s') + 1)) (c := r + q)
        (by omega) (Nat.lt_succ_self (r + s'))
      have hDC : (rHi.compose (QRegister.block (s' + 1) (q - (s' + 1)) (by omega))).DisjointWires
          (QRegister.singleton (rHi ⟨s', by omega⟩)) := by
        rw [QRegister.disjoint_iff]
        intro i j hij
        have hv := congrArg Fin.val hij
        simp only [rHi, QRegister.compose_apply, QRegister.block_apply_val,
          QRegister.singleton_apply] at hv
        omega
      have hCongr {k₁ k₂ : ℕ} (hk : k₁ = k₂) (r₁ : QRegister k₁ (r + q))
          (r₂ : QRegister k₂ (r + q)) (t₁ t₂ : Wire (r + q)) (ht : t₁ = t₂)
          (hd₁ : r₁.DisjointWires (QRegister.singleton t₁))
          (hd₂ : r₂.DisjointWires (QRegister.singleton t₂))
          (hr : ∀ (i : ℕ) (hi₁ : i < k₁) (hi₂ : i < k₂), (r₁ ⟨i, hi₁⟩).val = (r₂ ⟨i, hi₂⟩).val) :
          wordPairTreeCircuit k₁ r₁ t₁ hd₁ tr = wordPairTreeCircuit k₂ r₂ t₂ hd₂ tr := by
        subst hk
        subst ht
        have hreq : r₁ = r₂ := by
          ext i
          exact hr i.val i.isLt i.isLt
        subst hreq
        rfl
      have hCircEq : (wordPairTreeCircuit (q - (s' + 1))
          (QRegister.block (s' + 1) (q - (s' + 1)) (by omega)) ⟨s', by omega⟩ hD₁ tr).onRegister
            rHi = wordPairTreeCircuit ((r + q) - ((r + s') + 1))
            (QRegister.block ((r + s') + 1) ((r + q) - ((r + s') + 1)) (by omega))
            ⟨r + s', by omega⟩ hD₂ tr :=
        (wordPairTreeCircuit_onRegister rHi (q - (s' + 1))
          (QRegister.block (s' + 1) (q - (s' + 1)) (by omega)) ⟨s', by omega⟩ hD₁ hDC tr).trans
          (hCongr (by omega) _ _ _ _
            (Fin.ext (by simp only [rHi, QRegister.block_apply_val])) hDC hD₂ fun i _ _ ↦ by
              simp only [rHi, QRegister.compose_apply, QRegister.block_apply_val]
              omega)
      refine ⟨fun g ↦ ?_, ?_⟩
      · have hCnt := congrArg (fun c ↦ c.count g) hCircEq
        rw [Circuit.count_onRegister] at hCnt
        rw [List.take_succ_cons, List.drop_succ_cons,
          mottonenCascade_congr_tot (Nat.add_assoc r s' 1).symm _ (by omega)]
        dsimp only [mottonenCascade]
        rw [Circuit.count_seq, Circuit.count_seq, hCnt, ← ihCnt g]
        exact Nat.add_assoc _ _ _
      · have hEv := congrArg Circuit.eval hCircEq
        rw [Circuit.eval_onRegister] at hEv
        dsimp only [rHi] at hEv
        rw [List.take_succ_cons, List.drop_succ_cons,
          mottonenCascade_congr_tot (Nat.add_assoc r s' 1).symm _ (by omega)]
        dsimp only [mottonenCascade]
        rw [Circuit.eval_seq, Circuit.eval_seq, QRegister.embedUnitary_mul,
          ← mul_assoc, ihEval, hEv]

theorem mottonenCascade_split_of_eq (n r q s tot : ℕ) (hn : r + q = n) (htot : r + s = tot)
    (hs : s ≤ q) (trs : List WordPairTree) :
    (∀ {d : ℕ} (g : PrimitiveGate d),
      (mottonenCascade q s hs (trs.take s)).count g +
        (mottonenCascade n r (by omega) (trs.drop s)).count g =
      (mottonenCascade n tot (by omega) trs).count g) ∧
    (mottonenCascade n r (by omega) (trs.drop s)).eval *
      (QRegister.block r q (by omega) : QRegister q n).embedUnitary
        (mottonenCascade q s hs (trs.take s)).eval =
    (mottonenCascade n tot (by omega) trs).eval := by
  subst hn
  subst htot
  exact mottonenCascade_split_gen r q s hs trs

/-- Multi-layer `mottonenCascade q s` along `rSub` commutes with `QubitisedWalk.qpeMuxUnitary F`
whenever
`rSub` is disjoint from `rSysMux` and targets `rSub ⟨0⟩ .. rSub ⟨s - 1⟩` lie outside `rCtrlMux`. -/
theorem mottonenCascade_comm_qpeMuxUnitary {bCtrl mSys q n : ℕ}
    (rCtrlMux : QRegister bCtrl n) (rSysMux : QRegister mSys n)
    (hMuxDisj : rCtrlMux.DisjointWires rSysMux)
    (F : Fin (2 ^ bCtrl) → Unitary (2 ^ mSys))
    (rSub : QRegister q n) (hSubSys : rSub.DisjointWires rSysMux) :
    ∀ (s : ℕ) (hs : s ≤ q)
      (_hTargetsOut : ∀ j (hj : j < s), rSub ⟨j, by omega⟩ ∉ rCtrlMux.image)
      (trs : List WordPairTree),
      rSub.embedUnitary (mottonenCascade q s hs trs).eval *
          (rCtrlMux.concat rSysMux hMuxDisj).embedUnitary (QubitisedWalk.qpeMuxUnitary F) =
        (rCtrlMux.concat rSysMux hMuxDisj).embedUnitary (QubitisedWalk.qpeMuxUnitary F) *
          rSub.embedUnitary (mottonenCascade q s hs trs).eval
  | 0, _, _, _ | _ + 1, _, _, [] => by simp [mottonenCascade]
  | s' + 1, hs, hTargetsOut, tr :: trs => by
      have ih := mottonenCascade_comm_qpeMuxUnitary rCtrlMux rSysMux hMuxDisj F rSub hSubSys
        s' (by omega) (fun j hj ↦ hTargetsOut j (by omega)) trs
      let k := q - (s' + 1)
      let rCtrlLoc : QRegister k q := QRegister.block (s' + 1) k (by omega)
      let tgtLoc : Wire q := ⟨s', by omega⟩
      have hDLoc : rCtrlLoc.DisjointWires (QRegister.singleton tgtLoc) := by
        rw [QRegister.disjoint_iff]
        intro i j hij
        have hv := congrArg Fin.val hij
        simp only [rCtrlLoc, tgtLoc, QRegister.block_apply_val, QRegister.singleton_apply] at hv
        omega
      have hDC : (rSub.compose rCtrlLoc).DisjointWires (QRegister.singleton (rSub tgtLoc)) := by
        rw [QRegister.disjoint_iff]
        intro i j hij
        exact hDLoc.ne i ⟨0, Nat.zero_lt_one⟩ (rSub.wires.injective
          (by simpa [QRegister.singleton_apply] using hij))
      have hEv : rSub.embedUnitary (wordPairTreeCircuit k rCtrlLoc tgtLoc hDLoc tr).eval =
          (wordPairTreeCircuit k (rSub.compose rCtrlLoc) (rSub tgtLoc) hDC tr).eval := by
        rw [← Circuit.eval_onRegister,
          wordPairTreeCircuit_onRegister rSub k rCtrlLoc tgtLoc hDLoc hDC tr]
      have hStep := (wordPairTreeCircuit_comm_qpeMuxUnitary rCtrlMux rSysMux hMuxDisj
        (rSub.compose rCtrlLoc) (rSub tgtLoc) hDC (hTargetsOut s' (Nat.lt_succ_self s'))
        (fun hm ↦ by obtain ⟨j, hj⟩ := (QRegister.mem_image _ _).mp hm
                     exact hSubSys.ne tgtLoc j hj.symm)
        (QubitisedWalk.disjointWires_compose_left hSubSys) tr F).symm
      dsimp only [mottonenCascade]
      rw [Circuit.eval_seq, QRegister.embedUnitary_mul, hEv, mul_assoc, hStep,
        ← mul_assoc, ih, mul_assoc]

/-! ## Section 2: `ThreeGearBondDeferSpec` & Certified Zero-Ancilla Window Instances -/

/-- Three-Gear Bond-Deferred Sine-Window specification (`StageC + StageM + StageF`) without
requiring `2 ^ m2 ∣ M + 1`. -/
structure ThreeGearBondDeferSpec (M m2 m1 nDirtyLo : ℕ) where
  base : TwoGearWindowSpec M m1 nDirtyLo
  hDC_lo : 2 ^ (16 - m2 - 1) ≤ mcSteps M m2
  hm12 : m1 ≤ m2
  hm2_14 : m2 ≤ 14
  cWinC : Circuit (nDirtyLo + (16 - m2))
  cWinM : Circuit (nDirtyLo + (16 - m1))
  cBond : Circuit (16 - m1 + 1)
  count_c_toff : cWinC.count .TOFF = 0
  count_m_toff : cWinM.count .TOFF = 0
  count_bond_toff : cBond.count .TOFF = 0
  count_split_t : cWinC.count .T + cWinM.count .T + cBond.count .T ≤ base.cWinHi.count .T
  eval_split_eq :
    (rBondHiInQPE16 m1 (le_trans (by decide : 1 ≤ 2) base.hmLow2)
        (le_trans base.hmLow14 (by decide))).embedUnitary cBond.eval *
      (rWinHiDeferInQPE m1 nDirtyLo (le_trans base.hmLow14 (by decide))
        (le_trans base.hDirty (Nat.sub_le m1 1))).embedUnitary cWinM.eval *
      (rWinHiDeferInQPE m2 nDirtyLo (by omega)
        (le_trans (le_trans base.hDirty (Nat.sub_le m1 1)) hm12)).embedUnitary cWinC.eval =
    (rWinHiInQPE m1 nDirtyLo (le_trans (by decide : 1 ≤ 2) base.hmLow2)
      (le_trans base.hmLow14 (by decide)) base.hDirty).embedUnitary base.cWinHi.eval
  comm_winM_phaseC : ∀ (mOut mMid : ℕ)
      (F : Fin (2 ^ (16 - m2)) → Unitary (2 ^ walkCatWidth 11 mOut mMid)),
    let rQPE := rQPEInAct 16 11 mOut mMid
    let rWC := rWalkCatInAct 16 11 mOut mMid
    let rHiC := rHiInQPE16 m2 (by omega)
    have hDisj : (rQPE.compose rHiC).DisjointWires rWC :=
      QubitisedWalk.disjointWires_compose_left (rQPEInAct_disjoint_rWalkCatInAct 16 11 mOut mMid)
    (rQPE.compose (rWinHiDeferInQPE m1 nDirtyLo (le_trans base.hmLow14 (by decide))
        (le_trans base.hDirty (Nat.sub_le m1 1)))).embedUnitary cWinM.eval *
      ((rQPE.compose rHiC).concat rWC hDisj).embedUnitary (QubitisedWalk.qpeMuxUnitary F) =
    ((rQPE.compose rHiC).concat rWC hDisj).embedUnitary (QubitisedWalk.qpeMuxUnitary F) *
      (rQPE.compose (rWinHiDeferInQPE m1 nDirtyLo (le_trans base.hmLow14 (by decide))
        (le_trans base.hDirty (Nat.sub_le m1 1)))).embedUnitary cWinM.eval
  comm_bond_mux : ∀ (bSub mOut mMid : ℕ) (rClock : QRegister bSub 16)
      (_hClockGe : ∀ j : Fin bSub, m1 ≤ (rClock j).val)
      (F : Fin (2 ^ bSub) → Unitary (2 ^ walkCatWidth 11 mOut mMid)),
    let rQPE := rQPEInAct 16 11 mOut mMid
    let rWC := rWalkCatInAct 16 11 mOut mMid
    have hDisj : (rQPE.compose rClock).DisjointWires rWC :=
      QubitisedWalk.disjointWires_compose_left (rQPEInAct_disjoint_rWalkCatInAct 16 11 mOut mMid)
    (rQPE.compose (rBondHiInQPE16 m1 (le_trans (by decide : 1 ≤ 2) base.hmLow2)
        (le_trans base.hmLow14 (by decide)))).embedUnitary cBond.eval *
      ((rQPE.compose rClock).concat rWC hDisj).embedUnitary (QubitisedWalk.qpeMuxUnitary F) =
    ((rQPE.compose rClock).concat rWC hDisj).embedUnitary (QubitisedWalk.qpeMuxUnitary F) *
      (rQPE.compose (rBondHiInQPE16 m1 (le_trans (by decide : 1 ≤ 2) base.hmLow2)
        (le_trans base.hmLow14 (by decide)))).embedUnitary cBond.eval

theorem concat_zero_compose_drop0 {k N : ℕ} (r0 : QRegister 0 N) (r : QRegister k N)
    (hd : r0.DisjointWires r) :
    (r0.concat r hd).compose (QRegister.block 0 k le_rfl : QRegister k (0 + k)) = r := by
  let rDrop0 : QRegister k (0 + k) := QRegister.block 0 k le_rfl
  change (r0.concat r hd).compose rDrop0 = r
  ext i
  obtain ⟨a | b, hab⟩ := finSumFinEquiv.surjective (rDrop0 i)
  · exact Fin.elim0 a
  · have hb : b = i := Fin.ext (by
      have hv := congrArg Fin.val hab
      simpa [rDrop0, QRegister.block_apply_val] using hv)
    rw [QRegister.compose_apply, ← hab, finSumFinEquiv_apply_right,
      QRegister.concat_apply_right, hb]

/-- Zero-extra-`T` Three-Gear Bond-Deferred window builder from any certified `TwoGearRegimeData`
record `d` (fine cut `m1 = d.mLow`) and any coarse cut `d.mLow ≤ m2 ≤ 14` with `2 ^ 15 ≤ d.M`. -/
noncomputable def mkThreeGearBondDeferSpec_zeroAnc (d : TwoGearRegimeData) (m2 : ℕ)
    (hok : checkTwoGearRegime d = true)
    (hm12 : d.mLow ≤ m2 := by decide)
    (hm2_14 : m2 ≤ 14 := by decide)
    (hM15 : 2 ^ 15 ≤ d.M := by decide) :
    ThreeGearBondDeferSpec d.M m2 d.mLow 0 :=
  let hmeta := checkTwoGearRegime_meta d hok
  let hdiv1 : 2 ^ d.mLow ∣ d.M + 1 := hmeta.1
  let _hm2_lo : 2 ≤ d.mLow := hmeta.2.2.2.1
  let _hm14 : d.mLow ≤ 14 := hmeta.2.2.2.2
  let hDlo1 : 2 ^ (16 - d.mLow - 1) ≤ (d.M + 1) / 2 ^ d.mLow - 1 := by
    have hadd := two_pow_15_add_le_of_dvd (by omega : d.mLow ≤ 15) hM15 hdiv1
    have hpow : 2 ^ (16 - d.mLow - 1) * 2 ^ d.mLow = 2 ^ 15 := by
      rw [← pow_add]
      congr 1
      omega
    have hle : 2 ^ (16 - d.mLow - 1) + 1 ≤ (d.M + 1) / 2 ^ d.mLow :=
      (Nat.le_div_iff_mul_le (Nat.two_pow_pos d.mLow)).mpr (by nlinarith)
    omega
  let hDC_lo : 2 ^ (16 - m2 - 1) ≤ mcSteps d.M m2 := by
    have hpow : 2 ^ (16 - m2 - 1) * 2 ^ m2 = 2 ^ 15 := by
      rw [← pow_add]
      congr 1
      omega
    exact (Nat.le_div_iff_mul_le (Nat.two_pow_pos m2)).mpr (by linarith)
  let w2 := mkTwoGearBondDeferSpec_zeroAnc d hok hDlo1
  let n := 16 - d.mLow
  let qC := 16 - m2
  let rM := m2 - d.mLow
  let topTrees := d.hiTrees.take n
  let hSplit := mottonenCascade_split_of_eq n rM qC qC n (by omega) (by omega) le_rfl topTrees
  let cC0 : Circuit qC := mottonenCascade qC qC le_rfl (topTrees.take qC)
  let cWinC : Circuit (0 + qC) := cC0.onRegister (QRegister.block 0 qC le_rfl)
  let cM0 : Circuit n := mottonenCascade n rM (by omega) (topTrees.drop qC)
  let cWinM : Circuit (0 + n) := cM0.onRegister (QRegister.block 0 n le_rfl)
  have hTopCnt {dg : ℕ} (g : PrimitiveGate dg) :
      cWinC.count g + cWinM.count g = w2.cHiPre.count g := by
    dsimp only [cWinC, cC0, cWinM, cM0, w2, mkTwoGearBondDeferSpec_zeroAnc, n, topTrees]
    rw [Circuit.count_onRegister, Circuit.count_onRegister, Circuit.count_onRegister]
    exact hSplit.1 g
  { base := w2.base, hDC_lo, hm12, hm2_14, cWinC, cWinM, cBond := w2.cHiBond
    count_c_toff := by
      have h1 := hTopCnt .TOFF
      have h2 := w2.count_pre_toff
      omega
    count_m_toff := by
      have h1 := hTopCnt .TOFF
      have h2 := w2.count_pre_toff
      omega
    count_bond_toff := w2.count_bond_toff
    count_split_t := by rw [hTopCnt .T, w2.count_split_t]
    eval_split_eq := by
      have hEvalMC :
          (rWinHiDeferInQPE d.mLow 0 (by omega) (Nat.zero_le _)).embedUnitary cWinM.eval *
            (rWinHiDeferInQPE m2 0 (by omega) (Nat.zero_le _)).embedUnitary cWinC.eval =
          (rWinHiDeferInQPE d.mLow 0 (by omega) (Nat.zero_le _)).embedUnitary w2.cHiPre.eval := by
        let rM16 : QRegister n 16 := QRegister.block d.mLow n (by omega)
        have hrM : (rWinHiDeferInQPE d.mLow 0 (by omega) (Nat.zero_le _)).compose
            (QRegister.block 0 n le_rfl) = rM16 := concat_zero_compose_drop0 _ _ _
        have hrC : (rWinHiDeferInQPE m2 0 (by omega) (Nat.zero_le _)).compose
            (QRegister.block 0 qC le_rfl) = rM16.compose (QRegister.block rM qC (by omega)) := by
          dsimp only [rWinHiDeferInQPE, rHiInQPE16]
          rw [concat_zero_compose_drop0]
          dsimp only [rM16, rM]
          ext i
          simp only [QRegister.compose_apply, QRegister.block_apply_val]
          omega
        have hrPre : (rWinHiDeferInQPE d.mLow 0 (by omega) (Nat.zero_le _)).embedUnitary
            w2.cHiPre.eval = rM16.embedUnitary (mottonenCascade n n le_rfl topTrees).eval := by
          dsimp only [w2, mkTwoGearBondDeferSpec_zeroAnc]
          rw [Circuit.eval_onRegister, ← QRegister.embedUnitary_compose, hrM]
        dsimp only [cWinM, cM0, cWinC, cC0]
        rw [Circuit.eval_onRegister, Circuit.eval_onRegister, ← QRegister.embedUnitary_compose,
          ← QRegister.embedUnitary_compose, hrM, hrC, hrPre, QRegister.embedUnitary_compose,
          ← QRegister.embedUnitary_mul]
        exact congrArg rM16.embedUnitary hSplit.2
      rw [mul_assoc, hEvalMC]
      exact w2.eval_split
    comm_winM_phaseC := fun mOut mMid F ↦ by
      intro rQPE rWC rHiC hDisj
      let rM16 : QRegister n 16 := QRegister.block d.mLow n (by omega)
      have hrM : (rWinHiDeferInQPE d.mLow 0 (by omega) (Nat.zero_le _)).compose
          (QRegister.block 0 n le_rfl) = rM16 := concat_zero_compose_drop0 _ _ _
      dsimp only [cWinM, cM0]
      rw [Circuit.eval_onRegister, ← QRegister.embedUnitary_compose, QRegister.compose_assoc, hrM]
      refine mottonenCascade_comm_qpeMuxUnitary (rQPE.compose rHiC) rWC hDisj F
        (rQPE.compose rM16) (QubitisedWalk.disjointWires_compose_left
          (rQPEInAct_disjoint_rWalkCatInAct 16 11 mOut mMid)) rM (by omega) (fun j hj hm ↦ ?_)
        (topTrees.drop qC)
      obtain ⟨ic, hic⟩ := (QRegister.mem_image _ _).mp hm
      have hv := congrArg Fin.val (rQPE.wires.injective hic)
      simp only [rHiC, rHiInQPE16, rM16, QRegister.block_apply_val] at hv
      omega
    comm_bond_mux := fun bSub mOut mMid rClock hClockGe F ↦ by
      intro rQPE rWC hDisj
      let rPlace := rQPE.compose (rBondHiInQPE16 d.mLow (by omega) (by omega))
      have htCtrl : rPlace ⟨0, by omega⟩ ∉ (rQPE.compose rClock).image := fun hm ↦ by
        obtain ⟨j, hj⟩ := (QRegister.mem_image _ _).mp hm
        have hv := congrArg Fin.val (rQPE.wires.injective hj)
        have hge := hClockGe j
        simp only [rBondHiInQPE16, QRegister.block_apply_val] at hv
        omega
      have htTgt : rPlace ⟨0, by omega⟩ ∉ rWC.image := fun hm ↦ by
        obtain ⟨j, hj⟩ := (QRegister.mem_image _ _).mp hm
        have hjlt := j.isLt
        have hv := congrArg Fin.val hj
        simp only [rPlace, rWC, rWalkCatInAct, rQPE, rQPEInAct, rBondHiInQPE16,
          QRegister.compose_apply, QRegister.block_apply_val] at hv
        omega
      exact (mottonenCascade_one_comm_qpeMuxUnitary (rQPE.compose rClock) rWC hDisj rPlace
        htCtrl htTgt (QubitisedWalk.disjointWires_compose_left
          (QubitisedWalk.disjointWires_compose_left
          (rQPEInAct_disjoint_rWalkCatInAct 16 11 mOut mMid))) (d.hiTrees.drop n) F).symm }

/-- Computable circuit-only projection of `ThreeGearBondDeferSpec` (`0` `Unitary` / `ℝ` fields). -/
structure ThreeGearWindowCirc (m2 m1 nDirtyLo : ℕ) where
  /-- Coarse-vs-fine cut ordering `m1 ≤ m2`. -/
  hm12 : m1 ≤ m2
  /-- Coarse cut upper bound `m2 ≤ 14`. -/
  hm2_14 : m2 ≤ 14
  /-- Coarse window preparation circuit on `nDirtyLo + (16 - m2)` wires. -/
  cWinC : Circuit (nDirtyLo + (16 - m2))
  /-- Middle window preparation circuit on `nDirtyLo + (16 - m1)` wires. -/
  cWinM : Circuit (nDirtyLo + (16 - m1))
  /-- Deferred bond preparation circuit on `16 - m1 + 1` wires. -/
  cBond : Circuit (16 - m1 + 1)
  /-- Fine low-gear window preparation circuit on `m1` wires. -/
  cWinLo : Circuit m1

/-- Projects `w : ThreeGearBondDeferSpec M m2 m1 nDirtyLo` to `ThreeGearWindowCirc`. -/
def ThreeGearBondDeferSpec.toCirc {M m2 m1 nDirtyLo : ℕ}
    (w : ThreeGearBondDeferSpec M m2 m1 nDirtyLo) : ThreeGearWindowCirc m2 m1 nDirtyLo where
  hm12 := w.hm12
  hm2_14 := w.hm2_14
  cWinC := w.cWinC
  cWinM := w.cWinM
  cBond := w.cBond
  cWinLo := w.base.cWinLo

/-- Computable zero-ancilla `ThreeGearWindowCirc` built directly from `d : TwoGearRegimeData`. -/
def mkThreeGearWindowCirc_zeroAnc (d : TwoGearRegimeData) (m2 : ℕ)
    (hm1 : 1 ≤ d.mLow := by decide)
    (hm12 : d.mLow ≤ m2 := by decide)
    (hm2_14 : m2 ≤ 14 := by decide) :
    ThreeGearWindowCirc m2 d.mLow 0 :=
  let n := 16 - d.mLow
  let qC := 16 - m2
  let rM := m2 - d.mLow
  let topTrees := d.hiTrees.take n
  let cC0 : Circuit qC := mottonenCascade qC qC le_rfl (topTrees.take qC)
  let cM0 : Circuit n := mottonenCascade n rM (by omega) (topTrees.drop qC)
  { hm12 := hm12
    hm2_14 := hm2_14
    cWinC := cC0.onRegister (QRegister.block 0 qC le_rfl)
    cWinM := cM0.onRegister (QRegister.block 0 n le_rfl)
    cBond := mottonenCascade (n + 1) 1 (by omega) (d.hiTrees.drop n)
    cWinLo := twoGearZeroAncLo d hm1 }

/-! ### Exact Affine-Fold All-Ones Tail-Wraparound Identities (`m2 ∈ {10, 9}`) -/

/-- Exact `affineFoldVal 5 13 45 = 63` wraparound identity (`m2 = 10`, `nStd = 44`). -/
theorem affineFoldVal_5_13_45_eq_63 : affineFoldVal 5 13 45 = 63 := by decide

theorem affineFoldVal_5_13_lt_63_of_le_44 (q : Fin 64) (hq : q.val ≤ 44) :
    affineFoldVal 5 13 q.val < 63 := by
  revert hq
  revert q
  decide

/-! ## Section 3: Unified `(bGear, mCut)` Relocation & Three-Gear Programs -/

theorem scrAncillas_gearDefer_le (bGear aRem mRem mCut nDirtyLo sRem sUbGear : ℕ)
    (hb16 : bGear ≤ 16) (hsUb : sUbGear ≤ sRem + (mCut - nDirtyLo)) :
    scrAncillas bGear 0 aRem mRem sUbGear ≤
      scrAncillas 16 0 aRem mRem sRem + (mCut - nDirtyLo) := by
  dsimp [scrAncillas, chunkedCtrlScrNeed]
  omega

theorem hbScr_gearDefer (bGear wOuter wInner2 ko km sUbGear : ℕ)
    (hkOut : ko ≤ wOuter) (hkMid : km ≤ wInner2) (hb16 : bGear ≤ 16) :
    bGear - 2 ≤
      scrAncillas bGear 0 (combARem wOuter wInner2 ko km) (midRemWidth wInner2 km) sUbGear := by
  have h1 : 15 ≤ combARem wOuter wInner2 ko km := by
    dsimp [combARem, outRemWidth, midRemWidth, blockRemWidth, mOutUB, mMidUB]
    omega
  have h2 := scr_ge_lowCtrl bGear 0 (combARem wOuter wInner2 ko km) (midRemWidth wInner2 km) sUbGear
  omega

/-- Wire relocation map embedding `combQubitsAt bGear ... sUbGear` into `combQubitsB`. -/
def rGearDeferInBVal (bGear mCut wOuter wInner2 ko km nDirtyLo sRem i : ℕ) : ℕ :=
  let mOut := mOutUB wOuter
  let mMid := mMidUB wInner2
  let aRem := combARem wOuter wInner2 ko km
  let mRem := midRemWidth wInner2 km
  if i < walkCatWidth 11 mOut mMid then i
  else if i < walkCatWidth 11 mOut mMid + bGear then i + mCut
  else
    let j := i - actWidth bGear 11 mOut mMid
    if j < scrAncillas 16 0 aRem mRem sRem then actWidth 16 11 mOut mMid + j
    else walkCatWidth 11 mOut mMid + nDirtyLo + (j - scrAncillas 16 0 aRem mRem sRem)

theorem rGearDeferInBVal_lt_and_inj {bGear mCut wOuter wInner2 ko km nDirtyLo sRem sUbGear : ℕ}
    (hbCut : mCut + bGear ≤ 16) (hDirty : nDirtyLo ≤ mCut)
    (hsUb : sUbGear ≤ sRem + (mCut - nDirtyLo)) :
    (∀ {i}, i < combQubitsAt bGear wOuter wInner2 ko km 0 sUbGear →
      rGearDeferInBVal bGear mCut wOuter wInner2 ko km nDirtyLo sRem i <
        combQubitsB wOuter wInner2 ko km sRem) ∧
    (∀ {i j}, i < combQubitsAt bGear wOuter wInner2 ko km 0 sUbGear →
      j < combQubitsAt bGear wOuter wInner2 ko km 0 sUbGear →
      rGearDeferInBVal bGear mCut wOuter wInner2 ko km nDirtyLo sRem i =
        rGearDeferInBVal bGear mCut wOuter wInner2 ko km nDirtyLo sRem j → i = j) := by
  let mOut := mOutUB wOuter
  let mMid := mMidUB wInner2
  let aRem := combARem wOuter wInner2 ko km
  let mRem := midRemWidth wInner2 km
  have hactG := actWidth_eq bGear 11 mOut mMid
  have hactB := actWidth_eq 16 11 mOut mMid
  have hscr := scrAncillas_gearDefer_le bGear aRem mRem mCut nDirtyLo sRem sUbGear
    (by omega) hsUb
  have hUnf {k} (hk : k < combQubitsAt bGear wOuter wInner2 ko km 0 sUbGear) :
      k < actWidth bGear 11 mOut mMid + scrAncillas bGear 0 aRem mRem sUbGear := by
    dsimp [combQubitsAt, cat11TotalQubits, totalQubits, totalAncillas, actWidth,
      mOut, mMid, aRem, mRem] at hk ⊢
    omega
  refine ⟨fun {i} hi ↦ ?_, fun {i j} hi hj hij ↦ ?_⟩
  · have hi' := hUnf hi
    suffices hlt : rGearDeferInBVal bGear mCut wOuter wInner2 ko km nDirtyLo sRem i <
        actWidth 16 11 mOut mMid + scrAncillas 16 0 aRem mRem sRem by
      dsimp [combQubitsB, combQubits, cat11TotalQubits, totalQubits, totalAncillas,
        actWidth, mOut, mMid, aRem, mRem] at hlt ⊢
      omega
    dsimp only [mOut, mMid, aRem, mRem] at hactG hactB hscr hi' ⊢
    dsimp only [rGearDeferInBVal]
    split_ifs <;> omega
  · have hi' := hUnf hi
    have hj' := hUnf hj
    dsimp only [mOut, mMid, aRem, mRem] at hactG hactB hscr hi' hj'
    dsimp only [rGearDeferInBVal] at hij
    split_ifs at hij <;> omega

/-- Embedding of `combQubitsAt bGear ... sUbGear` into `combQubitsB`. -/
def rGearDeferInB (bGear mCut wOuter wInner2 ko km nDirtyLo sRem sUbGear : ℕ)
    (hbCut : mCut + bGear ≤ 16) (hDirty : nDirtyLo ≤ mCut)
    (hsUb : sUbGear ≤ sRem + (mCut - nDirtyLo)) :
    QRegister (combQubitsAt bGear wOuter wInner2 ko km 0 sUbGear)
      (combQubitsB wOuter wInner2 ko km sRem) where
  wires := { toFun := fun i ↦ ⟨rGearDeferInBVal bGear mCut wOuter wInner2 ko km nDirtyLo sRem i.val,
               (rGearDeferInBVal_lt_and_inj hbCut hDirty hsUb).1 i.isLt⟩
             inj' := fun i j h ↦ Fin.ext ((rGearDeferInBVal_lt_and_inj hbCut hDirty hsUb).2
               i.isLt j.isLt (congrArg Fin.val h)) }

@[simp] theorem rGearDeferInB_apply_val (bGear mCut wOuter wInner2 ko km nDirtyLo sRem sUbGear : ℕ)
    (hbCut : mCut + bGear ≤ 16) (hDirty : nDirtyLo ≤ mCut)
    (hsUb : sUbGear ≤ sRem + (mCut - nDirtyLo))
    (i : Fin (combQubitsAt bGear wOuter wInner2 ko km 0 sUbGear)) :
    (rGearDeferInB bGear mCut wOuter wInner2 ko km nDirtyLo sRem sUbGear hbCut hDirty hsUb i).val =
      rGearDeferInBVal bGear mCut wOuter wInner2 ko km nDirtyLo sRem i.val := rfl

/-- Sub-register `(mCut .. mCut + bGear - 1) ++ WalkCat` inside `actWidth 16 11 mOut mMid`. -/
abbrev rCombSubInAct (mOut mMid mCut bGear : ℕ) (hbCut : mCut + bGear ≤ 16) :
    QRegister (bGear + walkCatWidth 11 mOut mMid) (actWidth 16 11 mOut mMid) :=
  ((rQPEInAct 16 11 mOut mMid).compose (QRegister.block mCut bGear hbCut)).concat
    (rWalkCatInAct 16 11 mOut mMid)
    (QubitisedWalk.disjointWires_compose_left (rQPEInAct_disjoint_rWalkCatInAct 16 11 mOut mMid))

theorem rGearDeferInB_compose_rCombGear (bGear mCut wOuter wInner2 ko km nDirtyLo sRem sUbGear : ℕ)
    (hbCut : mCut + bGear ≤ 16) (hDirty : nDirtyLo ≤ mCut)
    (hsUb : sUbGear ≤ sRem + (mCut - nDirtyLo)) :
    let mOut := mOutUB wOuter
    let mMid := mMidUB wInner2
    let aRem := combARem wOuter wInner2 ko km
    let mRem := midRemWidth wInner2 km
    (rGearDeferInB bGear mCut wOuter wInner2 ko km nDirtyLo sRem sUbGear hbCut hDirty hsUb).compose
      ((rQPELoc bGear 11 mOut mMid 0 aRem mRem sUbGear).concat
        (rWalkCatLoc bGear 11 mOut mMid 0 aRem mRem sUbGear)
        (rQPELoc_disjoint_rWalkCatLoc bGear 11 mOut mMid 0 aRem mRem sUbGear)) =
    (rActLoc 16 11 mOut mMid 0 aRem mRem sRem).compose
      (rCombSubInAct mOut mMid mCut bGear hbCut) := by
  intro mOut mMid aRem mRem
  ext idx
  rcases finSumFinEquiv.surjective idx with ⟨ih | iw, rfl⟩
  · have hlt : ¬ (walkCatWidth 11 mOut mMid + ih.val < walkCatWidth 11 mOut mMid) := by omega
    have hlt2 : walkCatWidth 11 mOut mMid + ih.val < walkCatWidth 11 mOut mMid + bGear := by
      omega
    simp only [QRegister.compose_apply, finSumFinEquiv_apply_left, QRegister.concat_apply_left,
      rGearDeferInB_apply_val, rQPELoc, rActLoc, rCombSubInAct, rQPEInAct,
      QRegister.block_apply_val, zero_add]
    dsimp only [rGearDeferInBVal, mOut, mMid] at hlt hlt2 ⊢
    rw [ite_eq_right hlt, ite_eq_left hlt2]
    omega
  · have hlt : iw.val < walkCatWidth 11 mOut mMid := iw.isLt
    simp only [QRegister.compose_apply, finSumFinEquiv_apply_right, QRegister.concat_apply_right,
      rGearDeferInB_apply_val, rWalkCatLoc, rActLoc, rCombSubInAct, rWalkCatInAct,
      QRegister.block_apply_val, zero_add]
    dsimp only [rGearDeferInBVal, mOut, mMid] at hlt ⊢
    exact ite_eq_left hlt

theorem rGearDeferInB_rFullZero_subset_and_disjoint
    (bGear mCut wOuter wInner2 ko km nDirtyLo sRem sUbGear : ℕ) (hkOut : ko ≤ wOuter) (hkMid : km ≤
      wInner2)
    (hmCut14 : mCut ≤ 14) (hbCut : mCut + bGear ≤ 16) (hDirty : nDirtyLo ≤ mCut)
    (hsUb : sUbGear ≤ sRem + (mCut - nDirtyLo)) :
    let mOut := mOutUB wOuter
    let mMid := mMidUB wInner2
    let aRem := combARem wOuter wInner2 ko km
    let mRem := midRemWidth wInner2 km
    let rAncZ := liftOutMidZeroToAnc mOut mMid
      (outZeroPrefixReg wOuter ko hkOut) (midZeroPrefixReg wInner2 km hkMid)
    let rScr₁ := (rGearDeferInB bGear mCut wOuter wInner2 ko km nDirtyLo sRem sUbGear hbCut hDirty
      hsUb).compose (rFullZeroLoc bGear 11 mOut mMid 0 aRem mRem sUbGear rAncZ)
    let rExt := rExtZeroDeferLocB wOuter wInner2 ko km mCut nDirtyLo sRem hkOut hkMid hmCut14 hDirty
    rScr₁.image ⊆ rExt.image ∧ Disjoint (((rActLoc 16 11 mOut mMid 0 aRem mRem sRem).compose
        (rCombSubInAct mOut mMid mCut bGear hbCut)).image) (rExt.image \ rScr₁.image) := by
  intro mOut mMid aRem mRem rAncZ rScr₁ rExt
  have hactG := actWidth_eq bGear 11 mOut mMid
  have hactB := actWidth_eq 16 11 mOut mMid
  have hscr_le := scrAncillas_gearDefer_le bGear aRem mRem mCut nDirtyLo sRem sUbGear
    (by omega) hsUb
  have hAncMap (ia : Fin (ko + km)) :
      rGearDeferInB bGear mCut wOuter wInner2 ko km nDirtyLo sRem sUbGear hbCut hDirty hsUb
        (rAncZeroLoc bGear 11 mOut mMid 0 aRem mRem sUbGear rAncZ ia) =
      rAncZeroLoc 16 11 mOut mMid 0 aRem mRem sRem rAncZ ia := by
    apply Fin.ext
    have hlt_wc : (rAncZeroLoc bGear 11 mOut mMid 0 aRem mRem sUbGear rAncZ ia).val <
        walkCatWidth 11 mOut mMid :=
      (rAncZeroLoc_val_bounds bGear 11 mOut mMid 0 aRem mRem sUbGear rAncZ ia).2.trans_le
        (by
          dsimp [walkCatWidth]
          omega)
    simp only [rGearDeferInB_apply_val]
    dsimp only [rGearDeferInBVal]
    dsimp only [mOut, mMid] at hlt_wc ⊢
    rw [ite_eq_left hlt_wc]
    simp only [rAncZeroLoc, rWalkCatLoc, rActLoc, rWalkCatInAct, QRegister.compose_apply,
      QRegister.block_apply_val, zero_add]
  refine ⟨fun q hq ↦ ?_, Finset.disjoint_left.mpr fun q hqAct hqDiff ↦ ?_⟩
  · obtain ⟨idx, rfl⟩ := (QRegister.mem_image _ _).mp hq
    let wG := rFullZeroLoc bGear 11 mOut mMid 0 aRem mRem sUbGear rAncZ idx
    have hwG : wG ∈ (rFullZeroLoc bGear 11 mOut mMid 0 aRem mRem sUbGear rAncZ).image :=
      (QRegister.mem_image _ _).mpr ⟨idx, rfl⟩
    rw [image_rFullZeroLoc, Finset.mem_union] at hwG
    rcases hwG with hscr | hanc
    · obtain ⟨is, his⟩ := (QRegister.mem_image _ _).mp hscr
      have his_val : wG.val = actWidth bGear 11 mOut mMid + is.val := by
        rw [← his]
        simp only [rScrLoc, QRegister.block_apply_val]
      have hnot1 : ¬ (wG.val < walkCatWidth 11 mOut mMid) := by omega
      have hnot2 : ¬ (wG.val < walkCatWidth 11 mOut mMid + bGear) := by omega
      have hsub_val : wG.val - actWidth bGear 11 (mOutUB wOuter) (mMidUB wInner2) = is.val := by
        dsimp only [mOut, mMid] at his_val
        omega
      by_cases hltB : is.val < scrAncillas 16 0 aRem mRem sRem
      · have hmem_scrB : rScrLoc 16 11 mOut mMid 0 aRem mRem sRem ⟨is.val, hltB⟩ ∈
            (rFullZeroLocB wOuter wInner2 ko km sRem hkOut hkMid).image := by
          rw [rFullZeroLocB, image_rFullZeroLoc, Finset.mem_union]
          exact Or.inl ((QRegister.mem_image _ _).mpr ⟨_, rfl⟩)
        obtain ⟨ifull, hifull⟩ := (QRegister.mem_image _ _).mp hmem_scrB
        refine (QRegister.mem_image _ _).mpr ⟨Fin.castAdd _ ifull, ?_⟩
        dsimp only [rExt, rExtZeroDeferLocB, rExtZeroLocB]
        rw [QRegister.concat_apply_left, hifull]
        apply Fin.ext
        simp only [rScrLoc, QRegister.block_apply_val, rScr₁,
          QRegister.compose_apply, rGearDeferInB_apply_val]
        dsimp only [rGearDeferInBVal]
        dsimp only [mOut, mMid, aRem, mRem] at hnot1 hnot2 hltB ⊢
        rw [ite_eq_right hnot1, ite_eq_right hnot2, hsub_val, ite_eq_left hltB]
      · have his_lt := is.isLt
        refine (QRegister.mem_image _ _).mpr
          ⟨Fin.natAdd _ ⟨is.val - scrAncillas 16 0 aRem mRem sRem, by omega⟩, ?_⟩
        dsimp only [rExt, rExtZeroDeferLocB, rExtZeroLocB]
        rw [QRegister.concat_apply_right]
        apply Fin.ext
        simp only [rBorrowLocB, rQPELoc, rActLoc, rQPEInAct, rBorrowInQPE16, rScr₁,
          QRegister.compose_apply, QRegister.block_apply_val, zero_add, rGearDeferInB_apply_val]
        dsimp only [rGearDeferInBVal]
        dsimp only [mOut, mMid, aRem, mRem] at hnot1 hnot2 hltB ⊢
        rw [ite_eq_right hnot1, ite_eq_right hnot2, hsub_val, ite_eq_right hltB]
        omega
    · obtain ⟨ia, hia⟩ := (QRegister.mem_image _ _).mp hanc
      have hmem_ancB : rAncZeroLoc 16 11 mOut mMid 0 aRem mRem sRem rAncZ ia ∈
          (rFullZeroLocB wOuter wInner2 ko km sRem hkOut hkMid).image := by
        rw [rFullZeroLocB, image_rFullZeroLoc, Finset.mem_union]
        exact Or.inr ((QRegister.mem_image _ _).mpr ⟨ia, rfl⟩)
      obtain ⟨ifull, hifull⟩ := (QRegister.mem_image _ _).mp hmem_ancB
      refine (QRegister.mem_image _ _).mpr ⟨Fin.castAdd _ ifull, ?_⟩
      dsimp only [rExt, rExtZeroDeferLocB, rExtZeroLocB]
      rw [QRegister.concat_apply_left, hifull]
      exact (hAncMap ia).symm.trans (congrArg
        (rGearDeferInB bGear mCut wOuter wInner2 ko km nDirtyLo sRem sUbGear hbCut hDirty
          hsUb).wires hia)
  · obtain ⟨hqExt, hqNotG⟩ := Finset.mem_sdiff.mp hqDiff
    have hqAct_range : q.val < walkCatWidth 11 mOut mMid ∨
        (walkCatWidth 11 mOut mMid + mCut ≤ q.val ∧
          q.val < walkCatWidth 11 mOut mMid + 16) := by
      obtain ⟨idx, rfl⟩ := (QRegister.mem_image _ _).mp hqAct
      rcases finSumFinEquiv.surjective idx with ⟨ih | iw, rfl⟩
      · right
        have := ih.isLt
        simp only [QRegister.compose_apply, finSumFinEquiv_apply_left,
          rCombSubInAct, QRegister.concat_apply_left, rActLoc, rQPEInAct,
          QRegister.block_apply_val, zero_add]
        omega
      · left
        have := iw.isLt
        simp only [QRegister.compose_apply, finSumFinEquiv_apply_right,
          rCombSubInAct, QRegister.concat_apply_right, rActLoc, rWalkCatInAct,
          QRegister.block_apply_val, zero_add]
        omega
    obtain ⟨iext, rfl⟩ := (QRegister.mem_image _ _).mp hqExt
    rcases finSumFinEquiv.surjective iext with ⟨ifull | ibor, rfl⟩
    · simp only [finSumFinEquiv_apply_left, rExt, rExtZeroDeferLocB, rExtZeroLocB,
        QRegister.concat_apply_left] at hqAct_range hqNotG
      have hmem : rFullZeroLocB wOuter wInner2 ko km sRem hkOut hkMid ifull ∈
          (rFullZeroLoc 16 11 mOut mMid 0 aRem mRem sRem rAncZ).image :=
        (QRegister.mem_image _ _).mpr ⟨ifull, rfl⟩
      rw [image_rFullZeroLoc, Finset.mem_union] at hmem
      rcases hmem with hscrB | hancB
      · obtain ⟨is, his⟩ := (QRegister.mem_image _ _).mp hscrB
        have hge : actWidth 16 11 mOut mMid ≤
            (rFullZeroLocB wOuter wInner2 ko km sRem hkOut hkMid ifull).val := by
          rw [← his]
          simp only [rScrLoc, QRegister.block_apply_val]
          omega
        omega
      · obtain ⟨ia, hia⟩ := (QRegister.mem_image _ _).mp hancB
        apply hqNotG
        have hmemG : rAncZeroLoc bGear 11 mOut mMid 0 aRem mRem sUbGear rAncZ ia ∈
            (rFullZeroLoc bGear 11 mOut mMid 0 aRem mRem sUbGear rAncZ).image := by
          rw [image_rFullZeroLoc, Finset.mem_union]
          exact Or.inr ((QRegister.mem_image _ _).mpr ⟨ia, rfl⟩)
        obtain ⟨idxG, hidxG⟩ := (QRegister.mem_image _ _).mp hmemG
        exact (QRegister.mem_image _ _).mpr ⟨idxG, by
          dsimp only [rScr₁]
          rw [QRegister.compose_apply, hidxG, hAncMap ia]
          exact hia⟩
    · have := ibor.isLt
      simp only [finSumFinEquiv_apply_right, rExt, rExtZeroDeferLocB, rExtZeroLocB,
        QRegister.concat_apply_right, rBorrowLocB, rQPELoc, rActLoc, rQPEInAct, rBorrowInQPE16,
        QRegister.compose_apply, QRegister.block_apply_val, zero_add] at hqAct_range
      dsimp only [mOut, mMid] at hqAct_range
      omega

/-- Relocates `CleanRealizes` for a `(bGear, mCut)` multiplexed gear onto `rExtZeroDeferLocB`. -/
theorem cleanRealizes_gearDefer_relocated {Var : Type} [Fintype Var] [DecidableEq Var]
    (bGear mCut wOuter wInner2 ko km nDirtyLo sRem sUbGear : ℕ)
    (hkOut : ko ≤ wOuter) (hkMid : km ≤ wInner2) (hmCut14 : mCut ≤ 14) (hbCut : mCut + bGear ≤ 16)
    (hDirty : nDirtyLo ≤ mCut) (hsUb : sUbGear ≤ sRem + (mCut - nDirtyLo)) (v : Var)
    {uMux : Unitary (2 ^ (bGear + walkCatWidth 11 (mOutUB wOuter) (mMidUB wInner2)))}
    {pGear : DynamicCircuit Var (combQubitsAt bGear wOuter wInner2 ko km 0 sUbGear)} (hGear :
      let mOut := mOutUB wOuter
      let mMid := mMidUB wInner2
      let aRem := combARem wOuter wInner2 ko km
      let mRem := midRemWidth wInner2 km
      XMeasCircuit.CleanRealizes v ((rQPELoc bGear 11 mOut mMid 0 aRem mRem sUbGear).concat
          (rWalkCatLoc bGear 11 mOut mMid 0 aRem mRem sUbGear)
          (rQPELoc_disjoint_rWalkCatLoc bGear 11 mOut mMid 0 aRem mRem sUbGear))
        (rFullZeroLoc bGear 11 mOut mMid 0 aRem mRem sUbGear
          (liftOutMidZeroToAnc mOut mMid (outZeroPrefixReg wOuter ko hkOut)
            (midZeroPrefixReg wInner2 km hkMid))) uMux pGear) :
    let mOut := mOutUB wOuter
    let mMid := mMidUB wInner2
    let aRem := combARem wOuter wInner2 ko km
    let mRem := midRemWidth wInner2 km
    XMeasCircuit.CleanRealizes v (rActLoc 16 11 mOut mMid 0 aRem mRem sRem)
      (rExtZeroDeferLocB wOuter wInner2 ko km mCut nDirtyLo sRem hkOut hkMid hmCut14 hDirty)
      ((rCombSubInAct mOut mMid mCut bGear hbCut).embedUnitary uMux)
      (pGear.onRegister
        (rGearDeferInB bGear mCut wOuter wInner2 ko km nDirtyLo sRem sUbGear hbCut hDirty
          hsUb)) := by
  intro mOut mMid aRem mRem
  let emb := rGearDeferInB bGear mCut wOuter wInner2 ko km nDirtyLo sRem sUbGear hbCut hDirty hsUb
  have hLift : XMeasCircuit.CleanRealizes v (rActLoc 16 11 mOut mMid 0 aRem mRem sRem) _
      ((rCombSubInAct mOut mMid mCut bGear hbCut).embedUnitary uMux) (pGear.onRegister emb) :=
    XMeasCircuit.CleanRealizes.liftActiveOfEq
      (rGearDeferInB_compose_rCombGear bGear mCut wOuter wInner2 ko km nDirtyLo sRem sUbGear
        hbCut hDirty hsUb) (CleanDyn.CleanRealizes.onRegister emb hGear)
  obtain ⟨hsub, hDisjDiff⟩ := rGearDeferInB_rFullZero_subset_and_disjoint bGear mCut wOuter wInner2
    ko km nDirtyLo sRem sUbGear hkOut hkMid hmCut14 hbCut hDirty hsUb
  refine XMeasCircuit.CleanRealizes.absorbCleanActive hLift hsub rfl ?_
  let rScr₁ := emb.compose (rFullZeroLoc bGear 11 mOut mMid 0 aRem mRem sUbGear
    (liftOutMidZeroToAnc mOut mMid (outZeroPrefixReg wOuter ko hkOut) (midZeroPrefixReg wInner2 km
      hkMid)))
  let rExt := rExtZeroDeferLocB wOuter wInner2 ko km mCut nDirtyLo sRem hkOut hkMid hmCut14 hDirty
  let Sdiff := rExt.image \ rScr₁.image
  let rDiff := qregOfFinset Sdiff
  have hPres₁ := cleanRealizes_preserves_zeroProj hLift
  change rScr₁.basisOutcomeProjector 0 * _ = _ at hPres₁
  have hPext : rExt.basisOutcomeProjector 0 =
      rDiff.basisOutcomeProjector 0 * rScr₁.basisOutcomeProjector 0 := by
    rw [SelectSwapQROM.basisOutcomeProjector_zero_eq_zeroProjOn,
      show rDiff.basisOutcomeProjector 0 = SelectSwapQROM.zeroProjOn Sdiff from
        basisOutcomeProjector_zero_qregOfFinset Sdiff,
      SelectSwapQROM.basisOutcomeProjector_zero_eq_zeroProjOn,
      (Finset.union_sdiff_of_subset hsub).symm, Finset.union_comm,
      ← SelectSwapQROM.zeroProjOn_mul_union]
  have hcomm_proj := QRegister.basisOutcomeProjector_comm rDiff 0 rScr₁ 0
  let rCombB := (rActLoc 16 11 mOut mMid 0 aRem mRem sRem).compose
    (rCombSubInAct mOut mMid mCut bGear hbCut)
  have hDisjReg : rCombB.DisjointWires rDiff := QRegister.disjoint_iff.mpr fun i j hij ↦ by
    have hm : rDiff j ∈ rDiff.image := (QRegister.mem_image rDiff _).mpr ⟨j, rfl⟩
    dsimp only [rDiff] at hm
    rw [image_qregOfFinset Sdiff] at hm
    exact Finset.disjoint_left.mp hDisjDiff ((QRegister.mem_image _ _).mpr ⟨i, rfl⟩) (hij ▸ hm)
  have hW_eq : ((rActLoc 16 11 mOut mMid 0 aRem mRem sRem).embedUnitary
      ((rCombSubInAct mOut mMid mCut bGear hbCut).embedUnitary uMux)).1 =
      rCombB.embedMatrix uMux.1 := by
    rw [← QRegister.embedUnitary_compose]
    rfl
  have hW_comm := QRegister.embedMatrix_comm_basisOutcomeProjector_of_disjoint
    rCombB rDiff hDisjReg uMux.1 0
  let Pd := rDiff.basisOutcomeProjector 0
  let Ps := rScr₁.basisOutcomeProjector 0
  let W := rCombB.embedMatrix uMux.1
  rw [hW_eq] at hPres₁
  change rExt.basisOutcomeProjector 0 * (_ * rExt.basisOutcomeProjector 0) = _
  rw [hW_eq]
  calc rExt.basisOutcomeProjector 0 * (W * rExt.basisOutcomeProjector 0)
      = Pd * (Ps * (W * Ps)) * Pd := by
          rw [hPext]
          nth_rw 2 [hcomm_proj]
          dsimp only [Pd, Ps]
          simp only [Matrix.mul_assoc]
    _ = (Pd * W) * (Ps * Pd) := by
          dsimp only [Pd, Ps, W]
          rw [hPres₁]
          dsimp only [rScr₁, mOut, mMid, aRem, mRem]
          simp only [Matrix.mul_assoc]
    _ = W * (Ps * (Pd * Pd)) := by
          dsimp only [Pd, Ps, W]
          rw [← hW_comm, Matrix.mul_assoc,
            ← Matrix.mul_assoc (rDiff.basisOutcomeProjector 0), hcomm_proj]
          simp only [Matrix.mul_assoc]
    _ = W * rExt.basisOutcomeProjector 0 := by
          dsimp only [Pd, Ps, W]
          rw [rDiff.basisOutcomeProjector_mul_self 0, ← hcomm_proj, ← hPext]

/-- Relocated `StageM` (`m2 - m1` QPE bits, `2 ^ (m2 - m1) - 1` super-steps at `sUbM`). -/
def threeGearDeferPhaseMSuperDyn {Var : Type} (wOuter wInner2 ko km m2 m1 nDirtyLo sRem sUbM : ℕ)
    (hkOut : ko ≤ wOuter) (hkMid : km ≤ wInner2) (hm2_14 : m2 ≤ 14) (hDirty1 : nDirtyLo ≤ m1)
    (hsUbM : sUbM ≤ sRem + (m1 - nDirtyLo)) (v : Var)
    (pSuperM : DynamicCircuit Var (combQubitsAt (m2 - m1) wOuter wInner2 ko km 0 sUbM)) :
    DynamicCircuit Var (combQubitsB wOuter wInner2 ko km sRem) :=
  if hm12_lt : m1 < m2 then
    (affineDihedralRefl2Dyn (m2 - m1) 11 (mOutUB wOuter) (mMidUB wInner2) 0 sUbM v
      (combWalkReflRegs 11 wOuter wInner2 ko km hkOut hkMid) (m2 - m1) (2 ^ (m2 - m1) - 1)
      (by omega) le_rfl (hbScr_gearDefer (m2 - m1) wOuter wInner2 ko km sUbM hkOut hkMid (by omega))
      pSuperM).onRegister
      (rGearDeferInB (m2 - m1) m1 wOuter wInner2 ko km nDirtyLo sRem sUbM (by omega) hDirty1 hsUbM)
  else .circuit .identity

/-- Blocked Part 3 (`w.cBond, w.base.cWinLo, StageF, cIqft`), keeping `rFullZeroLocB` clean. -/
def threeGearDeferBlockedPart3Prog {Var : Type} (wOuter wInner2 ko km M m2 m1 nDirtyLo sRem : ℕ)
    (hkOut : ko ≤ wOuter) (hkMid : km ≤ wInner2) (hm1_1 : 1 ≤ m1) (_hDirty : nDirtyLo ≤ m1 - 1)
    (v : Var) (cIqft : Circuit 16) (w : ThreeGearBondDeferSpec M m2 m1 nDirtyLo)
    (pRefl2F : DynamicCircuit Var (combQubitsB wOuter wInner2 ko km sRem)) :
    DynamicCircuit Var (combQubitsB wOuter wInner2 ko km sRem) :=
  let mOut := mOutUB wOuter
  let mMid := mMidUB wInner2
  let aRem := combARem wOuter wInner2 ko km
  let mRem := midRemWidth wInner2 km
  let hm1_15 : m1 ≤ 15 := le_trans (le_trans w.hm12 w.hm2_14) (by decide)
  let rBond := (rQPELoc 16 11 mOut mMid 0 aRem mRem sRem).compose
    (rBondHiInQPE16 m1 hm1_1 hm1_15)
  .seq (.circuit (w.cBond.onRegister rBond))
    (twoGearBlockedPart2Prog wOuter wInner2 ko km M m1 nDirtyLo sRem hkOut hkMid
      hm1_1 hm1_15 v cIqft w.base pRefl2F)

/-- Computable Part 3 (`wc.cBond, wc.cWinLo, StageF, cIqft`) from `ThreeGearWindowCirc`. -/
def threeGearDeferBlockedPart3CircProg {Var : Type} (wOuter wInner2 ko km m2 m1 nDirtyLo sRem : ℕ)
    (hkOut : ko ≤ wOuter) (hkMid : km ≤ wInner2) (hm1_1 : 1 ≤ m1) (_hDirty : nDirtyLo ≤ m1 - 1)
    (v : Var) (cIqft : Circuit 16) (wc : ThreeGearWindowCirc m2 m1 nDirtyLo)
    (pRefl2F : DynamicCircuit Var (combQubitsB wOuter wInner2 ko km sRem)) :
    DynamicCircuit Var (combQubitsB wOuter wInner2 ko km sRem) :=
  let mOut := mOutUB wOuter
  let mMid := mMidUB wInner2
  let aRem := combARem wOuter wInner2 ko km
  let mRem := midRemWidth wInner2 km
  let hm1_15 : m1 ≤ 15 := le_trans (le_trans wc.hm12 wc.hm2_14) (by decide)
  let rBond := (rQPELoc 16 11 mOut mMid 0 aRem mRem sRem).compose
    (rBondHiInQPE16 m1 hm1_1 hm1_15)
  .seq (.circuit (wc.cBond.onRegister rBond))
    (twoGearBlockedPart2CircProg wOuter wInner2 ko km m1 nDirtyLo sRem hkOut hkMid
      hm1_1 hm1_15 v cIqft ⟨.identity, wc.cWinLo⟩ pRefl2F)

@[simp] theorem threeGearDeferBlockedPart3CircProg_toCirc {Var : Type}
    (wOuter wInner2 ko km M m2 m1 nDirtyLo sRem : ℕ)
    (hkOut : ko ≤ wOuter) (hkMid : km ≤ wInner2) (hm1_1 : 1 ≤ m1) (hDirty : nDirtyLo ≤ m1 - 1)
    (v : Var) (cIqft : Circuit 16) (w : ThreeGearBondDeferSpec M m2 m1 nDirtyLo)
    (pRefl2F : DynamicCircuit Var (combQubitsB wOuter wInner2 ko km sRem)) :
    threeGearDeferBlockedPart3CircProg wOuter wInner2 ko km m2 m1 nDirtyLo sRem
      hkOut hkMid hm1_1 hDirty v cIqft w.toCirc pRefl2F =
    threeGearDeferBlockedPart3Prog wOuter wInner2 ko km M m2 m1 nDirtyLo sRem
      hkOut hkMid hm1_1 hDirty v cIqft w pRefl2F := rfl

end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.TailShiftWindow46847
