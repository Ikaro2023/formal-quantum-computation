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

public import QuantumComputationDiscoveries.Algorithms.Photochemistry.Solution.WStateHalfBellCollapse
set_option allowUnsafeReducibility true
open QuantumComputation.Specs.PhotochemistrySolution.SpecDefs
open QuantumComputation.Specs.PhotochemistrySolution.QhlAux
open QuantumComputation.Specs.PhotochemistrySolution.PgBase
open QuantumComputation.Specs.PhotochemistrySolution.SelectBase
@[expose] public section
set_option autoImplicit false
open scoped Matrix BigOperators ComplexOrder MatrixOrder Circuit.Notation
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SelectCompactAnc (ancWOfScr)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.PotOraclePortBStream (cHiNSub341
    val_cHiNSub341)
set_option maxRecDepth 16384
set_option exponentiation.threshold 8192

noncomputable section
namespace QuantumComputation.Specs.PhotochemistrySolution.WStateStage5Unload
open Operator QProg Matrix Circuit Qubit HermitianMat PrimitiveGate QuantumComputation.Specs
  PhotochemistrySolution.KetSupport PhotochemistrySolution
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
open PhotochemistrySolution.XMeasUnld PhotochemistrySolution.SplitRouter47_187
  PhotochemistrySolution.SelectOracles PhotochemistrySolution.RouterSelectWiringA
  PhotochemistrySolution.RouterSelectWiringB
open PhotochemistrySolution.ProviderCore PhotochemistrySolution.Stage12Compact
  PhotochemistrySolution.ZeroNEremSpec PhotochemistrySolution.PotSelectWiring
  PhotochemistrySolution.SortedRouterSpec
open PhotochemistrySolution.Coin70Lift PhotochemistrySolution.Sub5885MuxD1
  PhotochemistrySolution.Sub5885 PhotochemistrySolution.PortBDualBellUnld
  PhotochemistrySolution.PortBStage5Merged PhotochemistrySolution.WStateRouterPrim
open _root_.DynamicCircuit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt hiding ket matrix_ext_ket
  qAssign_obs_map_val ket_projector_zero ket_projector_one ket_X ket_CNOT ket_TOFF eval_seq_mulVec
  bit_cases localIdx
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB hiding writeReg
  writeReg_apply_of_not_mem ket ket_X ket_CNOT ket_TOFF matrix_ext_ket bitSign eval_seq_mulVec
  localIdx
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynQromUncompA (fwdCirc
    fwdCirc_mulVec_ket)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SplitBellVecCleanStep (fanoutXorBits
    fanoutXorBits_of_ne_tgt specFanoutCopyCirc specFanoutCopyCirc_mulVec_ket specFanoutCopyVecCirc
    unitary_comm_inv_of_comm bellZHalfVecDyn bellXHalfVecDyn subspaceStep_congr_in)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SelectCsa64ProvSpec (SubspaceStep)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SplitRouterSeqBell26k hiding ket
  matrix_ext_ket
open _root_.QuantumComputation.Specs.PhotochemistrySolution.HalfBellCollapse (fixedFanoutVecCirc
    hcnotSupportedIn_fixedFanoutVec fanoutXorBits_eq_fixedFanoutBits)
local instance (priority := 100000) {k : ℕ} : NeZero (2 ^ k) := ⟨pow_ne_zero k two_ne_zero⟩
attribute [local irreducible] systemQubits_frozen
attribute [local semireducible]
  PhotochemistrySolution.DynQromUncompA.fwdCirc
  ComputeProg.fwdBits
  PhotochemistrySolution.SplitBellVecCleanStep.specFanoutCopyCirc
  PhotochemistrySolution.SplitBellVecCleanStep.specFanoutCopyVecCirc
theorem ket_sb_eq {n : ℕ} (α : BitAssignment n) :
    PhotochemistrySolution.KinB.ket α = ket α := rfl

theorem ket_sr_eq_xm {n : ℕ} (α : BitAssignment n) :
    PhotochemistrySolution.SplitRouterSeqBell26k.ket α = ket α := rfl

/-- Pad an `M`-wire one-hot array `c` with `N - M` scratch wires `pad` to reach `N` wires. -/
def padWires {M N n : ℕ} (c : Fin M → Wire n) (pad : Fin (N - M) → Wire n) : Fin N → Wire n :=
  fun j ↦ if h : j.val < M then c ⟨j.val, h⟩ else pad ⟨j.val - M, by omega⟩

theorem padWires_cast {M N n : ℕ} (hMN : M ≤ N) (c : Fin M → Wire n) (pad : Fin (N - M) → Wire n)
    (p : Fin M) : padWires c pad ⟨p.val, Nat.lt_of_lt_of_le p.isLt hMN⟩ =
    c p := by dsimp [padWires]; rw [dite_eq_left p.isLt]
theorem padWires_mem {M N n : ℕ} {S : Wire n → Prop} {c : Fin M → Wire n}
    {pad : Fin (N - M) → Wire n} (hc : ∀ p, S (c p)) (hp : ∀ i, S (pad i))
    (j : Fin N) : S (padWires c pad j) := by
  by_cases h : j.val < M <;> simp [padWires, h, hc, hp]

theorem padWires_zero_of_zero {M N n : ℕ} {c : Fin M → Wire n} {pad : Fin (N - M) → Wire n}
    {δ : BitAssignment n} (hc : ∀ p, δ (c p) = 0) (hp : ∀ i, δ (pad i) = 0)
    (j : Fin N) : δ (padWires c pad j) = 0 := by
  exact padWires_mem (S := fun w ↦ δ w = 0) hc hp j

theorem wRouterDisj_padWires {D M N n : ℕ} {wHas : Wire n} {wIdx : Fin D → Wire n}
    {c : Fin M → Wire n} {pad : Fin (N - M) → Wire n} {qEnc : Wire n}
    (hHasC : ∀ p, wHas ≠ c p) (hHasP : ∀ i, wHas ≠ pad i) (hHasQ : wHas ≠ qEnc)
    (hIdxC : ∀ d p, wIdx d ≠ c p) (hIdxP : ∀ d i, wIdx d ≠ pad i) (hIdxQ : ∀ d, wIdx d ≠ qEnc)
    (hcInj : ∀ p q, p ≠ q → c p ≠ c q) (hpInj : ∀ i j, i ≠ j → pad i ≠ pad j)
    (hcp : ∀ p i, c p ≠ pad i) (hcQ : ∀ p, c p ≠ qEnc) (hpQ : ∀ i, pad i ≠ qEnc) :
    WRouterDisj wHas wIdx (padWires c pad) qEnc where
  has_ne_out := padWires_mem (S := (wHas ≠ ·)) hHasC hHasP
  has_ne_q := hHasQ
  idx_ne_out d := padWires_mem (S := (wIdx d ≠ ·)) (hIdxC d) (hIdxP d)
  idx_ne_q := hIdxQ
  out_inj i j hne := by
    have hv := Fin.val_ne_of_ne hne; dsimp [padWires]
    split_ifs with hi hj
    · exact hcInj _ _ (fun e ↦ hv (Fin.mk.inj e))
    · exact hcp _ _
    · exact (hcp _ _).symm
    · exact hpInj _ _ (fun hsub ↦ by have hs := congrArg Fin.val hsub; dsimp at hs; omega)
  out_ne_q := padWires_mem (S := (· ≠ qEnc)) hcQ hpQ

theorem uOneHotToggle_padWires_eq_fwdCirc_of_supportedOn {D M N n : ℕ} (hMN : M ≤ N) {wHas : Wire n}
    {wIdx : Fin D → Wire n} {c : Fin M → Wire n} {pad : Fin (N - M) → Wire n} {qEnc : Wire n}
    (hd : WRouterDisj wHas wIdx (padWires c pad) qEnc) (pDec : ComputeProg n) (R : Operator (2 ^ n))
    (hSupp : SupportedOn (fun δ ↦ (∀ p : Fin M, δ (c p) = 0) ∧ (∀ i : Fin (N - M), δ (pad i) = 0) ∧
    idxValD wIdx δ < M ∧ (∀ p : Fin M, pDec.fwdBits δ (c p) = if idxValD wIdx δ =
    p.val then δ wHas else 0) ∧ (∀ u : Wire n, (∀ p : Fin M, u ≠ c p) → pDec.fwdBits δ u =
    δ u)) R) : (uOneHotToggle wHas wIdx (padWires c pad) hd.has_ne_out hd.idx_ne_out).1 * R =
    (fwdCirc pDec).eval.1 * R :=
  uOneHotToggle_mul_eq_of_supportedOn hMN wHas wIdx (padWires c pad)
    hd.has_ne_out hd.idx_ne_out hd.out_inj (fwdCirc pDec).eval.1 R
    (fun A B hAB ↦ hSupp A B fun δ ⟨hc0, hp0, hLt, hOut, hOth⟩ ↦
      hAB δ ⟨padWires_zero_of_zero hc0 hp0, hLt, pDec.fwdBits δ,
        by simpa only [ket_sb_eq, ket_sr_eq_xm] using fwdCirc_mulVec_ket pDec δ,
        fun p ↦ (congrArg (pDec.fwdBits δ) (padWires_cast hMN c pad p)).trans (hOut p),
        fun u hu ↦ hOth u fun p e ↦ hu p (e.trans (padWires_cast hMN c pad p).symm)⟩)

theorem uOneHotToggle_eq_fwdCirc_pDecLoN {n : ℕ} (rN : RouterReg 47 6 n)
    (pad : Fin (48 - 47) → Wire n) (qEnc : Wire n) (hd : WRouterDisj (rHas1 rN) (rIdx1 rN)
    (padWires (rCtrlLo rN) pad) qEnc) (R : Operator (2 ^ n))
    (hSupp : SupportedOn (fun δ ↦ (∀ p : Fin 47, δ (rCtrlLo rN p) = 0) ∧ (∀ i, δ (pad i) = 0) ∧
    UnloadLoPred rN δ) R) : (uOneHotToggle (rHas1 rN) (rIdx1 rN)
    (padWires (rCtrlLo rN) pad) hd.has_ne_out hd.idx_ne_out).1 * R =
    (fwdCirc (pDecLoNSorted rN)).eval.1 * R := by
  refine uOneHotToggle_padWires_eq_fwdCirc_of_supportedOn (by omega) hd (pDecLoNSorted rN) R
    fun A B hAB ↦ hSupp A B fun δ ⟨hc0, hp0, hPLo⟩ ↦ ?_
  obtain ⟨h1, h2, _⟩ := spec_pDecLo_sorted (by omega) (by omega) sorted47_hPow rN (fun d p ↦ rr_ne
    rN (by have : _ ∧ _ := ⟨d.isLt, p.isLt⟩; dsimp [basePub]; omega)) δ hc0 hPLo
  exact hAB δ ⟨hc0, hp0, hPLo.1, h1, h2⟩

theorem uOneHotToggle_eq_fwdCirc_pDecLoE {n : ℕ} (rE : RouterReg 187 8 n)
    (pad : Fin (192 - 187) → Wire n) (qEnc : Wire n) (hd : WRouterDisj (rHas1 rE) (rIdx1 rE)
    (padWires (rCtrlLo rE) pad) qEnc) (R : Operator (2 ^ n))
    (hSupp : SupportedOn (fun δ ↦ (∀ q : Fin 187, δ (rCtrlLo rE q) = 0) ∧ (∀ i, δ (pad i) = 0) ∧
    UnloadLoPred rE δ) R) : (uOneHotToggle (rHas1 rE) (rIdx1 rE)
    (padWires (rCtrlLo rE) pad) hd.has_ne_out hd.idx_ne_out).1 * R =
    (fwdCirc (pDecLoESorted rE)).eval.1 * R := by
  refine uOneHotToggle_padWires_eq_fwdCirc_of_supportedOn (by omega) hd (pDecLoESorted rE) R
    fun A B hAB ↦ hSupp A B fun δ ⟨hc0, hp0, hPLo⟩ ↦ ?_
  obtain ⟨h1, h2, _⟩ := spec_pDecLo_sorted (by omega) (by omega) sorted187_hPow rE (fun d q ↦ rr_ne
    rE (by have : _ ∧ _ := ⟨d.isLt, q.isLt⟩; dsimp [basePub]; omega)) δ hc0 hPLo
  exact hAB δ ⟨hc0, hp0, hPLo.1, h1, h2⟩

theorem uOneHotToggle_eq_fwdCirc_pDecHiN {n : ℕ} (rN : RouterReg 47 6 n) (rE : RouterReg 187 8 n)
    (cHiN : Fin 47 → Wire n) (w : SharedPortBWiring rN rE cHiN) (pad : Fin (48 - 47) → Wire n)
    (qEnc : Wire n) (hd : WRouterDisj (rRawHas2 rN) (rIdx2 rN) (padWires cHiN pad) qEnc)
    (R : Operator (2 ^ n)) (hSupp : SupportedOn (fun δ ↦ (∀ p : Fin 47, δ (cHiN p) = 0) ∧
    (∀ i, δ (pad i) = 0) ∧ UnloadHiPred rN δ) R) : (uOneHotToggle (rRawHas2 rN) (rIdx2 rN)
    (padWires cHiN pad) hd.has_ne_out hd.idx_ne_out).1 * R =
    (fwdCirc (pDecHiNOn rN rE cHiN w)).eval.1 * R := by
  exact uOneHotToggle_padWires_eq_fwdCirc_of_supportedOn (by omega) hd (pDecHiNOn rN rE cHiN w) R
    fun A B hAB ↦ hSupp A B fun δ ⟨hc0, hp0, hPHi⟩ ↦
      let hs := spec_pDecHiNOn rN rE cHiN w δ hc0 hPHi
      hAB δ ⟨hc0, hp0, hPHi.1, hs.1, hs.2.1⟩

theorem uOneHotToggle_eq_fwdCirc_pDecHiE {n : ℕ} (rE : RouterReg 187 8 n)
    (pad : Fin (192 - 187) → Wire n) (qEnc : Wire n) (hd : WRouterDisj (rRawHas2 rE) (rIdx2 rE)
    (padWires (rCtrlLo rE) pad) qEnc) (R : Operator (2 ^ n))
    (hSupp : SupportedOn (fun δ ↦ (∀ q : Fin 187, δ (rCtrlLo rE q) = 0) ∧ (∀ i, δ (pad i) = 0) ∧
    UnloadHiPred rE δ) R) : (uOneHotToggle (rRawHas2 rE) (rIdx2 rE)
    (padWires (rCtrlLo rE) pad) hd.has_ne_out hd.idx_ne_out).1 * R =
    (fwdCirc (pDecHiESorted rE)).eval.1 * R := by
  exact uOneHotToggle_padWires_eq_fwdCirc_of_supportedOn (by omega) hd (pDecHiESorted rE) R
    fun A B hAB ↦ hSupp A B fun δ ⟨hc0, hp0, hPHi⟩ ↦
      let hs := spec_pDecHi_sorted sorted187_hD1 sorted187_hMlo (by omega)
        (fun d hdlt ↦ sorted187_hPow d (sortedUnload_lt_of_sub hdlt)) rE δ hc0 hPHi
      hAB δ ⟨hc0, hp0, hPHi.1, hs.1, hs.2.1⟩
/-- `1`-wire nuclear padding slice `s7 0`. -/
def padNOfS7 {n : ℕ} (s7 : Fin 7 → Wire n) : Fin (48 - 47) → Wire n :=
  fun _ ↦ s7 ⟨0, by omega⟩

/-- `5`-wire electronic padding slice `s7 1..5`. -/
def padEOfS7 {n : ℕ} (s7 : Fin 7 → Wire n) : Fin (192 - 187) → Wire n :=
  fun i ↦ s7 ⟨1 + i.val, by omega⟩

/-- Shared `1`-wire barrel-shift parity ancilla `s7 6`. -/
def qEncOfS7 {n : ℕ} (s7 : Fin 7 → Wire n) : Wire n :=
  s7 ⟨6, by omega⟩

/-- Stage-5 W-state scratch disjointness bundle for `PortOnly` mode (does not forbid `rHB rE`). -/
structure Stage5PortOnlyScratch {n : ℕ} (rN : RouterReg 47 6 n) (rE : RouterReg 187 8 n)
    (cHiN : Fin 47 → Wire n) (s7 : Fin 7 → Wire n) : Prop where
  s7_inj : ∀ i j : Fin 7, i ≠ j → s7 i ≠ s7 j
  s7_notHdrN : ∀ j, ¬ RouterCtrlSet rN (s7 j)
  s7_notHdrE : ∀ j, ¬ RouterCtrlSet rE (s7 j)
  s7_ne_ctrlN : ∀ j p, s7 j ≠ rCtrlLo rN p
  s7_ne_ctrlE : ∀ j q, s7 j ≠ rCtrlLo rE q
  s7_ne_cHiN : ∀ j p, s7 j ≠ cHiN p
  s7_notModN : ∀ j, ¬ AllPlaneMod rN (s7 j)
  s7_ne_bufLoE : ∀ j k, s7 j ≠ rBufLo rE k
  s7_ne_bufHiE : ∀ j k, s7 j ≠ rBufHi rE k
  s7_ne_hAE : ∀ j k, s7 j ≠ rHA rE k
  s7_ne_sysE : ∀ j q b, s7 j ≠ rSys rE q b

private theorem wRouterDisj_of_s7 {D M N n : ℕ} {wHas : Wire n} {wIdx : Fin D → Wire n}
    {c : Fin M → Wire n} {s7 : Fin 7 → Wire n} {idx : Fin (N - M) → Fin 7}
    (hs : ∀ i j : Fin 7, i ≠ j → s7 i ≠ s7 j) (hNotHdr : ∀ j : Fin 7, wHas ≠ s7 j ∧ ∀ d, wIdx d ≠
        s7 j)
    (hNeC : ∀ (j : Fin 7) (p : Fin M), s7 j ≠ c p) (hHasC : ∀ p, wHas ≠ c p)
    (hIdxC : ∀ d p, wIdx d ≠ c p) (hcInj : ∀ p q, p ≠ q → c p ≠ c q)
    (hiInj : ∀ i j, i ≠ j → idx i ≠ idx j) (hi6 : ∀ i, idx i ≠ 6) :
    WRouterDisj wHas wIdx (padWires c (fun i ↦ s7 (idx i))) (qEncOfS7 s7) :=
  wRouterDisj_padWires hHasC (fun i ↦ (hNotHdr (idx i)).1) (hNotHdr 6).1 hIdxC
    (fun d i ↦ (hNotHdr (idx i)).2 d) (hNotHdr 6).2 hcInj (fun i j hne ↦ hs _ _ (hiInj i j hne))
    (fun p i ↦ (hNeC (idx i) p).symm) (fun p ↦ (hNeC 6 p).symm) (fun i ↦ hs _ _ (hi6 i))

theorem Stage5PortOnlyScratch.disjLoN {n : ℕ} {rN : RouterReg 47 6 n} {rE : RouterReg 187 8 n}
    {cHiN : Fin 47 → Wire n} {s7 : Fin 7 → Wire n} (hs : Stage5PortOnlyScratch rN rE cHiN s7) :
    WRouterDisj (rHas1 rN) (rIdx1 rN) (padWires (rCtrlLo rN) (padNOfS7 s7)) (qEncOfS7 s7) :=
  wRouterDisj_of_s7 hs.s7_inj (fun j ↦ ⟨fun e ↦ hs.s7_notHdrN j (e ▸ Or.inl rfl),
      fun d e ↦ hs.s7_notHdrN j (e ▸ Or.inr (Or.inr (Or.inl ⟨d, rfl⟩)))⟩) hs.s7_ne_ctrlN
    (hne_prep_dec rN).1 (fun d p ↦
        rr_ne rN (by have := d.isLt; have := p.isLt; unfold basePub; dsimp; omega))
    (hne_prep_dec rN).2.2.1 (by decide) (by decide)
theorem Stage5PortOnlyScratch.disjLoE {n : ℕ} {rN : RouterReg 47 6 n} {rE : RouterReg 187 8 n}
    {cHiN : Fin 47 → Wire n} {s7 : Fin 7 → Wire n} (hs : Stage5PortOnlyScratch rN rE cHiN s7) :
    WRouterDisj (rHas1 rE) (rIdx1 rE) (padWires (rCtrlLo rE) (padEOfS7 s7)) (qEncOfS7 s7) :=
  wRouterDisj_of_s7 hs.s7_inj (fun j ↦ ⟨fun e ↦ hs.s7_notHdrE j (e ▸ Or.inl rfl),
      fun d e ↦ hs.s7_notHdrE j (e ▸ Or.inr (Or.inr (Or.inl ⟨d, rfl⟩)))⟩) hs.s7_ne_ctrlE
    (hne_prep_dec rE).1 (fun d q ↦
        rr_ne rE (by have := d.isLt; have := q.isLt; unfold basePub; dsimp; omega))
    (hne_prep_dec rE).2.2.1 (by decide) (by decide)
theorem Stage5PortOnlyScratch.disjHiN {n : ℕ} {rN : RouterReg 47 6 n} {rE : RouterReg 187 8 n}
    {cHiN : Fin 47 → Wire n} {s7 : Fin 7 → Wire n} (hs : Stage5PortOnlyScratch rN rE cHiN s7)
    (w : SharedPortBWiring rN rE cHiN) :
    WRouterDisj (rRawHas2 rN) (rIdx2 rN) (padWires cHiN (padNOfS7 s7)) (qEncOfS7 s7) :=
  wRouterDisj_of_s7 hs.s7_inj (fun j ↦ ⟨fun e ↦ hs.s7_notHdrN j (e ▸ Or.inr (Or.inl rfl)),
      fun d e ↦ hs.s7_notHdrN j (e ▸ Or.inr (Or.inr (Or.inr ⟨d, rfl⟩)))⟩) hs.s7_ne_cHiN
    w.rawN_ne_cHiN w.idx2N_ne_cHiN w.cHiN_inj (by decide) (by decide)
theorem Stage5PortOnlyScratch.disjHiE {n : ℕ} {rN : RouterReg 47 6 n} {rE : RouterReg 187 8 n}
    {cHiN : Fin 47 → Wire n} {s7 : Fin 7 → Wire n} (hs : Stage5PortOnlyScratch rN rE cHiN s7) :
    WRouterDisj (rRawHas2 rE) (rIdx2 rE) (padWires (rCtrlLo rE) (padEOfS7 s7)) (qEncOfS7 s7) :=
  wRouterDisj_of_s7 hs.s7_inj (fun j ↦ ⟨fun e ↦ hs.s7_notHdrE j (e ▸ Or.inr (Or.inl rfl)),
      fun d e ↦ hs.s7_notHdrE j (e ▸ Or.inr (Or.inr (Or.inr ⟨d, rfl⟩)))⟩) hs.s7_ne_ctrlE
    (hne_rRawHas2_ctrlLo rE) (hne_rIdx2_ctrlLo rE) (hne_prep_dec rE).2.2.1 (by decide) (by decide)
def s7OfHBE {n : ℕ} (rE : RouterReg 187 8 n) (j : Fin 7) : Wire n :=
  rHB rE ⟨j.val, by omega⟩

theorem stage5PortOnlyScratch_s7OfHBE {n : ℕ} {rNuc : RouterReg 47 6 dLayout}
    {rElec : RouterReg 187 8 dLayout} (hRegs : ValidMuxD1Stage2Regs rNuc rElec)
    (rTot : QRegister dLayout n) : Stage5PortOnlyScratch (rTot.compose rNuc) (rTot.compose rElec)
    (fun p ↦ rTot (cHiNSub341 p)) (s7OfHBE (rTot.compose rElec)) := by
  let rN := rTot.compose rNuc
  let rE := rTot.compose rElec
  have hValS7 (j : Fin 7) :
      (rElec ⟨90 + j.val, rw_ltHB 187 8 ⟨j.val, by omega⟩⟩).val = 5923 + j.val := by
    have := j.isLt
    rw [hRegs.pubElec _ (by dsimp; omega), val_rElecLayout_eq, val_elecRouterWireFn]
    dsimp [routerWidth]; split_ifs <;> omega
  have hDisjN (j : Fin 7) (i : Fin (routerWidth 47 6)) (e : s7OfHBE rE j = rN i) : False := by
    have : _ ∧ _ := ⟨j.isLt, hRegs.val_rNuc_bounds i⟩
    have hv := congrArg Fin.val (rTot.wires.injective e)
    rw [hValS7 j] at hv; omega
  have hNeE (j : Fin 7) {m : Fin (routerWidth 187 8)} (hm : m.val < 90 ∨ 97 ≤ m.val) :
      s7OfHBE rE j ≠ rE m := rr_ne rE (hm.elim
    (fun h ↦ (h.trans_le (Nat.le_add_right 90 j.val)).ne')
    fun h ↦ ((Nat.add_lt_add_left j.isLt 90).trans_le h).ne)
  refine ⟨fun _ _ hne ↦ rr_ne rE fun h ↦ Fin.val_ne_of_ne hne (Nat.add_left_cancel h),
    fun j hh ↦ (routerCtrlSet_pubIdx_nuc hh).elim fun i hi ↦ hDisjN j i hi.2,
    fun j hh ↦ (routerCtrlSet_pubIdx_elec hh).elim fun _ hk ↦
      hNeE j (Or.inl (hk.1.trans (by decide))) hk.2,
    fun j p ↦ hDisjN j ⟨basePub 47 6 + 6 + 2 * 6 + p.val, rw_ltCtrlLo p⟩,
    fun j q ↦ hNeE j (Or.inr ((by decide : 97 ≤ basePub 187 8 + 6 + 2 * 8).trans
      (Nat.le_add_right _ q.val))),
    fun j p e ↦ ?_, fun j hm ↦ (allPlaneMod_pubIdx_nuc hm).elim fun i hi ↦ hDisjN j i hi.2.2,
    fun j k ↦ hNeE j (Or.inl ((Nat.add_lt_add_left k.isLt 18).trans (by decide))),
    fun j k ↦ hNeE j (Or.inl ((Nat.add_lt_add_left k.isLt 42).trans (by decide))),
    fun j k ↦ hNeE j (Or.inl (Nat.add_lt_add_left k.isLt 66)),
    fun j q b ↦ hNeE j (Or.inr ((by decide : 97 ≤ 114).trans
      ((Nat.le_add_right 114 (24 * q.val)).trans (Nat.le_add_right _ b.val))))⟩
  have : _ ∧ _ := ⟨j.isLt, p.isLt⟩
  have hv := congrArg Fin.val (rTot.wires.injective e)
  rw [hValS7 j, val_cHiNSub341] at hv; split_ifs at hv <;> omega

/--
Shared-`PortB` `PortOnly` conjugation operator `F_N⁻¹ * (F_E⁻¹ * (C_NE * (S_NE * (F_E * F_N))))`
for Stage 5 after `rHB rE` and `rHB rN` have been collapsed onto `rBufHi rE`.
-/
def uSharedHiPortOnlyConj {n : ℕ} (rN : RouterReg 47 6 n) (rE : RouterReg 187 8 n)
    (cHiN : Fin 47 → Wire n) (w : SharedPortBWiring rN rE cHiN) : Operator (2 ^ n) :=
  let F_N := (fwdCirc (pDecHiNOn rN rE cHiN w)).eval;
  let F_E := (fwdCirc (pDecHiESorted rE)).eval
  let sysNE : Fin 24 → Fin (47 + 187) → Wire n := fun k ↦
      appendFin (fun p ↦ pSys (planeOfRouter rN k) p) (fun q ↦ pSys (planeOfRouter rE k) q)
  let C_NE :=
      (specFanoutCopyVecCirc (47 + 187) 24 (rBufHi rE)
      (appendFin cHiN (rCtrlLo rE)) sysNE w.hBC_NE (fun k ↦ w.hBT_NE_all k k)
      (fun k i ↦ w.hCT_NE_all k i i)).eval.1
  let S_NE :=
      (portSwapVecCirc (47 + 187) 24 (rBufHi rE)
      (appendFin cHiN (rCtrlLo rE)) sysNE w.hBC_NE (fun k ↦ w.hBT_NE_all k k)
      (fun k i ↦ w.hCT_NE_all k i i)).eval.1
  (F_N⁻¹).1 * ((F_E⁻¹).1 * (C_NE * (S_NE * (F_E.1 * F_N.1))))

/-- Precondition on `X₁` for `pUnloadSharedHiPortOnlyWState` (does not constrain `rHB rE`). -/
def SharedHiPortOnlyPred {n : ℕ} (rN : RouterReg 47 6 n) (rE : RouterReg 187 8 n)
    (cHiN : Fin 47 → Wire n) (α : BitAssignment n) : Prop :=
  (∀ p : Fin 47, α (cHiN p) = 0) ∧
  (∀ q : Fin 187, α (rCtrlLo rE q) = 0) ∧
  UnloadHiPred rN α ∧
  UnloadHiPred rE α ∧
  (α (rRawHas2 rN) = 1 → α (rRawHas2 rE) = 0) ∧
  (∀ k : Fin 24, α (rBufHi rE k) = 0) ∧
  ValidZeroGatedSortedRouterInput rN α

/--
Wires actively modified by `uSharedHiPortOnlyConj` : `{rBufHi rE, rSys rN, rSys rE}` (excludes
`rHB rE` ).
-/
def PortOnlyHiMod {n : ℕ} (rN : RouterReg 47 6 n) (rE : RouterReg 187 8 n) (u : Wire n) : Prop :=
    (∃ b : Fin 24, u = rBufHi rE b) ∨ (∃ (p : Fin 47) (b : Fin 24), u = rSys rN p b) ∨
    (∃ (q : Fin 187) (b : Fin 24), u = rSys rE q b)
theorem fwdCirc_inv_mulVec_ket_of_fwdBits_eq {n : ℕ} (pDec : ComputeProg n) {δ' ζ : BitAssignment n}
    (hEq : pDec.fwdBits δ' = ζ) : ((fwdCirc pDec).eval⁻¹).1.mulVec (ket ζ) = ket δ' := by
  have hFwd : (fwdCirc pDec).eval.1.mulVec (ket δ') = ket ζ := by
    simpa only [ket_sb_eq,
        ket_sr_eq_xm] using (fwdCirc_mulVec_ket pDec δ').trans (congrArg _ hEq)
  rw [← hFwd, Matrix.mulVec_mulVec,
      show ((fwdCirc pDec).eval⁻¹).1 * (fwdCirc pDec).eval.1 = 1 from
        congrArg Subtype.val (inv_mul_cancel (fwdCirc pDec).eval),
      Matrix.one_mulVec]

theorem portSwapVecCirc_ket_preserve {n : ℕ} (M : ℕ) :
    ∀ (m : ℕ) (qB : Fin m → Wire n) (wCtrl : Fin M → Wire n) (wTgt : Fin m → Fin M → Wire n)
      (hbc : ∀ k p, qB k ≠ wCtrl p) (hbt : ∀ k p, qB k ≠ wTgt k p)
      (hct : ∀ k p, wCtrl p ≠ wTgt k p) (δ : BitAssignment n),
      ∃ ζ : BitAssignment n,
        (portSwapVecCirc M m qB wCtrl wTgt hbc hbt hct).eval.1.mulVec (ket δ) = ket ζ ∧
        ∀ u : Wire n, (∀ k, u ≠ qB k) → (∀ k p, u ≠ wTgt k p) → ζ u = δ u
  | 0, _, _, _, _, _, _, δ =>
      ⟨δ,
          by unfold portSwapVecCirc; rw [Circuit.eval_identity, Submonoid.coe_one,
               Matrix.one_mulVec],
        fun _ _ _ ↦ rfl⟩
  | m + 1, qB, wCtrl, wTgt, hbc, hbt, hct, δ => by
      obtain ⟨ζ₀, hζ₀, hEq₀⟩ :=
          portSwapVecCirc_ket_preserve M m (fun k ↦ qB k.castSucc) wCtrl (fun k ↦ wTgt k.castSucc)
          (fun k ↦ hbc k.castSucc) (fun k ↦ hbt k.castSucc) (fun k ↦ hct k.castSucc) δ
      refine ⟨portSwap1Bits M (qB (Fin.last m)) wCtrl (wTgt (Fin.last m)) ζ₀, ?_, ?_⟩
      · unfold portSwapVecCirc;
        rw [eval_seq_mulVec, hζ₀, ← ket_sr_eq_xm, portSwap1Circ_mulVec_ket, ket_sr_eq_xm]
      · intro u hB hT
        exact (portSwap1Bits_of_ne M (qB (Fin.last m)) wCtrl (wTgt (Fin.last m)) ζ₀ u
            (hB (Fin.last m)) (hT (Fin.last m))).trans (hEq₀ u (fun k ↦ hB k.castSucc)
            (fun k ↦ hT k.castSucc))

theorem specFanoutCopyVecCirc_ket_preserve {n : ℕ} (M : ℕ) :
    ∀ (m : ℕ) (qB : Fin m → Wire n) (wCtrl : Fin M → Wire n) (wTgt : Fin m → Fin M → Wire n)
      (hbc : ∀ k p, qB k ≠ wCtrl p) (hbt : ∀ k p, qB k ≠ wTgt k p)
      (hct : ∀ k p, wCtrl p ≠ wTgt k p) (δ : BitAssignment n),
      ∃ ζ : BitAssignment n,
        (specFanoutCopyVecCirc M m qB wCtrl wTgt hbc hbt hct).eval.1.mulVec (ket δ) = ket ζ ∧
        ∀ u : Wire n, (∀ k p, u ≠ wTgt k p) → ζ u = δ u
  | 0, _, _, _, _, _, _, δ =>
      ⟨δ,
          by unfold specFanoutCopyVecCirc; rw [Circuit.eval_identity, Submonoid.coe_one,
               Matrix.one_mulVec],
        fun _ _ ↦ rfl⟩
  | m + 1, qB, wCtrl, wTgt, hbc, hbt, hct, δ => by
      obtain ⟨ζ₀, hζ₀, hEq₀⟩ :=
          specFanoutCopyVecCirc_ket_preserve M m (fun k ↦ qB k.castSucc) wCtrl (fun k ↦
          wTgt k.castSucc) (fun k ↦ hbc k.castSucc) (fun k ↦ hbt k.castSucc)
          (fun k ↦ hct k.castSucc) δ
      let ζ₁ :=
          if ζ₀ (qB (Fin.last m)) = 0 then ζ₀ else fanoutXorBits M wCtrl (wTgt (Fin.last m)) ζ₀
      refine ⟨ζ₁, ?_, ?_⟩
      · unfold specFanoutCopyVecCirc; rw [eval_seq_mulVec, hζ₀];
        simpa only [ket_sb_eq, ket_sr_eq_xm] using specFanoutCopyCirc_mulVec_ket M _ _ _ _ _ _ ζ₀
      · intro u hT; dsimp only [ζ₁]; split_ifs
        · exact hEq₀ u fun k ↦ hT k.castSucc
        · exact (fanoutXorBits_of_ne_tgt M wCtrl (wTgt (Fin.last m)) ζ₀ u
            (hT (Fin.last m))).trans (hEq₀ u fun k ↦ hT k.castSucc)

/--
Pure classical-control single-port `PortOnly` circuit `fixedSwapVecCirc ;;ᶜ fixedFanoutVecCirc`
(after `qH` has been Z-collapsed onto `qB`).
-/
def cFixedPortOnlyCirc {M n : ℕ} (qB : Fin 24 → Wire n) (cVec : Fin M → ZMod 2)
    (wT : Fin 24 → Fin M → Wire n) (hbt : ∀ (b : Fin 24) (p : Fin M), qB b ≠ wT b p) : Circuit n :=
  fixedSwapVecCirc M 24 qB cVec wT hbt ;;ᶜ fixedFanoutVecCirc M 24 qB cVec wT hbt
theorem unloadHiPred_congr {M D n : ℕ} {r : RouterReg M D n} {α β : BitAssignment n}
    (hRaw : α (rRawHas2 r) = β (rRawHas2 r)) (hIdx : ∀ d : Fin D, α (rIdx2 r d) = β (rIdx2 r d))
    (hβ : UnloadHiPred r β) : UnloadHiPred r α :=
    ⟨(SplitRouter47_187.idxValD_congr hIdx).trans_lt hβ.1, fun hz ↦
    (SplitRouter47_187.idxValD_congr hIdx).trans (hβ.2.1 (hRaw.symm.trans hz)), fun ho h0 ↦
    hβ.2.2 (hRaw.symm.trans ho) ((SplitRouter47_187.idxValD_congr hIdx).symm.trans h0)⟩
theorem fwdCirc_ket {n : ℕ} (pDec : ComputeProg n) (δ : BitAssignment n) :
    (fwdCirc pDec).eval.1.mulVec (ket δ) = ket (pDec.fwdBits δ)
    := by simpa only [ket_sb_eq, ket_sr_eq_xm] using fwdCirc_mulVec_ket pDec δ
theorem specFanoutCopyVec_eq_fixedFanoutVec {n : ℕ} {P : BitAssignment n → Prop} (M : ℕ)
    (wCtrl : Fin M → Wire n) (cVec : Fin M → ZMod 2) (hC : ∀ p α, P α → α (wCtrl p) = cVec p) :
    ∀ (m : ℕ) (qB : Fin m → Wire n) (wTgt₁ wTgt₂ : Fin m → Fin M → Wire n)
      (_hT : ∀ k p, wTgt₁ k p = wTgt₂ k p)
      (hbc : ∀ k p, qB k ≠ wCtrl p) (hbt₁ : ∀ k p, qB k ≠ wTgt₁ k p)
      (hct : ∀ k p, wCtrl p ≠ wTgt₁ k p) (hbt₂ : ∀ k p, qB k ≠ wTgt₂ k p)
      (_hc_disj : ∀ k p q, wCtrl p ≠ wTgt₂ k q)
      (_hUpdT : ∀ k p α v, P α → P (Function.update α (wTgt₂ k p) v))
      {ψ : Fin (2 ^ n) → ℂ}, PreservesKetPred P ψ →
      (specFanoutCopyVecCirc M m qB wCtrl wTgt₁ hbc hbt₁ hct).eval.1.mulVec ψ =
        (fixedFanoutVecCirc M m qB cVec wTgt₂ hbt₂).eval.1.mulVec ψ ∧
      PreservesKetPred P ((fixedFanoutVecCirc M m qB cVec wTgt₂ hbt₂).eval.1.mulVec ψ)
  | 0, _, _, _, _, _, _, _, _, _, _, _, hψ =>
      ⟨by simp [specFanoutCopyVecCirc, fixedFanoutVecCirc],
       by simpa [fixedFanoutVecCirc] using hψ⟩
  | m + 1, qB, wTgt₁, wTgt₂, hT, hbc, hbt₁, hct, hbt₂, hc_disj, hUpdT, ψ, hψ => by
      obtain ⟨hEqV, hPV⟩ :=
          specFanoutCopyVec_eq_fixedFanoutVec M wCtrl cVec hC m (fun k ↦ qB k.castSucc)
          (fun k ↦ wTgt₁ k.castSucc) (fun k ↦ wTgt₂ k.castSucc) (fun k ↦ hT k.castSucc)
          (fun k ↦ hbc k.castSucc) (fun k ↦ hbt₁ k.castSucc) (fun k ↦ hct k.castSucc)
          (fun k ↦ hbt₂ k.castSucc) (fun k ↦ hc_disj k.castSucc) (fun k ↦ hUpdT k.castSucc) hψ
      let kL := Fin.last m; have htEq : wTgt₁ kL = wTgt₂ kL := funext (hT kL)
      refine ⟨?_, ?_⟩
      · dsimp only [specFanoutCopyVecCirc, fixedFanoutVecCirc]
        rw [eval_seq_mulVec, eval_seq_mulVec, hEqV]
        exact hPV _ _ fun α hPα ↦ by
          have hL : (specFanoutCopyCirc M (qB kL) wCtrl (wTgt₁ kL) (hbc kL) (hbt₁ kL)
              (hct kL)).eval.1.mulVec (ket α) = ket (if α (qB kL) =
              0 then α else fanoutXorBits M wCtrl (wTgt₁ kL) α)
              := by simpa only [ket_sb_eq,
                      ket_sr_eq_xm] using specFanoutCopyCirc_mulVec_ket M (qB kL) wCtrl (wTgt₁ kL)
                      (hbc kL) (hbt₁ kL) (hct kL) α
          rw [hL, fixedFanoutCirc_mulVec_ket M (qB kL) cVec (wTgt₂ kL) (hbt₂ kL) α, htEq]
          rcases DynCircExt.bit_cases (α (qB kL)) with hb0 | hb1
          · rw [hb0, ite_eq_left rfl, fixedFanoutBits_zero_src]
          · rw [hb1, ite_eq_right one_ne_zero,
                fanoutXorBits_eq_fixedFanoutBits M wCtrl (wTgt₂ kL) cVec α (fun p ↦ hC p α hPα)
                (hc_disj kL)]
      · dsimp only [fixedFanoutVecCirc]; rw [eval_seq_mulVec];
        exact preservesKetPred_fixedFanout M (qB kL) cVec (wTgt₂ kL) (hbt₂ kL) (hUpdT kL) hPV

theorem hcnotSupportedIn_PortOnlyHiMod {n : ℕ} (rN : RouterReg 47 6 n) (rE : RouterReg 187 8 n)
    (cHiN : Fin 47 → Wire n) (w : SharedPortBWiring rN rE cHiN)
    (cHiNVec : Fin 47 → ZMod 2) (cHiEVec : Fin 187 → ZMod 2) :
    HCNOTSupportedIn (PortOnlyHiMod rN rE)
      (fixedSwapVecCirc (47 + 187) 24 (rBufHi rE) (appendFin cHiNVec cHiEVec)
          (fun b ↦ appendFin (fun p ↦ rSys rN p b) (fun q ↦ rSys rE q b)) w.hBTs_NE ;;ᶜ
        fixedFanoutVecCirc (47 + 187) 24 (rBufHi rE) (appendFin cHiNVec cHiEVec)
          (fun b ↦ appendFin (fun p ↦ rSys rN p b) (fun q ↦ rSys rE q b)) w.hBTs_NE) := by
  have hS (b : Fin 24) (i : Fin (47 + 187)) (_ : appendFin cHiNVec cHiEVec i = 1) :
      PortOnlyHiMod rN rE (appendFin (fun p ↦ rSys rN p b) (fun q ↦ rSys rE q b) i) :=
    (appendFin_eq i).elim (fun ⟨p, hp⟩ ↦ hp ▸ Or.inr (Or.inl ⟨p, b, appendFin_castAdd _ _ p⟩))
      fun ⟨q, hq⟩ ↦ hq ▸ Or.inr (Or.inr ⟨q, b, appendFin_natAdd _ _ q⟩)
  exact .seq (hcnotSupportedIn_fixedSwapVec _ 24 _ _ _ (fun b ↦ Or.inl ⟨b, rfl⟩) hS)
    (hcnotSupportedIn_fixedFanoutVec 24 _ _ _ _ (fun b ↦ Or.inl ⟨b, rfl⟩) hS)
theorem uSharedHiInnerPortOnly_mulVec_ket {n : ℕ} (rN : RouterReg 47 6 n) (rE : RouterReg 187 8 n)
    (cHiN : Fin 47 → Wire n) (w : SharedPortBWiring rN rE cHiN)
    {γ₁ : BitAssignment n} {cHiNVec : Fin 47 → ZMod 2} {cHiEVec : Fin 187 → ZMod 2}
    (hγ₁N : ∀ p : Fin 47, γ₁ (cHiN p) = cHiNVec p)
    (hγ₂E : ∀ q : Fin 187, (pDecHiESorted rE).fwdBits γ₁ (rCtrlLo rE q) = cHiEVec q)
    (hγ₂Oth : ∀ u : Wire n, (∀ q : Fin 187, u ≠ rCtrlLo rE q) →
      (pDecHiESorted rE).fwdBits γ₁ u = γ₁ u) :
    let F_E := (fwdCirc (pDecHiESorted rE)).eval
    let sysNE : Fin 24 → Fin (47 + 187) → Wire n := fun k ↦
        appendFin (fun p ↦ pSys (planeOfRouter rN k) p) (fun q ↦ pSys (planeOfRouter rE k) q)
    let C_NE :=
        (specFanoutCopyVecCirc (47 + 187) 24 (rBufHi rE)
        (appendFin cHiN (rCtrlLo rE)) sysNE w.hBC_NE (fun k ↦ w.hBT_NE_all k k)
        (fun k i ↦ w.hCT_NE_all k i i)).eval.1
    let S_NE :=
        (portSwapVecCirc (47 + 187) 24 (rBufHi rE)
        (appendFin cHiN (rCtrlLo rE)) sysNE w.hBC_NE (fun k ↦ w.hBT_NE_all k k)
        (fun k i ↦ w.hCT_NE_all k i i)).eval.1
    ((F_E⁻¹).1 * (C_NE * (S_NE * F_E.1))).mulVec (ket γ₁) =
      (fixedSwapVecCirc (47 + 187) 24 (rBufHi rE) (appendFin cHiNVec cHiEVec)
          (fun b ↦ appendFin (fun p ↦ rSys rN p b) (fun q ↦ rSys rE q b)) w.hBTs_NE ;;ᶜ
        fixedFanoutVecCirc (47 + 187) 24 (rBufHi rE) (appendFin cHiNVec cHiEVec)
          (fun b ↦ appendFin (fun p ↦ rSys rN p b) (fun q ↦ rSys rE q b))
          w.hBTs_NE).eval.1.mulVec (ket γ₁) := by
  intro F_E sysNE C_NE S_NE; let γ₂ := (pDecHiESorted rE).fwdBits γ₁
  let P_both : BitAssignment n → Prop := fun α ↦
      (∀ p, α (cHiN p) = cHiNVec p) ∧ (∀ q, α (rCtrlLo rE q) = cHiEVec q)
  have hγ₂Both : P_both γ₂ := ⟨fun p ↦ (hγ₂Oth (cHiN p) (w.cHiN_ne_ctrlE p)).trans (hγ₁N p), hγ₂E⟩
  have hγ₂App : ∀ (i : Fin (47 + 187)) (α : BitAssignment n), P_both α →
      α (appendFin cHiN (rCtrlLo rE) i) = appendFin cHiNVec cHiEVec i :=
    fun i α ⟨h1, h2⟩ ↦ by
      rcases appendFin_eq i with ⟨p, rfl⟩ | ⟨q, rfl⟩
      · rw [appendFin_castAdd, appendFin_castAdd]; exact h1 p
      · rw [appendFin_natAdd, appendFin_natAdd]; exact h2 q
  let S_In : Wire n → Prop := PortOnlyHiMod rN rE
  have hKeepBoth : ∀ {u : Wire n}, S_In u → ∀ α val, P_both α →
      P_both (Function.update α u val) := fun {u} hu α val ⟨h1, h2⟩ ↦
    ⟨fun p ↦ (Function.update_of_ne (a := cHiN p) (a' := u) (by
        rcases hu with ⟨b, rfl⟩ | ⟨p', b, rfl⟩ | ⟨q', b, rfl⟩
        · exact (w.hBC_N b p).symm
        · exact fun e ↦ w.cHiN_notModN p
            (e ▸ ⟨b, Or.inr (Or.inr (Or.inr (Or.inr ⟨p', (planeOfRouter_sys rN b p').symm⟩)))⟩)
        · exact fun e ↦ w.cHiN_notModE p
            (e ▸ ⟨b, Or.inr (Or.inr (Or.inr (Or.inr
              ⟨q', (planeOfRouter_sys rE b q').symm⟩)))⟩)) val α).trans (h1 p),
     fun q ↦ (Function.update_of_ne (a := rCtrlLo rE q) (a' := u) (by
        rcases hu with ⟨b, rfl⟩ | ⟨p', b, rfl⟩ | ⟨q', b, rfl⟩
        · exact rr_ne rE (by have := b.isLt; have := q.isLt; unfold basePub; dsimp; omega)
        · exact w.ctrlE_ne_sysN q p' b
        · exact rr_ne rE
            (by have := b.isLt; have := q.isLt; have := q'.isLt; unfold basePub; dsimp; omega)
      ) val α).trans (h2 q)⟩
  let sysR : Fin 24 → Fin (47 + 187) → Wire n :=
    fun b ↦ appendFin (fun p ↦ rSys rN p b) (fun q ↦ rSys rE q b)
  have hwT_eq : ∀ b i, sysNE b i = sysR b i := fun b i ↦ by
      dsimp only [sysNE, sysR]
      rcases appendFin_eq i with ⟨p, rfl⟩ | ⟨q, rfl⟩
      · rw [appendFin_castAdd, appendFin_castAdd, planeOfRouter_sys]
      · rw [appendFin_natAdd, appendFin_natAdd, planeOfRouter_sys]
  have hKeepSys : ∀ b i α val, P_both α → P_both (Function.update α (sysR b i) val) := fun b i ↦ by
      dsimp only [sysR]
      rcases appendFin_eq i with ⟨p, rfl⟩ | ⟨q, rfl⟩
      · rw [appendFin_castAdd]; exact hKeepBoth (Or.inr (Or.inl ⟨p, b, rfl⟩))
      · rw [appendFin_natAdd]; exact hKeepBoth (Or.inr (Or.inr ⟨q, b, rfl⟩))
  obtain ⟨e1, p1⟩ := portSwapVec_eq_fixedSwapVec (47 + 187)
    (appendFin cHiN (rCtrlLo rE)) (appendFin cHiNVec cHiEVec) hγ₂App 24 (rBufHi rE)
    sysNE sysR hwT_eq w.hBC_NE (fun k ↦ w.hBT_NE_all k k) (fun k i ↦ w.hCT_NE_all k i i)
    w.hBTs_NE (fun b ↦ hKeepBoth (Or.inl ⟨b, rfl⟩)) hKeepSys (preservesKetPred_ket hγ₂Both)
  obtain ⟨e2, _⟩ := specFanoutCopyVec_eq_fixedFanoutVec (47 + 187)
    (appendFin cHiN (rCtrlLo rE)) (appendFin cHiNVec cHiEVec) hγ₂App 24 (rBufHi rE)
    sysNE sysR hwT_eq w.hBC_NE (fun k ↦ w.hBT_NE_all k k) (fun k i ↦ w.hCT_NE_all k i i)
    w.hBTs_NE (fun b i j ↦ hwT_eq b j ▸ w.hCT_NE_all b i j) hKeepSys p1
  let cIn := cFixedPortOnlyCirc (rBufHi rE) (appendFin cHiNVec cHiEVec) sysR w.hBTs_NE
  have hSuppIn : HCNOTSupportedIn S_In cIn :=
    hcnotSupportedIn_PortOnlyHiMod rN rE cHiN w cHiNVec cHiEVec
  have hCommFE : cIn.eval.1 * F_E.1 = F_E.1 * cIn.eval.1 :=
    hSuppIn.toCircSupportedIn F_E
      (actsIndepOf_fwdCirc_of_disj (pDecHiESorted rE) (progSupportedIn_pDecHiESorted rE)
        fun u hu hT ↦ by
          rcases hT with hHdr | ⟨q, rfl⟩
          · obtain ⟨j, hj18, rfl⟩ := routerCtrlSet_pubIdx_elec hHdr
            rcases hu with ⟨b, h⟩ | ⟨p', b, h⟩ | ⟨q', b, h⟩
            · exact rr_ne rE (by have := b.isLt; dsimp; omega) h
            · exact (w.pubN_ne_pubE (i := ⟨110 + 24 * p'.val + b.val, _⟩)
                (by have := p'.isLt; have := b.isLt; dsimp; omega) (by omega)) h.symm
            · exact rr_ne rE (by have := q'.isLt; have := b.isLt; dsimp; omega) h
          · rcases hu with ⟨b, h⟩ | ⟨p', b, h⟩ | ⟨q', b, h⟩
            · exact rr_ne rE (by have := b.isLt; have := q.isLt; unfold basePub; dsimp; omega)
                  h.symm
            · exact w.ctrlE_ne_sysN q p' b h
            · exact rr_ne rE
                (by have := b.isLt; have := q.isLt; have := q'.isLt; unfold basePub; dsimp; omega)
                h.symm)
  have hCommFEInv : cIn.eval.1 * (F_E⁻¹).1 = (F_E⁻¹).1 * cIn.eval.1 :=
      unitary_comm_inv_of_comm F_E cIn.eval.1 hCommFE; simp only [← Matrix.mulVec_mulVec];
      rw [fwdCirc_ket (pDecHiESorted rE) γ₁, ← ket_sr_eq_xm, e1, e2]
  have hSeq :
      (fixedFanoutVecCirc (47 + 187) 24 (rBufHi rE)
          (appendFin cHiNVec cHiEVec) sysR w.hBTs_NE).eval.1.mulVec
        ((fixedSwapVecCirc (47 + 187) 24 (rBufHi rE)
            (appendFin cHiNVec cHiEVec) sysR w.hBTs_NE).eval.1.mulVec
          (PhotochemistrySolution.SplitRouterSeqBell26k.ket γ₂)) =
        cIn.eval.1.mulVec (F_E.1.mulVec (ket γ₁)) := by
    dsimp only [cIn, cFixedPortOnlyCirc]
    rw [eval_seq_mulVec, fwdCirc_ket (pDecHiESorted rE) γ₁, ket_sr_eq_xm]
  rw [hSeq, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← hCommFEInv, Matrix.mul_assoc,
      show (F_E⁻¹).1 * F_E.1 = 1 from congrArg Subtype.val (inv_mul_cancel F_E), Matrix.mul_one]
  rfl

theorem uSharedHiPortOnlyConj_mulVec_ket {n : ℕ} (rN : RouterReg 47 6 n) (rE : RouterReg 187 8 n)
    (cHiN : Fin 47 → Wire n) (w : SharedPortBWiring rN rE cHiN)
    {α : BitAssignment n}
    (hCHiN0 : ∀ p : Fin 47, α (cHiN p) = 0)
    (hCtrlE0 : ∀ q : Fin 187, α (rCtrlLo rE q) = 0)
    (hPHiN : UnloadHiPred rN α) (hPHiE : UnloadHiPred rE α) :
    (uSharedHiPortOnlyConj rN rE cHiN w).mulVec (ket α) =
      (fixedSwapVecCirc (47 + 187) 24 (rBufHi rE)
          (appendFin (cOfSortedHi rN α) (cOfSortedHi rE α))
          (fun b ↦ appendFin (fun p ↦ rSys rN p b) (fun q ↦ rSys rE q b)) w.hBTs_NE ;;ᶜ
        fixedFanoutVecCirc (47 + 187) 24 (rBufHi rE)
          (appendFin (cOfSortedHi rN α) (cOfSortedHi rE α))
          (fun b ↦ appendFin (fun p ↦ rSys rN p b) (fun q ↦ rSys rE q b))
          w.hBTs_NE).eval.1.mulVec (ket α) := by
  let cHiNVec := cOfSortedHi rN α; let cHiEVec := cOfSortedHi rE α;
  let F_N := (fwdCirc (pDecHiNOn rN rE cHiN w)).eval;
  let γ₁ := (pDecHiNOn rN rE cHiN w).fwdBits α; obtain ⟨hγ₁N, hγ₁Oth, _⟩ :=
      spec_pDecHiNOn rN rE cHiN w α hCHiN0 hPHiN
  have hγ₁CtrlE0 : ∀ q : Fin 187, γ₁ (rCtrlLo rE q) = 0 := fun q ↦
      (hγ₁Oth (rCtrlLo rE q) fun p e ↦ w.cHiN_ne_ctrlE p q e.symm).trans (hCtrlE0 q)
  have hγ₁HdrE : γ₁ (rRawHas2 rE) = α (rRawHas2 rE) ∧
      ∀ d : Fin 8, γ₁ (rIdx2 rE d) = α (rIdx2 rE d) :=
    ⟨hγ₁Oth _ fun p e ↦ w.cHiN_notHdrE p (e ▸ Or.inr (Or.inl rfl)),
     fun d ↦ hγ₁Oth _ fun p e ↦ w.cHiN_notHdrE p (e ▸ Or.inr (Or.inr (Or.inr ⟨d, rfl⟩)))⟩
  have hPHiE_γ₁ : UnloadHiPred rE γ₁ := unloadHiPred_congr hγ₁HdrE.1 hγ₁HdrE.2 hPHiE
  have hcHiEEq : cOfSortedHi rE γ₁ = cHiEVec := by
    funext q; dsimp [cOfSortedHi, cHiEVec];
    rw [SplitRouter47_187.idxValD_congr hγ₁HdrE.2, hγ₁HdrE.1]
  obtain ⟨hγ₂E0, hγ₂Oth, _⟩ := spec_pDecHi_sorted sorted187_hD1 sorted187_hMlo (by omega)
    (fun d hdlt ↦ sorted187_hPow d (sortedUnload_lt_of_sub hdlt)) rE γ₁ hγ₁CtrlE0 hPHiE_γ₁
  have hγ₂E : ∀ q, (pDecHiESorted rE).fwdBits γ₁ (rCtrlLo rE q) = cHiEVec q := fun q ↦
      (hγ₂E0 q).trans (congrFun hcHiEEq q)
  let cIn := cFixedPortOnlyCirc (rBufHi rE) (appendFin cHiNVec cHiEVec)
    (fun b ↦ appendFin (fun p ↦ rSys rN p b) (fun q ↦ rSys rE q b)) w.hBTs_NE
  have hSuppIn : HCNOTSupportedIn (PortOnlyHiMod rN rE) cIn :=
    hcnotSupportedIn_PortOnlyHiMod rN rE cHiN w cHiNVec cHiEVec
  have hCommFN : cIn.eval.1 * F_N.1 = F_N.1 * cIn.eval.1 :=
    hSuppIn.toCircSupportedIn F_N
      (actsIndepOf_fwdCirc_of_disj (pDecHiNOn rN rE cHiN w) (progSupportedIn_pDecHiNOn rN rE cHiN w)
        fun u hu hT ↦ by
          rcases hT with hHdr | ⟨p, rfl⟩
          · obtain ⟨i, hi14, rfl⟩ := routerCtrlSet_pubIdx_nuc hHdr
            rcases hu with ⟨b, h⟩ | ⟨p', b, h⟩ | ⟨q', b, h⟩
            · exact (w.pubN_ne_pubE (j := ⟨42 + b.val, _⟩) (by omega)
                (by have := b.isLt; dsimp; omega)) h
            · exact rr_ne rN (by have := p'.isLt; have := b.isLt; dsimp; omega) h
            · exact (w.pubN_ne_pubE (j := ⟨114 + 24 * q'.val + b.val, _⟩) (by omega)
                (by have := q'.isLt; have := b.isLt; dsimp; omega)) h
          · rcases hu with ⟨b, h⟩ | ⟨p', b, h⟩ | ⟨q', b, h⟩
            · exact (w.hBC_N b p) h.symm
            · exact w.cHiN_notModN p ⟨b,
                  Or.inr (Or.inr (Or.inr (Or.inr ⟨p', h.trans (planeOfRouter_sys rN b p').symm⟩)))⟩
            · exact w.cHiN_notModE p
                ⟨b,
                    Or.inr (Or.inr (Or.inr (Or.inr ⟨q',
                    h.trans (planeOfRouter_sys rE b q').symm⟩)))⟩)
  have hCommFNInv : cIn.eval.1 * (F_N⁻¹).1 = (F_N⁻¹).1 * cIn.eval.1 :=
      unitary_comm_inv_of_comm F_N cIn.eval.1 hCommFN; dsimp only [uSharedHiPortOnlyConj];
      have hStepIn := uSharedHiInnerPortOnly_mulVec_ket rN rE cHiN w hγ₁N hγ₂E hγ₂Oth
  dsimp only [cIn, cFixedPortOnlyCirc] at hCommFNInv
  rw [show ∀ (A B C D E : Operator (2 ^ n)),
        A * (B * (C * (D * (E * F_N.1)))) = A * ((B * (C * (D * E))) * F_N.1) from
        fun _ _ _ _ _ ↦ by simp only [Matrix.mul_assoc],
      ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      fwdCirc_ket (pDecHiNOn rN rE cHiN w) α, hStepIn, ← fwdCirc_ket (pDecHiNOn rN rE cHiN w) α,
      Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← hCommFNInv, Matrix.mul_assoc,
      show (F_N⁻¹).1 * F_N.1 = 1 from congrArg Subtype.val (inv_mul_cancel F_N), Matrix.mul_one]
private theorem fixedSwap1Circ_ket_preserve {n : ℕ} :
    ∀ (M : ℕ) (qB : Wire n) (cVec : Fin M → ZMod 2) (wTgt : Fin M → Wire n) (hbt : ∀ p, qB ≠ wTgt p)
        (δ : BitAssignment n),
      ∃ ζ : BitAssignment n, (fixedSwap1Circ M qB cVec wTgt hbt).eval.1.mulVec (ket δ) = ket ζ ∧
        ∀ u : Wire n, u ≠ qB → (∀ p, u ≠ wTgt p) → ζ u = δ u
  | 0, _, _, _, _, δ =>
        ⟨δ,
        by unfold fixedSwap1Circ; rw [Circuit.eval_identity, Submonoid.coe_one, Matrix.one_mulVec],
        fun _ _ _ ↦ rfl⟩
  | M + 1, qB, cVec, wTgt, hbt, δ => by
      obtain ⟨ζ, hζ, hEq⟩ :=
          fixedSwap1Circ_ket_preserve M qB (fun p ↦ cVec p.castSucc) (fun p ↦ wTgt p.castSucc)
          (fun p ↦ hbt p.castSucc) δ
      dsimp only [fixedSwap1Circ]
      rw [eval_seq_mulVec, hζ]
      split_ifs
      · simp only [eval_seq_mulVec, ket_CNOT]
        exact ⟨_, rfl, fun u hB hT ↦ by
          simpa [Function.update_of_ne hB, Function.update_of_ne (hT _)] using
            hEq u hB fun p ↦ hT p.castSucc⟩
      · rw [Circuit.eval_identity, Submonoid.coe_one, Matrix.one_mulVec]
        exact ⟨ζ, rfl, fun u hB hT ↦ hEq u hB fun p ↦ hT p.castSucc⟩

private theorem fixedSwapVecCirc_ket_preserve {n : ℕ} (M : ℕ) :
    ∀ (m : ℕ) (qB : Fin m → Wire n) (cVec : Fin M → ZMod 2) (wTgt : Fin m → Fin M → Wire n)
        (hbt : ∀ k p, qB k ≠ wTgt k p) (δ : BitAssignment n),
      ∃ ζ : BitAssignment n, (fixedSwapVecCirc M m qB cVec wTgt hbt).eval.1.mulVec (ket δ) = ket ζ ∧
        ∀ u : Wire n, (∀ k, u ≠ qB k) → (∀ k p, u ≠ wTgt k p) → ζ u = δ u
  | 0, _, _, _, _, δ =>
        ⟨δ,
        by unfold fixedSwapVecCirc; rw [Circuit.eval_identity, Submonoid.coe_one,
             Matrix.one_mulVec], fun _ _ _ ↦ rfl⟩
  | m + 1, qB, cVec, wTgt, hbt, δ => by
      obtain ⟨ζ₀, hζ₀, hEq₀⟩ :=
          fixedSwapVecCirc_ket_preserve M m (fun k ↦ qB k.castSucc) cVec (fun k ↦ wTgt k.castSucc)
          (fun k ↦ hbt k.castSucc) δ
      obtain ⟨ζ₁, hζ₁, hEq₁⟩ :=
          fixedSwap1Circ_ket_preserve M (qB (Fin.last m)) cVec (wTgt (Fin.last m))
          (hbt (Fin.last m)) ζ₀
      refine ⟨ζ₁, ?_, fun u hB hT ↦ (hEq₁ u (hB _) (hT _)).trans (hEq₀ u (fun k ↦ hB k.castSucc)
          (fun k ↦ hT k.castSucc))⟩
      dsimp only [fixedSwapVecCirc]
      rw [eval_seq_mulVec, hζ₀, hζ₁]

private theorem fixedFanoutVecCirc_ket_preserve {n : ℕ} (M : ℕ) :
    ∀ (m : ℕ) (qB : Fin m → Wire n) (cVec : Fin M → ZMod 2) (wTgt : Fin m → Fin M → Wire n)
        (hbt : ∀ k p, qB k ≠ wTgt k p) (δ : BitAssignment n),
      ∃ ζ : BitAssignment n, (fixedFanoutVecCirc M m qB cVec wTgt hbt).eval.1.mulVec (ket δ) =
          ket ζ ∧
        ∀ u : Wire n, (∀ k p, u ≠ wTgt k p) → ζ u = δ u
  | 0, _, _, _, _, δ =>
        ⟨δ,
        by unfold fixedFanoutVecCirc; rw [Circuit.eval_identity, Submonoid.coe_one,
             Matrix.one_mulVec], fun _ _ ↦ rfl⟩
  | m + 1, qB, cVec, wTgt, hbt, δ => by
      obtain ⟨ζ₀, hζ₀, hEq₀⟩ :=
          fixedFanoutVecCirc_ket_preserve M m (fun k ↦ qB k.castSucc) cVec (fun k ↦ wTgt k.castSucc)
          (fun k ↦ hbt k.castSucc) δ
      refine ⟨fixedFanoutBits M (ζ₀ (qB (Fin.last m))) cVec (wTgt (Fin.last m)) ζ₀, ?_,
        fun u hT ↦
            (fixedFanoutBits_of_ne_tgt M _ cVec _ ζ₀ u (hT _)).trans (hEq₀ u fun k ↦ hT k.castSucc)⟩
      dsimp only [fixedFanoutVecCirc]
      rw [eval_seq_mulVec, hζ₀, ← ket_sr_eq_xm,
          fixedFanoutCirc_mulVec_ket M _ cVec _ (hbt (Fin.last m)) ζ₀]

theorem uSharedHiPortOnlyConj_ket_preserve {n : ℕ} (rN : RouterReg 47 6 n) (rE : RouterReg 187 8 n)
    (cHiN : Fin 47 → Wire n) (w : SharedPortBWiring rN rE cHiN) {α : BitAssignment n}
    (hCHiN0 : ∀ p : Fin 47, α (cHiN p) = 0) (hCtrlE0 : ∀ q : Fin 187, α (rCtrlLo rE q) = 0)
    (hPHiN : UnloadHiPred rN α) (hPHiE : UnloadHiPred rE α) :
    ∃ η₀ : BitAssignment n, (uSharedHiPortOnlyConj rN rE cHiN w).mulVec (ket α) = ket η₀ ∧
      ∀ u : Wire n, ¬ PortOnlyHiMod rN rE u → η₀ u = α u := by
  let cV := appendFin (cOfSortedHi rN α) (cOfSortedHi rE α)
  let wT (b) := appendFin (fun p ↦ rSys rN p b) (fun q ↦ rSys rE q b)
  obtain ⟨ζ₁, hζ₁, hEq₁⟩ := fixedSwapVecCirc_ket_preserve _ 24 (rBufHi rE) cV wT w.hBTs_NE α
  obtain ⟨η₀, hη₀, hEq₂⟩ := fixedFanoutVecCirc_ket_preserve _ 24 (rBufHi rE) cV wT w.hBTs_NE ζ₁
  refine ⟨η₀, by rw [uSharedHiPortOnlyConj_mulVec_ket rN rE cHiN w hCHiN0 hCtrlE0 hPHiN hPHiE,
      eval_seq_mulVec, hζ₁, hη₀], fun u hnm ↦ ?_⟩
  have hT (k i) (e : u = wT k i) : False := by
    rcases appendFin_eq i with ⟨p, rfl⟩ | ⟨q, rfl⟩
    · exact hnm (Or.inr (Or.inl ⟨p, k, by simpa only [wT, appendFin_castAdd] using e⟩))
    · exact hnm (Or.inr (Or.inr ⟨q, k, by simpa only [wT, appendFin_natAdd] using e⟩))
  exact (hEq₂ u hT).trans (hEq₁ u (fun k e ↦ hnm (Or.inl ⟨k, e⟩)) hT)
attribute [local irreducible] systemQubits_frozen ancWOfScr uSharedHiPortOnlyConj uSwapHi24
    uRouterSwapConj
theorem Stage5PortOnlyScratch.padN_disj_loN {n : ℕ} {rN : RouterReg 47 6 n} {rE : RouterReg 187 8 n}
    {cHiN : Fin 47 → Wire n} {s7 : Fin 7 → Wire n} (hs : Stage5PortOnlyScratch rN rE cHiN s7) :
    (∀ i : Fin (48 - 47), (∀ b : Fin 24, padNOfS7 s7 i ≠ rBufLo rN b ∧ padNOfS7 s7 i ≠ rHA rN b) ∧
    ∀ (p : Fin 47) (b : Fin 24), padNOfS7 s7 i ≠ rSys rN p b) ∧
    ((∀ b : Fin 24, qEncOfS7 s7 ≠ rBufLo rN b ∧ qEncOfS7 s7 ≠ rHA rN b) ∧ ∀ (p : Fin 47)
    (b : Fin 24), qEncOfS7 s7 ≠ rSys rN p b) :=
    ⟨fun _ ↦ ⟨fun b ↦ ⟨fun e ↦ hs.s7_notModN 0 ⟨b, Or.inl e⟩, fun e ↦ hs.s7_notModN 0 ⟨b,
    Or.inr (Or.inr (Or.inl e))⟩⟩, fun p b e ↦
    hs.s7_notModN 0 ⟨b,
    Or.inr (Or.inr (Or.inr (Or.inr ⟨p, e.trans (planeOfRouter_sys rN b p).symm⟩)))⟩⟩,
    ⟨fun b ↦ ⟨fun e ↦ hs.s7_notModN 6 ⟨b, Or.inl e⟩, fun e ↦ hs.s7_notModN 6 ⟨b,
    Or.inr (Or.inr (Or.inl e))⟩⟩, fun p b e ↦
    hs.s7_notModN 6 ⟨b,
    Or.inr (Or.inr (Or.inr (Or.inr ⟨p, e.trans (planeOfRouter_sys rN b p).symm⟩)))⟩⟩⟩
theorem Stage5PortOnlyScratch.padE_disj_loE {n : ℕ} {rN : RouterReg 47 6 n} {rE : RouterReg 187 8 n}
    {cHiN : Fin 47 → Wire n} {s7 : Fin 7 → Wire n} (hs : Stage5PortOnlyScratch rN rE cHiN s7) :
    (∀ i : Fin (192 - 187), (∀ b : Fin 24, padEOfS7 s7 i ≠ rBufLo rE b ∧ padEOfS7 s7 i ≠ rHA rE b) ∧
    ∀ (q : Fin 187) (b : Fin 24), padEOfS7 s7 i ≠ rSys rE q b) ∧
    ((∀ b : Fin 24, qEncOfS7 s7 ≠ rBufLo rE b ∧ qEncOfS7 s7 ≠ rHA rE b) ∧ ∀ (q : Fin 187)
    (b : Fin 24), qEncOfS7 s7 ≠ rSys rE q b) :=
  ⟨fun i ↦ ⟨fun b ↦ ⟨hs.s7_ne_bufLoE ⟨1 + i.val, by omega⟩ b, hs.s7_ne_hAE ⟨1 + i.val, by omega⟩ b⟩,
     fun q b ↦ hs.s7_ne_sysE ⟨1 + i.val, by omega⟩ q b⟩,
   ⟨fun b ↦ ⟨hs.s7_ne_bufLoE 6 b, hs.s7_ne_hAE 6 b⟩, fun q b ↦ hs.s7_ne_sysE 6 q b⟩⟩
end QuantumComputation.Specs.PhotochemistrySolution.WStateStage5Unload
end
end

@[expose] public section
set_option autoImplicit false
open scoped Matrix BigOperators ComplexOrder MatrixOrder Circuit.Notation
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SelectCompactAnc (ancWOfScr)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.PotOraclePortBStream (cHiNSub341
    val_cHiNSub341)
set_option exponentiation.threshold 256

noncomputable section
namespace QuantumComputation.Specs.PhotochemistrySolution.WStateStage2Load
open Operator QProg Matrix Circuit Qubit HermitianMat PrimitiveGate QuantumComputation.Specs
  PhotochemistrySolution.KetSupport PhotochemistrySolution PhotochemistrySolution.XMeasUnld
  PhotochemistrySolution.SplitRouter47_187 PhotochemistrySolution.SplitRouterFredkinMux
  PhotochemistrySolution.SplitRouterMuxD1 PhotochemistrySolution.ProviderCore
  PhotochemistrySolution.Stage12Compact
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
open PhotochemistrySolution.ZeroNEremSpec PhotochemistrySolution.PotSelectWiring
  PhotochemistrySolution.Stage2QromMux PhotochemistrySolution.Stage2ZeroGated
  PhotochemistrySolution.Stage2ChDiffMux960 PhotochemistrySolution.Stage2ChDiffNoNF
  PhotochemistrySolution.Sub5885MuxD1 PhotochemistrySolution.Sub5885
  PhotochemistrySolution.PortBDualBellUnld
open PhotochemistrySolution.PortBStage5Merged PhotochemistrySolution.WStateRouterPrim
  PhotochemistrySolution.HalfBellCollapse
open _root_.DynamicCircuit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt hiding ket matrix_ext_ket
  qAssign_obs_map_val ket_projector_zero ket_projector_one ket_X ket_CNOT ket_TOFF eval_seq_mulVec
  bit_cases localIdx
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB hiding writeReg
  writeReg_apply_of_not_mem ket ket_X ket_CNOT ket_TOFF matrix_ext_ket bitSign eval_seq_mulVec
  localIdx
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SelectCsa64ProvSpec (SubspaceStep)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynQromUncompA (fwdCirc
    wrapDyn fwdCirc_mulVec_ket subspaceStep_wrapDyn)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SplitBellVecCleanStep
  (subspaceStep_congr_in subspaceStep_congr_out)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SplitRouterSeqBell26k hiding ket
  matrix_ext_ket
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Stage2ElecFirstZero (swapPair
    swapPair_lt swapPair_fixed)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SortedRouterSpec (zmod2_cases
    ValidZeroGatedSortedRouterInput)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.RouterSelectWiringA (dLayout)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.WStateStage5Unload (padWires
    padWires_cast padWires_mem padWires_zero_of_zero wRouterDisj_padWires)
open scoped ComplexOrder MatrixOrder Circuit.Notation
local instance (priority := 100000) {k : ℕ} : NeZero (2 ^ k) := ⟨pow_ne_zero k two_ne_zero⟩
attribute [local irreducible] systemQubits_frozen ancWOfScr
attribute [local semireducible]
  ComputeProg.ValidProg ComputeProg.finalClean ComputeProg.fwdBits
/-
Section 1: W-state bracket interface, ket-support preservation, and wWork = 346 / 350 footprints
-/

theorem actsIndepOf_allPlaneMod_uOneHotToggle {M D D_idx N n : ℕ} (r : RouterReg M D n)
    {wHas : Wire n} {wIdx : Fin D_idx → Wire n} {wOut : Fin N → Wire n}
    (hHasOut : ∀ j, wHas ≠ wOut j) (hIdxOut : ∀ d j, wIdx d ≠ wOut j)
    (hHasNotMod : ¬ AllPlaneMod r wHas) (hIdxNotMod : ∀ d, ¬ AllPlaneMod r (wIdx d))
    (hOutNotMod : ∀ j, ¬ AllPlaneMod r (wOut j)) : ActsIndepOf (AllPlaneMod r)
    (uOneHotToggle wHas wIdx wOut hHasOut hIdxOut) := by
  refine ⟨toggleOneHotBits wHas wIdx wOut, uOneHotToggle_mulVec_ket wHas wIdx wOut hHasOut hIdxOut,
    fun q hq α val ↦ ?_⟩
  · have hqOut (j) : wOut j ≠ q := fun e ↦ hOutNotMod j (e ▸ hq)
    have hIdxEq : idxValD wIdx (Function.update α q val) = idxValD wIdx α :=
      idxValD_congr wIdx fun d ↦
        Function.update_of_ne (fun e : wIdx d = q ↦ hIdxNotMod d (e ▸ hq)) val α
    by_cases hLt : idxValD wIdx α < N
    · have hLt' : idxValD wIdx (Function.update α q val) < N := hIdxEq ▸ hLt
      dsimp only [toggleOneHotBits]
      rw [dite_eq_left hLt', dite_eq_left hLt,
        show (⟨_, hLt'⟩ : Fin N) = ⟨_, hLt⟩ from Fin.ext hIdxEq,
        Function.update_of_ne (hqOut _), Function.update_of_ne fun e : wHas = q ↦
          hHasNotMod (e ▸ hq), Function.update_comm (hqOut _).symm]
    · have hLt' : ¬ idxValD wIdx (Function.update α q val) < N := hIdxEq ▸ hLt
      dsimp only [toggleOneHotBits]
      rw [dite_eq_right hLt', dite_eq_right hLt]
/-- Wires modified by `cFixedSwapCirc r` (`rBufLo`, `rBufHi`, `rSys`, excluding `rHA` and `rHB`). -/
def SwapModSet {M D n : ℕ} (r : RouterReg M D n) (w : Wire n) : Prop :=
    (∃ b : Fin 24, w = rBufLo r b) ∨ (∃ b : Fin 24, w = rBufHi r b) ∨ (∃ (b : Fin 24)
    (p : Fin M), w = rSys r p b)
theorem swapModSet_sub_allPlaneMod {M D n : ℕ} (r : RouterReg M D n) {w : Wire n}
    (hw : SwapModSet r w) : AllPlaneMod r w := by
  exact Or.elim hw (fun ⟨b, e⟩ ↦ ⟨b, Or.inl e⟩) fun h ↦
    h.elim (fun ⟨b, e⟩ ↦ ⟨b, Or.inr (Or.inl e)⟩)
      fun ⟨b, p, e⟩ ↦
          ⟨b, Or.inr (Or.inr (Or.inr (Or.inr ⟨p, e.trans (planeOfRouter_sys r b p).symm⟩)))⟩

theorem preservesKetPred_cFixedSwapCirc {M D n : ℕ} (r : RouterReg M D n) (cLo cHi : Fin M → ZMod 2)
    {P : BitAssignment n → Prop} (hKeep : ∀ {u : Wire n}, SwapModSet r u → ∀ α v, P α →
    P (Function.update α u v)) {ψ : Fin (2 ^ n) → ℂ} (hψ : PreservesKetPred P ψ) :
    PreservesKetPred P ((cFixedSwapCirc r cLo cHi).eval.1.mulVec ψ) := by
  have hSV : ∀ (m : ℕ) (qB : Fin m → Wire n) (cV : Fin M → ZMod 2) (wT : Fin m → Fin M → Wire n)
      (hbt : ∀ k p, qB k ≠ wT k p) (hqB : ∀ k, SwapModSet r (qB k))
      (hwT : ∀ k p, SwapModSet r (wT k p)) {φ : Fin (2 ^ n) → ℂ}, PreservesKetPred P φ →
      PreservesKetPred P ((fixedSwapVecCirc M m qB cV wT hbt).eval.1.mulVec φ) := by
    intro m; induction m with
    | zero => intros; simpa [fixedSwapVecCirc]
    | succ m ihm =>
        intro qB cV wT hbt hqB hwT φ hφ
        dsimp only [fixedSwapVecCirc]; rw [eval_seq_mulVec]
        exact preservesKetPred_fixedSwap1 M _ _ _ _ (hKeep (hqB (Fin.last m)))
            (fun p ↦ hKeep (hwT (Fin.last m) p)) (ihm _ _ _ _ (fun k ↦ hqB k.castSucc)
            (fun k p ↦ hwT k.castSucc p) hφ)
  dsimp only [cFixedSwapCirc]; rw [eval_seq_mulVec]
  exact hSV 24 _ _ _ _ (fun b ↦ Or.inr (Or.inl ⟨b, rfl⟩)) (fun b p ↦ Or.inr (Or.inr ⟨b, p, rfl⟩))
    (hSV 24 _ _ _ _ (fun b ↦ Or.inl ⟨b, rfl⟩) (fun b p ↦ Or.inr (Or.inr ⟨b, p, rfl⟩)) hψ)

attribute [local irreducible] uRouterSwapConj uOneHotToggle fwdCirc cFixedRouterCirc
    cFixedBellOverlayCirc

def swapNucW350 (i : ℕ) : ℕ := swapPair 1344 1358 6 i
theorem swapNucW350_lt : ∀ i < routerWidth 47 6, swapNucW350 i < routerWidth 47 6 :=
  fun _ ↦ swapPair_lt (by decide) (by decide)

theorem swapNucW350_pub : ∀ i < basePub 47 6, swapNucW350 i = i :=
  fun _ hi ↦
      swapPair_fixed (Or.inl (Nat.lt_trans hi (by decide))) (Or.inl (Nat.lt_trans hi (by decide)))

theorem rw47_lt_1364 : 1364 < routerWidth 47 6 := by unfold routerWidth; omega
theorem rw47_lt_1365 : 1365 < routerWidth 47 6 := by unfold routerWidth; omega
theorem rw47_lt_1366 : 1366 < routerWidth 47 6 := by unfold routerWidth; omega

/-- Dummy wire `47` (`rn 1364`, `r 1364`, `rk = 83`) padding `rCtrlLo rn` to `48` outputs. -/
def padLoN48 {n : ℕ} (rn : RouterReg 47 6 n) : Fin (48 - 47) → Wire n :=
  fun _ ↦ rn ⟨1364, rw47_lt_1364⟩

/-- Dummy wire `47` (`rn 1365`, `r 1365`, `rk = 84`) padding `rCtrlHi rn` to `48` outputs. -/
def padHiN48 {n : ℕ} (rn : RouterReg 47 6 n) : Fin (48 - 47) → Wire n :=
  fun _ ↦ rn ⟨1365, rw47_lt_1365⟩

/-- Shared coherent-coin ancilla `qEnc` (`rn 1366`, `r 1366`, `rk = 85`) for both `S2_N` trees. -/
def qEncNuc {n : ℕ} (rn : RouterReg 47 6 n) : Wire n :=
  rn ⟨1366, rw47_lt_1366⟩

/-- Padded `48`-wire low-port array on `rn`. -/
abbrev wOutLoN48 {n : ℕ} (rn : RouterReg 47 6 n) : Fin 48 → Wire n :=
  padWires (rCtrlLo rn) (padLoN48 rn)

/-- Padded `48`-wire high-port array on `rn`. -/
abbrev wOutHiN48 {n : ℕ} (rn : RouterReg 47 6 n) : Fin 48 → Wire n :=
    padWires (rCtrlHi rn) (padHiN48 rn)
theorem wOutLoN48_mem {n : ℕ} {S : Wire n → Prop} (rn : RouterReg 47 6 n)
    (hc : ∀ p : Fin 47, S (rCtrlLo rn p)) (hp : S (rn ⟨1364, rw47_lt_1364⟩))
    (j : Fin 48) : S (wOutLoN48 rn j) :=
  padWires_mem (S := S) hc (fun _ ↦ hp) j

theorem wOutHiN48_mem {n : ℕ} {S : Wire n → Prop} (rn : RouterReg 47 6 n)
    (hc : ∀ p : Fin 47, S (rCtrlHi rn p)) (hp : S (rn ⟨1365, rw47_lt_1365⟩))
    (j : Fin 48) : S (wOutHiN48 rn j) :=
  padWires_mem (S := S) hc (fun _ ↦ hp) j

theorem rn_ne_wOutHiN48 {n : ℕ} (rn : RouterReg 47 6 n) {k : Fin (routerWidth 47 6)}
    (hk : k.val < 1303 ∨ 1350 ≤ k.val ∧ k.val ≠ 1365) (j : Fin 48) : rn k ≠ wOutHiN48 rn j :=
  wOutHiN48_mem (S := fun v ↦ rn k ≠ v) rn
    (fun q ↦ rr_ne rn (hk.elim
      (fun h ↦ Nat.ne_of_lt (Nat.lt_of_lt_of_le h (Nat.le_add_right 1303 q.val)))
      (fun h ↦ Nat.ne_of_gt (Nat.lt_of_lt_of_le (Nat.add_lt_add_left q.isLt 1303) h.1))))
    (rr_ne rn (hk.elim (fun h ↦ Nat.ne_of_lt (Nat.lt_trans h (by decide))) (fun h ↦ h.2))) j

theorem hne_wOutLoN48_wOutHiN48 {n : ℕ} (rn : RouterReg 47 6 n) (i j : Fin 48) : wOutLoN48 rn i ≠
    wOutHiN48 rn j := by
  exact wOutLoN48_mem (S := fun w ↦ w ≠ wOutHiN48 rn j) rn
    (fun p ↦ rn_ne_wOutHiN48 rn (Or.inl (Nat.add_lt_add_left p.isLt 1256)) j)
    (rn_ne_wOutHiN48 rn (Or.inr ⟨by decide, by decide⟩) j) i

theorem idxValPrefix_eq_zero_of_zero {D n : ℕ} (wBit : Fin D → Wire n) {δ : BitAssignment n}
    (h : ∀ d, δ (wBit d) = 0) : ∀ (k : ℕ) (hk : k ≤ D), idxValPrefix wBit δ k hk = 0
  | 0, _ => rfl
  | k + 1, hk => by
      simp [idxValPrefix, idxValPrefix_eq_zero_of_zero wBit h k (Nat.le_of_succ_le hk), h ⟨k, hk⟩]
theorem idxValD_eq_zero_of_zero {D n : ℕ} (wBit : Fin D → Wire n) {δ : BitAssignment n}
    (h : ∀ d, δ (wBit d) = 0) : idxValD wBit δ = 0 := idxValPrefix_eq_zero_of_zero wBit h D le_rfl

/--
Shared 1-wire-padded nuclear `WRouterDisj` constructor by disjoint `Fin (routerWidth 47 6)` index
bands.
-/
theorem wRouterDisj_nuc48 {n : ℕ} (rn : RouterReg 47 6 n)
    {iHas iPad : Fin (routerWidth 47 6)} {iIdx : Fin 6 → Fin (routerWidth 47 6)}
    {iCtrl : Fin 47 → Fin (routerWidth 47 6)}
    (hHas : iHas.val < 2) (hIdx : ∀ d, (iIdx d).val < 14)
    (hCtrlLo : ∀ p, 1256 ≤ (iCtrl p).val) (hCtrlHi : ∀ p, (iCtrl p).val < 1350)
    (hCtrlInj : ∀ p q, p ≠ q → (iCtrl p).val ≠ (iCtrl q).val)
    (hPadLo : 1364 ≤ iPad.val) (hPadHi : iPad.val < 1366) :
    WRouterDisj (rn iHas) (fun d ↦ rn (iIdx d))
      (padWires (fun p ↦ rn (iCtrl p)) (fun (_ : Fin (48 - 47)) ↦ rn iPad)) (qEncNuc rn) :=
  let hlt {a b : Fin (routerWidth 47 6)} (h : a.val < b.val) : rn a ≠ rn b := rr_ne rn h.ne
  wRouterDisj_padWires (fun p ↦ hlt (hHas.trans_le ((by decide : 2 ≤ 1256).trans (hCtrlLo p))))
    (fun _ ↦ hlt (hHas.trans_le ((by decide : 2 ≤ 1364).trans hPadLo)))
    (hlt (hHas.trans (by decide)))
    (fun d p ↦ hlt ((hIdx d).trans_le ((by decide : 14 ≤ 1256).trans (hCtrlLo p))))
    (fun d _ ↦ hlt ((hIdx d).trans_le ((by decide : 14 ≤ 1364).trans hPadLo)))
    (fun d ↦ hlt ((hIdx d).trans (by decide))) (fun p q hne ↦ rr_ne rn (hCtrlInj p q hne))
    (fun i j hne ↦ absurd (Fin.ext (by omega)) hne)
    (fun p _ ↦ hlt ((hCtrlHi p).trans_le ((by decide : 1350 ≤ 1364).trans hPadLo)))
    (fun p ↦ hlt ((hCtrlHi p).trans (by decide))) fun _ ↦ hlt hPadHi

theorem wRouterDisj_loN48 {n : ℕ} (rn : RouterReg 47 6 n) :
    WRouterDisj (rHas1 rn) (rIdx1 rn) (wOutLoN48 rn) (qEncNuc rn) :=
  wRouterDisj_nuc48 rn (by decide)
    (fun d ↦ Nat.lt_trans (Nat.add_lt_add_left d.isLt 2) (by decide))
    (fun p ↦ Nat.le_add_right 1256 p.val)
    (fun p ↦ Nat.lt_trans (Nat.add_lt_add_left p.isLt 1256) (by decide))
    (fun _ _ hne h ↦ Fin.val_ne_of_ne hne (Nat.add_left_cancel h)) (by decide) (by decide)

theorem wRouterDisj_hiN48 {n : ℕ} (rn : RouterReg 47 6 n) :
    WRouterDisj (rRawHas2 rn) (rIdx2 rn) (wOutHiN48 rn) (qEncNuc rn) :=
  wRouterDisj_nuc48 rn (by decide) (fun d ↦ Nat.add_lt_add_left d.isLt 8)
    (fun p ↦ Nat.le_trans (by decide) (Nat.le_add_right 1303 p.val))
    (fun p ↦ Nat.add_lt_add_left p.isLt 1303)
    (fun _ _ hne h ↦ Fin.val_ne_of_ne hne (Nat.add_left_cancel h)) (by decide) (by decide)

/--
Zero-`T` `ComputeProg` XORing `rCtrlHi r[0..k)` into `rCtrlLo r[0..k)` (`UX` bridge for
`pDualBellPlanesMuxD1CHDiffMD`).
-/
def pXorCtrlHiToLoLoop {M D n : ℕ} (r : RouterReg M D n) : (k : ℕ) → k ≤ M → ComputeProg n
  | 0, _ => .id
  | k + 1, hk =>
      .seq (pXorCtrlHiToLoLoop r k (Nat.le_of_succ_le hk))
        (.cnot (rCtrlHi r ⟨k, hk⟩) (rCtrlLo r ⟨k, hk⟩)
            (rr_ne r (by dsimp [rCtrlHi, rCtrlLo]; omega)))

/-- Full `M`-port `0-T` CNOT sweep `rCtrlHi r p -> rCtrlLo r p`. -/
def pXorCtrlHiToLo {M D n : ℕ} (r : RouterReg M D n) : ComputeProg n :=
    pXorCtrlHiToLoLoop r M le_rfl

private theorem pXorCtrlHiToLoLoop_props {M D n : ℕ} (r : RouterReg M D n) :
    ∀ k hk, (pXorCtrlHiToLoLoop r k hk).numAnd = 0 ∧ (pXorCtrlHiToLoLoop r k hk).finalClean ∅ = ∅ ∧
      (pXorCtrlHiToLoLoop r k hk).ValidProg ∅ ∅
  | 0, _ => ⟨rfl, rfl, trivial⟩
  | k + 1, hk => by
      obtain ⟨hA, hC, hV⟩ := pXorCtrlHiToLoLoop_props r k (Nat.le_of_succ_le hk)
      exact ⟨by simpa [pXorCtrlHiToLoLoop, ComputeProg.numAnd] using hA, hC, by
        simpa [pXorCtrlHiToLoLoop, ComputeProg.ValidProg, hC] using hV⟩

theorem numAnd_pXorCtrlHiToLo {M D n : ℕ} (r : RouterReg M D n) : (pXorCtrlHiToLo r).numAnd = 0 :=
  (pXorCtrlHiToLoLoop_props r M le_rfl).1

theorem progSupportedIn_pXorCtrlHiToLo {M D n : ℕ} {S : Wire n → Prop} (r : RouterReg M D n)
    (hLo : ∀ p, S (rCtrlLo r p)) (hHi : ∀ p, S (rCtrlHi r p)) : ProgSupportedIn S (pXorCtrlHiToLo r)
        :=
  Nat.rec (motive := fun k ↦ ∀ hk : k ≤ M, ProgSupportedIn S (pXorCtrlHiToLoLoop r k hk))
      (fun _ ↦ trivial)
    (fun _ ih hk ↦ ⟨ih (Nat.le_of_succ_le hk), hHi ⟨_, hk⟩, hLo ⟨_, hk⟩⟩) M le_rfl

private theorem fwdBits_pXorCtrlHiToLoLoop {M D n : ℕ} (r : RouterReg M D n) :
    ∀ (k : ℕ) (hk : k ≤ M) (δ : BitAssignment n),
      (∀ p : Fin M, p.val < k → (pXorCtrlHiToLoLoop r k hk).fwdBits δ (rCtrlLo r p) =
          δ (rCtrlLo r p) + δ (rCtrlHi r p)) ∧
      (∀ p : Fin M, k ≤ p.val → (pXorCtrlHiToLoLoop r k hk).fwdBits δ (rCtrlLo r p) =
          δ (rCtrlLo r p)) ∧
      (∀ w : Wire n, (∀ p : Fin M, w ≠ rCtrlLo r p) → (pXorCtrlHiToLoLoop r k hk).fwdBits δ w = δ w)
  | 0, _, _ => ⟨fun _ h ↦ absurd h (Nat.not_lt_zero _), fun _ _ ↦ rfl, fun _ _ ↦ rfl⟩
  | k + 1, hk, δ => by
      obtain ⟨ihLt, ihGe, ihOth⟩ := fwdBits_pXorCtrlHiToLoLoop r k (Nat.le_of_succ_le hk) δ
      let pk : Fin M := ⟨k, hk⟩
      have hneLo {a b : Fin M} (h : a ≠ b) : rCtrlLo r a ≠ rCtrlLo r b :=
        rr_ne r fun e ↦ Fin.val_ne_of_ne h (Nat.add_left_cancel e)
      dsimp only [pXorCtrlHiToLoLoop, ComputeProg.fwdBits]
      refine ⟨fun p hp ↦ ?_, fun p hp ↦ (Function.update_of_ne (hneLo fun e ↦
          (Nat.lt_of_succ_le hp).ne' (congrArg Fin.val e)) _ _).trans
          (ihGe p (Nat.le_of_succ_le hp)),
        fun w hw ↦ (Function.update_of_ne (hw pk) _ _).trans (ihOth w hw)⟩
      rcases eq_or_ne p pk with rfl | hpk
      · rw [Function.update_self, ihGe pk le_rfl, ihOth (rCtrlHi r pk) fun p ↦
          rr_ne r (by have := p.isLt; dsimp [rCtrlHi, rCtrlLo]; omega)]
      · exact (Function.update_of_ne (hneLo hpk) _ _).trans
          (ihLt p (Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp hp) (Fin.val_ne_of_ne hpk)))

theorem subspaceStep_wrap_pXorCtrlHiToLo {Var : Type} [Fintype Var] [DecidableEq Var]
    {M D n : ℕ} (v : Var) (r : RouterReg M D n) (mid : DynamicCircuit Var n)
        (R_in R_out : Operator (2 ^ n))
    (hMid : SubspaceStep (Var := Var) ((uPlaneXorCtrl (planeOfRouter (rHas2Alias r) 0)).1 * R_in)
      ((uPlaneXorCtrl (planeOfRouter (rHas2Alias r) 0)).1 * R_out) mid) :
    SubspaceStep (Var := Var) R_in R_out (wrapDyn v (pXorCtrlHiToLo r) mid) := by
  have hFXorEq : (fwdCirc (pXorCtrlHiToLo r)).eval.1 =
      (uPlaneXorCtrl (planeOfRouter (rHas2Alias r) 0)).1 := by
    refine KinB.matrix_ext_ket fun δ ↦ ?_
    rw [fwdCirc_mulVec_ket, ← ket_sr_eq, uPlaneXorCtrl_mulVec_ket, ket_sr_eq]
    obtain ⟨hLo, _, hOth⟩ := fwdBits_pXorCtrlHiToLoLoop r M le_rfl δ
    set pr0 := planeOfRouter (rHas2Alias r) 0
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, pr0CL, pr0CH, _⟩ :=
      planeOfRouter_rHas2Alias_roles r 0
    refine congrArg _ (funext fun w ↦ ?_)
    by_cases hw : ∃ p : Fin M, w = rCtrlLo r p
    · obtain ⟨p, rfl⟩ := hw
      rw [pXorCtrlHiToLo, hLo p p.isLt, (congrFun pr0CL p).symm, planeXorBits_ctrlLo,
        congrFun pr0CL p, congrFun pr0CH p]
    · exact (hOth w fun p e ↦ hw ⟨p, e⟩).trans
        (planeXorBits_other pr0 δ fun p e ↦ hw ⟨p, e.trans (congrFun pr0CL p)⟩).symm
  exact subspaceStep_wrapDyn v (pXorCtrlHiToLo r) ∅ mid R_in R_out
    (pXorCtrlHiToLoLoop_props r M le_rfl).2.2 (cleanProj_empty_mul R_in) (cleanProj_empty_mul R_out)
    (subspaceStep_congr_in (congrArg (· * R_in) hFXorEq)
      (subspaceStep_congr_out hMid (congrArg (· * R_out) hFXorEq.symm)))
theorem validWRouterBase_nuc {n : ℕ} (rn : RouterReg 47 6 n) {β : BitAssignment n}
    (hβ : ValidZeroGatedSortedRouterInput rn β) : ValidWRouterIn (rRawHas2 rn) (rIdx2 rn)
    (wOutHiN48 rn) (qEncNuc rn) β ∧ ValidWRouterClean (rRawHas2 rn) (rIdx2 rn)
    (wOutHiN48 rn) β ∧ ValidWRouterIn (rHas1 rn) (rIdx1 rn) (wOutLoN48 rn) (qEncNuc rn)
    (toggleOneHotBits (rRawHas2 rn) (rIdx2 rn) (wOutHiN48 rn) β) ∧ ValidWRouterClean (rHas1 rn)
    (rIdx1 rn) (wOutLoN48 rn) β := by
  have hCl {k : Fin (routerWidth 47 6)} (hk : basePub 47 6 ≤ k.val) : β (rn k) = 0 :=
    hβ.1.2.2.2.2 _ ((mem_sPrivCleanSet_iff rn k).mpr hk)
  have hHi0 := padWires_zero_of_zero (c := rCtrlHi rn) (pad := padHiN48 rn)
    (fun p ↦ hCl (Nat.le_trans (by decide) (Nat.le_add_right 1303 p.val))) fun _ ↦ hCl (by decide)
  have hLo0 := padWires_zero_of_zero (c := rCtrlLo rn) (pad := padLoN48 rn)
    (fun p ↦ hCl (Nat.le_trans (by decide) (Nat.le_add_right 1256 p.val))) fun _ ↦ hCl (by decide)
  have hQ0 : β (qEncNuc rn) = 0 := hCl (by decide)
  have hZ2 (h0 : β (rRawHas2 rn) = 0) := idxValD_eq_zero_of_zero _ (hβ.2.2.1 h0)
  have hZ1 (h0 : β (rHas1 rn) = 0) := idxValD_eq_zero_of_zero _ (hβ.2.1 h0)
  have hLt {w : Wire n} {idx : Fin 6 → Wire n} (hZ : β w = 0 → idxValD idx β = 0)
      (h1 : β w = 1 → idxValD idx β < 47) : idxValD idx β < 48 :=
    (zmod2_cases (β w)).elim (fun h0 ↦ (hZ h0).trans_lt (by decide)) fun ho ↦
      Nat.lt_succ_of_lt (h1 ho)
  have hL2 := hLt hZ2 hβ.1.2.2.1
  have hL1 := hLt hZ1 hβ.1.2.1
  have hOth {w : Wire n} (h : ∀ j, w ≠ wOutHiN48 rn j) :=
    toggleOneHotBits_apply_other (wHas := rRawHas2 rn) (wIdx := rIdx2 rn) β h
  have hI1 := idxValD_congr (rIdx1 rn) fun d ↦
    hOth (rn_ne_wOutHiN48 rn (Or.inl ((Nat.add_lt_add_left d.isLt 2).trans (by decide))))
  exact ⟨⟨hHi0, hQ0, hL2, hZ2⟩, ⟨hHi0, hL2, hZ2⟩,
    ⟨fun j ↦ (hOth (hne_wOutLoN48_wOutHiN48 rn j)).trans (hLo0 j),
     (hOth (rn_ne_wOutHiN48 rn (Or.inr ⟨by decide, by decide⟩))).trans hQ0, hI1 ▸ hL1,
     fun h0 ↦ hI1 ▸ hZ1 ((hOth (rn_ne_wOutHiN48 rn (Or.inl (by decide)))).symm.trans h0)⟩,
    ⟨hLo0, hL1, hZ1⟩⟩
end QuantumComputation.Specs.PhotochemistrySolution.WStateStage2Load
end
end
