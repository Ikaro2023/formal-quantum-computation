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

public import QuantumComputationDiscoveries.Algorithms.Photochemistry.Solution.WStateStage2LoadUnload
public import QuantumComputationDiscoveries.Algorithms.Photochemistry.Solution.Mux48CtrlSafeOracleBase
open QuantumComputation.Specs.PhotochemistrySolution.SpecDefs
open QuantumComputation.Specs.PhotochemistrySolution.QhlAux
open QuantumComputation.Specs.PhotochemistrySolution.PgBase
open QuantumComputation.Specs.PhotochemistrySolution.SelectBase
@[expose] public section

set_option allowUnsafeReducibility true

open QuantumComputation.Specs.PhotochemistrySolution.DynQromUncompA
  QuantumComputation.Specs.PhotochemistrySolution.SelectCsa64ProvSpec
  QuantumComputation.Specs.PhotochemistrySolution.SelectSandwich
open _root_.QuantumComputation.Specs.PhotochemistrySolution.OuterW11Bridge (concatBitsGen
    rCoinExtOut val_rCoinExtOut_bounds)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SelectCompactAnc (ancWOfScr
    totDimCompactGen locCat8SharedCompactGen cat8SharedProjCompactGen projOneQCompactGen
    OffIndexAndScratchPoly lcuProjPoly locSysPoly cat8SharedProjPoly projOneQPoly
    SelectLocalSpecGen)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Coin70Lift (circWires_toCircuit_c70
    circ_comm_embedMatrix_c70 projBits_c70 projBits_mulVec_ket_c70 projBits_eq_embedMatrix_c70
    rScrExt val_rScrExt scrLExt uStage1Clean_c70 muxMat_c70)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SplitBellVecCleanStep (zResetFixupDyn
    subspaceStep_of_circuit subspaceStep_seq_zResetFixup subspaceStep_congr_out cnotFanoutCirc
    count_cnotFanoutCirc_t count_cnotFanoutCirc_toff cnotFanoutCirc_mulVec_ket)
open scoped Matrix BigOperators
open QuantumComputation.Specs.PhotochemistrySolution.SubspaceMbu
  QuantumComputation.Specs.PhotochemistrySolution.FineLegendre
  QuantumComputation.Specs.PhotochemistrySolution.SelectKin526OneWrap
  QuantumComputation.Specs.PhotochemistrySolution.SelectOracles
  QuantumComputation.Specs.PhotochemistrySolution.Stage2ElecFirstZero
  QuantumComputation.Specs.PhotochemistrySolution.Stage5StackCore
  QuantumComputation.Specs.PhotochemistrySolution.UnembedO3Bridge
open QuantumComputation.Specs.PhotochemistrySolution.WStateMux48
set_option autoImplicit false
set_option maxRecDepth 16384
set_option exponentiation.threshold 256

namespace QuantumComputation.Specs.PhotochemistrySolution.Stage2ElecOptA
noncomputable section
open scoped ComplexOrder MatrixOrder Circuit.Notation
open Operator QProg Matrix Circuit Qubit HermitianMat PrimitiveGate QuantumComputation.Specs
  PhotochemistrySolution.KetSupport PhotochemistrySolution PhotochemistrySolution.XMeasUnld
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
open PhotochemistrySolution.SplitRouter47_187 PhotochemistrySolution.SplitRouterFredkinMux
  PhotochemistrySolution.SplitRouterMuxD1 PhotochemistrySolution.ProviderCore
  PhotochemistrySolution.Stage12Compact PhotochemistrySolution.ZeroNEremSpec
  PhotochemistrySolution.PotSelectWiring
open PhotochemistrySolution.Stage2QromMux PhotochemistrySolution.Stage2ZeroGated
  PhotochemistrySolution.Stage2ChDiffMux960 PhotochemistrySolution.Stage2ChDiffNoNF
  PhotochemistrySolution.Sub5885MuxD1 PhotochemistrySolution.Sub5885
  PhotochemistrySolution.WStateRouterPrim
open PhotochemistrySolution.HalfBellCollapse PhotochemistrySolution.PortBDualBellUnld
  PhotochemistrySolution.SortedRouterSpec PhotochemistrySolution.XMeasLinearCleanStep
open _root_.DynamicCircuit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt hiding bit_cases
  eval_seq_mulVec ket ket_CNOT ket_TOFF ket_X ket_projector_one ket_projector_zero localIdx
  matrix_ext_ket qAssign_obs_map_val
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB hiding bitSign eval_seq_mulVec ket
  ket_CNOT ket_TOFF ket_X localIdx matrix_ext_ket writeReg writeReg_apply_of_not_mem
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SplitRouterSeqBell26k hiding ket
  matrix_ext_ket
open _root_.QuantumComputation.Specs.PhotochemistrySolution.QubitizationWalkSem hiding bitSign
  bitSign_add bitSign_mul_self sqrtHalf sqrtHalf_mul_sqrtHalf star_sqrtHalf
open _root_.QuantumComputation.Specs.PhotochemistrySolution.RouterSelectWiringA (dLayout)
local instance (priority := 100000) {k : ℕ} : NeZero (2 ^ k) := ⟨pow_ne_zero k two_ne_zero⟩
section
attribute [local irreducible] systemQubits_frozen ancWOfScr
/- Section 1: wWork = 341 footprint, slice wires, Bell scratch buffer, and unload permutation -/
/--
Tight electronic `(187, 8)` Stage-2 Option A footprint (`privRank454Sub < 238`, fitting all
`341 ≤ wWork`, including `wWork = 341`, `346`, and `350`).
-/
def UsedNoNFW341 {n : ℕ} (r : RouterReg 187 8 n) (w : Wire n) : Prop :=
    ∃ j : Fin (routerWidth 187 8), w = r j ∧ (j.val < basePub 187 8 ∨ privRank454Sub (j.val -
    basePub 187 8) < 238)
abbrev UsedNoNFW346 {n : ℕ} (r : RouterReg 187 8 n) (w : Wire n) : Prop :=
  UsedNoNFW341 r w

/-- Explicit router-index predicate equivalent to `UsedNoNFW341`. -/
def NoNFW341Idx (j : ℕ) : Prop :=
    j < 4602 ∨ (4608 ≤ j ∧ j < 4811) ∨ (5000 ≤ j ∧ j < 5019) ∨ (5040 ≤ j ∧ j < 5056)
theorem usedNoNFW341_of_idx {n : ℕ} (r : RouterReg 187 8 n) (j : Fin (routerWidth 187 8))
    (hj : NoNFW341Idx j.val) : UsedNoNFW341 r (r j) := by
  refine ⟨j, rfl, hj.imp id fun h ↦ ?_⟩
  unfold privRank454Sub basePub
  split_ifs <;> omega
abbrev usedNoNFW346_of_idx := @usedNoNFW341_of_idx

theorem rw187_eq : routerWidth 187 8 = 5056 := rfl
theorem bp187_eq : basePub 187 8 = 4602 := rfl

/-- Router index in `NoNFW341Idx` for `wA24` (`[4608..4623] ++ [5007..5014]`). -/
def idxA24Val (q : ℕ) : ℕ := if q < 16 then 4608 + q else 5007 + (q - 16)
theorem idxA24Val_lt {q : ℕ} (hq : q < 24) : idxA24Val q < routerWidth 187 8 := by
  unfold idxA24Val routerWidth; split_ifs <;> omega
def idxB24Val (q : ℕ) : ℕ :=
    if q < 7 then 5000 + q else if q < 11 then 5015 + (q - 7) else if q < 12 then 5050 else if q <
    16 then 5052 + (q - 12) else 5040 + (q - 16)
theorem idxB24Val_lt {q : ℕ} (hq : q < 24) : idxB24Val q < routerWidth 187 8 := by
  unfold idxB24Val routerWidth; split_ifs <;> omega
abbrev wA24 {n : ℕ} (r : RouterReg 187 8 n) (q : Fin 24) : Wire n :=
  r ⟨idxA24Val q.val, idxA24Val_lt q.isLt⟩

/-- `24`-wire high-quotient slice `B_24` (`idx2 / 8`, CNOT-scrubbed during planes). -/
abbrev wB24 {n : ℕ} (r : RouterReg 187 8 n) (q : Fin 24) : Wire n :=
    r ⟨idxB24Val q.val, idxB24Val_lt q.isLt⟩
theorem rw187_lt_5048 : 5048 < routerWidth 187 8 := by unfold routerWidth; omega
theorem rw187_lt_5049 : 5049 < routerWidth 187 8 := by unfold routerWidth; omega
theorem rw187_lt_5051 : 5051 < routerWidth 187 8 := by unfold routerWidth; omega

/-- Shared coherent-coin ancilla `qEnc` (`r 5048`) for `S2_E` `W`-routers. -/
abbrev qEncE {n : ℕ} (r : RouterReg 187 8 n) : Wire n := r ⟨5048, rw187_lt_5048⟩

/-- Dummy child wire `w_dum` (`r 5049`) for dummy-assisted shift rounds. -/
abbrev wDumE {n : ℕ} (r : RouterReg 187 8 n) : Wire n := r ⟨5049, rw187_lt_5049⟩

/-- Parity accumulator wire `r_dum` (`r 5051`) for inactive roots in `cHi_E`. -/
abbrev rDumE {n : ℕ} (r : RouterReg 187 8 n) : Wire n := r ⟨5051, rw187_lt_5051⟩

theorem rw187_lt_buf96 (i : Fin 96) : 18 + i.val < routerWidth 187 8 := by
  have := i.isLt; unfold routerWidth; omega
/--
Contiguous `96`-wire public Bell buffer `r (18 + i)` (`rBufLo ++ rBufHi ++ rHA ++ rHB`),
clean `|0⟩^{96}` before `pDualBellPlanesMuxD1CHDiffNoNFMD` and reused as `cHi_E` `W` -expansion
scratch.
-/
abbrev buf96 {n : ℕ} (r : RouterReg 187 8 n) (i : Fin 96) : Wire n :=
    r ⟨18 + i.val, rw187_lt_buf96 i⟩
theorem buf96_zero_of_valid {n : ℕ} (r : RouterReg 187 8 n) {β : BitAssignment n}
    (hβ : ValidZeroGatedSortedRouterInput r β) (i : Fin 96) : β (buf96 r i) = 0 := by
  have hi := i.isLt
  have eq {j} (hz : β (r j) = 0) (h : 18 + i.val = j.val) : β (buf96 r i) = 0 :=
    (congrArg β (congrArg r.wires (Fin.ext h) : buf96 r i = r j)).trans hz
  if h1 : i.val < 24 then exact eq (hβ.1.2.2.2.1 ⟨i.val, h1⟩).1 rfl
  else if h2 : i.val < 48 then exact eq (hβ.1.2.2.2.1 ⟨i.val - 24, by omega⟩).2.1 (show 18 + i.val =
      42 + (i.val - 24) by omega)
  else if h3 : i.val < 72 then exact eq (hβ.1.2.2.2.1 ⟨i.val - 48, by omega⟩).2.2.1 (show 18 +
      i.val = 66 + (i.val - 48) by omega)
  else exact eq (hβ.1.2.2.2.1 ⟨i.val - 72, by omega⟩).2.2.2 (show 18 + i.val = 90 +
      (i.val - 72) by omega)
abbrev idxLo3_1 {n : ℕ} (r : RouterReg 187 8 n) (d : Fin 3) : Wire n :=
  rIdx1 r ⟨d.val, Nat.lt_of_lt_of_le d.isLt (by omega)⟩

abbrev idxHi5_1 {n : ℕ} (r : RouterReg 187 8 n) (d : Fin 5) : Wire n :=
  rIdx1 r ⟨3 + d.val, by have := d.isLt; omega⟩

abbrev idxLo3_2 {n : ℕ} (r : RouterReg 187 8 n) (d : Fin 3) : Wire n :=
  rIdx2 r ⟨d.val, Nat.lt_of_lt_of_le d.isLt (by omega)⟩

abbrev idxHi5_2 {n : ℕ} (r : RouterReg 187 8 n) (d : Fin 5) : Wire n :=
  rIdx2 r ⟨3 + d.val, by have := d.isLt; omega⟩

theorem routerOfInvol_apply {M D n : ℕ} (r : RouterReg M D n) (f : ℕ → ℕ)
    (hlt : ∀ j < routerWidth M D, f j < routerWidth M D)
    (hinv : ∀ j < routerWidth M D, f (f j) = j) (j : Fin (routerWidth M D)) :
    (routerOfInvol r f hlt hinv) j = r ⟨f j.val, hlt j.val j.isLt⟩ := rfl
theorem zg187_hM24 : 187 ≤ 2 ^ 3 * 24 := by decide
end
section
attribute [local semireducible] zResetFixupDyn projBit
/- Section 2a: Dummy-assisted W-shift round definition and pre-circuit action -/
/--
Pairwise disjointness bundle for a dummy-assisted W-shift round on `w : Fin R → Fin (2^k) → Wire n`
.
-/
structure WOptInj {n : ℕ} (R k : ℕ) (uLo : Fin k → Wire n)
    (w : Fin R → Fin (2 ^ k) → Wire n) (rDum wDum qEnc : Wire n) : Prop where
  w_inj : WInj w
  uLo_ne_w : ∀ d b p, uLo d ≠ w b p
  uLo_ne_rDum : ∀ d, uLo d ≠ rDum
  uLo_ne_wDum : ∀ d, uLo d ≠ wDum
  uLo_ne_qEnc : ∀ d, uLo d ≠ qEnc
  w_ne_rDum : ∀ b p, w b p ≠ rDum
  w_ne_wDum : ∀ b p, w b p ≠ wDum
  w_ne_qEnc : ∀ b p, w b p ≠ qEnc
  rDum_ne_wDum : rDum ≠ wDum
  rDum_ne_qEnc : rDum ≠ qEnc
  wDum_ne_qEnc : wDum ≠ qEnc

theorem update_eq_self_of_zero {n : ℕ} {δ : BitAssignment n} {q : Wire n}
    (h0 : δ q = 0) : Function.update δ q 0 = δ := h0 ▸ Function.update_eq_self q δ
theorem projBit_zero_mulVec_ket {n : ℕ} (q : Wire n) (δ : BitAssignment n) :
    (projBit q 0).mulVec (ket δ) = if δ q = 0 then ket δ else 0 := ket_projector_zero q δ
theorem ket_CNOT_ctrl_zero {n : ℕ} {c t : Wire n} (h : c ≠ t) {δ : BitAssignment n}
    (hc0 : δ c = 0) : (Circuit.CNOT c t h).eval.1.mulVec (ket δ) =
    ket δ := by rw [ket_CNOT c t h δ, hc0, add_zero, Function.update_eq_self]
theorem cnotOddToEnc_mulVec_ket_zero {n R k : ℕ} (w : Fin R → Fin (2 ^ k) → Wire n) (qEnc : Wire n)
    (hwq : ∀ b p, w b p ≠ qEnc) (d : ℕ) (δ : BitAssignment n) (hw0 : ∀ b p, δ (w b p) = 0) :
    (cnotOddToEnc R k w qEnc hwq d).eval.1.mulVec (ket δ) = ket δ :=
  seqNat_mulVec_fixed (ket δ) (R * 2 ^ k) _ fun _ _ ↦ by
    dsimp only; split_ifs
    · exact ket_CNOT_ctrl_zero _ (hw0 _ _)
    · rw [Circuit.eval_identity, Submonoid.coe_one, Matrix.one_mulVec]

theorem barrelSwap_mulVec_ket_zero {n R k : ℕ} (w : Fin R → Fin (2 ^ k) → Wire n) (hw : WInj w)
    (d : ℕ) (δ : BitAssignment n) (hw0 : ∀ b p, δ (w b p) = 0) :
    (barrelSwap R k w hw d).eval.1.mulVec (ket δ) = ket δ :=
  seqNat_mulVec_fixed (ket δ) (R * 2 ^ k) _ fun _ _ ↦ by
    dsimp only; split_ifs
    · exact swap3Cnot_mulVec_ket_zero _ _ _ δ (hw0 _ _) (hw0 _ _)
    · rw [Circuit.eval_identity, Submonoid.coe_one, Matrix.one_mulVec]

/-- Pre-measurement circuit of `wShiftDummyLevel`. -/
def wShiftDummyPre {n : ℕ} (R k : ℕ) (uLo : Fin k → Wire n) (w : Fin R → Fin (2 ^ k) → Wire n)
    (rDum wDum qEnc : Wire n) (hInj : WOptInj R k uLo w rDum wDum qEnc) (d : ℕ)
    (hd : d < k) : Circuit n :=
  chGateCirc rDum wDum hInj.rDum_ne_wDum ;;ᶜ
  cnotOddToEnc R k w qEnc hInj.w_ne_qEnc d ;;ᶜ
  Circuit.CNOT wDum qEnc hInj.wDum_ne_qEnc ;;ᶜ
  Circuit.CNOT (uLo ⟨d, hd⟩) qEnc (hInj.uLo_ne_qEnc ⟨d, hd⟩)

/-- Outcome-1 fixup circuit of `wShiftDummyLevel`. -/
def wShiftDummyFix {n : ℕ} (R k : ℕ) (uLo : Fin k → Wire n) (w : Fin R → Fin (2 ^ k) → Wire n)
    (rDum wDum qEnc : Wire n) (hInj : WOptInj R k uLo w rDum wDum qEnc) (d : ℕ) : Circuit n :=
  Circuit.CNOT rDum wDum hInj.rDum_ne_wDum ;;ᶜ
  barrelSwap R k w hInj.w_inj d

/-- Single `2-T` (`0 .TOFF`) dummy-assisted barrel-shift round at bit `d < k`. -/
def wShiftDummyLevel {Var : Type} {n : ℕ} (v : Var) (R k : ℕ) (uLo : Fin k → Wire n)
    (w : Fin R → Fin (2 ^ k) → Wire n) (rDum wDum qEnc : Wire n)
    (hInj : WOptInj R k uLo w rDum wDum qEnc) (d : ℕ) (hd : d < k) : DynamicCircuit Var n :=
    .seq (.circuit (wShiftDummyPre R k uLo w rDum wDum qEnc hInj d hd))
    (.seq (zResetFixupDyn v qEnc (wShiftDummyFix R k uLo w rDum wDum qEnc hInj d))
    (xUnloadCzPairsSeqDyn v wDum [⟨rDum, ⟨uLo ⟨d, hd⟩, (hInj.uLo_ne_rDum ⟨d, hd⟩).symm⟩⟩]
    (.circuit .identity)))
theorem count_wShiftDummyLevel {Var : Type} {n : ℕ} (v : Var) (R k : ℕ) (uLo : Fin k → Wire n)
    (w : Fin R → Fin (2 ^ k) → Wire n) (rDum wDum qEnc : Wire n)
    (hInj : WOptInj R k uLo w rDum wDum qEnc) (d : ℕ)
    (hd : d < k) : (wShiftDummyLevel v R k uLo w rDum wDum qEnc hInj d hd).count .T = 2 ∧
    (wShiftDummyLevel v R k uLo w rDum wDum qEnc hInj d hd).count .TOFF = 0 := by
  obtain ⟨tc, fc⟩ := count_chGateCirc rDum wDum hInj.rDum_ne_wDum; obtain ⟨to_, fo_⟩ :=
      count_cnotOddToEnc R k w qEnc hInj.w_ne_qEnc d; obtain ⟨tb, fb⟩ :=
      count_barrelSwap R k w hInj.w_inj d; obtain ⟨tx, fx⟩ :=
      count_xUnloadCzPairsSeqDyn v wDum [⟨rDum, ⟨uLo ⟨d, hd⟩, (hInj.uLo_ne_rDum ⟨d, hd⟩).symm⟩⟩]
      (.circuit .identity)
  refine ⟨?_, ?_⟩ <;>
    simp [wShiftDummyLevel, wShiftDummyPre, wShiftDummyFix, zResetFixupDyn, DynamicCircuit.count,
        Circuit.count_seq, Circuit.CNOT, Circuit.X, tc, fc, to_, fo_, tb, fb, tx, fx]

theorem dw_wShiftDummyLevel {Var : Type} {n : ℕ} {S : Wire n → Prop} (v : Var) (R k : ℕ)
    (uLo : Fin k → Wire n) (w : Fin R → Fin (2 ^ k) → Wire n) (rDum wDum qEnc : Wire n)
    (hInj : WOptInj R k uLo w rDum wDum qEnc) (huS : ∀ d, S (uLo d)) (hwS : ∀ b p, S (w b p))
    (hrS : S rDum) (hwdS : S wDum) (hqS : S qEnc) (d : ℕ)
    (hd : d < k) : DynWires S (wShiftDummyLevel v R k uLo w rDum wDum qEnc hInj d hd) := by
  exact ⟨cw_seq (cw_chGateCirc hrS hwdS) (cw_seq (cw_cnotOddToEnc _ _ _ _ _ _ hwS hqS)
      (cw_seq (cw_cnot hwdS hqS) (cw_cnot (huS _) hqS))),
    ⟨fun _ ↦ hqS, cw_seq (cw_1 hqS) (cw_seq (cw_cnot hrS hwdS) (cw_barrelSwap _ _ _ _ _ hwS)),
        trivial⟩,
    dw_xUnload hwdS (fun _ hp ↦ List.mem_singleton.mp hp ▸ ⟨hrS, huS _⟩) trivial⟩

/--
Optional shifted W-superposition vector at level `d ≤ k` (`wSuperVec` on `activePred` , `ket δ`
otherwise).
-/
def wOptSuperVec {n R k : ℕ} (P activePred : BitAssignment n → Prop) [DecidablePred P]
    [DecidablePred activePred] (bStarFn : BitAssignment n → Fin R) (uLo : Fin k → Wire n)
    (w : Fin R → Fin (2 ^ k) → Wire n) (wDum qEnc : Wire n) (δ : BitAssignment n) (d : ℕ)
    (hd : d ≤ k) : Fin (2 ^ n) → ℂ :=
  if P δ ∧ (∀ b p, δ (w b p) = 0) ∧ δ wDum = 0 ∧ δ qEnc = 0 then
    if activePred δ then wSuperVec bStarFn uLo w qEnc δ d hd else ket δ
  else 0

/-- Operator mapping computational basis kets via `wOptSuperVec`. -/
def wOptSuperOp {n R k : ℕ} (P activePred : BitAssignment n → Prop) [DecidablePred P]
    [DecidablePred activePred] (bStarFn : BitAssignment n → Fin R) (uLo : Fin k → Wire n)
    (w : Fin R → Fin (2 ^ k) → Wire n) (wDum qEnc : Wire n) (d : ℕ) (hd : d ≤ k) : Operator (2 ^ n)
    := mkVecOp fun δ ↦ wOptSuperVec P activePred bStarFn uLo w wDum qEnc δ d hd
theorem fDum_indep {n k : ℕ} (uLo : Fin k → Wire n) (rDum wDum qEnc : Wire n) {R : ℕ}
    {w : Fin R → Fin (2 ^ k) → Wire n} (hInj : WOptInj R k uLo w rDum wDum qEnc) (d : ℕ)
    (hd : d < k) (β : BitAssignment n)
    (a : ZMod 2) : czPairsParity [⟨rDum, ⟨uLo ⟨d, hd⟩, (hInj.uLo_ne_rDum ⟨d, hd⟩).symm⟩⟩]
    (Function.update β wDum a) =
    czPairsParity [⟨rDum,
    ⟨uLo ⟨d, hd⟩,
    (hInj.uLo_ne_rDum ⟨d,
    hd⟩).symm⟩⟩] β := by dsimp only [czPairsParity]; rw [Function.update_of_ne hInj.rDum_ne_wDum,
                           Function.update_of_ne (hInj.uLo_ne_wDum ⟨d, hd⟩)]
theorem wShiftDummy_pre_act {n R k : ℕ} (uLo : Fin k → Wire n)
    (w : Fin R → Fin (2 ^ k) → Wire n) (rDum wDum qEnc : Wire n)
    (hInj : WOptInj R k uLo w rDum wDum qEnc) (d : ℕ) (hd : d < k)
    (δ : BitAssignment n) (hr0 : δ rDum = 0) (hw0 : ∀ b p, δ (w b p) = 0)
    (hwd0 : δ wDum = 0) (hq0 : δ qEnc = 0) (b : Fin R) (p : Fin (2 ^ k)) :
    (wShiftDummyPre R k uLo w rDum wDum qEnc hInj d hd).eval.1.mulVec
        (ket (Function.update δ (w b p) 1)) =
    (cnotOddToEnc R k w qEnc hInj.w_ne_qEnc d ;;ᶜ
      Circuit.CNOT (uLo ⟨d, hd⟩) qEnc (hInj.uLo_ne_qEnc ⟨d, hd⟩)).eval.1.mulVec
        (ket (Function.update δ (w b p) 1)) := by
  let δ₁ := Function.update δ (w b p) 1;
  have hr1 : δ₁ rDum = 0 := (Function.update_of_ne (hInj.w_ne_rDum b p).symm 1 δ).trans hr0;
  have hwd1 : δ₁ wDum = 0 :=
      (Function.update_of_ne (hInj.w_ne_wDum b p).symm 1 δ).trans hwd0; dsimp only [wShiftDummyPre];
      simp only [eval_seq_mulVec]; rw [chGateCirc_mulVec_ket_zero rDum wDum hInj.rDum_ne_wDum δ₁
      hr1, cnotOddToEnc_mulVec_ket w qEnc hInj.w_inj hInj.w_ne_qEnc d δ hw0 hq0 b p,
      ket_CNOT_ctrl_zero _ ((Function.update_of_ne hInj.wDum_ne_qEnc _ δ₁).trans hwd1)]
theorem wShiftDummy_pre_inact {n R k : ℕ} (uLo : Fin k → Wire n) (w : Fin R → Fin (2 ^ k) → Wire n)
    (rDum wDum qEnc : Wire n) (hInj : WOptInj R k uLo w rDum wDum qEnc) (d : ℕ) (hd : d < k)
    (δ : BitAssignment n) (hr1 : δ rDum = 1) (hw0 : ∀ b p, δ (w b p) = 0) (hwd0 : δ wDum = 0)
    (hq0 : δ qEnc = 0) : (wShiftDummyPre R k uLo w rDum wDum qEnc hInj d hd).eval.1.mulVec (ket δ) =
    sqrtHalf • (ket (Function.update δ qEnc (δ (uLo ⟨d, hd⟩))) +
    ket (Function.update (Function.update δ wDum 1) qEnc (1 + δ (uLo ⟨d, hd⟩)))) := by
  simp only [wShiftDummyPre, eval_seq_mulVec]
  rw [chGateCirc_mulVec_ket_one rDum wDum hInj.rDum_ne_wDum δ hr1, ket_H wDum δ, hwd0,
    show bitSign (0 : ZMod 2) = (1 : ℂ) from rfl, one_smul, update_eq_self_of_zero hwd0]
  simp only [Matrix.mulVec_smul, Matrix.mulVec_add]
  refine congrArg (_ • ·) (congrArg₂ (· + ·) ?_ ?_)
  · rw [cnotOddToEnc_mulVec_ket_zero w qEnc hInj.w_ne_qEnc d δ hw0, ket_CNOT_ctrl_zero _ hwd0,
        ket_CNOT, hq0, zero_add]
  · rw [cnotOddToEnc_mulVec_ket_zero w qEnc hInj.w_ne_qEnc d _ fun b p ↦
        (Function.update_of_ne (hInj.w_ne_wDum b p) 1 δ).trans (hw0 b p),
      ket_CNOT, Function.update_of_ne hInj.wDum_ne_qEnc.symm, Function.update_self, hq0, zero_add,
      ket_CNOT, Function.update_self, Function.update_of_ne (hInj.uLo_ne_qEnc ⟨d, hd⟩),
      Function.update_of_ne (hInj.uLo_ne_wDum ⟨d, hd⟩), Function.update_idem]
end
/- Section 2b1: Dummy parity unitary and outcome-0 branch identity for `wShiftDummyLevel` -/
/-- Dummy-ancilla parity unitary toggled by `rDum * uLo[d]` before X-measurement unload. -/
def uDumShift {n R k : ℕ} (uLo : Fin k → Wire n) (w : Fin R → Fin (2 ^ k) → Wire n)
    (rDum wDum qEnc : Wire n) (hInj : WOptInj R k uLo w rDum wDum qEnc) (d : ℕ)
    (hd : d < k) : unitaryGroup (Fin (2 ^ n)) ℂ :=
    xorWireUnitary wDum (czPairsParity [⟨rDum, ⟨uLo ⟨d, hd⟩, (hInj.uLo_ne_rDum ⟨d, hd⟩).symm⟩⟩])
    (fDum_indep uLo rDum wDum qEnc hInj d hd)
theorem uDumShift_act {n R k : ℕ} (uLo : Fin k → Wire n) (w : Fin R → Fin (2 ^ k) → Wire n)
    (rDum wDum qEnc : Wire n) (hInj : WOptInj R k uLo w rDum wDum qEnc) (d : ℕ) (hd : d < k)
    (δ : BitAssignment n) (hr0 : δ rDum = 0) (hwd0 : δ wDum = 0) (b : Fin R)
    (p : Fin (2 ^ k)) :
    (uDumShift uLo w rDum wDum qEnc hInj d hd).1.mulVec (ket (Function.update δ (w b p) 1)) =
    ket (Function.update δ (w b p) 1) := by
  dsimp only [uDumShift]; rw [xorWireUnitary_mulVec_ket]
  have h1 : czPairsParity [⟨rDum, ⟨uLo ⟨d, hd⟩, (hInj.uLo_ne_rDum ⟨d, hd⟩).symm⟩⟩]
      (Function.update δ (w b p) 1) =
      0 := by dsimp only [czPairsParity]; rw [Function.update_of_ne (hInj.w_ne_rDum b p).symm, hr0,
                zero_mul, add_zero]
  have h2 : Function.update δ (w b p) 1 wDum = 0 :=
      (Function.update_of_ne (hInj.w_ne_wDum b p).symm 1 δ).trans hwd0; rw [h1, h2, add_zero,
      update_eq_self_of_zero h2]
theorem uDumShift_inact {n R k : ℕ} (uLo : Fin k → Wire n) (w : Fin R → Fin (2 ^ k) → Wire n)
    (rDum wDum qEnc : Wire n) (hInj : WOptInj R k uLo w rDum wDum qEnc) (d : ℕ) (hd : d < k)
    (δ : BitAssignment n) (hr1 : δ rDum = 1) (hwd0 : δ wDum = 0) :
    (uDumShift uLo w rDum wDum qEnc hInj d hd).1.mulVec (ket δ) =
    ket (Function.update δ wDum (δ (uLo ⟨d, hd⟩))) := by
  dsimp only [uDumShift]; rw [xorWireUnitary_mulVec_ket]
  have h1 : czPairsParity [⟨rDum, ⟨uLo ⟨d, hd⟩, (hInj.uLo_ne_rDum ⟨d, hd⟩).symm⟩⟩] δ =
      δ (uLo ⟨d, hd⟩) := by dsimp only [czPairsParity]; rw [hr1, one_mul, add_zero]
  rw [h1, hwd0, zero_add]

theorem wShiftDummy_branch0 {n R k : ℕ} (P activePred : BitAssignment n → Prop) [DecidablePred P]
    [DecidablePred activePred] (bStarFn : BitAssignment n → Fin R) (uLo : Fin k → Wire n)
    (w : Fin R → Fin (2 ^ k) → Wire n) (rDum wDum qEnc : Wire n)
    (hInj : WOptInj R k uLo w rDum wDum qEnc)
    (hDumBit : ∀ δ, P δ → δ rDum = (if activePred δ then 0 else 1)) (d : ℕ)
    (hd : d < k) : (QRegister.singleton qEnc).basisOutcomeProjector 0 *
    ((wShiftDummyPre R k uLo w rDum wDum qEnc hInj d hd).eval.1 *
    wOptSuperOp P activePred bStarFn uLo w wDum qEnc d (Nat.le_of_lt hd)) =
    sqrtHalf • ((uDumShift uLo w rDum wDum qEnc hInj d hd).1 *
    wOptSuperOp P activePred bStarFn uLo w wDum qEnc (d + 1) hd) := by
  let P₀ := (QRegister.singleton qEnc).basisOutcomeProjector 0;
  let cPreFull := wShiftDummyPre R k uLo w rDum wDum qEnc hInj d hd;
  let UDum := uDumShift uLo w rDum wDum qEnc hInj d hd
  have hev (q : Fin (2 ^ (k - (d + 1)))) : ¬ decide (2 * q.val % 2 = 1) = true :=
      Bool.eq_false_iff.mp (decide_eq_false (by omega))
  have hod (q : Fin (2 ^ (k - (d + 1)))) : decide ((2 * q.val + 1) % 2 = 1) = true :=
      decide_eq_true (by omega)
  have hPow2 : 2 ^ (k - d) = 2 * 2 ^ (k - (d + 1)) := by
    rw [show k - d = k - (d + 1) + 1 by omega, Nat.pow_succ']
  have hEv (q : Fin (2 ^ (k - (d + 1)))) : 2 * q.val < 2 ^ (k - d) := (fun _ ↦ by omega) q.isLt
  have hOd (q : Fin (2 ^ (k - (d + 1)))) : 2 * q.val + 1 < 2 ^ (k - d) := (fun _ ↦ by omega) q.isLt
  apply matrix_ext_ket; intro δ
  simp only [← Matrix.mulVec_mulVec, Matrix.smul_mulVec, wOptSuperOp, mkVecOp_mulVec_ket,
      wOptSuperVec]
  by_cases hV : P δ ∧ (∀ b p, δ (w b p) = 0) ∧ δ wDum = 0 ∧ δ qEnc = 0
  · have ⟨hP, hw0, hwd0, hq0⟩ := hV; rw [ite_eq_left hV, ite_eq_left hV]
    by_cases hAct : activePred δ
    · have hr0 : δ rDum = 0 :=
          (hDumBit δ hP).trans (ite_eq_left hAct); rw [ite_eq_left hAct,
          ite_eq_left hAct]; dsimp only [wSuperVec]; rw [ite_eq_left ⟨hw0, hq0⟩, ite_eq_left ⟨hw0,
          hq0⟩, Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.mulVec_sum,
          Matrix.mulVec_sum, Matrix.mulVec_sum]
      rw [show sqrtHalf ^ (k - d) = sqrtHalf * sqrtHalf ^ (k - (d + 1)) by
        rw [show k - d = k - (d + 1) + 1 by omega, _root_.pow_succ'], smul_smul]
      congr 1
      conv_rhs =>
          rw [Finset.sum_congr rfl fun _ _ ↦
          uDumShift_act uLo w rDum wDum qEnc hInj d hd δ hr0 hwd0 _ _]
      let e := (finTwoMulEquiv (2 ^ (k - (d + 1)))).trans (finCongr hPow2.symm)
      rw [← e.sum_comp, Fintype.sum_sum_type]; let lo := idxValPrefix uLo δ d (Nat.le_of_lt hd);
      have hlo : lo < 2 ^ d := idxValPrefix_lt_two_pow uLo δ d (Nat.le_of_lt hd);
      let kIn (hi : ℕ) (hhi : hi < 2 ^ (k - d)) :=
          ket (Function.update δ (w (bStarFn δ)
          ⟨lo + 2 ^ d * hi,
          shift_pos_lt (Nat.le_of_lt hd) hlo hhi⟩) 1); let kOut (q : Fin (2 ^ (k - (d + 1)))) :=
                                                         ket (Function.update δ (w (bStarFn δ)
                                                         ⟨idxValPrefix uLo δ (d + 1) hd +
                                                         2 ^ (d + 1) * q.val,
                                                         shift_pos_lt hd (idxValPrefix_lt_two_pow
                                                         uLo δ (d +
                                                         1) hd) q.isLt⟩) 1); change (∑ q : Fin
                                                         (2 ^ (k - (d + 1))),
                                                         P₀.mulVec (cPreFull.eval.1.mulVec (kIn (2 *
                                                         q.val)
                                                         (hEv q)))) +
                                                         (∑ q : Fin (2 ^ (k - (d + 1))),
                                                         P₀.mulVec (cPreFull.eval.1.mulVec (kIn (2 *
                                                         q.val + 1)
                                                         (hOd q)))) = ∑ q : Fin (2 ^ (k - (d + 1))),
                                                         kOut q
      have hPre {hi : ℕ} (hhi : hi < 2 ^ (k - d)) :=
        cnotOddAndIdx_mulVec_ket uLo w qEnc hInj.w_inj hInj.w_ne_qEnc hInj.uLo_ne_qEnc
          hInj.uLo_ne_w d hd δ hw0 hq0 (bStarFn δ) hhi
      have hqId (p : Fin (2 ^ k)) : Function.update (Function.update δ (w (bStarFn δ) p) 1) qEnc 0 =
          Function.update δ (w (bStarFn δ) p) 1 :=
          update_eq_self_of_zero ((Function.update_of_ne (hInj.w_ne_qEnc _ _).symm 1 δ).trans hq0)
      have ketEq {a b : ℕ} {ha : a < 2 ^ k} {hb : b < 2 ^ k} (h : a = b) :
          ket (Function.update δ (w (bStarFn δ) ⟨a, ha⟩) 1) = ket (Function.update δ (w (bStarFn δ)
              ⟨b, hb⟩) 1) :=
        congrArg (fun p ↦ ket (Function.update δ (w (bStarFn δ) p) 1)) (Fin.ext h)
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun q _ ↦ ?_
      dsimp only [P₀, cPreFull, kIn, kOut]
      rw [wShiftDummy_pre_act uLo w rDum wDum qEnc hInj d hd δ hr0 hw0 hwd0 hq0 _ _, hPre (hEv q),
          ite_eq_right (hev q),
        wShiftDummy_pre_act uLo w rDum wDum qEnc hInj d hd δ hr0 hw0 hwd0 hq0 _ _, hPre (hOd q),
            ite_eq_left (hod q)]
      rcases DynCircExt.bit_cases (δ (uLo ⟨d, hd⟩)) with hu0 | hu1
      · rw [hu0, add_zero, add_zero, ket_projector_zero, Function.update_self, ite_eq_left rfl,
          ket_projector_zero, Function.update_self, ite_eq_right one_ne_zero, add_zero, hqId]
        exact ketEq
            (by simpa only [idxValPrefix, lo, ite_eq_right (hu0 ▸ zero_ne_one)] using by ring)
      · rw [hu1, zero_add, CharTwo.add_self_eq_zero, ket_projector_zero, Function.update_self,
            ite_eq_right one_ne_zero,
          ket_projector_zero, Function.update_self, ite_eq_left rfl, zero_add, hqId]
        exact ketEq (by simpa only [idxValPrefix, lo, ite_eq_left hu1] using by ring)
    · have hr1 : δ rDum = 1 :=
          (hDumBit δ hP).trans (ite_eq_right hAct); rw [ite_eq_right hAct, ite_eq_right hAct,
          uDumShift_inact uLo w rDum wDum qEnc hInj d hd δ hr1 hwd0,
          wShiftDummy_pre_inact uLo w rDum wDum qEnc hInj d hd δ hr1 hw0 hwd0 hq0,
          Matrix.mulVec_smul, Matrix.mulVec_add]; congr 1
      rcases DynCircExt.bit_cases (δ (uLo ⟨d, hd⟩)) with hu0 | hu1
      · rw [hu0, add_zero, ket_projector_zero, Function.update_self, ite_eq_left rfl,
            ket_projector_zero, Function.update_self, ite_eq_right one_ne_zero, add_zero,
            update_eq_self_of_zero hq0, update_eq_self_of_zero hwd0]
      · have hq0w := (Function.update_of_ne hInj.wDum_ne_qEnc.symm 1 δ).trans hq0
        rw [hu1, CharTwo.add_self_eq_zero, ket_projector_zero, Function.update_self,
            ite_eq_right one_ne_zero, ket_projector_zero, Function.update_self, ite_eq_left rfl,
            zero_add, update_eq_self_of_zero hq0w]
  · simp only [ite_eq_right hV, Matrix.mulVec_zero, smul_zero]
section
attribute [local semireducible] zResetFixupDyn projBit
attribute [local irreducible] wShiftDummyFix wShiftDummyPre uDumShift barrelSwap
/- Section 2b2: Outcome-1 branch identity and `subspaceStep_wShiftDummyLevel` -/
theorem wShiftDummy_branch1 {n R k : ℕ} (P activePred : BitAssignment n → Prop) [DecidablePred P]
    [DecidablePred activePred] (bStarFn : BitAssignment n → Fin R) (uLo : Fin k → Wire n)
    (w : Fin R → Fin (2 ^ k) → Wire n) (rDum wDum qEnc : Wire n)
    (hInj : WOptInj R k uLo w rDum wDum qEnc)
    (hDumBit : ∀ δ, P δ → δ rDum = (if activePred δ then 0 else 1)) (d : ℕ)
    (hd : d < k) : (wShiftDummyFix R k uLo w rDum wDum qEnc hInj d).eval.1 *
    (Circuit.X qEnc).eval.1 * (QRegister.singleton qEnc).basisOutcomeProjector 1 *
    ((wShiftDummyPre R k uLo w rDum wDum qEnc hInj d hd).eval.1 *
    wOptSuperOp P activePred bStarFn uLo w wDum qEnc d (Nat.le_of_lt hd)) =
    sqrtHalf • ((uDumShift uLo w rDum wDum qEnc hInj d hd).1 *
    wOptSuperOp P activePred bStarFn uLo w wDum qEnc (d + 1) hd) := by
  let F₁ :=
      (wShiftDummyFix R k uLo w rDum wDum qEnc hInj d).eval.1 * (Circuit.X qEnc).eval.1 *
      (QRegister.singleton qEnc).basisOutcomeProjector 1; let cPreFull :=
                                                            wShiftDummyPre R k uLo w rDum wDum qEnc
                                                            hInj d hd;
                                                            let cFixFull :=
                                                            wShiftDummyFix R k uLo w rDum wDum qEnc
                                                            hInj d;
                                                            let cB :=
                                                            barrelSwap R k w hInj.w_inj d;
                                                            let UDum :=
                                                            uDumShift uLo w rDum wDum qEnc hInj d hd
  have hev (q : Fin (2 ^ (k - (d + 1)))) : ¬ decide (2 * q.val % 2 = 1) = true :=
      Bool.eq_false_iff.mp (decide_eq_false (by omega))
  have hod (q : Fin (2 ^ (k - (d + 1)))) : decide ((2 * q.val + 1) % 2 = 1) = true :=
      decide_eq_true (by omega)
  have hPow2 : 2 ^ (k - d) = 2 * 2 ^ (k - (d + 1)) := by
    rw [show k - d = k - (d + 1) + 1 by omega, Nat.pow_succ']
  have hEv (q : Fin (2 ^ (k - (d + 1)))) : 2 * q.val < 2 ^ (k - d) := (fun _ ↦ by omega) q.isLt
  have hOd (q : Fin (2 ^ (k - (d + 1)))) : 2 * q.val + 1 < 2 ^ (k - d) := (fun _ ↦ by omega) q.isLt
  refine matrix_ext_ket fun δ ↦ ?_
  rw [← Matrix.mulVec_mulVec (ket δ) F₁, ← Matrix.mulVec_mulVec (ket δ) cPreFull.eval.1,
    Matrix.smul_mulVec, ← Matrix.mulVec_mulVec (ket δ) UDum.1,
    wOptSuperOp, mkVecOp_mulVec_ket, wOptSuperOp, mkVecOp_mulVec_ket]
  dsimp only [wOptSuperVec]
  by_cases hV : P δ ∧ (∀ b p, δ (w b p) = 0) ∧ δ wDum = 0 ∧ δ qEnc = 0
  · have ⟨hP, hw0, hwd0, hq0⟩ := hV; rw [ite_eq_left hV, ite_eq_left hV]
    by_cases hAct : activePred δ
    · have hr0 : δ rDum = 0 :=
          (hDumBit δ hP).trans (ite_eq_left hAct); rw [ite_eq_left hAct,
          ite_eq_left hAct]; dsimp only [wSuperVec]; rw [ite_eq_left ⟨hw0, hq0⟩, ite_eq_left ⟨hw0,
          hq0⟩, Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.mulVec_sum,
          Matrix.mulVec_sum, Matrix.mulVec_sum]
      rw [show sqrtHalf ^ (k - d) = sqrtHalf * sqrtHalf ^ (k - (d + 1)) by
        rw [show k - d = k - (d + 1) + 1 by omega, _root_.pow_succ'], smul_smul]
      congr 1
      conv_rhs =>
          rw [Finset.sum_congr rfl fun _ _ ↦
          uDumShift_act uLo w rDum wDum qEnc hInj d hd δ hr0 hwd0 _ _]
      let e := (finTwoMulEquiv (2 ^ (k - (d + 1)))).trans (finCongr hPow2.symm)
      rw [← e.sum_comp, Fintype.sum_sum_type]; let lo := idxValPrefix uLo δ d (Nat.le_of_lt hd);
      have hlo : lo < 2 ^ d := idxValPrefix_lt_two_pow uLo δ d (Nat.le_of_lt hd);
      let kIn (hi : ℕ) (hhi : hi < 2 ^ (k - d)) :=
          ket (Function.update δ (w (bStarFn δ)
          ⟨lo + 2 ^ d * hi,
          shift_pos_lt (Nat.le_of_lt hd) hlo hhi⟩) 1); let kOut (q : Fin (2 ^ (k - (d + 1)))) :=
                                                         ket (Function.update δ (w (bStarFn δ)
                                                         ⟨idxValPrefix uLo δ (d + 1) hd +
                                                         2 ^ (d + 1) * q.val,
                                                         shift_pos_lt hd (idxValPrefix_lt_two_pow
                                                         uLo δ (d +
                                                         1) hd) q.isLt⟩) 1); change (∑ q : Fin
                                                         (2 ^ (k - (d + 1))),
                                                         F₁.mulVec (cPreFull.eval.1.mulVec (kIn (2 *
                                                         q.val)
                                                         (hEv q)))) +
                                                         (∑ q : Fin (2 ^ (k - (d + 1))),
                                                         F₁.mulVec (cPreFull.eval.1.mulVec (kIn (2 *
                                                         q.val + 1)
                                                         (hOd q)))) = ∑ q : Fin (2 ^ (k - (d + 1))),
                                                         kOut q
      have hPre {hi : ℕ} (hhi : hi < 2 ^ (k - d)) :=
        cnotOddAndIdx_mulVec_ket uLo w qEnc hInj.w_inj hInj.w_ne_qEnc hInj.uLo_ne_qEnc
          hInj.uLo_ne_w d hd δ hw0 hq0 (bStarFn δ) hhi
      have hqId (p : Fin (2 ^ k)) : Function.update (Function.update δ (w (bStarFn δ) p) 1) qEnc 0 =
          Function.update δ (w (bStarFn δ) p) 1 :=
          update_eq_self_of_zero ((Function.update_of_ne (hInj.w_ne_qEnc _ _).symm 1 δ).trans hq0)
      have ketEq {a b : ℕ} {ha : a < 2 ^ k} {hb : b < 2 ^ k} (h : a = b) :
          ket (Function.update δ (w (bStarFn δ) ⟨a, ha⟩) 1) = ket (Function.update δ (w (bStarFn δ)
              ⟨b, hb⟩) 1) :=
        congrArg (fun p ↦ ket (Function.update δ (w (bStarFn δ) p) 1)) (Fin.ext h)
      have hpLo (q : Fin (2 ^ (k - (d + 1)))) : lo + 2 ^ d * (2 * q.val) < 2 ^ k :=
        shift_pos_lt (Nat.le_of_lt hd) hlo (hEv q)
      have htbLo (q : Fin (2 ^ (k - (d + 1)))) : (lo + 2 ^ d * (2 * q.val)).testBit d = false :=
        (testBit_lo_add_mul_two_pow hlo).trans (decide_eq_false (by omega))
      have hpHi (q : Fin (2 ^ (k - (d + 1)))) : (lo + 2 ^ d * (2 * q.val)) + 2 ^ d < 2 ^ k := by
        rw [show (lo + 2 ^ d * (2 * q.val)) + 2 ^ d = lo + 2 ^ d * (2 * q.val + 1) by ring]
        exact shift_pos_lt (Nat.le_of_lt hd) hlo (hOd q)
      have hFixEq (p : Fin (2 ^ k)) :
          cFixFull.eval.1.mulVec (ket (Function.update δ (w (bStarFn δ) p) 1)) =
          cB.eval.1.mulVec (ket (Function.update δ (w (bStarFn δ) p) 1))
          := by change (wShiftDummyFix R k uLo w rDum wDum qEnc hInj d).eval.1.mulVec _ =
                  _; unfold wShiftDummyFix; rw [eval_seq_mulVec,
                  ket_CNOT_ctrl_zero _ ((Function.update_of_ne (hInj.w_ne_rDum _ p).symm 1 δ).trans
                  hr0)]
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun q _ ↦ ?_
      dsimp only [F₁, kIn, kOut]
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
        wShiftDummy_pre_act uLo w rDum wDum qEnc hInj d hd δ hr0 hw0 hwd0 hq0 _ _, hPre (hEv q),
            ite_eq_right (hev q),
        ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
        wShiftDummy_pre_act uLo w rDum wDum qEnc hInj d hd δ hr0 hw0 hwd0 hq0 _ _, hPre (hOd q),
            ite_eq_left (hod q)]
      rcases DynCircExt.bit_cases (δ (uLo ⟨d, hd⟩)) with hu0 | hu1
      · rw [hu0, add_zero, add_zero, ket_projector_one, Function.update_self,
            ite_eq_right zero_ne_one,
          Matrix.mulVec_zero, Matrix.mulVec_zero, zero_add, ket_projector_one, Function.update_self,
              ite_eq_left rfl,
          ket_X, Function.update_self, CharTwo.add_self_eq_zero, Function.update_idem, hqId, hFixEq,
          show (⟨lo + 2 ^ d * (2 * q.val + 1),
              shift_pos_lt (Nat.le_of_lt hd) hlo (hOd q)⟩ : Fin (2 ^ k)) =
            if true then ⟨(lo + 2 ^ d * (2 * q.val)) + 2 ^ d, hpHi q⟩ else ⟨_, hpLo q⟩ from
            Fin.ext (show lo + 2 ^ d * (2 * q.val + 1) = (lo + 2 ^ d * (2 * q.val)) +
                2 ^ d by ring),
          barrelSwap_mulVec_ket_pair w hInj.w_inj d δ hw0 (bStarFn δ) (hpLo q) (htbLo q)
              (hpHi q) true]
        exact ketEq
            (by simpa only [idxValPrefix, lo, ite_eq_right (hu0 ▸ zero_ne_one)] using by ring)
      · rw [hu1, zero_add, CharTwo.add_self_eq_zero, ket_projector_one, Function.update_self,
            ite_eq_left rfl,
          ket_projector_one, Function.update_self, ite_eq_right zero_ne_one, Matrix.mulVec_zero,
              Matrix.mulVec_zero,
          add_zero, ket_X, Function.update_self, CharTwo.add_self_eq_zero, Function.update_idem,
              hqId, hFixEq]
        exact (barrelSwap_mulVec_ket_pair w hInj.w_inj d δ hw0 (bStarFn δ) (hpLo q) (htbLo q)
            (hpHi q) false).trans
          (ketEq (by simpa only [idxValPrefix, lo, ite_eq_left hu1] using by ring))
    · have hr1 : δ rDum = 1 :=
          (hDumBit δ hP).trans (ite_eq_right hAct); rw [ite_eq_right hAct, ite_eq_right hAct,
          ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
          uDumShift_inact uLo w rDum wDum qEnc hInj d hd δ hr1 hwd0,
          wShiftDummy_pre_inact uLo w rDum wDum qEnc hInj d hd δ hr1 hw0 hwd0 hq0,
          Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.mulVec_add,
          Matrix.mulVec_add, Matrix.mulVec_add]; congr 1
      rcases DynCircExt.bit_cases (δ (uLo ⟨d, hd⟩)) with hu0 | hu1
      · have hq0w := (Function.update_of_ne hInj.wDum_ne_qEnc.symm 1 δ).trans hq0
        rw [hu0, add_zero, ket_projector_one, Function.update_self, ite_eq_right zero_ne_one,
            Matrix.mulVec_zero, Matrix.mulVec_zero, zero_add, ket_projector_one,
            Function.update_self, ite_eq_left rfl, ket_X, Function.update_self,
            CharTwo.add_self_eq_zero, Function.update_idem, update_eq_self_of_zero hq0w]
        unfold wShiftDummyFix; rw [eval_seq_mulVec, ket_CNOT, Function.update_self,
          Function.update_of_ne hInj.rDum_ne_wDum, hr1, CharTwo.add_self_eq_zero,
          Function.update_idem, update_eq_self_of_zero hwd0,
          barrelSwap_mulVec_ket_zero w hInj.w_inj d δ hw0]
      · rw [hu1, CharTwo.add_self_eq_zero, ket_projector_one, Function.update_self, ite_eq_left rfl,
            ket_projector_one, Function.update_self, ite_eq_right zero_ne_one, Matrix.mulVec_zero,
            Matrix.mulVec_zero, add_zero, ket_X, Function.update_self, CharTwo.add_self_eq_zero,
            Function.update_idem, update_eq_self_of_zero hq0]
        unfold wShiftDummyFix; rw [eval_seq_mulVec, ket_CNOT, hr1, hwd0, zero_add]
        exact barrelSwap_mulVec_ket_zero w hInj.w_inj d (Function.update δ wDum 1) fun b p ↦
            (Function.update_of_ne (hInj.w_ne_wDum b p) 1 δ).trans (hw0 b p)
  · simp only [ite_eq_right hV, Matrix.mulVec_zero, smul_zero]

theorem subspaceStep_wShiftDummyLevel {Var : Type} [Fintype Var] [DecidableEq Var] {n R k : ℕ}
    (v : Var) (P activePred : BitAssignment n → Prop) [DecidablePred P] [DecidablePred activePred]
    (bStarFn : BitAssignment n → Fin R) (uLo : Fin k → Wire n) (w : Fin R → Fin (2 ^ k) → Wire n)
    (rDum wDum qEnc : Wire n) (hInj : WOptInj R k uLo w rDum wDum qEnc)
    (hDumBit : ∀ δ, P δ → δ rDum = (if activePred δ then 0 else 1)) (d : ℕ)
    (hd : d < k) :
    SubspaceStep (wOptSuperOp P activePred bStarFn uLo w wDum qEnc d (Nat.le_of_lt hd))
    (wOptSuperOp P activePred bStarFn uLo w wDum qEnc (d + 1) hd)
    (wShiftDummyLevel v R k uLo w rDum wDum qEnc hInj d hd) := by
  let pairs : List (WirePair n) := [⟨rDum, ⟨uLo ⟨d, hd⟩, (hInj.uLo_ne_rDum ⟨d, hd⟩).symm⟩⟩];
  let R_in := wOptSuperOp P activePred bStarFn uLo w wDum qEnc d (Nat.le_of_lt hd);
  let R_out := wOptSuperOp P activePred bStarFn uLo w wDum qEnc (d + 1) hd;
  let UDum := uDumShift uLo w rDum wDum qEnc hInj d hd
  have hProjWDum0 : projBit wDum 0 * R_out = R_out := matrix_ext_ket fun δ ↦ by
    simp only [← Matrix.mulVec_mulVec, R_out, wOptSuperOp, mkVecOp_mulVec_ket, wOptSuperVec]
    if hV : P δ ∧ (∀ b p, δ (w b p) = 0) ∧ δ wDum = 0 ∧ δ qEnc = 0 then
      rw [ite_eq_left hV]
      if hAct : activePred δ then
        rw [ite_eq_left hAct, wSuperVec, ite_eq_left ⟨hV.2.1, hV.2.2.2⟩, Matrix.mulVec_smul,
            Matrix.mulVec_sum]
        exact congrArg (_ • ·) (Finset.sum_congr rfl fun _ _ ↦ by
          rw [projBit_zero_mulVec_ket,
              ite_eq_left ((Function.update_of_ne (hInj.w_ne_wDum _ _).symm 1 δ).trans hV.2.2.1)])
      else rw [ite_eq_right hAct, projBit_zero_mulVec_ket, ite_eq_left hV.2.2.1]
    else rw [ite_eq_right hV, Matrix.mulVec_zero]
  have hUnload : SubspaceStep (UDum.1 *
      R_out) R_out (xUnloadCzPairsSeqDyn v wDum pairs (.circuit .identity)) := by
    unfold UDum uDumShift
    exact subspaceStep_xUnloadCzPairsSeqDyn v wDum pairs (.circuit .identity) (czPairsParity pairs)
      (fDum_indep uLo rDum wDum qEnc hInj d hd) (fun _ ↦ rfl) R_out R_out hProjWDum0
      (by simpa only [Circuit.eval_identity, Submonoid.coe_one, Matrix.one_mul] using
        subspaceStep_of_circuit (Var := Var) R_out .identity)
  have hShift : SubspaceStep R_in (UDum.1 * R_out)
      (.seq (.circuit (wShiftDummyPre R k uLo w rDum wDum qEnc hInj d hd))
      (zResetFixupDyn v qEnc (wShiftDummyFix R k uLo w rDum wDum qEnc hInj d))) :=
      subspaceStep_seq_zResetFixup v qEnc _ (subspaceStep_of_circuit R_in _)
      (wShiftDummy_branch0 P activePred bStarFn uLo w rDum wDum qEnc hInj hDumBit d hd)
      (wShiftDummy_branch1 P activePred bStarFn uLo w rDum wDum qEnc hInj hDumBit d hd);
      dsimp only [wShiftDummyLevel]; exact hShift.seq hUnload
end
section
attribute [local semireducible] projBit
/-
Section 2c1: Base definitions, resource counts, and measurement prefix for optional MBU uncompute
-/
theorem qUp_ne_of_ne_opt {n R k : ℕ} {w : Fin R → Fin (2 ^ k) → Wire n} (hw : WInj w)
    {r : ℕ} (hr : r < k) {i₁ i₂ : ℕ} (hi₁ : i₁ < R * 2 ^ r) (hi₂ : i₂ < R * 2 ^ r)
    (hne : i₁ ≠ i₂) : qUp R k w r hr i₁ hi₁ ≠ qUp R k w r hr i₂ hi₂ := fun e ↦ by
  obtain ⟨hb, hp⟩ := hw _ _ _ _ e; have hdiv : i₁ / 2 ^ r = i₂ / 2 ^ r := congrArg Fin.val hb;
  have hmod : i₁ % 2 ^ r + 2 ^ r = i₂ % 2 ^ r + 2 ^ r := congrArg Fin.val hp
  have hmod' : i₁ % 2 ^ r = i₂ % 2 ^ r := by omega
  have hd₁ := Nat.div_add_mod i₁ (2 ^ r);
  have hd₂ := Nat.div_add_mod i₂ (2 ^ r); rw [hdiv, hmod'] at hd₁; exact hne (hd₁.symm.trans hd₂)
def fPairOpt {n : ℕ} (R k : ℕ) (uLo : Fin k → Wire n) (w : Fin R → Fin (2 ^ k) → Wire n)
    (huw : ∀ d b p, uLo d ≠ w b p) (r : ℕ) (hr : r < k) (i : ℕ) (hi : i < R * 2 ^ r)
    (β : BitAssignment n) : ZMod 2 := czPairsParity (pairOf R k uLo w huw r hr i hi) β
theorem fPairOpt_indep {n : ℕ} (R k : ℕ) (uLo : Fin k → Wire n) (w : Fin R → Fin (2 ^ k) → Wire n)
    (hw : WInj w) (huw : ∀ d b p, uLo d ≠ w b p) (r : ℕ) (hr : r < k) (i : ℕ) (hi : i < R * 2 ^ r)
    (β : BitAssignment n)
    (a : ZMod 2) : fPairOpt R k uLo w huw r hr i hi (Function.update β (qUp R k w r hr i hi) a) =
    fPairOpt R k uLo w huw r hr i hi β := by have huw' : uLo ⟨r, hr⟩ ≠ qUp R k w r hr i hi :=
                                               huw ⟨r, hr⟩ _ _; dsimp only [fPairOpt, pairOf,
                                               czPairsParity]; rw [Function.update_of_ne (qLo_ne_qUp
                                               hw hr hi hi), Function.update_of_ne huw']
def upperXorBitsOpt {n : ℕ} (R k : ℕ) (uLo : Fin k → Wire n)
    (w : Fin R → Fin (2 ^ k) → Wire n) (huw : ∀ d b p, uLo d ≠ w b p)
    (r : ℕ) (hr : r < k) : (m : ℕ) → m ≤ R * 2 ^ r → BitAssignment n → BitAssignment n
  | 0, _, β => β
  | m + 1, hm, β =>
      let β' := upperXorBitsOpt R k uLo w huw r hr m (Nat.le_of_succ_le hm) β
      Function.update β' (qUp R k w r hr m hm)
        (β' (qUp R k w r hr m hm) + fPairOpt R k uLo w huw r hr m hm β')

theorem upperXorBitsOpt_of_ne {n : ℕ} (R k : ℕ) (uLo : Fin k → Wire n)
    (w : Fin R → Fin (2 ^ k) → Wire n) (huw : ∀ d b p, uLo d ≠ w b p)
    (r : ℕ) (hr : r < k) (β : BitAssignment n) (u : Wire n) :
    ∀ (m : ℕ) (hm : m ≤ R * 2 ^ r),
      (∀ i (hi : i < m), u ≠ qUp R k w r hr i (Nat.lt_of_lt_of_le hi hm)) →
      upperXorBitsOpt R k uLo w huw r hr m hm β u = β u
  | 0, _, _ => rfl
  | m + 1, hm, hne => by
      dsimp only [upperXorBitsOpt]
      rw [Function.update_of_ne (hne m (Nat.lt_succ_self m)),
        upperXorBitsOpt_of_ne R k uLo w huw r hr β u m (Nat.le_of_succ_le hm) fun i hi ↦
            hne i (Nat.lt_succ_of_lt hi)]
theorem upperXorBitsOpt_qUp_lt {n : ℕ} (R k : ℕ) (uLo : Fin k → Wire n)
    (w : Fin R → Fin (2 ^ k) → Wire n) (hw : WInj w) (huw : ∀ d b p, uLo d ≠ w b p)
    (r : ℕ) (hr : r < k) (β : BitAssignment n) :
    ∀ (m : ℕ) (hm : m ≤ R * 2 ^ r) (i : ℕ) (hi : i < m),
      let hiR := Nat.lt_of_lt_of_le hi hm
      upperXorBitsOpt R k uLo w huw r hr m hm β (qUp R k w r hr i hiR) = β (qUp R k w r hr i hiR) +
          β (qLo R k w r hr i hiR) * β (uLo ⟨r, hr⟩)
  | 0, _, _, hi => absurd hi (Nat.not_lt_zero _)
  | m + 1, hm, i, hi => by
      dsimp only [upperXorBitsOpt]
      if him : i = m then
        subst him
        dsimp only [fPairOpt, pairOf, czPairsParity]
        rw [Function.update_self,
            upperXorBitsOpt_of_ne R k uLo w huw r hr β _ i (Nat.le_of_succ_le hm) fun _ hj ↦
            qUp_ne_of_ne_opt hw hr hm _ (Nat.ne_of_gt hj),
          upperXorBitsOpt_of_ne R k uLo w huw r hr β _ i (Nat.le_of_succ_le hm) fun _ _ ↦
              qLo_ne_qUp hw hr hm _,
          upperXorBitsOpt_of_ne R k uLo w huw r hr β _ i (Nat.le_of_succ_le hm) fun _ _ ↦
              huw ⟨r, hr⟩ _ _, add_zero]
      else
        rw [Function.update_of_ne (qUp_ne_of_ne_opt hw hr _ hm him),
            upperXorBitsOpt_qUp_lt R k uLo w hw huw r hr β m (Nat.le_of_succ_le hm) i (by omega)]
def uUpperXorPrefixOpt {n : ℕ} (R k : ℕ) (uLo : Fin k → Wire n)
    (w : Fin R → Fin (2 ^ k) → Wire n) (hw : WInj w) (huw : ∀ d b p, uLo d ≠ w b p)
    (r : ℕ) (hr : r < k) : (m : ℕ) → m ≤ R * 2 ^ r → Operator (2 ^ n)
  | 0, _ => 1
  | m + 1, hm =>
      (xorWireUnitary (qUp R k w r hr m hm) (fPairOpt R k uLo w huw r hr m hm)
        (fPairOpt_indep R k uLo w hw huw r hr m hm)).1 *
      uUpperXorPrefixOpt R k uLo w hw huw r hr m (Nat.le_of_succ_le hm)

theorem uUpperXorPrefixOpt_mulVec_ket {n : ℕ} (R k : ℕ) (uLo : Fin k → Wire n)
    (w : Fin R → Fin (2 ^ k) → Wire n) (hw : WInj w) (huw : ∀ d b p, uLo d ≠ w b p)
    (r : ℕ) (hr : r < k) (β : BitAssignment n) :
    ∀ (m : ℕ) (hm : m ≤ R * 2 ^ r),
      (uUpperXorPrefixOpt R k uLo w hw huw r hr m hm).mulVec (ket β) =
        ket (upperXorBitsOpt R k uLo w huw r hr m hm β)
  | 0, _ => Matrix.one_mulVec _
  | m + 1, hm => by
      rw [uUpperXorPrefixOpt, ← Matrix.mulVec_mulVec,
          uUpperXorPrefixOpt_mulVec_ket R k uLo w hw huw r hr β m (Nat.le_of_succ_le hm),
          xorWireUnitary_mulVec_ket]
      rfl
theorem count_wUncompMeasPrefix_opt {Var : Type} {n : ℕ} (v : Var) (R k : ℕ)
    (uLo : Fin k → Wire n) (w : Fin R → Fin (2 ^ k) → Wire n) (huw : ∀ d b p, uLo d ≠ w b p)
    (r : ℕ) (hr : r < k) (rest : DynamicCircuit Var n) :
    ∀ (m : ℕ) (hm : m ≤ R * 2 ^ r),
      (wUncompMeasPrefix v R k uLo w huw r hr rest m hm).count .T = rest.count .T ∧
      (wUncompMeasPrefix v R k uLo w huw r hr rest m hm).count .TOFF = rest.count .TOFF
  | 0, _ => ⟨rfl, rfl⟩
  | m + 1, hm =>
      let ⟨ht, hf⟩ := count_wUncompMeasPrefix_opt v R k uLo w huw r hr rest m (Nat.le_of_succ_le hm)
      let ⟨xt, xf⟩ :=
          count_xUnloadCzPairsSeqDyn v (qUp R k w r hr m hm) (pairOf R k uLo w huw r hr m hm)
          (wUncompMeasPrefix v R k uLo w
        huw r hr rest m (Nat.le_of_succ_le hm))
      ⟨xt.trans ht, xf.trans hf⟩
theorem count_wUncompRoundDyn_opt {Var : Type} {n : ℕ} (v : Var) (R k : ℕ) (uLo : Fin k → Wire n)
    (w : Fin R → Fin (2 ^ k) → Wire n)
    (hw : WInj w) (huw : ∀ d b p, uLo d ≠ w b p) (r : ℕ) (hr : r < k)
        (rest : DynamicCircuit Var n) :
    (wUncompRoundDyn v R k uLo w hw huw r hr rest).count .T = rest.count .T ∧
        (wUncompRoundDyn v R k uLo w hw huw r hr rest).count .TOFF = rest.count .TOFF := by
  obtain ⟨mt, mf⟩ := count_wUncompMeasPrefix_opt v R k uLo w huw r hr rest (R * 2 ^ r) le_rfl
  exact ⟨(congrArg₂ (· + ·)
      ((count_seqNat_T 0 (R * 2 ^ r) _ fun _ _ ↦
      by simp [Circuit.CNOT]).trans (Nat.mul_zero _)) mt).trans
      (Nat.zero_add _),
    (congrArg₂ (· + ·) (count_seqNat_TOFF_zero _ _ fun _ _ ↦
        by simp [Circuit.CNOT]) mf).trans (Nat.zero_add _)⟩
theorem count_wUncompTreeDyn_opt {Var : Type} {n : ℕ} (v : Var) (R k : ℕ)
    (uLo : Fin k → Wire n) (w : Fin R → Fin (2 ^ k) → Wire n)
    (hw : WInj w) (huw : ∀ d b p, uLo d ≠ w b p) (rest : DynamicCircuit Var n) :
    ∀ (m : ℕ) (hm : m ≤ k),
      (wUncompTreeDyn v R k uLo w hw huw rest m hm).count .T = rest.count .T ∧
      (wUncompTreeDyn v R k uLo w hw huw rest m hm).count .TOFF = rest.count .TOFF
  | 0, _ => ⟨rfl, rfl⟩
  | r + 1, hr =>
      let ⟨ht, hf⟩ := count_wUncompTreeDyn_opt v R k uLo w hw huw rest r (Nat.le_of_succ_le hr)
      let ⟨rt, rf⟩ :=
          count_wUncompRoundDyn_opt v R k uLo w hw huw r hr (wUncompTreeDyn v R k uLo w hw huw rest
          r (Nat.le_of_succ_le hr))
      ⟨rt.trans ht, rf.trans hf⟩
theorem dw_wUncompMeasPrefix_opt {Var : Type} {n : ℕ} {S : Wire n → Prop} (v : Var) (R k : ℕ)
    (uLo : Fin k → Wire n) (w : Fin R → Fin (2 ^ k) → Wire n) (huw : ∀ d b p, uLo d ≠ w b p)
    (huS : ∀ d, S (uLo d)) (hwS : ∀ b p, S (w b p))
    (r : ℕ) (hr : r < k) {rest : DynamicCircuit Var n} (hRest : DynWires S rest) :
    ∀ (m : ℕ) (hm : m ≤ R * 2 ^ r), DynWires S (wUncompMeasPrefix v R k uLo w huw r hr rest m hm)
  | 0, _ => hRest
  | m + 1, hm =>
      dw_xUnload (hwS _ _) (fun _ hp ↦ Eq.rec (motive := fun x _ ↦ S x.1 ∧ S x.2) ⟨hwS _ _, huS _⟩
          (List.mem_singleton.mp hp).symm)
        (dw_wUncompMeasPrefix_opt v R k uLo w huw huS hwS r hr hRest m (Nat.le_of_succ_le hm))
theorem dw_wUncompRoundDyn_opt {Var : Type} {n : ℕ} {S : Wire n → Prop} (v : Var) (R k : ℕ)
    (uLo : Fin k → Wire n) (w : Fin R → Fin (2 ^ k) → Wire n)
    (hw : WInj w) (huw : ∀ d b p, uLo d ≠ w b p) (huS : ∀ d, S (uLo d)) (hwS : ∀ b p, S (w b p))
        (r : ℕ) (hr : r < k) {rest : DynamicCircuit Var n}
    (hRest : DynWires S rest) : DynWires S (wUncompRoundDyn v R k uLo w hw huw r hr rest) :=
  ⟨cw_seqNat (R * 2 ^ r) _ (fun _ _ ↦ cw_cnot (hwS _ _) (hwS _ _)),
      dw_wUncompMeasPrefix_opt v R k uLo w huw huS hwS r hr hRest (R * 2 ^ r) le_rfl⟩
theorem dw_wUncompTreeDyn_opt {Var : Type} {n : ℕ} {S : Wire n → Prop} (v : Var) (R k : ℕ)
    (uLo : Fin k → Wire n) (w : Fin R → Fin (2 ^ k) → Wire n)
    (hw : WInj w) (huw : ∀ d b p, uLo d ≠ w b p)
    (huS : ∀ d, S (uLo d)) (hwS : ∀ b p, S (w b p))
    {rest : DynamicCircuit Var n} (hRest : DynWires S rest) :
    ∀ (m : ℕ) (hm : m ≤ k), DynWires S (wUncompTreeDyn v R k uLo w hw huw rest m hm)
  | 0, _ => hRest
  | r + 1, hr =>
        dw_wUncompRoundDyn_opt v R k uLo w hw huw huS hwS r hr (dw_wUncompTreeDyn_opt v R k uLo w hw
        huw huS hwS hRest r (Nat.le_of_succ_le hr))
/--
Optional pre-shift one-hot vector at tree level `m ≤ k` (`1`-hot on `activePred` , `ket δ`
otherwise).
-/
def oneHotOptPreVec {n R k : ℕ} (P activePred : BitAssignment n → Prop) [DecidablePred P]
    [DecidablePred activePred] (bStarFn : BitAssignment n → Fin R) (uLo : Fin k → Wire n)
    (w : Fin R → Fin (2 ^ k) → Wire n) (δ : BitAssignment n) (m : ℕ) (hm : m ≤ k) : Fin (2 ^ n) →
    ℂ :=
  if P δ ∧ ∀ b p, δ (w b p) = 0 then
    if activePred δ then
      ket (Function.update δ
        (w (bStarFn δ) ⟨idxValPrefix uLo δ m hm,
          Nat.lt_of_lt_of_le (idxValPrefix_lt_two_pow uLo δ m hm)
            (Nat.pow_le_pow_right (by omega) hm)⟩) 1)
    else ket δ
  else 0

/-- Operator mapping computational basis kets via `oneHotOptPreVec`. -/
def oneHotOptPreOp {n R k : ℕ} (P activePred : BitAssignment n → Prop) [DecidablePred P]
    [DecidablePred activePred] (bStarFn : BitAssignment n → Fin R) (uLo : Fin k → Wire n)
    (w : Fin R → Fin (2 ^ k) → Wire n) (m : ℕ) (hm : m ≤ k) : Operator (2 ^ n) := mkVecOp fun δ ↦
    oneHotOptPreVec P activePred bStarFn uLo w δ m hm
theorem upperXorBitsOpt_all_zero {n : ℕ} (R k : ℕ) (uLo : Fin k → Wire n)
    (w : Fin R → Fin (2 ^ k) → Wire n) (huw : ∀ d b p, uLo d ≠ w b p)
    (r : ℕ) (hr : r < k) (δ : BitAssignment n) (hw0 : ∀ b p, δ (w b p) = 0) :
    ∀ (m : ℕ) (hm : m ≤ R * 2 ^ r), upperXorBitsOpt R k uLo w huw r hr m hm δ = δ
  | 0, _ => rfl
  | m + 1, hm => by
      dsimp only [upperXorBitsOpt, fPairOpt, pairOf, czPairsParity, qLo, qUp]
      rw [upperXorBitsOpt_all_zero R k uLo w huw r hr δ hw0 m (Nat.le_of_succ_le hm),
        hw0 _ _, hw0 _ _, zero_mul, add_zero, add_zero, update_eq_self_of_zero (hw0 _ _)]
/- Section 2c2: SubspaceStep correctness for `wUncompRoundDyn` and `wUncompTreeDyn` -/
theorem projBit_zero_uUpperXorPrefixOpt {n R k : ℕ} (P activePred : BitAssignment n → Prop)
    [DecidablePred P] [DecidablePred activePred]
    (bStarFn : BitAssignment n → Fin R) (uLo : Fin k → Wire n) (w : Fin R → Fin (2 ^ k) → Wire n)
        (hw : WInj w) (huw : ∀ d b p, uLo d ≠ w b p)
    (r : ℕ) (hr : r < k) (m : ℕ) (hm : m < R * 2 ^ r) :
    projBit (qUp R k w r hr m hm) 0 *
        (uUpperXorPrefixOpt R k uLo w hw huw r hr m (Nat.le_of_succ_le hm) * oneHotOptPreOp P
      activePred bStarFn uLo w r (Nat.le_of_lt hr)) =
      uUpperXorPrefixOpt R k uLo w hw huw r hr m (Nat.le_of_succ_le hm) *
          oneHotOptPreOp P activePred bStarFn uLo w r (Nat.le_of_lt hr) := by
  refine matrix_ext_ket fun δ ↦ ?_
  simp only [← Matrix.mulVec_mulVec, oneHotOptPreOp, mkVecOp_mulVec_ket, oneHotOptPreVec]
  if hV : P δ ∧ ∀ b p, δ (w b p) = 0 then
    rw [ite_eq_left hV]
    if hAct : activePred δ then
      rw [ite_eq_left hAct, uUpperXorPrefixOpt_mulVec_ket, projBit_zero_mulVec_ket,
        ite_eq_left ((upperXorBitsOpt_of_ne R k uLo w huw r hr _ _ m (Nat.le_of_succ_le hm) fun _ hi
            ↦
          qUp_ne_of_ne_opt hw hr hm _ (Nat.ne_of_gt hi)).trans ((Function.update_of_ne
          (w_ne_of_pair_ne hw (Or.inr fun e ↦
              Nat.ne_of_lt (Nat.lt_of_lt_of_le (idxValPrefix_lt_two_pow uLo δ r _)
            (Nat.le_add_left _ _)) (congrArg Fin.val e))).symm 1 δ).trans (hV.2 _ _)))]
    else
      have hUp0 : δ (qUp R k w r hr m hm) = 0 := hV.2 _ _
      rw [ite_eq_right hAct, uUpperXorPrefixOpt_mulVec_ket,
        upperXorBitsOpt_all_zero R k uLo w huw r hr δ hV.2 m (Nat.le_of_succ_le hm),
        projBit_zero_mulVec_ket, ite_eq_left hUp0]
  else rw [ite_eq_right hV, Matrix.mulVec_zero, Matrix.mulVec_zero]
theorem subspaceStep_wUncompMeasPrefix_opt {Var : Type} [Fintype Var] [DecidableEq Var]
    {n R k : ℕ} (v : Var) (P activePred : BitAssignment n → Prop)
    [DecidablePred P] [DecidablePred activePred]
    (bStarFn : BitAssignment n → Fin R) (uLo : Fin k → Wire n)
    (w : Fin R → Fin (2 ^ k) → Wire n) (hw : WInj w) (huw : ∀ d b p, uLo d ≠ w b p)
    (r : ℕ) (hr : r < k) {rest : DynamicCircuit Var n} {R_out : Operator (2 ^ n)}
    (hRest : SubspaceStep (oneHotOptPreOp P activePred bStarFn uLo w r (Nat.le_of_lt hr)) R_out
        rest) :
    ∀ (m : ℕ) (hm : m ≤ R * 2 ^ r),
      SubspaceStep
        (uUpperXorPrefixOpt R k uLo w hw huw r hr m hm *
          oneHotOptPreOp P activePred bStarFn uLo w r (Nat.le_of_lt hr))
        R_out
        (wUncompMeasPrefix v R k uLo w huw r hr rest m hm)
  | 0, _ => by simpa only [uUpperXorPrefixOpt, Matrix.one_mul, wUncompMeasPrefix] using hRest
  | m + 1, hm => by
      dsimp only [uUpperXorPrefixOpt, wUncompMeasPrefix]
      rw [Matrix.mul_assoc]
      exact subspaceStep_xUnloadCzPairsSeqDyn v (qUp R k w r hr m hm)
          (pairOf R k uLo w huw r hr m hm) _ (fPairOpt R k uLo w huw r hr m hm)
        (fPairOpt_indep R k uLo w hw huw r hr m hm) (fun _ ↦ rfl) _ R_out
        (projBit_zero_uUpperXorPrefixOpt P activePred bStarFn uLo w hw huw r hr m hm)
        (subspaceStep_wUncompMeasPrefix_opt v P activePred bStarFn uLo w hw huw r hr hRest m
            (Nat.le_of_succ_le hm))
theorem wUncompCnotRound_mul_oneHotOptPreOp {n R k : ℕ} (P activePred : BitAssignment n → Prop)
    [DecidablePred P] [DecidablePred activePred]
    (bStarFn : BitAssignment n → Fin R) (uLo : Fin k → Wire n) (w : Fin R → Fin (2 ^ k) → Wire n)
        (hw : WInj w) (huw : ∀ d b p, uLo d ≠ w b p) (r : ℕ) (hr : r < k) :
    (wUncompCnotRound R k w hw r hr).eval.1 * oneHotOptPreOp P activePred bStarFn uLo w (r + 1) hr =
      uUpperXorPrefixOpt R k uLo w hw huw r hr (R * 2 ^ r) le_rfl *
          oneHotOptPreOp P activePred bStarFn uLo w r (Nat.le_of_lt hr) := by
  refine matrix_ext_ket fun δ ↦ ?_
  simp only [← Matrix.mulVec_mulVec, oneHotOptPreOp, mkVecOp_mulVec_ket, oneHotOptPreVec]
  by_cases hV : P δ ∧ ∀ b p, δ (w b p) = 0
  · have hw0 := hV.2
    rw [ite_eq_left hV, ite_eq_left hV]
    by_cases hAct : activePred δ
    · rw [ite_eq_left hAct, ite_eq_left hAct, uUpperXorPrefixOpt_mulVec_ket]
      let bStar := bStarFn δ
      let sLo := idxValPrefix uLo δ r (Nat.le_of_lt hr)
      have hsLo : sLo < 2 ^ r := idxValPrefix_lt_two_pow uLo δ r (Nat.le_of_lt hr)
      let pLo : Fin (2 ^ k) := ⟨sLo, pair_lo_lt hr hsLo⟩
      let pHi : Fin (2 ^ k) := ⟨sLo + 2 ^ r, pair_hi_lt hr hsLo⟩
      let δMid := Function.update δ (w bStar pLo) 1
      let δAfter := Function.update δMid (w bStar pHi) (δ (uLo ⟨r, hr⟩))
      let i₀ := bStar.val * 2 ^ r + sLo
      obtain ⟨hi₀, hdiv₀, hmod₀⟩ := enc_div_mod bStar.isLt hsLo
      have hqUp₀ : qUp R k w r hr i₀ hi₀ = w bStar pHi :=
        congrArg₂ w (Fin.ext hdiv₀) (Fin.ext (congrArg (· + 2 ^ r) hmod₀))
      have hqLo₀ : qLo R k w r hr i₀ hi₀ = w bStar pLo :=
          congrArg₂ w (Fin.ext hdiv₀) (Fin.ext hmod₀)
      have hMidUp0 (i : ℕ) (hi : i < R * 2 ^ r) : δMid (qUp R k w r hr i hi) = 0 :=
        (Function.update_of_ne (w_ne_of_pair_ne hw (Or.inr fun e ↦ Nat.ne_of_lt
          (Nat.lt_of_lt_of_le hsLo (Nat.le_add_left _ _))
              (congrArg Fin.val e).symm)) 1 δ).trans (hw0 _ _)
      have hneLoHi : w bStar pLo ≠ w bStar pHi :=
        w_ne_of_pair_ne hw (Or.inr fun e ↦ absurd (congrArg Fin.val e)
            (show sLo ≠ sLo + 2 ^ r by omega))
      refine Eq.trans (b := ket δAfter) ?_ (congrArg ket (funext fun u ↦ ?_))
      · let fGate (i : ℕ) (hi : i < R * 2 ^ r) :=
          Circuit.CNOT (qUp R k w r hr i hi) (qLo R k w r hr i hi) (qLo_ne_qUp hw hr hi hi).symm
        dsimp only [wUncompCnotRound]
        rcases DynCircExt.bit_cases (δ (uLo ⟨r, hr⟩)) with hu0 | hu1
        · rw [show (⟨idxValPrefix uLo δ (r + 1) hr, _⟩ : Fin (2 ^ k)) = pLo from
              Fin.ext ((congrArg (sLo + ·)
                  (ite_eq_right (hu0 ▸ zero_ne_one))).trans (Nat.add_zero sLo)),
            show δAfter = δMid from (congrArg (Function.update δMid (w bStar pHi)) hu0).trans
              (update_eq_self_of_zero ((Function.update_of_ne hneLoHi.symm 1 δ).trans (hw0 bStar
                  pHi)))]
          exact seqNat_mulVec_fixed (ket δMid) (R * 2 ^ r) fGate fun i hi ↦
              ket_CNOT_ctrl_zero _ (hMidUp0 i hi)
        · rw [show (⟨idxValPrefix uLo δ (r + 1) hr, _⟩ : Fin (2 ^ k)) = pHi from
              Fin.ext (congrArg (sLo + ·) (ite_eq_left hu1))]
          exact (seqNat_mulVec_single (ket (Function.update δ (w bStar pHi) 1))
              (ket δAfter) i₀ (R * 2 ^ r) fGate
            (fun i hi hlt ↦ ket_CNOT_ctrl_zero _ ((Function.update_of_ne
              (fun e ↦ qUp_ne_of_ne_opt hw hr hi hi₀ (Nat.ne_of_lt hlt)
                  (e.trans hqUp₀.symm)) 1 δ).trans (hw0 _ _)))
            (fun hi₀' ↦ by
              dsimp only [fGate, δAfter, δMid]
              rw [ket_CNOT, show qUp R k w r hr i₀ hi₀' = w bStar pHi from hqUp₀,
                show qLo R k w r hr i₀ hi₀' = w bStar pLo from hqLo₀, Function.update_of_ne hneLoHi,
                    hw0 bStar pLo,
                Function.update_self, zero_add, Function.update_comm hneLoHi.symm, hu1])
            (fun i hi hgt ↦ ket_CNOT_ctrl_zero _ ((Function.update_of_ne
              (fun e ↦ qUp_ne_of_ne_opt hw hr hi hi₀ (Nat.ne_of_gt hgt)
                  (e.trans hqUp₀.symm)) _ δMid).trans (hMidUp0 i hi)))).trans
            (ite_eq_left hi₀)
      · if hU : ∃ idx : Fin (R * 2 ^ r), u = qUp R k w r hr idx.val idx.isLt then
          obtain ⟨⟨i, hi⟩, rfl⟩ := hU
          rw [upperXorBitsOpt_qUp_lt R k uLo w hw huw r hr δMid (R * 2 ^ r) le_rfl i hi,
              hMidUp0 i hi, zero_add,
            show δMid (uLo ⟨r, hr⟩) = δ (uLo ⟨r, hr⟩) from Function.update_of_ne (huw ⟨r,
                hr⟩ _ _) 1 δ]
          if hii₀ : i = i₀ then
            subst hii₀
            simp only [δAfter, δMid, hqUp₀, hqLo₀, Function.update_self, one_mul]
          else
            have hneLo : qLo R k w r hr i hi ≠ w bStar pLo :=
                w_ne_of_pair_ne hw ((enc_ne_iff hii₀).imp
              (fun h e ↦ h (congrArg Fin.val e)) (fun h e ↦ h (congrArg Fin.val e)))
            have hLo0 : δ (qLo R k w r hr i hi) = 0 := hw0 _ _
            dsimp only [δAfter, δMid]
            rw [(Function.update_of_ne (fun e ↦
                qUp_ne_of_ne_opt hw hr hi hi₀ hii₀ (e.trans hqUp₀.symm)) _ δMid).trans (hMidUp0 i
                hi),
              Function.update_of_ne hneLo, hLo0, zero_mul]
        else
          have hneAll : ∀ i (hi : i < R * 2 ^ r), u ≠ qUp R k w r hr i hi := fun i hi e ↦
              hU ⟨⟨i, hi⟩, e⟩
          rw [show δAfter u = δMid u from Function.update_of_ne (fun e ↦
              hneAll i₀ hi₀ (e.trans hqUp₀.symm)) _ δMid,
            upperXorBitsOpt_of_ne R k uLo w huw r hr δMid u (R * 2 ^ r) le_rfl hneAll]
    · rw [ite_eq_right hAct, ite_eq_right hAct, uUpperXorPrefixOpt_mulVec_ket,
          upperXorBitsOpt_all_zero R k uLo w huw r hr δ hw0 (R * 2 ^ r) le_rfl]
      exact seqNat_mulVec_fixed (ket δ) (R * 2 ^ r) _ fun _ _ ↦ ket_CNOT_ctrl_zero _ (hw0 _ _)
  · rw [ite_eq_right hV, ite_eq_right hV, Matrix.mulVec_zero, Matrix.mulVec_zero]
theorem subspaceStep_wUncompRoundDyn_opt {Var : Type} [Fintype Var] [DecidableEq Var] {n R k : ℕ}
    (v : Var) (P activePred : BitAssignment n → Prop)
    [DecidablePred P] [DecidablePred activePred] (bStarFn : BitAssignment n → Fin R)
        (uLo : Fin k → Wire n) (w : Fin R → Fin (2 ^ k) → Wire n)
    (hw : WInj w) (huw : ∀ d b p, uLo d ≠ w b p) (r : ℕ) (hr : r < k) {rest : DynamicCircuit Var n}
        {R_out : Operator (2 ^ n)}
    (hRest : SubspaceStep (oneHotOptPreOp P activePred bStarFn uLo w r (Nat.le_of_lt hr)) R_out
        rest) :
    SubspaceStep (oneHotOptPreOp P activePred bStarFn uLo w (r +
        1) hr) R_out (wUncompRoundDyn v R k uLo w hw huw r hr rest) :=
  (subspaceStep_congr_out (subspaceStep_of_circuit (Var := Var) _ _)
      (wUncompCnotRound_mul_oneHotOptPreOp P activePred bStarFn uLo w hw huw r hr)).seq
    (subspaceStep_wUncompMeasPrefix_opt v P activePred bStarFn uLo w hw huw r hr hRest (R *
        2 ^ r) le_rfl)
theorem subspaceStep_wUncompTreeDyn_opt {Var : Type} [Fintype Var] [DecidableEq Var]
    {n R k : ℕ} (v : Var) (P activePred : BitAssignment n → Prop)
    [DecidablePred P] [DecidablePred activePred]
    (bStarFn : BitAssignment n → Fin R) (uLo : Fin k → Wire n)
    (w : Fin R → Fin (2 ^ k) → Wire n) (hw : WInj w) (huw : ∀ d b p, uLo d ≠ w b p)
    {rest : DynamicCircuit Var n} {R_out : Operator (2 ^ n)}
    (hRest : SubspaceStep (oneHotOptPreOp P activePred bStarFn uLo w 0 (Nat.zero_le k)) R_out
        rest) :
    ∀ (m : ℕ) (hm : m ≤ k),
      SubspaceStep (oneHotOptPreOp P activePred bStarFn uLo w m hm) R_out
        (wUncompTreeDyn v R k uLo w hw huw rest m hm)
  | 0, _ => hRest
  | r + 1, hr =>
      subspaceStep_wUncompRoundDyn_opt v P activePred bStarFn uLo w hw huw r hr
        (subspaceStep_wUncompTreeDyn_opt v P activePred
          bStarFn uLo w hw huw hRest r (Nat.le_of_succ_le hr))
end
/- Section 3a: Generic optional W-expansion, last-round split-shift, and 8-bit 3+5 index split -/
theorem eval_X_mul_self_opt {n : ℕ} (q : Wire n) : (Circuit.X q).eval.1 * (Circuit.X q).eval.1 =
    1 := by
  apply matrix_ext_ket; intro δ
  rw [← Matrix.mulVec_mulVec, ket_X, ket_X, Function.update_idem, Function.update_self, add_assoc,
      CharTwo.add_self_eq_zero, add_zero, Function.update_eq_self, Matrix.one_mulVec]

theorem mulVec_X_invol_opt {n : ℕ} (q : Wire n) (v : Fin (2 ^ n) → ℂ) :
    (Circuit.X q).eval.1.mulVec ((Circuit.X q).eval.1.mulVec v) =
    v := by rw [Matrix.mulVec_mulVec, eval_X_mul_self_opt, Matrix.one_mulVec]
theorem eval_CNOT_mul_self_opt {n : ℕ} (c t : Wire n) (h : c ≠ t) : (Circuit.CNOT c t h).eval.1 *
    (Circuit.CNOT c t h).eval.1 = 1 := by
  apply matrix_ext_ket; intro δ
  rw [← Matrix.mulVec_mulVec, ket_CNOT, ket_CNOT, Function.update_idem, Function.update_self,
      Function.update_of_ne h, add_assoc, CharTwo.add_self_eq_zero, add_zero,
      Function.update_eq_self, Matrix.one_mulVec]

theorem mulVec_CNOT_invol_opt {n : ℕ} (c t : Wire n) (h : c ≠ t) (v : Fin (2 ^ n) → ℂ) :
    (Circuit.CNOT c t h).eval.1.mulVec ((Circuit.CNOT c t h).eval.1.mulVec v) =
    v := by rw [Matrix.mulVec_mulVec, eval_CNOT_mul_self_opt, Matrix.one_mulVec]
theorem wZeroGate_id_of_one {n : ℕ} {wHas t0 : Wire n} (hHas0 : wHas ≠ t0) {β : BitAssignment n}
    (h1 : β wHas = 1) : (wZeroGate wHas t0 hHas0).eval.1.mulVec (ket β) =
    ket β := by rw [wZeroGate, eval_seq_mulVec, ket_X, ket_CNOT, Function.update_idem,
                  Function.update_self, Function.update_of_ne hHas0, h1, add_assoc,
                  CharTwo.add_self_eq_zero, add_zero, Function.update_eq_self]
theorem wZeroGate_ket {n : ℕ} {wHas t0 tStar : Wire n} (hHas0 : wHas ≠ t0) (hHasStar : wHas ≠ tStar)
    {δ : BitAssignment n} (hZero : δ wHas = 0 → tStar = t0) :
    (wZeroGate wHas t0 hHas0).eval.1.mulVec (ket (Function.update δ tStar 1)) =
    ket (Function.update δ tStar (δ wHas)) := by
  rcases DynCircExt.bit_cases (δ wHas) with h0 | h1
  · rw [hZero h0, h0, wZeroGate, eval_seq_mulVec, ket_X, Function.update_idem, Function.update_self,
        CharTwo.add_self_eq_zero, ket_CNOT, Function.update_idem, Function.update_self,
        Function.update_of_ne hHas0, h0, add_zero]
  · rw [h1]; exact wZeroGate_id_of_one hHas0 ((Function.update_of_ne hHasStar 1 δ).trans h1)
theorem wUnzeroGate_id_of_one {n : ℕ} {wHas t0 : Wire n} (hHas0 : wHas ≠ t0) {β : BitAssignment n}
    (h1 : β wHas = 1) : (wUnzeroGate wHas t0 hHas0).eval.1.mulVec (ket β) =
    ket β := by rw [wUnzeroGate, eval_seq_mulVec, ket_CNOT, h1, ket_X, Function.update_idem,
                  Function.update_self, add_assoc, CharTwo.add_self_eq_zero, add_zero,
                  Function.update_eq_self]
theorem wUnzeroGate_ket {n : ℕ} {wHas t0 tStar : Wire n} (hHas0 : wHas ≠ t0)
    (hHasStar : wHas ≠ tStar) {δ : BitAssignment n} (hZero : δ wHas = 0 → tStar = t0) :
    (wUnzeroGate wHas t0 hHas0).eval.1.mulVec (ket (Function.update δ tStar (δ wHas))) =
    ket (Function.update δ tStar 1)
    := by rw [← wZeroGate_ket hHas0 hHasStar hZero]; simp only [wUnzeroGate, wZeroGate,
            eval_seq_mulVec, mulVec_CNOT_invol_opt, mulVec_X_invol_opt]
theorem wSuperVec_bot_pub {n R k : ℕ} (bStarFn : BitAssignment n → Fin R) (uLo : Fin k → Wire n)
    (w : Fin R → Fin (2 ^ k) → Wire n) (hw : WInj w) (qEnc : Wire n) (δ : BitAssignment n)
    (hw0 : ∀ b p, δ (w b p) = 0) (hq0 : δ qEnc = 0) :
    (wTreePrefix R k w hw k le_rfl).eval.1.mulVec (ket (Function.update δ (w (bStarFn δ)
    ⟨0, Nat.two_pow_pos k⟩) 1)) = wSuperVec bStarFn uLo w qEnc δ 0 (Nat.zero_le k) := by
  rw [wTreePrefix_mulVec_ket w hw δ hw0 (bStarFn δ) k le_rfl]; dsimp only [wSuperVec];
  rw [ite_eq_left ⟨hw0, hq0⟩]; have hk0 : k - 0 = k := Nat.sub_zero k
  let e : Fin (2 ^ k) ≃ Fin (2 ^ (k - 0)) := finCongr (by rw [hk0])
  rw [← e.sum_comp]; simp only [hk0]; congr 1
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  exact congrArg (fun p ↦ ket (Function.update δ (w (bStarFn δ) p) 1))
    (Fin.ext (by dsimp [e, idxValPrefix]; omega))

theorem wSuperVec_top_pub {n R k : ℕ} (bStarFn : BitAssignment n → Fin R) (uLo : Fin k → Wire n)
    (w : Fin R → Fin (2 ^ k) → Wire n)
    (qEnc : Wire n) (δ : BitAssignment n) (hw0 : ∀ b p, δ (w b p) = 0) (hq0 : δ qEnc = 0) :
    wSuperVec bStarFn uLo w qEnc δ k le_rfl = ket (Function.update δ (w (bStarFn δ)
        ⟨idxValPrefix uLo δ k le_rfl, idxValPrefix_lt_two_pow uLo δ k le_rfl⟩) 1) := by
  dsimp only [wSuperVec]
  rw [ite_eq_left ⟨hw0, hq0⟩, show sqrtHalf ^ (k - k) = 1 by rw [Nat.sub_self, _root_.pow_zero],
      one_smul, Finset.sum_eq_single ⟨0, Nat.two_pow_pos (k - k)⟩]
  · exact congrArg (fun p ↦ ket (Function.update δ (w (bStarFn δ) p) 1)) (Fin.ext (by dsimp))
  · exact fun hi _ hne ↦
        absurd (Fin.ext (Nat.lt_one_iff.mp
        (by simpa only [Nat.sub_self, Nat.pow_zero] using hi.isLt))) hne
  · exact fun habs ↦ (habs (Finset.mem_univ _)).elim
theorem wTreeRound_mulVec_ket_zero {n R k : ℕ} (w : Fin R → Fin (2 ^ k) → Wire n) (hw : WInj w)
    (r : ℕ) (hr : r < k) (δ : BitAssignment n) (h0 : ∀ b p, δ (w b p) = 0) :
    (wTreeRound R k w hw r hr).eval.1.mulVec (ket δ) = ket δ :=
    seqNat_mulVec_fixed (ket δ) (R * 2 ^ r) _ fun _ _ ↦
    wSplitPair_mulVec_ket_zero _ _ _ δ (h0 _ _) (h0 _ _)
/-- Combined base + clean-ancilla predicate `P δ ∧ δ wDum = 0 ∧ δ qEnc = 0` for `oneHotOptPreOp`. -/
def OptBasePred {n : ℕ} (P : BitAssignment n → Prop) (wDum qEnc : Wire n) (δ : BitAssignment n) :
    Prop := P δ ∧ δ wDum = 0 ∧ δ qEnc = 0
instance instDecidableOptBasePred {n : ℕ} (P : BitAssignment n → Prop) [DecidablePred P]
    (wDum qEnc : Wire n) : DecidablePred (OptBasePred P wDum qEnc) := fun δ ↦ by
  unfold OptBasePred; infer_instance

theorem wOptSuperOp_top_eq_oneHotOptPreOp {n R k : ℕ} (P activePred : BitAssignment n → Prop)
    [DecidablePred P] [DecidablePred activePred] (bStarFn : BitAssignment n → Fin R)
    (uLo : Fin k → Wire n) (w : Fin R → Fin (2 ^ k) → Wire n) (wDum qEnc : Wire n) :
    wOptSuperOp P activePred bStarFn uLo w wDum qEnc k le_rfl =
    oneHotOptPreOp (OptBasePred P wDum qEnc) activePred bStarFn uLo w k le_rfl := by
  refine matrix_ext_ket fun δ ↦ ?_
  simp only [wOptSuperOp, oneHotOptPreOp, mkVecOp_mulVec_ket, wOptSuperVec, oneHotOptPreVec]
  if hV : P δ ∧ (∀ b p, δ (w b p) = 0) ∧ δ wDum = 0 ∧ δ qEnc = 0 then
    rw [ite_eq_left hV, ite_eq_left (⟨⟨hV.1, hV.2.2.1, hV.2.2.2⟩,
        hV.2.1⟩ : OptBasePred P wDum qEnc δ ∧ _)]
    if hAct : activePred δ then
      rw [ite_eq_left hAct, ite_eq_left hAct,
          wSuperVec_top_pub bStarFn uLo w qEnc δ hV.2.1 hV.2.2.2]
    else rw [ite_eq_right hAct, ite_eq_right hAct]
  else rw [ite_eq_right hV, ite_eq_right fun ⟨⟨hp, hwd, hq⟩, hw⟩ ↦ hV ⟨hp, hw, hwd, hq⟩]

def wLastSplitShiftDyn {Var : Type} {n : ℕ} (v : Var) (R d : ℕ) (uLo : Fin (d + 1) → Wire n)
    (w : Fin R → Fin (2 ^ (d + 1)) → Wire n) (rDum wDum qEnc : Wire n)
    (hInj : WOptInj R (d + 1) uLo w rDum wDum qEnc) : DynamicCircuit Var n :=
    .seq (.circuit (wTreeRound R (d + 1) w hInj.w_inj d (Nat.lt_succ_self d)))
    (wShiftDummyLevel v R (d + 1) uLo w rDum wDum qEnc hInj d (Nat.lt_succ_self d))
theorem count_wLastSplitShiftDyn {Var : Type} {n : ℕ} (v : Var) (R d : ℕ)
    (uLo : Fin (d + 1) → Wire n) (w : Fin R → Fin (2 ^ (d + 1)) → Wire n) (rDum wDum qEnc : Wire n)
    (hInj : WOptInj R (d + 1) uLo w rDum wDum qEnc) :
    (wLastSplitShiftDyn v R d uLo w rDum wDum qEnc hInj).count .T = 2 * R * 2 ^ d + 2 ∧
    (wLastSplitShiftDyn v R d uLo w rDum wDum qEnc hInj).count .TOFF = 0 := by
  have hrt : (wTreeRound R (d + 1) w hInj.w_inj d (Nat.lt_succ_self d)).count .T = (R * 2 ^ d) *
      2 := count_seqNat_T 2 (R * 2 ^ d) _ fun _ _ ↦ (count_wSplitPair _ _ _).1
  have hrf : (wTreeRound R (d + 1) w hInj.w_inj d (Nat.lt_succ_self d)).count .TOFF = 0 :=
      count_seqNat_TOFF_zero (R * 2 ^ d) _ fun _ _ ↦ (count_wSplitPair _ _ _).2
  obtain ⟨ts, fs⟩ :=
      count_wShiftDummyLevel v R (d +
      1) uLo w rDum wDum qEnc hInj d (Nat.lt_succ_self d); dsimp only [wLastSplitShiftDyn,
      DynamicCircuit.count]
  rw [hrt, hrf, ts, fs]; exact ⟨by ring, rfl⟩

theorem dw_wLastSplitShiftDyn {Var : Type} {n : ℕ} {S : Wire n → Prop} (v : Var) (R d : ℕ)
    (uLo : Fin (d + 1) → Wire n) (w : Fin R → Fin (2 ^ (d + 1)) → Wire n) (rDum wDum qEnc : Wire n)
    (hInj : WOptInj R (d + 1) uLo w rDum wDum qEnc) (huS : ∀ i, S (uLo i)) (hwS : ∀ b p, S (w b p))
    (hrS : S rDum) (hwdS : S wDum)
    (hqS : S qEnc) : DynWires S (wLastSplitShiftDyn v R d uLo w rDum wDum qEnc hInj) :=
    ⟨cw_seqNat (R * 2 ^ d) _ (fun _ _ ↦ cw_wSplitPair (hwS _ _) (hwS _ _)),
    dw_wShiftDummyLevel v R (d +
    1) uLo w rDum wDum qEnc hInj huS hwS hrS hwdS hqS d (Nat.lt_succ_self d)⟩
theorem subspaceStep_wLastSplitShiftDyn {Var : Type} [Fintype Var] [DecidableEq Var] {n R d : ℕ}
    (v : Var) (P activePred : BitAssignment n → Prop) [DecidablePred P] [DecidablePred activePred]
    (bStarFn : BitAssignment n → Fin R) (uLo : Fin (d + 1) → Wire n)
    (w : Fin R → Fin (2 ^ (d + 1)) → Wire n) (rDum wDum qEnc : Wire n)
    (hInj : WOptInj R (d + 1) uLo w rDum wDum qEnc)
    (hDumBit : ∀ δ, P δ → δ rDum = (if activePred δ then 0 else 1)) :
    SubspaceStep (oneHotOptPreOp (OptBasePred P wDum qEnc) activePred bStarFn uLo w d (Nat.le_succ
    d)) (oneHotOptPreOp (OptBasePred P wDum qEnc) activePred bStarFn uLo w (d + 1) le_rfl)
    (wLastSplitShiftDyn v R d uLo w rDum wDum qEnc hInj) := by
  have hd : d < d + 1 := Nat.lt_succ_self d
  have hRound : (wTreeRound R (d + 1) w hInj.w_inj d hd).eval.1 *
      oneHotOptPreOp (OptBasePred P wDum qEnc) activePred bStarFn uLo w d (Nat.le_succ d) =
      wOptSuperOp P activePred bStarFn uLo w wDum qEnc d (Nat.le_of_lt hd) := by
    apply matrix_ext_ket; intro δ
    simp only [← Matrix.mulVec_mulVec, oneHotOptPreOp, wOptSuperOp, mkVecOp_mulVec_ket,
        oneHotOptPreVec, wOptSuperVec]
    by_cases hV : P δ ∧ (∀ b p, δ (w b p) = 0) ∧ δ wDum = 0 ∧ δ qEnc = 0
    · have hV' : OptBasePred P wDum qEnc δ ∧ ∀ b p, δ (w b p) = 0 :=
          ⟨⟨hV.1, hV.2.2.1, hV.2.2.2⟩, hV.2.1⟩; rw [ite_eq_left hV', ite_eq_left hV]
      by_cases hAct : activePred δ
      · rw [ite_eq_left hAct, ite_eq_left hAct];
        let s : Fin (2 ^ d) :=
            ⟨idxValPrefix uLo δ d (Nat.le_succ d),
            idxValPrefix_lt_two_pow uLo δ d (Nat.le_succ d)⟩; rw [wTreeRound_mulVec_ket w hInj.w_inj
            d hd δ hV.2.1 (bStarFn δ) s]; dsimp only [wSuperVec]; rw [ite_eq_left ⟨hV.2.1,
            hV.2.2.2⟩]; have hsub : d + 1 - d = 1 := Nat.add_sub_cancel_left d 1
        let e : Fin 2 ≃ Fin (2 ^ (d + 1 - d)) := finCongr (by rw [hsub]; norm_num)
        rw [← e.sum_comp, Fin.sum_univ_two, show sqrtHalf ^ (d + 1 - d) =
            sqrtHalf by rw [hsub, _root_.pow_one]]
        exact congrArg (sqrtHalf • ·) (congrArg₂ (· + ·)
          (congrArg (fun p ↦ ket (Function.update δ (w (bStarFn δ) p) 1)) (Fin.ext rfl))
          (congrArg (fun p ↦ ket (Function.update δ (w (bStarFn δ) p) 1))
              (Fin.ext (by simp [e, s]))))
      · rw [ite_eq_right hAct, ite_eq_right hAct,
            wTreeRound_mulVec_ket_zero w hInj.w_inj d hd δ hV.2.1]
    · rw [ite_eq_right fun ⟨⟨hp, hwd, hq⟩, hw⟩ ↦ hV ⟨hp, hw, hwd, hq⟩, ite_eq_right hV,
          Matrix.mulVec_zero]
  exact (subspaceStep_congr_out (subspaceStep_of_circuit _ _) hRound).seq (subspaceStep_congr_out
      (subspaceStep_wShiftDummyLevel v P activePred bStarFn uLo w rDum wDum qEnc hInj hDumBit d hd)
      (wOptSuperOp_top_eq_oneHotOptPreOp P activePred bStarFn uLo w wDum qEnc))

theorem idxValD_8_split35 {n : ℕ} (wIdx : Fin 8 → Wire n) (δ : BitAssignment n) :
    idxValD wIdx δ =
      8 * idxValD (fun d : Fin 5 ↦ wIdx ⟨3 + d.val, by have := d.isLt; omega⟩) δ +
        idxValD (fun d : Fin 3 ↦ wIdx ⟨d.val, by have := d.isLt; omega⟩) δ := by
  let z (i : Fin 8) : ℕ := if δ (wIdx i) = 1 then 1 else 0
  have hz (i : Fin 8) (m : ℕ) : (if δ (wIdx i) = 1 then m else 0) = m * z i := by
    dsimp [z]; split_ifs <;> ring
  dsimp only [idxValD, idxValPrefix]; simp only [hz]; ring
theorem idxValD_8_div8 {n : ℕ} (wIdx : Fin 8 → Wire n) (δ : BitAssignment n) :
    idxValD wIdx δ / 8 =
      idxValD (fun d : Fin 5 ↦ wIdx ⟨3 + d.val, by have := d.isLt; omega⟩) δ := by
  have hlo : idxValD (fun d : Fin 3 ↦ wIdx ⟨d.val, Nat.lt_trans d.isLt (by decide)⟩) δ < 8 :=
      idxValPrefix_lt_two_pow _ δ 3 le_rfl
  rw [idxValD_8_split35 wIdx δ, Nat.mul_add_div (by decide), Nat.div_eq_of_lt hlo, add_zero]

theorem idxValD_8_mod8 {n : ℕ} (wIdx : Fin 8 → Wire n) (δ : BitAssignment n) :
    idxValD wIdx δ % 8 =
      idxValD (fun d : Fin 3 ↦ wIdx ⟨d.val, by have := d.isLt; omega⟩) δ := by
  have hlo : idxValD (fun d : Fin 3 ↦ wIdx ⟨d.val, Nat.lt_trans d.isLt (by decide)⟩) δ < 8 :=
      idxValPrefix_lt_two_pow _ δ 3 le_rfl
  rw [idxValD_8_split35 wIdx δ, Nat.mul_add_mod, Nat.mod_eq_of_lt hlo]
/- Section 3b1: Wire slices, disjointness, and circuit definition for `pCLoE` (`330 T`) -/
theorem rHas1_ne_wA24 {n : ℕ} (r : RouterReg 187 8 n) (q : Fin 24) : rHas1 r ≠ wA24 r q :=
  rr_ne r (by have := q.isLt; unfold idxA24Val; dsimp; split_ifs <;> omega)

def uXorPubLo {n : ℕ} (r : RouterReg 187 8 n) : Unitary (2 ^ n) :=
  uVecToggle (rCtrlLo r) (rCtrlLo_inj_ne r) (pubCtrlLo r)
    (fun _ _ hEq ↦ (pubCtrl_congr r fun w ⟨u, hu, hw⟩ ↦ hw ▸
      hEq (r u) fun p ↦ rr_ne r (by have := p.isLt; unfold basePub; dsimp; omega)).1)

theorem wA24_inj {n : ℕ} (r : RouterReg 187 8 n) {q₁ q₂ : Fin 24} (heq : wA24 r q₁ = wA24 r q₂) :
    q₁ = q₂ := by
  have hv := congrArg Fin.val (r.wires.injective heq)
  have := q₁.isLt; have := q₂.isLt
  unfold idxA24Val at hv; dsimp at hv
  exact Fin.ext (by split_ifs at hv <;> omega)

theorem idxHi5_1_lt24_of_lt187 {n : ℕ} (r : RouterReg 187 8 n) {γ : BitAssignment n}
    (hlt : idxValD (rIdx1 r) γ < 187) : idxValD (idxHi5_1 r) γ <
    24 := by have hd :=
               idxValD_8_div8 (rIdx1 r) γ; change idxValD (rIdx1 r) γ / 8 =
               idxValD (idxHi5_1 r) γ at hd; omega
theorem eval_seq_eq {n : ℕ} (c₁ c₂ : Circuit n) : (c₁ ;;ᶜ c₂).eval.1 = c₂.eval.1 * c₁.eval.1 :=
  matrix_ext_ket fun δ ↦
      (eval_seq_mulVec c₁ c₂ (ket δ)).trans (Matrix.mulVec_mulVec (ket δ) c₂.eval.1 c₁.eval.1)
theorem eval_CNOT_comm {n : ℕ} {c₁ t₁ c₂ t₂ : Wire n} (h₁ : c₁ ≠ t₁) (h₂ : c₂ ≠ t₂) (hc₁ : c₁ ≠ t₂)
    (hc₂ : c₂ ≠ t₁) :
    (Circuit.CNOT c₁ t₁ h₁).eval.1 * (Circuit.CNOT c₂ t₂ h₂).eval.1 =
        (Circuit.CNOT c₂ t₂ h₂).eval.1 * (Circuit.CNOT c₁ t₁ h₁).eval.1 :=
  matrix_ext_ket fun δ ↦ by
    simp only [← Matrix.mulVec_mulVec, ket_CNOT]
    rw [Function.update_of_ne hc₁, Function.update_of_ne hc₂]
    if ht : t₁ = t₂ then
      subst ht
      simpa only [Function.update_idem, Function.update_self] using congrArg (fun x ↦
          ket (Function.update δ t₁ x)) (by ring)
    else rw [Function.update_of_ne ht, Function.update_of_ne (Ne.symm ht),
        Function.update_comm (Ne.symm ht)]
theorem seqNat_eval_comm {n : ℕ} (A : Operator (2 ^ n)) :
    ∀ (m : ℕ) (f : (i : ℕ) → i < m → Circuit n),
      (∀ i hi, A * (f i hi).eval.1 = (f i hi).eval.1 * A) →
      A * (seqNat m f).eval.1 = (seqNat m f).eval.1 * A
  | 0, _, _ => by simp [seqNat, Circuit.eval_identity]
  | m + 1, f, hc =>
        by rw [seqNat, eval_seq_eq, ← Matrix.mul_assoc, hc m (Nat.lt_succ_self m), Matrix.mul_assoc,
      seqNat_eval_comm A m _ fun i hi ↦ hc i (Nat.lt_succ_of_lt hi), ← Matrix.mul_assoc]
theorem seqNat_eval_mul_self {n : ℕ} :
    ∀ (m : ℕ) (f : (i : ℕ) → i < m → Circuit n),
      (∀ i hi, (f i hi).eval.1 * (f i hi).eval.1 = 1) →
      (∀ i hi j hj, (f i hi).eval.1 * (f j hj).eval.1 = (f j hj).eval.1 * (f i hi).eval.1) →
      (seqNat m f).eval.1 * (seqNat m f).eval.1 = 1
  | 0, _, _, _ => by simp [seqNat, Circuit.eval_identity]
  | m + 1, f, hself, hcomm => by
      let fm := (f m (Nat.lt_succ_self m)).eval.1
      let Sm := (seqNat m fun i hi ↦ f i (Nat.lt_succ_of_lt hi)).eval.1
      rw [seqNat, eval_seq_eq, show (fm * Sm) * (fm * Sm) =
        fm * (Sm * fm) * Sm by simp only [Matrix.mul_assoc], ← seqNat_eval_comm fm m _ fun i hi ↦
        hcomm m (Nat.lt_succ_self m) i (Nat.lt_succ_of_lt hi),
        show fm * (fm * Sm) * Sm = (fm * fm) * (Sm * Sm) by simp only [Matrix.mul_assoc],
            hself m (Nat.lt_succ_self m),
        seqNat_eval_mul_self m _ (fun i hi ↦ hself i (Nat.lt_succ_of_lt hi)) fun i hi j hj ↦
            hcomm i (Nat.lt_succ_of_lt hi) j (Nat.lt_succ_of_lt hj), Matrix.mul_one]
/-- `K` parallel CNOTs `wSrc i → wDst i`. -/
def seqCnotVec {n : ℕ} (K : ℕ) (wSrc wDst : Fin K → Wire n) (hne : ∀ i, wSrc i ≠ wDst i) :
    Circuit n := seqNat K fun i hi ↦ Circuit.CNOT (wSrc ⟨i, hi⟩) (wDst ⟨i, hi⟩) (hne ⟨i, hi⟩)
theorem count_seqCnotVec {n : ℕ} (K : ℕ) (wSrc wDst : Fin K → Wire n) (hne : ∀ i, wSrc i ≠ wDst i) :
    (seqCnotVec K wSrc wDst hne).count .T = 0 ∧ (seqCnotVec K wSrc wDst hne).count .TOFF = 0 :=
  ⟨(count_seqNat_T 0 K _ fun _ _ ↦ by simp [Circuit.CNOT]).trans (Nat.mul_zero K),
      count_seqNat_TOFF_zero K _ fun _ _ ↦ by simp [Circuit.CNOT]⟩
@[simp] theorem count_seqCnotVec_t {n : ℕ} (K : ℕ) (wSrc wDst : Fin K → Wire n) (hne : ∀ i,
  wSrc i ≠ wDst i) : (seqCnotVec K wSrc wDst hne).count .T = 0 :=
      (count_seqCnotVec K wSrc wDst hne).1
@[simp] theorem count_seqCnotVec_toff {n : ℕ} (K : ℕ) (wSrc wDst : Fin K → Wire n) (hne : ∀ i,
  wSrc i ≠ wDst i) : (seqCnotVec K wSrc wDst hne).count .TOFF = 0 :=
      (count_seqCnotVec K wSrc wDst hne).2
theorem cw_seqCnotVec {n : ℕ} {S : Wire n → Prop} (K : ℕ) (wSrc wDst : Fin K → Wire n)
    (hne : ∀ i, wSrc i ≠ wDst i) (hs : ∀ i, S (wSrc i))
    (hd : ∀ i, S (wDst i)) : CircWires S (seqCnotVec K wSrc wDst hne) :=
  cw_seqNat K _ fun i hi ↦ cw_cnot (hs ⟨i, hi⟩) (hd ⟨i, hi⟩)
theorem seqCnotVec_mulVec_zero {n : ℕ} (K : ℕ) (wSrc wDst : Fin K → Wire n)
    (hne : ∀ i, wSrc i ≠ wDst i) (δ : BitAssignment n) (h0 : ∀ i : Fin K, δ (wSrc i) = 0) :
    (seqCnotVec K wSrc wDst hne).eval.1.mulVec (ket δ) = ket δ :=
  seqNat_mulVec_fixed (ket δ) K _ fun i hi ↦
      by rw [ket_CNOT, h0 ⟨i, hi⟩, add_zero, Function.update_eq_self]
theorem seqCnotVec_mulVec_oneHot {n : ℕ} (K : ℕ) (wSrc wDst : Fin K → Wire n)
    (hne : ∀ i, wSrc i ≠ wDst i) (hDisj : ∀ i j, wSrc i ≠ wDst j)
    (δ : BitAssignment n) (iStar : Fin K) (h1 : ∀ i : Fin K, δ (wSrc i) = if i =
        iStar then 1 else 0) :
    (seqCnotVec K wSrc wDst hne).eval.1.mulVec (ket δ) = ket (Function.update δ (wDst iStar)
        (δ (wDst iStar) + 1)) := by
  refine (seqNat_mulVec_single (ket δ) (ket (Function.update δ (wDst iStar)
      (δ (wDst iStar) + 1))) iStar.val K
    (fun i hi ↦ Circuit.CNOT (wSrc ⟨i, hi⟩) (wDst ⟨i, hi⟩) (hne ⟨i, hi⟩))
    (fun i hi hlt ↦
        by rw [ket_CNOT, h1 ⟨i, hi⟩, ite_eq_right (hlt.ne ∘ congrArg Fin.val), add_zero,
             Function.update_eq_self])
    (fun hi' ↦
        by rw [ket_CNOT, show (⟨iStar.val, hi'⟩ : Fin K) = iStar from Fin.ext rfl, h1 iStar,
             ite_eq_left rfl])
    (fun i hi hgt ↦ by rw [ket_CNOT, Function.update_of_ne (hDisj ⟨i, hi⟩ iStar), h1 ⟨i, hi⟩,
      ite_eq_right (hgt.ne' ∘ congrArg Fin.val), add_zero,
          Function.update_eq_self])).trans (ite_eq_left iStar.isLt)

/-- `K` CNOTs gathering parity of `wSrc[0..K-1]` into a single target wire `t`. -/
def seqGatherParity {n : ℕ} (K : ℕ) (wSrc : Fin K → Wire n) (t : Wire n) (hne : ∀ i, wSrc i ≠ t) :
    Circuit n := seqNat K fun i hi ↦ Circuit.CNOT (wSrc ⟨i, hi⟩) t (hne ⟨i, hi⟩)
theorem count_seqGatherParity {n : ℕ} (K : ℕ) (wSrc : Fin K → Wire n) (t : Wire n)
    (hne : ∀ i, wSrc i ≠ t) :
    (seqGatherParity K wSrc t hne).count .T = 0 ∧ (seqGatherParity K wSrc t hne).count .TOFF = 0 :=
        count_seqCnotVec K wSrc (fun _ ↦ t) hne
@[simp] theorem count_seqGatherParity_t {n : ℕ} (K : ℕ) (wSrc : Fin K → Wire n) (t : Wire n)
    (hne : ∀ i,
  wSrc i ≠ t) : (seqGatherParity K wSrc t hne).count .T = 0 :=
      (count_seqGatherParity K wSrc t hne).1
@[simp] theorem count_seqGatherParity_toff {n : ℕ} (K : ℕ) (wSrc : Fin K → Wire n) (t : Wire n)
    (hne : ∀ i,
  wSrc i ≠ t) : (seqGatherParity K wSrc t hne).count .TOFF = 0 :=
      (count_seqGatherParity K wSrc t hne).2
theorem cw_seqGatherParity {n : ℕ} {S : Wire n → Prop} (K : ℕ) (wSrc : Fin K → Wire n) (t : Wire n)
    (hne : ∀ i, wSrc i ≠ t)
    (hs : ∀ i, S (wSrc i)) (ht : S t) : CircWires S (seqGatherParity K wSrc t hne) :=
  cw_seqCnotVec K wSrc (fun _ ↦ t) hne hs (fun _ ↦ ht)
theorem eval_seqGatherParity_mul_self {n : ℕ} (K : ℕ) (wSrc : Fin K → Wire n) (t : Wire n)
    (hne : ∀ i, wSrc i ≠ t) :
    (seqGatherParity K wSrc t hne).eval.1 * (seqGatherParity K wSrc t hne).eval.1 = 1 :=
  seqNat_eval_mul_self K _ (fun _ _ ↦ eval_CNOT_mul_self_opt _ _ _)
      (fun i hi j hj ↦ eval_CNOT_comm _ _ (hne ⟨i, hi⟩) (hne ⟨j, hj⟩))
theorem seqGatherParity_mulVec_zero {n : ℕ} (K : ℕ) (wSrc : Fin K → Wire n) (t : Wire n)
    (hne : ∀ i, wSrc i ≠ t) (δ : BitAssignment n)
    (h0 : ∀ i : Fin K, δ (wSrc i) = 0) :
    (seqGatherParity K wSrc t hne).eval.1.mulVec (ket δ) = ket δ :=
        seqCnotVec_mulVec_zero K wSrc (fun _ ↦ t) hne δ h0
theorem seqGatherParity_mulVec_oneHot {n : ℕ} (K : ℕ) (wSrc : Fin K → Wire n) (t : Wire n)
    (hne : ∀ i, wSrc i ≠ t) (δ : BitAssignment n)
    (iStar : Fin K) (h1 : ∀ i : Fin K, δ (wSrc i) = if i = iStar then 1 else 0) :
    (seqGatherParity K wSrc t hne).eval.1.mulVec (ket δ) = ket (Function.update δ t (δ t + 1)) :=
      seqCnotVec_mulVec_oneHot K wSrc (fun _ ↦ t) hne (fun i _ ↦ hne i) δ iStar h1
abbrev uLo2_2 {n : ℕ} (r : RouterReg 187 8 n) (d : Fin 2) : Wire n :=
  rIdx2 r ⟨d.val, by have := d.isLt; omega⟩

theorem buf96_inj {n : ℕ} (r : RouterReg 187 8 n) {i₁ i₂ : Fin 96} (heq : buf96 r i₁ = buf96 r i₂) :
    i₁ = i₂ := by
  have hv := congrArg Fin.val (r.wires.injective heq)
  dsimp [buf96] at hv; exact Fin.ext (by omega)

theorem wB24_inj {n : ℕ} (r : RouterReg 187 8 n) {q₁ q₂ : Fin 24} (heq : wB24 r q₁ = wB24 r q₂) :
    q₁ = q₂ := by
  have hv := congrArg Fin.val (r.wires.injective heq)
  have := q₁.isLt; have := q₂.isLt
  unfold idxB24Val at hv; dsimp at hv
  exact Fin.ext (by split_ifs at hv <;> omega)

theorem r_idx_ne_buf96 {n : ℕ} (r : RouterReg 187 8 n) (j : Fin (routerWidth 187 8)) (i : Fin 96)
    (hj : j.val < 18 ∨ 114 ≤ j.val) : r j ≠ buf96 r i :=
  rr_ne r (by have := i.isLt; dsimp [buf96]; omega)

theorem rRawHas2_ne_wB24 {n : ℕ} (r : RouterReg 187 8 n) (q : Fin 24) : rRawHas2 r ≠ wB24 r q := by
  exact rr_ne r ((show ∀ q : Fin 24, 1 ≠ idxB24Val q.val by decide) q)

theorem rRawHas2_ne_rCtrlLo {n : ℕ} (r : RouterReg 187 8 n) (p : Fin 187) : rRawHas2 r ≠
    rCtrlLo r p := by
  exact rr_ne r (Nat.ne_of_lt (show 1 < 4624 + p.val by omega))

theorem wB24_ne_rCtrlLo {n : ℕ} (r : RouterReg 187 8 n) (q : Fin 24) (p : Fin 187) : wB24 r q ≠
    rCtrlLo r p :=
  rr_ne r (by have := q.isLt; have := p.isLt; unfold idxB24Val basePub; dsimp; split_ifs <;> omega)

theorem wB24_ne_rDumE {n : ℕ} (r : RouterReg 187 8 n) (q : Fin 24) : wB24 r q ≠ rDumE r :=
  rr_ne r (by have := q.isLt; unfold idxB24Val; dsimp; split_ifs <;> omega)

theorem wB24_ne_buf96 {n : ℕ} (r : RouterReg 187 8 n) (q : Fin 24) (i : Fin 96) : wB24 r q ≠
    buf96 r i :=
  r_idx_ne_buf96 r _ i (Or.inr (by have := q.isLt; unfold idxB24Val; dsimp; split_ifs <;> omega))

theorem buf96_ne_rCtrlLo {n : ℕ} (r : RouterReg 187 8 n) (i : Fin 96) (p : Fin 187) : buf96 r i ≠
    rCtrlLo r p :=
  (r_idx_ne_buf96 r _ i (Or.inr (by have := p.isLt; unfold basePub; dsimp; omega))).symm
theorem idxHi5_2_lt24_of_lt187 {n : ℕ} (r : RouterReg 187 8 n) {γ : BitAssignment n}
    (hlt : idxValD (rIdx2 r) γ < 187) : idxValD (idxHi5_2 r) γ <
    24 := by have hd :=
               idxValD_8_div8 (rIdx2 r) γ; change idxValD (rIdx2 r) γ / 8 =
               idxValD (idxHi5_2 r) γ at hd; omega
theorem idxLo3_2_bit2_zero_of_q23 {n : ℕ} (r : RouterReg 187 8 n) {γ : BitAssignment n}
    (hlt : idxValD (rIdx2 r) γ < 187) (hq23 : idxValD (idxHi5_2 r) γ = 23) :
    idxValPrefix (uLo2_2 r) γ 2 le_rfl = idxValD (idxLo3_2 r) γ := by
  have hsp :=
      idxValD_8_split35 (rIdx2 r) γ; change idxValD (rIdx2 r) γ = 8 * idxValD (idxHi5_2 r) γ +
      idxValD (idxLo3_2 r) γ at hsp; rw [hq23] at hsp
  have hlo3 : idxValD (idxLo3_2 r) γ < 3 := by omega
  have hb2 : ¬ γ (idxLo3_2 r ⟨2, by omega⟩) = 1 := by
    intro h1; dsimp only [idxValD, idxValPrefix] at hlo3
    rw [ite_eq_left h1] at hlo3; omega
  dsimp only [idxValD, idxValPrefix, uLo2_2, idxLo3_2]
  rw [ite_eq_right hb2]; omega
abbrev predTrueOpt {n : ℕ} (_ : BitAssignment n) : Prop := True
section
attribute [local irreducible] uRouterSwapConj
attribute [local semireducible] ComputeProg.ValidProg ComputeProg.finalClean ComputeProg.fwdBits
    DynQromUncompA.fwdCirc
/- Section 5a: 0-T B24 CNOT scrub and rBot5015 header preparation -/
theorem rw187_lt_1 : 1 < routerWidth 187 8 := by rw [rw187_eq]; omega

theorem rRawHas2_eq_r1 {n : ℕ} (r : RouterReg 187 8 n) :
    rRawHas2 r = r ⟨1, rw187_lt_1⟩ := rfl

theorem rRawHas2_ne_r {n : ℕ} (r : RouterReg 187 8 n) {j : Fin (routerWidth 187 8)}
    (hj : j.val ≠ 1) : rRawHas2 r ≠
    r j := by intro e; have hv : (⟨1, rw187_lt_1⟩ : Fin (routerWidth 187 8)).val = j.val :=
                         congrArg Fin.val (r.wires.injective e); exact hj hv.symm
theorem privZero_of_ge4602 {n : ℕ} (r : RouterReg 187 8 n) {β : BitAssignment n}
    (hβ : ValidZeroGatedSortedRouterInput r β) {u : Fin (routerWidth 187 8)} (hu : 4602 ≤ u.val) :
    β (r u) = 0 :=
  hβ.1.2.2.2.2 _ ((mem_sPrivCleanSet_iff r u).mpr (by rw [bp187_eq]; exact hu))

theorem wA24_ne_rCtrlLo {n : ℕ} (r : RouterReg 187 8 n) (q : Fin 24) (p : Fin 187) : wA24 r q ≠
    rCtrlLo r p :=
  rr_ne r (by
    have := q.isLt; have := p.isLt
    unfold idxA24Val basePub; dsimp; split_ifs <;> omega)

theorem pubCtrlSet_ne_wA24 {n : ℕ} (r : RouterReg 187 8 n) {w : Wire n} (hw : PubCtrlSet r w)
    (q : Fin 24) : w ≠ wA24 r q := by
  rcases hw with ⟨u, hu, rfl⟩
  exact rr_ne r (by have := q.isLt; unfold idxA24Val; dsimp; split_ifs <;> omega)
end
section
attribute [local semireducible] ComputeProg.ValidProg ComputeProg.finalClean ComputeProg.fwdBits
theorem numAnd_pUMsbHdrZG {M D n : ℕ} (hD2 : 2 ≤ D) (r : RouterReg M D n) :
    (pUMsbHdrZG hD2 r).numAnd = D -
    2 := by dsimp only [pUMsbHdrZG, ComputeProg.numAnd]; rw [numAnd_pUMsbDownLoop true r (D - 2)
              (hdr_lt2 hD2)]; omega
theorem validProg_pUMsbHdrZG {M D n : ℕ} (hD2 : 2 ≤ D) (r : RouterReg M D n) :
    (pUMsbHdrZG hD2 r).ValidProg ∅ (sCleanHdr (D - 2) r) := by
  let F := sCleanHdr (D - 2) r
  have hi2 : ∀ d, rIdx2 r d ∉ F := fun d hm ↦ by
    rcases Finset.mem_image.mp hm with ⟨d', _, eqw⟩
    exact rUMsb_ne_rIdx2 r d' d eqw
  have hTop : rUMsb r ⟨D - 1, hdr_lt1 (Nat.le_of_succ_le hD2)⟩ ∉ F := fun hm ↦ by
    have hlt := (mem_sCleanHdr_uMsb (D - 2) r ⟨D - 1, hdr_lt1 (Nat.le_of_succ_le hD2)⟩).mp hm
    dsimp at hlt; omega
  have hSub : rUMsb r ⟨D - 2, hdr_lt2 hD2⟩ ∉ F := fun hm ↦
      Nat.lt_irrefl (D - 2) ((mem_sCleanHdr_uMsb (D - 2) r _).mp hm)
  dsimp only [pUMsbHdrZG, ComputeProg.ValidProg, ComputeProg.finalClean];
  exact ⟨⟨⟨Finset.notMem_empty _, Finset.notMem_empty _, Or.inl hTop⟩, ⟨Finset.notMem_empty _,
      Finset.notMem_empty _, Or.inl hTop⟩, ⟨Finset.notMem_empty _, Finset.notMem_empty _,
      Or.inl hTop⟩, ⟨Finset.notMem_empty _, Finset.notMem_empty _, Or.inl hTop⟩,
      ⟨Finset.notMem_empty _, Finset.notMem_empty _, Or.inl hSub⟩, ⟨Finset.notMem_empty _,
      Finset.notMem_empty _, Or.inl hSub⟩⟩, validProg_pUMsbDownLoop true r (D - 2)
      (hdr_lt2 hD2) F hi2 (mem_sCleanHdr_uMsb (D - 2) r)⟩
theorem fwdBits_pUMsbHdrZG_of_ne_uMsb {M D n : ℕ} (hD2 : 2 ≤ D) (r : RouterReg M D n)
    (η : BitAssignment n) {w : Wire n} (hw : ∀ d : Fin D, w ≠ rUMsb r d) :
    (pUMsbHdrZG hD2 r).fwdBits η w =
    η w
    := by dsimp only [pUMsbHdrZG, ComputeProg.fwdBits]; rw [fwdBits_pUMsbDownLoop_of_ne_uMsb r (D -
            2) (hdr_lt2 hD2) _ hw]; simp only [Function.update_of_ne (hw _)]
end
section
attribute [local irreducible] uRouterSwapConj
attribute [local semireducible] ComputeProg.ValidProg ComputeProg.finalClean ComputeProg.fwdBits
    DynQromUncompA.fwdCirc
/- Section 5b: 18,936-T 24-plane step pElecPlanesOptA -/
theorem wRouterDisj_b24 {n : ℕ} (r : RouterReg 187 8 n) :
    WRouterDisj (rRawHas2 r) (idxHi5_2 r) (wB24 r) (qEncE r) where
  has_ne_out := rRawHas2_ne_wB24 r
  has_ne_q := rRawHas2_ne_r r (by dsimp; omega)
  idx_ne_out := fun d q ↦
      rr_ne r (by have := d.isLt; have := q.isLt; unfold idxB24Val; dsimp; split_ifs <;> omega)
  idx_ne_q := fun d ↦ rr_ne r (by have := d.isLt; dsimp; omega)
  out_inj := fun _ _ hne e ↦ hne (wB24_inj r e)
  out_ne_q := fun q ↦ rr_ne r (by have := q.isLt; unfold idxB24Val; dsimp; split_ifs <;> omega)

theorem wRouterDisj_a24 {n : ℕ} (r : RouterReg 187 8 n) :
    WRouterDisj (rHas1 r) (idxHi5_1 r) (wA24 r) (qEncE r) where
  has_ne_out := rHas1_ne_wA24 r
  has_ne_q := rr_ne r (by dsimp; omega)
  idx_ne_out := fun d q ↦
      rr_ne r (by have := d.isLt; have := q.isLt; unfold idxA24Val; dsimp; split_ifs <;> omega)
  idx_ne_q := fun d ↦ rr_ne r (by have := d.isLt; dsimp; omega)
  out_inj := fun _ _ hne e ↦ hne (wA24_inj r e)
  out_ne_q := fun q ↦ rr_ne r (by have := q.isLt; unfold idxA24Val; dsimp; split_ifs <;> omega)

abbrev uToggleB24 {n : ℕ} (r : RouterReg 187 8 n) : Unitary (2 ^ n) :=
    uOneHotToggle (rRawHas2 r) (idxHi5_2 r) (wB24 r)
    (wRouterDisj_b24 r).has_ne_out (wRouterDisj_b24 r).idx_ne_out
theorem pubCtrl_eq_routerCtrl_of_valid {n : ℕ} (r : RouterReg 187 8 n) {β : BitAssignment n}
    (hβ : ValidZeroGatedSortedRouterInput r β) : pubCtrlLo r β = routerCtrlLo r β ∧ pubCtrlHi r β =
    routerCtrlHi r β := by
  exact ⟨funext fun p ↦
      (cond_nat_beq _ _ _ _).trans (congrFun (routerCtrlLo_of_zeroGatedSorted hβ) p).symm,
    funext fun p ↦
        (cond_nat_beq _ _ _ _).trans (congrFun (routerCtrlHi_of_zeroGatedSorted hβ) p).symm⟩

theorem idxValD_zero_of_all_zero_8 {n : ℕ} (wIdx : Fin 8 → Wire n) {δ : BitAssignment n}
    (hz : ∀ d : Fin 8, δ (wIdx d) = 0) : idxValD wIdx δ =
    0 := by dsimp only [idxValD, idxValPrefix]; simp [hz]
theorem validZeroGated_idx_lt187 {n : ℕ} (r : RouterReg 187 8 n) {β : BitAssignment n}
    (hβ : ValidZeroGatedSortedRouterInput r β) : idxValD (rIdx1 r) β < 187 ∧ idxValD (rIdx2 r) β <
    187 ∧ (β (rHas1 r) = 0 → idxValD (rIdx1 r) β = 0) ∧ (β (rRawHas2 r) = 0 → idxValD (rIdx2 r) β =
    0) := by
  exact ⟨(zmod2_cases (β (rHas1 r))).elim (fun h0 ↦
      (idxValD_zero_of_all_zero_8 _ (hβ.2.1 h0)).symm ▸ by decide) hβ.1.2.1,
    (zmod2_cases (β (rRawHas2 r))).elim (fun h0 ↦
        (idxValD_zero_of_all_zero_8 _ (hβ.2.2.1 h0)).symm ▸ by decide) hβ.1.2.2.1,
    fun h0 ↦ idxValD_zero_of_all_zero_8 _ (hβ.2.1 h0), fun h0 ↦
        idxValD_zero_of_all_zero_8 _ (hβ.2.2.1 h0)⟩
end
section
attribute [local irreducible] uRouterSwapConj
/- Section 6a1: Post-swap support preservation and Bell/XorTargetLo commutations -/
/-- Wires modified by `cFixedSwapCirc r` (`rBufLo`, `rBufHi`, `rSys`, excluding `rHA` and `rHB`). -/
def ElecSwapModSet {M D n : ℕ} (r : RouterReg M D n) (w : Wire n) : Prop :=
    (∃ b : Fin 24, w = rBufLo r b) ∨ (∃ b : Fin 24, w = rBufHi r b) ∨ (∃ (b : Fin 24)
    (p : Fin M), w = rSys r p b)
theorem preservesKetPred_cFixedSwapCirc_elec {M D n : ℕ} (r : RouterReg M D n)
    (cLo cHi : Fin M → ZMod 2) {P : BitAssignment n → Prop}
    (hKeep : ∀ {u : Wire n}, ElecSwapModSet r u → ∀ α v, P α → P (Function.update α u v))
    {ψ : Fin (2 ^ n) → ℂ} (hψ : PreservesKetPred P ψ) :
    PreservesKetPred P ((cFixedSwapCirc r cLo cHi).eval.1.mulVec ψ) := by
  have hSV : ∀ (m : ℕ) (qB : Fin m → Wire n) (cV : Fin M → ZMod 2) (wT : Fin m → Fin M → Wire n)
      (hbt : ∀ k p, qB k ≠ wT k p) (hqB : ∀ k, ElecSwapModSet r (qB k))
      (hwT : ∀ k p, ElecSwapModSet r (wT k p)) {φ : Fin (2 ^ n) → ℂ}, PreservesKetPred P φ →
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
  have hwSys : ∀ (b : Fin 24) (p : Fin M), ElecSwapModSet r (rSys r p b) :=
    fun b p ↦ Or.inr (Or.inr ⟨b, p, rfl⟩)
  exact hSV 24 _ _ _ _ (fun b ↦ Or.inr (Or.inl ⟨b, rfl⟩)) hwSys
    (hSV 24 _ _ _ _ (fun b ↦ Or.inl ⟨b, rfl⟩) hwSys hψ)
/- Section 6a2: 0-T rHB collapse step and 24-T post-collapse rCtrlLo MBU unloader -/
theorem elecSwapModSet_idx {n : ℕ} (r : RouterReg 187 8 n) {u : Wire n} (hu : ElecSwapModSet r u) :
    ∃ j : Fin (routerWidth 187 8), u = r j ∧ ((18 ≤ j.val ∧ j.val < 66) ∨ (114 ≤ j.val ∧ j.val <
    4602)) := by
  rcases hu with ⟨b, rfl⟩ | ⟨b, rfl⟩ | ⟨b, p, rfl⟩
  · exact ⟨_, rfl, Or.inl ⟨by dsimp [rBufLo]; omega, by have := b.isLt; dsimp [rBufLo]; omega⟩⟩
  · exact ⟨_, rfl, Or.inl ⟨by dsimp [rBufHi]; omega, by have := b.isLt; dsimp [rBufHi]; omega⟩⟩
  · exact ⟨_, rfl, Or.inr ⟨by dsimp [rSys]; omega,
      by have := b.isLt; have := p.isLt; dsimp [rSys]; omega⟩⟩

theorem supportedOn_ketMap {n : ℕ} {P Q : BitAssignment n → Prop} {U : Operator (2 ^ n)}
    {g : BitAssignment n → BitAssignment n} (hKet : ∀ α, U.mulVec (ket α) = ket (g α))
    (hImp : ∀ α, P α → Q (g α)) {R : Operator (2 ^ n)} (hR : SupportedOn P R) : SupportedOn Q (U *
    R) := by
  intro A B hAB; rw [← Matrix.mul_assoc, ← Matrix.mul_assoc]
  refine hR (A * U) (B * U) fun α hα ↦ ?_
  change (A * U).mulVec (ket α) = (B * U).mulVec (ket α);
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hKet α]; exact hAB (g α) (hImp α hα)
/-- Clean-ancilla and public-control invariant preserved on `(uRouterSwapConj r).1 * R`. -/
def PostSwapClean {n : ℕ} (r : RouterReg 187 8 n) (α : BitAssignment n) : Prop :=
    (∀ b : Fin 24, α (rHA r b) = 0) ∧ (∀ b : Fin 24, α (rHB r b) = 0) ∧ (∀ p : Fin 187,
    α (rCtrlLo r p) = 0) ∧ (∀ q : Fin 24, α (wA24 r q) = 0) ∧ (∀ q : Fin 24, α (wB24 r q) = 0) ∧
    α (qEncE r) = 0 ∧ idxValD (rIdx1 r) α < 187 ∧ idxValD (rIdx2 r) α < 187 ∧ (α (rHas1 r) = 0 →
    ∀ d : Fin 8, α (rIdx1 r d) = 0) ∧ (α (rRawHas2 r) = 0 → ∀ d : Fin 8, α (rIdx2 r d) = 0) ∧
    pubCtrlLo r α = routerCtrlLo r α ∧ pubCtrlHi r α = routerCtrlHi r α
end
theorem sliceProd_eq_cond {n : ℕ} (wHas : Wire n) (wIdx : Fin 8 → Wire n)
    (γ : BitAssignment n) (p : Fin 187) :
    let wLo : Fin 3 → Wire n := fun d ↦ wIdx ⟨d.val, Nat.lt_of_lt_of_le d.isLt (by omega)⟩
    let wHi : Fin 5 → Wire n := fun d ↦ wIdx ⟨3 + d.val, Nat.add_lt_add_left d.isLt 3⟩
    (if idxValD wHi γ = p.val / 8 then γ wHas else 0) * (if idxValD wLo γ =
        p.val % 8 then γ wHas else 0) =
      cond (Nat.beq p.val (idxValD wIdx γ)) (γ wHas) 0 := by
  intro wLo wHi
  have hsp : idxValD wIdx γ = 8 * idxValD wHi γ + idxValD wLo γ := idxValD_8_split35 wIdx γ
  have hlo8 : idxValD wLo γ < 8 := idxValPrefix_lt_two_pow wLo γ 3 le_rfl
  rw [cond_nat_beq]
  if hp : p.val = idxValD wIdx γ then
    rw [ite_eq_left (by omega), ite_eq_left (by omega), ite_eq_left hp]
    exact (zmod2_cases (γ wHas)).elim (fun h ↦ by simp [h]) (fun h ↦ by simp [h])
  else if hq : idxValD wHi γ = p.val / 8 then
    rw [ite_eq_right (show idxValD wLo γ ≠ p.val % 8 by omega), mul_zero, ite_eq_right hp]
  else rw [ite_eq_right hq, zero_mul, ite_eq_right hp]
end
end QuantumComputation.Specs.PhotochemistrySolution.Stage2ElecOptA

namespace QuantumComputation.Specs.PhotochemistrySolution.WStateWalkSeam
noncomputable section
set_option exponentiation.threshold 8192
noncomputable section
open Operator QProg Matrix Circuit Qubit PrimitiveGate QuantumComputation.Specs
  PhotochemistrySolution.KetSupport PhotochemistrySolution PhotochemistrySolution.SplitRouter47_187
  PhotochemistrySolution.RouterSelectWiringA
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
open PhotochemistrySolution.RouterSelectWiringB PhotochemistrySolution.ProviderCore
  PhotochemistrySolution.Stage12Compact PhotochemistrySolution.ZeroNEremSpec
  PhotochemistrySolution.PotSelectWiring PhotochemistrySolution.Coin70Lift
  PhotochemistrySolution.Sub5885
open PhotochemistrySolution.OuterW11Bridge PhotochemistrySolution.GenWeightsSelect
  PhotochemistrySolution.ReflStage4 PhotochemistrySolution.SelectQft8GidneyStg3
  PhotochemistrySolution.ProviderCoreFused PhotochemistrySolution.ProviderZeroFloor
open PhotochemistrySolution.Sub5885MuxD1 PhotochemistrySolution.FastQft8
  PhotochemistrySolution.Kinetic664 PhotochemistrySolution.Kinetic664Stage4
  PhotochemistrySolution.Qft8PostCancelT5
open _root_.DynamicCircuit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt hiding bit_cases
  eval_seq_mulVec ket ket_CNOT ket_TOFF ket_X ket_projector_one ket_projector_zero localIdx
  matrix_ext_ket qAssign_obs_map_val
open PhotochemistrySolution.DepthArithWalk PhotochemistrySolution.KinNormSlice
  PhotochemistrySolution.TopSelectBridge PhotochemistrySolution.SelectQft8KinMid
  PhotochemistrySolution.PotOracleGen
open _root_.QuantumComputation.Specs.PhotochemistrySolution.QubitizationWalkSem (sqrtHalf bitSign
    bitSign_zero)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SelectFastQft8Gidney (spliceUnitary
    spliceUnitaryMat)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB (ket matrix_ext_ket)
local instance (priority := 100000) {k : ℕ} : NeZero (2 ^ k) := ⟨pow_ne_zero k two_ne_zero⟩
theorem val_locGrad3HiLayout_wstate (j : Fin 3) : (locGrad3HiLayout j).val = 5647 + j.val := by
  have hj : (locGrad3HiLayout j).val = systemQubits_frozen + (31 + j.val) :=
      rfl; rw [hj, hSys5616_fused]; omega
attribute [local reducible] totDimCompactGen
attribute [local irreducible] systemQubits_frozen ancWOfScr uRouterSwapConj
    PgBase.phaseGradientState

theorem locGrad3HiLayout_eq_cat8_wstate (j : Fin 3) :
    locGrad3HiLayout j = locCat8SharedCompactGen scrWLayout ⟨5 + j.val, by omega⟩ :=
  Fin.ext (by rw [val_locGrad3HiLayout_wstate, val_locCat8_layout]; dsimp only; omega)

theorem hoff_locGrad3HiLayout_wstate :
    OffIndexAndScratchPoly systemQubits_frozen scrWLayout (lcuSubLGen hpLayout)
    (scrSubLGen hpLayout) locGrad3HiLayout :=
  fun j ↦ locGrad3HiLayout_eq_cat8_wstate j ▸ hoff_cat8_layout ⟨5 + j.val, by omega⟩

theorem val_rCoinExtOut_coinBand7256_wstate {kExt kOut : ℕ} (hk : kExt ≤ 72)
    (rSub : QRegister kOut 41) (u : Fin (kExt + kOut)) : 7143 ≤ (rCoinExtOut hk rSub u).val ∧
    (rCoinExtOut hk rSub u).val < 7256 := by have hb := val_rCoinExtOut_bounds hk rSub u; omega
/--
Pure-unitary `(kExt + kOut)`-coin Stage-4 slice package decoupled from router/clean-pool
implementation.
-/
structure Stage4OuterSubUnitaryPkgWs (kExt kOut w1 : ℕ) (hk : kExt ≤ 72)
    (rSub : QRegister kOut 41) (decode : Fin (2 ^ 41) → ZeroNEremSector)
    (o1 : Stage1ZeroNEremLayout w1 decode)
    (peKOut : BitAssignment (kExt + kOut) → PotExpectFn) where
  uIdSlice : BitAssignment (kExt + kOut) → Unitary (2 ^ dLayout)
  uUselSlice : BitAssignment (kExt + kOut) → Unitary (2 ^ dLayout)
  uCselSlice : BitAssignment (kExt + kOut) → Unitary (2 ^ dLayout)
  comm_coinExtOut : ∀ γω (M : Operator (2 ^ (kExt + kOut))),
    Commute (uIdSlice γω).1 ((rCoinExtOut hk rSub).embedMatrix M) ∧
    Commute (uUselSlice γω).1 ((rCoinExtOut hk rSub).embedMatrix M) ∧
    Commute (uCselSlice γω).1 ((rCoinExtOut hk rSub).embedMatrix M)
  hCtrlSlice : ∀ γω, (uCselSlice γω).1 =
    (1 - projOneQCompactGen scrWLayout) + projOneQCompactGen scrWLayout * (uUselSlice γω).1
  hCatSlice : ∀ γω,
    (uUselSlice γω).1 * cat8SharedProjCompactGen scrWLayout =
      (uIdSlice γω).1 * cat8SharedProjCompactGen scrWLayout
  hIdOff : ∀ γω {k : ℕ} (r : QRegister k dLayout),
    OffIndexAndScratchPoly systemQubits_frozen scrWLayout (lcuSubLGen hpLayout)
        (scrSubLGen hpLayout) r →
    ∀ M : Operator (2 ^ k), Commute (uIdSlice γω).1 (r.embedMatrix M)
  comm_scr : ∀ γω, CommScr (preLoc o1.uLocal (uIdSlice γω)) ∧
    CommScr (preLoc o1.uLocal (uUselSlice γω)) ∧
    CommScr (preLoc o1.uLocal (uCselSlice γω))
  hInvolPreScr : ∀ γω,
    preLoc o1.uLocal (uIdSlice γω) * (preLoc o1.uLocal (uIdSlice γω) * pScr) = pScr
  comm_grad3Hi : ∀ γω (M : Operator (2 ^ 3)),
    Commute (uUselSlice γω).1 ((locGrad3HiCompactGen scrWLayout).embedMatrix M) ∧
    Commute (uCselSlice γω).1 ((locGrad3HiCompactGen scrWLayout).embedMatrix M)
  sum_z41_slice : ∀ γω {β : BitAssignment dLayout},
    (∀ u, β (rLcu82Layout u) = 0) → CleanScr β → ∀ c,
    (∑ z : BitAssignment 41, (rLcu82Layout.basisOutcomeProjector 0 * (uHad82Layout⁻¹).1).mulVec
      ((((wNoHad o1.uLocal)⁻¹ * uIdSlice γω * wNoHad o1.uLocal).1).mulVec
        (ket (routedStage0 β c z)))) =
      (sqrtHalf ^ 82) •
        (rSysLayout.embedMatrix (bOuterZeroNErem decode (peKOut γω) c)).mulVec (ket β)
section
attribute [local reducible] totDimCompactGen
attribute [local irreducible] systemQubits_frozen ancWOfScr uRouterSwapConj
    PgBase.phaseGradientState
theorem huId_wstate {kExt kOut w1 : ℕ} {decode : Fin (2 ^ 41) → ZeroNEremSector}
    {peKOut : BitAssignment (kExt + kOut) → PotExpectFn} {hk : kExt ≤ 72} {rSub : QRegister kOut 41}
    {o1 : Stage1ZeroNEremLayout w1 decode}
    (s4 : Stage4OuterSubUnitaryPkgWs kExt kOut w1 hk rSub decode o1 peKOut)
    (γω : BitAssignment (kExt + kOut)) (M : Operator (2 ^ (kExt + kOut))) :
    Commute (s4.uIdSlice γω).1 ((rCoinExtOut hk rSub).embedMatrix M) := (s4.comm_coinExtOut γω M).1
theorem huUsel_wstate {kExt kOut w1 : ℕ} {decode : Fin (2 ^ 41) → ZeroNEremSector}
    {peKOut : BitAssignment (kExt + kOut) → PotExpectFn} {hk : kExt ≤ 72} {rSub : QRegister kOut 41}
    {o1 : Stage1ZeroNEremLayout w1 decode}
    (s4 : Stage4OuterSubUnitaryPkgWs kExt kOut w1 hk rSub decode o1 peKOut)
    (γω : BitAssignment (kExt + kOut)) (M : Operator (2 ^ (kExt + kOut))) :
    Commute (s4.uUselSlice γω).1 ((rCoinExtOut hk rSub).embedMatrix M) :=
    (s4.comm_coinExtOut γω M).2.1
theorem huCsel_wstate {kExt kOut w1 : ℕ} {decode : Fin (2 ^ 41) → ZeroNEremSector}
    {peKOut : BitAssignment (kExt + kOut) → PotExpectFn} {hk : kExt ≤ 72} {rSub : QRegister kOut 41}
    {o1 : Stage1ZeroNEremLayout w1 decode}
    (s4 : Stage4OuterSubUnitaryPkgWs kExt kOut w1 hk rSub decode o1 peKOut)
    (γω : BitAssignment (kExt + kOut)) (M : Operator (2 ^ (kExt + kOut))) :
    Commute (s4.uCselSlice γω).1 ((rCoinExtOut hk rSub).embedMatrix M) :=
  (s4.comm_coinExtOut γω M).2.2

/-- Ideal multiplexed `(kExt + kOut)`-coin Stage-4 unitary. -/
def uIdMuxWState {kExt kOut w1 : ℕ} {decode : Fin (2 ^ 41) → ZeroNEremSector}
    {peKOut : BitAssignment (kExt + kOut) → PotExpectFn} (hk : kExt ≤ 72) (rSub : QRegister kOut 41)
    (o1 : Stage1ZeroNEremLayout w1 decode)
    (s4 : Stage4OuterSubUnitaryPkgWs kExt kOut w1 hk rSub decode o1 peKOut) : Unitary (2 ^ dLayout)
    :=
  uMuxExtOut hk rSub s4.uIdSlice (huId_wstate s4)

/-- Unguarded cat multiplexed `(kExt + kOut)`-coin Stage-4 unitary. -/
def uUselMuxWState {kExt kOut w1 : ℕ} {decode : Fin (2 ^ 41) → ZeroNEremSector}
    {peKOut : BitAssignment (kExt + kOut) → PotExpectFn} (hk : kExt ≤ 72) (rSub : QRegister kOut 41)
    (o1 : Stage1ZeroNEremLayout w1 decode)
    (s4 : Stage4OuterSubUnitaryPkgWs kExt kOut w1 hk rSub decode o1 peKOut) : Unitary (2 ^ dLayout)
    :=
  uMuxExtOut hk rSub s4.uUselSlice (huUsel_wstate s4)

/-- Controlled cat multiplexed `(kExt + kOut)`-coin Stage-4 unitary. -/
def uCselMuxWState {kExt kOut w1 : ℕ} {decode : Fin (2 ^ 41) → ZeroNEremSector}
    {peKOut : BitAssignment (kExt + kOut) → PotExpectFn} (hk : kExt ≤ 72) (rSub : QRegister kOut 41)
    (o1 : Stage1ZeroNEremLayout w1 decode)
    (s4 : Stage4OuterSubUnitaryPkgWs kExt kOut w1 hk rSub decode o1 peKOut) : Unitary (2 ^ dLayout)
    := uMuxExtOut hk rSub s4.uCselSlice (huCsel_wstate s4)
theorem uMuxWState_ctrl_and_cat {kExt kOut w1 : ℕ} {decode : Fin (2 ^ 41) → ZeroNEremSector}
    {peKOut : BitAssignment (kExt + kOut) → PotExpectFn} (hk : kExt ≤ 72) (rSub : QRegister kOut 41)
    (o1 : Stage1ZeroNEremLayout w1 decode)
    (s4 : Stage4OuterSubUnitaryPkgWs kExt kOut w1 hk rSub decode o1 peKOut) :
    (uCselMuxWState hk rSub o1 s4).1 = (1 - projOneQCompactGen scrWLayout) +
    projOneQCompactGen scrWLayout * (uUselMuxWState hk rSub o1 s4).1 ∧
    (uUselMuxWState hk rSub o1 s4).1 * cat8SharedProjCompactGen scrWLayout =
    (uIdMuxWState hk rSub o1 s4).1 * cat8SharedProjCompactGen scrWLayout := by
  let rCO := rCoinExtOut hk rSub; let Pq := projOneQCompactGen scrWLayout;
  let Pc := cat8SharedProjCompactGen scrWLayout;
  have dCO := rCoinExtOut_disj_off hk rSub hoff_cat8_layout
  have cPc : ∀ γω, projBits_c70 rCO γω * Pc = Pc * projBits_c70 rCO γω := fun γω ↦ by
    rw [projBits_eq_embedMatrix_c70 rCO γω];
    exact rCO.embedMatrix_comm_of_disjoint (locCat8SharedCompactGen scrWLayout) dCO _ _
  refine ⟨?_, ?_⟩
  · simp only [uCselMuxWState, uUselMuxWState, uMuxExtOut_val, muxMat_c70]
    rw [show (1 : Operator (2 ^ dLayout)) - Pq = (1 - Pq) * ∑ γω, projBits_c70 rCO γω by
      rw [sum_projBits_c70 rCO, Matrix.mul_one], Matrix.mul_sum, Matrix.mul_sum,
          ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun γω _ ↦ by rw [s4.hCtrlSlice γω, add_mul, Matrix.mul_assoc]
  · simp only [uUselMuxWState, uIdMuxWState, uMuxExtOut_val, muxMat_c70, Finset.sum_mul]
    exact Finset.sum_congr rfl fun γω _ ↦ by
      rw [Matrix.mul_assoc, cPc γω, ← Matrix.mul_assoc, s4.hCatSlice γω, Matrix.mul_assoc, ← cPc γω,
          ← Matrix.mul_assoc]

theorem comm_pScrExt_id_wstate {kExt kOut w1 : ℕ} {decode : Fin (2 ^ 41) → ZeroNEremSector}
    {peKOut : BitAssignment (kExt + kOut) → PotExpectFn} (hk : kExt ≤ 72) (rSub : QRegister kOut 41)
    (o1 : Stage1ZeroNEremLayout w1 decode)
    (s4 : Stage4OuterSubUnitaryPkgWs kExt kOut w1 hk rSub decode o1 peKOut) : pScrExt kExt hk *
    (uPreExt hk decode (uIdMuxWState hk rSub o1 s4)).1 =
    (uPreExt hk decode (uIdMuxWState hk rSub o1 s4)).1 * pScrExt kExt hk :=
    comm_pScrExt_uPreExt_outerSub hk rSub o1 s4.uIdSlice (huId_wstate s4)
    (fun γω ↦ (s4.comm_scr γω).1)
theorem comm_pScrExt_usel_wstate {kExt kOut w1 : ℕ} {decode : Fin (2 ^ 41) → ZeroNEremSector}
    {peKOut : BitAssignment (kExt + kOut) → PotExpectFn} (hk : kExt ≤ 72) (rSub : QRegister kOut 41)
    (o1 : Stage1ZeroNEremLayout w1 decode)
    (s4 : Stage4OuterSubUnitaryPkgWs kExt kOut w1 hk rSub decode o1 peKOut) : pScrExt kExt hk *
    (uPreExt hk decode (uUselMuxWState hk rSub o1 s4)).1 =
    (uPreExt hk decode (uUselMuxWState hk rSub o1 s4)).1 * pScrExt kExt hk :=
    comm_pScrExt_uPreExt_outerSub hk rSub o1 s4.uUselSlice (huUsel_wstate s4)
    (fun γω ↦ (s4.comm_scr γω).2.1)
theorem comm_pScrExt_csel_wstate {kExt kOut w1 : ℕ} {decode : Fin (2 ^ 41) → ZeroNEremSector}
    {peKOut : BitAssignment (kExt + kOut) → PotExpectFn} (hk : kExt ≤ 72) (rSub : QRegister kOut 41)
    (o1 : Stage1ZeroNEremLayout w1 decode)
    (s4 : Stage4OuterSubUnitaryPkgWs kExt kOut w1 hk rSub decode o1 peKOut) : pScrExt kExt hk *
    (uPreExt hk decode (uCselMuxWState hk rSub o1 s4)).1 =
    (uPreExt hk decode (uCselMuxWState hk rSub o1 s4)).1 * pScrExt kExt hk :=
    comm_pScrExt_uPreExt_outerSub hk rSub o1 s4.uCselSlice (huCsel_wstate s4)
    (fun γω ↦ (s4.comm_scr γω).2.2)
theorem whole_compose_wstate {k : ℕ} (r : QRegister k dLayout) :
    (QRegister.whole dLayout).compose r = r :=
  congrArg QRegister.mk (Function.Embedding.ext fun _ ↦ rfl)

theorem lift_whole_pScrExt_wstate {kExt : ℕ} (hk : kExt ≤ 72) {L₁ L₂ : Operator (2 ^ dLayout)}
    (hRk : L₁ * pScr = L₂ * pScr)
    (c₁ : ∀ M : Operator (2 ^ kExt), Commute L₁ ((rCoinExt kExt hk).embedMatrix M))
    (c₂ : ∀ M : Operator (2 ^ kExt), Commute L₂ ((rCoinExt kExt hk).embedMatrix M)) :
    L₁ * pScrExt kExt hk = L₂ * pScrExt kExt hk :=
  lift_eq_of_pScrExt_c70 hk (QRegister.whole dLayout) (L₁ := L₁) (L₂ := L₂) (X := pScrExt kExt hk)
    (by rwa [whole_compose_wstate])
    (fun δ ↦ by
      rw [whole_compose_wstate, ← embedUnitary_uTogLocal_c70]
      exact (c₁ _).eq)
    (fun δ ↦ by
      rw [whole_compose_wstate, ← embedUnitary_uTogLocal_c70]
      exact (c₂ _).eq)
    (by simpa only [whole_compose_wstate] using pScrExt_idem kExt hk)

theorem invol_pScrExt_wstate {kExt kOut w1 : ℕ} {decode : Fin (2 ^ 41) → ZeroNEremSector}
    {peKOut : BitAssignment (kExt + kOut) → PotExpectFn} (hk : kExt ≤ 72) (rSub : QRegister kOut 41)
    (o1 : Stage1ZeroNEremLayout w1 decode)
    (s4 : Stage4OuterSubUnitaryPkgWs kExt kOut w1 hk rSub decode o1 peKOut) :
    (uPreExt hk decode (uIdMuxWState hk rSub o1 s4)).1 *
    ((uPreExt hk decode (uIdMuxWState hk rSub o1 s4)).1 * pScrExt kExt hk) = pScrExt kExt hk := by
  let huI := huId_wstate s4; let rC := rCoinExt kExt hk; let P_ext := pScrExt kExt hk
  have cScrR : ∀ M : Operator (2 ^ kExt), Commute P_ext (rC.embedMatrix M) := fun M ↦
      (rC.embedMatrix_comm_of_disjoint (rScrExt kExt hk)
      (rCoinExt_disj_helpers_c70 hk).2.1 M (compProj 0)).symm
  have hSliceRk : ∀ γω,
      ((preConj (uStage1Clean_c70 decode) (s4.uIdSlice γω)).1 *
        (preConj (uStage1Clean_c70 decode) (s4.uIdSlice γω)).1) * pScr = pScr := fun γω ↦ by
    let Mc := (preConj (uStage1Clean_c70 decode) (s4.uIdSlice γω)).1;
    let Mo := preLoc o1.uLocal (s4.uIdSlice γω); have hCMo := (s4.comm_scr γω).1;
    have hEqRk := (preConj_uStage1Clean_c70 o1 _ hCMo).1
    have hAbsMo : pScr * (Mo * pScr) = Mo * pScr := by
      rw [← Matrix.mul_assoc, hCMo, Matrix.mul_assoc, pScr_idem]
    rw [Matrix.mul_assoc, hEqRk, ← hAbsMo, ← Matrix.mul_assoc Mc, hEqRk, Matrix.mul_assoc, hAbsMo,
        s4.hInvolPreScr γω]
  have hOutExt (γ : BitAssignment kExt) : ((preConj (uStage1Clean_c70 decode)
      (uMuxOut hk rSub s4.uIdSlice huI γ)).1 *
      (preConj (uStage1Clean_c70 decode) (uMuxOut hk rSub s4.uIdSlice huI γ)).1) * P_ext =
          P_ext := by
    have cF := preConjClean_comm_rCoinExt_c70 decode hk _ (uMuxOut_comm_rCoinExt hk rSub huI γ)
    simpa only [Matrix.one_mul] using lift_whole_pScrExt_wstate hk (by
        rw [Matrix.one_mul, preConjClean_uMuxOut_eq decode hk rSub huI γ]
        exact sum_mul_orthProj_sq_eq (fun ω ↦ (preConj (uStage1Clean_c70 decode)
            (s4.uIdSlice (concatBitsGen γ ω))).1)
          (qOutHad rSub) pScr (sum_qOutHad rSub) (qOutHad_mul rSub)
          (fun ω ω' ↦
              (preConjClean_comm_qOutHad decode rSub ω _ (slice_comm_projBits_rOut hk rSub huI γ ω'
              ω)).symm.eq)
          (fun ω ↦ (comm_pScr_qOutHad rSub ω).symm.eq) fun ω ↦ hSliceRk (concatBitsGen γ ω))
      (fun M ↦ (cF M).mul_left (cF M)) fun _ ↦ Commute.one_left _
  let uP := preConj (uStage1Clean_c70 decode) (uIdMuxWState hk rSub o1 s4)
  have hMid : uP.1 * (uP.1 * P_ext) = P_ext := by
    dsimp only [uP, uIdMuxWState]; unfold uMuxExtOut
    rw [← Matrix.mul_assoc,
        preConjClean_mux_eq_c70 decode hk _ (uMuxOut_comm_projBits_rCoinExt hk rSub huI)]
    exact sum_mul_orthProj_sq_eq (fun γ ↦ (preConj (uStage1Clean_c70 decode)
        (uMuxOut hk rSub s4.uIdSlice huI γ)).1)
      (projBits_c70 rC) P_ext (sum_projBits_c70 rC) (projBits_mul_c70 rC)
      (fun γ δ ↦ by simpa only [projBits_eq_embedMatrix_c70 rC γ] using
        (preConjClean_comm_rCoinExt_c70 decode hk _ (uMuxOut_comm_rCoinExt hk rSub huI δ)
            _).symm.eq)
      (fun γ ↦ by simpa only [projBits_eq_embedMatrix_c70 rC γ] using (cScrR _).symm.eq) hOutExt
  have cHfP : (uHadCoinExt hk).1 * P_ext = P_ext * (uHadCoinExt hk).1 :=
      (uHadCoinExt_eq_embed_c70 hk).1 ▸ (cScrR _).symm.eq
  have hCanc : (uHadCoinExt hk).1 * (uHadCoinExt hk)⁻¹.1 = 1 := by
    rw [← Submonoid.coe_mul, mul_inv_cancel, OneMemClass.coe_one]
  have hCancI : (uHadCoinExt hk)⁻¹.1 * (uHadCoinExt hk).1 = 1 := by
    rw [← Submonoid.coe_mul, inv_mul_cancel, OneMemClass.coe_one]
  simp only [uPreExt, Submonoid.coe_mul, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (uHadCoinExt hk).1 (uHadCoinExt hk)⁻¹.1, hCanc, Matrix.one_mul, cHfP,
    ← Matrix.mul_assoc uP.1 P_ext, ← Matrix.mul_assoc uP.1 (uP.1 * P_ext), hMid, ← cHfP,
        ← Matrix.mul_assoc, hCancI, Matrix.one_mul]
theorem block_pScrExt_wstate {kExt kOut w1 : ℕ} {decode : Fin (2 ^ 41) → ZeroNEremSector}
    {peKOut : BitAssignment (kExt + kOut) → PotExpectFn} (hk : kExt ≤ 72) (rSub : QRegister kOut 41)
    (o1 : Stage1ZeroNEremLayout w1 decode)
    (s4 : Stage4OuterSubUnitaryPkgWs kExt kOut w1 hk rSub decode o1 peKOut) {A : OpSys}
    (hAvgOp : (2 ^ kExt : ℂ)⁻¹ • ∑ γ : BitAssignment kExt, ((2 ^ 82 : ℂ)⁻¹ • ∑ c : Fin (2 ^ 41),
    bOuterZeroNErem decode (peKOut (concatBitsGen γ (outSubRawBits rSub c))) c) = A) :
    lcuProjPoly systemQubits_frozen scrWLayout (lcuSubLGen (hpExt kExt hk)) *
    (uPreExt hk decode (uIdMuxWState hk rSub o1 s4)).1 *
    lcuProjPoly systemQubits_frozen scrWLayout (lcuSubLGen (hpExt kExt hk)) * pScrExt kExt hk =
    (locSysPoly systemQubits_frozen scrWLayout).embedMatrix A *
    lcuProjPoly systemQubits_frozen scrWLayout (lcuSubLGen (hpExt kExt hk)) * pScrExt kExt hk := by
  let rC := rCoinExt kExt hk; let Pc := rC.basisOutcomeProjector 0;
  let L8 := lcuProjPoly systemQubits_frozen scrWLayout (lcuSubLGen hpLayout);
  let Le := lcuProjPoly systemQubits_frozen scrWLayout (lcuSubLGen (hpExt kExt hk));
  let P_ext := pScrExt kExt hk; let rS := locSysPoly systemQubits_frozen scrWLayout
  let A_γ : BitAssignment kExt → OpSys := fun γ ↦
      (2 ^ 82 : ℂ)⁻¹ • ∑ c : Fin (2 ^ 41),
      bOuterZeroNErem decode (peKOut (concatBitsGen γ (outSubRawBits rSub c))) c
  obtain ⟨hD1, hD2, hD3, _⟩ := rCoinExt_disj_helpers_c70 hk; obtain ⟨hSplit, cPcL8⟩ :=
      lcuProj_ext_split_c70 hk
  have cL8R : ∀ M : Operator (2 ^ kExt), Commute L8 (rC.embedMatrix M) := fun M ↦
      (rC.embedMatrix_comm_of_disjoint rLcu82Layout hD1 M (compProj 0)).symm
  have cScrR : ∀ M : Operator (2 ^ kExt), Commute P_ext (rC.embedMatrix M) := fun M ↦
      (rC.embedMatrix_comm_of_disjoint (rScrExt kExt hk) hD2 M (compProj 0)).symm
  have cSysR : ∀ (B : Operator (2 ^ systemQubits_frozen)) (M : Operator (2 ^ kExt)),
      Commute (rS.embedMatrix B) (rC.embedMatrix M) := fun B M ↦
      (rC.embedMatrix_comm_of_disjoint rS hD3 M B).symm
  obtain ⟨hHf, hHi⟩ := uHadCoinExt_eq_embed_c70 hk
  have cL8Hf : L8 * (uHadCoinExt hk).1 = (uHadCoinExt hk).1 * L8 := by rw [hHf]; exact (cL8R _).eq
  have cL8Hi : L8 * (uHadCoinExt hk)⁻¹.1 = (uHadCoinExt hk)⁻¹.1 * L8 := by
    rw [hHi]; exact (cL8R _).eq
  have hSlice : ∀ γ : BitAssignment kExt,
      (L8 * (preConj (uStage1Clean_c70 decode)
          (uMuxOut hk rSub s4.uIdSlice (huId_wstate s4) γ)).1 * L8) * P_ext =
        (rS.embedMatrix (A_γ γ) * L8) * P_ext := fun γ ↦ by
    let W := wNoHad (uStage1Clean_c70 decode);
    let uOut := uMuxOut hk rSub s4.uIdSlice (huId_wstate s4) γ
    have hConjOut : (W⁻¹ * uOut * W).1 = muxMat_c70 (rOutLayout rSub)
        (fun ω ↦ W⁻¹ * s4.uIdSlice (concatBitsGen γ ω) * W) := by
      rw [Submonoid.coe_mul, Submonoid.coe_mul]
      change (W⁻¹).1 * muxMat_c70 (rOutLayout rSub) _ * W.1 = _
      simp only [muxMat_c70, Matrix.mul_sum, Finset.sum_mul, Submonoid.coe_mul, Matrix.mul_assoc]
      exact Finset.sum_congr rfl fun ω _ ↦
          by rw [(wNoHadClean_comm_projBits_rOutLayout decode rSub ω).symm.eq]
    have hEqRk : (L8 * (preConj (uStage1Clean_c70 decode) uOut).1 * L8) * pScr =
        (rS.embedMatrix (A_γ γ) * L8) * pScr :=
      block_encoding_of_ket rLcu82Layout rSysLayout rScrLayout (A_γ γ) uHad82Layout W uOut
          routedStage0
        (fun c ↦ bOuterZeroNErem decode (peKOut (concatBitsGen γ (outSubRawBits rSub c))) c) rfl
        (fun β hr0 ↦ (hadamardRegSym_unitary_mulVec_zero (Var :=
            Unit) wHasN1 82 rLcu82Layout hDisjHad82_layout β hr0).trans
          (congrArg ((sqrtHalf ^ 82) • ·)
              (sum_bitAssignment82 (fun δ ↦ ket (DynCircExt.writeReg β rLcu82Layout δ)))))
        (fun β hr0 hScr c ↦ by
          have hStep (z : BitAssignment 41) :
              ((W⁻¹ * uOut * W).1).mulVec (ket (routedStage0 β c z)) =
              (((wNoHad o1.uLocal)⁻¹ * s4.uIdSlice (concatBitsGen γ (outSubRawBits rSub c)) *
                  wNoHad o1.uLocal).1).mulVec
                (ket (routedStage0 β c z)) := by
            have hKetP : pScr.mulVec (ket (routedStage0 β c z)) = ket (routedStage0 β c z)
                := by
              rw [SelectRefl.ket_basisOutcomeProjector_zero,
                  ite_eq_left (cleanScr_routedStage0_ext hScr c z)]
            rw [hConjOut, muxMat_mulVec_ket, funext (routedStage0_rOutLayout rSub β c z)]
            conv_lhs => rw [← hKetP]
            rw [Matrix.mulVec_mulVec, wNoHad_conj_uStage1Clean_mul_pScr o1 _ (s4.comm_scr _).1,
                ← Matrix.mulVec_mulVec, hKetP]
          simp_rw [hStep]
          exact s4.sum_z41_slice (concatBitsGen γ (outSubRawBits rSub c)) hr0 hScr c)
    have cMc : ∀ M, Commute (preConj (uStage1Clean_c70 decode) uOut).1 (rC.embedMatrix M) :=
        preConjClean_comm_rCoinExt_c70 decode hk _ (uMuxOut_comm_rCoinExt hk rSub (huId_wstate s4)
        γ)
    exact lift_whole_pScrExt_wstate hk hEqRk
      (fun M ↦ ((cL8R M).mul_left (cMc M)).mul_left (cL8R M))
          (fun M ↦ (cSysR _ M).mul_left (cL8R M))
  have hExpand : Le * (uPreExt hk decode (uIdMuxWState hk rSub o1 s4)).1 * Le * P_ext = ∑ γ :
      BitAssignment kExt, Le * ((uHadCoinExt hk)⁻¹.1 * ((preConj (uStage1Clean_c70 decode)
      (uMuxOut hk rSub s4.uIdSlice (huId_wstate s4) γ)).1 * projBits_c70 rC γ) *
      (uHadCoinExt hk).1) * Le *
      P_ext := by unfold uPreExt uIdMuxWState uMuxExtOut; rw [Submonoid.coe_mul, Submonoid.coe_mul,
                    preConjClean_mux_eq_c70 decode hk _ (uMuxOut_comm_projBits_rCoinExt hk rSub
                    (huId_wstate s4)), Matrix.mul_sum, Finset.sum_mul, Matrix.mul_sum,
                    Finset.sum_mul, Finset.sum_mul]
  rw [← hAvgOp, hExpand, rS.embedMatrix_smul, rS.embedMatrix_sum, Matrix.smul_mul, Matrix.smul_mul,
      Finset.sum_mul, Finset.sum_mul, Finset.smul_sum]
  refine Finset.sum_congr rfl fun γ _ ↦ ?_
  let Mc :=
      (preConj (uStage1Clean_c70 decode)
      (uMuxOut hk rSub s4.uIdSlice (huId_wstate s4) γ)).1; have cMcR : ∀ M,
      Commute Mc (rC.embedMatrix M) :=
      preConjClean_comm_rCoinExt_c70 decode hk _ (uMuxOut_comm_rCoinExt hk rSub (huId_wstate s4) γ)
  have cMcHi : (uHadCoinExt hk)⁻¹.1 * Mc = Mc * (uHadCoinExt hk)⁻¹.1 := hHi ▸ (cMcR _).symm.eq
  have cMcPc : Pc * Mc = Mc * Pc := (cMcR (compProj 0)).symm.eq
  have cL8P : projBits_c70 rC γ * L8 = L8 * projBits_c70 rC γ :=
      projBits_eq_embedMatrix_c70 rC γ ▸ (cL8R _).symm.eq
  have cPcExt : Pc * P_ext = P_ext * Pc := (cScrR (compProj 0)).symm.eq
  have cPcL8_eq : Pc * L8 = L8 * Pc := cPcL8.eq
  have swapL {X Y : Operator (2 ^ dLayout)} (Z) (h : X * Y = Y * X) : X * (Y * Z) = Y * (X * Z)
      := by
    rw [← Matrix.mul_assoc, h, Matrix.mul_assoc]
  have hMidFactor : Le * ((uHadCoinExt hk)⁻¹.1 * (Mc * projBits_c70 rC γ) * (uHadCoinExt hk).1) *
      Le =
      (L8 * Mc * L8) * (Pc * (uHadCoinExt hk)⁻¹.1 * projBits_c70 rC γ * (uHadCoinExt hk).1 * Pc)
          := by
    simp only [show Le = L8 * Pc from hSplit.trans cPcL8_eq, Matrix.mul_assoc]
    rw [swapL _ cMcHi, swapL _ cMcPc, swapL _ cL8Hf.symm, swapL _ cL8P, swapL _ cL8Hi.symm,
        swapL _ cPcL8_eq]
  rw [hMidFactor, proj0_uHadCoinExt_projBits_c70 hk γ, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_assoc (L8 * Mc * L8) Pc P_ext, cPcExt, ← Matrix.mul_assoc (L8 * Mc * L8),
    hSlice γ]
  refine congrArg ((2 ^ kExt : ℂ)⁻¹ • ·) ?_
  rw [Matrix.mul_assoc _ P_ext Pc, ← cPcExt, Matrix.mul_assoc (rS.embedMatrix _),
    swapL P_ext cPcL8_eq.symm, ← Matrix.mul_assoc Pc L8 P_ext, ← hSplit, ← Matrix.mul_assoc]
end
section
attribute [local reducible] totDimCompactGen
attribute [local irreducible] systemQubits_frozen ancWOfScr uRouterSwapConj
    PgBase.phaseGradientState reflULGen
/-- Clean-scratch restricted ideal `(kExt + kOut)`-coin `SELECT` unitary on `dLayout`. -/
def sSliceWState {kExt kOut w1 : ℕ} {decode : Fin (2 ^ 41) → ZeroNEremSector}
    {peKOut : BitAssignment (kExt + kOut) → PotExpectFn} (hk : kExt ≤ 72) (rSub : QRegister kOut 41)
    (o1 : Stage1ZeroNEremLayout w1 decode)
    (s4 : Stage4OuterSubUnitaryPkgWs kExt kOut w1 hk rSub decode o1 peKOut) : Unitary (2 ^ dLayout)
    :=
  unitaryOnProj (d := 2 ^ dLayout) (uPreExt hk decode (uIdMuxWState hk rSub o1 s4))
    (pScrExt kExt hk) (pScrExt_herm kExt hk) (pScrExt_idem kExt hk)
    (comm_pScrExt_id_wstate hk rSub o1 s4)

/-- Clean-scratch restricted unguarded cat `(kExt + kOut)`-coin `SELECT` unitary on `dLayout`. -/
def uselSliceWState {kExt kOut w1 : ℕ} {decode : Fin (2 ^ 41) → ZeroNEremSector}
    {peKOut : BitAssignment (kExt + kOut) → PotExpectFn} (hk : kExt ≤ 72) (rSub : QRegister kOut 41)
    (o1 : Stage1ZeroNEremLayout w1 decode)
    (s4 : Stage4OuterSubUnitaryPkgWs kExt kOut w1 hk rSub decode o1 peKOut) : Unitary (2 ^ dLayout)
    :=
  unitaryOnProj (d := 2 ^ dLayout) (uPreExt hk decode (uUselMuxWState hk rSub o1 s4))
    (pScrExt kExt hk) (pScrExt_herm kExt hk) (pScrExt_idem kExt hk)
    (comm_pScrExt_usel_wstate hk rSub o1 s4)

/-- Clean-scratch restricted controlled cat `(kExt + kOut)`-coin `SELECT` unitary on `dLayout`. -/
def cselSliceWState {kExt kOut w1 : ℕ} {decode : Fin (2 ^ 41) → ZeroNEremSector}
    {peKOut : BitAssignment (kExt + kOut) → PotExpectFn} (hk : kExt ≤ 72) (rSub : QRegister kOut 41)
    (o1 : Stage1ZeroNEremLayout w1 decode)
    (s4 : Stage4OuterSubUnitaryPkgWs kExt kOut w1 hk rSub decode o1 peKOut) : Unitary (2 ^ dLayout)
    :=
  unitaryOnProj (d := 2 ^ dLayout) (uPreExt hk decode (uCselMuxWState hk rSub o1 s4))
    (pScrExt kExt hk) (pScrExt_herm kExt hk) (pScrExt_idem kExt hk)
    (comm_pScrExt_csel_wstate hk rSub o1 s4)

theorem comm_wExt_of_off4_wstate (decode : Fin (2 ^ 41) → ZeroNEremSector) {kExt k : ℕ}
    (hk : kExt ≤ 72)
    {r : QRegister k dLayout}
    (hoff4 : OffIndexAndScratchPoly systemQubits_frozen scrWLayout (lcuSubLGen hpLayout)
        (scrSubLGen hpLayout) r)
    (M : Operator (2 ^ k)) : Commute (wFull (uStage1Clean_c70 decode) *
        uHadCoinExt hk).1 (r.embedMatrix M) := by
  rw [Submonoid.coe_mul, (uHadCoinExt_eq_embed_c70 hk).1]
  exact (wFullClean_comm_off_c70 decode hoff4 M).mul_left (rCoinExt_comm_off4 hk hoff4 _ M)

/--
Master `SelectLocalSpecGen` + `cat8SharedProjCompactGen` theorem for `Stage4OuterSubUnitaryPkgWs` .
-/
theorem selectLocalSpecGen_outerSubUnitary_wstate {kExt kOut w1 : ℕ}
    {decode : Fin (2 ^ 41) → ZeroNEremSector} {peKOut : BitAssignment (kExt + kOut) → PotExpectFn}
    (hk : kExt ≤ 72) (rSub : QRegister kOut 41) (o1 : Stage1ZeroNEremLayout w1 decode)
    (s4 : Stage4OuterSubUnitaryPkgWs kExt kOut w1 hk rSub decode o1 peKOut) {A : OpSys}
    (hAvgOp : (2 ^ kExt : ℂ)⁻¹ • ∑ γ : BitAssignment kExt, ((2 ^ 82 : ℂ)⁻¹ • ∑ c : Fin (2 ^ 41),
    bOuterZeroNErem decode (peKOut (concatBitsGen γ (outSubRawBits rSub c))) c) = A) :
    SelectLocalSpecGen (scrSubLGen (hpExt kExt hk))
    (lcuSubLGen (hpExt kExt hk)) A (sSliceWState hk rSub o1 s4) (cselSliceWState hk rSub o1 s4)
    (reflULGen (hpExt kExt hk)) ∧ (uselSliceWState hk rSub o1 s4).1 *
    cat8SharedProjCompactGen scrWLayout = (sSliceWState hk rSub o1 s4).1 *
    cat8SharedProjCompactGen scrWLayout := by
  obtain ⟨hCtrl4, hCat4⟩ := uMuxWState_ctrl_and_cat hk rSub o1 s4;
  have hCommId := comm_pScrExt_id_wstate hk rSub o1 s4;
  have hCommUsel := comm_pScrExt_usel_wstate hk rSub o1 s4;
  have hCommCsel := comm_pScrExt_csel_wstate hk rSub o1 s4; let P := pScrExt kExt hk;
  let Mcat : Operator (2 ^ 8) :=
      Matrix.vecMulVec (PgBase.phaseGradientState 8)
      (star (PgBase.phaseGradientState 8)); let W_ext :=
                                              wFull (uStage1Clean_c70 decode) * uHadCoinExt hk
  have hPreEq (u4 : Unitary (2 ^ dLayout)) : uPreExt hk decode u4 = W_ext⁻¹ * u4 * W_ext := by
    simp only [uPreExt, preConj, W_ext, _root_.mul_inv_rev, mul_assoc]
  have hCtrlPre := by
    simpa only [← hPreEq] using unitary_conj_ctrl (d :=
        2 ^ dLayout) W_ext (uCselMuxWState hk rSub o1 s4)
      (uUselMuxWState hk rSub o1 s4) (projOneQCompactGen scrWLayout)
      (comm_wExt_of_off4_wstate decode hk hoff_wLocQ (compProj 1)).eq hCtrl4
  have hCatPre := by
    simpa only [← hPreEq] using unitary_conj_mul_right (d :=
        2 ^ dLayout) W_ext (uUselMuxWState hk rSub o1 s4)
      (uIdMuxWState hk rSub o1 s4) (cat8SharedProjCompactGen scrWLayout)
      (comm_wExt_of_off4_wstate decode hk hoff_cat8_layout Mcat).eq hCat4
  let uS := sSliceWState hk rSub o1 s4; let uU := uselSliceWState hk rSub o1 s4;
  let uC := cselSliceWState hk rSub o1 s4
  have hCtrlRestr : uC.1 = (1 - projOneQCompactGen scrWLayout) + projOneQCompactGen scrWLayout *
      uU.1 :=
    unitaryOnProj_ctrl_eq (d := 2 ^ dLayout) (uPreExt hk decode (uCselMuxWState hk rSub o1 s4))
        (uPreExt hk decode (uUselMuxWState hk rSub o1 s4))
      P (projOneQCompactGen scrWLayout) (pScrExt_herm kExt hk)
          (pScrExt_idem kExt hk) hCommCsel hCommUsel hCtrlPre
  have hCatRestr : uU.1 * cat8SharedProjCompactGen scrWLayout = uS.1 *
      cat8SharedProjCompactGen scrWLayout :=
    unitaryOnProj_mul_right (d := 2 ^ dLayout) (uPreExt hk decode (uUselMuxWState hk rSub o1 s4))
        (uPreExt hk decode (uIdMuxWState hk rSub o1 s4))
      P (cat8SharedProjCompactGen scrWLayout) (pScrExt_herm kExt hk)
          (pScrExt_idem kExt hk) hCommUsel hCommId
      (pScrExt_comm_off_c70 hk ((hoffExt_iff_layout_c70 hk _).mpr hoff_cat8_layout) Mcat).eq hCatPre
  have hLcuCommScr : lcuProjPoly systemQubits_frozen scrWLayout (lcuSubLGen (hpExt kExt hk)) * P =
      P * lcuProjPoly systemQubits_frozen scrWLayout (lcuSubLGen (hpExt kExt hk))
      := by obtain ⟨hSp, _⟩ :=
              lcuProj_ext_split_c70 hk;
              have c1 : (rCoinExt kExt hk).basisOutcomeProjector 0 * P = P *
              (rCoinExt kExt hk).basisOutcomeProjector 0 :=
              (rCoinExt kExt hk).embedMatrix_comm_of_disjoint (rScrExt kExt hk)
              (rCoinExt_disj_helpers_c70 hk).2.1 (compProj 0)
              (compProj 0);
              have c2 : lcuProjPoly systemQubits_frozen scrWLayout (lcuSubLGen hpLayout) * P = P *
              lcuProjPoly systemQubits_frozen scrWLayout (lcuSubLGen hpLayout) :=
              ((rScrExt kExt hk).embedMatrix_comm_of_disjoint rLcu82Layout
              (rCoinExt_disj_helpers_c70 hk).2.2.2 (compProj 0)
              (compProj 0)).symm; rw [hSp, Matrix.mul_assoc, c2, ← Matrix.mul_assoc, c1,
              Matrix.mul_assoc]
  have hBlockRestr : lcuProjPoly systemQubits_frozen scrWLayout (lcuSubLGen (hpExt kExt hk)) *
      uS.1 *
      lcuProjPoly systemQubits_frozen scrWLayout (lcuSubLGen (hpExt kExt hk)) * P =
      (locSysPoly systemQubits_frozen scrWLayout).embedMatrix A *
        lcuProjPoly systemQubits_frozen scrWLayout (lcuSubLGen (hpExt kExt hk)) * P := by
    let Le := lcuProjPoly systemQubits_frozen scrWLayout (lcuSubLGen (hpExt kExt hk))
    dsimp only [uS, sSliceWState]
    rw [Matrix.mul_assoc _ Le P, hLcuCommScr, Matrix.mul_assoc Le _ (P * Le),
        ← Matrix.mul_assoc _ P Le,
      unitaryOnProj_mul_proj (d := 2 ^ dLayout) (uPreExt hk decode (uIdMuxWState hk rSub o1 s4)) P
        (pScrExt_herm kExt hk) (pScrExt_idem kExt hk) hCommId,
      Matrix.mul_assoc _ P Le, ← hLcuCommScr, ← Matrix.mul_assoc Le, ← Matrix.mul_assoc]
    exact block_pScrExt_wstate hk rSub o1 s4 hAvgOp
  refine ⟨{
    S_herm :=
        unitaryOnProj_herm (d := 2 ^ dLayout) _ P (pScrExt_herm _ hk)
        (pScrExt_idem _ hk) hCommId (invol_pScrExt_wstate hk rSub o1 s4)
    S_comm := fun r M hoff ↦ by
      have cM :=
          uPreExt_comm_off_c70 hk decode (uIdMuxWState hk rSub o1 s4)
          (fun r' hoff' M' ↦ uMuxExtOut_comm_off hk rSub (huId_wstate s4) s4.hIdOff hoff' M') hoff M
      have cP :=
          pScrExt_comm_off_c70 hk hoff M; dsimp only [uS,
          sSliceWState]; change (unitaryOnProj _ P _ _ _).1 * r.embedMatrix M = r.embedMatrix M *
          (unitaryOnProj _ P _ _ _).1; rw [unitaryOnProj_val (d := 2 ^ dLayout), add_mul, mul_add,
          Matrix.mul_assoc, cP.eq, ← Matrix.mul_assoc, cM.eq, Matrix.mul_assoc, sub_mul, mul_sub,
          one_mul, mul_one, cP.eq]
    S_scr :=
        unitaryOnProj_comm_proj (d := 2 ^ dLayout)
        (uPreExt hk decode (uIdMuxWState hk rSub o1 s4)) P (pScrExt_herm kExt hk)
        (pScrExt_idem kExt hk) hCommId
    hblock := hBlockRestr
    cselU_cat := by
      change uC.1 * cat8SharedProjCompactGen _ = (1 - projOneQCompactGen _ * (1 - uS.1)) *
          cat8SharedProjCompactGen _
      rw [hCtrlRestr, add_mul, Matrix.mul_assoc, sub_mul, one_mul, hCatRestr,
        mul_sub, mul_one, sub_mul, one_mul, sub_mul, Matrix.mul_assoc, sub_sub_eq_add_sub,
            sub_add_eq_add_sub]
    reflU_eq := reflULGen_eq (hpExt kExt hk) }, hCatRestr⟩
theorem unitaryOnProj_uPreExt_wstate_comm_locGrad3Hi {kExt kOut : ℕ}
    (decode : Fin (2 ^ 41) → ZeroNEremSector) (hk : kExt ≤ 72) (rSub : QRegister kOut 41)
    (uSlice : BitAssignment (kExt + kOut) → Unitary (2 ^ dLayout))
    (hu : ∀ γω (M : Operator (2 ^ (kExt + kOut))),
      Commute (uSlice γω).1 ((rCoinExtOut hk rSub).embedMatrix M))
    (hCommP : pScrExt kExt hk * (uPreExt hk decode (uMuxExtOut hk rSub uSlice hu)).1 =
      (uPreExt hk decode (uMuxExtOut hk rSub uSlice hu)).1 * pScrExt kExt hk)
    (M : Operator (2 ^ 3))
    (hG : ∀ γω, Commute (uSlice γω).1 ((locGrad3HiCompactGen scrWLayout).embedMatrix M)) :
    Commute
      (unitaryOnProj (d := 2 ^ dLayout) (uPreExt hk decode (uMuxExtOut hk rSub uSlice hu))
        (pScrExt kExt hk) (pScrExt_herm kExt hk) (pScrExt_idem kExt hk) hCommP).1
      ((locGrad3HiCompactGen scrWLayout).embedMatrix M) := by
  let rCO := rCoinExtOut hk rSub; let rG := locGrad3HiLayout; let P := pScrExt kExt hk;
  have dCG := rCoinExtOut_disj_off hk rSub hoff_locGrad3HiLayout_wstate
  have cMux : Commute (uMuxExtOut hk rSub uSlice hu).1 (rG.embedMatrix M) := by
    change (uMuxExtOut hk rSub uSlice hu).1 * rG.embedMatrix M = rG.embedMatrix M *
        (uMuxExtOut hk rSub uSlice hu).1
    simp only [uMuxExtOut_val, muxMat_c70, Finset.sum_mul, Matrix.mul_sum]
    refine Finset.sum_congr rfl fun γω _ ↦ ?_
    rw [projBits_eq_embedMatrix_c70 rCO γω]
    exact ((hG γω).mul_left (rCO.embedMatrix_comm_of_disjoint rG dCG _ M)).eq
  have cW := comm_wExt_of_off4_wstate decode hk hoff_locGrad3HiLayout_wstate M
  have cM : Commute (uPreExt hk decode (uMuxExtOut hk rSub uSlice hu)).1 (rG.embedMatrix M) := by
    rw [show uPreExt hk decode (uMuxExtOut hk rSub uSlice hu) = (wFull (uStage1Clean_c70 decode) *
        uHadCoinExt hk)⁻¹ *
        uMuxExtOut hk rSub uSlice hu * (wFull (uStage1Clean_c70 decode) * uHadCoinExt hk) by
      unfold uPreExt preConj
      group]
    simpa only [Submonoid.coe_mul] using ((show Commute _ _ from unitary_inv_comm _ _ cW).mul_left
        cMux).mul_left cW
  have cP :=
    pScrExt_comm_off_c70 hk ((hoffExt_iff_layout_c70 hk rG).mpr hoff_locGrad3HiLayout_wstate) M
  change (unitaryOnProj _ P _ _ _).1 * rG.embedMatrix M = rG.embedMatrix M *
    (unitaryOnProj _ P _ _ _).1
  rw [unitaryOnProj_val (d := 2 ^ dLayout), add_mul, mul_add,
    Matrix.mul_assoc, cP.eq, ← Matrix.mul_assoc, cM.eq, Matrix.mul_assoc, sub_mul, mul_sub,
    one_mul, mul_one, cP.eq]
/--
Retired top-3 phase-gradient (`{5647, 5648, 5649}`) commutation for `uselSliceWState` and
`cselSliceWState`.
-/
theorem comm_locGrad3Hi_outerSubUnitary_wstate {kExt kOut w1 : ℕ}
    {decode : Fin (2 ^ 41) → ZeroNEremSector} {peKOut : BitAssignment (kExt + kOut) → PotExpectFn}
    (hk : kExt ≤ 72) (rSub : QRegister kOut 41) (o1 : Stage1ZeroNEremLayout w1 decode)
    (s4 : Stage4OuterSubUnitaryPkgWs kExt kOut w1 hk rSub decode o1 peKOut) (M : Operator (2 ^ 3)) :
    Commute (uselSliceWState hk rSub o1 s4).1 ((locGrad3HiCompactGen scrWLayout).embedMatrix M) ∧
    Commute (cselSliceWState hk rSub o1 s4).1 ((locGrad3HiCompactGen scrWLayout).embedMatrix M) :=
    ⟨unitaryOnProj_uPreExt_wstate_comm_locGrad3Hi decode hk rSub s4.uUselSlice (huUsel_wstate s4)
    (comm_pScrExt_usel_wstate hk rSub o1 s4) M (fun γω ↦ (s4.comm_grad3Hi γω M).1),
    unitaryOnProj_uPreExt_wstate_comm_locGrad3Hi decode hk rSub s4.uCselSlice (huCsel_wstate s4)
    (comm_pScrExt_csel_wstate hk rSub o1 s4) M (fun γω ↦ (s4.comm_grad3Hi γω M).2)⟩
theorem comm_coinExtOut_refl2m1_98_wstate {kExt kOut : ℕ} {peKOut : BitAssignment (kExt + kOut) →
    PotExpectFn} (hk : kExt ≤ 72) (rSub : QRegister kOut 41)
    (specKOut : ∀ γω : BitAssignment (kExt + kOut), ReflPotSliceSpec (peKOut γω))
    (γω : BitAssignment (kExt + kOut)) (M : Operator (2 ^ (kExt + kOut))) :
    Commute (uStage4ReflZeroNErem2m1Ideal (specKOut γω)).1 ((rCoinExtOut hk rSub).embedMatrix M) ∧
    Commute (uStage4ReflZeroNErem2m1_98CatUsel (specKOut γω)).1 ((rCoinExtOut hk rSub).embedMatrix
    M) ∧
    Commute (uStage4ReflZeroNErem2m1_98CatCsel (specKOut γω)).1 ((rCoinExtOut hk rSub).embedMatrix
    M) :=
    uStage4ReflZeroNErem2m1_98_comm_coinBand7256 (rCoinExtOut hk rSub)
    (val_rCoinExtOut_coinBand7256_wstate hk rSub) (specKOut γω) M
theorem hCtrlSlice_refl2m1_98_wstate {kExt kOut : ℕ} {peKOut : BitAssignment (kExt + kOut) →
    PotExpectFn} (specKOut : ∀ γω : BitAssignment (kExt + kOut), ReflPotSliceSpec (peKOut γω))
    (γω : BitAssignment (kExt + kOut)) : (uStage4ReflZeroNErem2m1_98CatCsel (specKOut γω)).1 =
    (1 - projOneQCompactGen scrWLayout) + projOneQCompactGen scrWLayout *
    (uStage4ReflZeroNErem2m1_98CatUsel (specKOut γω)).1 :=
    (uStage4ReflZeroNErem2m1_98Layout_props (specKOut γω)).1
theorem hCatSlice_refl2m1_98_wstate {kExt kOut : ℕ} {peKOut : BitAssignment (kExt + kOut) →
    PotExpectFn} (specKOut : ∀ γω : BitAssignment (kExt + kOut), ReflPotSliceSpec (peKOut γω))
    (γω : BitAssignment (kExt + kOut)) : (uStage4ReflZeroNErem2m1_98CatUsel (specKOut γω)).1 *
    cat8SharedProjCompactGen scrWLayout = (uStage4ReflZeroNErem2m1Ideal (specKOut γω)).1 *
    cat8SharedProjCompactGen scrWLayout :=
    (uStage4ReflZeroNErem2m1_98Layout_props (specKOut γω)).2.1
theorem hIdOff_refl2m1_98_wstate {kExt kOut : ℕ} {peKOut : BitAssignment (kExt + kOut) →
    PotExpectFn} (specKOut : ∀ γω : BitAssignment (kExt + kOut), ReflPotSliceSpec (peKOut γω))
    (γω : BitAssignment (kExt + kOut)) {k : ℕ} (r : QRegister k dLayout)
    (hoff : OffIndexAndScratchPoly systemQubits_frozen scrWLayout (lcuSubLGen hpLayout)
    (scrSubLGen hpLayout) r) (M : Operator (2 ^ k)) :
    Commute (uStage4ReflZeroNErem2m1Ideal (specKOut γω)).1 (r.embedMatrix M) :=
    (uStage4ReflZeroNErem2m1_98Layout_props (specKOut γω)).2.2 r hoff M
theorem comm_scr_refl2m1_98_wstate {kExt kOut w1 : ℕ} {decode : Fin (2 ^ 41) → ZeroNEremSector}
    {peKOut : BitAssignment (kExt + kOut) → PotExpectFn} (o1 : Stage1ZeroNEremLayout w1 decode)
    (specKOut : ∀ γω : BitAssignment (kExt + kOut), ReflPotSliceSpec (peKOut γω))
    (γω : BitAssignment (kExt + kOut)) :
    CommScr (preLoc o1.uLocal (uStage4ReflZeroNErem2m1Ideal (specKOut γω))) ∧
    CommScr (preLoc o1.uLocal (uStage4ReflZeroNErem2m1_98CatUsel (specKOut γω))) ∧
    CommScr (preLoc o1.uLocal (uStage4ReflZeroNErem2m1_98CatCsel (specKOut γω))) :=
    ⟨comm_pScr_refl2m1_IdPre o1 (specKOut γω), comm_pScr_refl2m1_98UselPre o1 (specKOut γω),
    comm_pScr_refl2m1_98CselPre o1 (specKOut γω)⟩
theorem hInvolPreScr_refl2m1_98_wstate {kExt kOut w1 : ℕ} {decode : Fin (2 ^ 41) → ZeroNEremSector}
    {peKOut : BitAssignment (kExt + kOut) → PotExpectFn} (o1 : Stage1ZeroNEremLayout w1 decode)
    (specKOut : ∀ γω : BitAssignment (kExt + kOut), ReflPotSliceSpec (peKOut γω))
    (γω : BitAssignment (kExt + kOut)) :
    preLoc o1.uLocal (uStage4ReflZeroNErem2m1Ideal (specKOut γω)) *
    (preLoc o1.uLocal (uStage4ReflZeroNErem2m1Ideal (specKOut γω)) * pScr) = pScr :=
    rawIdealSelectReflZeroNErem_2m1_invol o1 (specKOut γω)
theorem comm_grad3Hi_refl2m1_98_wstate {kExt kOut : ℕ} {peKOut : BitAssignment (kExt + kOut) →
    PotExpectFn} (specKOut : ∀ γω : BitAssignment (kExt + kOut), ReflPotSliceSpec (peKOut γω))
    (γω : BitAssignment (kExt + kOut)) (M : Operator (2 ^ 3)) :
    Commute (uStage4ReflZeroNErem2m1_98CatUsel (specKOut γω)).1 ((locGrad3HiCompactGen
    scrWLayout).embedMatrix M) ∧
    Commute (uStage4ReflZeroNErem2m1_98CatCsel (specKOut γω)).1 ((locGrad3HiCompactGen
    scrWLayout).embedMatrix M) :=
    ⟨(uStage4ReflZeroNErem2m1_98_comm_locGrad3Hi (specKOut γω) M).2.1,
    (uStage4ReflZeroNErem2m1_98_comm_locGrad3Hi (specKOut γω) M).2.2⟩
theorem sum_z41_slice_refl2m1_98_wstate {kExt kOut w1 : ℕ} {wEE : Fin 4 → ℕ}
    {wNN : Fin 4 → Fin 4 → ℕ} {wEN : Fin 4 → ℕ} {wKin : Particle_frozen → ℕ} {wIdle : ℕ}
    {decode : Fin (2 ^ 41) → ZeroNEremSector} {peKOut : BitAssignment (kExt + kOut) → PotExpectFn}
    (o1 : Stage1ZeroNEremLayout w1 decode) (specKOut : ∀ γω : BitAssignment (kExt + kOut),
    ReflPotSliceSpec (peKOut γω)) (hCoin : ValidGenZeroNEremCoin wEE wNN wEN wKin wIdle decode)
    (γω : BitAssignment (kExt + kOut)) {β : BitAssignment dLayout}
    (hr0 : ∀ u, β (rLcu82Layout u) = 0) (hScr : CleanScr β) (c : Fin (2 ^ 41)) :
    (∑ z : BitAssignment 41, (rLcu82Layout.basisOutcomeProjector 0 *
    (uHad82Layout⁻¹).1).mulVec ((((wNoHad o1.uLocal)⁻¹ *
    uStage4ReflZeroNErem2m1Ideal (specKOut γω) *
    wNoHad o1.uLocal).1).mulVec (ket (routedStage0 β c z)))) =
    (sqrtHalf ^ 82) • (rSysLayout.embedMatrix (bOuterZeroNErem decode (peKOut γω) c)).mulVec (ket β)
    :=
  sum_z41_sector_gen_refl_2m1 o1 (specKOut γω) hCoin hr0 hScr c

/--
Pure-unitary `(kExt + kOut)`-coin reflected `(2m+1)` `98-T` Stage-4 slice package built from
any `ReflPotSliceSpec` family `specKOut` and `ValidGenZeroNEremCoin`.
-/
def stage4OuterSubUnitaryPkg_refl2m1_98_wstate {kExt kOut w1 : ℕ}
    {wEE : Fin 4 → ℕ} {wNN : Fin 4 → Fin 4 → ℕ} {wEN : Fin 4 → ℕ}
    {wKin : Particle_frozen → ℕ} {wIdle : ℕ}
    {decode : Fin (2 ^ 41) → ZeroNEremSector}
    {peKOut : BitAssignment (kExt + kOut) → PotExpectFn}
    (hk : kExt ≤ 72) (rSub : QRegister kOut 41) (o1 : Stage1ZeroNEremLayout w1 decode)
    (specKOut : ∀ γω : BitAssignment (kExt + kOut), ReflPotSliceSpec (peKOut γω))
    (hCoin : ValidGenZeroNEremCoin wEE wNN wEN wKin wIdle decode) :
    Stage4OuterSubUnitaryPkgWs kExt kOut w1 hk rSub decode o1 peKOut where
  uIdSlice γω := uStage4ReflZeroNErem2m1Ideal (specKOut γω)
  uUselSlice γω := uStage4ReflZeroNErem2m1_98CatUsel (specKOut γω)
  uCselSlice γω := uStage4ReflZeroNErem2m1_98CatCsel (specKOut γω)
  comm_coinExtOut := comm_coinExtOut_refl2m1_98_wstate hk rSub specKOut
  hCtrlSlice := hCtrlSlice_refl2m1_98_wstate specKOut
  hCatSlice := hCatSlice_refl2m1_98_wstate specKOut
  hIdOff := hIdOff_refl2m1_98_wstate specKOut
  comm_scr := comm_scr_refl2m1_98_wstate o1 specKOut
  hInvolPreScr := hInvolPreScr_refl2m1_98_wstate o1 specKOut
  comm_grad3Hi := comm_grad3Hi_refl2m1_98_wstate specKOut
  sum_z41_slice := sum_z41_slice_refl2m1_98_wstate o1 specKOut hCoin

/-- Clean-scratch restricted ideal `(kExt + kOut)`-coin `(2m+1)` reflected `SELECT` unitary. -/
def sReflSliceOuterSub2m1_wstate {kExt kOut w1 : ℕ} {wEE : Fin 4 → ℕ} {wNN : Fin 4 → Fin 4 → ℕ}
    {wEN : Fin 4 → ℕ} {wKin : Particle_frozen → ℕ} {wIdle : ℕ}
    {decode : Fin (2 ^ 41) → ZeroNEremSector} {peKOut : BitAssignment (kExt + kOut) → PotExpectFn}
    (hk : kExt ≤ 72) (rSub : QRegister kOut 41) (o1 : Stage1ZeroNEremLayout w1 decode)
    (specKOut : ∀ γω : BitAssignment (kExt + kOut), ReflPotSliceSpec (peKOut γω))
    (hCoin : ValidGenZeroNEremCoin wEE wNN wEN wKin wIdle decode) : Unitary (2 ^ dLayout) :=
  sSliceWState hk rSub o1 (stage4OuterSubUnitaryPkg_refl2m1_98_wstate hk rSub o1 specKOut hCoin)

/--
Clean-scratch restricted unguarded cat `98-T` `(kExt + kOut)` -coin reflected `SELECT` unitary.
-/
def uselReflSliceOuterSub2m1_98_wstate {kExt kOut w1 : ℕ} {wEE : Fin 4 → ℕ}
    {wNN : Fin 4 → Fin 4 → ℕ} {wEN : Fin 4 → ℕ} {wKin : Particle_frozen → ℕ} {wIdle : ℕ}
    {decode : Fin (2 ^ 41) → ZeroNEremSector} {peKOut : BitAssignment (kExt + kOut) → PotExpectFn}
    (hk : kExt ≤ 72) (rSub : QRegister kOut 41) (o1 : Stage1ZeroNEremLayout w1 decode)
    (specKOut : ∀ γω : BitAssignment (kExt + kOut), ReflPotSliceSpec (peKOut γω))
    (hCoin : ValidGenZeroNEremCoin wEE wNN wEN wKin wIdle decode) : Unitary (2 ^ dLayout) :=
  uselSliceWState hk rSub o1 (stage4OuterSubUnitaryPkg_refl2m1_98_wstate hk rSub o1 specKOut hCoin)

/--
Clean-scratch restricted controlled cat `98-T` `(kExt + kOut)` -coin reflected `SELECT` unitary.
-/
def cselReflSliceOuterSub2m1_98_wstate {kExt kOut w1 : ℕ} {wEE : Fin 4 → ℕ}
    {wNN : Fin 4 → Fin 4 → ℕ} {wEN : Fin 4 → ℕ} {wKin : Particle_frozen → ℕ} {wIdle : ℕ}
    {decode : Fin (2 ^ 41) → ZeroNEremSector} {peKOut : BitAssignment (kExt + kOut) → PotExpectFn}
    (hk : kExt ≤ 72) (rSub : QRegister kOut 41) (o1 : Stage1ZeroNEremLayout w1 decode)
    (specKOut : ∀ γω : BitAssignment (kExt + kOut), ReflPotSliceSpec (peKOut γω))
    (hCoin : ValidGenZeroNEremCoin wEE wNN wEN wKin wIdle decode) : Unitary (2 ^ dLayout) :=
  cselSliceWState hk rSub o1 (stage4OuterSubUnitaryPkg_refl2m1_98_wstate hk rSub o1 specKOut hCoin)

/--
Master `(kExt + kOut)`-coin `SelectLocalSpecGen` + `cat8SharedProjCompactGen` theorem for
reflected `(2m+1)` `98-T` Stage-4 slice families (`ReflPotSliceSpec`).
-/
theorem selectLocalSpecGen_reflOuterSub2m1_98_wstate {kExt kOut w1 : ℕ} {wEE : Fin 4 → ℕ}
    {wNN : Fin 4 → Fin 4 → ℕ} {wEN : Fin 4 → ℕ} {wKin : Particle_frozen → ℕ} {wIdle : ℕ}
    {decode : Fin (2 ^ 41) → ZeroNEremSector} {peKOut : BitAssignment (kExt + kOut) → PotExpectFn}
    (hk : kExt ≤ 72) (rSub : QRegister kOut 41) (o1 : Stage1ZeroNEremLayout w1 decode)
    (specKOut : ∀ γω : BitAssignment (kExt + kOut), ReflPotSliceSpec (peKOut γω))
    (hCoin : ValidGenZeroNEremCoin wEE wNN wEN wKin wIdle decode) {A : OpSys}
    (hAvgOp : (2 ^ kExt : ℂ)⁻¹ • ∑ γ : BitAssignment kExt, ((2 ^ 82 : ℂ)⁻¹ • ∑ c : Fin (2 ^ 41),
    bOuterZeroNErem decode (peKOut (concatBitsGen γ (outSubRawBits rSub c))) c) = A) :
    SelectLocalSpecGen (scrSubLGen (hpExt kExt hk))
    (lcuSubLGen (hpExt kExt hk)) A (sReflSliceOuterSub2m1_wstate hk rSub o1 specKOut hCoin)
    (cselReflSliceOuterSub2m1_98_wstate hk rSub o1 specKOut hCoin) (reflULGen (hpExt kExt hk)) ∧
    (uselReflSliceOuterSub2m1_98_wstate hk rSub o1 specKOut hCoin).1 *
    cat8SharedProjCompactGen scrWLayout =
    (sReflSliceOuterSub2m1_wstate hk rSub o1 specKOut hCoin).1 *
    cat8SharedProjCompactGen scrWLayout :=
    selectLocalSpecGen_outerSubUnitary_wstate hk rSub o1 (stage4OuterSubUnitaryPkg_refl2m1_98_wstate
    hk rSub o1 specKOut hCoin) hAvgOp
end
section
attribute [local reducible] totDimCompactGen
attribute [local irreducible] systemQubits_frozen ancWOfScr uRouterSwapConj
    PgBase.phaseGradientState
theorem hk0_le72_wstate : 0 ≤ 72 := Nat.zero_le 72

theorem val_wHasN1_wstate : wHasN1.val = 5715 := by
  dsimp only [wHasN1]; rw [val_rOut40Layout]; dsimp only
theorem hadamardRegCirc_eval_congr_wstate {d : ℕ} :
    ∀ {m₁ m₂ : ℕ} (_hm : m₁ = m₂) (r₁ : QRegister m₁ d) (r₂ : QRegister m₂ d),
      (∀ (i : ℕ) (h₁ : i < m₁) (h₂ : i < m₂), r₁ ⟨i, h₁⟩ = r₂ ⟨i, h₂⟩) →
      (hadamardRegCirc m₁ r₁).eval = (hadamardRegCirc m₂ r₂).eval
  | 0, 0, _, _, _, _ => rfl
  | 0, _ + 1, hm, _, _, _ => by omega
  | _ + 1, 0, hm, _, _, _ => by omega
  | m₁ + 1, m₂ + 1, hm, r₁, r₂, heq => by
      have h0 : r₁ 0 = r₂ 0 := heq 0 (Nat.zero_lt_succ _) (Nat.zero_lt_succ _)
      change (hadamardRegCirc m₁ (tailReg r₁)).eval * (Circuit.H (r₁ 0)).eval =
          (hadamardRegCirc m₂ (tailReg r₂)).eval * (Circuit.H (r₂ 0)).eval
      rw [h0, hadamardRegCirc_eval_congr_wstate (Nat.succ.inj hm) (tailReg r₁)
          (tailReg r₂) fun i h₁ h₂ ↦ heq (i + 1) (Nat.succ_lt_succ h₁) (Nat.succ_lt_succ h₂)]
theorem eval_hadamardRegCirc_split_wstate {d : ℕ} :
    ∀ (a b m : ℕ) (_hm : m = a + b) (rA : QRegister a d) (rB : QRegister b d) (rAB : QRegister m d),
      (∀ (i : ℕ) (hi : i < a) (hm' : i < m), rAB ⟨i, hm'⟩ = rA ⟨i, hi⟩) →
      (∀ (j : ℕ) (hj : j < b) (hm' : a + j < m), rAB ⟨a + j, hm'⟩ = rB ⟨j, hj⟩) →
      (hadamardRegCirc m rAB).eval = (hadamardRegCirc b rB).eval * (hadamardRegCirc a rA).eval
  | 0, b, m, hm, _, rB, rAB, _, hB =>
      (hadamardRegCirc_eval_congr_wstate (by omega) rAB rB fun j _ hj₂ ↦
          by simpa only [Nat.zero_add] using hB j hj₂ (by omega)).trans (mul_one _).symm
  | a + 1, _, 0, hm, _, _, _, _, _ => by omega
  | a + 1, b, m + 1, hm, rA, rB, rAB, hA, hB => by
      have h0 : rAB 0 = rA 0 := hA 0 (Nat.zero_lt_succ a) (Nat.zero_lt_succ m)
      change (hadamardRegCirc m (tailReg rAB)).eval * (Circuit.H (rAB 0)).eval =
        (hadamardRegCirc b rB).eval * ((hadamardRegCirc a (tailReg rA)).eval *
            (Circuit.H (rA 0)).eval)
      rw [eval_hadamardRegCirc_split_wstate a b m (by omega) (tailReg rA) rB (tailReg rAB)
        (fun i hi hm' ↦ hA (i + 1) (Nat.succ_lt_succ hi) (Nat.succ_lt_succ hm'))
        (fun j hj hm' ↦ (congrArg rAB.wires (Fin.ext (by
          dsimp only
          omega) : (⟨(a + j) + 1, Nat.succ_lt_succ hm'⟩ : Fin (m + 1)) =
              ⟨a + 1 + j, by omega⟩)).trans (hB j hj (by omega))),
        h0, mul_assoc]
theorem uHadCoinExt_zero_eq_one_wstate : uHadCoinExt hk0_le72_wstate = 1 := by
  rw [← eval_cHadCoinExtFwd_c70 hk0_le72_wstate]; exact Circuit.eval_identity
/-- Outer `41`-wire coin subregister `dLayout[7215..7255]`. -/
def rOuter41Layout_wstate : QRegister 41 dLayout :=
  rLcu82Layout.compose (QRegister.block 0 41 (by dsimp [mLayout]; omega))

theorem val_rOuter41Layout_wstate (k : Fin 41) : (rOuter41Layout_wstate k).val = 7215 + k.val := by
  have hk := k.isLt; change (rLcu82Layout ⟨0 + k.val, _⟩).val = 7215 + k.val
  rw [val_rLcu82Layout]; dsimp only; omega

theorem hDisjOut40Outer41_wstate : rOut40Layout.DisjointWires rOuter41Layout_wstate :=
  disj_of_ne fun i j e ↦ by
    have hi := i.isLt; have hj := j.isLt
    have hv := congrArg Fin.val e; rw [val_rOut40Layout, val_rOuter41Layout_wstate] at hv; omega

/--
Clean `81` -wire Stage-1 outer-coin + output register (`rOut40Layout ++ rOuter41Layout_wstate`).
-/
def rStage1Clean81_wstate : QRegister (40 + 41) dLayout :=
  rOut40Layout.concat rOuter41Layout_wstate hDisjOut40Outer41_wstate

/-- `81`-bit involutive Stage-1 mask toggle depending only on `rOuter41Layout_wstate`. -/
def stage1Clean81Bits_wstate (decodeCoin : Fin (2 ^ 41) → ZeroNEremSector)
    (ξ : BitAssignment (40 + 41)) : BitAssignment (40 + 41) := fun idx ↦
    if idx.val < 40 then ξ idx +
    (if (zeroNEremOutMask (decodeCoin ⟨∑ k : Fin 41,
    if (ξ (Fin.natAdd 40 k) == 1) then 2 ^ k.val else 0,
    PotSelectWiring.sum_fin_pow2_lt 41 (fun k ↦
    ξ (Fin.natAdd 40 k) == 1)⟩)).testBit idx.val then 1 else 0) else ξ idx
theorem stage1Clean81Bits_invol_wstate (decodeCoin : Fin (2 ^ 41) → ZeroNEremSector) :
    Function.Involutive (stage1Clean81Bits_wstate decodeCoin) := fun ξ ↦ by
  let ξ' := stage1Clean81Bits_wstate decodeCoin ξ
  have hCoin : (⟨∑ k : Fin 41, if (ξ' (Fin.natAdd 40 k) == 1) then 2 ^ k.val else 0,
      PotSelectWiring.sum_fin_pow2_lt 41 (fun k ↦ ξ' (Fin.natAdd 40 k) == 1)⟩ : Fin (2 ^ 41)) =
      ⟨∑ k : Fin 41, if (ξ (Fin.natAdd 40 k) == 1) then 2 ^ k.val else 0,
      PotSelectWiring.sum_fin_pow2_lt 41 (fun k ↦ ξ (Fin.natAdd 40 k) == 1)⟩ := by
    apply Fin.ext
    dsimp only
    exact Finset.sum_congr rfl fun k _ ↦ by
      rw [show ξ' (Fin.natAdd 40 k) =
          ξ (Fin.natAdd 40 k) from ite_eq_right (Nat.not_lt.mpr (Nat.le_add_right 40 k.val))]
  refine funext fun idx ↦ ?_
  change stage1Clean81Bits_wstate decodeCoin ξ' idx = ξ idx
  unfold stage1Clean81Bits_wstate
  if h40 : idx.val < 40 then
    have hξ' : ξ' idx = ξ idx + (if (zeroNEremOutMask (decodeCoin ⟨∑ k : Fin 41,
        if (ξ (Fin.natAdd 40 k) == 1) then 2 ^ k.val else 0,
        PotSelectWiring.sum_fin_pow2_lt 41 (fun k ↦ ξ (Fin.natAdd 40 k) == 1)⟩)).testBit idx.val
      then 1 else 0) := ite_eq_left h40
    rw [ite_eq_left h40, hCoin, hξ']
    exact CharTwo.add_cancel_right _ _
  else exact (ite_eq_right h40).trans (ite_eq_right h40)
theorem uStage1Clean_eq_embed81_wstate (decodeCoin : Fin (2 ^ 41) → ZeroNEremSector) :
    uStage1Clean_c70 decodeCoin =
    rStage1Clean81_wstate.embedUnitary (involUnitary_c70 (stage1Clean81Bits_wstate decodeCoin)
    (stage1Clean81Bits_invol_wstate decodeCoin)) := by
  refine Subtype.ext (matrix_ext_ket fun β ↦ ?_)
  unfold uStage1Clean_c70;
  rw [QRegister.embedUnitary_val, QRegister.embedUnitary_val,
      embedMatrix_ket_eq_writeReg rStage1Clean122_c70 _ β (involUnitary_mulVec_ket_c70 _ _ _),
      embedMatrix_ket_eq_writeReg rStage1Clean81_wstate _ β (involUnitary_mulVec_ket_c70 _ _ _)]
  have hCoinEq : outerCoinOf82 (fun i : Fin (mLayout + 2) ↦
      β (rStage1Clean122_c70 (Fin.natAdd 40 i))) =
      ⟨∑ k : Fin 41, if (β (rStage1Clean81_wstate (Fin.natAdd 40 k)) == 1) then 2 ^ k.val else 0,
      PotSelectWiring.sum_fin_pow2_lt 41 (fun k ↦
      β (rStage1Clean81_wstate (Fin.natAdd 40 k)) == 1)⟩ := by
    apply Fin.ext; dsimp only [outerCoinOf82]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    have h1 : rStage1Clean122_c70 (Fin.natAdd 40 ⟨k.val, fin41_lt_mLayout k⟩) =
        rLcu82Layout ⟨k.val, fin41_lt_mLayout k⟩ :=
        QRegister.concat_apply_right rOut40Layout rLcu82Layout hDisjOut40Lcu82_c70 _;
        have h2 : rStage1Clean81_wstate (Fin.natAdd 40 k) = rOuter41Layout_wstate k :=
        QRegister.concat_apply_right rOut40Layout rOuter41Layout_wstate hDisjOut40Outer41_wstate k
    have h3 : rLcu82Layout ⟨k.val, fin41_lt_mLayout k⟩ = rOuter41Layout_wstate k :=
        Fin.ext (by rw [val_rLcu82Layout, val_rOuter41Layout_wstate])
    change (if (β (rStage1Clean122_c70 (Fin.natAdd 40 ⟨k.val,
        fin41_lt_mLayout k⟩)) == 1) then 2 ^ k.val else 0) = _
    rw [h1, h2, h3]
  refine congrArg ket (funext fun w ↦ ?_)
  by_cases hwOut : ∃ j : Fin 40, rOut40Layout j = w
  · obtain ⟨j, rfl⟩ := hwOut;
    have hj122 : rOut40Layout j = rStage1Clean122_c70 (Fin.castAdd (mLayout + 2) j) :=
        (QRegister.concat_apply_left rOut40Layout rLcu82Layout hDisjOut40Lcu82_c70 j).symm;
        have hj81 : rOut40Layout j = rStage1Clean81_wstate (Fin.castAdd 41 j) :=
        (QRegister.concat_apply_left rOut40Layout rOuter41Layout_wstate hDisjOut40Outer41_wstate
        j).symm; have hlt122 : (Fin.castAdd (mLayout + 2) j).val < 40 :=
                   j.isLt; have hlt81 : (Fin.castAdd 41 j).val < 40 := j.isLt
    conv_lhs => rw [hj122, writeReg_apply_reg]
    conv_rhs => rw [hj81, writeReg_apply_reg]
    unfold stage1Clean122Bits_c70 stage1Clean81Bits_wstate;
    rw [ite_eq_left hlt122, ite_eq_left hlt81]; dsimp only [Fin.val_castAdd];
    rw [hCoinEq, ← hj122, ← hj81]
  · refine Eq.trans (b := β w) ?_ (Eq.symm ?_)
    · if hm122 : ∃ i : Fin (40 + (mLayout + 2)), rStage1Clean122_c70 i = w then
        obtain ⟨i, rfl⟩ := hm122
        simpa only [writeReg_apply_reg, stage1Clean122Bits_c70] using ite_eq_right fun h40 ↦
          hwOut ⟨⟨i.val, h40⟩,
              (QRegister.concat_apply_left rOut40Layout rLcu82Layout hDisjOut40Lcu82_c70 _).symm⟩
      else exact writeReg_apply_of_not_mem _ _ _ w hm122
    · if hm81 : ∃ i : Fin (40 + 41), rStage1Clean81_wstate i = w then
        obtain ⟨i, rfl⟩ := hm81
        simpa only [writeReg_apply_reg, stage1Clean81Bits_wstate] using ite_eq_right fun h40 ↦
          hwOut ⟨⟨i.val, h40⟩,
              (QRegister.concat_apply_left rOut40Layout rOuter41Layout_wstate
              hDisjOut40Outer41_wstate _).symm⟩
      else exact writeReg_apply_of_not_mem _ _ _ w hm81
end
section
attribute [local reducible] totDimCompactGen
attribute [local irreducible] systemQubits_frozen ancWOfScr uRouterSwapConj
    PgBase.phaseGradientState reflULGen
/--
Any operator `U` that commutes with every single-wire embedding on `r : QRegister k n`
commutes with `r.embedMatrix M` for all `M : Operator (2 ^ k)`.
-/
theorem commute_embedMatrix_of_singleton_wstate {k n : ℕ} [NeZero (2 ^ n)]
    (U : Operator (2 ^ n)) (r : QRegister k n)
    (h1 : ∀ (j : Fin k) (N : Operator 2), Commute U ((QRegister.singleton (r j)).embedMatrix N))
    (M : Operator (2 ^ k)) : Commute U (r.embedMatrix M) := by
  induction k with
  | zero =>
      rw [show M = M 0 0 • (1 : Operator 1) from Matrix.ext fun (i : Fin 1)
          (j : Fin 1) ↦ by simp [Fin.eq_zero i, Fin.eq_zero j],
        r.embedMatrix_smul, r.embedMatrix_one]
      exact (Commute.one_right U).smul_right (M 0 0)
  | succ k ih =>
      let eUnit {d : ℕ} (a b : Fin d) : Operator d := fun p q ↦ if p = a ∧ q = b then 1 else 0
      rw [show M = ∑ a, ∑ b, M a b • eUnit a b from Matrix.ext fun p q ↦ by
          simp_rw [Matrix.sum_apply, Matrix.smul_apply]
          simp [eUnit, ite_and], r.embedMatrix_sum]
      refine Commute.sum_right Finset.univ _ U fun a _ ↦ ?_
      rw [r.embedMatrix_sum]
      refine Commute.sum_right Finset.univ _ U fun b _ ↦ ?_
      rw [r.embedMatrix_smul]
      refine (?_ : Commute U (r.embedMatrix (eUnit a b))).smul_right (M a b)
      let s0 : QRegister 1 (k + 1) := QRegister.singleton 0
      let sT : QRegister k (k + 1) := ⟨⟨Fin.succ, Fin.succ_injective _⟩⟩
      have hSplitEq (x y : Fin (2 ^ (k + 1))) : (s0.extractIndex x = s0.extractIndex y ∧
          sT.extractIndex x = sT.extractIndex y) ↔ x = y :=
        ⟨fun ⟨e0, eT⟩ ↦ (_root_.basisBits (k + 1)).injective (funext (Fin.cases
          ((s0.basisBits_extractIndex x 0).symm.trans ((congrFun (congrArg (_root_.basisBits 1) e0)
              0).trans (s0.basisBits_extractIndex y 0)))
          fun j ↦
              (sT.basisBits_extractIndex x j).symm.trans ((congrFun (congrArg (_root_.basisBits k)
              eT) j).trans (sT.basisBits_extractIndex y j)))),
         fun h ↦ h ▸ ⟨rfl, rfl⟩⟩
      have hSingle : eUnit a b = s0.embedMatrix (eUnit (s0.extractIndex a) (s0.extractIndex b)) *
          sT.embedMatrix (eUnit (sT.extractIndex a) (sT.extractIndex b)) := by
        classical
        ext p q
        rw [Matrix.mul_apply]
        let m₀ : Fin (2 ^ (k + 1)) := s0.replaceIndex p (s0.extractIndex q)
        have hm0_0 : _root_.basisBits (k + 1) m₀ 0 = _root_.basisBits (k + 1) q 0 :=
          (s0.basisBits_replaceIndex_apply p (s0.extractIndex q) 0).trans (s0.basisBits_extractIndex
              q 0)
        have hm0_s (j : Fin k) : _root_.basisBits (k + 1) m₀ j.succ = _root_.basisBits (k +
            1) p j.succ :=
          s0.basisBits_replaceIndex_of_not_mem p (s0.extractIndex q) j.succ
              (by simp [s0, Fin.succ_ne_zero])
        rw [Finset.sum_eq_single m₀]
        · have ha0 : s0.AgreeOutside p m₀ :=
              (QRegister.singleton_agreeOutside 0 p m₀).mpr (Fin.cases (fun hw ↦
              (hw rfl).elim) fun j _ ↦ (hm0_s j).symm)
          have haT : sT.AgreeOutside m₀ q := Fin.cases (fun _ ↦ hm0_0) fun j hw ↦ (hw ⟨j, rfl⟩).elim
          have heT : sT.extractIndex m₀ = sT.extractIndex p :=
              (_root_.basisBits k).injective (funext fun j ↦ by simp [sT, hm0_s j])
          rw [s0.embedMatrix_apply_of_agreeOutside, sT.embedMatrix_apply_of_agreeOutside,
              ite_eq_left ha0, ite_eq_left haT, s0.extractIndex_replaceIndex, heT]
          if hpq : p = a ∧ q = b then simp [eUnit, hpq.1, hpq.2, ite_and]
          else if hc0 : s0.extractIndex p = s0.extractIndex a ∧ s0.extractIndex q =
              s0.extractIndex b then
            simpa [eUnit, hpq, hc0] using fun h1 h2 ↦
                hpq ⟨(hSplitEq p a).mp ⟨hc0.1, h1⟩, (hSplitEq q b).mp ⟨hc0.2, h2⟩⟩
          else simp [eUnit, hpq, hc0]
        · intro m _ hm
          rw [s0.embedMatrix_apply_of_agreeOutside, sT.embedMatrix_apply_of_agreeOutside]
          if ha0 : s0.AgreeOutside p m then
            simp [show ¬ sT.AgreeOutside m q from fun hT ↦ hm <|
                (_root_.basisBits (k + 1)).injective <| funext <|
              Fin.cases ((hT 0 (by simp [sT])).trans hm0_0.symm) fun j ↦
                ((QRegister.singleton_agreeOutside 0 p m).mp ha0 j.succ (Fin.succ_ne_zero
                    j)).symm.trans (hm0_s j).symm]
          else simp [ha0]
        · exact fun ha ↦ (ha (Finset.mem_univ m₀)).elim
      have hr0 : r.compose s0 = QRegister.singleton (r 0) :=
        congrArg QRegister.mk (Function.Embedding.ext fun i ↦ Subsingleton.elim i 0 ▸ rfl)
      have hrT : r.compose sT = tailReg r :=
          congrArg QRegister.mk (Function.Embedding.ext fun _ ↦ rfl)
      rw [hSingle, r.embedMatrix_mul, ← QRegister.embedMatrix_compose,
          ← QRegister.embedMatrix_compose, hr0, hrT]
      exact (h1 0 _).mul_right (ih (tailReg r) (fun j N ↦ h1 j.succ N) _)
end
section
attribute [local reducible] totDimCompactGen
attribute [local irreducible] systemQubits_frozen ancWOfScr uRouterSwapConj
    PgBase.phaseGradientState
/--
Exact `dLayout` wire permutation moving `pAlignedKinBellMux456AsymSub`'s `24` dirty scratch
wires `5692..5712` (`21w`) and `5947..5949` (`3w`) onto clean `rHB rN` (`5827..5850`), and
moving `5950..5972` (`23w`) and `5990..6019` (`30w`) via 3-cycles and 2-cycles onto clean
`6020..6054` (`35w`) and phantom `6604..6656`, so all physical kinetic gates stay in `< 6055`
(`340 ≤ wWork`), all `uAlignedKin` wires are fixed pointwise, and
`rPermKinStack_wstate.compose rClean690Layout`
lands inside clean wires (`[5680..5691] ∪ [5827..5850] ∪ [5973..5989] ∪ [6020..6656]`).
-/
def permKinStackVal_wstate (x : ℕ) : ℕ :=
  if 5692 ≤ x ∧ x ≤ 5712 then 5827 + (x - 5692)
  else if 5827 ≤ x ∧ x ≤ 5847 then 5692 + (x - 5827)
  else if 5947 ≤ x ∧ x ≤ 5949 then 5848 + (x - 5947)
  else if 5848 ≤ x ∧ x ≤ 5850 then 5947 + (x - 5848)
  else if 5950 ≤ x ∧ x ≤ 5972 then 6020 + (x - 5950)
  else if 6020 ≤ x ∧ x ≤ 6042 then 6622 + (x - 6020)
  else if 6622 ≤ x ∧ x ≤ 6644 then 5950 + (x - 6622)
  else if 5990 ≤ x ∧ x ≤ 6001 then 6043 + (x - 5990)
  else if 6043 ≤ x ∧ x ≤ 6054 then 6645 + (x - 6043)
  else if 6645 ≤ x ∧ x ≤ 6656 then 5990 + (x - 6645)
  else if 6002 ≤ x ∧ x ≤ 6019 then 6604 + (x - 6002)
  else if 6604 ≤ x ∧ x ≤ 6621 then 6002 + (x - 6604)
  else x

theorem permKinStackVal_cases_wstate (x : ℕ) : (5692 ≤ x ∧ x ≤ 5712 ∧ permKinStackVal_wstate x =
    5827 + (x - 5692)) ∨ (5827 ≤ x ∧ x ≤ 5847 ∧ permKinStackVal_wstate x = 5692 + (x - 5827)) ∨
    (5947 ≤ x ∧ x ≤ 5949 ∧ permKinStackVal_wstate x = 5848 + (x - 5947)) ∨ (5848 ≤ x ∧ x ≤ 5850 ∧
    permKinStackVal_wstate x = 5947 + (x - 5848)) ∨ (5950 ≤ x ∧ x ≤ 5972 ∧
    permKinStackVal_wstate x = 6020 + (x - 5950)) ∨ (6020 ≤ x ∧ x ≤ 6042 ∧
    permKinStackVal_wstate x = 6622 + (x - 6020)) ∨ (6622 ≤ x ∧ x ≤ 6644 ∧
    permKinStackVal_wstate x = 5950 + (x - 6622)) ∨ (5990 ≤ x ∧ x ≤ 6001 ∧
    permKinStackVal_wstate x = 6043 + (x - 5990)) ∨ (6043 ≤ x ∧ x ≤ 6054 ∧
    permKinStackVal_wstate x = 6645 + (x - 6043)) ∨ (6645 ≤ x ∧ x ≤ 6656 ∧
    permKinStackVal_wstate x = 5990 + (x - 6645)) ∨ (6002 ≤ x ∧ x ≤ 6019 ∧
    permKinStackVal_wstate x = 6604 + (x - 6002)) ∨ (6604 ≤ x ∧ x ≤ 6621 ∧
    permKinStackVal_wstate x = 6002 + (x - 6604)) ∨ ((x < 5692 ∨ (5713 ≤ x ∧ x ≤ 5826) ∨
    (5851 ≤ x ∧ x ≤ 5946) ∨ (5973 ≤ x ∧ x ≤ 5989) ∨ (6055 ≤ x ∧ x ≤ 6603) ∨ 6657 ≤ x) ∧
    permKinStackVal_wstate x = x) := by
  if hx : x < 5692 ∨ 6657 ≤ x then
    refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr ⟨by omega, ?_⟩)))))))))))
    unfold permKinStackVal_wstate
    rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
        ite_eq_right (by omega),
      ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
          ite_eq_right (by omega),
      ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
          ite_eq_right (by omega)]
  else
    rw [show x = 5692 + (⟨x - 5692, by omega⟩ : Fin 965).val from show x = 5692 +
        (x - 5692) by omega]
    generalize (⟨x - 5692, _⟩ : Fin 965) = d
    clear hx x
    revert d
    decide +kernel
theorem permKinStackVal_lt_wstate (w : Wire dLayout) : permKinStackVal_wstate w.val < dLayout := by
  have hd : dLayout = 7298 := hDLayout_w0; have hw : w.val < dLayout := w.isLt
  rcases permKinStackVal_cases_wstate w.val with h | h | h | h | h | h | h | h | h | h | h | h | h
      <;> omega

theorem permKinStackFn_inj_wstate : Function.Injective (fun w : Wire dLayout ↦
    (⟨permKinStackVal_wstate w.val, permKinStackVal_lt_wstate w⟩ : Wire dLayout)) := by
  intro a b h; have hv := congrArg Fin.val h; dsimp only at hv
  rcases permKinStackVal_cases_wstate a.val with ha | ha | ha | ha | ha | ha | ha | ha | ha | ha
      | ha | ha | ha <;>
    (rcases permKinStackVal_cases_wstate b.val with hb | hb | hb | hb | hb | hb | hb | hb | hb | hb
        | hb | hb | hb <;>
      exact Fin.ext (by omega))

/-- Full `dLayout` register bijection for W-state Stage-4 kinetic execution. -/
def rPermKinStack_wstate : QRegister dLayout dLayout :=
    ⟨⟨fun w ↦ ⟨permKinStackVal_wstate w.val, permKinStackVal_lt_wstate w⟩,
    permKinStackFn_inj_wstate⟩⟩
theorem val_rPermKinStack_wstate (w : Wire dLayout) :
    (rPermKinStack_wstate w).val = permKinStackVal_wstate w.val := rfl

theorem rPermKinStack_fix_of_bounds_wstate (w : Wire dLayout)
    (h : w.val < 5692 ∨ (5713 ≤ w.val ∧ w.val ≤ 5826) ∨ (5851 ≤ w.val ∧ w.val ≤ 5946) ∨
    (5973 ≤ w.val ∧ w.val ≤ 5989) ∨ (6055 ≤ w.val ∧ w.val ≤ 6603) ∨ 6657 ≤ w.val) :
    rPermKinStack_wstate w = w :=
  Fin.ext (by
    rw [val_rPermKinStack_wstate]
    rcases permKinStackVal_cases_wstate w.val with g | g | g | g | g | g | g | g | g | g | g | g | g
        <;> omega)
/-- Exact coin-tight wire footprint of `pAlignedKinBellMux456AsymSub` (`[7291..7296]` excluded). -/
def IsKinBellMux98ExactWire_wstate (w : Wire dLayout) : Prop :=
    (5642 ≤ w.val ∧ w.val ≤ 5646) ∨ (5680 ≤ w.val ∧ w.val ≤ 5712) ∨ w.val = 5729 ∨ (5748 ≤ w.val ∧
    w.val ≤ 5749) ∨ (5752 ≤ w.val ∧ w.val ≤ 5778) ∨ (5851 ≤ w.val ∧ w.val ≤ 5874) ∨ (5947 ≤ w.val ∧
    w.val ≤ 6001) ∨ (7256 ≤ w.val ∧ w.val ≤ 7269) ∨ w.val = 7297
def IsKinBellMuxStackWire_wstate (w : Wire dLayout) : Prop :=
    (5642 ≤ w.val ∧ w.val ≤ 5646) ∨ (5680 ≤ w.val ∧ w.val ≤ 5691) ∨ w.val = 5729 ∨ (5748 ≤ w.val ∧
    w.val ≤ 5749) ∨ (5752 ≤ w.val ∧ w.val ≤ 5778) ∨ (5827 ≤ w.val ∧ w.val ≤ 5874) ∨ (5973 ≤ w.val ∧
    w.val ≤ 5989) ∨ (6020 ≤ w.val ∧ w.val ≤ 6054) ∨ (7256 ≤ w.val ∧ w.val ≤ 7269) ∨ w.val = 7297
theorem rPermKinStack_clean690_bounds_wstate (m : Fin 690) :
    let v := (rPermKinStack_wstate (rClean690Layout m)).val
    (5680 ≤ v ∧ v ≤ 5691) ∨ (5827 ≤ v ∧ v ≤ 5850) ∨
      (5973 ≤ v ∧ v ≤ 5989) ∨ (6020 ≤ v ∧ v ≤ 6656) := by
  have hm := m.isLt; rw [val_rPermKinStack_wstate, val_rClean690Layout]
  by_cases hm33 : m.val < 33
  · rw [ite_eq_left hm33]
    rcases permKinStackVal_cases_wstate (5680 +
        m.val) with g | g | g | g | g | g | g | g | g | g | g | g | g <;> omega
  · rw [ite_eq_right hm33]
    rcases permKinStackVal_cases_wstate (5947 +
        (m.val - 33)) with g | g | g | g | g | g | g | g | g | g | g | g | g <;> omega

theorem embedMatrix_fix_of_subreg_wstate {k : ℕ} (rP : QRegister dLayout dLayout)
    (rSub : QRegister k dLayout) (hFix : ∀ i : Fin k, rP (rSub i) = rSub i) (M : Operator (2 ^ k)) :
    rP.embedMatrix (rSub.embedMatrix M) = rSub.embedMatrix M := by
  have hComp : rP.compose rSub = rSub :=
    congrArg QRegister.mk (Function.Embedding.ext hFix)
  rw [← rP.embedMatrix_compose, hComp]

theorem embedUnitary_circ_fix_wstate (rP : QRegister dLayout dLayout) :
    ∀ {c : Circuit dLayout}, CircWires (fun w ↦ rP w = w) c →
      rP.embedUnitary c.eval = c.eval
  | .identity, _ => by rw [Circuit.eval_identity, rP.embedUnitary_one]
  | .seq _ _, ⟨h₁, h₂⟩ => by
      rw [Circuit.eval_seq, rP.embedUnitary_mul, embedUnitary_circ_fix_wstate rP h₁,
          embedUnitary_circ_fix_wstate rP h₂]
  | .gate g reg, hg =>
      Subtype.ext (embedMatrix_fix_of_subreg_wstate rP reg hg g.eval.1)

theorem alignedKin_wires_of_bounds_wstate {P : Wire dLayout → Prop}
    (hP : ∀ w : Wire dLayout,
      ((5642 ≤ w.val ∧ w.val ≤ 5649) ∨ w.val = 5729 ∨ (5748 ≤ w.val ∧ w.val ≤ 5778) ∨
        (5851 ≤ w.val ∧ w.val ≤ 5874) ∨ (6056 ≤ w.val ∧ w.val ≤ 6603) ∨ 6657 ≤ w.val) → P w) :
    UnembedO3Bridge.CircWires P (DynQromUncompA.fwdCirc pKinAlign0) ∧
    (∀ i : Fin 50, P (rSpeciesSwap50Layout i)) ∧ (∀ i : Fin 27, P (rMux27Layout i)) ∧
    (∀ i : Fin 8, P (rPKinLayout i)) ∧ (∀ i : Fin 226, P (rKin226Layout i)) ∧
    (∀ i : Fin 13, P (qft8Stg3Clean13 scrWLayout offKinLayout hoffKinLayout i)) ∧
    PhotochemistrySolution.UnembedO3Bridge.AndBracketWires P
      (polyPostCancelT5Qft8Bracket98 (locCat8SharedCompactGen scrWLayout) rPKinLayout
        (qft8Stg3Delta7 scrWLayout offKinLayout hoffKinLayout)
            (qft8Stg3Carry6 scrWLayout offKinLayout hoffKinLayout)
        (qft8Stg3_rP_disj_cat8 qft8Stg3ValidP_layout)
            (qft8Stg3_rP_disj_delta7 hoffKinLayout qft8Stg3ValidP_layout)
        (qft8Stg3_delta7_disj_cat8 hoffKinLayout) (qft8Stg3_delta7_disj_carry6 hoffKinLayout)
        (qft8Stg3_cat8_disj_carry6 hoffKinLayout)
            (qft8Stg3_rP_disj_carry6 hoffKinLayout qft8Stg3ValidP_layout)) := by
  have hd : dLayout = 7298 := hDLayout_w0
  have hOut (i : Fin 40) (hi : i.val = 14 ∨ i.val = 33 ∨ 38 ≤ i.val) : P (rOut40Layout i) :=
    (fun _ _ ↦ hP _ (by omega)) i.isLt (val_rOut40Layout i)
  have hAln (i : Fin 136) (hi : 109 ≤ i.val) : P (rAlignLayout i) :=
    (fun _ _ ↦ hP _ (by omega)) i.isLt (val_rAlignLayout i)
  have hP8 (i : Fin 8) : P (rPKinLayout i) := (fun _ _ ↦ hP _ (by omega)) i.isLt (val_rPKinLayout i)
  have hCln (i : Fin 13) : P (qft8Stg3Clean13 scrWLayout offKinLayout hoffKinLayout i) :=
    qft8Stg3Clean13_eq_workInner i ▸ (fun _ _ ↦
        hP _ (by omega)) i.isLt (val_rWorkInnerLayout ⟨i.val, by omega⟩)
  refine ⟨PhotochemistrySolution.FusedUnembedLGen.circWires_fwdCirc_of_cpWires_fs
      (cpWires_pKinAlign0_exact ⟨hOut ⟨38, by decide⟩ (by decide), hAln ⟨109, by decide⟩
          (by decide)⟩
        ⟨hOut ⟨39, by decide⟩ (by decide), hAln ⟨110, by decide⟩ (by decide)⟩
        ⟨hOut ⟨33, by decide⟩ (by decide), hAln ⟨135, by decide⟩ (by decide)⟩
        ⟨hOut ⟨14, by decide⟩ (by decide), hAln ⟨111, by decide⟩ (by decide)⟩),
    fun i ↦
        rSp50_eq_fn_w0 i ▸ (fun _ h ↦
        hP _ (by split_ifs at h <;> omega)) i.isLt (val_speciesSwap50WireFn i),
    fun i ↦
        rMux27_eq_fn_w0 i ▸ (fun _ h ↦
        hP _ (by split_ifs at h <;> omega)) i.isLt (val_mux27WireFn i),
    hP8,
    fun i ↦
        rKin226_eq_fn_w0 i ▸ (fun _ h ↦
        hP _ (by split_ifs at h <;> omega)) i.isLt (val_kin226WireFn i),
    hCln,
    andBracketWires_polyPostCancelT5Qft8Bracket98 (P := P) _ _ _ _ _ _ _ _ _ _
      (fun c ↦ hP _ (by
        have := c.isLt
        rw [val_locCat8_layout]
        omega)) hP8
      (fun i ↦ qft8Stg3_clean13_sub_delta7 hoffKinLayout ⟨i.val, by omega⟩ ▸ hCln ⟨i.val, by omega⟩)
      (fun i ↦ qft8Stg3_clean13_sub_carry6 hoffKinLayout ⟨i.val, by omega⟩ ▸ hCln ⟨7 + i.val,
          by omega⟩)⟩

theorem rPermKinStack_embedUnitary_uAlignedKin_eq_wstate :
    rPermKinStack_wstate.embedUnitary uAlignedKinIdeal2m1Layout = uAlignedKinIdeal2m1Layout ∧
    rPermKinStack_wstate.embedUnitary uAlignedKinCat2m1_98UselLayout =
    uAlignedKinCat2m1_98UselLayout ∧
    rPermKinStack_wstate.embedUnitary uAlignedKinCat2m1_98CselLayout =
    uAlignedKinCat2m1_98CselLayout := by
  let rP := rPermKinStack_wstate; have hd : dLayout = 7298 := hDLayout_w0
  have fConj : ∀ {W V : Unitary (2 ^ dLayout)},
      rP.embedUnitary W = W → rP.embedUnitary V = V →
      rP.embedUnitary (W⁻¹ * V * W) = W⁻¹ * V * W := fun {W V} hW hV ↦ by
    rw [rP.embedUnitary_mul, rP.embedUnitary_mul, rP.embedUnitary_inv, hW, hV]
  obtain ⟨cwA0, hSp, hMux, hFixP, hMid, hFixCln, abQ⟩ :=
    alignedKin_wires_of_bounds_wstate (P := fun w ↦ rP w = w) fun w hw ↦
        rPermKinStack_fix_of_bounds_wstate w (by omega)
  have fA0 : rP.embedUnitary uKinAlign0Layout = uKinAlign0Layout :=
      embedUnitary_circ_fix_wstate rP cwA0
  have fSp : rP.embedUnitary uSpeciesSwap50Layout = uSpeciesSwap50Layout :=
      Subtype.ext (embedMatrix_fix_of_subreg_wstate rP _ hSp _)
  have fMux : rP.embedUnitary uMux27Layout = uMux27Layout :=
      Subtype.ext (embedMatrix_fix_of_subreg_wstate rP rMux27Layout hMux _)
  have fQid : rP.embedUnitary (qft8Stg3IdealU scrWLayout rPKinLayout) =
      qft8Stg3IdealU scrWLayout rPKinLayout :=
    Subtype.ext (embedMatrix_fix_of_subreg_wstate rP rPKinLayout hFixP _)
  have fQdpost : rP.embedUnitary (rPKinLayout.embedUnitary (dPost8U * qftGridUnitary)) =
      rPKinLayout.embedUnitary (dPost8U * qftGridUnitary) :=
          Subtype.ext (embedMatrix_fix_of_subreg_wstate rP rPKinLayout hFixP _)
  have fMid : rP.embedUnitary uKinMid2m1UselLayout = uKinMid2m1UselLayout :=
      Subtype.ext (embedMatrix_fix_of_subreg_wstate rP _ hMid _)
  have fQcat :
      rP.embedUnitary (qft8PostCancel98CatU () scrWLayout offKinLayout hoffKinLayout rPKinLayout
      qft8Stg3ValidP_layout) =
      qft8PostCancel98CatU () scrWLayout offKinLayout hoffKinLayout rPKinLayout
          qft8Stg3ValidP_layout := by
    let rCln := qft8Stg3Clean13 scrWLayout offKinLayout hoffKinLayout
    have fBr :
        rP.embedMatrix (polyPostCancelT5Qft8Bracket98 (locCat8SharedCompactGen scrWLayout)
        rPKinLayout (qft8Stg3Delta7 scrWLayout offKinLayout hoffKinLayout)
        (qft8Stg3Carry6 scrWLayout offKinLayout hoffKinLayout)
        (qft8Stg3_rP_disj_cat8 qft8Stg3ValidP_layout)
        (qft8Stg3_rP_disj_delta7 hoffKinLayout qft8Stg3ValidP_layout)
        (qft8Stg3_delta7_disj_cat8 hoffKinLayout) (qft8Stg3_delta7_disj_carry6 hoffKinLayout)
        (qft8Stg3_cat8_disj_carry6 hoffKinLayout)
        (qft8Stg3_rP_disj_carry6 hoffKinLayout qft8Stg3ValidP_layout)).toCircuit.eval.1 = _ :=
        congrArg Subtype.val (embedUnitary_circ_fix_wstate rP (circWires_toCircuit_c70 abQ));
        have fP13 : rP.embedMatrix (rCln.basisOutcomeProjector 0) = rCln.basisOutcomeProjector 0 :=
        embedMatrix_fix_of_subreg_wstate rP rCln hFixCln (compProj 0);
        have fQdpostM : rP.embedMatrix (rPKinLayout.embedUnitary (dPost8U * qftGridUnitary)).1 =
        (rPKinLayout.embedUnitary (dPost8U * qftGridUnitary)).1 :=
        congrArg Subtype.val fQdpost; refine Subtype.ext ?_; unfold qft8PostCancel98CatU
        polyPostCancelCleanUnitary spliceUnitary; change rP.embedMatrix (spliceUnitaryMat _ _ _) =
        spliceUnitaryMat _ _ _; unfold spliceUnitaryMat; rw [rP.embedMatrix_add, rP.embedMatrix_mul,
        rP.embedMatrix_mul, (QRegExt.embedMatrix_sub rP), rP.embedMatrix_one, fBr, fP13, fQdpostM]
  have fId : rP.embedUnitary uAlignedKinIdeal2m1Layout = uAlignedKinIdeal2m1Layout :=
      fConj fA0 (fConj fSp (fConj fMux (fConj fQid fMid)));
      have fUsel : rP.embedUnitary uAlignedKinCat2m1_98UselLayout =
      uAlignedKinCat2m1_98UselLayout :=
      fConj fA0 (fConj fSp (fConj fMux (fConj fQcat fMid)));
      let Pq :=
      projOneQCompactGen scrWLayout; have sKin :=
                                       csel_conj_unitary Pq uKinAlign0Layout
                                       uKinCat2m1_98CselLayout uKinCat2m1_98UselLayout
                                       comm_pq.2.eq uKin2m1_98Layout_props.1
                                       uKin2m1_98Layout_props.2.1
  have fPq : rP.embedMatrix Pq = Pq :=
      embedMatrix_fix_of_subreg_wstate rP (QRegister.singleton wLocQLayout)
    (fun i ↦ Subsingleton.elim i 0 ▸ rPermKinStack_fix_of_bounds_wstate wLocQLayout ((fun _ ↦
        by omega) val_wLocQLayout))
    (compProj 1)
  have fCsel : rP.embedUnitary uAlignedKinCat2m1_98CselLayout = uAlignedKinCat2m1_98CselLayout := by
    have fUselM : rP.embedMatrix (uKinAlign0Layout⁻¹ * uKinCat2m1_98UselLayout *
        uKinAlign0Layout).1 = (uKinAlign0Layout⁻¹ * uKinCat2m1_98UselLayout * uKinAlign0Layout).1 :=
        congrArg Subtype.val fUsel; refine Subtype.ext ?_; change rP.embedMatrix
        uAlignedKinCat2m1_98CselLayout.1 = uAlignedKinCat2m1_98CselLayout.1
    unfold uAlignedKinCat2m1_98CselLayout at *
    rw [sKin.1, rP.embedMatrix_add, (QRegExt.embedMatrix_sub rP), rP.embedMatrix_one,
        rP.embedMatrix_mul, fPq,
        fUselM]
  exact ⟨fId, fUsel, fCsel⟩
end
section
attribute [local reducible] totDimCompactGen
attribute [local irreducible] systemQubits_frozen ancWOfScr uRouterSwapConj
    PgBase.phaseGradientState reflULGen
def uStage4ReflRev2m1Ideal {potExpect : PotExpectFn} (spec : ReflPotSliceSpec potExpect) :
    Unitary (2 ^ dLayout) :=
  uPotReflIdealZeroNErem spec * uAlignedKinIdeal2m1Layout

/-- Reversed-order unguarded cat `98-T` `(2m+1)` Stage-4 unitary `uPot * uKin`. -/
def uStage4ReflRev2m1_98CatUsel {potExpect : PotExpectFn} (spec : ReflPotSliceSpec potExpect) :
    Unitary (2 ^ dLayout) :=
  uPotReflIdealZeroNErem spec * uAlignedKinCat2m1_98UselLayout

/-- Reversed-order cat-guarded `98-T` `(2m+1)` Stage-4 unitary `uPotCsel * uKinCsel`. -/
def uStage4ReflRev2m1_98CatCsel {potExpect : PotExpectFn} (spec : ReflPotSliceSpec potExpect) :
    Unitary (2 ^ dLayout) := uPotReflCatCselZeroNErem spec * uAlignedKinCat2m1_98CselLayout
theorem uStage4ReflRev2m1_98Layout_props {potExpect : PotExpectFn}
    (spec : ReflPotSliceSpec potExpect) : (uStage4ReflRev2m1_98CatCsel spec).1 =
    (1 - projOneQCompactGen scrWLayout) + projOneQCompactGen scrWLayout *
    (uStage4ReflRev2m1_98CatUsel spec).1 ∧ (uStage4ReflRev2m1_98CatUsel spec).1 *
    cat8SharedProjCompactGen scrWLayout = (uStage4ReflRev2m1Ideal spec).1 *
    cat8SharedProjCompactGen scrWLayout ∧ (∀ {k : ℕ} (r : QRegister k dLayout),
    OffIndexAndScratchPoly systemQubits_frozen scrWLayout (lcuSubLGen hpLayout)
    (scrSubLGen hpLayout) r → ∀ M : Operator (2 ^ k),
    Commute (uStage4ReflRev2m1Ideal spec).1 (r.embedMatrix M)) := by
  let Pq := projOneQCompactGen scrWLayout;
  have hPq_idem : Pq * Pq = Pq :=
      (QRegister.singleton wLocQLayout).basisOutcomeProjector_mul_self 1;
      have sKin :=
      csel_conj_unitary Pq uKinAlign0Layout uKinCat2m1_98CselLayout uKinCat2m1_98UselLayout
      comm_pq.2.eq uKin2m1_98Layout_props.1 uKin2m1_98Layout_props.2.1;
      have cPotPq : (uPotReflIdealZeroNErem spec).1 * Pq = Pq * (uPotReflIdealZeroNErem spec).1 :=
      (uPotReflIdealZeroNErem_comm_off spec hoff_wLocQ (compProj 1)).eq;
      have sAll :=
      (csel_seq_and_conj_eq_of_comm_proj Pq hPq_idem 1 ((one_mul Pq).trans (mul_one Pq).symm)
      (uPotReflCatCselZeroNErem spec).1 (uPotReflIdealZeroNErem spec).1
      uAlignedKinCat2m1_98CselLayout.1 uAlignedKinCat2m1_98UselLayout.1
      (uPotReflCatCselZeroNErem_eq_ctrl spec) sKin.1 cPotPq).1;
      let Mcat :=
      Matrix.vecMulVec (PgBase.phaseGradientState 8)
      (star (PgBase.phaseGradientState 8)); let Pc : Operator (2 ^ dLayout) :=
                                              cat8SharedProjCompactGen scrWLayout;
                                              have cKin0Cat : uKinAlign0Layout.1 * Pc = Pc *
                                              uKinAlign0Layout.1 :=
                                              (cOffPre _ hoff_cat8_layout Mcat).2.eq
  have hKinCat : uAlignedKinCat2m1_98UselLayout.1 * Pc = uAlignedKinIdeal2m1Layout.1 * Pc := by
    simpa only [Matrix.mul_one, Matrix.one_mul] using
      conj_seq_cat_eq (uKinAlign0Layout⁻¹).1 uKinAlign0Layout.1 uKinCat2m1_98UselLayout.1
          uKinIdeal2m1UselLayout.1
        uAlignedKinCat2m1_98UselLayout.1 uAlignedKinIdeal2m1Layout.1 1 Pc cKin0Cat
            uKin2m1_98Layout_props.2.2.1 rfl rfl (Commute.one_left Pc).eq
  have hCat : (uStage4ReflRev2m1_98CatUsel spec).1 * Pc = (uStage4ReflRev2m1Ideal spec).1 * Pc := by
    unfold uStage4ReflRev2m1_98CatUsel uStage4ReflRev2m1Ideal;
    rw [Submonoid.coe_mul, Submonoid.coe_mul, Matrix.mul_assoc, hKinCat, ← Matrix.mul_assoc]
  have cConjOff {W V : Unitary (2 ^ dLayout)} {A : Operator (2 ^ dLayout)} (cW : Commute W.1 A)
      (cV : Commute V.1 A) : Commute (W⁻¹ * V * W).1 A :=
    Commute.mul_left (Commute.mul_left (SelectFastQft8Gidney.unitary_inv_comm W _ cW) cV) cW
  exact ⟨sAll, hCat, fun r hoff M ↦
      (uPotReflIdealZeroNErem_comm_off spec hoff M).mul_left (cConjOff (cOffPre r hoff M).2
      (uKin2m1_98Layout_props.2.2.2 r hoff M))⟩
theorem uStage4ReflRev2m1_98_comm_coinBand7256 {kCoin : ℕ} {potExpect : PotExpectFn}
    (rC : QRegister kCoin dLayout) (hBand : ∀ j : Fin kCoin, 7143 ≤ (rC j).val ∧ (rC j).val < 7256)
    (spec : ReflPotSliceSpec potExpect) (M : Operator (2 ^ kCoin)) :
    Commute (uStage4ReflRev2m1Ideal spec).1 (rC.embedMatrix M) ∧
    Commute (uStage4ReflRev2m1_98CatUsel spec).1 (rC.embedMatrix M) ∧
    Commute (uStage4ReflRev2m1_98CatCsel spec).1 (rC.embedMatrix M)
    := by obtain ⟨cKI, cKU, cKC⟩ :=
            uAlignedKin2m1_98_comm_coinBand7256 rC hBand M; exact
            ⟨(uPotReflZeroNErem_comm_coinBand7256 rC hBand spec false M).mul_left cKI,
            (uPotReflZeroNErem_comm_coinBand7256 rC hBand spec false M).mul_left cKU,
            (uPotReflZeroNErem_comm_coinBand7256 rC hBand spec true M).mul_left cKC⟩
theorem uStage4ReflRev2m1_98_comm_locGrad3Hi {potExpect : PotExpectFn}
    (spec : ReflPotSliceSpec potExpect) (M : Operator (2 ^ 3)) :
    Commute (uStage4ReflRev2m1_98CatUsel spec).1 ((locGrad3HiCompactGen scrWLayout).embedMatrix M) ∧
    Commute (uStage4ReflRev2m1_98CatCsel spec).1 ((locGrad3HiCompactGen scrWLayout).embedMatrix M)
    := by obtain ⟨_, cKU, cKC⟩ :=
            uAlignedKin2m1_98_comm_locGrad3Hi M; exact ⟨(uPotReflZeroNErem_comm_locGrad3Hi spec
            false M).mul_left cKU, (uPotReflZeroNErem_comm_locGrad3Hi spec true M).mul_left cKC⟩
theorem uStage4ReflRev2m1_98_preserves_routed {decodeCoin : Fin (2 ^ 41) → ZeroNEremSector}
    {potExpect : PotExpectFn} (spec : ReflPotSliceSpec potExpect) (isCsel : Bool)
    (γ : BitAssignment dLayout) (hγ : IsRoutedKet decodeCoin γ) :
    inKetPred (IsRoutedKet decodeCoin)
    ((if isCsel then uStage4ReflRev2m1_98CatCsel spec else uStage4ReflRev2m1_98CatUsel
    spec).1.mulVec (ket γ)) := by
  have hUsel : inKetPred (IsRoutedKet decodeCoin)
      ((uStage4ReflRev2m1_98CatUsel spec).1.mulVec (ket γ)) := by
    unfold uStage4ReflRev2m1_98CatUsel uPotReflIdealZeroNErem;
    rw [Submonoid.coe_mul, ← Matrix.mulVec_mulVec]
    refine inKetPred_mulVec (uPotReflZeroNErem spec false).1 (fun δ ⟨α, c, z0, hα, hEq⟩ ↦ ?_)
        (uAlignedKinCat2m1_98Usel_preserves_routed γ hγ)
    subst hEq
    obtain ⟨z', hz'⟩ := potReflSwap4_routedKet (decodeCoin := decodeCoin) spec α c z0
    rw [uPotReflZeroNErem_mulVec_ket, hz'];
    exact inKetPred_smul _ (inKetPred_ket ⟨α, c, z', hα, rfl⟩)
  cases isCsel
  · exact hUsel
  · change inKetPred (IsRoutedKet decodeCoin)
        ((uStage4ReflRev2m1_98CatCsel spec).1.mulVec (ket γ))
    rw [(uStage4ReflRev2m1_98Layout_props spec).1, Matrix.add_mulVec, Matrix.sub_mulVec,
        Matrix.one_mulVec,
        ← Matrix.mulVec_mulVec]; exact inKetPred_add (inKetPred_sub (inKetPred_ket hγ)
        (projOneQ_inKetPred (inKetPred_ket hγ))) (projOneQ_inKetPred hUsel)
theorem comm_pScr_reflRev2m1_98UselPre {wIn : ℕ} {decodeCoin : Fin (2 ^ 41) → ZeroNEremSector}
    {potExpect : PotExpectFn} (o1 : Stage1ZeroNEremLayout wIn decodeCoin)
    (spec : ReflPotSliceSpec potExpect) : pScr *
    (preConj o1.uLocal (uStage4ReflRev2m1_98CatUsel spec)).1 =
    (preConj o1.uLocal (uStage4ReflRev2m1_98CatUsel spec)).1 * pScr := by
  let uMid := (wNoHad o1.uLocal)⁻¹ * uStage4ReflRev2m1_98CatUsel spec * wNoHad o1.uLocal
  have hMid : pScr * uMid.1 = uMid.1 * pScr := comm_pScr_of_cleanKet uMid fun α hα ↦ by
    let c := outerCoinOf82 (fun i ↦ α (rLcu82Layout i))
    let z := innerBitsOf82 (fun i ↦ α (rLcu82Layout i))
    have hFwd : (wNoHad o1.uLocal).1.mulVec (ket α) = ket (routedKet decodeCoin α c z) :=
        (congrArg (wNoHad o1.uLocal).1.mulVec (congrArg ket (routedStage0_self α).symm)).trans
        (wNoHad_mulVec_ket o1 hα c z); dsimp only [uMid]; rw [Submonoid.coe_mul,
        Submonoid.coe_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hFwd]
    refine inKetPred_mulVec ((wNoHad o1.uLocal)⁻¹).1 (fun γ hγ ↦ ?_)
        (uStage4ReflRev2m1_98_preserves_routed spec false _ ⟨α, c, z, hα, rfl⟩)
    obtain ⟨β', c', z', hScr', rfl⟩ :=
        hγ; rw [wNoHad_inv_mulVec_ket o1 hScr' c' z']; exact inKetPred_ket
        (cleanScr_routedStage0 hScr' c' z')
  have hW : (preConj o1.uLocal (uStage4ReflRev2m1_98CatUsel spec)).1 = (uHad82Layout⁻¹).1 *
      uMid.1 *
      uHad82Layout.1
      := by unfold preConj wFull; rw [_root_.mul_inv_rev]; simp only [Submonoid.coe_mul,
              Matrix.mul_assoc, uMid]
  rw [hW]; exact conj_uHad82_comm_pScr uMid.1 hMid
theorem comm_pScr_reflRev2m1_98CselPre {wIn : ℕ} {decodeCoin : Fin (2 ^ 41) → ZeroNEremSector}
    {potExpect : PotExpectFn} (o1 : Stage1ZeroNEremLayout wIn decodeCoin)
    (spec : ReflPotSliceSpec potExpect) : pScr *
    (preConj o1.uLocal (uStage4ReflRev2m1_98CatCsel spec)).1 =
    (preConj o1.uLocal (uStage4ReflRev2m1_98CatCsel spec)).1 * pScr :=
  comm_proj_of_ctrl pScr (projOneQCompactGen scrWLayout)
      (preConj o1.uLocal (uStage4ReflRev2m1_98CatUsel spec)).1 (preConj
    o1.uLocal (uStage4ReflRev2m1_98CatCsel spec)).1
    (pScr_comm_off hoff_wLocQ (compProj 1)).eq (comm_pScr_reflRev2m1_98UselPre o1 spec)
    (unitary_conj_ctrl (d := 2 ^ dLayout) (wFull o1.uLocal) (uStage4ReflRev2m1_98CatCsel spec)
        (uStage4ReflRev2m1_98CatUsel spec)
      (projOneQCompactGen scrWLayout)
          (wFull_comm_off o1 hoff_wLocQ (compProj 1)).eq (uStage4ReflRev2m1_98Layout_props
          spec).1)
theorem comm_pScr_reflRev2m1_IdPre {wIn : ℕ} {decodeCoin : Fin (2 ^ 41) → ZeroNEremSector}
    {potExpect : PotExpectFn} (o1 : Stage1ZeroNEremLayout wIn decodeCoin)
    (spec : ReflPotSliceSpec potExpect) : pScr *
    (preConj o1.uLocal (uStage4ReflRev2m1Ideal spec)).1 =
    (preConj o1.uLocal (uStage4ReflRev2m1Ideal spec)).1 * pScr :=
  comm_pScr_id_of_usel o1 (uStage4ReflRev2m1Ideal spec) (uStage4ReflRev2m1_98CatUsel spec)
      (fun r M hoff ↦ (uStage4ReflRev2m1_98Layout_props spec).2.2 r hoff M)
    (unitary_conj_mul_right (d := 2 ^ dLayout) (wFull o1.uLocal)
        (uStage4ReflRev2m1_98CatUsel spec) (uStage4ReflRev2m1Ideal spec)
        (cat8SharedProjCompactGen scrWLayout)
      (wFull_comm_off o1 hoff_cat8_layout (Matrix.vecMulVec (PgBase.phaseGradientState 8)
          (star (PgBase.phaseGradientState 8)))).eq
        (uStage4ReflRev2m1_98Layout_props spec).2.1)
    (comm_pScr_reflRev2m1_98UselPre o1 spec)
theorem uStage4ReflRev2m1Ideal_routedKet_eq {decodeCoin : Fin (2 ^ 41) → ZeroNEremSector}
    {potExpect : PotExpectFn} (spec : ReflPotSliceSpec potExpect) {α : BitAssignment dLayout}
    (hScr : CleanScr α) (c : Fin (2 ^ 41)) (z : BitAssignment 41) :
    (uStage4ReflRev2m1Ideal spec).1.mulVec (ket (routedKet decodeCoin α c z)) =
    (uStage4ReflZeroNErem2m1Ideal spec).1.mulVec (ket (routedKet decodeCoin α c z)) := by
  let γ := routedKet decodeCoin α c z; let U := uPotReflIdealZeroNErem spec;
  let K := uAlignedKinIdeal2m1Layout
  have hClean22 := routedKet_workInner (decodeCoin := decodeCoin) hScr c z ⟨22, fin22_lt_521_pot⟩
  have hSec := uStage4ReflZeroNErem2m1Ideal_sector_and_invol spec γ hClean22
  have hPot0 (δ : BitAssignment dLayout) (h0 : δ wIsFine = 0) : U.1.mulVec (ket δ) = ket δ := by
    have hAct : potGateActive4 false rPot0Layout δ = false := by
      simp [potGateActive4, wPotIsPot_rPot0Layout_eq, h0]
    simp only [U, uPotReflIdealZeroNErem, uPotReflZeroNErem_mulVec_ket, potReflPh4, potReflSwap4,
      hAct, wPotIsPot_rPot0Layout_eq, h0, Bool.false_eq_true, ↓reduceIte, zero_mul, bitSign_zero,
          one_smul]
  rcases routedKet_sector_flags (decodeCoin := decodeCoin) hScr c z with ⟨hf, hk⟩ | ⟨hf,
      hk⟩ | ⟨hf, hk⟩
  · rw [(hSec.1 hf hk).1]; unfold uStage4ReflRev2m1Ideal;
    rw [Submonoid.coe_mul, ← Matrix.mulVec_mulVec, uAlignedKinIdeal2m1_fix γ hk hClean22];
    exact hPot0 γ hf
  · rw [(hSec.2.1 hf hk).1]; have hfγ : γ wIsFine = 1 := hf
    have hAct : potGateActive4 false rPot0Layout γ = true := by
      unfold potGateActive4; rw [wPotIsPot_rPot0Layout_eq, hfγ]; rfl
    unfold uStage4ReflRev2m1Ideal;
    rw [Submonoid.coe_mul, ← Matrix.mulVec_mulVec, uAlignedKinIdeal2m1_fix γ hk hClean22];
    dsimp only [uPotReflIdealZeroNErem]; rw [uPotReflZeroNErem_mulVec_ket];
    simp only [potReflPh4, potReflSwap4, hAct, wPotIsPot_rPot0Layout_eq, hfγ, Bool.false_eq_true,
        ↓reduceIte, one_mul]
  · rw [(hSec.2.2 hf hk).1]; let P := pBit0 wIsFine
    have hUP : U.1 * P = P := matrix_ext_ket fun δ ↦ by
      rw [← Matrix.mulVec_mulVec, show P = _ from rfl, SelectRefl.ket_basisOutcomeProjector_zero]
      if zF : ∀ i : Fin 1, δ ((QRegister.singleton wIsFine) i) = 0 then rw [ifPosSqf zF,
          hPot0 δ (zF 0)]
      else rw [ifNegSqf zF, Matrix.mulVec_zero]
    have cA : uKinAlign0Layout.1 * P = P * uKinAlign0Layout.1 := matrix_ext_ket fun δ ↦ by
      have hku : (pKinAlign0.fwdBits δ) wIsFine = δ wIsFine :=
        fwdBits_not_target targetsIn_pKinAlign0 δ (by simp [wIsFine, val_rOut40Layout])
      have hkδ : uKinAlign0Layout.1.mulVec (ket δ) = ket (pKinAlign0.fwdBits δ) :=
          fwdCirc_mulVec_ket pKinAlign0 δ
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hkδ]
      if hz : δ wIsFine = 0 then rw [pBit0_ket hz, hkδ, pBit0_ket (hku.trans hz)]
      else
        dsimp only [P, pBit0]
        rw [SelectRefl.ket_basisOutcomeProjector_zero, ifNegSqf fun h ↦ hz (h 0),
            Matrix.mulVec_zero,
          SelectRefl.ket_basisOutcomeProjector_zero, ifNegSqf fun h ↦ hz (hku.symm.trans (h 0))]
    have hKA : K.1 = _ :=
        congrArg (fun X : Unitary _ ↦ X.1 * uKinIdeal2m1UselLayout.1 *
        uKinAlign0Layout.1) uKinAlign0Layout_inv_eq
    have cKP : K.1 * P = P * K.1 := by
      calc K.1 * P = uKinAlign0Layout.1 * uKinIdeal2m1UselLayout.1 * (uKinAlign0Layout.1 * P) := by
            simp only [hKA, Matrix.mul_assoc]
        _ = uKinAlign0Layout.1 * (uKinIdeal2m1UselLayout.1 * P) * uKinAlign0Layout.1 := by
            rw [cA, ← Matrix.mul_assoc _ P, Matrix.mul_assoc uKinAlign0Layout.1]
        _ = (uKinAlign0Layout.1 * P) * uKinIdeal2m1UselLayout.1 * uKinAlign0Layout.1 := by
            rw [show P = pBit0 wIsFine from rfl, uKinIdeal2m1_comm_pBit0_wIsFine,
                ← Matrix.mul_assoc uKinAlign0Layout.1]
        _ = P * K.1 := by simp only [cA, hKA, Matrix.mul_assoc]
    have hUKP : (U * K).1 * P = K.1 * P := by
      rw [Submonoid.coe_mul, Matrix.mul_assoc, cKP, ← Matrix.mul_assoc, hUP, ← cKP]
    have hPγ : P.mulVec (ket γ) = ket γ := pBit0_ket hf
    simpa only [uStage4ReflRev2m1Ideal, ← Matrix.mulVec_mulVec,
        hPγ] using congrArg (·.mulVec (ket γ)) hUKP
theorem preLoc_reflRev2m1Ideal_mul_pScr {wIn : ℕ} {decodeCoin : Fin (2 ^ 41) → ZeroNEremSector}
    {potExpect : PotExpectFn} (o1 : Stage1ZeroNEremLayout wIn decodeCoin)
    (spec : ReflPotSliceSpec potExpect) : preLoc o1.uLocal (uStage4ReflRev2m1Ideal spec) *
    pScr = preLoc o1.uLocal (uStage4ReflZeroNErem2m1Ideal spec) * pScr := by
  let W := wNoHad o1.uLocal
  have hMid : (W⁻¹ * uStage4ReflRev2m1Ideal spec * W).1 * pScr =
      (W⁻¹ * uStage4ReflZeroNErem2m1Ideal spec * W).1 * pScr := matrix_ext_ket fun α ↦ by
    change (_ * rScrLayout.basisOutcomeProjector 0).mulVec (ket α) =
        (_ * rScrLayout.basisOutcomeProjector 0).mulVec (ket α)
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, SelectRefl.ket_basisOutcomeProjector_zero]
    if hScr : CleanScr α then
      rw [ifPosSqf hScr]
      simp only [Submonoid.coe_mul, ← Matrix.mulVec_mulVec,
        (congrArg W.1.mulVec (congrArg ket (routedStage0_self α).symm)).trans (wNoHad_mulVec_ket
            o1 hScr _ _),
        uStage4ReflRev2m1Ideal_routedKet_eq spec hScr]
    else rw [ifNegSqf hScr, Matrix.mulVec_zero, Matrix.mulVec_zero]
  have cHad : uHad82Layout.1 * pScr = pScr * uHad82Layout.1 :=
    SelectSandwich.hadamardRegSym_comm_disjoint (Var :=
        Unit) wHasN1 82 rLcu82Layout hDisjHad82_layout rScrLayout
      (PhotochemistrySolution.PotOracleGen.disj_of_ne fun i j e ↦ by
        have hm80 : mLayout = 80 := rfl; have hi82 : i.val < mLayout + 2 := i.isLt;
        have hj : j.val < scrLExt 0 := j.isLt; have hj1565 : j.val < 1565 := j.isLt;
        have hv : (rLcu82Layout ⟨i.val, hi82⟩).val = (rScrExt 0 hk0_le72_wstate ⟨j.val, hj⟩).val :=
            congrArg Fin.val e; rw [val_rLcu82Layout, val_rScrExt] at hv
        dsimp only at hv; omega) (compProj 0)
  have hForm (M : Unitary (2 ^ dLayout)) : preLoc o1.uLocal M * pScr = (uHad82Layout⁻¹).1 *
      ((W⁻¹ * M * W).1 * pScr) * uHad82Layout.1 := by
    change (preConj o1.uLocal M).1 * pScr = _; unfold preConj wFull;
    rw [_root_.mul_inv_rev]; simp only [Submonoid.coe_mul, Matrix.mul_assoc, W]; rw [cHad]
  rw [hForm, hForm, hMid]
theorem hInvolPreScr_reflRev2m1_98_wstate {wIn : ℕ} {decodeCoin : Fin (2 ^ 41) → ZeroNEremSector}
    {potExpect : PotExpectFn} (o1 : Stage1ZeroNEremLayout wIn decodeCoin)
    (spec : ReflPotSliceSpec potExpect) : preLoc o1.uLocal (uStage4ReflRev2m1Ideal spec) *
    (preLoc o1.uLocal (uStage4ReflRev2m1Ideal spec) * pScr) = pScr := by
  have hEq := preLoc_reflRev2m1Ideal_mul_pScr o1 spec;
  have hC := comm_pScr_refl2m1_IdPre o1 spec
  have hAbs : pScr * (preLoc o1.uLocal (uStage4ReflZeroNErem2m1Ideal spec) * pScr) =
      preLoc o1.uLocal (uStage4ReflZeroNErem2m1Ideal spec) *
      pScr := by rw [← Matrix.mul_assoc, hC, Matrix.mul_assoc, pScr_idem]
  rw [hEq, ← hAbs, ← Matrix.mul_assoc, hEq, Matrix.mul_assoc, hAbs];
  exact rawIdealSelectReflZeroNErem_2m1_invol o1 spec
theorem sum_z41_slice_reflRev2m1_98_wstate {kExt kOut w1 : ℕ} {wEE : Fin 4 → ℕ}
    {wNN : Fin 4 → Fin 4 → ℕ} {wEN : Fin 4 → ℕ} {wKin : Particle_frozen → ℕ} {wIdle : ℕ}
    {decode : Fin (2 ^ 41) → ZeroNEremSector} {peKOut : BitAssignment (kExt + kOut) → PotExpectFn}
    (o1 : Stage1ZeroNEremLayout w1 decode) (specKOut : ∀ γω : BitAssignment (kExt + kOut),
    ReflPotSliceSpec (peKOut γω)) (hCoin : ValidGenZeroNEremCoin wEE wNN wEN wKin wIdle decode)
    (γω : BitAssignment (kExt + kOut)) {β : BitAssignment dLayout}
    (hr0 : ∀ u, β (rLcu82Layout u) = 0) (hScr : CleanScr β) (c : Fin (2 ^ 41)) :
    (∑ z : BitAssignment 41, (rLcu82Layout.basisOutcomeProjector 0 *
    (uHad82Layout⁻¹).1).mulVec ((((wNoHad o1.uLocal)⁻¹ * uStage4ReflRev2m1Ideal (specKOut γω) *
    wNoHad o1.uLocal).1).mulVec (ket (routedStage0 β c z)))) =
    (sqrtHalf ^ 82) • (rSysLayout.embedMatrix (bOuterZeroNErem decode (peKOut γω) c)).mulVec (ket β)
    := by
  refine (Finset.sum_congr rfl fun z _ ↦
      congrArg _ ?_).trans (sum_z41_sector_gen_refl_2m1 o1 (specKOut γω) hCoin hr0 hScr c)
  unfold noHadMidRefl2m1;
  simp only [Submonoid.coe_mul, ← Matrix.mulVec_mulVec, wNoHad_mulVec_ket o1 hScr c z,
      uStage4ReflRev2m1Ideal_routedKet_eq (specKOut γω) hScr c z]
/-- Pure-unitary `(kExt + kOut)`-coin reversed-order reflected `(2m+1)` `98-T` Stage-4 package. -/
def stage4OuterSubUnitaryPkg_reflRev2m1_98_wstate {kExt kOut w1 : ℕ}
    {wEE : Fin 4 → ℕ} {wNN : Fin 4 → Fin 4 → ℕ} {wEN : Fin 4 → ℕ}
    {wKin : Particle_frozen → ℕ} {wIdle : ℕ}
    {decode : Fin (2 ^ 41) → ZeroNEremSector}
    {peKOut : BitAssignment (kExt + kOut) → PotExpectFn}
    (hk : kExt ≤ 72) (rSub : QRegister kOut 41) (o1 : Stage1ZeroNEremLayout w1 decode)
    (specKOut : ∀ γω : BitAssignment (kExt + kOut), ReflPotSliceSpec (peKOut γω))
    (hCoin : ValidGenZeroNEremCoin wEE wNN wEN wKin wIdle decode) :
    Stage4OuterSubUnitaryPkgWs kExt kOut w1 hk rSub decode o1 peKOut where
  uIdSlice γω := uStage4ReflRev2m1Ideal (specKOut γω)
  uUselSlice γω := uStage4ReflRev2m1_98CatUsel (specKOut γω)
  uCselSlice γω := uStage4ReflRev2m1_98CatCsel (specKOut γω)
  comm_coinExtOut γω M := uStage4ReflRev2m1_98_comm_coinBand7256 (rCoinExtOut hk rSub)
    (val_rCoinExtOut_coinBand7256_wstate hk rSub) (specKOut γω) M
  hCtrlSlice γω := (uStage4ReflRev2m1_98Layout_props (specKOut γω)).1
  hCatSlice γω := (uStage4ReflRev2m1_98Layout_props (specKOut γω)).2.1
  hIdOff γω := (uStage4ReflRev2m1_98Layout_props (specKOut γω)).2.2
  comm_scr γω := ⟨comm_pScr_reflRev2m1_IdPre o1 (specKOut γω),
    comm_pScr_reflRev2m1_98UselPre o1 (specKOut γω),
    comm_pScr_reflRev2m1_98CselPre o1 (specKOut γω)⟩
  hInvolPreScr γω := hInvolPreScr_reflRev2m1_98_wstate o1 (specKOut γω)
  comm_grad3Hi γω M := uStage4ReflRev2m1_98_comm_locGrad3Hi (specKOut γω) M
  sum_z41_slice := sum_z41_slice_reflRev2m1_98_wstate o1 specKOut hCoin

/-- Reversed-order unguarded cat `98-T` `(kExt + kOut)`-coin reflected `SELECT` unitary. -/
def uselReflRevSliceOuterSub2m1_98_wstate {kExt kOut w1 : ℕ} {wEE : Fin 4 → ℕ}
    {wNN : Fin 4 → Fin 4 → ℕ} {wEN : Fin 4 → ℕ} {wKin : Particle_frozen → ℕ} {wIdle : ℕ}
    {decode : Fin (2 ^ 41) → ZeroNEremSector} {peKOut : BitAssignment (kExt + kOut) → PotExpectFn}
    (hk : kExt ≤ 72) (rSub : QRegister kOut 41) (o1 : Stage1ZeroNEremLayout w1 decode)
    (specKOut : ∀ γω : BitAssignment (kExt + kOut), ReflPotSliceSpec (peKOut γω))
    (hCoin : ValidGenZeroNEremCoin wEE wNN wEN wKin wIdle decode) : Unitary (2 ^ dLayout) :=
  uselSliceWState hk rSub o1 (stage4OuterSubUnitaryPkg_reflRev2m1_98_wstate hk rSub o1 specKOut
      hCoin)

/-- Reversed-order controlled cat `98-T` `(kExt + kOut)`-coin reflected `SELECT` unitary. -/
def cselReflRevSliceOuterSub2m1_98_wstate {kExt kOut w1 : ℕ} {wEE : Fin 4 → ℕ}
    {wNN : Fin 4 → Fin 4 → ℕ} {wEN : Fin 4 → ℕ} {wKin : Particle_frozen → ℕ} {wIdle : ℕ}
    {decode : Fin (2 ^ 41) → ZeroNEremSector} {peKOut : BitAssignment (kExt + kOut) → PotExpectFn}
    (hk : kExt ≤ 72) (rSub : QRegister kOut 41) (o1 : Stage1ZeroNEremLayout w1 decode)
    (specKOut : ∀ γω : BitAssignment (kExt + kOut), ReflPotSliceSpec (peKOut γω))
    (hCoin : ValidGenZeroNEremCoin wEE wNN wEN wKin wIdle decode) : Unitary (2 ^ dLayout) :=
    cselSliceWState hk rSub o1 (stage4OuterSubUnitaryPkg_reflRev2m1_98_wstate hk rSub o1 specKOut
    hCoin)
theorem uStage4ReflRevMux2m1_98_eq_pot_mul {kExt kOut w1 : ℕ}
    {wEE : Fin 4 → ℕ} {wNN : Fin 4 → Fin 4 → ℕ} {wEN : Fin 4 → ℕ}
    {wKin : Particle_frozen → ℕ} {wIdle : ℕ}
    {decode : Fin (2 ^ 41) → ZeroNEremSector}
    {peKOut : BitAssignment (kExt + kOut) → PotExpectFn}
    (hk : kExt ≤ 72) (rSub : QRegister kOut 41) (o1 : Stage1ZeroNEremLayout w1 decode)
    (specKOut : ∀ γω : BitAssignment (kExt + kOut), ReflPotSliceSpec (peKOut γω))
    (hCoin : ValidGenZeroNEremCoin wEE wNN wEN wKin wIdle decode) (isCsel : Bool) :
    let s4 := stage4OuterSubUnitaryPkg_reflRev2m1_98_wstate hk rSub o1 specKOut hCoin
    let rC := rCoinExtOut hk rSub
    let hBand := val_rCoinExtOut_coinBand7256_wstate hk rSub
    (if isCsel then uCselMuxWState hk rSub o1 s4 else uUselMuxWState hk rSub o1 s4) =
      uPotReflMuxZeroNErem rC hBand specKOut
      isCsel * (if isCsel then uAlignedKinCat2m1_98CselLayout else uAlignedKinCat2m1_98UselLayout)
          := by
  intro s4 rC hBand
  have hMux (U : Unitary (2 ^ dLayout)) (cU : ∀ M, Commute U.1 (rC.embedMatrix M)) (b : Bool) :
      muxMat_c70 rC (fun γω ↦ uPotReflZeroNErem (specKOut γω) b * U) = muxMat_c70 rC (fun γω ↦
          uPotReflZeroNErem (specKOut γω) b) * U.1 := by
    simp only [muxMat_c70, Finset.sum_mul]
    exact Finset.sum_congr rfl fun γω _ ↦ by
      rw [Submonoid.coe_mul, Matrix.mul_assoc, projBits_eq_embedMatrix_c70 rC γω, (cU _).eq,
        ← projBits_eq_embedMatrix_c70 rC γω, ← Matrix.mul_assoc]
  cases isCsel
  · exact Subtype.ext ((uMuxExtOut_val hk rSub s4.uUselSlice (huUsel_wstate s4)).trans
        (hMux _ (fun M ↦ (uAlignedKin2m1_98_comm_coinBand7256 rC hBand M).2.1) false))
  · exact Subtype.ext ((uMuxExtOut_val hk rSub s4.uCselSlice (huCsel_wstate s4)).trans
        (hMux _ (fun M ↦ (uAlignedKin2m1_98_comm_coinBand7256 rC hBand M).2.2) true))
theorem sSliceWState_reflRev_eq {kExt kOut w1 : ℕ} {wEE : Fin 4 → ℕ} {wNN : Fin 4 → Fin 4 → ℕ}
    {wEN : Fin 4 → ℕ} {wKin : Particle_frozen → ℕ} {wIdle : ℕ}
    {decode : Fin (2 ^ 41) → ZeroNEremSector} {peKOut : BitAssignment (kExt + kOut) →
      PotExpectFn} (hk : kExt ≤ 72) (rSub : QRegister kOut 41)
          (o1 : Stage1ZeroNEremLayout w1 decode)
    (specKOut : ∀ γω : BitAssignment (kExt + kOut), ReflPotSliceSpec (peKOut γω))
        (hCoin : ValidGenZeroNEremCoin wEE wNN wEN wKin wIdle decode) :
    sSliceWState hk rSub o1 (stage4OuterSubUnitaryPkg_reflRev2m1_98_wstate hk rSub o1 specKOut
        hCoin) = sReflSliceOuterSub2m1_wstate hk rSub o1 specKOut hCoin := by
  let s4R := stage4OuterSubUnitaryPkg_reflRev2m1_98_wstate hk rSub o1 specKOut hCoin
  let s4O := stage4OuterSubUnitaryPkg_refl2m1_98_wstate hk rSub o1 specKOut hCoin
  have cScrR (M : Operator (2 ^ kExt)) : Commute (pScrExt kExt hk)
      ((rCoinExt kExt hk).embedMatrix M) :=
    ((rCoinExt kExt hk).embedMatrix_comm_of_disjoint (rScrExt kExt hk)
        (rCoinExt_disj_helpers_c70 hk).2.1 M (compProj 0)).symm
  have hSliceClean (γω : BitAssignment (kExt + kOut)) :
      (preConj (uStage1Clean_c70 decode) (s4R.uIdSlice γω)).1 * pScr =
        (preConj (uStage1Clean_c70 decode) (s4O.uIdSlice γω)).1 * pScr :=
    (preConj_uStage1Clean_c70 o1 _ (s4R.comm_scr γω).1).1.trans
      ((preLoc_reflRev2m1Ideal_mul_pScr o1 (specKOut γω)).trans (preConj_uStage1Clean_c70 o1 _
          (s4O.comm_scr γω).1).1.symm)
  have hOutExt (γ : BitAssignment kExt) :
      (preConj (uStage1Clean_c70 decode) (uMuxOut hk rSub s4R.uIdSlice (huId_wstate s4R) γ)).1 *
          pScrExt kExt hk =
        (preConj (uStage1Clean_c70 decode) (uMuxOut hk rSub s4O.uIdSlice (huId_wstate s4O) γ)).1 *
            pScrExt kExt hk :=
    lift_whole_pScrExt_wstate hk (by
        rw [preConjClean_uMuxOut_eq decode hk rSub (huId_wstate s4R) γ,
          preConjClean_uMuxOut_eq decode hk rSub (huId_wstate s4O) γ, Finset.sum_mul,
              Finset.sum_mul]
        exact Finset.sum_congr rfl fun ω _ ↦ by
          rw [Matrix.mul_assoc, ← (comm_pScr_qOutHad rSub ω).eq, ← Matrix.mul_assoc,
              hSliceClean (concatBitsGen γ ω),
            Matrix.mul_assoc, (comm_pScr_qOutHad rSub ω).eq, ← Matrix.mul_assoc])
      (preConjClean_comm_rCoinExt_c70 decode hk _ (uMuxOut_comm_rCoinExt hk rSub (huId_wstate s4R)
          γ))
      (preConjClean_comm_rCoinExt_c70 decode hk _ (uMuxOut_comm_rCoinExt hk rSub (huId_wstate s4O)
          γ))
  have cHfP : (uHadCoinExt hk).1 * pScrExt kExt hk = pScrExt kExt hk * (uHadCoinExt hk).1 :=
    (uHadCoinExt_eq_embed_c70 hk).1 ▸ (cScrR _).symm.eq
  have hMid : (preConj (uStage1Clean_c70 decode) (uIdMuxWState hk rSub o1 s4R)).1 *
      pScrExt kExt hk =
      (preConj (uStage1Clean_c70 decode) (uIdMuxWState hk rSub o1 s4O)).1 * pScrExt kExt hk := by
    simp only [uIdMuxWState, uMuxExtOut,
        preConjClean_mux_eq_c70 decode hk _ (uMuxOut_comm_projBits_rCoinExt hk rSub (huId_wstate
        s4R)),
      preConjClean_mux_eq_c70 decode hk _ (uMuxOut_comm_projBits_rCoinExt hk rSub (huId_wstate
          s4O)), Finset.sum_mul]
    refine Finset.sum_congr rfl fun γ _ ↦ ?_
    have cProjP : projBits_c70 (rCoinExt kExt hk) γ * pScrExt kExt hk = pScrExt kExt hk *
        projBits_c70 (rCoinExt kExt hk) γ :=
      projBits_eq_embedMatrix_c70 (rCoinExt kExt hk) γ ▸ (cScrR _).symm.eq
    rw [Matrix.mul_assoc, cProjP, ← Matrix.mul_assoc, hOutExt γ, Matrix.mul_assoc, ← cProjP,
        ← Matrix.mul_assoc]
  refine Subtype.ext (show (sSliceWState hk rSub o1 s4R).1 = (sSliceWState hk rSub o1 s4O).1 by
    simp only [sSliceWState, unitaryOnProj, uPreExt, Submonoid.coe_mul, Matrix.mul_assoc]
    rw [cHfP, ← Matrix.mul_assoc _ (pScrExt kExt hk), hMid, Matrix.mul_assoc _ (pScrExt kExt hk),
        ← cHfP])
attribute [local irreducible] sSliceWState cselSliceWState uselSliceWState
  sReflSliceOuterSub2m1_wstate stage4OuterSubUnitaryPkg_reflRev2m1_98_wstate
  cat8SharedProjCompactGen

theorem comm_locGrad3Hi_reflRevOuterSub2m1_98_wstate {kExt kOut w1 : ℕ} {wEE : Fin 4 → ℕ}
    {wNN : Fin 4 → Fin 4 → ℕ} {wEN : Fin 4 → ℕ} {wKin : Particle_frozen → ℕ} {wIdle : ℕ}
    {decode : Fin (2 ^ 41) → ZeroNEremSector} {peKOut : BitAssignment (kExt + kOut) → PotExpectFn}
    (hk : kExt ≤ 72) (rSub : QRegister kOut 41) (o1 : Stage1ZeroNEremLayout w1 decode)
    (specKOut : ∀ γω : BitAssignment (kExt + kOut), ReflPotSliceSpec (peKOut γω))
    (hCoin : ValidGenZeroNEremCoin wEE wNN wEN wKin wIdle decode) (M : Operator (2 ^ 3)) :
    Commute (uselReflRevSliceOuterSub2m1_98_wstate hk rSub o1 specKOut hCoin).1
    ((locGrad3HiCompactGen scrWLayout).embedMatrix M) ∧
    Commute (cselReflRevSliceOuterSub2m1_98_wstate hk rSub o1 specKOut hCoin).1
    ((locGrad3HiCompactGen scrWLayout).embedMatrix M)
    := by unfold uselReflRevSliceOuterSub2m1_98_wstate cselReflRevSliceOuterSub2m1_98_wstate; exact
            comm_locGrad3Hi_outerSubUnitary_wstate hk rSub o1
            (stage4OuterSubUnitaryPkg_reflRev2m1_98_wstate hk rSub o1 specKOut hCoin) M
end
end
noncomputable section
set_option maxRecDepth 4096
open scoped ComplexOrder MatrixOrder Circuit.Notation
open Operator QProg Matrix HermitianMat Circuit Qubit PrimitiveGate QuantumComputation.Specs
  PhotochemistrySolution PhotochemistrySolution.XMeasUnld PhotochemistrySolution.SplitRouter47_187
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
open PhotochemistrySolution.HalfBellCollapse
open _root_.DynamicCircuit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt hiding bit_cases
  eval_seq_mulVec ket ket_CNOT ket_TOFF ket_X ket_projector_one ket_projector_zero matrix_ext_ket
  qAssign_obs_map_val
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB hiding bitSign eval_seq_mulVec ket
  ket_CNOT ket_TOFF ket_X matrix_ext_ket writeReg writeReg_apply_of_not_mem
open _root_.QuantumComputation.Specs.PhotochemistrySolution.QubitizationWalkSem hiding bitSign
  bitSign_add bitSign_mul_self ket_H_apply sqrtHalf sqrtHalf_mul_sqrtHalf star_sqrtHalf
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SplitRouterSeqBell26k hiding ket
  matrix_ext_ket
open _root_.QuantumComputation.Specs.PhotochemistrySolution.PortBDualBellUnld (HCNOTSupportedIn
    hcnotSupportedIn_fixedBellVec)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.PortBStage5Merged (topPlaneFin
    fixedFanoutBits fixedFanoutBits_of_ne_tgt fixedFanoutCirc_mulVec_ket fixedFanoutBits_zero_src
    fixedBell1Circ_mulVec_ket_zero hcnotSupportedIn_mono hcnotSupportedIn_fixedBell1)
local instance (priority := 100000) {k : ℕ} : NeZero (2 ^ k) := ⟨pow_ne_zero k two_ne_zero⟩
attribute [local semireducible] DynamicCircuit.identity Circuit.H Circuit.X
attribute [local irreducible] systemQubits_frozen
theorem hne_bufLo_hA_wstate {M D n : ℕ} (r : RouterReg M D n) (b : Fin 24) : rBufLo r b ≠ rHA r b :=
  rr_ne r (by have := b.isLt; dsimp [rBufLo, rHA]; omega)

theorem fixedBell1_comm_fixedFanout_sameSys_wstate {M n : ℕ} (qA qB : Wire n)
    (cLo cHi : Fin M → ZMod 2) (wS : Fin M → Wire n)
    (hAS : ∀ p, qA ≠ wS p) (hBS : ∀ p, qB ≠ wS p) (hAB : qA ≠ qB)
        (hInjS : ∀ p₁ p₂ : Fin M, p₁ ≠ p₂ → wS p₁ ≠ wS p₂) :
    (fixedBell1Circ M qA cLo wS hAS).eval.1 * (fixedFanoutCirc M qB cHi wS hBS).eval.1 =
      (fixedFanoutCirc M qB cHi wS hBS).eval.1 * (fixedBell1Circ M qA cLo wS hAS).eval.1 := by
  have cHFan :=
      (HCNOTSupportedIn.comm (hcnotSupportedIn_fixedFanout1 (S := fun w ↦ w = qB ∨ ∃ p, w =
      wS p) qB cHi wS hBS (Or.inl rfl) (fun p _ ↦ Or.inr ⟨p, rfl⟩))
    (HCNOTSupportedIn.h (S := fun w ↦ w = qA) rfl) fun _ hw heq ↦
        hw.elim (fun h0 ↦ hAB (heq.symm.trans h0)) fun ⟨p, hp⟩ ↦ hAS p (heq.symm.trans hp)).symm
  have cFF : (fixedFanoutCirc M qA cLo wS hAS).eval.1 * (fixedFanoutCirc M qB cHi wS hBS).eval.1 =
    (fixedFanoutCirc M qB cHi wS hBS).eval.1 * (fixedFanoutCirc M qA cLo wS hAS).eval.1 :=
        matrix_ext_ket fun δ ↦ by
    simp only [← Matrix.mulVec_mulVec, fixedFanoutCirc_mulVec_ket,
        fixedFanoutBits_of_ne_tgt M _ _ wS δ qA hAS, fixedFanoutBits_of_ne_tgt M _ _ wS δ qB hBS]
    refine (DynCircExt.bit_cases (δ qA)).elim (fun h ↦
        by simp [h, fixedFanoutBits_zero_src]) fun ha1 ↦
      (DynCircExt.bit_cases (δ qB)).elim (fun h ↦
          by simp [h, fixedFanoutBits_zero_src]) fun hb1 ↦ ?_
    rw [ha1, hb1, HalfBellCollapse.fixedFanoutBits_comm cLo cHi wS hInjS δ]
  dsimp only [fixedBell1Circ]
  rw [Circuit.eval_seq, Submonoid.coe_mul, Matrix.mul_assoc, cHFan, ← Matrix.mul_assoc, cFF,
      Matrix.mul_assoc]
theorem fixedBellVec_comm_fixedFanoutVec_sameSys_wstate {M D n : ℕ} (r : RouterReg M D n)
    (cLo cHi : Fin M → ZMod 2) :
    (fixedBellVecCirc M 24 (rHA r) cLo (fun b p ↦ rSys r p b) (hne_hA_sys r)).eval.1 *
        (fixedFanoutVecCirc M 24 (rBufHi r) cHi (fun b p ↦
      rSys r p b) (hne_bufHi_sys r)).eval.1 =
      (fixedFanoutVecCirc M 24 (rBufHi r) cHi (fun b p ↦
        rSys r p b) (hne_bufHi_sys r)).eval.1 * (fixedBellVecCirc M 24 (rHA r) cLo (fun b p ↦
            rSys r p b) (hne_hA_sys r)).eval.1 := by
  let sub (k : ℕ) (hk : k ≤ 24) (j : Fin k) : Fin 24 := ⟨j.val, Nat.lt_of_lt_of_le j.isLt hk⟩
  let bv (k : ℕ) (hk : k ≤ 24) := fixedBellVecCirc M k (fun j ↦ rHA r (sub k hk j)) cLo
    (fun j p ↦ rSys r p (sub k hk j)) (fun j p ↦ hne_hA_sys r (sub k hk j) p)
  let fv (k : ℕ) (hk : k ≤ 24) := fixedFanoutVecCirc M k (fun j ↦ rBufHi r (sub k hk j)) cHi
    (fun j p ↦ rSys r p (sub k hk j)) (fun j p ↦ hne_bufHi_sys r (sub k hk j) p)
  have hBV24 : bv 24 (Nat.le_refl 24) = fixedBellVecCirc M 24 (rHA r) cLo (fun b p ↦ rSys r p b)
      (hne_hA_sys r) := rfl
  have hFV24 : fv 24 (Nat.le_refl 24) = fixedFanoutVecCirc M 24 (rBufHi r) cHi (fun b p ↦
      rSys r p b) (hne_bufHi_sys r) := rfl
  rw [← hBV24, ← hFV24]
  suffices h0 : ∀ (k : ℕ) (hk : k ≤ 24), (bv k hk).eval.1 * (fv k hk).eval.1 = (fv k hk).eval.1 *
      (bv k hk).eval.1 from
    h0 24 (Nat.le_refl 24)
  intro k
  induction k with
  | zero => exact fun _ ↦ rfl
  | succ k ih =>
      intro hk
      let hk' := Nat.le_of_succ_le hk
      let b : Fin 24 := ⟨k, hk⟩
      let B_pre := bv k hk'
      let F_pre := fv k hk'
      let B_b := fixedBell1Circ M (rHA r b) cLo (fun p ↦ rSys r p b) (hne_hA_sys r b)
      let F_b := fixedFanoutCirc M (rBufHi r b) cHi (fun p ↦ rSys r p b) (hne_bufHi_sys r b)
      have hDisj := routerPlaneSet_disj r (P₁ := fun d ↦ d.val < k) (P₂ := fun d ↦ d = b)
        fun d hd e ↦ absurd (congrArg Fin.val e) (Nat.ne_of_lt hd)
      have cPreFb : B_pre.eval.1 * F_b.eval.1 = F_b.eval.1 * B_pre.eval.1 := HCNOTSupportedIn.comm
        (hcnotSupportedIn_fixedBellVec cLo k _ _ _ (fun j ↦ ⟨sub k hk' j, j.isLt, Or.inl rfl⟩)
          fun j p _ ↦ ⟨sub k hk' j, j.isLt, Or.inr (Or.inr (Or.inr ⟨p, rfl⟩))⟩)
        (hcnotSupportedIn_fixedFanout1 _ cHi _ _ ⟨b, rfl, Or.inr (Or.inr (Or.inl rfl))⟩
          fun p _ ↦ ⟨b, rfl, Or.inr (Or.inr (Or.inr ⟨p, rfl⟩))⟩) hDisj
      have cBbFpre : B_b.eval.1 * F_pre.eval.1 = F_pre.eval.1 * B_b.eval.1 := (HCNOTSupportedIn.comm
        (hcnotSupportedIn_fixedFanoutVec k _ cHi _ _ (fun j ↦ ⟨sub k hk' j, j.isLt,
            Or.inr (Or.inr (Or.inl rfl))⟩)
          fun j p _ ↦ ⟨sub k hk' j, j.isLt, Or.inr (Or.inr (Or.inr ⟨p, rfl⟩))⟩)
        (hcnotSupportedIn_fixedBell1 _ cLo _ _ ⟨b, rfl, Or.inl rfl⟩
          fun p ↦ ⟨b, rfl, Or.inr (Or.inr (Or.inr ⟨p, rfl⟩))⟩) hDisj).symm
      have cSame :=
          fixedBell1_comm_fixedFanout_sameSys_wstate (rHA r b)
          (rBufHi r b) cLo cHi (fun p ↦ rSys r p b)
        (hne_hA_sys r b) (hne_bufHi_sys r b) (HalfBellCollapse.hne_bufHi_hA r b).symm fun _ _ hp ↦
            hne_sys_inj r b hp
      change (B_b.eval.1 * B_pre.eval.1) * (F_b.eval.1 * F_pre.eval.1) =
        (F_b.eval.1 * F_pre.eval.1) * (B_b.eval.1 * B_pre.eval.1)
      calc (B_b.eval.1 * B_pre.eval.1) * (F_b.eval.1 * F_pre.eval.1)
          = B_b.eval.1 * (B_pre.eval.1 * F_b.eval.1) * F_pre.eval.1 := by
            simp only [Matrix.mul_assoc]
        _ = (B_b.eval.1 * F_b.eval.1) * (B_pre.eval.1 * F_pre.eval.1) := by
            rw [cPreFb, ← Matrix.mul_assoc B_b.eval.1, Matrix.mul_assoc (B_b.eval.1 * F_b.eval.1)]
        _ = F_b.eval.1 * (B_b.eval.1 * F_pre.eval.1) * B_pre.eval.1 := by
            rw [cSame, ih hk', Matrix.mul_assoc F_b.eval.1, ← Matrix.mul_assoc B_b.eval.1,
                ← Matrix.mul_assoc F_b.eval.1]
        _ = (F_b.eval.1 * F_pre.eval.1) * (B_b.eval.1 * B_pre.eval.1) := by
            rw [cBbFpre, ← Matrix.mul_assoc F_b.eval.1, Matrix.mul_assoc (F_b.eval.1 *
                F_pre.eval.1)]
/--
Plane-scoped router wires `{rHA r d, rBufLo r d, rBufHi r d, rSys r _ d}` restricted to `P d` .
-/
def RouterPlaneSetLo {M D n : ℕ} (r : RouterReg M D n) (P : Fin 24 → Prop) (w : Wire n) : Prop :=
    ∃ d : Fin 24, P d ∧ (w = rHA r d ∨ w = rBufLo r d ∨ w = rBufHi r d ∨ ∃ p : Fin M, w =
    rSys r p d)
theorem routerPlaneSetLo_disj {M D n : ℕ} (r : RouterReg M D n) {P₁ P₂ : Fin 24 → Prop}
    (hDisjP : ∀ d, P₁ d → ¬ P₂ d) : ∀ w : Wire n, RouterPlaneSetLo r P₁ w →
    ¬ RouterPlaneSetLo r P₂ w := by
  rintro w ⟨d₁, hp₁, hw₁⟩ ⟨d₂, hp₂, hw₂⟩
  have hneD : d₁.val ≠ d₂.val := fun e ↦ hDisjP d₁ hp₁ (Fin.ext e ▸ hp₂)
  have _ := d₁.isLt; have _ := d₂.isLt
  rcases hw₁ with rfl | rfl | rfl | ⟨p₁, rfl⟩ <;>
    rcases hw₂ with h | h | h | ⟨p₂, h⟩
  all_goals exact rr_ne r (by dsimp at *; omega) h

/-- Collapsed `rBufLo` fanout suffix on planes `24 - m .. 23` in increasing plane order. -/
def cCopyLoTop {M D n : ℕ} (r : RouterReg M D n) (cLo : Fin M → ZMod 2) :
    (m : ℕ) → m ≤ 24 → Circuit n
  | 0, _ => .identity
  | m + 1, hm =>
      let b := topPlaneFin m hm
      fixedFanoutCirc M (rBufLo r b) cLo (fun p ↦ rSys r p b) ((hne_fixed_router r).1 b) ;;ᶜ
      cCopyLoTop r cLo m (Nat.le_of_succ_le hm)

/-- Prefix accumulator on planes `0 .. k - 1` for `cCopyLoTop` associativity. -/
def cCopyLoPre {M D n : ℕ} (r : RouterReg M D n) (cLo : Fin M → ZMod 2) :
    (k : ℕ) → k ≤ 24 → Circuit n
  | 0, _ => .identity
  | k + 1, hk =>
      cCopyLoPre r cLo k (Nat.le_of_succ_le hk) ;;ᶜ
      fixedFanoutCirc M (rBufLo r ⟨k, hk⟩) cLo (fun p ↦ rSys r p ⟨k, hk⟩)
        ((hne_fixed_router r).1 ⟨k, hk⟩)

theorem eval_cCopyLoTop_24 {M D n : ℕ} (r : RouterReg M D n) (cLo : Fin M → ZMod 2) :
    (cCopyLoTop r cLo 24 (Nat.le_refl 24)).eval.1 =
    (fixedFanoutVecCirc M 24 (rBufLo r) cLo (fun b p ↦ rSys r p b)
    (hne_fixed_router r).1).eval.1 := by
  have hPreCon : ∀ {k₁ k₂ : ℕ} (e : k₁ = k₂) (h₁ : k₁ ≤ 24) (h₂ : k₂ ≤ 24),
      (cCopyLoPre r cLo k₁ h₁).eval.1 = (cCopyLoPre r cLo k₂ h₂).eval.1
    | _, _, rfl, _, _ => rfl
  have hPre24 : (cCopyLoPre r cLo 24 (Nat.le_refl 24)).eval.1 =
      (fixedFanoutVecCirc M 24 (rBufLo r) cLo (fun b p ↦ rSys r p b)
          (hne_fixed_router r).1).eval.1 := by
    suffices hp : ∀ (k : ℕ) (hk : k ≤ 24), (cCopyLoPre r cLo k hk).eval.1 =
        (fixedFanoutVecCirc M k (fun j : Fin k ↦ rBufLo r ⟨j.val, Nat.lt_of_lt_of_le j.isLt hk⟩) cLo
          (fun j p ↦ rSys r p ⟨j.val, Nat.lt_of_lt_of_le j.isLt hk⟩)
          (fun j p ↦ (hne_fixed_router r).1 ⟨j.val,
              Nat.lt_of_lt_of_le j.isLt hk⟩ p)).eval.1 from hp 24 le_rfl
    intro k
    induction k with
    | zero => exact fun _ ↦ rfl
    | succ k ih =>
        exact fun hk ↦ by
          simp [cCopyLoPre, fixedFanoutVecCirc, Circuit.eval_seq, ih (Nat.le_of_succ_le hk)]
  have hInv : ∀ (m : ℕ) (hm : m ≤ 24), (cCopyLoTop r cLo m hm).eval.1 *
      (cCopyLoPre r cLo (24 - m) (Nat.sub_le 24 m)).eval.1 =
          (cCopyLoPre r cLo 24 (Nat.le_refl 24)).eval.1 := by
    intro m
    induction m with
    | zero => exact fun _ ↦ by simp [cCopyLoTop, Circuit.eval_identity]
    | succ m ihm =>
        intro hm
        rw [← ihm (Nat.le_of_succ_le hm), hPreCon (show 24 - m = (23 - m) + 1 by omega)
            (Nat.sub_le 24 m) (by omega)]
        simp only [cCopyLoTop, cCopyLoPre, Circuit.eval_seq, Submonoid.coe_mul, Matrix.mul_assoc,
          hPreCon (show 23 - m = 24 - (m + 1) by omega) _ (Nat.sub_le 24 (m + 1))]
        rfl
  simpa only [Nat.sub_self, cCopyLoPre, Circuit.eval_identity, Submonoid.coe_one,
      Matrix.mul_one] using
    (hInv 24 le_rfl).trans hPre24
/--
Classical-control overlay after collapsing both `rHB r` and `rHA r`:
`fixedFanoutVecCirc` on `(rBufHi r, rSys r)` followed by `fixedFanoutVecCirc` on
`(rBufLo r, rSys r)` .
-/
def cFixedCopyLoHiCirc {M D n : ℕ} (r : RouterReg M D n) (cLo cHi : Fin M → ZMod 2) : Circuit n :=
  fixedFanoutVecCirc M 24 (rBufHi r) cHi (fun b p ↦ rSys r p b) (hne_bufHi_sys r) ;;ᶜ
  fixedFanoutVecCirc M 24 (rBufLo r) cLo (fun b p ↦ rSys r p b) (hne_fixed_router r).1
def cHACollapseStage {M D n : ℕ} (r : RouterReg M D n) (cLo cHi : Fin M → ZMod 2) (m : ℕ)
    (hm : m ≤ 24) : Circuit n :=
  fixedFanoutVecCirc M 24 (rBufHi r) cHi (fun b p ↦ rSys r p b) (hne_bufHi_sys r) ;;ᶜ
  cCopyLoTop r cLo m hm ;;ᶜ
  cBellLoBelow r cLo (24 - m) (Nat.sub_le 24 m)

theorem hcnotSupportedIn_cBellLoBelow_lo {M D n : ℕ} (r : RouterReg M D n)
    (cLo : Fin M → ZMod 2) :
    ∀ (k : ℕ) (hk : k ≤ 24),
      HCNOTSupportedIn (RouterPlaneSetLo r (fun d ↦ d.val < k)) (cBellLoBelow r cLo k hk)
  | 0, _ => .id
  | k + 1, hk =>
      .seq (hcnotSupportedIn_mono (fun _ ⟨d, hd, hw⟩ ↦ ⟨d, by omega, hw⟩)
          (hcnotSupportedIn_cBellLoBelow_lo r cLo k (Nat.le_of_succ_le hk)))
        (hcnotSupportedIn_fixedBell1 _ _ _ _ ⟨⟨k, hk⟩, Nat.lt_succ_self k, Or.inl rfl⟩ fun p ↦
            ⟨⟨k, hk⟩, Nat.lt_succ_self k, Or.inr (Or.inr (Or.inr ⟨p, rfl⟩))⟩)
theorem hcnotSupportedIn_cCopyLoTop_lo {M D n : ℕ} (r : RouterReg M D n)
    (cLo : Fin M → ZMod 2) :
    ∀ (m : ℕ) (hm : m ≤ 24),
      HCNOTSupportedIn (RouterPlaneSetLo r (fun d ↦ 24 - m ≤ d.val)) (cCopyLoTop r cLo m hm)
  | 0, _ => .id
  | m + 1, hm =>
      let b := topPlaneFin m hm
      have hbGe : 24 - (m + 1) ≤ b.val := by
        dsimp [b, topPlaneFin]
        omega
      .seq (hcnotSupportedIn_fixedFanout1 _ _ _ _ ⟨b, hbGe, Or.inr (Or.inl rfl)⟩ fun p _ ↦
          ⟨b, hbGe, Or.inr (Or.inr (Or.inr ⟨p, rfl⟩))⟩)
        (hcnotSupportedIn_mono (fun _ ⟨d, hd, hw⟩ ↦ ⟨d, by omega, hw⟩)
            (hcnotSupportedIn_cCopyLoTop_lo r cLo m (Nat.le_of_succ_le hm)))
theorem cHACollapseStage_factor_plane {M D n : ℕ} (r : RouterReg M D n)
    (cLo cHi : Fin M → ZMod 2) (m : ℕ) (hm : m + 1 ≤ 24) :
    let b := topPlaneFin m hm
    let k := 23 - m
    let hkLe : k ≤ 24 := by omega
    let hmLe : m ≤ 24 := Nat.le_of_succ_le hm
    let Lo_b := fixedBell1Circ M (rHA r b) cLo (fun p ↦ rSys r p b) (hne_hA_sys r b)
    let CopyLo_b :=
        fixedFanoutCirc M (rBufLo r b) cLo (fun p ↦ rSys r p b) ((hne_fixed_router r).1 b)
    let cRest :=
        fixedFanoutVecCirc M 24 (rBufHi r) cHi (fun d p ↦ rSys r p d)
        (hne_bufHi_sys r) ;;ᶜ cCopyLoTop r cLo m hmLe ;;ᶜ cBellLoBelow r cLo k hkLe
    HCNOTSupportedIn (fun w ↦ (∃ d : Fin 24, w = rBufHi r d ∨ ∃ p : Fin M, w = rSys r p d) ∨
        RouterPlaneSetLo r (fun d ↦ d ≠ b) w) cRest ∧
    (cHACollapseStage r cLo cHi m hmLe).eval.1 = Lo_b.eval.1 * cRest.eval.1 ∧
    (cHACollapseStage r cLo cHi (m + 1) hm).eval.1 = CopyLo_b.eval.1 * cRest.eval.1 := by
  intro b k hkLe hmLe Lo_b CopyLo_b cRest
  have hk1 : k + 1 ≤ 24 := by omega
  have hbEq : (⟨k, hk1⟩ : Fin 24) = b := rfl
  have hLoBelowS : HCNOTSupportedIn (RouterPlaneSetLo r (· ≠ b)) (cBellLoBelow r cLo k hkLe) :=
    hcnotSupportedIn_mono (fun _ ⟨d, hd, hw⟩ ↦ ⟨d, fun e ↦ Nat.ne_of_lt hd
      (congrArg Fin.val e), hw⟩) (hcnotSupportedIn_cBellLoBelow_lo r cLo k hkLe)
  have hCopyTopS : HCNOTSupportedIn (RouterPlaneSetLo r (· ≠ b)) (cCopyLoTop r cLo m hmLe) :=
    hcnotSupportedIn_mono (fun _ ⟨d, hd, hw⟩ ↦ ⟨d, fun e ↦ by
      have hv := congrArg Fin.val e
      dsimp [b, topPlaneFin] at hv hd
      omega, hw⟩) (hcnotSupportedIn_cCopyLoTop_lo r cLo m hmLe)
  have hcCopyLo_b : HCNOTSupportedIn (RouterPlaneSetLo r (· = b)) CopyLo_b :=
    hcnotSupportedIn_fixedFanout1 _ _ _ _ ⟨b, rfl, Or.inr (Or.inl rfl)⟩
      fun p _ ↦ ⟨b, rfl, Or.inr (Or.inr (Or.inr ⟨p, rfl⟩))⟩
  have hDisjB := routerPlaneSetLo_disj r (P₁ := (· ≠ b)) (P₂ := (· = b)) fun _ hne heq ↦ hne heq
  have cCopyTopCopyB := HCNOTSupportedIn.comm hCopyTopS hcCopyLo_b hDisjB
  have cBelowCopyB := HCNOTSupportedIn.comm hLoBelowS hcCopyLo_b hDisjB
  refine ⟨.seq (hcnotSupportedIn_fixedFanoutVec 24 (rBufHi r) cHi _ _
        (fun d ↦ Or.inl ⟨d, Or.inl rfl⟩) fun d p _ ↦ Or.inl ⟨d, Or.inr ⟨p, rfl⟩⟩)
      (.seq (hcnotSupportedIn_mono (fun _ ↦ Or.inr) hCopyTopS)
          (hcnotSupportedIn_mono (fun _ ↦ Or.inr) hLoBelowS)), ?_, ?_⟩
  · simp only [cHACollapseStage, cRest, Lo_b, b, k, Circuit.eval_seq, Submonoid.coe_mul,
      eval_cBellLoBelow_congr r cLo (show 24 - m = k + 1 by omega) _ hk1, cBellLoBelow, hbEq,
          Matrix.mul_assoc]
  · dsimp only [CopyLo_b, b, k] at cCopyTopCopyB cBelowCopyB
    simp only [cHACollapseStage, cCopyLoTop, cRest, CopyLo_b, b, k, Circuit.eval_seq,
        Submonoid.coe_mul,
      eval_cBellLoBelow_congr r cLo (by omega : 24 - (m + 1) = 23 - m) _ hkLe, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (cCopyLoTop r cLo m hmLe).eval.1, cCopyTopCopyB, Matrix.mul_assoc,
      ← Matrix.mul_assoc (cBellLoBelow r cLo (23 - m) hkLe).eval.1, cBelowCopyB, Matrix.mul_assoc]
def pHACollapseDirectTopDyn {Var : Type} {M D n : ℕ}
    (v : Var) (r : RouterReg M D n) (wCtrl : Fin M → Wire n)
    (hct : ∀ (b : Fin 24) (p : Fin M), wCtrl p ≠ rSys r p b) :
    (m : ℕ) → m ≤ 24 → DynamicCircuit Var n
  | 0, _ => .circuit .identity
  | m + 1, hm =>
      let b := topPlaneFin m hm
      .seq
        (.seq (pHACollapseDirectTopDyn v r wCtrl hct m (Nat.le_of_succ_le hm))
          (.circuit (Circuit.CNOT (rBufLo r b) (rHA r b) (hne_bufLo_hA_wstate r b))))
        (zResetFixupDyn v (rHA r b)
          (cnotFanoutCirc M wCtrl (fun p ↦ rSys r p b) (hct b)))

/--
Complete 24-plane `0-T` direct `cLo`-controlled `rHA` Z-collapse `pHACollapseDirect24Dyn`:
collapses `(uBellLoCopyHiConj r).1 * R_in` into `uCopyLoHiMat r * R_in` when `wCtrl` holds
`routerCtrlLo r`, freeing `rHA r` (`24` wires) to `|0⟩^{24}`.
-/
def pHACollapseDirect24Dyn {Var : Type} {M D n : ℕ} (v : Var) (r : RouterReg M D n)
    (wCtrl : Fin M → Wire n) (hct : ∀ (b : Fin 24) (p : Fin M), wCtrl p ≠ rSys r p b) :
    DynamicCircuit Var n := pHACollapseDirectTopDyn v r wCtrl hct 24 (Nat.le_refl 24)
theorem count_pHACollapseDirect24Dyn {Var : Type} {M D n : ℕ} (v : Var) (r : RouterReg M D n)
    (wCtrl : Fin M → Wire n) (hct : ∀ (b : Fin 24) (p : Fin M), wCtrl p ≠ rSys r p b) :
    (pHACollapseDirect24Dyn v r wCtrl hct).count .T = 0 ∧
    (pHACollapseDirect24Dyn v r wCtrl hct).count .TOFF = 0 := by
  suffices h : ∀ (m : ℕ) (hm : m ≤ 24), (pHACollapseDirectTopDyn v r wCtrl hct m hm).count .T = 0 ∧
      (pHACollapseDirectTopDyn v r wCtrl hct m hm).count .TOFF = 0 from h 24 le_rfl
  intro m
  induction m with
  | zero => exact fun _ ↦ ⟨rfl, rfl⟩
  | succ m ihm =>
      exact fun hm ↦
        ⟨by simp [pHACollapseDirectTopDyn, DynamicCircuit.count, Circuit.CNOT,
              (ihm (Nat.le_of_succ_le hm)).1, count_cnotFanoutCirc_t],
         by simp [pHACollapseDirectTopDyn, DynamicCircuit.count, Circuit.CNOT,
              (ihm (Nat.le_of_succ_le hm)).2, count_cnotFanoutCirc_toff]⟩

theorem dynWires_pHACollapseDirect24Dyn {Var : Type} {M D n : ℕ} {S : Wire n → Prop} (v : Var)
    (r : RouterReg M D n) (wCtrl : Fin M → Wire n) (hct : ∀ (b : Fin 24) (p : Fin M), wCtrl p ≠
    rSys r p b) (hBuf : ∀ b : Fin 24, S (rBufLo r b)) (hHA : ∀ b : Fin 24, S (rHA r b))
    (hCtrl : ∀ p : Fin M, S (wCtrl p)) (hSys : ∀ (b : Fin 24) (p : Fin M), S (rSys r p b)) :
    DynWires S (pHACollapseDirect24Dyn v r wCtrl hct) := by
  have cwCnot {c t : Wire n} {h : c ≠ t} (hc : S c) (ht : S t) : CircWires S (Circuit.CNOT c t h) :=
    fun i ↦ Fin.cases hc (Fin.cases ht fun k ↦ k.elim0) i
  have hCF : ∀ (K : ℕ) (wc wt : Fin K → Wire n) (h : ∀ p, wc p ≠ wt p),
      (∀ p, S (wc p)) → (∀ p, S (wt p)) → CircWires S (cnotFanoutCirc K wc wt h) := by
    intro K
    induction K with
    | zero => exact fun _ _ _ _ _ ↦ trivial
    | succ K ih => exact fun _ _ _ hc ht ↦
          ⟨ih _ _ _ (fun p ↦ hc p.castSucc) (fun p ↦ ht p.castSucc), cwCnot (hc _) (ht _)⟩
  suffices h : ∀ (m : ℕ)
      (hm : m ≤ 24), DynWires S (pHACollapseDirectTopDyn v r wCtrl hct m hm) from h 24 le_rfl
  intro m
  induction m with
  | zero => exact fun _ ↦ trivial
  | succ m ihm =>
      exact fun hm ↦ ⟨⟨ihm (Nat.le_of_succ_le hm), cwCnot (hBuf _) (hHA _)⟩,
        ⟨fun _ ↦ hHA _, ⟨⟨fun _ ↦ hHA _, hCF M wCtrl _ (hct _) hCtrl (hSys _)⟩, trivial⟩⟩⟩

theorem haCollapseDirect1_kraus_ket {M D n : ℕ}
    (r : RouterReg M D n) (wCtrl : Fin M → Wire n)
    (hct : ∀ (b : Fin 24) (p : Fin M), wCtrl p ≠ rSys r p b)
    (hDisjCS : ∀ (b : Fin 24) (p q : Fin M), wCtrl p ≠ rSys r q b)
    (b : Fin 24) (cLo : Fin M → ZMod 2)
    {α : BitAssignment n}
    (hQH : α (rHA r b) = 0)
    (hCtrl : ∀ p : Fin M, α (wCtrl p) = cLo p) :
    let qB := rBufLo r b; let qH := rHA r b
    let wS : Fin M → Wire n := fun p ↦ rSys r p b
    let Lo := (fixedBell1Circ M qH cLo wS (hne_hA_sys r b)).eval.1;
    let CopyLo := (fixedFanoutCirc M qB cLo wS ((hne_fixed_router r).1 b)).eval.1;
    let cBH := (Circuit.CNOT qB qH (hne_bufLo_hA_wstate r b)).eval.1;
    let cFix := (cnotFanoutCirc M wCtrl wS (hct b)).eval.1;
    let P₀ := (QRegister.singleton qH).basisOutcomeProjector 0;
    let P₁ := (QRegister.singleton qH).basisOutcomeProjector 1
    (P₀ * cBH).mulVec (Lo.mulVec (ket α)) = sqrtHalf • (CopyLo.mulVec (ket α)) ∧
    (cFix * (Circuit.X qH).eval.1 * P₁ * cBH).mulVec (Lo.mulVec (ket α)) =
      sqrtHalf • (CopyLo.mulVec (ket α)) := by
  intro qB qH wS Lo CopyLo cBH cFix P₀ P₁; have hBH : qB ≠ qH := hne_bufLo_hA_wstate r b;
  let α1 := fixedFanoutBits M 1 cLo wS α; have hQH' : α qH = 0 := hQH;
  have hα1_qB : α1 qB = α qB :=
      fixedFanoutBits_of_ne_tgt M 1 cLo wS α qB ((hne_fixed_router r).1 b);
      have hα1_qH : α1 qH = 0 :=
      (fixedFanoutBits_of_ne_tgt M 1 cLo wS α qH (hne_hA_sys r b)).trans hQH'
  have hα1_wC : ∀ p : Fin M, α1 (wCtrl p) = cLo p := fun p ↦
      (fixedFanoutBits_of_ne_tgt M 1 cLo wS α (wCtrl p) (hDisjCS b p)).trans (hCtrl p)
  have hLo : Lo.mulVec (ket α) = sqrtHalf • (ket α + ket (Function.update α1 qH 1)) :=
      fixedBell1Circ_mulVec_ket_zero M qH cLo wS (hne_hA_sys r b) hQH';
      have hCopy : CopyLo.mulVec (ket α) = ket (fixedFanoutBits M (α qB) cLo wS α) :=
      fixedFanoutCirc_mulVec_ket M qB cLo wS ((hne_fixed_router r).1 b) α;
      have h11 : (1 : ZMod 2) + 1 = 0 :=
      rfl; have hu_α_qH : Function.update α qH 0 = α :=
             hQH' ▸ Function.update_eq_self qH α; have hu_α1_qH : Function.update α1 qH 0 = α1 :=
                                                    hα1_qH ▸ Function.update_eq_self qH α1
  have hInjS : ∀ p₁ p₂ : Fin M, p₁ ≠ p₂ → wS p₁ ≠ wS p₂ := fun _ _ hp ↦ hne_sys_inj r b hp
  rw [hLo, hCopy]
  rcases DynCircExt.bit_cases (α qB) with hb0 | hb1
  · rw [hb0, fixedFanoutBits_zero_src]; constructor
    · simp only [P₀, cBH, ← Matrix.mulVec_mulVec, Matrix.mulVec_smul, Matrix.mulVec_add, ket_CNOT,
          ket_projector_zero, Function.update_of_ne hBH, hQH', hb0, hα1_qB, add_zero, hu_α_qH,
          Function.update_self, Function.update_idem, ↓reduceIte, one_ne_zero]
    · simp only [P₁, cBH, cFix, ← Matrix.mulVec_mulVec, Matrix.mulVec_smul, Matrix.mulVec_add,
          Matrix.mulVec_zero, ket_CNOT, ket_projector_one, Function.update_of_ne hBH, hQH', hb0,
          hα1_qB, add_zero, zero_add, hu_α_qH, Function.update_self, Function.update_idem,
          zero_ne_one, ↓reduceIte, ket_X, h11, hu_α1_qH,
          cnotFanoutCirc_mulVec_ket]; rw [fanoutXorBits_eq_fixedFanoutBits M wCtrl wS cLo α1 hα1_wC
          (hDisjCS b), fixedFanoutBits_self_cancel cLo wS hInjS α]
  · rw [hb1]; constructor
    · simp only [P₀, cBH, ← Matrix.mulVec_mulVec, Matrix.mulVec_smul, Matrix.mulVec_add, ket_CNOT,
          ket_projector_zero, Function.update_of_ne hBH, hQH', hb1, hα1_qB, zero_add, h11, hu_α1_qH,
          Function.update_self, Function.update_idem, one_ne_zero, ↓reduceIte, hα1_qH]; rfl
    · simp only [P₁, cBH, cFix, ← Matrix.mulVec_mulVec, Matrix.mulVec_smul, Matrix.mulVec_add,
          Matrix.mulVec_zero, ket_CNOT, ket_projector_one, Function.update_of_ne hBH, hQH', hb1,
          hα1_qB, zero_add, add_zero, h11, hu_α1_qH, Function.update_self, Function.update_idem,
          zero_ne_one, ↓reduceIte, hα1_qH, ket_X, hu_α_qH,
          cnotFanoutCirc_mulVec_ket]; rw [fanoutXorBits_eq_fixedFanoutBits M wCtrl wS cLo α hCtrl
          (hDisjCS b)]
end
noncomputable section
set_option maxRecDepth 4096
open scoped Circuit.Notation
open Operator QProg Matrix Circuit Qubit PrimitiveGate QuantumComputation.Specs
  PhotochemistrySolution.KetSupport PhotochemistrySolution PhotochemistrySolution.SplitRouter47_187
  PhotochemistrySolution.SplitRouterFredkinMux
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
open PhotochemistrySolution.SplitRouterMuxD1 PhotochemistrySolution.ProviderCore
  PhotochemistrySolution.Stage12Compact PhotochemistrySolution.Stage2QromMux
  PhotochemistrySolution.Stage2ZeroGated PhotochemistrySolution.Stage2ChDiffMux960
  PhotochemistrySolution.Stage2ChDiffNoNF
open PhotochemistrySolution.Sub5885 PhotochemistrySolution.Sub5885MuxD1
  PhotochemistrySolution.PortBDualBellUnld PhotochemistrySolution.PortBStage5Merged
  PhotochemistrySolution.HalfBellCollapse PhotochemistrySolution.WStateStage2Load
  PhotochemistrySolution.RouterSelectWiringA
open PhotochemistrySolution.RouterSelectWiringB PhotochemistrySolution.PotSelectWiring HermitianMat
  PhotochemistrySolution.ProviderCoreFused PhotochemistrySolution.ZeroNEremSpec
  PhotochemistrySolution.SelectFastQft8Gidney PhotochemistrySolution.SelectQft8GidneyStg3
open PhotochemistrySolution.FastQft8 PhotochemistrySolution.Kinetic664
  PhotochemistrySolution.Kinetic664Stage4 PhotochemistrySolution.Qft8PostCancelT5
  PhotochemistrySolution.FusedUnembedLGen PhotochemistrySolution.PotOracleGen
open _root_.DynamicCircuit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt hiding bit_cases
  eval_seq_mulVec ket ket_CNOT ket_TOFF ket_X ket_projector_one ket_projector_zero localIdx
  matrix_ext_ket qAssign_obs_map_val
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SplitRouterSeqBell26k hiding ket
  matrix_ext_ket
open _root_.QuantumComputation.Specs.PhotochemistrySolution.PotOraclePortBStream (hDLayout_eq_7298)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SplitRouterSeqBell26k (ActsIndepOf)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB (ket matrix_ext_ket)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.WStateRouterPrim
  (toggleOneHotBits_apply_other uOneHotToggle uOneHotToggle_mulVec_ket toggleOneHotBits)
local instance (priority := 100000) {k : ℕ} : NeZero (2 ^ k) := ⟨pow_ne_zero k two_ne_zero⟩
section
attribute [local irreducible] systemQubits_frozen
/--
Private-wire involution `[1338..1343] <-> [1367..1372]` composed with `swapNucW350`,
redirecting `rCtrlHi[35..46]` (`rk = 141..152`) into unused nuclear slice scratch
(`rk = 77..82, 86..91 < 141`, `340 ≤ wWork`).
-/
def swapNucW340 (i : ℕ) : ℕ := swapPair 1338 1367 6 (swapNucW350 i)
theorem swapNucW340_lt : ∀ i < routerWidth 47 6, swapNucW340 i < routerWidth 47 6 := fun i hi ↦ by
  exact swapPair_lt (by decide) (by decide) (swapNucW350_lt i hi)
theorem swapNucW340_invol : ∀ i < routerWidth 47 6, swapNucW340 (swapNucW340 i) = i :=
    fun i (hi : i < 1394) ↦ by
  have hComm (x : ℕ) : swapPair 1338 1367 6 (swapPair 1344 1358 6 x) =
      swapPair 1344 1358 6 (swapPair 1338 1367 6 x) := by
    unfold swapPair
    split_ifs <;> omega
  dsimp only [swapNucW340, swapNucW350]
  rw [← hComm (swapPair 1344 1358 6 i), swapPair_invol (Or.inl (by omega)) _,
      swapPair_invol (Or.inl (by omega)) i]
theorem swapNucW340_pub : ∀ i < basePub 47 6, swapNucW340 i = i := fun i (hi : i < 1238) ↦ by
  simpa only [swapNucW340, swapNucW350_pub i hi] using swapPair_fixed (by omega) (by omega)
/--
Nuclear `(47, 6)` router with `rCtrlHi[35..46]` redirected to `< 141` private rank (`340 ≤ wWork`).
-/
def rNucW340 {n : ℕ} (r : RouterReg 47 6 n) : RouterReg 47 6 n :=
    routerOfInvol r swapNucW340 swapNucW340_lt swapNucW340_invol
theorem samePubPriv_rNucW340 {n : ℕ} (r : RouterReg 47 6 n) : SamePubPriv (rNucW340 r) r :=
    samePubPriv_routerOfInvol r swapNucW340 swapNucW340_lt swapNucW340_invol swapNucW340_pub
theorem hne_ctrlLo_sys_own {M D n : ℕ} (r : RouterReg M D n) (b : Fin 24)
    (p : Fin M) : rCtrlLo r p ≠ rSys r p b := hne_ctrlLo_sys_all r b p p
theorem not_bellLoCopyHiModSet_rElecSub_of_val {n : ℕ} (rTot : QRegister dLayout n)
    {w : Wire dLayout} (hw : w.val < 1128 ∨ (5616 ≤ w.val ∧ w.val < 5899) ∨ 5923 ≤ w.val) :
    ¬ BellLoCopyHiModSet (rTot.compose rElecSub) (rTot w) := by
  let rE := rTot.compose rElecSub; have hew : routerWidth 187 8 = 5056 := rfl
  rintro (⟨b, h⟩ | ⟨q, b, h⟩)
  · have hv := congrArg Fin.val (rTot.wires.injective h); have hb := b.isLt
    change w.val = (elecSubWireFn ⟨66 + b.val, by rw [hew]; omega⟩).val at hv
    rw [val_elecSubWireFn] at hv; dsimp at hv; split_ifs at hv <;> omega
  · have hv := congrArg Fin.val (rTot.wires.injective h)
    have hb := b.isLt; have hq := q.isLt
    change w.val = (elecSubWireFn ⟨98 + 2 * 8 + 24 * q.val + b.val, by rw [hew]; omega⟩).val at hv
    rw [val_elecSubWireFn] at hv; dsimp at hv; split_ifs at hv <;> omega

theorem innerLoCopyHiSafe_rElecSub_of_val {n : ℕ} (rTot : QRegister dLayout n) {w : Wire dLayout}
    (hw : w.val < 1128 ∨ (5616 ≤ w.val ∧ w.val < 5729) ∨ (5747 ≤ w.val ∧ w.val < 5875) ∨ 5923 ≤
    w.val) : InnerLoCopyHiSafe (rTot.compose rElecSub) (rTot w) := by
  have noIdx (k : ℕ) (hk : k < 5056) (hr : k < 18 ∨ (42 ≤ k ∧ k < 66))
      (h : rTot w = (rTot.compose rElecSub) ⟨k, hk⟩) : False := by
    have hv : w.val = (elecSubWireFn ⟨k, hk⟩).val := congrArg Fin.val (rTot.wires.injective h)
    rw [val_elecSubWireFn] at hv
    dsimp only at hv
    split_ifs at hv <;> omega
  refine ⟨fun h ↦ h.elim (noIdx 0 (by decide) (Or.inl (by decide))) fun h ↦
      h.elim (noIdx 1 (by decide) (Or.inl (by decide))) fun h ↦
        h.elim (fun ⟨d, hd⟩ ↦ noIdx (2 + d.val) (by omega) (Or.inl (by omega)) hd)
          fun ⟨d, hd⟩ ↦ noIdx (10 + d.val) (by omega) (Or.inl (by omega)) hd, ?_⟩
  rintro (⟨b, h⟩ | ⟨b, h⟩ | ⟨q, b, h⟩)
  · exact not_bellLoCopyHiModSet_rElecSub_of_val rTot (by omega) (Or.inl ⟨b, h⟩)
  · exact noIdx (42 + b.val) (by omega) (Or.inr ⟨by omega, by omega⟩) h
  · exact not_bellLoCopyHiModSet_rElecSub_of_val rTot (by omega) (Or.inr ⟨q, b, h⟩)

theorem innerLoCopyHiSafe_rElecSub_of_rNucSub {n : ℕ} (rTot : QRegister dLayout n)
    (u : Fin (routerWidth 47 6)) : InnerLoCopyHiSafe (rTot.compose rElecSub) (rTot (rNucSub u))
    := by
  have hrw : routerWidth 47 6 = 1394 := rfl
  have hu : u.val < 1394 := by rw [← hrw]; exact u.isLt
  have hfn : rNucSub u = nucSubWireFn u :=
      rfl; rw [hfn]; refine innerLoCopyHiSafe_rElecSub_of_val rTot ?_; rw [val_nucSubWireFn]
  split_ifs <;> omega

def LoToggleNucSet {n : ℕ} (rn : RouterReg 47 6 n) (w : Wire n) : Prop :=
    w = rHas1 rn ∨ (∃ d : Fin 6, w = rIdx1 rn d) ∨ (∃ j : Fin 48, w = wOutLoN48 rn j)
theorem actsIndepOf_not_loToggleNucSet {n : ℕ} (rn : RouterReg 47 6 n) :
    let dLo := wRouterDisj_loN48 rn
    ActsIndepOf (fun w ↦ ¬ LoToggleNucSet rn w)
      (uOneHotToggle (rHas1 rn) (rIdx1 rn) (wOutLoN48 rn) dLo.has_ne_out dLo.idx_ne_out) := by
  intro dLo
  refine ⟨toggleOneHotBits (rHas1 rn) (rIdx1 rn) (wOutLoN48 rn), fun α ↦
      uOneHotToggle_mulVec_ket _ _ _ dLo.has_ne_out dLo.idx_ne_out α, fun q hq α val ↦ ?_⟩
  have hOut (j) : wOutLoN48 rn j ≠ q := fun e ↦ hq (Or.inr (Or.inr ⟨j, e.symm⟩))
  have hIdxEq : idxValD (rIdx1 rn) (Function.update α q val) = idxValD (rIdx1 rn) α :=
    idxValD_congr fun d ↦ Function.update_of_ne (fun e ↦ hq (Or.inr (Or.inl ⟨d, e.symm⟩))) val α
  if hLt : idxValD (rIdx1 rn) α < 48 then
    have hLt' : idxValD (rIdx1 rn) (Function.update α q val) < 48 := hIdxEq ▸ hLt
    dsimp only [toggleOneHotBits]
    rw [dite_eq_left hLt', dite_eq_left hLt, show (⟨_, hLt'⟩ : Fin 48) =
        ⟨_, hLt⟩ from Fin.ext hIdxEq,
      Function.update_of_ne (hOut _), Function.update_of_ne fun e ↦
          hq (Or.inl e.symm), Function.update_comm (hOut _).symm]
  else
    have hLt' : ¬ idxValD (rIdx1 rn) (Function.update α q val) < 48 := hIdxEq ▸ hLt
    dsimp only [toggleOneHotBits]
    rw [dite_eq_right hLt', dite_eq_right hLt]
theorem rNucW340_sub_eq_and_privRank {n : ℕ} (rTot : QRegister dLayout n)
    {u : Fin (routerWidth 47 6)}
    (hu : u.val < 14 ∨ (62 ≤ u.val ∧ u.val < 86) ∨ (1256 ≤ u.val ∧ u.val < 1303) ∨ u.val = 1364) :
    rNucW340 (rTot.compose rNucSub) u = rTot (rNucSub u) ∧
    (u.val < 1238 ∨ (12 ≤ privRank156Sub (u.val - 1238) ∧ privRank156Sub (u.val - 1238) ≤ 58) ∨
      privRank156Sub (u.val - 1238) = 83) := by
  have huLt : u.val < 1394 :=
      Nat.lt_of_lt_of_le u.isLt (Nat.le_of_eq (rfl : routerWidth 47 6 = 1394))
  have hFix : swapNucW340 u.val = u.val := by
    rw [swapNucW340, swapNucW350, show swapPair 1344 1358 6 u.val =
        u.val from swapPair_fixed (by omega) (by omega),
      swapPair_fixed (by omega) (by omega)]
  refine ⟨congrArg (rTot.compose rNucSub).wires (Fin.ext hFix), ?_⟩
  refine hu.elim (fun _ ↦ Or.inl (by omega)) fun h ↦ h.elim (fun _ ↦ Or.inl (by omega)) fun h ↦
    h.elim (fun h2 ↦ Or.inr (Or.inl ?_)) fun h3 ↦ Or.inr (Or.inr (h3 ▸ rfl))
  unfold privRank156Sub
  split_ifs <;> omega

theorem loToggleNucSet_val_bounds {n : ℕ} (rTot : QRegister dLayout n) {w : Wire dLayout}
    (h : LoToggleNucSet (rNucW340 (rTot.compose rNucSub)) (rTot w)) : (5692 ≤ w.val ∧ w.val ≤
    5712) ∨ w.val = 5715 ∨ (5717 ≤ w.val ∧ w.val ≤ 5722) ∨ (5947 ≤ w.val ∧ w.val ≤ 5972) ∨ w.val =
    5997 := by
  let rn := rNucW340 (rTot.compose rNucSub)
  have hChk (u : Fin (routerWidth 47 6))
      (hu : u.val = 0 ∨ (2 ≤ u.val ∧ u.val < 8) ∨ (1256 ≤ u.val ∧ u.val < 1303) ∨ u.val = 1364)
      (heq : rTot w = rn u) : (5692 ≤ w.val ∧ w.val ≤ 5712) ∨ w.val = 5715 ∨
        (5717 ≤ w.val ∧ w.val ≤ 5722) ∨ (5947 ≤ w.val ∧ w.val ≤ 5972) ∨ w.val = 5997 := by
    have huLt : u.val < 1394 := u.isLt
    obtain ⟨hrn, hrk⟩ := rNucW340_sub_eq_and_privRank (u := u) rTot
      (hu.elim (fun _ ↦ Or.inl (by omega)) fun h ↦ h.elim (fun _ ↦ Or.inl (by omega))
          (Or.inr ∘ Or.inr))
    have hv : w.val = (nucSubWireFn u).val :=
        congrArg Fin.val (rTot.wires.injective (heq.trans hrn))
    rw [val_nucSubWireFn] at hv
    split_ifs at hv <;> omega
  rcases h with h1 | ⟨d, hd⟩ | ⟨j, hj⟩
  · exact hChk ⟨0, by decide⟩ (Or.inl rfl) h1
  · exact hChk ⟨2 + d.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left d.isLt 2) (by decide)⟩
      (Or.inr (Or.inl ⟨Nat.le_add_right 2 d.val, Nat.add_lt_add_left d.isLt 2⟩)) hd
  · exact wOutLoN48_mem (S := fun v ↦ rTot w = v → _) rn
      (fun p ↦ hChk ⟨1256 + p.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left p.isLt 1256) (by decide)⟩
        (Or.inr (Or.inr (Or.inl ⟨Nat.le_add_right 1256 p.val, Nat.add_lt_add_left p.isLt 1256⟩))))
      (hChk ⟨1364, by decide⟩ (Or.inr (Or.inr (Or.inr rfl)))) j hj
end
section
attribute [local reducible] totDimCompactGen
attribute [local irreducible] systemQubits_frozen ancWOfScr uRouterSwapConj
attribute [local irreducible] PgBase.phaseGradientState bSpeciesSwap50
attribute [local irreducible] PhotochemistrySolution.Stage4KinFull.bAxisMux27
/--
`dLayout` wires disjoint from `uAlignedKinCat2m1_98UselLayout` and `uAlignedKinCat2m1_98CselLayout`
.
-/
def KinDisjBand_wstate (w : Wire dLayout) : Prop :=
    (5680 ≤ w.val ∧ w.val ≤ 5728) ∨ (5730 ≤ w.val ∧ w.val ≤ 5747) ∨ (5779 ≤ w.val ∧ w.val ≤ 5850) ∨
    (5875 ≤ w.val ∧ w.val ≤ 6055)
theorem uAlignedKin2m1_98_comm_kinDisjBand_wstate {k : ℕ} (rC : QRegister k dLayout)
    (hrC : ∀ j : Fin k, KinDisjBand_wstate (rC j)) (M : Operator (2 ^ k)) :
    Commute uAlignedKinCat2m1_98UselLayout.1 (rC.embedMatrix M) ∧
    Commute uAlignedKinCat2m1_98CselLayout.1 (rC.embedMatrix M) := by
  have hd : dLayout = 7298 := hDLayout_eq_7298
  have hNe (w : Wire dLayout)
      (hw : (5642 ≤ w.val ∧ w.val ≤ 5649) ∨ w.val = 5729 ∨ (5748 ≤ w.val ∧ w.val ≤ 5778) ∨
        (5851 ≤ w.val ∧ w.val ≤ 5874) ∨ 6056 ≤ w.val) (j : Fin k) (e : w = rC j) : False := by
    have hb := hrC j
    unfold KinDisjBand_wstate at hb
    exact absurd (congrArg Fin.val e) (by omega)
  have cConj {W V : Unitary (2 ^ dLayout)} (cW : Commute W.1 (rC.embedMatrix M))
      (cV : Commute V.1 (rC.embedMatrix M)) :
      Commute (W⁻¹ * V * W).1 (rC.embedMatrix M) :=
    Commute.mul_left (Commute.mul_left (SelectFastQft8Gidney.unitary_inv_comm W _ cW) cV) cW
  obtain ⟨cwA0, hSp, hMux, hP8, hMid, hCln, abQ⟩ :=
    alignedKin_wires_of_bounds_wstate (P := fun w ↦ ∀ j : Fin k, w ≠ rC j) fun w hw ↦
        hNe w (by omega)
  have cA0 := circ_comm_embedMatrix_c70 rC M cwA0
  have cSp : Commute uSpeciesSwap50Layout.1 (rC.embedMatrix M) :=
    embedUnitary_comm_of_disjoint rSpeciesSwap50Layout _ rC (disj_of_ne hSp) M
  have cMux : Commute uMux27Layout.1 (rC.embedMatrix M) :=
    embedUnitary_comm_of_disjoint rMux27Layout _ rC (disj_of_ne hMux) M
  have cQdpost :=
      embedUnitary_comm_of_disjoint rPKinLayout (dPost8U * qftGridUnitary) rC (disj_of_ne hP8) M
  have cMid : Commute uKinMid2m1UselLayout.1 (rC.embedMatrix M) :=
    embedUnitary_comm_of_disjoint rKin226Layout _ rC (disj_of_ne hMid) M
  have cQcat :
      Commute (qft8PostCancel98CatU () scrWLayout offKinLayout hoffKinLayout rPKinLayout
      qft8Stg3ValidP_layout).1
      (rC.embedMatrix M) := by
    let rCln := qft8Stg3Clean13 scrWLayout offKinLayout hoffKinLayout
    have cBr :
        Commute (polyPostCancelT5Qft8Bracket98 (locCat8SharedCompactGen scrWLayout) rPKinLayout
        (qft8Stg3Delta7 scrWLayout offKinLayout hoffKinLayout)
        (qft8Stg3Carry6 scrWLayout offKinLayout hoffKinLayout)
        (qft8Stg3_rP_disj_cat8 qft8Stg3ValidP_layout)
        (qft8Stg3_rP_disj_delta7 hoffKinLayout qft8Stg3ValidP_layout)
        (qft8Stg3_delta7_disj_cat8 hoffKinLayout) (qft8Stg3_delta7_disj_carry6 hoffKinLayout)
        (qft8Stg3_cat8_disj_carry6 hoffKinLayout)
        (qft8Stg3_rP_disj_carry6 hoffKinLayout qft8Stg3ValidP_layout)).toCircuit.eval.1
        (rC.embedMatrix M) :=
        circ_comm_embedMatrix_c70 rC M (circWires_toCircuit_c70 abQ);
        have cP13 : Commute (rCln.basisOutcomeProjector 0) (rC.embedMatrix M) :=
        rCln.embedMatrix_comm_of_disjoint rC (disj_of_ne hCln)
        (compProj 0) M; unfold qft8PostCancel98CatU polyPostCancelCleanUnitary spliceUnitary; change
        spliceUnitaryMat _ _ _ * rC.embedMatrix M = rC.embedMatrix M *
        spliceUnitaryMat _ _ _; unfold spliceUnitaryMat; exact Commute.add_left (Commute.mul_left
        cBr cP13) (Commute.mul_left cQdpost (Commute.sub_left (Commute.one_left _) cP13))
  have cUsel : Commute uAlignedKinCat2m1_98UselLayout.1 (rC.embedMatrix M) :=
      cConj cA0 (cConj cSp (cConj cMux (cConj cQcat cMid)));
      let Pq :=
      projOneQCompactGen scrWLayout; have sKin :=
                                       csel_conj_unitary Pq uKinAlign0Layout
                                       uKinCat2m1_98CselLayout uKinCat2m1_98UselLayout
                                       comm_pq.2.eq uKin2m1_98Layout_props.1
                                       uKin2m1_98Layout_props.2.1
  have cPq : Commute Pq (rC.embedMatrix M) :=
      (QRegister.singleton wLocQLayout).embedMatrix_comm_of_disjoint rC
    (disj_of_ne fun i j e ↦ hNe wLocQLayout ((fun _ ↦ by omega) val_wLocQLayout) j
      ((congrArg (QRegister.singleton wLocQLayout).wires (Subsingleton.elim 0 i)).trans e))
          (compProj 1) M
  refine ⟨cUsel, ?_⟩
  unfold uAlignedKinCat2m1_98CselLayout uAlignedKinCat2m1_98UselLayout at *
  exact sKin.1.symm ▸ Commute.add_left (Commute.sub_left (Commute.one_left _) cPq)
      (Commute.mul_left cPq cUsel)

theorem embedMatrix_comm_uKin_of_kinDisjBand_wstate {k n : ℕ}
    (rTot : QRegister dLayout n) (rC : QRegister k dLayout)
    (hrC : ∀ j : Fin k, KinDisjBand_wstate (rC j)) (M : Operator (2 ^ k)) (isCsel : Bool) :
    let uKin :=
        rTot.embedUnitary (if isCsel then uAlignedKinCat2m1_98CselLayout else
        uAlignedKinCat2m1_98UselLayout)
    (rTot.compose rC).embedMatrix M * uKin.1 = uKin.1 * (rTot.compose rC).embedMatrix M := by
  intro uKin;
  obtain ⟨cU, cC⟩ :=
      uAlignedKin2m1_98_comm_kinDisjBand_wstate rC hrC M; dsimp only [uKin];
      rw [QRegister.embedMatrix_compose, QRegister.embedUnitary_val, ← rTot.embedMatrix_mul,
      ← rTot.embedMatrix_mul]; refine congrArg rTot.embedMatrix ?_
  exact Bool.rec cU.symm.eq cC.symm.eq isCsel

theorem sum_mulVec_finset_wstate {ι : Type*} {m n : ℕ} (s : Finset ι) (f : ι → Matrix (Fin m)
    (Fin n) ℂ) (v : Fin n → ℂ) : (∑ i ∈ s, f i).mulVec v = ∑ i ∈ s, (f i).mulVec v := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Matrix.zero_mulVec]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, Matrix.add_mulVec, ih]

theorem supportedOn_of_ket_proj_absorb_wstate {n : ℕ} {P : BitAssignment n → Prop} [DecidablePred P]
    {Q M : Operator (2 ^ n)} (hQ : ∀ β : BitAssignment n, Q.mulVec (ket β) =
    if P β then ket β else 0) (hAbs : Q * M = M) : SupportedOn P M := by
  intro A B hAB
  have hAQ : A * Q = B * Q := matrix_ext_ket fun β ↦ by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hQ β]
    exact if hP : P β then by simpa only [ite_eq_left hP] using hAB β hP else by simp [hP]
  rw [← hAbs, ← Matrix.mul_assoc, hAQ, Matrix.mul_assoc]

theorem supportedOn_uKin_of_dep_kinDisjBand_wstate {n : ℕ}
    (rTot : QRegister dLayout n) (isCsel : Bool)
    {P : BitAssignment n → Prop}
    (hDep : ∀ α α' : BitAssignment n,
      (∀ u : Wire dLayout, KinDisjBand_wstate u → α (rTot u) = α' (rTot u)) → P α → P α')
    {X : Operator (2 ^ n)} (hX : SupportedOn P X) :
    let uKin :=
        rTot.embedUnitary (if isCsel then uAlignedKinCat2m1_98CselLayout else
        uAlignedKinCat2m1_98UselLayout)
    SupportedOn P (uKin.1 * X) := by
  intro uKin
  classical
  let lB : List (Wire dLayout) :=
      (List.finRange dLayout).filter (fun u ↦ decide (KinDisjBand_wstate u))
  have hlNodup : lB.Nodup := (List.nodup_finRange dLayout).filter _
  let rBand : QRegister lB.length dLayout :=
      ⟨⟨fun i ↦ lB.get i, fun i j e ↦ (hlNodup.get_inj_iff).mp e⟩⟩
  have hrB : ∀ i : Fin lB.length, KinDisjBand_wstate (rBand i) := fun i ↦
      of_decide_eq_true (List.mem_filter.mp (List.get_mem lB i)).2
  have hMemB : ∀ u : Wire dLayout, KinDisjBand_wstate u → ∃ i : Fin lB.length, rBand i = u :=
      fun u hu ↦ List.mem_iff_get.mp (List.mem_filter.mpr ⟨List.mem_finRange u, decide_eq_true hu⟩)
  let P₀ : BitAssignment lB.length → Prop := fun δ ↦
      ∃ α : BitAssignment n, (∀ i, α ((rTot.compose rBand) i) = δ i) ∧ P α
  have hPiff : ∀ β : BitAssignment n, P₀ (fun i ↦ β ((rTot.compose rBand) i)) ↔ P β :=
    fun β ↦ ⟨fun ⟨α, hα, hpα⟩ ↦ hDep α β (fun u hu ↦ by
        obtain ⟨i, rfl⟩ := hMemB u hu; exact hα i) hpα,
      fun hpβ ↦ ⟨β, fun _ ↦ rfl, hpβ⟩⟩
  let Q : Operator (2 ^ n) := ∑ δ ∈ Finset.univ.filter P₀, projBits_c70 (rTot.compose rBand) δ
  have hQ (β : BitAssignment n) : Q.mulVec (ket β) = if P β then ket β else 0 := by
    let δ₀ : BitAssignment lB.length := fun i ↦ β ((rTot.compose rBand) i)
    simp only [Q, sum_mulVec_finset_wstate, projBits_mulVec_ket_c70,
      show ∀ δ, (∀ i, β ((rTot.compose rBand) i) = δ i) ↔ δ = δ₀ from
        fun _ ↦ ⟨fun h ↦ funext fun i ↦ (h i).symm, fun h i ↦ (congrFun h i).symm⟩,
      Finset.sum_ite_eq' (Finset.univ.filter P₀) δ₀, Finset.mem_filter, Finset.mem_univ, true_and,
      show P₀ δ₀ ↔ P β from hPiff β]
  have hQX : Q * X = X :=
      (hX Q 1 fun β hp ↦ by rw [hQ β, ite_eq_left hp, Matrix.one_mulVec]).trans (Matrix.one_mul X)
  have hQComm : Q * uKin.1 = uKin.1 * Q := by
    dsimp only [Q]
    rw [Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun δ _ ↦ ?_
    rw [projBits_eq_embedMatrix_c70 (rTot.compose rBand) δ]
    exact embedMatrix_comm_uKin_of_kinDisjBand_wstate rTot rBand hrB _ isCsel
  exact supportedOn_of_ket_proj_absorb_wstate hQ
      (by rw [← Matrix.mul_assoc, hQComm, Matrix.mul_assoc, hQX])
end
end
noncomputable section
set_option maxRecDepth 4096
open scoped Circuit.Notation
open Operator QProg Matrix HermitianMat Circuit Qubit PrimitiveGate QuantumComputation.Specs
  PhotochemistrySolution.KetSupport PhotochemistrySolution
  PhotochemistrySolution.RouterSelectWiringA
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
open PhotochemistrySolution.ZeroNEremSpec PhotochemistrySolution.PotSelectWiring
  PhotochemistrySolution.Stage2ZeroGated PhotochemistrySolution.Sub5885
  PhotochemistrySolution.Sub5885MuxD1 PhotochemistrySolution.HalfBellCollapse
  PhotochemistrySolution.WStateStage2Load
open _root_.DynamicCircuit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt hiding bit_cases
  eval_seq_mulVec ket ket_CNOT ket_TOFF ket_X ket_projector_one ket_projector_zero localIdx
  matrix_ext_ket qAssign_obs_map_val
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SplitRouterSeqBell26k hiding ket
  matrix_ext_ket
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SplitRouter47_187 hiding idxValD_congr
open PhotochemistrySolution.SelectRefl PhotochemistrySolution.PotOraclePortBStream
open _root_.QuantumComputation.Specs.PhotochemistrySolution.RouterSelectWiringB (rClean690Layout
    uAlignedKinCat2m1_98CselLayout uAlignedKinCat2m1_98UselLayout)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.PortBStage5Merged (supportedOn_and)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.PotOracleGen (disj_of_ne)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SortedRouterSpec
  (ValidZeroGatedSortedRouterInput)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB (ket matrix_ext_ket)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.WStateRouterPrim
  (toggleOneHotBits_apply_other uOneHotToggle uOneHotToggle_mulVec_ket toggleOneHotBits
   idxValD_congr)
local instance (priority := 100000) {k : ℕ} : NeZero (2 ^ k) := ⟨pow_ne_zero k two_ne_zero⟩
attribute [local irreducible] systemQubits_frozen uRouterSwapConj
theorem block6604_53_le_dLayout : 6604 + 53 ≤ dLayout := by rw [hDLayout_eq_7298]; omega
/-- Upper `53` clean scratch wires `[6604..6656]` of `rScrExt 0` used by `rPermKinStack_wstate`. -/
def rHi53Layout_wstate : QRegister 53 dLayout := QRegister.block 6604 53 block6604_53_le_dLayout
theorem val_rHi53Layout_wstate (j : Fin 53) : (rHi53Layout_wstate j).val = 6604 + j.val := rfl

theorem wNoHadClean_comm_rHi53_wstate (decodeCoin : Fin (2 ^ 41) → ZeroNEremSector)
    (M : Operator (2 ^ 53)) :
    Commute (wNoHad (uStage1Clean_c70 decodeCoin)).1 (rHi53Layout_wstate.embedMatrix M) := by
  have cS1 : Commute (uStage1Clean_c70 decodeCoin).1 (rHi53Layout_wstate.embedMatrix M) := by
    rw [uStage1Clean_eq_embed81_wstate decodeCoin]
    exact rStage1Clean81_wstate.embedMatrix_comm_of_disjoint rHi53Layout_wstate
      (disj_of_ne fun i j e ↦ by
        if h40 : i.val < 40 then
          have h1 : rStage1Clean81_wstate i = rOut40Layout ⟨i.val, h40⟩ :=
            QRegister.concat_apply_left rOut40Layout rOuter41Layout_wstate hDisjOut40Outer41_wstate
                ⟨i.val, h40⟩
          exact absurd (congrArg Fin.val (h1.symm.trans e))
            ((fun _ _ _ _ ↦ by omega) i.isLt j.isLt (val_rOut40Layout ⟨i.val, h40⟩)
                (val_rHi53Layout_wstate j))
        else
          have h1 : rStage1Clean81_wstate i = rOuter41Layout_wstate ⟨i.val - 40, by omega⟩ :=
            (congrArg rStage1Clean81_wstate.wires (Fin.ext (show i.val = 40 +
                (i.val - 40) by omega))).trans
              (QRegister.concat_apply_right rOut40Layout rOuter41Layout_wstate
                  hDisjOut40Outer41_wstate _)
          exact absurd (congrArg Fin.val (h1.symm.trans e))
            ((fun _ _ _ _ ↦ by omega) i.isLt j.isLt (val_rOuter41Layout_wstate ⟨i.val - 40,
                by omega⟩) (val_rHi53Layout_wstate j))) _ M
  have dE (i : Fin (routerWidth 187 8)) (j : Fin 53) (e : rElecLayout i = rHi53Layout_wstate j) :
      False := by
    have hv : (elecRouterWireFn i).val = 6604 + j.val := congrArg Fin.val e
    rw [val_elecRouterWireFn] at hv
    exact (fun (_ : i.val < 5056) _ ↦ by split_ifs at hv <;> omega) i.isLt j.isLt
  have dN (i : Fin (routerWidth 47 6)) (j : Fin 53) (e : rNucLayout i = rHi53Layout_wstate j) :
      False :=
    (fun _ _ (_ : (rNucLayout i).val = 6604 + j.val) ↦ by omega)
        (val_rNuc_bounds i) j.isLt (congrArg Fin.val e)
  simpa only [wNoHad, Submonoid.coe_mul] using Commute.mul_left
    (comm_uRouterSwapConj_embedMat_pot rElecLayout rHi53Layout_wstate dE M)
    (Commute.mul_left (comm_uRouterSwapConj_embedMat_pot rNucLayout rHi53Layout_wstate dN M) cS1)

theorem clean690_absorb_on_Wnh_wstate {n : ℕ} [NeZero (2 ^ n)]
    {decode : Fin (2 ^ 41) → ZeroNEremSector}
    (rTot : QRegister dLayout n) (X₁ : Operator (2 ^ n))
    (hAbsX₁ : (rTot.compose (rScrExt 0 hk0_le72_wstate)).basisOutcomeProjector 0 * X₁ = X₁)
    (c714₁ : (rTot.compose rClean714Layout).basisOutcomeProjector 0 *
      ((rTot.embedUnitary (wNoHad (uStage1Clean_c70 decode))).1 * X₁) =
      (rTot.embedUnitary (wNoHad (uStage1Clean_c70 decode))).1 * X₁) :
    let Z₀ := (rTot.embedUnitary (wNoHad (uStage1Clean_c70 decode))).1 * X₁
    (rTot.compose (rPermKinStack_wstate.compose rClean690Layout)).basisOutcomeProjector 0 * Z₀ =
        Z₀ := by
  intro Z₀; let P53 := (rTot.compose rHi53Layout_wstate).basisOutcomeProjector 0
  have h53X₁ : P53 * X₁ = X₁ := ((supportedOn_of_ket_proj_absorb_wstate
      (ket_basisOutcomeProjector_zero (rTot.compose (rScrExt 0 hk0_le72_wstate))) hAbsX₁) P53 1
          fun β hβ ↦ by
    have h0 (j : Fin 53) : β ((rTot.compose rHi53Layout_wstate) j) = 0 :=
      (congrArg (fun u ↦ β (rTot u)) (Fin.ext (by
          have := j.isLt
          rw [val_rHi53Layout_wstate, val_rScrExt]
          dsimp only
          omega)
        : rHi53Layout_wstate j = rScrExt 0 hk0_le72_wstate
            ⟨954 + j.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left j.isLt 954)
                (by decide)⟩)).trans (hβ _)
    rw [ket_basisOutcomeProjector_zero, ite_eq_left h0,
        Matrix.one_mulVec]).trans (Matrix.one_mul X₁)
  have h53Comm : P53 * (rTot.embedUnitary (wNoHad (uStage1Clean_c70 decode))).1 =
      (rTot.embedUnitary (wNoHad (uStage1Clean_c70 decode))).1 *
      P53
      := by dsimp only [P53]; rw [basisOutcomeProjector_compose_zero, QRegister.embedUnitary_val,
              ← rTot.embedMatrix_mul,
              ← rTot.embedMatrix_mul]; exact congrArg rTot.embedMatrix
              (wNoHadClean_comm_rHi53_wstate decode (compProj 0)).symm.eq
  have h53Z₀ : P53 * Z₀ = Z₀ := by
    dsimp only [Z₀]; rw [← Matrix.mul_assoc, h53Comm, Matrix.mul_assoc, h53X₁]
  have s53 :=
      supportedOn_of_ket_proj_absorb_wstate (fun β ↦
      ket_basisOutcomeProjector_zero (rTot.compose rHi53Layout_wstate) β) h53Z₀
  have s714 :=
      supportedOn_of_ket_proj_absorb_wstate (fun β ↦
      ket_basisOutcomeProjector_zero (rTot.compose rClean714Layout) β) c714₁
  let rC690 := rTot.compose (rPermKinStack_wstate.compose rClean690Layout)
  refine ((supportedOn_and s714 s53) (rC690.basisOutcomeProjector 0) 1 fun β ⟨h7, h5⟩ ↦
      ?_).trans (Matrix.one_mul Z₀)
  have h0 : ∀ m : Fin 690, β (rC690 m) = 0 := fun m ↦ by
    let u := rPermKinStack_wstate (rClean690Layout m);
    have hb := rPermKinStack_clean690_bounds_wstate m; change β (rTot u) = 0
    by_cases hhi : 6604 ≤ u.val
    · have heq : u = rHi53Layout_wstate ⟨u.val - 6604, by omega⟩ :=
        Fin.ext (by rw [val_rHi53Layout_wstate]; dsimp only; omega)
      rw [heq]; exact h5 _
    · have hMem : ∃ k : Fin 714, u = rClean714Layout k := by
        by_cases hb1 : 5827 ≤ u.val ∧ u.val ≤ 5850
        · exact ⟨⟨u.val - 5827, by omega⟩,
              Fin.ext (by rw [val_rClean714Layout]; dsimp only; split_ifs <;> omega)⟩
        · by_cases hb2 : 5680 ≤ u.val ∧ u.val ≤ 5691
          · exact ⟨⟨24 + (u.val - 5680), by omega⟩,
                Fin.ext (by rw [val_rClean714Layout]; dsimp only; split_ifs <;> omega)⟩
          · exact ⟨⟨57 + (u.val - 5947), by omega⟩,
                Fin.ext (by rw [val_rClean714Layout]; dsimp only; split_ifs <;> omega)⟩
      obtain ⟨k, hku⟩ := hMem; rw [hku]; exact h7 k
  rw [ket_basisOutcomeProjector_zero, ite_eq_left h0, Matrix.one_mulVec]

theorem uLoToggle_comm_uHiToggle_nuc {n : ℕ} (rn : RouterReg 47 6 n) :
    let dLo := wRouterDisj_loN48 rn; let dHi := wRouterDisj_hiN48 rn;
    let ULo := uOneHotToggle (rHas1 rn) (rIdx1 rn) (wOutLoN48 rn) dLo.has_ne_out dLo.idx_ne_out;
    let UHi := uOneHotToggle (rRawHas2 rn) (rIdx2 rn) (wOutHiN48 rn) dHi.has_ne_out dHi.idx_ne_out
    UHi.1 * ULo.1 = ULo.1 * UHi.1 := by
  intro dLo dHi ULo UHi
  have hDisj := hne_wOutLoN48_wOutHiN48 rn
  refine matrix_ext_ket fun α ↦ ?_
  have hIdx2Eq : idxValD (rIdx2 rn) (toggleOneHotBits (rHas1 rn) (rIdx1 rn) (wOutLoN48 rn) α) =
      idxValD (rIdx2 rn) α :=
    idxValD_congr (rIdx2 rn) fun d ↦
        toggleOneHotBits_apply_other α (wOutLoN48_mem (S := (rIdx2 rn d ≠ ·)) rn
      (fun _ ↦ rr_ne rn (by
        have := d.isLt
        dsimp [rIdx2, rCtrlLo, basePub]
        omega))
      (rr_ne rn (by
        have := d.isLt
        dsimp [rIdx2]
        omega)))
  have hHas2Eq : toggleOneHotBits (rHas1 rn) (rIdx1 rn) (wOutLoN48 rn) α (rRawHas2 rn) =
      α (rRawHas2 rn) :=
    toggleOneHotBits_apply_other α (wOutLoN48_mem (S := (rRawHas2 rn ≠ ·)) rn
      (fun p ↦ rr_ne rn (by
        have := p.isLt
        dsimp [rRawHas2, rCtrlLo, basePub, routerWidth]
        omega))
      (rr_ne rn (by decide)))
  have hIdx1Eq : idxValD (rIdx1 rn) (toggleOneHotBits (rRawHas2 rn) (rIdx2 rn) (wOutHiN48 rn) α) =
      idxValD (rIdx1 rn) α :=
    idxValD_congr (rIdx1 rn) fun d ↦
        toggleOneHotBits_apply_other α (wOutHiN48_mem (S := (rIdx1 rn d ≠ ·)) rn
      (fun _ ↦ rr_ne rn (by
        have := d.isLt
        dsimp [rIdx1, rCtrlHi, basePub]
        omega))
      (rr_ne rn (by
        have := d.isLt
        dsimp [rIdx1]
        omega)))
  have hHas1Eq : toggleOneHotBits (rRawHas2 rn) (rIdx2 rn) (wOutHiN48 rn) α (rHas1 rn) =
      α (rHas1 rn) :=
    toggleOneHotBits_apply_other α (wOutHiN48_mem (S := (rHas1 rn ≠ ·)) rn
      (fun _ ↦ rr_ne rn (by
        dsimp [rHas1, rCtrlHi, basePub]
        omega))
      (rr_ne rn (by decide)))
  simp only [ULo, UHi, ← Matrix.mulVec_mulVec, uOneHotToggle_mulVec_ket]
  congr 1
  have hTog (wH : Wire n) (wI : Fin 6 → Wire n) (wO : Fin 48 → Wire n) (β) :
      toggleOneHotBits wH wI wO β = if h : idxValD wI β < 48 then
        Function.update β (wO ⟨idxValD wI β, h⟩) (β (wO ⟨idxValD wI β, h⟩) + β wH) else β := rfl
  by_cases h1 : idxValD (rIdx1 rn) α < 48
  · by_cases h2 : idxValD (rIdx2 rn) α < 48
    · let h1' := hIdx1Eq.symm ▸ h1
      let h2' := hIdx2Eq.symm ▸ h2
      rw [hTog (rRawHas2 rn) _ _ (toggleOneHotBits _ _ _ α),
        hTog (rHas1 rn) _ _ (toggleOneHotBits _ _ _ α), dite_eq_left h2', dite_eq_left h1',
        show (⟨_, h1'⟩ : Fin 48) = ⟨idxValD (rIdx1 rn) α, h1⟩ from Fin.ext hIdx1Eq,
        show (⟨_, h2'⟩ : Fin 48) = ⟨idxValD (rIdx2 rn) α, h2⟩ from Fin.ext hIdx2Eq,
        hHas2Eq, hHas1Eq, toggleOneHotBits_apply_other α fun j ↦ (hDisj j ⟨_, h2⟩).symm,
        toggleOneHotBits_apply_other α (hDisj ⟨_, h1⟩), hTog (rHas1 rn) _ _ α,
        hTog (rRawHas2 rn) _ _ α, dite_eq_left h1, dite_eq_left h2,
            Function.update_comm (hDisj _ _)]
    · rw [hTog (rRawHas2 rn) _ _ (toggleOneHotBits _ _ _ α), dite_eq_right (hIdx2Eq ▸ h2),
        show toggleOneHotBits (rRawHas2 rn) (rIdx2 rn)
            (wOutHiN48 rn) α = α by rw [hTog, dite_eq_right h2]]
  · rw [hTog (rHas1 rn) _ _ (toggleOneHotBits _ _ _ α), dite_eq_right (hIdx1Eq ▸ h1),
      show toggleOneHotBits (rHas1 rn) (rIdx1 rn)
          (wOutLoN48 rn) α = α by rw [hTog, dite_eq_right h1]]
theorem circWires_and_toff_fixedFanoutVec {M n : ℕ} {S : Wire n → Prop} (m : ℕ)
    (qB : Fin m → Wire n) (cVec : Fin M → ZMod 2) (wT : Fin m → Fin M → Wire n)
    (hbt : ∀ k p, qB k ≠ wT k p) (hq : ∀ k, S (qB k)) (hw : ∀ k p, S (wT k p)) :
    CircWires S (fixedFanoutVecCirc M m qB cVec wT hbt) ∧
    (fixedFanoutVecCirc M m qB cVec wT hbt).count .TOFF = 0 := by
  have h1 : ∀ (K : ℕ) (q0 : Wire n) (cV : Fin K → ZMod 2) (w0 : Fin K → Wire n)
      (h0 : ∀ p, q0 ≠ w0 p),
      S q0 → (∀ p, S (w0 p)) → CircWires S (fixedFanoutCirc K q0 cV w0 h0) ∧
          (fixedFanoutCirc K q0 cV w0 h0).count .TOFF = 0 := by
    intro K
    induction K with
    | zero => exact fun _ _ _ _ _ _ ↦ ⟨trivial, rfl⟩
    | succ K ih =>
        intro q0 _ _ _ hq0 hw0
        obtain ⟨cw, ct⟩ := ih q0 _ _ _ hq0 (fun p ↦ hw0 p.castSucc)
        refine ⟨⟨cw, ?_⟩,
            by simpa only [fixedFanoutCirc, Circuit.count_seq, ct,
                 zero_add] using by split_ifs <;> rfl⟩
        split_ifs
        · exact fun i ↦ Fin.cases hq0 (Fin.cases (hw0 _) fun k ↦ k.elim0) i
        · trivial
  induction m with
  | zero => exact ⟨trivial, rfl⟩
  | succ m ih =>
      obtain ⟨cw, ct⟩ :=
          ih (fun k ↦ qB k.castSucc) (fun k ↦ wT k.castSucc) (fun k p ↦ hbt k.castSucc p)
          (fun k ↦ hq k.castSucc) (fun k p ↦ hw k.castSucc p)
      obtain ⟨cwL, ctL⟩ :=
          h1 M _ cVec _ (hbt (Fin.last m)) (hq (Fin.last m))
          (hw (Fin.last m)); dsimp only [fixedFanoutVecCirc]
      exact ⟨⟨cw, cwL⟩, by rw [Circuit.count_seq, ct, ctL]⟩

theorem rNucW340_kinDisjBand_fixed {n : ℕ} (rTot : QRegister dLayout n) {u : Fin (routerWidth 47 6)}
    (hu : u.val < 14 ∨ (62 ≤ u.val ∧ u.val < 86) ∨ (1256 ≤ u.val ∧ u.val < 1303) ∨ u.val = 1364) :
    rNucW340 (rTot.compose rNucSub) u = rTot (rNucSub u) ∧ KinDisjBand_wstate (rNucSub u) := by
  have huLt : u.val < 1394 := u.isLt
  obtain ⟨hEq, hrk⟩ := rNucW340_sub_eq_and_privRank rTot hu
  refine ⟨hEq, ?_⟩
  change KinDisjBand_wstate (nucSubWireFn u)
  unfold KinDisjBand_wstate
  rw [val_nucSubWireFn]
  split_ifs <;> omega
end
end
noncomputable section
set_option exponentiation.threshold 8192
open Operator QProg Matrix Circuit Qubit PrimitiveGate QuantumComputation.Specs
  PhotochemistrySolution.KetSupport PhotochemistrySolution PhotochemistrySolution.SplitRouter47_187
  PhotochemistrySolution.RouterSelectWiringA
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
open PhotochemistrySolution.RouterSelectWiringB PhotochemistrySolution.ProviderCore
  PhotochemistrySolution.Stage12Compact PhotochemistrySolution.ZeroNEremSpec
  PhotochemistrySolution.PotSelectWiring PhotochemistrySolution.Sub5885MuxD1
  PhotochemistrySolution.PotOraclePortBStream
open PhotochemistrySolution.PotOraclePortB PhotochemistrySolution.ReflStage4
open _root_.DynamicCircuit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt hiding bit_cases
  eval_seq_mulVec ket ket_CNOT ket_TOFF ket_X ket_projector_one ket_projector_zero localIdx
  matrix_ext_ket qAssign_obs_map_val
open _root_.QuantumComputation.Specs.PhotochemistrySolution.QubitizationWalkSem (bitSign sqrtHalf)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.PotOracleGen (disj_of_ne)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB (ket matrix_ext_ket)
section
attribute [local reducible] totDimCompactGen
attribute [local irreducible] systemQubits_frozen ancWOfScr uRouterSwapConj
    PgBase.phaseGradientState
/-- Restrict a `41`-coin bit assignment to its lower `35` coins. -/
def take35Of41_wstate (z : BitAssignment 41) : BitAssignment 35 :=
  fun j ↦ z ⟨j.val, Nat.lt_trans j.isLt (by decide : 35 < 41)⟩

/-- Splice a new `35`-coin assignment onto the lower `35` indices of `z : BitAssignment 41`. -/
def put35In41_wstate (z35 : BitAssignment 35) (z : BitAssignment 41) : BitAssignment 41 :=
  fun i ↦ if h : i.val < 35 then z35 ⟨i.val, h⟩ else z i

/-- Equivalence splitting `BitAssignment 41` into `(BitAssignment 35) × (BitAssignment 6)`. -/
def equiv41_split35_6_wstate : BitAssignment 41 ≃ BitAssignment 35 × BitAssignment 6 where
  toFun z := (take35Of41_wstate z, fun j ↦ z ⟨35 + j.val, by have := j.isLt; omega⟩)
  invFun p := fun i ↦
    if h : i.val < 35 then p.1 ⟨i.val, h⟩
    else p.2 ⟨i.val - 35, by have := i.isLt; omega⟩
  left_inv z := funext fun i ↦ by
    by_cases h : i.val < 35
    · simp [take35Of41_wstate, h]
    · simp only [h, ↓reduceDIte]
      exact congrArg z (Fin.ext (by dsimp; omega))
  right_inv p := Prod.ext
    (funext fun j ↦ by
      have hj : j.val < 35 := j.isLt
      simp [take35Of41_wstate, hj])
    (funext fun j ↦ by
      have hn : ¬ (35 + j.val < 35) := by omega
      simp only [hn, ↓reduceDIte]
      exact congrArg p.2 (Fin.ext (by dsimp; omega)))

/--
Lift a `35`-coin `ReflPotSliceSpec35` to a `41`-coin `ReflPotSliceSpec` acting as identity on
retired inner coins `35 .. 40`.
-/
def liftReflPotSlice35To41_wstate {potExpect : PotExpectFn} (s : ReflPotSliceSpec35 potExpect) :
    ReflPotSliceSpec potExpect where
  phaseBit s0 nn sp1 sp2 nA nB eA eB z :=
    s.phaseBit s0 nn sp1 sp2 nA nB eA eB (take35Of41_wstate z)
  coinSwap s0 nn sp1 sp2 nA nB eA eB z :=
    put35In41_wstate (s.coinSwap s0 nn sp1 sp2 nA nB eA eB (take35Of41_wstate z)) z
  coinSwap_invol s0 nn sp1 sp2 nA nB eA eB z := funext fun i ↦ by
    have hTake : take35Of41_wstate
        (put35In41_wstate (s.coinSwap s0 nn sp1 sp2 nA nB eA eB (take35Of41_wstate z)) z) =
        s.coinSwap s0 nn sp1 sp2 nA nB eA eB (take35Of41_wstate z) :=
      funext fun j ↦ by simp [take35Of41_wstate, put35In41_wstate, j.isLt]
    rw [hTake, s.coinSwap_invol]
    by_cases hi : i.val < 35 <;> simp [put35In41_wstate, take35Of41_wstate, hi]
  phaseBit_coinSwap s0 nn sp1 sp2 nA nB eA eB z := by
    have hTake : take35Of41_wstate
        (put35In41_wstate (s.coinSwap s0 nn sp1 sp2 nA nB eA eB (take35Of41_wstate z)) z) =
        s.coinSwap s0 nn sp1 sp2 nA nB eA eB (take35Of41_wstate z) :=
      funext fun j ↦ by simp [take35Of41_wstate, put35In41_wstate, j.isLt]
    rw [hTake]; exact s.phaseBit_coinSwap s0 nn sp1 sp2 nA nB eA eB (take35Of41_wstate z)
  phaseBit_port s0 nn sp1 sp2 nA nB eA eB z :=
    s.phaseBit_port s0 nn sp1 sp2 nA nB eA eB (take35Of41_wstate z)
  coinSwap_port s0 nn sp1 sp2 nA nB eA eB z :=
    congrArg (fun u ↦ put35In41_wstate u z)
      (s.coinSwap_port s0 nn sp1 sp2 nA nB eA eB (take35Of41_wstate z))
  avg_coin41 s0 nn sp1 sp2 nA nB eA eB := by
    let f : BitAssignment 41 → ℂ := fun z ↦
        bitSign (s.phaseBit s0 nn sp1 sp2 nA nB eA eB (take35Of41_wstate z))
    change (2 ^ 41 : ℂ)⁻¹ * ∑ z : BitAssignment 41, f z = (potExpect s0 nn sp1 sp2 nA nB eA eB : ℂ);
    rw [← Equiv.sum_comp equiv41_split35_6_wstate.symm f, Fintype.sum_prod_type]
    have hPoint : ∀ (z35 : BitAssignment 35) (z6 : BitAssignment 6),
        f (equiv41_split35_6_wstate.symm (z35, z6)) =
          bitSign (s.phaseBit s0 nn sp1 sp2 nA nB eA eB z35) := fun z35 z6 ↦ by
      dsimp only [f]
      rw [show take35Of41_wstate (equiv41_split35_6_wstate.symm (z35, z6)) = z35 from
        congrArg Prod.fst (equiv41_split35_6_wstate.apply_symm_apply (z35, z6))]
    simp_rw [hPoint]
    have hCard6 : Fintype.card (BitAssignment 6) = 2 ^ 6 := by decide
    simp only [Finset.sum_const, Finset.card_univ, hCard6, nsmul_eq_mul, Nat.cast_pow,
        Nat.cast_ofNat, ← Finset.mul_sum, ← mul_assoc]
    have h2 : (2 ^ 41 : ℂ)⁻¹ * (2 : ℂ) ^ 6 = (2 ^ 35 : ℂ)⁻¹ := by
      have h41 : (2 : ℂ) ^ 41 = (2 : ℂ) ^ 35 * (2 : ℂ) ^ 6 := by norm_num
      rw [h41, mul_inv, mul_assoc, inv_mul_cancel₀ (pow_ne_zero 6 two_ne_zero), mul_one]
    rw [h2]; exact s.avg_coin35 s0 nn sp1 sp2 nA nB eA eB
end
def skip6Val_wstate (k : ℕ) : ℕ := if k < 116 then k else k + 6
theorem skip6Val_lt_wstate {Wp : ℕ} (i : Fin (116 + Wp)) : skip6Val_wstate i.val < 122 + Wp := by
  have := i.isLt; unfold skip6Val_wstate; split_ifs <;> omega
/-- Subregister embedding `116 + Wp` into `122 + Wp` skipping retired inner coins `116 .. 121`. -/
def skip6Of122Wp_wstate (Wp : ℕ) : QRegister (116 + Wp) (122 + Wp) where
  wires :=
    { toFun := fun i ↦ ⟨skip6Val_wstate i.val, skip6Val_lt_wstate i⟩
      inj' := fun a b h ↦ by
        have hv := congrArg Fin.val h
        dsimp [skip6Val_wstate] at hv; split_ifs at hv <;> exact Fin.ext (by omega) }

theorem val_skip6Of122Wp_wstate {Wp : ℕ} (i : Fin (116 + Wp)) :
    (skip6Of122Wp_wstate Wp i).val = if i.val < 116 then i.val else i.val + 6 := rfl
end
noncomputable section
set_option maxRecDepth 4096
open scoped Circuit.Notation
open Operator QProg Matrix HermitianMat Circuit Qubit PrimitiveGate QuantumComputation.Specs
  PhotochemistrySolution.KetSupport PhotochemistrySolution PhotochemistrySolution.SplitRouter47_187
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
open PhotochemistrySolution.RouterSelectWiringA PhotochemistrySolution.RouterSelectWiringB
  PhotochemistrySolution.ProviderCore PhotochemistrySolution.Stage12Compact
  PhotochemistrySolution.ZeroNEremSpec PhotochemistrySolution.PotSelectWiring
  PhotochemistrySolution.PotOraclePortB
open PhotochemistrySolution.PotOraclePortBStream PhotochemistrySolution.PotOraclePortBStage4
  PhotochemistrySolution.Coin70Lift PhotochemistrySolution.PortBDualBellUnld
  PhotochemistrySolution.ReflStage4 PhotochemistrySolution.SelectCompactAnc
open PhotochemistrySolution.ProviderZeroFloor PhotochemistrySolution.Kinetic664
  PhotochemistrySolution.Kinetic664Stage4 PhotochemistrySolution.SortedRouterSpec
  PhotochemistrySolution.PortBStage5Merged PhotochemistrySolution.HalfBellCollapse
open _root_.DynamicCircuit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt hiding bit_cases
  eval_seq_mulVec ket ket_CNOT ket_TOFF ket_X ket_projector_one ket_projector_zero localIdx
  matrix_ext_ket qAssign_obs_map_val
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SplitRouterSeqBell26k hiding ket
  matrix_ext_ket
open PhotochemistrySolution.XMeasChunkQromUnldA PhotochemistrySolution.GenWeightsSelect
open _root_.QuantumComputation.Specs.PhotochemistrySolution.QubitizationWalkSem (bitSign
    bitSign_zero)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Sub5885MuxD1 (rNucSub rElecSub
    validMuxD1Stage2Regs_sub)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.PotOracleGen (disj_of_ne)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB (ket matrix_ext_ket ket_CNOT)
local instance (priority := 100000) {k : ℕ} : NeZero (2 ^ k) := ⟨pow_ne_zero k two_ne_zero⟩
/--
Raw index permutation on `0 .. 7297` shifting `5995 .. 6603` down by `48`,
mapping `5947 .. 5970` into `rHA rNucLayout` (`5803 .. 5826`), mapping `5971 .. 5994`
into `rHB rElecLayout` (`5923 .. 5946`), and closing both `24`-wire cycles at `6556 .. 6603`
while leaving `rHB rNucLayout` (`5827 .. 5850`, already used by `PortB` (`151`-wire)) fixed.
-/
def permPot103Val (x : ℕ) : ℕ :=
    if 5803 ≤ x ∧ x ≤ 5826 then 6556 + (x - 5803) else if 5923 ≤ x ∧ x ≤ 5946 then 6580 +
    (x - 5923) else if 5947 ≤ x ∧ x ≤ 5970 then 5803 + (x - 5947) else if 5971 ≤ x ∧ x ≤
    5994 then 5923 + (x - 5971) else if 5995 ≤ x ∧ x ≤ 6603 then x - 48 else x
theorem permPot103Val_lt (x : ℕ) (hx : x < dLayout) : permPot103Val x < dLayout := by
  have hd : dLayout = 7298 := hDLayout_eq_7298; unfold permPot103Val
  split_ifs <;> omega

theorem permPot103Val_inj {x y : ℕ} (hx : x < dLayout) (hy : y < dLayout)
    (h : permPot103Val x = permPot103Val y) : x = y := by
  have hd : dLayout = 7298 := hDLayout_eq_7298; unfold permPot103Val at h
  split_ifs at h <;> omega

/--
`dLayout` wire permutation routing `48` `rClean690Layout` wires of `rPotZeroNEremPortB151`
onto `rHA rNucLayout` (`5803 .. 5826`) and `rHB rElecLayout` (`5923 .. 5946`), shifting the
remaining Stage-4 scratch pool down by `48` (`103 + Wp ≤ wWork`).
-/
def rPermPot103 : QRegister dLayout dLayout :=
    ⟨⟨fun w ↦ ⟨permPot103Val w.val, permPot103Val_lt w.val w.isLt⟩, fun a b hab ↦
    Fin.ext (permPot103Val_inj a.isLt b.isLt (congrArg Fin.val hab))⟩⟩
@[simp] theorem val_rPermPot103 (w : Wire dLayout) :
    (rPermPot103 w).val = permPot103Val w.val := rfl

theorem rPermPot103_fix_of_bounds (w : Wire dLayout)
    (h : w.val < 5803 ∨ (5827 ≤ w.val ∧ w.val < 5923) ∨ 6604 ≤ w.val) : rPermPot103 w = w := by
  apply Fin.ext; rw [val_rPermPot103]; unfold permPot103Val
  split_ifs <;> omega
section
attribute [local irreducible] clampOneHot
theorem permPot103_rPot0_and_clamp {n : ℕ} (rTot : QRegister dLayout n) :
    let rTot' := rTot.compose rPermPot103
    rTot'.compose rPot0Layout = rTot.compose rPot0Layout ∧ (uSwapHi24 rTot').1 =
        (uSwapHi24 rTot).1 ∧ clampPotBRefl rTot' = clampPotBRefl rTot := by
  intro rTot'
  have hPot0 (i : Fin 146) : rPermPot103 (rPot0Layout i) = rPot0Layout i := by
    have _ := i.isLt; refine rPermPot103_fix_of_bounds _ ?_;
    have hv : (rPot0Layout i).val = (potZeroNEremWireFn 0 pot0_le_690 i).val := rfl
    rw [hv, val_potZeroNEremWireFn pot0_le_690]; split_ifs <;> omega
  have hNHi (b : Fin 24) : rPermPot103 (rBufHi rNucLayout b) = rBufHi rNucLayout b :=
    rPermPot103_fix_of_bounds _ ((fun (_ : _ < _) (_ : _) ↦ by omega) b.isLt (val_bufHi_nuc b))
  have hEHi (b : Fin 24) : rPermPot103 (rBufHi rElecLayout b) = rBufHi rElecLayout b :=
    rPermPot103_fix_of_bounds _ ((fun (_ : _ < _) (_ : _) ↦ by omega) b.isLt (val_bufHi_elec b))
  have hwNN : rTot' (wPotIsNN rPot0Layout) = rTot (wPotIsNN rPot0Layout) :=
      congrArg rTot.wires (hPot0 ⟨4, by decide⟩)
  have hEqE (b : Fin 24) : rTot' (rBufHi rElecLayout b) = rTot (rBufHi rElecLayout b) :=
      congrArg rTot.wires (hEHi b)
  have hEqN (b : Fin 24) : rTot' (rBufHi rNucLayout b) = rTot (rBufHi rNucLayout b) :=
      congrArg rTot.wires (hNHi b)
  refine ⟨congrArg QRegister.mk (Function.Embedding.ext fun i ↦ congrArg rTot.wires (hPot0 i)),
    matrix_ext_ket fun β ↦ ?_, funext fun β ↦ ?_⟩
  · rw [uSwapHi24_mulVec_ket rTot' β, uSwapHi24_mulVec_ket rTot β]
    refine congrArg ket (funext fun w ↦ ?_)
    obtain ⟨⟨eE1, eN1, eO1⟩, eE2, eN2, eO2⟩ :=
        And.intro (swapHi24Bits_apply rTot' β) (swapHi24Bits_apply rTot β)
    if hwE : ∃ b, w = rTot (rBufHi rElecLayout b) then
      rcases hwE with ⟨b, rfl⟩
      rw [← hEqE b, eE1 b, hEqE b, hEqN b, hwNN, eE2 b]
    else if hwN : ∃ b, w = rTot (rBufHi rNucLayout b) then
      rcases hwN with ⟨b, rfl⟩
      rw [← hEqN b, eN1 b, hEqE b, hEqN b, hwNN, eN2 b]
    else rw [eO1 w (fun b e ↦ hwE ⟨b, e.trans (hEqE b)⟩) (fun b e ↦ hwN ⟨b, e.trans (hEqN b)⟩),
      eO2 w (fun b e ↦ hwE ⟨b, e⟩) (fun b e ↦ hwN ⟨b, e⟩)]
  · dsimp only [clampPotBRefl]
    rw [show clampFlags rTot' β = clampFlags rTot β by
      simp only [clampFlags, show rTot' (wPotIsPot rPot0Layout) =
          _ from congrArg rTot.wires (hPot0 ⟨2, by decide⟩),
        show rTot' (wPotIsScreen rPot0Layout) = _ from congrArg rTot.wires (hPot0 ⟨1, by decide⟩),
            hwNN]]
    refine funext fun w ↦ ?_
    obtain ⟨⟨cN1, cE1, cO1⟩, cN2, cE2, cO2⟩ :=
        And.intro (clampOneHot_apply rTot' _) (clampOneHot_apply rTot _)
    if hwN : ∃ b, w = rTot (rBufHi rNucLayout b) then
      rcases hwN with ⟨b, rfl⟩
      rw [← hEqN b, cN1 b, hEqN b, hwNN, cN2 b]
    else if hwE : ∃ b, w = rTot (rBufHi rElecLayout b) then
      rcases hwE with ⟨b, rfl⟩
      rw [← hEqE b, cE1 b, hEqE b, hwNN, cE2 b]
    else rw [cO1 w (fun b e ↦ hwN ⟨b, e.trans (hEqN b)⟩) (fun b e ↦ hwE ⟨b, e.trans (hEqE b)⟩),
      cO2 w (fun b e ↦ hwN ⟨b, e⟩) (fun b e ↦ hwE ⟨b, e⟩)]
theorem val_rPermPot103_rClean714Layout_rng (q : Fin 714) :
    (5680 ≤ (rPermPot103 (rClean714Layout q)).val ∧ (rPermPot103 (rClean714Layout q)).val < 5713) ∨
    (5803 ≤ (rPermPot103 (rClean714Layout q)).val ∧ (rPermPot103 (rClean714Layout q)).val < 5851) ∨
    (5923 ≤ (rPermPot103 (rClean714Layout q)).val ∧ (rPermPot103 (rClean714Layout q)).val < 6604)
    := by
  have _ := q.isLt
  set x := (rClean714Layout q).val
  have hx : x = _ :=
      val_rClean714Layout q; change (5680 ≤ permPot103Val x ∧ permPot103Val x < 5713) ∨
      (5803 ≤ permPot103Val x ∧ permPot103Val x < 5851) ∨ (5923 ≤ permPot103Val x ∧
      permPot103Val x < 6604)
  split_ifs at hx <;> (unfold permPot103Val; split_ifs <;> omega)
end
attribute [local reducible] totDimCompactGen in
attribute [local irreducible] systemQubits_frozen ancWOfScr in
theorem uAlignedKin2m1_98_preserves_routed_wstate {decode : Fin (2 ^ 41) → ZeroNEremSector}
    (isCsel : Bool) (rk : BitAssignment dLayout) (hrk : IsRoutedKet decode rk) :
    inKetPred (IsRoutedKet decode)
        ((if isCsel then uAlignedKinCat2m1_98CselLayout else
        uAlignedKinCat2m1_98UselLayout).1.mulVec (ket rk)) := by
  cases isCsel
  · exact uAlignedKinCat2m1_98Usel_preserves_routed rk hrk
  · let Pq : Operator (2 ^ dLayout) := projOneQCompactGen scrWLayout
    change inKetPred (IsRoutedKet decode) (uAlignedKinCat2m1_98CselLayout.1.mulVec (ket rk))
    unfold uAlignedKinCat2m1_98CselLayout
    rw [(csel_conj_unitary Pq uKinAlign0Layout uKinCat2m1_98CselLayout uKinCat2m1_98UselLayout
      comm_pq.2.eq uKin2m1_98Layout_props.1 uKin2m1_98Layout_props.2.1).1,
      Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec]
    exact inKetPred_add (inKetPred_sub (inKetPred_ket hrk)
        (projOneQ_inKetPred (inKetPred_ket hrk)))
      (projOneQ_inKetPred (uAlignedKinCat2m1_98Usel_preserves_routed rk hrk))
theorem routed_wnh_inKetPred_wstate {w1 n : ℕ} [NeZero (2 ^ n)]
    {decode : Fin (2 ^ 41) → ZeroNEremSector}
    (o1 : Stage1ZeroNEremLayout w1 decode) (rTot : QRegister dLayout n) (X₁ : Operator (2 ^ n))
    (hAbsX₁ : (rTot.compose (rScrExt 0 hk0_le72_wstate)).basisOutcomeProjector 0 * X₁ = X₁)
        (ξ : BitAssignment n) :
    inKetPred (fun η ↦ IsRoutedKet decode (fun i ↦ η (rTot i)))
        (((rTot.embedUnitary (wNoHad (uStage1Clean_c70 decode))).1 * X₁).mulVec (ket ξ)) := by
  have hScrX : (rTot.compose rScrLayout).basisOutcomeProjector 0 * X₁ = X₁ := by
    rwa [← hP0_rScrExt_c70 hk0_le72_wstate rTot,
        show (rTot.compose (rCoinExt 0 hk0_le72_wstate)).basisOutcomeProjector 0 = 1 from
      matrix_ext_ket fun β ↦ by
        rw [SelectRefl.ket_basisOutcomeProjector_zero, ite_eq_left (fun j ↦ Fin.elim0 j),
            Matrix.one_mulVec], mul_one]
  have hClX : inKetPred (fun η ↦ CleanScr (fun i ↦ η (rTot i))) (X₁.mulVec (ket ξ)) := fun η hnz ↦
    Classical.byContradiction fun (hnot : ¬ ∀ i, η ((rTot.compose rScrLayout) i) = 0) ↦ hnz <| by
      simpa only [← Matrix.mulVec_mulVec, proj_zero_vec_entry (rTot.compose rScrLayout) _ η,
          ite_eq_right hnot] using
        (congrFun (congrArg (·.mulVec (ket ξ)) hScrX) ((basisBitsEquiv n).symm η)).symm
  rw [← hScrX, ← Matrix.mul_assoc, wNoHadClean_mul_rScrLayout_c70 o1 rTot, Matrix.mul_assoc, hScrX,
      ← Matrix.mulVec_mulVec]
  exact inKetPred_mulVec (rTot.embedUnitary (wNoHad o1.uLocal)).1 (fun η hScr ↦ by
    let c := outerCoinOf82 (fun i ↦ η (rTot (rLcu82Layout i)))
    let z := innerBitsOf82 (fun i ↦ η (rTot (rLcu82Layout i)))
    rw [QRegister.embedUnitary_val,
        embedMatrix_ket_eq_writeReg rTot _ η ((congrArg (wNoHad o1.uLocal).1.mulVec
        (congrArg ket
      (routedStage0_self (fun i ↦ η (rTot i))).symm)).trans (wNoHad_mulVec_ket o1 hScr c z))]
    exact inKetPred_ket ⟨fun i ↦ η (rTot i), c, z, hScr, funext fun i ↦
        DynCircExt.writeReg_apply_reg η rTot _ i⟩) hClX
theorem routed_uKin_inKetPred_wstate
    {w1 n : ℕ} [NeZero (2 ^ n)]
    {decode : Fin (2 ^ 41) → ZeroNEremSector}
    (o1 : Stage1ZeroNEremLayout w1 decode)
    (rTot : QRegister dLayout n) (isCsel : Bool) (X₁ : Operator (2 ^ n))
    (hAbsX₁ : (rTot.compose (rScrExt 0 hk0_le72_wstate)).basisOutcomeProjector 0 * X₁ = X₁)
    (ξ : BitAssignment n) :
    let Wnh := rTot.embedUnitary (wNoHad (uStage1Clean_c70 decode))
    let uKin :=
        rTot.embedUnitary (if isCsel then uAlignedKinCat2m1_98CselLayout else
        uAlignedKinCat2m1_98UselLayout)
    inKetPred (fun η ↦ IsRoutedKet decode (fun i ↦ η (rTot i)))
        ((uKin.1 * (Wnh.1 * X₁)).mulVec (ket ξ)) := by
  intro Wnh uKin
  rw [← Matrix.mulVec_mulVec]
  refine inKetPred_mulVec uKin.1 (fun η hrk δ hnz ↦ ?_)
      (routed_wnh_inKetPred_wstate o1 rTot X₁ hAbsX₁ ξ)
  let KL := (if isCsel then uAlignedKinCat2m1_98CselLayout else uAlignedKinCat2m1_98UselLayout).1
  dsimp only [uKin] at hnz
  rw [QRegister.embedUnitary_val, SelectDataBuilder.embedMatrix_mulVec_ket_sym rTot KL η,
      Finset.sum_apply] at hnz
  obtain ⟨z', _, hz'⟩ := Finset.exists_ne_zero_of_sum_ne_zero hnz
  rw [Pi.smul_apply, smul_eq_mul] at hz'
  rw [inKetPred_ket (Pred :=
      (· = DynCircExt.writeReg η rTot (basisBits dLayout z'))) rfl δ (right_ne_zero_of_mul hz'),
    show (fun i ↦ DynCircExt.writeReg η rTot (basisBits dLayout z') (rTot i)) =
        basisBits dLayout z' from
      funext (DynCircExt.writeReg_apply_reg η rTot _)]
  refine uAlignedKin2m1_98_preserves_routed_wstate isCsel _ hrk (basisBits dLayout z') ?_
  change (KL.mulVec (ket (fun i ↦ η (rTot i))))
      ((basisBitsEquiv dLayout).symm ((basisBitsEquiv dLayout) z')) ≠ 0
  rw [(basisBitsEquiv dLayout).symm_apply_apply, ket_eq_single_symm (fun i ↦ η (rTot i)),
    ← PhotochemistrySolution.SelectDataBuilder.readRegIdx_eq_of_bits rTot η _ fun i ↦
      (congrFun ((basisBitsEquiv dLayout).apply_symm_apply (fun j ↦ η (rTot j))) i).symm,
          Matrix.mulVec_single_one]
  exact left_ne_zero_of_mul hz'
theorem mkKetOpW_mul_eq_of_inKetPred_wstate {w n : ℕ} [NeZero (2 ^ n)] (rW : QRegister w n)
    (st0 : BitAssignment n → BitAssignment n) (R : Operator (2 ^ n))
    (h : ∀ ξ : BitAssignment n, inKetPred (fun β ↦ (∀ q : Fin w, β (rW q) = 0) ∧ st0 β = β)
        (R.mulVec (ket ξ))) : mkKetOpW rW st0 (fun _ ↦ 0) * R = R :=
  matrix_ext_ket fun ξ ↦ by
    rw [← Matrix.mulVec_mulVec (ket ξ) (mkKetOpW rW st0 (fun _ ↦ 0)) R,
        vec_eq_sum_ket (R.mulVec (ket ξ)), Matrix.mulVec_sum]
    refine Finset.sum_congr rfl fun β _ ↦ ?_
    if hc : R.mulVec (ket ξ) ((basisBitsEquiv n).symm β) = 0 then rw [hc, zero_smul,
        Matrix.mulVec_zero]
    else rw [Matrix.mulVec_smul, mkKetOpW_mulVec_ket, ite_eq_left (h ξ β hc).1, bitSign_zero,
        one_smul, (h ξ β hc).2]
attribute [local irreducible] routedKet in
theorem routed_clean714_zero_wstate {n : ℕ} {decode : Fin (2 ^ 41) → ZeroNEremSector}
    (rTot : QRegister dLayout n) (β : BitAssignment n)
    (hrk : IsRoutedKet decode (fun i ↦ β (rTot i)))
    (q : Fin 714) : β (((rTot.compose rPermPot103).compose rClean714Layout) q) = 0 := by
  rcases hrk with ⟨α, c0, z0, hScr, heq⟩
  change β (rTot (rPermPot103 (rClean714Layout q))) = 0;
  rw [congrFun heq (rPermPot103 (rClean714Layout q))];
  have hRng := val_rPermPot103_rClean714Layout_rng q
  exact ((validRouter_stage1 (decodeCoin := decode) hScr c0 z0).2.2.2.1 _
    (by rcases hRng with h | h | h <;> omega)).trans
    (stage1_scr_zero hScr c0 z0 (by rcases hRng with h | h | h <;> omega))

attribute [local irreducible] clampOneHot DynCircExt.writeReg routedKet in
theorem routed_clampPotBRefl_fix_wstate {n : ℕ} {decode : Fin (2 ^ 41) → ZeroNEremSector}
    (rTot : QRegister dLayout n) (β : BitAssignment n)
    (hrk : IsRoutedKet decode (fun i ↦ β (rTot i))) : clampPotBRefl rTot β = β := by
  rcases hrk with ⟨α, c0, z0, hScr, heq⟩
  have hAt (u : Wire dLayout) : β (rTot u) = routedKet decode α c0 z0 u := congrFun heq u
  have hVF := routedKet_validFlags_portB (decodeCoin := decode) hScr c0 z0
  have hOH := routedKet_oneHot_portB (decodeCoin := decode) hScr c0 z0
  have hFl : clampFlags rTot β = β := funext fun w ↦ by
    obtain ⟨_, fS, fN, fO⟩ := clampFlags_apply rTot β
    if hwS : w = rTot (wPotIsScreen rPot0Layout) then
      rw [hwS, fS, hAt, hAt]
      exact (DynCircExt.bit_cases (routedKet decode α c0 z0 (wPotIsPot rPot0Layout))).elim
        (fun hp0 ↦ by simp [hp0, (hVF.1 hp0).1]) fun hp1 ↦ by simp [hp1]
    else if hwN : w = rTot (wPotIsNN rPot0Layout) then
      rw [hwN, fN, hAt, hAt, hAt]
      exact (DynCircExt.bit_cases (routedKet decode α c0 z0 (wPotIsPot rPot0Layout))).elim
        (fun hp0 ↦ by simp [hp0, (hVF.1 hp0).2]) fun hp1 ↦
          (DynCircExt.bit_cases (routedKet decode α c0 z0 (wPotIsScreen rPot0Layout))).elim
            (fun hs0 ↦ by simp [hp1, hs0, hVF.2 hs0]) fun hs1 ↦ by simp [hp1, hs1]
    else exact fO w hwS hwN
  refine (congrArg (clampOneHot rTot) hFl).trans (funext fun w ↦ ?_)
  obtain ⟨cN, cE, cO⟩ := clampOneHot_apply rTot β
  if hwN : ∃ b, w = rTot (rBufHi rNucLayout b) then
    obtain ⟨b, rfl⟩ := hwN
    exact (DynCircExt.bit_cases (routedKet decode α c0 z0 (wPotIsNN rPot0Layout))).elim
      (fun h0 ↦ by simp [cN b, hAt, h0, ((hOH b).1 h0).symm]) fun h1 ↦ by simp [cN b, hAt, h1]
  else if hwE : ∃ b, w = rTot (rBufHi rElecLayout b) then
    obtain ⟨b, rfl⟩ := hwE
    exact (DynCircExt.bit_cases (routedKet decode α c0 z0 (wPotIsNN rPot0Layout))).elim
      (fun h0 ↦ by simp [cE b, hAt, h0]) fun h1 ↦ by simp [cE b, hAt, h1, ((hOH b).2 h1).symm]
  else exact cO w (fun b e ↦ hwN ⟨b, e⟩) (fun b e ↦ hwE ⟨b, e⟩)

theorem routed_m0Abs_and_potKin_rev_wstate
    {w1 kOut n : ℕ} [NeZero (2 ^ n)]
    {wEE : Fin 4 → ℕ} {wNN : Fin 4 → Fin 4 → ℕ} {wEN : Fin 4 → ℕ}
    {wKin : Particle_frozen → ℕ} {wIdle : ℕ}
    {decode : Fin (2 ^ 41) → ZeroNEremSector}
    {peK : BitAssignment (0 + kOut) → PotExpectFn}
    (o1 : Stage1ZeroNEremLayout w1 decode)
    (hCoin : ValidGenZeroNEremCoin wEE wNN wEN wKin wIdle decode)
    (rSub : QRegister kOut 41)
    (specK : ∀ γ : BitAssignment (0 + kOut), ReflPotSliceSpec (peK γ))
    (rTot : QRegister dLayout n) (isCsel : Bool)
    (X₁ : Operator (2 ^ n))
    (hAbsX₁ : (rTot.compose (rScrExt 0 hk0_le72_wstate)).basisOutcomeProjector 0 * X₁ = X₁) :
    let rTot' := rTot.compose rPermPot103
    let rCoin := rCoinExtOut hk0_le72_wstate rSub
    let hBand := val_rCoinExtOut_coinBand7256_wstate hk0_le72_wstate rSub
    let Wnh := rTot.embedUnitary (wNoHad (uStage1Clean_c70 decode))
    let uKin :=
        rTot.embedUnitary (if isCsel then uAlignedKinCat2m1_98CselLayout else
        uAlignedKinCat2m1_98UselLayout)
    let M0 := mkKetOpW (rTot'.compose rClean714Layout) (clampPotBRefl rTot) (fun _ ↦ 0)
    let UPot := rTot.embedUnitary (uPotReflMuxZeroNErem rCoin hBand specK isCsel)
    let s4 := stage4OuterSubUnitaryPkg_reflRev2m1_98_wstate hk0_le72_wstate rSub o1 specK hCoin
    let uStage4 :=
        if isCsel then uCselMuxWState hk0_le72_wstate rSub o1 s4 else uUselMuxWState hk0_le72_wstate
        rSub o1 s4
    M0 * (uKin.1 * (Wnh.1 * X₁)) = uKin.1 * (Wnh.1 * X₁) ∧ UPot.1 * (uKin.1 * (Wnh.1 * X₁)) =
        (rTot.embedUnitary uStage4).1 * (Wnh.1 * X₁) :=
  ⟨mkKetOpW_mul_eq_of_inKetPred_wstate ((rTot.compose rPermPot103).compose rClean714Layout)
      (clampPotBRefl rTot) _ (fun ξ β hnz ↦
    let hrk := routed_uKin_inKetPred_wstate o1 rTot isCsel X₁ hAbsX₁ ξ β hnz
    ⟨routed_clean714_zero_wstate rTot β hrk, routed_clampPotBRefl_fix_wstate rTot β hrk⟩),
   by rw [uStage4ReflRevMux2m1_98_eq_pot_mul hk0_le72_wstate rSub o1 specK hCoin isCsel,
        QRegister.embedUnitary_mul, Submonoid.coe_mul, Matrix.mul_assoc]⟩
/--
`32` -wire router public-control block `5715 .. 5746` covering `RouterCtrlSet` of both routers.
-/
def rCtrl32Layout_wstate : QRegister 32 dLayout :=
  QRegister.block 5715 32 (by rw [hDLayout_eq_7298]; omega)

theorem circ_comm_embedMatrix_wstate {m n : ℕ} (rC : QRegister m n) (M : Operator (2 ^ m)) :
    ∀ {c : Circuit n}, UnembedO3Bridge.CircWires (fun w ↦ ∀ j : Fin m, w ≠ rC j) c →
      c.eval.1 * rC.embedMatrix M = rC.embedMatrix M * c.eval.1 :=
  fun {_} hc ↦ circ_comm_embedMatrix_c70 rC M hc

def ctrlBits32Layout_wstate (γ : BitAssignment 32) : BitAssignment dLayout :=
    DynCircExt.writeReg (fun _ ↦ 0) rCtrl32Layout_wstate γ
theorem routerCtrlPair_eq_ctrlBits32_wstate {n : ℕ} (rTot : QRegister dLayout n)
    (β : BitAssignment n) :
    let rN := rTot.compose rNucSub; let rE := rTot.compose rElecSub
    let γ : BitAssignment 32 := fun j ↦ β ((rTot.compose rCtrl32Layout_wstate) j)
    (routerCtrlLo rN β = routerCtrlLo rNucLayout (ctrlBits32Layout_wstate γ) ∧
     routerCtrlHi rN β = routerCtrlHi rNucLayout (ctrlBits32Layout_wstate γ)) ∧
    (routerCtrlLo rE β = routerCtrlLo rElecLayout (ctrlBits32Layout_wstate γ) ∧
     routerCtrlHi rE β = routerCtrlHi rElecLayout (ctrlBits32Layout_wstate γ)) := by
  intro rN rE γ
  have hN (i : Fin (routerWidth 47 6)) (hi : i.val < 14) : β (rN i) =
      ctrlBits32Layout_wstate γ (rNucLayout i) := by
    rw [show rN i =
        rTot (rNucLayout i) from congrArg rTot.wires (validMuxD1Stage2Regs_sub.pubNuc i (by omega)),
      show rNucLayout i = rCtrl32Layout_wstate ⟨i.val, by omega⟩ from
        Fin.ext (show (nucRouterWireFn i).val = 5715 +
            i.val by rw [val_nucRouterWireFn, ite_eq_left hi])]
    exact (DynCircExt.writeReg_apply_reg (fun _ ↦ 0) rCtrl32Layout_wstate γ _).symm
  have hE (j : Fin (routerWidth 187 8)) (hj18 : j.val < 18) : β (rE j) =
      ctrlBits32Layout_wstate γ (rElecLayout j) := by
    rw [show rE j =
        rTot (rElecLayout j) from congrArg rTot.wires (validMuxD1Stage2Regs_sub.pubElec j
        (by omega)),
      show rElecLayout j = rCtrl32Layout_wstate ⟨14 + j.val, by omega⟩ from Fin.ext
        ((show (elecRouterWireFn j).val = 5729 +
            j.val by rw [val_elecRouterWireFn, ite_eq_left hj18]).trans
          (show 5729 + j.val = 5715 + (14 + j.val) by omega))]
    exact (DynCircExt.writeReg_apply_reg (fun _ ↦ 0) rCtrl32Layout_wstate γ _).symm
  have hCtrlLt {M D : ℕ} {u : Fin (routerWidth M D)}
      (hu : RouterCtrlSet (QRegister.whole (routerWidth M D)) u) : u.val < 2 + 2 * D := by
    rcases hu with rfl | rfl | ⟨d, rfl⟩ | ⟨d, rfl⟩ <;> unfold routerWidth <;> dsimp <;> omega
  exact ⟨routerCtrlPair_eq_of_eq (QRegister.whole _) (α := fun i ↦ β (rN i))
      (β := fun i ↦ ctrlBits32Layout_wstate γ (rNucLayout i)) fun u hu ↦ hN u (hCtrlLt hu),
    routerCtrlPair_eq_of_eq (QRegister.whole _) (α := fun j ↦ β (rE j))
      (β := fun j ↦ ctrlBits32Layout_wstate γ (rElecLayout j)) fun u hu ↦ hE u (hCtrlLt hu)⟩
def copyVecAuxBits_wstate {M n : ℕ} (qB : Fin 24 → Wire n) (cVec : Fin M → ZMod 2)
    (wTgt : Fin 24 → Fin M → Wire n) : (m : ℕ) → m ≤ 24 → BitAssignment n → BitAssignment n
  | 0, _, β => β
  | m + 1, hm, β =>
      let prev := copyVecAuxBits_wstate qB cVec wTgt m (Nat.le_of_succ_le hm) β
      fixedFanoutBits M (prev (qB ⟨m, hm⟩)) cVec (wTgt ⟨m, hm⟩) prev

theorem fixedFanoutVecCirc_24_mulVec_ket_wstate {M n : ℕ} (qB : Fin 24 → Wire n)
    (cVec : Fin M → ZMod 2) (wTgt : Fin 24 → Fin M → Wire n) (hbt : ∀ (k : Fin 24)
    (p : Fin M), qB k ≠ wTgt k p) (β : BitAssignment n) :
    (fixedFanoutVecCirc M 24 qB cVec wTgt hbt).eval.1.mulVec (ket β) =
    ket (copyVecAuxBits_wstate qB cVec wTgt 24 le_rfl β) := by
  suffices h : ∀ (m : ℕ) (hm : m ≤ 24),
      (fixedFanoutVecCirc M m (fun k : Fin m ↦ qB ⟨k.val, Nat.lt_of_lt_of_le k.isLt hm⟩)
        cVec (fun k : Fin m ↦ wTgt ⟨k.val, Nat.lt_of_lt_of_le k.isLt hm⟩)
        (fun k p ↦ hbt ⟨k.val, Nat.lt_of_lt_of_le k.isLt hm⟩ p)).eval.1.mulVec (ket β) =
      ket (copyVecAuxBits_wstate qB cVec wTgt m hm β) from h 24 le_rfl
  intro m
  induction m with
  | zero =>
      intro _
      dsimp only [fixedFanoutVecCirc, copyVecAuxBits_wstate]
      rw [Circuit.eval_identity, Submonoid.coe_one, Matrix.one_mulVec]
  | succ m ihm =>
      exact fun hm ↦ by
        simpa only [fixedFanoutVecCirc, copyVecAuxBits_wstate, Fin.val_last, Fin.val_castSucc,
          DynCircExt.eval_seq_mulVec,
              ihm (Nat.le_of_succ_le hm)] using fixedFanoutCirc_mulVec_ket M _ cVec _ _ _
theorem copyVecAuxBits_of_ne_tgt_wstate {M n : ℕ} (qB : Fin 24 → Wire n) (cVec : Fin M → ZMod 2)
    (wTgt : Fin 24 → Fin M → Wire n) (β : BitAssignment n) (w : Wire n)
    (hne : ∀ (k : Fin 24) (p : Fin M), w ≠ wTgt k p) :
    ∀ (m : ℕ) (hm : m ≤ 24), copyVecAuxBits_wstate qB cVec wTgt m hm β w = β w
  | 0, _ => rfl
  | m + 1, hm =>
      (fixedFanoutBits_of_ne_tgt M _ cVec (wTgt ⟨m, hm⟩) _ w (hne ⟨m, hm⟩)).trans
        (copyVecAuxBits_of_ne_tgt_wstate qB cVec wTgt β w hne m (Nat.le_of_succ_le hm))
theorem fixedFanoutBits_add_diff_wstate {n : ℕ} :
    ∀ (M : ℕ) (srcVal : ZMod 2) (cVec : Fin M → ZMod 2) (wTgt : Fin M → Wire n)
      (β : BitAssignment n) (d : Wire n → ZMod 2),
      (∀ p : Fin M, d (wTgt p) = 0) →
      fixedFanoutBits M srcVal cVec wTgt (fun w ↦ β w + d w) =
        fun w ↦ fixedFanoutBits M srcVal cVec wTgt β w + d w
  | 0, _, _, _, _, _, _ => rfl
  | M + 1, srcVal, cVec, wTgt, β, d, hd => by
      dsimp only [fixedFanoutBits]
      rw [fixedFanoutBits_add_diff_wstate M srcVal (fun p ↦ cVec p.castSucc)
          (fun p ↦ wTgt p.castSucc) β d (fun p ↦ hd p.castSucc)]
      split_ifs
      · refine funext fun w ↦ ?_
        if hw : w = wTgt (Fin.last M) then simp [hw,
            hd (Fin.last M)] else simp [Function.update_of_ne hw]
      · rfl
theorem copyVecAuxBits_add_diff_wstate {M n : ℕ} (qB : Fin 24 → Wire n) (cVec : Fin M → ZMod 2)
    (wTgt : Fin 24 → Fin M → Wire n) (β : BitAssignment n) (d : Wire n → ZMod 2)
    (hBNeT : ∀ (b k : Fin 24) (p : Fin M), qB b ≠ wTgt k p)
    (hdB : ∀ b : Fin 24, d (qB b) = 0)
    (hdT : ∀ (b : Fin 24) (p : Fin M), d (wTgt b p) = 0) :
    ∀ (m : ℕ) (hm : m ≤ 24),
      copyVecAuxBits_wstate qB cVec wTgt m hm (fun w ↦ β w + d w) =
        fun w ↦ copyVecAuxBits_wstate qB cVec wTgt m hm β w + d w
  | 0, _ => rfl
  | m + 1, hm => by
      dsimp only [copyVecAuxBits_wstate];
      rw [copyVecAuxBits_add_diff_wstate qB cVec wTgt β d hBNeT hdB hdT m (Nat.le_of_succ_le hm)]
      have hPrevR : copyVecAuxBits_wstate qB cVec wTgt m (Nat.le_of_succ_le hm) β (qB ⟨m, hm⟩) =
          β (qB ⟨m, hm⟩) :=
          copyVecAuxBits_of_ne_tgt_wstate qB cVec wTgt β (qB ⟨m, hm⟩)
          (fun k p ↦ hBNeT ⟨m, hm⟩ k p) m (Nat.le_of_succ_le hm)
      have hPrevB : copyVecAuxBits_wstate qB cVec wTgt m (Nat.le_of_succ_le hm) β (qB ⟨m, hm⟩) +
          d (qB ⟨m, hm⟩) = β (qB ⟨m, hm⟩) := by rw [hdB ⟨m, hm⟩, add_zero, hPrevR]
      dsimp only; rw [hPrevB, hPrevR];
      exact fixedFanoutBits_add_diff_wstate M _ cVec (wTgt ⟨m, hm⟩) _ d (hdT ⟨m, hm⟩)
section
attribute [local irreducible] clampOneHot
theorem coordOfReg24_congr_wstate {n : ℕ} (r24 : QRegister 24 n) {δ₁ δ₂ : BitAssignment n}
    (h : ∀ k : Fin 24, δ₁ (r24 k) = δ₂ (r24 k)) : coordOfReg24 r24 δ₁ =
    coordOfReg24 r24 δ₂ := by funext ax; dsimp only [coordOfReg24]; congr 1; funext k; exact h _
theorem potRefl4_congr_of_eq_wstate {W n : ℕ} {potExpect : PotExpectFn}
    (spec : ReflPotSliceSpec potExpect) (isCsel : Bool)
    (r : QRegister (146 + W) n) {δ₁ δ₂ : BitAssignment n}
    (h : ∀ i : Fin 146, δ₁ (r ⟨i.val, by omega⟩) = δ₂ (r ⟨i.val, by omega⟩)) :
    potGateActive4 isCsel r δ₁ = potGateActive4 isCsel r δ₂ ∧
    potOracleCoinEval spec.coinSwap r δ₁ = potOracleCoinEval spec.coinSwap r δ₂ ∧
    potReflPh4 spec isCsel r δ₁ = potReflPh4 spec isCsel r δ₂ := by
  have hk (k : ℕ) (hk : k < 146) : δ₁ (r ⟨k, by omega⟩) = δ₂ (r ⟨k, by omega⟩) := h ⟨k, hk⟩
  have hNA := coordOfReg24_congr_wstate (rPotNucA r) fun j ↦ hk (9 + j.val) (by omega)
  have hNB := coordOfReg24_congr_wstate (rPotNucB r) fun j ↦ hk (33 + j.val) (by omega)
  have hEA := coordOfReg24_congr_wstate (rPotElecA r) fun j ↦ hk (57 + j.val) (by omega)
  have hEB := coordOfReg24_congr_wstate (rPotElecB r) fun j ↦ hk (81 + j.val) (by omega)
  have hC : (fun m : Fin 41 ↦ δ₁ (rPotCoin41 r m)) = (fun m ↦ δ₂ (rPotCoin41 r m)) := funext fun m ↦
      hk (105 + m.val) (by omega)
  exact ⟨by simp only [potGateActive4, wPotLocQ, wPotIsPot, hk 0 (by decide), hk 2 (by decide)],
    by simp only [potOracleCoinEval, wPotIsScreen, wPotIsNN, wPotSp1B0, wPotSp1B1, wPotSp2B0,
         wPotSp2B1,
         hk 1 (by decide), hk 4 (by decide), hk 5 (by decide), hk 6 (by decide), hk 7 (by decide),
             hk 8 (by decide),
         hNA, hNB, hEA, hEB, hC],
    by simp only [potReflPh4, potOracleBitEval, wPotLocQ, wPotIsPot, wPotIsScreen, wPotIsNN,
         wPotSp1B0, wPotSp1B1, wPotSp2B0, wPotSp2B1, hk 0 (by decide), hk 1 (by decide),
             hk 2 (by decide),
         hk 4 (by decide), hk 5 (by decide), hk 6 (by decide), hk 7 (by decide), hk 8 (by decide),
             hNA, hNB, hEA, hEB, hC]⟩
end
/--
Fine-grained H/CNOT support separating Hadamard wires, CNOT controls, and CNOT targets so
circuits sharing CNOT targets with disjoint controls commute.
-/
inductive HCNOTCtrlTgt {n : ℕ} (HSet CSet TSet : Wire n → Prop) : Circuit n → Prop where
  | id : HCNOTCtrlTgt HSet CSet TSet .identity
  | seq {c₁ c₂} : HCNOTCtrlTgt HSet CSet TSet c₁ → HCNOTCtrlTgt HSet CSet TSet c₂ →
      HCNOTCtrlTgt HSet CSet TSet (c₁ ;;ᶜ c₂)
  | h {q} : HSet q → HCNOTCtrlTgt HSet CSet TSet (Circuit.H q)
  | cnot {c t} (hct : c ≠ t) : CSet c → TSet t → HCNOTCtrlTgt HSet CSet TSet (Circuit.CNOT c t hct)

theorem HCNOTCtrlTgt.comm_cnotOnly {n : ℕ} {HSet C₁ T₁ C₂ T₂ : Wire n → Prop} {c₁ c₂ : Circuit n}
    (h₁ : HCNOTCtrlTgt HSet C₁ T₁ c₁) (h₂ : HCNOTCtrlTgt (fun _ ↦ False) C₂ T₂ c₂)
    (dH : ∀ q, HSet q → ¬ C₂ q ∧ ¬ T₂ q) (dC₁ : ∀ u, C₁ u → ¬ T₂ u) (dC₂ : ∀ u, C₂ u → ¬ T₁ u) :
    c₁.eval.1 * c₂.eval.1 = c₂.eval.1 * c₁.eval.1 := by
  induction h₂ with
  | id => simp [Circuit.eval_identity]
  | seq _ _ ihA ihB =>
      rw [Circuit.eval_seq, Submonoid.coe_mul, ← Matrix.mul_assoc, ihB, Matrix.mul_assoc, ihA,
          ← Matrix.mul_assoc]
  | h hq => exact False.elim hq
  | @cnot c₂w t₂w hct₂ hc₂ ht₂ =>
      induction h₁ with
      | id => simp [Circuit.eval_identity]
      | seq _ _ ih₁ ih₂ =>
          rw [Circuit.eval_seq, Submonoid.coe_mul, Matrix.mul_assoc, ih₁, ← Matrix.mul_assoc, ih₂,
              Matrix.mul_assoc]
      | @h qw hq =>
          exact (HCNOTSupportedIn.h (S := fun w ↦ w = qw) rfl).comm
            (HCNOTSupportedIn.cnot (S := fun w ↦ w = c₂w ∨ w = t₂w) hct₂ (Or.inl rfl) (Or.inr rfl))
            fun u e1 e2 ↦
                e2.elim (fun h ↦ (dH u (e1 ▸ hq)).1 (h ▸ hc₂))
                (fun h ↦ (dH u (e1 ▸ hq)).2 (h ▸ ht₂))
      | @cnot c₁w t₁w hct₁ hc₁ ht₁ =>
          refine matrix_ext_ket fun β ↦ ?_
          rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ket_CNOT, ket_CNOT, ket_CNOT,
              ket_CNOT,
            Function.update_of_ne fun (e : c₁w = t₂w) ↦ dC₁ c₁w hc₁ (e ▸ ht₂),
            Function.update_of_ne fun (e : c₂w = t₁w) ↦ dC₂ c₂w hc₂ (e ▸ ht₁)]
          if htt : t₁w = t₂w then
            subst htt
            simp only [Function.update_self, Function.update_idem, add_assoc, add_comm (β c₂w)
                (β c₁w)]
          else rw [Function.update_of_ne htt, Function.update_of_ne (Ne.symm htt),
              Function.update_comm (Ne.symm htt)]

theorem hcnotCtrlTgt_fixedFanout {n : ℕ} {CSet TSet : Wire n → Prop} :
    ∀ (M : ℕ) (qB : Wire n) (cVec : Fin M → ZMod 2) (wTgt : Fin M → Wire n)
      (hbt : ∀ p, qB ≠ wTgt p),
      CSet qB → (∀ p, TSet (wTgt p)) →
      HCNOTCtrlTgt (fun _ ↦ False) CSet TSet (fixedFanoutCirc M qB cVec wTgt hbt)
  | 0, _, _, _, _, _, _ => .id
  | M + 1, qB, cVec, wTgt, hbt, hC, hT => by
      dsimp only [fixedFanoutCirc]
      refine .seq (hcnotCtrlTgt_fixedFanout M qB _ _ _ hC (fun p ↦ hT p.castSucc)) ?_
      split_ifs
      · exact .cnot _ hC (hT _)
      · exact .id

theorem hcnotCtrlTgt_mono_H {n : ℕ} {H₁ H₂ CSet TSet : Wire n → Prop} {c : Circuit n}
    (hH : ∀ u, H₁ u → H₂ u) (hc : HCNOTCtrlTgt H₁ CSet TSet c) : HCNOTCtrlTgt H₂ CSet TSet c := by
  exact hc.rec .id (fun _ _ ↦ .seq) (fun hh ↦ .h (hH _ hh)) fun hct ↦ .cnot hct

theorem hcnotCtrlTgt_fixedBellVec {M n : ℕ} {HSet TSet : Wire n → Prop} :
    ∀ (m : ℕ) (qH : Fin m → Wire n) (cVec : Fin M → ZMod 2) (wTgt : Fin m → Fin M → Wire n)
      (hht : ∀ k p, qH k ≠ wTgt k p),
      (∀ k, HSet (qH k)) → (∀ k p, TSet (wTgt k p)) →
      HCNOTCtrlTgt HSet HSet TSet (fixedBellVecCirc M m qH cVec wTgt hht)
  | 0, _, _, _, _, _, _ => .id
  | m + 1, _, cVec, _, _, hH, hT => by
      dsimp only [fixedBellVecCirc, fixedBell1Circ]
      exact .seq (hcnotCtrlTgt_fixedBellVec m _ cVec _ _ (fun k ↦ hH k.castSucc)
          (fun k p ↦ hT k.castSucc p)) (.seq (.h (hH _)) (hcnotCtrlTgt_mono_H (fun _ ↦ False.elim)
          (hcnotCtrlTgt_fixedFanout M _ cVec _ _ (hH _) (hT _))))
section
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt (bit_cases eval_seq_mulVec
  ket_CNOT ket_TOFF ket_X ket_projector_one ket_projector_zero localIdx qAssign_obs_map_val)
attribute [local reducible] totDimCompactGen
attribute [local irreducible] systemQubits_frozen ancWOfScr CleanWorkStep phaseFlipUnitary
    uRouterSwapConj uSwapHi24
def sLocalReflOuterSub2m1_wstate {kExt kOut w1 : ℕ} {wEE : Fin 4 → ℕ} {wNN : Fin 4 → Fin 4 → ℕ}
    {wEN : Fin 4 → ℕ} {wKin : Particle_frozen → ℕ} {wIdle : ℕ}
    {decode : Fin (2 ^ 41) → ZeroNEremSector} {peKOut : BitAssignment (kExt + kOut) → PotExpectFn}
    (hk : kExt ≤ 72) (rSub : QRegister kOut 41) (o1 : Stage1ZeroNEremLayout w1 decode)
    (specKOut : ∀ γω : BitAssignment (kExt + kOut), ReflPotSliceSpec (peKOut γω))
    (hCoin : ValidGenZeroNEremCoin wEE wNN wEN wKin wIdle decode) : LocalUnitary dLayout :=
  ⟨sReflSliceOuterSub2m1_wstate hk rSub o1 specKOut hCoin⟩

/-- `LocalUnitary dLayout` wrapper around `cselReflRevSliceOuterSub2m1_98_wstate`. -/
def cselLocalReflRevOuterSub2m1_98_wstate {kExt kOut w1 : ℕ} {wEE : Fin 4 → ℕ}
    {wNN : Fin 4 → Fin 4 → ℕ} {wEN : Fin 4 → ℕ} {wKin : Particle_frozen → ℕ} {wIdle : ℕ}
    {decode : Fin (2 ^ 41) → ZeroNEremSector} {peKOut : BitAssignment (kExt + kOut) → PotExpectFn}
    (hk : kExt ≤ 72) (rSub : QRegister kOut 41) (o1 : Stage1ZeroNEremLayout w1 decode)
    (specKOut : ∀ γω : BitAssignment (kExt + kOut), ReflPotSliceSpec (peKOut γω))
    (hCoin : ValidGenZeroNEremCoin wEE wNN wEN wKin wIdle decode) : LocalUnitary dLayout :=
  ⟨cselReflRevSliceOuterSub2m1_98_wstate hk rSub o1 specKOut hCoin⟩

/-- `LocalUnitary dLayout` wrapper around `uselReflRevSliceOuterSub2m1_98_wstate`. -/
def uselLocalReflRevOuterSub2m1_98_wstate {kExt kOut w1 : ℕ} {wEE : Fin 4 → ℕ}
    {wNN : Fin 4 → Fin 4 → ℕ} {wEN : Fin 4 → ℕ} {wKin : Particle_frozen → ℕ} {wIdle : ℕ}
    {decode : Fin (2 ^ 41) → ZeroNEremSector} {peKOut : BitAssignment (kExt + kOut) → PotExpectFn}
    (hk : kExt ≤ 72) (rSub : QRegister kOut 41) (o1 : Stage1ZeroNEremLayout w1 decode)
    (specKOut : ∀ γω : BitAssignment (kExt + kOut), ReflPotSliceSpec (peKOut γω))
    (hCoin : ValidGenZeroNEremCoin wEE wNN wEN wKin wIdle decode) : LocalUnitary dLayout :=
    ⟨uselReflRevSliceOuterSub2m1_98_wstate hk rSub o1 specKOut hCoin⟩
end
end
end QuantumComputation.Specs.PhotochemistrySolution.WStateWalkSeam

end
