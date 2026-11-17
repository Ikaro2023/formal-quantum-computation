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

public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.HGadgetSympQromAux

@[expose] public section

/-! # Grouped Hadamard-Gadget Symplectic `14`-Plane QROM Loader
`(60 + 2 * R + 2 * G)`-`T`, `0`-`TOFF`, `33 ≤ sScr` loader on `keep9Symp14Spec` (Babbush et al.,
*Phys. Rev. X* **8**, 041015, 2018; Gidney, *Quantum* **2**, 74, 2018; Low, Kliuchnikov, and
Schaeffer, *Quantum* **8**, 1375, 2024, DOI: `10.22331/q-2024-06-17-1375`). -/
namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.HGadgetSympQrom
open QuantumComputation.Specs QuantumComputation.Specs.P450
section HGadgetImpl
open Operator QProg Matrix Circuit Real HermitianMat BlockEncodingCore BlockEncodingCircuit
  QuantumComputation.Specs QuantumComputation.Specs.P450 CoherentAlias AliasPrep
  Mobius126OneHot MidReflCtxRetain StepBound148Borrow
  Tuned162ScheduledSympQrom21 Tuned162StepSympAnfQrom21 StepAnfAndCoin14Core StepKeep9Symp14Data
open _root_.QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.StepOuter8Pi145Outer
  (predProj_mulVec_ket)
open _root_.Function (update update_of_ne update_self update_idem update_eq_self)
open CircuitModular.UnsignedGivens (evolve_CNOT_ket)
open _root_.QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.GroupUnary
  (predProj predProj_conjTranspose)
open _root_.QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.CompactOuterAlias
  (eval_h_mul_self)
open _root_.QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.XMeasCircuit
  (ket_H sqrtHalf sqrtHalf_mul_sqrtHalf bitSign_zero xorWireUnitary
  xorWireUnitary_mulVec_ket phaseFlipUnitary phaseFlipUnitary_mulVec_ket xMeasUnloadWireDyn
  count_xMeasUnloadWireDyn_toff count_xMeasUnloadWireDyn_t wp_xMeasUnloadWireDyn_update_self
  cleanFinsetProj restrictAssertionToCleanFinset restrictAssertionToCleanFinset_coe
  restrictAssertionToCleanFinset_wp_xorWireUnitary_xMeasUnloadWireDyn)
open _root_.QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.SelectSwapQROM
  (zeroProjOn zeroProjOn_mulVec_ket
  zeroProjOn_conjTranspose bitSign bitSign_add bit_cases basisBits_symm ket_Z czCircuit
  ket_czCircuit czMaskCircuit count_czMaskCircuit_toff count_czMaskCircuit_t ket_czMaskCircuit
  monoEval monoEval_zero anfCoeffs sum_anfCoeffs_mul_monoEval disjoint_image_of_disjointWires)
open scoped Matrix BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator Circuit.Notation
/-- Loop executing groups `0 .. n - 1` (`n ≤ G`). -/
def grpsLoopD {Var : Type} {R G N : ℕ} (v :
  Var) (P : HGadgetSymp14Plan R G) (M : MidLayout N) : (n : ℕ) → n ≤ G → DynamicCircuit Var N
  | 0, _ => .circuit .identity
  | n + 1, hn => .seq (grpsLoopD v P M n (Nat.le_of_succ_le hn)) (grpStepD v P ⟨n, hn⟩ M)
@[simp] theorem count_grpsLoopDyn_toff {Var : Type} {R G N : ℕ} (v : Var) (P : HGadgetSymp14Plan R
  G) (M : MidLayout N) : ∀ (n : ℕ) (hn : n ≤ G), (grpsLoopD v P M n hn).count .TOFF = 0
  | 0, _ => rfl
  | n + 1, hn => by
      simp [grpsLoopD, DynamicCircuit.count, count_grpsLoopDyn_toff v P M n (Nat.le_of_succ_le hn)]
theorem count_grpsLoopDyn_t {Var : Type} {R G N : ℕ} (v : Var) (P : HGadgetSymp14Plan R G) (M :
  MidLayout N) : ∀ (n : ℕ) (hn : n ≤ G), (grpsLoopD v P M n hn).count .T = 2 * prefLen P.groupLen n
  hn + 2 * n
  | 0, _ => rfl
  | n + 1, hn => by
      simp only [grpsLoopD, DynamicCircuit.count, count_grpStepDyn_t, count_grpsLoopDyn_t v P M n
        (Nat.le_of_succ_le hn), prefLen]
      omega
/-- Raw prefix XOR of groups `0 .. n - 1` (`n ≤ G`) on plane `k` at `γ`. -/
def rGrpsP {R G N : ℕ}
  (P : HGadgetSymp14Plan R G) (k : Fin 14) (M : MidLayout N) (γ : BitAssignment N) : (n : ℕ) → n ≤ G
  → Bool
  | 0, _ => false
  | n + 1, hn =>
      xor (rGrpsP P k M γ n (Nat.le_of_succ_le hn))
        (P.groupW ⟨n, hn⟩ k && rgBit P ⟨n, hn⟩ M γ)
/-- Raw prefix carry phase `∑_{i < n} b2z (rgCarry i)` (`n ≤ G`). -/
def rCarryP {R G N : ℕ} (P :
  HGadgetSymp14Plan R G) (M : MidLayout N) (γ : BitAssignment N) : (n : ℕ) → n ≤ G → ZMod 2
  | 0, _ => 0
  | n + 1, hn => rCarryP P M γ n (Nat.le_of_succ_le hn) + b2z (rgCarry P ⟨n, hn⟩ M γ)
theorem wpZeroSet_grpsLoopDyn {Var : Type} [Fintype Var] [DecidableEq Var] {R G N : ℕ} (v : Var) (P
  : HGadgetSymp14Plan R G) (M : MidLayout N) (S : Finset (Wire N)) (hwS : M.wG ∈ S) : ∀ (n : ℕ) (hn
  : n ≤ G), WpZeroSet v S (diagKetUnitary fun γ ↦ rCarryP P M γ n hn + ∑ k : Fin 14, γ (M.rOut k) *
  b2z (rGrpsP P k M γ n hn)) (grpsLoopD v P M n hn)
  | 0, _ => by
      rw [grpsLoopD]
      refine WpZeroSet.congr_unitary (WpZeroSet.of_circuit v S .identity rfl) fun γ _ ↦ ?_
      rw [Circuit.eval_identity, Submonoid.coe_one, one_mulVec, ket_sdk_eq γ,
        diagKetUnitary_mulVec_ket]
      simp [rCarryP, rGrpsP, b2z]
  | n + 1, hn => by
      rw [grpsLoopD]
      have ih := wpZeroSet_grpsLoopDyn v P M S hwS n (Nat.le_of_succ_le hn)
      have hStep := wpZeroSet_grpStepDyn v P ⟨n, hn⟩ M S hwS
      refine WpZeroSet.congr_unitary (WpZeroSet.seq_diag_left ih hStep) fun γ _ ↦ ?_
      rw [Submonoid.coe_mul, ← mulVec_mulVec, ket_sdk_eq γ, diagKetUnitary_mulVec_ket, mulVec_smul,
        diagKetUnitary_mulVec_ket, diagKetUnitary_mulVec_ket, smul_smul, ← bitSign_add]
      refine congrArg (· • SelectSwapQROM.ket γ) (congrArg bitSign ?_)
      have hSum : b2z (rgBit P ⟨n, hn⟩ M γ) * ∑ k : Fin 14, b2z (P.groupW ⟨n, hn⟩ k) * γ (M.rOut k)
        = ∑ k : Fin 14, γ (M.rOut k) * (b2z (P.groupW ⟨n, hn⟩ k) * b2z (rgBit P ⟨n, hn⟩ M γ)) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun _ _ ↦ by ring
      simp only [rgPhase, rCarryP, rGrpsP, b2z_xor, b2z_and, mul_add, Finset.sum_add_distrib, hSum]
      ring
/-- Raw diagonal bit on plane `k` at `γ`. -/
def rDiagB {R G N : ℕ} (P : HGadgetSymp14Plan R G) (k :
  Fin 14) (M : MidLayout N) (γ : BitAssignment N) : Bool := evStep (vEnv M γ) (rcColAff (P.rowDiag
  k) (P.colDiag k))
/-- Mapped diagonal affine form on plane `k`. -/
def diagAff {R G N : ℕ} (P : HGadgetSymp14Plan R G)
  (M : MidLayout N) (k : Fin 14) : AffForm (CtrlWire N (M.rOut k)) := mapAff (vCtrl M.rHot M.rMono
  (M.rOut k) (fun c ↦ M.hHotOut c k) (fun u ↦ M.hMonoOut u k)) (rcColAff (P.rowDiag k) (P.colDiag
  k))
/-- `0-T`, `0-TOFF` row + column diagonal `14`-plane CZ loop (`m ≤ 14`). -/
def diagCirc {R G N : ℕ}
  (P : HGadgetSymp14Plan R G) (M : MidLayout N) : (m : ℕ) → m ≤ 14 → Circuit N
  | 0, _ => .identity
  | m + 1, hm =>
      diagCirc P M m (Nat.le_of_succ_le hm) ;;ᶜ
        czStepC (M.rOut ⟨m, hm⟩) (diagAff P M ⟨m, hm⟩).1 (diagAff P M ⟨m, hm⟩).2
@[simp] theorem count_diagCirc_toff {R G N : ℕ} (P : HGadgetSymp14Plan R G) (M : MidLayout N) : ∀ (m
  : ℕ) (hm : m ≤ 14), (diagCirc P M m hm).count .TOFF = 0
  | 0, _ => rfl
  | m + 1, hm => by simp [diagCirc, count_diagCirc_toff P M m (Nat.le_of_succ_le hm)]
@[simp] theorem count_diagCirc_t {R G N : ℕ} (P : HGadgetSymp14Plan R G) (M : MidLayout N) : ∀ (m :
  ℕ) (hm : m ≤ 14), (diagCirc P M m hm).count .T = 0
  | 0, _ => rfl
  | m + 1, hm => by simp [diagCirc, count_diagCirc_t P M m (Nat.le_of_succ_le hm)]
theorem ket_diagCirc {R G N : ℕ} (P : HGadgetSymp14Plan R G) (M : MidLayout N) (γ : BitAssignment N)
  : ∀ (m : ℕ) (hm : m ≤ 14), (diagCirc P M m hm).eval.1.mulVec (XMeasCircuit.ket γ) = bitSign (∑ j :
  Fin m, γ (M.rOut ⟨j.val, j.isLt.trans_le hm⟩) * b2z (rDiagB P ⟨j.val, j.isLt.trans_le hm⟩ M γ)) •
  QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.XMeasCircuit.ket γ
  | 0, _ => by
      rw [diagCirc, Circuit.eval_identity, Submonoid.coe_one, one_mulVec, Fin.sum_univ_zero,
        bitSign_zero2, one_smul]
  | m + 1, hm => by
      set aff := diagAff P M ⟨m, hm⟩
      have hStep := ket_czStep_upd (M.rOut ⟨m, hm⟩) aff.1 aff.2 γ (z2b (γ (M.rOut ⟨m, hm⟩)))
      rw [b2z_z2b, update_eq_self, b2z_and, b2z_z2b] at hStep
      have hAff : evStep (fun c ↦ z2b (γ c.1)) (aff.1, aff.2) = rDiagB P ⟨m, hm⟩ M γ := by
        change evStep (fun c ↦ z2b (γ c.1)) (diagAff P M ⟨m, hm⟩) = _
        dsimp only [diagAff]
        rw [evalStep_map, ctrl_v157]
        rfl
      rw [diagCirc, eval_seq_mv, ket_diagCirc P M γ m (Nat.le_of_succ_le hm), mulVec_smul, hStep,
        hAff, smul_smul, ← bitSign_add, Fin.sum_univ_castSucc]
      rfl
/-- `(2 * R + 2 * G)`-`T` diagonal mid-body. -/
def midDyn {Var : Type} {R G N : ℕ} (v : Var) (P :
  HGadgetSymp14Plan R G) (M : MidLayout N) : DynamicCircuit Var N := .seq (grpsLoopD v P M G le_rfl)
  (.circuit (diagCirc P M 14 le_rfl ;;ᶜ fix128C M.rHot M.rMono M.hHotMono (totPhi P)))
@[simp] theorem count_midDyn_toff {Var R G N} (v : Var) (P : HGadgetSymp14Plan R G) (M : MidLayout
  N) : (midDyn v P M).count .TOFF = 0 := by simp [midDyn, DynamicCircuit.count]
@[simp] theorem count_midDyn_t {Var R G N} (v : Var) (P : HGadgetSymp14Plan R G) (M : MidLayout N) :
  (midDyn v P M).count .T = 2 * R + 2 * G := by
  simp [midDyn, DynamicCircuit.count, count_grpsLoopDyn_t, pref_sum, P.sum_groupLen]
/-- Raw `14`-plane Boolean word on `γ`. -/
def rMidW {R G N : ℕ} (P : HGadgetSymp14Plan R G) (M :
  MidLayout N) (γ : BitAssignment N) (k : Fin 14) : Bool := xor (rGrpsP P k M γ G le_rfl) (rDiagB P
  k M γ)
/-- Raw residual carry-mismatch phase on `γ`. -/
def rDelS2 {R G N : ℕ} (P : HGadgetSymp14Plan R G)
  (M : MidLayout N) (γ : BitAssignment N) : ZMod 2 := rCarryP P M γ G le_rfl + rFixP M.rHot M.rMono
  (totPhi P) γ
/-- Raw diagonal phase of `midDyn` on `γ`. -/
def rMidP {R G N : ℕ} (P : HGadgetSymp14Plan R G) (M :
  MidLayout N) (γ : BitAssignment N) : ZMod 2 := rDelS2 P M γ + ∑ k : Fin 14, γ (M.rOut k) * b2z
  (rMidW P M γ k)
theorem rawMidWord_upd {R G N : ℕ} (P : HGadgetSymp14Plan R G) (M : MidLayout N) {w : Wire N} (hHot
  : ∀ c, M.rHot c ≠ w) (hMono : ∀ u, M.rMono u ≠ w) (β : BitAssignment N) (b : ZMod 2) : rMidW P M
  (update β w b) = rMidW P M β := by
  funext k
  dsimp only [rMidW, rDiagB]
  rw [v157_upd M hHot hMono]
  congr 1
  suffices ∀ n hn, rGrpsP P k M (update β w b) n hn =
      rGrpsP P k M β n hn from this G le_rfl
  intro n hn
  induction n with
  | zero => rfl
  | succ _ ihm => simp only [rGrpsP, ihm (Nat.le_of_succ_le hn), rgBit, v157_upd M hHot hMono]
theorem wpZeroSet_midDyn {Var : Type} [Fintype Var] [DecidableEq Var] {R G N : ℕ} (v : Var) (P :
  HGadgetSymp14Plan R G) (M : MidLayout N) (S : Finset (Wire N)) (hwS : M.wG ∈ S) : WpZeroSet v S
  (diagKetUnitary (rMidP P M)) (midDyn v P M) := by
  have hLoop := wpZeroSet_grpsLoopDyn v P M S hwS G le_rfl
  set cTail := diagCirc P M 14 le_rfl ;;ᶜ fix128C M.rHot M.rMono M.hHotMono (totPhi P)
  have hTail := WpZeroSet.of_circuit v S cTail (by simp [cTail])
  rw [midDyn]
  refine WpZeroSet.congr_unitary (WpZeroSet.seq_diag_left hLoop hTail) fun γ _ ↦ ?_
  rw [Submonoid.coe_mul, ← mulVec_mulVec, ket_sdk_eq γ, diagKetUnitary_mulVec_ket, mulVec_smul,
    diagKetUnitary_mulVec_ket, ← ket_sdk_eq γ]
  dsimp only [cTail]
  rw [eval_seq_mv, ket_diagCirc P
    M γ 14 le_rfl, mulVec_smul, ket_fix128Circ, smul_smul, smul_smul, ← bitSign_add, ← bitSign_add]
  refine congrArg (· • XMeasCircuit.ket γ) (congrArg bitSign ?_)
  simp only [Fin.eta, rMidP, rDelS2, rMidW, b2z_xor, mul_add, Finset.sum_add_distrib]
  ring
attribute [irreducible] grpsLoopD diagCirc midDyn
/-- Forward `H` sweep across the first `m ≤ 14` wires of `rOut` (`0 T`, `0 TOFF`). -/
def hPreC {N :
  ℕ} (rOut : QRegister 14 N) : (m : ℕ) → m ≤ 14 → Circuit N
  | 0, _ => .identity
  | m + 1, hm => Circuit.H (rOut ⟨m, hm⟩) ;;ᶜ hPreC rOut m (Nat.le_of_succ_le hm)
/-- Reverse `H` sweep across the first `m ≤ 14` wires of `rOut` (`0 T`, `0 TOFF`). -/
def hRevC {N :
  ℕ} (rOut : QRegister 14 N) : (m : ℕ) → m ≤ 14 → Circuit N
  | 0, _ => .identity
  | m + 1, hm => hRevC rOut m (Nat.le_of_succ_le hm) ;;ᶜ Circuit.H (rOut ⟨m, hm⟩)
@[simp] theorem count_hPreCirc_toff {N : ℕ} (rOut : QRegister 14 N) : ∀ (m : ℕ) (hm : m ≤ 14),
  (hPreC rOut m hm).count .TOFF = 0
  | 0, _ => rfl
  | m + 1, hm => by simp [hPreC, count_hPreCirc_toff rOut m (Nat.le_of_succ_le hm)]
@[simp] theorem count_hPreCirc_t {N : ℕ} (rOut : QRegister 14 N) : ∀ (m : ℕ) (hm : m ≤ 14), (hPreC
  rOut m hm).count .T = 0
  | 0, _ => rfl
  | m + 1, hm => by simp [hPreC, count_hPreCirc_t rOut m (Nat.le_of_succ_le hm)]
@[simp] theorem count_hRevCirc_toff {N : ℕ} (rOut : QRegister 14 N) : ∀ (m : ℕ) (hm : m ≤ 14),
  (hRevC rOut m hm).count .TOFF = 0
  | 0, _ => rfl
  | m + 1, hm => by simp [hRevC, count_hRevCirc_toff rOut m (Nat.le_of_succ_le hm)]
@[simp] theorem count_hRevCirc_t {N : ℕ} (rOut : QRegister 14 N) : ∀ (m : ℕ) (hm : m ≤ 14), (hRevC
  rOut m hm).count .T = 0
  | 0, _ => rfl
  | m + 1, hm => by simp [hRevC, count_hRevCirc_t rOut m (Nat.le_of_succ_le hm)]
theorem zProj_comm_H {N : ℕ} {S : Finset (Wire N)} {q : Wire N} (hq : q ∉ S) : zeroProjOn S *
  (Circuit.H q).eval.1 = (Circuit.H q).eval.1 * zeroProjOn S := by
  refine XMeasCircuit.matrix_ext_ket fun β ↦ ?_
  have hiff (b : ZMod 2) : (∀ w ∈ S, update β q b w = 0) ↔ ∀ w ∈ S, β w = 0 :=
    forall₂_congr fun w hw ↦ by
      have hne : w ≠ q := fun h ↦ hq (h ▸ hw)
      rw [update_of_ne hne]
  simp only [← mulVec_mulVec]
  rw [ket_H, mulVec_smul, mulVec_add, mulVec_smul, ket_sdk_eq (update β q 0), zeroProjOn_mulVec_ket,
    ket_sdk_eq (update β q 1), zeroProjOn_mulVec_ket, ket_sdk_eq β, zeroProjOn_mulVec_ket]
  by_cases h0 : ∀ w ∈ S, β w = 0
  · rw [ite_t (((hiff 0).mpr h0)), ite_t (((hiff 1).mpr h0)), ite_t (h0), ← ket_sdk_eq β, ket_H]
  · rw [ite_f ((mt (hiff 0).mp h0)), ite_f ((mt (hiff 1).mp h0)), ite_f (h0), smul_zero, add_zero,
      smul_zero, mulVec_zero]
theorem zProj_comm_hPre {N : ℕ} (rOut : QRegister 14 N) {S : Finset (Wire N)} (hDisj : Disjoint
  rOut.image S) : ∀ (m : ℕ) (hm : m ≤ 14), zeroProjOn S * (hPreC rOut m hm).eval.1 = (hPreC rOut m
  hm).eval.1 * zeroProjOn S
  | 0, _ => by simp [hPreC]
  | m + 1, hm => by
      have hq : rOut ⟨m, hm⟩ ∉ S := Finset.disjoint_left.mp hDisj ((rOut.mem_image _).mpr ⟨⟨m, hm⟩,
        rfl⟩)
      rw [hPreC, Circuit.eval_seq, Submonoid.coe_mul, ← Matrix.mul_assoc, zProj_comm_hPre rOut hDisj
        m _, Matrix.mul_assoc, zProj_comm_H hq, ← Matrix.mul_assoc]
theorem wpZero_seq_circ {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ} {v : Var} {S : Finset
  (Wire n)} (c : Circuit n) (hc0 : c.count .TOFF = 0) (hComm : zeroProjOn S * c.eval.1 = c.eval.1 *
  zeroProjOn S) {U₂ : Unitary (2 ^ n)} {d₂ : DynamicCircuit Var n} (h₂ : WpZeroSet v S U₂ d₂) :
  WpZeroSet v S (U₂ * c.eval) (.seq (.circuit c) d₂) := by
  have hCommH : zeroProjOn S * c.eval.1ᴴ = c.eval.1ᴴ * zeroProjOn S := by
    simpa only [conjTranspose_mul, zeroProjOn_conjTranspose] using (congrArg (·ᴴ) hComm).symm
  have hSeq (Θ : QCAssertion Var (2 ^ n)) : wp ((DynamicCircuit.circuit c).seq d₂).compile Θ =
    qcWpQAssign c.eval (wp d₂.compile Θ) := by
    rw [DynamicCircuit.compile_seq, wp_qSeq, DynamicCircuit.compile_circuit,
      DynamicCircuit.qc_wp_circuit_compile (Var := Var)]
  refine ⟨by simp [DynamicCircuit.count, hc0, h₂.1], fun Θ hΘ σ val ↦ ?_, fun Θ hΘ ↦ ?_⟩
  · rw [hSeq]
    simp only [qcWpQAssign, h₂.2.1 Θ hΘ σ val]
  · rw [hSeq Θ]
    funext σ
    apply Subtype.ext
    rw [rZero_wp_coe, rZero_wp_coe, hCommH, ← conj_conj, ←
      SelectSwapQROM.restrictZeroSet_coe, h₂.2.2 Θ hΘ, rZero_wp_coe, conj_conj, ←
      Matrix.mul_assoc, ← hCommH, Matrix.mul_assoc, Submonoid.coe_mul, conjTranspose_mul]
/-- Prefix XOR on `rOut` wires `k < m`. -/
noncomputable def xorPrefAssign {N : ℕ} (rOut : QRegister
  14 N) (γ : BitAssignment N) (w : Fin 14 → Bool) (m : ℕ) : BitAssignment N := writeReg γ rOut (fun
  k ↦ γ (rOut k) + if k.val < m then b2z (w k) else 0)
/-- Remaining suffix phase on `rOut` wires `k ≥ m`. -/
def remPhase {N : ℕ} (rOut : QRegister 14 N)
  (γ : BitAssignment N) (φ₀ : ZMod 2) (w : Fin 14 → Bool) (m : ℕ) : ZMod 2 := φ₀ + ∑ k : Fin 14, if
  m ≤ k.val then γ (rOut k) * b2z (w k) else 0
theorem xorPrefAssign_14 {N : ℕ} (rOut : QRegister 14 N) (γ : BitAssignment N) (w : Fin 14 → Bool) :
  xorPrefAssign rOut γ w 14 = writeReg γ rOut (fun k ↦ γ (rOut k) + b2z (w k)) := by
  dsimp only [xorPrefAssign]
  congr 1
  funext k
  simp [k.isLt]
theorem remPhase_14 {N : ℕ} (rOut : QRegister 14 N) (γ : BitAssignment N) (φ₀ : ZMod 2) (w : Fin 14
  → Bool) : remPhase rOut γ φ₀ w 14 = φ₀ := by
  dsimp only [remPhase]
  rw [Finset.sum_eq_zero, add_zero]
  intro k _
  have := k.isLt
  simp [show ¬(14 ≤ k.val) by omega]
theorem ket_hSand_diag {N : ℕ} (rOut : QRegister 14 N) (D : Unitary (2 ^ N)) (word : BitAssignment N
  → Fin 14 → Bool) (φ₀ : BitAssignment N → ZMod 2) (hWordOut : ∀ j β b, word (update β (rOut j) b) =
  word β) (hPhiOut : ∀ j β b, φ₀ (update β (rOut j) b) = φ₀ β) (hDKet : ∀ δ, D.1.mulVec
  (XMeasCircuit.ket δ) = bitSign (φ₀ δ + ∑ k : Fin 14, δ (rOut k) * b2z (word δ k)) •
  XMeasCircuit.ket δ) : ∀ (m : ℕ) (hm : m ≤ 14) (γ : BitAssignment N), ((hRevC rOut m hm).eval * D *
  (hPreC rOut m hm).eval).1.mulVec (XMeasCircuit.ket γ) =
    bitSign (remPhase rOut γ (φ₀ γ) (word γ) m) •
  XMeasCircuit.ket (xorPrefAssign rOut γ (word γ) m)
  | 0, _, γ => by
      have h0 : xorPrefAssign rOut γ (word γ) 0 = γ := by
        funext w
        by_cases hwo : w ∈ Set.range rOut.wires
        · obtain ⟨k, rfl⟩ := hwo
          simp [xorPrefAssign, writeReg_apply_reg]
        · exact writeReg_apply_of_not_mem _ rOut _ _ hwo
      simp only [hRevC, hPreC, Circuit.eval_identity, one_mul, mul_one, remPhase, Nat.zero_le,
        ↓reduceIte, h0]
      exact hDKet γ
  | m + 1, hm, γ => by
      let q := rOut ⟨m, hm⟩
      have ih0 := ket_hSand_diag rOut D word φ₀ hWordOut hPhiOut hDKet m (Nat.le_of_succ_le hm)
        (update γ q 0)
      have ih1 := ket_hSand_diag rOut D word φ₀ hWordOut hPhiOut hDKet m (Nat.le_of_succ_le hm)
        (update γ q 1)
      set γ' := xorPrefAssign rOut γ (word γ) (m + 1)
      set x := b2z (word γ ⟨m, hm⟩)
      set Φ' := remPhase rOut γ (φ₀ γ) (word γ) (m + 1)
      have hRem (b : ZMod 2) : remPhase rOut (update γ q b) (φ₀ (update γ q b)) (word (update γ q
        b)) m = Φ' + b * x := by
        rw [hPhiOut, hWordOut]
        dsimp only [remPhase, Φ']
        rw [add_assoc]
        congr 1
        have hpt (k : Fin 14) : (if m ≤ k.val then update γ q b (rOut k) * b2z (word γ k) else 0) =
          (if m + 1 ≤ k.val then γ (rOut k) * b2z (word γ k) else 0) + if k = ⟨m, hm⟩ then b * x
          else 0 := by
          by_cases hkm : k = ⟨m, hm⟩
          · subst hkm
            simp [q, x, update_self]
          · have hne : rOut k ≠ q := rOut.wires.injective.ne hkm
            have : k.val ≠ m := fun hv ↦ hkm (Fin.ext hv)
            simp [hkm, update_of_ne hne, show (m ≤ k.val) ↔ m + 1 ≤ k.val by omega]
        simp_rw [hpt]
        rw [Finset.sum_add_distrib]
        simp
      have hPref (b : ZMod 2) : xorPrefAssign rOut (update γ q b) (word (update γ q b)) m = update
        γ' q b := by
        rw [hWordOut]
        funext w
        by_cases hwo : w ∈ Set.range rOut.wires
        · obtain ⟨k, rfl⟩ := hwo
          by_cases hkm : k = ⟨m, hm⟩
          · subst hkm
            simp [q, xorPrefAssign, writeReg_apply_reg]
          · have hne : rOut k ≠ q := rOut.wires.injective.ne hkm
            have : k.val ≠ m := fun hv ↦ hkm (Fin.ext hv)
            have hiff : (k.val < m) ↔ (k.val < m + 1) := by omega
            simp [γ', xorPrefAssign, writeReg_apply_reg, update_of_ne hne, hiff]
        · have hne : w ≠ q := fun h ↦ hwo ⟨⟨m, hm⟩, h.symm⟩
          simp [γ', xorPrefAssign, writeReg_apply_of_not_mem _ rOut _ _ hwo, update_of_ne hne]
      have hγ'q : γ' q = γ q + x := by
        dsimp only [γ', q, x, xorPrefAssign]
        rw [writeReg_apply_reg]
        simp
      rw [hRem 0, zero_mul, add_zero, hPref 0] at ih0
      rw [hRem 1, one_mul, hPref 1] at ih1
      set V := (hRevC rOut m (Nat.le_of_succ_le hm)).eval * D * (hPreC rOut m (Nat.le_of_succ_le
        hm)).eval
      have hAssoc : (hRevC rOut (m + 1) hm).eval * D * (hPreC rOut (m + 1) hm).eval = (Circuit.H
        q).eval * V * (Circuit.H q).eval := by
        simp only [V, q, hRevC, hPreC, Circuit.eval_seq, mul_assoc]
      have hV : V.1.mulVec ((Circuit.H q).eval.1.mulVec (XMeasCircuit.ket γ)) = bitSign Φ' •
        (Circuit.H q).eval.1.mulVec (XMeasCircuit.ket γ') := by
        rw [ket_H q γ, ket_H q γ', mulVec_smul, mulVec_add, mulVec_smul, ih0, ih1, bitSign_add]
        have hbs : XMeasCircuit.bitSign (γ' q) = XMeasCircuit.bitSign (γ q) * bitSign x := by
          rw [hγ'q]
          exact XMeasCircuit.bitSign_add (γ q) x
        rw [hbs]
        ext i
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        ring
      rw [hAssoc, Submonoid.coe_mul, Submonoid.coe_mul, ← mulVec_mulVec, ← mulVec_mulVec, hV,
        mulVec_smul, mulVec_mulVec, ← Submonoid.coe_mul, eval_h_mul_self q, Submonoid.coe_one,
        one_mulVec]
attribute [irreducible] hPreC hRevC
/-- Build `StepPow2Layout 4 N` from `(rQrom, rScr)` reusing `rScr 32` as `qEnc`. -/
def mkStep {N
  sScr : ℕ} (rQrom : QRegister (aliasQromBits 5 128 9 0) N) (rScr : QRegister sScr N) (hScr : 33 ≤
  sScr) (hdisj : rQrom.DisjointWires rScr) : StepPow2Layout 4 N := ⟨rQrom.slice 0 5 (by decide),
  rScr.slice 0 32 (by omega), rScr ⟨32, by omega⟩, (hdisj.compose_left _).compose_right _, fun i ↦
  (hdisj.compose_left _).ne i ⟨32, by omega⟩, fun g hEq ↦ Nat.ne_of_lt g.isLt ((Nat.zero_add
  g.val).symm.trans (congrArg Fin.val (rScr.wires.injective hEq)))⟩
/-- Build `MidLayout N` from `(rQrom, rScr)` reusing `rScr 32` as `wG`. -/
def mkMid {N sScr : ℕ}
  (rQrom : QRegister (aliasQromBits 5 128 9 0) N) (rScr : QRegister sScr N) (hScr : 33 ≤ sScr)
  (hdisj : rQrom.DisjointWires rScr) : MidLayout N := ⟨rQrom.slice 5 128 (by decide), rScr.slice 1
  31 (by omega), rScr ⟨32, by omega⟩, rQrom.slice 133 14 (by decide), fun c u ↦ ((hdisj.compose_left
  _).compose_right _).ne c u, fun c ↦ (hdisj.compose_left _).ne c ⟨32, by omega⟩, fun u hEq ↦
  Nat.ne_of_lt (Nat.succ_lt_succ u.isLt) ((Nat.add_comm u.val 1).trans (congrArg Fin.val
  (rScr.wires.injective hEq))), fun k ↦ ((hdisj.compose_left _).ne k ⟨32, by omega⟩).symm, fun c k ↦
  (rQrom.slice_disjoint_of_le 5 128 133 14 (by decide) (by decide) (by omega)).ne c k, fun u k ↦
  (((hdisj.compose_left _).compose_right _).ne k u).symm⟩
/-- Parametric `(60 + 2 * R + 2 * G)`-`T` QROM loader. -/
def qromHGadgetSymp14FromHot128LoadDyn
  {Var : Type} {R G N sScr : ℕ} (v : Var) (P : HGadgetSymp14Plan R G) (rQrom : QRegister
  (aliasQromBits 5 128 9 0) N) (rScr : QRegister sScr N) (hScr : 33 ≤ sScr) (hdisj :
  rQrom.DisjointWires rScr) : DynamicCircuit Var N :=
  let L := mkStep rQrom rScr hScr hdisj
  let M := mkMid rQrom rScr hScr hdisj
  .seq (.circuit (hPreC M.rOut 14 le_rfl)) (.seq (withStepAnfPow2Dyn v L (midDyn v P M)) (.circuit
    (hRevC M.rOut 14 le_rfl)))
@[simp] theorem count_qromHGadgetSymp14FromHot128LoadDyn_toff {Var : Type} {R G N sScr : ℕ} (v :
  Var) (P : HGadgetSymp14Plan R G) (rQrom : QRegister (aliasQromBits 5 128 9 0) N) (rScr : QRegister
  sScr N) (hScr : 33 ≤ sScr) (hdisj : rQrom.DisjointWires rScr) :
  (qromHGadgetSymp14FromHot128LoadDyn v P rQrom rScr hScr hdisj).count .TOFF = 0 := by
  simp [qromHGadgetSymp14FromHot128LoadDyn, DynamicCircuit.count]
@[simp] theorem count_qromHGadgetSymp14FromHot128LoadDyn_t {Var : Type} {R G N sScr : ℕ} (v : Var)
  (P : HGadgetSymp14Plan R G) (rQrom : QRegister (aliasQromBits 5 128 9 0) N) (rScr : QRegister sScr
  N) (hScr : 33 ≤ sScr) (hdisj : rQrom.DisjointWires rScr) : (qromHGadgetSymp14FromHot128LoadDyn v P
  rQrom rScr hScr hdisj).count .T = 60 + 2 * R + 2 * G := by
  simp only [qromHGadgetSymp14FromHot128LoadDyn, DynamicCircuit.count, count_hRevCirc_t,
    count_hPreCirc_t, count_withStepAnfPow2Dyn_t, count_midDyn_t]
  omega
theorem cleanPredRealizes_qromHGadgetSymp14FromHot128LoadDyn {Var : Type} [Fintype Var]
  [DecidableEq Var] {R G N sScr : ℕ} (v : Var) (P : HGadgetSymp14Plan R G) (rQrom : QRegister
  (aliasQromBits 5 128 9 0) N) (rScr : QRegister sScr N) (hScr : 33 ≤ sScr) (hdisj :
  rQrom.DisjointWires rScr) : CleanPredRealizes v (Mobius126OneHot.cleanPredProj rScr.image
  (oneHotPred (rQrom.slice 5 128 (by decide)))) (rQrom.embedUnitary (aliasTableXorUnitary (5 + 128)
  14 (hotLinearTargetFn 5 128 14 P.targetBoolTable))) (qromHGadgetSymp14FromHot128LoadDyn v P rQrom
  rScr hScr hdisj) := by
  let L := mkStep rQrom rScr hScr hdisj
  let M := mkMid rQrom rScr hScr hdisj
  have hQromScr := disjoint_image_of_disjointWires hdisj
  let S_clean : Finset (Wire N) := rScr.image \ L.rHot.image
  have hHotSubScr : L.rHot.image ⊆ rScr.image := rScr.image_compose_subset _
  have hUnionScr : L.rHot.image ∪ S_clean = rScr.image := Finset.union_sdiff_of_subset hHotSubScr
  have hDisjHotS : Disjoint L.rHot.image S_clean := disjoint_sdiff_self_right
  have hwS : M.wG ∈ S_clean := Finset.mem_sdiff.mpr ⟨(rScr.mem_image M.wG).mpr ⟨⟨32, by omega⟩,
    rfl⟩, fun hm ↦ ((L.rHot.mem_image _).mp hm).elim L.hHotEnc⟩
  have hDisjOutScr : Disjoint M.rOut.image rScr.image := Disjoint.mono_left
    (rQrom.image_compose_subset _) hQromScr
  have hStepWp := WpZeroSet.withStepAnfPow2_diag (by decide) le_rfl L S_clean hwS hDisjHotS
    (wpZeroSet_midDyn v P M S_clean hwS) (fun γ _ ↦ by rw [ket_sdk_eq γ, diagKetUnitary_mulVec_ket])
  rw [hUnionScr] at hStepWp
  set D := diagKetUnitary (fun β ↦ rMidP P M (anfEncAssign2 L β))
  have hSeq1 := WpZeroSet.seq_diag_left hStepWp (WpZeroSet.of_circuit v rScr.image (hRevC M.rOut 14
    le_rfl) (by simp))
  have hFullWp := wpZero_seq_circ (hPreC M.rOut 14 le_rfl) (by simp) (zProj_comm_hPre M.rOut
    hDisjOutScr 14 le_rfl) hSeq1
  set G_full : Unitary (2 ^ N) := (hRevC M.rOut 14 le_rfl).eval * D * (hPreC M.rOut 14 le_rfl).eval
  have hAnfUpdOut (j : Fin 14) (β : BitAssignment N) (b : ZMod 2) : anfEncAssign2 L (update β
    (M.rOut j) b) = update (anfEncAssign2 L β) (M.rOut j) b := by
    have hne (i : Fin 5) : L.rCtx i ≠ M.rOut j := (rQrom.slice_disjoint_of_le 0 5 133 14 (by decide)
      (by decide) (by omega)).ne i j
    have hIdxEq : (fun i ↦ update β (M.rOut j) b (L.rCtx i)) = fun i ↦ β (L.rCtx i) := funext fun i
      ↦ update_of_ne (hne i) b β
    funext w
    dsimp only [anfEncAssign2]
    rw [hIdxEq]
    by_cases hwh : w ∈ Set.range L.rHot.wires
    · obtain ⟨g, rfl⟩ := hwh
      have hneG : L.rHot g ≠ M.rOut j := (((hdisj.compose_left _).compose_right _).ne j g).symm
      rw [writeReg_apply_reg, update_of_ne hneG, writeReg_apply_reg]
    · rw [writeReg_apply_of_not_mem _ L.rHot _ _ hwh]
      by_cases hwo : w = M.rOut j
      · subst hwo
        simp [update_self]
      · simp [update_of_ne hwo, writeReg_apply_of_not_mem _ L.rHot _ _ hwh]
  let wordFull (β : BitAssignment N) : Fin 14 → Bool := rMidW P M (anfEncAssign2 L β)
  let φFull (β : BitAssignment N) : ZMod 2 := rDelS2 P M (anfEncAssign2 L β)
  have hWordOut (j : Fin 14) (β : BitAssignment N) (b : ZMod 2) : rMidW P M (update β (M.rOut j) b)
    = rMidW P M β := rawMidWord_upd P M (fun c ↦ M.hHotOut c j) (fun u ↦ M.hMonoOut u j) β b
  have hPhiOut (j : Fin 14) (β : BitAssignment N) (b : ZMod 2) : rDelS2 P M (update β (M.rOut j) b)
    = rDelS2 P M β := by
    unfold rDelS2
    refine congrArg₂ (· + ·) ?_ ?_
    · suffices ∀ n hn, rCarryP P M (update β (M.rOut j) b) n hn =
          rCarryP P M β n hn from this G le_rfl
      intro n hn
      induction n with
      | zero => rfl
      | succ _ ihm =>
          simp only [rCarryP, ihm (Nat.le_of_succ_le hn), rgCarry, v157_upd M (fun c ↦ M.hHotOut c
            j) (fun u ↦ M.hMonoOut u j)]
    · unfold rFixP
      refine Finset.sum_congr rfl fun c _ ↦ ?_
      rw [update_of_ne (M.hHotOut c j)]
      refine congrArg₂ (· * ·) rfl (congrArg₂ (· + ·) rfl ?_)
      refine Finset.sum_congr rfl fun u _ ↦ ?_
      rw [update_of_ne (M.hMonoOut u j)]
  have hDK (δ : BitAssignment N) :
      D.1.mulVec (XMeasCircuit.ket δ) =
        bitSign (φFull δ + ∑ k : Fin 14, δ (M.rOut k) * b2z (wordFull δ k)) •
          XMeasCircuit.ket δ := by
    dsimp only [D]
    rw [ket_sdk_eq δ, diagKetUnitary_mulVec_ket, ← ket_sdk_eq δ]
    refine congrArg (· • XMeasCircuit.ket δ) (congrArg bitSign ?_)
    dsimp only [rMidP, φFull, wordFull]
    refine congrArg₂ (· + ·) rfl ?_
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    have hnot : M.rOut k ∉ L.rHot.image := fun hm ↦ Finset.disjoint_left.mp hDisjOutScr
      ((M.rOut.mem_image _).mpr ⟨k, rfl⟩) (hHotSubScr hm)
    rw [anfEncAssign2_apply_of_not_mem L δ hnot]
  have hGK (β : BitAssignment N) : G_full.1.mulVec (XMeasCircuit.ket β) = bitSign (φFull β) •
    XMeasCircuit.ket (writeReg β M.rOut (fun k ↦ β (M.rOut k) + b2z (wordFull β k))) := by
    have hK := ket_hSand_diag M.rOut D wordFull φFull (fun j δ b ↦ (congrArg (rMidW P M) (hAnfUpdOut
      j δ b)).trans (hWordOut j _ b)) (fun j δ b ↦ (congrArg (rDelS2 P M) (hAnfUpdOut j δ b)).trans
      (hPhiOut j _ b)) hDK 14 le_rfl β
    rwa [remPhase_14, xorPrefAssign_14] at hK
  let F_lin := hotLinearTargetFn 5 128 14 P.targetBoolTable
  let U_q := rQrom.embedUnitary (aliasTableXorUnitary (5 + 128) 14 F_lin)
  let Q := Mobius126OneHot.cleanPredProj rScr.image (oneHotPred M.rHot)
  have hPresU : PreservesWires U_q.1 (rScr.image ∪ M.rHot.image) := by
    intro i j ⟨w, hw, hne⟩
    have hketU : U_q.1 i j = (U_q.1 *ᵥ CoherentAlias.ket (basisBits N j)) i := by
      simp [CoherentAlias.ket, basisState]
    rw [hketU]
    dsimp only [U_q]
    rw [aliasTableXorUnitary, embedUnitary_bitPermUnitary_mulVec_ket]
    dsimp only [Equiv.coe_fn_mk]
    have hSame : writeReg (basisBits N j) rQrom (aliasTableXorBits (5 + 128) 14 F_lin (fun m ↦
      basisBits N j (rQrom m))) w = basisBits N j w := by
      rcases Finset.mem_union.mp hw with hwS | hwH
      · obtain ⟨s, rfl⟩ := (rScr.mem_image w).mp hwS
        exact writeReg_apply_of_not_mem _ _ _ _ fun ⟨m, hm⟩ ↦ hdisj.ne m s hm
      · obtain ⟨c, rfl⟩ := (M.rHot.mem_image w).mp hwH
        have hcEq : M.rHot c = rQrom ⟨5 + c.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left c.isLt 5)
          (by decide)⟩ := rfl
        rw [hcEq, writeReg_apply_reg]
        simp [aliasTableXorBits, show ¬(5 + 128 ≤ 5 + c.val) by omega]
    have hneI : i ≠ (basisBits N).symm (writeReg (basisBits N j) rQrom (aliasTableXorBits (5 +
      128) 14 F_lin (fun m ↦ basisBits N j (rQrom m)))) := by
      intro heq
      apply hne
      rw [heq, basisBits_symm]
      exact hSame
    simp only [CoherentAlias.ket, basisState, Pi.single_apply]
    exact ite_f (hneI)
  have hCommS : zeroProjOn rScr.image * U_q.1ᴴ = U_q.1ᴴ * zeroProjOn rScr.image := by
    simpa only [conjTranspose_mul, zeroProjOn_conjTranspose] using congrArg (·ᴴ)
      (preservesWires_comm_zeroProjOn hPresU Finset.subset_union_left)
  have hCommP : predProj (oneHotPred M.rHot) * U_q.1ᴴ = U_q.1ᴴ * predProj (oneHotPred M.rHot) := by
    have hc := preservesWires_comm_predProj hPresU (P := oneHotPred M.rHot) fun α β h ↦ by
      have hH (c : Fin 128) := h _ (Finset.mem_union_right _ ((M.rHot.mem_image _).mpr ⟨c, rfl⟩))
      unfold oneHotPred
      exact decide_eq_decide.mpr ⟨fun ⟨rc, hrc⟩ ↦ ⟨rc, fun c ↦ (hH c).symm.trans
        (hrc c)⟩, fun ⟨rc, hrc⟩ ↦ ⟨rc, fun c ↦ (hH c).trans (hrc c)⟩⟩
    simpa only [conjTranspose_mul, predProj_conjTranspose] using congrArg (·ᴴ) hc
  have hCommQ : Q * U_q.1ᴴ = U_q.1ᴴ * Q := by
    dsimp only [Q, Mobius126OneHot.cleanPredProj]
    rw [Matrix.mul_assoc, hCommP, ← Matrix.mul_assoc, hCommS, Matrix.mul_assoc]
  have hMat : G_full.1 * Q = U_q.1 * Q := by
    refine XMeasCircuit.matrix_ext_ket fun β ↦ ?_
    dsimp only [Q, Mobius126OneHot.cleanPredProj]
    rw [ket_sdk_eq β]
    simp only [← mulVec_mulVec, predProj_mulVec_ket]
    by_cases hOh : oneHotPred M.rHot β = true
    · simp only [hOh, ↓reduceIte, zeroProjOn_mulVec_ket]
      rw [← ket_sdk_eq β]
      by_cases hS0 : ∀ w ∈ rScr.image, β w = 0
      · rw [ite_t (hS0)]
        unfold oneHotPred at hOh
        obtain ⟨rc, hrc⟩ := of_decide_eq_true hOh
        let x : Fin (2 ^ 5) := (basisBits 5).symm (fun i ↦ β (L.rCtx i))
        have hxBits : basisBits 5 x = fun i ↦ β (L.rCtx i) := basisBits_symm _
        set γ := anfEncAssign2 L β
        have hγHot (c : Fin 128) : γ (M.rHot c) = if c = rc then 1 else 0 := by
          have hn : M.rHot c ∉ L.rHot.image := fun hm ↦ Finset.disjoint_left.mp hQromScr
            (rQrom.image_compose_subset _ ((M.rHot.mem_image _).mpr ⟨c, rfl⟩)) (hHotSubScr hm)
          dsimp only [γ]
          rw [anfEncAssign2_apply_of_not_mem L β hn, hrc c]
        have hγMono (u : Fin 31) : γ (M.rMono u) = monoEval 5 (basisBits 5 x) ⟨u.val + 1, by omega⟩
          := by
          have hrw : M.rMono u = L.rHot ⟨u.val + 1, by omega⟩ := congrArg rScr.wires (Fin.ext
            ((Nat.add_comm 1 u.val).trans (Nat.zero_add _).symm))
          dsimp only [γ]
          rw [hrw, anfEncAssign2_apply_reg L β ⟨u.val + 1, by omega⟩, hxBits]
        have hEnvEq : vEnv M γ = idEnv rc x := by
          funext y
          rcases y with j | u
          · dsimp only [vEnv, vWire, idEnv]
            rw [hγHot ⟨j.val, by omega⟩]
            by_cases hj : j.val = rc.val
            · simp [hj, z2b]
            · simp [hj, show (⟨j.val, by omega⟩ : Fin 128) ≠ rc from fun h ↦ hj (congrArg Fin.val
                h), z2b]
          · dsimp only [vEnv, vWire, idEnv]
            rw [hγMono u]
        have hCarryEq : rCarryP P M γ G le_rfl = totPhi P rc x := by
          have hEqG (g : Fin G) : rgCarry P g M γ = idCarry P g rc x := by
            dsimp only [rgCarry, idCarry]
            rw [hEnvEq]
          suffices ∀ n hn, rCarryP P M γ n hn =
              ∑ i : Fin n, b2z (idCarry P ⟨i.val, i.isLt.trans_le hn⟩ rc x) from
            this G le_rfl
          intro n hn
          induction n with
          | zero => rfl
          | succ n ihm =>
              rw [rCarryP, ihm (Nat.le_of_succ_le hn), hEqG ⟨n, hn⟩, Fin.sum_univ_castSucc]
              rfl
        have hFixEq : rFixP M.rHot M.rMono (totPhi P) γ = totPhi P rc x := by
          dsimp only [rFixP]
          rw [Finset.sum_eq_single rc]
          · rw [hγHot rc, ite_t (rfl), one_mul]
            simp_rw [hγMono]
            exact anf5_decomp (totPhi P rc) x
          · intro c _ hc
            simp [hγHot c, hc]
          · intro h
            exact False.elim (h (Finset.mem_univ rc))
        have hPhiZero : φFull β = 0 := by
          change rCarryP P M γ G le_rfl + rFixP M.rHot M.rMono (totPhi P) γ = 0
          rw [hCarryEq, hFixEq, CharTwo.add_self_eq_zero]
        have hWordEq : wordFull β = P.targetBoolTable rc x := by
          funext k
          change xor (rGrpsP P k M γ G le_rfl) (rDiagB P k M γ) = P.targetBoolTable rc x k
          dsimp only [HGadgetSymp14Plan.targetBoolTable]
          have hGPref : ∀ n hn, rGrpsP P k M γ n hn = P.prefBool k rc x n hn := by
            intro n hn
            induction n with
            | zero => rfl
            | succ _ ihm =>
                simp only [rGrpsP, HGadgetSymp14Plan.prefBool, ihm (Nat.le_of_succ_le hn), rgBit,
                  HGadgetSymp14Plan.grpBit, hEnvEq]
          have hDiag : rDiagB P k M γ = xor (if h : rc.val < 126 then P.rowDiag k ⟨rc.val, h⟩ else
            false) (extCol24Bool (P.colDiag k) x) := by
            dsimp only [rDiagB]
            rw [hEnvEq, evalStep_rcColAff]
          rw [hGPref G le_rfl, hDiag]
        rw [hGK β, hPhiZero, bitSign_zero2, one_smul]
        have hketC (δ : BitAssignment N) : XMeasCircuit.ket δ = CoherentAlias.ket δ := rfl
        dsimp only [U_q]
        rw [hketC β, aliasTableXorUnitary, embedUnitary_bitPermUnitary_mulVec_ket,
          ← hketC]
        dsimp only [Equiv.coe_fn_mk]
        let cHot : Fin (2 ^ 128) := (basisBits 128).symm (fun c ↦ β (M.rHot c))
        have hcHot (c : Fin 128) : basisBits 128 cHot c = if c = rc then 1 else 0 := by
          rw [congrFun (basisBits_symm _) c, hrc c]
        have hAddrEq : (basisBits (5 + 128)).symm
            (fun i : Fin (5 + 128) ↦ β (rQrom ⟨i.val, i.isLt.trans_le (by decide)⟩)) =
            combineAddr x cHot := by
          dsimp only [combineAddr]
          apply congrArg (basisBits (5 + 128)).symm
          funext i
          by_cases hi5 : i.val < 5
          · simp only [hi5, ↓reduceDIte]
            rw [congrFun hxBits ⟨i.val, hi5⟩]
            exact congrArg β (congrArg rQrom.wires (Fin.ext (Nat.zero_add i.val).symm))
          · simp only [hi5, ↓reduceDIte]
            rw [congrFun (basisBits_symm (fun c ↦ β (M.rHot c))) _]
            exact congrArg β (congrArg rQrom.wires (Fin.ext (Nat.add_sub_of_le (Nat.le_of_not_lt
              hi5)).symm))
        have hFn := hotLinearTargetFn_combineAddr_oneHot P.targetBoolTable x rc cHot hcHot
        apply congrArg QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.XMeasCircuit.ket
        funext w
        by_cases hwQ : w ∈ Set.range rQrom.wires
        · obtain ⟨m, rfl⟩ := hwQ
          rw [writeReg_apply_reg]
          change _ = aliasTableXorBits (5 + 128) 14 F_lin (fun q ↦ β (rQrom q)) m
          dsimp only [aliasTableXorBits]
          by_cases hm : 5 + 128 ≤ m.val
          · have hk14 : m.val - 133 < 14 := by
              have := m.isLt
              dsimp [aliasQromBits, aliasOutBits] at this
              omega
            let k : Fin 14 := ⟨m.val - 133, hk14⟩
            have hmOut : rQrom m = M.rOut k := congrArg rQrom.wires (Fin.ext (Nat.add_sub_of_le
              hm).symm)
            have hkEq : (⟨m.val - (5 + 128), by omega⟩ : Fin 14) = k := Fin.ext rfl
            simp only [hm, ↓reduceDIte, F_lin]
            rw [hmOut, writeReg_apply_reg, hWordEq, hAddrEq, hFn, hkEq]
            rfl
          · have hnotOut : rQrom m ∉ Set.range M.rOut.wires := by
              rintro ⟨k, hk'⟩
              change rQrom (QRegister.block 133 14 (by decide) k) = rQrom m at hk'
              have hv := congrArg Fin.val (rQrom.wires.injective hk')
              rw [QRegister.block_apply_val] at hv
              omega
            rw [writeReg_apply_of_not_mem _ M.rOut _ _ hnotOut]
            simp [hm]
        · have hnotOut : w ∉ Set.range M.rOut.wires := fun ⟨k, hk'⟩ ↦ hwQ ⟨QRegister.block 133 14
            (by decide) k, hk'⟩
          rw [writeReg_apply_of_not_mem _ M.rOut _ _ hnotOut, writeReg_apply_of_not_mem _ rQrom _ _
            hwQ]
      · rw [ite_f (hS0), mulVec_zero, mulVec_zero]
    · simp [hOh]
  dsimp only [qromHGadgetSymp14FromHot128LoadDyn]
  refine ⟨hFullWp.1, hCommQ, hFullWp.2.1, fun Θ hΘ σ ↦ ?_⟩
  have hQH : Qᴴ = Q := cleanPredProj_conjTranspose rScr.image (oneHotPred M.rHot)
  have hQMat : Q * G_full.1ᴴ = Q * U_q.1ᴴ := by
    simpa only [conjTranspose_mul, hQH] using congrArg (·ᴴ) hMat
  have hWpS := congrArg (fun A : QCAssertion Var (2 ^ N) ↦ (A σ).1.conj (predProj (oneHotPred
    M.rHot))) (hFullWp.2.2 Θ hΘ)
  rw [SelectSwapQROM.restrictZeroSet_coe, SelectSwapQROM.restrictZeroSet_coe, conj_conj,
    conj_conj, predProj_mul_zeroProjOn_eq_cleanPredProj] at hWpS
  change ((wp _ Θ σ).1).conj Q = ((qcWpQAssign G_full Θ σ).1).conj Q at hWpS
  refine hWpS.trans ?_
  change ((qcWpQAssign G_full Θ σ).1).conj Q = ((qcWpQAssign U_q Θ σ).1).conj Q
  simp only [qcWpQAssign, qcQAssignObsMap, Observable.conj_coe, Unitary.coe_star,
    star_eq_conjTranspose, conj_conj, hQMat]
attribute [irreducible] qromHGadgetSymp14FromHot128LoadDyn
/-- Single-step Boolean product of `S : Symp14Spec R`. -/
def stepTerm {R : ℕ} (S : Symp14Spec R)
  (rc : Fin 128) (x : Fin (2 ^ 5)) (m : Fin R) : Bool := xor (if h : rc.val < 126 then S.stepA m
  ⟨rc.val, h⟩ else false) (extCol24Bool (S.stepC m) x) && xor (if h : rc.val < 126 then S.stepB m
  ⟨rc.val, h⟩ else false) (extCol24Bool (S.stepD m) x)
theorem b2z_stepXor {R : ℕ} (S : Symp14Spec R) (k : Fin 14) (rc : Fin 128) (x : Fin (2 ^ 5)) : ∀ (n
  : ℕ) (hn : n ≤ R), b2z (S.stepXorBool k (if h : rc.val < 126 then some ⟨rc.val, h⟩ else none) x n
  hn) = ∑ m : Fin n, b2z (S.stepW ⟨m.val, m.isLt.trans_le hn⟩ k) * b2z (stepTerm S rc x ⟨m.val,
  m.isLt.trans_le hn⟩)
  | 0, _ => rfl
  | m + 1, hm => by
      rw [Fin.sum_univ_castSucc]
      unfold Symp14Spec.stepXorBool
      dsimp only
      cases hw : S.stepW ⟨m, hm⟩ k
      · simp only [hw, Bool.false_eq_true, ↓reduceIte, Fin.val_castSucc, Fin.val_last, b2z_stepXor S
          k rc x m (Nat.le_of_succ_le hm), b2z_false, zero_mul, add_zero]
      · simp only [hw, ↓reduceIte, b2z_xor, Fin.val_castSucc, Fin.val_last, b2z_stepXor
          S k rc x m (Nat.le_of_succ_le hm), b2z_true, one_mul, stepTerm]
        by_cases hrc : rc.val < 126 <;> simp only [hrc, ↓reduceDIte]
theorem b2z_xorPairs_map {V α : Type} (f : V → Bool) (h : α → AffPair V) : ∀ l : List α, b2z
  (xorPairs f (l.map h)) = (l.map fun a ↦ b2z (evStep f (h a).1 && evStep f (h a).2)).sum
  | [] => rfl
  | _ :: as => by
      simp only [List.map_cons, xorPairs, b2z_xor, List.sum_cons, b2z_xorPairs_map f h as]
theorem finRange_map_sum {M : Type} [AddCommMonoid M] : ∀ (m : ℕ) (ϕ : Fin m → M), ((List.finRange
  m).map ϕ).sum = ∑ j : Fin m, ϕ j
  | 0, _ => rfl
  | m + 1, ϕ => by
      rw [List.finRange_succ, List.map_cons, List.sum_cons, List.map_map, finRange_map_sum m (ϕ ∘
        Fin.succ), Fin.sum_univ_succ]
      rfl
theorem sum_grpIdx_pref {R G : ℕ} (P : HGadgetSymp14Plan R G) (F : Fin R → ZMod 2) : ∀ (n : ℕ) (hn :
  n ≤ G), (∑ g : Fin n, ∑ j : Fin (P.groupLen ⟨g.val, g.isLt.trans_le hn⟩), F (P.stepIdx ⟨g.val,
  g.isLt.trans_le hn⟩ j)) = ∑ t ∈ Finset.range (prefLen P.groupLen n hn), (if ht : t < R then F ⟨t,
  ht⟩ else 0)
  | 0, _ => rfl
  | n + 1, hn => by
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last]
      rw [sum_grpIdx_pref P F n (Nat.le_of_succ_le hn), prefLen, Finset.sum_range_add]
      congr 1
      rw [← Fin.sum_univ_eq_sum_range]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      have hlt := P.step_lt ⟨n, hn⟩ j
      simp [HGadgetSymp14Plan.stepIdx, hlt]
theorem b2z_grpsPref {R G : ℕ} (P : HGadgetSymp14Plan R G) (k : Fin 14) (rc : Fin 128) (x : Fin (2 ^
  5)) : ∀ (n : ℕ) (hn : n ≤ G), b2z (P.prefBool k rc x n hn) = ∑ g : Fin n, b2z (P.groupW ⟨g.val,
  g.isLt.trans_le hn⟩ k) * b2z (P.grpBit ⟨g.val, g.isLt.trans_le hn⟩ rc x)
  | 0, _ => rfl
  | n + 1, hn => by
      rw [Fin.sum_univ_castSucc, HGadgetSymp14Plan.prefBool, b2z_xor, b2z_grpsPref P k rc x n
        (Nat.le_of_succ_le hn), b2z_and]
      rfl
/-- Build `HGadgetSymp14Plan R G` from `Symp14Spec R`. -/
def HGadgetSymp14Plan.ofSymp14Spec {R G :
  ℕ} (S : Symp14Spec R) (groupLen : Fin G → ℕ) (hsum : (∑ g : Fin G, groupLen g) = R) (groupW : Fin
  G → Fin 14 → Bool) (permFwd : Fin R → Fin R) : HGadgetSymp14Plan R G := ⟨groupLen, hsum, groupW,
  fun m ↦ S.stepA (permFwd m), fun m ↦ S.stepB (permFwd m), fun m ↦ S.stepC (permFwd m), fun m ↦
  S.stepD (permFwd m), S.rowDiag, S.colDiag⟩
theorem HGadgetSymp14Plan.ofSymp14Spec_targetBoolTable_eq {R G : ℕ} (S : Symp14Spec R) (groupLen :
  Fin G → ℕ) (hsum : (∑ g : Fin G, groupLen g) = R) (groupW : Fin G → Fin 14 → Bool) (perm : Fin R ≃
  Fin R) (hW : ∀ (g : Fin G) (j : Fin (groupLen g)) (k : Fin 14), S.stepW (perm
  ((HGadgetSymp14Plan.ofSymp14Spec S groupLen hsum groupW perm).stepIdx g j)) k = groupW g k) (rc :
  Fin 128) (x : Fin (2 ^ 5)) (k : Fin 14) : (HGadgetSymp14Plan.ofSymp14Spec S groupLen hsum groupW
  perm).targetBoolTable rc x k = S.evalBool k (if h : rc.val < 126 then some ⟨rc.val, h⟩ else none)
  x := by
  set P := HGadgetSymp14Plan.ofSymp14Spec S groupLen hsum groupW perm
  rw [← z2b_b2z (P.targetBoolTable rc x k), ← z2b_b2z (S.evalBool k _ x)]
  congr 1
  unfold HGadgetSymp14Plan.targetBoolTable Symp14Spec.evalBool
  dsimp only
  simp only [b2z_xor, b2z_grpsPref, b2z_stepXor, Fin.eta]
  have hrd : P.rowDiag = S.rowDiag := rfl
  have hcd : P.colDiag = S.colDiag := rfl
  have hgrp : (∑ g : Fin G, b2z (P.groupW g k) * b2z (P.grpBit g rc x)) = ∑ i : Fin R, b2z (S.stepW
    i k) * b2z (stepTerm S rc x i) := by
    have h1 : (∑ g : Fin G, b2z (P.groupW g k) * b2z (P.grpBit g rc x)) = ∑ g : Fin G, ∑ j : Fin
      (P.groupLen g), b2z (S.stepW (perm (P.stepIdx g j)) k) * b2z (stepTerm S rc x (perm (P.stepIdx
      g j))) := by
      refine Finset.sum_congr rfl fun g _ ↦ ?_
      dsimp only [HGadgetSymp14Plan.grpBit, HGadgetSymp14Plan.affPairs]
      rw [b2z_xorPairs_map, finRange_map_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      have hWj : P.groupW g k = S.stepW (perm (P.stepIdx g j)) k := (hW g j k).symm
      rw [hWj, evalStep_rcColAff, evalStep_rcColAff]
      rfl
    let F : Fin R → ZMod 2 := fun m ↦ b2z (S.stepW (perm m) k) * b2z (stepTerm S rc x (perm m))
    have h2 := sum_grpIdx_pref P F G le_rfl
    have hprefR : prefLen P.groupLen G le_rfl = R := (pref_full P.groupLen).trans hsum
    rw [h1, h2, hprefR, ← Fin.sum_univ_eq_sum_range]
    have h3 : (∑ t : Fin R, (if ht : t.val < R then F ⟨t.val, ht⟩ else 0)) = ∑ m : Fin R, F m :=
      Finset.sum_congr rfl fun m _ ↦ by simp [m.isLt]
    rw [h3]
    exact Equiv.sum_comp perm (fun i ↦ b2z (S.stepW i k) * b2z (stepTerm S rc x i))
  rw [hrd, hcd, hgrp]
  by_cases hrc : rc.val < 126 <;> simp only [hrc, ↓reduceDIte] <;> exact add_comm _ _

end HGadgetImpl
end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.HGadgetSympQrom
