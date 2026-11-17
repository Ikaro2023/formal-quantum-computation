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

public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.Inner18Symp14Walk
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.Pi145CompactRouter
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.HGadgetSympQrom
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.HadWStateMux25B
/-!
# Narrow `wInner2 = 18` + `46-T` Hadamard W-State Three-Gear Superstep Walk Legs

Self-contained `wInner2 = 18` walk-leg package combining:
1. `hadWMux23Bundle`: `46-T` (`16`-ancilla) Hadamard W-state `23`-wire `Mux23Bundle` adapter.
2. `Mag30Bundle2`: modular `30`-state index-magnitude loader (`T72`, `Quant66`, `Quant56`).
3. `OneHot14LoadBundle_3`: modular `128 × 14` one-hot loader (`406-T` H-gadget Keep-9 default).
4. `inner18Mfwd` & alignment between `hot128NegRegUnitary` and `defaultNegRegUnitary`.
5. `TailShift`-compatible Coarse/Mid (`inner18Step1Dyn`, `inner18TurnGenDyn`,
   `inner18Step4ColdDyn`) and Fine low-scratch walk legs with explicit Bell-wire &
   `rSys116` disjointness.
-/

@[expose] public section
namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.Inner18HadWSuperLegsA
open QuantumComputation.Specs QuantumComputation.Specs.P450
open Operator QProg Matrix Circuit Real HermitianMat BlockEncodingCore BlockEncodingCircuit
open QuantumComputation.Specs Solution QuantumComputation.Specs.P450 CoherentAlias Solution.CleanDyn
open AliasPrep
open Solution.CircuitModular Solution.GivensOps
open MidReflCtxRetain Phase2MidSandwich OptFactoredMag30AndCoin9 QuantizedFactoredMag30
open Cat11CompactPhase2Bridge ReordOuter13Bridge ZeroRcHotPrepMid21Fast OptXMeasUnload21
open Tuned162ScheduledSympQrom21 Tuned162StepSympAnfQrom21 OptStepSympAnfQrom21 TopIntegrationBridge
open MobiusOptSubcube163Walk CompactTuned162StepZeroCmp20 CompactZeroCmp20OuterParam
open CompactStepZeroCmp20OuterParam StepAnfAndCoin14Core CompactStepCompact2504ZeroCmp20
open Pi145SOSPermBridge StepOuter8Pi145Outer StepOuter8Pi145L1 StepKeep9Symp14Data
open StepBound148Borrow Tuned155Hot128SympQrom20 CompactOuter9Bound50Core
open LowBitPi145Select BellSingletCSwap58 FastUniform
open Inner18Symp14Walk HGadgetSympQrom
open QRegister InnerTable GroupUnary Pi145CompactRouter HadWStateMux25CompactA
open HadWStateMux25CompactB
open Solution.CircuitModular.UnsignedGivens (maskSumBit basisBits_symm_eq cnotMaskReg
  evolve_cnotMaskReg_ket eval_identity_mulVec)
open Function (update update_of_ne update_self update_apply)
open Observable (conj_coe)
open Unitary (coe_star)
open Submonoid (coe_mul)
open DynamicCircuit (qc_wp_circuit_compile compile_circuit)
open scoped Matrix BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator Circuit.Notation
local instance (priority := 1000000) instNeZeroTwoPowLegs (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩
/-! ## Section 1: Modular `30`-State Index-Magnitude Loader (`Mag30Circ2` / `Mag30Bundle2`) -/

/-- Computable `{Var : Type}` `0`-scratch `5`-wire `L = 30` index-magnitude circuit carrier
(`tMag` `T`, `0 TOFF`), usable in computable programs and `{Var : Type}` cost theorems. -/
structure Mag30Circ2 (Var : Type) (tMag : ℕ) where
  fwdDyn : ∀ {N : ℕ}, QRegister 5 N → DynamicCircuit Var N
  invDyn : ∀ {N : ℕ}, QRegister 5 N → DynamicCircuit Var N
  count_fwd_toff : ∀ {N : ℕ} (r : QRegister 5 N), (fwdDyn r).count .TOFF = 0
  count_inv_toff : ∀ {N : ℕ} (r : QRegister 5 N), (invDyn r).count .TOFF = 0
  count_fwd_t : ∀ {N : ℕ} (r : QRegister 5 N), (fwdDyn r).count .T = tMag
  count_inv_t : ∀ {N : ℕ} (r : QRegister 5 N), (invDyn r).count .T = tMag
  support_fwd_sub : ∀ {N : ℕ} (r : QRegister 5 N), (fwdDyn r).support ⊆ r.image
  support_inv_sub : ∀ {N : ℕ} (r : QRegister 5 N), (invDyn r).support ⊆ r.image
/-- Computable `72-T` (`0 TOFF`) `Mag30Circ2` backed by `factoredMag30T72Circuit`. -/
def Mag30Circ2.t72 (Var : Type) : Mag30Circ2 Var 72 where
  fwdDyn r := factoredMag30T72Dyn r
  invDyn r := unprepFactoredMag30T72Dyn r
  count_fwd_toff := countFactoredMag30T72Dyn_toff
  count_inv_toff := countUnprepFactoredMag30T72Dyn_toff
  count_fwd_t := countFactoredMag30T72Dyn_t
  count_inv_t := countUnprepFactoredMag30T72Dyn_t
  support_fwd_sub r := by
    unfold factoredMag30T72Dyn
    exact DynamicCircuit.circuit_support_onRegister_subset r _
  support_inv_sub r := by
    unfold unprepFactoredMag30T72Dyn
    exact DynamicCircuit.circuit_support_onRegister_subset r _
/-- Modular `0`-scratch `5`-wire `L = 30` index-magnitude state-preparation package (`tMag` `T`,
`0 TOFF`), extending `Mag30Circ2` with QHL `CleanRealizes` and support vanishing on `30 ≤ x`. -/
structure Mag30Bundle2 (Var : Type) [Fintype Var] [DecidableEq Var]
    (tMag : ℕ) (uIdx : Unitary (2 ^ 5)) extends Mag30Circ2 Var tMag where
  clean_fwd : ∀ {N s : ℕ} (v : Var) (r : QRegister 5 N) (rScr : QRegister s N),
    r.DisjointWires rScr → Solution.CleanDyn.CleanRealizes v r rScr uIdx (fwdDyn r)
  clean_inv : ∀ {N s : ℕ} (v : Var) (r : QRegister 5 N) (rScr : QRegister s N),
    r.DisjointWires rScr → Solution.CleanDyn.CleanRealizes v r rScr uIdx⁻¹ (invDyn r)
  vanish_ge30 : ∀ (x : Fin (2 ^ 5)), 30 ≤ x.val → (uIdx.1 *ᵥ basisState 0) x = 0
/-- `72-T` (`0 TOFF`) `Mag30Bundle2` backed by `factoredMag30T72Circuit`. -/
def Mag30Bundle2.t72 (Var : Type) [Fintype Var] [DecidableEq Var] :
    Mag30Bundle2 Var 72 factoredMag30T72Circuit.eval where
  toMag30Circ2 := Mag30Circ2.t72 Var
  clean_fwd := cleanRealizesFactoredMag30T72Dyn
  clean_inv := cleanRealizesUnprepFactoredMag30T72Dyn
  vanish_ge30 := factoredMag30T72Circuit_vanish
/-! ## Section 2: Modular `128 × 14` One-Hot Loader (`OneHot14LoadCirc2` / `OneHot14LoadBundle_3`)
-/

open SelectSwapQROM GroupUnary
theorem preservesWires_comm_predProj_oneHot {N L : ℕ} {M : Operator (2 ^ N)} {rHot : QRegister L N}
    (hPres : PreservesWires M rHot.image) :
    M * predProj (oneHotPred rHot) = predProj (oneHotPred rHot) * M :=
  preservesWires_comm_predProj hPres fun α β h ↦ by
    have hH (c : Fin L) := h _ ((QRegister.mem_image rHot _).mpr ⟨c, rfl⟩)
    unfold oneHotPred
    exact decide_eq_decide.mpr
      ⟨fun ⟨c₀, hc⟩ ↦ ⟨c₀, fun c ↦ (hH c).symm.trans (hc c)⟩,
       fun ⟨c₀, hc⟩ ↦ ⟨c₀, fun c ↦ (hH c).trans (hc c)⟩⟩
/-- Computable `{Var : Type}` `128 × 14` one-hot QROM loader circuit carrier
(`tLoad14` `T`, `0 TOFF`, `sQrom ≤ sScr`). -/
structure OneHot14LoadCirc2 (Var : Type) (sQrom tLoad14 : ℕ) where
  loadDyn : ∀ {N sScr : ℕ}, Var → (rQrom : QRegister (5 + 128 + 14) N) →
    (rScr : QRegister sScr N) → sQrom ≤ sScr → rQrom.DisjointWires rScr → DynamicCircuit Var N
  count_toff : ∀ {N sScr : ℕ} (v : Var) (rQrom : QRegister (5 + 128 + 14) N)
    (rScr : QRegister sScr N) (hs : sQrom ≤ sScr) (hdisj : rQrom.DisjointWires rScr),
    (loadDyn v rQrom rScr hs hdisj).count .TOFF = 0
  count_t : ∀ {N sScr : ℕ} (v : Var) (rQrom : QRegister (5 + 128 + 14) N)
    (rScr : QRegister sScr N) (hs : sQrom ≤ sScr) (hdisj : rQrom.DisjointWires rScr),
    (loadDyn v rQrom rScr hs hdisj).count .T = tLoad14
/-- Build computable `{Var : Type}` `OneHot14LoadCirc2` (`60 + 2 * R + 2 * G` `T`, `33` scratch)
from any `HGadgetSymp14Plan R G`. -/
def OneHot14LoadCirc2.ofHGadgetPlan (Var : Type) {R G : ℕ} (P : HGadgetSymp14Plan R G) :
    OneHot14LoadCirc2 Var 33 (60 + 2 * R + 2 * G) where
  loadDyn v rQrom rScr hs hdisj := qromHGadgetSymp14FromHot128LoadDyn v P rQrom rScr hs hdisj
  count_toff v rQrom rScr hs hdisj :=
    count_qromHGadgetSymp14FromHot128LoadDyn_toff v P rQrom rScr hs hdisj
  count_t v rQrom rScr hs hdisj :=
    count_qromHGadgetSymp14FromHot128LoadDyn_t v P rQrom rScr hs hdisj
/-- Modular `128 × 14` one-hot QROM loader package (`tLoad14` `T`, `0 TOFF`, `sQrom ≤ sScr`),
extending `OneHot14LoadCirc2` with `CleanPredRealizes` on `oneHotPred`. -/
structure OneHot14LoadBundle_3 (Var : Type) [Fintype Var] [DecidableEq Var]
    (sQrom tLoad14 : ℕ) (boolTbl : Fin 128 → Fin (2 ^ 5) → Fin 14 → Bool)
    extends OneHot14LoadCirc2 Var sQrom tLoad14 where
  clean2 : ∀ {N sScr : ℕ} (v : Var) (rQrom : QRegister (5 + 128 + 14) N)
    (rScr : QRegister sScr N) (hs : sQrom ≤ sScr) (hdisj : rQrom.DisjointWires rScr),
    CleanPredRealizes v
      (Mobius126OneHot.cleanPredProj rScr.image (oneHotPred (rQrom.slice 5 128 (by decide))))
      (rQrom.embedUnitary (aliasTableXorUnitary (5 + 128) 14 (hotLinearTargetFn 5 128 14 boolTbl)))
      (loadDyn v rQrom rScr hs hdisj)
/-- Build `OneHot14LoadBundle_3` (`60 + 2 * R + 2 * G` `T`, `33` scratch) from any
  `HGadgetSymp14Plan`
whose `targetBoolTable` equals `boolTbl`. -/
def OneHot14LoadBundle_3.ofHGadgetPlan (Var : Type) [Fintype Var] [DecidableEq Var]
    {R G : ℕ} (P : HGadgetSymp14Plan R G)
    (boolTbl : Fin 128 → Fin (2 ^ 5) → Fin 14 → Bool) (hTbl : P.targetBoolTable = boolTbl) :
    OneHot14LoadBundle_3 Var 33 (60 + 2 * R + 2 * G) boolTbl where
  toOneHot14LoadCirc2 := OneHot14LoadCirc2.ofHGadgetPlan Var P
  clean2 v rQrom rScr hs hdisj := by
    rw [← hTbl]
    exact cleanPredRealizes_qromHGadgetSymp14FromHot128LoadDyn v P rQrom rScr hs hdisj
theorem mid159Xo7Reg_disjoint_qro : mid159Xo7Reg.DisjointWires mid159QroReg :=
  QRegister.disjoint_iff.mpr fun b i hij ↦ by
    have hv := congrArg Fin.val hij
    have hb := b.isLt
    have hi := i.isLt
    simp only [mid159Xo7Reg, mid159Xo7InCtx, midGen18CtxReg, mid159QroReg,
      midGen18QromReg_apply_val, mid161Hot128InCtx, QRegister.compose_apply,
      QRegister.block_apply_val, mMidUB] at hv
    split_ifs at hv <;> omega
theorem mid159Hot128Reg_eq_qrom (c : Fin 128) :
    mid159Hot128Reg c = mid159QroReg ⟨5 + c.val, by omega⟩ := by
  apply Fin.ext
  have hc := c.isLt
  simp only [mid159Hot128Reg, midGen18CtxReg, mid159QroReg, midGen18QromReg_apply_val,
    mid161Hot128InCtx, QRegister.compose_apply, QRegister.block_apply_val, mMidUB]
  split_ifs <;> omega
theorem oneHotPred_perm_eq {N : ℕ} (r1 r2 : QRegister 128 N) (ρ : Equiv.Perm (Fin 128))
    (hPerm : ∀ c : Fin 128, r1 c = r2 (ρ c)) :
    oneHotPred r1 = oneHotPred r2 := by
  funext β
  unfold oneHotPred
  refine decide_eq_decide.mpr ⟨fun ⟨c₀, hc⟩ ↦ ⟨ρ c₀, fun d ↦ ?_⟩,
    fun ⟨d₀, hd⟩ ↦ ⟨ρ.symm d₀, fun c ↦ ?_⟩⟩
  · have h1 := hc (ρ.symm d)
    rw [hPerm (ρ.symm d), ρ.apply_symm_apply] at h1
    rw [h1]
    congr 1
    exact propext ⟨fun h ↦ by rw [← h, ρ.apply_symm_apply],
      fun h ↦ by rw [h, ρ.symm_apply_apply]⟩
  · rw [hPerm c, hd (ρ c)]
    congr 1
    exact propext ⟨fun h ↦ by rw [← h, ρ.symm_apply_apply],
      fun h ↦ by rw [h, ρ.apply_symm_apply]⟩
theorem xo7OneHotClearCirc_mul_qrom14_mul_self {N : ℕ}
    (r : QRegister (mMidUB 18 + (7 + 128)) N) (rHotOrig : QRegister 128 N)
    (hXoHot : (r.compose mid159Xo7Reg).DisjointWires rHotOrig)
    (hHotIn : ∀ c : Fin 128, ∃ c' : Fin 128, rHotOrig c = (r.compose mid159Hot128Reg) c')
    (F : Fin (2 ^ (5 + 128)) → BitAssignment 14) :
    let C := xo7OneHotClearCirc (r.compose mid159Xo7Reg) rHotOrig hXoHot
    let U := (r.compose mid159QroReg).embedUnitary (aliasTableXorUnitary (5 + 128) 14 F)
    C.eval * U * C.eval = U := by
  intro C U
  let rXo := r.compose mid159Xo7Reg
  have hXoQr : rXo.DisjointWires (r.compose mid159QroReg) :=
    compose_disjoint_zc20 r mid159Xo7Reg_disjoint_qro
  apply Subtype.ext
  refine Solution.CircuitModular.UnsignedGivens.matrix_ext_ket fun γ ↦ ?_
  have hUmul (δ : BitAssignment N) : U.1.mulVec (Solution.CircuitModular.UnsignedGivens.ket δ) =
      Solution.CircuitModular.UnsignedGivens.ket (CoherentAlias.writeReg δ (r.compose mid159QroReg)
        (aliasTableXorBits (5 + 128) 14 F (fun i ↦ δ ((r.compose mid159QroReg) i)))) := by
    change ((r.compose mid159QroReg).embedUnitary
      (aliasTableXorUnitary (5 + 128) 14 F)).1 *ᵥ CoherentAlias.ket δ = _
    rw [aliasTableXorUnitary, CoherentAlias.embedUnitary_bitPermUnitary_mulVec_ket]
    rfl
  simp only [Submonoid.coe_mul, ← mulVec_mulVec]
  rw [ket_xo7OneHotClearCirc, hUmul, ket_xo7OneHotClearCirc, hUmul]
  set γ₁ := CoherentAlias.writeReg γ rXo fun b ↦
    γ (rXo b) + maskSumBit rHotOrig (xoBitMask128 b) γ with hγ₁
  have hQrIn : (fun i ↦ γ₁ ((r.compose mid159QroReg) i)) =
      fun i ↦ γ ((r.compose mid159QroReg) i) := funext fun i ↦ by
    rw [hγ₁]
    exact CoherentAlias.writeReg_apply_of_not_mem _ _ _ _ fun ⟨b, hb⟩ ↦ hXoQr.ne b i hb
  set γ₂ := CoherentAlias.writeReg γ₁ (r.compose mid159QroReg)
    (aliasTableXorBits (5 + 128) 14 F (fun i ↦ γ₁ ((r.compose mid159QroReg) i))) with hγ₂
  have hHotEq (c : Fin 128) : γ₂ (rHotOrig c) = γ (rHotOrig c) := by
    obtain ⟨c', hc'⟩ := hHotIn c
    have hcEq : rHotOrig c = (r.compose mid159QroReg) ⟨5 + c'.val, by omega⟩ :=
      hc'.trans (congrArg r (mid159Hot128Reg_eq_qrom c'))
    rw [hγ₂, hcEq, CoherentAlias.writeReg_apply_reg, hQrIn]
    simp [aliasTableXorBits, show ¬ (5 + 128 ≤ 5 + c'.val) by omega]
  apply congrArg Solution.CircuitModular.UnsignedGivens.ket
  funext w
  by_cases hwXo : w ∈ Set.range rXo.wires
  · obtain ⟨b, rfl⟩ := hwXo
    have hnotQr : rXo b ∉ Set.range (r.compose mid159QroReg).wires :=
      fun ⟨i, hi⟩ ↦ hXoQr.ne b i hi.symm
    have hMask : maskSumBit rHotOrig (xoBitMask128 b) γ₂ = maskSumBit rHotOrig (xoBitMask128 b) γ :=
      Finset.sum_congr rfl fun c _ ↦ by rw [hHotEq c]
    rw [CoherentAlias.writeReg_apply_reg, CoherentAlias.writeReg_apply_of_not_mem _ _ _ _ hnotQr,
      hMask, hγ₂, CoherentAlias.writeReg_apply_of_not_mem _ _ _ _ hnotQr, hγ₁,
      CoherentAlias.writeReg_apply_reg, add_assoc, CharTwo.add_self_eq_zero, add_zero]
  · rw [CoherentAlias.writeReg_apply_of_not_mem _ _ _ _ hwXo]
    by_cases hwQr : w ∈ Set.range (r.compose mid159QroReg).wires
    · obtain ⟨i, rfl⟩ := hwQr
      rw [hγ₂, CoherentAlias.writeReg_apply_reg, CoherentAlias.writeReg_apply_reg, hQrIn]
    · rw [hγ₂, CoherentAlias.writeReg_apply_of_not_mem _ _ _ _ hwQr, hγ₁,
        CoherentAlias.writeReg_apply_of_not_mem _ _ _ _ hwXo]
      exact (CoherentAlias.writeReg_apply_of_not_mem _ _ _ _ hwQr).symm
theorem preservesWiresMid159Qroxo_hot {N : ℕ} (r : QRegister (mMidUB 18 + (7 + 128)) N)
    (rHotOrig : QRegister 128 N)
    (hHotIn : ∀ c : Fin 128, ∃ c' : Fin 128, rHotOrig c = (r.compose mid159Hot128Reg) c')
    (F : Fin (2 ^ (5 + 128)) → BitAssignment 14) :
    PreservesWires ((r.compose mid159QroReg).embedUnitary
      (aliasTableXorUnitary (5 + 128) 14 F)).1
      ((r.compose mid159Xo7Reg).image ∪ rHotOrig.image) := by
  intro i j ⟨w, hw, hne⟩
  have hket : ((r.compose mid159QroReg).embedUnitary
      (aliasTableXorUnitary (5 + 128) 14 F)).1 i j =
      (((r.compose mid159QroReg).embedUnitary
        (aliasTableXorUnitary (5 + 128) 14 F)).1 *ᵥ CoherentAlias.ket (basisBits N j)) i := by
    simp [CoherentAlias.ket, basisState]
  rw [hket, aliasTableXorUnitary, CoherentAlias.embedUnitary_bitPermUnitary_mulVec_ket]
  have hSame : CoherentAlias.writeReg (basisBits N j) (r.compose mid159QroReg)
      (aliasTableXorBits (5 + 128) 14 F (fun m ↦ basisBits N j ((r.compose mid159QroReg) m)))
      w = basisBits N j w := by
    rcases Finset.mem_union.mp hw with hXo | hHot
    · obtain ⟨b, rfl⟩ := (QRegister.mem_image _ w).mp hXo
      exact CoherentAlias.writeReg_apply_of_not_mem _ _ _ _ fun ⟨m, hm⟩ ↦
        (compose_disjoint_zc20 r mid159Xo7Reg_disjoint_qro).ne b m hm.symm
    · obtain ⟨c, rfl⟩ := (QRegister.mem_image _ w).mp hHot
      obtain ⟨c', hc'⟩ := hHotIn c
      have hcEq : rHotOrig c = (r.compose mid159QroReg) ⟨5 + c'.val, by omega⟩ :=
        hc'.trans (congrArg r (mid159Hot128Reg_eq_qrom c'))
      rw [hcEq, CoherentAlias.writeReg_apply_reg]
      simp [aliasTableXorBits, show ¬ (5 + 128 ≤ 5 + c'.val) by omega]
  rw [CoherentAlias.ket, basisState, Pi.single_eq_of_ne]
  rintro rfl
  rw [SelectSwapQROM.basisBits_symm] at hne
  exact hne hSame
/-- `rXo7`-borrowing wrapper around any `14`-plane `qromLoad` (`0` extra `T`, `0` extra `TOFF`). -/
def qromXoBorrowLoad14GenDyn {Var : Type} {N : ℕ} (r : QRegister (mMidUB 18 + (7 + 128)) N)
    (rHotOrig : QRegister 128 N) (hXoHot : (r.compose mid159Xo7Reg).DisjointWires rHotOrig)
    (qromLoad : DynamicCircuit Var N) : DynamicCircuit Var N :=
  let cClear := DynamicCircuit.circuit (Var := Var)
    (xo7OneHotClearCirc (r.compose mid159Xo7Reg) rHotOrig hXoHot)
  .seq cClear (.seq qromLoad cClear)
@[simp] theorem countQromXoBorrowLoad14GenDyn_toff {Var : Type} {N : ℕ}
    (r : QRegister (mMidUB 18 + (7 + 128)) N) (rHotOrig : QRegister 128 N)
    (hXoHot : (r.compose mid159Xo7Reg).DisjointWires rHotOrig) {qromLoad : DynamicCircuit Var N}
    (hq : qromLoad.count .TOFF = 0) :
    (qromXoBorrowLoad14GenDyn r rHotOrig hXoHot qromLoad).count .TOFF = 0 := by
  dsimp only [qromXoBorrowLoad14GenDyn]
  simp [DynamicCircuit.count, count_xo7OneHotClearCirc_toff, hq]
@[simp] theorem countQromXoBorrowLoad14GenDyn_t {Var : Type} {N : ℕ}
    (r : QRegister (mMidUB 18 + (7 + 128)) N) (rHotOrig : QRegister 128 N)
    (hXoHot : (r.compose mid159Xo7Reg).DisjointWires rHotOrig) (qromLoad : DynamicCircuit Var N) :
    (qromXoBorrowLoad14GenDyn r rHotOrig hXoHot qromLoad).count .T = qromLoad.count .T := by
  dsimp only [qromXoBorrowLoad14GenDyn]
  simp [DynamicCircuit.count, count_xo7OneHotClearCirc_t]
theorem predProj_oneHot_comm_xo7Clear {N : ℕ} (rXo : QRegister 7 N) (rHot : QRegister 128 N)
    (hXoHot : rXo.DisjointWires rHot) :
    predProj (oneHotPred rHot) * (xo7OneHotClearCirc rXo rHot hXoHot).eval.1 =
      (xo7OneHotClearCirc rXo rHot hXoHot).eval.1 * predProj (oneHotPred rHot) := by
  symm
  refine preservesWires_comm_predProj_oneHot ?_
  intro i j ⟨w, hw, hne⟩
  obtain ⟨c, rfl⟩ := (QRegister.mem_image rHot w).mp hw
  have hket : (xo7OneHotClearCirc rXo rHot hXoHot).eval.1 i j =
      ((xo7OneHotClearCirc rXo rHot hXoHot).eval.1 *ᵥ
        Solution.CircuitModular.UnsignedGivens.ket (basisBits N j)) i :=
    by simp [Solution.CircuitModular.UnsignedGivens.ket, basisState]
  rw [hket, ket_xo7OneHotClearCirc]
  have hSame : CoherentAlias.writeReg (basisBits N j) rXo
      (fun b ↦ basisBits N j (rXo b) + maskSumBit rHot (xoBitMask128 b) (basisBits N j)) (rHot c) =
      basisBits N j (rHot c) :=
    CoherentAlias.writeReg_apply_of_not_mem _ _ _ _ fun ⟨b, hb⟩ ↦ hXoHot.ne b c hb
  have hiNe : i ≠ (basisBits N).symm (CoherentAlias.writeReg (basisBits N j) rXo
      (fun b ↦ basisBits N j (rXo b) + maskSumBit rHot (xoBitMask128 b) (basisBits N j))) :=
    fun hEq ↦ by
      subst hEq
      exact hne (by rw [SelectSwapQROM.basisBits_symm, hSame])
  rw [Solution.CircuitModular.UnsignedGivens.ket, basisState, Pi.single_eq_of_ne hiNe]
/-- `CleanPredRealizes` for `qromXoBorrowLoad14GenDyn` on any `oneHotPred`-subspace loader. -/
theorem cleanPredRealizesQromXoBorrowLoad14GenDyn {Var : Type} [Fintype Var] [DecidableEq Var]
    {N sTail : ℕ} (v : Var) (r : QRegister (mMidUB 18 + (7 + 128)) N) (rHotOrig : QRegister 128 N)
    (rTail : QRegister sTail N) (hXoHot : (r.compose mid159Xo7Reg).DisjointWires rHotOrig)
    (hHotPerm : ∃ ρ : Equiv.Perm (Fin 128), ∀ c : Fin 128,
      (r.compose mid159Hot128Reg) c = rHotOrig (ρ c))
    (hdisj : r.DisjointWires rTail) (F : Fin (2 ^ (5 + 128)) → BitAssignment 14)
    {qromLoad : DynamicCircuit Var N} (hqrom : CleanPredRealizes v
      (Mobius126OneHot.cleanPredProj
        ((r.compose mid159Xo7Reg).concat rTail (hdisj.compose_left mid159Xo7Reg)).image
        (oneHotPred ((r.compose mid159QroReg).slice 5 128 (by decide))))
      ((r.compose mid159QroReg).embedUnitary (aliasTableXorUnitary (5 + 128) 14 F))
      qromLoad) :
    CleanPredRealizes v
      (Mobius126OneHot.cleanPredProj rTail.image
        (xoOneHotPred (r.compose mid159Xo7Reg) rHotOrig))
      ((r.compose mid159QroReg).embedUnitary (aliasTableXorUnitary (5 + 128) 14 F))
      (qromXoBorrowLoad14GenDyn r rHotOrig hXoHot qromLoad) := by
  obtain ⟨ρ, hρ⟩ := hHotPerm
  have hHotIn : ∀ c : Fin 128, ∃ c' : Fin 128, rHotOrig c = (r.compose mid159Hot128Reg) c' :=
    fun c ↦ ⟨ρ.symm c, by rw [hρ (ρ.symm c), ρ.apply_symm_apply]⟩
  let rXo := r.compose mid159Xo7Reg
  have hXoTail := hdisj.compose_left mid159Xo7Reg
  let cClear := xo7OneHotClearCirc rXo rHotOrig hXoHot
  let Q_xo := Mobius126OneHot.cleanPredProj rTail.image (xoOneHotPred rXo rHotOrig)
  let S_b := (rXo.concat rTail hXoTail).image
  let P_b := zeroProjOn S_b
  let rHotQ := (r.compose mid159QroReg).slice 5 128 (by decide)
  let P_q := Mobius126OneHot.cleanPredProj S_b (oneHotPred rHotQ)
  let U_q := (r.compose mid159QroReg).embedUnitary (aliasTableXorUnitary (5 + 128) 14 F)
  have hHotQEq : oneHotPred rHotQ = oneHotPred rHotOrig := oneHotPred_perm_eq rHotQ rHotOrig ρ
    fun c ↦ (congrArg r (mid159Hot128Reg_eq_qrom c).symm).trans (hρ c)
  have hQxoH : Q_xoᴴ = Q_xo := cleanPredProj_conjTranspose _ _
  have hPqH : P_qᴴ = P_q := cleanPredProj_conjTranspose _ _
  have hCH : cClear.eval.1ᴴ = cClear.eval.1 := xo7OneHotClearCirc_conjTranspose rXo rHotOrig hXoHot
  have hAbsZ : P_b * (cClear.eval.1 * Q_xo) = cClear.eval.1 * Q_xo :=
    zeroProjOn_borrow_mul_clear_cleanPredProj rXo rHotOrig rTail hXoHot hXoTail
  have hAbsP : P_q * (cClear.eval.1 * Q_xo) = cClear.eval.1 * Q_xo := by
    dsimp only [P_q]
    rw [hHotQEq, ← predProj_mul_zeroProjOn_eq_cleanPredProj, Matrix.mul_assoc,
      hAbsZ, ← Matrix.mul_assoc, predProj_oneHot_comm_xo7Clear rXo rHotOrig hXoHot,
      Matrix.mul_assoc]
    suffices predProj (oneHotPred rHotOrig) * Q_xo = Q_xo by rw [this]
    apply SelectSwapQROM.matrix_ext_ket
    intro β
    dsimp only [Q_xo]
    rw [← predProj_mul_zeroProjOn_eq_cleanPredProj, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      SelectSwapQROM.zeroProjOn_mulVec_ket]
    by_cases hz : ∀ w ∈ rTail.image, β w = 0
    · rw [ite_eq_left hz, StepOuter8Pi145Outer.predProj_mulVec_ket]
      by_cases hx : xoOneHotPred rXo rHotOrig β = true
      · rw [ite_eq_left hx, StepOuter8Pi145Outer.predProj_mulVec_ket,
          ite_eq_left (xoOneHotPred_implies_oneHotPred rXo rHotOrig β hx)]
      · rw [ite_eq_right hx, Matrix.mulVec_zero]
    · rw [ite_eq_right hz, Matrix.mulVec_zero, Matrix.mulVec_zero]
  have hCU : cClear.eval.1 * U_q.1 * cClear.eval.1 = U_q.1 := by
    simpa only [Submonoid.coe_mul] using
      congrArg Subtype.val (xo7OneHotClearCirc_mul_qrom14_mul_self r rHotOrig hXoHot hHotIn F)
  have hCUH : cClear.eval.1 * U_q.1ᴴ * cClear.eval.1 = U_q.1ᴴ := by
    simpa only [conjTranspose_mul, hCH, ← Matrix.mul_assoc] using congrArg (·ᴴ) hCU
  have hPresUq := preservesWiresMid159Qroxo_hot r rHotOrig hHotIn F
  have hCommT : zeroProjOn rTail.image * U_q.1ᴴ = U_q.1ᴴ * zeroProjOn rTail.image := by
    have hc := preservesWires_comm_zeroProjOn (preservesWires_embedMatrix_of_disjoint
      (r.compose mid159QroReg) (aliasTableXorUnitary (5 + 128) 14 F).1 rTail.image
      (disjoint_image_of_disjointWires (hdisj.compose_left _))) Finset.Subset.rfl
    change zeroProjOn rTail.image *
        ((r.compose mid159QroReg).embedMatrix (aliasTableXorUnitary (5 + 128) 14 F).1)ᴴ =
      ((r.compose mid159QroReg).embedMatrix (aliasTableXorUnitary (5 + 128) 14 F).1)ᴴ *
        zeroProjOn rTail.image
    simpa only [conjTranspose_mul, zeroProjOn_conjTranspose] using congrArg (·ᴴ) hc
  have hCommP : predProj (xoOneHotPred rXo rHotOrig) * U_q.1ᴴ =
      U_q.1ᴴ * predProj (xoOneHotPred rXo rHotOrig) := by
    simpa only [conjTranspose_mul, predProj_conjTranspose] using
      congrArg (·ᴴ) (preservesWires_comm_predProj_xoOneHot (rXo := rXo) (rHot := rHotOrig) hPresUq)
  have hC {Ψ : QCAssertion Var (2 ^ N)} (hΨ : ∀ τ b, Ψ (Function.update τ v b) = Ψ τ)
      (τ : Store Var) (b : ℤ) :
      wp (DynamicCircuit.circuit cClear).compile Ψ (Function.update τ v b) =
        wp (DynamicCircuit.circuit cClear).compile Ψ τ := by
    simp [qcWpQAssign, hΨ τ b]
  refine ⟨countQromXoBorrowLoad14GenDyn_toff r rHotOrig hXoHot hqrom.1, ?_,
    fun Θ hΘ σ val ↦ hC (hqrom.2.2.1 _ (hC hΘ)) σ val, fun Θ hΘ σ ↦ ?_⟩
  · dsimp only [Q_xo, Mobius126OneHot.cleanPredProj]
    rw [Matrix.mul_assoc, hCommP, ← Matrix.mul_assoc, hCommT, Matrix.mul_assoc]
  · change ((wp (qromXoBorrowLoad14GenDyn r rHotOrig hXoHot qromLoad).compile Θ σ).1).conj Q_xo =
      ((qcWpQAssign U_q Θ σ).1).conj Q_xo
    apply HermitianMat.ext
    simp only [conj_apply_mat, hQxoH, qcWpQAssign, qcQAssignObsMap, Observable.conj_coe, coe_star,
      star_eq_conjTranspose, conjTranspose_conjTranspose]
    let Ψ_c := wp (DynamicCircuit.circuit cClear).compile Θ
    have hCMat (Φ : QCAssertion Var (2 ^ N)) :
        (wp (DynamicCircuit.circuit cClear).compile Φ σ).1.mat =
          cClear.eval.1 * (Φ σ).1.mat * cClear.eval.1 := by
      simp [qcWpQAssign, qcQAssignObsMap, Observable.conj_coe, conj_apply_mat, coe_star,
        star_eq_conjTranspose, hCH]
    have hQMat : P_q * (wp qromLoad.compile Ψ_c σ).1.mat * P_q =
        P_q * (U_q.1ᴴ * (Ψ_c σ).1.mat * U_q.1) * P_q := by
      have hqrC : ((wp qromLoad.compile Ψ_c σ).1).conj P_q =
          ((qcWpQAssign U_q Ψ_c σ).1).conj P_q := hqrom.2.2.2 Ψ_c (hC hΘ) σ
      have hv := congrArg HermitianMat.mat hqrC
      simpa only [conj_apply_mat, hPqH, qcWpQAssign, qcQAssignObsMap, Observable.conj_coe,
        coe_star, star_eq_conjTranspose, conjTranspose_conjTranspose] using hv
    have hStep : (wp (qromXoBorrowLoad14GenDyn r rHotOrig hXoHot qromLoad).compile Θ σ).1.mat =
        cClear.eval.1 * (wp qromLoad.compile Ψ_c σ).1.mat * cClear.eval.1 := by
      unfold qromXoBorrowLoad14GenDyn
      dsimp only
      rw [DynamicCircuit.compile_seq, DynamicCircuit.compile_seq, wp_qSeq, wp_qSeq]
      exact hCMat _
    let E := cClear.eval.1 * Q_xo
    have hEP (M : Operator (2 ^ N)) : Eᴴ * (P_q * M * P_q) * E = Eᴴ * M * E := by
      have hL : Eᴴ * P_q = Eᴴ := by
        calc Eᴴ * P_q = (P_q * E)ᴴ := by rw [conjTranspose_mul P_q E, hPqH]
          _ = Eᴴ := by rw [hAbsP]
      calc Eᴴ * (P_q * M * P_q) * E = (Eᴴ * P_q) * M * (P_q * E) := by simp only [Matrix.mul_assoc]
        _ = Eᴴ * M * E := by rw [hL, hAbsP]
    have hWrap (M : Operator (2 ^ N)) :
        Q_xo * (cClear.eval.1 * M * cClear.eval.1) * Q_xo = Eᴴ * M * E := by
      dsimp only [E]
      rw [conjTranspose_mul, hCH, hQxoH]
      simp only [Matrix.mul_assoc]
    have hAssoc : Q_xo * cClear.eval.1 *
        (U_q.1ᴴ * (cClear.eval.1 * (Θ σ).1.mat * cClear.eval.1) * U_q.1) * (cClear.eval.1 * Q_xo) =
      Q_xo * ((cClear.eval.1 * U_q.1ᴴ * cClear.eval.1) * (Θ σ).1.mat *
        (cClear.eval.1 * U_q.1 * cClear.eval.1)) * Q_xo := by simp only [Matrix.mul_assoc]
    rw [hStep, hWrap, ← hEP, hQMat, hEP, show (Ψ_c σ).1.mat = _ from hCMat Θ]
    dsimp only [E]
    rw [conjTranspose_mul, hCH, hQxoH, hAssoc, hCUH, hCU]
attribute [irreducible] qromXoBorrowLoad14GenDyn
theorem midSub18_disjoint_xo_hot {N k : ℕ} (r : QRegister (mMidUB 18 + (7 + 128)) N)
    (rHotOrig : QRegister 128 N)
    (hHotIn : ∀ c : Fin 128, ∃ c' : Fin 128, rHotOrig c = (r.compose mid159Hot128Reg) c')
    (sub : QRegister k (mMidUB 18)) :
    (r.compose ((midGen18MidReg (7 + 128)).compose sub)).DisjointWires (r.compose mid159Xo7Reg) ∧
    (r.compose ((midGen18MidReg (7 + 128)).compose sub)).DisjointWires rHotOrig := by
  have hMC : (midGen18MidReg (7 + 128)).DisjointWires (midGen18CtxReg (7 + 128)) :=
    (midGen18Ctx_disjoint_mid (7 + 128)).symm
  refine ⟨compose_disjoint_zc20 r ((hMC.compose_left sub).compose_right _),
    QRegister.disjoint_iff.mpr fun i c hij ↦ ?_⟩
  obtain ⟨c', hc'⟩ := hHotIn c
  exact (compose_disjoint_zc20 r ((hMC.compose_left sub).compose_right _)).ne i c' (hij.trans hc')
/-- Computable `{Var : Type}` `23`-wire (`10 + 13`) clean mux-swap circuit carrier (`0 TOFF`, `tMux`
`T` gates, `sMuxReq ≤ sScr`), decoupled from `[Fintype Var] [DecidableEq Var]`. -/
structure Mux23Circ (Var : Type) (sMuxReq tMux : ℕ) where
  fwdDyn : ∀ {N sScr : ℕ}, Var → (rAct : QRegister (10 + 13) N) → (rScr : QRegister sScr N) →
    sMuxReq ≤ sScr → rAct.DisjointWires rScr → DynamicCircuit Var N
  invDyn : ∀ {N sScr : ℕ}, Var → (rAct : QRegister (10 + 13) N) → (rScr : QRegister sScr N) →
    sMuxReq ≤ sScr → rAct.DisjointWires rScr → DynamicCircuit Var N
  fwd_toff : ∀ {N sScr : ℕ} (v : Var) (rAct : QRegister (10 + 13) N) (rScr : QRegister sScr N)
    (hs : sMuxReq ≤ sScr) (hdisj : rAct.DisjointWires rScr),
    (fwdDyn v rAct rScr hs hdisj).count .TOFF = 0
  inv_toff : ∀ {N sScr : ℕ} (v : Var) (rAct : QRegister (10 + 13) N) (rScr : QRegister sScr N)
    (hs : sMuxReq ≤ sScr) (hdisj : rAct.DisjointWires rScr),
    (invDyn v rAct rScr hs hdisj).count .TOFF = 0
  fwd_t : ∀ {N sScr : ℕ} (v : Var) (rAct : QRegister (10 + 13) N) (rScr : QRegister sScr N)
    (hs : sMuxReq ≤ sScr) (hdisj : rAct.DisjointWires rScr),
    (fwdDyn v rAct rScr hs hdisj).count .T = tMux
  inv_t : ∀ {N sScr : ℕ} (v : Var) (rAct : QRegister (10 + 13) N) (rScr : QRegister sScr N)
    (hs : sMuxReq ≤ sScr) (hdisj : rAct.DisjointWires rScr),
    (invDyn v rAct rScr hs hdisj).count .T = tMux
/-- Certified `23`-wire (`10 + 13`) clean mux-swap package extending `Mux23Circ`. -/
structure Mux23Bundle (Var : Type)
    (sMuxReq tMux : ℕ) (muxBit : Fin (2 ^ 4) → Fin (2 ^ 9) → Bool)
    extends Mux23Circ Var sMuxReq tMux where
  fwd_cr : ∀ [Fintype Var] [DecidableEq Var] {N sScr : ℕ} (v : Var)
    (rAct : QRegister (10 + 13) N) (rScr : QRegister sScr N) (hs : sMuxReq ≤ sScr)
    (hdisj : rAct.DisjointWires rScr),
    Solution.CleanDyn.CleanRealizes v rAct rScr (pktMuxSwap23Unitary muxBit)
      (fwdDyn v rAct rScr hs hdisj)
  inv_cr : ∀ [Fintype Var] [DecidableEq Var] {N sScr : ℕ} (v : Var)
    (rAct : QRegister (10 + 13) N) (rScr : QRegister sScr N) (hs : sMuxReq ≤ sScr)
    (hdisj : rAct.DisjointWires rScr),
    Solution.CleanDyn.CleanRealizes v rAct rScr (pktMuxSwap23Unitary muxBit)⁻¹
      (invDyn v rAct rScr hs hdisj)
/-- Parametric `159`-wire `rXo7`-borrowing `PREP_mid` at `wInner2 = 18`
(`14 + tMux + qromLoad.count .T + uP.count .T` `T`, `0 TOFF`, `sMuxReq ≤ sTail`). -/
def prepMid18BorrowGenDyn {Var : Type} {sMuxReq tMux : ℕ}
    (bundleSpec : Mux23Circ Var sMuxReq tMux)
    {N sTail : ℕ} (v : Var) (r : QRegister (mMidUB 18 + (7 + 128)) N)
    (rHotOrig : QRegister 128 N) (rTail : QRegister sTail N)
    (hTail : sMuxReq ≤ sTail) (hXoHot : (r.compose mid159Xo7Reg).DisjointWires rHotOrig)
    (hdisj : r.DisjointWires rTail) (qromLoad uP : DynamicCircuit Var N) : DynamicCircuit Var N :=
  .seq uP
    (.seq (optCoin9Dyn (Var := Var) (r.compose (midGen18Pkt4Reg (7 + 128))))
      (.seq (qromXoBorrowLoad14GenDyn r rHotOrig hXoHot qromLoad)
        (.seq (bundleSpec.fwdDyn v (r.compose (midGen18MuxSwap23Reg (7 + 128))) rTail hTail
            (hdisj.compose_left _))
          (.circuit ((Circuit.H 0).onRegister (r.compose (midGen18Sig1Reg (7 + 128))))))))
@[simp] theorem countPrepMid18BorrowGenDyn_toff {Var : Type} {sMuxReq tMux : ℕ}
    (bundleSpec : Mux23Circ Var sMuxReq tMux) {N sTail : ℕ} (v : Var)
    (r : QRegister (mMidUB 18 + (7 + 128)) N) (rHotOrig : QRegister 128 N)
    (rTail : QRegister sTail N) (hTail : sMuxReq ≤ sTail)
    (hXoHot : (r.compose mid159Xo7Reg).DisjointWires rHotOrig) (hdisj : r.DisjointWires rTail)
    {qromLoad uP : DynamicCircuit Var N} (hq : qromLoad.count .TOFF = 0)
    (hu : uP.count .TOFF = 0) :
    (prepMid18BorrowGenDyn bundleSpec v r rHotOrig rTail hTail hXoHot hdisj qromLoad uP).count .TOFF
      =
      0 := by
  dsimp only [prepMid18BorrowGenDyn]
  simp only [DynamicCircuit.count, hu, countOptCoin9Dyn_toff,
    countQromXoBorrowLoad14GenDyn_toff _ _ _ hq, bundleSpec.fwd_toff, Circuit.count_onRegister]
  rfl
@[simp] theorem countPrepMid18BorrowGenDyn_t {Var : Type} {sMuxReq tMux : ℕ}
    (bundleSpec : Mux23Circ Var sMuxReq tMux) {N sTail : ℕ} (v : Var)
    (r : QRegister (mMidUB 18 + (7 + 128)) N) (rHotOrig : QRegister 128 N)
    (rTail : QRegister sTail N) (hTail : sMuxReq ≤ sTail)
    (hXoHot : (r.compose mid159Xo7Reg).DisjointWires rHotOrig) (hdisj : r.DisjointWires rTail)
    (qromLoad uP : DynamicCircuit Var N) :
    (prepMid18BorrowGenDyn bundleSpec v r rHotOrig rTail hTail hXoHot hdisj qromLoad uP).count .T =
      14 + tMux + qromLoad.count .T + uP.count .T := by
  dsimp only [prepMid18BorrowGenDyn]
  simp only [DynamicCircuit.count, countOptCoin9Dyn_t, countQromXoBorrowLoad14GenDyn_t,
    bundleSpec.fwd_t, Circuit.count_onRegister, show (Circuit.H (0 : Wire 1)).count .T = 0 from rfl]
  omega
theorem cleanPredRealizesPrepMid18BorrowGenDyn {Var : Type} [Fintype Var] [DecidableEq Var]
    {sMuxReq tMux : ℕ} {muxBit : Fin (2 ^ 4) → Fin (2 ^ 9) → Bool}
    (bundleSpec : Mux23Bundle Var sMuxReq tMux muxBit) {N sTail : ℕ} (v : Var)
    (r : QRegister (mMidUB 18 + (7 + 128)) N) (rHotOrig : QRegister 128 N)
    (rTail : QRegister sTail N) (hTail : sMuxReq ≤ sTail)
    (hXoHot : (r.compose mid159Xo7Reg).DisjointWires rHotOrig)
    (hHotPerm : ∃ ρ : Equiv.Perm (Fin 128), ∀ c : Fin 128,
      (r.compose mid159Hot128Reg) c = rHotOrig (ρ c))
    (hdisj : r.DisjointWires rTail) (uIdx : Unitary (2 ^ 5))
    (F : Fin (2 ^ (5 + 128)) → BitAssignment 14) {qromLoad uP : DynamicCircuit Var N}
    (hqrom : CleanPredRealizes v
      (Mobius126OneHot.cleanPredProj
        ((r.compose mid159Xo7Reg).concat rTail (hdisj.compose_left mid159Xo7Reg)).image
        (oneHotPred ((r.compose mid159QroReg).slice 5 128 (by decide))))
      ((r.compose mid159QroReg).embedUnitary (aliasTableXorUnitary (5 + 128) 14 F))
      qromLoad) (huP : Solution.CleanDyn.CleanRealizes v (r.compose mid159Idx5Reg) rTail uIdx uP) :
    CleanPredRealizes v
      (Mobius126OneHot.cleanPredProj rTail.image
        (xoOneHotPred (r.compose mid159Xo7Reg) rHotOrig))
      (r.embedUnitary (muxOnAct (mMidUB 18) (7 + 128) (hotBranch18Of muxBit uIdx F)))
      (prepMid18BorrowGenDyn bundleSpec.toMux23Circ v r rHotOrig rTail hTail hXoHot hdisj
        qromLoad uP) := by
  obtain ⟨ρ, hρ⟩ := hHotPerm
  have hHotIn : ∀ c : Fin 128, ∃ c' : Fin 128, rHotOrig c = (r.compose mid159Hot128Reg) c' :=
    fun c ↦ ⟨ρ.symm c, by rw [hρ (ρ.symm c), ρ.apply_symm_apply]⟩
  have lift {k : ℕ} {rS : QRegister k N} {V : Unitary (2 ^ k)} {P : DynamicCircuit Var N}
      (hP : Solution.CleanDyn.CleanRealizes v rS rTail V P) (sub : QRegister k (mMidUB 18))
      (hrS : rS = r.compose ((midGen18MidReg (7 + 128)).compose sub)) :
      CleanPredRealizes v
        (Mobius126OneHot.cleanPredProj rTail.image
          (xoOneHotPred (r.compose mid159Xo7Reg) rHotOrig))
        (rS.embedUnitary V) P := by
    have hd := midSub18_disjoint_xo_hot r rHotOrig hHotIn sub
    exact CleanPredRealizes.of_cleanRealizes_xoOneHot
      (hrS ▸ hdisj.compose_left _) (hrS ▸ hd.1) (hrS ▸ hd.2) hP
  have h1 := lift huP (mid18Core23Reg.compose core23IdxReg) rfl
  have h2 := lift (cleanRealizesOptCoin9Dyn v (r.compose (midGen18Pkt4Reg (7 + 128))) rTail
    (hdisj.compose_left _)) (mid18Core23Reg.compose core23PktReg) rfl
  have h3 := cleanPredRealizesQromXoBorrowLoad14GenDyn v r rHotOrig rTail hXoHot ⟨ρ, hρ⟩
    hdisj F hqrom
  have h4 := lift (bundleSpec.fwd_cr v (r.compose (midGen18MuxSwap23Reg (7 + 128))) rTail hTail
    (hdisj.compose_left _)) (mid18Core23Reg.compose Inner18Symp14Walk.core23MuxSwap23Reg) rfl
  have h5 := lift (Solution.CleanDyn.CleanRealizes.circuit v (r.compose (midGen18Sig1Reg (7 +
    128))) rTail
    (hdisj.compose_left _) (Circuit.H 0) rfl) (rSigInLoc 18) rfl
  have hseq := h1.seq (h2.seq (h3.seq (h4.seq h5)))
  have hUnitEq : (r.compose (midGen18Sig1Reg (7 + 128))).embedUnitary (Circuit.H 0).eval *
      ((r.compose (midGen18MuxSwap23Reg (7 + 128))).embedUnitary (pktMuxSwap23Unitary muxBit) *
        ((r.compose mid159QroReg).embedUnitary (aliasTableXorUnitary (5 + 128) 14 F) *
          ((r.compose (midGen18Pkt4Reg (7 + 128))).embedUnitary optCoin9Unitary *
            (r.compose mid159Idx5Reg).embedUnitary uIdx))) =
      r.embedUnitary (muxOnAct (mMidUB 18) (7 + 128) (hotBranch18Of muxBit uIdx F)) := by
    rw [← mux159_eq muxBit uIdx F]
    simp only [QRegister.embedUnitary_mul, QRegister.embedUnitary_compose]
  simp only [mul_assoc] at hseq
  rwa [hUnitEq] at hseq
attribute [irreducible] prepMid18BorrowGenDyn
/-- Generic `(mMidUB 18 + cBits)`-wire X-measurement `PREP_mid†` (`14 + tMux + t_qrom + t_uDP` `T`,
`0 TOFF`, `sMuxReq ≤ sScr`). -/
def genPrepMid18InvDyn {Var : Type} {sMuxReq tMux : ℕ}
    (bundleSpec : Mux23Circ Var sMuxReq tMux) {N cBits sScr : ℕ} (v : Var)
    (r : QRegister (mMidUB 18 + cBits) N) (rScr : QRegister sScr N) (hScr : sMuxReq ≤ sScr)
    (hdisj : r.DisjointWires rScr) (qromUnload uDP : DynamicCircuit Var N) : DynamicCircuit Var N :=
  .seq (.circuit ((Circuit.H 0).onRegister (r.compose (midGen18Sig1Reg cBits))))
    (.seq (bundleSpec.invDyn v (r.compose (midGen18MuxSwap23Reg cBits)) rScr hScr
      (hdisj.compose_left _))
      (.seq qromUnload (.seq (optCoin9InvDyn (r.compose (midGen18Pkt4Reg cBits))) uDP)))
@[simp] theorem countGenPrepMid18InvDyn_toff {Var : Type} {sMuxReq tMux : ℕ}
    (bundleSpec : Mux23Circ Var sMuxReq tMux) {N cBits sScr : ℕ} (v : Var)
    (r : QRegister (mMidUB 18 + cBits) N) (rScr : QRegister sScr N) (hScr : sMuxReq ≤ sScr)
    (hdisj : r.DisjointWires rScr) {qromUnload uDP : DynamicCircuit Var N}
    (hq : qromUnload.count .TOFF = 0) (hu : uDP.count .TOFF = 0) :
    (genPrepMid18InvDyn bundleSpec v r rScr hScr hdisj qromUnload uDP).count .TOFF = 0 := by
  dsimp only [genPrepMid18InvDyn]
  simp only [DynamicCircuit.count, Circuit.count_onRegister, bundleSpec.inv_toff, hq,
    countOptCoin9InvDyn_toff, hu]
  rfl
@[simp] theorem countGenPrepMid18InvDyn_t {Var : Type} {sMuxReq tMux : ℕ}
    (bundleSpec : Mux23Circ Var sMuxReq tMux) {N cBits sScr : ℕ} (v : Var)
    (r : QRegister (mMidUB 18 + cBits) N) (rScr : QRegister sScr N) (hScr : sMuxReq ≤ sScr)
    (hdisj : r.DisjointWires rScr) (qromUnload uDP : DynamicCircuit Var N) :
    (genPrepMid18InvDyn bundleSpec v r rScr hScr hdisj qromUnload uDP).count .T =
      14 + tMux + qromUnload.count .T + uDP.count .T := by
  dsimp only [genPrepMid18InvDyn]
  simp only [DynamicCircuit.count, Circuit.count_onRegister,
    show (Circuit.H (0 : Wire 1)).count .T = 0 from rfl, bundleSpec.inv_t, countOptCoin9InvDyn_t]
  omega
theorem cleanUnloadsWpGenPrepMid18InvDyn {Var : Type} [Fintype Var] [DecidableEq Var]
    {sMuxReq tMux : ℕ} {muxBit : Fin (2 ^ 4) → Fin (2 ^ 9) → Bool}
    (bundleSpec : Mux23Bundle Var sMuxReq tMux muxBit)
    {N cBits addrCtx sScr : ℕ} (v : Var) (ctxSub : QRegister addrCtx cBits)
    (F : Fin (2 ^ (5 + addrCtx)) → BitAssignment 14)
    (r : QRegister (mMidUB 18 + cBits) N) (rScr : QRegister sScr N) (hScr : sMuxReq ≤ sScr)
    (hdisj : r.DisjointWires rScr) (uIdx : Unitary (2 ^ 5))
    (W_target : Unitary (2 ^ (mMidUB 18 + cBits))) {qromUnload uDP : DynamicCircuit Var N}
    (hqrom : SelectSwapQROM.CleanUnloadsSet v
      (rScr.image ∪ (r.compose (midGen18AliasOutReg cBits)).image)
      (r.compose (midGen18AliasOutReg cBits)).image
      ((r.compose (midGen18QromReg cBits addrCtx ctxSub)).embedUnitary
        (aliasTableXorUnitary (5 + addrCtx) 14 F)) 1 qromUnload)
    (huDP : Solution.CleanDyn.CleanRealizes v (r.compose (midGen18Idx5Reg cBits)) rScr uIdx⁻¹ uDP)
    (hMuxEq : (midGen18Sig1Reg cBits).embedUnitary (Circuit.H 0).eval *
        ((midGen18MuxSwap23Reg cBits).embedUnitary (pktMuxSwap23Unitary muxBit) *
          ((midGen18QromReg cBits addrCtx ctxSub).embedUnitary
              (aliasTableXorUnitary (5 + addrCtx) 14 F) *
            ((midGen18Pkt4Reg cBits).embedUnitary optCoin9Unitary *
              (midGen18Idx5Reg cBits).embedUnitary uIdx))) = W_target) :
    CleanUnloadsWp v (rScr.image ∪ (r.compose (midGen18AliasOutReg cBits)).image)
      (r.embedUnitary W_target)
      (genPrepMid18InvDyn bundleSpec.toMux23Circ v r rScr hScr hdisj qromUnload uDP) := by
  let rMeas := r.compose (midGen18AliasOutReg cBits)
  let S₀ := rScr.image
  let M_out := rMeas.image
  let S_all := S₀ ∪ M_out
  have hScrMeas : rScr.DisjointWires rMeas := (hdisj.compose_left _).symm
  have hSdiff : S_all \ M_out = S₀ :=
    Finset.union_sdiff_cancel_right (SelectSwapQROM.disjoint_image_of_disjointWires hScrMeas)
  let rSig := r.compose (midGen18Sig1Reg cBits)
  let rMs := r.compose (midGen18MuxSwap23Reg cBits)
  let rQr := r.compose (midGen18QromReg cBits addrCtx ctxSub)
  let rPk := r.compose (midGen18Pkt4Reg cBits)
  let rId := r.compose (midGen18Idx5Reg cBits)
  let W_H := rSig.embedUnitary (Circuit.H 0).eval
  let W_ms := rMs.embedUnitary (pktMuxSwap23Unitary muxBit)
  let W_qrom := rQr.embedUnitary (aliasTableXorUnitary (5 + addrCtx) 14 F)
  let U_pkt := rPk.embedUnitary optCoin9Unitary
  let U_u := rId.embedUnitary uIdx
  have hH := crSet_of
    (Solution.CleanDyn.CleanRealizes.circuit v rSig rScr (hdisj.compose_left _) (Circuit.H 0) rfl)
  have hMs : SelectSwapQROM.CleanRealizesSet v S₀ W_ms⁻¹
      (bundleSpec.invDyn v rMs rScr hScr (hdisj.compose_left _)) := by
    rw [show W_ms⁻¹ = rMs.embedUnitary (pktMuxSwap23Unitary muxBit)⁻¹ from
      (QRegister.embedUnitary_inv _ _).symm]
    exact crSet_of (bundleSpec.inv_cr v rMs rScr hScr (hdisj.compose_left _))
  have hPreCr := hH.seq hMs
  have hWH : W_H⁻¹ = W_H := by
    dsimp only [W_H]
    rw [← QRegister.embedUnitary_inv, ← Circuit.eval_inverse]
    exact congrArg (rSig.embedUnitary ∘ Circuit.eval) rfl
  have hPreInv : W_ms⁻¹ * W_H = (W_H * W_ms)⁻¹ := by simp only [_root_.mul_inv_rev, hWH]
  rw [hPreInv] at hPreCr
  have hPresS₀ {k} (ri : QRegister k (mMidUB 18 + cBits)) (U : Unitary (2 ^ k)) :
      AliasPrep.PreservesWires ((r.compose ri).embedUnitary U).1 S₀ :=
    AliasPrep.preservesWires_embedMatrix_of_disjoint _ _ S₀
      (SelectSwapQROM.disjoint_image_of_disjointWires (hdisj.compose_left _))
  have hOfInvGen (Z : Operator (2 ^ N)) (hZH : Zᴴ = Z)
      {S : Finset (Wire N)} (hZ : SelectSwapQROM.zeroProjOn S = Z)
      {W : Unitary (2 ^ N)} {P : DynamicCircuit Var N}
      (hc : SelectSwapQROM.CleanRealizesSet v S W⁻¹ P) (hComm : W.1 * Z = Z * W.1) :
      SelectSwapQROM.CleanUnloadsSet v S ∅ W 1 P :=
    ⟨hc.1, hc.2.1, fun Θ hΘ ↦ by
      funext σ
      apply Subtype.ext
      apply HermitianMat.ext
      have hUinv : (W⁻¹ : Unitary (2 ^ N)).1 = W.1ᴴ := by simp [Matrix.star_eq_conjTranspose]
      have hv := congrArg (fun x : Observable (Fin (2 ^ N)) ↦ x.1.mat) (congrFun (hc.2.2.1 Θ hΘ) σ)
      simp only [SelectSwapQROM.restrictZeroSet_coe, qcWpQAssign, qcQAssignObsMap, conj_coe,
        conj_apply_mat, coe_star, Matrix.star_eq_conjTranspose, OneMemClass.coe_one,
        conjTranspose_one, one_mul, mul_one, hUinv, conjTranspose_conjTranspose, hZ, hZH] at hv ⊢
      have hWC : Z * W.1ᴴ = W.1ᴴ * Z := by
        simpa only [conjTranspose_mul, hZH] using congrArg (·ᴴ) hComm
      have hU1 : W.1ᴴ * W.1 = 1 := by
        rw [← Matrix.star_eq_conjTranspose]
        exact W.prop.1
      calc Z * (W.1ᴴ * (wp P.compile Θ σ).1.mat * W.1) * Z
          = (Z * W.1ᴴ) * (wp P.compile Θ σ).1.mat * (W.1 * Z) := by simp only [Matrix.mul_assoc]
        _ = (W.1ᴴ * Z) * (wp P.compile Θ σ).1.mat * (Z * W.1) := by rw [hWC, hComm]
        _ = W.1ᴴ * (Z * (wp P.compile Θ σ).1.mat * Z) * W.1 := by simp only [Matrix.mul_assoc]
        _ = W.1ᴴ * (Z * (W.1 * (Θ σ).1.mat * W.1ᴴ) * Z) * W.1 := by rw [hv]
        _ = W.1ᴴ * ((Z * W.1) * (Θ σ).1.mat * (W.1ᴴ * Z)) * W.1 := by simp only [Matrix.mul_assoc]
        _ = W.1ᴴ * ((W.1 * Z) * (Θ σ).1.mat * (Z * W.1ᴴ)) * W.1 := by rw [← hComm, ← hWC]
        _ = (W.1ᴴ * W.1) * (Z * (Θ σ).1.mat * Z) * (W.1ᴴ * W.1) := by simp only [Matrix.mul_assoc]
        _ = Z * (Θ σ).1.mat * Z := by rw [hU1, one_mul, mul_one],
      fun Θ ↦ by simpa only [Finset.sdiff_empty] using hc.2.2.2 Θ⟩
  have hOfInv {S : Finset (Wire N)} {W : Unitary (2 ^ N)} {P : DynamicCircuit Var N}
      (hc : SelectSwapQROM.CleanRealizesSet v S W⁻¹ P)
      (hComm : W.1 * SelectSwapQROM.zeroProjOn S = SelectSwapQROM.zeroProjOn S * W.1) :
      SelectSwapQROM.CleanUnloadsSet v S ∅ W 1 P :=
    hOfInvGen (SelectSwapQROM.zeroProjOn S) (SelectSwapQROM.zeroProjOn_conjTranspose S) rfl
      hc hComm
  have hPrePres := AliasPrep.preservesWires_mul
    (hPresS₀ (midGen18Sig1Reg cBits) (Circuit.H 0).eval)
    (hPresS₀ (midGen18MuxSwap23Reg cBits) (pktMuxSwap23Unitary muxBit))
  have hPreUnload : SelectSwapQROM.CleanUnloadsSet v (S_all \ M_out) ∅ (W_H * W_ms) 1
      (.seq (.circuit ((Circuit.H 0).onRegister rSig))
        (bundleSpec.invDyn v rMs rScr hScr (hdisj.compose_left _))) :=
    hSdiff.symm ▸ hOfInv hPreCr
      (AliasPrep.preservesWires_comm_zeroProjOn hPrePres Finset.Subset.rfl)
  have hPreMid := hPreUnload.seq Finset.subset_union_right hqrom (by
    rw [hSdiff]
    exact AliasPrep.preservesWires_comm_zeroProjOn
      (hPresS₀ (midGen18QromReg cBits addrCtx ctxSub) (aliasTableXorUnitary (5 + addrCtx) 14 F))
      Finset.Subset.rfl)
  rw [Finset.empty_union] at hPreMid
  let rScrOut := rScr.concat rMeas hScrMeas
  have hScrOutImg : rScrOut.image = S_all := QRegister.image_concat rScr rMeas hScrMeas
  have hPktDisj : rPk.DisjointWires rScrOut :=
    QRegister.disjointWires_concat_right hScrMeas (hdisj.compose_left _)
      (QRegister.disjoint_iff.mpr fun _ j hij ↦ by
        have hv := congrArg Fin.val (r.wires.injective hij)
        simp only [midGen18Pkt4Reg, midGen18AliasOutReg, midGen18MidReg, mid18Core23Reg,
          core23PktReg, mid18AliasOutReg, QRegister.compose_apply, QRegister.block_apply_val] at hv
        have := j.isLt
        omega)
  have hIdxDisj : rId.DisjointWires rScrOut :=
    QRegister.disjointWires_concat_right hScrMeas (hdisj.compose_left _)
      (QRegister.disjoint_iff.mpr fun i _ hij ↦ by
        have hv := congrArg Fin.val (r.wires.injective hij)
        simp only [midGen18Idx5Reg, midGen18AliasOutReg, midGen18MidReg, mid18Core23Reg,
          core23IdxReg, mid18AliasOutReg, QRegister.compose_apply, QRegister.block_apply_val] at hv
        have := i.isLt
        omega)
  have hPktSet : SelectSwapQROM.CleanRealizesSet v S_all U_pkt⁻¹ (optCoin9InvDyn rPk) := by
    rw [← hScrOutImg, ← QRegister.embedUnitary_inv]
    exact crSet_of (Solution.CleanDyn.CleanRealizes.extend_scr hPktDisj
      (by
          rw [hScrOutImg]
          exact Finset.subset_union_left)
      (cleanRealizesOptCoin9InvDyn v rPk rScr (hdisj.compose_left _)))
  have hIdxSet : SelectSwapQROM.CleanRealizesSet v S_all U_u⁻¹ uDP := by
    rw [← hScrOutImg, ← QRegister.embedUnitary_inv]
    exact crSet_of (Solution.CleanDyn.CleanRealizes.extend_scr hIdxDisj
      (by
          rw [hScrOutImg]
          exact Finset.subset_union_left) huDP)
  have hPostCr := hPktSet.seq hIdxSet
  rw [← _root_.mul_inv_rev] at hPostCr
  have hPostPres : AliasPrep.PreservesWires (U_pkt * U_u).1 S_all := by
    rw [← hScrOutImg]
    exact AliasPrep.preservesWires_mul
      (AliasPrep.preservesWires_embedMatrix_of_disjoint rPk _ _
        (SelectSwapQROM.disjoint_image_of_disjointWires hPktDisj))
      (AliasPrep.preservesWires_embedMatrix_of_disjoint rId _ _
        (SelectSwapQROM.disjoint_image_of_disjointWires hIdxDisj))
  have hPostUnload : SelectSwapQROM.CleanUnloadsSet v S_all ∅ (U_pkt * U_u) 1
      (.seq (optCoin9InvDyn rPk) uDP) :=
    hOfInv hPostCr (AliasPrep.preservesWires_comm_zeroProjOn hPostPres Finset.Subset.rfl)
  rw [← Finset.sdiff_empty (s := rScr.image ∪ (r.compose (midGen18AliasOutReg cBits)).image)]
    at hPreMid
  have hAll := hPreMid.seq (Finset.empty_subset S_all) hPostUnload
    (AliasPrep.preservesWires_comm_zeroProjOn hPostPres Finset.sdiff_subset)
  rw [Finset.union_empty] at hAll
  have hUnitEq : ((W_H * W_ms) * W_qrom) * (U_pkt * U_u) = r.embedUnitary W_target := by
    rw [← hMuxEq]
    simp only [W_H, W_ms, W_qrom, U_pkt, U_u, rSig, rMs, rQr, rPk, rId,
      QRegister.embedUnitary_mul, QRegister.embedUnitary_compose, mul_assoc]
  rw [hUnitEq] at hAll
  obtain ⟨_, hUpd, hRestr⟩ := CleanUnloadsWp.of_cleanUnloadsSet hAll
  have hSeqWp (A B : DynamicCircuit Var N) (Ψ : QCAssertion Var (2 ^ N)) :
      wp (A.seq B).compile Ψ = wp A.compile (wp B.compile Ψ) := by
    rw [DynamicCircuit.compile_seq, wp_qSeq]
  have hEq (Φ : QCAssertion Var (2 ^ N)) :
      wp (genPrepMid18InvDyn bundleSpec.toMux23Circ v r rScr hScr hdisj qromUnload uDP).compile Φ =
        wp (DynamicCircuit.seq (DynamicCircuit.seq (DynamicCircuit.seq
            (.circuit ((Circuit.H 0).onRegister rSig))
            (bundleSpec.invDyn v rMs rScr hScr (hdisj.compose_left _))) qromUnload)
          (DynamicCircuit.seq (optCoin9InvDyn rPk) uDP)).compile Φ := by
    trans wp (DynamicCircuit.circuit ((Circuit.H 0).onRegister rSig)).compile
      (wp (bundleSpec.invDyn v rMs rScr hScr (hdisj.compose_left _)).compile
        (wp qromUnload.compile (wp (optCoin9InvDyn rPk).compile (wp uDP.compile Φ))))
    · unfold genPrepMid18InvDyn
      rw [hSeqWp, hSeqWp, hSeqWp, hSeqWp]
    · symm
      rw [hSeqWp, hSeqWp, hSeqWp, hSeqWp]
  refine ⟨countGenPrepMid18InvDyn_toff bundleSpec.toMux23Circ v r rScr hScr hdisj hqrom.1 huDP.1,
    fun Θ hΘ σ val ↦ by
      rw [hEq]
      exact hUpd Θ hΘ σ val,
    fun Θ hΘ ↦ by
      rw [hEq]
      exact hRestr Θ hΘ⟩
theorem genPrepMid18InvDyn_wp_split {Var : Type} [DecidableEq Var]
    {sMuxReq tMux : ℕ} (bundleSpec : Mux23Circ Var sMuxReq tMux)
    {N cBits sScr : ℕ} (v : Var) (r : QRegister (mMidUB 18 + cBits) N)
    (rScr : QRegister sScr N) (hScr : sMuxReq ≤ sScr) (hdisj : r.DisjointWires rScr)
    (qromUnload uDP : DynamicCircuit Var N) (Θ : QCAssertion Var (2 ^ N)) :
    wp (genPrepMid18InvDyn bundleSpec v r rScr hScr hdisj qromUnload uDP).compile Θ =
      wp (DynamicCircuit.seq
          (.circuit ((Circuit.H 0).onRegister (r.compose (midGen18Sig1Reg cBits))))
          (bundleSpec.invDyn v (r.compose (midGen18MuxSwap23Reg cBits)) rScr hScr
            (hdisj.compose_left _))).compile
        (wp qromUnload.compile
          (wp (DynamicCircuit.seq (optCoin9InvDyn (r.compose (midGen18Pkt4Reg cBits)))
            uDP).compile Θ)) := by
  have hSeqWp (A B : DynamicCircuit Var N) (Ψ : QCAssertion Var (2 ^ N)) :
      wp (A.seq B).compile Ψ = wp A.compile (wp B.compile Ψ) := by
    rw [DynamicCircuit.compile_seq, wp_qSeq]
  unfold genPrepMid18InvDyn
  rw [hSeqWp, hSeqWp, hSeqWp, ← hSeqWp]
attribute [irreducible] genPrepMid18InvDyn
/-! ## Section 3: `46-T` Hadamard `W`-State `Mux23Circ`/`Mux23Bundle` & `w = 3` `PREP_mid†` -/

theorem pktMuxSwap23UnitaryMux9AltBit_eq :
    pktMuxSwap23Unitary mux9AltBit = pktMuxSwapAlt23Unitary := by
  rw [pktMuxSwap23Unitary_eq_bitPermUnitary]
  rfl
/-- Computable `{Var : Type}` `46-T` (`16`-ancilla, `0 TOFF`) Hadamard-target `W`-state
`Mux23Circ` for `mux9AltBit`. -/
def hadWMux23Circ (Var : Type) : Mux23Circ Var 16 46 where
  fwdDyn v rAct rScr hs _ := hadWMuxSwap23Dyn v rAct rScr hs
  invDyn v rAct rScr hs _ := hadWMuxSwap23Dyn v rAct rScr hs
  fwd_toff v rAct rScr hs _ := countHadWMuxSwap23Dyn_toff v rAct rScr hs
  inv_toff v rAct rScr hs _ := countHadWMuxSwap23Dyn_toff v rAct rScr hs
  fwd_t v rAct rScr hs hdisj := countHadWMuxSwap23Dyn_t v rAct rScr hs hdisj
  inv_t v rAct rScr hs hdisj := countHadWMuxSwap23Dyn_t v rAct rScr hs hdisj
/-- `46-T` (`16`-ancilla, `0 TOFF`) Hadamard-target `W`-state `Mux23Bundle` for `mux9AltBit`. -/
def hadWMux23Bundle (Var : Type) :
    Mux23Bundle Var 16 46 mux9AltBit where
  toMux23Circ := hadWMux23Circ Var
  fwd_cr v rAct rScr hs hdisj := by
    rw [pktMuxSwap23UnitaryMux9AltBit_eq]
    exact cleanRealizesHadWMuxSwap23Dyn v rAct rScr hs hdisj
  inv_cr v rAct rScr hs hdisj := by
    rw [pktMuxSwap23UnitaryMux9AltBit_eq]
    exact cleanRealizesHadWMuxSwap23Dyn_inv v rAct rScr hs hdisj
/-- `π128`-permuted `128 × 32 × 14` Boolean table for `44-T` `w = 3` turnaround unloads. -/
def keep9Pi128Hot14Bool (π128 : Equiv.Perm (Fin 128)) (c : Fin 128) :
    Fin (2 ^ 5) → Fin 14 → Bool :=
  keep9Hot24BoolTable (π128 c)
theorem hotLinearKeep9Pi128_oneHot (π128 : Equiv.Perm (Fin 128)) :
    HotTableSpec14 (hotLinearTargetFn 5 128 14 (keep9Pi128Hot14Bool π128))
      (genPi128SliceFn14 keep9SliceTargetFn14 π128) :=
  fun rc cHot hc x ↦ hotLinearTargetFn_combineAddr_oneHot (keep9Pi128Hot14Bool π128) x rc cHot hc
/-- `58 + tMux + uDP.count .T` `T` (`0 TOFF`, `sMuxReq ≤ sScr`) `w = 3` one-hot `X`-measurement
`PREP_mid†` inside `withHot128Dyn`. -/
def prepMid18DagW3Pi128Dyn {Var : Type} {sMuxReq tMux : ℕ}
    (bundleSpec : Mux23Circ Var sMuxReq tMux) (π128 : Equiv.Perm (Fin 128))
    {N sScr : ℕ} (v : Var) (r : QRegister (mMidUB 18 + (7 + 128)) N)
    (rScr : QRegister sScr N) (hScr : sMuxReq ≤ sScr) (hdisj : r.DisjointWires rScr)
    (uDP : DynamicCircuit Var N) : DynamicCircuit Var N :=
  genPrepMid18InvDyn bundleSpec v r rScr hScr hdisj
    (qromXMeasW3FromHotCtxAliasUnloadDyn (L_ctx := 128) (b := 9) (payBits := 0) v
      (keep9Pi128Hot14Bool π128) (r.compose mid159ToAlias157) rScr
      (by
          dsimp [CoherentAlias.aliasOutBits]
          omega) (hdisj.compose_left _)) uDP
@[simp] theorem countPrepMid18DagW3Pi128Dyn_toff {Var : Type} {sMuxReq tMux : ℕ}
    (bundleSpec : Mux23Circ Var sMuxReq tMux) (π128 : Equiv.Perm (Fin 128))
    {N sScr : ℕ} (v : Var) (r : QRegister (mMidUB 18 + (7 + 128)) N)
    (rScr : QRegister sScr N) (hScr : sMuxReq ≤ sScr) (hdisj : r.DisjointWires rScr)
    {uDP : DynamicCircuit Var N} (hu : uDP.count .TOFF = 0) :
    (prepMid18DagW3Pi128Dyn bundleSpec π128 v r rScr hScr hdisj uDP).count .TOFF = 0 :=
  countGenPrepMid18InvDyn_toff bundleSpec v r rScr hScr hdisj
    (count_qromXMeasW3FromHotCtxAliasUnloadDyn_toff (L_ctx := 128) (b := 9) (payBits := 0) ..) hu
@[simp] theorem countPrepMid18DagW3Pi128Dyn_t {Var : Type} {sMuxReq tMux : ℕ}
    (bundleSpec : Mux23Circ Var sMuxReq tMux) (π128 : Equiv.Perm (Fin 128))
    {N sScr : ℕ} (v : Var) (r : QRegister (mMidUB 18 + (7 + 128)) N)
    (rScr : QRegister sScr N) (hScr : sMuxReq ≤ sScr) (hdisj : r.DisjointWires rScr)
    (uDP : DynamicCircuit Var N) :
    (prepMid18DagW3Pi128Dyn bundleSpec π128 v r rScr hScr hdisj uDP).count .T =
      58 + tMux + uDP.count .T := by
  dsimp only [prepMid18DagW3Pi128Dyn]
  rw [countGenPrepMid18InvDyn_t, count_qromXMeasW3FromHotCtxAliasUnloadDyn_t]
  omega
theorem wpQAssign_conj {Var : Type} [Fintype Var] {N : ℕ}
    (U : Unitary (2 ^ N)) (Ψ : QCAssertion Var (2 ^ N)) (σ : Store Var)
    (Q : Operator (2 ^ N)) :
    ((qcWpQAssign U Ψ σ).1).conj Q = ((Ψ σ).1).conj (Q * U.1ᴴ) := by
  simp only [qcWpQAssign, qcQAssignObsMap, conj_coe, coe_star, Matrix.star_eq_conjTranspose,
    conj_conj]
theorem cleanUnloadConj {Var : Type} [Fintype Var] [DecidableEq Var] {N : ℕ} {v : Var}
    {Q : Operator (2 ^ N)} {U : Unitary (2 ^ N)} {P : DynamicCircuit Var N} (hQ : Qᴴ = Q)
    (h : CleanPredRealizes v Q U⁻¹ P) (Θ : QCAssertion Var (2 ^ N))
    (hΘ : ∀ σ val, Θ (Function.update σ v val) = Θ σ) (σ : Store Var) :
    ((wp P.compile Θ σ).1).conj (Q * U.1ᴴ) = ((Θ σ).1).conj Q := by
  have hUinvH : (U⁻¹ : Unitary (2 ^ N)).1ᴴ = U.1 := by
    change (star U : Unitary (2 ^ N)).1ᴴ = U.1
    rw [coe_star, Matrix.star_eq_conjTranspose, conjTranspose_conjTranspose]
  have hComm : Q * U.1 = U.1 * Q := by
    have hp : Q * (U⁻¹).1ᴴ = (U⁻¹).1ᴴ * Q := h.2.1
    rwa [hUinvH] at hp
  have hCommH : U.1ᴴ * Q = Q * U.1ᴴ := by
    simpa only [conjTranspose_mul, hQ] using congrArg (·ᴴ) hComm
  have hv := congrArg (fun M : HermitianMat (Fin (2 ^ N)) ℂ ↦ M.conj U.1ᴴ) (h.2.2.2 Θ hΘ σ)
  rw [wpQAssign_conj, hUinvH, conj_conj, conj_conj, hCommH] at hv
  have hCancel : U.1ᴴ * (Q * U.1) = Q := by
    rw [hComm, ← Matrix.mul_assoc, ← Matrix.star_eq_conjTranspose, U.prop.1, one_mul]
  rwa [hCancel] at hv
theorem predProj_xoOneHot_mul_cleanPredProj_oneHot {N : ℕ} (S_all : Finset (Wire N))
    (rXo : QRegister 7 N) (rHot : QRegister 128 N) :
    predProj (xoOneHotPred rXo rHot) *
        Mobius126OneHot.cleanPredProj S_all (oneHotPred rHot) =
      Mobius126OneHot.cleanPredProj S_all (xoOneHotPred rXo rHot) := by
  apply SelectSwapQROM.matrix_ext_ket
  intro β
  rw [← predProj_mul_zeroProjOn_eq_cleanPredProj, ← predProj_mul_zeroProjOn_eq_cleanPredProj,
    ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    SelectSwapQROM.zeroProjOn_mulVec_ket]
  by_cases hz : ∀ w ∈ S_all, β w = 0
  · rw [ite_eq_left hz, StepOuter8Pi145Outer.predProj_mulVec_ket,
      StepOuter8Pi145Outer.predProj_mulVec_ket]
    by_cases hx : xoOneHotPred rXo rHot β = true
    · rw [ite_eq_left (xoOneHotPred_implies_oneHotPred rXo rHot β hx), ite_eq_left hx,
        StepOuter8Pi145Outer.predProj_mulVec_ket, ite_eq_left hx]
    · rw [ite_eq_right hx]
      by_cases hh : oneHotPred rHot β = true
      · rw [ite_eq_left hh, StepOuter8Pi145Outer.predProj_mulVec_ket, ite_eq_right hx]
      · rw [ite_eq_right hh, Matrix.mulVec_zero]
  · rw [ite_eq_right hz, Matrix.mulVec_zero, Matrix.mulVec_zero]
theorem wp_qromW3Keep9Pi128_conj_xoOneHot {Var : Type} [Finite Var] [DecidableEq Var]
    {N sScr : ℕ} (π128 : Equiv.Perm (Fin 128)) (v : Var)
    (r : QRegister (mMidUB 18 + (7 + 128)) N) (rScr : QRegister sScr N)
    (hdisj : r.DisjointWires rScr) (Ψ : QCAssertion Var (2 ^ N))
    (hΨ : ∀ σ' b, Ψ (Function.update σ' v b) = Ψ σ') (σ : Store Var) :
    let F_lin := hotLinearTargetFn 5 128 14 (keep9Pi128Hot14Bool π128)
    let W_qrom := (r.compose mid159QroReg).embedUnitary
      (aliasTableXorUnitary (5 + 128) 14 F_lin)
    let Q_all := Mobius126OneHot.cleanPredProj
      (rScr.image ∪ (r.compose mid159AliasOutReg).image)
      (xoOneHotPred (r.compose mid159Xo7Reg) (r.compose mid159Hot128Reg))
    ((wp (qromXMeasW3FromHotCtxAliasUnloadDyn (L_ctx := 128) (b := 9) (payBits := 0) v
        (keep9Pi128Hot14Bool π128) (r.compose mid159ToAlias157) rScr
        (by
            dsimp [CoherentAlias.aliasOutBits]
            omega) (hdisj.compose_left _)).compile Ψ σ).1).conj (Q_all * W_qrom.1ᴴ) =
      ((Ψ σ).1).conj Q_all := by
  cases nonempty_fintype Var
  intro F_lin W_qrom Q_all
  have hRaw := wp_qromXMeasW3FromHotCtxAliasUnloadDyn_oneHot (L_ctx := 128) (b := 9)
    (payBits := 0) v (keep9Pi128Hot14Bool π128)
    (fun c k ↦ anfCoeffsKeep9Hot24BoolTable_30 (π128 c) k)
    (fun c k ↦ anfCoeffsKeep9Hot24BoolTable_31 (π128 c) k)
    (r.compose mid159ToAlias157) rScr
    (by
        dsimp [CoherentAlias.aliasOutBits]
        omega) (hdisj.compose_left _) Ψ hΨ σ
  have eQ : (r.compose mid159ToAlias157).compose (CoherentAlias.aliasQromReg 5 128 9 0) =
      r.compose mid159QroReg :=
    (CoherentAlias.qreg_ext fun _ ↦ rfl).trans
      (congrArg r.compose mid159ToAlias157_compose_qrom)
  have eO : (r.compose mid159ToAlias157).compose (AliasPrep.aliasOutReg 5 128 9 0) =
      r.compose mid159AliasOutReg :=
    (CoherentAlias.qreg_ext fun _ ↦ rfl).trans
      (congrArg r.compose mid159ToAlias157_compose_out)
  have eC : (r.compose mid159ToAlias157).compose (CoherentAlias.aliasCtxReg 5 128 9 0) =
      r.compose mid159Hot128Reg :=
    (CoherentAlias.qreg_ext fun _ ↦ rfl).trans
      (congrArg r.compose mid159ToAlias157_compose_ctx)
  dsimp only at hRaw
  rw [eQ, eO, eC] at hRaw
  change ((qcWpQAssign W_qrom _ σ).1).conj
    (Mobius126OneHot.cleanPredProj (rScr.image ∪ (r.compose mid159AliasOutReg).image)
      (oneHotPred (r.compose mid159Hot128Reg))) = _ at hRaw
  have hc := congrArg (fun M : HermitianMat (Fin (2 ^ N)) ℂ ↦
    M.conj (predProj (xoOneHotPred (r.compose mid159Xo7Reg) (r.compose mid159Hot128Reg)))) hRaw
  rw [conj_conj, conj_conj, predProj_xoOneHot_mul_cleanPredProj_oneHot, wpQAssign_conj] at hc
  exact hc
theorem conj_unload3_xoOneHot {Var : Type} [Fintype Var] [DecidableEq Var] {N : ℕ} {v : Var}
    {Q₀ Q_all : Operator (2 ^ N)} (hQ0H : Q₀ᴴ = Q₀) (hQaH : Q_allᴴ = Q_all)
    (hQQ : Q₀ * Q_all = Q_all) {U_pre W_qrom U_post W_1 : Unitary (2 ^ N)}
    (hW1Eq : W_1 = U_pre * W_qrom * U_post) (hQrQ0 : Q₀ * W_qrom.1 = W_qrom.1 * Q₀)
    {cPre qromW3 cPost : DynamicCircuit Var N}
    (hPre : CleanPredRealizes v Q₀ U_pre⁻¹ cPre)
    (hPost : CleanPredRealizes v Q_all U_post⁻¹ cPost)
    (Θ : QCAssertion Var (2 ^ N)) (hΘ : ∀ σ val, Θ (Function.update σ v val) = Θ σ)
    (hQrUpd : ∀ σ' b, wp qromW3.compile (wp cPost.compile Θ) (Function.update σ' v b) =
      wp qromW3.compile (wp cPost.compile Θ) σ')
    (σ : Store Var)
    (hConjQr : ((wp qromW3.compile (wp cPost.compile Θ) σ).1).conj (Q_all * W_qrom.1ᴴ) =
      ((wp cPost.compile Θ σ).1).conj Q_all) :
    ((qcWpQAssign W_1 (wp cPre.compile (wp qromW3.compile (wp cPost.compile Θ))) σ).1).conj Q_all =
      ((Θ σ).1).conj Q_all := by
  have hInvH : (U_post⁻¹ : Unitary (2 ^ N)).1ᴴ = U_post.1 := by
    change (star U_post : Unitary (2 ^ N)).1ᴴ = U_post.1
    rw [coe_star, star_eq_conjTranspose, conjTranspose_conjTranspose]
  have hPostComm : Q_all * U_post.1 = U_post.1 * Q_all := by
    have hp : Q_all * (U_post⁻¹).1ᴴ = (U_post⁻¹).1ᴴ * Q_all := hPost.2.1
    rwa [hInvH] at hp
  have hPostCommH : U_post.1ᴴ * Q_all = Q_all * U_post.1ᴴ := by
    have h := congrArg Matrix.conjTranspose hPostComm
    rwa [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hQaH] at h
  have hQrQ0H : W_qrom.1ᴴ * Q₀ = Q₀ * W_qrom.1ᴴ := by
    have h := congrArg Matrix.conjTranspose hQrQ0
    rwa [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hQ0H] at h
  have hQQ' : Q_all * Q₀ = Q_all := by
    have h := congrArg Matrix.conjTranspose hQQ
    rwa [Matrix.conjTranspose_mul, hQ0H, hQaH] at h
  have hAbsQ0 : (Q_all * W_qrom.1ᴴ) * Q₀ = Q_all * W_qrom.1ᴴ := by
    rw [Matrix.mul_assoc, hQrQ0H, ← Matrix.mul_assoc, hQQ']
  have hW1H : W_1.1ᴴ = U_post.1ᴴ * (W_qrom.1ᴴ * U_pre.1ᴴ) := by
    rw [hW1Eq, Submonoid.coe_mul, Submonoid.coe_mul, conjTranspose_mul, conjTranspose_mul]
  let X := U_post.1ᴴ * (Q_all * W_qrom.1ᴴ)
  have hAbs2 : X * Q₀ = X := by
    dsimp only [X]
    rw [Matrix.mul_assoc, hAbsQ0]
  have hXeq : Q_all * W_1.1ᴴ = X * (Q₀ * U_pre.1ᴴ) :=
    calc Q_all * W_1.1ᴴ
        = (Q_all * U_post.1ᴴ) * (W_qrom.1ᴴ * U_pre.1ᴴ) := by rw [hW1H, ← Matrix.mul_assoc]
      _ = X * U_pre.1ᴴ := by
            dsimp only [X]
            rw [← hPostCommH, Matrix.mul_assoc, ← Matrix.mul_assoc Q_all,
              ← Matrix.mul_assoc U_post.1ᴴ]
      _ = (X * Q₀) * U_pre.1ᴴ := by rw [hAbs2]
      _ = X * (Q₀ * U_pre.1ᴴ) := by rw [Matrix.mul_assoc]
  rw [wpQAssign_conj, hXeq, ← conj_conj, cleanUnloadConj hQ0H hPre _ hQrUpd σ,
    conj_conj, hAbs2]
  dsimp only [X]
  rw [← conj_conj, hConjQr, conj_conj, hPostCommH]
  exact cleanUnloadConj hQaH hPost Θ hΘ σ
theorem cleanMid159_pre {Var : Type} [Fintype Var] [DecidableEq Var]
    {sMuxReq tMux : ℕ} {muxBit : Fin (2 ^ 4) → Fin (2 ^ 9) → Bool}
    (bundleSpec : Mux23Bundle Var sMuxReq tMux muxBit)
    {N sScr : ℕ} (v : Var) (r : QRegister (mMidUB 18 + (7 + 128)) N)
    (rScr : QRegister sScr N) (hScr : sMuxReq ≤ sScr) (hdisj : r.DisjointWires rScr) :
    CleanPredRealizes v
      (Mobius126OneHot.cleanPredProj rScr.image
        (xoOneHotPred (r.compose mid159Xo7Reg) (r.compose mid159Hot128Reg)))
      ((r.compose (midGen18Sig1Reg (7 + 128))).embedUnitary (Circuit.H 0).eval *
        (r.compose (midGen18MuxSwap23Reg (7 + 128))).embedUnitary
          (pktMuxSwap23Unitary muxBit))⁻¹
      (.seq (.circuit ((Circuit.H 0).onRegister (r.compose (midGen18Sig1Reg (7 + 128)))))
        (bundleSpec.toMux23Circ.invDyn v (r.compose (midGen18MuxSwap23Reg (7 + 128))) rScr hScr
          (hdisj.compose_left _))) := by
  have hHotIn : ∀ c : Fin 128, ∃ c' : Fin 128,
      (r.compose mid159Hot128Reg) c = (r.compose mid159Hot128Reg) c' := fun c ↦ ⟨c, rfl⟩
  have hdSig := midSub18_disjoint_xo_hot r (r.compose mid159Hot128Reg) hHotIn (rSigInLoc 18)
  have hdMs := midSub18_disjoint_xo_hot r (r.compose mid159Hot128Reg) hHotIn
    (mid18Core23Reg.compose Inner18Symp14Walk.core23MuxSwap23Reg)
  have hH := CleanPredRealizes.of_cleanRealizes_xoOneHot
    (rSub := r.compose (midGen18Sig1Reg (7 + 128)))
    (hdisj.compose_left _) hdSig.1 hdSig.2
    (Solution.CleanDyn.CleanRealizes.circuit v (r.compose (midGen18Sig1Reg (7 + 128))) rScr
      (hdisj.compose_left _) (Circuit.H 0) rfl)
  have hMs := CleanPredRealizes.of_cleanRealizes_xoOneHot
    (rSub := r.compose (midGen18MuxSwap23Reg (7 + 128)))
    (hdisj.compose_left _) hdMs.1 hdMs.2
    (bundleSpec.inv_cr v (r.compose (midGen18MuxSwap23Reg (7 +
      128))) rScr hScr (hdisj.compose_left _))
  have hWH : ((r.compose (midGen18Sig1Reg (7 + 128))).embedUnitary (Circuit.H 0).eval)⁻¹ =
      (r.compose (midGen18Sig1Reg (7 + 128))).embedUnitary (Circuit.H 0).eval := by
    rw [← QRegister.embedUnitary_inv, ← Circuit.eval_inverse]
    exact congrArg ((r.compose (midGen18Sig1Reg (7 + 128))).embedUnitary ∘ Circuit.eval) rfl
  have hs := hH.seq hMs
  rw [QRegister.embedUnitary_inv] at hs
  rwa [_root_.mul_inv_rev, hWH]
theorem cleanMid159_post {Var : Type} [Fintype Var] [DecidableEq Var]
    {N sScr : ℕ} (v : Var) (r : QRegister (mMidUB 18 + (7 + 128)) N)
    (rScr : QRegister sScr N) (hdisj : r.DisjointWires rScr)
    (uIdx : Unitary (2 ^ 5)) {uDP : DynamicCircuit Var N}
    (huDP : Solution.CleanDyn.CleanRealizes v (r.compose mid159Idx5Reg) rScr uIdx⁻¹ uDP) :
    CleanPredRealizes v
      (Mobius126OneHot.cleanPredProj (rScr.image ∪ (r.compose mid159AliasOutReg).image)
        (xoOneHotPred (r.compose mid159Xo7Reg) (r.compose mid159Hot128Reg)))
      ((r.compose (midGen18Pkt4Reg (7 + 128))).embedUnitary optCoin9Unitary *
        (r.compose mid159Idx5Reg).embedUnitary uIdx)⁻¹
      (.seq (optCoin9InvDyn (r.compose (midGen18Pkt4Reg (7 + 128)))) uDP) := by
  have hHotIn : ∀ c : Fin 128, ∃ c' : Fin 128,
      (r.compose mid159Hot128Reg) c = (r.compose mid159Hot128Reg) c' := fun c ↦ ⟨c, rfl⟩
  have hdPkt := midSub18_disjoint_xo_hot r (r.compose mid159Hot128Reg) hHotIn
    (mid18Core23Reg.compose core23PktReg)
  have hdIdx := midSub18_disjoint_xo_hot r (r.compose mid159Hot128Reg) hHotIn
    (mid18Core23Reg.compose core23IdxReg)
  have hScrMeas : rScr.DisjointWires (r.compose mid159AliasOutReg) :=
    QRegister.disjoint_comm.mp (hdisj.compose_left _)
  have hScrOutImg : (rScr.concat (r.compose mid159AliasOutReg) hScrMeas).image =
      rScr.image ∪ (r.compose mid159AliasOutReg).image :=
    QRegister.image_concat rScr (r.compose mid159AliasOutReg) hScrMeas
  have hPkDisj : (r.compose (midGen18Pkt4Reg (7 + 128))).DisjointWires
      (rScr.concat (r.compose mid159AliasOutReg) hScrMeas) :=
    disjointWires_concat_right hScrMeas (hdisj.compose_left _)
      (QRegister.disjoint_iff.mpr fun _ j hij ↦ by
        have hv := congrArg Fin.val (r.wires.injective hij)
        simp only [midGen18Pkt4Reg, mid159AliasOutReg, midGen18AliasOutReg, midGen18MidReg,
          mid18Core23Reg, core23PktReg, mid18AliasOutReg, QRegister.compose_apply,
          QRegister.block_apply_val] at hv
        have := j.isLt
        omega)
  have hIdDisj : (r.compose mid159Idx5Reg).DisjointWires
      (rScr.concat (r.compose mid159AliasOutReg) hScrMeas) :=
    disjointWires_concat_right hScrMeas (hdisj.compose_left _)
      (QRegister.disjoint_iff.mpr fun i _ hij ↦ by
        have hv := congrArg Fin.val (r.wires.injective hij)
        simp only [mid159Idx5Reg, midGen18Idx5Reg, mid159AliasOutReg, midGen18AliasOutReg,
          midGen18MidReg, mid18Core23Reg, core23IdxReg, mid18AliasOutReg,
          QRegister.compose_apply, QRegister.block_apply_val] at hv
        have := i.isLt
        omega)
  have h1 := CleanPredRealizes.of_cleanRealizes_xoOneHot hPkDisj hdPkt.1 hdPkt.2
    (Solution.CleanDyn.CleanRealizes.extend_scr hPkDisj
      (by
          rw [hScrOutImg]
          exact Finset.subset_union_left)
      (cleanRealizesOptCoin9InvDyn v (r.compose (midGen18Pkt4Reg (7 + 128))) rScr
        (hdisj.compose_left _)))
  have h2 := CleanPredRealizes.of_cleanRealizes_xoOneHot hIdDisj hdIdx.1 hdIdx.2
    (Solution.CleanDyn.CleanRealizes.extend_scr hIdDisj
      (by
          rw [hScrOutImg]
          exact Finset.subset_union_left) huDP)
  have hs := h1.seq h2
  rw [hScrOutImg, QRegister.embedUnitary_inv, QRegister.embedUnitary_inv, ← _root_.mul_inv_rev]
    at hs
  exact hs
theorem wpGenPrepMid18InvDyn_xoOneHot_aux {Var : Type} [Fintype Var] [DecidableEq Var]
    {sMuxReq tMux : ℕ} {muxBit : Fin (2 ^ 4) → Fin (2 ^ 9) → Bool}
    (bundleSpec : Mux23Bundle Var sMuxReq tMux muxBit)
    {N sScr : ℕ} (v : Var) (r : QRegister (mMidUB 18 + (7 + 128)) N)
    (rScr : QRegister sScr N) (hScr : sMuxReq ≤ sScr) (hdisj : r.DisjointWires rScr)
    (uIdx : Unitary (2 ^ 5)) {uDP : DynamicCircuit Var N}
    (huDP : Solution.CleanDyn.CleanRealizes v (r.compose mid159Idx5Reg) rScr uIdx⁻¹ uDP)
    (F : Fin (2 ^ (5 + 128)) → BitAssignment 14) (qromUnload : DynamicCircuit Var N)
    (hQrUpd : ∀ Ψ : QCAssertion Var (2 ^ N), (∀ σ' b, Ψ (Function.update σ' v b) = Ψ σ') →
      ∀ σ' b, wp qromUnload.compile Ψ (Function.update σ' v b) = wp qromUnload.compile Ψ σ')
    (hQrConj : ∀ Ψ : QCAssertion Var (2 ^ N), (∀ σ' b, Ψ (Function.update σ' v b) = Ψ σ') →
      ∀ σ : Store Var,
        ((wp qromUnload.compile Ψ σ).1).conj
          (Mobius126OneHot.cleanPredProj (rScr.image ∪ (r.compose mid159AliasOutReg).image)
            (xoOneHotPred (r.compose mid159Xo7Reg) (r.compose mid159Hot128Reg)) *
            ((r.compose mid159QroReg).embedUnitary
              (aliasTableXorUnitary (5 + 128) 14 F)).1ᴴ) =
        ((Ψ σ).1).conj
          (Mobius126OneHot.cleanPredProj (rScr.image ∪ (r.compose mid159AliasOutReg).image)
            (xoOneHotPred (r.compose mid159Xo7Reg) (r.compose mid159Hot128Reg)))) :
    (∀ Θ : QCAssertion Var (2 ^ N), (∀ σ val, Θ (Function.update σ v val) = Θ σ) →
      ∀ σ val,
        wp (genPrepMid18InvDyn bundleSpec.toMux23Circ v r rScr hScr hdisj qromUnload uDP).compile
          Θ (Function.update σ v val) =
        wp (genPrepMid18InvDyn bundleSpec.toMux23Circ v r rScr hScr hdisj qromUnload uDP).compile
          Θ σ) ∧
    (∀ Θ : QCAssertion Var (2 ^ N), (∀ σ val, Θ (Function.update σ v val) = Θ σ) →
      ∀ σ : Store Var,
        ((qcWpQAssign
          (r.embedUnitary (muxOnAct (mMidUB 18) (7 + 128) (hotBranch18Of muxBit uIdx F)))
          (wp (genPrepMid18InvDyn bundleSpec.toMux23Circ v r rScr hScr hdisj qromUnload uDP).compile
            Θ)
          σ).1).conj
          (Mobius126OneHot.cleanPredProj (rScr.image ∪ (r.compose mid159AliasOutReg).image)
            (xoOneHotPred (r.compose mid159Xo7Reg) (r.compose mid159Hot128Reg))) =
        ((Θ σ).1).conj
          (Mobius126OneHot.cleanPredProj (rScr.image ∪ (r.compose mid159AliasOutReg).image)
            (xoOneHotPred (r.compose mid159Xo7Reg) (r.compose mid159Hot128Reg)))) := by
  have hPre := cleanMid159_pre bundleSpec v r rScr hScr hdisj
  have hPost := cleanMid159_post v r rScr hdisj uIdx huDP
  have hW1Eq : r.embedUnitary (muxOnAct (mMidUB 18) (7 + 128) (hotBranch18Of muxBit uIdx F)) =
      ((r.compose (midGen18Sig1Reg (7 + 128))).embedUnitary (Circuit.H 0).eval *
        (r.compose (midGen18MuxSwap23Reg (7 + 128))).embedUnitary (pktMuxSwap23Unitary muxBit)) *
      (r.compose mid159QroReg).embedUnitary (aliasTableXorUnitary (5 + 128) 14 F) *
      ((r.compose (midGen18Pkt4Reg (7 + 128))).embedUnitary optCoin9Unitary *
        (r.compose mid159Idx5Reg).embedUnitary uIdx) := by
    rw [← mux159_eq muxBit uIdx F]
    simp only [QRegister.embedUnitary_mul, QRegister.embedUnitary_compose, mul_assoc]
  have hHotIn : ∀ c : Fin 128, ∃ c' : Fin 128,
      (r.compose mid159Hot128Reg) c = (r.compose mid159Hot128Reg) c' := fun c ↦ ⟨c, rfl⟩
  have hQrZ : SelectSwapQROM.zeroProjOn rScr.image *
      ((r.compose mid159QroReg).embedUnitary (aliasTableXorUnitary (5 + 128) 14 F)).1 =
      ((r.compose mid159QroReg).embedUnitary (aliasTableXorUnitary (5 + 128) 14 F)).1 *
      SelectSwapQROM.zeroProjOn rScr.image := by
    rw [QRegister.embedUnitary_val]
    exact (preservesWires_comm_zeroProjOn (preservesWires_embedMatrix_of_disjoint
      (r.compose mid159QroReg) (aliasTableXorUnitary (5 + 128) 14 F).1 rScr.image
      (SelectSwapQROM.disjoint_image_of_disjointWires (hdisj.compose_left _)))
      Finset.Subset.rfl).symm
  have hQrP : predProj (xoOneHotPred (r.compose mid159Xo7Reg) (r.compose mid159Hot128Reg)) *
      ((r.compose mid159QroReg).embedUnitary (aliasTableXorUnitary (5 + 128) 14 F)).1 =
      ((r.compose mid159QroReg).embedUnitary (aliasTableXorUnitary (5 + 128) 14 F)).1 *
      predProj (xoOneHotPred (r.compose mid159Xo7Reg) (r.compose mid159Hot128Reg)) :=
    (preservesWires_comm_predProj_xoOneHot
      (rXo := r.compose mid159Xo7Reg) (rHot := r.compose mid159Hot128Reg)
      (preservesWiresMid159Qroxo_hot r (r.compose mid159Hot128Reg) hHotIn F)).symm
  have hQrQ0 : Mobius126OneHot.cleanPredProj rScr.image
      (xoOneHotPred (r.compose mid159Xo7Reg) (r.compose mid159Hot128Reg)) *
      ((r.compose mid159QroReg).embedUnitary (aliasTableXorUnitary (5 + 128) 14 F)).1 =
      ((r.compose mid159QroReg).embedUnitary (aliasTableXorUnitary (5 + 128) 14 F)).1 *
      Mobius126OneHot.cleanPredProj rScr.image
        (xoOneHotPred (r.compose mid159Xo7Reg) (r.compose mid159Hot128Reg)) := by
    dsimp only [Mobius126OneHot.cleanPredProj]
    rw [Matrix.mul_assoc, hQrP, ← Matrix.mul_assoc, hQrZ, Matrix.mul_assoc]
  refine ⟨fun Θ hΘ σ val ↦ by
    rw [genPrepMid18InvDyn_wp_split]
    exact hPre.2.2.1 _ (hQrUpd _ (hPost.2.2.1 Θ hΘ)) σ val, fun Θ hΘ σ ↦ ?_⟩
  rw [genPrepMid18InvDyn_wp_split]
  exact conj_unload3_xoOneHot (cleanPredProj_conjTranspose _ _)
    (cleanPredProj_conjTranspose _ _) (cleanPredProj_mul_of_subset Finset.subset_union_left _)
    hW1Eq hQrQ0 hPre hPost Θ hΘ (hQrUpd _ (hPost.2.2.1 Θ hΘ)) σ
    (hQrConj _ (hPost.2.2.1 Θ hΘ) σ)
theorem wpPrepMid18DagW3Pi128Dyn_xoOneHot {Var : Type} [Fintype Var] [DecidableEq Var]
    {sMuxReq tMux : ℕ} {muxBit : Fin (2 ^ 4) → Fin (2 ^ 9) → Bool}
    (bundleSpec : Mux23Bundle Var sMuxReq tMux muxBit) (π128 : Equiv.Perm (Fin 128))
    {N sScr : ℕ} (v : Var) (r : QRegister (mMidUB 18 + (7 + 128)) N)
    (rScr : QRegister sScr N) (hScr : sMuxReq ≤ sScr) (hdisj : r.DisjointWires rScr)
    (uIdx : Unitary (2 ^ 5)) {uDP : DynamicCircuit Var N}
    (huDP : Solution.CleanDyn.CleanRealizes v (r.compose mid159Idx5Reg) rScr uIdx⁻¹ uDP) :
    let F_lin := hotLinearTargetFn 5 128 14 (keep9Pi128Hot14Bool π128)
    let W_1 := r.embedUnitary (muxOnAct (mMidUB 18) (7 + 128) (hotBranch18Of muxBit uIdx F_lin))
    let S_all := rScr.image ∪ (r.compose mid159AliasOutReg).image
    let Q_all := Mobius126OneHot.cleanPredProj S_all
      (xoOneHotPred (r.compose mid159Xo7Reg) (r.compose mid159Hot128Reg))
    (∀ Θ : QCAssertion Var (2 ^ N), (∀ σ val, Θ (Function.update σ v val) = Θ σ) →
      ∀ σ val,
        wp (prepMid18DagW3Pi128Dyn bundleSpec.toMux23Circ π128 v r rScr hScr hdisj uDP).compile
        Θ (Function.update σ v val) =
      wp (prepMid18DagW3Pi128Dyn bundleSpec.toMux23Circ π128 v r rScr hScr hdisj uDP).compile Θ σ) ∧
    (∀ Θ : QCAssertion Var (2 ^ N), (∀ σ val, Θ (Function.update σ v val) = Θ σ) →
      ∀ σ : Store Var,
        ((qcWpQAssign W_1
          (wp (prepMid18DagW3Pi128Dyn bundleSpec.toMux23Circ π128 v r rScr hScr hdisj uDP).compile
            Θ)
          σ).1).conj Q_all = ((Θ σ).1).conj Q_all) := by
  dsimp only [prepMid18DagW3Pi128Dyn]
  exact wpGenPrepMid18InvDyn_xoOneHot_aux bundleSpec v r rScr hScr hdisj uIdx huDP
    (hotLinearTargetFn 5 128 14 (keep9Pi128Hot14Bool π128))
    (qromXMeasW3FromHotCtxAliasUnloadDyn (L_ctx := 128) (b := 9) (payBits := 0) v
      (keep9Pi128Hot14Bool π128) (r.compose mid159ToAlias157) rScr
      (by
          dsimp [CoherentAlias.aliasOutBits]
          omega) (hdisj.compose_left _))
    (fun Ψ hΨ σ' b ↦ wp_qromXMeasW3FromHotCtxAliasUnloadDyn_update_self _ _ _ _ _ _ Ψ hΨ σ' b)
    (fun Ψ hΨ σ ↦ wp_qromW3Keep9Pi128_conj_xoOneHot π128 v r rScr hdisj Ψ hΨ σ)
attribute [irreducible] prepMid18DagW3Pi128Dyn

end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.Inner18HadWSuperLegsA
end
