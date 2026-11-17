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
public import QuantumComputationDiscoveries.Algorithms.Photochemistry.Solution.ReflectedStage4Coin70

open QuantumComputation.Specs.PhotochemistrySolution.SpecDefs
open QuantumComputation.Specs.PhotochemistrySolution.QhlAux
open QuantumComputation.Specs.PhotochemistrySolution.PgBase
open QuantumComputation.Specs.PhotochemistrySolution.SelectBase
@[expose] public section
set_option allowUnsafeReducibility true
set_option autoImplicit false

noncomputable section
set_option exponentiation.threshold 256
open scoped Matrix BigOperators


noncomputable section
open Operator QProg Matrix Circuit Qubit QuantumComputation.Specs.PhotochemistrySolution
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
namespace QuantumComputation.Specs.PhotochemistrySolution.ReflStage4
set_option exponentiation.threshold 8192
open Real QuantumComputation.Specs
  PhotochemistrySolution.SelectOracles PhotochemistrySolution.Stage12Compact
open PhotochemistrySolution.ZeroNEremSpec PhotochemistrySolution.PotSelectWiring
  PhotochemistrySolution.SelectCompactAnc PhotochemistrySolution.TopSelectBridge
theorem pow_two_ne_zero_bridge0 (k : ℕ) : 2 ^ k ≠ 0 := pow_ne_zero k two_ne_zero
local instance (priority := 100000) {k : ℕ} : NeZero (2 ^ k) := ⟨pow_two_ne_zero_bridge0 k⟩
attribute [local reducible] totDimCompactGen
attribute [local irreducible] systemQubits_frozen SelectCompactAnc.ancWOfScr reflULGen
    SelectLocalSpecGen
end QuantumComputation.Specs.PhotochemistrySolution.ReflStage4

namespace QuantumComputation.Specs.PhotochemistrySolution.Stage2ZeroGated
open PhotochemistrySolution.SplitRouter47_187
open _root_.DynamicCircuit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt hiding bit_cases
  eval_seq_mulVec ket ket_CNOT ket_TOFF ket_X ket_projector_one ket_projector_zero matrix_ext_ket
  qAssign_obs_map_val
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SplitRouterSeqBell26k hiding ket
  matrix_ext_ket
attribute [local irreducible] uRouterSwapConj
theorem zg47_hMD : 47 < 2 ^ 6 := by omega
theorem zg47_hD2 : 2 ≤ 6 := by omega
theorem zg187_hMD : 187 < 2 ^ 8 := by omega
theorem zg187_hD2 : 2 ≤ 8 := by omega
end QuantumComputation.Specs.PhotochemistrySolution.Stage2ZeroGated

namespace QuantumComputation.Specs.PhotochemistrySolution.Stage2ChDiffNoNF
open scoped ComplexOrder MatrixOrder
open HermitianMat PhotochemistrySolution.XMeasUnld PhotochemistrySolution.SplitRouter47_187
  PhotochemistrySolution.Stage2QromMux
open PhotochemistrySolution.Stage2ZeroGated PhotochemistrySolution.DynQromUncompA
open _root_.DynamicCircuit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt hiding bit_cases
  eval_seq_mulVec ket ket_CNOT ket_TOFF ket_X ket_projector_one ket_projector_zero matrix_ext_ket
  qAssign_obs_map_val
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB hiding bitSign eval_seq_mulVec ket
  ket_CNOT ket_TOFF ket_X matrix_ext_ket writeReg writeReg_apply_of_not_mem
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SplitRouterSeqBell26k hiding ket
  matrix_ext_ket
attribute [local semireducible]
  ComputeProg.ValidProg ComputeProg.finalClean ComputeProg.fwdBits
  PhotochemistrySolution.DynQromUncompA.fwdCirc
theorem fwdBits_pUMsbStep_uMsb_spec {M D n : ℕ} (r : RouterReg M D n)
    (m : ℕ) (hm : m + 1 < D) (η : BitAssignment n) :
    let dk : Fin D := ⟨m + 1, hm⟩; let dk1 : Fin D := ⟨m, Nat.lt_of_succ_lt hm⟩;
    let v1 : ZMod 2 := η (rUMsb r dk1) + η (rUMsb r dk) * (1 + diffBit true r η dk)
    ((pUMsbStep true r m hm).fwdBits η (rUMsb r dk1) = v1) ∧
        ((pUMsbStep true r m hm).fwdBits η (rUMsb r dk) = η (rUMsb r dk) + v1) ∧
    (∀ d : Fin D, d ≠ dk1 → d ≠ dk → (pUMsbStep true r m hm).fwdBits η (rUMsb r d) = η (rUMsb r d))
        := by
  intro dk dk1 v1; have hNeU : dk1 ≠ dk := hdr_succ_ne m hm
  let η₁ := Function.update η (rIdx2 r dk) (1 + diffBit true r η dk);
  let η₂ := Function.update η₁ (rUMsb r dk1) v1
  have hPostU (st : BitAssignment n) (d : Fin D) : (pUMsbPost true r dk).fwdBits st (rUMsb r d) =
      st (rUMsb r d) := by
    simp only [pUMsbPost, ↓reduceIte, ComputeProg.fwdBits,
        Function.update_of_ne (rUMsb_ne_rIdx2 r d dk)]
  have hStep (d : Fin D) : (pUMsbStep true r m hm).fwdBits η (rUMsb r d) =
      (ComputeProg.cnot (rUMsb r dk1) (rUMsb r dk)
          (rUMsb_ne_of_ne r hNeU)).fwdBits ((pUMsbPost true r dk).fwdBits η₂) (rUMsb r d) := by
    rw [← show (ComputeProg.andGate (rUMsb r dk) (rIdx2 r dk) (rUMsb r dk1) (rUMsb_ne_rIdx2 r dk dk)
        (rUMsb_ne_of_ne r hNeU).symm (rUMsb_ne_rIdx2 r dk1 dk).symm).fwdBits
            ((pUMsbPre true r dk).fwdBits η) = η₂ by
      rw [show (pUMsbPre true r dk).fwdBits η = η₁ from funext fun u ↦ by
        dsimp [pUMsbPre, diffBit, ComputeProg.fwdBits, η₁]
        rcases eq_or_ne u (rIdx2 r dk) with rfl | h
        · simp only [Function.update_self, Function.update_of_ne ((hne_zg_hdr r).2.2.2.1 dk),
            Function.update_of_ne ((hne_zg_hdr r).2.2.2.2.1 dk)]
          exact zmod2_pre_true _ _ _ _
        · simp only [Function.update_of_ne h]]
      simp only [ComputeProg.fwdBits, η₂, v1, η₁, Function.update_self,
        Function.update_of_ne (rUMsb_ne_rIdx2 r dk1 dk),
            Function.update_of_ne (rUMsb_ne_rIdx2 r dk dk)]]
    rfl
  exact
      ⟨by simp only [hStep dk1, ComputeProg.fwdBits, Function.update_of_ne (rUMsb_ne_of_ne r hNeU),
            hPostU, η₂, Function.update_self],
    by simp only [hStep dk, ComputeProg.fwdBits, Function.update_self, hPostU, η₂, η₁,
      Function.update_of_ne (rUMsb_ne_of_ne r hNeU.symm),
          Function.update_of_ne (rUMsb_ne_rIdx2 r dk dk)],
    fun d hd1 hd ↦
        by simp only [hStep d, ComputeProg.fwdBits, Function.update_of_ne (rUMsb_ne_of_ne r hd),
             hPostU, η₂, η₁,
      Function.update_of_ne (rUMsb_ne_of_ne r hd1), Function.update_of_ne (rUMsb_ne_rIdx2 r d dk)]⟩
theorem fwdBits_pUMsbDownLoop_uMsb_congr {M D n : ℕ} {r₁ r₂ : RouterReg M D n}
    (hSPP : SamePubPriv r₁ r₂) :
    ∀ (k : ℕ) (hk : k < D) {δ₁ δ₂ : BitAssignment n},
      (∀ w, PubCtrlSet r₁ w → δ₁ w = δ₂ w) →
      (∀ d : Fin D, δ₁ (rUMsb r₁ d) = δ₂ (rUMsb r₂ d)) →
      (∀ w, PubCtrlSet r₁ w →
        (pUMsbDownLoop true r₁ k hk).fwdBits δ₁ w =
        (pUMsbDownLoop true r₂ k hk).fwdBits δ₂ w) ∧
      (∀ d : Fin D,
        (pUMsbDownLoop true r₁ k hk).fwdBits δ₁ (rUMsb r₁ d) =
        (pUMsbDownLoop true r₂ k hk).fwdBits δ₂ (rUMsb r₂ d))
  | 0, _, _, _, hPub, hU => ⟨hPub, hU⟩
  | k + 1, hk, δ₁, δ₂, hPub, hU => by
      have hPE := samePubPriv_pub_eq hSPP; have hPR := pubCtrlSet_roles r₁
      let dk : Fin D := ⟨k + 1, hk⟩; let dk1 : Fin D := ⟨k, Nat.lt_of_succ_lt hk⟩
      have hDiff : diffBit true r₁ δ₁ dk = diffBit true r₂ δ₂ dk := by
        dsimp [diffBit]
        rw [← hPE.1, ← hPE.2.1, ← congrFun hPE.2.2.1 dk, ← congrFun hPE.2.2.2.1 dk,
          hPub _ (hPR.2.2.1 dk), hPub _ (hPR.2.2.2 dk), hPub _ hPR.1, hPub _ hPR.2.1]
      obtain ⟨s1a, s1b, s1c⟩ := fwdBits_pUMsbStep_uMsb_spec r₁ k hk δ₁; obtain ⟨s2a, s2b, s2c⟩ :=
          fwdBits_pUMsbStep_uMsb_spec r₂ k hk δ₂
      refine fwdBits_pUMsbDownLoop_uMsb_congr hSPP k (Nat.lt_of_succ_lt hk) ?_ fun d ↦ ?_
      · rintro _ ⟨u, hu, rfl⟩
        rw [fwdBits_pUMsbStep_of_ne_uMsb r₁ k hk δ₁ (fun d ↦
            rr_ne r₁ (by have := d.isLt; unfold basePub; dsimp; omega)),
          fwdBits_pUMsbStep_of_ne_uMsb r₂ k hk δ₂ (fun d ↦
              (hSPP.1 u (by unfold basePub; omega)) ▸ rr_ne r₂
              (by have := d.isLt; unfold basePub; dsimp; omega))]
        exact hPub (r₁ u) ⟨u, hu, rfl⟩
      · rcases eq_or_ne d dk1 with rfl | hd1
        · rw [s1a, s2a, hU dk1, hU dk, hDiff]
        · exact (eq_or_ne d dk).elim (fun h ↦ h ▸ by rw [s1b, s2b, hU dk, hU dk1, hDiff]) fun hd ↦
              by
            rw [s1c d hd1 hd, s2c d hd1 hd, hU d]
/-- Top 6-CNOT initializer of `pUMsbHdrZG` for general `(M, D)`. -/
def pInitTopD {M D n : ℕ} (hD2 : 2 ≤ D) (r : RouterReg M D n) : ComputeProg n :=
  let hu := (hne_zg_hdr r).2.2; let dTop : Fin D := ⟨D - 1, hdr_lt1 (Nat.le_of_succ_le hD2)⟩;
  let dSub : Fin D := ⟨D - 2, hdr_lt2 hD2⟩; let hNeTS : dTop ≠ dSub := hdr_top_ne_sub hD2
  .seq (.cnot (rIdx1 r dTop) (rUMsb r dTop) (hu.2.2.2.2.2.1 dTop))
    (.seq (.cnot (rIdx2 r dTop) (rUMsb r dTop) (hu.2.2.2.2.2.2.1 dTop))
      (.seq (.cnot (rHas1 r) (rUMsb r dTop) (hu.2.2.2.1 dTop))
        (.seq (.cnot (rRawHas2 r) (rUMsb r dTop) (hu.2.2.2.2.1 dTop))
          (.seq (.cnot (rHas1 r) (rUMsb r dSub) (hu.2.2.2.1 dSub))
                (.cnot (rUMsb r dTop) (rUMsb r dSub) (rUMsb_ne_of_ne r hNeTS))))))
theorem fwdBits_pInitTopD_uMsb_spec {M D n : ℕ} (hD2 : 2 ≤ D) (r : RouterReg M D n)
    (δ : BitAssignment n) :
    let dTop : Fin D := ⟨D - 1, hdr_lt1 (Nat.le_of_succ_le hD2)⟩;
    let dSub : Fin D := ⟨D - 2, hdr_lt2 hD2⟩;
    let vTop : ZMod 2 :=
        δ (rUMsb r dTop) + δ (rIdx1 r dTop) + δ (rIdx2 r dTop) + δ (rHas1 r) + δ (rRawHas2 r)
    ((pInitTopD hD2 r).fwdBits δ (rUMsb r dTop) = vTop) ∧
        ((pInitTopD hD2 r).fwdBits δ (rUMsb r dSub) = δ (rUMsb r dSub) + δ (rHas1 r) + vTop) ∧
    (∀ d : Fin D, d ≠ dSub → d ≠ dTop → (pInitTopD hD2 r).fwdBits δ (rUMsb r d) = δ (rUMsb r d))
        := by
  intro dTop dSub vTop; have hNeTS : dTop ≠ dSub := hdr_top_ne_sub hD2; let hu := (hne_zg_hdr r).2.2
  exact
      ⟨by simp only [pInitTopD, dTop, dSub, vTop, ComputeProg.fwdBits, Function.update_self,
            Function.update_of_ne (rUMsb_ne_of_ne r hNeTS), Function.update_of_ne (hu.2.2.2.1 dTop),
            Function.update_of_ne (hu.2.2.2.2.1 dTop),
            Function.update_of_ne (hu.2.2.2.2.2.2.1 dTop)],
    by simp only [pInitTopD, dTop, dSub, vTop, ComputeProg.fwdBits, Function.update_self,
         Function.update_of_ne (rUMsb_ne_of_ne r hNeTS),
         Function.update_of_ne (rUMsb_ne_of_ne r hNeTS.symm),
         Function.update_of_ne (hu.2.2.2.1 dTop), Function.update_of_ne (hu.2.2.2.2.1 dTop),
         Function.update_of_ne (hu.2.2.2.2.2.2.1 dTop)],
    fun d hdS hdT ↦
        by simp only [pInitTopD, dTop, dSub, ComputeProg.fwdBits,
             Function.update_of_ne (rUMsb_ne_of_ne r hdS),
             Function.update_of_ne (rUMsb_ne_of_ne r hdT)]⟩
theorem fwdBits_pUMsbHdrZG_uMsb_congr {M D n : ℕ} (hD2 : 2 ≤ D) {r₁ r₂ : RouterReg M D n}
    (hSPP : SamePubPriv r₁ r₂)
    {δ₁ δ₂ : BitAssignment n} (hPub : ∀ w, PubCtrlSet r₁ w → δ₁ w = δ₂ w)
        (hU : ∀ d : Fin D, δ₁ (rUMsb r₁ d) = δ₂ (rUMsb r₂ d)) :
    ∀ d : Fin D, (pUMsbHdrZG hD2 r₁).fwdBits δ₁ (rUMsb r₁ d) =
        (pUMsbHdrZG hD2 r₂).fwdBits δ₂ (rUMsb r₂ d) := by
  have hPE := samePubPriv_pub_eq hSPP; have hPR := pubCtrlSet_roles r₁
  let dTop : Fin D := ⟨D - 1, hdr_lt1 (Nat.le_of_succ_le hD2)⟩;
  let dSub : Fin D := ⟨D - 2, hdr_lt2 hD2⟩
  obtain ⟨s1T, s1S, s1O⟩ := fwdBits_pInitTopD_uMsb_spec hD2 r₁ δ₁; obtain ⟨s2T, s2S, s2O⟩ :=
      fwdBits_pInitTopD_uMsb_spec hD2 r₂ δ₂
  have eTop : (pInitTopD hD2 r₁).fwdBits δ₁ (rUMsb r₁ dTop) =
      (pInitTopD hD2 r₂).fwdBits δ₂ (rUMsb r₂ dTop) := by
    rw [s1T, s2T, hU dTop, ← congrFun hPE.2.2.1 dTop, ← congrFun hPE.2.2.2.1 dTop, ← hPE.1,
        ← hPE.2.1,
      hPub _ (hPR.2.2.1 dTop), hPub _ (hPR.2.2.2 dTop), hPub _ hPR.1, hPub _ hPR.2.1]
  refine (fwdBits_pUMsbDownLoop_uMsb_congr hSPP (D - 2) (hdr_lt2 hD2)
    (δ₁ := (pInitTopD hD2 r₁).fwdBits δ₁) (δ₂ := (pInitTopD hD2 r₂).fwdBits δ₂) ?_ fun d ↦ ?_).2
  · rintro _ ⟨u, hu, rfl⟩; have eqw : r₁ u = r₂ u := hSPP.1 u (by unfold basePub; omega)
    simp only [pInitTopD, dTop, dSub, ComputeProg.fwdBits,
      Function.update_of_ne (rr_ne r₁ (by have := dSub.isLt; unfold basePub; dsimp; omega) : r₁ u ≠
          rUMsb r₁ dSub),
      Function.update_of_ne (rr_ne r₁ (by have := dTop.isLt; unfold basePub; dsimp; omega) : r₁ u ≠
          rUMsb r₁ dTop),
      Function.update_of_ne (eqw ▸ rr_ne r₂ (by have := dSub.isLt; unfold basePub; dsimp; omega) :
          r₁ u ≠ rUMsb r₂ dSub),
      Function.update_of_ne (eqw ▸ rr_ne r₂ (by have := dTop.isLt; unfold basePub; dsimp; omega) :
          r₁ u ≠ rUMsb r₂ dTop)]
    exact hPub (r₁ u) ⟨u, hu, rfl⟩
  · rcases eq_or_ne d dSub with rfl | hdS
    · rw [s1S, s2S, ← s1T, ← s2T, eTop, hU dSub, ← hPE.1, hPub _ hPR.1]
    · exact (eq_or_ne d dTop).elim (fun h ↦ h ▸ eTop) fun hdT ↦
          by rw [s1O d hdS hdT, s2O d hdS hdT, hU d]
theorem samePubPriv_symm_ke0 {M D n : ℕ} {r₁ r₂ : RouterReg M D n} (h : SamePubPriv r₁ r₂) :
    SamePubPriv r₂ r₁ := ⟨fun u hu ↦ (h.1 u hu).symm, h.2.symm⟩
end QuantumComputation.Specs.PhotochemistrySolution.Stage2ChDiffNoNF
end

section

open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynQromUncompA (fwdCirc
    wrapDyn)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SplitBellVecCleanStep
  (specFanoutCopyCirc bellZHalfVecDyn bellXHalfVecDyn)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SplitRouterSeqBell26k (SupportedOn)
noncomputable section
namespace QuantumComputation.Specs.PhotochemistrySolution.OuterW11Alt
open Real PhotochemistrySolution.ZHi30
/-- Per-sample `30`-bit channel shift function matching `zKnotW11`. -/
def chFn : ChW11 → ℕ → ℕ
  | .ee => fnEE30
  | .nn => fnNN30
  | .en9 => fnEN9_30
  | .en10 => fnEN10_30
theorem chFn_eq_chFnFast (ch : ChW11) (y : ℕ) : chFn ch y = chFnFast ch y := by
  cases ch <;> simp [chFn, chFnFast, fnEE30, fnNN30, fnEN9_30, fnEN10_30, Nat.shiftRight_eq_div_pow]
def qKnotW11 (q0 q1 q2 q3 j : ℕ) : ℕ :=
    if j = 0 then q0 else if j = 1 then q1 else if j = 2 then q2 else q3
end QuantumComputation.Specs.PhotochemistrySolution.OuterW11Alt

namespace QuantumComputation.Specs.PhotochemistrySolution.Stage2ChDiffNoNF
open Operator QProg Matrix Circuit Qubit PhotochemistrySolution PhotochemistrySolution.XMeasUnld
  PhotochemistrySolution.SplitRouter47_187
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
open PhotochemistrySolution.Stage2QromMux PhotochemistrySolution.Stage2ZeroGated
  PhotochemistrySolution.Stage2ElecFirstZero
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB hiding bitSign eval_seq_mulVec ket
  ket_CNOT ket_TOFF ket_X matrix_ext_ket writeReg writeReg_apply_of_not_mem
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SplitRouterSeqBell26k hiding ket
  matrix_ext_ket
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SortedRouterSpec
  (ValidZeroGatedSortedRouterInput)
def swapBotNoNF (i : ℕ) : ℕ := swapPair 4999 5028 1 i
theorem swapBotNoNF_lt : ∀ i < routerWidth 187 8, swapBotNoNF i < routerWidth 187 8 := fun _ hi ↦
  swapPair_lt (by decide) (by decide) hi
theorem swapBotNoNF_invol : ∀ i < routerWidth 187 8, swapBotNoNF (swapBotNoNF i) = i :=
  fun i _ ↦ swapPair_invol (Or.inl (by omega)) i
theorem swapBotNoNF_pub : ∀ i < basePub 187 8, swapBotNoNF i = i :=
  fun i (hi : i < 4602) ↦ swapPair_fixed (by omega) (by omega)
/-- Router redirecting `rUMsb 0` to `r 5028` while keeping `PubCtrlSet` and `rUMsb[1..7]` fixed. -/
def rBotNoNF {n : ℕ} (r : RouterReg 187 8 n) : RouterReg 187 8 n :=
    routerOfInvol r swapBotNoNF swapBotNoNF_lt swapBotNoNF_invol
theorem samePubPriv_rBotNoNF {n : ℕ} (r : RouterReg 187 8 n) : SamePubPriv (rBotNoNF r) r :=
    samePubPriv_routerOfInvol r swapBotNoNF swapBotNoNF_lt swapBotNoNF_invol swapBotNoNF_pub
theorem actsIndepOf_mul_unitary {n : ℕ} {P : Wire n → Prop} {U₁ U₂ : Unitary (2 ^ n)}
    (h₁ : ActsIndepOf P U₁) (h₂ : ActsIndepOf P U₂) : ActsIndepOf P (U₁ * U₂) :=
  let ⟨f₁, k₁, u₁⟩ := h₁
  let ⟨f₂, k₂, u₂⟩ := h₂
  ⟨fun α ↦ f₁ (f₂ α), fun α ↦ by rw [Submonoid.coe_mul, ← Matrix.mulVec_mulVec, k₂ α, k₁ (f₂ α)],
    fun q hq α val ↦ (congrArg f₁ (u₂ q hq α val)).trans (u₁ q hq (f₂ α) val)⟩
theorem cleanProj_unitary_in {M D n : ℕ} (r : RouterReg M D n) (F : Finset (Wire n))
    (U : Unitary (2 ^ n)) (f : BitAssignment n → BitAssignment n)
    (hfKet : ∀ β, ValidZeroGatedSortedRouterInput r β → U.1.mulVec (ket β) = ket (f β))
    (hf0 : ∀ β, ValidZeroGatedSortedRouterInput r β → ∀ w ∈ F, f β w = 0) (R : Operator (2 ^ n))
    (hR : SupportedOn (ValidZeroGatedSortedRouterInput r) R) : cleanProj F * (U.1 * R) = U.1 *
    R := by
  let _ : NeZero (2 ^ n) := ⟨pow_ne_zero n two_ne_zero⟩
  rw [← Matrix.mul_assoc]
  refine hR (cleanProj F * U.1) U.1 fun β hβ ↦ ?_
  rw [← Matrix.mulVec_mulVec, ket_sr_eq, hfKet β hβ, cleanProj_mulVec_ket, ite_eq_left (hf0 β hβ)]
end QuantumComputation.Specs.PhotochemistrySolution.Stage2ChDiffNoNF
end

set_option maxRecDepth 4096
namespace QuantumComputation.Specs.PhotochemistrySolution.Instances
scoped instance (priority := 100000) {k : ℕ} : NeZero (2 ^ k) := ⟨pow_ne_zero k two_ne_zero⟩
end QuantumComputation.Specs.PhotochemistrySolution.Instances
open scoped QuantumComputation.Specs.PhotochemistrySolution.Instances
/- ## Section 4: `dLayout` Safe-Range Bounds (`5827..5850` Included) & Stage-4 Commutations -/

noncomputable section
open Operator QProg Matrix Circuit Qubit PrimitiveGate QuantumComputation.Specs
  QuantumComputation.Specs.PhotochemistrySolution.KetSupport
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
open QuantumComputation.Specs.PhotochemistrySolution
  QuantumComputation.Specs.PhotochemistrySolution.SplitRouter47_187
  QuantumComputation.Specs.PhotochemistrySolution.UnembedO3Bridge
open QuantumComputation.Specs.PhotochemistrySolution.SelectOracles
  QuantumComputation.Specs.PhotochemistrySolution.RouterSelectWiringA
  QuantumComputation.Specs.PhotochemistrySolution.RouterSelectWiringB
  QuantumComputation.Specs.PhotochemistrySolution.ProviderCore
open QuantumComputation.Specs.PhotochemistrySolution.Stage12Compact
  QuantumComputation.Specs.PhotochemistrySolution.ZeroNEremSpec
  QuantumComputation.Specs.PhotochemistrySolution.PotSelectWiring
  QuantumComputation.Specs.PhotochemistrySolution.Stage2Xor84
open QuantumComputation.Specs.PhotochemistrySolution.Stage2PotUnld
  QuantumComputation.Specs.PhotochemistrySolution.Stage2ElecFirst
  QuantumComputation.Specs.PhotochemistrySolution.SortedRouterSpec
  QuantumComputation.Specs.PhotochemistrySolution.Coin70Lift
open QuantumComputation.Specs.PhotochemistrySolution.Sub5885MuxD1
noncomputable section
namespace QuantumComputation.Specs.PhotochemistrySolution.Sub5885
open PhotochemistrySolution.ProviderCoreFused PhotochemistrySolution.GenWeightsSelect
  PhotochemistrySolution.PotOraclePortB PhotochemistrySolution.Kinetic664
open PhotochemistrySolution.Kinetic664Stage4 PhotochemistrySolution.SelectCompactAnc
  PhotochemistrySolution.XMeasChunkQromUnldA
open _root_.DynamicCircuit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt hiding bit_cases
  eval_seq_mulVec ket ket_CNOT ket_TOFF ket_X ket_projector_one ket_projector_zero localIdx
  matrix_ext_ket qAssign_obs_map_val
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB (ket)
attribute [local irreducible] systemQubits_frozen SelectCompactAnc.ancWOfScr uRouterSwapConj
    phaseFlipUnitary
  CleanWorkStep

theorem lift_sup_pScrExt {kExt n : ℕ} (hk : kExt ≤ 72) (rTot : QRegister dLayout n)
    {L X : Operator (2 ^ n)} {P : BitAssignment n → Prop}
    (hComm : ∀ γ, L * (uTogGen_c70 (rTot.compose (rCoinExt kExt hk)) γ).1 =
      (uTogGen_c70 (rTot.compose (rCoinExt kExt hk)) γ).1 * L)
          (hCongr : ∀ γ β, P β → P (togBits_c70 (rTot.compose (rCoinExt kExt hk)) γ β))
          (hBase : ∀ Z : Operator (2 ^ n),
      (rTot.compose rScrLayout).basisOutcomeProjector 0 *
          ((rTot.compose rScrLayout).basisOutcomeProjector 0 * Z) =
          (rTot.compose rScrLayout).basisOutcomeProjector 0 * Z →
      SupportedOn P (L * ((rTot.compose rScrLayout).basisOutcomeProjector 0 * Z)))
          (hX : (rTot.compose (rScrExt kExt hk)).basisOutcomeProjector 0 * X = X) :
          SupportedOn P (L * X) := by
  let rC := rTot.compose (rCoinExt kExt hk)
  let R₀ := (rTot.compose rScrLayout).basisOutcomeProjector 0
  nth_rw 1 [← hX]
  rw [pScrExt_eq_sum_tog_c70 hk rTot, Finset.sum_mul, Matrix.mul_sum,
    Finset.sum_congr rfl fun γ _ ↦ show L * (_ * R₀ * _ * X) =
      (uTogGen_c70 rC γ).1 * (L * (R₀ * ((uTogGen_c70 rC γ).1 * X))) by
      simp only [← Matrix.mul_assoc, hComm γ, rC]]
  refine supportedOn_sum_c70 fun γ ↦ supportedOn_uTogGen_mul_c70 rC γ (hCongr γ) (hBase _ ?_)
  rw [← Matrix.mul_assoc, QRegister.basisOutcomeProjector_mul_self]

/-- Lift `routerChain_sorted_of_validMuxD1Stage2Regs` from `rScrLayout` to `rScrExt kExt hk`. -/
theorem routerChain_sorted_validMuxD1_ext {kExt w1 n : ℕ}
    {decodeCoin : Fin (2 ^ 41) → ZeroNEremSector}
    {rNuc : RouterReg 47 6 dLayout} {rElec : RouterReg 187 8 dLayout}
    (hk : kExt ≤ 72) (hRegs : ValidMuxD1Stage2Regs rNuc rElec)
    (dN : ∀ i j, rNuc i ≠ rCoinExt kExt hk j)
    (dE : ∀ i j, rElec i ≠ rCoinExt kExt hk j)
    (hSort : SortedZeroNEremCoin decodeCoin)
    (rTot : QRegister dLayout n) (o1 : Stage1ZeroNEremLayout w1 decodeCoin)
    {X : Operator (2 ^ n)}
    (hX : (rTot.compose (rScrExt kExt hk)).basisOutcomeProjector 0 * X = X) :
    let W_cl := rTot.embedUnitary (uStage1Clean_c70 decodeCoin)
    let Wnh_cl := rTot.embedUnitary (wNoHad (uStage1Clean_c70 decodeCoin))
    SupportedOn (ValidZeroGatedSortedRouterInput (rTot.compose rElec))
        (W_cl.1 * X) ∧ SupportedOn (ValidZeroGatedSortedRouterInput (rTot.compose rNuc))
        ((uRouterSwapConj (rTot.compose rElec)).1 * (W_cl.1 * X)) ∧
    (uRouterSwapConj (rTot.compose rNuc)).1 * ((uRouterSwapConj (rTot.compose rElec)).1 *
        (W_cl.1 * X)) = Wnh_cl.1 * X ∧ (rTot.compose rClean690Layout).basisOutcomeProjector 0 *
        (Wnh_cl.1 * X) = Wnh_cl.1 * X := by
  intro W_cl Wnh_cl
  let rC := rTot.compose (rCoinExt kExt hk)
  let rE := rTot.compose rElec
  let rN := rTot.compose rNuc
  let rW := rTot.compose rClean690Layout
  have cU (γ) : W_cl.1 * (uTogGen_c70 rC γ).1 = (uTogGen_c70 rC γ).1 * W_cl.1 := by
    simpa only [embedUnitary_uTogLocal_c70] using wStage1Clean_comm_rCoinExt_c70 decodeCoin hk rTot
        (uTogLocal_c70 γ)
  have cWnh (γ) : Wnh_cl.1 * (uTogGen_c70 rC γ).1 = (uTogGen_c70 rC γ).1 * Wnh_cl.1 := by
    simpa only [embedUnitary_uTogLocal_c70] using wNoHadClean_comm_rCoinExt_c70 decodeCoin hk rTot
        (uTogLocal_c70 γ)
  have cR {M D} {r : RouterReg M D dLayout} (hd : ∀ i j, r i ≠ rCoinExt kExt hk j) (γ) :
      Commute (uRouterSwapConj (rTot.compose r)).1 (uTogGen_c70 rC γ).1 := by
    simpa only [Commute, SemiconjBy,
        embedUnitary_uTogLocal_c70] using comm_uRouterSwapConj_embedUnitary_c70
      (rTot.compose r) rC (fun i j e ↦ hd i j (rTot.wires.injective e)) (uTogLocal_c70 γ)
  have cP (γ) : rW.basisOutcomeProjector 0 * (uTogGen_c70 rC γ).1 = (uTogGen_c70 rC γ).1 *
      rW.basisOutcomeProjector 0 := by
    rw [← embedUnitary_uTogLocal_c70, QRegister.basisOutcomeProjector, QRegister.embedUnitary_val]
    exact rW.embedMatrix_comm_of_disjoint rC
      (QRegister.disjoint_iff.mpr fun i j e ↦
          (router_disj_rCoinExt_c70 hk).2.2.2.2 i j (rTot.wires.injective e))
      (compProj 0) (uTogLocal_c70 γ).1
  obtain ⟨_, _, cEq0, _, c690_0⟩ := routerChain_sorted_of_validMuxD1Stage2Regs hRegs hSort rTot o1
    (QRegister.basisOutcomeProjector_mul_self _ 0)
  rw [← wStage1Clean_mul_rScrLayout_c70 o1 rTot, ← wNoHadClean_mul_rScrLayout_c70 o1 rTot] at cEq0
  rw [← wNoHadClean_mul_rScrLayout_c70 o1 rTot] at c690_0
  have hKeep {M D} {r : RouterReg M D dLayout} (hd : ∀ i j, r i ≠ rCoinExt kExt hk j) (γ) (β) (i) :
      β (rTot (r i)) = togBits_c70 rC γ β (rTot (r i)) :=
    (DynCircExt.writeReg_apply_of_not_mem _ _ _ _ fun ⟨j, hj⟩ ↦
        hd i j (rTot.wires.injective hj.symm)).symm
  have hW (Z) : (rTot.embedUnitary o1.uLocal).1 *
      ((rTot.compose rScrLayout).basisOutcomeProjector 0 * Z) =
      W_cl.1 * ((rTot.compose rScrLayout).basisOutcomeProjector 0 * Z) := by
    rw [← Matrix.mul_assoc, ← wStage1Clean_mul_rScrLayout_c70 o1 rTot, Matrix.mul_assoc]
  exact ⟨lift_sup_pScrExt hk rTot cU (fun γ β ↦ validZeroGatedSorted_congr_c70 rE (hKeep dE γ β))
      (fun Z hAbs ↦
          hW Z ▸ (routerChain_sorted_of_validMuxD1Stage2Regs hRegs hSort rTot o1 hAbs).1) hX,
    by simpa only [Matrix.mul_assoc] using lift_sup_pScrExt hk rTot
        (L := (uRouterSwapConj rE).1 * W_cl.1) (fun γ ↦ (cR dE γ).mul_left (cU γ))
        (fun γ β ↦ validZeroGatedSorted_congr_c70 rN (hKeep dN γ β)) (fun _ h ↦ by
          simpa only [hW, Matrix.mul_assoc] using
            (routerChain_sorted_of_validMuxD1Stage2Regs hRegs hSort rTot o1 h).2.1) hX,
    by simpa only [Matrix.mul_assoc] using lift_eq_of_pScrExt_c70 hk rTot
        (L₁ := (uRouterSwapConj rN).1 * (uRouterSwapConj rE).1 * W_cl.1) (L₂ := Wnh_cl.1)
        (by simpa only [Matrix.mul_assoc] using cEq0)
            (fun γ ↦ ((cR dN γ).mul_left (cR dE γ)).mul_left (cU γ)) cWnh hX,
    by simpa only [Matrix.mul_assoc] using lift_eq_of_pScrExt_c70 hk rTot
        (L₁ := rW.basisOutcomeProjector 0 * Wnh_cl.1) (L₂ := Wnh_cl.1)
        (by simpa only [Matrix.mul_assoc] using c690_0) (fun γ ↦ Commute.mul_left (cP γ)
            (cWnh γ)) cWnh hX⟩
end QuantumComputation.Specs.PhotochemistrySolution.Sub5885

namespace QuantumComputation.Specs.PhotochemistrySolution.PortBDualBellUnld
set_option exponentiation.threshold 8192
open scoped ComplexOrder MatrixOrder Circuit.Notation
open HermitianMat PhotochemistrySolution.XMeasUnld PhotochemistrySolution.SelectCompactAnc
  PhotochemistrySolution.Stage2QromMux
open PhotochemistrySolution.Sub5885
open _root_.DynamicCircuit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt hiding bit_cases
  eval_seq_mulVec ket ket_CNOT ket_TOFF ket_X ket_projector_one ket_projector_zero localIdx
  matrix_ext_ket qAssign_obs_map_val

section Block2
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB (ket)
attribute [local irreducible] systemQubits_frozen SelectCompactAnc.ancWOfScr uRouterSwapConj

theorem inKetPred_cleanScr_of_proj {n : ℕ} (rTot : QRegister dLayout n) {X : Operator (2 ^ n)}
    (hX : (rTot.compose rScrLayout).basisOutcomeProjector 0 * X = X) (ξ : BitAssignment n) :
    inKetPred (fun η ↦ CleanScr (fun i ↦ η (rTot i))) (X.mulVec (KinB.ket ξ)) := fun η hnz ↦ by
  by_contra hnot
  change ¬ ∀ i : Fin scrLLayout, η ((rTot.compose rScrLayout) i) = 0 at hnot
  have heq := congrFun (congrArg (fun M ↦ M.mulVec (KinB.ket ξ)) hX) ((basisBitsEquiv n).symm η)
  rw [← Matrix.mulVec_mulVec, proj_zero_vec_entry (rTot.compose rScrLayout) _ η,
      ite_eq_right hnot] at heq
  exact hnz heq.symm

theorem routedStage1_scr_zero {decodeCoin : Fin (2 ^ 41) → ZeroNEremSector}
    {α : BitAssignment dLayout} (hScr : CleanScr α)
    (c : Fin (2 ^ 41)) (z : BitAssignment 41) (m : Fin scrLLayout)
        (hmb : m.val < 65 ∨ 105 ≤ m.val) :
    routedStage1 decodeCoin α c z (rScrLayout m) = 0 := by
  have _ : m.val < 1565 := m.isLt
  unfold routedStage1 routedStage0
  rw [DynCircExt.writeReg_apply_of_not_mem _ rOut40Layout _ _ fun ⟨q, hq⟩ ↦
      ((fun _ ↦ by omega)
          ((val_rOut40Layout q).symm.trans ((congrArg Fin.val hq).trans (val_rScrLayout m)))),
    DynCircExt.writeReg_apply_of_not_mem _ rLcu82Layout _ _ fun ⟨l, hl⟩ ↦
      ((fun (_ : _ ∧ _) ↦ by omega)
          ⟨l.isLt, (val_rLcu82Layout l).symm.trans ((congrArg (·.1) hl).trans (val_rScrLayout m))⟩)]
  exact hScr m

theorem routerChain_sharedPortB_of_validMuxD1Stage2Regs {n wIn : ℕ}
    {decodeCoin : Fin (2 ^ 41) → ZeroNEremSector}
    {rNuc : RouterReg 47 6 dLayout} {rElec : RouterReg 187 8 dLayout}
        (hRegs : ValidMuxD1Stage2Regs rNuc rElec)
    (hSort : SortedZeroNEremCoin decodeCoin) (rTot : QRegister dLayout n)
        (o1 : Stage1ZeroNEremLayout wIn decodeCoin) {X : Operator (2 ^ n)}
        (hX : (rTot.compose rScrLayout).basisOutcomeProjector 0 * X = X) :
    SupportedOn (SharedPortBInput rTot (rTot.compose rNuc) (rTot.compose rElec))
        ((rTot.embedUnitary o1.uLocal).1 * X) := by
  refine supportedOn_of_inKetPred fun ξ ↦ ?_
  rw [← Matrix.mulVec_mulVec]
  refine inKetPred_mulVec (rTot.embedUnitary o1.uLocal).1 (fun η hScr ↦ ?_)
      (inKetPred_cleanScr_of_proj rTot hX ξ)
  rw [w1Ket rTot o1 η hScr]
  let α := fun i ↦ η (rTot i)
  let c := outerCoinOf82 (fun i ↦ α (rLcu82Layout i))
  let z := innerBitsOf82 (fun i ↦ α (rLcu82Layout i))
  let δ₁ := routedStage1 decodeCoin α c z
  have hOut1 (j : Fin 40) : δ₁ (rOut40Layout j) = outMaskBits40 (decodeCoin c) j :=
    DynCircExt.writeReg_apply_reg _ rOut40Layout _ j
  have hSH := zeroNEremOutMask_router_sorted hSort c δ₁ hOut1
  have hNN1 := zeroNEremOutMask_isNN_and_oneHot c δ₁ hOut1
  obtain ⟨hVN, hSameE, hVE2, _, _, _⟩ := validRouter_stage1 (decodeCoin := decodeCoin) hScr c z
  have hValEC : ValidZeroGatedSortedRouterInput rElec δ₁ := by
    obtain ⟨h1, h2, hi1, hi2, hBL, hBH, hA, hB, _⟩ := hRegs.rolesElec
    refine ⟨⟨by simpa only [δ₁, α, h1, h2, rRawHas2, rHas1, hSameE] using hVE2.1,
      by simpa only [δ₁, α, h1, hi1, rHas1, hSameE, idxValD_congr_gen fun _ ↦
           hSameE _] using hVE2.2.1,
      by simpa only [δ₁, α, h2, hi2, rRawHas2, hSameE, idxValD_congr_gen fun _ ↦
           hSameE _] using hVE2.2.2.1,
      fun b ↦ by simpa only [δ₁, α, congrFun hBL, congrFun hBH, congrFun hA, congrFun hB,
        rBufLo, rBufHi, rHA, rHB, hSameE] using hVE2.2.2.2.1 b, fun w hw ↦ ?_⟩,
      by simpa only [h1, congrFun hi1] using hSH.2.2.2.1,
          by simpa only [h2, congrFun hi2] using hSH.2.2.2.2.1,
      by simpa only [h2, hi1, hi2] using hSH.2.2.2.2.2⟩
    rcases Finset.mem_image.mp hw with ⟨i, hi, rfl⟩
    have ⟨_, _⟩ : _ ∧ _ :=
        ⟨(show basePub 187 8 = 4602 from rfl) ▸ (Finset.mem_filter.mp hi).2,
        i.isLt.trans_eq hEW5056⟩
    obtain ⟨m, hm, hmb⟩ := hRegs.privElec ⟨i.val - 4602, by omega⟩
    exact (congrArg δ₁ ((congrArg rElec.wires (Fin.ext (by dsimp; omega) :
      i = ⟨4602 + (i.val - 4602), privIdx_lt ⟨i.val - 4602, by omega⟩⟩)).trans hm)).trans
      (routedStage1_scr_zero hScr c z m hmb)
  have hValNC : ValidZeroGatedSortedRouterInput rNuc δ₁ := by
    obtain ⟨h1, h2, hi1, hi2, hBL, hBH, hA, hB, _⟩ := hRegs.rolesNuc
    refine ⟨⟨by simpa only [δ₁, h1, h2] using hVN.1, by simpa only [δ₁, h1, hi1] using hVN.2.1,
      by simpa only [δ₁, h2, hi2] using hVN.2.2.1,
      fun b ↦
          by simpa only [δ₁, congrFun hBL, congrFun hBH, congrFun hA,
               congrFun hB] using hVN.2.2.2.1 b,
      fun w hw ↦ ?_⟩, by simpa only [h1, congrFun hi1] using hSH.1,
      by simpa only [h2, congrFun hi2] using hSH.2.1, by simpa only [h2, hi1, hi2] using hSH.2.2.1⟩
    rcases Finset.mem_image.mp hw with ⟨i, hi, rfl⟩
    have ⟨_, _⟩ : _ ∧ _ :=
        ⟨(show basePub 47 6 = 1238 from rfl) ▸ (Finset.mem_filter.mp hi).2, i.isLt.trans_eq hNW1394⟩
    obtain ⟨m, hrm, _⟩ := hRegs.privNuc ⟨i.val - 1238, by omega⟩
    exact (congrArg δ₁ ((congrArg rNuc.wires (Fin.ext (by dsimp; omega) :
      i = ⟨1238 + (i.val - 1238), nucPrivIdx_lt ⟨i.val - 1238, by omega⟩⟩)).trans hrm)).trans
      (routedStage1_scr_zero hScr c z m (by omega))
  have hRawN := DynCircExt.writeReg_apply_reg η rTot δ₁ (rRawHas2 rNuc)
  have hRawE := DynCircExt.writeReg_apply_reg η rTot δ₁ (rRawHas2 rElec)
  exact inKetPred_ket ⟨validZeroGatedSorted_compose_writeReg rTot rElec η δ₁ hValEC,
      validZeroGatedSorted_compose_writeReg rTot rNuc η δ₁ hValNC, fun p ↦
      (DynCircExt.writeReg_apply_reg η rTot δ₁ (cHiNSub p)).trans
      (routedStage1_scr_zero hScr c z ⟨371 + p.val, cHiNSub_scrIdx_lt p⟩
          (Or.inr (by omega : 105 ≤ 371 + p.val))),
          (DynCircExt.writeReg_apply_reg η rTot δ₁ (wPotIsNN rPot0Layout)).trans
      ((hNN1.1.trans (congrArg δ₁ hRegs.rolesNuc.2.1.symm)).trans hRawN.symm), fun ho ↦
          hRawE.trans ((congrArg δ₁ hRegs.rolesElec.2.1).trans
          (hNN1.2 ((congrArg δ₁ hRegs.rolesNuc.2.1.symm).trans (hRawN.symm.trans ho))))⟩

theorem routerChain_sharedPortB_ext {kExt w1 n : ℕ}
    {decodeCoin : Fin (2 ^ 41) → ZeroNEremSector}
    {rNuc : RouterReg 47 6 dLayout} {rElec : RouterReg 187 8 dLayout}
    (hk : kExt ≤ 72) (hRegs : ValidMuxD1Stage2Regs rNuc rElec)
    (dN : ∀ i j, rNuc i ≠ rCoinExt kExt hk j)
    (dE : ∀ i j, rElec i ≠ rCoinExt kExt hk j)
    (hSort : SortedZeroNEremCoin decodeCoin)
    (rTot : QRegister dLayout n) (o1 : Stage1ZeroNEremLayout w1 decodeCoin)
    {X : Operator (2 ^ n)}
    (hX : (rTot.compose (rScrExt kExt hk)).basisOutcomeProjector 0 * X = X) :
    let W_cl := rTot.embedUnitary (uStage1Clean_c70 decodeCoin)
    let Wnh_cl := rTot.embedUnitary (wNoHad (uStage1Clean_c70 decodeCoin))
    SupportedOn (SharedPortBInput rTot (rTot.compose rNuc) (rTot.compose rElec))
        (W_cl.1 * X) ∧ SupportedOn (ValidZeroGatedSortedRouterInput (rTot.compose rElec))
        (W_cl.1 * X) ∧
    SupportedOn (ValidZeroGatedSortedRouterInput (rTot.compose rNuc))
        ((uRouterSwapConj (rTot.compose rElec)).1 * (W_cl.1 * X)) ∧
    (uRouterSwapConj (rTot.compose rNuc)).1 * ((uRouterSwapConj (rTot.compose rElec)).1 *
        (W_cl.1 * X)) = Wnh_cl.1 * X ∧ (rTot.compose rClean690Layout).basisOutcomeProjector 0 *
        (Wnh_cl.1 * X) = Wnh_cl.1 * X := by
  intro W_cl Wnh_cl
  let rC := rTot.compose (rCoinExt kExt hk)
  obtain ⟨hSE, hSN, hEq, h690⟩ := routerChain_sorted_validMuxD1_ext hk hRegs dN dE hSort rTot o1 hX
  have cU (γ) : W_cl.1 * (uTogGen_c70 rC γ).1 = (uTogGen_c70 rC γ).1 * W_cl.1 := by
    simpa only [embedUnitary_uTogLocal_c70] using wStage1Clean_comm_rCoinExt_c70 decodeCoin hk rTot
        (uTogLocal_c70 γ)
  have wrK {γ β} {w : Wire dLayout} (hd : ∀ j, w ≠ rCoinExt kExt hk j) : β (rTot w) =
      togBits_c70 rC γ β (rTot w) :=
    (DynCircExt.writeReg_apply_of_not_mem _ _ _ _ fun ⟨j, hj⟩ ↦
        hd j (rTot.wires.injective hj.symm)).symm
  exact ⟨lift_sup_pScrExt hk rTot cU (fun _ _ hβ ↦ sharedPortBInput_congr rTot (rTot.compose rNuc)
      (rTot.compose rElec)
      (fun i ↦ wrK (dE i)) (fun i ↦ wrK (dN i)) (fun p ↦ wrK (cHiNSub_disj_rCoinExt hk p))
      (wrK fun j e ↦ ((fun (_ : _ ∧ _) ↦ by omega)
        ⟨j.isLt,
            val_wPotIsNN_rPot0Layout.symm.trans ((congrArg Fin.val e).trans (val_rCoinExt hk j))⟩))
            hβ)
      (fun _ hAbs ↦
          by simpa only [← Matrix.mul_assoc, ← wStage1Clean_mul_rScrLayout_c70 o1 rTot] using
        routerChain_sharedPortB_of_validMuxD1Stage2Regs hRegs hSort rTot o1 hAbs) hX, hSE, hSN, hEq,
            h690⟩
end Block2

section Block34
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB hiding writeReg
  writeReg_apply_of_not_mem ket ket_X ket_CNOT ket_TOFF matrix_ext_ket bitSign eval_seq_mulVec
open _root_.QuantumComputation.Specs.PhotochemistrySolution.QubitizationWalkSem hiding bitSign
  bitSign_add bitSign_mul_self sqrtHalf sqrtHalf_mul_sqrtHalf star_sqrtHalf
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SplitRouterSeqBell26k hiding ket
  matrix_ext_ket
attribute [local semireducible] PhotochemistrySolution.DynQromUncompA.remeasureIf
  PhotochemistrySolution.DynQromUncompA.wrapDyn
  DynQromUncompA.fwdCirc ComputeProg.ValidProg ComputeProg.finalClean ComputeProg.fwdBits
  SplitBellVecCleanStep.cnotFanoutCirc SplitBellVecCleanStep.czFanoutCirc
      SplitBellVecCleanStep.specFanoutCopyCirc
  SplitBellVecCleanStep.bellZHalf1Dyn SplitBellVecCleanStep.bellXHalf1Dyn
  SplitBellVecCleanStep.bellZHalfVecDyn SplitBellVecCleanStep.bellXHalfVecDyn

theorem routerCtrlSet_pubIdx_nuc {n : ℕ} {rN : RouterReg 47 6 n} {u : Wire n}
    (h : RouterCtrlSet rN u) : ∃ i
    : Fin (routerWidth 47 6), i.val < 14 ∧ u = rN i := by
  rcases h with rfl | rfl | ⟨d, rfl⟩ | ⟨d, rfl⟩ <;> first
    | exact ⟨⟨0, rw_lt0 47 6⟩, by dsimp [routerWidth]; omega, rfl⟩
    | exact ⟨⟨1, rw_lt1 47 6⟩, by dsimp [routerWidth]; omega, rfl⟩
    | exact ⟨⟨2 + d.val, rw_ltIdx1 d⟩, (fun _ ↦ by dsimp; omega) d.isLt, rfl⟩
    | exact ⟨⟨2 + 6 + d.val, rw_ltIdx2 d⟩, (fun _ ↦ by dsimp; omega) d.isLt, rfl⟩

theorem routerCtrlSet_pubIdx_elec {n : ℕ} {rE : RouterReg 187 8 n} {u : Wire n}
    (h : RouterCtrlSet rE u) : ∃ j
    : Fin (routerWidth 187 8), j.val < 18 ∧ u = rE j := by
  rcases h with rfl | rfl | ⟨d, rfl⟩ | ⟨d, rfl⟩ <;> first
    | exact ⟨⟨0, rw_lt0 187 8⟩, by dsimp [routerWidth]; omega, rfl⟩
    | exact ⟨⟨1, rw_lt1 187 8⟩, by dsimp [routerWidth]; omega, rfl⟩
    | exact ⟨⟨2 + d.val, rw_ltIdx1 d⟩, (fun _ ↦ by dsimp; omega) d.isLt, rfl⟩
    | exact ⟨⟨2 + 8 + d.val, rw_ltIdx2 d⟩, (fun _ ↦ by dsimp; omega) d.isLt, rfl⟩

theorem SharedPortBWiring.modN_ne_modE {n : ℕ} {rN : RouterReg 47 6 n} {rE : RouterReg 187 8 n}
    {cHiN : Fin 47 → Wire n}
    (w : SharedPortBWiring rN rE cHiN) {u v : Wire n} (hu : AllPlaneMod rN u)
        (hv : AllPlaneMod rE v) : u ≠ v :=
  let ⟨_, _, hi, e1⟩ := allPlaneMod_pubIdx_nuc hu
  let ⟨_, _, hj, e2⟩ := allPlaneMod_pubIdx_elec hv
  e1 ▸ e2 ▸ w.pubN_ne_pubE hi hj

theorem SharedPortBWiring.modN_ne_hdrE {n : ℕ} {rN : RouterReg 47 6 n} {rE : RouterReg 187 8 n}
    {cHiN : Fin 47 → Wire n}
    (w : SharedPortBWiring rN rE cHiN) {u v : Wire n} (hu : AllPlaneMod rN u)
        (hv : RouterCtrlSet rE v) : u ≠ v :=
  let ⟨_, _, hi, e1⟩ := allPlaneMod_pubIdx_nuc hu
  let ⟨_, hj, e2⟩ := routerCtrlSet_pubIdx_elec hv
  e1 ▸ e2 ▸ w.pubN_ne_pubE hi (by omega)

theorem SharedPortBWiring.hBC_NE {n : ℕ} {rN : RouterReg 47 6 n} {rE : RouterReg 187 8 n}
    {cHiN : Fin 47 → Wire n}
    (w : SharedPortBWiring rN rE cHiN) (k : Fin 24) (i : Fin (47 + 187)) : rBufHi rE k ≠
        appendFin cHiN (rCtrlLo rE) i := by
  rcases appendFin_eq i with ⟨p, rfl⟩ | ⟨q, rfl⟩
  · rw [appendFin_castAdd]
    exact fun e ↦ w.cHiN_notModE p (e ▸ ⟨k, Or.inr (Or.inl rfl)⟩)
  · rw [appendFin_natAdd]
    exact rr_ne rE (by have := k.isLt; have := q.isLt; unfold basePub; dsimp; omega)

theorem SharedPortBWiring.hBT_NE_all {n : ℕ} {rN : RouterReg 47 6 n} {rE : RouterReg 187 8 n}
    {cHiN : Fin 47 → Wire n}
    (w : SharedPortBWiring rN rE cHiN) (k₁ k₂ : Fin 24) (i : Fin (47 + 187)) :
    rBufHi rE k₁ ≠ appendFin (fun p ↦ pSys (planeOfRouter rN k₂) p)
        (fun q ↦ pSys (planeOfRouter rE k₂) q) i := by
  rcases appendFin_eq i with ⟨p, rfl⟩ | ⟨q, rfl⟩
  · rw [appendFin_castAdd]
    exact (w.modN_ne_modE ⟨k₂, Or.inr (Or.inr (Or.inr (Or.inr ⟨p, rfl⟩)))⟩
        ⟨k₁, Or.inr (Or.inl rfl)⟩).symm
  · rw [appendFin_natAdd]
    exact (hne_fixed_router_sys rE k₁ k₂ q).2.1

theorem SharedPortBWiring.hCT_NE_all {n : ℕ} {rN : RouterReg 47 6 n} {rE : RouterReg 187 8 n}
    {cHiN : Fin 47 → Wire n}
    (w : SharedPortBWiring rN rE cHiN) (k : Fin 24) (i j : Fin (47 + 187)) :
    appendFin cHiN (rCtrlLo rE) i ≠ appendFin (fun p ↦ pSys (planeOfRouter rN k) p)
        (fun q ↦ pSys (planeOfRouter rE k) q) j := by
  rcases appendFin_eq i with ⟨p, rfl⟩ | ⟨q, rfl⟩ <;> rcases appendFin_eq j with ⟨p', rfl⟩ | ⟨q',
      rfl⟩ <;>
    simp only [appendFin_castAdd, appendFin_natAdd]
  · exact fun e ↦ w.cHiN_notModN p (e.symm ▸ ⟨k, .inr (.inr (.inr (.inr ⟨p', rfl⟩)))⟩)
  · exact fun e ↦ w.cHiN_notModE p (e.symm ▸ ⟨k, .inr (.inr (.inr (.inr ⟨q', rfl⟩)))⟩)
  · simpa only [planeOfRouter_sys] using w.ctrlE_ne_sysN q p' k
  · exact hne_rCtrlLo_pSys rE k q q'

theorem SharedPortBWiring.hBTs_NE {n : ℕ} {rN : RouterReg 47 6 n} {rE : RouterReg 187 8 n}
    {cHiN : Fin 47 → Wire n}
    (w : SharedPortBWiring rN rE cHiN) (b : Fin 24) (i : Fin (47 + 187)) :
    rBufHi rE b ≠ appendFin (fun p ↦ rSys rN p b) (fun q ↦ rSys rE q b) i := by
  simpa only [planeOfRouter_sys] using w.hBT_NE_all b b i

theorem SharedPortBWiring.hBC_N {n : ℕ} {rN : RouterReg 47 6 n} {rE : RouterReg 187 8 n}
    {cHiN : Fin 47 → Wire n}
    (w : SharedPortBWiring rN rE cHiN) (k : Fin 24) (p : Fin 47) : rBufHi rE k ≠ cHiN p :=
  fun e ↦ w.cHiN_notModE p (e ▸ ⟨k, Or.inr (Or.inl rfl)⟩)
def pDecHiNOn {n : ℕ} (rN : RouterReg 47 6 n) (rE : RouterReg 187 8 n) (cHiN : Fin 47 → Wire n)
    (w : SharedPortBWiring rN rE cHiN) : ComputeProg n :=
    oneHotPosZeroGated sorted47_hD1 sorted47_hMlo (fun d hdlt ↦
    sorted47_hPow d (sortedUnload_lt_of_sub hdlt)) (rRawHas2 rN)
    (rIdx2 rN) cHiN w.rawN_ne_cHiN w.idx2N_ne_cHiN w.cHiN_inj
def pDecHiESorted {n : ℕ} (rE : RouterReg 187 8 n) : ComputeProg n :=
    oneHotPosZeroGated sorted187_hD1 sorted187_hMlo (fun d hdlt ↦
    sorted187_hPow d (sortedUnload_lt_of_sub hdlt)) (rRawHas2 rE) (rIdx2 rE) (rCtrlLo rE)
    (hne_rRawHas2_ctrlLo rE) (hne_rIdx2_ctrlLo rE) (hne_prep_dec rE).2.2.1
def pDecLoNSorted {n : ℕ} (rN : RouterReg 47 6 n) : ComputeProg n :=
  oneHotZeroGated (by decide : 0 < 47) sorted47_hPow (rHas1 rN) (rIdx1 rN) (rCtrlLo rN)
    (hne_prep_dec rN).1
    (fun d p ↦ rr_ne rN (by have := d.isLt; have := p.isLt; unfold basePub; dsimp; omega))
    (hne_prep_dec rN).2.2.1
def pDecLoESorted {n : ℕ} (rE : RouterReg 187 8 n) : ComputeProg n :=
  oneHotZeroGated (by decide : 0 < 187) sorted187_hPow (rHas1 rE) (rIdx1 rE) (rCtrlLo rE)
    (hne_prep_dec rE).1
    (fun d q ↦ rr_ne rE (by have := d.isLt; have := q.isLt; unfold basePub; dsimp; omega))
    (hne_prep_dec rE).2.2.1
theorem spec_pDecHiNOn {n : ℕ} (rN : RouterReg 47 6 n) (rE : RouterReg 187 8 n)
    (cHiN : Fin 47 → Wire n)
    (w : SharedPortBWiring rN rE cHiN) (δ : BitAssignment n) (hC0 : ∀ p : Fin 47, δ (cHiN p) = 0)
        (hP : UnloadHiPred rN δ) :
    (∀ p : Fin 47, (pDecHiNOn rN rE cHiN w).fwdBits δ (cHiN p) = cOfSortedHi rN δ p) ∧
        (∀ u : Wire n, (∀ p : Fin 47, u ≠ cHiN p) → (pDecHiNOn rN rE cHiN w).fwdBits δ u = δ u) ∧
    AtMostOneCtrl cHiN ((pDecHiNOn rN rE cHiN w).fwdBits δ) := by
  obtain ⟨hC, hOth⟩ := fwdBits_oneHotPosZeroGated sorted47_hD1 sorted47_hMlo (by decide)
    (fun d hdlt ↦ sorted47_hPow d (sortedUnload_lt_of_sub hdlt)) (rRawHas2 rN) (rIdx2 rN) cHiN
    w.rawN_ne_cHiN w.idx2N_ne_cHiN w.cHiN_inj δ hP.1 hP.2.1 hP.2.2 hC0
  refine ⟨hC, hOth, (DynCircExt.bit_cases (δ (rRawHas2 rN))).imp
    (fun hz p ↦ (hC p).trans (by rw [hz]; exact ite_self 0)) fun ho ↦
      ⟨⟨idxValD (rIdx2 rN) δ, hP.1⟩, (hC _).trans (by dsimp; rw [ite_eq_left rfl, ho]),
        fun p hp ↦ (hC p).trans (ite_eq_right fun e ↦ hp (Fin.ext e.symm))⟩⟩

theorem progSupportedIn_pDecHiNOn {n : ℕ} (rN : RouterReg 47 6 n) (rE : RouterReg 187 8 n)
    (cHiN : Fin 47 → Wire n)
    (w : SharedPortBWiring rN rE cHiN) :
    ProgSupportedIn (fun u ↦ RouterCtrlSet rN u ∨ ∃ p : Fin 47, u = cHiN p) (pDecHiNOn rN rE cHiN w)
        := progSupportedIn_oneHotPosZeroGated sorted47_hD1 sorted47_hMlo _ _ _ _ _ _ _
    (Or.inl (Or.inr (Or.inl rfl))) (fun d ↦ Or.inl (Or.inr (Or.inr (Or.inr ⟨d, rfl⟩))))
        (fun p ↦ Or.inr ⟨p, rfl⟩)

theorem progSupportedIn_pDecHiESorted {n : ℕ} (rE : RouterReg 187 8 n)
    : ProgSupportedIn (fun u ↦ RouterCtrlSet rE u ∨ ∃ q : Fin 187, u = rCtrlLo rE q)
        (pDecHiESorted rE) :=
  progSupportedIn_oneHotPosZeroGated sorted187_hD1 sorted187_hMlo _ _ _ _ _ _ _
      (Or.inl (Or.inr (Or.inl rfl)))
    (fun d ↦ Or.inl (Or.inr (Or.inr (Or.inr ⟨d, rfl⟩)))) (fun q ↦ Or.inr ⟨q, rfl⟩)

theorem dynWires_bellZHalfVecDyn_gen {Var : Type} {M n : ℕ} {S : Wire n → Prop} (v : Var) (m : ℕ)
    (qB qH : Fin m → Wire n)
    (wC : Fin M → Wire n) (wT : Fin m → Fin M → Wire n) (hBH : ∀ k, qB k ≠ qH k)
        (hct : ∀ k p, wC p ≠ wT k p)
    (hB : ∀ k, S (qB k)) (hH : ∀ k, S (qH k)) (hC : ∀ p, S (wC p)) (hT : ∀ k p, S (wT k p)) :
        DynWires S (bellZHalfVecDyn v M m qB qH wC wT hBH hct) := by
  have cw2 {c t : Wire n} {h : c ≠ t} (hc : S c) (ht : S t) : CircWires S (Circuit.CNOT c t h) :=
    fun i ↦ by fin_cases i <;> assumption
  have hCF (K) : ∀ (wc wt : Fin K → Wire n) (h : ∀ p, wc p ≠ wt p), (∀ p, S (wc p)) →
      (∀ p, S (wt p)) → CircWires S (SplitBellVecCleanStep.cnotFanoutCirc K wc wt h) := by
    induction K with
    | zero => exact fun _ _ _ _ _ ↦ trivial
    | succ K ih => exact fun _ _ _ hc ht ↦
        ⟨ih _ _ _ (fun p ↦ hc p.castSucc) (fun p ↦ ht p.castSucc), cw2 (hc _) (ht _)⟩
  induction m with
  | zero => trivial
  | succ m ih =>
        exact ⟨⟨cw2 (hB _) (hH _), fun _ ↦ hH _, ⟨fun _ ↦ hH _, hCF M wC (wT _) (hct _) hC (hT _)⟩,
        trivial⟩,
      ih (fun k ↦ qB k.castSucc) (fun k ↦ qH k.castSucc) (fun k ↦ wT k.castSucc)
          (fun k ↦ hBH k.castSucc)
        (fun k ↦ hct k.castSucc) (fun k ↦ hB k.castSucc) (fun k ↦ hH k.castSucc)
            (fun k ↦ hT k.castSucc)⟩

theorem dynWires_bellXHalfVecDyn_gen {Var : Type} {M n : ℕ} {S : Wire n → Prop} (v : Var) (m : ℕ)
    (qB : Fin m → Wire n)
    (wC : Fin M → Wire n) (wT : Fin m → Fin M → Wire n)
    (hct : ∀ k p, wC p ≠ wT k p) (hB : ∀ k, S (qB k)) (hC : ∀ p, S (wC p))
        (hT : ∀ k p, S (wT k p)) : DynWires S (bellXHalfVecDyn v M m qB wC wT hct) := by
  have cw2 {c t : Wire n} {h : c ≠ t} (hc : S c) (ht : S t) : CircWires S (Circuit.CNOT c t h) :=
    fun i ↦ by fin_cases i <;> assumption
  have hZF (K) : ∀ (wc wt : Fin K → Wire n) (h : ∀ p, wc p ≠ wt p), (∀ p, S (wc p)) →
      (∀ p, S (wt p)) → CircWires S (SplitBellVecCleanStep.czFanoutCirc K wc wt h) := by
    induction K with
    | zero => exact fun _ _ _ _ _ ↦ trivial
    | succ K ih => exact fun _ _ _ hc ht ↦
        ⟨ih _ _ _ (fun p ↦ hc p.castSucc) (fun p ↦ ht p.castSucc), ⟨fun _ ↦ ht _, cw2 (hc _)
            (ht _), fun _ ↦ ht _⟩⟩
  induction m with
  | zero => trivial
  | succ m ih =>
        exact ⟨⟨fun _ ↦ hB _, fun _ ↦ hB _, ⟨fun _ ↦ hB _, hZF M wC (wT _) (hct _) hC (hT _)⟩,
        trivial⟩,
      ih (fun k ↦ qB k.castSucc) (fun k ↦ wT k.castSucc) (fun k ↦ hct k.castSucc)
          (fun k ↦ hB k.castSucc) (fun k ↦ hT k.castSucc)⟩
end Block34
end QuantumComputation.Specs.PhotochemistrySolution.PortBDualBellUnld
end
end

noncomputable section
namespace QuantumComputation.Specs.PhotochemistrySolution.PortBStage5Merged
open Operator QProg Matrix HermitianMat Circuit Qubit PrimitiveGate QuantumComputation.Specs
  PhotochemistrySolution.KetSupport
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
open PhotochemistrySolution PhotochemistrySolution.XMeasUnld
  PhotochemistrySolution.SelectCompactAnc PhotochemistrySolution.SplitRouter47_187
open PhotochemistrySolution.UnembedO3Bridge PhotochemistrySolution.SelectOracles
  PhotochemistrySolution.RouterSelectWiringA PhotochemistrySolution.RouterSelectWiringB
open PhotochemistrySolution.ProviderCore PhotochemistrySolution.Stage12Compact
  PhotochemistrySolution.ZeroNEremSpec PhotochemistrySolution.PotSelectWiring
open PhotochemistrySolution.Stage2Xor84 PhotochemistrySolution.Stage2QromMux
  PhotochemistrySolution.Stage2PotUnld PhotochemistrySolution.Stage2ElecFirst
open PhotochemistrySolution.SortedRouterSpec PhotochemistrySolution.Coin70Lift
  PhotochemistrySolution.Sub5885MuxD1 PhotochemistrySolution.Sub5885
open PhotochemistrySolution.PortBDualBellUnld PhotochemistrySolution.PotOraclePortBStream
open _root_.DynamicCircuit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt hiding ket matrix_ext_ket
  qAssign_obs_map_val ket_projector_zero ket_projector_one ket_X ket_CNOT ket_TOFF eval_seq_mulVec
  bit_cases localIdx
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB hiding writeReg
  writeReg_apply_of_not_mem ket ket_X ket_CNOT ket_TOFF matrix_ext_ket bitSign eval_seq_mulVec
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SplitRouterSeqBell26k hiding ket
  matrix_ext_ket
open scoped ComplexOrder MatrixOrder Circuit.Notation
attribute [local irreducible] systemQubits_frozen SelectCompactAnc.ancWOfScr uRouterSwapConj
/- ## Section 6A: Tight Footprints, `pUnloadSharedHiMerged`, Counts, & `DynWires` -/
/--
Tight router wire footprint on `rN` (`RouterReg 47 6`) touched by `pHBZMerge24Dyn` and
`pSharedPortBStage5UnloadMerged`: public wires `< 1238` plus `rCtrlLo rN` (`1256..1302`).
-/
def UnloadFootprintN {n : ℕ} (r : RouterReg 47 6 n) (w : Wire n) : Prop :=
  ∃ i : Fin (routerWidth 47 6), w = r i ∧ (i.val < basePub 47 6 ∨ (1256 ≤ i.val ∧ i.val < 1303))
/--
Tight router wire footprint on `rE` (`RouterReg 187 8`) touched by `pHBZMerge24Dyn` and
`pSharedPortBStage5UnloadMerged`: public wires `< 4602` plus `rCtrlLo rE` (`4624..4810`),
excluding `nFlag` (`4602..4607`).
-/
def UnloadFootprintE {n : ℕ} (r : RouterReg 187 8 n) (w : Wire n) : Prop :=
    ∃ j : Fin (routerWidth 187 8), w = r j ∧ (j.val < basePub 187 8 ∨ (4624 ≤ j.val ∧ j.val < 4811))
/- ## Section 6B: Ket Evaluation of `uSharedHiInnerMerged` & `uSharedHiConjMerged` -/
theorem sysNE_inj {n : ℕ} {rN : RouterReg 47 6 n} {rE : RouterReg 187 8 n} {cHiN : Fin 47 → Wire n}
    (w : SharedPortBWiring rN rE cHiN) (k : Fin 24) :
    Function.Injective (appendFin (fun p ↦ pSys (planeOfRouter rN k) p)
        (fun q ↦ pSys (planeOfRouter rE k) q)) := by
  have inj {M D} (r : RouterReg M D n) : Function.Injective (pSys (planeOfRouter r k)) :=
      fun _ _ e ↦ Fin.ext <| by
    rw [planeOfRouter_sys, planeOfRouter_sys] at e
    exact ((fun _ ↦ by dsimp at *; omega) (congrArg Fin.val (r.wires.injective e)))
  exact appendFin_inj (inj rN) (inj rE) fun p q ↦
    w.modN_ne_modE ⟨k, .inr (.inr (.inr (.inr ⟨p, rfl⟩)))⟩ ⟨k, .inr (.inr (.inr (.inr ⟨q, rfl⟩)))⟩

theorem sysNE_plane_disj {n : ℕ} {rN : RouterReg 47 6 n} {rE : RouterReg 187 8 n}
    {cHiN : Fin 47 → Wire n}
    (w : SharedPortBWiring rN rE cHiN) (k₁ k₂ : Fin 24) (hne : k₁ ≠ k₂) : ∀ i j : Fin (47 + 187),
      appendFin (fun p ↦ pSys (planeOfRouter rN k₁) p) (fun q ↦ pSys (planeOfRouter rE k₁) q) i ≠
        appendFin (fun p ↦ pSys (planeOfRouter rN k₂) p)
          (fun q ↦ pSys (planeOfRouter rE k₂) q) j := by
  have mS {M D} {r : RouterReg M D n} {k p u} (e : u = pSys (planeOfRouter r k) p) :
      PlaneModSet (planeOfRouter r k) u := Or.inr (Or.inr (Or.inr (Or.inr ⟨p, e⟩)))
  refine appendFin_cases (fun p₁ ↦ appendFin_cases (fun p₂ ↦ ?_) (fun q₂ ↦ ?_))
    (fun q₁ ↦ appendFin_cases (fun p₂ ↦ ?_) (fun q₂ ↦ ?_))
  · simpa [appendFin_castAdd] using fun e ↦ planeModDisj rN hne _ (mS rfl) (mS e)
  · simpa [appendFin_castAdd, appendFin_natAdd] using w.modN_ne_modE ⟨k₁, mS rfl⟩ ⟨k₂, mS rfl⟩
  · simpa [appendFin_natAdd, appendFin_castAdd] using
      (w.modN_ne_modE ⟨k₂, mS rfl⟩ ⟨k₁, mS rfl⟩).symm
  · simpa [appendFin_natAdd] using fun e ↦ planeModDisj rE hne _ (mS rfl) (mS e)

/- ## Section 6C: `subspaceStep_pUnloadSharedHiMerged` -/
/- ## Section 7A: `cHiNSub341` Shared-`PortB` Wiring & `SharedPortBInput341` -/
theorem rCtrlLo_elec_eq_scr {rNuc : RouterReg 47 6 dLayout} {rElec : RouterReg 187 8 dLayout}
    (hRegs : ValidMuxD1Stage2Regs rNuc rElec)
    (q : Fin 187) :
    ∃ m : Fin scrLLayout, rCtrlLo rElec q = rScrLayout m ∧ (m.val < 65 ∨ 105 ≤ m.val) := by
  have := q.isLt
  obtain ⟨m, hm, hmb⟩ := hRegs.privElec ⟨22 + q.val, by omega⟩
  exact ⟨m, (congrArg rElec.wires (Fin.ext (by simp only [basePub]; omega))).trans hm, hmb⟩

theorem SharedPortBWiring.ofValidMuxD1_341 {n : ℕ} {rNuc : RouterReg 47 6 dLayout}
    {rElec : RouterReg 187 8 dLayout}
    (hRegs : ValidMuxD1Stage2Regs rNuc rElec) (hCtrlN : ∀ p q : Fin 47, cHiNSub341 p ≠
        rCtrlLo rNuc q)
    (hCtrlE : ∀ (p : Fin 47) (q : Fin 187), cHiNSub341 p ≠ rCtrlLo rElec q)
        (rTot : QRegister dLayout n) :
    SharedPortBWiring (rTot.compose rNuc) (rTot.compose rElec) (fun p ↦ rTot (cHiNSub341 p)) := by
  have neNE (i) {j : Fin (routerWidth 187 8)} (hj : j.val < basePub 187 8)
      (e : rTot (rNuc i) = rTot (rElec j)) : False := by
    have _ := j.isLt
    have _ := hRegs.val_rNuc_bounds i
    have hv : (rNuc i).val = (rElec j).val := congrArg Fin.val (rTot.wires.injective e)
    rw [hRegs.pubElec j hj, val_rElecLayout_eq, val_elecRouterWireFn j] at hv
    dsimp [basePub, routerWidth, dLayout] at *; split_ifs at hv <;> omega
  have neEN (q) {i : Fin (routerWidth 47 6)} (hi : i.val < 14 ∨ 110 ≤ i.val ∧ i.val < 1238)
      (e : rTot (rCtrlLo rElec q) = rTot (rNuc i)) : False := by
    obtain ⟨m, hmEq, _⟩ := rCtrlLo_elec_eq_scr hRegs q
    have : m.val < 1565 := m.isLt
    have hv : (rCtrlLo rElec q).val = (rNuc i).val := congrArg Fin.val (rTot.wires.injective e)
    rw [hmEq, val_rScrLayout, hRegs.pubNuc i (show i.val <
        basePub 47 6 by dsimp [basePub]; omega),
      val_rNucLayout_eq, val_nucRouterWireFn i] at hv
    dsimp [scrLLayout, routerWidth] at *; split_ifs at hv <;> omega
  exact {
    cHiN_inj := fun p q ↦ cHiNSub341_ne rTot p q
    rawN_ne_cHiN :=
        cHiNSub341_ne_pubNuc hRegs rTot (i := ⟨1, rw_lt1 47 6⟩)
        (by dsimp [routerWidth, basePub]; omega)
    idx2N_ne_cHiN := fun d ↦ cHiNSub341_ne_pubNuc hRegs rTot (i := ⟨2 + 6 + d.val, rw_ltIdx2 d⟩)
      ((fun _ ↦ by dsimp [basePub]; omega) d.isLt)
    cHiN_ne_ctrlE := fun p q e ↦ hCtrlE p q (rTot.wires.injective e)
    cHiN_ne_ctrlN := fun p q e ↦ hCtrlN p q (rTot.wires.injective e)
    cHiN_notModN := fun p hm ↦ let ⟨_, _, hi, heq⟩ := allPlaneMod_pubIdx_nuc hm
      cHiNSub341_ne_pubNuc hRegs rTot hi p heq.symm
    cHiN_notModE := fun p hm ↦ let ⟨_, _, hj, heq⟩ := allPlaneMod_pubIdx_elec hm
      cHiNSub341_ne_pubElec hRegs rTot hj p heq.symm
    cHiN_notHdrE := fun p hh ↦ let ⟨_, hj, heq⟩ := routerCtrlSet_pubIdx_elec hh
      cHiNSub341_ne_pubElec hRegs rTot (Nat.lt_trans hj (by decide)) p heq.symm
    pubN_ne_pubE := fun {_} hi {_} hj ↦ pubNuc_ne_pubElec hRegs rTot hi hj
    rN_disj_rE_mod := fun i _ hu e ↦ let ⟨_, _, hj, heq⟩ := allPlaneMod_pubIdx_elec hu
      neNE i hj (e.trans heq)
    ctrlN_disj_rE_hdr := fun _ _ hu e ↦ let ⟨_, hj, heq⟩ := routerCtrlSet_pubIdx_elec hu
      neNE _ (Nat.lt_trans hj (by decide)) (e.trans heq)
    ctrlE_ne_sysN := fun q p b ↦
        neEN q (.inr ((fun (_ : _ ∧ _) ↦ by dsimp; omega) ⟨p.isLt, b.isLt⟩))
    ctrlE_disj_rN_hdr := fun q _ hu e ↦ let ⟨_, hi, heq⟩ := routerCtrlSet_pubIdx_nuc hu
      neEN q (.inl hi) (e.trans heq) }
/-- Pre-router ket invariant for merged shared-`PortB` Stage 5 at `cHiNSub341`. -/
def SharedPortBInput341 {n : ℕ} (rTot : QRegister dLayout n) (rN : RouterReg 47 6 n)
    (rE : RouterReg 187 8 n) (β : BitAssignment n) : Prop :=
  ValidZeroGatedSortedRouterInput rE β ∧
  ValidZeroGatedSortedRouterInput rN β ∧
  (∀ p : Fin 47, β (rTot (cHiNSub341 p)) = 0) ∧
  β (rTot (wPotIsNN rPot0Layout)) = β (rRawHas2 rN) ∧
  (β (rRawHas2 rN) = 1 → β (rRawHas2 rE) = 0)
/- ## Section 7B.1: `uSwapHi24` Merge-Swap Ket Expansion -/
/- ## Section 7B.2: `uBellLoHiMerged` + `uSwapHi24` LHS Ket Expansion -/
/- ## Section 7C.1: Commutation Reordering & `uLoEConj` Ket Action -/
/- ## Section 7C.2: `sharedPortBMerged_stage5_input_factor` -/
/- ## Section 7D.1: `uBellLoHiMerged` Congruence & `cHiNSub341` Clean-Scratch Support -/

theorem supportedOn_and {n : ℕ} {P₁ P₂ : BitAssignment n → Prop} {M : Operator (2 ^ n)}
    (h₁ : SupportedOn P₁ M)
    (h₂ : SupportedOn P₂ M) : SupportedOn (fun β ↦ P₁ β ∧ P₂ β) M := by
  classical
  let D₁ : Operator (2 ^ n) := Matrix.diagonal fun x ↦ if P₁ (basisBitsEquiv n x) then 1 else 0
  have hD_ket (β : BitAssignment n) : D₁.mulVec (SplitRouterSeqBell26k.ket β) =
      if P₁ β then SplitRouterSeqBell26k.ket β else 0 := funext fun x ↦ by
    rw [Matrix.mulVec_diagonal]
    rcases eq_or_ne x ((basisBitsEquiv n).symm β) with rfl | hx
    · simp only [Equiv.apply_symm_apply]; split_ifs <;> simp
    · have h0 : PhotochemistrySolution.SplitRouterSeqBell26k.ket β x = 0 :=
        (congrFun (Matrix.one_mulVec (KinB.ket β)).symm x).trans
          ((mulVec_ket_apply _ β x).trans (Matrix.one_apply_ne hx))
      split_ifs <;> simp [h0]
  have e₁ : D₁ * M = M := (h₁ D₁ 1 fun β hp ↦ by
    rw [hD_ket β, ite_eq_left hp, Matrix.one_mulVec]).trans (Matrix.one_mul M)
  intro A B hAB
  rw [← e₁, ← Matrix.mul_assoc, h₂ (A * D₁) (B * D₁) fun β hp₂ ↦ by
    simp only [← Matrix.mulVec_mulVec, hD_ket β]; split_ifs with hp₁ <;>
      first | exact hAB β ⟨hp₁, hp₂⟩ | simp only [Matrix.mulVec_zero], Matrix.mul_assoc, e₁]

theorem supportedOn_cHiNSub341_zero_of_scr {n wIn : ℕ} {decodeCoin : Fin (2 ^ 41) → ZeroNEremSector}
    (rTot : QRegister dLayout n)
    (o1 : Stage1ZeroNEremLayout wIn decodeCoin) {X : Operator (2 ^ n)}
    (hX : (rTot.compose rScrLayout).basisOutcomeProjector 0 * X = X) : SupportedOn (fun β ↦
        ∀ p : Fin 47, β (rTot (cHiNSub341 p)) = 0) ((rTot.embedUnitary o1.uLocal).1 * X) := by
  refine supportedOn_of_inKetPred fun ξ ↦ ?_
  rw [← Matrix.mulVec_mulVec]
  refine inKetPred_mulVec (rTot.embedUnitary o1.uLocal).1 (fun η hScr ↦ ?_)
      (inKetPred_cleanScr_of_proj rTot hX ξ)
  rw [w1Ket rTot o1 η hScr]
  refine inKetPred_ket fun p ↦ ?_
  obtain ⟨m, hmb, hpm⟩ := cHiNSub341_isScrLayout p
  rw [DynCircExt.writeReg_apply_reg, hpm]
  exact routedStage1_scr_zero hScr _ _ m hmb

end QuantumComputation.Specs.PhotochemistrySolution.PortBStage5Merged
end
end
end

noncomputable section
set_option exponentiation.threshold 8192
open Operator QProg DynamicCircuit Matrix Circuit Qubit PrimitiveGate QuantumComputation.Specs
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
  _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt
open QuantumComputation.Specs.PhotochemistrySolution
  QuantumComputation.Specs.PhotochemistrySolution.OvBidir
  QuantumComputation.Specs.PhotochemistrySolution.SelectCompactAnc
open QuantumComputation.Specs.PhotochemistrySolution.SelectCompactRot34
  QuantumComputation.Specs.PhotochemistrySolution.SelectCsa64ThreeSpec
namespace QuantumComputation.Specs.PhotochemistrySolution.Stage5StackCerts
set_option maxRecDepth 4096
open scoped Matrix Matrix.Norms.L2Operator BigOperators Polynomial
open Real WithLp Polynomial ComplexConjugate PhotochemistrySolution.GQSP
  PhotochemistrySolution.QubitizationCore PhotochemistrySolution.QubitizationWalkSem
open PhotochemistrySolution.QubitizationProgram PhotochemistrySolution.QubitizationTop
  PhotochemistrySolution.QubitizationKapteyn PhotochemistrySolution.SelectSymDyn
open PhotochemistrySolution.SelectSymDynInstance PhotochemistrySolution.SelectApprox
  PhotochemistrySolution.BucketRouterCircuit
open PhotochemistrySolution.DiagShiftSpecBridge PhotochemistrySolution.SelectEulerRot32
open PhotochemistrySolution.SelectCsa64GqspWalk PhotochemistrySolution.SelectLcu70Rot32
open PhotochemistrySolution.TightWalkCauchy PhotochemistrySolution.TightWalkCauchy54
  PhotochemistrySolution.ClusterPotSlice PhotochemistrySolution.GenWeightsSelect
open PhotochemistrySolution.ScreenFermatCore PhotochemistrySolution.Tier1K3708
attribute [local irreducible] systemQubits_frozen SelectCompactAnc.ancWOfScr

abbrev delta_walkStack : ℝ := 1 / ((10 : ℕ) : ℝ) ^ (20 : ℕ)

def epsBlockCap (α εKin εEE εNN εEN : ℝ) : ℝ :=
  α⁻¹ * (εKin +
    (17391 * εEE + 16955 * εNN + 34969 * εEN) / ((2 ^ 35 : ℝ) * gridSpacing_frozen))

/-- Parametric `hCap` bridge (`4231872 * epsBlockCap α εKin εEE εNN εEN ≤ 100`). -/
theorem hCap_of_pot_cap {α εKin εEE εNN εEN C : ℝ} (hα : 0 < α)
    (hC : 17391 * εEE + 16955 * εNN + 34969 * εEN ≤ C)
    (hBnd : 4231872 * (α⁻¹ * (εKin + C / ((2 ^ 35 : ℝ) * gridSpacing_frozen))) ≤ 100) : 4231872 *
    epsBlockCap α εKin εEE εNN εEN ≤ 100 := by
  exact le_trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
    (add_le_add_right (div_le_div_of_nonneg_right hC
      (mul_pos (by norm_num) gridSpacing_pos).le) εKin)
    (inv_nonneg.mpr hα.le)) (by norm_num)) hBnd

/-- Parametric Hamiltonian error budget bridge (`(α * t) * epsBlockCap ≤ εHam`). -/
theorem hham_of_pot_cap {α εKin εEE εNN εEN C εHam : ℝ} (hα : 0 < α)
    (hC : 17391 * εEE + 16955 * εNN + 34969 * εEN ≤ C)
    (hBnd : evolutionTime_frozen * (εKin + C / ((2 ^ 35 : ℝ) * gridSpacing_frozen)) ≤ εHam) :
    (α * evolutionTime_frozen) * epsBlockCap α εKin εEE εNN εEN ≤ εHam := by
  rw [epsBlockCap, mul_comm α, mul_assoc, mul_inv_cancel_left₀ hα.ne']
  exact le_trans (mul_le_mul_of_nonneg_left (add_le_add_right
    (div_le_div_of_nonneg_right hC (mul_pos (by norm_num) gridSpacing_pos).le) εKin)
    (by norm_num [evolutionTime_frozen])) hBnd

abbrev alphaTier1WalkFull : ℝ := alphaFermatCoin * (167085 / 167340) * (100000 / 100155)

/-- Time-scale cap `sMax` for the `p = 155` regime (`q_ee = 167,340`, `p = 155`). -/
abbrev sMax_tier1Walk_full : ℝ := ((33258891316 : ℕ) : ℝ) / ((10000 : ℕ) : ℝ)

theorem hs_tier1Walk_full_le_sMax : alphaTier1WalkFull * evolutionTime_frozen ≤
    sMax_tier1Walk_full
    := by unfold alphaTier1WalkFull alphaFermatCoin evolutionTime_frozen sMax_tier1Walk_full;
            norm_num
end QuantumComputation.Specs.PhotochemistrySolution.Stage5StackCerts

namespace QuantumComputation.Specs.PhotochemistrySolution.Stage5StackCore
open PhotochemistrySolution.SelectCsa64ProvSpec PhotochemistrySolution.TopSelectBridge
  PhotochemistrySolution.UnembedIdleAncillas
open PhotochemistrySolution.UnembedO3Bridge PhotochemistrySolution.SelectOracles
  PhotochemistrySolution.RouterSelectWiringA PhotochemistrySolution.RouterSelectWiringB
open PhotochemistrySolution.ProviderCore PhotochemistrySolution.ProviderCoreFused
  PhotochemistrySolution.FusedUnembedLGen
open PhotochemistrySolution.ProviderZeroFloor PhotochemistrySolution.Coin70Lift
  PhotochemistrySolution.Sub5885 PhotochemistrySolution.DepthArithWalk

/--
Kept physical ancilla count `(62 - gLo) + wWork + (mCoin + 2)` on `dLayout = 7298`
(`gLo = 6, wWork = 351, mCoin = 74 -> 483`; `gLo = 23, wWork = 351, mCoin = 74 -> 466`).
-/
abbrev outerCoinAncillasStack (gLo wWork mCoin : ℕ) : ℕ :=
  (62 - gLo) + wWork + (mCoin + 2)

/--
Idle physical ancilla count `(1618 + gLo) - wWork - mCoin` (`483 + 1199 = 1682`,
`466 + 1216 = 1682`).
-/
abbrev outerCoinIdleStack (gLo wWork mCoin : ℕ) : ℕ :=
  (1618 + gLo) - wWork - mCoin

/-- LCU block bound `scrLLayout + (mCoin + 2) ≤ scrWLayout + 70` for `mCoin ≤ 80`. -/
theorem hpStack (mCoin : ℕ) (hm : mCoin ≤ 80) : 1565 + (mCoin + 2) ≤ scrWLayout + 70 := by
  dsimp only [scrWLayout]; omega
/-- Reflection offset bound `65 + (mCoin + 1) ≤ 1565` for `mCoin ≤ 80`. -/
theorem hmStackOff65 (mCoin : ℕ) (hm : mCoin ≤ 80) :
    65 + (mCoin + 1) ≤ 1565 := by omega

/--
Kept ancilla index map in `0 .. 1681`: `[3 + gLo .. 30]`, `[64 .. 96]`,
`[99 .. 99 + wWork)`, `[1599 .. 1600 + mCoin]`, `{1681}`.
-/
def keepStackVal (gLo wWork mCoin i : ℕ) : ℕ :=
  natIte i (28 - gLo) (3 + gLo + i)
    (natIte i (61 - gLo) ((36 + gLo) + i)
      (natIte i ((61 - gLo) + wWork) ((38 + gLo) + i)
        (natIte i ((61 - gLo) + wWork + (mCoin + 2)) ((1538 + gLo) + (i - wWork))
          1681)))

/--
Idle ancilla index map in `0 .. 1681`: `[0 .. 2 + gLo]`, `[31 .. 63]`, `[97 .. 98]`,
`[99 + wWork .. 1598]`, `[1601 + mCoin .. 1680]`.
-/
def idleStackVal (gLo wWork mCoin l : ℕ) : ℕ :=
    natIte l (3 + gLo) l (natIte l (36 + gLo) ((28 - gLo) + l) (natIte l (38 + gLo) ((61 - gLo) + l)
    (natIte l ((1538 + gLo) - wWork) ((61 - gLo + wWork) + l) (((63 - gLo) + wWork + mCoin) + l))))
theorem keepStackVal_lt (gLo wWork mCoin : ℕ) (hgLo : gLo ≤ 23) (hmCoin : mCoin ≤ 80)
    (hwHi : wWork ≤ 1500) (i : Fin (outerCoinAncillasStack gLo wWork mCoin)) :
    keepStackVal gLo wWork mCoin i.val < ancWOfScr scrWLayoutFused := by
  have := i.isLt
  rw [ancWOfScr_layoutFused]; dsimp only [keepStackVal, outerCoinAncillasStack, natIte] at *
  (repeat' split) <;> omega

/-- Typed kept wire embedding into `ancWOfScr scrWLayoutFused = 1682`. -/
def keepStackFn (gLo wWork mCoin : ℕ) (hgLo : gLo ≤ 23) (hmCoin : mCoin ≤ 80) (hwHi : wWork ≤ 1500)
    (i : Fin (outerCoinAncillasStack gLo wWork mCoin)) : Fin (ancWOfScr scrWLayoutFused) :=
    ⟨keepStackVal gLo wWork mCoin i.val, keepStackVal_lt gLo wWork mCoin hgLo hmCoin hwHi i⟩
theorem idleStackVal_lt (gLo wWork mCoin : ℕ) (hgLo : gLo ≤ 23) (_hmCoin : mCoin ≤ 80)
    (hwHi : wWork ≤ 1500) (l : Fin (outerCoinIdleStack gLo wWork mCoin)) :
    idleStackVal gLo wWork mCoin l.val < ancWOfScr scrWLayoutFused := by
  have := l.isLt
  rw [ancWOfScr_layoutFused]; dsimp only [idleStackVal, outerCoinIdleStack, natIte] at *
  (repeat' split) <;> omega

/-- Typed idle wire embedding into `ancWOfScr scrWLayoutFused = 1682`. -/
def idleStackFn (gLo wWork mCoin : ℕ) (hgLo : gLo ≤ 23) (hmCoin : mCoin ≤ 80) (hwHi : wWork ≤ 1500)
    (l : Fin (outerCoinIdleStack gLo wWork mCoin)) : Fin (ancWOfScr scrWLayoutFused) :=
    ⟨idleStackVal gLo wWork mCoin l.val, idleStackVal_lt gLo wWork mCoin hgLo hmCoin hwHi l⟩
theorem invStack_lt0 {gLo wWork mCoin v : ℕ} (hgLo : gLo ≤ 23) (hmCoin : mCoin ≤ 80)
    (hwHi : wWork ≤ 1500) (h : v < 3 + gLo) : v <
    outerCoinIdleStack gLo wWork mCoin := by dsimp only [outerCoinIdleStack]; omega
theorem invStack_lt1 {gLo wWork mCoin v : ℕ} (h : v < 31) : v - (3 + gLo) <
    outerCoinAncillasStack gLo wWork mCoin := by dsimp only [outerCoinAncillasStack]; omega
theorem invStack_lt2 {gLo wWork mCoin v : ℕ} (hgLo : gLo ≤ 23) (hmCoin : mCoin ≤ 80)
    (hwHi : wWork ≤ 1500) (h : v < 64) : v - (28 - gLo) <
    outerCoinIdleStack gLo wWork mCoin := by dsimp only [outerCoinIdleStack]; omega
theorem invStack_lt3 {gLo wWork mCoin v : ℕ} (hgLo : gLo ≤ 23) (h : v < 97) : v - (36 + gLo) <
    outerCoinAncillasStack gLo wWork mCoin := by dsimp only [outerCoinAncillasStack]; omega
theorem invStack_lt4 {gLo wWork mCoin v : ℕ} (hgLo : gLo ≤ 23) (hmCoin : mCoin ≤ 80)
    (hwHi : wWork ≤ 1500) (h : v < 99) : v - (61 - gLo) <
    outerCoinIdleStack gLo wWork mCoin := by dsimp only [outerCoinIdleStack]; omega
theorem invStack_lt5 {gLo wWork mCoin v : ℕ} (hgLo : gLo ≤ 23) (h : v < 99 + wWork) : v -
    (38 + gLo) <
    outerCoinAncillasStack gLo wWork mCoin := by dsimp only [outerCoinAncillasStack]; omega
theorem invStack_lt6 {gLo wWork mCoin v : ℕ} (hgLo : gLo ≤ 23) (hmCoin : mCoin ≤ 80)
    (hwHi : wWork ≤ 1500) (h6 : v < 1599) : v - (61 - gLo + wWork) <
    outerCoinIdleStack gLo wWork mCoin := by dsimp only [outerCoinIdleStack]; omega
theorem invStack_lt7 {gLo wWork mCoin v : ℕ} (hgLo : gLo ≤ 23) (h7 : v < 1601 + mCoin) :
    (v + wWork) - (1538 + gLo) <
    outerCoinAncillasStack gLo wWork mCoin := by dsimp only [outerCoinAncillasStack]; omega
theorem invStack_lt8 {gLo wWork mCoin v : ℕ} (hgLo : gLo ≤ 23) (hmCoin : mCoin ≤ 80)
    (hwHi : wWork ≤ 1500) (h8 : v < 1681) : v - ((63 - gLo) + wWork + mCoin) <
    outerCoinIdleStack gLo wWork mCoin := by dsimp only [outerCoinIdleStack]; omega
theorem invStack_lt9 {gLo wWork mCoin : ℕ} (hgLo : gLo ≤ 23) : (61 - gLo) + wWork + (mCoin + 2) <
    outerCoinAncillasStack gLo wWork mCoin := by dsimp only [outerCoinAncillasStack]; omega
/-- Non-dependent inverse value map on `ℕ` for the dual-Bell reflected Stage-5 stack. -/
def invStackOfVal (gLo wWork mCoin : ℕ) (hgLo : gLo ≤ 23) (hmCoin : mCoin ≤ 80)
    (hwHi : wWork ≤ 1500) (v : ℕ) : Sum (Fin (outerCoinAncillasStack gLo wWork mCoin))
    (Fin (outerCoinIdleStack gLo wWork mCoin)) :=
  natDIte v (3 + gLo) (fun h0 ↦ .inr ⟨v, invStack_lt0 hgLo hmCoin hwHi h0⟩) fun _ ↦
  natDIte v 31 (fun h1 ↦ .inl ⟨v - (3 + gLo), invStack_lt1 h1⟩) fun _ ↦
  natDIte v 64 (fun h2 ↦ .inr ⟨v - (28 - gLo), invStack_lt2 hgLo hmCoin hwHi h2⟩) fun _ ↦
  natDIte v 97 (fun h3 ↦ .inl ⟨v - (36 + gLo), invStack_lt3 hgLo h3⟩) fun _ ↦
  natDIte v 99 (fun h4 ↦ .inr ⟨v - (61 - gLo), invStack_lt4 hgLo hmCoin hwHi h4⟩) fun _ ↦
  natDIte v (99 + wWork) (fun h5 ↦ .inl ⟨v - (38 + gLo), invStack_lt5 hgLo h5⟩) fun _ ↦
  natDIte v 1599 (fun h6 ↦ .inr ⟨v - (61 - gLo + wWork), invStack_lt6 hgLo hmCoin hwHi h6⟩) fun _ ↦
  natDIte v (1601 + mCoin)
      (fun h7 ↦ .inl ⟨(v + wWork) - (1538 + gLo), invStack_lt7 hgLo h7⟩) fun _ ↦
  natDIte v 1681 (fun h8 ↦ .inr ⟨v - ((63 - gLo) + wWork + mCoin),
      invStack_lt8 hgLo hmCoin hwHi h8⟩) fun _ ↦
  .inl ⟨(61 - gLo) + wWork + (mCoin + 2), invStack_lt9 hgLo⟩

/-- Inverse partition map for `(keepStackFn, idleStackFn)`. -/
def invStackFn (gLo wWork mCoin : ℕ) (hgLo : gLo ≤ 23) (hmCoin : mCoin ≤ 80) (hwHi : wWork ≤ 1500)
    (j : Fin (ancWOfScr scrWLayoutFused)) : Sum (Fin (outerCoinAncillasStack gLo wWork mCoin))
    (Fin (outerCoinIdleStack gLo wWork mCoin)) :=
    invStackOfVal gLo wWork mCoin hgLo hmCoin hwHi j.val
theorem invStackFn_keep (gLo wWork mCoin : ℕ) (hgLo : gLo ≤ 23) (hmCoin : mCoin ≤ 80)
    (hwHi : wWork ≤ 1500) (i : Fin (outerCoinAncillasStack gLo wWork mCoin)) :
    invStackFn gLo wWork mCoin hgLo hmCoin hwHi (keepStackFn gLo wWork mCoin hgLo hmCoin hwHi i) =
    .inl i := by
  have := i.isLt
  dsimp only [outerCoinAncillasStack, invStackFn, keepStackFn, keepStackVal, natIte] at *
  (repeat' split) <;> (
    unfold invStackOfVal
    repeat' first | rw [natDIte_left (by omega)] | rw [natDIte_right (by omega)]
    exact congrArg Sum.inl (Fin.ext (by dsimp only; omega)))

theorem invStackFn_idle (gLo wWork mCoin : ℕ) (hgLo : gLo ≤ 23) (hmCoin : mCoin ≤ 80)
    (hwHi : wWork ≤ 1500) (l : Fin (outerCoinIdleStack gLo wWork mCoin)) :
    invStackFn gLo wWork mCoin hgLo hmCoin hwHi (idleStackFn gLo wWork mCoin hgLo hmCoin hwHi l) =
    .inr l := by
  have := l.isLt
  dsimp only [outerCoinIdleStack, invStackFn, idleStackFn, idleStackVal, natIte] at *
  (repeat' split) <;> (
    unfold invStackOfVal
    repeat' first | rw [natDIte_left (by omega)] | rw [natDIte_right (by omega)]
    try exact congrArg Sum.inr (Fin.ext (by dsimp only; omega)))

theorem invStackFn_right (gLo wWork mCoin : ℕ) (hgLo : gLo ≤ 23) (hmCoin : mCoin ≤ 80)
    (hwHi : wWork ≤ 1500) (j : Fin (ancWOfScr scrWLayoutFused)) :
    Sum.elim (keepStackFn gLo wWork mCoin hgLo hmCoin hwHi)
    (idleStackFn gLo wWork mCoin hgLo hmCoin hwHi) (invStackFn gLo wWork mCoin hgLo hmCoin hwHi j) =
    j := by
  have := j.isLt.trans_le (le_of_eq ancWOfScr_layoutFused)
  dsimp only [invStackFn, invStackOfVal, natDIte]
  (repeat' split) <;> (
    apply Fin.ext
    dsimp only [Sum.elim, keepStackFn, idleStackFn, keepStackVal, idleStackVal]
    repeat' first | rw [natIte_left (by omega)] | rw [natIte_right (by omega)]
    try omega)

theorem keepStackFn_inj (gLo wWork mCoin : ℕ) (hgLo : gLo ≤ 23) (hmCoin : mCoin ≤ 80)
    (hwHi : wWork ≤ 1500) : Function.Injective (keepStackFn gLo wWork mCoin hgLo hmCoin hwHi)
    := by exact fun a b h ↦
            Sum.inl.inj ((invStackFn_keep _ _ _ _ _ _ a).symm.trans (h ▸ invStackFn_keep _ _ _ _ _ _
            b))
theorem idleStackFn_inj (gLo wWork mCoin : ℕ) (hgLo : gLo ≤ 23) (hmCoin : mCoin ≤ 80)
    (hwHi : wWork ≤ 1500) : Function.Injective (idleStackFn gLo wWork mCoin hgLo hmCoin hwHi)
    := by exact fun a b h ↦
            Sum.inr.inj ((invStackFn_idle _ _ _ _ _ _ a).symm.trans (h ▸ invStackFn_idle _ _ _ _ _ _
            b))
theorem keepStackFn_disjoint_idle (gLo wWork mCoin : ℕ) (hgLo : gLo ≤ 23) (hmCoin : mCoin ≤ 80)
    (hwHi : wWork ≤ 1500) : (QRegister.mk ⟨keepStackFn gLo wWork mCoin hgLo hmCoin hwHi,
    keepStackFn_inj gLo wWork mCoin hgLo hmCoin hwHi⟩).DisjointWires (QRegister.mk ⟨idleStackFn gLo
    wWork mCoin hgLo hmCoin hwHi, idleStackFn_inj gLo wWork mCoin hgLo hmCoin hwHi⟩) :=
  QRegister.disjoint_iff.mpr fun i l h ↦ by
    change keepStackFn gLo wWork mCoin hgLo hmCoin hwHi i =
        idleStackFn gLo wWork mCoin hgLo hmCoin hwHi l at h;
        have h1 :=
        invStackFn_keep gLo wWork mCoin hgLo hmCoin hwHi i; rw [h,
        invStackFn_idle gLo wWork mCoin hgLo hmCoin hwHi l] at h1
    cases h1

theorem keepStackFn_cover_idle (gLo wWork mCoin : ℕ) (hgLo : gLo ≤ 23) (hmCoin : mCoin ≤ 80)
    (hwHi : wWork ≤ 1500) (j : Fin (ancWOfScr scrWLayoutFused)) :
    (∃ i, keepStackFn gLo wWork mCoin hgLo hmCoin hwHi i = j) ∨
    (∃ l, idleStackFn gLo wWork mCoin hgLo hmCoin hwHi l = j) := by
  have hr := invStackFn_right gLo wWork mCoin hgLo hmCoin hwHi j
  rcases h : invStackFn gLo wWork mCoin hgLo hmCoin hwHi j with i | l
  · exact .inl ⟨i, by simpa [h] using hr⟩
  · exact .inr ⟨l, by simpa [h] using hr⟩

/--
Parametric `AncillaPartition` on `ancWOfScr scrWLayoutFused = 1682` keeping
`(62 - gLo) + wWork + (mCoin + 2)` physical ancillas.
-/
def partOuterCoinStackOf (gLo wWork mCoin : ℕ) (hgLo : gLo ≤ 23) (hmCoin : mCoin ≤ 80)
    (hwHi : wWork ≤ 1500) : AncillaPartition (ancWOfScr scrWLayoutFused)
    (outerCoinAncillasStack gLo wWork mCoin) (outerCoinIdleStack gLo wWork mCoin) :=
    AncillaPartition.mk ⟨⟨keepStackFn gLo wWork mCoin hgLo hmCoin hwHi,
    keepStackFn_inj gLo wWork mCoin hgLo hmCoin hwHi⟩⟩
    ⟨⟨idleStackFn gLo wWork mCoin hgLo hmCoin hwHi,
    idleStackFn_inj gLo wWork mCoin hgLo hmCoin hwHi⟩⟩
    (keepStackFn_disjoint_idle gLo wWork mCoin hgLo hmCoin hwHi)
    (keepStackFn_cover_idle gLo wWork mCoin hgLo hmCoin hwHi)
    (invStackFn gLo wWork mCoin hgLo hmCoin hwHi) (invStackFn_keep gLo wWork mCoin hgLo hmCoin hwHi)
    (invStackFn_idle gLo wWork mCoin hgLo hmCoin hwHi)
    (invStackFn_right gLo wWork mCoin hgLo hmCoin hwHi)
theorem hIdleSafe_partOuterCoinStackOf {gLo wWork mCoin : ℕ} (hgLo : gLo ≤ 23)
    (hmCoin : mCoin ≤ 80) (hwLo : 65 + (mCoin + 1) ≤ 65 + wWork) (hwHi : wWork ≤ 1500)
    (l : Fin (outerCoinIdleStack gLo wWork mCoin)) :
    let u := ((partOuterCoinStackOf gLo wWork mCoin hgLo hmCoin hwHi).idleIdx l).val
    u < 3 + gLo ∨
      (31 ≤ u ∧ u < 64) ∨
      (97 ≤ u ∧ u < 34 + 65) ∨
      (34 + 65 + (mCoin + 1) ≤ u ∧ u < 34 + 1565) ∨
      (34 + 1565 + (mCoin + 2) ≤ u ∧ u < ancWOfScr scrWLayoutFused - 1) := by
  have := l.isLt
  dsimp only [outerCoinIdleStack] at *
  rw [show ((partOuterCoinStackOf gLo wWork mCoin hgLo hmCoin hwHi).idleIdx l).val =
      idleStackVal gLo wWork mCoin l.val from rfl,
    show ancWOfScr scrWLayoutFused - 1 = 1681 from rfl]
  dsimp only [idleStackVal, natIte]; (repeat' split) <;> omega

/--
Active wire predicate on `dLayoutFused = 7298` keeping `[5619 + gLo .. 5646]`,
`[5680 .. 5712]`, `[5715 .. 5715 + wWork)`, `[7215 .. 7216 + mCoin]`, and `7297`.
-/
def ActiveOuterCoinStackOf (gLo wWork mCoin : ℕ) (w : Wire dLayoutFused) : Prop :=
    w.val < 5616 ∨ (5619 + gLo ≤ w.val ∧ w.val ≤ 5646) ∨ (5680 ≤ w.val ∧ w.val ≤ 5712) ∨
    (5715 ≤ w.val ∧ w.val < 5715 + wWork) ∨ (7215 ≤ w.val ∧ w.val ≤ 7216 + mCoin) ∨ w.val = 7297
/-- Ambient wire safety predicate for the dual-Bell reflected Stage-5 stack. -/
def SafeConcatActiveStack (gLo wWork mCoin n : ℕ)
    (rS : QRegister systemQubits_frozen (n + outerCoinIdleStack gLo wWork mCoin))
    (rA : QRegister (ancWOfScr scrWLayout) (n + outerCoinIdleStack gLo wWork mCoin))
    (u : Wire (n + outerCoinIdleStack gLo wWork mCoin)) : Prop :=
    ∃ (hd : rS.DisjointWires rA) (w : Wire dLayout), ActiveOuterCoinStackOf gLo wWork mCoin w ∧ u =
    (rS.concat rA hd) w
attribute [local irreducible] systemQubits_frozen ancWOfScr in
theorem allWiresLtDyn_of_safeConcatActiveStack {Var : Type} {gLo wWork mCoin n : ℕ}
    (hgLo : gLo ≤ 23) (hmCoin : mCoin ≤ 80) (hwHi : wWork ≤ 1500)
    (rSys : QRegister systemQubits_frozen n)
    (rAncSmall : QRegister (outerCoinAncillasStack gLo wWork mCoin) n)
    {p : DynamicCircuit Var (n + outerCoinIdleStack gLo wWork mCoin)}
    (hDyn : DynWires (SafeConcatActiveStack gLo wWork mCoin n ((QRegister.block 0 n
    (zero_add_le_add_right n (outerCoinIdleStack gLo wWork mCoin))).compose rSys)
    (assembleAnc (partOuterCoinStackOf gLo wWork mCoin hgLo hmCoin hwHi)
    ((QRegister.block 0 n (zero_add_le_add_right n (outerCoinIdleStack gLo wWork mCoin))).compose
    rAncSmall) (QRegister.block n (outerCoinIdleStack gLo wWork mCoin) le_rfl)
    (amb_disj_phantom rAncSmall))) p) : AllWiresLtDyn n p :=
  allWiresLtDyn_of_dynWires (dynWires_mono (fun _ ⟨hd, w, hwAct, hu⟩ ↦ hu ▸
    PhotochemistrySolution.UnembedDualBell531.concat_val_lt_of_not_idle
      (partOuterCoinStackOf gLo wWork mCoin hgLo hmCoin hwHi) rSys rAncSmall w (fun l ↦ by
        have hlLt := l.isLt
        dsimp only [outerCoinIdleStack] at hlLt
        change systemQubits_frozen + idleStackVal gLo wWork mCoin l.val ≠ w.val
        rw [hSys5616_fused]
        dsimp only [ActiveOuterCoinStackOf] at hwAct
        dsimp only [idleStackVal, natIte]
        (repeat' split) <;> omega) hd) hDyn)

/--
Unified asymmetric `SELECT` bundle on `dLayout = 7298` parameterized by `(gLo, wWork, mCoin)`.
Proving this once at `gLo = 23` yields `gLo = 6` and `gLo = 23` via `widenGLo`.
-/
structure OuterCoinSelectBundleStackAsym (gLo wWork mCoin tUsel tCsel : ℕ)
    (hgLo : gLo ≤ 23) (hmCoin : mCoin ≤ 80) (A : Operator (2 ^ systemQubits_frozen)) where
  hwLo : mCoin + 1 ≤ wWork
  hwHi : wWork ≤ 1500
  S : LocalUnitary dLayout
  cselU : LocalUnitary dLayout
  uselU : LocalUnitary dLayout
  cOf : ∀ {Var : Type} {n : ℕ},
    Var → QRegister systemQubits_frozen n → QRegister (ancWOfScr scrWLayout) n →
        DynamicCircuit Var n
  uOf : ∀ {Var : Type} {n : ℕ},
    Var → QRegister systemQubits_frozen n → QRegister (ancWOfScr scrWLayout) n →
        DynamicCircuit Var n
  hlocal : SelectLocalSpecGen (scrSubLGen (hpStack mCoin hmCoin))
    (lcuSubLGen (hpStack mCoin hmCoin)) A S.u cselU.u (reflULGen (hpStack mCoin hmCoin))
  hUselCat : uselU.u.1 * cat8SharedProjCompactGen scrWLayout =
    S.u.1 * cat8SharedProjCompactGen scrWLayout
  hCommC : ∀ M : Operator (2 ^ 3),
      Commute cselU.u.1 ((locGrad3HiCompactGen scrWLayout).embedMatrix M)
  hCommU : ∀ M : Operator (2 ^ 3),
      Commute uselU.u.1 ((locGrad3HiCompactGen scrWLayout).embedMatrix M)
  hC : ∀ {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)]
    (v : Var) (rS : QRegister systemQubits_frozen n) (rA : QRegister (ancWOfScr scrWLayout) n)
    (hd : rS.DisjointWires rA),
    CleanWorkStep (rA.compose (scrSubLGen (hpStack mCoin hmCoin)))
      ((rS.concat rA hd).embedUnitary cselU.u) (cOf v rS rA) ∧
    CleanWorkStep (rA.compose (scrSubLGen (hpStack mCoin hmCoin)))
      ((rS.concat rA hd).embedUnitary uselU.u) (uOf v rS rA) ∧
    (cOf v rS rA).count .TOFF = 0 ∧ (uOf v rS rA).count .TOFF = 0 ∧
    (uOf v rS rA).count .T + 4 * (mCoin + 1) ≤ tUsel ∧
    (cOf v rS rA).count .T + 4 * (mCoin + 1) ≤ tCsel
  hDyn : ∀ {Var : Type} {m : ℕ} (v : Var)
    (rS : QRegister systemQubits_frozen m)
    (rA : QRegister (ancWOfScr scrWLayout) m),
    DynWires (SafeConcatGen (ActiveOuterCoinStackOf gLo wWork mCoin) rS rA) (cOf v rS rA) ∧
    DynWires (SafeConcatGen (ActiveOuterCoinStackOf gLo wWork mCoin) rS rA) (uOf v rS rA)
end QuantumComputation.Specs.PhotochemistrySolution.Stage5StackCore
end

end
