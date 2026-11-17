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

public import QuantumComputationDiscoveries.Algorithms.Photochemistry.Solution.DynQromMeasureUncompute
open QuantumComputation.Specs.PhotochemistrySolution.SpecDefs
open QuantumComputation.Specs.PhotochemistrySolution.QhlAux
open QuantumComputation.Specs.PhotochemistrySolution.PgBase
open QuantumComputation.Specs.PhotochemistrySolution.SelectBase
@[expose] public section
set_option allowUnsafeReducibility true
set_option autoImplicit false
set_option exponentiation.threshold 256

open scoped Matrix BigOperators
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SelectCsa64ProvSpec (SubspaceStep)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SplitBellVecCleanStep (CommutesWithDyn
    subspaceStep_of_circuit subspaceStep_congr_out)
noncomputable section
section
open scoped ComplexOrder MatrixOrder Circuit.Notation
open Operator QProg Matrix HermitianMat QuantumComputation.Specs.PhotochemistrySolution
  QuantumComputation.Specs.PhotochemistrySolution.XMeasUnld
open _root_.QuantumComputation.Specs.PhotochemistrySolution.QubitizationWalkSem hiding bitSign
  bitSign_add bitSign_mul_self sqrtHalf sqrtHalf_mul_sqrtHalf star_sqrtHalf
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynQromUncompA (fwdCirc
    wrapDyn count_wrapDyn fwdCirc_mulVec_ket projBit)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynQromUncompA
    (subspaceStep_wrapDyn)
namespace QuantumComputation.Specs.PhotochemistrySolution.SplitRouterSeqBell26k
set_option exponentiation.threshold 8192
open _root_.DynamicCircuit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt hiding bit_cases
  eval_seq_mulVec ket ket_CNOT ket_TOFF ket_X ket_projector_one ket_projector_zero matrix_ext_ket
  qAssign_obs_map_val
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB hiding bitSign eval_seq_mulVec ket
  ket_CNOT ket_TOFF ket_X matrix_ext_ket writeReg writeReg_apply_of_not_mem
open _root_.QuantumComputation.Specs.PhotochemistrySolution.XMeasLinearCleanStep
    (WirePair cnotPairsCircuit count_cnotPairsCircuit)
local instance (priority := 100000) {k : ℕ} : NeZero (2 ^ k) := ⟨pow_ne_zero k two_ne_zero⟩
abbrev ket {n : ℕ} := PhotochemistrySolution.XMeasUnld.ket (n := n)
theorem matrix_ext_ket {n : ℕ} {A B : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ}
    (h : ∀ β : BitAssignment n, A.mulVec (ket β) = B.mulVec (ket β)) : A = B :=
    XMeasUnld.matrix_ext_ket h
theorem z2_cswap_tgt (t b c : ZMod 2) :
    t + b + (b + c * (t + b)) = t + c * (t + b) := by decide +revert
theorem z2_cswap_1 (t b : ZMod 2) :
    b + 1 * (t + b) = t ∧ t + 1 * (t + b) = b := by decide +revert
/-! ## Section 1: `SupportedOn` & `4-T` Dynamic Temporary-AND Fanout Primitive -/

/--
`R` is supported on basis states satisfying `Pred` iff any two operators agreeing on all `ket β`
with `Pred β` agree when right-multiplied by `R`.
-/
def SupportedOn {n : ℕ} (Pred : BitAssignment n → Prop) (R : Operator (2 ^ n)) : Prop :=
    ∀ (A B : Operator (2 ^ n)), (∀ β : BitAssignment n, Pred β → A.mulVec (ket β) =
    B.mulVec (ket β)) → A * R = B * R
theorem supportedOn_projBit_zero {n : ℕ} {P : BitAssignment n → Prop} {R : Operator (2 ^ n)}
    (q : Wire n) (hq : ∀ β, P β → β q = 0) (hR : SupportedOn P R) : projBit q 0 * R = R :=
  (hR _ 1 fun β hβ ↦
      by simp only [ket_projector_zero, hq β hβ, ↓reduceIte,
           Matrix.one_mulVec]).trans (Matrix.one_mul R)
theorem projBit_zero_mulVec_ket {n : ℕ} (q : Wire n) (β : BitAssignment n) :
    (projBit q 0).mulVec (ket β) = if β q = 0 then ket β else 0 := ket_projector_zero q β
theorem cleanProj_singleton_eq_projBit {n : ℕ} (q : Wire n) : cleanProj ({q} : Finset (Wire n)) =
    projBit q 0 :=
  matrix_ext_ket fun β ↦ by
    rw [cleanProj_mulVec_ket, projBit_zero_mulVec_ket]; by_cases h : β q = 0 <;> simp [h]
theorem projBit_zero_comm_of_ket {n : ℕ} (q : Wire n) (A : Operator (2 ^ n))
    (F : BitAssignment n → BitAssignment n) (hA : ∀ β, A.mulVec (ket β) = ket (F β))
    (hq : ∀ β, F β q = β q) : projBit q 0 * A = A * projBit q 0 :=
  matrix_ext_ket fun β ↦ by
    simp only [← Matrix.mulVec_mulVec, hA, projBit_zero_mulVec_ket, hq]
    rcases bit_cases (β q) with h | h <;> simp [h, hA, one_ne_zero]
/-- Add constant bit `v : ZMod 2` sequentially onto every wire in `ts`. -/
def xorConstList {n : ℕ} (v : ZMod 2) : List (Wire n) → BitAssignment n → BitAssignment n
  | [], β => β
  | t :: ts, β => xorConstList v ts (Function.update β t (β t + v))
theorem xorConstList_of_not_mem {n : ℕ} (v : ZMod 2) :
    ∀ (ts : List (Wire n)) (β : BitAssignment n) (w : Wire n),
      (∀ t ∈ ts, w ≠ t) → xorConstList v ts β w = β w
  | [], _, _, _ => rfl
  | t :: ts, β, w, hne => by
      rw [xorConstList, xorConstList_of_not_mem v ts _ w (fun t' ht' ↦
          hne t' (List.mem_cons_of_mem t ht')), Function.update_of_ne (hne t List.mem_cons_self)]
theorem xorConstList_update_comm {n : ℕ} (v : ZMod 2) (q : Wire n) (x : ZMod 2) :
    ∀ (ts : List (Wire n)), (∀ t ∈ ts, t ≠ q) → ∀ (β : BitAssignment n),
      xorConstList v ts (Function.update β q x) =
        Function.update (xorConstList v ts β) q x
  | [], _, _ => rfl
  | t :: ts, hne, β => by
      simp only [xorConstList, Function.update_of_ne (hne t List.mem_cons_self),
        Function.update_comm (hne t List.mem_cons_self).symm,
            xorConstList_update_comm v q x ts fun _ h ↦ hne _ (.tail t h)]
/-- Classical Toffoli fanout specification circuit matching `tempAndFanoutDyn`. -/
def toffFanoutCirc {n : ℕ} (c₁ c₂ : Wire n) (h12 : c₁ ≠ c₂) :
    List { t : Wire n // c₁ ≠ t ∧ c₂ ≠ t } → Circuit n
  | [] => .identity
  | t :: ts => Circuit.TOFF c₁ c₂ t.1 h12 t.2.1 t.2.2 ;;ᶜ toffFanoutCirc c₁ c₂ h12 ts
theorem toffFanoutCirc_mulVec_ket {n : ℕ} (c₁ c₂ : Wire n) (h12 : c₁ ≠ c₂) :
    ∀ (tgts : List { t : Wire n // c₁ ≠ t ∧ c₂ ≠ t }) (β : BitAssignment n),
      (toffFanoutCirc c₁ c₂ h12 tgts).eval.1.mulVec (ket β) =
        ket (xorConstList (β c₁ * β c₂) (tgts.map Subtype.val) β)
  | [], _ => by
      simp only [List.map_nil, toffFanoutCirc, xorConstList, Circuit.eval_identity,
          Submonoid.coe_one, Matrix.one_mulVec]
  | t :: ts, β => by
      rw [toffFanoutCirc, eval_seq_mulVec, ket_TOFF, toffFanoutCirc_mulVec_ket c₁ c₂ h12 ts]
      simp only [List.map_cons, xorConstList, Function.update_of_ne t.2.1,
          Function.update_of_ne t.2.2]
theorem cnotPairs_from_src_mulVec_ket {n : ℕ} (qSrc : Wire n) :
    ∀ (tgts : List { t : Wire n // qSrc ≠ t }) (β : BitAssignment n),
      (cnotPairsCircuit (tgts.map fun t ↦
          (⟨qSrc, ⟨t.1, t.2⟩⟩ : WirePair n))).eval.1.mulVec (ket β) =
        ket (xorConstList (β qSrc) (tgts.map Subtype.val) β)
  | [], _ => by
      simp only [List.map_nil, cnotPairsCircuit, xorConstList, Circuit.eval_identity,
          Submonoid.coe_one, Matrix.one_mulVec]
  | t :: ts, β => by
      simp only [List.map_cons, cnotPairsCircuit, eval_seq_mulVec, ket_CNOT, xorConstList,
      cnotPairs_from_src_mulVec_ket qSrc ts, Function.update_of_ne t.2]
/-- `4-T`, `0-TOFF` dynamic temporary-AND fanout gate (`wrapDyn` + `cnotPairsCircuit`). -/
def tempAndFanoutDyn {Var : Type} {n : ℕ} (v : Var) (c₁ c₂ qAnc : Wire n) (h12 : c₁ ≠ c₂)
    (h1a : c₁ ≠ qAnc) (h2a : c₂ ≠ qAnc) (tgts : List { t : Wire n // c₁ ≠ t ∧ c₂ ≠ t ∧ qAnc ≠ t }) :
    DynamicCircuit Var n :=
  wrapDyn v (.andGate c₁ c₂ qAnc h12 h1a h2a)
    (.circuit (cnotPairsCircuit (tgts.map fun (t : { t : Wire n // c₁ ≠ t ∧ c₂ ≠ t ∧ qAnc ≠ t }) ↦
        ⟨qAnc, ⟨t.1, t.2.2.2⟩⟩)))
theorem count_tempAndFanoutDyn {Var : Type} {n : ℕ} (v : Var) (c₁ c₂ qAnc : Wire n) (h12 : c₁ ≠ c₂)
    (h1a : c₁ ≠ qAnc) (h2a : c₂ ≠ qAnc) (tgts : List { t : Wire n // c₁ ≠ t ∧ c₂ ≠ t ∧ qAnc ≠ t }) :
    (tempAndFanoutDyn v c₁ c₂ qAnc h12 h1a h2a tgts).count .T = 4 ∧
    (tempAndFanoutDyn v c₁ c₂ qAnc h12 h1a h2a tgts).count .TOFF = 0 := by
  let ps : List (WirePair n) := tgts.map fun t ↦ ⟨qAnc, ⟨t.1, t.2.2.2⟩⟩
  simpa [tempAndFanoutDyn, ComputeProg.numAnd, DynamicCircuit.count, ps,
      (count_cnotPairsCircuit ps).1,
    (count_cnotPairsCircuit ps).2] using count_wrapDyn v (.andGate c₁ c₂ qAnc h12 h1a h2a)
        (.circuit (cnotPairsCircuit ps))
theorem subspaceStep_tempAndFanoutDyn {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    (v : Var) (c₁ c₂ qAnc : Wire n)
    (h12 : c₁ ≠ c₂) (h1a : c₁ ≠ qAnc) (h2a : c₂ ≠ qAnc)
    (tgts : List { t : Wire n // c₁ ≠ t ∧ c₂ ≠ t ∧ qAnc ≠ t })
    (R : Operator (2 ^ n)) (hqAnc : projBit qAnc 0 * R = R) :
    let tgtsT : List { t : Wire n // c₁ ≠ t ∧ c₂ ≠ t } := tgts.map fun t ↦ ⟨t.1, t.2.1, t.2.2.1⟩
    SubspaceStep (Var := Var) R ((toffFanoutCirc c₁ c₂ h12 tgtsT).eval.1 * R)
      (tempAndFanoutDyn v c₁ c₂ qAnc h12 h1a h2a tgts) ∧
    projBit qAnc 0 * ((toffFanoutCirc c₁ c₂ h12 tgtsT).eval.1 * R) =
      (toffFanoutCirc c₁ c₂ h12 tgtsT).eval.1 * R := by
  intro tgtsT
  let P := projBit qAnc 0
  let pA : ComputeProg n := .andGate c₁ c₂ qAnc h12 h1a h2a
  let F := (fwdCirc pA).eval.1
  let cMid : Circuit n := cnotPairsCircuit (tgts.map fun t ↦ ⟨qAnc, ⟨t.1, t.2.2.2⟩⟩)
  let cTgt : Circuit n := toffFanoutCirc c₁ c₂ h12 tgtsT
  have hmem {w : Wire n} (hw : w ∈ tgtsT.map Subtype.val) : c₁ ≠ w ∧ c₂ ≠ w ∧ qAnc ≠ w :=
    let ⟨_, ht, hw'⟩ := List.mem_map.mp hw
    let ⟨u, _, hu⟩ := List.mem_map.mp ht
    hw' ▸ hu ▸ u.2
  have hAncOut : P * (cTgt.eval.1 * R) = cTgt.eval.1 * R := by
    rw [← Matrix.mul_assoc,
        projBit_zero_comm_of_ket qAnc cTgt.eval.1 _ (toffFanoutCirc_mulVec_ket c₁ c₂ h12 tgtsT)
      fun _ ↦ xorConstList_of_not_mem _ _ _ _ fun _ hw ↦ (hmem hw).2.2, Matrix.mul_assoc, hqAnc]
  refine ⟨subspaceStep_wrapDyn v pA ({qAnc} : Finset (Wire n))
      (.circuit cMid) R (cTgt.eval.1 * R)
    ⟨Finset.notMem_empty _, Finset.notMem_empty _, Finset.notMem_empty _,
        Finset.mem_singleton_self qAnc⟩
    (cleanProj_singleton_eq_projBit qAnc ▸ hqAnc) (cleanProj_singleton_eq_projBit qAnc ▸ hAncOut)
    (subspaceStep_congr_out (subspaceStep_of_circuit _ cMid) ?_), hAncOut⟩
  nth_rw 1 [← hqAnc]
  rw [show cMid.eval.1 * (F * (P * R)) = (cMid.eval.1 * F * P) * R by simp only [Matrix.mul_assoc],
    show cMid.eval.1 * F * P = F * cTgt.eval.1 * P from matrix_ext_ket fun β ↦ by
      simp only [F, P, ← Matrix.mulVec_mulVec, projBit_zero_mulVec_ket]
      rcases bit_cases (β qAnc) with h0 | h1
      · simp only [h0, ↓reduceIte, fwdCirc_mulVec_ket, pA, ComputeProg.fwdBits, zero_add]
        rw [show cMid.eval.1.mulVec (ket (Function.update β qAnc (β c₁ * β c₂))) =
              ket (xorConstList (β c₁ * β c₂) (tgtsT.map Subtype.val)
                  (Function.update β qAnc (β c₁ * β c₂))) by
            simpa [cMid, tgtsT, List.map_map, Function.comp_def, Function.update_self] using
              cnotPairs_from_src_mulVec_ket qAnc (tgts.map fun t ↦ ⟨t.1, t.2.2.2⟩)
                  (Function.update β qAnc (β c₁ * β c₂)),
          toffFanoutCirc_mulVec_ket c₁ c₂ h12 tgtsT β, fwdCirc_mulVec_ket, ComputeProg.fwdBits,
          xorConstList_of_not_mem _ _ _ _ fun _ hw ↦
              (hmem hw).2.2, xorConstList_of_not_mem _ _ _ _ fun _ hw ↦ (hmem hw).1,
          xorConstList_of_not_mem _ _ _ _ fun _ hw ↦ (hmem hw).2.1, h0, zero_add,
          xorConstList_update_comm _ _ _ _ fun _ hw ↦ (hmem hw).2.2.symm]
      · simp [h1],
    Matrix.mul_assoc, Matrix.mul_assoc, hqAnc]
/- ## Section 3: Zero-Boilerplate `PlaneReg M D n := QRegister (8 + 5 * D + 3 * M) n` -/

abbrev planeWidth (M D : ℕ) : ℕ := 8 + 5 * D + 3 * M
abbrev PlaneReg (M D n : ℕ) := QRegister (planeWidth M D) n
theorem pw_lt0 (M D : ℕ) : 0 < planeWidth M D := by unfold planeWidth; omega
theorem pw_lt1 (M D : ℕ) : 1 < planeWidth M D := by unfold planeWidth; omega
theorem pw_lt2 (M D : ℕ) : 2 < planeWidth M D := by unfold planeWidth; omega
theorem pw_lt3 (M D : ℕ) : 3 < planeWidth M D := by unfold planeWidth; omega
theorem pw_lt4 (M D : ℕ) : 4 < planeWidth M D := by unfold planeWidth; omega
theorem pw_lt5 (M D : ℕ) : 5 < planeWidth M D := by unfold planeWidth; omega
theorem pw_lt6 (M D : ℕ) : 6 < planeWidth M D := by unfold planeWidth; omega
theorem pw_lt7 (M D : ℕ) : 7 < planeWidth M D := by unfold planeWidth; omega
theorem pw_ltMsb {M D : ℕ} (d : Fin D) : 8 + d.val < planeWidth M D := by unfold planeWidth; omega
theorem pw_ltNMin {M D : ℕ} (d : Fin D) : 8 + D + d.val < planeWidth M D := by
  unfold planeWidth; omega
theorem pw_ltNMax {M D : ℕ} (d : Fin D) : 8 + 2 * D + d.val < planeWidth M D := by
  unfold planeWidth; omega
theorem pw_ltAMsb {M D : ℕ} (d : Fin D) : 8 + 3 * D + d.val < planeWidth M D := by
  unfold planeWidth; omega
theorem pw_ltCReg {M D : ℕ} (d : Fin D) : 8 + 4 * D + d.val < planeWidth M D := by
  unfold planeWidth; omega
theorem pw_ltCLo {M D : ℕ} (p : Fin M) : 8 + 5 * D + p.val < planeWidth M D := by
  unfold planeWidth; omega
theorem pw_ltCHi {M D : ℕ} (p : Fin M) : 8 + 5 * D + M + p.val < planeWidth M D := by
  unfold planeWidth; omega
theorem pw_ltSys {M D : ℕ} (p : Fin M) : 8 + 5 * D + 2 * M + p.val < planeWidth M D := by
  unfold planeWidth; omega
abbrev pHas1 {M D n : ℕ} (r : PlaneReg M D n) : Wire n := r ⟨0, pw_lt0 M D⟩
abbrev pHas2Eff {M D n : ℕ} (r : PlaneReg M D n) : Wire n := r ⟨1, pw_lt1 M D⟩
abbrev pOnly1 {M D n : ℕ} (r : PlaneReg M D n) : Wire n := r ⟨2, pw_lt2 M D⟩
abbrev pBufLo {M D n : ℕ} (r : PlaneReg M D n) : Wire n := r ⟨3, pw_lt3 M D⟩
abbrev pBufHi {M D n : ℕ} (r : PlaneReg M D n) : Wire n := r ⟨4, pw_lt4 M D⟩
abbrev pHA {M D n : ℕ} (r : PlaneReg M D n) : Wire n := r ⟨5, pw_lt5 M D⟩
abbrev pHB {M D n : ℕ} (r : PlaneReg M D n) : Wire n := r ⟨6, pw_lt6 M D⟩
abbrev pAnc {M D n : ℕ} (r : PlaneReg M D n) : Wire n := r ⟨7, pw_lt7 M D⟩
abbrev pUMsb {M D n : ℕ} (r : PlaneReg M D n) (d : Fin D) : Wire n := r ⟨8 + d.val, pw_ltMsb d⟩
abbrev pNotMin {M D n : ℕ} (r : PlaneReg M D n) (d : Fin D) : Wire n :=
    r ⟨8 + D + d.val, pw_ltNMin d⟩
abbrev pNotMax {M D n : ℕ} (r : PlaneReg M D n) (d : Fin D) : Wire n :=
    r ⟨8 + 2 * D + d.val, pw_ltNMax d⟩
abbrev pAMsb {M D n : ℕ} (r : PlaneReg M D n) (d : Fin D) : Wire n :=
    r ⟨8 + 3 * D + d.val, pw_ltAMsb d⟩
abbrev pCReg {M D n : ℕ} (r : PlaneReg M D n) (d : Fin D) : Wire n :=
    r ⟨8 + 4 * D + d.val, pw_ltCReg d⟩
abbrev pCtrlLo {M D n : ℕ} (r : PlaneReg M D n) (p : Fin M) : Wire n :=
    r ⟨8 + 5 * D + p.val, pw_ltCLo p⟩
abbrev pCtrlHi {M D n : ℕ} (r : PlaneReg M D n) (p : Fin M) : Wire n :=
    r ⟨8 + 5 * D + M + p.val, pw_ltCHi p⟩
abbrev pSys {M D n : ℕ} (r : PlaneReg M D n) (p : Fin M) : Wire n :=
    r ⟨8 + 5 * D + 2 * M + p.val, pw_ltSys p⟩
theorem pr_ne {M D n : ℕ} (r : PlaneReg M D n) {i j : Fin (planeWidth M D)} (h : i.val ≠ j.val) :
    r i ≠ r j :=
  fun heq ↦ h (congrArg Fin.val (r.wires.injective heq))
/-- Construct `WirePair n` explicitly (`0` inner-product notation ambiguity). -/
abbrev mkWP {n : ℕ} (u v : Wire n) (h : u ≠ v) : WirePair n :=
  Sigma.mk (β := fun w ↦ { t : Wire n // w ≠ t }) u (Subtype.mk v h)

-- Wire-distinctness witnesses (zero tactic proofs inside `def` bodies):
theorem pr_neOpt {M D n : ℕ} (r : PlaneReg M D n) {a b : ℕ}
    {ha : a < planeWidth M D} {hb : b < planeWidth M D} (h : a ≠ b) : r ⟨a, ha⟩ ≠ r ⟨b, hb⟩ :=
        pr_ne r h
theorem hne_AMsb_Hi {M D n : ℕ} (r : PlaneReg M D n) (d : Fin D) :
    pAMsb r d ≠ pBufHi r := pr_neOpt r (by omega)
theorem hne_Ctrl_HiLo {M D n : ℕ} (r : PlaneReg M D n) (p : Fin M) :
    pCtrlHi r p ≠ pCtrlLo r p := pr_neOpt r (by omega)
theorem hne_Hi_Sys {M D n : ℕ} (r : PlaneReg M D n) (p : Fin M) :
    pBufHi r ≠ pSys r p := pr_neOpt r (by omega)
theorem hne_Msb_Init {M D n : ℕ} (r : PlaneReg M D n) (d : Fin D) :
    pUMsb r d ≠ pHB r ∧ pUMsb r d ≠ pAnc r ∧ pHB r ≠ pAnc r ∧ pUMsb r d ≠ pAMsb r d ∧ pHB r ≠
        pAMsb r d ∧ pAnc r ≠ pAMsb r d :=
  let ne {a b} {ha : a < _} {hb : b < _} (h : a ≠ b := by omega) : r ⟨a, ha⟩ ≠ r ⟨b, hb⟩ :=
      pr_neOpt r h
  ⟨ne, ne, ne, ne, ne, ne⟩
attribute [local semireducible] DynQromUncompA.remeasureIf DynQromUncompA.wrapDyn
    DynQromUncompA.fwdCirc
/- ## Section 5: Disjoint-Support Dynamic Commutation (`ActsIndepOf` -> `CommutesWithDyn`) -/

/-- `U : Unitary (2 ^ n)` acts independently of every wire satisfying `S`. -/
def ActsIndepOf {n : ℕ} (S : Wire n → Prop) (U : Unitary (2 ^ n)) : Prop :=
    ∃ G : BitAssignment n → BitAssignment n, (∀ β, U.1.mulVec (ket β) = ket (G β)) ∧
    (∀ q, S q → ∀ β v, G (Function.update β q v) = Function.update (G β) q v)
theorem actsIndepOf_fix {n : ℕ} {S : Wire n → Prop} {G : BitAssignment n → BitAssignment n}
    (hG : ∀ q, S q → ∀ β v, G (Function.update β q v) = Function.update (G β) q v) {q : Wire n}
    (hq : S q) (β : BitAssignment n) : G β q = β q := by
  simpa [Function.update_eq_self] using congrFun (hG q hq β (β q)) q
/-- Predicate confirming every gate and measurement of `c` / `p` acts only on wires inside `S`. -/
def CircSupportedIn {n : ℕ} (S : Wire n → Prop) (c : Circuit n) : Prop :=
  ∀ U : Unitary (2 ^ n), ActsIndepOf S U → c.eval.1 * U.1 = U.1 * c.eval.1
/-- Predicate asserting every gate and measurement in a dynamic circuit lies in `S`. -/
def DynSupportedIn {Var : Type} {n : ℕ} (S : Wire n → Prop) : DynamicCircuit Var n → Prop
  | .circuit c => CircSupportedIn S c
  | .measure _ r => ∃ q : Wire n, S q ∧ r = QRegister.singleton q
  | @DynamicCircuit.qIf _ _ _ _ t f => DynSupportedIn S t ∧ DynSupportedIn S f
  | .seq p₁ p₂ => DynSupportedIn S p₁ ∧ DynSupportedIn S p₂
theorem commutesWithDyn_of_dynSupportedIn {Var : Type} {n : ℕ} {S : Wire n → Prop}
    {U : Unitary (2 ^ n)} (hU : ActsIndepOf S U) :
    ∀ {p : DynamicCircuit Var n}, DynSupportedIn S p → CommutesWithDyn U p := by
  intro p hp
  induction p with
  | circuit _ => exact hp U hU
  | measure _ _ =>
      rcases And.intro hp hU with ⟨⟨q, hq, rfl⟩, _, hUk, hG⟩
      exact fun o ↦ matrix_ext_ket fun β ↦ by
        rcases (by fin_cases o <;> simp : o = 0 ∨ o = 1) with rfl | rfl <;>
          simp only [← Matrix.mulVec_mulVec, hUk, ket_projector_zero, ket_projector_one,
              actsIndepOf_fix hG hq β] <;>
          split_ifs <;> simp [hUk]
  | qIf _ _ _ iht ihf => exact ⟨iht hp.1, ihf hp.2⟩
  | seq _ _ ih₁ ih₂ => exact ⟨ih₁ hp.1, ih₂ hp.2⟩
theorem circSupportedIn_id {n : ℕ} {S : Wire n → Prop} : CircSupportedIn S .identity :=
  fun _ _ ↦ by simp [Circuit.eval_identity]
theorem circSupportedIn_seq {n : ℕ} {S : Wire n → Prop} {c₁ c₂ : Circuit n}
    (h₁ : CircSupportedIn S c₁) (h₂ : CircSupportedIn S c₂) :
    CircSupportedIn S (c₁ ;;ᶜ c₂) := fun U hU ↦ by
  rw [Circuit.eval_seq, Submonoid.coe_mul, Matrix.mul_assoc, h₁ U hU, ← Matrix.mul_assoc, h₂ U hU,
      Matrix.mul_assoc]
theorem circSupportedIn_H {n : ℕ} {S : Wire n → Prop} {q : Wire n} (hq : S q) :
    CircSupportedIn S (Circuit.H q) := fun _ ⟨_, hUk, hG⟩ ↦ matrix_ext_ket fun β ↦ by
  simp only [← Matrix.mulVec_mulVec, hUk, ket_H, Matrix.mulVec_smul, Matrix.mulVec_add,
    actsIndepOf_fix hG hq β, hG q hq β 0, hG q hq β 1]
theorem circSupportedIn_CNOT {n : ℕ} {S : Wire n → Prop} {c t : Wire n} (h : c ≠ t)
    (hc : S c) (ht : S t) : CircSupportedIn S (Circuit.CNOT c t h) :=
  fun _ ⟨_, hUk, hG⟩ ↦ matrix_ext_ket fun β ↦ by
    simp only [← Matrix.mulVec_mulVec, hUk, ket_CNOT, actsIndepOf_fix hG hc β,
      actsIndepOf_fix hG ht β, hG t ht]
theorem singleton_embedMatrix_mulVec_ket_pub {n : ℕ} (q : Wire n) (A : Matrix (Fin 2) (Fin 2) ℂ)
    (β : BitAssignment n) : ((QRegister.singleton q).embedMatrix A).mulVec (ket β) =
    A 0 (if β q = 0 then 0 else 1) • ket (Function.update β q 0) +
    A 1 (if β q = 0 then 0 else 1) • ket (Function.update β q 1) := by
  have hw (l : Fin 2) (b : ZMod 2) (hb : basisBits 1 l = fun _ ↦ b) :
      DynCircExt.writeReg β (QRegister.singleton q) (basisBits 1 l) = Function.update β q b :=
    (DynCircExt.writeReg_eq_update _ _ _ 0 fun i hi ↦
        absurd (Subsingleton.elim i 0) hi).trans (congrArg _ (congrFun hb 0))
  rw [DynCircExt.embedMatrix_mulVec_ket,
      show DynCircExt.localIdx (QRegister.singleton q) β = if β q = 0 then 0 else 1 from
    (by decide : ∀ b : ZMod 2, ((basisBitsEquiv 1).symm (fun _ ↦ b) : Fin 2) = if b =
          0 then 0 else 1) (β q)]
  change ∑ l : Fin 2, _ = _
  rw [Fin.sum_univ_two, hw 0 0 (by decide), hw 1 1 (by decide)]
theorem circSupportedIn_single {n : ℕ} {S : Wire n → Prop} (g : PrimitiveGate 1)
    {q : Wire n} (hq : S q) : CircSupportedIn S (Circuit.single g q) :=
  fun U ⟨_, hUk, hG⟩ ↦ matrix_ext_ket fun β ↦ by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hUk, Circuit.eval_single,
        QRegister.embedUnitary_val]
    change ((QRegister.singleton q).embedMatrix g.eval.1).mulVec _ =
      U.1.mulVec (((QRegister.singleton q).embedMatrix g.eval.1).mulVec _)
    rw [singleton_embedMatrix_mulVec_ket_pub, singleton_embedMatrix_mulVec_ket_pub,
      Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hUk, hUk,
      actsIndepOf_fix hG hq β, hG q hq β 0, hG q hq β 1]
/-- Write-set of plane `r`: `{pBufLo r, pBufHi r, pHA r, pHB r} ∪ range (pSys r)`. -/
def PlaneModSet {M D n : ℕ} (r : PlaneReg M D n) (w : Wire n) : Prop :=
    w = pBufLo r ∨ w = pBufHi r ∨ w = pHA r ∨ w = pHB r ∨ ∃ p : Fin M, w = pSys r p
end QuantumComputation.Specs.PhotochemistrySolution.SplitRouterSeqBell26k

namespace QuantumComputation.Specs.PhotochemistrySolution.SplitRouter47_187
open PhotochemistrySolution.SplitRouterSeqBell26k
open _root_.DynamicCircuit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt hiding bit_cases
  eval_seq_mulVec ket ket_CNOT ket_TOFF ket_X ket_projector_one ket_projector_zero matrix_ext_ket
  qAssign_obs_map_val
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB hiding bitSign eval_seq_mulVec ket
  ket_CNOT ket_TOFF ket_X matrix_ext_ket writeReg writeReg_apply_of_not_mem
/-!
## Section 1: Exact Frozen `RouterReg M D n` Wire Layout (`routerWidth M D = 106 + 11 * D + 26 * M`)
-/

/--
Total local wire width of the `(M, D)` Dual-Bell sub-router (`1394` at `(47, 6)` , `5056` at
`(187, 8)` ).
-/
abbrev routerWidth (M D : ℕ) : ℕ := 106 + 11 * D + 26 * M
/-- Public + Bell + System wire prefix size (`98 + 2 * D + 24 * M`). -/
abbrev basePub (M D : ℕ) : ℕ := 98 + 2 * D + 24 * M
/-- Sub-router register alias over any ambient `n`-qubit state space (`0` call-site `≠` proofs!). -/
abbrev RouterReg (M D n : ℕ) := QRegister (routerWidth M D) n
theorem rw_lt0 (M D : ℕ) : 0 < routerWidth M D := by unfold routerWidth; omega
theorem rw_lt1 (M D : ℕ) : 1 < routerWidth M D := by unfold routerWidth; omega
theorem rw_ltIdx1 {M D : ℕ} (d : Fin D) : 2 + d.val < routerWidth M D := by
  unfold routerWidth; omega
theorem rw_ltIdx2 {M D : ℕ} (d : Fin D) : 2 + D + d.val < routerWidth M D := by
  unfold routerWidth; omega
theorem rw_ltBufLo (M D : ℕ) (b : Fin 24) : 2 + 2 * D + b.val < routerWidth M D := by
  unfold routerWidth; omega
theorem rw_ltBufHi (M D : ℕ) (b : Fin 24) : 26 + 2 * D + b.val < routerWidth M D := by
  unfold routerWidth; omega
theorem rw_ltHA (M D : ℕ) (b : Fin 24) : 50 + 2 * D + b.val < routerWidth M D := by
  unfold routerWidth; omega
theorem rw_ltHB (M D : ℕ) (b : Fin 24) : 74 + 2 * D + b.val < routerWidth M D := by
  unfold routerWidth; omega
theorem rw_ltSys {M D : ℕ} (p : Fin M) (b : Fin 24) :
    98 + 2 * D + 24 * p.val + b.val < routerWidth M D := by unfold routerWidth; omega
theorem rw_ltHas2Eff (M D : ℕ) : basePub M D + 1 < routerWidth M D := by
  unfold basePub routerWidth; omega
theorem rw_ltOnly1 (M D : ℕ) : basePub M D + 2 < routerWidth M D := by
  unfold basePub routerWidth; omega
theorem rw_ltNotMin {M D : ℕ} (d : Fin D) : basePub M D + 6 + d.val < routerWidth M D := by
  unfold basePub routerWidth; omega
theorem rw_ltNotMax {M D : ℕ} (d : Fin D) : basePub M D + 6 + D + d.val < routerWidth M D := by
  unfold basePub routerWidth; omega
theorem rw_ltCtrlLo {M D : ℕ} (p : Fin M) : basePub M D + 6 + 2 * D + p.val < routerWidth M D := by
  unfold basePub routerWidth; omega
theorem rw_ltCtrlHi {M D : ℕ} (p : Fin M) : basePub M D + 6 + 2 * D + M + p.val <
    routerWidth M D := by unfold basePub routerWidth; omega
theorem rw_ltUMsb {M D : ℕ} (d : Fin D) : basePub M D + 7 + 2 * D + 2 * M + d.val <
    routerWidth M D := by unfold basePub routerWidth; omega
theorem rw_ltDelta {M D : ℕ} (d : Fin D) : basePub M D + 7 + 4 * D + 2 * M + d.val <
    routerWidth M D := by unfold basePub routerWidth; omega
theorem rw_ltIdxMin {M D : ℕ} (d : Fin D) : basePub M D + 7 + 5 * D + 2 * M + d.val <
    routerWidth M D := by unfold basePub routerWidth; omega
theorem rw_ltIdxMax {M D : ℕ} (d : Fin D) : basePub M D + 7 + 6 * D + 2 * M + d.val <
    routerWidth M D := by unfold basePub routerWidth; omega
theorem rw_ltAMsb {M D : ℕ} (d : Fin D) : basePub M D + 7 + 7 * D + 2 * M + d.val <
    routerWidth M D := by unfold basePub routerWidth; omega
theorem rw_ltCReg {M D : ℕ} (d : Fin D) : basePub M D + 7 + 8 * D + 2 * M + d.val <
    routerWidth M D := by unfold basePub routerWidth; omega
theorem rw_ltAnc (M D : ℕ) : basePub M D + 7 + 9 * D + 2 * M < routerWidth M D := by
  unfold basePub routerWidth; omega
abbrev rHas1 {M D n : ℕ} (r : RouterReg M D n) : Wire n := r ⟨0, rw_lt0 M D⟩
abbrev rRawHas2 {M D n : ℕ} (r : RouterReg M D n) : Wire n := r ⟨1, rw_lt1 M D⟩
abbrev rIdx1 {M D n : ℕ} (r : RouterReg M D n) (d : Fin D) : Wire n := r ⟨2 + d.val, rw_ltIdx1 d⟩
abbrev rIdx2 {M D n : ℕ} (r : RouterReg M D n) (d : Fin D) : Wire n :=
    r ⟨2 + D + d.val, rw_ltIdx2 d⟩
abbrev rBufLo {M D n : ℕ} (r : RouterReg M D n) (b : Fin 24) : Wire n :=
    r ⟨2 + 2 * D + b.val, rw_ltBufLo M D b⟩
abbrev rBufHi {M D n : ℕ} (r : RouterReg M D n) (b : Fin 24) : Wire n :=
    r ⟨26 + 2 * D + b.val, rw_ltBufHi M D b⟩
abbrev rHA {M D n : ℕ} (r : RouterReg M D n) (b : Fin 24) : Wire n :=
    r ⟨50 + 2 * D + b.val, rw_ltHA M D b⟩
abbrev rHB {M D n : ℕ} (r : RouterReg M D n) (b : Fin 24) : Wire n :=
    r ⟨74 + 2 * D + b.val, rw_ltHB M D b⟩
abbrev rSys {M D n : ℕ} (r : RouterReg M D n) (p : Fin M) (b : Fin 24) : Wire n :=
    r ⟨98 + 2 * D + 24 * p.val + b.val, rw_ltSys p b⟩
abbrev rHas2Eff {M D n : ℕ} (r : RouterReg M D n) : Wire n := r ⟨basePub M D + 1, rw_ltHas2Eff M D⟩
abbrev rOnly1 {M D n : ℕ} (r : RouterReg M D n) : Wire n := r ⟨basePub M D + 2, rw_ltOnly1 M D⟩
abbrev rNotMin {M D n : ℕ} (r : RouterReg M D n) (d : Fin D) : Wire n :=
    r ⟨basePub M D + 6 + d.val, rw_ltNotMin d⟩
abbrev rNotMax {M D n : ℕ} (r : RouterReg M D n) (d : Fin D) : Wire n :=
    r ⟨basePub M D + 6 + D + d.val, rw_ltNotMax d⟩
abbrev rCtrlLo {M D n : ℕ} (r : RouterReg M D n) (p : Fin M) : Wire n :=
    r ⟨basePub M D + 6 + 2 * D + p.val, rw_ltCtrlLo p⟩
abbrev rCtrlHi {M D n : ℕ} (r : RouterReg M D n) (p : Fin M) : Wire n :=
    r ⟨basePub M D + 6 + 2 * D + M + p.val, rw_ltCtrlHi p⟩
abbrev rUMsb {M D n : ℕ} (r : RouterReg M D n) (d : Fin D) : Wire n :=
    r ⟨basePub M D + 7 + 2 * D + 2 * M + d.val, rw_ltUMsb d⟩
abbrev rDelta {M D n : ℕ} (r : RouterReg M D n) (d : Fin D) : Wire n :=
    r ⟨basePub M D + 7 + 4 * D + 2 * M + d.val, rw_ltDelta d⟩
abbrev rIdxMin {M D n : ℕ} (r : RouterReg M D n) (d : Fin D) : Wire n :=
    r ⟨basePub M D + 7 + 5 * D + 2 * M + d.val, rw_ltIdxMin d⟩
abbrev rIdxMax {M D n : ℕ} (r : RouterReg M D n) (d : Fin D) : Wire n :=
    r ⟨basePub M D + 7 + 6 * D + 2 * M + d.val, rw_ltIdxMax d⟩
abbrev rAMsb {M D n : ℕ} (r : RouterReg M D n) (d : Fin D) : Wire n :=
    r ⟨basePub M D + 7 + 7 * D + 2 * M + d.val, rw_ltAMsb d⟩
abbrev rCReg {M D n : ℕ} (r : RouterReg M D n) (d : Fin D) : Wire n :=
    r ⟨basePub M D + 7 + 8 * D + 2 * M + d.val, rw_ltCReg d⟩
abbrev rAnc {M D n : ℕ} (r : RouterReg M D n) : Wire n :=
    r ⟨basePub M D + 7 + 9 * D + 2 * M, rw_ltAnc M D⟩
theorem rr_ne {M D n : ℕ} (r : RouterReg M D n) {i j : Fin (routerWidth M D)} (h : i.val ≠ j.val) :
    r i ≠ r j :=
  fun heq ↦ h (congrArg Fin.val (r.wires.injective heq))
theorem rr_neOpt {M D n : ℕ} (r : RouterReg M D n) {a b : ℕ}
    {ha : a < routerWidth M D} {hb : b < routerWidth M D} (h : a ≠ b) : r ⟨a, ha⟩ ≠ r ⟨b, hb⟩ :=
        rr_ne r h
/--
Fixed-wire arm (`iv < 8`, balanced depth-3 binary `if` -tree -> `rfl` in 4 steps + instant
`split_ifs` ).
-/
def planeIdxFixed (M D : ℕ) (b : Fin 24) (iv : ℕ) : ℕ :=
  if iv < 4 then
    if iv < 2 then (if iv = 0 then 0 else basePub M D + 1)
    else (if iv = 2 then basePub M D + 2 else 2 + 2 * D + b.val)
  else
    if iv < 6 then (if iv = 4 then 26 + 2 * D + b.val else 50 + 2 * D + b.val)
    else (if iv = 6 then 74 + 2 * D + b.val else basePub M D + 7 + 9 * D + 2 * M)
/-- `D`-register arm (`8 ≤ iv < 8 + 5 * D`, 4 `if`s) of `planeIdxVal`. -/
def planeIdxD (M D iv : ℕ) : ℕ :=
  if iv < 8 + D then basePub M D + 7 + 2 * D + 2 * M + (iv - 8)
  else if iv < 8 + 2 * D then basePub M D + 6 + (iv - (8 + D))
  else if iv < 8 + 3 * D then basePub M D + 6 + D + (iv - (8 + 2 * D))
  else if iv < 8 + 4 * D then basePub M D + 7 + 7 * D + 2 * M + (iv - (8 + 3 * D))
  else basePub M D + 7 + 8 * D + 2 * M + (iv - (8 + 4 * D))
/-- `M`-register arm (`8 + 5 * D ≤ iv`, 2 `if`s) of `planeIdxVal`. -/
def planeIdxM (M D : ℕ) (b : Fin 24) (iv : ℕ) : ℕ :=
  if iv < 8 + 5 * D + M then basePub M D + 6 + 2 * D + (iv - (8 + 5 * D))
  else if iv < 8 + 5 * D + 2 * M then basePub M D + 6 + 2 * D + M + (iv - (8 + 5 * D + M))
  else 98 + 2 * D + 24 * (iv - (8 + 5 * D + 2 * M)) + b.val
/--
Map local plane wire index `i : Fin (planeWidth M D)` for bit-plane `b : Fin 24` into
`Fin (routerWidth M D)` .
-/
def planeIdxVal (M D : ℕ) (b : Fin 24) (iv : ℕ) : ℕ :=
    if iv < 8 then planeIdxFixed M D b iv else if iv < 8 + 5 *
    D then planeIdxD M D iv else planeIdxM M D b iv
theorem planeIdxVal_lt {M D : ℕ} (b : Fin 24) (i : Fin (planeWidth M D)) : planeIdxVal M D b i.val <
    routerWidth M D := by
  have hi := i.isLt; have _ := b.isLt
  unfold planeWidth at hi
  unfold planeIdxVal planeIdxFixed planeIdxD planeIdxM basePub routerWidth; split_ifs <;> omega
theorem planeIdx_inj_ff_rtrPrepA {M D : ℕ} (b : Fin 24) {x y : ℕ} (hx : x < 8) (hy : y < 8)
    (h : planeIdxFixed M D b x = planeIdxFixed M D b y) : x = y := by
  have _ := b.isLt; unfold planeIdxFixed basePub at h; split_ifs at h <;> omega
theorem planeIdx_ne_fd_rtrPrepA {M D : ℕ} (b : Fin 24) {x y : ℕ} (hy0 : ¬ y < 8)
    (hy1 : y < 8 + 5 * D) : planeIdxFixed M D b x ≠ planeIdxD M D y := fun h ↦ by
  have _ := b.isLt; unfold planeIdxFixed planeIdxD basePub at h; split_ifs at h <;> omega
theorem planeIdx_ne_fm_rtrPrepA {M D : ℕ} (b : Fin 24) {x y : ℕ} (hy0 : ¬ y < 8 + 5 * D)
    (hy1 : y < 8 + 5 * D + 3 * M) : planeIdxFixed M D b x ≠ planeIdxM M D b y := fun h ↦ by
  have _ := b.isLt; unfold planeIdxFixed planeIdxM basePub at h; split_ifs at h <;> omega
theorem planeIdx_inj_hi_rtrPrepA {M D : ℕ} (b : Fin 24) {x y : ℕ} (hx0 : ¬ x < 8)
    (hx : x < 8 + 5 * D + 3 * M) (hy0 : ¬ y < 8) (hy : y < 8 + 5 * D + 3 * M)
    (h : (if x < 8 + 5 * D then planeIdxD M D x else planeIdxM M D b x) = (if y < 8 + 5 *
    D then planeIdxD M D y else planeIdxM M D b y)) : x = y := by
  have _ := b.isLt; unfold planeIdxD planeIdxM basePub at h; split_ifs at h <;> omega
theorem planeIdxMap_injective {M D : ℕ} (b : Fin 24) :
    Function.Injective (fun i : Fin (planeWidth M D) ↦
      (⟨planeIdxVal M D b i.val, planeIdxVal_lt b i⟩ : Fin (routerWidth M D))) := fun i j hij ↦ by
  have h : planeIdxVal M D b i.val = planeIdxVal M D b j.val := congrArg Fin.val hij
  have ne_f {x y} (hy8 : ¬ y < 8) (hy : y < 8 + 5 * D + 3 * M)
      (he : planeIdxFixed M D b x = if y < 8 + 5 * D then planeIdxD M D y else planeIdxM M D b y) :
          False := by
    split_ifs at he with hy5
    · exact planeIdx_ne_fd_rtrPrepA b hy8 hy5 he
    · exact planeIdx_ne_fm_rtrPrepA b hy5 hy he
  unfold planeIdxVal at h
  by_cases hi8 : i.val < 8 <;> by_cases hj8 : j.val < 8 <;> simp only [hi8, hj8, ↓reduceIte] at h
  · exact Fin.ext (planeIdx_inj_ff_rtrPrepA b hi8 hj8 h)
  · exact (ne_f hj8 j.isLt h).elim
  · exact (ne_f hi8 i.isLt h.symm).elim
  · exact Fin.ext (planeIdx_inj_hi_rtrPrepA b hi8 i.isLt hj8 j.isLt h)
/-- Projected single-bit-plane register `PlaneReg M D n` for coordinate bit `b : Fin 24`. -/
def planeOfRouter {M D n : ℕ} (r : RouterReg M D n) (b : Fin 24) : PlaneReg M D n :=
    ⟨⟨fun i ↦ r ⟨planeIdxVal M D b i.val, planeIdxVal_lt b i⟩, fun _ _ hij ↦
    planeIdxMap_injective b (r.wires.injective hij)⟩⟩
@[simp] theorem planeOfRouter_has1 {M D n : ℕ} (r : RouterReg M D n) (b : Fin 24) :
    pHas1 (planeOfRouter r b) = rHas1 r := rfl
@[simp] theorem planeOfRouter_has2Eff {M D n : ℕ} (r : RouterReg M D n) (b : Fin 24) :
    pHas2Eff (planeOfRouter r b) = rHas2Eff r := rfl
@[simp] theorem planeOfRouter_only1 {M D n : ℕ} (r : RouterReg M D n) (b : Fin 24) :
    pOnly1 (planeOfRouter r b) = rOnly1 r := rfl
@[simp] theorem planeOfRouter_bufLo {M D n : ℕ} (r : RouterReg M D n) (b : Fin 24) :
    pBufLo (planeOfRouter r b) = rBufLo r b := rfl
@[simp] theorem planeOfRouter_bufHi {M D n : ℕ} (r : RouterReg M D n) (b : Fin 24) :
    pBufHi (planeOfRouter r b) = rBufHi r b := rfl
@[simp] theorem planeOfRouter_hA {M D n : ℕ} (r : RouterReg M D n) (b : Fin 24) :
    pHA (planeOfRouter r b) = rHA r b := rfl
@[simp] theorem planeOfRouter_hB {M D n : ℕ} (r : RouterReg M D n) (b : Fin 24) :
    pHB (planeOfRouter r b) = rHB r b := rfl
@[simp] theorem planeOfRouter_anc {M D n : ℕ} (r : RouterReg M D n) (b : Fin 24) :
    pAnc (planeOfRouter r b) = rAnc r := rfl
theorem por_eq {M D n : ℕ} (r : RouterReg M D n) (b : Fin 24)
    {iv jv : ℕ} {hi : iv < planeWidth M D} {hj : jv < routerWidth M D}
    (h : (if iv < 8 then planeIdxFixed M D b iv else if iv < 8 + 5 *
        D then planeIdxD M D iv else planeIdxM M D b iv) = jv) :
    planeOfRouter r b ⟨iv, hi⟩ = r ⟨jv, hj⟩ := congrArg r.wires (Fin.ext h)
theorem planeOfRouter_uMsb {M D n : ℕ} (r : RouterReg M D n) (b : Fin 24)
    (d : Fin D) : pUMsb (planeOfRouter r b) d = rUMsb r d :=
  por_eq r b (by unfold planeIdxD; split_ifs <;> omega)
theorem planeOfRouter_notMin {M D n : ℕ} (r : RouterReg M D n) (b : Fin 24)
    (d : Fin D) : pNotMin (planeOfRouter r b) d = rNotMin r d :=
  por_eq r b (by unfold planeIdxD; split_ifs <;> omega)
theorem planeOfRouter_notMax {M D n : ℕ} (r : RouterReg M D n) (b : Fin 24) :
    ∀ d : Fin D, pNotMax (planeOfRouter r b) d = rNotMax r d :=
  fun _ ↦ por_eq r b (by unfold planeIdxD; split_ifs <;> omega)
theorem planeOfRouter_aMsb {M D n : ℕ} (r : RouterReg M D n) (b : Fin 24)
    (d : Fin D) : pAMsb (planeOfRouter r b) d = rAMsb r d :=
  por_eq r b (by unfold planeIdxD; split_ifs <;> omega)
theorem planeOfRouter_cReg {M D n : ℕ} (r : RouterReg M D n) (b : Fin 24)
    (d : Fin D) : pCReg (planeOfRouter r b) d = rCReg r d :=
  por_eq r b (by unfold planeIdxD; split_ifs <;> omega)
theorem planeOfRouter_ctrlLo {M D n : ℕ} (r : RouterReg M D n)
    (b : Fin 24) : pCtrlLo (planeOfRouter r b) = rCtrlLo r :=
  funext fun _ ↦ por_eq r b (by unfold planeIdxM; split_ifs <;> omega)
theorem planeOfRouter_ctrlHi {M D n : ℕ} (r : RouterReg M D n)
    (b : Fin 24) : pCtrlHi (planeOfRouter r b) = rCtrlHi r :=
  funext fun _ ↦ por_eq r b (by unfold planeIdxM; split_ifs <;> omega)
theorem planeOfRouter_sys {M D n : ℕ} (r : RouterReg M D n) (b : Fin 24)
    (p : Fin M) : pSys (planeOfRouter r b) p = rSys r p b :=
  por_eq r b (by unfold planeIdxM; split_ifs <;> omega)
theorem planeModSet_disj_planeOfRouter {M D n : ℕ} (r : RouterReg M D n) (b₁ b₂ : Fin 24)
    (hb : b₁ ≠ b₂) :
    ∀ w : Wire n, PlaneModSet (planeOfRouter r b₁) w →
        w ∉ Set.range (planeOfRouter r b₂).wires := by
  have hbne := Fin.val_ne_of_ne hb
  have neV {j : Fin (routerWidth M D)} {i₂ : Fin (planeWidth M D)}
      (hi₂ : planeOfRouter r b₂ i₂ = r j)
      (hk : j.val = 2 + 2 * D + b₁.val ∨ j.val = 26 + 2 * D + b₁.val ∨ j.val = 50 + 2 * D + b₁.val ∨
        j.val = 74 + 2 * D + b₁.val ∨ ∃ p : Fin M, j.val = 98 + 2 * D + 24 * p.val + b₁.val) :
            False := by
    have heq : planeIdxVal M D b₂ i₂.val = j.val := congrArg Fin.val (r.wires.injective hi₂)
    have hi2 := i₂.isLt
    unfold planeWidth at hi2
    unfold planeIdxVal planeIdxFixed planeIdxD planeIdxM basePub at heq
    rcases hk with h | h | h | h | ⟨p, h⟩ <;> (try have _ := p.isLt) <;> split_ifs at heq <;> omega
  rintro w (rfl | rfl | rfl | rfl | ⟨p, rfl⟩) ⟨i₂, hi₂⟩
  · exact neV hi₂ (.inl rfl)
  · exact neV hi₂ (.inr (.inl rfl))
  · exact neV hi₂ (.inr (.inr (.inl rfl)))
  · exact neV hi₂ (.inr (.inr (.inr (.inl rfl))))
  · exact neV (planeOfRouter_sys r b₁ p ▸ hi₂) (.inr (.inr (.inr (.inr ⟨p, rfl⟩))))

attribute [local semireducible] DynQromUncompA.remeasureIf DynQromUncompA.wrapDyn
    DynQromUncompA.fwdCirc ComputeProg.ValidProg ComputeProg.finalClean ComputeProg.fwdBits
theorem itePos {p : Prop} [Decidable p] {α : Type*} {a b : α} (h : p) : (if p then a else b) = a :=
    ite_eq_left h
theorem iteNeg {p : Prop} [Decidable p] {α : Type*} {a b : α} (h : ¬ p) : (if p then a else b) =
    b := ite_eq_right h
theorem ditePos {p : Prop} [Decidable p] {α : Type*} {a : p → α} {b : ¬ p → α}
    (h : p) : (if hp : p then a hp else b hp) = a h := dite_eq_left h
theorem diteNeg {p : Prop} [Decidable p] {α : Type*} {a : p → α} {b : ¬ p → α} (h : ¬ p) :
    (if hp : p then a hp else b hp) = b h := dite_eq_right h
/--
Full private-scratch `Finset` (`basePub M D ≤ i.val`, all `8 + 9 * D + 2 * M` internal wires).
-/
def sPrivCleanSet {M D n : ℕ} (r : RouterReg M D n) : Finset (Wire n) :=
    (Finset.univ.filter (fun i : Fin (routerWidth M D) ↦ basePub M D ≤ i.val)).image r.wires
theorem mem_sPrivCleanSet_iff {M D n : ℕ} (r : RouterReg M D n) (i : Fin (routerWidth M D)) :
    r i ∈ sPrivCleanSet r ↔ basePub M D ≤ i.val := by
  simp only [sPrivCleanSet, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun ⟨j, hj, heq⟩ ↦ r.wires.injective heq ▸ hj, fun hi ↦ ⟨i, hi, rfl⟩⟩
end QuantumComputation.Specs.PhotochemistrySolution.SplitRouter47_187
end

-- Catalyst-disjoint shift, router wire disjointness, and particle-exchange symmetry lemmas.
namespace QuantumComputation.Specs.PhotochemistrySolution.RouterSelectWiringA

private theorem qreg_bwv_gridSelectSup {n : ℕ} (o w : ℕ) (h : o + w ≤ n) (i : Fin w) :
    (_root_.QRegister.block o w h).wires i = ⟨o + i.val, by omega⟩ := rfl
open Operator QProg Matrix Circuit Qubit PrimitiveGate DynamicCircuit
  PhotochemistrySolution.SelectCompactAnc PhotochemistrySolution.SelectCompactRot34
  PhotochemistrySolution.SelectFastFlags PhotochemistrySolution.SplitRouter47_187
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
  _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB hiding writeReg
  writeReg_apply_of_not_mem ket ket_X ket_CNOT ket_TOFF matrix_ext_ket bitSign
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SelectQft8GidneyStg3 (Qft8Stg3ValidP
    qft8Stg3Clean13)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.TopSelectBridge (scrSubLGen lcuSubLGen)
local instance (priority := 100000) {k : ℕ} : NeZero (2 ^ k) := ⟨pow_ne_zero k two_ne_zero⟩
/-! ## Section 1: Master Layout Dimensions & Contiguous Non-Overlapping Wire Map -/

def mLayout : ℕ := 80
def scrLLayout : ℕ := 1565
def scrWLayout : ℕ := 1577
def offKinLayout : ℕ := 433
theorem hpLayout : scrLLayout + (mLayout + 2) ≤ scrWLayout + 70 := by decide
theorem hoffKinLayout : 1 ≤ offKinLayout ∧ offKinLayout + 21 ≤ scrWLayout := by decide
theorem hSys5616 : systemQubits_frozen = 5616 := by decide
theorem hNW1394 : routerWidth 47 6 = 1394 := by decide
theorem hEW5056 : routerWidth 187 8 = 5056 := by decide
abbrev dLayout : ℕ := totDimCompactGen scrWLayout
abbrev rSysLayout : QRegister systemQubits_frozen dLayout := locSysCompactGen scrWLayout
abbrev rAncLayout : QRegister (ancWOfScr scrWLayout) dLayout := locAncCompactGen scrWLayout
abbrev wLocQLayout : Wire dLayout := locQCompactGen scrWLayout
abbrev rScrLayout : QRegister scrLLayout dLayout := rAncLayout.compose (scrSubLGen hpLayout)
abbrev rLcu82Layout : QRegister (mLayout + 2) dLayout := rAncLayout.compose (lcuSubLGen hpLayout)
def rOuter41Layout : QRegister 41 dLayout :=
  rLcu82Layout.compose (QRegister.block 0 41 (by dsimp [mLayout]; omega))
def rInner41Layout : QRegister 41 dLayout :=
  rLcu82Layout.compose (QRegister.block 41 41 (by dsimp [mLayout]; omega))
theorem val_rSysLayout (i : Fin systemQubits_frozen) : (rSysLayout i).val = i.val := by
  dsimp [rSysLayout, locSysCompactGen, qreg_bwv_gridSelectSup, QRegister.block_apply_val];
  omega
theorem val_rScrLayout (i : Fin scrLLayout) : (rScrLayout i).val = 5650 + i.val := by
  dsimp [rScrLayout, rAncLayout, scrSubLGen, locAncCompactGen, QRegister.compose,
      qreg_bwv_gridSelectSup, QRegister.block_apply_val]; rw [hSys5616]; omega
theorem val_rLcu82Layout (i : Fin (mLayout + 2)) : (rLcu82Layout i).val = 7215 + i.val := by
  dsimp [rLcu82Layout, rAncLayout, lcuSubLGen, locAncCompactGen, QRegister.compose,
      qreg_bwv_gridSelectSup, QRegister.block_apply_val, scrLLayout]; rw [hSys5616];
      omega
theorem val_rOuter41Layout (k : Fin 41) : (rOuter41Layout k).val = 7215 + k.val := by
  dsimp [rOuter41Layout, QRegister.compose, qreg_bwv_gridSelectSup, QRegister.block_apply_val,
      scrLLayout]; rw [hSys5616]; omega
theorem val_rInner41Layout (k : Fin 41) : (rInner41Layout k).val = 7256 + k.val := by
  dsimp [rInner41Layout, QRegister.compose, qreg_bwv_gridSelectSup, QRegister.block_apply_val,
      scrLLayout]; rw [hSys5616]; omega
theorem val_wLocQLayout : wLocQLayout.val = 7297 :=
  show systemQubits_frozen + (34 + scrWLayout + 70) = 7297 by rw [hSys5616]; rfl
def rOut40Layout : QRegister 40 dLayout :=
  rScrLayout.compose (QRegister.block 65 40 (by dsimp [scrLLayout]; omega))
theorem val_rOut40Layout (j : Fin 40) : (rOut40Layout j).val = 5715 + j.val := by
  dsimp [rOut40Layout, QRegister.compose, qreg_bwv_gridSelectSup,
      QRegister.block_apply_val]; rw [hSys5616]; omega
abbrev wHasN1 : Wire dLayout := rOut40Layout ⟨0, by omega⟩
abbrev wRawHasN2 : Wire dLayout := rOut40Layout ⟨1, by omega⟩
abbrev wHasE1 : Wire dLayout := rOut40Layout ⟨14, by omega⟩
abbrev wRawHasE2 : Wire dLayout := rOut40Layout ⟨15, by omega⟩
abbrev wIsFine : Wire dLayout := rOut40Layout ⟨33, by omega⟩
abbrev wIsKin : Wire dLayout := rOut40Layout ⟨34, by omega⟩
abbrev wAxis0 : Wire dLayout := rOut40Layout ⟨38, by omega⟩
abbrev wAxis1 : Wire dLayout := rOut40Layout ⟨39, by omega⟩
def nucRouterWireFn (j : Fin (routerWidth 47 6)) : Wire dLayout :=
  if _ : j.val < 14 then rScrLayout ⟨65 + j.val, by dsimp [scrLLayout]; omega⟩
  else if _ : j.val < 110 then rScrLayout ⟨105 + (j.val - 14), by dsimp [scrLLayout]; omega⟩
  else if _ : j.val < 1238 then rSysLayout ⟨j.val - 110, by rw [hSys5616]; omega⟩
  else
    have _ : j.val < 1394 := hNW1394 ▸ j.isLt
    rScrLayout ⟨433 + (j.val - 1238), by dsimp [scrLLayout]; omega⟩
theorem val_nucRouterWireFn (j : Fin (routerWidth 47 6)) : (nucRouterWireFn j).val = if j.val <
    14 then 5715 + j.val else if j.val < 110 then 5755 + (j.val - 14) else if j.val <
    1238 then j.val - 110 else 6083 + (j.val - 1238) := by
  have _ : j.val < 1394 := hNW1394 ▸ j.isLt
  dsimp only [nucRouterWireFn]
  split_ifs <;> simp only [val_rScrLayout, val_rSysLayout] <;> omega
def rNucLayout : RouterReg 47 6 dLayout :=
  ⟨⟨nucRouterWireFn, fun a b h ↦ by
    have _ : a.val < 1394 := hNW1394 ▸ a.isLt; have _ : b.val < 1394 := hNW1394 ▸ b.isLt;
    have hv := congrArg Fin.val h; rw [val_nucRouterWireFn, val_nucRouterWireFn] at hv
    split_ifs at hv <;> exact Fin.ext (by omega)⟩⟩
def elecRouterWireFn (j : Fin (routerWidth 187 8)) : Wire dLayout :=
  if _ : j.val < 18 then rScrLayout ⟨79 + j.val, by dsimp [scrLLayout]; omega⟩
  else if _ : j.val < 114 then rScrLayout ⟨201 + (j.val - 18), by dsimp [scrLLayout]; omega⟩
  else if _ : j.val < 4602 then rSysLayout ⟨1128 + (j.val - 114), by rw [hSys5616]; omega⟩
  else
    have _ : j.val < 5056 := hEW5056 ▸ j.isLt
    rScrLayout ⟨433 + (j.val - 4602), by dsimp [scrLLayout]; omega⟩
theorem val_elecRouterWireFn (j : Fin (routerWidth 187 8)) : (elecRouterWireFn j).val = if j.val <
    18 then 5729 + j.val else if j.val < 114 then 5851 + (j.val - 18) else if j.val <
    4602 then 1128 + (j.val - 114) else 6083 + (j.val - 4602) := by
  have _ : j.val < 5056 := hEW5056 ▸ j.isLt
  dsimp only [elecRouterWireFn]
  split_ifs <;> simp only [val_rScrLayout, val_rSysLayout] <;> omega
def rElecLayout : RouterReg 187 8 dLayout :=
  ⟨⟨elecRouterWireFn, fun a b h ↦ by
    have _ : a.val < 5056 := hEW5056 ▸ a.isLt; have _ : b.val < 5056 := hEW5056 ▸ b.isLt;
    have hv := congrArg Fin.val h; rw [val_elecRouterWireFn, val_elecRouterWireFn] at hv
    split_ifs at hv <;> exact Fin.ext (by omega)⟩⟩
theorem val_rNuc_bounds (j : Fin (routerWidth 47 6)) : (rNucLayout j).val < 1128 ∨
    (5715 ≤ (rNucLayout j).val ∧ (rNucLayout j).val ≤ 5728) ∨ (5755 ≤ (rNucLayout j).val ∧
    (rNucLayout j).val ≤ 5850) ∨ (6083 ≤ (rNucLayout j).val ∧ (rNucLayout j).val ≤ 6238) := by
  have _ : j.val < 1394 := hNW1394 ▸ j.isLt
  rw [show (rNucLayout j).val = _ from val_nucRouterWireFn j]; split_ifs <;> omega
theorem val_rElec_bounds (j : Fin (routerWidth 187 8)) : (1128 ≤ (rElecLayout j).val ∧
    (rElecLayout j).val < 5616) ∨ (5729 ≤ (rElecLayout j).val ∧ (rElecLayout j).val ≤ 5746) ∨
    (5851 ≤ (rElecLayout j).val ∧ (rElecLayout j).val ≤ 5946) ∨ (6083 ≤ (rElecLayout j).val ∧
    (rElecLayout j).val ≤ 6536) := by
  have _ : j.val < 5056 := hEW5056 ▸ j.isLt
  rw [show (rElecLayout j).val = _ from val_elecRouterWireFn j]; split_ifs <;> omega
def rAlignLayout : QRegister 136 dLayout :=
  rScrLayout.compose (QRegister.block 297 136 (by dsimp [scrLLayout]; omega))
theorem val_rAlignLayout (k : Fin 136) : (rAlignLayout k).val = 5947 + k.val := by
  dsimp [rAlignLayout, QRegister.compose, qreg_bwv_gridSelectSup,
      QRegister.block_apply_val]; rw [hSys5616]; omega
abbrev rXorNuc (d : Fin 6) : Wire dLayout := rAlignLayout ⟨d.val, by omega⟩
abbrev rEqNucChain (d : Fin 6) : Wire dLayout := rAlignLayout ⟨6 + d.val, by omega⟩
abbrev wEqNuc : Wire dLayout := rAlignLayout ⟨11, by omega⟩
abbrev rCoord1Align (b : Fin 24) : Wire dLayout := rAlignLayout ⟨12 + b.val, by omega⟩
abbrev wIsMixed : Wire dLayout := rAlignLayout ⟨36, by omega⟩
abbrev rFineT (b : Fin 24) : Wire dLayout := rAlignLayout ⟨37 + b.val, by omega⟩
abbrev pFineA (b : Fin 24) : Wire dLayout := rAlignLayout ⟨61 + b.val, by omega⟩
abbrev pFineB (b : Fin 24) : Wire dLayout := rAlignLayout ⟨85 + b.val, by omega⟩
abbrev wKinAxis0 : Wire dLayout := rAlignLayout ⟨109, by omega⟩
abbrev wKinAxis1 : Wire dLayout := rAlignLayout ⟨110, by omega⟩
abbrev wIsElecKin : Wire dLayout := rAlignLayout ⟨111, by omega⟩
abbrev wIsFineCopy : Wire dLayout := rAlignLayout ⟨135, by omega⟩
def rCoordLayout : Fin 4 → Fin 24 → Wire dLayout
  | ⟨0, _⟩, b => rBufLo rNucLayout b
  | ⟨1, _⟩, b => rCoord1Align b
  | ⟨2, _⟩, b => rBufLo rElecLayout b
  | ⟨3, _⟩, b => rBufHi rElecLayout b
theorem val_rCoordLayout (p : Fin 4) (b : Fin 24) : (rCoordLayout p b).val = if p.val =
    0 then 5755 + b.val else if p.val = 1 then 5959 + b.val else if p.val = 2 then 5851 +
    b.val else 5875 + b.val := by
  have _ := b.isLt
  fin_cases p <;> dsimp [rCoordLayout, rBufLo, rBufHi, rCoord1Align] <;>
    simp only [show ∀ k, (rNucLayout k).val = _ from val_nucRouterWireFn,
      show ∀ k, (rElecLayout k).val = _ from val_elecRouterWireFn, val_rAlignLayout] <;>
    (try split_ifs) <;> omega
def rWorkInnerLayout : QRegister 521 dLayout :=
  rScrLayout.compose (QRegister.block 433 521 (by dsimp [scrLLayout]; omega))
theorem val_rWorkInnerLayout (k : Fin 521) : (rWorkInnerLayout k).val = 6083 + k.val := by
  dsimp [rWorkInnerLayout, QRegister.compose, qreg_bwv_gridSelectSup,
      QRegister.block_apply_val]; rw [hSys5616]; omega
theorem qft8Stg3Clean13_eq_workInner (i : Fin 13) :
    qft8Stg3Clean13 scrWLayout offKinLayout hoffKinLayout i = rWorkInnerLayout ⟨i.val, by omega⟩ :=
  Fin.ext (by
    simp only [qft8Stg3Clean13, QRegister.slice_apply, locAncCompactGen, QRegister.block_apply_val,
      offKinLayout, val_rWorkInnerLayout, hSys5616]; dsimp; omega)
def mux27WireFn (j : Fin 27) : Wire dLayout :=
  if _ : j.val < 2 then rAlignLayout ⟨109 + j.val, by omega⟩
  else if _ : j.val < 26 then rBufLo rNucLayout ⟨j.val - 2, by omega⟩
  else rWorkInnerLayout ⟨21, by omega⟩
theorem val_mux27WireFn (j : Fin 27) : (mux27WireFn j).val = if j.val < 2 then 6056 +
    j.val else if j.val < 26 then 5755 + (j.val - 2) else 6104 := by
  have _ := j.isLt
  dsimp [mux27WireFn, rBufLo]
  split_ifs <;> simp only [val_rAlignLayout, show ∀ k, (rNucLayout k).val =
      _ from val_nucRouterWireFn, val_rWorkInnerLayout] <;>
    (try dsimp) <;> (try split_ifs) <;> omega
def rMux27Layout : QRegister 27 dLayout :=
  ⟨⟨mux27WireFn, fun a b h ↦ by
    have hv := congrArg Fin.val h; rw [val_mux27WireFn, val_mux27WireFn] at hv
    split_ifs at hv <;> exact Fin.ext (by omega)⟩⟩
def speciesSwap50WireFn (j : Fin 50) : Wire dLayout :=
  if _ : j.val = 0 then wIsElecKin
  else if _ : j.val < 25 then rBufLo rNucLayout ⟨j.val - 1, by omega⟩
  else if _ : j.val < 49 then rBufLo rElecLayout ⟨j.val - 25, by omega⟩
  else rWorkInnerLayout ⟨21, by omega⟩
theorem val_speciesSwap50WireFn (j : Fin 50) : (speciesSwap50WireFn j).val = if j.val =
    0 then 6058 else if j.val < 25 then 5755 + (j.val - 1) else if j.val < 49 then 5851 +
    (j.val - 25) else 6104 := by
  have _ := j.isLt
  dsimp [speciesSwap50WireFn, wIsElecKin, rBufLo]
  split_ifs <;> simp only [val_rAlignLayout, show ∀ k, (rNucLayout k).val =
      _ from val_nucRouterWireFn,
    show ∀ k, (rElecLayout k).val = _ from val_elecRouterWireFn, val_rWorkInnerLayout] <;>
    (try dsimp) <;> (try split_ifs) <;> omega
def rSpeciesSwap50Layout : QRegister 50 dLayout :=
  ⟨⟨speciesSwap50WireFn, fun a b h ↦ by
    have hv := congrArg Fin.val h; rw [val_speciesSwap50WireFn, val_speciesSwap50WireFn] at hv
    split_ifs at hv <;> exact Fin.ext (by omega)⟩⟩
theorem val_rPKin_aux (k : Fin 8) : (rBufLo rNucLayout ⟨k.val, by omega⟩).val = 5755 + k.val := by
  change (nucRouterWireFn ⟨14 + k.val, _⟩).val = _
  rw [val_nucRouterWireFn]; dsimp; split_ifs <;> omega
def rPKinLayout : QRegister 8 dLayout :=
  ⟨⟨fun k ↦ rBufLo rNucLayout ⟨k.val, by omega⟩, fun a b h ↦ by
    have hv := congrArg Fin.val h; rw [val_rPKin_aux, val_rPKin_aux] at hv
    exact Fin.ext (by omega)⟩⟩
theorem val_rPKinLayout (k : Fin 8) : (rPKinLayout k).val = 5755 + k.val := val_rPKin_aux k
theorem qft8Stg3ValidP_layout : Qft8Stg3ValidP scrWLayout offKinLayout rPKinLayout := fun k ↦
  ⟨⟨34 + (105 + k.val), by dsimp [ancWOfScr, scrWLayout]; omega⟩,
   Fin.ext
       (by rw [val_rPKinLayout]; dsimp [locAncCompactGen, qreg_bwv_gridSelectSup,
             QRegister.block_apply_val];
             rw [hSys5616]; omega), by dsimp; omega, by dsimp [offKinLayout]; omega⟩
end QuantumComputation.Specs.PhotochemistrySolution.RouterSelectWiringA

-- bridging 41-bit Stage-1 coin multiplicities + 30-bit fine spline expectations to
-- vImplFineGen;
namespace QuantumComputation.Specs.PhotochemistrySolution.RouterSelectWiringB
open Operator QProg Matrix Circuit Qubit PrimitiveGate DynamicCircuit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
  _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt
open PhotochemistrySolution.ClusterPotSlice
  PhotochemistrySolution.SelectOracles
open PhotochemistrySolution.RouterSelectWiringA
/-- Split `BitAssignment (m + r)` into low `m` bits and high `r` bits (`0` WHNF expansion). -/
theorem sum_split_bits (m r : ℕ) (h : BitAssignment m → ℂ) :
    (∑ z : BitAssignment (m + r), h (fun b : Fin m ↦ z ⟨b.val, by omega⟩)) =
      (2 ^ r : ℂ) * ∑ u : BitAssignment m, h u := by
  let e : BitAssignment m × BitAssignment r ≃ BitAssignment (m + r) :=
    ⟨fun p k ↦ if hk : k.val < m then p.1 ⟨k.val, hk⟩ else p.2 ⟨k.val - m, by omega⟩,
     fun z ↦ (fun b ↦ z ⟨b.val, by omega⟩, fun t ↦ z ⟨m + t.val, by omega⟩),
     fun p ↦ Prod.ext (funext fun k ↦ dite_eq_left k.isLt) (funext fun k ↦
       (dite_eq_right (by omega : ¬ m + k.val < m)).trans (congrArg p.2
           (Fin.ext (Nat.add_sub_cancel_left m k.val)))),
     fun z ↦ funext fun k ↦ if hk : k.val < m then dite_eq_left hk else
       (dite_eq_right hk).trans (congrArg z (Fin.ext (Nat.add_sub_of_le (Nat.not_lt.mp hk))))⟩
  rw [← Equiv.sum_comp e, Fintype.sum_prod_type]
  simp_rw [show ∀ u v, (fun b : Fin m ↦ e (u, v) ⟨b.val, by omega⟩) = u from fun _ _ ↦
      funext fun b ↦ dite_eq_left b.isLt,
    Finset.sum_const, Finset.card_univ, show Fintype.card (BitAssignment r) =
        2 ^ r by simp [BitAssignment],
    nsmul_eq_mul, ← Finset.mul_sum, Nat.cast_pow, Nat.cast_ofNat]
end QuantumComputation.Specs.PhotochemistrySolution.RouterSelectWiringB

namespace QuantumComputation.Specs.PhotochemistrySolution.SortedRouterSpec
open QProg DynamicCircuit PhotochemistrySolution.SplitRouter47_187
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SplitRouterSeqBell26k hiding ket
  matrix_ext_ket
theorem sorted47_hD1 : 1 ≤ 6 := by decide
theorem sorted47_hMlo : 2 ^ (6 - 1) + 2 ≤ 47 := by decide
theorem sorted47_hPow : ∀ d < 6, 2 ^ d < 47 := fun d hd ↦ by interval_cases d <;> decide
theorem sorted187_hD1 : 1 ≤ 8 := by decide
theorem sorted187_hMlo : 2 ^ (8 - 1) + 2 ≤ 187 := by decide
theorem sorted187_hPow : ∀ d < 8, 2 ^ d < 187 := fun d hd ↦ by interval_cases d <;> decide
end QuantumComputation.Specs.PhotochemistrySolution.SortedRouterSpec

namespace QuantumComputation.Specs.PhotochemistrySolution.Stage2ZeroGated
open Operator QProg Matrix Circuit Qubit HermitianMat PhotochemistrySolution.SplitRouter47_187
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
open _root_.DynamicCircuit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt hiding bit_cases
  eval_seq_mulVec ket ket_CNOT ket_TOFF ket_X ket_projector_one ket_projector_zero matrix_ext_ket
  qAssign_obs_map_val
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB hiding bitSign eval_seq_mulVec ket
  ket_CNOT ket_TOFF ket_X matrix_ext_ket writeReg writeReg_apply_of_not_mem
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SplitRouterSeqBell26k hiding ket
  matrix_ext_ket
theorem hdr_lt1 {D : ℕ} (hD1 : 1 ≤ D) : D - 1 < D := by omega
theorem hdr_lt2 {D : ℕ} (hD2 : 2 ≤ D) : D - 2 < D := by omega
theorem hdr_succ_ne {D : ℕ} (m : ℕ) (hm : m + 1 < D) : (⟨m, Nat.lt_of_succ_lt hm⟩ : Fin D) ≠
    ⟨m + 1, hm⟩ := fun e ↦ Nat.ne_of_lt (Nat.lt_succ_self m) (congrArg Fin.val e)
theorem hdr_top_ne_sub {D : ℕ} (hD2 : 2 ≤ D) : (⟨D - 1, hdr_lt1 (Nat.le_of_succ_le hD2)⟩ : Fin D) ≠
    ⟨D - 2, hdr_lt2 hD2⟩ :=
  fun e ↦ by have hv := congrArg Fin.val e; dsimp at hv; omega
theorem hne_zg_hdr {M D n : ℕ} (r : RouterReg M D n) :
    ((∀ d : Fin D, rHas1 r ≠ rNotMin r d) ∧ (∀ d : Fin D, rIdx1 r d ≠ rNotMin r d) ∧
      (∀ d : Fin D, rRawHas2 r ≠ rNotMax r d) ∧ (∀ d : Fin D, rIdx2 r d ≠ rNotMax r d)) ∧
    (rHas1 r ≠ rOnly1 r ∧ rRawHas2 r ≠ rOnly1 r) ∧
    ((∀ d : Fin D, rIdx1 r d ≠ rIdx2 r d) ∧ (∀ d : Fin D, rHas1 r ≠ rIdx2 r d) ∧
      (∀ d : Fin D, rRawHas2 r ≠ rIdx2 r d) ∧ (∀ d : Fin D, rHas1 r ≠ rUMsb r d) ∧
      (∀ d : Fin D, rRawHas2 r ≠ rUMsb r d) ∧ (∀ d : Fin D, rIdx1 r d ≠ rUMsb r d) ∧
      (∀ d : Fin D, rIdx2 r d ≠ rUMsb r d) ∧ (∀ d1 d2 : Fin D, rUMsb r d1 ≠ rIdx2 r d2) ∧
      (∀ d1 d2 : Fin D, d1 ≠ d2 → rUMsb r d1 ≠ rUMsb r d2)) :=
  let ne {a b} {ha : a < _} {hb : b < _} (h : a ≠ b := by omega) : r ⟨a, ha⟩ ≠ r ⟨b, hb⟩ :=
      rr_neOpt r h
  ⟨⟨fun _ ↦ ne, fun _ ↦ ne, fun _ ↦ ne, fun _ ↦ ne⟩, ⟨ne, ne⟩,
   ⟨fun _ ↦ ne, fun _ ↦ ne, fun _ ↦ ne, fun _ ↦ ne, fun _ ↦ ne, fun _ ↦ ne, fun _ ↦ ne, fun _ _ ↦
       ne,
    fun _ _ hne ↦ ne (by have _ := Fin.val_ne_of_ne hne; omega)⟩⟩
theorem rUMsb_ne_rIdx2 {M D n : ℕ} (r : RouterReg M D n) (d1 d2 : Fin D) : rUMsb r d1 ≠
    rIdx2 r d2 := (hne_zg_hdr r).2.2.2.2.2.2.2.2.2.1 d1 d2
theorem rUMsb_ne_of_ne {M D n : ℕ} (r : RouterReg M D n) {d1 d2 : Fin D}
    (hne : d1 ≠ d2) : rUMsb r d1 ≠ rUMsb r d2 :=
  (hne_zg_hdr r).2.2.2.2.2.2.2.2.2.2 d1 d2 hne
/--
`#H1-C1` zero-`T` CNOT loop populating `rNotMin[d] = rHas1 + rIdx1[d]` and
`rNotMax[d] = rRawHas2 + rIdx2[d]` across `0 .. k - 1`.
-/
def pNotFlagsZG {M D n : ℕ} (r : RouterReg M D n) : (k : ℕ) → k ≤ D → ComputeProg n
  | 0, _ => .id
  | k + 1, hk =>
      let hn := (hne_zg_hdr r).1; let d : Fin D := ⟨k, hk⟩
      .seq (pNotFlagsZG r k (Nat.le_of_succ_le hk))
        (.seq (.cnot (rHas1 r) (rNotMin r d) (hn.1 d))
          (.seq (.cnot (rIdx1 r d) (rNotMin r d) (hn.2.1 d))
            (.seq (.cnot (rRawHas2 r) (rNotMax r d) (hn.2.2.1 d))
                  (.cnot (rIdx2 r d) (rNotMax r d) (hn.2.2.2 d)))))
/-- Pre-toggle placing `1 + δ_d` onto `rIdx2 r d` (`0` `TempAND`s). -/
def pUMsbPre {M D n : ℕ} (usePhantom : Bool) (r : RouterReg M D n) (d : Fin D) : ComputeProg n :=
  let hu := (hne_zg_hdr r).2.2
  if usePhantom then
    .seq (.cnot (rIdx1 r d) (rIdx2 r d) (hu.1 d))
      (.seq (.cnot (rHas1 r) (rIdx2 r d) (hu.2.1 d))
        (.seq (.cnot (rRawHas2 r) (rIdx2 r d) (hu.2.2.1 d))
              (.x (rIdx2 r d))))
  else
    .seq (.cnot (rIdx1 r d) (rIdx2 r d) (hu.1 d)) (.x (rIdx2 r d))
/-- Exact inverse post-toggle restoring `rIdx2 r d` (`0` `TempAND`s). -/
def pUMsbPost {M D n : ℕ} (usePhantom : Bool) (r : RouterReg M D n) (d : Fin D) : ComputeProg n :=
  let hu := (hne_zg_hdr r).2.2
  if usePhantom then
    .seq (.x (rIdx2 r d))
      (.seq (.cnot (rRawHas2 r) (rIdx2 r d) (hu.2.2.1 d))
        (.seq (.cnot (rHas1 r) (rIdx2 r d) (hu.2.1 d))
              (.cnot (rIdx1 r d) (rIdx2 r d) (hu.1 d))))
  else
    .seq (.x (rIdx2 r d)) (.cnot (rIdx1 r d) (rIdx2 r d) (hu.1 d))
/-- Single top-down suffix-zero step propagating `rUMsb (m + 1)` to `rUMsb m` (`1` `TempAND`). -/
def pUMsbStep {M D n : ℕ} (usePhantom : Bool) (r : RouterReg M D n) (m : ℕ)
    (hm : m + 1 < D) : ComputeProg n :=
  let dk : Fin D := ⟨m + 1, hm⟩; let dk1 : Fin D := ⟨m, Nat.lt_of_succ_lt hm⟩;
  let hNeU : dk1 ≠ dk := hdr_succ_ne m hm
  .seq (pUMsbPre usePhantom r dk)
    (.seq (.andGate (rUMsb r dk) (rIdx2 r dk) (rUMsb r dk1)
            (rUMsb_ne_rIdx2 r dk dk) (rUMsb_ne_of_ne r hNeU).symm
            (rUMsb_ne_rIdx2 r dk1 dk).symm)
      (.seq (pUMsbPost usePhantom r dk)
            (.cnot (rUMsb r dk1) (rUMsb r dk) (rUMsb_ne_of_ne r hNeU))))
/-- `#H1-C3` top-down suffix-zero chain executing `steps` `TempAND`s down to `rUMsb 0`. -/
def pUMsbDownLoop {M D n : ℕ} (usePhantom : Bool) (r : RouterReg M D n) :
    (steps : ℕ) → steps < D → ComputeProg n
  | 0, _ => .id
  | k + 1, hk =>
      .seq (pUMsbStep usePhantom r k hk)
           (pUMsbDownLoop usePhantom r k (Nat.lt_of_succ_lt hk))
/-- Complete zero-gated `MuxD1` header (`D - 2` `TempAND`s; leaves `[bp .. bp + 3]` untouched). -/
def pHdrD1ZG {M D n : ℕ} (hD2 : 2 ≤ D) (r : RouterReg M D n) : ComputeProg n :=
  let hu := (hne_zg_hdr r).2.2; let dTop : Fin D := ⟨D - 1, hdr_lt1 (Nat.le_of_succ_le hD2)⟩;
  let dSub : Fin D := ⟨D - 2, hdr_lt2 hD2⟩; let hNeTS : dTop ≠ dSub := hdr_top_ne_sub hD2;
  let pInitTop :=
      ComputeProg.seq (.cnot (rIdx1 r dTop) (rUMsb r dTop) (hu.2.2.2.2.2.1 dTop))
      (.seq (.cnot (rIdx2 r dTop) (rUMsb r dTop) (hu.2.2.2.2.2.2.1 dTop))
      (.seq (.cnot (rHas1 r) (rUMsb r dTop) (hu.2.2.2.1 dTop))
      (.seq (.cnot (rRawHas2 r) (rUMsb r dTop) (hu.2.2.2.2.1 dTop))
      (.seq (.cnot (rHas1 r) (rUMsb r dSub) (hu.2.2.2.1 dSub)) (.cnot (rUMsb r dTop) (rUMsb r dSub)
      (rUMsb_ne_of_ne r hNeTS))))))
  .seq (pNotFlagsZG r D le_rfl)
    (.seq pInitTop (pUMsbDownLoop true r (D - 2) (hdr_lt2 hD2)))
/-- Clean `TempAND` target finset `{rUMsb r d | d.val < k}` for `pUMsbDownLoop`. -/
def sCleanHdr {M D n : ℕ} (k : ℕ) (r : RouterReg M D n) : Finset (Wire n) :=
    (Finset.univ.filter (fun d : Fin D ↦ d.val < k)).image (rUMsb r)
theorem mem_sCleanHdr_uMsb {M D n : ℕ} (k : ℕ) (r : RouterReg M D n) (d : Fin D) :
    rUMsb r d ∈ sCleanHdr k r ↔ d.val < k := by
  simp only [sCleanHdr, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun ⟨d', hd', heq⟩ ↦ (by_contra fun hne ↦ rUMsb_ne_of_ne r hne heq) ▸ hd', fun hd ↦
      ⟨d, hd, rfl⟩⟩
theorem numAnd_pUMsbDownLoop {M D n : ℕ} (usePhantom : Bool) (r : RouterReg M D n) :
    ∀ k hk, (pUMsbDownLoop usePhantom r k hk).numAnd = k
  | 0, _ => rfl
  | k + 1, hk => by
      cases usePhantom <;>
        simp only [pUMsbDownLoop, pUMsbStep, pUMsbPre, pUMsbPost, ComputeProg.numAnd,
          Bool.false_eq_true, ↓reduceIte, numAnd_pUMsbDownLoop _ r k (Nat.lt_of_succ_lt hk)] <;>
              omega
end QuantumComputation.Specs.PhotochemistrySolution.Stage2ZeroGated
end
end
