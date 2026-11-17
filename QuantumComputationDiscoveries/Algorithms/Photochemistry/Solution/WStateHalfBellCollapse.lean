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

public import QuantumComputationDiscoveries.Algorithms.Photochemistry.Solution.SharedPortBKineticBell

open QuantumComputation.Specs.PhotochemistrySolution.SpecDefs
open QuantumComputation.Specs.PhotochemistrySolution.QhlAux
open QuantumComputation.Specs.PhotochemistrySolution.PgBase
open QuantumComputation.Specs.PhotochemistrySolution.SelectBase
@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 4096
set_option exponentiation.threshold 8192

noncomputable section
open Operator QProg Matrix HermitianMat Circuit Qubit QuantumComputation.Specs
  QuantumComputation.Specs.PhotochemistrySolution
  QuantumComputation.Specs.PhotochemistrySolution.XMeasUnld
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
open QuantumComputation.Specs.PhotochemistrySolution.UnembedO3Bridge
  QuantumComputation.Specs.PhotochemistrySolution.SelectOracles
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SelectCsa64ProvSpec (SubspaceStep)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SplitBellVecCleanStep (zResetFixupDyn
    subspaceStep_of_circuit subspaceStep_congr_out subspaceStep_seq_zResetFixup)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynQromUncompA (wrapDyn
    projBit)
open scoped Matrix ComplexOrder MatrixOrder Circuit.Notation BigOperators
namespace QuantumComputation.Specs.PhotochemistrySolution.Instances
scoped instance (priority := 100000) {k : ℕ} : NeZero (2 ^ k) := ⟨pow_ne_zero k two_ne_zero⟩
end QuantumComputation.Specs.PhotochemistrySolution.Instances
open scoped QuantumComputation.Specs.PhotochemistrySolution.Instances
set_option allowUnsafeReducibility true

namespace QuantumComputation.Specs.PhotochemistrySolution.HalfBellCollapse
open PrimitiveGate PhotochemistrySolution.SplitRouter47_187
open _root_.DynamicCircuit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt hiding ket matrix_ext_ket
  qAssign_obs_map_val ket_projector_zero ket_projector_one ket_X ket_CNOT ket_TOFF eval_seq_mulVec
  bit_cases
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB hiding writeReg
  writeReg_apply_of_not_mem ket ket_X ket_CNOT ket_TOFF matrix_ext_ket bitSign eval_seq_mulVec
open _root_.QuantumComputation.Specs.PhotochemistrySolution.QubitizationWalkSem hiding sqrtHalf
  star_sqrtHalf sqrtHalf_mul_sqrtHalf bitSign bitSign_add bitSign_mul_self ket_H_apply
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SplitBellVecCleanStep (fanoutXorBits
    fanoutXorBits_of_ne_tgt)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SplitRouterSeqBell26k hiding ket
  matrix_ext_ket
open _root_.QuantumComputation.Specs.PhotochemistrySolution.PortBDualBellUnld (HCNOTSupportedIn)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.PortBStage5Merged (topPlaneFin
    fixedFanoutBits fixedFanoutBits_of_ne_tgt fixedFanoutBits_zero_ctrl)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.PortBStage5Merged
  (fixedFanoutBits_update_comm)
attribute [local semireducible] DynamicCircuit.identity Circuit.H Circuit.X Circuit.T Circuit.S
attribute [local semireducible] DynQromUncompA.wrapDyn KinB.andComputeCircuit
attribute [local semireducible] KinB.andUncomputeDyn DynCircExt.andUncompute_loc
    CircExt.andUncomputeFixup_loc
attribute [local irreducible] systemQubits_frozen

/- Section 1: Multi-plane classical-control fanout and ZMod 2 bit-transformer identities. -/

/-- Multi-plane classical-control CNOT fanout sweep across `m` bit-planes. -/
def fixedFanoutVecCirc {n : ℕ} (M : ℕ) : (m : ℕ) → (qB : Fin m → Wire n) →
    (cVec : Fin M → ZMod 2) → (wTgt : Fin m → Fin M → Wire n) →
    (∀ (k : Fin m) (p : Fin M), qB k ≠ wTgt k p) → Circuit n
  | 0, _, _, _, _ => .identity
  | m + 1, qB, cVec, wTgt, hbt =>
      fixedFanoutVecCirc M m (fun k ↦ qB k.castSucc) cVec (fun k ↦ wTgt k.castSucc)
        (fun k ↦ hbt k.castSucc) ;;ᶜ
      fixedFanoutCirc M (qB (Fin.last m)) cVec (wTgt (Fin.last m)) (hbt (Fin.last m))

theorem hcnotSupportedIn_fixedFanout1 {M n : ℕ} {S : Wire n → Prop} (qB : Wire n)
    (cVec : Fin M → ZMod 2) (wT : Fin M → Wire n) (hbt : ∀ p, qB ≠ wT p) (hq : S qB)
    (hw : ∀ p, cVec p = 1 → S (wT p)) : HCNOTSupportedIn S (fixedFanoutCirc M qB cVec wT hbt) := by
  induction M with
  | zero => exact .id
  | succ K ih =>
      dsimp only [fixedFanoutCirc]
      refine .seq (ih _ _ _ fun p ↦ hw p.castSucc) ?_
      split_ifs with hc <;> first | exact .cnot (hbt _) hq (hw _ hc) | exact .id

theorem hcnotSupportedIn_fixedFanoutVec {M n : ℕ} {S : Wire n → Prop} (m : ℕ) (qB : Fin m → Wire n)
    (cVec : Fin M → ZMod 2) (wT : Fin m → Fin M → Wire n) (hbt : ∀ k p, qB k ≠ wT k p)
    (hq : ∀ k, S (qB k)) (hw : ∀ k p, cVec p = 1 → S (wT k p)) :
    HCNOTSupportedIn S (fixedFanoutVecCirc M m qB cVec wT hbt) := by
  induction m with
  | zero => exact .id
  | succ k ih =>
      exact .seq (ih _ _ _ (fun j ↦ hq j.castSucc) fun j ↦ hw j.castSucc)
        (hcnotSupportedIn_fixedFanout1 _ cVec _ _ (hq _) (hw _))

theorem preservesKetPred_fixedFanoutVec {M n : ℕ} {P : BitAssignment n → Prop}
    (cVec : Fin M → ZMod 2) :
    ∀ (m : ℕ) (qB : Fin m → Wire n) (wTgt : Fin m → Fin M → Wire n)
      (hbt : ∀ k p, qB k ≠ wTgt k p)
      (_hUpdT : ∀ k p α v, P α → P (Function.update α (wTgt k p) v))
      {ψ : Fin (2 ^ n) → ℂ}, PreservesKetPred P ψ →
      PreservesKetPred P ((fixedFanoutVecCirc M m qB cVec wTgt hbt).eval.1.mulVec ψ)
  | 0, _, _, _, _, _, hψ =>
        by simpa only [fixedFanoutVecCirc, Circuit.eval_identity, Submonoid.coe_one,
             Matrix.one_mulVec] using hψ
  | m + 1, _, _, _, hUpdT, _, hψ => by
      rw [fixedFanoutVecCirc, eval_seq_mulVec]
      exact preservesKetPred_fixedFanout M _ _ _ _ (hUpdT _)
        (preservesKetPred_fixedFanoutVec cVec m _ _ _ (fun k ↦ hUpdT k.castSucc) hψ)

theorem fanoutXorBits_eq_fixedFanoutBits {n : ℕ} :
    ∀ (M : ℕ) (wCtrl wTgt : Fin M → Wire n) (cVec : Fin M → ZMod 2) (β : BitAssignment n),
      (∀ p : Fin M, β (wCtrl p) = cVec p) →
      (∀ p q : Fin M, wCtrl p ≠ wTgt q) →
      fanoutXorBits M wCtrl wTgt β = fixedFanoutBits M 1 cVec wTgt β
  | 0, _, _, _, _, _, _ => rfl
  | M + 1, wCtrl, wTgt, cVec, β, hC, hDisj => by
      dsimp only [fanoutXorBits, fixedFanoutBits]
      rw [(fanoutXorBits_of_ne_tgt M (fun p ↦ wCtrl p.castSucc) _ β _
          fun q ↦ hDisj (Fin.last M) q.castSucc).trans (hC (Fin.last M)),
        fanoutXorBits_eq_fixedFanoutBits M _ _ (fun p ↦ cVec p.castSucc) β
          (fun p ↦ hC p.castSucc) fun p q ↦ hDisj p.castSucc q.castSucc]
      rcases bit_cases (cVec (Fin.last M)) with h | h <;>
        simp only [h, zero_ne_one, ↓reduceIte, add_zero, Function.update_eq_self]

theorem fixedFanoutBits_add {n : ℕ} :
    ∀ (M : ℕ) (c₁ c₂ : Fin M → ZMod 2) (wTgt : Fin M → Wire n),
      (∀ p₁ p₂ : Fin M, p₁ ≠ p₂ → wTgt p₁ ≠ wTgt p₂) → ∀ (β : BitAssignment n),
      fixedFanoutBits M 1 (fun p ↦ c₁ p + c₂ p) wTgt β =
        fixedFanoutBits M 1 c₂ wTgt (fixedFanoutBits M 1 c₁ wTgt β)
  | 0, _, _, _, _, _ => rfl
  | M + 1, c₁, c₂, wTgt, hInj, β => by
      have hNe (p : Fin M) := hInj (Fin.last M) p.castSucc (Fin.castSucc_lt_last p).ne'
      dsimp only [fixedFanoutBits]
      rw [fixedFanoutBits_add M (fun p ↦ c₁ p.castSucc) (fun p ↦ c₂ p.castSucc)
        (fun p ↦ wTgt p.castSucc) (fun _ _ hp ↦ hInj _ _ (mt Fin.castSucc_inj.mp hp)) β]
      set X := fixedFanoutBits M 1 (fun p ↦ c₁ p.castSucc) (fun p ↦ wTgt p.castSucc) β
      have hYX := fixedFanoutBits_of_ne_tgt M 1 (fun p ↦ c₂ p.castSucc)
        (fun p ↦ wTgt p.castSucc) X (wTgt (Fin.last M)) hNe
      rcases bit_cases (c₁ (Fin.last M)) with h1 | h1 <;>
        rcases bit_cases (c₂ (Fin.last M)) with h2 | h2 <;>
        simp only [h1, h2, zero_add, add_zero, CharTwo.add_self_eq_zero, zero_ne_one, ↓reduceIte,
          fun v ↦ fixedFanoutBits_update_comm M 1 (fun p ↦ c₂ p.castSucc) _ _ v hNe X, ← hYX,
          Function.update_self, Function.update_idem, add_assoc, Function.update_eq_self]

theorem fixedFanoutBits_self_cancel {n M : ℕ} (c : Fin M → ZMod 2) (wTgt : Fin M → Wire n)
    (hInj : ∀ p₁ p₂ : Fin M, p₁ ≠ p₂ → wTgt p₁ ≠ wTgt p₂) (β : BitAssignment n) :
    fixedFanoutBits M 1 c wTgt (fixedFanoutBits M 1 c wTgt β) = β :=
  (fixedFanoutBits_add M c c wTgt hInj β).symm.trans (fixedFanoutBits_zero_ctrl M 1 _ wTgt β fun p ↦
      by
    rcases bit_cases (c p) with hp | hp <;> simp only [hp, add_zero, show (1 : ZMod 2) + 1 =
        0 from rfl])

theorem fixedFanoutBits_comm {n M : ℕ} (c₁ c₂ : Fin M → ZMod 2) (wTgt : Fin M → Wire n)
    (hInj : ∀ p₁ p₂ : Fin M, p₁ ≠ p₂ → wTgt p₁ ≠ wTgt p₂) (β : BitAssignment n) :
    fixedFanoutBits M 1 c₂ wTgt (fixedFanoutBits M 1 c₁ wTgt β) =
    fixedFanoutBits M 1 c₁ wTgt (fixedFanoutBits M 1 c₂ wTgt β) := by
  rw [← fixedFanoutBits_add M c₁ c₂ wTgt hInj β, ← fixedFanoutBits_add M c₂ c₁ wTgt hInj β,
    show (fun p ↦ c₁ p + c₂ p) = fun p ↦ c₂ p + c₁ p from funext fun p ↦ add_comm (c₁ p) (c₂ p)]

/- Section 2: Single-router post-HB-collapse ghost unitary `uBellLoCopyHiConj` and commutations. -/

theorem hne_hA_sys {M D n : ℕ} (r : RouterReg M D n) (b : Fin 24) (p : Fin M) : rHA r b ≠
    rSys r p b := (hne_fixed_router r).2.2.1 b p
theorem hne_bufHi_sys {M D n : ℕ} (r : RouterReg M D n) (b : Fin 24) (p : Fin M) : rBufHi r b ≠
    rSys r p b := (hne_fixed_router r).2.1 b p

theorem hne_bufHi_hA {M D n : ℕ} (r : RouterReg M D n) (b : Fin 24) : rBufHi r b ≠ rHA r b :=
  rr_ne r (by have := b.isLt; dsimp; omega)

theorem hne_ctrlLo_sys_all {M D n : ℕ} (r : RouterReg M D n) (b : Fin 24)
    (p q : Fin M) : rCtrlLo r p ≠ rSys r q b :=
  rr_ne r (by have := b.isLt; have := p.isLt; have := q.isLt; unfold basePub; dsimp; omega)

theorem hne_sys_inj {M D n : ℕ} (r : RouterReg M D n) (b : Fin 24) {p₁ p₂ : Fin M}
    (hne : p₁ ≠ p₂) : rSys r p₁ b ≠ rSys r p₂ b :=
  rr_ne r fun e ↦ hne (Fin.ext (by cases b; cases p₁; cases p₂; dsimp at *; omega))

/--
Classical-control overlay after collapsing `rHB r` onto `rBufHi r`:
`fixedBellVecCirc` on `(rHA r, rSys r)` followed by `fixedFanoutVecCirc` on `(rBufHi r, rSys r)`.
-/
def cFixedBellLoCopyHiCirc {M D n : ℕ} (r : RouterReg M D n) (cLo cHi : Fin M → ZMod 2) :
    Circuit n :=
  fixedBellVecCirc M 24 (rHA r) cLo (fun b p ↦ rSys r p b) (hne_hA_sys r) ;;ᶜ
  fixedFanoutVecCirc M 24 (rBufHi r) cHi (fun b p ↦ rSys r p b) (hne_bufHi_sys r)

/--
Wires actively modified by `cFixedBellLoCopyHiCirc`: `{rHA r, rSys r}` (excludes both `rHB r`
and `rBufHi r`, since `rBufHi r` is used only as CNOT control).
-/
def BellLoCopyHiModSet {M D n : ℕ} (r : RouterReg M D n) (w : Wire n) : Prop :=
  (∃ b : Fin 24, w = rHA r b) ∨
  (∃ (p : Fin M) (b : Fin 24), w = rSys r p b)

/--
Wires read or modified by `cFixedBellLoCopyHiCirc`: `{rHA r, rBufHi r, rSys r}` (excludes
`rHB r` and `rBufLo r`).
-/
def BellLoCopyHiTouchSet {M D n : ℕ} (r : RouterReg M D n) (w : Wire n) : Prop :=
  (∃ b : Fin 24, w = rHA r b) ∨
  (∃ b : Fin 24, w = rBufHi r b) ∨
  (∃ (p : Fin M) (b : Fin 24), w = rSys r p b)

/--
Wires safe for arbitrary modification, Hadamard, and measurement under `uBellLoCopyHiConj r`:
excludes `RouterCtrlSet r` and `BellLoCopyHiTouchSet r`, hence includes `rHB r`, `rBufLo r`, and
all private/external workspace wires.
-/
def InnerLoCopyHiSafe {M D n : ℕ} (r : RouterReg M D n) (w : Wire n) : Prop :=
    ¬ RouterCtrlSet r w ∧ ¬ BellLoCopyHiTouchSet r w
theorem bellLoCopyHiModSet_sub_bellModSet {M D n : ℕ} (r : RouterReg M D n) {w : Wire n}
    (h : BellLoCopyHiModSet r w) : BellModSet r w :=
  match h with | .inl ⟨b, hw⟩ => .inl ⟨b, hw⟩ | .inr ⟨p, b, hw⟩ => .inr (.inr ⟨p, b, hw⟩)

theorem bellLoCopyHiModSet_sub_touchSet {M D n : ℕ} (r : RouterReg M D n) {w : Wire n}
    (h : BellLoCopyHiModSet r w) : BellLoCopyHiTouchSet r w :=
  match h with | .inl ⟨b, hw⟩ => .inl ⟨b, hw⟩ | .inr ⟨p, b, hw⟩ => .inr (.inr ⟨p, b, hw⟩)

theorem bellLoCopyHiTouchSet_sub_allPlaneMod {M D n : ℕ} (r : RouterReg M D n) {w : Wire n}
    (h : BellLoCopyHiTouchSet r w) : AllPlaneMod r w := by
  rcases h with ⟨b, rfl⟩ | ⟨b, rfl⟩ | ⟨p, b, rfl⟩
  exacts [⟨b, .inr (.inr (.inl rfl))⟩, ⟨b, .inr (.inl rfl)⟩,
    ⟨b, .inr (.inr (.inr (.inr ⟨p, (planeOfRouter_sys r b p).symm⟩)))⟩]

theorem innerLoCopyHiSafe_of_not_ctrl_not_planeMod {M D n : ℕ} (r : RouterReg M D n) {w : Wire n}
    (hc : ¬ RouterCtrlSet r w) (hp : ¬ AllPlaneMod r w) : InnerLoCopyHiSafe r w :=
    ⟨hc, fun ht ↦ hp (bellLoCopyHiTouchSet_sub_allPlaneMod r ht)⟩
theorem bellLoCopyHiModSet_disj_innerSafe {M D n : ℕ} (r : RouterReg M D n) {w : Wire n}
    (hb : BellLoCopyHiModSet r w) (hs : InnerLoCopyHiSafe r w) : False :=
    hs.2 (bellLoCopyHiModSet_sub_touchSet r hb)
theorem preservesKetPred_cFixedBellLoCopyHi {M D n : ℕ} (r : RouterReg M D n)
    (cLo cHi : Fin M → ZMod 2)
    {P : BitAssignment n → Prop} (hKeep : ∀ {u : Wire n}, BellLoCopyHiModSet r u → ∀ α v, P α →
        P (Function.update α u v))
    {ψ : Fin (2 ^ n) → ℂ} (hψ : PreservesKetPred P ψ) :
    PreservesKetPred P ((cFixedBellLoCopyHiCirc r cLo cHi).eval.1.mulVec ψ) := by
  have hBV (m : ℕ) : ∀ (qH : Fin m → Wire n) (wT : Fin m → Fin M → Wire n)
      (hht : ∀ k p, qH k ≠ wT k p),
      (∀ k, BellLoCopyHiModSet r (qH k)) → (∀ k p, BellLoCopyHiModSet r (wT k p)) →
      ∀ {φ : Fin (2 ^ n) → ℂ}, PreservesKetPred P φ →
          PreservesKetPred P ((fixedBellVecCirc M m qH cLo wT hht).eval.1.mulVec φ) := by
    induction m with
    | zero =>
        exact fun _ _ _ _ _ _ hφ ↦ by
          simpa only [fixedBellVecCirc, Circuit.eval_identity, Submonoid.coe_one,
            Matrix.one_mulVec] using hφ
    | succ m ihm =>
        intro qH wT hht hqH hwT φ hφ
        rw [fixedBellVecCirc, fixedBell1Circ, eval_seq_mulVec, eval_seq_mulVec]
        exact preservesKetPred_fixedFanout M _ _ _ _ (fun p ↦ hKeep (hwT (Fin.last m) p))
          (preservesKetPred_H (hKeep (hqH (Fin.last m)))
            (ihm _ _ _ (fun k ↦ hqH k.castSucc) (fun k p ↦ hwT k.castSucc p) hφ))
  rw [cFixedBellLoCopyHiCirc, eval_seq_mulVec]
  exact preservesKetPred_fixedFanoutVec cHi 24 (rBufHi r) (fun b p ↦ rSys r p b)
    (hne_bufHi_sys r) (fun b p ↦ hKeep (.inr ⟨p, b, rfl⟩))
    (hBV 24 (rHA r) (fun b p ↦ rSys r p b) (hne_hA_sys r) (fun b ↦ .inl ⟨b, rfl⟩)
      (fun b p ↦ .inr ⟨p, b, rfl⟩) hψ)
def ProgLoCopyHiCtrlSafe {M D n : ℕ} (r : RouterReg M D n) : ComputeProg n → Prop
  | .id => True
  | .x u => InnerLoCopyHiSafe r u
  | .cnot c tgt _ => ¬ BellLoCopyHiModSet r c ∧ InnerLoCopyHiSafe r tgt
  | .andGate c₁ c₂ a _ _ _ =>
      ¬ BellLoCopyHiModSet r c₁ ∧ ¬ BellLoCopyHiModSet r c₂ ∧ InnerLoCopyHiSafe r a
  | .seq p₁ p₂ => ProgLoCopyHiCtrlSafe r p₁ ∧ ProgLoCopyHiCtrlSafe r p₂

def RouterPlaneSet {M D n : ℕ} (r : RouterReg M D n) (P : Fin 24 → Prop) (w : Wire n) : Prop :=
    ∃ d : Fin 24, P d ∧ (w = rHA r d ∨ w = rHB r d ∨ w = rBufHi r d ∨ ∃ p : Fin M, w = rSys r p d)
theorem routerPlaneSet_disj {M D n : ℕ} (r : RouterReg M D n) {P₁ P₂ : Fin 24 → Prop}
    (hDisjP : ∀ d, P₁ d → ¬ P₂ d) : ∀ w : Wire n, RouterPlaneSet r P₁ w →
    ¬ RouterPlaneSet r P₂ w := by
  rintro w ⟨d₁, hp₁, hw₁⟩ ⟨d₂, hp₂, hw₂⟩
  have : d₁.1 ≠ d₂.1 ∧ d₁.1 < 24 ∧ d₂.1 < 24 :=
    ⟨fun e ↦ hDisjP d₁ hp₁ (Fin.ext e ▸ hp₂), d₁.2, d₂.2⟩
  rcases hw₁ with rfl | rfl | rfl | ⟨_, rfl⟩ <;> rcases hw₂ with h | h | h | ⟨_, h⟩ <;>
    exact rr_ne r (by dsimp at *; omega) h

/-- Low-port Bell prefix on planes `0 .. k - 1`. -/
def cBellLoBelow {M D n : ℕ} (r : RouterReg M D n) (cLo : Fin M → ZMod 2) :
    (k : ℕ) → k ≤ 24 → Circuit n
  | 0, _ => .identity
  | k + 1, hk =>
      cBellLoBelow r cLo k (Nat.le_of_succ_le hk) ;;ᶜ
      fixedBell1Circ M (rHA r ⟨k, hk⟩) cLo (fun p ↦ rSys r p ⟨k, hk⟩) (hne_hA_sys r ⟨k, hk⟩)

/-- Low-port Bell suffix on planes `24 - m .. 23` in increasing plane order. -/
def cBellLoTop {M D n : ℕ} (r : RouterReg M D n) (cLo : Fin M → ZMod 2) :
    (m : ℕ) → m ≤ 24 → Circuit n
  | 0, _ => .identity
  | m + 1, hm =>
      let b := topPlaneFin m hm
      fixedBell1Circ M (rHA r b) cLo (fun p ↦ rSys r p b) (hne_hA_sys r b) ;;ᶜ
      cBellLoTop r cLo m (Nat.le_of_succ_le hm)

theorem eval_cBellLoBelow_congr {M D n : ℕ} (r : RouterReg M D n) (cLo : Fin M → ZMod 2) {k₁ k₂ : ℕ}
    (hk : k₁ = k₂) (h₁ : k₁ ≤ 24) (h₂ : k₂ ≤ 24) :
    (cBellLoBelow r cLo k₁ h₁).eval.1 = (cBellLoBelow r cLo k₂ h₂).eval.1 := hk ▸ rfl

theorem eval_cBellLoSplit {M D n : ℕ} (r : RouterReg M D n) (cLo : Fin M → ZMod 2) :
    ∀ (m : ℕ) (hm : m ≤ 24),
      (cBellLoTop r cLo m hm).eval.1 * (cBellLoBelow r cLo (24 - m) (Nat.sub_le 24 m)).eval.1 =
        (fixedBellVecCirc M 24 (rHA r) cLo (fun b p ↦ rSys r p b) (hne_hA_sys r)).eval.1 := by
  have hp (k : ℕ) : ∀ hk : k ≤ 24, (cBellLoBelow r cLo k hk).eval.1 =
      (fixedBellVecCirc M k (fun j ↦ rHA r ⟨j.1, j.2.trans_le hk⟩) cLo
        (fun j p ↦ rSys r p ⟨j.1, j.2.trans_le hk⟩)
        fun j p ↦ hne_hA_sys r ⟨j.1, j.2.trans_le hk⟩ p).eval.1 := by
    induction k with
    | zero => exact fun _ ↦ rfl
    | succ _ ih => exact fun hk ↦ by simp [cBellLoBelow, fixedBellVecCirc, ih (by omega)]
  intro m hm
  induction m with
  | zero => simp [cBellLoTop, hp 24 le_rfl]
  | succ m ihm =>
      rw [← ihm (by omega), eval_cBellLoBelow_congr r cLo
        (show 24 - m = (23 - m) + 1 by omega) _ (by omega)]
      simp only [cBellLoBelow, cBellLoTop, Circuit.eval_seq, Submonoid.coe_mul, Matrix.mul_assoc,
        eval_cBellLoBelow_congr r cLo (show 23 - m = 24 - (m + 1) by omega) _ (Nat.sub_le 24 _)]
      rfl
end QuantumComputation.Specs.PhotochemistrySolution.HalfBellCollapse
namespace QuantumComputation.Specs.PhotochemistrySolution.WStateRouterPrim
open PhotochemistrySolution.XMeasChunkQromUnldA PhotochemistrySolution.DynQromUncompA
open _root_.DynamicCircuit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt hiding ket matrix_ext_ket
  qAssign_obs_map_val ket_projector_zero ket_projector_one ket_X ket_CNOT ket_TOFF eval_seq_mulVec
  bit_cases localIdx
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB hiding writeReg
  writeReg_apply_of_not_mem ket ket_X ket_CNOT ket_TOFF matrix_ext_ket bitSign eval_seq_mulVec
  localIdx
open _root_.QuantumComputation.Specs.PhotochemistrySolution.QubitizationWalkSem hiding sqrtHalf
  star_sqrtHalf sqrtHalf_mul_sqrtHalf bitSign bitSign_add bitSign_mul_self
open _root_.QuantumComputation.Specs.PhotochemistrySolution.XMeasLinearCleanStep (WirePair
    czPairsParity xUnloadCzPairsSeqDyn count_xUnloadCzPairsSeqDyn subspaceStep_xUnloadCzPairsSeqDyn)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SplitRouterSeqBell26k (SupportedOn)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SplitRouter47_187 (idxValPrefix
    idxValPrefix_lt_two_pow idxValD)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.ProviderCore (cw_1 cw_cnot dw_xUnload)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Stage2ChDiffMux960 (chGateCirc
    count_chGateCirc cw_chGateCirc cw_seq chGateCirc_mulVec_ket_zero chGateCirc_mulVec_ket_one)
attribute [local semireducible] remeasureIf projBit zResetFixupDyn
/- Section 1: Balanced Z-measurement teleportation and one-hot toggle unitary -/

def mkVecOp {n : ℕ} (f : BitAssignment n → Fin (2 ^ n) → ℂ) : Operator (2 ^ n) :=
    Matrix.of fun row col ↦ f (basisBits n col) row
theorem mkVecOp_mulVec_ket {n : ℕ} (f : BitAssignment n → Fin (2 ^ n) → ℂ) (δ : BitAssignment n) :
    (mkVecOp f).mulVec (ket δ) = f δ := by
  ext row; simp only [mkVecOp, Matrix.mulVec, dotProduct, Matrix.of_apply, ket, basisState];
  rw [Finset.sum_eq_single ((basisBitsEquiv n).symm δ)]
  · simp
  · intro col _ hne; simp [hne.symm]
  · intro habs; exact (habs (Finset.mem_univ _)).elim

/-- Pairwise disjointness bundle for a zero-gated W-state one-hot router. -/
structure WRouterDisj {D N n : ℕ} (wHas : Wire n) (wIdx : Fin D → Wire n)
    (wOut : Fin N → Wire n) (qEnc : Wire n) : Prop where
  has_ne_out : ∀ j, wHas ≠ wOut j
  has_ne_q : wHas ≠ qEnc
  idx_ne_out : ∀ d j, wIdx d ≠ wOut j
  idx_ne_q : ∀ d, wIdx d ≠ qEnc
  out_inj : ∀ i j, i ≠ j → wOut i ≠ wOut j
  out_ne_q : ∀ j, wOut j ≠ qEnc

/-- Subspace precondition for forward W-state one-hot loading. -/
def ValidWRouterIn {D N n : ℕ} (wHas : Wire n) (wIdx : Fin D → Wire n) (wOut : Fin N → Wire n)
    (qEnc : Wire n) (δ : BitAssignment n) : Prop :=
  (∀ j : Fin N, δ (wOut j) = 0) ∧ δ qEnc = 0 ∧
    idxValD wIdx δ < N ∧ (δ wHas = 0 → idxValD wIdx δ = 0)

/-- Subspace precondition on clean output state for W-state uncomputation. -/
def ValidWRouterClean {D N n : ℕ} (wHas : Wire n) (wIdx : Fin D → Wire n) (wOut : Fin N → Wire n)
    (δ : BitAssignment n) : Prop :=
    (∀ j : Fin N, δ (wOut j) = 0) ∧ idxValD wIdx δ < N ∧ (δ wHas = 0 → idxValD wIdx δ = 0)
theorem idxValPrefix_congr {D n : ℕ} (wIdx : Fin D → Wire n) (δ₁ δ₂ : BitAssignment n)
    (h : ∀ d : Fin D, δ₁ (wIdx d) = δ₂ (wIdx d)) :
    ∀ (m : ℕ) (hm : m ≤ D), idxValPrefix wIdx δ₁ m hm = idxValPrefix wIdx δ₂ m hm
  | 0, _ => rfl
  | m + 1, hm => by simp [idxValPrefix, idxValPrefix_congr wIdx δ₁ δ₂ h m (by omega), h ⟨m, hm⟩]
theorem idxValD_congr {D n : ℕ} (wIdx : Fin D → Wire n) {δ₁ δ₂ : BitAssignment n}
    (h : ∀ d : Fin D, δ₁ (wIdx d) = δ₂ (wIdx d)) : idxValD wIdx δ₁ = idxValD wIdx δ₂ :=
  idxValPrefix_congr wIdx δ₁ δ₂ h D le_rfl

/-- Involutive bit-map toggling `wOut (idxValD wIdx δ)` by `δ wHas` when `idxValD wIdx δ < N`. -/
def toggleOneHotBits {D N n : ℕ} (wHas : Wire n) (wIdx : Fin D → Wire n) (wOut : Fin N → Wire n)
    (δ : BitAssignment n) : BitAssignment n :=
  if h : idxValD wIdx δ < N then
    let t := wOut ⟨idxValD wIdx δ, h⟩
    Function.update δ t (δ t + δ wHas)
  else δ

theorem toggleOneHotBits_invol {D N n : ℕ} (wHas : Wire n) (wIdx : Fin D → Wire n)
    (wOut : Fin N → Wire n)
    (hHasOut : ∀ j, wHas ≠ wOut j) (hIdxOut : ∀ d j, wIdx d ≠ wOut j) (δ : BitAssignment n) :
    toggleOneHotBits wHas wIdx wOut (toggleOneHotBits wHas wIdx wOut δ) = δ := by
  dsimp only [toggleOneHotBits]
  by_cases h : idxValD wIdx δ < N
  · let t := wOut ⟨idxValD wIdx δ, h⟩
    have hIdx := idxValD_congr wIdx fun d ↦
      Function.update_of_ne (hIdxOut d ⟨idxValD wIdx δ, h⟩) (δ t + δ wHas) δ
    have hF : (⟨_, hIdx.symm ▸ h⟩ : Fin N) = ⟨_, h⟩ := Fin.ext hIdx
    rw [dite_eq_left h, dite_eq_left (hIdx.symm ▸ h), hF, Function.update_self,
      Function.update_of_ne (hHasOut _), Function.update_idem, add_assoc,
      CharTwo.add_self_eq_zero, add_zero, Function.update_eq_self]
  · simp [h]

/-- Permutation unitary for `toggleOneHotBits`. -/
def uOneHotToggle {D N n : ℕ} (wHas : Wire n) (wIdx : Fin D → Wire n) (wOut : Fin N → Wire n)
    (hHasOut : ∀ j, wHas ≠ wOut j) (hIdxOut : ∀ d j, wIdx d ≠ wOut j) : Unitary (2 ^ n) :=
  permUnitary
    { toFun := toggleOneHotBits wHas wIdx wOut
      invFun := toggleOneHotBits wHas wIdx wOut
      left_inv := toggleOneHotBits_invol wHas wIdx wOut hHasOut hIdxOut
      right_inv := toggleOneHotBits_invol wHas wIdx wOut hHasOut hIdxOut }

theorem uOneHotToggle_mulVec_ket {D N n : ℕ} (wHas : Wire n) (wIdx : Fin D → Wire n)
    (wOut : Fin N → Wire n) (hHasOut : ∀ j, wHas ≠ wOut j) (hIdxOut : ∀ d j, wIdx d ≠ wOut j)
    (δ : BitAssignment n) : (uOneHotToggle wHas wIdx wOut hHasOut hIdxOut).1.mulVec (ket δ) =
    ket (toggleOneHotBits wHas wIdx wOut δ) := permUnitary_mulVec_ket _ δ
theorem toggleOneHotBits_apply_out {D N n : ℕ} {wHas : Wire n} {wIdx : Fin D → Wire n}
    {wOut : Fin N → Wire n}
    (hInj : ∀ i j, i ≠ j → wOut i ≠ wOut j) {δ : BitAssignment n} (h0 : ∀ j, δ (wOut j) = 0)
        (hLt : idxValD wIdx δ < N) (j : Fin N) :
    toggleOneHotBits wHas wIdx wOut δ (wOut j) = if idxValD wIdx δ = j.val then δ wHas else 0 := by
  dsimp only [toggleOneHotBits]
  rw [dite_eq_left hLt]
  by_cases hj : idxValD wIdx δ = j.val
  · rw [ite_eq_left hj, show j = ⟨idxValD wIdx δ, hLt⟩ from Fin.ext hj.symm, Function.update_self,
        h0 _, zero_add]
  · rw [ite_eq_right hj, Function.update_of_ne (hInj j _ fun e ↦ hj (congrArg Fin.val e).symm),
        h0 j]

theorem toggleOneHotBits_apply_other {D N n : ℕ} {wHas : Wire n} {wIdx : Fin D → Wire n}
    {wOut : Fin N → Wire n}
    (δ : BitAssignment n) {u : Wire n} (hu : ∀ j, u ≠ wOut j) :
        toggleOneHotBits wHas wIdx wOut δ u = δ u := by
  by_cases h : idxValD wIdx δ < N <;> simp [toggleOneHotBits, h, Function.update_of_ne (hu _)]

theorem supportedOn_uOneHotToggle {D N n : ℕ} (wHas : Wire n) (wIdx : Fin D → Wire n)
    (wOut : Fin N → Wire n) (hHasOut : ∀ j, wHas ≠ wOut j) (hIdxOut : ∀ d j, wIdx d ≠ wOut j)
    {P Q : BitAssignment n → Prop} {R : Operator (2 ^ n)}
    (hPQ : ∀ δ, P δ → Q (toggleOneHotBits wHas wIdx wOut δ)) (hR : SupportedOn P R) :
    SupportedOn Q ((uOneHotToggle wHas wIdx wOut hHasOut hIdxOut).1 * R) := fun A B hAB ↦ by
  rw [← Matrix.mul_assoc A, ← Matrix.mul_assoc B]
  exact hR _ _ fun δ hP ↦
      by simpa only [← Matrix.mulVec_mulVec, uOneHotToggle_mulVec_ket] using hAB _ (hPQ δ hP)

theorem uOneHotToggle_mul_eq_of_supportedOn {D M N n : ℕ} (hMN : M ≤ N) (wHas : Wire n)
    (wIdx : Fin D → Wire n) (wOut : Fin N → Wire n)
    (hHasOut : ∀ j, wHas ≠ wOut j) (hIdxOut : ∀ d j, wIdx d ≠ wOut j)
        (hInj : ∀ i j, i ≠ j → wOut i ≠ wOut j) (F R : Operator (2 ^ n))
    (hSupp : SupportedOn (fun δ ↦ (∀ j : Fin N, δ (wOut j) = 0) ∧ idxValD wIdx δ < M ∧
        ∃ δ' : BitAssignment n, F.mulVec (ket δ) = ket δ' ∧
      (∀ p : Fin M, δ' (wOut ⟨p.val, Nat.lt_of_lt_of_le p.isLt hMN⟩) = if idxValD wIdx δ =
          p.val then δ wHas else 0) ∧
      (∀ u : Wire n, (∀ p : Fin M, u ≠ wOut ⟨p.val, Nat.lt_of_lt_of_le p.isLt hMN⟩) → δ' u =
          δ u)) R) :
    (uOneHotToggle wHas wIdx wOut hHasOut hIdxOut).1 * R = F * R :=
  hSupp _ _ fun δ ⟨h0, hLtM, δ', hF, hOutM, hOthM⟩ ↦ by
    rw [uOneHotToggle_mulVec_ket, hF]
    refine congrArg _ (funext fun u ↦ ?_)
    by_cases hu : ∃ j : Fin N, u = wOut j
    · obtain ⟨j, rfl⟩ := hu
      rw [toggleOneHotBits_apply_out hInj h0 (hLtM.trans_le hMN) j]
      by_cases hjM : j.val < M
      · exact (hOutM ⟨j.val, hjM⟩).symm
      · rw [ite_eq_right (by omega), hOthM _ (fun p ↦ hInj j _ fun e ↦ hjM (e ▸ p.isLt)), h0 j]
    · rw [toggleOneHotBits_apply_other δ (fun j e ↦ hu ⟨j, e⟩), hOthM u fun _ e ↦ hu ⟨_, e⟩]

/- Section 2: Generic 1D sequential circuit combinators -/

/-- Left-to-right sequential composition of `m` circuits `f 0 ;;ᶜ ... ;;ᶜ f (m - 1)`. -/
def seqNat {n : ℕ} : (m : ℕ) → ((i : ℕ) → i < m → Circuit n) → Circuit n
  | 0, _ => .identity
  | m + 1, f => seqNat m (fun i hi ↦ f i (Nat.lt_succ_of_lt hi)) ;;ᶜ f m (Nat.lt_succ_self m)

theorem count_seqNat_T {n : ℕ} (c : ℕ) :
    ∀ (m : ℕ) (f : (i : ℕ) → i < m → Circuit n),
      (∀ i hi, (f i hi).count .T = c) → (seqNat m f).count .T = m * c
  | 0, _, _ => by simp [seqNat]
  | m + 1, _, hc => (by simp [seqNat, Circuit.count_seq,
      count_seqNat_T c m _ fun i _ ↦ hc i (by omega), hc] : _ = m * c + c).trans (by ring)

theorem count_seqNat_TOFF_zero {n : ℕ} :
    ∀ (m : ℕ) (f : (i : ℕ) → i < m → Circuit n),
      (∀ i hi, (f i hi).count .TOFF = 0) → (seqNat m f).count .TOFF = 0
  | 0, _, _ => rfl
  | m + 1, f, hc =>
        by simp [seqNat, Circuit.count_seq, count_seqNat_TOFF_zero m _ fun i hi ↦
             hc i (Nat.lt_succ_of_lt hi), hc m (Nat.lt_succ_self m)]

theorem cw_seqNat {n : ℕ} {S : Wire n → Prop} :
    ∀ (m : ℕ) (f : (i : ℕ) → i < m → Circuit n),
      (∀ i hi, CircWires S (f i hi)) → CircWires S (seqNat m f)
  | 0, _, _ => trivial
  | m + 1, _, hc =>
        ⟨cw_seqNat m _ fun i hi ↦ hc i (Nat.lt_succ_of_lt hi), hc m (Nat.lt_succ_self m)⟩

theorem seqNat_mulVec_fixed {n : ℕ} (ψ : Fin (2 ^ n) → ℂ) :
    ∀ (m : ℕ) (f : (i : ℕ) → i < m → Circuit n),
      (∀ i hi, (f i hi).eval.1.mulVec ψ = ψ) → (seqNat m f).eval.1.mulVec ψ = ψ
  | 0, _, _ => by simp [seqNat, Circuit.eval_identity]
  | m + 1, f, hc =>
        by rw [seqNat, eval_seq_mulVec, seqNat_mulVec_fixed ψ m _ fun i hi ↦
             hc i (Nat.lt_succ_of_lt hi), hc m (Nat.lt_succ_self m)]

theorem seqNat_mulVec_single {n : ℕ} (ψ ψ' : Fin (2 ^ n) → ℂ) (i₀ : ℕ) :
    ∀ (m : ℕ) (f : (i : ℕ) → i < m → Circuit n),
      (∀ i (hi : i < m), i < i₀ → (f i hi).eval.1.mulVec ψ = ψ) →
      (∀ hi₀ : i₀ < m, (f i₀ hi₀).eval.1.mulVec ψ = ψ') →
      (∀ i (hi : i < m), i₀ < i → (f i hi).eval.1.mulVec ψ' = ψ') →
      (seqNat m f).eval.1.mulVec ψ = if i₀ < m then ψ' else ψ
  | 0, _, _, _, _ => by simp [seqNat, Circuit.eval_identity]
  | m + 1, f, hlt, heq, hgt => by
      rw [seqNat, eval_seq_mulVec, seqNat_mulVec_single ψ ψ' i₀ m _
        (fun i _ ↦ hlt i (by omega)) (fun _ ↦ heq (by omega)) fun i _ ↦ hgt i (by omega)]
      rcases lt_trichotomy i₀ m with h | rfl | h
      · simp [h, Nat.lt_succ_of_lt h, hgt m (Nat.lt_succ_self m) h]
      · simp [heq (Nat.lt_succ_self i₀)]
      · simp [show ¬ i₀ < m by omega, show ¬ i₀ < m + 1 by omega, hlt m (Nat.lt_succ_self m) h]

/- Section 3: R-block CH-tree expansion and barrel-shift primitives -/

theorem w_ne_of_pair_ne {n R k : ℕ} {w : Fin R → Fin (2 ^ k) → Wire n}
    (hw : ∀ b₁ p₁ b₂ p₂, w b₁ p₁ = w b₂ p₂ → b₁ = b₂ ∧ p₁ = p₂)
    {b₁ b₂ : Fin R} {p₁ p₂ : Fin (2 ^ k)} (h : b₁ ≠ b₂ ∨ p₁ ≠ p₂) :
    w b₁ p₁ ≠ w b₂ p₂ := fun e ↦ h.elim (· (hw b₁ p₁ b₂ p₂ e).1) (· (hw b₁ p₁ b₂ p₂ e).2)

/-- Single `2-T` W-state splitter `chGateCirc a b ;;ᶜ CNOT b a`. -/
def wSplitPair {n : ℕ} (a b : Wire n) (hab : a ≠ b) : Circuit n :=
  chGateCirc a b hab ;;ᶜ Circuit.CNOT b a hab.symm

theorem count_wSplitPair {n : ℕ} (a b : Wire n) (hab : a ≠ b) : (wSplitPair a b hab).count .T = 2 ∧
    (wSplitPair a b hab).count .TOFF = 0 := by
  simpa [wSplitPair, Circuit.count_seq, Circuit.CNOT] using count_chGateCirc a b hab

theorem cw_wSplitPair {n : ℕ} {S : Wire n → Prop} {a b : Wire n} {hab : a ≠ b} (ha : S a)
    (hb : S b) : CircWires S (wSplitPair a b hab) := cw_seq (cw_chGateCirc ha hb) (cw_cnot hb ha)
theorem wSplitPair_mulVec_ket_zero {n : ℕ} (a b : Wire n) (hab : a ≠ b) (δ : BitAssignment n)
    (ha0 : δ a = 0) (hb0 : δ b = 0) : (wSplitPair a b hab).eval.1.mulVec (ket δ) = ket δ := by
  rw [wSplitPair, eval_seq_mulVec, chGateCirc_mulVec_ket_zero a b hab δ ha0,
      ket_CNOT b a hab.symm δ, ha0, hb0, add_zero,
    show Function.update δ a 0 = δ from ha0 ▸ Function.update_eq_self a δ]

theorem wSplitPair_mulVec_ket_one {n : ℕ} (a b : Wire n) (hab : a ≠ b) (δ : BitAssignment n)
    (ha0 : δ a = 0) (hb0 : δ b = 0) :
    (wSplitPair a b hab).eval.1.mulVec (ket (Function.update δ a 1)) =
        sqrtHalf • (ket (Function.update δ a 1) + ket (Function.update δ b 1)) := by
  rw [wSplitPair, eval_seq_mulVec, chGateCirc_mulVec_ket_one a b hab _
    (Function.update_self a 1 δ), ket_H, (Function.update_of_ne hab.symm 1 δ).trans hb0]
  simp only [bitSign, ↓reduceIte, one_smul, Matrix.mulVec_smul, Matrix.mulVec_add, ket_CNOT]
  exact congrArg (sqrtHalf • ·) (congrArg₂ (· + ·)
    (congrArg ket (funext fun u ↦ by
      by_cases hua : u = a <;> by_cases hub : u = b <;> simp [*, hab.symm]))
    (congrArg ket (funext fun u ↦ by
      by_cases hua : u = a <;> by_cases hub : u = b <;>
        simp [*, hab.symm, CharTwo.add_self_eq_zero])))
theorem div_lt_of_lt_mul_right {i A B : ℕ} (hB : 0 < B) (hi : i < A * B) : i / B < A :=
    (Nat.div_lt_iff_lt_mul hB).mpr hi
theorem pair_lo_lt {r k j : ℕ} (hr : r < k) (hj : j < 2 ^ r) : j < 2 ^ k :=
  Nat.lt_of_lt_of_le hj (Nat.pow_le_pow_right (by omega) (Nat.le_of_lt hr))

theorem pair_hi_lt {r k j : ℕ} (hr : r < k) (hj : j < 2 ^ r) : j + 2 ^ r < 2 ^ k := by
  have : 2 ^ r * 2 ≤ 2 ^ k := Nat.pow_succ 2 r ▸ Nat.pow_le_pow_right (by omega) hr
  omega

/-- Round `r < k` of `wSplitPair` across all `R` blocks and `j < 2^r`. -/
def wTreeRound {n : ℕ} (R k : ℕ) (w : Fin R → Fin (2 ^ k) → Wire n)
    (hw : ∀ b₁ p₁ b₂ p₂, w b₁ p₁ = w b₂ p₂ → b₁ = b₂ ∧ p₁ = p₂) (r : ℕ) (hr : r < k) : Circuit n :=
  seqNat (R * 2 ^ r) fun i hi ↦
    let hB : 0 < 2 ^ r := Nat.two_pow_pos r;
    let blk : Fin R := ⟨i / 2 ^ r, div_lt_of_lt_mul_right hB hi⟩; let j := i % 2 ^ r;
    let hj : j < 2 ^ r := Nat.mod_lt i hB; let p0 : Fin (2 ^ k) := ⟨j, pair_lo_lt hr hj⟩;
    let p1 : Fin (2 ^ k) := ⟨j + 2 ^ r, pair_hi_lt hr hj⟩
    wSplitPair (w blk p0) (w blk p1)
      (w_ne_of_pair_ne hw (Or.inr fun e ↦ by
        have hv := congrArg Fin.val e; dsimp [p0, p1] at hv; omega))

/-- First `m ≤ k` rounds of `wTreeRound`. -/
def wTreePrefix {n : ℕ} (R k : ℕ) (w : Fin R → Fin (2 ^ k) → Wire n)
    (hw : ∀ b₁ p₁ b₂ p₂, w b₁ p₁ = w b₂ p₂ → b₁ = b₂ ∧ p₁ = p₂) :
    (m : ℕ) → m ≤ k → Circuit n
  | 0, _ => .identity
  | r + 1, hr => wTreePrefix R k w hw r (Nat.le_of_succ_le hr) ;;ᶜ wTreeRound R k w hw r hr

theorem count_wTreePrefix {n : ℕ} (R k : ℕ) (w : Fin R → Fin (2 ^ k) → Wire n)
    (hw : ∀ b₁ p₁ b₂ p₂, w b₁ p₁ = w b₂ p₂ → b₁ = b₂ ∧ p₁ = p₂) :
    ∀ (m : ℕ) (hm : m ≤ k),
      (wTreePrefix R k w hw m hm).count .T = 2 * R * (2 ^ m - 1) ∧
      (wTreePrefix R k w hw m hm).count .TOFF = 0
  | 0, _ => ⟨by simp [wTreePrefix], rfl⟩
  | r + 1, hr => by
      have := Nat.one_le_two_pow (n := r)
      simp only [wTreePrefix, wTreeRound, Circuit.count_seq, Nat.pow_succ,
        count_wTreePrefix R k w hw r (by omega), add_zero, and_true,
        count_seqNat_T 2 _ _ fun _ _ ↦ (count_wSplitPair _ _ _).1,
        count_seqNat_TOFF_zero _ _ fun _ _ ↦ (count_wSplitPair _ _ _).2,
        show 2 ^ r * 2 - 1 = 2 ^ r - 1 + 2 ^ r by omega]
      ring

theorem cw_wTreePrefix {n : ℕ} {S : Wire n → Prop} (R k : ℕ) (w : Fin R → Fin (2 ^ k) → Wire n)
    (hw : ∀ b₁ p₁ b₂ p₂, w b₁ p₁ = w b₂ p₂ → b₁ = b₂ ∧ p₁ = p₂)
    (hS : ∀ b p, S (w b p)) :
    ∀ (m : ℕ) (hm : m ≤ k), CircWires S (wTreePrefix R k w hw m hm)
  | 0, _ => trivial
  | r + 1, hr =>
        ⟨cw_wTreePrefix R k w hw hS r (Nat.le_of_succ_le hr), cw_seqNat (R * 2 ^ r) _ fun _ _ ↦
        cw_wSplitPair (hS _ _) (hS _ _)⟩

theorem enc_div_mod {A B a b : ℕ} (ha : a < A) (hb : b < B) : a * B + b < A * B ∧ (a * B + b) / B =
    a ∧ (a * B + b) % B = b := by
  refine ⟨by nlinarith, ?_, by rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hb]⟩
  rw [Nat.mul_comm a B, Nat.mul_add_div (by omega), Nat.div_eq_of_lt hb, add_zero]

theorem enc_ne_iff {B i a b : ℕ} (hne : i ≠ a * B + b) : i / B ≠ a ∨ i % B ≠ b := by
  refine Decidable.or_iff_not_imp_left.mpr fun h1 h2 ↦ hne ?_
  simpa [Decidable.not_not.mp h1, h2, Nat.mul_comm] using (Nat.div_add_mod i B).symm

private theorem fin_mk_eq {N a b : ℕ} {ha : a < N} {hb : b < N} (h : a = b) : (⟨a, ha⟩ : Fin N) =
    ⟨b, hb⟩ := Fin.ext h

private theorem w_ne_of_enc_ne {n R B k : ℕ} {w : Fin R → Fin (2 ^ k) → Wire n}
    (hw : ∀ b₁ p₁ b₂ p₂, w b₁ p₁ = w b₂ p₂ → b₁ = b₂ ∧ p₁ = p₂) {i a b : ℕ} (hne : i ≠ a * B + b)
    {hb1 : i / B < R} {hb2 : a < R} {p₁ p₂ : Fin (2 ^ k)} (hmod : i % B ≠ b → p₁.val ≠ p₂.val) :
    w ⟨i / B, hb1⟩ p₁ ≠ w ⟨a, hb2⟩ p₂ :=
  w_ne_of_pair_ne hw <| (enc_ne_iff hne).imp (fun h e ↦ h (congrArg Fin.val e))
    fun h e ↦ hmod h (congrArg Fin.val e)
theorem wTreeRound_mulVec_ket {n R k : ℕ} (w : Fin R → Fin (2 ^ k) → Wire n)
    (hw : ∀ b₁ p₁ b₂ p₂, w b₁ p₁ = w b₂ p₂ → b₁ = b₂ ∧ p₁ = p₂)
    (r : ℕ) (hr : r < k) (δ : BitAssignment n) (h0 : ∀ b p, δ (w b p) = 0) (bStar : Fin R)
        (s : Fin (2 ^ r)) :
    (wTreeRound R k w hw r hr).eval.1.mulVec (ket (Function.update δ (w bStar ⟨s.val,
        pair_lo_lt hr s.isLt⟩) 1)) =
      sqrtHalf • (ket (Function.update δ (w bStar ⟨s.val, pair_lo_lt hr s.isLt⟩) 1) +
          ket (Function.update δ (w bStar ⟨s.val + 2 ^ r, pair_hi_lt hr s.isLt⟩) 1)) := by
  let pS0 : Fin (2 ^ k) := ⟨s.val, pair_lo_lt hr s.isLt⟩
  let pS1 : Fin (2 ^ k) := ⟨s.val + 2 ^ r, pair_hi_lt hr s.isLt⟩
  let i₀ := bStar.val * 2 ^ r + s.val
  obtain ⟨hi₀, hdiv₀, hmod₀⟩ := enc_div_mod bStar.isLt s.isLt
  have hFix (pX : Fin (2 ^ k)) (hpX : pX = pS0 ∨ pX = pS1) (i : ℕ) (hi : i < R * 2 ^ r)
      (hne : i ≠ i₀) :
      let hB := Nat.two_pow_pos r
      (wSplitPair (w ⟨i / 2 ^ r, div_lt_of_lt_mul_right hB hi⟩
          ⟨i % 2 ^ r, pair_lo_lt hr (Nat.mod_lt i hB)⟩)
        (w ⟨i / 2 ^ r, div_lt_of_lt_mul_right hB hi⟩
            ⟨i % 2 ^ r + 2 ^ r, pair_hi_lt hr (Nat.mod_lt i hB)⟩)
        (w_ne_of_pair_ne hw (Or.inr fun e ↦ Nat.ne_of_lt (Nat.lt_add_of_pos_right hB)
            (congrArg Fin.val e)))).eval.1.mulVec
        (ket (Function.update δ (w bStar pX) 1)) = ket (Function.update δ (w bStar pX) 1) := by
    intro hB
    have hj := Nat.mod_lt i hB
    have hs := s.isLt
    have hne0 := w_ne_of_enc_ne hw hne (hb1 := div_lt_of_lt_mul_right hB hi) (hb2 := bStar.isLt)
      (p₁ := ⟨i % 2 ^ r, pair_lo_lt hr hj⟩) (p₂ := pX) fun hm ↦
          by rcases hpX with rfl | rfl <;> dsimp [pS0, pS1] <;> omega
    have hne1 := w_ne_of_enc_ne hw hne (hb1 := div_lt_of_lt_mul_right hB hi) (hb2 := bStar.isLt)
      (p₁ := ⟨i % 2 ^ r + 2 ^ r, pair_hi_lt hr hj⟩) (p₂ := pX) fun hm ↦
          by rcases hpX with rfl | rfl <;> dsimp [pS0, pS1] <;> omega
    exact wSplitPair_mulVec_ket_zero _ _ _ _ ((Function.update_of_ne hne0 _ _).trans (h0 _ _))
        ((Function.update_of_ne hne1 _ _).trans (h0 _ _))
  have hSeq := seqNat_mulVec_single (ket (Function.update δ (w bStar pS0) 1))
    (sqrtHalf • (ket (Function.update δ (w bStar pS0) 1) +
        ket (Function.update δ (w bStar pS1) 1))) i₀ (R * 2 ^ r) _
    (fun i hi hlt ↦ hFix pS0 (.inl rfl) i hi (Nat.ne_of_lt hlt))
    (fun hi₀' ↦ by
      simp only [show (⟨i₀ / 2 ^ r, div_lt_of_lt_mul_right (Nat.two_pow_pos r) hi₀'⟩ : Fin R) =
          bStar from Fin.ext hdiv₀,
        show (⟨i₀ % 2 ^ r, pair_lo_lt hr (Nat.mod_lt i₀ (Nat.two_pow_pos r))⟩ : Fin (2 ^ k)) =
            pS0 from Fin.ext hmod₀,
        show (⟨i₀ % 2 ^ r + 2 ^ r,
            pair_hi_lt hr (Nat.mod_lt i₀ (Nat.two_pow_pos r))⟩ : Fin (2 ^ k)) =
            pS1 from fin_mk_eq (congrArg (· + 2 ^ r) hmod₀)]
      exact wSplitPair_mulVec_ket_one _ _ _ δ (h0 bStar pS0) (h0 bStar pS1))
    (fun i hi hgt ↦
        by rw [Matrix.mulVec_smul, Matrix.mulVec_add, hFix pS0 (.inl rfl) i hi (Nat.ne_of_gt hgt),
             hFix pS1 (.inr rfl) i hi (Nat.ne_of_gt hgt)])
  rwa [ite_eq_left hi₀] at hSeq

theorem wTreePrefix_mulVec_ket {n R k : ℕ} (w : Fin R → Fin (2 ^ k) → Wire n)
    (hw : ∀ b₁ p₁ b₂ p₂, w b₁ p₁ = w b₂ p₂ → b₁ = b₂ ∧ p₁ = p₂)
    (δ : BitAssignment n) (h0 : ∀ b p, δ (w b p) = 0) (bStar : Fin R) :
    ∀ (m : ℕ) (hm : m ≤ k),
      (wTreePrefix R k w hw m hm).eval.1.mulVec
          (ket (Function.update δ (w bStar ⟨0, Nat.two_pow_pos k⟩) 1)) =
        (sqrtHalf ^ m) •
          ∑ s : Fin (2 ^ m),
            ket (Function.update δ
              (w bStar ⟨s.val, Nat.lt_of_lt_of_le s.isLt (Nat.pow_le_pow_right (by omega) hm)⟩) 1)
  | 0, _ => by
      simp only [wTreePrefix, Circuit.eval_identity, Submonoid.coe_one, Matrix.one_mulVec,
          _root_.pow_zero, one_smul]
      rw [Finset.sum_eq_single ⟨0, Nat.two_pow_pos 0⟩
          (fun s _ hne ↦ absurd (Fin.ext (Nat.lt_one_iff.mp s.isLt)) hne) fun h ↦
          (h (Finset.mem_univ _)).elim]
  | r + 1, hr => by
      rw [wTreePrefix, eval_seq_mulVec,
          wTreePrefix_mulVec_ket w hw δ h0 bStar r (Nat.le_of_succ_le hr), Matrix.mulVec_smul,
          Matrix.mulVec_sum]
      simp_rw [wTreeRound_mulVec_ket w hw r hr δ h0 bStar]
      let e : Fin (2 ^ r + 2 ^ r) ≃ Fin (2 ^ (r + 1)) :=
          finCongr (by ring : 2 ^ r + 2 ^ r = 2 ^ (r + 1))
      rw [← Finset.smul_sum, smul_smul, ← _root_.pow_succ, Finset.sum_add_distrib, ← e.sum_comp,
          Fin.sum_univ_add]
      exact congrArg (sqrtHalf ^ (r + 1) • ·) (congrArg (_ + ·) (Finset.sum_congr rfl fun s _ ↦
        congrArg (fun p ↦ ket (Function.update δ (w bStar p) 1)) (Fin.ext (by
          dsimp [e]
          omega))))

/- Section 1: Binary stride arithmetic and 3-CNOT swap -/

theorem shift_pos_lt {d k lo hi : ℕ} (hd : d ≤ k) (hlo : lo < 2 ^ d) (hhi : hi < 2 ^ (k - d)) : lo +
    2 ^ d * hi < 2 ^ k := by
  have := Nat.mul_le_mul_left (2 ^ d) hhi
  rw [Nat.mul_succ, ← Nat.pow_add, Nat.add_sub_of_le hd] at this
  omega

theorem testBit_lo_add_mul_two_pow {d lo m : ℕ} (hlo : lo < 2 ^ d) : (lo + 2 ^ d * m).testBit d =
    decide (m % 2 = 1)
    := by rw [Nat.testBit_eq_decide_div_mod_eq, Nat.add_comm, Nat.mul_add_div (Nat.two_pow_pos d),
            Nat.div_eq_of_lt hlo, add_zero]
theorem testBit_add_two_pow_self {p0 d : ℕ} (h : p0.testBit d = false) : (p0 + 2 ^ d).testBit d =
    true
    := by rw [Nat.testBit_eq_decide_div_mod_eq] at h ⊢; rw [Nat.add_div_right p0 (Nat.two_pow_pos
            d)]; simp only [decide_eq_false_iff_not, decide_eq_true_eq] at h ⊢; omega
/-- Even/odd decomposition `Fin M ⊕ Fin M ≃ Fin (2 * M)`. -/
def finTwoMulEquiv (M : ℕ) : Fin M ⊕ Fin M ≃ Fin (2 * M) where
  toFun | .inl q => ⟨2 * q.val, by omega⟩ | .inr q => ⟨2 * q.val + 1, by omega⟩
  invFun x := if x.val % 2 = 0 then .inl ⟨x.val / 2, by omega⟩ else .inr ⟨x.val / 2, by omega⟩
  left_inv
    | .inl q => by
        dsimp only
        rw [ite_eq_left (by omega)]
        exact congrArg Sum.inl (Fin.ext (show 2 * q.val / 2 = q.val by omega))
    | .inr q => by
        dsimp only
        rw [ite_eq_right (by omega)]
        exact congrArg Sum.inr (Fin.ext (show (2 * q.val + 1) / 2 = q.val by omega))
  right_inv x := by
    dsimp only
    split_ifs with h
    · exact Fin.ext (show 2 * (x.val / 2) = x.val by omega)
    · exact Fin.ext (show 2 * (x.val / 2) + 1 = x.val by omega)
/-- 3-CNOT wire swap (`0 T`, `0 TOFF`). -/
def swap3Cnot {n : ℕ} (a b : Wire n) (hab : a ≠ b) : Circuit n :=
  Circuit.CNOT a b hab ;;ᶜ Circuit.CNOT b a hab.symm ;;ᶜ Circuit.CNOT a b hab

theorem count_swap3Cnot {n : ℕ} (a b : Wire n) (hab : a ≠ b) : (swap3Cnot a b hab).count .T = 0 ∧
    (swap3Cnot a b hab).count .TOFF = 0 := by simp [swap3Cnot, Circuit.count_seq, Circuit.CNOT]
theorem cw_swap3Cnot {n : ℕ} {S : Wire n → Prop} {a b : Wire n} {hab : a ≠ b} (ha : S a)
    (hb : S b) : CircWires S (swap3Cnot a b hab) :=
    cw_seq (cw_cnot ha hb) (cw_seq (cw_cnot hb ha) (cw_cnot ha hb))
theorem swap3Cnot_mulVec_ket_zero {n : ℕ} (a b : Wire n) (hab : a ≠ b) (δ : BitAssignment n)
    (ha : δ a = 0) (hb : δ b = 0) : (swap3Cnot a b hab).eval.1.mulVec (ket δ) =
    ket δ := by have ub : Function.update δ b 0 = δ :=
                  hb ▸ Function.update_eq_self b δ; have ua : Function.update δ a 0 = δ :=
                                                      ha ▸ Function.update_eq_self a δ;
                                                      rw [swap3Cnot, eval_seq_mulVec, ket_CNOT, ha,
                                                        hb,
                                                      add_zero, ub, eval_seq_mulVec, ket_CNOT, ha,
                                                      hb, add_zero, ua, ket_CNOT, ha, hb, add_zero,
                                                      ub]
theorem swap3Cnot_mulVec_ket_dir {n : ℕ} (a b : Wire n) (hab : a ≠ b) (δ : BitAssignment n)
    (ha : δ a = 0) (hb : δ b = 0) (dir : Bool) :
    (swap3Cnot a b hab).eval.1.mulVec (ket (Function.update δ (if dir then b else a) 1)) =
        ket (Function.update δ (if dir then a else b) 1) := by
  cases dir <;> simp only [Bool.false_eq_true, ↓reduceIte, swap3Cnot, eval_seq_mulVec, ket_CNOT]
  all_goals exact congrArg ket (funext fun u ↦ by
    by_cases hua : u = a <;> by_cases hub : u = b <;>
      simp [*, hab.symm, CharTwo.add_self_eq_zero])

/- Section 2: Odd-block parity gather and stride-`2^d` barrel swap -/

/-- CNOT from every `w blk p` with `p.val.testBit d = true` onto `qEnc`. -/
def cnotOddToEnc {n : ℕ} (R k : ℕ) (w : Fin R → Fin (2 ^ k) → Wire n) (qEnc : Wire n)
    (hwq : ∀ b p, w b p ≠ qEnc) (d : ℕ) : Circuit n :=
  seqNat (R * 2 ^ k) fun i hi ↦
    let hB : 0 < 2 ^ k := Nat.two_pow_pos k;
    let blk : Fin R := ⟨i / 2 ^ k, div_lt_of_lt_mul_right hB hi⟩;
    let p : Fin (2 ^ k) := ⟨i % 2 ^ k, Nat.mod_lt i hB⟩
    if (i % 2 ^ k).testBit d then Circuit.CNOT (w blk p) qEnc (hwq blk p) else .identity

theorem count_cnotOddToEnc {n : ℕ} (R k : ℕ) (w : Fin R → Fin (2 ^ k) → Wire n) (qEnc : Wire n)
    (hwq : ∀ b p, w b p ≠ qEnc) (d : ℕ) :
    (cnotOddToEnc R k w qEnc hwq d).count .T = 0 ∧ (cnotOddToEnc R k w qEnc hwq d).count .TOFF =
        0 :=
  ⟨(count_seqNat_T 0 _ _ fun i _ ↦ by cases (i % 2 ^ k).testBit d <;> simp [Circuit.CNOT]).trans
    (Nat.mul_zero _), count_seqNat_TOFF_zero _ _ fun i _ ↦ by
    cases (i % 2 ^ k).testBit d <;> simp [Circuit.CNOT]⟩

theorem cw_cnotOddToEnc {n : ℕ} {S : Wire n → Prop} (R k : ℕ) (w : Fin R → Fin (2 ^ k) → Wire n)
    (qEnc : Wire n) (hwq : ∀ b p, w b p ≠ qEnc)
    (d : ℕ) (hwS : ∀ b p, S (w b p)) (hqS : S qEnc) : CircWires S (cnotOddToEnc R k w qEnc hwq d) :=
  cw_seqNat (R * 2 ^ k) _ fun _ _ ↦ by
    dsimp only
    split_ifs <;> first | exact cw_cnot (hwS _ _) hqS | trivial

theorem cnotOddToEnc_mulVec_ket {n R k : ℕ} (w : Fin R → Fin (2 ^ k) → Wire n) (qEnc : Wire n)
    (hw : ∀ b₁ p₁ b₂ p₂, w b₁ p₁ = w b₂ p₂ → b₁ = b₂ ∧ p₁ = p₂) (hwq : ∀ b p, w b p ≠ qEnc)
    (d : ℕ) (δ : BitAssignment n) (hw0 : ∀ b p, δ (w b p) = 0) (hq0 : δ qEnc = 0) (bStar : Fin R)
        (pStar : Fin (2 ^ k)) :
    (cnotOddToEnc R k w qEnc hwq d).eval.1.mulVec (ket (Function.update δ (w bStar pStar) 1)) =
      ket (Function.update (Function.update δ (w bStar pStar) 1) qEnc (if pStar.val.testBit d then 1
          else 0)) := by
  let δ₁ := Function.update δ (w bStar pStar) 1
  have hq1 : δ₁ qEnc = 0 := (Function.update_of_ne (hwq bStar pStar).symm 1 δ).trans hq0
  have hz0 : Function.update δ₁ qEnc 0 = δ₁ := hq1 ▸ Function.update_eq_self qEnc δ₁
  let i₀ := bStar.val * 2 ^ k + pStar.val
  obtain ⟨hi₀, hdiv₀, hmod₀⟩ := enc_div_mod bStar.isLt pStar.isLt
  have hFix (z : ZMod 2) (i : ℕ) (hi : i < R * 2 ^ k) (hne : i ≠ i₀) :
      let hB : 0 < 2 ^ k := Nat.two_pow_pos k
      (if (i % 2 ^ k).testBit d then
        Circuit.CNOT (w ⟨i / 2 ^ k, div_lt_of_lt_mul_right hB hi⟩
            ⟨i % 2 ^ k, Nat.mod_lt i hB⟩) qEnc (hwq _ _)
      else .identity).eval.1.mulVec (ket (Function.update δ₁ qEnc z)) =
          ket (Function.update δ₁ qEnc z) := by
    intro hB
    split_ifs with htb
    · have hneW := w_ne_of_enc_ne hw hne (hb1 := div_lt_of_lt_mul_right hB hi) (hb2 := bStar.isLt)
        (p₁ := ⟨i % 2 ^ k, Nat.mod_lt i hB⟩) (p₂ := pStar) id
      rw [ket_CNOT, show Function.update δ₁ qEnc z _ = 0 from
        (Function.update_of_ne (hwq _ _) z δ₁).trans ((Function.update_of_ne hneW 1 δ).trans
            (hw0 _ _)),
        add_zero, Function.update_idem, Function.update_self]
    · rw [Circuit.eval_identity, Submonoid.coe_one, Matrix.one_mulVec]
  have hSeq := seqNat_mulVec_single (ket δ₁)
    (ket (Function.update δ₁ qEnc (if pStar.val.testBit d then 1 else 0))) i₀ (R * 2 ^ k) _
    (fun i hi hlt ↦ by simpa [hz0] using hFix 0 i hi (Nat.ne_of_lt hlt))
    (fun hi₀' ↦ by
      by_cases ht : pStar.val.testBit d = true
      · rw [ite_eq_left (hmod₀.symm ▸ ht), ite_eq_left ht, ket_CNOT, hq1, zero_add]
        exact congrArg (fun v ↦ ket (Function.update δ₁ qEnc v))
          ((congrArg δ₁ (congrArg₂ w (Fin.ext hdiv₀) (Fin.ext hmod₀))).trans
            (Function.update_self (w bStar pStar) 1 δ))
      · rw [ite_eq_right (hmod₀.symm ▸ ht), ite_eq_right ht, Circuit.eval_identity,
          Submonoid.coe_one, Matrix.one_mulVec, hz0])
    (fun i hi hgt ↦ hFix _ i hi (Nat.ne_of_gt hgt))
  rwa [ite_eq_left hi₀] at hSeq
/-- Stride-`2^d` barrel swap across all `R` blocks (`0 T`, `0 TOFF`). -/
def barrelSwap {n : ℕ} (R k : ℕ) (w : Fin R → Fin (2 ^ k) → Wire n)
    (hw : ∀ b₁ p₁ b₂ p₂, w b₁ p₁ = w b₂ p₂ → b₁ = b₂ ∧ p₁ = p₂) (d : ℕ) : Circuit n :=
  seqNat (R * 2 ^ k) fun i hi ↦
    let hB : 0 < 2 ^ k := Nat.two_pow_pos k;
    let blk : Fin R := ⟨i / 2 ^ k, div_lt_of_lt_mul_right hB hi⟩; let p0 := i % 2 ^ k;
    let hp0 : p0 < 2 ^ k := Nat.mod_lt i hB
    if hp : p0.testBit d = false ∧ p0 + 2 ^ d < 2 ^ k then
      swap3Cnot (w blk ⟨p0, hp0⟩) (w blk ⟨p0 + 2 ^ d, hp.2⟩)
        (w_ne_of_pair_ne hw (Or.inr fun e ↦ by
          have hv := congrArg Fin.val e; have hpd := Nat.two_pow_pos d; dsimp at hv; omega))
    else .identity

theorem count_barrelSwap {n : ℕ} (R k : ℕ) (w : Fin R → Fin (2 ^ k) → Wire n)
    (hw : ∀ b₁ p₁ b₂ p₂, w b₁ p₁ = w b₂ p₂ → b₁ = b₂ ∧ p₁ = p₂) (d : ℕ) :
    (barrelSwap R k w hw d).count .T = 0 ∧ (barrelSwap R k w hw d).count .TOFF = 0 :=
  ⟨(count_seqNat_T 0 (R * 2 ^ k) _ fun _ _ ↦ by
      dsimp only
      split_ifs <;> first | exact (count_swap3Cnot _ _ _).1 | rfl).trans (Nat.mul_zero _),
   count_seqNat_TOFF_zero (R * 2 ^ k) _ fun _ _ ↦ by
      dsimp only
      split_ifs <;> first | exact (count_swap3Cnot _ _ _).2 | rfl⟩

theorem cw_barrelSwap {n : ℕ} {S : Wire n → Prop} (R k : ℕ) (w : Fin R → Fin (2 ^ k) → Wire n)
    (hw : ∀ b₁ p₁ b₂ p₂, w b₁ p₁ = w b₂ p₂ → b₁ = b₂ ∧ p₁ = p₂)
    (d : ℕ) (hwS : ∀ b p, S (w b p)) : CircWires S (barrelSwap R k w hw d) :=
  cw_seqNat (R * 2 ^ k) _ fun _ _ ↦ by
    dsimp only
    split_ifs <;> first | exact cw_swap3Cnot (hwS _ _) (hwS _ _) | trivial

theorem barrelSwap_mulVec_ket_pair {n R k : ℕ} (w : Fin R → Fin (2 ^ k) → Wire n)
    (hw : ∀ b₁ p₁ b₂ p₂, w b₁ p₁ = w b₂ p₂ → b₁ = b₂ ∧ p₁ = p₂)
    (d : ℕ) (δ : BitAssignment n) (hw0 : ∀ b p, δ (w b p) = 0) (bStar : Fin R) {pLo : ℕ}
        (hpLo : pLo < 2 ^ k)
    (htbLo : pLo.testBit d = false) (hpHi : pLo + 2 ^ d < 2 ^ k) (dir : Bool) :
    (barrelSwap R k w hw d).eval.1.mulVec (ket (Function.update δ (w bStar (if dir then ⟨pLo +
        2 ^ d, hpHi⟩ else ⟨pLo, hpLo⟩)) 1)) =
      ket (Function.update δ (w bStar (if dir then ⟨pLo, hpLo⟩ else ⟨pLo + 2 ^ d, hpHi⟩)) 1) := by
  let i₀ := bStar.val * 2 ^ k + pLo
  obtain ⟨hi₀, hdiv₀, hmod₀⟩ := enc_div_mod bStar.isLt hpLo
  have hFix (pX : Fin (2 ^ k)) (hpX : pX = ⟨pLo, hpLo⟩ ∨ pX = ⟨pLo + 2 ^ d, hpHi⟩) (i : ℕ)
      (hi : i < R * 2 ^ k) (hne : i ≠ i₀) :
      let hB := Nat.two_pow_pos k
      let blk : Fin R := ⟨i / 2 ^ k, div_lt_of_lt_mul_right hB hi⟩
      let p0 := i % 2 ^ k
      (if hp : p0.testBit d = false ∧ p0 + 2 ^ d < 2 ^ k then
        swap3Cnot (w blk ⟨p0, Nat.mod_lt i hB⟩) (w blk ⟨p0 + 2 ^ d, hp.2⟩)
          (w_ne_of_pair_ne hw (Or.inr fun e ↦
              Nat.ne_of_lt (Nat.lt_add_of_pos_right (Nat.two_pow_pos d)) (congrArg Fin.val e)))
      else .identity).eval.1.mulVec (ket (Function.update δ (w bStar pX) 1)) =
          ket (Function.update δ (w bStar pX) 1) := by
    intro hB blk p0
    split_ifs with hp
    · have hneA : w blk ⟨p0, Nat.mod_lt i hB⟩ ≠ w bStar pX := w_ne_of_enc_ne hw hne fun hm ↦ by
        rcases hpX with rfl | rfl
        · exact hm
        · exact fun hv ↦
              Bool.false_ne_true (hp.1.symm.trans ((congrArg (Nat.testBit · d) hv).trans
              (testBit_add_two_pow_self htbLo)))
      have hneB : w blk ⟨p0 + 2 ^ d, hp.2⟩ ≠ w bStar pX := w_ne_of_enc_ne hw hne fun hm ↦ by
        rcases hpX with rfl | rfl
        · exact fun hv ↦
              Bool.false_ne_true (htbLo.symm.trans ((congrArg (Nat.testBit · d) hv).symm.trans
              (testBit_add_two_pow_self hp.1)))
        · exact fun hv ↦ hm (Nat.add_right_cancel hv)
      exact swap3Cnot_mulVec_ket_zero _ _ _ _ ((Function.update_of_ne hneA _ _).trans (hw0 _ _))
          ((Function.update_of_ne hneB _ _).trans (hw0 _ _))
    · rw [Circuit.eval_identity, Submonoid.coe_one, Matrix.one_mulVec]
  have hSeq := seqNat_mulVec_single
    (ket (Function.update δ (w bStar (if dir then ⟨pLo + 2 ^ d, hpHi⟩ else ⟨pLo, hpLo⟩)) 1))
    (ket (Function.update δ (w bStar (if dir then ⟨pLo, hpLo⟩ else ⟨pLo + 2 ^ d, hpHi⟩)) 1)) i₀ (R *
        2 ^ k) _
    (fun i hi hlt ↦ hFix _ (by cases dir <;> simp) i hi (Nat.ne_of_lt hlt))
    (fun hi₀' ↦ by
      have hpCond : (i₀ % 2 ^ k).testBit d = false ∧ i₀ % 2 ^ k + 2 ^ d < 2 ^ k :=
          hmod₀.symm ▸ ⟨htbLo, hpHi⟩
      rw [dite_eq_left hpCond]
      simp only [show (⟨i₀ / 2 ^ k, div_lt_of_lt_mul_right (Nat.two_pow_pos k) hi₀'⟩ : Fin R) =
          bStar from Fin.ext hdiv₀,
        show (⟨i₀ % 2 ^ k, Nat.mod_lt i₀ (Nat.two_pow_pos k)⟩ : Fin (2 ^ k)) =
            ⟨pLo, hpLo⟩ from Fin.ext hmod₀,
        show (⟨i₀ % 2 ^ k + 2 ^ d, hpCond.2⟩ : Fin (2 ^ k)) =
            ⟨pLo + 2 ^ d, hpHi⟩ from fin_mk_eq (congrArg (· + 2 ^ d) hmod₀)]
      simpa [apply_ite (w bStar)] using swap3Cnot_mulVec_ket_dir _ _ _ δ (hw0 _ _) (hw0 _ _) dir)
    (fun i hi hgt ↦ hFix _ (by cases dir <;> simp) i hi (Nat.ne_of_gt hgt))
  rwa [ite_eq_left hi₀] at hSeq
/-- Block-position wire injectivity predicate. -/
abbrev WInj {n R k : ℕ} (w : Fin R → Fin (2 ^ k) → Wire n) : Prop :=
  ∀ b₁ p₁ b₂ p₂, w b₁ p₁ = w b₂ p₂ → b₁ = b₂ ∧ p₁ = p₂

/-- Level `d < k` Z-measurement shift step; resets `qEnc` to `|0⟩` on both outcomes (`0 T`). -/
def wShiftLevel {Var : Type} {n : ℕ} (v : Var) (R k : ℕ) (uLo : Fin k → Wire n)
    (w : Fin R → Fin (2 ^ k) → Wire n) (qEnc : Wire n) (hw : WInj w) (hwq : ∀ b p, w b p ≠ qEnc)
    (huq : ∀ d, uLo d ≠ qEnc) (d : ℕ) (hd : d < k) : DynamicCircuit Var n :=
  .seq (.circuit (cnotOddToEnc R k w qEnc hwq d ;;ᶜ Circuit.CNOT (uLo ⟨d, hd⟩) qEnc (huq ⟨d, hd⟩)))
    (zResetFixupDyn v qEnc (barrelSwap R k w hw d))

/-- First `m ≤ k` levels of `wShiftLevel`. -/
def wShiftLevels {Var : Type} {n : ℕ} (v : Var) (R k : ℕ) (uLo : Fin k → Wire n)
    (w : Fin R → Fin (2 ^ k) → Wire n) (qEnc : Wire n)
    (hw : WInj w) (hwq : ∀ b p, w b p ≠ qEnc) (huq : ∀ d, uLo d ≠ qEnc) :
    (m : ℕ) → m ≤ k → DynamicCircuit Var n
  | 0, _ => .circuit .identity
  | d + 1, hd =>
      .seq (wShiftLevels v R k uLo w qEnc hw hwq huq d (Nat.le_of_succ_le hd))
        (wShiftLevel v R k uLo w qEnc hw hwq huq d hd)

theorem count_wShiftLevels {Var : Type} {n : ℕ} (v : Var) (R k : ℕ) (uLo : Fin k → Wire n)
    (w : Fin R → Fin (2 ^ k) → Wire n) (qEnc : Wire n)
    (hw : WInj w) (hwq : ∀ b p, w b p ≠ qEnc) (huq : ∀ d, uLo d ≠ qEnc) :
    ∀ (m : ℕ) (hm : m ≤ k),
      (wShiftLevels v R k uLo w qEnc hw hwq huq m hm).count .T = 0 ∧
      (wShiftLevels v R k uLo w qEnc hw hwq huq m hm).count .TOFF = 0
  | 0, _ => ⟨rfl, rfl⟩
  | d + 1, hd => by
      simp [wShiftLevels, wShiftLevel, DynamicCircuit.count, Circuit.count_seq, Circuit.CNOT,
        count_wShiftLevels v R k uLo w qEnc hw hwq huq d (by omega), count_cnotOddToEnc,
        count_barrelSwap]

theorem dw_wShiftLevels {Var : Type} {n : ℕ} {S : Wire n → Prop} (v : Var) (R k : ℕ)
    (uLo : Fin k → Wire n) (w : Fin R → Fin (2 ^ k) → Wire n) (qEnc : Wire n)
    (hw : WInj w) (hwq : ∀ b p, w b p ≠ qEnc) (huq : ∀ d, uLo d ≠ qEnc)
    (huS : ∀ d, S (uLo d)) (hwS : ∀ b p, S (w b p)) (hqS : S qEnc) :
    ∀ (m : ℕ) (hm : m ≤ k), DynWires S (wShiftLevels v R k uLo w qEnc hw hwq huq m hm)
  | 0, _ => trivial
  | d + 1, hd => ⟨dw_wShiftLevels v R k uLo w qEnc hw hwq huq huS hwS hqS d (Nat.le_of_succ_le hd),
      ⟨⟨cw_cnotOddToEnc R k w qEnc hwq d hwS hqS, cw_cnot (huS _) hqS⟩,
          ⟨fun _ ↦ hqS, ⟨⟨cw_1 hqS, cw_barrelSwap R k w hw d hwS⟩, trivial⟩⟩⟩⟩

theorem subspaceStep_mul_right {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    {R₀ R₁ : Operator (2 ^ n)} (G : Operator (2 ^ n)) {p : DynamicCircuit Var n}
    (h : SubspaceStep R₀ R₁ p) :
    SubspaceStep (R₀ * G) (R₁ * G) p := fun M ↦ by
  obtain ⟨N, hwp, hobs⟩ := h M
  exact ⟨N, hwp, by simpa [Matrix.mul_assoc] using congrArg (fun X ↦ Gᴴ * (X * G)) hobs⟩
/-- Shifted W-state superposition vector at level `d ≤ k`. -/
def wSuperVec {n R k : ℕ} (bStarFn : BitAssignment n → Fin R) (uLo : Fin k → Wire n)
    (w : Fin R → Fin (2 ^ k) → Wire n) (qEnc : Wire n) (δ : BitAssignment n) (d : ℕ)
    (hd : d ≤ k) : Fin (2 ^ n) → ℂ :=
  if (∀ b p, δ (w b p) = 0) ∧ δ qEnc = 0 then
    (sqrtHalf ^ (k - d)) •
      ∑ hi : Fin (2 ^ (k - d)),
        ket (Function.update δ
          (w (bStarFn δ) ⟨idxValPrefix uLo δ d hd + 2 ^ d * hi.val,
            shift_pos_lt hd (idxValPrefix_lt_two_pow uLo δ d hd) hi.isLt⟩) 1)
  else 0

/-- Operator mapping valid clean `ket δ` to `wSuperVec ... d hd`. -/
def wSuperOp {n R k : ℕ} (bStarFn : BitAssignment n → Fin R) (uLo : Fin k → Wire n)
    (w : Fin R → Fin (2 ^ k) → Wire n) (qEnc : Wire n) (d : ℕ) (hd : d ≤ k) : Operator (2 ^ n) :=
    mkVecOp fun δ ↦ wSuperVec bStarFn uLo w qEnc δ d hd
theorem cnotOddAndIdx_mulVec_ket {n R k : ℕ} (uLo : Fin k → Wire n)
    (w : Fin R → Fin (2 ^ k) → Wire n) (qEnc : Wire n)
    (hw : WInj w) (hwq : ∀ b p, w b p ≠ qEnc) (huq : ∀ d, uLo d ≠ qEnc)
        (huw : ∀ d b p, uLo d ≠ w b p)
    (d : ℕ) (hd : d < k) (δ : BitAssignment n) (hw0 : ∀ b p, δ (w b p) = 0) (hq0 : δ qEnc = 0)
    (bStar : Fin R) {hi : ℕ} (hhi : hi < 2 ^ (k - d)) :
    let lo := idxValPrefix uLo δ d (Nat.le_of_lt hd)
    let pS : Fin (2 ^ k) :=
        ⟨lo + 2 ^ d * hi, shift_pos_lt (Nat.le_of_lt hd)
        (idxValPrefix_lt_two_pow uLo δ d (Nat.le_of_lt hd)) hhi⟩
    (cnotOddToEnc R k w qEnc hwq d ;;ᶜ Circuit.CNOT (uLo ⟨d, hd⟩) qEnc (huq ⟨d,
        hd⟩)).eval.1.mulVec (ket (Function.update δ (w bStar pS) 1)) =
      ket (Function.update (Function.update δ (w bStar pS) 1) qEnc ((if decide (hi % 2 =
          1) then (1 : ZMod 2) else 0) + δ (uLo ⟨d, hd⟩))) := by
  intro lo pS
  rw [eval_seq_mulVec, cnotOddToEnc_mulVec_ket w qEnc hw hwq d δ hw0 hq0 bStar pS, ket_CNOT,
      Function.update_self,
    Function.update_of_ne (huq ⟨d, hd⟩), Function.update_of_ne (huw ⟨d, hd⟩ _ _),
        Function.update_idem]
  dsimp only [pS]
  rw [testBit_lo_add_mul_two_pow (idxValPrefix_lt_two_pow uLo δ d (Nat.le_of_lt hd))]

private theorem mul2_lt {k d b : ℕ} (hd : d < k) (hb : b < 2) (q : Fin (2 ^ (k - (d + 1)))) : 2 *
    q.val + b < 2 ^ (k - d) := by
  have h : 2 ^ (k - d) = 2 ^ (k - (d + 1)) * 2 := by
    rw [show k - d = k - (d + 1) + 1 by omega, Nat.pow_succ]
  have hq := q.isLt
  omega

theorem subspaceStep_wShiftLevel {Var : Type} [Fintype Var] [DecidableEq Var] {n R k : ℕ} (v : Var)
    (bStarFn : BitAssignment n → Fin R) (uLo : Fin k → Wire n) (w : Fin R → Fin (2 ^ k) → Wire n)
        (qEnc : Wire n)
    (hw : WInj w) (hwq : ∀ b p, w b p ≠ qEnc) (huq : ∀ d, uLo d ≠ qEnc)
        (huw : ∀ d b p, uLo d ≠ w b p) (d : ℕ) (hd : d < k) :
    SubspaceStep (wSuperOp bStarFn uLo w qEnc d (Nat.le_of_lt hd))
        (wSuperOp bStarFn uLo w qEnc (d + 1) hd) (wShiftLevel v R k uLo w qEnc hw hwq huq d hd)
        := by
  let cPre := cnotOddToEnc R k w qEnc hwq d ;;ᶜ Circuit.CNOT (uLo ⟨d, hd⟩) qEnc (huq ⟨d, hd⟩)
  let cB := barrelSwap R k w hw d
  have hev (q : Fin (2 ^ (k - (d + 1)))) : ¬ decide (2 * q.val % 2 = 1) = true :=
    fun h ↦ absurd (of_decide_eq_true h) (by omega)
  have hod (q : Fin (2 ^ (k - (d + 1)))) : decide ((2 * q.val + 1) % 2 = 1) = true :=
      decide_eq_true (by omega)
  have hEv (q : Fin (2 ^ (k - (d + 1)))) : 2 * q.val < 2 ^ (k - d) :=
      mul2_lt hd (b := 0) (by omega) q
  have hOd (q : Fin (2 ^ (k - (d + 1)))) : 2 * q.val + 1 < 2 ^ (k - d) := mul2_lt hd (by omega) q
  have hIdx {δ : BitAssignment n} {b : ℕ}
      (hb : (if δ (uLo ⟨d, hd⟩) = 1 then 2 ^ d else 0) = 2 ^ d * b)
      (q : Fin (2 ^ (k - (d + 1)))) :
      idxValPrefix uLo δ d (Nat.le_of_lt hd) + 2 ^ d * (2 * q.val + b) =
        idxValPrefix uLo δ (d + 1) hd + 2 ^ (d + 1) * q.val := by
    dsimp only [idxValPrefix]
    rw [hb]
    ring
  have stepSplit (F : Operator (2 ^ n))
      (hTerm : ∀ (δ : BitAssignment n) (hw0 : ∀ b p, δ (w b p) = 0) (hq0 : δ qEnc = 0)
        (hqId : ∀ p : Fin (2 ^ k), Function.update (Function.update δ (w (bStarFn δ) p) 1) qEnc 0 =
            Function.update δ (w (bStarFn δ) p) 1)
        (q : Fin (2 ^ (k - (d + 1)))),
        let lo := idxValPrefix uLo δ d (Nat.le_of_lt hd)
        let hlo := idxValPrefix_lt_two_pow uLo δ d (Nat.le_of_lt hd)
        F.mulVec (cPre.eval.1.mulVec (ket (Function.update δ (w (bStarFn δ)
            ⟨lo + 2 ^ d * (2 * q.val), shift_pos_lt (Nat.le_of_lt hd) hlo (hEv q)⟩) 1))) +
          F.mulVec (cPre.eval.1.mulVec (ket (Function.update δ (w (bStarFn δ)
              ⟨lo + 2 ^ d * (2 * q.val + 1), shift_pos_lt (Nat.le_of_lt hd) hlo (hOd q)⟩) 1))) =
          ket (Function.update δ (w (bStarFn δ) ⟨idxValPrefix uLo δ (d + 1) hd + 2 ^ (d + 1) *
              q.val, shift_pos_lt hd (idxValPrefix_lt_two_pow uLo δ (d + 1) hd) q.isLt⟩) 1)) :
      F * (cPre.eval.1 * wSuperOp bStarFn uLo w qEnc d (Nat.le_of_lt hd)) =
          sqrtHalf • wSuperOp bStarFn uLo w qEnc (d + 1) hd := by
    refine matrix_ext_ket fun δ ↦ ?_
    simp only [← Matrix.mulVec_mulVec, Matrix.smul_mulVec, wSuperOp, mkVecOp_mulVec_ket, wSuperVec]
    by_cases hV : (∀ b p, δ (w b p) = 0) ∧ δ qEnc = 0
    · obtain ⟨hw0, hq0⟩ := hV
      have hkd : k - d = k - (d + 1) + 1 := by omega
      let e : Fin (2 ^ (k - (d + 1))) ⊕ Fin (2 ^ (k - (d + 1))) ≃ Fin (2 ^ (k - d)) :=
        (finTwoMulEquiv (2 ^ (k -
            (d + 1)))).trans (finCongr (by rw [hkd, Nat.pow_succ, Nat.mul_comm]))
      rw [ite_eq_left ⟨hw0, hq0⟩, ite_eq_left ⟨hw0, hq0⟩, Matrix.mulVec_smul, Matrix.mulVec_smul,
          Matrix.mulVec_sum, Matrix.mulVec_sum,
        show sqrtHalf ^ (k - d) = sqrtHalf * sqrtHalf ^ (k - (d + 1)) by rw [hkd, _root_.pow_succ'],
            smul_smul,
        ← e.sum_comp, Fintype.sum_sum_type, ← Finset.sum_add_distrib]
      exact congrArg (_ • ·) (Finset.sum_congr rfl fun q _ ↦
        hTerm δ hw0 hq0 (fun _ ↦
            ((Function.update_of_ne (hwq _ _).symm 1 δ).trans hq0) ▸ Function.update_eq_self qEnc _)
            q)
    · rw [ite_eq_right hV, ite_eq_right hV, Matrix.mulVec_zero, Matrix.mulVec_zero, smul_zero]
  have hIdx0 {δ : BitAssignment n} (h0 : δ (uLo ⟨d, hd⟩) = 0) :=
    hIdx ((ite_eq_right fun e ↦ zero_ne_one (h0.symm.trans e)).trans (Nat.mul_zero _).symm)
  have hIdx1 {δ : BitAssignment n} (h1 : δ (uLo ⟨d, hd⟩) = 1) :=
    hIdx ((ite_eq_left h1).trans (Nat.mul_one _).symm)
  refine subspaceStep_seq_zResetFixup v qEnc cB (subspaceStep_of_circuit _ cPre)
    (stepSplit ((QRegister.singleton qEnc).basisOutcomeProjector 0) ?_)
    (stepSplit (cB.eval.1 * (Circuit.X qEnc).eval.1 *
      (QRegister.singleton qEnc).basisOutcomeProjector 1) ?_)
  · intro δ hw0 hq0 hqId q lo hlo
    rw [cnotOddAndIdx_mulVec_ket uLo w qEnc hw hwq huq huw d hd δ hw0 hq0 (bStarFn δ) (hEv q),
      cnotOddAndIdx_mulVec_ket uLo w qEnc hw hwq huq huw d hd δ hw0 hq0 (bStarFn δ) (hOd q),
      ite_eq_right (hev q), ite_eq_left (hod q)]
    rcases DynCircExt.bit_cases (δ (uLo ⟨d, hd⟩)) with hu0 | hu1
    · rw [hu0, add_zero, add_zero, ket_projector_zero, ket_projector_zero, Function.update_self,
        Function.update_self, ite_eq_left rfl, ite_eq_right one_ne_zero, add_zero, hqId]
      exact congrArg (fun p ↦ ket (Function.update δ (w (bStarFn δ) p) 1)) (Fin.ext (hIdx0 hu0 q))
    · rw [hu1, zero_add, CharTwo.add_self_eq_zero, ket_projector_zero, ket_projector_zero,
        Function.update_self, Function.update_self, ite_eq_right one_ne_zero, ite_eq_left rfl,
        zero_add, hqId]
      exact congrArg (fun p ↦ ket (Function.update δ (w (bStarFn δ) p) 1)) (Fin.ext (hIdx1 hu1 q))
  · intro δ hw0 hq0 hqId q lo hlo
    have hpLo : lo + 2 ^ d * (2 * q.val) < 2 ^ k := shift_pos_lt (Nat.le_of_lt hd) hlo (hEv q)
    have htbLo : (lo + 2 ^ d * (2 * q.val)).testBit d = false :=
      (testBit_lo_add_mul_two_pow hlo).trans (decide_eq_false (by omega))
    have hpHi : (lo + 2 ^ d * (2 * q.val)) + 2 ^ d < 2 ^ k :=
      (by ring : (lo + 2 ^ d * (2 * q.val)) + 2 ^ d = lo + 2 ^ d * (2 * q.val + 1)).symm ▸
        shift_pos_lt (Nat.le_of_lt hd) hlo (hOd q)
    rw [cnotOddAndIdx_mulVec_ket uLo w qEnc hw hwq huq huw d hd δ hw0 hq0 (bStarFn δ) (hEv q),
      cnotOddAndIdx_mulVec_ket uLo w qEnc hw hwq huq huw d hd δ hw0 hq0 (bStarFn δ) (hOd q),
      ite_eq_right (hev q), ite_eq_left (hod q)]
    rcases DynCircExt.bit_cases (δ (uLo ⟨d, hd⟩)) with hu0 | hu1
    · rw [hu0, add_zero, add_zero, ← Matrix.mulVec_mulVec, ket_projector_one, Function.update_self,
        ite_eq_right zero_ne_one, Matrix.mulVec_zero, zero_add, ← Matrix.mulVec_mulVec,
        ← Matrix.mulVec_mulVec, ket_projector_one, Function.update_self, ite_eq_left rfl, ket_X,
        Function.update_self, CharTwo.add_self_eq_zero, Function.update_idem, hqId]
      exact (congrArg (fun p ↦ cB.eval.1.mulVec (ket (Function.update δ (w (bStarFn δ) p) 1)))
        (Fin.ext (by dsimp [lo]; ring))).trans
        ((barrelSwap_mulVec_ket_pair w hw d δ hw0 (bStarFn δ) hpLo htbLo hpHi true).trans
          (congrArg (fun p ↦ ket (Function.update δ (w (bStarFn δ) p) 1)) (Fin.ext (hIdx0 hu0 q))))
    · rw [hu1, zero_add, CharTwo.add_self_eq_zero, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
        ket_projector_one, Function.update_self, ite_eq_left rfl, ket_X, Function.update_self,
        CharTwo.add_self_eq_zero, Function.update_idem, hqId, ← Matrix.mulVec_mulVec,
        ket_projector_one, Function.update_self, ite_eq_right zero_ne_one, Matrix.mulVec_zero,
        add_zero]
      exact (barrelSwap_mulVec_ket_pair w hw d δ hw0 (bStarFn δ) hpLo htbLo hpHi false).trans
        (congrArg (fun p ↦ ket (Function.update δ (w (bStarFn δ) p) 1))
          (Fin.ext ((by dsimp; ring : _ = lo + 2 ^ d * (2 * q.val + 1)).trans (hIdx1 hu1 q))))

theorem subspaceStep_wShiftLevels {Var : Type} [Fintype Var] [DecidableEq Var] {n R k : ℕ}
    (v : Var) (bStarFn : BitAssignment n → Fin R) (uLo : Fin k → Wire n)
    (w : Fin R → Fin (2 ^ k) → Wire n) (qEnc : Wire n)
    (hw : WInj w) (hwq : ∀ b p, w b p ≠ qEnc) (huq : ∀ d, uLo d ≠ qEnc)
        (huw : ∀ d b p, uLo d ≠ w b p) :
    ∀ (m : ℕ) (hm : m ≤ k),
      SubspaceStep (wSuperOp bStarFn uLo w qEnc 0 (Nat.zero_le k))
        (wSuperOp bStarFn uLo w qEnc m hm)
        (wShiftLevels v R k uLo w qEnc hw hwq huq m hm)
  | 0, _ => by
      simpa only [wShiftLevels, Circuit.eval_identity, Submonoid.coe_one, Matrix.one_mul] using
        subspaceStep_of_circuit (Var := Var) (wSuperOp bStarFn uLo w qEnc 0 (Nat.zero_le k))
          (.identity : Circuit n)
  | d + 1, hd =>
      (subspaceStep_wShiftLevels v bStarFn uLo w qEnc hw hwq huq huw d (Nat.le_of_succ_le hd)).seq
        (subspaceStep_wShiftLevel v bStarFn uLo w qEnc hw hwq huq huw d hd)

/- Section 1: Self-inverse gate involutions, decidable disjointness, and block reshaping -/

private theorem ket_sr_eq {n : ℕ} (δ : BitAssignment n) :
    PhotochemistrySolution.SplitRouterSeqBell26k.ket δ = ket δ := rfl

private theorem eval_X_mul_self_loc {n : ℕ} (q : Wire n) : (Circuit.X q).eval.1 *
    (Circuit.X q).eval.1 = 1 := by
  refine matrix_ext_ket fun δ ↦
      by rw [← Matrix.mulVec_mulVec, ket_X, ket_X, Function.update_idem, Function.update_self,
           add_assoc, CharTwo.add_self_eq_zero, add_zero, Function.update_eq_self,
           Matrix.one_mulVec]

private theorem mulVec_X_invol {n : ℕ} (q : Wire n) (v : Fin (2 ^ n) → ℂ) :
    (Circuit.X q).eval.1.mulVec ((Circuit.X q).eval.1.mulVec v) =
    v := by rw [Matrix.mulVec_mulVec, eval_X_mul_self_loc, Matrix.one_mulVec]
private theorem eval_CNOT_mul_self_loc {n : ℕ} (c t : Wire n)
    (h : c ≠ t) : (Circuit.CNOT c t h).eval.1 * (Circuit.CNOT c t h).eval.1 = 1 := by
  exact matrix_ext_ket fun _ ↦
      by rw [← mulVec_mulVec, ket_CNOT, ket_CNOT, Function.update_idem, Function.update_self,
           Function.update_of_ne h, add_assoc, CharTwo.add_self_eq_zero, add_zero,
           Function.update_eq_self, one_mulVec]

private theorem mulVec_CNOT_invol {n : ℕ} (c t : Wire n) (h : c ≠ t) (v : Fin (2 ^ n) → ℂ) :
    (Circuit.CNOT c t h).eval.1.mulVec ((Circuit.CNOT c t h).eval.1.mulVec v) =
    v := by rw [Matrix.mulVec_mulVec, eval_CNOT_mul_self_loc, Matrix.one_mulVec]
private theorem ket_CNOT_of_ctrl_zero {n : ℕ} {c t : Wire n} (h : c ≠ t) {β : BitAssignment n}
    (hc : β c = 0) : (Circuit.CNOT c t h).eval.1.mulVec (ket β) =
    ket β := by rw [ket_CNOT, hc, add_zero, Function.update_eq_self]
private theorem projBit_zero_mulVec_ket {n : ℕ} (q : Wire n) (δ : BitAssignment n) :
    (projBit q 0).mulVec (ket δ) = if δ q = 0 then ket δ else 0 :=
  ket_projector_zero q δ

/-- Decidable disjointness proposition equivalent to `WRouterDisj`. -/
def WRouterDisjProp {D N n : ℕ} (wHas : Wire n) (wIdx : Fin D → Wire n) (wOut : Fin N → Wire n)
    (qEnc : Wire n) : Prop :=
    (∀ j, wHas ≠ wOut j) ∧ wHas ≠ qEnc ∧ (∀ d j, wIdx d ≠ wOut j) ∧ (∀ d, wIdx d ≠ qEnc) ∧
    (∀ i j, i ≠ j → wOut i ≠ wOut j) ∧ (∀ j, wOut j ≠ qEnc)
instance instDecidableWRouterDisjProp {D N n : ℕ} (wHas : Wire n) (wIdx : Fin D → Wire n)
    (wOut : Fin N → Wire n) (qEnc : Wire n) : Decidable (WRouterDisjProp wHas wIdx wOut qEnc)
    := by unfold WRouterDisjProp; infer_instance
/-- Output-only disjointness proposition for `0-T` MBU uncomputation (independent of `qEnc`). -/
def WRouterOutDisj {D N n : ℕ} (wHas : Wire n) (wIdx : Fin D → Wire n) (wOut : Fin N → Wire n) :
    Prop := (∀ j, wHas ≠ wOut j) ∧ (∀ d j, wIdx d ≠ wOut j) ∧ (∀ i j, i ≠ j → wOut i ≠ wOut j)
instance instDecidableWRouterOutDisj {D N n : ℕ} (wHas : Wire n) (wIdx : Fin D → Wire n)
    (wOut : Fin N → Wire n) : Decidable (WRouterOutDisj wHas wIdx wOut)
    := by unfold WRouterOutDisj; infer_instance
theorem WRouterDisj.disjProp {D N n : ℕ} {wHas : Wire n} {wIdx : Fin D → Wire n}
    {wOut : Fin N → Wire n} {qEnc : Wire n} (hd : WRouterDisj wHas wIdx wOut qEnc) :
    WRouterDisjProp wHas wIdx wOut qEnc :=
    ⟨hd.has_ne_out, hd.has_ne_q, hd.idx_ne_out, hd.idx_ne_q, hd.out_inj, hd.out_ne_q⟩
theorem WRouterDisj.outDisj {D N n : ℕ} {wHas : Wire n} {wIdx : Fin D → Wire n}
    {wOut : Fin N → Wire n} {qEnc : Wire n} (hd : WRouterDisj wHas wIdx wOut qEnc) :
    WRouterOutDisj wHas wIdx wOut := ⟨hd.has_ne_out, hd.idx_ne_out, hd.out_inj⟩
theorem blockIdx_lt {R k N : ℕ} (hRN : R * 2 ^ k = N) (b : Fin R) (p : Fin (2 ^ k)) : b.val *
    2 ^ k + p.val < N := by rw [← hRN]; exact (enc_div_mod b.isLt p.isLt).1
/-- Reshape `wOut : Fin N → Wire n` (`R * 2^k = N`) into `R` blocks of `2^k` wires. -/
abbrev blockWires {R k N n : ℕ} (hRN : R * 2 ^ k = N) (wOut : Fin N → Wire n) (b : Fin R)
    (p : Fin (2 ^ k)) : Wire n := wOut ⟨b.val * 2 ^ k + p.val, blockIdx_lt hRN b p⟩
theorem wInj_blockWires {R k N n : ℕ} (hRN : R * 2 ^ k = N) {wOut : Fin N → Wire n}
    (hInj : ∀ i j, i ≠ j → wOut i ≠ wOut j) :
    WInj (blockWires hRN wOut) := fun b₁ p₁ b₂ p₂ heq ↦ by
  have hv : b₁.val * 2 ^ k + p₁.val = b₂.val * 2 ^ k + p₂.val :=
      congrArg Fin.val (Decidable.byContradiction fun hne ↦ hInj _ _ hne heq)
  obtain ⟨⟨_, hd₁, hm₁⟩, _, hd₂, hm₂⟩ :=
      And.intro (enc_div_mod b₁.isLt p₁.isLt) (enc_div_mod b₂.isLt p₂.isLt)
  exact ⟨Fin.ext (hd₁.symm.trans ((congrArg (· / 2 ^ k) hv).trans hd₂)),
      Fin.ext (hm₁.symm.trans ((congrArg (· % 2 ^ k) hv).trans hm₂))⟩

/-- Prefix slice of the lower `k ≤ D` index wires. -/
abbrev uLoOf {k D n : ℕ} (hk : k ≤ D) (wIdx : Fin D → Wire n) (d : Fin k) : Wire n :=
    wIdx ⟨d.val, Nat.lt_of_lt_of_le d.isLt hk⟩
theorem idxValPrefix_uLoOf {k D n : ℕ} (hk : k ≤ D) (wIdx : Fin D → Wire n) (δ : BitAssignment n) :
    ∀ (m : ℕ) (hm : m ≤ k),
      idxValPrefix (uLoOf hk wIdx) δ m hm = idxValPrefix wIdx δ m (Nat.le_trans hm hk)
  | 0, _ => rfl
  | m + 1, hm =>
        by simpa only [idxValPrefix, uLoOf] using congrArg (· + _)
             (idxValPrefix_uLoOf hk wIdx δ m (Nat.le_of_succ_le hm))
/- Section 2: Zero-gating and `0-T` MBU reverse CH-tree uncomputation -/

/--
Forward `0-T` zero-gating pair clearing `t0` when `wHas = 0` and preserving kets when `wHas = 1` .
-/
def wZeroGate {n : ℕ} (wHas t0 : Wire n) (h : wHas ≠ t0) : Circuit n :=
  Circuit.X t0 ;;ᶜ Circuit.CNOT wHas t0 h

/-- Reverse `0-T` unzero-gating pair restoring `t0 = 1` when `wHas = 0`. -/
def wUnzeroGate {n : ℕ} (wHas t0 : Wire n) (h : wHas ≠ t0) : Circuit n :=
  Circuit.CNOT wHas t0 h ;;ᶜ Circuit.X t0

private theorem wZeroGate_mulVec_ket {n : ℕ} {wHas t0 tStar : Wire n} (hHas0 : wHas ≠ t0)
    (hHasStar : wHas ≠ tStar) {δ : BitAssignment n} (hZero : δ wHas = 0 → tStar = t0) :
    (wZeroGate wHas t0 hHas0).eval.1.mulVec (ket (Function.update δ tStar 1)) =
    ket (Function.update δ tStar (δ wHas)) := by
  rcases DynCircExt.bit_cases (δ wHas) with h0 | h1
  · rw [hZero h0, h0, wZeroGate, eval_seq_mulVec, ket_X, Function.update_idem, Function.update_self,
        CharTwo.add_self_eq_zero, ket_CNOT, Function.update_idem, Function.update_self,
        Function.update_of_ne hHas0, h0, add_zero]
  · let β := Function.update δ tStar 1;
    have hβHas : β wHas = 1 :=
        (Function.update_of_ne hHasStar 1 δ).trans h1; rw [h1]; change (wZeroGate wHas t0
        hHas0).eval.1.mulVec (ket β) = ket β; rw [wZeroGate, eval_seq_mulVec, ket_X, ket_CNOT,
        Function.update_idem, Function.update_self, Function.update_of_ne hHas0, hβHas, add_assoc,
        CharTwo.add_self_eq_zero, add_zero, Function.update_eq_self]
private theorem wUnzeroGate_mulVec_ket {n : ℕ} {wHas t0 tStar : Wire n} (hHas0 : wHas ≠ t0)
    (hHasStar : wHas ≠ tStar) {δ : BitAssignment n} (hZero : δ wHas = 0 → tStar = t0) :
    (wUnzeroGate wHas t0 hHas0).eval.1.mulVec (ket (Function.update δ tStar (δ wHas))) =
    ket (Function.update δ tStar 1)
    := by rw [← wZeroGate_mulVec_ket hHas0 hHasStar hZero]; simp only [wUnzeroGate, wZeroGate,
            eval_seq_mulVec, mulVec_CNOT_invol, mulVec_X_invol]
private theorem wSuperVec_bot {n R k : ℕ} (bStarFn : BitAssignment n → Fin R) (uLo : Fin k → Wire n)
    (w : Fin R → Fin (2 ^ k) → Wire n) (hw : WInj w) (qEnc : Wire n) (δ : BitAssignment n)
    (hw0 : ∀ b p, δ (w b p) = 0) (hq0 : δ qEnc = 0) :
    (wTreePrefix R k w hw k le_rfl).eval.1.mulVec (ket (Function.update δ (w (bStarFn δ)
    ⟨0, Nat.two_pow_pos k⟩) 1)) = wSuperVec bStarFn uLo w qEnc δ 0 (Nat.zero_le k) := by
  rw [wTreePrefix_mulVec_ket w hw δ hw0 (bStarFn δ) k le_rfl]
  dsimp only [wSuperVec]
  let e : Fin (2 ^ k) ≃ Fin (2 ^ (k - 0)) := finCongr (congrArg (2 ^ ·) (Nat.sub_zero k).symm)
  rw [ite_eq_left ⟨hw0, hq0⟩, ← e.sum_comp, show sqrtHalf ^ (k - 0) =
      sqrtHalf ^ k from congrArg _ (Nat.sub_zero k)]
  exact congrArg (_ • ·) (Finset.sum_congr rfl fun s _ ↦
    congrArg (fun p ↦ ket (Function.update δ (w (bStarFn δ) p) 1)) (Fin.ext (by
      dsimp [e, idxValPrefix]
      omega)))

private theorem wSuperVec_top {n R k : ℕ} (bStarFn : BitAssignment n → Fin R) (uLo : Fin k → Wire n)
    (w : Fin R → Fin (2 ^ k) → Wire n) (qEnc : Wire n) (δ : BitAssignment n)
    (hw0 : ∀ b p, δ (w b p) = 0) (hq0 : δ qEnc = 0) : wSuperVec bStarFn uLo w qEnc δ k le_rfl =
    ket (Function.update δ (w (bStarFn δ)
    ⟨idxValPrefix uLo δ k le_rfl, idxValPrefix_lt_two_pow uLo δ k le_rfl⟩) 1) := by
  dsimp only [wSuperVec]
  rw [ite_eq_left ⟨hw0, hq0⟩, show sqrtHalf ^ (k - k) = 1 by rw [Nat.sub_self, _root_.pow_zero],
      one_smul,
    Finset.sum_eq_single ⟨0, Nat.two_pow_pos (k - k)⟩
      (fun hi _ hne ↦
          absurd (Fin.ext (Nat.lt_one_iff.mp
          (by simpa only [Nat.sub_self, _root_.pow_zero] using hi.isLt))) hne)
      (fun habs ↦ (habs (Finset.mem_univ _)).elim)]
  exact congrArg (fun p ↦ ket (Function.update δ (w (bStarFn δ) p) 1)) (Fin.ext (by dsimp))

/-- Lower partner wire in reverse CH-tree round `r < k` at flat index `i < R * 2^r`. -/
def qLo {n : ℕ} (R k : ℕ) (w : Fin R → Fin (2 ^ k) → Wire n) (r : ℕ) (hr : r < k) (i : ℕ)
    (hi : i < R * 2 ^ r) : Wire n :=
  w ⟨i / 2 ^ r, div_lt_of_lt_mul_right (Nat.two_pow_pos r) hi⟩
    ⟨i % 2 ^ r, pair_lo_lt hr (Nat.mod_lt i (Nat.two_pow_pos r))⟩

/-- Upper partner wire in reverse CH-tree round `r < k` at flat index `i < R * 2^r`. -/
def qUp {n : ℕ} (R k : ℕ) (w : Fin R → Fin (2 ^ k) → Wire n) (r : ℕ) (hr : r < k) (i : ℕ)
    (hi : i < R * 2 ^ r) : Wire n :=
    w ⟨i / 2 ^ r, div_lt_of_lt_mul_right (Nat.two_pow_pos r) hi⟩
    ⟨i % 2 ^ r + 2 ^ r, pair_hi_lt hr (Nat.mod_lt i (Nat.two_pow_pos r))⟩
theorem qLo_ne_qUp {n R k : ℕ} {w : Fin R → Fin (2 ^ k) → Wire n} (hw : WInj w) {r : ℕ} (hr : r < k)
    {i₁ i₂ : ℕ} (hi₁ : i₁ < R * 2 ^ r) (hi₂ : i₂ < R * 2 ^ r) :
    qLo R k w r hr i₁ hi₁ ≠ qUp R k w r hr i₂ hi₂ :=
  w_ne_of_pair_ne hw (Or.inr fun e ↦ absurd (congrArg Fin.val e)
      (Nat.ne_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt i₁ (Nat.two_pow_pos r)) (Nat.le_add_left _ _))))

private theorem qUp_ne_of_ne {n R k : ℕ} {w : Fin R → Fin (2 ^ k) → Wire n} (hw : WInj w)
    {r : ℕ} (hr : r < k) {i₁ i₂ : ℕ} (hi₁ : i₁ < R * 2 ^ r) (hi₂ : i₂ < R * 2 ^ r)
    (hne : i₁ ≠ i₂) : qUp R k w r hr i₁ hi₁ ≠ qUp R k w r hr i₂ hi₂ := fun e ↦ by
  obtain ⟨hb, hp⟩ := hw _ _ _ _ e; have hdiv : i₁ / 2 ^ r = i₂ / 2 ^ r := congrArg Fin.val hb;
  have hmod : i₁ % 2 ^ r + 2 ^ r = i₂ % 2 ^ r + 2 ^ r := congrArg Fin.val hp
  have hmod' : i₁ % 2 ^ r = i₂ % 2 ^ r := by omega
  have hd₁ := Nat.div_add_mod i₁ (2 ^ r);
  have hd₂ := Nat.div_add_mod i₂ (2 ^ r); rw [hdiv, hmod'] at hd₁; exact hne (hd₁.symm.trans hd₂)
/-- Single-pair CZ target list `[(qLo, uLo r)]` for X-measurement uncomputation of `qUp`. -/
def pairOf {n : ℕ} (R k : ℕ) (uLo : Fin k → Wire n) (w : Fin R → Fin (2 ^ k) → Wire n)
    (huw : ∀ d b p, uLo d ≠ w b p) (r : ℕ) (hr : r < k) (i : ℕ) (hi : i < R * 2 ^ r) :
    List (WirePair n) := [⟨qLo R k w r hr i hi, ⟨uLo ⟨r, hr⟩, (huw ⟨r, hr⟩ _ _).symm⟩⟩]
private def fPair {n : ℕ} (R k : ℕ) (uLo : Fin k → Wire n) (w : Fin R → Fin (2 ^ k) → Wire n)
    (huw : ∀ d b p, uLo d ≠ w b p) (r : ℕ) (hr : r < k) (i : ℕ) (hi : i < R * 2 ^ r)
    (β : BitAssignment n) : ZMod 2 := czPairsParity (pairOf R k uLo w huw r hr i hi) β
private theorem fPair_indep {n : ℕ} (R k : ℕ) (uLo : Fin k → Wire n)
    (w : Fin R → Fin (2 ^ k) → Wire n) (hw : WInj w) (huw : ∀ d b p, uLo d ≠ w b p) (r : ℕ)
    (hr : r < k) (i : ℕ) (hi : i < R * 2 ^ r) (β : BitAssignment n)
    (a : ZMod 2) : fPair R k uLo w huw r hr i hi (Function.update β (qUp R k w r hr i hi) a) =
    fPair R k uLo w huw r hr i hi β := by have huw' : uLo ⟨r, hr⟩ ≠ qUp R k w r hr i hi :=
                                            huw ⟨r, hr⟩ _ _; dsimp only [fPair, pairOf,
                                            czPairsParity]; rw [Function.update_of_ne (qLo_ne_qUp hw
                                            hr hi hi), Function.update_of_ne huw']
/-- Reverse CNOT gather round `r < k` folding `qUp` into `qLo` across all `R * 2^r` pairs. -/
def wUncompCnotRound {n : ℕ} (R k : ℕ) (w : Fin R → Fin (2 ^ k) → Wire n) (hw : WInj w) (r : ℕ)
    (hr : r < k) : Circuit n := seqNat (R * 2 ^ r) fun i hi ↦
    Circuit.CNOT (qUp R k w r hr i hi) (qLo R k w r hr i hi) (qLo_ne_qUp hw hr hi hi).symm
private def upperXorBits {n : ℕ} (R k : ℕ) (uLo : Fin k → Wire n)
    (w : Fin R → Fin (2 ^ k) → Wire n) (huw : ∀ d b p, uLo d ≠ w b p)
    (r : ℕ) (hr : r < k) : (m : ℕ) → m ≤ R * 2 ^ r → BitAssignment n → BitAssignment n
  | 0, _, β => β
  | m + 1, hm, β =>
      let β' := upperXorBits R k uLo w huw r hr m (Nat.le_of_succ_le hm) β
      Function.update β' (qUp R k w r hr m hm)
        (β' (qUp R k w r hr m hm) + fPair R k uLo w huw r hr m hm β')

private theorem upperXorBits_of_ne {n : ℕ} (R k : ℕ) (uLo : Fin k → Wire n)
    (w : Fin R → Fin (2 ^ k) → Wire n) (huw : ∀ d b p, uLo d ≠ w b p)
    (r : ℕ) (hr : r < k) (β : BitAssignment n) (u : Wire n) :
    ∀ (m : ℕ) (hm : m ≤ R * 2 ^ r),
      (∀ i (hi : i < m), u ≠ qUp R k w r hr i (Nat.lt_of_lt_of_le hi hm)) →
      upperXorBits R k uLo w huw r hr m hm β u = β u
  | 0, _, _ => rfl
  | m + 1, hm, hne => by
      dsimp only [upperXorBits]
      rw [Function.update_of_ne (hne m (Nat.lt_succ_self m)),
          upperXorBits_of_ne R k uLo w huw r hr β u m (Nat.le_of_succ_le hm)
          (fun i hi ↦ hne i (Nat.lt_succ_of_lt hi))]

private theorem upperXorBits_qUp_lt {n : ℕ} (R k : ℕ) (uLo : Fin k → Wire n)
    (w : Fin R → Fin (2 ^ k) → Wire n) (hw : WInj w) (huw : ∀ d b p, uLo d ≠ w b p)
    (r : ℕ) (hr : r < k) (β : BitAssignment n) :
    ∀ (m : ℕ) (hm : m ≤ R * 2 ^ r) (i : ℕ) (hi : i < m),
      let hiR := Nat.lt_of_lt_of_le hi hm
      upperXorBits R k uLo w huw r hr m hm β (qUp R k w r hr i hiR) = β (qUp R k w r hr i hiR) +
          β (qLo R k w r hr i hiR) * β (uLo ⟨r, hr⟩)
  | 0, _, _, hi => absurd hi (Nat.not_lt_zero _)
  | m + 1, hm, i, hi => by
      dsimp only [upperXorBits]
      by_cases him : i = m
      · subst him
        dsimp only [fPair, pairOf, czPairsParity]
        rw [Function.update_self,
          upperXorBits_of_ne R k uLo w huw r hr β (qUp R k w r hr i hm) i (Nat.le_of_succ_le hm)
              fun _ hj ↦ qUp_ne_of_ne hw hr hm _ (Nat.ne_of_gt hj),
          upperXorBits_of_ne R k uLo w huw r hr β (qLo R k w r hr i hm) i (Nat.le_of_succ_le hm)
              fun _ _ ↦ qLo_ne_qUp hw hr hm _,
          upperXorBits_of_ne R k uLo w huw r hr β (uLo ⟨r, hr⟩) i (Nat.le_of_succ_le hm) fun _ _ ↦
              huw ⟨r, hr⟩ _ _, add_zero]
      · rw [Function.update_of_ne (qUp_ne_of_ne hw hr _ hm him),
            upperXorBits_qUp_lt R k uLo w hw huw r hr β m (Nat.le_of_succ_le hm) i (by omega)]

private def uUpperXorPrefix {n : ℕ} (R k : ℕ) (uLo : Fin k → Wire n)
    (w : Fin R → Fin (2 ^ k) → Wire n) (hw : WInj w) (huw : ∀ d b p, uLo d ≠ w b p)
    (r : ℕ) (hr : r < k) : (m : ℕ) → m ≤ R * 2 ^ r → Operator (2 ^ n)
  | 0, _ => 1
  | m + 1, hm =>
      (xorWireUnitary (qUp R k w r hr m hm) (fPair R k uLo w huw r hr m hm)
        (fPair_indep R k uLo w hw huw r hr m hm)).1 *
      uUpperXorPrefix R k uLo w hw huw r hr m (Nat.le_of_succ_le hm)

private theorem uUpperXorPrefix_mulVec_ket {n : ℕ} (R k : ℕ) (uLo : Fin k → Wire n)
    (w : Fin R → Fin (2 ^ k) → Wire n) (hw : WInj w) (huw : ∀ d b p, uLo d ≠ w b p)
    (r : ℕ) (hr : r < k) (β : BitAssignment n) :
    ∀ (m : ℕ) (hm : m ≤ R * 2 ^ r),
      (uUpperXorPrefix R k uLo w hw huw r hr m hm).mulVec (ket β) =
        ket (upperXorBits R k uLo w huw r hr m hm β)
  | 0, _ => Matrix.one_mulVec _
  | m + 1, hm => by
      rw [uUpperXorPrefix, ← Matrix.mulVec_mulVec,
        uUpperXorPrefix_mulVec_ket R k uLo w hw huw r hr β m (Nat.le_of_succ_le hm),
        xorWireUnitary_mulVec_ket]
      rfl
/--
Sequential `0-T` X-measurement + conditional CZ unloader for the `m` upper wires of round `r` .
-/
def wUncompMeasPrefix {Var : Type} {n : ℕ} (v : Var) (R k : ℕ) (uLo : Fin k → Wire n)
    (w : Fin R → Fin (2 ^ k) → Wire n) (huw : ∀ d b p, uLo d ≠ w b p)
    (r : ℕ) (hr : r < k) (rest : DynamicCircuit Var n) :
    (m : ℕ) → m ≤ R * 2 ^ r → DynamicCircuit Var n
  | 0, _ => rest
  | m + 1, hm =>
      xUnloadCzPairsSeqDyn v (qUp R k w r hr m hm) (pairOf R k uLo w huw r hr m hm)
        (wUncompMeasPrefix v R k uLo w huw r hr rest m (Nat.le_of_succ_le hm))

private theorem count_wUncompMeasPrefix {Var : Type} {n : ℕ} (v : Var) (R k : ℕ)
    (uLo : Fin k → Wire n) (w : Fin R → Fin (2 ^ k) → Wire n) (huw : ∀ d b p, uLo d ≠ w b p)
    (r : ℕ) (hr : r < k) (rest : DynamicCircuit Var n) :
    ∀ (m : ℕ) (hm : m ≤ R * 2 ^ r),
      (wUncompMeasPrefix v R k uLo w huw r hr rest m hm).count .T = rest.count .T ∧
      (wUncompMeasPrefix v R k uLo w huw r hr rest m hm).count .TOFF = rest.count .TOFF
  | 0, _ => ⟨rfl, rfl⟩
  | m + 1, hm => by
      obtain ⟨ht, hf⟩ :=
          count_wUncompMeasPrefix v R k uLo w huw r hr rest m (Nat.le_of_succ_le hm); obtain ⟨xt,
          xf⟩ := count_xUnloadCzPairsSeqDyn v (qUp R k w r hr m hm) (pairOf R k uLo w huw r hr m hm)
          (wUncompMeasPrefix v R k uLo w huw r hr rest m (Nat.le_of_succ_le hm));
          dsimp only [wUncompMeasPrefix]; exact ⟨xt.trans ht, xf.trans hf⟩
private theorem dw_wUncompMeasPrefix {Var : Type} {n : ℕ} {S : Wire n → Prop} (v : Var) (R k : ℕ)
    (uLo : Fin k → Wire n) (w : Fin R → Fin (2 ^ k) → Wire n) (huw : ∀ d b p, uLo d ≠ w b p)
    (huS : ∀ d, S (uLo d)) (hwS : ∀ b p, S (w b p))
    (r : ℕ) (hr : r < k) {rest : DynamicCircuit Var n} (hRest : DynWires S rest) :
    ∀ (m : ℕ) (hm : m ≤ R * 2 ^ r), DynWires S (wUncompMeasPrefix v R k uLo w huw r hr rest m hm)
  | 0, _ => hRest
  | m + 1, hm =>
      dw_xUnload (hwS _ _) (fun _ hp ↦ (List.mem_singleton.mp hp).symm ▸ ⟨hwS _ _, huS _⟩)
        (dw_wUncompMeasPrefix v R k uLo w huw huS hwS r hr hRest m (Nat.le_of_succ_le hm))

/--
Pre-shift one-hot vector at tree level `m ≤ k` on kets satisfying `P δ ∧ ∀ b p, δ (w b p) = 0` .
-/
def oneHotPreVec {n R k : ℕ} (P : BitAssignment n → Prop) [DecidablePred P]
    (bStarFn : BitAssignment n → Fin R) (uLo : Fin k → Wire n) (w : Fin R → Fin (2 ^ k) → Wire n)
    (δ : BitAssignment n) (m : ℕ) (hm : m ≤ k) : Fin (2 ^ n) → ℂ :=
  if P δ ∧ ∀ b p, δ (w b p) = 0 then
    ket (Function.update δ
      (w (bStarFn δ) ⟨idxValPrefix uLo δ m hm,
        Nat.lt_of_lt_of_le (idxValPrefix_lt_two_pow uLo δ m hm)
          (Nat.pow_le_pow_right (by omega) hm)⟩) 1)
  else 0

/-- Operator mapping computational basis kets via `oneHotPreVec`. -/
def oneHotPreOp {n R k : ℕ} (P : BitAssignment n → Prop) [DecidablePred P]
    (bStarFn : BitAssignment n → Fin R) (uLo : Fin k → Wire n) (w : Fin R → Fin (2 ^ k) → Wire n)
    (m : ℕ) (hm : m ≤ k) : Operator (2 ^ n) := mkVecOp fun δ ↦ oneHotPreVec P bStarFn uLo w δ m hm
private theorem oneHotPreOp_mulVec_ket {n R k : ℕ} (P : BitAssignment n → Prop) [DecidablePred P]
    (bStarFn : BitAssignment n → Fin R) (uLo : Fin k → Wire n) (w : Fin R → Fin (2 ^ k) → Wire n)
    (m : ℕ) (hm : m ≤ k) (δ : BitAssignment n) : (oneHotPreOp P bStarFn uLo w m hm).mulVec (ket δ) =
    oneHotPreVec P bStarFn uLo w δ m hm := mkVecOp_mulVec_ket _ δ
set_option allowUnsafeReducibility true in
attribute [local irreducible] oneHotPreOp

private theorem projBit_zero_uUpperXorPrefix_oneHotPreOp {n R k : ℕ} (P : BitAssignment n → Prop)
    [DecidablePred P] (bStarFn : BitAssignment n → Fin R) (uLo : Fin k → Wire n)
    (w : Fin R → Fin (2 ^ k) → Wire n) (hw : WInj w) (huw : ∀ d b p, uLo d ≠ w b p) (r : ℕ)
    (hr : r < k) (m : ℕ) (hm : m < R * 2 ^ r) : projBit (qUp R k w r hr m hm) 0 *
    (uUpperXorPrefix R k uLo w hw huw r hr m (Nat.le_of_succ_le hm) *
    oneHotPreOp P bStarFn uLo w r (Nat.le_of_lt hr)) =
    uUpperXorPrefix R k uLo w hw huw r hr m (Nat.le_of_succ_le hm) *
    oneHotPreOp P bStarFn uLo w r (Nat.le_of_lt hr) := by
  refine matrix_ext_ket fun δ ↦ ?_
  simp only [← Matrix.mulVec_mulVec, oneHotPreOp_mulVec_ket, oneHotPreVec]
  by_cases hV : P δ ∧ ∀ b p, δ (w b p) = 0
  · rw [ite_eq_left hV, uUpperXorPrefix_mulVec_ket, projBit_zero_mulVec_ket]
    have hneLo : w (bStarFn δ) ⟨idxValPrefix uLo δ r (Nat.le_of_lt hr),
        Nat.lt_of_lt_of_le (idxValPrefix_lt_two_pow uLo δ r (Nat.le_of_lt hr))
            (Nat.pow_le_pow_right (by omega) (Nat.le_of_lt hr))⟩ ≠ qUp R k w r hr m hm :=
      w_ne_of_pair_ne hw (Or.inr fun e ↦ absurd (congrArg Fin.val e)
        (Nat.ne_of_lt (Nat.lt_of_lt_of_le (idxValPrefix_lt_two_pow uLo δ r (Nat.le_of_lt hr))
            (Nat.le_add_left _ _))))
    exact ite_eq_left ((upperXorBits_of_ne R k uLo w huw r hr _ _ m (Nat.le_of_succ_le hm)
      fun _ hi ↦
          qUp_ne_of_ne hw hr hm _ (Nat.ne_of_gt hi)).trans ((Function.update_of_ne hneLo.symm 1
          δ).trans (hV.2 _ _)))
  · rw [ite_eq_right hV, Matrix.mulVec_zero, Matrix.mulVec_zero]

private theorem subspaceStep_wUncompMeasPrefix {Var : Type} [Fintype Var] [DecidableEq Var]
    {n R k : ℕ}
    (v : Var) (P : BitAssignment n → Prop) [DecidablePred P] (bStarFn : BitAssignment n → Fin R)
    (uLo : Fin k → Wire n) (w : Fin R → Fin (2 ^ k) → Wire n) (hw : WInj w)
        (huw : ∀ d b p, uLo d ≠ w b p)
    (r : ℕ) (hr : r < k) {rest : DynamicCircuit Var n} {R_out : Operator (2 ^ n)}
    (hRest : SubspaceStep (oneHotPreOp P bStarFn uLo w r (Nat.le_of_lt hr)) R_out rest) :
    ∀ (m : ℕ) (hm : m ≤ R * 2 ^ r),
      SubspaceStep (uUpperXorPrefix R k uLo w hw huw r hr m hm *
          oneHotPreOp P bStarFn uLo w r (Nat.le_of_lt hr)) R_out
        (wUncompMeasPrefix v R k uLo w huw r hr rest m hm)
  | 0, _ => by simpa only [uUpperXorPrefix, Matrix.one_mul, wUncompMeasPrefix] using hRest
  | m + 1, hm => by
      dsimp only [uUpperXorPrefix, wUncompMeasPrefix]
      rw [Matrix.mul_assoc]
      exact subspaceStep_xUnloadCzPairsSeqDyn v _ _ _ _ (fPair_indep R k uLo w hw huw r hr m hm)
          (fun _ ↦ rfl) _ R_out
        (projBit_zero_uUpperXorPrefix_oneHotPreOp P bStarFn uLo w hw huw r hr m hm)
        (subspaceStep_wUncompMeasPrefix v P bStarFn uLo w hw huw r hr hRest m (Nat.le_of_succ_le
            hm))
private theorem wUncompCnotRound_mul_oneHotPreOp {n R k : ℕ} (P : BitAssignment n → Prop)
    [DecidablePred P] (bStarFn : BitAssignment n → Fin R) (uLo : Fin k → Wire n)
    (w : Fin R → Fin (2 ^ k) → Wire n) (hw : WInj w) (huw : ∀ d b p, uLo d ≠ w b p) (r : ℕ)
    (hr : r < k) : (wUncompCnotRound R k w hw r hr).eval.1 * oneHotPreOp P bStarFn uLo w (r +
    1) hr = uUpperXorPrefix R k uLo w hw huw r hr (R * 2 ^ r) le_rfl *
    oneHotPreOp P bStarFn uLo w r (Nat.le_of_lt hr) := by
  refine matrix_ext_ket fun δ ↦ ?_
  simp only [← Matrix.mulVec_mulVec, oneHotPreOp_mulVec_ket, oneHotPreVec]
  by_cases hV : P δ ∧ ∀ b p, δ (w b p) = 0
  · have hw0 := hV.2
    rw [ite_eq_left hV, ite_eq_left hV, uUpperXorPrefix_mulVec_ket]
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
    have hqLo₀ : qLo R k w r hr i₀ hi₀ = w bStar pLo := congrArg₂ w (Fin.ext hdiv₀) (Fin.ext hmod₀)
    have hMidUp0 (i : ℕ) (hi : i < R * 2 ^ r) : δMid (qUp R k w r hr i hi) = 0 :=
      (Function.update_of_ne (hqLo₀ ▸ (qLo_ne_qUp hw hr hi₀ hi).symm) 1 δ).trans (hw0 _ _)
    have hneLoHi : w bStar pLo ≠ w bStar pHi := hqLo₀ ▸ hqUp₀ ▸ qLo_ne_qUp hw hr hi₀ hi₀
    let pIn : Fin (2 ^ k) := ⟨idxValPrefix uLo δ (r + 1) hr,
      (idxValPrefix_lt_two_pow uLo δ (r + 1) hr).trans_le (Nat.pow_le_pow_right (by omega) hr)⟩
    have hLHS : (wUncompCnotRound R k w hw r hr).eval.1.mulVec
        (ket (Function.update δ (w bStar pIn) 1)) = ket δAfter := by
      let fGate (i : ℕ) (hi : i < R * 2 ^ r) :=
          Circuit.CNOT (qUp R k w r hr i hi) (qLo R k w r hr i hi) (qLo_ne_qUp hw hr hi hi).symm
      dsimp only [wUncompCnotRound]
      rcases DynCircExt.bit_cases (δ (uLo ⟨r, hr⟩)) with hu0 | hu1
      · rw [show pIn = pLo from Fin.ext (by simp [pIn, idxValPrefix, pLo, sLo, hu0]),
          show δAfter = δMid from (congrArg (Function.update δMid (w bStar pHi)) hu0).trans
            (((Function.update_of_ne hneLoHi.symm 1 δ).trans (hw0 bStar pHi)) ▸
              Function.update_eq_self (w bStar pHi) δMid)]
        exact seqNat_mulVec_fixed (ket δMid) (R * 2 ^ r) fGate fun i hi ↦
          ket_CNOT_of_ctrl_zero _ (hMidUp0 i hi)
      · have hpEq : pIn = pHi := Fin.ext (by simp [pIn, idxValPrefix, pHi, sLo, hu1])
        rw [hpEq]
        have hSeq :=
            seqNat_mulVec_single (ket (Function.update δ (w bStar pHi) 1))
            (ket δAfter) i₀ (R * 2 ^ r) fGate
          (fun i hi hlt ↦
              ket_CNOT_of_ctrl_zero _ ((Function.update_of_ne (hqUp₀ ▸ qUp_ne_of_ne hw hr hi hi₀
              (Nat.ne_of_lt hlt)) 1 δ).trans (hw0 _ _)))
          (fun _ ↦ by
            dsimp only [fGate, δAfter, δMid]
            rw [ket_CNOT, hqUp₀, hqLo₀, Function.update_of_ne hneLoHi, hw0 bStar pLo,
              Function.update_self, zero_add, Function.update_comm hneLoHi.symm, hu1])
          (fun i hi hgt ↦
              ket_CNOT_of_ctrl_zero _ ((Function.update_of_ne (show qUp R k w r hr i hi ≠
              w bStar pHi from hqUp₀ ▸ qUp_ne_of_ne hw hr hi hi₀ (Nat.ne_of_gt hgt))
              (δ (uLo ⟨r, hr⟩)) δMid).trans (hMidUp0 i hi)))
        rwa [ite_eq_left hi₀] at hSeq
    rw [hLHS]
    refine congrArg ket (funext fun u ↦ ?_)
    by_cases hU : ∃ idx : Fin (R * 2 ^ r), u = qUp R k w r hr idx.val idx.isLt
    · obtain ⟨⟨i, hi⟩, rfl⟩ := hU
      rw [upperXorBits_qUp_lt R k uLo w hw huw r hr δMid _ le_rfl i hi, hMidUp0 i hi, zero_add]
      dsimp only [δAfter, δMid]
      rw [Function.update_of_ne (huw ⟨r, hr⟩ _ _)]
      by_cases hii₀ : i = i₀
      · subst hii₀
        rw [hqUp₀, hqLo₀, Function.update_self, Function.update_self, one_mul]
      · have hneLo : qLo R k w r hr i hi ≠ w bStar pLo := w_ne_of_enc_ne hw hii₀ id
        rw [Function.update_of_ne (hqUp₀ ▸ qUp_ne_of_ne hw hr hi hi₀ hii₀),
          Function.update_of_ne hneLo, show δ (qLo R k w r hr i hi) = 0 from hw0 _ _, zero_mul]
        exact hMidUp0 i hi
    · dsimp only [δAfter]
      rw [Function.update_of_ne (hqUp₀ ▸ fun e ↦ hU ⟨⟨i₀, hi₀⟩, e⟩),
        upperXorBits_of_ne R k uLo w huw r hr δMid u _ le_rfl fun i hi e ↦ hU ⟨⟨i, hi⟩, e⟩]
  · rw [ite_eq_right hV, ite_eq_right hV, Matrix.mulVec_zero, Matrix.mulVec_zero]

/-- Single `0-T` reverse tree round `r < k`: `wUncompCnotRound` followed by `wUncompMeasPrefix`. -/
def wUncompRoundDyn {Var : Type} {n : ℕ} (v : Var) (R k : ℕ) (uLo : Fin k → Wire n)
    (w : Fin R → Fin (2 ^ k) → Wire n) (hw : WInj w) (huw : ∀ d b p, uLo d ≠ w b p) (r : ℕ)
    (hr : r < k) (rest : DynamicCircuit Var n) : DynamicCircuit Var n :=
  .seq (.circuit (wUncompCnotRound R k w hw r hr))
    (wUncompMeasPrefix v R k uLo w huw r hr rest (R * 2 ^ r) le_rfl)

/--
Full `0-T` reverse CH-tree uncomputation across levels `m - 1, ..., 0` , continuing with `rest` .
-/
def wUncompTreeDyn {Var : Type} {n : ℕ} (v : Var) (R k : ℕ) (uLo : Fin k → Wire n)
    (w : Fin R → Fin (2 ^ k) → Wire n) (hw : WInj w) (huw : ∀ d b p, uLo d ≠ w b p)
    (rest : DynamicCircuit Var n) : (m : ℕ) → m ≤ k → DynamicCircuit Var n
  | 0, _ => rest
  | r + 1, hr =>
      wUncompRoundDyn v R k uLo w hw huw r hr
        (wUncompTreeDyn v R k uLo w hw huw rest r (Nat.le_of_succ_le hr))

private theorem count_wUncompTreeDyn {Var : Type} {n : ℕ} (v : Var) (R k : ℕ) (uLo : Fin k → Wire n)
    (w : Fin R → Fin (2 ^ k) → Wire n) (hw : WInj w) (huw : ∀ d b p, uLo d ≠ w b p)
        (rest : DynamicCircuit Var n) :
    ∀ (m : ℕ) (hm : m ≤ k),
      (wUncompTreeDyn v R k uLo w hw huw rest m hm).count .T = rest.count .T ∧
      (wUncompTreeDyn v R k uLo w hw huw rest m hm).count .TOFF = rest.count .TOFF
  | 0, _ => ⟨rfl, rfl⟩
  | r + 1, hr => by
      obtain ⟨ht, hf⟩ := count_wUncompTreeDyn v R k uLo w hw huw rest r (Nat.le_of_succ_le hr)
      obtain ⟨mt, mf⟩ :=
          count_wUncompMeasPrefix v R k uLo w huw r hr (wUncompTreeDyn v R k uLo w hw huw rest r
          (Nat.le_of_succ_le hr)) (R * 2 ^ r) le_rfl
      simp [wUncompTreeDyn, wUncompRoundDyn, DynamicCircuit.count, mt, mf, ht, hf,
        show (wUncompCnotRound R k w hw r hr).count .T =
            0 from (count_seqNat_T 0 (R * 2 ^ r) _ fun _ _ ↦
            by simp [Circuit.CNOT]).trans (Nat.mul_zero _),
        show (wUncompCnotRound R k w hw r hr).count .TOFF = 0 from count_seqNat_TOFF_zero (R *
            2 ^ r) _ fun _ _ ↦ by simp [Circuit.CNOT]]

private theorem dw_wUncompTreeDyn {Var : Type} {n : ℕ} {S : Wire n → Prop} (v : Var) (R k : ℕ)
    (uLo : Fin k → Wire n)
    (w : Fin R → Fin (2 ^ k) → Wire n) (hw : WInj w) (huw : ∀ d b p, uLo d ≠ w b p)
        (huS : ∀ d, S (uLo d)) (hwS : ∀ b p, S (w b p))
    {rest : DynamicCircuit Var n} (hRest : DynWires S rest) : ∀ (m : ℕ)
        (hm : m ≤ k), DynWires S (wUncompTreeDyn v R k uLo w hw huw rest m hm)
  | 0, _ => hRest
  | r + 1, hr => ⟨cw_seqNat (R * 2 ^ r) _ fun _ _ ↦ cw_cnot (hwS _ _) (hwS _ _),
      dw_wUncompMeasPrefix v R k uLo w huw huS hwS r hr (dw_wUncompTreeDyn v R k uLo w hw huw huS
          hwS hRest r (Nat.le_of_succ_le hr)) (R * 2 ^ r) le_rfl⟩

private theorem subspaceStep_wUncompTreeDyn {Var : Type} [Fintype Var] [DecidableEq Var] {n R k : ℕ}
    (v : Var)
    (P : BitAssignment n → Prop) [DecidablePred P] (bStarFn : BitAssignment n → Fin R)
        (uLo : Fin k → Wire n)
    (w : Fin R → Fin (2 ^ k) → Wire n) (hw : WInj w) (huw : ∀ d b p, uLo d ≠ w b p)
    {rest : DynamicCircuit Var n} {R_out : Operator (2 ^ n)}
    (hRest : SubspaceStep (oneHotPreOp P bStarFn uLo w 0 (Nat.zero_le k)) R_out rest) :
    ∀ (m : ℕ)
        (hm : m ≤ k),
        SubspaceStep (oneHotPreOp P bStarFn uLo w m hm) R_out (wUncompTreeDyn v R k uLo w hw huw
        rest m hm)
  | 0, _ => hRest
  | r + 1, hr =>
      (subspaceStep_congr_out (subspaceStep_of_circuit (Var := Var)
          (oneHotPreOp P bStarFn uLo w (r + 1) hr) (wUncompCnotRound R k w hw r hr))
        (wUncompCnotRound_mul_oneHotPreOp P bStarFn uLo w hw huw r hr)).seq
        (subspaceStep_wUncompMeasPrefix v P bStarFn uLo w hw huw r hr
          (subspaceStep_wUncompTreeDyn v P bStarFn uLo w hw huw hRest r (Nat.le_of_succ_le hr))
              (R * 2 ^ r) le_rfl)
/-
Section 3: Generic `R` -block root specification, `wComputeCore` , `wUncomputeCore` , and
`WRouterBracket`
-/

/-- Root-initialization specification for an `R`-block W-state router (`N = R * 2^k`). -/
structure WRootSpec (R k D N n : ℕ) (hRN : R * 2 ^ k = N) (hk : k ≤ D)
    (wIdx : Fin D → Wire n) (wOut : Fin N → Wire n) : Type where
  bStarFn : BitAssignment n → Fin R
  cRootInit : Circuit n
  cRootUninit : Circuit n
  count_init : cRootInit.count .T = 0 ∧ cRootInit.count .TOFF = 0
  count_uninit : cRootUninit.count .T = 0 ∧ cRootUninit.count .TOFF = 0
  cw_init : ∀ {S : Wire n → Prop}, (∀ d, S (wIdx d)) → (∀ j, S (wOut j)) → CircWires S cRootInit
  cw_uninit : ∀ {S : Wire n → Prop}, (∀ d, S (wIdx d)) → (∀ j, S (wOut j)) → CircWires S cRootUninit
  idx_decomp : ∀ δ : BitAssignment n, idxValD wIdx δ < N →
    (bStarFn δ).val * 2 ^ k + idxValPrefix (uLoOf hk wIdx) δ k le_rfl = idxValD wIdx δ
  init_ket : ∀ δ : BitAssignment n, (∀ j, δ (wOut j) = 0) → idxValD wIdx δ < N →
    cRootInit.eval.1.mulVec (ket δ) =
      ket (Function.update δ (blockWires hRN wOut (bStarFn δ) ⟨0, Nat.two_pow_pos k⟩) 1)
  uninit_init : ∀ v : Fin (2 ^ n) → ℂ, cRootUninit.eval.1.mulVec (cRootInit.eval.1.mulVec v) = v

/-- Core `2*R*(2^k - 1)`-`T` forward W-state one-hot loader under `WRouterDisjProp`. -/
def wComputeCore {Var : Type} {R k D N n : ℕ} (hR : 0 < R) (hRN : R * 2 ^ k = N) (hk : k ≤ D)
    (v : Var) (wHas : Wire n) (wIdx : Fin D → Wire n) (wOut : Fin N → Wire n) (qEnc : Wire n)
    (hd : WRouterDisjProp wHas wIdx wOut qEnc) (root : WRootSpec R k D N n hRN hk wIdx wOut) :
    DynamicCircuit Var n :=
  let w := blockWires hRN wOut; let hw : WInj w := wInj_blockWires hRN hd.2.2.2.2.1;
  let uLo := uLoOf hk wIdx
  let hwq : ∀ b p, w b p ≠ qEnc := fun _ _ ↦ hd.2.2.2.2.2 _
  let huq : ∀ d, uLo d ≠ qEnc := fun _ ↦ hd.2.2.2.1 _
  let t0 := w ⟨0, hR⟩ ⟨0, Nat.two_pow_pos k⟩
  .seq (.circuit (root.cRootInit ;;ᶜ wTreePrefix R k w hw k le_rfl))
    (.seq (wShiftLevels v R k uLo w qEnc hw hwq huq k le_rfl)
      (.circuit (wZeroGate wHas t0 (hd.1 _))))

private theorem count_wComputeCore {Var : Type} {R k D N n : ℕ} (hR : 0 < R) (hRN : R * 2 ^ k = N)
    (hk : k ≤ D) (v : Var) (wHas : Wire n) (wIdx : Fin D → Wire n) (wOut : Fin N → Wire n)
    (qEnc : Wire n) (hd : WRouterDisjProp wHas wIdx wOut qEnc)
    (root : WRootSpec R k D N n hRN hk wIdx wOut) :
    (wComputeCore hR hRN hk v wHas wIdx wOut qEnc hd root).count .T = 2 * R * (2 ^ k - 1) ∧
    (wComputeCore hR hRN hk v wHas wIdx wOut qEnc hd root).count .TOFF = 0 := by
  simp [wComputeCore, wZeroGate, DynamicCircuit.count, Circuit.count_seq, Circuit.X,
    Circuit.CNOT, root.count_init, count_wTreePrefix, count_wShiftLevels]

private theorem dw_wComputeCore {Var : Type} {R k D N n : ℕ} {S : Wire n → Prop} (hR : 0 < R)
    (hRN : R * 2 ^ k = N) (hk : k ≤ D) (v : Var) (wHas : Wire n) (wIdx : Fin D → Wire n)
    (wOut : Fin N → Wire n) (qEnc : Wire n) (hd : WRouterDisjProp wHas wIdx wOut qEnc)
    (root : WRootSpec R k D N n hRN hk wIdx wOut) (hHas : S wHas) (hIdx : ∀ d, S (wIdx d))
    (hOut : ∀ j, S (wOut j))
    (hQ : S qEnc) : DynWires S (wComputeCore hR hRN hk v wHas wIdx wOut qEnc hd root) :=
    ⟨⟨root.cw_init hIdx hOut, cw_wTreePrefix R k _ _ (fun _ _ ↦ hOut _) k le_rfl⟩,
    dw_wShiftLevels v R k _ _ qEnc _ _ _ (fun _ ↦ hIdx _) (fun _ _ ↦ hOut _) hQ k le_rfl,
    ⟨cw_1 (hOut _), cw_cnot hHas (hOut _)⟩⟩
private theorem subspaceStep_wComputeCore {Var : Type} [Fintype Var] [DecidableEq Var]
    {R k D N n : ℕ}
    (hR : 0 < R) (hRN : R * 2 ^ k = N) (hk : k ≤ D) (v : Var) (wHas : Wire n)
        (wIdx : Fin D → Wire n)
    (wOut : Fin N → Wire n) (qEnc : Wire n) (hd : WRouterDisj wHas wIdx wOut qEnc)
    (root : WRootSpec R k D N n hRN hk wIdx wOut) (G : Operator (2 ^ n))
        (hSupp : SupportedOn (ValidWRouterIn wHas wIdx wOut qEnc) G) :
    SubspaceStep (Var := Var) G ((uOneHotToggle wHas wIdx wOut hd.has_ne_out hd.idx_ne_out).1 * G)
      (wComputeCore hR hRN hk v wHas wIdx wOut qEnc hd.disjProp root) := by
  let w := blockWires hRN wOut
  let hw : WInj w := wInj_blockWires hRN hd.out_inj
  let uLo := uLoOf hk wIdx
  have hStage1Eq : (root.cRootInit ;;ᶜ wTreePrefix R k w hw k le_rfl).eval.1 * G =
      wSuperOp root.bStarFn uLo w qEnc 0 (Nat.zero_le k) * G :=
    hSupp _ _ fun δ ⟨hOut0, hq0, hLt, _⟩ ↦ by
      rw [ket_sr_eq, eval_seq_mulVec, root.init_ket δ hOut0 hLt,
          wSuperVec_bot root.bStarFn uLo w hw qEnc δ (fun _ _ ↦ hOut0 _) hq0, wSuperOp,
          mkVecOp_mulVec_ket]
  have hStage3Eq : (wZeroGate wHas (w ⟨0, hR⟩ ⟨0, Nat.two_pow_pos k⟩) (hd.has_ne_out _)).eval.1 *
      (wSuperOp root.bStarFn uLo w qEnc k le_rfl * G) =
          (uOneHotToggle wHas wIdx wOut hd.has_ne_out hd.idx_ne_out).1 * G := by
    rw [← Matrix.mul_assoc]
    refine hSupp _ _ fun δ ⟨hOut0, hq0, hLt, hZero⟩ ↦ ?_
    rw [ket_sr_eq, ← Matrix.mulVec_mulVec, wSuperOp, mkVecOp_mulVec_ket,
        wSuperVec_top root.bStarFn uLo w qEnc δ (fun _ _ ↦ hOut0 _) hq0,
      uOneHotToggle_mulVec_ket, show w (root.bStarFn δ)
          ⟨idxValPrefix uLo δ k le_rfl, idxValPrefix_lt_two_pow uLo δ k le_rfl⟩ =
        wOut ⟨idxValD wIdx δ, hLt⟩ from congrArg wOut (Fin.ext (root.idx_decomp δ hLt))]
    refine (wZeroGate_mulVec_ket (hd.has_ne_out _) (hd.has_ne_out _)
      (fun h0 ↦ congrArg wOut (fin_mk_eq ((hZero h0).trans (Nat.zero_mul (2 ^ k)).symm)))).trans ?_
    dsimp only [toggleOneHotBits]
    rw [dite_eq_left hLt, hOut0 _, zero_add]
  exact (subspaceStep_congr_out (subspaceStep_of_circuit G _) hStage1Eq).seq
    ((subspaceStep_mul_right G (subspaceStep_wShiftLevels v root.bStarFn uLo w qEnc hw
      (fun _ _ ↦ hd.out_ne_q _) (fun _ ↦ hd.idx_ne_q _)
          (fun _ _ _ ↦ hd.idx_ne_out _ _) k le_rfl)).seq
      (subspaceStep_congr_out (subspaceStep_of_circuit _ _) hStage3Eq))
/-- Core `0-T` MBU uncomputer for an `R`-block W-state router under `WRouterOutDisj`. -/
def wUncomputeCore {Var : Type} {R k D N n : ℕ} (hR : 0 < R) (hRN : R * 2 ^ k = N) (hk : k ≤ D)
    (v : Var) (wHas : Wire n) (wIdx : Fin D → Wire n) (wOut : Fin N → Wire n)
    (ho : WRouterOutDisj wHas wIdx wOut) (root : WRootSpec R k D N n hRN hk wIdx wOut) :
    DynamicCircuit Var n :=
  let w := blockWires hRN wOut; let hw : WInj w := wInj_blockWires hRN ho.2.2;
  let uLo := uLoOf hk wIdx
  let huw : ∀ d b p, uLo d ≠ w b p := fun _ _ _ ↦ ho.2.1 _ _
  let t0 := w ⟨0, hR⟩ ⟨0, Nat.two_pow_pos k⟩
  .seq (.circuit (wUnzeroGate wHas t0 (ho.1 _)))
    (wUncompTreeDyn v R k uLo w hw huw (.circuit root.cRootUninit) k le_rfl)

private theorem count_wUncomputeCore {Var : Type} {R k D N n : ℕ} (hR : 0 < R) (hRN : R * 2 ^ k = N)
    (hk : k ≤ D) (v : Var) (wHas : Wire n) (wIdx : Fin D → Wire n) (wOut : Fin N → Wire n)
    (ho : WRouterOutDisj wHas wIdx wOut) (root : WRootSpec R k D N n hRN hk wIdx wOut) :
    (wUncomputeCore hR hRN hk v wHas wIdx wOut ho root).count .T = 0 ∧
    (wUncomputeCore hR hRN hk v wHas wIdx wOut ho root).count .TOFF = 0 := by
  simp [wUncomputeCore, wUnzeroGate, DynamicCircuit.count, Circuit.count_seq, Circuit.X,
    Circuit.CNOT, root.count_uninit, count_wUncompTreeDyn]

private theorem dw_wUncomputeCore {Var : Type} {R k D N n : ℕ} {S : Wire n → Prop} (hR : 0 < R)
    (hRN : R * 2 ^ k = N) (hk : k ≤ D) (v : Var) (wHas : Wire n) (wIdx : Fin D → Wire n)
    (wOut : Fin N → Wire n) (ho : WRouterOutDisj wHas wIdx wOut)
    (root : WRootSpec R k D N n hRN hk wIdx wOut) (hHas : S wHas) (hIdx : ∀ d, S (wIdx d))
    (hOut : ∀ j, S (wOut j)) : DynWires S (wUncomputeCore hR hRN hk v wHas wIdx wOut ho root) :=
  ⟨⟨cw_cnot hHas (hOut _), cw_1 (hOut _)⟩, dw_wUncompTreeDyn (rest :=
      .circuit root.cRootUninit) v R k _ _ _ _ (fun _ ↦ hIdx _) (fun _ _ ↦ hOut _)
      (root.cw_uninit hIdx hOut) k le_rfl⟩

private theorem subspaceStep_wUncomputeCore {Var : Type} [Fintype Var] [DecidableEq Var]
    {R k D N n : ℕ}
    (hR : 0 < R) (hRN : R * 2 ^ k = N) (hk : k ≤ D) (v : Var) (wHas : Wire n)
        (wIdx : Fin D → Wire n)
    (wOut : Fin N → Wire n) (ho : WRouterOutDisj wHas wIdx wOut)
        (root : WRootSpec R k D N n hRN hk wIdx wOut)
    (G : Operator (2 ^ n)) (hSupp : SupportedOn (ValidWRouterClean wHas wIdx wOut) G) :
    SubspaceStep (Var := Var) ((uOneHotToggle wHas wIdx wOut ho.1 ho.2.1).1 *
        G) G (wUncomputeCore hR hRN hk v wHas wIdx wOut ho root) := by
  classical
  let w := blockWires hRN wOut
  let hw : WInj w := wInj_blockWires hRN ho.2.2
  let uLo := uLoOf hk wIdx
  let P := ValidWRouterClean wHas wIdx wOut
  let idOnP : Operator (2 ^ n) := mkVecOp fun δ ↦ if P δ ∧ ∀ b p, δ (w b p) = 0 then ket δ else 0
  have hStage1Eq : (wUnzeroGate wHas (w ⟨0, hR⟩ ⟨0, Nat.two_pow_pos k⟩) (ho.1 _)).eval.1 *
      ((uOneHotToggle wHas wIdx wOut ho.1 ho.2.1).1 * G) =
          oneHotPreOp P root.bStarFn uLo w k le_rfl * G := by
    rw [← Matrix.mul_assoc]
    refine hSupp _ _ fun δ ⟨hOut0, hLt, hZero⟩ ↦ ?_
    rw [ket_sr_eq, ← Matrix.mulVec_mulVec, uOneHotToggle_mulVec_ket, oneHotPreOp_mulVec_ket]
    dsimp only [oneHotPreVec, toggleOneHotBits]
    rw [ite_eq_left ⟨⟨hOut0, hLt, hZero⟩, fun _ _ ↦ hOut0 _⟩, dite_eq_left hLt, hOut0 _, zero_add,
      show w (root.bStarFn δ)
          ⟨idxValPrefix uLo δ k le_rfl, Nat.lt_of_lt_of_le (idxValPrefix_lt_two_pow uLo δ k le_rfl)
          (Nat.pow_le_pow_right (by omega) le_rfl)⟩ =
        wOut ⟨idxValD wIdx δ, hLt⟩ from congrArg wOut (Fin.ext (root.idx_decomp δ hLt))]
    exact wUnzeroGate_mulVec_ket (ho.1 _) (ho.1 _) fun h0 ↦
        congrArg wOut (fin_mk_eq ((hZero h0).trans (Nat.zero_mul (2 ^ k)).symm))
  have hBaseEq : root.cRootUninit.eval.1 * oneHotPreOp P root.bStarFn uLo w 0 (Nat.zero_le k) =
      idOnP :=
    matrix_ext_ket fun δ ↦ by
      simp only [← Matrix.mulVec_mulVec, oneHotPreOp_mulVec_ket, idOnP, mkVecOp_mulVec_ket,
          oneHotPreVec]
      split_ifs with hV
      · erw [← root.init_ket δ hV.1.1 hV.1.2.1]
        exact root.uninit_init _
      · exact Matrix.mulVec_zero _
  have hIdG : idOnP * G = G := (hSupp idOnP 1 fun δ hP ↦ by
    simpa only [ket_sr_eq, idOnP, mkVecOp_mulVec_ket, Matrix.one_mulVec] using
      ite_eq_left ⟨hP, fun _ _ ↦ hP.1 _⟩).trans (Matrix.one_mul G)
  exact (subspaceStep_congr_out (subspaceStep_of_circuit _ _) hStage1Eq).seq
    (subspaceStep_congr_out (subspaceStep_mul_right G (subspaceStep_wUncompTreeDyn v P root.bStarFn
        uLo w hw (fun _ _ _ ↦ ho.2.1 _ _)
      (subspaceStep_congr_out (subspaceStep_of_circuit _ root.cRootUninit) hBaseEq) k le_rfl)) hIdG)
/-- Decoupled zero-gated W-state one-hot bracket (`tCost` `T` compute, `0-T` MBU uncompute). -/
structure WRouterBracket (D N tCost : ℕ) : Type 1 where
  pComp : ∀ {Var : Type} {n : ℕ},
    Var → Wire n → (Fin D → Wire n) → (Fin N → Wire n) → Wire n → DynamicCircuit Var n
  pUncomp : ∀ {Var : Type} {n : ℕ},
    Var → Wire n → (Fin D → Wire n) → (Fin N → Wire n) → DynamicCircuit Var n
  count_comp : ∀ {Var : Type} {n : ℕ} (v : Var) (wHas : Wire n) (wIdx : Fin D → Wire n)
    (wOut : Fin N → Wire n) (qEnc : Wire n),
    (pComp v wHas wIdx wOut qEnc).count .T = tCost ∧
    (pComp v wHas wIdx wOut qEnc).count .TOFF = 0
  count_uncomp : ∀ {Var : Type} {n : ℕ} (v : Var) (wHas : Wire n) (wIdx : Fin D → Wire n)
    (wOut : Fin N → Wire n),
    (pUncomp v wHas wIdx wOut).count .T = 0 ∧
    (pUncomp v wHas wIdx wOut).count .TOFF = 0
  dynWires_comp : ∀ {Var : Type} {n : ℕ} {S : Wire n → Prop} (v : Var) (wHas : Wire n)
    (wIdx : Fin D → Wire n) (wOut : Fin N → Wire n) (qEnc : Wire n),
    S wHas → (∀ d, S (wIdx d)) → (∀ j, S (wOut j)) → S qEnc →
    DynWires S (pComp v wHas wIdx wOut qEnc)
  dynWires_uncomp : ∀ {Var : Type} {n : ℕ} {S : Wire n → Prop} (v : Var) (wHas : Wire n)
    (wIdx : Fin D → Wire n) (wOut : Fin N → Wire n),
    S wHas → (∀ d, S (wIdx d)) → (∀ j, S (wOut j)) →
    DynWires S (pUncomp v wHas wIdx wOut)
  step_comp : ∀ {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    (v : Var) (wHas : Wire n) (wIdx : Fin D → Wire n) (wOut : Fin N → Wire n) (qEnc : Wire n)
    (hd : WRouterDisj wHas wIdx wOut qEnc) (R : Operator (2 ^ n)),
    SupportedOn (ValidWRouterIn wHas wIdx wOut qEnc) R →
    SubspaceStep (Var := Var) R ((uOneHotToggle wHas wIdx wOut hd.has_ne_out hd.idx_ne_out).1 * R)
      (pComp v wHas wIdx wOut qEnc)
  step_uncomp : ∀ {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    (v : Var) (wHas : Wire n) (wIdx : Fin D → Wire n) (wOut : Fin N → Wire n) {qEnc : Wire n}
    (hd : WRouterDisj wHas wIdx wOut qEnc) (R : Operator (2 ^ n)),
    SupportedOn (ValidWRouterClean wHas wIdx wOut) R →
    SubspaceStep (Var := Var) ((uOneHotToggle wHas wIdx wOut hd.has_ne_out hd.idx_ne_out).1 * R) R
      (pUncomp v wHas wIdx wOut)

/-- Bracketed dynamic subroutine `pComp ;; mid ;; pUncomp`. -/
def WRouterBracket.wrap {D N tCost : ℕ} (B : WRouterBracket D N tCost) {Var : Type} {n : ℕ}
    (v : Var) (wHas : Wire n) (wIdx : Fin D → Wire n) (wOut : Fin N → Wire n) (qEnc : Wire n)
    (mid : DynamicCircuit Var n) : DynamicCircuit Var n :=
    .seq (B.pComp v wHas wIdx wOut qEnc) (.seq mid (B.pUncomp v wHas wIdx wOut))
theorem WRouterBracket.count_wrap {D N tCost : ℕ} (B : WRouterBracket D N tCost) {Var : Type}
    {n : ℕ} (v : Var) (wHas : Wire n) (wIdx : Fin D → Wire n) (wOut : Fin N → Wire n)
    (qEnc : Wire n) (mid : DynamicCircuit Var n) : (B.wrap v wHas wIdx wOut qEnc mid).count .T =
    tCost + mid.count .T ∧ (B.wrap v wHas wIdx wOut qEnc mid).count .TOFF = mid.count .TOFF :=
    by
  simp [WRouterBracket.wrap, DynamicCircuit.count, B.count_comp, B.count_uncomp]
theorem WRouterBracket.dynWires_wrap {D N tCost : ℕ} (B : WRouterBracket D N tCost) {Var : Type}
    {n : ℕ} {S : Wire n → Prop} (v : Var) (wHas : Wire n) (wIdx : Fin D → Wire n)
    (wOut : Fin N → Wire n) (qEnc : Wire n) (mid : DynamicCircuit Var n) (hHas : S wHas)
    (hIdx : ∀ d, S (wIdx d)) (hOut : ∀ j, S (wOut j)) (hQ : S qEnc) (hMid : DynWires S mid) :
    DynWires S (B.wrap v wHas wIdx wOut qEnc mid) :=
    ⟨B.dynWires_comp v wHas wIdx wOut qEnc hHas hIdx hOut hQ, hMid,
    B.dynWires_uncomp v wHas wIdx wOut hHas hIdx hOut⟩
theorem WRouterBracket.subspaceStep_wrap {D N tCost : ℕ} (B : WRouterBracket D N tCost)
    {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    (v : Var) (wHas : Wire n) (wIdx : Fin D → Wire n) (wOut : Fin N → Wire n) (qEnc : Wire n)
    (hd : WRouterDisj wHas wIdx wOut qEnc) (mid : DynamicCircuit Var n)
    (R_in R_out : Operator (2 ^ n))
    (hIn : SupportedOn (ValidWRouterIn wHas wIdx wOut qEnc) R_in)
    (hOut : SupportedOn (ValidWRouterClean wHas wIdx wOut) R_out)
    (hMid : SubspaceStep (Var := Var)
      ((uOneHotToggle wHas wIdx wOut hd.has_ne_out hd.idx_ne_out).1 * R_in)
      ((uOneHotToggle wHas wIdx wOut hd.has_ne_out hd.idx_ne_out).1 * R_out)
      mid) :
    SubspaceStep (Var := Var) R_in R_out (B.wrap v wHas wIdx wOut qEnc mid) :=
  (B.step_comp v wHas wIdx wOut qEnc hd R_in hIn).seq (hMid.seq (B.step_uncomp v wHas wIdx wOut hd
      R_out hOut))

/-
Section 4: `Pow2` (`R = 2`, `N = 2^(k+1)` , `4*(2^k - 1)` `T` ) and `3x2k` (`R = 3`, `N = 3*2^k` ,
`6*(2^k - 1)` `T` )
-/

theorem two_mul_pow_eq (k : ℕ) : 2 * 2 ^ k = 2 ^ (k + 1) := by ring

/-- Block selector for `Pow2` (`R = 2`) from MSB `u0`. -/
def bStarPow2 {n : ℕ} (u0 : Wire n) (δ : BitAssignment n) : Fin 2 :=
  if δ u0 = 1 then ⟨1, by omega⟩ else ⟨0, by omega⟩

/-- Root initialization/uninitialization bundle for `Pow2` (`N = 2^(k+1)`). -/
def wRootSpecPow2 {k n : ℕ} (wIdx : Fin (k + 1) → Wire n) (wOut : Fin (2 ^ (k + 1)) → Wire n)
    (hIdxOut : ∀ d j, wIdx d ≠ wOut j) : WRootSpec 2 k (k + 1) (2 ^ (k + 1)) n (two_mul_pow_eq k)
    (Nat.le_succ k) wIdx wOut :=
  let u0 := wIdx ⟨k, Nat.lt_succ_self k⟩; let w := blockWires (two_mul_pow_eq k) wOut;
  let p00 : Fin (2 ^ k) := ⟨0, Nat.two_pow_pos k⟩
  let w00 := w ⟨0, by omega⟩ p00
  let w10 := w ⟨1, by omega⟩ p00
  let hu00 : u0 ≠ w00 := hIdxOut ⟨k, Nat.lt_succ_self k⟩ _;
  let hu10 : u0 ≠ w10 := hIdxOut ⟨k, Nat.lt_succ_self k⟩ _
  { bStarFn := bStarPow2 u0
    cRootInit := Circuit.X w00 ;;ᶜ Circuit.CNOT u0 w00 hu00 ;;ᶜ Circuit.CNOT u0 w10 hu10
    cRootUninit := Circuit.CNOT u0 w10 hu10 ;;ᶜ Circuit.CNOT u0 w00 hu00 ;;ᶜ Circuit.X w00
    count_init := ⟨by simp [Circuit.count_seq, Circuit.X, Circuit.CNOT],
      by simp [Circuit.count_seq, Circuit.X, Circuit.CNOT]⟩
    count_uninit := ⟨by simp [Circuit.count_seq, Circuit.X, Circuit.CNOT],
      by simp [Circuit.count_seq, Circuit.X, Circuit.CNOT]⟩
    cw_init := fun hI hO ↦ ⟨cw_1 (hO _), cw_cnot (hI _) (hO _), cw_cnot (hI _) (hO _)⟩
    cw_uninit := fun hI hO ↦ ⟨cw_cnot (hI _) (hO _), cw_cnot (hI _) (hO _), cw_1 (hO _)⟩
    idx_decomp := fun δ _ ↦ by
      rw [idxValPrefix_uLoOf (Nat.le_succ k) wIdx δ k le_rfl];
      dsimp only [idxValD, idxValPrefix, bStarPow2, u0]
      split_ifs <;> dsimp <;> omega
    init_ket := fun δ hOut0 _ ↦ by
      have hw00 : δ w00 = 0 := hOut0 _; have hw10 : δ w10 = 0 := hOut0 _
      rcases DynCircExt.bit_cases (δ u0) with hu0 | hu1
      · have hb : bStarPow2 u0 δ = ⟨0, by omega⟩ := by
          dsimp [bStarPow2]; rw [ite_eq_right (by rw [hu0]; decide)]
        have hc0 : Function.update δ w00 1 u0 = 0 :=
            (Function.update_of_ne hu00 1 δ).trans hu0; rw [hb, eval_seq_mulVec, eval_seq_mulVec,
            ket_X, hw00, zero_add, ket_CNOT_of_ctrl_zero hu00 hc0, ket_CNOT_of_ctrl_zero hu10 hc0]
      · have hb : bStarPow2 u0 δ = ⟨1, by omega⟩ := by
          dsimp [bStarPow2]; rw [ite_eq_left hu1]
        have hw00_0 : Function.update δ w00 0 = δ :=
            hw00 ▸ Function.update_eq_self w00 δ; rw [hb, eval_seq_mulVec, eval_seq_mulVec, ket_X,
            hw00, zero_add, ket_CNOT, Function.update_of_ne hu00, hu1, Function.update_self,
            CharTwo.add_self_eq_zero, Function.update_idem, hw00_0, ket_CNOT, hw10, hu1, zero_add]
    uninit_init := fun v ↦ by
      simp only [eval_seq_mulVec, mulVec_CNOT_invol, mulVec_X_invol] }

/-- Forward `4*(2^k - 1)`-`T` zero-gated W-state one-hot loader for `N = 2^(k+1)`. -/
def wStateComputePow2 {Var : Type} {n : ℕ} (k : ℕ) (v : Var) (wHas : Wire n)
    (wIdx : Fin (k + 1) → Wire n) (wOut : Fin (2 ^ (k + 1)) → Wire n)
    (qEnc : Wire n) : DynamicCircuit Var n :=
  if h : WRouterDisjProp wHas wIdx wOut qEnc then wComputeCore (by omega) (two_mul_pow_eq k)
      (Nat.le_succ k) v wHas wIdx wOut qEnc h (wRootSpecPow2 wIdx wOut h.2.2.1)
  else .circuit (seqNat (4 * (2 ^ k - 1)) fun _ _ ↦ Circuit.T wHas)

/-- Reverse `0-T` MBU uncomputer for `N = 2^(k+1)` zero-gated W-state one-hot loader. -/
def wStateUncomputePow2 {Var : Type} {n : ℕ} (k : ℕ) (v : Var) (wHas : Wire n)
    (wIdx : Fin (k + 1) → Wire n) (wOut : Fin (2 ^ (k + 1)) → Wire n) : DynamicCircuit Var n :=
  if h : WRouterOutDisj wHas wIdx wOut then wUncomputeCore (by omega) (two_mul_pow_eq k)
      (Nat.le_succ k) v wHas wIdx wOut h (wRootSpecPow2 wIdx wOut h.2.1)
  else .circuit .identity

/-- Decoupled `Pow2` W-state one-hot bracket (`N = 2^(k+1)`, `D = k+1`, `4*(2^k - 1)` `T`). -/
def wRouterBracketPow2 (k : ℕ) : WRouterBracket (k + 1) (2 ^ (k + 1)) (4 * (2 ^ k - 1)) where
  pComp := wStateComputePow2 k
  pUncomp := wStateUncomputePow2 k
  count_comp v wHas wIdx wOut qEnc := by
    dsimp only [wStateComputePow2]
    split_ifs with h
    · exact count_wComputeCore (by omega) (two_mul_pow_eq k)
          (Nat.le_succ k) v wHas wIdx wOut qEnc h _
    · exact ⟨by simpa [DynamicCircuit.count] using count_seqNat_T 1 (4 * (2 ^ k - 1)) _ fun _ _ ↦
                  by simp [Circuit.T],
        count_seqNat_TOFF_zero (4 * (2 ^ k - 1)) _ fun _ _ ↦ by simp [Circuit.T]⟩
  count_uncomp v wHas wIdx wOut := by
    dsimp only [wStateUncomputePow2]
    split_ifs with h
    · exact count_wUncomputeCore (by omega) (two_mul_pow_eq k) (Nat.le_succ k) v wHas wIdx wOut h _
    · exact ⟨rfl, rfl⟩
  dynWires_comp v wHas wIdx wOut qEnc hHas hIdx hOut hQ := by
    dsimp only [wStateComputePow2]
    split_ifs with h
    · exact dw_wComputeCore (by omega) (two_mul_pow_eq k)
          (Nat.le_succ k) v wHas wIdx wOut qEnc h _ hHas hIdx hOut hQ
    · exact cw_seqNat _ _ fun _ _ ↦ cw_1 hHas
  dynWires_uncomp v wHas wIdx wOut hHas hIdx hOut := by
    dsimp only [wStateUncomputePow2]
    split_ifs with h
    · exact dw_wUncomputeCore (by omega) (two_mul_pow_eq k)
          (Nat.le_succ k) v wHas wIdx wOut h _ hHas hIdx hOut
    · trivial
  step_comp v wHas wIdx wOut qEnc hd R hSupp := by
    dsimp only [wStateComputePow2]
    rw [dite_eq_left hd.disjProp]
    exact subspaceStep_wComputeCore (by omega) (two_mul_pow_eq k)
        (Nat.le_succ k) v wHas wIdx wOut qEnc hd _ R hSupp
  step_uncomp := fun {Var} [Fintype Var] [DecidableEq Var] {n} v wHas wIdx wOut {_qEnc} hd R hSupp ↦
      by
    dsimp only [wStateUncomputePow2]
    rw [dite_eq_left hd.outDisj]
    exact subspaceStep_wUncomputeCore (by omega) (two_mul_pow_eq k)
        (Nat.le_succ k) v wHas wIdx wOut hd.outDisj _ R hSupp
/-- Block selector for `3x2k` (`R = 3`) from upper bits `(u0, u1)`. -/
def bStar3x2k {n : ℕ} (u0 u1 : Wire n) (δ : BitAssignment n) : Fin 3 :=
  if δ u1 = 1 then ⟨2, by omega⟩ else if δ u0 = 1 then ⟨1, by omega⟩ else ⟨0, by omega⟩

theorem not_both_one_of_lt_3x2k {k n : ℕ} (wIdx : Fin (k + 2) → Wire n) (δ : BitAssignment n)
    (hLt : idxValD wIdx δ < 3 * 2 ^ k) :
    ¬ (δ (wIdx ⟨k, Nat.le_of_succ_le (Nat.lt_succ_self (k + 1))⟩) = 1 ∧
    δ (wIdx ⟨k + 1, Nat.lt_succ_self (k + 1)⟩) = 1) := by
  rintro ⟨hu0, hu1⟩
  rw [idxValD, idxValPrefix, idxValPrefix, ite_eq_left hu0, ite_eq_left hu1, Nat.pow_succ] at hLt
  omega
/-- Root initialization/uninitialization bundle for `3x2k` (`N = 3 * 2^k`). -/
def wRootSpec3x2k {k n : ℕ} (wIdx : Fin (k + 2) → Wire n) (wOut : Fin (3 * 2 ^ k) → Wire n)
    (hIdxOut : ∀ d j, wIdx d ≠ wOut j) : WRootSpec 3 k (k + 2)
    (3 * 2 ^ k) n rfl (Nat.le_add_right k 2) wIdx wOut :=
  let hk0 : k < k + 2 := Nat.le_of_succ_le (Nat.lt_succ_self (k + 1));
  let hk1 : k + 1 < k + 2 := Nat.lt_succ_self (k + 1); let u0 := wIdx ⟨k, hk0⟩;
  let u1 := wIdx ⟨k + 1, hk1⟩; let w := blockWires (rfl : 3 * 2 ^ k = 3 * 2 ^ k) wOut;
  let p00 : Fin (2 ^ k) := ⟨0, Nat.two_pow_pos k⟩
  let w00 := w ⟨0, by omega⟩ p00
  let w10 := w ⟨1, by omega⟩ p00
  let w20 := w ⟨2, by omega⟩ p00
  let hu0_00 : u0 ≠ w00 := hIdxOut ⟨k, hk0⟩ _; let hu0_10 : u0 ≠ w10 := hIdxOut ⟨k, hk0⟩ _;
  let hu1_00 : u1 ≠ w00 := hIdxOut ⟨k + 1, hk1⟩ _; let hu1_20 : u1 ≠ w20 := hIdxOut ⟨k + 1, hk1⟩ _
  { bStarFn := bStar3x2k u0 u1
    cRootInit := Circuit.X w00 ;;ᶜ Circuit.CNOT u0 w00 hu0_00 ;;ᶜ
      Circuit.CNOT u0 w10 hu0_10 ;;ᶜ Circuit.CNOT u1 w00 hu1_00 ;;ᶜ
      Circuit.CNOT u1 w20 hu1_20
    cRootUninit := Circuit.CNOT u1 w20 hu1_20 ;;ᶜ
      Circuit.CNOT u1 w00 hu1_00 ;;ᶜ Circuit.CNOT u0 w10 hu0_10 ;;ᶜ
      Circuit.CNOT u0 w00 hu0_00 ;;ᶜ Circuit.X w00
    count_init := ⟨by simp [Circuit.count_seq, Circuit.X, Circuit.CNOT],
      by simp [Circuit.count_seq, Circuit.X, Circuit.CNOT]⟩
    count_uninit := ⟨by simp [Circuit.count_seq, Circuit.X, Circuit.CNOT],
      by simp [Circuit.count_seq, Circuit.X, Circuit.CNOT]⟩
    cw_init := fun hI hO ↦
      ⟨cw_1 (hO _), cw_cnot (hI _) (hO _), cw_cnot (hI _) (hO _),
        cw_cnot (hI _) (hO _), cw_cnot (hI _) (hO _)⟩
    cw_uninit := fun hI hO ↦
      ⟨cw_cnot (hI _) (hO _), cw_cnot (hI _) (hO _), cw_cnot (hI _) (hO _),
        cw_cnot (hI _) (hO _), cw_1 (hO _)⟩
    idx_decomp := fun δ hLt ↦ by
      have hnb := not_both_one_of_lt_3x2k wIdx δ hLt
      have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
      rw [idxValPrefix_uLoOf (Nat.le_add_right k 2) wIdx δ k le_rfl];
      dsimp only [idxValD, idxValPrefix, bStar3x2k, u0, u1, hk0, hk1]; rw [hpow]
      split_ifs <;> first | (exfalso; exact hnb ⟨by assumption, by assumption⟩) | (dsimp; omega)
    init_ket := fun δ hOut0 hLt ↦ by
      have hnb := not_both_one_of_lt_3x2k wIdx δ hLt; have hw00 : δ w00 = 0 := hOut0 _;
      have hw10 : δ w10 = 0 := hOut0 _; have hw20 : δ w20 = 0 := hOut0 _;
      have hw00_0 : Function.update δ w00 0 = δ := hw00 ▸ Function.update_eq_self w00 δ
      rcases DynCircExt.bit_cases (δ u1) with hu1_0 | hu1_1
      · rcases DynCircExt.bit_cases (δ u0) with hu0_0 | hu0_1
        · have hb : bStar3x2k u0 u1 δ = ⟨0, by omega⟩ := by
            dsimp [bStar3x2k]
            rw [ite_eq_right (by rw [hu1_0]; decide), ite_eq_right (by rw [hu0_0]; decide)]
          have hc0 : Function.update δ w00 1 u0 = 0 :=
              (Function.update_of_ne hu0_00 1 δ).trans hu0_0;
              have hc1 : Function.update δ w00 1 u1 = 0 :=
              (Function.update_of_ne hu1_00 1 δ).trans hu1_0; rw [hb, eval_seq_mulVec,
              eval_seq_mulVec, eval_seq_mulVec, eval_seq_mulVec, ket_X, hw00, zero_add,
              ket_CNOT_of_ctrl_zero hu0_00 hc0, ket_CNOT_of_ctrl_zero hu0_10 hc0,
              ket_CNOT_of_ctrl_zero hu1_00 hc1, ket_CNOT_of_ctrl_zero hu1_20 hc1]
        · have hb : bStar3x2k u0 u1 δ = ⟨1, by omega⟩ := by
            dsimp [bStar3x2k]
            rw [ite_eq_right (by rw [hu1_0]; decide), ite_eq_left hu0_1]
          have hu1_10 : u1 ≠ w10 := hIdxOut ⟨k + 1, hk1⟩ _;
          have hc1 : Function.update δ w10 1 u1 = 0 :=
              (Function.update_of_ne hu1_10 1 δ).trans hu1_0; rw [hb, eval_seq_mulVec,
              eval_seq_mulVec, eval_seq_mulVec, eval_seq_mulVec, ket_X, hw00, zero_add, ket_CNOT,
              Function.update_of_ne hu0_00, hu0_1, Function.update_self, CharTwo.add_self_eq_zero,
              Function.update_idem, hw00_0, ket_CNOT, hw10, hu0_1, zero_add,
              ket_CNOT_of_ctrl_zero hu1_00 hc1, ket_CNOT_of_ctrl_zero hu1_20 hc1]
      · have hu0_0 : δ u0 = 0 := by
          rcases DynCircExt.bit_cases (δ u0) with h | h
          · exact h
          · exact (hnb ⟨h, hu1_1⟩).elim
        have hb : bStar3x2k u0 u1 δ = ⟨2, by omega⟩ := by dsimp [bStar3x2k]; rw [ite_eq_left hu1_1]
        have hc0 : Function.update δ w00 1 u0 = 0 :=
            (Function.update_of_ne hu0_00 1 δ).trans hu0_0; rw [hb, eval_seq_mulVec,
            eval_seq_mulVec, eval_seq_mulVec, eval_seq_mulVec, ket_X, hw00, zero_add,
            ket_CNOT_of_ctrl_zero hu0_00 hc0, ket_CNOT_of_ctrl_zero hu0_10 hc0, ket_CNOT,
            Function.update_of_ne hu1_00, hu1_1, Function.update_self, CharTwo.add_self_eq_zero,
            Function.update_idem, hw00_0, ket_CNOT, hw20, hu1_1, zero_add]
    uninit_init := fun v ↦ by
      simp only [eval_seq_mulVec, mulVec_CNOT_invol, mulVec_X_invol] }

/-- Forward `6*(2^k - 1)`-`T` zero-gated W-state one-hot loader for `N = 3 * 2^k`. -/
def wStateCompute3x2k {Var : Type} {n : ℕ} (k : ℕ) (v : Var) (wHas : Wire n)
    (wIdx : Fin (k + 2) → Wire n) (wOut : Fin (3 * 2 ^ k) → Wire n)
    (qEnc : Wire n) : DynamicCircuit Var n :=
  if h :
      WRouterDisjProp wHas wIdx wOut qEnc then wComputeCore (by omega) rfl (Nat.le_add_right k 2) v
      wHas wIdx wOut qEnc h (wRootSpec3x2k wIdx wOut h.2.2.1)
  else .circuit (seqNat (6 * (2 ^ k - 1)) fun _ _ ↦ Circuit.T wHas)

/-- Reverse `0-T` MBU uncomputer for `N = 3 * 2^k` zero-gated W-state one-hot loader. -/
def wStateUncompute3x2k {Var : Type} {n : ℕ} (k : ℕ) (v : Var) (wHas : Wire n)
    (wIdx : Fin (k + 2) → Wire n) (wOut : Fin (3 * 2 ^ k) → Wire n) : DynamicCircuit Var n :=
  if h :
      WRouterOutDisj wHas wIdx wOut then wUncomputeCore (by omega) rfl (Nat.le_add_right k 2) v wHas
      wIdx wOut h (wRootSpec3x2k wIdx wOut h.2.1)
  else .circuit .identity

theorem count_wStateCompute3x2k {Var : Type} {n : ℕ} (k : ℕ) (v : Var) (wHas : Wire n)
    (wIdx : Fin (k + 2) → Wire n) (wOut : Fin (3 * 2 ^ k) → Wire n) (qEnc : Wire n) :
    (wStateCompute3x2k k v wHas wIdx wOut qEnc).count .T = 6 * (2 ^ k - 1) ∧
        (wStateCompute3x2k k v wHas wIdx wOut qEnc).count .TOFF = 0 := by
  dsimp only [wStateCompute3x2k]
  split_ifs with h
  · exact count_wComputeCore (by omega) rfl (Nat.le_add_right k 2) v wHas wIdx wOut qEnc h _
  · exact ⟨by simpa [DynamicCircuit.count] using count_seqNat_T 1 (6 * (2 ^ k - 1)) _ fun _ _ ↦
                by simp [Circuit.T],
      count_seqNat_TOFF_zero (6 * (2 ^ k - 1)) _ fun _ _ ↦ by simp [Circuit.T]⟩

theorem count_wStateUncompute3x2k {Var : Type} {n : ℕ} (k : ℕ) (v : Var) (wHas : Wire n)
    (wIdx : Fin (k + 2) → Wire n) (wOut : Fin (3 * 2 ^ k) → Wire n) :
    (wStateUncompute3x2k k v wHas wIdx wOut).count .T = 0 ∧
        (wStateUncompute3x2k k v wHas wIdx wOut).count .TOFF = 0 := by
  by_cases WRouterOutDisj wHas wIdx wOut <;> simp [wStateUncompute3x2k, *, count_wUncomputeCore]

theorem dynWires_wStateCompute3x2k {Var : Type} {n : ℕ} {S : Wire n → Prop} (k : ℕ) (v : Var)
    (wHas : Wire n)
    (wIdx : Fin (k + 2) → Wire n) (wOut : Fin (3 * 2 ^ k) → Wire n) (qEnc : Wire n)
    (hHas : S wHas) (hIdx : ∀ d, S (wIdx d)) (hOut : ∀ j, S (wOut j))
        (hQ : S qEnc) : DynWires S (wStateCompute3x2k k v wHas wIdx wOut qEnc) := by
  dsimp only [wStateCompute3x2k]
  split_ifs with h <;> first
    | exact dw_wComputeCore (by omega) rfl (Nat.le_add_right k 2) v wHas wIdx wOut qEnc h _
        hHas hIdx hOut hQ
    | exact cw_seqNat _ _ fun _ _ ↦ cw_1 hHas

theorem dynWires_wStateUncompute3x2k {Var : Type} {n : ℕ} {S : Wire n → Prop} (k : ℕ) (v : Var)
    (wHas : Wire n)
    (wIdx : Fin (k + 2) → Wire n) (wOut : Fin (3 * 2 ^ k) → Wire n)
    (hHas : S wHas) (hIdx : ∀ d, S (wIdx d)) (hOut : ∀ j, S (wOut j)) :
        DynWires S (wStateUncompute3x2k k v wHas wIdx wOut) := by
  dsimp only [wStateUncompute3x2k]
  split_ifs with h <;> first
    | exact dw_wUncomputeCore (by omega) rfl (Nat.le_add_right k 2) v wHas wIdx wOut h _
        hHas hIdx hOut
    | trivial

theorem subspaceStep_wStateCompute3x2k {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ} (k : ℕ)
    (v : Var) (wHas : Wire n)
    (wIdx : Fin (k + 2) → Wire n) (wOut : Fin (3 * 2 ^ k) → Wire n) (qEnc : Wire n)
    (hd : WRouterDisj wHas wIdx wOut qEnc) (R : Operator (2 ^ n))
        (hSupp : SupportedOn (ValidWRouterIn wHas wIdx wOut qEnc) R) :
    SubspaceStep (Var := Var) R ((uOneHotToggle wHas wIdx wOut hd.has_ne_out hd.idx_ne_out).1 * R)
      (wStateCompute3x2k k v wHas wIdx wOut qEnc) := by
  simpa only [wStateCompute3x2k, dite_eq_left hd.disjProp] using
    subspaceStep_wComputeCore (by omega) rfl (Nat.le_add_right k 2) v wHas wIdx wOut qEnc hd _ R
        hSupp

theorem subspaceStep_wStateUncompute3x2k {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    (k : ℕ) (v : Var) (wHas : Wire n)
    (wIdx : Fin (k + 2) → Wire n) (wOut : Fin (3 * 2 ^ k) → Wire n)
        (ho : WRouterOutDisj wHas wIdx wOut)
    (R : Operator (2 ^ n)) (hSupp : SupportedOn (ValidWRouterClean wHas wIdx wOut) R) :
    SubspaceStep (Var := Var) ((uOneHotToggle wHas wIdx wOut ho.1 ho.2.1).1 * R) R
      (wStateUncompute3x2k k v wHas wIdx wOut) := by
  simpa only [wStateUncompute3x2k, dite_eq_left ho] using
    subspaceStep_wUncomputeCore (by omega) rfl (Nat.le_add_right k 2) v wHas wIdx wOut ho _ R hSupp

/-- Decoupled `3x2k` W-state one-hot bracket (`N = 3*2^k`, `D = k+2`, `6*(2^k - 1)` `T`). -/
def wRouterBracket3x2k (k : ℕ) : WRouterBracket (k + 2) (3 * 2 ^ k) (6 * (2 ^ k - 1)) where
  pComp := wStateCompute3x2k k
  pUncomp := wStateUncompute3x2k k
  count_comp := count_wStateCompute3x2k k
  count_uncomp := count_wStateUncompute3x2k k
  dynWires_comp := dynWires_wStateCompute3x2k k
  dynWires_uncomp := dynWires_wStateUncompute3x2k k
  step_comp := subspaceStep_wStateCompute3x2k k
  step_uncomp := fun {Var} [Fintype Var] [DecidableEq Var] {n} v wHas wIdx wOut {_qEnc} hd R hSupp ↦
    subspaceStep_wStateUncompute3x2k (Var := Var) (n := n) k v wHas wIdx wOut hd.outDisj R hSupp

end QuantumComputation.Specs.PhotochemistrySolution.WStateRouterPrim
end
end
