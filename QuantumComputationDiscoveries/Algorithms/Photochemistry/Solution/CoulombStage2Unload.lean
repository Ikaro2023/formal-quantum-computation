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
public import QuantumComputationDiscoveries.Algorithms.Photochemistry.Solution.SplitRouterBellSwap

open QuantumComputation.Specs.PhotochemistrySolution.SpecDefs
open QuantumComputation.Specs.PhotochemistrySolution.QhlAux
open QuantumComputation.Specs.PhotochemistrySolution.PgBase
open QuantumComputation.Specs.PhotochemistrySolution.SelectBase
@[expose] public section
set_option allowUnsafeReducibility true
set_option autoImplicit false
set_option exponentiation.threshold 256

noncomputable section ScopedLocalHelpers
open scoped Matrix BigOperators
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynQromUncompA (wrapDyn
    fwdCirc)
section

open QuantumComputation.Specs.PhotochemistrySolution.ZeroNEremAxisSq18
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SelectCsa64ProvSpec (stepCB)
noncomputable section
open Operator QProg Matrix Circuit Qubit QuantumComputation.Specs.PhotochemistrySolution
  QuantumComputation.Specs.PhotochemistrySolution.SelectCsa64ProvSpec
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
open QuantumComputation.Specs.PhotochemistrySolution.UnembedO3Bridge
section
open DynamicCircuit PrimitiveGate QuantumComputation.Specs
  QuantumComputation.Specs.PhotochemistrySolution.SelectCompactAnc
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB hiding bitSign ket ket_CNOT
  ket_TOFF ket_X matrix_ext_ket writeReg writeReg_apply_of_not_mem
namespace QuantumComputation.Specs.PhotochemistrySolution.FusedUnembedLGen
open ComplexConjugate PhotochemistrySolution.QubitizationWalkSem
  PhotochemistrySolution.QubitizationTop PhotochemistrySolution.SelectSymDyn
  PhotochemistrySolution.SelectSymDynInstance PhotochemistrySolution.SelectRefl
  PhotochemistrySolution.SelectGidneyFast PhotochemistrySolution.TargetBScr
open PhotochemistrySolution.OvBidir PhotochemistrySolution.SelectCompactRot34
  PhotochemistrySolution.SelectEulerRot32 PhotochemistrySolution.SelectLcu70Rot32
  PhotochemistrySolution.DynQromUncompA
open PhotochemistrySolution.TopSelectBridge PhotochemistrySolution.UnembedIdleAncillas
attribute [local irreducible] SpecDefs.systemQubits_frozen
    SelectCompactAnc.ancWOfScr
theorem assoc5 {S : Type*} [Semigroup S] (a b c d e : S) :
    (a * b) * c * (d * e) = a * (b * c * d) * e := by simp only [mul_assoc]
theorem cleanWorkStep_of_subspaceStep {Var : Type} [Fintype Var] [DecidableEq Var] {n w : ℕ}
    [NeZero (2 ^ n)] (rScr : QRegister w n) (U : Unitary (2 ^ n)) (p : DynamicCircuit Var n)
    (hc : U.1 * rScr.basisOutcomeProjector 0 = rScr.basisOutcomeProjector 0 * U.1)
    (hSub : SubspaceStep (rScr.basisOutcomeProjector 0) (U.1 * rScr.basisOutcomeProjector 0) p) :
    CleanWorkStep rScr U p :=
  ⟨hc, fun M ↦ let ⟨N, hw, hm⟩ := hSub M
    ⟨N, hw,
        by rwa [Matrix.conjTranspose_mul, rScr.basisOutcomeProjector_conjTranspose 0,
             assoc5] at hm⟩⟩
theorem fused_semigrp_steps {S : Type*} [Semigroup S] (F C X R U Uf P P35 : S)
    (hUf : Uf = R * U * X * R * X) (hFCR : C * (F * P) = F * (R * P)) (hRP : R * P = P * R)
    (hXP : X * P = P * X) (hUP : U * P = P * U) (hFX : X * F = F * X) (hFP35 : P35 * F = F * P35)
    (hFU : U * F = F * U) (hPP : P * P = P) (hP35 : P35 * P = P) : Uf * P = P * Uf ∧ X * (F * P) =
    (F * P) * X ∧ C * ((F * P) * X) = F * (R * (P * X)) ∧ X * (F * (R * (P * X))) = F *
    (P * (X * (R * X))) ∧ P35 * (F * (P * (X * (R * X)))) = F * (P * (X * (R * X))) ∧ U *
    (F * (P * (X * (R * X)))) = (F * P) * (U * (X * (R * X))) ∧ C *
    ((F * P) * (U * (X * (R * X)))) = F * (Uf * P) ∧ P * (Uf * P) = Uf * P := by
  have hr (z : S) : R * (P * z) = P * (R * z) := by rw [← mul_assoc, hRP, mul_assoc]
  have hx (z : S) : X * (P * z) = P * (X * z) := by rw [← mul_assoc, hXP, mul_assoc]
  have hu (z : S) : U * (P * z) = P * (U * z) := by rw [← mul_assoc, hUP, mul_assoc]
  have hc : Uf * P = P * Uf := by simp only [hUf, mul_assoc]; rw [hXP, hr, hx, hu, hr]
  exact ⟨hc, by rw [← mul_assoc, hFX, mul_assoc, hXP, ← mul_assoc],
    by rw [← mul_assoc C, hFCR, mul_assoc, mul_assoc],
        by rw [← mul_assoc X F, hFX, mul_assoc F X, hr, hx],
    by rw [← mul_assoc P35 F, hFP35, mul_assoc F, ← mul_assoc P35 P, hP35],
    by rw [← mul_assoc U F, hFU, mul_assoc F U, hu, ← mul_assoc F P],
    by rw [← mul_assoc C, hFCR, mul_assoc F, hc, mul_assoc R P, hr, hUf]; simp only [mul_assoc],
    by rw [← mul_assoc, ← hc, mul_assoc, hPP]⟩
end QuantumComputation.Specs.PhotochemistrySolution.FusedUnembedLGen

namespace QuantumComputation.Specs.PhotochemistrySolution.ProviderCore
open scoped Circuit.Notation
open PhotochemistrySolution.SelectFastQft8Gidney PhotochemistrySolution.SelectQft8GidneyStg3
  PhotochemistrySolution.SplitRouterSeqBell26k PhotochemistrySolution.SplitRouter47_187
  PhotochemistrySolution.UnembedIdleAncillas PhotochemistrySolution.SelectOracles
open PhotochemistrySolution.RouterSelectWiringA PhotochemistrySolution.XMeasLinearCleanStep
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynQromUncompA (remeasureIf)
attribute [local semireducible] wrapDyn remeasureIf xUnloadCzPairsSeqDyn tempAndFanoutDyn
/-! ## Section 3: Symbolic `(M, D)` Dual-Bell `DynWires` & `stage2FourPortRouter` -/

theorem cw_1 {n : ℕ} {S : Wire n → Prop} {g : PrimitiveGate 1} {w : Wire n}
    (hw : S w) : CircWires S (.gate g (QRegister.singleton w)) := fun _ ↦ hw
theorem cw_cnot {n : ℕ} {S : Wire n → Prop} {c t : Wire n} {h : c ≠ t} (hc : S c)
    (ht : S t) : CircWires S (Circuit.CNOT c t h) :=
  fun i ↦ by fin_cases i <;> first | exact hc | exact ht
theorem cw_cnotPairs {n : ℕ} {S : Wire n → Prop} :
    ∀ (ps : List (WirePair n)), (∀ p ∈ ps, S p.1 ∧ S p.2.1) → CircWires S (cnotPairsCircuit ps)
  | [], _ => trivial
  | p :: ps, hS =>
      ⟨cw_cnot (hS p List.mem_cons_self).1 (hS p List.mem_cons_self).2, cw_cnotPairs ps fun p' hp' ↦
          hS p' (List.mem_cons_of_mem p hp')⟩
theorem cw_czPairs {n : ℕ} {S : Wire n → Prop} :
    ∀ (ps : List (WirePair n)), (∀ p ∈ ps, S p.1 ∧ S p.2.1) → CircWires S (czPairsCircuit ps)
  | [], _ => trivial
  | p :: ps, hS =>
      let h := hS p List.mem_cons_self
      ⟨⟨cw_1 h.2, cw_cnot h.1 h.2, cw_1 h.2⟩, cw_czPairs ps fun p' hp' ↦
          hS p' (List.mem_cons_of_mem p hp')⟩
theorem dw_xUnload {Var : Type} {n : ℕ} {S : Wire n → Prop} {v : Var} {q : Wire n}
    {ps : List (WirePair n)} {rest : DynamicCircuit Var n} (hq : S q)
    (hps : ∀ p ∈ ps, S p.1 ∧ S p.2.1) (hRest : DynWires S rest) :
    DynWires S (xUnloadCzPairsSeqDyn v q ps rest) :=
  ⟨cw_1 hq, ⟨fun _ ↦ hq, ⟨cw_1 hq, cw_czPairs ps hps⟩, trivial⟩, hRest⟩

/-!
## Section 4: `DynWires` Combinators for `AndBracketProg.onRegister`, `pKinFullFromRegs`,
`pCluster22`, & `idlePhaseBracket`
-/

theorem dynWires_onRegister {Var : Type} {K N : ℕ} (v : Var) (r : QRegister K N)
    {P : Wire K → Prop} {S : Wire N → Prop} (hP : ∀ w, P w → S (r w)) :
    ∀ {p : AndBracketProg K}, AndBracketWires P p → DynWires S ((p.onRegister r).toDyn v)
  | .id, _ => trivial
  | .prim c, hc => by
      induction c with
      | identity => trivial
      | gate _ reg => exact fun i ↦ hP (reg i) (hc i)
      | seq _ _ ih₁ ih₂ => exact ⟨ih₁ hc.1, ih₂ hc.2⟩
  | .seq _ _, ⟨h₁, h₂⟩ => ⟨dynWires_onRegister v r hP h₁, dynWires_onRegister v r hP h₂⟩
  | .tempAnd c₁ c₂ a _ _ _ _, ⟨hc₁, hc₂, haP, hb⟩ =>
      have ha := hP a haP
      ⟨⟨cw_1 ha, cw_1 ha, cw_cnot (hP c₂ hc₂) ha, circWires_inverse (cw_1 ha),
          cw_cnot (hP c₁ hc₁) ha,
        cw_1 ha, cw_cnot (hP c₂ hc₂) ha, circWires_inverse (cw_1 ha), cw_cnot (hP c₁ hc₁) ha,
            cw_1 ha, cw_1 ha⟩,
       dynWires_onRegister v r hP hb, ⟨cw_1 ha, fun _ ↦ ha,
        ⟨cw_1 ha, ⟨cw_1 (hP c₂ hc₂), cw_cnot (hP c₁ hc₁) (hP c₂ hc₂), cw_1 (hP c₂ hc₂)⟩⟩, trivial⟩⟩
end QuantumComputation.Specs.PhotochemistrySolution.ProviderCore
end

namespace QuantumComputation.Specs.PhotochemistrySolution.Stage2ZeroGated
open scoped ComplexOrder MatrixOrder
open HermitianMat PhotochemistrySolution.XMeasUnld PhotochemistrySolution.SplitRouter47_187
open PrimitiveGate hiding s
open _root_.DynamicCircuit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt hiding bit_cases
  eval_seq_mulVec ket ket_CNOT ket_TOFF ket_X ket_projector_one ket_projector_zero matrix_ext_ket
  qAssign_obs_map_val
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB hiding bitSign eval_seq_mulVec ket
  ket_CNOT ket_TOFF ket_X matrix_ext_ket writeReg writeReg_apply_of_not_mem
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SplitRouterSeqBell26k hiding ket
  matrix_ext_ket
attribute [local semireducible] ComputeProg.fwdBits DynQromUncompA.remeasureIf
    DynQromUncompA.wrapDyn DynQromUncompA.fwdCirc
theorem progSupportedIn_mono {n : ℕ} {P Q : Wire n → Prop} (hPQ : ∀ w, P w → Q w) :
    ∀ {p : ComputeProg n}, ProgSupportedIn P p → ProgSupportedIn Q p
  | .id, _ => trivial
  | .x _, hp => hPQ _ hp
  | .cnot _ _ _, hp => ⟨hPQ _ hp.1, hPQ _ hp.2⟩
  | .andGate _ _ _ _ _ _, hp => ⟨hPQ _ hp.1, hPQ _ hp.2.1, hPQ _ hp.2.2⟩
  | .seq _ _, hp => ⟨progSupportedIn_mono hPQ hp.1, progSupportedIn_mono hPQ hp.2⟩
end QuantumComputation.Specs.PhotochemistrySolution.Stage2ZeroGated
end

noncomputable section
open Operator QProg Matrix QuantumComputation.Specs.PhotochemistrySolution
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SplitBellVecCleanStep
    (specFanoutCopyCirc bellZHalfVecDyn bellXHalfVecDyn)
open _root_.DynamicCircuit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt hiding bit_cases
  eval_seq_mulVec ket ket_CNOT ket_TOFF ket_X ket_projector_one ket_projector_zero matrix_ext_ket
  qAssign_obs_map_val
section
open scoped ComplexOrder MatrixOrder Circuit.Notation
open HermitianMat QuantumComputation.Specs.PhotochemistrySolution.XMeasUnld
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB hiding bitSign eval_seq_mulVec ket
  ket_CNOT ket_TOFF ket_X matrix_ext_ket writeReg writeReg_apply_of_not_mem
open _root_.QuantumComputation.Specs.PhotochemistrySolution.QubitizationWalkSem hiding bitSign
  bitSign_add bitSign_mul_self sqrtHalf sqrtHalf_mul_sqrtHalf star_sqrtHalf
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SplitRouterSeqBell26k hiding ket
  matrix_ext_ket
namespace QuantumComputation.Specs.PhotochemistrySolution.SplitRouter47_187
attribute [local semireducible] DynQromUncompA.remeasureIf DynQromUncompA.wrapDyn
    DynQromUncompA.fwdCirc ComputeProg.ValidProg ComputeProg.finalClean ComputeProg.fwdBits
    SplitBellVecCleanStep.cnotFanoutCirc SplitBellVecCleanStep.czFanoutCirc
    SplitBellVecCleanStep.specFanoutCopyCirc SplitBellVecCleanStep.bellZHalf1Dyn
    SplitBellVecCleanStep.bellXHalf1Dyn SplitBellVecCleanStep.bellZHalfVecDyn
    SplitBellVecCleanStep.bellXHalfVecDyn
theorem hne_rBufLo_ctrlLo {M D n : ℕ} (r : RouterReg M D n) (k : Fin 24) (p : Fin M) : rBufLo r k ≠
    rCtrlLo r p :=
  rr_ne r (by cases k; cases p; unfold basePub; dsimp; omega)
theorem hne_rHA_ctrlLo {M D n : ℕ} (r : RouterReg M D n) (k : Fin 24) (p : Fin M) : rHA r k ≠
    rCtrlLo r p :=
  rr_ne r (by cases k; cases p; unfold basePub; dsimp; omega)
theorem hne_rCtrlLo_pSys {M D n : ℕ} (r : RouterReg M D n) (k : Fin 24)
    (p q : Fin M) : rCtrlLo r p ≠ pSys (planeOfRouter r k) q := by
  rw [planeOfRouter_sys];
      exact rr_ne r (by cases k; cases p; cases q; unfold basePub; dsimp; omega)
theorem hne_rCtrlHi_pSys {M D n : ℕ} (r : RouterReg M D n) (k : Fin 24)
    (p q : Fin M) : rCtrlHi r p ≠ pSys (planeOfRouter r k) q := by
  rw [planeOfRouter_sys];
      exact rr_ne r (by cases k; cases p; cases q; unfold basePub; dsimp; omega)
theorem hne_fixed_router_sys {M D n : ℕ} (r : RouterReg M D n) (b₁ b₂ : Fin 24)
    (p : Fin M) : rBufLo r b₁ ≠ pSys (planeOfRouter r b₂) p ∧ rBufHi r b₁ ≠
    pSys (planeOfRouter r b₂) p ∧ rHA r b₁ ≠ pSys (planeOfRouter r b₂) p ∧ rHB r b₁ ≠
    pSys (planeOfRouter r b₂) p := by
  rcases b₁, b₂, p with ⟨⟨_, h1⟩, ⟨_, h2⟩, ⟨_, hp⟩⟩
  rw [planeOfRouter_sys]; refine ⟨rr_ne r ?_, rr_ne r ?_, rr_ne r ?_, rr_ne r ?_⟩ <;> dsimp <;>
      omega
theorem planeModDisj {M D n : ℕ} (r : RouterReg M D n) {j k : Fin 24} (hjk : j ≠ k) (w : Wire n)
    (hj : PlaneModSet (planeOfRouter r j) w) (hk : PlaneModSet (planeOfRouter r k) w) : False := by
  refine planeModSet_disj_planeOfRouter r j k hjk w hj
      (by rcases hk with rfl | rfl | rfl | rfl | ⟨_, rfl⟩ <;> exact ⟨_, rfl⟩)

def AtMostOneCtrl {M n : ℕ} (wC : Fin M → Wire n) (γ : BitAssignment n) : Prop :=
    (∀ p : Fin M, γ (wC p) = 0) ∨ ∃ p₀ : Fin M, γ (wC p₀) = 1 ∧ ∀ p : Fin M, p ≠ p₀ → γ (wC p) = 0
/- ## Part C2: Fanout Support, `pDualBellUnloadMD` (`488` / `1,648 T`) & Support Bound -/

theorem portSwap1Bits_of_ne {n : ℕ} : ∀ (K : ℕ) (qB : Wire n) (wCtrl wTgt : Fin K → Wire n)
    (α : BitAssignment n) (w : Wire n), w ≠ qB → (∀ p : Fin K, w ≠ wTgt p) →
    portSwap1Bits K qB wCtrl wTgt α w = α w
  | 0, _, _, _, _, _, _, _ => rfl
  | K + 1, qB, wCtrl, wTgt, α, w, hwB, hwT => by
      simp only [portSwap1Bits, Function.update_of_ne (hwT (Fin.last K)), Function.update_of_ne hwB]
      exact portSwap1Bits_of_ne K qB (wCtrl ∘ Fin.castSucc) (wTgt ∘ Fin.castSucc) α w hwB fun p ↦
          hwT p.castSucc
theorem hne_unload_core {M D n : ℕ} (r : RouterReg M D n) : (∀ k : Fin 24, rBufHi r k ≠ rHB r k) ∧
    (∀ k : Fin 24, rBufLo r k ≠ rHA r k) ∧ (∀ (k : Fin 24) (p : Fin M), rCtrlHi r p ≠
    pSys (planeOfRouter r k) p) ∧ (∀ (k : Fin 24) (p : Fin M), rCtrlLo r p ≠
    pSys (planeOfRouter r k) p) :=
  ⟨fun k ↦ rr_ne r (by rcases k with ⟨_, hk⟩; dsimp; omega),
   fun k ↦ rr_ne r (by rcases k with ⟨_, hk⟩; dsimp; omega),
   fun k p ↦ hne_rCtrlHi_pSys r k p p, fun k p ↦ hne_rCtrlLo_pSys r k p p⟩
end QuantumComputation.Specs.PhotochemistrySolution.SplitRouter47_187
end

namespace QuantumComputation.Specs.PhotochemistrySolution.PotSelectWiring
open Circuit Qubit PrimitiveGate PhotochemistrySolution.SplitRouter47_187
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB (ket)
theorem three_cnot_mulVec_ket {n : ℕ} [NeZero (2 ^ n)] (a b : Wire n) (hab : a ≠ b)
    (β : BitAssignment n) : ((Circuit.seq (Circuit.CNOT a b hab)
    (Circuit.seq (Circuit.CNOT b a hab.symm) (Circuit.CNOT a b hab))).eval.1).mulVec (ket β) =
    ket (swapPairBits a b β) := by
  change ((Circuit.seq (Circuit.CNOT a b hab) (Circuit.seq (Circuit.CNOT b a hab.symm)
    (Circuit.CNOT a b hab))).eval.1).mulVec (DynCircExt.ket β) =
        DynCircExt.ket (swapPairBits a b β)
  rw [DynCircExt.eval_seq_mulVec, DynCircExt.eval_seq_mulVec, DynCircExt.ket_CNOT,
    DynCircExt.ket_CNOT, DynCircExt.ket_CNOT]
  refine congrArg DynCircExt.ket (funext fun w ↦ ?_)
  rcases eq_or_ne w a with rfl | hwa
  · rcases DynCircExt.bit_cases (β w) with hw | hw <;>
        rcases DynCircExt.bit_cases (β b) with hb | hb <;>
      simp [swapPairBits, hab, hab.symm, hw, hb, CharTwo.add_self_eq_zero]
  · rcases eq_or_ne w b with rfl | hwb
    · rcases DynCircExt.bit_cases (β a) with ha | ha <;>
          rcases DynCircExt.bit_cases (β w) with hw | hw <;>
        simp [swapPairBits, hab, hab.symm, ha, hw, CharTwo.add_self_eq_zero]
    · simp [swapPairBits, hwa, hwb]
theorem fixedSwap1Circ_zero_ket_ul {n : ℕ} [NeZero (2 ^ n)] :
    ∀ (M : ℕ) (qB : Wire n) (cVec : Fin M → ZMod 2) (wTgt : Fin M → Wire n)
      (hbt : ∀ p : Fin M, qB ≠ wTgt p) (β : BitAssignment n),
      (∀ p : Fin M, cVec p = 0) →
      (fixedSwap1Circ M qB cVec wTgt hbt).eval.1.mulVec (ket β) = ket β
  | 0, _, _, _, _, β, _ => Matrix.one_mulVec (ket β)
  | M + 1, qB, cVec, wTgt, hbt, β, hz => by
      simp only [fixedSwap1Circ, DynCircExt.eval_seq_mulVec,
      Circuit.eval_identity, Submonoid.coe_one, Matrix.one_mulVec, hz (Fin.last M), zero_ne_one,
                                              ↓reduceIte,
      fixedSwap1Circ_zero_ket_ul M qB _ _ (fun p ↦ hbt p.castSucc) β fun p ↦ hz p.castSucc]
theorem fixedSwap1Circ_oneHot_ket_ul {n : ℕ} [NeZero (2 ^ n)] :
    ∀ (M : ℕ) (qB : Wire n) (cVec : Fin M → ZMod 2) (wTgt : Fin M → Wire n)
      (hbt : ∀ p : Fin M, qB ≠ wTgt p) (p₀ : Fin M) (β : BitAssignment n),
      (∀ p : Fin M, cVec p = if p = p₀ then 1 else 0) →
      (fixedSwap1Circ M qB cVec wTgt hbt).eval.1.mulVec (ket β) =
        ket (swapPairBits qB (wTgt p₀) β)
  | 0, _, _, _, _, p₀, _, _ => Fin.elim0 p₀
  | M + 1, qB, cVec, wTgt, hbt, p₀, β, h1 => by
      dsimp only [fixedSwap1Circ]; rw [DynCircExt.eval_seq_mulVec]
      rcases Fin.eq_castSucc_or_eq_last p₀ with ⟨p₁, rfl⟩ | rfl
      · rw [fixedSwap1Circ_oneHot_ket_ul M qB _ _ (fun p ↦ hbt p.castSucc) p₁ β (fun p ↦
            by simp [h1]),
          h1 (Fin.last M), ite_eq_right (Fin.castSucc_lt_last p₁).ne.symm]
        simp only [zero_ne_one, ↓reduceIte, Circuit.eval_identity, Submonoid.coe_one,
            Matrix.one_mulVec]
      · rw [fixedSwap1Circ_zero_ket_ul M qB _ _ (fun p ↦ hbt p.castSucc) β (fun p ↦
            by simp [h1, (Fin.castSucc_lt_last p).ne]),
          h1 (Fin.last M), ite_eq_left rfl, ite_eq_left rfl]
        exact three_cnot_mulVec_ket qB (wTgt (Fin.last M)) (hbt (Fin.last M)) β
theorem fixedSwapVecCirc_zero_ket_ul {n M : ℕ} [NeZero (2 ^ n)] :
    ∀ (m : ℕ) (qB : Fin m → Wire n) (cVec : Fin M → ZMod 2)
      (wTgt : Fin m → Fin M → Wire n) (hbt : ∀ (k : Fin m) (p : Fin M), qB k ≠ wTgt k p)
      (β : BitAssignment n),
      (∀ p : Fin M, cVec p = 0) →
      (fixedSwapVecCirc M m qB cVec wTgt hbt).eval.1.mulVec (ket β) = ket β
  | 0, _, _, _, _, β, _ => Matrix.one_mulVec (ket β)
  | m + 1, qB, cVec, wTgt, hbt, β, hz => by
      simp only [fixedSwapVecCirc, DynCircExt.eval_seq_mulVec,
      fixedSwapVecCirc_zero_ket_ul m _ cVec _ (fun k ↦ hbt k.castSucc) β hz,
      fixedSwap1Circ_zero_ket_ul M _ cVec _ (hbt (Fin.last m)) β hz]
theorem fixedSwapVecCirc_oneHot_ket_ul {n M : ℕ} [NeZero (2 ^ n)] :
    ∀ (m : ℕ) (qB : Fin m → Wire n) (cVec : Fin M → ZMod 2)
      (wTgt : Fin m → Fin M → Wire n) (hbt : ∀ (k : Fin m) (p : Fin M), qB k ≠ wTgt k p)
      (p₀ : Fin M) (β : BitAssignment n),
      (∀ p : Fin M, cVec p = if p = p₀ then 1 else 0) →
      (fixedSwapVecCirc M m qB cVec wTgt hbt).eval.1.mulVec (ket β) =
        ket (swapVecBits m qB (fun k ↦ wTgt k p₀) β)
  | 0, _, _, _, _, _, β, _ => Matrix.one_mulVec (ket β)
  | m + 1, qB, cVec, wTgt, hbt, p₀, β, h1 => by simp only [fixedSwapVecCirc, swapVecBits,
      DynCircExt.eval_seq_mulVec, fixedSwapVecCirc_oneHot_ket_ul m _ cVec _ (fun k ↦
                                                  hbt k.castSucc) p₀ β h1,
      fixedSwap1Circ_oneHot_ket_ul M _ cVec _ (hbt (Fin.last m)) p₀ _ h1]
end QuantumComputation.Specs.PhotochemistrySolution.PotSelectWiring
end

noncomputable section
namespace QuantumComputation.Specs.PhotochemistrySolution.CoulombFast
open Qubit PhotochemistrySolution.FineLegendre
theorem stepCB_primTree_bit {m n : ℕ} (t : PrimTree) (r : QRegister (m + 1) n)
    (β : BitAssignment n) (u : Fin (m + 1)) :
    stepCB r (decodePrimTree m t).fwdBits β (r u) =
      if (evalPrimTree m (natOfZModBits (m + 1) (fun i ↦ β (r i))) t).testBit u.val
      then 1 else 0 :=
  PhotochemistrySolution.PopBernstein.stepCB_decodePrimTree_apply t r β u
end QuantumComputation.Specs.PhotochemistrySolution.CoulombFast
namespace QuantumComputation.Specs.PhotochemistrySolution.PopBernstein
/-- Encode a single-qubit `.X` gate on `dst < 96` in `PrimTree` (`0` `TempAND`s). -/
def pX95 (dst : ℕ) : PrimTree := .leaf (dst <<< 2)
theorem evalPrimTree95_x {dst : ℕ} (hd : dst < 96) (st i : ℕ) :
    (evalPrimTree 95 st (pX95 dst)).testBit i =
      if i = dst then xor (st.testBit i) true else st.testBit i := by
  have hc : (dst <<< 2) % 4 = 0 := by simp only [Nat.shiftLeft_eq]; omega
  have hw1 : (((dst <<< 2) >>> 2) % 512) % 96 = dst := by
    simp only [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]; omega
  unfold pX95 evalPrimTree evalPrimGate
  dsimp only
  rw [hc, hw1]
  rcases eq_or_ne i dst with rfl | hi
  · simp
  · simp [hi, pbK179_xor_bit_ne st dst i hi]
end QuantumComputation.Specs.PhotochemistrySolution.PopBernstein
namespace QuantumComputation.Specs.PhotochemistrySolution.CoulOWPersBridge
open Qubit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt (writeReg_apply_reg
  writeReg_apply_of_not_mem)
theorem cowp_stepCB_eq {w n : ℕ} (r : QRegister w n)
    (f : (Fin w → ZMod 2) → Fin w → ZMod 2) (s₁ s₂ : BitAssignment n)
    (hEq : ∀ u : Fin w, s₁ (r u) = s₂ (r u)) (x : Wire n)
    (hxOut : (∀ u : Fin w, r u ≠ x) → s₁ x = s₂ x) :
    stepCB r f s₁ x = stepCB r f s₂ x := by
  rcases Classical.em (∃ u : Fin w, r u = x) with ⟨u, rfl⟩ | hne
  · simp only [stepCB, writeReg_apply_reg,
      show (fun q ↦ s₁ (r q)) = fun q ↦ s₂ (r q) from funext hEq]
  · simpa only [stepCB, writeReg_apply_of_not_mem _ _ _ _ hne] using hxOut fun u hu ↦ hne ⟨u, hu⟩
end QuantumComputation.Specs.PhotochemistrySolution.CoulOWPersBridge
end
end

noncomputable section
open QuantumComputation.Specs.PhotochemistrySolution.SelectCsa64ProvSpec
open Operator QProg Matrix HermitianMat QuantumComputation.Specs.PhotochemistrySolution
  QuantumComputation.Specs.PhotochemistrySolution.XMeasUnld
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SplitBellVecCleanStep
    (subspaceStep_congr_out specFanoutCopyCirc specFanoutCopyCirc_mulVec_ket specFanoutCopyVecCirc
    specPortUnextract1Unitary specPortUnextractVecUnitary bellZHalfVecDyn bellXHalfVecDyn)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SplitBellVecCleanStep
    (subspaceStep_bellXHalfVec fanoutXorBits czFanoutPhase czFanoutPhase_indep
    czFanoutPhase_of_all_zero czFanoutPhase_of_unique_one)
open scoped ComplexOrder MatrixOrder
open _root_.DynamicCircuit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt hiding bit_cases
  eval_seq_mulVec ket ket_CNOT ket_TOFF ket_X ket_projector_one ket_projector_zero matrix_ext_ket
  qAssign_obs_map_val
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB hiding bitSign eval_seq_mulVec ket
  ket_CNOT ket_TOFF ket_X matrix_ext_ket writeReg writeReg_apply_of_not_mem
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SplitRouterSeqBell26k hiding ket
  matrix_ext_ket
namespace QuantumComputation.Specs.PhotochemistrySolution.SplitRouter47_187
open scoped Circuit.Notation
open _root_.QuantumComputation.Specs.PhotochemistrySolution.QubitizationWalkSem hiding bitSign
  bitSign_add bitSign_mul_self sqrtHalf sqrtHalf_mul_sqrtHalf star_sqrtHalf
attribute [local semireducible] DynQromUncompA.remeasureIf DynQromUncompA.wrapDyn
    DynQromUncompA.fwdCirc ComputeProg.ValidProg ComputeProg.finalClean ComputeProg.fwdBits
    SplitBellVecCleanStep.cnotFanoutCirc SplitBellVecCleanStep.czFanoutCirc
    SplitBellVecCleanStep.specFanoutCopyCirc SplitBellVecCleanStep.bellZHalf1Dyn
    SplitBellVecCleanStep.bellXHalf1Dyn SplitBellVecCleanStep.bellZHalfVecDyn
    SplitBellVecCleanStep.bellXHalfVecDyn
theorem ket_sr_eq {n : ℕ} (α : BitAssignment n) :
    PhotochemistrySolution.SplitRouterSeqBell26k.ket α = ket α := rfl

/-! ## Part C1: 24-Plane `bellXHalfVec` Cancellation -/

theorem ket_dc_eq {n : ℕ} (α : BitAssignment n) :
    DynCircExt.ket α = ket α := rfl
theorem preservesKetPred_mono {n : ℕ} {P Q : BitAssignment n → Prop} (hPQ : ∀ α, P α → Q α)
    {ψ : Fin (2 ^ n) → ℂ} (hψ : PreservesKetPred P ψ) : PreservesKetPred Q ψ := fun A B hAB ↦
    hψ A B (fun α hα ↦ hAB α (hPQ α hα))
theorem unextract1_portSwap1_ket {M D n : ℕ} (rp : PlaneReg M D n) (qB : Wire n)
    (wC : Fin M → Wire n) (hbc : ∀ p, qB ≠ wC p) (hbt : ∀ p, qB ≠ pSys rp p)
    (hc_disj : ∀ p q, wC p ≠ pSys rp q) {δ : BitAssignment n} (hOne : AtMostOneCtrl wC δ)
    (hqB0 : δ qB = 0) : (specPortUnextract1Unitary M qB wC (pSys rp) hbc hbt (fun p ↦
    hc_disj p p)).1.mulVec ((portSwap1Circ M qB wC (pSys rp) hbc hbt (fun p ↦
    hc_disj p p)).eval.1.mulVec (ket δ)) = ket δ := by
  dsimp only [specPortUnextract1Unitary, Submonoid.coe_mul];
  rw [← Matrix.mulVec_mulVec, portSwap1Circ_mulVec_ket, ket_sr_eq, specFanoutCopyCirc_mulVec_ket]
  have hUpdB0 : Function.update δ qB 0 = δ := hqB0 ▸ Function.update_eq_self qB δ
  rcases hOne with hz | ⟨p₀, hp1, hp0⟩
  · rw [portSwap1Bits_of_all_zero M qB wC (pSys rp) hc_disj hbc δ hz, itePos hqB0, ← ket_sr_eq,
      bitToggleUnitary_mulVec_ket, ket_sr_eq, hqB0,
      czFanoutPhase_of_all_zero M wC (pSys rp) δ hz, add_zero, hUpdB0]
  · rw [portSwap1Bits_of_unique_one M qB wC (pSys rp) hbc hbt hc_disj (pr_inj_sys rp) δ p₀ hp1 hp0,
        hqB0]
    set δs := Function.update (Function.update δ qB (δ (pSys rp p₀))) (pSys rp p₀) 0
    have hδs_qB : δs qB = δ (pSys rp p₀) := by
      dsimp only [δs]; rw [Function.update_of_ne (hbt p₀), Function.update_self]
    have hδs_c : ∀ p, δs (wC p) = δ (wC p) := fun p ↦ by
      dsimp only [δs]; rw [Function.update_of_ne (hc_disj p p₀), Function.update_of_ne (hbc p).symm]
    rw [hδs_qB]
    rcases bit_cases (δ (pSys rp p₀)) with hs0 | hs1
    · rw [itePos hs0,
      show δs = δ by simpa only [δs, hs0, hUpdB0] using Function.update_eq_self (pSys rp p₀) δ,
        ← ket_sr_eq, bitToggleUnitary_mulVec_ket, ket_sr_eq, hqB0,
        czFanoutPhase_of_unique_one M wC (pSys rp) δ p₀ hp1 hp0, hs0, add_zero, hUpdB0]
    · rw [iteNeg (hs1 ▸ one_ne_zero),
          SplitBellVecCleanStep.fanoutXorBits_of_unique_one M wC (pSys rp) hc_disj δs p₀
          ((hδs_c p₀).trans hp1) (fun p hp ↦ (hδs_c p).trans (hp0 p hp))]
      have hUpdEq : Function.update δs (pSys rp p₀) (δs (pSys rp p₀) + 1) =
          Function.update δ qB 1 := by
        simp only [δs, hs1, Function.update_self, zero_add, Function.update_idem]
        exact Function.update_eq_self_iff.mpr
          ((Function.update_of_ne (hbt p₀).symm 1 δ).trans hs1).symm
      rw [hUpdEq, ← ket_sr_eq, bitToggleUnitary_mulVec_ket, ket_dc_eq, Function.update_self,
        czFanoutPhase_indep M wC (pSys rp) (fun p ↦ (hbc p).symm) (fun p ↦ (hbt p).symm) δ 1,
        czFanoutPhase_of_unique_one M wC (pSys rp) δ p₀ hp1 hp0, hs1,
        show (1 : ZMod 2) + 1 = 0 from rfl, Function.update_idem, hUpdB0]
theorem planeUnextract1_localKetOp {M D n : ℕ} (rp : PlaneReg M D n) (qB : Wire n)
    (wC : Fin M → Wire n) (hbc : ∀ p, qB ≠ wC p) (hbt : ∀ p, qB ≠ pSys rp p)
    (hct : ∀ p, wC p ≠ pSys rp p) (hqB : PlaneModSet rp qB) (O : Wire n → Prop)
    (hO_disj : ∀ u, PlaneModSet rp u → ¬ O u) (hO_C : ∀ p, ¬ O (wC p)) :
    LocalKetOp (PlaneModSet rp) O
      (specPortUnextract1Unitary M qB wC (pSys rp) hbc hbt hct).1
      (fun β ↦
        let η := if β qB = 0 then β else fanoutXorBits M wC (pSys rp) β
        Function.update η qB (η qB + czFanoutPhase M wC (pSys rp) η)) := by
  have opC := planeFanout1_localKetOp rp qB wC hbc hbt hct hqB O hO_disj hO_C
  refine ⟨fun β ↦ ?_, fun β w hw ↦ ?_, fun β₁ β₂ hEq w hwW ↦ ?_⟩
  · dsimp only [specPortUnextract1Unitary, Submonoid.coe_mul];
    rw [← Matrix.mulVec_mulVec, opC.1 β, bitToggleUnitary_mulVec_ket, ket_dc_eq, ket_sr_eq]
  · simp only [Function.update_of_ne (fun h : w = qB ↦ hw (h ▸ hqB)), opC.2.1 β w hw]
  · have hEqη (u : Wire n) (hu : ¬ O u) :
        (if β₁ qB = 0 then β₁ else fanoutXorBits M wC (pSys rp) β₁) u =
        (if β₂ qB = 0 then β₂ else fanoutXorBits M wC (pSys rp) β₂) u :=
      (Classical.em (PlaneModSet rp u)).elim (opC.2.2 β₁ β₂ hEq u) fun huW ↦
        (opC.2.1 β₁ u huW).trans ((hEq u hu).trans (opC.2.1 β₂ u huW).symm)
    have hPh : ∀ (K : ℕ) (hK : K ≤ M), czFanoutPhase K (fun p ↦
        wC ⟨p.val, Nat.lt_of_lt_of_le p.isLt hK⟩)
        (fun p ↦ pSys rp ⟨p.val, Nat.lt_of_lt_of_le p.isLt hK⟩)
        (if β₁ qB = 0 then β₁ else fanoutXorBits M wC (pSys rp) β₁) = czFanoutPhase K (fun p ↦
        wC ⟨p.val, Nat.lt_of_lt_of_le p.isLt hK⟩)
        (fun p ↦ pSys rp ⟨p.val, Nat.lt_of_lt_of_le p.isLt hK⟩)
        (if β₂ qB = 0 then β₂ else fanoutXorBits M wC (pSys rp) β₂) := by
      intro K; induction K with
      | zero => intros; rfl
      | succ q ihq =>
          intro hq; dsimp only [czFanoutPhase, Fin.val_last, Fin.val_castSucc]
          rw [ihq (Nat.le_of_succ_le hq), hEqη _ (hO_C ⟨q, hq⟩),
              hEqη _ (hO_disj _ (Or.inr (Or.inr (Or.inr (Or.inr ⟨⟨q, hq⟩, rfl⟩)))))]
    dsimp only; have hPhM := hPh M le_rfl; simp only [Fin.eta] at hPhM
    by_cases hwB : w = qB
    · subst hwB; rw [Function.update_self, Function.update_self, hEqη w (hO_disj w hwW), hPhM]
    · rw [Function.update_of_ne hwB, Function.update_of_ne hwB, hEqη w (hO_disj w hwW)]
/-- Complete 24-plane `bellXHalfVecDyn` step cancelling `C_vec * S_vec * R₀ ──▶ R₀` in `0 T`. -/
theorem subspaceStep_bellXHalfVec_portSwap {Var : Type} [Fintype Var] [DecidableEq Var]
    {M D n : ℕ} (v : Var) (r : RouterReg M D n)
    (qB : Fin 24 → Wire n) (wC : Fin M → Wire n)
    (hB_inj : ∀ k₁ k₂, k₁ ≠ k₂ → qB k₁ ≠ qB k₂)
    (hB_mod : ∀ k, PlaneModSet (planeOfRouter r k) (qB k))
    (hC_notMod : ∀ k p, ¬ PlaneModSet (planeOfRouter r k) (wC p))
    (hbc : ∀ k p, qB k ≠ wC p)
    (hbt_all : ∀ k₁ k₂ p, qB k₁ ≠ pSys (planeOfRouter r k₂) p)
    (hc_disj : ∀ k p q, wC p ≠ pSys (planeOfRouter r k) q)
    (R₀ : Operator (2 ^ n))
    (hSupp : SupportedOn (fun δ ↦ AtMostOneCtrl wC δ ∧ ∀ k : Fin 24, δ (qB k) = 0) R₀) :
    SubspaceStep (Var := Var)
      ((specFanoutCopyVecCirc M 24 qB wC (fun k p ↦ pSys (planeOfRouter r k) p)
          hbc (fun k ↦ hbt_all k k) (fun k p ↦ hc_disj k p p)).eval.1 *
        ((portSwapVecCirc M 24 qB wC (fun k p ↦ pSys (planeOfRouter r k) p)
          hbc (fun k ↦ hbt_all k k) (fun k p ↦ hc_disj k p p)).eval.1 * R₀))
      R₀
      (bellXHalfVecDyn v M 24 qB wC (fun k p ↦ pSys (planeOfRouter r k) p)
        (fun k p ↦ hc_disj k p p)) := by
  let rs := planeOfRouter r
  let s1 (j : Fin 24) :=
      portSwap1Circ M (qB j) wC (pSys (rs j)) (hbc j) (hbt_all j j) (fun p ↦ hc_disj j p p)
  let u1 (j : Fin 24) :=
      specPortUnextract1Unitary M (qB j) wC (pSys (rs j)) (hbc j) (hbt_all j j)
      (fun p ↦ hc_disj j p p)
  have ht_disj : ∀ k₁ k₂, k₁ ≠ k₂ → ∀ p q, pSys (rs k₁) p ≠ pSys (rs k₂) q := fun k₁ k₂ hne p q e ↦
    planeModDisj r hne _ (Or.inr (Or.inr (Or.inr (Or.inr ⟨p, rfl⟩))))
      (e ▸ Or.inr (Or.inr (Or.inr (Or.inr ⟨q, rfl⟩))))
  let Pinv : (Fin 24 → Prop) → BitAssignment n → Prop := fun Q δ ↦
      AtMostOneCtrl wC δ ∧ ∀ k : Fin 24, Q k → δ (qB k) = 0
  have hS1Keep : ∀ (j : Fin 24) {Q : Fin 24 → Prop}, ¬ Q j → ∀ δ, Pinv Q δ →
      PreservesKetPred (Pinv Q) ((s1 j).eval.1.mulVec (ket δ)) := by
    intro j Q hnj δ ⟨h1, hq⟩
    dsimp only [s1]; rw [portSwap1Circ_mulVec_ket, ket_sr_eq]
    have opS := planeSwap1_localKetOp (rs j) (qB j) wC (hbc j) (hbt_all j j) (fun p ↦ hc_disj j p p)
        (hB_mod j) (fun _ ↦ False) (fun _ _ h ↦ h) (fun _ h ↦ h)
    have hC (p : Fin M) := opS.2.1 δ _ (hC_notMod j p)
    exact preservesKetPred_ket
      ⟨h1.elim (fun hz ↦ .inl fun p ↦ (hC p).trans (hz p))
        (fun ⟨p₀, hp1, hp0⟩ ↦ .inr ⟨p₀, (hC p₀).trans hp1, fun p hp ↦ (hC p).trans (hp0 p hp)⟩),
       fun k hk ↦ (opS.2.1 δ (qB k) fun hm ↦
         planeModDisj r (fun e : j = k ↦ hnj (e ▸ hk)) _ hm (hB_mod k)).trans (hq k hk)⟩
  have hPreS : ∀ (q : ℕ) (hq : q ≤ 24) (jq : Fin 24) (_hle : q ≤ jq.val) {δ : BitAssignment n},
      AtMostOneCtrl wC δ → (∀ k : Fin 24, δ (qB k) = 0) → PreservesKetPred (Pinv (fun k ↦ k = jq))
      ((portSwapVecCirc M q (fun i ↦ qB ⟨i.val, Nat.lt_of_lt_of_le i.isLt hq⟩) wC (fun i p ↦
      pSys (rs ⟨i.val, Nat.lt_of_lt_of_le i.isLt hq⟩) p) (fun _ ↦ hbc _) (fun _ ↦ hbt_all _ _)
      (fun _ p ↦ hc_disj _ p p)).eval.1.mulVec (ket δ)) := by
    intro q; induction q with
    | zero =>
        intro _ jq _ δ h1 hq0; dsimp only [portSwapVecCirc];
        rw [Circuit.eval_identity, Submonoid.coe_one, Matrix.one_mulVec]
        exact preservesKetPred_ket ⟨h1, fun _ hk ↦ hk ▸ hq0 jq⟩
    | succ q' ihq' =>
        intro hq jq hle δ h1 hq0
        dsimp only [portSwapVecCirc, Fin.val_last, Fin.val_castSucc]; rw [eval_seq_mulVec]
        exact preservesKetPred_mulVec_of_ket
          (hS1Keep ⟨q', hq⟩ (fun e ↦ by have := congrArg Fin.val e; dsimp at this; omega))
          (ihq' (Nat.le_of_succ_le hq) jq (Nat.le_of_succ_le hle) h1 hq0)
  have hCancelAt (q : ℕ) (hq : q < 24) {δ : BitAssignment n} (h1 : AtMostOneCtrl wC δ)
      (hq0 : ∀ k : Fin 24, δ (qB k) = 0) :=
    let jq : Fin 24 := ⟨q, hq⟩
    let hPre := hPreS q (Nat.le_of_succ_le hq) jq le_rfl h1 hq0
    And.intro hPre (hPre ((u1 jq).1 * (s1 jq).eval.1) 1 fun α ⟨h1α, h0α⟩ ↦ by
      simpa only [← Matrix.mulVec_mulVec, Matrix.one_mulVec] using
        unextract1_portSwap1_ket (rs jq) (qB jq) wC
          (hbc jq) (hbt_all jq jq) (hc_disj jq) h1α (h0α jq rfl))
  have hCleanUk : ∀ (k₀ : Fin 24) (m : ℕ) (hm : m ≤ 24) (_hk₀ : k₀.val < m) {δ : BitAssignment n},
      AtMostOneCtrl wC δ → (∀ k : Fin 24, δ (qB k) = 0) → PreservesKetPred (fun η ↦ η (qB k₀) = 0)
      ((u1 k₀).1.mulVec ((portSwapVecCirc M m (fun i ↦
      qB ⟨i.val, Nat.lt_of_lt_of_le i.isLt hm⟩) wC (fun i p ↦
      pSys (rs ⟨i.val, Nat.lt_of_lt_of_le i.isLt hm⟩) p) (fun _ ↦ hbc _) (fun _ ↦ hbt_all _ _)
      (fun _ p ↦ hc_disj _ p p)).eval.1.mulVec (ket δ))) := by
    intro k₀ m; induction m with
    | zero => intro _ hk₀; exact absurd hk₀ (Nat.not_lt_zero _)
    | succ q ihq =>
        intro hq hk₀ δ h1 hq0; let jq : Fin 24 := ⟨q, hq⟩
        dsimp only [portSwapVecCirc, Fin.val_last, Fin.val_castSucc]; rw [eval_seq_mulVec]
        by_cases hEq : jq = k₀
        · subst hEq
          obtain ⟨hPre, hCancelLast⟩ := hCancelAt q hq h1 hq0
          rw [Matrix.mulVec_mulVec, hCancelLast, Matrix.one_mulVec]
          exact preservesKetPred_mono (fun _ h ↦ h.2 jq rfl) hPre
        · have hlt : k₀.val < q :=
            Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hk₀) fun e ↦ hEq (Fin.ext e.symm)
          have hComm : (u1 k₀).1 * (s1 jq).eval.1 = (s1 jq).eval.1 * (u1 k₀).1 :=
              localKetOp_comm (fun u hk hj ↦ planeModDisj r hEq u hj hk)
              (planeUnextract1_localKetOp (rs k₀) (qB k₀) wC (hbc k₀) (hbt_all k₀ k₀)
              (fun p ↦ hc_disj k₀ p p) (hB_mod k₀) (PlaneModSet (rs jq))
              (fun u hk hu ↦ planeModDisj r hEq u hu hk) (hC_notMod jq))
              (planeSwap1_localKetOp (rs jq) (qB jq) wC (hbc jq) (hbt_all jq jq)
              (fun p ↦ hc_disj jq p p) (hB_mod jq) (PlaneModSet (rs k₀))
              (fun u hj hu ↦ planeModDisj r hEq u hj hu) (hC_notMod k₀))
          rw [Matrix.mulVec_mulVec, hComm, ← Matrix.mulVec_mulVec]
          have opJ :=
              planeSwap1_localKetOp (rs jq) (qB jq) wC (hbc jq) (hbt_all jq jq)
              (fun p ↦ hc_disj jq p p) (hB_mod jq) (fun _ ↦ False) (fun _ _ h ↦ h) (fun _ h ↦ h)
          exact preservesKetPred_mulVec_of_ket
            (fun α hα ↦ by
              dsimp only [s1]; rw [portSwap1Circ_mulVec_ket, ket_sr_eq]
              exact preservesKetPred_ket
                ((opJ.2.1 α (qB k₀) (fun hm ↦ planeModDisj r hEq _ hm (hB_mod k₀))).trans hα))
            (ihq (Nat.le_of_succ_le hq) hlt h1 hq0)
  have hCancelVec : ∀ (m : ℕ) (hm : m ≤ 24) {δ : BitAssignment n}, AtMostOneCtrl wC δ →
      (∀ k : Fin 24, δ (qB k) = 0) →
      ((specPortUnextractVecUnitary M m (fun i ↦
      qB ⟨i.val, Nat.lt_of_lt_of_le i.isLt hm⟩) wC (fun i p ↦
      pSys (rs ⟨i.val, Nat.lt_of_lt_of_le i.isLt hm⟩) p) (fun _ ↦ hbc _) (fun _ ↦ hbt_all _ _)
      (fun _ p ↦ hc_disj _ p p)).1 *
      (portSwapVecCirc M m (fun i ↦ qB ⟨i.val, Nat.lt_of_lt_of_le i.isLt hm⟩) wC (fun i p ↦
      pSys (rs ⟨i.val, Nat.lt_of_lt_of_le i.isLt hm⟩) p) (fun _ ↦ hbc _) (fun _ ↦ hbt_all _ _)
      (fun _ p ↦ hc_disj _ p p)).eval.1).mulVec (ket δ) = ket δ := by
    intro m; induction m with
    | zero =>
        intro _ _ _ _; dsimp only [specPortUnextractVecUnitary, portSwapVecCirc];
        simp only [Circuit.eval_identity, Submonoid.coe_one, one_mul, Matrix.one_mulVec]
    | succ q ihq =>
        intro hq _ h1 hq0
        have hCancelLast := (hCancelAt q hq h1 hq0).2
        dsimp only [specPortUnextractVecUnitary, portSwapVecCirc, Fin.val_last, Fin.val_castSucc];
        simp only [Circuit.eval_seq, Submonoid.coe_mul, ← Matrix.mulVec_mulVec] at hCancelLast ⊢;
        rw [hCancelLast];
        simpa only [Matrix.one_mulVec,
            ← Matrix.mulVec_mulVec] using ihq (Nat.le_of_succ_le hq) h1 hq0
  let SV :=
      (portSwapVecCirc M 24 qB wC (fun k p ↦ pSys (rs k) p) hbc (fun k ↦ hbt_all k k)
      (fun k p ↦ hc_disj k p p)).eval.1
  have hStep := subspaceStep_bellXHalfVec v M 24 qB wC (fun k p ↦ pSys (rs k) p)
    hB_inj hbc hbt_all hc_disj ht_disj (SV * R₀)
    (fun k ↦ by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.mul_assoc]
      refine hSupp _ _ (fun δ ⟨h1, hq0⟩ ↦ ?_)
      simp only [← Matrix.mulVec_mulVec]
      simpa only [Fin.eta, Matrix.one_mulVec] using
        (hCleanUk k 24 le_rfl k.isLt h1 hq0)
          ((QRegister.singleton (qB k)).basisOutcomeProjector 0) 1
          (fun η hη ↦ by rw [ket_projector_zero, itePos hη, Matrix.one_mulVec]))
  refine subspaceStep_congr_out hStep ?_; rw [← Matrix.mul_assoc]
  exact (hSupp _ 1 (fun δ ⟨h1, hq0⟩ ↦ by
    rw [Matrix.one_mulVec]
    simpa only [Fin.eta] using hCancelVec 24 le_rfl h1 hq0)).trans (Matrix.one_mul R₀)
/-! ## Part D1: Disjoint Swap/Bell Commutation & Single-Port Unload Theorem -/

theorem comm_cnot_H_disj {n : ℕ} {c t q : Wire n} (hct : c ≠ t) (hqc : q ≠ c)
    (hqt : q ≠ t) : (Circuit.CNOT c t hct).eval.1 * (Circuit.H q).eval.1 = (Circuit.H q).eval.1 *
    (Circuit.CNOT c t hct).eval.1 :=
  localKetOp_comm_H (W := fun w ↦ w = t) (O := fun w ↦ w ≠ c ∧ w ≠ t)
    (F := fun β ↦ Function.update β t (β t + β c)) ⟨hqc, hqt⟩ hqt
    ⟨fun β ↦ by rw [ket_sr_eq, ket_CNOT, ← ket_sr_eq],
     fun _ _ hw ↦ Function.update_of_ne hw _ _,
     fun β₁ β₂ hEq _ hw ↦ by
       subst hw; dsimp only
       rw [Function.update_self, Function.update_self,
           hEq _ fun h ↦ h.2 rfl, hEq c fun h ↦ h.1 rfl]⟩
theorem actsIndepOf_cnot_disj {n : ℕ} {S : Wire n → Prop} {c t : Wire n} (hct : c ≠ t) (hc : ¬ S c)
    (ht : ¬ S t) : ActsIndepOf S (Circuit.CNOT c t hct).eval :=
  ⟨fun β ↦ Function.update β t (β t + β c),
   fun β ↦ by rw [ket_sr_eq, ket_CNOT, ← ket_sr_eq],
   fun _ hu _ _ ↦ by
     dsimp only
     rw [Function.update_of_ne (by rintro rfl; exact ht hu),
         Function.update_of_ne (by rintro rfl; exact hc hu),
         Function.update_comm (by rintro rfl; exact ht hu)]⟩
end QuantumComputation.Specs.PhotochemistrySolution.SplitRouter47_187

namespace QuantumComputation.Specs.PhotochemistrySolution.Stage2ZeroGated
open Circuit Qubit PhotochemistrySolution.SplitRouter47_187
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
attribute [local semireducible] ComputeProg.fwdBits
theorem cond_nat_beq {α : Type} (a b : ℕ) (u v : α) : cond (Nat.beq a b) u v = if a =
    b then u else v := by
  cases hb : Nat.beq a b
  · exact (ite_eq_right fun e ↦ Bool.noConfusion ((Nat.beq_refl b).symm.trans (e ▸ hb))).symm
  · exact (ite_eq_left (Nat.eq_of_beq_eq_true hb)).symm
theorem cond_wire_beq {n : ℕ} {α : Type} (w₁ w₂ : Wire n)
    (u v : α) : cond (Nat.beq w₁.val w₂.val) u v = if w₁ = w₂ then u else v :=
  (cond_nat_beq w₁.val w₂.val u v).trans
    (PhotochemistrySolution.SortedRouterSpec.ite_iff_eq ⟨Fin.ext, congrArg Fin.val⟩ u v)
/--
Public control wire set `{rHas1, rRawHas2, rIdx1[0..D), rIdx2[0..D)}`
(`u.val < 2 + 2 * D`).
-/
def PubCtrlSet {M D n : ℕ} (r : RouterReg M D n) (w : Wire n) : Prop :=
    ∃ u : Fin (routerWidth M D), u.val < 2 + 2 * D ∧ w = r u
theorem pubCtrlSet_roles {M D n : ℕ} (r : RouterReg M D n) : PubCtrlSet r (rHas1 r) ∧
    PubCtrlSet r (rRawHas2 r) ∧ (∀ d : Fin D, PubCtrlSet r (rIdx1 r d)) ∧
    (∀ d : Fin D, PubCtrlSet r (rIdx2 r d)) :=
  ⟨⟨_, by dsimp [routerWidth]; omega, rfl⟩, ⟨_, by dsimp [routerWidth]; omega, rfl⟩,
   fun d ↦ ⟨_, by cases d; dsimp [routerWidth]; omega, rfl⟩,
   fun d ↦ ⟨_, by cases d; dsimp [routerWidth]; omega, rfl⟩⟩
theorem not_allPlaneMod_of_pubCtrlSet {M D n : ℕ} {r : RouterReg M D n} {w : Wire n}
    (hw : PubCtrlSet r w) : ¬ AllPlaneMod r w :=
  let ⟨_, hu, h⟩ := hw
  h ▸ not_allPlaneMod_of_idx r (Or.inl hu)
theorem fwdBits_congr_on_supp {n : ℕ} (p : ComputeProg n) {Q : Wire n → Prop}
    (hp : ProgSupportedIn Q p) {γ₁ γ₂ : BitAssignment n} (hEq : ∀ w, Q w → γ₁ w = γ₂ w) : ∀ w, Q w →
    p.fwdBits γ₁ w = p.fwdBits γ₂ w := by
  have upd {a b : BitAssignment n} (hab : ∀ u, Q u → a u = b u) (t : Wire n) {v₁ v₂ : ZMod 2}
      (hv : v₁ = v₂) (w : Wire n) (hw : Q w) :
      Function.update a t v₁ w = Function.update b t v₂ w := by
    exact (eq_or_ne w t).elim (fun h ↦ by simp [h, hv]) fun h ↦ by simp [h, hab w hw]
  induction p generalizing γ₁ γ₂ with
  | id => exact hEq
  | x tgt => exact upd hEq tgt (by rw [hEq _ hp])
  | cnot _ tgt _ => exact upd hEq tgt (by rw [hEq _ hp.2, hEq _ hp.1])
  | andGate _ _ tgt _ _ _ => exact upd hEq tgt (by rw [hEq _ hp.2.2, hEq _ hp.1, hEq _ hp.2.1])
  | seq _ _ ih₁ ih₂ => exact ih₂ hp.2 (ih₁ hp.1 hEq)
/-- Computable `Bool`-equality vector toggle flipping `wVec p` by `delta p` across `p < k`. -/
def vecToggleLoop {M n : ℕ} (wVec : Fin M → Wire n) (delta : Fin M → ZMod 2)
    (α : BitAssignment n) : (k : ℕ) → k ≤ M → BitAssignment n
  | 0, _, w => α w
  | k + 1, hk, w =>
      let prev := vecToggleLoop wVec delta α k (Nat.le_of_succ_le hk); let pk : Fin M := ⟨k, hk⟩
      cond (Nat.beq w.val (wVec pk).val) (prev w + delta pk) (prev w)
/-- Computable vector toggle flipping `wVec p` by `delta α p` across `0 .. M - 1`. -/
def vecToggleBits {M n : ℕ} (wVec : Fin M → Wire n) (delta : BitAssignment n → Fin M → ZMod 2)
    (α : BitAssignment n) : BitAssignment n := vecToggleLoop wVec (delta α) α M le_rfl
theorem vecToggleLoop_spec {M n : ℕ} (wVec : Fin M → Wire n)
    (hInj : ∀ p q : Fin M, p ≠ q → wVec p ≠ wVec q)
    (delta : Fin M → ZMod 2) (α : BitAssignment n) :
    ∀ (k : ℕ) (hk : k ≤ M),
      (∀ p : Fin M, vecToggleLoop wVec delta α k hk (wVec p) =
        α (wVec p) + if p.val < k then delta p else 0) ∧
      (∀ w : Wire n, (∀ p : Fin M, w ≠ wVec p) →
        vecToggleLoop wVec delta α k hk w = α w)
  | 0, _ =>
      ⟨fun p ↦ by rw [ite_eq_right (Nat.not_lt_zero p.val), add_zero]; rfl,
       fun _ _ ↦ rfl⟩
  | k + 1, hk => by
      obtain ⟨ih1, ih2⟩ := vecToggleLoop_spec wVec hInj delta α k (Nat.le_of_succ_le hk);
      let pk : Fin M := ⟨k, hk⟩
      refine ⟨fun p ↦ ?_, fun w hw ↦ ?_⟩
      · dsimp only [vecToggleLoop]; rw [cond_wire_beq]
        by_cases hp : p = pk
        · subst hp; dsimp only [pk]
          rw [ite_eq_left rfl, ih1 ⟨k, hk⟩, ite_eq_right (Nat.lt_irrefl k),
              ite_eq_left (Nat.lt_succ_self k), add_zero]
        · rw [ite_eq_right (hInj p pk hp), ih1 p]
          exact congrArg (α (wVec p) + ·)
            (PhotochemistrySolution.SortedRouterSpec.ite_iff_eq
              (by have : p.val ≠ k := fun e ↦ hp (Fin.ext e); omega) _ _)
      · dsimp only [vecToggleLoop]; rw [cond_wire_beq, ite_eq_right (hw pk), ih2 w hw]
theorem vecToggleBits_spec {M n : ℕ} (wVec : Fin M → Wire n) (hInj : ∀ p q : Fin M, p ≠ q → wVec p ≠
    wVec q) (delta : BitAssignment n → Fin M → ZMod 2) (α : BitAssignment n) :
    (∀ p : Fin M, vecToggleBits wVec delta α (wVec p) = α (wVec p) + delta α p) ∧
    (∀ w : Wire n, (∀ p : Fin M, w ≠ wVec p) → vecToggleBits wVec delta α w = α w) :=
  ⟨fun p ↦ ((vecToggleLoop_spec wVec hInj (delta α) α M le_rfl).1 p).trans
     (by rw [ite_eq_left p.isLt]),
   (vecToggleLoop_spec wVec hInj (delta α) α M le_rfl).2⟩
theorem vecToggleBits_involutive {M n : ℕ} (wVec : Fin M → Wire n)
    (hInj : ∀ p q : Fin M, p ≠ q → wVec p ≠ wVec q) (delta : BitAssignment n → Fin M → ZMod 2)
    (hIndep : ∀ α₁ α₂, (∀ w, (∀ p, w ≠ wVec p) → α₁ w = α₂ w) → delta α₁ = delta α₂)
    (α : BitAssignment n) : vecToggleBits wVec delta (vecToggleBits wVec delta α) = α := by
  let β := vecToggleBits wVec delta α;
  have hd : delta β = delta α := hIndep β α (vecToggleBits_spec wVec hInj delta α).2; funext w
  by_cases hw : ∃ p : Fin M, w = wVec p
  · rcases hw with ⟨p, rfl⟩
    rw [(vecToggleBits_spec wVec hInj delta β).1 p, hd]; dsimp only [β];
    rw [(vecToggleBits_spec wVec hInj delta α).1 p, add_assoc, CharTwo.add_self_eq_zero, add_zero]
  · have hnw : ∀ p : Fin M, w ≠ wVec p := fun p e ↦ hw ⟨p, e⟩
    exact ((vecToggleBits_spec wVec hInj delta β).2 w hnw).trans ((vecToggleBits_spec wVec hInj
        delta α).2 w hnw)
/-- Unitary toggling `wVec p` by `delta α p` for read-disjoint `delta`. -/
def uVecToggle {M n : ℕ} (wVec : Fin M → Wire n) (hInj : ∀ p q : Fin M, p ≠ q → wVec p ≠ wVec q)
    (delta : BitAssignment n → Fin M → ZMod 2) (hIndep : ∀ α₁ α₂, (∀ w, (∀ p, w ≠ wVec p) → α₁ w =
    α₂ w) → delta α₁ = delta α₂) : Unitary (2 ^ n) :=
    unitaryOfBitsInv (vecToggleBits wVec delta) (vecToggleBits_involutive wVec hInj delta hIndep)
theorem uVecToggle_mulVec_ket {M n : ℕ} (wVec : Fin M → Wire n)
    (hInj : ∀ p q : Fin M, p ≠ q → wVec p ≠ wVec q) (delta : BitAssignment n → Fin M → ZMod 2)
    (hIndep : ∀ α₁ α₂, (∀ w, (∀ p, w ≠ wVec p) → α₁ w = α₂ w) → delta α₁ = delta α₂)
    (α : BitAssignment n) : (uVecToggle wVec hInj delta hIndep).1.mulVec (ket α) =
    ket (vecToggleBits wVec delta α) := unitaryOfBitsInv_mulVec_ket _ _ α
theorem uVecToggle_sq_eq_one {M n : ℕ} (wVec : Fin M → Wire n)
    (hInj : ∀ p q : Fin M, p ≠ q → wVec p ≠ wVec q) (delta : BitAssignment n → Fin M → ZMod 2)
    (hIndep : ∀ α₁ α₂, (∀ w, (∀ p, w ≠ wVec p) → α₁ w = α₂ w) → delta α₁ = delta α₂) :
    (uVecToggle wVec hInj delta hIndep).1 * (uVecToggle wVec hInj delta hIndep).1 = 1 := by
  let _ : NeZero (2 ^ n) := ⟨pow_ne_zero n two_ne_zero⟩
  apply matrix_ext_ket; intro α
  rw [← Matrix.mulVec_mulVec, Matrix.one_mulVec, uVecToggle_mulVec_ket, uVecToggle_mulVec_ket,
      vecToggleBits_involutive wVec hInj delta hIndep]
theorem actsIndepOf_uVecToggle {M n : ℕ} {S : Wire n → Prop} (wVec : Fin M → Wire n)
    (hInj : ∀ p q : Fin M, p ≠ q → wVec p ≠ wVec q) (delta : BitAssignment n → Fin M → ZMod 2)
    (hIndep : ∀ α₁ α₂, (∀ w, (∀ p, w ≠ wVec p) → α₁ w = α₂ w) → delta α₁ = delta α₂)
    (hSDisj : ∀ w, S w → ∀ p, w ≠ wVec p)
    (hSDelta : ∀ w, S w → ∀ α val, delta (Function.update α w val) = delta α) :
    ActsIndepOf S (uVecToggle wVec hInj delta hIndep) :=
  ⟨vecToggleBits wVec delta,
   fun δ ↦ by rw [ket_sr_eq, uVecToggle_mulVec_ket, ← ket_sr_eq],
   fun q hq α val ↦ by
     funext w
     by_cases hw : ∃ p : Fin M, w = wVec p
     · rcases hw with ⟨p, rfl⟩
       rw [(vecToggleBits_spec wVec hInj delta _).1 p, hSDelta q hq α val,
           Function.update_of_ne (hSDisj q hq p).symm, Function.update_of_ne (hSDisj q hq p).symm,
           (vecToggleBits_spec wVec hInj delta α).1 p]
     · have hnw (p : Fin M) : w ≠ wVec p := fun e ↦ hw ⟨p, e⟩
       rw [(vecToggleBits_spec wVec hInj delta _).2 w hnw]
       exact (eq_or_ne w q).elim (fun h ↦ by simp [h]) fun h ↦ by
         simp [h, (vecToggleBits_spec wVec hInj delta α).2 w hnw]⟩
end QuantumComputation.Specs.PhotochemistrySolution.Stage2ZeroGated
end

end ScopedLocalHelpers
end
