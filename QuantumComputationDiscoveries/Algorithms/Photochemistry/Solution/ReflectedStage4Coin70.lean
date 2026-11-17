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

public import QuantumComputationDiscoveries.Algorithms.Photochemistry.Solution.Stage2ZeroGatedPotPortB

set_option allowUnsafeReducibility true
open QuantumComputation.Specs.PhotochemistrySolution.SpecDefs
open QuantumComputation.Specs.PhotochemistrySolution.QhlAux
open QuantumComputation.Specs.PhotochemistrySolution.PgBase
open QuantumComputation.Specs.PhotochemistrySolution.SelectBase
@[expose] public section
set_option exponentiation.threshold 256

noncomputable section
set_option autoImplicit false
namespace QuantumComputation.Specs.PhotochemistrySolution.PotSelectWiring

open Operator QProg Matrix Circuit Qubit QuantumComputation.Specs PhotochemistrySolution.KetSupport
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
open PhotochemistrySolution PhotochemistrySolution.SplitRouter47_187
  PhotochemistrySolution.SelectOracles PhotochemistrySolution.RouterSelectWiringA
open PhotochemistrySolution.RouterSelectWiringB PhotochemistrySolution.Stage12Compact
  PhotochemistrySolution.ZeroNEremSpec
open _root_.DynamicCircuit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt hiding ket matrix_ext_ket
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SelectCompactAnc (ancWOfScr)
open scoped Matrix BigOperators
set_option allowUnsafeReducibility true in
attribute [local irreducible] systemQubits_frozen ancWOfScr PgBase.phaseGradientState
theorem rSys_nuc_eq_sysCoord (p : Fin 47) (ax : Fin 3) (k : Fin 8) : rSys rNucLayout p ⟨8 *
    ax.val + k.val, coord24_lt ax k⟩ =
    rSysLayout ((coordinateRegister_frozen (nucParticle p) ax) k) := by
  refine Fin.ext ?_; change (nucRouterWireFn ⟨98 + 2 * 6 + 24 * p.val + (8 * ax.val + k.val),
      _⟩).val = _
  rw [val_nucRouterWireFn, val_rSysLayout]; dsimp [coordinateRegister_frozen, nucParticle,
    gridBits_frozen, QRegister.block, Fin.natAddEmb, Fin.natAdd, DFunLike.coe,
    -Function.Embedding.toFun_eq_coe]; split_ifs <;> omega
theorem rSys_elec_eq_sysCoord (p : Fin 187) (ax : Fin 3) (k : Fin 8) : rSys rElecLayout p ⟨8 *
    ax.val + k.val, coord24_lt ax k⟩ =
    rSysLayout ((coordinateRegister_frozen (elecParticle p) ax) k) := by
  refine Fin.ext ?_; change (elecRouterWireFn ⟨98 + 2 * 8 + 24 * p.val + (8 * ax.val + k.val),
      _⟩).val = _
  rw [val_elecRouterWireFn, val_rSysLayout]; dsimp [coordinateRegister_frozen, elecParticle,
    gridBits_frozen, QRegister.block, Fin.natAddEmb, Fin.natAdd, DFunLike.coe,
    -Function.Embedding.toFun_eq_coe]; split_ifs <;> omega
theorem rSC_wire_lt_5616 (i : Particle_frozen) (ax : Fin 3)
    (b : Fin 8) : ((rSysLayout.compose (coordinateRegister_frozen i ax)) b).val < 5616 := by
  change (rSysLayout ((coordinateRegister_frozen i ax) b)).val < 5616; rw [val_rSysLayout]
  exact lt_of_lt_of_eq ((coordinateRegister_frozen i ax) b).isLt hSys5616
theorem packOut40_kin (i : Particle_frozen) (ax : Fin 3) (δ : BitAssignment dLayout)
    (hOut : ∀ j : Fin 40, δ (rOut40Layout j) = outMaskBits40 (.kin i ax) j) :
    δ (rHas1 rNucLayout) = (if i.val < 47 then 1 else 0) ∧ δ (rRawHas2 rNucLayout) = 0 ∧
        idxValD (rIdx1 rNucLayout) δ =
      (if i.val < 47 then i.val else 0) ∧
    δ (rHas1 rElecLayout) = (if i.val < 47 then 0 else 1) ∧ δ (rRawHas2 rElecLayout) = 0 ∧
        idxValD (rIdx1 rElecLayout) δ =
      (if i.val < 47 then 0 else i.val - 47) ∧
    δ wIsFine = 0 ∧ δ wIsKin = 1 ∧ δ wAxis0 = (if ax.val.testBit 0 then 1 else 0) ∧ δ wAxis1 =
      (if ax.val.testBit 1 then 1 else 0) := by
  have hi234 := i.isLt
  obtain ⟨f1, f2, f3, _, f5, f6, f7, _, _, f10, f11, _, _, _, f15, f16⟩ :=
    packOut40ZeroNErem_fields (decide (i.val < 47)) false (if i.val < 47 then i.val else 0) 0
      (decide ¬(i.val < 47)) false (if i.val < 47 then 0 else i.val -
          47) 0 false false true false 0 ax.val
      (by split_ifs <;> omega) (by omega) (by split_ifs <;> omega) (by omega) δ fun m ↦
          (hOut m).trans
        (by by_cases hi : i.val < 47 <;> simp [outMaskBits40, zeroNEremOutMask, hi])
  by_cases hi : i.val < 47 <;> simp only [hi, not_true_eq_false, not_false_eq_true, decide_true,
      decide_false, ↓reduceIte] at * <;>
    exact ⟨f1, f2, f3, f5, f6, f7, f10, f11, f15, f16⟩
theorem postSp_kin_readout {decodeCoin : Fin (2 ^ 41) → ZeroNEremSector} {c : Fin (2 ^ 41)}
    {i : Particle_frozen}
    {ax : Fin 3} (hc : decodeCoin c = .kin i ax)
    (α : BitAssignment dLayout) (hSA : ∀ m, α (rScrLayout m) = 0) (z : BitAssignment 41) :
    let σ := speciesSwapBits (pKinAlign0.fwdBits (routedKet decodeCoin α c z))
    σ wKinAxis0 = (if ax.val.testBit 0 then 1 else 0) ∧ σ wKinAxis1 =
        (if ax.val.testBit 1 then 1 else 0) ∧ σ (rWorkInnerLayout
      ⟨21, fin21_lt_521⟩) = 0 ∧
    (∀ (a : Fin 3) (b : Fin 8), σ (rBufLo rNucLayout ⟨8 * a.val + b.val, coord24_lt a b⟩) =
        α (rSysLayout
      ((coordinateRegister_frozen i a) b))) := by
  intro σ
  let δ := routedKet decodeCoin α c z
  let η := pKinAlign0.fwdBits δ
  obtain ⟨hVN, hKeepE, hVE, _, hLoN, _⟩ := validRouter_stage1 (decodeCoin := decodeCoin) hSA c z
  obtain ⟨kSN, kSE⟩ := routedBuf_keep_stage1 (decodeCoin := decodeCoin) hSA c z
  obtain ⟨_, _, _, f0HE1, _, _, _, _, f0Ax0, f0Ax1⟩ := packOut40_kin i ax δ
    fun m ↦ (routedKet_out40 hSA c z m).trans (by rw [hc])
  obtain ⟨f1HN1, f1RN2, f1IN1, f1HE1, f1RE2, f1IE1, _, _, _, _⟩ := packOut40_kin i ax
    (routedStage1 decodeCoin α c z) fun m ↦
        (writeReg_apply_reg _ rOut40Layout _ m).trans (by rw [hc])
  have hAl0 := routedKet_align_zero (decodeCoin := decodeCoin) hSA c z
  have ⟨_, hAx0, hAx1, _, hEK⟩ := s5k_ax δ (hAl0 ⟨109, by omega⟩) (hAl0 ⟨110, by omega⟩)
    (hAl0 ⟨135, by omega⟩) (hAl0 ⟨111, by omega⟩)
  obtain ⟨hW21v, hAx0v, hAx1v⟩ : _ ∧ wKinAxis0.val = 5947 + 109 ∧ wKinAxis1.val = 5947 + 110 :=
    ⟨val_rWorkInnerLayout ⟨21, fin21_lt_521⟩, val_rAlignLayout _, val_rAlignLayout _⟩
  refine ⟨(speciesSwapBits_outside η (by omega) (by omega)).trans (hAx0.trans f0Ax0),
    (speciesSwapBits_outside η (by omega) (by omega)).trans (hAx1.trans f0Ax1),
    (speciesSwapBits_outside η (by omega)
        (by omega)).trans ((fwdBits_not_target targetsIn_pKinAlign0 δ
      (by omega)).trans (routedKet_workInner hSA c z ⟨21, fin21_lt_521⟩)), fun a b ↦ ?_⟩
  have hi234 := i.isLt; dsimp only [σ]
  by_cases hi : i.val < 47
  · let ni : Fin 47 := ⟨i.val, hi⟩
    have hbN := (val_rBufLo_hi_nuc ⟨8 * a.val + b.val, coord24_lt a b⟩).1
    obtain ⟨sLo, _⟩ :=
      (routerSwapBits_cases rNucLayout hVN).2.1 ni (f1HN1.trans (ite_eq_left hi)) f1RN2
        (f1IN1.trans (ite_eq_left hi))
    rw [speciesSwapBits_bufLo_nuc, show pKinAlign0.fwdBits δ wIsElecKin = 0 from hEK.trans
      (rElec_header_eq_out40.1 ▸ f0HE1.trans (ite_eq_left hi)), ite_eq_right zero_ne_one]
    exact (fwdBits_not_target targetsIn_pKinAlign0 δ (by omega)).trans ((hLoN _).trans
        ((sLo _).trans
      ((kSN ni _).trans (congrArg α ((rSys_nuc_eq_sysCoord ni a b).trans
        (by rw [show nucParticle ni = i from Fin.ext rfl]))))))
  · let ei : Fin 187 := ⟨i.val - 47, by omega⟩
    have hei : elecParticle ei = i := Fin.ext (by dsimp only [ei, elecParticle]; omega)
    have hbE := (val_rBufLo_hi ⟨8 * a.val + b.val, coord24_lt a b⟩).1
    obtain ⟨sLo, _⟩ :=
        (routerSwapBits_cases rElecLayout hVE).2.1 ei ((hKeepE _).trans (f1HE1.trans
        (ite_eq_right hi)))
      ((hKeepE _).trans f1RE2)
          ((idxValD_elec_stage2_eq hKeepE).1.trans (f1IE1.trans (ite_eq_right hi)))
    rw [speciesSwapBits_bufLo_nuc, show pKinAlign0.fwdBits δ wIsElecKin = 1 from hEK.trans
      (rElec_header_eq_out40.1 ▸ f0HE1.trans (ite_eq_right hi)), ite_eq_left rfl]
    exact (fwdBits_not_target targetsIn_pKinAlign0 δ (by omega)).trans ((sLo _).trans
      ((kSE ei _).trans (congrArg α ((rSys_elec_eq_sysCoord ei a b).trans (hei ▸ rfl)))))
theorem writeReg_rSC_rScr (β : BitAssignment dLayout) (i : Particle_frozen) (ax : Fin 3)
    (v : BitAssignment 8)
    (m : Fin scrLLayout) :
    DynCircExt.writeReg β (rSysLayout.compose (coordinateRegister_frozen i ax)) v (rScrLayout m)
        = β (rScrLayout m) :=
  DynCircExt.writeReg_apply_of_not_mem β _ v _ fun ⟨q, hq⟩ ↦ by
    have hv :=
        congrArg Fin.val hq;
        have := rSC_wire_lt_5616 i ax q; rw [val_rScrLayout] at hv; omega
theorem outEq_kin {decodeCoin : Fin (2 ^ 41) → ZeroNEremSector}
    {β : BitAssignment dLayout} (hScr : ∀ m, β (rScrLayout m) = 0)
    {c : Fin (2 ^ 41)} {i : Particle_frozen} {ax : Fin 3} (hc : decodeCoin c = .kin i ax)
    (z : BitAssignment 41) (k : Fin 256)
    (u : Wire dLayout) (huN : ¬(5755 ≤ u.val ∧ u.val < 5779))
    (huE : ¬(5851 ≤ u.val ∧ u.val < 5875)) :
    let rSC := rSysLayout.compose (coordinateRegister_frozen i ax)
    routedKet decodeCoin β c z u =
        routedKet decodeCoin (DynCircExt.writeReg β rSC (basisBits 8 k)) c z u := by
  intro rSC
  let β₂ := writeReg β rSC (basisBits 8 k)
  have hScrK (m : Fin scrLLayout) := (writeReg_rSC_rScr β i ax (basisBits 8 k) m).trans (hScr m)
  by_cases hsc : ∃ b : Fin 8, u = rSC b
  · obtain ⟨b, rfl⟩ := hsc
    have hZero {α : BitAssignment dLayout} (hSA : ∀ m, α (rScrLayout m) = 0) :
        routedKet decodeCoin α c z (rSC b) = 0 := by
      have hSys0 {M D : ℕ} (r : RouterReg M D dLayout) {γ : BitAssignment dLayout}
          (hV : ValidRouterInput r γ)
          (hh1 : γ (rHas1 r) = 1) (hr2 : γ (rRawHas2 r) = 0) (p : Fin M) (m : Fin 24)
              (hIdx : idxValD (rIdx1 r) γ = p.val) :
          routerSwapBits r γ (rSys r p m) = 0 := by
        have heff : routerHas2Eff r γ = 0 := by unfold routerHas2Eff; simp [hr2]
        exact (routerSwapBits_spec r hV).2.2.1 p m (.inl ⟨hh1,
            by unfold routerIdxMinVal; simp [heff, hIdx]⟩)
      obtain ⟨hVN, hKE, hVE, _, _, _⟩ := validRouter_stage1 (decodeCoin := decodeCoin) hSA c z
      obtain ⟨fHN1, fRN2, fIN1, fHE1, fRE2, fIE1, _, _, _, _⟩ :=
          packOut40_kin i ax (routedStage1 decodeCoin α c z)
        fun m ↦ (writeReg_apply_reg _ rOut40Layout _ m).trans (by rw [hc])
      have hi234 := i.isLt
      by_cases hi : i.val < 47
      · let ni : Fin 47 := ⟨i.val, hi⟩
        have eu : rSC b = rSys rNucLayout ni ⟨8 * ax.val + b.val, coord24_lt ax b⟩ :=
          (rSys_nuc_eq_sysCoord ni ax b).symm
        have hlt1128 : (rSC b).val < 1128 := by
          have hv : (rSys rNucLayout ni ⟨8 * ax.val + b.val, coord24_lt ax b⟩).val = _ :=
            val_nucRouterWireFn ⟨110 + 24 * ni.val + (8 * ax.val + b.val), _⟩
          rw [eu, hv]; dsimp; split_ifs <;> omega
        have keepE : routedKet decodeCoin α c z (rSC b) = routedStage2 decodeCoin α c z (rSC b)
            :=
          routerSwapBits_outside_mod rElecLayout hVE
            (fun m e ↦ by rw [e, (val_rBufLo_hi m).1] at hlt1128; omega)
            (fun m e ↦ by rw [e, (val_rBufLo_hi m).2] at hlt1128; omega)
            (fun p m e ↦ by
              have hv : (rSys rElecLayout p m).val = _ :=
                  val_elecRouterWireFn ⟨114 + 24 * p.val + m.val, _⟩
              rw [e, hv] at hlt1128; dsimp at hlt1128; split_ifs at hlt1128 <;> omega)
        rw [keepE, eu]
        exact hSys0 rNucLayout hVN (fHN1.trans (ite_eq_left hi)) fRN2 ni _
          (fIN1.trans (ite_eq_left hi))
      · let ei : Fin 187 := ⟨i.val - 47, by omega⟩
        have hei : elecParticle ei = i := Fin.ext (by dsimp only [ei, elecParticle]; omega)
        have eu : rSC b = rSys rElecLayout ei ⟨8 * ax.val + b.val, coord24_lt ax b⟩ := by
          change rSysLayout ((coordinateRegister_frozen i ax) b) = _;
              rw [← hei, ← rSys_elec_eq_sysCoord]
        rw [eu]; exact hSys0 rElecLayout hVE ((hKE _).trans (fHE1.trans (ite_eq_right hi)))
          ((hKE ⟨1,
              rw_lt1 187 8⟩).trans fRE2) ei _ ((idxValD_elec_stage2_eq hKE).1.trans (fIE1.trans
              (ite_eq_right hi)))
    exact (hZero hScr).trans (hZero hScrK).symm
  · obtain ⟨hVN1, hKE1, hVE1, _, _, _⟩ := validRouter_stage1 (decodeCoin := decodeCoin) hScr c z
    obtain ⟨hVN2, hKE2, hVE2, _, _, _⟩ := validRouter_stage1 (decodeCoin := decodeCoin) hScrK c z
    have pk1 (α : BitAssignment dLayout) := packOut40_kin i ax (routedStage1 decodeCoin α c z)
      fun m ↦ (writeReg_apply_reg _ rOut40Layout _ m).trans (by rw [hc])
    obtain ⟨f1HN1, hF_rawN2_1, f1IN1, f1HE1, f1RE2, f1IE1, _, _, _, _⟩ := pk1 β
    obtain ⟨f2HN1, hF_rawN2_2, f2IN1, f2HE1, f2RE2, f2IE1, _, _, _, _⟩ := pk1 β₂
    have stepSwap {M D : ℕ} (r : RouterReg M D dLayout) {γ₁ γ₂ : BitAssignment dLayout}
        (hV1 : ValidRouterInput r γ₁)
        (hV2 : ValidRouterInput r γ₂) (hr1 : γ₁ (rRawHas2 r) = 0) (hr2 : γ₂ (rRawHas2 r) = 0)
        (hHas : γ₁ (rHas1 r) = γ₂ (rHas1 r)) (hIdx : idxValD (rIdx1 r) γ₁ = idxValD (rIdx1 r) γ₂)
            {q : Wire dLayout}
        (hqLo : ∀ m : Fin 24, q ≠ rBufLo r m) (hqEq : γ₁ q = γ₂ q) : routerSwapBits r γ₁ q =
            routerSwapBits r γ₂ q := by
      have heff1 : routerHas2Eff r γ₁ = 0 := by unfold routerHas2Eff; simp [hr1]
      have heff2 : routerHas2Eff r γ₂ = 0 := by unfold routerHas2Eff; simp [hr2]
      have hMin : routerIdxMinVal r γ₁ = routerIdxMinVal r γ₂ := by
        unfold routerIdxMinVal; simp [heff1, heff2, hIdx]
      by_cases hHi : ∃ m : Fin 24, q = rBufHi r m
      · obtain ⟨m, rfl⟩ := hHi
        rw [(routerSwapBits_spec r hV1).2.1 m, (routerSwapBits_spec r hV2).2.1 m,
          dite_eq_right (fun h ↦ zero_ne_one (heff1 ▸ h.1)), dite_eq_right (fun h ↦
              zero_ne_one (heff2 ▸ h.1))]
      · by_cases hAct : ∃ (p : Fin M) (m : Fin 24), q = rSys r p m ∧ γ₁ (rHas1 r) = 1 ∧ p.val =
            routerIdxMinVal r γ₁
        · obtain ⟨p, m, rfl, hh1, hpv⟩ := hAct
          exact ((routerSwapBits_spec r hV1).2.2.1 p m (.inl ⟨hh1, hpv⟩)).trans
            ((routerSwapBits_spec r hV2).2.2.1 p m (.inl ⟨hHas ▸ hh1, hMin ▸ hpv⟩)).symm
        · exact ((routerSwapBits_spec r hV1).2.2.2 q hqLo (fun m e ↦ hHi ⟨m, e⟩)
            (fun p m e ↦ ⟨fun hh1 hpv ↦ hAct ⟨p, m, e, hh1, hpv⟩, fun hh2 ↦
                absurd (heff1 ▸ hh2) zero_ne_one⟩)).trans
            (hqEq.trans ((routerSwapBits_spec r hV2).2.2.2 q hqLo (fun m e ↦ hHi ⟨m, e⟩)
              (fun p m e ↦ ⟨fun hh1 hpv ↦ hAct ⟨p, m, e, hHas.symm ▸ hh1, hMin.symm ▸ hpv⟩,
                fun hh2 ↦ absurd (heff2 ▸ hh2) zero_ne_one⟩)).symm)
    have hS1 (q : Wire dLayout) (hq : ∀ b : Fin 8, q ≠ rSC b) :
        routedStage1 decodeCoin β c z q = routedStage1 decodeCoin β₂ c z q := by
      unfold routedStage1 routedStage0
      by_cases ho : ∃ m, rOut40Layout m = q
      · obtain ⟨m, rfl⟩ := ho; rw [writeReg_apply_reg, writeReg_apply_reg]
      · rw [writeReg_apply_of_not_mem _ rOut40Layout _ q ho,
            writeReg_apply_of_not_mem _ rOut40Layout _ q ho]
        by_cases hl : ∃ m, rLcu82Layout m = q
        · obtain ⟨m, rfl⟩ := hl; rw [writeReg_apply_reg, writeReg_apply_reg]
        · dsimp only [β₂]; rw [writeReg_apply_of_not_mem _ rLcu82Layout _ q hl,
            writeReg_apply_of_not_mem _ rLcu82Layout _ q hl,
            writeReg_apply_of_not_mem β rSC _ q fun ⟨b, hb⟩ ↦ hq b hb.symm]
    have hS2 : routedStage2 decodeCoin β c z u = routedStage2 decodeCoin β₂ c z u :=
      stepSwap rNucLayout hVN1 hVN2 hF_rawN2_1 hF_rawN2_2 (f1HN1.trans f2HN1.symm)
          (f1IN1.trans f2IN1.symm)
        (fun m e ↦ huN (by rw [e, (val_rBufLo_hi_nuc m).1]; omega))
            (hS1 u fun b hb ↦ hsc ⟨b, hb⟩)
    exact stepSwap rElecLayout hVE1 hVE2 ((hKE1 ⟨1, rw_lt1 187 8⟩).trans f1RE2)
        ((hKE2 ⟨1, rw_lt1 187 8⟩).trans f2RE2)
      (((hKE1 ⟨0, rw_lt0 187 8⟩).trans f1HE1).trans ((hKE2 ⟨0, rw_lt0 187 8⟩).trans f2HE1).symm)
      (((idxValD_elec_stage2_eq hKE1).1.trans f1IE1).trans ((idxValD_elec_stage2_eq
          hKE2).1.trans f2IE1).symm)
      (fun m e ↦ huE (by rw [e, (val_rBufLo_hi m).1]; omega)) hS2
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB (ket)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.QubitizationWalkSem (sqrtHalf)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Stage4KinFull (wMux bAxisMux27
    bAxisMux27_evalS mux1Bit6_axes)
theorem kinFwdBits_kin_comm {decodeCoin : Fin (2 ^ 41) → ZeroNEremSector}
    {β : BitAssignment dLayout} (hScr : ∀ m, β (rScrLayout m) = 0)
    {c : Fin (2 ^ 41)} {i : Particle_frozen} {ax : Fin 3}
    (hc : decodeCoin c = .kin i ax) (z : BitAssignment 41) :
    let rSC := rSysLayout.compose (coordinateRegister_frozen i ax)
    (∀ b : Fin 8, kinFwdBits (routedKet decodeCoin β c z) (rPKinLayout b) = β (rSC b)) ∧
    (∀ k : Fin 256,
        DynCircExt.writeReg (kinFwdBits (routedKet decodeCoin β c z)) rPKinLayout (basisBits
        8 k) =
      kinFwdBits (routedKet decodeCoin (DynCircExt.writeReg β rSC (basisBits 8 k)) c z))
          := by
  intro rSC
  have hScrK (k : Fin 256) (m : Fin scrLLayout) :=
      (writeReg_rSC_rScr β i ax (basisBits 8 k) m).trans (hScr m)
  obtain ⟨m0, m1, m26, mPK, mBuf⟩ := mux27_wires_eq
  have mB (a : Fin 3) (n : ℕ) (b : Fin 8) (hn : n = 2 + (8 * a.val + b.val)) :=
    (congrArg (fun k ↦ rMux27Layout (wMux k)) hn).trans (mBuf a b)
  have hMuxOut (α : BitAssignment dLayout) (hSA : ∀ m, α (rScrLayout m) = 0) (b : Fin 8) :
      kinFwdBits (routedKet decodeCoin α c z) (rPKinLayout b) = α (rSC b) := by
    obtain ⟨s0, s1, s26, sBuf⟩ := postSp_kin_readout hc α hSA z
    let σ := speciesSwapBits (pKinAlign0.fwdBits (routedKet decodeCoin α c z))
    unfold kinFwdBits muxBits; rw [← mPK b, writeReg_apply_reg]
    change bAxisMux27.evalS (fun j ↦ σ (rMux27Layout j)) (wMux (2 + b.val)) = _
    rw [((bAxisMux27_evalS (fun j ↦ σ (rMux27Layout j)) (m26 ▸ s26)).2.2.2 b).1,
      m0, m1, mB 0 (2 + b.val) b (by omega), mB 1 (10 + b.val) b (by omega),
          mB 2 (18 + b.val) b (by omega)]
    dsimp only [σ]
    rw [s0, s1, sBuf 0 b, sBuf 1 b, sBuf 2 b]
    fin_cases ax
    · exact congrArg Prod.fst (mux1Bit6_axes.1 _ _ _)
    · exact congrArg Prod.fst (mux1Bit6_axes.2.1 _ _ _)
    · exact congrArg Prod.fst (mux1Bit6_axes.2.2 _ _ _)
  refine ⟨hMuxOut β hScr, fun k ↦ funext fun w ↦ ?_⟩
  let β₂ := writeReg β rSC (basisBits 8 k)
  let σ₁ := speciesSwapBits (pKinAlign0.fwdBits (routedKet decodeCoin β c z))
  let σ₂ := speciesSwapBits (pKinAlign0.fwdBits (routedKet decodeCoin β₂ c z))
  by_cases hwP : ∃ b : Fin 8, w = rPKinLayout b
  · obtain ⟨b, rfl⟩ := hwP; rw [writeReg_apply_reg, hMuxOut β₂ (hScrK k) b]
    exact (writeReg_apply_reg β rSC (basisBits 8 k) b).symm
  · rw [writeReg_apply_of_not_mem _ rPKinLayout _ w fun ⟨b, hb⟩ ↦ hwP ⟨b, hb.symm⟩]
    obtain ⟨s0_1, s1_1, s26_1, sBuf1⟩ := postSp_kin_readout hc β hScr z
    obtain ⟨s0_2, s1_2, s26_2, sBuf2⟩ := postSp_kin_readout hc β₂ (hScrK k) z
    have hOthAx (a : Fin 3) (ha : a ≠ ax) (b : Fin 8) :
        β₂ (rSysLayout ((coordinateRegister_frozen i a) b)) =
            β (rSysLayout ((coordinateRegister_frozen i a) b)) :=
      writeReg_apply_of_not_mem β rSC (basisBits 8 k) _ fun ⟨b', hb'⟩ ↦ ha (by
        have hv2 := congrArg Fin.val (rSysLayout.wires.injective hb')
        dsimp [coordinateRegister_frozen, QRegister.block, Fin.natAddEmb, Fin.natAdd, DFunLike.coe,
          -Function.Embedding.toFun_eq_coe, gridBits_frozen] at hv2; omega)
    by_cases hwM : ∃ j : Fin 27, w = rMux27Layout j
    · obtain ⟨j, rfl⟩ :=
          hwM; unfold kinFwdBits muxBits; rw [writeReg_apply_reg, writeReg_apply_reg]
      have hEv1 := bAxisMux27_evalS (fun u ↦ σ₁ (rMux27Layout u)) (m26 ▸ s26_1)
      have hEv2 := bAxisMux27_evalS (fun u ↦ σ₂ (rMux27Layout u)) (m26 ▸ s26_2)
      by_cases hj2 : j.val < 2
      · rcases (by omega : j.val = 0 ∨ j.val = 1) with hj0 | hj1
        · rw [show j = wMux 0 from Fin.ext hj0, hEv1.1, hEv2.1, m0]; dsimp only [σ₁, σ₂];
              rw [s0_1, s0_2]
        · rw [show j = wMux 1 from Fin.ext hj1, hEv1.2.1, hEv2.2.1, m1]; dsimp only [σ₁, σ₂];
              rw [s1_1, s1_2]
      · by_cases hj26 : j.val = 26
        · rw [show j = wMux 26 from Fin.ext hj26, hEv1.2.2.1, hEv2.2.2.1]
        · have hj25 : 2 ≤ j.val ∧ j.val < 26 := ⟨by omega, by have := j.isLt; omega⟩
          by_cases hj10 : j.val < 10
          · exact False.elim (hwP ⟨⟨j.val - 2, by omega⟩, (congrArg rMux27Layout (Fin.ext (by
              dsimp [wMux, SelectStructuredCB.finMod]; omega))).trans (mPK ⟨j.val - 2,
                  by omega⟩)⟩)
          · have z2a (u v : ZMod 2) : v + 1 * (u + v) = u := by fin_cases u <;> fin_cases v <;> rfl
            have z2b (u v w : ZMod 2) : w + 1 * (u + v + (v + 0 * (u + v)) + w) = u := by
              fin_cases u <;> fin_cases v <;> fin_cases w <;> rfl
            by_cases hj18 : j.val < 18
            · let b : Fin 8 := ⟨j.val - 10, by omega⟩
              rw [show j =
                  wMux (10 +
                  b.val) from Fin.ext (by dsimp [wMux, SelectStructuredCB.finMod, b]; omega),
                (hEv1.2.2.2 b).2.1, (hEv2.2.2.2 b).2.1, m0, mB 0 (2 + b.val) b (by omega),
                    mB 1 (10 + b.val) b (by omega)]
              dsimp only [σ₁, σ₂]; rw [s0_1, s0_2, sBuf1 0 b, sBuf1 1 b, sBuf2 0 b, sBuf2 1 b]
              fin_cases ax <;> dsimp
              · rw [zero_mul, add_zero, zero_mul, add_zero, hOthAx 1 (by decide) b]
              · rw [z2a, z2a, hOthAx 0 (by decide) b]
              · rw [zero_mul, add_zero, zero_mul, add_zero, hOthAx 1 (by decide) b]
            · let b : Fin 8 := ⟨j.val - 18, by omega⟩
              rw [show j =
                  wMux (18 +
                  b.val) from Fin.ext (by dsimp [wMux, SelectStructuredCB.finMod, b]; omega),
                (hEv1.2.2.2 b).2.2, (hEv2.2.2.2 b).2.2, m0, m1, mB 0 (2 + b.val) b (by omega),
                mB 1 (10 + b.val) b (by omega), mB 2 (18 + b.val) b (by omega)]
              dsimp only [σ₁, σ₂]
              rw [s0_1, s1_1, s0_2, s1_2, sBuf1 0 b, sBuf1 1 b, sBuf1 2 b, sBuf2 0 b, sBuf2 1 b,
                  sBuf2 2 b]
              fin_cases ax <;> simp only [Nat.testBit] <;> dsimp
              · rw [zero_mul, add_zero, zero_mul, add_zero, hOthAx 2 (by decide) b]
              · rw [zero_mul, add_zero, zero_mul, add_zero, hOthAx 2 (by decide) b]
              · rw [z2b, z2b, hOthAx 0 (by decide) b]
    · have nwM (α : BitAssignment dLayout) : muxBits α w = α w :=
        writeReg_apply_of_not_mem _ rMux27Layout _ w fun ⟨j, hj⟩ ↦ hwM ⟨j, hj.symm⟩
      unfold kinFwdBits; rw [nwM, nwM]
      have nwLoN : ¬(5755 ≤ w.val ∧ w.val < 5779) := fun hb ↦ by
        let qa : Fin 3 := ⟨(w.val - 5755) / 8, by omega⟩
        let qb : Fin 8 := ⟨(w.val - 5755) % 8, by omega⟩
        exact hwM ⟨wMux (2 + (8 * qa.val + qb.val)),
            (Fin.ext (by
              rw [(val_rBufLo_hi_nuc ⟨8 * qa.val + qb.val, _⟩).1]
              dsimp [qa, qb]; omega)).trans (mBuf qa qb).symm⟩
      by_cases hwLoE : 5851 ≤ w.val ∧ w.val < 5875
      · let b24 : Fin 24 := ⟨w.val - 5851, by omega⟩
        have hLoE0 {α : BitAssignment dLayout} (hSA : ∀ m, α (rScrLayout m) = 0) :
            speciesSwapBits (pKinAlign0.fwdBits (routedKet decodeCoin α c z))
                (rBufLo rElecLayout b24) = 0 := by
          obtain ⟨hVN, hKE, hVE, _, hLN, _⟩ :=
              validRouter_stage1 (decodeCoin := decodeCoin) hSA c z
          have hAl := routedKet_align_zero (decodeCoin := decodeCoin) hSA c z
          have ⟨_, _, _, _, hEK⟩ := s5k_ax _ (hAl ⟨109, by omega⟩) (hAl ⟨110, by omega⟩)
            (hAl ⟨135, by omega⟩) (hAl ⟨111, by omega⟩)
          obtain ⟨_, _, _, f0HE1, _, _, _, _, _, _⟩ :=
              packOut40_kin i ax (routedKet decodeCoin α c z)
            fun m ↦ (routedKet_out40 hSA c z m).trans (by rw [hc])
          obtain ⟨f1HN1, f1RN2, _, f1HE1, f1RE2, _, _, _, _, _⟩ :=
              packOut40_kin i ax (routedStage1 decodeCoin α c z)
            fun m ↦ (writeReg_apply_reg _ rOut40Layout _ m).trans (by rw [hc])
          have hbE := (val_rBufLo_hi b24).1; have hbN := (val_rBufLo_hi_nuc b24).1
          rw [speciesSwapBits_bufLo_elec, hEK, ← rElec_header_eq_out40.1]
          by_cases hi : i.val < 47
          · rw [f0HE1.trans (ite_eq_left hi), ite_eq_right zero_ne_one]
            exact (fwdBits_not_target targetsIn_pKinAlign0 _ (by omega)).trans
                (((routerSwapBits_cases rElecLayout hVE).1
              ((hKE _).trans (f1HE1.trans (ite_eq_left hi))) ((hKE _).trans f1RE2)).1 b24)
          · rw [f0HE1.trans (ite_eq_right hi), ite_eq_left rfl]
            exact (fwdBits_not_target targetsIn_pKinAlign0 _ (by omega)).trans ((hLN b24).trans
              (((routerSwapBits_cases rNucLayout hVN).1
                (f1HN1.trans (ite_eq_right hi)) f1RN2).1 b24))
        rw [show w =
            rBufLo rElecLayout b24 from Fin.ext
            (by rw [(val_rBufLo_hi b24).1]; dsimp [b24]; omega)]
        exact (hLoE0 hScr).trans (hLoE0 (hScrK k)).symm
      · rw [speciesSwapBits_outside _ nwLoN hwLoE, speciesSwapBits_outside _ nwLoN hwLoE]
        exact fwdBits_congr_wires (cpWires_pKinAlign0 (S := fun u ↦ ¬(5755 ≤ u.val ∧ u.val < 5779) ∧
            ¬(5851 ≤ u.val ∧
          u.val < 5875))
          (fun m ↦ ⟨by rw [val_rAlignLayout]; omega, by rw [val_rAlignLayout]; omega⟩)
              (fun m ↦
            ⟨by rw [val_rOut40Layout]; omega, by rw [val_rOut40Layout]; omega⟩))
          (fun u ⟨hu1, hu2⟩ ↦ outEq_kin hScr hc z k u hu1 hu2) w ⟨nwLoN, hwLoE⟩
end QuantumComputation.Specs.PhotochemistrySolution.PotSelectWiring
end
end

@[expose] public section

noncomputable section
set_option autoImplicit false
namespace QuantumComputation.Specs.PhotochemistrySolution.ReflStage4

open Operator QProg Matrix Circuit Qubit PrimitiveGate QuantumComputation.Specs
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
open PhotochemistrySolution.KetSupport PhotochemistrySolution
  PhotochemistrySolution.SelectOracles
open PhotochemistrySolution.RouterSelectWiringA PhotochemistrySolution.RouterSelectWiringB
  PhotochemistrySolution.Stage12Compact
open PhotochemistrySolution.PotSelectWiring PhotochemistrySolution.Kinetic664Stage4
open _root_.DynamicCircuit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt hiding ket matrix_ext_ket
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SelectCompactAnc (totDimCompactGen
    ancWOfScr cat8SharedProjCompactGen projOneQCompactGen)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.TopSelectBridge (scrSubLGen lcuSubLGen
    reflULGen)
open scoped Matrix BigOperators
local instance (priority := 100000) {k : ℕ} : NeZero (2 ^ k) := ⟨pow_ne_zero k two_ne_zero⟩
set_option allowUnsafeReducibility true in
attribute [local reducible] totDimCompactGen
set_option allowUnsafeReducibility true in
attribute [local irreducible] systemQubits_frozen ancWOfScr PgBase.phaseGradientState reflULGen

section Walk0
set_option exponentiation.threshold 8192
open PhotochemistrySolution.SelectCompactAnc PhotochemistrySolution.SelectQft8GidneyStg3
open PhotochemistrySolution.ProviderCore PhotochemistrySolution.Qft8PostCancelT5
  PhotochemistrySolution.Coin70Lift
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SelectKin526OneWrap
  (embedUnitary_comm_of_disjoint)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SelectFastQft8Gidney (spliceUnitary
    spliceUnitaryMat)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SelectQft8KinMid
  (csel_seq_and_conj_eq_of_comm_proj)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.XMeasChunkQromUnldA (phaseFlipUnitary)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Stage4Cluster22Xnor (byteOfBits)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.PotOracleGen (disj_ne disj_of_ne)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Kinetic664 (abpKin15SqFree2m1Usel
    abpKin15SqFree2m1Csel)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Stage4KinFull (bAxisMux27)
set_option allowUnsafeReducibility true in
attribute [local irreducible] phaseFlipUnitary bSpeciesSwap50 bAxisMux27 qft8PostCancel98CatU
    abpKin15SqFree2m1Usel abpKin15SqFree2m1Csel
theorem writeReg_comm_of_ne {n k₁ k₂ : ℕ} (r₁ : QRegister k₁ n) (r₂ : QRegister k₂ n)
    (hne : ∀ i j, r₁ i ≠ r₂ j) (δ : BitAssignment n) (v₁ : BitAssignment k₁)
        (v₂ : BitAssignment k₂) :
    writeReg (writeReg δ r₁ v₁) r₂ v₂ = writeReg (writeReg δ r₂ v₂) r₁ v₁ := funext fun w ↦ by
  by_cases h₂ : ∃ j, r₂ j = w
  · obtain ⟨j, rfl⟩ := h₂
    rw [writeReg_apply_reg, writeReg_apply_of_not_mem _ r₁ v₁ _ fun ⟨i, hi⟩ ↦ hne i j hi,
        writeReg_apply_reg]
  · rw [writeReg_apply_of_not_mem _ r₂ v₂ w h₂]
    by_cases h₁ : ∃ i, r₁ i = w
    · obtain ⟨i, rfl⟩ := h₁; rw [writeReg_apply_reg, writeReg_apply_reg]
    · rw [writeReg_apply_of_not_mem _ r₁ v₁ w h₁, writeReg_apply_of_not_mem _ r₁ v₁ w h₁,
        writeReg_apply_of_not_mem _ r₂ v₂ w h₂]
theorem uPotReflZeroNErem_comm_of_disj {potExpect : PotExpectFn} (spec : ReflPotSliceSpec potExpect)
    (isCsel : Bool) {k : ℕ}
    (r : QRegister k dLayout)
    (hDisj : ∀ (j : Fin (146 + 0)) (i : Fin k), (isCsel = true ∨ 1 ≤ j.val) → rPot0Layout j ≠ r i)
        (M : Operator
      (2 ^ k)) : Commute (uPotReflZeroNErem spec isCsel).1 (r.embedMatrix M) := by
  have hkeep (δ : BitAssignment dLayout) (η : BitAssignment k) (j : ℕ) (hj : j < 146)
      (hc : isCsel = true ∨ 1 ≤ j) :
      writeReg δ r η (rPot0Layout ⟨j, by omega⟩) = δ (rPot0Layout ⟨j, by omega⟩) :=
    writeReg_apply_of_not_mem δ r η _ fun ⟨i, hi⟩ ↦ hDisj ⟨j, by omega⟩ i hc hi.symm
  have hk1 (δ : BitAssignment dLayout) (η : BitAssignment k) (j : ℕ) (hj : 1 ≤ j ∧ j < 146) :=
      hkeep δ η j hj.2 (.inr hj.1)
  have hC24 (δ : BitAssignment dLayout) (η : BitAssignment k) (off : ℕ) (h0 : off + 24 ≤ 146 + 0)
      (_ho : 1 ≤ off) :
      coordOfReg24 (rPot0Layout.compose (QRegister.block off 24 h0)) (writeReg δ r η) =
        coordOfReg24 (rPot0Layout.compose (QRegister.block off 24 h0)) δ :=
    funext fun ax ↦ congrArg byteOfBits <| funext fun b ↦
      hk1 δ η (off + (8 * ax.val + b.val))
          (by have := PotSelectWiring.coordOfReg24_lt ax b; omega)
  have hZ (δ : BitAssignment dLayout) (η : BitAssignment k) :
      (fun m : Fin 41 ↦ writeReg δ r η (rPotCoin41 rPot0Layout m)) = fun m ↦
          δ (rPotCoin41 rPot0Layout m) :=
    funext fun m ↦ hk1 δ η (105 + m.val) (by omega)
  refine signedPermUnitary_comm_embedMatrix _ _ _ r (fun δ η ↦ ?_) (fun δ η ↦ ?_) M
  · have hgEq : potGateActive4 isCsel rPot0Layout (writeReg δ r η) =
        potGateActive4 isCsel rPot0Layout δ := by
      dsimp only [potGateActive4, wPotLocQ, wPotIsPot]
      by_cases hC : isCsel = true
      · rw [ite_eq_left hC, ite_eq_left hC, hkeep δ η 0 (by omega) (.inl hC), hk1 δ η 2 (by omega)]
      · rw [ite_eq_right hC, ite_eq_right hC, hk1 δ η 2 (by omega)]
    dsimp only [potReflSwap4];
        rw [hgEq, show potOracleCoinEval spec.coinSwap rPot0Layout (writeReg δ r η) =
        potOracleCoinEval spec.coinSwap rPot0Layout δ by
      dsimp only [potOracleCoinEval]
      rw [hk1 δ η 1 (by omega), hk1 δ η 4 (by omega), hk1 δ η 5 (by omega), hk1 δ η 6 (by omega),
        hk1 δ η 7 (by omega), hk1 δ η 8 (by omega), hC24 δ η 9 potBlkNucA_le (by omega),
        hC24 δ η 33 potBlkNucB_le (by omega), hC24 δ η 57 potBlkElecA_le (by omega),
        hC24 δ η 81 potBlkElecB_le (by omega), hZ δ η]]; split_ifs
    · exact writeReg_comm_of_ne r (rPotCoin41 rPot0Layout)
        (fun i m e ↦ hDisj ⟨105 + m.val, by omega⟩ i (.inr (by dsimp only; omega)) e.symm) δ η _
    · rfl
  · dsimp only [potReflPh4, wPotLocQ, wPotIsPot];
        rw [show potOracleBitEval spec.phaseBit rPot0Layout (writeReg δ r η) =
        potOracleBitEval spec.phaseBit rPot0Layout δ by
      dsimp only [potOracleBitEval]
      rw [hk1 δ η 1 (by omega), hk1 δ η 4 (by omega), hk1 δ η 5 (by omega), hk1 δ η 6 (by omega),
        hk1 δ η 7 (by omega), hk1 δ η 8 (by omega), hC24 δ η 9 potBlkNucA_le (by omega),
        hC24 δ η 33 potBlkNucB_le (by omega), hC24 δ η 57 potBlkElecA_le (by omega),
        hC24 δ η 81 potBlkElecB_le (by omega), hZ δ η]]
    by_cases hC : isCsel = true
    · rw [ite_eq_left hC, ite_eq_left hC, hkeep δ η 0 (by omega) (.inl hC), hk1 δ η 2 (by omega)]
    · rw [ite_eq_right hC, ite_eq_right hC, hk1 δ η 2 (by omega)]
theorem uPotReflIdealZeroNErem_comm_off {potExpect : PotExpectFn}
    (spec : ReflPotSliceSpec potExpect) {k : ℕ}
    {r : QRegister k dLayout}
    (hoff : OffIndexAndScratchPoly systemQubits_frozen scrWLayout (lcuSubLGen hpLayout)
        (scrSubLGen hpLayout) r) (M : Operator
      (2 ^ k)) : Commute (uPotReflIdealZeroNErem spec).1 (r.embedMatrix M) :=
  uPotReflZeroNErem_comm_of_disj spec false r (fun j i h e ↦ by
    have hj1 : 1 ≤ j.val := h.resolve_left Bool.false_ne_true
    have hb := hoffIndex_bounds_layout hoff i
    have hv : (potZeroNEremWireFn 0 pot0_le_690 j).val = (r i).val := congrArg Fin.val e
    rw [val_potZeroNEremWireFn pot0_le_690] at hv; split_ifs at hv <;> omega) M
theorem uPotReflZeroNErem_comm_locGrad3Hi {potExpect : PotExpectFn}
    (spec : ReflPotSliceSpec potExpect) (isCsel : Bool) (M : Operator (2 ^ 3)) :
    Commute (uPotReflZeroNErem spec isCsel).1 (locGrad3HiLayout_refl.embedMatrix M) :=
  uPotReflZeroNErem_comm_of_disj spec isCsel locGrad3HiLayout_refl (fun j i _ e ↦ by
    have hi := i.isLt
    have hv : (potZeroNEremWireFn 0 pot0_le_690 j).val = (locGrad3HiLayout_refl i).val :=
        congrArg Fin.val e
    rw [val_potZeroNEremWireFn pot0_le_690, val_locGrad3HiLayout_refl] at hv;
        split_ifs at hv <;> omega) M
/-
## Section 2: `98-T` Kinetic + Reflected Potential Stage-4 Unitaries & `locGrad3Hi` Commutation
-/

theorem uAlignedKin2m1_98_comm_band {kCoin : ℕ} (rC : QRegister kCoin dLayout)
    (hBand : ∀ j : Fin kCoin,
      (5647 ≤ (rC j).val ∧ (rC j).val < 5650) ∨ (7143 ≤ (rC j).val ∧ (rC j).val < 7256))
    (M : Operator (2 ^ kCoin)) :
    Commute uAlignedKinIdeal2m1Layout.1 (rC.embedMatrix M) ∧
    Commute uAlignedKinCat2m1_98UselLayout.1 (rC.embedMatrix M) ∧
    Commute uAlignedKinCat2m1_98CselLayout.1 (rC.embedMatrix M) := by
  have hd := hDLayout_w0
  have cConj {W V : Unitary (2 ^ dLayout)} (cW : Commute W.1 (rC.embedMatrix M))
      (cV : Commute V.1 (rC.embedMatrix M)) :
      Commute (W⁻¹ * V * W).1 (rC.embedMatrix M) :=
    Commute.mul_left (Commute.mul_left (SelectFastQft8Gidney.unitary_inv_comm W _ cW) cV) cW
  have cA0 : Commute uKinAlign0Layout.1 (rC.embedMatrix M) :=
      fwdCirc_comm_embedMatrix_of_disj rC (cpWires_pKinAlign0
    (fun m j e ↦
        by have := hBand j; have hv :=
                                 congrArg Fin.val e; rw [val_rAlignLayout] at hv; omega)
    (fun i j e ↦
        by have := hBand j; have hv :=
                                 congrArg Fin.val e; rw [val_rOut40Layout] at hv; omega)) M
  have hNe {w : ℕ} (r : QRegister w dLayout)
      (hOut : ∀ i, ¬((5647 ≤ (r i).val ∧ (r i).val < 5650) ∨ (7143 ≤ (r i).val ∧ (r i).val <
          7256))) : r.DisjointWires rC :=
    disj_of_ne fun i j e ↦ hOut i (by have := hBand j; have := congrArg Fin.val e; omega)
  have cSp : Commute uSpeciesSwap50Layout.1 (rC.embedMatrix M) :=
      embedUnitary_comm_of_disjoint rSpeciesSwap50Layout _ rC
    (hNe _ fun i ↦
        by have :=
             i.isLt; rw [rSp50_eq_fn_w0, val_speciesSwap50WireFn]; split_ifs <;> omega) M
  have cMux : Commute uMux27Layout.1 (rC.embedMatrix M) :=
      embedUnitary_comm_of_disjoint rMux27Layout _ rC
    (hNe _ fun i ↦
        by have := i.isLt; rw [rMux27_eq_fn_w0, val_mux27WireFn]; split_ifs <;> omega) M
  have dP := hNe rPKinLayout fun i ↦ by have := i.isLt; rw [val_rPKinLayout]; omega
  have cQid : Commute (qft8Stg3IdealU scrWLayout rPKinLayout).1 (rC.embedMatrix M) :=
    embedUnitary_comm_of_disjoint rPKinLayout _ rC dP M
  have cMid : Commute uKinMid2m1UselLayout.1 (rC.embedMatrix M) :=
      embedUnitary_comm_of_disjoint rKin226Layout _ rC
    (hNe _ fun i ↦
        by have := i.isLt; have hv : (rKin226Layout i).val = _ :=
                                val_kin226WireFn i; rw [hv]; split_ifs <;> omega) M
  have cQcat :
      Commute (qft8PostCancel98CatU () scrWLayout offKinLayout hoffKinLayout rPKinLayout
      qft8Stg3ValidP_layout).1
      (rC.embedMatrix M) := by
    let rCln := qft8Stg3Clean13 scrWLayout offKinLayout hoffKinLayout
    have dCln := hNe rCln fun i ↦ by
      rw [qft8Stg3Clean13_eq_workInner ⟨i.val, by omega⟩, val_rWorkInnerLayout]; dsimp only;
          omega
    have abQ :=
        andBracketWires_polyPostCancelT5Qft8Bracket98 (P := fun w ↦ ∀ j : Fin kCoin, w ≠ rC j)
      (locCat8SharedCompactGen scrWLayout) rPKinLayout (qft8Stg3Delta7 scrWLayout offKinLayout
          hoffKinLayout)
      (qft8Stg3Carry6 scrWLayout offKinLayout hoffKinLayout)
      (qft8Stg3_rP_disj_cat8 qft8Stg3ValidP_layout)
          (qft8Stg3_rP_disj_delta7 hoffKinLayout qft8Stg3ValidP_layout)
      (qft8Stg3_delta7_disj_cat8 hoffKinLayout) (qft8Stg3_delta7_disj_carry6 hoffKinLayout)
      (qft8Stg3_cat8_disj_carry6 hoffKinLayout)
          (qft8Stg3_rP_disj_carry6 hoffKinLayout qft8Stg3ValidP_layout)
      (fun c j e ↦ by
        have := c.isLt; have := hBand j; have hv := congrArg Fin.val e
        rw [val_locCat8_layout] at hv; dsimp only at hv; omega)
            (fun i j e ↦ disj_ne dP i j e)
      (fun i j e ↦ disj_ne dCln ⟨i.val,
          by omega⟩ j ((qft8Stg3_clean13_sub_delta7 hoffKinLayout ⟨i.val, by omega⟩).trans e))
      (fun i j e ↦ disj_ne dCln ⟨7 + i.val,
          by omega⟩ j ((qft8Stg3_clean13_sub_carry6 hoffKinLayout ⟨i.val, by omega⟩).trans e))
    have cP13 := rCln.embedMatrix_comm_of_disjoint rC dCln (compProj 0) M
    unfold qft8PostCancel98CatU polyPostCancelCleanUnitary spliceUnitary
    change spliceUnitaryMat _ _ _ * rC.embedMatrix M = rC.embedMatrix M * spliceUnitaryMat _ _ _;
        unfold spliceUnitaryMat
    exact Commute.add_left (Commute.mul_left (circ_comm_embedMatrix_c70 rC M
        (circWires_toCircuit_c70 abQ)) cP13)
      (Commute.mul_left (embedUnitary_comm_of_disjoint rPKinLayout (dPost8U *
          qftGridUnitary) rC dP M)
        (Commute.sub_left (Commute.one_left _) cP13))
  have cUsel : Commute uAlignedKinCat2m1_98UselLayout.1 (rC.embedMatrix M) :=
      cConj cA0 (cConj cSp (cConj cMux (cConj cQcat cMid)))
  let Pq := projOneQCompactGen scrWLayout
  have sKin :=
      csel_conj_unitary Pq uKinAlign0Layout uKinCat2m1_98CselLayout uKinCat2m1_98UselLayout
    comm_pq.2.eq uKin2m1_98Layout_props.1 uKin2m1_98Layout_props.2.1
  have cPq : Commute Pq (rC.embedMatrix M) :=
      (QRegister.singleton wLocQLayout).embedMatrix_comm_of_disjoint rC
    (disj_of_ne fun _ j e ↦ by
      have :=
          hBand j;
          have hv : wLocQLayout.val = _ :=
          congrArg Fin.val e; rw [val_wLocQLayout] at hv; omega) (compProj 1) M
  refine ⟨cConj cA0 (cConj cSp (cConj cMux (cConj cQid cMid))), cUsel, ?_⟩
  change uAlignedKinCat2m1_98CselLayout.1 * _ = _ * uAlignedKinCat2m1_98CselLayout.1
  unfold uAlignedKinCat2m1_98CselLayout uAlignedKinCat2m1_98UselLayout at *
  rw [sKin.1]; exact ((Commute.one_left _).sub_left cPq).add_left (cPq.mul_left cUsel)
theorem uAlignedKin2m1_98_comm_locGrad3Hi (M : Operator (2 ^ 3)) :
    let rG := locGrad3HiLayout_refl
    Commute uAlignedKinIdeal2m1Layout.1 (rG.embedMatrix M) ∧
        Commute uAlignedKinCat2m1_98UselLayout.1
      (rG.embedMatrix M) ∧ Commute uAlignedKinCat2m1_98CselLayout.1 (rG.embedMatrix M) :=
  uAlignedKin2m1_98_comm_band locGrad3HiLayout_refl (fun j ↦ Or.inl
    (by have := j.isLt; rw [val_locGrad3HiLayout_refl]; omega)) M
/-- Ideal `(2m+1)` Stage-4 unitary with reflected potential oracle on `dLayout`. -/
def uStage4ReflZeroNErem2m1Ideal {potExpect : PotExpectFn} (spec : ReflPotSliceSpec potExpect) :
    Unitary (2 ^ dLayout) :=
  uAlignedKinIdeal2m1Layout * uPotReflIdealZeroNErem spec
/-- Unguarded cat `98-T` `(2m+1)` Stage-4 unitary with reflected potential oracle on `dLayout`. -/
def uStage4ReflZeroNErem2m1_98CatUsel {potExpect : PotExpectFn}
    (spec : ReflPotSliceSpec potExpect) : Unitary (2 ^ dLayout) :=
  uAlignedKinCat2m1_98UselLayout * uPotReflIdealZeroNErem spec
/-- Cat-guarded `98-T` `(2m+1)` Stage-4 unitary with reflected potential oracle on `dLayout`. -/
def uStage4ReflZeroNErem2m1_98CatCsel {potExpect : PotExpectFn}
    (spec : ReflPotSliceSpec potExpect) : Unitary (2 ^ dLayout) :=
    uAlignedKinCat2m1_98CselLayout * uPotReflCatCselZeroNErem spec
theorem uStage4ReflZeroNErem2m1_98Layout_props {potExpect : PotExpectFn}
    (spec : ReflPotSliceSpec potExpect) : (uStage4ReflZeroNErem2m1_98CatCsel spec).1 =
    (1 - projOneQCompactGen scrWLayout) + projOneQCompactGen scrWLayout *
    (uStage4ReflZeroNErem2m1_98CatUsel spec).1 ∧ (uStage4ReflZeroNErem2m1_98CatUsel spec).1 *
    cat8SharedProjCompactGen scrWLayout = (uStage4ReflZeroNErem2m1Ideal spec).1 *
    cat8SharedProjCompactGen scrWLayout ∧ (∀ {k : ℕ} (r : QRegister k dLayout),
    OffIndexAndScratchPoly systemQubits_frozen scrWLayout (lcuSubLGen hpLayout)
    (scrSubLGen hpLayout) r → ∀ M : Operator (2 ^ k),
    Commute (uStage4ReflZeroNErem2m1Ideal spec).1 (r.embedMatrix M)) := by
  let Pq := projOneQCompactGen scrWLayout
  have sKin :=
      csel_conj_unitary Pq uKinAlign0Layout uKinCat2m1_98CselLayout uKinCat2m1_98UselLayout
    comm_pq.2.eq uKin2m1_98Layout_props.1 uKin2m1_98Layout_props.2.1
  let Mcat := Matrix.vecMulVec (PgBase.phaseGradientState 8) (star (PgBase.phaseGradientState 8))
  exact ⟨(csel_seq_and_conj_eq_of_comm_proj Pq ((QRegister.singleton
      wLocQLayout).basisOutcomeProjector_mul_self 1) 1
      ((one_mul Pq).trans (mul_one Pq).symm) uAlignedKinCat2m1_98CselLayout.1
          uAlignedKinCat2m1_98UselLayout.1
      (uPotReflCatCselZeroNErem spec).1 (uPotReflIdealZeroNErem spec).1 sKin.1
          (uPotReflCatCselZeroNErem_eq_ctrl spec) sKin.2).1,
    conj_seq_cat_eq (uKinAlign0Layout⁻¹).1 uKinAlign0Layout.1 uKinCat2m1_98UselLayout.1
        uKinIdeal2m1UselLayout.1
      uAlignedKinCat2m1_98UselLayout.1 uAlignedKinIdeal2m1Layout.1 (uPotReflIdealZeroNErem spec).1
          (cat8SharedProjCompactGen scrWLayout)
      (cOffPre _ hoff_cat8_layout Mcat).2.eq uKin2m1_98Layout_props.2.2.1 rfl rfl
      (uPotReflIdealZeroNErem_comm_off spec hoff_cat8_layout Mcat).eq,
    fun r hoff M ↦ ((((show Commute _ _ from
      SelectFastQft8Gidney.unitary_inv_comm _ _ (cOffPre r hoff M).2).mul_left
      (uKin2m1_98Layout_props.2.2.2 r hoff M)).mul_left (cOffPre r hoff M).2)).mul_left
      (uPotReflIdealZeroNErem_comm_off spec hoff M)⟩
theorem uStage4ReflZeroNErem2m1_98_comm_locGrad3Hi {potExpect : PotExpectFn}
    (spec : ReflPotSliceSpec potExpect) (M : Operator
  (2 ^ 3)) :
    let rG := locGrad3HiLayout_refl
    Commute (uStage4ReflZeroNErem2m1Ideal spec).1 (rG.embedMatrix M) ∧
        Commute (uStage4ReflZeroNErem2m1_98CatUsel spec).1
      (rG.embedMatrix M) ∧ Commute (uStage4ReflZeroNErem2m1_98CatCsel spec).1 (rG.embedMatrix M)
          := by
  obtain ⟨cKI, cKU, cKC⟩ := uAlignedKin2m1_98_comm_locGrad3Hi M
  exact ⟨cKI.mul_left (uPotReflZeroNErem_comm_locGrad3Hi spec false M), cKU.mul_left
    (uPotReflZeroNErem_comm_locGrad3Hi spec false M),
        cKC.mul_left (uPotReflZeroNErem_comm_locGrad3Hi spec true M)⟩
end Walk0

section Walk1a
set_option exponentiation.threshold 8192
open PhotochemistrySolution.ProviderCore PhotochemistrySolution.ZeroNEremSpec
  PhotochemistrySolution.Kinetic664
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB (ket matrix_ext_ket)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.QubitizationWalkSem (bitSign
    bitSign_zero)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.XMeasChunkQromUnldA (phaseFlipUnitary)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynQromUncompA (fwdCirc_mulVec_ket)
set_option allowUnsafeReducibility true in
attribute [local irreducible] phaseFlipUnitary
theorem wPotIsPot_rPot0Layout_eq : wPotIsPot rPot0Layout = wIsFine :=
  Fin.ext (by
    change (potZeroNEremWireFn 0 pot0_le_690 ⟨2, potIdx2_lt⟩).val = wIsFine.val
    rw [val_potZeroNEremWireFn pot0_le_690 ⟨2,
      potIdx2_lt⟩]; dsimp only [wIsFine]; rw [val_rOut40Layout]; dsimp only;
          split_ifs <;> norm_num at *)
theorem writeReg_rPotCoin41_routedKet {decodeCoin : Fin (2 ^ 41) → ZeroNEremSector}
    (α : BitAssignment dLayout) (c : Fin
  (2 ^ 41)) (z z' : BitAssignment 41) :
    DynCircExt.writeReg (routedKet decodeCoin α c z) (rPotCoin41 rPot0Layout) z' =
        routedKet decodeCoin α c z' := by
  rw [show rPotCoin41 rPot0Layout = rInner41Layout from congrArg QRegister.mk
    (Function.Embedding.ext fun k ↦ rPot0_ports_eq.2.2.2.2.2.2 k),
        routedKet_eq_writeReg_z decodeCoin α c z,
      routedKet_eq_writeReg_z decodeCoin α c z']
  funext w
  by_cases hw : ∃ k : Fin 41, w = rInner41Layout k
  · obtain ⟨k, rfl⟩ := hw; simp only [writeReg_apply_reg]
  · simp only [writeReg_apply_of_not_mem _ rInner41Layout _ w fun ⟨k, hk⟩ ↦ hw ⟨k, hk.symm⟩]
/-- 3-sector computational-basis action and involutivity of `uStage4ReflZeroNErem2m1Ideal`. -/
theorem uStage4ReflZeroNErem2m1Ideal_sector_and_invol {potExpect : PotExpectFn}
    (spec : ReflPotSliceSpec potExpect) (β : BitAssignment dLayout)
    (hClean22 : β (rWorkInnerLayout ⟨22, fin22_lt_521_pot⟩) = 0) : (β wIsFine = 0 → β wIsKin = 0 →
    (uStage4ReflZeroNErem2m1Ideal spec).1.mulVec (ket β) = ket β ∧
    (uStage4ReflZeroNErem2m1Ideal spec).1.mulVec ((uStage4ReflZeroNErem2m1Ideal spec).1.mulVec
    (ket β)) = ket β) ∧ (β wIsFine = 1 → β wIsKin = 0 →
    (uStage4ReflZeroNErem2m1Ideal spec).1.mulVec (ket β) =
    bitSign (potOracleBitEval spec.phaseBit rPot0Layout β) • ket (DynCircExt.writeReg β
    (rPotCoin41 rPot0Layout) (potOracleCoinEval spec.coinSwap rPot0Layout β)) ∧
    (uStage4ReflZeroNErem2m1Ideal spec).1.mulVec ((uStage4ReflZeroNErem2m1Ideal spec).1.mulVec
    (ket β)) = ket β) ∧ (β wIsFine = 0 → β wIsKin = 1 →
    (uStage4ReflZeroNErem2m1Ideal spec).1.mulVec (ket β) =
    uAlignedKinIdeal2m1Layout.1.mulVec (ket β) ∧
    (uStage4ReflZeroNErem2m1Ideal spec).1.mulVec ((uStage4ReflZeroNErem2m1Ideal spec).1.mulVec
    (ket β)) = ket β) := by
  let U := uPotReflIdealZeroNErem spec
  let K := uAlignedKinIdeal2m1Layout
  have hPot0 (δ : BitAssignment dLayout) (h0 : δ wIsFine = 0) : U.1.mulVec (ket δ) = ket δ := by
    have hAct : potGateActive4 false rPot0Layout δ = false := by
      unfold potGateActive4; rw [wPotIsPot_rPot0Layout_eq, h0]; rfl
    dsimp only [U, uPotReflIdealZeroNErem]; rw [uPotReflZeroNErem_mulVec_ket]
    simp only [potReflPh4, potReflSwap4, hAct, wPotIsPot_rPot0Layout_eq, h0, Bool.false_eq_true,
        ↓reduceIte, zero_mul,
      bitSign_zero, one_smul]
  refine ⟨fun hf0 hk0 ↦ ?_, fun hf1 hk0 ↦ ?_, fun hf0 _ ↦ ?_⟩
  · have h1 : (uStage4ReflZeroNErem2m1Ideal spec).1.mulVec (ket β) = ket β := by
      unfold uStage4ReflZeroNErem2m1Ideal; rw [Submonoid.coe_mul, ← Matrix.mulVec_mulVec,
          hPot0 β hf0]
      exact uAlignedKinIdeal2m1_fix β hk0 hClean22
    exact ⟨h1, by rw [h1, h1]⟩
  · let β' := writeReg β (rPotCoin41 rPot0Layout) (potOracleCoinEval spec.coinSwap rPot0Layout β)
    have hAct : potGateActive4 false rPot0Layout β = true := by
      unfold potGateActive4; rw [wPotIsPot_rPot0Layout_eq, hf1]; rfl
    have hUβ : U.1.mulVec (ket β) =
        bitSign (potOracleBitEval spec.phaseBit rPot0Layout β) • ket β' := by
      dsimp only [U, uPotReflIdealZeroNErem]; rw [uPotReflZeroNErem_mulVec_ket]
      simp only [potReflPh4, potReflSwap4, hAct, wPotIsPot_rPot0Layout_eq, hf1, Bool.false_eq_true,
          ↓reduceIte, one_mul, β']
    have hNotC {w : Wire dLayout} (hw : w.val < 7256) : β' w = β w :=
      writeReg_apply_of_not_mem β (rPotCoin41 rPot0Layout) _ w fun ⟨m, hm⟩ ↦ by
        have hv :=
            congrArg Fin.val (hm.symm.trans (rPot0_ports_eq.2.2.2.2.2.2 m));
            rw [val_rInner41Layout] at hv; omega
    have h1 : (uStage4ReflZeroNErem2m1Ideal spec).1.mulVec (ket β) =
        bitSign (potOracleBitEval spec.phaseBit rPot0Layout β) • ket β' := by
      unfold uStage4ReflZeroNErem2m1Ideal; rw [Submonoid.coe_mul, ← Matrix.mulVec_mulVec, hUβ,
          Matrix.mulVec_smul,
        uAlignedKinIdeal2m1_fix β'
            ((hNotC (by dsimp [wIsKin]; rw [val_rOut40Layout]; omega)).trans hk0)
          ((hNotC (by rw [val_rWorkInnerLayout]; omega)).trans hClean22)]
    refine ⟨h1, ?_⟩; rw [h1, ← hUβ]; change (K.1 * U.1).mulVec (U.1.mulVec (ket β)) = ket β
    rw [← Matrix.mulVec_mulVec, Matrix.mulVec_mulVec (ket β) U.1 U.1,
        uPotReflZeroNErem_sq_one spec false, Matrix.one_mulVec]
    exact uAlignedKinIdeal2m1_fix β hk0 hClean22
  · let P := pBit0 wIsFine
    have hUP : U.1 * P = P := matrix_ext_ket fun δ ↦ by
      dsimp only [P, pBit0]; rw [← Matrix.mulVec_mulVec,
          SelectRefl.ket_basisOutcomeProjector_zero]
      by_cases zF : ∀ i : Fin 1, δ ((QRegister.singleton wIsFine) i) = 0
      · rw [ifPosSqf zF, hPot0 δ (zF 0)]
      · rw [ifNegSqf zF, Matrix.mulVec_zero]
    have cA : uKinAlign0Layout.1 * P = P * uKinAlign0Layout.1 := matrix_ext_ket fun δ ↦ by
      have hku : (pKinAlign0.fwdBits δ) wIsFine = δ wIsFine :=
          fwdBits_not_target targetsIn_pKinAlign0 δ
        (by dsimp only [wIsFine]; rw [val_rOut40Layout]; norm_num)
      have hkδ : uKinAlign0Layout.1.mulVec (ket δ) = ket (pKinAlign0.fwdBits δ) :=
          fwdCirc_mulVec_ket pKinAlign0 δ
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hkδ]
      by_cases hz : δ wIsFine = 0
      · rw [pBit0_ket hz, hkδ, pBit0_ket (hku.trans hz)]
      · dsimp only [P, pBit0]; rw [SelectRefl.ket_basisOutcomeProjector_zero,
          ifNegSqf (fun h ↦ hz (h 0)), Matrix.mulVec_zero,
              SelectRefl.ket_basisOutcomeProjector_zero,
          ifNegSqf (fun h ↦ hz (hku.symm.trans (h 0)))]
    have hKA : K.1 = uKinAlign0Layout.1 * uKinIdeal2m1UselLayout.1 * uKinAlign0Layout.1 :=
      congrArg (fun X : Unitary (2 ^ dLayout) ↦ X.1 * uKinIdeal2m1UselLayout.1 *
          uKinAlign0Layout.1) uKinAlign0Layout_inv_eq
    have cKP : K.1 * P = P * K.1 := by
      rw [hKA, Matrix.mul_assoc, Matrix.mul_assoc, cA,
          ← Matrix.mul_assoc uKinIdeal2m1UselLayout.1 P,
        show uKinIdeal2m1UselLayout.1 * P = P *
            uKinIdeal2m1UselLayout.1 from uKinIdeal2m1_comm_pBit0_wIsFine,
        Matrix.mul_assoc P, ← Matrix.mul_assoc uKinAlign0Layout.1 P, cA];
            simp only [Matrix.mul_assoc]
    have hKSq : K.1 * K.1 = 1 := congrArg Subtype.val
      (inv_conj_sq_one uKinAlign0Layout uKinIdeal2m1UselLayout uKinIdeal2m1Usel_sq_one)
    have hPβ : P.mulVec (ket β) = ket β := pBit0_ket hf0
    have h1 : (uStage4ReflZeroNErem2m1Ideal spec).1.mulVec (ket β) = K.1.mulVec (ket β) := by
      change (K.1 * U.1).mulVec (ket β) = K.1.mulVec (ket β)
      rw [← hPβ, Matrix.mulVec_mulVec (ket β) (K.1 * U.1) P, Matrix.mul_assoc, hUP,
          ← Matrix.mulVec_mulVec]
    refine ⟨h1, ?_⟩; rw [h1]; change (K.1 * U.1).mulVec (K.1.mulVec (ket β)) = ket β
    rw [← hPβ, Matrix.mulVec_mulVec (ket β) K.1 P, Matrix.mulVec_mulVec _ (K.1 * U.1) (K.1 * P),
      cKP, Matrix.mul_assoc K.1 U.1 (P * K.1), ← Matrix.mul_assoc U.1 P K.1, hUP, ← cKP,
      ← Matrix.mul_assoc K.1 K.1 P, hKSq, Matrix.one_mul]
theorem potReflSwap4_routedKet {decodeCoin : Fin (2 ^ 41) → ZeroNEremSector}
    {potExpect : PotExpectFn} (spec : ReflPotSliceSpec potExpect) (α : BitAssignment dLayout)
    (c : Fin (2 ^ 41)) (z : BitAssignment 41) : ∃ z' : BitAssignment 41,
    potReflSwap4 spec false rPot0Layout (routedKet decodeCoin α c z) =
    routedKet decodeCoin α c z' := by
  let δ := routedKet decodeCoin α c z
  by_cases hAct : potGateActive4 false rPot0Layout δ = true
  · refine ⟨potOracleCoinEval spec.coinSwap rPot0Layout δ, ?_⟩; unfold potReflSwap4;
        rw [ite_eq_left hAct];
      exact writeReg_rPotCoin41_routedKet α c z _
  · refine ⟨z, ?_⟩; unfold potReflSwap4; exact ite_eq_right hAct
/-- Reflected `98-T` Stage-4 unitary (`isCsel : Bool`) preserves `IsRoutedKet`. -/
theorem uStage4ReflZeroNErem2m1_98_preserves_routed {decodeCoin : Fin (2 ^ 41) → ZeroNEremSector}
    {potExpect : PotExpectFn} (spec : ReflPotSliceSpec potExpect) (isCsel : Bool)
    (γ : BitAssignment dLayout) (hγ : IsRoutedKet decodeCoin γ) :
    inKetPred (IsRoutedKet decodeCoin)
    ((if isCsel then uStage4ReflZeroNErem2m1_98CatCsel spec else uStage4ReflZeroNErem2m1_98CatUsel
    spec).1.mulVec (ket γ)) := by
  have hUsel : inKetPred (IsRoutedKet decodeCoin)
      ((uStage4ReflZeroNErem2m1_98CatUsel spec).1.mulVec (ket γ)) := by
    obtain ⟨α, c, z, hα, rfl⟩ := hγ
    obtain ⟨z', hz'⟩ := potReflSwap4_routedKet (decodeCoin := decodeCoin) spec α c z
    unfold uStage4ReflZeroNErem2m1_98CatUsel uPotReflIdealZeroNErem
    rw [Submonoid.coe_mul, ← Matrix.mulVec_mulVec, uPotReflZeroNErem_mulVec_ket, hz',
        Matrix.mulVec_smul]
    exact inKetPred_smul _ (uAlignedKinCat2m1_98Usel_preserves_routed _ ⟨α, c, z', hα, rfl⟩)
  cases isCsel
  · exact hUsel
  · change inKetPred (IsRoutedKet decodeCoin)
        ((uStage4ReflZeroNErem2m1_98CatCsel spec).1.mulVec (ket γ))
    rw [(uStage4ReflZeroNErem2m1_98Layout_props spec).1, Matrix.add_mulVec, Matrix.sub_mulVec,
        Matrix.one_mulVec,
      ← Matrix.mulVec_mulVec]
    exact inKetPred_add (inKetPred_sub (inKetPred_ket hγ)
        (projOneQ_inKetPred (inKetPred_ket hγ)))
      (projOneQ_inKetPred hUsel)
/--
Clean-scratch commutation `pScr * U = U * pScr` for unguarded reflected `98-T` `preConj` .
-/
theorem comm_pScr_refl2m1_98UselPre {wIn : ℕ} {decodeCoin : Fin (2 ^ 41) → ZeroNEremSector}
    {potExpect : PotExpectFn} (o1 : Stage1ZeroNEremLayout wIn decodeCoin)
    (spec : ReflPotSliceSpec potExpect) : pScr *
    (preConj o1.uLocal (uStage4ReflZeroNErem2m1_98CatUsel spec)).1 =
    (preConj o1.uLocal (uStage4ReflZeroNErem2m1_98CatUsel spec)).1 * pScr := by
  let uMid := (wNoHad o1.uLocal)⁻¹ * uStage4ReflZeroNErem2m1_98CatUsel spec * wNoHad o1.uLocal
  have hMid : pScr * uMid.1 = uMid.1 * pScr := comm_pScr_of_cleanKet uMid fun α hα ↦ by
    let c := outerCoinOf82 (fun i ↦ α (rLcu82Layout i))
    let z := innerBitsOf82 (fun i ↦ α (rLcu82Layout i))
    have hFwd : (wNoHad o1.uLocal).1.mulVec (ket α) = ket (routedKet decodeCoin α c z) :=
        (congrArg
      (wNoHad o1.uLocal).1.mulVec (congrArg ket (routedStage0_self α).symm)).trans
          (wNoHad_mulVec_ket o1 hα c z)
    dsimp only [uMid]
    rw [Submonoid.coe_mul, Submonoid.coe_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hFwd]
    refine inKetPred_mulVec ((wNoHad o1.uLocal)⁻¹).1 (fun γ ⟨β', c', z', hScr', hEq⟩ ↦ ?_)
      (uStage4ReflZeroNErem2m1_98_preserves_routed spec false _ ⟨α, c, z, hα, rfl⟩)
    rw [hEq, wNoHad_inv_mulVec_ket o1 hScr' c' z'];
        exact inKetPred_ket (cleanScr_routedStage0 hScr' c' z')
  have hW : (preConj o1.uLocal (uStage4ReflZeroNErem2m1_98CatUsel spec)).1 = (uHad82Layout⁻¹).1 *
      uMid.1 * uHad82Layout.1 := by
    unfold preConj wFull; rw [_root_.mul_inv_rev]; simp only [Submonoid.coe_mul,
        Matrix.mul_assoc, uMid]
  rw [hW]; exact conj_uHad82_comm_pScr uMid.1 hMid
/--
Clean-scratch commutation `pScr * C = C * pScr` for controlled reflected `98-T` `preConj` .
-/
theorem comm_pScr_refl2m1_98CselPre {wIn : ℕ} {decodeCoin : Fin (2 ^ 41) → ZeroNEremSector}
    {potExpect : PotExpectFn} (o1 : Stage1ZeroNEremLayout wIn decodeCoin)
    (spec : ReflPotSliceSpec potExpect) : pScr *
    (preConj o1.uLocal (uStage4ReflZeroNErem2m1_98CatCsel spec)).1 =
    (preConj o1.uLocal (uStage4ReflZeroNErem2m1_98CatCsel spec)).1 * pScr :=
  comm_proj_of_ctrl pScr _ _ _ (pScr_comm_off hoff_wLocQ (compProj 1)).eq
    (comm_pScr_refl2m1_98UselPre o1 spec)
    (unitary_conj_ctrl (wFull o1.uLocal) _ _ _ (wFull_comm_off o1 hoff_wLocQ (compProj 1)).eq
      (uStage4ReflZeroNErem2m1_98Layout_props spec).1)
/-- Clean-scratch commutation `pScr * S = S * pScr` for ideal reflected `preConj`. -/
theorem comm_pScr_refl2m1_IdPre {wIn : ℕ} {decodeCoin : Fin (2 ^ 41) → ZeroNEremSector}
    {potExpect : PotExpectFn} (o1 : Stage1ZeroNEremLayout wIn decodeCoin)
    (spec : ReflPotSliceSpec potExpect) : pScr *
    (preConj o1.uLocal (uStage4ReflZeroNErem2m1Ideal spec)).1 =
    (preConj o1.uLocal (uStage4ReflZeroNErem2m1Ideal spec)).1 * pScr :=
  comm_pScr_id_of_usel o1 _ _ (fun r M hoff ↦
      (uStage4ReflZeroNErem2m1_98Layout_props spec).2.2 r hoff M)
    (unitary_conj_mul_right (wFull o1.uLocal) _ _ _
      (wFull_comm_off o1 hoff_cat8_layout _).eq (uStage4ReflZeroNErem2m1_98Layout_props spec).2.1)
    (comm_pScr_refl2m1_98UselPre o1 spec)
open PhotochemistrySolution.SplitRouter47_187 PhotochemistrySolution.QubitizationWalkSem
/-- Pre-restriction `SELECT^2 = I` involutivity on clean scratch `pScr` for `ReflPotSliceSpec`. -/
theorem rawIdealSelectReflZeroNErem_2m1_invol {wIn : ℕ}
    {decodeCoin : Fin (2 ^ 41) → ZeroNEremSector} {potExpect : PotExpectFn}
    (o1 : Stage1ZeroNEremLayout wIn decodeCoin) (spec : ReflPotSliceSpec potExpect) :
    (preConj o1.uLocal (uStage4ReflZeroNErem2m1Ideal spec)).1 *
    ((preConj o1.uLocal (uStage4ReflZeroNErem2m1Ideal spec)).1 * pScr) = pScr := by
  let M := uStage4ReflZeroNErem2m1Ideal spec
  let W := wNoHad o1.uLocal
  let N := W⁻¹ * M * W
  have hNoHad : N.1 * (N.1 * pScr) = pScr := matrix_ext_ket fun β ↦ by
    change (N.1 * (N.1 * rScrLayout.basisOutcomeProjector 0)).mulVec (ket β) =
        (rScrLayout.basisOutcomeProjector 0).mulVec (ket β)
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
        SelectRefl.ket_basisOutcomeProjector_zero rScrLayout β]
    by_cases hScr : ∀ m : Fin scrLLayout, β (rScrLayout m) = 0
    · rw [ifPosSqf hScr]
      let c := outerCoinOf82 (fun i ↦ β (rLcu82Layout i))
      let z := innerBitsOf82 (fun i ↦ β (rLcu82Layout i))
      let γ := routedKet decodeCoin β c z
      have hSec :=
          uStage4ReflZeroNErem2m1Ideal_sector_and_invol spec γ (routedKet_workInner hScr c z ⟨22,
          fin22_lt_521_pot⟩)
      have hSqγ : M.1.mulVec (M.1.mulVec (ket γ)) = ket γ :=
        (routedKet_sector_flags (decodeCoin := decodeCoin) hScr c z).elim (fun ⟨hf, hk⟩ ↦
            (hSec.1 hf hk).2)
          (fun h ↦ h.elim (fun ⟨hf, hk⟩ ↦ (hSec.2.1 hf hk).2) (fun ⟨hf, hk⟩ ↦ (hSec.2.2 hf hk).2))
      dsimp only [N]; simp only [Submonoid.coe_mul, ← Matrix.mulVec_mulVec]
      rw [show W.1.mulVec (ket β) =
          ket γ by rw [← routedStage0_self β]; exact wNoHad_mulVec_ket o1 hScr c z,
        Matrix.mulVec_mulVec _ W.1 (W⁻¹).1, show W.1 * (W⁻¹).1 =
            1 from congrArg Subtype.val (mul_inv_cancel W),
        Matrix.one_mulVec, hSqγ, ← routedStage0_self β, wNoHad_inv_mulVec_ket o1 hScr c z,
            routedStage0_self]
    · rw [ifNegSqf hScr, Matrix.mulVec_zero, Matrix.mulVec_zero]
  have hW : (preConj o1.uLocal M).1 = (uHad82Layout⁻¹).1 * N.1 * uHad82Layout.1 := by
    unfold preConj wFull; rw [_root_.mul_inv_rev]; simp only [Submonoid.coe_mul,
        Matrix.mul_assoc, N, W]
  rw [hW]; simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc uHad82Layout.1 (uHad82Layout⁻¹).1,
    show uHad82Layout.1 * (uHad82Layout⁻¹).1 =
        1 from congrArg Subtype.val (mul_inv_cancel uHad82Layout),
    one_mul, comm_pScr_uHad82.eq, ← Matrix.mul_assoc N.1 pScr, ← Matrix.mul_assoc N.1 (N.1 *
        pScr), hNoHad,
    ← comm_pScr_uHad82.eq, ← Matrix.mul_assoc (uHad82Layout⁻¹).1 uHad82Layout.1,
    show (uHad82Layout⁻¹).1 * uHad82Layout.1 =
        1 from congrArg Subtype.val (inv_mul_cancel uHad82Layout), one_mul]
/-- Reflected `(2m+1)` Stage-4 ideal unitary conjugated by `wNoHad o1.uLocal`. -/
def noHadMidRefl2m1 {wIn : ℕ} {decodeCoin : Fin (2 ^ 41) → ZeroNEremSector}
    {potExpect : PotExpectFn} (o1 : Stage1ZeroNEremLayout wIn decodeCoin)
    (spec : ReflPotSliceSpec potExpect) : Operator (2 ^ dLayout) :=
    ((wNoHad o1.uLocal)⁻¹ * uStage4ReflZeroNErem2m1Ideal spec * wNoHad o1.uLocal).1
theorem noHadMidRefl2m1_pot_ket {wIn : ℕ} {decodeCoin : Fin (2 ^ 41) → ZeroNEremSector}
    {potExpect : PotExpectFn} (o1 : Stage1ZeroNEremLayout wIn decodeCoin)
    (spec : ReflPotSliceSpec potExpect) {β : BitAssignment dLayout}
    (hr0 : ∀ i, β (rLcu82Layout i) = 0) (hScr : ∀ m, β (rScrLayout m) = 0) (c : Fin (2 ^ 41))
    (z z' : BitAssignment 41) (s : ℂ)
    (hK4 : (uStage4ReflZeroNErem2m1Ideal spec).1.mulVec (ket (routedKet decodeCoin β c z)) =
    s • ket (routedKet decodeCoin β c z')) : (rLcu82Layout.basisOutcomeProjector 0 *
    (uHad82Layout⁻¹).1).mulVec ((noHadMidRefl2m1 o1 spec).mulVec (ket (routedStage0 β c z))) =
    s • ((sqrtHalf ^ 82) • ket β) := by
  unfold noHadMidRefl2m1; rw [Submonoid.coe_mul, Submonoid.coe_mul,
    mulVec_chain3 _ _ _ _ _ _ s (wNoHad_mulVec_ket o1 hScr c z) hK4,
        wNoHad_inv_mulVec_ket o1 hScr c z',
    Matrix.mulVec_smul, proj_had82_ket_routedStage0 hr0 c z']
theorem sum_z41_pot_refl_general {wIn : ℕ} {decodeCoin : Fin (2 ^ 41) → ZeroNEremSector}
    {potExpect : PotExpectFn} (o1 : Stage1ZeroNEremLayout wIn decodeCoin)
    (spec : ReflPotSliceSpec potExpect) {β : BitAssignment dLayout}
    (hr0 : ∀ u, β (rLcu82Layout u) = 0) (hScr : CleanScr β) (c : Fin (2 ^ 41)) (isSc isNN : Bool)
    (sp1 sp2 : Fin 4) (nA nB eA eB : Fin 3 → Fin 256) (hf1 : routedKet decodeCoin β c 0 wIsFine =
    1) (hk0 : routedKet decodeCoin β c 0 wIsKin = 0)
    (hSc : (routedKet decodeCoin β c 0 (wPotIsScreen rPot0Layout) == 1) = isSc)
    (hNNb : (routedKet decodeCoin β c 0 (wPotIsNN rPot0Layout) == 1) = isNN)
    (hSp1 : speciesOfBits2 (routedKet decodeCoin β c 0 (wPotSp1B0 rPot0Layout))
    (routedKet decodeCoin β c 0 (wPotSp1B1 rPot0Layout)) = sp1)
    (hSp2 : speciesOfBits2 (routedKet decodeCoin β c 0 (wPotSp2B0 rPot0Layout))
    (routedKet decodeCoin β c 0 (wPotSp2B1 rPot0Layout)) = sp2)
    (hNA : coordOfReg24 (rPotNucA rPot0Layout) (routedKet decodeCoin β c 0) = nA)
    (hNB : coordOfReg24 (rPotNucB rPot0Layout) (routedKet decodeCoin β c 0) = nB)
    (hEA : coordOfReg24 (rPotElecA rPot0Layout) (routedKet decodeCoin β c 0) = eA)
    (hEB : coordOfReg24 (rPotElecB rPot0Layout) (routedKet decodeCoin β c 0) = eB) :
    (∑ z : BitAssignment 41, (rLcu82Layout.basisOutcomeProjector 0 *
    (uHad82Layout⁻¹).1).mulVec ((noHadMidRefl2m1 o1 spec).mulVec (ket (routedStage0 β c z)))) =
    ((2 ^ 41 : ℂ) * (potExpect isSc isNN sp1 sp2 nA nB eA eB : ℂ)) • ((sqrtHalf ^ 82) • ket β) := by
  let δ₀ := routedKet decodeCoin β c 0
  have hKeep (z : BitAssignment 41) (w : Wire dLayout) (hw : w.val < 7256) :
      routedKet decodeCoin β c z w = δ₀ w := by
    rw [routedKet_eq_writeReg_z decodeCoin β c z]
    exact writeReg_apply_of_not_mem δ₀ rInner41Layout z w fun ⟨m, hm⟩ ↦ by
      have hv := congrArg Fin.val hm; rw [val_rInner41Layout] at hv; omega
  have hterm (z : BitAssignment 41) :=
    let δ := routedKet decodeCoin β c z
    let z' := potOracleCoinEval spec.coinSwap rPot0Layout δ
    have hf1z :=
        (hKeep z wIsFine (by dsimp [wIsFine]; rw [val_rOut40Layout]; omega)).trans hf1
    have hk0z := (hKeep z wIsKin (by dsimp [wIsKin]; rw [val_rOut40Layout]; omega)).trans hk0
    have hK4_raw := ((uStage4ReflZeroNErem2m1Ideal_sector_and_invol spec δ
      (routedKet_workInner hScr c z ⟨22, fin22_lt_521_pot⟩)).2.1 hf1z hk0z).1
    have hkP (k : ℕ) (hk : 1 ≤ k ∧ k < 105) := hKeep z (rPot0Layout ⟨k, by omega⟩) (by
      change (potZeroNEremWireFn 0 pot0_le_690 ⟨k, by omega⟩).val < 7256
      rw [val_potZeroNEremWireFn pot0_le_690]; dsimp only; split_ifs <;> omega)
    have hC24 (off : ℕ) (h0 : off + 24 ≤ 146 + 0) (_ho : 9 ≤ off ∧ off ≤ 81) :
        coordOfReg24 (rPot0Layout.compose (QRegister.block off 24 h0)) δ =
          coordOfReg24 (rPot0Layout.compose (QRegister.block off 24 h0)) δ₀ :=
      funext fun ax ↦ congrArg Stage4Cluster22Xnor.byteOfBits <| funext fun k ↦
        hkP (off + (8 * ax.val + k.val)) (by have := PotSelectWiring.coordOfReg24_lt ax k; omega)
    have hZ : (fun m : Fin 41 ↦ δ (rPotCoin41 rPot0Layout m)) = z :=
      funext fun m ↦
          (congrArg δ (rPot0_ports_eq.2.2.2.2.2.2 m)).trans (routedKet_rInner41 decodeCoin β c
          z m)
    have hEval : potOracleBitEval spec.phaseBit rPot0Layout δ =
        spec.phaseBit isSc isNN sp1 sp2 nA nB eA eB z := by
      dsimp only [potOracleBitEval]; rw [hZ]; dsimp only [δ]
      rw [hkP 1 (by omega), hkP 4 (by omega), hkP 5 (by omega), hkP 6 (by omega), hkP 7 (by omega),
          hkP 8 (by omega),
        hC24 9 potBlkNucA_le (by omega), hC24 33 potBlkNucB_le (by omega),
        hC24 57 potBlkElecA_le (by omega), hC24 81 potBlkElecB_le (by omega)]
      dsimp only [δ₀]; rw [hSc, hNNb, hSp1, hSp2, hNA, hNB, hEA, hEB]
    noHadMidRefl2m1_pot_ket o1 spec hr0 hScr c z z' (bitSign (spec.phaseBit isSc isNN sp1 sp2 nA
        nB eA eB z))
      (by rw [hK4_raw, writeReg_rPotCoin41_routedKet β c z z', hEval])
  simp_rw [hterm, ← Finset.sum_smul]
  rw [← spec.avg_coin41, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero 41 two_ne_zero), one_mul]
end Walk1a

section Walk1
set_option exponentiation.threshold 256
open PhotochemistrySolution.SplitRouter47_187 PhotochemistrySolution.ZeroNEremSpec
  PhotochemistrySolution.GenWeightsSelect
open PhotochemistrySolution.Kinetic664 PhotochemistrySolution.TelescopeSlice
  PhotochemistrySolution.BlockApprox
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB (ket)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.QubitizationWalkSem (bitSign sqrtHalf)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SelectDataBuilder
  (embedMatrix_mulVec_ket_sym readRegIdx)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SelectQft8GidneyStg3 (qft8Stg3IdealU)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinNormSlice (kinNormOp)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Stage4KinFull (kinAxisShiftedOp
    bAxisMux27)
set_option allowUnsafeReducibility true in
attribute [local irreducible] abpKin15SqFree2m1Usel kin2m1OutBit bAxisMux27
/-- Local 8-qubit QFT sandwich matrix of `uKinMid2m1UselLayout` on fiber `δ`. -/
def kinMidQft8Mat2m1 (δ : BitAssignment dLayout) : Operator (2 ^ 8) :=
  (QFT.qftMatrix 8)ᴴ *
    Matrix.diagonal (fun k : Fin 256 ↦
      bitSign (kin2m1OutBit (fun j ↦ DynCircExt.writeReg δ rPKinLayout (basisBits 8 k)
          (rKin226Layout j)))) *
    QFT.qftMatrix 8
theorem sum_z41_kin_2m1 {wIn : ℕ} {decodeCoin : Fin (2 ^ 41) → ZeroNEremSector}
    {potExpect : PotExpectFn}
    (o1 : Stage1ZeroNEremLayout wIn decodeCoin) (spec : ReflPotSliceSpec potExpect)
    {β : BitAssignment dLayout} (hr0 : ∀ u, β (rLcu82Layout u) = 0)
        (hScr : ∀ m, β (rScrLayout m) = 0)
    {c : Fin (2 ^ 41)} {i : Particle_frozen} {ax : Fin 3} (hc : decodeCoin c = .kin i ax) :
    (∑ z : BitAssignment 41,
      (rLcu82Layout.basisOutcomeProjector 0 * (uHad82Layout⁻¹).1).mulVec
        ((noHadMidRefl2m1 o1 spec).mulVec (ket (routedStage0 β c z)))) =
      (sqrtHalf ^ 82) • (rSysLayout.embedMatrix ((2 ^ 41 : ℂ) • kinNormOp i ax)).mulVec (ket β)
          := by
  let rSC := rSysLayout.compose (coordinateRegister_frozen i ax)
  let σ₀ := kinFwdBits (routedKet decodeCoin β c 0)
  have hterm (z : BitAssignment 41) : (rLcu82Layout.basisOutcomeProjector 0 *
      (uHad82Layout⁻¹).1).mulVec
      ((noHadMidRefl2m1 o1 spec).mulVec (ket (routedStage0 β c z))) =
      (sqrtHalf ^ 82) • (rSC.embedMatrix (kinMidQft8Mat2m1 (kinFwdBits (routedKet decodeCoin β c
          z)))).mulVec (ket β) := by
    let δ := routedKet decodeCoin β c z
    obtain ⟨_, _, _, _, _, _, fFine, fKin, _, _⟩ := packOut40_kin i ax δ fun m ↦
        (routedKet_out40 hScr c z m).trans (hc ▸ rfl)
    have hK4 := ((uStage4ReflZeroNErem2m1Ideal_sector_and_invol spec δ
      (routedKet_workInner hScr c z ⟨22, fin22_lt_521_pot⟩)).2.2 fFine fKin).1
    obtain ⟨hRead, hComm⟩ := kinFwdBits_kin_comm hScr hc z
    have hIdx : readRegIdx rPKinLayout (kinFwdBits δ) = readRegIdx rSC β :=
      congrArg (basisBitsEquiv 8).symm (funext fun b ↦
          ((congrFun ((basisBitsEquiv dLayout).apply_symm_apply (kinFwdBits δ))
        (rPKinLayout.wires b)).trans (hRead b)).trans
            (congrFun ((basisBitsEquiv dLayout).apply_symm_apply β) (rSC.wires b)).symm)
    have hk_step (k : Fin 256) : (rLcu82Layout.basisOutcomeProjector 0 * (uHad82Layout⁻¹).1).mulVec
        (((uKinFwd o1)⁻¹).1.mulVec (kinMidQft8Mat2m1 (kinFwdBits δ) k (readRegIdx rSC β) •
          ket (writeReg (kinFwdBits δ) rPKinLayout (basisBits 8 k)))) =
        (sqrtHalf ^ 82) • (kinMidQft8Mat2m1 (kinFwdBits δ) k (readRegIdx rSC β) • ket (writeReg β
            rSC (basisBits 8 k))) := by
      have hScr_k (m : Fin scrLLayout) :=
          (writeReg_rSC_rScr β i ax (basisBits 8 k) m).trans (hScr m)
      have hr0_k (u : Fin (mLayout + 2)) :=
          (writeReg_apply_of_not_mem β rSC (basisBits 8 k) (rLcu82Layout u) fun ⟨q, hq⟩ ↦ by
        have hv : ((rSysLayout.compose (coordinateRegister_frozen i ax)) q).val =
            (rLcu82Layout.wires u).val := congrArg Fin.val hq
        have := rSC_wire_lt_5616 i ax q; rw [val_rLcu82Layout] at hv; omega).trans (hr0 u)
      rw [Matrix.mulVec_smul, hComm k, inv_mulVec_of_fwd (uKinFwd o1)
          (uKinFwd_mulVec_ket o1 hScr_k c z),
        Matrix.mulVec_smul, proj_had82_ket_routedStage0 hr0_k c z, smul_comm]
    exact (kin_conj_mid_mulVec (wNoHad o1.uLocal)
        (uStage4ReflZeroNErem2m1Ideal spec) uAlignedKinIdeal2m1Layout
      (uKinFwd o1) ((qft8Stg3IdealU scrWLayout rPKinLayout)⁻¹ * uKinMid2m1UselLayout *
          qft8Stg3IdealU scrWLayout rPKinLayout)
      (rLcu82Layout.basisOutcomeProjector 0 * (uHad82Layout⁻¹).1) (ket (routedStage0 β c z))
          (ket δ) (ket (kinFwdBits δ)) _ _
      (sqrtHalf ^ 82) (wNoHad_mulVec_ket o1 hScr c z) hK4
      (conj4_group uMux27Layout uSpeciesSwap50Layout uKinAlign0Layout (wNoHad o1.uLocal) _)
          (uKinFwd_mulVec_ket o1 hScr c z)
      ((qft8_conj_phaseDiag_mulVec_ket rPKinLayout (qft8Stg3IdealU scrWLayout rPKinLayout)
          uKinMid2m1UselLayout
        ((QRegister.embedUnitary_val rPKinLayout qftGridUnitary).trans rfl)
        (fun γ ↦ bitSign (kin2m1OutBit (fun j ↦
            γ (rKin226Layout j)))) uKinMid2m1_isPhaseDiag_layout (kinFwdBits δ)).trans
        ((embedMatrix_mulVec_ket_sym rPKinLayout _ (kinFwdBits δ)).trans (by rw [hIdx]; rfl)))
            hk_step).trans
      (congrArg ((sqrtHalf ^ 82) • ·) (embedMatrix_mulVec_ket_sym rSC _ β).symm)
  simp_rw [hterm, ← Finset.smul_sum, ← Matrix.sum_mulVec, ← rSC.embedMatrix_sum]
  have hSwapReg (z : BitAssignment 41) (k : Fin 256) :
      writeReg (kinFwdBits (routedKet decodeCoin β c z)) rPKinLayout (basisBits 8 k) =
        writeReg (writeReg σ₀ rPKinLayout (basisBits 8 k)) rInner41Layout z := by
    rw [routedKet_eq_writeReg_z decodeCoin β c z, kinFwdBits_writeReg_z]
    exact writeReg_comm_of_ne rInner41Layout rPKinLayout
      (fun m b e ↦
          by have hv :=
               congrArg Fin.val e; rw [val_rInner41Layout, val_rPKinLayout] at hv;
               omega) σ₀ z (basisBits 8 k)
  have hσ_eq (w : Wire dLayout) (hw : w.val < 5755 ∨ 6105 ≤ w.val) :
      σ₀ w = routedKet decodeCoin β c 0 w := by
    unfold σ₀ kinFwdBits muxBits
    rw [writeReg_apply_of_not_mem _ rMux27Layout _ w fun ⟨j, hj⟩ ↦ by
        have hv := congrArg Fin.val hj; have hm : (rMux27Layout j).val = _ := val_mux27WireFn j
        rw [hm] at hv; split_ifs at hv <;> omega,
      speciesSwapBits_outside _ (by omega)
          (by omega), fwdBits_not_target targetsIn_pKinAlign0 _ (by omega)]
  have hσ_isk : σ₀ wIsKin = 1 :=
    (hσ_eq wIsKin (by dsimp [wIsKin]; rw [val_rOut40Layout]; omega)).trans
      (packOut40_kin i ax (routedKet decodeCoin β c 0) fun m ↦
          (routedKet_out40 hScr c 0 m).trans (hc ▸ rfl)).2.2.2.2.2.2.2.1
  have hσ_scr (m : Fin 521) (hm : 22 ≤ m.val) : σ₀ (rWorkInnerLayout m) = 0 :=
    (hσ_eq _ (by rw [val_rWorkInnerLayout]; omega)).trans (routedKet_workInner hScr c 0 m)
  have hMatEq : (∑ z : BitAssignment 41,
      kinMidQft8Mat2m1 (kinFwdBits (routedKet decodeCoin β c z))) =
      (2 ^ 41 : ℂ) • kinAxisShiftedOp :=
    (Finset.sum_congr rfl fun z _ ↦ by
      unfold kinMidQft8Mat2m1
      exact congrArg (fun M ↦ (QFT.qftMatrix 8)ᴴ * M * QFT.qftMatrix 8) (congrArg Matrix.diagonal
        (funext fun k ↦ congrArg bitSign (congrArg kin2m1OutBit (funext fun j ↦
            by rw [hSwapReg z k]))))).trans
      (sum_z41_qft8_kin2m1OutBit_matrix σ₀ hσ_isk hσ_scr)
  rw [hMatEq, rSC.embedMatrix_smul, rSysLayout.embedMatrix_smul,
      (show rSC.embedMatrix kinAxisShiftedOp = rSysLayout.embedMatrix
        (kinNormOp i ax) from QRegister.embedMatrix_compose rSysLayout (coordinateRegister_frozen
            i ax) kinAxisShiftedOp)]
/-- Arbitrary-weight 41-bit coin sector sum for `uStage4ReflZeroNErem2m1Ideal`. -/
theorem sum_z41_sector_gen_refl_2m1 {wIn : ℕ} {wEE : Fin 4 → ℕ} {wNN : Fin 4 → Fin 4 → ℕ}
    {wEN : Fin 4 → ℕ} {wKin : Particle_frozen → ℕ} {wIdle : ℕ}
    {decodeCoin : Fin (2 ^ 41) → ZeroNEremSector} {potExpect : PotExpectFn}
    (o1 : Stage1ZeroNEremLayout wIn decodeCoin) (spec : ReflPotSliceSpec potExpect)
    (hCoin : ValidGenZeroNEremCoin wEE wNN wEN wKin wIdle decodeCoin) {β : BitAssignment dLayout}
    (hr0 : ∀ u, β (rLcu82Layout u) = 0) (hScr : CleanScr β) (c : Fin (2 ^ 41)) :
    (∑ z : BitAssignment 41, (rLcu82Layout.basisOutcomeProjector 0 *
    (uHad82Layout⁻¹).1).mulVec ((noHadMidRefl2m1 o1 spec).mulVec (ket (routedStage0 β c z)))) =
    (sqrtHalf ^ 82) • (rSysLayout.embedMatrix (bOuterZeroNErem decodeCoin potExpect c)).mulVec
    (ket β) := by
  have hLoc : readRegIdx rSysLayout β = PhotochemistrySolution.KinB.localIdx rSysLayout β :=
    congrArg (basisBitsEquiv systemQubits_frozen).symm (funext fun j ↦
        congrFun ((basisBitsEquiv dLayout).apply_symm_apply β)
      (rSysLayout.wires j))
  let δ := routedKet decodeCoin β c 0
  obtain ⟨hVN, hKE, hVE, _, hLoN, hHiN⟩ := validRouter_stage1 (decodeCoin := decodeCoin) hScr c 0
  obtain ⟨kSN, kSE⟩ := routedBuf_keep_stage1 (decodeCoin := decodeCoin) hScr c 0
  obtain ⟨p2B0, p2B1, pNA, pNB, pEA, pEB, _⟩ := rPot0_ports_eq
  have hIdxE := idxValD_elec_stage2_eq hKE
  have cNA : ∀ (n1 : Fin 47), (∀ b, routedStage2 decodeCoin β c 0 (rBufLo rNucLayout b) =
      routedStage1 decodeCoin β c 0
    (rSys rNucLayout n1 b)) →
      coordOfReg24 (rPotNucA rPot0Layout) δ = sysCoord (readRegIdx rSysLayout β) (nucParticle n1) :=
    fun n1 sLoN ↦ coordOfReg24_sysCoord _ δ β (nucParticle n1) fun ax k ↦
      (congrArg δ (pNA _)).trans ((hLoN _).trans ((sLoN _).trans ((kSN n1 _).trans (congrArg β
        (rSys_nuc_eq_sysCoord n1 ax k)))))
  have cEA (e1 : Fin 187) (sLoE : ∀ b, δ (rBufLo rElecLayout b) =
      routedStage2 decodeCoin β c 0 (rSys rElecLayout e1 b)) :
      coordOfReg24 (rPotElecA rPot0Layout) δ = sysCoord (readRegIdx rSysLayout β) (elecParticle e1)
          :=
    coordOfReg24_sysCoord _ δ β (elecParticle e1) fun ax k ↦
      (congrArg δ (pEA _)).trans ((sLoE _).trans ((kSE e1 _).trans (congrArg β
          (rSys_elec_eq_sysCoord e1 ax k))))
  have hF1 (hn2 he2 isSc isNN : Bool) (n1 : Fin 47) (in2 : ℕ) (e1 : Fin 187) (ie2 : ℕ) (sp2 : Fin 4)
      (h2 : in2 < 64) (h4 : ie2 < 256)
      (hM : ∀ j : Fin 40, outMaskBits40 (decodeCoin c) j =
        if (packOut40ZeroNErem true hn2 n1.val in2 true he2 e1.val ie2 isSc true false isNN
          (nucSpecies n1).val sp2.val).testBit j.val then 1 else 0) :=
    packOut40ZeroNErem_fields true hn2 n1.val in2 true he2 e1.val ie2 isSc true false isNN
      (nucSpecies n1).val sp2.val (by omega) h2 (by omega) h4 (routedStage1 decodeCoin β c 0)
      fun j ↦ (writeReg_apply_reg _ rOut40Layout _ j).trans (hM j)
  have hPot (hn2 he2 isSc isNN : Bool) (n1 : Fin 47) (in2 : ℕ) (e1 : Fin 187) (ie2 : ℕ)
      (sp2 : Fin 4)
      {nB eB : Fin 3 → Fin 256} (h2 : in2 < 64) (h4 : ie2 < 256)
      (hM : ∀ j : Fin 40, outMaskBits40 (decodeCoin c) j =
        if (packOut40ZeroNErem true hn2 n1.val in2 true he2 e1.val ie2 isSc true false isNN
          (nucSpecies n1).val sp2.val).testBit j.val then 1 else 0)
      (sLoN : ∀ b, routedStage2 decodeCoin β c 0 (rBufLo rNucLayout b) =
        routedStage1 decodeCoin β c 0 (rSys rNucLayout n1 b))
      (hNB : coordOfReg24 (rPotNucB rPot0Layout) δ = nB)
      (sLoE : ∀ b, δ (rBufLo rElecLayout b) =
          routedStage2 decodeCoin β c 0 (rSys rElecLayout e1 b))
      (hEB : coordOfReg24 (rPotElecB rPot0Layout) δ = eB)
      (hB : bOuterZeroNErem decodeCoin potExpect c =
        (2 ^ 41 : ℂ) • SelectApprox.diagReal (potTermZeroNErem decodeCoin potExpect c))
      (hVal : potTermZeroNErem decodeCoin potExpect c (readRegIdx rSysLayout β) =
        potExpect isSc isNN (nucSpecies n1) sp2
          (sysCoord (readRegIdx rSysLayout β) (nucParticle n1)) nB
          (sysCoord (readRegIdx rSysLayout β) (elecParticle e1)) eB) :
      (∑ z : BitAssignment 41, (rLcu82Layout.basisOutcomeProjector 0 * (uHad82Layout⁻¹).1).mulVec
        ((noHadMidRefl2m1 o1 spec).mulVec (ket (routedStage0 β c z)))) =
        (sqrtHalf ^ 82) • (rSysLayout.embedMatrix (bOuterZeroNErem decodeCoin potExpect c)).mulVec
            (ket β) := by
    obtain ⟨_, _, _, _, _, _, _, _, hScrF, hFine, hKin, hIsNN, hSp1B0, hSp1B1, hAx0, hAx1⟩ :=
      packOut40ZeroNErem_fields true hn2 n1.val in2 true he2 e1.val ie2 isSc true false isNN
        (nucSpecies n1).val sp2.val (by omega) h2 (by omega) h4 (routedKet decodeCoin β c 0)
        fun j ↦ (routedKet_out40 hScr c 0 j).trans (hM j)
    rw [sum_z41_pot_refl_general o1 spec hr0 hScr c isSc isNN (nucSpecies n1) sp2 _ nB _ eB hFine
        hKin
      (by rw [hScrF]; cases isSc <;> rfl) (by rw [hIsNN]; cases isNN <;> rfl)
      (by rw [hSp1B0, hSp1B1]; exact speciesOfBits2_of_fin4 (nucSpecies n1))
      (by rw [p2B0, p2B1, hAx0, hAx1]; exact speciesOfBits2_of_fin4 sp2)
      (cNA n1 sLoN) hNB (cEA e1 sLoE) hEB,
      hB, rSysLayout.embedMatrix_smul, Matrix.smul_mulVec, embed_diagReal_mulVec_ket, smul_smul,
          smul_smul, smul_smul]
    exact congrArg (· • ket β) (by rw [← hLoc, hVal]; ring)
  match hc : decodeCoin c with
  | .idle =>
      have hterm (z : BitAssignment 41) :=
        let δz := routedKet decodeCoin β c z
        have F :=
            packOut40ZeroNErem_fields false false 0 0 false false 0 0 false false false false 0 0
            (by omega)
          (by omega) (by omega) (by omega) δz fun j ↦
              (routedKet_out40 hScr c z j).trans (hc ▸ rfl)
        (noHadMidRefl2m1_pot_ket o1 spec hr0 hScr c z z 1
          (((uStage4ReflZeroNErem2m1Ideal_sector_and_invol spec δz (routedKet_workInner hScr c z
              ⟨22, fin22_lt_521_pot⟩)).1
            F.2.2.2.2.2.2.2.2.2.1 F.2.2.2.2.2.2.2.2.2.2.1).1.trans (one_smul ℂ
                (ket δz)).symm)).trans (one_smul ℂ _)
      simp_rw [hterm, Finset.sum_const, Finset.card_univ, show Fintype.card (BitAssignment 41) =
          2 ^ 41 by simp [BitAssignment]]
      unfold bOuterZeroNErem; rw [← Nat.cast_smul_eq_nsmul ℂ (2 ^ 41), Nat.cast_pow,
          Nat.cast_ofNat, hc,
        rSysLayout.embedMatrix_smul, rSysLayout.embedMatrix_one, Matrix.smul_mulVec,
            Matrix.one_mulVec, smul_comm]
  | .kin i ax => unfold bOuterZeroNErem; rw [sum_z41_kin_2m1 o1 spec hr0 hScr hc, hc]
  | .ee n1 e1 e2 =>
      have F1 := hF1 false true true false n1 0 e1 e2.val 0 (by omega) (by omega) fun _ ↦ hc ▸ rfl
      obtain ⟨sLoN, sHiN⟩ := (routerSwapBits_cases rNucLayout hVN).2.1 n1 F1.1 F1.2.1 F1.2.2.1
      obtain ⟨sLoE, sHiE⟩ := (routerSwapBits_cases rElecLayout hVE).2.2 e1 e2 (hCoin.ee_lt hc)
        ((hKE ⟨0, rw_lt0 187 8⟩).trans F1.2.2.2.2.1) ((hKE ⟨1, rw_lt1 187 8⟩).trans F1.2.2.2.2.2.1)
        (hIdxE.1.trans F1.2.2.2.2.2.2.1) (hIdxE.2.trans F1.2.2.2.2.2.2.2.1)
      exact hPot false true true false n1 0 e1 e2.val 0 (by omega) (by omega)
          (fun _ ↦ hc ▸ rfl) sLoN
        (coordOfReg24_zero _ δ fun b ↦ (congrArg δ (pNB b)).trans ((hHiN b).trans (sHiN b))) sLoE
        (coordOfReg24_sysCoord _ δ β (elecParticle e2) fun ax k ↦
            (congrArg δ (pEB _)).trans ((sHiE _).trans
          ((kSE e2 _).trans (congrArg β (rSys_elec_eq_sysCoord e2 ax k)))))
        (by unfold bOuterZeroNErem; rw [hc]) (by unfold potTermZeroNErem; rw [hc])
  | .nn n1 n2 e1 =>
      have F1 :=
          hF1 true false true true n1 n2.val e1 0 (nucSpecies n2) (by omega) (by omega) fun _ ↦
          hc ▸ rfl
      obtain ⟨sLoN, sHiN⟩ :=
          (routerSwapBits_cases rNucLayout hVN).2.2 n1 n2 (hCoin.nn_lt hc) F1.1 F1.2.1 F1.2.2.1
          F1.2.2.2.1
      obtain ⟨sLoE, sHiE⟩ := (routerSwapBits_cases rElecLayout hVE).2.1 e1
        ((hKE ⟨0, rw_lt0 187 8⟩).trans F1.2.2.2.2.1) ((hKE ⟨1, rw_lt1 187 8⟩).trans F1.2.2.2.2.2.1)
            (hIdxE.1.trans F1.2.2.2.2.2.2.1)
      exact hPot true false true true n1 n2.val e1 0 (nucSpecies n2) (by omega) (by omega)
          (fun _ ↦ hc ▸ rfl) sLoN
        (coordOfReg24_sysCoord _ δ β (nucParticle n2) fun ax k ↦
            (congrArg δ (pNB _)).trans ((hHiN _).trans
          ((sHiN _).trans ((kSN n2 _).trans (congrArg β (rSys_nuc_eq_sysCoord n2 ax k)))))) sLoE
        (coordOfReg24_zero _ δ fun b ↦ (congrArg δ (pEB b)).trans (sHiE b))
        (by unfold bOuterZeroNErem; rw [hc]) (by unfold potTermZeroNErem; rw [hc])
  | .en n1 e1 =>
      have F1 := hF1 false false false false n1 0 e1 0 0 (by omega) (by omega) fun _ ↦ hc ▸ rfl
      obtain ⟨sLoN, sHiN⟩ := (routerSwapBits_cases rNucLayout hVN).2.1 n1 F1.1 F1.2.1 F1.2.2.1
      obtain ⟨sLoE, sHiE⟩ := (routerSwapBits_cases rElecLayout hVE).2.1 e1
        ((hKE ⟨0, rw_lt0 187 8⟩).trans F1.2.2.2.2.1) ((hKE ⟨1, rw_lt1 187 8⟩).trans F1.2.2.2.2.2.1)
            (hIdxE.1.trans F1.2.2.2.2.2.2.1)
      exact hPot false false false false n1 0 e1 0 0 (by omega) (by omega) (fun _ ↦ hc ▸ rfl) sLoN
        (coordOfReg24_zero _ δ fun b ↦ (congrArg δ (pNB b)).trans ((hHiN b).trans (sHiN b))) sLoE
        (coordOfReg24_zero _ δ fun b ↦ (congrArg δ (pEB b)).trans (sHiE b))
        (by unfold bOuterZeroNErem; rw [hc]) (by unfold potTermZeroNErem; rw [hc])
end Walk1

section Walk2a
set_option exponentiation.threshold 8192
open PhotochemistrySolution.SelectCompactAnc PhotochemistrySolution.SelectQft8GidneyStg3
open PhotochemistrySolution.ProviderCore PhotochemistrySolution.Qft8PostCancelT5
  PhotochemistrySolution.Coin70Lift
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB (ket matrix_ext_ket)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SelectKin526OneWrap
  (embedUnitary_comm_of_disjoint)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SelectFastQft8Gidney (spliceUnitary
    spliceUnitaryMat)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.XMeasChunkQromUnldA (phaseFlipUnitary)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.PotOracleGen (disj_ne disj_of_ne)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Kinetic664 (abpKin15SqFree2m1Usel
    abpKin15SqFree2m1Csel)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Stage4KinFull (bAxisMux27)
set_option allowUnsafeReducibility true in
attribute [local irreducible] phaseFlipUnitary bSpeciesSwap50 bAxisMux27 qft8PostCancel98CatU
    abpKin15SqFree2m1Usel abpKin15SqFree2m1Csel
theorem uPotReflZeroNErem_comm_coinBand7256 {kCoin : ℕ} {potExpect : PotExpectFn}
    (rC : QRegister kCoin dLayout) (hBand : ∀ j : Fin kCoin, 7143 ≤ (rC j).val ∧ (rC j).val < 7256)
    (spec : ReflPotSliceSpec potExpect) (isCsel : Bool) (M : Operator (2 ^ kCoin)) :
    Commute (uPotReflZeroNErem spec isCsel).1 (rC.embedMatrix M) :=
  uPotReflZeroNErem_comm_of_disj spec isCsel rC (fun j i _ e ↦ by
    have hb :=
        hBand i;
        have hv : (potZeroNEremWireFn 0 pot0_le_690 j).val = (rC i).val := congrArg Fin.val e
    rw [val_potZeroNEremWireFn pot0_le_690] at hv; split_ifs at hv <;> omega) M
theorem uAlignedKin2m1_98_comm_coinBand7256 {kCoin : ℕ} (rC : QRegister kCoin dLayout)
    (hBand : ∀ j : Fin kCoin, 7143 ≤ (rC j).val ∧ (rC j).val < 7256) (M : Operator (2 ^ kCoin)) :
    Commute uAlignedKinIdeal2m1Layout.1 (rC.embedMatrix M) ∧
    Commute uAlignedKinCat2m1_98UselLayout.1 (rC.embedMatrix M) ∧
    Commute uAlignedKinCat2m1_98CselLayout.1 (rC.embedMatrix M) :=
  uAlignedKin2m1_98_comm_band rC (fun j ↦ Or.inr (hBand j)) M
theorem uStage4ReflZeroNErem2m1_98_comm_coinBand7256 {kCoin : ℕ} {potExpect : PotExpectFn}
    (rC : QRegister kCoin dLayout)
    (hBand : ∀ j : Fin kCoin, 7143 ≤ (rC j).val ∧ (rC j).val < 7256)
        (spec : ReflPotSliceSpec potExpect) (M : Operator
      (2 ^ kCoin)) :
    Commute (uStage4ReflZeroNErem2m1Ideal spec).1 (rC.embedMatrix M) ∧
        Commute (uStage4ReflZeroNErem2m1_98CatUsel spec).1
      (rC.embedMatrix M) ∧ Commute (uStage4ReflZeroNErem2m1_98CatCsel spec).1 (rC.embedMatrix M) :=
  let cK := uAlignedKin2m1_98_comm_coinBand7256 rC hBand M
  ⟨cK.1.mul_left (uPotReflZeroNErem_comm_coinBand7256 rC hBand spec false M), cK.2.1.mul_left
    (uPotReflZeroNErem_comm_coinBand7256 rC hBand spec false M), cK.2.2.mul_left
      (uPotReflZeroNErem_comm_coinBand7256 rC hBand spec true M)⟩
/- ## Section 2: Coin-Multiplexed Reflected Potential & Stage-4 Unitaries -/

theorem potReflSlice_comm_projBits_coinBand {kCoin : ℕ} {peK : BitAssignment kCoin → PotExpectFn}
    (rC : QRegister kCoin dLayout)
    (hBand : ∀ j : Fin kCoin, 7143 ≤ (rC j).val ∧ (rC j).val < 7256)
        (specK : ∀ γ : BitAssignment kCoin, ReflPotSliceSpec
      (peK γ)) (isCsel : Bool) (γ δ : BitAssignment kCoin) :
    (uPotReflZeroNErem (specK γ) isCsel).1 * projBits_c70 rC δ = projBits_c70 rC δ *
        (uPotReflZeroNErem
      (specK γ) isCsel).1 := by
  rw [projBits_eq_embedMatrix_c70 rC δ];
      exact (uPotReflZeroNErem_comm_coinBand7256 rC hBand (specK γ) isCsel _).eq
/-- Coin-multiplexed reflected potential unitary over any coin register `rC` in `[7143 .. 7255]`. -/
def uPotReflMuxZeroNErem {kCoin : ℕ} {peK : BitAssignment kCoin → PotExpectFn}
    (rC : QRegister kCoin dLayout) (hBand : ∀ j : Fin kCoin, 7143 ≤ (rC j).val ∧ (rC j).val < 7256)
    (specK : ∀ γ : BitAssignment kCoin, ReflPotSliceSpec (peK γ))
    (isCsel : Bool) : Unitary (2 ^ dLayout) :=
    muxUnitary_c70 rC (fun γ ↦ uPotReflZeroNErem (specK γ) isCsel)
    (potReflSlice_comm_projBits_coinBand rC hBand specK isCsel)
end Walk2a
end QuantumComputation.Specs.PhotochemistrySolution.ReflStage4
end
end

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option exponentiation.threshold 8192

open Operator QProg Matrix Circuit Qubit PrimitiveGate QuantumComputation.Specs
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
open QuantumComputation.Specs.PhotochemistrySolution.KetSupport
  QuantumComputation.Specs.PhotochemistrySolution
  QuantumComputation.Specs.PhotochemistrySolution.SelectOracles
open QuantumComputation.Specs.PhotochemistrySolution.RouterSelectWiringA
  QuantumComputation.Specs.PhotochemistrySolution.RouterSelectWiringB
  QuantumComputation.Specs.PhotochemistrySolution.ProviderCore
open QuantumComputation.Specs.PhotochemistrySolution.Stage12Compact
  QuantumComputation.Specs.PhotochemistrySolution.ZeroNEremSpec
  QuantumComputation.Specs.PhotochemistrySolution.PotSelectWiring
open _root_.DynamicCircuit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt hiding ket matrix_ext_ket
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB (ket matrix_ext_ket)
open QuantumComputation.Specs.PhotochemistrySolution.QubitizationWalkSem
    (sqrtHalf sqrtHalf_mul_sqrtHalf)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SelectCompactAnc (totDimCompactGen
    ancWOfScr lcuProjPoly locSysPoly OffIndexAndScratchPoly)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SelectCompactAnc (projOneQCompactGen
    cat8SharedProjCompactGen)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SelectSandwich (tailReg hadamardRegSym
    hadamardRegSym_comm_disjoint)
open QuantumComputation.Specs.PhotochemistrySolution.SelectSandwich
    (hadamardRegSym_unitary_mulVec_zero proj_zero_mul_hadamardRegSym_inv_mulVec)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.TopSelectBridge (lcuSubLGen scrSubLGen)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.PotOracleGen (disj_of_ne)
open scoped Matrix BigOperators
namespace QuantumComputation.Specs.PhotochemistrySolution.Instances
scoped instance (priority := 100000) {k : ℕ} : NeZero (2 ^ k) := ⟨pow_ne_zero k two_ne_zero⟩
end QuantumComputation.Specs.PhotochemistrySolution.Instances
open scoped QuantumComputation.Specs.PhotochemistrySolution.Instances
set_option allowUnsafeReducibility true in
attribute [local reducible] totDimCompactGen
set_option allowUnsafeReducibility true in
attribute [local irreducible] systemQubits_frozen ancWOfScr

namespace QuantumComputation.Specs.PhotochemistrySolution.Coin70Lift
theorem hDisjHadCoinExt_c70 {kExt : ℕ} (hk : kExt ≤ 72) (i : Fin kExt) :
    rCoinExt kExt hk i ≠ wHasN1 := fun e ↦ by
  have hi := i.isLt; have hv := congrArg Fin.val e
  dsimp only [wHasN1] at hv; rw [val_rCoinExt, val_rOut40Layout] at hv; dsimp only at hv;
      omega
/-- Forward `kExt`-qubit Hadamard circuit on `rCoinExt kExt hk`. -/
def cHadCoinExtFwd {kExt : ℕ} (hk : kExt ≤ 72) : Circuit dLayout :=
    hadamardRegCirc kExt (rCoinExt kExt hk)
def uHadCoinExt {kExt : ℕ} (hk : kExt ≤ 72) : Unitary (2 ^ dLayout) :=
  (hadamardRegSym (Var := Unit) wHasN1 kExt (rCoinExt kExt hk)
    (hDisjHadCoinExt_c70 hk)).unitary
theorem eval_cHadCoinExtFwd_c70 {kExt : ℕ} (hk : kExt ≤ 72) : (cHadCoinExtFwd hk).eval =
    uHadCoinExt hk := eval_hadamardRegCirc wHasN1 kExt (rCoinExt kExt hk) (hDisjHadCoinExt_c70 hk)
theorem eval_hadamardRegCirc_eq_embed_c70 {d : ℕ} [NeZero (2 ^ d)] :
    ∀ (m : ℕ) (r : QRegister m d),
      (hadamardRegCirc m r).eval =
        r.embedUnitary (hadamardRegCirc m (QRegister.whole m)).eval
  | 0, r => by simp only [hadamardRegCirc, Circuit.eval_identity, r.embedUnitary_one]
  | m + 1, r => by
      have ht : tailReg r = r.compose (tailReg (QRegister.whole (m + 1))) := congrArg QRegister.mk
        (Function.Embedding.ext fun _ ↦ rfl)
      have h0 : (QRegister.whole (m + 1) : QRegister (m + 1) (m + 1)) 0 = 0 := rfl
      rw [hadamardRegCirc, hadamardRegCirc, Circuit.eval_seq, Circuit.eval_seq,
          eval_hadamardRegCirc_eq_embed_c70 m (tailReg r),
          eval_hadamardRegCirc_eq_embed_c70 m (tailReg (QRegister.whole (m + 1))), ht,
              QRegister.embedUnitary_compose,
            ← embedUnitary_single_c70 r PrimitiveGate.H 0, h0, ← r.embedUnitary_mul]
theorem uHadCoinExt_eq_embed_c70 {kExt : ℕ} (hk : kExt ≤ 72) :
    let u0 := (hadamardRegCirc kExt (QRegister.whole kExt)).eval
    uHadCoinExt hk = (rCoinExt kExt hk).embedUnitary u0 ∧ (uHadCoinExt hk)⁻¹ =
        (rCoinExt kExt hk).embedUnitary u0⁻¹ := by
  have he :=
      (eval_cHadCoinExtFwd_c70 hk).symm.trans (eval_hadamardRegCirc_eq_embed_c70 kExt (rCoinExt kExt
      hk))
  exact ⟨he, by rw [he, QRegister.embedUnitary_inv]⟩
/-- Factored `(82 + kExt)`-coin pre-restriction sandwich around `uStage1Clean_c70`. -/
def uPreExt {kExt : ℕ} (hk : kExt ≤ 72) (decodeCoin : Fin (2 ^ 41) → ZeroNEremSector)
    (u4 : Unitary (2 ^ dLayout)) : Unitary (2 ^ dLayout) :=
    (uHadCoinExt hk)⁻¹ * preConj (uStage1Clean_c70 decodeCoin) u4 * uHadCoinExt hk
theorem wFullClean_comm_rCoinExt_c70 (decodeCoin : Fin (2 ^ 41) → ZeroNEremSector) {kExt : ℕ}
    (hk : kExt ≤ 72) (M : Operator
  (2 ^ kExt)) :
    let rC := rCoinExt kExt hk
    Commute (wFull (uStage1Clean_c70 decodeCoin)).1 (rC.embedMatrix M) ∧
        Commute ((wFull (uStage1Clean_c70 decodeCoin))⁻¹).1
      (rC.embedMatrix M) := by
  intro rC
  obtain ⟨dE, dN, _, _, _⟩ := router_disj_rCoinExt_c70 hk
  have cH : Commute uHad82Layout.1 (rC.embedMatrix M) := by
    unfold uHad82Layout
    exact hadamardRegSym_comm_disjoint (Var := Unit) wHasN1 82 rLcu82Layout hDisjHad82_layout rC
      (disj_of_ne fun i j e ↦ by
        have hv : (rLcu82Layout.wires ⟨i.val, i.isLt⟩).val = (rC j).val := congrArg Fin.val e
        rw [val_rLcu82Layout, val_rCoinExt] at hv; omega) M
  have cF : Commute (wFull (uStage1Clean_c70 decodeCoin)).1 (rC.embedMatrix M) := by
    unfold wFull wNoHad; rw [Submonoid.coe_mul, Submonoid.coe_mul, Submonoid.coe_mul]
    exact ((comm_uRouterSwapConj_embedMat_pot rElecLayout rC dE M).mul_left
      ((comm_uRouterSwapConj_embedMat_pot rNucLayout rC dN M).mul_left
        (uStage1Clean_comm_rCoinExt_c70 decodeCoin hk M))).mul_left cH
  exact ⟨cF, unitary_inv_comm (wFull (uStage1Clean_c70 decodeCoin)) (rC.embedMatrix M) cF⟩
theorem preConjClean_comm_rCoinExt_c70 (decodeCoin : Fin (2 ^ 41) → ZeroNEremSector) {kExt : ℕ}
    (hk : kExt ≤ 72) (u4 : Unitary (2 ^ dLayout))
    (hu4 : ∀ M : Operator (2 ^ kExt), Commute u4.1 ((rCoinExt kExt hk).embedMatrix M))
    (M : Operator (2 ^ kExt)) :
    Commute (preConj (uStage1Clean_c70 decodeCoin) u4).1 ((rCoinExt kExt hk).embedMatrix M) := by
  obtain ⟨cF, cFi⟩ := wFullClean_comm_rCoinExt_c70 decodeCoin hk M
  unfold preConj; rw [Submonoid.coe_mul, Submonoid.coe_mul];
      exact (cFi.mul_left (hu4 M)).mul_left cF
theorem preConjClean_mux_eq_c70 (decodeCoin : Fin (2 ^ 41) → ZeroNEremSector) {kExt : ℕ}
    (hk : kExt ≤ 72) (uF : BitAssignment kExt → Unitary (2 ^ dLayout))
    (hC : ∀ γ δ, (uF γ).1 * projBits_c70 (rCoinExt kExt hk) δ = projBits_c70 (rCoinExt kExt hk) δ *
    (uF γ).1) : (preConj (uStage1Clean_c70 decodeCoin)
    (muxUnitary_c70 (rCoinExt kExt hk) uF hC)).1 = ∑ γ : BitAssignment kExt,
    (preConj (uStage1Clean_c70 decodeCoin) (uF γ)).1 * projBits_c70 (rCoinExt kExt hk) γ := by
  let rC := rCoinExt kExt hk
  let Fc := wFull (uStage1Clean_c70 decodeCoin)
  change (Fc⁻¹).1 * muxMat_c70 rC uF * Fc.1 = _
  unfold muxMat_c70; rw [Matrix.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun γ _ ↦ ?_
  have cP : Fc.1 * projBits_c70 rC γ = projBits_c70 rC γ * Fc.1 := by
    rw [projBits_eq_embedMatrix_c70 rC γ];
        exact (wFullClean_comm_rCoinExt_c70 decodeCoin hk _).1.eq
  change (Fc⁻¹).1 * ((uF γ).1 * projBits_c70 rC γ) * Fc.1 = ((Fc⁻¹).1 * (uF γ).1 * Fc.1) *
      projBits_c70 rC γ
  simp only [Matrix.mul_assoc]; rw [← cP]
theorem rCoinExt_disj_helpers_c70 {kExt : ℕ} (hk : kExt ≤ 72) :
    (rCoinExt kExt hk).DisjointWires rLcu82Layout ∧
        (rCoinExt kExt hk).DisjointWires (rScrExt kExt hk) ∧
    (rCoinExt kExt hk).DisjointWires (locSysPoly systemQubits_frozen scrWLayout) ∧
        (rScrExt kExt hk).DisjointWires rLcu82Layout :=
  ⟨disj_of_ne fun i j e ↦ by
    have hv : (rCoinExt kExt hk i).val = (rLcu82Layout.wires j).val :=
        congrArg Fin.val e; rw [val_rCoinExt,
      val_rLcu82Layout] at hv; omega,
   disj_of_ne fun i j e ↦ by
     have :=
         i.isLt;
         have : j.val < 1565 - kExt :=
         j.isLt; have hv := congrArg Fin.val e; rw [val_rCoinExt,
       val_rScrExt] at hv; omega,
   disj_of_ne fun i j e ↦ by
     have := i.isLt; have := j.isLt; have : systemQubits_frozen = 5616 := hSys5616
     have hl : (locSysPoly systemQubits_frozen scrWLayout j).val = j.val := Nat.zero_add j.val
     have hv := congrArg Fin.val e; rw [val_rCoinExt, hl] at hv; omega,
   disj_of_ne fun i j e ↦ by
     have : i.val < 1565 - kExt := i.isLt; have hv : (rScrExt kExt hk i).val =
       (rLcu82Layout.wires j).val :=
           congrArg Fin.val e; rw [val_rScrExt, val_rLcu82Layout] at hv; omega⟩
theorem lcuProj_ext_split_c70 {kExt : ℕ}
    (hk : kExt ≤ 72) : lcuProjPoly systemQubits_frozen scrWLayout (lcuSubLGen (hpExt kExt hk)) =
    (rCoinExt kExt hk).basisOutcomeProjector 0 *
    lcuProjPoly systemQubits_frozen scrWLayout (lcuSubLGen hpLayout) ∧
    Commute ((rCoinExt kExt hk).basisOutcomeProjector 0)
    (lcuProjPoly systemQubits_frozen scrWLayout (lcuSubLGen hpLayout)) := by
  refine ⟨matrix_ext_ket fun β ↦ ?_,
    (rCoinExt kExt hk).embedMatrix_comm_of_disjoint rLcu82Layout (rCoinExt_disj_helpers_c70 hk).1
        (compProj 0) (compProj 0)⟩
  change ((rLcuExt kExt hk).basisOutcomeProjector 0).mulVec (ket β) =
    ((rCoinExt kExt hk).basisOutcomeProjector 0 *
        rLcu82Layout.basisOutcomeProjector 0).mulVec (ket β)
  rw [← Matrix.mulVec_mulVec, SelectRefl.ket_basisOutcomeProjector_zero,
    PhotochemistrySolution.SelectRefl.ket_basisOutcomeProjector_zero]
  have hCond : (∀ j : Fin kExt, β (rCoinExt kExt hk j) = 0) ∧ (∀ a : Fin (mLayout + 2),
      β (rLcu82Layout a) = 0) ↔
      ∀ i : Fin (mExt kExt + 2), β (rLcuExt kExt hk i) = 0 := by
    refine ⟨fun ⟨hc, hl⟩ i ↦ ?_, fun hAll ↦ ⟨fun j ↦ ?_, fun a ↦ ?_⟩⟩
    · have hi : i.val < 80 + kExt + 2 := i.isLt
      by_cases hlt : i.val < kExt
      · exact (congrArg β (Fin.ext (by rw [val_rLcuExt, val_rCoinExt] :
          (rLcuExt kExt hk i).val = (rCoinExt kExt hk ⟨i.val, hlt⟩).val))).trans (hc _)
      · let a' : Fin (mLayout + 2) := ⟨i.val - kExt, by dsimp [mLayout]; omega⟩
        exact (congrArg β (Fin.ext (by
          have hv : _ = 7215 + (i.val - kExt) := val_rLcu82Layout a'
          rw [val_rLcuExt, hv]
          omega : (rLcuExt kExt hk i).val = (rLcu82Layout a').val))).trans (hl _)
    · have hj := j.isLt
      exact (congrArg β (Fin.ext (by rw [val_rCoinExt, val_rLcuExt] :
        (rCoinExt kExt hk j).val =
            (rLcuExt kExt hk ⟨j.val, by dsimp [mExt]; omega⟩).val))).trans (hAll _)
    · have ha : a.val < 82 := a.isLt
      exact (congrArg β
          (Fin.ext
          (by have hv := val_rLcu82Layout a; rw [hv, val_rLcuExt]; dsimp only; omega :
        (rLcu82Layout a).val = (rLcuExt kExt hk ⟨kExt + a.val,
            by dsimp [mExt]; omega⟩).val))).trans (hAll _)
  by_cases h8 : ∀ a : Fin (mLayout + 2), β (rLcu82Layout a) = 0
  · rw [ite_eq_left h8, PhotochemistrySolution.SelectRefl.ket_basisOutcomeProjector_zero]
    by_cases hc : ∀ j : Fin kExt, β (rCoinExt kExt hk j) = 0
    · rw [ite_eq_left (hCond.mp ⟨hc, h8⟩), ite_eq_left hc]
    · rw [ite_eq_right (fun hA ↦ hc (hCond.mpr hA).1), ite_eq_right hc]
  · rw [ite_eq_right h8, ite_eq_right (fun hA ↦ h8 (hCond.mpr hA).2), Matrix.mulVec_zero]
theorem proj0_uHadCoinExt_projBits_c70 {kExt : ℕ} (hk : kExt ≤ 72)
    (γ : BitAssignment kExt) :
    let rC := rCoinExt kExt hk
    rC.basisOutcomeProjector 0 * (uHadCoinExt hk)⁻¹.1 * projBits_c70 rC γ * (uHadCoinExt hk).1 *
        rC.basisOutcomeProjector 0 =
      (2 ^ kExt : ℂ)⁻¹ • rC.basisOutcomeProjector 0 := by
  intro rC
  refine matrix_ext_ket fun β ↦ ?_
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.smul_mulVec,
    PhotochemistrySolution.SelectRefl.ket_basisOutcomeProjector_zero]
  by_cases hz : ∀ j : Fin kExt, β (rC j) = 0
  · unfold uHadCoinExt; rw [ite_eq_left hz,
      hadamardRegSym_unitary_mulVec_zero (Var := Unit) wHasN1 kExt rC (hDisjHadCoinExt_c70 hk) β hz,
      Matrix.mulVec_smul, Matrix.mulVec_sum,
      Finset.sum_eq_single γ (fun δ _ hne ↦ by
        rw [projBits_mulVec_ket_c70, ite_eq_right]
        exact fun hEq ↦ hne (funext fun j ↦ (writeReg_apply_reg β rC δ j).symm.trans (hEq j)))
        (fun ha ↦ False.elim (ha (Finset.mem_univ γ))),
      projBits_mulVec_ket_c70, ite_eq_left (fun j ↦ writeReg_apply_reg ..), Matrix.mulVec_smul,
      proj_zero_mul_hadamardRegSym_inv_mulVec (Var :=
          Unit) wHasN1 kExt rC (hDisjHadCoinExt_c70 hk) β hz γ,
      smul_smul, ← mul_pow, sqrtHalf_mul_sqrtHalf, one_div, inv_pow]
  · rw [ite_eq_right hz, smul_zero, Matrix.mulVec_zero, Matrix.mulVec_zero, Matrix.mulVec_zero]
open PhotochemistrySolution.SplitRouter47_187
set_option allowUnsafeReducibility true in
attribute [local irreducible] uRouterSwapConj
theorem lift_comm_pScrExt_c70 {kExt : ℕ} (hk : kExt ≤ 72) {L : Operator (2 ^ dLayout)}
    (hRk : pScr * L = L * pScr)
    (hCR : ∀ M : Operator (2 ^ kExt), Commute L ((rCoinExt kExt hk).embedMatrix M)) :
    pScrExt kExt hk * L = L * pScrExt kExt hk := by
  have hTog (γ : BitAssignment kExt) : L * (uTogGen_c70 (rCoinExt kExt hk) γ).1 =
      (uTogGen_c70 (rCoinExt kExt hk) γ).1 * L := by
    rw [← embedUnitary_uTogLocal_c70]; exact (hCR (uTogLocal_c70 γ).1).eq
  have hW {n : ℕ} (r : QRegister n dLayout) : (QRegister.whole dLayout).compose r = r :=
    congrArg QRegister.mk (Function.Embedding.ext fun _ ↦ rfl)
  have hSum := pScrExt_eq_sum_tog_c70 hk (QRegister.whole dLayout); rw [hW, hW, hW] at hSum
  dsimp only [pScrExt, pScr]; rw [hSum, Finset.sum_mul, Matrix.mul_sum]
  refine Finset.sum_congr rfl fun γ _ ↦ ?_; simp only [Matrix.mul_assoc]
  rw [← hTog γ, ← Matrix.mul_assoc pScr L, hRk, Matrix.mul_assoc L pScr,
    ← Matrix.mul_assoc (uTogGen_c70 (rCoinExt kExt hk) γ).1 L, ← hTog γ, Matrix.mul_assoc]
theorem hoffExt_iff_layout_c70 {kExt k : ℕ} (hk : kExt ≤ 72) (r : QRegister k dLayout) :
    OffIndexAndScratchPoly systemQubits_frozen scrWLayout (lcuSubLGen (hpExt kExt hk))
    (scrSubLGen (hpExt kExt hk)) r ↔
    OffIndexAndScratchPoly systemQubits_frozen scrWLayout (lcuSubLGen hpLayout)
    (scrSubLGen hpLayout) r := by
  refine ⟨fun hoff i ↦ ?_, fun hoff i ↦ ?_⟩
  · obtain ⟨j, hj, hnl, hns⟩ := hoff i
    refine ⟨j, hj, fun ⟨a, ha⟩ ↦ ?_, fun ⟨b, hb⟩ ↦ ?_⟩
    · have haLt : a.val < 82 := a.isLt
      exact hnl ⟨⟨kExt + a.val, by dsimp [mExt]; omega⟩, Fin.ext (by
        have hv : (34 + 1565) + a.val = j.val :=
            congrArg Fin.val ha; change (34 + (1565 - kExt)) + (kExt + a.val) =
          j.val; omega)⟩
    · have hbLt : b.val < 1565 := b.isLt
      by_cases hlt : b.val < 1565 - kExt
      · exact hns ⟨⟨b.val, hlt⟩, Fin.ext (congrArg Fin.val hb)⟩
      · exact hnl ⟨⟨b.val - (1565 - kExt), by dsimp [mExt]; omega⟩, Fin.ext (by
          have hv : 34 + b.val = j.val :=
              congrArg Fin.val hb; change (34 + (1565 - kExt)) + (b.val - (1565 - kExt)) =
            j.val; omega)⟩
  · obtain ⟨j, hj, hnl, hns⟩ := hoff i
    refine ⟨j, hj, fun ⟨a, ha⟩ ↦ ?_, fun ⟨b, hb⟩ ↦ hns ⟨⟨b.val,
      by have : b.val < 1565 - kExt := b.isLt; dsimp [scrLLayout]; omega⟩,
          Fin.ext (congrArg Fin.val hb)⟩⟩
    have haLt : a.val < 80 + kExt + 2 := a.isLt
    have hv : (34 + (1565 - kExt)) + a.val = j.val := congrArg Fin.val ha
    by_cases hlt : a.val < kExt
    · exact hns ⟨⟨(1565 - kExt) + a.val, by dsimp [scrLLayout]; omega⟩, Fin.ext (by
        change 34 + ((1565 - kExt) + a.val) = j.val; omega)⟩
    · exact hnl ⟨⟨a.val - kExt, by dsimp [mLayout]; omega⟩, Fin.ext (by
        change (34 + 1565) + (a.val - kExt) = j.val; omega)⟩
theorem wFullClean_comm_off_c70 (decodeCoin : Fin (2 ^ 41) → ZeroNEremSector) {k : ℕ}
    {r : QRegister k dLayout}
    (hoff4 : OffIndexAndScratchPoly systemQubits_frozen scrWLayout (lcuSubLGen hpLayout)
    (scrSubLGen hpLayout) r) (M : Operator (2 ^ k)) :
    Commute (wFull (uStage1Clean_c70 decodeCoin)).1 (r.embedMatrix M) := by
  have cCl : Commute (uStage1Clean_c70 decodeCoin).1 (r.embedMatrix M) :=
    rStage1Clean122_c70.embedMatrix_comm_of_disjoint r (disj_of_ne fun i j e ↦ by
      have hb :=
          hoffIndex_bounds_layout hoff4 j;
          have hi : i.val < 122 := i.isLt; have hv := congrArg Fin.val e
      unfold rStage1Clean122_c70 at hv
      by_cases h40 : i.val < 40
      · rw [show i = Fin.castAdd (mLayout + 2) ⟨i.val, h40⟩ from rfl,
          QRegister.concat_apply_left rOut40Layout rLcu82Layout hDisjOut40Lcu82_c70 ⟨i.val, h40⟩,
          val_rOut40Layout] at hv; dsimp only at hv; omega
      · let i82 : Fin (mLayout + 2) := ⟨i.val - 40, by dsimp [mLayout]; omega⟩
        have hi82 : i82.val < 82 := i82.isLt
        rw [show i = Fin.natAdd 40 i82 from Fin.ext (by dsimp [i82, Fin.natAdd]; omega),
          QRegister.concat_apply_right rOut40Layout rLcu82Layout hDisjOut40Lcu82_c70 i82,
              val_rLcu82Layout] at hv; omega) _ M
  unfold wFull wNoHad uHad82Layout; rw [Submonoid.coe_mul, Submonoid.coe_mul,
      Submonoid.coe_mul]
  exact ((comm_uRouterSwapConj_embedMat_pot rElecLayout r (fun i j e ↦ by
      have hb := hoffIndex_bounds_layout hoff4 j; have _ : i.val < 5056 := hEW5056 ▸ i.isLt
      have hv : (elecRouterWireFn i).val = (r j).val := congrArg Fin.val e
      rw [val_elecRouterWireFn] at hv; split_ifs at hv <;> omega) M).mul_left
    ((comm_uRouterSwapConj_embedMat_pot rNucLayout r (fun i j e ↦ by
      have hb := hoffIndex_bounds_layout hoff4 j; have _ : i.val < 1394 := hNW1394 ▸ i.isLt
      have hv : (nucRouterWireFn i).val = (r j).val := congrArg Fin.val e
      rw [val_nucRouterWireFn] at hv; split_ifs at hv <;> omega) M).mul_left cCl)).mul_left
    (hadamardRegSym_comm_disjoint (Var :=
        Unit) wHasN1 82 rLcu82Layout hDisjHad82_layout r (disj_of_ne fun i j e ↦ by
      have hb := hoffIndex_bounds_layout hoff4 j
      have hv : (rLcu82Layout.wires ⟨i.val, i.isLt⟩).val = (r j).val := congrArg Fin.val e
      rw [val_rLcu82Layout] at hv; dsimp only at hv; omega) M)
theorem uPreExt_comm_off_c70 {kExt k : ℕ} (hk : kExt ≤ 72)
    (decodeCoin : Fin (2 ^ 41) → ZeroNEremSector) (u4 : Unitary (2 ^ dLayout)) (hu4 : ∀ {m : ℕ}
    (r' : QRegister m dLayout),
    OffIndexAndScratchPoly systemQubits_frozen scrWLayout (lcuSubLGen (hpExt kExt hk))
    (scrSubLGen (hpExt kExt hk)) r' → ∀ M' : Operator (2 ^ m), Commute u4.1 (r'.embedMatrix M'))
    {r : QRegister k dLayout}
    (hoff : OffIndexAndScratchPoly systemQubits_frozen scrWLayout (lcuSubLGen (hpExt kExt hk))
    (scrSubLGen (hpExt kExt hk)) r) (M : Operator (2 ^ k)) :
    Commute (uPreExt hk decodeCoin u4).1 (r.embedMatrix M) := by
  have hoff4 := (hoffExt_iff_layout_c70 hk r).mp hoff
  have cFc := wFullClean_comm_off_c70 decodeCoin hoff4 M
  have dRC : (rCoinExt kExt hk).DisjointWires r := disj_of_ne fun i j e ↦ by
    have hb :=
        hoffIndex_bounds_layout hoff4 j; have hi := i.isLt; have hv := congrArg Fin.val e
    rw [val_rCoinExt] at hv; omega
  have cRC (U : Operator (2 ^ kExt)) : Commute ((rCoinExt kExt hk).embedMatrix U) (r.embedMatrix M)
      :=
    (rCoinExt kExt hk).embedMatrix_comm_of_disjoint r dRC U M
  obtain ⟨hHf, hHi⟩ := uHadCoinExt_eq_embed_c70 hk
  unfold uPreExt preConj; simp only [Submonoid.coe_mul]; rw [hHi, hHf]
  exact ((cRC _).mul_left
    ((((show Commute _ _ from unitary_inv_comm _ _ cFc).mul_left (hu4 r hoff M)).mul_left
        cFc))).mul_left (cRC _)
set_option allowUnsafeReducibility true in
attribute [local irreducible] PgBase.phaseGradientState
theorem pScrExt_comm_off_c70 {kExt k : ℕ} (hk : kExt ≤ 72) {r : QRegister k dLayout}
    (hoff : OffIndexAndScratchPoly systemQubits_frozen scrWLayout (lcuSubLGen (hpExt kExt hk))
        (scrSubLGen (hpExt kExt hk)) r)
    (M : Operator (2 ^ k)) : Commute (pScrExt kExt hk) (r.embedMatrix M) :=
  let hoff4 := (hoffExt_iff_layout_c70 hk r).mp hoff
  (rScrExt kExt hk).embedMatrix_comm_of_disjoint r (disj_of_ne fun i j e ↦ by
    have hb := hoffIndex_bounds_layout hoff4 j; have hi : i.val < 1565 - kExt := i.isLt
    have hv := congrArg Fin.val e; rw [val_rScrExt] at hv; omega) (compProj 0) M
end QuantumComputation.Specs.PhotochemistrySolution.Coin70Lift

namespace QuantumComputation.Specs.PhotochemistrySolution.OuterW11Bridge
open PhotochemistrySolution.Stage2Xor84 PhotochemistrySolution.Stage2PotUnld
  PhotochemistrySolution.Stage2ElecFirst
open PhotochemistrySolution.Coin70Lift PhotochemistrySolution.Sub5885
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SplitRouter47_187 (uRouterSwapConj)
set_option allowUnsafeReducibility true in
attribute [local irreducible] uRouterSwapConj PgBase.phaseGradientState
abbrev CommScr (L : Operator (2 ^ dLayout)) : Prop := pScr * L = L * pScr
abbrev preLoc (U₁ U₄ : Unitary (2 ^ dLayout)) : Operator (2 ^ dLayout) := (preConj U₁ U₄).1
/- ## Subregister Commutation & Nested Multiplexers -/

theorem castAdd_inj_out (k₁ k₂ : ℕ) : Function.Injective (Fin.castAdd k₂ : Fin k₁ → Fin (k₁ + k₂))
    := fun _ _ h ↦ Fin.ext (by
  simpa using congrArg Fin.val h)
theorem natAdd_inj_out (k₁ k₂ : ℕ) : Function.Injective (Fin.natAdd k₁ : Fin k₂ → Fin (k₁ + k₂)) :=
    fun _ _ h ↦ Fin.ext (by
  have hv := congrArg Fin.val h; dsimp [Fin.natAdd] at hv; omega)
/-- Left subregister `Fin k₁ ↪ Fin (k₁ + k₂)`. -/
def rLeftInConcat (k₁ k₂ : ℕ) : QRegister k₁ (k₁ + k₂) :=
  ⟨⟨Fin.castAdd k₂, castAdd_inj_out k₁ k₂⟩⟩
/-- Right subregister `Fin k₂ ↪ Fin (k₁ + k₂)`. -/
def rRightInConcat (k₁ k₂ : ℕ) : QRegister k₂ (k₁ + k₂) := ⟨⟨Fin.natAdd k₁, natAdd_inj_out k₁ k₂⟩⟩
theorem slice_comm_projBits_rOut {kExt kOut : ℕ} (hk : kExt ≤ 72) (rSub : QRegister kOut 41)
    {uSlice : BitAssignment (kExt + kOut) → Unitary (2 ^ dLayout)}
    (hu : ∀ γω (M : Operator (2 ^ (kExt + kOut))),
        Commute (uSlice γω).1 ((rCoinExtOut hk rSub).embedMatrix M))
    (γ : BitAssignment kExt) (ω ω' : BitAssignment kOut) :
    (uSlice (concatBitsGen γ ω)).1 * projBits_c70 (rOutLayout rSub) ω' =
      projBits_c70 (rOutLayout rSub) ω' * (uSlice (concatBitsGen γ ω)).1 := by
  have hComp : ((rCoinExt kExt hk).concat (rOutLayout rSub)
      (rCoinExt_disj_rOutLayout hk rSub)).compose
      (rRightInConcat kExt kOut) = rOutLayout rSub :=
    congrArg QRegister.mk (Function.Embedding.ext fun j ↦
        QRegister.concat_apply_right (rCoinExt kExt hk) (rOutLayout rSub)
      (rCoinExt_disj_rOutLayout hk rSub) j)
  rw [projBits_eq_embedMatrix_c70 (rOutLayout rSub) ω', ← hComp, QRegister.embedMatrix_compose]
  exact (hu (concatBitsGen γ ω) _).eq
/-- Inner `rOutLayout rSub` multiplexed unitary at fixed `γ : BitAssignment kExt`. -/
def uMuxOut {kExt kOut : ℕ} (hk : kExt ≤ 72) (rSub : QRegister kOut 41)
    (uSlice : BitAssignment (kExt + kOut) → Unitary (2 ^ dLayout))
    (hu : ∀ γω (M : Operator (2 ^ (kExt + kOut))),
    Commute (uSlice γω).1 ((rCoinExtOut hk rSub).embedMatrix M)) (γ : BitAssignment kExt) :
    Unitary (2 ^ dLayout) :=
    muxUnitary_c70 (rOutLayout rSub) (fun ω ↦ uSlice (concatBitsGen γ ω))
    (slice_comm_projBits_rOut hk rSub hu γ)
theorem uMuxOut_comm_rCoinExt {kExt kOut : ℕ} (hk : kExt ≤ 72) (rSub : QRegister kOut 41)
    {uSlice : BitAssignment (kExt + kOut) → Unitary (2 ^ dLayout)}
    (hu : ∀ γω (M : Operator (2 ^ (kExt + kOut))),
    Commute (uSlice γω).1 ((rCoinExtOut hk rSub).embedMatrix M)) (γ : BitAssignment kExt)
    (M : Operator (2 ^ kExt)) :
    Commute (uMuxOut hk rSub uSlice hu γ).1 ((rCoinExt kExt hk).embedMatrix M) := by
  have hComp : ((rCoinExt kExt hk).concat (rOutLayout rSub)
      (rCoinExt_disj_rOutLayout hk rSub)).compose
      (rLeftInConcat kExt kOut) = rCoinExt kExt hk :=
    congrArg QRegister.mk (Function.Embedding.ext fun i ↦
        QRegister.concat_apply_left (rCoinExt kExt hk) (rOutLayout rSub)
      (rCoinExt_disj_rOutLayout hk rSub) i)
  change muxMat_c70 (rOutLayout rSub) _ * _ = _ * muxMat_c70 (rOutLayout rSub) _
  unfold muxMat_c70; rw [Finset.sum_mul, Matrix.mul_sum]
  refine Finset.sum_congr rfl fun ω _ ↦ ?_
  have cU : Commute (uSlice (concatBitsGen γ ω)).1 ((rCoinExt kExt hk).embedMatrix M) := by
    rw [← hComp, QRegister.embedMatrix_compose]; exact hu (concatBitsGen γ ω) _
  have cP : Commute (projBits_c70 (rOutLayout rSub) ω) ((rCoinExt kExt hk).embedMatrix M) := by
    rw [projBits_eq_embedMatrix_c70 (rOutLayout rSub) ω]
    exact ((rCoinExt kExt hk).embedMatrix_comm_of_disjoint (rOutLayout rSub)
        (rCoinExt_disj_rOutLayout hk rSub) M _).symm
  exact (cU.mul_left cP).eq
theorem uMuxOut_comm_projBits_rCoinExt {kExt kOut : ℕ} (hk : kExt ≤ 72) (rSub : QRegister kOut 41)
    {uSlice : BitAssignment (kExt + kOut) → Unitary (2 ^ dLayout)}
    (hu : ∀ γω (M : Operator (2 ^ (kExt + kOut))),
    Commute (uSlice γω).1 ((rCoinExtOut hk rSub).embedMatrix M)) (γ δ : BitAssignment kExt) :
    (uMuxOut hk rSub uSlice hu γ).1 * projBits_c70 (rCoinExt kExt hk) δ =
    projBits_c70 (rCoinExt kExt hk) δ * (uMuxOut hk rSub uSlice hu γ).1 := by
  rw [projBits_eq_embedMatrix_c70 (rCoinExt kExt hk) δ];
      exact (uMuxOut_comm_rCoinExt hk rSub hu γ _).eq
/--
Nested `rCoinExt` + `rOutLayout` multiplexed unitary equivalent to
`muxMat_c70 (rCoinExtOut hk rSub)` .
-/
def uMuxExtOut {kExt kOut : ℕ} (hk : kExt ≤ 72) (rSub : QRegister kOut 41)
    (uSlice : BitAssignment (kExt + kOut) → Unitary (2 ^ dLayout))
    (hu : ∀ γω (M : Operator (2 ^ (kExt + kOut))),
    Commute (uSlice γω).1 ((rCoinExtOut hk rSub).embedMatrix M)) : Unitary (2 ^ dLayout) :=
    muxUnitary_c70 (rCoinExt kExt hk) (uMuxOut hk rSub uSlice hu)
    (uMuxOut_comm_projBits_rCoinExt hk rSub hu)
theorem uMuxExtOut_val {kExt kOut : ℕ} (hk : kExt ≤ 72) (rSub : QRegister kOut 41)
    (uSlice : BitAssignment (kExt + kOut) → Unitary (2 ^ dLayout))
    (hu : ∀ γω (M : Operator (2 ^ (kExt + kOut))),
    Commute (uSlice γω).1 ((rCoinExtOut hk rSub).embedMatrix M)) :
    (uMuxExtOut hk rSub uSlice hu).1 = muxMat_c70 (rCoinExtOut hk rSub) uSlice :=
    (muxMat_concat_eq_c70 (rCoinExt kExt hk) (rOutLayout rSub)
    (rCoinExt_disj_rOutLayout hk rSub) uSlice (slice_comm_projBits_rOut hk rSub hu)).symm
theorem uMuxExtOut_comm_off {kExt kOut k : ℕ} (hk : kExt ≤ 72) (rSub : QRegister kOut 41)
    {uSlice : BitAssignment (kExt + kOut) → Unitary (2 ^ dLayout)}
    (hu : ∀ γω (M : Operator (2 ^ (kExt + kOut))),
    Commute (uSlice γω).1 ((rCoinExtOut hk rSub).embedMatrix M)) (hOff : ∀ γω {m : ℕ}
    (r' : QRegister m dLayout),
    OffIndexAndScratchPoly systemQubits_frozen scrWLayout (lcuSubLGen hpLayout)
    (scrSubLGen hpLayout) r' → ∀ M' : Operator (2 ^ m), Commute (uSlice γω).1 (r'.embedMatrix M'))
    {r : QRegister k dLayout}
    (hoff : OffIndexAndScratchPoly systemQubits_frozen scrWLayout (lcuSubLGen (hpExt kExt hk))
    (scrSubLGen (hpExt kExt hk)) r) (M : Operator (2 ^ k)) :
    Commute (uMuxExtOut hk rSub uSlice hu).1 (r.embedMatrix M) := by
  have hoff4 := (hoffExt_iff_layout_c70 hk r).mp hoff
  have dCO := rCoinExtOut_disj_off hk rSub hoff4
  change (uMuxExtOut hk rSub uSlice hu).1 * r.embedMatrix M = r.embedMatrix M *
      (uMuxExtOut hk rSub uSlice hu).1
  rw [uMuxExtOut_val]
  unfold muxMat_c70; rw [Finset.sum_mul, Matrix.mul_sum]
  refine Finset.sum_congr rfl fun γω _ ↦ ?_
  have cP : Commute (projBits_c70 (rCoinExtOut hk rSub) γω) (r.embedMatrix M) := by
    rw [projBits_eq_embedMatrix_c70 (rCoinExtOut hk rSub) γω]; exact
      (rCoinExtOut hk rSub).embedMatrix_comm_of_disjoint r dCO _ M
  exact ((hOff γω r hoff4 M).mul_left cP).eq
/- ## Hadamard-Conjugated Outer-Bit Projector `qOutHad` -/

/--
Hadamard-conjugated outer-bit projector
`(uHad82Layout⁻¹).1 * projBits_c70 (rOutLayout rSub) ω * uHad82Layout.1` .
-/
def qOutHad {kOut : ℕ} (rSub : QRegister kOut 41) (ω : BitAssignment kOut) : Operator (2 ^ dLayout)
    := (uHad82Layout⁻¹).1 * projBits_c70 (rOutLayout rSub) ω * uHad82Layout.1
theorem uHad82_mul_inv_out : uHad82Layout.1 * (uHad82Layout⁻¹).1 = 1 := by
  rw [← Submonoid.coe_mul, mul_inv_cancel, OneMemClass.coe_one]
theorem preConjClean_unw_out (decode : Fin (2 ^ 41) → ZeroNEremSector) (U : Unitary (2 ^ dLayout)) :
    (preConj (uStage1Clean_c70 decode) U).1 =
      (uHad82Layout⁻¹).1 * ((wNoHad (uStage1Clean_c70 decode))⁻¹ * U *
          wNoHad (uStage1Clean_c70 decode)).1 * uHad82Layout.1 := by
  unfold preConj wFull; rw [_root_.mul_inv_rev]; simp only [Submonoid.coe_mul,
      Matrix.mul_assoc]
theorem sum_qOutHad {kOut : ℕ} (rSub : QRegister kOut 41) : (∑ ω : BitAssignment kOut,
    qOutHad rSub ω) = 1 := by
  unfold qOutHad; rw [← Finset.sum_mul, ← Matrix.mul_sum, sum_projBits_c70 (rOutLayout rSub),
      Matrix.mul_one,
    ← Submonoid.coe_mul, inv_mul_cancel, OneMemClass.coe_one]
theorem qOutHad_mul {kOut : ℕ} (rSub : QRegister kOut 41) (ω ω' : BitAssignment kOut) :
    qOutHad rSub ω * qOutHad rSub ω' = if ω = ω' then qOutHad rSub ω else 0 := by
  have hM : qOutHad rSub ω * qOutHad rSub ω' =
      (uHad82Layout⁻¹).1 * (projBits_c70 (rOutLayout rSub) ω * projBits_c70 (rOutLayout rSub) ω') *
          uHad82Layout.1 := by
    unfold qOutHad; simp only [Matrix.mul_assoc];
        rw [← Matrix.mul_assoc uHad82Layout.1 (uHad82Layout⁻¹).1, uHad82_mul_inv_out, one_mul]
  rw [hM, projBits_mul_c70]; split_ifs <;> simp [qOutHad]
theorem preConjClean_uMuxOut_eq {kExt kOut : ℕ} (decode : Fin (2 ^ 41) → ZeroNEremSector)
    (hk : kExt ≤ 72) (rSub : QRegister kOut 41) {uSlice : BitAssignment (kExt + kOut) →
    Unitary (2 ^ dLayout)} (hu : ∀ γω (M : Operator (2 ^ (kExt + kOut))),
    Commute (uSlice γω).1 ((rCoinExtOut hk rSub).embedMatrix M)) (γ : BitAssignment kExt) :
    (preConj (uStage1Clean_c70 decode) (uMuxOut hk rSub uSlice hu γ)).1 = ∑ ω :
    BitAssignment kOut, (preConj (uStage1Clean_c70 decode) (uSlice (concatBitsGen γ ω))).1 *
    qOutHad rSub ω := by
  let W := wNoHad (uStage1Clean_c70 decode)
  rw [preConjClean_unw_out decode]
  change (uHad82Layout⁻¹).1 * ((W⁻¹).1 * muxMat_c70 (rOutLayout rSub) _ * W.1) * uHad82Layout.1 = _
  unfold muxMat_c70; rw [Matrix.mul_sum, Finset.sum_mul, Matrix.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun ω _ ↦ ?_
  have cW := (wNoHadClean_comm_projBits_rOutLayout decode rSub ω).symm.eq
  rw [preConjClean_unw_out decode]; unfold qOutHad; symm; simp only [Submonoid.coe_mul,
      Matrix.mul_assoc]
  rw [← Matrix.mul_assoc uHad82Layout.1 (uHad82Layout⁻¹).1, uHad82_mul_inv_out, one_mul,
    ← Matrix.mul_assoc W.1 (projBits_c70 (rOutLayout rSub) ω), ← cW]
  dsimp only [W]; simp only [Matrix.mul_assoc]
theorem comm_pScr_qOutHad {kOut : ℕ} (rSub : QRegister kOut 41) (ω : BitAssignment kOut) :
    Commute pScr (qOutHad rSub ω) := by
  have cP : Commute pScr (projBits_c70 (rOutLayout rSub) ω) := by
    rw [projBits_eq_embedMatrix_c70 (rOutLayout rSub) ω]
    exact rScrLayout.embedMatrix_comm_of_disjoint (rOutLayout rSub) (disj_of_ne fun i j e ↦ by
      have hi : i.val < 1565 := i.isLt; have hb := val_rOutLayout_bounds rSub j
      have hv := congrArg Fin.val e; rw [val_rScrLayout] at hv; omega) (compProj 0) _
  unfold qOutHad; exact ((show Commute _ _ from
    (unitary_inv_comm uHad82Layout pScr comm_pScr_uHad82.eq).symm).mul_right cP).mul_right
        comm_pScr_uHad82.symm
/- ## Generic Orthogonal-Projector Family Reductions -/

/-- Projected involutivity lifts across any complete orthogonal projector family `Q`. -/
theorem sum_mul_orthProj_sq_eq {α : Type*} [Fintype α] [DecidableEq α] {d : ℕ}
    (M Q : α → Operator d) (P : Operator d) (hSum : (∑ a : α, Q a) = 1)
    (hOrth : ∀ a b : α, Q a * Q b = if a = b then Q a else 0) (hCommM : ∀ a b : α, Q a * M b = M b *
    Q a) (hCommP : ∀ a : α, Q a * P = P * Q a) (hSq : ∀ a : α, (M a * M a) * P = P) :
    ((∑ a : α, M a * Q a) * (∑ a : α, M a * Q a)) * P = P := by
  rw [Finset.sum_mul, Finset.sum_mul]
  refine (Finset.sum_congr rfl fun a _ ↦ ?_).trans (by rw [← Finset.sum_mul, hSum, Matrix.one_mul])
  rw [Matrix.mul_sum, Finset.sum_mul, Finset.sum_eq_single a]
  · simp only [Matrix.mul_assoc]; rw [← Matrix.mul_assoc (Q a)
        (M a), hCommM a a, Matrix.mul_assoc (M a) (Q a),
      ← Matrix.mul_assoc (Q a) (Q a), hOrth a a, ite_eq_left rfl, hCommP a,
          ← Matrix.mul_assoc (M a) P,
      ← Matrix.mul_assoc (M a) (M a * P), ← Matrix.mul_assoc (M a) (M a) P, hSq a, ← hCommP a]
  · intro b _ hne; simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (Q a) (M b), hCommM a b, Matrix.mul_assoc (M b)
        (Q a), ← Matrix.mul_assoc (Q a) (Q b),
      hOrth a b, ite_eq_right hne.symm, zero_mul, mul_zero, mul_zero]
  · exact fun hm ↦ absurd (Finset.mem_univ a) hm
theorem preConjClean_comm_qOutHad {kOut : ℕ} (decode : Fin (2 ^ 41) → ZeroNEremSector)
    (rSub : QRegister kOut 41) (ω : BitAssignment kOut) (u4 : Unitary (2 ^ dLayout))
    (hu4 : Commute u4.1 (projBits_c70 (rOutLayout rSub) ω)) :
    Commute (preConj (uStage1Clean_c70 decode) u4).1 (qOutHad rSub ω) := by
  let W := wNoHad (uStage1Clean_c70 decode)
  have cW := wNoHadClean_comm_projBits_rOutLayout decode rSub ω
  have cMid : Commute ((W⁻¹ * u4 * W).1) (projBits_c70 (rOutLayout rSub) ω) := by
    rw [Submonoid.coe_mul, Submonoid.coe_mul];
        exact ((show Commute _ _ from unitary_inv_comm W _ cW).mul_left hu4).mul_left cW
  change (preConj (uStage1Clean_c70 decode) u4).1 * _ = _ *
      (preConj (uStage1Clean_c70 decode) u4).1
  rw [preConjClean_unw_out decode u4]; unfold qOutHad; simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc uHad82Layout.1 (uHad82Layout⁻¹).1, uHad82_mul_inv_out, one_mul,
    ← Matrix.mul_assoc uHad82Layout.1 (uHad82Layout⁻¹).1, uHad82_mul_inv_out, one_mul,
    ← Matrix.mul_assoc (W⁻¹ * u4 * W).1 (projBits_c70 (rOutLayout rSub) ω), cMid.eq,
        Matrix.mul_assoc]
/- ## `pScrExt` Commutation, Involutivity, `Csel`, and `Cat8` Lifts -/

theorem comm_pScrExt_uPreExt_outerSub {kExt kOut w1 : ℕ} {decode : Fin (2 ^ 41) → ZeroNEremSector}
    (hk : kExt ≤ 72) (rSub : QRegister kOut 41) (o1 : Stage1ZeroNEremLayout w1 decode)
    (uSlice : BitAssignment (kExt + kOut) → Unitary (2 ^ dLayout))
    (hu : ∀ γω (M : Operator (2 ^ (kExt + kOut))),
    Commute (uSlice γω).1 ((rCoinExtOut hk rSub).embedMatrix M))
    (hCS : ∀ γω, CommScr (preLoc o1.uLocal (uSlice γω))) : pScrExt kExt hk *
    (uPreExt hk decode (uMuxExtOut hk rSub uSlice hu)).1 =
    (uPreExt hk decode (uMuxExtOut hk rSub uSlice hu)).1 * pScrExt kExt hk := by
  let rC := rCoinExt kExt hk
  have cScrR (M : Operator (2 ^ kExt)) : Commute (pScrExt kExt hk) (rC.embedMatrix M) :=
    (rC.embedMatrix_comm_of_disjoint (rScrExt kExt hk)
        (rCoinExt_disj_helpers_c70 hk).2.1 M (compProj 0)).symm
  obtain ⟨hHf, hHi⟩ := uHadCoinExt_eq_embed_c70 hk
  have cHf : Commute (pScrExt kExt hk) (uHadCoinExt hk).1 := by rw [hHf]; exact cScrR _
  have cHi : Commute (pScrExt kExt hk) (uHadCoinExt hk)⁻¹.1 := by rw [hHi]; exact cScrR _
  have cMux : Commute (pScrExt kExt hk) (preConj (uStage1Clean_c70 decode)
      (uMuxExtOut hk rSub uSlice hu)).1 := by
    change pScrExt kExt hk * _ = _ * pScrExt kExt hk
    unfold uMuxExtOut;
        rw [preConjClean_mux_eq_c70 decode hk _ (uMuxOut_comm_projBits_rCoinExt hk rSub hu),
      Matrix.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun γ _ ↦ ?_
    have hRkγ : pScr * (preConj (uStage1Clean_c70 decode) (uMuxOut hk rSub uSlice hu γ)).1 =
        (preConj (uStage1Clean_c70 decode) (uMuxOut hk rSub uSlice hu γ)).1 * pScr := by
      rw [preConjClean_uMuxOut_eq decode hk rSub hu γ, Matrix.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun ω _ ↦ ?_
      rw [← Matrix.mul_assoc, (preConj_uStage1Clean_c70 o1 _ (hCS (concatBitsGen γ ω))).2,
          Matrix.mul_assoc,
        (comm_pScr_qOutHad rSub ω).eq, ← Matrix.mul_assoc]
    rw [← Matrix.mul_assoc, lift_comm_pScrExt_c70 hk hRkγ
        (preConjClean_comm_rCoinExt_c70 decode hk _ (uMuxOut_comm_rCoinExt hk rSub hu γ)),
      Matrix.mul_assoc, projBits_eq_embedMatrix_c70 rC γ, (cScrR _).eq, ← Matrix.mul_assoc]
  unfold uPreExt; rw [Submonoid.coe_mul, Submonoid.coe_mul];
      exact ((cHi.mul_right cMux).mul_right cHf).eq
end QuantumComputation.Specs.PhotochemistrySolution.OuterW11Bridge
end
end
