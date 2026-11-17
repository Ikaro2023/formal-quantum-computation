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

public import QuantumComputationDiscoveries.Algorithms.Photochemistry.Solution.UpperSelectAlwaysLoW338

open QuantumComputation.Specs.PhotochemistrySolution.SpecDefs
open QuantumComputation.Specs.PhotochemistrySolution.QhlAux
open QuantumComputation.Specs.PhotochemistrySolution.PgBase
open QuantumComputation.Specs.PhotochemistrySolution.SelectBase
@[expose] public section
set_option Elab.async false
set_option allowUnsafeReducibility true
set_option autoImplicit false
set_option exponentiation.threshold 256
open scoped Matrix BigOperators
open QuantumComputation.Specs.PhotochemistrySolution.SelectCsa64ProvSpec
  QuantumComputation.Specs.PhotochemistrySolution.SelectOracles
  QuantumComputation.Specs.PhotochemistrySolution.FineLegendre
open QuantumComputation.Specs.PhotochemistrySolution.InPlaceModAdd
  QuantumComputation.Specs.PhotochemistrySolution.ProviderCore
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SplitBellVecCleanStep
    (subspaceStep_of_circuit subspaceStep_congr_in subspaceStep_congr_out)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SelectStructuredCB (StructuredCB)


noncomputable section
namespace QuantumComputation.Specs.PhotochemistrySolution.AlwaysLo25860Opt
open Operator QProg Matrix Circuit Qubit HermitianMat PrimitiveGate PhotochemistrySolution.XMeasUnld
  PhotochemistrySolution.SplitRouter47_187 PhotochemistrySolution.Stage2QromMux
  PhotochemistrySolution.Stage2ZeroGated PhotochemistrySolution.WStateRouterPrim
  PhotochemistrySolution.Stage2ElecOptA PhotochemistrySolution.WState25PortOpt
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
open _root_.DynamicCircuit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt hiding ket matrix_ext_ket
  qAssign_obs_map_val ket_projector_zero ket_projector_one ket_X ket_CNOT ket_TOFF eval_seq_mulVec
  bit_cases localIdx
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB hiding writeReg
  writeReg_apply_of_not_mem ket ket_X ket_CNOT ket_TOFF matrix_ext_ket bitSign eval_seq_mulVec
  localIdx
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SplitRouterSeqBell26k hiding ket
  matrix_ext_ket
open scoped ComplexOrder MatrixOrder Circuit.Notation
noncomputable local instance {n : ℕ} (wHas : Wire n) (wIdx : Fin 8 → Wire n)
    (wOut : Fin 192 → Wire n) (qEnc : Wire n) :
    Decidable (WRouterDisjProp wHas wIdx wOut qEnc) :=
  Classical.propDecidable _

noncomputable local instance {n : ℕ} (wHas : Wire n) (wIdx : Fin 8 → Wire n)
    (wOut : Fin 192 → Wire n) :
    Decidable (WRouterOutDisj wHas wIdx wOut) :=
  Classical.propDecidable _

theorem wTail5_ne_wOut0 {n : ℕ} {wOut : Fin 192 → Wire n}
    (hInj : ∀ i j : Fin 192, i ≠ j → wOut i ≠ wOut j) (t : Fin 5) :
    wTail5 wOut t ≠ wOut ⟨0, by omega⟩ :=
  hInj _ _ (by intro e; have := t.isLt; have h := congrArg Fin.val e; dsimp at h; omega)

/-- Folded `91`-block index mapping `91..95` onto `0` (`w91x2 wOut ⟨0, _⟩ ⟨0, _⟩ = wOut[0]`). -/
def bFold91 {n : ℕ} (wIdx : Fin 8 → Wire n) (δ : BitAssignment n) : Fin 91 :=
  ⟨if idxValD (wIdx3x32 wIdx) δ < 91 then idxValD (wIdx3x32 wIdx) δ else 0, by split_ifs <;> omega⟩

theorem bFold91_val_pos {n : ℕ} (wIdx : Fin 8 → Wire n) (δ : BitAssignment n) (h : act91 wIdx δ) :
    (bFold91 wIdx δ).val = idxValD (wIdx3x32 wIdx) δ := by
  unfold bFold91 act91 at *; exact ite_eq_left h
/--
Exact `368-T` (`0 .TOFF`, `0` pad wires `wOut[187..191]` ) forward `187` -way zero-gated W-state
one-hot loader.
-/
def wComp187_368 {Var : Type} {n : ℕ} (v : Var) (wHas : Wire n) (wIdx : Fin 8 → Wire n)
    (wOut : Fin 192 → Wire n) (qEnc : Wire n) : DynamicCircuit Var n :=
  if hd : WRouterDisjProp wHas wIdx wOut qEnc then
    let hIdxOut3 : ∀ d j, wIdx3x32 wIdx d ≠ wOut3x32 wOut j := fun d j ↦ by
      obtain ⟨d8, heq⟩ := wIdx3x32_mem wIdx d; rw [heq]; exact hd.2.2.1 d8 _
    let root3 := wRootSpec3x2k (k := 5) (wIdx3x32 wIdx) (wOut3x32 wOut) hIdxOut3
    let w3 := blockWires (rfl : 3 * 2 ^ 5 = 3 * 2 ^ 5) (wOut3x32 wOut)
    let hw3 : WInj w3 := wInj_blockWires rfl (wOut3x32_inj hd.2.2.2.2.1)
    let uLo5 := uLoOf (Nat.le_add_right 5 2) (wIdx3x32 wIdx)
    let hwq3 : ∀ b p, w3 b p ≠ qEnc := fun _ _ ↦ hd.2.2.2.2.2 _
    let huq3 : ∀ d, uLo5 d ≠ qEnc := fun d ↦ by
      dsimp only [uLo5]; rw [uLo5_eq_wIdx]; exact hd.2.2.2.1 ⟨d.val, by omega⟩
    let cGat0 := seqGatherParity 5 (wTail5 wOut) (wOut ⟨0, by omega⟩) (wTail5_ne_wOut0 hd.2.2.2.2.1)
    let hw91 : WInj (w91x2 wOut) := wInj_w91x2 hd.2.2.2.2.1
    .seq (.circuit (root3.cRootInit ;;ᶜ wTreePrefix 3 5 w3 hw3 5 le_rfl))
      (.seq (wShiftLevels v 3 5 uLo5 w3 qEnc hw3 hwq3 huq3 5 le_rfl)
        (.seq (.circuit (cGat0 ;;ᶜ wTreePrefix 91 1 (w91x2 wOut) hw91 1 le_rfl))
          (.seq (wShiftLevels v 91 1 (uBit5 wIdx) (w91x2 wOut) qEnc hw91
              (fun _ _ ↦ hd.2.2.2.2.2 _) (fun _ ↦ hd.2.2.2.1 _) 1 le_rfl)
            (.circuit (cGat0 ;;ᶜ wZeroGate wHas (wOut ⟨0, by omega⟩) (hd.1 _))))))
  else
    .circuit (seqNat 368 fun _ _ ↦ Circuit.T wHas)

theorem idxValD_wIdx3x32_update_wOut {n : ℕ} {wIdx : Fin 8 → Wire n} {wOut : Fin 192 → Wire n}
    (hIdxOut : ∀ d j, wIdx d ≠ wOut j) (δ : BitAssignment n) (j : Fin 192) (x : ZMod 2) :
    idxValD (wIdx3x32 wIdx) (Function.update δ (wOut j) x) = idxValD (wIdx3x32 wIdx) δ :=
  idxValD_congr (wIdx3x32 wIdx) fun d ↦ (wIdx3x32_mem wIdx d).elim fun d8 heq ↦
      heq ▸ Function.update_of_ne (hIdxOut d8 j) x δ

theorem seqGatherParity_wTail5_set {n : ℕ} {wOut : Fin 192 → Wire n}
    (hInj : ∀ i j : Fin 192, i ≠ j → wOut i ≠ wOut j)
    {δ : BitAssignment n} (hOut0 : ∀ j, δ (wOut j) = 0) (k : Fin 192)
        (hne : ∀ t, wTail5 wOut t ≠ wOut k) (tStar : Fin 5) :
    (seqGatherParity 5 (wTail5 wOut)
        (wOut k) hne).eval.1.mulVec (ket (Function.update δ (wTail5 wOut tStar) 1)) =
      ket (Function.update (Function.update δ (wTail5 wOut tStar) 1) (wOut k) 1) := by
  rw [seqGatherParity_mulVec_oneHot 5 (wTail5 wOut) (wOut k) hne _ tStar (fun t ↦
      if ht : t = tStar then ht ▸ (Function.update_self _ _ _).trans (ite_eq_left rfl).symm
      else (Function.update_of_ne (wTail5_inj_ne hInj ht) 1 δ).trans ((hOut0 _).trans
          (ite_eq_right ht).symm)),
    Function.update_of_ne (hne tStar).symm, hOut0 k, zero_add]

theorem seqGatherParity_wTail5_clr {n : ℕ} {wOut : Fin 192 → Wire n}
    (hInj : ∀ i j : Fin 192, i ≠ j → wOut i ≠ wOut j)
    {δ : BitAssignment n} (hOut0 : ∀ j, δ (wOut j) = 0) (k : Fin 192)
        (hne : ∀ t, wTail5 wOut t ≠ wOut k) (tStar : Fin 5) :
    (seqGatherParity 5 (wTail5 wOut) (wOut k) hne).eval.1.mulVec
      (ket (Function.update (Function.update δ (wTail5 wOut tStar) 1) (wOut k) 1)) =
          ket (Function.update δ (wTail5 wOut tStar) 1) := by
  rw [seqGatherParity_mulVec_oneHot 5 (wTail5 wOut) (wOut k) hne _ tStar (fun t ↦ by
      rw [Function.update_of_ne (hne t)]
      exact if ht : t = tStar then ht ▸ (Function.update_self _ _ _).trans (ite_eq_left rfl).symm
        else (Function.update_of_ne (wTail5_inj_ne hInj ht) 1 δ).trans ((hOut0 _).trans
            (ite_eq_right ht).symm)),
    Function.update_self, CharTwo.add_self_eq_zero, Function.update_idem,
    update_eq_self_of_zero ((Function.update_of_ne (hne tStar).symm 1 δ).trans (hOut0 k))]

theorem count_wComp187_368 {Var : Type} {n : ℕ} (v : Var) (wHas : Wire n) (wIdx : Fin 8 → Wire n)
    (wOut : Fin 192 → Wire n) (qEnc : Wire n) : (wComp187_368 v wHas wIdx wOut qEnc).count .T =
    368 ∧ (wComp187_368 v wHas wIdx wOut qEnc).count .TOFF = 0 := by
  dsimp only [wComp187_368]; split_ifs with hd
  · let root3 := wRootSpec3x2k (k := 5) (wIdx3x32 wIdx) (wOut3x32 wOut) (fun d j ↦
      (wIdx3x32_mem wIdx d).elim fun d8 heq ↦ heq ▸ hd.2.2.1 d8 _)
    have hw3 := wInj_blockWires (rfl : 3 * 2 ^ 5 = 3 * 2 ^ 5) (wOut3x32_inj hd.2.2.2.2.1)
    rcases root3.count_init, count_wTreePrefix 3 5 _ hw3 5 le_rfl,
      count_wShiftLevels v 3 5 (uLoOf (Nat.le_add_right 5 2) (wIdx3x32 wIdx)) _ qEnc hw3 (fun _ _ ↦
          hd.2.2.2.2.2 _)
        (fun d ↦ by rw [uLo5_eq_wIdx]; exact hd.2.2.2.1 ⟨d.val, by omega⟩) 5 le_rfl,
      count_wTreePrefix 91 1 (w91x2 wOut) (wInj_w91x2 hd.2.2.2.2.1) 1 le_rfl,
      count_wShiftLevels v 91 1 (uBit5 wIdx) (w91x2 wOut) qEnc (wInj_w91x2 hd.2.2.2.2.1)
          (fun _ _ ↦ hd.2.2.2.2.2 _)
        (fun _ ↦ hd.2.2.2.1 _) 1 le_rfl
      with ⟨⟨ri_t, ri_f⟩, ⟨tr_t, tr_f⟩, ⟨sh_t, sh_f⟩, ⟨t91_t, t91_f⟩, ⟨s91_t, s91_f⟩⟩
    dsimp only [DynamicCircuit.count]
    simp only [Circuit.count_seq, count_seqGatherParity_t, count_seqGatherParity_toff]
    rw [ri_t, ri_f, tr_t, tr_f, sh_t, sh_f, t91_t, t91_f, s91_t, s91_f]
    refine ⟨?_, ?_⟩ <;> simp [wZeroGate, Circuit.count_seq, Circuit.X, Circuit.CNOT]
  · exact ⟨(count_seqNat_T 1 368 _ fun _ _ ↦ by simp [Circuit.T]).trans (by omega),
      count_seqNat_TOFF_zero 368 _ fun _ _ ↦ by simp [Circuit.T]⟩

theorem dynWires_wComp187_368 {Var : Type} {n : ℕ} {S : Wire n → Prop} (v : Var) (wHas : Wire n)
    (wIdx : Fin 8 → Wire n) (wOut : Fin 192 → Wire n) (qEnc : Wire n) (hHas : S wHas)
    (hIdx : ∀ d, S (wIdx d)) (hOut : ∀ j, S (wOut j))
    (hQ : S qEnc) : DynWires S (wComp187_368 v wHas wIdx wOut qEnc) := by
  dsimp only [wComp187_368]; split_ifs with hd
  · let root3 := wRootSpec3x2k (k := 5) (wIdx3x32 wIdx) (wOut3x32 wOut) (fun d j ↦
      (wIdx3x32_mem wIdx d).elim fun d8 heq ↦ heq ▸ hd.2.2.1 d8 _)
    exact ⟨⟨root3.cw_init (fun d ↦ (wIdx3x32_mem wIdx d).elim fun d8 heq ↦ heq ▸ hIdx d8)
        (fun _ ↦ hOut _), cw_wTreePrefix 3 5 _ _
      (fun _ _ ↦ hOut _) 5 le_rfl⟩,
      dw_wShiftLevels v 3 5 _ _ qEnc _ _ _ (fun d ↦ (uLo5_eq_wIdx wIdx d) ▸ hIdx ⟨d.val, by omega⟩)
          (fun _ _ ↦ hOut _) hQ 5 le_rfl,
      ⟨cw_seqGatherParity 5 _ _ _ (fun _ ↦ hOut _) (hOut _), cw_wTreePrefix 91 1 _ _ (fun _ _ ↦
          hOut _) 1 le_rfl⟩,
      dw_wShiftLevels v 91 1 _ _ qEnc _ _ _ (fun _ ↦ hIdx _) (fun _ _ ↦ hOut _) hQ 1 le_rfl,
      ⟨cw_seqGatherParity 5 _ _ _ (fun _ ↦ hOut _)
          (hOut _), ⟨cw_1 (hOut _), cw_cnot hHas (hOut _)⟩⟩⟩
  · exact cw_seqNat 368 _ fun _ _ ↦ cw_1 hHas

theorem subspaceStep_wComp187_368 {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    (v : Var) (wHas : Wire n) (wIdx : Fin 8 → Wire n) (wOut : Fin 192 → Wire n) (qEnc : Wire n)
    (hd : WRouterDisj wHas wIdx wOut qEnc) (G : Operator (2 ^ n))
    (hSupp : SupportedOn (ValidWRouterIn187 wHas wIdx wOut qEnc) G) :
    SubspaceStep (Var := Var) G
      ((uOneHotToggle wHas wIdx wOut hd.has_ne_out hd.idx_ne_out).1 * G)
      (wComp187_368 v wHas wIdx wOut qEnc) := by
  have ket_sr (δ : BitAssignment n) : SplitRouterSeqBell26k.ket δ = ket δ := rfl
  have hdp := hd.disjProp
  unfold wComp187_368; rw [dite_eq_left hdp]
  let root3 := wRootSpec3x2k (k := 5) (wIdx3x32 wIdx) (wOut3x32 wOut) (fun d j ↦
    (wIdx3x32_mem wIdx d).elim fun d8 heq ↦ heq ▸ hdp.2.2.1 d8 _)
  let w3 := blockWires (rfl : 3 * 2 ^ 5 = 3 * 2 ^ 5) (wOut3x32 wOut)
  let hw3 : WInj w3 := wInj_blockWires rfl (wOut3x32_inj hdp.2.2.2.2.1)
  let uLo5 := uLoOf (Nat.le_add_right 5 2) (wIdx3x32 wIdx)
  let cGat0 := seqGatherParity 5 (wTail5 wOut) (wOut ⟨0, by omega⟩) (wTail5_ne_wOut0 hdp.2.2.2.2.1)
  let hw91 : WInj (w91x2 wOut) := wInj_w91x2 hdp.2.2.2.2.1
  classical
  let δMid (δ : BitAssignment n) : BitAssignment n :=
    if hV :
        ValidWRouterIn187 wHas wIdx wOut qEnc δ then if act91 wIdx δ then δ else Function.update δ
        (wOut (outIdx187 hV.2.2.1)) 1 else δ
  let M_fwd : Operator (2 ^ n) := (mkVecOp fun δ ↦ ket (δMid δ)) * G
  have hInact91 {δ : BitAssignment n} (hOut0 : ∀ j, δ (wOut j) = 0) (hq0 : δ qEnc = 0)
      (hLt : idxValD wIdx δ < 187) (hA : ¬ act91 wIdx δ) :
      let δ' := Function.update δ (wOut (outIdx187 hLt)) 1
      (wTreePrefix 91 1 (w91x2 wOut) hw91 1 le_rfl).eval.1.mulVec (ket (Function.update δ' (wOut ⟨0,
          by omega⟩) 1)) =
        wSuperVec (bFold91 wIdx) (uBit5 wIdx) (w91x2 wOut) qEnc δ' 0 (Nat.zero_le 1) ∧
      wSuperVec (bFold91 wIdx) (uBit5 wIdx) (w91x2 wOut) qEnc δ' 1 le_rfl =
        ket (Function.update δ' (wOut ⟨0, by omega⟩) 1) := by
    intro δ'
    obtain ⟨hb5_0, hDecomp, hGe91, hLt96⟩ := inact91_decomp wIdx δ hLt hA
    have hbEq : bFold91 wIdx δ' = ⟨0, by omega⟩ :=
        Fin.ext (ite_eq_right (c := idxValD (wIdx3x32 wIdx) δ' < 91)
      (by dsimp only [δ']; rw [idxValD_wIdx3x32_update_wOut hd.idx_ne_out]; omega))
    have hwTail : wOut (outIdx187 hLt) = wTail5 wOut ⟨idxValD (wIdx3x32 wIdx) δ - 91, by omega⟩
        := by
      unfold wTail5; exact congrArg wOut (Fin.ext hDecomp)
    have hw91_0 (m : Fin 91) (s : Fin (2 ^ 1)) : δ' (w91x2 wOut m s) = 0 :=
      (Function.update_of_ne (by rw [hwTail]; exact w91x2_ne_wTail5 hd.out_inj m s _) 1 δ).trans
          (hOut0 _)
    have hq' := (Function.update_of_ne (hd.out_ne_q (outIdx187 hLt)).symm 1 δ).trans hq0
    exact ⟨by
        rw [show wOut ⟨0, by omega⟩ = w91x2 wOut (bFold91 wIdx δ') ⟨0, by omega⟩ by
            rw [hbEq]; exact congrArg wOut (Fin.ext (by dsimp [w91x2])),
          wSuperVec_bot_pub (bFold91 wIdx) (uBit5 wIdx) (w91x2 wOut) hw91 qEnc δ' hw91_0 hq'],
      (wSuperVec_top_pub (bFold91 wIdx) (uBit5 wIdx) (w91x2 wOut) qEnc δ' hw91_0 hq').trans (by
        rw [hbEq]
        exact congrArg (fun w ↦ ket (Function.update δ' w 1)) (congrArg wOut (Fin.ext (by
          dsimp; rw [(idxValPrefix_congr (uBit5 wIdx) δ' δ
            (fun _ ↦
                Function.update_of_ne (hd.idx_ne_out _ (outIdx187 hLt)) 1 δ) 1 le_rfl).trans
                hb5_0]))))⟩
  have hStage3Eq : (cGat0 ;;ᶜ wTreePrefix 91 1 (w91x2 wOut) hw91 1 le_rfl).eval.1 *
      (wSuperOp root3.bStarFn uLo5 w3 qEnc 5 le_rfl * G) =
      wSuperOp (bFold91 wIdx) (uBit5 wIdx) (w91x2 wOut) qEnc 0 (Nat.zero_le 1) * M_fwd := by
    dsimp only [M_fwd]; rw [← Matrix.mul_assoc, ← Matrix.mul_assoc]
    refine hSupp _ _ fun δ hV ↦ ?_
    have ⟨hOut0, hq0, hLt, _⟩ := hV
    have hLt96 := idxValD_3x32_lt96 wIdx δ hLt
    have ht3Eq : w3 (root3.bStarFn δ)
        ⟨idxValPrefix uLo5 δ 5 le_rfl, idxValPrefix_lt_two_pow uLo5 δ 5 le_rfl⟩ =
        wOut3x32 wOut ⟨idxValD (wIdx3x32 wIdx) δ, hLt96⟩ :=
      congrArg (wOut3x32 wOut) (Fin.ext (root3.idx_decomp δ hLt96))
    rw [ket_sr, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, wSuperOp, mkVecOp_mulVec_ket,
      wSuperVec_top_pub root3.bStarFn uLo5 w3 qEnc δ (fun _ _ ↦ hOut0 _) hq0, eval_seq_mulVec,
          mkVecOp_mulVec_ket,
      wSuperOp, mkVecOp_mulVec_ket, ht3Eq]
    dsimp only [δMid]; rw [dite_eq_left hV]
    by_cases hA : act91 wIdx δ
    · rw [ite_eq_left hA,
        seqGatherParity_mulVec_zero 5 (wTail5 wOut) (wOut ⟨0, by omega⟩) _ _ (fun t ↦
          (Function.update_of_ne (wOut3x32_ne_wTail5_of_lt91 hdp.2.2.2.2.1 hA t).symm 1 δ).trans
              (hOut0 _)),
        show wOut3x32 wOut ⟨idxValD (wIdx3x32 wIdx) δ, hLt96⟩ = w91x2 wOut (bFold91 wIdx δ)
            ⟨0, by omega⟩ from
          congrArg wOut
              (Fin.ext (by dsimp [wOut3x32, w91x2]; rw [bFold91_val_pos wIdx δ hA])),
        wSuperVec_bot_pub (bFold91 wIdx) (uBit5 wIdx) (w91x2 wOut) hw91 qEnc δ (fun _ _ ↦
            hOut0 _) hq0]
    · obtain ⟨_, hDecomp, hGe91, _⟩ := inact91_decomp wIdx δ hLt hA
      let tStar : Fin 5 := ⟨idxValD (wIdx3x32 wIdx) δ - 91, by omega⟩
      have hwIdxTail : wOut (outIdx187 hLt) = wTail5 wOut tStar := by
        unfold wTail5; exact congrArg wOut (Fin.ext hDecomp)
      rw [ite_eq_right hA, show wOut3x32 wOut ⟨idxValD (wIdx3x32 wIdx) δ, hLt96⟩ = wTail5 wOut tStar
          from
        congrArg wOut (Fin.ext (by dsimp [wOut3x32, wTail5, tStar]; omega))]
      change (wTreePrefix 91 1 (w91x2 wOut) hw91 1 le_rfl).eval.1.mulVec
        (cGat0.eval.1.mulVec (ket (Function.update δ (wTail5 wOut tStar) 1))) = _
      rw [seqGatherParity_wTail5_set hd.out_inj hOut0 ⟨0, by omega⟩ _ tStar, ← hwIdxTail]
      exact (hInact91 hOut0 hq0 hLt hA).1
  have hEndEq : (cGat0 ;;ᶜ wZeroGate wHas (wOut ⟨0, by omega⟩) (hdp.1 _)).eval.1 *
      (wSuperOp (bFold91 wIdx) (uBit5 wIdx) (w91x2 wOut) qEnc 1 le_rfl * M_fwd) =
      (uOneHotToggle wHas wIdx wOut hd.has_ne_out hd.idx_ne_out).1 * G := by
    dsimp only [M_fwd]; rw [← Matrix.mul_assoc, ← Matrix.mul_assoc]
    refine hSupp _ _ fun δ ⟨hOut0, hq0, hLt, hZero⟩ ↦ ?_
    rw [ket_sr, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, mkVecOp_mulVec_ket, wSuperOp,
        mkVecOp_mulVec_ket,
      uOneHotToggle_mulVec_ket, eval_seq_mulVec, show cGat0.eval.1.mulVec (wSuperVec (bFold91 wIdx)
          (uBit5 wIdx) (w91x2 wOut) qEnc (δMid δ) 1 le_rfl) =
              ket (Function.update δ (wOut (outIdx187 hLt)) 1) by
        dsimp only [δMid]; rw [dite_eq_left ⟨hOut0, hq0, hLt, hZero⟩]
        by_cases hA : act91 wIdx δ
        · rw [ite_eq_left hA, wSuperVec_top_pub (bFold91 wIdx) (uBit5 wIdx)
              (w91x2 wOut) qEnc δ (fun _ _ ↦ hOut0 _) hq0]
          have hwEq : w91x2 wOut (bFold91 wIdx δ)
              ⟨idxValPrefix (uBit5 wIdx) δ 1 le_rfl, idxValPrefix_lt_two_pow _ δ 1 le_rfl⟩ =
                  wOut (outIdx187 hLt) :=
            (fun _ ↦ congrArg wOut (Fin.ext (by
              dsimp [w91x2, outIdx187]; rw [bFold91_val_pos wIdx δ hA]; omega)))
                  (idxValD_perm370 wIdx δ)
          exact hwEq ▸ seqGatherParity_mulVec_zero 5 (wTail5 wOut) (wOut ⟨0, by omega⟩) _ _ fun t ↦
            (Function.update_of_ne (w91x2_ne_wTail5 hd.out_inj _ _ t).symm 1 δ).trans (hOut0 _)
        · obtain ⟨_, hDecomp, hGe91, hLt96⟩ := inact91_decomp wIdx δ hLt hA
          have hwTail : wOut (outIdx187 hLt) = wTail5 wOut ⟨idxValD (wIdx3x32 wIdx) δ - 91,
              by omega⟩ := by
            unfold wTail5; exact congrArg wOut (Fin.ext hDecomp)
          rw [ite_eq_right hA, (hInact91 hOut0 hq0 hLt hA).2, hwTail]
          exact seqGatherParity_wTail5_clr hd.out_inj hOut0 ⟨0, by omega⟩ _ _,
      wZeroGate_ket (hd.has_ne_out _) (hd.has_ne_out _)
        (fun h0 ↦ congrArg wOut (Fin.ext (by dsimp [outIdx187]; rw [hZero h0])))]
    dsimp only [toggleOneHotBits];
        rw [dite_eq_left (Nat.lt_trans hLt (by omega)), hOut0 _, zero_add]
  exact (subspaceStep_congr_out (subspaceStep_of_circuit (Var := Var) G _)
      (hSupp _ _ fun δ ⟨hOut0, hq0, hLt, _⟩ ↦ by
        rw [ket_sr, eval_seq_mulVec, root3.init_ket δ (fun _ ↦ hOut0 _)
            (idxValD_3x32_lt96 wIdx δ hLt),
          wSuperVec_bot_pub root3.bStarFn uLo5 w3 hw3 qEnc δ (fun _ _ ↦ hOut0 _) hq0, wSuperOp,
              mkVecOp_mulVec_ket])).seq
    ((subspaceStep_mul_right G (subspaceStep_wShiftLevels v root3.bStarFn uLo5 w3 qEnc hw3
        (fun _ _ ↦ hdp.2.2.2.2.2 _)
        (fun d ↦ by dsimp only [uLo5]; rw [uLo5_eq_wIdx]; exact hdp.2.2.2.1 ⟨d.val, by omega⟩)
        (fun d _ _ ↦
            by dsimp only [uLo5]; rw [uLo5_eq_wIdx]; exact hdp.2.2.1 ⟨d.val,
                 by omega⟩ _) 5 le_rfl)).seq
      ((subspaceStep_congr_out (subspaceStep_of_circuit (Var := Var) _ _) hStage3Eq).seq
        ((subspaceStep_mul_right M_fwd (subspaceStep_wShiftLevels v (bFold91 wIdx) (uBit5 wIdx)
            (w91x2 wOut) qEnc hw91
            (fun _ _ ↦ hdp.2.2.2.2.2 _) (fun _ ↦ hdp.2.2.2.1 _)
                (fun _ _ _ ↦ hdp.2.2.1 _ _) 1 le_rfl)).seq
          (subspaceStep_congr_out (subspaceStep_of_circuit (Var := Var) _ _) hEndEq))))

section WrapLo187Irred
attribute [local irreducible] wComp187_368 wUncomp187_0
/--
Bracketed `368-T` (`0 .TOFF`, `0` pad) dynamic subroutine `wComp187_368 ;; mid ;; wUncomp187_0` .
-/
def wWrapLo187_368 {Var : Type} {n : ℕ} (v : Var) (wHas : Wire n) (wIdx : Fin 8 → Wire n)
    (wOut : Fin 192 → Wire n) (qEnc : Wire n) (mid : DynamicCircuit Var n) : DynamicCircuit Var n :=
    .seq (wComp187_368 v wHas wIdx wOut qEnc) (.seq mid (wUncomp187_0 v wHas wIdx wOut))
theorem count_wWrapLo187_368 {Var : Type} {n : ℕ} (v : Var) (wHas : Wire n) (wIdx : Fin 8 → Wire n)
    (wOut : Fin 192 → Wire n) (qEnc : Wire n) (mid : DynamicCircuit Var n) :
    (wWrapLo187_368 v wHas wIdx wOut qEnc mid).count .T = 368 + mid.count .T ∧
    (wWrapLo187_368 v wHas wIdx wOut qEnc mid).count .TOFF = mid.count .TOFF := by
  obtain ⟨tc, fc⟩ := count_wComp187_368 v wHas wIdx wOut qEnc; obtain ⟨tu, fu⟩ :=
      count_wUncomp187_0 v wHas wIdx wOut; dsimp only [wWrapLo187_368, DynamicCircuit.count]
  rw [tc, fc, tu, fu]; exact ⟨by omega, by omega⟩

theorem dynWires_wWrapLo187_368 {Var : Type} {n : ℕ} {S : Wire n → Prop} (v : Var) (wHas : Wire n)
    (wIdx : Fin 8 → Wire n) (wOut : Fin 192 → Wire n) (qEnc : Wire n) (mid : DynamicCircuit Var n)
    (hHas : S wHas) (hIdx : ∀ d, S (wIdx d)) (hOut : ∀ j, S (wOut j)) (hQ : S qEnc)
    (hMid : DynWires S mid) : DynWires S (wWrapLo187_368 v wHas wIdx wOut qEnc mid) :=
    ⟨dynWires_wComp187_368 v wHas wIdx wOut qEnc hHas hIdx hOut hQ, hMid,
    dynWires_wUncomp187_0 v wHas wIdx wOut hHas hIdx hOut⟩
theorem subspaceStep_wWrapLo187_368 {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    (v : Var) (wHas : Wire n) (wIdx : Fin 8 → Wire n) (wOut : Fin 192 → Wire n) (qEnc : Wire n)
    (hd : WRouterDisj wHas wIdx wOut qEnc) (mid : DynamicCircuit Var n)
    (R_in R_out : Operator (2 ^ n))
    (hSuppIn : SupportedOn (ValidWRouterIn187 wHas wIdx wOut qEnc) R_in)
    (hSuppOut : SupportedOn (ValidWRouterClean187 wHas wIdx wOut) R_out)
    (hMid : SubspaceStep (Var := Var)
      ((uOneHotToggle wHas wIdx wOut hd.has_ne_out hd.idx_ne_out).1 * R_in)
      ((uOneHotToggle wHas wIdx wOut hd.has_ne_out hd.idx_ne_out).1 * R_out) mid) :
    SubspaceStep (Var := Var) R_in R_out (wWrapLo187_368 v wHas wIdx wOut qEnc mid) :=
  (subspaceStep_wComp187_368 v wHas wIdx wOut qEnc hd R_in hSuppIn).seq
    (hMid.seq (subspaceStep_wUncomp187_0 v wHas wIdx wOut hd R_out hSuppOut))
end WrapLo187Irred

/-!
## Section 2: `wCompHi187_366` + `wUncompHi187_0` + `wWrapHi187_366` (`366 T` fwd / `0 T` rev)
-/

theorem wOut192_ne_of_val_ne {n : ℕ} {wOut : Fin 192 → Wire n}
    (hInj : ∀ i j : Fin 192, i ≠ j → wOut i ≠ wOut j) {i j : Fin 192} (hne : i.val ≠ j.val) :
    wOut i ≠ wOut j := hInj i j (fun e ↦ hne (congrArg Fin.val e))
theorem mulVec_seqGatherParity_invol {n : ℕ} (K : ℕ) (wSrc : Fin K → Wire n) (t : Wire n)
    (hne : ∀ i, wSrc i ≠ t) (v : Fin (2 ^ n) → ℂ) :
    (seqGatherParity K wSrc t hne).eval.1.mulVec ((seqGatherParity K wSrc t hne).eval.1.mulVec v) =
    v := by rw [Matrix.mulVec_mulVec, eval_seqGatherParity_mul_self, Matrix.one_mulVec]
theorem ket_wZeroGate_of_one_hi {n : ℕ} {wHas t0 : Wire n} (h : wHas ≠ t0) {δ : BitAssignment n}
    (h1 : δ wHas = 1) : (wZeroGate wHas t0 h).eval.1.mulVec (ket δ) = ket δ := by
  dsimp only [wZeroGate];
  rw [eval_seq_mulVec, ket_X, ket_CNOT, Function.update_of_ne h, h1, Function.update_self,
      add_assoc, CharTwo.add_self_eq_zero, add_zero, Function.update_idem, Function.update_eq_self]
theorem ket_wZeroGate_of_zero_hi {n : ℕ} {wHas t0 : Wire n} (h : wHas ≠ t0) {δ : BitAssignment n}
    (h0 : δ wHas = 0) : (wZeroGate wHas t0 h).eval.1.mulVec (ket δ) =
    ket (Function.update δ t0 (δ t0 + 1)) := by
  dsimp only [wZeroGate];
  have hc0 : Function.update δ t0 (δ t0 + 1) wHas = 0 :=
      (Function.update_of_ne h _ δ).trans h0; rw [eval_seq_mulVec, ket_X, ket_CNOT_ctrl_zero h hc0]

def ValidWRouterInHi187 {n : ℕ} (wHas : Wire n) (wIdx : Fin 8 → Wire n) (wOut : Fin 192 → Wire n)
    (qEnc : Wire n) (δ : BitAssignment n) : Prop :=
    (∀ j : Fin 192, δ (wOut j) = 0) ∧ δ qEnc = 0 ∧ idxValD wIdx δ < 187 ∧
    (δ wHas = 0 → idxValD wIdx δ = 0) ∧ (δ wHas = 1 → idxValD wIdx δ ≠ 0)
def ValidWRouterCleanHi187 {n : ℕ} (wHas : Wire n) (wIdx : Fin 8 → Wire n) (wOut : Fin 192 → Wire n)
    (δ : BitAssignment n) : Prop :=
    (∀ j : Fin 192, δ (wOut j) = 0) ∧ idxValD wIdx δ < 187 ∧ (δ wHas = 0 → idxValD wIdx δ = 0) ∧
    (δ wHas = 1 → idxValD wIdx δ ≠ 0)
noncomputable instance instDecidableValidWRouterCleanHi187 {n : ℕ} (wHas : Wire n)
    (wIdx : Fin 8 → Wire n) (wOut : Fin 192 → Wire n) :
    DecidablePred (ValidWRouterCleanHi187 wHas wIdx wOut) :=
  Classical.decPred _

/-- `96`-wire Stage-A slice redirecting `j = 0` onto `wOut[32]` (`0` touches on `wOut[0]`). -/
def wOut3x32Hi {n : ℕ} (wOut : Fin 192 → Wire n) (j : Fin (3 * 2 ^ 5)) : Wire n :=
  if j.val = 0 then wOut ⟨32, by omega⟩ else wOut3x32 wOut j

theorem wOut3x32Hi_mem {n : ℕ} (wOut : Fin 192 → Wire n) (j : Fin (3 * 2 ^ 5)) : ∃ k : Fin 192,
    wOut3x32Hi wOut j = wOut k := by unfold wOut3x32Hi wOut3x32; split_ifs <;> exact ⟨_, rfl⟩
theorem w3Hi_ne_of_wOut_ne {n : ℕ} {wOut : Fin 192 → Wire n} {u : Wire n}
    (h : ∀ k : Fin 192, wOut k ≠ u) (b : Fin 3) (p : Fin (2 ^ 5))
    : blockWires (rfl : 3 * 2 ^ 5 = 3 * 2 ^ 5) (wOut3x32Hi wOut) b p ≠ u :=
  (wOut3x32Hi_mem wOut ⟨b.val * 2 ^ 5 + p.val, blockIdx_lt rfl b p⟩).elim fun k hok ↦
    (show blockWires (rfl : 3 * 2 ^ 5 = 3 * 2 ^ 5) (wOut3x32Hi wOut) b p = wOut k from hok) ▸ h k

theorem ne_w3Hi_of_ne_wOut {n : ℕ} {wOut : Fin 192 → Wire n} {u : Wire n}
    (h : ∀ k : Fin 192, u ≠ wOut k) (b : Fin 3) (p : Fin (2 ^ 5))
    : u ≠ blockWires (rfl : 3 * 2 ^ 5 = 3 * 2 ^ 5) (wOut3x32Hi wOut) b p :=
  (wOut3x32Hi_mem wOut ⟨b.val * 2 ^ 5 + p.val, blockIdx_lt rfl b p⟩).elim fun k hok ↦
    (show blockWires (rfl : 3 * 2 ^ 5 = 3 * 2 ^ 5) (wOut3x32Hi wOut) b p = wOut k from hok) ▸ h k

theorem wOut3x32Hi_inj {n : ℕ} {wOut : Fin 192 → Wire n} (hInj : ∀ i j : Fin 192, i ≠ j → wOut i ≠
    wOut j) : ∀ i j : Fin
    (3 * 2 ^ 5), i ≠ j → wOut3x32Hi wOut i ≠ wOut3x32Hi wOut j := fun i j hne heq ↦
  hne <| Fin.ext <| (fun _ _ ↦ by
    unfold wOut3x32Hi wOut3x32 at heq; split_ifs at heq <;> first | omega |
      exact (fun h ↦ by dsimp at h; omega) (Fin.mk.inj_iff.mp (Classical.byContradiction fun h' ↦
          hInj _ _ h' heq))) i.isLt j.isLt

/--
`90 × 2` Stage-B leaf-split array (`m' = 1..90`), completely disjoint from `wOut[0]` and `wOut[32]`
.
-/
def wPair90 {n : ℕ} (wOut : Fin 192 → Wire n) (m : Fin 90) (s : Fin (2 ^ 1)) : Wire n :=
  w91x2 wOut ⟨m.val + 1, by omega⟩ s

theorem wInj_wPair90 {n : ℕ} {wOut : Fin 192 → Wire n} (hInj : ∀ i j : Fin 192, i ≠ j → wOut i ≠
    wOut j) : WInj (wPair90 wOut) := by
  intro b₁ p₁ b₂ p₂ heq
  obtain ⟨hb, hp⟩ := wInj_w91x2 hInj ⟨b₁.val + 1, by omega⟩ p₁ ⟨b₂.val + 1, by omega⟩ p₂ heq
  exact ⟨Fin.ext (by have h := congrArg Fin.val hb; dsimp at h; omega), hp⟩

def bStarHi90 {n : ℕ} (wIdx : Fin 8 → Wire n) (δ : BitAssignment n) : Fin 90 :=
  ⟨if 1 ≤ idxValD (wIdx3x32 wIdx) δ ∧ idxValD (wIdx3x32 wIdx) δ ≤ 90
    then idxValD (wIdx3x32 wIdx) δ - 1 else 0, by split_ifs <;> omega⟩

theorem wTail5_ne_wOut1 {n : ℕ} {wOut : Fin 192 → Wire n}
    (hInj : ∀ i j : Fin 192, i ≠ j → wOut i ≠ wOut j) (t : Fin 5) :
    wTail5 wOut t ≠ wOut ⟨1, by omega⟩ :=
  hInj _ _ (by intro e; have := t.isLt; have h := congrArg Fin.val e; dsimp at h; omega)

theorem wTail5_ne_wOut32 {n : ℕ} {wOut : Fin 192 → Wire n}
    (hInj : ∀ i j : Fin 192, i ≠ j → wOut i ≠ wOut j) (t : Fin 5) :
    wTail5 wOut t ≠ wOut ⟨32, by omega⟩ :=
  hInj _ _ (by intro e; have := t.isLt; have h := congrArg Fin.val e; dsimp at h; omega)

def cPreHi187 {n : ℕ} (wOut : Fin 192 → Wire n) (hInj : ∀ i j : Fin 192, i ≠ j → wOut i ≠ wOut j) :
    Circuit n :=
  Circuit.CNOT (wOut ⟨32, by omega⟩) (wOut ⟨1, by omega⟩)
    (wOut192_ne_of_val_ne hInj (by dsimp; omega)) ;;ᶜ
  seqGatherParity 5 (wTail5 wOut) (wOut ⟨1, by omega⟩) (wTail5_ne_wOut1 hInj)

def cPreHi187Inv {n : ℕ} (wOut : Fin 192 → Wire n) (hInj : ∀ i j : Fin 192, i ≠ j → wOut i ≠
    wOut j) : Circuit n :=
  seqGatherParity 5 (wTail5 wOut) (wOut ⟨1, by omega⟩) (wTail5_ne_wOut1 hInj) ;;ᶜ
  Circuit.CNOT (wOut ⟨32, by omega⟩) (wOut ⟨1, by omega⟩)
    (wOut192_ne_of_val_ne hInj (by dsimp; omega))

def cPostHi187 {n : ℕ} (wHas : Wire n) (wOut : Fin 192 → Wire n) (hHasOut : ∀ j, wHas ≠ wOut j)
    (hInj : ∀ i j : Fin 192, i ≠ j → wOut i ≠ wOut j) : Circuit n :=
  (wZeroGate wHas (wOut ⟨32, by omega⟩) (hHasOut _) ;;ᶜ
    Circuit.CNOT (wOut ⟨32, by omega⟩) (wOut ⟨33, by omega⟩)
      (wOut192_ne_of_val_ne hInj (by dsimp; omega))) ;;ᶜ
  (seqGatherParity 5 (wTail5 wOut) (wOut ⟨1, by omega⟩) (wTail5_ne_wOut1 hInj) ;;ᶜ
    wZeroGate wHas (wOut ⟨1, by omega⟩) (hHasOut _))

def cPostHi187Inv {n : ℕ} (wHas : Wire n) (wOut : Fin 192 → Wire n) (hHasOut : ∀ j, wHas ≠ wOut j)
    (hInj : ∀ i j : Fin 192, i ≠ j → wOut i ≠ wOut j) : Circuit n :=
  (wUnzeroGate wHas (wOut ⟨1, by omega⟩) (hHasOut _) ;;ᶜ
    seqGatherParity 5 (wTail5 wOut) (wOut ⟨1, by omega⟩) (wTail5_ne_wOut1 hInj)) ;;ᶜ
  (Circuit.CNOT (wOut ⟨32, by omega⟩) (wOut ⟨33, by omega⟩)
      (wOut192_ne_of_val_ne hInj (by dsimp; omega)) ;;ᶜ
    wUnzeroGate wHas (wOut ⟨32, by omega⟩) (hHasOut _))

/--
Exact `366-T` (`186 + 180 = 366 T`, `0 .TOFF` , `0` pad, `0 wOut[0]` ) forward `Hi187` W-state
loader.
-/
def wCompHi187_366 {Var : Type} {n : ℕ} (v : Var) (wHas : Wire n) (wIdx : Fin 8 → Wire n)
    (wOut : Fin 192 → Wire n) (qEnc : Wire n) : DynamicCircuit Var n :=
  if hd : WRouterDisjProp wHas wIdx wOut qEnc then
    let hIdxOut3 : ∀ d j, wIdx3x32 wIdx d ≠ wOut3x32Hi wOut j := fun d j ↦ by
      obtain ⟨d8, heq⟩ := wIdx3x32_mem wIdx d; obtain ⟨k, hok⟩ := wOut3x32Hi_mem wOut j
      rw [heq, hok]; exact hd.2.2.1 d8 k
    let root3 := wRootSpec3x2k (k := 5) (wIdx3x32 wIdx) (wOut3x32Hi wOut) hIdxOut3
    let w3 := blockWires (rfl : 3 * 2 ^ 5 = 3 * 2 ^ 5) (wOut3x32Hi wOut)
    let hw3 : WInj w3 := wInj_blockWires rfl (wOut3x32Hi_inj hd.2.2.2.2.1)
    let uLo5 := uLoOf (Nat.le_add_right 5 2) (wIdx3x32 wIdx)
    let hwq3 : ∀ b p, w3 b p ≠ qEnc := w3Hi_ne_of_wOut_ne hd.2.2.2.2.2
    let huq3 : ∀ d, uLo5 d ≠ qEnc := fun d ↦ by
      dsimp only [uLo5]; rw [uLo5_eq_wIdx]; exact hd.2.2.2.1 ⟨d.val, by omega⟩
    let hw90 : WInj (wPair90 wOut) := wInj_wPair90 hd.2.2.2.2.1
    .seq (.circuit (root3.cRootInit ;;ᶜ wTreePrefix 3 5 w3 hw3 5 le_rfl))
      (.seq (wShiftLevels v 3 5 uLo5 w3 qEnc hw3 hwq3 huq3 5 le_rfl)
        (.seq (.circuit (cPreHi187 wOut hd.2.2.2.2.1 ;;ᶜ
            wTreePrefix 90 1 (wPair90 wOut) hw90 1 le_rfl))
          (.seq (wShiftLevels v 90 1 (uBit5 wIdx) (wPair90 wOut) qEnc hw90
              (fun _ _ ↦ hd.2.2.2.2.2 _) (fun _ ↦ hd.2.2.2.1 _) 1 le_rfl)
            (.circuit (cPostHi187 wHas wOut hd.1 hd.2.2.2.2.1)))))
  else
    .circuit (seqNat 366 fun _ _ ↦ Circuit.T wHas)

/-- Exact `0-T` (`0 .TOFF`, `0` pad, `0 wOut[0]`) MBU reverse `Hi187` W-state unloader. -/
def wUncompHi187_0 {Var : Type} {n : ℕ} (v : Var) (wHas : Wire n) (wIdx : Fin 8 → Wire n)
    (wOut : Fin 192 → Wire n) : DynamicCircuit Var n :=
  if ho : WRouterOutDisj wHas wIdx wOut then
    let hIdxOut3 : ∀ d j, wIdx3x32 wIdx d ≠ wOut3x32Hi wOut j := fun d j ↦ by
      obtain ⟨d8, heq⟩ := wIdx3x32_mem wIdx d; obtain ⟨k, hok⟩ := wOut3x32Hi_mem wOut j
      rw [heq, hok]; exact ho.2.1 d8 k
    let root3 := wRootSpec3x2k (k := 5) (wIdx3x32 wIdx) (wOut3x32Hi wOut) hIdxOut3
    let w3 := blockWires (rfl : 3 * 2 ^ 5 = 3 * 2 ^ 5) (wOut3x32Hi wOut)
    let hw3 : WInj w3 := wInj_blockWires rfl (wOut3x32Hi_inj ho.2.2)
    let uLo5 := uLoOf (Nat.le_add_right 5 2) (wIdx3x32 wIdx)
    let huw3 : ∀ d b p, uLo5 d ≠ w3 b p := fun d ↦ by
      dsimp only [uLo5]; rw [uLo5_eq_wIdx]; exact ne_w3Hi_of_ne_wOut (ho.2.1 ⟨d.val, by omega⟩)
    let hw90 : WInj (wPair90 wOut) := wInj_wPair90 ho.2.2
    let huw90 : ∀ d b p, uBit5 wIdx d ≠ wPair90 wOut b p := fun _ _ _ ↦ ho.2.1 _ _
    .seq (.circuit (cPostHi187Inv wHas wOut ho.1 ho.2.2))
      (.seq (wUncompTreeDyn v 90 1 (uBit5 wIdx) (wPair90 wOut) hw90 huw90
          (.circuit .identity) 1 le_rfl)
        (.seq (.circuit (cPreHi187Inv wOut ho.2.2))
          (wUncompTreeDyn v 3 5 uLo5 w3 hw3 huw3 (.circuit root3.cRootUninit) 5 le_rfl)))
  else
    .circuit .identity

theorem wIdx3x32_lift {n : ℕ} {P : Wire n → Prop} {wIdx : Fin 8 → Wire n} (h : ∀ d, P (wIdx d))
    (d : Fin (5 + 2)) : P (wIdx3x32 wIdx d) :=
  (wIdx3x32_mem wIdx d).elim fun d8 heq ↦ heq ▸ h d8

theorem wOut3x32Hi_lift {n : ℕ} {P : Wire n → Prop} {wOut : Fin 192 → Wire n} (h : ∀ j, P (wOut j))
    (j : Fin (3 * 2 ^ 5)) : P
    (wOut3x32Hi wOut j) :=
  (wOut3x32Hi_mem wOut j).elim fun k hok ↦ hok ▸ h k

theorem wIdx3x32_ne_Hi {n : ℕ} {wIdx : Fin 8 → Wire n} {wOut : Fin 192 → Wire n}
    (h : ∀ d j, wIdx d ≠ wOut j) (d : Fin (5 + 2)) (j : Fin
  (3 * 2 ^ 5)) :
    wIdx3x32 wIdx d ≠ wOut3x32Hi wOut j :=
  (wIdx3x32_mem wIdx d).elim fun d8 heq ↦ (wOut3x32Hi_mem wOut j).elim fun k hok ↦
      heq ▸ hok ▸ h d8 k

def δ_rHi187 {n : ℕ} (wIdx : Fin 8 → Wire n) (wOut : Fin 192 → Wire n)
    (δ : BitAssignment n) : BitAssignment n :=
  if idxValD (wIdx3x32 wIdx) δ = 0 then
    Function.update δ (wOut ⟨32, by omega⟩) 1
  else if idxValD (wIdx3x32 wIdx) δ ≤ 90 then
    δ
  else
    Function.update δ (wTail5 wOut ⟨min (idxValD (wIdx3x32 wIdx) δ - 91) 4, by omega⟩) 1

theorem bStarHi90_δ_rHi187 {n : ℕ} {wIdx : Fin 8 → Wire n} {wOut : Fin 192 → Wire n}
    (hIdxOut : ∀ d j, wIdx d ≠ wOut j) (δ : BitAssignment n) :
    bStarHi90 wIdx (δ_rHi187 wIdx wOut δ) = bStarHi90 wIdx δ := by
  dsimp only [δ_rHi187]; split_ifs <;>
    first
      | rfl
      | exact Fin.ext
            (by dsimp only [bStarHi90, wTail5]; rw [idxValD_wIdx3x32_update_wOut hIdxOut])

theorem δ_rHi187_wPair90 {n : ℕ} {wIdx : Fin 8 → Wire n} {wOut : Fin 192 → Wire n}
    (hInj : ∀ i j : Fin 192, i ≠ j → wOut i ≠ wOut j) {δ : BitAssignment n}
        (hOut0 : ∀ j : Fin 192, δ (wOut j) = 0)
    (m : Fin 90) (s : Fin (2 ^ 1)) : δ_rHi187 wIdx wOut δ (wPair90 wOut m s) = 0 := by
  have hne : wPair90 wOut m s ≠ wOut ⟨32, by omega⟩ :=
    wOut192_ne_of_val_ne hInj ((fun _ _ ↦ by dsimp [wPair90, w91x2]; omega) m.isLt s.isLt)
  dsimp only [δ_rHi187]; split_ifs <;> first
    | exact hOut0 _ | exact (Function.update_of_ne hne 1 δ).trans (hOut0 _)
    | (dsimp only [wPair90];
        exact (Function.update_of_ne (w91x2_ne_wTail5 hInj ⟨m.val + 1,
            by omega⟩ s _) 1 δ).trans (hOut0 _))

attribute [local irreducible] wCompHi187_366 wUncompHi187_0
/--
Bracketed `366-T` (`0 .TOFF`, `0` pad, `0 wOut[0]` ) dynamic subroutine
`wCompHi187_366 ;; mid ;; wUncompHi187_0` .
-/
def wWrapHi187_366 {Var : Type} {n : ℕ} (v : Var) (wHas : Wire n) (wIdx : Fin 8 → Wire n)
    (wOut : Fin 192 → Wire n) (qEnc : Wire n) (mid : DynamicCircuit Var n) : DynamicCircuit Var n :=
    .seq (wCompHi187_366 v wHas wIdx wOut qEnc) (.seq mid (wUncompHi187_0 v wHas wIdx wOut))
theorem count_wWrapHi187_366 {Var : Type} {n : ℕ} (v : Var) (wHas : Wire n) (wIdx : Fin 8 → Wire n)
    (wOut : Fin 192 → Wire n) (qEnc : Wire n) (mid : DynamicCircuit Var n) :
    (wWrapHi187_366 v wHas wIdx wOut qEnc mid).count .T = 366 + mid.count .T ∧
    (wWrapHi187_366 v wHas wIdx wOut qEnc mid).count .TOFF = mid.count .TOFF := by
  have ⟨tc, fc⟩ : (wCompHi187_366 v wHas wIdx wOut qEnc).count .T = 366 ∧
      (wCompHi187_366 v wHas wIdx wOut qEnc).count .TOFF = 0 := by
    unfold wCompHi187_366; dsimp only; split_ifs with hd
    · let root3 :=
          wRootSpec3x2k (k := 5) (wIdx3x32 wIdx) (wOut3x32Hi wOut) (wIdx3x32_ne_Hi hd.2.2.1)
      have hw3 := wInj_blockWires (rfl : 3 * 2 ^ 5 = 3 * 2 ^ 5) (wOut3x32Hi_inj hd.2.2.2.2.1)
      rcases root3.count_init, count_wTreePrefix 3 5 _ hw3 5 le_rfl,
        count_wShiftLevels v 3 5 (uLoOf (Nat.le_add_right 5 2) (wIdx3x32 wIdx)) _ qEnc hw3
          (w3Hi_ne_of_wOut_ne hd.2.2.2.2.2)
          (fun d ↦ by rw [uLo5_eq_wIdx]; exact hd.2.2.2.1 ⟨d.val, by omega⟩) 5 le_rfl,
        count_wTreePrefix 90 1 (wPair90 wOut) (wInj_wPair90 hd.2.2.2.2.1) 1 le_rfl,
        count_wShiftLevels v 90 1 (uBit5 wIdx) (wPair90 wOut) qEnc (wInj_wPair90 hd.2.2.2.2.1)
          (fun _ _ ↦ hd.2.2.2.2.2 _) (fun _ ↦ hd.2.2.2.1 _) 1 le_rfl
        with ⟨⟨ri_t, ri_f⟩, ⟨tr_t, tr_f⟩, ⟨sh_t, sh_f⟩, ⟨t90_t, t90_f⟩, ⟨s90_t, s90_f⟩⟩
      dsimp only [DynamicCircuit.count]; simp only [Circuit.count_seq]
      rw [ri_t, ri_f, tr_t, tr_f, sh_t, sh_f, t90_t, t90_f, s90_t, s90_f]
      refine ⟨?_, ?_⟩ <;> simp [cPreHi187, cPostHi187, wZeroGate, Circuit.count_seq, Circuit.X,
          Circuit.CNOT,
        count_seqGatherParity_t, count_seqGatherParity_toff]
    · exact ⟨(count_seqNat_T 1 366 _ fun _ _ ↦ by simp [Circuit.T]).trans (by omega),
        count_seqNat_TOFF_zero 366 _ fun _ _ ↦ by simp [Circuit.T]⟩
  have ⟨tu, fu⟩ : (wUncompHi187_0 v wHas wIdx wOut).count .T = 0 ∧
      (wUncompHi187_0 v wHas wIdx wOut).count .TOFF = 0 := by
    unfold wUncompHi187_0; dsimp only; split_ifs with ho
    · let root3 := wRootSpec3x2k (k := 5) (wIdx3x32 wIdx) (wOut3x32Hi wOut) (wIdx3x32_ne_Hi ho.2.1)
      rcases root3.count_uninit,
        count_wUncompTreeDyn_opt v 90 1 (uBit5 wIdx) (wPair90 wOut) (wInj_wPair90 ho.2.2)
          (fun _ _ _ ↦ ho.2.1 _ _) (.circuit .identity) 1 le_rfl,
        count_wUncompTreeDyn_opt v 3 5 (uLoOf (Nat.le_add_right 5 2) (wIdx3x32 wIdx))
          (blockWires (rfl : 3 * 2 ^ 5 = 3 * 2 ^ 5) (wOut3x32Hi wOut))
          (wInj_blockWires rfl (wOut3x32Hi_inj ho.2.2))
          (fun d ↦ by rw [uLo5_eq_wIdx]; exact ne_w3Hi_of_ne_wOut (ho.2.1 ⟨d.val, by omega⟩))
          (.circuit root3.cRootUninit) 5 le_rfl
        with ⟨⟨ru_t, ru_f⟩, ⟨tr90_t, tr90_f⟩, ⟨tr3_t, tr3_f⟩⟩
      dsimp only [DynamicCircuit.count] at tr90_t tr90_f tr3_t tr3_f ⊢
      rw [tr90_t, tr90_f, tr3_t, tr3_f, ru_t, ru_f]
      refine ⟨?_, ?_⟩ <;>
          simp [cPostHi187Inv, cPreHi187Inv, wUnzeroGate, Circuit.count_seq, Circuit.X,
          Circuit.CNOT, count_seqGatherParity_t, count_seqGatherParity_toff]
    · exact ⟨rfl, rfl⟩
  dsimp only [wWrapHi187_366, DynamicCircuit.count]; rw [tc, fc, tu, fu]; exact ⟨by omega,
      by omega⟩

theorem dynWires_wWrapHi187_366 {Var : Type} {n : ℕ} {S : Wire n → Prop} (v : Var) (wHas : Wire n)
    (wIdx : Fin 8 → Wire n) (wOut : Fin 192 → Wire n) (qEnc : Wire n) (mid : DynamicCircuit Var n)
    (hHas : S wHas) (hIdx : ∀ d, S (wIdx d)) (hOut : ∀ j, S (wOut j)) (hQ : S qEnc)
    (hMid : DynWires S mid) : DynWires S (wWrapHi187_366 v wHas wIdx wOut qEnc mid) :=
  by
    have hO3 := wOut3x32Hi_lift hOut
    refine ⟨?_, hMid, ?_⟩
    · unfold wCompHi187_366; dsimp only; split_ifs with hd
      · let root3 :=
            wRootSpec3x2k (k := 5) (wIdx3x32 wIdx) (wOut3x32Hi wOut) (wIdx3x32_ne_Hi hd.2.2.1)
        exact ⟨⟨root3.cw_init (wIdx3x32_lift hIdx) hO3, cw_wTreePrefix 3 5 _ _ (fun _ _ ↦
            hO3 _) 5 le_rfl⟩,
          dw_wShiftLevels v 3 5 _ _ qEnc _ _ _ (fun d ↦ (uLo5_eq_wIdx wIdx d) ▸ hIdx ⟨d.val,
              by omega⟩)
            (fun _ _ ↦ hO3 _) hQ 5 le_rfl,
          ⟨⟨cw_cnot (hOut _) (hOut _), cw_seqGatherParity 5 _ _ _ (fun _ ↦ hOut _) (hOut _)⟩,
            cw_wTreePrefix 90 1 _ _ (fun _ _ ↦ hOut _) 1 le_rfl⟩,
          dw_wShiftLevels v 90 1 _ _ qEnc _ _ _ (fun _ ↦ hIdx _) (fun _ _ ↦ hOut _) hQ 1 le_rfl,
          ⟨⟨⟨cw_1 (hOut _), cw_cnot hHas (hOut _)⟩, cw_cnot (hOut _) (hOut _)⟩,
           ⟨cw_seqGatherParity 5 _ _ _ (fun _ ↦ hOut _)
               (hOut _), ⟨cw_1 (hOut _), cw_cnot hHas (hOut _)⟩⟩⟩⟩
      · exact cw_seqNat 366 _ fun _ _ ↦ cw_1 hHas
    · unfold wUncompHi187_0; dsimp only; split_ifs with ho
      · let root3 :=
            wRootSpec3x2k (k := 5) (wIdx3x32 wIdx) (wOut3x32Hi wOut) (wIdx3x32_ne_Hi ho.2.1)
        exact ⟨⟨⟨⟨cw_cnot hHas (hOut _), cw_1 (hOut _)⟩, cw_seqGatherParity 5 _ _ _ (fun _ ↦ hOut _)
            (hOut _)⟩,
            ⟨cw_cnot (hOut _) (hOut _), ⟨cw_cnot hHas (hOut _), cw_1 (hOut _)⟩⟩⟩,
          dw_wUncompTreeDyn_opt v 90 1 _ _ _ _ (fun _ ↦ hIdx _) (fun _ _ ↦ hOut _)
            (rest := .circuit .identity) trivial 1 le_rfl,
          ⟨cw_seqGatherParity 5 _ _ _ (fun _ ↦ hOut _) (hOut _), cw_cnot (hOut _) (hOut _)⟩,
          dw_wUncompTreeDyn_opt v 3 5 _ _ _ _ (fun d ↦ (uLo5_eq_wIdx wIdx d) ▸ hIdx ⟨d.val,
              by omega⟩)
            (fun _ _ ↦ hO3 _) (rest := .circuit root3.cRootUninit)
            (root3.cw_uninit (wIdx3x32_lift hIdx) hO3) 5 le_rfl⟩
      · exact trivial
set_option maxHeartbeats 800000 in
-- Large circuit/register elaboration requires raised heartbeat limit.
theorem subspaceStep_wWrapHi187_366 {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    (v : Var) (wHas : Wire n) (wIdx : Fin 8 → Wire n) (wOut : Fin 192 → Wire n) (qEnc : Wire n)
    (hd : WRouterDisj wHas wIdx wOut qEnc) (mid : DynamicCircuit Var n)
    (R_in R_out : Operator (2 ^ n))
    (hSuppIn : SupportedOn (ValidWRouterInHi187 wHas wIdx wOut qEnc) R_in)
    (hSuppOut : SupportedOn (ValidWRouterCleanHi187 wHas wIdx wOut) R_out)
    (hMid : SubspaceStep (Var := Var)
      ((uOneHotToggle wHas wIdx wOut hd.has_ne_out hd.idx_ne_out).1 * R_in)
      ((uOneHotToggle wHas wIdx wOut hd.has_ne_out hd.idx_ne_out).1 * R_out) mid) :
    SubspaceStep (Var := Var) R_in R_out (wWrapHi187_366 v wHas wIdx wOut qEnc mid) :=
  by
    have ket_sr (δ : BitAssignment n) : SplitRouterSeqBell26k.ket δ = ket δ := rfl
    have hdp := hd.disjProp
    have ho := hd.outDisj
    let root3 := wRootSpec3x2k (k := 5) (wIdx3x32 wIdx) (wOut3x32Hi wOut) (wIdx3x32_ne_Hi hdp.2.2.1)
    let w3 := blockWires (rfl : 3 * 2 ^ 5 = 3 * 2 ^ 5) (wOut3x32Hi wOut)
    let hw3 : WInj w3 := wInj_blockWires rfl (wOut3x32Hi_inj hdp.2.2.2.2.1)
    let uLo5 := uLoOf (Nat.le_add_right 5 2) (wIdx3x32 wIdx)
    let hw90 := wInj_wPair90 hd.out_inj
    have hw3Eq {δ : BitAssignment n} (hLt : idxValD wIdx δ < 187) :
        w3 (root3.bStarFn δ) ⟨idxValPrefix uLo5 δ 5 le_rfl, idxValPrefix_lt_two_pow _ δ 5 le_rfl⟩ =
        wOut3x32Hi wOut ⟨idxValD (wIdx3x32 wIdx) δ, idxValD_3x32_lt96 wIdx δ hLt⟩ :=
      congrArg (wOut3x32Hi wOut) (Fin.ext (root3.idx_decomp δ (idxValD_3x32_lt96 wIdx δ hLt)))
    have hqEnc {δ : BitAssignment n} (hq0 : δ qEnc = 0) : δ_rHi187 wIdx wOut δ qEnc = 0 := by
      dsimp only [δ_rHi187]; split_ifs <;>
        first | exact hq0 | exact (Function.update_of_ne (hd.out_ne_q _).symm 1 δ).trans hq0
    let hInj := hd.out_inj
    have hne32_1 :=
        wOut192_ne_of_val_ne hInj (i := ⟨32, by omega⟩) (j := ⟨1, by omega⟩) (by dsimp; omega)
    have hne32_33 :=
        wOut192_ne_of_val_ne hInj (i := ⟨32, by omega⟩) (j := ⟨33, by omega⟩) (by dsimp; omega)
    have hwP00 : wPair90 wOut ⟨0, by omega⟩ ⟨0, by omega⟩ = wOut ⟨1, by omega⟩ :=
      congrArg wOut (Fin.ext (by dsimp [wPair90, w91x2]))
    have hPreKet {δ : BitAssignment n} (hOut0 : ∀ j : Fin 192, δ (wOut j) = 0)
        (hLt : idxValD wIdx δ < 187) :
        (cPreHi187 wOut hInj).eval.1.mulVec (ket (Function.update δ
          (wOut3x32Hi wOut ⟨idxValD (wIdx3x32 wIdx) δ, idxValD_3x32_lt96 wIdx δ hLt⟩) 1)) =
        ket (Function.update (δ_rHi187 wIdx wOut δ) (wPair90 wOut (bStarHi90 wIdx δ)
            ⟨0, by omega⟩) 1) := by
      have hq96 := idxValD_3x32_lt96 wIdx δ hLt
      dsimp only [cPreHi187]; rw [eval_seq_mulVec]
      by_cases hq0 : idxValD (wIdx3x32 wIdx) δ = 0
      · rw [show wOut3x32Hi wOut ⟨idxValD (wIdx3x32 wIdx) δ, hq96⟩ =
            wOut ⟨32, by omega⟩ from ite_eq_left hq0,
          ket_CNOT, (Function.update_of_ne hne32_1.symm 1 δ).trans (hOut0 _), Function.update_self,
              zero_add,
          show δ_rHi187 wIdx wOut δ = Function.update δ (wOut ⟨32, by omega⟩) 1 from ite_eq_left
              hq0,
          show bStarHi90 wIdx δ =
              ⟨0, by omega⟩ from Fin.ext (by dsimp only [bStarHi90]; rw [hq0]; simp), hwP00]
        exact seqGatherParity_mulVec_zero 5 (wTail5 wOut) (wOut ⟨1, by omega⟩) _ _ fun t ↦
          (Function.update_of_ne (wTail5_ne_wOut1 hInj t) 1 _).trans
            ((Function.update_of_ne (wTail5_ne_wOut32 hInj t) 1 δ).trans (hOut0 _))
      · by_cases hq90 : idxValD (wIdx3x32 wIdx) δ ≤ 90
        · have h32_0 : Function.update δ (wOut3x32 wOut ⟨idxValD (wIdx3x32 wIdx) δ, hq96⟩) 1
              (wOut ⟨32, by omega⟩) = 0 := by
            unfold wOut3x32; exact (Function.update_of_ne
              (wOut192_ne_of_val_ne hInj (by dsimp; omega)) 1 δ).trans (hOut0 _)
          rw [show wOut3x32Hi wOut ⟨idxValD (wIdx3x32 wIdx) δ, hq96⟩ =
              wOut3x32 wOut ⟨idxValD (wIdx3x32 wIdx) δ, hq96⟩
              from ite_eq_right hq0, ket_CNOT_ctrl_zero hne32_1 h32_0,
            show δ_rHi187 wIdx wOut δ = δ by
                dsimp only [δ_rHi187];
                rw [ite_eq_right hq0, ite_eq_left hq90],
            show bStarHi90 wIdx δ = ⟨idxValD (wIdx3x32 wIdx) δ - 1,
                by omega⟩ from Fin.ext (ite_eq_left ⟨by omega, hq90⟩),
            show wPair90 wOut ⟨idxValD (wIdx3x32 wIdx) δ - 1, by omega⟩ ⟨0, by omega⟩ =
              wOut3x32 wOut ⟨idxValD (wIdx3x32 wIdx) δ, hq96⟩ from
              congrArg wOut (Fin.ext (by dsimp [wPair90, w91x2, wOut3x32]; omega))]
          exact seqGatherParity_mulVec_zero 5 (wTail5 wOut) (wOut ⟨1, by omega⟩) _ _ fun t ↦
            (Function.update_of_ne (wOut3x32_ne_wTail5_of_lt91 hInj (by omega) t).symm 1 δ).trans
                (hOut0 _)
        · let tStar : Fin 5 := ⟨idxValD (wIdx3x32 wIdx) δ - 91, by omega⟩
          rw [show wOut3x32Hi wOut ⟨idxValD (wIdx3x32 wIdx) δ, hq96⟩ =
              wTail5 wOut tStar from (ite_eq_right hq0).trans
              (congrArg wOut (Fin.ext (by dsimp [wOut3x32, wTail5, tStar]; omega))),
            ket_CNOT_ctrl_zero hne32_1 ((Function.update_of_ne (wTail5_ne_wOut32 hInj tStar).symm 1
                δ).trans (hOut0 _)),
            show δ_rHi187 wIdx wOut δ = Function.update δ (wTail5 wOut tStar) 1 by
              dsimp only [δ_rHi187]; rw [ite_eq_right hq0, ite_eq_right hq90]
              exact congrArg (fun u ↦ Function.update δ (wTail5 wOut u) 1)
                  (Fin.ext (by dsimp [tStar]; omega)),
            show bStarHi90 wIdx δ = ⟨0, by omega⟩ from Fin.ext (ite_eq_right (by omega)), hwP00]
          exact seqGatherParity_wTail5_set hInj hOut0 ⟨1, by omega⟩ _ tStar
    have hPostKet {δ : BitAssignment n} (hOut0 : ∀ j : Fin 192, δ (wOut j) = 0)
        (hLt : idxValD wIdx δ < 187)
        (hZero : δ wHas = 0 → idxValD wIdx δ = 0) (hOne : δ wHas = 1 → idxValD wIdx δ ≠ 0) :
        let δr := δ_rHi187 wIdx wOut δ
        (cPostHi187 wHas wOut hd.has_ne_out hInj).eval.1.mulVec (ket (Function.update δr
          (wPair90 wOut (bStarHi90 wIdx δr) ⟨idxValPrefix (uBit5 wIdx) δr 1 le_rfl,
            idxValPrefix_lt_two_pow _ δr 1 le_rfl⟩) 1)) =
        (uOneHotToggle wHas wIdx wOut hd.has_ne_out hd.idx_ne_out).1.mulVec (ket δ) := by
      intro δr
      rw [bStarHi90_δ_rHi187 hd.idx_ne_out δ, show (⟨idxValPrefix (uBit5 wIdx) δr 1 le_rfl,
            idxValPrefix_lt_two_pow _ δr 1 le_rfl⟩ : Fin (2 ^ 1)) =
          ⟨idxValPrefix (uBit5 wIdx) δ 1 le_rfl,
              idxValPrefix_lt_two_pow _ δ 1 le_rfl⟩ from Fin.ext (by
            dsimp only [δr, δ_rHi187]; split_ifs <;> first
              | rfl
              | exact idxValPrefix_congr _ _ _ (fun _ ↦
                    Function.update_of_ne (hd.idx_ne_out _ _) 1 δ) 1 le_rfl)]
      set b5 : Fin (2 ^ 1) :=
          ⟨idxValPrefix (uBit5 wIdx) δ 1 le_rfl, idxValPrefix_lt_two_pow _ δ 1 le_rfl⟩
      simp only [cPostHi187, eval_seq_mulVec, uOneHotToggle_mulVec_ket]
      dsimp only [toggleOneHotBits]; rw [dite_eq_left (Nat.lt_trans hLt (by omega))]
      have hp := idxValD_perm370 wIdx δ
      by_cases hq0 : idxValD (wIdx3x32 wIdx) δ = 0
      · rw [show δr = Function.update δ (wOut ⟨32, by omega⟩) 1 from ite_eq_left hq0,
          show bStarHi90 wIdx δ =
              ⟨0, by omega⟩ from Fin.ext (by dsimp only [bStarHi90]; rw [hq0]; simp)]
        rcases DynCircExt.bit_cases (δ wHas) with hh0 | hh1
        · let η1 :=
              Function.update (Function.update δ (wOut ⟨32, by omega⟩) 1) (wOut ⟨1, by omega⟩) 1
          rw [show b5 =
              ⟨0,
              by omega⟩ from Fin.ext (by dsimp only [b5]; rw [hZero hh0, hq0] at hp; omega),
              hwP00,
            ket_wZeroGate_of_zero_hi (hd.has_ne_out _)
              (by rw [Function.update_of_ne (hd.has_ne_out _),
                    Function.update_of_ne (hd.has_ne_out _), hh0]),
            show Function.update η1 (wOut ⟨32, by omega⟩) (η1 (wOut ⟨32, by omega⟩) + 1) =
                Function.update δ (wOut ⟨1, by omega⟩) 1 by
              dsimp only [η1]; rw [Function.update_comm hne32_1, Function.update_self,
                  CharTwo.add_self_eq_zero,
                Function.update_idem,
                    update_eq_self_of_zero ((Function.update_of_ne hne32_1 1 δ).trans (hOut0 _))],
            ket_CNOT_ctrl_zero hne32_33 ((Function.update_of_ne hne32_1 1 δ).trans (hOut0 _)),
            seqGatherParity_mulVec_zero 5 (wTail5 wOut) (wOut ⟨1, by omega⟩) _ _
              (fun t ↦ (Function.update_of_ne (wTail5_ne_wOut1 hInj t) 1 δ).trans (hOut0 _)),
            ket_wZeroGate_of_zero_hi (hd.has_ne_out _)
                ((Function.update_of_ne (hd.has_ne_out _) 1 δ).trans hh0),
            Function.update_self, CharTwo.add_self_eq_zero, Function.update_idem,
            update_eq_self_of_zero (hOut0 _), hh0, hOut0 _, zero_add,
                update_eq_self_of_zero (hOut0 _)]
        · have hb5_1 : b5 = ⟨1, by omega⟩ := Fin.ext ((fun hIdxNz hb5Lt ↦ by
            dsimp only [b5] at hb5Lt ⊢; rw [hq0] at hp; omega) (hOne hh1) b5.isLt)
          rw [hb5_1, show wPair90 wOut ⟨0, by omega⟩ ⟨1, by omega⟩ = wOut ⟨33, by omega⟩ from
              congrArg wOut (Fin.ext (by dsimp [wPair90, w91x2])),
            ket_wZeroGate_of_one_hi (hd.has_ne_out _)
              (by rw [Function.update_of_ne (hd.has_ne_out _),
                    Function.update_of_ne (hd.has_ne_out _), hh1]),
            ket_CNOT, Function.update_self, Function.update_of_ne hne32_33, Function.update_self,
            CharTwo.add_self_eq_zero, Function.update_idem,
            update_eq_self_of_zero ((Function.update_of_ne hne32_33.symm 1 δ).trans (hOut0 _)),
            seqGatherParity_mulVec_zero 5 (wTail5 wOut) (wOut ⟨1, by omega⟩) _ _
              (fun t ↦ (Function.update_of_ne (wTail5_ne_wOut32 hInj t) 1 δ).trans (hOut0 _)),
            ket_wZeroGate_of_one_hi (hd.has_ne_out _)
                ((Function.update_of_ne (hd.has_ne_out _) 1 δ).trans hh1),
            hOut0 _, hh1, zero_add]
          exact congrArg (fun j ↦ ket (Function.update δ (wOut j) 1))
              (Fin.ext (by
            dsimp [outIdx187];
            rw [hq0, show idxValPrefix (uBit5 wIdx) δ 1 le_rfl =
                1 from congrArg Fin.val hb5_1] at hp; omega))
      · have hh1 : δ wHas = 1 :=
          (DynCircExt.bit_cases (δ wHas)).elim (fun hh0 ↦ by rw [hZero hh0] at hp; omega) id
        rw [hOut0 _, hh1, zero_add]
        by_cases hq90 : idxValD (wIdx3x32 wIdx) δ ≤ 90
        · have hwP : wPair90 wOut (bStarHi90 wIdx δ) b5 = wOut (outIdx187 hLt) := by
            have hbS : bStarHi90 wIdx δ = ⟨idxValD (wIdx3x32 wIdx) δ - 1, by omega⟩ :=
                Fin.ext (ite_eq_left ⟨by omega, hq90⟩)
            rw [hbS];
                exact congrArg wOut (Fin.ext (by dsimp [wPair90, w91x2, b5, outIdx187]; omega))
          have hηHas : Function.update δ (wOut (outIdx187 hLt)) 1 wHas = 1 :=
            (Function.update_of_ne (hd.has_ne_out _) 1 δ).trans hh1
          have hNe32 : wPair90 wOut (bStarHi90 wIdx δ) b5 ≠ wOut ⟨32, by omega⟩ :=
            wOut192_ne_of_val_ne hInj ((fun _ _ ↦ by dsimp [wPair90, w91x2]; omega)
                (bStarHi90 wIdx δ).isLt b5.isLt)
          rw [show δr = δ by
              dsimp only [δr, δ_rHi187];
              rw [ite_eq_right hq0, ite_eq_left hq90], hwP,
            ket_wZeroGate_of_one_hi (hd.has_ne_out _) hηHas,
            ket_CNOT_ctrl_zero hne32_33 (by rw [← hwP, Function.update_of_ne hNe32.symm, hOut0 _]),
            seqGatherParity_mulVec_zero 5 (wTail5 wOut) (wOut ⟨1, by omega⟩) _ _ (fun t ↦ by
              rw [← hwP]; dsimp only [wPair90];
                  exact (Function.update_of_ne (w91x2_ne_wTail5 hInj
                ⟨(bStarHi90 wIdx δ).val + 1,
                    Nat.succ_lt_succ (bStarHi90 wIdx δ).isLt⟩ b5 t).symm 1 δ).trans (hOut0 _)),
            ket_wZeroGate_of_one_hi (hd.has_ne_out _) hηHas]
        · obtain ⟨hb5_0, hDecomp, _, _⟩ := inact91_decomp wIdx δ hLt (by unfold act91; omega)
          let tStar : Fin 5 := ⟨idxValD (wIdx3x32 wIdx) δ - 91, by omega⟩
          have hHasTail : wHas ≠ wTail5 wOut tStar := by unfold wTail5; exact hd.has_ne_out _
          rw [show δr = Function.update δ (wTail5 wOut tStar) 1 by
              dsimp only [δr, δ_rHi187]; rw [ite_eq_right hq0, ite_eq_right hq90]
              exact congrArg (fun u ↦ Function.update δ (wTail5 wOut u) 1)
                  (Fin.ext (by dsimp [tStar]; omega)),
            show bStarHi90 wIdx δ = ⟨0, by omega⟩ from Fin.ext (ite_eq_right (by omega)),
            show b5 = ⟨0, by omega⟩ from Fin.ext hb5_0, hwP00,
            ket_wZeroGate_of_one_hi (hd.has_ne_out _)
              (by rw [Function.update_of_ne (hd.has_ne_out _), Function.update_of_ne hHasTail,
                    hh1]),
            ket_CNOT_ctrl_zero hne32_33 (by
              rw [Function.update_of_ne hne32_1,
                  Function.update_of_ne (wTail5_ne_wOut32 hInj tStar).symm, hOut0 _]),
            seqGatherParity_wTail5_clr hInj hOut0 ⟨1, by omega⟩ _ tStar,
            ket_wZeroGate_of_one_hi (hd.has_ne_out _)
                ((Function.update_of_ne hHasTail 1 δ).trans hh1),
            ← show wOut (outIdx187 hLt) = wTail5 wOut tStar from
              by unfold wTail5; exact congrArg wOut (Fin.ext hDecomp)]
    have hComp : SubspaceStep (Var := Var) R_in
        ((uOneHotToggle wHas wIdx wOut hd.has_ne_out hd.idx_ne_out).1 * R_in)
        (wCompHi187_366 v wHas wIdx wOut qEnc) := by
      unfold wCompHi187_366; rw [dite_eq_left hdp]
      let R₁ : Operator (2 ^ n) := mkVecOp (fun δ ↦ ket (δ_rHi187 wIdx wOut δ)) * R_in
      refine SubspaceStep.seq (subspaceStep_congr_out (subspaceStep_of_circuit (Var := Var) R_in _)
          (hSuppIn _ _ fun δ ⟨hOut0, hq0, hLt, _, _⟩ ↦ by
            have hOHi := wOut3x32Hi_lift (P := fun w ↦ δ w = 0) hOut0
            rw [ket_sr, eval_seq_mulVec, root3.init_ket δ hOHi (idxValD_3x32_lt96 wIdx δ hLt),
              wSuperVec_bot_pub root3.bStarFn uLo5 w3 hw3 qEnc δ (fun _ _ ↦ hOHi _) hq0,
              wSuperOp, mkVecOp_mulVec_ket])) <|
        SubspaceStep.seq (subspaceStep_mul_right R_in (subspaceStep_wShiftLevels v root3.bStarFn
            uLo5 w3 qEnc hw3
            (w3Hi_ne_of_wOut_ne hd.out_ne_q)
            (fun d ↦
                by dsimp only [uLo5]; rw [uLo5_eq_wIdx]; exact hdp.2.2.2.1 ⟨d.val, by omega⟩)
            (fun d ↦ by
              dsimp only [uLo5]; rw [uLo5_eq_wIdx];
              exact ne_w3Hi_of_ne_wOut (hd.idx_ne_out ⟨d.val, by omega⟩)) 5 le_rfl)) <|
        SubspaceStep.seq (subspaceStep_congr_out (subspaceStep_of_circuit (Var := Var) _ _) ?_) <|
        SubspaceStep.seq (subspaceStep_mul_right R₁ (subspaceStep_wShiftLevels v (bStarHi90 wIdx)
            (uBit5 wIdx)
            (wPair90 wOut) qEnc hw90 (fun _ _ ↦ hd.out_ne_q _) (fun _ ↦ hdp.2.2.2.1 _)
            (fun _ _ _ ↦ hd.idx_ne_out _ _) 1 le_rfl))
          (subspaceStep_congr_out (subspaceStep_of_circuit (Var := Var) _ _) ?_)
      · dsimp only [R₁]; simp only [← Matrix.mul_assoc]
        refine hSuppIn _ _ fun δ ⟨hOut0, hq0, hLt, _, _⟩ ↦ ?_
        have hOHi := wOut3x32Hi_lift (P := fun w ↦ δ w = 0) hOut0
        rw [ket_sr, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, wSuperOp, mkVecOp_mulVec_ket,
          wSuperVec_top_pub root3.bStarFn uLo5 w3 qEnc δ (fun _ _ ↦ hOHi _) hq0, eval_seq_mulVec,
          mkVecOp_mulVec_ket, wSuperOp, mkVecOp_mulVec_ket, hw3Eq hLt, hPreKet hOut0 hLt,
          ← bStarHi90_δ_rHi187 hd.idx_ne_out δ, wSuperVec_bot_pub (bStarHi90 wIdx) (uBit5 wIdx)
              (wPair90 wOut)
            hw90 qEnc (δ_rHi187 wIdx wOut δ) (δ_rHi187_wPair90 hd.out_inj hOut0) (hqEnc hq0)]
      · dsimp only [R₁]; simp only [← Matrix.mul_assoc]
        refine hSuppIn _ _ fun δ ⟨hOut0, hq0, hLt, hZero, hOne⟩ ↦ ?_
        rw [ket_sr, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, mkVecOp_mulVec_ket, wSuperOp,
            mkVecOp_mulVec_ket,
          wSuperVec_top_pub (bStarHi90 wIdx) (uBit5 wIdx) (wPair90 wOut) qEnc (δ_rHi187 wIdx wOut δ)
            (δ_rHi187_wPair90 hd.out_inj hOut0) (hqEnc hq0)]
        exact hPostKet hOut0 hLt hZero hOne
    have hUncomp : SubspaceStep (Var := Var)
        ((uOneHotToggle wHas wIdx wOut ho.1 ho.2.1).1 *
            R_out) R_out (wUncompHi187_0 v wHas wIdx wOut) := by
      unfold wUncompHi187_0; rw [dite_eq_left ho]
      have mX (q : Wire n) (u : Fin (2 ^ n) → ℂ) :
          (Circuit.X q).eval.1.mulVec ((Circuit.X q).eval.1.mulVec u) = u := by
        rw [Matrix.mulVec_mulVec, show (Circuit.X q).eval.1 * (Circuit.X q).eval.1 =
            1 from matrix_ext_ket fun _ ↦ by
          rw [← Matrix.mulVec_mulVec, ket_X, ket_X, Function.update_idem, Function.update_self,
              add_assoc,
            CharTwo.add_self_eq_zero, add_zero, Function.update_eq_self, Matrix.one_mulVec],
                Matrix.one_mulVec]
      have mC (c t : Wire n) (h : c ≠ t) (u : Fin (2 ^ n) → ℂ) :
          (Circuit.CNOT c t h).eval.1.mulVec ((Circuit.CNOT c t h).eval.1.mulVec u) = u := by
        rw [Matrix.mulVec_mulVec, show (Circuit.CNOT c t h).eval.1 * (Circuit.CNOT c t h).eval.1 =
            1 from
          matrix_ext_ket fun _ ↦ by
            rw [← Matrix.mulVec_mulVec, ket_CNOT, ket_CNOT, Function.update_idem,
            Function.update_self, Function.update_of_ne h, add_assoc, CharTwo.add_self_eq_zero,
                                      add_zero,
            Function.update_eq_self, Matrix.one_mulVec], Matrix.one_mulVec]
      let Ptrue : BitAssignment n → Prop := fun _ ↦ True
      let : DecidablePred Ptrue := fun _ ↦ isTrue trivial
      let Pclean := ValidWRouterCleanHi187 wHas wIdx wOut
      let M_tail : Operator (2 ^ n) := mkVecOp (fun δ ↦ ket (δ_rHi187 wIdx wOut δ)) * R_out
      let idOnClean : Operator (2 ^ n) := mkVecOp fun δ ↦
          if Pclean δ ∧ ∀ b p, δ (w3 b p) = 0 then ket δ else 0
      refine SubspaceStep.seq (subspaceStep_congr_out (subspaceStep_of_circuit (Var :=
          Var) _ _) ?_) <|
        SubspaceStep.seq (subspaceStep_mul_right M_tail (subspaceStep_wUncompTreeDyn_opt v Ptrue
            Ptrue
            (bStarHi90 wIdx) (uBit5 wIdx) (wPair90 wOut) hw90 (fun _ _ _ ↦ ho.2.1 _ _)
            (by simpa only [Circuit.eval_identity, Submonoid.coe_one, Matrix.one_mul] using
              subspaceStep_of_circuit (Var := Var) _ (.identity : Circuit n)) 1 le_rfl)) <|
        SubspaceStep.seq (subspaceStep_congr_out (subspaceStep_of_circuit (Var := Var) _ _) ?_) <|
        subspaceStep_congr_out (subspaceStep_mul_right R_out (subspaceStep_wUncompTreeDyn_opt v
            Pclean Ptrue
            root3.bStarFn uLo5 w3 hw3
            (fun d ↦ by
              dsimp only [uLo5]; rw [uLo5_eq_wIdx];
              exact ne_w3Hi_of_ne_wOut (ho.2.1 ⟨d.val, by omega⟩))
            (subspaceStep_congr_out (subspaceStep_of_circuit (Var := Var) _ root3.cRootUninit)
              (matrix_ext_ket fun δ ↦ by
                simp only [← Matrix.mulVec_mulVec, oneHotOptPreOp, idOnClean, mkVecOp_mulVec_ket,
                    oneHotOptPreVec]
                by_cases hV : Pclean δ ∧ ∀ b p, δ (w3 b p) = 0
                · rw [ite_eq_left hV, ite_eq_left trivial, ite_eq_left hV,
                      show (⟨idxValPrefix uLo5 δ 0 (Nat.zero_le 5), _⟩ :
                      Fin (2 ^ 5)) = ⟨0, by omega⟩ from Fin.ext rfl,
                    ← root3.init_ket δ (wOut3x32Hi_lift (P := fun w ↦ δ w = 0) hV.1.1)
                      (idxValD_3x32_lt96 wIdx δ hV.1.2.1), root3.uninit_init]
                · rw [ite_eq_right hV, ite_eq_right hV, Matrix.mulVec_zero])) 5 le_rfl))
          ((hSuppOut idOnClean 1 fun δ hP ↦ by
              rw [ket_sr]; simp only [idOnClean, mkVecOp_mulVec_ket, Matrix.one_mulVec]
              exact ite_eq_left ⟨hP, fun _ _ ↦ wOut3x32Hi_lift (P := fun w ↦ δ w =
                  0) hP.1 _⟩).trans (Matrix.one_mul R_out))
      · dsimp only [M_tail]; simp only [← Matrix.mul_assoc]
        refine hSuppOut _ _ fun δ ⟨hOut0, hLt, hZero, hOne⟩ ↦ ?_
        rw [ket_sr, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, mkVecOp_mulVec_ket,
            oneHotOptPreOp,
          mkVecOp_mulVec_ket, oneHotOptPreVec, ite_eq_left ⟨trivial, δ_rHi187_wPair90 ho.2.2 hOut0⟩,
              ite_eq_left trivial,
          ← hPostKet hOut0 hLt hZero hOne]
        simp only [cPostHi187Inv, cPostHi187, wUnzeroGate, wZeroGate, eval_seq_mulVec, mC, mX,
          mulVec_seqGatherParity_invol]
      · dsimp only [M_tail]; simp only [← Matrix.mul_assoc]
        refine hSuppOut _ _ fun δ hP ↦ ?_
        have ⟨hOut0, hLt, _, _⟩ := hP
        have hOHi := wOut3x32Hi_lift (P := fun w ↦ δ w = 0) hP.1
        rw [ket_sr, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, mkVecOp_mulVec_ket,
            oneHotOptPreOp,
          mkVecOp_mulVec_ket, oneHotOptPreVec, ite_eq_left ⟨trivial, δ_rHi187_wPair90 ho.2.2 hOut0⟩,
              ite_eq_left trivial,
          oneHotOptPreOp, mkVecOp_mulVec_ket, oneHotOptPreVec, ite_eq_left ⟨hP, fun _ _ ↦ hOHi _⟩,
              ite_eq_left trivial,
          show (⟨idxValPrefix (uBit5 wIdx) (δ_rHi187 wIdx wOut δ) 0 (Nat.zero_le 1),
              _⟩ : Fin (2 ^ 1)) =
            ⟨0, by omega⟩ from Fin.ext rfl, bStarHi90_δ_rHi187 ho.2.1 δ, ← hPreKet hOut0 hLt,
                hw3Eq hLt]
        simp only [cPreHi187Inv, cPreHi187, eval_seq_mulVec, mulVec_seqGatherParity_invol, mC]
    exact hComp.seq (hMid.seq hUncomp)
end QuantumComputation.Specs.PhotochemistrySolution.AlwaysLo25860Opt
end

/-!
## Section 3A: `pUnloadLoEAlways1WState_368` (`368 T`, `-2 T/step` on Stage-5 `Lo_E`)
-/

namespace QuantumComputation.Specs.PhotochemistrySolution.Stage2AlwaysLo

noncomputable section
open Operator QProg Matrix Circuit Qubit HermitianMat PhotochemistrySolution.KetSupport
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
open PhotochemistrySolution.XMeasUnld PhotochemistrySolution.SplitRouter47_187
  PhotochemistrySolution.PotSelectWiring
open PhotochemistrySolution.SortedRouterSpec PhotochemistrySolution.PortBDualBellUnld
  PhotochemistrySolution.PortBStage5Merged
open PhotochemistrySolution.WStateRouterPrim PhotochemistrySolution.WStateStage5Unload
  PhotochemistrySolution.WState25PortOpt
open PrimitiveGate hiding x y z h s t cnot swap toffoli
open _root_.DynamicCircuit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt hiding ket matrix_ext_ket
  qAssign_obs_map_val ket_projector_zero ket_projector_one ket_X ket_CNOT ket_TOFF eval_seq_mulVec
  bit_cases localIdx
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB hiding writeReg
  writeReg_apply_of_not_mem ket ket_X ket_CNOT ket_TOFF matrix_ext_ket bitSign eval_seq_mulVec
  localIdx
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynQromUncompA (fwdCirc)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SplitBellVecCleanStep
    (specBellEntangleVecCirc specFanoutCopyVecCirc bellZHalfVecDyn bellXHalfVecDyn)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SplitBellVecCleanStep
    (subspaceStep_bellZHalfVec count_bellZHalfVecDyn_t count_bellZHalfVecDyn_toff)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SplitBellVecCleanStep
    (count_bellXHalfVecDyn_t count_bellXHalfVecDyn_toff)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SplitRouterSeqBell26k hiding ket
  matrix_ext_ket
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Stage2ZeroGated (zg187_hM0)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.AlwaysLo25860Opt (wWrapLo187_368
    count_wWrapLo187_368 dynWires_wWrapLo187_368 subspaceStep_wWrapLo187_368)
open scoped ComplexOrder MatrixOrder Circuit.Notation
/-- Step 3 `368-T` (`0 .TOFF`) W-state `Lo_E` `Always1` single-port Bell unloader. -/
def pUnloadLoEAlways1WState_368 {Var : Type} {n : ℕ} (v : Var) (rE : RouterReg 187 8 n)
    (pad : Fin (192 - 187) → Wire n) (qEnc : Wire n) : DynamicCircuit Var n :=
  let hc := hne_unload_core rE
  wWrapLo187_368 v (rHas1 rE) (rIdx1 rE) (padWires (rCtrlLo rE) pad) qEnc
    (.seq (.circuit (cFlipLo0 zg187_hM0 rE))
      (.seq
        (.seq
          (bellZHalfVecDyn v 187 24 (rBufLo rE) (rHA rE) (rCtrlLo rE)
            (fun k q ↦ pSys (planeOfRouter rE k) q) hc.2.1 hc.2.2.2)
          (bellXHalfVecDyn v 187 24 (rBufLo rE) (rCtrlLo rE)
            (fun k q ↦ pSys (planeOfRouter rE k) q) hc.2.2.2))
        (.circuit (cFlipLo0 zg187_hM0 rE))))

theorem count_pUnloadLoEAlways1WState_368 {Var : Type} {n : ℕ} (v : Var) (rE : RouterReg 187 8 n)
    (pad : Fin (192 - 187) → Wire n)
    (qEnc : Wire n) : (pUnloadLoEAlways1WState_368 v rE pad qEnc).count .T = 368 ∧
    (pUnloadLoEAlways1WState_368 v rE pad qEnc).count .TOFF = 0 := by
  unfold pUnloadLoEAlways1WState_368;
  obtain ⟨hT, hF⟩ :=
      count_wWrapLo187_368 v (rHas1 rE) (rIdx1 rE) (padWires (rCtrlLo rE) pad) qEnc _; rw [hT,
      hF]; simp [DynamicCircuit.count, count_cFlipLo0_T, count_cFlipLo0_TOFF,
      count_bellZHalfVecDyn_t, count_bellZHalfVecDyn_toff, count_bellXHalfVecDyn_t,
      count_bellXHalfVecDyn_toff]
attribute [local irreducible] systemQubits_frozen portSwapVecCirc specFanoutCopyVecCirc
    specBellEntangleVecCirc bellZHalfVecDyn
attribute [local irreducible] bellXHalfVecDyn
attribute [local semireducible] DynQromUncompA.fwdCirc ComputeProg.fwdBits


theorem subspaceStep_pUnloadLoEAlways1WState_368
    {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    (v : Var) (rE : RouterReg 187 8 n) (pad : Fin (192 - 187) → Wire n) (qEnc : Wire n)
    (hd : WRouterDisj (rHas1 rE) (rIdx1 rE) (padWires (rCtrlLo rE) pad) qEnc)
    (hPadDisj : ∀ i, (∀ b, pad i ≠ rBufLo rE b ∧ pad i ≠ rHA rE b) ∧ ∀ q b, pad i ≠ rSys rE q b)
    (hQDisj : (∀ b, qEnc ≠ rBufLo rE b ∧ qEnc ≠ rHA rE b) ∧ ∀ q b, qEnc ≠ rSys rE q b)
    (X : Operator (2 ^ n))
    (hSuppX : SupportedOn (fun δ ↦
      (∀ q : Fin 187, δ (rCtrlLo rE q) = 0) ∧
      (∀ i, δ (pad i) = 0) ∧
      δ qEnc = 0 ∧
      UnloadLoPred rE δ ∧
      (∀ k : Fin 24, δ (rBufLo rE k) = 0) ∧
      (∀ k : Fin 24, δ (rHA rE k) = 0)) X) :
    SubspaceStep (Var := Var) (uLoEAlways1Conj rE * X) X
      (pUnloadLoEAlways1WState_368 v rE pad qEnc) := by
  let rs := planeOfRouter rE
  let pDec := pDecLoESorted rE
  let F := (fwdCirc pDec).eval
  let F_fl := (cFlipLo0 zg187_hM0 rE).eval
  let hBC := hne_rBufLo_ctrlLo rE
  let hBT : ∀ k q, rBufLo rE k ≠ pSys (rs k) q := fun k q ↦ (hne_fixed_router_sys rE k k q).1
  let hHC := hne_rHA_ctrlLo rE
  let hHT : ∀ k q, rHA rE k ≠ pSys (rs k) q := fun k q ↦ (hne_fixed_router_sys rE k k q).2.2.1
  let hCT : ∀ k q, rCtrlLo rE q ≠ pSys (rs k) q := fun k q ↦ hne_rCtrlLo_pSys rE k q q
  let S_p :=
      (portSwapVecCirc 187 24 (rBufLo rE) (rCtrlLo rE) (fun k q ↦ pSys (rs k) q) hBC hBT hCT).eval.1
  let E_p :=
      (specBellEntangleVecCirc 187 24 (rHA rE) (rCtrlLo rE)
      (fun k q ↦ pSys (rs k) q) hHC hHT hCT).eval.1
  have hSuppIn : SupportedOn (fun δ ↦ (∀ q : Fin 187, δ (rCtrlLo rE q) = 0) ∧ (∀ i, δ (pad i) = 0) ∧
      δ qEnc = 0 ∧ UnloadLoPred rE δ)
      (uLoEAlways1Conj rE * X) :=
    supportedOn_preserves_uLoEAlways1Conj rE
      (fun {u} hu α val ⟨hc0, hp0, hq0, hPLo⟩ ↦ by
        have hDisj {w} (h1 : ∀ b, w ≠ rBufLo rE b ∧ w ≠ rHA rE b) (h2 : ∀ q' b, w ≠ rSys rE q' b) :
            w ≠ u :=
          hu.elim (fun ⟨b, hb⟩ ↦ hb.elim (· ▸ (h1 b).1) (· ▸ (h1 b).2)) fun ⟨q', b, e⟩ ↦ e ▸ h2 q' b
        have hi1 (d : Fin 8) : Function.update α u val (rIdx1 rE d) = α (rIdx1 rE d) :=
          Function.update_of_ne (by
            rcases hu with ⟨b, rfl | rfl⟩ | ⟨_, b, rfl⟩ <;>
              exact rr_ne rE ((fun _ _ ↦ by dsimp [routerWidth]; omega) d.isLt b.isLt)) _ _
        exact ⟨fun q ↦ (Function.update_of_ne (by
            rcases hu with ⟨b, rfl | rfl⟩ | ⟨_, b, rfl⟩ <;>
              exact rr_ne rE ((fun _ _ ↦
                  by unfold basePub; dsimp; omega) q.isLt b.isLt)) _ _).trans (hc0 q),
          fun i ↦ (Function.update_of_ne (hDisj (hPadDisj i).1 (hPadDisj i).2) _ _).trans (hp0 i),
          (Function.update_of_ne (hDisj hQDisj.1 hQDisj.2) _ _).trans hq0,
          (SplitRouter47_187.idxValD_congr hi1).trans_lt hPLo.1,
          fun hz ↦ (SplitRouter47_187.idxValD_congr hi1).trans (hPLo.2 ((Function.update_of_ne
            (show rHas1 rE ≠ u by rcases hu with ⟨b, rfl | rfl⟩ | ⟨q', b, rfl⟩ <;> first
              | exact rr_ne rE ((fun _ ↦ by
                  dsimp [routerWidth]; omega) b.isLt)) val α).symm.trans hz))⟩)
      (fun A B hAB ↦ hSuppX A B fun δ ⟨hc0, hp0, hq0, hPLo, _, _⟩ ↦ hAB δ ⟨hc0, hPLo, hc0, hp0, hq0,
          hPLo⟩)
  have hEqOut := uOneHotToggle_eq_fwdCirc_pDecLoE rE pad qEnc hd X fun _ _ h ↦
      hSuppX _ _ fun δ ⟨a, b, _, c, _, _⟩ ↦ h δ ⟨a, b, c⟩
  have hEqIn : (uOneHotToggle (rHas1 rE) (rIdx1 rE)
      (padWires (rCtrlLo rE) pad) hd.has_ne_out hd.idx_ne_out).1 * (uLoEAlways1Conj rE * X) =
      F_fl.1 * (E_p * (S_p * (F_fl.1 * (F.1 * X)))) := by
    rw [uOneHotToggle_eq_fwdCirc_pDecLoE rE pad qEnc hd (uLoEAlways1Conj rE * X)
        (fun A B hAB ↦ hSuppIn A B fun δ ⟨hc0, hp0, _, hPLo⟩ ↦ hAB δ ⟨hc0, hp0, hPLo⟩)]
    dsimp only [uLoEAlways1Conj, uDecPortAlways1Conj, F, F_fl, pDec, E_p, S_p, rs, hBC, hBT, hHC,
        hHT, hCT]
    rw [← Matrix.mul_assoc F.1, ← Matrix.mul_assoc F.1, ← Submonoid.coe_mul, mul_inv_cancel F,
        Submonoid.coe_one, Matrix.one_mul]
    simp only [Matrix.mul_assoc]
  have hSuppFlFX : SupportedOn (fun γ' ↦ AtMostOneCtrl (rCtrlLo rE) γ' ∧
      (∀ k : Fin 24, γ' (rBufLo rE k) = 0) ∧ (∀ k : Fin 24, γ' (rHA rE k) = 0))
      (F_fl.1 * (F.1 * X)) := fun A B hAB ↦ by
    simp only [← Matrix.mul_assoc]
    refine hSuppX (A * F_fl.1 * F.1) (B * F_fl.1 * F.1) fun δ ⟨hc0, _, _, hPLo, hB0, hH0⟩ ↦ ?_
    simp only [← Matrix.mulVec_mulVec]
    rw [ket_sr_eq_xm, fwdCirc_ket pDec δ, cFlipLo0_mulVec_ket zg187_hM0 rE, ← ket_sr_eq_xm]
    obtain ⟨_, hOth, hAtMost⟩ := flipLo0Bits_pDecLo_sorted zg187_hM0 (by omega) sorted187_hPow rE
      (fun d q ↦
          rr_ne rE ((fun _ _ ↦ by unfold basePub; dsimp; omega) d.isLt q.isLt)) δ hc0 hPLo
    exact hAB _ ⟨hAtMost, fun k ↦ (hOth _ (hBC k)).trans (hB0 k), fun k ↦
        (hOth _ (hHC k)).trans (hH0 k)⟩
  have hBH_all : ∀ k₁ k₂ : Fin 24, rBufLo rE k₁ ≠ rHA rE k₂ := fun k₁ k₂ ↦
      rr_ne rE ((fun _ _ ↦ by dsimp; omega) k₁.isLt k₂.isLt)
  have hSuppSP : SupportedOn (fun α ↦ ∀ k : Fin 24, α (rHA rE k) = 0) (S_p * (F_fl.1 * (F.1 * X)))
      := fun A B hAB ↦ by
    rw [← Matrix.mul_assoc A, ← Matrix.mul_assoc B]
    refine hSuppFlFX (A * S_p) (B * S_p) fun γ' ⟨_, _, hH0⟩ ↦ ?_
    obtain ⟨ζ, hζ, hEqζ⟩ :=
        portSwapVecCirc_ket_preserve 187 24 (rBufLo rE) (rCtrlLo rE)
        (fun k q ↦ pSys (rs k) q) hBC hBT hCT γ'
    simp only [← Matrix.mulVec_mulVec]; rw [ket_sr_eq_xm, hζ, ← ket_sr_eq_xm]
    exact hAB ζ fun k ↦
        (hEqζ (rHA rE k) (fun j ↦ (hBH_all j k).symm)
        (fun j q ↦ (hne_fixed_router_sys rE k j q).2.2.1)).trans (hH0 k)
  have sZ :=
      subspaceStep_bellZHalfVec v 187 24 (rBufLo rE) (rHA rE) (rCtrlLo rE)
      (fun k q ↦ pSys (rs k) q) hBH_all
    (fun k₁ k₂ hne ↦
        rr_ne rE ((fun _ _ _ ↦ by dsimp; omega) k₁.isLt k₂.isLt (Fin.val_ne_of_ne hne)))
    hHC (fun k₁ k₂ q ↦ (hne_fixed_router_sys rE k₁ k₂ q).2.2.1) hBC (fun k₁ k₂ q ↦
        (hne_fixed_router_sys rE k₁ k₂ q).1) (hne_rCtrlLo_pSys rE)
    (fun _ _ hne p q e ↦ planeModDisj rE hne _ (Or.inr (Or.inr (Or.inr (Or.inr ⟨p, rfl⟩))))
        (Or.inr (Or.inr (Or.inr (Or.inr ⟨q, e⟩)))))
    (S_p * (F_fl.1 * (F.1 * X)))
    (fun k ↦ (hSuppSP _ 1 fun _ hH0 ↦
        by rw [ket_projector_zero, itePos (hH0 k), Matrix.one_mulVec]).trans (Matrix.one_mul _))
  have sX := subspaceStep_bellXHalfVec_portSwap v rE (rBufLo rE) (rCtrlLo rE)
    (fun k₁ k₂ hne ↦
        rr_ne rE ((fun _ _ _ ↦ by dsimp; omega) k₁.isLt k₂.isLt (Fin.val_ne_of_ne hne)))
    (fun k ↦ Or.inl (planeOfRouter_bufLo rE k).symm)
    (fun k q hM ↦
        by rw [← planeOfRouter_ctrlLo rE k] at hM; rcases hM with e | e | e | e | ⟨_, e⟩ <;>
             exact pr_ne (rs k) (by dsimp; omega) e)
    hBC (fun k₁ k₂ q ↦ (hne_fixed_router_sys rE k₁ k₂ q).1) (hne_rCtrlLo_pSys rE)
        (F_fl.1 * (F.1 * X))
    (fun A B hAB ↦ hSuppFlFX A B fun _ ⟨h1, hB0, _⟩ ↦ hAB _ ⟨h1, hB0⟩)
  have sFl (M : Operator (2 ^ n)) : SubspaceStep (Var := Var)
      (F_fl.1 * M) M (.circuit (cFlipLo0 zg187_hM0 rE)) :=
    subspaceStep_congr_out (subspaceStep_of_circuit (Var := Var) (F_fl.1 * M)
        (cFlipLo0 zg187_hM0 rE))
      (by dsimp only [F_fl]; rw [← Matrix.mul_assoc, cFlipLo0_eval_sq_eq_one zg187_hM0 rE,
            Matrix.one_mul])
  exact subspaceStep_wWrapLo187_368 v _ _ _ _ hd _ (uLoEAlways1Conj rE * X) X
    (fun A B hAB ↦ hSuppIn A B fun δ ⟨hc0, hp0, hq0, hLt, hZG⟩ ↦
        hAB δ ⟨padWires_zero_of_zero hc0 hp0, hq0, hLt, hZG⟩)
    (fun A B hAB ↦ hSuppX A B fun δ ⟨hc0, hp0, _, ⟨hLt, hZG⟩, _, _⟩ ↦
        hAB δ ⟨padWires_zero_of_zero hc0 hp0, hLt, hZG⟩)
    (subspaceStep_congr_in hEqIn (subspaceStep_congr_out ((sFl _).seq ((sZ.seq sX).seq (sFl _)))
        hEqOut.symm))
end

end QuantumComputation.Specs.PhotochemistrySolution.Stage2AlwaysLo


noncomputable section
-- Dual-Axis Triple-GLFA (`GLFA@c4 + GLFA@c6 + GLFA@c8` on Axes 0 & 1) + Axis-2 `p012` Cubic
-- Collapse:
-- * Forward `dist18DualGlfa142Pkg : Dist18XorPkg` (`142` TempANDs = `568 T` , `kDist = 146` , `194`
-- wires, `0 .TOFF` )
-- * Reverse `dist18DualGlfaUnld125Pkg : Dist18UnldPkg` (`125` TempANDs = `500 T` ,
-- `kDistUnld = 129` , `177` wires, `96` CZs, `0 .TOFF` )
-- * Combined `Dist18` = `1,068 T/step` (`568-T` compute + `500-T` uncompute).

namespace QuantumComputation.Specs.PhotochemistrySolution.Dist18DualGlfaOpt

open Operator QProg Matrix Circuit Qubit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
open PhotochemistrySolution.SelectStructuredCB PhotochemistrySolution.SelectFastFlags
  PhotochemistrySolution.Word73PotPool
open PhotochemistrySolution.Stage4Cluster22Xnor PhotochemistrySolution.Dist18QuadUnld
open _root_.DynamicCircuit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt hiding ket matrix_ext_ket
  qAssign_obs_map_val ket_projector_zero ket_projector_one ket_X ket_CNOT ket_TOFF bit_cases
  localIdx writeReg writeReg_apply_reg writeReg_apply_of_not_mem
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB hiding writeReg writeReg_apply_reg
  writeReg_apply_of_not_mem ket ket_X ket_CNOT ket_TOFF matrix_ext_ket bitSign localIdx


-- ============================================================================
-- Part 0: Shared NTree5 Bit-Parallel Evaluator & Pool Identity (`initDualGlfa135`)
-- ============================================================================

inductive NTree5 where
  | leaf (v : ℕ)
  | node (l r : NTree5)
  deriving DecidableEq

def zeroNT5 : ℕ → NTree5
  | 0 => .leaf 0
  | d + 1 => .node (zeroNT5 d) (zeroNT5 d)

def wfNT5 : ℕ → NTree5 → Prop
  | 0, .leaf _ => True
  | 0, .node _ _ => False
  | _ + 1, .leaf _ => False
  | d + 1, .node l r => wfNT5 d l ∧ wfNT5 d r

namespace NT5Lemmas
theorem zeroNT5_wf : ∀ d, wfNT5 d (zeroNT5 d) :=
  Nat.rec (motive := fun d ↦ wfNT5 d (zeroNT5 d)) trivial fun _ ih ↦ ⟨ih, ih⟩
end NT5Lemmas
open NT5Lemmas

def getNT5 : ℕ → NTree5 → ℕ → ℕ
  | 0, .leaf v, _ => v
  | 0, .node _ _, _ => 0
  | _ + 1, .leaf _, _ => 0
  | d + 1, .node l r, i => cond (i.testBit d) (getNT5 d r i) (getNT5 d l i)

def mkLeafStrict {α : Type} (v : ℕ) (k : NTree5 → α) : α :=
    cond (v == 0) (k (.leaf 0)) (k (.leaf v))
theorem NT5Lemmas.mkLeafStrict_eq {α : Type} (v : ℕ) (k : NTree5 → α) : mkLeafStrict v k =
    k (.leaf v) := by
  cases hv : (v == 0) <;> simp_all [mkLeafStrict]

def setNT5 : ℕ → NTree5 → ℕ → ℕ → NTree5
  | 0, .leaf _, _, v => .leaf v
  | 0, .node l r, _, _ => .node l r
  | _ + 1, .leaf v, _, _ => .leaf v
  | d + 1, .node l r, i, v =>
      cond (i.testBit d) (.node l (setNT5 d r i v)) (.node (setNT5 d l i v) r)

def setNT5CPS {α : Type} : ℕ → NTree5 → ℕ → ℕ → (NTree5 → α) → α
  | 0, .leaf _, _, v, k => mkLeafStrict v k
  | 0, .node l r, _, _, k => k (.node l r)
  | _ + 1, .leaf v, _, _, k => k (.leaf v)
  | d + 1, .node l r, i, v, k =>
      cond (i.testBit d)
        (setNT5CPS d r i v fun r' ↦ k (.node l r'))
        (setNT5CPS d l i v fun l' ↦ k (.node l' r))

theorem NT5Lemmas.setNT5CPS_eq {α : Type} :
    ∀ (d : ℕ) (t : NTree5) (i v : ℕ) (k : NTree5 → α),
      setNT5CPS d t i v k = k (setNT5 d t i v)
  | 0, .leaf _, _, v, k => mkLeafStrict_eq v k
  | 0, .node _ _, _, _, _ => rfl
  | _ + 1, .leaf _, _, _, _ => rfl
  | d + 1, .node l r, i, v, k => by
      cases h : i.testBit d <;>
          simp only [setNT5CPS, setNT5, h, Bool.cond_true, Bool.cond_false] <;> first
        | exact setNT5CPS_eq d l i v _
        | exact setNT5CPS_eq d r i v _

theorem NT5Lemmas.setNT5_wf :
    ∀ (d : ℕ) (t : NTree5) (i v : ℕ), wfNT5 d t → wfNT5 d (setNT5 d t i v)
  | 0, .leaf _, _, _, _ => trivial
  | 0, .node _ _, _, _, h => False.elim h
  | _ + 1, .leaf _, _, _, h => False.elim h
  | d + 1, .node l r, i, v, ⟨hl, hr⟩ => by
      cases h : i.testBit d <;> simp only [setNT5, h, Bool.cond_true, Bool.cond_false] <;> first
        | exact ⟨setNT5_wf d l i v hl, hr⟩
        | exact ⟨hl, setNT5_wf d r i v hr⟩

def eqLowBits5 : ℕ → ℕ → ℕ → Bool
  | 0, _, _ => true
  | d + 1, i, j => (j.testBit d == i.testBit d) && eqLowBits5 d i j

theorem NT5Lemmas.getNT5_setNT5 :
    ∀ (d : ℕ) (t : NTree5), wfNT5 d t → ∀ (i j v : ℕ),
      getNT5 d (setNT5 d t i v) j =
        cond (eqLowBits5 d i j) v (getNT5 d t j)
  | 0, .leaf _, _, _, _, _ => rfl
  | 0, .node _ _, h, _, _, _ => False.elim h
  | _ + 1, .leaf _, h, _, _, _ => False.elim h
  | d + 1, .node l r, ⟨hl, hr⟩, i, j, v => by
      cases hi : i.testBit d <;> cases hj : j.testBit d <;>
          simp only [setNT5, cond, hi, getNT5, hj, eqLowBits5, BEq.rfl, Bool.true_and, beq_false,
            Bool.not_true, Bool.false_and, beq_true] <;>
        first | exact getNT5_setNT5 d l hl i j v | exact getNT5_setNT5 d r hr i j v

theorem NT5Lemmas.eqLowBits5_eq_beq {M : ℕ} (hM : M ≤ 32)
    (u w : Wire M) : eqLowBits5 5 u.val w.val = (w == u) := by
  have hchk : ((List.range 32).all fun i ↦ (List.range 32).all fun j ↦
      (eqLowBits5 5 i j == (j == i))) = true := by decide +kernel
  have hw :=
      beq_iff_eq.mp ((List.all_eq_true.mp ((List.all_eq_true.mp hchk) u.val (List.mem_range.mpr
      (by omega)))) w.val (List.mem_range.mpr (by omega)))
  exact hw.trans (by cases h1 : (w == u) <;> simp_all [Fin.ext_iff])

def bitsOfNT5 {M : ℕ} (t : NTree5) (m : ℕ) : BitAssignment M := fun u ↦
    cond ((getNT5 5 t u.val).testBit m) 1 0
theorem NT5Lemmas.zmod2_cond_xor (a b : Bool) : cond (Bool.xor a b) (1 : ZMod 2) 0 = cond a 1 0 +
    cond b 1 0 := by cases a <;> cases b <;> decide
theorem NT5Lemmas.zmod2_cond_and (a b : Bool) : cond (a && b) (1 : ZMod 2) 0 = cond a 1 0 *
    cond b 1 0 := by cases a <;> cases b <;> decide
theorem NT5Lemmas.zmod2_cond_ite (a : Bool) : (if a then (1 : ZMod 2) else 0) = cond a 1 0 := by
  cases a <;> rfl
theorem NT5Lemmas.zmod2_cond_val (a : Bool) : (cond a (1 : ZMod 2) 0).val = cond a 1 0 := by
  cases a <;> decide

def evalProgNT5 {M : ℕ} (ones : ℕ) : ComputeProg M → NTree5 → NTree5
  | .id, t => t
  | .x u, t => setNT5 5 t u.val ((getNT5 5 t u.val) ^^^ ones)
  | .cnot c tg _, t => setNT5 5 t tg.val ((getNT5 5 t tg.val) ^^^ (getNT5 5 t c.val))
  | .andGate c1 c2 a _ _ _, t =>
      setNT5 5 t a.val ((getNT5 5 t a.val) ^^^ ((getNT5 5 t c1.val) &&& (getNT5 5 t c2.val)))
  | .seq p q, t => evalProgNT5 ones q (evalProgNT5 ones p t)

theorem NT5Lemmas.evalProgNT5_wf {M : ℕ} (ones : ℕ) :
    ∀ (p : ComputeProg M) (t : NTree5), wfNT5 5 t → wfNT5 5 (evalProgNT5 ones p t)
  | .id, _, hwf => hwf
  | .x _, t, hwf => setNT5_wf 5 t _ _ hwf
  | .cnot _ _ _, t, hwf => setNT5_wf 5 t _ _ hwf
  | .andGate _ _ _ _ _ _, t, hwf => setNT5_wf 5 t _ _ hwf
  | .seq p q, t, hwf => evalProgNT5_wf ones q _ (evalProgNT5_wf ones p t hwf)

theorem NT5Lemmas.bitsOfNT5_set {M : ℕ} (hM : M ≤ 32) (t : NTree5) (hwf : wfNT5 5 t)
    (u : Wire M) (v m : ℕ) (z : ZMod 2) (hz : cond (v.testBit m) (1 : ZMod 2) 0 = z) :
    bitsOfNT5 (M := M) (setNT5 5 t u.val v) m = Function.update (bitsOfNT5 t m) u z :=
        funext fun w ↦ by
  dsimp only [bitsOfNT5]; rw [getNT5_setNT5 5 t hwf u.val w.val v, eqLowBits5_eq_beq hM u w]
  by_cases hwu : w = u
  · subst hwu; simpa [cond] using hz
  · simp [hwu, beq_eq_false_iff_ne.mpr hwu, cond, bitsOfNT5]

theorem NT5Lemmas.fwdBits_bitsOfNT5 {M : ℕ} (hM : M ≤ 32) (ones m : ℕ)
    (hones : ones.testBit m = true) :
    ∀ (p : ComputeProg M) (t : NTree5), wfNT5 5 t →
      p.fwdBits (bitsOfNT5 t m) = bitsOfNT5 (evalProgNT5 ones p t) m
  | .id, _, _ => rfl
  | .x u, t, hwf =>
    Eq.symm (bitsOfNT5_set hM t hwf u _ m _
        (by rw [Nat.testBit_xor, zmod2_cond_xor, hones]; rfl))
  | .cnot c tg _, t, hwf =>
    Eq.symm (bitsOfNT5_set hM t hwf tg _ m _ (by rw [Nat.testBit_xor, zmod2_cond_xor]; rfl))
  | .andGate c1 c2 a _ _ _, t, hwf =>
    Eq.symm (bitsOfNT5_set hM t hwf a _ m _
        (by rw [Nat.testBit_xor, Nat.testBit_and, zmod2_cond_xor, zmod2_cond_and]; rfl))
  | .seq p q, t, hwf =>
    (congrArg q.fwdBits (fwdBits_bitsOfNT5 hM ones m hones p t hwf)).trans (fwdBits_bitsOfNT5 hM
        ones m hones q _ (evalProgNT5_wf ones p t hwf))
inductive GateN where
  | x (u : ℕ)
  | cnot (c t : ℕ)
  | andGate (c1 c2 a : ℕ)
  deriving DecidableEq

def toGatesNAux {n : ℕ} : ComputeProg n → List GateN → List GateN
  | .id, acc => acc
  | .x u, acc => .x u.val :: acc
  | .cnot c t _, acc => .cnot c.val t.val :: acc
  | .andGate c1 c2 a _ _ _, acc => .andGate c1.val c2.val a.val :: acc
  | .seq p q, acc => toGatesNAux p (toGatesNAux q acc)

def stepGateNT5 (ones : ℕ) (g : GateN) (t : NTree5) : NTree5 :=
  match g with
  | .x u => setNT5 5 t u ((getNT5 5 t u) ^^^ ones)
  | .cnot c tg => setNT5 5 t tg ((getNT5 5 t tg) ^^^ (getNT5 5 t c))
  | .andGate c1 c2 a =>
      setNT5 5 t a ((getNT5 5 t a) ^^^ ((getNT5 5 t c1) &&& (getNT5 5 t c2)))

def stepGateNT5CPS {α : Type} (ones : ℕ) (g : GateN) (t : NTree5) (k : NTree5 → α) : α :=
  match g with
  | .x u => setNT5CPS 5 t u ((getNT5 5 t u) ^^^ ones) k
  | .cnot c tg => setNT5CPS 5 t tg ((getNT5 5 t tg) ^^^ (getNT5 5 t c)) k
  | .andGate c1 c2 a =>
      setNT5CPS 5 t a ((getNT5 5 t a) ^^^ ((getNT5 5 t c1) &&& (getNT5 5 t c2))) k

def evalGatesNT5 (ones : ℕ) : List GateN → NTree5 → NTree5
  | [], t => t
  | g :: gs, t => evalGatesNT5 ones gs (stepGateNT5 ones g t)

def evalGatesNT5CPS {α : Type} (ones : ℕ) : List GateN → NTree5 → (NTree5 → α) → α
  | [], t, k => k t
  | g :: gs, t, k => stepGateNT5CPS ones g t fun t' ↦ evalGatesNT5CPS ones gs t' k

theorem NT5Lemmas.stepGateNT5CPS_eq {α : Type} (ones : ℕ) (g : GateN) (t : NTree5)
    (k : NTree5 → α) : stepGateNT5CPS ones g t k = k (stepGateNT5 ones g t) := by
  cases g <;> exact setNT5CPS_eq 5 t _ _ k
theorem NT5Lemmas.evalGatesNT5CPS_eq {α : Type} (ones : ℕ) :
    ∀ (gs : List GateN) (t : NTree5) (k : NTree5 → α),
      evalGatesNT5CPS ones gs t k = k (evalGatesNT5 ones gs t)
  | [], _, _ => rfl
  | g :: gs, t, k => (stepGateNT5CPS_eq ones g t _).trans (evalGatesNT5CPS_eq ones gs _ k)
theorem NT5Lemmas.toGatesNAux_eval_nt5 {M : ℕ} (ones : ℕ) :
    ∀ (p : ComputeProg M) (acc : List GateN) (t : NTree5),
      evalGatesNT5 ones (toGatesNAux p acc) t = evalGatesNT5 ones acc (evalProgNT5 ones p t)
  | .id, _, _ => rfl
  | .x _, _, _ => rfl
  | .cnot _ _ _, _, _ => rfl
  | .andGate _ _ _ _ _ _, _, _ => rfl
  | .seq p q, acc, t =>
    (toGatesNAux_eval_nt5 ones p (toGatesNAux q acc) t).trans (toGatesNAux_eval_nt5 ones q acc _)
def packBits (f : ℕ → Bool) : ℕ → ℕ → ℕ
  | 0, base => cond (f base) 1 0
  | d + 1, base =>
      let lo := packBits f d base
      let hi := packBits f d (base + (1 <<< d))
      lo ||| (hi <<< (1 <<< d))

theorem NT5Lemmas.packBits_testBit :
    ∀ (f : ℕ → Bool) (d base m : ℕ),
      (packBits f d base).testBit m = (decide (m < 2 ^ d) && f (base + m))
  | f, 0, base, 0 =>
      by dsimp only [packBits, Nat.pow_zero]; rw [Nat.add_zero]; cases f base <;> rfl
  | f, 0, base, k + 1 => by
      dsimp only [packBits, Nat.pow_zero]; rw [decide_eq_false (by omega : ¬(k + 1 < 1)),
          Bool.false_and]
      cases f base <;>
          (first
          | exact Nat.zero_testBit (k +
          1) | exact (Nat.testBit_succ 1 k).trans (Nat.zero_testBit k))
  | f, d + 1, base, m => by
      dsimp only [packBits]
      rw [show (1 <<< d) = 2 ^ d by simp [Nat.shiftLeft_eq], Nat.testBit_or, Nat.testBit_shiftLeft,
          packBits_testBit f d base m, packBits_testBit f d (base + 2 ^ d)
          (m - 2 ^ d), Nat.pow_succ]
      by_cases h1 : m < 2 ^ d
      · simp [h1, show ¬(m ≥ 2 ^ d) by omega, show m < 2 ^ d * 2 by omega]
      · by_cases h2 : m < 2 ^ d * 2
        · simp [h1, show m ≥ 2 ^ d by omega, h2, show m - 2 ^ d < 2 ^ d by omega, show base +
              2 ^ d + (m - 2 ^ d) = base + m by omega]
        · simp [h1, show m ≥ 2 ^ d by omega, h2, show ¬(m - 2 ^ d < 2 ^ d) by omega]

def evalWords : List ℕ → ℕ → ℕ
  | [], _ => 0
  | b :: bs, m => cond (b.testBit m) 1 0 + 2 * evalWords bs m

def addMask0 : ℕ → List ℕ → List ℕ
  | c, [] => cond (c == 0) [] [c]
  | c, b :: bs =>
      let s := b ^^^ c
      let c' := b &&& c
      let s1 := cond (s == 0) 0 s
      let c1 := cond (c' == 0) 0 c'
      s1 :: addMask0 c1 bs

def addMaskAt : ℕ → ℕ → List ℕ → List ℕ
  | 0, c, bs => addMask0 c bs
  | k + 1, c, [] => 0 :: addMaskAt k c []
  | k + 1, c, b :: bs => b :: addMaskAt k c bs

theorem NT5Lemmas.cond_zero_eq (x : ℕ) : cond (x == 0) 0 x = x := by
  cases hx : (x == 0) <;> simp_all
theorem NT5Lemmas.evalWords_addMask0 :
    ∀ (bs : List ℕ) (c m : ℕ),
      evalWords (addMask0 c bs) m = cond (c.testBit m) 1 0 + evalWords bs m
  | [], c, m => by cases hc : (c == 0) <;> simp_all [addMask0, evalWords]
  | b :: bs, c, m => by
      dsimp only [addMask0, evalWords]
      rw [cond_zero_eq (b ^^^ c), cond_zero_eq (b &&& c), evalWords_addMask0 bs (b &&& c) m,
          Nat.testBit_xor, Nat.testBit_and]
      cases b.testBit m <;> cases c.testBit m <;> simp; omega

theorem NT5Lemmas.evalWords_addMaskAt :
    ∀ (k c : ℕ) (bs : List ℕ) (m : ℕ),
      evalWords (addMaskAt k c bs) m = cond (c.testBit m) 1 0 * 2 ^ k + evalWords bs m
  | 0, c, bs, m =>
      by simpa only [addMaskAt, Nat.pow_zero, Nat.mul_one] using evalWords_addMask0 bs c m
  | k + 1, c, [], m => by
      dsimp only [addMaskAt, evalWords]
      rw [evalWords_addMaskAt k c [] m, Nat.zero_testBit, Nat.pow_succ]
      cases c.testBit m <;> dsimp only [cond, evalWords] <;> omega
  | k + 1, c, b :: bs, m => by
      dsimp only [addMaskAt, evalWords]
      rw [evalWords_addMaskAt k c bs m, Nat.pow_succ]
      cases c.testBit m <;> dsimp only [cond] <;> omega

def allZero : List ℕ → Bool
  | [] => true
  | x :: xs => (x == 0) && allZero xs

theorem NT5Lemmas.allZero_sound :
    ∀ (xs : List ℕ), allZero xs = true → ∀ m, evalWords xs m = 0
  | [], _, _ => rfl
  | x :: xs, h, m =>
      by simp only [allZero, Bool.and_eq_true, beq_iff_eq] at h; simp [evalWords, h.1,
           allZero_sound xs h.2 m]
def eqWords : List ℕ → List ℕ → Bool
  | [], bs => allZero bs
  | a :: as, [] => (a == 0) && allZero as
  | a :: as, b :: bs => (a == b) && eqWords as bs

theorem NT5Lemmas.eqWords_sound :
    ∀ (as bs : List ℕ), eqWords as bs = true → ∀ m, evalWords as m = evalWords bs m
  | [], bs, h, m => (allZero_sound bs h m).symm
  | a :: as, [], h, m =>
      by simp only [eqWords, Bool.and_eq_true, beq_iff_eq] at h; simp [evalWords, h.1,
           allZero_sound as h.2 m]
  | a :: as, b :: bs, h, m =>
      by simp only [eqWords, Bool.and_eq_true, beq_iff_eq] at h; simp [evalWords, h.1,
           eqWords_sound as bs h.2 m]
def tokWiresLt304 (tok : DToken) : Bool := tok.2.1.all fun s ↦ Nat.blt s 304
def ones512 : ℕ := 2 ^ 512 - 1

theorem NT5Lemmas.ones512_testBit_lt {m : ℕ} (hm : m < 512) : ones512.testBit m = true := by
  simpa only [ones512, Nat.testBit_two_pow_sub_one] using decide_eq_true hm
theorem NT5Lemmas.ones512_testBit (m : Fin 512) : ones512.testBit m.val = true :=
    ones512_testBit_lt m.isLt
def axTokensHa1 : List DToken :=
    [ (0, [32], true), (2, [67], false), (8, [66], true), (2, [34], true), (3, [34], false),
    (3, [35], false), (4, [36], false), (5, [37], false), (6, [38], false), (7, [39], false),
    (8, [32, 66], false), (9, [33, 66], false), (10, [34, 66], false), (11, [35, 66], false),
    (12, [36, 66], false), (13, [37, 66], false), (14, [38, 66], false), (15, [39, 66], false),
    (2, [32, 34], true), (3, [32, 35], true), (4, [32, 36], true), (5, [32, 37], true),
    (6, [32, 38], true), (7, [32, 39], true), (3, [33, 34], true), (4, [33, 35], true),
    (5, [33, 36], true), (6, [33, 37], true), (7, [33, 38], true), (8, [33, 39], true),
    (5, [34, 35], true), (6, [34, 36], true), (7, [34, 37], true), (8, [34, 38], true),
    (9, [34, 39], true), (7, [35, 36], true), (8, [35, 37], true), (9, [35, 38], true),
    (10, [35, 39], true), (9, [36, 37], true), (10, [36, 38], true), (11, [36, 39], true),
    (11, [37, 38], true), (12, [37, 39], true), (13, [38, 39], true)]
def ax2TokensSub4 : List DToken :=
    [ (0, [40], true), (2, [41, 42], true), (2, [40, 41, 42, 76], true), (3, [78], false),
    (8, [75], true), (3, [43], false), (4, [44], false), (5, [45], false), (6, [46], false),
    (7, [47], false), (8, [40, 75], false), (9, [41, 75], false), (10, [42, 75], false),
    (11, [43, 75], false), (12, [44, 75], false), (13, [45, 75], false), (14, [46, 75], false),
    (15, [47, 75], false), (3, [40, 43], true), (4, [40, 44], true), (5, [40, 45], true),
    (6, [40, 46], true), (7, [40, 47], true), (4, [41, 43], true), (5, [41, 44], true),
    (6, [41, 45], true), (7, [41, 46], true), (8, [41, 47], true), (5, [42, 43], true),
    (6, [42, 44], true), (7, [42, 45], true), (8, [42, 46], true), (9, [42, 47], true),
    (7, [43, 44], true), (8, [43, 45], true), (9, [43, 46], true), (10, [43, 47], true),
    (9, [44, 45], true), (10, [44, 46], true), (11, [44, 47], true), (11, [45, 46], true),
    (12, [45, 47], true), (13, [46, 47], true)]
def initDualGlfa135 : List DToken :=
    axTokens0_ha ++ axTokensHa1 ++ ax2TokensSub4 ++ [(16, [], true), (17, [], true)]
def stepGlfa (pool : List DToken) (k0 k1 k2 : ℕ) : List DToken × ComputeProg 304 :=
  let (t0, p1) := splitTok k0 pool
  let (t1, p2) := splitTok k1 p1
  let (t2, p3) := splitTok k2 p2
  let wS := t0.2.1.headD 0
  let wP := t1.2.1.headD 0
  (p3 ++ [(t0.1, [wS], false), (t0.1 + 1, [wP], false)],
   .seq (xorTokCP wS t1) (xorTokCP wS t2))

def codesAx0B1C1 : List ℕ := [ 80904, 5373692437, 5469649417, 5506337285]
def codesAx0B2 : List ℕ := [ 5573970429, 5669925369, 5707139573]
def codesAx0B3 : List ℕ := [ 5774248429, 5870201321, 5905843685]
def poolAfter0Dual : List DToken := (stepDadda initDualGlfa135 5171578885).1
def ax0StepB1 : List DToken × ComputeProg 304 := runDaddaList poolAfter0Dual codesAx0B1C1
def ax0StepG1 : List DToken × ComputeProg 304 := stepGlfa ax0StepB1.1 129 128 16
def ax0StepB2 : List DToken × ComputeProg 304 := runDaddaList ax0StepG1.1 codesAx0B2
def ax0StepG2 : List DToken × ComputeProg 304 := stepGlfa ax0StepB2.1 125 124 12
def ax0StepB3 : List DToken × ComputeProg 304 := runDaddaList ax0StepG2.1 codesAx0B3
def ax0StepG3 : List DToken × ComputeProg 304 := stepGlfa ax0StepB3.1 121 120 8

def pAx0Prefix304 : ComputeProg 304 :=
    .seq ax0StepB1.2 (.seq ax0StepG1.2 (.seq ax0StepB2.2 (.seq ax0StepG2.2 (.seq ax0StepB3.2
    ax0StepG3.2))))
def pStep0Ax0_304 : ComputeProg 304 := .seq (stepDadda initDualGlfa135 5171578885).2 pAx0Prefix304
def ax0DonePre23 : List DToken :=
    [ (0, [24], true), (9, [25, 57], false), (10, [26, 57], false), (11, [27, 57], false),
    (12, [28, 57], false), (13, [29, 57], false), (14, [30, 57], false), (15, [31, 57], false),
    (5, [26, 27], true), (6, [26, 28], true), (7, [26, 29], true), (8, [26, 30], true),
    (9, [26, 31], true), (7, [27, 28], true), (8, [27, 29], true), (9, [27, 30], true),
    (10, [27, 31], true), (9, [28, 29], true), (10, [28, 30], true), (11, [28, 31], true),
    (11, [29, 30], true), (12, [29, 31], true), (13, [30, 31], true)]
def ax0DoneTail9 : List DToken :=
    [ (2, [58], false), (3, [77], false), (4, [80], false), (5, [81], false), (6, [83], false),
    (7, [84], false), (9, [88], false), (8, [86], false), (9, [87], false)]
abbrev ActiveAx0Prop (n : ℕ) : Prop :=
    n = 24 ∨ n = 25 ∨ n = 26 ∨ n = 27 ∨ n = 28 ∨ n = 29 ∨ n = 30 ∨ n = 31 ∨ n = 49 ∨ n = 57 ∨ n =
    58 ∨ n = 77 ∨ n = 79 ∨ n = 80 ∨ n = 81 ∨ n = 82 ∨ n = 83 ∨ n = 84 ∨ n = 85 ∨ n = 86 ∨ n = 87 ∨
    n = 88
def okW304_Ax0 (n : ℕ) : Bool :=
    (n == 24) || (n == 25) || (n == 26) || (n == 27) || (n == 28) || (n == 29) || (n == 30) ||
    (n == 31) || (n == 49) || (n == 57) || (n == 58) || (n == 77) || (n == 79) || (n == 80) ||
    (n == 81) || (n == 82) || (n == 83) || (n == 84) || (n == 85) || (n == 86) || (n == 87) ||
    (n == 88)
def fAx0To304 (u : Wire 22) : Wire 304 :=
    if u.val = 0 then w304 24 else if u.val = 1 then w304 25 else if u.val =
    2 then w304 26 else if u.val = 3 then w304 27 else if u.val = 4 then w304 28 else if u.val =
    5 then w304 29 else if u.val = 6 then w304 30 else if u.val = 7 then w304 31 else if u.val =
    8 then w304 49 else if u.val = 9 then w304 57 else if u.val = 10 then w304 58 else if u.val =
    11 then w304 77 else if u.val = 12 then w304 79 else if u.val = 13 then w304 80 else if u.val =
    14 then w304 81 else if u.val = 15 then w304 82 else if u.val = 16 then w304 83 else if u.val =
    17 then w304 84 else if u.val = 18 then w304 85 else if u.val = 19 then w304 86 else if u.val =
    20 then w304 87 else w304 88
def f304ToAx0 (w : Wire 304) : Wire 22 :=
  if _h0 : w.val = 24 then ⟨0, by decide⟩
  else if _h1 : w.val = 25 then ⟨1, by decide⟩
  else if _h2 : w.val = 26 then ⟨2, by decide⟩
  else if _h3 : w.val = 27 then ⟨3, by decide⟩
  else if _h4 : w.val = 28 then ⟨4, by decide⟩
  else if _h5 : w.val = 29 then ⟨5, by decide⟩
  else if _h6 : w.val = 30 then ⟨6, by decide⟩
  else if _h7 : w.val = 31 then ⟨7, by decide⟩
  else if _h8 : w.val = 49 then ⟨8, by decide⟩
  else if _h9 : w.val = 57 then ⟨9, by decide⟩
  else if _h10 : w.val = 58 then ⟨10, by decide⟩
  else if _h11 : w.val = 77 then ⟨11, by decide⟩
  else if _h12 : w.val = 79 then ⟨12, by decide⟩
  else if _h13 : w.val = 80 then ⟨13, by decide⟩
  else if _h14 : w.val = 81 then ⟨14, by decide⟩
  else if _h15 : w.val = 82 then ⟨15, by decide⟩
  else if _h16 : w.val = 83 then ⟨16, by decide⟩
  else if _h17 : w.val = 84 then ⟨17, by decide⟩
  else if _h18 : w.val = 85 then ⟨18, by decide⟩
  else if _h19 : w.val = 86 then ⟨19, by decide⟩
  else if _h20 : w.val = 87 then ⟨20, by decide⟩
  else if _h21 : w.val = 88 then ⟨21, by decide⟩
  else ⟨0, by decide⟩
def f304ToAx0Nat (s : ℕ) : ℕ :=
    if s == 24 then 0 else if s == 25 then 1 else if s == 26 then 2 else if s == 27 then 3 else if s
    == 28 then 4 else if s == 29 then 5 else if s == 30 then 6 else if s == 31 then 7 else if s ==
    49 then 8 else if s == 57 then 9 else if s == 58 then 10 else if s == 77 then 11 else if s == 79
    then 12 else if s == 80 then 13 else if s == 81 then 14 else if s == 82 then 15 else if s == 83
    then 16 else if s == 84 then 17 else if s == 85 then 18 else if s == 86 then 19 else if s == 87
    then 20 else if s == 88 then 21 else 0
theorem activeWireAx0_of_bool {n : ℕ} (h : okW304_Ax0 n = true) : ActiveAx0Prop n := by
  simp only [okW304_Ax0, Bool.or_eq_true, beq_iff_eq] at h; omega
theorem okW304_Ax0_of_active {n : ℕ} (h : ActiveAx0Prop n) : okW304_Ax0 n = true := by
  simp only [okW304_Ax0, Bool.or_eq_true, beq_iff_eq]; omega
theorem fAx0_f304_id {w : Wire 304} (hw : ActiveAx0Prop w.val) : fAx0To304 (f304ToAx0 w) = w := by
  have hchk : ((List.finRange 304).all fun u ↦ !(okW304_Ax0 u.val) ||
      (fAx0To304 (f304ToAx0 u) == u)) = true := by decide +kernel
  simpa [okW304_Ax0_of_active hw] using (List.all_eq_true.mp hchk) w (List.mem_finRange w)

def activeInAx0 : ComputeProg 304 → Bool
  | .id => true
  | .x u => okW304_Ax0 u.val
  | .cnot c t _ => okW304_Ax0 c.val && okW304_Ax0 t.val
  | .andGate c1 c2 a _ _ _ => okW304_Ax0 c1.val && okW304_Ax0 c2.val && okW304_Ax0 a.val
  | .seq p q => activeInAx0 p && activeInAx0 q

def stepActiveAx0_1 : List (ComputeProg 304) → Option (List (ComputeProg 304))
  | [] => some []
  | .id :: rest => some rest
  | .x u :: rest => if okW304_Ax0 u.val then some rest else none
  | .cnot c t _ :: rest => if okW304_Ax0 c.val && okW304_Ax0 t.val then some rest else none
  | .andGate c1 c2 a _ _ _ :: rest =>
      if okW304_Ax0 c1.val && okW304_Ax0 c2.val && okW304_Ax0 a.val then some rest else none
  | .seq p q :: rest => some (p :: q :: rest)

def stepActiveAx0Pow : ℕ → List (ComputeProg 304) → Option (List (ComputeProg 304))
  | 0, ws => stepActiveAx0_1 ws
  | d + 1, ws => match stepActiveAx0Pow d ws with
    | none => none
    | some ws' => stepActiveAx0Pow d ws'

def checkActiveAx0Pow (d : ℕ) (ws : List (ComputeProg 304)) : Bool :=
  match stepActiveAx0Pow d ws with
  | some [] => true
  | _ => false

theorem stepActiveAx0Pow_sound :
    ∀ (d : ℕ) {ws ws' : List (ComputeProg 304)},
      stepActiveAx0Pow d ws = some ws' →
      (∀ q ∈ ws', activeInAx0 q = true) → ∀ q ∈ ws, activeInAx0 q = true
  | 0, ws, ws', h, hall => by
      have hLeaf {b : Bool} {p : ComputeProg 304} {rest : List (ComputeProg 304)}
          (hb : activeInAx0 p = b)
          (hs : (if b then some rest else none) = some ws') : ∀ q ∈ p :: rest, activeInAx0 q =
              true := by
        cases b <;>
            simp only [Bool.false_eq_true, ↓reduceIte, reduceCtorEq, Option.some.injEq] at hs
        exact fun q hq ↦ (List.mem_cons.mp hq).elim (fun e ↦ e ▸ hb) fun hm ↦ hall q (hs ▸ hm)
      cases ws with
      | nil => exact fun _ hm ↦ False.elim (List.not_mem_nil hm)
      | cons p rest =>
        cases p with
        | id | x _ | cnot _ _ _ | andGate _ _ _ _ _ _ => exact hLeaf rfl h
        | seq p1 p2 =>
            cases h
            exact fun q hq ↦ (List.mem_cons.mp hq).elim
              (fun e ↦ e ▸ Bool.and_eq_true_iff.mpr
                ⟨hall p1 List.mem_cons_self, hall p2 (List.mem_cons_of_mem _ List.mem_cons_self)⟩)
              fun hr ↦ hall q (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr))
  | d + 1, ws, _, h, hall => by
      dsimp only [stepActiveAx0Pow] at h; cases hm : stepActiveAx0Pow d ws <;> rw [hm] at h
      · nomatch h
      · exact stepActiveAx0Pow_sound d hm (stepActiveAx0Pow_sound d h hall)

def pullBackAx0 : ComputeProg 304 → ComputeProg 22
  | .id => .id
  | .x u => .x (f304ToAx0 u)
  | .cnot c t _ => safeCnotCP (f304ToAx0 c) (f304ToAx0 t)
  | .andGate c1 c2 a _ _ _ => safeAndGateCP (f304ToAx0 c1) (f304ToAx0 c2) (f304ToAx0 a)
  | .seq p q => .seq (pullBackAx0 p) (pullBackAx0 q)

def projAx0 (γ : BitAssignment 304) : BitAssignment 22 := fun u ↦ γ (fAx0To304 u)

def patchAx0 (γ : BitAssignment 304) (δ : BitAssignment 22) : BitAssignment 304 := fun w ↦
    if _hw : ActiveAx0Prop w.val then δ (f304ToAx0 w) else γ w
theorem patchAx0_pos {w : Wire 304} (hw : ActiveAx0Prop w.val) (γ : BitAssignment 304)
    (δ : BitAssignment 22) : patchAx0 γ δ w = δ (f304ToAx0 w) := leg_dif_pos hw
theorem patchAx0_neg {w : Wire 304} (hw : ¬ActiveAx0Prop w.val) (γ : BitAssignment 304)
    (δ : BitAssignment 22) : patchAx0 γ δ w = γ w := leg_dif_neg hw
theorem patchAx0_projAx0 (γ : BitAssignment 304) : patchAx0 γ (projAx0 γ) = γ :=
  funext fun w ↦
      (Classical.em (ActiveAx0Prop w.val)).elim (fun hw ↦
      (patchAx0_pos hw _ _).trans (congrArg γ (fAx0_f304_id hw))) fun hw ↦ patchAx0_neg hw _ _

theorem f304ToAx0_ne_of_ne {u v : Wire 304} (hu : ActiveAx0Prop u.val) (hv : ActiveAx0Prop v.val)
    (hne : u ≠ v) : f304ToAx0 u ≠ f304ToAx0 v :=
  fun e ↦ hne ((fAx0_f304_id hu).symm.trans ((congrArg fAx0To304 e).trans (fAx0_f304_id hv)))

theorem patchAx0_update {u : Wire 304} (hu : ActiveAx0Prop u.val) (γ : BitAssignment 304)
    (δ : BitAssignment 22) (v : ZMod 2) :
    Function.update (patchAx0 γ δ) u v = patchAx0 γ (Function.update δ (f304ToAx0 u) v) :=
        funext fun w ↦ by
  by_cases hw : ActiveAx0Prop w.val
  · by_cases hwu : w = u <;> first
      | (subst hwu; simp [patchAx0_pos hw])
      | simp [hwu, f304ToAx0_ne_of_ne hw hu hwu, patchAx0_pos hw]
  · rw [Function.update_of_ne (fun (e : w = u) ↦ hw (e ▸ hu)), patchAx0_neg hw, patchAx0_neg hw]

theorem pullBackAx0_fwdBits :
    ∀ (p : ComputeProg 304), activeInAx0 p = true →
      ∀ (γ : BitAssignment 304) (δ : BitAssignment 22),
        p.fwdBits (patchAx0 γ δ) = patchAx0 γ ((pullBackAx0 p).fwdBits δ)
  | .id, _, _, _ => rfl
  | .x u, ha, _, _ =>
      by rw [pullBackAx0, ComputeProg.fwdBits, ComputeProg.fwdBits,
           patchAx0_pos (activeWireAx0_of_bool ha), patchAx0_update (activeWireAx0_of_bool ha)]
  | .cnot c t hct, ha, _, _ => by
      simp only [activeInAx0, Bool.and_eq_true] at ha
      rw [pullBackAx0, safeCnotCP, leg_dif_neg (f304ToAx0_ne_of_ne (activeWireAx0_of_bool ha.1)
          (activeWireAx0_of_bool ha.2) hct)]
      rw [ComputeProg.fwdBits, ComputeProg.fwdBits, patchAx0_pos (activeWireAx0_of_bool ha.2),
          patchAx0_pos (activeWireAx0_of_bool ha.1), patchAx0_update (activeWireAx0_of_bool ha.2)]
  | .andGate c1 c2 a h12 h1a h2a, ha, _, _ => by
      simp only [activeInAx0, Bool.and_eq_true] at ha
      have hc1 := activeWireAx0_of_bool ha.1.1
      have hc2 := activeWireAx0_of_bool ha.1.2
      have haa := activeWireAx0_of_bool ha.2
      rw [pullBackAx0, safeAndGateCP, leg_dif_neg (f304ToAx0_ne_of_ne hc1 hc2 h12),
          leg_dif_neg (f304ToAx0_ne_of_ne hc1 haa h1a),
          leg_dif_neg (f304ToAx0_ne_of_ne hc2 haa h2a)]
      rw [ComputeProg.fwdBits, ComputeProg.fwdBits, patchAx0_pos haa, patchAx0_pos hc1,
          patchAx0_pos hc2, patchAx0_update haa]
  | .seq p q, ha, γ, δ => by
      simp only [activeInAx0, Bool.and_eq_true] at ha
      exact (congrArg q.fwdBits (pullBackAx0_fwdBits p ha.1 γ δ)).trans (pullBackAx0_fwdBits q ha.2
          γ _)
def tokBitAx0 (t : DToken) (δ : BitAssignment 22) : ZMod 2 :=
    (if t.2.2 then 1 else 0) + t.2.1.foldr (fun s acc ↦ δ (f304ToAx0 (w304 s)) + acc) 0
def poolSumAx0 (ps : List DToken) (δ : BitAssignment 22) : ℕ :=
    ps.foldr (fun t acc ↦ (tokBitAx0 t δ).val * 2 ^ t.1 + acc) 0
def tokInAx0 (t : DToken) : Bool := t.2.1.all fun s ↦ okW304_Ax0 (w304 s).val

theorem poolSum_patchAx0 {ps : List DToken} (hps : ps.all tokInAx0 = true) (γ : BitAssignment 304)
    (δ : BitAssignment 22) : poolSum ps (patchAx0 γ δ) = poolSumAx0 ps δ := by
  induction ps with
  | nil => rfl
  | cons t ts ih =>
      rcases t with ⟨col, ws, inv⟩; simp only [List.all_cons, Bool.and_eq_true, tokInAx0] at hps
      rcases hps with ⟨ht, hts⟩
      refine congrArg₂ (fun (b : ZMod 2) r ↦ b.val * 2 ^ col + r)
        (congrArg ((if inv then 1 else 0) + ·) ?_) (ih hts)
      induction ws with
      | nil => rfl
      | cons s ss ihw =>
          simp only [List.all_cons, Bool.and_eq_true] at ht
          exact congrArg₂ (· + ·) (patchAx0_pos (activeWireAx0_of_bool ht.1) γ δ) (ihw ht.2)
def tokMaskNT5Ax0 (ones : ℕ) (tok : DToken) (t : NTree5) : ℕ :=
  let m0 := cond tok.2.2 ones 0
  tok.2.1.foldr (fun s acc ↦
    let v := (getNT5 5 t (f304ToAx0Nat s)) ^^^ acc
    cond (v == 0) 0 v) m0

def poolWordsNT5Ax0 (ones : ℕ) (ps : List DToken) (t : NTree5) : List ℕ :=
    ps.foldr (fun tok acc ↦ addMaskAt tok.1 (tokMaskNT5Ax0 ones tok t) acc) []
theorem poolWordsNT5Ax0_eval (ones m : ℕ) (hones : ones.testBit m = true) {ps : List DToken}
    (hps : ps.all tokWiresLt304 = true) (t : NTree5) :
    evalWords (poolWordsNT5Ax0 ones ps t) m = poolSumAx0 ps (bitsOfNT5 t m) := by
  have hchk : ((List.range 304).all fun n ↦ f304ToAx0Nat n == (f304ToAx0 (w304 n)).val) = true := by
    decide +kernel
  have hws : ∀ (l : List ℕ), (l.all fun s ↦ Nat.blt s 304) = true → ∀ (base : ℕ),
      cond ((l.foldr (fun s acc ↦
        let v := (getNT5 5 t (f304ToAx0Nat s)) ^^^ acc
        cond (v == 0) 0 v) base).testBit m) (1 : ZMod 2) 0 =
        l.foldr (fun s acc ↦ bitsOfNT5 (M := 22) t m (f304ToAx0 (w304 s)) + acc) 0 +
            cond (base.testBit m) 1 0 := by
    intro l; induction l with
    | nil => exact fun _ _ ↦ (zero_add _).symm
    | cons s ss ih =>
        intro hl base; simp only [List.all_cons, Bool.and_eq_true] at hl;
            dsimp only [List.foldr, bitsOfNT5]
        rw [cond_zero_eq, Nat.testBit_xor, zmod2_cond_xor, ih hl.2,
          beq_iff_eq.mp ((List.all_eq_true.mp hchk) s (List.mem_range.mpr (Nat.blt_eq.mp hl.1))),
              ← add_assoc]; rfl
  induction ps with
  | nil => rfl
  | cons tok ts ih =>
      rcases tok with ⟨col, ws, inv⟩; simp only [List.all_cons, Bool.and_eq_true,
          tokWiresLt304] at hps
      have hTok : cond ((tokMaskNT5Ax0 ones (col, ws, inv) t).testBit m) (1 : ZMod 2) 0 =
          tokBitAx0 (col, ws, inv) (bitsOfNT5 t m) := by
        dsimp only [tokMaskNT5Ax0, tokBitAx0]; rw [hws ws hps.1 (cond inv ones 0), add_comm]
        cases inv <;> simp [cond, hones]
      simpa only [poolWordsNT5Ax0, poolSumAx0, List.foldr, evalWords_addMaskAt, ← hTok,
          zmod2_cond_val] using
        congrArg (_ + ·) (ih hps.2)
def pStep0Ax0_22 : ComputeProg 22 := pullBackAx0 pStep0Ax0_304

theorem pStep0Ax0_304_active : activeInAx0 pStep0Ax0_304 = true := by
  have hc : checkActiveAx0Pow 10 [pStep0Ax0_304] = true := by decide +kernel
  unfold checkActiveAx0Pow at hc
  exact stepActiveAx0Pow_sound 10 (by split at hc <;> first | assumption | cases hc)
    (fun _ hm ↦ False.elim (List.not_mem_nil hm)) pStep0Ax0_304 (List.mem_singleton_self _)

def gsStep0Ax0_22 : List GateN :=
    [ .x 10, .cnot 0 10, .cnot 2 10, .x 8, .cnot 2 8, .x 8, .cnot 0 8, .cnot 2 8, .andGate 10 8 11,
    .x 8, .cnot 0 8, .cnot 2 8, .x 8, .cnot 2 8, .x 11, .cnot 0 11, .cnot 2 11, .x 10, .cnot 2 10,
    .cnot 2 12, .x 12, .cnot 1 12, .cnot 2 12, .cnot 3 8, .x 8, .cnot 1 8, .cnot 2 8,
    .andGate 12 8 13, .x 8, .cnot 1 8, .cnot 2 8, .cnot 3 8, .x 13, .cnot 1 13, .cnot 2 13,
    .cnot 3 12, .cnot 12 11, .x 8, .cnot 0 8, .cnot 3 8, .cnot 12 8, .andGate 11 8 14, .cnot 12 8,
    .x 8, .cnot 0 8, .cnot 3 8, .cnot 12 14, .x 11, .cnot 0 11, .cnot 3 11, .x 13, .cnot 0 13,
    .cnot 4 13, .cnot 4 8, .x 8, .cnot 0 8, .cnot 4 8, .andGate 13 8 15, .x 8, .cnot 0 8, .cnot 4 8,
    .cnot 4 8, .x 15, .cnot 0 15, .cnot 4 15, .cnot 4 13, .cnot 14 13, .x 13, .cnot 1 13,
    .cnot 3 13, .x 15, .cnot 1 15, .cnot 4 15, .cnot 5 8, .x 8, .cnot 1 8, .cnot 4 8,
    .andGate 15 8 16, .x 8, .cnot 1 8, .cnot 4 8, .cnot 5 8, .x 16, .cnot 1 16, .cnot 4 16,
    .cnot 5 15, .cnot 15 14, .x 8, .cnot 0 8, .cnot 5 8, .cnot 15 8, .andGate 14 8 17, .cnot 15 8,
    .x 8, .cnot 0 8, .cnot 5 8, .cnot 15 17, .x 14, .cnot 0 14, .cnot 5 14, .x 16, .cnot 0 16,
    .cnot 6 16, .cnot 6 8, .x 8, .cnot 0 8, .cnot 6 8, .andGate 16 8 18, .x 8, .cnot 0 8, .cnot 6 8,
    .cnot 6 8, .x 18, .cnot 0 18, .cnot 6 18, .cnot 6 16, .cnot 17 16, .x 16, .cnot 1 16,
    .cnot 5 16, .x 18, .cnot 1 18, .cnot 6 18, .cnot 7 8, .x 8, .cnot 1 8, .cnot 6 8,
    .andGate 18 8 19, .x 8, .cnot 1 8, .cnot 6 8, .cnot 7 8, .x 19, .cnot 1 19, .cnot 6 19,
    .cnot 7 18, .cnot 18 17, .x 8, .cnot 0 8, .cnot 7 8, .cnot 18 8, .andGate 17 8 20, .cnot 18 8,
    .x 8, .cnot 0 8, .cnot 7 8, .cnot 18 20, .x 17, .cnot 0 17, .cnot 7 17, .cnot 0 19, .cnot 9 19,
    .x 8, .cnot 9 8, .cnot 0 8, .cnot 9 8, .andGate 19 8 21, .cnot 0 8, .cnot 9 8, .x 8, .cnot 9 8,
    .cnot 0 21, .cnot 9 21, .x 19, .cnot 9 19, .cnot 20 19, .x 19, .cnot 1 19, .cnot 7 19]
theorem evalProgNT5_pStep0Ax0_eq (ones : ℕ) (t : NTree5) : evalProgNT5 ones pStep0Ax0_22 t =
    evalGatesNT5 ones gsStep0Ax0_22 t :=
  ((by decide +kernel : toGatesNAux pStep0Ax0_22 [] = gsStep0Ax0_22) ▸ toGatesNAux_eval_nt5 ones
      pStep0Ax0_22 [] t).symm

def mkIn22 (m : Fin 512) : BitAssignment 22 := fun u ↦
    if u.val < 8 then (if m.val.testBit u.val then 1 else 0) else if u.val =
    9 then (if m.val.testBit 8 then 1 else 0) else if u.val =
    10 then (if m.val.testBit 0 then 1 else 0) * (if m.val.testBit 1 then 1 else 0) else 0
def inMask22 (u : ℕ) : ℕ :=
    if Nat.blt u 8 then packBits (fun m ↦ m.testBit u) 9 0 else if u == 9 then packBits (fun m ↦
    m.testBit 8) 9 0 else if u == 10 then packBits (fun m ↦ m.testBit 0 && m.testBit 1) 9 0 else 0
def initNT5_22 : NTree5 := (List.range 11).foldl (fun t u ↦ setNT5 5 t u (inMask22 u)) (zeroNT5 5)
def initNT5_22_cps {α : Type} (k : NTree5 → α) : α :=
    setNT5CPS 5 (zeroNT5 5) 0 (inMask22 0) fun t1 ↦ setNT5CPS 5 t1 1 (inMask22 1) fun t2 ↦
    setNT5CPS 5 t2 2 (inMask22 2) fun t3 ↦ setNT5CPS 5 t3 3 (inMask22 3) fun t4 ↦
    setNT5CPS 5 t4 4 (inMask22 4) fun t5 ↦ setNT5CPS 5 t5 5 (inMask22 5) fun t6 ↦
    setNT5CPS 5 t6 6 (inMask22 6) fun t7 ↦ setNT5CPS 5 t7 7 (inMask22 7) fun t8 ↦
    setNT5CPS 5 t8 8 (inMask22 8) fun t9 ↦ setNT5CPS 5 t9 9 (inMask22 9) fun t10 ↦
    setNT5CPS 5 t10 10 (inMask22 10) k
theorem NT5Lemmas.initNT5_22_cps_eq {α : Type} (k : NTree5 → α) : initNT5_22_cps k =
    k initNT5_22 := by
  dsimp only [initNT5_22_cps, initNT5_22, List.range, List.range.loop, List.foldl]
  rw [setNT5CPS_eq, setNT5CPS_eq, setNT5CPS_eq, setNT5CPS_eq, setNT5CPS_eq, setNT5CPS_eq,
      setNT5CPS_eq, setNT5CPS_eq, setNT5CPS_eq, setNT5CPS_eq, setNT5CPS_eq]
theorem NT5Lemmas.initNT5_22_wf : wfNT5 5 initNT5_22 := by
  dsimp only [initNT5_22, List.range, List.range.loop, List.foldl]
  exact setNT5_wf 5 _ _ _ (setNT5_wf 5 _ _ _ (setNT5_wf 5 _ _ _ (setNT5_wf 5 _ _ _ (setNT5_wf 5 _ _
      _ (setNT5_wf 5 _ _ _ (setNT5_wf 5 _ _ _ (setNT5_wf 5 _ _ _ (setNT5_wf 5 _ _ _ (setNT5_wf 5 _ _
      _ (setNT5_wf 5 _ _ _ (zeroNT5_wf 5)))))))))))
theorem NT5Lemmas.getNT5_initNT5_22 (u : Wire 22) : getNT5 5 initNT5_22 u.val = inMask22 u.val := by
  have hchk : initNT5_22_cps (fun t ↦ (List.range 22).all fun u' ↦ getNT5 5 t u' == inMask22 u') =
      true := by decide +kernel
  rw [initNT5_22_cps_eq] at hchk
  exact beq_iff_eq.mp ((List.all_eq_true.mp hchk) u.val (List.mem_range.mpr u.isLt))
theorem NT5Lemmas.mkIn22_eq_bitsOfNT5 (m : Fin 512) : mkIn22 m = bitsOfNT5 initNT5_22 m.val :=
    funext fun u ↦ by
  have hm9 : decide (m.val < 2 ^ 9) = true := decide_eq_true m.isLt
  rw [mkIn22, bitsOfNT5, getNT5_initNT5_22 u, inMask22]
  by_cases h8 : u.val < 8
  · rw [leg_if_pos h8, leg_if_pos (Nat.blt_eq.mpr h8), packBits_testBit, hm9, Bool.true_and,
        Nat.zero_add, zmod2_cond_ite]
  · rw [leg_if_neg h8, leg_if_neg fun h ↦ h8 (Nat.blt_eq.mp h)]
    by_cases h9 : u.val = 9
    · rw [leg_if_pos h9, leg_if_pos (beq_iff_eq.mpr h9), packBits_testBit, hm9, Bool.true_and,
          Nat.zero_add, zmod2_cond_ite]
    · rw [leg_if_neg h9, leg_if_neg fun h ↦ h9 (beq_iff_eq.mp h)]
      by_cases h10 : u.val = 10
      · rw [leg_if_pos h10, leg_if_pos (beq_iff_eq.mpr h10), packBits_testBit, hm9, Bool.true_and,
            Nat.zero_add, zmod2_cond_ite, zmod2_cond_ite, ← zmod2_cond_and]
      · rw [leg_if_neg h10, leg_if_neg fun h ↦ h10 (beq_iff_eq.mp h), Nat.zero_testBit]; rfl

def checkStep0Ax0_22 (m : Fin 512) : Bool :=
  let inp := mkIn22 m
  let out := pStep0Ax0_22.fwdBits inp
  (out ⟨8, by decide⟩ == 0) &&
  ((List.finRange 8).all fun i ↦ out ⟨i.val, by omega⟩ == inp ⟨i.val, by omega⟩) &&
  (out ⟨9, by decide⟩ == inp ⟨9, by decide⟩) &&
  (poolSumAx0 (ax0DonePre23 ++ ax0DoneTail9) out == poolSumAx0 axTokens0_ha inp)

private def checkStep0Ax0_512_cert_bool : Bool := initNT5_22_cps fun inpT ↦
    evalGatesNT5CPS ones512 gsStep0Ax0_22 inpT fun outT ↦
    (getNT5 5 outT 8 == 0) && ((List.range 8).all fun i ↦ getNT5 5 outT i == getNT5 5 inpT i) &&
    (getNT5 5 outT 9 == getNT5 5 inpT 9) && eqWords (poolWordsNT5Ax0 ones512 (ax0DonePre23 ++
    ax0DoneTail9) outT) (poolWordsNT5Ax0 ones512 axTokens0_ha inpT)
private theorem checkStep0Ax0_512_cert : checkStep0Ax0_512_cert_bool = true := by decide +kernel
attribute [local irreducible] pStep0Ax0_22 gsStep0Ax0_22 in
theorem checkStep0Ax0_22_true (m : Fin 512) : checkStep0Ax0_22 m = true := by
  have hcert := checkStep0Ax0_512_cert
  dsimp only [checkStep0Ax0_512_cert_bool] at hcert
  rw [initNT5_22_cps_eq, evalGatesNT5CPS_eq, ← evalProgNT5_pStep0Ax0_eq ones512] at hcert
  simp only [Bool.and_eq_true, beq_iff_eq] at hcert
  obtain ⟨⟨⟨hw8, hw_lo8⟩, hw9⟩, hwords⟩ := hcert
  dsimp only [checkStep0Ax0_22]
  rw [mkIn22_eq_bitsOfNT5 m,
    fwdBits_bitsOfNT5 (by decide) ones512 m.val (ones512_testBit m) pStep0Ax0_22 initNT5_22
        initNT5_22_wf]
  simp only [Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨⟨by dsimp [bitsOfNT5]; rw [hw8, Nat.zero_testBit]; rfl,
    List.all_eq_true.mpr fun i _ ↦ beq_iff_eq.mpr (by
      dsimp [bitsOfNT5];
          rw [beq_iff_eq.mp ((List.all_eq_true.mp hw_lo8) i.val (List.mem_range.mpr i.isLt))])⟩,
    by dsimp [bitsOfNT5]; rw [hw9]⟩, ?_⟩
  have hew := eqWords_sound _ _ hwords m.val
  rw [poolWordsNT5Ax0_eval ones512 m.val (ones512_testBit m) (by decide +kernel),
    poolWordsNT5Ax0_eval ones512 m.val (ones512_testBit m) (by decide +kernel)] at hew
  exact hew
def code9Ax0 (γ : BitAssignment 304) : Fin 512 :=
    ⟨finBitsVal (fun k : Fin 9 ↦ if _h : k.val < 8 then γ (w304 (24 + k.val)) else γ (w304 57)),
    finBitsVal_lt _⟩
theorem projAx0_eq_mkIn22 (γ0 : BitAssignment 304) (h49 : γ0 (w304 49) = 0)
    (h58 : γ0 (w304 58) = γ0 (w304 24) * γ0 (w304 25)) (h77 : γ0 (w304 77) = 0)
    (hcl : ∀ w : Wire 304, 79 ≤ w.val → w.val < 89 → γ0 w = 0) : projAx0 γ0 = mkIn22 (code9Ax0 γ0)
    := by
  let f9 : Fin 9 → ZMod 2 := fun k ↦ if _h : k.val < 8 then γ0 (w304 (24 + k.val)) else γ0 (w304 57)
  have hbit : ∀ k : Fin 9, (if (code9Ax0 γ0).val.testBit k.val then (1 : ZMod 2) else 0) = f9 k :=
      fun k ↦ (finBitsVal_testBit f9 k).symm
  funext u
  by_cases h8 : u.val < 8
  · have hk := (hbit ⟨u.val, by omega⟩).symm
    fin_cases u <;> first | contradiction | simpa [projAx0, fAx0To304, mkIn22, f9] using hk
  · fin_cases u <;> first
      | contradiction | exact h49 | exact h77 | exact hcl _ (by decide) (by decide)
      | simpa [projAx0, fAx0To304, mkIn22, f9] using (hbit ⟨8, by decide⟩).symm
      | exact (show γ0 (w304 58) = _ * _ from h58.trans (congrArg₂ (· * ·)
          (by simpa [f9] using (hbit ⟨0, by decide⟩).symm)
              (by simpa [f9] using (hbit ⟨1, by decide⟩).symm)))

def forbAx0List : List ℕ :=
    [ 24, 25, 26, 27, 28, 29, 30, 31, 49, 57, 58, 77, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88]
theorem activeAx0_iff_inForb (w : Wire 304) : inNatList w.val forbAx0List = false →
    ¬ActiveAx0Prop w.val := by
  have hchk : ((List.range 304).all fun n ↦ okW304_Ax0 n == inNatList n forbAx0List) = true := by
    decide +kernel
  intro hfalse hact
  have heq := beq_iff_eq.mp ((List.all_eq_true.mp hchk) w.val (List.mem_range.mpr w.isLt))
  rw [okW304_Ax0_of_active hact, hfalse] at heq
  exact Bool.noConfusion heq
theorem pStep0Ax0_22_def : pullBackAx0 pStep0Ax0_304 = pStep0Ax0_22 := rfl

theorem nat_range_mem_bounds : ∀ (n base a : ℕ),
    inNatList a ((List.range n).map (fun i => base + i)) = true →
    base ≤ a ∧ a < base + n
  | 0, _, _, ha => Bool.noConfusion ha
  | m + 1, base, a, ha => by
      rw [List.range_succ, List.map_append, inNatList_append_quad] at ha
      rcases Bool.or_eq_true_iff.mp ha with hl | hr
      · have := nat_range_mem_bounds m base a hl
        omega
      · simp only [List.map, inNatList, Bool.or_false, beq_iff_eq] at hr
        omega

def checkStepsWf (cmEnd : List ℕ) (poolEnd : List DToken) :
    List DToken → List ℕ → List ℕ → Bool
  | pool, cm, [] => (cm == cmEnd) && (pool == poolEnd)
  | pool, cm, c :: cs =>
      match wfDaddaStep pool cm c with
      | none => false
      | some cm' => checkStepsWf cmEnd poolEnd (stepDadda pool c).1 cm' cs

theorem checkStepsWf_sound (cmEnd : List ℕ) (poolEnd : List DToken)
    (cs : List ℕ) (pool : List DToken) (cm : List ℕ)
    (hok : checkStepsWf cmEnd poolEnd pool cm cs = true) (γ1 γ : BitAssignment 304)
    (hinv : daddaInv pool cm γ1 γ) :
    let r := runDaddaList pool cs
    daddaInv r.1 cmEnd γ1 (r.2.fwdBits γ) ∧ r.1 = poolEnd := by
  induction cs generalizing pool cm γ with
  | nil =>
      simp only [checkStepsWf, Bool.and_eq_true, beq_iff_eq] at hok; exact ⟨hok.1 ▸ hinv, hok.2⟩
  | cons c cs ih =>
      dsimp only [checkStepsWf] at hok
      cases hwf : wfDaddaStep pool cm c <;> rw [hwf] at hok
      · exact Bool.noConfusion hok
      · exact ih _ _ hok _ (stepDadda_inv pool cm _ c hwf γ1 γ hinv)

attribute [local semireducible] StructuredCB.validProgMask StructuredCB.finalCleanMask

theorem step0_dual_prog_eq : (stepDadda initDualGlfa135 5171578885).2 =
    (stepDadda initTokens128 5171578885).2 := rfl
end QuantumComputation.Specs.PhotochemistrySolution.Dist18DualGlfaOpt
end


noncomputable section
namespace QuantumComputation.Specs.PhotochemistrySolution.WRouterCsaDual180
open Operator QProg Matrix Circuit Qubit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
open PhotochemistrySolution.WStateMux48
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB (ComputeProg ket matrix_ext_ket)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.XMeasUnld (ket_X ket_CNOT
    eval_seq_mulVec)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SplitRouter47_187 (idxValPrefix
    idxValPrefix_lt_two_pow)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.WStateRouterPrim (WInj wUncompTreeDyn
    mkVecOp mkVecOp_mulVec_ket subspaceStep_mul_right)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Stage2ElecOptA (WOptInj OptBasePred
    oneHotOptPreVec oneHotOptPreOp wLastSplitShiftDyn count_wLastSplitShiftDyn)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Stage2ElecOptA (dw_wLastSplitShiftDyn
    subspaceStep_wLastSplitShiftDyn count_wUncompTreeDyn_opt)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Stage2ElecOptA (dw_wUncompTreeDyn_opt
    subspaceStep_wUncompTreeDyn_id_opt)
open scoped Circuit.Notation
local instance : NeZero 2 := ⟨two_ne_zero⟩
/-! ### 1. Uniform `pSplit2Bracket` (`6 T`, `0 .TOFF`) and `XorOp56` Clifford Brackets -/

def pTrueSplit {n : ℕ} (_ : BitAssignment n) : Prop := True
instance instDecidablePTrueSplit {n : ℕ} : DecidablePred (@pTrueSplit n) := fun _ ↦ isTrue trivial

def actDumZero {n : ℕ} (rDum : Wire n) (δ : BitAssignment n) : Prop := δ rDum = 0
instance instDecidableActDumZero {n : ℕ} (rDum : Wire n) : DecidablePred (actDumZero rDum) :=
  fun δ ↦ inferInstanceAs (Decidable (δ rDum = 0))

def actExprOne {n : ℕ} (eAct : BitAssignment n → ZMod 2) (δ : BitAssignment n) : Prop := eAct δ = 1
instance instDecidableActExprOne {n : ℕ} (eAct : BitAssignment n → ZMod 2) :
    DecidablePred (actExprOne eAct) :=
  fun δ ↦ inferInstanceAs (Decidable (eAct δ = 1))

abbrev f1_0 : Fin 1 := ⟨0, by decide⟩
abbrev f2_0 : Fin 2 := ⟨0, by decide⟩
abbrev f2_1 : Fin 2 := ⟨1, by decide⟩
abbrev fp1_0 : Fin (2 ^ 1) := ⟨0, by decide⟩
abbrev fp1_1 : Fin (2 ^ 1) := ⟨1, by decide⟩

def bStarOfWire {n : ℕ} (bWire : Wire n) (δ : BitAssignment n) : Fin 2 :=
    if δ bWire = 1 then f2_1 else f2_0
abbrev wPair2 {n : ℕ} (l0 h0 l1 h1 : Wire n) (b : Fin 2) (p : Fin (2 ^ 1)) : Wire n :=
    if b.val = 0 then (if p.val = 0 then l0 else h0) else (if p.val = 0 then l1 else h1)
theorem wPair2_wInj {n : ℕ} {l0 h0 l1 h1 : Wire n} (h01 : l0 ≠ h0) (h02 : l0 ≠ l1) (h03 : l0 ≠ h1)
    (h12 : h0 ≠ l1) (h13 : h0 ≠ h1) (h23 : l1 ≠ h1) : WInj (wPair2 l0 h0 l1 h1) := by
  intro b1 p1 b2 p2 h
  have hb1 := b1.isLt
  have hb2 := b2.isLt
  have hp1 : p1.val < 2 := p1.isLt
  have hp2 : p2.val < 2 := p2.isLt
  unfold wPair2 at h
  split_ifs at h <;> first
    | exact ⟨Fin.ext (by omega), Fin.ext (by omega)⟩
    | exact absurd h (by assumption)
    | exact absurd h.symm (by assumption)

def cSplit2Pre {n : ℕ} (l0 l1 rDum : Wire n) (hl0 : l0 ≠ rDum) (hl1 : l1 ≠ rDum) : Circuit n :=
  Circuit.X rDum ;;ᶜ Circuit.CNOT l0 rDum hl0 ;;ᶜ Circuit.CNOT l1 rDum hl1

def cSplit2Post {n : ℕ} (l0 h0 l1 h1 rDum : Wire n) (hh1 : h1 ≠ rDum) (hl1 : l1 ≠ rDum)
    (hh0 : h0 ≠ rDum) (hl0 : l0 ≠ rDum) : Circuit n :=
  Circuit.CNOT h1 rDum hh1 ;;ᶜ Circuit.CNOT l1 rDum hl1 ;;ᶜ
    Circuit.CNOT h0 rDum hh0 ;;ᶜ Circuit.CNOT l0 rDum hl0 ;;ᶜ Circuit.X rDum

def pSplit2Bracket {Var : Type} {n : ℕ} (v : Var) (uWire l0 h0 l1 h1 rDum wDum qEnc : Wire n)
    (hInj : WOptInj 2 1 (fun _ : Fin 1 ↦ uWire) (wPair2 l0 h0 l1 h1) rDum wDum qEnc)
    (mid : DynamicCircuit Var n) : DynamicCircuit Var n :=
  let uLo1 : Fin 1 → Wire n := fun _ ↦ uWire
  let wP := wPair2 l0 h0 l1 h1
  (DynamicCircuit.circuit (cSplit2Pre l0 l1 rDum (hInj.w_ne_rDum f2_0 fp1_0)
      (hInj.w_ne_rDum f2_1 fp1_0))).seq
    ((wLastSplitShiftDyn v 2 0 uLo1 wP rDum wDum qEnc hInj).seq
      ((DynamicCircuit.circuit (cSplit2Post l0 h0 l1 h1 rDum
          (hInj.w_ne_rDum f2_1 fp1_1) (hInj.w_ne_rDum f2_1 fp1_0) (hInj.w_ne_rDum f2_0 fp1_1)
              (hInj.w_ne_rDum f2_0 fp1_0))).seq
        (mid.seq
          (wUncompTreeDyn v 2 1 uLo1 wP hInj.w_inj hInj.uLo_ne_w (.circuit .identity) 1 le_rfl))))

theorem counts_pSplit2Bracket {Var : Type} {n : ℕ} (v : Var)
    (uWire l0 h0 l1 h1 rDum wDum qEnc : Wire n) (hInj : WOptInj 2 1 (fun _ : Fin 1 ↦ uWire)
    (wPair2 l0 h0 l1 h1) rDum wDum qEnc) (mid : DynamicCircuit Var n) :
    (pSplit2Bracket v uWire l0 h0 l1 h1 rDum wDum qEnc hInj mid).count .T = 6 + mid.count .T ∧
        (pSplit2Bracket v uWire l0 h0 l1 h1 rDum wDum qEnc hInj mid).count .TOFF =
        mid.count .TOFF := by
  obtain ⟨tS, fS⟩ :=
      count_wLastSplitShiftDyn v 2 0 (fun _ ↦ uWire) (wPair2 l0 h0 l1 h1) rDum wDum qEnc hInj
  obtain ⟨tU, fU⟩ :=
      count_wUncompTreeDyn_opt v 2 1 (fun _ ↦ uWire)
      (wPair2 l0 h0 l1 h1) hInj.w_inj hInj.uLo_ne_w (.circuit .identity) 1 le_rfl
  dsimp only [DynamicCircuit.count] at tU fU
  dsimp only [pSplit2Bracket, DynamicCircuit.count]
  rw [tS, fS, tU, fU]
  constructor <;> simp [cSplit2Pre, cSplit2Post, Circuit.count_seq, Circuit.X, Circuit.CNOT]

theorem ctrlSafe_pSplit2Bracket {Var : Type} {n : ℕ} {S_ctrl S_tgt : Wire n → Prop} (v : Var)
    (uWire l0 h0 l1 h1 rDum wDum qEnc : Wire n)
    (hInj : WOptInj 2 1 (fun _ : Fin 1 ↦ uWire) (wPair2 l0 h0 l1 h1) rDum wDum qEnc)
        (mid : DynamicCircuit Var n)
    (hu : S_ctrl uWire ∧ S_tgt uWire) (hl0 : S_ctrl l0 ∧ S_tgt l0) (hh0 : S_ctrl h0 ∧ S_tgt h0)
        (hl1 : S_ctrl l1 ∧ S_tgt l1)
    (hh1 : S_ctrl h1 ∧ S_tgt h1) (hr : S_ctrl rDum ∧ S_tgt rDum) (hwd : S_ctrl wDum ∧ S_tgt wDum)
        (hq : S_ctrl qEnc ∧ S_tgt qEnc)
    (hMid : DynCtrlSafe S_ctrl S_tgt mid) :
        DynCtrlSafe S_ctrl S_tgt (pSplit2Bracket v uWire l0 h0 l1 h1 rDum wDum qEnc hInj mid) := by
  have hwP : ∀ b p, S_ctrl (wPair2 l0 h0 l1 h1 b p) ∧ S_tgt (wPair2 l0 h0 l1 h1 b p) := fun b p ↦ by
    dsimp only [wPair2]; split_ifs <;> assumption
  obtain ⟨_, fS⟩ :=
      count_wLastSplitShiftDyn v 2 0 (fun _ ↦ uWire) (wPair2 l0 h0 l1 h1) rDum wDum qEnc hInj
  obtain ⟨_, fU⟩ :=
      count_wUncompTreeDyn_opt v 2 1 (fun _ ↦ uWire)
      (wPair2 l0 h0 l1 h1) hInj.w_inj hInj.uLo_ne_w (.circuit .identity) 1 le_rfl
  exact .seq (.of_dynWires ⟨cw_1 hr, ⟨cw_cnot hl0 hr, cw_cnot hl1 hr⟩⟩
      (by simp [DynamicCircuit.count, cSplit2Pre, Circuit.X, Circuit.CNOT]))
    (.seq (.of_dynWires (dw_wLastSplitShiftDyn v 2 0 _ _ rDum wDum qEnc hInj (fun _ ↦
        hu) hwP hr hwd hq) fS)
      (.seq (.of_dynWires ⟨cw_cnot hh1 hr, ⟨cw_cnot hl1 hr, ⟨cw_cnot hh0 hr, ⟨cw_cnot hl0 hr,
          cw_1 hr⟩⟩⟩⟩ (by simp [DynamicCircuit.count, cSplit2Post, Circuit.X, Circuit.CNOT]))
        (.seq hMid (.of_dynWires (dw_wUncompTreeDyn_opt v 2 1 _ _ hInj.w_inj hInj.uLo_ne_w (fun _ ↦
            hu) hwP (rest := .circuit .identity) trivial 1 le_rfl) (fU.trans rfl)))))

def stSplit2Fwd {n : ℕ} (uWire l0 h0 l1 h1 : Wire n) (β : BitAssignment n) : BitAssignment n :=
    Function.update (Function.update (Function.update (Function.update β l0 (β l0 *
    (1 + β uWire))) h0 (β l0 * β uWire)) l1 (β l1 * (1 + β uWire))) h1 (β l1 * β uWire)
def stSplit2BasePre {n : ℕ} (l0 l1 rDum : Wire n) (β : BitAssignment n) : BitAssignment n :=
    Function.update (Function.update (Function.update β l0 0) l1 0) rDum (1 + β l0 + β l1)
def stSplit2Clear4 {n : ℕ} (l0 h0 l1 h1 : Wire n) (β : BitAssignment n) : BitAssignment n :=
    Function.update (Function.update (Function.update (Function.update β l0 0) h0 0) l1 0) h1 0
theorem ket_eq_of_eq_on5 {n : ℕ} {w0 w1 w2 w3 w4 : Wire n} {α β : BitAssignment n}
    (h0 : α w0 = β w0) (h1 : α w1 = β w1) (h2 : α w2 = β w2) (h3 : α w3 = β w3) (h4 : α w4 = β w4)
    (hOth : ∀ x, x ≠ w0 → x ≠ w1 → x ≠ w2 → x ≠ w3 → x ≠ w4 → α x = β x) : ket α = ket β :=
  congrArg ket <| funext fun x ↦
    (Classical.em (x = w0)).elim (fun e ↦ e ▸ h0) fun e0 ↦
        (Classical.em (x = w1)).elim (fun e ↦ e ▸ h1) fun e1 ↦
      (Classical.em (x = w2)).elim (fun e ↦ e ▸ h2) fun e2 ↦
          (Classical.em (x = w3)).elim (fun e ↦ e ▸ h3) fun e3 ↦
        (Classical.em (x = w4)).elim (fun e ↦ e ▸ h4) (hOth x e0 e1 e2 e3)

set_option maxHeartbeats 1600000 in
-- Large circuit/register elaboration requires raised heartbeat limit.
theorem step_pSplit2Bracket {Var : Type} [Fintype Var] [DecidableEq Var] {W n : ℕ} [NeZero (2 ^ n)]
    (v : Var) (rWork : QRegister W n) (uWire l0 h0 l1 h1 rDum wDum qEnc bWire : Wire n)
        (eAct : BitAssignment n → ZMod 2)
    (hInj : WOptInj 2 1 (fun _ : Fin 1 ↦ uWire) (wPair2 l0 h0 l1 h1) rDum wDum qEnc)
    (hbNe : bWire ≠ l0 ∧ bWire ≠ l1 ∧ bWire ≠ h0 ∧ bWire ≠ h1 ∧ bWire ≠ rDum)
    (heIndep : ∀ (β : BitAssignment n) (v0 v1 v2 v3 : ZMod 2),
        eAct (Function.update (Function.update (Function.update (Function.update β l0 v0) h0 v1) l1
        v2) h1 v3) = eAct β)
    (st stPost : BitAssignment n → BitAssignment n) (phPre phPost : BitAssignment n → ZMod 2)
        (mid : DynamicCircuit Var n)
    (hMut : ∀ δ, (∀ q, δ (rWork q) = 0) → st δ l0 * st δ l1 = 0)
    (hCln : ∀ δ, (∀ q, δ (rWork q) = 0) → st δ h0 = 0 ∧ st δ h1 = 0 ∧ st δ rDum = 0 ∧ st δ wDum =
        0 ∧ st δ qEnc = 0)
    (hbStar : ∀ δ, (∀ q, δ (rWork q) = 0) → (st δ l0 = 1 → st δ bWire = 0) ∧
        (st δ l1 = 1 → st δ bWire = 1))
    (heEq : ∀ δ, (∀ q, δ (rWork q) = 0) → eAct (st δ) = st δ l0 + st δ l1)
    (hSame : ∀ δ, (∀ q, δ (rWork q) = 0) → stPost δ uWire = st δ uWire ∧ stPost δ l0 = st δ l0 ∧
        stPost δ h0 = st δ h0 ∧
      stPost δ l1 = st δ l1 ∧ stPost δ h1 = st δ h1 ∧ stPost δ rDum = st δ rDum ∧ stPost δ wDum =
          st δ wDum ∧ stPost δ qEnc = st δ qEnc ∧ stPost δ bWire = st δ bWire ∧ eAct (stPost δ) =
          eAct (st δ))
    (hMid : SubspaceStep (mkKetOpW rWork (fun δ ↦ stSplit2Fwd uWire l0 h0 l1 h1 (st δ)) phPre)
        (mkKetOpW rWork (fun δ ↦ stSplit2Fwd uWire l0 h0 l1 h1 (stPost δ)) phPost) mid) :
    SubspaceStep (mkKetOpW rWork st phPre) (mkKetOpW rWork stPost phPost)
        (pSplit2Bracket v uWire l0 h0 l1 h1 rDum wDum qEnc hInj mid) := by
  let uLo1 : Fin 1 → Wire n := fun _ ↦ uWire
  let wP := wPair2 l0 h0 l1 h1
  have ne (b1 : Fin 2) (p1 : Fin (2 ^ 1)) (b2 : Fin 2) (p2 : Fin (2 ^ 1))
      (h : (b1, p1) ≠ (b2, p2)) :
      wP b1 p1 ≠ wP b2 p2 := fun eq ↦
          h (Prod.ext (hInj.w_inj b1 p1 b2 p2 eq).1 (hInj.w_inj b1 p1 b2 p2 eq).2)
  have ⟨hl0h0, hl0l1, hl0h1, hh0l1, hh0h1, hl1h1⟩ : l0 ≠ h0 ∧ l0 ≠ l1 ∧ l0 ≠ h1 ∧ h0 ≠ l1 ∧ h0 ≠
      h1 ∧ l1 ≠ h1 :=
    ⟨ne f2_0 fp1_0 f2_0 fp1_1 (by decide), ne f2_0 fp1_0 f2_1 fp1_0 (by decide),
        ne f2_0 fp1_0 f2_1 fp1_1 (by decide),
     ne f2_0 fp1_1 f2_1 fp1_0 (by decide), ne f2_0 fp1_1 f2_1 fp1_1 (by decide),
         ne f2_1 fp1_0 f2_1 fp1_1 (by decide)⟩
  have ⟨hl0r, hh0r, hl1r, hh1r⟩ : l0 ≠ rDum ∧ h0 ≠ rDum ∧ l1 ≠ rDum ∧ h1 ≠ rDum :=
    ⟨hInj.w_ne_rDum f2_0 fp1_0, hInj.w_ne_rDum f2_0 fp1_1, hInj.w_ne_rDum f2_1 fp1_0,
        hInj.w_ne_rDum f2_1 fp1_1⟩
  have ⟨hl0w, hh0w, hl1w, hh1w⟩ : l0 ≠ wDum ∧ h0 ≠ wDum ∧ l1 ≠ wDum ∧ h1 ≠ wDum :=
    ⟨hInj.w_ne_wDum f2_0 fp1_0, hInj.w_ne_wDum f2_0 fp1_1, hInj.w_ne_wDum f2_1 fp1_0,
        hInj.w_ne_wDum f2_1 fp1_1⟩
  have ⟨hl0q, hh0q, hl1q, hh1q⟩ : l0 ≠ qEnc ∧ h0 ≠ qEnc ∧ l1 ≠ qEnc ∧ h1 ≠ qEnc :=
    ⟨hInj.w_ne_qEnc f2_0 fp1_0, hInj.w_ne_qEnc f2_0 fp1_1, hInj.w_ne_qEnc f2_1 fp1_0,
        hInj.w_ne_qEnc f2_1 fp1_1⟩
  have ⟨hur, hul0, huh0, hul1, huh1⟩ : uWire ≠ rDum ∧ uWire ≠ l0 ∧ uWire ≠ h0 ∧ uWire ≠ l1 ∧ uWire ≠
      h1 :=
    ⟨hInj.uLo_ne_rDum f1_0, hInj.uLo_ne_w f1_0 f2_0 fp1_0, hInj.uLo_ne_w f1_0 f2_0 fp1_1,
     hInj.uLo_ne_w f1_0 f2_1 fp1_0, hInj.uLo_ne_w f1_0 f2_1 fp1_1⟩
  have hOptPre {γ : BitAssignment n} (hh0 : γ h0 = 0) (hh1 : γ h1 = 0) (hw : γ wDum = 0)
      (hq : γ qEnc = 0) :
      OptBasePred (@pTrueSplit n) wDum qEnc (stSplit2BasePre l0 l1 rDum γ) ∧
      ∀ b p, stSplit2BasePre l0 l1 rDum γ (wPair2 l0 h0 l1 h1 b p) = 0 := by
    refine ⟨⟨trivial,
        by simp [stSplit2BasePre, hInj.rDum_ne_wDum.symm, hl1w.symm, hl0w.symm, hw],
      by simp [stSplit2BasePre, hInj.rDum_ne_qEnc.symm, hl1q.symm, hl0q.symm, hq]⟩,
          fun b p ↦ ?_⟩
    dsimp only [wPair2, stSplit2BasePre]
    split_ifs <;> simp [hl0r, hh0r, hl1r, hh1r, hl0l1, hh0l1, hl0h0.symm, hl1h1.symm, hl0h1.symm,
        hh0, hh1]
  have hOptClr {γ : BitAssignment n} (hw : γ wDum = 0) (hq : γ qEnc = 0) :
      OptBasePred (@pTrueSplit n) wDum qEnc (stSplit2Clear4 l0 h0 l1 h1 γ) ∧
      ∀ b p, stSplit2Clear4 l0 h0 l1 h1 γ (wPair2 l0 h0 l1 h1 b p) = 0 := by
    refine ⟨⟨trivial,
        by simp [stSplit2Clear4, hh1w.symm, hl1w.symm, hh0w.symm, hl0w.symm, hw],
      by simp [stSplit2Clear4, hh1q.symm, hl1q.symm, hh0q.symm, hl0q.symm, hq]⟩,
          fun b p ↦ ?_⟩
    dsimp only [wPair2, stSplit2Clear4]
    split_ifs <;> simp [hl0h1, hl0l1, hl0h0, hh0h1, hh0l1, hl1h1]
  have op_eq {A B : Operator (2 ^ n)} {s1 s2 : BitAssignment n → BitAssignment n}
      {ph : BitAssignment n → ZMod 2}
      (h : ∀ δ, (∀ q, δ (rWork q) = 0) → A.mulVec (ket (s1 δ)) = B.mulVec (ket (s2 δ))) :
      A * mkKetOpW rWork s1 ph = B * mkKetOpW rWork s2 ph :=
    matrix_ext_ket fun δ ↦ by
      simp only [← Matrix.mulVec_mulVec, mkKetOpW_mulVec_ket]
      by_cases hz : ∀ q, δ (rWork q) = 0
      · rw [ite_eq_left hz, ite_eq_left hz, Matrix.mulVec_smul, Matrix.mulVec_smul, h δ hz]
      · rw [ite_eq_right hz, ite_eq_right hz, Matrix.mulVec_zero, Matrix.mulVec_zero]
  have hNo11 {δ : BitAssignment n} (hz : ∀ q, δ (rWork q) = 0) (h0 : st δ l0 = 1)
      (h1 : st δ l1 = 1) : False := by
    simpa [h0, h1] using hMut δ hz
  have hbS1 {δ : BitAssignment n} (hz : ∀ q, δ (rWork q) = 0) {β : BitAssignment n}
      (hb : β bWire = st δ bWire)
      (h1 : st δ l1 = 1) : bStarOfWire bWire β = f2_1 := by
        unfold bStarOfWire; rw [hb, (hbStar δ hz).2 h1]; simp
  have hbS0 {δ : BitAssignment n} (hz : ∀ q, δ (rWork q) = 0) {β : BitAssignment n}
      (hb : β bWire = st δ bWire)
      (h0 : st δ l0 = 1) : bStarOfWire bWire β = f2_0 := by
        unfold bStarOfWire; rw [hb, (hbStar δ hz).1 h0]; simp
  have hD00 {γ : BitAssignment n} (h0 : γ l0 = 0) (h1 : γ l1 = 0) :
      ¬ actDumZero rDum (stSplit2BasePre l0 l1 rDum γ) := by
        simp [stSplit2BasePre, actDumZero, h0, h1]
  have hD01 {γ : BitAssignment n} (h0 : γ l0 = 0) (h1 : γ l1 = 1) :
      actDumZero rDum (stSplit2BasePre l0 l1 rDum γ) := by
    simp [stSplit2BasePre, actDumZero, h0, h1, CharTwo.add_self_eq_zero]
  have hD10 {γ : BitAssignment n} (h0 : γ l0 = 1) (h1 : γ l1 = 0) :
      actDumZero rDum (stSplit2BasePre l0 l1 rDum γ) := by
    simp [stSplit2BasePre, actDumZero, h0, h1, CharTwo.add_self_eq_zero]
  have hS1 : (cSplit2Pre l0 l1 rDum hl0r hl1r).eval.1 * mkKetOpW rWork st phPre =
      oneHotOptPreOp (OptBasePred (@pTrueSplit n) wDum qEnc) (actDumZero rDum) (bStarOfWire bWire)
        uLo1 wP 0 (Nat.zero_le 1) * mkKetOpW rWork (fun δ ↦
            stSplit2BasePre l0 l1 rDum (st δ)) phPre :=
    op_eq fun δ hz ↦ by
      obtain ⟨hh0_0, hh1_0, hr_0, hw_0, hq_0⟩ := hCln δ hz
      dsimp only [cSplit2Pre, oneHotOptPreOp, oneHotOptPreVec]
      rw [eval_seq_mulVec, eval_seq_mulVec, ket_X, ket_CNOT, ket_CNOT, mkVecOp_mulVec_ket,
        ite_eq_left (hOptPre hh0_0 hh1_0 hw_0 hq_0)]
      set β0 := stSplit2BasePre l0 l1 rDum (st δ)
      have hbB : β0 bWire = st δ bWire := by
        simp [β0, stSplit2BasePre, hbNe.2.2.2.2, hbNe.2.1, hbNe.1]
      rcases DynCircExt.bit_cases (st δ l0) with hl0v | hl0v <;>
        rcases DynCircExt.bit_cases (st δ l1) with hl1v | hl1v <;>
        (first | exact (hNo11 hz hl0v hl1v).elim | rw [ite_eq_right (c := actDumZero rDum β0)
                                                     (hD00 hl0v hl1v)]
               | rw [ite_eq_left (c := actDumZero rDum β0) (hD01 hl0v hl1v), hbS1 hz hbB hl1v]
               | rw [ite_eq_left (c := actDumZero rDum β0) (hD10 hl0v hl1v), hbS0 hz hbB hl0v]) <;>
        (try dsimp only [wP, wPair2, f2_0, f2_1, idxValPrefix]) <;>
            (try simp only [↓reduceIte, Nat.one_ne_zero]) <;>
        refine ket_eq_of_eq_on5 (w0 := l0) (w1 := l1) (w2 := rDum) (w3 := rDum)
            (w4 := rDum) ?_ ?_ ?_ ?_ ?_
          (fun x n0 n1 n2 _ _ ↦ by simp [β0, stSplit2BasePre, n0, n1, n2]) <;>
        (simp [β0, stSplit2BasePre, hr_0, hl0v, hl1v, hl0r, hl0r.symm, hl1r, hl1r.symm, hl0l1,
            hl0l1.symm,
          CharTwo.add_self_eq_zero])
  have hS2 : (cSplit2Post l0 h0 l1 h1 rDum hh1r hl1r hh0r hl0r).eval.1 *
      (oneHotOptPreOp (OptBasePred (@pTrueSplit n) wDum qEnc) (actDumZero rDum) (bStarOfWire bWire)
        uLo1 wP 1 le_rfl * mkKetOpW rWork (fun δ ↦ stSplit2BasePre l0 l1 rDum (st δ)) phPre) =
      mkKetOpW rWork (fun δ ↦ stSplit2Fwd uWire l0 h0 l1 h1 (st δ)) phPre :=
    (Matrix.mul_assoc _ _ _).symm.trans ((op_eq (B := 1) fun δ hz ↦ by
      rw [← Matrix.mulVec_mulVec, Matrix.one_mulVec]
      obtain ⟨hh0_0, hh1_0, hr_0, hw_0, hq_0⟩ := hCln δ hz
      dsimp only [oneHotOptPreOp, oneHotOptPreVec]
      rw [mkVecOp_mulVec_ket, ite_eq_left (hOptPre hh0_0 hh1_0 hw_0 hq_0)]
      set β0 := stSplit2BasePre l0 l1 rDum (st δ)
      have hbB : β0 bWire = st δ bWire := by
        simp [β0, stSplit2BasePre, hbNe.2.2.2.2, hbNe.2.1, hbNe.1]
      have evalPost (γ : BitAssignment n) :
          (cSplit2Post l0 h0 l1 h1 rDum hh1r hl1r hh0r hl0r).eval.1.mulVec (ket γ) =
          ket (Function.update γ rDum (γ rDum + γ h1 + γ l1 + γ h0 + γ l0 + 1)) := by
        rw [cSplit2Post, eval_seq_mulVec, eval_seq_mulVec, eval_seq_mulVec, eval_seq_mulVec,
          ket_CNOT, ket_CNOT, ket_CNOT, ket_CNOT, ket_X]
        exact congrArg ket <| funext fun x ↦ by
          by_cases hx : x = rDum <;> simp [hx, hl1r, hh0r, hl0r]
      rcases DynCircExt.bit_cases (st δ l0) with hl0v | hl0v <;>
        rcases DynCircExt.bit_cases (st δ l1) with hl1v | hl1v <;>
        (first | exact (hNo11 hz hl0v hl1v).elim | rw [ite_eq_right (c := actDumZero rDum β0)
                                                     (hD00 hl0v hl1v)]
               | rw [ite_eq_left (c := actDumZero rDum β0) (hD01 hl0v hl1v), hbS1 hz hbB hl1v]
               | rw [ite_eq_left (c := actDumZero rDum β0) (hD10 hl0v hl1v), hbS0 hz hbB hl0v]) <;>
        rw [evalPost] <;> rcases DynCircExt.bit_cases (st δ uWire) with huv | huv <;>
        refine ket_eq_of_eq_on5 (w0 := h1) (w1 := l1) (w2 := h0) (w3 := l0)
            (w4 := rDum) ?_ ?_ ?_ ?_ ?_
          (fun x n0 n1 n2 n3 n4 ↦ by
            simp [wP, wPair2, f2_0, f2_1, idxValPrefix, uLo1, stSplit2Fwd, β0, stSplit2BasePre,
              hur, hul1, hul0, huv, n0, n1, n2, n3, n4]) <;>
        (simp [wP, wPair2, f2_0, f2_1, idxValPrefix, uLo1, stSplit2Fwd, β0, stSplit2BasePre, hur,
            hul1, hul0,
          hh1r, hl1r, hh0r, hl0r, hh1r.symm, hl1r.symm, hh0r.symm, hl0r.symm, hl1h1, hl1h1.symm,
              hl0h1, hl0h1.symm,
          hh0h1, hh0h1.symm, hh0l1, hh0l1.symm, hl0h0, hl0h0.symm, hl0l1, hl0l1.symm,
          hh1_0, hh0_0, hr_0, hl0v, hl1v, huv, CharTwo.add_self_eq_zero])).trans (Matrix.one_mul _))
  have hClrVec (k : ℕ) (hk : k ≤ 1) (δ : BitAssignment n) (hz : ∀ q, δ (rWork q) = 0) :
      (oneHotOptPreOp (OptBasePred (@pTrueSplit n) wDum qEnc) (actExprOne eAct) (bStarOfWire bWire)
        uLo1 wP k hk).mulVec (ket (stSplit2Clear4 l0 h0 l1 h1 (stPost δ))) =
      ket (if k = 0 then stPost δ else stSplit2Fwd uWire l0 h0 l1 h1 (stPost δ)) := by
    obtain ⟨su, sl0, sh0, sl1, sh1, _, sw, sq, sb, se⟩ := hSame δ hz
    obtain ⟨hh0_0, hh1_0, _, hw_0, hq_0⟩ := hCln δ hz
    dsimp only [oneHotOptPreOp, oneHotOptPreVec]
    rw [mkVecOp_mulVec_ket, ite_eq_left (hOptClr (sw.trans hw_0) (sq.trans hq_0))]
    set βc := stSplit2Clear4 l0 h0 l1 h1 (stPost δ)
    have heC : eAct βc = st δ l0 + st δ l1 :=
        (heIndep (stPost δ) 0 0 0 0).trans (se.trans (heEq δ hz))
    have hbC : βc bWire = st δ bWire := by
      simp [βc, stSplit2Clear4, hbNe.2.2.2.1, hbNe.2.1, hbNe.2.2.1, hbNe.1, sb]
    have hE00 (h0 : st δ l0 = 0) (h1 : st δ l1 = 0) : ¬ actExprOne eAct βc := by
      simp [actExprOne, heC, h0, h1]
    have hE01 (h0 : st δ l0 = 0) (h1 : st δ l1 = 1) : actExprOne eAct βc := by
      simp [actExprOne, heC, h0, h1]
    have hE10 (h0 : st δ l0 = 1) (h1 : st δ l1 = 0) : actExprOne eAct βc := by
      simp [actExprOne, heC, h0, h1]
    rcases (show k = 0 ∨ k = 1 by omega) with rfl | rfl <;>
        (try simp only [↓reduceIte, Nat.one_ne_zero]) <;>
      rcases DynCircExt.bit_cases (st δ l0) with hl0v | hl0v <;>
      rcases DynCircExt.bit_cases (st δ l1) with hl1v | hl1v <;>
      (first | exact (hNo11 hz hl0v hl1v).elim | rw [ite_eq_right (hE00 hl0v hl1v)]
             | rw [ite_eq_left (hE01 hl0v hl1v), hbS1 hz hbC hl1v]
             | rw [ite_eq_left (hE10 hl0v hl1v), hbS0 hz hbC hl0v]) <;>
      rcases DynCircExt.bit_cases (st δ uWire) with huv | huv <;>
      refine ket_eq_of_eq_on5 (w0 := h1) (w1 := l1) (w2 := h0) (w3 := l0) (w4 := l0) ?_ ?_ ?_ ?_ ?_
        (fun x n0 n1 n2 n3 _ ↦ by
          simp [wP, wPair2, f2_0, f2_1, idxValPrefix, uLo1, stSplit2Fwd, βc, stSplit2Clear4,
            huh1, hul1, huh0, hul0, su, huv, n0, n1, n2, n3]) <;>
      (simp [wP, wPair2, f2_0, f2_1, idxValPrefix, uLo1, stSplit2Fwd, βc, stSplit2Clear4, huh1,
          hul1, huh0, hul0,
        sl0, sl1, su, sh0.trans hh0_0, sh1.trans hh1_0, hl0v, hl1v, huv, hl1h1, hl1h1.symm, hl0h1,
            hl0h1.symm,
        hh0h1, hh0h1.symm, hh0l1, hh0l1.symm, hl0h0, hl0h0.symm, hl0l1, hl0l1.symm,
        CharTwo.add_self_eq_zero])
  have hS3 : mkKetOpW rWork (fun δ ↦ stSplit2Fwd uWire l0 h0 l1 h1 (stPost δ)) phPost =
      oneHotOptPreOp (OptBasePred (@pTrueSplit n) wDum qEnc) (actExprOne eAct) (bStarOfWire bWire)
        uLo1 wP 1 le_rfl * mkKetOpW rWork (fun δ ↦ stSplit2Clear4 l0 h0 l1 h1 (stPost δ)) phPost :=
    (Matrix.one_mul _).symm.trans (op_eq (A := 1) fun δ hz ↦
        (Matrix.one_mulVec _).trans (hClrVec 1 le_rfl δ hz).symm)
  have hK4 : oneHotOptPreOp (OptBasePred (@pTrueSplit n) wDum qEnc) (actExprOne eAct)
      (bStarOfWire bWire)
      uLo1 wP 0 (Nat.zero_le 1) * mkKetOpW rWork (fun δ ↦
          stSplit2Clear4 l0 h0 l1 h1 (stPost δ)) phPost =
      mkKetOpW rWork stPost phPost :=
    (op_eq (B := 1) fun δ hz ↦
        (hClrVec 0 (by decide) δ hz).trans (Matrix.one_mulVec _).symm).trans (Matrix.one_mul _)
  dsimp only [pSplit2Bracket]
  exact (subspaceStep_congr_out (subspaceStep_of_circuit (Var := Var)
      (mkKetOpW rWork st phPre) _) hS1).seq
    ((subspaceStep_mul_right (mkKetOpW rWork (fun δ ↦ stSplit2BasePre l0 l1 rDum (st δ)) phPre)
      (subspaceStep_wLastSplitShiftDyn v pTrueSplit (actDumZero rDum)
          (bStarOfWire bWire) uLo1 wP rDum wDum qEnc hInj
        (fun γ _ ↦
            by rcases DynCircExt.bit_cases (γ rDum) with h | h <;> simp [actDumZero, h]))).seq
    ((subspaceStep_congr_out (subspaceStep_of_circuit (Var := Var) _ _) hS2).seq
    (hMid.seq (subspaceStep_congr_in hS3
      (subspaceStep_congr_out (subspaceStep_mul_right
          (mkKetOpW rWork (fun δ ↦ stSplit2Clear4 l0 h0 l1 h1 (stPost δ)) phPost)
          (subspaceStep_wUncompTreeDyn_id_opt v (OptBasePred (@pTrueSplit n) wDum qEnc)
              (actExprOne eAct)
            (bStarOfWire bWire) uLo1 wP hInj.w_inj hInj.uLo_ne_w)) hK4)))))
/-! ### 1b. Generic `XorOp56` Clifford Brackets & `liftSt56` -/

inductive XorOp56 where
  | x (q : Fin 56)
  | cnot (c tg : Fin 56)

def applyXorOp56 (op : XorOp56) (f : BitAssignment 56) : BitAssignment 56 :=
  match op with
  | .x q => Function.update f q (f q + 1)
  | .cnot c tg => if c = tg then f else Function.update f tg (f tg + f c)

def applyXorOps56 : List XorOp56 → BitAssignment 56 → BitAssignment 56
  | [], f => f
  | op :: rest, f => applyXorOps56 rest (applyXorOp56 op f)

theorem applyXorOp56_invol (op : XorOp56) (f : BitAssignment 56) :
    applyXorOp56 op (applyXorOp56 op f) = f := by
  cases op with
  | x q =>
      exact funext fun u ↦ by
        by_cases hu : u = q <;> simp [applyXorOp56, hu, add_assoc, CharTwo.add_self_eq_zero]
  | cnot c tg =>
      dsimp [applyXorOp56]
      split_ifs with hct
      · rfl
      · exact funext fun u ↦ by
          by_cases hu : u = tg <;> simp [hu, Function.update_of_ne hct, add_assoc,
              CharTwo.add_self_eq_zero]

def Distinct5_56 (uIdx l0 h0 l1 h1 : Fin 56) : Prop :=
    uIdx ≠ l0 ∧ uIdx ≠ h0 ∧ uIdx ≠ l1 ∧ uIdx ≠ h1 ∧ l0 ≠ h0 ∧ l0 ≠ l1 ∧ l0 ≠ h1 ∧ h0 ≠ l1 ∧ h0 ≠
    h1 ∧ l1 ≠ h1
instance instDecidableDistinct5_56 (uIdx l0 h0 l1 h1 : Fin 56) :
    Decidable (Distinct5_56 uIdx l0 h0 l1 h1) := by unfold Distinct5_56; infer_instance
open PhotochemistrySolution.Sh14P5Mux17 PhotochemistrySolution.ShortBin7Pre6ZHi30
  PhotochemistrySolution.ReflStage4 PhotochemistrySolution.MuxSum34Opt
open PhotochemistrySolution.PotSelectWiring PhotochemistrySolution.ZeroNEremAxisSq18
  PhotochemistrySolution.ZeroNEremCsa36Kick
open PhotochemistrySolution.CtrlSafeOracleBase.Legs
open _root_.QuantumComputation.Specs.PhotochemistrySolution.ShortBin7 (packBits packBits_lt
    packBits_testBit mkCT getCT_mkCT repMask repMask_testBit evalCTW evalCTW_sound)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.ShortBin7 (zmod2_eq_of_beq_one)
/-! ### 2. `treeFront5_22`, `treeBack16_52`, and `4096`-Column `CT` Certificate -/
def sMaskFront5_22 : ℕ := 4063232

def treeFront5_22 : PrimTree :=
    (pN (pN (p3 18473 17844246 18473) (p4 10309 32 18890774 32)) (pN (p4 10309 28 19937354 28)
    (p4 20983886 5 22026242 5)))
def sMaskBack16_52 : ℕ := 1125882726973440

def treeBack16_52 : PrimTree :=
    (pN (pN (pN (pN (pN (pN (pN (p6 102405 102477 102485 104453 104457 104525)
    (p6 104529 35756234 102401 102409 102473 102489))
    (pN (p6 102525 104453 104533 36804810 102401 102409) (pN (p3 102477 102489 102513)
    (p4 102529 102517 102541 104453)))) (pN (pN (p6 104521 104525 104533 104537 104541 104565)
    (pN (p3 104581 37853386 102405) (p4 102489 102513 102521 102517)))
    (pN (p6 102525 102541 104449 104529 104537 104541) (pN (p3 104569 104565 104585)
    (p4 104593 38901962 102401 102409)))))
    (pN (pN (pN (p6 102473 102485 102493 102521 102525 102533)
    (p6 102537 102541 102545 102549 104453 104525))
    (pN (p6 104529 104533 104561 104581 104585 104589) (pN (p3 104593 39950538 102405)
    (p4 102481 102521 102529 102517)))) (pN (pN (p6 102537 102549 104521 104537 104577 104565)
    (pN (p3 104585 104589 104597) (p4 104601 40999114 102405 102409)))
    (pN (p6 102421 102473 102477 102481 102493 102497) (pN (p3 102513 102521 102501)
    (p4 102517 102533 102537 102545))))))
    (pN (pN (pN (pN (p6 102557 104521 104529 104537 104541 104545)
    (p6 104549 104565 104581 104585 104589 104593))
    (pN (p6 104597 42047690 102401 102409 102421 102477) (pN (p3 102497 102521 102529)
    (p4 102501 102533 102537 102541)))) (pN (pN (p6 102545 102549 102553 102557 102561 104449)
    (pN (p3 104469 104517 104521) (p4 104529 104533 104537 104541)))
    (pN (p6 104561 104577 104573 104589 104601 43096266) (pN (p3 102409 102473 102477)
    (p4 102485 102489 102497 102513))))) (pN (pN (pN (p6 102521 102501 102517 102525 102533 102537)
    (p6 102541 102549 102553 102565 104453 104457))
    (pN (p6 104469 104517 104521 104525 104529 104541) (pN (p3 104545 104561 104569)
    (p4 104577 104549 104581 104585)))) (pN (pN (p6 104589 104593 104597 104601 104609 44144842)
    (pN (p3 102401 102405 102409) (p4 102477 102493 102525 102537)))
    (pN (p6 102541 102557 102561 102569 104453 104469) (pN (p3 104517 104521 104537)
    (p4 104553 104557 104565 104573)))))))
    (pN (pN (pN (pN (pN (p6 104601 104605 104613 45193418 102401 102473)
    (p6 102477 102481 102485 102497 102513 102529))
    (pN (p6 102501 102517 102525 102537 102541 102561) (pN (p3 104453 104457 104469)
    (p4 104517 104521 104525 104533)))) (pN (pN (p6 104541 104553 104561 104577 104557 104573)
    (pN (p3 104581 104585 104589) (p4 104593 104601 104609 104621)))
    (pN (p6 46241994 102405 102473 102481 102485 102497) (pN (p3 102513 102521 102501)
    (p4 102517 102533 102537 102541))))) (pN
  (pN (pN (p6 102545 102553 102561 102565 104453 104525)
      (p6 104533 104541 104565 104573 104581 104589))
      (pN (p6 104597 104613 104625 47290570 102401 102405) (pN (p3 102473 102481 102513)
      (p4 102529 102517 102533 102545)))) (pN (pN (p6 102581 104453 104517 104521 104529 104533)
      (pN (p3 104541 104545 104561) (p4 104569 104577 104549 104597)))
      (pN (p6 104601 104605 104613 104617 104621 104625) (pN (p3 48339146 102401 102409)
      (p4 102473 102481 102521 102529))))))
      (pN (pN (pN (pN (p6 102533 102545 104457 104517 104529 104533)
      (p6 104545 104553 104561 104577 104549 104557))
      (pN (p6 104589 104605 104609 104613 104625 104633) (pN (p3 49387722 102405 102477)
      (p4 102481 102493 102497 102505)))) (pN (pN (p6 102513 102529 102501 102509 102517 102533)
      (pN (p3 102537 102541 102549) (p4 102553 102557 102565 102573)))
      (pN (p6 102581 102585 104457 104469 104517 104525) (pN (p3 104529 104545 104553)
      (p4 104569 104577 104549 104557)))))
      (pN (pN (pN (p6 104573 104613 104617 104621 104625 104633)
      (p6 104637 50436298 102405 102409 102477 102485))
      (pN (p6 102489 102497 102521 102501 102517 102525) (pN (p3 102533 102541 102553)
      (p4 102557 102569 102581 104453)))) (pN (pN (p6 104457 104517 104521 104525 104529 104533)
      (pN (p3 104545 104561 104569) (p4 104549 104565 104573 104581)))
      (pN (p6 104585 104589 104597 104601 104609 104613) (pN (p3 104617 104621 104637)
      (p4 104641 51484874 102405 102409))))))))
      (pN (pN (pN (pN (pN (pN (p6 102477 102481 102489 102497 102505 102521)
      (p6 102529 102501 102509 102525 102533 102537))
      (pN (p6 102549 102553 102557 102565 102573 102581) (pN (p3 102585 104469 104521)
      (p4 104533 104561 104569 104577)))) (pN (pN (p6 104565 104581 104585 104589 104593 104601)
      (pN (p3 104605 104617 104641) (p4 100557 98509 96461 92365)))
      (pN (p6 84173 78029 75981 104649 100553 98505) (pN (p3 96457 86217 80073)
      (p4 78025 75977 102605 98501))))) (pN (pN (pN (p6 82117 80069 104641 94401 92353 90305)
      (p6 88257 86209 80065 67777 98509 102589)) (pN (p6 94397 92349 90301 78013 75965 67773)
      (pN (p3 96457 104633 100537) (p4 98489 96441 90297 88249))))
      (pN (pN (p6 80057 78009 73913 67769 94397 98485) (pN (p3 90293 84149 82101)
      (p4 80053 78005 75957 104625))) (pN (p6 98481 80049 67761 90305 96429 92333)
      (pN (p3 90285 86189 77997) (p4 73901 104617 100521 98473))))))
      (pN (pN (pN (pN (p6 96425 94377 88233 82089 75945 73897)
      (p6 67753 102565 98469 96421 94373 92325)) (pN (p6 90277
  88229 86181 82085 75941 73893) (pN (p3 67749 98465 90273) (p4 80033 82097 102557 98461))))
      (pN (pN (p6 96413 90269 88221 86173 77981 75933) (pN (p3 67741 80041 102553)
      (p4 98457 90265 88217 86169))) (pN (p6 82073 73881 69785 63641 59545 104597)
      (pN (p3 98453 96405 94357) (p4 90261 84117 80021 77973)))))
      (pN (pN (pN (p6 69781 67733 63637 59541 75929 104593)
      (p6 102545 100497 94353 92305 82065 80017)) (pN (p6 69777 67729 65681 57489 49297 47249)
      (pN (p3 45201 102541 100493) (p4 98445 94349 90253 84109))))
      (pN (pN (p6 82061 80013 77965 73869 69773 67725) (pN (p3 63629 59533 71825)
      (p4 102537 98441 96393 94345))) (pN (p6 92297 90249 88201 84105 80009 75913)
      (pN (p3 71817 67721 69773) (p4 102533 98437 92293 90245)))))))
      (pN (pN (pN (pN (pN (p6 88197 82053 77957 67737 92285 90237)
      (p6 86141 82045 77949 75901 73853 71805)) (pN (p6 67709 63621 104565 96373 84085 82037)
      (pN (p3 77941 75893 73845) (p4 63605 55413 104557 102509))))
      (pN (pN (p6 96365 94317 90221 88173 84077 82029) (pN (p3 79981 75885 73837)
      (p4 69741 59501 51309 65645))) (pN (p6 61549 57453 49261 47213 45165 100453)
      (pN (p3 92261 88165 55397) (p4 51309 100481 98433 82049)))))
      (pN (pN (pN (p6 77953 69761 65673 104569 102521 98425)
      (p6 96377 94329 92281 90233 84089 79993)) (pN (p6 77945 75897 73849 51321 65657 57465)
      (pN (p3 53369 49273 47225) (p4 45177 104561 102513 100465))))
      (pN (pN (p6 96369 84081 77937 65649 57473 104553) (pN (p3 92265 84073 82025)
      (p4 77929 75881 61545 57449))) (pN (p6 49257 45161 53361 100449 92257 88161)
      (pN (p3 57441 49265 104541) (p4 102493 100445 92253 90205))))))
      (pN (pN (pN (pN (p6 88157 86109 82013 75869 73821 71773)
      (p6 53341 49245 45149 43101 41053 36957)) (pN (p6 102489 96345 94297 92249 90201 88153)
      (pN (p3 86105 84057 79961) (p4 75865 49241 47193 43097))))
      (pN (pN (p6 36953 45149 100437 96341 88149 86101) (pN (p3 82005 77909 47189)
      (p4 43101 98385 96337 92241))) (pN (p6 90193 86097 82001 77905 45137 43089)
      (pN (p3 38993 36945 34897) (p4 104525 102477 100429 98381)))))
      (pN (pN (pN (p6 96333 92237 90189 88141 86093 79949)
      (p6 75853 71757 41037 34893 104521 98377)) (pN (p6 96329 94281 92233 90185 86089 84041)
      (pN (p3 81993 79945 43081) (p4 41029 34897 36865 38921))))
      (pN (pN (p6 69633 69641 73729 73737 75777 75781) (pN (p3 77833 81925 81929)
      (p4 83969 86017 88069 88073))) (pN (p6 92161 92165 94217 96257 96265 98313)
      (pN (p3 100357 102401 102405) (p4 102409 104449 104453
  104457)))))))))
def cpFront5_22 : ComputeProg 22 := decodePrimTree 21 treeFront5_22
def cpBack16_52 : ComputeProg 52 := decodePrimTree 51 treeBack16_52

theorem checkFront5_22_eq : checkPrimTree18S 21 0 sMaskFront5_22 treeFront5_22 = (true, 0, 5) := by
  decide +kernel
theorem checkBack16_52_eq : checkPrimTree18S 51 0 sMaskBack16_52 treeBack16_52 = (true, 0, 16) := by
  decide +kernel
theorem cpFront5_22_vp : StructuredCB.validProgMask 0 sMaskFront5_22 cpFront5_22 = true := by
  have hc :=
      (checkPrimTree18S_eq 21 0 treeFront5_22 sMaskFront5_22).symm.trans checkFront5_22_eq; exact
      (decodePrimTree_spec 21 treeFront5_22 0 sMaskFront5_22).1.trans (congrArg Prod.fst hc)
theorem cpFront5_22_and : cpFront5_22.numAnd = 5 := by
  have hc := (checkPrimTree18S_eq 21 0 treeFront5_22 sMaskFront5_22).symm.trans checkFront5_22_eq
  exact (decodePrimTree_spec 21 treeFront5_22 0 sMaskFront5_22).2.2.trans (congrArg (fun x ↦
      x.2.2) hc)

theorem cpBack16_52_vp : StructuredCB.validProgMask 0 sMaskBack16_52 cpBack16_52 = true := by
  have hc :=
      (checkPrimTree18S_eq 51 0 treeBack16_52 sMaskBack16_52).symm.trans checkBack16_52_eq; exact
      (decodePrimTree_spec 51 treeBack16_52 0 sMaskBack16_52).1.trans (congrArg Prod.fst hc)
theorem cpBack16_52_and : cpBack16_52.numAnd = 16 := by
  have hc := (checkPrimTree18S_eq 51 0 treeBack16_52 sMaskBack16_52).symm.trans checkBack16_52_eq
  exact (decodePrimTree_spec 51 treeBack16_52 0 sMaskBack16_52).2.2.trans (congrArg (fun x ↦
      x.2.2) hc)

theorem sMaskFront5_22_ge17 (u : Wire 22) (hu : sMaskFront5_22.testBit u.val = true) : 17 ≤
    u.val := by have := u.isLt; revert u; decide
theorem sMaskBack16_52_ge34 (u : Wire 52) (hu : sMaskBack16_52.testBit u.val = true) : 34 ≤
    u.val := by have := u.isLt; revert u; decide
def idx52To56 (v : Fin 52) : Fin 56 :=
  ⟨if v.val < 22 then v.val else if v.val < 24 then v.val + 2 else v.val + 4,
   by have := v.isLt; split_ifs <;> omega⟩

def opsInitA : List XorOp56 :=
  [.cnot ⟨0, by decide⟩ ⟨22, by decide⟩,
   .cnot ⟨1, by decide⟩ ⟨22, by decide⟩,
   .cnot ⟨21, by decide⟩ ⟨22, by decide⟩,
   .cnot ⟨21, by decide⟩ ⟨23, by decide⟩]

def opsPostA : List XorOp56 :=
  [.cnot ⟨25, by decide⟩ ⟨24, by decide⟩]

def opsPreSplits04 : List XorOp56 :=
  [.cnot ⟨16, by decide⟩ ⟨15, by decide⟩,
   .x ⟨15, by decide⟩,
   .x ⟨14, by decide⟩,
   .x ⟨13, by decide⟩,
   .cnot ⟨1, by decide⟩ ⟨26, by decide⟩,
   .cnot ⟨2, by decide⟩ ⟨26, by decide⟩,
   .cnot ⟨2, by decide⟩ ⟨27, by decide⟩]

def opsPostSplits04 : List XorOp56 :=
  [.x ⟨13, by decide⟩,
   .x ⟨14, by decide⟩,
   .x ⟨15, by decide⟩,
   .cnot ⟨16, by decide⟩ ⟨15, by decide⟩,
   .cnot ⟨36, by decide⟩ ⟨34, by decide⟩,
   .cnot ⟨34, by decide⟩ ⟨32, by decide⟩,
   .cnot ⟨32, by decide⟩ ⟨30, by decide⟩,
   .cnot ⟨30, by decide⟩ ⟨28, by decide⟩,
   .cnot ⟨37, by decide⟩ ⟨35, by decide⟩,
   .cnot ⟨35, by decide⟩ ⟨33, by decide⟩,
   .cnot ⟨33, by decide⟩ ⟨31, by decide⟩,
   .cnot ⟨31, by decide⟩ ⟨29, by decide⟩,
   .cnot ⟨29, by decide⟩ ⟨28, by decide⟩,
   .cnot ⟨31, by decide⟩ ⟨30, by decide⟩,
   .cnot ⟨33, by decide⟩ ⟨32, by decide⟩,
   .cnot ⟨35, by decide⟩ ⟨34, by decide⟩,
   .cnot ⟨37, by decide⟩ ⟨36, by decide⟩]

def f56Front (x : BitAssignment 56) (u : Fin 56) : ZMod 2 :=
  if h : u.val < 22 then cpFront5_22.fwdBits (fun j : Fin 22 ↦ x ⟨j.val, by omega⟩)
      ⟨u.val, h⟩ else x u

def f56PreSplitA (x : BitAssignment 56) : BitAssignment 56 := applyXorOps56 opsInitA (f56Front x)
def f56PostSplitA (x : BitAssignment 56) : BitAssignment 56 :=
  stSplit2Fwd ⟨4, by decide⟩ ⟨22, by decide⟩ ⟨24, by decide⟩ ⟨23, by decide⟩ ⟨25, by decide⟩
      (f56PreSplitA x)

def f56PostA (x : BitAssignment 56) : BitAssignment 56 := applyXorOps56 opsPostA (f56PostSplitA x)
def f56PreSplit0 (x : BitAssignment 56) : BitAssignment 56 :=
    applyXorOps56 opsPreSplits04 (f56PostA x)
def f56PreSplit1 (x : BitAssignment 56) : BitAssignment 56 :=
  stSplit2Fwd ⟨11, by decide⟩ ⟨26, by decide⟩ ⟨28, by decide⟩ ⟨27, by decide⟩ ⟨29, by decide⟩
      (f56PreSplit0 x)

def f56PreSplit2 (x : BitAssignment 56) : BitAssignment 56 :=
  stSplit2Fwd ⟨15, by decide⟩ ⟨28, by decide⟩ ⟨30, by decide⟩ ⟨29, by decide⟩ ⟨31, by decide⟩
      (f56PreSplit1 x)

def f56PreSplit3 (x : BitAssignment 56) : BitAssignment 56 :=
  stSplit2Fwd ⟨14, by decide⟩ ⟨30, by decide⟩ ⟨32, by decide⟩ ⟨31, by decide⟩ ⟨33, by decide⟩
      (f56PreSplit2 x)

def f56PreSplit4 (x : BitAssignment 56) : BitAssignment 56 :=
  stSplit2Fwd ⟨13, by decide⟩ ⟨32, by decide⟩ ⟨34, by decide⟩ ⟨33, by decide⟩ ⟨35, by decide⟩
      (f56PreSplit3 x)

def f56PostSplit4 (x : BitAssignment 56) : BitAssignment 56 :=
  stSplit2Fwd ⟨12, by decide⟩ ⟨34, by decide⟩ ⟨36, by decide⟩ ⟨35, by decide⟩ ⟨37, by decide⟩
      (f56PreSplit4 x)

def f56PreBack (x : BitAssignment 56) : BitAssignment 56 :=
    applyXorOps56 opsPostSplits04 (f56PostSplit4 x)
def setCT7 (ct : CT) (w val : ℕ) : CT := xorCT 7 ct w (getCT 7 ct w ^^^ val)
theorem getCT_setCT7 (ct : CT) (u w val : ℕ) (hu : u < 128)
    (hw : w < 128) : getCT 7 (setCT7 ct w val) u = if w = u then val else getCT 7 ct u := by
  dsimp [setCT7]
  rw [getCT_xorCT 7 ct u w _ (by norm_num; omega) (by norm_num; omega)]
  split_ifs with h
  · subst h
    exact Nat.eq_of_testBit_eq fun k ↦ by
      rw [Nat.testBit_xor, Nat.testBit_xor]; cases (getCT 7 ct w).testBit k <;>
          cases val.testBit k <;> rfl
  · rfl

def applyXorOp56CT (m12 : ℕ) (op : XorOp56) (ct : CT) : CT :=
  match op with
  | .x q => xorCT 7 ct q.val m12
  | .cnot c tg => if c = tg then ct else xorCT 7 ct tg.val (getCT 7 ct c.val)

def applyXorOps56CT (m12 : ℕ) : List XorOp56 → CT → CT
  | [], ct => ct
  | op :: rest, ct => applyXorOps56CT m12 rest (applyXorOp56CT m12 op ct)

def split2Fwd56CT (m12 : ℕ) (uIdx l0 h0 l1 h1 : Fin 56) (ct : CT) : CT :=
  let cu := getCT 7 ct uIdx.val
  let cuBar := cu ^^^ m12
  let cl0 := getCT 7 ct l0.val
  let cl1 := getCT 7 ct l1.val
  setCT7 (setCT7 (setCT7 (setCT7 ct l0.val (cl0 &&& cuBar)) h0.val (cl0 &&& cu))
    l1.val (cl1 &&& cuBar)) h1.val (cl1 &&& cu)

def ct56Front (hi : ℕ) : CT := evalCTW (repMask 12) 21 (initMuxSumCT hi) treeFront5_22
def ct56AfterSplitA (hi : ℕ) : CT :=
  let m12 := repMask 12
  let c1 := applyXorOps56CT m12 opsInitA (ct56Front hi)
  let c2 := split2Fwd56CT m12 ⟨4, by decide⟩ ⟨22, by decide⟩ ⟨24, by decide⟩ ⟨23, by decide⟩
      ⟨25, by decide⟩ c1
  applyXorOps56CT m12 opsPreSplits04 (applyXorOps56CT m12 opsPostA c2)

def ct56PreBack (hi : ℕ) : CT :=
  let m12 := repMask 12
  let c3 := ct56AfterSplitA hi
  let c4 := split2Fwd56CT m12 ⟨11, by decide⟩ ⟨26, by decide⟩ ⟨28, by decide⟩ ⟨27, by decide⟩
      ⟨29, by decide⟩ c3
  let c5 := split2Fwd56CT m12 ⟨15, by decide⟩ ⟨28, by decide⟩ ⟨30, by decide⟩ ⟨29, by decide⟩
      ⟨31, by decide⟩ c4
  let c6 := split2Fwd56CT m12 ⟨14, by decide⟩ ⟨30, by decide⟩ ⟨32, by decide⟩ ⟨31, by decide⟩
      ⟨33, by decide⟩ c5
  let c7 := split2Fwd56CT m12 ⟨13, by decide⟩ ⟨32, by decide⟩ ⟨34, by decide⟩ ⟨33, by decide⟩
      ⟨35, by decide⟩ c6
  let c8 := split2Fwd56CT m12 ⟨12, by decide⟩ ⟨34, by decide⟩ ⟨36, by decide⟩ ⟨35, by decide⟩
      ⟨37, by decide⟩ c7
  applyXorOps56CT m12 opsPostSplits04 c8

def ct52PreBack (hi : ℕ) : CT :=
  let c56 := ct56PreBack hi
  mkCT 7 fun v ↦ if hv : v < 52 then getCT 7 c56 (idx52To56 ⟨v, hv⟩).val else 0

def outBack52CT (hi : ℕ) : CT := evalCTW (repMask 12) 51 (ct52PreBack hi) treeBack16_52
def checkFrontHi (hi : ℕ) : Bool :=
  let ct := ct56Front hi
  ((List.range 17).all fun u ↦ Nat.beq (getCT 7 ct u) (initMuxSumCol hi u)) &&
  Nat.beq (getCT 7 ct 21) ((initMuxSumCol hi 0 ^^^ initMuxSumCol hi 1) &&& initMuxSumCol hi 3) &&
  ((List.range 34).all fun d ↦ Nat.beq (getCT 7 ct (22 + d)) 0)

def checkFrontAll : Bool := (List.range 32).all checkFrontHi
def rippleCarryCol (ct : CT) : ℕ → ℕ
  | 0 => getCT 7 ct 34
  | k + 1 => rippleCarryCol ct k &&& getCT 7 ct (35 + k)

def cz4ColOfCT (ct : CT) : ℕ :=
    (getCT 7 ct 0 &&& getCT 7 ct 17) ^^^ (getCT 7 ct 1 &&& getCT 7 ct 18) ^^^ (getCT 7 ct 2 &&&
    getCT 7 ct 19) ^^^ (getCT 7 ct 34 &&& getCT 7 ct 36)
def effWrcsaCol (ct : CT) (k : ℕ) : ℕ :=
    if k < 16 then rippleCarryCol ct k ^^^ getCT 7 ct (35 +
    k) else rippleCarryCol ct 16 ^^^ getCT 7 ct 51 ^^^ cz4ColOfCT ct
def checkWrcsaBucket (ct : CT) (hi b1v b2v : ℕ) : Bool :=
  if h1 : b1v < 6 then
    if h2 : b2v < 6 then
      let m := colMaskB1 ⟨b1v, h1⟩ &&& colMaskB2 ⟨b2v, h2⟩
      let tgt := tgtValHi hi ⟨b1v, h1⟩ ⟨b2v, h2⟩
      (List.range 17).all fun k ↦
        Nat.beq (effWrcsaCol ct k &&& m) (if tgt.testBit k then m else 0)
    else true
  else true

def checkWrcsaHi (hi : ℕ) : Bool :=
  if isRoutedHi hi then
    let ct := outBack52CT hi
    (List.range 6).all fun b1v ↦
      (List.range 6).all fun b2v ↦
        checkWrcsaBucket ct hi b1v b2v
  else true

def checkWrcsaActive : Bool := (List.range 32).all checkWrcsaHi
/-! ### 2b. `CT` Column Soundness, Router Invariants, and Ripple-Carry Arithmetic -/

theorem ct56Front_spec {hi q u : ℕ} (hhi : hi < 32) (hq : q < 4096)
    (hu : u < 22) : (getCT 7 (ct56Front hi) u).testBit q =
    (evalPrimTree 21 (hi + 32 * q) treeFront5_22).testBit u :=
  evalCTW_sound (W := 12) (M := 21) (by norm_num : 21 < 128) treeFront5_22 (initMuxSumCT hi)
      (hi + 32 * q) q (by norm_num; omega)
    (fun v hv ↦ initMuxSumCT_testBit hhi hq (by omega)) u hu

theorem checkFrontHi_of_lt {hi : ℕ} (hhi : hi < 32) : checkFrontHi hi = true :=
  (List.all_eq_true.mp (by decide +kernel : checkFrontAll = true)) hi (List.mem_range.mpr hhi)

def packIn17_56 (x : BitAssignment 56) : ℕ :=
  packBits 17 fun i ↦ x ⟨i % 17, by omega⟩ == 1

theorem packIn17_56_testBit (x : BitAssignment 56)
    (hCln : ∀ u : Fin 56, 17 ≤ u.val → x u = 0) (v : Wire 22) :
    (x ⟨v.val, by omega⟩ == 1) = (packIn17_56 x).testBit v.val := by
  have := v.isLt
  rw [packIn17_56, packBits_testBit]
  by_cases hv : v.val < 17
  · simpa only [hv, decide_true, Bool.true_and] using congrArg (fun w : Fin 56 ↦ x w == 1)
        (Fin.ext (Nat.mod_eq_of_lt hv)).symm
  · simp only [hv, decide_false, Bool.false_and]; rw [hCln ⟨v.val, by omega⟩
        (by dsimp; omega)]; decide

theorem f56Front_col_eq (x : BitAssignment 56) (hCln : ∀ u : Fin 56, 17 ≤ u.val → x u = 0) :
    (∀ u : Fin 56, u.val < 22 →
      (f56Front x u == 1) =
          (getCT 7 (ct56Front (packIn17_56 x % 32)) u.val).testBit (packIn17_56 x / 32)) ∧
    (∀ (k : ℕ) (hk : k < 17),
      (initMuxSumCol (packIn17_56 x % 32) k).testBit (packIn17_56 x / 32) = (x ⟨k, by omega⟩ == 1))
          := by
  set st := packIn17_56 x
  have hhi : st % 32 < 32 := Nat.mod_lt st (by norm_num)
  have hq : st / 32 < 4096 := (fun h : st < 2 ^ 17 ↦ by norm_num at h; omega) (packBits_lt 17 _)
  have hSplit : st % 32 + 32 * (st / 32) = st := Nat.mod_add_div st 32
  refine ⟨fun u hu22 ↦ ?_, fun k hk ↦ (congrArg (·.testBit (st / 32))
    (getCT_mkCT 7 (initMuxSumCol (st % 32)) k (by omega)).symm).trans
      ((initMuxSumCT_testBit hhi hq (by omega)).trans
        (by rw [hSplit, ← packIn17_56_testBit x hCln ⟨k, by omega⟩]))⟩
  unfold f56Front; rw [dite_eq_left hu22, cpFront5_22, fwdBits_decodePrimTree_testBit (M :=
      21) treeFront5_22 _ st
    (packIn17_56_testBit x hCln) ⟨u.val, hu22⟩, ct56Front_spec hhi hq hu22, hSplit]

theorem f56Front_keep_lt17 (x : BitAssignment 56) (hCln : ∀ u : Fin 56, 17 ≤ u.val → x u = 0)
    (u : Fin 56) (hu : u.val < 17) : f56Front x u = x u := by
  obtain ⟨hF, hC⟩ := f56Front_col_eq x hCln
  have hKeep : getCT 7 (ct56Front (packIn17_56 x % 32)) u.val =
      initMuxSumCol (packIn17_56 x % 32) u.val :=
    Nat.beq_eq.mp ((List.all_eq_true.mp (Bool.and_eq_true_iff.mp
      (Bool.and_eq_true_iff.mp (checkFrontHi_of_lt (Nat.mod_lt _ (by norm_num)))).1).1) u.val
          (List.mem_range.mpr hu))
  exact zmod2_eq_of_beq_one _ _ (by rw [hF u (by omega), hKeep, hC u.val hu])

theorem applyXorOps56_ct_sound {q : ℕ} (hq : q < 4096) :
    ∀ (ops : List XorOp56) (f : BitAssignment 56) (ct : CT),
      (∀ u : Fin 56, (f u == 1) = (getCT 7 ct u.val).testBit q) →
      ∀ u : Fin 56, (applyXorOps56 ops f u == 1) =
        (getCT 7 (applyXorOps56CT (repMask 12) ops ct) u.val).testBit q
  | [], _, _, hHyp => hHyp
  | op :: rest, f, ct, hHyp => applyXorOps56_ct_sound hq rest _ _ fun u ↦ by
      have hu128 : u.val < 2 ^ 7 := u.isLt.trans (by decide)
      cases op with
      | x w =>
          have hrm : (repMask 12).testBit q = true := by
            rw [repMask_testBit]; exact decide_eq_true (by norm_num; omega)
          dsimp only [applyXorOp56, applyXorOp56CT]
          rw [getCT_xorCT 7 ct u.val w.val (repMask 12) hu128 (w.isLt.trans (by decide))]
          by_cases hwu : w = u
          · simp [hwu, zmod2_add_beq1, hHyp u, hrm]
          · simp [Ne.symm hwu, show w.val ≠ u.val from fun e ↦ hwu (Fin.ext e), hHyp u]
      | cnot c tg =>
          dsimp only [applyXorOp56, applyXorOp56CT]
          split_ifs with hct
          · exact hHyp u
          · rw [getCT_xorCT 7 ct u.val tg.val _ hu128 (tg.isLt.trans (by decide))]
            by_cases htu : tg = u
            · simp [htu, zmod2_add_beq1, hHyp u, hHyp c]
            · simp [Ne.symm htu, show tg.val ≠ u.val from fun e ↦ htu (Fin.ext e), hHyp u]

theorem split2Fwd56_ct_sound {q : ℕ} (hq : q < 4096) {uIdx l0 h0 l1 h1 : Fin 56}
    (hd : Distinct5_56 uIdx l0 h0 l1 h1)
    (f : BitAssignment 56) (ct : CT)
        (hHyp : ∀ u : Fin 56, (f u == 1) = (getCT 7 ct u.val).testBit q) :
    ∀ u : Fin 56, (stSplit2Fwd uIdx l0 h0 l1 h1 f u == 1) =
        (getCT 7 (split2Fwd56CT (repMask 12) uIdx l0 h0 l1 h1 ct) u.val).testBit q := fun u ↦ by
  obtain ⟨_, _, _, _, h01, h02, h03, h12, h13, h23⟩ := hd
  have hrm : (repMask 12).testBit q = true := by
    rw [repMask_testBit]; exact decide_eq_true (by norm_num; omega)
  have h128 (v : Fin 56) : v.val < 128 := v.isLt.trans (by decide)
  have vne {a b : Fin 56} (h : a ≠ b) : b.val ≠ a.val := fun e ↦ h (Fin.ext e.symm)
  dsimp only [stSplit2Fwd, split2Fwd56CT]
  rw [getCT_setCT7 _ u.val h1.val _ (h128 u) (h128 h1), getCT_setCT7 _ u.val l1.val _ (h128 u)
      (h128 l1),
    getCT_setCT7 _ u.val h0.val _ (h128 u) (h128 h0), getCT_setCT7 _ u.val l0.val _ (h128 u)
        (h128 l0)]
  by_cases uh1 : u = h1
  · simp [uh1, zmod2_mul_beq1, hHyp l1, hHyp uIdx]
  · by_cases ul1 : u = l1
    · simp [ul1, h23, vne h23, zmod2_mul_beq1, zmod2_add_beq1, hHyp l1, hHyp uIdx, hrm]
    · by_cases uh0 : u = h0
      · simp [uh0, h13, h12, vne h13, vne h12, zmod2_mul_beq1, hHyp l0, hHyp uIdx]
      · by_cases ul0 : u = l0
        · simp [ul0, h03, h02, h01, vne h03, vne h02, vne h01, zmod2_mul_beq1, zmod2_add_beq1,
              hHyp l0, hHyp uIdx, hrm]
        · simp [uh1, ul1, uh0, ul0, vne uh1, vne ul1, vne uh0, vne ul0, hHyp u]

def cz4Val52 (β52 : BitAssignment 52) : ZMod 2 :=
  β52 ⟨0, by decide⟩ * β52 ⟨17, by decide⟩ +
  β52 ⟨1, by decide⟩ * β52 ⟨18, by decide⟩ +
  β52 ⟨2, by decide⟩ * β52 ⟨19, by decide⟩ +
  β52 ⟨34, by decide⟩ * β52 ⟨36, by decide⟩

set_option maxHeartbeats 800000 in
-- Large circuit/register elaboration requires raised heartbeat limit.
theorem cpBack16_52_wrcsa_spec (x : BitAssignment 56)
    (hCln : ∀ u : Fin 56, 17 ≤ u.val → x u = 0)
    (p1 p2 : Fin 64)
    (hp1 : validPre6Mask64.testBit p1.val = true)
    (hp2 : validPre6Mask64.testBit p2.val = true)
    (hP1B : ∀ j : Fin 6, (x ⟨5 + j.val, by omega⟩ == 1) = p1.val.testBit j.val)
    (hP2B : ∀ j : Fin 6, (x ⟨11 + j.val, by omega⟩ == 1) = p2.val.testBit j.val)
    (hRouted : ((x ⟨0, by decide⟩ == 1) = false ∧ (x ⟨1, by decide⟩ == 1) = false ∧
                (x ⟨2, by decide⟩ == 1) = false) ∨
               ((x ⟨0, by decide⟩ == 1) = true ∧
                ((x ⟨1, by decide⟩ == 1) = false → (x ⟨2, by decide⟩ == 1) = false))) :
    let β52 := cpBack16_52.fwdBits (fun v ↦ f56PreBack x (idx52To56 v))
    let col16 := finBitsVal (fun k : Fin 16 ↦ β52 ⟨35 + k.val, by omega⟩)
    let cw := (β52 ⟨34, by decide⟩).val
    let sp1 := speciesOfBits2 (x ⟨3, by decide⟩) (x ⟨4, by decide⟩)
    let tgt := if x ⟨0, by decide⟩ == 1 then
      (v1U10Pre5 (x ⟨1, by decide⟩ == 1) (x ⟨2, by decide⟩ == 1) sp1 (pre5OfPre6 p1) +
        v2U10Pre5 (x ⟨1, by decide⟩ == 1) (x ⟨2, by decide⟩ == 1) 0 (pre5OfPre6 p2)) % 2 ^ 17
    else 0
    ∃ c16 : ℕ, c16 < 2 ∧ col16 + cw = tgt % 2 ^ 16 + c16 * 2 ^ 16 ∧
      ((c16 : ZMod 2) + β52 ⟨51, by decide⟩ + cz4Val52 β52) = ((tgt / 2 ^ 16 : ℕ) : ZMod 2) := by
  intro β52 col16 cw sp1 tgt
  set hi := packBits 5 fun i ↦ x ⟨i % 5, by omega⟩ == 1
  have hhi : hi < 32 := by simpa using packBits_lt 5 (fun i ↦ x ⟨i % 5, by omega⟩ == 1)
  set q := p1.val + 64 * p2.val
  have hq : q < 4096 := (fun _ _ ↦ by omega) p1.isLt p2.isLt
  have hHiBit (i : Fin 5) : hi.testBit i.val = (x ⟨i.val, by omega⟩ == 1) := by
    rw [packBits_testBit]; simpa only [i.isLt, decide_true, Bool.true_and] using
      congrArg (fun w : Fin 56 ↦ x w == 1) (Fin.ext (Nat.mod_eq_of_lt i.isLt))
  have hPreBack : ∀ u : Fin 56, (f56PreBack x u == 1) =
      (getCT 7 (ct56PreBack hi) u.val).testBit q := by
    have hModTb {a b m j : ℕ} (ha : a < 2 ^ m) (hj : j < m) : (a + 2 ^ m * b).testBit j =
        a.testBit j := by
      have h1 := Nat.testBit_mod_two_pow (a + 2 ^ m * b) m j
      rw [Nat.mul_comm (2 ^ m) b, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt ha,
          Nat.mul_comm b (2 ^ m)] at h1
      simpa [hj] using h1.symm
    have hShiftTb {a b m k : ℕ} (hm : 0 < 2 ^ m) (ha : a < 2 ^ m) (hmk : m ≤ k) :
        (a + 2 ^ m * b).testBit k = b.testBit (k - m) := by
      rw [Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq,
        show 2 ^ k = 2 ^ m *
            2 ^ (k - m) by rw [← Nat.pow_add]; exact congrArg (2 ^ ·) (by omega),
        ← Nat.div_div_eq_div_mul, show a + 2 ^ m * b = a + b * 2 ^ m by ring,
        Nat.add_mul_div_right _ _ hm, Nat.div_eq_of_lt ha, zero_add]
    have hStEq : packIn17_56 x = hi + 32 * q := Nat.eq_of_testBit_eq fun k ↦ by
      by_cases hk17 : k < 17
      · refine (packIn17_56_testBit x hCln ⟨k, by omega⟩).symm.trans ?_
        by_cases hk5 : k < 5
        · exact (hHiBit ⟨k, hk5⟩).symm.trans (hModTb (m := 5) hhi hk5).symm
        · by_cases hk11 : k < 11
          · exact ((congrArg (fun w : Fin 56 ↦ x w == 1) (Fin.ext (by dsimp; omega))).trans
              (hP1B ⟨k - 5, by omega⟩)).trans ((hModTb (m := 6)
                  (b := p2.val) p1.isLt (by omega)).symm.trans
                (hShiftTb (m := 5) (by norm_num) hhi (by omega)).symm)
          · exact ((congrArg (fun w : Fin 56 ↦ x w == 1) (Fin.ext (by dsimp; omega))).trans
              (hP2B ⟨k - 11, by omega⟩)).trans ((congrArg p2.val.testBit (show k - 11 = (k - 5) -
                  6 by omega)).trans
                ((hShiftTb (m := 6) (b := p2.val) (by norm_num) p1.isLt (by omega)).symm.trans
                  (hShiftTb (m := 5) (by norm_num) hhi (by omega)).symm))
      · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le (show packIn17_56 x <
            2 ^ 17 from packBits_lt 17 _)
            (Nat.pow_le_pow_right (by omega) (by omega))),
          Nat.testBit_lt_two_pow (lt_of_lt_of_le (show hi + 32 * q < 2 ^ 17 by norm_num; omega)
            (Nat.pow_le_pow_right (by omega) (by omega)))]
    have hFront : ∀ u : Fin 56, (f56Front x u == 1) = (getCT 7 (ct56Front hi) u.val).testBit q :=
        fun u ↦ by
      unfold f56Front; split_ifs with hu22
      · exact (fwdBits_decodePrimTree_testBit (M := 21) treeFront5_22 (fun j : Fin 22 ↦
            x ⟨j.val, by omega⟩)
          (hi + 32 * q) (fun v ↦ (packIn17_56_testBit x hCln v).trans (by rw [hStEq]))
              ⟨u.val, hu22⟩).trans
          (ct56Front_spec hhi hq hu22).symm
      · have hd :=
            Nat.beq_eq.mp ((List.all_eq_true.mp (Bool.and_eq_true_iff.mp (checkFrontHi_of_lt
            hhi)).2)
          (u.val - 22) (List.mem_range.mpr (by omega)))
        rw [show 22 + (u.val - 22) = u.val by omega] at hd
        rw [hCln u (by omega), hd, Nat.zero_testBit]; rfl
    dsimp only [f56PreBack, f56PostSplit4, f56PreSplit4, f56PreSplit3, f56PreSplit2, f56PreSplit1,
        f56PreSplit0,
      f56PostA, f56PostSplitA, f56PreSplitA, ct56PreBack, ct56AfterSplitA]
    apply applyXorOps56_ct_sound hq
    repeat apply split2Fwd56_ct_sound hq (by decide)
    exact applyXorOps56_ct_sound hq _ _ _ (applyXorOps56_ct_sound hq _ _ _
      (split2Fwd56_ct_sound hq (by decide) _ _ (applyXorOps56_ct_sound hq _ _ _ hFront)))
  set β52In : BitAssignment 52 := fun v ↦ f56PreBack x (idx52To56 v)
  set st52 : ℕ := packBits 52 fun i ↦ β52In ⟨i % 52, by omega⟩ == 1
  have hSt52Bit (v : Wire 52) : (β52In v == 1) = st52.testBit v.val := by
    rw [packBits_testBit]; simpa only [v.isLt, decide_true, Bool.true_and] using
      congrArg (fun w : Wire 52 ↦ β52In w == 1) (Fin.ext (Nat.mod_eq_of_lt v.isLt)).symm
  have hOut52 (v : Wire 52) : (β52 v == 1) = (getCT 7 (outBack52CT hi) v.val).testBit q :=
    (fwdBits_decodePrimTree_testBit (M := 51) treeBack16_52 β52In st52 hSt52Bit v).trans
      (evalCTW_sound (W := 12) (M := 51)
          (by norm_num) treeBack16_52 (ct52PreBack hi) st52 q (by norm_num; omega)
        (fun w hw ↦
            by
        dsimp [ct52PreBack]; rw [getCT_mkCT 7 _ w (by norm_num; omega), dite_eq_left hw,
          ← hPreBack (idx52To56 ⟨w, hw⟩)]; exact hSt52Bit ⟨w, hw⟩) v.val v.isLt).symm
  have hRHi : isRoutedHi hi = true :=
    isRoutedHi_of_flags hhi
        (by rwa [hHiBit ⟨0, by omega⟩, hHiBit ⟨1, by omega⟩, hHiBit ⟨2, by omega⟩])
  have hTgtEq : tgtValHi hi (pre5OfPre6 p1) (pre5OfPre6 p2) = tgt := by
    unfold tgtValHi; dsimp only [tgt]
    rw [show ∀ hp, (⟨(if hi.testBit 3 then 1 else 0) + (if hi.testBit 4 then 2 else 0),
        hp⟩ : Fin 4) = sp1 from
      fun _ ↦ Fin.ext (by
        dsimp only [sp1, speciesOfBits2]; rw [hHiBit ⟨3, by omega⟩, hHiBit ⟨4, by omega⟩]
        rcases DynCircExt.bit_cases (x ⟨3, by decide⟩) with h3 | h3 <;>
          rcases DynCircExt.bit_cases (x ⟨4, by decide⟩) with h4 | h4 <;> (rw [h3, h4]; simp)),
      hHiBit ⟨0, by omega⟩, hHiBit ⟨1, by omega⟩, hHiBit ⟨2, by omega⟩]
  set colPack := packBits 16 fun k ↦ β52 ⟨35 + (k % 16), by omega⟩ == 1
  have hColEqPack : col16 = colPack := by
    have hfn : (fun k : Fin 16 ↦ β52 ⟨35 + k.val, by omega⟩) = fun k ↦
        if colPack.testBit k.val then 1 else 0 :=
      funext fun k ↦ by
        rw [packBits_testBit]; simp only [k.isLt, decide_true, Bool.true_and,
            Nat.mod_eq_of_lt k.isLt]
        rcases DynCircExt.bit_cases (β52 ⟨35 + k.val, by omega⟩) with hk | hk <;> simp [hk]
    dsimp [col16]; rw [hfn, finBitsVal_ite_testBit, Nat.mod_eq_of_lt (packBits_lt 16 _)]
  set ct := outBack52CT hi
  have hColBit (m : ℕ) (hm : m < 16) : col16.testBit m = (getCT 7 ct (35 + m)).testBit q := by
    rw [hColEqPack, packBits_testBit]
    simpa only [hm, decide_true, Bool.true_and, Nat.mod_eq_of_lt hm] using hOut52 ⟨35 + m, by omega⟩
  have hCwEq : cw = if (rippleCarryCol ct 0).testBit q then 1 else 0 := by
    rw [show rippleCarryCol ct 0 = getCT 7 ct 34 from rfl, ← hOut52 ⟨34, by decide⟩];
        dsimp only [cw]
    rcases DynCircExt.bit_cases (β52 ⟨34, by decide⟩) with h | h <;> rw [h] <;> decide
  have hTgtBit (k : ℕ) (hk : k < 17) : tgt.testBit k = (effWrcsaCol ct k).testBit q := by
    set b1 := pre5OfPre6 p1
    set b2 := pre5OfPre6 p2
    have hcHi : checkWrcsaHi hi = true :=
      (List.all_eq_true.mp (by decide +kernel : checkWrcsaActive = true)) hi (List.mem_range.mpr
          hhi)
    unfold checkWrcsaHi at hcHi; rw [ite_eq_left hRHi] at hcHi
    have hcB2 :=
        (List.all_eq_true.mp ((List.all_eq_true.mp hcHi) b1.val (List.mem_range.mpr b1.isLt)))
      b2.val (List.mem_range.mpr b2.isLt)
    unfold checkWrcsaBucket at hcB2; rw [dite_eq_left b1.isLt, dite_eq_left b2.isLt] at hcB2
    have hTbEq :=
        congrArg (·.testBit q)
        (Nat.beq_eq.mp ((List.all_eq_true.mp hcB2) k (List.mem_range.mpr hk)))
    have hqMod : q % 64 = p1.val := by
      rw [show q = p1.val + p2.val * 64 by omega, Nat.add_mul_mod_self_right,
          Nat.mod_eq_of_lt p1.isLt]
    have hqDiv : (q / 64) % 64 = p2.val := by
      rw [show q = p1.val + p2.val * 64 by omega, Nat.add_mul_div_right _ _ (by norm_num : 0 < 64),
        Nat.div_eq_of_lt p1.isLt, zero_add, Nat.mod_eq_of_lt p2.isLt]
    have hm1 : (colMaskB1 b1).testBit q = true := by
      rw [colMaskB1_testBit b1 hq, show (⟨q % 64, Nat.mod_lt q (by norm_num)⟩ : Fin 64) =
          p1 from Fin.ext hqMod,
        hqMod, hp1]; simp [b1]
    have hm2 : (colMaskB2 b2).testBit q = true := by
      rw [colMaskB2_testBit b2 hq, show (⟨(q / 64) % 64, Nat.mod_lt _ (by norm_num)⟩ : Fin 64) =
          p2 from Fin.ext hqDiv,
        hqDiv, hp2]; simp [b2]
    have hm : (colMaskB1 b1 &&& colMaskB2 b2).testBit q = true := by
      rw [Nat.testBit_and, hm1, hm2]; rfl
    rw [Nat.testBit_and, hm, Bool.and_true] at hTbEq; rw [← hTgtEq]
    cases htk : (tgtValHi hi b1 b2).testBit k <;>
      simpa only [htk, Bool.false_eq_true, ↓reduceIte, Nat.zero_testBit, hm] using hTbEq.symm
  have hRipple : ∀ m ≤ 16, col16 % 2 ^ m + cw = tgt % 2 ^ m +
      (if (rippleCarryCol ct m).testBit q then 1 else 0) * 2 ^ m := by
    intro m hm
    induction m with
    | zero => simp -zeta [Nat.mod_one, hCwEq]
    | succ m ih =>
        have hm16 : m < 16 := by omega
        have hEffM : (effWrcsaCol ct m).testBit q =
            ((rippleCarryCol ct m).testBit q ^^ (getCT 7 ct (35 + m)).testBit q) := by
          unfold effWrcsaCol; rw [ite_eq_left hm16, Nat.testBit_xor]
        have hHa (a b : Bool) (p : ℕ) : (if a then 1 else 0) * p + (if b then 1 else 0) * p =
            (if (a ^^ b) then 1 else 0) * p + (if (a && b) then 1 else 0) * (2 * p) := by
          cases a <;> cases b <;> simp; ring
        have hModPow (v : ℕ) : v % 2 ^ (m + 1) = v % 2 ^ m + (if v.testBit m then 1 else 0) *
            2 ^ m := by
          rw [Nat.mod_pow_succ, Nat.testBit_eq_decide_div_mod_eq]
          rcases (show (v / 2 ^ m) % 2 = 0 ∨ (v / 2 ^ m) % 2 = 1 by omega) with h | h <;>
              simp [h]
        calc col16 % 2 ^ (m + 1) + cw
          _ = (col16 % 2 ^ m + cw) + (if (getCT 7 ct (35 + m)).testBit q then 1 else 0) *
              2 ^ m := by
              rw [hModPow col16, hColBit m hm16]; ring
          _ = tgt % 2 ^ m + ((if tgt.testBit m then 1 else 0) * 2 ^ m +
                (if (rippleCarryCol ct (m + 1)).testBit q then 1 else 0) * 2 ^ (m + 1)) := by
              rw [ih (by omega), add_assoc, hHa, ← hEffM, ← hTgtBit m (by omega),
                show rippleCarryCol ct (m + 1) = rippleCarryCol ct m &&& getCT 7 ct (35 +
                    m) from rfl,
                Nat.testBit_and, show 2 * 2 ^ m = 2 ^ (m + 1) by ring]
          _ = tgt % 2 ^ (m + 1) + (if (rippleCarryCol ct (m + 1)).testBit q then 1 else 0) *
              2 ^ (m + 1) := by
              rw [hModPow tgt]; ring
  let c16 : ℕ := if (rippleCarryCol ct 16).testBit q then 1 else 0
  have hColLt : col16 < 2 ^ 16 := by rw [hColEqPack]; exact packBits_lt 16 _
  refine ⟨c16, by dsimp only [c16]; split_ifs <;> omega,
    by simpa only [Nat.mod_eq_of_lt hColLt] using hRipple 16 le_rfl, zmod2_eq_of_beq_one _ _ ?_⟩
  have hTgtLt : tgt < 2 ^ 17 := by
    dsimp only [tgt]; split_ifs <;> first | exact Nat.mod_lt _ (by norm_num) | norm_num
  rw [zmod2_add_beq1, zmod2_add_beq1, show ((c16 : ZMod 2) == 1) =
      (rippleCarryCol ct 16).testBit q by
      dsimp only [c16]; cases (rippleCarryCol ct 16).testBit q <;> decide,
    hOut52 ⟨51, by decide⟩, show (cz4Val52 β52 == 1) = (cz4ColOfCT ct).testBit q by
      unfold cz4Val52 cz4ColOfCT
      simp only [zmod2_add_beq1, zmod2_mul_beq1, Nat.testBit_xor, Nat.testBit_and,
        hOut52 ⟨0, by decide⟩, hOut52 ⟨17, by decide⟩, hOut52 ⟨1, by decide⟩,
            hOut52 ⟨18, by decide⟩,
        hOut52 ⟨2, by decide⟩, hOut52 ⟨19, by decide⟩, hOut52 ⟨34, by decide⟩,
            hOut52 ⟨36, by decide⟩],
    show (((tgt / 2 ^ 16 : ℕ) : ZMod 2) == 1) = tgt.testBit 16 by
      rw [Nat.testBit_eq_decide_div_mod_eq]
      rcases (show tgt / 2 ^ 16 = 0 ∨ tgt / 2 ^ 16 =
          1 by norm_num at hTgtLt ⊢; omega) with h | h <;> rw [h] <;> decide,
    hTgtBit 16 (by omega)]
  unfold effWrcsaCol; rw [ite_eq_right (show ¬(16 < 16) by omega), Nat.testBit_xor, Nat.testBit_xor]

/-! ### 2c. Symbolic Invariants for the `6` W-Splits and `f56PreBack` Clean Scratch -/

def SplitInv56 (l0 h0 l1 h1 bIdx : Fin 56) (e56 : BitAssignment 56 → ZMod 2)
    (y : BitAssignment 56) : Prop :=
    y l0 * y l1 = 0 ∧ y h0 = 0 ∧ y h1 = 0 ∧ (y l0 = 1 → y bIdx = 0) ∧ (y l1 = 1 → y bIdx = 1) ∧
    e56 y = y l0 + y l1
def XorOp56.tgt : XorOp56 → Fin 56
  | .x q => q
  | .cnot _ tg => tg

theorem applyXorOp56_of_ne_tgt (op : XorOp56) (f : BitAssignment 56) {u : Fin 56}
    (hne : u ≠ op.tgt) : applyXorOp56 op f u = f u := by
  cases op <;> dsimp only [XorOp56.tgt, applyXorOp56] at hne ⊢ <;> try split_ifs
  all_goals first | rfl | rw [Function.update_of_ne hne]

theorem applyXorOp56_cnot_same {c tg : Fin 56} {f : BitAssignment 56}
    (h : c ≠ tg) : applyXorOp56 (.cnot c tg) f tg = f tg + f c := by
  dsimp only [applyXorOp56]
  rw [ite_eq_right h, Function.update_self]
theorem applyXorOps56_of_forall_ne_tgt :
    ∀ (ops : List XorOp56) (f : BitAssignment 56) {u : Fin 56},
      (∀ op ∈ ops, u ≠ op.tgt) → applyXorOps56 ops f u = f u
  | [], _, _, _ => rfl
  | op :: rest, f, _, hHyp =>
    (applyXorOps56_of_forall_ne_tgt rest _ fun o ho ↦ hHyp o (List.mem_cons_of_mem _ ho)).trans
      (applyXorOp56_of_ne_tgt op f (hHyp op (List.mem_cons_self ..)))

theorem applyXorOps56_eq_of_nonTgt {ops : List XorOp56} {f : BitAssignment 56} {u : Fin 56}
    (h : (ops.all fun op ↦ u != op.tgt) = true) :
    applyXorOps56 ops f u = f u :=
  applyXorOps56_of_forall_ne_tgt ops f fun op hop ↦ bne_iff_ne.mp (List.all_eq_true.mp h op hop)
theorem applyXorOps56_of_lt (ops : List XorOp56) (B : ℕ) (f : BitAssignment 56) {u : Fin 56}
    (hu : B ≤ u.val) (h : (ops.all fun op ↦ decide (op.tgt.val < B)) = true := by decide) :
    applyXorOps56 ops f u = f u :=
  applyXorOps56_of_forall_ne_tgt ops f fun op hop heq ↦ by
    have := of_decide_eq_true (List.all_eq_true.mp h op hop); rw [heq] at hu; omega
theorem stSplit2Fwd_of_ne {uIdx l0 h0 l1 h1 u : Fin 56} (f : BitAssignment 56) (hne0 : u ≠ l0)
    (hne1 : u ≠ h0) (hne2 : u ≠ l1) (hne3 : u ≠ h1) :
    stSplit2Fwd uIdx l0 h0 l1 h1 f u = f u := by
  dsimp only [stSplit2Fwd]
  rw [Function.update_of_ne hne3, Function.update_of_ne hne2, Function.update_of_ne hne1,
      Function.update_of_ne hne0]
theorem stSplit2Fwd_eq_of_bne {uIdx l0 h0 l1 h1 u : Fin 56} {f : BitAssignment 56}
    (h : (u != l0 && u != h0 && u != l1 && u != h1) = true) :
    stSplit2Fwd uIdx l0 h0 l1 h1 f u = f u := by
  simp only [Bool.and_eq_true, bne_iff_ne] at h
  exact stSplit2Fwd_of_ne f h.1.1.1 h.1.1.2 h.1.2 h.2
theorem stSplit2Fwd_of_lt {uIdx l0 h0 l1 h1 u : Fin 56} {B : ℕ} {f : BitAssignment 56}
    (hu : B ≤ u.val)
    (h : (decide (l0.val < B) && decide (h0.val < B) && decide (l1.val < B) && decide (h1.val <
        B)) = true) : stSplit2Fwd uIdx l0 h0 l1 h1 f u = f u := by
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact stSplit2Fwd_of_ne f (fun e ↦ by rw [e] at hu; omega) (fun e ↦ by rw [e] at hu; omega)
      (fun e ↦ by rw [e] at hu; omega) (fun e ↦ by rw [e] at hu; omega)

theorem upd4_eq_of_bne {l0 h0 l1 h1 u : Fin 56} {y : BitAssignment 56} {v0 v1 v2 v3 : ZMod 2}
    (h : (u != l0 && u != h0 && u != l1 && u != h1) = true) :
    Function.update (Function.update (Function.update (Function.update y l0 v0) h0 v1) l1 v2) h1 v3
        u = y u := by
  simp only [Bool.and_eq_true, bne_iff_ne] at h
  rw [Function.update_of_ne h.2, Function.update_of_ne h.1.2, Function.update_of_ne h.1.1.2,
      Function.update_of_ne h.1.1.1]
theorem f56Front_zero_ge22 (x : BitAssignment 56) (hCln : ∀ u : Fin 56, 17 ≤ u.val → x u = 0)
    {u : Fin 56} (hu : 22 ≤ u.val) : f56Front x u = 0 := by
  unfold f56Front
  rw [dite_eq_right (by omega)]
  exact hCln u (by omega)

attribute [local irreducible] f56Front

theorem f56PreSplit0_zero_ge28 (x : BitAssignment 56) (hCln : ∀ u : Fin 56, 17 ≤ u.val → x u = 0)
    {u : Fin 56} (hu : 28 ≤ u.val) : f56PreSplit0 x u = 0 := by
  dsimp only [f56PreSplit0, f56PostA, f56PostSplitA, f56PreSplitA]
  rw [applyXorOps56_of_lt opsPreSplits04 28 _ hu, applyXorOps56_of_lt opsPostA 28 _ hu,
      stSplit2Fwd_of_lt hu, applyXorOps56_of_lt opsInitA 28 _ hu]
  · exact f56Front_zero_ge22 x hCln (by omega)
  · decide

def eActSplitA (z : BitAssignment 56) : ZMod 2 := z ⟨0, by decide⟩ + z ⟨1, by decide⟩
def eActSplit0 (z : BitAssignment 56) : ZMod 2 := z ⟨1, by decide⟩
def eActSplit1 (z : BitAssignment 56) : ZMod 2 := z ⟨1, by decide⟩ * z ⟨11, by decide⟩
def eActSplit2 (z : BitAssignment 56) : ZMod 2 :=
    z ⟨1, by decide⟩ * z ⟨11, by decide⟩ * z ⟨15, by decide⟩
def eActSplit3 (z : BitAssignment 56) : ZMod 2 :=
    z ⟨1, by decide⟩ * z ⟨11, by decide⟩ * z ⟨15, by decide⟩ * z ⟨14, by decide⟩
def eActSplit4 (z : BitAssignment 56) : ZMod 2 :=
  z ⟨1, by decide⟩ * z ⟨11, by decide⟩ * z ⟨15, by decide⟩ * z ⟨14, by decide⟩ * z ⟨13, by decide⟩

theorem inv_f56PreSplitA (x : BitAssignment 56)
    (hCln : ∀ u : Fin 56, 17 ≤ u.val → x u = 0) :
    SplitInv56 ⟨22, by decide⟩ ⟨24, by decide⟩ ⟨23, by decide⟩ ⟨25, by decide⟩
      ⟨3, by decide⟩ eActSplitA (f56PreSplitA x) := by
  have hf0 := f56Front_keep_lt17 x hCln ⟨0, by decide⟩ (by decide)
  have hf1 := f56Front_keep_lt17 x hCln ⟨1, by decide⟩ (by decide)
  have hf21 : f56Front x ⟨21, by decide⟩ = (x ⟨0, by decide⟩ + x ⟨1, by decide⟩) * x ⟨3, by decide⟩
      := by
    obtain ⟨hF, hC⟩ := f56Front_col_eq x hCln
    have hc21 : getCT 7 (ct56Front (packIn17_56 x % 32)) 21 =
        ((initMuxSumCol (packIn17_56 x % 32) 0 ^^^ initMuxSumCol (packIn17_56 x % 32) 1) &&&
          initMuxSumCol (packIn17_56 x % 32) 3) :=
      Nat.beq_eq.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp
        (checkFrontHi_of_lt (Nat.mod_lt _ (by norm_num)))).1).2
    apply zmod2_eq_of_beq_one
    rw [hF ⟨21, by decide⟩ (by decide), hc21, Nat.testBit_and, Nat.testBit_xor,
      hC 0 (by omega), hC 1 (by omega), hC 3 (by omega), zmod2_mul_beq1, zmod2_add_beq1]
  have hf22 := f56Front_zero_ge22 x hCln (u := ⟨22, by decide⟩) (by decide)
  have hf23 := f56Front_zero_ge22 x hCln (u := ⟨23, by decide⟩) (by decide)
  have hKeep (u : Fin 56) (hb : opsInitA.all (fun op ↦ u != op.tgt) = true) : f56PreSplitA x u =
      f56Front x u := applyXorOps56_eq_of_nonTgt hb
  dsimp only [SplitInv56, eActSplitA]
  rw [(hKeep ⟨0, by decide⟩ (by decide)).trans hf0, (hKeep ⟨1, by decide⟩ (by decide)).trans hf1,
    (hKeep ⟨3, by decide⟩ (by decide)).trans (f56Front_keep_lt17 x hCln ⟨3, by decide⟩ (by decide)),
    (hKeep ⟨24, by decide⟩ (by decide)).trans (f56Front_zero_ge22 x hCln (u := ⟨24, by decide⟩)
        (by decide)),
    (hKeep ⟨25, by decide⟩ (by decide)).trans (f56Front_zero_ge22 x hCln (u := ⟨25, by decide⟩)
        (by decide))]
  simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one, Fin.reduceFinMk] at hf0 hf1 hf21 hf22 hf23
  rw [show f56PreSplitA x ⟨22, by decide⟩ =
        x ⟨0, by decide⟩ + x ⟨1, by decide⟩ + (x ⟨0, by decide⟩ + x ⟨1, by decide⟩) *
            x ⟨3, by decide⟩ by
      dsimp only [f56PreSplitA, opsInitA, applyXorOps56, applyXorOp56]; simp [hf22, hf0, hf1,
          hf21],
    show f56PreSplitA x ⟨23, by decide⟩ = (x ⟨0, by decide⟩ + x ⟨1, by decide⟩) *
        x ⟨3, by decide⟩ by
      dsimp only [f56PreSplitA, opsInitA, applyXorOps56, applyXorOp56]; simp [hf23, hf21]]
  rcases DynCircExt.bit_cases (x ⟨0, by decide⟩) with h0 | h0 <;>
    rcases DynCircExt.bit_cases (x ⟨1, by decide⟩) with h1 | h1 <;>
    rcases DynCircExt.bit_cases (x ⟨3, by decide⟩) with h3 | h3 <;> (rw [h0, h1, h3]; decide)

theorem inv_f56PreSplit0 (x : BitAssignment 56)
    (hCln : ∀ u : Fin 56, 17 ≤ u.val → x u = 0)
    (hRouted : ((x ⟨0, by decide⟩ == 1) = false ∧ (x ⟨1, by decide⟩ == 1) = false ∧
                (x ⟨2, by decide⟩ == 1) = false) ∨
               ((x ⟨0, by decide⟩ == 1) = true ∧
                ((x ⟨1, by decide⟩ == 1) = false → (x ⟨2, by decide⟩ == 1) = false))) :
    SplitInv56 ⟨26, by decide⟩ ⟨28, by decide⟩ ⟨27, by decide⟩ ⟨29, by decide⟩
      ⟨2, by decide⟩ eActSplit0 (f56PreSplit0 x) := by
  have hKeep (u : Fin 56) (hb1 : opsPostA.all (fun op ↦ u != op.tgt) = true)
      (hb2 : (u != ⟨22, by decide⟩ && u != ⟨24, by decide⟩ && u != ⟨23, by decide⟩ &&
          u != ⟨25, by decide⟩) = true)
      (hb3 : opsInitA.all (fun op ↦ u != op.tgt) = true) : f56PostA x u = f56Front x u :=
    (applyXorOps56_eq_of_nonTgt hb1).trans ((stSplit2Fwd_eq_of_bne hb2).trans
        (applyXorOps56_eq_of_nonTgt hb3))
  have hP1 := (hKeep ⟨1, by decide⟩ (by decide) (by decide) (by decide)).trans
    (f56Front_keep_lt17 x hCln ⟨1, by decide⟩ (by decide))
  have hP2 := (hKeep ⟨2, by decide⟩ (by decide) (by decide) (by decide)).trans
    (f56Front_keep_lt17 x hCln ⟨2, by decide⟩ (by decide))
  have hP26 := (hKeep ⟨26, by decide⟩ (by decide) (by decide) (by decide)).trans
    (f56Front_zero_ge22 x hCln (u := ⟨26, by decide⟩) (by decide))
  have hP27 := (hKeep ⟨27, by decide⟩ (by decide) (by decide) (by decide)).trans
    (f56Front_zero_ge22 x hCln (u := ⟨27, by decide⟩) (by decide))
  have ⟨hy26, hy27⟩ : f56PreSplit0 x ⟨26, by decide⟩ = x ⟨1, by decide⟩ + x ⟨2, by decide⟩ ∧
      f56PreSplit0 x ⟨27, by decide⟩ = x ⟨2, by decide⟩ := by
    dsimp only [f56PreSplit0, opsPreSplits04, applyXorOps56, applyXorOp56]
    generalize f56PostA x = y at hP26 hP27 hP1 hP2 ⊢
    simp only [Fin.reduceFinMk, Fin.isValue, Fin.mk_one] at hP26 hP27 hP1 hP2;
        exact ⟨by
        simp [hP26, hP1, hP2], by
        simp [hP27, hP2]⟩
  have hKeep0 (u : Fin 56) (hb : (opsPreSplits04.all fun op ↦ u != op.tgt) = true) :
      f56PreSplit0 x u = f56PostA x u := applyXorOps56_eq_of_nonTgt hb
  dsimp only [SplitInv56, eActSplit0]
  rw [(hKeep0 ⟨1, by decide⟩ (by decide)).trans hP1, (hKeep0 ⟨2, by decide⟩ (by decide)).trans hP2,
      hy26, hy27,
    f56PreSplit0_zero_ge28 x hCln (u := ⟨28, by decide⟩) (by decide),
    f56PreSplit0_zero_ge28 x hCln (u := ⟨29, by decide⟩) (by decide)]
  rcases DynCircExt.bit_cases (x ⟨1, by decide⟩) with h1 | h1 <;>
    rcases DynCircExt.bit_cases (x ⟨2, by decide⟩) with h2 | h2 <;>
    first | (rw [h1, h2]; decide) | (rw [h1, h2] at hRouted; simp at hRouted)

attribute [local irreducible] f56PreSplit0

theorem f56PreSplit1_zero_ge30 (x : BitAssignment 56) (hCln : ∀ u : Fin 56, 17 ≤ u.val → x u = 0)
    {u : Fin 56} (hu : 30 ≤ u.val) : f56PreSplit1 x u = 0 := by
  unfold f56PreSplit1; rw [stSplit2Fwd_of_lt hu] <;> first
    | decide
    | exact f56PreSplit0_zero_ge28 x hCln (by omega)
theorem f56PreSplit2_zero_ge32 (x : BitAssignment 56) (hCln : ∀ u : Fin 56, 17 ≤ u.val → x u = 0)
    {u : Fin 56} (hu : 32 ≤ u.val) : f56PreSplit2 x u = 0 := by
  unfold f56PreSplit2; rw [stSplit2Fwd_of_lt hu] <;> first
    | decide
    | exact f56PreSplit1_zero_ge30 x hCln (by omega)
theorem f56PreSplit3_zero_ge34 (x : BitAssignment 56) (hCln : ∀ u : Fin 56, 17 ≤ u.val → x u = 0)
    {u : Fin 56} (hu : 34 ≤ u.val) : f56PreSplit3 x u = 0 := by
  unfold f56PreSplit3; rw [stSplit2Fwd_of_lt hu] <;> first
    | decide
    | exact f56PreSplit2_zero_ge32 x hCln (by omega)
theorem f56PreBack_zero_ge38 (x : BitAssignment 56) (hCln : ∀ u : Fin 56, 17 ≤ u.val → x u = 0)
    {u : Fin 56} (hu : 38 ≤ u.val) : f56PreBack x u = 0 := by
  unfold f56PreBack f56PostSplit4
  rw [applyXorOps56_of_lt opsPostSplits04 38 _ hu, stSplit2Fwd_of_lt hu] <;>
    first | decide | (unfold f56PreSplit4; rw [stSplit2Fwd_of_lt (show 36 ≤ u.val by omega)] <;>
      first | decide | exact f56PreSplit3_zero_ge34 x hCln (by omega))

theorem split2Fwd_chain_inv (uIdx : Fin 56) {l0 h0 l1 h1 : Fin 56}
    (h0Next h1Next : Fin 56) {bIdx : Fin 56}
    {ePrev : BitAssignment 56 → ZMod 2} {y : BitAssignment 56}
    (hPrev : SplitInv56 l0 h0 l1 h1 bIdx ePrev y)
    (hClnNext : y h0Next = 0 ∧ y h1Next = 0)
    (hd : Distinct5_56 uIdx l0 h0 l1 h1 := by decide)
    (hb : (bIdx != l0 && bIdx != h0 && bIdx != l1 && bIdx != h1) = true := by decide)
    (hn0 : (h0Next != l0 && h0Next != h0 && h0Next != l1 && h0Next != h1) = true := by decide)
    (hn1 : (h1Next != l0 && h1Next != h0 && h1Next != l1 && h1Next != h1) = true := by decide)
    (heKeep : ePrev (stSplit2Fwd uIdx l0 h0 l1 h1 y) = ePrev y) :
    SplitInv56 h0 h0Next h1 h1Next bIdx
      (fun z ↦ ePrev z * z uIdx)
      (stSplit2Fwd uIdx l0 h0 l1 h1 y) := by
  obtain ⟨hu0, hu1, hu2, hu3, _, _, _, h12, h13, _⟩ := hd
  obtain ⟨hMut, _, _, hb0, hb1, heEq⟩ := hPrev
  set y' := stSplit2Fwd uIdx l0 h0 l1 h1 y
  have hyh0 : y' h0 = y l0 * y uIdx := by
    dsimp only [y', stSplit2Fwd]
    rw [Function.update_of_ne h13, Function.update_of_ne h12, Function.update_self]
  have hyh1 : y' h1 = y l1 * y uIdx := by
    dsimp only [y', stSplit2Fwd]; exact Function.update_self _ _ _
  have hyu : y' uIdx = y uIdx := stSplit2Fwd_of_ne y hu0 hu1 hu2 hu3
  have hMul1 {a b : ZMod 2} (hab : a * b = 1) : a = 1 := by
    rcases DynCircExt.bit_cases a with rfl | rfl <;> simp at hab ⊢
  refine ⟨by
      rw [hyh0, hyh1, show (y l0 * y uIdx) * (y l1 * y uIdx) = (y l0 * y l1) *
          (y uIdx * y uIdx) by ring, hMut,
        zero_mul],
    (stSplit2Fwd_eq_of_bne hn0).trans hClnNext.1, (stSplit2Fwd_eq_of_bne hn1).trans hClnNext.2,
    fun hh01 ↦ (stSplit2Fwd_eq_of_bne hb).trans (hb0 (hMul1 (hyh0 ▸ hh01))),
    fun hh11 ↦ (stSplit2Fwd_eq_of_bne hb).trans (hb1 (hMul1 (hyh1 ▸ hh11))), ?_⟩
  change ePrev y' * y' uIdx = y' h0 + y' h1
  rw [heKeep, hyu, heEq, hyh0, hyh1, add_mul]

theorem inv_f56PreSplit1 (x : BitAssignment 56)
    (hCln : ∀ u : Fin 56, 17 ≤ u.val → x u = 0)
    (hRouted : ((x ⟨0, by decide⟩ == 1) = false ∧ (x ⟨1, by decide⟩ == 1) = false ∧
                (x ⟨2, by decide⟩ == 1) = false) ∨
               ((x ⟨0, by decide⟩ == 1) = true ∧
                ((x ⟨1, by decide⟩ == 1) = false → (x ⟨2, by decide⟩ == 1) = false))) :
    SplitInv56 ⟨28, by decide⟩ ⟨30, by decide⟩ ⟨29, by decide⟩ ⟨31, by decide⟩
      ⟨2, by decide⟩ eActSplit1 (f56PreSplit1 x) :=
  split2Fwd_chain_inv ⟨11, by decide⟩ ⟨30, by decide⟩ ⟨31, by decide⟩
      (inv_f56PreSplit0 x hCln hRouted)
    ⟨f56PreSplit0_zero_ge28 x hCln (u := ⟨30, by decide⟩)
        (by decide), f56PreSplit0_zero_ge28 x hCln (u := ⟨31, by decide⟩) (by decide)⟩
    (heKeep := by rw [stSplit2Fwd_eq_of_bne]; decide)

theorem inv_f56PreSplit2 (x : BitAssignment 56)
    (hCln : ∀ u : Fin 56, 17 ≤ u.val → x u = 0)
    (hRouted : ((x ⟨0, by decide⟩ == 1) = false ∧ (x ⟨1, by decide⟩ == 1) = false ∧
                (x ⟨2, by decide⟩ == 1) = false) ∨
               ((x ⟨0, by decide⟩ == 1) = true ∧
                ((x ⟨1, by decide⟩ == 1) = false → (x ⟨2, by decide⟩ == 1) = false))) :
    SplitInv56 ⟨30, by decide⟩ ⟨32, by decide⟩ ⟨31, by decide⟩ ⟨33, by decide⟩
      ⟨2, by decide⟩ eActSplit2 (f56PreSplit2 x) :=
  split2Fwd_chain_inv ⟨15, by decide⟩ ⟨32, by decide⟩ ⟨33, by decide⟩
      (inv_f56PreSplit1 x hCln hRouted)
    ⟨f56PreSplit1_zero_ge30 x hCln (u := ⟨32, by decide⟩)
        (by decide), f56PreSplit1_zero_ge30 x hCln (u := ⟨33, by decide⟩) (by decide)⟩
    (heKeep := by rw [stSplit2Fwd_eq_of_bne, stSplit2Fwd_eq_of_bne] <;> decide)

theorem inv_f56PreSplit3 (x : BitAssignment 56)
    (hCln : ∀ u : Fin 56, 17 ≤ u.val → x u = 0)
    (hRouted : ((x ⟨0, by decide⟩ == 1) = false ∧ (x ⟨1, by decide⟩ == 1) = false ∧
                (x ⟨2, by decide⟩ == 1) = false) ∨
               ((x ⟨0, by decide⟩ == 1) = true ∧
                ((x ⟨1, by decide⟩ == 1) = false → (x ⟨2, by decide⟩ == 1) = false))) :
    SplitInv56 ⟨32, by decide⟩ ⟨34, by decide⟩ ⟨33, by decide⟩ ⟨35, by decide⟩
      ⟨2, by decide⟩ eActSplit3 (f56PreSplit3 x) :=
  split2Fwd_chain_inv ⟨14, by decide⟩ ⟨34, by decide⟩ ⟨35, by decide⟩
      (inv_f56PreSplit2 x hCln hRouted)
    ⟨f56PreSplit2_zero_ge32 x hCln (u := ⟨34, by decide⟩)
        (by decide), f56PreSplit2_zero_ge32 x hCln (u := ⟨35, by decide⟩) (by decide)⟩
    (heKeep := by rw [stSplit2Fwd_eq_of_bne, stSplit2Fwd_eq_of_bne, stSplit2Fwd_eq_of_bne] <;>
                    decide)

theorem inv_f56PreSplit4 (x : BitAssignment 56)
    (hCln : ∀ u : Fin 56, 17 ≤ u.val → x u = 0)
    (hRouted : ((x ⟨0, by decide⟩ == 1) = false ∧ (x ⟨1, by decide⟩ == 1) = false ∧
                (x ⟨2, by decide⟩ == 1) = false) ∨
               ((x ⟨0, by decide⟩ == 1) = true ∧
                ((x ⟨1, by decide⟩ == 1) = false → (x ⟨2, by decide⟩ == 1) = false))) :
    SplitInv56 ⟨34, by decide⟩ ⟨36, by decide⟩ ⟨35, by decide⟩ ⟨37, by decide⟩
      ⟨2, by decide⟩ eActSplit4 (f56PreSplit4 x) :=
  split2Fwd_chain_inv ⟨13, by decide⟩ ⟨36, by decide⟩ ⟨37, by decide⟩
      (inv_f56PreSplit3 x hCln hRouted)
    ⟨f56PreSplit3_zero_ge34 x hCln (u := ⟨36, by decide⟩)
        (by decide), f56PreSplit3_zero_ge34 x hCln (u := ⟨37, by decide⟩) (by decide)⟩
    (heKeep
        := by rw [stSplit2Fwd_eq_of_bne, stSplit2Fwd_eq_of_bne, stSplit2Fwd_eq_of_bne,
                stSplit2Fwd_eq_of_bne] <;> decide)
end QuantumComputation.Specs.PhotochemistrySolution.WRouterCsaDual180
end


open QuantumComputation.Specs.PhotochemistrySolution.OuterW11Bridge

namespace QuantumComputation.Specs.PhotochemistrySolution.Stage2W325AlwaysLo

open Operator QProg Matrix HermitianMat Circuit Qubit PrimitiveGate
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
open PhotochemistrySolution.KetSupport PhotochemistrySolution.SelectQft8GidneyStg3
open PhotochemistrySolution.SplitRouter47_187 PhotochemistrySolution.RouterSelectWiringA
  PhotochemistrySolution.RouterSelectWiringB PhotochemistrySolution.ProviderCoreFused
open PhotochemistrySolution.Stage12Compact PhotochemistrySolution.ProviderZeroFloor
  PhotochemistrySolution.FastQft8 PhotochemistrySolution.Kinetic664
open PhotochemistrySolution.Kinetic664Stage4 PhotochemistrySolution.Qft8PostCancelT5
  PhotochemistrySolution.ZeroNEremSpec PhotochemistrySolution.PotSelectWiring
open PhotochemistrySolution.Sub5885MuxD1 PhotochemistrySolution.PortBDualBellUnld
  PhotochemistrySolution.ReflStage4 PhotochemistrySolution.WStateRouterPrim
open PhotochemistrySolution.HalfBellCollapse PhotochemistrySolution.WStateStage5Unload
  PhotochemistrySolution.WStateWalkSeam PhotochemistrySolution.MidOW58U10
open PhotochemistrySolution.Dist18Leg1Pass PhotochemistrySolution.Dist18Col9Domino147
  PhotochemistrySolution.Dist18P26QuadCol2Unld
open _root_.DynamicCircuit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt hiding ket matrix_ext_ket
  qAssign_obs_map_val ket_projector_zero ket_projector_one ket_X ket_CNOT ket_TOFF eval_seq_mulVec
  bit_cases localIdx
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SelectCompactAnc (totDimCompactGen)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SplitRouterSeqBell26k hiding ket
  matrix_ext_ket
open scoped Circuit.Notation

noncomputable section
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB (ket matrix_ext_ket)
attribute [local reducible] totDimCompactGen
/-! ### 1. Electronic 222-private-wire footprint (`UsedNoNFW325`) & stack bound (`wWork ≥ 325`) -/

def Stage5ElecFootprintNoHB7 {n : ℕ} (rE : RouterReg 187 8 n) (w : Wire n) : Prop :=
    ∃ j : Fin (routerWidth 187 8), w = rE j ∧ (j.val < 97 ∨ (114 ≤ j.val ∧ j.val < 4602) ∨
    (4624 ≤ j.val ∧ j.val < 4811))
lemma fixedSwapVecCirc_congr_w325 {M m n : ℕ} {q₁ q₂ : Fin m → Wire n} (hq : q₁ = q₂)
    (cV : Fin M → ZMod 2) {w₁ w₂ : Fin m → Fin M → Wire n} (hw : w₁ = w₂)
    (h₁ : ∀ k p, q₁ k ≠ w₁ k p) (h₂ : ∀ k p, q₂ k ≠ w₂ k p) : fixedSwapVecCirc M m q₁ cV w₁ h₁ =
    fixedSwapVecCirc M m q₂ cV w₂ h₂ := by subst hq; subst hw; rfl
lemma fixedBellVecCirc_congr_w325 {M m n : ℕ} {q₁ q₂ : Fin m → Wire n} (hq : q₁ = q₂)
    (cV : Fin M → ZMod 2) {w₁ w₂ : Fin m → Fin M → Wire n} (hw : w₁ = w₂)
    (h₁ : ∀ k p, q₁ k ≠ w₁ k p) (h₂ : ∀ k p, q₂ k ≠ w₂ k p) : fixedBellVecCirc M m q₁ cV w₁ h₁ =
    fixedBellVecCirc M m q₂ cV w₂ h₂ := by subst hq; subst hw; rfl
open PhotochemistrySolution.Stage2AlwaysLo
end

end QuantumComputation.Specs.PhotochemistrySolution.Stage2W325AlwaysLo


noncomputable section

namespace QuantumComputation.Specs.PhotochemistrySolution.Stage1UlpElecNuc
open Real Operator QProg DynamicCircuit Matrix PhotochemistrySolution.ClusterPotSlice
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt
open PhotochemistrySolution.ZeroNEremSpec PhotochemistrySolution.TelescopeSlice
  PhotochemistrySolution.EvenOctB70
open PhotochemistrySolution.WStateStage4Ulp
open _root_.QuantumComputation.Specs.PhotochemistrySolution.GrayCodeKinNuc (wEESpeciesTier1Walk
    wNNSpeciesTier1Walk wENSpeciesTier1Walk wKinTier1Walk totalSlotsIdleTier1Walk)

/--
`g66` -stratified `.en` `W11` weight (`3072` for `w < 401` , `3052` otherwise; sum `6,258,516` ).
-/
def wgtEN (w : ℕ) : ℕ := if w < 401 then 3072 else 3052

inductive ChEN : Type
  | en : ChEN
  | enAux : ChEN

def cntEN2048Tier1 (s : Fin 4) (w : ℕ) : ℕ := mSpCart254 s * (3052 + 20 * if w < 401 then 1 else 0)
theorem sum_cntEN2048Tier1 (s : Fin 4) : (∑ u : Fin 2048, cntEN2048Tier1 s u.val) =
    wENSpeciesTier1Walk s := by
  simp only [cntEN2048Tier1, ← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_fin, smul_eq_mul, sum_fin_lt_nat (M := 2048) (t := 401) (by omega)]
  fin_cases s <;> rfl

/-- `.en` `W11` fiber counts (`0x000` polarity) for `Stage1_1424`. -/
def cntENTier1 (s : Fin 4) (ω : BitAssignment 11) : ℕ := cntEN2048Tier1 s (natOfZModBits 11 ω)
theorem cntENTier1_eq_wgtEN (s : Fin 4) (ω : BitAssignment 11) : cntENTier1 s ω = mSpCart254 s *
    wgtEN (natOfZModBits 11 ω) := by unfold cntENTier1 cntEN2048Tier1 wgtEN; split_ifs <;> rfl
end QuantumComputation.Specs.PhotochemistrySolution.Stage1UlpElecNuc
end

section
namespace QuantumComputation.Specs.PhotochemistrySolution.Stage1CoinDecode
open DynamicCircuit PhotochemistrySolution.ZeroNEremSpec PhotochemistrySolution.ScreenFermatCore
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt
open PhotochemistrySolution.Stage1ZeroNEremSpec PhotochemistrySolution.FermatInverse
  PhotochemistrySolution.Cartesian254 PhotochemistrySolution.Tier1K3708
open PhotochemistrySolution.GrayCodeKinNuc
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Stage1UlpElecNuc (cntEN2048Tier1
    sum_cntEN2048Tier1 cntENTier1 cntENTier1_eq_wgtEN)
def tier1WalkKinNucS8T1aHi (s8 : ℕ) (ax : Fin 3) (naGrp4 : ℕ) : ZeroNEremSector × ℕ :=
  let q4 := (s8 / 16) % 16
  let b2 := (s8 / 4) % 2
  let b1 := (s8 / 2) % 2
  let b0 := s8 % 2
  let low3 := s8 % 8
  cond (Nat.beq q4 12) (.kin (mkFin234 low3) ax, 29235)
    (cond (Nat.beq q4 13)
      (cond (Nat.beq low3 7) (.idle, 0) (.kin (mkFin234 (16 + low3)) ax, 29235))
      (cond (Nat.beq q4 14) (.kin (mkFin234 (8 + low3)) ax, 29235)
        (cond (Nat.beq b2 0) (.kin (mkFin234 naGrp4) ax, 20509)
          (cond (Nat.beq b1 0) (.kin (mkFin234 (44 + b0)) ax, 25053)
            (cond (Nat.beq b0 0) (.kin (mkFin234 46) ax, 21933)
              (.kin (mkFin234 43) ax, 25053))))))

def tier1WalkKinNucS8T1a (s8 : ℕ) (ax : Fin 3) : ZeroNEremSector × ℕ :=
  let q4 := (s8 / 16) % 16
  let b3 := (s8 / 8) % 2
  let low3 := s8 % 8
  let naGrp4 := cond (Bool.and (Nat.beq ((s8 / 2) % 2) 1) (Nat.beq (s8 % 2) 1)) 23 (40 + s8 % 4)
  let na24_39 := cond (Nat.beq b3 1) (32 + low3) (24 + low3)
  cond (Nat.blt q4 10) (.kin (mkFin234 na24_39) ax, 32768)
    (cond (Nat.beq q4 10) (.kin (mkFin234 na24_39) ax, 20509)
      (cond (Nat.beq b3 1) (.kin (mkFin234 naGrp4) ax, 32768)
        (cond (Nat.beq q4 11) (.idle, 0)
          (tier1WalkKinNucS8T1aHi s8 ax naGrp4))))

def permS8BToA (s8 : ℕ) : ℕ := ((s8 / 4) % 8) + 8 * (s8 % 4) + 32 * ((s8 / 32) % 8)
def invPermS8AToB (s8 : ℕ) : ℕ := ((s8 / 8) % 4) + 4 * (s8 % 8) + 32 * ((s8 / 32) % 8)
def tier1T1bKinNucS8 (s8 : ℕ) (ax : Fin 3) : ZeroNEremSector × ℕ :=
    tier1WalkKinNucS8T1a (permS8BToA s8) ax
def tier1T1bKinNucBlk (hi10 : ℕ) : ZeroNEremSector × ℕ :=
    cond (Nat.ble 768 hi10) (.idle, 0) (tier1T1bKinNucS8 (hi10 % 256) (mkFin3 (hi10 / 256)))
abbrev lo2L2Mask64 : ℕ := 0xfff3000f000f000

def kinNucThr9 (thr15 lo2 : ℕ) : ℕ :=
  cond (Nat.beq thr15 0) 0
    (cond (Nat.beq thr15 32768) 512
      (let aBase := cond (Nat.beq thr15 20509) 306
        (cond (Nat.beq thr15 29235) 487
          (cond (Nat.beq thr15 25053) 400 305))
       let ubI := Bool.not (Nat.beq thr15 21933)
       let gk1 := lo2.testBit 0
       let l2B := lo2L2Mask64.testBit (lo2 % 64)
       let gk2 := Bool.and gk1 (xor ubI l2B)
       Nat.xor (Nat.xor aBase (cond gk1 128 0)) (cond gk2 169 0)))

def g66VOpt (h2 lo2 : ℕ) : Bool :=
    Bool.or (Bool.and (Nat.beq h2 0) (Nat.ble 48 lo2)) (Bool.and (Nat.blt 0 h2)
    (Nat.beq (lo2 / 2) 23))
def t1SoloRow (z1 : ℕ) : ℕ :=
    cond (bitAt z1 7) (cond (bitAt z1 6) 0 (cond (bitAt z1 5) (cond (bitAt z1 4)
    (cond (bitAt z1 0) 6277101734290554535837612234495481669679444926523705917439
    6277101733926606374197592464805889078093712918613831188479) (cond (bitAt z1 3)
    (cond (bitAt z1 2)
    (cond (bitAt z1 1) 1096148528403093352414389027585181429425531584511
    16725558898897967357058483069197243010564096) 21952296054803582156139259028321381451365376)
    (cond (bitAt z1 2) 22278967127047683081081807525766640103915456
    22299384069062939388890716806856968769699836))) (cond (bitAt z1 4) (cond (bitAt z1 3)
    (cond (bitAt z1 2) 95780971304117713366327842473064553673779069656760319
    4184766417248221881624837945143703466432844527370755899391)
    (cond (bitAt z1 2) 4707826301540010572621626397992402063346210677194953326591
    6277101735386680763750718831477431800224213869398627188735)) (cond (bitAt z1 3)
    (cond (bitAt z1 2) 95779509802480722749670703142433930280505368316477440
    73330844653078053924845159535692719990783677164421120)
    (cond (bitAt z1 2) 71927803081240387123293563060271394347676071467417600
    71840112983000532948196588280557561494981846111354880))))) (cond (bitAt z1 6) (cond (bitAt z1 5)
    (cond (bitAt z1 4) (cond (bitAt z1 3) (cond (bitAt z1 2)
    (cond (bitAt z1 1) 6277101733925268329485680627417324399448177139172986060799
    6277101733948015089588181863022923936422285389667353231359)
    6277101733948015089588181863022923936422285389667353231359)
    6277101733948015089588181863022923936422285389667353231359) (cond (bitAt z1 3)
    (cond (bitAt z1 2)
    (cond (bitAt z1 1) 1460096690043113122103981619170913437335406313471
    16725558898897967357058483069197243010564096) 21952296054803582156139259028321381451365376)
    (cond (bitAt z1 2) 22278967127047683081081807525766640103915456
    22299384069062939388890716806856968769699836))) (cond (bitAt z1 4) (cond (bitAt z1 3)
    (cond (bitAt z1 2) 95780971304117713366327842473064553673779069656760319
    4184766417248221881624837945143703466432844527370755899391)
    (cond (bitAt z1 2) 4707826301540010572621626397992402063346210677194953326591
    6277101735386680763750718831477431800224213869398627188735)) (cond (bitAt z1 3)
    (cond (bitAt z1 2) 95779509802480722749670703142433930280505368316477440
    73330844653078053924845159535692719990783677164421120)
    (cond (bitAt z1 2) 71927803081240387123293563060271394347676071467417600
    71840112983000532948196588280557561494981846111354880))))
  (cond (bitAt z1 5) (cond (bitAt z1 4) (cond (bitAt z1 3) (cond (bitAt z1 2)
      (cond (bitAt z1 0) 6277101733925184701691186137580539107032831152957933240319
      6277101734290532235432696070793277388517174015038502928384)
      (cond (bitAt z1 0) 6277101733925179474954030231965740026256872028819492439039
      6277101733947992789183265699320719655260014478182150242304)) (cond (bitAt z1 2)
      (cond (bitAt z1 0) 6277101733925179148282957987864815083708374583560839888959
      6277101733926584073792676301103684796931442007128628199424)
      (cond (bitAt z1 0) 6277101733925179127866015972608507274799093493232174104579
      6277101733925246029080764463715120118285906227687783071744))) (cond (bitAt z1 3)
      (cond (bitAt z1 2) (cond (bitAt z1 1)
      (cond (bitAt z1 0) 1438665674247607560184742479680070054796681281536
      16725558898897967357058483069197243010564096) 16725558898897967357058483069197243010564096)
      21952296054803582156139259028321381451365376)
      (cond (bitAt z1 2) 22278967127047683081081807525766640103915456
      22299384069062939388890716806856968769699836))) (cond (bitAt z1 4) (cond (bitAt z1 3)
      (cond (bitAt z1 2) 95780971304117713366327842473064553673779069656760319
      4184766417248221881624837945143703466432844527370755899391)
      (cond (bitAt z1 2) 4707826301540010572621626397992402063346210677194953326591
      6277101735386680763750718831477431800224213869398627188735)) (cond (bitAt z1 3)
      (cond (bitAt z1 2) 95779509802480722749670703142433930280505368316477440
      73330844653078053924845159535692719990783677164421120)
      (cond (bitAt z1 2) 71927803081240387123293563060271394347676071467417600
      71840112983000532948196588280557561494981846111354880)))))
def t1PairRow (z1 : ℕ) : ℕ :=
    cond (bitAt z1 7) (cond (bitAt z1 6) 0 (cond (bitAt z1 5) (cond (bitAt z1 4) (cond (bitAt z1 3)
    (cond (bitAt z1 2) (cond (bitAt z1 1)
    (cond (bitAt z1 0) 1255402387871180892242829002536762439024591461239443620659
    5021681458462493655055050804039210992871303112494501645564)
    (cond (bitAt z1 0) 1255402387871180892242829002536762439024591461239443620659
    5021681107696748435122938899783246088441323736389143809036))
    (cond (bitAt z1 0) 1255402387871180892242829002536762439024591461239443620659
    5021681107696748435122938899783246088441323736389143809036))
    (cond (bitAt z1 0) 1255402387871180892242829002536762439024591461239443620659
    5021681107696748435122938899783246088441323736389143809036)) (cond (bitAt z1 3)
    (cond (bitAt z1 2)
    (cond (bitAt z1 1) 5021681387213201657511555451886591327966681197982289497292
    2510879006817229691145043749628630775400486339573323726028)
    (cond (bitAt z1 1) 5021681388240835676505344596759499030351784805185522286796
    5021681388326471844734976009225919603722450757136446967756)) (cond (bitAt z1 2)
    (cond (bitAt z1 1) 5335555631268657664458818160600763872376329335575493266444
    3452405954463744872212763370657470617779441103197462908156)
    (cond (bitAt z1 1) 5021681388309076997872719584576689403639230300201720794304
    5021681388309411514240003639468142141393782391626691235023)))) (cond (bitAt z1 4)
    (cond (bitAt z1 3) (cond (bitAt z1 2)
    (cond (bitAt z1 1) 5021609552580849796969497093081878403641997901507838348492
    2510896965475317656280559312885469981760684644431949528268)
    (cond (bitAt z1 1) 5021676898576313685221465705945289228761735228970865836236
    5021682510742602342555945731929472054119963151190111080396)) (cond (bitAt z1 2)
    (cond (bitAt z1 1) 5335555350664625040003575729924875759776951237062077238284
    3452406024614753028326573978326442645929285627825816915196)
    (cond (bitAt z1 1) 5021681370771324958844266932659446396601769169044632292544
    5021681392693849523997116802447452893153147674415963360463))) (cond (bitAt z1 3)
    (cond (bitAt z1 2)
    (cond (bitAt z1 1) 5021609551484740294530218802337050715702156580810520317132
    2510896965749345031890378885571676903745644974606279036108)
    (cond (bitAt z1 1) 5021676898507806841319010812773737498265495146427283459276
    5021682510759729053531559455222359986744023171826006674636)) (cond (bitAt z1 2)
    (cond (bitAt z1 1) 5335555350660343362259672299101653776620936231903103339724
  3452406024615823447762549836032248141718289379115560389836)
      (cond (bitAt z1 1) 5021681370771057353985272968232995022654518231222196423884
      5021681392693916425211865293554065736639960408871572327628)))))) (cond (bitAt z1 6)
      (cond (bitAt z1 5) (cond (bitAt z1 4) (cond (bitAt z1 3) (cond (bitAt z1 2) (cond (bitAt z1 1)
      (cond (bitAt z1 0) 1255420364615623413763763674565463723498006127591687140159
      5021681392693916426317782986047115742951268115245947669711)
      (cond (bitAt z1 0) 1255424836878874967898240105167725994269440995806147723059
      5021682510759729314851402093697681310644126832299562815436))
      (cond (bitAt z1 0) 1255424836878874967898240105167725994269440995806147723059
      5021682510759729314851402093697681310644126832299562815436))
      (cond (bitAt z1 0) 1255424836878874967898240105167725994269440995806147723059
      5021682510759729314851402093697681310644126832299562815436)) (cond (bitAt z1 3)
      (cond (bitAt z1 2)
      (cond (bitAt z1 1) 3452406024615823464096107342459938289966431145651112561916
      2510879006817229691145043749628630775400486339573323726028)
      (cond (bitAt z1 1) 5021681388240835676505344596759499030351784805185522286796
      5021681388326471844734976009225919603722450757136446967756)) (cond (bitAt z1 2)
      (cond (bitAt z1 1) 5335555631268657664458818160600763872376329335575493266444
      3452405954463744872212763370657470617779441103197462908156)
      (cond (bitAt z1 1) 5021681388309076997872719584576689403639230300201720794304
      5021681388309411514240003639468142141393782391626691235023)))) (cond (bitAt z1 4)
      (cond (bitAt z1 3) (cond (bitAt z1 2)
      (cond (bitAt z1 1) 5021609552580849796969497093081878403641997901507838348492
      2510896965475317656280559312885469981760684644431949528268)
      (cond (bitAt z1 1) 5021676898576313685221465705945289228761735228970865836236
      5021682510742602342555945731929472054119963151190111080396)) (cond (bitAt z1 2)
      (cond (bitAt z1 1) 5335555350664625040003575729924875759776951237062077238284
      3452406024614753028326573978326442645929285627825816915196)
      (cond (bitAt z1 1) 5021681370771324958844266932659446396601769169044632292544
      5021681392693849523997116802447452893153147674415963360463))) (cond (bitAt z1 3)
      (cond (bitAt z1 2)
      (cond (bitAt z1 1) 5021609551484740294530218802337050715702156580810520317132
      2510896965749345031890378885571676903745644974606279036108)
      (cond (bitAt z1 1) 5021676898507806841319010812773737498265495146427283459276
  5021682510759729053531559455222359986744023171826006674636)) (cond (bitAt z1 2)
      (cond (bitAt z1 1) 5335555350660343362259672299101653776620936231903103339724
      3452406024615823447762549836032248141718289379115560389836)
      (cond (bitAt z1 1) 5021681370771057353985272968232995022654518231222196423884
      5021681392693916425211865293554065736639960408871572327628))))) (cond (bitAt z1 5)
      (cond (bitAt z1 4) (cond (bitAt z1 3) (cond (bitAt z1 2) (cond (bitAt z1 1)
      (cond (bitAt z1 0) 5021609551484723568971319904369693657228310755604364528844
      5021681387213201657511555451886591327966681197982289497292)
      (cond (bitAt z1 0) 2510896965749349213280103610063516168364106430907817983180
      2510896965749349213280103610063516168365259352412424830156)) (cond (bitAt z1 1)
      (cond (bitAt z1 0) 5021676898507805795971579631650777682110879782351898722508
      5021676898507805795971579631650777682110591551975747010764)
      (cond (bitAt z1 0) 5021682510759729314868417250503099940782677012844852858828
      5021682510759729314868417250503099940782749070438890786764))) (cond (bitAt z1 2)
      (cond (bitAt z1 1)
      (cond (bitAt z1 0) 5335555350660343296925457850281468788111272771648391793676
      5335555350660343296925457850281468788111254757249882311692)
      (cond (bitAt z1 0) 3452406024615823464096103448237294388845705244179238276348
      3452406024615823464096107342459938289966431145651112561916)) (cond (bitAt z1 1)
      (cond (bitAt z1 0) 5021681370771057349901884565181733460872664264956276952256
      5021681370771057349901884565181733460872663139056370109632)
      (cond (bitAt z1 0) 5021681392693916426232712394316881127085423900438052195535
      5021681392693916426232712394316881127085424181913028906191)))) (cond (bitAt z1 3)
      (cond (bitAt z1 2) (cond (bitAt z1 1)
      (cond (bitAt z1 0) 5021682510759729314851402093697681310644126832299562815436
      1255492183901957194864469518837972758883267990527780582195)
      (cond (bitAt z1 0) 2510879006817229691145043749628630775400486339573323726028
      3766222728569451072690745673579035640701869104890710786867)) (cond (bitAt z1 1)
      (cond (bitAt z1 0) 5021681388240835676505344596759499030351784805185522286796
      1255420347145845087330444826448167385750570639278512226099)
      (cond (bitAt z1 0) 5021681388326471844734976009225919603722450757136446967756
      1255420347060208919100813413981746812379904687327587545139))) (cond (bitAt z1 2)
      (cond (bitAt z1 1)
      (cond (bitAt z1 0) 5335555631268657664458818160600763872376329335575493266444
  941546104118023099376971262606902543726026108888541246451)
      (cond (bitAt z1 0) 3452405954463744872212763370657470617779441103197462908156
      2824695780922935891623026052550195798322914341266571604739)) (cond (bitAt z1 1)
      (cond (bitAt z1 0) 5021681388309076997872719584576689403639230300201720794304
      1255420347077603765963069838630977012463125144262313718591)
      (cond (bitAt z1 0) 5021681388309411514240003639468142141393782391626691235023
      1255420347077269249595785783739524274708573052837343277872))))) (cond (bitAt z1 4)
      (cond (bitAt z1 3) (cond (bitAt z1 2) (cond (bitAt z1 1)
      (cond (bitAt z1 0) 5021609552580849796969497093081878403641997901507838348492
      1255492182805830966866292330125788012460357542956196164403)
      (cond (bitAt z1 0) 2510896965475317656280559312885469981760684644431949528268
      3766204769911363107555230110322196434341670800032084984627)) (cond (bitAt z1 1)
      (cond (bitAt z1 0) 5021676898576313685221465705945289228761735228970865836236
      1255424836810367078614323717262377187340620215493168676659)
      (cond (bitAt z1 0) 5021682510742602342555945731929472054119963151190111080396
      1255419224644078421279843691278194361982392293273923432499))) (cond (bitAt z1 2)
      (cond (bitAt z1 1)
      (cond (bitAt z1 0) 5335555350664625040003575729924875759776951237062077238284
      941546384722055723832213693282790656325404207401957274611)
      (cond (bitAt z1 0) 3452406024614753028326573978326442645929285627825816915196
      2824695710771927735509215444881223770173069816638217597699)) (cond (bitAt z1 1)
      (cond (bitAt z1 0) 5021681370771324958844266932659446396601769169044632292544
      1255420364615355804991522490548220019500586275419402220351)
      (cond (bitAt z1 0) 5021681392693849523997116802447452893153147674415963360463
      1255420342692831239838672620760213522949207770048071152432)))) (cond (bitAt z1 3)
      (cond (bitAt z1 2) (cond (bitAt z1 1)
      (cond (bitAt z1 0) 5021609551484740294530218802337050715702156580810520317132
      1255492183901940469305570620870615700400198863653514195763)
      (cond (bitAt z1 0) 2510896965749345031890378885571676903745644974606279036108
      3766204769637335731945410537635989512356710469857755476787)) (cond (bitAt z1 1)
      (cond (bitAt z1 0) 5021676898507806841319010812773737498265495146427283459276
      1255424836878873922516778610433928917836860298036751053619)
      (cond (bitAt z1 0) 5021682510759729053531559455222359986744023171826006674636
      1255419224626951710304229967985306429358332272638027838259))) (cond
  (bitAt z1 2) (cond (bitAt z1 1)
      (cond (bitAt z1 0) 5335555350660343362259672299101653776620936231903103339724
      941546384726337401576117124106012639481419212560931173171)
      (cond (bitAt z1 0) 3452406024615823447762549836032248141718289379115560389836
      2824695710770857316073239587175418274384066065348474123059)) (cond (bitAt z1 1)
      (cond (bitAt z1 0) 5021681370771057353985272968232995022654518231222196423884
      1255420364615623409850516454974671393447837213241838089011)
      (cond (bitAt z1 0) 5021681392693916425211865293554065736639960408871572327628
      1255420342692764338623924129653600679462395035592462185267)))))))
def t1SoloBit (z1 z2 : ℕ) : Bool := (t1SoloRow z1).testBit z2
def t1PairBit (z1 z2 : ℕ) : Bool := (t1PairRow z1).testBit z2
def tier1W11IntCell (u1 h1 h2 q5 q31 lo1 lo2 w11 : ℕ) : ZeroNEremSector :=
  let fbKin := ZeroNEremSector.kin (mkFin234 (47 + u1)) (mkFin3 h1)
  let kinAx0 := ZeroNEremSector.kin (mkFin234 (47 + u1)) (mkFin3 0)
  let d1 := decodeUltraNuc192 (64 * h1 + lo1)
  let d2 := decodeUltraNuc192 (64 * h2 + lo2)
  let z2 := b11Z2OfHX h2 lo2
  let z1Idx := 64 * h1 + lo1
  let z2Idx := 64 * h2 + lo2
  cond (Nat.blt q31 16 || (Nat.beq q31 24 && Nat.beq q5 4) ||
        (Nat.beq q31 25 && Nat.beq q5 4 && Nat.blt w11 1452))
    (cond (d1.1 && d2.1 && Bool.not (Nat.beq u1 z2))
      (.ee d1.2 (mkFin187 (cond (Nat.blt z2 u1) z2 u1)) (mkFin187 (cond (Nat.blt z2 u1) u1 z2)))
      fbKin)
    (let cN := Nat.blt d2.2.val d1.2.val
     cond ((Nat.ble 16 q31 && Nat.blt q31 24) ||
           (Nat.beq q31 26 && Nat.beq q5 4 && Nat.blt w11 1750))
       (cond (d1.1 && d2.1 && Bool.not (Nat.beq d1.2.val d2.2.val))
         (.nn (cond cN d2.2 d1.2) (cond cN d1.2 d2.2) (mkFin187 u1))
         fbKin)
       (let enHit := Nat.ble 28 q31 ||
          (Nat.beq q31 27 && Nat.beq q5 4 &&
            (Bool.or (Bool.not (g66VOpt h2 lo2)) (Nat.blt w11 401)))
        cond enHit
          (cond d1.1 (.en d1.2 (mkFin187 u1)) fbKin)
          (cond (Nat.beq q31 27 && Nat.beq q5 3)
            (cond (Nat.beq h1 0)
              (cond (Nat.blt w11 (cond (t1SoloBit z1Idx z2Idx) 149 148)) .idle fbKin)
              (cond (Nat.beq h1 1 && Nat.blt w11 (cond (t1PairBit z1Idx z2Idx) 1944 1306))
                kinAx0
                (cond (Nat.beq h1 2 && Nat.blt w11 (cond (t1PairBit z1Idx z2Idx) 1406 2044))
                  kinAx0 fbKin)))
            fbKin)))

def decodeTier1W11Opt1424Coin (c : Fin (2 ^ 41)) : ZeroNEremSector :=
  let c5 := c.val % 32
  let lo8 := (c.val / 33554432) % 256
  let hi8 := (c.val / 33554432) / 256
  let lo10 := ((c.val / 32) % 1048576) % 1024
  let hi10 := ((c.val / 32) % 1048576) / 1024
  let b8 := cond (hi8 == 255) 0 lo8
  let w11 := c5 + 32 * (lo10 / 64) + 512 * (b8 / 64)
  let px := b2Spec (cond (hi8 == 255) (255 - lo8) hi8)
  let py := b6Spec (Nat.xor hi10 96)
  cond px.2.2.2
    (cond (Nat.blt w11 (kinNucThr9 (tier1T1bKinNucBlk hi10).2 (lo10 % 64)))
      (tier1T1bKinNucBlk hi10).1 .idle)
    (cond py.2.2.2 .idle
      (cond (hi8 == 255)
        (.kin (mkFin234 (47 + phiU1 py.1 px.1)) (mkFin3 px.2.1))
        (tier1W11IntCell (phiU1 py.1 px.1) px.2.1 py.2.1 px.2.2.1 py.2.2.1
          (b8 % 64) (lo10 % 64) w11)))

def permS8A (s : ℕ) : ℕ :=
    cond (bitAt s 7) (cond (bitAt s 6) (cond (bitAt s 5) (cond (bitAt s 4) (cond (bitAt s 3)
    (cond (bitAt s 2) (cond (bitAt s 1) (cond (bitAt s 0) (174) (175)) (cond (bitAt s 0) (173)
    (172))) (cond (bitAt s 1) (cond (bitAt s 0) (170) (171)) (cond (bitAt s 0) (169) (168))))
    (cond (bitAt s 2) (cond (bitAt s 1) (cond (bitAt s 0) (166) (167)) (cond (bitAt s 0) (165)
    (164))) (cond (bitAt s 1) (cond (bitAt s 0) (162) (163)) (cond (bitAt s 0) (161) (160)))))
    (cond (bitAt s 3) (cond (bitAt s 2) (cond (bitAt s 1) (cond (bitAt s 0) (215) (183))
    (cond (bitAt s 0) (182) (181))) (cond (bitAt s 1) (cond (bitAt s 0) (242) (243))
    (cond (bitAt s 0) (241) (240)))) (cond (bitAt s 2) (cond (bitAt s 1) (cond (bitAt s 0) (254)
    (255)) (cond (bitAt s 0) (253) (252))) (cond (bitAt s 1) (cond (bitAt s 0) (250) (251))
    (cond (bitAt s 0) (249) (248)))))) (cond (bitAt s 4) (cond (bitAt s 3) (cond (bitAt s 2)
    (cond (bitAt s 1) (cond (bitAt s 0) (238) (239)) (cond (bitAt s 0) (237) (236)))
    (cond (bitAt s 1) (cond (bitAt s 0) (234) (235)) (cond (bitAt s 0) (233) (232))))
    (cond (bitAt s 2) (cond (bitAt s 1) (cond (bitAt s 0) (222) (223)) (cond (bitAt s 0) (221)
    (220))) (cond (bitAt s 1) (cond (bitAt s 0) (218) (219)) (cond (bitAt s 0) (217) (216)))))
    (cond (bitAt s 3) (cond (bitAt s 2) (cond (bitAt s 1) (cond (bitAt s 0) (206) (207))
    (cond (bitAt s 0) (205) (204))) (cond (bitAt s 1) (cond (bitAt s 0) (202) (203))
    (cond (bitAt s 0) (201) (200)))) (cond (bitAt s 2) (cond (bitAt s 1) (cond (bitAt s 0) (190)
    (191)) (cond (bitAt s 0) (189) (188))) (cond (bitAt s 1) (cond (bitAt s 0) (186) (187))
    (cond (bitAt s 0) (185) (184))))))) (cond (bitAt s 5) (cond (bitAt s 4) (cond (bitAt s 3)
    (cond (bitAt s 2) (cond (bitAt s 1) (cond (bitAt s 0) (246) (180)) (cond (bitAt s 0) (245)
    (244))) (cond (bitAt s 1) (cond (bitAt s 0) (179) (178)) (cond (bitAt s 0) (177) (176))))
    (cond (bitAt s 2) (cond (bitAt s 1) (cond (bitAt s 0) (214) (247)) (cond (bitAt s 0) (213)
    (212))) (cond (bitAt s 1) (cond (bitAt s 0) (210) (211)) (cond (bitAt s 0) (209) (208)))))
    (cond (bitAt s 3) (cond (bitAt s 2) (cond (bitAt s 1) (cond (bitAt s 0) (230) (231))
    (cond (bitAt s 0) (229) (228))) (cond (bitAt s 1) (cond (bitAt s 0) (226) (227))
    (cond (bitAt s 0) (225) (224)))) (cond (bitAt s 2) (cond (bitAt s 1) (cond (bitAt s 0) (198)
    (199)) (cond (bitAt s 0) (197) (196))) (cond (bitAt s 1) (cond (bitAt s 0)
  (194) (195)) (cond (bitAt s 0) (193) (192)))))) (cond (bitAt s 4) (cond (bitAt s 3)
      (cond (bitAt s 2) (cond (bitAt s 1) (cond (bitAt s 0) (158) (159)) (cond (bitAt s 0) (157)
      (156))) (cond (bitAt s 1) (cond (bitAt s 0) (154) (155)) (cond (bitAt s 0) (153) (152))))
      (cond (bitAt s 2) (cond (bitAt s 1) (cond (bitAt s 0) (150) (151)) (cond (bitAt s 0) (149)
      (148))) (cond (bitAt s 1) (cond (bitAt s 0) (146) (147)) (cond (bitAt s 0) (145) (144)))))
      (cond (bitAt s 3) (cond (bitAt s 2) (cond (bitAt s 1) (cond (bitAt s 0) (142) (143))
      (cond (bitAt s 0) (141) (140))) (cond (bitAt s 1) (cond (bitAt s 0) (138) (139))
      (cond (bitAt s 0) (137) (136)))) (cond (bitAt s 2) (cond (bitAt s 1) (cond (bitAt s 0) (134)
      (135)) (cond (bitAt s 0) (133) (132))) (cond (bitAt s 1) (cond (bitAt s 0) (130) (131))
      (cond (bitAt s 0) (129) (128)))))))) (cond (bitAt s 6) (cond (bitAt s 5) (cond (bitAt s 4)
      (cond (bitAt s 3) (cond (bitAt s 2) (cond (bitAt s 1) (cond (bitAt s 0) (126) (127))
      (cond (bitAt s 0) (125) (124))) (cond (bitAt s 1) (cond (bitAt s 0) (122) (123))
      (cond (bitAt s 0) (121) (120)))) (cond (bitAt s 2) (cond (bitAt s 1) (cond (bitAt s 0) (118)
      (119)) (cond (bitAt s 0) (117) (116))) (cond (bitAt s 1) (cond (bitAt s 0) (114) (115))
      (cond (bitAt s 0) (113) (112))))) (cond (bitAt s 3) (cond (bitAt s 2) (cond (bitAt s 1)
      (cond (bitAt s 0) (110) (111)) (cond (bitAt s 0) (109) (108))) (cond (bitAt s 1)
      (cond (bitAt s 0) (106) (107)) (cond (bitAt s 0) (105) (104)))) (cond (bitAt s 2)
      (cond (bitAt s 1) (cond (bitAt s 0) (102) (103)) (cond (bitAt s 0) (101) (100)))
      (cond (bitAt s 1) (cond (bitAt s 0) (98) (99)) (cond (bitAt s 0) (97) (96))))))
      (cond (bitAt s 4) (cond (bitAt s 3) (cond (bitAt s 2) (cond (bitAt s 1) (cond (bitAt s 0) (94)
      (95)) (cond (bitAt s 0) (93) (92))) (cond (bitAt s 1) (cond (bitAt s 0) (90) (91))
      (cond (bitAt s 0) (89) (88)))) (cond (bitAt s 2) (cond (bitAt s 1) (cond (bitAt s 0) (86)
      (87)) (cond (bitAt s 0) (85) (84))) (cond (bitAt s 1) (cond (bitAt s 0) (82) (83))
      (cond (bitAt s 0) (81) (80))))) (cond (bitAt s 3) (cond (bitAt s 2) (cond (bitAt s 1)
      (cond (bitAt s 0) (78) (79)) (cond (bitAt s 0) (77) (76))) (cond (bitAt s 1) (cond (bitAt s 0)
      (74) (75)) (cond (bitAt s 0) (73) (72)))) (cond (bitAt s 2) (cond (bitAt s 1)
      (cond (bitAt s 0) (70) (71)) (cond (bitAt s 0) (69) (68))) (cond (bitAt s 1) (cond (bitAt s 0)
      (66) (67)) (cond (bitAt s 0) (65) (64)))))))
  (cond (bitAt s 5) (cond (bitAt s 4) (cond (bitAt s 3) (cond (bitAt s 2) (cond (bitAt s 1)
      (cond (bitAt s 0) (62) (63)) (cond (bitAt s 0) (61) (60))) (cond (bitAt s 1) (cond (bitAt s 0)
      (58) (59)) (cond (bitAt s 0) (57) (56)))) (cond (bitAt s 2) (cond (bitAt s 1)
      (cond (bitAt s 0) (54) (55)) (cond (bitAt s 0) (53) (52))) (cond (bitAt s 1) (cond (bitAt s 0)
      (50) (51)) (cond (bitAt s 0) (49) (48))))) (cond (bitAt s 3) (cond (bitAt s 2)
      (cond (bitAt s 1) (cond (bitAt s 0) (46) (47)) (cond (bitAt s 0) (45) (44))) (cond (bitAt s 1)
      (cond (bitAt s 0) (42) (43)) (cond (bitAt s 0) (41) (40)))) (cond (bitAt s 2)
      (cond (bitAt s 1) (cond (bitAt s 0) (38) (39)) (cond (bitAt s 0) (37) (36))) (cond (bitAt s 1)
      (cond (bitAt s 0) (34) (35)) (cond (bitAt s 0) (33) (32)))))) (cond (bitAt s 4)
      (cond (bitAt s 3) (cond (bitAt s 2) (cond (bitAt s 1) (cond (bitAt s 0) (30) (31))
      (cond (bitAt s 0) (29) (28))) (cond (bitAt s 1) (cond (bitAt s 0) (26) (27)) (cond (bitAt s 0)
      (25) (24)))) (cond (bitAt s 2) (cond (bitAt s 1) (cond (bitAt s 0) (22) (23))
      (cond (bitAt s 0) (21) (20))) (cond (bitAt s 1) (cond (bitAt s 0) (18) (19)) (cond (bitAt s 0)
      (17) (16))))) (cond (bitAt s 3) (cond (bitAt s 2) (cond (bitAt s 1) (cond (bitAt s 0) (14)
      (15)) (cond (bitAt s 0) (13) (12))) (cond (bitAt s 1) (cond (bitAt s 0) (10) (11))
      (cond (bitAt s 0) (9) (8)))) (cond (bitAt s 2) (cond (bitAt s 1) (cond (bitAt s 0) (6) (7))
      (cond (bitAt s 0) (5) (4))) (cond (bitAt s 1) (cond (bitAt s 0) (2) (3)) (cond (bitAt s 0) (1)
      (0))))))))
def invPermS8A (s : ℕ) : ℕ :=
    cond (bitAt s 7) (cond (bitAt s 6) (cond (bitAt s 5) (cond (bitAt s 4) (cond (bitAt s 3)
    (cond (bitAt s 2) (cond (bitAt s 1) (cond (bitAt s 0) (230) (231)) (cond (bitAt s 0) (229)
    (228))) (cond (bitAt s 1) (cond (bitAt s 0) (226) (227)) (cond (bitAt s 0) (225) (224))))
    (cond (bitAt s 2) (cond (bitAt s 1) (cond (bitAt s 0) (182) (191)) (cond (bitAt s 0) (189)
    (188))) (cond (bitAt s 1) (cond (bitAt s 0) (234) (235)) (cond (bitAt s 0) (233) (232)))))
    (cond (bitAt s 3) (cond (bitAt s 2) (cond (bitAt s 1) (cond (bitAt s 0) (222) (223))
    (cond (bitAt s 0) (221) (220))) (cond (bitAt s 1) (cond (bitAt s 0) (218) (219))
    (cond (bitAt s 0) (217) (216)))) (cond (bitAt s 2) (cond (bitAt s 1) (cond (bitAt s 0) (174)
    (175)) (cond (bitAt s 0) (173) (172))) (cond (bitAt s 1) (cond (bitAt s 0) (170) (171))
    (cond (bitAt s 0) (169) (168)))))) (cond (bitAt s 4) (cond (bitAt s 3) (cond (bitAt s 2)
    (cond (bitAt s 1) (cond (bitAt s 0) (214) (215)) (cond (bitAt s 0) (213) (212)))
    (cond (bitAt s 1) (cond (bitAt s 0) (210) (211)) (cond (bitAt s 0) (209) (208))))
    (cond (bitAt s 2) (cond (bitAt s 1) (cond (bitAt s 0) (239) (183)) (cond (bitAt s 0) (181)
    (180))) (cond (bitAt s 1) (cond (bitAt s 0) (178) (179)) (cond (bitAt s 0) (177) (176)))))
    (cond (bitAt s 3) (cond (bitAt s 2) (cond (bitAt s 1) (cond (bitAt s 0) (206) (207))
    (cond (bitAt s 0) (205) (204))) (cond (bitAt s 1) (cond (bitAt s 0) (202) (203))
    (cond (bitAt s 0) (201) (200)))) (cond (bitAt s 2) (cond (bitAt s 1) (cond (bitAt s 0) (166)
    (167)) (cond (bitAt s 0) (165) (164))) (cond (bitAt s 1) (cond (bitAt s 0) (162) (163))
    (cond (bitAt s 0) (161) (160))))))) (cond (bitAt s 5) (cond (bitAt s 4) (cond (bitAt s 3)
    (cond (bitAt s 2) (cond (bitAt s 1) (cond (bitAt s 0) (198) (199)) (cond (bitAt s 0) (197)
    (196))) (cond (bitAt s 1) (cond (bitAt s 0) (194) (195)) (cond (bitAt s 0) (193) (192))))
    (cond (bitAt s 2) (cond (bitAt s 1) (cond (bitAt s 0) (238) (237)) (cond (bitAt s 0) (236)
    (190))) (cond (bitAt s 1) (cond (bitAt s 0) (187) (186)) (cond (bitAt s 0) (185) (184)))))
    (cond (bitAt s 3) (cond (bitAt s 2) (cond (bitAt s 1) (cond (bitAt s 0) (254) (255))
    (cond (bitAt s 0) (253) (252))) (cond (bitAt s 1) (cond (bitAt s 0) (250) (251))
    (cond (bitAt s 0) (249) (248)))) (cond (bitAt s 2) (cond (bitAt s 1) (cond (bitAt s 0) (246)
    (247)) (cond (bitAt s 0) (245) (244))) (cond (bitAt s 1) (cond (bitAt s 0)
  (242) (243)) (cond (bitAt s 0) (241) (240)))))) (cond (bitAt s 4) (cond (bitAt s 3)
      (cond (bitAt s 2) (cond (bitAt s 1) (cond (bitAt s 0) (158) (159)) (cond (bitAt s 0) (157)
      (156))) (cond (bitAt s 1) (cond (bitAt s 0) (154) (155)) (cond (bitAt s 0) (153) (152))))
      (cond (bitAt s 2) (cond (bitAt s 1) (cond (bitAt s 0) (150) (151)) (cond (bitAt s 0) (149)
      (148))) (cond (bitAt s 1) (cond (bitAt s 0) (146) (147)) (cond (bitAt s 0) (145) (144)))))
      (cond (bitAt s 3) (cond (bitAt s 2) (cond (bitAt s 1) (cond (bitAt s 0) (142) (143))
      (cond (bitAt s 0) (141) (140))) (cond (bitAt s 1) (cond (bitAt s 0) (138) (139))
      (cond (bitAt s 0) (137) (136)))) (cond (bitAt s 2) (cond (bitAt s 1) (cond (bitAt s 0) (134)
      (135)) (cond (bitAt s 0) (133) (132))) (cond (bitAt s 1) (cond (bitAt s 0) (130) (131))
      (cond (bitAt s 0) (129) (128)))))))) (cond (bitAt s 6) (cond (bitAt s 5) (cond (bitAt s 4)
      (cond (bitAt s 3) (cond (bitAt s 2) (cond (bitAt s 1) (cond (bitAt s 0) (126) (127))
      (cond (bitAt s 0) (125) (124))) (cond (bitAt s 1) (cond (bitAt s 0) (122) (123))
      (cond (bitAt s 0) (121) (120)))) (cond (bitAt s 2) (cond (bitAt s 1) (cond (bitAt s 0) (118)
      (119)) (cond (bitAt s 0) (117) (116))) (cond (bitAt s 1) (cond (bitAt s 0) (114) (115))
      (cond (bitAt s 0) (113) (112))))) (cond (bitAt s 3) (cond (bitAt s 2) (cond (bitAt s 1)
      (cond (bitAt s 0) (110) (111)) (cond (bitAt s 0) (109) (108))) (cond (bitAt s 1)
      (cond (bitAt s 0) (106) (107)) (cond (bitAt s 0) (105) (104)))) (cond (bitAt s 2)
      (cond (bitAt s 1) (cond (bitAt s 0) (102) (103)) (cond (bitAt s 0) (101) (100)))
      (cond (bitAt s 1) (cond (bitAt s 0) (98) (99)) (cond (bitAt s 0) (97) (96))))))
      (cond (bitAt s 4) (cond (bitAt s 3) (cond (bitAt s 2) (cond (bitAt s 1) (cond (bitAt s 0) (94)
      (95)) (cond (bitAt s 0) (93) (92))) (cond (bitAt s 1) (cond (bitAt s 0) (90) (91))
      (cond (bitAt s 0) (89) (88)))) (cond (bitAt s 2) (cond (bitAt s 1) (cond (bitAt s 0) (86)
      (87)) (cond (bitAt s 0) (85) (84))) (cond (bitAt s 1) (cond (bitAt s 0) (82) (83))
      (cond (bitAt s 0) (81) (80))))) (cond (bitAt s 3) (cond (bitAt s 2) (cond (bitAt s 1)
      (cond (bitAt s 0) (78) (79)) (cond (bitAt s 0) (77) (76))) (cond (bitAt s 1) (cond (bitAt s 0)
      (74) (75)) (cond (bitAt s 0) (73) (72)))) (cond (bitAt s 2) (cond (bitAt s 1)
      (cond (bitAt s 0) (70) (71)) (cond (bitAt s 0) (69) (68))) (cond (bitAt s 1) (cond (bitAt s 0)
      (66) (67)) (cond (bitAt s 0) (65) (64)))))))
  (cond (bitAt s 5) (cond (bitAt s 4) (cond (bitAt s 3) (cond (bitAt s 2) (cond (bitAt s 1)
      (cond (bitAt s 0) (62) (63)) (cond (bitAt s 0) (61) (60))) (cond (bitAt s 1) (cond (bitAt s 0)
      (58) (59)) (cond (bitAt s 0) (57) (56)))) (cond (bitAt s 2) (cond (bitAt s 1)
      (cond (bitAt s 0) (54) (55)) (cond (bitAt s 0) (53) (52))) (cond (bitAt s 1) (cond (bitAt s 0)
      (50) (51)) (cond (bitAt s 0) (49) (48))))) (cond (bitAt s 3) (cond (bitAt s 2)
      (cond (bitAt s 1) (cond (bitAt s 0) (46) (47)) (cond (bitAt s 0) (45) (44))) (cond (bitAt s 1)
      (cond (bitAt s 0) (42) (43)) (cond (bitAt s 0) (41) (40)))) (cond (bitAt s 2)
      (cond (bitAt s 1) (cond (bitAt s 0) (38) (39)) (cond (bitAt s 0) (37) (36))) (cond (bitAt s 1)
      (cond (bitAt s 0) (34) (35)) (cond (bitAt s 0) (33) (32)))))) (cond (bitAt s 4)
      (cond (bitAt s 3) (cond (bitAt s 2) (cond (bitAt s 1) (cond (bitAt s 0) (30) (31))
      (cond (bitAt s 0) (29) (28))) (cond (bitAt s 1) (cond (bitAt s 0) (26) (27)) (cond (bitAt s 0)
      (25) (24)))) (cond (bitAt s 2) (cond (bitAt s 1) (cond (bitAt s 0) (22) (23))
      (cond (bitAt s 0) (21) (20))) (cond (bitAt s 1) (cond (bitAt s 0) (18) (19)) (cond (bitAt s 0)
      (17) (16))))) (cond (bitAt s 3) (cond (bitAt s 2) (cond (bitAt s 1) (cond (bitAt s 0) (14)
      (15)) (cond (bitAt s 0) (13) (12))) (cond (bitAt s 1) (cond (bitAt s 0) (10) (11))
      (cond (bitAt s 0) (9) (8)))) (cond (bitAt s 2) (cond (bitAt s 1) (cond (bitAt s 0) (6) (7))
      (cond (bitAt s 0) (5) (4))) (cond (bitAt s 1) (cond (bitAt s 0) (2) (3)) (cond (bitAt s 0) (1)
      (0))))))))
def permS8B (s : ℕ) : ℕ := invPermS8AToB (permS8A s)
def invPermS8B (s : ℕ) : ℕ := invPermS8A (permS8BToA s)
def permHi10KinT1bNat (h : ℕ) : ℕ := cond (Nat.ble 768 h) h (256 * (h / 256) + permS8B (h % 256))
def invPermHi10KinT1bNat (h : ℕ) : ℕ :=
    cond (Nat.ble 768 h) h (256 * (h / 256) + invPermS8B (h % 256))
theorem permHi10KinT1b_props {h : ℕ} (hh : h < 1024) :
    permHi10KinT1bNat h < 1024 ∧ invPermHi10KinT1bNat h < 1024 ∧
    invPermHi10KinT1bNat (permHi10KinT1bNat h) = h ∧ permHi10KinT1bNat (invPermHi10KinT1bNat h) =
        h ∧
    tier1T1bKinNucBlk (permHi10KinT1bNat h) = tier1WalkKinNucBlk h ∧ (tier1T1bKinNucBlk h).2 ≤
        32768 ∧
    (∀ {lo2 : ℕ}, lo2 < 64 → kinNucThr9 (tier1T1bKinNucBlk h).2 lo2 ≤ 512) ∧
    foldSum 64 (fun lo2 ↦ kinNucThr9 (tier1T1bKinNucBlk h).2 lo2) = (tier1T1bKinNucBlk h).2 ∧
    foldSum 64 (fun lo2 ↦ 512 - kinNucThr9 (tier1T1bKinNucBlk h).2 lo2) = 32768 -
        (tier1T1bKinNucBlk h).2 := by
  have cert : allTree 11 0 1024 (fun h ↦
      let ⟨p, q, lhs, rhs, t⟩ :=
          (permHi10KinT1bNat h, invPermHi10KinT1bNat h, tier1T1bKinNucBlk (permHi10KinT1bNat h),
        tier1WalkKinNucBlk h, (tier1T1bKinNucBlk h).2)
      Bool.and (Nat.blt p 1024) (Bool.and (Nat.blt q 1024)
          (Bool.and (Nat.beq (invPermHi10KinT1bNat p) h)
        (Bool.and (Nat.beq (permHi10KinT1bNat q) h) (Bool.and (eqSec lhs.1 rhs.1)
            (Bool.and (Nat.beq lhs.2 rhs.2)
          (Bool.and (Nat.ble t 32768)
              (Bool.and (allTree 7 0 64 (fun lo2 ↦ Nat.ble (kinNucThr9 t lo2) 512))
            (Bool.and (Nat.beq (foldSum 64 (fun lo2 ↦ kinNucThr9 t lo2)) t)
              (Nat.beq (foldSum 64 (fun lo2 ↦ 512 - kinNucThr9 t lo2)) (32768 - t))))))))))) =
                  true := by
    decide +kernel
  have c0 := allTree_zero cert hh
  simp only [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq, Nat.ble_eq, eqSec_iff] at c0
  rcases c0 with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  exact ⟨h1, h2, h3, h4, Prod.ext h5 h6, h7, fun hlo2 ↦ Nat.ble_eq.mp (allTree_zero h8 hlo2), h9,
      h10⟩

def equivHi10KinT1b : Fin 1024 ≃ Fin 1024 where
  toFun h := ⟨permHi10KinT1bNat h.val, (permHi10KinT1b_props h.isLt).1⟩
  invFun h := ⟨invPermHi10KinT1bNat h.val, (permHi10KinT1b_props h.isLt).2.1⟩
  left_inv h := Fin.ext (permHi10KinT1b_props h.isLt).2.2.1
  right_inv h := Fin.ext (permHi10KinT1b_props h.isLt).2.2.2.1

theorem xor1024_96_props {h : ℕ} (hh : h < 1024) : Nat.xor h 96 < 1024 ∧ Nat.xor (Nat.xor h 96) 96 =
    h := by
  have cert : allTree 11 0 1024 (fun h ↦
      Bool.and (Nat.blt (Nat.xor h 96) 1024) (Nat.beq (Nat.xor (Nat.xor h 96) 96) h)) =
          true := by decide +kernel
  have ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp (allTree_zero cert hh)
  exact ⟨Nat.blt_eq.mp h1, Nat.beq_eq.mp h2⟩

def equivXor1024_96 : Fin 1024 ≃ Fin 1024 where
  toFun h := ⟨Nat.xor h.val 96, (xor1024_96_props h.isLt).1⟩
  invFun h := ⟨Nat.xor h.val 96, (xor1024_96_props h.isLt).1⟩
  left_inv h := Fin.ext (xor1024_96_props h.isLt).2
  right_inv h := Fin.ext (xor1024_96_props h.isLt).2

theorem sum_hi10_xor96 (G : ℕ → ℕ) : (∑ hi10 : Fin 1024, G (Nat.xor hi10.val 96)) = ∑ hi10 :
    Fin 1024, G hi10.val :=
  Fintype.sum_equiv equivXor1024_96 (fun h ↦ G (equivXor1024_96 h).val) (fun h ↦ G h.val)
      (fun _ ↦ rfl)

theorem decodeTier1W11Opt1424Coin_coinOf5 {hi8 lo8 hi10 lo10 c5 : ℕ}
    (h1 : hi8 < 256) (h2 : lo8 < 256) (h3 : hi10 < 1024) (h4 : lo10 < 1024) (h5 : c5 < 32) :
    decodeTier1W11Opt1424Coin (tier1CoinOf5 hi8 lo8 hi10 lo10 c5) =
      let b8 := cond (hi8 == 255) 0 lo8
      let w11 := c5 + 32 * (lo10 / 64) + 512 * (b8 / 64)
      let px := b2Spec (cond (hi8 == 255) (255 - lo8) hi8)
      let py := b6Spec (Nat.xor hi10 96)
      cond px.2.2.2
        (cond (Nat.blt w11 (kinNucThr9 (tier1T1bKinNucBlk hi10).2 (lo10 % 64)))
          (tier1T1bKinNucBlk hi10).1 .idle)
        (cond py.2.2.2 .idle
          (cond (hi8 == 255)
            (.kin (mkFin234 (47 + phiU1 py.1 px.1)) (mkFin3 px.2.1))
            (tier1W11IntCell (phiU1 py.1 px.1) px.2.1 py.2.1 px.2.2.1 py.2.2.1
              (b8 % 64) (lo10 % 64) w11))) := by
  rcases tier1CoinOf5_digits h1 h2 h3 h4 h5 with ⟨dc5, dlo10, dhi10, dlo8, dhi8, _⟩
  unfold decodeTier1W11Opt1424Coin; dsimp only; rw [dc5, dlo10, dhi10, dlo8, dhi8]
theorem sum_a8_lt255_decodeCoin (a8 : Fin 255) (G : ZeroNEremSector → ℕ → ℕ) :
    (∑ lo8 : Fin 256, ∑ hi10 : Fin 1024, ∑ lo10 : Fin 1024, ∑ c5 : Fin 32,
      G (decodeTier1W11Opt1424Coin (tier1CoinOf5 a8.val lo8.val hi10.val lo10.val c5.val))
          (c5.val + 32 * (lo10.val / 64) + 512 * (lo8.val / 64))) =
    (∑ _lo1 : Fin 64, ∑ _lo2 : Fin 64, ∑ w11 : Fin 2048, G .idle w11.val) +
    ∑ a10 : Fin 1023, ∑ lo1 : Fin 64, ∑ lo2 : Fin 64, ∑ w11 : Fin 2048,
      G (tier1W11IntCell (phiU1 (b6Spec a10.val).1 (b2Spec a8.val).1)
          (b2Spec a8.val).2.1 (b6Spec a10.val).2.1
        (b2Spec a8.val).2.2.1 (b6Spec a10.val).2.2.1 lo1.val lo2.val w11.val) w11.val := by
  have hne8 : (a8.val == 255) = false := beq_eq_false_iff_ne.mpr (Nat.ne_of_lt a8.isLt)
  have hb2f := (b2Spec_lt255 a8.isLt).2.2.2.1
  let cell (h lo1 lo2 w11 : ℕ) := cond (b6Spec h).2.2.2 ZeroNEremSector.idle
    (tier1W11IntCell (phiU1 (b6Spec h).1 (b2Spec a8.val).1)
        (b2Spec a8.val).2.1 (b6Spec h).2.1 (b2Spec a8.val).2.2.1 (b6Spec h).2.2.1 lo1 lo2 w11)
  trans ∑ hi10 : Fin 1024, ∑ lo1 : Fin 64, ∑ lo2 : Fin 64, ∑ w11 : Fin 2048,
      G (cell hi10.val lo1.val lo2.val w11.val) w11.val
  · rw [Finset.sum_comm, ← sum_hi10_xor96 (fun h ↦ ∑ lo1 : Fin 64, ∑ lo2 : Fin 64, ∑ w11 : Fin 2048,
        G (cell h lo1.val lo2.val w11.val) w11.val)]
    refine Finset.sum_congr rfl fun hi10 _ ↦ ?_
    rw [← tier1_sum_lo8_lo10_c5_w11 (fun lo1 lo2 w11 ↦
        G (cell (Nat.xor hi10.val 96) lo1 lo2 w11) w11)]
    refine Finset.sum_congr rfl fun lo8 _ ↦ Finset.sum_congr rfl fun lo10 _ ↦
        Finset.sum_congr rfl fun c5 _ ↦ ?_
    rw [decodeTier1W11Opt1424Coin_coinOf5 (Nat.lt_trans a8.isLt (by decide)) lo8.isLt hi10.isLt
        lo10.isLt c5.isLt]
    dsimp only [cell]
    simp only [hne8, hb2f, Bool.cond_false]
  · rw [show (1024 : ℕ) = 1023 + 1 from rfl, sum_fin_add (M := 1023) (N := 1)
        (fun hi10 ↦ ∑ lo1 : Fin 64, ∑ lo2 : Fin 64, ∑ w11 : Fin 2048,
        G (cell hi10 lo1.val lo2.val w11.val) w11.val), Fin.sum_univ_one, add_comm]
    simp only [cell, Fin.val_zero, Nat.add_zero, b6Spec_1023, Bool.cond_true]
    exact congrArg₂ HAdd.hAdd rfl (Finset.sum_congr rfl fun a10 _ ↦
        by simp only [(b6Spec_lt1023 a10.isLt).2.2.2.1, Bool.cond_false])

def tier1WalkSym96TileKind (q5 q31 : ℕ) : ℕ :=
  cond (Nat.blt q31 16 || (Nat.beq q31 24 && Nat.beq q5 4)) 0
    (cond (Nat.beq q31 25 && Nat.beq q5 4) 1
      (cond (Nat.ble 16 q31 && Nat.blt q31 24) 2
        (cond (Nat.beq q31 26 && Nat.beq q5 4) 3
          (cond (Nat.ble 28 q31) 4
            (cond (Nat.beq q31 27 && Nat.beq q5 4) 5
              (cond (Nat.beq q31 27 && Nat.beq q5 3) 6 7))))))

theorem tier1WalkSym96TileKind_lt8 (q5 q31 : ℕ) : tier1WalkSym96TileKind q5 q31 <
    8 := by
  have hc {b : Bool} {x y : ℕ} (hx : x < 8) (hy : y < 8) : cond b x y < 8 := by
    cases b <;> assumption
  unfold tier1WalkSym96TileKind; exact hc (by omega)
      (hc (by omega) (hc (by omega) (hc (by omega)
    (hc (by omega) (hc (by omega) (hc (by omega) (by omega)))))))

def tier1WalkSym96TileKindMult : ℕ → ℕ
  | 0 => 81 | 1 => 1 | 2 => 40 | 3 => 1 | 4 => 15 | 5 => 1 | 6 => 1 | _ => 15

def tier1WalkSym96TileCnt31 (k q5 : ℕ) : ℕ := foldSum 31 fun q31 ↦
    cond (Nat.beq (tier1WalkSym96TileKind q5 q31) k) 1 0
theorem tier1WalkSym96TileCnt31_eq (k q5 : ℕ) : (∑ q31 : Fin 31,
    cond (Nat.beq (tier1WalkSym96TileKind q5 q31.val) k) 1 0) =
    tier1WalkSym96TileCnt31 k q5 :=
    sum_fin_eq_foldSum 31 (fun q31 ↦ cond (Nat.beq (tier1WalkSym96TileKind q5 q31) k) 1 0)
theorem check_tier1WalkSym96TileKindMult : (allTree 4 0 8 fun k ↦
    Nat.beq (foldSum 5 (tier1WalkSym96TileCnt31 k))
    (tier1WalkSym96TileKindMult k)) = true := by decide +kernel
section
attribute [local irreducible] foldSum tier1WalkSym96TileCnt31
theorem sum_q5_q31_tier1WalkSym96TileKind (V : ℕ → ℕ) :
    (∑ q5 : Fin 5, ∑ q31 : Fin 31, V (tier1WalkSym96TileKind q5.val q31.val)) =
        (81 * V 0 + V 1 + 40 * V 2 + V 3 + 15 * V 4 + V 5) + (V 6 + 15 * V 7) := by
  have hind (q5 : Fin 5) (q31 : Fin 31) : V (tier1WalkSym96TileKind q5.val q31.val) =
      ∑ k : Fin 8, cond (Nat.beq (tier1WalkSym96TileKind q5.val q31.val) k.val) 1 0 *
          V k.val := by
    symm; rw [Finset.sum_eq_single ⟨tier1WalkSym96TileKind q5.val q31.val,
        tier1WalkSym96TileKind_lt8 _ _⟩
      (fun k _ hne ↦
          by rw [tier1_nat_beq_eq_false_of_ne fun hv ↦ hne (Fin.ext hv.symm)]; exact zero_mul _)
      (fun h ↦ absurd (Finset.mem_univ _) h)]
    dsimp only; rw [Nat.beq_eq.mpr rfl]; exact one_mul _
  simp only [hind]; rw [Finset.sum_congr rfl fun q5 _ ↦ Finset.sum_comm, Finset.sum_comm]
  refine Eq.trans (b := ∑ k : Fin 8, tier1WalkSym96TileKindMult k.val * V k.val)
    (Finset.sum_congr rfl fun k _ ↦ ?_)
    (by simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero, Fin.val_succ,
      tier1WalkSym96TileKindMult]; ring)
  simp only [← Finset.sum_mul]; refine congrArg (· * V k.val)
    (Eq.trans (b := ∑ q5 : Fin 5, tier1WalkSym96TileCnt31 k.val q5.val)
      (Finset.sum_congr rfl fun q5 _ ↦ tier1WalkSym96TileCnt31_eq k.val q5.val)
      ((sum_fin_eq_foldSum 5 (tier1WalkSym96TileCnt31 k.val)).trans
        (Nat.beq_eq.mp (allTree_zero check_tier1WalkSym96TileKindMult k.isLt))))
end

def tier1W11ByKind : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ZeroNEremSector
  | 0, u1, h1, h2, lo1, lo2, _ => tier1EeTag u1 h1 h2 lo1 lo2
  | 1, u1, h1, h2, lo1, lo2, w11 =>
      cond (Nat.blt w11 1452) (tier1EeTag u1 h1 h2 lo1 lo2) (tier1FbKin u1 h1)
  | 2, u1, h1, h2, lo1, lo2, _ => tier1NnTag u1 h1 h2 lo1 lo2
  | 3, u1, h1, h2, lo1, lo2, w11 =>
      cond (Nat.blt w11 1750) (tier1NnTag u1 h1 h2 lo1 lo2) (tier1FbKin u1 h1)
  | 4, u1, h1, _, lo1, _, _ => tier1EnTag u1 h1 lo1
  | 5, u1, h1, h2, lo1, lo2, w11 =>
      cond (Bool.or (Bool.not (g66VOpt h2 lo2)) (Nat.blt w11 401))
        (tier1EnTag u1 h1 lo1) (tier1FbKin u1 h1)
  | 6, u1, h1, h2, lo1, lo2, w11 =>
      let z1Idx := 64 * h1 + lo1
      let z2Idx := 64 * h2 + lo2
      cond (Nat.beq h1 0)
        (cond (Nat.blt w11 (cond (t1SoloBit z1Idx z2Idx) 149 148)) .idle (tier1FbKin u1 h1))
        (cond (Nat.beq h1 1 && Nat.blt w11 (cond (t1PairBit z1Idx z2Idx) 1944 1306))
            (tier1FbKin u1 0)
          (cond (Nat.beq h1 2 && Nat.blt w11 (cond (t1PairBit z1Idx z2Idx) 1406 2044))
              (tier1FbKin u1 0)
            (tier1FbKin u1 h1)))
  | _, u1, h1, _, _, _, _ => tier1FbKin u1 h1

theorem tier1W11IntCell_eq_byKind (u1 h1 h2 lo1 lo2 w11 : ℕ) (q5 : Fin 5) (q31 : Fin 31) :
    tier1W11IntCell u1 h1 h2 q5.val q31.val lo1 lo2 w11 =
    tier1W11ByKind (tier1WalkSym96TileKind q5.val q31.val) u1 h1 h2 lo1 lo2 w11 := by
  unfold tier1W11IntCell; dsimp only
  rcases Nat.lt_or_ge q31.val 16 with h16 | h16
  · unfold tier1WalkSym96TileKind
    simp only [Nat.blt_eq.mpr h16, Bool.true_or, Bool.cond_true, tier1W11ByKind]; rfl
  · rcases Nat.lt_or_ge q31.val 24 with h24 | h24
    · unfold tier1WalkSym96TileKind
      simp only [Bool.eq_false_iff.mpr fun h ↦ Nat.not_lt.mpr h16 (Nat.blt_eq.mp h),
        tier1_nat_beq_eq_false_of_ne (by omega : q31.val ≠ 24),
            tier1_nat_beq_eq_false_of_ne (by omega : q31.val ≠ 25),
        Nat.ble_eq.mpr h16, Nat.blt_eq.mpr h24, Bool.false_and, Bool.false_or, Bool.true_and,
            Bool.true_or,
        Bool.cond_true, Bool.cond_false, tier1W11ByKind]; rfl
    · rcases Nat.lt_or_ge q31.val 28 with h28 | h28
      · have hq5 := q5.isLt
        rcases (show q31.val = 24 ∨ q31.val = 25 ∨ q31.val = 26 ∨ q31.val =
            27 by omega) with r31 | r31 | r31 | r31 <;>
          rcases (show q5.val = 0 ∨ q5.val = 1 ∨ q5.val = 2 ∨ q5.val = 3 ∨ q5.val =
              4 by omega) with r5 | r5 | r5 | r5 | r5 <;> rw [r31, r5] <;> rfl
      · unfold tier1WalkSym96TileKind
        simp only [Bool.eq_false_iff.mpr fun h ↦ Nat.not_lt.mpr h16 (Nat.blt_eq.mp h),
            Bool.eq_false_iff.mpr fun h ↦ Nat.not_lt.mpr h24 (Nat.blt_eq.mp h),
          tier1_nat_beq_eq_false_of_ne (by omega : q31.val ≠ 24),
              tier1_nat_beq_eq_false_of_ne (by omega : q31.val ≠ 25),
              tier1_nat_beq_eq_false_of_ne (by omega : q31.val ≠ 26),
          Nat.ble_eq.mpr h16, Nat.ble_eq.mpr h28, Bool.false_and, Bool.false_or, Bool.true_and,
          Bool.true_or, Bool.cond_true, Bool.cond_false, tier1W11ByKind]; rfl

theorem t1b_sum_w11_blt (K : ℕ) (hK : K ≤ 2048) (a b : ZeroNEremSector) (f : ZeroNEremSector → ℕ) :
    (∑ w11 : Fin 2048, f (cond (Nat.blt w11.val K) a b)) = K * f a + (2048 - K) * f b := by
  rw [tier1_sum_fin_blt_val 2048 K a b f, Nat.min_eq_right hK]
theorem cert_kind6_mat_sums : Bool.and (Nat.beq (foldSum 64 (fun lo1 ↦ foldSum 192 (fun z2 ↦
    cond ((t1SoloRow (64 * 0 + lo1)).testBit z2) 149 148))) 1824216)
    (Bool.and (Nat.beq (foldSum 64 (fun lo1 ↦ foldSum 192 (fun z2 ↦ cond ((t1SoloRow (64 * 0 +
    lo1)).testBit z2) (2048 - 149) (2048 - 148)))) 23341608)
    (Bool.and (Nat.beq (foldSum 64 (fun lo1 ↦ foldSum 192 (fun z2 ↦ cond ((t1PairRow (64 * 1 +
    lo1)).testBit z2) 1944 1306))) 20209164)
    (Bool.and (Nat.beq (foldSum 64 (fun lo1 ↦ foldSum 192 (fun z2 ↦ cond ((t1PairRow (64 * 1 +
    lo1)).testBit z2) (2048 - 1944) (2048 - 1306)))) 4956660)
    (Bool.and (Nat.beq (foldSum 64 (fun lo1 ↦ foldSum 192 (fun z2 ↦ cond ((t1PairRow (64 * 2 +
    lo1)).testBit z2) 1406 2044))) 21380544)
    (Nat.beq (foldSum 64 (fun lo1 ↦ foldSum 192 (fun z2 ↦
    cond ((t1PairRow (64 * 2 + lo1)).testBit z2) (2048 - 1406) (2048 - 2044)))) 3785280))))) =
    true := by decide +kernel
theorem validTier1WalkCoin_decodeTier1W11Opt1424Coin :
    ValidTier1WalkCoin decodeTier1W11Opt1424Coin := fun s ↦ by
  let fs (sec : ZeroNEremSector) : ℕ := cond (eqSec sec s) 1 0
  have hCard (dec : Fin (2 ^ 41) → ZeroNEremSector) :
      ((Finset.univ : Finset (Fin (2 ^ 41))).filter (fun c ↦ dec c = s)).card = ∑ c : Fin (2 ^ 41),
          fs (dec c) := by
    rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    refine Finset.sum_congr rfl fun c _ ↦ ?_
    dsimp only [fs]; cases hs : eqSec (dec c) s
    · rw [ite_eq_right (fun h ↦ Bool.noConfusion (hs.symm.trans ((eqSec_iff _ _).mpr h))),
          Bool.cond_false]
    · rw [ite_eq_left ((eqSec_iff _ _).mp hs), Bool.cond_true]
  have hSumSec : (∑ c : Fin (2 ^ 41), fs (decodeTier1W11Opt1424Coin c)) =
      (∑ u1 : Fin 187, ∑ h1 : Fin 3, ∑ h2 : Fin 3,
        (5079040 * fs (.kin (mkFin234 (47 + u1.val)) (mkFin3 h1.val)) +
         ∑ q5 : Fin 5, ∑ q31 : Fin 31, ∑ lo1 : Fin 64, ∑ lo2 : Fin 64, ∑ w11 : Fin 2048,
           fs (tier1W11IntCell u1.val h1.val h2.val q5.val q31.val lo1.val lo2.val w11.val))) +
      2147450880 * fs .idle +
      ∑ hi10 : Fin 1024, ∑ u15 : Fin 32768,
        fs (cond (Nat.blt u15.val (tier1WalkKinNucBlk hi10.val).2)
            (tier1WalkKinNucBlk hi10.val).1 .idle) := by
    rw [tier1_sum_coin41_split5 (fun c ↦ fs (decodeTier1W11Opt1424Coin c)), show (256 : ℕ) =
        255 + 1 from rfl,
      sum_fin_add (M := 255) (N := 1) (fun hi8 ↦ ∑ lo8 : Fin 256, ∑ hi10 : Fin 1024,
          ∑ lo10 : Fin 1024, ∑ c5 : Fin 32,
        fs (decodeTier1W11Opt1424Coin (tier1CoinOf5 hi8 lo8.val hi10.val lo10.val c5.val))),
            Fin.sum_univ_one]
    simp only [Fin.val_zero, Nat.add_zero]
    have hTop8 : (∑ lo8 : Fin 256, ∑ hi10 : Fin 1024, ∑ lo10 : Fin 1024, ∑ c5 : Fin 32,
        fs (decodeTier1W11Opt1424Coin (tier1CoinOf5 255 lo8.val hi10.val lo10.val c5.val))) =
        (∑ hi10 : Fin 1024, ∑ u15 : Fin 32768,
          fs (cond (Nat.blt u15.val (tier1WalkKinNucBlk hi10.val).2)
              (tier1WalkKinNucBlk hi10.val).1 .idle)) +
        (8355840 * fs .idle + ∑ a8 : Fin 255, ∑ a10 : Fin 1023,
          32768 * fs (.kin (mkFin234 (47 + phiU1 (b6Spec a10.val).1 (b2Spec a8.val).1))
            (mkFin3 (b2Spec a8.val).2.1))) := by
      rw [show (256 : ℕ) = 1 + 255 from rfl, sum_fin_add (M := 1) (N := 255) (fun lo8 ↦
        ∑ hi10 : Fin 1024, ∑ lo10 : Fin 1024, ∑ c5 : Fin 32,
          fs (decodeTier1W11Opt1424Coin (tier1CoinOf5 255 lo8 hi10.val lo10.val c5.val))),
              Fin.sum_univ_one]
      simp only [Fin.val_zero]
      refine congrArg₂ HAdd.hAdd ?_ ?_
      · let Gp (p : ZeroNEremSector × ℕ) : ℕ :=
            ∑ u15 : Fin 32768, fs (cond (Nat.blt u15.val p.2) p.1 .idle)
        have hHiEq : (∑ hi10 : Fin 1024, Gp (tier1T1bKinNucBlk hi10.val)) =
            ∑ hi10 : Fin 1024, Gp (tier1WalkKinNucBlk hi10.val) :=
          (Fintype.sum_equiv equivHi10KinT1b (fun h ↦
              Gp (tier1T1bKinNucBlk (equivHi10KinT1b h).val))
            (fun h ↦ Gp (tier1T1bKinNucBlk h.val)) (fun _ ↦ rfl)).symm.trans
            (Finset.sum_congr rfl fun h _ ↦ congrArg Gp (permHi10KinT1b_props h.isLt).2.2.2.2.1)
        have hSplit (G : ℕ → ℕ → ℕ) :
            (∑ lo10 : Fin 1024, ∑ c5 : Fin 32, G (lo10.val % 64) (c5.val + 32 * (lo10.val / 64))) =
            ∑ lo2 : Fin 64, ∑ w9 : Fin 512, G lo2.val w9.val := by
          rw [show (1024 : ℕ) = 16 * 64 from rfl, sum_fin_mul (A := 16) (B := 64) (Nat.succ_pos _)
            (fun l ↦ ∑ c5 : Fin 32, G (l % 64) (c5.val + 32 * (l / 64))), Finset.sum_comm]
          refine Finset.sum_congr rfl fun lo2 _ ↦ ?_
          rw [show (512 : ℕ) = 16 * 32 from rfl, sum_fin_mul (A := 16) (B := 32) (Nat.succ_pos _)
              (fun w ↦ G lo2.val w)]
          exact Finset.sum_congr rfl fun b4 _ ↦ Finset.sum_congr rfl fun c5 _ ↦
            congrArg₂ G ((fun _ _ ↦ by omega) lo2.isLt b4.isLt)
                ((fun _ _ _ ↦ by omega) lo2.isLt b4.isLt c5.isLt)
        rw [← hHiEq]
        refine Finset.sum_congr rfl fun hi10 _ ↦ ?_
        rcases permHi10KinT1b_props hi10.isLt with ⟨_, _, _, _, _, htLe, hThrLe, hSum1, hSum2⟩
        let a := (tier1T1bKinNucBlk hi10.val).1
        let t := (tier1T1bKinNucBlk hi10.val).2
        trans ∑ lo10 : Fin 1024, ∑ c5 : Fin 32,
          fs (cond (Nat.blt (c5.val + 32 * (lo10.val / 64)) (kinNucThr9 t (lo10.val % 64))) a .idle)
        · refine Finset.sum_congr rfl fun lo10 _ ↦ Finset.sum_congr rfl fun c5 _ ↦ ?_
          rw [decodeTier1W11Opt1424Coin_coinOf5 (by decide)
              (by decide) hi10.isLt lo10.isLt c5.isLt]
          dsimp only [a, t]; rw [show (255 == 255) = true from rfl]
          dsimp only [cond, Nat.sub_zero, Nat.zero_div, Nat.mul_zero, Nat.add_zero];
              rw [b2Spec_255]; rfl
        · rw [hSplit (fun lo2 w9 ↦ fs (cond (Nat.blt w9 (kinNucThr9 t lo2)) a .idle))]
          have hInner (lo2 : Fin 64) : (∑ w9 : Fin 512,
              fs (cond (Nat.blt w9.val (kinNucThr9 t lo2.val)) a .idle)) =
              kinNucThr9 t lo2.val * fs a + (512 - kinNucThr9 t lo2.val) * fs .idle := by
            rw [tier1_sum_fin_blt_val 512 (kinNucThr9 t lo2.val) a .idle fs,
                Nat.min_eq_right (hThrLe lo2.isLt)]
          simp only [hInner, Finset.sum_add_distrib, ← Finset.sum_mul]
          rw [sum_fin_eq_foldSum 64 (fun lo2 ↦ kinNucThr9 t lo2),
            sum_fin_eq_foldSum 64 (fun lo2 ↦ 512 - kinNucThr9 t lo2), hSum1, hSum2]
          dsimp only [Gp, a, t]; rw [tier1_sum_fin_blt_val 32768 t a .idle fs,
              Nat.min_eq_right htLe]
      · let kSec (h a8 : ℕ) : ZeroNEremSector := cond (b6Spec h).2.2.2 .idle
          (.kin (mkFin234 (47 + phiU1 (b6Spec h).1 (b2Spec a8).1)) (mkFin3 (b2Spec a8).2.1))
        have hr8 (r8 : Fin 255) : (∑ hi10 : Fin 1024, ∑ lo10 : Fin 1024, ∑ c5 : Fin 32,
            fs (decodeTier1W11Opt1424Coin (tier1CoinOf5 255 (1 +
                r8.val) hi10.val lo10.val c5.val))) =
            32768 * fs .idle + ∑ a10 : Fin 1023,
              32768 *
                  fs (.kin (mkFin234 (47 + phiU1 (b6Spec a10.val).1 (b2Spec (255 - 1 - r8.val)).1))
                (mkFin3 (b2Spec (255 - 1 - r8.val)).2.1)) := by
          have hrLt := r8.isLt
          trans ∑ hi10 : Fin 1024, 32768 * fs (kSec hi10.val (255 - 1 - r8.val))
          · rw [← sum_hi10_xor96 (fun h ↦ 32768 * fs (kSec h (255 - 1 - r8.val)))]
            refine Finset.sum_congr rfl fun hi10 _ ↦ ?_
            simp only [show ∀ (lo10 : Fin 1024) (c5 : Fin 32),
                fs (decodeTier1W11Opt1424Coin (tier1CoinOf5 255 (1 +
                    r8.val) hi10.val lo10.val c5.val)) =
                  fs (kSec (Nat.xor hi10.val 96) (255 - 1 - r8.val)) from fun lo10 c5 ↦ by
              rw [decodeTier1W11Opt1424Coin_coinOf5 (by omega)
                  (by omega) hi10.isLt lo10.isLt c5.isLt]
              dsimp only [kSec]; rw [show (255 == 255) = true from rfl]; dsimp only [cond]
              rw [(b2Spec_lt255 (show 255 - (1 + r8.val) < 255 by omega)).2.2.2.1,
                show 255 - (1 + r8.val) = 255 - 1 - r8.val by omega],
              Finset.sum_const, Finset.card_fin, smul_eq_mul]; ring
          · rw [show (1024 : ℕ) = 1023 + 1 from rfl,
              sum_fin_add (M := 1023) (N := 1)
                  (fun hi10 ↦ 32768 * fs (kSec hi10 (255 - 1 - r8.val))),
              Fin.sum_univ_one, add_comm]
            simp only [kSec, Fin.val_zero, Nat.add_zero, b6Spec_1023, Bool.cond_true]
            exact congrArg₂ HAdd.hAdd rfl
              (Finset.sum_congr rfl fun a10 _ ↦
                  by simp only [(b6Spec_lt1023 a10.isLt).2.2.2.1, Bool.cond_false])
        rw [Finset.sum_congr rfl fun r8 _ ↦ hr8 r8, Finset.sum_add_distrib,
          tier1_sum_rev_fin (N := 255) (fun a8 ↦ ∑ a10 : Fin 1023,
            32768 * fs (.kin (mkFin234 (47 + phiU1 (b6Spec a10.val).1 (b2Spec a8).1))
                (mkFin3 (b2Spec a8).2.1)))]
        simp only [Finset.sum_const, Finset.card_fin, smul_eq_mul]; ring
    have hComb : (∑ a8 : Fin 255, ∑ a10 : Fin 1023,
          32768 * fs (.kin (mkFin234 (47 + phiU1 (b6Spec a10.val).1 (b2Spec a8.val).1))
              (mkFin3 (b2Spec a8.val).2.1))) +
        (∑ a8 : Fin 255, ∑ a10 : Fin 1023, ∑ lo1 : Fin 64, ∑ lo2 : Fin 64, ∑ w11 : Fin 2048,
          fs (tier1W11IntCell (phiU1 (b6Spec a10.val).1 (b2Spec a8.val).1)
              (b2Spec a8.val).2.1 (b6Spec a10.val).2.1
            (b2Spec a8.val).2.2.1 (b6Spec a10.val).2.2.1 lo1.val lo2.val w11.val)) =
        ∑ u1 : Fin 187, ∑ h1 : Fin 3, ∑ h2 : Fin 3, (5079040 * fs (.kin (mkFin234 (47 + u1.val))
            (mkFin3 h1.val)) +
          ∑ q5 : Fin 5, ∑ q31 : Fin 31, ∑ lo1 : Fin 64, ∑ lo2 : Fin 64, ∑ w11 : Fin 2048,
            fs (tier1W11IntCell u1.val h1.val h2.val q5.val q31.val lo1.val lo2.val w11.val))
                := by
      rw [← Finset.sum_add_distrib, Finset.sum_congr rfl fun a8 _ ↦ (Finset.sum_add_distrib).symm,
        sum_a8_a10_cart254 (fun u1 h1 h2 q5 q31 ↦ 32768 * fs (.kin (mkFin234 (47 + u1))
            (mkFin3 h1)) +
          ∑ lo1 : Fin 64, ∑ lo2 : Fin 64, ∑ w11 : Fin 2048,
            fs (tier1W11IntCell u1 h1 h2 q5 q31 lo1.val lo2.val w11.val))]
      refine Finset.sum_congr rfl fun u1 _ ↦ Finset.sum_congr rfl fun h1 _ ↦
          Finset.sum_congr rfl fun h2 _ ↦ ?_
      simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_fin, smul_eq_mul]; ring
    rw [Finset.sum_congr rfl fun a8 _ ↦ sum_a8_lt255_decodeCoin a8 (fun sec _ ↦ fs sec),
        Finset.sum_add_distrib,
      hTop8, show (∑ _a8 : Fin 255, ∑ _lo1 : Fin 64, ∑ _lo2 : Fin 64, ∑ _w11 : Fin 2048, fs .idle) =
        2139095040 *
            fs .idle by simp only [Finset.sum_const, Finset.card_fin, smul_eq_mul]; ring,
            ← hComb]; ring
  have hOld := validTier1WalkCoin_decodeTier1WalkCoin s
  rw [Finset.filter_congr_decidable (p := fun c ↦ decodeTier1W11Opt1424Coin c = s), hCard]
  rw [Finset.filter_congr_decidable (p := fun c ↦ decodeTier1WalkCoin c = s), hCard] at hOld
  refine (?_ : _ = ∑ c : Fin (2 ^ 41), fs (decodeTier1WalkCoin c)).trans hOld
  rw [hSumSec, sum_decodeTier1WalkCoin_sec fs]
  refine congrArg₂ HAdd.hAdd (congrArg₂ HAdd.hAdd (Finset.sum_congr rfl fun u1 _ ↦ ?_) rfl) rfl
  simp only [Finset.sum_add_distrib]; refine congrArg₂ HAdd.hAdd rfl ?_
  let Zold (h1 h2 k : ℕ) : ℕ :=
    ∑ lo1 : Fin 64, ∑ lo2 : Fin 64, ∑ w11 : Fin 2048,
        fs (tier1WalkByKind k u1.val h1 h2 lo1.val lo2.val w11.val)
  let Zsym (h1 h2 k : ℕ) : ℕ :=
    ∑ lo1 : Fin 64, ∑ lo2 : Fin 64, ∑ w11 : Fin 2048,
        fs (tier1W11ByKind k u1.val h1 h2 lo1.val lo2.val w11.val)
  have hL (h1 h2 : Fin 3) :
      (∑ q5 : Fin 5, ∑ q31 : Fin 31, ∑ lo1 : Fin 64, ∑ lo2 : Fin 64, ∑ w11 : Fin 2048,
        fs (tier1W11IntCell u1.val h1.val h2.val q5.val q31.val lo1.val lo2.val w11.val)) =
      (81 * Zold h1.val h2.val 0 + Zold h1.val h2.val 1 + 40 * Zold h1.val h2.val 2 +
        Zold h1.val h2.val 3 + 15 * Zold h1.val h2.val 4) +
      (Zsym h1.val h2.val 5 + (Zsym h1.val h2.val 6 + 15 * Zsym h1.val h2.val 7)) := by
    simp only [tier1W11IntCell_eq_byKind]; exact (sum_q5_q31_tier1WalkSym96TileKind
      (Zsym h1.val h2.val)).trans (by
        change (81 * Zold h1.val h2.val 0 + Zold h1.val h2.val 1 + 40 * Zold h1.val h2.val 2 +
            Zold h1.val h2.val 3 +
          15 * Zold h1.val h2.val 4 + Zsym h1.val h2.val 5) + (Zsym h1.val h2.val 6 + 15 *
              Zsym h1.val h2.val 7) = _
        ring)
  have hR (h1 h2 : Fin 3) :
      (∑ q5 : Fin 5, ∑ q31 : Fin 31, ∑ lo1 : Fin 64, ∑ lo2 : Fin 64, ∑ w11 : Fin 2048,
        fs (tier1WalkIntCell u1.val h1.val h2.val q5.val q31.val lo1.val lo2.val w11.val)) =
      (81 * Zold h1.val h2.val 0 + Zold h1.val h2.val 1 + 40 * Zold h1.val h2.val 2 +
        Zold h1.val h2.val 3 + 15 * Zold h1.val h2.val 4) +
      (Zold h1.val h2.val 5 + (2 * Zold h1.val h2.val 6 + Zold h1.val h2.val 7 + 13 *
          Zold h1.val h2.val 8)) := by
    simp only [tier1WalkIntCell_eq_byKind];
        exact (sum_q5_q31_tier1WalkTileKind (Zold h1.val h2.val)).trans (by ring)
  simp only [hL, hR, Finset.sum_add_distrib];
      refine congrArg₂ HAdd.hAdd rfl (congrArg₂ HAdd.hAdd ?_ ?_)
  · refine Finset.sum_congr rfl fun h1 _ ↦ ?_
    have hK5 (cFn : ℕ → ℕ → Bool) (tFn : ℕ → ℕ) (ht : ∀ l, tFn l ≤ 2048)
        (hc : ∀ l (w : Fin 2048), cFn l w.val = Nat.blt w.val (tFn l)) :
        (∑ lo1 : Fin 64, ∑ lo2 : Fin 64, ∑ w11 : Fin 2048,
          fs (cond (cFn lo2.val w11.val) (tier1EnTag u1.val h1.val lo1.val)
              (tier1FbKin u1.val h1.val))) =
        foldSum 64 tFn * (∑ lo1 : Fin 64, fs (tier1EnTag u1.val h1.val lo1.val)) +
        foldSum 64 (fun l ↦ 2048 - tFn l) * (∑ _ : Fin 64, fs (tier1FbKin u1.val h1.val)) := by
      rw [Finset.sum_comm]
      simp only [hc, fun (lo2 lo1 : Fin 64) ↦ t1b_sum_w11_blt (tFn lo2.val) (ht lo2.val)
          (tier1EnTag u1.val h1.val lo1.val) (tier1FbKin u1.val h1.val) fs,
        Finset.sum_add_distrib, ← Finset.mul_sum]
      rw [← Finset.sum_mul, ← Finset.sum_mul, sum_fin_eq_foldSum 64 tFn,
        sum_fin_eq_foldSum 64 (fun l ↦ 2048 - tFn l)]
    let tNew (h2 l : ℕ) : ℕ := cond (g66VOpt h2 l) 401 2048
    let tOld (l : ℕ) : ℕ := cond (Nat.blt l 56) 2048 (cond (Nat.blt l 60) 1351 0)
    have hb0 (x : ℕ) : Nat.blt x 0 = false := Bool.eq_false_iff.mpr fun h ↦
        Nat.not_lt_zero _ (Nat.blt_eq.mp h)
    have hNew (h2 : Fin 3) : Zsym h1.val h2.val 5 =
        foldSum 64 (tNew h2.val) * (∑ lo1 : Fin 64, fs (tier1EnTag u1.val h1.val lo1.val)) +
        foldSum 64 (fun l ↦ 2048 - tNew h2.val l) * (∑ _ : Fin 64, fs (tier1FbKin u1.val h1.val)) :=
      hK5 (fun l w ↦ Bool.or (Bool.not (g66VOpt h2.val l)) (Nat.blt w 401)) (tNew h2.val)
        (fun l ↦ by dsimp only [tNew]; cases g66VOpt h2.val l <;> decide)
        (fun l w ↦ by dsimp only [tNew]; cases g66VOpt h2.val l <;> simp [Nat.blt_eq.mpr w.isLt])
    have hOldK5 (h2 : Fin 3) : Zold h1.val h2.val 5 =
        foldSum 64 tOld * (∑ lo1 : Fin 64, fs (tier1EnTag u1.val h1.val lo1.val)) +
        foldSum 64 (fun l ↦ 2048 - tOld l) * (∑ _ : Fin 64, fs (tier1FbKin u1.val h1.val)) :=
      hK5 (fun l w ↦ Nat.blt l 56 || (Nat.blt l 60 && Nat.blt w 1351)) tOld
        (fun l ↦ by dsimp only [tOld]; cases Nat.blt l 56 <;> cases Nat.blt l 60 <;> decide)
            (fun l w ↦ by
          dsimp only [tOld]; cases Nat.blt l 56 <;> cases Nat.blt l 60 <;>
              simp [hb0, Nat.blt_eq.mpr w.isLt])
    have hc1 : foldSum 64 (tNew 0) + foldSum 64 (tNew 1) + foldSum 64 (tNew 2) = 3 *
        foldSum 64 tOld := by
      decide +kernel
    have hc2 : foldSum 64 (fun l ↦ 2048 - tNew 0 l) + foldSum 64 (fun l ↦ 2048 - tNew 1 l) +
        foldSum 64 (fun l ↦ 2048 - tNew 2 l) = 3 * foldSum 64 (fun l ↦ 2048 - tOld l) := by
          decide +kernel
    simp only [hNew, hOldK5, Fin.sum_univ_three, Fin.val_zero, Fin.val_one, Fin.val_two]
    exact Eq.trans (b := (foldSum 64 (tNew 0) + foldSum 64 (tNew 1) + foldSum 64 (tNew 2)) *
        (∑ lo1 : Fin 64, fs (tier1EnTag u1.val h1.val lo1.val)) +
        (foldSum 64 (fun l ↦ 2048 - tNew 0 l) + foldSum 64 (fun l ↦ 2048 - tNew 1 l) +
          foldSum 64 (fun l ↦ 2048 - tNew 2 l)) * (∑ _ : Fin 64, fs (tier1FbKin u1.val h1.val)))
      (by ring) (by rw [hc1, hc2]; ring)
  · have ck6 := cert_kind6_mat_sums
    simp only [Bool.and_eq_true, Nat.beq_eq] at ck6; rcases ck6 with ⟨m0a, m0b, m1a, m1b, m2a,
        m2b⟩
    have hv23 (K : ℕ) (hK : K ≤ 8388608) (a b : ZeroNEremSector) :
        (∑ lo1 : Fin 64, ∑ lo2 : Fin 64, ∑ w11 : Fin 2048,
          fs (cond (Nat.blt (cart254V23 lo1.val lo2.val w11.val) K) a b)) = K * fs a +
              (8388608 - K) * fs b := by
      rw [tier1_sum_lo1_lo2_w11_v23 (fun v ↦ fs (cond (Nat.blt v K) a b)),
        tier1_sum_fin_blt_val 8388608 K a b fs, Nat.min_eq_right hK]
    have hMat (rFn : ℕ → ℕ) (h1 K1 K0 : ℕ) (hK1 : K1 ≤ 2048) (hK0 : K0 ≤ 2048)
        (a b : ZeroNEremSector) :
        (∑ h2 : Fin 3, ∑ lo1 : Fin 64, ∑ lo2 : Fin 64, ∑ w11 : Fin 2048,
          fs (cond (Nat.blt w11.val (cond ((rFn (64 * h1 + lo1.val)).testBit (64 * h2.val +
              lo2.val)) K1 K0)) a b)) =
        foldSum 64 (fun l1 ↦ foldSum 192 (fun z2 ↦ cond ((rFn (64 * h1 + l1)).testBit z2) K1 K0)) *
            fs a +
        foldSum 64 (fun l1 ↦ foldSum 192 (fun z2 ↦
          cond ((rFn (64 * h1 + l1)).testBit z2) (2048 - K1) (2048 - K0))) * fs b := by
      rw [Finset.sum_comm]
      have hlo1 (l1 : Fin 64) : (∑ h2 : Fin 3, ∑ l2 : Fin 64, ∑ w11 : Fin 2048,
          fs (cond (Nat.blt w11.val (cond ((rFn (64 * h1 + l1.val)).testBit (64 * h2.val +
              l2.val)) K1 K0)) a b)) =
          foldSum 192 (fun z2 ↦ cond ((rFn (64 * h1 + l1.val)).testBit z2) K1 K0) * fs a +
          foldSum 192 (fun z2 ↦ cond ((rFn (64 * h1 + l1.val)).testBit z2) (2048 - K1)
              (2048 - K0)) * fs b := by
        have hw (h2 : Fin 3) (l2 : Fin 64) : (∑ w11 : Fin 2048, fs (cond (Nat.blt w11.val
            (cond ((rFn (64 * h1 + l1.val)).testBit (64 * h2.val + l2.val)) K1 K0)) a b)) =
            cond ((rFn (64 * h1 + l1.val)).testBit (h2.val * 64 + l2.val)) K1 K0 * fs a +
            cond ((rFn (64 * h1 + l1.val)).testBit (h2.val * 64 + l2.val)) (2048 - K1)
                (2048 - K0) * fs b := by
          rw [show 64 * h2.val + l2.val = h2.val * 64 + l2.val from Nat.mul_comm 64 h2.val ▸ rfl]
          cases (rFn (64 * h1 + l1.val)).testBit (h2.val * 64 + l2.val)
          · exact t1b_sum_w11_blt K0 hK0 a b fs
          · exact t1b_sum_w11_blt K1 hK1 a b fs
        simp only [hw, Finset.sum_add_distrib, ← Finset.sum_mul]
        rw [← sum_fin_mul (A := 3) (B := 64) (Nat.succ_pos _)
            (fun z2 ↦ cond ((rFn (64 * h1 + l1.val)).testBit z2) K1 K0),
          ← sum_fin_mul (A := 3) (B := 64) (Nat.succ_pos _)
            (fun z2 ↦ cond ((rFn (64 * h1 + l1.val)).testBit z2) (2048 - K1) (2048 - K0)),
          sum_fin_eq_foldSum 192 (fun z2 ↦ cond ((rFn (64 * h1 + l1.val)).testBit z2) K1 K0),
          sum_fin_eq_foldSum 192 (fun z2 ↦ cond ((rFn (64 * h1 + l1.val)).testBit z2) (2048 - K1)
              (2048 - K0))]
      simp only [hlo1, Finset.sum_add_distrib, ← Finset.sum_mul]
      rw [sum_fin_eq_foldSum 64 (fun l1 ↦ foldSum 192 (fun z2 ↦
          cond ((rFn (64 * h1 + l1)).testBit z2) K1 K0)),
        sum_fin_eq_foldSum 64 (fun l1 ↦ foldSum 192 (fun z2 ↦
          cond ((rFn (64 * h1 + l1)).testBit z2) (2048 - K1) (2048 - K0)))]
    have ⟨hb00, hb01, hb02, hb10, hb11, hb12, hb20, hb21, hb22⟩ :
        Nat.beq 0 0 = true ∧ Nat.beq 0 1 = false ∧ Nat.beq 0 2 = false ∧ Nat.beq 1 0 = false ∧
            Nat.beq 1 1 = true ∧
        Nat.beq 1 2 = false ∧ Nat.beq 2 0 = false ∧ Nat.beq 2 1 = false ∧ Nat.beq 2 2 = true :=
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    rw [show (∑ h1 : Fin 3, ∑ h2 : Fin 3, Zsym h1.val h2.val 6) =
          (1824216 * fs .idle + 23341608 * fs (tier1FbKin u1.val 0)) +
          (20209164 * fs (tier1FbKin u1.val 0) + 4956660 * fs (tier1FbKin u1.val 1)) +
          (21380544 * fs (tier1FbKin u1.val 0) + 3785280 * fs (tier1FbKin u1.val 2)) by
      rw [Fin.sum_univ_three]
      dsimp only [Fin.val_zero, Fin.val_one, Fin.val_two, Zsym, tier1W11ByKind, t1SoloBit,
          t1PairBit]
      simp only [hb00, hb01, hb02, hb10, hb11, hb12, hb20, hb21, hb22, Bool.true_and,
          Bool.false_and,
        Bool.cond_true, Bool.cond_false]
      rw [hMat t1SoloRow 0 149 148 (by omega) (by omega) .idle (tier1FbKin u1.val 0), m0a, m0b,
        hMat t1PairRow 1 1944 1306 (by omega) (by omega) (tier1FbKin u1.val 0)
            (tier1FbKin u1.val 1), m1a, m1b,
        hMat t1PairRow 2 1406 2044 (by omega) (by omega) (tier1FbKin u1.val 0)
            (tier1FbKin u1.val 2), m2a, m2b]]
    simp only [Fin.sum_univ_three, Fin.val_zero, Fin.val_one, Fin.val_two]
    dsimp only [Zsym, Zold, tier1W11ByKind, tier1WalkByKind]
    simp only [hb00, hb01, hb02, hb10, hb11, hb12, hb20, hb21, hb22, Bool.true_and, Bool.false_and,
      Bool.cond_true, Bool.cond_false, hv23 3431948 (by omega), hv23 2779112 (by omega),
      hv23 1824216 (by omega), Finset.sum_const, Finset.card_fin, smul_eq_mul]; ring

theorem t1b_cond_ne_of_ne {b : Bool} {x y s : ZeroNEremSector} (hx : x ≠ s)
    (hy : y ≠ s) : cond b x y ≠ s := by cases b <;> assumption

theorem kinNucBlkT1b_fst_ne {s : ZeroNEremSector} (hNot : (∀ i ax, s ≠ .kin i ax) ∧ s ≠ .idle)
    (h : ℕ) : (tier1T1bKinNucBlk h).1 ≠ s := by
  have hk : ∀ m ax, ZeroNEremSector.kin (mkFin234 m) ax ≠ s := fun _ _ hEq ↦ hNot.1 _ _ hEq.symm
  have hi : ZeroNEremSector.idle ≠ s := fun hEq ↦ hNot.2 hEq.symm
  have hp {α β} (b : Bool) (x y : α × β) : (cond b x y).1 = cond b x.1 y.1 := by cases b <;> rfl
  unfold tier1T1bKinNucBlk tier1T1bKinNucS8 tier1WalkKinNucS8T1a tier1WalkKinNucS8T1aHi
     ; dsimp only
  repeat rw [hp]
  exact t1b_cond_ne_of_ne hi (t1b_cond_ne_of_ne (hk _ _) (t1b_cond_ne_of_ne (hk _ _)
      (t1b_cond_ne_of_ne (hk _ _)
    (t1b_cond_ne_of_ne hi (t1b_cond_ne_of_ne (hk _ _)
        (t1b_cond_ne_of_ne (t1b_cond_ne_of_ne hi (hk _ _))
      (t1b_cond_ne_of_ne (hk _ _) (t1b_cond_ne_of_ne (hk _ _) (t1b_cond_ne_of_ne (hk _ _)
        (t1b_cond_ne_of_ne (hk _ _) (hk _ _)))))))))))

def flipCoinHi10_96 (c : Fin (2 ^ 41)) : Fin (2 ^ 41) :=
    tier1CoinOf5 ((c.val / 33554432) / 256) ((c.val / 33554432) % 256)
    (Nat.xor (((c.val / 32) % 1048576) / 1024) 96) (((c.val / 32) % 1048576) % 1024) (c.val % 32)
theorem card_ee_nn_w11_t1b_eq_tier1Walk {s : ZeroNEremSector}
    (hNot : ((∀ i ax, s ≠ .kin i ax) ∧ s ≠ .idle) ∧ ∀ n1 e1, s ≠ .en n1 e1) (w : ℕ) :
    ((Finset.univ : Finset (Fin (2 ^ 41))).filter (fun c ↦ decodeTier1W11Opt1424Coin c = s ∧
        w11NatOfCoin c = w)).card =
      ((Finset.univ : Finset (Fin (2 ^ 41))).filter (fun c ↦ decodeTier1WalkCoin c = s ∧
          w11NatOfCoin c = w)).card := by
  have hFlip (c : Fin (2 ^ 41)) : (w11NatOfCoin (flipCoinHi10_96 c) = w11NatOfCoin c ∧
      flipCoinHi10_96 (flipCoinHi10_96 c) = c) ∧
      ((decodeTier1W11Opt1424Coin c = s) ↔ (decodeTier1WalkCoin (flipCoinHi10_96 c) = s))
          := by
    have hcLt := c.isLt
    have h3 := xor1024_96_props (show ((c.val / 32) % 1048576) / 1024 < 1024 by omega)
    rcases tier1CoinOf5_digits (show (c.val / 33554432) / 256 < 256 by omega)
      (show (c.val / 33554432) % 256 < 256 by omega) h3.1
      (show ((c.val / 32) % 1048576) % 1024 < 1024 by omega)
      (show c.val % 32 < 32 by omega) with ⟨dc5, dlo10, dhi10, dlo8, dhi8, dm10⟩
    refine ⟨⟨by unfold w11NatOfCoin flipCoinHi10_96; rw [dc5, dm10, dlo8]; omega,
      by
        unfold flipCoinHi10_96; rw [dhi8, dlo8, dhi10, h3.2, dlo10, dc5];
        apply Fin.ext; dsimp only [tier1CoinOf5, tier1PackCoin5]; omega⟩, ?_⟩
    unfold decodeTier1W11Opt1424Coin decodeTier1WalkCoin flipCoinHi10_96; dsimp only
    rw [dc5, dlo10, dhi10, dlo8, dhi8]
    cases (b2Spec (cond ((c.val / 33554432) / 256 == 255) (255 - (c.val / 33554432) % 256)
      ((c.val / 33554432) / 256))).2.2.2 <;> dsimp only [cond]
    · cases (b6Spec (Nat.xor (((c.val / 32) % 1048576) / 1024) 96)).2.2.2 <;> dsimp only [cond]
      · cases ((c.val / 33554432) / 256 == 255) <;> dsimp only [cond]
        · rw [tier1WalkIntCell_eq_raw]; unfold tier1W11IntCell; dsimp only
          have hSame {b : Bool} {t e1 e2 : ZeroNEremSector} (he : (e1 = s) ↔ (e2 = s)) :
              (cond b t e1 = s) ↔ (cond b t e2 = s) := by
                cases b <;> first | exact he | exact Iff.rfl
          refine hSame (hSame ?_)
          have hk : ∀ u1 ax, tier1FbKin u1 ax ≠ s := fun _ _ h ↦ hNot.1.1 _ _ h.symm
          have hi : ZeroNEremSector.idle ≠ s := fun h ↦ hNot.1.2 h.symm
          have hen (u1 h1 lo1 : ℕ) : tier1EnTag u1 h1 lo1 ≠ s := by
            unfold tier1EnTag tier1FbKin; exact t1b_cond_ne_of_ne (fun h ↦ hNot.2 _ _ h.symm)
                (hk u1 h1)
          exact ⟨fun h ↦ absurd h (t1b_cond_ne_of_ne (t1b_cond_ne_of_ne (fun e ↦ hNot.2 _ _ e.symm)
              (hk _ _))
              (t1b_cond_ne_of_ne (t1b_cond_ne_of_ne (t1b_cond_ne_of_ne hi (hk _ _))
                (t1b_cond_ne_of_ne (hk _ 0) (t1b_cond_ne_of_ne (hk _ 0) (hk _ _)))) (hk _ _))),
            fun h ↦
                absurd h (t1b_cond_ne_of_ne (hen _ _ _) (t1b_cond_ne_of_ne (hk _ 0)
                (t1b_cond_ne_of_ne
              (t1b_cond_ne_of_ne (hk _ 0) (t1b_cond_ne_of_ne (hk _ 0)
                  (t1b_cond_ne_of_ne hi (hk _ _)))) (hk _ _))))⟩
        · exact Iff.rfl
      · exact Iff.rfl
    · exact ⟨fun hL ↦ absurd hL (t1b_cond_ne_of_ne (kinNucBlkT1b_fst_ne hNot.1 _)
          (fun h ↦ hNot.1.2 h.symm)),
        fun hR ↦
            absurd hR (t1b_cond_ne_of_ne ((permHi10KinT1b_props h3.1).2.2.2.2.1 ▸
            kinNucBlkT1b_fst_ne hNot.1 _)
          (fun h ↦ hNot.1.2 h.symm))⟩
  refine Finset.card_bij (fun c _ ↦ flipCoinHi10_96 c)
    (fun c hc ↦ Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        (hFlip c).2.mp (Finset.mem_filter.mp hc).2.1,
      (hFlip c).1.1.trans (Finset.mem_filter.mp hc).2.2⟩)
    (fun c1 _ c2 _ hEq ↦
        (hFlip c1).1.2.symm.trans ((congrArg flipCoinHi10_96 hEq).trans (hFlip c2).1.2))
    fun d hd ↦
        ⟨flipCoinHi10_96 d, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        (hFlip (flipCoinHi10_96 d)).2.mpr
      ((hFlip d).1.2.symm ▸ (Finset.mem_filter.mp hd).2.1),
          (hFlip d).1.1.trans (Finset.mem_filter.mp hd).2.2⟩,
      (hFlip d).1.2⟩

theorem fib_ee_t1b_w11Nat_eq_cntEE2048 (n1 : Fin 47) (e1 e2 : Fin 187) {w : ℕ}
    (hw : w < 2048) : ((Finset.univ : Finset (Fin (2 ^ 41))).filter (fun c ↦
    decodeTier1W11Opt1424Coin c = .ee n1 e1 e2 ∧ w11NatOfCoin c = w)).card = if e1 <
    e2 then cntEE2048Tier1Walk (nucSpecies n1) w else 0 :=
    (card_ee_nn_w11_t1b_eq_tier1Walk ⟨⟨fun _ _ ↦ ZeroNEremSector.noConfusion,
    ZeroNEremSector.noConfusion⟩, fun _ _ ↦
    ZeroNEremSector.noConfusion⟩ w).trans (fib_ee_tier1Walk_w11Nat_eq_cntEE2048 n1 e1 e2 hw)
theorem fib_nn_t1b_w11Nat_eq_cntNN2048 (n1 n2 : Fin 47) (e1 : Fin 187) {w : ℕ} (hw : w < 2048) :
    ((Finset.univ : Finset (Fin (2 ^ 41))).filter (fun c ↦ decodeTier1W11Opt1424Coin c =
        .nn n1 n2 e1 ∧ w11NatOfCoin c = w)).card =
      if n1 < n2 then cntNN2048Tier1Walk (nucSpecies n1) (nucSpecies n2) w else 0 :=
  (card_ee_nn_w11_t1b_eq_tier1Walk ⟨⟨fun _ _ ↦ ZeroNEremSector.noConfusion,
      ZeroNEremSector.noConfusion⟩, fun _ _ ↦
      ZeroNEremSector.noConfusion⟩ w).trans (fib_nn_tier1Walk_w11Nat_eq_cntNN2048 n1 n2 e1 hw)

-- ============================================================================
-- Section 4. `.en` `w11` Fiber (`3072` vs `3052`) & Stratified Block Bridge
-- ============================================================================

theorem cert_g66_en_counts :
    Bool.and (Nat.beq (foldSum 64 (fun lo2 ↦ cond (Bool.not (g66VOpt 0 lo2)) 1 0)) 48)
    (Bool.and (Nat.beq (foldSum 64 (fun lo2 ↦ cond (Bool.not (g66VOpt 1 lo2)) 1 0)) 62)
    (Nat.beq (foldSum 64 (fun lo2 ↦ cond (Bool.not (g66VOpt 2 lo2)) 1 0)) 62)) =
    true := by decide +kernel

section UltraNucSumIrred
attribute [local irreducible] foldSum
theorem sum_h1_lo1_ultraNuc_mul (n1 : Fin 47) (K : ℕ) : (∑ h1 : Fin 3, ∑ lo1 : Fin 64,
    cond ((decodeUltraNuc192 (h1.val * 64 + lo1.val)).1 &&
    ((decodeUltraNuc192 (h1.val * 64 + lo1.val)).2 == n1)) K 0) = speciesZ (nucSpecies n1) * K := by
  rw [← sum_fin_mul (A := 3) (B := 64) (Nat.succ_pos _)
      (fun z1 ↦ cond ((decodeUltraNuc192 z1).1 && ((decodeUltraNuc192 z1).2 == n1)) K 0),
    sum_fin_eq_foldSum 192 (fun z1 ↦ cond ((decodeUltraNuc192 z1).1 &&
        ((decodeUltraNuc192 z1).2 == n1)) K 0), foldSum_cond_const, ultraNucCnt_eq]
end UltraNucSumIrred

theorem fib_en_t1b_w11Nat_eq_cntEN2048 (n1 : Fin 47) (e1 : Fin 187) {w : ℕ} (hw : w < 2048) :
    ((Finset.univ : Finset (Fin (2 ^ 41))).filter (fun c ↦ decodeTier1W11Opt1424Coin c =
        .en n1 e1 ∧ w11NatOfCoin c = w)).card = cntEN2048Tier1 (nucSpecies n1) w := by
  have he1 : (mkFin187 e1.val == e1) = true := beq_iff_eq.mpr (mkFin187_of_lt e1.isLt)
  have hIdle : ZeroNEremSector.en n1 e1 ≠ .idle := fun h ↦ by cases h
  have hKin : ∀ i ax, ZeroNEremSector.en n1 e1 ≠ .kin i ax := fun _ _ h ↦ by cases h
  have hPotCard : ((Finset.univ : Finset (Fin (2 ^ 41))).filter
      (fun c ↦ decodeTier1W11Opt1424Coin c = .en n1 e1 ∧ w11NatOfCoin c = w)).card =
      ∑ u1 : Fin 187, ∑ h1 : Fin 3, ∑ h2 : Fin 3, ∑ q5 : Fin 5, ∑ q31 : Fin 31, ∑ lo1 : Fin 64,
          ∑ lo2 : Fin 64,
        cond (eqSec (tier1W11IntCell u1.val h1.val h2.val q5.val q31.val lo1.val lo2.val w)
            (.en n1 e1)) 1 0 := by
    let H c : ℕ :=
        cond (eqSec (decodeTier1W11Opt1424Coin c) (.en n1 e1) && (w11NatOfCoin c == w)) 1 0
    have hNe0 (sec : ZeroNEremSector) (hne : sec ≠ .en n1 e1) : eqSec sec (.en n1 e1) = false :=
      Bool.eq_false_iff.mpr fun h ↦ hne ((eqSec_iff _ _).mp h)
    rw [Finset.card_eq_sum_ones, Finset.sum_filter, Finset.sum_congr rfl fun c _ ↦ show _ = H c by
        dsimp only [H]; cases hs : eqSec (decodeTier1W11Opt1424Coin c) (.en n1 e1)
        · rw [ite_eq_right (fun h ↦ nomatch hs.symm.trans ((eqSec_iff _ _).mpr h.1)),
              Bool.false_and, Bool.cond_false]
        · cases hw0 : (w11NatOfCoin c == w)
          · rw [ite_eq_right (fun h ↦ nomatch hw0.symm.trans (beq_iff_eq.mpr h.2)), Bool.and_false,
                Bool.cond_false]
          · rw [ite_eq_left ⟨(eqSec_iff _ _).mp hs, beq_iff_eq.mp hw0⟩, Bool.and_true,
                Bool.cond_true],
      tier1_sum_coin41_split5 H, show (256 : ℕ) = 255 + 1 from rfl, sum_fin_add (M := 255) (N := 1)
        (fun hi8 ↦ ∑ lo8 : Fin 256, ∑ hi10 : Fin 1024, ∑ lo10 : Fin 1024, ∑ c5 : Fin 32,
          H (tier1CoinOf5 hi8 lo8.val hi10.val lo10.val c5.val)), Fin.sum_univ_one,
      show (∑ lo8 : Fin 256, ∑ hi10 : Fin 1024, ∑ lo10 : Fin 1024, ∑ c5 : Fin 32,
          H (tier1CoinOf5 (255 + (0 : Fin 1).val) lo8.val hi10.val lo10.val c5.val)) = 0 from
        Finset.sum_eq_zero fun lo8 _ ↦ Finset.sum_eq_zero fun hi10 _ ↦
            Finset.sum_eq_zero fun lo10 _ ↦
          Finset.sum_eq_zero fun c5 _ ↦ by
            dsimp only [H, Fin.val_zero, Nat.add_zero]
            rw [hNe0 _ (by
              rw [decodeTier1W11Opt1424Coin_coinOf5 (by omega) lo8.isLt hi10.isLt lo10.isLt
                  c5.isLt]; dsimp only
              rw [show (255 == 255) = true from rfl, Bool.cond_true]
              exact t1b_cond_ne_of_ne (t1b_cond_ne_of_ne (kinNucBlkT1b_fst_ne ⟨hKin,
                  hIdle⟩ hi10.val)
                (fun h ↦ hIdle h.symm)) (t1b_cond_ne_of_ne (fun h ↦ hIdle h.symm)
                    (fun h ↦ hKin _ _ h.symm))),
              Bool.false_and, Bool.cond_false],
      Nat.add_zero, Finset.sum_congr rfl fun (a8 : Fin 255) _ ↦ show _ =
          ∑ a10 : Fin 1023, ∑ lo1 : Fin 64, ∑ lo2 : Fin 64, cond (eqSec (tier1W11IntCell
            (phiU1 (b6Spec a10.val).1 (b2Spec a8.val).1) (b2Spec a8.val).2.1 (b6Spec a10.val).2.1
            (b2Spec a8.val).2.2.1 (b6Spec a10.val).2.2.1 lo1.val lo2.val w) (.en n1 e1)) 1 0 by
        dsimp only [H]
        simp only [fun (lo8 : Fin 256) (hi10 lo10 : Fin 1024) (c5 : Fin 32) ↦
          w11NatOfCoin_tier1CoinOf5 (Nat.lt_trans a8.isLt (by decide)) lo8.isLt hi10.isLt lo10.isLt
              c5.isLt]
        rw [sum_a8_lt255_decodeCoin a8 (fun sec w11 ↦ cond (eqSec sec (.en n1 e1) &&
            (w11 == w)) 1 0)]
        simp only [hNe0 .idle (fun h ↦ hIdle h.symm), Bool.false_and, Bool.cond_false,
            Finset.sum_const_zero, zero_add]
        refine Finset.sum_congr rfl fun a10 _ ↦ Finset.sum_congr rfl fun lo1 _ ↦
            Finset.sum_congr rfl fun lo2 _ ↦ ?_
        rw [Finset.sum_eq_single ⟨w, hw⟩
            (fun u _ hne ↦ by rw [beq_eq_false_iff_ne.mpr fun hv ↦ hne (Fin.ext hv),
          Bool.and_false, Bool.cond_false]) (fun h ↦ absurd (Finset.mem_univ _) h)]
        simp only [beq_self_eq_true, Bool.and_true]]
    exact sum_a8_a10_cart254 (fun u1 h1 h2 q5 q31 ↦
      ∑ a : Fin 64, ∑ b : Fin 64, cond (eqSec (tier1W11IntCell u1 h1 h2 q5 q31 a.val b.val w)
          (.en n1 e1)) 1 0)
  have hKindZero {k : ℕ} (hk8 : k < 8) (hk4 : k ≠ 4) (hk5 : k ≠ 5) (u1 h1 h2 lo1 lo2 : ℕ) :
      eqSec (tier1W11ByKind k u1 h1 h2 lo1 lo2 w) (.en n1 e1) = false := by
    have hCond {a b} (c : Bool) (ha : eqSec a (.en n1 e1) = false)
        (hb : eqSec b (.en n1 e1) = false) :
        eqSec (cond c a b) (.en n1 e1) = false := by cases c <;> assumption
    have hee0 : eqSec (tier1EeTag u1 h1 h2 lo1 lo2) (.en n1 e1) = false := by
      unfold tier1EeTag tier1FbKin; dsimp only; exact hCond _ rfl rfl
    have hnn0 : eqSec (tier1NnTag u1 h1 h2 lo1 lo2) (.en n1 e1) = false := by
      unfold tier1NnTag tier1FbKin; dsimp only; exact hCond _ rfl rfl
    rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 6 ∨ k =
        7 by omega) with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [tier1W11ByKind] <;> first
        | exact hee0 | exact hCond _ hee0 rfl | exact hnn0 | exact hCond _ hnn0 rfl
        | exact hCond _ (hCond _ rfl rfl) (hCond _ rfl (hCond _ rfl rfl)) | rfl
  have hu1Ne (u1 : Fin 187) (hne : u1 ≠ e1) :
      (∑ h1 : Fin 3, ∑ h2 : Fin 3, ∑ q5 : Fin 5, ∑ q31 : Fin 31, ∑ lo1 : Fin 64, ∑ lo2 : Fin 64,
        cond (eqSec (tier1W11IntCell u1.val h1.val h2.val q5.val q31.val lo1.val lo2.val w)
            (.en n1 e1)) 1 0) = 0 :=
    Finset.sum_eq_zero fun h1 _ ↦ Finset.sum_eq_zero fun h2 _ ↦ Finset.sum_eq_zero fun q5 _ ↦
      Finset.sum_eq_zero fun q31 _ ↦ Finset.sum_eq_zero fun lo1 _ ↦ Finset.sum_eq_zero fun lo2 _ ↦
          by
        rw [tier1W11IntCell_eq_byKind]
        have hk8 := tier1WalkSym96TileKind_lt8 q5.val q31.val
        generalize tier1WalkSym96TileKind q5.val q31.val = k at hk8 ⊢
        by_cases hk45 : k = 4 ∨ k = 5
        · have hen0 : eqSec (tier1EnTag u1.val h1.val lo1.val) (.en n1 e1) = false := by
            unfold tier1EnTag tier1FbKin; dsimp only; cases (decodeUltraNuc192 (64 * h1.val +
                lo1.val)).1
            · rfl
            · dsimp only [cond, eqSec]; rw [mkFin187_of_lt u1.isLt, beq_eq_false_iff_ne.mpr hne,
                  Bool.and_false]
          rcases hk45 with rfl | rfl <;> simp only [tier1W11ByKind]
          · rw [hen0, Bool.cond_false]
          · cases Bool.or (Bool.not (g66VOpt h2.val lo2.val)) (Nat.blt w 401) <;>
              first | rfl | rw [Bool.cond_true, hen0, Bool.cond_false]
        · rw [hKindZero hk8 (fun e ↦ hk45 (Or.inl e)) (fun e ↦ hk45 (Or.inr e)), Bool.cond_false]
  have hCell (h1 h2 : Fin 3) :
      (∑ q5 : Fin 5, ∑ q31 : Fin 31, ∑ lo1 : Fin 64, ∑ lo2 : Fin 64,
        cond (eqSec (tier1W11IntCell e1.val h1.val h2.val q5.val q31.val lo1.val lo2.val w)
            (.en n1 e1)) 1 0) =
      ∑ lo1 : Fin 64, cond ((decodeUltraNuc192 (h1.val * 64 + lo1.val)).1 &&
        ((decodeUltraNuc192 (h1.val * 64 + lo1.val)).2 == n1))
        (960 + ∑ lo2 : Fin 64, cond (Bool.or (Bool.not (g66VOpt h2.val lo2.val))
            (Nat.blt w 401)) 1 0) 0 := by
    simp only [tier1W11IntCell_eq_byKind]
    let Z (k : ℕ) : ℕ := ∑ lo1 : Fin 64, ∑ lo2 : Fin 64,
      cond (eqSec (tier1W11ByKind k e1.val h1.val h2.val lo1.val lo2.val w) (.en n1 e1)) 1 0
    have hzOth {k : ℕ} (hk8 : k < 8) (hk4 : k ≠ 4) (hk5 : k ≠ 5) : Z k = 0 :=
      Finset.sum_eq_zero fun _ _ ↦ Finset.sum_eq_zero fun _ _ ↦ by
        rw [hKindZero hk8 hk4 hk5, Bool.cond_false]
    rw [sum_q5_q31_tier1WalkSym96TileKind Z,
      hzOth (by decide) (by decide) (by decide : 0 ≠ 5), hzOth (by decide) (by decide)
          (by decide : 1 ≠ 5),
      hzOth (by decide) (by decide) (by decide : 2 ≠ 5), hzOth (by decide) (by decide)
          (by decide : 3 ≠ 5),
      hzOth (by decide) (by decide) (by decide : 6 ≠ 5), hzOth (by decide) (by decide)
          (by decide : 7 ≠ 5),
      show (81 * 0 + 0 + 40 * 0 + 0 + 15 * Z 4 + Z 5) + (0 + 15 * 0) = 15 * Z 4 + Z 5 by ring]
    dsimp only [Z]; rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun lo1 _ ↦ ?_
    have hz1e : 64 * h1.val + lo1.val = h1.val * 64 + lo1.val := Nat.mul_comm 64 h1.val ▸ rfl
    simp only [tier1W11ByKind]; unfold tier1EnTag tier1FbKin; dsimp only; rw [hz1e]
    have hZeroSec (sec : ZeroNEremSector) (h0 : eqSec sec (.en n1 e1) = false) :
        15 * (∑ _ : Fin 64, cond (eqSec sec (.en n1 e1)) 1 0) + (∑ lo2 : Fin 64,
          cond (eqSec (cond (Bool.or (Bool.not (g66VOpt h2.val lo2.val)) (Nat.blt w 401))
            sec (.kin (mkFin234 (47 + e1.val)) (mkFin3 h1.val))) (.en n1 e1)) 1 0) = 0 := by
      rw [Finset.sum_eq_zero fun _ _ ↦ by rw [h0]; rfl, Finset.sum_eq_zero fun lo2 _ ↦ by
        cases Bool.or (Bool.not (g66VOpt h2.val lo2.val)) (Nat.blt w 401)
        · rfl
        · rw [Bool.cond_true, h0]; rfl, mul_zero, add_zero]
    cases hd1 : (decodeUltraNuc192 (h1.val * 64 + lo1.val)).1
    · simp only [Bool.false_and, Bool.cond_false]; exact hZeroSec (.kin (mkFin234 (47 + e1.val))
          (mkFin3 h1.val)) rfl
    · simp only [Bool.true_and, Bool.cond_true]
      cases hn : ((decodeUltraNuc192 (h1.val * 64 + lo1.val)).2 == n1)
      · simp only [Bool.cond_false]; exact hZeroSec (.en (decodeUltraNuc192 (h1.val * 64 +
            lo1.val)).2
          (mkFin187 e1.val)) (by dsimp only [eqSec]; rw [hn]; rfl)
      · rw [beq_iff_eq.mp hn]; simp only [Bool.cond_true]
        have hfe : cond (eqSec (.en n1 (mkFin187 e1.val)) (.en n1 e1)) 1 0 = 1 := by
          dsimp only [eqSec]; rw [beq_self_eq_true, he1]; rfl
        have hc5 (lo2 : Fin 64) : cond (eqSec (cond (Bool.or (Bool.not (g66VOpt h2.val lo2.val))
            (Nat.blt w 401))
            (.en n1 (mkFin187 e1.val)) (.kin (mkFin234 (47 + e1.val)) (mkFin3 h1.val)))
                (.en n1 e1)) 1 0 =
            cond (Bool.or (Bool.not (g66VOpt h2.val lo2.val)) (Nat.blt w 401)) 1 0 := by
          cases Bool.or (Bool.not (g66VOpt h2.val lo2.val)) (Nat.blt w 401) <;> first
            | rfl
            | exact hfe
        simp only [Finset.sum_const, Finset.card_fin, smul_eq_mul]
        rw [hfe, mul_one, show 15 * 64 = 960 from rfl, Finset.sum_congr rfl fun lo2 _ ↦ hc5 lo2]
  rw [hPotCard, Finset.sum_eq_single e1 (fun u1 _ hne ↦ hu1Ne u1 hne)
      (fun h ↦ absurd (Finset.mem_univ _) h),
    Finset.sum_congr rfl fun h1 _ ↦ Finset.sum_congr rfl fun h2 _ ↦ hCell h1 h2]
  have hh1 (h1 : Fin 3) :
      (∑ h2 : Fin 3, ∑ lo1 : Fin 64, cond ((decodeUltraNuc192 (h1.val * 64 + lo1.val)).1 &&
        ((decodeUltraNuc192 (h1.val * 64 + lo1.val)).2 == n1))
        (960 + ∑ lo2 : Fin 64, cond (Bool.or (Bool.not (g66VOpt h2.val lo2.val))
            (Nat.blt w 401)) 1 0) 0) =
      ∑ lo1 : Fin 64, cond ((decodeUltraNuc192 (h1.val * 64 + lo1.val)).1 &&
        ((decodeUltraNuc192 (h1.val * 64 + lo1.val)).2 == n1))
            (3052 + 20 * if w < 401 then 1 else 0) 0 := by
    rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun lo1 _ ↦ ?_
    cases (decodeUltraNuc192 (h1.val * 64 + lo1.val)).1 &&
        ((decodeUltraNuc192 (h1.val * 64 + lo1.val)).2 == n1)
    · simp only [Bool.cond_false, Finset.sum_const_zero]
    · simp only [Bool.cond_true]
      by_cases hw401 : w < 401
      · simp only [hw401, ↓reduceIte, Nat.blt_eq.mpr hw401, Bool.or_true, Bool.cond_true,
            Finset.sum_const,
          Finset.card_fin, smul_eq_mul]
      · have hb : Nat.blt w 401 = false := Bool.eq_false_iff.mpr fun h ↦ hw401 (Nat.blt_eq.mp h)
        rcases Bool.and_eq_true_iff.mp cert_g66_en_counts with ⟨c0, cg⟩
        rcases Bool.and_eq_true_iff.mp cg with ⟨c1, c2⟩
        simp only [hw401, ↓reduceIte, hb, Bool.or_false, Fin.sum_univ_three, Fin.val_zero,
            Fin.val_one, Fin.val_two]
        rw [sum_fin_eq_foldSum 64 (fun lo2 ↦ cond (Bool.not (g66VOpt 0 lo2)) 1 0),
          sum_fin_eq_foldSum 64 (fun lo2 ↦ cond (Bool.not (g66VOpt 1 lo2)) 1 0),
          sum_fin_eq_foldSum 64 (fun lo2 ↦ cond (Bool.not (g66VOpt 2 lo2)) 1 0),
          Nat.beq_eq.mp c0, Nat.beq_eq.mp c1, Nat.beq_eq.mp c2]
  unfold cntEN2048Tier1
  rw [Finset.sum_congr rfl fun h1 _ ↦ hh1 h1,
    sum_h1_lo1_ultraNuc_mul n1 (3052 + 20 * if w < 401 then 1 else 0), tier1_speciesZ_eq_mSp]

/--
Closed `0x000` -polarity 13-sector `W11` stratified coin certificate for
`decodeTier1W11Opt1424Coin` .
-/
theorem validOuterW11_decodeTier1W11Opt1424Coin :
    ValidOuterW11StratifiedCoin wEESpeciesTier1Walk wNNSpeciesTier1Walk wENSpeciesTier1Walk
    wKinTier1Walk totalSlotsIdleTier1Walk cntEETier1Walk cntNNTier1Walk cntENTier1
    decodeTier1W11Opt1424Coin :=
  validOuterW11_of_nat w11NatOfCoin_lt2048 w11NatOfCoin_testBit
      validTier1WalkCoin_decodeTier1W11Opt1424Coin
    sum_cntEE2048Tier1Walk sum_cntNN2048Tier1Walk sum_cntEN2048Tier1
    (fun n1 e1 e2 {_} hw ↦ fib_ee_t1b_w11Nat_eq_cntEE2048 n1 e1 e2 hw)
    (fun n1 n2 e1 {_} hw ↦ fib_nn_t1b_w11Nat_eq_cntNN2048 n1 n2 e1 hw)
        (fun n1 e1 {_} hw ↦ fib_en_t1b_w11Nat_eq_cntEN2048 n1 e1 hw)
end QuantumComputation.Specs.PhotochemistrySolution.Stage1CoinDecode
end

end
