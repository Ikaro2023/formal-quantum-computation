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

public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.NarrowTempPhase

@[expose] public section
set_option allowUnsafeReducibility true

namespace QuantumComputation.Specs.StoppingPowerSolution
open SpecsAux

section PosTailWithAnchor18_244_p2
local instance (priority := 1000000) instNeZeroTwoPow_PosTailWithAnchor18_244_p2 (k : ℕ) :
    NeZero (2 ^ k) := ⟨(Nat.two_pow_pos k).ne'⟩

/-
# Anchor-Assisted Unbarreled `244`-Clean-Wire Tail+Slack (`PosTailWithAnchor18_244`)

Implements `dPosTailWithAnchor18_244` (`24,432 T`, `0` `.TOFF`, `244 <= mScr`) on active register
`rCore.concat rAnchor18 hCA` (`posCoreWires + 18` wires):
- `dPartnerLoad216` (`8,648 T`, `0` `.TOFF`) loading `partnerTblVal216` into `rPartner18`,
- unheld `2 x dSingleEqSwap` (`2 x 124 = 248 T`, `0` `.TOFF`) swapping `rPartner18 <-> rAnchor18`,
- `269`-wire hoisted `dOrbitSandHoisted60_244` (`1,124 T`) around `28`-column `53`-AND
  `dMidTailPhaseMux2T53PolyDyn` (`13,576 T` at `150 <= mClean`, `k_drop = 3`
  `liftTailMag27` / `roundTailMag27`),
- `X`-measurement uncompute `dMeasPhaseFix123` + `dPartnerPhaseFix216` (`<= 836 T`, `0` `.TOFF`).
-/

public section

namespace PosTailWithAnchor18_244

section ConfigPosTailWithAnchor18_244

set_option backward.isDefEq.respectTransparency true
set_option exponentiation.threshold 256
set_option maxRecDepth 4096

open Operator QProg Matrix _root_.DynamicCircuit DynCircuitExt HermitianMat Real
open scoped Matrix ComplexOrder MatrixOrder BigOperators Circuit.Notation
open SpecsAux.SpecMirror
open Dyadic128CoulombMath
    PosSlots24BranchConcrete
open CanonRank7Circuit hiding count_copyXorRegCircuit_toff
open MeasureBranchHadamardSem (projZeroAll ket_projZeroAll)
open MeasureBranchHadamardSem (toffoli_eval_sq)
open StreamingBchComparator (PreservesStoreConst)
open TempPhaseProg
open PosSlots24SpectatorPrunedPhase
open PosSlots24PartnerMux288 hiding sandPhase18
open PosSlots24OrbitToggleFast288 hiding dite_pos dite_neg ite_pos ite_neg
    rawOrbitCoord128 orbitRankFin16 matrix_ext_ket basisBits_symm_apply_at
open PosSlots24PartnerMuxZeroT123 (toDynWithDyn)

section SandAndTailScope
open MeasureBranchHadamardSem (ket matrix_ext_ket ket_TOFF)
open OctahedralOrbit hiding ket eval_seq_mulVec ket_X ket_CNOT ket_TOFF
    matrix_ext_ket ket_projector_zero

/- ## Section 3: `269`-Wire Hoisted `OrbitToggle60` (`dOrbitSandHoisted60_244`, `1,124 + tMid`
  `.T`) -/

/-- Stage-1 (`60`-wire `[60 .. 120)`, `57`-`TempAnd` = `228 T`) prefix of `orbitToggleCtx177`. -/
def orbitTogglePrefix60 (slot2SwappedTo0 : Bool) : TempCtx 303 :=
  (ctxAxisFold7 slot2SwappedTo0 0).append
    ((ctxAxisFold7 slot2SwappedTo0 1).append (ctxAxisFold7 slot2SwappedTo0 2))

theorem orbitTogglePrefix60_countTempAnd (slot2SwappedTo0 : Bool) : (orbitTogglePrefix60
    slot2SwappedTo0).countTempAnd = 57 := by
  simp [orbitTogglePrefix60, tempCtx_append_count]

theorem TempCtx.fwdBits_congr_nonMut {M : ℕ} {mutW : Wire M →
    Prop} {K : TempCtx M} (hDisj : K.DisjointFrom mutW) : ∀ {β₁ β₂ : BitAssignment M},
    (∀ w, ¬ mutW w → β₁ w = β₂ w) → ∀ w, ¬ mutW w → K.fwdBits β₁ w = K.fwdBits β₂ w := by
  induction K with
  | hole => exact fun {_ _} hEq w hw ↦ hEq w hw
  | seqPre _ _ ih => exact fun {_ _} hEq ↦ ih hDisj.2 (hDisj.1.eval_congr_nonMut hEq)
  | seqPost _ _ ih => exact fun {_ _} hEq ↦ ih hDisj.1 hEq
  | tempAnd c₁ c₂ anc _ _ _ _ ih =>
      refine fun {_ _} hEq ↦ ih hDisj.2.2.2 fun u hu ↦ ?_
      by_cases hua : u = anc
      · subst hua
        simp [Function.update_self, hEq u hDisj.2.2.1, hEq c₁ hDisj.1, hEq c₂ hDisj.2.1]
      · simp [Function.update_of_ne hua, hEq u hu]

theorem TempCtx.append_assoc {M : ℕ} :
    ∀ (F G H : TempCtx M), (F.append G).append H = F.append (G.append H)
  | .hole, _, _ => rfl
  | .seqPre _ F, G, H => by simp [TempCtx.append, TempCtx.append_assoc F G H]
  | .seqPost F _, G, H => by simp [TempCtx.append, TempCtx.append_assoc F G H]
  | .tempAnd _ _ _ _ _ _ F, G, H => by simp [TempCtx.append, TempCtx.append_assoc F G H]

private theorem writeRegProg_helpers {M n : ℕ} (rComb : QRegister M n) : (∀ (β : BitAssignment n) (f
    g : BitAssignment M),
    writeRegProg (writeRegProg β rComb f) rComb g = writeRegProg β rComb g) ∧
        (∀ (β : BitAssignment n) (f : BitAssignment M),
    (fun idx ↦ writeRegProg β rComb f (rComb idx)) = f) ∧ (∀ β : BitAssignment n,
        writeRegProg β rComb (fun idx ↦ β (rComb idx)) = β) ∧
    (∀ (β : BitAssignment n) (f : BitAssignment M) (q : Wire M) (x : ZMod 2),
        Function.update (writeRegProg β rComb f) (rComb q) x =
    writeRegProg β rComb (Function.update f q x)) := by
  refine ⟨fun β f g ↦ funext fun w ↦ ?_,
    fun _ _ ↦ funext fun idx ↦ writeRegProg_apply_reg _ _ _ idx,
    fun β ↦ funext fun w ↦ ?_, fun β f q x ↦ funext fun w ↦ ?_⟩
  · rcases Classical.em (w ∈ Set.range rComb.wires) with ⟨idx, rfl⟩ | hm
    · simp [writeRegProg_apply_reg]
    · simp [writeRegProg_apply_of_not_mem _ _ _ _ hm]
  · rcases Classical.em (w ∈ Set.range rComb.wires) with ⟨idx, rfl⟩ | hm
    · exact writeRegProg_apply_reg _ _ _ _
    · exact writeRegProg_apply_of_not_mem _ _ _ _ hm
  · by_cases hm : w ∈ Set.range rComb.wires
    · obtain ⟨idx, rfl⟩ := hm
      by_cases hia : idx = q
      · subst hia
        simp [Function.update_self, writeRegProg_apply_reg]
      · simp [Function.update_of_ne (rComb.wires.injective.ne hia),
          Function.update_of_ne hia, writeRegProg_apply_reg]
    · rw [Function.update_of_ne (fun h ↦ hm ⟨q, h.symm⟩),
        writeRegProg_apply_of_not_mem _ _ _ _ hm, writeRegProg_apply_of_not_mem _ _ _ _ hm]

private theorem ketPredProj_mul_absorb {n : ℕ} [NeZero (2 ^ n)] {P Q : BitAssignment n →
    Prop} {V : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ}
    (h : ∀ β, P β → ∃ (c : ℂ) (γ : BitAssignment n), V.mulVec (ket β) = c • ket γ ∧ Q γ) :
    p2t_ketPredProj Q * (V * p2t_ketPredProj P) = V * p2t_ketPredProj P ∧
        p2t_ketPredProj P * Vᴴ * p2t_ketPredProj Q = p2t_ketPredProj P * Vᴴ := by
  have h1 : p2t_ketPredProj Q * (V * p2t_ketPredProj P) = V * p2t_ketPredProj P := by
    classical
    apply MeasureBranchHadamardSem.matrix_ext_ket
    intro β
    rw [mbh_ket_eq_ket, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, p2t_ketPredProj_mul_ket]
    by_cases hp : P β
    · obtain ⟨c, γ, hV, hq⟩ := h β hp
      rw [ite_eq_left hp, ← mbh_ket_eq_ket, hV, Matrix.mulVec_smul, mbh_ket_eq_ket,
          p2t_ketPredProj_mul_ket, ite_eq_left hq]
    · rw [ite_eq_right hp, Matrix.mulVec_zero, Matrix.mulVec_zero]
  refine ⟨h1, ?_⟩
  simpa only [Matrix.conjTranspose_mul, p2t_ketPredProj_conjTranspose, Matrix.mul_assoc] using
    congrArg conjTranspose h1

def S_cleanCtxPred {M n : ℕ} (rComb : QRegister M n) (P_fwd : BitAssignment M → Prop)
    (S_ext : BitAssignment n → Prop) (K : TempCtx M) (rem : ℕ) (hrem : rem ≤ M)
    (β : BitAssignment n) : Prop := (∀ j : Fin rem, β (tailScr rComb rem hrem j) = 0) ∧ P_fwd
    (K.fwdBits (fun idx ↦ β (rComb idx))) ∧ S_ext β

set_option maxHeartbeats 400000 in
-- Structural induction over TempCtx with clean-ancilla QHL conjugation.
private theorem p2t_realizes_toDynWithDyn_gen {Var : Type} [Fintype Var] [DecidableEq Var] {M n : ℕ}
    [NeZero (2 ^ n)] (v : Var) (rComb : QRegister M n)
    (P_fwd : BitAssignment M → Prop) (S_ext : BitAssignment n →
        Prop) (hExtComb : ∀ (β : BitAssignment n) (f : BitAssignment M),
    S_ext (writeRegProg β rComb f) ↔ S_ext β) (remHole : ℕ) (hremHole : remHole ≤ M) (probe :
        TempPhaseProg M)
    (hProbeRem : ∀ rem, ValidCleanRem M rem probe → remHole ≤ rem) (hProbeBits : ∀ γ : BitAssignment
        M, probe.evalBits γ = γ) (inner : DynamicCircuit Var n)
    (U₀ : Unitary (2 ^ n)) (hInner : p2t_RealizesConstCleanUnitary (p2t_ketPredProj (S_cleanCtxPred
        rComb P_fwd S_ext .hole remHole hremHole)) inner U₀)
    (sgn₀ : BitAssignment n → ℂ) (step₀ : BitAssignment n →
        BitAssignment n) (hStepFixComb : ∀ (β : BitAssignment n) (idx : Fin M),
    step₀ β (rComb idx) = β (rComb idx)) (hInnerKet : ∀ β : BitAssignment n, U₀.1.mulVec (ket β) =
        sgn₀ β • ket (step₀ β)) :
    ∀ (K : TempCtx M) (rem : ℕ) (hrem : rem ≤ M), ValidCleanRem M rem (K.plug probe) →
        ∃ U : Unitary (2 ^ n), p2t_RealizesConstCleanUnitary
    (p2t_ketPredProj (S_cleanCtxPred rComb P_fwd S_ext K rem hrem)) (toDynWithDyn v rComb inner K) U
        ∧ ∀ β : BitAssignment n, U.1.mulVec (ket β) =
    sgn₀ (writeRegProg β rComb (K.fwdBits (fun idx ↦ β (rComb idx)))) •
    ket (writeRegProg (step₀ (writeRegProg β rComb (K.fwdBits (fun idx ↦
        β (rComb idx))))) rComb ((K.plug probe).evalBits (fun idx ↦ β (rComb idx)))) := by
  obtain ⟨hwidem, hread, hw_self, hWriteUpd⟩ := writeRegProg_helpers rComb
  have hWriteQ (β : BitAssignment n) (q : Wire M) (x : ZMod 2) : Function.update β (rComb q) x =
      writeRegProg β rComb (Function.update (fun idx ↦ β (rComb idx)) q x) := by
    conv_lhs => rw [← hw_self β]
    exact hWriteUpd β _ q x
  have hw_step (β : BitAssignment n) :
      writeRegProg (step₀ β) rComb (fun idx ↦ β (rComb idx)) = step₀ β := funext fun w ↦ by
    by_cases hm : w ∈ Set.range rComb.wires
    · obtain ⟨idx, rfl⟩ := hm
      exact (writeRegProg_apply_reg _ _ _ _).trans (hStepFixComb β idx).symm
    · exact writeRegProg_apply_of_not_mem _ _ _ _ hm
  have hcKet (c : CliffProg M) (β : BitAssignment n) : (c.onRegister rComb).toCircuit.eval.1.mulVec
      (ket β) =
      ket (writeRegProg β rComb (c.eval (fun idx ↦ β (rComb idx)))) :=
    (eval_onRegister_prog_ket rComb (.cliff c) β).trans
      (by simp [TempPhaseProg.evalSign, TempPhaseProg.evalBits])
  have tailSub {r₁ r₂ : ℕ} {hr₁ : r₁ ≤ M} {hr₂ : r₂ ≤ M} (hle : r₁ ≤ r₂) (j : Fin r₁) :
      tailScr rComb r₁ hr₁ j = tailScr rComb r₂ hr₂ ⟨(r₂ - r₁) + j.val, by omega⟩ :=
    congrArg rComb.wires (Fin.ext (by dsimp; omega))
  have cleanOfTail {r : ℕ} {hr : r ≤ M} {β : BitAssignment n}
      (hz : ∀ j : Fin r, β (tailScr rComb r hr j) = 0) :
      cleanRem M r (fun idx ↦ β (rComb idx)) := fun w hw ↦ by
    rw [show w = ⟨(M - r) + (w.val - (M - r)), by omega⟩ by ext; dsimp; omega]
    exact hz ⟨w.val - (M - r), by omega⟩
  intro K
  induction K with
  | hole =>
      intro rem hrem hv
      refine ⟨U₀, p2t_RealizesConstCleanUnitary_mono_proj
        (p2t_ketPredProj_conjTranspose (S_cleanCtxPred rComb P_fwd S_ext .hole remHole hremHole))
        (p2t_ketPredProj_conjTranspose _)
        (p2t_ketPredProj_mul_imp fun β hs ↦
          ⟨fun j ↦ (congrArg β (tailSub (hProbeRem rem hv) j)).trans (hs.1 _),
            hs.2.1, hs.2.2⟩) hInner, fun β ↦ ?_⟩
      dsimp only [TempCtx.fwdBits, TempCtx.plug]
      rw [hProbeBits, hw_self, hw_step]
      exact hInnerKet β
  | seqPre c K₁ ih =>
      intro rem hrem ⟨remMid, hmid, _, hv₁, hpres₁⟩
      obtain ⟨U₁, hReal₁, hKet₁⟩ := ih remMid hmid hv₁
      let cPre := (c.onRegister rComb).toCircuit
      have hclean := (ketPredProj_mul_absorb (V := cPre.eval.1)
        (P := S_cleanCtxPred rComb P_fwd S_ext (.seqPre c K₁) rem hrem)
        (Q := S_cleanCtxPred rComb P_fwd S_ext K₁ remMid hmid) fun β hs ↦
        ⟨1, _, (hcKet c β).trans (one_smul _ _).symm, fun j ↦ by
          dsimp [tailScr]
          rw [writeRegProg_apply_reg]
          exact hpres₁ _ (cleanOfTail hs.1) ⟨(M - remMid) + j.val, by omega⟩
            (by dsimp; omega),
          by rw [hread]; exact hs.2.1, (hExtComb β _).mpr hs.2.2⟩).1
      refine ⟨U₁ * cPre.eval, p2t_RealizesConstCleanUnitary_seq_proj
        (p2t_ketPredProj_conjTranspose _) (p2t_ketPredProj_conjTranspose _)
        (p2t_RealizesConstCleanUnitary_circuit _ cPre) hReal₁ hclean, fun β ↦ ?_⟩
      rw [Submonoid.coe_mul, ← Matrix.mulVec_mulVec, hcKet c β, hKet₁, hread, hwidem]
      rfl
  | seqPost K₁ c ih =>
      intro rem hrem ⟨_, _, hv₁, _, _⟩
      obtain ⟨U₁, hReal₁, hKet₁⟩ := ih rem hrem hv₁
      let cPost := (c.onRegister rComb).toCircuit
      have hP2_one : p2t_ketPredProj (fun _ : BitAssignment n ↦ True) = 1 := by
        classical
        ext i j
        by_cases hij : i = j
        all_goals simp [p2t_ketPredProj, Matrix.diagonal, Matrix.one_apply, hij]
      refine ⟨cPost.eval * U₁, p2t_RealizesConstCleanUnitary_seq_proj
        (p2t_ketPredProj_conjTranspose _) (p2t_ketPredProj_conjTranspose _) hReal₁
        (p2t_RealizesConstCleanUnitary_circuit _ cPost) (by rw [hP2_one, Matrix.one_mul]),
        fun β ↦ ?_⟩
      rw [Submonoid.coe_mul, ← Matrix.mulVec_mulVec, hKet₁, Matrix.mulVec_smul, hcKet c, hread,
          hwidem]
      rfl
  | tempAnd c₁ c₂ anc h₁₂ h₁a h₂a K₁ ih =>
      intro rem hrem ⟨hanc_lo, hvBody, hpresBody⟩
      have hanc_lt : anc.val < M := anc.isLt
      let rem' := M - (anc.val + 1)
      have hrem' : rem' ≤ M := by omega
      obtain ⟨U_body, ihBody, hKetBody⟩ := ih rem' hrem' hvBody
      have h₁₂' := rComb.wires.injective.ne h₁₂
      have h₁a' := rComb.wires.injective.ne h₁a
      have h₂a' := rComb.wires.injective.ne h₂a
      let T_anc := (Circuit.TOFF (rComb c₁) (rComb c₂) (rComb anc) h₁₂' h₁a' h₂a').eval
      let U_clean := T_anc * U_body * T_anc
      let K_and := TempCtx.tempAnd c₁ c₂ anc h₁₂ h₁a h₂a K₁
      have hCleanKet (β : BitAssignment n) : U_clean.1.mulVec (ket β) =
          sgn₀ (writeRegProg β rComb (K_and.fwdBits (fun idx ↦ β (rComb idx)))) •
          ket (writeRegProg (step₀ (writeRegProg β rComb (K_and.fwdBits (fun idx ↦ β (rComb idx)))))
          rComb ((K_and.plug probe).evalBits (fun idx ↦ β (rComb idx)))) := by
        simp only [U_clean, Submonoid.coe_mul, ← Matrix.mulVec_mulVec]
        dsimp only [T_anc]
        rw [ket_TOFF, hKetBody, hWriteQ β anc, hread, hwidem, Matrix.mulVec_smul, ket_TOFF,
          hWriteUpd, writeRegProg_apply_reg, writeRegProg_apply_reg, writeRegProg_apply_reg]
        rfl
      let S_pre := S_cleanCtxPred rComb P_fwd S_ext K_and rem hrem
      let S_post := S_cleanCtxPred rComb P_fwd S_ext K₁ rem' hrem'
      let P_pre := p2t_ketPredProj S_pre
      let P_post := p2t_ketPredProj S_post
      let P₀ := (QRegister.singleton (rComb anc)).basisOutcomeProjector 0
      let dBody := toDynWithDyn v rComb inner K₁
      let dUncomp := DynamicCircuit.andUncompute v (rComb c₁) (rComb c₂) (rComb anc) h₁₂'
      let dSeq := DynamicCircuit.seq
        (DynamicCircuit.andCompute (rComb c₁) (rComb c₂) (rComb anc) h₁a' h₂a')
        (DynamicCircuit.seq dBody dUncomp)
      have hAncZero (β : BitAssignment n) (hs : S_pre β) : β (rComb anc) = 0 := by
        rw [show rComb anc = tailScr rComb rem hrem ⟨anc.val - (M - rem), by omega⟩ from
          congrArg rComb.wires (Fin.ext (by dsimp; omega))]
        exact hs.1 _
      have hP₀_eq : P₀ = p2t_ketPredProj (fun β ↦ β (rComb anc) = 0) := by
        apply MeasureBranchHadamardSem.matrix_ext_ket
        intro β
        classical
        rw [mbh_ket_eq_ket, p2t_ket_projector_zero, p2t_ketPredProj_mul_ket]
      have hP₀_pre : P₀ * P_pre = P_pre :=
        (congrArg (· * P_pre) hP₀_eq).trans (p2t_ketPredProj_mul_imp hAncZero)
      have hPre_P₀ : P_pre * P₀ = P_pre :=
        (congrArg (P_pre * ·) hP₀_eq).trans (p2t_ketPredProj_mul_imp_right hAncZero)
      obtain ⟨hPost_T_pre, hPre_Tadj_Post⟩ :
          P_post * (T_anc.1 * P_pre) = T_anc.1 * P_pre ∧
          P_pre * T_anc.1ᴴ * P_post = P_pre * T_anc.1ᴴ :=
        ketPredProj_mul_absorb (V := T_anc.1) (P := S_pre) (Q := S_post) fun β hs ↦ by
          refine ⟨1, _, by
              dsimp only [T_anc]
              rw [ket_TOFF, one_smul],
            fun j ↦ ?_, by
              rw [hWriteQ, hread]
              exact hs.2.1,
            by
              rw [hWriteQ]
              exact (hExtComb β _).mpr hs.2.2⟩
          have hne : tailScr rComb rem' hrem' j ≠ rComb anc := fun h ↦ by
            have hinj := congrArg Fin.val (rComb.wires.injective h)
            dsimp [tailScr, rem'] at hinj
            omega
          exact (Function.update_of_ne hne _ _).trans
            ((congrArg β (tailSub (by omega : rem' ≤ rem) j)).trans (hs.1 _))
      obtain ⟨hP₀_U_pre, hPre_Uadj_P₀⟩ :
          P₀ * (U_clean.1 * P_pre) = U_clean.1 * P_pre ∧
          P_pre * U_clean.1ᴴ * P₀ = P_pre * U_clean.1ᴴ := by
        rw [hP₀_eq]
        refine ketPredProj_mul_absorb (V := U_clean.1) (P := S_pre)
          (Q := fun β ↦ β (rComb anc) = 0) fun β hs ↦ ⟨_, _, hCleanKet β, ?_⟩
        let γ : BitAssignment M := fun idx ↦ β (rComb idx)
        let β₁ := Function.update γ anc (γ anc + γ c₁ * γ c₂)
        obtain ⟨hc₁, hc₂, ha⟩ := hpresBody β₁ fun w hw ↦
          (Function.update_of_ne (wire_ne_of_gt (by omega)) _ _).trans
            (cleanOfTail hs.1 w (by omega))
        rw [writeRegProg_apply_reg]
        dsimp only [K_and, TempCtx.plug, TempPhaseProg.evalBits]
        change Function.update ((K₁.plug probe).evalBits β₁) anc _ anc = 0
        rw [Function.update_self, ha, hc₁, hc₂]
        have hγ_anc : γ anc = 0 := hAncZero β hs
        simp [β₁, hγ_anc, Function.update_self, Function.update_of_ne h₁a,
          Function.update_of_ne h₂a, CharTwo.add_self_eq_zero]
      have hUT_pre : U_body.1 * (T_anc.1 * P_pre) = T_anc.1 * (U_clean.1 * P_pre) := by
        have h : U_body * T_anc = T_anc * U_clean := by
          dsimp only [U_clean]
          rw [← mul_assoc, ← mul_assoc, MeasureBranchHadamardSem.toffoli_eval_sq _ _ _ h₁₂' h₁a'
              h₂a', one_mul]
        rw [← Matrix.mul_assoc, show U_body.1 * T_anc.1 = T_anc.1 * U_clean.1 by
          simpa only [Submonoid.coe_mul] using congrArg Subtype.val h, Matrix.mul_assoc]
      have hPre_TU_adj : (P_pre * T_anc.1ᴴ) * U_body.1ᴴ = (P_pre * U_clean.1ᴴ) * T_anc.1ᴴ := by
        have hPreH : P_preᴴ = P_pre := p2t_ketPredProj_conjTranspose S_pre
        simpa only [Matrix.conjTranspose_mul, hPreH, Matrix.mul_assoc]
          using congrArg conjTranspose hUT_pre
      refine ⟨U_clean, ⟨PreservesStoreConst.seq (PreservesStoreConst.circuit _)
        (PreservesStoreConst.seq ihBody.1
          (PreservesStoreConst.andUncompute v (rComb c₁) (rComb c₂) (rComb anc) h₁₂')),
        fun M_obs σ ↦ ?_⟩, hCleanKet⟩
      obtain ⟨M_uncomp, hUncomp_wp⟩ :=
        PreservesStoreConst.andUncompute v (rComb c₁) (rComb c₂) (rComb anc) h₁₂' M_obs
      obtain ⟨M_body, hBody_wp⟩ := ihBody.1 M_uncomp
      have hStep1 : P₀ * (wp dSeq.compile (fun _ ↦ M_obs) σ).1.1 * P₀ =
          P₀ * (T_anc.1ᴴ * M_body.1.1 * T_anc.1) * P₀ := by
        have hRaw := congrArg HermitianMat.mat (congrArg Subtype.val (congrFun
          (restrictToZeroAncilla_wp_andCompute_seq_compat
            (rComb c₁) (rComb c₂) (rComb anc) h₁₂' h₁a' h₂a'
            (.qSeq dBody.compile dUncomp.compile) (fun _ ↦ M_obs)) σ))
        have hSeq : wp (.qSeq dBody.compile dUncomp.compile) (fun _ ↦ M_obs) =
            fun _ ↦ M_body := funext fun τ ↦ by
          change wp dBody.compile (wp dUncomp.compile (fun _ ↦ M_obs)) τ = M_body
          rw [hUncomp_wp, hBody_wp]
        rw [hSeq] at hRaw
        simp only [CQAssertion.restrictToZeroAncilla, CQAssertion.conj, T_anc, P₀, dSeq,
            QRegister.basisOutcomeProjector_conjTranspose, DynamicCircuit.compile_seq,
          HermitianMat.conj_apply_mat, wpQAssignCompat, qAssignObsMap, Observable.conj_coe,
          Unitary.coe_star, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose,
              Matrix.mul_assoc] at hRaw ⊢
        exact hRaw
      have hStepUncomp : P₀ * (T_anc.1ᴴ * M_uncomp.1.1 * T_anc.1) * P₀ = P₀ * M_obs.1.1 * P₀ := by
        have hRaw := congrArg HermitianMat.mat (congrArg Subtype.val (congrFun
          (restrictAssertionToZeroAncilla_wpQAssign_toffoli_wp_andUncompute_of_update_eq
            v (rComb c₁) (rComb c₂) (rComb anc) h₁₂' h₁a' h₂a'
            (fun _ ↦ M_obs) (fun _ _ ↦ rfl)) σ))
        rw [hUncomp_wp] at hRaw
        simp only [CQAssertion.restrictToZeroAncilla, CQAssertion.conj, T_anc, P₀,
            QRegister.basisOutcomeProjector_conjTranspose, HermitianMat.conj_apply_mat,
          wpQAssignCompat, qAssignObsMap, Observable.conj_coe, Unitary.coe_star,
              Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose,
          Matrix.mul_assoc] at hRaw ⊢
        exact hRaw
      have hBodyConj : P_post * M_body.1.1 * P_post = P_post * (U_body.1ᴴ * M_uncomp.1.1 * U_body.1)
          * P_post := by
        rw [(congrFun hBody_wp σ).symm]
        exact ihBody.2 M_uncomp σ
      calc P_pre * (wp dSeq.compile (fun _ ↦ M_obs) σ).1.1 * P_pre
          = P_pre * (P₀ * (wp dSeq.compile (fun _ ↦ M_obs) σ).1.1 * P₀) * P_pre := by
              simp only [← Matrix.mul_assoc, hPre_P₀]
              simp only [Matrix.mul_assoc, hP₀_pre]
        _ = (P_pre * T_anc.1ᴴ) * (P_post * M_body.1.1 * P_post) * (T_anc.1 * P_pre) := by
              rw [hStep1]
              simp only [← Matrix.mul_assoc, hPre_P₀, hPre_Tadj_Post]
              simp only [Matrix.mul_assoc, hP₀_pre, hPost_T_pre]
        _ = ((P_pre * T_anc.1ᴴ) * U_body.1ᴴ) * M_uncomp.1.1 *
              (U_body.1 * (T_anc.1 * P_pre)) := by
              rw [hBodyConj]
              simp only [← Matrix.mul_assoc, hPre_Tadj_Post]
              simp only [Matrix.mul_assoc, hPost_T_pre]
        _ = (P_pre * U_clean.1ᴴ) * (P₀ * (T_anc.1ᴴ * M_uncomp.1.1 * T_anc.1) * P₀) *
              (U_clean.1 * P_pre) := by
              rw [hPre_TU_adj, hUT_pre]
              simp only [← Matrix.mul_assoc, hPre_Uadj_P₀]
              simp only [Matrix.mul_assoc, hP₀_U_pre]
        _ = P_pre * (U_clean.1ᴴ * M_obs.1.1 * U_clean.1) * P_pre := by
              rw [hStepUncomp]
              simp only [← Matrix.mul_assoc, hPre_Uadj_P₀]
              simp only [Matrix.mul_assoc, hP₀_U_pre]

theorem p2t_realizes_toDynWithDyn_of_validPred {Var : Type} [Fintype Var] [DecidableEq Var]
    {M n : ℕ} [NeZero (2 ^ n)] (v : Var) (rComb : QRegister M n)
    (P_fwd : BitAssignment M → Prop) (S_ext : BitAssignment n → Prop) (hExtComb : ∀ (β :
    BitAssignment n) (f : BitAssignment M), S_ext (writeRegProg β rComb f) ↔ S_ext β)
    (remHole : ℕ) (hremHole : remHole ≤ M) (probe : TempPhaseProg M)
    (hProbeRem : ∀ rem, ValidCleanRem M rem probe → remHole ≤ rem)
    (hProbeBits : ∀ γ : BitAssignment M, probe.evalBits γ = γ) (inner : DynamicCircuit Var n)
    (U₀ : Unitary (2 ^ n)) (hInner : p2t_RealizesConstCleanUnitary (p2t_ketPredProj
    (S_cleanCtxPred rComb P_fwd S_ext .hole remHole hremHole)) inner U₀)
    (ph : BitAssignment n → ZMod 2) (hInnerKet : ∀ β : BitAssignment n, U₀.1.mulVec (ket β) =
    ((-1 : ℂ) ^ (ph β).val) • ket β) : ∀ (K : TempCtx M) (rem : ℕ) (hrem : rem ≤ M),
    ValidCleanRem M rem (K.plug probe) → ∃ U : Unitary (2 ^ n), p2t_RealizesConstCleanUnitary
    (p2t_ketPredProj (S_cleanCtxPred rComb P_fwd S_ext K rem hrem))
    (toDynWithDyn v rComb inner K) U ∧ ∀ β : BitAssignment n, U.1.mulVec (ket β) = ((-1 : ℂ) ^
    (ph (writeRegProg β rComb (K.fwdBits (fun idx ↦ β (rComb idx))))).val) • ket (writeRegProg
    β rComb ((K.plug probe).evalBits (fun idx ↦ β (rComb idx)))) := fun K rem hrem hv ↦ by
  obtain ⟨U, hReal0, hKet⟩ := p2t_realizes_toDynWithDyn_gen v rComb P_fwd S_ext hExtComb
    remHole hremHole probe hProbeRem hProbeBits inner U₀ hInner
    (fun β ↦ (-1 : ℂ) ^ (ph β).val) id (fun _ _ ↦ rfl) hInnerKet K rem hrem hv
  exact ⟨U, hReal0, fun β ↦ (hKet β).trans (by dsimp; rw [(writeRegProg_helpers rComb).1])⟩
def castAssign {M' M : ℕ} (β : BitAssignment M') : BitAssignment M :=
  fun w ↦ if hw : w.val < M' then β ⟨w.val, hw⟩ else 0

@[simp]
theorem castAssign_lt {M' M : ℕ} (β : BitAssignment M') (w : Wire M) (hw : w.val < M') :
    castAssign β w = β ⟨w.val, hw⟩ := PosSlots24OrbitToggleFast288.dite_pos hw

theorem castAssign_ge {M' M : ℕ} (β : BitAssignment M') (w : Wire M) (hw : M' ≤ w.val) :
    castAssign β w = 0 := PosSlots24OrbitToggleFast288.dite_neg (by omega)

theorem castAssign_update {M' M : ℕ} (hMM : M' ≤ M) (β : BitAssignment M') (q : Wire M') (v : ZMod
    2) : castAssign (M := M) (Function.update β q v) =
      Function.update (castAssign (M := M) β) ⟨q.val, lt_of_lt_of_le q.isLt hMM⟩ v := by
  funext w
  by_cases hw : w.val < M'
  · by_cases hq : w.val = q.val
    all_goals simp [castAssign_lt _ w hw, Function.update_apply, Fin.ext_iff, hq]
  · rw [castAssign_ge _ w (by omega), Function.update_of_ne
      (fun h ↦ hw (by rw [congrArg Fin.val h]; exact q.isLt)),
      castAssign_ge _ w (by omega)]

theorem cleanRem_castAssign_iff {M' M : ℕ} (hMM : M' ≤ M) (rem : ℕ) (β : BitAssignment M') :
    cleanRem M' (rem - (M - M')) β ↔ cleanRem M rem (castAssign (M := M) β) := by
  refine ⟨fun hβ w hw ↦ ?_, fun hγ u hu ↦ ?_⟩
  · by_cases hlt : w.val < M'
    · exact (castAssign_lt β w hlt).trans (hβ ⟨w.val, hlt⟩ (by dsimp; omega))
    · exact castAssign_ge β w (by omega)
  · simpa only [castAssign_lt β ⟨u.val, lt_of_lt_of_le u.isLt hMM⟩ u.isLt] using
      hγ ⟨u.val, lt_of_lt_of_le u.isLt hMM⟩ (by dsimp; omega)

def cliffSupportsBelowB {M : ℕ} (bound : ℕ) : CliffProg M → Bool
  | .nil => true
  | .x q => decide (q.val < bound)
  | .cnot c t _ => decide (c.val < bound) && decide (t.val < bound)
  | .seq c₁ c₂ => cliffSupportsBelowB bound c₁ && cliffSupportsBelowB bound c₂

def progSupportsBelowB {M : ℕ} (bound : ℕ) : TempPhaseProg M → Bool
  | .nil => true
  | .cliff c => cliffSupportsBelowB bound c
  | .z q => decide (q.val < bound)
  | .seq p₁ p₂ => progSupportsBelowB bound p₁ && progSupportsBelowB bound p₂
  | .tempAnd c₁ c₂ anc _ _ _ body =>
      decide (c₁.val < bound) && (decide (c₂.val < bound) &&
        (decide (anc.val < bound) && progSupportsBelowB bound body))

def ctxSupportsBelowB {M : ℕ} (bound : ℕ) : TempCtx M → Bool
  | .hole => true
  | .seqPre c K => cliffSupportsBelowB bound c && ctxSupportsBelowB bound K
  | .seqPost K c => ctxSupportsBelowB bound K && cliffSupportsBelowB bound c
  | .tempAnd c₁ c₂ anc _ _ _ K =>
      decide (c₁.val < bound) && (decide (c₂.val < bound) &&
        (decide (anc.val < bound) && ctxSupportsBelowB bound K))

def truncateCliffB {M : ℕ} (M' : ℕ) :
    (c : CliffProg M) → cliffSupportsBelowB M' c = true → CliffProg M'
  | .nil, _ => .nil
  | .x q, hq => .x ⟨q.val, of_decide_eq_true hq⟩
  | .cnot c t hct, h =>
      .cnot ⟨c.val, of_decide_eq_true (Bool.and_eq_true _ _ |>.mp h).1⟩
        ⟨t.val, of_decide_eq_true (Bool.and_eq_true _ _ |>.mp h).2⟩
        (fun he ↦ hct (Fin.ext (congrArg (Fin.val (n := M')) he)))
  | .seq c₁ c₂, h =>
      .seq (truncateCliffB M' c₁ (Bool.and_eq_true _ _ |>.mp h).1)
        (truncateCliffB M' c₂ (Bool.and_eq_true _ _ |>.mp h).2)

theorem truncateCliffB_eval {M' M : ℕ} (hMM : M' ≤ M) : ∀ (c : CliffProg M) (hc :
    cliffSupportsBelowB M' c = true) (β : BitAssignment M'),
    castAssign (M := M) ((truncateCliffB M' c hc).eval β) = c.eval (castAssign (M := M) β)
  | .nil, _, _ => rfl
  | .x q, hq, β => by
      dsimp only [truncateCliffB, CliffProg.eval]
      rw [castAssign_update hMM, castAssign_lt β q (of_decide_eq_true hq)]
  | .cnot c t _, h, β => by
      dsimp only [truncateCliffB, CliffProg.eval]
      rw [castAssign_update hMM, castAssign_lt β t (of_decide_eq_true (Bool.and_eq_true _ _ |>.mp
          h).2),
        castAssign_lt β c (of_decide_eq_true (Bool.and_eq_true _ _ |>.mp h).1)]
  | .seq c₁ c₂, h, β => by
      dsimp only [truncateCliffB, CliffProg.eval]
      rw [truncateCliffB_eval hMM c₂ (Bool.and_eq_true _ _ |>.mp h).2,
          truncateCliffB_eval hMM c₁ (Bool.and_eq_true _ _ |>.mp h).1]

def truncateProgB {M : ℕ} (M' : ℕ) :
    (p : TempPhaseProg M) → progSupportsBelowB M' p = true → TempPhaseProg M'
  | .nil, _ => .nil
  | .cliff c, hc => .cliff (truncateCliffB M' c hc)
  | .z q, hq => .z ⟨q.val, of_decide_eq_true hq⟩
  | .seq p₁ p₂, h => .seq (truncateProgB M' p₁ (Bool.and_eq_true _ _ |>.mp h).1)
      (truncateProgB M' p₂ (Bool.and_eq_true _ _ |>.mp h).2)
  | .tempAnd c₁ c₂ anc h₁₂ h₁a h₂a body, h =>
      let h1 := Bool.and_eq_true _ _ |>.mp h
      let h2 := Bool.and_eq_true _ _ |>.mp h1.2
      let h3 := Bool.and_eq_true _ _ |>.mp h2.2
      .tempAnd ⟨c₁.val, of_decide_eq_true h1.1⟩ ⟨c₂.val, of_decide_eq_true h2.1⟩
        ⟨anc.val, of_decide_eq_true h3.1⟩
        (fun he ↦ h₁₂ (Fin.ext (congrArg (Fin.val (n := M')) he)))
        (fun he ↦ h₁a (Fin.ext (congrArg (Fin.val (n := M')) he)))
        (fun he ↦ h₂a (Fin.ext (congrArg (Fin.val (n := M')) he)))
        (truncateProgB M' body h3.2)

def truncateCtxB {M : ℕ} (M' : ℕ) :
    (K : TempCtx M) → ctxSupportsBelowB M' K = true → TempCtx M'
  | .hole, _ => .hole
  | .seqPre c K, h => .seqPre (truncateCliffB M' c (Bool.and_eq_true _ _ |>.mp h).1)
      (truncateCtxB M' K (Bool.and_eq_true _ _ |>.mp h).2)
  | .seqPost K c, h => .seqPost (truncateCtxB M' K (Bool.and_eq_true _ _ |>.mp h).1)
      (truncateCliffB M' c (Bool.and_eq_true _ _ |>.mp h).2)
  | .tempAnd c₁ c₂ anc h₁₂ h₁a h₂a K, h =>
      let h1 := Bool.and_eq_true _ _ |>.mp h
      let h2 := Bool.and_eq_true _ _ |>.mp h1.2
      let h3 := Bool.and_eq_true _ _ |>.mp h2.2
      .tempAnd ⟨c₁.val, of_decide_eq_true h1.1⟩ ⟨c₂.val, of_decide_eq_true h2.1⟩
        ⟨anc.val, of_decide_eq_true h3.1⟩
        (fun he ↦ h₁₂ (Fin.ext (congrArg (Fin.val (n := M')) he)))
        (fun he ↦ h₁a (Fin.ext (congrArg (Fin.val (n := M')) he)))
        (fun he ↦ h₂a (Fin.ext (congrArg (Fin.val (n := M')) he))) (truncateCtxB M' K h3.2)

@[simp] theorem truncateProgB_countTempAnd {M' M : ℕ} :
    ∀ (p : TempPhaseProg M) (hp : progSupportsBelowB M' p = true),
      (truncateProgB M' p hp).countTempAnd = p.countTempAnd
  | .nil, _ | .cliff _, _ | .z _, _ => rfl
  | .seq p₁ p₂, _ => by simp [truncateProgB, TempPhaseProg.countTempAnd,
      truncateProgB_countTempAnd p₁, truncateProgB_countTempAnd p₂]
  | .tempAnd _ _ _ _ _ _ body, _ => by
      simp [truncateProgB, TempPhaseProg.countTempAnd, truncateProgB_countTempAnd body]

@[simp] theorem truncateCtxB_countTempAnd {M' M : ℕ} :
    ∀ (K : TempCtx M) (hK : ctxSupportsBelowB M' K = true),
      (truncateCtxB M' K hK).countTempAnd = K.countTempAnd
  | .hole, _ => rfl
  | .seqPre _ K, h => truncateCtxB_countTempAnd K (Bool.and_eq_true _ _ |>.mp h).2
  | .seqPost K _, h => truncateCtxB_countTempAnd K (Bool.and_eq_true _ _ |>.mp h).1
  | .tempAnd _ _ _ _ _ _ K, _ => by
      simp [truncateCtxB, TempCtx.countTempAnd, truncateCtxB_countTempAnd K]

theorem ctxSupportsBelowB_plug {M bound : ℕ} : ∀ {K : TempCtx M} {p : TempPhaseProg M},
    ctxSupportsBelowB bound K = true → progSupportsBelowB bound p = true →
    progSupportsBelowB bound (K.plug p) = true
  | .hole, _, _, hp => hp
  | .seqPre _ _, _, hK, hp => Bool.and_eq_true _ _ |>.mpr
      ⟨(Bool.and_eq_true _ _ |>.mp hK).1,
        ctxSupportsBelowB_plug (Bool.and_eq_true _ _ |>.mp hK).2 hp⟩
  | .seqPost _ _, _, hK, hp => Bool.and_eq_true _ _ |>.mpr
      ⟨ctxSupportsBelowB_plug (Bool.and_eq_true _ _ |>.mp hK).1 hp,
        (Bool.and_eq_true _ _ |>.mp hK).2⟩
  | .tempAnd _ _ _ _ _ _ _, _, hK, hp => by
      simp only [ctxSupportsBelowB, TempCtx.plug, progSupportsBelowB, Bool.and_eq_true] at hK ⊢
      exact ⟨hK.1, hK.2.1, hK.2.2.1, ctxSupportsBelowB_plug hK.2.2.2 hp⟩

theorem truncateCtxB_plug {M' M : ℕ} : ∀ (K : TempCtx M) (hK : ctxSupportsBelowB M' K = true)
    (p : TempPhaseProg M) (hp : progSupportsBelowB M' p = true),
    (truncateCtxB M' K hK).plug (truncateProgB M' p hp) =
      truncateProgB M' (K.plug p) (ctxSupportsBelowB_plug hK hp)
  | .hole, _, _, _ => rfl
  | .seqPre _ K, _, p, hp => by
      simp [truncateCtxB, TempCtx.plug, truncateProgB, truncateCtxB_plug K _ p hp]
  | .seqPost K _, _, p, hp => by
      simp [truncateCtxB, TempCtx.plug, truncateProgB, truncateCtxB_plug K _ p hp]
  | .tempAnd _ _ _ _ _ _ K, _, p, hp => by
      simp [truncateCtxB, TempCtx.plug, truncateProgB, truncateCtxB_plug K _ p hp]

theorem truncateCtxB_fwdBits {M' M : ℕ} (hMM : M' ≤ M) : ∀ (K : TempCtx M) (hK : ctxSupportsBelowB
    M' K = true) (β : BitAssignment M'),
    castAssign (M := M) ((truncateCtxB M' K hK).fwdBits β) = K.fwdBits (castAssign (M := M) β)
  | .hole, _, _ => rfl
  | .seqPre c K, h, β => by
      dsimp only [truncateCtxB, TempCtx.fwdBits]
      rw [truncateCtxB_fwdBits hMM K (Bool.and_eq_true _ _ |>.mp h).2 _,
          truncateCliffB_eval hMM c (Bool.and_eq_true _ _ |>.mp h).1 β]
  | .seqPost K _, h, β => truncateCtxB_fwdBits hMM K (Bool.and_eq_true _ _ |>.mp h).1 β
  | .tempAnd c₁ c₂ anc _ _ _ K, hK, β => by
      have h1 := Bool.and_eq_true _ _ |>.mp hK
      have h2 := Bool.and_eq_true _ _ |>.mp h1.2
      have h3 := Bool.and_eq_true _ _ |>.mp h2.2
      dsimp only [truncateCtxB, TempCtx.fwdBits]
      rw [truncateCtxB_fwdBits hMM K h3.2 _, castAssign_update hMM,
          castAssign_lt β anc (of_decide_eq_true h3.1),
        castAssign_lt β c₁ (of_decide_eq_true h1.1), castAssign_lt β c₂ (of_decide_eq_true h2.1)]

theorem truncateProgB_evalBits {M' M : ℕ} (hMM : M' ≤ M) : ∀ (p : TempPhaseProg M) (hp :
    progSupportsBelowB M' p = true) (β : BitAssignment M'),
    castAssign (M := M) ((truncateProgB M' p hp).evalBits β) =
        p.evalBits (castAssign (M := M) β)
  | .nil, _, _ | .z _, _, _ => rfl
  | .cliff c, hc, β => truncateCliffB_eval hMM c hc β
  | .seq p₁ p₂, h, β => by
      dsimp only [truncateProgB, TempPhaseProg.evalBits]
      rw [truncateProgB_evalBits hMM p₂ (Bool.and_eq_true _ _ |>.mp h).2,
          truncateProgB_evalBits hMM p₁ (Bool.and_eq_true _ _ |>.mp h).1]
  | .tempAnd c₁ c₂ anc _ _ _ body, h, β => by
      let h1 := Bool.and_eq_true _ _ |>.mp h
      let h2 := Bool.and_eq_true _ _ |>.mp h1.2
      let h3 := Bool.and_eq_true _ _ |>.mp h2.2
      have hc₁ := of_decide_eq_true h1.1
      have hc₂ := of_decide_eq_true h2.1
      have ha := of_decide_eq_true h3.1
      dsimp only [truncateProgB, TempPhaseProg.evalBits]
      let β₁ : BitAssignment M' := Function.update β ⟨anc.val, ha⟩
        (β ⟨anc.val, ha⟩ + β ⟨c₁.val, hc₁⟩ * β ⟨c₂.val, hc₂⟩)
      have hβ₁ : castAssign (M := M) β₁ = Function.update (castAssign (M := M) β) anc
          (castAssign (M := M) β anc +
            castAssign (M := M) β c₁ * castAssign (M := M) β c₂) := by
        dsimp only [β₁]
        rw [castAssign_update hMM, castAssign_lt β anc ha, castAssign_lt β c₁ hc₁,
            castAssign_lt β c₂ hc₂]
      let β₂ : BitAssignment M' := (truncateProgB M' body h3.2).evalBits β₁
      change castAssign (M := M) (Function.update β₂ ⟨anc.val, ha⟩
        (β₂ ⟨anc.val, ha⟩ + β₂ ⟨c₁.val, hc₁⟩ * β₂ ⟨c₂.val, hc₂⟩)) = _
      rw [castAssign_update hMM, ← hβ₁, ← truncateProgB_evalBits hMM body h3.2 β₁,
        castAssign_lt β₂ anc ha, castAssign_lt β₂ c₁ hc₁, castAssign_lt β₂ c₂ hc₂]

theorem truncateProgB_validCleanRem {M' M : ℕ} (hMM : M' ≤ M) :
    ∀ (p : TempPhaseProg M) (hp : progSupportsBelowB M' p = true) (rem : ℕ),
      ValidCleanRem M rem p → ValidCleanRem M' (rem - (M - M')) (truncateProgB M' p hp)
  | .nil, _, _, _ | .cliff _, _, _, _ | .z _, _, _, _ => trivial
  | .seq p₁ p₂, h, rem, ⟨remMid, hmid, hv₁, hv₂, hpres⟩ => by
      refine ⟨remMid - (M - M'), by omega,
        truncateProgB_validCleanRem hMM p₁ (Bool.and_eq_true _ _ |>.mp h).1 rem hv₁,
        truncateProgB_validCleanRem hMM p₂ (Bool.and_eq_true _ _ |>.mp h).2 remMid hv₂,
        fun β hβ ↦ ?_⟩
      rw [cleanRem_castAssign_iff hMM remMid, truncateProgB_evalBits hMM p₁ _ β]
      exact hpres (castAssign β) ((cleanRem_castAssign_iff hMM rem β).mp hβ)
  | .tempAnd c₁ c₂ anc _ _ _ body, h, rem, ⟨hanc_lo, hvBody, hpresBody⟩ => by
      let h1 := Bool.and_eq_true _ _ |>.mp h
      let h2 := Bool.and_eq_true _ _ |>.mp h1.2
      let h3 := Bool.and_eq_true _ _ |>.mp h2.2
      have hrem_eq : (M - (anc.val + 1)) - (M - M') = M' - (anc.val + 1) := by omega
      refine ⟨by dsimp; omega, by
        have ih := truncateProgB_validCleanRem hMM body h3.2 (M - (anc.val + 1)) hvBody
        rwa [hrem_eq] at ih, fun β₁ hβ₁ ↦ ?_⟩
      obtain ⟨hp1, hp2, hp3⟩ := hpresBody (castAssign β₁)
        ((cleanRem_castAssign_iff hMM (M - (anc.val + 1)) β₁).mp (by rwa [hrem_eq]))
      have hev := truncateProgB_evalBits hMM body h3.2 β₁
      have hAt (q : Wire M) (hq : q.val < M') (hp : body.evalBits (castAssign β₁) q =
          castAssign β₁ q) :
          (truncateProgB M' body h3.2).evalBits β₁ ⟨q.val, hq⟩ = β₁ ⟨q.val, hq⟩ := by
        simpa only [castAssign_lt _ q hq] using (congrFun hev q).trans hp
      exact ⟨hAt c₁ (of_decide_eq_true h1.1) hp1, hAt c₂ (of_decide_eq_true h2.1) hp2,
        hAt anc (of_decide_eq_true h3.1) hp3⟩

/- ## Section 3: Truncated `269`-Wire (`59 + 210`) `orbitTogglePrefix60_269` &
  `orbitToggleTailProg60_269` -/

theorem constClean_toDynWithDyn_perm {Var : Type} [Fintype Var] [DecidableEq Var] {M n : ℕ}
    (v : Var) (rComb : QRegister M n) (remHole : ℕ) (hremHole : remHole ≤ M)
    (probe : TempPhaseProg M) (hProbeRem : ∀ rem, ValidCleanRem M rem probe → remHole ≤ rem)
    (hProbeBits : ∀ γ : BitAssignment M, probe.evalBits γ = γ) (inner : DynamicCircuit Var n)
    (U₀ : Unitary (2 ^ n)) (hInner : p2t_RealizesConstCleanUnitary (projZeroAll remHole
    (tailScr rComb remHole hremHole)) inner U₀) (step₀ : BitAssignment n → BitAssignment n)
    (hStepFixComb : ∀ (β : BitAssignment n) (idx : Fin M), step₀ β (rComb idx) = β (rComb
    idx)) (hInnerKet : ∀ β : BitAssignment n, U₀.1.mulVec (ket β) = ket (step₀ β)) : ∀
    (K : TempCtx M) (rem : ℕ) (hrem : rem ≤ M), ValidCleanRem M rem (K.plug probe) → ∃ U :
    Unitary (2 ^ n), p2t_RealizesConstCleanUnitary (projZeroAll rem (tailScr rComb rem hrem))
    (toDynWithDyn v rComb inner K) U ∧ ∀ β : BitAssignment n, U.1.mulVec (ket β) = ket
    (writeRegProg (step₀ (writeRegProg β rComb (K.fwdBits (fun idx ↦
        β (rComb idx))))) rComb ((K.plug probe).evalBits (fun idx ↦ β (rComb idx)))) := by
  have hProjEq (K : TempCtx M) (r : ℕ) (hr : r ≤ M) : p2t_ketPredProj (S_cleanCtxPred rComb (fun _ ↦
      True) (fun _ ↦ True) K r hr) =
      projZeroAll r (tailScr rComb r hr) := by
    classical
    apply MeasureBranchHadamardSem.matrix_ext_ket
    intro β
    conv_lhs => rw [mbh_ket_eq_ket, p2t_ketPredProj_mul_ket]
    rw [← mbh_ket_eq_ket, ket_projZeroAll]
    by_cases hz : ∀ j : Fin r, β (tailScr rComb r hr j) = 0
    all_goals simp [S_cleanCtxPred, hz, mbh_ket_eq_ket]
  intro K rem hrem hv
  obtain ⟨U, _hReal, hKet⟩ := p2t_realizes_toDynWithDyn_gen v rComb
    (fun _ ↦ True) (fun _ ↦ True) (fun _ _ ↦ Iff.rfl) remHole hremHole
    probe hProbeRem hProbeBits inner U₀ (by rwa [hProjEq .hole remHole hremHole])
    (fun _ ↦ 1) step₀ hStepFixComb (fun β ↦ (hInnerKet β).trans (one_smul _ _).symm)
    K rem hrem hv
  exact ⟨U, by rwa [← hProjEq K rem hrem], fun β ↦ (hKet β).trans (one_smul _ _)⟩

end SandAndTailScope
end ConfigPosTailWithAnchor18_244
end PosTailWithAnchor18_244
end
end PosTailWithAnchor18_244_p2
section ShiftedMagS1

/-!
# Slot 3 (`OAA_33` / `dPrep3`) Compact Single-Threshold Synthesis (`tOaa33 = 2352`)

Replaces the `11,336`-`T` schoolbook-multiplication `progCoarseGood33` with a shifted-shell
(`mt_w = 2 ^ (6 - μ) * m_w`) + 16-bit inverse-`c_8` SelectSwap (`d = 6, W = 32` + `16`-bit mux)
threshold comparison (`556` `TempAnd`s + `32` `TempAnd`s in `progNotZero33` = `588` `TempAnd`s =
`2,352` `T` gates per `OAA_33` / `dPrep3` call, saving `17,968` `T` gates per walk step on
`rWork : QRegister 288 n`).
-/

public section
namespace ShiftedMagS1

def cB (c : Fin 256) : Fin 4 := ⟨c.val % 4, by omega⟩

end ShiftedMagS1
end
end ShiftedMagS1

section Prod57BoothHoist
local instance (priority := 1000000) instNeZeroTwoPow_Prod57BoothHoist (k : ℕ) :
    NeZero (2 ^ k) := ⟨(Nat.two_pow_pos k).ne'⟩

/-!
# Unsigned Offset-Booth `18 × 38 → 57` Hoisted Multiplier for Slot 3 Step B

Hoisted multiplier for Slot 3 Step B (`M = 437`):
- Computes `sTrue18 = ∑_{w : Fin 3} dMag_w ^ 2` (`3 × 102 = 306` `tempAnd`s forward,
  `306` `tempAnd`s reverse) using an 8-bit `wWrap` comparator (`8` `tempAnd`s/axis, exact on
  every on-grid `p_w ≠ 128`), Clifford XOR-negation `dMag_w` (`0` `tempAnd`s), and split
  `u6 + 64 * u2` squaring (`ctxSelectSwapB2 5 12` + `ctxSelectSwapB2 1 4`).
- Computes `prod57 = sTrue * (u38 + 1) + boothConst57` (`boothConst57 = 48038396025110528`)
  via 19 Radix-4 Offset-Booth windows (`19 × 58 = 1,102` `tempAnd`s, with window `0` setting
  `b_{-1} = 1` and XOR-disjoint `{0, S, 2*S}` selection) plus top bit `u_37 * S * 2^38`
  (`38` `tempAnd`s) = `1,140` `tempAnd`s per side (`2,892` `tempAnd`s total when `sTrue18` is
  hoisted on `[259..275) ++ [199, 200]`, leaving wire `258` untouched).
- Exports both the parameterized hoisted 4-tuple `(sTrue18Fwd, boothAdd57, boothSub57, sTrue18Rev)`
  (with canonical `275` specializations `sTrue18Fwd275`, `boothAdd57_275`, `boothSub57_275`,
  `sTrue18Rev275`) and self-contained `(prod57Fwd, prod57Rev)` mutating only `prod57[201..258)`.
-/

public section
namespace Prod57BoothHoist
section ConfigProd57BoothHoist
set_option maxRecDepth 512
set_option exponentiation.threshold 256
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Operator Matrix QProg Circuit _root_.DynamicCircuit DynCircuitExt Real
open MeasureBranchHadamardSem (bit_cases)
open scoped Matrix BigOperators Matrix.Norms.L2Operator

theorem zmod2_eq_zero_or_one (b : ZMod 2) : b = 0 ∨ b = 1 := bit_cases b

theorem s3LtTrans {a b c : ℕ} (h1 : a < b) (h2 : b < c) : a < c := Nat.lt_trans h1 h2

/- ## Section 4C.1: Clean-Scratch `TempCtx` Combinators & Zero-Leak Modular Arithmetic -/

section Slot3ArithCombinators

def ctxLtStep {M : ℕ} (cur : ℕ) (hcur : cur + 1 ≤ M) (a b prev : Wire M) (hab : a ≠ b)
    (ha : a.val < cur) (hb : b.val < cur) (hp : prev.val < cur) (hbp : b ≠ prev) : TempCtx M :=
  let out : Wire M := ⟨cur, by omega⟩
  (ctxCliffAlloc (.seq (.cnot b a hab.symm) (.cnot prev b hbp.symm))).append
    ((ctxTempBit a b out hab (wire_ne_of_lt (by dsimp [out]; omega))
      (wire_ne_of_lt (by dsimp [out]; omega))).append
      (ctxCliffAlloc (.seq (.cnot prev b hbp.symm) (.seq (.cnot b a hab.symm)
        (.cnot prev out (wire_ne_of_lt (by dsimp [out]; omega)))))))

theorem ctxLtStep_plug {M : ℕ} (cur : ℕ) (hcur : cur + 1 ≤ M) (a b prev : Wire M)
    (hab : a ≠ b) (ha : a.val < cur) (hb : b.val < cur) (hp : prev.val < cur) (hbp : b ≠ prev)
    (body : TempPhaseProg M) : (ctxLtStep cur hcur a b prev hab ha hb hp hbp).plug body =
        withLtStep cur hcur a b prev hab ha hb hp hbp body := by
  simp only [ctxLtStep, withLtStep, TempCtx.append_plug, ctxCliffAlloc_plug, ctxTempBit_plug]

theorem ctxLtStep_props {M : ℕ} {mutW : Wire M → Prop} (cur : ℕ) (hcur : cur + 1 ≤ M)
    (a b prev : Wire M) (hab : a ≠ b) (ha : a.val < cur) (hb : b.val < cur) (hp : prev.val < cur)
        (hbp : b ≠ prev) (hna : ¬ mutW a) (hnb : ¬ mutW b)
    (hnp : ¬ mutW prev) (hno : ¬ mutW ⟨cur, by omega⟩) : (ctxLtStep cur hcur a b prev hab ha hb hp
        hbp).DisjointFrom mutW ∧
    (ctxLtStep cur hcur a b prev hab ha hb hp hbp).SupportsBelowCtx (cur + 1) :=
  ⟨TempCtx.disjointFrom_append (ctxCliffAlloc_disjoint ⟨⟨hnb, hna⟩, ⟨hnp, hnb⟩⟩)
      (TempCtx.disjointFrom_append ⟨hna, hnb, hno, trivial⟩
        (ctxCliffAlloc_disjoint ⟨⟨hnp, hnb⟩, ⟨hnb, hna⟩, ⟨hnp, hno⟩⟩)),
    TempCtx.supportsBelowCtx_append le_rfl
      (ctxCliffAlloc_supports (by dsimp [CliffProg.SupportsBelow]; omega))
      (TempCtx.supportsBelowCtx_append le_rfl ⟨by dsimp; omega, trivial⟩
        (ctxCliffAlloc_supports (by dsimp [CliffProg.SupportsBelow]; omega)))⟩

/-- `TempCtx` witness for `withLtCompLoop`. -/
def ctxLtCompLoop {M : ℕ} : (W cur : ℕ) → (hcur : cur + W + 1 ≤ M) → (a b : Fin W → Wire M) →
    (hab : ∀ j, a j ≠ b j) → (ha : ∀ j, (a j).val < cur) → (hb : ∀ j, (b j).val < cur) →
    TempCtx M
  | 0, _, _, _, _, _, _, _ => .hole
  | W + 1, cur, hcur, a, b, hab, ha, hb =>
      let prev : Wire M := ⟨cur, by omega⟩
      (ctxLtStep (cur + 1) (by omega) (a 0) (b 0) prev (hab 0) (s3LtTrans (ha 0) (by omega))
        (s3LtTrans (hb 0) (by omega)) (by dsimp [prev]; omega)
        (wire_ne_of_lt (by have := hb 0; dsimp [prev]; omega))).append
        (ctxLtCompLoop W (cur + 1) (by omega) (fun j ↦ a j.succ) (fun j ↦ b j.succ)
          (fun j ↦ hab j.succ) (fun j ↦ s3LtTrans (ha j.succ) (by omega))
          (fun j ↦ s3LtTrans (hb j.succ) (by omega)))

theorem ctxLtCompLoop_plug {M : ℕ} : ∀ (W cur : ℕ) (hcur : cur + W + 1 ≤ M)
    (a b : Fin W → Wire M) (hab : ∀ j, a j ≠ b j) (ha : ∀ j, (a j).val < cur)
    (hb : ∀ j, (b j).val < cur) (body : TempPhaseProg M),
    (ctxLtCompLoop W cur hcur a b hab ha hb).plug body =
      withLtCompLoop W cur hcur a b hab ha hb body
  | 0, _, _, _, _, _, _, _, _ => rfl
  | W + 1, cur, hcur, a, b, hab, ha, hb, body => by
      dsimp only [ctxLtCompLoop, withLtCompLoop]
      rw [TempCtx.append_plug, ctxLtStep_plug, ctxLtCompLoop_plug]

theorem ctxLtCompLoop_countTempAnd {M : ℕ} (W cur : ℕ) (hcur : cur + W + 1 ≤ M) (a b : Fin W →
    Wire M) (hab : ∀ j, a j ≠ b j) (ha : ∀ j, (a j).val < cur)
    (hb : ∀ j, (b j).val < cur) : (ctxLtCompLoop W cur hcur a b hab ha hb).countTempAnd = W := by
  have h1 := TempCtx.plug_countTempAnd (ctxLtCompLoop W cur hcur a b hab ha hb) .nil
  rw [ctxLtCompLoop_plug, withLtCompLoop_countTempAnd] at h1
  dsimp [TempPhaseProg.countTempAnd] at h1
  omega

theorem ctxLtCompLoop_props {M : ℕ} {mutW : Wire M → Prop} :
    ∀ (W cur : ℕ) (hcur : cur + W + 1 ≤ M) (a b : Fin W → Wire M) (hab : ∀ j, a j ≠ b j)
      (ha : ∀ j, (a j).val < cur) (hb : ∀ j, (b j).val < cur),
      (∀ j, ¬ mutW (a j)) → (∀ j, ¬ mutW (b j)) → (∀ w : Wire M, cur ≤ w.val → ¬ mutW w) →
      (ctxLtCompLoop W cur hcur a b hab ha hb).DisjointFrom mutW ∧
      (ctxLtCompLoop W cur hcur a b hab ha hb).SupportsBelowCtx (cur + W + 1)
  | 0, _, _, _, _, _, _, _, _, _, _ => ⟨trivial, trivial⟩
  | W + 1, cur, hcur, a, b, hab, ha, hb, hna, hnb, hncur => by
      obtain ⟨hd0, hs0⟩ := ctxLtStep_props (mutW := mutW) (cur + 1) (by omega)
        (a 0) (b 0) ⟨cur, by omega⟩ (hab 0) (s3LtTrans (ha 0) (by omega))
        (s3LtTrans (hb 0) (by omega)) (by dsimp; omega)
        (wire_ne_of_lt (by have := hb 0; dsimp; omega))
        (hna 0) (hnb 0) (hncur _ (by dsimp; omega)) (hncur _ (by dsimp; omega))
      obtain ⟨hdR, hsR⟩ := ctxLtCompLoop_props (mutW := mutW) W (cur + 1) (by omega)
        (fun j ↦ a j.succ) (fun j ↦ b j.succ) (fun j ↦ hab j.succ)
        (fun j ↦ s3LtTrans (ha j.succ) (by omega)) (fun j ↦ s3LtTrans (hb j.succ) (by omega))
        (fun j ↦ hna j.succ) (fun j ↦ hnb j.succ) (fun w hw ↦ hncur w (by omega))
      exact ⟨TempCtx.disjointFrom_append hd0 hdR, TempCtx.supportsBelowCtx_append (by omega)
        hs0 (TempCtx.supportsBelowCtx_mono (by omega) hsR)⟩

theorem ctxLtCompLoop_scoped {M : ℕ} (W cur : ℕ) (hcur : cur + W + 1 ≤ M)
    (a b : Fin W → Wire M) (hab : ∀ j, a j ≠ b j)
    (ha : ∀ j, (a j).val < cur) (hb : ∀ j, (b j).val < cur) :
    let K := ctxLtCompLoop W cur hcur a b hab ha hb
    (∀ q : Wire M, ScopedBlock M (M - (cur + 1)) K.fwdBits (.z q) (K.plug (.z q))) ∧
    (∀ β : BitAssignment M, cleanRem M (M - cur) β →
      ((K.fwdBits β ⟨cur + W, by omega⟩ = 1) ↔
        bitsVal (fun j ↦ β (a j)) < bitsVal (fun j ↦ β (b j)))) := by
  intro K
  have hL (q : Wire M) := ScopedBlock.withLtCompLoop_block W cur hcur a b hab ha hb
    (.z q) (.z q) id (ScopedBlock.z_kick q)
  refine ⟨TempCtx.scopedBlock_fwdBits K fun q ↦ ?_, fun β hβ ↦ ?_⟩
  · obtain ⟨sQ, hBlkQ, _⟩ := hL q
    exact ⟨sQ, by rwa [ctxLtCompLoop_plug]⟩
  · let u : Wire M := ⟨cur + W, by omega⟩
    obtain ⟨sU, hBlkU, hSpecU⟩ := hL u
    have hβ1 : cleanRem M (M - (cur + 1)) β := cleanRem_anti (by omega) hβ
    rw [TempCtx.fwdBits_eq_of_block K u (by rwa [ctxLtCompLoop_plug]) β hβ1]
    simpa [hβ ⟨cur, by omega⟩ (by dsimp; omega)] using (hSpecU β hβ1).2.2

end Slot3ArithCombinators

/-! ## Section 4B: Signed Odd-Digit Radix-2 Clean-MSB `Prod57` (`740` Fwd / `740` Static Rev /
  `684` Dyn Rev) -/

section P57CleanMsbBooth

open HermitianMat MeasureBranchHadamardSem StreamingBchComparator

attribute [local irreducible] inPlaceAddMod1 xorAndVecStatic ctxCleanMsbSub cleanMsbSubStatic

theorem boothRad2PrefixVal_37_add_top (S : ℕ) (hS : S < 2 ^ 18) (uBit : Fin 38 → ZMod 2) :
    boothRad2PrefixVal S uBit 37 (by decide) + 2 ^ 37 * S = S * (bitsVal uBit + 1) +
    boothConst57 ∧ boothRad2PrefixVal S uBit 37 (by decide) + 2 ^ 37 * S < 2 ^ 57 := by
  have hcf := boothRad2PrefixVal_closed_form S hS uBit 37 (by decide)
  rw [show (fun k : Fin 38 ↦ uBit ⟨k.val, by omega⟩) = uBit from funext fun _ ↦ rfl,
    add_comm 1 (bitsVal uBit)] at hcf
  refine ⟨hcf, ?_⟩
  rw [hcf]
  exact lt_of_le_of_lt (Nat.add_le_add_right (Nat.mul_le_mul (Nat.le_sub_one_of_lt hS)
    (Nat.succ_le_of_lt (bitsVal_lt_two_pow uBit))) _) (by decide)

def p57Acc20 (m : ℕ) (hm : m ≤ 37) (j : Fin 20) : Wire 437 := p57OutW ⟨m + j.val, by omega⟩
def p57Acc19 (m : ℕ) (hm : m ≤ 37) (j : Fin 19) : Wire 437 := p57OutW ⟨m + j.val, by omega⟩
def p57AccMsb (m : ℕ) (hm : m ≤ 37) : Wire 437 := p57OutW ⟨m + 19, by omega⟩
def p57AccInit18 (j : Fin 18) : Wire 437 := p57OutW ⟨j.val, by omega⟩

attribute [local irreducible] cBoothRowSetup

/-- Forward Row `m` (`0 ≤ m < 37`, `19` `TempAnd`s). -/
def boothAddRow57 (m : ℕ) (hm : m < 37) : TempPhaseProg 437 := withCliffAlloc
    (cBoothRowSetup m hm) (inPlaceAddMod1 19 278 (by decide) p57B20Row (p57Acc20 m (by omega))
    p57CinW (fun j ↦ p57OutW_ne_b20Row _ j) (fun j ↦ wire_ne_of_lt (p57OutW_lt_275 _))
    p57B20Row_ne_cin p57B20Row_lt_278 (fun j ↦ lt_trans (p57OutW_lt_275 _) (by decide))
    (by decide))

/-- Forward Top Row (`m = 37`, `19` `TempAnd`s). -/
def boothAddTop57 : TempPhaseProg 437 := inPlaceAddMod1 19 278 (by decide) p57B20Row
    (p57Acc20 37 (by decide)) p57CinW (fun j ↦ p57OutW_ne_b20Row _ j)
    (fun j ↦ wire_ne_of_lt (p57OutW_lt_275 _)) p57B20Row_ne_cin p57B20Row_lt_278
    (fun j ↦ lt_trans (p57OutW_lt_275 _) (by decide)) (by decide)

/-- Forward Init + `m` rows (`18 + 19 * m` `TempAnd`s). -/
def boothAddRows57 : (m : ℕ) → (hm : m ≤ 37) → TempPhaseProg 437
  | 0, _ =>
      xorAndVecStatic 18 275 (by decide) (p57U38W 0) sTrue18WDefault p57AccInit18
        (fun j ↦ (validSTrueMap_default.2.2.2.2.2.1 j 0).symm) (by dsimp [p57U38W]; decide)
        validSTrueMap_default.2.1 (fun j ↦ p57OutW_lt_275 _)
  | m + 1, hm => .seq (boothAddRows57 m (by omega)) (boothAddRow57 m (by omega))

/-- Canonical `cur = 275` forward Signed Odd-Digit Radix-2 multiplier (`740` `TempAnd`s). -/
def boothAdd57_275 : TempPhaseProg 437 := .seq (boothAddRows57 37 (by decide)) boothAddTop57

attribute [local irreducible] boothAddRow57 boothAddTop57 boothAddRows57 boothAdd57_275

def boothSubRow57 (m : ℕ) (hm : m < 37) : TempPhaseProg 437 := withCliffAlloc
    (cBoothRowSetup m hm) (cleanMsbSubStatic 18 278 (by decide) p57B19Row (p57Acc19 m
    (by omega)) (p57AccMsb m (by omega)) p57CinW (fun j ↦ p57OutW_ne_b19Row _ j) (fun j ↦
    wire_ne_of_lt (p57OutW_lt_275 _)) p57B19Row_ne_cin (wire_ne_of_lt (p57OutW_lt_275 _))
    p57B19Row_lt_278 (fun j ↦ lt_trans (p57OutW_lt_275 _) (by decide)) (lt_trans
    (p57OutW_lt_275 _) (by decide)) (by decide))

def boothSubTop57 : TempPhaseProg 437 := cleanMsbSubStatic 18 278 (by decide) p57B19Row
    (p57Acc19 37 (by decide)) (p57AccMsb 37 (by decide)) p57CinW
    (fun j ↦ p57OutW_ne_b19Row _ j) (fun j ↦ wire_ne_of_lt (p57OutW_lt_275 _))
    p57B19Row_ne_cin (wire_ne_of_lt (p57OutW_lt_275 _)) p57B19Row_lt_278
    (fun j ↦ lt_trans (p57OutW_lt_275 _) (by decide))
    (lt_trans (p57OutW_lt_275 _) (by decide)) (by decide)

def boothSubRows57 : (m : ℕ) → (hm : m ≤ 37) → TempPhaseProg 437
  | 0, _ =>
      xorAndVecStatic 18 275 (by decide) (p57U38W 0) sTrue18WDefault p57AccInit18
        (fun j ↦ (validSTrueMap_default.2.2.2.2.2.1 j 0).symm) (by dsimp [p57U38W]; decide)
        validSTrueMap_default.2.1 (fun j ↦ p57OutW_lt_275 _)
  | m + 1, hm => .seq (boothSubRow57 m (by omega)) (boothSubRows57 m (by omega))

/-- Canonical `cur = 275` static reverse Signed Odd-Digit Radix-2 uncompute (`740` `TempAnd`s). -/
def boothSub57_275 : TempPhaseProg 437 := .seq boothSubTop57 (boothSubRows57 37 (by decide))

attribute [local irreducible]
  boothSubRow57 boothSubRows57 boothSubTop57 boothSub57_275
end P57CleanMsbBooth
end
end ConfigProd57BoothHoist
end Prod57BoothHoist
end
end Prod57BoothHoist

section StepBBlock0
public section
namespace StepBBlock0
set_option backward.isDefEq.respectTransparency false

/- ## Section 4C.1: Clean-Scratch `TempCtx` Combinators & Zero-Leak Modular Arithmetic -/

theorem bitsVal_castSucc_mod {W : ℕ} (f : Fin (W + 1) → ZMod 2) : bitsVal (fun j : Fin W ↦
    f j.castSucc) = bitsVal f % 2 ^ W := by
  rw [bitsVal_castSucc_split f, mul_comm (2 ^ W), Nat.add_mul_mod_self_right,
      Nat.mod_eq_of_lt (bitsVal_lt_two_pow _)]

end StepBBlock0
end
end StepBBlock0

section TwoAngleBiGqspVerifierBridge
public section
namespace TwoAngleBiGqspVerifierBridge
section ConfigTwoAngleBiGqspVerifierBridge
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency true
set_option exponentiation.threshold 256

open Real Operator Matrix Circuit
open scoped Matrix Matrix.Norms.L2Operator BigOperators

/- ## Section 1A: 2x2 Complex Cayley-Klein Matrix Algebra (`su2Matrix`) -/

def shiftRightC (M : ℕ) (p : Fin (2 * M + 1) → ℂ) (i : Fin (2 * M + 1)) : ℂ :=
  if h : i.val = 0 then 0 else p ⟨i.val - 1, by omega⟩

/-- Left-shift (`W_inv * ·`) on complex Laurent coefficient arrays. -/
def shiftLeftC (M : ℕ) (p : Fin (2 * M + 1) → ℂ) (i : Fin (2 * M + 1)) : ℂ :=
  if h : i.val < 2 * M then p ⟨i.val + 1, by omega⟩ else 0

@[local simp] theorem shiftRightC_zero (M : ℕ) (p : Fin (2 * M + 1) → ℂ) :
    shiftRightC M p 0 = 0 := by simp [shiftRightC]

@[local simp] theorem shiftRightC_succ (M : ℕ) (p : Fin (2 * M + 1) →
    ℂ) (i : Fin (2 * M)) : shiftRightC M p i.succ = p i.castSucc := by
  simp only [shiftRightC, Fin.val_succ, Nat.succ_ne_zero, ↓reduceDIte, Nat.add_sub_cancel]
  rfl

@[local simp] theorem shiftLeftC_last (M : ℕ) (p : Fin (2 * M + 1) → ℂ) :
    shiftLeftC M p (Fin.last (2 * M)) = 0 := by simp [shiftLeftC]

@[local simp] theorem shiftLeftC_castSucc (M : ℕ) (p : Fin (2 * M + 1) →
    ℂ) (i : Fin (2 * M)) : shiftLeftC M p i.castSucc = p i.succ := by
  simp only [shiftLeftC, Fin.val_castSucc, i.isLt, ↓reduceDIte]
  rfl

/-- Complex `SU(2)` coefficient update `(P, Q) ↦ (a P - conj(b) Q, b P + conj(a) Q)`. -/
def gqspSu2Step (M : ℕ) (a b : ℂ) (pq : (Fin (2 * M + 1) → ℂ) × (Fin (2 * M + 1) → ℂ)) :
    (Fin (2 * M + 1) → ℂ) × (Fin (2 * M + 1) → ℂ) := (fun i ↦ a * pq.1 i - star b * pq.2 i,
    fun i ↦ b * pq.1 i + star a * pq.2 i)

/-- Initial `(1, W)` complex Laurent pair prior to step `0` of bidirectional 2-angle GQSP. -/
def biGqspTwoAnglePreInit (M : ℕ) : (Fin (2 * (M + 1) + 1) → ℂ) × (Fin (2 * (M + 1) + 1) → ℂ)
    := (fun i ↦ if i.val = M + 1 then 1 else 0, fun i ↦ if i.val = M + 2 then 1 else 0)

/-- One interior bidirectional walk + complex `SU(2)` step on degree-`(M + 1)` Laurent arrays. -/
def biGqspTwoAngleStep (M : ℕ) (a b : ℂ) (pq : (Fin (2 * (M + 1) + 1) → ℂ) × (Fin (2 * (M + 1) +
    1) → ℂ)) :
    (Fin (2 * (M + 1) + 1) → ℂ) × (Fin (2 * (M + 1) + 1) → ℂ) :=
  gqspSu2Step (M + 1) a b (shiftRightC (M + 1) pq.1, shiftLeftC (M + 1) pq.2)

/-- Prefix execution of `t + 1` complex `SU(2)` gates and `t` bidirectional walk steps. -/
def biGqspTwoAngleRunLoop (M : ℕ) (ab : ℕ → ℂ × ℂ) :
    ℕ → (Fin (2 * (M + 1) + 1) → ℂ) × (Fin (2 * (M + 1) + 1) → ℂ)
  | 0 => gqspSu2Step (M + 1) (ab 0).1 (ab 0).2 (biGqspTwoAnglePreInit M)
  | t + 1 => biGqspTwoAngleStep M (ab (t + 1)).1 (ab (t + 1)).2 (biGqspTwoAngleRunLoop M ab t)

/- ## Section 1D: 2-Angle Bidirectional Operator Loop, Segment Unitary & Telescoping -/

end ConfigTwoAngleBiGqspVerifierBridge
end TwoAngleBiGqspVerifierBridge
end
end TwoAngleBiGqspVerifierBridge

section OraAndPrepBundle

/-
# Oracle, Prepare, Guard, QFT & Two-World Endpoint Bundle

Assembles leaf oracle, post-Hadamard state-preparation, grid-guard reflection, catalyzed QFT_64,
nuclear twist, slack-cancellation, payload-widening (`80 -> 158`), and non-symmetric two-world
(`Heff_sm` & `Heff_twos`) block-encoding bridges.
-/

public section
namespace OraAndPrepBundle

open Operator Matrix QProg Circuit _root_.DynamicCircuit DynCircuitExt

theorem castNatReg_realizes {Var : Type} [Fintype Var] [DecidableEq Var] {a b m n : ℕ} (h : a =
    b) (r : QRegister a n) (rW : QRegister m n)
    (U : Unitary (2 ^ b)) (d : DynamicCircuit Var n) :
        DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace (castNatReg h r) rW U d →
    DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace r rW (castNatUnitary h.symm U) d := by
  subst h; exact id

end OraAndPrepBundle
end
end OraAndPrepBundle

section CoinDispatchedBarrel288
local instance (priority := 1000000) instNeZeroTwoPow_CoinDispatchedBarrel288 (k : ℕ) :
    NeZero (2 ^ k) := ⟨(Nat.two_pow_pos k).ne'⟩

public section

/-
# Coin-Dispatched Hoisted Barrel Swap and Post-Swap Nuclear Twist Remainder (`mWork = 265 <= 288`)

Polymorphic clean-workspace quantum circuit synthesis and unitary bridge module, parameterized
across **every** payload width `{mPayload : Nat}` with
`hmPay : 80 <= mPayload` and **every** workspace width `{mWork : Nat}` with `265 <= mWork`,
with ready-to-use abbreviations at **both** `mPayload = 80, mWork = 288` and
`mPayload = 158, mWork = 288`:

1. **Leaf #1 (`uBarrel`, `dBarrel`, `mWorkBarrel = 265 <= 269 <= 288`, `tBarrel = 29028`,
    `0` `.TOFF`)**:
   - Single self-inverse coin-dispatched electron barrel swap `rElec[0] <-> rElec[idx]` on
     `fullSysCoreWires mPayload` handling all active branches simultaneously:
     * `c2 = 0` and `c1 = 0` (position coins `{0, 1}`): anchor register `[3968 .. 3976)` clamped to
       `< 218`,
     * `c2 = 0` and `c1 = 1` (slack coins `{2, 3}`): identity (`idx = 0`), matching
       `NuclearTwistRealizes.uBarrelCore true` identically across **all** of
           `slotBitProj (iSlot2 mPayload) 0`,
     * `c2 = 1, c1 = 0, c0 = 0` (`coin = 4`, `MomSlot 0`): `(2 * (u36 % 327) + bPar) / 3`,
     * `c2 = 1, c1 = 1, c0 = 1` (`coin = 7`, `MomSlot 5`): `u21 % 218` on `[4011 .. 4032)`,
     * `coins {5, 6}` (`MomSlot 1`, `MomSlot 3`): identity (`idx = 0`).
2. **Leaf #2 (`uTwistRest`, `dTwistRest`, `dTwistRestInv`, `tTwistRest = 102504`, `0` `.TOFF`)**:
   - Post-swap twist remainder omitting redundant inner `dBarrelSwap` (`-17,680 T` per pass,
     `-35,360 T` per walk step), proving exact operator agreement
     `(uTwistRest hm cfg * uBarrel hmPay).1 * slotBitProj (iSlot2 mPayload) 0 =
       (uTwistParam true hm cfg).1 * slotBitProj (iSlot2 mPayload) 0`
     across every `hmPay : 80 <= mPayload` (including both `mPayload = 80` and `mPayload = 158`).
-/

namespace CoinDispatchedBarrel288

section ConfigCoinDispatchedBarrel288

set_option backward.isDefEq.respectTransparency false
set_option exponentiation.threshold 256

namespace Internal

open Operator Matrix _root_.DynamicCircuit DynCircuitExt QProg HermitianMat
open BchCubeDecoder StreamingBchComparator
open scoped Matrix ComplexOrder MatrixOrder Circuit.Notation BigOperators

namespace TempPhaseProg
def x {m : ℕ} (q : Wire m) : TempPhaseProg m := .cliff (.x q)
end TempPhaseProg

theorem ScopedBlock.cast_rem {M rem₁ rem₂ : ℕ} (h : rem₁ = rem₂) {s : BitAssignment M →
    BitAssignment M} {leaf p : TempPhaseProg M}
    (hb : ScopedBlock M rem₁ s leaf p) : ScopedBlock M rem₂ s leaf p := h ▸ hb

def withFullAdd {M : ℕ} (cur : ℕ) (hcur : cur + 2 ≤ M) (a b cin : Wire M) (hab : a ≠ b)
    (hac : a ≠ cin) (hbc : b ≠ cin) (ha : a.val < cur) (hb : b.val < cur) (hc : cin.val < cur) (body
        : TempPhaseProg M) : TempPhaseProg M :=
  let sumWire : Wire M := ⟨cur, by omega⟩
  let coutWire : Wire M := ⟨cur + 1, by omega⟩
  withCliffAlloc (.seq (.cnot cin a hac.symm) (.cnot cin b hbc.symm))
    (withTempBit a b coutWire hab (wire_ne_of_lt (by dsimp [coutWire]; omega))
      (wire_ne_of_lt (by dsimp [coutWire]; omega))
      (withCliffAlloc (.seq (.cnot cin b hbc.symm) (.seq (.cnot cin a hac.symm)
        (.seq (.cnot cin coutWire (wire_ne_of_lt (by dsimp [coutWire]; omega)))
          (.seq (.cnot a sumWire (wire_ne_of_lt (by dsimp [sumWire]; omega)))
            (.seq (.cnot b sumWire (wire_ne_of_lt (by dsimp [sumWire]; omega)))
              (.cnot cin sumWire (wire_ne_of_lt (by dsimp [sumWire]; omega)))))))) body))

@[simp] theorem withFullAdd_countTempAnd {M : ℕ} (cur : ℕ) (hcur : cur + 2 ≤ M)
    (a b cin : Wire M) (hab : a ≠ b) (hac : a ≠ cin) (hbc : b ≠ cin) (ha : a.val < cur)
    (hb : b.val < cur) (hc : cin.val < cur) (body : TempPhaseProg M) : (withFullAdd cur hcur a
    b cin hab hac hbc ha hb hc body).countTempAnd = 1 + body.countTempAnd := by
  simp [withFullAdd]

def withLtStep {M : ℕ} (cur : ℕ) (hcur : cur + 1 ≤ M) (a b prev : Wire M) (hab : a ≠ b)
    (ha : a.val < cur) (hb : b.val < cur) (hp : prev.val < cur) (hbp : b ≠ prev) (body :
        TempPhaseProg M) : TempPhaseProg M :=
  let out : Wire M := ⟨cur, by omega⟩
  withCliffAlloc (.seq (.cnot b a hab.symm) (.cnot prev b hbp.symm))
    (withTempBit a b out hab (wire_ne_of_lt (by dsimp [out]; omega))
      (wire_ne_of_lt (by dsimp [out]; omega))
      (withCliffAlloc (.seq (.cnot prev b hbp.symm) (.seq (.cnot b a hab.symm)
        (.cnot prev out (wire_ne_of_lt (by dsimp [out]; omega))))) body))

@[simp] theorem withLtStep_countTempAnd {M : ℕ} (cur : ℕ) (hcur : cur + 1 ≤ M)
    (a b prev : Wire M) (hab : a ≠ b) (ha : a.val < cur) (hb : b.val < cur)
    (hp : prev.val < cur) (hbp : b ≠ prev) (body : TempPhaseProg M) :
    (withLtStep cur hcur a b prev hab ha hb hp hbp body).countTempAnd =
      1 + body.countTempAnd := by simp [withLtStep]

def ltStepSetup {M : ℕ} (cur : ℕ) (hcur : cur + 1 ≤ M) (a b prev : Wire M) (β : BitAssignment M) :
    BitAssignment M :=
  Function.update β ⟨cur, by omega⟩ (β prev + (β a + β b) * (β b + β prev))

theorem ltStep_bit_iff (a b prev : ZMod 2) : (prev + (a + b) * (b + prev)) = 1 ↔ (a.val < b.val ∨
    (a.val = b.val ∧ prev = 1)) := by
  revert a b prev; decide

theorem ScopedBlock.withLtStep_block {M : ℕ} (cur : ℕ) (hcur : cur + 1 ≤ M)
    (a b prev : Wire M) (hab : a ≠ b) (hap : a ≠ prev) (ha : a.val < cur) (hb : b.val < cur)
    (hp : prev.val < cur) (hbp : b ≠ prev) {sBody : BitAssignment M → BitAssignment M}
    {leaf body : TempPhaseProg M} (hBody : ScopedBlock M (M - (cur + 1)) sBody leaf body) :
    ScopedBlock M (M - cur) (sBody ∘ ltStepSetup cur hcur a b prev) leaf (withLtStep cur hcur a b
        prev hab ha hb hp hbp body) := by
  let remIn := M - (cur + 1)
  let out : Wire M := ⟨cur, by omega⟩
  have h1 := ScopedBlock.withCliffAlloc_block (M := M) (rem := remIn) (remIn := remIn)
    (by dsimp [remIn]; omega) le_rfl
    (.seq (.cnot prev b hbp.symm) (.seq (.cnot b a hab.symm)
      (.cnot prev out (wire_ne_of_lt (by dsimp [out]; omega)))))
    (by dsimp [CliffProg.SupportsBelow, out, remIn]; omega) hBody
  have h3 := ScopedBlock.withCliffAlloc_block (M := M) (rem := M - cur) (remIn := M - cur)
    (by omega) le_rfl (.seq (.cnot b a hab.symm) (.cnot prev b hbp.symm))
    (by dsimp [CliffProg.SupportsBelow]; omega)
    (ScopedBlock.withTempBit_block (M := M) cur hcur a b hab ha hb h1)
  refine ⟨h3.valid, h3.bits, fun β hβ ↦ ?_⟩
  dsimp only [withLtStep]
  rw [h3.sign β hβ]
  dsimp only [Function.comp_apply, ltStepSetup, CliffProg.eval]
  congr 1
  congr 1
  rw [show (⟨cur, hcur⟩ : Wire M) = out from rfl]
  have hao : a ≠ out := wire_ne_of_lt (by dsimp [out]; omega)
  have hbo : b ≠ out := wire_ne_of_lt (by dsimp [out]; omega)
  have hpo : prev ≠ out := wire_ne_of_lt (by dsimp [out]; omega)
  funext w
  simp only [Function.update_apply]
  by_cases hwo : w = out
  · subst hwo
    simp only [↓reduceIte, hab, hab.symm, hap.symm, hbp.symm, hao.symm, hbo.symm, hpo]
    ring
  · by_cases hwa : w = a
    · subst hwa
      simp only [↓reduceIte, hab, hab.symm, hap.symm, hbp.symm, hao, hbo, hpo, add_assoc,
          CharTwo.add_self_eq_zero, add_zero]
    · by_cases hwb : w = b
      · subst hwb
        simp only [↓reduceIte, hwa, hap.symm, hbp.symm, hbo, hpo, add_assoc,
            CharTwo.add_self_eq_zero, add_zero]
      · simp only [↓reduceIte, hwo, hwa, hwb]

/-- `W`-bit unsigned `<` comparator (`W` `tempAnd`s = `4 W` `T`, allocates `W + 1` wires
`[cur .. cur + W + 1)`, with `[bitsVal a < bitsVal b]` placed on wire `⟨cur + W, _⟩`). -/
def withLtCompLoop {M : ℕ} : (W cur : ℕ) → (hcur : cur + W + 1 ≤ M) →
    (a b : Fin W → Wire M) → (hab : ∀ j, a j ≠ b j) → (ha : ∀ j, (a j).val < cur) →
    (hb : ∀ j, (b j).val < cur) → TempPhaseProg M → TempPhaseProg M
  | 0, _, _, _, _, _, _, _, body => body
  | W + 1, cur, hcur, a, b, hab, ha, hb, body =>
      let prev : Wire M := ⟨cur, by omega⟩
      withLtStep (cur + 1) (by omega) (a 0) (b 0) prev (hab 0) (lt_trans (ha 0) (by omega))
        (lt_trans (hb 0) (by omega)) (by dsimp [prev]; omega)
        (wire_ne_of_lt (by have := hb 0; dsimp [prev]; omega))
        (withLtCompLoop W (cur + 1) (by omega) (fun j ↦ a j.succ) (fun j ↦ b j.succ)
          (fun j ↦ hab j.succ) (fun j ↦ lt_trans (ha j.succ) (by omega))
          (fun j ↦ lt_trans (hb j.succ) (by omega)) body)

@[simp] theorem withLtCompLoop_countTempAnd {M : ℕ} : ∀ (W cur : ℕ) (hcur : cur + W + 1 ≤ M)
    (a b : Fin W → Wire M) (hab : ∀ j, a j ≠ b j) (ha : ∀ j, (a j).val < cur)
    (hb : ∀ j, (b j).val < cur) (body : TempPhaseProg M),
    (withLtCompLoop W cur hcur a b hab ha hb body).countTempAnd = W + body.countTempAnd
  | 0, _, _, _, _, _, _, _, _ => by simp [withLtCompLoop]
  | W + 1, _, _, _, _, _, _, _, _ => by
      simp only [withLtCompLoop, withLtStep_countTempAnd, withLtCompLoop_countTempAnd]
      omega

theorem ScopedBlock.withLtCompLoop_block {M : ℕ} : ∀ (W cur : ℕ) (hcur : cur + W + 1 ≤ M)
    (a b : Fin W → Wire M) (hab : ∀ j, a j ≠ b j) (ha : ∀ j, (a j).val < cur)
    (hb : ∀ j, (b j).val < cur) (leaf body : TempPhaseProg M)
    (sBody : BitAssignment M → BitAssignment M),
    ScopedBlock M (M - (cur + W + 1)) sBody leaf body →
    ∃ setup : BitAssignment M → BitAssignment M,
      ScopedBlock M (M - (cur + 1)) (fun β ↦ sBody (setup β)) leaf
        (withLtCompLoop W cur hcur a b hab ha hb body) ∧
      ∀ β : BitAssignment M, cleanRem M (M - (cur + 1)) β →
        cleanRem M (M - (cur + W + 1)) (setup β) ∧
        (∀ w : Wire M, w.val < cur → setup β w = β w) ∧
        ((setup β ⟨cur + W, by omega⟩ = 1) ↔
          (bitsVal (fun j ↦ β (a j)) < bitsVal (fun j ↦ β (b j)) ∨
            (bitsVal (fun j ↦ β (a j)) = bitsVal (fun j ↦ β (b j)) ∧
              β ⟨cur, by omega⟩ = 1)))
  | 0, cur, _, _, _, _, _, _, _, _, _, hBody =>
      ⟨id, hBody, fun _ hβ ↦ ⟨hβ, fun _ _ ↦ rfl, by simp [bitsVal]⟩⟩
  | W + 1, cur, hcur, a, b, hab, ha, hb, leaf, body, sBody, hBody => by
      let prev : Wire M := ⟨cur, by omega⟩
      obtain ⟨setupInner, hInner, hSpecInner⟩ := ScopedBlock.withLtCompLoop_block W (cur + 1)
        (by omega) (fun j ↦ a j.succ) (fun j ↦ b j.succ) (fun j ↦ hab j.succ)
        (fun j ↦ lt_trans (ha j.succ) (by omega)) (fun j ↦ lt_trans (hb j.succ) (by omega))
        leaf body sBody
        (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hBody)
      refine ⟨fun β ↦ setupInner (ltStepSetup (cur + 1) (by omega) (a 0) (b 0) prev β),
        ScopedBlock.withLtStep_block (M := M) (cur + 1) (by omega) (a 0) (b 0) prev (hab 0)
          (wire_ne_of_lt (by have := ha 0; dsimp [prev]; omega))
          (lt_trans (ha 0) (by omega)) (lt_trans (hb 0) (by omega)) (by dsimp [prev]; omega)
          (wire_ne_of_lt (by have := hb 0; dsimp [prev]; omega)) hInner, fun β hβ ↦ ?_⟩
      let β₁ := ltStepSetup (cur + 1) (by omega) (a 0) (b 0) prev β
      obtain ⟨hcl, hbelow, hlt_ih⟩ := hSpecInner β₁ fun w hw ↦ by
        dsimp [β₁, ltStepSetup]
        rw [Function.update_of_ne (wire_ne_of_gt (by dsimp; omega))]
        exact hβ w (by omega)
      have splitVal (f : Fin (W + 1) → ZMod 2) : bitsVal f = (f 0).val + 2 * bitsVal (fun j ↦
          f j.succ) := by
        simp only [bitsVal, Fin.sum_univ_succ, Fin.val_zero, _root_.pow_zero, mul_one, Fin.val_succ,
            pow_succ, Finset.mul_sum]
        exact congrArg ((f 0).val + ·) (Finset.sum_congr rfl fun _ _ ↦ by ring)
      have ha_fun : (fun j : Fin W ↦ β₁ (a j.succ)) = fun j ↦ β (a j.succ) := funext fun j ↦
        Function.update_of_ne (wire_ne_of_lt (by have := ha j.succ; dsimp; omega)) _ _
      have hb_fun : (fun j : Fin W ↦ β₁ (b j.succ)) = fun j ↦ β (b j.succ) := funext fun j ↦
        Function.update_of_ne (wire_ne_of_lt (by have := hb j.succ; dsimp; omega)) _ _
      have hbit1 : β₁ ⟨cur + 1, by omega⟩ = 1 ↔ (β (a 0)).val < (β (b 0)).val ∨ ((β (a 0)).val =
          (β (b 0)).val ∧ β ⟨cur, by omega⟩ = 1) := by
        dsimp only [β₁, ltStepSetup]
        rw [Function.update_self]
        exact ltStep_bit_iff (β (a 0)) (β (b 0)) (β prev)
      refine ⟨by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hcl,
        fun w hw ↦ (hbelow w (by omega)).trans
          (Function.update_of_ne (wire_ne_of_lt (by dsimp; omega)) _ _), ?_⟩
      dsimp only
      rw [show (⟨cur + (W + 1), by omega⟩ : Wire M) = ⟨cur + 1 + W, by omega⟩ by
          ext; dsimp; omega, hlt_ih, ha_fun, hb_fun, hbit1,
        splitVal (fun j ↦ β (a j)), splitVal (fun j ↦ β (b j))]
      have := ZMod.val_lt (β (a 0))
      have := ZMod.val_lt (β (b 0))
      by_cases hp1 : β ⟨cur, by omega⟩ = 1
      all_goals
        simp only [hp1, and_true, and_false, or_false]
        omega

/-- Gidney binary-to-unary split (`1` `tempAnd` = `4 T`, allocates `hiWire = ⟨cur, _⟩`). -/
def withUnarySplit {M : ℕ} (cur : ℕ) (hcur : cur + 1 ≤ M) (loWire sel : Wire M) (hlo_sel : loWire ≠
    sel) (hlo : loWire.val < cur) (hsel : sel.val < cur)
    (body : TempPhaseProg M) : TempPhaseProg M :=
  let hiWire : Wire M := ⟨cur, by omega⟩
  withTempBit loWire sel hiWire hlo_sel
    (wire_ne_of_lt (by dsimp [hiWire]; omega))
    (wire_ne_of_lt (by dsimp [hiWire]; omega))
    (withCliffAlloc (.cnot hiWire loWire (wire_ne_of_gt (by dsimp [hiWire]; omega))) body)

@[simp] theorem withUnarySplit_countTempAnd {M : ℕ} (cur : ℕ) (hcur : cur +
    1 ≤ M) (loWire sel : Wire M) (hlo_sel : loWire ≠ sel) (hlo : loWire.val < cur)
    (hsel : sel.val < cur) (body : TempPhaseProg M) : (withUnarySplit cur hcur loWire sel hlo_sel
        hlo hsel body).countTempAnd = 1 + body.countTempAnd := by
  simp [withUnarySplit]

/-- Splits `K` consecutive unary wires `[base .. base + K)` into `[base .. base + L)` and
`[base + L .. base + L + K)` controlled by `sel < base` (`K` `tempAnd`s). -/
def withUnarySplitRange {M : ℕ} (base L : ℕ) (sel : Wire M) (hsel : sel.val < base)
    (hcur : base + 2 * L ≤ M) : (K : ℕ) → (hK : K ≤ L) → TempPhaseProg M → TempPhaseProg M
  | 0, _, body => body
  | K + 1, hK, body =>
      let idx := L - (K + 1)
      let pos := base + L + idx
      withUnarySplit pos (by dsimp [pos, idx]; omega) ⟨base + idx, by dsimp [idx]; omega⟩ sel
        (wire_ne_of_gt (by dsimp; omega)) (by dsimp [pos]; omega) (by dsimp [pos]; omega)
        (withUnarySplitRange base L sel hsel hcur K (by omega) body)

@[simp] theorem withUnarySplitRange_countTempAnd {M : ℕ} (base L : ℕ) (sel : Wire M)
    (hsel : sel.val < base) (hcur : base + 2 * L ≤ M) :
    ∀ (K : ℕ) (hK : K ≤ L) (body : TempPhaseProg M),
      (withUnarySplitRange base L sel hsel hcur K hK body).countTempAnd =
        K + body.countTempAnd
  | 0, _, _ => by simp [withUnarySplitRange]
  | K + 1, _, _ => by
      simp only [withUnarySplitRange, withUnarySplit_countTempAnd,
          withUnarySplitRange_countTempAnd base L sel hsel hcur K]
      omega

end Internal

open Operator Matrix PosMomSelectSandwich NuclearTwistRealizes
open MeasureBranchHadamardSem (ket bit_cases)
open scoped Matrix ComplexOrder MatrixOrder BigOperators

set_option backward.isDefEq.respectTransparency true

/- ### Per-Coin Bit-Assignment & Matrix Specialization Bridges (`Pos`, `Coin 4`, `Coins 5 & 6`,
  `Coin 7`) -/

theorem slotBitProj_mulVec_ket {N : ℕ} (q : Wire N) (b : Fin 2) (γ : BitAssignment N) : (slotBitProj
    q b).mulVec (ket γ) =
    (if γ q = (if b.val = 1 then (1 : ZMod 2) else 0) then (1 : ℂ) else 0) • ket γ := by
  funext x
  simp only [slotBitProj, Matrix.diagonal_mulVec_single, ket, basisState, Pi.smul_apply,
      Pi.single_apply, smul_eq_mul]
  by_cases hx : x = (basisBitsEquiv N).symm γ
  · subst hx
    simp only [↓reduceIte, mul_one, NuclearTwistRealizes.basisBits_symm_apply]
    fin_cases b
    all_goals
      rcases bit_cases (γ q) with hγ | hγ
      all_goals simp [hγ]
  · simp [hx]

end ConfigCoinDispatchedBarrel288
end CoinDispatchedBarrel288
end
end CoinDispatchedBarrel288

section FastCoinBarrelDecoder279

/-!
# Fast Unified Coin-Dispatched Barrel Index Decoder (`271` `TempAnd`s, `276` Scratch Wires)

Computes the exact 8-bit active electron index `coinBarrelIdx hmPay α` into `[C + 260 .. C + 274]`
using `271` `TempAnd`s (`1,084 T` one-way, `0` `.TOFF` gates) and `276 ≤ 279` clean workspace wires
(`[C .. C + 276)`), proved sound for ALL `BitAssignment (fullSysCoreWires mPayload)` via the
polynomial-time linear/modular weight certificate checker `checkCert` (`WtTrie`).
-/

public section
namespace FastCoinBarrelDecoder279

theorem progNumAnd_append : ∀ p₁ p₂ : List DecStep,
    progNumAnd (p₁ ++ p₂) = progNumAnd p₁ + progNumAnd p₂
  | [], _ => by simp [progNumAnd]
  | _ :: rest, p₂ => by simp [progNumAnd, progNumAnd_append rest p₂, Nat.add_assoc]

end FastCoinBarrelDecoder279
end
end FastCoinBarrelDecoder279

end QuantumComputation.Specs.StoppingPowerSolution
