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

public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.Qutrit216SignedMul

set_option Elab.async false

@[expose] public section

namespace QuantumComputation.Specs.StoppingPowerSolution
open SpecsAux

section ModSlot2ZeroMuxApex46Part2a2
@[expose] public section
namespace Slot2ZeroMuxSignedMul46
section ConfigSlot2ZeroMuxApex46Part2a2
set_option maxRecDepth 4096
set_option exponentiation.threshold 256
open Operator QProg Matrix _root_.DynamicCircuit DynCircuitExt
open scoped Matrix BigOperators Circuit.Notation
open SpecsAux.SpecMirror
open SpecsAux.PhaseGradCatalystCore
open DyadicQft64 hiding dyadicTurn phaseGradKet andSymStep andSymStep_stepFwd
open DyadicQft64WalkCircuit
open NuclearTwistAndXor654Concrete hiding fullSysCoreWires
open NuclearTwistRealizes
open NuclearTwistMulKickAndBridge288
open WindowedSlot2MulKick288
open WindowedSlot2FusedTwist288
local instance (priority := 1000000) instNeZeroTwoPowSlot2ZMA46P2A2 (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩
attribute [local irreducible]
  cnotFanoutCircuit apexGidneyRippleAuxDyn apexGidneyRippleAuxCircuit
def apexGidneyNoCinCircuit {n : ℕ} (cApex : Wire n → Circuit n) (k : ℕ)
    (uWires : Fin (k + 2) → Wire n) (rT : QRegister (k + 2) n) (rC : QRegister (k + 2) n)
    (hu_T : ∀ j, uWires j ∉ rT.image) (hu_C : ∀ j, uWires j ∉ rC.image)
    (hdisj_TC : rT.DisjointWires rC) : Circuit n :=
  ((andSymStep (uWires 0) (rT 0) (rC 0)
      (QRegister.ne_apply_of_not_mem_image rT _ (hu_T 0) 0)
      (QRegister.ne_apply_of_not_mem_image rC _ (hu_C 0) 0)
      (hdisj_TC.ne 0 0)).toTempAndStep.wrapCircuit
    (apexGidneyRippleAuxCircuit cApex k (fun j ↦ uWires j.succ)
      (rT.slice 1 (k + 1) (by omega)) (rC.slice 1 (k + 1) (by omega)) (rC 0)
      (fun j hj ↦ hu_T j.succ (QRegister.image_compose_subset rT _ hj))
      (fun j hj ↦ hu_C j.succ (QRegister.image_compose_subset rC _ hj))
      ((hdisj_TC.compose_left _).compose_right _)
      (fun j h ↦ hu_C j.succ ((QRegister.mem_image rC _).mpr ⟨0, h⟩))
      (fun hj ↦ hdisj_TC.apply_not_mem_left 0 (QRegister.image_compose_subset rT _ hj))
      (QRegExt.head_not_mem_tail_image rC))) ;;ᶜ
  Circuit.CNOT (uWires 0) (rT 0) (QRegister.ne_apply_of_not_mem_image rT _ (hu_T 0) 0)
def apexGidneyNoCinDyn {Var : Type} {n : ℕ} (v : Var) (cApex : Wire n → Circuit n) (k : ℕ)
    (uWires : Fin (k + 2) → Wire n) (rT : QRegister (k + 2) n) (rC : QRegister (k + 2) n)
    (hu_T : ∀ j, uWires j ∉ rT.image) (hu_C : ∀ j, uWires j ∉ rC.image)
    (hdisj_TC : rT.DisjointWires rC) : DynamicCircuit Var n :=
  .seq
    ((andSymStep (uWires 0) (rT 0) (rC 0)
        (QRegister.ne_apply_of_not_mem_image rT _ (hu_T 0) 0)
        (QRegister.ne_apply_of_not_mem_image rC _ (hu_C 0) 0)
        (hdisj_TC.ne 0 0)).toTempAndStep.wrapDynamic v
      (apexGidneyRippleAuxDyn v cApex k (fun j ↦ uWires j.succ)
        (rT.slice 1 (k + 1) (by omega)) (rC.slice 1 (k + 1) (by omega)) (rC 0)
        (fun j hj ↦ hu_T j.succ (QRegister.image_compose_subset rT _ hj))
        (fun j hj ↦ hu_C j.succ (QRegister.image_compose_subset rC _ hj))
        ((hdisj_TC.compose_left _).compose_right _)
        (fun j h ↦ hu_C j.succ ((QRegister.mem_image rC _).mpr ⟨0, h⟩))
        (fun hj ↦ hdisj_TC.apply_not_mem_left 0 (QRegister.image_compose_subset rT _ hj))
        (QRegExt.head_not_mem_tail_image rC)))
    (.circuit (Circuit.CNOT (uWires 0) (rT 0)
      (QRegister.ne_apply_of_not_mem_image rT _ (hu_T 0) 0)))
theorem count_apexGidneyNoCinDyn_toff {Var : Type} {n : ℕ} (v : Var) (cApex : Wire n → Circuit n)
    (hApexToff : ∀ w, (cApex w).count .TOFF = 0) (k : ℕ) (uWires : Fin (k + 2) → Wire n)
    (rT : QRegister (k + 2) n) (rC : QRegister (k + 2) n) (hu_T : ∀ j, uWires j ∉ rT.image)
    (hu_C : ∀ j, uWires j ∉ rC.image) (hdisj_TC : rT.DisjointWires rC) :
    (apexGidneyNoCinDyn v cApex k uWires rT rC hu_T hu_C hdisj_TC).count .TOFF = 0 := by
  rw [apexGidneyNoCinDyn]
  simp only [NuclearTwistMulKickAndBridge288.count_dyn_seq,
    TempAndStep.count_wrapDynamic_toff _ _ _ (andSymStep ..).clifford,
    count_apexGidneyRippleAuxDyn_toff v cApex hApexToff]
  rfl
theorem count_apexGidneyNoCinDyn_t {Var : Type} {n : ℕ} (v : Var) (cApex : Wire n → Circuit n)
    (hApexT : ∀ w, (cApex w).count .T = 1) (k : ℕ) (uWires : Fin (k + 2) → Wire n)
    (rT : QRegister (k + 2) n) (rC : QRegister (k + 2) n) (hu_T : ∀ j, uWires j ∉ rT.image)
    (hu_C : ∀ j, uWires j ∉ rC.image) (hdisj_TC : rT.DisjointWires rC) :
    (apexGidneyNoCinDyn v cApex k uWires rT rC hu_T hu_C hdisj_TC).count .T =
      4 * (k + 2) + 1 := by
  rw [apexGidneyNoCinDyn]
  simp only [NuclearTwistMulKickAndBridge288.count_dyn_seq,
    TempAndStep.count_wrapDynamic_t _ _ _ (andSymStep ..).clifford,
    count_apexGidneyRippleAuxDyn_t v cApex hApexT]
  rw [show (DynamicCircuit.circuit (Var := Var) (Circuit.CNOT _ _ _)).count .T = 0 from rfl]
  omega
theorem apexGidneyNoCin_correct {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    [NeZero (2 ^ n)] (v : Var) (cApex : Wire n → Circuit n)
    (φApex : BitAssignment n → ZMod 2 → ℂ) (k : ℕ) (uWires : Fin (k + 2) → Wire n)
    (rT : QRegister (k + 2) n) (rC : QRegister (k + 2) n) (hu_T : ∀ j, uWires j ∉ rT.image)
    (hu_C : ∀ j, uWires j ∉ rC.image) (hdisj_TC : rT.DisjointWires rC) (hApex_pp : ∀ w ∈
    rC.image, PhasePerm (∅ : Finset (Wire n)) (cApex w) (fun γ ↦ φApex γ (γ w)) id) (hApex_upd
    : ∀ (γ : BitAssignment n) (w : Wire n), w ∈ rC.image → ∀ b : ZMod 2, φApex
    (Function.update γ w b) = φApex γ) : ∃ φ f, CleanPhasePermEquiv v rC rT.image
    (apexGidneyNoCinDyn v cApex k uWires rT rC hu_T hu_C hdisj_TC)
    (apexGidneyNoCinCircuit cApex k uWires rT rC hu_T hu_C hdisj_TC) φ f ∧ (∀ β, (∀ i : Fin (k
    + 2), β (rC i) = 0) → ∃ c_out : ZMod 2, regVal rT (f β) + 2 ^ (k + 2) * c_out.val = regVal
    rT β + bitsVal (fun j ↦ β (uWires j)) ∧ φ β = φApex β c_out) := by
  let rT_rest := rT.slice 1 (k + 1) (by omega)
  let rC_rest := rC.slice 1 (k + 1) (by omega)
  have hut : uWires 0 ≠ rT 0 := QRegister.ne_apply_of_not_mem_image rT _ (hu_T 0) 0
  have huc : uWires 0 ≠ rC 0 := QRegister.ne_apply_of_not_mem_image rC _ (hu_C 0) 0
  have htc : rT 0 ≠ rC 0 := hdisj_TC.ne 0 0
  have hc0_u : ∀ j : Fin (k + 1), rC 0 ≠ uWires j.succ :=
    fun j h ↦ hu_C j.succ ((QRegister.mem_image rC _).mpr ⟨0, h⟩)
  have hc0_T_rest : rC 0 ∉ rT_rest.image :=
    fun hj ↦ hdisj_TC.apply_not_mem_left 0 (QRegister.image_compose_subset rT _ hj)
  have hc0_C_rest : rC 0 ∉ rC_rest.image := QRegExt.head_not_mem_tail_image rC
  have ht0_T_rest : rT 0 ∉ rT_rest.image := QRegExt.head_not_mem_tail_image rT
  have hu0_T_rest : uWires 0 ∉ rT_rest.image :=
    fun hj ↦ hu_T 0 (QRegister.image_compose_subset rT _ hj)
  obtain ⟨φ_rest, f_rest, hEq_rest, hVal_rest⟩ := apexGidneyRippleAux_correct v cApex φApex k
      (fun j ↦ uWires j.succ) rT_rest rC_rest (rC 0)
      (fun j hj ↦ hu_T j.succ (QRegister.image_compose_subset rT _ hj))
      (fun j hj ↦ hu_C j.succ (QRegister.image_compose_subset rC _ hj))
      ((hdisj_TC.compose_left _).compose_right _) hc0_u hc0_T_rest hc0_C_rest
      (fun w hw ↦ hApex_pp w (QRegister.image_compose_subset rC _ hw))
      (fun γ w hw ↦ hApex_upd γ w (QRegister.image_compose_subset rC _ hw))
  let st := andSymStep (uWires 0) (rT 0) (rC 0) hut huc htc
  have hDisjSM : Disjoint st.S rT_rest.image := by
    simp only [st, andSymStep, Finset.disjoint_insert_left, Finset.disjoint_singleton_left]
    exact ⟨hu0_T_rest, ht0_T_rest, hc0_T_rest⟩
  have hDisjSR : Disjoint st.S rC_rest.image := by
    simp only [st, andSymStep, Finset.disjoint_insert_left, Finset.disjoint_singleton_left]
    exact ⟨fun hj ↦ hu_C 0 (QRegister.image_compose_subset rC _ hj), fun hj ↦
      hdisj_TC.apply_not_mem_right 0 (QRegister.image_compose_subset rC _ hj), hc0_C_rest⟩
  have hWrap := (CleanPhasePermEquiv.wrapSymStep v st hDisjSM rC rfl hDisjSR hEq_rest).mono
    (QRegister.image_compose_subset rT _)
  let fTail : BitAssignment n → BitAssignment n :=
    fun γ ↦ Function.update γ (rT 0) (γ (rT 0) + γ (uWires 0))
  have ht0_mem : rT 0 ∈ rT.image := (QRegister.mem_image rT _).mpr ⟨0, rfl⟩
  have hTailEq : CleanPhasePermEquiv v rC rT.image
      (.circuit (Circuit.CNOT (uWires 0) (rT 0) hut)) (Circuit.CNOT (uWires 0) (rT 0) hut)
      (fun _ ↦ 1) fTail := CleanPhasePermEquiv.ofCircuit v rC (PhasePerm.of_classicalPerm
      (ClassicalPerm.CNOT (uWires 0) (rT 0) hut) (fun γ w hw ↦ Function.update_of_ne (fun h :
      w = rT 0 ↦ hw (h ▸ ht0_mem)) _ _))
  have hDisjTC : Disjoint rT.image rC.image :=
    (QRegExt.disjointWires_iff_disjoint_image rT rC).mp hdisj_TC
  have hSeq := CleanPhasePermEquiv.seq hDisjTC hWrap hTailEq
  refine ⟨_, _, hSeq, fun β hz ↦ ?_⟩
  let c₀ : ZMod 2 := β (uWires 0) * β (rT 0)
  have hStep : st.stepFwd β = Function.update β (rC 0) c₀ :=
    andSymStep_stepFwd (uWires 0) (rT 0) (rC 0) hut huc htc β (hz 0)
  let β_mid := st.stepFwd β
  have hβ_ne {w : Wire n} (hw : w ≠ rC 0) : β_mid w = β w := by
    simpa only [β_mid, hStep] using Function.update_of_ne hw c₀ β
  have hz_rest (i : Fin (k + 1)) : β_mid (rC_rest i) = 0 := by
    have hi := (QRegister.mem_image rC_rest _).mpr ⟨i, rfl⟩
    obtain ⟨q, hq⟩ := (QRegister.mem_image rC _).mp (QRegister.image_compose_subset rC _ hi)
    exact (hβ_ne fun h ↦ hc0_C_rest (h ▸ hi)).trans (hq ▸ hz q)
  obtain ⟨c_out, hVal_mid, hPhi_mid⟩ := hVal_rest β_mid hz_rest
  refine ⟨c_out, ?_, ?_⟩
  · have hT_mid : regVal rT_rest β_mid = regVal rT_rest β :=
      regVal_congr rT_rest fun i ↦
        hβ_ne fun h ↦ hc0_T_rest (h ▸ (QRegister.mem_image rT_rest _).mpr ⟨i, rfl⟩)
    have hu_mid : bitsVal (fun j : Fin (k + 1) ↦ β_mid (uWires j.succ)) =
        bitsVal (fun j ↦ β (uWires j.succ)) :=
      congrArg bitsVal (funext fun j ↦ hβ_ne (hc0_u j).symm)
    have hc0_mid : β_mid (rC 0) = c₀ := by simp [β_mid, hStep]
    rw [hT_mid, hu_mid, hc0_mid] at hVal_mid
    let fAll := fTail ∘ fun (γ : BitAssignment n) (w : Wire n) ↦
      if w ∈ rT_rest.image then f_rest (st.stepFwd γ) w else γ w
    have hf0 : fAll β (rT 0) = β (uWires 0) + β (rT 0) := by
      dsimp only [fAll, fTail, Function.comp_apply]
      simp only [ht0_T_rest, hu0_T_rest, ↓reduceIte, Function.update_self]
      ring
    have hf_rest_eq : regVal rT_rest (fAll β) = regVal rT_rest (f_rest β_mid) :=
      regVal_congr rT_rest fun i ↦ by
        have hi := (QRegister.mem_image rT_rest _).mpr ⟨i, rfl⟩
        dsimp only [fAll, fTail, Function.comp_apply, β_mid]
        simp only [Function.update_of_ne (fun h ↦ ht0_T_rest (h ▸ hi) : rT_rest i ≠ rT 0),
          hi, ↓reduceIte]
    rw [regVal_head_tail rT (fAll β), hf0, hf_rest_eq, regVal_head_tail rT β,
      @bitsVal_succ_head_tail (k + 1) (fun j ↦ β (uWires j)), pow_succ' 2 (k + 1)]
    have hhalf := zmod2_half_adder_val_zm (β (uWires 0)) (β (rT 0))
    dsimp only [c₀] at hVal_mid
    linarith
  · rw [mul_one, hPhi_mid]
    dsimp only [β_mid]
    rw [hStep, hApex_upd β (rC 0) ((QRegister.mem_image rC _).mpr ⟨0, rfl⟩) c₀]
attribute [local irreducible] apexGidneyNoCinDyn apexGidneyNoCinCircuit
noncomputable def ctrlSignApexShiftDyn {Var : Type} {n : ℕ} (v : Var) (s k : ℕ)
    (hs45 : s + (k + 2) = 45) (wNeg : Wire n) (uWires : Fin (k + 2) → Wire n)
    (rPG45 : QRegister 45 n) (rC : QRegister (k + 2) n)
    (hwNeg_T : wNeg ∉ (rPG45.slice s (k + 2) (by omega)).image)
    (hu_T : ∀ j, uWires j ∉ (rPG45.slice s (k + 2) (by omega)).image)
    (hu_C : ∀ j, uWires j ∉ rC.image)
    (hdisj_TC : (rPG45.slice s (k + 2) (by omega)).DisjointWires rC) : DynamicCircuit Var n :=
  let rHigh := rPG45.slice s (k + 2) (by omega)
  let cFan := cnotFanoutCircuit (k + 2) wNeg rHigh hwNeg_T
  .seq (.circuit cFan)
    (.seq
      (apexGidneyNoCinDyn v (cApexQuantum wNeg) k uWires rHigh rC hu_T hu_C hdisj_TC)
      (.circuit cFan))
@[simp] theorem count_ctrlSignApexShiftDyn_toff {Var : Type} {n : ℕ} (v : Var) (s k : ℕ)
    (hs45 : s + (k + 2) = 45) (wNeg : Wire n) (uWires : Fin (k + 2) → Wire n)
    (rPG45 : QRegister 45 n) (rC : QRegister (k + 2) n)
    (hwNeg_T : wNeg ∉ (rPG45.slice s (k + 2) (by omega)).image)
    (hu_T : ∀ j, uWires j ∉ (rPG45.slice s (k + 2) (by omega)).image)
    (hu_C : ∀ j, uWires j ∉ rC.image)
    (hdisj_TC : (rPG45.slice s (k + 2) (by omega)).DisjointWires rC) : (ctrlSignApexShiftDyn v
    s k hs45 wNeg uWires rPG45 rC hwNeg_T hu_T hu_C hdisj_TC).count .TOFF = 0 := by
  simp [ctrlSignApexShiftDyn,
    count_apexGidneyNoCinDyn_toff v (cApexQuantum wNeg) (count_cApexQuantum_toff wNeg)]
@[simp] theorem count_ctrlSignApexShiftDyn_t {Var : Type} {n : ℕ} (v : Var) (s k : ℕ)
    (hs45 : s + (k + 2) = 45) (wNeg : Wire n) (uWires : Fin (k + 2) → Wire n)
    (rPG45 : QRegister 45 n) (rC : QRegister (k + 2) n)
    (hwNeg_T : wNeg ∉ (rPG45.slice s (k + 2) (by omega)).image)
    (hu_T : ∀ j, uWires j ∉ (rPG45.slice s (k + 2) (by omega)).image)
    (hu_C : ∀ j, uWires j ∉ rC.image)
    (hdisj_TC : (rPG45.slice s (k + 2) (by omega)).DisjointWires rC) : (ctrlSignApexShiftDyn v
    s k hs45 wNeg uWires rPG45 rC hwNeg_T hu_T hu_C hdisj_TC).count .T = 4 * (k + 2) + 1 := by
  simp [ctrlSignApexShiftDyn,
    count_apexGidneyNoCinDyn_t v (cApexQuantum wNeg) (count_cApexQuantum_t wNeg)]
theorem ctrlSignApexShift_spec {Var : Type} [Fintype Var] [DecidableEq Var]
    {n : ℕ} [NeZero (2 ^ n)] (v : Var)
    (s k : ℕ) (hs45 : s + (k + 2) = 45)
    (wNeg : Wire n) (uWires : Fin (k + 2) → Wire n)
    (rPG45 : QRegister 45 n) (rC : QRegister (k + 2) n)
    (hwNeg_T : wNeg ∉ (rPG45.slice s (k + 2) (by omega)).image)
    (hwNeg_C : wNeg ∉ rC.image)
    (hu_T : ∀ j, uWires j ∉ (rPG45.slice s (k + 2) (by omega)).image)
    (hu_C : ∀ j, uWires j ∉ rC.image)
    (hdisj_TC : (rPG45.slice s (k + 2) (by omega)).DisjointWires rC) :
    ∃ c f φ,
      CleanPhasePermEquiv v rC rPG45.image
        (ctrlSignApexShiftDyn v s k hs45 wNeg uWires rPG45 rC hwNeg_T hu_T hu_C hdisj_TC)
        c φ f ∧
      (∀ β, (∀ i : Fin (k + 2), β (rC i) = 0) →
        let d_low : ℤ := (1 - 2 * ((β wNeg).val : ℤ)) * (2 ^ s : ℤ) *
          (bitsVal (fun j ↦ β (uWires j)) : ℤ)
        ((regVal rPG45 (f β) : ℤ) - ((regVal rPG45 β : ℤ) + d_low)) % (2 ^ 45 : ℤ) = 0 ∧
        φ β = DyadicQft64.dyadicTurn 48
          (d_low - ((regVal rPG45 (f β) : ℤ) - (regVal rPG45 β : ℤ)) +
            (2 ^ 45 : ℤ) * ((β wNeg).val : ℤ))) := by
  let rHigh := rPG45.slice s (k + 2) (by omega)
  let φApex : BitAssignment n → ZMod 2 → ℂ := fun γ b ↦ DyadicQft64.dyadicTurn 48 ((1 - 2 *
      ((γ wNeg).val : ℤ)) * (2 ^ 45 : ℤ) * (b.val : ℤ) + (2 ^ 45 : ℤ) * ((γ wNeg).val : ℤ))
  obtain ⟨φGid, fGid, hEqGid, hValGid⟩ :=
    apexGidneyNoCin_correct v (cApexQuantum wNeg) φApex k uWires rHigh rC hu_T hu_C hdisj_TC
      (fun w hw ↦ phasePerm_cApexQuantum wNeg w (fun h ↦ hwNeg_C (h ▸ hw)))
      (fun γ w hw b ↦ by
        funext x
        dsimp only [φApex]
        rw [Function.update_of_ne (fun h : wNeg = w ↦ hwNeg_C (h ▸ hw))])
  have hFanEq : CleanPhasePermEquiv v rC rHigh.image
      (.circuit (cnotFanoutCircuit (k + 2) wNeg rHigh hwNeg_T))
      (cnotFanoutCircuit (k + 2) wNeg rHigh hwNeg_T) (fun _ ↦ 1) (fanoutToggleFn wNeg rHigh) :=
    CleanPhasePermEquiv.ofCircuit v rC (phasePerm_cnotFanout wNeg rHigh hwNeg_T)
  have hDisjHC : Disjoint rHigh.image rC.image :=
    (QRegExt.disjointWires_iff_disjoint_image rHigh rC).mp hdisj_TC
  have hSeq := (CleanPhasePermEquiv.seq hDisjHC hFanEq
    (CleanPhasePermEquiv.seq hDisjHC hEqGid hFanEq)).mono (QRegister.image_compose_subset rPG45 _)
  refine ⟨_, _, _, hSeq, fun β hz ↦ ?_⟩
  let β₁ := fanoutToggleFn wNeg rHigh β
  have hz₁ : ∀ i : Fin (k + 2), β₁ (rC i) = 0 := fun i ↦ by
    have hnot : rC i ∉ rHigh.image :=
      Finset.disjoint_right.mp hDisjHC ((QRegister.mem_image rC _).mpr ⟨i, rfl⟩)
    exact (fanoutToggleFn_of_not_mem wNeg rHigh β hnot).trans (hz i)
  have hu₁ : (fun j : Fin (k + 2) ↦ β₁ (uWires j)) = (fun j ↦ β (uWires j)) :=
    funext fun j ↦ fanoutToggleFn_of_not_mem wNeg rHigh β (hu_T j)
  have hwNeg₁ : β₁ wNeg = β wNeg := fanoutToggleFn_of_not_mem wNeg rHigh β hwNeg_T
  have hwNeg₂ : fGid β₁ wNeg = β wNeg := (hEqGid.phasePerm.outside β₁ wNeg hwNeg_T).trans hwNeg₁
  obtain ⟨c_out, hAdd, hPhi⟩ := hValGid β₁ hz₁
  rw [hu₁] at hAdd
  let fShift := (fanoutToggleFn wNeg rHigh ∘ fGid) ∘ fanoutToggleFn wNeg rHigh
  have hLoEq : bitsVal (fun i : Fin s ↦ fShift β (rPG45 ⟨i.val, by omega⟩)) =
      bitsVal (fun i : Fin s ↦ β (rPG45 ⟨i.val, by omega⟩)) :=
    congrArg bitsVal <| funext fun i ↦ by
      have hnot : rPG45 ⟨i.val, by omega⟩ ∉ rHigh.image := fun hm ↦ by
        obtain ⟨j, hj⟩ := (QRegister.mem_image rHigh _).mp hm
        have hv := congrArg Fin.val
          (rPG45.wires.injective ((QRegister.slice_apply ..).symm.trans hj))
        dsimp only at hv
        omega
      simp only [fShift, Function.comp_apply, fanoutToggleFn_of_not_mem wNeg rHigh _ hnot,
        hEqGid.phasePerm.outside _ _ hnot]
  have hAlg := signed_carry_shift_algebra hs45
    (bitsVal (fun i : Fin s ↦ β (rPG45 ⟨i.val, by omega⟩)))
    (regVal rHigh β) (regVal rHigh (fGid β₁)) (regVal rHigh (fShift β))
    (bitsVal (fun j ↦ β (uWires j))) c_out (β wNeg)
    (regVal_lt_two_pow rHigh β) (regVal_lt_two_pow rHigh (fGid β₁))
    (fun hb0 ↦ by
      have h1 : regVal rHigh β₁ = regVal rHigh β := by simp [β₁, regVal_fanoutToggleFn, hb0]
      exact ⟨h1 ▸ hAdd, by simp [fShift, β₁, regVal_fanoutToggleFn, hwNeg₂, hb0]⟩)
    (fun hb1 ↦ by
      have h1 : regVal rHigh β₁ = (2 ^ (k + 2) - 1) - regVal rHigh β := by
        simp [β₁, regVal_fanoutToggleFn, hb1]
      exact ⟨h1 ▸ hAdd, by simp [fShift, β₁, regVal_fanoutToggleFn, hwNeg₂, hb1]⟩)
  have hSplitIn : regVal rPG45 β =
      bitsVal (fun i : Fin s ↦ β (rPG45 ⟨i.val, by omega⟩)) + 2 ^ s * regVal rHigh β :=
    regVal_split_at_shift hs45 rPG45 β
  have hSplitOut : regVal rPG45 (fShift β) =
      bitsVal (fun i : Fin s ↦ β (rPG45 ⟨i.val, by omega⟩)) + 2 ^ s * regVal rHigh (fShift β) := by
    rw [regVal_split_at_shift hs45 rPG45 (fShift β), hLoEq]
  dsimp only [fShift] at hSplitOut hAlg
  dsimp only [φApex] at hPhi
  rw [hwNeg₁] at hPhi
  dsimp only
  rw [hSplitOut, hSplitIn]
  exact ⟨hAlg.1, by rw [mul_one, one_mul, hPhi, hAlg.2]⟩
attribute [local irreducible] ctrlSignApexShiftDyn
theorem bitsVal_48_shift_mod48 {s k : ℕ} (hs45 : s + (k + 2) = 45)
    (sgn : ℤ) (hsgn : sgn = 1 ∨ sgn = -1) (M : Fin 48 → ZMod 2) :
    ((sgn * (2 ^ s : ℤ) * (bitsVal (fun j : Fin (k + 2) ↦ M ⟨j.val, by omega⟩) : ℤ) +
        sgn * (2 ^ 45 : ℤ) * ((M ⟨k + 2, by omega⟩).val : ℤ) +
        sgn * (2 ^ 46 : ℤ) * ((M ⟨k + 3, by omega⟩).val : ℤ) +
        (2 ^ 47 : ℤ) * ((M ⟨k + 4, by omega⟩).val : ℤ)) -
      sgn * (2 ^ s : ℤ) * (bitsVal M : ℤ)) % (2 ^ 48 : ℤ) = 0 := by
  have hSplit48 : bitsVal M =
      bitsVal (fun j : Fin (k + 5) ↦ M ⟨j.val, by omega⟩) +
        2 ^ (k + 5) * bitsVal (fun j : Fin s ↦ M ⟨k + 5 + j.val, by omega⟩) :=
    regVal_split_at_shift (by omega : (k + 5) + s = 48) (QRegExt.idReg 48) M
  have hSplit5 : bitsVal (fun j : Fin (k + 5) ↦ M ⟨j.val, by omega⟩) =
      bitsVal (fun j : Fin (k + 2) ↦ M ⟨j.val, by omega⟩) +
        (M ⟨k + 2, by omega⟩).val * 2 ^ (k + 2) +
        (M ⟨k + 3, by omega⟩).val * 2 ^ (k + 3) +
        (M ⟨k + 4, by omega⟩).val * 2 ^ (k + 4) := by
    rw [show bitsVal (fun j : Fin (k + 5) ↦ M ⟨j.val, by omega⟩) =
        bitsVal (fun j : Fin ((k + 2) + 1 + 1 + 1) ↦ M ⟨j.val, by omega⟩) from rfl]
    unfold bitsVal
    rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
  have hPow45 : (2 ^ s : ℤ) * (2 ^ (k + 2) : ℤ) = (2 ^ 45 : ℤ) := by rw [← pow_add, hs45]
  obtain ⟨qSgn, hqSgn⟩ : ∃ q : ℤ, 1 - sgn = 2 * q := by
    rcases hsgn with rfl | rfl
    · exact ⟨0, by ring⟩
    · exact ⟨1, by ring⟩
  let mHi : ℤ := (bitsVal (fun j : Fin s ↦ M ⟨k + 5 + j.val, by omega⟩) : ℤ)
  let m4 : ℤ := ((M ⟨k + 4, by omega⟩).val : ℤ)
  have hDiff : (sgn * (2 ^ s : ℤ) * (bitsVal (fun j : Fin (k + 2) ↦ M ⟨j.val, by omega⟩) : ℤ) +
        sgn * (2 ^ 45 : ℤ) * ((M ⟨k + 2, by omega⟩).val : ℤ) +
        sgn * (2 ^ 46 : ℤ) * ((M ⟨k + 3, by omega⟩).val : ℤ) +
        (2 ^ 47 : ℤ) * ((M ⟨k + 4, by omega⟩).val : ℤ)) -
      sgn * (2 ^ s : ℤ) * (bitsVal M : ℤ) = (qSgn * m4 - sgn * mHi) * (2 ^ 48 : ℤ) := by
    rw [hSplit48, hSplit5]
    push_cast
    rw [show (2 : ℤ) ^ (k + 3) = 2 * (2 : ℤ) ^ (k + 2) by ring,
      show (2 : ℤ) ^ (k + 4) = 4 * (2 : ℤ) ^ (k + 2) by ring,
      show (2 : ℤ) ^ (k + 5) = 8 * (2 : ℤ) ^ (k + 2) by ring]
    linear_combination
      -(sgn * ((M ⟨k + 2, by omega⟩).val : ℤ) +
          2 * sgn * ((M ⟨k + 3, by omega⟩).val : ℤ) +
          4 * sgn * m4 + 8 * sgn * mHi) * hPow45 +
        (2 ^ 47 : ℤ) * m4 * hqSgn
  rw [hDiff, Int.mul_emod_left]
theorem realizesCleanPair_apexCatModAddZ_of_cleanPhasePerm
    {Var : Type} [Fintype Var] [DecidableEq Var] {kSys mScr mAnc n : ℕ} [NeZero (2 ^ n)]
    (v : Var) (rSys : QRegister kSys n) (rPGTwist : QRegister 48 n)
    (rScr : QRegister mScr n) (rAnc : QRegister mAnc n) (hSMP : rSys.DisjointWires rPGTwist)
    (hSubAnc : rScr.image ⊆ rAnc.image) {dFwd dInv : DynamicCircuit Var n}
    (Δ_sys : BitAssignment kSys → ℤ) {cF cI : Circuit n}
    {fF fI : BitAssignment n → BitAssignment n} {φF φI : BitAssignment n → ℂ}
    (hEqF : CleanPhasePermEquiv v rScr (rPGTwist.slice 0 45 (by decide)).image dFwd cF φF fF)
    (hValF : ∀ β : BitAssignment n, (∀ i : Fin mScr, β (rScr i) = 0) →
      ((regVal (rPGTwist.slice 0 45 (by decide)) (fF β) : ℤ) -
        ((regVal (rPGTwist.slice 0 45 (by decide)) β : ℤ) +
          Δ_sys (fun i ↦ β (rSys i)))) % (2 ^ 45 : ℤ) = 0 ∧
      φF β = DyadicQft64.dyadicTurn 48
        (Δ_sys (fun i ↦ β (rSys i)) -
          ((regVal (rPGTwist.slice 0 45 (by decide)) (fF β) : ℤ) -
            (regVal (rPGTwist.slice 0 45 (by decide)) β : ℤ))))
    (hEqI : CleanPhasePermEquiv v rScr (rPGTwist.slice 0 45 (by decide)).image dInv cI φI fI)
    (hValI : ∀ β : BitAssignment n, (∀ i : Fin mScr, β (rScr i) = 0) →
      ((regVal (rPGTwist.slice 0 45 (by decide)) (fI β) : ℤ) -
        ((regVal (rPGTwist.slice 0 45 (by decide)) β : ℤ) +
          (-Δ_sys (fun i ↦ β (rSys i))))) % (2 ^ 45 : ℤ) = 0 ∧
      φI β = DyadicQft64.dyadicTurn 48
        ((-Δ_sys (fun i ↦ β (rSys i))) -
          ((regVal (rPGTwist.slice 0 45 (by decide)) (fI β) : ℤ) -
            (regVal (rPGTwist.slice 0 45 (by decide)) β : ℤ)))) :
    RealizesCleanPair (rSys.concat rPGTwist hSMP) rAnc
      (apexCatModAddZ kSys Δ_sys) dFwd dInv := by
  have hzSub (β : BitAssignment n) (hz : ∀ q : Fin mAnc, β (rAnc q) = 0) (i : Fin mScr) :
      β (rScr i) = 0 := by
    obtain ⟨q, hq⟩ := (QRegister.mem_image rAnc _).mp
      (hSubAnc ((QRegister.mem_image rScr _).mpr ⟨i, rfl⟩))
    exact hq ▸ hz q
  refine ⟨realizesClean_of_cleanPhasePermEquiv (hEqF.widenAnc hSubAnc) fun β hz ↦ ?_, ?_⟩
  · obtain ⟨hMod, hPhi⟩ := hValF β (hzSub β hz)
    rw [apexCatModAddZ_mulVec_basisKet rSys rPGTwist hSMP Δ_sys (fF β) β
      (hEqF.phasePerm.outside β) hMod, hPhi]
  · rw [apexCatModAddZ_inv kSys Δ_sys]
    refine realizesClean_of_cleanPhasePermEquiv (hEqI.widenAnc hSubAnc) fun β hz ↦ ?_
    obtain ⟨hMod, hPhi⟩ := hValI β (hzSub β hz)
    rw [apexCatModAddZ_mulVec_basisKet rSys rPGTwist hSMP (fun x ↦ -Δ_sys x) (fI β) β
      (hEqI.phasePerm.outside β) hMod, hPhi]
attribute [local irreducible] apexCatModAddZ
end ConfigSlot2ZeroMuxApex46Part2a2
end Slot2ZeroMuxSignedMul46
end
end ModSlot2ZeroMuxApex46Part2a2

section ModSubvoxelNuclearTrunc37Physics
@[expose] public section
namespace SubvoxelNuclearTrunc37Physics
section ConfigSubvoxelNuclearTrunc37Physics
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 4096
set_option exponentiation.threshold 8192
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup
local instance (priority := 1000000) instNeZeroTwoPowTrunc37Phys (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩
open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt Real
open scoped Matrix BigOperators Matrix.Norms.L2Operator
open SpecsAux.SpecMirror
noncomputable def nuclearM37 (c : Configuration) (l : Fin 216) (w : Fin 3) : ℕ :=
  ⌊(2 ^ 37 : ℝ) * Int.fract (c.nuclei l w / cellVolume ^ ((1 : ℝ) / 3)) + 1 / 2⌋₊ % 2 ^ 37
noncomputable def trunc37Cfg (c : Configuration) : Configuration where
  nuclei := fun l w ↦ (nuclearM37 c l w : ℝ) * (cellVolume ^ ((1 : ℝ) / 3) / (2 ^ 37 : ℝ))
  projectileMomentum := c.projectileMomentum
  momentum_le := c.momentum_le
end ConfigSubvoxelNuclearTrunc37Physics
end SubvoxelNuclearTrunc37Physics
end
end ModSubvoxelNuclearTrunc37Physics

section ModZeroSubwireGridPert80
@[expose] public section
namespace ZeroSubwireGridPert80
section ConfigZeroSubwireGridPert80
set_option backward.isDefEq.respectTransparency true
set_option exponentiation.threshold 8192
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup
local instance (priority := 1000000) instNeZeroTwoPowZeroSubGrid (k : ℕ) : NeZero (2 ^ k) :=
  ⟨Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos k)⟩
open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt Real
open scoped Matrix BigOperators Matrix.Norms.L2Operator
open SpecsAux.SpecMirror
open SpecsAux.BridgeFermionicComm.SpecInner
open SpecsAux.FullScaleBESector
open PosMomSelectSandwich (slotBitProj)
open PosMomSelectDynamic (unitaryConj unitaryConj_val)
open TwosCompAndWire0Cancel (smToTwosSysUnitary)
open SixSlotEndpointJunctionBridge (commute_fermionicProjector_of_inGridPerm)
open FullSysPrepare6Slot (fullSysCoinIdx coinSelOutcome basisBits_coinSelOutcome_coin
  basisBits_coinSelOutcome_outside)
open FullSysCatSegmentBridge (fullSysCoreWires fullSysBEWires beCoreBlock)
open FullSysFullPrepareAndTopConcrete (selWiresSym coreWiresSym coreSysSym coreAncSym selCoin3Sym
  coreHadamardUnitary)
open FullSysMomSlots0135Concrete (momCoreWires iSlot0Mom iSlot1Mom iSlot2Mom coinBitFin2 momCoinProj
  momCoinProj_eq_diagonal momCoinProj_mul_ancOutcomeProj slotBitProj_mul_idem slotBitProj_self_adj
  slotBitProj_comm_any coreHadamardMom_comm_momCoinProj offProj_left_of_sa_and_right
  MomSingleSlotOracle)
open OraAndPrepBundle (castNatUnitary_embedUnitary momCoreWires_eq_fullSysCoreWires
  coreUnitaryFromFullSys coreSysSym_eq_momSysReg_sym coreAncSym_eq_momAncReg_sym
  selCoin3Sym_eq_momCoin3Sel_sym coreHadamardUnitary_eq_mom_sym posCoin01ProjMom
  op_sandwiched_proj_sub_eq PosPostPrepCert)
private theorem lemHex433 {a b : ℕ} (h : a = b) (j : Fin a) : (h ▸ j).val = j.val := by
  subst h; rfl
theorem beCoreBlock_eq_coreUnitaryFromFullSys {mPayload : ℕ} (U : Unitary (2 ^ (fullSysCoreWires
    mPayload))) : (beCoreBlock mPayload).embedUnitary U =
    coreUnitaryFromFullSys U := by
  let ha := (momCoreWires_eq_fullSysCoreWires mPayload).symm
  have h :=
    castNatUnitary_embedUnitary ha (rfl : fullSysBEWires mPayload = momCoreWires mPayload)
      (beCoreBlock mPayload) (QRegister.whole (momCoreWires mPayload))
      (fun i ↦ by
        change 0 + (ha.symm ▸ i).val = i.val
        rw [Nat.zero_add, lemHex433])
      U
  simpa only [QRegister.whole_embedUnitary] using h
theorem coinSelOutcome_80_zero : coinSelOutcome (selCoin3Sym 80) 0 =
    (0 : Fin (2 ^ (selWiresSym 80))) := by
  apply (basisBitsEquiv (selWiresSym 80)).injective
  funext w
  change basisBits (selWiresSym 80) (coinSelOutcome (selCoin3Sym 80) 0) w =
    basisBits (selWiresSym 80) 0 w
  by_cases hw : w ∈ (selCoin3Sym 80).image
  · rcases (QRegister.mem_image (selCoin3Sym 80) w).mp hw with ⟨j, rfl⟩
    rw [basisBits_coinSelOutcome_coin, basisBits_zero_at, basisBits_zero_at]
  · rw [basisBits_coinSelOutcome_outside (selCoin3Sym 80) 0 hw, basisBits_zero_at]
theorem extractIndex_coinSelOutcome_80 (c : Fin 8) : (selCoin3Sym 80).extractIndex (coinSelOutcome
    (selCoin3Sym 80) c) = c := by
  apply (basisBitsEquiv 3).injective
  funext j
  change basisBits 3 ((selCoin3Sym 80).extractIndex (coinSelOutcome (selCoin3Sym 80) c)) j =
    basisBits 3 c j
  rw [QRegister.basisBits_extractIndex, basisBits_coinSelOutcome_coin]
theorem eq_coinSelOutcome_80_of_outside_zero (x : Fin (2 ^ (selWiresSym 80))) (hOut : ∀ w ∉
    (selCoin3Sym 80).image, basisBits (selWiresSym 80) x w = 0) : x
    = coinSelOutcome (selCoin3Sym 80) ((selCoin3Sym 80).extractIndex x) := by
  apply (basisBitsEquiv (selWiresSym 80)).injective
  funext w
  change basisBits (selWiresSym 80) x w =
    basisBits (selWiresSym 80) (coinSelOutcome (selCoin3Sym 80) ((selCoin3Sym 80).extractIndex x)) w
  by_cases hw : w ∈ (selCoin3Sym 80).image
  · rcases (QRegister.mem_image (selCoin3Sym 80) w).mp hw with ⟨j, rfl⟩
    rw [basisBits_coinSelOutcome_coin, QRegister.basisBits_extractIndex]
  · rw [hOut w hw, basisBits_coinSelOutcome_outside _ _ hw]
def elemMat86 (a b : Fin (2 ^ (selWiresSym 80))) : Operator (2 ^ (selWiresSym 80)) :=
  fun x y ↦ if x = a ∧ y = b then 1 else 0
theorem elemMat86_conjTranspose (a b : Fin (2 ^ (selWiresSym 80))) : (elemMat86 a b)ᴴ =
    elemMat86 b a := by
  ext x y
  simp [elemMat86, and_comm]
theorem elemMat86_mul (a b c d : Fin (2 ^ (selWiresSym 80))) :
    elemMat86 a b * elemMat86 c d = if b = c then elemMat86 a d else 0 := by
  ext x y
  simp only [Matrix.mul_apply, elemMat86]
  rw [Finset.sum_eq_single b (fun z _ hzb ↦ by simp [hzb])
    (fun hb ↦ absurd (Finset.mem_univ b) hb)]
  by_cases hbc : b = c
  · subst hbc
    by_cases hxa : x = a
    · simp [hxa, elemMat86]
    · simp [hxa, elemMat86]
  · simp [hbc]
theorem embed_elemMat86_diag (a : Fin (2 ^ (selWiresSym 80))) :
    (coreAncSym 80).embedMatrix (elemMat86 a a) = (coreAncSym 80).basisOutcomeProjector a := by
  have hd : elemMat86 a a = Matrix.diagonal (fun x ↦ if x = a then (1 : ℂ) else 0) := by
    ext x y
    by_cases hxy : x = y
    · subst hxy
      simp [elemMat86, Matrix.diagonal]
    · simp [elemMat86, Matrix.diagonal, hxy,
        show ¬(x = a ∧ y = a) from fun h ↦ hxy (h.1.trans h.2.symm)]
  rw [hd, QRegister.embedMatrix_diagonal, QRegister.basisOutcomeProjector_eq_diagonal]
theorem embedMatrix_sum_fin8 (f : Fin 8 →
    Operator (2 ^ (selWiresSym 80))) : (coreAncSym 80).embedMatrix (∑ c : Fin 8, f c) = ∑ c : Fin 8,
    (coreAncSym
    80).embedMatrix (f c) := by
  simp only [Fin.sum_univ_eight, QRegister.embedMatrix_add]
theorem coreSysSym80_disjoint_coreAncSym80 : (coreSysSym 80).DisjointWires (coreAncSym 80) :=
  QRegister.block_disjoint_of_le 0 systemQubits systemQubits (selWiresSym 80)
    (by
      dsimp [coreWiresSym, selWiresSym, systemQubits, numElectrons, electronBits, projectileBits];
      omega)
    le_rfl
    (by
      dsimp [coreWiresSym, selWiresSym, systemQubits, numElectrons, electronBits, projectileBits];
      omega)
theorem ancTransition_sandwich_sysEmbed (c : Fin 8) (B : Operator (2 ^ systemQubits)) :
    let o := coinSelOutcome (selCoin3Sym 80) c
    let T := (coreAncSym 80).embedMatrix (elemMat86 o 0)
    let P0 := (coreAncSym 80).basisOutcomeProjector 0
    Tᴴ * ((coreSysSym 80).embedMatrix B) * T = P0 * (coreSysSym 80).embedMatrix B * P0 := by
  intro o T P0
  have hComm : (coreSysSym 80).embedMatrix B * T = T * (coreSysSym 80).embedMatrix B :=
    (coreSysSym 80).embedMatrix_comm_of_disjoint (coreAncSym 80)
      coreSysSym80_disjoint_coreAncSym80 B (elemMat86 o 0)
  have hComm0 : (coreSysSym 80).embedMatrix B * P0 = P0 * (coreSysSym 80).embedMatrix B := by
    dsimp only [P0]
    rw [← embed_elemMat86_diag 0]
    exact (coreSysSym 80).embedMatrix_comm_of_disjoint (coreAncSym 80)
      coreSysSym80_disjoint_coreAncSym80 B (elemMat86 0 0)
  have hTT : Tᴴ * T = P0 := by
    dsimp only [T, P0]
    rw [← QRegister.embedMatrix_conjTranspose, ← QRegister.embedMatrix_mul, elemMat86_conjTranspose,
      elemMat86_mul]
    simp [embed_elemMat86_diag]
  have hP0_idem : P0 * P0 = P0 := by
    dsimp only [P0]
    rw [← embed_elemMat86_diag 0, ← QRegister.embedMatrix_mul, elemMat86_mul]
    simp
  calc Tᴴ * (coreSysSym 80).embedMatrix B * T
      = (Tᴴ * T) * (coreSysSym 80).embedMatrix B := by
          rw [Matrix.mul_assoc, hComm, ← Matrix.mul_assoc]
    _ = (P0 * P0) * (coreSysSym 80).embedMatrix B := by rw [hTT, hP0_idem]
    _ = P0 * (coreSysSym 80).embedMatrix B * P0 := by
          conv_lhs => rw [Matrix.mul_assoc, ← hComm0, ← Matrix.mul_assoc]
theorem ancTransition_left_proj (c : Fin 8) :
    let o := coinSelOutcome (selCoin3Sym 80) c
    (coreAncSym 80).basisOutcomeProjector o * (coreAncSym 80).embedMatrix (elemMat86 o 0) =
      (coreAncSym 80).embedMatrix (elemMat86 o 0) := by
  intro o
  rw [← embed_elemMat86_diag o, ← QRegister.embedMatrix_mul, elemMat86_mul]
  simp
theorem ancTransition_right_proj_adj (c : Fin 8) :
    let o := coinSelOutcome (selCoin3Sym 80) c
    ((coreAncSym 80).embedMatrix (elemMat86 o 0))ᴴ *
        (coreAncSym 80).basisOutcomeProjector o =
      ((coreAncSym 80).embedMatrix (elemMat86 o 0))ᴴ := by
  intro o
  rw [← embed_elemMat86_diag o, ← QRegister.embedMatrix_conjTranspose, ← QRegister.embedMatrix_mul,
    elemMat86_conjTranspose, elemMat86_mul]
  simp
theorem momCoinProj_80_idem (c : Fin 8) : momCoinProj 80 c * momCoinProj 80 c = momCoinProj 80 c :=
  by
  rw [momCoinProj_eq_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1; funext x
  split_ifs <;> ring
theorem momCoinProj_80_sa (c : Fin 8) : (momCoinProj 80 c)ᴴ = momCoinProj 80 c := by
  unfold momCoinProj
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, slotBitProj_self_adj,
    slotBitProj_self_adj, slotBitProj_self_adj, slotBitProj_comm_any (iSlot1Mom
      80) (iSlot0Mom 80), ← Matrix.mul_assoc, slotBitProj_comm_any (iSlot2Mom 80) (iSlot0Mom 80),
        Matrix.mul_assoc, slotBitProj_comm_any (iSlot2Mom 80)
      (iSlot1Mom 80), ← Matrix.mul_assoc]
theorem post_mul_ancProj_mem_coin (post : PosPostPrepCert 80) (hSuppPost01 : ∀ c : Fin 8,
    c.val < 2 → momCoinProj 80 c * ((post.uPosPost *
    coreHadamardUnitary 80).1 *
      (coreAncSym 80).basisOutcomeProjector (coinSelOutcome (selCoin3Sym 80) c)) = (post.uPosPost *
      coreHadamardUnitary 80).1 *
    (coreAncSym 80).basisOutcomeProjector (coinSelOutcome (selCoin3Sym 80) c)) (c : Fin 8) :
      momCoinProj 80 c * ((post.uPosPost * coreHadamardUnitary 80).1
    * (coreAncSym 80).basisOutcomeProjector (coinSelOutcome (selCoin3Sym 80) c)) = (post.uPosPost *
      coreHadamardUnitary 80).1 * (coreAncSym
    80).basisOutcomeProjector (coinSelOutcome (selCoin3Sym 80) c) := by
  by_cases hc : c.val < 2
  · exact hSuppPost01 c hc
  · have hc2 : 2 ≤ c.val := Nat.le_of_not_lt hc
    let P_anc := (coreAncSym 80).basisOutcomeProjector (coinSelOutcome (selCoin3Sym 80) c)
    have hP_in : momCoinProj 80 c * P_anc = P_anc := by
      dsimp only [P_anc]
      rw [coreAncSym_eq_momAncReg_sym 80, selCoin3Sym_eq_momCoin3Sel_sym 80]
      exact momCoinProj_mul_ancOutcomeProj 80 c
    have hHad_comm : (coreHadamardUnitary 80).1 * momCoinProj 80 c =
        momCoinProj 80 c * (coreHadamardUnitary 80).1 := by
      rw [coreHadamardUnitary_eq_mom_sym 80]
      exact coreHadamardMom_comm_momCoinProj 80 c
    have hEq : (post.uPosPost * coreHadamardUnitary 80).1 * P_anc =
        momCoinProj 80 c * ((coreHadamardUnitary 80).1 * P_anc) := by
      calc (post.uPosPost * coreHadamardUnitary 80).1 * P_anc
          = post.uPosPost.1 * ((coreHadamardUnitary 80).1 * (momCoinProj 80 c * P_anc)) := by
              rw [hP_in, Submonoid.coe_mul, Matrix.mul_assoc]
        _ = post.uPosPost.1 * (((coreHadamardUnitary 80).1 * momCoinProj 80 c) * P_anc) := by
              simp only [Matrix.mul_assoc]
        _ = (post.uPosPost.1 * momCoinProj 80 c) * ((coreHadamardUnitary 80).1 * P_anc) := by
              rw [hHad_comm]; simp only [Matrix.mul_assoc]
        _ = momCoinProj 80 c * ((coreHadamardUnitary 80).1 * P_anc) := by
              rw [post.hPosPost_nonPos c hc2]
    change momCoinProj 80 c * ((post.uPosPost * coreHadamardUnitary 80).1 * P_anc) =
      (post.uPosPost * coreHadamardUnitary 80).1 * P_anc
    rw [hEq, ← Matrix.mul_assoc, momCoinProj_80_idem]
theorem preserves_proj_of_sa_and_offProj {D : ℕ} {P : Operator D} {U : Unitary D} (hP_sa : Pᴴ =
    P) (hP_idem : P * P = P) (hU_sa : U.1ᴴ = U.1) (hOff : U.1 *
    (1 - P) = 1 - P) : P * (U.1 * P) = U.1 * P := by
  have hLeft := offProj_left_of_sa_and_right hP_sa hU_sa hOff
  have hZero : (1 - P) * (U.1 * P) = 0 := by
    rw [← Matrix.mul_assoc, hLeft, Matrix.sub_mul, Matrix.one_mul, hP_idem, sub_self]
  rw [Matrix.sub_mul, Matrix.one_mul] at hZero
  exact (sub_eq_zero.mp hZero).symm
theorem posCoin01ProjMom_mul_momCoinProj_01 (c : Fin 8) (h1 : coinBitFin2 c 1 =
    0) (h2 : coinBitFin2 c 2 = 0) : posCoin01ProjMom 80 * momCoinProj 80 c =
    momCoinProj 80 c := by
  unfold posCoin01ProjMom momCoinProj
  rw [h1, h2]
  let A := slotBitProj (iSlot0Mom 80) (coinBitFin2 c 0)
  let B := slotBitProj (iSlot1Mom 80) 0
  let C := slotBitProj (iSlot2Mom 80) 0
  have hBA : B * A = A * B := slotBitProj_comm_any _ _ _ _
  have hCA : C * A = A * C := slotBitProj_comm_any _ _ _ _
  have hCB : C * B = B * C := slotBitProj_comm_any _ _ _ _
  have hBB : B * B = B := slotBitProj_mul_idem _ _
  have hCC : C * C = C := slotBitProj_mul_idem _ _
  change (C * B) * ((A * B) * C) = (A * B) * C
  calc (C * B) * ((A * B) * C)
      = (C * A) * ((B * B) * C) := by
          simp only [Matrix.mul_assoc]
          rw [← Matrix.mul_assoc B A, hBA, Matrix.mul_assoc]
    _ = (A * B) * C := by
          rw [hCA, hBB]
          simp only [Matrix.mul_assoc]
          rw [← Matrix.mul_assoc C B C, hCB, Matrix.mul_assoc, hCC]
theorem unitaryConj_comm_proj {D : ℕ} (U M : Unitary D) (P : Operator D) (hP_sa : Pᴴ = P)
    (hU : U.1 * P = P * U.1) (hM : M.1 * P = P * M.1) :
    (unitaryConj U M).1 * P = P * (unitaryConj U M).1 := by
  have hU_adj : U.1ᴴ * P = P * U.1ᴴ := by
    simpa only [Matrix.conjTranspose_mul, hP_sa] using (congrArg Matrix.conjTranspose hU).symm
  rw [unitaryConj_val]
  calc (U.1ᴴ * M.1 * U.1) * P
      = U.1ᴴ * (M.1 * P) * U.1 := by simp only [Matrix.mul_assoc, hU]
    _ = P * (U.1ᴴ * M.1 * U.1) := by
          rw [hM, ← Matrix.mul_assoc U.1ᴴ P, hU_adj]
          simp only [Matrix.mul_assoc]
theorem momSingleSlotOracle_bUnitTwos_isHermitian {k : Fin 6}
    (s : MomSingleSlotOracle 80 48 k) (cfg : Configuration) :
    (s.bUnitTwos cfg).IsHermitian := by
  let c := fullSysCoinIdx k
  let Pc := (coreAncSym 80).basisOutcomeProjector (coinSelOutcome (selCoin3Sym 80) c)
  let T := (coreAncSym 80).embedMatrix (elemMat86 (coinSelOutcome (selCoin3Sym 80) c) 0)
  let P0 := (coreAncSym 80).basisOutcomeProjector 0
  have hTop : Pc * (unitaryConj (coreHadamardUnitary 80) (s.uSlotEff cfg)).1 * Pc =
      Pc * (coreSysSym 80).embedMatrix (s.bUnitTwos cfg) * Pc := by
    dsimp only [Pc]
    rw [coreAncSym_eq_momAncReg_sym 80, selCoin3Sym_eq_momCoin3Sel_sym 80,
      coreSysSym_eq_momSysReg_sym 80, coreHadamardUnitary_eq_mom_sym 80]
    exact s.hTopBlock cfg
  have hTL : Tᴴ * Pc = Tᴴ := ancTransition_right_proj_adj c
  have hTR : Pc * T = T := ancTransition_left_proj c
  have hSand : Tᴴ * (unitaryConj (coreHadamardUnitary 80) (s.uSlotEff cfg)).1 * T =
      P0 * (coreSysSym 80).embedMatrix (s.bUnitTwos cfg) * P0 := by
    calc Tᴴ * (unitaryConj (coreHadamardUnitary 80) (s.uSlotEff cfg)).1 * T
        = Tᴴ * (Pc * (unitaryConj (coreHadamardUnitary 80) (s.uSlotEff cfg)).1 * Pc) * T := by
            simp only [← Matrix.mul_assoc]
            rw [hTL, Matrix.mul_assoc (Tᴴ * _) Pc T, hTR]
      _ = (Tᴴ * Pc) * (coreSysSym 80).embedMatrix (s.bUnitTwos cfg) * (Pc * T) := by
            rw [hTop]
            simp only [Matrix.mul_assoc]
      _ = P0 * (coreSysSym 80).embedMatrix (s.bUnitTwos cfg) * P0 := by
            rw [hTL, hTR]
            exact ancTransition_sandwich_sysEmbed c (s.bUnitTwos cfg)
  have hM_sa : (unitaryConj (coreHadamardUnitary 80) (s.uSlotEff cfg)).1ᴴ =
      (unitaryConj (coreHadamardUnitary 80) (s.uSlotEff cfg)).1 :=
    PosMomSelectDynamic.unitaryConj_conjTranspose (s.hSA cfg)
  have hP0_sa : P0ᴴ = P0 := by
    dsimp only [P0]
    rw [← embed_elemMat86_diag 0, ← QRegister.embedMatrix_conjTranspose, elemMat86_conjTranspose]
  have hAdj := congrArg Matrix.conjTranspose hSand
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hM_sa, hP0_sa,
    ← QRegister.embedMatrix_conjTranspose, Matrix.mul_assoc] at hAdj
  simp only [Matrix.mul_assoc] at hSand
  have hEq0 : P0 * ((coreSysSym 80).embedMatrix (s.bUnitTwos cfg)ᴴ * P0) = P0 *
      ((coreSysSym 80).embedMatrix (s.bUnitTwos cfg) * P0) := hAdj.symm.trans hSand
  exact FullScaleBESector.embedMatrix_sandwich_zero_inj (m := 86)
    (s.bUnitTwos cfg)ᴴ (s.bUnitTwos cfg)
    (by simpa only [P0, coreSysSym, coreAncSym, Matrix.mul_assoc] using hEq0)
theorem target_slot_agrees_unquantized_sym (w_k : ℝ) (spinUp : Finset (Fin numElectrons))
    (B_unit_twos H_target : Operator (2 ^ systemQubits)) {ε_intr : ℝ}
    (hPermSm : ∀ (g : Equiv.Perm (Fin numElectrons)) (x y : Fin (2 ^ systemQubits)),
      IsGridState x → IsGridState y → (smToTwosSysUnitary.1 * B_unit_twos *
    smToTwosSysUnitary.1) (permElectron g x) (permElectron g y) = (smToTwosSysUnitary.1 *
      B_unit_twos * smToTwosSysUnitary.1) x y) (hIntr :
    ‖fermionicProjector spinUp * ((w_k : ℂ) • (smToTwosSysUnitary.1 * B_unit_twos *
      smToTwosSysUnitary.1) - H_target) * fermionicProjector spinUp‖ ≤
    ε_intr) : AgreesOnFermionicSector spinUp (SpecsAux.gridProjector * (smToTwosSysUnitary.1 *
      ((w_k : ℂ) • B_unit_twos) *
    smToTwosSysUnitary.1) * SpecsAux.gridProjector) H_target ε_intr := by
  let G := SpecsAux.gridProjector
  let P_F := fermionicProjector spinUp
  let B_sm := smToTwosSysUnitary.1 * B_unit_twos * smToTwosSysUnitary.1
  have hSmul : smToTwosSysUnitary.1 * ((w_k : ℂ) • B_unit_twos) * smToTwosSysUnitary.1 =
      (w_k : ℂ) • B_sm := by
    rw [Matrix.mul_smul, Matrix.smul_mul]
  have hPermScaled : ∀ (g : Equiv.Perm (Fin numElectrons)) (x y : Fin (2 ^ systemQubits)),
      IsGridState x → IsGridState y → ((w_k : ℂ) • B_sm) (permElectron g x) (permElectron g y)
      = ((w_k : ℂ) • B_sm) x y := by
    intro g x y hx hy
    simp only [Matrix.smul_apply, smul_eq_mul]
    exact congrArg _ (hPermSm g x y hx hy)
  refine ⟨by rw [hSmul]; exact commute_fermionicProjector_of_inGridPerm _ hPermScaled spinUp, ?_⟩
  have hGP : G * P_F = P_F := SpecsAux.gridProjector_mul_fermionicProjector spinUp
  have hPG : P_F * G = P_F := SpecsAux.fermionicProjector_mul_gridProjector spinUp
  change ‖P_F * (G * (smToTwosSysUnitary.1 * ((w_k : ℂ) • B_unit_twos) * smToTwosSysUnitary.1) * G -
    H_target) * P_F‖ ≤ ε_intr
  rw [hSmul, op_sandwiched_proj_sub_eq P_F G ((w_k : ℂ) • B_sm) H_target hPG hGP]
  exact hIntr
theorem norm_triple_mul_le_local {D : ℕ} [NeZero D] (A B C : Operator D) {cA cB cC : ℝ} (hA : ‖A‖ ≤
    cA) (hB : ‖B‖ ≤ cB) (hC : ‖C‖ ≤ cC) (hcA : 0 ≤ cA) (hcB
    : 0 ≤ cB) : ‖A * B * C‖ ≤ (cA * cB) * cC := by
  calc ‖A * B * C‖
      ≤ ‖A * B‖ * ‖C‖ := norm_mul_le _ _
    _ ≤ (‖A‖ * ‖B‖) * ‖C‖ := mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
    _ ≤ (cA * cB) * cC :=
        mul_le_mul (mul_le_mul hA hB (norm_nonneg _) hcA) hC (norm_nonneg _) (mul_nonneg hcA hcB)
end ConfigZeroSubwireGridPert80
end ZeroSubwireGridPert80
end
end ModZeroSubwireGridPert80

section ModInterWalkRSum42HoistCircuits
@[expose] public section
namespace InterWalkRSum42Hoist
section ConfigInterWalkRSum42Hoist
set_option backward.isDefEq.respectTransparency true
set_option exponentiation.threshold 8192
set_option maxRecDepth 4096
local instance (priority := 1000000) instNeZeroTwoPowRSum42Hoist (k : ℕ) : NeZero (2 ^ k) :=
  ⟨Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos k)⟩
open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt Real
open scoped Matrix BigOperators Matrix.Norms.L2Operator
open DyadicQft64 hiding dyadicTurn phaseGradKet
open DyadicQft64.PhasePerm SpecsAux.SpecMirror
open FullSysCatSegmentBridge (fullSysCoreWires fullSysBEWires beCoreBlock
  disjointWires_compose_of_disjoint)
open NuclearTwistAndXor654Concrete (dXor32All654)
open NuclearTwistRealizes (uXor32Core slot2AxisSum)
open HybridStream288Aux (threePlaneChunkWire selCoreSlice uBitXor weightedBatchVal
  weightedBatchVal_le accInvar_zero accInvar_step1_bitXor9 accInvar_step_sliceModAdd
  hybridSixBatch_eq_slot2AxisSum)
open SingleCatSpine (rTopCatSlice)
open SingleCatClosure (mActSingleCatClosure kActSingleCatClosure rBEInSingleCat rBECatSingleCatInAct
  rBESelLoc rCatSelLoc rBESelLoc_disj_rCatSelLoc)
abbrev RealizesClean := @DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace
theorem embedUnitary_inv_symm {k n : ℕ} (r : QRegister k n) (U : Unitary (2 ^ k)) : (r.embedUnitary
    U)⁻¹ = r.embedUnitary U⁻¹ := by
  apply mul_eq_one_iff_inv_eq.mp
  rw [← r.embedUnitary_mul, mul_inv_cancel, r.embedUnitary_one]
attribute [local irreducible] dXor32All654
theorem qreg_ext {k n : ℕ} {r s : QRegister k n} (h : ∀ i, r i = s i) : r = s :=
  QRegister.ext (Function.Embedding.ext h)
theorem qreg_block_apply {n : ℕ} (offset width : ℕ) (h : offset + width ≤ n) (i : Fin width) :
    QRegister.block offset width h i = ⟨offset + i.val, by omega⟩ := rfl
abbrev mActOrig : ℕ := mActSingleCatClosure 80 48 40
abbrev kActOrig : ℕ := kActSingleCatClosure 80 48 40
abbrev mActHoist : ℕ := mActOrig + 42
abbrev kFull80 : ℕ := SpecsAux.SpecMirror.systemQubits + mActHoist
def rAct0 : QRegister kActOrig kFull80 := QRegister.block 0 kActOrig (by decide)
def rSum0 : QRegister 42 kFull80 := QRegister.block kActOrig 42 (by decide)
def rSum14In42 (w : Fin 3) : QRegister 14 42 := QRegister.block (14 * w.val) 14 (by omega)
def rSum14Full (w : Fin 3) : QRegister 14 kFull80 := rSum0.compose (rSum14In42 w)
abbrev rBEOrig : QRegister (fullSysBEWires 80) kActOrig := rBEInSingleCat 80 48 40
abbrev rCoreOrig : QRegister (fullSysCoreWires 80) kActOrig :=
  rBEOrig.compose (beCoreBlock 80)
abbrev rCoreFull : QRegister (fullSysCoreWires 80) kFull80 := rAct0.compose rCoreOrig
abbrev rSegOrig : QRegister (fullSysBEWires 80 + 48) kActOrig :=
  rBECatSingleCatInAct 80 48 40
abbrev rSegFull : QRegister (fullSysBEWires 80 + 48) kFull80 := rAct0.compose rSegOrig
abbrev rPG48Loc : QRegister 48 (fullSysBEWires 80 + 48) :=
  (rCatSelLoc 80 48).compose (rTopCatSlice 48 48 le_rfl)
abbrev rPG48Orig : QRegister 48 kActOrig := rSegOrig.compose rPG48Loc
abbrev rPG48Full : QRegister 48 kFull80 := rSegFull.compose rPG48Loc
theorem rSegOrig_compose_rBESelLoc : rSegOrig.compose (rBESelLoc 80 48) = rBEOrig := by
  apply qreg_ext; intro i
  have hEq : rBESelLoc 80 48 i = Fin.castAdd 48 i := by
    ext; simp [rBESelLoc]
  change rSegOrig (rBESelLoc 80 48 i) = rBEOrig i
  rw [hEq, rSegOrig, rBECatSingleCatInAct, QRegister.concat_apply_left]
theorem rSegOrig_compose_rCoreLoc : rSegOrig.compose ((rBESelLoc 80 48).compose (beCoreBlock 80)) =
    rCoreOrig := by
  apply qreg_ext; intro i
  exact congrArg (fun r ↦ r (beCoreBlock 80 i)) rSegOrig_compose_rBESelLoc
theorem rSegFull_compose_rCoreLoc : rSegFull.compose ((rBESelLoc 80 48).compose (beCoreBlock 80)) =
    rCoreFull := by
  apply qreg_ext; intro i
  exact congrArg rAct0 (congrArg (fun r ↦ r i) rSegOrig_compose_rCoreLoc)
theorem hCoreOrig_disj_PG48Orig : rCoreOrig.DisjointWires rPG48Orig := by
  rw [← rSegOrig_compose_rCoreLoc]
  exact disjointWires_compose_of_disjoint rSegOrig (((rBESelLoc_disj_rCatSelLoc 80
    48).compose_left (beCoreBlock 80)).compose_right (rTopCatSlice 48 48 le_rfl))
theorem hCoreFull_disj_PG48Full : rCoreFull.DisjointWires rPG48Full :=
  disjointWires_compose_of_disjoint rAct0 hCoreOrig_disj_PG48Orig
noncomputable abbrev rCTOrig : QRegister (fullSysCoreWires 80 + 48) kActOrig :=
  rCoreOrig.concat rPG48Orig hCoreOrig_disj_PG48Orig
noncomputable abbrev rCTFull : QRegister (fullSysCoreWires 80 + 48) kFull80 :=
  rCoreFull.concat rPG48Full hCoreFull_disj_PG48Full
theorem hAct0_disj_Sum0 : rAct0.DisjointWires rSum0 := by
  rw [QRegister.disjoint_iff]
  intro i j hij
  rw [rAct0, rSum0, qreg_block_apply, qreg_block_apply] at hij
  have hv := congrArg Fin.val hij
  dsimp only at hv
  omega
theorem hAct0_disj_Sum14 (w : Fin 3) : rAct0.DisjointWires (rSum14Full w) :=
  hAct0_disj_Sum0.compose_right (rSum14In42 w)
theorem hCoreFull_disj_Sum14 (w : Fin 3) : rCoreFull.DisjointWires (rSum14Full w) :=
  (hAct0_disj_Sum14 w).compose_left rCoreOrig
theorem hSum14In42_disj {w w' : Fin 3} (h : w ≠ w') : (rSum14In42 w).DisjointWires (rSum14In42 w')
    := by
  rw [QRegister.disjoint_iff]
  intro i j hij
  rw [rSum14In42, rSum14In42, qreg_block_apply, qreg_block_apply] at hij
  have hv := congrArg Fin.val hij
  dsimp only at hv
  have hw : w.val ≠ w'.val := fun heq ↦ h (Fin.ext heq)
  omega
noncomputable def pSum42Zero : Operator (2 ^ kFull80) := rSum0.basisOutcomeProjector 0
noncomputable def uHybridStream220 {mPayload : ℕ} (w : Fin 3) :
    Unitary (2 ^ (fullSysCoreWires mPayload + 14)) :=
  let kC := fullSysCoreWires mPayload
  let w1 := threePlaneChunkWire (mPayload := mPayload) w 0 0 73 (by decide) (by decide)
  let w2 := threePlaneChunkWire (mPayload := mPayload) w 0 73 72 (by decide) (by decide)
  let w3 := threePlaneChunkWire (mPayload := mPayload) w 0 145 73 (by decide) (by decide)
  let w4 := threePlaneChunkWire (mPayload := mPayload) w 3 0 72 (by decide) (by decide)
  let w5 := threePlaneChunkWire (mPayload := mPayload) w 3 72 73 (by decide) (by decide)
  let w6 := threePlaneChunkWire (mPayload := mPayload) w 3 145 73 (by decide) (by decide)
  (selCoreSlice kC 3 11 (by decide)).embedUnitary (catModAddUnitary kC 11 (weightedBatchVal w6)) *
    ((selCoreSlice kC 3 11 (by
      decide)).embedUnitary (catModAddUnitary kC 11 (weightedBatchVal w5)) *
      ((selCoreSlice kC 3 10 (by
        decide)).embedUnitary (catModAddUnitary kC 10 (weightedBatchVal w4)) *
        ((selCoreSlice kC 0 11 (by
          decide)).embedUnitary (catModAddUnitary kC 11 (weightedBatchVal w3)) *
          ((selCoreSlice kC 0 10 (by
            decide)).embedUnitary (catModAddUnitary kC 10 (weightedBatchVal w2)) *
            (selCoreSlice kC 0 9 (by decide)).embedUnitary (uBitXor kC 9 (weightedBatchVal w1))))))
theorem uHybridStream220_compute_ket {mPayload n : ℕ} [NeZero (2 ^ n)] (w : Fin 3)
    (rCore : QRegister (fullSysCoreWires mPayload) n) (rSum14 : QRegister 14 n)
    (hCSum : rCore.DisjointWires rSum14) : ∀ β₀ : Fin n → ZMod 2,
    (∀ i : Fin 14, β₀ (rSum14 i) = 0) → ∃ β : Fin n → ZMod 2, ((rCore.concat rSum14
    hCSum).embedUnitary (uHybridStream220 w)).1.mulVec (basisKet β₀) = basisKet β ∧
    (∀ g : Fin n, g ∉ rSum14.image → β g = β₀ g) ∧ (∀ i : Fin 14, β (rSum14 i) = if
    (slot2AxisSum w (fun q ↦ β₀ (rCore q))).testBit i.val then 1 else 0) := by
  intro β₀ hz
  let w1 := threePlaneChunkWire (mPayload := mPayload) w 0 0 73 (by decide) (by decide)
  let w2 := threePlaneChunkWire (mPayload := mPayload) w 0 73 72 (by decide) (by decide)
  let w3 := threePlaneChunkWire (mPayload := mPayload) w 0 145 73 (by decide) (by decide)
  let w4 := threePlaneChunkWire (mPayload := mPayload) w 3 0 72 (by decide) (by decide)
  let w5 := threePlaneChunkWire (mPayload := mPayload) w 3 72 73 (by decide) (by decide)
  let w6 := threePlaneChunkWire (mPayload := mPayload) w 3 145 73 (by decide) (by decide)
  have hb1 : weightedBatchVal w1 (fun q ↦ β₀ (rCore q)) ≤ 511 := weightedBatchVal_le w1 _
  have hb2 : weightedBatchVal w2 (fun q ↦ β₀ (rCore q)) ≤ 504 := weightedBatchVal_le w2 _
  have hb3 : weightedBatchVal w3 (fun q ↦ β₀ (rCore q)) ≤ 511 := weightedBatchVal_le w3 _
  have hb4 : weightedBatchVal w4 (fun q ↦ β₀ (rCore q)) ≤ 504 := weightedBatchVal_le w4 _
  have hb5 : weightedBatchVal w5 (fun q ↦ β₀ (rCore q)) ≤ 511 := weightedBatchVal_le w5 _
  have hb6 : weightedBatchVal w6 (fun q ↦ β₀ (rCore q)) ≤ 511 := weightedBatchVal_le w6 _
  obtain ⟨β₁, hket₁, hInv₁⟩ := accInvar_step1_bitXor9 rCore rSum14 hCSum (weightedBatchVal w1)
    β₀ (accInvar_zero rSum14 β₀ hz) (by omega)
  obtain ⟨β₂, hket₂, hInv₂⟩ := accInvar_step_sliceModAdd rCore rSum14 hCSum 0 10 (by decide)
    (weightedBatchVal w2) _ β₀ β₁ hInv₁ (by omega) (by omega)
  obtain ⟨β₃, hket₃, hInv₃⟩ := accInvar_step_sliceModAdd rCore rSum14 hCSum 0 11 (by decide)
    (weightedBatchVal w3) _ β₀ β₂ hInv₂ (by omega) (by omega)
  obtain ⟨β₄, hket₄, hInv₄⟩ := accInvar_step_sliceModAdd rCore rSum14 hCSum 3 10 (by decide)
    (weightedBatchVal w4) _ β₀ β₃ hInv₃ (by omega) (by omega)
  obtain ⟨β₅, hket₅, hInv₅⟩ := accInvar_step_sliceModAdd rCore rSum14 hCSum 3 11 (by decide)
    (weightedBatchVal w5) _ β₀ β₄ hInv₄ (by omega) (by omega)
  obtain ⟨β₆, hket₆, hInv₆⟩ := accInvar_step_sliceModAdd rCore rSum14 hCSum 3 11 (by decide)
    (weightedBatchVal w6) _ β₀ β₅ hInv₅ (by omega) (by omega)
  rw [hybridSixBatch_eq_slot2AxisSum w (fun q ↦ β₀ (rCore q))] at hInv₆
  refine ⟨β₆, ?_, hInv₆.1, hInv₆.2⟩
  simp only [uHybridStream220, QRegister.embedUnitary_mul, Submonoid.coe_mul,
    ← Matrix.mulVec_mulVec]
  rw [hket₁, hket₂, hket₃, hket₄, hket₅, hket₆]
noncomputable def rCSFull (w : Fin 3) : QRegister (fullSysCoreWires 80 + 14) kFull80 :=
  rCoreFull.concat (rSum14Full w) (hCoreFull_disj_Sum14 w)
noncomputable def uXor32Full : Unitary (2 ^ kFull80) := rCoreFull.embedUnitary (uXor32Core 80)
noncomputable def uStreamFull (w : Fin 3) : Unitary (2 ^ kFull80) :=
  (rCSFull w).embedUnitary (uHybridStream220 w)
noncomputable def uStream42Init : Unitary (2 ^ kFull80) :=
  uXor32Full * (uStreamFull 2 * (uStreamFull 1 * (uStreamFull 0 * uXor32Full)))
def rCSInCSP : QRegister (fullSysCoreWires 80 + 14) ((fullSysCoreWires 80 + 14) + 48) :=
  QRegister.block 0 (fullSysCoreWires 80 + 14) (by decide)
theorem qreg_concat_eq_of_eq {k₁ k₂ n : ℕ} {r₁ r₁' : QRegister k₁ n} {r₂ r₂' : QRegister k₂ n} {h :
    r₁.DisjointWires r₂} {h' : r₁'.DisjointWires r₂'} (e₁ :
    r₁ = r₁') (e₂ : r₂ = r₂') : r₁.concat r₂ h = r₁'.concat r₂' h' := by
  subst e₁; subst e₂; rfl
theorem concat_compose_block_left {k₁ k₂ n : ℕ} (r₁ : QRegister k₁ n) (r₂ : QRegister k₂ n) (h :
    r₁.DisjointWires r₂) (hle : 0 + k₁ ≤ k₁ + k₂) : (r₁.concat
    r₂ h).compose (QRegister.block 0 k₁ hle) = r₁ := by
  apply qreg_ext; intro i
  have hidx : QRegister.block 0 k₁ hle i = Fin.castAdd k₂ i :=
    Fin.ext (by simp)
  change (r₁.concat r₂ h) (QRegister.block 0 k₁ hle i) = r₁ i
  rw [hidx, QRegister.concat_apply_left]
theorem realizesClean_of_reg_eq {Var : Type} [Fintype Var] [DecidableEq Var] {k m n : ℕ} [NeZero (2
    ^ n)] {r r' : QRegister k n} {rWork : QRegister m n} {U
    : Unitary (2 ^ k)} {d : DynamicCircuit Var n} (heq : r =
      r') (h : RealizesClean r rWork U d) : RealizesClean r' rWork U d := by
  subst heq; exact h
theorem widenActive_of_eq {Var : Type} [Fintype Var] [DecidableEq Var] {k kAct m n : ℕ}
    [NeZero (2 ^ n)] {r : QRegister k n} {rAct : QRegister kAct n} {sub : QRegister k kAct}
    {rWork : QRegister m n} {U : Unitary (2 ^ k)} {d : DynamicCircuit Var n}
    (heq : r = rAct.compose sub) (h : RealizesClean r rWork U d) : RealizesClean rAct rWork
    (sub.embedUnitary U) d := (realizesClean_of_reg_eq heq h).widenActive
theorem hPSumFull (w : Fin 3) : rPG48Full.DisjointWires (rSum14Full w) :=
  (hAct0_disj_Sum14 w).compose_left rPG48Orig
theorem hCSFull_disj_PG48 (w : Fin 3) : (rCSFull w).DisjointWires rPG48Full :=
  QRegExt.disjointWires_concat_left hCoreFull_disj_PG48Full
    (QRegister.disjoint_comm.mp (hPSumFull w))
noncomputable def rCSPFull (w : Fin 3) : QRegister ((fullSysCoreWires 80 + 14) + 48) kFull80
    := (rCSFull w).concat rPG48Full (hCSFull_disj_PG48 w)
end ConfigInterWalkRSum42Hoist
end InterWalkRSum42Hoist
end
end ModInterWalkRSum42HoistCircuits

end QuantumComputation.Specs.StoppingPowerSolution
