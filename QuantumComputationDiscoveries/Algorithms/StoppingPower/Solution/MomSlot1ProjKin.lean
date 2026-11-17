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

public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.HoistedSwapSelect
set_option Elab.async false

@[expose] public section
set_option allowUnsafeReducibility true

namespace QuantumComputation.Specs.StoppingPowerSolution

section ModMomSlots01Slot1ProjKinetic
@[expose] public section
namespace MomSlots01Slot1ProjKineticAlt
theorem qreg_block_apply {n : ℕ} (offset width : ℕ) (h : offset + width ≤ n) (i : Fin width) :
    QRegister.block offset width h i = ⟨offset + i.val, by omega⟩ := rfl
theorem qreg_block_wires_apply {n : ℕ} (offset width : ℕ) (h : offset + width ≤ n) (i : Fin width) :
    (QRegister.block offset width h).wires i = ⟨offset + i.val, by omega⟩ := rfl
theorem qreg_whole_wires {n : ℕ} (i : Fin n) : (QRegister.whole n).wires i = i := rfl
theorem emb_refl_apply {α : Type*} (x : α) : (Function.Embedding.refl α) x = x := rfl
theorem emb_mk_apply {α β : Type*} (f : α → β) (h : Function.Injective f) (x : α) :
    ({ toFun := f, inj' := h } : α ↪ β) x = f x := rfl
theorem emb_trans_apply {α β γ : Type*} (f : α ↪ β) (g : β ↪ γ) (x : α) :
    (f.trans g) x = g (f x) := rfl
end MomSlots01Slot1ProjKineticAlt
namespace MomSlots01Slot1ProjKinetic
open Operator Matrix QProg Circuit _root_.DynamicCircuit DynCircuitExt Real SpecsAux
open SpecsAux.SpecMirror
open SpecsAux.PhaseGradCatalystCore
open SpecsAux.BridgeFermionicComm
open SpecsAux.BridgeFermionicComm.SpecInner
open PosMomSelectSandwich
open PosMomSelectDynamic
open FullSysPrepare6Slot
open TwosCompAndWire0Cancel
open LiteralKineticAndMidpoint128
open scoped Matrix BigOperators Matrix.Norms.L2Operator
theorem ite_pos_s1 {c : Prop} [Decidable c] (hc : c) {α : Sort*} {t e : α} :
    (if c then t else e) = t := by simp [hc]
theorem ite_neg_s1 {c : Prop} [Decidable c] (hnc : ¬c) {α : Sort*} {t e : α} :
    (if c then t else e) = e := by simp [hnc]
theorem dite_pos_s1 {c : Prop} [Decidable c] (hc : c) {α : Sort*}
    {t : c → α} {e : ¬c → α} : (if h : c then t h else e h) = t hc := by simp [hc]
theorem dite_neg_s1 {c : Prop} [Decidable c] (hnc : ¬c) {α : Sort*}
    {t : c → α} {e : ¬c → α} : (if h : c then t h else e h) = e hnc := by simp [hnc]
abbrev selWiresSym (mPayload : ℕ) : ℕ := 6 + mPayload
abbrev coreWiresSym (mPayload : ℕ) : ℕ := SpecsAux.SpecMirror.systemQubits + selWiresSym mPayload
abbrev selCoin3Sym (mPayload : ℕ) : QRegister 3 (selWiresSym mPayload) :=
  QRegister.block 0 3 (by dsimp [selWiresSym]; omega)
abbrev coreSysSym (mPayload : ℕ) : QRegister SpecsAux.SpecMirror.systemQubits (coreWiresSym
    mPayload) :=
  QRegister.block 0 SpecsAux.SpecMirror.systemQubits (by dsimp [coreWiresSym]; omega)
abbrev coreAncSym (mPayload : ℕ) : QRegister (selWiresSym mPayload) (coreWiresSym mPayload) :=
  QRegister.block SpecsAux.SpecMirror.systemQubits (selWiresSym mPayload) le_rfl
abbrev corePayloadSym (mPayload : ℕ) : QRegister mPayload (coreWiresSym mPayload) :=
  QRegister.block (SpecsAux.SpecMirror.systemQubits + 6) mPayload (Nat.add_assoc _ _ _).le
noncomputable abbrev coreHadamardUnitary (mPayload : ℕ) :
    Unitary (2 ^ (coreWiresSym mPayload)) :=
  (hadamardAll (corePayloadSym mPayload)).eval
abbrev iSlot0Mom (mPayload : ℕ) : Wire (coreWiresSym mPayload) :=
  ⟨3948, show 3948 < 3948 + (6 + mPayload) by omega⟩
abbrev iSlot1Mom (mPayload : ℕ) : Wire (coreWiresSym mPayload) :=
  ⟨3949, show 3949 < 3948 + (6 + mPayload) by omega⟩
abbrev iSlot2Mom (mPayload : ℕ) : Wire (coreWiresSym mPayload) :=
  ⟨3950, show 3950 < 3948 + (6 + mPayload) by omega⟩
def coinBitFin2 (c : Fin 8) (j : Fin 3) : Fin 2 := ⟨(basisBits 3 c j).val, ZMod.val_lt _⟩
noncomputable def momCoinProj (mPayload : ℕ) (c : Fin 8) : Operator
    (2 ^ (coreWiresSym mPayload)) := slotBitProj (iSlot0Mom mPayload) (coinBitFin2 c 0) *
    slotBitProj (iSlot1Mom mPayload) (coinBitFin2 c 1) * slotBitProj (iSlot2Mom mPayload)
    (coinBitFin2 c 2)
def slot1AxisInt (u : Fin 256) : ℤ :=
  if u.val = 128 then 0 else TwosCompAndWire0Cancel.twosComp8Int u
noncomputable def projAxisTerm (cfg : SpecsAux.SpecMirror.Configuration) (p : ℤ) (w : Fin 3) : ℝ :=
  (((p : ℝ) ^ 2 - 16129 / 2) * (gridKappa ^ 2 / 2) -
    gridKappa * (p : ℝ) * waveVector cfg.projectileMomentum w) / projectileMass
theorem sum_projAxisTerm_eq_centered (cfg : SpecsAux.SpecMirror.Configuration)
    (x : Fin (2 ^ SpecsAux.SpecMirror.systemQubits)) :
    (∑ w : Fin 3, projAxisTerm cfg (SpecsAux.SpecMirror.momentum x .projectile w) w) =
      waveNumberSq (SpecsAux.SpecMirror.momentum x .projectile - cfg.projectileMomentum) /
        (2 * projectileMass) - projMidpointOffset cfg := by
  have hm_ne : (projectileMass : ℝ) ≠ 0 := by norm_num [projectileMass]
  let p := SpecsAux.SpecMirror.momentum x .projectile
  have hwnsq : waveNumberSq p =
      ((p 0 : ℝ) ^ 2 + (p 1 : ℝ) ^ 2 + (p 2 : ℝ) ^ 2) * gridKappa ^ 2 := by
    simp only [p, waveNumberSq, waveVector, gridKappa, dotProduct, Fin.sum_univ_three]
    ring
  have hwvec (w : Fin 3) : waveVector p w = gridKappa * (p w : ℝ) := by
    dsimp [p, waveVector, gridKappa]
    ring
  unfold projAxisTerm projMidpointOffset
  rw [stepNumberSq_sub_eq, hwnsq, Fin.sum_univ_three, Fin.sum_univ_three,
    hwvec 0, hwvec 1, hwvec 2]
  field_simp [hm_ne]
  ring
theorem neg_one_pow_bit_mul_self (k : ℕ) : ((-1 : ℂ) ^ k) * ((-1 : ℂ) ^ k) = 1 := by
  rw [← pow_add, ← two_mul, pow_mul]
  norm_num
theorem embedMatrix_diagonal {k N : ℕ} (r : QRegister k N) (f : Fin (2 ^ k) → ℂ) :
    r.embedMatrix (Matrix.diagonal f) = Matrix.diagonal (fun g ↦ f (r.extractIndex g)) := by
  ext i j
  rw [QRegister.embedMatrix_apply]
  by_cases hij : i = j
  · subst hij
    simp
  · rw [Matrix.diagonal_apply_ne _ hij]
    by_cases envEq : (r.basisSplitEquiv i).2 = (r.basisSplitEquiv j).2
    · rw [Matrix.diagonal_apply_ne _ (show r.extractIndex i ≠ r.extractIndex j from fun h ↦
        hij (r.basisSplitEquiv.injective (Prod.ext h envEq))), zero_mul]
    · simp [envEq]
abbrev coreSixSym (mPayload : ℕ) : QRegister 6 (coreWiresSym mPayload) :=
  QRegister.block SpecsAux.SpecMirror.systemQubits 6 (by dsimp [coreWiresSym, selWiresSym]; omega)
noncomputable def coinSixOutcome (c : Fin 8) : Fin (2 ^ 6) :=
  (basisBitsEquiv 6).symm (fun i ↦ if h : i.val < 3 then basisBits 3 c ⟨i.val, h⟩ else 0)
theorem basisBits_symm_apply_local_slot1 {m : ℕ} (f : Fin m → ZMod 2) (i : Fin m) :
    basisBits m ((basisBitsEquiv m).symm f) i = f i :=
  congrFun ((basisBitsEquiv m).apply_symm_apply f) i
theorem ancProjector_eq_six_mul_payload (mPayload : ℕ) (c : Fin 8) :
    (coreAncSym mPayload).basisOutcomeProjector (coinSelOutcome (selCoin3Sym mPayload) c) =
      (coreSixSym mPayload).basisOutcomeProjector (coinSixOutcome c) *
        (corePayloadSym mPayload).basisOutcomeProjector 0 := by
  rw [QRegister.basisOutcomeProjector_eq_diagonal, QRegister.basisOutcomeProjector_eq_diagonal,
    QRegister.basisOutcomeProjector_eq_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext g
  have hCoinOut (k : Wire (selWiresSym mPayload)) :
      basisBits (selWiresSym mPayload) (coinSelOutcome (selCoin3Sym mPayload) c) k =
        if hk : k.val < 3 then basisBits 3 c ⟨k.val, hk⟩ else 0 := by
    by_cases hk : k.val < 3
    · rw [dite_pos_s1 hk]
      exact (congrArg (basisBits _ _) (Fin.ext (Nat.zero_add k.val).symm)).trans
        (basisBits_coinSelOutcome_coin (selCoin3Sym mPayload) c ⟨k.val, hk⟩)
    · rw [dite_neg_s1 hk]
      apply basisBits_coinSelOutcome_outside
      intro hmem
      rcases Finset.mem_map.mp hmem with ⟨r, _, hr⟩
      have hv := congrArg Fin.val hr
      dsimp [selCoin3Sym, MomSlots01Slot1ProjKineticAlt.qreg_block_wires_apply] at hv
      omega
  have hPayWire (j : Fin mPayload) : corePayloadSym mPayload j =
      coreAncSym mPayload ⟨6 + j.val, lt_of_lt_of_le (Nat.add_lt_add_left j.isLt 6) le_rfl⟩ :=
    Fin.ext (Nat.add_assoc SpecsAux.SpecMirror.systemQubits 6 j.val)
  have hSixWire (i : Fin 6) :
      coreSixSym mPayload i = coreAncSym mPayload ⟨i.val, Nat.lt_add_right mPayload i.isLt⟩ :=
    Fin.ext rfl
  have hb0 (j : Fin mPayload) : basisBits mPayload 0 j = 0 := by
    simp [-Nat.reducePow, basisBits_eq_div_mod]
  have hiff : (coreAncSym mPayload).extractIndex g = coinSelOutcome (selCoin3Sym mPayload) c ↔
      (coreSixSym mPayload).extractIndex g = coinSixOutcome c ∧
      (corePayloadSym mPayload).extractIndex g = 0 := by
    refine ⟨fun hAnc ↦ ⟨(basisBitsEquiv 6).injective (funext fun i ↦ ?_),
      (basisBitsEquiv mPayload).injective (funext fun j ↦ ?_)⟩, fun ⟨hSix, hPay⟩ ↦
        (basisBitsEquiv (selWiresSym mPayload)).injective (funext fun k ↦ ?_)⟩
    · change basisBits 6 _ i = basisBits 6 _ i
      rw [QRegister.basisBits_extractIndex, hSixWire i, ← QRegister.basisBits_extractIndex,
        hAnc, hCoinOut, coinSixOutcome, basisBits_symm_apply_local_slot1]
    · change basisBits mPayload _ j = basisBits mPayload 0 j
      rw [QRegister.basisBits_extractIndex, hPayWire j, ← QRegister.basisBits_extractIndex,
        hAnc, hCoinOut, dite_neg_s1 (by dsimp; omega), hb0]
    · change basisBits _ _ k = basisBits _ _ k
      rw [QRegister.basisBits_extractIndex, hCoinOut]
      by_cases hk6 : k.val < 6
      · rw [(hSixWire ⟨k.val, hk6⟩).symm, ← QRegister.basisBits_extractIndex, hSix,
          coinSixOutcome, basisBits_symm_apply_local_slot1]
      · have hk_lt : k.val < 6 + mPayload := k.isLt
        let j : Fin mPayload := ⟨k.val - 6, by omega⟩
        have hk_eq : coreAncSym mPayload k = corePayloadSym mPayload j := by
          rw [hPayWire j]
          exact congrArg (coreAncSym mPayload) (Fin.ext (show k.val = 6 + (k.val - 6) by omega))
        rw [hk_eq, ← QRegister.basisBits_extractIndex, hPay, hb0, dite_neg_s1 (by omega)]
  by_cases hA : (coreAncSym mPayload).extractIndex g = coinSelOutcome (selCoin3Sym mPayload) c
  · rcases hiff.mp hA with ⟨h1, h2⟩
    simp [hA, h1, h2]
  · by_cases h1 : (coreSixSym mPayload).extractIndex g = coinSixOutcome c
    · simp [hA, h1, show (corePayloadSym mPayload).extractIndex g ≠ 0 from
        fun h2 ↦ hA (hiff.mpr ⟨h1, h2⟩)]
    · simp [hA, h1]
theorem coin3_bits_eq_5_iff (c : Fin 8) :
    (basisBits 3 c 0 = 1 ∧ basisBits 3 c 1 = 0 ∧ basisBits 3 c 2 = 1) ↔ c = 5 := by
  fin_cases c <;> decide
theorem card_fin_lt_two_pow_slot1 {b T : ℕ} (hT : T ≤ 2 ^ b) :
    ((Finset.univ : Finset (Fin (2 ^ b))).filter (fun v ↦ v.val < T)).card = T := by
  let emb : Fin T ↪ Fin (2 ^ b) :=
    ⟨fun i ↦ ⟨i.val, lt_of_lt_of_le i.isLt hT⟩, fun _ _ h ↦ Fin.ext (by
      simpa using congrArg Fin.val h)⟩
  have hmap : Finset.map emb Finset.univ =
      (Finset.univ : Finset (Fin (2 ^ b))).filter (fun v ↦ v.val < T) := by
    ext v
    simp only [Finset.mem_map, Finset.mem_univ, true_and, Finset.mem_filter]
    exact ⟨fun ⟨i, hi⟩ ↦ hi ▸ i.isLt, fun hv ↦ ⟨⟨v.val, hv⟩, rfl⟩⟩
  rw [← hmap, Finset.card_map, Finset.card_fin]
theorem hadamardAll_comm_embedMatrix_slot1 {b k N : ℕ} (r : QRegister b N)
    (rOther : QRegister k N) (hdisj : r.DisjointWires rOther) (A : Operator (2 ^ k)) :
    (PhaseGradCatalystCore.hadamardAll r).eval.1 * rOther.embedMatrix A = rOther.embedMatrix A
    * (PhaseGradCatalystCore.hadamardAll r).eval.1 := by
  induction b with
  | zero =>
      simp [show (PhaseGradCatalystCore.hadamardAll r).eval.1 = 1 by
        unfold PhaseGradCatalystCore.hadamardAll
        rw [List.ofFn_zero]
        rfl]
  | succ b ih =>
      let rTail : QRegister b N :=
        ⟨fun i ↦ r i.succ, fun _ _ h ↦ Fin.succ_injective _ (r.wires.injective h)⟩
      have hsplit : (PhaseGradCatalystCore.hadamardAll r).eval.1 =
          (PhaseGradCatalystCore.hadamardAll rTail).eval.1 * (Circuit.H (r 0)).eval.1 := by
        unfold PhaseGradCatalystCore.hadamardAll
        rw [List.ofFn_succ]
        rfl
      have h1q : (Circuit.H (r 0)).eval.1 * rOther.embedMatrix A =
          rOther.embedMatrix A * (Circuit.H (r 0)).eval.1 := by
        simpa only [Circuit.eval_single, PrimitiveGate.eval, QRegister.embedUnitary_val] using
          (QRegister.singleton (r 0)).embedMatrix_comm_of_disjoint rOther
            (QRegister.disjoint_iff.mpr fun ⟨0, _⟩ j ↦ hdisj.ne 0 j) Qubit.H.1 A
      rw [hsplit, Matrix.mul_assoc, h1q, ← Matrix.mul_assoc,
        ih rTail (QRegister.disjoint_iff.mpr fun i j ↦ hdisj.ne i.succ j), Matrix.mul_assoc]
theorem twosComp8Int_injective : Function.Injective twosComp8Int := fun u v huv ↦ by
  have := u.isLt
  have := v.isLt
  unfold twosComp8Int at huv
  exact Fin.ext (by omega)
theorem smToTwosSys_conj_diagonal_slot1 (d : Fin (2 ^ SpecsAux.SpecMirror.systemQubits) → ℂ) :
    smToTwosSysUnitary.1 * Matrix.diagonal d * smToTwosSysUnitary.1 =
      Matrix.diagonal (d ∘ smToTwosSysPerm) := by
  nth_rw 1 [← smToTwosSysUnitary_conjTranspose]
  exact fwdPermUnitary_conj_diagonal smToTwosSysPerm d
theorem norm_sandwich_le_of_norm_le_one {D : ℕ} (P M : Operator D) (hP : ‖P‖ ≤ 1) :
    ‖P * M * P‖ ≤ ‖M‖ :=
  (Matrix.l2_opNorm_mul (P * M) P).trans <|
    (mul_le_of_le_one_right (norm_nonneg _) hP).trans <|
      (Matrix.l2_opNorm_mul P M).trans (mul_le_of_le_one_left (norm_nonneg M) hP)
section Slot1CleanCircuit
noncomputable abbrev ket {K : ℕ} (β : BitAssignment K) : Fin (2 ^ K) → ℂ :=
  basisState ((basisBitsEquiv K).symm β)
theorem single_eq_ket {K : ℕ} (g : Fin (2 ^ K)) :
    (Pi.single g 1 : Fin (2 ^ K) → ℂ) = ket (basisBits K g) := by simp [ket, basisState]
theorem matrix_ext_ket {K : ℕ} {A B : Matrix (Fin (2 ^ K)) (Fin (2 ^ K)) ℂ}
    (h : ∀ β, A.mulVec (ket β) = B.mulVec (ket β)) : A = B := by
  ext i j
  simpa [← single_eq_ket, Matrix.mulVec_single_one] using congrFun (h (basisBits K j)) i
theorem zmod2_add_self (x : ZMod 2) : x + x = 0 :=
  (by decide : ∀ y : ZMod 2, y + y = 0) x
inductive RevProg (K : ℕ) : Type
  | nil : RevProg K
  | x (t : Wire K) : RevProg K
  | cnot (c t : Wire K) (h : c ≠ t) : RevProg K
  | toff (c₁ c₂ t : Wire K) (h₁₂ : c₁ ≠ c₂) (h₁t : c₁ ≠ t) (h₂t : c₂ ≠ t) : RevProg K
  | seq (p₁ p₂ : RevProg K) : RevProg K
namespace RevProg
def toCircuit {K : ℕ} : RevProg K → Circuit K
  | .nil => .identity
  | .x t => Circuit.X t
  | .cnot c t h => Circuit.CNOT c t h
  | .toff c₁ c₂ t h₁₂ h₁t h₂t => Circuit.TOFF c₁ c₂ t h₁₂ h₁t h₂t
  | .seq p₁ p₂ => p₁.toCircuit.seq p₂.toCircuit
def inv {K : ℕ} : RevProg K → RevProg K
  | .nil => .nil
  | .x t => .x t
  | .cnot c t h => .cnot c t h
  | .toff c₁ c₂ t h₁₂ h₁t h₂t => .toff c₁ c₂ t h₁₂ h₁t h₂t
  | .seq p₁ p₂ => .seq p₂.inv p₁.inv
def eval {K : ℕ} : RevProg K → BitAssignment K → BitAssignment K
  | .nil, β => β
  | .x t, β => Function.update β t (β t + 1)
  | .cnot c t _, β => Function.update β t (β t + β c)
  | .toff c₁ c₂ t _ _ _, β => Function.update β t (β t + β c₁ * β c₂)
  | .seq p₁ p₂, β => p₂.eval (p₁.eval β)
@[simp] theorem count_t_zero {K : ℕ} (p : RevProg K) :
    p.toCircuit.count PrimitiveGate.T = 0 := by
  induction p <;> simp_all [toCircuit]
@[simp] theorem eval_inv_left {K : ℕ} (p : RevProg K) (β : BitAssignment K) :
    p.inv.eval (p.eval β) = β := by
  induction p generalizing β with
  | nil => rfl
  | x t => simp [inv, eval, add_assoc]
  | cnot c t h => simp [inv, eval, h, add_assoc]
  | toff c₁ c₂ t _ h₁t h₂t => simp [inv, eval, h₁t, h₂t, add_assoc]
  | seq p₁ p₂ ih₁ ih₂ => simp [inv, eval, ih₂, ih₁]
@[simp] theorem eval_seq {K : ℕ} (p₁ p₂ : RevProg K) (β : BitAssignment K) :
    (p₁.seq p₂).eval β = p₂.eval (p₁.eval β) := rfl
def countToff {K : ℕ} : RevProg K → ℕ
  | .nil | .x _ | .cnot _ _ _ => 0
  | .toff _ _ _ _ _ _ => 1
  | .seq p₁ p₂ => p₁.countToff + p₂.countToff
@[simp] theorem countToff_inv {K : ℕ} : ∀ p : RevProg K, p.inv.countToff = p.countToff
  | .nil | .x _ | .cnot _ _ _ | .toff _ _ _ _ _ _ => rfl
  | .seq p₁ p₂ =>
      (Nat.add_comm _ _).trans (congrArg₂ (· + ·) (countToff_inv p₁) (countToff_inv p₂))
@[simp] theorem toCircuit_count_toff {K : ℕ} :
    ∀ p : RevProg K, p.toCircuit.count PrimitiveGate.TOFF = p.countToff
  | .nil | .x _ | .cnot _ _ _ | .toff _ _ _ _ _ _ => rfl
  | .seq p₁ p₂ =>
      by simp [toCircuit, countToff, toCircuit_count_toff p₁, toCircuit_count_toff p₂]
end RevProg
def padZeroBits {kAct mClean : ℕ} (α : BitAssignment kAct) : BitAssignment (kAct + mClean) :=
  Fin.addCases α (fun _ ↦ 0)
noncomputable def phaseDiagUnitary {kAct : ℕ} (pred : BitAssignment kAct → ZMod 2) :
    Unitary (2 ^ kAct) :=
  ⟨Matrix.diagonal fun g ↦ ((-1 : ℂ) ^ (pred (basisBits kAct g)).val), by
    rw [mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
      Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext g
    simpa using neg_one_pow_bit_mul_self (pred (basisBits kAct g)).val⟩
@[simp] theorem slice_one_succ {K m : ℕ} (r : QRegister (m + 1) K) (h : 1 + m ≤ m + 1)
    (j : Fin m) : (r.slice 1 m h) j = r j.succ :=
  congrArg r (Fin.ext (Nat.add_comm 1 j.val))
@[simp] theorem block_one_wires_apply {m : ℕ} (h : 1 + m ≤ m + 1) (j : Fin m) :
    (QRegister.block 1 m h).wires j = j.succ := Fin.ext (Nat.add_comm 1 j.val)
end Slot1CleanCircuit
theorem momCoinProj_eq_fullSys (mPayload : ℕ) (c : Fin 8) : momCoinProj mPayload c =
    FullSysMomSlots0135Concrete.momCoinProj mPayload c := by
  unfold momCoinProj FullSysMomSlots0135Concrete.momCoinProj coinBitFin2
    FullSysMomSlots0135Concrete.coinBitFin2
  rfl
end MomSlots01Slot1ProjKinetic
namespace MomSlot1GeomPriority288
section ConfigMomSlot1GeomPriority288
set_option maxRecDepth 1024
set_option exponentiation.threshold 256
set_option backward.isDefEq.respectTransparency true
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup
local instance (priority := 1000000) instNeZeroTwoPowMom1Geom (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩
open Operator Matrix QProg Circuit _root_.DynamicCircuit DynCircuitExt HermitianMat Real
open SpecsAux SpecsAux.SpecMirror
open SpecsAux.PhaseGradCatalystCore
open SpecsAux.BridgeFermionicComm
open SpecsAux.BridgeFermionicComm.SpecInner
open PosMomSelectSandwich
open PosMomSelectDynamic hiding embedMatrix_diagonal
open SixSlotEndpointJunctionBridge
open FullSysPrepare6Slot
-- Root solution namespace already active.
open TwosCompAndWire0Cancel
open LiteralKineticAndMidpoint128
open SpecsAux.SpecMirror.SixChannelHamiltonianSplit (sixChannelRaw sixChannelShifted)
open InPlaceFullAddSlice (ket bitSign bit_cases matrix_ext_ket eval_seq_mulVec ket_CNOT ket_TOFF
  ket_projector_zero projZeroAll ket_projZeroAll projZeroAll_conjTranspose RealizesCleanUnitary
  PreservesStoreConst wire_ne_of_gt mul_mulVec_prog writeRegProg writeRegProg_apply_reg
  writeRegProg_apply_of_not_mem CliffProg TempPhaseProg cleanRem tailScr tailScr_succ
  projZeroAll_tailScr_sub ValidCleanRem eval_onRegister_prog_ket RealizesCleanUnitary_seq_asym)
open MeasureBranchHadamardSem (sqrtHalf)
open MomSlots01Slot1ProjKinetic (coreWiresSym coreAncSym coreSysSym corePayloadSym selCoin3Sym
  selWiresSym coreHadamardUnitary slot1AxisInt projAxisTerm sum_projAxisTerm_eq_centered coreSixSym
  coinSixOutcome ancProjector_eq_six_mul_payload embedMatrix_diagonal
  hadamardAll_comm_embedMatrix_slot1 twosComp8Int_injective smToTwosSys_conj_diagonal_slot1
  norm_sandwich_le_of_norm_le_one momCoinProj coin3_bits_eq_5_iff)
open scoped Matrix BigOperators Circuit.Notation Matrix.Norms.L2Operator
theorem cleanRem_anti {M rem₁ rem₂ : ℕ} (hle : rem₁ ≤ rem₂) {β : BitAssignment M}
    (h : cleanRem M rem₂ β) : cleanRem M rem₁ β := fun w hw ↦ h w (by omega)
theorem validCleanRem_mono {M : ℕ} :
    ∀ {p : TempPhaseProg M} {rem₁ rem₂ : ℕ}, rem₁ ≤ rem₂ →
      ValidCleanRem M rem₁ p → ValidCleanRem M rem₂ p
  | .nil, _, _, _, _ | .cliff _, _, _, _, _ | .z _, _, _, _, _ => trivial
  | .seq _ _, _, _, hle, ⟨remMid, hmid, hv₁, hv₂, hpres⟩ =>
      ⟨remMid, hmid, validCleanRem_mono hle hv₁, hv₂, fun β hβ ↦ hpres β (cleanRem_anti hle hβ)⟩
  | .tempAnd _ _ _ _ _ _ _, _, _, hle, ⟨_, hvB, hpB⟩ => ⟨by omega, hvB, hpB⟩
theorem ite_pos_s1 {α : Type*} {c : Prop} [Decidable c] (hc : c) (a b : α) :
    (if c then a else b) = a := ite_eq_left hc
theorem ite_neg_s1 {α : Type*} {c : Prop} [Decidable c] (hc : ¬c) (a b : α) :
    (if c then a else b) = b := ite_eq_right hc
theorem dite_pos_s1 {α : Type*} {c : Prop} [Decidable c] (hc : c) (a : c → α) (b : ¬c → α) :
    (if h : c then a h else b h) = a hc := dite_eq_left hc
theorem dite_neg_s1 {α : Type*} {c : Prop} [Decidable c] (hc : ¬c) (a : c → α) (b : ¬c → α) :
    (if h : c then a h else b h) = b hc := dite_eq_right hc
def czCircuit {n : ℕ} (a b : Wire n) (h : a ≠ b) : Circuit n :=
  Circuit.H b ;;ᶜ Circuit.CNOT a b h ;;ᶜ Circuit.H b
@[simp] theorem czCircuit_count_toff {n : ℕ} (a b : Wire n) (h : a ≠ b) :
    (czCircuit a b h).count PrimitiveGate.TOFF = 0 := by
  simp [czCircuit, Circuit.H, Circuit.CNOT, Circuit.single, Circuit.count]
@[simp] theorem czCircuit_count_t {n : ℕ} (a b : Wire n) (h : a ≠ b) :
    (czCircuit a b h).count PrimitiveGate.T = 0 := by
  simp [czCircuit, Circuit.H, Circuit.CNOT, Circuit.single, Circuit.count]
theorem sqrtHalf_mul_self_two : (sqrtHalf * sqrtHalf : ℂ) * 2 = 1 := by
  rw [show (sqrtHalf : ℂ) = ((√(1 / 2 : ℝ) : ℝ) : ℂ) by simp [sqrtHalf],
    ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
  norm_num
theorem ket_H_local {n : ℕ} (b : Wire n) (β : BitAssignment n) :
    (Circuit.H b).eval.1.mulVec (ket β) =
      sqrtHalf • (ket (Function.update β b 0) + bitSign (β b) • ket (Function.update β b 1)) := by
  simpa [ket, bitSign, MeasureBranchHadamardSem.ket, MeasureBranchHadamardSem.bitSign] using
    MeasureBranchHadamardSem.ket_H b β
theorem ket_czCircuit {n : ℕ} (a b : Wire n) (h : a ≠ b) (β : BitAssignment n) :
    (czCircuit a b h).eval.1.mulVec (ket β) = ((-1 : ℂ) ^ (β a * β b).val) • ket β := by
  dsimp only [czCircuit]
  rw [eval_seq_mulVec, eval_seq_mulVec, ket_H_local]
  simp only [Matrix.mulVec_smul, Matrix.mulVec_add, ket_CNOT,
    Function.update_of_ne h, Function.update_self, Function.update_idem]
  rw [ket_H_local, ket_H_local]
  simp only [Function.update_self, Function.update_idem]
  have h11 : (1 : ZMod 2) + 1 = 0 := rfl
  ext idx
  rcases bit_cases (β b) with hb | hb
  · have hb0 : Function.update β b 0 = β := by simp [← hb]
    rcases bit_cases (β a) with ha | ha
    · simp [ha, hb, bitSign, hb0]
      linear_combination (ket β idx) * sqrtHalf_mul_self_two
    · simp [ha, hb, h11, bitSign, hb0]
      linear_combination (ket β idx) * sqrtHalf_mul_self_two
  · have hb1 : Function.update β b 1 = β := by simp [← hb]
    rcases bit_cases (β a) with ha | ha
    · simp [ha, hb, bitSign, hb1]
      linear_combination (ket β idx) * sqrtHalf_mul_self_two
    · simp [ha, hb, h11, bitSign, hb1]
      linear_combination -(ket β idx) * sqrtHalf_mul_self_two
inductive TempCtx (M : ℕ) where
  | hole : TempCtx M
  | seqPre (c : CliffProg M) (K : TempCtx M) : TempCtx M
  | seqPost (K : TempCtx M) (c : CliffProg M) : TempCtx M
  | tempAnd (c₁ c₂ anc : Wire M) (h₁₂ : c₁ ≠ c₂) (h₁a : c₁ ≠ anc) (h₂a : c₂ ≠ anc)
      (K : TempCtx M) : TempCtx M
namespace TempCtx
def plug {M : ℕ} : TempCtx M → TempPhaseProg M → TempPhaseProg M
  | .hole, body => body
  | .seqPre c K, body => .seq (.cliff c) (K.plug body)
  | .seqPost K c, body => .seq (K.plug body) (.cliff c)
  | .tempAnd c₁ c₂ anc h₁₂ h₁a h₂a K, body => .tempAnd c₁ c₂ anc h₁₂ h₁a h₂a (K.plug body)
def countTempAnd {M : ℕ} : TempCtx M → ℕ
  | .hole => 0
  | .seqPre _ K => K.countTempAnd
  | .seqPost K _ => K.countTempAnd
  | .tempAnd _ _ _ _ _ _ K => 1 + K.countTempAnd
def fwdBits {M : ℕ} : TempCtx M → BitAssignment M → BitAssignment M
  | .hole, β => β
  | .seqPre c K, β => K.fwdBits (c.eval β)
  | .seqPost K _, β => K.fwdBits β
  | .tempAnd c₁ c₂ anc _ _ _ K, β => K.fwdBits (Function.update β anc (β anc + β c₁ * β c₂))
end TempCtx
def toDynWithDyn {Var : Type} {M n : ℕ} (v : Var) (r : QRegister M n)
    (inner : DynamicCircuit Var n) : TempCtx M → DynamicCircuit Var n
  | .hole => inner
  | .seqPre c K => .seq (.circuit (c.onRegister r).toCircuit) (toDynWithDyn v r inner K)
  | .seqPost K c => .seq (toDynWithDyn v r inner K) (.circuit (c.onRegister r).toCircuit)
  | .tempAnd c₁ c₂ anc h₁₂ h₁a h₂a K => .seq (DynamicCircuit.andCompute (r c₁) (r c₂) (r anc)
      (r.wires.injective.ne h₁a) (r.wires.injective.ne h₂a)) (.seq (toDynWithDyn v r inner K)
        (DynamicCircuit.andUncompute v (r c₁) (r c₂) (r anc) (r.wires.injective.ne h₁₂)))
theorem toDynWithDyn_count_toff {Var : Type} {M n : ℕ} (v : Var) (r : QRegister M n)
    (inner : DynamicCircuit Var n) (hInner : inner.count PrimitiveGate.TOFF = 0) :
    ∀ K : TempCtx M, (toDynWithDyn v r inner K).count PrimitiveGate.TOFF = 0
  | .hole => hInner
  | .seqPre _ K | .seqPost K _ => by
      simp [toDynWithDyn, CliffProg.toCircuit_count_toff,
        toDynWithDyn_count_toff v r inner hInner K]
  | .tempAnd _ _ _ _ _ _ K => by
      simp [toDynWithDyn, DynamicCircuit.count_andCompute_toff,
        DynamicCircuit.count_andUncompute_toff, toDynWithDyn_count_toff v r inner hInner K]
theorem toDynWithDyn_count_t {Var : Type} {M n : ℕ} (v : Var) (r : QRegister M n)
    (inner : DynamicCircuit Var n) : ∀ K : TempCtx M,
      (toDynWithDyn v r inner K).count PrimitiveGate.T =
        4 * K.countTempAnd + inner.count PrimitiveGate.T
  | .hole => by simp [toDynWithDyn, TempCtx.countTempAnd]
  | .seqPre _ K | .seqPost K _ => by
      simp [toDynWithDyn, TempCtx.countTempAnd, CliffProg.toCircuit_count_t,
        toDynWithDyn_count_t v r inner K]
  | .tempAnd _ _ _ _ _ _ K => by
      simp [toDynWithDyn, DynamicCircuit.count_andCompute_t,
        DynamicCircuit.count_andUncompute_t, TempCtx.countTempAnd,
        toDynWithDyn_count_t v r inner K]
      ring
theorem toDynWithDyn_preservesStoreConst {Var : Type} [Fintype Var] [DecidableEq Var]
    {M n : ℕ} (v : Var) (r : QRegister M n) (inner : DynamicCircuit Var n)
    (hInner : PreservesStoreConst inner) :
    ∀ K : TempCtx M, PreservesStoreConst (toDynWithDyn v r inner K)
  | .hole => hInner
  | .seqPre _ K => PreservesStoreConst.seq (PreservesStoreConst.circuit _)
      (toDynWithDyn_preservesStoreConst v r inner hInner K)
  | .seqPost K _ => PreservesStoreConst.seq
      (toDynWithDyn_preservesStoreConst v r inner hInner K) (PreservesStoreConst.circuit _)
  | .tempAnd c₁ c₂ anc h₁₂ _ _ K => PreservesStoreConst.seq (PreservesStoreConst.circuit _)
      (PreservesStoreConst.seq (toDynWithDyn_preservesStoreConst v r inner hInner K)
        (PreservesStoreConst.andUncompute v (r c₁) (r c₂) (r anc)
          (r.wires.injective.ne h₁₂)))
private theorem regProg_self {M n : ℕ} (β : BitAssignment n) (r : QRegister M n) :
    writeRegProg β r (fun idx ↦ β (r idx)) = β := funext fun w ↦ by
  by_cases hm : w ∈ Set.range r.wires
  · rcases hm with ⟨idx, rfl⟩
    exact writeRegProg_apply_reg _ _ _ _
  · exact writeRegProg_apply_of_not_mem _ _ _ _ hm
private theorem regProg_idem {M n : ℕ} (β : BitAssignment n) (r : QRegister M n)
    (f g : BitAssignment M) :
    writeRegProg (writeRegProg β r f) r g = writeRegProg β r g := funext fun w ↦ by
  by_cases hm : w ∈ Set.range r.wires
  · rcases hm with ⟨idx, rfl⟩
    simp [writeRegProg_apply_reg]
  · simp [writeRegProg_apply_of_not_mem _ _ _ _ hm]
private theorem regProg_update {M n : ℕ} (β : BitAssignment n) (r : QRegister M n)
    (f : BitAssignment M) (a : Wire M) (v : ZMod 2) :
    Function.update (writeRegProg β r f) (r a) v = writeRegProg β r (Function.update f a v) :=
  funext fun w ↦ by
    by_cases hm : w ∈ Set.range r.wires
    · rcases hm with ⟨idx, rfl⟩
      by_cases hia : idx = a
      · simp [hia, writeRegProg_apply_reg]
      · simp [hia, r.wires.injective.ne hia, writeRegProg_apply_reg]
    · simp [show w ≠ r a from fun h ↦ hm ⟨a, h.symm⟩, writeRegProg_apply_of_not_mem _ _ _ _ hm]
theorem realizes_toDynWithDyn_of_valid {Var : Type} [Fintype Var] [DecidableEq Var] {M n : ℕ}
    [NeZero (2 ^ n)] (v : Var) (rComb : QRegister M n) (remHole : ℕ) (hremHole : remHole ≤ M)
    (probe : TempPhaseProg M) (hProbeRem : ∀ rem, ValidCleanRem M rem probe → remHole ≤ rem)
    (hProbeBits : ∀ γ : BitAssignment M, probe.evalBits γ = γ) (inner : DynamicCircuit Var n)
    (U₀ : Unitary (2 ^ n)) (hInner : RealizesCleanUnitary v (projZeroAll remHole (tailScr
    rComb remHole hremHole)) inner U₀) (ph : BitAssignment M → ZMod 2) (hInnerKet : ∀ β :
    BitAssignment n, U₀.1.mulVec (ket β) = ((-1 : ℂ) ^ (ph (fun idx ↦ β (rComb idx))).val) •
    ket β) : ∀ (K : TempCtx M) (rem : ℕ) (hrem : rem ≤ M), ValidCleanRem M rem (K.plug probe)
    → ∃ U : Unitary (2 ^ n), RealizesCleanUnitary v (projZeroAll rem (tailScr rComb rem hrem))
    (toDynWithDyn v rComb inner K) U ∧ ∀ β : BitAssignment n, U.1.mulVec (ket β) =
    ((-1 : ℂ) ^ (ph (K.fwdBits (fun idx ↦ β (rComb idx)))).val) • ket (writeRegProg β rComb
    ((K.plug probe).evalBits (fun idx ↦ β (rComb idx)))) := by
  have hcKet : ∀ (c : CliffProg M) (β : BitAssignment n),
      (c.onRegister rComb).toCircuit.eval.1.mulVec (ket β) =
        ket (writeRegProg β rComb (c.eval (fun idx ↦ β (rComb idx)))) := fun c β ↦
    (eval_onRegister_prog_ket rComb (.cliff c) β).trans
      (by simp [TempPhaseProg.evalSign, TempPhaseProg.evalBits])
  have hread : ∀ (β : BitAssignment n) (f : BitAssignment M),
      (fun idx ↦ writeRegProg β rComb f (rComb idx)) = f :=
    fun β f ↦ funext fun idx ↦ writeRegProg_apply_reg _ _ _ idx
  have htail_clean : ∀ {r : ℕ} (hr : r ≤ M) (β : BitAssignment n),
      (∀ j : Fin r, β (tailScr rComb r hr j) = 0) → cleanRem M r (fun i ↦ β (rComb i)) :=
    fun {r} hr β hz w hw ↦ by
      rw [show w = ⟨(M - r) + (w.val - (M - r)), by omega⟩ from Fin.ext (by dsimp; omega)]
      exact hz ⟨w.val - (M - r), by omega⟩
  intro K
  induction K with
  | hole =>
      intro rem hrem hv
      refine ⟨U₀, RealizesCleanUnitary.mono_proj (projZeroAll_conjTranspose remHole _)
        (projZeroAll_conjTranspose rem _) (projZeroAll_tailScr_sub rComb hremHole hrem
        (hProbeRem rem hv)) hInner, fun β ↦ ?_⟩
      dsimp only [TempCtx.fwdBits, TempCtx.plug]
      rw [hProbeBits, regProg_self]
      exact hInnerKet β
  | seqPre c K₁ ih =>
      intro rem hrem ⟨remMid, hmid, _, hv₁, hpres₁⟩
      obtain ⟨U₁, hReal₁, hKet₁⟩ := ih remMid hmid hv₁
      let cPre := (c.onRegister rComb).toCircuit
      have hclean : projZeroAll remMid (tailScr rComb remMid hmid) *
          (cPre.eval.1 * projZeroAll rem (tailScr rComb rem hrem)) =
          cPre.eval.1 * projZeroAll rem (tailScr rComb rem hrem) := matrix_ext_ket fun β ↦ by
        simp only [mul_mulVec_prog, ket_projZeroAll]
        by_cases hz : ∀ j : Fin rem, β (tailScr rComb rem hrem j) = 0
        · dsimp only [cPre]
          have hout (j : Fin remMid) : writeRegProg β rComb (c.eval (fun i ↦ β (rComb i)))
              (tailScr rComb remMid hmid j) = 0 :=
            (writeRegProg_apply_reg _ _ _ _).trans
              (hpres₁ _ (htail_clean hrem β hz) ⟨(M - remMid) + j.val, by omega⟩
                (Nat.le_add_right _ _))
          simp only [hz, hout, imp_true_iff, ↓reduceIte, hcKet c, ket_projZeroAll]
        · simp only [hz, ↓reduceIte, Matrix.mulVec_zero]
      refine ⟨U₁ * cPre.eval, RealizesCleanUnitary_seq_asym (projZeroAll_conjTranspose rem _)
        (projZeroAll_conjTranspose remMid _) (RealizesCleanUnitary.circuit v _ cPre) hReal₁
        hclean, fun β ↦ ?_⟩
      simp only [cPre, Submonoid.coe_mul, ← Matrix.mulVec_mulVec, hcKet c, hKet₁,
        hread, regProg_idem]
      rfl
  | seqPost K₁ c ih =>
      intro rem hrem ⟨_, _, hv₁, _, _⟩
      obtain ⟨U₁, hReal₁, hKet₁⟩ := ih rem hrem hv₁
      let cPost := (c.onRegister rComb).toCircuit
      refine ⟨cPost.eval * U₁, RealizesCleanUnitary_seq_asym (projZeroAll_conjTranspose rem _)
        (projZeroAll_conjTranspose 0 _) hReal₁ (RealizesCleanUnitary.circuit v
          (projZeroAll 0 (tailScr rComb 0 (Nat.zero_le M))) cPost)
        (by rw [show projZeroAll 0 (tailScr rComb 0 (Nat.zero_le M)) = 1 from
          matrix_ext_ket fun α ↦ by simp [ket_projZeroAll], Matrix.one_mul]), fun β ↦ ?_⟩
      simp only [cPost, Submonoid.coe_mul, ← Matrix.mulVec_mulVec, hKet₁, Matrix.mulVec_smul,
        hcKet c, hread, regProg_idem]
      rfl
  | tempAnd c₁ c₂ anc h₁₂ h₁a h₂a K₁ ih =>
      intro rem hrem ⟨hanc_lo, hvBody, hpresBody⟩
      have hanc_lt : anc.val < M := anc.isLt
      let rem' := M - (anc.val + 1)
      have hrem1 : rem' + 1 ≤ M := by omega
      obtain ⟨U_body, ihBody, hKetBody⟩ := ih rem' (Nat.le_of_succ_le hrem1) hvBody
      have hdisj (j : Fin rem') : rComb anc ≠ tailScr rComb rem' (Nat.le_of_succ_le hrem1) j :=
        fun h ↦ by
          have hinj := congrArg Fin.val (rComb.wires.injective h)
          change anc.val = (M - rem') + j.val at hinj
          omega
      let h₁₂' := rComb.wires.injective.ne h₁₂
      let h₁a' := rComb.wires.injective.ne h₁a
      let h₂a' := rComb.wires.injective.ne h₂a
      let U_clean := (Circuit.TOFF (rComb c₁) (rComb c₂) (rComb anc) h₁₂' h₁a' h₂a').eval *
        U_body * (Circuit.TOFF (rComb c₁) (rComb c₂) (rComb anc) h₁₂' h₁a' h₂a').eval
      have hCleanKet (β : BitAssignment n) : U_clean.1.mulVec (ket β) =
          ((-1 : ℂ) ^ (ph ((TempCtx.tempAnd c₁ c₂ anc h₁₂ h₁a h₂a K₁).fwdBits
            (fun idx ↦ β (rComb idx)))).val) • ket (writeRegProg β rComb
            (((TempCtx.tempAnd c₁ c₂ anc h₁₂ h₁a h₂a K₁).plug probe).evalBits
              (fun idx ↦ β (rComb idx)))) := by
        simp only [U_clean, Submonoid.coe_mul, ← Matrix.mulVec_mulVec]
        change (Circuit.TOFF _ _ _ _ _ _).eval.1.mulVec (U_body.1.mulVec
          ((Circuit.TOFF _ _ _ _ _ _).eval.1.mulVec (ket β))) = _
        rw [ket_TOFF, ← regProg_self β rComb, regProg_update,
          regProg_self, hKetBody, hread, Matrix.mulVec_smul, ket_TOFF,
          regProg_idem, writeRegProg_apply_reg, writeRegProg_apply_reg,
          writeRegProg_apply_reg, regProg_update]
        rfl
      have hstep := RealizesCleanUnitary.withTempAnd_projZeroAll v (rComb c₁) (rComb c₂)
        (rComb anc) h₁₂' h₁a' h₂a' rem' (tailScr rComb rem' (Nat.le_of_succ_le hrem1)) hdisj
        (toDynWithDyn v rComb inner K₁) U_body U_clean ihBody
        (fun β hanc0 _ ↦ by
          simp only [U_clean, Submonoid.coe_mul, ← Matrix.mulVec_mulVec]
          symm
          change (Circuit.TOFF _ _ _ _ _ _).eval.1.mulVec (U_body.1.mulVec
            ((Circuit.TOFF _ _ _ _ _ _).eval.1.mulVec (ket β))) = _
          rw [ket_TOFF, hanc0, zero_add])
        (fun β hanc0 hscr0 ↦ by
          let β₁ : BitAssignment M := Function.update (fun idx ↦ β (rComb idx)) anc
            (β (rComb anc) + β (rComb c₁) * β (rComb c₂))
          obtain ⟨hc₁, hc₂, ha⟩ := hpresBody β₁ fun w hw ↦ by
            dsimp only [β₁]
            rw [Function.update_of_ne (wire_ne_of_gt (by omega))]
            exact htail_clean (Nat.le_of_succ_le hrem1) β hscr0 w hw
          have hfinal_anc : (((TempCtx.tempAnd c₁ c₂ anc h₁₂ h₁a h₂a K₁).plug probe).evalBits
              (fun idx ↦ β (rComb idx))) anc = 0 := by
            dsimp only [TempCtx.plug, TempPhaseProg.evalBits]
            change Function.update ((K₁.plug probe).evalBits β₁) anc _ anc = 0
            rw [Function.update_self, ha, hc₁, hc₂]
            simp [β₁, hanc0, Function.update_self, Function.update_of_ne h₁a,
              Function.update_of_ne h₂a, CharTwo.add_self_eq_zero]
          simp [hCleanKet β, Matrix.mulVec_smul, ket_projector_zero, writeRegProg_apply_reg,
            hfinal_anc])
      exact ⟨U_clean, RealizesCleanUnitary.mono_proj (projZeroAll_conjTranspose (rem' + 1) _)
        (projZeroAll_conjTranspose rem _) (projZeroAll_tailScr_sub rComb hrem1 hrem (by omega))
        (by simpa only [toDynWithDyn, show anc = ⟨M - (rem' + 1), by omega⟩ from
          Fin.ext (by dsimp; omega), ← tailScr_succ rComb rem' hrem1] using hstep), hCleanKet⟩
theorem zmod2_add_self (z : ZMod 2) : z + z = 0 := by
  rcases bit_cases z with rfl | rfl <;> rfl
theorem zmod2_add_assoc_cancel (a b : ZMod 2) : a + b + b = a := by
  rw [add_assoc, zmod2_add_self, add_zero]
inductive RawSsa (M : ℕ) : Type where
  | done : RawSsa M
  | x (q : Wire M) (rest : RawSsa M) : RawSsa M
  | cnot (c t : Wire M) (hct : c ≠ t) (rest : RawSsa M) : RawSsa M
  | skipZero (rest : RawSsa M) : RawSsa M
  | andClean (anc c₁ c₂ : Wire M) (h₁₂ : c₁ ≠ c₂) (hc1a : c₁ ≠ anc) (hc2a : c₂ ≠ anc)
      (rest : RawSsa M) : RawSsa M
namespace RawSsa
def Wf {M : ℕ} (cur endCur : ℕ) : RawSsa M → Prop
  | .done => cur = endCur
  | .x q rest => q.val < cur ∧ Wf cur endCur rest
  | .cnot c t _ rest => c.val < cur ∧ t.val < cur ∧ Wf cur endCur rest
  | .skipZero rest => cur < M ∧ Wf (cur + 1) endCur rest
  | .andClean anc c₁ c₂ _ _ _ rest =>
      anc.val = cur ∧ c₁.val < cur ∧ c₂.val < cur ∧ Wf (cur + 1) endCur rest
theorem le_end {M : ℕ} : ∀ {r : RawSsa M} {cur endCur : ℕ}, Wf cur endCur r → cur ≤ endCur
  | .done, _, _, h => le_of_eq h
  | .x _ _, _, _, ⟨_, hw⟩ | .cnot _ _ _ _, _, _, ⟨_, _, hw⟩ => le_end hw
  | .skipZero _, _, _, ⟨_, hw⟩
  | .andClean _ _ _ _ _ _ _, _, _, ⟨_, _, _, hw⟩ => Nat.le_of_succ_le (le_end hw)
def countAnd {M : ℕ} : RawSsa M → ℕ
  | .done => 0
  | .x _ rest | .cnot _ _ _ rest | .skipZero rest => rest.countAnd
  | .andClean _ _ _ _ _ _ rest => 1 + rest.countAnd
def eval {M : ℕ} : RawSsa M → BitAssignment M → BitAssignment M
  | .done, β => β
  | .x q rest, β => rest.eval (Function.update β q (β q + 1))
  | .cnot c t _ rest, β => rest.eval (Function.update β t (β t + β c))
  | .skipZero rest, β => rest.eval β
  | .andClean anc c₁ c₂ _ _ _ rest, β =>
      rest.eval (Function.update β anc (β anc + β c₁ * β c₂))
def append {M : ℕ} : RawSsa M → RawSsa M → RawSsa M
  | .done, q => q
  | .x w rest, q => .x w (rest.append q)
  | .cnot c t hct rest, q => .cnot c t hct (rest.append q)
  | .skipZero rest, q => .skipZero (rest.append q)
  | .andClean anc c₁ c₂ h₁₂ hc1a hc2a rest, q =>
      .andClean anc c₁ c₂ h₁₂ hc1a hc2a (rest.append q)
theorem append_wf {M : ℕ} :
    ∀ {p q : RawSsa M} {c₁ c₂ c₃ : ℕ}, Wf c₁ c₂ p → Wf c₂ c₃ q → Wf c₁ c₃ (p.append q)
  | .done, _, _, _, _, rfl, hq => hq
  | .x _ _, _, _, _, _, ⟨h1, hw⟩, hq => ⟨h1, append_wf hw hq⟩
  | .cnot _ _ _ _, _, _, _, _, ⟨h1, h2, hw⟩, hq => ⟨h1, h2, append_wf hw hq⟩
  | .skipZero _, _, _, _, _, ⟨h1, hw⟩, hq => ⟨h1, append_wf hw hq⟩
  | .andClean _ _ _ _ _ _ _, _, _, _, _, ⟨ha, h1, h2, hw⟩, hq => ⟨ha, h1, h2, append_wf hw hq⟩
theorem append_countAnd {M : ℕ} :
    ∀ (p q : RawSsa M), (p.append q).countAnd = p.countAnd + q.countAnd
  | .done, _ => by simp [append, countAnd]
  | .x _ rest, q | .cnot _ _ _ rest, q | .skipZero rest, q =>
      append_countAnd rest q
  | .andClean _ _ _ _ _ _ rest, q => by
      simp only [append, countAnd, append_countAnd rest q]
      omega
theorem append_eval {M : ℕ} :
    ∀ (p q : RawSsa M) (β : BitAssignment M), (p.append q).eval β = q.eval (p.eval β)
  | .done, _, _ => rfl
  | .x _ rest, q, _ | .cnot _ _ _ rest, q, _ | .skipZero rest, q, _
  | .andClean _ _ _ _ _ _ rest, q, _ => append_eval rest q _
def toTempCtx {M : ℕ} : RawSsa M → TempCtx M
  | .done => .hole
  | .x q rest => .seqPre (.x q) (.seqPost rest.toTempCtx (.x q))
  | .cnot c t hct rest => .seqPre (.cnot c t hct) (.seqPost rest.toTempCtx (.cnot c t hct))
  | .skipZero rest => rest.toTempCtx
  | .andClean anc c₁ c₂ h₁₂ hc1a hc2a rest => .tempAnd c₁ c₂ anc h₁₂ hc1a hc2a rest.toTempCtx
theorem toTempCtx_countTempAnd {M : ℕ} : ∀ (p : RawSsa M), p.toTempCtx.countTempAnd = p.countAnd
  | .done => rfl
  | .x _ rest | .cnot _ _ _ rest | .skipZero rest => toTempCtx_countTempAnd rest
  | .andClean _ _ _ _ _ _ rest => congrArg (1 + ·) (toTempCtx_countTempAnd rest)
theorem toTempCtx_fwdBits {M : ℕ} :
    ∀ (p : RawSsa M) (β : BitAssignment M), p.toTempCtx.fwdBits β = p.eval β
  | .done, _ => rfl
  | .x _ rest, _ | .cnot _ _ _ rest, _ =>
      by simp [toTempCtx, TempCtx.fwdBits, CliffProg.eval, eval, toTempCtx_fwdBits rest]
  | .skipZero rest, β => toTempCtx_fwdBits rest β
  | .andClean _ _ _ _ _ _ rest, _ =>
      by simp [toTempCtx, TempCtx.fwdBits, eval, toTempCtx_fwdBits rest]
private theorem wrap_valid {M cur : ℕ} (c : CliffProg M) (K : TempCtx M)
    (hInv : ∀ β : BitAssignment M, c.eval (c.eval β) = β)
    (hPres : ∀ β : BitAssignment M, cleanRem M (M - cur) β → cleanRem M (M - cur) (c.eval β))
    (ihBits : ∀ β : BitAssignment M, cleanRem M (M - cur) β → (K.plug .nil).evalBits β = β)
    (ihVal : ValidCleanRem M (M - cur) (K.plug .nil)) :
    (∀ β : BitAssignment M, cleanRem M (M - cur) β →
      ((TempCtx.seqPre c (.seqPost K c)).plug .nil).evalBits β = β) ∧
    ValidCleanRem M (M - cur) ((TempCtx.seqPre c (.seqPost K c)).plug .nil) := by
  refine ⟨fun β hβ ↦ ?_, ⟨M - cur, Nat.sub_le M cur, trivial,
    ⟨M - cur, Nat.sub_le M cur, ihVal, trivial, fun β₁ hβ₁ ↦ ?_⟩, hPres⟩⟩
  · dsimp only [TempCtx.plug, TempPhaseProg.evalBits]
    rw [ihBits _ (hPres β hβ), hInv]
  · rw [ihBits β₁ hβ₁]
    exact hβ₁
theorem toTempCtx_valid_and_bits {M : ℕ} :
    ∀ (p : RawSsa M) {cur endCur : ℕ},
      Wf cur endCur p →
      endCur ≤ M →
      (∀ β : BitAssignment M, cleanRem M (M - cur) β →
        (p.toTempCtx.plug .nil).evalBits β = β) ∧
      ValidCleanRem M (M - cur) (p.toTempCtx.plug .nil)
  | .done, _, _, _, _ => ⟨fun _ _ ↦ rfl, trivial⟩
  | .x q rest, cur, _, ⟨hq, hwf⟩, hEnd => by
      have hcurM : cur ≤ M := le_trans (le_end hwf) hEnd
      obtain ⟨ihBits, ihVal⟩ := toTempCtx_valid_and_bits rest hwf hEnd
      refine wrap_valid (.x q) rest.toTempCtx
        (fun _ ↦ by simp [CliffProg.eval]) (fun β hβ w hw ↦ ?_) ihBits ihVal
      rw [CliffProg.eval, Function.update_of_ne (Fin.ne_of_val_ne (by omega))]
      exact hβ w hw
  | .cnot c t hct rest, cur, _, ⟨_, ht, hwf⟩, hEnd => by
      have hcurM : cur ≤ M := le_trans (le_end hwf) hEnd
      obtain ⟨ihBits, ihVal⟩ := toTempCtx_valid_and_bits rest hwf hEnd
      refine wrap_valid (.cnot c t hct) rest.toTempCtx
        (fun _ ↦ by simp [CliffProg.eval, hct])
        (fun β hβ w hw ↦ ?_) ihBits ihVal
      rw [CliffProg.eval, Function.update_of_ne (Fin.ne_of_val_ne (by omega))]
      exact hβ w hw
  | .skipZero rest, cur, _, ⟨_, hwf⟩, hEnd => by
      obtain ⟨ihBits, ihVal⟩ := toTempCtx_valid_and_bits rest hwf hEnd
      exact ⟨fun β hβ ↦ ihBits β (fun w hw ↦ hβ w (by omega)), validCleanRem_mono (by omega) ihVal⟩
  | .andClean anc c₁ c₂ h₁₂ hc1a hc2a rest, cur, _, ⟨hanc_val, _, _, hwf⟩, hEnd => by
      have hcur_lt : cur < M := lt_of_lt_of_le (Nat.lt_succ_self cur) (le_trans (le_end hwf) hEnd)
      obtain ⟨ihBits, ihVal⟩ := toTempCtx_valid_and_bits rest hwf hEnd
      refine ⟨fun β hβ ↦ ?_, by omega, by simpa only [hanc_val] using ihVal, fun β₁ hβ₁ ↦ ?_⟩
      · dsimp only [toTempCtx, TempCtx.plug, TempPhaseProg.evalBits]
        rw [ihBits _ fun w hw ↦ by
          rw [Function.update_of_ne (Fin.ne_of_val_ne (by omega))]
          exact hβ w (by omega)]
        simp [hc1a, hc2a]
      · rw [ihBits β₁ (by simpa only [hanc_val] using hβ₁)]
        exact ⟨rfl, rfl, rfl⟩
end RawSsa
structure SsaProg (M : ℕ) (cur endCur : ℕ) where
  raw : RawSsa M
  wf : RawSsa.Wf cur endCur raw
namespace SsaProg
def done {M : ℕ} (cur : ℕ) : SsaProg M cur cur := ⟨.done, rfl⟩
def x {M cur endCur : ℕ} (q : Wire M) (hq : q.val < cur) (rest : SsaProg M cur endCur) :
    SsaProg M cur endCur := ⟨.x q rest.raw, ⟨hq, rest.wf⟩⟩
def cnot {M cur endCur : ℕ} (c t : Wire M) (hct : c ≠ t) (hc : c.val < cur) (ht : t.val < cur)
    (rest : SsaProg M cur endCur) : SsaProg M cur endCur := ⟨.cnot c t hct rest.raw, ⟨hc, ht,
      rest.wf⟩⟩
def skipZero {M cur endCur : ℕ} (hcur : cur < M) (rest : SsaProg M (cur + 1) endCur) : SsaProg
    M cur endCur := ⟨.skipZero rest.raw, ⟨hcur, rest.wf⟩⟩
def andClean {M cur endCur : ℕ} (hcur : cur < M) (c₁ c₂ : Wire M) (h₁₂ : c₁ ≠ c₂)
    (h₁ : c₁.val < cur) (h₂ : c₂.val < cur) (rest : SsaProg M (cur + 1) endCur) : SsaProg M
    cur endCur := ⟨.andClean ⟨cur, hcur⟩ c₁ c₂ h₁₂ (Fin.ne_of_val_ne (ne_of_lt h₁))
      (Fin.ne_of_val_ne (ne_of_lt h₂)) rest.raw, ⟨rfl, h₁, h₂, rest.wf⟩⟩
def countAnd {M cur endCur : ℕ} (p : SsaProg M cur endCur) : ℕ := p.raw.countAnd
@[simp] theorem countAnd_done {M : ℕ} (cur : ℕ) : (done (M := M) cur).countAnd = 0 := rfl
@[simp] theorem countAnd_x {M cur endCur : ℕ} (q : Wire M) (hq : q.val < cur)
    (rest : SsaProg M cur endCur) : (x q hq rest).countAnd = rest.countAnd := rfl
@[simp] theorem countAnd_cnot {M cur endCur : ℕ} (c t : Wire M) (hct : c ≠ t) (hc : c.val < cur)
    (ht : t.val < cur) (rest : SsaProg M cur endCur) :
    (cnot c t hct hc ht rest).countAnd = rest.countAnd := rfl
@[simp] theorem countAnd_skipZero {M cur endCur : ℕ} (hcur : cur < M)
    (rest : SsaProg M (cur + 1) endCur) : (skipZero hcur rest).countAnd = rest.countAnd := rfl
@[simp] theorem countAnd_andClean {M cur endCur : ℕ} (hcur : cur < M) (c₁ c₂ : Wire M)
    (h₁₂ : c₁ ≠ c₂) (h₁ : c₁.val < cur) (h₂ : c₂.val < cur)
    (rest : SsaProg M (cur + 1) endCur) :
    (andClean hcur c₁ c₂ h₁₂ h₁ h₂ rest).countAnd = 1 + rest.countAnd := rfl
def eval {M cur endCur : ℕ} (p : SsaProg M cur endCur) (β : BitAssignment M) : BitAssignment M
    := p.raw.eval β
@[simp] theorem eval_done {M : ℕ} (cur : ℕ) (β : BitAssignment M) :
    (done (M := M) cur).eval β = β := rfl
@[simp] theorem eval_x {M cur endCur : ℕ} (q : Wire M) (hq : q.val < cur)
    (rest : SsaProg M cur endCur) (β : BitAssignment M) :
    (x q hq rest).eval β = rest.eval (Function.update β q (β q + 1)) := rfl
@[simp] theorem eval_cnot {M cur endCur : ℕ} (c t : Wire M) (hct : c ≠ t) (hc : c.val < cur)
    (ht : t.val < cur) (rest : SsaProg M cur endCur) (β : BitAssignment M) :
    (cnot c t hct hc ht rest).eval β = rest.eval (Function.update β t (β t + β c)) := rfl
@[simp] theorem eval_skipZero {M cur endCur : ℕ} (hcur : cur < M)
    (rest : SsaProg M (cur + 1) endCur) (β : BitAssignment M) :
    (skipZero hcur rest).eval β = rest.eval β := rfl
@[simp] theorem eval_andClean {M cur endCur : ℕ} (hcur : cur < M) (c₁ c₂ : Wire M)
    (h₁₂ : c₁ ≠ c₂) (h₁ : c₁.val < cur) (h₂ : c₂.val < cur) (rest : SsaProg M (cur + 1) endCur)
    (β : BitAssignment M) : (andClean hcur c₁ c₂ h₁₂ h₁ h₂ rest).eval β =
      rest.eval (Function.update β ⟨cur, hcur⟩ (β ⟨cur, hcur⟩ + β c₁ * β c₂)) := rfl
def append {M c₁ c₂ c₃ : ℕ} (p : SsaProg M c₁ c₂) (q : SsaProg M c₂ c₃) : SsaProg M c₁ c₃ :=
  ⟨p.raw.append q.raw, RawSsa.append_wf p.wf q.wf⟩
@[simp] theorem append_countAnd {M c₁ c₂ c₃ : ℕ} (p : SsaProg M c₁ c₂) (q : SsaProg M c₂ c₃) :
    (p.append q).countAnd = p.countAnd + q.countAnd := RawSsa.append_countAnd p.raw q.raw
@[simp] theorem append_eval {M c₁ c₂ c₃ : ℕ} (p : SsaProg M c₁ c₂) (q : SsaProg M c₂ c₃)
    (β : BitAssignment M) : (p.append q).eval β = q.eval (p.eval β) :=
  RawSsa.append_eval p.raw q.raw β
def toTempCtx {M cur endCur : ℕ} (p : SsaProg M cur endCur) : TempCtx M := p.raw.toTempCtx
@[simp] theorem toTempCtx_countTempAnd {M cur endCur : ℕ} (p : SsaProg M cur endCur) :
    p.toTempCtx.countTempAnd = p.countAnd := RawSsa.toTempCtx_countTempAnd p.raw
@[simp] theorem toTempCtx_fwdBits {M cur endCur : ℕ} (p : SsaProg M cur endCur)
    (β : BitAssignment M) : p.toTempCtx.fwdBits β = p.eval β :=
  RawSsa.toTempCtx_fwdBits p.raw β
theorem toTempCtx_valid_and_bits {M cur endCur : ℕ} (p : SsaProg M cur endCur)
    (hEnd : endCur ≤ M) : (∀ β : BitAssignment M, cleanRem M (M - cur) β → (p.toTempCtx.plug
    .nil).evalBits β = β) ∧ ValidCleanRem M (M - cur) (p.toTempCtx.plug .nil) :=
  RawSsa.toTempCtx_valid_and_bits p.raw p.wf hEnd
end SsaProg
noncomputable def phaseDiagAct {kAct : ℕ} (pred : BitAssignment kAct → ZMod 2) :
    Unitary (2 ^ kAct) :=
  ⟨Matrix.diagonal (fun x : Fin (2 ^ kAct) ↦ (-1 : ℂ) ^ (pred (basisBits kAct x)).val), by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
      Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    simpa [Pi.star_apply] using MomSlots01Slot1ProjKinetic.neg_one_pow_bit_mul_self _⟩
noncomputable def compileSsaCzDyn {Var : Type} {n kAct mClean mWork : ℕ} (v : Var)
    (rAct : QRegister kAct n) (rWork : QRegister mWork n) (hdisj : rAct.DisjointWires rWork)
    (hw_len : mClean ≤ mWork) (p : SsaProg (kAct + mClean) kAct (kAct + mClean))
    (wPhi wCoin : Wire (kAct + mClean)) (hne : wPhi ≠ wCoin) : DynamicCircuit Var n :=
  let rSub : QRegister mClean n := rWork.slice 0 mClean (by omega)
  let rComb : QRegister (kAct + mClean) n := rAct.concat rSub (hdisj.compose_right _)
  let inner : DynamicCircuit Var n :=
    .circuit (czCircuit (rComb wPhi) (rComb wCoin) (rComb.wires.injective.ne hne))
  toDynWithDyn v rComb inner p.toTempCtx
theorem compileSsaCzDyn_count_toff {Var : Type} {n kAct mClean mWork : ℕ}
    (v : Var) (rAct : QRegister kAct n) (rWork : QRegister mWork n)
    (hdisj : rAct.DisjointWires rWork) (hw_len : mClean ≤ mWork)
    (p : SsaProg (kAct + mClean) kAct (kAct + mClean))
    (wPhi wCoin : Wire (kAct + mClean)) (hne : wPhi ≠ wCoin) :
    (compileSsaCzDyn v rAct rWork hdisj hw_len p wPhi wCoin hne).count PrimitiveGate.TOFF = 0 := by
  dsimp only [compileSsaCzDyn]
  exact toDynWithDyn_count_toff v _ _ (by simp [DynamicCircuit.count, czCircuit_count_toff])
    p.toTempCtx
theorem compileSsaCzDyn_count_t {Var : Type} {n kAct mClean mWork : ℕ} (v : Var)
    (rAct : QRegister kAct n) (rWork : QRegister mWork n) (hdisj : rAct.DisjointWires rWork)
    (hw_len : mClean ≤ mWork) (p : SsaProg (kAct + mClean) kAct (kAct + mClean))
    (wPhi wCoin : Wire (kAct + mClean)) (hne : wPhi ≠ wCoin) :
    (compileSsaCzDyn v rAct rWork hdisj hw_len p wPhi wCoin hne).count PrimitiveGate.T = 4 *
    p.countAnd := by
  dsimp only [compileSsaCzDyn]
  rw [toDynWithDyn_count_t]
  change 4 * p.toTempCtx.countTempAnd + (czCircuit _ _ _).count PrimitiveGate.T = 4 * p.countAnd
  rw [czCircuit_count_t, add_zero, p.toTempCtx_countTempAnd]
def PreservesOutside {M : ℕ} (lo hi : ℕ) (f : BitAssignment M → BitAssignment M) : Prop :=
  ∀ (β : BitAssignment M) (w : Wire M),(w.val < lo ∨ hi ≤ w.val) → f β w = β w
theorem PreservesOutside.comp {M : ℕ} {c₁ c₂ c₃ : ℕ} (h₁₂ : c₁ ≤ c₂) (h₂₃ : c₂ ≤ c₃)
    {f g : BitAssignment M → BitAssignment M} (hf : PreservesOutside c₁ c₂ f)
    (hg : PreservesOutside c₂ c₃ g) : PreservesOutside c₁ c₃ (fun β ↦ g (f β)) :=
  fun β w hw ↦ hw.elim
    (fun h ↦ (hg (f β) w (Or.inl (lt_of_lt_of_le h h₁₂))).trans (hf β w (Or.inl h)))
    (fun h ↦ (hg (f β) w (Or.inr h)).trans (hf β w (Or.inr (le_trans h₂₃ h))))
def b2z (b : Bool) : ZMod 2 := if b then 1 else 0
def xorListInto {M : ℕ} (cur : ℕ) (hcur : cur < M) :
    List (Bool × { w : Wire M // w.val < cur }) → SsaProg M (cur + 1) (cur + 1)
  | [] => .done (cur + 1)
  | (en, ⟨w, hw⟩) :: tl =>
      if en then .cnot w ⟨cur, hcur⟩ (Fin.ne_of_val_ne (ne_of_lt hw))
        (Nat.lt_succ_of_lt hw) (Nat.lt_succ_self cur) (xorListInto cur hcur tl)
      else xorListInto cur hcur tl
def listXorSum {M : ℕ} (cur : ℕ) (β : BitAssignment M) :
    List (Bool × { w : Wire M // w.val < cur }) → ZMod 2
  | [] => 0
  | (en, ⟨w, _⟩) :: tl => (if en then β w else 0) + listXorSum cur β tl
@[simp] theorem xorListInto_countAnd {M : ℕ} (cur : ℕ) (hcur : cur < M) :
    ∀ ls, (xorListInto cur hcur ls).countAnd = 0
  | [] => rfl
  | (false, ⟨_, _⟩) :: tl | (true, ⟨_, _⟩) :: tl => xorListInto_countAnd cur hcur tl
private theorem xorSum_upd {M : ℕ} (cur : ℕ) (hcur : cur < M)
    (β : BitAssignment M) (v : ZMod 2) :
    ∀ ls, listXorSum cur (Function.update β ⟨cur, hcur⟩ v) ls = listXorSum cur β ls
  | [] => rfl
  | (_, ⟨_, hw⟩) :: tl => by
      dsimp only [listXorSum]
      rw [Function.update_of_ne (Fin.ne_of_val_ne (ne_of_lt hw)),
        xorSum_upd cur hcur β v tl]
theorem xorListInto_eval {M : ℕ} (cur : ℕ) (hcur : cur < M) :
    ∀ (ls : List (Bool × { w : Wire M // w.val < cur })) (β : BitAssignment M),
      (xorListInto cur hcur ls).eval β =
        Function.update β ⟨cur, hcur⟩ (β ⟨cur, hcur⟩ + listXorSum cur β ls)
  | [], β => by simp [xorListInto, listXorSum]
  | (false, _) :: tl, β => by
      simpa [xorListInto, listXorSum] using xorListInto_eval cur hcur tl β
  | (true, ⟨w, _⟩) :: tl, β => by
      simp [xorListInto, listXorSum, xorListInto_eval cur hcur tl,
        xorSum_upd, add_assoc]
def writeXor {M : ℕ} (cur : ℕ) (hcur : cur < M) (c0 : Bool)
    (ls : List (Bool × { w : Wire M // w.val < cur })) : SsaProg M cur (cur + 1) :=
  .skipZero hcur <|
    if c0 then .x ⟨cur, hcur⟩ (Nat.lt_succ_self cur) (xorListInto cur hcur ls)
    else xorListInto cur hcur ls
@[simp] theorem writeXor_countAnd {M : ℕ} (cur : ℕ) (hcur : cur < M) (c0 : Bool)
    (ls : List (Bool × { w : Wire M // w.val < cur })) :
    (writeXor cur hcur c0 ls).countAnd = 0 := by
  cases c0
  · simp [writeXor]
  · simp [writeXor]
theorem writeXor_eval {M : ℕ} (cur : ℕ) (hcur : cur < M) (c0 : Bool)
    (ls : List (Bool × { w : Wire M // w.val < cur })) (β : BitAssignment M)
    (hz : β ⟨cur, hcur⟩ = 0) : (writeXor cur hcur c0 ls).eval β = Function.update β
    ⟨cur, hcur⟩ (b2z c0 + listXorSum cur β ls) := by
  cases c0
  · simp [writeXor, b2z, xorListInto_eval, hz]
  · simp [writeXor, b2z, xorListInto_eval, xorSum_upd, hz]
def andPol {M : ℕ} (cur : ℕ) (hcur : cur < M) (c₁ c₂ : Wire M) (h₁₂ : c₁ ≠ c₂)
    (h₁ : c₁.val < cur) (h₂ : c₂.val < cur) (pol₁ pol₂ : Bool) : SsaProg M cur (cur + 1) :=
  let post : SsaProg M (cur + 1) (cur + 1) :=
    match pol₁, pol₂ with
    | false, false => .done (cur + 1)
    | false, true => .x c₂ (Nat.lt_succ_of_lt h₂) (.done (cur + 1))
    | true, false => .x c₁ (Nat.lt_succ_of_lt h₁) (.done (cur + 1))
    | true, true => .x c₂ (Nat.lt_succ_of_lt h₂) (.x c₁ (Nat.lt_succ_of_lt h₁) (.done (cur + 1)))
  let core : SsaProg M cur (cur + 1) := .andClean hcur c₁ c₂ h₁₂ h₁ h₂ post
  match pol₁, pol₂ with
  | false, false => core
  | false, true => .x c₂ h₂ core
  | true, false => .x c₁ h₁ core
  | true, true => .x c₁ h₁ (.x c₂ h₂ core)
@[simp] theorem andPol_countAnd {M : ℕ} (cur : ℕ) (hcur : cur < M) (c₁ c₂ : Wire M)
    (h₁₂ : c₁ ≠ c₂) (h₁ : c₁.val < cur) (h₂ : c₂.val < cur) (pol₁ pol₂ : Bool) :
    (andPol cur hcur c₁ c₂ h₁₂ h₁ h₂ pol₁ pol₂).countAnd = 1 := by
  cases pol₁ <;> cases pol₂ <;> rfl
private theorem pol_eval_gen {M : ℕ} (cur : ℕ) (hcur : cur < M) (c₁ c₂ : Wire M)
    (h₁₂ : c₁ ≠ c₂) (h₁ : c₁.val < cur) (h₂ : c₂.val < cur) (pol₁ pol₂ : Bool)
    (β : BitAssignment M) :
    (andPol cur hcur c₁ c₂ h₁₂ h₁ h₂ pol₁ pol₂).eval β =
      Function.update β ⟨cur, hcur⟩
        (β ⟨cur, hcur⟩ + (β c₁ + b2z pol₁) * (β c₂ + b2z pol₂)) := by
  have hc1a : c₁ ≠ ⟨cur, hcur⟩ := Fin.ne_of_val_ne (ne_of_lt h₁)
  have hc2a : c₂ ≠ ⟨cur, hcur⟩ := Fin.ne_of_val_ne (ne_of_lt h₂)
  have hx (q : Wire M) (hq : q ≠ ⟨cur, hcur⟩) (v : ZMod 2) (γ : BitAssignment M) :
      Function.update (Function.update (Function.update γ q (γ q + 1)) ⟨cur, hcur⟩
        (Function.update γ q (γ q + 1) ⟨cur, hcur⟩ + v)) q
        (Function.update (Function.update γ q (γ q + 1)) ⟨cur, hcur⟩
          (Function.update γ q (γ q + 1) ⟨cur, hcur⟩ + v) q + 1) =
      Function.update γ ⟨cur, hcur⟩ (γ ⟨cur, hcur⟩ + v) := by
    funext w
    by_cases hw : w = ⟨cur, hcur⟩
    · simp [hw, hq.symm]
    · by_cases hwq : w = q
      · simp [hwq, hq]
      · simp [hw, hwq]
  cases pol₁
  · cases pol₂
    · simp [andPol, b2z]
    · dsimp only [andPol, SsaProg.eval_x, SsaProg.eval_andClean, SsaProg.eval_done]
      rw [hx c₂ hc2a _ β]
      simp [b2z, h₁₂]
  · cases pol₂
    · dsimp only [andPol, SsaProg.eval_x, SsaProg.eval_andClean, SsaProg.eval_done]
      rw [hx c₁ hc1a _ β]
      simp [b2z, h₁₂.symm]
    · dsimp only [andPol, SsaProg.eval_x, SsaProg.eval_andClean, SsaProg.eval_done]
      rw [hx c₂ hc2a _ (Function.update β c₁ (β c₁ + 1)), hx c₁ hc1a _ β]
      simp [b2z, h₁₂, h₁₂.symm]
theorem andPol_eval {M : ℕ} (cur : ℕ) (hcur : cur < M) (c₁ c₂ : Wire M) (h₁₂ : c₁ ≠ c₂)
    (h₁ : c₁.val < cur) (h₂ : c₂.val < cur) (pol₁ pol₂ : Bool) (β : BitAssignment M)
    (hz : β ⟨cur, hcur⟩ = 0) : (andPol cur hcur c₁ c₂ h₁₂ h₁ h₂ pol₁ pol₂).eval β =
    Function.update β ⟨cur, hcur⟩ ((β c₁ + b2z pol₁) * (β c₂ + b2z pol₂)) := by
  rw [pol_eval_gen, hz, zero_add]
theorem writeXor_preserves {M : ℕ} (cur : ℕ) (hcur : cur < M) (c0 : Bool)
    (ls : List (Bool × { w : Wire M // w.val < cur })) :
    PreservesOutside cur (cur + 1) (writeXor cur hcur c0 ls).eval := by
  intro β w hw
  have hne : w ≠ ⟨cur, hcur⟩ := Fin.ne_of_val_ne (show w.val ≠ cur by omega)
  dsimp only [writeXor, SsaProg.eval_skipZero]
  split_ifs
  · simp [xorListInto_eval, Function.update_of_ne hne]
  · simp [xorListInto_eval, Function.update_of_ne hne]
theorem andPol_preserves {M : ℕ} (cur : ℕ) (hcur : cur < M) (c₁ c₂ : Wire M) (h₁₂ : c₁ ≠ c₂)
    (h₁ : c₁.val < cur) (h₂ : c₂.val < cur) (pol₁ pol₂ : Bool) : PreservesOutside cur
    (cur + 1) (andPol cur hcur c₁ c₂ h₁₂ h₁ h₂ pol₁ pol₂).eval := fun β w hw ↦ by
  rw [pol_eval_gen,
    Function.update_of_ne (Fin.ne_of_val_ne (show w.val ≠ cur by omega))]
def muxBit {M : ℕ} (cur : ℕ) (hcur : cur < M) (sel x₀ x₁ : Wire M) (hs1 : sel ≠ x₁)
    (h01 : x₀ ≠ x₁) (hsel : sel.val < cur) (hx0 : x₀.val < cur) (hx1 : x₁.val < cur) : SsaProg
    M cur (cur + 1) :=
  let out : Wire M := ⟨cur, hcur⟩
  .cnot x₀ x₁ h01 hx0 hx1 <|
    .andClean hcur sel x₁ hs1 hsel hx1 <|
      .cnot x₀ x₁ h01 (Nat.lt_succ_of_lt hx0) (Nat.lt_succ_of_lt hx1) <|
        .cnot x₀ out (Fin.ne_of_val_ne (ne_of_lt hx0))
          (Nat.lt_succ_of_lt hx0) (Nat.lt_succ_self cur) <|
          .done (cur + 1)
@[simp] theorem muxBit_countAnd {M : ℕ} (cur : ℕ) (hcur : cur < M)
    (sel x₀ x₁ : Wire M) (hs1 : sel ≠ x₁) (h01 : x₀ ≠ x₁)
    (hsel : sel.val < cur) (hx0 : x₀.val < cur) (hx1 : x₁.val < cur) :
    (muxBit cur hcur sel x₀ x₁ hs1 h01 hsel hx0 hx1).countAnd = 1 := rfl
private theorem bit_eval_gen {M : ℕ} (cur : ℕ) (hcur : cur < M) (sel x₀ x₁ : Wire M)
    (hs1 : sel ≠ x₁) (h01 : x₀ ≠ x₁) (hsel : sel.val < cur) (hx0 : x₀.val < cur)
    (hx1 : x₁.val < cur) (β : BitAssignment M) :
    (muxBit cur hcur sel x₀ x₁ hs1 h01 hsel hx0 hx1).eval β =
      Function.update β ⟨cur, hcur⟩ (β ⟨cur, hcur⟩ + β sel * (β x₁ + β x₀) + β x₀) := by
  have h0o : x₀ ≠ ⟨cur, hcur⟩ := Fin.ne_of_val_ne (ne_of_lt hx0)
  have h1o : x₁ ≠ ⟨cur, hcur⟩ := Fin.ne_of_val_ne (ne_of_lt hx1)
  funext w
  by_cases hw : w = ⟨cur, hcur⟩
  · subst hw
    simp [muxBit, h1o.symm, h0o, hs1, h01]
  · rw [Function.update_of_ne hw]
    by_cases hw1 : w = x₁
    · subst hw1
      simp [muxBit, h1o, h0o, h01]
    · simp [muxBit, hw, hw1]
theorem muxBit_eval {M : ℕ} (cur : ℕ) (hcur : cur < M) (sel x₀ x₁ : Wire M) (hs1 : sel ≠ x₁)
    (h01 : x₀ ≠ x₁) (hsel : sel.val < cur) (hx0 : x₀.val < cur) (hx1 : x₁.val < cur)
    (β : BitAssignment M) (hz : β ⟨cur, hcur⟩ = 0) :
    (muxBit cur hcur sel x₀ x₁ hs1 h01 hsel hx0 hx1).eval β = Function.update β ⟨cur, hcur⟩
    (if β sel = 1 then β x₁ else β x₀) := by
  have halg : ∀ s a b : ZMod 2, 0 + s * (b + a) + a = if s = 1 then b else a := by decide
  rw [bit_eval_gen, hz, halg]
theorem muxBit_preserves {M : ℕ} (cur : ℕ) (hcur : cur < M)
    (sel x₀ x₁ : Wire M) (hs1 : sel ≠ x₁) (h01 : x₀ ≠ x₁)
    (hsel : sel.val < cur) (hx0 : x₀.val < cur) (hx1 : x₁.val < cur) :
    PreservesOutside cur (cur + 1) (muxBit cur hcur sel x₀ x₁ hs1 h01 hsel hx0 hx1).eval :=
  fun β w hw ↦ by
    rw [bit_eval_gen,
      Function.update_of_ne (Fin.ne_of_val_ne (show w.val ≠ cur by omega))]
def qqLtStep {M : ℕ} (cur : ℕ) (hcur : cur < M) (u_j thr_j prev_lt : Wire M)
    (hut : u_j ≠ thr_j) (hpt : prev_lt ≠ thr_j) (_hpu : prev_lt ≠ u_j) (hu : u_j.val < cur)
    (ht : thr_j.val < cur) (hp : prev_lt.val < cur) : SsaProg M cur (cur + 1) :=
  let out : Wire M := ⟨cur, hcur⟩
  .cnot thr_j u_j hut.symm ht hu <|
    .cnot prev_lt thr_j hpt hp ht <|
      .andClean hcur u_j thr_j hut hu ht <|
        .cnot prev_lt thr_j hpt (Nat.lt_succ_of_lt hp) (Nat.lt_succ_of_lt ht) <|
          .cnot thr_j u_j hut.symm (Nat.lt_succ_of_lt ht) (Nat.lt_succ_of_lt hu) <|
            .cnot prev_lt out (Fin.ne_of_val_ne (by dsimp [out]; omega))
              (Nat.lt_succ_of_lt hp) (Nat.lt_succ_self cur) <|
              .done (cur + 1)
@[simp] theorem qqLtStep_countAnd {M : ℕ} (cur : ℕ) (hcur : cur < M)
    (u_j thr_j prev_lt : Wire M) (hut : u_j ≠ thr_j) (hpt : prev_lt ≠ thr_j)
    (hpu : prev_lt ≠ u_j) (hu : u_j.val < cur) (ht : thr_j.val < cur) (hp : prev_lt.val < cur)
    : (qqLtStep cur hcur u_j thr_j prev_lt hut hpt hpu hu ht hp).countAnd = 1 := rfl
private theorem ltStep_eval_gen {M : ℕ} (cur : ℕ) (hcur : cur < M)
    (u_j thr_j prev_lt : Wire M) (hut : u_j ≠ thr_j) (hpt : prev_lt ≠ thr_j)
    (hpu : prev_lt ≠ u_j) (hu : u_j.val < cur) (ht : thr_j.val < cur) (hp : prev_lt.val < cur)
    (β : BitAssignment M) :
    (qqLtStep cur hcur u_j thr_j prev_lt hut hpt hpu hu ht hp).eval β =
      Function.update β ⟨cur, hcur⟩
        (β ⟨cur, hcur⟩ + (β u_j + β thr_j) * (β thr_j + β prev_lt) + β prev_lt) := by
  have huo : u_j ≠ ⟨cur, hcur⟩ := Fin.ne_of_val_ne (ne_of_lt hu)
  have hto : thr_j ≠ ⟨cur, hcur⟩ := Fin.ne_of_val_ne (ne_of_lt ht)
  have hpo : prev_lt ≠ ⟨cur, hcur⟩ := Fin.ne_of_val_ne (ne_of_lt hp)
  funext w
  by_cases hw : w = ⟨cur, hcur⟩
  · subst hw
    simp [qqLtStep, huo, huo.symm, hto, hto.symm, hpo, hut, hut.symm, hpt, hpu]
  · rw [Function.update_of_ne hw]
    by_cases hwu : w = u_j
    · subst hwu
      simp [qqLtStep, huo, hto, hpo, hut, hut.symm, hpt, hpu]
    · by_cases hwt : w = thr_j
      · subst hwt
        simp [qqLtStep, huo, hto, hpo, hut, hut.symm, hpt, hpu]
      · simp [qqLtStep, hw, hwu, hwt]
theorem qqLtStep_eval {M : ℕ} (cur : ℕ) (hcur : cur < M) (u_j thr_j prev_lt : Wire M)
    (hut : u_j ≠ thr_j) (hpt : prev_lt ≠ thr_j) (hpu : prev_lt ≠ u_j) (hu : u_j.val < cur)
    (ht : thr_j.val < cur) (hp : prev_lt.val < cur) (β : BitAssignment M)
    (hz : β ⟨cur, hcur⟩ = 0) : (qqLtStep cur hcur u_j thr_j prev_lt hut hpt hpu hu ht hp).eval
    β = Function.update β ⟨cur, hcur⟩ (if β u_j = β thr_j then β prev_lt else β thr_j) := by
  have halg : ∀ u t p : ZMod 2, 0 + (u + t) * (t + p) + p = if u = t then p else t := by decide
  rw [ltStep_eval_gen, hz, halg]
theorem qqLtStep_preserves {M : ℕ} (cur : ℕ) (hcur : cur < M) (u_j thr_j prev_lt : Wire M)
    (hut : u_j ≠ thr_j) (hpt : prev_lt ≠ thr_j) (hpu : prev_lt ≠ u_j) (hu : u_j.val < cur)
    (ht : thr_j.val < cur) (hp : prev_lt.val < cur) : PreservesOutside cur (cur + 1)
    (qqLtStep cur hcur u_j thr_j prev_lt hut hpt hpu hu ht hp).eval := fun β w hw ↦ by
  rw [ltStep_eval_gen,
    Function.update_of_ne (Fin.ne_of_val_ne (show w.val ≠ cur by omega))]
def sliceVal {M : ℕ} (β : BitAssignment M) (base : ℕ) : (n : ℕ) → (h : base + n ≤ M) → ℕ
  | 0, _ => 0
  | n + 1, h =>
      sliceVal β base n (by omega) + (β ⟨base + n, by omega⟩).val * 2 ^ n
theorem sliceVal_congr {M : ℕ} {β₁ β₂ : BitAssignment M} {base : ℕ} :
    ∀ (n : ℕ) (h : base + n ≤ M),
      (∀ (j : ℕ) (_ : j < n), β₁ ⟨base + j, by omega⟩ = β₂ ⟨base + j, by omega⟩) →
      sliceVal β₁ base n h = sliceVal β₂ base n h
  | 0, _, _ => rfl
  | n + 1, h, heq => by
      dsimp only [sliceVal]
      rw [sliceVal_congr n (by omega) (fun j hj ↦ heq j (Nat.lt_succ_of_lt hj)),
        heq n (Nat.lt_succ_self n)]
theorem sliceVal_lt_two_pow {M : ℕ} (β : BitAssignment M) (base : ℕ) :
    ∀ (n : ℕ) (h : base + n ≤ M), sliceVal β base n h < 2 ^ n
  | 0, _ => by simp [sliceVal]
  | n + 1, h => by
      dsimp only [sliceVal]
      have h1 := sliceVal_lt_two_pow β base n (by omega)
      have h2 := ZMod.val_lt (β ⟨base + n, by omega⟩)
      rcases (by omega : (β ⟨base + n, by omega⟩).val = 0 ∨
          (β ⟨base + n, by omega⟩).val = 1) with h0 | h1'
      · rw [h0, Nat.pow_succ]
        omega
      · rw [h1', Nat.pow_succ]
        omega
theorem nat_lt_step_msb {u0 t0 b_u b_t n : ℕ} (hu : u0 < 2 ^ n) (ht : t0 < 2 ^ n)
    (hbu : b_u < 2) (hbt : b_t < 2) : (u0 + b_u * 2 ^ n < t0 + b_t * 2 ^ n) ↔
    (if b_u = b_t then u0 < t0 else b_t = 1) := by
  rcases (by omega : b_u = 0 ∨ b_u = 1) with rfl | rfl
  · rcases (by omega : b_t = 0 ∨ b_t = 1) with rfl | rfl
    · simp
    · simp
      omega
  · rcases (by omega : b_t = 0 ∨ b_t = 1) with rfl | rfl
    · simp
      omega
    · simp
theorem nat_mod_two_pow_succ (K n : ℕ) :
    K % 2 ^ (n + 1) = K % 2 ^ n + (if K.testBit n then 1 else 0) * 2 ^ n := by
  have hpow : 2 ^ (n + 1) = 2 ^ n * 2 := by ring
  have hda := Nat.div_add_mod (K % 2 ^ (n + 1)) (2 ^ n)
  rw [hpow, Nat.mod_mul_right_div_self, Nat.mod_mul_right_mod] at hda
  rw [Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.and_comm 1, Nat.and_one_is_mod, hpow, ← hda]
  rcases (by omega : (K / 2 ^ n) % 2 = 0 ∨ (K / 2 ^ n) % 2 = 1) with hm | hm
  · simp only [hm, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
    ring
  · rw [hm]
    norm_num
    ring
abbrev slot1GeomWorkWires : ℕ := 231
noncomputable def slot1QuadBranchWeight : ℝ :=
  ((16129 / 2 : ℝ) * (gridKappa ^ 2 / 2)) / projectileMass
noncomputable def slot1LinBranchWeight (cfg : Configuration) (w : Fin 3) : ℝ :=
  (127 * gridKappa * |waveVector cfg.projectileMomentum w|) / projectileMass
noncomputable def slot1BranchWeight (cfg : Configuration) : Fin 6 → ℝ
  | 0 => slot1QuadBranchWeight
  | 1 => slot1LinBranchWeight cfg 0
  | 2 => slot1QuadBranchWeight
  | 3 => slot1LinBranchWeight cfg 1
  | 4 => slot1QuadBranchWeight
  | 5 => slot1LinBranchWeight cfg 2
noncomputable def slot1Delta (cfg : Configuration) (b : Fin 6) : ℕ :=
  ⌊(2 : ℝ) ^ 29 * (slot1BranchWeight cfg b / lambdaSlot1TpHi) + (1 / 2 : ℝ)⌋₊
noncomputable def slot1Tau (cfg : Configuration) (k : Fin 7) : ℕ :=
  ∑ b : Fin 6, if b.val < k.val then slot1Delta cfg b else 0
noncomputable def slot1Sigma (cfg : Configuration) (w : Fin 3) : Bool :=
  decide (0 ≤ waveVector cfg.projectileMomentum w)
def prioEval (f : ℕ → ZMod 2) : (k : ℕ) → BitAssignment k → ZMod 2
  | 0, _ => 0
  | k + 1, α => if α ⟨k, Nat.lt_succ_self k⟩ = 1 then f k
      else prioEval f k (fun i ↦ α ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)
def idxMagR (t : ℕ) : Fin 7 := if t = 0 then 6 else ⟨(t - 1) % 7, Nat.mod_lt _ (by decide)⟩
def idxMagS (t : ℕ) : Fin 7 := ⟨t % 7, Nat.mod_lt _ (by decide)⟩
def carryBool (u8 : Fin 8 → ZMod 2) : ℕ → ZMod 2
  | 0 => u8 7
  | k + 1 => if hk : k < 8 then carryBool u8 k * (u8 ⟨k, hk⟩ + 1) else 0
attribute [local irreducible]
  writeXor muxBit andPol
theorem sum_fin6_nat (f : Fin 6 → ℕ) :
    (∑ b : Fin 6, f b) = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 := by
  rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc, Fin.sum_univ_four]
  rfl
theorem sum_fin6_real (f : Fin 6 → ℝ) :
    (∑ b : Fin 6, f b) = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 := by
  rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc, Fin.sum_univ_four]
  rfl
theorem sum_fin7_nat (f : Fin 7 → ℕ) :
    (∑ b : Fin 7, f b) = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 := by
  rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc, Fin.sum_univ_castSucc, Fin.sum_univ_four]
  rfl
theorem slot1BranchWeight_nonneg (cfg : Configuration) (b : Fin 6) :
    0 ≤ slot1BranchWeight cfg b := by
  have hm : (0 : ℝ) < projectileMass := by norm_num [projectileMass]
  have hl (w : Fin 3) : 0 ≤ slot1LinBranchWeight cfg w :=
    div_nonneg (mul_nonneg (mul_nonneg (by norm_num) gridKappa_nonneg) (abs_nonneg _)) hm.le
  match b with
  | ⟨0, _⟩ | ⟨2, _⟩ | ⟨4, _⟩ =>
      dsimp [slot1BranchWeight, slot1QuadBranchWeight]
      positivity
  | ⟨1, _⟩ => exact hl 0
  | ⟨3, _⟩ => exact hl 1
  | ⟨5, _⟩ => exact hl 2
theorem sum_slot1BranchWeight_eq (cfg : Configuration) :
    (∑ b : Fin 6, slot1BranchWeight cfg b) = projLiteralPrepWeight cfg := by
  unfold projLiteralPrepWeight
  rw [sum_fin6_real, Fin.sum_univ_three]
  dsimp [slot1BranchWeight, slot1QuadBranchWeight, slot1LinBranchWeight]
  ring
theorem slot1Tau_mono (cfg : Configuration) {i j : Fin 7} (hij : i.val ≤ j.val) :
    slot1Tau cfg i ≤ slot1Tau cfg j :=
  Finset.sum_le_sum fun b _ ↦ by
    by_cases h1 : b.val < i.val
    · simp [h1, lt_of_lt_of_le h1 hij]
    · simp [h1]
theorem slot1Tau_zero (cfg : Configuration) : slot1Tau cfg 0 = 0 := rfl
theorem slot1Tau_succ_eq (cfg : Configuration) (b : Fin 6) :
    slot1Tau cfg ⟨b.val + 1, by omega⟩ = slot1Tau cfg ⟨b.val, by omega⟩ + slot1Delta cfg b := by
  match b with
  | ⟨0, _⟩ | ⟨1, _⟩ | ⟨2, _⟩ | ⟨3, _⟩ | ⟨4, _⟩ | ⟨5, _⟩ =>
      simp [slot1Tau, sum_fin6_nat, Nat.add_assoc]
  | ⟨_ + 6, h⟩ => omega
theorem slot1Tau_six_lt_two_pow_29 (cfg : Configuration) : slot1Tau cfg 6 < 2 ^ 29 := by
  have htight : projLiteralPrepWeight cfg ≤ 41496756 / 100000 := by
    unfold projLiteralPrepWeight
    have h1 := mul_le_mul gridKappa_le_ratHi (sum_abs_stepVector_projectileMomentum_le cfg)
      (Finset.sum_nonneg fun _ _ ↦ abs_nonneg _) (by unfold gridKappaRatHi; positivity)
    have h2 := kappaSqHalf_le_ratHi
    unfold gridKappaRatHi at h1 h2
    unfold projectileMass
    norm_num at h1 h2 ⊢
    linarith
  have hlam : (0 : ℝ) < lambdaSlot1TpHi := by norm_num [lambdaSlot1TpHi]
  have hsum : (∑ b : Fin 6, (slot1Delta cfg b : ℝ)) ≤
      (2 : ℝ) ^ 29 * (projLiteralPrepWeight cfg / lambdaSlot1TpHi) + 3 :=
    (Finset.sum_le_sum fun b _ ↦ Nat.floor_le (by
      have := slot1BranchWeight_nonneg cfg b
      positivity)).trans_eq (by
      rw [← sum_slot1BranchWeight_eq cfg, sum_fin6_real, sum_fin6_real]
      ring)
  exact_mod_cast (show (slot1Tau cfg 6 : ℝ) < ((2 ^ 29 : ℕ) : ℝ) by
    rw [show slot1Tau cfg 6 = ∑ b : Fin 6, slot1Delta cfg b by simp [slot1Tau, sum_fin6_nat]]
    push_cast
    unfold lambdaSlot1TpHi at hsum
    norm_num at hsum ⊢
    linarith)
theorem PreservesOutside.clean_above {M lo hi : ℕ} {f : BitAssignment M → BitAssignment M}
    (hf : PreservesOutside lo hi f) {β : BitAssignment M}
    (hz : ∀ w : Wire M, lo ≤ w.val → β w = 0) (hle : lo ≤ hi) :
    ∀ w : Wire M, hi ≤ w.val → f β w = 0 :=
  fun w hw ↦ (hf β w (Or.inr hw)).trans (hz w (le_trans hle hw))
theorem PreservesOutside.keep_lt {M lo hi : ℕ} {f : BitAssignment M → BitAssignment M}
    (hf : PreservesOutside lo hi f) (β : BitAssignment M) (w : Wire M) (hw : w.val < lo) :
    f β w = β w := hf β w (Or.inl hw)
theorem sliceVal_eq_of_testBit {M : ℕ} (β : BitAssignment M) (base K : ℕ) :
    ∀ (n : ℕ) (h : base + n ≤ M),
      (∀ (j : ℕ) (_ : j < n), β ⟨base + j, by omega⟩ = b2z (K.testBit j)) →
      sliceVal β base n h = K % 2 ^ n
  | 0, _, _ => (Nat.mod_one K).symm
  | n + 1, _, hbits => by
      dsimp only [sliceVal]
      rw [sliceVal_eq_of_testBit β base K n (by omega)
        (fun j hj ↦ hbits j (Nat.lt_succ_of_lt hj)),
        hbits n (Nat.lt_succ_self n), nat_mod_two_pow_succ K n]
      cases K.testBit n
      · rfl
      · rfl
theorem sliceVal_eq_sum {M : ℕ} (β : BitAssignment M) (base : ℕ) :
    ∀ (n : ℕ) (h : base + n ≤ M),
      sliceVal β base n h = ∑ j : Fin n, (β ⟨base + j.val, by omega⟩).val * 2 ^ j.val
  | 0, _ => rfl
  | n + 1, _ => by
      dsimp only [sliceVal]
      rw [Fin.sum_univ_castSucc, sliceVal_eq_sum β base n (by omega)]
      rfl
def u8FromFin (u : Fin 256) (b : Fin 8) : ZMod 2 := b2z (u.val.testBit b.val)
def mag7Bit (u8 : Fin 8 → ZMod 2) (b : Fin 7) : ZMod 2 :=
  if b.val = 0 then u8 0
  else u8 ⟨b.val, by omega⟩ + u8 7 + carryBool u8 b.val
def mag7Nat (u8 : Fin 8 → ZMod 2) : ℕ := (mag7Bit u8 0).val + (mag7Bit u8 1).val * 2 +
    (mag7Bit u8 2).val * 4 + (mag7Bit u8 3).val * 8 + (mag7Bit u8 4).val * 16 +
    (mag7Bit u8 5).val * 32 + (mag7Bit u8 6).val * 64
theorem mag7Nat_eq_sum (u8 : Fin 8 → ZMod 2) :
    (∑ b : Fin 7, (mag7Bit u8 b).val * 2 ^ b.val) = mag7Nat u8 := by
  rw [sum_fin7_nat]
  dsimp [mag7Nat]
  omega
theorem mag7Nat_u8FromFin_spec (u : Fin 256) : mag7Nat (u8FromFin u) ≤ 127 ∧ (if u8FromFin u 7
    = 1 then -(mag7Nat (u8FromFin u) : ℤ) else (mag7Nat (u8FromFin u) : ℤ)) = slot1AxisInt u ∧
    ((mag7Nat (u8FromFin u) : ℤ) ^ 2) = (slot1AxisInt u) ^ 2 := by
  have h16 : ∀ a b : Fin 16,
      let w : Fin 256 := ⟨16 * a.val + b.val, by omega⟩
      mag7Nat (u8FromFin w) ≤ 127 ∧
      (if u8FromFin w 7 = 1 then -(mag7Nat (u8FromFin w) : ℤ)
       else (mag7Nat (u8FromFin w) : ℤ)) = slot1AxisInt w ∧
      ((mag7Nat (u8FromFin w) : ℤ) ^ 2) = (slot1AxisInt w) ^ 2 := by decide
  have hu : u = ⟨16 * (u.val / 16) + u.val % 16, by omega⟩ :=
    Fin.ext (Nat.div_add_mod u.val 16).symm
  rw [hu]
  exact h16 ⟨u.val / 16, by omega⟩ ⟨u.val % 16, by omega⟩
noncomputable def slot1BranchIdx (cfg : Configuration) (uBr : ℕ) : Fin 7 := if uBr < slot1Tau
    cfg 1 then 0 else if uBr < slot1Tau cfg 2 then 1 else if uBr < slot1Tau cfg 3 then 2 else
    if uBr < slot1Tau cfg 4 then 3 else if uBr < slot1Tau cfg 5 then 4 else if uBr < slot1Tau
    cfg 6 then 5 else 6
theorem min_div2_two_lt_3 (n : ℕ) : min (n / 2) 2 < 3 :=
  Nat.lt_succ_of_le (Nat.min_le_right _ 2)
theorem add_fin_lt_of_le {base k M : ℕ} (i : Fin k) (h : base + k ≤ M) : base + i.val < M :=
  lt_of_lt_of_le (Nat.add_lt_add_left i.isLt base) h
theorem ax_bit_lt_of_le {M : ℕ} (ax : Fin 3) (b : Fin 8) (h : 24 ≤ M) : 8 * ax.val + b.val < M := by
  have := ax.isLt; have := b.isLt; omega
def slot1Ubr110 (α : BitAssignment 110) : ℕ :=
  ∑ j : Fin 29, (α ⟨30 + j.val, add_fin_lt_of_le j (by decide)⟩).val * 2 ^ j.val
def slot1AxOfBr (br : Fin 7) : Fin 3 := ⟨min (br.val / 2) 2, min_div2_two_lt_3 br.val⟩
def slot1U8_110 (α : BitAssignment 110) (ax : Fin 3) : Fin 8 → ZMod 2 :=
  fun b ↦ α ⟨8 * ax.val + b.val, ax_bit_lt_of_le ax b (by decide)⟩
def slot1OutR_110 (α : BitAssignment 110) (u8 : Fin 8 → ZMod 2) : ZMod 2 :=
  prioEval (fun t ↦ mag7Bit u8 (idxMagR t)) 29
    (fun i ↦ α ⟨59 + i.val, add_fin_lt_of_le i (by decide)⟩)
def slot1OutS_110 (α : BitAssignment 110) (u8 : Fin 8 → ZMod 2) : ZMod 2 :=
  prioEval (fun t ↦ mag7Bit u8 (idxMagS t)) 21
    (fun i ↦ α ⟨88 + i.val, add_fin_lt_of_le i (by decide)⟩)
noncomputable def slot1PhiBr (cfg : Configuration) (br : Fin 7) (ax : Fin 3)
    (u8 : Fin 8 → ZMod 2) (outR outS coinHalf : ZMod 2) : ZMod 2 :=
  if br.val = 6 then (b2z (slot1Sigma cfg 0) + b2z (slot1Sigma cfg 0 != slot1Sigma cfg 1) +
    b2z (slot1Sigma cfg 0 != slot1Sigma cfg 2) + u8 7 + outR * outS) + coinHalf
  else if br.val % 2 = 0 then 1 + outR * outS
  else b2z (slot1Sigma cfg ax) + u8 7 + coinHalf * (1 + outR)
noncomputable def slot1GeomPred110 (cfg : Configuration) (α : BitAssignment 110) : ZMod 2 :=
  if α ⟨24, by decide⟩ = 1 ∧ α ⟨25, by decide⟩ = 0 ∧ α ⟨26, by decide⟩ = 1 then
    let br : Fin 7 := slot1BranchIdx cfg (slot1Ubr110 α)
    let u8 := slot1U8_110 α (slot1AxOfBr br)
    slot1PhiBr cfg br (slot1AxOfBr br) u8 (slot1OutR_110 α u8) (slot1OutS_110 α u8)
      (α ⟨109, by decide⟩)
  else 0
section Slot1FwdEvalPrioIrred
attribute [local irreducible] prioEval
private theorem band {cfg : Configuration} {u : ℕ} {lo hi j : Fin 7}
    (hlo : ¬ u < slot1Tau cfg lo) (hhi : u < slot1Tau cfg hi) (h1 : lo.val = hi.val - 1) :
    (u < slot1Tau cfg j) ↔ hi.val - 1 < j.val :=
  ⟨fun h ↦ lt_of_not_ge fun hle ↦ hlo (lt_of_lt_of_le h (slot1Tau_mono cfg (by omega))),
   fun h ↦ lt_of_lt_of_le hhi (slot1Tau_mono cfg (by omega))⟩
private theorem slot1Tau_iff (cfg : Configuration) (uBr : ℕ)
    (j : Fin 7) (hj : 1 ≤ j.val) :
    (uBr < slot1Tau cfg j) ↔ (slot1BranchIdx cfg uBr).val < j.val := by
  unfold slot1BranchIdx
  split_ifs with c1 c2 c3 c4 c5 c6
  · exact ⟨fun _ ↦ hj, fun _ ↦ lt_of_lt_of_le c1 (slot1Tau_mono cfg hj)⟩
  · exact band c1 c2 rfl
  · exact band c2 c3 rfl
  · exact band c3 c4 rfl
  · exact band c4 c5 rfl
  · exact band c5 c6 rfl
  · exact ⟨fun h ↦ absurd (lt_of_lt_of_le h (slot1Tau_mono cfg (Nat.le_of_lt_succ j.isLt))) c6,
      fun h ↦ absurd h (not_lt_of_ge (Nat.le_of_lt_succ j.isLt))⟩
attribute [local irreducible] slot1Tau
end Slot1FwdEvalPrioIrred
theorem basisBitsEquiv_apply_eq {m : ℕ} (x : Fin (2 ^ m)) :
    basisBitsEquiv m x = basisBits m x := rfl
theorem coinBitFin2_5_0 : (MomSlots01Slot1ProjKinetic.coinBitFin2 5 0).val = 1 := rfl
theorem coinBitFin2_5_1 : (MomSlots01Slot1ProjKinetic.coinBitFin2 5 1).val = 0 := rfl
theorem coinBitFin2_5_2 : (MomSlots01Slot1ProjKinetic.coinBitFin2 5 2).val = 1 := rfl
attribute [local irreducible] basisBits QRegister.extractIndex
abbrev rActCore {mPayload : ℕ} (hmPay : 80 ≤ mPayload) :
    QRegister 110 (coreWiresSym mPayload) :=
  QRegister.block 3924 110 (show 3924 + 110 ≤ 3948 + (6 + mPayload) by omega)
noncomputable def slot1GeomPhaseCore {mPayload : ℕ} (hmPay : 80 ≤ mPayload)
    (cfg : Configuration) (β : BitAssignment (coreWiresSym mPayload)) : ZMod 2 :=
  slot1GeomPred110 cfg (fun i ↦ β (rActCore hmPay i))
noncomputable def slot1GeomSelectDiag {mPayload : ℕ} (hmPay : 80 ≤ mPayload)
    (cfg : Configuration) : Operator (2 ^ (coreWiresSym mPayload)) := Matrix.diagonal fun g ↦
    ((-1 : ℂ) ^ (slot1GeomPhaseCore hmPay cfg (basisBits (coreWiresSym mPayload) g)).val)
theorem slot1GeomSelectDiag_conjTranspose {mPayload : ℕ} (hmPay : 80 ≤ mPayload)
    (cfg : Configuration) :
    (slot1GeomSelectDiag hmPay cfg)ᴴ = slot1GeomSelectDiag hmPay cfg := by
  ext i j
  by_cases hij : i = j
  · subst hij
    simp [slot1GeomSelectDiag]
  · simp [slot1GeomSelectDiag, hij, Ne.symm hij]
noncomputable def slot1GeomSelectUnitary {mPayload : ℕ} (hmPay : 80 ≤ mPayload)
    (cfg : Configuration) : Unitary (2 ^ (coreWiresSym mPayload)) :=
  ⟨slot1GeomSelectDiag hmPay cfg, mem_unitaryGroup_iff.mpr (by
    rw [Matrix.star_eq_conjTranspose, slot1GeomSelectDiag_conjTranspose, slot1GeomSelectDiag,
      Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext g
    exact MomSlots01Slot1ProjKinetic.neg_one_pow_bit_mul_self _)⟩
@[simp] theorem slot1GeomSelectUnitary_val {mPayload : ℕ} (hmPay : 80 ≤ mPayload)
    (cfg : Configuration) :
    (slot1GeomSelectUnitary hmPay cfg).1 = slot1GeomSelectDiag hmPay cfg := rfl
theorem slot1GeomSelectUnitary_offCoin {mPayload : ℕ} (hmPay : 80 ≤ mPayload)
    (cfg : Configuration) : (slot1GeomSelectUnitary hmPay cfg).1 *
    (1 - momCoinProj mPayload (FullSysPrepare6Slot.fullSysCoinIdx 1)) = 1 - momCoinProj
    mPayload (FullSysPrepare6Slot.fullSysCoinIdx 1) := by
  rw [Matrix.mul_sub, Matrix.mul_one, slot1GeomSelectUnitary_val,
    show FullSysPrepare6Slot.fullSysCoinIdx 1 = 5 from rfl, momCoinProj,
    slotBitProj, slotBitProj, slotBitProj, Matrix.diagonal_mul_diagonal,
    Matrix.diagonal_mul_diagonal, slot1GeomSelectDiag, Matrix.diagonal_mul_diagonal]
  ext g₁ g₂
  by_cases hg : g₁ = g₂
  · subst hg
    simp only [Matrix.sub_apply, Matrix.one_apply_eq, Matrix.diagonal_apply_eq]
    let bb := basisBits (coreWiresSym mPayload) g₁
    have hw (k : Fin 110) (w : Wire (coreWiresSym mPayload)) (h : 3924 + k.val = w.val) :
        bb (rActCore hmPay k) = bb w :=
      congrArg bb (Fin.ext ((congrArg Fin.val
        (MomSlots01Slot1ProjKineticAlt.qreg_block_apply 3924 110 _ k)).trans h))
    by_cases hAll : bb (MomSlots01Slot1ProjKinetic.iSlot0Mom mPayload) = 1 ∧
        bb (MomSlots01Slot1ProjKinetic.iSlot1Mom mPayload) = 0 ∧
        bb (MomSlots01Slot1ProjKinetic.iSlot2Mom mPayload) = 1
    · rcases hAll with ⟨hc0, hc1, hc2⟩
      simp [bb, coinBitFin2_5_0, coinBitFin2_5_1, coinBitFin2_5_2, hc0, hc1, hc2,
        show (0 : ZMod 2).val = 0 from rfl, show (1 : ZMod 2).val = 1 from rfl]
    · rw [show slot1GeomPhaseCore hmPay cfg bb = 0 by
        unfold slot1GeomPhaseCore slot1GeomPred110
        dsimp only
        exact ite_eq_right fun ⟨h0, h1, h2⟩ ↦ hAll ⟨(hw ⟨24, by decide⟩ _ rfl).symm.trans h0,
          (hw ⟨25, by decide⟩ _ rfl).symm.trans h1, (hw ⟨26, by decide⟩ _ rfl).symm.trans h2⟩]
      simp
  · simp [hg]
noncomputable def slot1PR (u8 : Fin 8 → ZMod 2) : ℝ :=
  ((4227330 : ℝ) * (mag7Nat u8 : ℝ) + ((mag7Bit u8 6).val : ℝ)) / (2 : ℝ) ^ 29
theorem slot1PR_bounds (u8 : Fin 8 → ZMod 2) : 0 ≤ slot1PR u8 ∧ slot1PR u8 ≤ 1 ∧ 0 ≤
    (mag7Nat u8 : ℝ) / 127 - slot1PR u8 ∧ (mag7Nat u8 : ℝ) / 127 - slot1PR u8 ≤ 1 / (2 : ℝ) ^
    29 := by
  have ⟨h1, h2, h3⟩ : 4227330 * mag7Nat u8 + (mag7Bit u8 6).val ≤ 2 ^ 29 ∧
      127 * (4227330 * mag7Nat u8 + (mag7Bit u8 6).val) ≤ 2 ^ 29 * mag7Nat u8 ∧
      2 ^ 29 * mag7Nat u8 ≤ 127 * (4227330 * mag7Nat u8 + (mag7Bit u8 6).val) + 127 := by
    have := ZMod.val_lt (mag7Bit u8 0)
    have := ZMod.val_lt (mag7Bit u8 1)
    have := ZMod.val_lt (mag7Bit u8 2)
    have := ZMod.val_lt (mag7Bit u8 3)
    have := ZMod.val_lt (mag7Bit u8 4)
    have := ZMod.val_lt (mag7Bit u8 5)
    have := ZMod.val_lt (mag7Bit u8 6)
    unfold mag7Nat
    omega
  unfold slot1PR
  exact ⟨by positivity,
    by linarith [show (4227330 : ℝ) * (mag7Nat u8 : ℝ) + ((mag7Bit u8 6).val : ℝ) ≤ (2 : ℝ) ^ 29
      by exact_mod_cast h1],
    by linarith [show (127 : ℝ) * ((4227330 : ℝ) * (mag7Nat u8 : ℝ) + ((mag7Bit u8 6).val : ℝ)) ≤
      (2 : ℝ) ^ 29 * (mag7Nat u8 : ℝ) by exact_mod_cast h2],
    by linarith [show (2 : ℝ) ^ 29 * (mag7Nat u8 : ℝ) ≤ (127 : ℝ) * ((4227330 : ℝ) *
      (mag7Nat u8 : ℝ) + ((mag7Bit u8 6).val : ℝ)) + 127 by exact_mod_cast h3]⟩
noncomputable def slot1ValBranch (cfg : Configuration)
    (xSys : Fin (2 ^ SpecsAux.SpecMirror.systemQubits)) (b : Fin 6) : ℝ :=
  let w : Fin 3 := ⟨b.val / 2, by omega⟩
  let u8 := u8FromFin (projAxisField xSys w)
  if b.val % 2 = 0 then 2 * slot1PR u8 * (((16513 : ℝ) / (2 : ℝ) ^ 21) * (mag7Nat u8 : ℝ)) - 1
  else ((-1 : ℝ) ^ (b2z (slot1Sigma cfg w) + u8 7).val) * slot1PR u8
noncomputable def bUnitTwosSlot1Geom (cfg : Configuration) : Operator
    (2 ^ SpecsAux.SpecMirror.systemQubits) := Matrix.diagonal fun xSys ↦ ((((∑ b : Fin 6,
    ((slot1Delta cfg b : ℝ) / (2 : ℝ) ^ 29) * slot1ValBranch cfg xSys b) : ℝ)) : ℂ)
def bitSplitLastEquiv (L : ℕ) : BitAssignment (L + 1) ≃ BitAssignment L × ZMod 2 where
  toFun α := (fun i ↦ α i.castSucc, α (Fin.last L))
  invFun p idx := if h : idx.val < L then p.1 ⟨idx.val, h⟩ else p.2
  left_inv α := funext fun idx ↦ by
    dsimp only
    split_ifs with h
    · exact congrArg α (Fin.ext rfl)
    · exact congrArg α (Fin.ext (by dsimp [Fin.last]; omega))
  right_inv := fun ⟨α₀, b⟩ ↦ Prod.ext
    (funext fun i ↦ by simp only [Fin.val_castSucc, i.isLt, ↓reduceDIte, Fin.eta])
    (by dsimp only [Fin.last]; rw [dite_neg_s1 (Nat.lt_irrefl L)])
theorem sum_zmod2 {M : Type*} [AddCommMonoid M] (g : ZMod 2 → M) :
    (∑ b : ZMod 2, g b) = g 0 + g 1 := by
  rw [show (Finset.univ : Finset (ZMod 2)) = {0, 1} by decide, Finset.sum_pair (by decide)]
theorem prioEval_sum_val (f : ℕ → ZMod 2) :
    ∀ (L : ℕ), (∑ α : BitAssignment L, (prioEval f L α).val) =
      ∑ t : Fin L, (f t.val).val * 2 ^ t.val
  | 0 => by simp [prioEval]
  | L + 1 => by
      rw [← Equiv.sum_comp (bitSplitLastEquiv L).symm (fun α ↦ (prioEval f (L + 1) α).val),
        Fintype.sum_prod_type]
      have hinner : ∀ α₀ : BitAssignment L,
          (∑ b : ZMod 2, (prioEval f (L + 1) ((bitSplitLastEquiv L).symm (α₀, b))).val) =
            (prioEval f L α₀).val + (f L).val := fun α₀ ↦ by
        rw [sum_zmod2]
        dsimp only [prioEval, bitSplitLastEquiv, Equiv.coe_fn_symm_mk]
        simp only [lt_self_iff_false, ↓reduceDIte, zero_ne_one, ↓reduceIte,
          show (fun i : Fin L ↦ if h : i.val < L then α₀ ⟨i.val, h⟩ else 0) = α₀ from
            funext fun i ↦ by simp [i.isLt]]
      rw [Finset.sum_congr rfl fun α₀ _ ↦ hinner α₀, Finset.sum_add_distrib,
        prioEval_sum_val f L, Finset.sum_const, Finset.card_univ,
        show Fintype.card (BitAssignment L) = 2 ^ L by simp [BitAssignment],
        smul_eq_mul, Fin.sum_univ_castSucc]
      dsimp only [Fin.val_castSucc, Fin.val_last]
      ring
theorem sum_periodic7_geom (m : Fin 7 → ℕ) :
    ∀ (q : ℕ),
      (∑ t : Fin (7 * q), m ⟨t.val % 7, Nat.mod_lt _ (by decide)⟩ * 2 ^ t.val) =
        (∑ r : Fin q, 2 ^ (7 * r.val)) * (∑ b : Fin 7, m b * 2 ^ b.val)
  | 0 => by simp
  | q + 1 => by
      have hlen : 7 * (q + 1) = 7 * q + 7 := by ring
      rw [← Equiv.sum_comp (finCongr hlen).symm, Fin.sum_univ_add]
      have h2 : (∑ b : Fin 7, m ⟨((finCongr hlen).symm (Fin.natAdd (7 * q) b)).val % 7,
          Nat.mod_lt _ (by decide)⟩ * 2 ^ ((finCongr hlen).symm (Fin.natAdd (7 * q) b)).val) =
          2 ^ (7 * q) * ∑ b : Fin 7, m b * 2 ^ b.val := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun b _ ↦ ?_
        have hfin : (⟨((finCongr hlen).symm (Fin.natAdd (7 * q) b)).val % 7,
            Nat.mod_lt _ (by decide)⟩ : Fin 7) = b := Fin.ext <| by
          change (7 * q + b.val) % 7 = b.val
          rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt b.isLt]
        have hv : ((finCongr hlen).symm (Fin.natAdd (7 * q) b)).val = 7 * q + b.val := rfl
        rw [hfin, hv, pow_add]
        ring
      rw [show (∑ i : Fin (7 * q), m ⟨((finCongr hlen).symm (Fin.castAdd 7 i)).val % 7,
          Nat.mod_lt _ (by decide)⟩ * 2 ^ ((finCongr hlen).symm (Fin.castAdd 7 i)).val) =
          ∑ t : Fin (7 * q), m ⟨t.val % 7, Nat.mod_lt _ (by decide)⟩ * 2 ^ t.val from rfl,
        h2, sum_periodic7_geom m q, Fin.sum_univ_castSucc (n := q)]
      dsimp only [Fin.val_castSucc, Fin.val_last]
      ring
theorem prioEval_sum_29 (u8 : Fin 8 → ZMod 2) : (∑ α : BitAssignment 29, (prioEval (fun t ↦
    mag7Bit u8 (idxMagR t)) 29 α).val) = 4227330 * mag7Nat u8 + (mag7Bit u8 6).val := by
  rw [prioEval_sum_val, Fin.sum_univ_succ]
  have htail : (∑ i : Fin 28, (mag7Bit u8 (idxMagR i.succ.val)).val * 2 ^ i.succ.val) = 2 * ∑
      i : Fin 28, (mag7Bit u8 ⟨i.val % 7, Nat.mod_lt _ (by decide)⟩).val * 2 ^ i.val := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [show idxMagR i.succ.val = ⟨i.val % 7, Nat.mod_lt _ (by decide)⟩ from
      ite_eq_right (Nat.succ_ne_zero i.val), Fin.val_succ, Nat.pow_succ]
    ring
  have h28 := sum_periodic7_geom (fun b ↦ (mag7Bit u8 b).val) 4
  rw [mag7Nat_eq_sum u8, Fin.sum_univ_four] at h28
  norm_num at h28
  rw [show idxMagR (0 : Fin 29).val = 6 from rfl, htail, h28]
  dsimp only [Fin.val_zero]
  omega
theorem prioEval_sum_21 (u8 : Fin 8 → ZMod 2) : (∑ α : BitAssignment 21, (prioEval (fun t ↦
    mag7Bit u8 (idxMagS t)) 21 α).val) = 16513 * mag7Nat u8 := by
  have h21 := sum_periodic7_geom (fun b ↦ (mag7Bit u8 b).val) 3
  rw [mag7Nat_eq_sum u8, Fin.sum_univ_three] at h21
  norm_num at h21
  exact (prioEval_sum_val _ 21).trans h21
attribute [local irreducible] prioEval
theorem card_fin_Ico_two_pow {b lo hi : ℕ} (hlo : lo ≤ hi) (hhi : hi ≤ 2 ^ b) : ((Finset.univ
    : Finset (Fin (2 ^ b))).filter (fun v ↦ lo ≤ v.val ∧ v.val < hi)).card = hi - lo := by
  have hc := Finset.card_union_of_disjoint (s := (Finset.univ : Finset (Fin (2 ^ b))).filter
      (fun v ↦ v.val < lo)) (t := (Finset.univ : Finset (Fin (2 ^ b))).filter
      (fun v ↦ lo ≤ v.val ∧ v.val < hi)) (Finset.disjoint_filter.mpr fun _ _ _ _ ↦ by omega)
  rw [show ((Finset.univ : Finset (Fin (2 ^ b))).filter (fun v ↦ v.val < lo)) ∪
      ((Finset.univ : Finset (Fin (2 ^ b))).filter (fun v ↦ lo ≤ v.val ∧ v.val < hi)) =
      (Finset.univ : Finset (Fin (2 ^ b))).filter (fun v ↦ v.val < hi) by
    ext v
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    omega, MomSlots01Slot1ProjKinetic.card_fin_lt_two_pow_slot1 (le_trans hlo hhi),
    MomSlots01Slot1ProjKinetic.card_fin_lt_two_pow_slot1 hhi] at hc
  omega
theorem sum_slot1BranchIdx_of_pad_zero {b : ℕ} (cfg : Configuration)
    (hb : slot1Tau cfg 6 ≤ 2 ^ b) (g : Fin 7 → ℂ) (hg6 : g 6 = 0) :
    (∑ v : Fin (2 ^ b), g (slot1BranchIdx cfg v.val)) =
      ∑ k : Fin 6, (slot1Delta cfg k : ℂ) * g k.castSucc := by
  have hmem (v : Fin (2 ^ b)) (k : Fin 6) :
      (slot1Tau cfg k.castSucc ≤ v.val ∧ v.val < slot1Tau cfg k.succ) ↔
        (slot1BranchIdx cfg v.val).val = k.val := by
    have hhi := slot1Tau_iff cfg v.val k.succ (Nat.succ_pos k.val)
    rw [Fin.val_succ] at hhi
    have hlo : slot1Tau cfg k.castSucc ≤ v.val ↔ k.val ≤ (slot1BranchIdx cfg v.val).val := by
      by_cases hk0 : k.val = 0
      · simp [show k.castSucc = 0 from Fin.ext hk0, hk0, slot1Tau_zero]
      · simpa [Fin.val_castSucc] using (slot1Tau_iff cfg v.val k.castSucc
          (show 1 ≤ k.castSucc.val by rw [Fin.val_castSucc]; omega)).not
    rw [hlo, hhi]
    omega
  have hpt (v : Fin (2 ^ b)) : g (slot1BranchIdx cfg v.val) =
      ∑ k : Fin 6, if slot1Tau cfg k.castSucc ≤ v.val ∧ v.val < slot1Tau cfg k.succ
        then g k.castSucc else 0 := by
    simp_rw [hmem v]
    by_cases h6 : (slot1BranchIdx cfg v.val).val = 6
    · rw [show slot1BranchIdx cfg v.val = 6 from Fin.ext h6, hg6]
      exact (Finset.sum_eq_zero fun k _ ↦
        ite_eq_right (ne_of_gt (show k.val < (6 : Fin 7).val from k.isLt))).symm
    · let k₀ : Fin 6 := ⟨(slot1BranchIdx cfg v.val).val,
        by have := (slot1BranchIdx cfg v.val).isLt; omega⟩
      simp_rw [show ∀ k : Fin 6, ((slot1BranchIdx cfg v.val).val = k.val) ↔ k = k₀ from
        fun k ↦ ⟨fun h ↦ Fin.ext h.symm, fun h ↦ (congrArg Fin.val h).symm⟩]
      rw [Finset.sum_ite_eq', ite_eq_left (Finset.mem_univ k₀)]
      exact congrArg g (Fin.ext rfl)
  simp_rw [hpt]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, card_fin_Ico_two_pow
    (slot1Tau_mono cfg (Nat.le_succ _)) (le_trans (slot1Tau_mono cfg
      (show k.succ.val ≤ (6 : Fin 7).val by rw [Fin.val_succ]; exact k.isLt)) hb),
    show slot1Tau cfg k.succ - slot1Tau cfg k.castSucc = slot1Delta cfg k by
      rw [show k.succ = ⟨k.val + 1, by omega⟩ from Fin.ext rfl,
        show k.castSucc = ⟨k.val, by omega⟩ from Fin.ext rfl, slot1Tau_succ_eq cfg k]
      omega]
attribute [local irreducible] slot1BranchIdx
theorem sum_basisBits_val_eq {b : ℕ} (v : Fin (2 ^ b)) :
    (∑ j : Fin b, (basisBits b v j).val * 2 ^ j.val) = v.val := by
  have h0 : (∑ j : Fin b, (basisBits b v j).val * 2 ^ j.val) =
      sliceVal (basisBits b v) 0 b (Nat.zero_add b).le := by
    rw [sliceVal_eq_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [show (⟨0 + j.val, by omega⟩ : Fin b) = j from Fin.ext (Nat.zero_add j.val)]
  rw [h0, sliceVal_eq_of_testBit (basisBits b v) 0 v.val b (Nat.zero_add b).le fun j hj ↦ by
    rw [show (⟨0 + j, by omega⟩ : Fin b) = ⟨j, hj⟩ from Fin.ext (Nat.zero_add j),
      basisBits_eq_testBit b v ⟨j, hj⟩]
    rfl]
  exact Nat.mod_eq_of_lt v.isLt
def geomUbr {mPayload : ℕ} (hmPay : 80 ≤ mPayload) (γ : BitAssignment mPayload) : ℕ :=
  ∑ j : Fin 29, (γ ⟨j.val, lt_of_lt_of_le j.isLt (le_trans (by decide) hmPay)⟩).val * 2 ^ j.val
def geomOutR {mPayload : ℕ} (hmPay : 80 ≤ mPayload) (γ : BitAssignment mPayload)
    (u8 : Fin 8 → ZMod 2) : ZMod 2 := prioEval (fun t ↦ mag7Bit u8 (idxMagR t)) 29
  (fun i ↦ γ ⟨29 + i.val, add_fin_lt_of_le i (le_trans (by decide) hmPay)⟩)
def geomOutS {mPayload : ℕ} (hmPay : 80 ≤ mPayload) (γ : BitAssignment mPayload)
    (u8 : Fin 8 → ZMod 2) : ZMod 2 := prioEval (fun t ↦ mag7Bit u8 (idxMagS t)) 21
  (fun i ↦ γ ⟨58 + i.val, add_fin_lt_of_le i (le_trans (by decide) hmPay)⟩)
noncomputable def geomPhaseScalar {mPayload : ℕ} (hmPay : 80 ≤ mPayload) (cfg : Configuration)
    (c : Fin 8) (xSys : Fin (2 ^ SpecsAux.SpecMirror.systemQubits)) (u : Fin (2 ^ mPayload)) : ℂ :=
  if c = 5 then
    let γ := basisBits mPayload u
    let br := slot1BranchIdx cfg (geomUbr hmPay γ)
    let u8 := u8FromFin (projAxisField xSys (slot1AxOfBr br))
    (-1 : ℂ) ^ (slot1PhiBr cfg br (slot1AxOfBr br) u8 (geomOutR hmPay γ u8)
      (geomOutS hmPay γ u8) (γ ⟨79, lt_of_lt_of_le (by decide) hmPay⟩)).val
  else 1
theorem sixProj_mul_slot1GeomSelectDiag {mPayload : ℕ} (hmPay : 80 ≤ mPayload)
    (cfg : Configuration) (c : Fin 8) : (coreSixSym mPayload).basisOutcomeProjector
    (coinSixOutcome c) * slot1GeomSelectDiag hmPay cfg = ∑ u : Fin (2 ^ mPayload),
    (corePayloadSym mPayload).basisOutcomeProjector u *
    (coreSixSym mPayload).basisOutcomeProjector (coinSixOutcome c) *
    (coreSysSym mPayload).embedMatrix
    (Matrix.diagonal (fun xSys ↦ geomPhaseScalar hmPay cfg c xSys u)) := by
  simp_rw [MomSlots01Slot1ProjKinetic.embedMatrix_diagonal (coreSysSym mPayload),
    QRegister.basisOutcomeProjector_eq_diagonal, Matrix.diagonal_mul_diagonal]
  rw [slot1GeomSelectDiag, Matrix.diagonal_mul_diagonal]
  ext g₁ g₂
  by_cases hg : g₁ = g₂
  · subst hg
    simp only [Matrix.diagonal_apply_eq, Matrix.sum_apply]
    let u₀ : Fin (2 ^ mPayload) := (corePayloadSym mPayload).extractIndex g₁
    rw [Finset.sum_eq_single u₀ (fun u _ hu ↦ by simp [u₀, Ne.symm hu])
      (fun h ↦ (h (Finset.mem_univ u₀)).elim)]
    simp only [u₀, ↓reduceIte, one_mul]
    by_cases hSix : (coreSixSym mPayload).extractIndex g₁ = coinSixOutcome c
    · simp only [hSix, ↓reduceIte, one_mul]
      unfold slot1GeomPhaseCore
      obtain ⟨α, hα⟩ : ∃ x : BitAssignment 110,
          x = fun i ↦ basisBits (coreWiresSym mPayload) g₁ (rActCore hmPay i) := ⟨_, rfl⟩
      rw [← hα]
      have hα_app : ∀ i, α i = basisBits (coreWiresSym mPayload) g₁ (rActCore hmPay i) :=
        congrFun hα
      have hc (j : Fin 3) : α ⟨24 + j.val, by omega⟩ = basisBits 3 c j := by
        rw [hα_app, show rActCore hmPay ⟨24 + j.val, by omega⟩ =
            (coreSixSym mPayload) ⟨j.val, by omega⟩ from
          Fin.ext (show 3924 + (24 + j.val) = 3948 + j.val by omega),
          ← (coreSixSym mPayload).basisBits_extractIndex g₁, hSix, coinSixOutcome,
          MomSlots01Slot1ProjKinetic.basisBits_symm_apply_local_slot1]
        exact dite_eq_left j.isLt
      have hpay (k : ℕ) (hk : k < 80) :
          α ⟨30 + k, by omega⟩ = basisBits mPayload u₀ ⟨k, by omega⟩ := by
        rw [hα_app]
        exact (congrArg _ (show rActCore hmPay ⟨30 + k, by omega⟩ =
            corePayloadSym mPayload ⟨k, by omega⟩ from
          Fin.ext (show 3924 + (30 + k) = 3954 + k by omega))).trans
          ((corePayloadSym mPayload).basisBits_extractIndex g₁ _).symm
      have hproj (ax : Fin 3) (b : Fin 8) : α ⟨8 * ax.val + b.val, by omega⟩ =
          u8FromFin (projAxisField ((coreSysSym mPayload).extractIndex g₁) ax) b := by
        rw [hα_app, show rActCore hmPay ⟨8 * ax.val + b.val, by omega⟩ =
          (coreSysSym mPayload) ((proj3Axes ax) b) from Fin.ext (by
            dsimp [rActCore, coreSysSym, proj3Axes, SpecsAux.SpecMirror.numElectrons,
              SpecsAux.SpecMirror.electronBits, MomSlots01Slot1ProjKineticAlt.qreg_block_apply,
              MomSlots01Slot1ProjKineticAlt.qreg_block_wires_apply,
              MomSlots01Slot1ProjKineticAlt.qreg_whole_wires,
              MomSlots01Slot1ProjKineticAlt.emb_trans_apply,
              MomSlots01Slot1ProjKineticAlt.emb_refl_apply,
              MomSlots01Slot1ProjKineticAlt.emb_mk_apply]
            omega), ← (coreSysSym mPayload).basisBits_extractIndex g₁,
          ← (proj3Axes ax).basisBits_extractIndex]
        exact basisBits_eq_testBit 8 (projAxisField ((coreSysSym mPayload).extractIndex g₁) ax) b
      unfold slot1GeomPred110 geomPhaseScalar
      dsimp only
      rw [show α ⟨24, by decide⟩ = basisBits 3 c 0 from (congrArg α (Fin.ext rfl)).trans (hc 0),
        show α ⟨25, by decide⟩ = basisBits 3 c 1 from (congrArg α (Fin.ext rfl)).trans (hc 1),
        show α ⟨26, by decide⟩ = basisBits 3 c 2 from (congrArg α (Fin.ext rfl)).trans (hc 2)]
      by_cases hc5 : c = 5
      · rw [ite_eq_left ((coin3_bits_eq_5_iff c).mpr hc5), ite_eq_left hc5,
          show slot1Ubr110 α = geomUbr hmPay (basisBits mPayload u₀) from
            Finset.sum_congr rfl fun j _ ↦ by rw [hpay j.val (lt_trans j.isLt (by decide))],
          show ∀ u8, slot1OutR_110 α u8 = geomOutR hmPay (basisBits mPayload u₀) u8 from
            fun u8 ↦ congrArg (prioEval _ 29) (funext fun i ↦ (congrArg α (Fin.ext
              (Nat.add_assoc 30 29 i.val))).trans (hpay _ (add_fin_lt_of_le i (by decide)))),
          show ∀ u8, slot1OutS_110 α u8 = geomOutS hmPay (basisBits mPayload u₀) u8 from
            fun u8 ↦ congrArg (prioEval _ 21) (funext fun i ↦ (congrArg α (Fin.ext
              (Nat.add_assoc 30 58 i.val))).trans (hpay _ (add_fin_lt_of_le i (by decide)))),
          show α ⟨109, by decide⟩ = basisBits mPayload u₀ ⟨79, lt_of_lt_of_le (by decide) hmPay⟩
            from hpay 79 (by decide)]
        simp_rw [show ∀ ax, slot1U8_110 α ax =
          u8FromFin (projAxisField ((coreSysSym mPayload).extractIndex g₁) ax) from
          fun ax ↦ funext (hproj ax)]
        rfl
      · rw [ite_eq_right (fun hh ↦ hc5 ((coin3_bits_eq_5_iff c).mp hh)), ite_eq_right hc5]
        rfl
    · simp [hSix]
  · simp [Matrix.sum_apply, hg]
theorem neg_one_pow_pad_cancel (base : ZMod 2) :
    ((-1 : ℂ) ^ (base + 0).val) + ((-1 : ℂ) ^ (base + 1).val) = 0 := by
  have h2 : (1 + 1 : ZMod 2) = 0 := rfl
  have hv0 : (0 : ZMod 2).val = 0 := rfl
  have hv1 : (1 : ZMod 2).val = 1 := rfl
  rcases bit_cases base with rfl | rfl <;>
    simp only [add_zero, zero_add, h2, hv0, hv1] <;> norm_num
theorem neg_one_pow_quad_eq (r s : ZMod 2) :
    ((-1 : ℂ) ^ (1 + r * s).val) = 2 * (r.val : ℂ) * (s.val : ℂ) - 1 := by
  have h2 : (1 + 1 : ZMod 2) = 0 := rfl
  have hv0 : (0 : ZMod 2).val = 0 := rfl
  have hv1 : (1 : ZMod 2).val = 1 := rfl
  rcases bit_cases r with rfl | rfl <;> rcases bit_cases s with rfl | rfl <;>
    simp only [mul_zero, mul_one, add_zero, h2, hv0, hv1] <;> norm_num
theorem neg_one_pow_lin_sum (base r : ZMod 2) : ((-1 : ℂ) ^ (base + 0 * (1 + r)).val) +
    ((-1 : ℂ) ^ (base + 1 * (1 + r)).val) = 2 * ((-1 : ℂ) ^ base.val) * (r.val : ℂ) := by
  have h2 : (1 + 1 : ZMod 2) = 0 := rfl
  have hv0 : (0 : ZMod 2).val = 0 := rfl
  have hv1 : (1 : ZMod 2).val = 1 := rfl
  rcases bit_cases base with rfl | rfl <;> rcases bit_cases r with rfl | rfl <;>
    simp only [zero_mul, one_mul, add_zero, zero_add, h2, hv0, hv1] <;> norm_num
theorem inner_sum_geom_branch {bR bS : ℕ} (hbR : bR = 29) (hbS : bS = 21)
    (cfg : Configuration) (xSys : Fin (2 ^ SpecsAux.SpecMirror.systemQubits)) (br : Fin 7) :
    (∑ αR : BitAssignment bR, ∑ αS : BitAssignment bS, ∑ coinHalf : ZMod 2,
      let ax := slot1AxOfBr br
      let u8 := u8FromFin (projAxisField xSys ax)
      ((-1 : ℂ) ^ (slot1PhiBr cfg br ax u8
        (prioEval (fun t ↦ mag7Bit u8 (idxMagR t)) bR αR)
        (prioEval (fun t ↦ mag7Bit u8 (idxMagS t)) bS αS) coinHalf).val)) =
    if h6 : br.val = 6 then 0
    else (2 : ℂ) * ((2 ^ bR : ℕ) : ℂ) * ((2 ^ bS : ℕ) : ℂ) *
      ((slot1ValBranch cfg xSys ⟨br.val, by have := br.isLt; omega⟩ : ℝ) : ℂ) := by
  have hcardR : Fintype.card (BitAssignment bR) = 2 ^ bR := by simp [BitAssignment]
  have hcardS : Fintype.card (BitAssignment bS) = 2 ^ bS := by simp [BitAssignment]
  unfold slot1PhiBr slot1AxOfBr
  dsimp only
  by_cases h6 : br.val = 6
  · simp only [h6, ↓reduceIte, ↓reduceDIte]
    exact Finset.sum_eq_zero fun _ _ ↦ Finset.sum_eq_zero fun _ _ ↦ by
      rw [sum_zmod2, neg_one_pow_pad_cancel]
  · simp only [h6, ↓reduceIte, ↓reduceDIte]
    let b6 : Fin 6 := ⟨br.val, by have := br.isLt; omega⟩
    let w : Fin 3 := ⟨b6.val / 2, by omega⟩
    have hax_eq : (⟨min (br.val / 2) 2, min_div2_two_lt_3 br.val⟩ : Fin 3) = w :=
      Fin.ext (show min (br.val / 2) 2 = br.val / 2 by have := br.isLt; omega)
    let u8 : Fin 8 → ZMod 2 := u8FromFin (projAxisField xSys w)
    let rSumC : ℂ := (4227330 : ℂ) * (mag7Nat u8 : ℂ) + ((mag7Bit u8 6).val : ℂ)
    have hsumR : (∑ αR : BitAssignment bR,
        ((prioEval (fun t ↦ mag7Bit u8 (idxMagR t)) bR αR).val : ℂ)) = rSumC := by
      subst hbR
      dsimp only [rSumC]
      exact_mod_cast prioEval_sum_29 u8
    by_cases heven : br.val % 2 = 0
    · simp only [heven, ↓reduceIte, hax_eq]
      have hsumS : (∑ αS : BitAssignment bS,
          ((prioEval (fun t ↦ mag7Bit u8 (idxMagS t)) bS αS).val : ℂ)) =
          (16513 : ℂ) * (mag7Nat u8 : ℂ) := by
        subst hbS
        exact_mod_cast prioEval_sum_21 u8
      have h2 (αR : BitAssignment bR) : (∑ αS : BitAssignment bS, ∑ _c : ZMod 2, ((-1 : ℂ) ^
          (1 + prioEval (fun t ↦ mag7Bit u8 (idxMagR t)) bR αR * prioEval (fun t ↦ mag7Bit u8
          (idxMagS t)) bS αS).val)) = ((4 : ℂ) * ((16513 : ℂ) * (mag7Nat u8 : ℂ))) *
          ((prioEval (fun t ↦ mag7Bit u8 (idxMagR t)) bR αR).val : ℂ) -
          2 * ((2 ^ bS : ℕ) : ℂ) := by
        simp_rw [sum_zmod2, neg_one_pow_quad_eq, show ∀ a b : ℂ,
          (2 * a * b - 1) + (2 * a * b - 1) = 4 * a * b - 2 from fun _ _ ↦ by ring]
        rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hsumS,
          Finset.sum_const, Finset.card_univ, hcardS, nsmul_eq_mul]
        ring
      rw [Finset.sum_congr rfl fun αR _ ↦ h2 αR, Finset.sum_sub_distrib, ← Finset.mul_sum,
        hsumR, Finset.sum_const, Finset.card_univ, hcardR, nsmul_eq_mul]
      unfold slot1ValBranch slot1PR
      dsimp only [rSumC]
      rw [ite_eq_left (show b6.val % 2 = 0 from heven), hbR, hbS]
      push_cast
      norm_num
      ring
    · simp only [heven, ↓reduceIte, hax_eq]
      rw [Finset.sum_congr rfl fun αR _ ↦ Finset.sum_congr rfl fun _ _ ↦
        show (∑ coinHalf : ZMod 2, ((-1 : ℂ) ^ (b2z (slot1Sigma cfg w) + u8 7 + coinHalf *
          (1 + prioEval (fun t ↦ mag7Bit u8 (idxMagR t)) bR αR)).val)) =
          2 * ((-1 : ℂ) ^ (b2z (slot1Sigma cfg w) + u8 7).val) *
            ((prioEval (fun t ↦ mag7Bit u8 (idxMagR t)) bR αR).val : ℂ) by
          rw [sum_zmod2, neg_one_pow_lin_sum]]
      simp_rw [Finset.sum_const, Finset.card_univ, hcardS, nsmul_eq_mul, ← mul_assoc]
      rw [← Finset.mul_sum, hsumR]
      unfold slot1ValBranch slot1PR
      dsimp only [rSumC]
      rw [ite_eq_right (show ¬b6.val % 2 = 0 from heven), hbR, hbS]
      push_cast
      norm_num
      ring
private def splitBits (a b : ℕ) :
    BitAssignment (a + b) ≃ BitAssignment a × BitAssignment b where
  toFun γ := (fun i ↦ γ ⟨i.val, by omega⟩, fun j ↦ γ ⟨a + j.val, by omega⟩)
  invFun p k := if h : k.val < a then p.1 ⟨k.val, h⟩ else p.2 ⟨k.val - a, by omega⟩
  left_inv γ := funext fun k ↦ by
    by_cases h : k.val < a
    · exact (dite_eq_left h).trans (congrArg γ (Fin.ext rfl))
    · exact (dite_eq_right h).trans (congrArg γ (Fin.ext (by dsimp; omega)))
  right_inv := fun ⟨x, y⟩ ↦ Prod.ext
    (funext fun i ↦ (dite_eq_left i.isLt).trans (congrArg x (Fin.ext rfl)))
    (funext fun j ↦ (dite_eq_right (by dsimp; omega)).trans (congrArg y (Fin.ext (by
      dsimp; omega))))
private theorem splitBits_symm_lt {a b : ℕ} (x : BitAssignment a) (y : BitAssignment b)
    (k : Fin (a + b)) (hk : k.val < a) : (splitBits a b).symm (x, y) k = x ⟨k.val, hk⟩ :=
  dite_eq_left hk
private theorem splitBits_symm_ge {a b : ℕ} (x : BitAssignment a) (y : BitAssignment b)
    (k : Fin (a + b)) (hk : a ≤ k.val) :
    (splitBits a b).symm (x, y) k = y ⟨k.val - a, by omega⟩ :=
  dite_eq_right (not_lt_of_ge hk)
theorem avg_geomPhaseScalar_sym {mPayload bBr bR bS : ℕ}
    (hbBr : bBr = 29) (hbR : bR = 29) (hbS : bS = 21) (hmPay : bBr + bR + bS + 1 ≤ mPayload)
    (cfg : Configuration) (c : Fin 8) (xSys : Fin (2 ^ SpecsAux.SpecMirror.systemQubits)) :
    have hm80 : 80 ≤ mPayload := by omega
    ((2 : ℂ)⁻¹ ^ mPayload) * (∑ u : Fin (2 ^ mPayload), geomPhaseScalar hm80 cfg c xSys u) =
      if c = 5 then bUnitTwosSlot1Geom cfg xSys xSys else 1 := by
  intro hm80
  by_cases hc5 : c = 5
  · subst hc5
    rw [ite_eq_left rfl]
    have hSumCast {b : ℕ} (hb : b = 29) (v : Fin (2 ^ b)) (f : Fin 29 → ZMod 2)
        (h : ∀ j : Fin 29, f j = basisBits b v ⟨j.val, by omega⟩) :
        (∑ j : Fin 29, (f j).val * 2 ^ j.val) = v.val := by
      subst hb
      simp_rw [h]
      exact sum_basisBits_val_eq v
    have hPrioCast (f : ℕ → ZMod 2) (L₁ L₂ : ℕ) (hL : L₂ = L₁) (α₁ : BitAssignment L₁)
        (α₂ : BitAssignment L₂) (h : ∀ i : Fin L₁, α₁ i = α₂ ⟨i.val, by omega⟩) :
        prioEval f L₁ α₁ = prioEval f L₂ α₂ := by
      subst hL
      exact congrArg (prioEval f _) (funext h)
    let mRest := mPayload - (bBr + bR + bS + 1)
    let e0 : BitAssignment mPayload ≃ BitAssignment (bBr + (bR + ((bS + 1) + mRest))) :=
      ⟨fun γ k ↦ γ ⟨k.val, by omega⟩, fun γ k ↦ γ ⟨k.val, by omega⟩, fun _ ↦ rfl, fun _ ↦ rfl⟩
    let e := (basisBitsEquiv mPayload).trans <| e0.trans <|
      (splitBits bBr _).trans <| Equiv.prodCongr (basisBitsEquiv bBr).symm <|
      (splitBits bR _).trans <| Equiv.prodCongr (Equiv.refl _) <|
      (splitBits (bS + 1) mRest).trans <| Equiv.prodCongr (bitSplitLastEquiv bS) (Equiv.refl _)
    rw [← Equiv.sum_comp e.symm (fun u ↦ geomPhaseScalar hm80 cfg 5 xSys u)]
    have hbody (vBr : Fin (2 ^ bBr)) (αR : BitAssignment bR) (αS : BitAssignment bS)
        (coinHalf : ZMod 2) (rest : BitAssignment mRest) :
        geomPhaseScalar hm80 cfg 5 xSys (e.symm (vBr, αR, (αS, coinHalf), rest)) =
          let br := slot1BranchIdx cfg vBr.val
          let ax := slot1AxOfBr br
          let u8 := u8FromFin (projAxisField xSys ax)
          ((-1 : ℂ) ^ (slot1PhiBr cfg br ax u8
            (prioEval (fun t ↦ mag7Bit u8 (idxMagR t)) bR αR)
            (prioEval (fun t ↦ mag7Bit u8 (idxMagS t)) bS αS) coinHalf).val) := by
      have hB (idx : Fin mPayload) :
          basisBits mPayload (e.symm (vBr, αR, (αS, coinHalf), rest)) idx =
            (splitBits bBr _).symm (basisBitsEquiv bBr vBr, (splitBits bR _).symm (αR,
              (splitBits (bS + 1) mRest).symm ((bitSplitLastEquiv bS).symm (αS, coinHalf),
                rest))) ⟨idx.val, by omega⟩ :=
        MomSlots01Slot1ProjKinetic.basisBits_symm_apply_local_slot1 _ idx
      have hvBr := hSumCast hbBr vBr (fun j ↦ basisBits mPayload
        (e.symm (vBr, αR, (αS, coinHalf), rest)) ⟨j.val, by omega⟩) fun j ↦ by
        rw [hB, splitBits_symm_lt _ _ _ (show j.val < bBr by omega), basisBitsEquiv_apply_eq]
      have hR := hPrioCast (fun t ↦ mag7Bit (u8FromFin (projAxisField xSys
        (slot1AxOfBr (slot1BranchIdx cfg vBr.val)))) (idxMagR t)) _ _ hbR
        (fun i ↦ basisBits mPayload (e.symm (vBr, αR, (αS, coinHalf), rest))
          ⟨29 + i.val, by omega⟩) αR fun i ↦ by
        rw [hB, splitBits_symm_ge _ _ _ (show bBr ≤ 29 + i.val by omega),
          splitBits_symm_lt _ _ _ (show 29 + i.val - bBr < bR by omega)]
        exact congrArg αR (Fin.ext (show 29 + i.val - bBr = i.val by omega))
      have hS := hPrioCast (fun t ↦ mag7Bit (u8FromFin (projAxisField xSys
        (slot1AxOfBr (slot1BranchIdx cfg vBr.val)))) (idxMagS t)) _ _ hbS
        (fun i ↦ basisBits mPayload (e.symm (vBr, αR, (αS, coinHalf), rest))
          ⟨58 + i.val, by omega⟩) αS fun i ↦ by
        rw [hB, splitBits_symm_ge _ _ _ (show bBr ≤ 58 + i.val by omega),
          splitBits_symm_ge _ _ _ (show bR ≤ 58 + i.val - bBr by omega),
          splitBits_symm_lt _ _ _ (show 58 + i.val - bBr - bR < bS + 1 by omega)]
        exact (dite_eq_left (show 58 + i.val - bBr - bR < bS by omega)).trans
          (congrArg αS (Fin.ext (show 58 + i.val - bBr - bR = i.val by omega)))
      have hcH : basisBits mPayload (e.symm (vBr, αR, (αS, coinHalf), rest))
          ⟨79, by omega⟩ = coinHalf := by
        rw [hB, splitBits_symm_ge _ _ _ (show bBr ≤ 79 by omega),
          splitBits_symm_ge _ _ _ (show bR ≤ 79 - bBr by omega),
          splitBits_symm_lt _ _ _ (show 79 - bBr - bR < bS + 1 by omega)]
        exact dite_eq_right (show ¬(79 - bBr - bR < bS) by omega)
      unfold geomPhaseScalar geomUbr geomOutR geomOutS
      rw [ite_eq_left rfl]
      dsimp only
      rw [hvBr, hR, hS, hcH]
    simp_rw [Fintype.sum_prod_type, hbody, Finset.sum_const, Finset.card_univ,
      show Fintype.card (BitAssignment mRest) = 2 ^ mRest by simp [BitAssignment],
      nsmul_eq_mul, ← Finset.mul_sum, inner_sum_geom_branch hbR hbS cfg xSys]
    let gBranch : Fin 7 → ℂ := fun br ↦ if h6 : br.val = 6 then 0 else
      (2 : ℂ) * ((2 ^ bR : ℕ) : ℂ) * ((2 ^ bS : ℕ) : ℂ) * ((slot1ValBranch cfg xSys
        ⟨br.val, Nat.lt_of_le_of_ne (Nat.le_of_lt_succ br.isLt) h6⟩ : ℝ) : ℂ)
    rw [sum_slot1BranchIdx_of_pad_zero cfg
      (hbBr ▸ le_of_lt (slot1Tau_six_lt_two_pow_29 cfg)) gBranch (dite_eq_left rfl)]
    simp_rw [show ∀ k : Fin 6, gBranch k.castSucc = (2 : ℂ) * ((2 ^ bR : ℕ) : ℂ) *
      ((2 ^ bS : ℕ) : ℂ) * ((slot1ValBranch cfg xSys k : ℝ) : ℂ) from fun k ↦
      dite_eq_right (Fin.val_castSucc k ▸ ne_of_lt k.isLt)]
    unfold bUnitTwosSlot1Geom
    rw [Matrix.diagonal_apply_eq, show mPayload = mRest + bBr + bR + bS + 1 by omega]
    conv_lhs => rw [pow_add, pow_add, pow_add, pow_add]
    have hcPost' : ((2 : ℂ)⁻¹ ^ mRest) * ((2 : ℂ) ^ mRest) = 1 := by
      rw [inv_pow]
      exact inv_mul_cancel₀ (pow_ne_zero mRest (two_ne_zero : (2 : ℂ) ≠ 0))
    rw [hbBr, hbR, hbS]
    push_cast
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    calc _ = ((2 : ℂ)⁻¹ ^ mRest * (2 : ℂ) ^ mRest) *
          (((2 : ℂ)⁻¹ ^ 29 * (2 : ℂ)⁻¹ ^ 29 * (2 : ℂ)⁻¹ ^ 21 * (2 : ℂ)⁻¹ ^ 1) *
            ((slot1Delta cfg k : ℂ) * (2 * (2 : ℂ) ^ 29 * (2 : ℂ) ^ 21 *
              (slot1ValBranch cfg xSys k : ℂ)))) := by ring
      _ = _ := by
          rw [hcPost', one_mul]
          norm_num
          ring
  · rw [ite_eq_right hc5]
    simp_rw [show ∀ u : Fin (2 ^ mPayload), geomPhaseScalar hm80 cfg c xSys u = 1 from
      fun _ ↦ ite_eq_right hc5]
    rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul, mul_one]
    push_cast
    rw [inv_pow]
    exact inv_mul_cancel₀ (pow_ne_zero mPayload (two_ne_zero : (2 : ℂ) ≠ 0))
theorem slot1Geom_hadamard_topBlock_all {mPayload : ℕ} (hmPay : 80 ≤ mPayload)
    (cfg : Configuration) (c : Fin 8) :
    let B_c : Operator (2 ^ SpecsAux.SpecMirror.systemQubits) :=
      if c = 5 then bUnitTwosSlot1Geom cfg else 1
    (coreAncSym mPayload).basisOutcomeProjector (coinSelOutcome (selCoin3Sym mPayload) c) *
      (unitaryConj (coreHadamardUnitary mPayload) (slot1GeomSelectUnitary hmPay cfg)).1 *
      (coreAncSym mPayload).basisOutcomeProjector (coinSelOutcome (selCoin3Sym mPayload) c) =
    (coreAncSym mPayload).basisOutcomeProjector (coinSelOutcome (selCoin3Sym mPayload) c) *
      (coreSysSym mPayload).embedMatrix B_c *
      (coreAncSym mPayload).basisOutcomeProjector
        (coinSelOutcome (selCoin3Sym mPayload) c) := by
  intro B_c
  let sys := coreSysSym mPayload
  let six := coreSixSym mPayload
  let pay := corePayloadSym mPayload
  let H := (hadamardAll pay).eval
  let R_c := six.basisOutcomeProjector (coinSixOutcome c)
  let P_0 := pay.basisOutcomeProjector 0
  have hDisj_pay_six : pay.DisjointWires six := QRegister.disjoint_comm.mp <|
    QRegister.block_disjoint_of_le SpecsAux.SpecMirror.systemQubits 6
      (SpecsAux.SpecMirror.systemQubits + 6) mPayload (by dsimp [coreWiresSym, selWiresSym]; omega)
      (by dsimp [coreWiresSym, selWiresSym]; omega) le_rfl
  have hDisj_pay_sys : pay.DisjointWires sys := QRegister.disjoint_comm.mp <|
    QRegister.block_disjoint_of_le 0 SpecsAux.SpecMirror.systemQubits
      (SpecsAux.SpecMirror.systemQubits + 6) mPayload (by dsimp [coreWiresSym]; omega)
      (by dsimp [coreWiresSym, selWiresSym]; omega) (by omega)
  have hH_Rc : H.1 * R_c = R_c * H.1 :=
    hadamardAll_comm_embedMatrix_slot1 pay six hDisj_pay_six (compProj (coinSixOutcome c))
  have hH_sys (M : Operator (2 ^ SpecsAux.SpecMirror.systemQubits)) :
      H.1 * sys.embedMatrix M = sys.embedMatrix M * H.1 :=
    hadamardAll_comm_embedMatrix_slot1 pay sys hDisj_pay_sys M
  have hP0_Rc : P_0 * R_c = R_c * P_0 := by
    simp only [P_0, R_c, QRegister.basisOutcomeProjector_eq_diagonal,
      Matrix.diagonal_mul_diagonal, mul_comm]
  have hRc_idem : R_c * R_c = R_c := by
    simp only [R_c, QRegister.basisOutcomeProjector_eq_diagonal, Matrix.diagonal_mul_diagonal]
    refine congrArg Matrix.diagonal (funext fun i ↦ ?_)
    by_cases h : six.extractIndex i = coinSixOutcome c
    · simp [h]
    · simp [h]
  rw [ancProjector_eq_six_mul_payload mPayload c]
  change (R_c * P_0) * (H.1ᴴ * slot1GeomSelectDiag hmPay cfg * H.1) * (R_c * P_0) =
    (R_c * P_0) * sys.embedMatrix B_c * (R_c * P_0)
  have hLHS1 : (R_c * P_0) * (H.1ᴴ * slot1GeomSelectDiag hmPay cfg * H.1) * (R_c * P_0) =
      P_0 * H.1ᴴ * (R_c * slot1GeomSelectDiag hmPay cfg) * H.1 * P_0 * R_c := by
    have hHdag_Rc : R_c * H.1ᴴ = H.1ᴴ * R_c := by
      rw [FullSysPrepare6Slot.hadamardAll_eval_self_adj pay, ← hH_Rc]
    have hc : slot1GeomSelectDiag hmPay cfg * R_c = R_c * slot1GeomSelectDiag hmPay cfg := by
      simp only [R_c, slot1GeomSelectDiag, QRegister.basisOutcomeProjector_eq_diagonal,
        Matrix.diagonal_mul_diagonal, mul_comm]
    calc (R_c * P_0) * (H.1ᴴ * slot1GeomSelectDiag hmPay cfg * H.1) * (R_c * P_0)
        = (P_0 * R_c) * (H.1ᴴ * slot1GeomSelectDiag hmPay cfg * H.1) * (R_c * (P_0 * R_c)) :=
            congrArg₂ HMul.hMul (congrArg₂ HMul.hMul hP0_Rc.symm rfl)
              (by rw [← Matrix.mul_assoc, ← hP0_Rc, Matrix.mul_assoc, hRc_idem, hP0_Rc])
      _ = P_0 * H.1ᴴ * (R_c * (slot1GeomSelectDiag hmPay cfg * R_c)) * H.1 * P_0 * R_c := by
            simp only [Matrix.mul_assoc]
            rw [← Matrix.mul_assoc R_c H.1ᴴ, hHdag_Rc, ← Matrix.mul_assoc H.1 R_c, hH_Rc]
            simp only [Matrix.mul_assoc]
      _ = P_0 * H.1ᴴ * (R_c * slot1GeomSelectDiag hmPay cfg) * H.1 * P_0 * R_c := by
            rw [hc, ← Matrix.mul_assoc R_c R_c, hRc_idem]
  rw [hLHS1, sixProj_mul_slot1GeomSelectDiag hmPay cfg c, Finset.mul_sum, Finset.sum_mul,
    Finset.sum_mul, Finset.sum_mul]
  have hterm (u : Fin (2 ^ mPayload)) : P_0 * H.1ᴴ * (pay.basisOutcomeProjector u * R_c *
      sys.embedMatrix (Matrix.diagonal (fun xSys ↦ geomPhaseScalar hmPay cfg c xSys u))) * H.1
      * P_0 * R_c = (R_c * P_0) * (((2 : ℂ)⁻¹ ^ mPayload) • sys.embedMatrix (Matrix.diagonal
      (fun xSys ↦ geomPhaseScalar hmPay cfg c xSys u))) * (R_c * P_0) := by
    let D_u := Matrix.diagonal (fun xSys ↦ geomPhaseScalar hmPay cfg c xSys u)
    have hDu_Rc : sys.embedMatrix D_u * R_c = R_c * sys.embedMatrix D_u := by
      simp only [D_u, MomSlots01Slot1ProjKinetic.embedMatrix_diagonal, R_c,
        QRegister.basisOutcomeProjector_eq_diagonal, Matrix.diagonal_mul_diagonal, mul_comm]
    calc _ = P_0 * H.1ᴴ * pay.basisOutcomeProjector u * H.1 *
            ((R_c * (sys.embedMatrix D_u * P_0)) * R_c) := by
            simp only [Matrix.mul_assoc]
            rw [← Matrix.mul_assoc (sys.embedMatrix D_u) H.1, ← hH_sys D_u, Matrix.mul_assoc,
              ← Matrix.mul_assoc R_c H.1, ← hH_Rc]
            simp only [Matrix.mul_assoc]
      _ = (P_0 * H.1ᴴ * pay.basisOutcomeProjector u * H.1 * P_0) *
            sys.embedMatrix D_u * (R_c * R_c) := by
            rw [QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint
              sys pay hDisj_pay_sys.symm D_u 0, ← Matrix.mul_assoc R_c P_0, ← hP0_Rc,
              Matrix.mul_assoc P_0 R_c (sys.embedMatrix D_u), hDu_Rc.symm]
            simp only [Matrix.mul_assoc]
      _ = (((2 : ℂ)⁻¹ ^ mPayload) • P_0) * sys.embedMatrix D_u * R_c := by
            rw [FullSysPrepare6Slot.hadamardAll_proj_zero_conj pay u, hRc_idem]
      _ = _ := by
            rw [Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul]
            refine congrArg ((2 : ℂ)⁻¹ ^ mPayload • ·) ?_
            simp only [D_u, MomSlots01Slot1ProjKinetic.embedMatrix_diagonal, P_0, R_c,
              QRegister.basisOutcomeProjector_eq_diagonal, Matrix.diagonal_mul_diagonal]
            refine congrArg Matrix.diagonal (funext fun g ↦ ?_)
            by_cases h1 : pay.extractIndex g = 0
            · by_cases h2 : six.extractIndex g = coinSixOutcome c
              · simp [h1, h2]
              · simp [h1, h2]
            · simp [h1]
  rw [Finset.sum_congr rfl fun u _ ↦ hterm u, ← Finset.sum_mul, ← Finset.mul_sum]
  congr 2
  have hBc_diag : B_c = Matrix.diagonal (fun xSys ↦
      if c = 5 then bUnitTwosSlot1Geom cfg xSys xSys else 1) := by
    by_cases hc5 : c = 5
    · simp [B_c, hc5, bUnitTwosSlot1Geom]
    · simp [B_c, hc5, Matrix.diagonal_one]
  simp_rw [MomSlots01Slot1ProjKinetic.embedMatrix_diagonal]
  rw [hBc_diag, MomSlots01Slot1ProjKinetic.embedMatrix_diagonal]
  ext g₁ g₂
  by_cases hg : g₁ = g₂
  · subst hg
    simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.diagonal_apply_eq, smul_eq_mul,
      ← Finset.mul_sum]
    exact avg_geomPhaseScalar_sym (bBr := 29) (bR := 29) (bS := 21) rfl rfl rfl (by omega)
      cfg c (sys.extractIndex g₁)
  · simp [Matrix.sum_apply, hg]
theorem abs_slot1ValBranch_le_one (cfg : Configuration)
    (xSys : Fin (2 ^ SpecsAux.SpecMirror.systemQubits)) (b : Fin 6) :
    |slot1ValBranch cfg xSys b| ≤ 1 := by
  unfold slot1ValBranch
  dsimp only
  let u8 := u8FromFin (projAxisField xSys ⟨b.val / 2, by omega⟩)
  obtain ⟨hpR_nn, hpR_le, _, _⟩ := slot1PR_bounds u8
  have hm_le : (mag7Nat u8 : ℝ) ≤ 127 :=
    by exact_mod_cast (mag7Nat_u8FromFin_spec (projAxisField xSys ⟨b.val / 2, by omega⟩)).1
  have hm_nn : (0 : ℝ) ≤ (mag7Nat u8 : ℝ) := Nat.cast_nonneg _
  have hpS_nn : 0 ≤ ((16513 : ℝ) / (2 : ℝ) ^ 21) * (mag7Nat u8 : ℝ) :=
    mul_nonneg (by norm_num) hm_nn
  have hpS_le : ((16513 : ℝ) / (2 : ℝ) ^ 21) * (mag7Nat u8 : ℝ) ≤ 1 := by linarith
  split_ifs
  · exact abs_le.mpr ⟨by nlinarith, by nlinarith⟩
  · rw [abs_mul, abs_neg_one_pow, one_mul, abs_of_nonneg hpR_nn]
    exact hpR_le
theorem norm_bUnitTwosSlot1Geom_le_one (cfg : Configuration) :
    ‖bUnitTwosSlot1Geom cfg‖ ≤ 1 := by
  refine l2_opNorm_diagonal_le _ 1 zero_le_one fun xSys ↦ ?_
  rw [Complex.norm_real, Real.norm_eq_abs]
  refine (Finset.abs_sum_le_sum_abs _ _).trans
    ((Finset.sum_le_sum (g := fun b ↦ (slot1Delta cfg b : ℝ) / (2 : ℝ) ^ 29)
      fun b _ ↦ ?_).trans ?_)
  · have hd_nn : (0 : ℝ) ≤ (slot1Delta cfg b : ℝ) / (2 : ℝ) ^ 29 := by positivity
    rw [abs_mul, abs_of_nonneg hd_nn]
    exact mul_le_of_le_one_right hd_nn (abs_slot1ValBranch_le_one cfg xSys b)
  · simp_rw [div_eq_mul_inv, ← Finset.sum_mul]
    rw [← div_eq_mul_inv, div_le_one (by norm_num)]
    have hlt := slot1Tau_six_lt_two_pow_29 cfg
    rw [show slot1Tau cfg 6 = ∑ b : Fin 6, slot1Delta cfg b by
      simp [slot1Tau, sum_fin6_nat]] at hlt
    exact_mod_cast le_of_lt hlt
theorem bUnitTwosSlot1Geom_permElectron (cfg : Configuration)
    (g : Equiv.Perm (Fin numElectrons)) (x y : Fin (2 ^ SpecsAux.SpecMirror.systemQubits))
    (hx : IsGridState x) (_hy : IsGridState y) : (smToTwosSysUnitary.1 * bUnitTwosSlot1Geom
    cfg * smToTwosSysUnitary.1) (permElectron g x) (permElectron g y) = (smToTwosSysUnitary.1
    * bUnitTwosSlot1Geom cfg * smToTwosSysUnitary.1) x y := by
  rw [bUnitTwosSlot1Geom, smToTwosSys_conj_diagonal_slot1]
  by_cases hxy : x = y
  · subst hxy
    simp only [Matrix.diagonal_apply_eq, Function.comp_apply]
    have hproj_eq : ∀ w : Fin 3,
        projAxisField (smToTwosSysPerm (permElectron g x)) w =
          projAxisField (smToTwosSysPerm x) w := fun w ↦
      twosComp8Int_injective (by
        rw [twosComp8_smToTwosSys_eq_momentum ((isGridState_permElectron g x).mpr hx) w,
          twosComp8_smToTwosSys_eq_momentum hx w, momentum_permElectron_projectile])
    refine congrArg Complex.ofReal (Finset.sum_congr rfl fun b _ ↦ ?_)
    unfold slot1ValBranch
    dsimp only
    rw [hproj_eq]
  · rw [Matrix.diagonal_apply_ne _ (fun h ↦ hxy ((permElectron g).injective h)),
      Matrix.diagonal_apply_ne _ hxy]
noncomputable def slot1IdealValBranch (cfg : Configuration)
    (xSys : Fin (2 ^ SpecsAux.SpecMirror.systemQubits)) (b : Fin 6) : ℝ :=
  let w : Fin 3 := ⟨b.val / 2, by omega⟩
  let u8 := u8FromFin (projAxisField xSys w)
  let q : ℝ := (mag7Nat u8 : ℝ) / 127
  if b.val % 2 = 0 then
    2 * q ^ 2 - 1
  else
    ((-1 : ℝ) ^ (b2z (slot1Sigma cfg w) + u8 7).val) * q
theorem slot1BranchWeight_mul_idealVal_sum (cfg : Configuration)
    (xSys : Fin (2 ^ SpecsAux.SpecMirror.systemQubits)) :
    (∑ b : Fin 6, slot1BranchWeight cfg b * slot1IdealValBranch cfg xSys b) =
      ∑ w : Fin 3, projAxisTerm cfg (slot1AxisInt (projAxisField xSys w)) w := by
  have hbSign (s : Bool) (z : ZMod 2) :
      ((-1 : ℝ) ^ (b2z s + z).val) = (if s then -1 else 1) * (if z = 1 then -1 else 1) := by
    rw [show (b2z s + z).val = if (s != decide (z = 1)) then 1 else 0 from
      (by decide : ∀ (a : Bool) (b : ZMod 2),
        (b2z a + b).val = if (a != decide (b = 1)) then 1 else 0) s z]
    cases s
    · rcases bit_cases z with rfl | rfl
      · norm_num
      · norm_num
    · rcases bit_cases z with rfl | rfl
      · norm_num
      · norm_num
  have haxis (w : Fin 3) :
      slot1QuadBranchWeight *
          (2 * ((mag7Nat (u8FromFin (projAxisField xSys w)) : ℝ) / 127) ^ 2 - 1) +
        slot1LinBranchWeight cfg w *
          (((-1 : ℝ) ^ (b2z (slot1Sigma cfg w) +
            u8FromFin (projAxisField xSys w) 7).val) *
            ((mag7Nat (u8FromFin (projAxisField xSys w)) : ℝ) / 127)) =
      projAxisTerm cfg (slot1AxisInt (projAxisField xSys w)) w := by
    let u := projAxisField xSys w
    obtain ⟨_, hsign, hsq⟩ := mag7Nat_u8FromFin_spec u
    have hsqR : ((mag7Nat (u8FromFin u) : ℝ) ^ 2) = (slot1AxisInt u : ℝ) ^ 2 :=
      by exact_mod_cast hsq
    have hsignR : (if u8FromFin u 7 = 1 then -1 else (1 : ℝ)) * (mag7Nat (u8FromFin u) : ℝ) =
        (slot1AxisInt u : ℝ) := by
      by_cases h7 : u8FromFin u 7 = 1
      · rw [ite_eq_left h7] at hsign ⊢
        rw [neg_one_mul, ← hsign, Int.cast_neg, Int.cast_natCast]
      · rw [ite_eq_right h7] at hsign ⊢
        rw [one_mul, ← hsign, Int.cast_natCast]
    have hkw_abs : |waveVector cfg.projectileMomentum w| *
        (if decide (0 ≤ waveVector cfg.projectileMomentum w) then -1 else (1 : ℝ)) =
        -waveVector cfg.projectileMomentum w := by
      by_cases hkw : 0 ≤ waveVector cfg.projectileMomentum w
      · simp [hkw, abs_of_nonneg hkw]
      · simp [hkw, abs_of_neg (lt_of_not_ge hkw)]
    rw [hbSign]
    unfold slot1QuadBranchWeight slot1LinBranchWeight slot1Sigma projAxisTerm
    have h1 : (16129 / 2 : ℝ) * (2 * ((mag7Nat (u8FromFin u) : ℝ) / 127) ^ 2 - 1) =
        (mag7Nat (u8FromFin u) : ℝ) ^ 2 - 16129 / 2 := by ring
    calc _ = ((((16129 / 2 : ℝ) * (2 * ((mag7Nat (u8FromFin u) : ℝ) / 127) ^ 2 - 1)) *
            (gridKappa ^ 2 / 2)) + gridKappa *
            ((if u8FromFin u 7 = 1 then -1 else (1 : ℝ)) * (mag7Nat (u8FromFin u) : ℝ)) *
            (|waveVector cfg.projectileMomentum w| *
              (if decide (0 ≤ waveVector cfg.projectileMomentum w) then -1 else 1))) /
            projectileMass := by ring
      _ = _ := by
          rw [h1, hsqR, hsignR, hkw_abs]
          ring
  rw [sum_fin6_real, Fin.sum_univ_three, ← haxis 0, ← haxis 1, ← haxis 2]
  dsimp [slot1BranchWeight, slot1IdealValBranch]
  ring
theorem abs_slot1ValBranch_sub_ideal_quad (cfg : Configuration)
    (xSys : Fin (2 ^ SpecsAux.SpecMirror.systemQubits)) (b : Fin 6) (heven : b.val % 2 = 0) :
    |slot1ValBranch cfg xSys b - slot1IdealValBranch cfg xSys b| ≤
      2 * (1 / (2 : ℝ) ^ 29 + 1 / (2 : ℝ) ^ 21) := by
  unfold slot1ValBranch slot1IdealValBranch
  dsimp only
  rw [ite_pos_s1 heven, ite_pos_s1 heven]
  let w : Fin 3 := ⟨b.val / 2, by omega⟩
  let u8 := u8FromFin (projAxisField xSys w)
  obtain ⟨_, _, hdiffR_nn, hdiffR_le⟩ := slot1PR_bounds u8
  have hm_le : (mag7Nat u8 : ℝ) ≤ 127 :=
    by exact_mod_cast (mag7Nat_u8FromFin_spec (projAxisField xSys w)).1
  have hm_nn : (0 : ℝ) ≤ (mag7Nat u8 : ℝ) := Nat.cast_nonneg _
  let q : ℝ := (mag7Nat u8 : ℝ) / 127
  let pS : ℝ := ((16513 : ℝ) / (2 : ℝ) ^ 21) * (mag7Nat u8 : ℝ)
  have hq_le : q ≤ 1 := (div_le_one (by norm_num)).mpr hm_le
  have hpS_nn : 0 ≤ pS := mul_nonneg (by norm_num) hm_nn
  have hpS_le : pS ≤ 1 := by
    linarith [hm_le, show pS = ((16513 : ℝ) / (2 : ℝ) ^ 21) * (mag7Nat u8 : ℝ) from rfl]
  have hq_sub_pS : q - pS = q / (2 : ℝ) ^ 21 := by ring
  have hdiffS_nn : 0 ≤ q - pS := hq_sub_pS ▸ div_nonneg (div_nonneg hm_nn (by norm_num))
    (by positivity)
  have h1 : (q - slot1PR u8) * pS ≤ 1 / (2 : ℝ) ^ 29 :=
    (mul_le_of_le_one_right hdiffR_nn hpS_le).trans hdiffR_le
  have h2 : q * (q - pS) ≤ 1 / (2 : ℝ) ^ 21 := (mul_le_of_le_one_left hdiffS_nn hq_le).trans
    (hq_sub_pS ▸ div_le_div_of_nonneg_right hq_le (by norm_num))
  change |(2 * slot1PR u8 * pS - 1) - (2 * q ^ 2 - 1)| ≤ _
  rw [show (2 * slot1PR u8 * pS - 1) - (2 * q ^ 2 - 1) =
    -(2 * ((q - slot1PR u8) * pS + q * (q - pS))) by ring, abs_neg,
    abs_of_nonneg (mul_nonneg zero_le_two (add_nonneg (mul_nonneg hdiffR_nn hpS_nn)
      (mul_nonneg (div_nonneg hm_nn (by norm_num)) hdiffS_nn)))]
  dsimp only [q] at h1 h2 ⊢
  linarith
theorem abs_lambda_mul_delta_sub_weight (cfg : Configuration) (b : Fin 6) :
    |lambdaSlot1TpHi * ((slot1Delta cfg b : ℝ) / (2 : ℝ) ^ 29) - slot1BranchWeight cfg b| ≤
      (1 / 2 : ℝ) * (lambdaSlot1TpHi / (2 : ℝ) ^ 29) := by
  have hlam_pos : (0 : ℝ) < lambdaSlot1TpHi := by norm_num [lambdaSlot1TpHi]
  have hb := slot1BranchWeight_nonneg cfg b
  have hle : (slot1Delta cfg b : ℝ) ≤
      (2 : ℝ) ^ 29 * (slot1BranchWeight cfg b / lambdaSlot1TpHi) + (1 / 2 : ℝ) :=
    Nat.floor_le (by positivity)
  have hgt : (2 : ℝ) ^ 29 * (slot1BranchWeight cfg b / lambdaSlot1TpHi) - (1 / 2 : ℝ) <
      (slot1Delta cfg b : ℝ) := by
    unfold slot1Delta
    linarith [Nat.lt_floor_add_one
      ((2 : ℝ) ^ 29 * (slot1BranchWeight cfg b / lambdaSlot1TpHi) + (1 / 2 : ℝ))]
  have hscale : (0 : ℝ) < lambdaSlot1TpHi / (2 : ℝ) ^ 29 := by positivity
  have hid (c : ℝ) : (lambdaSlot1TpHi / (2 : ℝ) ^ 29) *
      ((2 : ℝ) ^ 29 * (slot1BranchWeight cfg b / lambdaSlot1TpHi) + c) =
      slot1BranchWeight cfg b + c * (lambdaSlot1TpHi / (2 : ℝ) ^ 29) := by
    field_simp [hlam_pos.ne']
  have hlhs : (lambdaSlot1TpHi / (2 : ℝ) ^ 29) * (slot1Delta cfg b : ℝ) =
      lambdaSlot1TpHi * ((slot1Delta cfg b : ℝ) / (2 : ℝ) ^ 29) := by ring
  exact abs_le.mpr ⟨by linarith [mul_lt_mul_of_pos_left hgt hscale, hid (-(1 / 2))],
    by linarith [mul_le_mul_of_nonneg_left hle hscale.le, hid (1 / 2)]⟩
theorem slot1QuadBranchWeight_le_ratHi :
    slot1QuadBranchWeight ≤ ((16129 / 2 : ℝ) * (gridKappaRatHi ^ 2 / 2)) / projectileMass :=
  div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left kappaSqHalf_le_ratHi (by norm_num))
    (by norm_num [projectileMass])
theorem sum_slot1LinBranchWeight_le_lambda (cfg : Configuration) : slot1LinBranchWeight cfg 0
    + slot1LinBranchWeight cfg 1 + slot1LinBranchWeight cfg 2 ≤ lambdaSlot1TpHi := by
  have hq_nn : 0 ≤ slot1QuadBranchWeight := slot1BranchWeight_nonneg cfg 0
  have hsum := sum_slot1BranchWeight_eq cfg
  rw [sum_fin6_real] at hsum
  dsimp only [slot1BranchWeight] at hsum
  linarith [projLiteralPrepWeight_le_414968_div_1000 cfg]
theorem bUnitTwosSlot1Geom_lambda_err_intr (cfg : SpecsAux.SpecMirror.Configuration)
    (spinUp : Finset (Fin numElectrons)) :
    let E_vec : Fin 6 → ℝ := fun j ↦ if j = 1 then projMidpointOffset cfg else 0
    ‖SpecsAux.SpecMirror.fermionicProjector spinUp *
        ((lambdaSlot1TpHi : ℂ) •
            (smToTwosSysUnitary.1 * bUnitTwosSlot1Geom cfg * smToTwosSysUnitary.1) -
          sixChannelShifted cfg E_vec 1) *
        SpecsAux.SpecMirror.fermionicProjector spinUp‖ ≤ (7 : ℝ) / 2000000 := by
  intro E_vec
  let P_F := SpecsAux.SpecMirror.fermionicProjector spinUp
  let G := SpecsAux.gridProjector
  let Δ := (lambdaSlot1TpHi : ℂ) • (smToTwosSysUnitary.1 * bUnitTwosSlot1Geom cfg *
      smToTwosSysUnitary.1) - sixChannelShifted cfg E_vec 1
  have heps_nn : (0 : ℝ) ≤ (7 : ℝ) / 2000000 := by norm_num
  rw [show P_F * Δ * P_F = P_F * (G * Δ * G) * P_F by
    have h1 := SpecsAux.fermionicProjector_mul_gridProjector spinUp
    calc P_F * Δ * P_F = (P_F * G) * Δ * (G * P_F) := by
            rw [h1, (SpecsAux.commute_fermionicProjector_gridProjector
              spinUp).symm.trans h1]
      _ = P_F * (G * Δ * G) * P_F := by simp only [Matrix.mul_assoc]]
  refine (norm_sandwich_le_of_norm_le_one P_F (G * Δ * G)
    (norm_fermionicProjector_le_one spinUp)).trans ?_
  rw [show G * Δ * G = Matrix.diagonal (fun x ↦ open Classical in
        if IsGridState x then (((lambdaSlot1TpHi * (∑ b : Fin 6,
          ((slot1Delta cfg b : ℝ) / (2 : ℝ) ^ 29) * slot1ValBranch cfg (smToTwosSysPerm x) b) -
          (waveNumberSq (SpecsAux.SpecMirror.momentum x .projectile - cfg.projectileMomentum) /
            (2 * projectileMass) - projMidpointOffset cfg)) : ℝ) : ℂ) else 0) by
    dsimp only [Δ, G]
    unfold sixChannelShifted
    rw [show sixChannelRaw cfg 1 = projectileKineticOp cfg from
        (projectileKineticOp_eq_matrixOf cfg).symm,
      show E_vec 1 = projMidpointOffset cfg by simp [E_vec],
      sixChannelGridProjector_eq_specsGridProjector, bUnitTwosSlot1Geom,
      smToTwosSys_conj_diagonal_slot1]
    classical
    unfold projectileKineticOp SpecsAux.gridProjector
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.diagonal_mul_diagonal]
    ext x y
    by_cases hxy : x = y
    · subst hxy
      by_cases hx : IsGridState x
      · simp [hx]
      · simp [hx]
    · simp [hxy]]
  refine l2_opNorm_diagonal_le _ _ heps_nn fun x ↦ ?_
  classical
  split_ifs with hx
  · rw [Complex.norm_real, Real.norm_eq_abs, ← sum_projAxisTerm_eq_centered cfg x]
    have haxis_int (w : Fin 3) : slot1AxisInt (projAxisField (smToTwosSysPerm x) w) =
        SpecsAux.SpecMirror.momentum x .projectile w := by
      have hmom := twosComp8_smToTwosSys_eq_momentum hx w
      have hne128 : (projAxisField (smToTwosSysPerm x) w).val ≠ 128 := fun h128 ↦ by
        have hle127 := abs_momentum_projectile_le_127 x w
        rw [← hmom, show twosComp8Int (projAxisField (smToTwosSysPerm x) w) = -128 by
          unfold twosComp8Int
          rw [h128]
          norm_num] at hle127
        norm_num at hle127
      unfold slot1AxisInt
      rw [ite_neg_s1 hne128]
      exact hmom
    rw [show (∑ w : Fin 3, projAxisTerm cfg (SpecsAux.SpecMirror.momentum x .projectile w) w) =
        ∑ b : Fin 6, slot1BranchWeight cfg b * slot1IdealValBranch cfg (smToTwosSysPerm x) b by
      rw [slot1BranchWeight_mul_idealVal_sum cfg (smToTwosSysPerm x)]
      exact Finset.sum_congr rfl fun w _ ↦ by rw [haxis_int w],
      Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum
      (g := fun b ↦ (1 / 2 : ℝ) * (lambdaSlot1TpHi / (2 : ℝ) ^ 29) + slot1BranchWeight cfg b *
        |slot1ValBranch cfg (smToTwosSysPerm x) b -
          slot1IdealValBranch cfg (smToTwosSysPerm x) b|) fun b _ ↦ ?_).trans ?_)
    · rw [show lambdaSlot1TpHi * (((slot1Delta cfg b : ℝ) / (2 : ℝ) ^ 29) *
          slot1ValBranch cfg (smToTwosSysPerm x) b) - slot1BranchWeight cfg b *
          slot1IdealValBranch cfg (smToTwosSysPerm x) b =
          (lambdaSlot1TpHi * ((slot1Delta cfg b : ℝ) / (2 : ℝ) ^ 29) -
            slot1BranchWeight cfg b) * slot1ValBranch cfg (smToTwosSysPerm x) b +
          slot1BranchWeight cfg b * (slot1ValBranch cfg (smToTwosSysPerm x) b -
            slot1IdealValBranch cfg (smToTwosSysPerm x) b) by ring]
      refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [abs_mul]
        exact (mul_le_of_le_one_right (abs_nonneg _)
          (abs_slot1ValBranch_le_one cfg _ b)).trans (abs_lambda_mul_delta_sub_weight cfg b)
      · rw [abs_mul, abs_of_nonneg (slot1BranchWeight_nonneg cfg b)]
    · rw [sum_fin6_real]
      have hqe := fun (b : Fin 6) (hb : b.val % 2 = 0) ↦ mul_le_mul_of_nonneg_left
        (abs_slot1ValBranch_sub_ideal_quad cfg (smToTwosSysPerm x) b hb)
        (slot1BranchWeight_nonneg cfg b)
      have hlo (b : Fin 6) (hodd : ¬(b.val % 2 = 0)) : slot1BranchWeight cfg b *
          |slot1ValBranch cfg (smToTwosSysPerm x) b -
            slot1IdealValBranch cfg (smToTwosSysPerm x) b| ≤
          slot1BranchWeight cfg b * (1 / (2 : ℝ) ^ 29) := by
        refine mul_le_mul_of_nonneg_left ?_ (slot1BranchWeight_nonneg cfg b)
        unfold slot1ValBranch slot1IdealValBranch
        dsimp only
        rw [ite_neg_s1 hodd, ite_neg_s1 hodd]
        obtain ⟨_, _, hdr0, hdr1⟩ :=
          slot1PR_bounds (u8FromFin (projAxisField (smToTwosSysPerm x) ⟨b.val / 2, by omega⟩))
        rw [show ∀ s a c : ℝ, s * a - s * c = -s * (c - a) from fun _ _ _ ↦ by ring,
          abs_mul, abs_neg, abs_neg_one_pow, one_mul, abs_of_nonneg hdr0]
        exact hdr1
      have hb0 := hqe 0 rfl
      have hb2 := hqe 2 rfl
      have hb4 := hqe 4 rfl
      have hb1 := hlo 1 (by decide)
      have hb3 := hlo 3 (by decide)
      have hb5 := hlo 5 (by decide)
      dsimp only [slot1BranchWeight] at hb0 hb1 hb2 hb3 hb4 hb5 ⊢
      have hquad_prod := mul_le_mul_of_nonneg_right slot1QuadBranchWeight_le_ratHi
        (show (0 : ℝ) ≤ 2 * (1 / (2 : ℝ) ^ 29 + 1 / (2 : ℝ) ^ 21) by norm_num)
      have hlin_prod := mul_le_mul_of_nonneg_right (sum_slot1LinBranchWeight_le_lambda cfg)
        (show (0 : ℝ) ≤ 1 / (2 : ℝ) ^ 29 by norm_num)
      have hnum : 6 * ((1 / 2 : ℝ) * (lambdaSlot1TpHi / (2 : ℝ) ^ 29)) +
          3 * ((((16129 / 2 : ℝ) * (gridKappaRatHi ^ 2 / 2)) / projectileMass) *
            (2 * (1 / (2 : ℝ) ^ 29 + 1 / (2 : ℝ) ^ 21))) +
          lambdaSlot1TpHi * (1 / (2 : ℝ) ^ 29) ≤ (7 : ℝ) / 2000000 := by
        norm_num [gridKappaRatHi, projectileMass, lambdaSlot1TpHi]
      linarith
  · simpa only [norm_zero] using heps_nn
end ConfigMomSlot1GeomPriority288
end MomSlot1GeomPriority288
namespace MomSlots01Slot1ProjKinetic
open Operator Matrix QProg Circuit _root_.DynamicCircuit DynCircuitExt HermitianMat Real
open SpecsAux SpecsAux.SpecMirror
open SpecsAux.PhaseGradCatalystCore
open SpecsAux.BridgeFermionicComm
open SpecsAux.BridgeFermionicComm.SpecInner
open FullSysPrepare6Slot
-- Root solution namespace already active.
open LiteralKineticAndMidpoint128
open scoped Matrix BigOperators Matrix.Norms.L2Operator
noncomputable def slot1ProjKineticOracleSym {mPayload : ℕ} (hmPay : 80 ≤ mPayload) :
    FullSysMomSlots0135Concrete.MomSingleSlotOracle mPayload 48 1 :=
  FullSysMomSlots0135Concrete.MomSingleSlotOracle.ofCoreOnly (mPayload := mPayload)
    (mPGTwist := 48) (k := 1) MomSlot1GeomPriority288.slot1GeomWorkWires
    (fun _ ↦ lambdaSlot1TpHi) projMidpointOffset
    (7 / 2000000) (MomSlot1GeomPriority288.slot1GeomSelectUnitary hmPay)
    MomSlot1GeomPriority288.bUnitTwosSlot1Geom
    (fun _ ↦ by
      unfold lambdaSlot1TpHi
      norm_num)
    (MomSlot1GeomPriority288.slot1GeomSelectDiag_conjTranspose hmPay)
    (fun cfg ↦ by
      rw [← momCoinProj_eq_fullSys mPayload (FullSysPrepare6Slot.fullSysCoinIdx 1)]
      exact MomSlot1GeomPriority288.slot1GeomSelectUnitary_offCoin hmPay cfg)
    (fun cfg ↦ by simpa [show FullSysPrepare6Slot.fullSysCoinIdx 1 = 5 from rfl] using
      MomSlot1GeomPriority288.slot1Geom_hadamard_topBlock_all hmPay cfg 5)
    MomSlot1GeomPriority288.norm_bUnitTwosSlot1Geom_le_one
    MomSlot1GeomPriority288.bUnitTwosSlot1Geom_permElectron
    MomSlot1GeomPriority288.bUnitTwosSlot1Geom_lambda_err_intr

end MomSlots01Slot1ProjKinetic
end
end ModMomSlots01Slot1ProjKinetic

section ModMomSlots35Coulomb
@[expose] public section
namespace MomSlots35Coulomb
open Operator Matrix QProg Circuit _root_.DynamicCircuit DynCircuitExt Real SpecsAux
open SpecsAux.SpecMirror SpecsAux.FullScaleBESector
open SpecsAux.BridgeFermionicComm
open SpecsAux.BridgeFermionicComm.SpecInner
open SpecsAux.PhaseGradCatalystCore
open MeasureBranchHadamardSem
open StreamingBchComparator
open scoped Matrix BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
section ClassicalAndGatePrimitives
abbrev uMat {N : ℕ} (U : unitaryGroup (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ := U.1
noncomputable abbrev ket {K : ℕ} (β : BitAssignment K) : Fin (2 ^ K) → ℂ :=
  basisState ((basisBitsEquiv K).symm β)
@[simp] theorem basisBits_symm_apply {K : ℕ} (β : BitAssignment K) : basisBits K
    ((basisBitsEquiv K).symm β) = β := (basisBitsEquiv K).apply_symm_apply β
@[simp] theorem symm_basisBits_apply {K : ℕ} (j : Fin (2 ^ K)) : (basisBitsEquiv K).symm
    (basisBits K j) = j := (basisBitsEquiv K).symm_apply_apply j
theorem zmod2_eq_or : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
@[simp] theorem zmod2_val_zero : (0 : ZMod 2).val = 0 := rfl
@[simp] theorem zmod2_val_one : (1 : ZMod 2).val = 1 := rfl
noncomputable def writeReg {K m : ℕ} (β : BitAssignment K) (r : QRegister m K)
    (γ : BitAssignment m) : BitAssignment K :=
  basisBits K (r.replaceIndex ((basisBitsEquiv K).symm β) ((basisBitsEquiv m).symm γ))
theorem writeReg_apply_of_not_mem {K m : ℕ} (β : BitAssignment K) (r : QRegister m K)
    (γ : BitAssignment m) (w : Wire K) (hw : w ∉ Set.range r.wires) :
    writeReg β r γ w = β w := by
  simp [writeReg, QRegister.basisBits_replaceIndex_of_not_mem _ _ _ _ hw]
noncomputable abbrev localIdx {K m : ℕ} (r : QRegister m K) (β : BitAssignment K) : Fin
    (2 ^ m) := (basisBitsEquiv m).symm (fun i ↦ β (r i))
theorem embedMatrix_mulVec_ket {K m : ℕ} (r : QRegister m K)
    (A : Matrix (Fin (2 ^ m)) (Fin (2 ^ m)) ℂ) (β : BitAssignment K) :
    (r.embedMatrix A).mulVec (ket β) =
      ∑ l : Fin (2 ^ m), A l (localIdx r β) • ket (writeReg β r (basisBits m l)) :=
  MomSlot0CircuitHalf.embedMatrix_mulVec_ket r A β
theorem eval_H_ket {K : ℕ} (q : Wire K) (β : BitAssignment K) :
    (uMat (Circuit.H q).eval).mulVec (ket β) = ((1 / √2 : ℝ) : ℂ) • ket
    (Function.update β q 0) + ((if (β q).val = 0 then (1 / √2 : ℝ) else -(1 / √2 : ℝ)) : ℂ) •
    ket (Function.update β q 1) := by
  rw [Circuit.H]
  erw [MomSlot0CircuitHalf.single_gate_mulVec_ket]
  rcases zmod2_eq_or (β q) with h | h
  · simp [h, MomSlot0CircuitHalf.uMat, PrimitiveGate.eval, Qubit.H]
  · simp [h, MomSlot0CircuitHalf.uMat, PrimitiveGate.eval, Qubit.H]
inductive RevProg (K : ℕ) : Type
  | nil : RevProg K
  | x (t : Wire K) : RevProg K
  | cnot (c t : Wire K) (h : c ≠ t) : RevProg K
  | toff (c₁ c₂ t : Wire K) (h₁₂ : c₁ ≠ c₂) (h₁t : c₁ ≠ t) (h₂t : c₂ ≠ t) : RevProg K
  | seq (p₁ p₂ : RevProg K) : RevProg K
namespace RevProg
def eval {K : ℕ} : RevProg K → BitAssignment K → BitAssignment K
  | .nil, β => β
  | .x t, β => Function.update β t (β t + 1)
  | .cnot c t _, β => Function.update β t (β t + β c)
  | .toff c₁ c₂ t _ _ _, β => Function.update β t (β t + β c₁ * β c₂)
  | .seq p₁ p₂, β => p₂.eval (p₁.eval β)

end RevProg
end ClassicalAndGatePrimitives
section UnsignedArithmetic
@[simp] theorem block_wires_eq {n : ℕ} (offset width : ℕ) (h : offset + width ≤ n)
    (j : Fin width) :
    (QRegister.block offset width h).wires j = ⟨offset + j.val, by omega⟩ := rfl
@[simp] theorem fin_one_add_eq_succ {m : ℕ} (j : Fin m) (h : 1 + j.val < m + 1) :
    (⟨1 + j.val, h⟩ : Fin (m + 1)) = j.succ := Fin.ext (Nat.add_comm 1 j.val)
@[simp] theorem slice_one_succ {K m : ℕ} (r : QRegister (m + 1) K) (h : 1 + m ≤ m + 1)
    (j : Fin m) : (r.slice 1 m h) j = r j.succ := by
  simp
end UnsignedArithmetic

end MomSlots35Coulomb
end
end ModMomSlots35Coulomb

section ModNuclearTwistAndXor654Concrete
@[expose] public section
namespace NuclearTwistAndXor654Concrete
open Operator QProg Matrix HermitianMat Real SpecsAux
open SpecsAux.SpecMirror
open SpecsAux.BridgeFermionicComm
open SpecsAux.BridgeFermionicComm.SpecInner DyadicQft64
open DyadicQft64Engine
open SpecsAux.PhaseGradCatalystCore
open SpecsAux.DyadicSubgridToeplitz128
open Slot2Slot4QuantizedChannelBridge
open AnchorTwistSelect
open SingleAnchorFermionicPauliCap
open scoped Matrix BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator Circuit.Notation
abbrev fullSysCoreWires (mPayload : ℕ) : ℕ := SpecsAux.SpecMirror.systemQubits + 6 + mPayload
abbrev mWorkTwist : ℕ := 256
noncomputable abbrev dyadicTurn (B : ℕ) (k : ℤ) : ℂ := turnPow2 B k
def IntertwinesLocalCat {kAct mCat : ℕ} (U_cat : Unitary (2 ^ mCat))
    (W_cat : Unitary (2 ^ (kAct + mCat))) (U_eff : Unitary (2 ^ kAct)) : Prop :=
  let rAct0 : QRegister kAct (kAct + mCat) := .block 0 kAct (by omega)
  let rCat0 : QRegister mCat (kAct + mCat) := .block kAct mCat le_rfl
  IntertwinesCatOp
    (rCat0.embedUnitary U_cat).1
    (rCat0.basisOutcomeProjector 0)
    W_cat.1
    (rAct0.embedUnitary U_eff).1
theorem IntertwinesLocalCat.mul {kAct mCat : ℕ} {U_cat : Unitary (2 ^ mCat)}
    {W₁ W₂ : Unitary (2 ^ (kAct + mCat))} {U₁ U₂ : Unitary (2 ^ kAct)}
    (h₁ : IntertwinesLocalCat U_cat W₁ U₁) (h₂ : IntertwinesLocalCat U_cat W₂ U₂) :
    IntertwinesLocalCat U_cat (W₂ * W₁) (U₂ * U₁) := by
  simpa only [IntertwinesLocalCat, Submonoid.coe_mul, QRegister.embedUnitary_mul] using
    IntertwinesCatOp.mul h₂ h₁
theorem IntertwinesLocalCat.inv {kAct mCat : ℕ} {U_cat : Unitary (2 ^ mCat)}
    {W_cat : Unitary (2 ^ (kAct + mCat))} {U_eff : Unitary (2 ^ kAct)}
    (h : IntertwinesLocalCat U_cat W_cat U_eff) :
    IntertwinesLocalCat U_cat W_cat⁻¹ U_eff⁻¹ := by
  let rAct0 : QRegister kAct (kAct + mCat) := .block 0 kAct (by omega)
  let rCat0 : QRegister mCat (kAct + mCat) := .block kAct mCat le_rfl
  change IntertwinesCatOp (rCat0.embedUnitary U_cat).1 (rCat0.basisOutcomeProjector 0)
    (W_cat⁻¹).1 (rAct0.embedUnitary U_eff⁻¹).1
  rw [congrArg Subtype.val (Unitary.star_eq_inv W_cat).symm,
    show (rAct0.embedUnitary U_eff⁻¹).1 = star (rAct0.embedUnitary U_eff).1 by
      rw [QRegister.embedUnitary_val, QRegister.embedUnitary_val, ← Unitary.star_eq_inv,
        Unitary.coe_star, Matrix.star_eq_conjTranspose, Matrix.star_eq_conjTranspose,
        rAct0.embedMatrix_conjTranspose]]
  exact IntertwinesCatOp.unitary_star
    (by rw [Matrix.star_eq_conjTranspose, QRegister.basisOutcomeProjector_conjTranspose])
    W_cat (rAct0.embedUnitary U_eff) h
theorem IntertwinesLocalCat.of_core_unitary {kAct mCat : ℕ} (U_cat : Unitary (2 ^ mCat))
    (U_eff : Unitary (2 ^ kAct)) : IntertwinesLocalCat U_cat
    ((QRegister.block 0 kAct (by omega)).embedUnitary U_eff) U_eff := by
  let rAct0 : QRegister kAct (kAct + mCat) := .block 0 kAct (by omega)
  let rCat0 : QRegister mCat (kAct + mCat) := .block kAct mCat le_rfl
  have hdisj : rAct0.DisjointWires rCat0 :=
    QRegister.block_disjoint_of_le 0 kAct kAct mCat (by omega) (by omega) (by omega)
  exact IntertwinesCatOp.refl_of_comm
    (rAct0.embedMatrix_comm_of_disjoint rCat0 hdisj U_eff.1 U_cat.1)
    ((QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint rAct0) rCat0 hdisj U_eff.1 0)
section ClassicalPrimitives
variable {n : ℕ}
theorem circuit_eval_eq_embed_perm_of_phasePerm {K : ℕ} [NeZero (2 ^ n)]
    (rTot : QRegister K n) (c : Circuit n) (perm : Equiv.Perm (Fin (2 ^ K)))
    (f : BitAssignment n → BitAssignment n) (hp : PhasePerm ⊤ c (fun _ ↦ 1) f)
    (hout : ∀ β w, w ∉ rTot.image → f β w = β w) (hloc : ∀ β : BitAssignment n, basisBits K
    (perm ((basisBitsEquiv K).symm (fun i ↦ β (rTot i)))) = fun i ↦ f β (rTot i)) : c.eval =
    rTot.embedUnitary (Operator.permutationUnitary perm) := by
  apply Subtype.ext
  suffices hcol : ∀ g : Fin (2 ^ n), c.eval.1.mulVec (Pi.single g (1 : ℂ)) =
      (rTot.embedUnitary (Operator.permutationUnitary perm)).1.mulVec (Pi.single g (1 : ℂ)) by
    ext i g
    simpa [Matrix.mulVec_single_one] using congrFun (hcol g) i
  intro g
  let β := basisBits n g
  let xloc : Fin (2 ^ K) := (basisBitsEquiv K).symm (fun i ↦ β (rTot i))
  rw [show (Pi.single g (1 : ℂ) : Fin (2 ^ n) → ℂ) = basisKet β by simp [basisKet, β],
    hp.evolve β, one_smul,
    show (rTot.embedUnitary (Operator.permutationUnitary perm)).1.mulVec (basisKet β) =
      Pi.single (rTot.replaceIndex g (perm xloc)) 1 by
      rw [show basisKet β = (Pi.single g (1 : ℂ) : Fin (2 ^ n) → ℂ) by simp [basisKet, β],
        QRegister.embedUnitary_val, rTot.embedMatrix_mulVec_single_factors,
        Operator.permutationUnitary_mulVec_single, rTot.tensorState_single_replaceIndex,
        (basisBitsEquiv K).injective (funext fun i ↦ (rTot.basisBits_extractIndex g i).trans
          (congrFun ((basisBitsEquiv K).apply_symm_apply (fun j ↦ β (rTot j))) i).symm)]]
  simp only [basisKet]
  refine congrArg (Pi.single · (1 : ℂ)) ((basisBitsEquiv n).injective (funext fun w ↦ ?_))
  rw [Equiv.apply_symm_apply]
  by_cases hw : w ∈ rTot.image
  · obtain ⟨i, rfl⟩ := (QRegister.mem_image rTot w).mp hw
    exact (congrFun (hloc β) i).symm.trans (rTot.basisBits_replaceIndex_apply g _ i).symm
  · exact (hout β w hw).trans (rTot.basisBits_replaceIndex_of_not_mem g _ w
      (fun hr ↦ hw ((QRegister.mem_image rTot w).mpr hr))).symm
theorem phasePerm_X (q : Wire n) :
    PhasePerm ⊤ (Circuit.X q) (fun _ ↦ 1) (fun β ↦ Function.update β q (β q + 1)) :=
  PhasePerm.of_classicalPerm (ClassicalPerm.X q) (fun _ x h ↦ absurd (Finset.mem_univ x) h)
theorem phasePerm_CNOT (c t : Wire n) (h : c ≠ t) :
    PhasePerm ⊤ (Circuit.CNOT c t h) (fun _ ↦ 1) (fun β ↦ Function.update β t (β t + β c)) :=
  PhasePerm.of_classicalPerm (ClassicalPerm.CNOT c t h)
    (fun _ x hm ↦ absurd (Finset.mem_univ x) hm)
theorem phasePerm_TOFF (c₁ c₂ t : Wire n) (h₁₂ : c₁ ≠ c₂) (h₁t : c₁ ≠ t) (h₂t : c₂ ≠ t) :
    PhasePerm ⊤ (Circuit.TOFF c₁ c₂ t h₁₂ h₁t h₂t) (fun _ ↦ 1)
    (fun β ↦ Function.update β t (β t + β c₁ * β c₂)) := PhasePerm.of_classicalPerm
    (ClassicalPerm.TOFF c₁ c₂ t h₁₂ h₁t h₂t) (fun _ x hm ↦ absurd (Finset.mem_univ x) hm)
@[simp] theorem count_inverse_toff (d : Circuit n) :
    d.inverse.count .TOFF = d.count .TOFF := by
  induction d with
  | identity => rfl
  | gate g _ =>
      cases g
      all_goals rfl
  | seq _ _ ih₁ ih₂ =>
      simpa only [Circuit.inverse, Circuit.count_seq, ih₁, ih₂] using Nat.add_comm _ _
theorem count_inverse_t_of_zero {d : Circuit n} (hd : d.count .T = 0) :
    d.inverse.count .T = 0 := by
  induction d with
  | identity => rfl
  | gate g r =>
      cases g with
      | t => simp [Circuit.count] at hd
      | _ => simp [Circuit.inverse, Circuit.inverseGate, Circuit.count]
  | seq d₁ d₂ ih₁ ih₂ =>
      simp only [Circuit.count_seq] at hd
      simp [Circuit.inverse, ih₁ (by omega), ih₂ (by omega)]
theorem circuit_inverse_evolve_of_evolve {cComp : Circuit n} {β γ : BitAssignment n}
    (h : cComp.eval.1.mulVec (basisKet β) = basisKet γ) :
    cComp.inverse.eval.1.mulVec (basisKet γ) = basisKet β := by
  rw [Circuit.eval_inverse, ← h, Matrix.mulVec_mulVec]
  have hinv : (cComp.eval⁻¹).1 * cComp.eval.1 = 1 :=
    congrArg Subtype.val (inv_mul_cancel cComp.eval)
  rw [hinv, Matrix.one_mulVec]
end ClassicalPrimitives
noncomputable def nuclearM48 (c : Configuration) (l : Fin 216) (w : Fin 3) : ℕ :=
  ⌊(2 ^ 48 : ℝ) * Int.fract (c.nuclei l w / cellVolume ^ (1 / 3 : ℝ)) + 1 / 2⌋₊ % 2 ^ 48
noncomputable def oneElectronPhase48 (c : Configuration) (l : Fin 216) (p : Fin 3 → ℤ) : ℂ :=
  dyadicTurn 48 (-(∑ w : Fin 3, p w * (nuclearM48 c l w : ℤ)))
noncomputable def uenSubGridKet48 (c : Configuration) (l : Fin 216)
    (b : NyqParity3D) (y : NyqGrid3D64) (u : Fin (2 ^ 18)) : ℂ :=
  oneElectronPhase48 c l (shiftedMom3D (elecOffsetGridEquiv18 u)) * veeSubGridKet b y u
section CoreLayout
variable {mPayload n : ℕ}
def rElecCore (rCore : QRegister (fullSysCoreWires mPayload) n) : QRegister 3924 n :=
  rCore.slice 0 3924 (show 0 + 3924 ≤ 3954 + mPayload by omega)
def rElecSlot (rCore : QRegister (fullSysCoreWires mPayload) n) (e : Fin numElectrons) :
    QRegister 18 n :=
  rCore.slice (18 * e.val) 18 (by
    have := e.isLt
    simp [fullSysCoreWires, SpecsAux.SpecMirror.systemQubits, SpecsAux.SpecMirror.numElectrons,
      SpecsAux.SpecMirror.electronBits, SpecsAux.SpecMirror.projectileBits] at *
    omega)
def rElecAxis654 (rCore : QRegister (fullSysCoreWires mPayload) n) (a : Fin 654) :
    QRegister 6 n := rCore.slice (6 * a.val) 6 (show 6 * a.val + 6 ≤ 3954 + mPayload by
  have := a.isLt
  omega)
def rElecSlotAxis (rCore : QRegister (fullSysCoreWires mPayload) n)
    (e : Fin numElectrons) (w : Fin 3) : QRegister 6 n :=
  rCore.slice (18 * e.val + 6 * w.val) 6 (show 18 * e.val + 6 * w.val + 6 ≤ 3954 + mPayload by
    have : e.val < 218 := e.isLt
    have : w.val < 3 := w.isLt
    omega)
def wSlot0 (rCore : QRegister (fullSysCoreWires mPayload) n) : Wire n :=
  rCore ⟨3948, show 3948 < 3954 + mPayload by omega⟩
def wSlot1 (rCore : QRegister (fullSysCoreWires mPayload) n) : Wire n :=
  rCore ⟨3949, show 3949 < 3954 + mPayload by omega⟩
def wSlot2 (rCore : QRegister (fullSysCoreWires mPayload) n) : Wire n :=
  rCore ⟨3950, show 3950 < 3954 + mPayload by omega⟩
def rCosetB1 (hm : 22 ≤ mPayload) (rCore : QRegister (fullSysCoreWires mPayload) n) :
    QRegister 3 n := rCore.slice 3954 3 (show 3954 + 3 ≤ 3954 + mPayload by omega)
def rCosetB0 (hm : 22 ≤ mPayload) (rCore : QRegister (fullSysCoreWires mPayload) n) :
    QRegister 3 n := rCore.slice 3957 3 (show 3957 + 3 ≤ 3954 + mPayload by omega)
def rNucIdx (hm : 22 ≤ mPayload) (rCore : QRegister (fullSysCoreWires mPayload) n) :
    QRegister 8 n := rCore.slice 3960 8 (show 3960 + 8 ≤ 3954 + mPayload by omega)
def rAnchorIdx (hm : 22 ≤ mPayload) (rCore : QRegister (fullSysCoreWires mPayload) n) :
    QRegister 8 n := rCore.slice 3968 8 (show 3968 + 8 ≤ 3954 + mPayload by omega)
end CoreLayout
section ConcreteCircuits
variable {Var : Type} {mPayload n : ℕ}
lemma reg_ne_of_ne {K : ℕ} (r : QRegister K n) {i j : Fin K} (h : i.val ≠ j.val) : r i ≠ r j
    := r.wires.injective.ne (fun heq ↦ h (congrArg Fin.val heq))
lemma disj_wire_ne {K₁ K₂ : ℕ} {r₁ : QRegister K₁ n} {r₂ : QRegister K₂ n}
    (hd : r₁.DisjointWires r₂) (i : Fin K₁) (j : Fin K₂) : r₁ i ≠ r₂ j :=
  QRegister.DisjointWires.ne hd i j
theorem dyn_seq_toff_zero {a b : DynamicCircuit Var n} (ha : a.count .TOFF = 0)
    (hb : b.count .TOFF = 0) : (DynamicCircuit.seq a b).count .TOFF = 0 := by
  change a.count .TOFF + b.count .TOFF = 0
  omega
theorem _root_.QuantumComputation.Specs.StoppingPowerSolution.OperatorExt.permutationUnitary_mul
    {d : ℕ} (e₁ e₂ : Equiv.Perm (Fin d)) :
    Operator.permutationUnitary (e₁ * e₂) =
      Operator.permutationUnitary e₁ * Operator.permutationUnitary e₂ := by
  apply Subtype.ext
  simp [Operator.permutationUnitary, _root_.mul_inv_rev, Matrix.permMatrix_mul]
def dXor32All654 (rCore : QRegister (fullSysCoreWires mPayload) n) : DynamicCircuit Var n :=
  .circuit (parallelBit5FlipAxes (rElecAxis654 rCore))
@[simp] theorem count_dXor32All654_toff (rCore : QRegister (fullSysCoreWires mPayload) n) :
    (dXor32All654 (Var := Var) rCore).count .TOFF = 0 :=
  count_parallelBit5FlipAxes_toff (rElecAxis654 rCore)
@[simp] theorem count_dXor32All654_t (rCore : QRegister (fullSysCoreWires mPayload) n) :
    (dXor32All654 (Var := Var) rCore).count .T = 0 :=
  count_parallelBit5FlipAxes_t (rElecAxis654 rCore)
attribute [local irreducible] dXor32All654
end ConcreteCircuits
section PhysicsAndNormBridges
theorem norm_exp_ofReal_mul_I_sub_le (a b : ℝ) :
    ‖Complex.exp ((a : ℂ) * Complex.I) - Complex.exp ((b : ℂ) * Complex.I)‖ ≤ |a - b| := by
  have hfactor : Complex.exp ((a : ℂ) * Complex.I) - Complex.exp ((b : ℂ) * Complex.I) =
      Complex.exp (((a + b) / 2 : ℝ) * Complex.I) *
        ((2 : ℂ) * Complex.I * Real.sin ((a - b) / 2)) := by
    rw [show (a : ℂ) * Complex.I =
          (((a + b) / 2 : ℝ) : ℂ) * Complex.I + (((a - b) / 2 : ℝ) : ℂ) * Complex.I by
        push_cast; ring,
      show (b : ℂ) * Complex.I =
          (((a + b) / 2 : ℝ) : ℂ) * Complex.I + ((-((a - b) / 2) : ℝ) : ℂ) * Complex.I by
        push_cast; ring,
      Complex.exp_add, Complex.exp_add, ← mul_sub]
    simp only [Complex.exp_mul_I, Complex.ofReal_neg, Complex.cos_neg, Complex.sin_neg,
      ← Complex.ofReal_sin]
    ring
  rw [hfactor, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, norm_mul, norm_mul,
    Complex.norm_two, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  have hsin := Real.abs_sin_le_abs (x := (a - b) / 2)
  rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at hsin
  linarith
noncomputable def oneElecNucDiag48 (c : Configuration) (l : Fin 216) : Unitary (2 ^ 18) :=
  ⟨Matrix.diagonal fun u : Fin (2 ^ 18) ↦
    oneElectronPhase48 c l (shiftedMom3D (elecOffsetGridEquiv18 u)), by
    rw [Matrix.mem_unitaryGroup_iff']
    change (Matrix.diagonal _)ᴴ * Matrix.diagonal _ = 1
    rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    exact congrArg Matrix.diagonal (funext fun _ ↦ by
      simpa only [Pi.star_apply, oneElectronPhase48, dyadicTurn] using
        star_turnPow2_mul_self 48 _)⟩
noncomputable def oneElecNucDiagExact (c : Configuration) (l : Fin 216) : Unitary (2 ^ 18) :=
  ⟨Matrix.diagonal fun u : Fin (2 ^ 18) ↦
    oneElectronPhase (c.nuclei l) (shiftedMom3D (elecOffsetGridEquiv18 u)), by
    rw [Matrix.mem_unitaryGroup_iff']
    change (Matrix.diagonal _)ᴴ * Matrix.diagonal _ = 1
    rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    exact congrArg Matrix.diagonal (funext fun _ ↦ by
      simp [Pi.star_apply, oneElectronPhase, RCLike.star_def, ← Complex.exp_conj,
        ← Complex.exp_add])⟩
theorem l2_opNorm_unitary_le_one {D : ℕ} (U : Unitary D) : ‖U.1‖ ≤ 1 := by
  have hsq : ‖U.1‖ * ‖U.1‖ = ‖(1 : Operator D)‖ := by
    rw [← Matrix.l2_opNorm_conjTranspose_mul_self U.1,
      show U.1ᴴ * U.1 = 1 by simpa [Matrix.star_eq_conjTranspose] using
        Matrix.mem_unitaryGroup_iff'.mp U.2]
  have hone : ‖(1 : Operator D)‖ ≤ 1 := by
    rw [← Matrix.diagonal_one, Matrix.l2_opNorm_diagonal]
    exact (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun _ ↦ by simp
  nlinarith [norm_nonneg U.1]
noncomputable def sysNucDiag48 (c : Configuration) (l : Fin 216) : Unitary (2 ^ systemQubits) :=
  (List.ofFn fun e : Fin numElectrons ↦ (rEl_sp e).embedUnitary (oneElecNucDiag48 c l)).prod
noncomputable def slot4CosetDiag18 (b₀ b₁ : NyqParity3D) : Unitary (2 ^ 18) :=
  ⟨Matrix.diagonal fun u : Fin (2 ^ 18) ↦
    ∏ w : Fin 3, dyadicTurn 48 ((2 ^ 41 : ℤ) *
      ((((b₁ w).val : ℤ) - ((b₀ w).val : ℤ)) * ((elecOffsetGridEquiv18 u w).val : ℤ))), by
    rw [Matrix.mem_unitaryGroup_iff']
    change (Matrix.diagonal _)ᴴ * Matrix.diagonal _ = 1
    rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    exact congrArg Matrix.diagonal (funext fun _ ↦ by
      simpa only [Pi.star_apply, star_prod, ← Finset.prod_mul_distrib, dyadicTurn] using
        Finset.prod_eq_one fun _ _ ↦ star_turnPow2_mul_self 48 _)⟩
theorem dyadicTurn48_shift41_eq_omega128 (m : ℤ) :
    dyadicTurn 48 ((2 ^ 41 : ℤ) * m) = omega128 m := by
  rw [dyadicTurn, turnPow2_scale_pow 41 7 m]
  unfold turnPow2 DyadicQft64.dyadicTurn SpecsAux.DyadicSubgridToeplitz128.omega128
  congr 1
  ring_nf
theorem slot4_barrelSwap_and_coset_conj {ι : Type*} [Fintype ι] (b₀ b₁ : NyqParity3D)
    (y : NyqGrid3D64) (χ₀ χ₁ : ι → Fin (2 ^ 18) → ℂ) (f : ι → ι) (i : Fin numElectrons) :
    (slot4CosetDiag18 b₀ b₁).1ᴴ * rk1_sp (veeSubGridKet b₁ y) * (slot4CosetDiag18 b₀ b₁).1 =
    rk1_sp (veeSubGridKet b₀ y) ∧
    (Operator.permutationUnitary (permElectron (Equiv.swap i 0))).1ᴴ * singleAnchorPairOp χ₀
    χ₁ f 0 * (Operator.permutationUnitary (permElectron (Equiv.swap i 0))).1 =
    singleAnchorPairOp χ₀ χ₁ f i := by
  refine ⟨?_, swapWireZero_conj_singleAnchorPairOp χ₀ χ₁ f i⟩
  have hstar_om := SpecsAux.DyadicSubgridToeplitz128.star_omega128
  have hmul_om (a b : ℤ) : omega128 a * omega128 b = omega128 (a + b) :=
    (SpecsAux.DyadicSubgridToeplitz128.omega128_add a b).symm
  let cConst : ℂ := ∏ w : Fin 3, omega128 (-(32 : ℤ) * (((b₁ w).val : ℤ) - ((b₀ w).val : ℤ)))
  have hc_norm : cConst * star cConst = 1 := by
    simp only [cConst, star_prod, ← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one fun w _ ↦ ?_
    rw [hstar_om, hmul_om, add_neg_cancel]
    exact SpecsAux.DyadicSubgridToeplitz128.omega128_zero
  let d (u : Fin (2 ^ 18)) : ℂ := ∏ w : Fin 3, dyadicTurn 48 ((2 ^ 41 : ℤ) * ((((b₁ w).val
      : ℤ) - ((b₀ w).val : ℤ)) * ((elecOffsetGridEquiv18 u w).val : ℤ)))
  have hpt (u : Fin (2 ^ 18)) : star (d u) * veeSubGridKet b₁ y u =
      cConst * veeSubGridKet b₀ y u := by
    unfold veeSubGridKet subGridUnitary64 subGridElem64_3D
    simp only [d, cConst, Matrix.of_apply, star_prod, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun w _ ↦ ?_
    rw [dyadicTurn48_shift41_eq_omega128]
    unfold subGridElem64_1D shiftedMom3D shiftedFin64ToInt
    simp only [star_mul, hstar_om, ← mul_assoc, hmul_om]
    exact congrArg (· * _) (congrArg omega128 (by ring))
  ext u v
  change ((Matrix.diagonal d)ᴴ * Matrix.of (fun u v ↦ veeSubGridKet b₁ y u *
      star (veeSubGridKet b₁ y v)) * Matrix.diagonal d) u v =
    veeSubGridKet b₀ y u * star (veeSubGridKet b₀ y v)
  rw [Matrix.diagonal_conjTranspose, Matrix.mul_diagonal, Matrix.diagonal_mul]
  simp only [Pi.star_apply, Matrix.of_apply]
  have hv := congrArg star (hpt v)
  simp only [star_mul, star_star] at hv
  linear_combination (veeSubGridKet b₀ y u * star (veeSubGridKet b₀ y v)) * hc_norm +
    (star (veeSubGridKet b₁ y v) * d v) * hpt u + (cConst * veeSubGridKet b₀ y u) * hv
end PhysicsAndNormBridges
end NuclearTwistAndXor654Concrete
end
end ModNuclearTwistAndXor654Concrete

end QuantumComputation.Specs.StoppingPowerSolution
