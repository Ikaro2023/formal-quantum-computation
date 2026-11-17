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

public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.CatalystPrepSpine

@[expose] public section
set_option allowUnsafeReducibility true

namespace QuantumComputation.Specs.StoppingPowerSolution
open SpecsAux

section ModPosSlots24SemanticOracleConcrete80
@[expose] public section
namespace PosSlots24SemanticOracleConcrete80Alt
theorem qreg_ext {k n : ℕ} {r s : QRegister k n} (h : ∀ i, r i = s i) : r = s :=
  QRegister.ext (Function.Embedding.ext h)
theorem qreg_block_apply {n : ℕ} (offset width : ℕ) (h : offset + width ≤ n) (i : Fin width) :
    QRegister.block offset width h i = ⟨offset + i.val, by omega⟩ := rfl
theorem qreg_block_wires_apply {n : ℕ} (offset width : ℕ) (h : offset + width ≤ n) (i : Fin width) :
    (QRegister.block offset width h).wires i = ⟨offset + i.val, by omega⟩ := rfl
theorem qreg_slice_wires {k n : ℕ} (r : QRegister k n) (offset width : ℕ)
    (h : offset + width ≤ k) (i : Fin width) :
    (r.slice offset width h).wires i = r.wires ⟨offset + i.val, by omega⟩ := rfl
theorem qreg_compose_wires {m k n : ℕ} (outer : QRegister k n) (inner : QRegister m k) (i : Fin m) :
    (outer.compose inner).wires i = outer.wires (inner.wires i) := rfl
theorem qreg_whole_wires {n : ℕ} (i : Fin n) : (QRegister.whole n).wires i = i := rfl
theorem emb_refl_apply {α : Type*} (x : α) : (Function.Embedding.refl α) x = x := rfl
theorem emb_mk_apply {α β : Type*} (f : α → β) (h : Function.Injective f) (x : α) :
    ({ toFun := f, inj' := h } : α ↪ β) x = f x := rfl
theorem emb_trans_apply {α β γ : Type*} (f : α ↪ β) (g : β ↪ γ) (x : α) :
    (f.trans g) x = g (f x) := rfl
end PosSlots24SemanticOracleConcrete80Alt
namespace PosSlots24SemanticOracleConcrete80
section ConfigPosSlots24SemanticOracleConcrete80
set_option exponentiation.threshold 256
theorem finPow2_ext_of_basisBits {K : ℕ} {i j : Fin (2 ^ K)}
    (h : ∀ q : Wire K, basisBits K i q = basisBits K j q) : i = j :=
  (basisBitsEquiv K).injective (funext h)
theorem basisBits_symm_injective {K : ℕ} {f g : BitAssignment K}
    (h : (basisBitsEquiv K).symm f = (basisBitsEquiv K).symm g) : f = g :=
  (basisBitsEquiv K).symm.injective h
theorem basisBits_symm_apply_fun {K : ℕ} (f : BitAssignment K) (idx : Wire K) :
    basisBits K ((basisBitsEquiv K).symm f) idx = f idx :=
  congrFun ((basisBitsEquiv K).apply_symm_apply f) idx
open Operator Matrix Real SpecsAux.SpecMirror
open PosSlots24SemanticBridge
open CanonRank7Circuit (fineCoordOfReg21)
open Dyadic128CoulombMath (orbitCount47905)
open PosSlots24BranchConcrete
  (posCoreWires wSlot0Core wSlot1Core wSlot2Core tailAndSlackPhaseBitSpec uPosPhase)
open PosSlots24PartnerMux288 (basisBits_symm_apply_at)
open scoped Matrix ComplexOrder MatrixOrder Circuit.Notation Matrix.Norms.L2Operator BigOperators
local instance (priority := 1000000) instNeZeroTwoPowCoh80 (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩
def pos80HeadWeightNat : ℕ := 727884457843
def pos80TailWeightNat : ℕ := 6388384375
def pos80Slot2TotNat : ℕ := pos80HeadWeightNat + 218 * pos80TailWeightNat
def pos80Slot4TotNat : ℕ := pos80HeadWeightNat + 217 * pos80TailWeightNat
noncomputable def pos80Slot2Scale : ℝ := (216 : ℝ) * (pos80Slot2TotNat : ℝ) / (8 * 2 ^ 30)
noncomputable def pos80Slot4Scale : ℝ := (218 : ℝ) * (pos80Slot4TotNat : ℝ) / (16 * 2 ^ 30)
theorem pos80Slot2Scale_pos : 0 < pos80Slot2Scale := by
  norm_num [pos80Slot2Scale, pos80Slot2TotNat, pos80HeadWeightNat, pos80TailWeightNat]
theorem pos80Slot4Scale_pos : 0 < pos80Slot4Scale := by
  norm_num [pos80Slot4Scale, pos80Slot4TotNat, pos80HeadWeightNat, pos80TailWeightNat]
def coreBetaOf (s0 : Bool) (p80 : BitAssignment 80) (z : Fin (2 ^ SpecsAux.SpecMirror.systemQubits))
    : BitAssignment posCoreWires := PosSlots24TopWrapper.writeSubBits
    PosSlots24TopWrapper.rPosSubLocal (fun w ↦ if hw : w.val < SpecsAux.SpecMirror.systemQubits then
    basisBits SpecsAux.SpecMirror.systemQubits z ⟨w.val, hw⟩ else if w.val == 3948 then (if s0 then
    1 else 0) else 0) p80
noncomputable def coreIdxOf {kCore : ℕ} (hk : posCoreWires = kCore) (s0 : Bool)
    (p80 : BitAssignment 80) (z : Fin (2 ^ SpecsAux.SpecMirror.systemQubits)) : Fin (2 ^ kCore) :=
    hk ▸ (basisBitsEquiv posCoreWires).symm (coreBetaOf s0 p80 z)
theorem sysBlockAtPayloadGen_apply {kCore : ℕ} (hk : posCoreWires = kCore)
    (M : Operator (2 ^ kCore)) (s0 : Bool) (p80 : BitAssignment 80)
    (x' x : Fin (2 ^ SpecsAux.SpecMirror.systemQubits)) : sysBlockAtPayloadGen hk M s0 p80 x' x = M
    (coreIdxOf hk s0 p80 x') (coreIdxOf hk s0 p80 x) := rfl
lemma lt_sys_4034 : SpecsAux.SpecMirror.systemQubits < 4034 := by decide
theorem coreBetaOf_lt3948 (s0 : Bool) (p80 : BitAssignment 80)
    (z : Fin (2 ^ SpecsAux.SpecMirror.systemQubits)) (w : Fin SpecsAux.SpecMirror.systemQubits) :
    coreBetaOf s0 p80 z ⟨w.val, Nat.lt_trans w.isLt lt_sys_4034⟩ =
      basisBits SpecsAux.SpecMirror.systemQubits z w := by
  rw [coreBetaOf, PosSlots24TopWrapper.writeSubBits_rPosSubLocal_lt3954 _ p80 _
    (Nat.lt_trans w.isLt (by decide))]
  simp only [w.isLt, ↓reduceDIte]
theorem coreBetaOf_mid (s0 : Bool) (p80 : BitAssignment 80)
    (z : Fin (2 ^ SpecsAux.SpecMirror.systemQubits))
    (w : Wire posCoreWires) (hlo : SpecsAux.SpecMirror.systemQubits ≤ w.val) (hhi : w.val < 3954) :
    coreBetaOf s0 p80 z w = (if w.val == 3948 then (if s0 then 1 else 0) else 0) := by
  rw [coreBetaOf, PosSlots24TopWrapper.writeSubBits_rPosSubLocal_lt3954 _ p80 w hhi]
  simp only [Nat.not_lt.mpr hlo, ↓reduceDIte]
theorem coreBetaOf_payload (s0 : Bool) (p80 : BitAssignment 80)
    (z : Fin (2 ^ SpecsAux.SpecMirror.systemQubits)) (j : Fin 80) :
    coreBetaOf s0 p80 z (PosSlots24TopWrapper.rPosSubLocal j) = p80 j :=
  PosSlots24TopWrapper.writeSubBits_apply_mem PosSlots24TopWrapper.rPosSubLocal _ p80 j
theorem coreIdxOf_injective {kCore : ℕ} (hk : posCoreWires = kCore) (s0 : Bool)
    (p80 : BitAssignment 80) : Function.Injective (coreIdxOf hk s0 p80) := by
  subst hk
  exact fun x y hxy ↦ finPow2_ext_of_basisBits fun w ↦ by
    rw [← coreBetaOf_lt3948 s0 p80 x w, ← coreBetaOf_lt3948 s0 p80 y w,
      basisBits_symm_injective hxy]
open Classical in
noncomputable def extendZero {α β M : Type*} [Zero M] (f : α → β) (g : α → M) (b : β) : M :=
  if h : ∃ a, f a = b then g (Classical.choose h) else 0
theorem extendZero_apply {α β M : Type*} [Zero M] {f : α → β} (hf : Function.Injective f)
    (g : α → M) (a : α) : extendZero f g (f a) = g a := by
  have hex : ∃ a', f a' = f a := ⟨a, rfl⟩
  simp only [extendZero, hex, ↓reduceDIte, hf (Classical.choose_spec hex)]
theorem extendZero_of_not_exists {α β M : Type*} [Zero M] (f : α → β) (g : α → M) {b : β}
    (hb : ¬ ∃ a, f a = b) : extendZero f g b = 0 := by simp [extendZero, hb]
theorem sum_extendZero {α β M : Type*} [Fintype α] [Fintype β]
    [AddCommMonoid M] {f : α → β} (hf : Function.Injective f) (g : α → M) :
    (∑ b : β, extendZero f g b) = ∑ a : α, g a := by
  classical
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image f))
      (fun b _ hb ↦ extendZero_of_not_exists f g fun ⟨a, ha⟩ ↦
        hb (Finset.mem_image.mpr ⟨a, Finset.mem_univ a, ha⟩)),
    Finset.sum_image (fun _ _ _ _ h ↦ hf h)]
  exact Finset.sum_congr rfl fun a _ ↦ extendZero_apply hf g a
theorem norm_sysBlockAtPayloadGen_le_one {kCore : ℕ} (hk : posCoreWires = kCore)
    (U : Unitary (2 ^ kCore)) (s0 : Bool) (p80 : BitAssignment 80) : ‖sysBlockAtPayloadGen hk
    U.1 s0 p80‖ ≤ 1 := le_trans
    (SpecsAux.SubmatrixOpNorm.l2_opNorm_le_of_submatrix ⟨coreIdxOf hk s0
    p80, coreIdxOf_injective hk s0 p80⟩ (sysBlockAtPayloadGen hk U.1 s0 p80) U.1
    (sysBlockAtPayloadGen_apply hk U.1 s0 p80)) (le_of_eq (CStarRing.norm_of_mem_unitary U.2))
theorem sysBlockAtPayloadGen_conjTranspose {kCore : ℕ} (hk : posCoreWires = kCore)
    (M : Operator (2 ^ kCore)) (s0 : Bool) (p80 : BitAssignment 80) :
    (sysBlockAtPayloadGen hk M s0 p80)ᴴ = sysBlockAtPayloadGen hk Mᴴ s0 p80 := by
  funext x' x
  simp only [Matrix.conjTranspose_apply, sysBlockAtPayloadGen_apply]
def PreservesCoreAnc {kCore : ℕ} (hk : posCoreWires = kCore) (M : Operator (2 ^ kCore))
    (s0 : Bool) (p80 : BitAssignment 80) : Prop :=
  ∀ x row, M row (coreIdxOf hk s0 p80 x) ≠ 0 → ∃ y, row = coreIdxOf hk s0 p80 y
theorem sysBlockAtPayloadGen_mul_of_preserves {kCore : ℕ} (hk : posCoreWires = kCore)
    (B M : Operator (2 ^ kCore)) (s0 : Bool) (p80 : BitAssignment 80)
    (hM : PreservesCoreAnc hk M s0 p80) : sysBlockAtPayloadGen hk (B * M) s0 p80 =
    sysBlockAtPayloadGen hk B s0 p80 * sysBlockAtPayloadGen hk M s0 p80 := by
  funext x' x
  simp only [sysBlockAtPayloadGen_apply, Matrix.mul_apply]
  let f := coreIdxOf hk s0 p80
  have hf : Function.Injective f := coreIdxOf_injective hk s0 p80
  refine (Finset.sum_congr rfl fun row _ ↦ ?_).trans
    (sum_extendZero hf fun y ↦ B (f x') (f y) * M (f y) (f x))
  by_cases hr : ∃ y, f y = row
  · obtain ⟨y, rfl⟩ := hr
    exact (extendZero_apply hf (fun y ↦ B (f x') (f y) * M (f y) (f x)) y).symm
  · rw [Classical.not_not.mp fun hne ↦ (hM x row hne).elim fun y hy ↦ hr ⟨y, hy.symm⟩,
      mul_zero, extendZero_of_not_exists f _ hr]
theorem sysBlockAtPayloadGen_conj_of_preserves {kCore : ℕ} (hk : posCoreWires = kCore)
    (M D : Operator (2 ^ kCore)) (s0 : Bool) (p80 : BitAssignment 80)
    (hM : PreservesCoreAnc hk M s0 p80) (hDM : PreservesCoreAnc hk (D * M) s0 p80) :
    sysBlockAtPayloadGen hk (Mᴴ * D * M) s0 p80 = (sysBlockAtPayloadGen hk M s0 p80)ᴴ *
    sysBlockAtPayloadGen hk D s0 p80 * sysBlockAtPayloadGen hk M s0 p80 := by
  rw [Matrix.mul_assoc, sysBlockAtPayloadGen_mul_of_preserves hk Mᴴ (D * M) s0 p80 hDM,
    sysBlockAtPayloadGen_mul_of_preserves hk D M s0 p80 hM,
    sysBlockAtPayloadGen_conjTranspose, Matrix.mul_assoc]
noncomputable def coherentSysOp80 (qft : FullSysCatSegmentBridge.FullSysQft654Bundle)
    (cfg : SpecsAux.SpecMirror.Configuration) (s0 : Bool) (α : BitAssignment 80 → ℝ) :
    Operator (2 ^ SpecsAux.SpecMirror.systemQubits) :=
  ∑ p80 : BitAssignment 80, (α p80 : ℂ) •
    sysBlockAtPayloadGen pos24_coreWires80_eq.symm (pos24ConjCore80 qft cfg).1 s0 p80
theorem norm_le_one_of_isProj {k : ℕ} (P : Operator (2 ^ k))
    (hsa : Pᴴ = P) (hidem : P * P = P) : ‖P‖ ≤ 1 := by
  have hsq : ‖P‖ * ‖P‖ = ‖P‖ := by
    rw [← CStarRing.norm_star_mul_self (x := P), Matrix.star_eq_conjTranspose, hsa, hidem]
  nlinarith [norm_nonneg P]
theorem embedMatrix_entry_of_agreeOutside {k N : ℕ} (rSub : QRegister k N)
    (X : Operator (2 ^ k)) {row col : Fin (2 ^ N)} (h : rSub.AgreeOutside row col) :
    (rSub.embedMatrix X) row col = X (rSub.extractIndex row) (rSub.extractIndex col) := by
  simp [QRegister.embedMatrix_apply, (rSub.basisSplit_environment_eq_iff row col).mpr h]
theorem embedMatrix_entry_of_not_agreeOutside {k N : ℕ} (rSub : QRegister k N)
    (X : Operator (2 ^ k)) {row col : Fin (2 ^ N)} (h : ¬rSub.AgreeOutside row col) :
    (rSub.embedMatrix X) row col = 0 := by
  simp [QRegister.embedMatrix_apply, mt (rSub.basisSplit_environment_eq_iff row col).mp h]
theorem comm_conjTranspose_of_selfAdj {k : ℕ} {U P : Operator (2 ^ k)} (hP : Pᴴ = P)
    (hComm : U * P = P * U) : Uᴴ * P = P * Uᴴ := by
  simpa only [Matrix.conjTranspose_mul, hP] using (congrArg conjTranspose hComm).symm
theorem regVal_eq_of_wire_eq {m N : ℕ} (r : QRegister m N) (β₁ β₂ : BitAssignment N)
    (heq : ∀ i : Fin m, β₁ (r i) = β₂ (r i)) : regVal r β₁ = regVal r β₂ := by
  unfold regVal
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  dsimp only
  rw [heq i]
theorem posPhaseBit_eq_of_eq_outside_scratch16 (slot2SwappedTo0 : Bool)
    (tailSign : Fin orbitCount47905 → Bool) (tailMag30 : Fin orbitCount47905 → Fin (2 ^ 30))
    (β₁ β₂ : BitAssignment posCoreWires) (heq : ∀ q : Wire posCoreWires, ¬(4017 ≤ q.val ∧
    q.val < 4033) → β₁ q = β₂ q) : PosSlots24BranchConcrete.posPhaseBit slot2SwappedTo0
    tailSign tailMag30 β₁ = PosSlots24BranchConcrete.posPhaseBit slot2SwappedTo0 tailSign
    tailMag30 β₂ := by
  let rC := QRegExt.ofFin posCoreWires
  have heq' (n : ℕ) (hn : n < 4034) (h : ¬(4017 ≤ n ∧ n < 4033)) : β₁ ⟨n, hn⟩ = β₂ ⟨n, hn⟩ :=
    heq ⟨n, hn⟩ h
  have hslot (e : Fin 218) :
      PosSlots24BranchConcrete.slotSubGridCoord64 (PosSlots24BranchConcrete.rElecSlot rC e) β₁ =
      PosSlots24BranchConcrete.slotSubGridCoord64 (PosSlots24BranchConcrete.rElecSlot rC e) β₂ :=
    funext fun w ↦ Fin.ext (regVal_eq_of_wire_eq _ β₁ β₂ fun i ↦
      heq' (18 * e.val + (6 * w.val + (5 - i.val))) (by omega) (by omega))
  have hpar0 : PosSlots24BranchConcrete.parity3OfReg (PosSlots24BranchConcrete.rCosetB0 rC) β₁ =
      PosSlots24BranchConcrete.parity3OfReg (PosSlots24BranchConcrete.rCosetB0 rC) β₂ :=
    funext fun w ↦ congrArg (decide <| · = 1) (heq' (3954 + (3 + w.val)) (by omega) (by omega))
  have hpar1 : PosSlots24BranchConcrete.parity3OfReg (PosSlots24BranchConcrete.rCosetB1 rC) β₁ =
      PosSlots24BranchConcrete.parity3OfReg (PosSlots24BranchConcrete.rCosetB1 rC) β₂ :=
    funext fun w ↦ congrArg (decide <| · = 1) (heq' (3954 + (0 + w.val)) (by omega) (by omega))
  have hf21 : fineCoordOfReg21 (PosSlots24BranchConcrete.rHeadFine21 rC) β₁ =
      fineCoordOfReg21 (PosSlots24BranchConcrete.rHeadFine21 rC) β₂ :=
    funext fun w ↦ Fin.ext (regVal_eq_of_wire_eq _ β₁ β₂ fun i ↦
      heq' (3954 + (32 + (7 * w.val + i.val))) (by omega) (by omega))
  have hnuc := regVal_eq_of_wire_eq (PosSlots24BranchConcrete.rNucIdx rC) β₁ β₂ fun i ↦
    heq' (3954 + (6 + i.val)) (by omega) (by omega)
  have hanc := regVal_eq_of_wire_eq (PosSlots24BranchConcrete.rAnchorIdx rC) β₁ β₂ fun i ↦
    heq' (3954 + (14 + i.val)) (by omega) (by omega)
  have hpart := regVal_eq_of_wire_eq (PosSlots24BranchConcrete.rPartnerIdx rC) β₁ β₂ fun i ↦
    heq' (3954 + (22 + i.val)) (by omega) (by omega)
  have hkeep := regVal_eq_of_wire_eq (PosSlots24BranchConcrete.rTailKeep30 rC) β₁ β₂ fun i ↦
    heq' (3954 + (32 + i.val)) (by omega) (by omega)
  have hw0 : β₁ (wSlot0Core rC) = β₂ (wSlot0Core rC) := heq' 3948 (by decide) (by decide)
  have hw1 : β₁ (wSlot1Core rC) = β₂ (wSlot1Core rC) := heq' 3949 (by decide) (by decide)
  have hw2 : β₁ (wSlot2Core rC) = β₂ (wSlot2Core rC) := heq' 3950 (by decide) (by decide)
  have hwsub : β₁ (PosSlots24BranchConcrete.wSubReject rC) =
      β₂ (PosSlots24BranchConcrete.wSubReject rC) := heq' 4016 (by decide) (by decide)
  have hwhd : β₁ (PosSlots24BranchConcrete.wIsHead rC) =
      β₂ (PosSlots24BranchConcrete.wIsHead rC) := heq' 3984 (by decide) (by decide)
  have hwht : β₁ (PosSlots24BranchConcrete.wHeadThresh rC) =
      β₂ (PosSlots24BranchConcrete.wHeadThresh rC) := heq' 3985 (by decide) (by decide)
  have hwrz : β₁ (PosSlots24BranchConcrete.wRejectZero rC) =
      β₂ (PosSlots24BranchConcrete.wRejectZero rC) := heq' 4033 (by decide) (by decide)
  unfold PosSlots24BranchConcrete.posPhaseBit
  rw [show PosSlots24BranchConcrete.headPhaseBitSpec β₁ =
      PosSlots24BranchConcrete.headPhaseBitSpec β₂ by
    unfold PosSlots24BranchConcrete.headPhaseBitSpec
    simp only [rC, hw0, hw1, hw2, hwsub, hwhd, hwht, hnuc, hanc, hf21, hpar0, hslot],
    show tailAndSlackPhaseBitSpec slot2SwappedTo0 tailSign tailMag30 β₁ =
      tailAndSlackPhaseBitSpec slot2SwappedTo0 tailSign tailMag30 β₂ by
    unfold tailAndSlackPhaseBitSpec
    simp only [rC, hw0, hw1, hw2, hwsub, hwhd, hwrz, hnuc, hanc, hpart, hkeep, hpar0, hpar1,
      hslot]]
abbrev QftPreservesCoset3 (qft : FullSysCatSegmentBridge.FullSysQft654Bundle) : Prop := ∀ o
    : Fin 8, qft.uQft654.1 * DyadicQft64WalkCircuit.rCoset3In654.basisOutcomeProjector o =
    DyadicQft64WalkCircuit.rCoset3In654.basisOutcomeProjector o * qft.uQft654.1
theorem qftPreservesCoset3_of_eq_ideal
    (qft : FullSysCatSegmentBridge.FullSysQft654Bundle)
    (hEq : qft.uQft654 = DyadicQft64WalkCircuit.qft64Ideal654Unitary) :
    QftPreservesCoset3 qft := fun o ↦
  hEq ▸ DyadicQft64WalkCircuit.qft64Ideal654Unitary_comm_cosetProj o
theorem basisOutcomeProjector_compose_local {k₁ k₂ N : ℕ}
    (r₁ : QRegister k₁ N) (r₂ : QRegister k₂ k₁) (o : Fin (2 ^ k₂)) :
    (r₁.compose r₂).basisOutcomeProjector o = r₁.embedMatrix (r₂.basisOutcomeProjector o) := by
  rw [QRegister.basisOutcomeProjector, QRegister.basisOutcomeProjector,
    QRegister.embedMatrix_compose]
theorem diag_mul_diag_eq {k : ℕ} (P₁ P₂ Q : Fin (2 ^ k) → Prop) [DecidablePred P₁]
    [DecidablePred P₂] [DecidablePred Q] (hiff : ∀ x, Q x ↔ P₁ x ∧ P₂ x) :
    (Matrix.diagonal fun x ↦ if Q x then (1 : ℂ) else 0) =
    (Matrix.diagonal fun x ↦ if P₁ x then (1 : ℂ) else 0) *
    (Matrix.diagonal fun x ↦ if P₂ x then (1 : ℂ) else 0) := by
  rw [Matrix.diagonal_mul_diagonal]
  refine congrArg Matrix.diagonal (funext fun x ↦ ?_)
  simp only [hiff x]
  split_ifs
  all_goals simp_all
theorem diagonal_comm_diagonal {M : Type*} [Fintype M] [DecidableEq M] (d₁ d₂ : M → ℂ) :
    Matrix.diagonal d₁ * Matrix.diagonal d₂ = Matrix.diagonal d₂ * Matrix.diagonal d₁ := by
  rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  exact congrArg Matrix.diagonal (funext fun _ ↦ mul_comm _ _)
theorem uPosPhase_cast_comm_diagonal {kCore : ℕ} (hk : posCoreWires = kCore)
    (slot2SwappedTo0 : Bool) (tailSign : Fin orbitCount47905 → Bool)
    (tailMag30 : Fin orbitCount47905 → Fin (2 ^ 30)) (d : Fin (2 ^ kCore) → ℂ) :
    (castUnitaryPow2 hk (uPosPhase slot2SwappedTo0 tailSign tailMag30)).1 * Matrix.diagonal d
    = Matrix.diagonal d * (castUnitaryPow2 hk (uPosPhase slot2SwappedTo0 tailSign
    tailMag30)).1 := by
  subst hk
  dsimp only [castUnitaryPow2, uPosPhase,
    BchCubeDecoder.diagonalSignUnitaryN,
    BchCubeDecoder.diagonalSignUnitary]
  exact diagonal_comm_diagonal _ d
def rAncFlag80 : QRegister 86 (FullSysCatSegmentBridge.fullSysCoreWires 80) :=
  QRegister.block 3948 86 (by decide)
def rAncRest83 : QRegister 83 (FullSysCatSegmentBridge.fullSysCoreWires 80) :=
  (QRegister.block 3948 6 (by decide)).concat (QRegister.block 3957 77 (by decide))
    (QRegister.block_disjoint_of_le 3948 6 3957 77 (by decide) (by decide) (by decide))
theorem coreElecCosetB1_compose_rCoset3 : (FullSysCatSegmentBridge.coreElecCosetB1Block
    pos24_6_le_80).compose DyadicQft64WalkCircuit.rCoset3In654 =
    FullSysCatSegmentBridge.coreCosetB1Block pos24_6_le_80 :=
  PosSlots24SemanticOracleConcrete80Alt.qreg_ext fun j ↦ by
    change (FullSysCatSegmentBridge.coreElecCosetB1Block pos24_6_le_80)
        (DyadicQft64WalkCircuit.rCoset3In654 j) = _
    rw [show DyadicQft64WalkCircuit.rCoset3In654 j = Fin.natAdd 3924 j from Fin.ext rfl,
      QRegister.concat_apply_right]
private theorem rAncRest83_eq (k : Fin 83) :
    rAncRest83 k = rAncFlag80 ⟨if k.val < 6 then k.val else 3 + k.val, by
      split_ifs
      all_goals omega⟩ := Fin.ext <| by
  dsimp only [rAncFlag80, PosSlots24SemanticOracleConcrete80Alt.qreg_block_apply]
  by_cases hk : k.val < 6
  · rw [ite_eq_left hk, show k = Fin.castAdd 77 ⟨k.val, hk⟩ from Fin.ext rfl, rAncRest83,
      QRegister.concat_apply_left]
    rfl
  · rw [ite_eq_right hk, show k = Fin.natAdd 6 (⟨k.val - 6, by omega⟩ : Fin 77) from
        Fin.ext (Nat.add_sub_of_le (Nat.not_lt.mp hk)).symm, rAncRest83,
      QRegister.concat_apply_right]
    simp only [PosSlots24SemanticOracleConcrete80Alt.qreg_block_apply, Fin.val_natAdd]
    omega
theorem coreElecCosetB1_disjoint_rAncRest83 :
    (FullSysCatSegmentBridge.coreElecCosetB1Block pos24_6_le_80).DisjointWires rAncRest83 :=
  QRegister.disjoint_iff.mpr fun i k hik ↦ by
    have hv := congrArg Fin.val (hik.trans (rAncRest83_eq k))
    by_cases hi : i.val < 3924
    · rw [show i = Fin.castAdd 3 ⟨i.val, hi⟩ from Fin.ext rfl,
        FullSysCatSegmentBridge.coreElecCosetB1Block, QRegister.concat_apply_left] at hv
      simp only [FullSysCatSegmentBridge.coreElecBlock, rAncFlag80,
        PosSlots24SemanticOracleConcrete80Alt.qreg_block_apply] at hv
      split_ifs at hv
      all_goals omega
    · rw [show i = Fin.natAdd 3924 ⟨i.val - 3924, by omega⟩ from
          Fin.ext (Nat.add_sub_of_le (Nat.not_lt.mp hi)).symm,
        FullSysCatSegmentBridge.coreElecCosetB1Block, QRegister.concat_apply_right] at hv
      simp only [FullSysCatSegmentBridge.coreCosetB1Block, rAncFlag80,
        PosSlots24SemanticOracleConcrete80Alt.qreg_block_apply] at hv
      split_ifs at hv
      all_goals omega
theorem rAncFlag80_basisOutcomeProjector_factor (a : Fin (2 ^ 86)) : ∃ (o3 : Fin (2 ^ 3))
    (o83 : Fin (2 ^ 83)), rAncFlag80.basisOutcomeProjector a =
    (FullSysCatSegmentBridge.coreCosetB1Block pos24_6_le_80).basisOutcomeProjector o3 *
    rAncRest83.basisOutcomeProjector o83 := by
  let bitsA := basisBits 86 a
  refine ⟨(basisBitsEquiv 3).symm fun j ↦ bitsA ⟨6 + j.val, by omega⟩, (basisBitsEquiv 83).symm
    fun k ↦ bitsA ⟨if k.val < 6 then k.val else 3 + k.val, by
      split_ifs
      all_goals omega⟩, ?_⟩
  rw [QRegister.basisOutcomeProjector_eq_diagonal, QRegister.basisOutcomeProjector_eq_diagonal,
    QRegister.basisOutcomeProjector_eq_diagonal]
  refine diag_mul_diag_eq _ _ _ fun x ↦ ?_
  have hw3 : ∀ j : Fin 3, FullSysCatSegmentBridge.coreCosetB1Block pos24_6_le_80 j =
      rAncFlag80 ⟨6 + j.val, by omega⟩ := fun j ↦ Fin.ext (by
    dsimp only [FullSysCatSegmentBridge.coreCosetB1Block, rAncFlag80,
      PosSlots24SemanticOracleConcrete80Alt.qreg_block_apply]
    omega)
  simp only [← (basisBitsEquiv 86).apply_eq_iff_eq, ← (basisBitsEquiv 3).apply_eq_iff_eq,
    ← (basisBitsEquiv 83).apply_eq_iff_eq, funext_iff]
  change (∀ idx : Fin 86, basisBits 86 (rAncFlag80.extractIndex x) idx = bitsA idx) ↔
    (∀ j : Fin 3, basisBits 3 ((FullSysCatSegmentBridge.coreCosetB1Block
      pos24_6_le_80).extractIndex x) j = _) ∧
    (∀ k : Fin 83, basisBits 83 (rAncRest83.extractIndex x) k = _)
  simp only [QRegister.basisBits_extractIndex, Equiv.apply_symm_apply]
  refine ⟨fun h ↦ ⟨fun j ↦ by rw [hw3 j, h], fun k ↦ by rw [rAncRest83_eq k, h]⟩, ?_⟩
  rintro ⟨h3, h83⟩ idx
  by_cases h1 : idx.val < 6
  · simpa only [rAncRest83_eq, h1, ↓reduceIte] using h83 ⟨idx.val, by omega⟩
  · by_cases h2 : idx.val < 9
    · simpa only [hw3, show (⟨6 + (idx.val - 6), by omega⟩ : Fin 86) = idx from
        Fin.ext (show 6 + (idx.val - 6) = idx.val by omega)] using h3 ⟨idx.val - 6, by omega⟩
    · simpa only [rAncRest83_eq, show ¬(idx.val - 3 < 6) by omega, ↓reduceIte,
        show (⟨3 + (idx.val - 3), by omega⟩ : Fin 86) = idx from
          Fin.ext (show 3 + (idx.val - 3) = idx.val by omega)] using
        h83 ⟨idx.val - 3, by omega⟩
theorem ofFin_embedUnitary_eq {N : ℕ} (U : Unitary (2 ^ N)) :
    (QRegExt.ofFin N).embedUnitary U = U := by
  ext row col
  rw [QRegister.embedUnitary_val,
    embedMatrix_entry_of_agreeOutside _ _ (fun q hnot ↦ False.elim (hnot ⟨q, rfl⟩))]
  have hex : ∀ z : Fin (2 ^ N), (QRegExt.ofFin N).extractIndex z = z :=
    fun _ ↦ finPow2_ext_of_basisBits fun _ ↦ QRegister.basisBits_extractIndex _ _ _
  rw [hex row, hex col]
theorem uTwistParam_cast_comm_highReg_proj {kCore : ℕ}
    (hk : NuclearTwistAndXor654Concrete.fullSysCoreWires 80 = kCore)
    (cfg : SpecsAux.SpecMirror.Configuration) (rAnc : QRegister 86 kCore)
    (hAncLo : ∀ j : Fin 86, 3948 ≤ (rAnc j).val) (a : Fin (2 ^ 86)) :
    (castUnitaryPow2 hk (NuclearTwistRealizes.uTwistParam true pos24_22_le_80 cfg)).1 *
      rAnc.basisOutcomeProjector a =
    rAnc.basisOutcomeProjector a *
      (castUnitaryPow2 hk (NuclearTwistRealizes.uTwistParam true pos24_22_le_80 cfg)).1 := by
  subst hk
  let rId := QRegExt.ofFin (NuclearTwistAndXor654Concrete.fullSysCoreWires 80)
  have hDisj : (NuclearTwistAndXor654Concrete.rElecCore rId).DisjointWires rAnc :=
    QRegister.disjoint_iff.mpr fun i j hij ↦ by
      have hv : 0 + i.val = (rAnc j).val := congrArg Fin.val hij
      have hi : i.val < 3924 := i.isLt
      have hj := hAncLo j
      omega
  dsimp only [castUnitaryPow2]
  have hcomm := NuclearTwistRealizes.uTwistParam_comm_highReg_proj true pos24_22_le_80 cfg rId
    rAnc hDisj a
  rwa [ofFin_embedUnitary_eq] at hcomm
lemma rAncFlag80_wire_ge_3948 (j : Fin 86) : 3948 ≤ (rAncFlag80 j).val :=
  Nat.le_add_right 3948 j.val
theorem entry_zero_of_comm_basisOutcomeProjector {K m : ℕ} (r : QRegister m K)
    (M : Operator (2 ^ K)) (hComm : ∀ a : Fin (2 ^ m), M * r.basisOutcomeProjector a =
      r.basisOutcomeProjector a * M) (row col : Fin (2 ^ K))
    (hne : r.extractIndex row ≠ r.extractIndex col) : M row col = 0 := by
  have hc := congrFun (congrFun (hComm (r.extractIndex col)) row) col
  rw [QRegister.basisOutcomeProjector_eq_diagonal, Matrix.mul_diagonal, Matrix.diagonal_mul] at hc
  simpa [hne] using hc
lemma ancIdx86_sub_lt (idx : Fin (FullSysFullPrepareAndTopConcrete.selWiresSym 80))
    (h : ¬ idx.val < 6) : idx.val - 6 < 80 :=
  Nat.sub_lt_left_of_lt_add (Nat.not_lt.mp h) idx.isLt
noncomputable def ancIdx86 (s0 : Bool) (p80 : BitAssignment 80) :
    Fin (2 ^ FullSysFullPrepareAndTopConcrete.selWiresSym 80) :=
  (basisBitsEquiv (FullSysFullPrepareAndTopConcrete.selWiresSym 80)).symm fun idx ↦
    if idx.val == 0 then (if s0 then 1 else 0)
    else if hlt : idx.val < 6 then 0 else p80 ⟨idx.val - 6, ancIdx86_sub_lt idx hlt⟩
theorem ancIdx86_injective (s0 : Bool) : Function.Injective (ancIdx86 s0) := fun p₁ p₂ h ↦ by
  funext j
  simpa only [show ((6 + j.val) == 0) = false by simp, Bool.false_eq_true, ↓reduceIte,
    show ¬(6 + j.val < 6) by omega, ↓reduceDIte,
    show (⟨6 + j.val - 6, _⟩ : Fin 80) = j from
      Fin.ext (Nat.add_sub_cancel_left 6 j.val)] using
    congrFun (basisBits_symm_injective h) ⟨6 + j.val, show 6 + j.val < 86 by omega⟩
theorem coreWiresSym80_eq_fullSys : FullSysCatSegmentBridge.fullSysCoreWires 80 =
    FullSysFullPrepareAndTopConcrete.coreWiresSym 80 := rfl
theorem basisOutcomeProjector_sandwich_apply {K m : ℕ} (r : QRegister m K) (a : Fin (2 ^ m))
    (X : Operator (2 ^ K)) (row col : Fin (2 ^ K)) :
    (r.basisOutcomeProjector a * X * r.basisOutcomeProjector a) row col =
    (if r.extractIndex row = a then (1 : ℂ) else 0) * X row col *
    (if r.extractIndex col = a then (1 : ℂ) else 0) := by
  rw [QRegister.basisOutcomeProjector_eq_diagonal r a, Matrix.mul_diagonal, Matrix.diagonal_mul]
abbrev hkSym80 : posCoreWires = FullSysFullPrepareAndTopConcrete.coreWiresSym 80 :=
  pos24_coreWires80_eq.symm.trans coreWiresSym80_eq_fullSys
private theorem pos80_coreIdxOf_bits (s0 : Bool) (p80 : BitAssignment 80)
    (z : Fin (2 ^ SpecsAux.SpecMirror.systemQubits))
    (q : Wire (FullSysFullPrepareAndTopConcrete.coreWiresSym 80)) :
    basisBits (FullSysFullPrepareAndTopConcrete.coreWiresSym 80)
      (coreIdxOf hkSym80 s0 p80 z) q = coreBetaOf s0 p80 z ⟨q.val, q.isLt⟩ := by
  have hgen : ∀ {kC : ℕ} (hk : posCoreWires = kC) (q' : Wire kC),
      basisBits kC (coreIdxOf hk s0 p80 z) q' = coreBetaOf s0 p80 z ⟨q'.val, hk ▸ q'.isLt⟩ := by
    rintro kC rfl q'
    exact basisBits_symm_apply_at (coreBetaOf s0 p80 z) q'
  exact hgen hkSym80 q
theorem pos80_coreIdxOf_extract_sys (s0 : Bool) (p80 : BitAssignment 80)
    (z : Fin (2 ^ SpecsAux.SpecMirror.systemQubits)) :
    (FullSysFullPrepareAndTopConcrete.coreSysSym 80).extractIndex
      (coreIdxOf hkSym80 s0 p80 z) = z :=
  finPow2_ext_of_basisBits fun w ↦ by
    rw [QRegister.basisBits_extractIndex, pos80_coreIdxOf_bits,
      show (⟨(FullSysFullPrepareAndTopConcrete.coreSysSym 80 w).val, _⟩ : Wire posCoreWires) =
        ⟨w.val, Nat.lt_trans w.isLt lt_sys_4034⟩ from Fin.ext (Nat.zero_add w.val)]
    exact coreBetaOf_lt3948 s0 p80 z w
theorem pos80_coreIdxOf_extract_anc (s0 : Bool) (p80 : BitAssignment 80)
    (z : Fin (2 ^ SpecsAux.SpecMirror.systemQubits)) :
    (FullSysFullPrepareAndTopConcrete.coreAncSym 80).extractIndex
      (coreIdxOf hkSym80 s0 p80 z) = ancIdx86 s0 p80 :=
  finPow2_ext_of_basisBits fun idx ↦ by
    have hpc : posCoreWires = 4034 ∧ SpecsAux.SpecMirror.systemQubits = 3948 ∧
        FullSysFullPrepareAndTopConcrete.selWiresSym 80 = 86 := ⟨rfl, rfl, rfl⟩
    rw [QRegister.basisBits_extractIndex, pos80_coreIdxOf_bits, ancIdx86, basisBits_symm_apply_fun]
    by_cases hlt : idx.val < 6
    · rw [show (⟨(FullSysFullPrepareAndTopConcrete.coreAncSym 80 idx).val,
          (FullSysFullPrepareAndTopConcrete.coreAncSym 80 idx).isLt⟩ : Wire posCoreWires) =
          ⟨3948 + idx.val, by omega⟩ from Fin.ext rfl,
        coreBetaOf_mid s0 p80 z _ (Nat.le_add_right 3948 idx.val)
          (show 3948 + idx.val < 3954 by omega)]
      by_cases h0 : idx.val = 0
      · simp [h0]
      · simp [h0, hlt, beq_false_of_ne (show 3948 + idx.val ≠ 3948 by omega)]
    · simp only [beq_false_of_ne (show idx.val ≠ 0 by omega), Bool.false_eq_true, ↓reduceIte,
        hlt, ↓reduceDIte]
      rw [show (⟨(FullSysFullPrepareAndTopConcrete.coreAncSym 80 idx).val,
          (FullSysFullPrepareAndTopConcrete.coreAncSym 80 idx).isLt⟩ : Wire posCoreWires) =
          PosSlots24TopWrapper.rPosSubLocal ⟨idx.val - 6, ancIdx86_sub_lt idx hlt⟩ from
          Fin.ext (show 3948 + idx.val = 3954 + (idx.val - 6) by omega)]
      exact coreBetaOf_payload s0 p80 z _
theorem pos80_coreIdxOf_uniq (s0 : Bool)
    (j : Fin (2 ^ FullSysFullPrepareAndTopConcrete.coreWiresSym 80))
    (p80 : BitAssignment 80) (z : Fin (2 ^ SpecsAux.SpecMirror.systemQubits))
    (hsys : (FullSysFullPrepareAndTopConcrete.coreSysSym 80).extractIndex j = z)
    (hanc : (FullSysFullPrepareAndTopConcrete.coreAncSym 80).extractIndex j = ancIdx86 s0 p80) :
    j = coreIdxOf hkSym80 s0 p80 z :=
  finPow2_ext_of_basisBits fun q ↦ by
    have hq4 : q.val < 4034 := q.isLt
    by_cases hq : q.val < SpecsAux.SpecMirror.systemQubits
    · simpa only [QRegister.basisBits_extractIndex,
        show FullSysFullPrepareAndTopConcrete.coreSysSym 80 ⟨q.val, hq⟩ = q from
          Fin.ext (Nat.zero_add q.val)] using
        congrFun (congrArg (basisBits _)
          (hsys.trans (pos80_coreIdxOf_extract_sys s0 p80 z).symm)) ⟨q.val, hq⟩
    · have hge : 3948 ≤ q.val := Nat.not_lt.mp hq
      have hsub : q.val - 3948 < FullSysFullPrepareAndTopConcrete.selWiresSym 80 :=
        Nat.sub_lt_left_of_lt_add hge q.isLt
      simpa only [QRegister.basisBits_extractIndex,
        show FullSysFullPrepareAndTopConcrete.coreAncSym 80 ⟨q.val - 3948, hsub⟩ = q from
          Fin.ext (Nat.add_sub_of_le hge)] using
        congrFun (congrArg (basisBits _)
          (hanc.trans (pos80_coreIdxOf_extract_anc s0 p80 z).symm)) ⟨q.val - 3948, hsub⟩
theorem pos80_coreAnc_agreeOutside_iff
    (j r : Fin (2 ^ FullSysFullPrepareAndTopConcrete.coreWiresSym 80)) :
    (FullSysFullPrepareAndTopConcrete.coreAncSym 80).AgreeOutside j r ↔
      (FullSysFullPrepareAndTopConcrete.coreSysSym 80).extractIndex j =
        (FullSysFullPrepareAndTopConcrete.coreSysSym 80).extractIndex r := by
  refine ⟨fun h ↦ finPow2_ext_of_basisBits fun w ↦ ?_, fun h q hnot ↦ ?_⟩
  · rw [QRegister.basisBits_extractIndex, QRegister.basisBits_extractIndex]
    exact h _ fun ⟨u, hu⟩ ↦ by
      have hv : 3948 + u.val = 0 + w.val := congrArg Fin.val hu
      have hw : w.val < 3948 := w.isLt
      omega
  · have hlt : q.val < SpecsAux.SpecMirror.systemQubits := by
      by_contra hge
      exact hnot ⟨⟨q.val - 3948, Nat.sub_lt_left_of_lt_add (Nat.not_lt.mp hge) q.isLt⟩,
        Fin.ext (Nat.add_sub_of_le (Nat.not_lt.mp hge))⟩
    simpa only [QRegister.basisBits_extractIndex,
      show FullSysFullPrepareAndTopConcrete.coreSysSym 80 ⟨q.val, hlt⟩ = q from
        Fin.ext (Nat.zero_add q.val)] using congrFun (congrArg (basisBits _) h) ⟨q.val, hlt⟩
theorem pos80_coreSys_agreeOutside
    (a_c : Fin (2 ^ FullSysFullPrepareAndTopConcrete.selWiresSym 80))
    (row col : Fin (2 ^ FullSysFullPrepareAndTopConcrete.coreWiresSym 80))
    (hr : (FullSysFullPrepareAndTopConcrete.coreAncSym 80).extractIndex row = a_c)
    (hc : (FullSysFullPrepareAndTopConcrete.coreAncSym 80).extractIndex col = a_c) :
    (FullSysFullPrepareAndTopConcrete.coreSysSym 80).AgreeOutside row col :=
  fun q hnot ↦ by
    have hge : 3948 ≤ q.val :=
      Nat.le_of_not_lt fun hlt ↦ hnot ⟨⟨q.val, hlt⟩, Fin.ext (Nat.zero_add q.val)⟩
    have hsub : q.val - 3948 < FullSysFullPrepareAndTopConcrete.selWiresSym 80 :=
      Nat.sub_lt_left_of_lt_add hge q.isLt
    simpa only [QRegister.basisBits_extractIndex,
      show FullSysFullPrepareAndTopConcrete.coreAncSym 80 ⟨q.val - 3948, hsub⟩ = q from
        Fin.ext (Nat.add_sub_of_le hge)] using
      congrFun (congrArg (basisBits _) (hr.trans hc.symm)) ⟨q.val - 3948, hsub⟩
end ConfigPosSlots24SemanticOracleConcrete80
end PosSlots24SemanticOracleConcrete80
end
end ModPosSlots24SemanticOracleConcrete80

section ModFastCoinBarrel288
@[expose] public section
section ConfigFastCoinBarrel288
set_option exponentiation.threshold 256
namespace FastCoinBarrel288
open CoinDispatchedBarrel288
open FullSysCatSegmentBridge
open FullSysHoistedSelectStitch
noncomputable def fastHoistedBarrelSpec145 {mPayload : ℕ} (hmPay : 80 ≤ mPayload) :
    HoistedBarrelSpec mPayload 288 where
  uBarrel _ := uBarrelFast hmPay
  hHighWireComm _ i hi g := uBarrelFast_comm_high_wire hmPay i hi g
@[simp] theorem fastHoistedBarrelSpec145_uBarrel {mPayload : ℕ} (hmPay : 80 ≤ mPayload)
    (cfg : SpecsAux.SpecMirror.Configuration) : (fastHoistedBarrelSpec145 hmPay).uBarrel cfg =
    uBarrelFast hmPay := rfl
end FastCoinBarrel288
end ConfigFastCoinBarrel288
end
end ModFastCoinBarrel288

section ModWeighted3ASegmentAndTopClosure
@[expose] public section
namespace SegmentAndTopClosure
open Operator Matrix Circuit _root_.DynamicCircuit DynCircuitExt SpecsAux.SpecMirror
open SpecsAux.BridgeFermionicComm
open SpecsAux.BridgeFermionicComm.SpecInner
open SpecsAux.FullScaleBESector
open SpecsAux.PhaseGradCatalystCore
open SpecsAux.BridgeDuhamel
open BiGqspSegmentSpine
open TFreeLaurentGQSP
open CatalyzedLaurentGQSP BidirectionalCatalyzedGQSP
open scoped Matrix Matrix.Norms.L2Operator BigOperators
instance (priority := 100000) instNeZeroTwoPowClosure (k : ℕ) : NeZero (2 ^ k) :=
  ⟨Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos k)⟩
abbrev rCleanAct0 (k_act k_w N : ℕ) (hN : k_act + k_w = N) : QRegister k_act N :=
  QRegister.block 0 k_act (by omega)
abbrev rCleanSubW (k_act k_w N : ℕ) (hN : k_act + k_w = N) : QRegister k_w N :=
  QRegister.block k_act k_w (by omega)
theorem rCleanAct0_disjoint_rCleanSubW (k_act k_w N : ℕ) (hN : k_act + k_w = N) :
    (rCleanAct0 k_act k_w N hN).DisjointWires (rCleanSubW k_act k_w N hN) :=
  QRegister.block_disjoint_of_le 0 k_act k_act k_w (by omega) (by omega) (by omega)
noncomputable def cleanZeroEmbedIdx {k_act k_w N : ℕ} (hN : k_act + k_w = N)
    (x : Fin (2 ^ k_act)) : Fin (2 ^ N) := (rCleanAct0 k_act k_w N hN).replaceIndex 0 x
theorem cleanZeroEmbedIdx_extract_act {k_act k_w N : ℕ} (hN : k_act + k_w = N)
    (x : Fin (2 ^ k_act)) :
    (rCleanAct0 k_act k_w N hN).extractIndex (cleanZeroEmbedIdx hN x) = x :=
  (basisBitsEquiv k_act).injective <| funext fun i ↦
    ((rCleanAct0 k_act k_w N hN).basisBits_extractIndex _ i).trans
      (QRegister.basisBits_replaceIndex_apply (rCleanAct0 k_act k_w N hN) 0 x i)
theorem cleanZeroEmbedIdx_extract_subW {k_act k_w N : ℕ} (hN : k_act + k_w = N)
    (x : Fin (2 ^ k_act)) :
    (rCleanSubW k_act k_w N hN).extractIndex (cleanZeroEmbedIdx hN x) = 0 := by
  rw [cleanZeroEmbedIdx, QRegister.extractIndex_replaceIndex_of_disjoint _ _
      (rCleanAct0_disjoint_rCleanSubW k_act k_w N hN).symm 0 x,
    BiGqspSegmentSpine.zero_extract_iff_bits_zero]
  exact fun idx ↦ basisBits_zero_spine N (rCleanSubW k_act k_w N hN idx)
theorem eq_cleanZeroEmbedIdx_of_subW_zero {k_act k_w N : ℕ} (hN : k_act + k_w = N)
    (g : Fin (2 ^ N)) (hg : (rCleanSubW k_act k_w N hN).extractIndex g = 0) :
    cleanZeroEmbedIdx hN ((rCleanAct0 k_act k_w N hN).extractIndex g) = g := by
  apply (basisBitsEquiv N).injective
  funext w
  change basisBits N _ w = basisBits N g w
  by_cases hw : w.val < k_act
  · rw [show w = rCleanAct0 k_act k_w N hN ⟨w.val, hw⟩ from Fin.ext (Nat.zero_add w.val).symm,
      ← (rCleanAct0 k_act k_w N hN).basisBits_extractIndex,
      ← (rCleanAct0 k_act k_w N hN).basisBits_extractIndex, cleanZeroEmbedIdx_extract_act]
  · rw [show w = rCleanSubW k_act k_w N hN ⟨w.val - k_act, by omega⟩ from
        Fin.ext (show w.val = k_act + (w.val - k_act) by omega),
      ← (rCleanSubW k_act k_w N hN).basisBits_extractIndex,
      ← (rCleanSubW k_act k_w N hN).basisBits_extractIndex, cleanZeroEmbedIdx_extract_subW, hg]
noncomputable def compressCleanMatrix {k_act k_w N : ℕ} (hN : k_act + k_w = N)
    (M : Operator (2 ^ N)) : Operator (2 ^ k_act) :=
  fun x y ↦ M (cleanZeroEmbedIdx hN x) (cleanZeroEmbedIdx hN y)
theorem embedMatrix_mul_cleanProj_apply {k_act k_w N : ℕ} (hN : k_act + k_w = N)
    (A : Operator (2 ^ k_act)) (x y : Fin (2 ^ k_act)) : ((rCleanAct0 k_act k_w N
    hN).embedMatrix A * (rCleanSubW k_act k_w N hN).basisOutcomeProjector 0)
    (cleanZeroEmbedIdx hN x) (cleanZeroEmbedIdx hN y) = A x y := by
  rw [(rCleanSubW k_act k_w N hN).basisOutcomeProjector_eq_diagonal, Matrix.mul_diagonal]
  simp only [cleanZeroEmbedIdx_extract_subW, ↓reduceIte, mul_one, QRegister.embedMatrix_apply]
  have hEnv : ((rCleanAct0 k_act k_w N hN).basisSplitEquiv (cleanZeroEmbedIdx hN x)).2 =
      ((rCleanAct0 k_act k_w N hN).basisSplitEquiv (cleanZeroEmbedIdx hN y)).2 := by
    funext e
    change basisBits N (cleanZeroEmbedIdx hN x) e.1 = basisBits N (cleanZeroEmbedIdx hN y) e.1
    have hge : k_act ≤ e.1.val := by
      by_contra hlt
      exact e.2 ⟨⟨e.1.val, Nat.lt_of_not_ge hlt⟩, Fin.ext (Nat.zero_add e.1.val)⟩
    rw [show e.1 = rCleanSubW k_act k_w N hN ⟨e.1.val - k_act, by omega⟩ from
        Fin.ext (show e.1.val = k_act + (e.1.val - k_act) by omega),
      ← (rCleanSubW k_act k_w N hN).basisBits_extractIndex,
      ← (rCleanSubW k_act k_w N hN).basisBits_extractIndex,
      cleanZeroEmbedIdx_extract_subW, cleanZeroEmbedIdx_extract_subW]
  simp only [hEnv, ↓reduceIte, mul_one, cleanZeroEmbedIdx_extract_act]
theorem embedMatrix_compressCleanMatrix_eq_proj_sandwich {k_act k_w N : ℕ}
    (hN : k_act + k_w = N) (M : Operator (2 ^ N)) : (rCleanAct0 k_act k_w N hN).embedMatrix
    (compressCleanMatrix hN M) * (rCleanSubW k_act k_w N hN).basisOutcomeProjector 0 =
    (rCleanSubW k_act k_w N hN).basisOutcomeProjector 0 * M *
    (rCleanSubW k_act k_w N hN).basisOutcomeProjector 0 := by
  ext g₁ g₂
  rw [(rCleanSubW k_act k_w N hN).basisOutcomeProjector_eq_diagonal]
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases h₂ : (rCleanSubW k_act k_w N hN).extractIndex g₂ = 0
  · by_cases h₁ : (rCleanSubW k_act k_w N hN).extractIndex g₁ = 0
    · rw [← eq_cleanZeroEmbedIdx_of_subW_zero hN g₁ h₁,
        ← eq_cleanZeroEmbedIdx_of_subW_zero hN g₂ h₂]
      simp only [cleanZeroEmbedIdx_extract_subW, ↓reduceIte, mul_one, one_mul]
      have hL := embedMatrix_mul_cleanProj_apply hN (compressCleanMatrix hN M)
        ((rCleanAct0 k_act k_w N hN).extractIndex g₁)
        ((rCleanAct0 k_act k_w N hN).extractIndex g₂)
      rw [(rCleanSubW k_act k_w N hN).basisOutcomeProjector_eq_diagonal,
        Matrix.mul_diagonal] at hL
      simpa only [compressCleanMatrix, cleanZeroEmbedIdx_extract_subW, ↓reduceIte,
        mul_one] using hL
    · have hEnvNe : ((rCleanAct0 k_act k_w N hN).basisSplitEquiv g₁).2 ≠
          ((rCleanAct0 k_act k_w N hN).basisSplitEquiv g₂).2 := fun heq ↦ h₁ <|
        (BiGqspSegmentSpine.zero_extract_iff_bits_zero _ _).mpr fun idx ↦
          (congrFun heq ⟨rCleanSubW k_act k_w N hN idx, fun ⟨j, hj⟩ ↦
            (rCleanAct0_disjoint_rCleanSubW k_act k_w N hN).ne j idx hj⟩).trans
            ((BiGqspSegmentSpine.zero_extract_iff_bits_zero _ _).mp h₂ idx)
      simp [QRegister.embedMatrix_apply, hEnvNe, h₁]
  · simp [h₂]
noncomputable def compressCleanUnitary {k_act k_w N : ℕ} (hN : k_act + k_w = N)
    (U : Unitary (2 ^ N)) (hClean : (rCleanSubW k_act k_w N hN).basisOutcomeProjector 0 * U.1
    * (rCleanSubW k_act k_w N hN).basisOutcomeProjector 0 = U.1 * (rCleanSubW k_act k_w N
    hN).basisOutcomeProjector 0) : Unitary (2 ^ k_act) :=
  ⟨compressCleanMatrix hN U.1, by
    let rA := rCleanAct0 k_act k_w N hN
    let rW := rCleanSubW k_act k_w N hN
    let P₀ := rW.basisOutcomeProjector 0
    let V := compressCleanMatrix hN U.1
    have hEP : rA.embedMatrix V * P₀ = U.1 * P₀ := by
      rw [embedMatrix_compressCleanMatrix_eq_proj_sandwich hN, hClean]
    have hVhComm : (rA.embedMatrix V)ᴴ * P₀ = P₀ * (rA.embedMatrix V)ᴴ :=
      rA.embedMatrix_conjTranspose V ▸ (QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint
        rA) _
        (rCleanAct0_disjoint_rCleanSubW k_act k_w N hN) Vᴴ 0
    have hP0sa : P₀ᴴ = P₀ := rW.basisOutcomeProjector_conjTranspose 0
    have hEPd : P₀ * (rA.embedMatrix V)ᴴ = P₀ * U.1ᴴ := by
      simpa only [conjTranspose_mul, hP0sa, hVhComm] using congrArg conjTranspose hEP
    have hUstarU : U.1ᴴ * U.1 = 1 := by
      simpa only [Unitary.coe_star, Matrix.star_eq_conjTranspose] using Unitary.coe_star_mul_self U
    have hProd : rA.embedMatrix (Vᴴ * V) * P₀ = rA.embedMatrix 1 * P₀ := by
      rw [rA.embedMatrix_mul, rA.embedMatrix_conjTranspose, Matrix.mul_assoc, hEP, ← hClean,
        ← Matrix.mul_assoc (rA.embedMatrix V)ᴴ, ← Matrix.mul_assoc (rA.embedMatrix V)ᴴ P₀,
        hVhComm, hEPd, Matrix.mul_assoc P₀ U.1ᴴ U.1, hUstarU, Matrix.mul_one,
        rW.basisOutcomeProjector_mul_self 0, rA.embedMatrix_one, Matrix.one_mul]
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
    ext x y
    rw [← embedMatrix_mul_cleanProj_apply hN (Vᴴ * V) x y, hProd,
      embedMatrix_mul_cleanProj_apply hN 1 x y]⟩
theorem embedUnitary_compressCleanUnitary_mul_proj {k_act k_w N : ℕ} (hN : k_act + k_w = N)
    (U : Unitary (2 ^ N)) (hClean : (rCleanSubW k_act k_w N hN).basisOutcomeProjector 0 * U.1
    * (rCleanSubW k_act k_w N hN).basisOutcomeProjector 0 = U.1 * (rCleanSubW k_act k_w N
    hN).basisOutcomeProjector 0) : ((rCleanAct0 k_act k_w N hN).embedUnitary
    (compressCleanUnitary hN U hClean)).1 * (rCleanSubW k_act k_w N hN).basisOutcomeProjector
    0 = U.1 * (rCleanSubW k_act k_w N hN).basisOutcomeProjector 0 := by
  rw [QRegister.embedUnitary_val, compressCleanUnitary,
    embedMatrix_compressCleanMatrix_eq_proj_sandwich hN, hClean]
theorem embedUnitary_compressCleanUnitary_inv_mul_proj {k_act k_w N : ℕ}
    (hN : k_act + k_w = N) (U : Unitary (2 ^ N)) (hClean : (rCleanSubW k_act k_w N
    hN).basisOutcomeProjector 0 * U.1 * (rCleanSubW k_act k_w N hN).basisOutcomeProjector 0 =
    U.1 * (rCleanSubW k_act k_w N hN).basisOutcomeProjector 0) : ((rCleanAct0 k_act k_w N
    hN).embedUnitary (compressCleanUnitary hN U hClean)⁻¹).1 *
    (rCleanSubW k_act k_w N hN).basisOutcomeProjector 0 = (U⁻¹).1 *
    (rCleanSubW k_act k_w N hN).basisOutcomeProjector 0 := by
  let rA := rCleanAct0 k_act k_w N hN
  let P₀ := (rCleanSubW k_act k_w N hN).basisOutcomeProjector 0
  let V := compressCleanUnitary hN U hClean
  have hEE : (rA.embedUnitary V).1 * (rA.embedUnitary V⁻¹).1 = 1 :=
    congrArg Subtype.val ((rA.embedUnitary_mul V V⁻¹).symm.trans
      (by rw [mul_inv_cancel, QRegister.embedUnitary_one]))
  have hInvU : (U⁻¹).1 * U.1 = 1 := by
    simpa only [Submonoid.coe_mul, OneMemClass.coe_one] using
      congrArg Subtype.val (inv_mul_cancel U)
  have hComm : (rA.embedUnitary V⁻¹).1 * P₀ = P₀ * (rA.embedUnitary V⁻¹).1 :=
    (QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint rA) _
      (rCleanAct0_disjoint_rCleanSubW k_act k_w N hN) (V⁻¹).1 0
  rw [hComm, ← Matrix.one_mul (P₀ * _), ← hInvU, Matrix.mul_assoc (U⁻¹).1 U.1,
    ← Matrix.mul_assoc U.1 P₀, ← embedUnitary_compressCleanUnitary_mul_proj hN U hClean,
    Matrix.mul_assoc (rA.embedUnitary V).1 P₀, ← hComm,
    ← Matrix.mul_assoc (rA.embedUnitary V).1, hEE, Matrix.one_mul]
end SegmentAndTopClosure
end
end ModWeighted3ASegmentAndTopClosure

section ModPos24HeadCoordXor80
@[expose] public section
namespace Pos24HeadCoordXor80
section ConfigPos24HeadCoordXor80
open Operator QProg Matrix
open scoped Matrix BigOperators Circuit.Notation
open HeavyHeadAndProjectile128 (FineCoord128)
abbrev bitsVal {m : ℕ} (γ : BitAssignment m) : ℕ := ∑ i : Fin m, (γ i).val * 2 ^ i.val
def pos24HeadU56 : Fin 56 → ℕ := ![0, 0, 0, 1, 0, 0, 1, 0, 1, 2, 0, 0, 1, 0, 1, 2, 0, 1, 2,
  3, 0, 0, 1, 0, 1, 2, 0, 1, 2, 3, 0, 1, 2, 3, 4, 0, 0, 1, 0, 1, 2, 0, 1, 2, 3, 0, 1, 2, 3, 4,
  0, 1, 2, 3, 4, 5]
def pos24HeadV56 : Fin 56 → ℕ := ![0, 0, 1, 1, 0, 1, 1, 2, 2, 2, 0, 1, 1, 2, 2, 2, 3, 3, 3,
  3, 0, 1, 1, 2, 2, 2, 3, 3, 3, 3, 4, 4, 4, 4, 4, 0, 1, 1, 2, 2, 2, 3, 3, 3, 3, 4, 4, 4, 4, 4,
  5, 5, 5, 5, 5, 5]
def pos24HeadW56 : Fin 56 → ℕ := ![0, 1, 1, 1, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3,
  3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5,
  5, 5, 5, 5, 5, 5]
def pos24PermAxis (pid : Fin 6) (ax : Fin 3) : Fin 3 :=
  match pid.val, ax.val with
  | 0, 0 => 0 | 0, 1 => 1 | 0, _ => 2 | 1, 0 => 0 | 1, 1 => 2 | 1, _ => 1
  | 2, 0 => 1 | 2, 1 => 0 | 2, _ => 2 | 3, 0 => 1 | 3, 1 => 2 | 3, _ => 0
  | 4, 0 => 2 | 4, 1 => 0 | 4, _ => 1 | _, 0 => 2 | _, 1 => 1 | _, _ => 0
lemma pos24_oh_lt128 (neg : Bool) (c : ℕ) :
    (if neg then (128 - c) % 128 else c % 128) < 128 :=
  Bool.recOn neg (Nat.mod_lt _ (Nat.succ_pos 127)) (Nat.mod_lt _ (Nat.succ_pos 127))
def pos24OhPoint (u v w : ℕ) (pid : Fin 6) (sm : Fin 8) : FineCoord128 :=
  let arr : Fin 3 → ℕ := (Matrix.vecCons (u % 128) (Matrix.vecCons (v % 128)
    (Matrix.vecCons (w % 128) Matrix.vecEmpty)))
  fun ax ↦
    let c := arr (pos24PermAxis pid ax)
    let neg := ((sm.val / (2 ^ ax.val)) % 2) == 1
    ⟨if neg then (128 - c) % 128 else c % 128, pos24_oh_lt128 neg c⟩
noncomputable def xorRegBits {b n : ℕ} (rOut : QRegister b n) (δ : BitAssignment b)
    (β : BitAssignment n) : BitAssignment n := fun q ↦ if hq : q ∈ rOut.image then β q + δ
    (Classical.choose ((QRegister.mem_image rOut q).mp hq)) else β q
@[simp] theorem xorRegBits_apply_reg {b n : ℕ} (rOut : QRegister b n) (δ : BitAssignment b)
    (β : BitAssignment n) (j : Fin b) : xorRegBits rOut δ β (rOut j) = β (rOut j) + δ j := by
  have hmem : rOut j ∈ rOut.image := (QRegister.mem_image rOut (rOut j)).mpr ⟨j, rfl⟩
  simp only [xorRegBits, hmem, ↓reduceDIte,
    rOut.wires.injective (Classical.choose_spec ((QRegister.mem_image rOut (rOut j)).mp hmem))]
theorem xorRegBits_apply_of_not_mem {b n : ℕ} (rOut : QRegister b n) (δ : BitAssignment b)
    (β : BitAssignment n) {q : Wire n} (hq : q ∉ rOut.image) :
    xorRegBits rOut δ β q = β q := dite_eq_right hq
@[simp] theorem xorRegBits_comp {b n : ℕ} (rOut : QRegister b n) (δ₁ δ₂ : BitAssignment b)
    (β : BitAssignment n) : xorRegBits rOut δ₂ (xorRegBits rOut δ₁ β) = xorRegBits rOut
    (fun j ↦ δ₁ j + δ₂ j) β := by
  funext q
  by_cases hq : q ∈ rOut.image
  · obtain ⟨j, rfl⟩ := (QRegister.mem_image rOut q).mp hq
    simp [add_assoc]
  · rw [xorRegBits_apply_of_not_mem rOut δ₂ _ hq, xorRegBits_apply_of_not_mem rOut δ₁ β hq,
      xorRegBits_apply_of_not_mem rOut _ β hq]
attribute [irreducible] xorRegBits
def natBits (m x : ℕ) : BitAssignment m := fun j ↦ if (x / 2 ^ j.val) % 2 = 1 then 1 else 0
theorem bitsVal3_lt8 (g : BitAssignment 3) : bitsVal g < 8 :=
  (by decide : ∀ f : Fin 3 → ZMod 2, bitsVal f < 8) g
theorem div7_lt3 {n : ℕ} (h : n < 21) : n / 7 < 3 := by omega
theorem sub21_lt3 {n : ℕ} (h : n < 24) : n - 21 < 3 := by omega
theorem sub3_lt3 {n : ℕ} (h : n < 6) : n - 3 < 3 := by omega
theorem sub6_lt3 {n : ℕ} (h : n < 9) : n - 6 < 3 := by omega
theorem idx63_lt80 (i : Fin 6) : 63 + i.val < 80 := by omega
theorem idx69_lt80 (i : Fin 3) : 69 + i.val < 80 := by omega
theorem idx72_lt80 (i : Fin 3) : 72 + i.val < 80 := by omega
theorem idx21_lt24 {n : ℕ} (h : n < 3) : 21 + n < 24 := by omega
theorem sub32_lt24 {n : ℕ} (h : 32 ≤ n ∧ n < 53) : n - 32 < 24 := by omega
def headOrbitTable56 (k : Fin 56) : BitAssignment 9 := fun j ↦
  if hj3 : j.val < 3 then natBits 3 (pos24HeadU56 k) ⟨j.val, hj3⟩
  else if hj6 : j.val < 6 then natBits 3 (pos24HeadV56 k) ⟨j.val - 3, sub3_lt3 hj6⟩
  else natBits 3 (pos24HeadW56 k) ⟨j.val - 6, sub6_lt3 j.isLt⟩
noncomputable def headOrbitUVWTable (γ : BitAssignment 6) : BitAssignment 9 :=
  if hk : bitsVal γ < 56 then headOrbitTable56 ⟨bitsVal γ, hk⟩ else fun _ ↦ 0
noncomputable def headOutMask24 (en : ZMod 2) (γK : BitAssignment 6) (γPid : BitAssignment 3)
    (γSm : BitAssignment 3) : BitAssignment 24 := fun outIdx ↦
  if en = 0 then 0
  else
    let cVal (ax : Fin 3) : ℕ :=
      if hp : bitsVal γPid < 6 then
        bitsVal fun b : Fin 3 ↦ headOrbitUVWTable γK
          ⟨3 * (pos24PermAxis ⟨bitsVal γPid, hp⟩ ax).val + b.val, by omega⟩
      else 0
    if hout : outIdx.val < 21 then
      let ax : Fin 3 := ⟨outIdx.val / 7, div7_lt3 hout⟩
      natBits 7 (if γSm ax == 1 then (128 - cVal ax) % 128 else cVal ax % 128)
        ⟨outIdx.val % 7, Nat.mod_lt _ (by decide)⟩
    else
      let ax : Fin 3 := ⟨outIdx.val - 21, sub21_lt3 outIdx.isLt⟩
      if (if γSm ax == 1 then (128 - cVal ax) % 128 else cVal ax % 128) % 2 = 1 then 1 else 0
@[simp] theorem headOutMask24_zero (γK : BitAssignment 6) (γPid : BitAssignment 3)
    (γSm : BitAssignment 3) (outIdx : Fin 24) : headOutMask24 0 γK γPid γSm outIdx = 0 := rfl
private theorem headOrbitTable56_axis : ∀ (k : Fin 56) (c : Fin 3),
    bitsVal (fun b : Fin 3 ↦ headOrbitTable56 k ⟨3 * c.val + b.val, by omega⟩) =
      ![pos24HeadU56 k, pos24HeadV56 k, pos24HeadW56 k] c := by decide +kernel
private theorem headOrbitUVWTable_axis {γK : BitAssignment 6} (hk : bitsVal γK < 56)
    (cIdx : Fin 3) :
    bitsVal (fun b : Fin 3 ↦ headOrbitUVWTable γK ⟨3 * cIdx.val + b.val, by omega⟩) =
      ![pos24HeadU56 ⟨bitsVal γK, hk⟩, pos24HeadV56 ⟨bitsVal γK, hk⟩,
        pos24HeadW56 ⟨bitsVal γK, hk⟩] cIdx := by
  simpa only [headOrbitUVWTable, hk, ↓reduceDIte] using
    headOrbitTable56_axis ⟨bitsVal γK, hk⟩ cIdx
theorem headOutMask24_of_valid (γK : BitAssignment 6) (γPid : BitAssignment 3)
    (γSm : BitAssignment 3) (hk : bitsVal γK < 56) (hp : bitsVal γPid < 6) :
    let k : Fin 56 := ⟨bitsVal γK, hk⟩
    let pid : Fin 6 := ⟨bitsVal γPid, hp⟩
    let sm : Fin 8 := ⟨bitsVal γSm, bitsVal3_lt8 γSm⟩
    let dH := pos24OhPoint (pos24HeadU56 k) (pos24HeadV56 k) (pos24HeadW56 k) pid sm
    (∀ (ax : Fin 3) (b : Fin 7),
      headOutMask24 1 γK γPid γSm ⟨7 * ax.val + b.val, by omega⟩ = natBits 7 (dH ax).val b) ∧
    (∀ ax : Fin 3,
      headOutMask24 1 γK γPid γSm ⟨21 + ax.val, by omega⟩ =
        if (dH ax).val % 2 = 1 then 1 else 0) := by
  intro k pid sm dH
  have hmod : ∀ j : Fin 3, ![pos24HeadU56 k, pos24HeadV56 k, pos24HeadW56 k] j =
      ![pos24HeadU56 k % 128, pos24HeadV56 k % 128, pos24HeadW56 k % 128] j :=
    (by decide +kernel : ∀ (j0 : Fin 56) (j : Fin 3),
      ![pos24HeadU56 j0, pos24HeadV56 j0, pos24HeadW56 j0] j =
        ![pos24HeadU56 j0 % 128, pos24HeadV56 j0 % 128, pos24HeadW56 j0 % 128] j) k
  have hsm_bit (ax : Fin 3) : (γSm ax == 1) = (((sm.val / 2 ^ ax.val) % 2) == 1) :=
    (by decide : ∀ (g : Fin 3 → ZMod 2) (a : Fin 3),
      (g a == 1) = (((bitsVal g / 2 ^ a.val) % 2) == 1)) γSm ax
  refine ⟨fun ax b ↦ ?_, fun ax ↦ ?_⟩
  · simp only [headOutMask24, one_ne_zero, ↓reduceIte, show 7 * ax.val + b.val < 21 by omega,
      ↓reduceDIte, hp]
    rw [show (⟨(7 * ax.val + b.val) / 7, _⟩ : Fin 3) = ax from
        Fin.ext (show (7 * ax.val + b.val) / 7 = ax.val by omega),
      show (⟨(7 * ax.val + b.val) % 7, Nat.mod_lt _ (by decide)⟩ : Fin 7) = b from
        Fin.ext (show (7 * ax.val + b.val) % 7 = b.val by omega),
      headOrbitUVWTable_axis hk (pos24PermAxis pid ax), hmod, hsm_bit ax]
    rfl
  · simp only [headOutMask24, one_ne_zero, ↓reduceIte, show ¬(21 + ax.val < 21) by omega,
      ↓reduceDIte, hp]
    rw [show (⟨21 + ax.val - 21, _⟩ : Fin 3) = ax from Fin.ext (Nat.add_sub_cancel_left 21 _),
      headOrbitUVWTable_axis hk (pos24PermAxis pid ax), hmod, hsm_bit ax]
    rfl
def headActMap80 (i : Fin 37) : Fin 80 :=
  if i.val = 0 then ⟨30, by decide⟩
  else if h7 : i.val < 7 then ⟨63 + (i.val - 1), by omega⟩
  else if h10 : i.val < 10 then ⟨69 + (i.val - 7), by omega⟩
  else if h13 : i.val < 13 then ⟨72 + (i.val - 10), by omega⟩
  else if h34 : i.val < 34 then ⟨32 + (i.val - 13), by omega⟩
  else ⟨i.val - 34, by omega⟩
def rHeadAct37In80 : QRegister 37 80 :=
  { wires := { toFun := headActMap80, inj' := by decide } }
inductive RevGate67 where
  | x (t : Fin 67) | cnot (c t : Fin 67) | toff (c1 c2 t : Fin 67)
  deriving DecidableEq
def RevGate67.wf : RevGate67 → Bool
  | .x _ => true | .cnot c t => c != t
  | .toff c1 c2 t => (c1 != c2) && (c1 != t) && (c2 != t)
def RevGate67.toCircuit : RevGate67 → Circuit 67
  | .x t => Circuit.X t
  | .cnot c t => if h : c ≠ t then Circuit.CNOT c t h else .identity
  | .toff c1 c2 t =>
      if h12 : c1 ≠ c2 then if h1t : c1 ≠ t then if h2t : c2 ≠ t then
        Circuit.TOFF c1 c2 t h12 h1t h2t else .identity else .identity else .identity
def compileRev67 : List RevGate67 → Circuit 67
  | [] => .identity | g :: gs => g.toCircuit ;;ᶜ compileRev67 gs
private theorem lemHex3d4 {c t : Fin 67} (h : (RevGate67.cnot c t).wf = true) : c ≠ t := by
  simpa [RevGate67.wf, bne_iff_ne] using h
private theorem lemHex3d5 {c1 c2 t : Fin 67} (h : (RevGate67.toff c1 c2 t).wf = true) :
    c1 ≠ c2 ∧ c1 ≠ t ∧ c2 ≠ t := by
  simpa [RevGate67.wf, Bool.and_eq_true, bne_iff_ne, and_assoc] using h
private theorem lemHex3da : ∀ (gs : List RevGate67), (compileRev67 gs).count PrimitiveGate.T = 0
  | [] => rfl
  | g :: gs => by
      rw [compileRev67, Circuit.count_seq, lemHex3da gs, add_zero]
      cases g
      · rfl
      all_goals
        dsimp only [RevGate67.toCircuit]
        split_ifs
        all_goals rfl
def unpackMask67 (m : ℕ) : BitAssignment 67 := fun q ↦ if m.testBit q.val then 1 else 0
def stepMask67 (g : RevGate67) (m : ℕ) : ℕ :=
  match g with
  | .x t => m ^^^ (2 ^ t.val)
  | .cnot c t => if m.testBit c.val then m ^^^ (2 ^ t.val) else m
  | .toff c1 c2 t =>
      if m.testBit c1.val && m.testBit c2.val then m ^^^ (2 ^ t.val) else m
def runMask67 : List RevGate67 → ℕ → ℕ
  | [], m => m
  | g :: gs, m => runMask67 gs (stepMask67 g m)
private def rg67Tgt : RevGate67 → Fin 67
  | .x t | .cnot _ t | .toff _ _ t => t
private def rg67Fires (m : ℕ) : RevGate67 → Bool
  | .x _ => true
  | .cnot c _ => m.testBit c.val
  | .toff c1 c2 _ => m.testBit c1.val && m.testBit c2.val
private theorem stepMask67_eq (g : RevGate67) (m : ℕ) :
    stepMask67 g m = if rg67Fires m g then m ^^^ (2 ^ (rg67Tgt g).val) else m := by
  cases g
  all_goals rfl
private theorem lemHex3dd (m : ℕ) (t : Fin 67) : unpackMask67 (m ^^^ (2 ^ t.val)) =
    Function.update (unpackMask67 m) t (unpackMask67 m t + 1) := by
  funext q
  by_cases hqt : q = t
  · subst hqt
    simp only [Function.update_self, unpackMask67, Nat.testBit_xor, Nat.testBit_two_pow_self]
    exact (by decide : ∀ b : Bool, (if xor b true then (1 : ZMod 2) else 0) =
      (if b then 1 else 0) + 1) (m.testBit q.val)
  · simp only [Function.update_of_ne hqt, unpackMask67, Nat.testBit_xor, Nat.testBit_two_pow,
      decide_eq_false (fun h : t.val = q.val ↦ hqt (Fin.ext h.symm)), Bool.xor_false]
private theorem lemHex3df {g : RevGate67} (hw : g.wf = true) (m : ℕ) : g.toCircuit.eval.1.mulVec
    (basisKet (unpackMask67 m)) = basisKet (unpackMask67 (stepMask67 g m)) := by
  have hite (t : Fin 67) (b : Bool) : Function.update (unpackMask67 m) t
      (unpackMask67 m t + if b then 1 else 0) =
      unpackMask67 (if b then m ^^^ (2 ^ t.val) else m) := by
    cases b
    · rw [ite_eq_right Bool.false_ne_true, ite_eq_right Bool.false_ne_true, add_zero,
      Function.update_eq_self]
    · simp [lemHex3dd m t]
  cases g with
  | x t =>
      dsimp only [RevGate67.toCircuit, stepMask67]
      rw [evolve_X_basisKet, lemHex3dd]
  | cnot c t =>
      rw [RevGate67.toCircuit, dite_eq_left (lemHex3d4 hw), evolve_CNOT_basisKet, stepMask67_eq]
      exact congrArg basisKet (hite t (m.testBit c.val))
  | toff c1 c2 t =>
      obtain ⟨h12, h1t, h2t⟩ := lemHex3d5 hw
      rw [RevGate67.toCircuit, dite_eq_left h12, dite_eq_left h1t, dite_eq_left h2t,
        evolve_TOFF_basisKet,
        stepMask67_eq]
      refine congrArg basisKet ((congrArg (Function.update (unpackMask67 m) t) ?_).trans
        (hite t (m.testBit c1.val && m.testBit c2.val)))
      exact congrArg (unpackMask67 m t + ·)
        ((by decide : ∀ a b : Bool, (if a then (1 : ZMod 2) else 0) * (if b then 1 else 0) =
          if (a && b) then 1 else 0) (m.testBit c1.val) (m.testBit c2.val))
private theorem lemHex3e0 : ∀ {gs : List RevGate67}, gs.all RevGate67.wf = true → ∀ (m : ℕ),
    (compileRev67 gs).eval.1.mulVec (basisKet (unpackMask67 m)) =
      basisKet (unpackMask67 (runMask67 gs m))
  | [], _, _ => by
      rw [compileRev67, Circuit.eval_identity, OneMemClass.coe_one, Matrix.one_mulVec,
        runMask67]
  | g :: gs, hw, m => by
      simp only [List.all_cons, Bool.and_eq_true] at hw
      rw [compileRev67, Circuit.eval_seq, Submonoid.coe_mul, ← Matrix.mulVec_mulVec,
        lemHex3df hw.1 m, lemHex3e0 hw.2, runMask67]
def packPrefix67 (β : BitAssignment 67) : ℕ → ℕ
  | 0 => 0
  | k + 1 => packPrefix67 β k ||| (if h : k < 67 then if β ⟨k, h⟩ = 1 then 2 ^ k else 0 else 0)
def pack67 (β : BitAssignment 67) : ℕ := packPrefix67 β 67
private theorem lemHex3e1 (β : BitAssignment 67) : ∀ (k i : ℕ),
    (packPrefix67 β k).testBit i =
      if i < k then if h67 : i < 67 then decide (β ⟨i, h67⟩ = 1) else false else false
  | 0, _ => by simp [packPrefix67]
  | k + 1, i => by
      rw [packPrefix67, Nat.testBit_or, lemHex3e1 β k i]
      by_cases hik : i = k
      · subst hik
        simp only [Nat.lt_irrefl, Nat.lt_succ_self, ↓reduceIte, Bool.false_or]
        split_ifs with h67 hb
        all_goals simp_all [Nat.testBit_two_pow_self]
      · simp only [show (i < k + 1) ↔ (i < k) by omega]
        split_ifs
        all_goals simp [Ne.symm hik]
private theorem lemHex3e2 (β : BitAssignment 67) : unpackMask67 (pack67 β) = β := by
  funext q
  simp only [unpackMask67, pack67, lemHex3e1 β 67 q.val, q.isLt, ↓reduceIte, ↓reduceDIte]
  exact (by decide : ∀ z : ZMod 2, (if decide (z = 1) = true then (1 : ZMod 2) else 0) = z)
    (β q)
private theorem lemHex3e3 (β : BitAssignment 67)
    (hClean : ∀ j : Fin 30, β ⟨37 + j.val, by omega⟩ = 0)
    {i : ℕ} (hi : 37 ≤ i) : (pack67 β).testBit i = false := by
  simp only [pack67, lemHex3e1 β 67 i]
  by_cases hi67 : i < 67
  · rw [ite_eq_left hi67, dite_eq_left hi67, show (⟨i, hi67⟩ : Fin 67) = ⟨37 + (i - 37),
    by omega⟩ from
        Fin.ext (show i = 37 + (i - 37) by omega), hClean ⟨i - 37, by omega⟩]
    decide
  · simp [hi67]
private theorem lemHex3e4 (a b : ℕ) : (a ^^^ b) ^^^ b = a := Nat.eq_of_testBit_eq fun i ↦ by
  simpa only [Nat.testBit_xor] using (by decide : ∀ x y : Bool, xor (xor x y) y = x)
    (a.testBit i) (b.testBit i)
private theorem lemHex3e5 (a b c : ℕ) : (a ^^^ b) ^^^ c = (a ^^^ c) ^^^ b :=
  Nat.eq_of_testBit_eq fun i ↦ by
    simpa only [Nat.testBit_xor] using
      (by decide : ∀ x y z : Bool, xor (xor x y) z = xor (xor x z) y)
      (a.testBit i) (b.testBit i) (c.testBit i)
private theorem lemHex3e6 (a b c : ℕ) : (a ^^^ b) ^^^ c = a ^^^ (b ^^^ c) := Nat.xor_assoc a b c
private theorem lemHex3e7 (a b M : ℕ) : (a ^^^ b) &&& M = (a &&& M) ^^^ (b &&& M) :=
  Nat.eq_of_testBit_eq fun i ↦ by
    simpa only [Nat.testBit_and, Nat.testBit_xor] using (by decide :
      ∀ x y z : Bool, (xor x y && z) = xor (x && z) (y && z))
      (a.testBit i) (b.testBit i) (M.testBit i)
private theorem lemHex3e8 {a δ M : ℕ} (hdisj : δ &&& M = 0) : (a ^^^ δ) &&& M = a &&& M := by
  rw [lemHex3e7, hdisj, Nat.xor_zero]
private theorem lemHex3e9 : ∀ (gs₁ gs₂ : List RevGate67) (m : ℕ),
    runMask67 (gs₁ ++ gs₂) m = runMask67 gs₂ (runMask67 gs₁ m)
  | [], _, _ => rfl
  | g :: gs₁, gs₂, m => lemHex3e9 gs₁ gs₂ (stepMask67 g m)
private theorem lemHex3ea (m : ℕ) {c t : Fin 67} (hne : c ≠ t) :
    (m ^^^ (2 ^ t.val)).testBit c.val = m.testBit c.val := by
  rw [Nat.testBit_xor, Nat.testBit_two_pow,
    decide_eq_false (fun e : t.val = c.val ↦ hne (Fin.ext e.symm)), Bool.xor_false]
private theorem lemHex3eb {g : RevGate67} (hw : g.wf = true) (m : ℕ) :
    stepMask67 g (stepMask67 g m) = m := by
  have hfires : rg67Fires (m ^^^ (2 ^ (rg67Tgt g).val)) g = rg67Fires m g := by
    cases g with
    | x _ => rfl
    | cnot c t => exact lemHex3ea m (lemHex3d4 hw)
    | toff c1 c2 t =>
        dsimp only [rg67Fires, rg67Tgt]
        rw [lemHex3ea m (lemHex3d5 hw).2.1, lemHex3ea m (lemHex3d5 hw).2.2]
  rw [stepMask67_eq g m]
  cases hf : rg67Fires m g
  · simp [stepMask67_eq, hf]
  · simp [stepMask67_eq, hfires, hf, lemHex3e4]
private theorem lemHex3ec : ∀ {gs : List RevGate67}, gs.all RevGate67.wf = true → ∀ (m : ℕ),
    runMask67 gs.reverse (runMask67 gs m) = m
  | [], _, _ => rfl
  | g :: gs, hw, m => by
      simp only [List.all_cons, Bool.and_eq_true] at hw
      rw [List.reverse_cons, runMask67, lemHex3e9, lemHex3ec hw.2]
      exact lemHex3eb hw.1 m
def isOut24Idx (i : ℕ) : Bool := decide (13 ≤ i ∧ i < 37)
def RevGate67.noOut24Ctrl : RevGate67 → Bool
  | .x _ => true
  | .cnot c _ => !isOut24Idx c.val
  | .toff c1 c2 _ => !isOut24Idx c1.val && !isOut24Idx c2.val
private theorem lemHex3ed {g : RevGate67} (hno : g.noOut24Ctrl = true)
    (m δ : ℕ) (hδ : ∀ i, isOut24Idx i = false → δ.testBit i = false) :
    stepMask67 g (m ^^^ δ) = (stepMask67 g m) ^^^ δ := by
  have htb : ∀ i, isOut24Idx i = false → (m ^^^ δ).testBit i = m.testBit i := fun i hi ↦ by
    rw [Nat.testBit_xor, hδ i hi, Bool.xor_false]
  have hfires : rg67Fires (m ^^^ δ) g = rg67Fires m g := by
    cases g with
    | x _ => rfl
    | cnot c _ => exact htb c.val (by simpa [RevGate67.noOut24Ctrl] using hno)
    | toff c1 c2 _ =>
        simp only [RevGate67.noOut24Ctrl, Bool.and_eq_true, Bool.not_eq_true'] at hno
        dsimp only [rg67Fires]
        rw [htb c1.val hno.1, htb c2.val hno.2]
  rw [stepMask67_eq, stepMask67_eq, hfires]
  cases rg67Fires m g
  · rfl
  · exact lemHex3e5 m δ _
private theorem lemHex3ee :
    ∀ {gs : List RevGate67}, gs.all RevGate67.noOut24Ctrl = true →
      ∀ (m δ : ℕ), (∀ i, isOut24Idx i = false → δ.testBit i = false) →
        runMask67 gs (m ^^^ δ) = (runMask67 gs m) ^^^ δ
  | [], _, _, _, _ => rfl
  | g :: gs, hno, m, δ, hδ => by
      simp only [List.all_cons, Bool.and_eq_true] at hno
      rw [runMask67, lemHex3ed hno.1 m δ hδ, lemHex3ee hno.2 _ δ hδ, runMask67]
def RevGate67.inMask (M : ℕ) : RevGate67 → Bool
  | .x t => M.testBit t.val
  | .cnot c t => M.testBit c.val && M.testBit t.val
  | .toff c1 c2 t => M.testBit c1.val && M.testBit c2.val && M.testBit t.val
private theorem lemHex3ef {g : RevGate67} {M : ℕ} (hm : g.inMask M = true) (m : ℕ) :
    (stepMask67 g m &&& M = stepMask67 g (m &&& M)) ∧
    (∀ i, M.testBit i = false → (stepMask67 g m).testBit i = m.testBit i) := by
  have htb (i : ℕ) (hi : M.testBit i = true) : (m &&& M).testBit i = m.testBit i := by
    simp [Nat.testBit_and, hi]
  have htgt : M.testBit (rg67Tgt g).val = true ∧ rg67Fires (m &&& M) g = rg67Fires m g := by
    cases g with
    | x _ => exact ⟨hm, rfl⟩
    | cnot c _ =>
        simp only [RevGate67.inMask, Bool.and_eq_true] at hm
        exact ⟨hm.2, htb c.val hm.1⟩
    | toff c1 c2 _ =>
        simp only [RevGate67.inMask, Bool.and_eq_true] at hm
        exact ⟨hm.2, by simp [rg67Fires, htb c1.val hm.1.1, htb c2.val hm.1.2]⟩
  rw [stepMask67_eq g m, stepMask67_eq g (m &&& M), htgt.2]
  cases rg67Fires m g
  · exact ⟨rfl, fun _ _ ↦ rfl⟩
  · refine ⟨Nat.eq_of_testBit_eq fun i ↦ ?_, fun i hi ↦ ?_⟩
    · by_cases hti : (rg67Tgt g).val = i
      · simp [← hti, Nat.testBit_and, Nat.testBit_xor, htgt.1]
      · simp [Nat.testBit_and, Nat.testBit_xor, hti]
    · simp [Nat.testBit_xor,
        show (rg67Tgt g).val ≠ i from fun e ↦ by simp [e ▸ htgt.1] at hi]
private theorem lemHex3f0 : ∀ {gs : List RevGate67} {M : ℕ}, gs.all (RevGate67.inMask M) = true →
    ∀ m : ℕ, (runMask67 gs m &&& M = runMask67 gs (m &&& M)) ∧
      (∀ i, M.testBit i = false → (runMask67 gs m).testBit i = m.testBit i)
  | [], _, _, _ => ⟨rfl, fun _ _ ↦ rfl⟩
  | g :: gs, _, hm, m => by
      simp only [List.all_cons, Bool.and_eq_true] at hm
      obtain ⟨h1, h2⟩ := lemHex3ef hm.1 m
      obtain ⟨ih1, ih2⟩ := lemHex3f0 hm.2 (stepMask67 g m)
      exact ⟨by rw [runMask67, ih1, h1, runMask67],
        fun i hi ↦ by rw [runMask67, ih2 i hi, h2 i hi]⟩
private theorem lemHex3f1 {gs : List RevGate67} {M : ℕ} (hm : gs.all (RevGate67.inMask M) = true)
    (m : ℕ) : runMask67 gs m = (m ^^^ (m &&& M)) ^^^ runMask67 gs (m &&& M) := by
  obtain ⟨hAnd, hOut⟩ := lemHex3f0 hm m
  obtain ⟨_, hOutSub⟩ := lemHex3f0 hm (m &&& M)
  refine Nat.eq_of_testBit_eq fun i ↦ ?_
  cases hMi : M.testBit i
  · simp [Nat.testBit_xor, Nat.testBit_and, hMi, hOut i hMi, hOutSub i hMi]
  · have hEq : (runMask67 gs m).testBit i = (runMask67 gs (m &&& M)).testBit i := by
      simpa [Nat.testBit_and, hMi] using congrArg (·.testBit i) hAnd
    simp [Nat.testBit_xor, Nat.testBit_and, hMi, hEq]
def gatesG67 : List RevGate67 := [.x 53, .toff 8 9 53, .toff 5 6 54, .x 55, .toff 4 54 55,
  .toff 0 53 56, .toff 56 55 46, .toff 46 1 47, .toff 46 2 48, .toff 46 3 49, .toff 46 4 50,
  .toff 46 5 51, .toff 46 6 52, .toff 0 53 56, .toff 4 54 55, .x 55, .toff 5 6 54,
  .toff 8 9 53, .x 53]
def gatesA67 : List RevGate67 := [.cnot 52 49, .x 49, .cnot 51 50, .cnot 52 50, .toff 49 50 53,
  .cnot 52 50, .cnot 51 50, .x 49, .cnot 52 49, .cnot 52 53, .x 53, .toff 51 53 45, .x 53,
  .cnot 52 53, .x 49, .cnot 52 53, .cnot 45 53, .toff 49 53 44, .cnot 45 53, .cnot 52 53,
  .x 49, .cnot 45 47, .toff 48 47 54, .cnot 45 47, .cnot 48 44, .cnot 49 44, .cnot 47 54,
  .cnot 52 54, .toff 44 54 43, .cnot 52 54, .cnot 47 54, .cnot 49 44, .cnot 48 44, .cnot 51 49,
  .cnot 52 49, .cnot 48 44, .cnot 50 44, .toff 49 44 55, .cnot 50 44, .cnot 48 44, .cnot 52 49,
  .cnot 51 49, .cnot 44 50, .cnot 55 50, .cnot 45 51, .cnot 44 51, .toff 50 51 56, .cnot 44 51,
  .cnot 45 51, .cnot 55 50, .cnot 44 50, .toff 47 55 57, .cnot 47 57, .toff 56 57 43,
  .cnot 47 57, .cnot 47 43, .cnot 48 43, .cnot 54 43, .cnot 55 43, .cnot 56 43, .cnot 49 44,
  .cnot 52 44, .cnot 45 44, .cnot 52 45, .toff 43 44 58, .toff 43 45 59, .x 47, .cnot 58 43,
  .toff 47 43 60, .cnot 58 43, .x 47, .cnot 43 47, .cnot 58 47, .cnot 60 61, .cnot 60 48,
  .x 48, .cnot 59 58, .cnot 60 58, .toff 48 58 61, .cnot 60 58, .cnot 59 58, .x 48,
  .cnot 60 48, .cnot 58 48, .cnot 59 48, .cnot 60 48, .cnot 61 62, .cnot 61 49, .x 49,
  .cnot 45 44, .cnot 58 44, .cnot 59 44, .cnot 61 44, .toff 49 44 62, .cnot 61 44,
  .cnot 59 44, .cnot 58 44, .cnot 45 44, .x 49, .cnot 61 49, .cnot 44 49, .cnot 45 49,
  .cnot 58 49, .cnot 59 49, .cnot 61 49, .cnot 45 51, .cnot 59 51, .cnot 62 51, .cnot 62 50,
  .x 50, .cnot 62 58, .toff 50 58 51, .cnot 62 58, .x 50, .cnot 62 50, .cnot 58 50,
  .cnot 62 50, .x 50, .cnot 51 48, .toff 50 48 63, .cnot 51 48, .x 50, .cnot 48 63,
  .cnot 49 63, .cnot 48 47, .x 47, .toff 63 47 64, .x 47, .cnot 48 47, .cnot 49 63,
  .cnot 48 63, .cnot 50 49, .x 49, .cnot 47 64, .cnot 51 64, .x 64, .toff 49 64 40, .x 64,
  .cnot 51 64, .cnot 47 64, .x 49, .cnot 50 49, .cnot 49 48, .cnot 49 40, .cnot 51 40,
  .toff 48 40 41, .cnot 51 40, .cnot 49 40, .cnot 49 48, .toff 50 41 42, .x 40, .cnot 48 40,
  .cnot 49 40, .cnot 51 40, .cnot 48 41, .cnot 50 41, .cnot 48 42, .cnot 63 42, .cnot 47 37,
  .cnot 40 37, .cnot 41 37, .x 47, .cnot 41 40, .toff 47 40 38, .cnot 41 40, .x 47,
  .cnot 49 39, .cnot 38 39, .cnot 42 41, .toff 40 41 39, .cnot 42 41, .cnot 38 48, .x 48,
  .cnot 42 41, .cnot 38 41, .toff 48 41 39, .cnot 38 41, .cnot 42 41, .x 48, .cnot 38 48,
  .cnot 48 38, .cnot 41 38, .cnot 42 38]
def gatesB67 : List RevGate67 := [.cnot 43 40, .toff 9 40 43, .cnot 43 40, .cnot 44 41,
  .toff 9 41 44, .cnot 44 41, .cnot 45 42, .toff 9 42 45, .cnot 45 42, .cnot 9 8, .cnot 40 37,
  .toff 8 37 40, .cnot 40 37, .cnot 41 38, .toff 8 38 41, .cnot 41 38, .cnot 42 39,
  .toff 8 39 42, .cnot 42 39, .cnot 9 8, .cnot 43 40, .toff 7 40 43, .cnot 43 40, .cnot 44 41,
  .toff 7 41 44, .cnot 44 41, .cnot 45 42, .toff 7 42 45, .cnot 45 42]
def stageCAxis0_67 : List RevGate67 := [ .toff 10 37 65, .cnot 37 13, .cnot 37 34, .cnot 38
    14, .cnot 65 14, .cnot 65 10, .cnot 39 15, .cnot 65 15, .toff 10 38 15, .cnot 38 39, .cnot
    65 66, .toff 10 39 66, .cnot 66 16, .cnot 66 17, .cnot 66 18, .cnot 66 19, .toff 10 39 66,
    .cnot 65 66, .cnot 38 39, .cnot 65 10, .toff 10 37 65]
def stageCAxis1_67 : List RevGate67 := [ .toff 11 40 65, .cnot 40 20, .cnot 40 35, .cnot 41
    21, .cnot 65 21, .cnot 65 11, .cnot 42 22, .cnot 65 22, .toff 11 41 22, .cnot 41 42, .cnot
    65 66, .toff 11 42 66, .cnot 66 23, .cnot 66 24, .cnot 66 25, .cnot 66 26, .toff 11 42 66,
    .cnot 65 66, .cnot 41 42, .cnot 65 11, .toff 11 40 65]
def stageCAxis2_67 : List RevGate67 := [ .toff 12 43 65, .cnot 43 27, .cnot 43 36, .cnot 44
    28, .cnot 65 28, .cnot 65 12, .cnot 45 29, .cnot 65 29, .toff 12 44 29, .cnot 44 45, .cnot
    65 66, .toff 12 45 66, .cnot 66 30, .cnot 66 31, .cnot 66 32, .cnot 66 33, .toff 12 45 66,
    .cnot 65 66, .cnot 44 45, .cnot 65 12, .toff 12 43 65]
def preGates67 : List RevGate67 := gatesG67 ++ gatesA67 ++ gatesB67
def stageCGates67 : List RevGate67 := stageCAxis0_67 ++ stageCAxis1_67 ++ stageCAxis2_67
def fullGates67 : List RevGate67 := preGates67 ++ stageCGates67 ++ preGates67.reverse
def headCoordXorLocal67 : Circuit 67 := compileRev67 fullGates67
private theorem lemHex3f3 : preGates67.all RevGate67.wf = true := by decide +kernel
private theorem lemHex3f5 : fullGates67.all RevGate67.wf = true := by decide +kernel
private theorem lemHex3f9 : preGates67.reverse.all RevGate67.noOut24Ctrl = true := by
  decide +kernel
private theorem lemHex3fa : fullGates67.all RevGate67.noOut24Ctrl = true := by decide +kernel
@[simp] theorem count_headCoordXorLocal67_t : headCoordXorLocal67.count PrimitiveGate.T = 0 :=
    lemHex3da fullGates67
def rOut24In67 : QRegister 24 67 := QRegister.block 13 24 (by decide)
def rOut24In37 : QRegister 24 37 := QRegister.block 13 24 (by decide)
theorem pack3x7_bit (c0 c1 c2 : ℕ) (h0 : c0 < 128) (h1 : c1 < 128) (_h2 : c2 < 128)
    (ax : Fin 3) (b : Fin 7) : ((c0 + 128 * c1 + 16384 * c2) / 2 ^ (7 * ax.val + b.val)) % 2 =
    ((if ax = 0 then c0 else if ax = 1 then c1 else c2) / 2 ^ b.val) % 2 := by
  fin_cases ax
  all_goals
    fin_cases b
    all_goals
      dsimp
      norm_num
      omega
def preMask67 : ℕ := 0x1ffffffe0000003ff
def maskA67 : ℕ := 0x1ffffbfe000000000
def maskB67 : ℕ := 0x3fe000000380
def maskC0_67 : ℕ := 0x6000000e4000fe400
def maskC1_67 : ℕ := 0x60000070807f00800
def maskC2_67 : ℕ := 0x600003813f8001000
private theorem lemHex3fb : gatesA67.all (RevGate67.inMask maskA67) = true := by decide +kernel
private theorem lemHex3fc : preGates67.all (RevGate67.inMask preMask67) = true := by decide +kernel
private theorem lemHex3fd : gatesB67.all (RevGate67.inMask maskB67) = true := by decide +kernel
private theorem lemHex3fe : stageCAxis0_67.all (RevGate67.inMask maskC0_67) = true := by
  decide +kernel
private theorem lemHex3ff : stageCAxis1_67.all (RevGate67.inMask maskC1_67) = true := by
  decide +kernel
private theorem lemHex400 : stageCAxis2_67.all (RevGate67.inMask maskC2_67) = true := by
  decide +kernel
private theorem lemHex401 {P : ℕ → Prop}
    (h : ∀ (lo : Fin 32) (hi : Fin 32), P (lo.val + 32 * hi.val)) (x : Fin 1024) : P x.val :=
  Nat.mod_add_div x.val 32 ▸ h ⟨x.val % 32, Nat.mod_lt _ (by decide)⟩ ⟨x.val / 32, by omega⟩
private theorem lemHex402 {P : ℕ → Prop}
    (h : ∀ (lo : Fin 64) (hi : Fin 128), P (lo.val + 64 * hi.val)) (z : Fin 8192) : P z.val :=
  Nat.mod_add_div z.val 64 ▸ h ⟨z.val % 64, Nat.mod_lt _ (by decide)⟩ ⟨z.val / 64, by omega⟩
def valid10 (x : ℕ) : Bool :=
  (x.testBit 0) && decide ((x / 2) % 64 < 56) && decide ((x / 128) % 8 < 6)
def gk10 (x : ℕ) : Fin 56 :=
  if h : (x / 2) % 64 < 56 then if valid10 x then ⟨(x / 2) % 64, h⟩ else ⟨0, by decide⟩
  else ⟨0, by decide⟩
def gOutExpected (x : ℕ) : ℕ :=
  x ^^^ ((if valid10 x then 1 else 0) * 2 ^ 46) ^^^ ((gk10 x).val * 2 ^ 47)
def uvwPack9 (gk : Fin 56) : ℕ := pos24HeadU56 gk + 8 * pos24HeadV56 gk + 64 * pos24HeadW56 gk
def cAxis10 (x : ℕ) (ax : Fin 3) : ℕ :=
  if valid10 x then
    if hp : (x / 128) % 8 < 6 then
      let gk := gk10 x
      let pid : Fin 6 := ⟨(x / 128) % 8, hp⟩
      let arr : Fin 3 → ℕ := Matrix.vecCons (pos24HeadU56 gk) (Matrix.vecCons (pos24HeadV56
          gk) (Matrix.vecCons (pos24HeadW56 gk) Matrix.vecEmpty))
      arr (pos24PermAxis pid ax)
    else 0
  else 0
def signedCoord128 (c : ℕ) (neg : Bool) : ℕ := if neg then (128 - c) % 128 else c % 128
def axisDeltaNat (ax : ℕ) (d : ℕ) : ℕ :=
  ((d % 128) * 2 ^ (13 + 7 * ax)) ^^^ ((d % 2) * 2 ^ (34 + ax))
private theorem lemHex403 (x : Fin 1024) : runMask67 gatesG67 x.val = gOutExpected x.val :=
  lemHex401 (P := fun n ↦ runMask67 gatesG67 n = gOutExpected n) (by decide +kernel) x
private theorem lemHex404 (x : Fin 1024) :
    gOutExpected x.val &&& maskA67 = (gk10 x.val).val * 2 ^ 47 :=
  lemHex401 (P := fun n ↦ gOutExpected n &&& maskA67 = (gk10 n).val * 2 ^ 47) (by decide +kernel) x
private theorem lemHex405 (x : Fin 1024) :
    (gOutExpected x.val ^^^ (gOutExpected x.val &&& maskA67)) &&& maskB67 =
      ((x.val / 128) % 8) * 2 ^ 7 :=
  lemHex401 (P := fun n ↦ (gOutExpected n ^^^ (gOutExpected n &&& maskA67)) &&& maskB67 =
    ((n / 128) % 8) * 2 ^ 7) (by decide +kernel) x
private theorem lemHex406 : ∀ gk : Fin 56,
    runMask67 gatesA67 (gk.val * 2 ^ 47) &&& maskB67 = uvwPack9 gk * 2 ^ 37 := by
  decide +kernel
private theorem lemHex407 (x : Fin 1024) :
    let bIn := (((x.val / 128) % 8) * 2 ^ 7) ^^^ (uvwPack9 (gk10 x.val) * 2 ^ 37)
    (runMask67 gatesB67 bIn &&& maskC0_67 = cAxis10 x.val 0 * 2 ^ 37) ∧
    (runMask67 gatesB67 bIn &&& maskC1_67 = cAxis10 x.val 1 * 2 ^ 40) ∧
    (runMask67 gatesB67 bIn &&& maskC2_67 = cAxis10 x.val 2 * 2 ^ 43) :=
  lemHex401 (P := fun n ↦
    let bIn := (((n / 128) % 8) * 2 ^ 7) ^^^ (uvwPack9 (gk10 n) * 2 ^ 37)
    (runMask67 gatesB67 bIn &&& maskC0_67 = cAxis10 n 0 * 2 ^ 37) ∧
    (runMask67 gatesB67 bIn &&& maskC1_67 = cAxis10 n 1 * 2 ^ 40) ∧
    (runMask67 gatesB67 bIn &&& maskC2_67 = cAxis10 n 2 * 2 ^ 43)) (by decide +kernel) x
private theorem lemHex409 (x : Fin 1024) (gk : Fin 56) :
    (((gOutExpected x.val ^^^ (gOutExpected x.val &&& maskA67)) ^^^
      runMask67 gatesA67 (gk.val * 2 ^ 47)) ^^^
    ((((gOutExpected x.val ^^^ (gOutExpected x.val &&& maskA67)) ^^^
      runMask67 gatesA67 (gk.val * 2 ^ 47)) &&& maskB67))) &&&
    (maskC0_67 ||| maskC1_67 ||| maskC2_67) = 0 := by
  have h1 := lemHex401 (P := fun n ↦ ((gOutExpected n ^^^ (gOutExpected n &&& maskA67)) ^^^
      ((gOutExpected n ^^^ (gOutExpected n &&& maskA67)) &&& maskB67)) &&&
      (maskC0_67 ||| maskC1_67 ||| maskC2_67) = 0) (by decide +kernel) x
  have h2 := (by decide +kernel : ∀ g : Fin 56,
    (runMask67 gatesA67 (g.val * 2 ^ 47) ^^^
      (runMask67 gatesA67 (g.val * 2 ^ 47) &&& maskB67)) &&&
      (maskC0_67 ||| maskC1_67 ||| maskC2_67) = 0) gk
  let a := gOutExpected x.val ^^^ (gOutExpected x.val &&& maskA67)
  let b := runMask67 gatesA67 (gk.val * 2 ^ 47)
  have hrew : ((a ^^^ b) ^^^ ((a ^^^ b) &&& maskB67)) =
      (a ^^^ (a &&& maskB67)) ^^^ (b ^^^ (b &&& maskB67)) :=
    Nat.eq_of_testBit_eq fun i ↦ by
      simpa only [Nat.testBit_xor, Nat.testBit_and] using
        (by decide : ∀ u v m : Bool,
          xor (xor u v) (xor u v && m) = xor (xor u (u && m)) (xor v (v && m)))
          (a.testBit i) (b.testBit i) (maskB67.testBit i)
  rw [hrew, lemHex3e7, h1, h2]
  rfl
private theorem lemHex40b (x : Fin 1024) : ∀ (ax : Fin 3), cAxis10 x.val ax < 6 :=
  lemHex401 (P := fun n ↦ ∀ ax : Fin 3, cAxis10 n ax < 6) (by decide +kernel) x
private theorem lemHex40c (x : Fin 1024) :
    let yPre := runMask67 preGates67 x.val
    (yPre &&& maskC0_67 = cAxis10 x.val 0 * 2 ^ 37) ∧
    (yPre &&& maskC1_67 = cAxis10 x.val 1 * 2 ^ 40) ∧
    (yPre &&& maskC2_67 = cAxis10 x.val 2 * 2 ^ 43) := by
  dsimp only [preGates67]
  rw [List.append_assoc, lemHex3e9, lemHex403 x, lemHex3e9,
    lemHex3f1 lemHex3fb (gOutExpected x.val), lemHex404 x]
  let gk := gk10 x.val
  let yA := (gOutExpected x.val ^^^ (gk.val * 2 ^ 47)) ^^^ runMask67 gatesA67 (gk.val * 2 ^ 47)
  have hyA_orig : yA = (gOutExpected x.val ^^^ (gOutExpected x.val &&& maskA67)) ^^^
      runMask67 gatesA67 (gk.val * 2 ^ 47) := by simp only [yA, gk, lemHex404 x]
  have hyA_B : yA &&& maskB67 = (((x.val / 128) % 8) * 2 ^ 7) ^^^ (uvwPack9 gk * 2 ^ 37) := by
    rw [hyA_orig, lemHex3e7, lemHex405 x, lemHex406 gk]
  rw [lemHex3f1 lemHex3fd yA]
  have hrem : ∀ M : ℕ, (maskC0_67 ||| maskC1_67 ||| maskC2_67) &&& M = M →
      (yA ^^^ (yA &&& maskB67)) &&& M = 0 := fun M hM ↦ by
    rw [← hM, ← Nat.and_assoc, hyA_orig, lemHex409 x gk, Nat.zero_and]
  obtain ⟨hB0, hB1, hB2⟩ := lemHex407 x
  exact ⟨by rw [lemHex3e7, hrem _ (by decide +kernel), Nat.zero_xor, hyA_B, hB0],
    by rw [lemHex3e7, hrem _ (by decide +kernel), Nat.zero_xor, hyA_B, hB1],
    by rw [lemHex3e7, hrem _ (by decide +kernel), Nat.zero_xor, hyA_B, hB2]⟩
private theorem lemHex40d : ∀ (c : Fin 6) (neg : Fin 2),
    runMask67 stageCAxis0_67 ((neg.val * 2 ^ 10) ^^^ (c.val * 2 ^ 37)) =
      ((neg.val * 2 ^ 10) ^^^ (c.val * 2 ^ 37)) ^^^
        axisDeltaNat 0 (signedCoord128 c.val (neg.val == 1)) := by decide +kernel
private theorem lemHex40e : ∀ (c : Fin 6) (neg : Fin 2),
    runMask67 stageCAxis1_67 ((neg.val * 2 ^ 11) ^^^ (c.val * 2 ^ 40)) =
      ((neg.val * 2 ^ 11) ^^^ (c.val * 2 ^ 40)) ^^^
        axisDeltaNat 1 (signedCoord128 c.val (neg.val == 1)) := by decide +kernel
private theorem lemHex40f : ∀ (c : Fin 6) (neg : Fin 2),
    runMask67 stageCAxis2_67 ((neg.val * 2 ^ 12) ^^^ (c.val * 2 ^ 43)) =
      ((neg.val * 2 ^ 12) ^^^ (c.val * 2 ^ 43)) ^^^
        axisDeltaNat 2 (signedCoord128 c.val (neg.val == 1)) := by decide +kernel
private theorem lemHex410 : (∀ d : Fin 128, axisDeltaNat 0 d.val &&& maskC1_67 = 0) ∧
    (∀ d : Fin 128, axisDeltaNat 0 d.val &&& maskC2_67 = 0) ∧
    (∀ d : Fin 128, axisDeltaNat 1 d.val &&& maskC2_67 = 0) ∧ (∀ (ax : Fin 3) (d : Fin 128),
    axisDeltaNat ax.val d.val < 2 ^ 37 ∧ axisDeltaNat ax.val d.val &&& 8191 = 0) :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩
private theorem lemHex411 (ax : Fin 3) (d : Fin 128) {i : ℕ} (hi : isOut24Idx i = false) :
    (axisDeltaNat ax.val d.val).testBit i = false := by
  by_cases hi37 : i < 37
  · exact (by decide +kernel : ∀ (a : Fin 3) (x : Fin 128) (j : Fin 37),
      isOut24Idx j.val = false → (axisDeltaNat a.val x.val).testBit j.val = false)
      ax d ⟨i, hi37⟩ hi
  · exact Nat.testBit_lt_two_pow (lt_of_lt_of_le (lemHex410.2.2.2 ax d).1
      (Nat.pow_le_pow_right (by decide) (by omega)))
def enOfX10 (x : ℕ) : ZMod 2 := if x.testBit 0 then 1 else 0
def gammaKOfX10 (x : ℕ) : BitAssignment 6 := fun i ↦ if x.testBit (1 + i.val) then 1 else 0
def gammaPidOfX10 (x : ℕ) : BitAssignment 3 := fun i ↦ if x.testBit (7 + i.val) then 1 else 0
private theorem lemHex412 (x : Fin 1024) : bitsVal (gammaKOfX10 x.val) = (x.val / 2) % 64 :=
  lemHex401 (P := fun n ↦ bitsVal (gammaKOfX10 n) = (n / 2) % 64) (by decide +kernel) x
private theorem lemHex413 (x : Fin 1024) : bitsVal (gammaPidOfX10 x.val) = (x.val / 128) % 8 :=
  lemHex401 (P := fun n ↦ bitsVal (gammaPidOfX10 n) = (n / 128) % 8) (by decide +kernel) x
private theorem lemHex414 : (∀ (ax : Fin 3) (d : Fin 128) (b : Fin 7), (axisDeltaNat ax.val
    d.val).testBit (13 + (7 * ax.val + b.val)) = decide ((d.val / 2 ^ b.val) % 2 = 1)) ∧ (∀
    (ax : Fin 3) (d : Fin 128), (axisDeltaNat ax.val d.val).testBit (13 + (21 + ax.val)) =
    decide (d.val % 2 = 1)) ∧ (∀ (ax₁ ax₂ : Fin 3) (d : Fin 128), ax₁ ≠ ax₂ → (∀ b : Fin 7,
    (axisDeltaNat ax₁.val d.val).testBit (13 + (7 * ax₂.val + b.val)) = false) ∧ (axisDeltaNat
    ax₁.val d.val).testBit (13 + (21 + ax₂.val)) = false) :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩
private theorem lemHex416 (x : Fin 1024) (γSm : BitAssignment 3) (outIdx : Fin 24) :
    let d0 := signedCoord128 (cAxis10 x.val 0) (γSm 0 == 1)
    let d1 := signedCoord128 (cAxis10 x.val 1) (γSm 1 == 1)
    let d2 := signedCoord128 (cAxis10 x.val 2) (γSm 2 == 1)
    let Δ := axisDeltaNat 0 d0 ^^^ axisDeltaNat 1 d1 ^^^ axisDeltaNat 2 d2
    (if Δ.testBit (13 + outIdx.val) then (1 : ZMod 2) else 0) =
      headOutMask24 (enOfX10 x.val) (gammaKOfX10 x.val) (gammaPidOfX10 x.val) γSm outIdx := by
  intro d0 d1 d2 Δ
  obtain ⟨hFineBit, hParBit, hOtherZero⟩ := lemHex414
  let df : Fin 3 → Fin 128 := fun ax ↦
    ⟨signedCoord128 (cAxis10 x.val ax) (γSm ax == 1), by
      dsimp only [signedCoord128]
      split_ifs
      all_goals exact Nat.mod_lt _ (by decide)⟩
  have hΔ_df : Δ = axisDeltaNat (0 : Fin 3).val (df 0).val ^^^
      axisDeltaNat (1 : Fin 3).val (df 1).val ^^^
      axisDeltaNat (2 : Fin 3).val (df 2).val := rfl
  have hxor3 (ax : Fin 3) (idx : ℕ) (target : Bool)
      (hself : (axisDeltaNat ax.val (df ax).val).testBit idx = target)
      (hoth : ∀ j : Fin 3, j ≠ ax → (axisDeltaNat j.val (df j).val).testBit idx = false) :
      Δ.testBit idx = target := by
    rw [hΔ_df, Nat.testBit_xor, Nat.testBit_xor]
    rcases (by decide : ∀ a : Fin 3, a = 0 ∨ a = 1 ∨ a = 2) ax with rfl | rfl | rfl
    · rw [hself, hoth 1 (by decide), hoth 2 (by decide)]
      simp
    · rw [hoth 0 (by decide), hself, hoth 2 (by decide)]
      simp
    · rw [hoth 0 (by decide), hoth 1 (by decide), hself]
      simp
  have hΔ_fine : ∀ (ax : Fin 3) (b : Fin 7),
      Δ.testBit (13 + (7 * ax.val + b.val)) = decide (((df ax).val / 2 ^ b.val) % 2 = 1) :=
    fun ax b ↦ hxor3 ax _ _ (hFineBit ax (df ax) b) fun j hj ↦ (hOtherZero j ax (df j) hj).1 b
  have hΔ_par : ∀ ax : Fin 3, Δ.testBit (13 + (21 + ax.val)) = decide ((df ax).val % 2 = 1) :=
    fun ax ↦ hxor3 ax _ _ (hParBit ax (df ax)) fun j hj ↦ (hOtherZero j ax (df j) hj).2
  have hcAxis_eq : x.val.testBit 0 = true → ∀ ax : Fin 3, cAxis10 x.val ax =
      if hp : bitsVal (gammaPidOfX10 x.val) < 6 then
        bitsVal (fun b : Fin 3 ↦ headOrbitUVWTable (gammaKOfX10 x.val)
          ⟨3 * (pos24PermAxis ⟨bitsVal (gammaPidOfX10 x.val), hp⟩ ax).val + b.val, by omega⟩)
      else 0 := fun hx0 ax ↦ by
    have hk_eq := lemHex412 x
    have hp_eq := lemHex413 x
    by_cases hp6 : (x.val / 128) % 8 < 6
    · have hp6' : bitsVal (gammaPidOfX10 x.val) < 6 := hp_eq ▸ hp6
      by_cases hk56 : (x.val / 2) % 64 < 56
      · have hk56' : bitsVal (gammaKOfX10 x.val) < 56 := hk_eq ▸ hk56
        have hval : valid10 x.val = true := by simp [valid10, hx0, hk56, hp6]
        have hgk_eq : gk10 x.val = ⟨bitsVal (gammaKOfX10 x.val), hk56'⟩ :=
          Fin.ext (by simp [gk10, hk56, hval, hk_eq])
        have hgp_eq : (⟨(x.val / 128) % 8, hp6⟩ : Fin 6) =
            ⟨bitsVal (gammaPidOfX10 x.val), hp6'⟩ := Fin.ext hp_eq.symm
        simp only [cAxis10, hval, ↓reduceIte, hp6, hp6', ↓reduceDIte, hgk_eq, hgp_eq]
        exact (headOrbitUVWTable_axis hk56' _).symm
      · simp [cAxis10, valid10, hk56, hp6', headOrbitUVWTable,
          show ¬(bitsVal (gammaKOfX10 x.val) < 56) from hk_eq ▸ hk56, bitsVal]
    · simp [cAxis10, valid10, hp6, show ¬(bitsVal (gammaPidOfX10 x.val) < 6) from hp_eq ▸ hp6]
  cases hx0 : x.val.testBit 0
  · have hdf0 (a : Fin 3) : (df a).val = 0 := by simp [df, signedCoord128, cAxis10, valid10, hx0]
    simp [hΔ_df, hdf0, axisDeltaNat, enOfX10, headOutMask24, hx0]
  · by_cases hout : outIdx.val < 21
    · let ax : Fin 3 := ⟨outIdx.val / 7, div7_lt3 hout⟩
      let b : Fin 7 := ⟨outIdx.val % 7, Nat.mod_lt _ (by decide)⟩
      rw [show outIdx.val = 7 * ax.val + b.val from
        show outIdx.val = 7 * (outIdx.val / 7) + outIdx.val % 7 by omega, hΔ_fine ax b]
      simp only [enOfX10, hx0, ↓reduceIte, headOutMask24, one_ne_zero, hout, ↓reduceDIte]
      change _ = natBits 7 (signedCoord128 _ (γSm ax == 1)) b
      rw [← hcAxis_eq hx0 ax]
      simp [df, natBits]
    · let ax : Fin 3 := ⟨outIdx.val - 21, sub21_lt3 outIdx.isLt⟩
      rw [show outIdx.val = 21 + ax.val from
        show outIdx.val = 21 + (outIdx.val - 21) by omega, hΔ_par ax]
      simp only [enOfX10, hx0, ↓reduceIte, headOutMask24, one_ne_zero, hout, ↓reduceDIte]
      change _ = if (signedCoord128 _ (γSm ax == 1)) % 2 = 1 then 1 else 0
      rw [← hcAxis_eq hx0 ax]
      simp [df]
attribute [irreducible] headOutMask24
theorem evolve_headCoordXorLocal67_of_clean (β : BitAssignment 67)
    (hClean : ∀ j : Fin 30, β ⟨37 + j.val, by omega⟩ = 0) :
    headCoordXorLocal67.eval.1.mulVec (basisKet β) =
      basisKet (xorRegBits rOut24In67
        (headOutMask24 (β ⟨0, by decide⟩) (fun i : Fin 6 ↦ β ⟨1 + i.val, by omega⟩)
          (fun i : Fin 3 ↦ β ⟨7 + i.val, by omega⟩) (fun i : Fin 3 ↦ β ⟨10 + i.val, by omega⟩))
        β) := by
  let m₀ := pack67 β
  have hm₀_unpack : unpackMask67 m₀ = β := lemHex3e2 β
  rw [headCoordXorLocal67, ← hm₀_unpack, lemHex3e0 lemHex3f5 m₀, hm₀_unpack]
  apply congrArg basisKet
  let mClean := m₀ &&& 8191
  let δInit := m₀ ^^^ mClean
  have hm₀_split : m₀ = mClean ^^^ δInit := Nat.eq_of_testBit_eq fun i ↦ by
    simpa only [mClean, δInit, Nat.testBit_xor, Nat.testBit_and] using
      (by decide : ∀ a b : Bool, a = xor (a && b) (xor a (a && b)))
        (m₀.testBit i) ((8191 : ℕ).testBit i)
  have h8191_t : ∀ j : Fin 13, (8191 : ℕ).testBit j.val = true := by decide
  have hδInit_out24 : ∀ i, isOut24Idx i = false → δInit.testBit i = false := fun i hi ↦ by
    dsimp only [δInit, mClean]
    rw [Nat.testBit_xor, Nat.testBit_and]
    by_cases hi13 : i < 13
    · simp [h8191_t ⟨i, hi13⟩]
    · rw [isOut24Idx, decide_eq_false_iff_not] at hi
      simp [show m₀.testBit i = false from lemHex3e3 β hClean (by omega)]
  rw [hm₀_split, lemHex3ee lemHex3fa mClean δInit hδInit_out24]
  let x10 : Fin 1024 := ⟨mClean &&& 1023, Nat.lt_succ_of_le Nat.and_le_right⟩
  have hmClean_pre : mClean &&& preMask67 = x10.val := Nat.eq_of_testBit_eq fun i ↦ by
    simp only [x10, mClean, Nat.testBit_and]
    by_cases hi13 : i < 13
    · rw [(by decide : ∀ j : Fin 13, preMask67.testBit j.val = (1023 : ℕ).testBit j.val)
        ⟨i, hi13⟩]
    · have hlt2i : 2 ^ 13 ≤ 2 ^ i := Nat.pow_le_pow_right (by decide) (by omega)
      simp [Nat.testBit_lt_two_pow (lt_of_lt_of_le (by decide : 8191 < 2 ^ 13) hlt2i),
        Nat.testBit_lt_two_pow (lt_of_lt_of_le (by decide : 1023 < 2 ^ 13) hlt2i)]
  let m₁ := runMask67 preGates67 mClean
  have hm₁_eq : m₁ = (mClean ^^^ x10.val) ^^^ runMask67 preGates67 x10.val := by
    simpa only [hmClean_pre] using lemHex3f1 lemHex3fc mClean
  let neg (k : ℕ) : Fin 2 :=
    ⟨if mClean.testBit k then 1 else 0, Bool.recOn (mClean.testBit k) (by decide) (by decide)⟩
  have hsm_maskC : ((mClean ^^^ x10.val) &&& maskC0_67 = (neg 10).val * 2 ^ 10) ∧
      ((mClean ^^^ x10.val) &&& maskC1_67 = (neg 11).val * 2 ^ 11) ∧
      ((mClean ^^^ x10.val) &&& maskC2_67 = (neg 12).val * 2 ^ 12) :=
    lemHex402 (P := fun n ↦
      let sb := n ^^^ (n &&& 1023)
      (sb &&& maskC0_67 = (if n.testBit 10 then 1 else 0) * 2 ^ 10) ∧
      (sb &&& maskC1_67 = (if n.testBit 11 then 1 else 0) * 2 ^ 11) ∧
      (sb &&& maskC2_67 = (if n.testBit 12 then 1 else 0) * 2 ^ 12))
      (by decide +kernel) ⟨mClean, Nat.lt_succ_of_le Nat.and_le_right⟩
  obtain ⟨hyC0, hyC1, hyC2⟩ := lemHex40c x10
  let cAx (ax : Fin 3) : Fin 6 := ⟨cAxis10 x10.val ax, lemHex40b x10 ax⟩
  let dNat (ax : Fin 3) (k : ℕ) : Fin 128 :=
    ⟨signedCoord128 (cAx ax).val ((neg k).val == 1), pos24_oh_lt128 _ _⟩
  let Δ0 := axisDeltaNat 0 (dNat 0 10).val
  let Δ1 := axisDeltaNat 1 (dNat 1 11).val
  let Δ2 := axisDeltaNat 2 (dNat 2 12).val
  obtain ⟨hD01, hD02, hD12, _⟩ := lemHex410
  have hStC {gs : List RevGate67} {M u c δ : ℕ} (hm : gs.all (RevGate67.inMask M) = true)
      (hmask : u &&& M = c) (hrun : runMask67 gs c = c ^^^ δ) : runMask67 gs u = u ^^^ δ := by
    rw [lemHex3f1 hm u, hmask, hrun, ← hmask, ← lemHex3e6, lemHex3e4]
  have hStageC0 := hStC (u := m₁) lemHex3fe (by rw [hm₁_eq, lemHex3e7, hsm_maskC.1, hyC0])
    (lemHex40d (cAx 0) (neg 10))
  have hStageC1 := hStC (u := m₁ ^^^ Δ0) lemHex3ff
    (by rw [lemHex3e8 (hD01 (dNat 0 10)), hm₁_eq, lemHex3e7, hsm_maskC.2.1, hyC1])
    (lemHex40e (cAx 1) (neg 11))
  have hStageC2 := hStC (u := (m₁ ^^^ Δ0) ^^^ Δ1) lemHex400
    (by rw [lemHex3e8 (hD12 (dNat 1 11)), lemHex3e8 (hD02 (dNat 0 10)), hm₁_eq, lemHex3e7,
      hsm_maskC.2.2,
      hyC2]) (lemHex40f (cAx 2) (neg 12))
  let Δ := (Δ0 ^^^ Δ1) ^^^ Δ2
  have hΔ_out24 : ∀ i, isOut24Idx i = false → Δ.testBit i = false := fun i hi ↦ by
    change (axisDeltaNat (0 : Fin 3).val (dNat 0 10).val ^^^
      axisDeltaNat (1 : Fin 3).val (dNat 1 11).val ^^^
      axisDeltaNat (2 : Fin 3).val (dNat 2 12).val).testBit i = false
    rw [Nat.testBit_xor, Nat.testBit_xor, lemHex411 0 (dNat 0 10) hi, lemHex411 1 (dNat 1 11) hi,
      lemHex411 2 (dNat 2 12) hi]
    rfl
  have hFull : (runMask67 fullGates67 mClean) ^^^ δInit = m₀ ^^^ Δ := by
    dsimp only [fullGates67, stageCGates67]
    rw [List.append_assoc, lemHex3e9, show runMask67 preGates67 mClean = m₁ from rfl, lemHex3e9,
      List.append_assoc, lemHex3e9, hStageC0, lemHex3e9, hStageC1, hStageC2, lemHex3e6 m₁ Δ0 Δ1,
      lemHex3e6 m₁ (Δ0 ^^^ Δ1) Δ2, lemHex3ee lemHex3f9 m₁ Δ hΔ_out24, lemHex3ec lemHex3f3 mClean,
      lemHex3e5 mClean Δ δInit, ← hm₀_split]
  rw [hFull]
  have hmClean_tb : ∀ j : Fin 13, mClean.testBit j.val = m₀.testBit j.val := fun j ↦ by
    simp [mClean, h8191_t j]
  have hx10_z2 : ∀ j : Fin 10, (if x10.val.testBit j.val then (1 : ZMod 2) else 0) =
      β ⟨j.val, lt_trans j.isLt (by decide)⟩ := fun j ↦ by
    have h1023 := (by decide : ∀ k : Fin 10, (1023 : ℕ).testBit k.val = true) j
    simpa [x10, h1023, hmClean_tb ⟨j.val, lt_trans j.isLt (by decide)⟩, unpackMask67] using
      congrFun hm₀_unpack ⟨j.val, lt_trans j.isLt (by decide)⟩
  let γSm : BitAssignment 3 := fun i ↦ β ⟨10 + i.val, by omega⟩
  have hneg_sm : ∀ ax : Fin 3, ((neg (10 + ax.val)).val == 1) = (γSm ax == 1) := fun ax ↦ by
    dsimp only [γSm, neg]
    rw [← congrFun hm₀_unpack ⟨10 + ax.val, by omega⟩, hmClean_tb ⟨10 + ax.val, by omega⟩]
    exact (by decide : ∀ b : Bool,
      (((if b then (1 : ℕ) else 0) == 1) = ((if b then (1 : ZMod 2) else 0) == 1)))
      (m₀.testBit (10 + ax.val))
  rw [show β ⟨0, by decide⟩ = enOfX10 x10.val from (hx10_z2 ⟨0, by decide⟩).symm,
    show (fun i : Fin 6 ↦ β ⟨1 + i.val, by omega⟩) = gammaKOfX10 x10.val from
      funext fun i ↦ (hx10_z2 ⟨1 + i.val, by omega⟩).symm,
    show (fun i : Fin 3 ↦ β ⟨7 + i.val, by omega⟩) = gammaPidOfX10 x10.val from
      funext fun i ↦ (hx10_z2 ⟨7 + i.val, by omega⟩).symm]
  funext q
  rw [show unpackMask67 (m₀ ^^^ Δ) q = β q + (if Δ.testBit q.val then (1 : ZMod 2) else 0) by
    rw [← congrFun hm₀_unpack q]
    dsimp only [unpackMask67]
    rw [Nat.testBit_xor]
    exact (by decide : ∀ a b : Bool, (if xor a b then (1 : ZMod 2) else 0) =
      (if a then 1 else 0) + (if b then 1 else 0)) (m₀.testBit q.val) (Δ.testBit q.val)]
  by_cases hqRange : 13 ≤ q.val ∧ q.val < 37
  · let outIdx : Fin 24 := ⟨q.val - 13, by omega⟩
    have hq_reg : q = rOut24In67 outIdx := Fin.ext (show q.val = 13 + (q.val - 13) by omega)
    rw [show q.val = 13 + outIdx.val from show q.val = 13 + (q.val - 13) by omega, hq_reg,
      xorRegBits_apply_reg]
    apply congrArg (fun z : ZMod 2 ↦ β (rOut24In67 outIdx) + z)
    rw [show Δ = axisDeltaNat 0 (signedCoord128 (cAxis10 x10.val 0) (γSm 0 == 1)) ^^^
        axisDeltaNat 1 (signedCoord128 (cAxis10 x10.val 1) (γSm 1 == 1)) ^^^
        axisDeltaNat 2 (signedCoord128 (cAxis10 x10.val 2) (γSm 2 == 1)) by
      dsimp only [Δ, Δ0, Δ1, Δ2, dNat, cAx]
      rw [show ((neg 10).val == 1) = (γSm 0 == 1) from hneg_sm 0,
        show ((neg 11).val == 1) = (γSm 1 == 1) from hneg_sm 1,
        show ((neg 12).val == 1) = (γSm 2 == 1) from hneg_sm 2]]
    exact lemHex416 x10 γSm outIdx
  · have hnotMem : q ∉ rOut24In67.image := fun hm ↦ by
      obtain ⟨j, hj⟩ := (QRegister.mem_image _ q).mp hm
      have hv : 13 + j.val = q.val := congrArg Fin.val hj
      omega
    rw [xorRegBits_apply_of_not_mem _ _ _ hnotMem, hΔ_out24 q.val (decide_eq_false hqRange)]
    simp
attribute [irreducible] headCoordXorLocal67
noncomputable abbrev headCoordXorSub80Fn (β : BitAssignment 80) : BitAssignment 80 :=
  let mask24 := headOutMask24 (β 30) (fun i : Fin 6 ↦ β ⟨63 + i.val, idx63_lt80 i⟩)
      (fun i : Fin 3 ↦ β ⟨69 + i.val, idx69_lt80 i⟩)
      (fun i : Fin 3 ↦ β ⟨72 + i.val, idx72_lt80 i⟩)
  fun q ↦
    if h0 : q.val < 3 then β q + mask24 ⟨21 + q.val, idx21_lt24 h0⟩
    else if h1 : 32 ≤ q.val ∧ q.val < 53 then β q + mask24 ⟨q.val - 32, sub32_lt24 h1⟩
    else β q
theorem headCoordXorSub80Fn_of_clean (β : BitAssignment 80) (hen : β 30 = 1)
    (hk : bitsVal (fun i : Fin 6 ↦ β ⟨63 + i.val, by omega⟩) < 56)
    (hp : bitsVal (fun i : Fin 3 ↦ β ⟨69 + i.val, by omega⟩) < 6)
    (hb1 : ∀ ax : Fin 3, β ⟨ax.val, by omega⟩ = 0)
    (hfine : ∀ j : Fin 30, β ⟨32 + j.val, by omega⟩ = 0) :
    let k : Fin 56 := ⟨bitsVal (fun i : Fin 6 ↦ β ⟨63 + i.val, by omega⟩), hk⟩
    let pid : Fin 6 := ⟨bitsVal (fun i : Fin 3 ↦ β ⟨69 + i.val, by omega⟩), hp⟩
    let sm : Fin 8 := ⟨bitsVal (fun i : Fin 3 ↦ β ⟨72 + i.val, by omega⟩),
      bitsVal3_lt8 (fun i : Fin 3 ↦ β ⟨72 + i.val, by omega⟩)⟩
    let dH := pos24OhPoint (pos24HeadU56 k) (pos24HeadV56 k) (pos24HeadW56 k) pid sm
    let dpH := ((dH 0).val % 2) + 2 * ((dH 1).val % 2) + 4 * ((dH 2).val % 2)
    let fineH := (dH 0).val + 128 * (dH 1).val + 16384 * (dH 2).val
    (∀ ax : Fin 3, headCoordXorSub80Fn β ⟨ax.val, by omega⟩ =
      if ((dpH / 2 ^ ax.val) % 2) = 1 then 1 else 0) ∧
    (∀ j : Fin 30, headCoordXorSub80Fn β ⟨32 + j.val, by omega⟩ =
      if ((fineH / 2 ^ j.val) % 2) = 1 then 1 else 0) ∧
    (∀ q : Fin 80, ¬ (q.val < 3) → ¬ (32 ≤ q.val ∧ q.val < 62) →
      headCoordXorSub80Fn β q = β q) := by
  intro k pid sm dH dpH fineH
  obtain ⟨hFine, hPar⟩ := headOutMask24_of_valid (fun i : Fin 6 ↦ β ⟨63 + i.val, by omega⟩)
    (fun i : Fin 3 ↦ β ⟨69 + i.val, by omega⟩) (fun i : Fin 3 ↦ β ⟨72 + i.val, by omega⟩) hk hp
  change ∀ (ax : Fin 3) (b : Fin 7),
    headOutMask24 1 _ _ _ ⟨7 * ax.val + b.val, _⟩ = natBits 7 (dH ax).val b at hFine
  change ∀ ax : Fin 3,
    headOutMask24 1 _ _ _ ⟨21 + ax.val, _⟩ = if (dH ax).val % 2 = 1 then 1 else 0 at hPar
  refine ⟨fun ax ↦ ?_, fun j ↦ ?_, fun q hq0 hq1 ↦ ?_⟩
  · simp only [headCoordXorSub80Fn, ax.isLt, ↓reduceDIte, hen, hb1 ax, zero_add, hPar ax]
    congr 1
    apply propext
    dsimp only [dpH]
    fin_cases ax
    all_goals
      dsimp only
      norm_num
      omega
  · by_cases hj21 : j.val < 21
    · let ax : Fin 3 := ⟨j.val / 7, div7_lt3 hj21⟩
      let b : Fin 7 := ⟨j.val % 7, Nat.mod_lt _ (by decide)⟩
      have h1 : 32 ≤ 32 + j.val ∧ 32 + j.val < 53 := by omega
      have hj_eq : (⟨32 + j.val - 32, sub32_lt24 h1⟩ : Fin 24) =
          ⟨7 * ax.val + b.val, by omega⟩ :=
        Fin.ext (show 32 + j.val - 32 = 7 * (j.val / 7) + j.val % 7 by omega)
      simp only [headCoordXorSub80Fn, show ¬(32 + j.val < 3) by omega, h1, ↓reduceDIte, hen,
        hfine j, zero_add, hj_eq, hFine ax b, natBits]
      rw [show j.val = 7 * ax.val + b.val from
          show j.val = 7 * (j.val / 7) + j.val % 7 by omega,
        pack3x7_bit (dH 0).val (dH 1).val (dH 2).val (dH 0).isLt (dH 1).isLt (dH 2).isLt ax b,
        (show ∀ a : Fin 3,
          (if a = 0 then (dH 0).val else if a = 1 then (dH 1).val else (dH 2).val) =
            (dH a).val from fun a ↦ by
            fin_cases a
            all_goals rfl) ax]
      simp
    · have := (dH 0).isLt
      have := (dH 1).isLt
      have := (dH 2).isLt
      have hzero : fineH / 2 ^ j.val = 0 := Nat.div_eq_of_lt (lt_of_lt_of_le
        (show fineH < 2 ^ 21 by omega) (Nat.pow_le_pow_right (by decide) (by omega)))
      simp [headCoordXorSub80Fn, show ¬(32 + j.val < 3) by omega,
        show ¬(32 + j.val < 53) by omega, hfine j, hzero]
  · simp [headCoordXorSub80Fn, hq0,
      show ¬(32 ≤ q.val ∧ q.val < 53) from fun h ↦ hq1 ⟨h.1, by omega⟩]
end ConfigPos24HeadCoordXor80
end Pos24HeadCoordXor80
end
end ModPos24HeadCoordXor80

section ModWeighted3APolymorphicTopClosure
@[expose] public section
namespace PolymorphicTopClosure
open Operator Matrix QProg Circuit _root_.DynamicCircuit DynCircuitExt Real
open SpecsAux.SpecMirror
open SpecsAux.BridgeFermionicComm
open SpecsAux.BridgeFermionicComm.SpecInner
open SpecsAux.FullScaleBESector
open SpecsAux.PhaseGradCatalystCore
open SpecsAux.BridgeDuhamel
open PhaseGradSignalRot hiding IntertwinesCat
open FullSysCatSegmentBridge
open TFreeLaurentGQSP
open CatalyzedLaurentGQSP BidirectionalCatalyzedGQSP
open BidirectionalCatalyzedGQSPBridge
open scoped Matrix Matrix.Norms.L2Operator BigOperators
instance (priority := 100000) instNeZeroTwoPowPolyClosure (k : ℕ) : NeZero (2 ^ k) :=
  ⟨Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos k)⟩
theorem inv_mul_cancel_val_gen {d : ℕ} (U : Unitary d) : (U⁻¹).1 * U.1 = 1 := congrArg
    Subtype.val (inv_mul_cancel U)
theorem embedMatrix_neg_poly {k N : ℕ} (r : QRegister k N) (X : Operator (2 ^ k)) :
    r.embedMatrix (-X) = -r.embedMatrix X := by
  rw [← neg_one_smul ℂ X, r.embedMatrix_smul, neg_one_smul]
theorem intertwinesCat_refl_of_comm_gen {d : ℕ} {U P X : Operator d} (hU : X * U = U * X)
    (hP : X * P = P * X) : IntertwinesCat U P X X :=
  ⟨by rw [hU], hU, hP⟩
theorem intertwinesCat_add_gen {d : ℕ} {U P M1 E1 M2 E2 : Operator d}
    (h1 : IntertwinesCat U P M1 E1) (h2 : IntertwinesCat U P M2 E2) :
    IntertwinesCat U P (M1 + M2) (E1 + E2) :=
  ⟨by simp only [Matrix.add_mul, Matrix.mul_add, h1.1, h2.1],
   by simp only [Matrix.add_mul, Matrix.mul_add, h1.2.1, h2.2.1],
   by simp only [Matrix.add_mul, Matrix.mul_add, h1.2.2, h2.2.2]⟩
theorem intertwinesCat_mul_gen {d : ℕ} {U P M1 E1 M2 E2 : Operator d}
    (h1 : IntertwinesCat U P M1 E1) (h2 : IntertwinesCat U P M2 E2) :
    IntertwinesCat U P (M1 * M2) (E1 * E2) :=
  ⟨by rw [Matrix.mul_assoc M1 M2 U, Matrix.mul_assoc M1 (M2 * U) P, h2.1,
        Matrix.mul_assoc U E2 P, h2.2.2, ← Matrix.mul_assoc U P E2,
        ← Matrix.mul_assoc M1 (U * P) E2, ← Matrix.mul_assoc M1 U P, h1.1,
        Matrix.mul_assoc U E1 P, Matrix.mul_assoc U (E1 * P) E2, Matrix.mul_assoc E1 P E2,
        ← h2.2.2, ← Matrix.mul_assoc E1 E2 P, ← Matrix.mul_assoc U (E1 * E2) P],
   by rw [Matrix.mul_assoc, h2.2.1, ← Matrix.mul_assoc, h1.2.1, Matrix.mul_assoc],
   by rw [Matrix.mul_assoc, h2.2.2, ← Matrix.mul_assoc, h1.2.2, Matrix.mul_assoc]⟩
abbrev mSegAncPoly (mPayload : ℕ) : ℕ := 1 + fullSysRawAncWires mPayload
theorem update_eq_self_of_eq {α : Type*} [DecidableEq α] {γ : Type*} (f : α → γ) (a : α)
    {v : γ} (hv : f a = v) : Function.update f a v = f :=
  Function.update_eq_self_iff.mpr hv.symm
private theorem singleton_proj_bit_mulVec_ket {N : ℕ} (q : Wire N) (b : Fin 2)
    (β : BitAssignment N) :
    ((QRegister.singleton q).basisOutcomeProjector b).mulVec (ket β) =
      if β q = (b.val : ZMod 2) then ket β else 0 := by
  rw [QRegister.basisOutcomeProjector, singleton_embedMatrix_mulVec_ket]
  fin_cases b
  all_goals
    rcases bit_cases (β q) with hq | hq
    all_goals simp [hq, update_eq_self_of_eq β q hq, compProj, Matrix.single]
theorem singleton_proj_zero_mulVec_ket {N : ℕ} (q : Wire N) (β : BitAssignment N) :
    ((QRegister.singleton q).basisOutcomeProjector 0).mulVec (ket β) =
      if β q = 0 then ket β else 0 := singleton_proj_bit_mulVec_ket q 0 β
theorem singleton_proj_one_mulVec_ket {N : ℕ} (q : Wire N) (β : BitAssignment N) :
    ((QRegister.singleton q).basisOutcomeProjector 1).mulVec (ket β) =
      if β q = 1 then ket β else 0 := singleton_proj_bit_mulVec_ket q 1 β
theorem singleton_proj_zero_add_one {N : ℕ} (q : Wire N) :
    (QRegister.singleton q).basisOutcomeProjector 0 +
      (QRegister.singleton q).basisOutcomeProjector 1 = 1 :=
  matrix_ext_ket fun β ↦ by
    rw [Matrix.add_mulVec, Matrix.one_mulVec,
      singleton_proj_zero_mulVec_ket, singleton_proj_one_mulVec_ket]
    rcases bit_cases (β q) with hq | hq
    all_goals simp [hq]
theorem embedMatrix_diagonal_mulVec_ket {k N : ℕ} (r : QRegister k N)
    (d : Fin (2 ^ k) → ℂ) (β : BitAssignment N) :
    (r.embedMatrix (Matrix.diagonal d)).mulVec (ket β) = d (localIdx r β) • ket β := by
  rw [embedMatrix_mulVec_ket, Finset.sum_eq_single (localIdx r β)]
  · have hw : writeReg β r (basisBits k (localIdx r β)) = β := by
      classical
      ext w
      by_cases hmem : w ∈ Set.range r.wires
      · rcases hmem with ⟨i, rfl⟩
        rw [writeReg_apply_reg]
        exact congrFun (Equiv.apply_symm_apply (basisBitsEquiv k) (fun j ↦ β (r j))) i
      · exact writeReg_apply_of_not_mem _ _ _ _ hmem
    rw [hw]
    simp [Matrix.diagonal]
  · intro l _ hl
    simp [Matrix.diagonal, hl]
  · simp
theorem zmod2_add_self (x : ZMod 2) : x + x = 0 :=
  (by decide : ∀ y : ZMod 2, y + y = 0) x
theorem zmod2_add_one_add_one (x : ZMod 2) : x + 1 + 1 = x :=
  (by decide : ∀ y : ZMod 2, y + 1 + 1 = y) x
theorem update_idem_val {α : Type*} [DecidableEq α] {γ : Type*} (f : α → γ) (a : α) (u v : γ) :
    Function.update (Function.update f a u) a v = Function.update f a v :=
  Function.update_idem u v f
theorem revStep_run_x {N : ℕ} (q : Wire N) (β : BitAssignment N) :
    (RevStep.x q).run β = Function.update β q (β q + 1) := rfl
private theorem run_cnot_ne {N : ℕ} {c t : Wire N} (h : c ≠ t) (β : BitAssignment N) :
    (RevStep.cnot c t).run β = Function.update β t (β t + β c) := ite_eq_left h
private theorem run_toff_ne {N : ℕ} {c₁ c₂ t : Wire N} (h12 : c₁ ≠ c₂) (h1t : c₁ ≠ t)
    (h2t : c₂ ≠ t) (β : BitAssignment N) :
    (RevStep.toff c₁ c₂ t).run β = Function.update β t (β t + β c₁ * β c₂) :=
  ite_eq_left ⟨h12, h1t, h2t⟩
private theorem parkZero_run {N : ℕ} {qS qC qV : Wire N} (hSC : qS ≠ qC) (hSV : qS ≠ qV)
    (hCV : qC ≠ qV) (ss : List (RevStep N)) (β : BitAssignment N) (hv : β qV = 0) :
    runRevList (RevStep.toff qS qC qV :: RevStep.cnot qV qC :: ss) β =
      runRevList ss (Function.update (Function.update β qV (β qS * β qC))
        qC (β qC + β qS * β qC)) := by
  dsimp only [runRevList]
  rw [run_toff_ne hSC hSV hCV, hv, zero_add, run_cnot_ne hCV.symm,
    Function.update_of_ne hCV, Function.update_self]
theorem parkZero_on_zero {N : ℕ} {qS qC qV : Wire N} (hSC : qS ≠ qC) (hSV : qS ≠ qV)
    (hCV : qC ≠ qV) (ss : List (RevStep N)) (β : BitAssignment N) (hs : β qS = 0)
    (hv : β qV = 0) :
    runRevList (RevStep.toff qS qC qV :: RevStep.cnot qV qC :: ss) β = runRevList ss β := by
  rw [parkZero_run hSC hSV hCV ss β hv, hs, zero_mul, add_zero,
    update_eq_self_of_eq β qV hv, update_eq_self_of_eq β qC rfl]
theorem parkZero_on_one {N : ℕ} {qS qC qV : Wire N} (hSC : qS ≠ qC) (hSV : qS ≠ qV)
    (hCV : qC ≠ qV) (ss : List (RevStep N)) (β : BitAssignment N) (hs : β qS = 1)
    (hv : β qV = 0) : runRevList (RevStep.toff qS qC qV :: RevStep.cnot qV qC :: ss) β =
    runRevList ss (Function.update (Function.update β qV (β qC)) qC 0) := by
  rw [parkZero_run hSC hSV hCV ss β hv, hs, one_mul, zmod2_add_self]
private theorem parkOne_run {N : ℕ} {qS qC qV : Wire N} (hSC : qS ≠ qC) (hSV : qS ≠ qV)
    (hCV : qC ≠ qV) (ss : List (RevStep N)) (β : BitAssignment N) (hv : β qV = 0) :
    runRevList (RevStep.x qC :: RevStep.toff qS qC qV :: RevStep.x qC ::
      RevStep.cnot qV qC :: ss) β =
    runRevList ss (Function.update (Function.update β qV (β qS * (β qC + 1)))
      qC (β qC + β qS * (β qC + 1))) := by
  simp only [runRevList, revStep_run_x, run_toff_ne hSC hSV hCV, run_cnot_ne hCV.symm,
    Function.update_self, Function.update_of_ne hCV, Function.update_of_ne hCV.symm,
    Function.update_of_ne hSC, hv, zero_add, zmod2_add_one_add_one]
  rw [update_idem_val, Function.update_comm hCV, update_idem_val]
theorem parkOne_on_zero {N : ℕ} {qS qC qV : Wire N} (hSC : qS ≠ qC) (hSV : qS ≠ qV)
    (hCV : qC ≠ qV) (ss : List (RevStep N)) (β : BitAssignment N) (hs : β qS = 0)
    (hv : β qV = 0) : runRevList (RevStep.x qC :: RevStep.toff qS qC qV :: RevStep.x qC ::
    RevStep.cnot qV qC :: ss) β = runRevList ss β := by
  rw [parkOne_run hSC hSV hCV ss β hv, hs, zero_mul, add_zero,
    update_eq_self_of_eq β qV hv, update_eq_self_of_eq β qC rfl]
theorem parkOne_on_one {N : ℕ} {qS qC qV : Wire N} (hSC : qS ≠ qC) (hSV : qS ≠ qV)
    (hCV : qC ≠ qV) (ss : List (RevStep N)) (β : BitAssignment N) (hs : β qS = 1)
    (hv : β qV = 0) : runRevList (RevStep.x qC :: RevStep.toff qS qC qV :: RevStep.x qC ::
    RevStep.cnot qV qC :: ss) β = runRevList ss
    (Function.update (Function.update β qV (β qC + 1)) qC 1) := by
  rw [parkOne_run hSC hSV hCV ss β hv, hs, one_mul,
    (by decide : ∀ y : ZMod 2, y + (y + 1) = 1) (β qC)]
def revStepDisjointFromReg {k N : ℕ} (r : QRegister k N) : RevStep N → Prop
  | RevStep.x q => q ∉ Set.range r.wires
  | RevStep.cnot c t => c ∉ Set.range r.wires ∧ t ∉ Set.range r.wires
  | RevStep.toff c₁ c₂ t =>
      c₁ ∉ Set.range r.wires ∧ c₂ ∉ Set.range r.wires ∧ t ∉ Set.range r.wires
private theorem revStep_comm_embedMatrix {k N : ℕ} (r : QRegister k N) (X : Operator (2 ^ k))
    (s : RevStep N) (hs : revStepDisjointFromReg r s) :
    s.toCircuit.eval.1 * r.embedMatrix X = r.embedMatrix X * s.toCircuit.eval.1 := by
  have hd {m : ℕ} (g : QRegister m N) (U : Unitary (2 ^ m)) (hg : ∀ i, g i ∉ Set.range r.wires) :
      (g.embedUnitary U).1 * r.embedMatrix X = r.embedMatrix X * (g.embedUnitary U).1 :=
    g.embedMatrix_comm_of_disjoint r (QRegister.disjoint_iff.mpr fun i j h ↦ hg i ⟨j, h.symm⟩) U.1 X
  cases s with
  | x q =>
      rw [RevStep.toCircuit, Circuit.eval_single]
      exact hd (QRegister.singleton q) _ fun i ↦ Fin.fin_one_eq_zero i ▸ hs
  | cnot _ _ =>
      dsimp only [RevStep.toCircuit]
      split_ifs
      · rw [Circuit.eval_gate]
        exact hd _ _ (Fin.cases hs.1 fun i ↦ Fin.fin_one_eq_zero i ▸ hs.2)
      · simp
  | toff _ _ _ =>
      dsimp only [RevStep.toCircuit]
      split_ifs
      · rw [Circuit.eval_gate]
        exact hd _ _ (Fin.cases hs.1 (Fin.cases hs.2.1 fun i ↦ Fin.fin_one_eq_zero i ▸ hs.2.2))
      · simp
theorem compileRevList_comm_embedMatrix {k N : ℕ} (r : QRegister k N) (X : Operator (2 ^ k))
    (steps : List (RevStep N)) (hSteps : ∀ s ∈ steps, revStepDisjointFromReg r s) :
    (compileRevList steps).eval.1 * r.embedMatrix X =
      r.embedMatrix X * (compileRevList steps).eval.1 := by
  induction steps with
  | nil => simp [compileRevList]
  | cons s rest ih =>
      simp only [compileRevList, Circuit.eval_seq, Submonoid.coe_mul]
      rw [Matrix.mul_assoc, revStep_comm_embedMatrix r X s (hSteps s List.mem_cons_self),
        ← Matrix.mul_assoc, ih (fun s' hs' ↦ hSteps s' (List.mem_cons_of_mem s hs')),
        Matrix.mul_assoc]
theorem embedMatrix_intertwinesCat {m N : ℕ} (r : QRegister m N)
    {U P M E : Operator (2 ^ m)} (h : IntertwinesCat U P M E) :
    IntertwinesCat (r.embedMatrix U) (r.embedMatrix P) (r.embedMatrix M) (r.embedMatrix E) :=
  ⟨by rw [← r.embedMatrix_mul, ← r.embedMatrix_mul, h.1, r.embedMatrix_mul, r.embedMatrix_mul],
   by rw [← r.embedMatrix_mul, h.2.1, r.embedMatrix_mul],
   by rw [← r.embedMatrix_mul, h.2.2, r.embedMatrix_mul]⟩
theorem conj_X_sig_swap {N : ℕ} (q : Wire N) (A B : Operator (2 ^ N))
    (hAX : A * (Circuit.X q).eval.1 = (Circuit.X q).eval.1 * A)
    (hBX : B * (Circuit.X q).eval.1 = (Circuit.X q).eval.1 * B) :
    let P0 := (QRegister.singleton q).basisOutcomeProjector 0
    let P1 := (QRegister.singleton q).basisOutcomeProjector 1
    (Circuit.X q).eval.1 * ((A * P0 + B * P1) * (Circuit.X q).eval.1) =
      B * P0 + A * P1 := by
  intro P0 P1
  have hXb (b : Fin 2) : (Circuit.X q).eval.1 *
      (QRegister.singleton q).basisOutcomeProjector b * (Circuit.X q).eval.1 =
      (QRegister.singleton q).basisOutcomeProjector (1 - b) :=
    matrix_ext_ket fun β ↦ by
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ket_X]
      rcases (by decide : ∀ x : Fin 2, x = 0 ∨ x = 1) b with rfl | rfl
      all_goals
        simp only [sub_zero, sub_self, singleton_proj_zero_mulVec_ket,
          singleton_proj_one_mulVec_ket, Function.update_self]
        rcases bit_cases (β q) with hq | hq
        all_goals simp only [hq, one_add_one_zmod2, zero_add, one_ne_zero, zero_ne_one, ↓reduceIte,
          Matrix.mulVec_zero, ket_X, Function.update_self, update_idem_val,
          update_eq_self_of_eq β q hq]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (Circuit.X q).eval.1 A, ← hAX, Matrix.mul_assoc A,
    ← Matrix.mul_assoc (Circuit.X q).eval.1 P0, hXb 0,
    ← Matrix.mul_assoc (Circuit.X q).eval.1 B, ← hBX, Matrix.mul_assoc B,
    ← Matrix.mul_assoc (Circuit.X q).eval.1 P1, hXb 1, sub_zero, sub_self, add_comm]
theorem approximatesTimeEvolution_embed_block0 {k m₀ m : ℕ}
    (r₀ : QRegister (k + m₀) (k + m)) (sub : QRegister m₀ m)
    (hSys : r₀.compose (QRegister.block 0 k (by omega)) = QRegister.block 0 k (by omega))
    (hAnc : r₀.compose (QRegister.block k m₀ le_rfl) =
      (QRegister.block k m le_rfl).compose sub)
    {H : Operator (2 ^ k)} {t ε : ℝ} {P : Operator (2 ^ k)} {W₀ : Unitary (2 ^ (k + m₀))}
    (h₀ : ApproximatesTimeEvolution (m := m₀) H t ε P W₀) :
    ApproximatesTimeEvolution (m := m) H t ε P (r₀.embedUnitary W₀) := by
  rcases h₀ with ⟨φ, hφ⟩
  refine ⟨φ, ?_⟩
  let sys₀ : QRegister k (k + m₀) := QRegister.block 0 k (by omega)
  let anc₀ : QRegister m₀ (k + m₀) := QRegister.block k m₀ le_rfl
  let sys : QRegister k (k + m) := QRegister.block 0 k (by omega)
  let anc : QRegister m (k + m) := QRegister.block k m le_rfl
  let E_exp : Operator (2 ^ k) := NormedSpace.exp ((-Complex.I * (t : ℂ)) • H)
  have hIn : r₀.embedMatrix (sys₀.embedMatrix P * anc₀.basisOutcomeProjector 0) *
      anc.basisOutcomeProjector 0 = sys.embedMatrix P * anc.basisOutcomeProjector 0 := by
    rw [r₀.embedMatrix_mul, ← QRegister.embedMatrix_compose, hSys, Matrix.mul_assoc,
      QRegister.basisOutcomeProjector, ← QRegister.embedMatrix_compose, hAnc,
      ← QRegister.basisOutcomeProjector,
      TFreeLaurentGQSP.basisOutcomeProjector_zero_compose_mul anc sub]
  have hProd : ((r₀.embedUnitary W₀).1 - Complex.exp (φ * Complex.I) • sys.embedMatrix E_exp) *
      (sys.embedMatrix P * anc.basisOutcomeProjector 0) =
      r₀.embedMatrix ((W₀.1 - Complex.exp (φ * Complex.I) • sys₀.embedMatrix E_exp) *
        (sys₀.embedMatrix P * anc₀.basisOutcomeProjector 0)) *
          anc.basisOutcomeProjector 0 := by
    rw [← hIn, ← Matrix.mul_assoc, QRegister.embedUnitary_val,
      show sys.embedMatrix E_exp = r₀.embedMatrix (sys₀.embedMatrix E_exp) by
        rw [← QRegister.embedMatrix_compose, hSys],
      ← r₀.embedMatrix_smul, ← BridgeDuhamel.embedMatrix_sub, ← r₀.embedMatrix_mul]
  rw [hProd]
  refine (norm_mul_le _ _).trans ((mul_le_mul (BridgeDuhamel.norm_embedMatrix_le r₀ _)
    (BridgeDuhamel.norm_basisOutcomeProjector_le_one anc 0)
    (norm_nonneg _) (norm_nonneg _)).trans ?_)
  rwa [mul_one]
end PolymorphicTopClosure
end
end ModWeighted3APolymorphicTopClosure

section ModFusedPreDiagFromTwist288
@[expose] public section
namespace FusedPreDiagFromTwist288Alt
theorem qreg_block_apply {n : ℕ} (offset width : ℕ) (h : offset + width ≤ n) (i : Fin width) :
    QRegister.block offset width h i = ⟨offset + i.val, by omega⟩ := rfl
theorem qreg_block_wires_apply {n : ℕ} (offset width : ℕ) (h : offset + width ≤ n) (i : Fin width) :
    (QRegister.block offset width h).wires i = ⟨offset + i.val, by omega⟩ := rfl
theorem qreg_slice_wires {k n : ℕ} (r : QRegister k n) (offset width : ℕ)
    (h : offset + width ≤ k) (i : Fin width) :
    (r.slice offset width h).wires i = r.wires ⟨offset + i.val, by omega⟩ := rfl
theorem qreg_compose_wires {m k n : ℕ} (outer : QRegister k n) (inner : QRegister m k) (i : Fin m) :
    (outer.compose inner).wires i = outer.wires (inner.wires i) := rfl
theorem qreg_whole_wires {n : ℕ} (i : Fin n) : (QRegister.whole n).wires i = i := rfl
theorem emb_refl_apply {α : Type*} (x : α) : (Function.Embedding.refl α) x = x := rfl
theorem emb_mk_apply {α β : Type*} (f : α → β) (h : Function.Injective f) (x : α) :
    ({ toFun := f, inj' := h } : α ↪ β) x = f x := rfl
theorem emb_trans_apply {α β γ : Type*} (f : α ↪ β) (g : β ↪ γ) (x : α) :
    (f.trans g) x = g (f x) := rfl
end FusedPreDiagFromTwist288Alt
namespace FusedPreDiagFromTwist288
section ConfigFusedPreDiagFromTwist288
set_option exponentiation.threshold 256
open Operator QProg Matrix _root_.DynamicCircuit DynCircuitExt
open scoped Matrix BigOperators Circuit.Notation
open SpecsAux.SpecMirror
open SpecsAux.PhaseGradCatalystCore
open DyadicQft64 hiding dyadicTurn phaseGradKet
open KaratsubaQft64Matrix
open DyadicQft64Engine
open DyadicQft64WalkCircuit
open PosMomSelectSandwich (slotBitProj)
open FullSysCatSegmentBridge
  (fullSysCoreWires coreCosetB1Block coreElecCosetB1Block)
open NuclearTwistAndXor654Concrete hiding fullSysCoreWires
open NuclearTwistRealizes
open NuclearTwistMulKickAndBridge288
private instance (priority := 1000000) instNeZeroTwoPowLocal (k : ℕ) : NeZero (2 ^ k) :=
  ⟨Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos k)⟩
theorem hm6_of_hm22 {mPayload : ℕ} (hm22 : 22 ≤ mPayload) : 6 ≤ mPayload :=
  le_trans (by decide : 6 ≤ 22) hm22
noncomputable def uPre654 : Unitary (2 ^ (3924 + 3)) := preDiag654 * bit5Flip654
theorem flipBit5Fin64_lt {u : Fin 64} :
    (if u.val < 32 then u.val + 32 else u.val - 32) < 64 :=
  (by decide : ∀ v : Fin 64, (if v.val < 32 then v.val + 32 else v.val - 32) < 64) u
def flipBit5Fin64 (u : Fin 64) : Fin 64 :=
  ⟨if u.val < 32 then u.val + 32 else u.val - 32, flipBit5Fin64_lt⟩
theorem karatsubaInExp128_bit5Flip_eq (b : Fin 2) (u : Fin 64) : karatsubaInExp128 b
    (flipBit5Fin64 u) = -32 * ((bit6 u 0 : ℤ) + (bit6 u 1 : ℤ) + (bit6 u 2 : ℤ) + (bit6 u 3 :
    ℤ) + (bit6 u 4 : ℤ) + (bit6 u 5 : ℤ)) + (1 - (b.val : ℤ)) * (u.val : ℤ) + 32 * (b.val : ℤ)
    := by
  revert b u
  decide
theorem elec_i_lt {i : Fin 3924} : i.val < 3924 + 3 := by omega
theorem elec3e_add_w_wire_lt {e : Fin 218} {w : Fin 3} {r : Fin 6} :
    6 * (3 * e.val + w.val) + r.val < 3924 + 3 := by omega
theorem coset_wire_lt {w : Fin 3} : 3924 + w.val < 3924 + 3 := by omega
def flipBit5Assign654 (γ : BitAssignment (3924 + 3)) : BitAssignment (3924 + 3) :=
  fun k ↦ if k.val < 3924 ∧ k.val % 6 = 5 then γ k + 1 else γ k
private theorem lemHex417 (u : Fin 64) :
    (fun r : Fin 6 ↦ if r.val = 5 then basisBits 6 u r + 1 else basisBits 6 u r) =
      basisBits 6 (flipBit5Fin64 u) := by
  funext r
  rw [basisBits_eq_div_mod, basisBits_eq_div_mod]
  revert u r
  decide
private theorem extract_flipBit5Assign654 (γ : BitAssignment (3924 + 3)) (a : Fin 654) :
    ((basisBitsEquiv 6).symm fun r : Fin 6 ↦ (flipBit5Assign654 γ) ⟨6 * a.val + r.val,
      by omega⟩) = flipBit5Fin64 ((basisBitsEquiv 6).symm fun r : Fin 6 ↦
      γ ⟨6 * a.val + r.val, by omega⟩) := by
  refine (basisBitsEquiv 6).symm_apply_eq.mpr ((funext fun r ↦ ?_).trans (lemHex417 _))
  dsimp only [flipBit5Assign654]
  simp only [show (6 * a.val + r.val < 3924 ∧ (6 * a.val + r.val) % 6 = 5) ↔ r.val = 5
    by omega]
  rw [← PosSlots24SemanticOracleConcrete80.basisBits_symm_apply_fun
    (fun r' : Fin 6 ↦ γ ⟨6 * a.val + r'.val, by omega⟩) r]
private theorem lemHex418 (f : Fin 654 → ℤ) : (∑ a : Fin 654, f a) =
    ∑ w : Fin 3, ∑ e : Fin 218, f ⟨3 * e.val + w.val, by omega⟩ := by
  let eEquiv : Fin 218 × Fin 3 ≃ Fin 654 :=
    { toFun := fun p ↦ ⟨3 * p.1.val + p.2.val, by omega⟩
      invFun := fun a ↦ (⟨a.val / 3, by omega⟩, ⟨a.val % 3, by omega⟩)
      left_inv := fun ⟨e, w⟩ ↦ Prod.ext
        (Fin.ext (show (3 * e.val + w.val) / 3 = e.val by omega))
        (Fin.ext (show (3 * e.val + w.val) % 3 = w.val by omega))
      right_inv := fun a ↦ Fin.ext (show 3 * (a.val / 3) + a.val % 3 = a.val by omega) }
  rw [← Equiv.sum_comp eEquiv f, Fintype.sum_prod_type_right]
  rfl
private theorem lemHex419 (g : Fin 3924 → ℤ) :
    (∑ i : Fin 3924, g i) =
      ∑ a : Fin 654, (g ⟨6 * a.val + 0, by omega⟩ + g ⟨6 * a.val + 1, by omega⟩ +
        g ⟨6 * a.val + 2, by omega⟩ + g ⟨6 * a.val + 3, by omega⟩ +
        g ⟨6 * a.val + 4, by omega⟩ + g ⟨6 * a.val + 5, by omega⟩) := by
  let eEquiv : Fin 654 × Fin 6 ≃ Fin 3924 :=
    { toFun := fun p ↦ ⟨6 * p.1.val + p.2.val, by omega⟩
      invFun := fun i ↦ (⟨i.val / 6, by omega⟩, ⟨i.val % 6, by omega⟩)
      left_inv := fun ⟨a, r⟩ ↦ Prod.ext
        (Fin.ext (show (6 * a.val + r.val) / 6 = a.val by omega))
        (Fin.ext (show (6 * a.val + r.val) % 6 = r.val by omega))
      right_inv := fun i ↦ Fin.ext (show 6 * (i.val / 6) + i.val % 6 = i.val by omega) }
  rw [← Equiv.sum_comp eEquiv g, Fintype.sum_prod_type]
  exact Finset.sum_congr rfl fun _ _ ↦ Fin.sum_univ_six _
theorem preDiag654_flipBit5_sum_eq (γ : BitAssignment (3924 + 3)) : (∑ a : Fin 654,
    karatsubaInExp128 ⟨((flipBit5Assign654 γ) ⟨3924 + a.val % 3, by omega⟩).val,
    ZMod.val_lt _⟩ ((basisBitsEquiv 6).symm fun r : Fin 6 ↦ (flipBit5Assign654 γ) ⟨6 * a.val +
    r.val, by omega⟩)) = -32 * (∑ i : Fin 3924, ((γ ⟨i.val, elec_i_lt⟩).val : ℤ)) + (∑ w :
    Fin 3, (1 - ((γ ⟨3924 + w.val, coset_wire_lt⟩).val : ℤ)) * (∑ e : Fin 218,
    (((basisBitsEquiv 6).symm fun r : Fin 6 ↦ γ ⟨6 * (3 * e.val + w.val) + r.val,
    elec3e_add_w_wire_lt⟩).val : ℤ))) + 6976 *
    (∑ w : Fin 3, ((γ ⟨3924 + w.val, coset_wire_lt⟩).val : ℤ)) := by
  have hcoset (a : Fin 654) : (flipBit5Assign654 γ) ⟨3924 + a.val % 3, by omega⟩ =
      γ ⟨3924 + a.val % 3, by omega⟩ :=
    ite_eq_right (by omega : ¬(3924 + a.val % 3 < 3924 ∧ (3924 + a.val % 3) % 6 = 5))
  have hstep (a : Fin 654) := karatsubaInExp128_bit5Flip_eq
    ⟨(γ ⟨3924 + a.val % 3, by omega⟩).val, ZMod.val_lt _⟩
    ((basisBitsEquiv 6).symm fun r : Fin 6 ↦ γ ⟨6 * a.val + r.val, by omega⟩)
  simp only [bit6_basisBitsEquiv_symm] at hstep
  simp_rw [hcoset, extract_flipBit5Assign654 γ, hstep, Finset.sum_add_distrib,
    ← Finset.mul_sum]
  have hs1 : (∑ a : Fin 654,
      (((γ ⟨6 * a.val + (0 : Fin 6).val, by omega⟩).val : ℤ) +
       ((γ ⟨6 * a.val + (1 : Fin 6).val, by omega⟩).val : ℤ) +
       ((γ ⟨6 * a.val + (2 : Fin 6).val, by omega⟩).val : ℤ) +
       ((γ ⟨6 * a.val + (3 : Fin 6).val, by omega⟩).val : ℤ) +
       ((γ ⟨6 * a.val + (4 : Fin 6).val, by omega⟩).val : ℤ) +
       ((γ ⟨6 * a.val + (5 : Fin 6).val, by omega⟩).val : ℤ))) =
      ∑ i : Fin 3924, ((γ ⟨i.val, elec_i_lt⟩).val : ℤ) :=
    (lemHex419 fun i ↦ ((γ ⟨i.val, elec_i_lt⟩).val : ℤ)).symm
  rw [hs1]
  have hw_eq (w : Fin 3) (e : Fin 218) :
      (⟨3924 + (3 * e.val + w.val) % 3, by omega⟩ : Wire (3924 + 3)) =
        ⟨3924 + w.val, coset_wire_lt⟩ :=
    Fin.ext (show 3924 + (3 * e.val + w.val) % 3 = 3924 + w.val by omega)
  have hs2 : (∑ a : Fin 654, (1 - ((γ ⟨3924 + a.val % 3, by omega⟩).val : ℤ)) *
      (((basisBitsEquiv 6).symm fun r : Fin 6 ↦ γ ⟨6 * a.val + r.val, by omega⟩).val : ℤ)) =
      ∑ w : Fin 3, (1 - ((γ ⟨3924 + w.val, coset_wire_lt⟩).val : ℤ)) * (∑ e : Fin 218,
      (((basisBitsEquiv 6).symm fun r : Fin 6 ↦ γ ⟨6 * (3 * e.val + w.val) + r.val,
      elec3e_add_w_wire_lt⟩).val : ℤ)) := by
    rw [lemHex418]
    refine Finset.sum_congr rfl fun w _ ↦ ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun e _ ↦ by rw [hw_eq w e]
  have hs3 : 32 * (∑ a : Fin 654, ((γ ⟨3924 + a.val % 3, by omega⟩).val : ℤ)) =
      6976 * (∑ w : Fin 3, ((γ ⟨3924 + w.val, coset_wire_lt⟩).val : ℤ)) := by
    rw [lemHex418]
    simp_rw [hw_eq, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      ← Finset.mul_sum]
    ring
  rw [hs2, hs3]
def elecWireList654 : List (Wire (3924 + 3)) :=
  List.ofFn fun i : Fin 3924 ↦ ⟨i.val, elec_i_lt⟩
def cosetWireList654 : List (Wire (3924 + 3)) :=
  List.ofFn fun w : Fin 3 ↦ ⟨3924 + w.val, coset_wire_lt⟩
def preDiagCliffordLocalCircuit : Circuit (3924 + 3) :=
  sDagList elecWireList654 ;;ᶜ zList cosetWireList654
def preDiagCliffordInvLocalCircuit : Circuit (3924 + 3) :=
  sList elecWireList654 ;;ᶜ zList cosetWireList654
def preDiagCliffordExp128 (γ : BitAssignment (3924 + 3)) : ℤ :=
  -32 * (∑ i : Fin 3924, ((γ ⟨i.val, elec_i_lt⟩).val : ℤ)) +
    64 * (∑ w : Fin 3, ((γ ⟨3924 + w.val, coset_wire_lt⟩).val : ℤ))
def uTildeFullExp128 (γ : BitAssignment (3924 + 3)) : ℤ := ∑ w : Fin 3,
    (1 - ((γ ⟨3924 + w.val, coset_wire_lt⟩).val : ℤ)) * (∑ e : Fin 218, (((basisBitsEquiv
    6).symm fun r : Fin 6 ↦ γ ⟨6 * (3 * e.val + w.val) + r.val, elec3e_add_w_wire_lt⟩).val :
    ℤ))
noncomputable def uPreDiagClifford654 : Unitary (2 ^ (3924 + 3)) :=
  DyadicQft64.dyadicDiagUnitary (3924 + 3) 7 preDiagCliffordExp128
noncomputable def uTildeFull654 : Unitary (2 ^ (3924 + 3)) :=
  DyadicQft64.dyadicDiagUnitary (3924 + 3) 7 uTildeFullExp128
@[simp] theorem count_preDiagCliffordLocal_toff :
    preDiagCliffordLocalCircuit.count .TOFF = 0 := by simp [preDiagCliffordLocalCircuit]
@[simp] theorem count_preDiagCliffordLocal_t :
    preDiagCliffordLocalCircuit.count .T = 0 := by simp [preDiagCliffordLocalCircuit]
@[simp] theorem count_preDiagCliffordInvLocal_toff :
    preDiagCliffordInvLocalCircuit.count .TOFF = 0 := by simp [preDiagCliffordInvLocalCircuit]
@[simp] theorem count_preDiagCliffordInvLocal_t :
    preDiagCliffordInvLocalCircuit.count .T = 0 := by simp [preDiagCliffordInvLocalCircuit]
private theorem lemHex41a {N M : ℕ} (f : Fin M → Wire N) (β : BitAssignment N) :
    (wireListSum (List.ofFn f) β : ℤ) = ∑ i : Fin M, ((β (f i)).val : ℤ) := by
  have haux (l : List (Wire N)) : (wireListSum l β : ℤ) = (l.map fun w ↦ ((β w).val : ℤ)).sum := by
    induction l with
    | nil => rfl
    | cons _ _ ih => simp [wireListSum_cons, ih]
  simp [haux, List.map_ofFn, List.sum_ofFn]
private theorem lemHex41b {K B : ℕ} (e : BitAssignment K → ℤ) (β : BitAssignment K) :
    (DyadicQft64.dyadicDiagUnitary K B e).1.mulVec (basisKet β) =
      DyadicQft64.dyadicTurn B (e β) • basisKet β := by
  have h := embedUnitary_dyadicDiagUnitary_mulVec_basisKet (QRegExt.idReg K) B e β
  rwa [embedUnitary_idReg_eq] at h
theorem preDiagCliffordLocalCircuit_eval :
    preDiagCliffordLocalCircuit.eval = uPreDiagClifford654 :=
  Subtype.ext <| matrix_ext_basisKet fun β ↦ by
    have hev := ((phasePerm_sDagList elecWireList654).seq
      (phasePerm_zList cosetWireList654)).evolve β
    dsimp only [Function.comp_apply, id_eq] at hev
    rw [preDiagCliffordLocalCircuit, uPreDiagClifford654, hev, lemHex41b,
      DyadicQft64.dyadicTurn_add]
    exact congrArg (DyadicQft64.dyadicTurn 7 · • basisKet β)
      (by simp only [elecWireList654, cosetWireList654, preDiagCliffordExp128, lemHex41a])
theorem preDiagCliffordInvLocalCircuit_eval :
    preDiagCliffordInvLocalCircuit.eval = uPreDiagClifford654⁻¹ := by
  rw [uPreDiagClifford654, DyadicQft64.dyadicDiagUnitary_inv]
  exact Subtype.ext <| matrix_ext_basisKet fun β ↦ by
    have hev := ((phasePerm_sList elecWireList654).seq (phasePerm_zList cosetWireList654)).evolve β
    dsimp only [Function.comp_apply, id_eq] at hev
    rw [preDiagCliffordInvLocalCircuit, hev, lemHex41b, DyadicQft64.dyadicTurn_add]
    refine congrArg (· • basisKet β) (DyadicQft64.dyadicTurn_eq_of_emod_eq 7 ?_)
    simp only [elecWireList654, cosetWireList654, preDiagCliffordExp128, lemHex41a]
    omega
private def lemHex41c {N : ℕ} : ∀ {M : ℕ}, (Fin M → Wire N) → Circuit N
  | 0, _ => .identity | _ + 1, f => lemHex41c (fun i ↦ f i.succ) ;;ᶜ Circuit.X (f 0)
private theorem lemHex41d {N : ℕ} : ∀ {M : ℕ} (rs : Fin M → QRegister 6 N),
    axisChainCircuit (Circuit.X (5 : Fin 6)) rs = lemHex41c (fun a ↦ rs a 5)
  | 0, _ => rfl | _ + 1, rs => congrArg (· ;;ᶜ Circuit.X (rs 0 5)) (lemHex41d fun i ↦ rs i.succ)
private theorem lemHex41e {N K : ℕ} (r : QRegister N K) : ∀ {M : ℕ} (f : Fin M → Wire N),
    (lemHex41c f).onRegister r = lemHex41c (fun a ↦ r (f a))
  | 0, _ => rfl | _ + 1, f => congrArg (· ;;ᶜ Circuit.X (r (f 0))) (lemHex41e r fun i ↦ f i.succ)
private theorem lemHex41f {N : ℕ} :
    ∀ {M : ℕ} (f : Fin M → Wire N), Function.Injective f →
      PhasePerm ⊤ (lemHex41c f) (fun _ ↦ 1)
        (fun β w ↦ if ∃ a : Fin M, f a = w then β w + 1 else β w)
  | 0, _, _ =>
      { evolve := fun β ↦ by simp [lemHex41c]
        outside := fun _ _ hm ↦ absurd (Finset.mem_univ _) hm }
  | M + 1, f, hf =>
      let ih := lemHex41f (fun i : Fin M ↦ f i.succ) (fun _ _ h ↦ Fin.succ_injective _ (hf h))
      { evolve := fun β ↦ by
          rw [lemHex41c, Circuit.eval_seq, Submonoid.coe_mul, ← Matrix.mulVec_mulVec,
            ih.evolve β, one_smul, (phasePerm_X (f 0)).evolve _, one_smul, one_smul]
          refine congrArg basisKet (funext fun w ↦ ?_)
          by_cases hw0 : w = f 0
          · subst hw0
            simp [show ¬∃ a : Fin M, f a.succ = f 0 from
                fun ⟨a, ha⟩ ↦ Fin.succ_ne_zero a (hf ha),
              show ∃ a : Fin (M + 1), f a = f 0 from ⟨0, rfl⟩]
          · simp [Function.update_of_ne hw0,
              show (∃ a : Fin M, f a.succ = w) ↔ (∃ a : Fin (M + 1), f a = w) from
                ⟨fun ⟨a, ha⟩ ↦ ⟨a.succ, ha⟩, fun ⟨a, ha⟩ ↦
                  (Fin.eq_zero_or_eq_succ a).elim (fun h0 ↦ absurd (h0 ▸ ha.symm) hw0)
                    fun ⟨b, hb⟩ ↦ ⟨b, hb ▸ ha⟩⟩]
        outside := fun _ _ hm ↦ absurd (Finset.mem_univ _) hm }
private theorem lemHex421 : (axisChainCircuit (Circuit.X 5) rAxis654).eval = bit5Flip654 :=
  ofAxis654Circuit_eval_fwd (Circuit.X (5 : Fin 6)) bit5Flip6 rfl
private theorem lemHex422 (β : BitAssignment (3924 + 3)) :
    bit5Flip654.1.mulVec (basisKet β) = basisKet (flipBit5Assign654 β) := by
  let fWire : Fin 654 → Wire (3924 + 3) := fun a ↦ rAxis654 a 5
  have hval (a : Fin 654) : (fWire a).val = 6 * a.val + 5 := rfl
  have hinj : Function.Injective fWire := fun a₁ a₂ h ↦ Fin.ext (by
    have hv := congrArg Fin.val h
    rw [hval, hval] at hv
    omega)
  have hev := (lemHex41f fWire hinj).evolve β
  rw [one_smul] at hev
  rw [← lemHex421, lemHex41d, hev]
  refine congrArg basisKet (funext fun k ↦ ?_)
  have hiff : (∃ a : Fin 654, fWire a = k) ↔ (k.val < 3924 ∧ k.val % 6 = 5) :=
    ⟨fun ⟨a, hk⟩ ↦ by
       rw [← hk, hval]
       omega,
     fun ⟨hlt, hm⟩ ↦ ⟨⟨k.val / 6, by omega⟩, Fin.ext (by
       rw [hval]
       exact show 6 * (k.val / 6) + 5 = k.val by omega)⟩⟩
  simp only [flipBit5Assign654, hiff]
theorem uPre654_eq_flip_clifford_uTildeFull :
    uPre654 = bit5Flip654 * (uPreDiagClifford654 * uTildeFull654) :=
  Subtype.ext (matrix_ext_basisKet fun β ↦ by
    change (preDiag654.1 * bit5Flip654.1).mulVec (basisKet β) =
      (bit5Flip654.1 * (uPreDiagClifford654.1 * uTildeFull654.1)).mulVec (basisKet β)
    rw [← Matrix.mulVec_mulVec, lemHex422 β, preDiag654, lemHex41b,
      ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, uTildeFull654, lemHex41b,
      Matrix.mulVec_smul, uPreDiagClifford654, lemHex41b, smul_smul, Matrix.mulVec_smul,
        lemHex422 β]
    apply congrArg (· • basisKet (flipBit5Assign654 β))
    change ParametricMulKickAndSlopePG.turnPow2 7 _ =
      ParametricMulKickAndSlopePG.turnPow2 7 (uTildeFullExp128 β) *
        ParametricMulKickAndSlopePG.turnPow2 7
          (preDiagCliffordExp128 β)
    rw [← ParametricMulKickAndSlopePG.turnPow2_add]
    apply ParametricMulKickAndSlopePG.turnPow2_eq_of_emod_eq 7
    rw [preDiag654_flipBit5_sum_eq β]
    dsimp only [uTildeFullExp128, preDiagCliffordExp128]
    omega)
noncomputable def uPreDiagCliffordCore {mPayload : ℕ} (hm6 : 6 ≤ mPayload) :
    Unitary (2 ^ (fullSysCoreWires mPayload)) :=
  (coreElecCosetB1Block hm6).embedUnitary uPreDiagClifford654
noncomputable def uTildeFullCore {mPayload : ℕ} (hm6 : 6 ≤ mPayload) :
    Unitary (2 ^ (fullSysCoreWires mPayload)) :=
  (coreElecCosetB1Block hm6).embedUnitary uTildeFull654
private theorem lemHex423 {mPayload : ℕ} (hm6 : 6 ≤ mPayload) (i : Fin 3924) :
    (coreElecCosetB1Block hm6 ⟨i.val, elec_i_lt⟩).val = i.val := by
  rw [show (⟨i.val, elec_i_lt⟩ : Fin (3924 + 3)) = Fin.castAdd 3 i from Fin.ext rfl,
    QRegister.concat_apply_left, FullSysCatSegmentBridge.coreElecBlock,
    FusedPreDiagFromTwist288Alt.qreg_block_apply]
  exact Nat.zero_add i.val
private theorem lemHex424 {mPayload : ℕ} (hm6 : 6 ≤ mPayload) (w : Fin 3) :
    coreElecCosetB1Block hm6 ⟨3924 + w.val, coset_wire_lt⟩ = coreCosetB1Block hm6 w := by
  rw [show (⟨3924 + w.val, coset_wire_lt⟩ : Fin (3924 + 3)) = Fin.natAdd 3924 w from
      Fin.ext rfl, QRegister.concat_apply_right]
theorem embed_bit5Flip654_eq_uXor32Core {mPayload : ℕ} (hm6 : 6 ≤ mPayload) :
    (coreElecCosetB1Block hm6).embedUnitary bit5Flip654 = uXor32Core mPayload := by
  let fWire : Fin 654 → Wire (fullSysCoreWires mPayload) :=
    fun a ↦ coreElecCosetB1Block hm6 (rAxis654 a 5)
  have hfVal (a : Fin 654) : (fWire a).val = 6 * a.val + 5 := by
    let idx : Fin 3924 := ⟨6 * a.val + 5, by omega⟩
    dsimp only [fWire]
    rw [show rAxis654 a 5 = ⟨idx.val, elec_i_lt⟩ from Fin.ext (by simp [idx, rAxis654])]
    exact lemHex423 hm6 idx
  have hinj : Function.Injective fWire := fun a₁ a₂ h ↦ Fin.ext (by
    have hv := congrArg Fin.val h
    rw [hfVal, hfVal] at hv
    omega)
  have hres := circuit_eval_eq_embed_perm_of_phasePerm
    (QRegExt.idReg (fullSysCoreWires mPayload)) (lemHex41c fWire)
    (xor32CorePerm mPayload) _ (lemHex41f fWire hinj)
    (fun _ w hw ↦ False.elim (hw ((QRegister.mem_image _ w).mpr ⟨w, rfl⟩)))
    (fun β ↦ by
      ext k
      change basisBits _ ((xor32CorePerm mPayload)
        ((basisBitsEquiv _).symm (fun q ↦ β q))) k = _
      unfold xor32CorePerm
      rw [basisBits_perm_ofBijective (xor32BitFn mPayload)
        (xor32BitFn_involutive mPayload).bijective]
      dsimp only [xor32BitFn]
      simp only [show (k.val < 3924 ∧ k.val % 6 = 5) ↔ (∃ a : Fin 654, fWire a = k) from
        ⟨fun ⟨hlt, hm⟩ ↦ ⟨⟨k.val / 6, by omega⟩, Fin.ext (by
           rw [hfVal]
           exact show 6 * (k.val / 6) + 5 = k.val by omega)⟩,
         fun ⟨a, hk⟩ ↦ by
           rw [← hk, hfVal]
           omega⟩]
      rfl)
  rw [embedUnitary_idReg_eq] at hres
  rw [← lemHex421, ← Circuit.eval_onRegister, lemHex41d, lemHex41e, hres]
  rfl
theorem embed_uPre654_eq_xor32_clifford_uTildeCore {mPayload : ℕ} (hm6 : 6 ≤ mPayload) :
    (coreElecCosetB1Block hm6).embedUnitary uPre654 =
      uXor32Core mPayload * (uPreDiagCliffordCore hm6 * uTildeFullCore hm6) := by
  rw [uPre654_eq_flip_clifford_uTildeFull, QRegister.embedUnitary_mul,
    QRegister.embedUnitary_mul, embed_bit5Flip654_eq_uXor32Core hm6]
  rfl
theorem uTildeFullCore_eq_dyadicDiag48 {mPayload : ℕ} (hm6 : 6 ≤ mPayload) : uTildeFullCore
    hm6 = DyadicQft64.dyadicDiagUnitary (fullSysCoreWires mPayload) 48 (fun γ ↦ ∑ w : Fin 3,
    (1 - ((γ (coreCosetB1Block hm6 w)).val : ℤ)) * (2 ^ 41 : ℤ) * (slot2AxisSum w γ : ℤ)) :=
  Subtype.ext (matrix_ext_basisKet fun γ ↦ by
    have hscale : DyadicQft64.dyadicTurn 7
        (uTildeFullExp128 fun k ↦ γ (coreElecCosetB1Block hm6 k)) =
        DyadicQft64.dyadicTurn 48
          ((2 ^ 41 : ℤ) * uTildeFullExp128 fun k ↦ γ (coreElecCosetB1Block hm6 k)) :=
      (ParametricMulKickAndSlopePG.turnPow2_scale_pow 41 7 _).symm
    change ((coreElecCosetB1Block hm6).embedUnitary uTildeFull654).1.mulVec (basisKet γ) = _
    rw [uTildeFull654, embedUnitary_dyadicDiagUnitary_mulVec_basisKet
        (coreElecCosetB1Block hm6) 7 uTildeFullExp128 γ, lemHex41b (B := 48) _ γ, hscale]
    apply congrArg (fun z ↦ DyadicQft64.dyadicTurn 48 z • basisKet γ)
    dsimp only [uTildeFullExp128]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun w _ ↦ ?_
    rw [lemHex424 hm6 w, show (∑ e : Fin 218, (((basisBitsEquiv 6).symm fun r : Fin 6 ↦ γ
        (coreElecCosetB1Block hm6 ⟨6 * (3 * e.val + w.val) + r.val, elec3e_add_w_wire_lt⟩)).val
        : ℤ)) = (slot2AxisSum w γ : ℤ) by
      unfold slot2AxisSum
      dsimp only [SpecsAux.SpecMirror.numElectrons]
      push_cast
      refine Finset.sum_congr rfl fun e _ ↦ congrArg Nat.cast ?_
      rw [← bitsVal_eq_symm_val]
      refine congrArg bitsVal (funext fun r ↦ congrArg γ (Fin.ext ?_))
      rw [lemHex423 hm6 ⟨6 * (3 * e.val + w.val) + r.val, by omega⟩]
      dsimp [rElecSlotAxis, rElecCore, QRegExt.idReg, QRegister.slice, QRegister.slice_apply,
        QRegister.compose, QRegister.compose_apply, SpecsAux.SpecMirror.electronBits,
        FusedPreDiagFromTwist288Alt.qreg_whole_wires,
        FusedPreDiagFromTwist288Alt.emb_trans_apply,
        FusedPreDiagFromTwist288Alt.emb_refl_apply,
        FusedPreDiagFromTwist288Alt.emb_mk_apply,
        FusedPreDiagFromTwist288Alt.qreg_slice_wires,
        FusedPreDiagFromTwist288Alt.qreg_compose_wires,
        FusedPreDiagFromTwist288Alt.qreg_block_apply,
        FusedPreDiagFromTwist288Alt.qreg_block_wires_apply]
      omega]
    ring)
theorem w48_ge_7 : 7 ≤ 48 := by decide
attribute [local irreducible] dXor32All654
theorem embed_uPre654_comm_high_wire {mPayload : ℕ} (hm : 22 ≤ mPayload)
    (q : Wire (fullSysCoreWires mPayload)) (hq : 3924 ≤ q.val) (b : Fin 2) :
    ((coreElecCosetB1Block (hm6_of_hm22 hm)).embedUnitary uPre654).1 * slotBitProj q b =
    slotBitProj q b * ((coreElecCosetB1Block (hm6_of_hm22 hm)).embedUnitary uPre654).1 := by
  let c₀ : Configuration :=
    { nuclei := fun _ _ ↦ 0
      projectileMomentum := fun _ ↦ 0
      momentum_le := by
        rw [SpecsAux.SpecMirror.waveNumberSq, show SpecsAux.SpecMirror.waveVector (fun _ ↦ 0) = 0 by
          ext
          simp [SpecsAux.SpecMirror.waveVector], dotProduct_zero]
        positivity }
  have hDiagComm (d : Fin (2 ^ (fullSysCoreWires mPayload)) → ℂ) :
      Matrix.diagonal d * slotBitProj q b = slotBitProj q b * Matrix.diagonal d := by
    unfold slotBitProj
    exact PosSlots24SemanticOracleConcrete80.diagonal_comm_diagonal d _
  have hMulComm {A B : Operator (2 ^ (fullSysCoreWires mPayload))}
      (hA : A * slotBitProj q b = slotBitProj q b * A)
      (hB : B * slotBitProj q b = slotBitProj q b * B) :
      (A * B) * slotBitProj q b = slotBitProj q b * (A * B) := by
    rw [Matrix.mul_assoc, hB, ← Matrix.mul_assoc, hA, Matrix.mul_assoc]
  have hPreDiag : ((coreElecCosetB1Block (hm6_of_hm22 hm)).embedUnitary preDiag654).1 *
      slotBitProj q b = slotBitProj q b *
        ((coreElecCosetB1Block (hm6_of_hm22 hm)).embedUnitary preDiag654).1 := by
    unfold preDiag654 DyadicQft64.dyadicDiagUnitary
    rw [QRegister.embedUnitary_val, QRegister.embedMatrix_diagonal]
    exact hDiagComm _
  have hInvDiag {B : ℕ} (e : BitAssignment (fullSysCoreWires mPayload) → ℤ) :
      (DyadicQft64.dyadicDiagUnitary _ B e)⁻¹.1 * slotBitProj q b =
        slotBitProj q b * (DyadicQft64.dyadicDiagUnitary _ B e)⁻¹.1 := by
    rw [DyadicQft64.dyadicDiagUnitary_inv]
    exact hDiagComm _
  have hXorEq : uXor32Core mPayload = (uSlot4KickCore hm)⁻¹ *
      ((uSlot2KickCore c₀ hm)⁻¹ * uTwistRest hm c₀) := by
    unfold uTwistRest
    group
  rw [uPre654, QRegister.embedUnitary_mul, embed_bit5Flip654_eq_uXor32Core (hm6_of_hm22 hm),
    Submonoid.coe_mul]
  refine hMulComm hPreDiag ?_
  rw [hXorEq, Submonoid.coe_mul, Submonoid.coe_mul]
  exact hMulComm (hInvDiag _) (hMulComm (hInvDiag _) (uTwistRest_comm_high_wire hm c₀ q hq b))
end ConfigFusedPreDiagFromTwist288
end FusedPreDiagFromTwist288
end
end ModFusedPreDiagFromTwist288

section ModWeighted3A2TierClosure
@[expose] public section
namespace TierClosureAlt
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
end TierClosureAlt
namespace TierClosure
section ConfigTierClosure
open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt Real
open scoped Matrix BigOperators Matrix.Norms.L2Operator
set_option exponentiation.threshold 256
local instance (priority := 1000000) instNeZeroTwoPow (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩
-- Root solution namespace already active.
open MeasureBranchHadamardSem (ket)
open SpecsAux.SpecMirror
open PosMomSelectSandwich (slotBitProj)
open FullSysMomSlots0135Concrete (MomSingleSlotOracle momCoreWires)
open FullSysCatSegmentBridge (fullSysCoreWires iSlot1 iSlot2)
open OraAndPrepBundle
  (castNatUnitary momCoreWires_eq_fullSysCoreWires)
theorem matrix_eq_of_mulVec_ket {N : ℕ} (A B : Operator (2 ^ N))
    (h : ∀ β : BitAssignment N, A.mulVec (ket β) = B.mulVec (ket β)) : A = B := by
  ext i j
  simpa only [ket, basisState, (basisBitsEquiv N).symm_apply_apply, Matrix.mulVec_single_one,
    Matrix.col_apply] using congrFun (h (basisBitsEquiv N j)) i
theorem castNatUnitary_mulVec_ket_at {a b : ℕ} (h : a = b) (U : Unitary (2 ^ b))
    (fB : BitAssignment b → BitAssignment b)
    (hKetB : ∀ γ : BitAssignment b, U.1.mulVec (ket γ) = ket (fB γ)) (β out : BitAssignment a)
    (hf : ∀ w : Wire a, out w = fB (fun q ↦ β ⟨q.val, h.symm ▸ q.isLt⟩) ⟨w.val, h ▸ w.isLt⟩) :
    (castNatUnitary h.symm U).1.mulVec (ket β) = ket out := by
  subst h
  exact (hKetB β).trans (congrArg ket (funext fun w ↦ (hf w).symm))
theorem castNatUnitary_comm_slotBitProj {a b : ℕ} (h : a = b) (U : Unitary (2 ^ b)) (hComm : ∀
    (q : Wire b), 3924 ≤ q.val → ∀ bit : Fin 2, U.1 * slotBitProj q bit = slotBitProj q bit *
    U.1) (q : Wire a) (hq : 3924 ≤ q.val) (bit : Fin 2) : (castNatUnitary h.symm U).1 *
    slotBitProj q bit = slotBitProj q bit * (castNatUnitary h.symm U).1 := by
  cases h
  exact hComm q hq bit
theorem castNatUnitary_sa {a b : ℕ} (h : a = b) (U : Unitary (2 ^ a)) (hSA : U.1ᴴ = U.1) :
    (castNatUnitary h U).1ᴴ = (castNatUnitary h U).1 := by
  cases h
  exact hSA
theorem castNatUnitary_mul_slotBitProj_id {a b : ℕ} (h : a = b) (U : Unitary (2 ^ a))
    (qA : Wire a) (qB : Wire b) (hq : qA.val = qB.val) (bit : Fin 2)
    (hId : U.1 * slotBitProj qA bit = slotBitProj qA bit) : (castNatUnitary h U).1 *
    slotBitProj qB bit = slotBitProj qB bit := by
  cases h
  exact Fin.ext hq ▸ hId
theorem castNatUnitary_conj_val_eq {a b : ℕ} (h : a = b)
    (B : Unitary (2 ^ b)) (M : Unitary (2 ^ a)) :
    (castNatUnitary h.symm (HoistedSwapSelectBridge.unitaryConj B (castNatUnitary h M))).1 =
      (HoistedSwapSelectBridge.unitaryConj (castNatUnitary h.symm B) M).1 := by
  cases h
  rfl
theorem slotBitProj_mulVec_ket {N : ℕ} (q : Wire N) (b : Fin 2) (γ : BitAssignment N) :
    (slotBitProj q b).mulVec (ket γ) =
      (if γ q = (if b.val = 1 then (1 : ZMod 2) else 0) then (1 : ℂ) else 0) • ket γ := by
  funext x
  simp only [slotBitProj, Matrix.diagonal_mulVec_single, ket, basisState, Pi.smul_apply,
    Pi.single_apply, smul_eq_mul]
  by_cases hx : x = (basisBitsEquiv N).symm γ
  · subst hx
    simp only [↓reduceIte, mul_one, NuclearTwistRealizes.basisBits_symm_apply]
    fin_cases b
    all_goals
      rcases (by decide : ∀ z : ZMod 2, z = 0 ∨ z = 1) (γ q) with hγ | hγ
      all_goals simp [hγ]
  · simp [hx]
private theorem coinBarrelBitFn_posBranch {mPayload : ℕ} (hmPay : 80 ≤ mPayload)
    (hm22 : 22 ≤ mPayload) (γ : BitAssignment (fullSysCoreWires mPayload))
    (hc2 : γ (iSlot2 mPayload) = 0) : CoinDispatchedBarrel288.coinBarrelBitFn hmPay γ =
    NuclearTwistRealizes.barrelBitFn true hm22 γ := by
  have _ : 4034 ≤ fullSysCoreWires mPayload := Nat.add_le_add_left hmPay 3954
  have hActEq : NuclearTwistRealizes.barrelActive true γ =
      decide (γ (iSlot2 mPayload) = 0 ∧ γ (iSlot1 mPayload) = 0) := by
    unfold NuclearTwistRealizes.barrelActive
    rw [show NuclearTwistAndXor654Concrete.wSlot2 _ = iSlot2 mPayload from
        Fin.ext (by simp [NuclearTwistAndXor654Concrete.wSlot2,
          QRegExt.idReg]),
      show NuclearTwistAndXor654Concrete.wSlot1 _ = iSlot1 mPayload from
        Fin.ext (by simp [NuclearTwistAndXor654Concrete.wSlot1,
          QRegExt.idReg])]
    rfl
  let u8 := CoinDispatchedBarrel288.Internal.bitsVal
    (fun j : Fin 8 ↦ γ ⟨3968 + j.val, by omega⟩)
  have hreg : _root_.QuantumComputation.Specs.StoppingPowerSolution.regVal
    (NuclearTwistAndXor654Concrete.rAnchorIdx hm22
      (QRegExt.idReg (fullSysCoreWires mPayload))) γ = u8 := rfl
  unfold CoinDispatchedBarrel288.coinBarrelBitFn CoinDispatchedBarrel288.coinBarrelIdx
    NuclearTwistRealizes.barrelBitFn
  simp only [hreg, hActEq]
  by_cases hc1 : γ (iSlot1 mPayload) = 0
  · simp only [hc2, hc1, and_self, decide_true, true_and, ↓reduceIte]
    by_cases hu : u8 < 218
    · rw [CoinDispatchedBarrel288.Internal.dite_true_eq hu,
        NuclearTwistRealizes.dite_pos_eq hu]
      funext k
      dsimp only [CoinDispatchedBarrel288.swapElec0Bits]
      by_cases hu0 : u8 = 0
      · rw [ite_eq_left hu0]
        by_cases hk0 : k.val < 18
        · rw [NuclearTwistRealizes.dite_pos_eq hk0]
          exact congrArg γ (Fin.ext (show k.val = 18 * u8 + k.val by omega))
        · rw [NuclearTwistRealizes.dite_neg_eq hk0,
            NuclearTwistRealizes.dite_neg_eq
              (by omega : ¬ (18 * u8 ≤ k.val ∧ k.val < 18 * u8 + 18))]
      · rw [ite_eq_right hu0]
    · rw [CoinDispatchedBarrel288.Internal.dite_false_eq hu,
        NuclearTwistRealizes.dite_neg_eq hu]
      rfl
  · simp [hc2, hc1, show ¬ ((0 : ZMod 2) = 1) by decide, CoinDispatchedBarrel288.swapElec0Bits]
theorem uBarrel_mul_posSlot2Proj {mPayload : ℕ}
    (hmPay : 80 ≤ mPayload) (hm22 : 22 ≤ mPayload) :
    (CoinDispatchedBarrel288.uBarrel hmPay).1 * slotBitProj (iSlot2 mPayload) 0 =
      (NuclearTwistRealizes.uBarrelCore true hm22).1 * slotBitProj (iSlot2 mPayload) 0 := by
  refine matrix_eq_of_mulVec_ket _ _ fun γ ↦ ?_
  have hrhs_ket : (NuclearTwistRealizes.uBarrelCore true hm22).1.mulVec (ket γ) =
      ket (NuclearTwistRealizes.barrelBitFn true hm22 γ) := by
    have hid := NuclearTwistRealizes.embedUnitary_perm_mulVec_basisKet
      (QRegExt.idReg (fullSysCoreWires mPayload))
      (NuclearTwistRealizes.barrelCorePerm true hm22) γ
      (NuclearTwistRealizes.barrelBitFn true hm22 γ)
      (fun q ↦ (NuclearTwistRealizes.basisBits_perm_ofBijective
        (NuclearTwistRealizes.barrelBitFn true hm22)
        (NuclearTwistRealizes.barrelBitFn_involutive true hm22).bijective γ q).symm)
      (fun z hz ↦ False.elim (hz ((QRegister.mem_image _ z).mpr ⟨z, rfl⟩)))
    rwa [NuclearTwistRealizes.embedUnitary_idReg_eq] at hid
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, slotBitProj_mulVec_ket,
    Matrix.mulVec_smul, Matrix.mulVec_smul]
  dsimp only [Fin.val_zero]
  by_cases hc2 : γ (iSlot2 mPayload) = 0
  · simp [hc2, CoinDispatchedBarrel288.uBarrel_mulVec_ket,
      coinBarrelBitFn_posBranch hmPay hm22 γ hc2, hrhs_ket]
  · simp [hc2]
theorem swapElec0Bits_mom_eq_barrel {mPayload : ℕ} (k : Fin 218)
    (β : BitAssignment (momCoreWires mPayload)) (w : Wire (momCoreWires mPayload)) :
    MomSlot0LocalAndMomCombine288.swapElec0Bits k β w = CoinDispatchedBarrel288.swapElec0Bits
    k (fun q ↦ β ⟨q.val, Nat.lt_of_lt_of_eq q.isLt (momCoreWires_eq_fullSysCoreWires
    mPayload).symm⟩) ⟨w.val, Nat.lt_of_lt_of_eq w.isLt (momCoreWires_eq_fullSysCoreWires
    mPayload)⟩ := by
  unfold MomSlot0LocalAndMomCombine288.swapElec0Bits CoinDispatchedBarrel288.swapElec0Bits
  by_cases hk0 : k.val = 0
  · simp [hk0]
  · rw [ite_eq_right hk0, ite_eq_right hk0]
    beta_reduce
    by_cases hw0 : w.val < 18
    · rw [dite_eq_left hw0, dite_eq_left hw0]
    · rw [dite_eq_right hw0, dite_eq_right hw0]
      simp [show (18 * k.val ≤ w.val ∧ w.val < 18 * (k.val + 1)) ↔
        (18 * k.val ≤ w.val ∧ w.val < 18 * k.val + 18) by omega]
noncomputable def zeroMomLocalSlotData {mPayload mPGTwist : ℕ} {k : Fin 6}
    (uBarrel : SpecsAux.SpecMirror.Configuration → Unitary (2 ^ (momCoreWires mPayload)))
    (sZero : MomSingleSlotOracle mPayload mPGTwist k)
    (hZero : ∀ cfg, sZero.uSlotEff cfg = 1) :
    MomSlot0LocalAndMomCombine288.MomLocalSlotData mPayload mPGTwist k uBarrel where
  mWork := sZero.mWork
  oracle := sZero
  uLocalCat := sZero.uSlotCat
  uLocalEff := sZero.uSlotEff
  hIntertwines := sZero.hIntertwines
  hLocalSA := sZero.hSA
  hLocalOffCoin := sZero.hOffCoin
  hConjOnCoin := fun cfg ↦ by
    have h1 : HoistedSwapSelectBridge.unitaryConj (uBarrel cfg) 1 = 1 := Subtype.ext (by
      rw [HoistedSwapSelectBridge.unitaryConj_val]
      change (uBarrel cfg).1ᴴ * (1 : Operator _) * (uBarrel cfg).1 = 1
      rw [Matrix.mul_one]
      exact Matrix.mem_unitaryGroup_iff'.mp (uBarrel cfg).2)
    rw [hZero cfg, h1]
end ConfigTierClosure
end TierClosure
end
end ModWeighted3A2TierClosure

section ModWeighted3AGeneralBetaAndAlphaTopEndpoint
@[expose] public section
namespace GeneralBetaAndAlphaTopEndpointAlt
theorem qreg_ext {k n : ℕ} {r s : QRegister k n} (h : ∀ i, r i = s i) : r = s :=
  QRegister.ext (Function.Embedding.ext h)
theorem qreg_block_apply {n : ℕ} (offset width : ℕ) (h : offset + width ≤ n) (i : Fin width) :
    QRegister.block offset width h i = ⟨offset + i.val, by omega⟩ := rfl
end GeneralBetaAndAlphaTopEndpointAlt
namespace GeneralBetaAndAlphaTopEndpoint
open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt Real
open scoped Matrix BigOperators Matrix.Norms.L2Operator
open SpecsAux.SpecMirror
open SpecsAux.BridgeFermionicComm
open SpecsAux.BridgeFermionicComm.SpecInner
open SpecsAux.FullScaleBESector
open SpecsAux.PhaseGradCatalystCore
open SpecsAux.BridgeDuhamel
open PhaseGradSignalRot hiding IntertwinesCat
open TFreeLaurentGQSP CatalyzedLaurentGQSP
open BidirectionalCatalyzedGQSP
open BidirectionalCatalyzedGQSPBridge
open SpecsAux.SpecMirror.SixChannelHamiltonianSplit
open PosSlots24TopWrapper
open PosMomSelectSandwich
open PosMomSelectDynamic
open SixSlotEndpointJunctionBridge
open SingleRBEGridGuardWalk
open FullSysMomSlots0135Concrete
open MomSlot0CircuitHalf
open NuclearTwistRealizes
open FullSysCatSegmentBridge
open HoistedSwapSelectBridge hiding unitaryConj unitaryConj_val
open BiGqspSegmentSpine
open CatalystPrep
open OraAndPrepBundle
open FullSysPosSlots24AndTopConcrete
section ConfigGeneralBetaAndAlphaTopEndpoint
set_option exponentiation.threshold 256
instance (priority := 1000000) instNeZeroTwoPowGeneral (k : ℕ) : NeZero (2 ^ k) :=
  ⟨Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos k)⟩
noncomputable def zeroMomSlotOracle5 (mPayload mPGTwist : ℕ) :
    MomSingleSlotOracle mPayload mPGTwist 5 where
  mWork := 0
  wSlot := fun _ ↦ 0
  eShift := fun _ ↦ 0
  epsIntr := 436 * ∑ ν ∈ openBox3D62, coulombKernel ν
  uSlotCat := fun _ ↦ 1
  uSlotEff := fun _ ↦ 1
  bUnitTwos := fun _ ↦ 1
  hWNonneg := fun _ ↦ le_rfl
  hIntertwines := fun _ U_cat _ ↦ by
    simpa only [QRegister.embedUnitary_one] using
      FullSysMomSlots0135Concrete.intertwinesMomCat_of_coreOnly U_cat
        (1 : Unitary (2 ^ FullSysMomSlots0135Concrete.momCoreWires mPayload))
  hSA := fun _ ↦ Matrix.conjTranspose_one
  hOffCoin := fun _ ↦ Matrix.one_mul _
  hTopBlock := fun _ ↦ by
    dsimp only
    rw [unitaryConj_val]
    change _ * ((coreHadamardMom mPayload).1ᴴ * (1 : Operator _) *
      (coreHadamardMom mPayload).1) * _ = _
    rw [Matrix.mul_one, ← Matrix.star_eq_conjTranspose,
      Matrix.mem_unitaryGroup_iff'.mp (coreHadamardMom mPayload).2, QRegister.embedMatrix_one]
  hUnitNorm := fun _ ↦ l2_opNorm_unitary_le_one (1 : Unitary _)
  hPermSm := fun _ g x y _ _ ↦ by
    rw [Matrix.mul_one, smToTwosSys_mul_self_val]
    by_cases hxy : x = y
    · subst hxy
      simp
    · rw [Matrix.one_apply_ne (fun h ↦ hxy ((permElectron g).injective h)),
        Matrix.one_apply_ne hxy]
  hErrIntrSm := fun cfg spinUp ↦ by
    intro E_vec
    let P_F := SpecsAux.SpecMirror.fermionicProjector spinUp
    have hPF : ‖P_F‖ ≤ 1 := BridgeDuhamel.norm_projector_le_one P_F
      (SpecsAux.BridgeFermionicComm.SpecInner.fermionicProjector_isHermitian spinUp)
        (fermionicProjector_idem spinUp)
    have hTarget : sixChannelShifted cfg E_vec 5 = elecProjOp := by
      unfold sixChannelShifted
      change sixChannelRaw cfg 5 - ((0 : ℝ) : ℂ) • _ = elecProjOp
      rw [show sixChannelRaw cfg 5 = elecProjOp from rfl,
        Complex.ofReal_zero, zero_smul, sub_zero]
    rw [hTarget, Complex.ofReal_zero, zero_smul, zero_sub, Matrix.mul_neg, Matrix.neg_mul,
      norm_neg]
    exact ((norm_mul_le (P_F * elecProjOp) P_F).trans
      ((mul_le_mul_of_nonneg_left hPF (norm_nonneg _)).trans (mul_one _).le)).trans
      (((norm_mul_le P_F elecProjOp).trans
        ((mul_le_mul_of_nonneg_right hPF (norm_nonneg _)).trans (one_mul _).le)).trans
        norm_elecProjOp_le)
theorem endpoint_heff_of_target_sum (c : SpecsAux.SpecMirror.Configuration)
    (spinUp : Finset (Fin SpecsAux.SpecMirror.numElectrons)) (E : Fin 6 → ℝ) (H_branch target : Fin
    6 → Operator (2 ^ SpecsAux.SpecMirror.systemQubits)) (ε_slot : Fin 6 → ℝ) (ε : ℝ) (hTargetSum :
    (∑ k : Fin 6, target k) = ∑ k : Fin 6, sixChannelShifted c E k) (hSlots : ∀ k : Fin 6,
    FullScaleBESector.AgreesOnFermionicSector spinUp (H_branch k) (target k) (ε_slot k))
    (hEps : (∑ k : Fin 6, ε_slot k) ≤ ε) : endpointHeff E H_branch -
    ((∑ k : Fin 6, E k : ℝ) : ℂ) • (1 : Operator (2 ^ SpecsAux.SpecMirror.systemQubits)) =
    (∑ k : Fin 6, H_branch k) ∧ FullScaleBESector.AgreesOnFermionicSector spinUp
    (endpointHeff E H_branch) (SpecsAux.SpecMirror.hamiltonian c) ε := by
  let P := SpecsAux.SpecMirror.fermionicProjector spinUp
  refine ⟨endpointHeff_sub_shift_eq_sum E H_branch, ?_, ?_⟩
  · unfold endpointHeff
    rw [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.one_mul, Matrix.mul_one, Finset.sum_mul, Finset.mul_sum]
    exact congrArg (· + _) (Finset.sum_congr rfl fun k _ ↦ (hSlots k).1)
  · have hP1 : P * (((∑ k : Fin 6, E k : ℝ) : ℂ) •
        (1 : Operator (2 ^ SpecsAux.SpecMirror.systemQubits))) * P =
        P * (((∑ k : Fin 6, E k : ℝ) : ℂ) •
        SpecsAux.SpecMirror.SixChannelHamiltonianSplit.gridProjector) *
          P := by
      rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul,
        sixChannelGridProjector_eq_specsGridProjector,
        SpecsAux.fermionicProjector_mul_gridProjector, Matrix.mul_one]
    have hdiff : P * (endpointHeff E H_branch - SpecsAux.SpecMirror.hamiltonian c) * P =
        ∑ k : Fin 6, P * (H_branch k - target k) * P := by
      unfold endpointHeff
      rw [show (∑ k : Fin 6, H_branch k + ((∑ k : Fin 6, E k : ℝ) : ℂ) • 1) -
            SpecsAux.SpecMirror.hamiltonian c =
            (∑ k : Fin 6, H_branch k) + (((∑ k : Fin 6, E k : ℝ) : ℂ) • 1 -
              SpecsAux.SpecMirror.hamiltonian c) by abel,
        Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul, hP1,
        ← Matrix.sub_mul, ← Matrix.mul_sub,
        show (((∑ k : Fin 6, E k : ℝ) : ℂ) •
        SpecsAux.SpecMirror.SixChannelHamiltonianSplit.gridProjector -
          SpecsAux.SpecMirror.hamiltonian c) =
          -(SpecsAux.SpecMirror.hamiltonian c - ((∑ k : Fin 6, E k : ℝ) : ℂ) •
        SpecsAux.SpecMirror.SixChannelHamiltonianSplit.gridProjector)
          by abel,
        ← sum_sixChannelShifted_eq_hamiltonian_sub_gridProjector c E, ← hTargetSum,
        Matrix.mul_neg, Matrix.neg_mul, ← sub_eq_add_neg, ← Matrix.sub_mul, ← Matrix.mul_sub,
        ← Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_mul]
    rw [hdiff]
    exact (norm_sum_le _ _).trans ((Finset.sum_le_sum fun k _ ↦ (hSlots k).2).trans hEps)
theorem fullSysSelectPosUnitary_eq_on_posCoin01_out {mPayload mPGTwist : ℕ}
    (hmPay6 : 6 ≤ mPayload) (qft : FullSysQft654Bundle)
    (sel : FullSysSelectOracleBundle mPayload mPGTwist)
    (uTwistOut uPosPhase₂ : Unitary (2 ^ (fullSysCoreWires mPayload)))
    (cfg : SpecsAux.SpecMirror.Configuration) (hPos2SA : uPosPhase₂.1ᴴ = uPosPhase₂.1)
    (hPos2OnP1 : uPosPhase₂.1 * slotBitProj (iSlot2 mPayload) 1 =
      slotBitProj (iSlot2 mPayload) 1)
    (hSlack2 : let P_c2 := slotBitProj (iSlot2 mPayload) 0 * slotBitProj (iSlot1 mPayload) 1 *
        slotBitProj (iSlot0 mPayload) 0
      uPosPhase₂.1 * P_c2 = P_c2)
    (hSlack3 : let P_c3 := slotBitProj (iSlot2 mPayload) 0 * slotBitProj (iSlot1 mPayload) 1 *
        slotBitProj (iSlot0 mPayload) 1
      uPosPhase₂.1 * P_c3 = -P_c3)
    (hPosOnP01 : (sel.uPosPhase cfg).1 * posCoin01Proj mPayload =
      uPosPhase₂.1 * posCoin01Proj mPayload)
    (hTwistComm1 : (sel.uTwist cfg).1 * slotBitProj (iSlot1 mPayload) 1 =
      slotBitProj (iSlot1 mPayload) 1 * (sel.uTwist cfg).1)
    (hOutComm2 : uTwistOut.1 * slotBitProj (iSlot2 mPayload) 0 =
      slotBitProj (iSlot2 mPayload) 0 * uTwistOut.1)
    (hOutComm1 : uTwistOut.1 * slotBitProj (iSlot1 mPayload) 0 =
      slotBitProj (iSlot1 mPayload) 0 * uTwistOut.1)
    (hTwistOnP01 : (sel.uTwist cfg).1 * posCoin01Proj mPayload =
      uTwistOut.1 * posCoin01Proj mPayload) :
    (fullSysSelectPosUnitary qft sel cfg).1 * posCoin01Proj mPayload =
      (unitaryConj (fullSysQftCoreUnitary hmPay6 qft * uTwistOut) uPosPhase₂).1 *
        posCoin01Proj mPayload := by
  let P₀₁ := posCoin01Proj mPayload
  let Q := fullSysQftCoreUnitary hmPay6 qft
  let V₁ := Q * sel.uTwist cfg
  let V₂ := Q * uTwistOut
  have h12 : (iSlot2 mPayload).val = 3950 ∧ (iSlot1 mPayload).val = 3949 := ⟨rfl, rfl⟩
  have hQ_P01 : Q.1 * P₀₁ = P₀₁ * Q.1 :=
    comm_mul_of_comm Q.1 _ _
      (fullSysQftCoreUnitary_comm_coinWire hmPay6 qft (iSlot2 mPayload)
        (by omega) (by omega) 0)
      (fullSysQftCoreUnitary_comm_coinWire hmPay6 qft (iSlot1 mPayload)
        (by omega) (by omega) 0)
  have hT1_P01 : (sel.uTwist cfg).1 * P₀₁ = P₀₁ * (sel.uTwist cfg).1 :=
    comm_mul_of_comm (sel.uTwist cfg).1 _ _
      (comm_slotBitProj_zero_of_comm_one _ _ (sel.hTwist_comm_P1 cfg))
      (comm_slotBitProj_zero_of_comm_one _ _ hTwistComm1)
  have hOut_P01 : uTwistOut.1 * P₀₁ = P₀₁ * uTwistOut.1 :=
    comm_mul_of_comm uTwistOut.1 _ _ hOutComm2 hOutComm1
  have hV1_comm : V₁.1 * P₀₁ = P₀₁ * V₁.1 :=
    (comm_mul_of_comm P₀₁ Q.1 _ hQ_P01.symm hT1_P01.symm).symm
  have hV2_comm : V₂.1 * P₀₁ = P₀₁ * V₂.1 :=
    (comm_mul_of_comm P₀₁ Q.1 _ hQ_P01.symm hOut_P01.symm).symm
  have hV_P01 : V₁.1 * P₀₁ = V₂.1 * P₀₁ := by
    change (Q.1 * (sel.uTwist cfg).1) * P₀₁ = (Q.1 * uTwistOut.1) * P₀₁
    rw [Matrix.mul_assoc, hTwistOnP01, ← Matrix.mul_assoc]
  have hP01_sa : P₀₁ᴴ = P₀₁ := twoProj_conjTranspose (iSlot2 mPayload) (iSlot1 mPayload) 0 0
  have hVd_P01 : V₁.1ᴴ * P₀₁ = V₂.1ᴴ * P₀₁ := by
    simpa only [Matrix.conjTranspose_mul, hP01_sa] using
      congrArg Matrix.conjTranspose (hV1_comm.symm.trans (hV_P01.trans hV2_comm))
  have hM2_comm : uPosPhase₂.1 * P₀₁ = P₀₁ * uPosPhase₂.1 :=
    posPhase_comm_posCoin01Proj uPosPhase₂ hPos2SA hPos2OnP1 hSlack2 hSlack3
  dsimp only [fullSysSelectPosUnitary, V₁, V₂, Q]
  rw [unitaryConj_val, unitaryConj_val]
  calc V₁.1ᴴ * (sel.uPosPhase cfg).1 * V₁.1 * P₀₁
    _ = V₁.1ᴴ * ((sel.uPosPhase cfg).1 * P₀₁) * V₂.1 := by
          rw [Matrix.mul_assoc _ V₁.1 P₀₁, hV_P01, hV2_comm]
          simp only [Matrix.mul_assoc]
    _ = (V₁.1ᴴ * P₀₁) * uPosPhase₂.1 * V₂.1 := by
          rw [hPosOnP01, hM2_comm]
          simp only [Matrix.mul_assoc]
    _ = V₂.1ᴴ * uPosPhase₂.1 * V₂.1 * P₀₁ := by
          rw [hVd_P01, Matrix.mul_assoc V₂.1ᴴ P₀₁ uPosPhase₂.1, ← hM2_comm]
          simp only [Matrix.mul_assoc]
          rw [← hV2_comm]
structure GeneralBetaSegmentCert (β_nat M N_seg : ℕ) where
  C : Fin (M + 1) → Fin (2 ^ 42)
  h_seg_bound : ∀ {k m_BE : ℕ} {α : ℝ}
    {A : Operator (2 ^ k)} {U_BE : Unitary (2 ^ (k + m_BE))}
    (τ : ℝ) (hα : 0 < α) (hτ : 0 ≤ τ)
    (hBE : FullScaleBESector.IsQubitizedBlockEncodingUnitary α A U_BE)
    (hβ_eq : α * τ = (β_nat : ℝ))
    (hnorm_A : ‖(-Complex.I * (τ : ℂ)) • A‖ ≤ α * τ),
    let sys : QRegister k (k + (m_BE + 1)) := QRegister.block 0 k (by omega)
    let anc : QRegister (m_BE + 1) (k + (m_BE + 1)) := QRegister.block k (m_BE + 1) le_rfl
    ‖((biCatSegmentUnitary k m_BE M C U_BE).1 -
        sys.embedMatrix (NormedSpace.exp ((-Complex.I * (τ : ℂ)) • A))) *
      anc.basisOutcomeProjector 0‖ ≤ ((N_seg : ℕ) : ℝ) / 2 ^ 48
private theorem disj_of_lt {a b N : ℕ} (r₁ : QRegister a N) (r₂ : QRegister b N) (m : ℕ)
    (h₁ : ∀ i, (r₁ i).val < m) (h₂ : ∀ j, m ≤ (r₂ j).val) : r₁.DisjointWires r₂ :=
  QRegister.disjoint_iff.mpr fun i j hij ↦
    absurd (congrArg Fin.val hij ▸ h₁ i) (Nat.not_lt.mpr (h₂ j))
private theorem basisZeroProj_mul_eq {N a b c : ℕ}
    (rA : QRegister a N) (rB : QRegister b N) (rC : QRegister c N)
    (hA : ∀ i, ∃ k, rA i = rC k) (hB : ∀ j, ∃ k, rB j = rC k)
    (hC : ∀ k, (∃ i, rC k = rA i) ∨ (∃ j, rC k = rB j)) :
    rA.basisOutcomeProjector 0 * rB.basisOutcomeProjector 0 = rC.basisOutcomeProjector 0 := by
  simp only [QRegister.basisOutcomeProjector_eq_diagonal]
  refine (PosSlots24SemanticOracleConcrete80.diag_mul_diag_eq
    (fun x ↦ rA.extractIndex x = 0) (fun x ↦ rB.extractIndex x = 0)
    (fun x ↦ rC.extractIndex x = 0) fun x ↦ ?_).symm
  simp only [BiGqspSegmentSpine.zero_extract_iff_bits_zero]
  exact ⟨fun h ↦ ⟨fun i ↦ let ⟨k, hk⟩ := hA i
      hk ▸ h k,
    fun j ↦ let ⟨k, hk⟩ := hB j
      hk ▸ h k⟩,
    fun ⟨h1, h2⟩ k ↦ (hC k).elim (fun ⟨i, hi⟩ ↦ hi ▸ h1 i) fun ⟨j, hj⟩ ↦ hj ▸ h2 j⟩
theorem physBiSegmentUnitaryGen_approx_exp_beta
    {k m β_nat M N_seg : ℕ} (hm : 0 < m) (b : Fin (2 ^ k) → Bool)
    (P_grid P_ferm : Operator (2 ^ k)) (hDiagEq : diagProj k b = P_grid)
    (hGridFerm : P_grid * P_ferm = P_ferm) (hFermHerm : P_ferm.IsHermitian)
    (hFermIdem : P_ferm * P_ferm = P_ferm) (cert : GeneralBetaSegmentCert β_nat M N_seg)
    {α τ : ℝ} (hα : 0 < α) (hτ : 0 ≤ τ) (hβ : α * τ = (β_nat : ℝ))
    {A : Operator (2 ^ k)} (hAGrid : Commute A P_grid) (U_raw : Unitary (2 ^ (k + m)))
    (hBE : FullScaleBESector.IsQubitizedBlockEncodingUnitary α A
      (ghostZeroedBE k m hm b U_raw)) :
    ApproximatesTimeEvolution (m := m + 1) A τ ((N_seg : ℝ) / 2 ^ 48) P_ferm
      (physBiSegmentUnitaryGen b M cert.C U_raw) := by
  have hNormSmul : ‖(-Complex.I * (τ : ℂ)) • A‖ ≤ α * τ := by
    rw [norm_smul, norm_mul, norm_neg, Complex.norm_I, one_mul, Complex.norm_real,
      Real.norm_of_nonneg hτ, mul_comm α τ]
    exact mul_le_mul_of_nonneg_left (norm_le_of_isQubitizedBlockEncodingUnitary hBE) hτ
  have hSegG := cert.h_seg_bound (k := k) (m_BE := m + 1) τ hα hτ hBE hβ hNormSmul
  dsimp only at hSegG
  let sysPhys : QRegister k (k + (m + 1)) := QRegister.block 0 k (by omega)
  let ancPhys : QRegister (m + 1) (k + (m + 1)) := QRegister.block k (m + 1) (by omega)
  let sysGhost : QRegister k (k + (m + 1 + 1)) := QRegister.block 0 k (by omega)
  let ancGhost : QRegister (m + 1 + 1) (k + (m + 1 + 1)) :=
    QRegister.block k (m + 1 + 1) (by omega)
  let rBEG : QRegister (k + (m + 1)) (k + (m + 1 + 1)) :=
    QRegister.block 0 (k + (m + 1)) (by omega)
  let qGhG : Wire (k + (m + 1 + 1)) := ⟨k + m, by omega⟩
  let qSigG : Wire (k + (m + 1 + 1)) := ⟨k + (m + 1), by omega⟩
  let P_gh0 : Operator (2 ^ (k + (m + 1 + 1))) :=
    (QRegister.singleton qGhG).basisOutcomeProjector 0
  let GG : Operator (2 ^ (k + (m + 1 + 1))) := rBEG.embedMatrix (ghostGuardMatrix k m b)
  let E_A : Operator (2 ^ k) := NormedSpace.exp ((-Complex.I * (τ : ℂ)) • A)
  set DiffPhys : Operator (2 ^ (k + (m + 1))) :=
    ((physBiSegmentUnitaryGen b M cert.C U_raw).1 - sysPhys.embedMatrix E_A) *
      (ancPhys.basisOutcomeProjector 0 * sysPhys.embedMatrix P_ferm)
  have hSysComp : (rPhysInGhost k m).compose sysPhys = sysGhost :=
    GeneralBetaAndAlphaTopEndpointAlt.qreg_ext fun i ↦
      Fin.ext (by simp [rPhysInGhost, sysPhys, sysGhost, show i.val < k + m by omega])
  have hAncW : ∀ j : Fin (m + 1), ((rPhysInGhost k m).compose ancPhys) j =
      ancGhost ⟨if j.val < m then j.val else m + 1, by
        split_ifs
        all_goals omega⟩ := fun j ↦ Fin.ext (by
    by_cases hj : j.val < m
    · simp [rPhysInGhost, ancPhys, ancGhost, hj, show k + j.val < k + m by omega]
    · simp [rPhysInGhost, ancPhys, ancGhost, hj, show ¬(k + j.val < k + m) by omega])
  have hAncProjProd :
      (rPhysInGhost k m).embedMatrix (ancPhys.basisOutcomeProjector 0) * P_gh0 =
      ancGhost.basisOutcomeProjector 0 := by
    unfold QRegister.basisOutcomeProjector
    rw [← QRegister.embedMatrix_compose]
    refine basisZeroProj_mul_eq ((rPhysInGhost k m).compose ancPhys) (QRegister.singleton qGhG)
      ancGhost (fun j ↦ ⟨_, hAncW j⟩) (fun j ↦ ⟨⟨m, by omega⟩, by
        fin_cases j
        rfl⟩)
      fun idx ↦ ?_
    by_cases hlt : idx.val < m
    · exact Or.inl ⟨⟨idx.val, by omega⟩, by simpa [hlt] using (hAncW ⟨idx.val, by omega⟩).symm⟩
    · by_cases heq : idx.val = m
      · exact Or.inr ⟨0, Fin.ext (show k + idx.val = k + m by omega)⟩
      · rw [show idx = ⟨m + 1, by omega⟩ from Fin.ext (show idx.val = m + 1 by omega)]
        exact Or.inl ⟨⟨m, by omega⟩, by simpa [Nat.lt_irrefl] using (hAncW ⟨m, by omega⟩).symm⟩
  have hSysDisj {b : ℕ} (r : QRegister b (k + (m + 1 + 1))) (hr : ∀ j, k ≤ (r j).val) :
      sysGhost.DisjointWires r :=
    disj_of_lt sysGhost r k (fun i ↦ show 0 + i.val < k by omega) hr
  have hGG_inGrid : GG * (ancGhost.basisOutcomeProjector 0 * sysGhost.embedMatrix P_grid) =
      ancGhost.basisOutcomeProjector 0 * sysGhost.embedMatrix P_grid := by
    have hEmb := congrArg rBEG.embedMatrix (hDiagEq ▸ ghostGuard_mul_inGrid_eq k m b)
    simp only [rBEG.embedMatrix_mul, ← QRegister.embedMatrix_compose,
      show rBEG.compose (sysReg k m) = sysGhost from
        GeneralBetaAndAlphaTopEndpointAlt.qreg_ext fun i ↦
          Fin.ext (by simp [rBEG, sysReg, sysGhost])] at hEmb
    let P_sig0 := (QRegister.singleton qSigG).basisOutcomeProjector 0
    have hAncSplit : rBEG.embedMatrix (ancGhostZeroProj k m) * P_sig0 =
        ancGhost.basisOutcomeProjector 0 := by
      unfold ancGhostZeroProj ancGhostReg QRegister.basisOutcomeProjector
      rw [← QRegister.embedMatrix_compose]
      refine basisZeroProj_mul_eq (rBEG.compose (QRegister.block k (m + 1) le_rfl))
        (QRegister.singleton qSigG) ancGhost
        (fun i ↦ ⟨⟨i.val, by omega⟩, Fin.ext (Nat.zero_add _)⟩)
        (fun j ↦ ⟨⟨m + 1, by omega⟩, by
          fin_cases j
          rfl⟩) fun idx ↦ ?_
      by_cases hlt : idx.val < m + 1
      · exact Or.inl ⟨⟨idx.val, hlt⟩, Fin.ext (Nat.zero_add _).symm⟩
      · exact Or.inr ⟨0, Fin.ext (show k + idx.val = k + (m + 1) by omega)⟩
    have hCommSigG : P_sig0 * sysGhost.embedMatrix P_grid =
        sysGhost.embedMatrix P_grid * P_sig0 :=
      (QRegister.singleton qSigG).embedMatrix_comm_of_disjoint sysGhost
        (hSysDisj _ fun j ↦ Fin.fin_one_eq_zero j ▸ show k ≤ k + (m + 1) by omega).symm
        (compProj 0) _
    rw [← hAncSplit, Matrix.mul_assoc _ P_sig0, hCommSigG, ← Matrix.mul_assoc _ _ P_sig0,
      ← Matrix.mul_assoc GG, hEmb]
  have hCommFSysGh : sysGhost.embedMatrix P_ferm * P_gh0 = P_gh0 * sysGhost.embedMatrix P_ferm :=
    (QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint sysGhost) _
      (hSysDisj _ fun j ↦ Fin.fin_one_eq_zero j ▸ show k ≤ k + m by omega) _ 0
  have hCommAncSys : ∀ X : Operator (2 ^ k), ancGhost.basisOutcomeProjector 0 *
      sysGhost.embedMatrix X = sysGhost.embedMatrix X * ancGhost.basisOutcomeProjector 0 :=
    fun X ↦ ((QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint sysGhost) ancGhost
      (hSysDisj _ fun j ↦ show k ≤ k + j.val by omega) X 0).symm
  have hGG_fix_of_grid : ∀ Y : Operator (2 ^ k), Y = P_grid * Y →
      GG * (ancGhost.basisOutcomeProjector 0 * sysGhost.embedMatrix Y) =
        ancGhost.basisOutcomeProjector 0 * sysGhost.embedMatrix Y := fun Y hY ↦ by
    conv_lhs => rw [hY, sysGhost.embedMatrix_mul]
    rw [← Matrix.mul_assoc (ancGhost.basisOutcomeProjector 0), ← Matrix.mul_assoc GG,
      hGG_inGrid, Matrix.mul_assoc, ← sysGhost.embedMatrix_mul, ← hY]
  have hGFix := hGG_fix_of_grid P_ferm hGridFerm.symm
  have hGEFix : GG * (sysGhost.embedMatrix E_A * (ancGhost.basisOutcomeProjector 0 *
      sysGhost.embedMatrix P_ferm)) = sysGhost.embedMatrix E_A *
      (ancGhost.basisOutcomeProjector 0 * sysGhost.embedMatrix P_ferm) := by
    have hSwap : sysGhost.embedMatrix E_A *
        (ancGhost.basisOutcomeProjector 0 * sysGhost.embedMatrix P_ferm) =
        ancGhost.basisOutcomeProjector 0 * sysGhost.embedMatrix (E_A * P_ferm) := by
      rw [← Matrix.mul_assoc, ← hCommAncSys E_A, Matrix.mul_assoc, ← sysGhost.embedMatrix_mul]
    rw [hSwap, hGG_fix_of_grid (E_A * P_ferm) (by
      conv_lhs => rw [← hGridFerm]
      rw [← Matrix.mul_assoc, (commute_exp_neg_I_smul hAGrid τ).eq,
        Matrix.mul_assoc]), ← hSwap]
  have hPghAnc :
      P_gh0 * ancGhost.basisOutcomeProjector 0 = ancGhost.basisOutcomeProjector 0 := by
    rw [← hAncProjProd, ← Matrix.mul_assoc,
      ← (QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint (rPhysInGhost k m))
        (QRegister.singleton qGhG) (rPhysInGhost_disjoint_ghost k m) _ 0,
      Matrix.mul_assoc, (QRegister.singleton qGhG).basisOutcomeProjector_mul_self 0,
      hAncProjProd]
  have hConj := ghostGuard_conj_biCatSegmentOp_mul_ghostZero_gen hm b M cert.C U_raw
  dsimp only at hConj
  have hBiEmb : (biCatSegmentUnitary k (m + 1) M cert.C (ghostZeroedBE k m hm b U_raw)).1 =
      biCatSegmentOp rBEG qSigG M cert.C (ghostZeroedBE k m hm b U_raw) := rfl
  have hDiffEmbEq : (rPhysInGhost k m).embedMatrix DiffPhys * P_gh0 = GG *
      (((biCatSegmentUnitary k (m + 1) M cert.C (ghostZeroedBE k m hm b U_raw)).1 -
      sysGhost.embedMatrix E_A) * ancGhost.basisOutcomeProjector 0) * sysGhost.embedMatrix
      P_ferm := by
    dsimp only [DiffPhys]
    rw [hBiEmb, (rPhysInGhost k m).embedMatrix_mul, BridgeDuhamel.embedMatrix_sub,
      (rPhysInGhost k m).embedMatrix_mul, ← (rPhysInGhost k m).embedMatrix_compose sysPhys E_A,
      ← (rPhysInGhost k m).embedMatrix_compose sysPhys P_ferm, hSysComp,
      Matrix.mul_assoc _ (_ * _) P_gh0, Matrix.mul_assoc _ _ P_gh0, hCommFSysGh,
      ← Matrix.mul_assoc _ P_gh0, hAncProjProd, ← hPghAnc,
      Matrix.mul_assoc P_gh0, ← Matrix.mul_assoc _ P_gh0, Matrix.sub_mul,
      Matrix.sub_mul, ← hConj, Matrix.mul_assoc _ P_gh0, ← Matrix.mul_assoc P_gh0, hPghAnc,
      Matrix.mul_assoc (sysGhost.embedMatrix E_A) P_gh0, ← Matrix.mul_assoc P_gh0, hPghAnc,
      Matrix.mul_assoc (GG * _) GG, hGFix, ← hGEFix]
    simp only [Matrix.mul_assoc, Matrix.sub_mul, Matrix.mul_sub]
    rfl
  have hNormRHS :
      ‖(rPhysInGhost k m).embedMatrix DiffPhys * P_gh0‖ ≤ (N_seg : ℝ) / 2 ^ 48 := by
    rw [hDiffEmbEq]
    exact (PhaseGradCatalystCore.norm_mul_le_of_right_le_one
      ((BridgeDuhamel.norm_embedMatrix_le sysGhost P_ferm).trans
        (BridgeDuhamel.norm_projector_le_one P_ferm hFermHerm hFermIdem))).trans
      ((PhaseGradCatalystCore.norm_mul_le_of_left_le_one
        (l2_opNorm_unitary_le_one (rBEG.embedUnitary (ghostGuardUnitary k m b)))).trans hSegG)
  refine ⟨0, ?_⟩
  change ‖((physBiSegmentUnitaryGen b M cert.C U_raw).1 -
      Complex.exp (((0 : ℝ) : ℂ) * Complex.I) • sysPhys.embedMatrix E_A) *
      (sysPhys.embedMatrix P_ferm * ancPhys.basisOutcomeProjector 0)‖ ≤ (N_seg : ℝ) / 2 ^ 48
  rw [show Complex.exp (((0 : ℝ) : ℂ) * Complex.I) = 1 by simp, one_smul,
    (QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint sysPhys) ancPhys
      (disj_of_lt sysPhys ancPhys k (fun i ↦ show 0 + i.val < k by omega)
        fun j ↦ show k ≤ k + j.val by omega) _ 0]
  refine (norm_le_of_embedMatrix_mul_proj (rPhysInGhost k m) qGhG ?_ DiffPhys).trans hNormRHS
  rintro ⟨j, hj⟩
  have hv := congrArg Fin.val hj
  by_cases hlt : j.val < k + m
  all_goals
    simp [rPhysInGhost, qGhG, hlt] at hv
    try omega
structure HoistedTwistRestOutBundle {mPayload mPGTwist : ℕ} (mWork : ℕ) where
  uTwistRestCat : SpecsAux.SpecMirror.Configuration →
    Unitary (2 ^ (fullSysCoreWires mPayload + mPGTwist))
  uTwistRest : SpecsAux.SpecMirror.Configuration →
    Unitary (2 ^ (fullSysCoreWires mPayload))
  hIntertwinesTwistRest : ∀ cfg (U_catTwist : Unitary (2 ^ mPGTwist)),
    (∀ m : Fin (2 ^ mPGTwist),
      U_catTwist.1 m 0 = PhaseGradCatalystCore.phaseGradientState mPGTwist m) →
    IntertwinesLocalCat U_catTwist (uTwistRestCat cfg) (uTwistRest cfg)
  hCoinWireComm : ∀ cfg (q : Wire (fullSysCoreWires mPayload)),
    3948 ≤ q.val → q.val < 3951 → ∀ b : Fin 2,
      (uTwistRest cfg).1 * slotBitProj q b = slotBitProj q b * (uTwistRest cfg).1
theorem iSlot2_ge_3924 (mPayload : ℕ) : 3924 ≤ (iSlot2 mPayload).val := show 3924 ≤ 3950 by decide
theorem iSlot2_ge_3948 (mPayload : ℕ) : 3948 ≤ (iSlot2 mPayload).val := show 3948 ≤ 3950 by decide
theorem iSlot2_lt_3951 (mPayload : ℕ) : (iSlot2 mPayload).val < 3951 := show 3950 < 3951 by decide
end ConfigGeneralBetaAndAlphaTopEndpoint
end GeneralBetaAndAlphaTopEndpoint
end
end ModWeighted3AGeneralBetaAndAlphaTopEndpoint

end QuantumComputation.Specs.StoppingPowerSolution
