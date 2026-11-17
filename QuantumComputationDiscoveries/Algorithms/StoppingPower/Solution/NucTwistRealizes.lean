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

public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.MomSlot1ProjKin

@[expose] public section
set_option allowUnsafeReducibility true

namespace QuantumComputation.Specs.StoppingPowerSolution

section ModNuclearTwistRealizes
@[expose] public section
namespace NuclearTwistRealizesAlt
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
end NuclearTwistRealizesAlt
namespace NuclearTwistRealizes
open Operator QProg Matrix HermitianMat Real SpecsAux
open SpecsAux.SpecMirror
open SpecsAux.BridgeFermionicComm
open SpecsAux.BridgeFermionicComm.SpecInner
open DyadicQft64 hiding dyadicTurn phaseGradKet
open DyadicQft64Engine
open SpecsAux.PhaseGradCatalystCore
open SpecsAux.DyadicSubgridToeplitz128
open Slot2Slot4QuantizedChannelBridge
open SingleAnchorFermionicPauliCap
open NuclearTwistAndXor654Concrete
open scoped Matrix BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator Circuit.Notation
section CleanPairEngine
theorem ite_pos_eq {α : Sort*} {c : Prop} {_h : Decidable c} (hc : c) {t e : α} :
    @ite α c _h t e = t := by
  cases _h with
  | isTrue _ => rfl
  | isFalse h => exact absurd hc h
theorem ite_neg_eq {α : Sort*} {c : Prop} {_h : Decidable c} (hnc : ¬c) {t e : α} :
    @ite α c _h t e = e := by
  cases _h with
  | isTrue h => exact absurd h hnc
  | isFalse _ => rfl
theorem dite_pos_eq {α : Sort*} {c : Prop} {_h : Decidable c} (hc : c) {t : c → α}
    {e : ¬c → α} : @dite α c _h t e = t hc := by
  cases _h with
  | isTrue _ => rfl
  | isFalse h => exact absurd hc h
theorem dite_neg_eq {α : Sort*} {c : Prop} {_h : Decidable c} (hnc : ¬c) {t : c → α}
    {e : ¬c → α} : @dite α c _h t e = e hnc := by
  cases _h with
  | isTrue h => exact absurd h hnc
  | isFalse _ => rfl
def _root_.QuantumComputation.Specs.StoppingPowerSolution.QRegExt.idReg (N : ℕ) : QRegister N N :=
  ⟨Function.Embedding.refl (Fin N)⟩
@[simp] theorem _root_.QuantumComputation.Specs.StoppingPowerSolution.QRegExt.idReg_apply (N : ℕ) (i
    : Fin N) : QRegExt.idReg N i = i := rfl
theorem embedUnitary_idReg_eq {N : ℕ} [NeZero (2 ^ N)] (U : Unitary (2 ^ N)) :
    (QRegExt.idReg N).embedUnitary U = U := by
  apply Subtype.ext
  ext i j
  have hextr : ∀ k : Fin (2 ^ N),(QRegExt.idReg N).extractIndex k = k := fun k ↦ by
    apply (basisBitsEquiv N).injective
    funext q
    change basisBits N ((QRegExt.idReg N).extractIndex k) q = basisBits N k q
    rw [(QRegExt.idReg N).basisBits_extractIndex]; rfl
  have henv : ((QRegExt.idReg N).basisSplitEquiv i).2 =
      ((QRegExt.idReg N).basisSplitEquiv j).2 :=
    funext fun ⟨w, hw⟩ ↦ False.elim (hw ⟨w, rfl⟩)
  simp only [QRegister.embedUnitary_val, QRegister.embedMatrix_apply, hextr i, hextr j, henv,
    ↓reduceIte, mul_one]
theorem _root_.QuantumComputation.Specs.StoppingPowerSolution.QRegExt.range_eq_image {k n : ℕ} (r :
    QRegister k n) :
    (r.image : Set (Wire n)) = Set.range r.wires := by
  ext w; simp [QRegister.mem_image]
theorem mem_support_X {n : ℕ} {z q : Wire n} (hz : z ∈ (Circuit.X q).support) : z = q := by
  obtain ⟨_, _, hq⟩ := Finset.mem_map.mp hz
  exact hq.symm
theorem support_X_sub {n : ℕ} {S : Finset (Wire n)} {q : Wire n} (hq : q ∈ S) :
    (Circuit.X q).support ⊆ S := fun _ hz ↦ (mem_support_X hz) ▸ hq
theorem support_seq_sub {n : ℕ} {S : Finset (Wire n)} {c₁ c₂ : Circuit n}
    (h₁ : c₁.support ⊆ S) (h₂ : c₂.support ⊆ S) : (c₁ ;;ᶜ c₂).support ⊆ S := by
  rw [Circuit.support_seq]; exact Finset.union_subset h₁ h₂
theorem take_succ_ofFn {α : Type*} {M : ℕ} (f : Fin M → α) (t : ℕ) (ht : t < M) :
    (List.ofFn f).take (t + 1) = (List.ofFn f).take t ++ [f ⟨t, ht⟩] := by
  rw [List.take_add_one, List.getElem?_ofFn]
  simp only [ht, ↓reduceDIte, Option.toList_some]
theorem _root_.QuantumComputation.Specs.StoppingPowerSolution.OperatorExt.permutationUnitary_one {d
    : ℕ} :
    Operator.permutationUnitary (1 : Equiv.Perm (Fin d)) = 1 := by
  apply Subtype.ext
  simp [Operator.permutationUnitary]
theorem _root_.QuantumComputation.Specs.StoppingPowerSolution.QRegExt.disjointWires_to_finset {k₁ k₂
    n : ℕ} {r : QRegister k₁ n}
    {s : QRegister k₂ n} (h : r.DisjointWires s) : Disjoint r.image s.image := by
  rw [← Finset.disjoint_coe, QRegExt.range_eq_image, QRegExt.range_eq_image]
  exact h
theorem _root_.QuantumComputation.Specs.StoppingPowerSolution.QRegExt.disjointWires_of_finset {k₁ k₂
    n : ℕ} {r : QRegister k₁ n}
    {s : QRegister k₂ n} (h : Disjoint r.image s.image) : r.DisjointWires s := by
  unfold QRegister.DisjointWires
  rw [← QRegExt.range_eq_image, ← QRegExt.range_eq_image]
  exact Finset.disjoint_coe.mpr h
theorem _root_.QuantumComputation.Specs.StoppingPowerSolution.QRegExt.disjointWires_mono_left {k₁
    k₁' k₂ n : ℕ} {r : QRegister k₁ n}
    {r' : QRegister k₁' n} {s : QRegister k₂ n} (h : r.DisjointWires s)
    (hsub : r'.image ⊆ r.image) : r'.DisjointWires s := QRegExt.disjointWires_of_finset
    (Finset.disjoint_of_subset_left hsub (QRegExt.disjointWires_to_finset h))
theorem _root_.QuantumComputation.Specs.StoppingPowerSolution.QRegExt.disjointWires_mono_right {k₁
    k₂ k₂' n : ℕ} {r : QRegister k₁ n}
    {s : QRegister k₂ n} {s' : QRegister k₂' n} (h : r.DisjointWires s)
    (hsub : s'.image ⊆ s.image) : r.DisjointWires s' := QRegExt.disjointWires_of_finset
    (Finset.disjoint_of_subset_right hsub (QRegExt.disjointWires_to_finset h))
theorem _root_.QuantumComputation.Specs.StoppingPowerSolution.QRegExt.disjointWires_concat_left {k₁
    k₂ k₃ n : ℕ} {r₁ : QRegister k₁ n}
    {r₂ : QRegister k₂ n} {s : QRegister k₃ n} {h₁₂ : r₁.DisjointWires r₂}
    (h₁ : r₁.DisjointWires s) (h₂ : r₂.DisjointWires s) : (r₁.concat r₂ h₁₂).DisjointWires s
    :=
  QRegExt.disjointWires_of_finset (by
    rw [QRegExt.image_concat, Finset.disjoint_union_left]
    exact ⟨QRegExt.disjointWires_to_finset h₁, QRegExt.disjointWires_to_finset h₂⟩)
theorem _root_.QuantumComputation.Specs.StoppingPowerSolution.QRegExt.disjointWires_concat_right {k₁
    k₂ k₃ n : ℕ} {r : QRegister k₁ n}
    {s₁ : QRegister k₂ n} {s₂ : QRegister k₃ n} {h₁₂ : s₁.DisjointWires s₂}
    (h₁ : r.DisjointWires s₁) (h₂ : r.DisjointWires s₂) : r.DisjointWires (s₁.concat s₂ h₁₂)
    :=
  QRegExt.disjointWires_of_finset (by
    rw [QRegExt.image_concat, Finset.disjoint_union_right]
    exact ⟨QRegExt.disjointWires_to_finset h₁, QRegExt.disjointWires_to_finset h₂⟩)
@[simp] theorem basisBits_symm_eq (N : ℕ) (β : BitAssignment N) : basisBits N
    ((basisBitsEquiv N).symm β) = β := (basisBitsEquiv N).apply_symm_apply β
@[simp] theorem basisBits_symm_apply (N : ℕ) (β : BitAssignment N) (w : Wire N) : basisBits N
    ((basisBitsEquiv N).symm β) w = β w := congrFun ((basisBitsEquiv N).apply_symm_apply β) w
theorem embedUnitary_perm_mulVec_basisKet {k n : ℕ} [NeZero (2 ^ n)] (r : QRegister k n)
    (perm : Equiv.Perm (Fin (2 ^ k))) (β β_out : BitAssignment n) (h_in : ∀ q : Fin k, β_out
    (r q) = basisBits k (perm ((basisBitsEquiv k).symm (fun q' ↦ β (r q')))) q)
    (h_out : ∀ z : Wire n, z ∉ r.image → β_out z = β z) :
    (r.embedUnitary (Operator.permutationUnitary perm)).1.mulVec (basisKet β) = basisKet β_out
    := by
  have hextr : r.extractIndex ((basisBitsEquiv n).symm β) =
      (basisBitsEquiv k).symm (fun q' ↦ β (r q')) := by
    apply (basisBitsEquiv k).injective; funext q
    change basisBits k _ q = basisBits k _ q
    rw [r.basisBits_extractIndex, basisBits_symm_apply, basisBits_symm_apply]
  have hket_g : basisKet β = Pi.single ((basisBitsEquiv n).symm β) (1 : ℂ) := rfl
  rw [hket_g, QRegister.embedUnitary_val, r.embedMatrix_mulVec_single_factors,
    Operator.permutationUnitary_mulVec_single, r.tensorState_single_replaceIndex, hextr]
  simp only [basisKet]
  congr 1
  apply (basisBitsEquiv n).injective; funext z
  change basisBits n _ z = basisBits n _ z
  rw [basisBits_symm_apply]
  by_cases hz : z ∈ r.image
  · obtain ⟨q, rfl⟩ := (QRegister.mem_image r z).mp hz
    rw [r.basisBits_replaceIndex_apply, h_in q]
  · have hnot : z ∉ Set.range r.wires :=
      fun ⟨q, hq⟩ ↦ hz ((QRegister.mem_image r z).mpr ⟨q, hq⟩)
    rw [r.basisBits_replaceIndex_of_not_mem _ _ z hnot, basisBits_symm_apply, h_out z hz]
theorem basisBits_perm_ofBijective {k : ℕ} (f : BitAssignment k → BitAssignment k)
    (hf : Function.Bijective f) (γ : BitAssignment k) (q : Fin k) : basisBits k
    (((basisBitsEquiv k).trans ((Equiv.ofBijective f hf).trans (basisBitsEquiv k).symm))
    ((basisBitsEquiv k).symm γ)) q = f γ q := by
  dsimp only [Equiv.trans_apply, Equiv.coe_ofBijective]
  rw [(basisBitsEquiv k).apply_symm_apply, (basisBitsEquiv k).apply_symm_apply]
structure RealizesCleanPair {Var : Type} [Fintype Var] [DecidableEq Var] {k m n : ℕ}
    [NeZero (2 ^ n)] (rAct : QRegister k n) (rWork : QRegister m n)
    (u : Unitary (2 ^ k)) (dFwd dInv : DynamicCircuit Var n) : Prop where
  fwd : DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace rAct rWork u dFwd
  inv : DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace rAct rWork u⁻¹ dInv
theorem embedUnitary_inv_eq {k M : ℕ} (sel : QRegister k M) (u : Unitary (2 ^ k)) :
    sel.embedUnitary u⁻¹ = (sel.embedUnitary u)⁻¹ := by
  symm
  apply mul_eq_one_iff_inv_eq.mp
  rw [← sel.embedUnitary_mul, mul_inv_cancel, sel.embedUnitary_one]
theorem RealizesCleanPair.symm {Var : Type} [Fintype Var] [DecidableEq Var]
    {k m n : ℕ} [NeZero (2 ^ n)]
    {rAct : QRegister k n} {rWork : QRegister m n}
    {u : Unitary (2 ^ k)} {dFwd dInv : DynamicCircuit Var n}
    (hp : RealizesCleanPair rAct rWork u dFwd dInv) :
    RealizesCleanPair rAct rWork u⁻¹ dInv dFwd where
  fwd := hp.inv
  inv := by
    rw [inv_inv]
    exact hp.fwd
theorem RealizesCleanPair.congr_unitary {Var : Type} [Fintype Var] [DecidableEq Var]
    {k m n : ℕ} [NeZero (2 ^ n)] {rAct : QRegister k n} {rWork : QRegister m n}
    {u u' : Unitary (2 ^ k)} {dFwd dInv : DynamicCircuit Var n}
    (hp : RealizesCleanPair rAct rWork u dFwd dInv) (hu : u = u') : RealizesCleanPair rAct
    rWork u' dFwd dInv := hu ▸ hp
theorem RealizesCleanPair.one {Var : Type} [Fintype Var] [DecidableEq Var]
    {k m n : ℕ} [NeZero (2 ^ n)]
    (rAct : QRegister k n) (rWork : QRegister m n) :
    RealizesCleanPair rAct rWork 1 (.identity : DynamicCircuit Var n) .identity where
  fwd := DynCircuitExt.realizesEmbeddedUnitaryWithCleanWorkspace_identity rAct rWork
  inv := by
    rw [inv_one]
    exact DynCircuitExt.realizesEmbeddedUnitaryWithCleanWorkspace_identity rAct rWork
theorem RealizesCleanPair.widenActive {Var : Type} [Fintype Var] [DecidableEq Var]
    {k₁ k m n : ℕ} [NeZero (2 ^ n)]
    {rAct : QRegister k n} {sel : QRegister k₁ k} {rWork : QRegister m n}
    {u : Unitary (2 ^ k₁)} {dFwd dInv : DynamicCircuit Var n}
    (hp : RealizesCleanPair (rAct.compose sel) rWork u dFwd dInv) :
    RealizesCleanPair rAct rWork (sel.embedUnitary u) dFwd dInv where
  fwd := hp.fwd.widenActive
  inv := by
    rw [← embedUnitary_inv_eq]
    exact hp.inv.widenActive
theorem RealizesCleanPair.widenWorkspace {Var : Type} [Fintype Var] [DecidableEq Var]
    {k m₁ m n : ℕ} [NeZero (2 ^ n)]
    {rAct : QRegister k n} {rWork : QRegister m n} {sel : QRegister m₁ m}
    {u : Unitary (2 ^ k)} {dFwd dInv : DynamicCircuit Var n}
    (hp : RealizesCleanPair rAct (rWork.compose sel) u dFwd dInv) :
    RealizesCleanPair rAct rWork u dFwd dInv where
  fwd := hp.fwd.widenWorkspace
  inv := hp.inv.widenWorkspace
theorem RealizesCleanPair.seq {Var : Type} [Fintype Var] [DecidableEq Var]
    {k m n : ℕ} [NeZero (2 ^ n)]
    {rAct : QRegister k n} {rWork : QRegister m n} (hdisj : rAct.DisjointWires rWork)
    {u₁ u₂ : Unitary (2 ^ k)} {d₁ d₁' d₂ d₂' : DynamicCircuit Var n}
    (p₁ : RealizesCleanPair rAct rWork u₁ d₁ d₁')
    (p₂ : RealizesCleanPair rAct rWork u₂ d₂ d₂') :
    RealizesCleanPair rAct rWork (u₂ * u₁) (.seq d₁ d₂) (.seq d₂' d₁') where
  fwd := p₁.fwd.seq hdisj p₂.fwd
  inv := by
    rw [_root_.mul_inv_rev]
    exact p₂.inv.seq hdisj p₁.inv
theorem wp_sequenceList_append {Var : Type} [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)]
    (as bs : List (DynamicCircuit Var n)) (Θ : CQAssertionCompat Var (2 ^ n)) :
    wp (DynCircuitExt.sequenceList (as ++ bs)).compile Θ =
      wp (DynamicCircuit.seq (DynCircuitExt.sequenceList as) (DynCircuitExt.sequenceList
        bs)).compile Θ := by
  induction as with
  | nil => rfl
  | cons a as ih =>
      simp only [List.cons_append, DynCircuitExt.sequenceList_cons, DynamicCircuit.compile_seq,
        wp_qSeq, ih]
theorem realizesClean_congr_wp {Var : Type} [Fintype Var] [DecidableEq Var] {k m n : ℕ}
    [NeZero (2 ^ n)] {rAct : QRegister k n} {rWork : QRegister m n} {u : Unitary (2 ^ k)}
    {d₁ d₂ : DynamicCircuit Var n} (hwp : ∀ M : Observable (Fin (2 ^ n)), wp d₂.compile (fun _ ↦ M)
    = wp d₁.compile (fun _ ↦ M)) (hd :
    DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace rAct rWork u d₁) :
    DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace rAct rWork u d₂ := by
  intro M
  obtain ⟨M', h₁, h₂⟩ := hd M
  exact ⟨M', (hwp M).trans h₁, h₂⟩
theorem RealizesCleanPair.sequenceList {Var : Type} [Fintype Var] [DecidableEq Var]
    {k m n : ℕ} [NeZero (2 ^ n)] {rAct : QRegister k n} {rWork : QRegister m n}
    (hdisj : rAct.DisjointWires rWork) (L : List (Unitary (2 ^ k) × DynamicCircuit Var n ×
    DynamicCircuit Var n)) (hL : ∀ x ∈ L, RealizesCleanPair rAct rWork x.1 x.2.1 x.2.2) :
    RealizesCleanPair rAct rWork (L.reverse.map Prod.fst).prod
    (DynCircuitExt.sequenceList (L.map fun x ↦ x.2.1))
    (DynCircuitExt.sequenceList (L.reverse.map fun x ↦ x.2.2)) := by
  induction L with
  | nil => exact RealizesCleanPair.one rAct rWork
  | cons hd tl ih =>
      have hhd := hL hd List.mem_cons_self
      have htl := ih (fun x hx ↦ hL x (List.mem_cons_of_mem hd hx))
      have hseq := hhd.seq hdisj htl
      have hprod : ((hd :: tl).reverse.map Prod.fst).prod = (tl.reverse.map Prod.fst).prod *
          hd.1 := by
        rw [List.reverse_cons, List.map_append, List.prod_append, List.map_singleton,
          List.prod_singleton]
      refine { fwd := ?_, inv := ?_ }
      · rw [hprod]
        exact hseq.fwd
      · rw [hprod, List.reverse_cons, List.map_append, List.map_singleton]
        refine realizesClean_congr_wp (fun M ↦ ?_) hseq.inv
        rw [wp_sequenceList_append]
        simp only [DynCircuitExt.sequenceList_cons, DynCircuitExt.sequenceList_nil,
          DynamicCircuit.compile_seq, DynamicCircuit.compile_identity, wp_qSeq, wp_skip]
theorem catModAddUnitary_mul (kSys B : ℕ) [NeZero (2 ^ (kSys + B))]
    (Δ₁ Δ₂ : BitAssignment kSys → ℕ) : catModAddUnitary kSys B Δ₂ * catModAddUnitary kSys B Δ₁
    = catModAddUnitary kSys B (fun γ ↦ Δ₁ γ + Δ₂ γ) := by
  let rSys0 : QRegister kSys (kSys + B) := .block 0 kSys (by omega)
  let rCat0 : QRegister B (kSys + B) := .block kSys B le_rfl
  have hdisj : rSys0.DisjointWires rCat0 :=
    QRegister.block_disjoint_of_le 0 kSys kSys B (by omega) (by omega) (by omega)
  have hid : rSys0.concat rCat0 hdisj = (QRegExt.idReg _) := by
    apply NuclearTwistRealizesAlt.qreg_ext
    intro i
    by_cases hi : i.val < kSys
    · have : i = Fin.castAdd B ⟨i.val, hi⟩ := Fin.ext rfl
      rw [this, QRegister.concat_apply_left]; ext; simp [QRegExt.idReg, rSys0]
    · have : i = Fin.natAdd kSys ⟨i.val - kSys, by omega⟩ := Fin.ext (by dsimp; omega)
      rw [this, QRegister.concat_apply_right]
      apply Fin.ext; dsimp [rCat0, NuclearTwistRealizesAlt.qreg_block_apply,
        NuclearTwistRealizesAlt.qreg_block_wires_apply,
        NuclearTwistRealizesAlt.qreg_whole_wires,
        NuclearTwistRealizesAlt.emb_trans_apply,
        NuclearTwistRealizesAlt.emb_refl_apply,
        NuclearTwistRealizesAlt.emb_mk_apply]
  apply Subtype.ext
  apply matrix_ext_basisKet
  intro β
  let m₁ : Fin (2 ^ B) := ⟨(regVal rCat0 β + Δ₁ (fun q ↦ β (rSys0 q))) % 2 ^ B,
    Nat.mod_lt _ (by positivity)⟩
  let β₁ : BitAssignment (kSys + B) :=
    basisBits (kSys + B) (rCat0.replaceIndex ((basisBitsEquiv (kSys + B)).symm β) m₁)
  have hout₁ : ∀ w, w ∉ rCat0.image → β₁ w = β w := fun w hw ↦ by
    have hnot : w ∉ Set.range rCat0.wires := fun ⟨j, hj⟩ ↦
      hw ((QRegister.mem_image rCat0 w).mpr ⟨j, hj⟩)
    simp only [β₁, rCat0.basisBits_replaceIndex_of_not_mem _ _ w hnot, basisBits_symm_apply]
  have hval₁ : regVal rCat0 β₁ = m₁.val := by
    have : (fun j ↦ β₁ (rCat0 j)) = basisBits B m₁ :=
      funext fun j ↦ by dsimp only [β₁]; exact rCat0.basisBits_replaceIndex_apply _ m₁ j
    rw [regVal, this, bitsVal_basisBits]
  have hev₁ : ((rSys0.concat rCat0 hdisj).embedUnitary (catModAddUnitary kSys B Δ₁)).1.mulVec
      (basisKet β) = basisKet β₁ :=
    (catModAddUnitary_mulVec_basisKet rSys0 rCat0 hdisj Δ₁ (fun _ ↦ β₁) β (fun w hw ↦
      hout₁ w hw) hval₁).symm
  let m₂ : Fin (2 ^ B) := ⟨(m₁.val + Δ₂ (fun q ↦ β₁ (rSys0 q))) % 2 ^ B,
    Nat.mod_lt _ (by positivity)⟩
  let β₂ : BitAssignment (kSys + B) :=
    basisBits (kSys + B) (rCat0.replaceIndex ((basisBitsEquiv (kSys + B)).symm β₁) m₂)
  have hout₂ : ∀ w, w ∉ rCat0.image → β₂ w = β₁ w := fun w hw ↦ by
    have hnot : w ∉ Set.range rCat0.wires := fun ⟨j, hj⟩ ↦
      hw ((QRegister.mem_image rCat0 w).mpr ⟨j, hj⟩)
    simp only [β₂, rCat0.basisBits_replaceIndex_of_not_mem _ _ w hnot, basisBits_symm_apply]
  have hval₂ : regVal rCat0 β₂ = m₂.val := by
    have : (fun j ↦ β₂ (rCat0 j)) = basisBits B m₂ :=
      funext fun j ↦ by dsimp only [β₂]; exact rCat0.basisBits_replaceIndex_apply _ m₂ j
    rw [regVal, this, bitsVal_basisBits]
  have hev₂ : ((rSys0.concat rCat0 hdisj).embedUnitary (catModAddUnitary kSys B Δ₂)).1.mulVec
      (basisKet β₁) = basisKet β₂ :=
    (catModAddUnitary_mulVec_basisKet rSys0 rCat0 hdisj Δ₂ (fun _ ↦ β₂) β₁
      (fun w hw ↦ hout₂ w hw) (hval₂.trans (by dsimp only [m₂]; rw [← hval₁]))).symm
  have hsys_eq : (fun q ↦ β₁ (rSys0 q)) = (fun q ↦ β (rSys0 q)) :=
    funext fun q ↦ hout₁ (rSys0 q) (hdisj.apply_not_mem_right q)
  have hev_sum : ((rSys0.concat rCat0 hdisj).embedUnitary
      (catModAddUnitary kSys B (fun γ ↦ Δ₁ γ + Δ₂ γ))).1.mulVec (basisKet β) = basisKet β₂ := by
    symm
    apply catModAddUnitary_mulVec_basisKet rSys0 rCat0 hdisj
      (fun γ ↦ Δ₁ γ + Δ₂ γ) (fun _ ↦ β₂) β
    · intro w hw
      rw [hout₂ w hw, hout₁ w hw]
    · rw [hval₂]
      dsimp only [m₂, m₁]
      rw [hsys_eq, Nat.mod_add_mod, add_assoc]
  rw [hid] at hev₁ hev₂ hev_sum
  simp only [embedUnitary_idReg_eq] at hev₁ hev₂ hev_sum
  rw [Submonoid.coe_mul, ← Matrix.mulVec_mulVec, hev₁, hev₂, hev_sum]
theorem catModAddUnitary_one (kSys B : ℕ) [NeZero (2 ^ (kSys + B))] :
    catModAddUnitary kSys B (fun _ ↦ 0) = 1 := by
  let rSys0 : QRegister kSys (kSys + B) := .block 0 kSys (by omega)
  let rCat0 : QRegister B (kSys + B) := .block kSys B le_rfl
  have hdisj : rSys0.DisjointWires rCat0 :=
    QRegister.block_disjoint_of_le 0 kSys kSys B (by omega) (by omega) (by omega)
  have hid : rSys0.concat rCat0 hdisj = (QRegExt.idReg _) := by
    apply NuclearTwistRealizesAlt.qreg_ext
    intro i
    by_cases hi : i.val < kSys
    · have : i = Fin.castAdd B ⟨i.val, hi⟩ := Fin.ext rfl
      rw [this, QRegister.concat_apply_left]; ext; simp [QRegExt.idReg, rSys0]
    · have : i = Fin.natAdd kSys ⟨i.val - kSys, by omega⟩ := Fin.ext (by dsimp; omega)
      rw [this, QRegister.concat_apply_right]
      apply Fin.ext; dsimp [rCat0, NuclearTwistRealizesAlt.qreg_block_apply,
        NuclearTwistRealizesAlt.qreg_block_wires_apply,
        NuclearTwistRealizesAlt.qreg_whole_wires,
        NuclearTwistRealizesAlt.emb_trans_apply,
        NuclearTwistRealizesAlt.emb_refl_apply,
        NuclearTwistRealizesAlt.emb_mk_apply]
  apply Subtype.ext
  apply matrix_ext_basisKet
  intro β
  have hev : ((rSys0.concat rCat0 hdisj).embedUnitary (catModAddUnitary kSys B (fun _ ↦
    0))).1.mulVec
      (basisKet β) = basisKet β := by
    symm
    apply catModAddUnitary_mulVec_basisKet rSys0 rCat0 hdisj (fun _ ↦ 0) id β (fun _ _ ↦ rfl)
    rw [add_zero, Nat.mod_eq_of_lt (regVal_lt_two_pow rCat0 β)]
    rfl
  rw [hid, embedUnitary_idReg_eq] at hev
  rw [hev, OneMemClass.coe_one, Matrix.one_mulVec]
theorem dyadicDiagUnitary_mul (k B : ℕ) [NeZero (2 ^ k)] (e₁ e₂ : BitAssignment k → ℤ) :
    dyadicDiagUnitary k B e₂ * dyadicDiagUnitary k B e₁ =
      dyadicDiagUnitary k B (fun γ ↦ e₁ γ + e₂ γ) := by
  apply Subtype.ext
  apply matrix_ext_basisKet
  intro β
  have h1 := embedUnitary_dyadicDiagUnitary_mulVec_basisKet (QRegExt.idReg k) B e₁ β
  have h2 := embedUnitary_dyadicDiagUnitary_mulVec_basisKet (QRegExt.idReg k) B e₂ β
  have h12 := embedUnitary_dyadicDiagUnitary_mulVec_basisKet (QRegExt.idReg k) B
    (fun γ ↦ e₁ γ + e₂ γ) β
  simp only [embedUnitary_idReg_eq] at h1 h2 h12
  rw [Submonoid.coe_mul, ← Matrix.mulVec_mulVec, h1, Matrix.mulVec_smul, h2, h12,
    smul_smul, ← dyadicTurn_add]
theorem dyadicDiagUnitary_congr (k B : ℕ) [NeZero (2 ^ k)] {e₁ e₂ : BitAssignment k → ℤ}
    (h : ∀ γ, e₁ γ = e₂ γ) : dyadicDiagUnitary k B e₁ = dyadicDiagUnitary k B e₂ := congrArg
    (dyadicDiagUnitary k B) (funext h)
def CleanComputePair {Var : Type} [Fintype Var] [DecidableEq Var] {kCore mTmp mScr n : ℕ}
    [NeZero (2 ^ n)] (rCore : QRegister kCore n) (rTmp : QRegister mTmp n)
    (rScr : QRegister mScr n) (hCT : rCore.DisjointWires rTmp)
    (uComp : Unitary (2 ^ (kCore + mTmp))) (gTmp : BitAssignment kCore → BitAssignment mTmp)
    (dComp dCompInv : DynamicCircuit Var n) : Prop := RealizesCleanPair
    (rCore.concat rTmp hCT) rScr uComp dComp dCompInv ∧ (∀ β : BitAssignment n, (∀ i : Fin
    mTmp, β (rTmp i) = 0) → ∃ β₁ : BitAssignment n, ((rCore.concat rTmp hCT).embedUnitary
    uComp).1.mulVec (basisKet β) = basisKet β₁ ∧ (∀ w, w ∉ rTmp.image → β₁ w = β w) ∧ (∀ i :
    Fin mTmp, β₁ (rTmp i) = gTmp (fun q ↦ β (rCore q)) i))
theorem CleanComputePair.pair {Var : Type} [Fintype Var] [DecidableEq Var]
    {kCore mTmp mScr n : ℕ} [NeZero (2 ^ n)] {rCore : QRegister kCore n}
    {rTmp : QRegister mTmp n} {rScr : QRegister mScr n} {hCT : rCore.DisjointWires rTmp}
    {uComp : Unitary (2 ^ (kCore + mTmp))} {gTmp : BitAssignment kCore → BitAssignment mTmp}
    {dComp dCompInv : DynamicCircuit Var n} (hc : CleanComputePair rCore rTmp rScr hCT uComp
    gTmp dComp dCompInv) : RealizesCleanPair (rCore.concat rTmp hCT) rScr uComp dComp dCompInv
    := hc.1
end CleanPairEngine
section BarrelAndXor32Core
lemma zmod2_add_one_invol (x : ZMod 2) : (x + 1) + 1 = x := by
  revert x; decide
def xor32BitFn (mPayload : ℕ) (γ : BitAssignment (fullSysCoreWires mPayload)) :
    BitAssignment (fullSysCoreWires mPayload) :=
  fun k ↦ if k.val < 3924 ∧ k.val % 6 = 5 then γ k + 1 else γ k
theorem xor32BitFn_involutive (mPayload : ℕ) :
    Function.Involutive (xor32BitFn mPayload) := fun γ ↦ by
  funext k
  dsimp only [xor32BitFn]
  split_ifs
  · exact zmod2_add_one_invol (γ k)
  · rfl
noncomputable def xor32CorePerm (mPayload : ℕ) : Equiv.Perm (Fin (2 ^ (fullSysCoreWires mPayload)))
    :=
  (basisBitsEquiv (fullSysCoreWires mPayload)).trans
    ((Equiv.ofBijective (xor32BitFn mPayload) (xor32BitFn_involutive mPayload).bijective).trans
      (basisBitsEquiv (fullSysCoreWires mPayload)).symm)
theorem xor32CorePerm_involutive (mPayload : ℕ) (x : Fin (2 ^ (fullSysCoreWires mPayload))) :
    xor32CorePerm mPayload (xor32CorePerm mPayload x) = x := by
  unfold xor32CorePerm
  change (basisBitsEquiv _).symm (xor32BitFn mPayload
    ((basisBitsEquiv _) ((basisBitsEquiv _).symm (xor32BitFn mPayload ((basisBitsEquiv _) x))))) = x
  rw [(basisBitsEquiv _).apply_symm_apply, xor32BitFn_involutive mPayload _,
    (basisBitsEquiv _).symm_apply_apply]
noncomputable def uXor32Core (mPayload : ℕ) : Unitary (2 ^ (fullSysCoreWires mPayload)) :=
  Operator.permutationUnitary (xor32CorePerm mPayload)
theorem uXor32Core_inv (mPayload : ℕ) : (uXor32Core mPayload)⁻¹ = uXor32Core mPayload := by
  apply mul_eq_one_iff_inv_eq.mp
  have hperm_sq : xor32CorePerm mPayload * xor32CorePerm mPayload = 1 := by
    apply Equiv.ext; intro x
    exact xor32CorePerm_involutive mPayload x
  unfold uXor32Core
  rw [← OperatorExt.permutationUnitary_mul, hperm_sq, OperatorExt.permutationUnitary_one]
theorem phasePerm_sequence_X {M n : ℕ} (f : Fin M → Wire n) (hinj : Function.Injective f) :
    PhasePerm ⊤ (Circuit.sequence (List.ofFn fun a : Fin M ↦ Circuit.X (f a))) (fun _ ↦ 1)
      (fun β w ↦ if ∃ a : Fin M, f a = w then β w + 1 else β w) := by
  have hFold : ∀ (t : ℕ) (ht : t ≤ M), PhasePerm ⊤ (Circuit.sequence ((List.ofFn fun a : Fin M
      ↦ Circuit.X (f a)).take t)) (fun _ ↦ 1) (fun β w ↦ if ∃ a : Fin M, a.val < t ∧ f a = w
      then β w + 1 else β w) := by
    intro t ht
    induction t with
    | zero =>
        refine { evolve := fun β ↦ ?_, outside := fun _ x hm ↦ absurd (Finset.mem_univ x) hm }
        have hid : (fun w ↦ if ∃ a : Fin M, a.val < 0 ∧ f a = w then β w + 1 else β w) = β := by
          funext w
          have hfalse : ¬(∃ a : Fin M, a.val < 0 ∧ f a = w) := fun ⟨a, ha, _⟩ ↦ by omega
          simp only [hfalse, ↓reduceIte]
        rw [hid]
        simp only [List.take_zero, Circuit.sequence_nil, Circuit.eval_identity,
          Submonoid.coe_one, Matrix.one_mulVec, one_smul]
    | succ t ih =>
        have ih_t := ih (by omega)
        let a_t : Fin M := ⟨t, ht⟩
        have htake : (List.ofFn fun a : Fin M ↦ Circuit.X (f a)).take (t + 1) =
            (List.ofFn fun a : Fin M ↦ Circuit.X (f a)).take t ++ [Circuit.X (f a_t)] :=
          take_succ_ofFn _ t (Nat.lt_of_succ_le ht)
        refine { evolve := fun β ↦ ?_, outside := fun _ x hm ↦ absurd (Finset.mem_univ x) hm }
        rw [htake, Circuit.eval_sequence, List.map_append, List.reverse_append,
          List.map_singleton, List.reverse_singleton, List.singleton_append, List.prod_cons,
          ← Circuit.eval_sequence, Submonoid.coe_mul, ← Matrix.mulVec_mulVec,
          ih_t.evolve β, one_smul, (phasePerm_X (f a_t)).evolve _, one_smul, one_smul]
        congr 1
        funext w
        by_cases hwat : w = f a_t
        · subst hwat
          have hnot_prev : ¬(∃ a : Fin M, a.val < t ∧ f a = f a_t) := by
            rintro ⟨a, ha_lt, hfa⟩
            have heq := congrArg Fin.val (hinj hfa)
            dsimp only [a_t] at heq; omega
          have hex_new : ∃ a : Fin M, a.val < t + 1 ∧ f a = f a_t :=
            ⟨a_t, Nat.lt_succ_self t, rfl⟩
          simp only [Function.update_self, hnot_prev, hex_new, ↓reduceIte]
        · have hiff : (∃ a : Fin M, a.val < t ∧ f a = w) ↔
              (∃ a : Fin M, a.val < t + 1 ∧ f a = w) := by
            constructor
            · rintro ⟨a, ha, rfl⟩; exact ⟨a, by omega, rfl⟩
            · rintro ⟨a, ha, rfl⟩
              have hne : a.val ≠ t := fun heq ↦ hwat (congrArg f (Fin.ext heq))
              exact ⟨a, by omega, rfl⟩
          simp only [Function.update_of_ne hwat, hiff]
  have hall := hFold M le_rfl
  rw [List.take_of_length_le (by rw [List.length_ofFn])] at hall
  refine { evolve := fun β ↦ ?_, outside := fun _ _ hw ↦ False.elim (hw (Finset.mem_univ _)) }
  rw [hall.evolve β]
  congr 2
  funext w
  have hiff : (∃ a : Fin M, a.val < M ∧ f a = w) ↔ (∃ a : Fin M, f a = w) :=
    ⟨fun ⟨a, _, h⟩ ↦ ⟨a, h⟩, fun ⟨a, h⟩ ↦ ⟨a, a.isLt, h⟩⟩
  simp only [hiff]
theorem dXor32All654_realizesPair {Var : Type} [Fintype Var] [DecidableEq Var]
    {mPayload mWork n : ℕ} [NeZero (2 ^ n)]
    (rCore : QRegister (fullSysCoreWires mPayload) n)
    (rWork : QRegister mWork n) :
    RealizesCleanPair rCore rWork (uXor32Core mPayload)
      (dXor32All654 (Var := Var) rCore) (dXor32All654 (Var := Var) rCore) := by
  let fWire : Fin 654 → Wire n := fun a ↦ rElecAxis654 rCore a 5
  have hinj : Function.Injective fWire := by
    intro a₁ a₂ h
    have hv := congrArg Fin.val (rCore.wires.injective h)
    dsimp [fWire, rElecAxis654, QRegister.slice, QRegister.slice_apply,
      NuclearTwistRealizesAlt.qreg_slice_wires,
      NuclearTwistRealizesAlt.qreg_whole_wires,
      NuclearTwistRealizesAlt.emb_trans_apply,
      NuclearTwistRealizesAlt.emb_refl_apply,
      NuclearTwistRealizesAlt.emb_mk_apply, QRegister.compose, QRegister.compose_apply,
      NuclearTwistRealizesAlt.qreg_compose_wires,
      NuclearTwistRealizesAlt.qreg_block_apply,
      NuclearTwistRealizesAlt.qreg_block_wires_apply] at hv
    exact Fin.ext (by have := a₁.isLt; have := a₂.isLt; omega)
  have hp := phasePerm_sequence_X fWire hinj
  have heval : (parallelBit5FlipAxes (rElecAxis654 rCore)).eval =
      rCore.embedUnitary (uXor32Core mPayload) := by
    apply circuit_eval_eq_embed_perm_of_phasePerm rCore
      (parallelBit5FlipAxes (rElecAxis654 rCore)) (xor32CorePerm mPayload) _ hp
    · intro β w hw
      have hnot : ¬(∃ a : Fin 654, fWire a = w) := by
        rintro ⟨a, rfl⟩
        exact hw ((QRegister.mem_image rCore _).mpr ⟨_, rfl⟩)
      simp only [hnot, ↓reduceIte]
    · intro β
      ext k
      change basisBits _ ((xor32CorePerm mPayload)
        ((basisBitsEquiv _).symm (fun q ↦ β (rCore q)))) k = _
      unfold xor32CorePerm
      rw [basisBits_perm_ofBijective (xor32BitFn mPayload) (xor32BitFn_involutive
        mPayload).bijective]
      dsimp only [xor32BitFn]
      have hiff : (k.val < 3924 ∧ k.val % 6 = 5) ↔ (∃ a : Fin 654, fWire a = rCore k) := by
        constructor
        · rintro ⟨hlt, hmod⟩
          refine ⟨⟨k.val / 6, by omega⟩, ?_⟩
          dsimp [fWire, rElecAxis654, QRegister.slice, QRegister.slice_apply,
            NuclearTwistRealizesAlt.qreg_slice_wires,
            NuclearTwistRealizesAlt.qreg_whole_wires,
            NuclearTwistRealizesAlt.emb_trans_apply,
            NuclearTwistRealizesAlt.emb_refl_apply,
            NuclearTwistRealizesAlt.emb_mk_apply, QRegister.compose,
            QRegister.compose_apply, NuclearTwistRealizesAlt.qreg_compose_wires,
            NuclearTwistRealizesAlt.qreg_block_apply,
            NuclearTwistRealizesAlt.qreg_block_wires_apply]
          exact congrArg rCore (Fin.ext (by dsimp; omega))
        · rintro ⟨a, h⟩
          have hv := congrArg Fin.val (rCore.wires.injective h)
          have ha := a.isLt
          dsimp [fWire, rElecAxis654, QRegister.slice, QRegister.slice_apply,
            NuclearTwistRealizesAlt.qreg_slice_wires,
            NuclearTwistRealizesAlt.qreg_whole_wires,
            NuclearTwistRealizesAlt.emb_trans_apply,
            NuclearTwistRealizesAlt.emb_refl_apply,
            NuclearTwistRealizesAlt.emb_mk_apply, QRegister.compose,
            QRegister.compose_apply, NuclearTwistRealizesAlt.qreg_compose_wires,
            NuclearTwistRealizesAlt.qreg_block_apply,
            NuclearTwistRealizesAlt.qreg_block_wires_apply] at hv
          omega
      simp only [hiff]
  have hfwd : DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace
      rCore rWork (uXor32Core mPayload) (dXor32All654 (Var := Var) rCore) :=
    DynCircuitExt.realizesEmbeddedUnitaryWithCleanWorkspace_circuit rCore rWork _ _ heval
  exact
    { fwd := hfwd
      inv := by
        rw [uXor32Core_inv]
        exact hfwd }
attribute [local irreducible] dXor32All654
def barrelActive {mPayload : ℕ} (swapOnSlot2 : Bool)
    (γ : BitAssignment (fullSysCoreWires mPayload)) : Bool := if swapOnSlot2 then decide (γ
    (wSlot2 (QRegExt.idReg _)) = 0 ∧ γ (wSlot1 (QRegExt.idReg _)) = 0) else decide (γ
    (wSlot2 (QRegExt.idReg _)) = 0 ∧ γ (wSlot1 (QRegExt.idReg _)) = 0 ∧ γ (wSlot0
    (QRegExt.idReg _)) = 1)
def barrelBitFn {mPayload : ℕ} (swapOnSlot2 : Bool) (hm : 22 ≤ mPayload)
    (γ : BitAssignment (fullSysCoreWires mPayload)) :
    BitAssignment (fullSysCoreWires mPayload) :=
  let idx := regVal (rAnchorIdx hm (QRegExt.idReg _)) γ
  if hcond : barrelActive swapOnSlot2 γ = true ∧ idx < 218 then
    fun k ↦
      if hk0 : k.val < 18 then
        γ ⟨18 * idx + k.val, by
          simp only [fullSysCoreWires, SpecsAux.SpecMirror.systemQubits,
            SpecsAux.SpecMirror.numElectrons, SpecsAux.SpecMirror.electronBits,
              SpecsAux.SpecMirror.projectileBits]
          omega⟩
      else if hk1 : 18 * idx ≤ k.val ∧ k.val < 18 * idx + 18 then
        γ ⟨k.val - 18 * idx, by
          simp only [fullSysCoreWires, SpecsAux.SpecMirror.systemQubits,
            SpecsAux.SpecMirror.numElectrons, SpecsAux.SpecMirror.electronBits,
              SpecsAux.SpecMirror.projectileBits]
          omega⟩
      else γ k
  else γ
theorem barrelBitFn_high_eq {mPayload : ℕ} (swapOnSlot2 : Bool) (hm : 22 ≤ mPayload)
    (γ : BitAssignment (fullSysCoreWires mPayload)) (k : Fin (fullSysCoreWires mPayload))
    (hk : 3924 ≤ k.val) : barrelBitFn swapOnSlot2 hm γ k = γ k := by
  unfold barrelBitFn
  by_cases hact : barrelActive swapOnSlot2 γ = true ∧ regVal (rAnchorIdx hm (QRegExt.idReg _)) γ <
    218
  · rw [dite_pos_eq hact]
    have hlt218 := hact.2
    have hn0 : ¬(k.val < 18) := by omega
    have hn1 : ¬(18 * regVal (rAnchorIdx hm (QRegExt.idReg _)) γ ≤ k.val ∧
        k.val < 18 * regVal (rAnchorIdx hm (QRegExt.idReg _)) γ + 18) := by omega
    rw [dite_neg_eq hn0, dite_neg_eq hn1]
  · rw [dite_neg_eq hact]
theorem barrelBitFn_involutive {mPayload : ℕ} (swapOnSlot2 : Bool) (hm : 22 ≤ mPayload) :
    Function.Involutive (barrelBitFn swapOnSlot2 hm) := fun γ ↦ by
  let γ' := barrelBitFn swapOnSlot2 hm γ
  have hhigh : ∀ (k : Fin (fullSysCoreWires mPayload)), 3924 ≤ k.val → γ' k = γ k :=
    barrelBitFn_high_eq swapOnSlot2 hm γ
  have hact_eq : barrelActive swapOnSlot2 γ' = barrelActive swapOnSlot2 γ := by
    unfold barrelActive
    have hs2 : γ' (wSlot2 (QRegExt.idReg _)) = γ (wSlot2 (QRegExt.idReg _)) :=
      hhigh _ (by simp [wSlot2])
    have hs1 : γ' (wSlot1 (QRegExt.idReg _)) = γ (wSlot1 (QRegExt.idReg _)) :=
      hhigh _ (by simp [wSlot1])
    have hs0 : γ' (wSlot0 (QRegExt.idReg _)) = γ (wSlot0 (QRegExt.idReg _)) :=
      hhigh _ (by simp [wSlot0])
    rw [hs2, hs1, hs0]
  have hidx_eq : regVal (rAnchorIdx hm (QRegExt.idReg _)) γ' =
    regVal (rAnchorIdx hm (QRegExt.idReg _)) γ :=
    regVal_congr (rAnchorIdx hm (QRegExt.idReg _)) fun j ↦
      hhigh _ (by simp [rAnchorIdx]; omega)
  funext k
  change barrelBitFn swapOnSlot2 hm γ' k = γ k
  set idx := regVal (rAnchorIdx hm (QRegExt.idReg _)) γ
  by_cases hcond : barrelActive swapOnSlot2 γ = true ∧ idx < 218
  · have hcond' : barrelActive swapOnSlot2 γ' = true ∧
        regVal (rAnchorIdx hm (QRegExt.idReg _)) γ' < 218 := by
      rw [hact_eq, hidx_eq]; exact hcond
    have hlhs : barrelBitFn swapOnSlot2 hm γ' k =
        (if hk0 : k.val < 18 then
          γ' ⟨18 * idx + k.val, by
            simp only [fullSysCoreWires, SpecsAux.SpecMirror.systemQubits,
              SpecsAux.SpecMirror.numElectrons, SpecsAux.SpecMirror.electronBits,
                SpecsAux.SpecMirror.projectileBits]
            omega⟩
        else if hk1 : 18 * idx ≤ k.val ∧ k.val < 18 * idx + 18 then
          γ' ⟨k.val - 18 * idx, by
            simp only [fullSysCoreWires, SpecsAux.SpecMirror.systemQubits,
              SpecsAux.SpecMirror.numElectrons, SpecsAux.SpecMirror.electronBits,
                SpecsAux.SpecMirror.projectileBits]
            omega⟩
        else γ' k) := by
      unfold barrelBitFn
      rw [dite_pos_eq hcond']
      simp only [hidx_eq]
    rw [hlhs]
    have hlt218 : idx < 218 := hcond.2
    by_cases hidx0 : idx = 0
    · dsimp only [γ']
      unfold barrelBitFn
      rw [dite_pos_eq hcond]
      by_cases hk18 : k.val < 18
      · rw [dite_pos_eq hk18]
        have h18k : 18 * idx + k.val < 18 := by omega
        (try dsimp only)
        rw [dite_pos_eq h18k]
        exact congrArg γ (Fin.ext (by dsimp; omega))
      · have hnot1 : ¬(18 * idx ≤ k.val ∧ k.val < 18 * idx + 18) := by omega
        rw[dite_neg_eq hk18, dite_neg_eq hnot1, dite_neg_eq hk18, dite_neg_eq hnot1]
    · have hge1 : 1 ≤ idx := by omega
      dsimp only [γ']
      unfold barrelBitFn
      rw [dite_pos_eq hcond]
      by_cases hk0 : k.val < 18
      · rw [dite_pos_eq hk0]
        have hn0 : ¬(18 * idx + k.val < 18) := by omega
        have hy1 : 18 * idx ≤ 18 * idx + k.val ∧ 18 * idx + k.val < 18 * idx + 18 := by omega
        (try dsimp only)
        rw [dite_neg_eq hn0, dite_pos_eq hy1]
        exact congrArg γ (Fin.ext (by dsimp; omega))
      · rw [dite_neg_eq hk0]
        by_cases hk1 : 18 * idx ≤ k.val ∧ k.val < 18 * idx + 18
        · rw [dite_pos_eq hk1]
          have hy0 : k.val - 18 * idx < 18 := by omega
          (try dsimp only)
          rw [dite_pos_eq hy0]
          exact congrArg γ (Fin.ext (by dsimp; omega))
        · rw[dite_neg_eq hk1, dite_neg_eq hk0, dite_neg_eq hk1]
  · have hcond' : ¬(barrelActive swapOnSlot2 γ' = true ∧
        regVal (rAnchorIdx hm (QRegExt.idReg _)) γ' < 218) := by
      rw [hact_eq, hidx_eq]; exact hcond
    unfold barrelBitFn
    rw [dite_neg_eq hcond']
    dsimp only [γ']
    unfold barrelBitFn
    rw [dite_neg_eq hcond]
noncomputable def barrelCorePerm {mPayload : ℕ} (swapOnSlot2 : Bool) (hm : 22 ≤ mPayload) :
    Equiv.Perm (Fin (2 ^ (fullSysCoreWires mPayload))) :=
    (basisBitsEquiv (fullSysCoreWires mPayload)).trans ((Equiv.ofBijective (barrelBitFn
    swapOnSlot2 hm) (barrelBitFn_involutive swapOnSlot2 hm).bijective).trans (basisBitsEquiv
    (fullSysCoreWires mPayload)).symm)
noncomputable def uBarrelCore {mPayload : ℕ} (swapOnSlot2 : Bool) (hm : 22 ≤ mPayload) :
    Unitary (2 ^ (fullSysCoreWires mPayload)) :=
  Operator.permutationUnitary (barrelCorePerm swapOnSlot2 hm)
end BarrelAndXor32Core
section Section5ClassicalHelpers
theorem unitary_list_prod_coe {D : ℕ} (L : List (Unitary D)) :
    L.prod.1 = (L.map Subtype.val).prod := by
  induction L with
  | nil => rfl
  | cons hd tl ih =>
      rw [List.prod_cons, Submonoid.coe_mul, List.map_cons, List.prod_cons, ih]
theorem list_prod_diagonal {α : Type*} [Fintype α] [DecidableEq α] {β : Type*} (L : List β)
    (g : β → α → ℂ) : (L.map fun b ↦ Matrix.diagonal (g b)).prod = Matrix.diagonal
    (fun x ↦ (L.map fun b ↦ g b x).prod) := by
  induction L with
  | nil => simp only [List.map_nil, List.prod_nil, Matrix.diagonal_one]
  | cons hd tl ih =>
      simp only [List.map_cons, List.prod_cons, ih, Matrix.diagonal_mul_diagonal]
theorem sysNucDiag48_coe_eq_diagonal (c : Configuration) (l : Fin 216) :
    (sysNucDiag48 c l).1 = Matrix.diagonal (fun x : Fin (2 ^ systemQubits) ↦
      ∏ e : Fin numElectrons,
        oneElectronPhase48 c l (shiftedMom3D (elecOffsetGridEquiv18 ((rEl_sp e).extractIndex x))))
          := by
  unfold sysNucDiag48
  have hmap : (List.ofFn fun e : Fin numElectrons ↦ (rEl_sp e).embedUnitary (oneElecNucDiag48
      c l)).map Subtype.val = (List.ofFn (id : Fin numElectrons → Fin numElectrons)).map (fun
      e : Fin numElectrons ↦ Matrix.diagonal (fun x : Fin (2 ^ systemQubits) ↦
      oneElectronPhase48 c l (shiftedMom3D (elecOffsetGridEquiv18 ((rEl_sp e).extractIndex
      x))))) := by
    rw [List.map_ofFn, List.map_ofFn]
    congr 1; funext e
    exact QRegister.embedMatrix_diagonal (rEl_sp e) _
  rw [unitary_list_prod_coe, hmap, list_prod_diagonal]
  apply congrArg Matrix.diagonal; funext x
  rw [List.map_ofFn, List.prod_ofFn]
  rfl
theorem prod_turnPow2 {ι : Type*} (s : Finset ι) (B : ℕ) (f : ι → ℤ) :
    (∏ i ∈ s, turnPow2 B (f i)) = turnPow2 B (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.prod_empty, Finset.sum_empty, turnPow2_zero]
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha, turnPow2_add, ih]
theorem star_turnPow2 (B : ℕ) (k : ℤ) : star (turnPow2 B k) = turnPow2 B (-k) := by
  have h1 : star (turnPow2 B k) * turnPow2 B k = 1 := star_turnPow2_mul_self B k
  have h2 : turnPow2 B k * turnPow2 B (-k) = 1 := by
    rw [← turnPow2_add, add_neg_cancel, turnPow2_zero]
  calc star (turnPow2 B k)
      = star (turnPow2 B k) * (turnPow2 B k * turnPow2 B (-k)) := by rw [h2, mul_one]
    _ = (star (turnPow2 B k) * turnPow2 B k) * turnPow2 B (-k) := by ring
    _ = turnPow2 B (-k) := by rw [h1, one_mul]
noncomputable def slot2GlobalPhase (c : Configuration) (l : Fin 216) : ℂ :=
  dyadicTurn 48 ((218 * 32 : ℤ) * ∑ w : Fin 3, (nuclearM48 c l w : ℤ))
theorem star_slot2GlobalPhase_mul_self (c : Configuration) (l : Fin 216) : star
    (slot2GlobalPhase c l) * slot2GlobalPhase c l = 1 := star_turnPow2_mul_self 48 _
theorem slot2_unsigned_sum_eq_globalPhase_mul_star_prod (c : Configuration) (l : Fin 216)
    (u : Fin numElectrons → NyqGrid3D64) : dyadicTurn 48 (∑ w : Fin 3, (∑ e : Fin
    numElectrons, ((u e w).val : ℤ)) * (nuclearM48 c l w : ℤ)) = slot2GlobalPhase c l * star
    (∏ e : Fin numElectrons, oneElectronPhase48 c l (shiftedMom3D (u e))) := by
  unfold slot2GlobalPhase oneElectronPhase48 dyadicTurn
  rw [prod_turnPow2, star_turnPow2, ← turnPow2_add]
  apply congrArg (turnPow2 48)
  have hexp : ∑ w : Fin 3, (∑ e : Fin numElectrons, ((u e w).val : ℤ)) *
      (nuclearM48 c l w : ℤ) = (218 * 32 : ℤ) * (∑ w : Fin 3, (nuclearM48 c l w : ℤ)) + -(∑ e
      : Fin numElectrons, -(∑ w : Fin 3, (((u e w).val : ℤ) - 32) * (nuclearM48 c l w : ℤ)))
      := by
    have hinner : -(∑ e : Fin numElectrons, -(∑ w : Fin 3, (((u e w).val : ℤ) - 32) *
        (nuclearM48 c l w : ℤ))) = ∑ w : Fin 3, ((∑ e : Fin numElectrons, ((u e w).val : ℤ)) *
        (nuclearM48 c l w : ℤ) - (218 * 32 : ℤ) * (nuclearM48 c l w : ℤ)) := by
      rw [← Finset.sum_neg_distrib]
      simp only [neg_neg]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun w _ ↦ ?_
      have hw : (∑ e : Fin numElectrons, (((u e w).val : ℤ) - 32) * (nuclearM48 c l w : ℤ)) =
          (∑ e : Fin numElectrons, ((u e w).val : ℤ)) * (nuclearM48 c l w : ℤ) -
          (∑ _e : Fin numElectrons, (32 : ℤ)) * (nuclearM48 c l w : ℤ) := by
        rw [Finset.sum_mul, Finset.sum_mul, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun e _ ↦ by ring
      rw [hw, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      dsimp [SpecsAux.SpecMirror.numElectrons]
    rw [hinner, Finset.sum_sub_distrib, Finset.mul_sum]
    ring
  simpa only [shiftedMom3D, shiftedFin64ToInt] using hexp
theorem slot2_rawSumDiag_eq_globalPhase_smul_diag {α : Type*} [DecidableEq α]
    (c : Configuration) (l : Fin 216) (uOf : α → Fin numElectrons → NyqGrid3D64) :
    Matrix.diagonal (fun x : α ↦ dyadicTurn 48 (∑ w : Fin 3, (∑ e : Fin numElectrons, ((uOf x
    e w).val : ℤ)) * (nuclearM48 c l w : ℤ))) = slot2GlobalPhase c l • (Matrix.diagonal (fun x
    : α ↦ ∏ e : Fin numElectrons, oneElectronPhase48 c l (shiftedMom3D (uOf x e))))ᴴ := by
  rw [Matrix.diagonal_conjTranspose]
  ext x y
  by_cases hxy : x = y
  · subst hxy
    simp only [Matrix.diagonal_apply_eq, Matrix.smul_apply, smul_eq_mul, Pi.star_apply]
    exact slot2_unsigned_sum_eq_globalPhase_mul_star_prod c l (uOf x)
  · simp only [Matrix.diagonal_apply_ne _ hxy, Matrix.smul_apply, smul_zero]
theorem slot2_offsetDiag_eq_smul_sysNucDiag48_conjTranspose (c : Configuration) (l : Fin 216)
    : Matrix.diagonal (fun x : Fin (2 ^ systemQubits) ↦ dyadicTurn 48 (∑ w : Fin 3, (∑ e : Fin
    numElectrons, ((elecOffsetGridEquiv18 ((rEl_sp e).extractIndex x) w).val : ℤ)) *
    (nuclearM48 c l w : ℤ))) = slot2GlobalPhase c l • (sysNucDiag48 c l).1ᴴ := by
  rw [sysNucDiag48_coe_eq_diagonal]
  exact slot2_rawSumDiag_eq_globalPhase_smul_diag c l
    (fun x e ↦ elecOffsetGridEquiv18 ((rEl_sp e).extractIndex x))
theorem comm_of_mulVec_basisKet_preserves {N : ℕ} [NeZero (2 ^ N)] (M P : Operator (2 ^ N))
    (φ p : BitAssignment N → ℂ) (permFn : BitAssignment N → BitAssignment N) (hM : ∀ β :
    BitAssignment N, M.mulVec (basisKet β) = φ β • basisKet (permFn β)) (hP : ∀ β :
    BitAssignment N, P.mulVec (basisKet β) = p β • basisKet β)
    (hpres : ∀ β : BitAssignment N, p (permFn β) = p β) : M * P = P * M := by
  apply matrix_ext_basisKet
  intro β
  calc (M * P).mulVec (basisKet β)
      = M.mulVec (P.mulVec (basisKet β)) := (Matrix.mulVec_mulVec _ _ _).symm
    _ = (φ β * p β) • basisKet (permFn β) := by
          rw [hP β, Matrix.mulVec_smul, hM β, smul_smul, mul_comm]
    _ = P.mulVec (M.mulVec (basisKet β)) := by
          rw [hM β, Matrix.mulVec_smul, hP (permFn β), hpres β, smul_smul]
    _ = (P * M).mulVec (basisKet β) := Matrix.mulVec_mulVec _ _ _
theorem comm_diagonal_on_wires_of_preserves {N : ℕ} [NeZero (2 ^ N)] (M : Operator (2 ^ N))
    (φ : BitAssignment N → ℂ) (permFn : BitAssignment N → BitAssignment N)
    (g : BitAssignment N → ℂ) (hM : ∀ β : BitAssignment N, M.mulVec (basisKet β) = φ β •
    basisKet (permFn β)) (hpres : ∀ β : BitAssignment N, g (permFn β) = g β) : M *
    Matrix.diagonal (fun x : Fin (2 ^ N) ↦ g (basisBits N x)) = Matrix.diagonal
    (fun x : Fin (2 ^ N) ↦ g (basisBits N x)) * M :=
  comm_of_mulVec_basisKet_preserves M
    (Matrix.diagonal (fun x : Fin (2 ^ N) ↦ g (basisBits N x)))
    φ g permFn hM
    (fun β ↦ by
      ext y
      rw [Matrix.mulVec_diagonal]
      by_cases hy : y = (basisBitsEquiv N).symm β
      · subst hy
        simp only [basisBits_symm_eq, basisKet, basisState, Pi.single_eq_same,
          Pi.smul_apply, smul_eq_mul, mul_one]
      · simp only [basisKet, basisState, Pi.single_eq_of_ne hy, Pi.smul_apply, smul_eq_mul,
        mul_zero])
    hpres
lemma fin2_eq_iff_basisBits1 (u b : Fin 2) :
    (u = b) ↔ (basisBits 1 u 0 = (b.val : ZMod 2)) := by
  fin_cases u <;> fin_cases b <;> simp [-Nat.reducePow, basisBits_eq_testBit]
theorem singleton_basisOutcomeProjector_eq_diagonal {N : ℕ} (q : Wire N) (b : Fin 2) :
    (QRegister.singleton q).basisOutcomeProjector b = Matrix.diagonal (fun x : Fin (2 ^ N) ↦
    if basisBits N x q = (b.val : ZMod 2) then 1 else 0) := by
  rw [(QRegister.singleton q).basisOutcomeProjector_eq_diagonal b]
  congr 1; funext x
  have hb0 : basisBits 1 ((QRegister.singleton q).extractIndex x) 0 = basisBits N x q :=
    QRegister.basisBits_extractIndex (QRegister.singleton q) x 0
  rw [if_congr (fin2_eq_iff_basisBits1 _ b) rfl rfl, hb0]
theorem comm_singleton_basisOutcomeProjector_of_preserves {N : ℕ} [NeZero (2 ^ N)]
    (M : Operator (2 ^ N)) (q : Wire N) (b : Fin 2)
    (φ : BitAssignment N → ℂ) (permFn : BitAssignment N → BitAssignment N)
    (hM : ∀ β : BitAssignment N, M.mulVec (basisKet β) = φ β • basisKet (permFn β))
    (hpres : ∀ β : BitAssignment N, permFn β q = β q) :
    M * (QRegister.singleton q).basisOutcomeProjector b =
      (QRegister.singleton q).basisOutcomeProjector b * M := by
  rw [singleton_basisOutcomeProjector_eq_diagonal]
  exact comm_diagonal_on_wires_of_preserves M φ permFn
    (fun β ↦ if β q = (b.val : ZMod 2) then 1 else 0) hM
    (fun β ↦ by rw [hpres β])
end Section5ClassicalHelpers
section TwistWorkspacePartition
variable {n : ℕ}
theorem bitsVal_eq_of_testBit :
    ∀ (B val : ℕ), val < 2 ^ B →
      bitsVal (fun j : Fin B ↦ if val.testBit j.val then (1 : ZMod 2) else 0) = val
  | 0, val, hlt => by
      have hv0 : val = 0 := by omega
      subst hv0
      simp only [bitsVal, Finset.univ_eq_empty, Finset.sum_empty]
  | B + 1, val, hlt => by
      unfold bitsVal
      rw [Fin.sum_univ_succ]
      have h0 : ((if val.testBit 0 then (1 : ZMod 2) else 0)).val * 2 ^ 0 = val % 2 := by
        rw [Nat.testBit_zero]
        by_cases hmod : val % 2 = 1
        · simp only [hmod, _root_.pow_zero, mul_one]; rfl
        · have hmod0 : val % 2 = 0 := by omega
          simp [hmod0]
      have htail : (∑ i : Fin B, ((if val.testBit (Fin.succ i).val then (1 : ZMod 2) else
          0)).val * 2 ^ (Fin.succ i).val) = 2 * bitsVal (fun i : Fin B ↦ if (val / 2).testBit
          i.val then (1 : ZMod 2) else 0) := by
        unfold bitsVal
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        have htb : val.testBit (i.val + 1) = (val / 2).testBit i.val := by
          rw [Nat.testBit_add_one]
        simp only [Fin.val_succ, htb, pow_succ]
        ring
      have hdiv_lt : val / 2 < 2 ^ B := by rw [pow_succ] at hlt; omega
      (try dsimp only)
      rw [Fin.val_zero, h0, htail, bitsVal_eq_of_testBit B (val / 2) hdiv_lt]
      omega
end TwistWorkspacePartition
section Slot4Realizes
def slot4TotalPhaseExp {mPayload : ℕ} (hm : 22 ≤ mPayload)
    (γ : BitAssignment (fullSysCoreWires mPayload)) : ℤ := if γ (wSlot2 (QRegExt.idReg _))
    = 0 ∧ γ (wSlot1 (QRegExt.idReg _)) = 0 ∧ γ (wSlot0 (QRegExt.idReg _)) = 1 then ∑ w :
    Fin 3, (2 ^ 41 : ℤ) * ((((γ (rCosetB1 hm (QRegExt.idReg _) w)).val : ℤ) - ((γ (rCosetB0
    hm (QRegExt.idReg _) w)).val : ℤ)) * (regVal (rElecSlotAxis (QRegExt.idReg _) 0 w) γ :
    ℤ)) else 0
noncomputable def uSlot4KickCore {mPayload : ℕ} (hm : 22 ≤ mPayload) :
    Unitary (2 ^ (fullSysCoreWires mPayload)) :=
  dyadicDiagUnitary (fullSysCoreWires mPayload) 48 (slot4TotalPhaseExp hm)
theorem dyadicDiagUnitary_zero (k B : ℕ) [NeZero (2 ^ k)] :
    dyadicDiagUnitary k B (fun _ ↦ 0) = 1 := by
  apply Subtype.ext; apply matrix_ext_basisKet; intro β
  have h0 := embedUnitary_dyadicDiagUnitary_mulVec_basisKet (QRegExt.idReg k) B (fun _ ↦ 0) β
  simp only [embedUnitary_idReg_eq, DyadicQft64.dyadicTurn_zero, one_smul] at h0
  rw [h0, OneMemClass.coe_one, Matrix.one_mulVec]
end Slot4Realizes
section Slot2Realizes
def coin0Active {mPayload : ℕ} (γ : BitAssignment (fullSysCoreWires mPayload)) : Bool :=
  decide (γ (wSlot2 (QRegExt.idReg _)) = 0 ∧ γ (wSlot1 (QRegExt.idReg _)) = 0 ∧
    γ (wSlot0 (QRegExt.idReg _)) = 0)
noncomputable def slot2M48Val {mPayload : ℕ} (c : Configuration) (hm : 22 ≤ mPayload)
    (w : Fin 3) (γ : BitAssignment (fullSysCoreWires mPayload)) : ℕ := if h : coin0Active γ =
    true ∧ regVal (rNucIdx hm (QRegExt.idReg _)) γ < 216 then nuclearM48 c
    ⟨regVal (rNucIdx hm (QRegExt.idReg _)) γ, h.2⟩ w else 0
def slot2AxisSum {mPayload : ℕ} (w : Fin 3) (γ : BitAssignment (fullSysCoreWires mPayload)) :
    ℕ := ∑ e : Fin numElectrons, regVal (rElecSlotAxis (QRegExt.idReg _) e w) γ
theorem slot2AxisSum_lt {mPayload : ℕ} (w : Fin 3)
    (γ : BitAssignment (fullSysCoreWires mPayload)) : slot2AxisSum w γ < 2 ^ 14 := by
  unfold slot2AxisSum
  have heach : ∀ e : Fin numElectrons, regVal (rElecSlotAxis (QRegExt.idReg _) e w) γ ≤ 63 :=
    fun e ↦ by
    have hlt := regVal_lt_two_pow (rElecSlotAxis (QRegExt.idReg _) e w) γ
    omega
  calc
    (∑ e : Fin numElectrons, regVal (rElecSlotAxis (QRegExt.idReg _) e w) γ)
      ≤ ∑ _e : Fin numElectrons, 63 := Finset.sum_le_sum fun e _ ↦ heach e
    _ = 218 * 63 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        dsimp [SpecsAux.SpecMirror.numElectrons]
    _ < 2 ^ 14 := by norm_num
noncomputable def slot2AxisDelta {mPayload : ℕ} (c : Configuration) (hm : 22 ≤ mPayload) (w : Fin 3)
    (γ : BitAssignment (fullSysCoreWires mPayload)) : ℕ :=
  slot2AxisSum w γ * slot2M48Val c hm w γ
noncomputable def slot2TotalPhaseExp {mPayload : ℕ} (c : Configuration) (hm : 22 ≤ mPayload)
    (γ : BitAssignment (fullSysCoreWires mPayload)) : ℤ :=
  ∑ w : Fin 3, (slot2AxisDelta c hm w γ : ℤ)
noncomputable def uSlot2KickCore {mPayload : ℕ} (c : Configuration) (hm : 22 ≤ mPayload) :
    Unitary (2 ^ (fullSysCoreWires mPayload)) :=
  dyadicDiagUnitary (fullSysCoreWires mPayload) 48 (slot2TotalPhaseExp c hm)
end Slot2Realizes
section MasterTwistBundle
noncomputable def uTwistParam {mPayload : ℕ} (swapOnSlot2 : Bool) (hm : 22 ≤ mPayload)
    (c : Configuration) : Unitary (2 ^ (fullSysCoreWires mPayload)) := uSlot2KickCore c hm *
    (uSlot4KickCore hm * (uXor32Core mPayload * uBarrelCore swapOnSlot2 hm))
noncomputable def twistCorePhase {mPayload : ℕ} (swapOnSlot2 : Bool) (hm : 22 ≤ mPayload)
    (c : Configuration) (γ : BitAssignment (fullSysCoreWires mPayload)) : ℂ :=
  let γ' := xor32BitFn mPayload (barrelBitFn swapOnSlot2 hm γ)
  dyadicTurn 48 (slot4TotalPhaseExp hm γ' + slot2TotalPhaseExp c hm γ')
def twistCorePermFn {mPayload : ℕ} (swapOnSlot2 : Bool) (hm : 22 ≤ mPayload)
    (γ : BitAssignment (fullSysCoreWires mPayload)) : BitAssignment
    (fullSysCoreWires mPayload) := xor32BitFn mPayload (barrelBitFn swapOnSlot2 hm γ)
theorem twistCorePermFn_high_eq {mPayload : ℕ} (swapOnSlot2 : Bool) (hm : 22 ≤ mPayload)
    (γ : BitAssignment (fullSysCoreWires mPayload)) (q : Fin (fullSysCoreWires mPayload))
    (hq : 3924 ≤ q.val) : twistCorePermFn swapOnSlot2 hm γ q = γ q := by
  unfold twistCorePermFn xor32BitFn
  have hn : ¬(q.val < 3924 ∧ q.val % 6 = 5) := by omega
  simp only [hn, ↓reduceIte, barrelBitFn_high_eq swapOnSlot2 hm γ q hq]
theorem uTwistParam_mulVec_basisKet {mPayload n : ℕ} [NeZero (2 ^ n)] (swapOnSlot2 : Bool)
    (hm : 22 ≤ mPayload) (c : Configuration)
    (rCore : QRegister (fullSysCoreWires mPayload) n) (β : BitAssignment n) :
    (rCore.embedUnitary (uTwistParam swapOnSlot2 hm c)).1.mulVec (basisKet β) = twistCorePhase
    swapOnSlot2 hm c (fun q ↦ β (rCore q)) • basisKet (fun z ↦ if hz : z ∈ rCore.image then
    twistCorePermFn swapOnSlot2 hm (fun q ↦ β (rCore q)) (Classical.choose
    ((QRegister.mem_image rCore z).mp hz)) else β z) := by
  let kC := fullSysCoreWires mPayload
  let γ := fun q ↦ β (rCore q)
  have huPerm : uXor32Core mPayload * uBarrelCore swapOnSlot2 hm =
      Operator.permutationUnitary (xor32CorePerm mPayload * barrelCorePerm swapOnSlot2 hm) :=
    (OperatorExt.permutationUnitary_mul _ _).symm
  let β_p : BitAssignment n := fun z ↦ if hz : z ∈ rCore.image then twistCorePermFn
      swapOnSlot2 hm γ (Classical.choose ((QRegister.mem_image rCore z).mp hz)) else β z
  have hβp_core : (fun q ↦ β_p (rCore q)) = twistCorePermFn swapOnSlot2 hm γ := funext fun q ↦ by
    have hm_q : rCore q ∈ rCore.image := (QRegister.mem_image rCore _).mpr ⟨q, rfl⟩
    have hch : Classical.choose ((QRegister.mem_image rCore (rCore q)).mp hm_q) = q :=
      rCore.wires.injective (Classical.choose_spec ((QRegister.mem_image rCore (rCore q)).mp hm_q))
    simp only [β_p, hm_q, ↓reduceDIte, hch]
  have hevPerm : (rCore.embedUnitary (uXor32Core mPayload * uBarrelCore swapOnSlot2 hm)).1.mulVec
      (basisKet β) = basisKet β_p := by
    rw [huPerm]
    refine embedUnitary_perm_mulVec_basisKet rCore _ β β_p (fun q ↦ ?_)
      (fun z hz ↦ by dsimp only [β_p]; simp only [hz, ↓reduceDIte])
    rw [congrFun hβp_core q]
    change twistCorePermFn swapOnSlot2 hm γ q = basisBits kC (xor32CorePerm mPayload
      (barrelCorePerm swapOnSlot2 hm ((basisBitsEquiv kC).symm γ))) q
    have hbar_symm : barrelCorePerm swapOnSlot2 hm ((basisBitsEquiv kC).symm γ) =
        (basisBitsEquiv kC).symm (barrelBitFn swapOnSlot2 hm γ) := by
      apply (basisBitsEquiv kC).injective
      rw [(basisBitsEquiv kC).apply_symm_apply]
      funext q'
      exact basisBits_perm_ofBijective (barrelBitFn swapOnSlot2 hm)
        (barrelBitFn_involutive swapOnSlot2 hm).bijective γ q'
    rw [hbar_symm, xor32CorePerm]
    exact (basisBits_perm_ofBijective (xor32BitFn mPayload)
      (xor32BitFn_involutive mPayload).bijective (barrelBitFn swapOnSlot2 hm γ) q).symm
  have hDiag : uSlot2KickCore c hm * uSlot4KickCore hm =
      dyadicDiagUnitary kC 48 (fun δ ↦ slot4TotalPhaseExp hm δ + slot2TotalPhaseExp c hm δ) :=
    dyadicDiagUnitary_mul kC 48 (slot4TotalPhaseExp hm) (slot2TotalPhaseExp c hm)
  have huEq : uTwistParam swapOnSlot2 hm c =
      dyadicDiagUnitary kC 48 (fun δ ↦ slot4TotalPhaseExp hm δ + slot2TotalPhaseExp c hm δ) *
        (uXor32Core mPayload * uBarrelCore swapOnSlot2 hm) := by
    rw [← hDiag, mul_assoc]; rfl
  rw [huEq, QRegister.embedUnitary_mul, Submonoid.coe_mul, ← Matrix.mulVec_mulVec, hevPerm,
    embedUnitary_dyadicDiagUnitary_mulVec_basisKet, hβp_core]
  rfl
theorem uTwistParam_comm_highReg_proj {mPayload kSub n : ℕ} [NeZero (2 ^ n)]
    (swapOnSlot2 : Bool) (hm : 22 ≤ mPayload) (c : Configuration)
    (rCore : QRegister (fullSysCoreWires mPayload) n) (rSub : QRegister kSub n)
    (hDisjElec : (rElecCore rCore).DisjointWires rSub) (v : Fin (2 ^ kSub)) :
    (rCore.embedUnitary (uTwistParam swapOnSlot2 hm c)).1 * rSub.basisOutcomeProjector v =
    rSub.basisOutcomeProjector v * (rCore.embedUnitary (uTwistParam swapOnSlot2 hm c)).1 := by
  have hproj_diag : rSub.basisOutcomeProjector v = Matrix.diagonal (fun x : Fin (2 ^ n) ↦ if
      (basisBitsEquiv kSub).symm (fun j ↦ basisBits n x (rSub j)) = v then 1 else 0) :=
      rSub.basisOutcomeProjector_eq_diagonal v
  rw [hproj_diag]
  exact comm_diagonal_on_wires_of_preserves
    (rCore.embedUnitary (uTwistParam swapOnSlot2 hm c)).1
    (fun β ↦ twistCorePhase swapOnSlot2 hm c (fun q' ↦ β (rCore q')))
    (fun β z ↦
      if hz : z ∈ rCore.image then
        twistCorePermFn swapOnSlot2 hm (fun q' ↦ β (rCore q'))
          (Classical.choose ((QRegister.mem_image rCore z).mp hz))
      else β z)
    (fun β ↦ if (basisBitsEquiv kSub).symm (fun j ↦ β (rSub j)) = v then 1 else 0)
    (uTwistParam_mulVec_basisKet swapOnSlot2 hm c rCore)
    (fun β ↦ by
      have hpres : (fun j : Fin kSub ↦
          if hz : rSub j ∈ rCore.image then
            twistCorePermFn swapOnSlot2 hm (fun q' ↦ β (rCore q'))
              (Classical.choose ((QRegister.mem_image rCore (rSub j)).mp hz))
          else β (rSub j)) = (fun j ↦ β (rSub j)) := funext fun j ↦ by
        by_cases hz : rSub j ∈ rCore.image
        · rw [dite_pos_eq hz]
          set q := Classical.choose ((QRegister.mem_image rCore (rSub j)).mp hz)
          have hq_eq : rCore q = rSub j :=
            Classical.choose_spec ((QRegister.mem_image rCore (rSub j)).mp hz)
          have hq3924 : 3924 ≤ q.val := Nat.not_lt.mp fun hlt ↦
            QRegister.DisjointWires.ne hDisjElec ⟨q.val, hlt⟩ j
              ((congrArg rCore (Fin.ext (by dsimp [rElecCore, QRegister.slice,
                QRegister.slice_apply, NuclearTwistRealizesAlt.qreg_slice_wires,
                NuclearTwistRealizesAlt.qreg_whole_wires,
                NuclearTwistRealizesAlt.emb_trans_apply,
                NuclearTwistRealizesAlt.emb_refl_apply,
                NuclearTwistRealizesAlt.emb_mk_apply,
                NuclearTwistRealizesAlt.qreg_block_apply,
                NuclearTwistRealizesAlt.qreg_block_wires_apply]; omega))).trans hq_eq)
          exact (twistCorePermFn_high_eq swapOnSlot2 hm (fun q' ↦ β (rCore q')) q hq3924).trans
            (congrArg β hq_eq)
        · rw [dite_neg_eq hz]
      rw [hpres])
end MasterTwistBundle
section FullSysBridgeExport
theorem intertwinesLocalCat_to_fullSys {kAct mCat : ℕ}
    {U_cat : Unitary (2 ^ mCat)} {W_cat : Unitary (2 ^ (kAct + mCat))} {U_eff : Unitary (2 ^ kAct)}
    (h : IntertwinesLocalCat U_cat W_cat U_eff) :
    FullSysCatSegmentBridge.IntertwinesLocalCat U_cat W_cat U_eff :=
  ⟨h.1, h.2.1, h.2.2⟩
end FullSysBridgeExport
end NuclearTwistRealizes
end
end ModNuclearTwistRealizes

section ModNuclearTwistMulKickAndBridge288
@[expose] public section
namespace NuclearTwistMulKickAndBridge288Alt
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
end NuclearTwistMulKickAndBridge288Alt
namespace NuclearTwistMulKickAndBridge288
open Operator QProg Matrix HermitianMat Real SpecsAux
open SpecsAux.SpecMirror
open DyadicQft64 hiding dyadicTurn phaseGradKet
open DyadicQft64Engine
open SpecsAux.PhaseGradCatalystCore
open NuclearTwistAndXor654Concrete
open NuclearTwistRealizes
open PosMomSelectSandwich (slotBitProj)
open scoped Matrix BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator Circuit.Notation
section GenericAndCopyBank
variable {Var : Type} {n : ℕ}
theorem restrictAssertionToZeroAncilla_eq_of_subset {kSub kBig : ℕ}
    {A B : CQAssertionCompat Var (2 ^ n)} {rSub : QRegister kSub n} {rBig : QRegister kBig n}
    (hSub : rSub.image ⊆ rBig.image)
    (hEq : CQAssertion.restrictToZeroAncilla A rSub = CQAssertion.restrictToZeroAncilla B rSub) :
    CQAssertion.restrictToZeroAncilla A rBig = CQAssertion.restrictToZeroAncilla B rBig := by
  funext σ
  apply Subtype.ext
  have h12 : rBig.basisOutcomeProjector 0 * rSub.basisOutcomeProjector 0 =
      rBig.basisOutcomeProjector 0 :=
    basisOutcomeProjector_zero_mul_of_image_subset rBig rSub hSub
  have hσ : (CQAssertion.restrictToZeroAncilla A rSub σ).1 =
      (CQAssertion.restrictToZeroAncilla B rSub σ).1 := congrArg Subtype.val (congrFun hEq σ)
  simp only [CQAssertion.restrictToZeroAncilla_coe] at hσ ⊢
  rw [← h12, ← conj_conj, hσ, conj_conj]
theorem restrictAssertionToZeroAncilla_eq_of_image_eq {k₁ k₂ : ℕ}
    {A B : CQAssertionCompat Var (2 ^ n)} {r₁ : QRegister k₁ n} {r₂ : QRegister k₂ n}
    (hImg : r₁.image = r₂.image)
    (hEq : CQAssertion.restrictToZeroAncilla A r₁ = CQAssertion.restrictToZeroAncilla B r₁) :
    CQAssertion.restrictToZeroAncilla A r₂ = CQAssertion.restrictToZeroAncilla B r₂ :=
  restrictAssertionToZeroAncilla_eq_of_subset (le_of_eq hImg) hEq
theorem support_CNOT_sub {S : Finset (Wire n)} {a b : Wire n} {hab : a ≠ b}
    (ha : a ∈ S) (hb : b ∈ S) : (Circuit.CNOT a b hab).support ⊆ S := fun _ hz ↦ by
  simp only [Circuit.support_cnot, Finset.mem_insert, Finset.mem_singleton] at hz
  rcases hz with rfl | rfl <;> assumption
end GenericAndCopyBank
section HoistedTwistRestExports
noncomputable def uTwistRest {mPayload : ℕ} (hm : 22 ≤ mPayload) (c : Configuration) :
    Unitary (2 ^ (fullSysCoreWires mPayload)) :=
  uSlot2KickCore c hm * (uSlot4KickCore hm * uXor32Core mPayload)
theorem count_dyn_seq {Var : Type} {n a : ℕ} (g : PrimitiveGate a)
    (d₁ d₂ : DynamicCircuit Var n) : (d₁.seq d₂).count g = d₁.count g + d₂.count g := rfl
private lemma lemHexAux {mPayload n : ℕ} (rCore : QRegister (fullSysCoreWires mPayload) n) :
    (parallelBit5FlipAxes (rElecAxis654 rCore)).support ⊆ (rElecCore rCore).image := by
  unfold parallelBit5FlipAxes
  refine Circuit.support_sequence_subset fun g hg ↦ ?_
  obtain ⟨a, rfl⟩ := List.mem_ofFn.mp hg
  exact support_X_sub ((QRegister.mem_image (rElecCore rCore) _).mpr
    ⟨⟨6 * a.val + 5, by have := a.isLt; omega⟩,
      congrArg rCore (Fin.ext (by
        dsimp [rElecAxis654, rElecCore, QRegister.slice, QRegister.slice_apply,
          NuclearTwistMulKickAndBridge288Alt.qreg_slice_wires,
          NuclearTwistMulKickAndBridge288Alt.qreg_whole_wires,
          NuclearTwistMulKickAndBridge288Alt.emb_trans_apply,
          NuclearTwistMulKickAndBridge288Alt.emb_refl_apply,
          NuclearTwistMulKickAndBridge288Alt.emb_mk_apply, QRegister.compose,
          QRegister.compose_apply, NuclearTwistMulKickAndBridge288Alt.qreg_compose_wires,
          NuclearTwistMulKickAndBridge288Alt.qreg_block_apply,
          NuclearTwistMulKickAndBridge288Alt.qreg_block_wires_apply]
        omega))⟩)
private lemma lemHex353 {mPayload n : ℕ} (rCore : QRegister (fullSysCoreWires mPayload) n) :
    (parallelBit5FlipAxes (rElecAxis654 rCore)).eval = rCore.embedUnitary
    (uXor32Core mPayload) := by
  let fWire : Fin 654 → Wire n := fun a ↦ rElecAxis654 rCore a 5
  have hinj : Function.Injective fWire := by
    intro a₁ a₂ h
    have hv := congrArg Fin.val (rCore.wires.injective h)
    dsimp [fWire, rElecAxis654, QRegister.slice, QRegister.slice_apply,
      NuclearTwistMulKickAndBridge288Alt.qreg_slice_wires,
      NuclearTwistMulKickAndBridge288Alt.qreg_whole_wires,
      NuclearTwistMulKickAndBridge288Alt.emb_trans_apply,
      NuclearTwistMulKickAndBridge288Alt.emb_refl_apply,
      NuclearTwistMulKickAndBridge288Alt.emb_mk_apply, QRegister.compose,
      QRegister.compose_apply, NuclearTwistMulKickAndBridge288Alt.qreg_compose_wires,
      NuclearTwistMulKickAndBridge288Alt.qreg_block_apply,
      NuclearTwistMulKickAndBridge288Alt.qreg_block_wires_apply] at hv
    exact Fin.ext (by have := a₁.isLt; have := a₂.isLt; omega)
  have hp := phasePerm_sequence_X fWire hinj
  apply circuit_eval_eq_embed_perm_of_phasePerm rCore
    (parallelBit5FlipAxes (rElecAxis654 rCore)) (xor32CorePerm mPayload) _ hp
  · intro β w hw
    have hnot : ¬(∃ a : Fin 654, fWire a = w) := by
      rintro ⟨a, rfl⟩
      exact hw ((QRegister.mem_image rCore _).mpr ⟨_, rfl⟩)
    simp only [hnot, ↓reduceIte]
  · intro β
    ext k
    change basisBits _ ((xor32CorePerm mPayload)
      ((basisBitsEquiv _).symm (fun q ↦ β (rCore q)))) k = _
    unfold xor32CorePerm
    rw [basisBits_perm_ofBijective (xor32BitFn mPayload)
      (xor32BitFn_involutive mPayload).bijective]
    dsimp only [xor32BitFn]
    have hiff : (k.val < 3924 ∧ k.val % 6 = 5) ↔ (∃ a : Fin 654, fWire a = rCore k) := by
      constructor
      · rintro ⟨hlt, hmod⟩
        refine ⟨⟨k.val / 6, by omega⟩, ?_⟩
        dsimp [fWire, rElecAxis654, QRegister.slice, QRegister.slice_apply,
          NuclearTwistMulKickAndBridge288Alt.qreg_slice_wires,
          NuclearTwistMulKickAndBridge288Alt.qreg_whole_wires,
          NuclearTwistMulKickAndBridge288Alt.emb_trans_apply,
          NuclearTwistMulKickAndBridge288Alt.emb_refl_apply,
          NuclearTwistMulKickAndBridge288Alt.emb_mk_apply, QRegister.compose,
          QRegister.compose_apply, NuclearTwistMulKickAndBridge288Alt.qreg_compose_wires,
          NuclearTwistMulKickAndBridge288Alt.qreg_block_apply,
          NuclearTwistMulKickAndBridge288Alt.qreg_block_wires_apply]
        exact congrArg rCore (Fin.ext (by dsimp; omega))
      · rintro ⟨a, h⟩
        have hv := congrArg Fin.val (rCore.wires.injective h)
        have ha := a.isLt
        dsimp [fWire, rElecAxis654, QRegister.slice, QRegister.slice_apply,
          NuclearTwistMulKickAndBridge288Alt.qreg_slice_wires,
          NuclearTwistMulKickAndBridge288Alt.qreg_whole_wires,
          NuclearTwistMulKickAndBridge288Alt.emb_trans_apply,
          NuclearTwistMulKickAndBridge288Alt.emb_refl_apply,
          NuclearTwistMulKickAndBridge288Alt.emb_mk_apply, QRegister.compose,
          QRegister.compose_apply, NuclearTwistMulKickAndBridge288Alt.qreg_compose_wires,
          NuclearTwistMulKickAndBridge288Alt.qreg_block_apply,
          NuclearTwistMulKickAndBridge288Alt.qreg_block_wires_apply] at hv
        omega
    simp only [hiff]
set_option maxRecDepth 2000000 in
theorem uTwistRest_comm_highReg_proj {mPayload kSub n : ℕ} [NeZero (2 ^ n)]
    (hm : 22 ≤ mPayload) (c : Configuration)
    (rCore : QRegister (fullSysCoreWires mPayload) n) (rSub : QRegister kSub n)
    (hDisjElec : (rElecCore rCore).DisjointWires rSub) (v : Fin (2 ^ kSub)) :
    (rCore.embedUnitary (uTwistRest hm c)).1 * rSub.basisOutcomeProjector v =
    rSub.basisOutcomeProjector v * (rCore.embedUnitary (uTwistRest hm c)).1 := by
  have hDiagComm : ∀ {K : ℕ} (d : Fin (2 ^ K) → ℂ) (P : Operator (2 ^ n)) (r : QRegister K n),
      (∃ dp : Fin (2 ^ n) → ℂ, P = Matrix.diagonal dp) → (r.embedMatrix (Matrix.diagonal d)) *
      P = P * (r.embedMatrix (Matrix.diagonal d)) := by
    rintro K d _ r ⟨dp, rfl⟩
    rw [QRegister.embedMatrix_diagonal, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    exact congrArg Matrix.diagonal (funext fun _ ↦ mul_comm _ _)
  have hPdiag : ∃ dp : Fin (2 ^ n) → ℂ, rSub.basisOutcomeProjector v = Matrix.diagonal dp :=
    ⟨_, rSub.basisOutcomeProjector_eq_diagonal v⟩
  have hS2 : (rCore.embedUnitary (uSlot2KickCore c hm)).1 * rSub.basisOutcomeProjector v =
      rSub.basisOutcomeProjector v * (rCore.embedUnitary (uSlot2KickCore c hm)).1 :=
    hDiagComm _ _ rCore hPdiag
  have hS4 : (rCore.embedUnitary (uSlot4KickCore hm)).1 * rSub.basisOutcomeProjector v =
      rSub.basisOutcomeProjector v * (rCore.embedUnitary (uSlot4KickCore hm)).1 :=
    hDiagComm _ _ rCore hPdiag
  have hXorDisj : Disjoint (parallelBit5FlipAxes (rElecAxis654 rCore)).support rSub.image := by
    rw [Finset.disjoint_left]
    intro w hwSupp hwSub
    exact Finset.disjoint_left.mp
      ((QRegExt.disjointWires_iff_disjoint_image _ _).mp hDisjElec)
      (lemHexAux rCore hwSupp) hwSub
  have hXor : (rCore.embedUnitary (uXor32Core mPayload)).1 * rSub.basisOutcomeProjector v =
      rSub.basisOutcomeProjector v * (rCore.embedUnitary (uXor32Core mPayload)).1 := by
    rw [← congrArg Subtype.val (lemHex353 rCore)]
    exact CircuitExt.eval_comm_basisOutcomeProjector_of_disjoint_support _ rSub hXorDisj v
  simp only [uTwistRest, QRegister.embedUnitary_mul, Submonoid.coe_mul]
  calc
    (rCore.embedUnitary (uSlot2KickCore c hm)).1 *
        ((rCore.embedUnitary (uSlot4KickCore hm)).1 *
          (rCore.embedUnitary (uXor32Core mPayload)).1) * rSub.basisOutcomeProjector v
      = (rCore.embedUnitary (uSlot2KickCore c hm)).1 *
          (rCore.embedUnitary (uSlot4KickCore hm)).1 *
          ((rCore.embedUnitary (uXor32Core mPayload)).1 * rSub.basisOutcomeProjector v) := by
          simp only [Matrix.mul_assoc]
    _ = (rCore.embedUnitary (uSlot2KickCore c hm)).1 *
          ((rCore.embedUnitary (uSlot4KickCore hm)).1 * rSub.basisOutcomeProjector v) *
          (rCore.embedUnitary (uXor32Core mPayload)).1 := by
          rw [hXor]; simp only [Matrix.mul_assoc]
    _ = ((rCore.embedUnitary (uSlot2KickCore c hm)).1 * rSub.basisOutcomeProjector v) *
          (rCore.embedUnitary (uSlot4KickCore hm)).1 *
          (rCore.embedUnitary (uXor32Core mPayload)).1 := by
          rw [hS4]; simp only [Matrix.mul_assoc]
    _ = rSub.basisOutcomeProjector v *
          ((rCore.embedUnitary (uSlot2KickCore c hm)).1 *
            ((rCore.embedUnitary (uSlot4KickCore hm)).1 *
              (rCore.embedUnitary (uXor32Core mPayload)).1)) := by
          rw [hS2]; simp only [Matrix.mul_assoc]
attribute [local irreducible] uTwistRest
theorem slotBitProj_eq_singleton_basisOutcomeProjector {n : ℕ} (w : Wire n) (b : Fin 2) :
    slotBitProj w b = (QRegister.singleton w).basisOutcomeProjector b := by
  rw [slotBitProj, (QRegister.singleton w).basisOutcomeProjector_eq_diagonal b]
  ext i j
  by_cases hij : i = j
  · subst hij
    simp only [Matrix.diagonal_apply_eq]
    have hbit : basisBits 1 ((QRegister.singleton w).extractIndex i) 0 = basisBits n i w :=
      (QRegister.singleton w).basisBits_extractIndex i 0
    rw [← hbit]
    have hcond : ∀ (u : Fin (2 ^ 1)) (c : Fin 2),(basisBits 1 u 0).val = c.val ↔ u = c := by
      intro u c
      rw [basisBits_eq_div_mod]
      fin_cases u <;> fin_cases c <;> decide
    by_cases hy : (QRegister.singleton w).extractIndex i = b
    · rw [ite_eq_left_iff.mpr fun h ↦ absurd ((hcond _ b).mpr hy) h,
        ite_eq_left_iff.mpr fun h ↦ absurd hy h]
    · rw [ite_eq_right_iff.mpr fun h ↦ absurd ((hcond _ b).mp h) hy,
        ite_eq_right_iff.mpr fun h ↦ absurd h hy]
  · rw [Matrix.diagonal_apply_ne _ hij, Matrix.diagonal_apply_ne _ hij]
theorem rElecCore_idReg_disj_singleton {mPayload : ℕ} (q : Wire (fullSysCoreWires mPayload))
    (hq : 3924 ≤ q.val) : (rElecCore (QRegExt.idReg (fullSysCoreWires
    mPayload))).DisjointWires (QRegister.singleton q) := by
  rw [QRegister.DisjointWires, Set.disjoint_left]
  rintro _ ⟨i, rfl⟩ ⟨_, hj⟩
  have hv : 0 + i.val = q.val := congrArg Fin.val hj.symm
  have hi : i.val < 3924 := i.isLt
  omega
theorem uTwistRest_comm_high_wire {mPayload : ℕ} (hm : 22 ≤ mPayload) (c : Configuration)
    (q : Wire (fullSysCoreWires mPayload)) (hq : 3924 ≤ q.val) (b : Fin 2) :
    (uTwistRest hm c).1 * slotBitProj q b = slotBitProj q b * (uTwistRest hm c).1 := by
  have hDisj : (rElecCore (QRegExt.idReg (fullSysCoreWires mPayload))).DisjointWires
      (QRegister.singleton q) := rElecCore_idReg_disj_singleton q hq
  have hProj : slotBitProj q b = (QRegister.singleton q).basisOutcomeProjector b :=
      slotBitProj_eq_singleton_basisOutcomeProjector q b
  have hId : ((QRegExt.idReg (fullSysCoreWires mPayload)).embedUnitary (uTwistRest hm c)).1
      = (uTwistRest hm c).1 := congrArg Subtype.val (embedUnitary_idReg_eq (uTwistRest hm c))
  have hComm : ((QRegExt.idReg (fullSysCoreWires mPayload)).embedUnitary (uTwistRest hm
      c)).1 * (QRegister.singleton q).basisOutcomeProjector b =
      (QRegister.singleton q).basisOutcomeProjector b * ((QRegExt.idReg (fullSysCoreWires
      mPayload)).embedUnitary (uTwistRest hm c)).1 := uTwistRest_comm_highReg_proj hm c
      (QRegExt.idReg (fullSysCoreWires mPayload)) (QRegister.singleton q) hDisj b
  exact (congrArg₂ (· * ·) hId.symm hProj).trans
    (hComm.trans (congrArg₂ (· * ·) hProj.symm hId))
end HoistedTwistRestExports
end NuclearTwistMulKickAndBridge288
end
end ModNuclearTwistMulKickAndBridge288

section ModNuclearTwistDisentangleSum288
@[expose] public section
namespace NuclearTwistDisentangleSum288Alt
theorem qreg_ext {k n : ℕ} {r s : QRegister k n} (h : ∀ i, r i = s i) : r = s :=
  QRegister.ext (Function.Embedding.ext h)
end NuclearTwistDisentangleSum288Alt
namespace RevTempPerm
open Operator Matrix _root_.DynamicCircuit DynCircuitExt QProg HermitianMat
open MeasureBranchHadamardSem (ket matrix_ext_ket eval_seq_mulVec ket_X
  ket_CNOT ket_TOFF ket_projector_zero projZeroAll ket_projZeroAll projZeroAll_conjTranspose
  projZeroAll_eq_basisOutcomeProjector_zero RealizesCleanUnitary)
open BchCubeDecoder StreamingBchComparator
open MomSlot0CircuitHalf (padZeroBits)
open DyadicQft64 hiding dyadicTurn phaseGradKet
open DyadicQft64.PhasePerm
open SpecsAux.PhaseGradCatalystCore
open NuclearTwistAndXor654Concrete hiding fullSysCoreWires
  IntertwinesLocalCat
open NuclearTwistRealizes
open FullSysCatSegmentBridge
open scoped Matrix BigOperators ComplexOrder MatrixOrder Circuit.Notation
@[simp] theorem zmod2_val_zero : (0 : ZMod 2).val = 0 := rfl
@[simp] theorem zmod2_val_one : (1 : ZMod 2).val = 1 := rfl
theorem wire_ne_of_lt {M : ℕ} {a b : Wire M} (h : a.val < b.val) : a ≠ b :=
  fun heq ↦ absurd (congrArg Fin.val heq) (Nat.ne_of_lt h)
theorem wire_ne_of_gt {M : ℕ} {a b : Wire M} (h : b.val < a.val) : a ≠ b :=
  (wire_ne_of_lt h).symm
theorem mul_mulVec_rev {n : ℕ} (A B : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ)
    (v : Fin (2 ^ n) → ℂ) : (A * B).mulVec v = A.mulVec (B.mulVec v) :=
  (Matrix.mulVec_mulVec v A B).symm
noncomputable def writeRegRev {k n : ℕ} (β : BitAssignment n) (r : QRegister k n)
    (γ : BitAssignment k) : BitAssignment n :=
  basisBits n (r.replaceIndex ((basisBitsEquiv n).symm β) ((basisBitsEquiv k).symm γ))
@[simp] theorem writeRegRev_apply_reg {k n : ℕ} (β : BitAssignment n) (r : QRegister k n)
    (γ : BitAssignment k) (i : Fin k) : writeRegRev β r γ (r i) = γ i := by
  simp [writeRegRev, QRegister.basisBits_replaceIndex_apply]
theorem writeRegRev_apply_of_not_mem {k n : ℕ} (β : BitAssignment n) (r : QRegister k n)
    (γ : BitAssignment k) (w : Wire n) (hw : w ∉ Set.range r.wires) :
    writeRegRev β r γ w = β w := by
  simp [writeRegRev, QRegister.basisBits_replaceIndex_of_not_mem _ _ _ _ hw]
noncomputable abbrev localIdxRev {k n : ℕ} (r : QRegister k n) (β : BitAssignment n) : Fin
    (2 ^ k) := (basisBitsEquiv k).symm (fun i ↦ β (r i))
theorem embedMatrix_mulVec_ket_rev {k n : ℕ} (r : QRegister k n)
    (A : Matrix (Fin (2 ^ k)) (Fin (2 ^ k)) ℂ) (β : BitAssignment n) :
    (r.embedMatrix A).mulVec (ket β) =
      ∑ l : Fin (2 ^ k), A l (localIdxRev r β) • ket (writeRegRev β r (basisBits k l)) := by
  have hext : r.extractIndex ((basisBitsEquiv n).symm β) = localIdxRev r β := by
    simp [QRegister.extractIndex]
  have hcol (j : Fin (2 ^ k)) :
      A.mulVec (Pi.single j 1) = ∑ l : Fin (2 ^ k), A l j • Pi.single l 1 := by
    funext x
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  rw [ket, basisState, r.embedMatrix_mulVec_single_factors, hext, hcol,
    QRegister.tensorState_sum_left]
  refine Finset.sum_congr rfl fun l _ ↦ ?_
  rw [QRegister.tensorState_smul_left, QRegister.tensorState_single_replaceIndex]
  simp [writeRegRev, ket, basisState]
inductive CliffProg (M : ℕ) where
  | nil : CliffProg M
  | x (q : Wire M) : CliffProg M
  | cnot (c t : Wire M) (h : c ≠ t) : CliffProg M
  | seq (c₁ c₂ : CliffProg M) : CliffProg M
namespace CliffProg
def eval {M : ℕ} : CliffProg M → BitAssignment M → BitAssignment M
  | .nil, β => β
  | .x q, β => Function.update β q (β q + 1)
  | .cnot c t _, β => Function.update β t (β t + β c)
  | .seq c₁ c₂, β => c₂.eval (c₁.eval β)
def inv {M : ℕ} : CliffProg M → CliffProg M
  | .nil => .nil
  | .x q => .x q
  | .cnot c t h => .cnot c t h
  | .seq c₁ c₂ => .seq c₂.inv c₁.inv
def toCircuit {M : ℕ} : CliffProg M → Circuit M
  | .nil => .identity
  | .x q => Circuit.X q
  | .cnot c t h => Circuit.CNOT c t h
  | .seq c₁ c₂ => c₁.toCircuit ;;ᶜ c₂.toCircuit
def onRegister {M n : ℕ} (r : QRegister M n) : CliffProg M → CliffProg n
  | .nil => .nil
  | .x q => .x (r q)
  | .cnot c t h => .cnot (r c) (r t) (r.wires.injective.ne h)
  | .seq c₁ c₂ => .seq (c₁.onRegister r) (c₂.onRegister r)
def SupportsRange {M : ℕ} (lo hi : ℕ) : CliffProg M → Prop
  | .nil => True
  | .x q => lo ≤ q.val ∧ q.val < hi
  | .cnot c t _ => (lo ≤ c.val ∧ c.val < hi) ∧ (lo ≤ t.val ∧ t.val < hi)
  | .seq c₁ c₂ => c₁.SupportsRange lo hi ∧ c₂.SupportsRange lo hi
@[simp]
theorem toCircuit_count_toff {M : ℕ} : ∀ c : CliffProg M, c.toCircuit.count PrimitiveGate.TOFF = 0
  | .nil => by simp [toCircuit]
  | .x _ => by simp [toCircuit]
  | .cnot _ _ _ => by simp [toCircuit]
  | .seq c₁ c₂ => by simp [toCircuit, toCircuit_count_toff]
@[simp]
theorem toCircuit_count_t {M : ℕ} : ∀ c : CliffProg M, c.toCircuit.count PrimitiveGate.T = 0
  | .nil => by simp [toCircuit]
  | .x _ => by simp [toCircuit]
  | .cnot _ _ _ => by simp [toCircuit]
  | .seq c₁ c₂ => by simp [toCircuit, toCircuit_count_t]
theorem toCircuit_eval_ket {M : ℕ} :
    ∀ (c : CliffProg M) (β : BitAssignment M),
      c.toCircuit.eval.1.mulVec (ket β) = ket (c.eval β)
  | .nil, _ => by simp [toCircuit]; rfl
  | .x q, β => by rw [toCircuit, ket_X]; rfl
  | .cnot c t h, β => by rw [toCircuit, ket_CNOT]; rfl
  | .seq c₁ c₂, β => by
      rw [toCircuit, eval_seq_mulVec, toCircuit_eval_ket c₁, toCircuit_eval_ket c₂]
      rfl
theorem onRegister_toCircuit_eval {M n : ℕ} (r : QRegister M n) :
    ∀ c : CliffProg M, ((c.onRegister r).toCircuit).eval = (c.toCircuit.onRegister r).eval
  | .nil => by simp [onRegister, toCircuit]
  | .x q => by
      simp only [onRegister, toCircuit, Circuit.X, Circuit.single, Circuit.onRegister]
      congr 2
  | .cnot c t h => by
      simp only [onRegister, toCircuit, Circuit.CNOT, Circuit.onRegister]
      congr 2; apply NuclearTwistDisentangleSum288Alt.qreg_ext; intro i; fin_cases i <;>
        rfl
  | .seq c₁ c₂ => by simp [onRegister, toCircuit, Circuit.eval_seq, onRegister_toCircuit_eval]
theorem inv_eval {M : ℕ} : ∀ (c : CliffProg M) (β : BitAssignment M), c.inv.eval (c.eval β) = β
  | .nil, _ => rfl
  | .x q, β => by
      funext w
      by_cases hw : w = q
      · subst hw
        have h11 : (1 + 1 : ZMod 2) = 0 := rfl
        simp [inv, eval, add_assoc, h11]
      · simp [inv, eval, Function.update_of_ne hw]
  | .cnot c t h, β => by
      funext w
      by_cases hw : w = t
      · subst hw
        simp [inv, eval, Function.update_of_ne h, add_assoc, CharTwo.add_self_eq_zero]
      · simp [inv, eval, Function.update_of_ne hw]
  | .seq c₁ c₂, β => by simp [inv, eval, inv_eval]
theorem inv_supportsRange {M lo hi : ℕ} :
    ∀ (c : CliffProg M), c.SupportsRange lo hi → c.inv.SupportsRange lo hi
  | .nil, _ => trivial
  | .x _, h => h
  | .cnot _ _ _, h => h
  | .seq c₁ c₂, ⟨h₁, h₂⟩ => ⟨inv_supportsRange c₂ h₂, inv_supportsRange c₁ h₁⟩
theorem eval_outside {M lo hi : ℕ} :
    ∀ (c : CliffProg M), c.SupportsRange lo hi →
      ∀ (β : BitAssignment M) (w : Wire M),(w.val < lo ∨ hi ≤ w.val) → c.eval β w = β w
  | .nil, _, _, _, _ => rfl
  | .x q, ⟨hlo, hhi⟩, β, w, hw =>
      Function.update_of_ne (fun heq ↦ by have := congrArg Fin.val heq; omega) _ _
  | .cnot _ t _, ⟨_, ⟨hlo, hhi⟩⟩, β, w, hw =>
      Function.update_of_ne (fun heq ↦ by have := congrArg Fin.val heq; omega) _ _
  | .seq c₁ c₂, ⟨h₁, h₂⟩, β, w, hw => by
      simp only [eval]
      rw [eval_outside c₂ h₂ _ w hw, eval_outside c₁ h₁ _ w hw]
theorem eval_congr_ge {M lo hi : ℕ} :
    ∀ (c : CliffProg M), c.SupportsRange lo hi →
      ∀ (β₁ β₂ : BitAssignment M),
        (∀ w : Wire M, lo ≤ w.val → β₁ w = β₂ w) →
        ∀ w : Wire M, lo ≤ w.val → c.eval β₁ w = c.eval β₂ w
  | .nil, _, _, _, h, w, hw => h w hw
  | .x q, ⟨_, _⟩, β₁, β₂, h, w, hw => by
      simp only [eval]
      by_cases hwq : w = q
      · subst hwq; simp [h w hw]
      · simp [Function.update_of_ne hwq, h w hw]
  | .cnot c t _, ⟨⟨hclo, _⟩,⟨_, _⟩⟩, β₁, β₂, h, w, hw => by
      simp only [eval]
      by_cases hwt : w = t
      · subst hwt; simp [h w hw, h c hclo]
      · simp [Function.update_of_ne hwt, h w hw]
  | .seq c₁ c₂, ⟨h₁, h₂⟩, β₁, β₂, h, w, hw =>
      eval_congr_ge c₂ h₂ (c₁.eval β₁) (c₁.eval β₂) (eval_congr_ge c₁ h₁ β₁ β₂ h) w hw
end CliffProg
inductive RevTempProg (m : ℕ) where
  | nil : RevTempProg m
  | cliff (c : CliffProg m) : RevTempProg m
  | seq (p₁ p₂ : RevTempProg m) : RevTempProg m
  | tempAnd (c₁ c₂ anc : Wire m) (h₁₂ : c₁ ≠ c₂) (h₁a : c₁ ≠ anc) (h₂a : c₂ ≠ anc)
      (body : RevTempProg m) : RevTempProg m
namespace RevTempProg
def cnot {m : ℕ} (c t : Wire m) (h : c ≠ t) : RevTempProg m := .cliff (.cnot c t h)
def evalBits {m : ℕ} : RevTempProg m → BitAssignment m → BitAssignment m
  | .nil, β => β
  | .cliff c, β => c.eval β
  | .seq p₁ p₂, β => p₂.evalBits (p₁.evalBits β)
  | .tempAnd c₁ c₂ anc _ _ _ body, β =>
      let β₁ := Function.update β anc (β anc + β c₁ * β c₂)
      let β₂ := body.evalBits β₁
      Function.update β₂ anc (β₂ anc + β₂ c₁ * β₂ c₂)
def countTempAnd {m : ℕ} : RevTempProg m → ℕ
  | .nil => 0
  | .cliff _ => 0
  | .seq p₁ p₂ => p₁.countTempAnd + p₂.countTempAnd
  | .tempAnd _ _ _ _ _ _ body => 1 + body.countTempAnd
@[simp] theorem countTempAnd_nil {m : ℕ} : (RevTempProg.nil : RevTempProg m).countTempAnd = 0 := rfl
@[simp] theorem countTempAnd_cliff {m : ℕ} (c : CliffProg m) :
    (RevTempProg.cliff c).countTempAnd = 0 := rfl
@[simp] theorem countTempAnd_seq {m : ℕ} (p₁ p₂ : RevTempProg m) :
    (RevTempProg.seq p₁ p₂).countTempAnd = p₁.countTempAnd + p₂.countTempAnd := rfl
@[simp] theorem countTempAnd_tempAnd {m : ℕ} (c₁ c₂ anc : Wire m)
    (h₁₂ : c₁ ≠ c₂) (h₁a : c₁ ≠ anc) (h₂a : c₂ ≠ anc) (body : RevTempProg m) :
    (RevTempProg.tempAnd c₁ c₂ anc h₁₂ h₁a h₂a body).countTempAnd = 1 + body.countTempAnd := rfl
def toToffCircuit {m : ℕ} : RevTempProg m → Circuit m
  | .nil => .identity
  | .cliff c => c.toCircuit
  | .seq p₁ p₂ => p₁.toToffCircuit ;;ᶜ p₂.toToffCircuit
  | .tempAnd c₁ c₂ anc h₁₂ h₁a h₂a body =>
      Circuit.TOFF c₁ c₂ anc h₁₂ h₁a h₂a ;;ᶜ body.toToffCircuit ;;ᶜ
        Circuit.TOFF c₁ c₂ anc h₁₂ h₁a h₂a
def onRegister {m n : ℕ} (r : QRegister m n) : RevTempProg m → RevTempProg n
  | .nil => .nil
  | .cliff c => .cliff (c.onRegister r)
  | .seq p₁ p₂ => .seq (p₁.onRegister r) (p₂.onRegister r)
  | .tempAnd c₁ c₂ anc h₁₂ h₁a h₂a body =>
      .tempAnd (r c₁) (r c₂) (r anc)
        (r.wires.injective.ne h₁₂) (r.wires.injective.ne h₁a) (r.wires.injective.ne h₂a)
        (body.onRegister r)
def toDyn {Var : Type} {n : ℕ} (v : Var) : RevTempProg n → DynamicCircuit Var n
  | .nil => .circuit .identity
  | .cliff c => .circuit c.toCircuit
  | .seq p₁ p₂ => .seq (p₁.toDyn v) (p₂.toDyn v)
  | .tempAnd c₁ c₂ anc h₁₂ h₁a h₂a body =>
      .seq (DynamicCircuit.andCompute c₁ c₂ anc h₁a h₂a)
        (.seq (body.toDyn v) (DynamicCircuit.andUncompute v c₁ c₂ anc h₁₂))
@[simp] theorem onRegister_countTempAnd {m n : ℕ} (r : QRegister m n) :
    ∀ p : RevTempProg m, (p.onRegister r).countTempAnd = p.countTempAnd
  | .nil => rfl
  | .cliff _ => rfl
  | .seq p₁ p₂ => by simp [onRegister, countTempAnd, onRegister_countTempAnd]
  | .tempAnd _ _ _ _ _ _ body => by simp [onRegister, countTempAnd, onRegister_countTempAnd]
@[simp] theorem toDyn_count_toff {Var : Type} {n : ℕ} (v : Var) :
    ∀ p : RevTempProg n, (p.toDyn v).count PrimitiveGate.TOFF = 0
  | .nil => by simp [toDyn]
  | .cliff _ => by simp [toDyn]
  | .seq p₁ p₂ => by simp [toDyn, toDyn_count_toff]
  | .tempAnd c₁ c₂ anc h₁₂ h₁a h₂a body => by
      simp [toDyn, DynamicCircuit.count_andCompute_toff,
        DynamicCircuit.count_andUncompute_toff, toDyn_count_toff]
@[simp] theorem toDyn_count_t {Var : Type} {n : ℕ} (v : Var) :
    ∀ p : RevTempProg n, (p.toDyn v).count PrimitiveGate.T = 4 * p.countTempAnd
  | .nil => by simp [toDyn, countTempAnd]
  | .cliff _ => by simp [toDyn, countTempAnd]
  | .seq p₁ p₂ => by
      simp [toDyn, countTempAnd, toDyn_count_t]
      ring
  | .tempAnd c₁ c₂ anc h₁₂ h₁a h₂a body => by
      simp [toDyn, DynamicCircuit.count_andCompute_t,
        DynamicCircuit.count_andUncompute_t, countTempAnd, toDyn_count_t]
      ring
theorem toToffCircuit_eval_ket {m : ℕ} :
    ∀ (p : RevTempProg m) (β : BitAssignment m),
      (p.toToffCircuit).eval.1.mulVec (ket β) = ket (p.evalBits β)
  | .nil, β => by simp [toToffCircuit]; rfl
  | .cliff c, β => by rw [toToffCircuit, c.toCircuit_eval_ket]; rfl
  | .seq p₁ p₂, β => by
      rw [toToffCircuit, eval_seq_mulVec, toToffCircuit_eval_ket p₁, toToffCircuit_eval_ket p₂]
      rfl
  | .tempAnd c₁ c₂ anc h₁₂ h₁a h₂a body, β => by
      rw [toToffCircuit, eval_seq_mulVec, eval_seq_mulVec,
        ket_TOFF, toToffCircuit_eval_ket body, ket_TOFF]
      rfl
theorem onRegister_toToffCircuit_eval {m n : ℕ} (r : QRegister m n) :
    ∀ p : RevTempProg m, ((p.onRegister r).toToffCircuit).eval = (p.toToffCircuit.onRegister r).eval
  | .nil => by simp [onRegister, toToffCircuit]
  | .cliff c => by simp [onRegister, toToffCircuit, c.onRegister_toCircuit_eval]
  | .seq p₁ p₂ => by
      simp [onRegister, toToffCircuit, Circuit.eval_seq, onRegister_toToffCircuit_eval]
  | .tempAnd c₁ c₂ anc h₁₂ h₁a h₂a body => by
      have htoff : (Circuit.TOFF (r c₁) (r c₂) (r anc) (r.wires.injective.ne h₁₂)
          (r.wires.injective.ne h₁a) (r.wires.injective.ne h₂a)).eval =
          ((Circuit.TOFF c₁ c₂ anc h₁₂ h₁a h₂a).onRegister r).eval := by
        simp only [Circuit.TOFF, Circuit.onRegister]
        congr 2; apply NuclearTwistDisentangleSum288Alt.qreg_ext; intro i; fin_cases i <;>
          rfl
      simp [onRegister, toToffCircuit, Circuit.eval_seq, htoff,
        onRegister_toToffCircuit_eval r body]
end RevTempProg
def CleanRem (M rem : ℕ) (β : BitAssignment M) : Prop :=
  ∀ w : Wire M, M - rem ≤ w.val → β w = 0
def tailScr {M n : ℕ} (rComb : QRegister M n) (rem : ℕ) (h : rem ≤ M) : Fin rem → Wire n :=
  fun j ↦ rComb ⟨(M - rem) + j.val, by omega⟩
theorem tailScr_succ {M n : ℕ} (rComb : QRegister M n) (rem' : ℕ) (h : rem' + 1 ≤ M) :
    tailScr rComb (rem' + 1) h =
      Fin.cons (rComb ⟨M - (rem' + 1), by omega⟩) (tailScr rComb rem' (by omega)) := by
  funext j
  cases j using Fin.cases with
  | zero => simp only [Fin.cons_zero, tailScr, Fin.val_zero, add_zero]
  | succ i =>
      simp only [Fin.cons_succ, tailScr, Fin.val_succ]
      congr 1; ext; dsimp; omega
theorem projZeroAll_tailScr_sub {M n : ℕ} [NeZero (2 ^ n)] (rComb : QRegister M n)
    {rem₁ rem₂ : ℕ} (h₁ : rem₁ ≤ M) (h₂ : rem₂ ≤ M) (hle : rem₁ ≤ rem₂) : projZeroAll rem₁
    (tailScr rComb rem₁ h₁) * projZeroAll rem₂ (tailScr rComb rem₂ h₂) = projZeroAll rem₂
    (tailScr rComb rem₂ h₂) := by
  apply matrix_ext_ket
  intro β
  simp only [mul_mulVec_rev, ket_projZeroAll]
  by_cases hz₂ : ∀ j : Fin rem₂, β (tailScr rComb rem₂ h₂ j) = 0
  · have hz₁ : ∀ i : Fin rem₁, β (tailScr rComb rem₁ h₁ i) = 0 := by
      intro i
      have heq : tailScr rComb rem₁ h₁ i =
          tailScr rComb rem₂ h₂ ⟨(M - rem₁) - (M - rem₂) + i.val, by omega⟩ := by
        dsimp [tailScr]; congr 1; ext; dsimp; omega
      rw [heq]
      exact hz₂ _
    simp [hz₁, hz₂, ket_projZeroAll]
  · simp [hz₂]
def ValidCleanRem (M : ℕ) : ℕ → RevTempProg M → Prop
  | _, .nil => True
  | _, .cliff _ => True
  | rem, .seq p₁ p₂ =>
      ∃ remMid : ℕ, remMid ≤ M ∧
        ValidCleanRem M rem p₁ ∧ ValidCleanRem M remMid p₂ ∧
        (∀ β : BitAssignment M, CleanRem M rem β → CleanRem M remMid (p₁.evalBits β))
  | rem, .tempAnd c₁ c₂ anc _ _ _ body =>
      M - rem ≤ anc.val ∧
        let rem' := M - (anc.val + 1)
        ValidCleanRem M rem' body ∧
          (∀ β₁ : BitAssignment M, CleanRem M rem' β₁ →
            body.evalBits β₁ c₁ = β₁ c₁ ∧
              body.evalBits β₁ c₂ = β₁ c₂ ∧
              body.evalBits β₁ anc = β₁ anc)
theorem eval_onRegister_rev_ket {M n : ℕ} (rComb : QRegister M n)
    (p : RevTempProg M) (β : BitAssignment n) :
    let γ : BitAssignment M := fun idx ↦ β (rComb idx)
    ((p.onRegister rComb).toToffCircuit).eval.1.mulVec (ket β) =
      ket (writeRegRev β rComb (p.evalBits γ)) := by
  intro γ
  rw [p.onRegister_toToffCircuit_eval rComb, Circuit.eval_onRegister,
    QRegister.embedUnitary_val, embedMatrix_mulVec_ket_rev]
  have hloc : localIdxRev rComb β = (basisBitsEquiv M).symm γ := rfl
  rw [hloc]
  have hcol : ∀ l : Fin (2 ^ M), (p.toToffCircuit).eval.1 l ((basisBitsEquiv M).symm γ) = if l
      = (basisBitsEquiv M).symm (p.evalBits γ) then 1 else 0 := by
    intro l
    have hk := congrFun (p.toToffCircuit_eval_ket γ) l
    simpa [ket, basisState, Matrix.mulVec_single_one, Pi.single_apply, eq_comm] using hk
  simp_rw [hcol, ite_smul, one_smul, zero_smul]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  rw [basisBits_symm_eq]
theorem realizesCleanUnitary_seq_asym {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    [NeZero (2 ^ n)] {v : Var} {P₁ P₂ : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ}
    {c₁ c₂ : DynamicCircuit Var n} {U₁ U₂ : Unitary (2 ^ n)} (hP₁ : P₁ᴴ = P₁) (hP₂ : P₂ᴴ = P₂)
    (h₁ : RealizesCleanUnitary v P₁ c₁ U₁) (h₂ : RealizesCleanUnitary v P₂ c₂ U₂)
    (hclean : P₂ * (U₁.1 * P₁) = U₁.1 * P₁) : RealizesCleanUnitary v P₁ (.seq c₁ c₂) (U₂ * U₁)
    := by
  refine ⟨fun Ψ hΨ σ val ↦ ?_, fun Θ hΘ σ ↦ ?_⟩
  · simp only [DynamicCircuit.compile_seq, wp_qSeq]
    exact h₁.1 (wp c₂.compile Ψ) (h₂.1 Ψ hΨ) σ val
  · have hΨ_inv := h₂.1 Θ hΘ
    have hadj : P₁ * U₁.1ᴴ * P₂ = P₁ * U₁.1ᴴ := by
      have h := congrArg conjTranspose hclean
      simpa [conjTranspose_mul, hP₁, hP₂, ← Matrix.mul_assoc] using h
    simp only [DynamicCircuit.compile_seq, wp_qSeq]
    rw [h₁.2 (wp c₂.compile Θ) hΨ_inv σ]
    simp only [wpQAssignCompat, qAssignObsMap, Observable.conj_coe, Unitary.coe_star,
      Matrix.star_eq_conjTranspose, conj_conj]
    calc
      ((wp c₂.compile Θ σ).1).conj (P₁ * U₁.1ᴴ)
        = (((wp c₂.compile Θ σ).1).conj P₂).conj (P₁ * U₁.1ᴴ) := by
            rw [conj_conj, hadj]
      _ = (((wpQAssignCompat U₂ Θ σ).1).conj P₂).conj (P₁ * U₁.1ᴴ) := by
            rw [h₂.2 Θ hΘ σ]
      _ = (Θ σ).1.conj (P₁ * (U₂ * U₁).1ᴴ) := by
            simp only [wpQAssignCompat, qAssignObsMap, Observable.conj_coe, Unitary.coe_star,
              Matrix.star_eq_conjTranspose, conj_conj, Submonoid.coe_mul, conjTranspose_mul]
            rw [← Matrix.mul_assoc (P₁ * U₁.1ᴴ) P₂ U₂.1ᴴ, hadj, Matrix.mul_assoc]
theorem realizes_of_validCleanRem
    {Var : Type} [Fintype Var] [DecidableEq Var] {M n : ℕ} [NeZero (2 ^ n)]
    (v : Var) (rComb : QRegister M n) :
    ∀ (p : RevTempProg M) (rem : ℕ) (hrem : rem ≤ M),
      ValidCleanRem M rem p →
      RealizesCleanUnitary v (projZeroAll rem (tailScr rComb rem hrem))
        ((p.onRegister rComb).toDyn v) (((p.onRegister rComb).toToffCircuit).eval)
  | .nil, _, _, _ => RealizesCleanUnitary.circuit v _ _
  | .cliff _, _, _, _ => RealizesCleanUnitary.circuit v _ _
  | .seq p₁ p₂, rem, hrem, ⟨remMid, hmid, hv₁, hv₂, hpres⟩ => by
      let P₁ := projZeroAll rem (tailScr rComb rem hrem)
      let P₂ := projZeroAll remMid (tailScr rComb remMid hmid)
      have hP₁ : P₁ᴴ = P₁ := projZeroAll_conjTranspose rem _
      have hP₂ : P₂ᴴ = P₂ := projZeroAll_conjTranspose remMid _
      have ih₁ := realizes_of_validCleanRem v rComb p₁ rem hrem hv₁
      have ih₂ := realizes_of_validCleanRem v rComb p₂ remMid hmid hv₂
      have hclean : P₂ * (((p₁.onRegister rComb).toToffCircuit).eval.1 * P₁) =
          ((p₁.onRegister rComb).toToffCircuit).eval.1 * P₁ := by
        apply matrix_ext_ket
        intro β
        simp only [P₁, P₂, mul_mulVec_rev, ket_projZeroAll]
        by_cases hz : ∀ j : Fin rem, β (tailScr rComb rem hrem j) = 0
        · simp only [hz, imp_true_iff, ↓reduceIte, eval_onRegister_rev_ket, ket_projZeroAll]
          have hγ : CleanRem M rem (fun idx ↦ β (rComb idx)) := by
            intro w hw
            have hj : w = ⟨(M - rem) + (w.val - (M - rem)), by omega⟩ := by
              ext; dsimp; omega
            rw [hj]
            exact hz ⟨w.val - (M - rem), by omega⟩
          have hout : ∀ j : Fin remMid, writeRegRev β rComb
              (p₁.evalBits (fun idx ↦ β (rComb idx))) (tailScr rComb remMid hmid j) = 0 := by
            intro j
            dsimp [tailScr]
            rw [writeRegRev_apply_reg]
            exact hpres _ hγ ⟨(M - remMid) + j.val, by omega⟩ (by dsimp; omega)
          simp only [hout, imp_true_iff, ↓reduceIte]
        · simp only [hz, ↓reduceIte, Matrix.mulVec_zero]
      have hseq := realizesCleanUnitary_seq_asym hP₁ hP₂ ih₁ ih₂ hclean
      have heq : (p₂.onRegister rComb).toToffCircuit.eval *
          (p₁.onRegister rComb).toToffCircuit.eval =
          ((RevTempProg.seq p₁ p₂).onRegister rComb).toToffCircuit.eval := by
        simp [RevTempProg.onRegister, RevTempProg.toToffCircuit, Circuit.eval_seq]
      simpa [RevTempProg.onRegister, RevTempProg.toDyn, heq] using hseq
  | .tempAnd c₁ c₂ anc h₁₂ h₁a h₂a body, rem, hrem, ⟨hanc_lo, hvBody, hpresBody⟩ => by
      have hanc_lt : anc.val < M := anc.isLt
      let rem' := M - (anc.val + 1)
      have hrem' : rem' ≤ M := by omega
      have hrem1 : rem' + 1 ≤ M := by omega
      have hrem_le : rem' + 1 ≤ rem := by omega
      have ihBody := realizes_of_validCleanRem v rComb body rem' hrem' hvBody
      have hanc_eq : anc = ⟨M - (rem' + 1), by omega⟩ := by
        ext; dsimp [rem']; omega
      have hdisj : ∀ j : Fin rem', rComb anc ≠ tailScr rComb rem' hrem' j := by
        intro j h
        have hinj := congrArg Fin.val (rComb.wires.injective h)
        dsimp [tailScr, rem'] at hinj
        omega
      let U_body := ((body.onRegister rComb).toToffCircuit).eval
      let U_clean :=
        (((RevTempProg.tempAnd c₁ c₂ anc h₁₂ h₁a h₂a body).onRegister rComb).toToffCircuit).eval
      have hstep := RealizesCleanUnitary.withTempAnd_projZeroAll
        v (rComb c₁) (rComb c₂) (rComb anc)
        (rComb.wires.injective.ne h₁₂) (rComb.wires.injective.ne h₁a) (rComb.wires.injective.ne h₂a)
        rem' (tailScr rComb rem' hrem') hdisj
        ((body.onRegister rComb).toDyn v) U_body U_clean ihBody
        (by
          intro β hanc0 _
          simp only [U_clean, U_body, RevTempProg.onRegister, RevTempProg.toToffCircuit,
            eval_seq_mulVec, ket_TOFF, hanc0, zero_add])
        (by
          intro β hanc0 hscr0
          let γ : BitAssignment M := fun idx ↦ β (rComb idx)
          have hγ_anc : γ anc = 0 := hanc0
          let β₁ : BitAssignment M := Function.update γ anc (γ anc + γ c₁ * γ c₂)
          have hγ₁_clean : CleanRem M rem' β₁ := by
            intro w hw
            have hw_ne : w ≠ anc := wire_ne_of_gt (by dsimp [rem'] at hw; omega)
            dsimp only [β₁]
            rw [Function.update_of_ne hw_ne]
            have hj : w = ⟨(M - rem') + (w.val - (M - rem')), by omega⟩ := by
              ext; dsimp; omega
            rw [hj]
            exact hscr0 ⟨w.val - (M - rem'), by omega⟩
          obtain ⟨hc₁, hc₂, ha⟩ := hpresBody β₁ hγ₁_clean
          have hfinal_anc :
              (RevTempProg.tempAnd c₁ c₂ anc h₁₂ h₁a h₂a body).evalBits γ anc = 0 := by
            dsimp only [RevTempProg.evalBits]
            change Function.update (body.evalBits β₁) anc
              (body.evalBits β₁ anc + body.evalBits β₁ c₁ * body.evalBits β₁ c₂) anc = 0
            rw [Function.update_self, ha, hc₁, hc₂]
            simp [β₁, hγ_anc, Function.update_self, Function.update_of_ne h₁a,
              Function.update_of_ne h₂a, CharTwo.add_self_eq_zero]
          rw [show U_clean.1.mulVec (ket β) = _ from
              eval_onRegister_rev_ket rComb
                (RevTempProg.tempAnd c₁ c₂ anc h₁₂ h₁a h₂a body) β,
            ket_projector_zero, writeRegRev_apply_reg, hfinal_anc]
          simp)
      have hscr_eq : projZeroAll (rem' + 1) (Fin.cons (rComb anc) (tailScr rComb rem' hrem'))
          = projZeroAll (rem' + 1) (tailScr rComb (rem' + 1) hrem1) := by
        rw [hanc_eq, ← tailScr_succ rComb rem' hrem1]
      have hstep' : RealizesCleanUnitary v
          (projZeroAll (rem' + 1) (tailScr rComb (rem' + 1) hrem1))
          (((RevTempProg.tempAnd c₁ c₂ anc h₁₂ h₁a h₂a body).onRegister rComb).toDyn v) U_clean :=
            by
        simpa [RevTempProg.onRegister, RevTempProg.toDyn, hscr_eq] using hstep
      exact RealizesCleanUnitary.mono_proj (projZeroAll_conjTranspose (rem' + 1) _)
        (projZeroAll_conjTranspose rem _) (projZeroAll_tailScr_sub rComb hrem1 hrem hrem_le)
        hstep'
theorem preservesStoreConst_toDyn {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    (v : Var) : ∀ p : RevTempProg n, PreservesStoreConst (p.toDyn v)
  | .nil => PreservesStoreConst.circuit _
  | .cliff _ => PreservesStoreConst.circuit _
  | .seq p₁ p₂ =>
      PreservesStoreConst.seq (preservesStoreConst_toDyn v p₁) (preservesStoreConst_toDyn v p₂)
  | .tempAnd c₁ c₂ anc h₁₂ _ _ body =>
      PreservesStoreConst.seq (PreservesStoreConst.circuit _)
        (PreservesStoreConst.seq (preservesStoreConst_toDyn v body)
          (PreservesStoreConst.andUncompute v c₁ c₂ anc h₁₂))
theorem realizes_clean_action
    {Var : Type} [Fintype Var] [DecidableEq Var] {n kAct mClean mScr : ℕ} [NeZero (2 ^ n)]
    (v : Var) (rAct : QRegister kAct n) (rScr : QRegister mScr n)
    (hdisj : rAct.DisjointWires rScr) (hw_len : mClean ≤ mScr)
    (U : Unitary (2 ^ kAct))
    (f : BitAssignment kAct → BitAssignment kAct)
    (p : RevTempProg (kAct + mClean))
    (hValid : ValidCleanRem (kAct + mClean) mClean p)
    (hActBits : ∀ (α : BitAssignment kAct) (i : Fin kAct),
      p.evalBits (padZeroBits α) (Fin.castAdd mClean i) = f α i)
    (hCleanBits : ∀ (α : BitAssignment kAct) (j : Fin mClean),
      p.evalBits (padZeroBits α) (Fin.natAdd kAct j) = 0)
    (hUnitary : ∀ (β β_out : BitAssignment n),
      (∀ i : Fin kAct, β_out (rAct i) = f (fun q ↦ β (rAct q)) i) →
      (∀ w : Wire n, w ∉ rAct.image → β_out w = β w) →
      (rAct.embedUnitary U).1.mulVec (basisKet β) = basisKet β_out) :
    let rSub : QRegister mClean n := rScr.slice 0 mClean (by omega)
    let rComb : QRegister (kAct + mClean) n := rAct.concat rSub (hdisj.compose_right _)
    DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace rAct rScr U
      ((p.onRegister rComb).toDyn v) := by
  intro rSub rComb
  have hrem : mClean ≤ kAct + mClean := Nat.le_add_left mClean kAct
  have hSmall := realizes_of_validCleanRem v rComb p mClean hrem hValid
  let P_small := projZeroAll mClean (tailScr rComb mClean hrem)
  let P_work := projZeroAll mScr rScr.wires
  have hPs : P_smallᴴ = P_small := projZeroAll_conjTranspose mClean _
  have hPw : P_workᴴ = P_work := projZeroAll_conjTranspose mScr _
  have htail_work : ∀ j : Fin mClean,
      tailScr rComb mClean hrem j = rScr ⟨j.val, by omega⟩ := by
    intro j
    dsimp [tailScr, rComb, rSub]
    have hidx : (⟨(kAct + mClean - mClean) + j.val, by omega⟩ : Fin (kAct + mClean)) =
        Fin.natAdd kAct j := by ext; dsimp; omega
    rw [hidx, QRegister.concat_apply_right, QRegister.slice_apply]
    congr 1; ext; dsimp; omega
  have hsub : P_small * P_work = P_work := by
    apply matrix_ext_ket
    intro β
    simp only [P_small, P_work, mul_mulVec_rev, ket_projZeroAll]
    by_cases hw : ∀ i : Fin mScr, β (rScr i) = 0
    · have hs : ∀ j : Fin mClean, β (tailScr rComb mClean hrem j) = 0 := by
        intro j; rw [htail_work j]; exact hw ⟨j.val, by omega⟩
      simp [hw, hs, ket_projZeroAll]
    · simp [hw]
  have hMono := RealizesCleanUnitary.mono_proj hPs hPw hsub hSmall
  have hUeq : ((p.onRegister rComb).toToffCircuit).eval.1 * P_work =
      (rAct.embedUnitary U).1 * P_work := by
    apply matrix_ext_ket
    intro β
    simp only [P_work, mul_mulVec_rev, ket_projZeroAll]
    by_cases hw : ∀ i : Fin mScr, β (rScr i) = 0
    · simp only [hw, imp_true_iff, ↓reduceIte, eval_onRegister_rev_ket]
      let α : BitAssignment kAct := fun i ↦ β (rAct i)
      have hpad : (fun idx ↦ β (rComb idx)) = padZeroBits α := by
        funext idx
        refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) idx
        · simp [rComb, padZeroBits, α]
        · simp only [rComb, QRegister.concat_apply_right, padZeroBits, Fin.addCases_right]
          have hj' : rSub j = rScr ⟨j.val, by omega⟩ := by
            rw [QRegister.slice_apply]; congr 1; ext; dsimp; omega
          rw [hj']; exact hw _
      rw [hpad]
      let β_out := writeRegRev β rComb (p.evalBits (padZeroBits α))
      have hket_eq : ket β = basisKet β := rfl
      have hket_out : ket β_out = basisKet β_out := rfl
      rw [hket_eq, hket_out]
      symm
      refine hUnitary β β_out (fun i ↦ ?_) (fun w hw_not ↦ ?_)
      · dsimp [β_out]
        have hi : rAct i = rComb (Fin.castAdd mClean i) :=
          (QRegister.concat_apply_left _ _ _ i).symm
        rw [hi, writeRegRev_apply_reg, hActBits α i]
      · dsimp [β_out]
        by_cases hmem : w ∈ Set.range rComb.wires
        · obtain ⟨idx, rfl⟩ := hmem
          rw [writeRegRev_apply_reg]
          induction idx using Fin.addCases with
          | left i =>
              exfalso
              exact hw_not ((QRegister.mem_image rAct _).mpr
                ⟨i, (QRegister.concat_apply_left rAct rSub (hdisj.compose_right _) i).symm⟩)
          | right j =>
              simp only [hCleanBits α j, rComb, QRegister.concat_apply_right]
              have hj' : rSub j = rScr ⟨j.val, by omega⟩ := by
                rw [QRegister.slice_apply]; congr 1; ext; dsimp; omega
              rw [hj']
              exact (hw _).symm
        · exact writeRegRev_apply_of_not_mem _ _ _ _ hmem
    · simp [hw]
  have hTarget := RealizesCleanUnitary.congr_unitary hPw hMono hUeq
  intro M_obs
  obtain ⟨M_out, hM_out⟩ := preservesStoreConst_toDyn v (p.onRegister rComb) M_obs
  refine ⟨M_out, hM_out, ?_⟩
  have hconj := hTarget.2 (fun _ ↦ M_obs) (fun _ _ ↦ rfl) default
  let dyn := (p.onRegister rComb).toDyn v
  have hM_eq : wp dyn.compile (fun _ ↦ M_obs) default = M_out := congrFun hM_out default
  rw [← hM_eq, ← projZeroAll_eq_basisOutcomeProjector_zero rScr]
  simpa [P_work, hPw, wpQAssignCompat, qAssignObsMap, Observable.conj_coe, Unitary.coe_star,
    Matrix.star_eq_conjTranspose, HermitianMat.conj_apply_mat, Matrix.mul_assoc] using
    congrArg Subtype.val hconj
def ScopedAlloc (M K_mut rem remIn : ℕ) (P : BitAssignment M → BitAssignment M → Prop)
    (body p : RevTempProg M) : Prop := ValidCleanRem M rem p ∧ ∀ β : BitAssignment M, CleanRem
    M rem β → (∀ w : Wire M, K_mut ≤ w.val → p.evalBits β w = β w) ∧ ∃ γ : BitAssignment M,
    CleanRem M remIn γ ∧ P β γ ∧ ∀ w : Wire M, w.val < K_mut → p.evalBits β w = body.evalBits
    γ w
theorem ScopedAlloc.id_leaf {M K_mut rem : ℕ} {body : RevTempProg M}
    (hv : ValidCleanRem M rem body) (hhigh : ∀ γ : BitAssignment M, CleanRem M rem γ → ∀ w :
    Wire M, K_mut ≤ w.val → body.evalBits γ w = γ w) : ScopedAlloc M K_mut rem rem
    (fun β γ ↦ γ = β) body body := ⟨hv, fun β hβ ↦ ⟨hhigh β hβ, β, hβ, rfl, fun _ _ ↦ rfl⟩⟩
theorem ScopedAlloc.cast_rem {M K_mut rem₁ rem₂ remIn : ℕ} (h : rem₁ = rem₂)
    {P : BitAssignment M → BitAssignment M → Prop} {body p : RevTempProg M}
    (hs : ScopedAlloc M K_mut rem₁ remIn P body p) : ScopedAlloc M K_mut rem₂ remIn P body p
    := h ▸ hs
theorem ScopedAlloc.comp {M K_mut rem₁ rem₂ rem₃ : ℕ}
    {P₁ P₂ : BitAssignment M → BitAssignment M → Prop} {p₁ p₂ p₃ : RevTempProg M}
    (h₁ : ScopedAlloc M K_mut rem₁ rem₂ P₁ p₂ p₁)
    (h₂ : ScopedAlloc M K_mut rem₂ rem₃ P₂ p₃ p₂) : ScopedAlloc M K_mut rem₁ rem₃
    (fun β δ ↦ ∃ γ, P₁ β γ ∧ P₂ γ δ) p₃ p₁ := by
  refine ⟨h₁.1, fun β hβ ↦ ?_⟩
  obtain ⟨hhigh₁, γ, hclγ, hp₁, hlow₁⟩ := h₁.2 β hβ
  obtain ⟨_, δ, hclδ, hp₂, hlow₂⟩ := h₂.2 γ hclγ
  exact ⟨hhigh₁, δ, hclδ, ⟨γ, hp₁, hp₂⟩, fun w hw ↦ (hlow₁ w hw).trans (hlow₂ w hw)⟩
def withCliffAlloc {M : ℕ} (c : CliffProg M) (body : RevTempProg M) : RevTempProg M :=
  .seq (.cliff c) (.seq body (.cliff c.inv))
@[simp] theorem withCliffAlloc_countTempAnd {M : ℕ} (c : CliffProg M) (body : RevTempProg M) :
    (withCliffAlloc c body).countTempAnd = body.countTempAnd := by
  simp [withCliffAlloc, RevTempProg.countTempAnd]
theorem ScopedAlloc.withCliff {M K_mut rem remIn : ℕ} (hremIn : remIn ≤ M) (hle : remIn ≤ rem)
    (c : CliffProg M) (hc : c.SupportsRange K_mut (M - remIn))
    {P : BitAssignment M → BitAssignment M → Prop} {body : RevTempProg M}
    (hBody : ScopedAlloc M K_mut remIn remIn P body body) : ScopedAlloc M K_mut rem remIn
    (fun β γ ↦ γ = c.eval β) body (withCliffAlloc c body) := by
  refine ⟨?_, fun β hβ ↦ ?_⟩
  · refine ⟨remIn, hremIn, trivial, ?_, fun β hβ w hw ↦ ?_⟩
    · refine ⟨0, Nat.zero_le M, hBody.1, trivial, fun _ _ w hw ↦ absurd hw (by omega)⟩
    · rw [RevTempProg.evalBits, c.eval_outside hc β w (Or.inr hw)]
      exact hβ w (by omega)
  · have hc_clean : CleanRem M remIn (c.eval β) := fun w hw ↦ by
      rw [c.eval_outside hc β w (Or.inr hw)]
      exact hβ w (by omega)
    obtain ⟨hhighB, _⟩ := hBody.2 (c.eval β) hc_clean
    have hcinv_supp : c.inv.SupportsRange K_mut (M - remIn) := c.inv_supportsRange hc
    refine ⟨fun w hw ↦ ?_, c.eval β, hc_clean, rfl, fun w hw ↦ ?_⟩
    · simp only [withCliffAlloc, RevTempProg.evalBits]
      rw [c.inv.eval_congr_ge hcinv_supp _ (c.eval β) hhighB w hw, c.inv_eval]
    · simp only [withCliffAlloc, RevTempProg.evalBits]
      exact c.inv.eval_outside hcinv_supp _ w (Or.inl hw)
def withTempBit {M : ℕ} (c₁ c₂ anc : Wire M) (h₁₂ : c₁ ≠ c₂) (h₁a : c₁ ≠ anc) (h₂a : c₂ ≠ anc)
    (body : RevTempProg M) : RevTempProg M := .tempAnd c₁ c₂ anc h₁₂ h₁a h₂a body
@[simp] theorem withTempBit_countTempAnd {M : ℕ} (c₁ c₂ anc : Wire M)
    (h₁₂ : c₁ ≠ c₂) (h₁a : c₁ ≠ anc) (h₂a : c₂ ≠ anc) (body : RevTempProg M) :
    (withTempBit c₁ c₂ anc h₁₂ h₁a h₂a body).countTempAnd = 1 + body.countTempAnd := rfl
theorem ScopedAlloc.withTemp {M K_mut : ℕ} (pos : ℕ) (hpos : pos + 1 ≤ M) (c₁ c₂ : Wire M)
    (h₁₂ : c₁ ≠ c₂) (hlo₁ : K_mut ≤ c₁.val) (hlo₂ : K_mut ≤ c₂.val) (hc₁ : c₁.val < pos)
    (hc₂ : c₂.val < pos) {body : RevTempProg M} (hBody : ScopedAlloc M K_mut (M - (pos + 1))
    (M - (pos + 1)) (fun β γ ↦ γ = β) body body) : ScopedAlloc M K_mut (M - pos)
    (M - (pos + 1)) (fun β γ ↦ γ = Function.update β ⟨pos, hpos⟩ (β c₁ * β c₂)) body
    (withTempBit c₁ c₂ ⟨pos, hpos⟩ h₁₂ (wire_ne_of_lt hc₁) (wire_ne_of_lt hc₂) body) := by
  let anc : Wire M := ⟨pos, hpos⟩
  have h1a : c₁ ≠ anc := wire_ne_of_lt hc₁
  have h2a : c₂ ≠ anc := wire_ne_of_lt hc₂
  refine ⟨⟨by dsimp [anc]; omega, hBody.1, fun β₁ hβ₁ ↦ ?_⟩, fun β hβ ↦ ?_⟩
  · obtain ⟨hhigh, _⟩ := hBody.2 β₁ hβ₁
    exact ⟨hhigh c₁ hlo₁, hhigh c₂ hlo₂, hhigh anc (by dsimp [anc]; omega)⟩
  · have hanc0 : β anc = 0 := hβ anc (by dsimp [anc]; omega)
    let β₁ := Function.update β anc (β c₁ * β c₂)
    have hβ₁_clean : CleanRem M (M - (pos + 1)) β₁ := fun w hw ↦ by
      have hw_ne : w ≠ anc := wire_ne_of_gt (by dsimp [anc]; omega)
      dsimp only [β₁]; rw [Function.update_of_ne hw_ne]; exact hβ w (by omega)
    obtain ⟨hhighB, _⟩ := hBody.2 β₁ hβ₁_clean
    have hanc_eq : (withTempBit c₁ c₂ anc h₁₂ h1a h2a body).evalBits β =
        Function.update (body.evalBits β₁) anc
          (body.evalBits β₁ anc + body.evalBits β₁ c₁ * body.evalBits β₁ c₂) := by
      simp [withTempBit, RevTempProg.evalBits, hanc0, β₁]
    refine ⟨fun w hw ↦ ?_, β₁, hβ₁_clean, rfl, fun w hw ↦ ?_⟩
    · rw [hanc_eq]
      by_cases hwa : w = anc
      · subst hwa
        rw [Function.update_self, hhighB anc (by dsimp [anc]; omega), hhighB c₁ hlo₁,
          hhighB c₂ hlo₂]
        simp [β₁, hanc0, Function.update_self, Function.update_of_ne h1a,
          Function.update_of_ne h2a, CharTwo.add_self_eq_zero]
      · rw [Function.update_of_ne hwa, hhighB w hw]
        simp [β₁, Function.update_of_ne hwa]
    · rw [hanc_eq]
      exact Function.update_of_ne (wire_ne_of_lt (by dsimp [anc]; omega)) _ _
theorem ScopedAlloc.wrap {M K_mut rem₁ rem₂ rem₃ : ℕ}
    {P₁ P₂ : BitAssignment M → BitAssignment M → Prop} {leaf inner : RevTempProg M}
    {F : RevTempProg M → RevTempProg M} (hF : ScopedAlloc M K_mut rem₂ rem₂ (fun β γ ↦ γ = β)
    inner inner → ScopedAlloc M K_mut rem₁ rem₂ P₁ inner (F inner))
    (hInner : ScopedAlloc M K_mut rem₂ rem₃ P₂ leaf inner) : ScopedAlloc M K_mut rem₁ rem₃
    (fun β δ ↦ ∃ γ, P₁ β γ ∧ P₂ γ δ) leaf (F inner) := ScopedAlloc.comp (hF ⟨hInner.1, fun γ
    hγ ↦ ⟨(hInner.2 γ hγ).1, γ, hγ, rfl, fun _ _ ↦ rfl⟩⟩) hInner
theorem bitsVal_cons_eq {W : ℕ} (f : Fin (W + 1) → ZMod 2) :
    bitsVal f = (f 0).val + 2 * bitsVal (fun j ↦ f j.succ) := by
  rw [bitsVal, Fin.sum_univ_succ]
  simp only [Fin.val_zero, _root_.pow_zero, mul_one, bitsVal, Finset.mul_sum]
  congr 1; refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [Fin.val_succ, pow_succ]; ring
def andXor {M : ℕ} (c₁ c₂ target anc : Wire M) (h₁₂ : c₁ ≠ c₂) (h₁a : c₁ ≠ anc)
    (h₂a : c₂ ≠ anc) (hat : anc ≠ target) : RevTempProg M := .tempAnd c₁ c₂ anc h₁₂ h₁a h₂a
    (.cnot anc target hat)
@[simp] theorem andXor_countTempAnd {M : ℕ} (c₁ c₂ target anc : Wire M)
    (h₁₂ : c₁ ≠ c₂) (h₁a : c₁ ≠ anc) (h₂a : c₂ ≠ anc) (hat : anc ≠ target) :
    (andXor c₁ c₂ target anc h₁₂ h₁a h₂a hat).countTempAnd = 1 := rfl
theorem andXor_spec {M rem : ℕ}
    (c₁ c₂ target anc : Wire M)
    (h₁₂ : c₁ ≠ c₂) (h₁t : c₁ ≠ target) (h₂t : c₂ ≠ target)
    (hc₁ : c₁.val < anc.val) (hc₂ : c₂.val < anc.val) (ht : target.val < anc.val)
    (hanc_rem : M - rem ≤ anc.val) :
    let p := andXor c₁ c₂ target anc h₁₂
      (wire_ne_of_lt hc₁) (wire_ne_of_lt hc₂) (wire_ne_of_gt ht)
    ValidCleanRem M rem p ∧
      ∀ β : BitAssignment M, CleanRem M rem β →
        p.evalBits β = Function.update β target (β target + β c₁ * β c₂) := by
  intro p
  have h1a : c₁ ≠ anc := wire_ne_of_lt hc₁
  have h2a : c₂ ≠ anc := wire_ne_of_lt hc₂
  have hat : anc ≠ target := wire_ne_of_gt ht
  refine ⟨⟨hanc_rem, trivial, fun β₁ _ ↦ ?_⟩, fun β hβ ↦ ?_⟩
  · simp [RevTempProg.cnot, RevTempProg.evalBits, CliffProg.eval,
      Function.update_of_ne h₁t, Function.update_of_ne h₂t, Function.update_of_ne hat]
  · have hanc0 : β anc = 0 := hβ anc hanc_rem
    funext w
    by_cases hw_a : w = anc
    · subst hw_a
      simp [p, andXor, RevTempProg.cnot, RevTempProg.evalBits, CliffProg.eval, hanc0,
        Function.update_self, Function.update_of_ne h₁t, Function.update_of_ne h₂t,
        Function.update_of_ne hat, Function.update_of_ne h1a, Function.update_of_ne h2a,
        CharTwo.add_self_eq_zero]
    · by_cases hw_t : w = target
      · subst hw_t
        simp [p, andXor, RevTempProg.cnot, RevTempProg.evalBits, CliffProg.eval, hanc0,
          Function.update_self, Function.update_of_ne hw_a]
      · simp [p, andXor, RevTempProg.cnot, RevTempProg.evalBits, CliffProg.eval,
          Function.update_of_ne hw_a, Function.update_of_ne hw_t]
def withUnarySplit {M : ℕ} (cur : ℕ) (hcur : cur + 1 ≤ M) (loWire sel : Wire M)
    (hlo_sel : loWire ≠ sel) (hlo : loWire.val < cur) (hsel : sel.val < cur)
    (body : RevTempProg M) : RevTempProg M :=
  let hiWire : Wire M := ⟨cur, by omega⟩
  withTempBit loWire sel hiWire hlo_sel
    (wire_ne_of_lt (by dsimp [hiWire]; omega))
    (wire_ne_of_lt (by dsimp [hiWire]; omega))
    (withCliffAlloc (.cnot hiWire loWire (wire_ne_of_gt (by dsimp [hiWire]; omega))) body)
@[simp] theorem withUnarySplit_countTempAnd {M : ℕ} (cur : ℕ) (hcur : cur + 1 ≤ M)
    (loWire sel : Wire M) (hlo_sel : loWire ≠ sel) (hlo : loWire.val < cur)
    (hsel : sel.val < cur) (body : RevTempProg M) : (withUnarySplit cur hcur loWire sel
    hlo_sel hlo hsel body).countTempAnd = 1 + body.countTempAnd := by
  simp [withUnarySplit]
def unarySplitSetup {M : ℕ} (cur : ℕ) (hcur : cur + 1 ≤ M) (loWire sel : Wire M)
    (β : BitAssignment M) : BitAssignment M :=
  Function.update
    (Function.update β ⟨cur, by omega⟩ (β loWire * β sel))
    loWire (β loWire + β loWire * β sel)
theorem ScopedAlloc.withUnarySplit_alloc {M K_mut : ℕ} (cur : ℕ) (hcur : cur + 1 ≤ M)
    (loWire sel : Wire M) (hlo_sel : loWire ≠ sel) (hlo_lo : K_mut ≤ loWire.val)
    (hsel_lo : K_mut ≤ sel.val) (hlo : loWire.val < cur) (hsel : sel.val < cur) {remLeaf : ℕ}
    {P : BitAssignment M → BitAssignment M → Prop} {leaf body : RevTempProg M}
    (hBody : ScopedAlloc M K_mut (M - (cur + 1)) remLeaf P leaf body) : ScopedAlloc M K_mut
    (M - cur) remLeaf (fun β δ ↦ P (unarySplitSetup cur hcur loWire sel β) δ) leaf
    (withUnarySplit cur hcur loWire sel hlo_sel hlo hsel body) := by
  let remIn := M - (cur + 1)
  let hiWire : Wire M := ⟨cur, by omega⟩
  have h1 := ScopedAlloc.wrap
    (fun hId ↦ ScopedAlloc.withCliff (M := M) (K_mut := K_mut) (rem := remIn) (remIn := remIn)
      (by dsimp [remIn]; omega) le_rfl
      (.cnot hiWire loWire (wire_ne_of_gt (by dsimp [hiWire]; omega)))
      ⟨⟨by dsimp [hiWire]; omega, by dsimp [hiWire, remIn]; omega⟩,
       ⟨hlo_lo, by dsimp [remIn]; omega⟩⟩ hId)
    hBody
  have h2 := ScopedAlloc.wrap
    (fun hId ↦ ScopedAlloc.withTemp (M := M) (K_mut := K_mut) cur hcur loWire sel hlo_sel
      hlo_lo hsel_lo hlo hsel hId)
    h1
  refine ⟨h2.1, fun β hβ ↦ ?_⟩
  obtain ⟨hhigh, δ, hclδ, ⟨γ₁, rfl, γ₂, rfl, hP⟩, hlow⟩ := h2.2 β hβ
  have heq : (CliffProg.cnot hiWire loWire (wire_ne_of_gt (by dsimp [hiWire]; omega))).eval
      (Function.update β (⟨cur, hcur⟩ : Wire M) (β loWire * β sel)) =
      unarySplitSetup cur hcur loWire sel β := by
    dsimp [unarySplitSetup, hiWire, CliffProg.eval]
    funext w
    have hne : loWire ≠ ⟨cur, hcur⟩ := wire_ne_of_lt hlo
    by_cases hwl : w = loWire
    · subst hwl; simp [Function.update_self, Function.update_of_ne hne]
    · simp [Function.update_of_ne hwl]
  rw [heq] at hP
  exact ⟨hhigh, δ, hclδ, hP, hlow⟩
def withUnarySplitRange {M : ℕ} (base L : ℕ) (sel : Wire M) (hsel : sel.val < base)
    (hcur : base + 2 * L ≤ M) :
    (K : ℕ) → (hK : K ≤ L) →
    RevTempProg M → RevTempProg M
  | 0, _, body => body
  | K + 1, _, body =>
      let idx := L - (K + 1)
      let pos := base + L + idx
      withUnarySplit pos (by dsimp [pos, idx]; omega)
        ⟨base + idx, by dsimp [idx]; omega⟩ sel
        (wire_ne_of_gt (by dsimp; omega))
        (by dsimp [pos]; omega) (by dsimp [pos]; omega)
        (withUnarySplitRange base L sel hsel hcur K (by omega) body)
@[simp] theorem withUnarySplitRange_countTempAnd {M : ℕ} (base L : ℕ) (sel : Wire M)
    (hsel : sel.val < base) (hcur : base + 2 * L ≤ M) :
    ∀ (K : ℕ) (hK : K ≤ L) (body : RevTempProg M),
      (withUnarySplitRange base L sel hsel hcur K hK body).countTempAnd = K + body.countTempAnd :=
        by
  intro K
  induction K with
  | zero => intro _ _; simp [withUnarySplitRange]
  | succ K ih =>
      intro hK body
      simp only [withUnarySplitRange, withUnarySplit_countTempAnd, ih (by omega) body]
      omega
def SplitRangePost {M : ℕ} (base L K : ℕ) (hcur : base + 2 * L ≤ M) (sel : Wire M)
    (β γ : BitAssignment M) : Prop :=
  (∀ w : Wire M,
    (w.val < base + (L - K) ∨ (base + L ≤ w.val ∧ w.val < base + L + (L - K))) →
    γ w = β w) ∧
  (∀ (i : ℕ) (_ : L - K ≤ i) (_ : i < L),
    γ ⟨base + i, by omega⟩ = β ⟨base + i, by omega⟩ + β ⟨base + i, by omega⟩ * β sel ∧
    γ ⟨base + L + i, by omega⟩ = β ⟨base + i, by omega⟩ * β sel)
theorem ScopedAlloc.withUnarySplitRange_alloc {M K_mut : ℕ} (base L : ℕ) (sel : Wire M)
    (hsel_lo : K_mut ≤ sel.val) (hsel : sel.val < base) (hcur : base + 2 * L ≤ M) : ∀ (K : ℕ)
    (hK : K ≤ L) {remLeaf : ℕ} {P : BitAssignment M → BitAssignment M → Prop}
    {leaf body : RevTempProg M}, ScopedAlloc M K_mut (M - (base + 2 * L)) remLeaf P leaf body
    → ScopedAlloc M K_mut (M - (base + 2 * L - K)) remLeaf
    (fun β δ ↦ ∃ γ, SplitRangePost base L K hcur sel β γ ∧ P γ δ) leaf
    (withUnarySplitRange base L sel hsel hcur K hK body) := by
  intro K
  induction K with
  | zero =>
      intro _ _ _ _ _ hBody
      have h0 : base + 2 * L - 0 = base + 2 * L := by omega
      refine ⟨(hBody.cast_rem (by omega)).1, fun β hβ ↦ ?_⟩
      obtain ⟨hhigh, δ, hclδ, hP, hlow⟩ := (hBody.cast_rem (by omega)).2 β hβ
      exact ⟨hhigh, δ, hclδ, ⟨β, ⟨fun _ _ ↦ rfl, fun _ hlo hhi ↦ absurd (lt_of_le_of_lt hlo
        hhi) (by omega)⟩, hP⟩, hlow⟩
  | succ K ih =>
      intro hK _ P leaf body hBody
      let idx := L - (K + 1)
      let pos := base + L + idx
      have hInner := ih (by omega) hBody
      have hStep := ScopedAlloc.withUnarySplit_alloc (M := M) (K_mut := K_mut)
        pos (by dsimp [pos, idx]; omega)
        ⟨base + idx, by dsimp [idx]; omega⟩ sel
        (wire_ne_of_gt (by dsimp; omega))
        (by dsimp [idx]; omega) hsel_lo
        (by dsimp [pos]; omega) (by dsimp [pos]; omega)
        (hInner.cast_rem (by dsimp [pos, idx]; omega))
      have hrem_eq : M - pos = M - (base + 2 * L - (K + 1)) := by dsimp [pos, idx]; omega
      refine ⟨(hStep.cast_rem hrem_eq).1, fun β hβ ↦ ?_⟩
      obtain ⟨hhigh, δ, hclδ, ⟨γ, ⟨hγ_below, hγ_split⟩, hP⟩, hlow⟩ :=
        (hStep.cast_rem hrem_eq).2 β hβ
      let β₁ := unarySplitSetup pos (by dsimp [pos, idx]; omega)
        ⟨base + idx, by dsimp [idx]; omega⟩ sel β
      have hsel_eq : β₁ sel = β sel := by
        dsimp [β₁, unarySplitSetup]
        rw [Function.update_of_ne (wire_ne_of_lt (by dsimp; omega)),
          Function.update_of_ne (wire_ne_of_lt (by dsimp [pos]; omega))]
      refine ⟨hhigh, δ, hclδ, ⟨γ, ⟨fun w hw ↦ ?_, fun i hilo hihi ↦ ?_⟩, hP⟩, hlow⟩
      · have hw' : w.val < base + (L - K) ∨ (base + L ≤ w.val ∧ w.val < base + L + (L - K)) := by
          rcases hw with h1 | ⟨h2, h3⟩
          · exact Or.inl (by omega)
          · exact Or.inr ⟨h2, by omega⟩
        have hw_ne_lo : w ≠ ⟨base + idx, by dsimp [idx]; omega⟩ := by
          intro h; have hv := congrArg Fin.val h; dsimp [idx] at hv
          rcases hw with h1 | ⟨h2, h3⟩ <;> omega
        have hw_ne_hi : w ≠ ⟨pos, by dsimp [pos, idx]; omega⟩ := by
          intro h; have hv := congrArg Fin.val h; dsimp [pos, idx] at hv
          rcases hw with h1 | ⟨h2, h3⟩ <;> omega
        rw [hγ_below w hw']
        dsimp [β₁, unarySplitSetup]
        rw [Function.update_of_ne hw_ne_lo, Function.update_of_ne hw_ne_hi]
      · by_cases hi_idx : i = idx
        · subst hi_idx
          let wLo : Wire M := ⟨base + idx, by dsimp [idx]; omega⟩
          let wHi : Wire M := ⟨pos, by dsimp [pos, idx]; omega⟩
          have hwHi_eq : (⟨base + L + idx, by dsimp [idx]; omega⟩ : Wire M) = wHi := rfl
          have hlo_keep : γ wLo = β₁ wLo := hγ_below wLo (Or.inl (by dsimp [wLo, idx]; omega))
          have hhi_keep : γ wHi = β₁ wHi :=
            hγ_below wHi (Or.inr ⟨by dsimp [wHi, pos]; omega, by dsimp [wHi, pos, idx]; omega⟩)
          rw [hwHi_eq, hlo_keep, hhi_keep]
          have hne_lohi : wLo ≠ wHi := wire_ne_of_lt (by dsimp [wLo, wHi, pos]; omega)
          have hb1_lo : β₁ wLo = β wLo + β wLo * β sel := by
            dsimp [β₁, unarySplitSetup, wLo]
            exact Function.update_self _ _ _
          have hb1_hi : β₁ wHi = β wLo * β sel := by
            dsimp [β₁, unarySplitSetup, wLo, wHi]
            rw [Function.update_of_ne hne_lohi.symm, Function.update_self]
          exact ⟨hb1_lo, hb1_hi⟩
        · have hi_gt : L - K ≤ i := by dsimp [idx] at hi_idx; omega
          obtain ⟨h1, h2⟩ := hγ_split i hi_gt hihi
          let wI : Wire M := ⟨base + i, by omega⟩
          have hn1 : wI ≠ ⟨base + idx, by dsimp [idx]; omega⟩ := by
            intro h; have hv := congrArg Fin.val h; dsimp [wI] at hv; omega
          have hn2 : wI ≠ ⟨pos, by dsimp [pos, idx]; omega⟩ := by
            intro h; have hv := congrArg Fin.val h; dsimp [wI, pos, idx] at hv; omega
          have hbi_eq : β₁ wI = β wI := by
            dsimp [β₁, unarySplitSetup]
            rw [Function.update_of_ne hn1, Function.update_of_ne hn2]
          exact ⟨h1.trans (by dsimp [β₁, wI] at hbi_eq hsel_eq; rw [hbi_eq, hsel_eq]),
            h2.trans (by dsimp [β₁, wI] at hbi_eq hsel_eq; rw [hbi_eq, hsel_eq])⟩
def condCnot {M : ℕ} (cond : Bool) (c t : Wire M) (h : c ≠ t) : CliffProg M :=
  if cond then .cnot c t h else .nil
def fanoutUnaryToTarget {M : ℕ} (uBase N : ℕ) (target : Wire M)
    (hdisj : target.val < uBase ∨ uBase + N ≤ target.val)
    (hbound : uBase + N ≤ M)
    (pred : ℕ → Bool) : (K : ℕ) → (hK : K ≤ N) → CliffProg M
  | 0, _ => .nil
  | K + 1, _ =>
      .seq (fanoutUnaryToTarget uBase N target hdisj hbound pred K (by omega))
        (condCnot (pred K) ⟨uBase + K, by omega⟩ target
          (fun heq ↦ by have hv := congrArg Fin.val heq; dsimp at hv; omega))
theorem fanoutUnaryToTarget_supportsRange {M : ℕ} (uBase N hi : ℕ) (target : Wire M)
    (hdisj : target.val < uBase ∨ uBase + N ≤ target.val) (hbound : uBase + N ≤ M)
    (ht_lo : uBase ≤ target.val) (ht_hi : target.val < hi) (hu_hi : uBase + N ≤ hi)
    (pred : ℕ → Bool) : ∀ (K : ℕ) (hK : K ≤ N), (fanoutUnaryToTarget uBase N target hdisj
    hbound pred K hK).SupportsRange uBase hi := by
  intro K
  induction K with
  | zero => intro _; trivial
  | succ K ih =>
      intro hK
      refine ⟨ih (by omega), ?_⟩
      dsimp [condCnot]
      split_ifs
      · exact ⟨⟨by dsimp; omega, by dsimp; omega⟩,⟨ht_lo, ht_hi⟩⟩
      · trivial
theorem fanoutUnaryToTarget_eval {M : ℕ} (uBase N : ℕ) (target : Wire M)
    (hdisj : target.val < uBase ∨ uBase + N ≤ target.val)
    (hbound : uBase + N ≤ M) (pred : ℕ → Bool) :
    ∀ (K : ℕ) (hK : K ≤ N) (β : BitAssignment M),
      (fanoutUnaryToTarget uBase N target hdisj hbound pred K hK).eval β =
        Function.update β target
          (β target + ∑ k : Fin K, if pred k.val then β ⟨uBase + k.val, by omega⟩ else 0) := by
  intro K
  induction K with
  | zero => intro _ β; simp [fanoutUnaryToTarget, CliffProg.eval]
  | succ K ih =>
      intro hK β
      have ihβ := ih (by omega) β
      have hneK : (⟨uBase + K, by omega⟩ : Wire M) ≠ target :=
        fun heq ↦ by have hv := congrArg Fin.val heq; dsimp at hv; omega
      have hsrc : ∀ β' : BitAssignment M,
          (Function.update β' target (β' target + ∑ k : Fin K,
            if pred k.val then β' ⟨uBase + k.val, by omega⟩ else 0))
              ⟨uBase + K, by omega⟩ =
            β' ⟨uBase + K, by omega⟩ := fun β' ↦ Function.update_of_ne hneK _ _
      simp only [fanoutUnaryToTarget, condCnot, CliffProg.eval]
      split_ifs with hp
      · simp only [CliffProg.eval, ihβ, hsrc, Function.update_idem, Function.update_self,
          Fin.sum_univ_castSucc, Fin.val_castSucc, Fin.val_last, hp, ↓reduceIte, add_assoc]
      · have hpf : pred K = false := Bool.eq_false_iff.mpr hp
        simp only [CliffProg.eval, ihβ, Fin.sum_univ_castSucc, Fin.val_castSucc, Fin.val_last,
          hpf, Bool.false_eq_true, ↓reduceIte, add_zero]
def selectSwapXorBit {M : ℕ} (uBase L : ℕ) (hM : uBase + L + 2 ≤ M)
    (lsb target : Wire M) (hlsb : lsb.val < uBase) (ht : target.val < uBase)
    (table : Fin (2 * L) → ℕ) (j : ℕ) : RevTempProg M :=
  let scrD : Wire M := ⟨uBase + L, by omega⟩
  let ancOut : Wire M := ⟨uBase + L + 1, by omega⟩
  let predD : ℕ → Bool := fun a ↦
    if ha : a < L then
      xor ((table ⟨2 * a, by omega⟩).testBit j) ((table ⟨2 * a + 1, by omega⟩).testBit j)
    else false
  let predB0 : ℕ → Bool := fun a ↦
    if ha : a < L then (table ⟨2 * a, by omega⟩).testBit j else false
  let cFanD := fanoutUnaryToTarget uBase L scrD (Or.inr (by dsimp [scrD]; omega))
    (by omega) predD L le_rfl
  let cFanB0 := fanoutUnaryToTarget uBase L target (Or.inl ht) (by omega) predB0 L le_rfl
  withCliffAlloc cFanD
    (.seq
      (andXor lsb scrD target ancOut
        (wire_ne_of_lt (by dsimp [scrD]; omega))
        (wire_ne_of_lt (by dsimp [ancOut]; omega))
        (wire_ne_of_lt (by dsimp [scrD, ancOut]; omega))
        (wire_ne_of_gt (by dsimp [ancOut]; omega)))
      (.cliff cFanB0))
@[simp] theorem selectSwapXorBit_countTempAnd {M : ℕ} (uBase L : ℕ) (hM : uBase + L + 2 ≤ M)
    (lsb target : Wire M) (hlsb : lsb.val < uBase) (ht : target.val < uBase)
    (table : Fin (2 * L) → ℕ) (j : ℕ) :
    (selectSwapXorBit uBase L hM lsb target hlsb ht table j).countTempAnd = 1 := by
  simp [selectSwapXorBit]
theorem selectSwapXorBit_pres_ne {M : ℕ} (uBase L : ℕ) (hM : uBase + L + 2 = M)
    (lsb target : Wire M) (hlsb : lsb.val < uBase) (ht : target.val < uBase)
    (hlt : lsb ≠ target) (table : Fin (2 * L) → ℕ) (j : ℕ) :
    let hM' : uBase + L + 2 ≤ M := by omega
    let p := selectSwapXorBit uBase L hM' lsb target hlsb ht table j
    ValidCleanRem M 2 p ∧
    ∀ (γ : BitAssignment M), CleanRem M 2 γ →
      ∀ (w : Wire M), w ≠ target → p.evalBits γ w = γ w := by
  subst hM
  intro hM' p
  let scrD : Wire (uBase + L + 2) := ⟨uBase + L, by omega⟩
  let ancOut : Wire (uBase + L + 2) := ⟨uBase + L + 1, by omega⟩
  let predD : ℕ → Bool := fun a ↦
    if ha : a < L then
      xor ((table ⟨2 * a, by omega⟩).testBit j) ((table ⟨2 * a + 1, by omega⟩).testBit j)
    else false
  let predB0 : ℕ → Bool := fun a ↦
    if ha : a < L then (table ⟨2 * a, by omega⟩).testBit j else false
  let cFanD := fanoutUnaryToTarget uBase L scrD (Or.inr (by dsimp [scrD]; omega))
    (by omega) predD L le_rfl
  let cFanB0 := fanoutUnaryToTarget uBase L target (Or.inl ht) (by omega) predB0 L le_rfl
  have hsuppD : cFanD.SupportsRange uBase (uBase + L + 1) :=
    fanoutUnaryToTarget_supportsRange uBase L (uBase + L + 1) scrD
      (Or.inr (by dsimp [scrD]; omega)) (by omega) (by dsimp [scrD]; omega)
      (by dsimp [scrD]; omega) (by omega) predD L le_rfl
  have hAnd := andXor_spec (M := uBase + L + 2) (rem := 1) lsb scrD target ancOut
    (wire_ne_of_lt (by dsimp [scrD]; omega)) hlt (wire_ne_of_gt (by dsimp [scrD]; omega))
    (by dsimp [ancOut]; omega) (by dsimp [scrD, ancOut]; omega) (by dsimp [ancOut]; omega)
    (by dsimp [ancOut]; omega)
  have hvInner : ValidCleanRem (uBase + L + 2) 1
      (.seq (andXor lsb scrD target ancOut
        (wire_ne_of_lt (by dsimp [scrD]; omega))
        (wire_ne_of_lt (by dsimp [ancOut]; omega))
        (wire_ne_of_lt (by dsimp [scrD, ancOut]; omega))
        (wire_ne_of_gt (by dsimp [ancOut]; omega))) (.cliff cFanB0)) :=
    ⟨0, Nat.zero_le _, hAnd.1, trivial, fun _ _ w hw ↦ absurd hw (by omega)⟩
  have hvAll : ValidCleanRem (uBase + L + 2) 2 p := by
    refine ⟨1, by omega, trivial,
      ⟨0, Nat.zero_le _, hvInner, trivial, fun _ _ w hw ↦ absurd hw (by omega)⟩,
      fun γ hγ w hw ↦ ?_⟩
    rw [RevTempProg.evalBits, cFanD.eval_outside hsuppD γ w (Or.inr (by omega))]
    exact hγ w (by omega)
  refine ⟨hvAll, fun γ hγ w hw_ne ↦ ?_⟩
  have hγ1_cl : CleanRem (uBase + L + 2) 1 (cFanD.eval γ) := fun u hu ↦
    (cFanD.eval_outside hsuppD γ u (Or.inr (by omega))).trans (hγ u (by omega))
  let γ₂ := (andXor lsb scrD target ancOut
    (wire_ne_of_lt (by dsimp [scrD]; omega))
    (wire_ne_of_lt (by dsimp [ancOut]; omega))
    (wire_ne_of_lt (by dsimp [scrD, ancOut]; omega))
    (wire_ne_of_gt (by dsimp [ancOut]; omega))).evalBits (cFanD.eval γ)
  have hγ₂_eq : γ₂ = Function.update (cFanD.eval γ) target
      (cFanD.eval γ target + cFanD.eval γ lsb * cFanD.eval γ scrD) :=
    hAnd.2 (cFanD.eval γ) hγ1_cl
  let γ₃ := cFanB0.eval γ₂
  have hγ₃_ne : ∀ u : Wire (uBase + L + 2), u ≠ target → γ₃ u = cFanD.eval γ u := fun u hu ↦ by
    dsimp [γ₃, cFanB0]
    rw [fanoutUnaryToTarget_eval, Function.update_of_ne hu, hγ₂_eq, Function.update_of_ne hu]
  change cFanD.inv.eval γ₃ w = γ w
  by_cases hwu : uBase ≤ w.val
  · rw [cFanD.inv.eval_congr_ge (cFanD.inv_supportsRange hsuppD) γ₃ (cFanD.eval γ)
      (fun u hu ↦ hγ₃_ne u (wire_ne_of_gt (by omega))) w hwu, cFanD.inv_eval]
  · rw [cFanD.inv.eval_outside (cFanD.inv_supportsRange hsuppD) γ₃ w (Or.inl (by omega)),
      hγ₃_ne w hw_ne, cFanD.eval_outside hsuppD γ w (Or.inl (by omega))]
def selectSwapXorBitLoop {M : ℕ} (uBase L W : ℕ) (hW_le : W ≤ uBase) (hM : uBase + L + 2 ≤ M)
    (lsb : Wire M) (_hlsb_lo : W ≤ lsb.val) (hlsb_hi : lsb.val < uBase)
    (table : Fin (2 * L) → ℕ) :
    (remW : ℕ) → (hW : remW ≤ W) → RevTempProg M
  | 0, _ => .nil
  | remW + 1, hW =>
      let j := W - (remW + 1)
      .seq
        (selectSwapXorBit uBase L hM lsb ⟨j, by omega⟩ hlsb_hi (by dsimp [j]; omega) table j)
        (selectSwapXorBitLoop uBase L W hW_le hM lsb _hlsb_lo hlsb_hi table remW (by omega))
@[simp] theorem selectSwapXorBitLoop_countTempAnd {M : ℕ} (uBase L W : ℕ) (hW_le : W ≤ uBase)
    (hM : uBase + L + 2 ≤ M) (lsb : Wire M) (hlsb_lo : W ≤ lsb.val)
    (hlsb_hi : lsb.val < uBase) (table : Fin (2 * L) → ℕ) : ∀ (remW : ℕ) (hW : remW ≤ W),
    (selectSwapXorBitLoop uBase L W hW_le hM lsb hlsb_lo hlsb_hi table remW hW).countTempAnd =
    remW := by
  intro remW
  induction remW with
  | zero => intro _; rfl
  | succ remW ih =>
      intro hW
      simp only [selectSwapXorBitLoop, RevTempProg.countTempAnd_seq,
        selectSwapXorBit_countTempAnd, ih (by omega)]
      omega
theorem selectSwapXorBitLoop_high {M : ℕ} (uBase L W : ℕ) (hW_le : W ≤ uBase)
    (hM : uBase + L + 2 = M) (lsb : Wire M) (hlsb_lo : W ≤ lsb.val) (hlsb_hi : lsb.val < uBase)
    (table : Fin (2 * L) → ℕ) :
    let hM' : uBase + L + 2 ≤ M := by omega
    ∀ (remW : ℕ) (hW : remW ≤ W),
      let p := selectSwapXorBitLoop uBase L W hW_le hM' lsb hlsb_lo hlsb_hi table remW hW
      ValidCleanRem M 2 p ∧
      ∀ (γ : BitAssignment M), CleanRem M 2 γ →
        ∀ (w : Wire M), W ≤ w.val → p.evalBits γ w = γ w := by
  subst hM
  intro hM' remW
  induction remW with
  | zero => intro _; exact ⟨trivial, fun _ _ _ _ ↦ rfl⟩
  | succ remW ih =>
      intro hW
      let j := W - (remW + 1)
      obtain ⟨hv1, hne1⟩ := selectSwapXorBit_pres_ne uBase L rfl lsb ⟨j, by omega⟩ hlsb_hi
        (by dsimp [j]; omega) (wire_ne_of_gt (by dsimp [j]; omega)) table j
      obtain ⟨hv2, hhi2⟩ := ih (by omega)
      have hcl1 : ∀ γ, CleanRem (uBase + L + 2) 2 γ → CleanRem (uBase + L + 2) 2
          ((selectSwapXorBit uBase L hM' lsb ⟨j, by omega⟩ hlsb_hi (by dsimp [j]; omega)
            table j).evalBits γ) := fun γ hγ w hw ↦
        (hne1 γ hγ w (wire_ne_of_gt (by dsimp [j]; omega))).trans (hγ w hw)
      exact ⟨⟨2, by omega, hv1, hv2, hcl1⟩, fun γ hγ w hw ↦
        (hhi2 _ (hcl1 γ hγ) w hw).trans (hne1 γ hγ w (wire_ne_of_gt (by dsimp [j]; omega)))⟩
end RevTempPerm
namespace NuclearTwistDisentangleSum288
open Operator Matrix _root_.DynamicCircuit DynCircuitExt QProg HermitianMat SpecsAux
open SpecsAux.SpecMirror
open BchCubeDecoder
open DyadicQft64 hiding dyadicTurn phaseGradKet
open DyadicQft64.PhasePerm
open SpecsAux.PhaseGradCatalystCore
open NuclearTwistAndXor654Concrete hiding fullSysCoreWires
  IntertwinesLocalCat
open NuclearTwistRealizes
open RevTempPerm
open scoped Matrix BigOperators ComplexOrder MatrixOrder Circuit.Notation
theorem permUnitaryBits_inv_eq_self {k : ℕ} (f : BitAssignment k → BitAssignment k)
    (hf : Function.Involutive f) : (Operator.permutationUnitary ((basisBitsEquiv k).trans
    ((Equiv.ofBijective f hf.bijective).trans (basisBitsEquiv k).symm)))⁻¹ =
    Operator.permutationUnitary ((basisBitsEquiv k).trans ((Equiv.ofBijective f
    hf.bijective).trans (basisBitsEquiv k).symm)) := by
  set u : Unitary (2 ^ k) := Operator.permutationUnitary
    ((basisBitsEquiv k).trans
      ((Equiv.ofBijective f hf.bijective).trans (basisBitsEquiv k).symm))
  apply mul_eq_one_iff_inv_eq.mp
  apply Subtype.ext
  apply matrix_ext_basisKet
  intro β
  have hu : ∀ γ : BitAssignment k, u.1.mulVec (basisKet γ) = basisKet (f γ) := fun γ ↦ by
    have hid : ((QRegExt.idReg k).embedUnitary u).1 = u.1 :=
      congrArg Subtype.val (embedUnitary_idReg_eq u)
    rw [← hid]
    exact embedUnitary_perm_mulVec_basisKet (QRegExt.idReg k) _ γ (f γ)
      (fun q ↦ by
        rw [QRegExt.idReg_apply, basisBits_perm_ofBijective f hf.bijective]
        exact congrFun (congrArg f (funext fun r ↦ by rw [QRegExt.idReg_apply])) q)
      (fun z hz ↦ False.elim (hz ((QRegister.mem_image (QRegExt.idReg k) z).mpr ⟨z, rfl⟩)))
  rw [Submonoid.coe_mul, OneMemClass.coe_one, Matrix.one_mulVec, mul_mulVec_rev, hu β,
    hu (f β), hf β]
end NuclearTwistDisentangleSum288
end
end ModNuclearTwistDisentangleSum288

section ModPosSlots24MergedVepBound
@[expose] public section
namespace PosSlots24MergedVepBoundAlt
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
end PosSlots24MergedVepBoundAlt
namespace PosSlots24MergedVepBound
section ConfigPosSlots24MergedVepBound
set_option maxRecDepth 4096
set_option exponentiation.threshold 16
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup
local instance (priority := 1000000) mergedVep_neZero_two_pow (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩
open Operator Matrix Real SpecsAux
open SpecsAux.SpecMirror
open SpecsAux.BridgeFermionicComm
open SpecsAux.BridgeFermionicComm.SpecInner
open SpecsAux.FullScaleBESector (AgreesOnFermionicSector)
open SpecsAux.SpecMirror.SixChannelHamiltonianSplit (sixChannelShifted
  norm_projector_le_one)
open SpecsAux.DyadicSubgridToeplitz128 (oneElectronPhase)
open SpecsAux.DyadicSubgridToeplitz512AndShift (NyqGrid3D256 NyqFine3D512
  nyq512ProjEquiv3D sum_nyqProj256_eq_fine512 omega512 omega512_zero omega512_add star_omega512
  omega512_mul_512 sum_omega512_of_abs_lt nyquist512Char3D nyquist512Char3D_add_left
  sum_nyquist512Char3D_of_abs_lt InProjMomGrid3D InElecMomGrid3D inProjMomGrid3D_of_state
  projSubGridElem256_3D star_projSubGridElem256_3D_mul)
open scoped Matrix BigOperators Matrix.Norms.L2Operator
theorem ite_eq_of_pos {α : Type*} {P : Prop} {_h : Decidable P} (hp : P) {a b : α} :
    (if P then a else b) = a := by
  simp [hp]
theorem ite_eq_of_neg {α : Type*} {P : Prop} {_h : Decidable P} (hp : ¬P) {a b : α} :
    (if P then a else b) = b := by
  simp [hp]
theorem dite_eq_of_pos {α : Type*} {P : Prop} {_h : Decidable P} (hp : P) {a : P → α}
    {b : ¬P → α} : (if h : P then a h else b h) = a hp := by
  simp [hp]
theorem dite_eq_of_neg {α : Type*} {P : Prop} {_h : Decidable P} (hp : ¬P) {a : P → α}
    {b : ¬P → α} : (if h : P then a h else b h) = b hp := by
  simp [hp]
noncomputable def cfgProjZ512 (zP : NyqFine3D512) : Configuration where
  nuclei := fun _ w ↦ ((zP w).val : ℝ) * (cellVolume ^ ((1 : ℝ) / 3) / 512)
  projectileMomentum := 0
  momentum_le := by
    simp [waveNumberSq, waveVector, dotProduct]
theorem cellLength_ne_zero : cellVolume ^ ((1 : ℝ) / 3) ≠ 0 := by
  have hpos : (0 : ℝ) < cellVolume := by
    unfold cellVolume
    norm_num
  exact ne_of_gt (Real.rpow_pos_of_pos hpos _)
theorem oneElectronPhase_cfgProjZ512 (zP : NyqFine3D512) (l : Fin 216) (ν : Fin 3 → ℤ) :
    oneElectronPhase ((cfgProjZ512 zP).nuclei l) ν = nyquist512Char3D (-ν) zP := by
  unfold oneElectronPhase nyquist512Char3D omega512 dotProduct
  rw [← Complex.exp_sum]
  refine congrArg Complex.exp ?_
  rw [Complex.ofReal_sum, ← Finset.sum_neg_distrib, Finset.sum_mul]
  refine Finset.sum_congr rfl fun w _ ↦ ?_
  have harg : waveVector ν w * (cfgProjZ512 zP).nuclei l w =
      (2 * Real.pi / 512) * ((ν w : ℝ) * ((zP w).val : ℝ)) := by
    have hLr : cellVolume ^ ((1 : ℝ) / 3) ≠ 0 := cellLength_ne_zero
    dsimp [waveVector, cfgProjZ512]
    field_simp [hLr]
  rw [harg]
  simp only [Pi.neg_apply, Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_ofNat,
    Complex.ofReal_intCast, Complex.ofReal_natCast, Int.cast_mul, Int.cast_neg, Int.cast_natCast]
  field_simp
theorem structureFactor_cfgProjZ512 (zP : NyqFine3D512) (ν : Fin 3 → ℤ) :
    structureFactor (cfgProjZ512 zP) ν = (216 : ℂ) * nyquist512Char3D (-ν) zP := by
  change (∑ l : Fin 216, oneElectronPhase ((cfgProjZ512 zP).nuclei l) ν) = _
  simp_rw [oneElectronPhase_cfgProjZ512]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℂ, smul_eq_mul]
  push_cast
  rfl
theorem projPlus512_avg_cfgProjZ512_eq (K : (Fin 3 → ℤ) → ℂ) {pe qe pP qP : Fin 3 → ℤ}
    (hpe : InElecMomGrid3D pe) (hqe : InElecMomGrid3D qe) (hpP : InProjMomGrid3D pP)
    (hqP : InProjMomGrid3D qP) : (((1 : ℝ) / (108 * 8) : ℂ) * ∑ bP : Fin 3 → Fin 2, ∑ yP :
    NyqGrid3D256, (star (projSubGridElem256_3D bP yP qP) * projSubGridElem256_3D bP yP pP) *
    (-(structureFactor (cfgProjZ512 (nyq512ProjEquiv3D (yP, bP))) (pe - qe) * K (pe - qe)))) =
    if pe + pP = qe + qP then -(2 : ℂ) * K (pe - qe) else 0 := by
  have hterm : ∀ (bP : Fin 3 → Fin 2) (yP : NyqGrid3D256), (star (projSubGridElem256_3D bP yP
      qP) * projSubGridElem256_3D bP yP pP) * (-(structureFactor (cfgProjZ512
      (nyq512ProjEquiv3D (yP, bP))) (pe - qe) * K (pe - qe))) =
      (-(216 / (256 ^ 3 : ℂ)) * K (pe - qe)) * nyquist512Char3D ((qP - pP) + -(pe - qe))
      (nyq512ProjEquiv3D (yP, bP)) :=
    fun bP yP ↦ by
      rw [star_projSubGridElem256_3D_mul, structureFactor_cfgProjZ512]
      calc ((1 / (256 ^ 3 : ℂ)) * nyquist512Char3D (qP - pP) (nyq512ProjEquiv3D (yP, bP))) *
              (-((216 : ℂ) * nyquist512Char3D (-(pe - qe)) (nyq512ProjEquiv3D (yP, bP)) *
                K (pe - qe)))
          = (-(216 / (256 ^ 3 : ℂ)) * K (pe - qe)) *
              (nyquist512Char3D (qP - pP) (nyq512ProjEquiv3D (yP, bP)) *
                nyquist512Char3D (-(pe - qe)) (nyq512ProjEquiv3D (yP, bP))) := by norm_num; ring
        _ = (-(216 / (256 ^ 3 : ℂ)) * K (pe - qe)) *
              nyquist512Char3D ((qP - pP) + -(pe - qe)) (nyq512ProjEquiv3D (yP, bP)) := by
              rw [nyquist512Char3D_add_left]
  simp_rw [hterm, ← Finset.mul_sum]
  rw [sum_nyqProj256_eq_fine512]
  have horth : (∑ zP : NyqFine3D512, nyquist512Char3D ((qP - pP) + -(pe - qe)) zP) = if pe +
      pP = qe + qP then (512 ^ 3 : ℂ) else 0 := by
    rw [sum_nyquist512Char3D_of_abs_lt
      (fun w ↦ by
        have := hpe w; have := hqe w; have := hpP w; have := hqP w
        simp only [Pi.add_apply, Pi.neg_apply, Pi.sub_apply]; omega)
      (fun w ↦ by
        have := hpe w; have := hqe w; have := hpP w; have := hqP w
        simp only [Pi.add_apply, Pi.neg_apply, Pi.sub_apply]; omega)]
    have hiff : ((qP - pP) + -(pe - qe) = 0) ↔ (pe + pP = qe + qP) := by
      refine ⟨fun h ↦ funext fun w ↦ ?_, fun h ↦ funext fun w ↦ ?_⟩
      · have hw := congrFun h w
        simp only [Pi.add_apply, Pi.neg_apply, Pi.sub_apply, Pi.zero_apply] at hw ⊢; omega
      · have hw := congrFun h w
        simp only [Pi.add_apply, Pi.neg_apply, Pi.sub_apply, Pi.zero_apply] at hw ⊢; omega
    exact if_congr hiff rfl rfl
  rw [horth]
  by_cases hcons : pe + pP = qe + qP
  · simp only [hcons, ↓reduceIte]
    push_cast
    field_simp
    ring
  · simp [hcons]
def rProj24_sp : QRegister 24 systemQubits :=
  QRegister.block 3924 24 (by change 3924 + 24 ≤ 3948; omega)
def projGridEquiv24 : Fin (2 ^ 24) ≃ NyqGrid3D256 where
  toFun u := fun w ↦ ⟨(u.val / 2 ^ (8 * w.val)) % 256, by omega⟩
  invFun g := ⟨(g 0).val + 256 * (g 1).val + 65536 * (g 2).val, by
    have h0 := (g 0).isLt; have h1 := (g 1).isLt; have h2 := (g 2).isLt; omega⟩
  left_inv u := by
    have hu := u.isLt
    ext
    change ((u.val / 1) % 256 + 256 * ((u.val / 256) % 256) + 65536 * ((u.val / 65536) % 256)) =
      u.val
    omega
  right_inv g := by
    have h0 := (g 0).isLt; have h1 := (g 1).isLt; have h2 := (g 2).isLt
    funext w
    ext
    match w with
    | ⟨0, _⟩ =>
      change ((g 0).val + 256 * (g 1).val + 65536 * (g 2).val) / 1 % 256 = (g 0).val; omega
    | ⟨1, _⟩ =>
      change ((g 0).val + 256 * (g 1).val + 65536 * (g 2).val) / 256 % 256 = (g 1).val; omega
    | ⟨2, _⟩ =>
      change ((g 0).val + 256 * (g 1).val + 65536 * (g 2).val) / 65536 % 256 = (g 2).val; omega
open Slots01AndGridGuardBridge (twosComp8Int) in
def projTwosMom3D (uIdx : Fin (2 ^ 24)) : Fin 3 → ℤ :=
  fun w ↦ twosComp8Int (projGridEquiv24 uIdx w)
open Slots01AndGridGuardBridge (signedMagToTwos8Perm) in
def projSignedMagToTwos24Equiv : Equiv.Perm (Fin (2 ^ 24)) := projGridEquiv24.trans
    ((Equiv.arrowCongr (Equiv.refl (Fin 3)) signedMagToTwos8Perm).trans projGridEquiv24.symm)
def twosComp8ToOffsetEquiv : Fin 256 ≃ Fin 256 where
  toFun u := ⟨if u.val < 128 then u.val + 128 else u.val - 128, by have := u.isLt; split_ifs <;>
    omega⟩
  invFun v := ⟨if v.val < 128 then v.val + 128 else v.val - 128, by have := v.isLt; split_ifs <;>
    omega⟩
  left_inv u := by
    have hu := u.isLt
    ext
    by_cases h : u.val < 128
    · have h2 : ¬ (u.val + 128 < 128) := by omega
      simp [h, h2]
    · have h2 : u.val - 128 < 128 := by omega
      simp [h, h2]
      omega
  right_inv v := by
    have hv := v.isLt
    ext
    by_cases h : v.val < 128
    · have h2 : ¬ (v.val + 128 < 128) := by omega
      simp [h, h2]
    · have h2 : v.val - 128 < 128 := by omega
      simp [h, h2]
      omega
def half512Equiv : Fin 2 × Fin 256 ≃ Fin 512 where
  toFun p := ⟨256 * p.1.val + p.2.val, by have := p.1.isLt; have := p.2.isLt; omega⟩
  invFun x := (⟨x.val / 256, by have := x.isLt; omega⟩,⟨x.val % 256, by omega⟩)
  left_inv p := by
    rcases p with ⟨s, k⟩
    have hs := s.isLt; have hk := k.isLt
    apply Prod.ext <;> ext <;> dsimp <;> omega
  right_inv x := by
    ext; dsimp; omega
open Slots01AndGridGuardBridge (twosComp8Int) in
theorem twosComp8Int_of_offsetEquiv_symm (k : Fin 256) :
    twosComp8Int (twosComp8ToOffsetEquiv.symm k) = (k.val : ℤ) - 128 := by
  have hk := k.isLt
  change twosComp8Int ⟨if k.val < 128 then k.val + 128 else k.val - 128, _⟩ = _
  unfold twosComp8Int
  dsimp only
  split_ifs <;> omega
open Slots01AndGridGuardBridge (twosComp8Int) in
noncomputable def uProjPlus512TwosMat1D (b : Fin 2) : Operator 256 := Matrix.of fun y u ↦
    (1 / 16 : ℂ) * omega512 (twosComp8Int u * (2 * (y.val : ℤ) + (b.val : ℤ)))
open Slots01AndGridGuardBridge (twosComp8Int) in
theorem uProjPlus512TwosMat1D_mul_conjTranspose (b : Fin 2) :
    uProjPlus512TwosMat1D b * (uProjPlus512TwosMat1D b)ᴴ = 1 := by
  ext y₁ y₂
  rw [Matrix.mul_apply, Matrix.one_apply]
  have hterm : ∀ u : Fin 256,
      uProjPlus512TwosMat1D b y₁ u * (uProjPlus512TwosMat1D b)ᴴ u y₂ =
        (1 / 256 : ℂ) *
          omega512 (twosComp8Int u * (2 * ((y₁.val : ℤ) - (y₂.val : ℤ)))) := fun u ↦ by
    calc uProjPlus512TwosMat1D b y₁ u * (uProjPlus512TwosMat1D b)ᴴ u y₂
        = (1 / 16 : ℂ) * omega512 (twosComp8Int u * (2 * (y₁.val : ℤ) + (b.val : ℤ))) *
            (omega512 (-(twosComp8Int u * (2 * (y₂.val : ℤ) + (b.val : ℤ)))) * (1 / 16 : ℂ)) := by
            dsimp only [uProjPlus512TwosMat1D, Matrix.of_apply, Matrix.conjTranspose_apply]
            rw [star_mul, star_omega512, show star (1 / 16 : ℂ) = 1 / 16 by norm_num]
      _ = (1 / 256 : ℂ) * (omega512 (twosComp8Int u * (2 * (y₁.val : ℤ) + (b.val : ℤ))) *
            omega512 (-(twosComp8Int u * (2 * (y₂.val : ℤ) + (b.val : ℤ))))) := by
            field_simp; ring
      _ = (1 / 256 : ℂ) * omega512 (twosComp8Int u * (2 * ((y₁.val : ℤ) - (y₂.val : ℤ)))) := by
            rw [← omega512_add]; congr 1; ring
  simp_rw [hterm, ← Finset.mul_sum]
  rw [← Equiv.sum_comp twosComp8ToOffsetEquiv.symm]
  simp_rw [twosComp8Int_of_offsetEquiv_symm]
  let d : ℤ := (y₁.val : ℤ) - (y₂.val : ℤ)
  have hshift : ∀ k : Fin 256,
      omega512 (((k.val : ℤ) - 128) * (2 * ((y₁.val : ℤ) - (y₂.val : ℤ)))) =
        omega512 (-256 * d) * omega512 ((2 * d) * (k.val : ℤ)) := fun k ↦ by
    rw [← omega512_add]
    congr 1; dsimp [d]; ring
  simp_rw [hshift, ← Finset.mul_sum]
  by_cases hy : y₁ = y₂
  · subst hy
    simp [d, omega512_zero]
  · simp only [hy, ↓reduceIte]
    have h2 : (2 : ℂ) * (∑ k : Fin 256, omega512 ((2 * d) * (k.val : ℤ))) = ∑ x : Fin 512,
        omega512 ((2 * d) * (x.val : ℤ)) := by
      rw [← Equiv.sum_comp half512Equiv, Fintype.sum_prod_type]
      rw [Fin.sum_univ_two]
      have h0 : ∀ k : Fin 256,
          omega512 ((2 * d) * ((half512Equiv (0, k)).val : ℤ)) =
            omega512 ((2 * d) * (k.val : ℤ)) := fun k ↦ by
        congr 2
        simp [half512Equiv]
      have h1 : ∀ k : Fin 256,
          omega512 ((2 * d) * ((half512Equiv (1, k)).val : ℤ)) =
            omega512 ((2 * d) * (k.val : ℤ)) := fun k ↦ by
        have hv : ((half512Equiv (1, k)).val : ℤ) = 256 + (k.val : ℤ) := by
          simp [half512Equiv]
        rw [hv, show (2 * d) * (256 + (k.val : ℤ)) = (2 * d) * (k.val : ℤ) + d * 512 by ring,
          omega512_add, omega512_mul_512, mul_one]
      simp_rw [h0, h1]
      ring
    have hz : (∑ x : Fin 512, omega512 ((2 * d) * (x.val : ℤ))) = 0 := by
      rw [sum_omega512_of_abs_lt (by have := y₁.isLt; have := y₂.isLt; dsimp [d]; omega)
        (by have := y₁.isLt; have := y₂.isLt; dsimp [d]; omega)]
      refine ite_eq_right_iff.mpr fun hzero ↦ (hy <| by ext; dsimp [d] at hzero; omega).elim
    have hk0 : (∑ k : Fin 256, omega512 ((2 * d) * (k.val : ℤ))) = 0 := by
      rw [hz] at h2
      exact (mul_eq_zero.mp h2).resolve_left (by norm_num)
    rw [hk0]
    ring
noncomputable def uProjPlus512TwosMat3D (b : Fin 3 → Fin 2) : Operator (2 ^ 24) := Matrix.of
    fun yIdx uIdx ↦ star (projSubGridElem256_3D b (projGridEquiv24 yIdx) (projTwosMom3D uIdx))
theorem uProjPlus512TwosMat3D_entry_factor (b : Fin 3 → Fin 2) (yIdx uIdx : Fin (2 ^ 24)) :
    uProjPlus512TwosMat3D b yIdx uIdx = ∏ w : Fin 3, uProjPlus512TwosMat1D (b w)
    (projGridEquiv24 yIdx w) (projGridEquiv24 uIdx w) := by
  unfold uProjPlus512TwosMat3D projSubGridElem256_3D uProjPlus512TwosMat1D projTwosMom3D
  simp only [Matrix.of_apply]
  rw [RCLike.star_def, map_prod]
  refine Finset.prod_congr rfl fun w _ ↦ ?_
  have h16 : (√256 : ℝ) = 16 := by
    rw [show (256 : ℝ) = 16 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [← RCLike.star_def, star_mul, star_omega512]
  have hs : star (1 / (√256 : ℂ)) = (1 / 16 : ℂ) := by
    rw [h16]
    norm_num
  rw [hs, mul_comm]
  congr 1
  congr 1
  ring
theorem uProjPlus512TwosMat3D_mul_conjTranspose (b : Fin 3 → Fin 2) :
    uProjPlus512TwosMat3D b * (uProjPlus512TwosMat3D b)ᴴ = 1 := by
  ext y₁ y₂
  rw [Matrix.mul_apply, Matrix.one_apply]
  let f (w : Fin 3) (u : Fin 256) : ℂ := uProjPlus512TwosMat1D (b w) (projGridEquiv24 y₁ w) u
      * (uProjPlus512TwosMat1D (b w))ᴴ u (projGridEquiv24 y₂ w)
  have hprod : ∀ uIdx : Fin (2 ^ 24), uProjPlus512TwosMat3D b y₁ uIdx *
      (uProjPlus512TwosMat3D b)ᴴ uIdx y₂ = ∏ w : Fin 3, f w (projGridEquiv24 uIdx w) := by
    intro uIdx
    simp only [f, Matrix.conjTranspose_apply, uProjPlus512TwosMat3D_entry_factor,
      RCLike.star_def, map_prod]
    rw [← Finset.prod_mul_distrib]
  simp_rw [hprod]
  rw [← Equiv.sum_comp projGridEquiv24.symm]
  simp_rw [projGridEquiv24.apply_symm_apply]
  rw [← Fintype.prod_sum f]
  have h1d : ∀ w : Fin 3,
      (∑ u : Fin 256, f w u) =
        if projGridEquiv24 y₁ w = projGridEquiv24 y₂ w then 1 else 0 := fun w ↦ by
    have hw := congrFun (congrFun (uProjPlus512TwosMat1D_mul_conjTranspose (b w))
      (projGridEquiv24 y₁ w)) (projGridEquiv24 y₂ w)
    simpa only [f, Matrix.mul_apply, Matrix.one_apply] using hw
  simp_rw [h1d]
  by_cases hy : y₁ = y₂
  · subst hy; simp only [↓reduceIte, Finset.prod_const_one]
  · simp only [hy, ↓reduceIte]
    have hne : ∃ w : Fin 3, projGridEquiv24 y₁ w ≠ projGridEquiv24 y₂ w := by
      by_contra hall
      have hall' : ∀ w : Fin 3, projGridEquiv24 y₁ w = projGridEquiv24 y₂ w :=
        fun w ↦ Decidable.byContradiction fun hw ↦ hall ⟨w, hw⟩
      exact hy (projGridEquiv24.injective (funext hall'))
    rcases hne with ⟨w₀, hw₀⟩
    exact Finset.prod_eq_zero (Finset.mem_univ w₀) (ite_eq_right_iff.mpr fun h ↦ absurd h hw₀)
noncomputable def uProjPlus512Twos_3D (b : Fin 3 → Fin 2) : Unitary (2 ^ 24) :=
  ⟨uProjPlus512TwosMat3D b, Matrix.mem_unitaryGroup_iff.mpr (by
    rw [Matrix.star_eq_conjTranspose]
    exact uProjPlus512TwosMat3D_mul_conjTranspose b)⟩
noncomputable abbrev uProjPlus512_3D (b : Fin 3 → Fin 2) : Unitary (2 ^ 24) :=
  uProjPlus512Twos_3D b
open TwosCompAndWire0Cancel (fwdPermUnitary) in
noncomputable def uProjPlus512SM_3D (b : Fin 3 → Fin 2) : Unitary (2 ^ 24) :=
  uProjPlus512_3D b * fwdPermUnitary projSignedMagToTwos24Equiv
theorem zmod2_ite_inj {p q : Bool}
    (h : (if p then (1 : ZMod 2) else 0) = (if q then (1 : ZMod 2) else 0)) : p = q := by
  cases p <;> cases q <;> simp at h ⊢
theorem extractIndex_rProj24_testBit (x : Fin (2 ^ systemQubits)) (j : ℕ) (hj : j < 24) :
    (rProj24_sp.extractIndex x).val.testBit j = x.val.testBit (3924 + j) := by
  have hb := rProj24_sp.basisBits_extractIndex x ⟨j, hj⟩
  rw [basisBits_eq_testBit, basisBits_eq_testBit] at hb
  exact zmod2_ite_inj hb
open Slots01AndGridGuardBridge (projAxisWord8) in
open SpecsAux.BridgeFermionicComm.SpecInner
    (testBit_div_two_pow_mod_two_pow signMagnitude_fst_eq_testBit) in
theorem projGridEquiv24_extractIndex_eq_projAxisWord8 (x : Fin (2 ^ systemQubits)) (w : Fin 3) :
    projGridEquiv24 (rProj24_sp.extractIndex x) w = projAxisWord8 x w := by
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro b
  by_cases hb : b < 8
  · have hL : (projGridEquiv24 (rProj24_sp.extractIndex x) w).val.testBit b =
        x.val.testBit (3924 + 8 * w.val + b) := by
      change (((rProj24_sp.extractIndex x).val / 2 ^ (8 * w.val)) % 256).testBit b = _
      rw [show (256 : ℕ) = 2 ^ 8 by rfl,
        testBit_div_two_pow_mod_two_pow _ (8 * w.val) 8 b hb,
        extractIndex_rProj24_testBit x (8 * w.val + b) (by have := w.isLt; omega)]
      ring_nf
    rw [hL]
    have hoff : bitOffset .projectile w = 3924 + 8 * w.val := rfl
    have hsm1 : (signMagnitude x .projectile w).1 < 2 := by simp only [signMagnitude]; omega
    have hsm2 : (signMagnitude x .projectile w).2 < 128 := by
      simp only [signMagnitude, componentBits, projectileBits]; omega
    have hword : (projAxisWord8 x w).val =
        128 * (signMagnitude x .projectile w).1 + (signMagnitude x .projectile w).2 := by
      simp [projAxisWord8, Nat.mod_eq_of_lt hsm1, Nat.mod_eq_of_lt hsm2]
    rw [hword]
    by_cases hb7 : b = 7
    · subst hb7
      have hsm_bit := signMagnitude_fst_eq_testBit x .projectile w
      rw [show componentBits .projectile - 1 = 7 by rfl, hoff] at hsm_bit
      by_cases hs0 : (signMagnitude x .projectile w).1 = 0
      · rw [hs0] at hsm_bit ⊢
        rw [Nat.mul_zero, Nat.zero_add]
        conv_rhs => rw [Nat.testBit_lt_two_pow hsm2]
        cases htb : x.val.testBit (3924 + 8 * w.val + 7) <;> simp [htb] at hsm_bit ⊢
      · have hs1 : (signMagnitude x .projectile w).1 = 1 := by omega
        rw [hs1] at hsm_bit ⊢
        have htb : x.val.testBit (3924 + 8 * w.val + 7) = true := by
          cases h : x.val.testBit (3924 + 8 * w.val + 7) <;> simp [h] at hsm_bit ⊢
        rw [htb]
        symm
        rw [Nat.testBit_eq_decide_div_mod_eq, show 2 ^ 7 = 128 by rfl,
          show (128 * 1 + (signMagnitude x .projectile w).2) / 128 = 1 by omega]
        rfl
    · have hb7' : b < 7 := by omega
      have hmod : (128 * (signMagnitude x .projectile w).1 +
          (signMagnitude x .projectile w).2) % 2 ^ 7 = (signMagnitude x .projectile w).2 := by omega
      have htb1 : (128 * (signMagnitude x .projectile w).1 + (signMagnitude x .projectile
          w).2).testBit b = ((128 * (signMagnitude x .projectile w).1 + (signMagnitude x
          .projectile w).2) % 2 ^ 7).testBit b := by
        rw [Nat.testBit_mod_two_pow, decide_eq_true hb7', Bool.true_and]
      rw [htb1, hmod]
      have htb2 := testBit_div_two_pow_mod_two_pow x.val (3924 + 8 * w.val) 7 b hb7'
      simpa only [signMagnitude, show componentBits .projectile - 1 = 5 + 2 by rfl,
        hoff] using htb2.symm
  · have hL : (projGridEquiv24 (rProj24_sp.extractIndex x) w).val < 2 ^ b :=
      lt_of_lt_of_le (projGridEquiv24 (rProj24_sp.extractIndex x) w).isLt
        (Nat.pow_le_pow_right Nat.zero_lt_two (show 8 ≤ b by omega))
    have hR : (projAxisWord8 x w).val < 2 ^ b :=
      lt_of_lt_of_le (projAxisWord8 x w).isLt
        (Nat.pow_le_pow_right Nat.zero_lt_two (show 8 ≤ b by omega))
    rw [Nat.testBit_lt_two_pow hL, Nat.testBit_lt_two_pow hR]
open Slots01AndGridGuardBridge (twosComp8Int signedMagToTwos8
  signedMagToTwos8Perm esmSignedInt256) in
theorem twosComp8Int_signedMagToTwos8_eq_esm (w : Fin 256) (hw : w.val ≠ 128) :
    twosComp8Int (signedMagToTwos8Perm w) = esmSignedInt256 w := by
  have hw_lt : w.val < 256 := w.isLt
  change twosComp8Int (signedMagToTwos8 w) = _
  unfold twosComp8Int signedMagToTwos8 esmSignedInt256
  by_cases hle : w.val ≤ 128
  · have hlt : w.val < 128 := by omega
    simp [hle, hlt]
  · have hge : ¬ (384 - w.val < 128) := by omega
    have hlt : ¬ (w.val < 128) := by omega
    simp [hle, hge, hlt]
    omega
open Slots01AndGridGuardBridge (projAxisWord8 esmSignedInt256) in
theorem esmSignedInt256_projAxisWord8_eq_momentum (x : Fin (2 ^ systemQubits)) (w : Fin 3) :
    esmSignedInt256 (projAxisWord8 x w) = momentum x .projectile w := by
  let s := (signMagnitude x .projectile w).1
  let m := (signMagnitude x .projectile w).2
  have hs : s < 2 := by simp only [s, signMagnitude]; omega
  have hm : m < 128 := by simp only [m, signMagnitude, componentBits, projectileBits]; omega
  have hval : (projAxisWord8 x w).val = 128 * s + m := by
    simp [projAxisWord8, s, m, Nat.mod_eq_of_lt hs, Nat.mod_eq_of_lt hm]
  unfold esmSignedInt256 momentum
  rw [hval]
  change (if 128 * s + m < 128 then ((128 * s + m : ℕ) : ℤ)
    else -(((128 * s + m - 128 : ℕ) : ℤ))) = (-1) ^ s * (m : ℤ)
  by_cases hs0 : s = 0
  · rw [hs0]; simp [hm]
  · have hs1 : s = 1 := by omega
    rw [hs1]
    have hge : ¬ (128 * 1 + m < 128) := by omega
    simp [hge]
open Slots01AndGridGuardBridge (signedMagToTwos8Perm) in
theorem projGridEquiv24_projSignedMagToTwos24 (u : Fin (2 ^ 24)) (w : Fin 3) : projGridEquiv24
    (projSignedMagToTwos24Equiv u) w = signedMagToTwos8Perm (projGridEquiv24 u w) := congrArg
    (fun g : NyqGrid3D256 ↦ g w) (projGridEquiv24.apply_symm_apply (Equiv.arrowCongr
    (Equiv.refl (Fin 3)) signedMagToTwos8Perm (projGridEquiv24 u)))
open Slots01AndGridGuardBridge (twosComp8Int signedMagToTwos8Perm) in
theorem projTwosMom3D_projSignedMagToTwos24 (u : Fin (2 ^ 24)) (w : Fin 3) : projTwosMom3D
    (projSignedMagToTwos24Equiv u) w = twosComp8Int
    (signedMagToTwos8Perm (projGridEquiv24 u w)) := congrArg
    (fun g : NyqGrid3D256 ↦ twosComp8Int (g w)) (projGridEquiv24.apply_symm_apply _)
theorem projTwosMom3D_sm_extractIndex_eq_momentum {x : Fin (2 ^ systemQubits)}
    (hx : IsGridState x) : projTwosMom3D
    (projSignedMagToTwos24Equiv (rProj24_sp.extractIndex x)) = momentum x .projectile := by
  funext w
  rw [projTwosMom3D_projSignedMagToTwos24, projGridEquiv24_extractIndex_eq_projAxisWord8,
    twosComp8Int_signedMagToTwos8_eq_esm _
      (SixSlotEndpointJunctionBridge.projAxisWord8_ne_128_of_isGridState hx
        w),
    esmSignedInt256_projAxisWord8_eq_momentum]
theorem env_eq_iff_electron_testBit_eq (x y : Fin (2 ^ systemQubits)) :
    (rProj24_sp.basisSplitEquiv x).2 = (rProj24_sp.basisSplitEquiv y).2 ↔
      ∀ k < 3924, x.val.testBit k = y.val.testBit k := by
  constructor
  · intro henv k hk
    have hnot : (⟨k, by change k < 3948; omega⟩ : Wire systemQubits) ∉
        Set.range rProj24_sp.wires := by
      rintro ⟨j, hj⟩
      have hv := congrArg Fin.val hj
      simp [rProj24_sp] at hv
      omega
    have hb := congrFun henv ⟨⟨k, by change k < 3948; omega⟩, hnot⟩
    rw [QRegister.basisSplitEquiv_apply_snd, QRegister.basisSplitEquiv_apply_snd,
      basisBits_eq_testBit, basisBits_eq_testBit] at hb
    exact zmod2_ite_inj hb
  · intro hbits
    funext ⟨w, hw⟩
    rw [QRegister.basisSplitEquiv_apply_snd, QRegister.basisSplitEquiv_apply_snd,
      basisBits_eq_testBit, basisBits_eq_testBit]
    have hlt : w.val < 3924 := by
      by_contra hge
      have hlt24 : w.val - 3924 < 24 := by have := w.isLt; change w.val < 3948 at this; omega
      exact hw ⟨⟨w.val - 3924, hlt24⟩, Fin.ext (by simp [rProj24_sp]; omega)⟩
    rw [hbits w.val hlt]
attribute [local irreducible] rProj24_sp
open SpecsAux.BridgeFermionicComm.SpecInner
    (signMagnitude_fst_eq_testBit testBit_div_two_pow_mod_two_pow) in
theorem signMagnitude_electron_eq_of_testBit_eq {x y : Fin (2 ^ systemQubits)}
    (hbits : ∀ k < 3924, x.val.testBit k = y.val.testBit k) (i : Fin numElectrons) (w : Fin 3)
    : signMagnitude x (.electron i) w = signMagnitude y (.electron i) w := by
  have hi : i.val < 218 := i.isLt
  have hw : w.val < 3 := w.isLt
  have hoff : bitOffset (.electron i) w + 6 ≤ 3924 := by
    change 6 * (3 * i.val + w.val) + 6 ≤ 3924; omega
  apply Prod.ext
  · rw [signMagnitude_fst_eq_testBit, signMagnitude_fst_eq_testBit,
      hbits _ (by change bitOffset (.electron i) w + 5 < 3924; omega)]
  · apply Nat.eq_of_testBit_eq
    intro b
    by_cases hb : b < 5
    · dsimp only [signMagnitude]
      change (x.val / 2 ^ bitOffset (.electron i) w % 2 ^ 5).testBit b =
        (y.val / 2 ^ bitOffset (.electron i) w % 2 ^ 5).testBit b
      rw [testBit_div_two_pow_mod_two_pow _ _ 5 b hb,
        testBit_div_two_pow_mod_two_pow _ _ 5 b hb]
      exact hbits (bitOffset (.electron i) w + b) (by omega)
    · have hx : (signMagnitude x (.electron i) w).2 < 2 ^ b := by
        have hlt32 : (signMagnitude x (.electron i) w).2 < 2 ^ 5 := by
          dsimp only [signMagnitude]
          exact Nat.mod_lt _ (by decide : 0 < 2 ^ 5)
        exact lt_of_lt_of_le hlt32 (Nat.pow_le_pow_right Nat.zero_lt_two (by omega))
      have hy : (signMagnitude y (.electron i) w).2 < 2 ^ b := by
        have hlt32 : (signMagnitude y (.electron i) w).2 < 2 ^ 5 := by
          dsimp only [signMagnitude]
          exact Nat.mod_lt _ (by decide : 0 < 2 ^ 5)
        exact lt_of_lt_of_le hlt32 (Nat.pow_le_pow_right Nat.zero_lt_two (by omega))
      rw [Nat.testBit_lt_two_pow hx, Nat.testBit_lt_two_pow hy]
open Slots01AndGridGuardBridge (signedMagToTwos8 signedMagToTwos8Perm) in
open TwosCompAndWire0Cancel (smToTwosAxisPerm smToTwosAxisPerm_val) in
theorem smToTwosAxisPerm5_eq_signedMagToTwos8 (u : Fin 256) :
    smToTwosAxisPerm 5 u = signedMagToTwos8Perm u := by
  apply Fin.ext
  rw [smToTwosAxisPerm_val]
  have hu := u.isLt
  by_cases hlt : u.val < 128
  · have hle : u.val ≤ 128 := by omega
    simp [signedMagToTwos8Perm, signedMagToTwos8, hlt, hle]
  · by_cases heq : u.val = 128
    · simp [signedMagToTwos8Perm, signedMagToTwos8, heq]
    · have hle : ¬ u.val ≤ 128 := by omega
      simp [signedMagToTwos8Perm, signedMagToTwos8, hlt, heq, hle]
      omega
open TwosCompAndWire0Cancel (fwdPermMatrix fwdPermMatrix_apply) in
theorem permMatrix_comm_embedMatrix_gen {m N : ℕ} (r : QRegister m N)
    (perm : Equiv.Perm (Fin (2 ^ N))) (hinv : ∀ z, perm (perm z) = z)
    (hkeep : ∀ z, r.extractIndex (perm z) = r.extractIndex z) (henv : ∀ z₁ z₂,
    (r.basisSplitEquiv (perm z₁)).2 = (r.basisSplitEquiv (perm z₂)).2 ↔ (r.basisSplitEquiv
    z₁).2 = (r.basisSplitEquiv z₂).2) (M : Operator (2 ^ m)) : fwdPermMatrix perm *
    r.embedMatrix M = r.embedMatrix M * fwdPermMatrix perm := by
  ext i j
  rw [Matrix.mul_apply, Finset.sum_eq_single (perm i)
      (fun k _ hk ↦ by
        have hne : perm k ≠ i := fun hh ↦ hk (by rw [← hh, hinv])
        simp [fwdPermMatrix_apply, hne])
      (by simp),
    Matrix.mul_apply, Finset.sum_eq_single (perm j)
      (fun k _ hk ↦ by simp [fwdPermMatrix_apply, hk.symm]) (by simp)]
  simp only [fwdPermMatrix_apply, hinv i, ↓reduceIte, one_mul, mul_one,
    QRegister.embedMatrix_apply, hkeep]
  by_cases hE : (r.basisSplitEquiv i).2 = (r.basisSplitEquiv (perm j)).2
  · have hE2 : (r.basisSplitEquiv (perm i)).2 = (r.basisSplitEquiv j).2 :=
      (henv (perm i) j).mp (by simpa [hinv i] using hE)
    simp [hE, hE2]
  · have hE2 : (r.basisSplitEquiv (perm i)).2 ≠ (r.basisSplitEquiv j).2 :=
      fun h ↦ hE (by simpa [hinv i] using (henv (perm i) j).mpr h)
    simp [hE, hE2]
open TwosCompAndWire0Cancel (fwdPermUnitary fwdPermUnitary_apply) in
theorem embedUnitary_fwdPerm_eq_fwdPerm {m N : ℕ} (r : QRegister m N)
    (pSub : Equiv.Perm (Fin (2 ^ m))) (pSys : Equiv.Perm (Fin (2 ^ N)))
    (hEnv : ∀ x : Fin (2 ^ N),(r.basisSplitEquiv (pSys x)).2 = (r.basisSplitEquiv x).2)
    (hExt : ∀ x : Fin (2 ^ N), r.extractIndex (pSys x) = pSub (r.extractIndex x)) :
    r.embedUnitary (fwdPermUnitary pSub) = fwdPermUnitary pSys := by
  apply Subtype.ext
  ext x' x
  rw [QRegister.embedUnitary_val, QRegister.embedMatrix_apply, fwdPermUnitary_apply,
    fwdPermUnitary_apply]
  by_cases henv : (r.basisSplitEquiv x').2 = (r.basisSplitEquiv x).2
  · simp only [henv, ↓reduceIte, mul_one]
    by_cases hex : pSub (r.extractIndex x) = r.extractIndex x'
    · have htot : pSys x = x' := by
        apply r.basisSplitEquiv.injective
        exact Prod.ext (by rw [QRegister.basisSplitEquiv_apply_fst,
          QRegister.basisSplitEquiv_apply_fst, hExt x, hex]) ((hEnv x).trans henv.symm)
      simp [hex, htot]
    · have htot : pSys x ≠ x' := fun h ↦ hex (by rw [← hExt x, h])
      simp [hex, htot]
  · have htot : pSys x ≠ x' := fun h ↦ henv (by rw [← h, hEnv x])
    simp [henv, htot]
open Slots01AndGridGuardBridge (projAxisWord8) in
open TwosCompAndWire0Cancel (proj3Axes) in
theorem proj3Axes_extractIndex_eq_projAxisWord8 (w : Fin 3) (z : Fin (2 ^ systemQubits)) :
    (proj3Axes w).extractIndex z = projAxisWord8 z w := by
  rw [← projGridEquiv24_extractIndex_eq_projAxisWord8 z w]
  apply Fin.ext; apply Nat.eq_of_testBit_eq; intro b
  by_cases hb : b < 8
  · have h1 := (proj3Axes w).basisBits_extractIndex z ⟨b, hb⟩
    rw [basisBits_eq_testBit, basisBits_eq_testBit] at h1
    have h1' := zmod2_ite_inj h1
    change _ = (((rProj24_sp.extractIndex z).val / 2 ^ (8 * w.val)) % 256).testBit b
    rw [show (256 : ℕ) = 2 ^ 8 by rfl,
      SpecsAux.BridgeFermionicComm.SpecInner.testBit_div_two_pow_mod_two_pow
        _ (8 * w.val) 8 b hb,
      extractIndex_rProj24_testBit z (8 * w.val + b) (by have := w.isLt; omega)]
    simpa [proj3Axes, PosSlots24MergedVepBoundAlt.qreg_block_apply,
      PosSlots24MergedVepBoundAlt.qreg_block_wires_apply, add_assoc] using h1'
  · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le ((proj3Axes w).extractIndex z).isLt
        (Nat.pow_le_pow_right Nat.zero_lt_two (show 8 ≤ b by omega))),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le (projGridEquiv24 (rProj24_sp.extractIndex z) w).isLt
        (Nat.pow_le_pow_right Nat.zero_lt_two (show 8 ≤ b by omega)))]
open TwosCompAndWire0Cancel (fwdPermUnitary smToTwosAxisPerm proj3Axes
  smToTwosProj3Perm) in
theorem embed_projSignedMagToTwos24_eq_smToTwosProj3 : rProj24_sp.embedUnitary
    (fwdPermUnitary projSignedMagToTwos24Equiv) = fwdPermUnitary smToTwosProj3Perm := by
  refine embedUnitary_fwdPerm_eq_fwdPerm rProj24_sp projSignedMagToTwos24Equiv smToTwosProj3Perm
    (fun x ↦ ?_) (fun x ↦ ?_)
  · rw [env_eq_iff_electron_testBit_eq]
    intro k hk
    have hnot : ∀ m : Fin 3, (⟨k, by change k < 3948; omega⟩ : Wire systemQubits) ∉
        Set.range (proj3Axes m).wires := by
      rintro m ⟨j, hj⟩
      have hv := congrArg Fin.val hj
      simp [proj3Axes] at hv
      omega
    have hb := TwosCompAndWire0Cancel.foldAxesPerm_outside
      (smToTwosAxisPerm 5) proj3Axes ⟨k, by change k < 3948; omega⟩ hnot x
    rw [basisBits_eq_testBit, basisBits_eq_testBit] at hb
    exact zmod2_ite_inj hb
  · apply projGridEquiv24.injective
    funext w
    have hfold : smToTwosProj3Perm x =
        TwosCompAndWire0Cancel.foldAxesPerm
          (smToTwosAxisPerm 5) proj3Axes x := rfl
    rw [projGridEquiv24_extractIndex_eq_projAxisWord8,
      projGridEquiv24_projSignedMagToTwos24,
      projGridEquiv24_extractIndex_eq_projAxisWord8,
      ← smToTwosAxisPerm5_eq_signedMagToTwos8,
      ← proj3Axes_extractIndex_eq_projAxisWord8 w (smToTwosProj3Perm x),
      hfold,
      TwosCompAndWire0Cancel.foldAxesPerm_extractIndex
        (smToTwosAxisPerm 5) proj3Axes
        (fun _ _ ↦ TwosCompAndWire0Cancel.proj3Axes_disjoint) w x,
      proj3Axes_extractIndex_eq_projAxisWord8 w x]
set_option exponentiation.threshold 32 in
theorem testBit_extractIndex_rProj24_ge (x : Fin (2 ^ systemQubits)) {j : ℕ}
    (hj : ¬ j < 24) : (rProj24_sp.extractIndex x).val.testBit j = false :=
  Nat.testBit_lt_two_pow (lt_of_lt_of_le (rProj24_sp.extractIndex x).isLt
    (Nat.pow_le_pow_right Nat.zero_lt_two (Nat.le_of_not_lt hj)))
set_option exponentiation.threshold 32 in
open TwosCompAndWire0Cancel (smToTwosAxisPerm elec654Axes
  smToTwos654SysPerm smToTwos654SysUnitary) in
theorem smToTwos654SysUnitary_comm_embedMatrix (M : Operator (2 ^ 24)) :
    smToTwos654SysUnitary.1 * rProj24_sp.embedMatrix M =
      rProj24_sp.embedMatrix M * smToTwos654SysUnitary.1 := by
  have hinv : ∀ z, smToTwos654SysPerm (smToTwos654SysPerm z) = z :=
    TwosCompAndWire0Cancel.foldAxesPerm_self_of_involutive
      (TwosCompAndWire0Cancel.smToTwosAxisPerm_self 3) elec654Axes
      fun _ _ ↦ TwosCompAndWire0Cancel.elec654Axes_disjoint
  have hkeep : ∀ z : Fin (2 ^ systemQubits),
      rProj24_sp.extractIndex (smToTwos654SysPerm z) = rProj24_sp.extractIndex z := fun z ↦ by
    apply Fin.ext; apply Nat.eq_of_testBit_eq; intro j
    by_cases hj : j < 24
    · rw [extractIndex_rProj24_testBit _ j hj, extractIndex_rProj24_testBit _ j hj]
      have hnot : ∀ m : Fin 654, (⟨3924 + j,
        by change 3924 + j < 3948; omega⟩ : Wire systemQubits) ∉
          Set.range (elec654Axes m).wires := by
        rintro m ⟨b, hb⟩
        have hv := congrArg Fin.val hb; have hm := m.isLt; have hblt := b.isLt
        simp [elec654Axes] at hv; omega
      have hb := TwosCompAndWire0Cancel.foldAxesPerm_outside
        (smToTwosAxisPerm 3) elec654Axes ⟨3924 + j, by change 3924 + j < 3948; omega⟩ hnot z
      rw [basisBits_eq_testBit, basisBits_eq_testBit] at hb
      exact zmod2_ite_inj hb
    · rw[testBit_extractIndex_rProj24_ge _ hj, testBit_extractIndex_rProj24_ge _ hj]
  have henv_inj : ∀ z₁ z₂ : Fin (2 ^ systemQubits),
      (rProj24_sp.basisSplitEquiv (smToTwos654SysPerm z₁)).2 =
        (rProj24_sp.basisSplitEquiv (smToTwos654SysPerm z₂)).2 ↔
      (rProj24_sp.basisSplitEquiv z₁).2 = (rProj24_sp.basisSplitEquiv z₂).2 := by
    have hfwd : ∀ a b,
        (rProj24_sp.basisSplitEquiv a).2 = (rProj24_sp.basisSplitEquiv b).2 →
        (rProj24_sp.basisSplitEquiv (smToTwos654SysPerm a)).2 =
          (rProj24_sp.basisSplitEquiv (smToTwos654SysPerm b)).2 := fun a b heq ↦ by
      rw [env_eq_iff_electron_testBit_eq] at heq ⊢
      intro k hk
      let m : Fin 654 := ⟨k / 6, by omega⟩
      have hsub_eq : (elec654Axes m).extractIndex a = (elec654Axes m).extractIndex b := by
        apply Fin.ext; apply Nat.eq_of_testBit_eq; intro q
        by_cases hq : q < 6
        · have h1 := zmod2_ite_inj (by
            simpa only [basisBits_eq_testBit] using (elec654Axes m).basisBits_extractIndex a ⟨q,
              hq⟩)
          have h2 := zmod2_ite_inj (by
            simpa only [basisBits_eq_testBit] using (elec654Axes m).basisBits_extractIndex b ⟨q,
              hq⟩)
          rw [h1, h2]
          exact heq (6 * m.val + q) (by have := m.isLt; omega)
        · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le ((elec654Axes m).extractIndex a).isLt
              (Nat.pow_le_pow_right Nat.zero_lt_two (show 6 ≤ q by omega))),
            Nat.testBit_lt_two_pow (lt_of_lt_of_le ((elec654Axes m).extractIndex b).isLt
              (Nat.pow_le_pow_right Nat.zero_lt_two (show 6 ≤ q by omega)))]
      have hex_after : (elec654Axes m).extractIndex (smToTwos654SysPerm a) =
          (elec654Axes m).extractIndex (smToTwos654SysPerm b) := by
        dsimp only [smToTwos654SysPerm]
        rw [TwosCompAndWire0Cancel.foldAxesPerm_extractIndex _ _
            (fun _ _ ↦ TwosCompAndWire0Cancel.elec654Axes_disjoint),
          TwosCompAndWire0Cancel.foldAxesPerm_extractIndex _ _
            (fun _ _ ↦ TwosCompAndWire0Cancel.elec654Axes_disjoint),
          hsub_eq]
      have h1 := zmod2_ite_inj (by
        simpa only [basisBits_eq_testBit] using
          (elec654Axes m).basisBits_extractIndex (smToTwos654SysPerm a) ⟨k % 6, by omega⟩)
      have h2 := zmod2_ite_inj (by
        simpa only [basisBits_eq_testBit] using
          (elec654Axes m).basisBits_extractIndex (smToTwos654SysPerm b) ⟨k % 6, by omega⟩)
      have hw_eq : ((elec654Axes m) ⟨k % 6, by omega⟩).val = k := by
        dsimp [elec654Axes, PosSlots24MergedVepBoundAlt.qreg_block_apply,
          PosSlots24MergedVepBoundAlt.qreg_block_wires_apply,
          PosSlots24MergedVepBoundAlt.qreg_whole_wires,
          PosSlots24MergedVepBoundAlt.emb_trans_apply,
          PosSlots24MergedVepBoundAlt.emb_refl_apply,
          PosSlots24MergedVepBoundAlt.emb_mk_apply, m]; omega
      rw [hw_eq] at h1 h2
      rw [← h1, ← h2, hex_after]
    exact fun z₁ z₂ ↦ ⟨fun h ↦ by simpa [hinv] using hfwd _ _ h, hfwd z₁ z₂⟩
  exact permMatrix_comm_embedMatrix_gen rProj24_sp smToTwos654SysPerm hinv hkeep henv_inj M
open TwosCompAndWire0Cancel (fwdPermUnitary fwdPermUnitary_trans
  smToTwos654SysPerm smToTwosProj3Perm smToTwos654SysUnitary smToTwosSysUnitary) in
theorem smToTwosSysUnitary_eq_proj_mul_elec : smToTwosSysUnitary = rProj24_sp.embedUnitary
    (fwdPermUnitary projSignedMagToTwos24Equiv) * smToTwos654SysUnitary := by
  rw [embed_projSignedMagToTwos24_eq_smToTwosProj3]
  exact fwdPermUnitary_trans smToTwos654SysPerm smToTwosProj3Perm
def matUnit24 {m : ℕ} (i j : Fin (2 ^ m)) : Operator (2 ^ m) :=
  Matrix.of fun a b ↦ if a = i ∧ b = j then 1 else 0
theorem matUnit24_conjTranspose {m : ℕ} (i j : Fin (2 ^ m)) :
    (matUnit24 i j)ᴴ = matUnit24 j i := by
  ext a b
  simp only [matUnit24, Matrix.conjTranspose_apply, Matrix.of_apply, and_comm]
  split_ifs <;> simp
theorem matUnit24_mul {m : ℕ} (i j k l : Fin (2 ^ m)) :
    matUnit24 i j * matUnit24 k l = if j = k then matUnit24 i l else 0 := by
  ext a b
  rw [Matrix.mul_apply]
  by_cases hjk : j = k
  · subst hjk
    rw [Finset.sum_eq_single j (fun m _ hm ↦ by simp [matUnit24, hm]) (by simp)]
    by_cases ha : a = i <;> by_cases hb : b = l <;> simp [matUnit24, ha, hb]
  · simp only [hjk, ↓reduceIte, Matrix.zero_apply]
    refine Finset.sum_eq_zero fun m _ ↦ ?_
    by_cases hm : m = j
    · subst hm; simp [matUnit24, hjk]
    · simp [matUnit24, hm]
noncomputable def projShift0Gen {m N : ℕ} (r : QRegister m N) (yIdx : Fin (2 ^ m)) : Operator
    (2 ^ N) := r.embedMatrix (matUnit24 0 yIdx)
noncomputable def projBasisGen {m N : ℕ} (r : QRegister m N) (yIdx : Fin (2 ^ m)) : Operator
    (2 ^ N) := r.embedMatrix (matUnit24 yIdx yIdx)
theorem projBasisGen_apply {m N : ℕ} (r : QRegister m N) (yIdx : Fin (2 ^ m))
    (x' x : Fin (2 ^ N)) : projBasisGen r yIdx x' x = if x' = x ∧ r.extractIndex x = yIdx then
    1 else 0 := by
  unfold projBasisGen matUnit24
  rw [QRegister.embedMatrix_apply]
  by_cases h : x' = x ∧ r.extractIndex x = yIdx
  · rcases h with ⟨rfl, hx⟩
    simp [hx]
  · simp only [h, ↓reduceIte]
    by_cases henv : (r.basisSplitEquiv x').2 = (r.basisSplitEquiv x).2
    · simp only [henv, ↓reduceIte, mul_one, Matrix.of_apply, ite_eq_right_iff, one_ne_zero,
      imp_false]
      rintro ⟨hx', hx⟩
      exact h ⟨r.basisSplitEquiv.injective (Prod.ext
        (by rw [QRegister.basisSplitEquiv_apply_fst, QRegister.basisSplitEquiv_apply_fst, hx', hx])
        henv), hx⟩
    · simp [henv]
theorem sum_projBasisGen {m N : ℕ} (r : QRegister m N) :
    (∑ yIdx : Fin (2 ^ m), projBasisGen r yIdx) = (1 : Operator (2 ^ N)) := by
  ext x' x
  rw [Matrix.sum_apply, Matrix.one_apply]
  simp_rw [projBasisGen_apply]
  by_cases hxx : x' = x
  · subst hxx
    rw [Finset.sum_eq_single (r.extractIndex x')
      (fun y _ hy ↦ by simp [hy.symm]) (by simp)]
    simp
  · simp [hxx]
theorem projBasisGen_idem {m N : ℕ} (r : QRegister m N) (yIdx : Fin (2 ^ m)) :
    projBasisGen r yIdx * projBasisGen r yIdx = projBasisGen r yIdx := by
  unfold projBasisGen
  rw [← r.embedMatrix_mul, matUnit24_mul]
  simp only [↓reduceIte]
theorem projBasisGen_isHermitian {m N : ℕ} (r : QRegister m N) (yIdx : Fin (2 ^ m)) :
    (projBasisGen r yIdx).IsHermitian := by
  rw [Matrix.IsHermitian, projBasisGen, ← r.embedMatrix_conjTranspose, matUnit24_conjTranspose]
theorem projShift0Gen_conjTranspose_mul_projBasis0 {m N : ℕ} (r : QRegister m N)
    (yIdx : Fin (2 ^ m)) :
    (projShift0Gen r yIdx)ᴴ * projBasisGen r 0 * projShift0Gen r yIdx = projBasisGen r yIdx := by
  unfold projShift0Gen projBasisGen
  rw [← r.embedMatrix_conjTranspose, ← r.embedMatrix_mul, ← r.embedMatrix_mul,
    matUnit24_conjTranspose, matUnit24_mul]
  simp only [↓reduceIte]
  rw [matUnit24_mul]
  simp only [↓reduceIte]
theorem projShift0Gen_mul_conjTranspose {m N : ℕ} (r : QRegister m N) (y₁ y₂ : Fin (2 ^ m)) :
    projShift0Gen r y₁ * (projShift0Gen r y₂)ᴴ = if y₁ = y₂ then projBasisGen r 0 else 0 := by
  unfold projShift0Gen projBasisGen
  rw [← r.embedMatrix_conjTranspose, ← r.embedMatrix_mul, matUnit24_conjTranspose, matUnit24_mul]
  by_cases h : y₁ = y₂ <;> simp [h]
theorem projBasis0_mul_projShift0Gen {m N : ℕ} (r : QRegister m N) (yIdx : Fin (2 ^ m)) :
    projBasisGen r 0 * projShift0Gen r yIdx = projShift0Gen r yIdx := by
  unfold projBasisGen projShift0Gen
  rw [← r.embedMatrix_mul, matUnit24_mul]
  simp only [↓reduceIte]
theorem projShift0Gen_conjTranspose_mul_projBasis0_self {m N : ℕ} (r : QRegister m N)
    (yIdx : Fin (2 ^ m)) :
    (projShift0Gen r yIdx)ᴴ * projBasisGen r 0 = (projShift0Gen r yIdx)ᴴ := by
  unfold projBasisGen projShift0Gen
  rw [← r.embedMatrix_conjTranspose, ← r.embedMatrix_mul, matUnit24_conjTranspose, matUnit24_mul]
  simp only [↓reduceIte]
theorem norm_projShift0Gen_le_one {m N : ℕ} (r : QRegister m N) (yIdx : Fin (2 ^ m)) :
    ‖projShift0Gen r yIdx‖ ≤ 1 := by
  have hsq : ‖(projShift0Gen r yIdx)ᴴ‖ * ‖(projShift0Gen r yIdx)ᴴ‖ ≤ 1 := by
    rw [← Matrix.l2_opNorm_conjTranspose_mul_self (projShift0Gen r yIdx)ᴴ,
      conjTranspose_conjTranspose, projShift0Gen_mul_conjTranspose]
    simp only [↓reduceIte]
    exact norm_projector_le_one _ (projBasisGen_isHermitian r 0) (projBasisGen_idem r 0)
  have hle : ‖(projShift0Gen r yIdx)ᴴ‖ ≤ 1 := by nlinarith [norm_nonneg (projShift0Gen r yIdx)ᴴ]
  simpa only [Matrix.l2_opNorm_conjTranspose] using hle
theorem projBasisGen_mul_of_idle {m N : ℕ} (r : QRegister m N) {A : Operator (2 ^ N)} (hIdle :
    ∀ M : Operator (2 ^ m), A * r.embedMatrix M = r.embedMatrix M * A) (yIdx : Fin (2 ^ m)) :
    projBasisGen r yIdx * A = (projShift0Gen r yIdx)ᴴ * projBasisGen r 0 * A * projBasisGen r
    0 * projShift0Gen r yIdx := by
  have hc1 : projShift0Gen r yIdx * A = A * projShift0Gen r yIdx := (hIdle _).symm
  have hc0 : projBasisGen r 0 * A = A * projBasisGen r 0 := (hIdle _).symm
  calc projBasisGen r yIdx * A
      = ((projShift0Gen r yIdx)ᴴ * projBasisGen r 0 * projShift0Gen r yIdx) * A := by
          rw [projShift0Gen_conjTranspose_mul_projBasis0]
    _ = (projShift0Gen r yIdx)ᴴ * (projBasisGen r 0 * projBasisGen r 0) *
          (projShift0Gen r yIdx * A) := by
          rw [projBasisGen_idem r 0]; simp only [Matrix.mul_assoc]
    _ = (projShift0Gen r yIdx)ᴴ * projBasisGen r 0 * (projBasisGen r 0 * A) *
          projShift0Gen r yIdx := by rw [hc1]; simp only [Matrix.mul_assoc]
    _ = (projShift0Gen r yIdx)ᴴ * projBasisGen r 0 * A * projBasisGen r 0 *
          projShift0Gen r yIdx := by rw [hc0]; simp only [Matrix.mul_assoc]
noncomputable def projLift0Gen {m N : ℕ} (r : QRegister m N) (X : Operator (2 ^ N)) : Operator
    (2 ^ N) := ∑ yIdx : Fin (2 ^ m), (projShift0Gen r yIdx)ᴴ * X * projShift0Gen r yIdx
theorem projLift0Gen_conjTranspose {m N : ℕ} (r : QRegister m N) {X : Operator (2 ^ N)}
    (hX : Xᴴ = X) : (projLift0Gen r X)ᴴ = projLift0Gen r X := by
  unfold projLift0Gen
  rw [conjTranspose_sum]
  refine Finset.sum_congr rfl fun yIdx _ ↦ ?_
  rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hX, Matrix.mul_assoc]
theorem projShift0Gen_mul_projLift0Gen_of_comm {m N : ℕ} (r : QRegister m N)
    {X : Operator (2 ^ N)} (hcomm0 : projBasisGen r 0 * X = X * projBasisGen r 0)
    (yIdx : Fin (2 ^ m)) :
    projShift0Gen r yIdx * projLift0Gen r X = X * projShift0Gen r yIdx := by
  unfold projLift0Gen
  rw [Matrix.mul_sum]
  have hterm : ∀ z : Fin (2 ^ m),
      projShift0Gen r yIdx * ((projShift0Gen r z)ᴴ * X * projShift0Gen r z) =
        if yIdx = z then projBasisGen r 0 * X * projShift0Gen r z else 0 := fun z ↦ by
    calc projShift0Gen r yIdx * ((projShift0Gen r z)ᴴ * X * projShift0Gen r z)
        = (projShift0Gen r yIdx * (projShift0Gen r z)ᴴ) * X * projShift0Gen r z := by
            simp only [Matrix.mul_assoc]
      _ = if yIdx = z then projBasisGen r 0 * X * projShift0Gen r z else 0 := by
            rw [projShift0Gen_mul_conjTranspose]
            by_cases h : yIdx = z <;> simp [h]
  simp_rw [hterm]
  rw [Finset.sum_eq_single yIdx
    (fun z _ hz ↦ ite_eq_right_iff.mpr fun h ↦ absurd h.symm hz) (by simp)]
  simp only [↓reduceIte]
  rw [hcomm0, Matrix.mul_assoc, projBasis0_mul_projShift0Gen]
theorem projLift0Gen_mul_projShift0Gen_conjTranspose_of_comm {m N : ℕ} (r : QRegister m N)
    {X : Operator (2 ^ N)} (hsa : Xᴴ = X)
    (hcomm0 : projBasisGen r 0 * X = X * projBasisGen r 0) (yIdx : Fin (2 ^ m)) :
    projLift0Gen r X * (projShift0Gen r yIdx)ᴴ = (projShift0Gen r yIdx)ᴴ * X := by
  have h := congrArg Matrix.conjTranspose (projShift0Gen_mul_projLift0Gen_of_comm r hcomm0 yIdx)
  rwa [conjTranspose_mul, conjTranspose_mul, projLift0Gen_conjTranspose r hsa, hsa] at h
theorem projLift0Gen_comm_embedMatrix {m N : ℕ} (r : QRegister m N) (X : Operator (2 ^ N))
    (M : Operator (2 ^ m)) :
    projLift0Gen r X * r.embedMatrix M = r.embedMatrix M * projLift0Gen r X := by
  have hexpand : r.embedMatrix M = ∑ y₁ : Fin (2 ^ m), ∑ y₂ : Fin (2 ^ m), (M y₁ y₂) •
      ((projShift0Gen r y₁)ᴴ * projShift0Gen r y₂) := by
    have hM : M = ∑ y₁ : Fin (2 ^ m), ∑ y₂ : Fin (2 ^ m),
        (M y₁ y₂) • (matUnit24 y₁ 0 * matUnit24 0 y₂) := by
      ext a b
      rw [Matrix.sum_apply]
      have hinner : ∀ x : Fin (2 ^ m),
          (∑ x_1 : Fin (2 ^ m),(M x x_1) • (matUnit24 x 0 * matUnit24 0 x_1)) a b =
            ∑ x_1 : Fin (2 ^ m), M x x_1 * matUnit24 x x_1 a b := fun x ↦ by
        rw [Matrix.sum_apply]
        refine Finset.sum_congr rfl fun x_1 _ ↦ ?_
        rw [Matrix.smul_apply, smul_eq_mul, matUnit24_mul]
        simp only [↓reduceIte]
      simp_rw [hinner]
      rw [Finset.sum_eq_single a (fun k _ hk ↦ Finset.sum_eq_zero fun l _ ↦ by
          simp [matUnit24, hk.symm]) (by simp),
        Finset.sum_eq_single b (fun l _ hl ↦ by simp [matUnit24, hl.symm]) (by simp)]
      simp [matUnit24]
    conv_lhs => rw [hM]
    rw [r.embedMatrix_sum]
    refine Finset.sum_congr rfl fun y₁ _ ↦ ?_
    rw [r.embedMatrix_sum]
    refine Finset.sum_congr rfl fun y₂ _ ↦ ?_
    rw [r.embedMatrix_smul, r.embedMatrix_mul, ← matUnit24_conjTranspose 0 y₁,
      r.embedMatrix_conjTranspose]
    rfl
  rw [hexpand, Matrix.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun y₁ _ ↦ ?_
  rw [Matrix.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun y₂ _ ↦ ?_
  rw [Matrix.mul_smul, Matrix.smul_mul]
  congr 1
  unfold projLift0Gen
  rw [Finset.sum_mul, Matrix.mul_sum]
  have hLHS : ∑ z : Fin (2 ^ m),
      ((projShift0Gen r z)ᴴ * X * projShift0Gen r z) * ((projShift0Gen r y₁)ᴴ *
        projShift0Gen r y₂) =
        (projShift0Gen r y₁)ᴴ * X * projShift0Gen r y₂ := by
    refine (Finset.sum_eq_single y₁ (fun z _ hz ↦ ?_) (by simp)).trans ?_
    · calc ((projShift0Gen r z)ᴴ * X * projShift0Gen r z) *
              ((projShift0Gen r y₁)ᴴ * projShift0Gen r y₂)
          = (projShift0Gen r z)ᴴ * X * (projShift0Gen r z * (projShift0Gen r y₁)ᴴ) *
              projShift0Gen r y₂ := by simp only [Matrix.mul_assoc]
        _ = 0 := by rw [projShift0Gen_mul_conjTranspose]; simp [hz]
    · calc ((projShift0Gen r y₁)ᴴ * X * projShift0Gen r y₁) *
              ((projShift0Gen r y₁)ᴴ * projShift0Gen r y₂)
          = (projShift0Gen r y₁)ᴴ * X *
              ((projShift0Gen r y₁ * (projShift0Gen r y₁)ᴴ) * projShift0Gen r y₂) := by
              simp only [Matrix.mul_assoc]
        _ = (projShift0Gen r y₁)ᴴ * X * projShift0Gen r y₂ := by
              rw [projShift0Gen_mul_conjTranspose]; simp only [↓reduceIte,
                projBasis0_mul_projShift0Gen]
  have hRHS : ∑ z : Fin (2 ^ m),
      ((projShift0Gen r y₁)ᴴ * projShift0Gen r y₂) * ((projShift0Gen r z)ᴴ * X *
        projShift0Gen r z) =
        (projShift0Gen r y₁)ᴴ * X * projShift0Gen r y₂ := by
    refine (Finset.sum_eq_single y₂ (fun z _ hz ↦ ?_) (by simp)).trans ?_
    · calc ((projShift0Gen r y₁)ᴴ * projShift0Gen r y₂) *
              ((projShift0Gen r z)ᴴ * X * projShift0Gen r z)
          = (projShift0Gen r y₁)ᴴ * (projShift0Gen r y₂ * (projShift0Gen r z)ᴴ) *
              X * projShift0Gen r z := by simp only [Matrix.mul_assoc]
        _ = 0 := by rw [projShift0Gen_mul_conjTranspose]; simp [hz.symm]
    · calc ((projShift0Gen r y₁)ᴴ * projShift0Gen r y₂) *
              ((projShift0Gen r y₂)ᴴ * X * projShift0Gen r y₂)
          = ((projShift0Gen r y₁)ᴴ * (projShift0Gen r y₂ * (projShift0Gen r y₂)ᴴ)) *
              X * projShift0Gen r y₂ := by simp only [Matrix.mul_assoc]
        _ = (projShift0Gen r y₁)ᴴ * X * projShift0Gen r y₂ := by
              rw [projShift0Gen_mul_conjTranspose]
              simp only [↓reduceIte, projShift0Gen_conjTranspose_mul_projBasis0_self]
  exact hLHS.trans hRHS.symm
theorem projLift0Gen_apply {m N : ℕ} (r : QRegister m N) (X : Operator (2 ^ N))
    (a b : Fin (2 ^ N)) : projLift0Gen r X a b = if r.extractIndex a = r.extractIndex b then X
    (r.basisSplitEquiv.symm (0, (r.basisSplitEquiv a).2))
    (r.basisSplitEquiv.symm (0, (r.basisSplitEquiv b).2)) else 0 := by
  let z0 (w : Fin (2 ^ N)) : Fin (2 ^ N) := r.basisSplitEquiv.symm (0, (r.basisSplitEquiv w).2)
  have hT : ∀ (u v : Fin (2 ^ N)) (y : Fin (2 ^ m)),
      projShift0Gen r y u v = if u = z0 v ∧ r.extractIndex v = y then 1 else 0 := fun u v y ↦ by
    unfold projShift0Gen matUnit24
    rw [QRegister.embedMatrix_apply]
    by_cases hc : u = z0 v ∧ r.extractIndex v = y
    · rcases hc with ⟨rfl, hv⟩
      have hu0 : r.extractIndex (z0 v) = 0 := by
        rw [← QRegister.basisSplitEquiv_apply_fst]; simp [z0]
      simp [z0, hu0, hv]
    · simp only [hc, ↓reduceIte]
      by_cases henv : (r.basisSplitEquiv u).2 = (r.basisSplitEquiv v).2
      · simp only [henv, ↓reduceIte, mul_one, Matrix.of_apply, ite_eq_right_iff, one_ne_zero,
        imp_false]
        rintro ⟨hu0, hv⟩
        exact hc ⟨r.basisSplitEquiv.injective (Prod.ext
          (by rw [QRegister.basisSplitEquiv_apply_fst, hu0]
              simp [z0])
          (by simp [z0, henv])), hv⟩
      · simp [henv]
  unfold projLift0Gen
  rw [Matrix.sum_apply]
  have hterm : ∀ y : Fin (2 ^ m),
      ((projShift0Gen r y)ᴴ * X * projShift0Gen r y) a b =
        if r.extractIndex a = y ∧ r.extractIndex b = y then X (z0 a) (z0 b) else 0 := fun y ↦ by
    rw [Matrix.mul_apply, Finset.sum_eq_single (z0 b)
        (fun m _ hm ↦ by rw [hT m b y]; simp [hm]) (by simp),
      Matrix.mul_apply, Finset.sum_eq_single (z0 a)
        (fun m _ hm ↦ by simp [Matrix.conjTranspose_apply, hT m a y, hm]) (by simp)]
    simp only [Matrix.conjTranspose_apply, hT]
    by_cases ha : r.extractIndex a = y <;> by_cases hb : r.extractIndex b = y <;> simp [ha, hb]
  simp_rw [hterm]
  rw [Finset.sum_eq_single (r.extractIndex a) (fun y _ hy ↦ by simp [hy.symm]) (by simp)]
  by_cases heq : r.extractIndex a = r.extractIndex b
  · simp [heq, z0]
  · simp [heq, Ne.symm heq]
noncomputable abbrev projBasisProj (yIdx : Fin (2 ^ 24)) : Operator (2 ^ systemQubits) :=
  projBasisGen rProj24_sp yIdx
theorem projBasisProj_apply (yIdx : Fin (2 ^ 24)) (x' x : Fin (2 ^ systemQubits)) :
    projBasisProj yIdx x' x = if x' = x ∧ rProj24_sp.extractIndex x = yIdx then 1 else 0 :=
    projBasisGen_apply rProj24_sp yIdx x' x
noncomputable abbrev elecFermionicProjector (spinUp : Finset (Fin numElectrons)) : Operator
    (2 ^ systemQubits) := projLift0Gen rProj24_sp (fermionicProjector spinUp)
set_option exponentiation.threshold 32 in
open Slots01AndGridGuardBridge (projAxisWord8) in
open SpecsAux.BridgeFermionicComm.SpecInner
    (signMagnitude_eq_of_momentum_eq_of_isGridState) in
theorem projBasisProj_comm_fermionicProjector (spinUp : Finset (Fin numElectrons))
    (yIdx : Fin (2 ^ 24)) : projBasisProj yIdx * fermionicProjector spinUp =
    fermionicProjector spinUp * projBasisProj yIdx := by
  ext x' x
  rw [Matrix.mul_apply, Matrix.mul_apply,
    Finset.sum_eq_single x'
      (fun k _ hk ↦ by rw [projBasisProj_apply, ite_eq_of_neg (fun h ↦ hk h.1.symm), zero_mul])
      (fun h ↦ absurd (Finset.mem_univ _) h),
    Finset.sum_eq_single x
      (fun k _ hk ↦ by rw [projBasisProj_apply, ite_eq_of_neg (fun h ↦ hk h.1), mul_zero])
      (fun h ↦ absurd (Finset.mem_univ _) h)]
  simp only [projBasisProj_apply, true_and]
  by_cases hP : fermionicProjector spinUp x' x = 0
  · simp [hP]
  · have hsame : rProj24_sp.extractIndex x' = rProj24_sp.extractIndex x := by
      unfold fermionicProjector at hP
      simp only [Matrix.of_apply] at hP
      by_cases hgrid : IsGridState x' ∧ IsGridState x
      · simp only [hgrid, and_self, ↓reduceIte] at hP
        have hsum_ne : (∑ g : Equiv.Perm (Fin numElectrons), if (∀ i, g i ∈ spinUp ↔ i ∈
            spinUp) ∧ momentum x' Particle.projectile = momentum x Particle.projectile ∧ ∀ i,
            momentum x' (Particle.electron i) = momentum x (Particle.electron (g i)) then
            ((Equiv.Perm.sign g : ℤ) : ℂ) else 0) ≠ 0 :=
          fun hz ↦ hP (by rw [hz, zero_div])
        obtain ⟨g, _, hg⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum_ne
        by_cases hcond : (∀ i, g i ∈ spinUp ↔ i ∈ spinUp) ∧
            momentum x' Particle.projectile = momentum x Particle.projectile ∧
            ∀ i, momentum x' (Particle.electron i) = momentum x (Particle.electron (g i))
        · apply projGridEquiv24.injective; funext w
          rw [projGridEquiv24_extractIndex_eq_projAxisWord8,
            projGridEquiv24_extractIndex_eq_projAxisWord8]
          have hsm :=
            signMagnitude_eq_of_momentum_eq_of_isGridState
              hgrid.1 hgrid.2 .projectile w (congrFun hcond.2.1 w)
          simp [projAxisWord8, hsm]
        · simp [hcond] at hg
      · simp [hgrid] at hP
    rw [hsame]
    by_cases hy : rProj24_sp.extractIndex x = yIdx <;> simp [hy]
theorem elecFermionicProjector_conjTranspose (spinUp : Finset (Fin numElectrons)) :
    (elecFermionicProjector spinUp)ᴴ = elecFermionicProjector spinUp :=
  projLift0Gen_conjTranspose rProj24_sp
    (SpecsAux.BridgeFermionicComm.SpecInner.fermionicProjector_isHermitian spinUp).eq
theorem elecFermionicProjector_comm_embedMatrix (spinUp : Finset (Fin numElectrons))
    (M : Operator (2 ^ 24)) : elecFermionicProjector spinUp * rProj24_sp.embedMatrix M =
    rProj24_sp.embedMatrix M * elecFermionicProjector spinUp := projLift0Gen_comm_embedMatrix
    rProj24_sp (fermionicProjector spinUp) M
set_option exponentiation.threshold 32 in
open Slots01AndGridGuardBridge (projAxisWord8 elecAxisWord6) in
open SixSlotEndpointJunctionBridge (isGridState_iff_axisWords_ne_minInt) in
theorem z0_grid_and_momenta {w : Fin (2 ^ systemQubits)}
    (hw_el : ∀ i : Fin numElectrons, ∀ ax : Fin 3, (elecAxisWord6 w i ax).val ≠ 32) :
    let z0 := rProj24_sp.basisSplitEquiv.symm (0, (rProj24_sp.basisSplitEquiv w).2)
    IsGridState z0 ∧ momentum z0 .projectile = 0 ∧
      ∀ i : Fin numElectrons, momentum z0 (.electron i) = momentum w (.electron i) := by
  intro z0
  have hex0 : rProj24_sp.extractIndex z0 = 0 := by
    rw [← QRegister.basisSplitEquiv_apply_fst]; simp [z0]
  have hp0 : ∀ ax : Fin 3, projAxisWord8 z0 ax = 0 := fun ax ↦ by
    rw [← projGridEquiv24_extractIndex_eq_projAxisWord8 z0 ax, hex0]; ext; simp [projGridEquiv24]
  have hbits : ∀ bit < 3924, z0.val.testBit bit = w.val.testBit bit :=
    (env_eq_iff_electron_testBit_eq z0 w).mp (by simp [z0])
  refine ⟨(isGridState_iff_axisWords_ne_minInt z0).mpr ⟨fun i ax ↦ ?_, fun ax ↦ ?_⟩,
    funext fun ax ↦ ?_, fun i ↦ funext fun ax ↦ ?_⟩
  · have hsm := signMagnitude_electron_eq_of_testBit_eq hbits i ax
    simpa [elecAxisWord6, hsm] using hw_el i ax
  · rw [hp0 ax]; decide
  · rw [← esmSignedInt256_projAxisWord8_eq_momentum, hp0 ax]; rfl
  · have hsm := signMagnitude_electron_eq_of_testBit_eq hbits i ax
    simp [momentum, hsm]
theorem fermionicProjector_eq_zero_of_not_grid (spinUp : Finset (Fin numElectrons))
    {a b : Fin (2 ^ systemQubits)} (h : ¬ (IsGridState a ∧ IsGridState b)) :
    fermionicProjector spinUp a b = 0 := by
  unfold fermionicProjector
  simp only [Matrix.of_apply, h, ↓reduceIte]
theorem fermionicProjector_eq_of_same_momenta (spinUp : Finset (Fin numElectrons))
    {zx' zk x' k : Fin (2 ^ systemQubits)} (hz0x' : IsGridState zx') (hz0k : IsGridState zk)
    (hx' : IsGridState x') (hk_grid : IsGridState k) (hp0x' : momentum zx' .projectile = 0)
    (hp0k : momentum zk .projectile = 0)
    (hmp_same : momentum x' .projectile = momentum k .projectile) (he0x' : ∀ i, momentum zx'
    (.electron i) = momentum x' (.electron i))
    (he0k : ∀ i, momentum zk (.electron i) = momentum k (.electron i)) : fermionicProjector
    spinUp zx' zk = fermionicProjector spinUp x' k := by
  unfold fermionicProjector
  simp only [Matrix.of_apply, hz0x', hz0k, hx', hk_grid, and_self, ↓reduceIte,
    hp0x', hp0k, hmp_same, true_and]
  refine congrArg (· / ((spinUp.card.factorial * (numElectrons -
    spinUp.card).factorial : ℕ) : ℂ)) ?_
  refine Finset.sum_congr rfl fun g _ ↦ ?_
  have hme : (∀ i, momentum zx' (.electron i) = momentum zk (.electron (g i))) ↔
      (∀ i, momentum x' (.electron i) = momentum k (.electron (g i))) :=
    forall_congr' fun i ↦ by rw [he0x' i, he0k (g i)]
  exact if_congr (and_congr_right fun _ ↦ hme) rfl rfl
set_option exponentiation.threshold 32 in
theorem z0_electron_testBit_eq (w : Fin (2 ^ systemQubits)) :
    let z0 := rProj24_sp.basisSplitEquiv.symm (0, (rProj24_sp.basisSplitEquiv w).2)
    ∀ bit < 3924, z0.val.testBit bit = w.val.testBit bit := by
  intro z0
  exact (env_eq_iff_electron_testBit_eq z0 w).mp (by simp [z0])
open Slots01AndGridGuardBridge (projAxisWord8 elecAxisWord6) in
open SixSlotEndpointJunctionBridge (isGridState_iff_axisWords_ne_minInt) in
theorem z0_isGridState_iff_aux {z0x' x' : Fin (2 ^ systemQubits)}
    (hbits : ∀ bit < 3924, z0x'.val.testBit bit = x'.val.testBit bit)
    (hFwd : (∀ i ax, (elecAxisWord6 x' i ax).val ≠ 32) → IsGridState z0x')
    (hy_not128 : ∀ ax : Fin 3, (projAxisWord8 x' ax).val ≠ 128) :
    IsGridState z0x' ↔ IsGridState x' := by
  constructor
  · intro hz
    refine (isGridState_iff_axisWords_ne_minInt x').mpr ⟨fun i ax ↦ ?_, hy_not128⟩
    have hsm := signMagnitude_electron_eq_of_testBit_eq hbits i ax
    have h1 := ((isGridState_iff_axisWords_ne_minInt z0x').mp hz).1 i ax
    dsimp only [elecAxisWord6] at h1 ⊢
    rwa [← hsm]
  · intro hx'
    exact hFwd ((isGridState_iff_axisWords_ne_minInt x').mp hx').1
theorem fermionicProjector_eq_zero_of_extractIndex_ne
    (spinUp : Finset (Fin numElectrons)) {x' k : Fin (2 ^ systemQubits)}
    (hne : rProj24_sp.extractIndex x' ≠ rProj24_sp.extractIndex k) :
    fermionicProjector spinUp x' k = 0 := by
  have hcomm := congrFun (congrFun
    (projBasisProj_comm_fermionicProjector spinUp (rProj24_sp.extractIndex x')) x') k
  rw [Matrix.mul_apply, Matrix.mul_apply,
    Finset.sum_eq_single x'
      (fun m _ hm ↦ by rw [projBasisProj_apply, ite_eq_of_neg (fun h ↦ hm h.1.symm), zero_mul])
      (fun h ↦ absurd (Finset.mem_univ _) h),
    Finset.sum_eq_single k
      (fun m _ hm ↦ by rw [projBasisProj_apply, ite_eq_of_neg (fun h ↦ hm h.1), mul_zero])
      (fun h ↦ absurd (Finset.mem_univ _) h),
    projBasisProj_apply, ite_eq_of_pos ⟨rfl, rfl⟩, one_mul,
    projBasisProj_apply, ite_eq_of_neg (fun h ↦ hne h.2.symm), mul_zero] at hcomm
  exact hcomm
private noncomputable def lemHex354 (w : Fin (2 ^ systemQubits)) : Fin (2 ^ systemQubits) :=
    Classical.choose (⟨rProj24_sp.basisSplitEquiv.symm (0, (rProj24_sp.basisSplitEquiv w).2),
    rfl⟩ : ∃ y : Fin (2 ^ systemQubits), y = rProj24_sp.basisSplitEquiv.symm (0,
    (rProj24_sp.basisSplitEquiv w).2))
private theorem lemHex355 (w : Fin (2 ^ systemQubits)) : lemHex354 w =
    rProj24_sp.basisSplitEquiv.symm
    (0, (rProj24_sp.basisSplitEquiv w).2) := Classical.choose_spec
    (⟨rProj24_sp.basisSplitEquiv.symm (0, (rProj24_sp.basisSplitEquiv w).2), rfl⟩ : ∃ y : Fin
    (2 ^ systemQubits), y = rProj24_sp.basisSplitEquiv.symm (0, (rProj24_sp.basisSplitEquiv
    w).2))
private theorem lemHex356 (spinUp : Finset (Fin numElectrons)) (a b : Fin (2 ^ systemQubits)) :
    elecFermionicProjector spinUp a b = if rProj24_sp.extractIndex a = rProj24_sp.extractIndex
    b then fermionicProjector spinUp (lemHex354 a) (lemHex354 b) else 0 := by
  rw [lemHex355 a, lemHex355 b]
  exact projLift0Gen_apply rProj24_sp (fermionicProjector spinUp) a b
set_option exponentiation.threshold 32 in
private theorem lemHex357 (w : Fin (2 ^ systemQubits)) :
    ∀ bit < 3924, (lemHex354 w).val.testBit bit = w.val.testBit bit := by
  rw [lemHex355 w]
  exact z0_electron_testBit_eq w
set_option exponentiation.threshold 32 in
open Slots01AndGridGuardBridge (elecAxisWord6) in
private theorem lemHex358 {w : Fin (2 ^ systemQubits)}
    (hw_el : ∀ i : Fin numElectrons, ∀ ax : Fin 3, (elecAxisWord6 w i ax).val ≠ 32) :
    IsGridState (lemHex354 w) ∧ momentum (lemHex354 w) .projectile = 0 ∧
      ∀ i : Fin numElectrons, momentum (lemHex354 w) (.electron i) = momentum w (.electron i) := by
  rw [lemHex355 w]
  exact z0_grid_and_momenta hw_el
set_option allowUnsafeReducibility true in
attribute [local irreducible] lemHex354
open Slots01AndGridGuardBridge (projAxisWord8) in
open SixSlotEndpointJunctionBridge (isGridState_iff_axisWords_ne_minInt) in
private theorem lemHex359 (spinUp : Finset (Fin numElectrons)) : elecFermionicProjector spinUp *
    fermionicProjector spinUp = fermionicProjector spinUp * fermionicProjector spinUp := by
  ext x' x
  rw [Matrix.mul_apply, Matrix.mul_apply]
  by_cases hx : IsGridState x
  · refine Finset.sum_congr rfl fun k _ ↦ ?_
    by_cases hPkx : fermionicProjector spinUp k x = 0
    · rw [hPkx, mul_zero, mul_zero]
    · have hk_grid : IsGridState k := by
        by_contra hnk
        exact hPkx (fermionicProjector_eq_zero_of_not_grid spinUp (fun hg ↦ hnk hg.1))
      rw [lemHex356]
      by_cases hex : rProj24_sp.extractIndex x' = rProj24_sp.extractIndex k
      · rw [ite_eq_of_pos hex]
        refine congrArg (· * fermionicProjector spinUp k x) ?_
        have hy_not128 : ∀ ax : Fin 3, (projAxisWord8 x' ax).val ≠ 128 := fun ax ↦ by
          have hkw := ((isGridState_iff_axisWords_ne_minInt k).mp hk_grid).2 ax
          rwa [← projGridEquiv24_extractIndex_eq_projAxisWord8 k ax, ← hex,
            projGridEquiv24_extractIndex_eq_projAxisWord8 x' ax] at hkw
        obtain ⟨hz0k, hp0k, he0k⟩ :=
          lemHex358 ((isGridState_iff_axisWords_ne_minInt k).mp hk_grid).1
        have hgx'_iff := z0_isGridState_iff_aux (lemHex357 x') (fun he ↦ (lemHex358 he).1) hy_not128
        have hmp_same : momentum x' .projectile = momentum k .projectile := funext fun ax ↦ by
          rw [← esmSignedInt256_projAxisWord8_eq_momentum,
            ← esmSignedInt256_projAxisWord8_eq_momentum,
            ← projGridEquiv24_extractIndex_eq_projAxisWord8,
            ← projGridEquiv24_extractIndex_eq_projAxisWord8, hex]
        by_cases hx' : IsGridState x'
        · obtain ⟨hz0x', hp0x', he0x'⟩ :=
            lemHex358 ((isGridState_iff_axisWords_ne_minInt x').mp hx').1
          exact fermionicProjector_eq_of_same_momenta spinUp hz0x' hz0k hx' hk_grid hp0x' hp0k
            hmp_same he0x' he0k
        · exact (fermionicProjector_eq_zero_of_not_grid spinUp (fun hg ↦
          hx' (hgx'_iff.mp hg.1))).trans
            (fermionicProjector_eq_zero_of_not_grid spinUp (fun hg ↦ hx' hg.1)).symm
      · rw [ite_eq_of_neg hex, zero_mul,
          fermionicProjector_eq_zero_of_extractIndex_ne spinUp hex, zero_mul]
  · have hzero : ∀ k : Fin (2 ^ systemQubits), fermionicProjector spinUp k x = 0 := fun k ↦
      fermionicProjector_eq_zero_of_not_grid spinUp (fun hg ↦ hx hg.2)
    simp only [hzero, mul_zero]
theorem elecFermionicProjector_mul_fermionicProjector (spinUp : Finset (Fin numElectrons)) :
    elecFermionicProjector spinUp * fermionicProjector spinUp = fermionicProjector spinUp :=
    (lemHex359 spinUp).trans (fermionicProjector_idem spinUp)
theorem fermionicProjector_mul_elecFermionicProjector (spinUp : Finset (Fin numElectrons)) :
    fermionicProjector spinUp * elecFermionicProjector spinUp = fermionicProjector spinUp := by
  have h := congrArg Matrix.conjTranspose (elecFermionicProjector_mul_fermionicProjector spinUp)
  rwa [conjTranspose_mul, elecFermionicProjector_conjTranspose,
    (SpecsAux.BridgeFermionicComm.SpecInner.fermionicProjector_isHermitian spinUp).eq] at h
theorem norm_sum_biOrthogonal_le {ι d : Type*} [Fintype d] [DecidableEq d]
    (S : Finset ι) (B : ι → Matrix d d ℂ) {ε : ℝ} (hε : 0 ≤ ε)
    (hRow : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → B i * (B j)ᴴ = 0)
    (hCol : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → (B i)ᴴ * B j = 0) (hBound : ∀ i ∈ S, ‖B i‖ ≤ ε) : ‖∑ i ∈
    S, B i‖ ≤ ε := by
  classical
  by_cases hd : IsEmpty d
  · have : IsEmpty d := hd
    rw [Subsingleton.elim (∑ i ∈ S, B i) 0, norm_zero]
    exact hε
  have : Nonempty d := not_isEmpty_iff.mp hd
  let M : Matrix d d ℂ := ∑ i ∈ S, B i
  let P_i : ι → Matrix d d ℂ := fun i ↦ (B i)ᴴ * B i
  have hCrossPow : ∀ {i j : ι}, i ∈ S → j ∈ S → i ≠ j → ∀ k l : ℕ,
      (P_i i ^ (k + 1)) * (P_i j ^ (l + 1)) = 0 := by
    intro i j hi hj hij k l
    have hmid : P_i i * P_i j = 0 := by
      calc ((B i)ᴴ * B i) * ((B j)ᴴ * B j)
          = (B i)ᴴ * (B i * (B j)ᴴ) * B j := by simp only [Matrix.mul_assoc]
        _ = 0 := by rw [hRow i hi j hj hij]; simp
    calc (P_i i ^ (k + 1)) * (P_i j ^ (l + 1))
        = (P_i i ^ k * P_i i) * (P_i j * P_i j ^ l) := by rw [pow_succ, pow_succ']
      _ = P_i i ^ k * (P_i i * P_i j) * P_i j ^ l := by simp only [Matrix.mul_assoc]
      _ = 0 := by rw [hmid]; simp
  have hBase : Mᴴ * M = ∑ i ∈ S, P_i i ^ 1 := by
    dsimp [M, P_i]
    rw [conjTranspose_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    rw [Matrix.mul_sum, Finset.sum_eq_single i
      (fun j hj hij ↦ hCol i hi j hj hij.symm)
      (fun hni ↦ absurd hi hni), pow_one]
  have hDouble : ∀ m : ℕ, ‖M‖ ^ (2 ^ (m + 1)) = ‖∑ i ∈ S, P_i i ^ (2 ^ m)‖ := by
    intro m
    induction m with
    | zero =>
      norm_num
      rw [sq, ← Matrix.l2_opNorm_conjTranspose_mul_self M, hBase]
      simp only [pow_one]
    | succ m ih =>
      let Am : Matrix d d ℂ := ∑ i ∈ S, P_i i ^ (2 ^ m)
      have hAm_sa : Amᴴ = Am := by
        dsimp [Am, P_i]
        rw [conjTranspose_sum]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        have hsa : ((B i)ᴴ * B i)ᴴ = (B i)ᴴ * B i := by
          rw [conjTranspose_mul, conjTranspose_conjTranspose]
        have hpow_sa : ∀ n : ℕ, (((B i)ᴴ * B i) ^ n)ᴴ = ((B i)ᴴ * B i) ^ n := by
          intro n; induction n with
          | zero => simp
          | succ n ihn =>
            rw [pow_succ', conjTranspose_mul, ihn, hsa]
            exact (pow_succ _ n).symm.trans (pow_succ' _ n)
        exact hpow_sa (2 ^ m)
      have hAm_sq : Amᴴ * Am = ∑ i ∈ S, P_i i ^ (2 ^ (m + 1)) := by
        rw [hAm_sa]
        dsimp [Am]
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun i hi ↦ ?_
        rw [Matrix.mul_sum, Finset.sum_eq_single i
          (fun j hj hij ↦ by
            have hk : 2 ^ m = (2 ^ m - 1) + 1 := by
              have hp := Nat.two_pow_pos m; omega
            rw [hk]
            exact hCrossPow hi hj hij.symm _ _)
          (fun hni ↦ absurd hi hni), ← pow_add, show 2 ^ m + 2 ^ m = 2 ^ (m + 1) by ring_nf]
      calc ‖M‖ ^ (2 ^ (m + 2))
          = (‖M‖ ^ (2 ^ (m + 1))) * (‖M‖ ^ (2 ^ (m + 1))) := by
              rw [← pow_add, show 2 ^ (m + 1) + 2 ^ (m + 1) = 2 ^ (m + 2) by ring_nf]
        _ = ‖Am‖ * ‖Am‖ := by rw [ih]
        _ = ‖Amᴴ * Am‖ := (Matrix.l2_opNorm_conjTranspose_mul_self Am).symm
        _ = ‖∑ i ∈ S, P_i i ^ (2 ^ (m + 1))‖ := by rw [hAm_sq]
  have hPowBound : ∀ m : ℕ, ‖M‖ ^ (2 ^ (m + 1)) ≤ (S.card : ℝ) * ε ^ (2 ^ (m + 1)) := by
    intro m
    rw [hDouble m]
    calc ‖∑ i ∈ S, P_i i ^ (2 ^ m)‖
        ≤ ∑ i ∈ S, ‖P_i i ^ (2 ^ m)‖ := norm_sum_le _ _
      _ ≤ ∑ _i ∈ S, ε ^ (2 ^ (m + 1)) := by
          refine Finset.sum_le_sum fun i hi ↦ ?_
          have hPi : ‖P_i i‖ ≤ ε ^ 2 := by
            dsimp [P_i]
            rw [Matrix.l2_opNorm_conjTranspose_mul_self, sq]
            exact mul_le_mul (hBound i hi) (hBound i hi) (norm_nonneg _) hε
          calc ‖P_i i ^ (2 ^ m)‖
              ≤ ‖P_i i‖ ^ (2 ^ m) := norm_pow_le _ _
            _ ≤ (ε ^ 2) ^ (2 ^ m) := pow_le_pow_left₀ (norm_nonneg _) hPi _
            _ = ε ^ (2 ^ (m + 1)) := by rw [← pow_mul, show 2 * 2 ^ m = 2 ^ (m + 1) by ring_nf]
      _ = (S.card : ℝ) * ε ^ (2 ^ (m + 1)) := by simp
  by_contra hgt
  have hlt : ε < ‖M‖ := lt_of_not_ge hgt
  rcases eq_or_lt_of_le hε with rfl | hε_pos
  · have h0 := hPowBound 0
    have h0' : ‖M‖ ^ 2 ≤ 0 := by simpa using h0
    nlinarith [norm_nonneg M]
  · let δ : ℝ := (‖M‖ - ε) / ε
    have hδ_pos : 0 < δ := div_pos (sub_pos.mpr hlt) hε_pos
    have hM_eq : ‖M‖ = ε * (1 + δ) := by
      dsimp [δ]; field_simp [ne_of_gt hε_pos]; ring
    obtain ⟨m, hm⟩ := exists_nat_gt ((S.card : ℝ) / δ)
    have hnat : ∀ q : ℕ, q < 2 ^ (q + 1) := fun q ↦ by
      induction q with
      | zero => decide
      | succ k ih =>
        calc k + 1 < 2 ^ (k + 1) + 1 := Nat.add_lt_add_right ih 1
          _ ≤ 2 ^ (k + 1) + 2 ^ (k + 1) := Nat.add_le_add_left Nat.one_le_two_pow _
          _ = 2 ^ (k + 2) := by ring_nf
    have hpow_gt : (m : ℝ) < (2 ^ (m + 1) : ℕ) := by exact_mod_cast hnat m
    have hbern : 1 + ((2 ^ (m + 1) : ℕ) : ℝ) * δ ≤ (1 + δ) ^ (2 ^ (m + 1)) :=
      one_add_mul_le_pow (by linarith) (2 ^ (m + 1))
    have hcap : (1 + δ) ^ (2 ^ (m + 1)) ≤ (S.card : ℝ) := by
      have hb := hPowBound m
      rw [hM_eq, mul_pow] at hb
      have hpos_pow : 0 < ε ^ (2 ^ (m + 1)) := pow_pos hε_pos _
      nlinarith
    have hmul_gt : (S.card : ℝ) < ((2 ^ (m + 1) : ℕ) : ℝ) * δ := by
      have hm' : (S.card : ℝ) < (m : ℝ) * δ := (div_lt_iff₀ hδ_pos).mp hm
      nlinarith
    linarith
noncomputable def vepGen {m N : ℕ} (r : QRegister m N) (gEq : Fin (2 ^ m) ≃ NyqGrid3D256)
    (uFam : (Fin 3 → Fin 2) → Unitary (2 ^ m)) (H : Configuration → Operator (2 ^ N)) :
    Operator (2 ^ N) := ((1 : ℝ) / (108 * 8) : ℂ) • ∑ bP : Fin 3 → Fin 2,
    (r.embedUnitary (uFam bP)).1ᴴ * (∑ yIdx : Fin (2 ^ m), projBasisGen r yIdx * H
    (cfgProjZ512 (nyq512ProjEquiv3D (gEq yIdx, bP)))) * (r.embedUnitary (uFam bP)).1
noncomputable def spliceProjGen {m N : ℕ} (r : QRegister m N) (x' x : Fin (2 ^ N)) : Fin
    (2 ^ N) := r.basisSplitEquiv.symm (r.extractIndex x, (r.basisSplitEquiv x').2)
theorem spliceProjGen_extract_and_env {m N : ℕ} (r : QRegister m N) (x' x : Fin (2 ^ N)) :
    r.extractIndex (spliceProjGen r x' x) = r.extractIndex x ∧
      (r.basisSplitEquiv (spliceProjGen r x' x)).2 = (r.basisSplitEquiv x').2 :=
  ⟨by rw [← QRegister.basisSplitEquiv_apply_fst]; simp [spliceProjGen], by simp [spliceProjGen]⟩
theorem idle_off_proj_zero_gen {m N : ℕ} (r : QRegister m N) {A : Operator (2 ^ N)} (hIdle : ∀
    M : Operator (2 ^ m), A * r.embedMatrix M = r.embedMatrix M * A) {k x : Fin (2 ^ N)}
    (hne : r.extractIndex k ≠ r.extractIndex x) : A k x = 0 := by
  have hc := congrFun (congrFun (hIdle (matUnit24 (r.extractIndex x) (r.extractIndex x))) k) x
  change (A * projBasisGen r (r.extractIndex x)) k x =
    (projBasisGen r (r.extractIndex x) * A) k x at hc
  rw [Matrix.mul_apply, Finset.sum_eq_single x (fun m _ hm ↦
    by simp [projBasisGen_apply, hm]) (by simp),
    Matrix.mul_apply, Finset.sum_eq_single k (fun m _ hm ↦
      by simp [projBasisGen_apply, hm.symm]) (by simp)] at hc
  simpa [projBasisGen_apply, hne] using hc
theorem conj_embedUnitary_projBasisGen_apply_of_idle {m N : ℕ} (r : QRegister m N)
    (U : Unitary (2 ^ m)) (yIdx : Fin (2 ^ m)) {A : Operator (2 ^ N)} (hIdle : ∀ M : Operator
    (2 ^ m), A * r.embedMatrix M = r.embedMatrix M * A) (x' x : Fin (2 ^ N)) :
    ((r.embedUnitary U).1ᴴ * (projBasisGen r yIdx * A) * (r.embedUnitary U).1) x' x =
    (star (U.1 yIdx (r.extractIndex x')) * U.1 yIdx (r.extractIndex x)) * A
    (spliceProjGen r x' x) x := by
  let M24 : Operator (2 ^ m) := U.1ᴴ * matUnit24 yIdx yIdx * U.1
  have hrearrange : (r.embedUnitary U).1ᴴ * (projBasisGen r yIdx * A) * (r.embedUnitary U).1 =
      r.embedMatrix M24 * A := by
    calc (r.embedUnitary U).1ᴴ * (projBasisGen r yIdx * A) * (r.embedUnitary U).1
        = (r.embedMatrix U.1)ᴴ * projBasisGen r yIdx * (A * r.embedMatrix U.1) := by
            simp only [QRegister.embedUnitary_val, Matrix.mul_assoc]
      _ = ((r.embedMatrix U.1)ᴴ * projBasisGen r yIdx * r.embedMatrix U.1) * A := by
            rw [hIdle]; simp only [Matrix.mul_assoc]
      _ = r.embedMatrix M24 * A := by
            unfold M24 projBasisGen
            rw [← r.embedMatrix_conjTranspose, ← r.embedMatrix_mul, ← r.embedMatrix_mul]
  rw [hrearrange, Matrix.mul_apply, Finset.sum_eq_single (spliceProjGen r x' x)]
  · obtain ⟨hex, henv⟩ := spliceProjGen_extract_and_env r x' x
    rw [QRegister.embedMatrix_apply]
    simp only [henv.symm, ↓reduceIte, mul_one, hex]
    congr 1
    dsimp [M24]
    rw [Matrix.mul_apply, Finset.sum_eq_single yIdx
      (fun m _ hm ↦ by
        rw [Matrix.mul_apply, Finset.sum_eq_single yIdx
          (fun l _ hl ↦ by simp [matUnit24, hl]) (by simp)]
        simp [matUnit24, hm]) (by simp),
      Matrix.mul_apply, Finset.sum_eq_single yIdx
        (fun l _ hl ↦ by simp [matUnit24, hl]) (by simp)]
    simp [matUnit24]
  · intro k _ hk
    by_cases henv : (r.basisSplitEquiv x').2 = (r.basisSplitEquiv k).2
    · by_cases hex : r.extractIndex k = r.extractIndex x
      · exact absurd (r.basisSplitEquiv.injective (Prod.ext
          (by rw [QRegister.basisSplitEquiv_apply_fst, QRegister.basisSplitEquiv_apply_fst,
                hex, (spliceProjGen_extract_and_env r x' x).1])
          (henv.symm.trans (spliceProjGen_extract_and_env r x' x).2.symm))) hk
      · rw [idle_off_proj_zero_gen r hIdle hex, mul_zero]
    · rw [QRegister.embedMatrix_apply]
      simp [henv]
  · simp
theorem vepGen_apply_of_idle {m N : ℕ} (r : QRegister m N) (gEq : Fin (2 ^ m) ≃ NyqGrid3D256)
    (uFam : (Fin 3 → Fin 2) → Unitary (2 ^ m)) {H : Configuration → Operator (2 ^ N)} (hIdle :
    ∀ (zP : NyqFine3D512) (M : Operator (2 ^ m)), H (cfgProjZ512 zP) * r.embedMatrix M =
    r.embedMatrix M * H (cfgProjZ512 zP)) (x' x : Fin (2 ^ N)) : vepGen r gEq uFam H x' x =
    ((1 : ℝ) / (108 * 8) : ℂ) * ∑ bP : Fin 3 → Fin 2, ∑ yIdx : Fin (2 ^ m), (star ((uFam bP).1
    yIdx (r.extractIndex x')) * (uFam bP).1 yIdx (r.extractIndex x)) * H
    (cfgProjZ512 (nyq512ProjEquiv3D (gEq yIdx, bP))) (spliceProjGen r x' x) x := by
  unfold vepGen
  rw [Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul]
  congr 1
  refine Finset.sum_congr rfl fun bP _ ↦ ?_
  rw [Matrix.mul_sum, Finset.sum_mul, Matrix.sum_apply]
  refine Finset.sum_congr rfl fun yIdx _ ↦ ?_
  exact conj_embedUnitary_projBasisGen_apply_of_idle r (uFam bP) yIdx (hIdle _) x' x
theorem vepGen_sub {m N : ℕ} (r : QRegister m N) (gEq : Fin (2 ^ m) ≃ NyqGrid3D256)
    (uFam : (Fin 3 → Fin 2) → Unitary (2 ^ m)) (F G : Configuration → Operator (2 ^ N)) :
    vepGen r gEq uFam (fun c ↦ F c - G c) = vepGen r gEq uFam F - vepGen r gEq uFam G := by
  unfold vepGen
  rw [← smul_sub, ← Finset.sum_sub_distrib]
  congr 1; refine Finset.sum_congr rfl fun bP _ ↦ ?_
  simp_rw [mul_sub, Finset.sum_sub_distrib]
  rw [Matrix.mul_sub, sub_mul]
theorem vepGen_const_smul_one {m N : ℕ} (r : QRegister m N) (gEq : Fin (2 ^ m) ≃ NyqGrid3D256)
    (uFam : (Fin 3 → Fin 2) → Unitary (2 ^ m)) (E₂ : ℝ) :
    vepGen r gEq uFam (fun _ ↦ (E₂ : ℂ) • (1 : Operator (2 ^ N))) =
      ((E₂ / 108 : ℝ) : ℂ) • (1 : Operator (2 ^ N)) := by
  unfold vepGen
  have hinner : ∀ bP : Fin 3 → Fin 2,
      (r.embedUnitary (uFam bP)).1ᴴ *
        (∑ yIdx : Fin (2 ^ m), projBasisGen r yIdx * ((E₂ : ℂ) • (1 : Operator (2 ^ N)))) *
        (r.embedUnitary (uFam bP)).1 =
      (E₂ : ℂ) • (1 : Operator (2 ^ N)) := fun bP ↦ by
    have hsum : (∑ yIdx : Fin (2 ^ m), projBasisGen r yIdx * ((E₂ : ℂ) • (1 : Operator (2 ^
        N)))) = (E₂ : ℂ) • (1 : Operator (2 ^ N)) := by
      simp_rw [Matrix.mul_smul, Matrix.mul_one, ← Finset.smul_sum, sum_projBasisGen]
    have hUinv : (r.embedUnitary (uFam bP)).1ᴴ * (r.embedUnitary (uFam bP)).1 = 1 := by
      simpa only [Matrix.star_eq_conjTranspose] using
        Unitary.coe_star_mul_self (r.embedUnitary (uFam bP))
    rw [hsum, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hUinv]
  simp_rw [hinner]
  rw[Finset.sum_const, Finset.card_univ, Fintype.card_pi, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, smul_smul]
  congr 1; push_cast; field_simp
open TwosCompAndWire0Cancel (fwdPermUnitary) in
theorem conj_vepGen_elec {m N : ℕ} (r : QRegister m N) (gEq : Fin (2 ^ m) ≃ NyqGrid3D256)
    (pSub : Equiv.Perm (Fin (2 ^ m))) (uTw uSM : (Fin 3 → Fin 2) → Unitary (2 ^ m))
    (hSM_def : ∀ bP, uSM bP = uTw bP * fwdPermUnitary pSub) (U_sys U_e : Operator (2 ^ N))
    (hU_sys : U_sys = (r.embedUnitary (fwdPermUnitary pSub)).1 * U_e) (hUe_sa : U_eᴴ = U_e)
    (hComm : ∀ M : Operator (2 ^ m), U_e * r.embedMatrix M = r.embedMatrix M * U_e)
    (H_twos2 : Configuration → Operator (2 ^ N)) : U_sysᴴ * vepGen r gEq uTw H_twos2 * U_sys =
    vepGen r gEq uSM (fun c ↦ U_eᴴ * H_twos2 c * U_e) := by
  let P_sm := (r.embedUnitary (fwdPermUnitary pSub)).1
  have hSM : ∀ bP : Fin 3 → Fin 2,
      (r.embedUnitary (uTw bP)).1 * P_sm =
        (r.embedUnitary (uSM bP)).1 := fun bP ↦ by
    dsimp [P_sm]
    rw [hSM_def bP]; exact (r.embedMatrix_mul _ _).symm
  unfold vepGen
  rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sum, Finset.sum_mul]
  congr 1
  refine Finset.sum_congr rfl fun bP _ ↦ ?_
  let U_tw := (r.embedUnitary (uTw bP)).1
  let U_sm := (r.embedUnitary (uSM bP)).1
  have hR : U_tw * U_sys = U_e * U_sm := by
    calc U_tw * U_sys
        = (U_tw * P_sm) * U_e := by rw [hU_sys, Matrix.mul_assoc]
      _ = U_sm * U_e := by rw [hSM bP]
      _ = U_e * U_sm := (hComm _).symm
  have hL : U_sysᴴ * U_twᴴ = U_smᴴ * U_eᴴ := by
    simpa only [conjTranspose_mul] using congrArg Matrix.conjTranspose hR
  calc U_sysᴴ *
          (U_twᴴ * (∑ yIdx : Fin (2 ^ m), projBasisGen r yIdx *
            H_twos2 (cfgProjZ512 (nyq512ProjEquiv3D (gEq yIdx, bP)))) * U_tw) *
          U_sys
      = (U_sysᴴ * U_twᴴ) *
          (∑ yIdx : Fin (2 ^ m), projBasisGen r yIdx *
            H_twos2 (cfgProjZ512 (nyq512ProjEquiv3D (gEq yIdx, bP)))) *
          (U_tw * U_sys) := by simp only [Matrix.mul_assoc]
    _ = U_smᴴ * (U_eᴴ *
          (∑ yIdx : Fin (2 ^ m), projBasisGen r yIdx *
            H_twos2 (cfgProjZ512 (nyq512ProjEquiv3D (gEq yIdx, bP)))) * U_e) * U_sm := by
          rw [hL, hR]; simp only [Matrix.mul_assoc]
    _ = U_smᴴ * (∑ yIdx : Fin (2 ^ m),
          projBasisGen r yIdx *
            (U_eᴴ * H_twos2 (cfgProjZ512 (nyq512ProjEquiv3D (gEq yIdx, bP))) * U_e)) *
          U_sm := by
          congr 2
          rw [Matrix.mul_sum, Finset.sum_mul]
          refine Finset.sum_congr rfl fun yIdx _ ↦ ?_
          have hc : U_eᴴ * projBasisGen r yIdx = projBasisGen r yIdx * U_eᴴ := by
            rw [hUe_sa]; exact hComm _
          calc U_eᴴ * (projBasisGen r yIdx *
                  H_twos2 (cfgProjZ512 (nyq512ProjEquiv3D (gEq yIdx, bP)))) * U_e
              = (U_eᴴ * projBasisGen r yIdx) *
                  H_twos2 (cfgProjZ512 (nyq512ProjEquiv3D (gEq yIdx, bP))) * U_e := by
                  simp only [Matrix.mul_assoc]
            _ = projBasisGen r yIdx *
                  (U_eᴴ * H_twos2 (cfgProjZ512 (nyq512ProjEquiv3D (gEq yIdx, bP))) * U_e) := by
                  rw [hc]; simp only [Matrix.mul_assoc]
theorem vepGen_congr {m N : ℕ} (r : QRegister m N) (gEq : Fin (2 ^ m) ≃ NyqGrid3D256)
    (uFam : (Fin 3 → Fin 2) → Unitary (2 ^ m)) {F G : Configuration → Operator (2 ^ N)}
    (h : ∀ zP : NyqFine3D512, F (cfgProjZ512 zP) = G (cfgProjZ512 zP)) : vepGen r gEq uFam F =
    vepGen r gEq uFam G := by
  unfold vepGen
  refine congrArg _ (Finset.sum_congr rfl fun bP _ ↦ ?_)
  refine congrArg (fun M ↦ (r.embedUnitary (uFam bP)).1ᴴ * M * (r.embedUnitary (uFam bP)).1) ?_
  exact Finset.sum_congr rfl fun yIdx _ ↦ congrArg (projBasisGen r yIdx * ·) (h _)
open TwosCompAndWire0Cancel (fwdPermUnitary) in
theorem conj_vepGen_idle {m N : ℕ} (r : QRegister m N) (gEq : Fin (2 ^ m) ≃ NyqGrid3D256)
    (pSub : Equiv.Perm (Fin (2 ^ m))) (uTw uSM : (Fin 3 → Fin 2) → Unitary (2 ^ m))
    (hSM_def : ∀ bP, uSM bP = uTw bP * fwdPermUnitary pSub) (U_sys U_e : Operator (2 ^ N))
    (hU_sys : U_sys = (r.embedUnitary (fwdPermUnitary pSub)).1 * U_e) (hUe_sa : U_eᴴ = U_e)
    (hComm : ∀ M : Operator (2 ^ m), U_e * r.embedMatrix M = r.embedMatrix M * U_e)
    (H_twos2 : Configuration → Operator (2 ^ N)) (hIdleTwos : ∀ (zP : NyqFine3D512) (M :
    Operator (2 ^ m)), H_twos2 (cfgProjZ512 zP) * r.embedMatrix M = r.embedMatrix M * H_twos2
    (cfgProjZ512 zP)) : U_sysᴴ * vepGen r gEq uTw H_twos2 * U_sys = vepGen r gEq uSM
    (fun c ↦ U_sysᴴ * H_twos2 c * U_sys) := by
  rw [conj_vepGen_elec r gEq pSub uTw uSM hSM_def U_sys U_e hU_sys hUe_sa hComm]
  refine vepGen_congr r gEq uSM fun zP ↦ ?_
  let P_sm := (r.embedUnitary (fwdPermUnitary pSub)).1
  have hP_inv : P_smᴴ * P_sm = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using
      Unitary.coe_star_mul_self (r.embedUnitary (fwdPermUnitary pSub))
  have hcommP : P_sm * H_twos2 (cfgProjZ512 zP) = H_twos2 (cfgProjZ512 zP) * P_sm :=
    (hIdleTwos zP _).symm
  calc U_eᴴ * H_twos2 (cfgProjZ512 zP) * U_e
      = U_eᴴ * ((P_smᴴ * P_sm) * H_twos2 (cfgProjZ512 zP)) * U_e := by rw [hP_inv, Matrix.one_mul]
    _ = U_eᴴ * (P_smᴴ * (H_twos2 (cfgProjZ512 zP) * P_sm)) * U_e := by
          rw [Matrix.mul_assoc P_smᴴ P_sm, hcommP]
    _ = U_sysᴴ * H_twos2 (cfgProjZ512 zP) * U_sys := by
          dsimp only [P_sm]
          rw [hU_sys, conjTranspose_mul]; simp only [Matrix.mul_assoc]
theorem vepGen_projError_le {m N : ℕ} (r : QRegister m N) (gEq : Fin (2 ^ m) ≃ NyqGrid3D256)
    (uSM : (Fin 3 → Fin 2) → Unitary (2 ^ m)) (P G : Operator (2 ^ N)) (hP_sa : Pᴴ = P)
    (hP_norm : ‖P‖ ≤ 1) (hcomm0 : projBasisGen r 0 * P = P * projBasisGen r 0)
    (hPe_abs : projLift0Gen r P * P = P ∧ P * projLift0Gen r P = P)
    (hPG : P * G = P ∧ G * P = P) (E₂ E₅ : ℝ) {eps2 : ℝ} (heps2 : 0 ≤ eps2)
    (hE5 : E₅ = E₂ / 108) (S_op B_raw2 S_shift2 : Configuration → Operator (2 ^ N))
    (S_shift5 : Operator (2 ^ N)) (hS_idle : ∀ (zP : NyqFine3D512) (M : Operator (2 ^ m)),
    S_op (cfgProjZ512 zP) * r.embedMatrix M = r.embedMatrix M * S_op (cfgProjZ512 zP)) (hIdle2
    : ∀ (zP : NyqFine3D512) (M : Operator (2 ^ m)), B_raw2 (cfgProjZ512 zP) * r.embedMatrix M
    = r.embedMatrix M * B_raw2 (cfgProjZ512 zP)) (hVep_ideal : G * vepGen r gEq uSM S_op * G -
    (E₅ : ℂ) • G = S_shift5) (hS2_ideal : ∀ zP : NyqFine3D512, G * S_op (cfgProjZ512 zP) * G -
    (E₂ : ℂ) • G = S_shift2 (cfgProjZ512 zP)) (hErr2 : ∀ zP : NyqFine3D512, ‖P * (B_raw2
    (cfgProjZ512 zP) - S_shift2 (cfgProjZ512 zP)) * P‖ ≤ eps2) : ‖P *
    (vepGen r gEq uSM B_raw2 - S_shift5) * P‖ ≤ (1 / 108 : ℝ) * eps2 := by
  let Pe := projLift0Gen r P
  let S_idle : Configuration → Operator (2 ^ N) :=
    fun c ↦ S_op c - (E₂ : ℂ) • (1 : Operator (2 ^ N))
  let Δ : Configuration → Operator (2 ^ N) := fun c ↦ B_raw2 c - S_idle c
  have hideal : P * vepGen r gEq uSM S_idle * P = P * S_shift5 * P := by
    change P * vepGen r gEq uSM (fun c ↦ S_op c - (E₂ : ℂ) • (1 : Operator (2 ^ N))) * P = _
    rw [vepGen_sub r gEq uSM S_op (fun _ ↦ (E₂ : ℂ) • (1 : Operator (2 ^ N))),
      vepGen_const_smul_one r gEq uSM E₂, mul_sub, sub_mul, ← hVep_ideal, mul_sub, sub_mul]
    refine congrArg₂ HSub.hSub ?_ ?_
    · calc P * vepGen r gEq uSM S_op * P
          = (P * G) * vepGen r gEq uSM S_op * (G * P) := by rw [hPG.1, hPG.2]
        _ = P * (G * vepGen r gEq uSM S_op * G) * P := by simp only [Matrix.mul_assoc]
    · rw [hE5, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul,
        Matrix.mul_one, hPG.1]
  have hΔ_eq : ∀ zP : NyqFine3D512,
      P * Δ (cfgProjZ512 zP) * P =
        P * (B_raw2 (cfgProjZ512 zP) - S_shift2 (cfgProjZ512 zP)) * P := fun zP ↦ by
    have hS2 : P * S_idle (cfgProjZ512 zP) * P = P * S_shift2 (cfgProjZ512 zP) * P := by
      change P * (S_op (cfgProjZ512 zP) - (E₂ : ℂ) • (1 : Operator (2 ^ N))) * P = _
      rw [← hS2_ideal zP, mul_sub, sub_mul, mul_sub, sub_mul]
      refine congrArg₂ HSub.hSub ?_ ?_
      · calc P * S_op (cfgProjZ512 zP) * P
            = (P * G) * S_op (cfgProjZ512 zP) * (G * P) := by rw [hPG.1, hPG.2]
          _ = P * (G * S_op (cfgProjZ512 zP) * G) * P := by simp only [Matrix.mul_assoc]
      · rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul,
          Matrix.mul_one, hPG.1]
    change P * (B_raw2 (cfgProjZ512 zP) - S_idle (cfgProjZ512 zP)) * P = _
    rw [mul_sub, sub_mul, hS2, ← sub_mul, ← mul_sub]
  have hΔ_idle : ∀ (zP : NyqFine3D512) (M : Operator (2 ^ m)),
      Δ (cfgProjZ512 zP) * r.embedMatrix M = r.embedMatrix M * Δ (cfgProjZ512 zP) := fun zP M ↦ by
    change (B_raw2 (cfgProjZ512 zP) - (S_op (cfgProjZ512 zP) - (E₂ : ℂ) • 1)) * r.embedMatrix M =
      r.embedMatrix M * (B_raw2 (cfgProjZ512 zP) - (S_op (cfgProjZ512 zP) - (E₂ : ℂ) • 1))
    rw [sub_mul, mul_sub, hIdle2 zP M, sub_mul, mul_sub,
      hS_idle zP M, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]
  have hmain_eq : P * (vepGen r gEq uSM B_raw2 - S_shift5) * P =
      P * vepGen r gEq uSM Δ * P := by
    have hlin : vepGen r gEq uSM B_raw2 - vepGen r gEq uSM S_idle =
        vepGen r gEq uSM Δ := (vepGen_sub r gEq uSM B_raw2 S_idle).symm
    rw [mul_sub, sub_mul, ← hideal, ← sub_mul, ← mul_sub, hlin]
  rw [hmain_eq]
  have hper_b : ∀ bP : Fin 3 → Fin 2,
      ‖Pe * ((r.embedUnitary (uSM bP)).1ᴴ *
        (∑ yIdx : Fin (2 ^ m),
          projBasisGen r yIdx * Δ (cfgProjZ512 (nyq512ProjEquiv3D (gEq yIdx, bP)))) *
        (r.embedUnitary (uSM bP)).1) * Pe‖ ≤ eps2 := fun bP ↦ by
    let U := (r.embedUnitary (uSM bP)).1
    have hPeU : Pe * U = U * Pe := projLift0Gen_comm_embedMatrix r P _
    have hPeUh : Pe * Uᴴ = Uᴴ * Pe := by
      dsimp only [U]
      rw [QRegister.embedUnitary_val, ← r.embedMatrix_conjTranspose]
      exact projLift0Gen_comm_embedMatrix r P _
    have hterm_eq : ∀ yIdx : Fin (2 ^ m),
        Pe * (projBasisGen r yIdx * Δ (cfgProjZ512 (nyq512ProjEquiv3D (gEq yIdx, bP)))) * Pe =
          (projShift0Gen r yIdx)ᴴ *
            (projBasisGen r 0 * (P * Δ (cfgProjZ512 (nyq512ProjEquiv3D (gEq yIdx, bP))) * P) *
              projBasisGen r 0) * projShift0Gen r yIdx := fun yIdx ↦ by
      let D := Δ (cfgProjZ512 (nyq512ProjEquiv3D (gEq yIdx, bP)))
      have hd : projBasisGen r yIdx * D =
          (projShift0Gen r yIdx)ᴴ * projBasisGen r 0 * D * projBasisGen r 0 *
            projShift0Gen r yIdx :=
        projBasisGen_mul_of_idle r (hΔ_idle _) yIdx
      calc Pe * (projBasisGen r yIdx * D) * Pe
          = (Pe * (projShift0Gen r yIdx)ᴴ) * projBasisGen r 0 * D * projBasisGen r 0 *
              (projShift0Gen r yIdx * Pe) := by rw [hd]; simp only [Matrix.mul_assoc]
        _ = (projShift0Gen r yIdx)ᴴ * (P * projBasisGen r 0) * D * (projBasisGen r 0 * P) *
              projShift0Gen r yIdx := by
              rw [projLift0Gen_mul_projShift0Gen_conjTranspose_of_comm r hP_sa hcomm0,
                projShift0Gen_mul_projLift0Gen_of_comm r hcomm0]; simp only [Matrix.mul_assoc]
        _ = (projShift0Gen r yIdx)ᴴ * (projBasisGen r 0 * (P * D * P) * projBasisGen r 0) *
              projShift0Gen r yIdx := by
              rw [← hcomm0]; nth_rw 2 [hcomm0]; simp only [Matrix.mul_assoc]
    let Ssum : Operator (2 ^ N) := ∑ yIdx : Fin (2 ^ m),
      projBasisGen r yIdx * Δ (cfgProjZ512 (nyq512ProjEquiv3D (gEq yIdx, bP)))
    have hmove : Pe * (Uᴴ * Ssum * U) * Pe = Uᴴ * (∑ yIdx : Fin (2 ^ m), Pe * (projBasisGen r
        yIdx * Δ (cfgProjZ512 (nyq512ProjEquiv3D (gEq yIdx, bP)))) * Pe) * U := by
      calc Pe * (Uᴴ * Ssum * U) * Pe
          = (Pe * Uᴴ) * Ssum * (U * Pe) := by simp only [Matrix.mul_assoc]
        _ = Uᴴ * (Pe * Ssum * Pe) * U := by rw [hPeUh, ← hPeU]; simp only [Matrix.mul_assoc]
        _ = Uᴴ * (∑ yIdx : Fin (2 ^ m),
              Pe * (projBasisGen r yIdx * Δ (cfgProjZ512 (nyq512ProjEquiv3D (gEq yIdx,
                bP)))) * Pe) * U := by
              dsimp only [Ssum]; rw [Matrix.mul_sum, Finset.sum_mul]
    rw [hmove]
    simp_rw [hterm_eq]
    have hU_norm : ‖U‖ ≤ 1 := by
      have hUinv : Uᴴ * U = 1 := by
        simpa only [Matrix.star_eq_conjTranspose] using
          Unitary.coe_star_mul_self (r.embedUnitary (uSM bP))
      have hsq : ‖U‖ * ‖U‖ ≤ 1 := by
        rw [← Matrix.l2_opNorm_conjTranspose_mul_self U, hUinv]
        exact norm_projector_le_one 1 Matrix.isHermitian_one (Matrix.mul_one 1)
      nlinarith [norm_nonneg U]
    have hP0_norm : ‖projBasisGen r 0‖ ≤ 1 :=
      norm_projector_le_one _ (projBasisGen_isHermitian r 0) (projBasisGen_idem r 0)
    let Mid : Fin (2 ^ m) → Operator (2 ^ N) := fun yIdx ↦
      projBasisGen r 0 * (P * Δ (cfgProjZ512 (nyq512ProjEquiv3D (gEq yIdx,
        bP))) * P) * projBasisGen r 0
    let BTerm : Fin (2 ^ m) → Operator (2 ^ N) := fun yIdx ↦
      (projShift0Gen r yIdx)ᴴ * Mid yIdx * projShift0Gen r yIdx
    have hSumNorm : ‖∑ yIdx : Fin (2 ^ m), BTerm yIdx‖ ≤ eps2 := by
      refine norm_sum_biOrthogonal_le Finset.univ BTerm heps2 (fun i _ j _ hij ↦ ?_)
        (fun i _ j _ hij ↦ ?_) (fun i _ ↦ ?_)
      · calc BTerm i * (BTerm j)ᴴ
            = (projShift0Gen r i)ᴴ * Mid i * (projShift0Gen r i * (projShift0Gen r j)ᴴ) *
                (Mid j)ᴴ * projShift0Gen r j := by
                dsimp only [BTerm]
                rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose]
                simp only [Matrix.mul_assoc]
          _ = 0 := by rw [projShift0Gen_mul_conjTranspose]; simp [hij]
      · calc (BTerm i)ᴴ * BTerm j
            = (projShift0Gen r i)ᴴ * (Mid i)ᴴ * (projShift0Gen r i * (projShift0Gen r j)ᴴ) *
                Mid j * projShift0Gen r j := by
                dsimp only [BTerm]
                rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose]
                simp only [Matrix.mul_assoc]
          _ = 0 := by rw [projShift0Gen_mul_conjTranspose]; simp [hij]
      · dsimp only [BTerm, Mid]
        have hT1 : ‖projShift0Gen r i‖ ≤ 1 := norm_projShift0Gen_le_one r i
        have hT2 : ‖(projShift0Gen r i)ᴴ‖ ≤ 1 := by
          simpa only [Matrix.l2_opNorm_conjTranspose] using hT1
        have hMid : ‖projBasisGen r 0 * (P * Δ (cfgProjZ512 (nyq512ProjEquiv3D (gEq i, bP))) * P) *
            projBasisGen r 0‖ ≤ eps2 := by
          calc ‖projBasisGen r 0 * (P * Δ (cfgProjZ512 (nyq512ProjEquiv3D (gEq i, bP))) * P) *
                  projBasisGen r 0‖
              ≤ ‖projBasisGen r 0‖ * ‖P * Δ (cfgProjZ512 (nyq512ProjEquiv3D (gEq i, bP))) * P‖ *
                  ‖projBasisGen r 0‖ :=
                le_trans (norm_mul_le _ _) (mul_le_mul_of_nonneg_right (norm_mul_le _ _)
                  (norm_nonneg _))
            _ ≤ 1 * eps2 * 1 := by
                rw [hΔ_eq]
                exact mul_le_mul (mul_le_mul hP0_norm (hErr2 _) (norm_nonneg _) zero_le_one)
                  hP0_norm (norm_nonneg _) (by linarith)
            _ = eps2 := by ring
        calc ‖(projShift0Gen r i)ᴴ * _ * projShift0Gen r i‖
            ≤ ‖(projShift0Gen r i)ᴴ‖ * ‖_‖ * ‖projShift0Gen r i‖ :=
              le_trans (norm_mul_le _ _) (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg
                _))
          _ ≤ 1 * eps2 * 1 :=
              mul_le_mul (mul_le_mul hT2 hMid (norm_nonneg _) zero_le_one) hT1 (norm_nonneg _) (by
                linarith)
          _ = eps2 := by ring
    have hUh_norm : ‖Uᴴ‖ ≤ 1 := by simpa only [Matrix.l2_opNorm_conjTranspose] using hU_norm
    calc ‖Uᴴ * (∑ yIdx : Fin (2 ^ m), BTerm yIdx) * U‖
        ≤ ‖Uᴴ‖ * ‖∑ yIdx : Fin (2 ^ m), BTerm yIdx‖ * ‖U‖ :=
          le_trans (norm_mul_le _ _) (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _ ≤ 1 * eps2 * 1 :=
          mul_le_mul (mul_le_mul hUh_norm hSumNorm (norm_nonneg _) zero_le_one) hU_norm (norm_nonneg
            _) (by linarith)
      _ = eps2 := by ring
  let RawTerm : (Fin 3 → Fin 2) → Operator (2 ^ N) := fun bP ↦ (r.embedUnitary (uSM bP)).1ᴴ *
      (∑ yIdx : Fin (2 ^ m), projBasisGen r yIdx * Δ (cfgProjZ512 (nyq512ProjEquiv3D (gEq
      yIdx, bP)))) * (r.embedUnitary (uSM bP)).1
  have hPe_wrap : P * vepGen r gEq uSM Δ * P =
      P * (((1 : ℝ) / (108 * 8) : ℂ) • ∑ bP : Fin 3 → Fin 2, Pe * RawTerm bP * Pe) * P := by
    change P * (((1 : ℝ) / (108 * 8) : ℂ) • ∑ bP : Fin 3 → Fin 2, RawTerm bP) * P = _
    rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul]
    refine congrArg (((1 : ℝ) / (108 * 8) : ℂ) • ·) ?_
    calc P * (∑ bP : Fin 3 → Fin 2, RawTerm bP) * P
        = (P * Pe) * (∑ bP : Fin 3 → Fin 2, RawTerm bP) * (Pe * P) := by rw [hPe_abs.2, hPe_abs.1]
      _ = P * (Pe * (∑ bP : Fin 3 → Fin 2, RawTerm bP) * Pe) * P := by simp only [Matrix.mul_assoc]
      _ = P * (∑ bP : Fin 3 → Fin 2, Pe * RawTerm bP * Pe) * P := by
        rw [Matrix.mul_sum, Finset.sum_mul]
  rw [hPe_wrap, Matrix.mul_smul, Matrix.smul_mul, norm_smul]
  have hscalar : ‖((1 : ℝ) / (108 * 8) : ℂ)‖ = (1 : ℝ) / (108 * 8) := by norm_num
  rw [hscalar]
  have hinner : ‖P * (∑ bP : Fin 3 → Fin 2, Pe * ((r.embedUnitary (uSM bP)).1ᴴ * (∑ yIdx : Fin
      (2 ^ m), projBasisGen r yIdx * Δ (cfgProjZ512 (nyq512ProjEquiv3D (gEq yIdx, bP)))) *
      (r.embedUnitary (uSM bP)).1) * Pe) * P‖ ≤ 8 * eps2 := by
    calc ‖P * (∑ bP, _) * P‖
        ≤ ‖P‖ * ‖∑ bP, _‖ * ‖P‖ :=
          le_trans (norm_mul_le _ _) (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _ ≤ 1 * (∑ _bP : Fin 3 → Fin 2, eps2) * 1 := by
          have hs : ‖∑ bP : Fin 3 → Fin 2, _‖ ≤ ∑ _bP : Fin 3 → Fin 2, eps2 :=
            (norm_sum_le _ _).trans (Finset.sum_le_sum fun bP _ ↦ hper_b bP)
          exact mul_le_mul (mul_le_mul hP_norm hs (norm_nonneg _) zero_le_one)
            hP_norm (norm_nonneg _) (by positivity)
      _ = 8 * eps2 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_pi, Finset.prod_const,
            Finset.card_univ, Fintype.card_fin, Fintype.card_fin]
          norm_num
  calc ((1 : ℝ) / (108 * 8)) * ‖P * (∑ bP, _) * P‖
      ≤ ((1 : ℝ) / (108 * 8)) * (8 * eps2) :=
        mul_le_mul_of_nonneg_left hinner (by positivity)
    _ = (1 / 108 : ℝ) * eps2 := by linarith
theorem projSector_guard_diff_eq {d : Type*} [Fintype d]
    (P G B T : Matrix d d ℂ) (hPG : P * G = P ∧ G * P = P) :
    P * (G * B * G - T) * P = P * (B - T) * P := by
  rw [mul_sub, sub_mul, mul_sub, sub_mul]
  congr 1
  calc P * (G * B * G) * P = (P * G) * B * (G * P) := by simp only [Matrix.mul_assoc]
    _ = P * B * P := by rw [hPG.1, hPG.2]
noncomputable abbrev vepFromSlot2TwosOp
    (H_twos2 : Configuration → Operator (2 ^ systemQubits)) : Operator (2 ^ systemQubits) :=
    vepGen rProj24_sp projGridEquiv24 uProjPlus512_3D H_twos2
noncomputable abbrev vepFromSlot2Op (H_branch2 : Configuration → Operator (2 ^ systemQubits))
    : Operator (2 ^ systemQubits) := vepGen rProj24_sp projGridEquiv24 uProjPlus512SM_3D
    H_branch2
open TwosCompAndWire0Cancel (fwdPermMatrix_conjTranspose fwdPermUnitary
  elec654Axes smToTwos654SysPerm smToTwos654SysUnitary smToTwosSysUnitary) in
theorem smToTwos654SysUnitary_sa : smToTwos654SysUnitary.1ᴴ = smToTwos654SysUnitary.1 := by
  have hinv : ∀ z, smToTwos654SysPerm (smToTwos654SysPerm z) = z :=
    TwosCompAndWire0Cancel.foldAxesPerm_self_of_involutive
      (TwosCompAndWire0Cancel.smToTwosAxisPerm_self 3) elec654Axes
      fun _ _ ↦ TwosCompAndWire0Cancel.elec654Axes_disjoint
  have hsymm : smToTwos654SysPerm.symm = smToTwos654SysPerm :=
    Equiv.ext fun z ↦ smToTwos654SysPerm.symm_apply_eq.mpr (hinv z).symm
  dsimp [smToTwos654SysUnitary, fwdPermUnitary]
  rw [fwdPermMatrix_conjTranspose, hsymm]
set_option allowUnsafeReducibility true in
attribute [local irreducible]
  TwosCompAndWire0Cancel.smToTwos654SysUnitary
  TwosCompAndWire0Cancel.smToTwosSysUnitary
set_option allowUnsafeReducibility true in
attribute [local irreducible]
  SpecsAux.BridgeFermionicComm.SpecInner.permElectron
set_option maxHeartbeats 400000 in
-- Elevated heartbeats needed for register-embedding conjugation elaboration.
open TwosCompAndWire0Cancel (smToTwos654SysUnitary smToTwosSysUnitary) in
theorem smToTwosSysUnitary_conj_vepFromSlot2TwosOp
    (H_twos2 : Configuration → Operator (2 ^ systemQubits)) (hIdleTwos : ∀ (zP : NyqFine3D512)
    (M : Operator (2 ^ 24)), H_twos2 (cfgProjZ512 zP) * rProj24_sp.embedMatrix M =
    rProj24_sp.embedMatrix M * H_twos2 (cfgProjZ512 zP)) : smToTwosSysUnitary.1ᴴ *
    vepFromSlot2TwosOp H_twos2 * smToTwosSysUnitary.1 = vepFromSlot2Op
    (fun c ↦ smToTwosSysUnitary.1ᴴ * H_twos2 c * smToTwosSysUnitary.1) := conj_vepGen_idle
    rProj24_sp projGridEquiv24 projSignedMagToTwos24Equiv uProjPlus512_3D uProjPlus512SM_3D
    (fun _ ↦ rfl) smToTwosSysUnitary.1 smToTwos654SysUnitary.1 ((congrArg Subtype.val
    smToTwosSysUnitary_eq_proj_mul_elec).trans (Submonoid.coe_mul (Matrix.unitaryGroup (Fin (2
    ^ systemQubits)) ℂ) _ _)) smToTwos654SysUnitary_sa smToTwos654SysUnitary_comm_embedMatrix
    H_twos2 hIdleTwos
noncomputable abbrev spliceProj (x' x : Fin (2 ^ systemQubits)) : Fin (2 ^ systemQubits) :=
  spliceProjGen rProj24_sp x' x
theorem vepFromSlot2Op_apply_of_idle {H_branch2 : Configuration → Operator (2 ^ systemQubits)}
    (hIdle : ∀ (zP : NyqFine3D512) (M : Operator (2 ^ 24)), H_branch2 (cfgProjZ512 zP) *
    rProj24_sp.embedMatrix M = rProj24_sp.embedMatrix M * H_branch2 (cfgProjZ512 zP))
    (x' x : Fin (2 ^ systemQubits)) : vepFromSlot2Op H_branch2 x' x =
    ((1 : ℝ) / (108 * 8) : ℂ) * ∑ bP : Fin 3 → Fin 2, ∑ yIdx : Fin (2 ^ 24), (star
    ((uProjPlus512SM_3D bP).1 yIdx (rProj24_sp.extractIndex x')) * (uProjPlus512SM_3D bP).1
    yIdx (rProj24_sp.extractIndex x)) * H_branch2
    (cfgProjZ512 (nyq512ProjEquiv3D (projGridEquiv24 yIdx, bP))) (spliceProj x' x) x :=
    vepGen_apply_of_idle rProj24_sp projGridEquiv24 uProjPlus512SM_3D hIdle x' x
set_option maxHeartbeats 400000 in
-- Elevated heartbeats needed for grid-permutation invariance elaboration.
open Slots01AndGridGuardBridge (elecAxisWord6) in
open SixSlotEndpointJunctionBridge (isGridState_iff_axisWords_ne_minInt) in
open SpecsAux.BridgeFermionicComm.SpecInner
    (signMagnitude_eq_of_momentum_eq_of_isGridState) in
theorem vepFromSlot2Op_inGridPerm {B_raw2 : Configuration → Operator (2 ^ systemQubits)}
    (hIdle2 : ∀ (zP : NyqFine3D512) (M : Operator (2 ^ 24)), B_raw2 (cfgProjZ512 zP) *
    rProj24_sp.embedMatrix M = rProj24_sp.embedMatrix M * B_raw2 (cfgProjZ512 zP)) (hPerm2 : ∀
    (zP : NyqFine3D512) (g : Equiv.Perm (Fin numElectrons)) (a b : Fin (2 ^ systemQubits)),
    IsGridState a → IsGridState b → B_raw2 (cfgProjZ512 zP) (permElectron g a) (permElectron g
    b) = B_raw2 (cfgProjZ512 zP) a b) : ∀ (g : Equiv.Perm (Fin numElectrons))
    (x' x : Fin (2 ^ systemQubits)), IsGridState x' → IsGridState x → vepFromSlot2Op B_raw2
    (permElectron g x') (permElectron g x) = vepFromSlot2Op B_raw2 x' x := by
  intro g x' x hx' hx
  have hex_perm : ∀ z : Fin (2 ^ systemQubits),
      rProj24_sp.extractIndex (permElectron g z) = rProj24_sp.extractIndex z := fun z ↦ by
    apply Fin.ext; apply Nat.eq_of_testBit_eq; intro j
    by_cases hj : j < 24
    · rw [extractIndex_rProj24_testBit _ j hj, extractIndex_rProj24_testBit _ j hj]
      have hpe :=
        SpecsAux.BridgeFermionicComm.SpecInner.testBit_permElectron
        g z ⟨3924 + j, by change 3924 + j < 3948; omega⟩
      have hfix : (SpecsAux.BridgeFermionicComm.SpecInner.permElectronWire
          g ⟨3924 + j, by change 3924 + j < 3948; omega⟩).val = 3924 + j := by
        change (SpecsAux.BridgeFermionicComm.SpecInner.permElectronWireFun
          g ⟨3924 + j, _⟩).val = 3924 + j
        unfold SpecsAux.BridgeFermionicComm.SpecInner.permElectronWireFun
        rw [dite_eq_of_neg (show ¬ (3924 + j < 3924) by omega)]
      simpa [hfix] using hpe
    · rw[testBit_extractIndex_rProj24_ge _ hj, testBit_extractIndex_rProj24_ge _ hj]
  have hsplice_grid : IsGridState (spliceProj x' x) := by
    rw [isGridState_iff_axisWords_ne_minInt]
    obtain ⟨hex, henv⟩ := spliceProjGen_extract_and_env rProj24_sp x' x
    have hbits := (env_eq_iff_electron_testBit_eq (spliceProj x' x) x').mp henv
    refine ⟨fun i w ↦ ?_, fun w ↦ ?_⟩
    · have hsm := signMagnitude_electron_eq_of_testBit_eq hbits i w
      have he := ((isGridState_iff_axisWords_ne_minInt x').mp hx').1 i w
      simpa [elecAxisWord6, hsm] using he
    · rw [← projGridEquiv24_extractIndex_eq_projAxisWord8, hex,
        projGridEquiv24_extractIndex_eq_projAxisWord8]
      exact ((isGridState_iff_axisWords_ne_minInt x).mp hx).2 w
  have hsplice_perm : permElectron g (spliceProj x' x) =
      spliceProj (permElectron g x') (permElectron g x) := by
    apply rProj24_sp.basisSplitEquiv.injective
    refine Prod.ext ?_ ?_
    · rw [QRegister.basisSplitEquiv_apply_fst, QRegister.basisSplitEquiv_apply_fst,
        hex_perm, (spliceProjGen_extract_and_env rProj24_sp x' x).1,
        (spliceProjGen_extract_and_env rProj24_sp (permElectron g x') (permElectron g x)).1,
        hex_perm]
    · rw [env_eq_iff_electron_testBit_eq]
      intro k hk
      have h1 := SpecsAux.BridgeFermionicComm.SpecInner.testBit_permElectron
        g (spliceProj x' x) ⟨k, by change k < 3948; omega⟩
      have h2 := ((env_eq_iff_electron_testBit_eq _ _).mp
        (spliceProjGen_extract_and_env rProj24_sp (permElectron g x') (permElectron g x)).2) k hk
      have h3 := SpecsAux.BridgeFermionicComm.SpecInner.testBit_permElectron
        g x' ⟨k, by change k < 3948; omega⟩
      have hw_lt : (SpecsAux.BridgeFermionicComm.SpecInner.permElectronWire
          g ⟨k, by change k < 3948; omega⟩).val < 3924 := by
        have hgi : (g ⟨k / 18,
            SpecsAux.BridgeFermionicComm.SpecInner.div_18_lt_numElectrons
              hk⟩).val < 218 :=
          (g _).isLt
        change (SpecsAux.BridgeFermionicComm.SpecInner.permElectronWireFun
          g ⟨k, _⟩).val < 3924
        unfold SpecsAux.BridgeFermionicComm.SpecInner.permElectronWireFun
        rw [dite_eq_of_pos hk]
        dsimp only
        omega
      have h4 := ((env_eq_iff_electron_testBit_eq _ _).mp
        (spliceProjGen_extract_and_env rProj24_sp x' x).2) _ hw_lt
      exact h1.trans (h4.trans (h3.symm.trans h2.symm))
  rw [vepFromSlot2Op_apply_of_idle hIdle2, vepFromSlot2Op_apply_of_idle hIdle2]
  refine congrArg (((1 : ℝ) / (108 * 8) : ℂ) * ·) ?_
  refine Finset.sum_congr rfl fun bP _ ↦ Finset.sum_congr rfl fun yIdx _ ↦ ?_
  rw [hex_perm x', hex_perm x, ← hsplice_perm, hPerm2 _ g _ _ hsplice_grid hx]
open Slots01AndGridGuardBridge (slot2Op_Uen) in
noncomputable abbrev slot2ElecOnlyOp (c : Configuration) : Operator (2 ^ systemQubits) :=
  projLift0Gen rProj24_sp (slot2Op_Uen c)
open Slots01AndGridGuardBridge (slot2Op_Uen) in
theorem slot2ElecOnlyOp_comm_embedMatrix (c : Configuration) (M : Operator (2 ^ 24)) :
    slot2ElecOnlyOp c * rProj24_sp.embedMatrix M = rProj24_sp.embedMatrix M * slot2ElecOnlyOp c :=
  projLift0Gen_comm_embedMatrix rProj24_sp (slot2Op_Uen c) M
open Slots01AndGridGuardBridge (projAxisWord8 slot2Op_Uen) in
open SixSlotEndpointJunctionBridge (isGridState_iff_axisWords_ne_minInt) in
theorem gridProjector_mul_slot2ElecOnlyOp (c : Configuration) :
    SpecsAux.gridProjector * slot2ElecOnlyOp c *
        SpecsAux.gridProjector = slot2Op_Uen c := by
  ext x' x
  simp only [SpecsAux.gridProjector, Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases hg : IsGridState x' ∧ IsGridState x
  · rcases hg with ⟨hx', hx⟩
    simp only [hx', hx, ↓reduceIte, one_mul, mul_one, slot2ElecOnlyOp, projLift0Gen_apply]
    obtain ⟨hz0', hp0', he0'⟩ :=
      z0_grid_and_momenta ((isGridState_iff_axisWords_ne_minInt x').mp hx').1
    obtain ⟨hz0, hp0, he0⟩ := z0_grid_and_momenta ((isGridState_iff_axisWords_ne_minInt x).mp hx).1
    by_cases hex : rProj24_sp.extractIndex x' = rProj24_sp.extractIndex x
    · simp only [hex, ↓reduceIte, slot2Op_Uen, Matrix.of_apply, hz0', hz0, hx', hx, and_self]
      have hmp : momentum x' .projectile = momentum x .projectile := funext fun ax ↦ by
        rw [← esmSignedInt256_projAxisWord8_eq_momentum,
          ← esmSignedInt256_projAxisWord8_eq_momentum,
          ← projGridEquiv24_extractIndex_eq_projAxisWord8,
          ← projGridEquiv24_extractIndex_eq_projAxisWord8, hex]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [he0' i, he0 i]
      refine if_congr ⟨fun h b hb ↦ ?_, fun h b hb ↦ ?_⟩ rfl rfl
      · cases b with
        | electron j => rw [← he0' j, ← he0 j]; exact h (.electron j) hb
        | projectile => exact hmp
      · cases b with
        | electron j => rw [he0' j, he0 j]; exact h (.electron j) hb
        | projectile => rw [hp0', hp0]
    · simp only [hex, ↓reduceIte]
      have hne_p : momentum x' .projectile ≠ momentum x .projectile := fun hmp ↦ hex <| by
        apply projGridEquiv24.injective; funext ax
        rw [projGridEquiv24_extractIndex_eq_projAxisWord8,
          projGridEquiv24_extractIndex_eq_projAxisWord8]
        have hsm :=
          signMagnitude_eq_of_momentum_eq_of_isGridState
            hx' hx .projectile ax (congrFun hmp ax)
        simp [projAxisWord8, hsm]
      simp only [slot2Op_Uen, Matrix.of_apply, hx', hx, and_self, ↓reduceIte]
      exact (Finset.sum_eq_zero fun i _ ↦
        ite_eq_right_iff.mpr fun hall ↦ absurd (hall .projectile Particle.noConfusion) hne_p).symm
  · by_cases hx' : IsGridState x'
    · have hx : ¬ IsGridState x := fun h ↦ hg ⟨hx', h⟩
      simp [hx', hx, slot2Op_Uen]
    · simp [hx', slot2Op_Uen]
open TwosCompAndWire0Cancel (fwdPermMatrix_apply fwdPermUnitary) in
theorem unitary_mul_fwdPermUnitary_apply {m : ℕ}
    (U : Unitary (2 ^ m)) (p : Equiv.Perm (Fin (2 ^ m))) (i j : Fin (2 ^ m)) :
    (U * fwdPermUnitary p).1 i j = U.1 i (p j) := by
  rw [Submonoid.coe_mul, Matrix.mul_apply,
    Finset.sum_eq_single (p j)
      (fun k _ hk ↦ by simp [fwdPermUnitary, fwdPermMatrix_apply, hk.symm])
      (fun h ↦ absurd (Finset.mem_univ _) h)]
  simp [fwdPermUnitary, fwdPermMatrix_apply]
theorem swap_vep_sum3 {I B Y : Type} [Fintype I] [Fintype B] [Fintype Y] (w : B → Y → ℂ)
    (g : B → Y → I → ℂ) : (((1 : ℝ) / (108 * 8) : ℂ) * ∑ b : B, ∑ y : Y, w b y * ∑ i : I, g b
    y i) = ∑ i : I, ((1 : ℝ) / (108 * 8) : ℂ) * ∑ b : B, ∑ y : Y, w b y * g b y i := by
  symm
  rw [← Finset.mul_sum]
  congr 1
  calc (∑ i : I, ∑ b : B, ∑ y : Y, w b y * g b y i)
      = ∑ b : B, ∑ i : I, ∑ y : Y, w b y * g b y i := Finset.sum_comm
    _ = ∑ b : B, ∑ y : Y, ∑ i : I, w b y * g b y i :=
        Finset.sum_congr rfl fun _ _ ↦ Finset.sum_comm
    _ = ∑ b : B, ∑ y : Y, w b y * ∑ i : I, g b y i :=
        Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ (Finset.mul_sum _ _ _).symm
set_option maxHeartbeats 400000 in
-- Elevated heartbeats needed for 512-point grid sum reindexing elaboration.
open Slots01AndGridGuardBridge (slot2Op_Uen slot5Op_Vep) in
open SixSlotEndpointJunctionBridge (isGridState_iff_axisWords_ne_minInt) in
open SpecsAux.SpecMirror.SixChannelHamiltonianSplit
    (electron_momentum_mem_Icc) in
theorem gridProjector_mul_vepFromSlot2_slot2ElecOnlyOp :
    SpecsAux.gridProjector * vepFromSlot2Op slot2ElecOnlyOp *
        SpecsAux.gridProjector = slot5Op_Vep := by
  ext x' x
  simp only [SpecsAux.gridProjector, Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases hg : IsGridState x' ∧ IsGridState x
  · rcases hg with ⟨hx', hx⟩
    simp only [hx', hx, ↓reduceIte, one_mul, mul_one]
    rw [vepFromSlot2Op_apply_of_idle (fun _ M ↦ slot2ElecOnlyOp_comm_embedMatrix _ M)]
    obtain ⟨hex_s, henv_s⟩ := spliceProjGen_extract_and_env rProj24_sp x' x
    have hsm_entry : ∀ (bP : Fin 3 → Fin 2) (yIdx : Fin (2 ^ 24)),
        star ((uProjPlus512SM_3D bP).1 yIdx (rProj24_sp.extractIndex x')) *
          (uProjPlus512SM_3D bP).1 yIdx (rProj24_sp.extractIndex x) =
        star (projSubGridElem256_3D bP (projGridEquiv24 yIdx) (momentum x .projectile)) *
          projSubGridElem256_3D bP (projGridEquiv24 yIdx) (momentum x' .projectile) := fun bP yIdx ↦
            by
      have hU : ∀ w : Fin (2 ^ systemQubits), IsGridState w →
          (uProjPlus512SM_3D bP).1 yIdx (rProj24_sp.extractIndex w) =
            star (projSubGridElem256_3D bP (projGridEquiv24 yIdx) (momentum w .projectile)) :=
              fun w hw ↦ by
        rw [uProjPlus512SM_3D, unitary_mul_fwdPermUnitary_apply]
        simp only [uProjPlus512_3D, uProjPlus512Twos_3D,
          uProjPlus512TwosMat3D, Matrix.of_apply, projTwosMom3D_sm_extractIndex_eq_momentum hw]
      rw [hU x' hx', hU x hx, star_star, mul_comm]
    have hz_eq : rProj24_sp.basisSplitEquiv.symm (0,
      (rProj24_sp.basisSplitEquiv (spliceProj x' x)).2) =
        rProj24_sp.basisSplitEquiv.symm (0, (rProj24_sp.basisSplitEquiv x').2) := by rw [henv_s]
    obtain ⟨hz0', hp0', he0'⟩ :=
      z0_grid_and_momenta ((isGridState_iff_axisWords_ne_minInt x').mp hx').1
    obtain ⟨hz0, hp0, he0⟩ := z0_grid_and_momenta ((isGridState_iff_axisWords_ne_minInt x).mp hx).1
    have hslot : ∀ c : Configuration,
        slot2ElecOnlyOp c (spliceProj x' x) x =
          ∑ i : Fin numElectrons,
            if ∀ d,
              d ≠ Particle.electron i → d ≠ Particle.projectile → momentum x' d = momentum x d then
              -(structureFactor c (momentum x' (.electron i) - momentum x (.electron i)) *
                (coulombKernel (momentum x' (.electron i) - momentum x (.electron i)) : ℂ))
            else 0 := fun c ↦ by
      rw [slot2ElecOnlyOp, projLift0Gen_apply]
      simp only [hex_s, ↓reduceIte, hz_eq, slot2Op_Uen, Matrix.of_apply, hz0', hz0, and_self]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [he0' i, he0 i]
      refine if_congr ⟨fun h d hd1 hd2 ↦ ?_, fun h b hb ↦ ?_⟩ rfl rfl
      · cases d with
        | electron j => rw [← he0' j, ← he0 j]; exact h (.electron j) hd1
        | projectile => exact (hd2 rfl).elim
      · cases b with
        | electron j => rw [he0' j, he0 j]; exact h (.electron j) hb Particle.noConfusion
        | projectile => rw [hp0', hp0]
    simp_rw [hsm_entry, hslot]
    let gTerm (bP : Fin 3 → Fin 2) (yIdx : Fin (2 ^ 24)) (i : Fin numElectrons) : ℂ := if ∀ d,
        d ≠ Particle.electron i → d ≠ Particle.projectile → momentum x' d = momentum x d then
        -(structureFactor (cfgProjZ512 (nyq512ProjEquiv3D (projGridEquiv24 yIdx, bP)))
        (momentum x' (.electron i) - momentum x (.electron i)) * (coulombKernel (momentum x'
        (.electron i) - momentum x (.electron i)) : ℂ)) else 0
    let wTerm (bP : Fin 3 → Fin 2) (yIdx : Fin (2 ^ 24)) : ℂ :=
      star (projSubGridElem256_3D bP (projGridEquiv24 yIdx) (momentum x .projectile)) *
        projSubGridElem256_3D bP (projGridEquiv24 yIdx) (momentum x' .projectile)
    have hswap : (((1 : ℝ) / (108 * 8) : ℂ) * ∑ bP : Fin 3 → Fin 2, ∑ yIdx : Fin (2 ^ 24),
        wTerm bP yIdx * ∑ i : Fin numElectrons, gTerm bP yIdx i) = ∑ i : Fin numElectrons,
        ((1 : ℝ) / (108 * 8) : ℂ) * ∑ bP : Fin 3 → Fin 2, ∑ yIdx : Fin (2 ^ 24), wTerm bP yIdx
        * gTerm bP yIdx i := swap_vep_sum3 wTerm gTerm
    change (((1 : ℝ) / (108 * 8) : ℂ) * ∑ bP : Fin 3 → Fin 2, ∑ yIdx : Fin (2 ^ 24), wTerm bP
      yIdx * ∑ i : Fin numElectrons, gTerm bP yIdx i) = _
    rw [hswap]
    dsimp only [wTerm, gTerm]
    simp only [slot5Op_Vep, Matrix.of_apply, hx', hx, and_self, ↓reduceIte]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    by_cases hspec : ∀ d,
      d ≠ Particle.electron i → d ≠ Particle.projectile → momentum x' d = momentum x d
    · simp only [eq_true hspec, true_and, ↓reduceIte]
      have hreidx : ∀ bP : Fin 3 → Fin 2, (∑ yIdx : Fin (2 ^ 24), (star (projSubGridElem256_3D
          bP (projGridEquiv24 yIdx) (momentum x .projectile)) * projSubGridElem256_3D bP
          (projGridEquiv24 yIdx) (momentum x' .projectile)) * (-(structureFactor (cfgProjZ512
          (nyq512ProjEquiv3D (projGridEquiv24 yIdx, bP))) (momentum x' (.electron i) -
          momentum x (.electron i)) * (coulombKernel (momentum x' (.electron i) - momentum x
          (.electron i)) : ℂ)))) = ∑ yP : NyqGrid3D256, (star (projSubGridElem256_3D bP yP
          (momentum x .projectile)) * projSubGridElem256_3D bP yP (momentum x' .projectile)) *
          (-(structureFactor (cfgProjZ512 (nyq512ProjEquiv3D (yP, bP))) (momentum x'
          (.electron i) - momentum x (.electron i)) * (coulombKernel (momentum x' (.electron
          i) - momentum x (.electron i)) : ℂ))) := fun bP ↦ Equiv.sum_comp projGridEquiv24 fun
          yP ↦ (star (projSubGridElem256_3D bP yP (momentum x .projectile)) *
          projSubGridElem256_3D bP yP (momentum x' .projectile)) * (-(structureFactor
          (cfgProjZ512 (nyq512ProjEquiv3D (yP, bP))) (momentum x' (.electron i) - momentum x
          (.electron i)) * (coulombKernel (momentum x' (.electron i) - momentum x (.electron
          i)) : ℂ)))
      simp_rw [hreidx]
      exact projPlus512_avg_cfgProjZ512_eq (fun ν ↦ (coulombKernel ν : ℂ))
        (electron_momentum_mem_Icc x' i)
        (electron_momentum_mem_Icc x i)
        (inProjMomGrid3D_of_state x') (inProjMomGrid3D_of_state x)
    · simp only [eq_false hspec, false_and, ↓reduceIte, mul_zero, Finset.sum_const_zero]
  · by_cases hx' : IsGridState x'
    · have hx : ¬ IsGridState x := fun h ↦ hg ⟨hx', h⟩
      simp [hx', hx, slot5Op_Vep]
    · simp [hx', slot5Op_Vep]
theorem vepFromSlot2Op_sub (F G : Configuration → Operator (2 ^ systemQubits)) :
    vepFromSlot2Op (fun c ↦ F c - G c) = vepFromSlot2Op F - vepFromSlot2Op G :=
  vepGen_sub rProj24_sp projGridEquiv24 uProjPlus512SM_3D F G
open SixSlotEndpointJunctionBridge (slot2Op_Uen_eq_sixChannelRaw
  slot5Op_Vep_eq_sixChannelRaw sixChannelGridProjector_eq_specsGridProjector
  norm_fermionicProjector_le_one) in
theorem vepFromSlot2_fermionicError_le (cfg : Configuration)
    (spinUp : Finset (Fin numElectrons)) (E : Fin 6 → ℝ) {eps2 : ℝ} (heps2 : 0 ≤ eps2)
    (hE5 : E 5 = E 2 / 108) (B_raw2 : Configuration → Operator (2 ^ systemQubits)) (hIdle2 : ∀
    (zP : NyqFine3D512) (M : Operator (2 ^ 24)), B_raw2 (cfgProjZ512 zP) *
    rProj24_sp.embedMatrix M = rProj24_sp.embedMatrix M * B_raw2 (cfgProjZ512 zP)) (hErr2 : ∀
    zP : NyqFine3D512, ‖fermionicProjector spinUp * (B_raw2 (cfgProjZ512 zP) -
    sixChannelShifted (cfgProjZ512 zP) E 2) * fermionicProjector spinUp‖ ≤ eps2) :
    ‖fermionicProjector spinUp * (vepFromSlot2Op B_raw2 - sixChannelShifted cfg E 5) *
    fermionicProjector spinUp‖ ≤ (1 / 108 : ℝ) * eps2 :=
  vepGen_projError_le rProj24_sp projGridEquiv24 uProjPlus512SM_3D
    (fermionicProjector spinUp) SpecsAux.gridProjector
    (SpecsAux.BridgeFermionicComm.SpecInner.fermionicProjector_isHermitian spinUp).eq
    (norm_fermionicProjector_le_one spinUp)
    (projBasisProj_comm_fermionicProjector spinUp 0)
    ⟨elecFermionicProjector_mul_fermionicProjector spinUp,
      fermionicProjector_mul_elecFermionicProjector spinUp⟩
    ⟨SpecsAux.fermionicProjector_mul_gridProjector spinUp,
      SpecsAux.gridProjector_mul_fermionicProjector spinUp⟩
    (E 2) (E 5) heps2 hE5
    slot2ElecOnlyOp B_raw2
    (fun c ↦ sixChannelShifted c E 2)
    (sixChannelShifted cfg E 5)
    (fun zP M ↦ slot2ElecOnlyOp_comm_embedMatrix (cfgProjZ512 zP) M)
    hIdle2
    (by
      unfold sixChannelShifted
      rw [gridProjector_mul_vepFromSlot2_slot2ElecOnlyOp, slot5Op_Vep_eq_sixChannelRaw cfg,
        sixChannelGridProjector_eq_specsGridProjector])
    (fun zP ↦ by
      unfold sixChannelShifted
      rw [gridProjector_mul_slot2ElecOnlyOp, slot2Op_Uen_eq_sixChannelRaw,
        sixChannelGridProjector_eq_specsGridProjector])
    hErr2
open SixSlotEndpointJunctionBridge (commute_fermionicProjector_of_inGridPerm)
  in
theorem vepFromSlot2_agreesOnFermionicSector (cfg : Configuration)
    (spinUp : Finset (Fin numElectrons)) (E : Fin 6 → ℝ) {eps2 : ℝ} (heps2 : 0 ≤ eps2)
    (hE5 : E 5 = E 2 / 108) (B_raw2 : Configuration → Operator (2 ^ systemQubits)) (hIdle2 : ∀
    (zP : NyqFine3D512) (M : Operator (2 ^ 24)), B_raw2 (cfgProjZ512 zP) *
    rProj24_sp.embedMatrix M = rProj24_sp.embedMatrix M * B_raw2 (cfgProjZ512 zP)) (hPerm2 : ∀
    (zP : NyqFine3D512) (g : Equiv.Perm (Fin numElectrons)) (a b : Fin (2 ^ systemQubits)),
    IsGridState a → IsGridState b → B_raw2 (cfgProjZ512 zP) (permElectron g a) (permElectron g
    b) = B_raw2 (cfgProjZ512 zP) a b) (hErr2 : ∀ zP : NyqFine3D512, ‖fermionicProjector spinUp
    * (B_raw2 (cfgProjZ512 zP) - sixChannelShifted (cfgProjZ512 zP) E 2) * fermionicProjector
    spinUp‖ ≤ eps2) : FullScaleBESector.AgreesOnFermionicSector spinUp
    (SpecsAux.gridProjector * vepFromSlot2Op B_raw2 *
    SpecsAux.gridProjector) (sixChannelShifted cfg E 5)
    ((1 / 108 : ℝ) * eps2) :=
  ⟨commute_fermionicProjector_of_inGridPerm (vepFromSlot2Op B_raw2)
      (vepFromSlot2Op_inGridPerm hIdle2 hPerm2) spinUp,
    by
      rw [projSector_guard_diff_eq (fermionicProjector spinUp)
        SpecsAux.gridProjector (vepFromSlot2Op B_raw2) (sixChannelShifted cfg E
          5)
        ⟨SpecsAux.fermionicProjector_mul_gridProjector spinUp,
          SpecsAux.gridProjector_mul_fermionicProjector spinUp⟩]
      exact vepFromSlot2_fermionicError_le cfg spinUp E heps2 hE5 B_raw2 hIdle2 hErr2⟩
set_option exponentiation.threshold 256
set_option maxRecDepth 512
set_option backward.isDefEq.respectTransparency true
end ConfigPosSlots24MergedVepBound
end PosSlots24MergedVepBound
end
end ModPosSlots24MergedVepBound

section ModPosSlots24TopWrapper
@[expose] public section
namespace PosSlots24TopWrapper
open Operator QProg Matrix Real
open scoped Matrix BigOperators Matrix.Norms.L2Operator Circuit.Notation
open SpecsAux SpecsAux.SpecMirror
open SpecsAux.BridgeFermionicComm
open SpecsAux.BridgeFermionicComm.SpecInner
open Dyadic128CoulombMath (orbitCount47905)
open PosSlots24BranchConcrete
def rPosSubLocal : QRegister posPayloadWires posCoreWires :=
  rSubPayloadCore (QRegExt.ofFin posCoreWires)
def regTail {m n : ℕ} (rSub : QRegister (m + 1) n) : QRegister m n where
  wires :=
    { toFun := fun i ↦ rSub i.succ
      inj' := fun _ _ h ↦ Fin.succ_inj.mp (rSub.wires.injective h) }
def writeSubBits {n : ℕ} : {m : ℕ} → QRegister m n → BitAssignment n → BitAssignment m →
    BitAssignment n
  | 0, _, β, _ => β
  | _ + 1, rSub, β, u =>
      writeSubBits (regTail rSub) (Function.update β (rSub 0) (u 0)) (fun i ↦ u i.succ)
theorem writeSubBits_apply_not_mem {n : ℕ} :
    ∀ {m : ℕ} (rSub : QRegister m n) (β : BitAssignment n) (u : BitAssignment m) (q : Wire n),
      (∀ j : Fin m, q ≠ rSub j) → writeSubBits rSub β u q = β q
  | 0, _, _, _, _, _ => rfl
  | _ + 1, rSub, β, u, q, hq => by
      dsimp only [writeSubBits]
      rw [writeSubBits_apply_not_mem (regTail rSub) _ _ q (fun j ↦ hq j.succ),
        Function.update_of_ne (hq 0)]
@[simp] theorem writeSubBits_apply_mem {n : ℕ} :
    ∀ {m : ℕ} (rSub : QRegister m n) (β : BitAssignment n) (u : BitAssignment m) (j : Fin m),
      writeSubBits rSub β u (rSub j) = u j
  | 0, _, _, _, j => Fin.elim0 j
  | _ + 1, rSub, β, u, j =>
      Fin.cases
        (by
          dsimp only [writeSubBits]
          rw [writeSubBits_apply_not_mem (regTail rSub) _ _ (rSub 0)
              (fun k h ↦ Fin.succ_ne_zero k (rSub.wires.injective h).symm),
            Function.update_self])
        (fun i ↦ by
          dsimp only [writeSubBits]
          exact writeSubBits_apply_mem (regTail rSub)
            (Function.update β (rSub 0) (u 0)) (fun k ↦ u k.succ) i)
        j
theorem writeSubBits_rPosSubLocal_lt3954 (β : BitAssignment posCoreWires)
    (u : BitAssignment posPayloadWires) (k : Wire posCoreWires) (hk : k.val < 3954) :
    writeSubBits rPosSubLocal β u k = β k :=
  writeSubBits_apply_not_mem rPosSubLocal β u k fun j h ↦ by
    have hv1 : k.val = (rPosSubLocal.wires j).val := congrArg Fin.val h
    have hv2 : (rPosSubLocal.wires j).val = 3954 + j.val := rfl
    omega
section FullSysPosSlots24Bundle
open PosMomSelectSandwich (slotBitProj)
theorem uPosPhase_sa_core (slot2SwappedTo0 : Bool) (tailSign : Fin orbitCount47905 → Bool)
    (tailMag30 : Fin orbitCount47905 → Fin (2 ^ 30)) :
    (uPosPhase slot2SwappedTo0 tailSign tailMag30).1ᴴ =
    (uPosPhase slot2SwappedTo0 tailSign tailMag30).1 := uPosPhase_conjTranspose
    slot2SwappedTo0 tailSign tailMag30
structure PosSlots24DataGen (coreW : ℕ) (w2 : Wire coreW) (mWorkSelect : ℕ) where
  uPosPhase : SpecsAux.SpecMirror.Configuration → Unitary (2 ^ coreW)
  hPos_sa : ∀ c, (uPosPhase c).1ᴴ = (uPosPhase c).1
  hPos_on_P1 : ∀ c, (uPosPhase c).1 * slotBitProj w2 1 = slotBitProj w2 1
end FullSysPosSlots24Bundle
end PosSlots24TopWrapper
end
end ModPosSlots24TopWrapper

end QuantumComputation.Specs.StoppingPowerSolution
