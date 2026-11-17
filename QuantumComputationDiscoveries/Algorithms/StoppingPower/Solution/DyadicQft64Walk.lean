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

public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.GridGuard654Refl
set_option Elab.async false

@[expose] public section
set_option exponentiation.threshold 256
set_option allowUnsafeReducibility true

namespace QuantumComputation.Specs.StoppingPowerSolution

section ModDyadicQft64WalkCircuit
@[expose] public section
namespace DyadicQft64WalkCircuitAlt
theorem qreg_ext {k n : ℕ} {r s : QRegister k n} (h : ∀ i, r i = s i) : r = s :=
  QRegister.ext (Function.Embedding.ext h)
end DyadicQft64WalkCircuitAlt
namespace DyadicQft64WalkCircuit
section ConfigDyadicQft64WalkCircuit
set_option maxRecDepth 200000
local instance (priority := 1000000) instNeZeroTwoPowWalk {k : ℕ} : NeZero (2 ^ k) := ⟨pow_ne_zero k
  (by decide)⟩
section Section1FredkinAndBypass
open Real Operator Matrix QProg HermitianMat
open DyadicQft64
open scoped Matrix ComplexOrder MatrixOrder Circuit.Notation BigOperators
section FredkinAndBypass
variable {Var : Type} {n : ℕ}
lemma basisBits_symm_apply {q : ℕ} (g : BitAssignment q) (i : Fin q) :
    basisBits q ((basisBitsEquiv q).symm g) i = g i :=
  congrFun ((basisBitsEquiv q).apply_symm_apply g) i
end FredkinAndBypass
end Section1FredkinAndBypass
section Section2APart1Batches
open Real Operator Matrix QProg HermitianMat _root_.DynamicCircuit DynCircuitExt LocalClassicalPerm
open DyadicQft64
open scoped Matrix ComplexOrder MatrixOrder Circuit.Notation BigOperators
section BatchEngines
variable {Var : Type} {n : ℕ}
lemma basisBits_symm_apply_2a {q : ℕ} (g : BitAssignment q) (i : Fin q) :
    basisBits q ((basisBitsEquiv q).symm g) i = g i :=
  congrFun ((basisBitsEquiv q).apply_symm_apply g) i
lemma zmod2_add_cancel_right (x y : ZMod 2) : x + y + y = x :=
  (by decide : ∀ x y : ZMod 2, x + y + y = x) x y
lemma count_dyn_circuit {a : ℕ} (g : PrimitiveGate a) (c : Circuit n) :
    (DynamicCircuit.circuit (Var := Var) c).count g = c.count g := rfl
lemma count_dyn_seq {a : ℕ} (g : PrimitiveGate a) (d₁ d₂ : DynamicCircuit Var n) :
    (d₁.seq d₂).count g = d₁.count g + d₂.count g := rfl
lemma count_cir_id {a : ℕ} (g : PrimitiveGate a) :
    (Circuit.identity : Circuit n).count g = 0 := rfl
def compressStepsNat : List ℕ → ℕ → ℕ
  | [], _ => 0
  | L :: rest, inC => (L + inC) / 2 + compressStepsNat rest ((L + inC) / 2)
def finalCarriesNat : List ℕ → ℕ → ℕ
  | [], inC => inC
  | L :: rest, inC => finalCarriesNat rest ((L + inC) / 2)
theorem compressStepsCount_eq_nat (buckets : List (List (Wire n))) (inC : ℕ) :
    compressStepsCount buckets inC = compressStepsNat (buckets.map List.length) inC := by
  induction buckets generalizing inC with
  | nil => rfl
  | cons _ _ ih => simp [compressStepsCount, compressStepsNat, ih]
theorem compressBucketsAux_carries_length {m_anc : ℕ} (rAnc : QRegister m_anc n)
    (buckets : List (List (Wire n))) (inCarries : List (Wire n)) (offset : ℕ) (hfit : offset +
    compressStepsCount buckets inCarries.length ≤ m_anc) (hB_nodup : ∀ B ∈ buckets, B.Nodup)
    (hB_disj : buckets.Pairwise fun B₁ B₂ ↦ ∀ x ∈ B₁, x ∉ B₂)
    (hB_anc : ∀ B ∈ buckets, ∀ x ∈ B, x ∉ rAnc.image) (hin_nodup : inCarries.Nodup) (hin_anc :
    ∀ c ∈ inCarries, ∃ k, ∃ hk : k < m_anc, k < offset ∧ c = rAnc ⟨k, hk⟩) :
    (compressBucketsAux rAnc buckets inCarries offset hfit hB_nodup hB_disj hB_anc hin_nodup
    hin_anc).carries.length = finalCarriesNat (buckets.map List.length) inCarries.length := by
  induction buckets generalizing inCarries offset with
  | nil => rfl
  | cons B rest ih =>
      let fullB := B ++ inCarries
      have hfit1 : offset + fullB.length / 2 ≤ m_anc := by
        simp only [fullB, List.length_append, compressStepsCount] at hfit ⊢
        omega
      have hfull_nodup : fullB.Nodup := List.nodup_append.mpr
        ⟨hB_nodup B (by simp), hin_nodup, fun _ hxB _ hy heq ↦
          let ⟨k, hk, _, hr⟩ := hin_anc _ (heq ▸ hy)
          hB_anc B (by simp) _ hxB ((QRegister.mem_image rAnc _).mpr ⟨⟨k, hk⟩, hr.symm⟩)⟩
      have hfull_anc_disj (x : Wire n) (hx : x ∈ fullB) (k : ℕ) (_ : offset ≤ k)
          (hkm : k < m_anc) (heq : x = rAnc ⟨k, hkm⟩) : False := by
        rcases List.mem_append.mp hx with hxB | hxc
        · exact hB_anc B (by simp) _ (heq ▸ hxB)
            ((QRegister.mem_image rAnc _).mpr ⟨⟨k, hkm⟩, rfl⟩)
        · rcases hin_anc x hxc with ⟨k₀, hk₀, hk₀_lt, rfl⟩
          have hv := congrArg Fin.val (rAnc.wires.injective heq)
          dsimp at hv
          omega
      have hr1_0 := reduceBucket_spec ∅ rAnc (by simp) fullB offset hfit1 hfull_nodup
        hfull_anc_disj (by simp)
      have hlen_c : (reduceBucket rAnc fullB offset hfit1 hfull_nodup
          hfull_anc_disj).carries.length = (B.length + inCarries.length) / 2 := by
        simpa [fullB, List.length_append] using hr1_0.2.1
      have hfit_rest : (offset + fullB.length / 2) + compressStepsCount rest
          (reduceBucket rAnc fullB offset hfit1 hfull_nodup hfull_anc_disj).carries.length ≤
          m_anc := by
        rw [hlen_c]
        simpa [fullB, List.length_append, compressStepsCount, add_assoc] using hfit
      change (compressBucketsAux rAnc rest _ (offset + fullB.length / 2) hfit_rest
        (fun B' hB' ↦ hB_nodup B' (by simp [hB'])) (List.pairwise_cons.mp hB_disj).2
        (fun B' hB' ↦ hB_anc B' (by simp [hB'])) hr1_0.2.2.1
        (fun c hc ↦ let ⟨k, hk, _, hk_lt, hc_eq⟩ := hr1_0.2.2.2.1 c hc
          ⟨k, hk, hk_lt, hc_eq⟩)).carries.length = _
      rw [ih, hlen_c]
      rfl
theorem compressBuckets_carries_length {m_anc : ℕ} (rAnc : QRegister m_anc n)
    (buckets : List (List (Wire n))) (offset : ℕ)
    (hfit : offset + compressStepsCount buckets 0 ≤ m_anc) (hB_nodup : ∀ B ∈ buckets, B.Nodup)
    (hB_disj : buckets.Pairwise fun B₁ B₂ ↦ ∀ x ∈ B₁, x ∉ B₂)
    (hB_anc : ∀ B ∈ buckets, ∀ x ∈ B, x ∉ rAnc.image) :
    (compressBuckets rAnc buckets offset hfit hB_nodup hB_disj hB_anc).carries.length =
      finalCarriesNat (buckets.map List.length) 0 :=
  compressBucketsAux_carries_length rAnc buckets [] offset hfit hB_nodup hB_disj hB_anc
    List.nodup_nil fun _ h ↦ nomatch h
theorem cleanPhasePerm_sandwich_phase
    [Fintype Var] [DecidableEq Var] [NeZero (2 ^ n)] {m : ℕ}
    {rWork : QRegister m n} {M_c M_d : Finset (Wire n)}
    (c_pre c_post : Circuit n)
    (φ_pre φ_post : BitAssignment n → ℂ)
    (f_pre f_post : BitAssignment n → BitAssignment n)
    (hc1 : PhasePerm M_c c_pre φ_pre f_pre)
    (hc3 : PhasePerm M_c c_post φ_post f_post)
    (hdisj_W : Disjoint M_c rWork.image)
    {d : DynamicCircuit Var n} {c_mid : Circuit n}
    {φ_mid : BitAssignment n → ℂ} {f_mid : BitAssignment n → BitAssignment n}
    (hcpp : CleanPhasePerm rWork M_d d c_mid φ_mid f_mid) :
    CleanPhasePerm rWork (M_c ∪ M_d)
      ((DynamicCircuit.circuit (Var := Var) c_pre).seq
        (d.seq (DynamicCircuit.circuit (Var := Var) c_post)))
      (c_pre ;;ᶜ c_mid ;;ᶜ c_post)
      (fun β ↦ φ_pre β * (φ_mid (f_pre β) * φ_post (f_mid (f_pre β))))
      (f_post ∘ f_mid ∘ f_pre) := by
  refine ⟨(hc1.mono Finset.subset_union_left).seq
    ((hcpp.phasePerm.mono Finset.subset_union_right).seq (hc3.mono Finset.subset_union_left)),
    fun Q ↦ ?_, fun Q ↦ restrictAssertionToZeroAncilla_seq_unitary_sandwich rWork M_c c_pre
      φ_pre f_pre hc1 hdisj_W d c_mid c_post (fun _ ↦ Q)
      (hcpp.wp_obs (qAssignObsMap c_post.eval Q))⟩
  obtain ⟨Q₂, hQ₂⟩ := hcpp.wp_const (qAssignObsMap c_post.eval Q)
  have hcirc {c : Circuit n} (R : Observable (Fin (2 ^ n))) :
      wp (DynamicCircuit.circuit (Var := Var) c).compile (fun _ ↦ R) =
        fun _ ↦ qAssignObsMap c.eval R := by
    rw [DynamicCircuit.compile_circuit, DynCircuitExt.wp_circuit_compile_compat]
    rfl
  refine ⟨qAssignObsMap c_pre.eval Q₂, ?_⟩
  simp only [DynamicCircuit.compile_seq, wp_qSeq, hcirc, hQ₂]
theorem restrictAssertionToZeroAncilla_sandwich_var [Fintype Var] [DecidableEq Var]
    [NeZero (2 ^ n)] {m : ℕ} (v : Var) (rC : QRegister m n) (M_c : Finset (Wire n))
    (c_pre c_post : Circuit n) (φ_pre : BitAssignment n → ℂ)
    (f_pre : BitAssignment n → BitAssignment n) (hc1 : PhasePerm M_c c_pre φ_pre f_pre)
    (hdisj_W : Disjoint M_c rC.image) (d_mid : DynamicCircuit Var n) (c_mid : Circuit n)
    (hwp_mid : ∀ Θ : CQAssertionCompat Var (2 ^ n), (∀ σ val, Θ (Function.update σ v val) = Θ σ) →
      CQAssertion.restrictToZeroAncilla (wp d_mid.compile Θ) rC =
      CQAssertion.restrictToZeroAncilla (wpQAssignCompat c_mid.eval Θ) rC) :
    ∀ Ψ : CQAssertionCompat Var (2 ^ n), (∀ σ val, Ψ (Function.update σ v val) = Ψ σ) →
      CQAssertion.restrictToZeroAncilla (wp ((DynamicCircuit.circuit (Var := Var) c_pre).seq
        (d_mid.seq (DynamicCircuit.circuit (Var := Var) c_post))).compile Ψ) rC =
      CQAssertion.restrictToZeroAncilla (wpQAssignCompat (c_pre ;;ᶜ c_mid ;;ᶜ c_post).eval Ψ) rC :=
  fun Ψ hΨ ↦ restrictAssertionToZeroAncilla_seq_unitary_sandwich rC M_c c_pre φ_pre f_pre hc1
    hdisj_W d_mid c_mid c_post Ψ
    (hwp_mid _ fun σ val ↦ congrArg (qAssignObsMap c_post.eval) (hΨ σ val))
noncomputable def canonAssign {kSys : ℕ} (rSys : QRegister kSys n) [NeZero (2 ^ n)]
    (γ : BitAssignment kSys) : BitAssignment n :=
  basisBits n (rSys.replaceIndex ⟨0, NeZero.pos (2 ^ n)⟩ ((basisBitsEquiv kSys).symm γ))
theorem canonAssign_apply_sys [NeZero (2 ^ n)] {kSys : ℕ} (rSys : QRegister kSys n)
    (γ : BitAssignment kSys) (i : Fin kSys) : canonAssign rSys γ (rSys i) = γ i :=
  (rSys.basisBits_replaceIndex_apply _ _ i).trans (basisBits_symm_apply_2a γ i)
theorem canonAssign_apply_outside [NeZero (2 ^ n)] {kSys : ℕ} (rSys : QRegister kSys n)
    (γ : BitAssignment kSys) {w : Wire n} (hw : w ∉ rSys.image) : canonAssign rSys γ w = 0 := by
  dsimp only [canonAssign]
  rw [rSys.basisBits_replaceIndex_of_not_mem _ _ w
    (fun ⟨i, hi⟩ ↦ hw ((QRegister.mem_image rSys w).mpr ⟨i, hi⟩)), basisBits_eq_div_mod]
  simp
theorem symStepFwdList_eq_on_superset {U : Finset (Wire n)} (steps : List (SymTempAndStep n))
    (hU : ∀ s ∈ steps, s.S ⊆ U) {β₁ β₂ : BitAssignment n} (hag : ∀ w ∈ U, β₁ w = β₂ w) :
    ∀ w ∈ U, symStepFwdList steps β₁ w = symStepFwdList steps β₂ w := by
  induction steps generalizing β₁ β₂ with
  | nil => exact hag
  | cons s rest ih =>
      exact ih (fun s' hs' ↦ hU s' (by simp [hs'])) fun w hw ↦ by
        by_cases hws : w ∈ s.S
        · have hp := s.local_pre.depends_on β₁ β₂ fun u hu ↦ hag u (hU s (by simp) hu)
          exact s.local_midPre.depends_on _ _ (fun q hq ↦ by
            by_cases hqa : q = s.anc
            · subst hqa
              simp only [Function.update_self, hp s.anc s.anc_mem, hp s.c₁ s.c₁_mem,
                hp s.c₂ s.c₂_mem]
            · simp only [Function.update_of_ne hqa, hp q hq]) w hws
        · rw [s.stepFwd_outside β₁ hws, s.stepFwd_outside β₂ hws, hag w hw]
def finMapList {α : Type*} : ∀ {L : ℕ}, (Fin L → α) → List α
  | 0, _ => []
  | _ + 1, f => f 0 :: finMapList fun i ↦ f i.succ
@[simp] theorem finMapList_length {α : Type*} : ∀ {L : ℕ} (f : Fin L → α),
    (finMapList f).length = L
  | 0, _ => rfl
  | _ + 1, _ => by simp [finMapList, finMapList_length]
theorem mem_finMapList {α : Type*} : ∀ {L : ℕ} {f : Fin L → α} {x : α},
    x ∈ finMapList f ↔ ∃ i : Fin L, f i = x
  | 0, _, _ => by simp [finMapList]
  | _ + 1, _, _ => by
      simp only [finMapList, List.mem_cons, mem_finMapList]
      exact ⟨fun h ↦ h.elim (fun h0 ↦ ⟨0, h0.symm⟩) fun ⟨i, hi⟩ ↦ ⟨i.succ, hi⟩,
        fun ⟨i, hi⟩ ↦ Fin.cases (fun h0 ↦ Or.inl h0.symm) (fun j hj ↦ Or.inr ⟨j, hj⟩) i hi⟩
theorem finMapList_nodup {α : Type*} : ∀ {L : ℕ} {f : Fin L → α},
    Function.Injective f → (finMapList f).Nodup
  | 0, _, _ => List.nodup_nil
  | _ + 1, _, hinj => List.nodup_cons.mpr ⟨fun hm ↦
      let ⟨j, hj⟩ := mem_finMapList.mp hm
      Fin.succ_ne_zero j (hinj hj), finMapList_nodup fun _ _ h ↦ Fin.succ_injective _ (hinj h)⟩
theorem wireListSum_finMapList : ∀ {L : ℕ} (f : Fin L → Wire n) (β : BitAssignment n),
    wireListSum (finMapList f) β = ∑ l : Fin L, (β (f l)).val
  | 0, _, _ => rfl
  | _ + 1, _, _ => by
      rw [finMapList, wireListSum_cons, wireListSum_finMapList, Fin.sum_univ_succ]
theorem weightedBucketsVal_finMapList : ∀ {m : ℕ} (g : Fin m → List (Wire n))
    (β : BitAssignment n), weightedBucketsVal (finMapList g) β =
      ∑ r : Fin m, 2 ^ r.val * wireListSum (g r) β
  | 0, _, _ => rfl
  | _ + 1, _, _ => by
      rw [finMapList, weightedBucketsVal, weightedBucketsVal_finMapList, Fin.sum_univ_succ]
      simp only [Fin.val_zero, _root_.pow_zero, one_mul, Fin.val_succ, pow_succ',
        Finset.mul_sum]
      exact congrArg (_ + ·) (Finset.sum_congr rfl fun _ _ ↦ by ring)
theorem buckets_pairwise_finMapList {m : ℕ} (g : Fin m → List (Wire n))
    (hdisj : ∀ r₁ r₂ : Fin m, r₁ ≠ r₂ → ∀ x ∈ g r₁, x ∉ g r₂) :
    (finMapList g).Pairwise fun B₁ B₂ ↦ ∀ x ∈ B₁, x ∉ B₂ := by
  induction m with
  | zero => simp [finMapList]
  | succ _ ih =>
      exact List.pairwise_cons.mpr ⟨fun _ hB₂ x hx₁ hx₂ ↦
        let ⟨r₂, hr₂⟩ := mem_finMapList.mp hB₂
        hdisj 0 r₂.succ (Fin.succ_ne_zero r₂).symm x hx₁ (hr₂ ▸ hx₂),
        ih (fun r ↦ g r.succ) fun _ _ hne ↦ hdisj _ _ fun he ↦ hne (Fin.succ_injective _ he)⟩
theorem disjWires_image {m₁ m₂ : ℕ} {r₁ : QRegister m₁ n} {r₂ : QRegister m₂ n}
    (h : r₁.DisjointWires r₂) : Disjoint r₁.image r₂.image :=
  ((QRegExt.disjointWires_iff_disjoint_image r₁) r₂).mp h
theorem two_pow_mul_four_sub (s : ℕ) (hs : s ≤ 3) : 2 ^ s * 2 ^ (4 - s) = 16 := by
  interval_cases s <;> decide
attribute [irreducible] finMapList
theorem weightedOptWiresVal_eq_bitsVal (wZero : Wire n) :
    ∀ {K : ℕ} (sw : List (Option (Wire n))) (hsw : sw.length = K)
      (β : BitAssignment n) (_hz : β wZero = 0),
      bitsVal (fun j : Fin K ↦ β (optWireOrZero wZero (sw.get ⟨j.val, by omega⟩))) =
        weightedOptWiresVal sw β
  | 0, [], _, _, _ => by simp [bitsVal, weightedOptWiresVal]
  | 0, _ :: _, hsw, _, _ => by simp at hsw
  | _ + 1, [], hsw, _, _ => by simp at hsw
  | K + 1, ow :: rest, hsw, β, hz => by
      have hrest : rest.length = K := by simpa using hsw
      have hstep := weightedOptWiresVal_eq_bitsVal wZero rest hrest β hz
      unfold bitsVal
      rw [Fin.sum_univ_succ]
      have htail : (∑ x : Fin K,
          (β (optWireOrZero wZero ((ow :: rest).get ⟨x.succ.val, by omega⟩))).val *
            2 ^ x.succ.val) = 2 * bitsVal
          (fun j : Fin K ↦ β (optWireOrZero wZero (rest.get ⟨j.val, by omega⟩))) := by
        unfold bitsVal
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun _ _ ↦ ?_
        simp only [Fin.val_succ, pow_succ', List.get_eq_getElem, List.getElem_cons_succ]
        ring
      rw [htail, hstep]
      simp only [Fin.val_zero, _root_.pow_zero, mul_one, List.get_eq_getElem,
        List.getElem_cons_zero, optWireOrZero_val wZero ow β hz]
      rfl
theorem wireListSum_congr {ws : List (Wire n)} {β₁ β₂ : BitAssignment n}
    (hag : ∀ w ∈ ws, β₁ w = β₂ w) : wireListSum ws β₁ = wireListSum ws β₂ := by
  induction ws with
  | nil => rfl
  | cons w _ ih =>
      rw [wireListSum_cons, wireListSum_cons, hag w (by simp),
        ih fun x hx ↦ hag x (by simp [hx])]
theorem weightedOptWiresVal_congr : ∀ {sw : List (Option (Wire n))} {β₁ β₂ : BitAssignment n},
    (∀ ow ∈ sw, ∀ w, ow = some w → β₁ w = β₂ w) →
      weightedOptWiresVal sw β₁ = weightedOptWiresVal sw β₂
  | [], _, _, _ => rfl
  | none :: _, _, _, hag => by
      rw [weightedOptWiresVal, weightedOptWiresVal, optBitVal, optBitVal,
        weightedOptWiresVal_congr fun ow how w hw ↦ hag ow (by simp [how]) w hw]
  | some w :: _, _, _, hag => by
      rw [weightedOptWiresVal, weightedOptWiresVal, optBitVal, optBitVal,
        hag (some w) (by simp) w rfl,
        weightedOptWiresVal_congr fun ow how u hu ↦ hag ow (by simp [how]) u hu]
theorem head_add_wireListSum_tail {L : ℕ} (hL : 1 ≤ L)
    (f : Fin L → Wire n) (δ : BitAssignment n) :
    (δ (f ⟨0, by omega⟩)).val +
      wireListSum (finMapList (fun i : Fin (L - 1) ↦ f ⟨i.val + 1, by omega⟩)) δ =
    ∑ l : Fin L, (δ (f l)).val := by
  rcases Nat.exists_eq_succ_of_ne_zero (by omega : L ≠ 0) with ⟨L', rfl⟩
  rw [wireListSum_finMapList, Fin.sum_univ_succ]
  rfl
end BatchEngines
end Section2APart1Batches
section Section2BBridge
open Operator Matrix QProg Circuit _root_.DynamicCircuit DynCircuitExt
open KaratsubaQft64Matrix
open DyadicQft64Engine
open PosMomSelectDynamic
open SpecsAux.DyadicSubgridToeplitz128 (NyqGrid3D64 NyqParity3D)
open scoped Matrix BigOperators
theorem disjoint_block_sep {d o₁ l₁ o₂ l₂ : ℕ} {h₁ : o₁ + l₁ ≤ d} {h₂ : o₂ + l₂ ≤ d}
    (hsep : o₁ + l₁ ≤ o₂ ∨ o₂ + l₂ ≤ o₁) :
    (QRegister.block o₁ l₁ h₁ : QRegister l₁ d).DisjointWires
    (QRegister.block o₂ l₂ h₂ : QRegister l₂ d) := by
  rw [QRegExt.disjointWires_iff_disjoint_image, Finset.disjoint_left]
  intro w hw₁ hw₂
  rcases (QRegister.mem_image _ _).mp hw₁ with ⟨i, rfl⟩
  rcases (QRegister.mem_image _ _).mp hw₂ with ⟨j, hj⟩
  have hv : o₁ + i.val = o₂ + j.val := congrArg Fin.val hj.symm
  omega
theorem disjoint_concat_left {m₁ m₂ m₃ d : ℕ} {r₁ : QRegister m₁ d} {r₂ : QRegister m₂ d}
    {r₃ : QRegister m₃ d} (h₁₂ : r₁.DisjointWires r₂) (h₁₃ : r₁.DisjointWires r₃)
    (h₂₃ : r₂.DisjointWires r₃) : (r₁.concat r₂ h₁₂).DisjointWires r₃ := by
  rw [QRegExt.disjointWires_iff_disjoint_image, Finset.disjoint_left] at h₁₃ h₂₃ ⊢
  intro w hw₁₂
  rcases (QRegister.mem_image _ _).mp hw₁₂ with ⟨idx, rfl⟩
  refine Fin.addCases (fun i hw₃ ↦ ?_) (fun j hw₃ ↦ ?_) idx
  · rw [QRegister.concat_apply_left] at hw₃
    exact h₁₃ ((QRegister.mem_image r₁ _).mpr ⟨i, rfl⟩) hw₃
  · rw [QRegister.concat_apply_right] at hw₃
    exact h₂₃ ((QRegister.mem_image r₂ _).mpr ⟨j, rfl⟩) hw₃
noncomputable def qft64OffsetUnitary1D (b : Fin 2) : Unitary 64 := wireHadamard6 0 *
    (stageDiag6 1 * wireHadamard6 1) * (stageDiag6 2 * wireHadamard6 2) *
    (stageDiag6 3 * wireHadamard6 3) * (stageDiag6 4 * wireHadamard6 4) *
    (stageDiag6 5 * wireHadamard6 5) * preDiag6 b * bit5Flip6
@[simp] theorem qft64OffsetUnitary1D_val (b : Fin 2) :
    (qft64OffsetUnitary1D b).1 = karatsubaOffsetUnitary128 b :=
  sixStageKaratsuba64_offset_eq_offsetUnitary b
noncomputable def qft64OffsetUnitary3D (b : NyqParity3D) : Unitary (2 ^ 18) :=
  (QRegister.block 0 6 (by decide) : QRegister 6 18).embedUnitary (qft64OffsetUnitary1D (b 0)) *
    (QRegister.block 6 6 (by decide) : QRegister 6 18).embedUnitary
      (qft64OffsetUnitary1D (b 1)) *
    (QRegister.block 12 6 (by decide) : QRegister 6 18).embedUnitary
      (qft64OffsetUnitary1D (b 2))
def u18GridEquiv : Fin (2 ^ 18) ≃ NyqGrid3D64 where
  toFun u := fun w ↦ ⟨(u.val / 2 ^ (6 * w.val)) % 64, by omega⟩
  invFun g := ⟨(g 0).val + 64 * (g 1).val + 4096 * (g 2).val, by
    have h0 := (g 0).isLt; have h1 := (g 1).isLt; have h2 := (g 2).isLt; omega⟩
  left_inv u := by
    ext
    have hu := u.isLt
    change (u.val / 1) % 64 + 64 * ((u.val / 64) % 64) + 4096 * ((u.val / 4096) % 64) = u.val
    omega
  right_inv g := by
    ext w
    have h0 := (g 0).isLt; have h1 := (g 1).isLt; have h2 := (g 2).isLt
    fin_cases w <;> simp <;> omega
theorem block6_extractIndex_u18 (w : Fin 3) (h : 6 * w.val + 6 ≤ 18) (u : Fin (2 ^ 18)) :
    (QRegister.block (6 * w.val) 6 h).extractIndex u = u18GridEquiv u w := by
  apply Fin.ext
  have hbits : ∀ r : Fin 6, (basisBits 6 ((QRegister.block (6 * w.val) 6 h).extractIndex u)
      r).val = (basisBits 6 (u18GridEquiv u w) r).val := by
    intro r
    have hbw : ((QRegister.block (6 * w.val) 6 h : QRegister 6 18) r).val = 6 * w.val + r.val := rfl
    rw [QRegister.basisBits_extractIndex, basisBits_eq_div_mod, basisBits_eq_div_mod, hbw]
    simp only [ZMod.val_natCast_of_lt (Nat.mod_lt _ (by decide : 0 < 2)), u18GridEquiv,
      Equiv.coe_fn_mk]
    have hu := u.isLt
    have hr := r.isLt
    fin_cases w <;> fin_cases r <;> norm_num <;> omega
  have heq : basisBits 6 ((QRegister.block (6 * w.val) 6 h).extractIndex u) =
      basisBits 6 (u18GridEquiv u w) := by
    funext r
    exact ZMod.val_injective 2 (hbits r)
  exact congrArg Fin.val ((basisBitsEquiv 6).injective heq)
theorem u18_eq_of_blocks_agree {x y : Fin (2 ^ 18)} (h0 : (QRegister.block 0 6 (by decide) :
    QRegister 6 18).extractIndex x = (QRegister.block 0 6 (by decide) : QRegister 6
    18).extractIndex y) (h1 : (QRegister.block 6 6 (by decide) : QRegister 6 18).extractIndex
    x = (QRegister.block 6 6 (by decide) : QRegister 6 18).extractIndex y) (h2 :
    (QRegister.block 12 6 (by decide) : QRegister 6 18).extractIndex x = (QRegister.block 12 6
    (by decide) : QRegister 6 18).extractIndex y) : x = y := by
  apply u18GridEquiv.injective
  funext w
  fin_cases w <;> dsimp only
  · exact (block6_extractIndex_u18 0 (by decide) x).symm.trans
      (h0.trans (block6_extractIndex_u18 0 (by decide) y))
  · exact (block6_extractIndex_u18 1 (by decide) x).symm.trans
      (h1.trans (block6_extractIndex_u18 1 (by decide) y))
  · exact (block6_extractIndex_u18 2 (by decide) x).symm.trans
      (h2.trans (block6_extractIndex_u18 2 (by decide) y))
theorem extractIndex_eq_of_disjoint_embedMatrix {m₁ m₂ d : ℕ} (r₁ : QRegister m₁ d)
    (r₂ : QRegister m₂ d) (hdisj : r₁.DisjointWires r₂) (A : Operator (2 ^ m₁))
    {x y : Fin (2 ^ d)} (hne : (r₁.embedMatrix A) x y ≠ 0) : r₂.extractIndex x =
    r₂.extractIndex y := by
  rw [QRegister.embedMatrix_apply] at hne
  by_cases hEnv : (r₁.basisSplitEquiv x).2 = (r₁.basisSplitEquiv y).2
  · rw [← (basisBitsEquiv m₂).apply_eq_iff_eq]
    funext idx
    change basisBits m₂ (r₂.extractIndex x) idx = basisBits m₂ (r₂.extractIndex y) idx
    rw [r₂.basisBits_extractIndex, r₂.basisBits_extractIndex]
    exact (r₁.basisSplit_environment_eq_iff x y).mp hEnv (r₂ idx)
      fun hm ↦ Set.disjoint_left.mp hdisj hm ⟨idx, rfl⟩
  · simp [hEnv] at hne
theorem mul_embedMatrix_of_extract_preserved {m d : ℕ} (X : Operator (2 ^ d))
    (r : QRegister m d) (A : Operator (2 ^ m)) (hX : ∀ x y : Fin (2 ^ d), X x y ≠ 0 →
    r.extractIndex x = r.extractIndex y) (z u : Fin (2 ^ d)) : (X * r.embedMatrix A) z u = X z
    (r.replaceIndex u (r.extractIndex z)) * A (r.extractIndex z) (r.extractIndex u) := by
  rw [Matrix.mul_apply]
  let y₀ : Fin (2 ^ d) := r.replaceIndex u (r.extractIndex z)
  have hy₀_env : (r.basisSplitEquiv y₀).2 = (r.basisSplitEquiv u).2 :=
    (r.basisSplit_environment_eq_iff y₀ u).mpr fun w hw ↦
      r.basisBits_replaceIndex_of_not_mem u (r.extractIndex z) w hw
  have hy₀_ext : r.extractIndex y₀ = r.extractIndex z := r.extractIndex_replaceIndex u _
  rw [Finset.sum_eq_single y₀]
  · simp only [QRegister.embedMatrix_apply, hy₀_env, ite_true, mul_one, hy₀_ext, y₀]
  · intro y _ hne
    by_cases hEnv : (r.basisSplitEquiv y).2 = (r.basisSplitEquiv u).2
    · by_cases hXzy : X z y = 0
      · simp [hXzy]
      · refine absurd (r.basisSplitEquiv.injective (Prod.ext ?_ (hEnv.trans hy₀_env.symm))) hne
        rw [QRegister.basisSplitEquiv_apply_fst, QRegister.basisSplitEquiv_apply_fst,
          ← hX z y hXzy, hy₀_ext]
    · simp [QRegister.embedMatrix_apply, hEnv]
  · exact fun hm ↦ absurd (Finset.mem_univ y₀) hm
theorem extractIndex_replaceIndex_of_disjoint {m₁ m₂ d : ℕ} (r₁ : QRegister m₁ d)
    (r₂ : QRegister m₂ d) (hdisj : r₁.DisjointWires r₂) (u : Fin (2 ^ d)) (k : Fin (2 ^ m₁)) :
    r₂.extractIndex (r₁.replaceIndex u k) = r₂.extractIndex u := by
  rw [← (basisBitsEquiv m₂).apply_eq_iff_eq]
  funext idx
  change basisBits m₂ (r₂.extractIndex (r₁.replaceIndex u k)) idx =
    basisBits m₂ (r₂.extractIndex u) idx
  rw [r₂.basisBits_extractIndex, r₂.basisBits_extractIndex]
  exact r₁.basisBits_replaceIndex_of_not_mem u k (r₂ idx)
    fun hm ↦ Set.disjoint_left.mp hdisj hm ⟨idx, rfl⟩
theorem qft64OffsetUnitary3D_apply (b : NyqParity3D) (z u : Fin (2 ^ 18)) :
    (qft64OffsetUnitary3D b).1 z u =
      ∏ w : Fin 3, karatsubaOffsetUnitary128 (b w) (u18GridEquiv z w) (u18GridEquiv u w) := by
  let r0 : QRegister 6 18 := QRegister.block 0 6 (by decide)
  let r1 : QRegister 6 18 := QRegister.block 6 6 (by decide)
  let r2 : QRegister 6 18 := QRegister.block 12 6 (by decide)
  have hd01 : r0.DisjointWires r1 := disjoint_block_sep (by omega)
  have hd02 : r0.DisjointWires r2 := disjoint_block_sep (by omega)
  have hd12 : r1.DisjointWires r2 := disjoint_block_sep (by omega)
  rw [show (qft64OffsetUnitary3D b).1 z u = ((r0.embedMatrix (karatsubaOffsetUnitary128 (b 0)) *
      r1.embedMatrix (karatsubaOffsetUnitary128 (b 1))) *
      r2.embedMatrix (karatsubaOffsetUnitary128 (b 2))) z u by
    simp only [qft64OffsetUnitary3D, Submonoid.coe_mul, QRegister.embedUnitary_val,
      qft64OffsetUnitary1D_val, r0, r1, r2]]
  rw [mul_embedMatrix_of_extract_preserved _ r2 _ (fun x y hxy ↦ by
      rw [Matrix.mul_apply] at hxy
      obtain ⟨t, _, ht⟩ := Finset.exists_ne_zero_of_sum_ne_zero hxy
      exact (extractIndex_eq_of_disjoint_embedMatrix r0 r2 hd02 _
        (left_ne_zero_of_mul ht)).trans
        (extractIndex_eq_of_disjoint_embedMatrix r1 r2 hd12 _ (right_ne_zero_of_mul ht))) z u,
    mul_embedMatrix_of_extract_preserved _ r1 _
      (fun _ _ ↦ extractIndex_eq_of_disjoint_embedMatrix r0 r1 hd01 _)]
  let u' := r1.replaceIndex (r2.replaceIndex u (r2.extractIndex z)) (r1.extractIndex z)
  have hao0 : (r0.basisSplitEquiv z).2 = (r0.basisSplitEquiv u').2 :=
    (r0.basisSplit_environment_eq_iff z u').mpr fun w hw ↦ by
      conv_lhs => rw [u18_eq_of_blocks_agree (r0.extractIndex_replaceIndex u' _).symm
        ((extractIndex_replaceIndex_of_disjoint r0 r1 hd01 _ _).trans
          (r1.extractIndex_replaceIndex _ _)).symm
        ((extractIndex_replaceIndex_of_disjoint r0 r2 hd02 _ _).trans
          ((extractIndex_replaceIndex_of_disjoint r1 r2 hd12 _ _).trans
            (r2.extractIndex_replaceIndex _ _))).symm]
      exact r0.basisBits_replaceIndex_of_not_mem u' (r0.extractIndex z) w hw
  simp only [QRegister.embedMatrix_apply, hao0, ite_true, mul_one, u',
    extractIndex_replaceIndex_of_disjoint r1 r0 hd01.symm,
    extractIndex_replaceIndex_of_disjoint r2 r0 hd02.symm,
    extractIndex_replaceIndex_of_disjoint r2 r1 hd12.symm]
  rw [Fin.prod_univ_three,
    show r0.extractIndex z = u18GridEquiv z 0 from block6_extractIndex_u18 0 (by decide) z,
    show r0.extractIndex u = u18GridEquiv u 0 from block6_extractIndex_u18 0 (by decide) u,
    show r1.extractIndex z = u18GridEquiv z 1 from block6_extractIndex_u18 1 (by decide) z,
    show r1.extractIndex u = u18GridEquiv u 1 from block6_extractIndex_u18 1 (by decide) u,
    show r2.extractIndex z = u18GridEquiv z 2 from block6_extractIndex_u18 2 (by decide) z,
    show r2.extractIndex u = u18GridEquiv u 2 from block6_extractIndex_u18 2 (by decide) u]
def axisCosetIdx (a : Fin 654) : Fin 3 := ⟨a.val % 3, Nat.mod_lt _ (by decide)⟩
def rAxis654 (a : Fin 654) : QRegister 6 (3924 + 3) := QRegister.block (6 * a.val) 6 (by omega)
def rElec18In654 (i : Fin 218) : QRegister 18 (3924 + 3) :=
  QRegister.block (18 * i.val) 18 (by omega)
def rCoset3In654 : QRegister 3 (3924 + 3) := QRegister.block 3924 3 (by decide)
theorem rAxis654_disjoint {a₁ a₂ : Fin 654} (hne : a₁ ≠ a₂) :
    (rAxis654 a₁).DisjointWires (rAxis654 a₂) := by
  have hv : a₁.val ≠ a₂.val := fun h ↦ hne (Fin.ext h)
  exact disjoint_block_sep (by omega)
theorem rAxis654_disjoint_rCoset3In654 (a : Fin 654) :
    (rAxis654 a).DisjointWires rCoset3In654 := disjoint_block_sep (by omega)
noncomputable def bit5Flip654 : Unitary (2 ^ (3924 + 3)) :=
  (List.ofFn fun a : Fin 654 ↦ (rAxis654 a).embedUnitary bit5Flip6).prod
noncomputable def preDiag654 : Unitary (2 ^ (3924 + 3)) :=
  DyadicQft64.dyadicDiagUnitary (3924 + 3) 7 fun γ ↦ ∑ a : Fin 654, karatsubaInExp128
    ⟨(γ ⟨3924 + a.val % 3, by omega⟩).val, ZMod.val_lt _⟩
    ((basisBitsEquiv 6).symm fun r : Fin 6 ↦ γ ⟨6 * a.val + r.val, by omega⟩)
noncomputable def stageH654 (kf : Fin 6) : Unitary (2 ^ (3924 + 3)) :=
  (List.ofFn fun a : Fin 654 ↦ (rAxis654 a).embedUnitary (wireHadamard6 kf)).prod
noncomputable def stageD654 (kf : Fin 6) : Unitary (2 ^ (3924 + 3)) :=
  (List.ofFn fun a : Fin 654 ↦ (rAxis654 a).embedUnitary (stageDiag6 kf)).prod
noncomputable def qft64Ideal654Unitary : Unitary (2 ^ (3924 + 3)) := stageH654 0 *
    (stageD654 1 * stageH654 1) * (stageD654 2 * stageH654 2) * (stageD654 3 * stageH654 3) *
    (stageD654 4 * stageH654 4) * (stageD654 5 * stageH654 5) * preDiag654 * bit5Flip654
theorem submonoid_coe_list_prod {K : ℕ} :
    ∀ l : List (Unitary K), (l.prod : Unitary K).1 = (l.map Subtype.val).prod
  | [] => rfl
  | _ :: s => by simp [submonoid_coe_list_prod s]
theorem prod_ofFn_diagonal {K : ℕ} : ∀ {M : ℕ} (f : Fin M → Fin K → ℂ),
    (List.ofFn fun a : Fin M ↦ Matrix.diagonal (f a)).prod =
      Matrix.diagonal fun x : Fin K ↦ (List.ofFn fun a : Fin M ↦ f a x).prod
  | 0, _ => by simp [Matrix.diagonal_one]
  | _ + 1, _ => by simp [List.ofFn_succ, prod_ofFn_diagonal, Matrix.diagonal_mul_diagonal]
theorem prod_ofFn_omega128 : ∀ {M : ℕ} (f : Fin M → ℤ),
    (List.ofFn fun a : Fin M ↦ omega128 (f a)).prod = omega128 (∑ a : Fin M, f a)
  | 0, _ => by simp [omega128_zero]
  | _ + 1, _ => by simp [List.ofFn_succ, prod_ofFn_omega128, Fin.sum_univ_succ, ← omega128_add]
theorem list_prod_comm_of_all {G : Type*} [Monoid G] (l : List G) (x : G)
    (hcomm : ∀ a ∈ l, a * x = x * a) : l.prod * x = x * l.prod := by
  induction l with
  | nil => simp
  | cons a s ih =>
      simp only [List.prod_cons, ← mul_assoc, ← hcomm a List.mem_cons_self]
      rw [mul_assoc, ih fun b hb ↦ hcomm b (List.mem_cons_of_mem a hb), ← mul_assoc]
theorem prod_ofFn_embedUnitary_mul {M d N : ℕ} (r : Fin M → QRegister d N)
    (hdisj : ∀ i j : Fin M, i ≠ j → (r i).DisjointWires (r j)) (A B : Fin M → Unitary (2 ^ d))
    : (List.ofFn fun i : Fin M ↦ (r i).embedUnitary (A i)).prod *
    (List.ofFn fun i : Fin M ↦ (r i).embedUnitary (B i)).prod =
    (List.ofFn fun i : Fin M ↦ (r i).embedUnitary (A i * B i)).prod := by
  induction M with
  | zero => simp
  | succ M ih =>
      simp only [List.ofFn_succ, List.prod_cons]
      have hcomm : (List.ofFn fun i : Fin M ↦ (r i.succ).embedUnitary (A i.succ)).prod *
          (r 0).embedUnitary (B 0) = (r 0).embedUnitary (B 0) *
          (List.ofFn fun i : Fin M ↦ (r i.succ).embedUnitary (A i.succ)).prod :=
        list_prod_comm_of_all _ _ fun x hx ↦ by
          rcases List.mem_ofFn.mp hx with ⟨i, rfl⟩
          exact Subtype.ext ((r i.succ).embedMatrix_comm_of_disjoint (r 0)
            (hdisj i.succ 0 (Fin.succ_ne_zero i)) _ _)
      rw [mul_assoc, ← mul_assoc _ ((r 0).embedUnitary (B 0)), hcomm, mul_assoc, ← mul_assoc,
        ← (r 0).embedUnitary_mul, ih (fun i ↦ r i.succ)
          (fun i j hij ↦ hdisj i.succ j.succ (Fin.succ_inj.not.mpr hij))
          (fun i ↦ A i.succ) (fun i ↦ B i.succ)]
def nyqParity3DEquivFin8 : NyqParity3D ≃ Fin 8 where
  toFun b := (basisBitsEquiv 3).symm fun w : Fin 3 ↦ ((b w).val : ZMod 2)
  invFun o := fun w ↦ ⟨(basisBits 3 o w).val, ZMod.val_lt (basisBits 3 o w)⟩
  left_inv b := funext fun w ↦ Fin.ext <| by
    have h1 := congrFun ((basisBitsEquiv 3).apply_symm_apply
      fun w' : Fin 3 ↦ ((b w').val : ZMod 2)) w
    change (basisBits 3 ((basisBitsEquiv 3).symm _) w).val = (b w).val
    change basisBits 3 ((basisBitsEquiv 3).symm _) w = ((b w).val : ZMod 2) at h1
    rw [h1, ZMod.val_natCast_of_lt (b w).isLt]
  right_inv o := (basisBitsEquiv 3).injective <| by
    change (basisBitsEquiv 3) ((basisBitsEquiv 3).symm _) = basisBits 3 o
    rw [(basisBitsEquiv 3).apply_symm_apply]
    exact funext fun w ↦ ZMod.natCast_zmod_val (basisBits 3 o w)
theorem list_prod_comm_proj {K : ℕ} (l : List (Unitary K)) (P : Operator K)
    (hcomm : ∀ u ∈ l, u.1 * P = P * u.1) : (l.prod).1 * P = P * (l.prod).1 := by
  rw [submonoid_coe_list_prod]
  exact list_prod_comm_of_all _ P fun A hA ↦ by
    rcases List.mem_map.mp hA with ⟨u, hu, rfl⟩
    exact hcomm u hu
theorem comm_mul_op {K : ℕ} {P : Operator K} {U V : Unitary K} (hU : U.1 * P = P * U.1)
    (hV : V.1 * P = P * V.1) : (U * V).1 * P = P * (U * V).1 := by
  change (U.1 * V.1) * P = P * (U.1 * V.1)
  rw [Matrix.mul_assoc, hV, ← Matrix.mul_assoc, hU, Matrix.mul_assoc]
noncomputable def axisProd654 (A : Fin 654 → Unitary 64) : Unitary (2 ^ (3924 + 3)) :=
  (List.ofFn fun a : Fin 654 ↦ (rAxis654 a).embedUnitary (A a)).prod
theorem axisProd654_mul (A B : Fin 654 → Unitary 64) :
    axisProd654 A * axisProd654 B = axisProd654 (fun a ↦ A a * B a) :=
  prod_ofFn_embedUnitary_mul rAxis654 (fun _ _ h ↦ rAxis654_disjoint h) A B
theorem stageH654_eq_axisProd (k : Fin 6) :
    stageH654 k = axisProd654 (fun _ ↦ wireHadamard6 k) := rfl
theorem stageD654_eq_axisProd (m : Fin 6) :
    stageD654 m = axisProd654 (fun _ ↦ stageDiag6 m) := rfl
theorem bit5Flip654_eq_axisProd : bit5Flip654 = axisProd654 (fun _ ↦ bit5Flip6) := rfl
theorem qft64Ideal654Unitary_comm_cosetProj (o : Fin 8) :
    qft64Ideal654Unitary.1 * rCoset3In654.basisOutcomeProjector o =
      rCoset3In654.basisOutcomeProjector o * qft64Ideal654Unitary.1 := by
  let P := rCoset3In654.basisOutcomeProjector o
  have hax (f : Fin 654 → Unitary 64) : (axisProd654 f).1 * P = P * (axisProd654 f).1 :=
    list_prod_comm_proj _ P fun u hu ↦ by
      rcases List.mem_ofFn.mp hu with ⟨a, rfl⟩
      exact (QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint (rAxis654 a))
        rCoset3In654 (rAxis654_disjoint_rCoset3In654 a) _ o
  have hdh (k : Fin 6) :
      (stageD654 k * stageH654 k).1 * P = P * (stageD654 k * stageH654 k).1 :=
    comm_mul_op (hax _) (hax _)
  have hpre : preDiag654.1 * P = P * preDiag654.1 := by
    dsimp only [P]
    rw [preDiag654, DyadicQft64.dyadicDiagUnitary, QRegister.basisOutcomeProjector_eq_diagonal,
      Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    exact congrArg Matrix.diagonal (funext fun _ ↦ mul_comm _ _)
  exact comm_mul_op (comm_mul_op (comm_mul_op (comm_mul_op (comm_mul_op (comm_mul_op
    (comm_mul_op (hax _) (hdh 1)) (hdh 2)) (hdh 3)) (hdh 4)) (hdh 5)) hpre) (hax _)
def prefixProd {G : Type*} [Monoid G] : ∀ (m : ℕ), (Fin m → G) → G
  | 0, _ => 1
  | m + 1, f => prefixProd m (fun i ↦ f i.castSucc) * f (Fin.last m)
theorem ofFn_eq_snoc {α : Type*} :
    ∀ (m : ℕ) (f : Fin (m + 1) → α),
      List.ofFn f = List.ofFn (fun i : Fin m ↦ f i.castSucc) ++ [f (Fin.last m)]
  | 0, _ => rfl
  | m + 1, f => by
      conv_lhs => rw [List.ofFn_succ]
      conv_rhs => rw [List.ofFn_succ]
      simp only [ofFn_eq_snoc m (fun i ↦ f i.succ),
        List.cons_append, Fin.castSucc_zero, Fin.castSucc_succ, Fin.succ_last]
theorem prod_ofFn_eq_prefixProd {G : Type*} [Monoid G] :
    ∀ (m : ℕ) (f : Fin m → G), (List.ofFn f).prod = prefixProd m f
  | 0, _ => rfl
  | m + 1, f => by
      rw [ofFn_eq_snoc, List.prod_append, List.prod_singleton, prod_ofFn_eq_prefixProd m]
      rfl
theorem prefixProd_group3 {G : Type*} [Monoid G] :
    ∀ (m : ℕ) (f : Fin (3 * m) → G),
      prefixProd (3 * m) f =
        prefixProd m (fun i : Fin m ↦
          f ⟨3 * i.val, by omega⟩ * f ⟨3 * i.val + 1, by omega⟩ * f ⟨3 * i.val + 2, by omega⟩)
  | 0, _ => rfl
  | m + 1, f => by
      change ((prefixProd (3 * m) fun i ↦ f ⟨i.val, by omega⟩) * f ⟨3 * m, by omega⟩) *
            f ⟨3 * m + 1, by omega⟩ * f ⟨3 * m + 2, by omega⟩ =
          prefixProd m (fun i : Fin m ↦
            f ⟨3 * i.val, by omega⟩ * f ⟨3 * i.val + 1, by omega⟩ *
              f ⟨3 * i.val + 2, by omega⟩) *
            (f ⟨3 * m, by omega⟩ * f ⟨3 * m + 1, by omega⟩ * f ⟨3 * m + 2, by omega⟩)
      rw [prefixProd_group3 m (fun i ↦ f ⟨i.val, by omega⟩)]
      simp only [mul_assoc]
theorem prod_ofFn_group3 {G : Type*} [Monoid G] (m : ℕ) (f : Fin (3 * m) → G) :
    (List.ofFn f).prod =
      (List.ofFn fun i : Fin m ↦
        f ⟨3 * i.val, by omega⟩ * f ⟨3 * i.val + 1, by omega⟩ *
          f ⟨3 * i.val + 2, by omega⟩).prod := by
  rw [prod_ofFn_eq_prefixProd, prod_ofFn_eq_prefixProd]
  exact prefixProd_group3 m f
theorem qft64Ideal654Unitary_mul_cosetProj_eq_elec3DProd (b : NyqParity3D) :
    qft64Ideal654Unitary.1 * rCoset3In654.basisOutcomeProjector (nyqParity3DEquivFin8 b) =
    ((List.ofFn fun i : Fin 218 ↦ (rElec18In654 i).embedUnitary (qft64OffsetUnitary3D
    b)).prod).1 * rCoset3In654.basisOutcomeProjector (nyqParity3DEquivFin8 b) := by
  let P := rCoset3In654.basisOutcomeProjector (nyqParity3DEquivFin8 b)
  let preFixed : Unitary (2 ^ (3924 + 3)) := axisProd654 (fun a ↦ preDiag6 (b (axisCosetIdx a)))
  have hpre_proj : preDiag654.1 * P = preFixed.1 * P := by
    dsimp only [P, preFixed, axisProd654]
    rw [submonoid_coe_list_prod, show ((List.ofFn fun a : Fin 654 ↦
          (rAxis654 a).embedUnitary (preDiag6 (b (axisCosetIdx a)))).map Subtype.val) =
        List.ofFn fun a : Fin 654 ↦ Matrix.diagonal fun x : Fin (2 ^ (3924 + 3)) ↦
          omega128 (karatsubaInExp128 (b (axisCosetIdx a)) ((rAxis654 a).extractIndex x)) by
      rw [List.map_ofFn]
      exact congrArg List.ofFn (funext fun a ↦
        PosMomSelectDynamic.embedMatrix_diagonal (rAxis654 a) _),
      prod_ofFn_diagonal, preDiag654, DyadicQft64.dyadicDiagUnitary,
      QRegister.basisOutcomeProjector_eq_diagonal, Matrix.diagonal_mul_diagonal,
      Matrix.diagonal_mul_diagonal]
    refine congrArg Matrix.diagonal (funext fun x ↦ ?_)
    by_cases ho : rCoset3In654.extractIndex x = nyqParity3DEquivFin8 b
    · simp only [ho, ite_true, mul_one]
      rw [prod_ofFn_omega128, ← DyadicQft64.dyadicTurn_eq_omega128]
      refine congrArg (DyadicQft64.dyadicTurn 7) (Finset.sum_congr rfl fun a _ ↦ ?_)
      have hb_eq : (⟨(basisBits (3924 + 3) x ⟨3924 + a.val % 3, by omega⟩).val,
          ZMod.val_lt _⟩ : Fin 2) = b (axisCosetIdx a) := Fin.ext <| by
        change (basisBits (3924 + 3) x ⟨3924 + a.val % 3, by omega⟩).val = _
        rw [show basisBits (3924 + 3) x ⟨3924 + a.val % 3, by omega⟩ =
            basisBits 3 (rCoset3In654.extractIndex x) (axisCosetIdx a) from
          (rCoset3In654.basisBits_extractIndex x (axisCosetIdx a)).symm, ho]
        exact congrArg Fin.val (congrFun (nyqParity3DEquivFin8.left_inv b) (axisCosetIdx a))
      rw [hb_eq, show ((basisBitsEquiv 6).symm fun r : Fin 6 ↦
          basisBits (3924 + 3) x ⟨6 * a.val + r.val, by omega⟩) = (rAxis654 a).extractIndex x from
        (basisBitsEquiv 6).apply_eq_iff_eq.mp (((basisBitsEquiv 6).apply_symm_apply _).trans
          (funext fun r ↦ ((rAxis654 a).basisBits_extractIndex x r).symm))]
    · simp only [ho, ite_false, mul_zero]
  have hflip_comm : bit5Flip654.1 * P = P * bit5Flip654.1 :=
    list_prod_comm_proj _ P fun u hu ↦ by
      rcases List.mem_ofFn.mp hu with ⟨a, rfl⟩
      exact (QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint (rAxis654 a))
        rCoset3In654 (rAxis654_disjoint_rCoset3In654 a) _ _
  have hswap : (preDiag654 * bit5Flip654).1 * P = (preFixed * bit5Flip654).1 * P := by
    change (preDiag654.1 * bit5Flip654.1) * P = (preFixed.1 * bit5Flip654.1) * P
    rw [Matrix.mul_assoc, hflip_comm, ← Matrix.mul_assoc, hpre_proj,
      Matrix.mul_assoc, ← hflip_comm, ← Matrix.mul_assoc]
  have hmerge : stageH654 0 * (stageD654 1 * stageH654 1) * (stageD654 2 * stageH654 2) *
      (stageD654 3 * stageH654 3) * (stageD654 4 * stageH654 4) * (stageD654 5 * stageH654 5) *
      preFixed * bit5Flip654 =
      axisProd654 (fun a ↦ qft64OffsetUnitary1D (b (axisCosetIdx a))) := by
    simp only [stageH654_eq_axisProd, stageD654_eq_axisProd, bit5Flip654_eq_axisProd, preFixed,
      axisProd654_mul]
    rfl
  have hgroup : axisProd654 (fun a ↦ qft64OffsetUnitary1D (b (axisCosetIdx a))) = (List.ofFn
      fun i : Fin 218 ↦ (rElec18In654 i).embedUnitary (qft64OffsetUnitary3D b)).prod := by
    change (List.ofFn fun a : Fin (3 * 218) ↦
      (rAxis654 a).embedUnitary (qft64OffsetUnitary1D (b (axisCosetIdx a)))).prod = _
    rw [prod_ofFn_group3 218]
    refine congrArg List.prod (congrArg List.ofFn (funext fun i ↦ ?_))
    have hr (o a : ℕ) (ha : a < 654) (ho : o + 6 ≤ 18) (heq : 18 * i.val + o = 6 * a) :
        (rElec18In654 i).compose (QRegister.block o 6 ho) = rAxis654 ⟨a, ha⟩ :=
      DyadicQft64WalkCircuitAlt.qreg_ext fun r ↦ Fin.ext <| by
        change 18 * i.val + (o + r.val) = 6 * a + r.val
        omega
    have hc (a : ℕ) (ha : a < 654) (w : Fin 3) (hw : a % 3 = w.val) :
        axisCosetIdx ⟨a, ha⟩ = w := Fin.ext hw
    rw [qft64OffsetUnitary3D, (rElec18In654 i).embedUnitary_mul,
      (rElec18In654 i).embedUnitary_mul, ← QRegister.embedUnitary_compose,
      ← QRegister.embedUnitary_compose, ← QRegister.embedUnitary_compose,
      hr 0 (3 * i.val) (by omega) (by decide) (by omega),
      hr 6 (3 * i.val + 1) (by omega) (by decide) (by omega),
      hr 12 (3 * i.val + 2) (by omega) (by decide) (by omega),
      hc (3 * i.val) (by omega) 0 (by omega),
      hc (3 * i.val + 1) (by omega) 1 (by omega),
      hc (3 * i.val + 2) (by omega) 2 (by omega)]
  rw [show qft64Ideal654Unitary.1 * P =
      (stageH654 0 * (stageD654 1 * stageH654 1) * (stageD654 2 * stageH654 2) *
        (stageD654 3 * stageH654 3) * (stageD654 4 * stageH654 4) *
        (stageD654 5 * stageH654 5)).1 * ((preDiag654 * bit5Flip654).1 * P) by
        simp only [qft64Ideal654Unitary, Submonoid.coe_mul, Matrix.mul_assoc],
    hswap, ← hgroup, ← hmerge]
  simp only [P, Submonoid.coe_mul, Matrix.mul_assoc]
abbrev kCore (mPayload : ℕ) : ℕ := 3954 + mPayload
abbrev kAct (mPayload : ℕ) : ℕ := 3993 + mPayload
def wSlot2 {K : ℕ} (hK : 3954 ≤ K) : Wire K := ⟨3950, by omega⟩
end Section2BBridge
section Section2APart2Assembly
open Real Operator Matrix QProg HermitianMat _root_.DynamicCircuit DynCircuitExt LocalClassicalPerm
open KaratsubaQft64Matrix
open DyadicQft64Engine
open DyadicQft64
open scoped Matrix ComplexOrder MatrixOrder Circuit.Notation BigOperators
theorem realizes_congr_slice {Var : Type} [Fintype Var] [DecidableEq Var] {k w m n : ℕ}
    [NeZero (2 ^ n)] {r₁ r₁' : QRegister k n} {rWork : QRegister m n} (hw : 0 + w ≤ m)
    (h₁ : r₁ = r₁') {u : Unitary (2 ^ k)} {d : DynamicCircuit Var n}
    (hd : RealizesEmbeddedUnitaryWithCleanWorkspace r₁ (rWork.slice 0 w hw) u d) :
    RealizesEmbeddedUnitaryWithCleanWorkspace r₁' rWork u d :=
  h₁ ▸ RealizesEmbeddedUnitaryWithCleanWorkspace.widenWorkspace
    (sel := QRegister.block 0 w hw) hd
theorem realizes_congr_slice2 {Var : Type} [Fintype Var] [DecidableEq Var] {k w m n : ℕ}
    [NeZero (2 ^ n)] {r₁ r₁' : QRegister k n} {r₂ : QRegister w n} {rWork : QRegister m n}
    (hw : 0 + w ≤ m) (h₁ : r₁ = r₁') (h₂ : r₂ = rWork.slice 0 w hw) {u : Unitary (2 ^ k)}
    {d : DynamicCircuit Var n} (hd : RealizesEmbeddedUnitaryWithCleanWorkspace r₁ r₂ u d) :
    RealizesEmbeddedUnitaryWithCleanWorkspace r₁' rWork u d := by
  subst h₁
  subst h₂
  exact RealizesEmbeddedUnitaryWithCleanWorkspace.widenWorkspace
    (sel := QRegister.block 0 w hw) hd
def rIdInCat : QRegister (3924 + 3) (3924 + 3 + 7) := QRegister.block 0 (3924 + 3) (by decide)
def rPGInCat : QRegister 7 (3924 + 3 + 7) := QRegister.block (3924 + 3) 7 (by decide)
theorem rIdOfCat_disjoint_rPGOfCat {n : ℕ} (rQftCat : QRegister (3924 + 3 + 7) n) :
    (rQftCat.compose rIdInCat).DisjointWires (rQftCat.compose rPGInCat) := by
  have hd : rIdInCat.DisjointWires rPGInCat := disjoint_block_sep (by decide)
  rw [QRegExt.disjointWires_iff_disjoint_image, Finset.disjoint_left] at hd ⊢
  rintro _ hw₁ hw₂
  rcases (QRegister.mem_image _ _).mp hw₁ with ⟨i, rfl⟩
  rcases (QRegister.mem_image _ _).mp hw₂ with ⟨j, hj⟩
  exact hd ((QRegister.mem_image _ _).mpr ⟨i, rfl⟩)
    ((QRegister.mem_image _ _).mpr ⟨j, (rQftCat.wires.injective hj.symm).symm⟩)
theorem rIdOfCat_concat_rPGOfCat {n : ℕ} (rQftCat : QRegister (3924 + 3 + 7) n) :
    (rQftCat.compose rIdInCat).concat (rQftCat.compose rPGInCat)
      (rIdOfCat_disjoint_rPGOfCat rQftCat) = rQftCat :=
  DyadicQft64WalkCircuitAlt.qreg_ext fun idx ↦ Fin.addCases
    (fun _ ↦ (QRegister.concat_apply_left ..).trans
      (congrArg rQftCat (Fin.ext (by simp [rIdInCat]))))
    (fun _ ↦ (QRegister.concat_apply_right ..).trans
      (congrArg rQftCat (Fin.ext (by simp [rPGInCat])))) idx
theorem concat_compose_rIdInCat {N : ℕ} (rId : QRegister (3924 + 3) N) (rPG : QRegister 7 N)
    (hdisj : rId.DisjointWires rPG) : (rId.concat rPG hdisj).compose rIdInCat = rId :=
  DyadicQft64WalkCircuitAlt.qreg_ext fun i ↦ by
    rw [QRegister.compose_apply,
      show rIdInCat i = Fin.castAdd 7 i from Fin.ext (by simp [rIdInCat]),
      QRegister.concat_apply_left]
theorem catModAddUnitary_congr_mod {kSys B : ℕ} (s₁ s₂ : BitAssignment kSys → ℕ)
    (hmod : ∀ γ : BitAssignment kSys, s₁ γ % 2 ^ B = s₂ γ % 2 ^ B) :
    catModAddUnitary kSys B s₁ = catModAddUnitary kSys B s₂ := by
  unfold catModAddUnitary catModAddPerm
  rw [show catModAddMidPerm kSys B s₁ = catModAddMidPerm kSys B s₂ from Equiv.ext fun ⟨γ, _⟩ ↦
    Prod.ext rfl (Fin.ext (by
      dsimp [catModAddMidPerm]
      rw [Nat.add_mod, hmod γ, ← Nat.add_mod]))]
theorem catModAddUnitary_mul_add {kSys B : ℕ} (s₁ s₂ : BitAssignment kSys → ℕ) :
    catModAddUnitary kSys B s₂ * catModAddUnitary kSys B s₁ =
      catModAddUnitary kSys B (fun γ ↦ s₁ γ + s₂ γ) :=
  Subtype.ext <| Matrix.ext fun row col ↦ by
  have hcomp : catModAddPerm kSys B s₂ (catModAddPerm kSys B s₁ col) =
      catModAddPerm kSys B (fun γ ↦ s₁ γ + s₂ γ) col := by
    dsimp [catModAddPerm, catModAddMidPerm]
    rw [(splitSysCatEquiv kSys B).apply_symm_apply]
    exact congrArg (splitSysCatEquiv kSys B).symm (Prod.ext rfl (Fin.ext (by
      dsimp
      rw [Nat.mod_add_mod, Nat.add_assoc])))
  have hmul : ((catModAddUnitary kSys B s₂ * catModAddUnitary kSys B s₁).1.mulVec
      (Pi.single col 1)) row = ((catModAddUnitary kSys B (fun γ ↦ s₁ γ + s₂ γ)).1.mulVec
      (Pi.single col 1)) row := by
    rw [Submonoid.coe_mul, ← Matrix.mulVec_mulVec]
    unfold catModAddUnitary
    rw [permutationUnitary_mulVec_single, permutationUnitary_mulVec_single,
      permutationUnitary_mulVec_single, hcomp]
  simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using hmul
theorem catModAddUnitary_zero_eq_one (kSys B : ℕ) :
    catModAddUnitary kSys B (fun _ ↦ 0) = 1 := by
  have hperm : catModAddPerm kSys B (fun _ ↦ 0) = Equiv.refl _ := Equiv.ext fun x ↦ by
    change (splitSysCatEquiv kSys B).symm (catModAddMidPerm kSys B (fun _ ↦ 0) _) = x
    rw [show catModAddMidPerm kSys B (fun _ ↦ 0) ((splitSysCatEquiv kSys B) x) =
        (splitSysCatEquiv kSys B) x from Prod.ext rfl (Fin.ext (by
      dsimp [catModAddMidPerm]
      exact Nat.mod_eq_of_lt (splitSysCatEquiv kSys B x).2.isLt)), Equiv.symm_apply_apply]
  unfold catModAddUnitary
  rw [hperm]
  refine Subtype.ext (Matrix.ext fun row col ↦ ?_)
  have hmul : ((permutationUnitary (Equiv.refl (Fin (2 ^ (kSys + B))))).1.mulVec
      (Pi.single col 1)) row =
      ((1 : Unitary (2 ^ (kSys + B))).1.mulVec (Pi.single col 1)) row := by
    rw [permutationUnitary_mulVec_single]
    by_cases hrc : row = col <;> simp [hrc]
  simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using hmul
noncomputable def liftDynamic {Var : Type} {m n : ℕ} (v : Var) (r : QRegister m n) :
    DynamicCircuit Unit m → DynamicCircuit Var n := dynMapReindex (fun σ _ ↦ σ v)
    (fun c ↦ .circuit (c.onRegister r)) (fun _ q ↦ .measure v (r.compose q))
theorem count_liftDynamic {Var : Type} {a m n : ℕ} (g : PrimitiveGate a)
    (v : Var) (r : QRegister m n) (d : DynamicCircuit Unit m) :
    (liftDynamic v r d).count g = d.count g := by
  induction d with
  | circuit _ => simp [liftDynamic, dynMapReindex]
  | measure _ _ => rfl
  | qIf _ dt df iht ihf =>
      change max ((liftDynamic v r dt).count g) ((liftDynamic v r df).count g) =
        max (dt.count g) (df.count g)
      rw [iht, ihf]
  | seq d₁ d₂ ih1 ih2 =>
      change (liftDynamic v r d₁).count g + (liftDynamic v r d₂).count g =
        d₁.count g + d₂.count g
      rw [ih1, ih2]
noncomputable def isoMat {m n : ℕ} (r : QRegister m n)
    (ψ : (r.Environment → ZMod 2) → ℂ) : Matrix (Fin (2 ^ n)) (Fin (2 ^ m)) ℂ :=
  fun g i ↦ if r.extractIndex g = i then ψ (r.basisSplitEquiv g).2 else 0
theorem extractIndex_basisSplit_symm {m n : ℕ} (r : QRegister m n) (k : Fin (2 ^ m))
    (e : r.Environment → ZMod 2) : r.extractIndex (r.basisSplitEquiv.symm (k, e)) = k :=
  (r.basisSplitEquiv_apply_fst _).symm.trans
    (congrArg Prod.fst (r.basisSplitEquiv.apply_symm_apply _))
theorem snd_basisSplit_symm {m n : ℕ} (r : QRegister m n)
    (k : Fin (2 ^ m)) (e : r.Environment → ZMod 2) :
    (r.basisSplitEquiv (r.basisSplitEquiv.symm (k, e))).2 = e :=
  congrArg Prod.snd (r.basisSplitEquiv.apply_symm_apply _)
theorem isoMat_conjTranspose_mul {m n : ℕ} (r : QRegister m n)
    (ψ : (r.Environment → ZMod 2) → ℂ) : (isoMat r ψ)ᴴ * isoMat r ψ = Matrix.diagonal fun _ :
    Fin (2 ^ m) ↦ ∑ e, star (ψ e) * ψ e := Matrix.ext fun i j ↦ by
  rw [Matrix.mul_apply, ← r.basisSplitEquiv.symm.sum_comp, Fintype.sum_prod_type]
  simp only [Matrix.conjTranspose_apply, isoMat, extractIndex_basisSplit_symm,
    snd_basisSplit_symm]
  by_cases hij : i = j
  · subst hij
    rw [Finset.sum_eq_single i (fun _ _ hk ↦ by simp [hk])
      (fun hm ↦ absurd (Finset.mem_univ i) hm)]
    simp
  · rw [Matrix.diagonal_apply_ne _ hij]
    exact Finset.sum_eq_zero fun k _ ↦ by by_cases hki : k = i <;> simp [hki, hij]
theorem embedMatrix_mul_isoMat {m n : ℕ} (r : QRegister m n)
    (ψ : (r.Environment → ZMod 2) → ℂ) (A : Matrix (Fin (2 ^ m)) (Fin (2 ^ m)) ℂ) :
    r.embedMatrix A * isoMat r ψ = isoMat r ψ * A := by
  ext g j
  rw [Matrix.mul_apply, Matrix.mul_apply, ← r.basisSplitEquiv.symm.sum_comp,
    Fintype.sum_prod_type]
  simp only [QRegister.embedMatrix_apply, isoMat, extractIndex_basisSplit_symm,
    snd_basisSplit_symm]
  rw [Finset.sum_eq_single j (fun _ _ hk ↦ by simp [hk])
    (fun hm ↦ absurd (Finset.mem_univ j) hm)]
  simp only [↓reduceIte]
  rw [Finset.sum_eq_single (r.basisSplitEquiv g).2 (fun _ _ he ↦ by simp [Ne.symm he])
      (fun hm ↦ absurd (Finset.mem_univ _) hm),
    Finset.sum_eq_single (r.extractIndex g) (fun _ _ hk ↦ by simp [Ne.symm hk])
      (fun hm ↦ absurd (Finset.mem_univ _) hm)]
  simp [mul_comm]
theorem isoMat_conj_embedMatrix {m n : ℕ} (r : QRegister m n)
    (ψ : (r.Environment → ZMod 2) → ℂ) (A B : Matrix (Fin (2 ^ m)) (Fin (2 ^ m)) ℂ)
    (X : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) : (isoMat r ψ)ᴴ *
    (r.embedMatrix A * X * r.embedMatrix B) * isoMat r ψ = A *
    ((isoMat r ψ)ᴴ * X * isoMat r ψ) * B := by
  have hc : (isoMat r ψ)ᴴ * r.embedMatrix A = A * (isoMat r ψ)ᴴ := by
    simpa only [conjTranspose_mul, conjTranspose_conjTranspose,
      QRegister.embedMatrix_conjTranspose]
      using congrArg conjTranspose (embedMatrix_mul_isoMat r ψ Aᴴ)
  calc (isoMat r ψ)ᴴ * (r.embedMatrix A * X * r.embedMatrix B) * isoMat r ψ
      = ((isoMat r ψ)ᴴ * r.embedMatrix A) * X * (r.embedMatrix B * isoMat r ψ) := by
          simp only [Matrix.mul_assoc]
    _ = (A * (isoMat r ψ)ᴴ) * X * (isoMat r ψ * B) := by rw [hc, embedMatrix_mul_isoMat]
    _ = A * ((isoMat r ψ)ᴴ * X * isoMat r ψ) * B := by simp only [Matrix.mul_assoc]
def IsoContraction {m n : ℕ} (r : QRegister m n) (ψ : (r.Environment → ZMod 2) → ℂ) : Prop :=
  ∃ c : ℝ, c ≤ 1 ∧ (∑ e, star (ψ e) * ψ e) = (c : ℂ)
noncomputable def pullObs {m n : ℕ} (r : QRegister m n) (ψ : (r.Environment → ZMod 2) → ℂ)
    (hc : IsoContraction r ψ) (M : Observable (Fin (2 ^ n))) : Observable (Fin (2 ^ m)) :=
  ⟨HermitianMat.conj (isoMat r ψ)ᴴ M.1, by
    rcases hc with ⟨c, hc1, hsum⟩
    refine ⟨M.1.conj_nonneg _ M.2.1,
      (HermitianMat.conj_mono M.2.2).trans (HermitianMat.le_iff.mpr ?_)⟩
    rw [HermitianMat.mat_sub, HermitianMat.mat_one, HermitianMat.conj_apply_mat,
      HermitianMat.mat_one, Matrix.mul_one, Matrix.conjTranspose_conjTranspose,
      isoMat_conjTranspose_mul, hsum, ← Matrix.diagonal_one, Matrix.diagonal_sub,
      Matrix.posSemidef_diagonal_iff]
    exact fun _ ↦ Complex.le_def.mpr ⟨by
      simp
      linarith, by simp⟩⟩
theorem pullObs_mat' {m n : ℕ} (r : QRegister m n) (ψ : (r.Environment → ZMod 2) → ℂ)
    (hc : IsoContraction r ψ) (M : Observable (Fin (2 ^ n))) : (pullObs r ψ hc M).1.mat =
    (isoMat r ψ)ᴴ * M.1.mat * isoMat r ψ := by
  change (HermitianMat.conj (isoMat r ψ)ᴴ M.1).mat = _
  rw [HermitianMat.conj_apply_mat, Matrix.conjTranspose_conjTranspose]
theorem pullObs_mat {m n : ℕ} (r : QRegister m n) (ψ : (r.Environment → ZMod 2) → ℂ)
    (hc : IsoContraction r ψ) (M : Observable (Fin (2 ^ n))) : (pullObs r ψ hc M).1.1 =
    (isoMat r ψ)ᴴ * M.1.1 * isoMat r ψ := pullObs_mat' r ψ hc M
theorem wp_liftDynamic_pull {Var : Type} [Finite Var] [DecidableEq Var] {m n : ℕ}
    [NeZero (2 ^ m)] [NeZero (2 ^ n)] (v : Var) (r : QRegister m n)
    (ψ : (r.Environment → ZMod 2) → ℂ) (hc : IsoContraction r ψ) : ∀
    (d : DynamicCircuit Unit m) (Θ : CQAssertionCompat Var (2 ^ n)) (σ : Store Var), pullObs r ψ hc
    (wp (liftDynamic v r d).compile Θ σ) = wp d.compile
    (fun τ ↦ pullObs r ψ hc (Θ (Function.update σ v (τ ())))) (fun _ ↦ σ v) := by
  intro d
  cases nonempty_fintype Var
  induction d with
  | circuit c =>
      intro Θ σ
      refine Subtype.ext (Subtype.ext ?_)
      rw [pullObs_mat, show liftDynamic v r (.circuit c) = .circuit (c.onRegister r) from rfl,
        DynamicCircuit.compile_circuit, DynamicCircuit.compile_circuit,
        DynCircuitExt.wp_circuit_compile_compat, DynCircuitExt.wp_circuit_compile_compat,
        wpQAssignCompat_apply_mat, wpQAssignCompat_apply_mat, Circuit.eval_onRegister,
        QRegister.embedUnitary_val, ← QRegister.embedMatrix_conjTranspose,
        Function.update_eq_self v σ, pullObs_mat]
      exact isoMat_conj_embedMatrix r ψ c.eval.1ᴴ c.eval.1 (Θ σ).1.1
  | measure u q =>
      intro Θ σ
      cases u
      have hwp_m {Var' : Type} [Fintype Var'] [DecidableEq Var'] {d : ℕ} [NeZero (2 ^ d)]
          (x : Var') (q' : QRegister 1 d) (θ : CQAssertionCompat Var' (2 ^ d)) (s : Store Var') :
          (wp (QProg.measureRegister x q') θ s).1.mat = ∑ o : Fin (2 ^ 1),
            (q'.basisOutcomeProjector o)ᴴ * (θ (Function.update s x (Int.ofNat o.val))).1.mat *
            q'.basisOutcomeProjector o := by
        simp only [QProg.measureRegister, wp_qMeasure_apply]
        rw [qMeasure_obs_map_coe, HermitianMat.mat_finset_sum]
        refine Finset.sum_congr rfl fun o _ ↦ ?_
        rw [qMeasure_outcome_herm_mat, CQAssertionCompat.subst_apply, Store.subst_eq_update]
        rfl
      have hdist (s : Finset (Fin (2 ^ 1)))
          (F : Fin (2 ^ 1) → Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) :
          ((isoMat r ψ)ᴴ * ∑ o ∈ s, F o) * isoMat r ψ =
            ∑ o ∈ s, ((isoMat r ψ)ᴴ * F o) * isoMat r ψ := by
        induction s using Finset.induction_on with
        | empty => simp
        | @insert a s ha ih => simp only [Finset.sum_insert ha, Matrix.mul_add, Matrix.add_mul, ih]
      refine Subtype.ext (HermitianMat.ext ?_)
      rw [pullObs_mat',
        show liftDynamic v r (.measure () q) = .measure v (r.compose q) from rfl,
        DynamicCircuit.compile_measure, DynamicCircuit.compile_measure, hwp_m, hwp_m,
        hdist Finset.univ]
      refine Finset.sum_congr rfl fun o _ ↦ ?_
      rw [Function.update_self, show (r.compose q).basisOutcomeProjector o =
          r.embedMatrix (q.basisOutcomeProjector o) from
          QRegister.embedMatrix_compose r q (compProj o),
        pullObs_mat', ← QRegister.embedMatrix_conjTranspose]
      exact isoMat_conj_embedMatrix r ψ (q.basisOutcomeProjector o)ᴴ
        (q.basisOutcomeProjector o) _
  | qIf cond t f iht ihf =>
      intro Θ σ
      dsimp only [liftDynamic, DynamicCircuit.compile, wp_qIf]
      split_ifs
      · exact iht Θ σ
      · exact ihf Θ σ
  | seq d₁ d₂ ih₁ ih₂ =>
      intro Θ σ
      rw [show liftDynamic v r (.seq d₁ d₂) = .seq (liftDynamic v r d₁) (liftDynamic v r d₂)
          from rfl,
        DynamicCircuit.compile_seq, DynamicCircuit.compile_seq]
      dsimp only [wp_qSeq, wp_qIf, wp_skip, wp_abort, wp_assign_eq_compat, wp_qAssign_eq_compat,
        wp_qMeasure_eq_compat]
      rw [ih₁ (wp (liftDynamic v r d₂).compile Θ) σ]
      refine congrArg (fun F ↦ wp d₁.compile F (fun _ ↦ σ v)) (funext fun τ ↦ ?_)
      rw [ih₂ Θ (Function.update σ v (τ ())),
        show (fun _ : Unit ↦ Function.update σ v (τ ()) v) = τ from funext fun () ↦ by simp]
      exact congrArg (fun F ↦ wp d₂.compile F τ) (funext fun _ ↦ by rw [Function.update_idem])
theorem isoMat_conj_apply {m n : ℕ} (r : QRegister m n) (ψ : (r.Environment → ZMod 2) → ℂ)
    (D : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) (i j : Fin (2 ^ m)) :
    ((isoMat r ψ)ᴴ * D * isoMat r ψ) i j = ∑ e₁, ∑ e₂, star (ψ e₁) * D
    (r.basisSplitEquiv.symm (i, e₁)) (r.basisSplitEquiv.symm (j, e₂)) * ψ e₂ := by
  rw [Matrix.mul_apply, ← r.basisSplitEquiv.symm.sum_comp, Fintype.sum_prod_type]
  simp only [isoMat, extractIndex_basisSplit_symm, snd_basisSplit_symm]
  rw [Finset.sum_eq_single j (fun _ _ hk₂ ↦ by simp [hk₂])
    (fun hm ↦ absurd (Finset.mem_univ j) hm)]
  simp only [↓reduceIte]
  rw [← Finset.sum_comm]
  refine Finset.sum_congr rfl fun e₂ _ ↦ ?_
  rw [Matrix.mul_apply, ← r.basisSplitEquiv.symm.sum_comp, Fintype.sum_prod_type,
    Finset.sum_eq_single i (fun _ _ hk₁ ↦ by
      simp [Matrix.conjTranspose_apply, isoMat, extractIndex_basisSplit_symm, hk₁])
      (fun hm ↦ absurd (Finset.mem_univ i) hm)]
  simp only [Matrix.conjTranspose_apply, isoMat, extractIndex_basisSplit_symm,
    snd_basisSplit_symm, ↓reduceIte, Finset.sum_mul]
theorem matrix_eq_of_isoMat_conj_eq {m n : ℕ} (r : QRegister m n)
    (X Y : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) (h : ∀ (ψ : (r.Environment → ZMod 2) → ℂ),
    IsoContraction r ψ → (isoMat r ψ)ᴴ * X * isoMat r ψ = (isoMat r ψ)ᴴ * Y * isoMat r ψ) :
    X = Y := by
  let D : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ := X - Y
  let sp := r.basisSplitEquiv.symm
  have hD {ψ : (r.Environment → ZMod 2) → ℂ} (hc : IsoContraction r ψ) (i j : Fin (2 ^ m)) :
      (∑ e₁, ∑ e₂, star (ψ e₁) * D (sp (i, e₁)) (sp (j, e₂)) * ψ e₂) = 0 := by
    rw [← isoMat_conj_apply, show (isoMat r ψ)ᴴ * D * isoMat r ψ =
      (isoMat r ψ)ᴴ * X * isoMat r ψ - (isoMat r ψ)ᴴ * Y * isoMat r ψ by
        dsimp only [D]
        rw [Matrix.mul_sub, Matrix.sub_mul], h ψ hc, sub_self, Matrix.zero_apply]
  have hdiag (i j : Fin (2 ^ m)) (e : r.Environment → ZMod 2) :
      D (sp (i, e)) (sp (j, e)) = 0 := by
    let ψ : (r.Environment → ZMod 2) → ℂ := fun x ↦ if x = e then 1 else 0
    have hψ (x) (hx : x ≠ e) : ψ x = 0 := by simp [ψ, hx]
    have hs1 (f : (r.Environment → ZMod 2) → ℂ) (hf : ∀ x ≠ e, f x = 0) : ∑ x, f x = f e :=
      Finset.sum_eq_single e (fun x _ hx ↦ hf x hx) (fun hm ↦ absurd (Finset.mem_univ e) hm)
    have hv := hD (ψ := ψ) ⟨1, le_rfl, by
      rw [hs1 _ fun x hx ↦ by simp [hψ x hx]]
      simp [ψ]⟩ i j
    rw [hs1 _ fun x hx ↦ by simp [hψ x hx], hs1 _ fun x hx ↦ by simp [hψ x hx]] at hv
    simpa [ψ] using hv
  have hexpand {e₁ e₂ : r.Environment → ZMod 2} (hne : e₁ ≠ e₂)
      (f : (r.Environment → ZMod 2) → ℂ) (hf : ∀ x, x ≠ e₁ → x ≠ e₂ → f x = 0) :
      ∑ x, f x = f e₁ + f e₂ := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ e₁),
      ← Finset.add_sum_erase _ _ (Finset.mem_erase.mpr ⟨hne.symm, Finset.mem_univ e₂⟩),
      Finset.sum_eq_zero fun x hx ↦ hf x (Finset.mem_erase.mp (Finset.mem_erase.mp hx).2).1
        (Finset.mem_erase.mp hx).1, add_zero]
  have hpair (i j : Fin (2 ^ m)) {e₁ e₂ : r.Environment → ZMod 2} (hne : e₁ ≠ e₂)
      (α : ℂ) (hα : star α * α = 1) :
      (1 / 2 : ℂ) * D (sp (i, e₁)) (sp (j, e₂)) * (α / 2) +
        (star α / 2) * D (sp (i, e₂)) (sp (j, e₁)) * (1 / 2 : ℂ) = 0 := by
    let ψ : (r.Environment → ZMod 2) → ℂ :=
      fun x ↦ if x = e₁ then (1 / 2 : ℂ) else if x = e₂ then α / 2 else 0
    have hs2 : star (2 : ℂ) = 2 := by simp
    have hc : IsoContraction r ψ := ⟨1 / 2, by norm_num, by
      rw [hexpand hne _ fun x h1 h2 ↦ by simp [ψ, h1, h2]]
      simp only [ψ, ↓reduceIte, hne.symm, star_div₀, star_one, hs2]
      rw [show ((1 : ℂ) / 2) * (1 / 2) + (star α / 2) * (α / 2) = (1 + star α * α) / 4 by ring,
        hα]
      norm_num⟩
    have hv := hD hc i j
    rw [hexpand hne _ fun x h1 h2 ↦ by simp [ψ, h1, h2],
      hexpand hne _ fun x h1 h2 ↦ by simp [ψ, h1, h2],
      hexpand hne _ fun x h1 h2 ↦ by simp [ψ, h1, h2]] at hv
    simp only [ψ, ↓reduceIte, hne.symm, hdiag, mul_zero, zero_mul, zero_add, add_zero,
      star_div₀, star_one, hs2] at hv
    simpa only [add_assoc] using hv
  refine sub_eq_zero.mp (Matrix.ext fun g₁ g₂ ↦ ?_)
  rw [(r.basisSplitEquiv.symm_apply_apply g₁).symm,
    (r.basisSplitEquiv.symm_apply_apply g₂).symm]
  let p₁ := r.basisSplitEquiv g₁
  let p₂ := r.basisSplitEquiv g₂
  change D (sp (p₁.1, p₁.2)) (sp (p₂.1, p₂.2)) = 0
  by_cases he : p₁.2 = p₂.2
  · exact he ▸ hdiag p₁.1 p₂.1 p₁.2
  · have h1 := hpair p₁.1 p₂.1 he 1 (by simp)
    have hI := hpair p₁.1 p₂.1 he Complex.I (by simp)
    rw [star_one] at h1
    rw [show star Complex.I = -Complex.I by simp] at hI
    linear_combination 2 * h1 - 2 * Complex.I * hI +
      ((1 : ℂ) / 2 * D (sp (p₁.1, p₁.2)) (sp (p₂.1, p₂.2)) -
       (1 : ℂ) / 2 * D (sp (p₁.1, p₂.2)) (sp (p₂.1, p₁.2))) * Complex.I_sq
theorem realizes_liftDynamic {Var : Type} [Fintype Var] [DecidableEq Var] {k w m n : ℕ}
    [NeZero (2 ^ m)] [NeZero (2 ^ n)] (v : Var) (r : QRegister m n) (rAct0 : QRegister k m)
    (rWork0 : QRegister w m) (u : Unitary (2 ^ k)) (d : DynamicCircuit Unit m)
    (hd : RealizesEmbeddedUnitaryWithCleanWorkspace rAct0 rWork0 u d) :
    RealizesEmbeddedUnitaryWithCleanWorkspace (r.compose rAct0) (r.compose rWork0) u
    (liftDynamic v r d) := fun M ↦ by
  let M' : Observable (Fin (2 ^ n)) := wp (liftDynamic v r d).compile (fun _ ↦ M) (fun _ ↦ 0)
  have hpull (σ : Store Var) {ψ : (r.Environment → ZMod 2) → ℂ} (hc : IsoContraction r ψ) :
      (isoMat r ψ)ᴴ * (wp (liftDynamic v r d).compile (fun _ ↦ M) σ).1.1 * isoMat r ψ =
        (wp d.compile (fun _ ↦ pullObs r ψ hc M) (fun _ ↦ σ v)).1.1 :=
    (pullObs_mat r ψ hc _).symm.trans
      (congrArg (fun Q ↦ Q.1.1) (wp_liftDynamic_pull v r ψ hc d _ σ))
  refine ⟨M', funext fun σ ↦ Subtype.ext <| Subtype.ext <| matrix_eq_of_isoMat_conj_eq r _ _
    fun ψ hc ↦ ?_, matrix_eq_of_isoMat_conj_eq r _ _ fun ψ hc ↦ ?_⟩
  · obtain ⟨M₀', hwp₀, _⟩ := hd (pullObs r ψ hc M)
    rw [hpull σ hc, hpull (fun _ ↦ 0) hc, hwp₀]
  · obtain ⟨M₀', hwp₀, hproj₀⟩ := hd (pullObs r ψ hc M)
    have hM' : (isoMat r ψ)ᴴ * M'.1.1 * isoMat r ψ = M₀'.1.1 := by
      simpa only [M', hwp₀] using hpull (fun _ ↦ 0) hc
    have hP : (r.compose rWork0).basisOutcomeProjector 0 =
        r.embedMatrix (rWork0.basisOutcomeProjector 0) :=
      QRegister.embedMatrix_compose r rWork0 (compProj 0)
    rw [hP,
      show ((r.compose rAct0).embedUnitary u).1 = r.embedMatrix (rAct0.embedUnitary u).1 by
        rw [QRegister.embedUnitary_compose, QRegister.embedUnitary_val,
          QRegister.embedUnitary_val],
      ← QRegister.embedMatrix_conjTranspose, isoMat_conj_embedMatrix, hM', hproj₀,
      isoMat_conj_embedMatrix, isoMat_conj_embedMatrix, pullObs_mat]
abbrev nCanon4102 : ℕ := (3924 + 3 + 7) + 168
def rQftCanon : QRegister (3924 + 3 + 7) nCanon4102 :=
  QRegister.block 0 (3924 + 3 + 7) (by decide)
def rWorkCanon : QRegister 168 nCanon4102 := QRegister.block (3924 + 3 + 7) 168 (by decide)
theorem rQftCanon_disjoint_rWorkCanon : rQftCanon.DisjointWires rWorkCanon :=
  disjoint_block_sep (by decide)
def rSysCanon : QRegister (3924 + 3) nCanon4102 := rQftCanon.compose rIdInCat
def rPGCanon : QRegister 7 nCanon4102 := rQftCanon.compose rPGInCat
theorem rSysCanon_disjoint_rPGCanon : rSysCanon.DisjointWires rPGCanon :=
  rIdOfCat_disjoint_rPGOfCat rQftCanon
theorem rSysCanon_disjoint_rWorkCanon : rSysCanon.DisjointWires rWorkCanon :=
  rQftCanon_disjoint_rWorkCanon.compose_left _
theorem rPGCanon_disjoint_rWorkCanon : rPGCanon.DisjointWires rWorkCanon :=
  rQftCanon_disjoint_rWorkCanon.compose_left _
structure CanonStageSpec where
  uCat : Unitary (2 ^ (3924 + 3 + 7))
  uEff : Unitary (2 ^ (3924 + 3))
  tCost : ℕ
  dFwd : DynamicCircuit Unit nCanon4102
  dInv : DynamicCircuit Unit nCanon4102
  hToffFwd : dFwd.count .TOFF = 0
  hToffInv : dInv.count .TOFF = 0
  hTFwd : dFwd.count .T = tCost
  hTInv : dInv.count .T = tCost
  hRealFwd : RealizesEmbeddedUnitaryWithCleanWorkspace rQftCanon rWorkCanon uCat dFwd
  hRealInv : RealizesEmbeddedUnitaryWithCleanWorkspace rQftCanon rWorkCanon uCat⁻¹ dInv
  hIntertwines : ∀ {N : ℕ} [NeZero (2 ^ N)] (rId : QRegister (3924 + 3) N)
    (rPG : QRegister 7 N) (hdisj : rId.DisjointWires rPG) (U_cat7 : Unitary (2 ^ 7)),
    U_cat7.1.mulVec (Pi.single 0 1) = DyadicQft64.phaseGradKet 7 →
    DyadicQft64.IntertwinesCatOp (rPG.embedUnitary U_cat7).1 (rPG.basisOutcomeProjector 0)
      ((rId.concat rPG hdisj).embedUnitary uCat).1 (rId.embedUnitary uEff).1
noncomputable def CanonStageSpec.id : CanonStageSpec :=
  { uCat := 1, uEff := 1, tCost := 0, dFwd := .identity, dInv := .identity,
    hToffFwd := rfl, hToffInv := rfl, hTFwd := rfl, hTInv := rfl,
    hRealFwd := realizesEmbeddedUnitaryWithCleanWorkspace_identity rQftCanon rWorkCanon,
    hRealInv := by
      rw [inv_one]
      exact realizesEmbeddedUnitaryWithCleanWorkspace_identity rQftCanon rWorkCanon,
    hIntertwines := fun rId rPG hdisj U_cat7 _ ↦ by
      rw [(rId.concat rPG hdisj).embedUnitary_one, rId.embedUnitary_one]
      exact DyadicQft64.IntertwinesCatOp.one _ _ }
noncomputable def CanonStageSpec.seq (S₁ S₂ : CanonStageSpec) : CanonStageSpec :=
  { uCat := S₂.uCat * S₁.uCat, uEff := S₂.uEff * S₁.uEff, tCost := S₁.tCost + S₂.tCost,
    dFwd := .seq S₁.dFwd S₂.dFwd, dInv := .seq S₂.dInv S₁.dInv,
    hToffFwd := by simp [S₁.hToffFwd, S₂.hToffFwd],
    hToffInv := by simp [S₂.hToffInv, S₁.hToffInv],
    hTFwd := by simp [S₁.hTFwd, S₂.hTFwd],
    hTInv := by simp only [DynamicCircuit.count, S₂.hTInv, S₁.hTInv, Nat.add_comm],
    hRealFwd := S₁.hRealFwd.seq rQftCanon_disjoint_rWorkCanon S₂.hRealFwd,
    hRealInv := by
      rw [_root_.mul_inv_rev]
      exact S₂.hRealInv.seq rQftCanon_disjoint_rWorkCanon S₁.hRealInv,
    hIntertwines := fun rId rPG hdisj U_cat7 hcol0 ↦ by
      rw [(rId.concat rPG hdisj).embedUnitary_mul, rId.embedUnitary_mul,
        Submonoid.coe_mul, Submonoid.coe_mul]
      exact (S₂.hIntertwines rId rPG hdisj U_cat7 hcol0).mul
        (S₁.hIntertwines rId rPG hdisj U_cat7 hcol0) }
noncomputable def CanonStageSpec.congr (S : CanonStageSpec)
    {uEff' : Unitary (2 ^ (3924 + 3))} {tCost' : ℕ}
    (hu : S.uEff = uEff') (ht : S.tCost = tCost') : CanonStageSpec :=
  { uCat := S.uCat, uEff := uEff', tCost := tCost', dFwd := S.dFwd, dInv := S.dInv,
    hToffFwd := S.hToffFwd, hToffInv := S.hToffInv,
    hTFwd := S.hTFwd.trans ht, hTInv := S.hTInv.trans ht,
    hRealFwd := S.hRealFwd, hRealInv := S.hRealInv,
    hIntertwines := fun rId rPG hdisj U_cat7 hcol0 ↦ by
      rw [← hu]
      exact S.hIntertwines rId rPG hdisj U_cat7 hcol0 }
def axisChainCircuit {n : ℕ} (c6 : Circuit 6) : ∀ {M : ℕ}, (Fin M → QRegister 6 n) → Circuit n
  | 0, _ => Circuit.identity
  | _ + 1, rs => axisChainCircuit c6 (fun i ↦ rs i.succ) ;;ᶜ c6.onRegister (rs 0)
theorem count_axisChainCircuit {a n : ℕ} (g : PrimitiveGate a) (c6 : Circuit 6) :
    ∀ {M : ℕ} (rs : Fin M → QRegister 6 n), (axisChainCircuit c6 rs).count g = M * c6.count g
  | 0, _ => by simp [axisChainCircuit]
  | _ + 1, rs => by
      rw [axisChainCircuit, Circuit.count_seq, Circuit.count_onRegister,
        count_axisChainCircuit g c6 (fun i ↦ rs i.succ)]
      ring
theorem eval_axisChainCircuit {n : ℕ} (c6 : Circuit 6) :
    ∀ {M : ℕ} (rs : Fin M → QRegister 6 n),
      (axisChainCircuit c6 rs).eval =
        (List.ofFn fun i : Fin M ↦ (rs i).embedUnitary c6.eval).prod
  | 0, _ => by simp [axisChainCircuit]
  | _ + 1, rs => by
      rw [axisChainCircuit, Circuit.eval_seq, Circuit.eval_onRegister,
        eval_axisChainCircuit c6 (fun i ↦ rs i.succ), List.ofFn_succ, List.prod_cons]
theorem ofAxis654Circuit_eval_fwd (c6 : Circuit 6) (u6 : Unitary 64) (heval6 : c6.eval = u6) :
    (axisChainCircuit c6 rAxis654).eval = axisProd654 (fun _ ↦ u6) := by
  simp only [axisProd654, eval_axisChainCircuit, heval6]
theorem bit6_eq_basisBits_val (u : Fin 64) (r : Fin 6) :
    bit6 u r = (basisBits 6 u r).val := by
  rw [basisBits_eq_div_mod, ZMod.val_natCast_of_lt (Nat.mod_lt _ (by decide : 0 < 2))]
  rfl
theorem bit6_basisBitsEquiv_symm (g : Fin 6 → ZMod 2) (r : Fin 6) :
    bit6 ((basisBitsEquiv 6).symm g) r = (g r).val := by
  have hb : basisBits 6 ((basisBitsEquiv 6).symm g) r = g r :=
    congrFun ((basisBitsEquiv 6).apply_symm_apply g) r
  rw [bit6_eq_basisBits_val, hb]
theorem phasePerm_to_diagonal6 (c6 : Circuit 6) (e : Fin 64 → ℤ) (hp : PhasePerm (∅ : Finset
    (Wire 6)) c6 (fun β : BitAssignment 6 ↦ dyadicTurn 7 (e ((basisBitsEquiv 6).symm β))) id)
    : c6.eval.1 = Matrix.diagonal (fun u : Fin 64 ↦ omega128 (e u)) :=
  matrix_ext_basisKet fun β ↦ (hp.evolve β).trans <| funext fun x ↦ by
    rw [Matrix.mulVec_diagonal]
    dsimp only [basisKet, basisState, Pi.smul_apply, smul_eq_mul, id]
    by_cases hx : x = (basisBitsEquiv 6).symm β <;> simp [hx, dyadicTurn_eq_omega128]
structure InnerModAddSpec where
  shift : BitAssignment (3924 + 3) → ℕ
  tCost : ℕ
  dFwd : DynamicCircuit Unit nCanon4102
  dInv : DynamicCircuit Unit nCanon4102
  hToffFwd : dFwd.count .TOFF = 0
  hToffInv : dInv.count .TOFF = 0
  hTFwd : dFwd.count .T = tCost
  hTInv : dInv.count .T = tCost
  hRealFwd : RealizesEmbeddedUnitaryWithCleanWorkspace
    (rSysCanon.concat rPGCanon rSysCanon_disjoint_rPGCanon)
    ((rWorkCanon.slice 0 159 (by decide)).slice 7 (159 - 7) (by decide))
    (catModAddUnitary (3924 + 3) 7 shift) dFwd
  hRealInv : RealizesEmbeddedUnitaryWithCleanWorkspace
    (rSysCanon.concat rPGCanon rSysCanon_disjoint_rPGCanon)
    ((rWorkCanon.slice 0 159 (by decide)).slice 7 (159 - 7) (by decide))
    (catModAddUnitary (3924 + 3) 7 shift)⁻¹ dInv
theorem rSub152_disj_sys : rSysCanon.DisjointWires
    ((rWorkCanon.slice 0 159 (by decide)).slice 7 (159 - 7) (by decide)) :=
  (rSysCanon_disjoint_rWorkCanon.compose_right _).compose_right _
theorem rSub152_disj_pg : rPGCanon.DisjointWires
    ((rWorkCanon.slice 0 159 (by decide)).slice 7 (159 - 7) (by decide)) :=
  (rPGCanon_disjoint_rWorkCanon.compose_right _).compose_right _
theorem rSub152_disj_qft :
    (rSysCanon.concat rPGCanon rSysCanon_disjoint_rPGCanon).DisjointWires
      ((rWorkCanon.slice 0 159 (by decide)).slice 7 (159 - 7) (by decide)) :=
  disjoint_concat_left rSysCanon_disjoint_rPGCanon rSub152_disj_sys rSub152_disj_pg
noncomputable def InnerModAddSpec.id : InnerModAddSpec :=
  { shift := fun _ ↦ 0, tCost := 0, dFwd := .identity, dInv := .identity,
    hToffFwd := rfl, hToffInv := rfl, hTFwd := rfl, hTInv := rfl,
    hRealFwd := by
      rw [catModAddUnitary_zero_eq_one]
      exact realizesEmbeddedUnitaryWithCleanWorkspace_identity _ _,
    hRealInv := by
      rw [catModAddUnitary_zero_eq_one, inv_one]
      exact realizesEmbeddedUnitaryWithCleanWorkspace_identity _ _ }
noncomputable def InnerModAddSpec.seq (A B : InnerModAddSpec) : InnerModAddSpec :=
  { shift := fun γ ↦ A.shift γ + B.shift γ, tCost := A.tCost + B.tCost,
    dFwd := .seq A.dFwd B.dFwd, dInv := .seq B.dInv A.dInv,
    hToffFwd := by simp [A.hToffFwd, B.hToffFwd],
    hToffInv := by simp [B.hToffInv, A.hToffInv],
    hTFwd := by simp [A.hTFwd, B.hTFwd],
    hTInv := by simp only [DynamicCircuit.count, B.hTInv, A.hTInv, Nat.add_comm],
    hRealFwd := by
      rw [← catModAddUnitary_mul_add]
      exact A.hRealFwd.seq rSub152_disj_qft B.hRealFwd,
    hRealInv := by
      rw [← catModAddUnitary_mul_add, _root_.mul_inv_rev]
      exact B.hRealInv.seq rSub152_disj_qft A.hRealInv }
end Section2APart2Assembly
end ConfigDyadicQft64WalkCircuit
set_option maxRecDepth 2000
set_option backward.isDefEq.respectTransparency true
end DyadicQft64WalkCircuit
end
end ModDyadicQft64WalkCircuit

section ModFullSysCatSegmentBridge
@[expose] public section
namespace FullSysCatSegmentBridgeAlt
theorem qreg_block_apply {n : ℕ} (offset width : ℕ) (h : offset + width ≤ n) (i : Fin width) :
    QRegister.block offset width h i = ⟨offset + i.val, by omega⟩ := rfl
end FullSysCatSegmentBridgeAlt
namespace FullSysCatSegmentBridge
open Operator Matrix QProg Circuit _root_.DynamicCircuit DynCircuitExt Real SpecsAux
open SpecsAux.SpecMirror
open SpecsAux.BridgeFermionicComm
open SpecsAux.BridgeFermionicComm.SpecInner
open SpecsAux.FullScaleBESector
open SpecsAux.PhaseGradCatalystCore
open PosMomSelectSandwich
open PosMomSelectDynamic
open FullSysWalkStepEndpoint
open TwosCompAndWire0Cancel
open scoped Matrix BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
theorem fullSys_zero_add_le_self (a : ℕ) : 0 + a ≤ a := by omega
theorem fullSys_zero_add_le_of_le {a b : ℕ} (h : a ≤ b) : 0 + a ≤ b := by omega
abbrev fullSysCoreWires (mPayload : ℕ) : ℕ := SpecsAux.SpecMirror.systemQubits + 6 + mPayload
@[reducible, inline] def fullSysRawAncWires (mPayload : ℕ) : ℕ := 6 + mPayload
abbrev fullSysBEWires (mPayload : ℕ) : ℕ :=
  SpecsAux.SpecMirror.systemQubits + fullSysRawAncWires mPayload
theorem le_fullSysCoreWires {k m : ℕ} (hk : k ≤ 3954 + m) : k ≤ fullSysCoreWires m := by
  dsimp [fullSysCoreWires, SpecsAux.SpecMirror.systemQubits, SpecsAux.SpecMirror.numElectrons,
    SpecsAux.SpecMirror.electronBits, SpecsAux.SpecMirror.projectileBits]
  omega
theorem lt_fullSysCoreWires {k m : ℕ} (hk : k < 3954) : k < fullSysCoreWires m :=
  Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le hk (Nat.le_add_right 3954 m))
    (le_fullSysCoreWires le_rfl)
abbrev iSlot0 (mPayload : ℕ) : Wire (fullSysCoreWires mPayload) :=
  ⟨3948, lt_fullSysCoreWires (by decide)⟩
abbrev iSlot1 (mPayload : ℕ) : Wire (fullSysCoreWires mPayload) :=
  ⟨3949, lt_fullSysCoreWires (by decide)⟩
abbrev iSlot2 (mPayload : ℕ) : Wire (fullSysCoreWires mPayload) :=
  ⟨3950, lt_fullSysCoreWires (by decide)⟩
abbrev coreElecBlock (mPayload : ℕ) : QRegister 3924 (fullSysCoreWires mPayload) :=
  QRegister.block 0 3924 (le_fullSysCoreWires (by omega))
abbrev coreCosetB1Block {mPayload : ℕ} (hmPay : 6 ≤ mPayload) :
    QRegister 3 (fullSysCoreWires mPayload) :=
  QRegister.block 3954 3 (le_fullSysCoreWires (by omega))
theorem coreElecBlock_disjoint_coreCosetB1Block {mPayload : ℕ} (hmPay : 6 ≤ mPayload) :
    (coreElecBlock mPayload).DisjointWires (coreCosetB1Block hmPay) :=
  QRegister.block_disjoint_of_le 0 3924 3954 3 (le_fullSysCoreWires (by omega))
    (le_fullSysCoreWires (by omega)) (by omega)
abbrev coreElecCosetB1Block {mPayload : ℕ} (hmPay : 6 ≤ mPayload) :
    QRegister (3924 + 3) (fullSysCoreWires mPayload) :=
  (coreElecBlock mPayload).concat (coreCosetB1Block hmPay)
    (coreElecBlock_disjoint_coreCosetB1Block hmPay)
abbrev beCoreBlock (mPayload : ℕ) :
    QRegister (fullSysCoreWires mPayload) (fullSysBEWires mPayload) :=
  QRegister.block 0 (fullSysCoreWires mPayload) (by
    dsimp [fullSysCoreWires, fullSysBEWires, fullSysRawAncWires]
    omega)
def IntertwinesLocalCat {kAct mCat : ℕ} (U_cat : Unitary (2 ^ mCat))
    (W_cat : Unitary (2 ^ (kAct + mCat))) (U_eff : Unitary (2 ^ kAct)) : Prop :=
  let rAct0 : QRegister kAct (kAct + mCat) := .block 0 kAct (fullSys_zero_add_le kAct mCat)
  let rCat0 : QRegister mCat (kAct + mCat) := .block kAct mCat le_rfl
  IntertwinesCat (rCat0.embedUnitary U_cat).1 (rCat0.basisOutcomeProjector 0)
    W_cat.1 (rAct0.embedUnitary U_eff).1
theorem liftCleanCoreToTwistCat {kAct mCat : ℕ} (U_cat : Unitary (2 ^ mCat))
    (U_eff : Unitary (2 ^ kAct)) : IntertwinesLocalCat U_cat
      ((QRegister.block 0 kAct (fullSys_zero_add_le kAct mCat)).embedUnitary U_eff) U_eff :=
  intertwinesCat_of_disjoint _ _ (QRegister.block_disjoint_of_le 0 kAct kAct mCat
    (fullSys_zero_add_le kAct mCat) le_rfl (fullSys_zero_add_le_self kAct)) U_cat U_eff.1
theorem IntertwinesLocalCat.inv {kAct mCat : ℕ} {U_cat : Unitary (2 ^ mCat)}
    {W_cat : Unitary (2 ^ (kAct + mCat))} {U_eff : Unitary (2 ^ kAct)}
    (h : IntertwinesLocalCat U_cat W_cat U_eff) :
    IntertwinesLocalCat U_cat W_cat⁻¹ U_eff⁻¹ := by
  let rAct0 : QRegister kAct (kAct + mCat) := .block 0 kAct (fullSys_zero_add_le kAct mCat)
  let rCat0 : QRegister mCat (kAct + mCat) := .block kAct mCat le_rfl
  have hP_sa : star (rCat0.basisOutcomeProjector 0) = rCat0.basisOutcomeProjector 0 := by
    rw [Matrix.star_eq_conjTranspose, QRegister.basisOutcomeProjector_conjTranspose]
  change IntertwinesCat (rCat0.embedUnitary U_cat).1 (rCat0.basisOutcomeProjector 0)
    (W_cat⁻¹).1 (rAct0.embedUnitary U_eff⁻¹).1
  rw [congrArg Subtype.val (Unitary.star_eq_inv W_cat).symm,
    show (rAct0.embedUnitary U_eff⁻¹).1 = star (rAct0.embedUnitary U_eff).1 by
      rw [QRegister.embedUnitary_val, QRegister.embedUnitary_val, ← Unitary.star_eq_inv,
        Unitary.coe_star, Matrix.star_eq_conjTranspose, Matrix.star_eq_conjTranspose,
        rAct0.embedMatrix_conjTranspose]]
  exact IntertwinesCat.unitary_star hP_sa W_cat (rAct0.embedUnitary U_eff) h
theorem disjointWires_compose_of_disjoint {k m₁ m₂ n : ℕ} (rOuter : QRegister k n)
    {r₁ : QRegister m₁ k} {r₂ : QRegister m₂ k} (hdisj : r₁.DisjointWires r₂) :
    (rOuter.compose r₁).DisjointWires (rOuter.compose r₂) := by
  rw [QRegister.DisjointWires, Set.disjoint_left]
  rintro _ ⟨i, rfl⟩ ⟨j, hj⟩
  exact Set.disjoint_left.mp hdisj ⟨i, rfl⟩ ⟨j, (rOuter.wires.injective hj.symm).symm⟩
theorem disjointWires_concat_left {k₁ k₂ k₃ n : ℕ} {r₁ : QRegister k₁ n} {r₂ : QRegister k₂ n}
    {r₃ : QRegister k₃ n} (h₁₂ : r₁.DisjointWires r₂) (h₁₃ : r₁.DisjointWires r₃)
    (h₂₃ : r₂.DisjointWires r₃) : (r₁.concat r₂ h₁₂).DisjointWires r₃ := by
  rw [QRegister.DisjointWires, Set.disjoint_left]
  rintro _ ⟨idx, rfl⟩ ⟨j, hj⟩
  by_cases hlt : idx.val < k₁
  · rw [show idx = Fin.castAdd k₂ ⟨idx.val, hlt⟩ from Fin.ext rfl,
      QRegister.concat_apply_left] at hj
    exact Set.disjoint_left.mp h₁₃ ⟨⟨idx.val, hlt⟩, rfl⟩ ⟨j, hj⟩
  · rw [show idx = Fin.natAdd k₁ ⟨idx.val - k₁, by omega⟩ from Fin.ext (by
      simp
      omega), QRegister.concat_apply_right] at hj
    exact Set.disjoint_left.mp h₂₃ ⟨⟨idx.val - k₁, by omega⟩, rfl⟩ ⟨j, hj⟩
structure FullSysQft654Bundle where
  mWorkQft : ℕ
  uQft654 : Unitary (2 ^ (3924 + 3))
  uQftCat : Unitary (2 ^ ((3924 + 3) + 7))
  hIntertwinesQft : ∀ (U_cat7 : Unitary (2 ^ 7)),
    (∀ m : Fin (2 ^ 7), U_cat7.1 m 0 = PhaseGradCatalystCore.phaseGradientState 7 m) →
    IntertwinesLocalCat U_cat7 uQftCat uQft654
/-- Catalyst-free `FullSysQft654Bundle` lifting any `(3924 + 3)`-wire `U_eff` directly. -/
noncomputable def FullSysQft654Bundle.ofIdeal654 (mWork : ℕ) (U_eff : Unitary (2 ^ (3924 + 3))) :
    FullSysQft654Bundle where
  mWorkQft := mWork
  uQft654 := U_eff
  uQftCat := (QRegister.block 0 (3924 + 3) (fullSys_zero_add_le (3924 + 3) 7)).embedUnitary U_eff
  hIntertwinesQft U_cat7 _ := liftCleanCoreToTwistCat U_cat7 U_eff
structure FullSysPrepareBundle (mPayload : ℕ) where
  mWorkPrep : ℕ
  tPrep : ℕ
  uPrep : SpecsAux.SpecMirror.Configuration → Unitary (2 ^ (fullSysBEWires mPayload))
  dPrep : SpecsAux.SpecMirror.Configuration → ∀ {Var : Type} {n : ℕ}, Var →
    (rBE : QRegister (fullSysBEWires mPayload) n) → (rWork : QRegister mWorkPrep n) →
    rBE.DisjointWires rWork → DynamicCircuit Var n
  dPrepInv : SpecsAux.SpecMirror.Configuration → ∀ {Var : Type} {n : ℕ}, Var →
    (rBE : QRegister (fullSysBEWires mPayload) n) → (rWork : QRegister mWorkPrep n) →
    rBE.DisjointWires rWork → DynamicCircuit Var n
  hToffPrep : ∀ c {Var : Type} {n : ℕ} v rBE rWork hD,
    (dPrep c (Var := Var) (n := n) v rBE rWork hD).count .TOFF = 0
  hToffPrepInv : ∀ c {Var : Type} {n : ℕ} v rBE rWork hD,
    (dPrepInv c (Var := Var) (n := n) v rBE rWork hD).count .TOFF = 0
  hTPrep : ∀ c {Var : Type} {n : ℕ} v rBE rWork hD,
    (dPrep c (Var := Var) (n := n) v rBE rWork hD).count .T ≤ tPrep
  hTPrepInv : ∀ c {Var : Type} {n : ℕ} v rBE rWork hD,
    (dPrepInv c (Var := Var) (n := n) v rBE rWork hD).count .T ≤ tPrep
  hRealPrep : ∀ c {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)]
    (v : Var) (rBE : QRegister (fullSysBEWires mPayload) n) (rWork : QRegister mWorkPrep n)
    hD, DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace rBE rWork (uPrep c)
      (dPrep c v rBE rWork hD)
  hRealPrepInv : ∀ c {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)]
    (v : Var) (rBE : QRegister (fullSysBEWires mPayload) n) (rWork : QRegister mWorkPrep n)
    hD, DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace rBE rWork (uPrep c)⁻¹
      (dPrepInv c v rBE rWork hD)
structure FullSysSelectOracleBundle (mPayload mPGTwist : ℕ) where
  hmPay : 6 ≤ mPayload
  uMomPhaseCat :
    SpecsAux.SpecMirror.Configuration → Unitary (2 ^ (fullSysCoreWires mPayload + mPGTwist))
  uMomPhase : SpecsAux.SpecMirror.Configuration → Unitary (2 ^ (fullSysCoreWires mPayload))
  uTwistCat :
    SpecsAux.SpecMirror.Configuration → Unitary (2 ^ (fullSysCoreWires mPayload + mPGTwist))
  uTwist : SpecsAux.SpecMirror.Configuration → Unitary (2 ^ (fullSysCoreWires mPayload))
  uPosPhase : SpecsAux.SpecMirror.Configuration → Unitary (2 ^ (fullSysCoreWires mPayload))
  hIntertwinesMom : ∀ c (U_catTwist : Unitary (2 ^ mPGTwist)),
    (∀ m, U_catTwist.1 m 0 = PhaseGradCatalystCore.phaseGradientState mPGTwist m) →
    IntertwinesLocalCat U_catTwist (uMomPhaseCat c) (uMomPhase c)
  hIntertwinesTwist : ∀ c (U_catTwist : Unitary (2 ^ mPGTwist)),
    (∀ m, U_catTwist.1 m 0 = PhaseGradCatalystCore.phaseGradientState mPGTwist m) →
    IntertwinesLocalCat U_catTwist (uTwistCat c) (uTwist c)
  hMom_sa : ∀ c, (uMomPhase c).1ᴴ = (uMomPhase c).1
  hMom_on_P0 : ∀ c,
    (uMomPhase c).1 * slotBitProj (iSlot2 mPayload) 0 = slotBitProj (iSlot2 mPayload) 0
  hTwist_comm_P1 : ∀ c,
    (uTwist c).1 * slotBitProj (iSlot2 mPayload) 1 =
      slotBitProj (iSlot2 mPayload) 1 * (uTwist c).1
  hPos_sa : ∀ c, (uPosPhase c).1ᴴ = (uPosPhase c).1
  hPos_on_P1 : ∀ c,
    (uPosPhase c).1 * slotBitProj (iSlot2 mPayload) 1 = slotBitProj (iSlot2 mPayload) 1
noncomputable def fullSysQftCoreUnitary {mPayload : ℕ} (hmPay : 6 ≤ mPayload)
    (qft : FullSysQft654Bundle) : Unitary (2 ^ (fullSysCoreWires mPayload)) :=
  (coreElecCosetB1Block hmPay).embedUnitary qft.uQft654
noncomputable abbrev fullSysSelectMomUnitary {mPayload mPGTwist : ℕ}
    (sel : FullSysSelectOracleBundle mPayload mPGTwist) (c : SpecsAux.SpecMirror.Configuration) :
    Unitary (2 ^ (fullSysCoreWires mPayload)) := sel.uMomPhase c
noncomputable def fullSysSelectPosUnitary {mPayload mPGTwist : ℕ}
    (qft : FullSysQft654Bundle) (sel : FullSysSelectOracleBundle mPayload mPGTwist)
    (c : SpecsAux.SpecMirror.Configuration) : Unitary (2 ^ (fullSysCoreWires mPayload)) :=
  unitaryConj (fullSysQftCoreUnitary sel.hmPay qft * sel.uTwist c) (sel.uPosPhase c)
noncomputable def fullSysSelectEffUnitary {mPayload mPGTwist : ℕ}
    (qft : FullSysQft654Bundle) (sel : FullSysSelectOracleBundle mPayload mPGTwist)
    (c : SpecsAux.SpecMirror.Configuration) : Unitary (2 ^ (fullSysCoreWires mPayload)) :=
  fullSysSelectPosUnitary qft sel c * fullSysSelectMomUnitary sel c
theorem wire_not_mem_coreElecCosetB1 {mPayload : ℕ} (hmPay : 6 ≤ mPayload)
    {w : Wire (fullSysCoreWires mPayload)} (hw1 : 3924 ≤ w.val) (hw2 : w.val < 3954) :
    w ∉ Set.range (coreElecCosetB1Block hmPay).wires := fun ⟨idx, hEq⟩ ↦ by
  have hv := congrArg Fin.val hEq
  by_cases hlt : idx.val < 3924
  · rw [show idx = Fin.castAdd 3 ⟨idx.val, hlt⟩ from Fin.ext rfl,
      QRegister.concat_apply_left] at hv
    simp [coreElecBlock, FullSysCatSegmentBridgeAlt.qreg_block_apply] at hv
    omega
  · rw [show idx = Fin.natAdd 3924 ⟨idx.val - 3924, by omega⟩ from Fin.ext (by
      simp
      omega), QRegister.concat_apply_right] at hv
    simp [coreCosetB1Block, FullSysCatSegmentBridgeAlt.qreg_block_apply] at hv
    omega
theorem fullSysQftCoreUnitary_comm_slotBitProj {mPayload : ℕ} (hmPay : 6 ≤ mPayload)
    (qft : FullSysQft654Bundle) {w : Wire (fullSysCoreWires mPayload)} (hw1 : 3924 ≤ w.val)
    (hw2 : w.val < 3954) (b : Fin 2) : (fullSysQftCoreUnitary hmPay qft).1 * slotBitProj w b
    = slotBitProj w b * (fullSysQftCoreUnitary hmPay qft).1 :=
  embedMatrix_comm_diagonal_of_outside (coreElecCosetB1Block hmPay) qft.uQft654.1 _
    fun _ _ hOut ↦ by rw [hOut w (wire_not_mem_coreElecCosetB1 hmPay hw1 hw2)]
theorem slotBitProj_zero_add_one {k : ℕ} (w : Wire k) :
    slotBitProj w 0 + slotBitProj w 1 = (1 : Operator (2 ^ k)) := by
  rw [slotBitProj, slotBitProj, Matrix.diagonal_add, ← Matrix.diagonal_one]
  refine congrArg Matrix.diagonal (funext fun x ↦ ?_)
  rcases (by decide : ∀ z : ZMod 2, z.val = 0 ∨ z.val = 1) (basisBits k x w) with h | h <;>
    simp [h]
theorem slotBitProj_conjTranspose_self {k : ℕ} (w : Wire k) (b : Fin 2) :
    (slotBitProj w b)ᴴ = slotBitProj w b := by
  rw [slotBitProj, Matrix.diagonal_conjTranspose]
  exact congrArg Matrix.diagonal (funext fun x ↦ by
    by_cases h : (basisBits k x w).val = b.val <;> simp [h])
theorem fullSysSelectEffUnitary_conjTranspose_and_split {mPayload mPGTwist : ℕ}
    (qft : FullSysQft654Bundle) (sel : FullSysSelectOracleBundle mPayload mPGTwist)
    (c : SpecsAux.SpecMirror.Configuration) :
    let P₀ := slotBitProj (iSlot2 mPayload) 0
    let P₁ := slotBitProj (iSlot2 mPayload) 1
    (fullSysSelectEffUnitary qft sel c).1 =
        (fullSysSelectPosUnitary qft sel c).1 * P₀ +
          (fullSysSelectMomUnitary sel c).1 * P₁ ∧
      (fullSysSelectEffUnitary qft sel c).1ᴴ = (fullSysSelectEffUnitary qft sel c).1 := by
  intro P₀ P₁
  set S_pos := fullSysSelectPosUnitary qft sel c
  set S_mom := fullSysSelectMomUnitary sel c
  have hP₀_sa : P₀ᴴ = P₀ := slotBitProj_conjTranspose_self (iSlot2 mPayload) 0
  have hP₁_sa : P₁ᴴ = P₁ := slotBitProj_conjTranspose_self (iSlot2 mPayload) 1
  have hSum : P₀ + P₁ = 1 := slotBitProj_zero_add_one (iSlot2 mPayload)
  have hPos_sa : S_pos.1ᴴ = S_pos.1 := unitaryConj_conjTranspose (sel.hPos_sa c)
  have hMom_sa : S_mom.1ᴴ = S_mom.1 := sel.hMom_sa c
  have hMom_P₀ : S_mom.1 * P₀ = P₀ := sel.hMom_on_P0 c
  have hP₀_Mom : P₀ * S_mom.1 = P₀ := by
    simpa only [conjTranspose_mul, hMom_sa, hP₀_sa] using
      congrArg Matrix.conjTranspose hMom_P₀
  have hOuter_P₁ : (fullSysQftCoreUnitary sel.hmPay qft * sel.uTwist c).1 * P₁ =
      P₁ * (fullSysQftCoreUnitary sel.hmPay qft * sel.uTwist c).1 := by
    simp only [Submonoid.coe_mul]
    rw [Matrix.mul_assoc, sel.hTwist_comm_P1 c, ← Matrix.mul_assoc,
      fullSysQftCoreUnitary_comm_slotBitProj sel.hmPay qft (w := iSlot2 mPayload)
        (show 3924 ≤ 3950 by decide) (show 3950 < 3954 by decide) 1, Matrix.mul_assoc]
  have hPos_P₁ : S_pos.1 * P₁ = P₁ := by
    dsimp only [S_pos, fullSysSelectPosUnitary]
    rw [unitaryConj_val]
    exact momCleanOp_on_posSlot (congrArg Subtype.val (inv_mul_cancel
      (fullSysQftCoreUnitary sel.hmPay qft * sel.uTwist c))) hOuter_P₁ (sel.hPos_on_P1 c)
  have hP₁_Pos : P₁ * S_pos.1 = P₁ := by
    simpa only [conjTranspose_mul, hPos_sa, hP₁_sa] using congrArg Matrix.conjTranspose hPos_P₁
  have hCommMomP₁ : S_mom.1 * P₁ = P₁ * S_mom.1 := by
    rw [eq_sub_of_add_eq' hSum, Matrix.mul_sub, Matrix.mul_one, hMom_P₀, Matrix.sub_mul,
      Matrix.one_mul, hP₀_Mom]
  have hCommPosP₀ : P₀ * S_pos.1 = S_pos.1 * P₀ := by
    rw [eq_sub_of_add_eq hSum, Matrix.sub_mul, Matrix.one_mul, hP₁_Pos, Matrix.mul_sub,
      Matrix.mul_one, hPos_P₁]
  have hSplit : S_pos.1 * S_mom.1 = S_pos.1 * P₀ + S_mom.1 * P₁ := by
    calc S_pos.1 * S_mom.1 = S_pos.1 * S_mom.1 * (P₀ + P₁) := by rw [hSum, Matrix.mul_one]
      _ = S_pos.1 * (S_mom.1 * P₀) + S_pos.1 * (S_mom.1 * P₁) := by
          simp only [Matrix.mul_add, Matrix.mul_assoc]
      _ = S_pos.1 * P₀ + S_mom.1 * P₁ := by
          rw [hMom_P₀, hCommMomP₁, ← Matrix.mul_assoc S_pos.1 P₁, hPos_P₁, ← hCommMomP₁]
  refine ⟨hSplit, ?_⟩
  change (S_pos.1 * S_mom.1)ᴴ = S_pos.1 * S_mom.1
  rw [hSplit, conjTranspose_add, conjTranspose_mul, conjTranspose_mul,
    hP₀_sa, hP₁_sa, hPos_sa, hMom_sa, hCommPosP₀, ← hCommMomP₁]
noncomputable def fullSysRawBEUnitary {mPayload mPGTwist : ℕ} (qft : FullSysQft654Bundle)
    (prep : FullSysPrepareBundle mPayload)
    (sel : FullSysSelectOracleBundle mPayload mPGTwist)
    (c : SpecsAux.SpecMirror.Configuration) : Unitary (2 ^ (fullSysBEWires mPayload)) :=
  unitaryConj (prep.uPrep c)
    ((beCoreBlock mPayload).embedUnitary (fullSysSelectEffUnitary qft sel c))
theorem fullSysSelectEffUnitary_on_slackCoin {mPayload mPGTwist : ℕ}
    (qft : FullSysQft654Bundle) (sel : FullSysSelectOracleBundle mPayload mPGTwist)
    (c : SpecsAux.SpecMirror.Configuration) (b : Fin 2)
    (hTwist_s2 : (sel.uTwist c).1 * slotBitProj (iSlot2 mPayload) 0 =
      slotBitProj (iSlot2 mPayload) 0 * (sel.uTwist c).1)
    (hTwist_s1 : (sel.uTwist c).1 * slotBitProj (iSlot1 mPayload) 1 =
      slotBitProj (iSlot1 mPayload) 1 * (sel.uTwist c).1)
    (hTwist_s0 : (sel.uTwist c).1 * slotBitProj (iSlot0 mPayload) b =
      slotBitProj (iSlot0 mPayload) b * (sel.uTwist c).1)
    (hPos_slack :
      let P_slack := slotBitProj (iSlot2 mPayload) 0 * slotBitProj (iSlot1 mPayload) 1 *
        slotBitProj (iSlot0 mPayload) b
      (sel.uPosPhase c).1 * P_slack = (if b.val = 0 then (1 : ℂ) else -1) • P_slack) :
    let P_slack := slotBitProj (iSlot2 mPayload) 0 * slotBitProj (iSlot1 mPayload) 1 *
      slotBitProj (iSlot0 mPayload) b
    (fullSysSelectEffUnitary qft sel c).1 * P_slack =
      (if b.val = 0 then (1 : ℂ) else -1) • P_slack := by
  intro P_slack
  have hProj0 : slotBitProj (iSlot2 mPayload) 0 * P_slack = P_slack := by
    dsimp only [P_slack, slotBitProj]
    simp only [Matrix.diagonal_mul_diagonal]
    exact congrArg Matrix.diagonal (funext fun x ↦ by
      by_cases h2 : (basisBits (fullSysCoreWires mPayload) x (iSlot2 mPayload)).val = 0 <;>
        simp [h2])
  have hProj1 : slotBitProj (iSlot2 mPayload) 1 * P_slack = 0 := by
    dsimp only [P_slack, slotBitProj]
    simp only [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_zero]
    exact congrArg Matrix.diagonal (funext fun x ↦ by
      by_cases h2 : (basisBits (fullSysCoreWires mPayload) x (iSlot2 mPayload)).val = 0 <;>
        simp [h2])
  have hComm3 {A : Operator (2 ^ (fullSysCoreWires mPayload))}
      (h2 : A * slotBitProj (iSlot2 mPayload) 0 = slotBitProj (iSlot2 mPayload) 0 * A)
      (h1 : A * slotBitProj (iSlot1 mPayload) 1 = slotBitProj (iSlot1 mPayload) 1 * A)
      (h0 : A * slotBitProj (iSlot0 mPayload) b = slotBitProj (iSlot0 mPayload) b * A) :
      A * P_slack = P_slack * A := by
    dsimp only [P_slack]
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc A, h2, Matrix.mul_assoc,
      ← Matrix.mul_assoc A, h1, Matrix.mul_assoc, h0]
    simp only [Matrix.mul_assoc]
  set U_out := fullSysQftCoreUnitary sel.hmPay qft * sel.uTwist c
  have hInv : (U_out⁻¹).1 * U_out.1 = 1 := congrArg Subtype.val (inv_mul_cancel U_out)
  have hOut_P : U_out.1 * P_slack = P_slack * U_out.1 := by
    simp only [U_out, Submonoid.coe_mul]
    rw [Matrix.mul_assoc, hComm3 hTwist_s2 hTwist_s1 hTwist_s0, ← Matrix.mul_assoc,
      hComm3 (fullSysQftCoreUnitary_comm_slotBitProj sel.hmPay qft (w := iSlot2 mPayload)
          (show 3924 ≤ 3950 by decide) (show 3950 < 3954 by decide) 0)
        (fullSysQftCoreUnitary_comm_slotBitProj sel.hmPay qft (w := iSlot1 mPayload)
          (show 3924 ≤ 3949 by decide) (show 3949 < 3954 by decide) 1)
        (fullSysQftCoreUnitary_comm_slotBitProj sel.hmPay qft (w := iSlot0 mPayload)
          (show 3924 ≤ 3948 by decide) (show 3948 < 3954 by decide) b), Matrix.mul_assoc]
  rw [(fullSysSelectEffUnitary_conjTranspose_and_split qft sel c).1, Matrix.add_mul,
    Matrix.mul_assoc, hProj0, Matrix.mul_assoc, hProj1, Matrix.mul_zero, add_zero,
    fullSysSelectPosUnitary, show fullSysQftCoreUnitary sel.hmPay qft * sel.uTwist c = U_out
      from rfl, unitaryConj_val]
  calc (U_out⁻¹).1 * (sel.uPosPhase c).1 * U_out.1 * P_slack
      = (U_out⁻¹).1 * ((sel.uPosPhase c).1 * P_slack) * U_out.1 := by
          rw [Matrix.mul_assoc _ U_out.1 P_slack, hOut_P]
          simp only [Matrix.mul_assoc]
    _ = (if b.val = 0 then (1 : ℂ) else -1) • ((U_out⁻¹).1 * P_slack * U_out.1) := by
          rw [hPos_slack, Matrix.mul_smul, Matrix.smul_mul]
    _ = (if b.val = 0 then (1 : ℂ) else -1) • (((U_out⁻¹).1 * U_out.1) * P_slack) := by
          rw [Matrix.mul_assoc (U_out⁻¹).1 P_slack U_out.1, ← hOut_P, ← Matrix.mul_assoc]
    _ = (if b.val = 0 then (1 : ℂ) else -1) • P_slack := by
          rw [hInv, Matrix.one_mul]
def smToTwosSysOnActDyn {Var : Type} {mAct mWork n : ℕ} (hm7 : 7 ≤ mWork) (v : Var)
    (rAct : QRegister (SpecsAux.SpecMirror.systemQubits + mAct) n) (rWork : QRegister mWork n)
    (hDisj : rAct.DisjointWires rWork) : DynamicCircuit Var n :=
  smToTwosSysDyn v (rAct.compose (QRegister.block 0 SpecsAux.SpecMirror.systemQubits
      (fullSys_zero_add_le SpecsAux.SpecMirror.systemQubits mAct)))
    (rWork.compose (QRegister.block 0 7 (fullSys_zero_add_le_of_le hm7)))
    ((hDisj.compose_left _).compose_right _)
@[simp] theorem count_toff_smToTwosSysOnActDyn {Var : Type} {mAct mWork n : ℕ}
    (hm7 : 7 ≤ mWork) (v : Var) (rAct : QRegister (SpecsAux.SpecMirror.systemQubits + mAct) n)
    (rWork : QRegister mWork n) (hDisj : rAct.DisjointWires rWork) :
    (smToTwosSysOnActDyn hm7 v rAct rWork hDisj).count .TOFF = 0 := by
  simp [smToTwosSysOnActDyn]
@[simp] theorem count_t_smToTwosSysOnActDyn {Var : Type} {mAct mWork n : ℕ} (hm7 : 7 ≤ mWork)
    (v : Var) (rAct : QRegister (SpecsAux.SpecMirror.systemQubits + mAct) n)
    (rWork : QRegister mWork n) (hDisj : rAct.DisjointWires rWork) :
    (smToTwosSysOnActDyn hm7 v rAct rWork hDisj).count .T = 10536 := by
  simp [smToTwosSysOnActDyn]
theorem realizesCleanWorkspace_smToTwosSysOnActDyn {Var : Type} [Fintype Var] [DecidableEq Var]
    {mAct mWork n : ℕ} [NeZero (2 ^ n)] (hm7 : 7 ≤ mWork) (v : Var)
    (rAct : QRegister (SpecsAux.SpecMirror.systemQubits + mAct) n) (rWork : QRegister mWork n)
    (hDisj : rAct.DisjointWires rWork) :
    DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace rAct rWork ((QRegister.block 0
      SpecsAux.SpecMirror.systemQubits (fullSys_zero_add_le SpecsAux.SpecMirror.systemQubits
      mAct)).embedUnitary smToTwosSysUnitary) (smToTwosSysOnActDyn hm7 v rAct rWork hDisj) :=
  ((smToTwosSysDyn_realizes v _ _ _).widenWorkspace).widenActive
theorem smToTwosSysOnAct_inv_eq {mAct : ℕ} : ((QRegister.block 0 SpecsAux.SpecMirror.systemQubits
    (fullSys_zero_add_le SpecsAux.SpecMirror.systemQubits mAct)).embedUnitary smToTwosSysUnitary)⁻¹
      =
    (QRegister.block 0 SpecsAux.SpecMirror.systemQubits (fullSys_zero_add_le
      SpecsAux.SpecMirror.systemQubits mAct)).embedUnitary smToTwosSysUnitary :=
  mul_eq_one_iff_inv_eq.mp <| by
    rw [← QRegister.embedUnitary_mul, smToTwosSysUnitary_mul_self, QRegister.embedUnitary_one]
theorem smToTwosSysUnitary_fermionicProjector_conj
    (spinUp : Finset (Fin SpecsAux.SpecMirror.numElectrons)) :
    smToTwosSysUnitary.1 * SpecsAux.SpecMirror.fermionicProjector spinUp * smToTwosSysUnitary.1ᴴ =
      SpecsAux.SpecMirror.fermionicProjector spinUp := by
  rw [smToTwosSys_comm_fermionicProjector spinUp, Matrix.mul_assoc,
    smToTwosSysUnitary_conjTranspose, ← Submonoid.coe_mul, smToTwosSysUnitary_mul_self,
    OneMemClass.coe_one, Matrix.mul_one]
end FullSysCatSegmentBridge
end
end ModFullSysCatSegmentBridge

end QuantumComputation.Specs.StoppingPowerSolution
