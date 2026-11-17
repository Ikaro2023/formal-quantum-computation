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

public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.FastMidKick275

@[expose] public section
set_option allowUnsafeReducibility true

namespace QuantumComputation.Specs.StoppingPowerSolution

section ModPosSlots24OrbitToggleFast288
@[expose] public section
namespace PosSlots24OrbitToggleFast288
open Operator QProg Matrix HermitianMat _root_.DynamicCircuit DynCircuitExt
open scoped Matrix ComplexOrder MatrixOrder BigOperators Circuit.Notation
open OctahedralOrbit
open Dyadic128CoulombMath
open MeasureBranchHadamardSem (bit_cases matrix_ext_ket)
open StreamingBchComparator BchCubeDecoder
open PosSlots24BranchConcrete
theorem ite_pos {α : Sort*} {c : Prop} [Decidable c] (hc : c) {a b : α} :
    ite c a b = a := ite_eq_left hc
theorem ite_neg {α : Sort*} {c : Prop} [Decidable c] (hc : ¬ c) {a b : α} :
    ite c a b = b := ite_eq_right hc
theorem dite_pos {α : Sort*} {c : Prop} [Decidable c] (hc : c) {a : c → α} {b : ¬ c → α} :
    dite c a b = a hc := dite_eq_left hc
theorem dite_neg {α : Sort*} {c : Prop} [Decidable c] (hc : ¬ c) {a : c → α} {b : ¬ c → α} :
    dite c a b = b hc := dite_eq_right hc
@[simp] theorem basisBits_symm_apply_at {q : ℕ} (f : BitAssignment q) (i : Fin q) : basisBits q
    ((basisBitsEquiv q).symm f) i = f i :=
  congrFun ((basisBitsEquiv q).apply_symm_apply f) i
abbrev rawOrbitCoord128 := PosSlots24PartnerMux288.rawOrbitCoord128
noncomputable abbrev orbitRankFin16 := PosSlots24PartnerMux288.orbitRankFin16
private theorem upd_app {M : ℕ} (γ : BitAssignment M) (a w : Wire M) (v : ZMod 2) : Function.update
    γ a v w = if w = a then v else γ w := by
  rcases eq_or_ne w a with rfl | h
  · rw [Function.update_self, ite_pos rfl]
  · rw [Function.update_of_ne h, ite_neg h]
private theorem upd_comm {M : ℕ} {a b : Wire M} (hab : a ≠ b) (γ : BitAssignment M) (u v : ZMod 2) :
    Function.update (Function.update γ a u) b v =
    Function.update (Function.update γ b v) a u := by
  funext w
  simp only [upd_app]
  rcases eq_or_ne w b with rfl | h
  · simp [hab.symm]
  · simp [h]
private theorem cnot_eval_w {M : ℕ} (c t : Wire M) (h : c ≠ t) (γ : BitAssignment M) (w : Wire M) :
    (CliffProg.cnot c t h).eval γ w = if w = t then γ t + γ c else γ w :=
  upd_app γ t w (γ t + γ c)
private theorem x_eval_w {M : ℕ} (q : Wire M) (γ : BitAssignment M) (w : Wire M) : (CliffProg.x
    q).eval γ w = if w = q then γ q + 1 else γ w :=
  upd_app γ q w (γ q + 1)
private theorem seq_eval_w {M : ℕ} (p₁ p₂ : CliffProg M) (γ : BitAssignment M) (w : Wire M) :
    (CliffProg.seq p₁ p₂).eval γ w = p₂.eval (p₁.eval γ) w := rfl
private theorem zmod2_cancel_right : ∀ a b : ZMod 2, a + b + b = a := by decide
private theorem zmod2_swap_a : ∀ x y : ZMod 2, (x + y) + (y + (x + y)) = y := by decide
private theorem zmod2_swap_b : ∀ x y : ZMod 2, y + (x + y) = x := by decide
private theorem zmod2_axis_true_p :
    ∀ s0 b0 b1 : ZMod 2, s0 * b0 + s0 + s0 + b1 = b1 + s0 * b0 := by decide
private theorem wire303_eq_iff (x y : Wire 303) : (x = y) ↔ x.val = y.val := Fin.ext_iff
private theorem fin3_cases : ∀ ax : Fin 3, ax = 0 ∨ ax = 1 ∨ ax = 2 := by decide
private theorem ScopedBlock.ctxCliff_single {M cur curIn : ℕ} (hIn : curIn ≤ M) (hle : cur ≤ curIn)
    (c : CliffProg M) (hc : c.SupportsBelow curIn)
    {s : BitAssignment M → BitAssignment M} {leaf body : TempPhaseProg M} (hB : ScopedBlock M (M -
      curIn) s leaf body) :
    ScopedBlock M (M - cur) (fun β ↦ s (c.eval β)) leaf ((ctxCliffAlloc c).plug body) := by
  rw [ctxCliffAlloc_plug]
  have h := ScopedBlock.withCliffAlloc_block (M := M) (rem := M - cur) (remIn := M - curIn)
    (by omega) (by omega) c (by rw [show M - (M - curIn) = curIn by omega]; exact hc) hB
  exact ⟨h.valid, h.bits, fun β hβ ↦ h.sign β hβ⟩
private theorem ScopedBlock.ctxCliff_append {M cur curIn : ℕ} (hIn : curIn ≤ M) (hle : cur ≤ curIn)
    (c : CliffProg M) (hc : c.SupportsBelow curIn)
    {K : TempCtx M} {s : BitAssignment M → BitAssignment M} {leaf body : TempPhaseProg M} (hK :
      ScopedBlock M (M - curIn) s leaf (K.plug body)) :
    ScopedBlock M (M - cur) (fun β ↦ s (c.eval β)) leaf (((ctxCliffAlloc c).append K).plug body) :=
      by
  rw [TempCtx.append_plug]
  exact ScopedBlock.ctxCliff_single hIn hle c hc hK
private theorem ScopedBlock.ctxTemp_append {M cur : ℕ} (hcur : cur + 1 ≤ M) {hcur' : cur < M}
    (x y : Wire M) (hxy : x ≠ y) {hxy' : x ≠ y} (hx : x.val < cur) (hy : y.val < cur) (hxa : x ≠
      ⟨cur, hcur'⟩) (hya : y ≠ ⟨cur, hcur'⟩) {K : TempCtx M}
    {s : BitAssignment M → BitAssignment M} {leaf body : TempPhaseProg M} (hK : ScopedBlock M (M -
      (cur + 1)) s leaf (K.plug body)) :
    ScopedBlock M (M - cur) (fun β ↦ s (Function.update β ⟨cur, hcur'⟩ (β x * β y))) leaf
    (((ctxTempBit x y ⟨cur, hcur'⟩ hxy' hxa hya).append K).plug body) := by
  rw [TempCtx.append_plug, ctxTempBit_plug]
  have h := ScopedBlock.withTempBit_block (M := M) cur hcur x y hxy hx hy hK
  exact ⟨h.valid, h.bits, fun β hβ ↦ h.sign β hβ⟩
private theorem ScopedBlock.ctxSandwich_append {M cur : ℕ} (hcur : cur + 1 ≤ M) {hcur' : cur < M}
    (cPre cPost : CliffProg M)
    (x y : Wire M) (hxy : x ≠ y) {hxy' : x ≠ y} (hx : x.val < cur) (hy : y.val < cur) (hxa : x ≠
      ⟨cur, hcur'⟩) (hya : y ≠ ⟨cur, hcur'⟩)
    (hsPre : cPre.SupportsBelow cur) (hsPost : cPost.SupportsBelow (cur + 1))
    {K : TempCtx M} {s : BitAssignment M → BitAssignment M} {leaf body : TempPhaseProg M} (hK :
      ScopedBlock M (M - (cur + 1)) s leaf (K.plug body)) :
    ScopedBlock M (M - cur) (fun β ↦ s (cPost.eval (Function.update (cPre.eval β) ⟨cur, hcur'⟩
    (cPre.eval β x * cPre.eval β y)))) leaf (((ctxCliffAlloc cPre).append ((ctxTempBit x y ⟨cur,
      hcur'⟩ hxy' hxa hya).append
    ((ctxCliffAlloc cPost).append K))).plug body) :=
  ScopedBlock.ctxCliff_append (by omega) le_rfl cPre hsPre
    (ScopedBlock.ctxTemp_append hcur x y hxy hx hy hxa hya
      (ScopedBlock.ctxCliff_append hcur le_rfl cPost hsPost hK))
theorem tempCtx_append_count {M : ℕ} (A B : TempCtx M) : (A.append B).countTempAnd = A.countTempAnd
    + B.countTempAnd := by
  have p0 := TempCtx.plug_countTempAnd (A.append B) .nil
  rw [TempCtx.append_plug] at p0
  have p1 := TempCtx.plug_countTempAnd A (B.plug .nil)
  have p2 := TempCtx.plug_countTempAnd B .nil
  dsimp [TempPhaseProg.countTempAnd] at p0 p1 p2
  omega
theorem bitsVal_succ_split {k : ℕ} (f : Fin (k + 1) → ZMod 2) : bitsVal f = (f 0).val + 2 * bitsVal
    (fun j ↦ f j.succ) := by
  rw [bitsVal, Fin.sum_univ_succ]
  simp only [Fin.val_zero, _root_.pow_zero, mul_one, bitsVal, Finset.mul_sum]
  refine congrArg _ (Finset.sum_congr rfl fun j _ ↦ ?_)
  rw [Fin.val_succ, pow_succ]
  ring
theorem bitsVal_injective : ∀ {W : ℕ} {f g : Fin W → ZMod 2},
    bitsVal f = bitsVal g → f = g
  | 0, _, _, _ => funext fun i ↦ Fin.elim0 i
  | _ + 1, f, g, h => by
      rw [bitsVal_succ_split f, bitsVal_succ_split g] at h
      have hf0 := ZMod.val_lt (f 0)
      have hg0 := ZMod.val_lt (g 0)
      exact funext (Fin.cases (ZMod.val_injective 2 (by omega))
        (congrFun (bitsVal_injective (by omega))))
theorem zmod2_sum3_mod2 :
    ∀ x y z : ZMod 2, (x + y + z).val = (x.val + y.val + z.val) % 2 := by decide
def ctxAddMod2Pow {M : ℕ} : (W cur : ℕ) → (cur + W ≤ M) → (src acc : Fin (W + 1) → Wire M) →
    (cin : Wire M) → (∀ i j, src i ≠ acc j) → (∀ i, src i ≠ cin) → (∀ i, acc i ≠ cin) →
    (∀ i, (src i).val < cur) → (∀ i, (acc i).val < cur) → cin.val < cur → TempCtx M
  | 0, _, _, src, acc, cin, hsa, _, hac, _, _, _ =>
      ctxCliffAlloc (.seq (.cnot (src 0) (acc 0) (hsa 0 0)) (.cnot cin (acc 0) (hac 0).symm))
  | W + 1, cur, _, src, acc, cin, hsa, hsc, hac, hs_lt, ha_lt, hc_lt =>
      let cout : Wire M := ⟨cur, by omega⟩
      let cPre := CliffProg.seq
        (.cnot cin (src 0) (hsc 0).symm) (.cnot cin (acc 0) (hac 0).symm)
      let cMid := CliffProg.seq (.cnot cin (src 0) (hsc 0).symm)
        (.seq (.cnot cin cout (wire_ne_of_lt hc_lt)) (.cnot (src 0) (acc 0) (hsa 0 0)))
      (ctxCliffAlloc cPre).append ((ctxTempBit (src 0) (acc 0) cout (hsa 0 0)
        (wire_ne_of_lt (hs_lt 0)) (wire_ne_of_lt (ha_lt 0))).append
          ((ctxCliffAlloc cMid).append (ctxAddMod2Pow W (cur + 1) (by omega)
            (fun j ↦ src j.succ) (fun j ↦ acc j.succ) cout (fun i j ↦ hsa i.succ j.succ)
            (fun i ↦ wire_ne_of_lt (hs_lt i.succ)) (fun i ↦ wire_ne_of_lt (ha_lt i.succ))
            (fun i ↦ lt_trans (hs_lt i.succ) (by omega))
            (fun i ↦ lt_trans (ha_lt i.succ) (by omega)) (Nat.lt_succ_self cur))))
@[simp] theorem ctxAddMod2Pow_countTempAnd {M : ℕ} : ∀ (W cur : ℕ) (hcur : cur + W ≤ M)
    (src acc : Fin (W + 1) → Wire M) (cin : Wire M) (hsa : ∀ i j, src i ≠ acc j)
    (hsc : ∀ i, src i ≠ cin) (hac : ∀ i, acc i ≠ cin) (hs_lt : ∀ i, (src i).val < cur)
    (ha_lt : ∀ i, (acc i).val < cur) (hc_lt : cin.val < cur), (ctxAddMod2Pow W cur hcur src
    acc cin hsa hsc hac hs_lt ha_lt hc_lt).countTempAnd = W
  | 0, _, _, _, _, _, _, _, _, _, _, _ => rfl
  | W + 1, cur, _, _, _, _, _, _, _, _, _, _ => by
      simp only [ctxAddMod2Pow, tempCtx_append_count, ctxCliffAlloc, ctxTempBit,
        TempCtx.countTempAnd]
      rw [ctxAddMod2Pow_countTempAnd W (cur + 1)]
      omega
theorem ctxAddMod2Pow_disj_supp {M : ℕ} {mutW : Wire M → Prop} : ∀ (W cur : ℕ)
    (hcur : cur + W ≤ M) (src acc : Fin (W + 1) → Wire M) (cin : Wire M)
    (hsa : ∀ i j, src i ≠ acc j) (hsc : ∀ i, src i ≠ cin) (hac : ∀ i, acc i ≠ cin)
    (hs_lt : ∀ i, (src i).val < cur) (ha_lt : ∀ i, (acc i).val < cur) (hc_lt : cin.val < cur),
    (∀ i, ¬ mutW (src i)) → (∀ i, ¬ mutW (acc i)) → (¬ mutW cin) →
    (∀ w : Wire M, cur ≤ w.val → ¬ mutW w) → (ctxAddMod2Pow W cur hcur src acc cin hsa hsc hac
    hs_lt ha_lt hc_lt).DisjointFrom mutW ∧ (ctxAddMod2Pow W cur hcur src acc cin hsa hsc hac
    hs_lt ha_lt hc_lt).SupportsBelowCtx (cur + W)
  | 0, _, _, _, _, _, _, _, _, hs_lt, ha_lt, hc_lt, hms, hma, hmc, _ =>
      ⟨ctxCliffAlloc_disjoint ⟨⟨hms 0, hma 0⟩, ⟨hmc, hma 0⟩⟩,
        ctxCliffAlloc_supports ⟨⟨hs_lt 0, ha_lt 0⟩, ⟨hc_lt, ha_lt 0⟩⟩⟩
  | W + 1, cur, _, src, acc, _, hsa, _, _, hs_lt, ha_lt, hc_lt, hms, hma, hmc, hmScr => by
      have hmC : ¬ mutW ⟨cur, by omega⟩ := hmScr _ le_rfl
      obtain ⟨hd, hs⟩ := ctxAddMod2Pow_disj_supp W (cur + 1) (by omega)
        (fun j ↦ src j.succ) (fun j ↦ acc j.succ) ⟨cur, by omega⟩
        (fun i j ↦ hsa i.succ j.succ) (fun i ↦ wire_ne_of_lt (hs_lt i.succ))
        (fun i ↦ wire_ne_of_lt (ha_lt i.succ))
        (fun i ↦ lt_trans (hs_lt i.succ) (by omega))
        (fun i ↦ lt_trans (ha_lt i.succ) (by omega)) (Nat.lt_succ_self cur)
        (fun i ↦ hms i.succ) (fun i ↦ hma i.succ) hmC (fun w hw ↦ hmScr w (by omega))
      have hs0 := lt_trans (hs_lt 0) (Nat.lt_succ_self cur)
      have ha0 := lt_trans (ha_lt 0) (Nat.lt_succ_self cur)
      have hc0 := lt_trans hc_lt (Nat.lt_succ_self cur)
      refine ⟨TempCtx.disjointFrom_append
          (ctxCliffAlloc_disjoint ⟨⟨hmc, hms 0⟩, ⟨hmc, hma 0⟩⟩)
          (TempCtx.disjointFrom_append ⟨hms 0, hma 0, hmC, trivial⟩
            (TempCtx.disjointFrom_append
              (ctxCliffAlloc_disjoint ⟨⟨hmc, hms 0⟩, ⟨⟨hmc, hmC⟩, ⟨hms 0, hma 0⟩⟩⟩) hd)),
        TempCtx.supportsBelowCtx_append (c₁ := cur + 1) (by omega)
          (ctxCliffAlloc_supports ⟨⟨hc0, hs0⟩, ⟨hc0, ha0⟩⟩)
          (TempCtx.supportsBelowCtx_append (c₁ := cur + 1) (by omega)
            ⟨Nat.lt_succ_self cur, trivial⟩
            (TempCtx.supportsBelowCtx_append (c₁ := cur + 1) (by omega)
              (ctxCliffAlloc_supports ⟨⟨hc0, hs0⟩, ⟨⟨hc0, Nat.lt_succ_self cur⟩, ⟨hs0, ha0⟩⟩⟩)
              (by simpa [Nat.add_assoc, Nat.add_comm 1 W] using hs)))⟩
theorem ScopedBlock.ctxAddMod2Pow_block {M : ℕ} : ∀ (W cur : ℕ) (hcur : cur + W ≤ M)
    (src acc : Fin (W + 1) → Wire M) (cin : Wire M) (hsa : ∀ i j, src i ≠ acc j)
    (hsc : ∀ i, src i ≠ cin) (hac : ∀ i, acc i ≠ cin) (_hinjAcc : Function.Injective acc)
    (hs_lt : ∀ i, (src i).val < cur) (ha_lt : ∀ i, (acc i).val < cur) (hc_lt : cin.val < cur)
    (leaf body : TempPhaseProg M) (sBody : BitAssignment M → BitAssignment M), ScopedBlock M
    (M - (cur + W)) sBody leaf body → ∃ setup : BitAssignment M → BitAssignment M, ScopedBlock
    M (M - cur) (fun β ↦ sBody (setup β)) leaf ((ctxAddMod2Pow W cur hcur src acc cin hsa hsc
    hac hs_lt ha_lt hc_lt).plug body) ∧ ∀ β : BitAssignment M, cleanRem M (M - cur) β →
    cleanRem M (M - (cur + W)) (setup β) ∧
    (∀ w : Wire M, w.val < cur → (∀ j, w ≠ acc j) → setup β w = β w) ∧ bitsVal
    (fun j ↦ setup β (acc j)) = (bitsVal (fun j ↦ β (src j)) + bitsVal (fun j ↦ β (acc j)) +
    (β cin).val) % (2 ^ (W + 1))
  | 0, _, hcur, src, acc, cin, hsa, _, hac, _, hs_lt, ha_lt, hc_lt, _, _, _, hBody => by
      let c0 : CliffProg M :=
        .seq (.cnot (src 0) (acc 0) (hsa 0 0)) (.cnot cin (acc 0) (hac 0).symm)
      refine ⟨c0.eval, ScopedBlock.ctxCliff_single hcur le_rfl c0
          ⟨⟨hs_lt 0, ha_lt 0⟩, ⟨hc_lt, ha_lt 0⟩⟩ (hBody.cast_rem (by omega)),
        fun β hβ ↦ ⟨fun w hw ↦ ?_, fun w _ hwne ↦ ?_, ?_⟩⟩
      · rw [c0.eval_outside ⟨⟨hs_lt 0, ha_lt 0⟩, ⟨hc_lt, ha_lt 0⟩⟩ β w (by omega)]
        exact hβ w (by omega)
      · simp only [c0, seq_eval_w, cnot_eval_w, hwne 0, ↓reduceIte]
      · have hbits1 : ∀ g : Fin 1 → ZMod 2, bitsVal g = (g 0).val := fun g ↦ by simp [bitsVal]
        rw [hbits1, hbits1, hbits1]
        simp only [c0, seq_eval_w, cnot_eval_w, (hac 0).symm, ↓reduceIte]
        rw [show β (acc 0) + β (src 0) + β cin = β (src 0) + β (acc 0) + β cin by ring,
          zmod2_sum3_mod2, show 2 ^ (0 + 1) = 2 from rfl]
  | W + 1, cur, _, src, acc, cin, hsa, hsc, hac, hinjAcc, hs_lt, ha_lt, hc_lt,
    leaf, body, sBody, hBody => by
      let cout : Wire M := ⟨cur, by omega⟩
      let cPre := CliffProg.seq
        (.cnot cin (src 0) (hsc 0).symm) (.cnot cin (acc 0) (hac 0).symm)
      let cMid := CliffProg.seq (.cnot cin (src 0) (hsc 0).symm)
        (.seq (.cnot cin cout (wire_ne_of_lt hc_lt)) (.cnot (src 0) (acc 0) (hsa 0 0)))
      obtain ⟨sTail, h4, hSpec4⟩ := ScopedBlock.ctxAddMod2Pow_block W (cur + 1) (by omega)
        (fun j ↦ src j.succ) (fun j ↦ acc j.succ) cout (fun i j ↦ hsa i.succ j.succ)
        (fun i ↦ wire_ne_of_lt (hs_lt i.succ)) (fun i ↦ wire_ne_of_lt (ha_lt i.succ))
        (hinjAcc.comp (Fin.succ_injective (W + 1)))
        (fun i ↦ lt_trans (hs_lt i.succ) (by omega))
        (fun i ↦ lt_trans (ha_lt i.succ) (by omega))
        (Nat.lt_succ_self cur) leaf body sBody (hBody.cast_rem (by omega))
      have hs0 : (src 0).val < cur + 1 := lt_trans (hs_lt 0) (Nat.lt_succ_self cur)
      have ha0 : (acc 0).val < cur + 1 := lt_trans (ha_lt 0) (Nat.lt_succ_self cur)
      have hc0 : cin.val < cur + 1 := lt_trans hc_lt (Nat.lt_succ_self cur)
      let s012 : BitAssignment M → BitAssignment M := fun β ↦ cMid.eval
        (Function.update (cPre.eval β) cout (cPre.eval β (src 0) * cPre.eval β (acc 0)))
      refine ⟨fun β ↦ sTail (s012 β),
        ScopedBlock.ctxSandwich_append (by omega) cPre cMid (src 0) (acc 0) (hsa 0 0)
          (hs_lt 0) (ha_lt 0) (wire_ne_of_lt (hs_lt 0)) (wire_ne_of_lt (ha_lt 0))
          ⟨⟨hc_lt, hs_lt 0⟩, ⟨hc_lt, ha_lt 0⟩⟩
          ⟨⟨hc0, hs0⟩, ⟨⟨hc0, Nat.lt_succ_self cur⟩, ⟨hs0, ha0⟩⟩⟩ h4,
        fun β hβ ↦ ?_⟩
      have hs0co : src 0 ≠ cout := wire_ne_of_lt (hs_lt 0)
      have ha0co : acc 0 ≠ cout := wire_ne_of_lt (ha_lt 0)
      have hcico : cin ≠ cout := wire_ne_of_lt hc_lt
      have hs012_eq : ∀ w : Wire M, s012 β w =
          if w = cout then β cin + (β (src 0) + β cin) * (β (acc 0) + β cin)
          else if w = acc 0 then β (src 0) + β (acc 0) + β cin else β w := fun w ↦ by
        dsimp only [s012, cMid, cPre]
        simp only [seq_eval_w, cnot_eval_w, upd_app, hsa 0 0, (hsa 0 0).symm,
          (hsc 0).symm, (hac 0).symm, hs0co, hs0co.symm, ha0co, hcico,
          zmod2_cancel_right, ↓reduceIte]
        rcases eq_or_ne w cout with rfl | hwc
        · simp only [ha0co.symm, ↓reduceIte]
          ring
        · rcases eq_or_ne w (acc 0) with rfl | hwa
          · simp only [ha0co, ↓reduceIte]
            ring
          · rcases eq_or_ne w (src 0) with rfl | hws
            · simp [hs0co, hsa 0 0]
            · simp [hwc, hwa, hws]
      obtain ⟨hcl4, hkeep4, hval4⟩ := hSpec4 (s012 β) fun w hw ↦ by
        rw [hs012_eq,
          ite_neg (wire_ne_of_gt (lt_of_lt_of_le (Nat.lt_succ_self cur) (by omega))),
          ite_neg (wire_ne_of_gt (lt_of_lt_of_le ha0 (by omega)))]
        exact hβ w (by omega)
      have hsrc_t : (fun j : Fin (W + 1) ↦ s012 β (src j.succ)) = fun j ↦ β (src j.succ) :=
        funext fun j ↦ by
          rw [hs012_eq, ite_neg (wire_ne_of_lt (hs_lt j.succ)), ite_neg (hsa j.succ 0)]
      have hacc_t : (fun j : Fin (W + 1) ↦ s012 β (acc j.succ)) = fun j ↦ β (acc j.succ) :=
        funext fun j ↦ by
          rw [hs012_eq, ite_neg (wire_ne_of_lt (ha_lt j.succ)),
            ite_neg (fun h ↦ Fin.succ_ne_zero j (hinjAcc h))]
      have hacc0 : sTail (s012 β) (acc 0) = β (src 0) + β (acc 0) + β cin := by
        rw [hkeep4 (acc 0) ha0 (fun j h ↦ Fin.succ_ne_zero j (hinjAcc h.symm)),
          hs012_eq, ite_neg ha0co, ite_pos rfl]
      refine ⟨by simpa [Nat.add_assoc, Nat.add_comm 1 W] using hcl4, fun w hw hwne ↦ ?_, ?_⟩
      · dsimp only
        rw [hkeep4 w (by omega) (fun j ↦ hwne j.succ),
          hs012_eq, ite_neg (wire_ne_of_lt hw), ite_neg (hwne 0)]
      · dsimp only
        rw [bitsVal_succ_split, hacc0, hval4, hsrc_t, hacc_t, hs012_eq cout, ite_pos rfl,
          bitsVal_succ_split (fun j ↦ β (src j)), bitsVal_succ_split (fun j ↦ β (acc j))]
        have hfa := fullAdd_val_eq (β (src 0)) (β (acc 0)) (β cin)
        have hlt0 : (β (src 0) + β (acc 0) + β cin).val < 2 := ZMod.val_lt _
        set M2 := 2 ^ (W + 1)
        set Q := bitsVal (fun j ↦ β (src j.succ)) + bitsVal (fun j ↦ β (acc j.succ)) +
          (β cin + (β (src 0) + β cin) * (β (acc 0) + β cin)).val
        set R := (β (src 0) + β (acc 0) + β cin).val
        have hltQ : Q % M2 < M2 := Nat.mod_lt Q (by positivity)
        have h1 : R + 2 * Q = (R + 2 * (Q % M2)) + (2 * M2) * (Q / M2) := by
          nth_rw 1 [(Nat.div_add_mod Q M2).symm]
          ring
        rw [show 2 ^ (W + 2) = 2 * M2 by ring,
          ← Nat.mod_eq_of_lt (show R + 2 * (Q % M2) < 2 * M2 by omega),
          ← Nat.add_mul_mod_self_left (R + 2 * (Q % M2)) (2 * M2) (Q / M2), ← h1]
        congr 1
        omega
def ctxLtStep {M : ℕ} (cur : ℕ) (hcur : cur + 1 ≤ M) (a b prev : Wire M) (hab : a ≠ b) (ha : a.val <
    cur) (hb : b.val < cur) (hp : prev.val < cur)
    (hbp : b ≠ prev) : TempCtx M :=
  let out : Wire M := ⟨cur, by omega⟩
  (ctxCliffAlloc (.seq (.cnot b a hab.symm) (.cnot prev b hbp.symm))).append
    ((ctxTempBit a b out hab (wire_ne_of_lt ha) (wire_ne_of_lt hb)).append
      (ctxCliffAlloc (.seq (.cnot prev b hbp.symm)
        (.seq (.cnot b a hab.symm) (.cnot prev out (wire_ne_of_lt hp))))))
@[simp] theorem ctxLtStep_plug {M : ℕ} (cur : ℕ) (hcur : cur + 1 ≤ M) (a b prev : Wire M)
    (hab : a ≠ b) (ha : a.val < cur) (hb : b.val < cur) (hp : prev.val < cur) (hbp : b ≠ prev)
    (body : TempPhaseProg M) : (ctxLtStep cur hcur a b prev hab ha hb hp hbp).plug body = withLtStep
      cur hcur a b prev hab ha hb hp hbp body := by
  simp [ctxLtStep, withLtStep, TempCtx.append_plug]
def ctxLtCompLoop {M : ℕ} : (W cur : ℕ) → (cur + W + 1 ≤ M) → (a b : Fin W → Wire M) →
    (∀ j, a j ≠ b j) → (∀ j, (a j).val < cur) → (∀ j, (b j).val < cur) → TempCtx M
  | 0, _, _, _, _, _, _, _ => .hole
  | W + 1, cur, _, a, b, hab, ha, hb =>
      (ctxLtStep (cur + 1) (by omega) (a 0) (b 0) ⟨cur, by omega⟩ (hab 0)
        (lt_trans (ha 0) (Nat.lt_succ_self cur)) (lt_trans (hb 0) (Nat.lt_succ_self cur))
        (Nat.lt_succ_self cur) (wire_ne_of_lt (hb 0))).append
        (ctxLtCompLoop W (cur + 1) (by omega) (fun j ↦ a j.succ) (fun j ↦ b j.succ)
          (fun j ↦ hab j.succ) (fun j ↦ lt_trans (ha j.succ) (Nat.lt_succ_self cur))
          (fun j ↦ lt_trans (hb j.succ) (Nat.lt_succ_self cur)))
@[simp] theorem ctxLtCompLoop_plug {M : ℕ} : ∀ (W cur : ℕ) (hcur : cur + W + 1 ≤ M)
    (a b : Fin W → Wire M) (hab : ∀ j, a j ≠ b j) (ha : ∀ j, (a j).val < cur)
    (hb : ∀ j, (b j).val < cur) (body : TempPhaseProg M),
    (ctxLtCompLoop W cur hcur a b hab ha hb).plug body = withLtCompLoop W cur hcur a b hab ha
    hb body
  | 0, _, _, _, _, _, _, _, _ => rfl
  | W + 1, cur, _, _, _, _, _, _, _ => by
      simp only [ctxLtCompLoop, withLtCompLoop, TempCtx.append_plug, ctxLtStep_plug]
      rw [ctxLtCompLoop_plug W (cur + 1)]
def ctxDeltaSwapReg {M : ℕ} : (W cur : ℕ) → (cur + W ≤ M) → (ctrl : Wire M) →
    (regA regB : Fin W → Wire M) → (∀ i, regA i ≠ regB i) → (∀ i, ctrl ≠ regA i) →
    ctrl.val < cur → (∀ i, (regA i).val < cur) → (∀ i, (regB i).val < cur) → TempCtx M
  | 0, _, _, _, _, _, _, _, _, _, _ => .hole
  | W + 1, cur, _, ctrl, regA, regB, hab, hca, hc_lt, ha_lt, hb_lt =>
      let dk : Wire M := ⟨cur, by omega⟩
      let cPost : CliffProg M := .seq (.cnot (regB 0) (regA 0) (hab 0).symm)
        (.seq (.cnot dk (regA 0) (wire_ne_of_gt (ha_lt 0)))
          (.cnot dk (regB 0) (wire_ne_of_gt (hb_lt 0))))
      (ctxCliffAlloc (.cnot (regB 0) (regA 0) (hab 0).symm)).append
        ((ctxTempBit ctrl (regA 0) dk (hca 0) (wire_ne_of_lt hc_lt)
          (wire_ne_of_lt (ha_lt 0))).append ((ctxCliffAlloc cPost).append
            (ctxDeltaSwapReg W (cur + 1) (by omega) ctrl (fun j ↦ regA j.succ)
              (fun j ↦ regB j.succ) (fun j ↦ hab j.succ) (fun j ↦ hca j.succ)
              (lt_trans hc_lt (Nat.lt_succ_self cur))
              (fun j ↦ lt_trans (ha_lt j.succ) (Nat.lt_succ_self cur))
              (fun j ↦ lt_trans (hb_lt j.succ) (Nat.lt_succ_self cur)))))
@[simp] theorem ctxDeltaSwapReg_countTempAnd {M : ℕ} : ∀ (W cur : ℕ) (hcur : cur + W ≤ M)
    (ctrl : Wire M) (regA regB : Fin W → Wire M) (hab : ∀ i, regA i ≠ regB i)
    (hca : ∀ i, ctrl ≠ regA i) (hc_lt : ctrl.val < cur) (ha_lt : ∀ i, (regA i).val < cur)
    (hb_lt : ∀ i, (regB i).val < cur), (ctxDeltaSwapReg W cur hcur ctrl regA regB hab hca
    hc_lt ha_lt hb_lt).countTempAnd = W
  | 0, _, _, _, _, _, _, _, _, _, _ => rfl
  | W + 1, cur, _, _, _, _, _, _, _, _, _ => by
      simp only [ctxDeltaSwapReg, tempCtx_append_count, ctxCliffAlloc, ctxTempBit,
        TempCtx.countTempAnd]
      rw [ctxDeltaSwapReg_countTempAnd W (cur + 1)]
      omega
private theorem ScopedBlock.ctxDeltaSwapReg_block {M : ℕ} : ∀ (W cur : ℕ) (hcur : cur + W ≤ M)
    (ctrl : Wire M) (regA regB : Fin W → Wire M) (hab : ∀ i, regA i ≠ regB i)
    (hca : ∀ i, ctrl ≠ regA i) (_hcb : ∀ i, ctrl ≠ regB i) (_hinjA : Function.Injective regA)
    (_hinjB : Function.Injective regB) (_hdisjAB : ∀ i j, regA i ≠ regB j)
    (hc_lt : ctrl.val < cur) (ha_lt : ∀ i, (regA i).val < cur)
    (hb_lt : ∀ i, (regB i).val < cur) (leaf body : TempPhaseProg M)
    (sBody : BitAssignment M → BitAssignment M),
    ScopedBlock M (M - (cur + W)) sBody leaf body →
    ∃ setup : BitAssignment M → BitAssignment M, ScopedBlock M (M - cur)
      (fun β ↦ sBody (setup β)) leaf
      ((ctxDeltaSwapReg W cur hcur ctrl regA regB hab hca hc_lt ha_lt hb_lt).plug body) ∧
    ∀ β : BitAssignment M, cleanRem M (M - cur) β → cleanRem M (M - (cur + W)) (setup β) ∧
      (∀ w : Wire M, w.val < cur → (∀ j, w ≠ regA j) → (∀ j, w ≠ regB j) → setup β w = β w) ∧
      (∀ j, setup β (regA j) = if β ctrl = 1 then β (regB j) else β (regA j)) ∧
      (∀ j, setup β (regB j) = if β ctrl = 1 then β (regA j) else β (regB j))
  | 0, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hBody =>
      ⟨id, hBody, fun _ hβ ↦
        ⟨by simpa using hβ, fun _ _ _ _ ↦ rfl, fun j ↦ Fin.elim0 j, fun j ↦ Fin.elim0 j⟩⟩
  | W + 1, cur, _, ctrl, regA, regB, hab, hca, hcb, hinjA, hinjB, hdisjAB, hc_lt, ha_lt,
    hb_lt, leaf, body, sBody, hBody => by
      let dk : Wire M := ⟨cur, by omega⟩
      let cPost : CliffProg M := .seq (.cnot (regB 0) (regA 0) (hab 0).symm)
        (.seq (.cnot dk (regA 0) (wire_ne_of_gt (ha_lt 0)))
          (.cnot dk (regB 0) (wire_ne_of_gt (hb_lt 0))))
      obtain ⟨sTail, h4, hSpec4⟩ := ScopedBlock.ctxDeltaSwapReg_block W (cur + 1) (by omega)
        ctrl (fun j ↦ regA j.succ) (fun j ↦ regB j.succ) (fun j ↦ hab j.succ)
        (fun j ↦ hca j.succ) (fun j ↦ hcb j.succ)
        (hinjA.comp (Fin.succ_injective W)) (hinjB.comp (Fin.succ_injective W))
        (fun i j ↦ hdisjAB i.succ j.succ) (lt_trans hc_lt (Nat.lt_succ_self cur))
        (fun j ↦ lt_trans (ha_lt j.succ) (Nat.lt_succ_self cur))
        (fun j ↦ lt_trans (hb_lt j.succ) (Nat.lt_succ_self cur))
        leaf body sBody (hBody.cast_rem (by omega))
      have ha0 : (regA 0).val < cur + 1 := lt_trans (ha_lt 0) (Nat.lt_succ_self cur)
      have hb0 : (regB 0).val < cur + 1 := lt_trans (hb_lt 0) (Nat.lt_succ_self cur)
      let cPre := CliffProg.cnot (regB 0) (regA 0) (hab 0).symm
      let s012 : BitAssignment M → BitAssignment M := fun β ↦ cPost.eval
        (Function.update (cPre.eval β) dk (cPre.eval β ctrl * cPre.eval β (regA 0)))
      refine ⟨fun β ↦ sTail (s012 β),
        ScopedBlock.ctxSandwich_append (by omega) cPre cPost ctrl (regA 0) (hca 0)
          hc_lt (ha_lt 0) (wire_ne_of_lt hc_lt) (wire_ne_of_lt (ha_lt 0)) ⟨hb_lt 0, ha_lt 0⟩
          ⟨⟨hb0, ha0⟩, ⟨⟨Nat.lt_succ_self cur, ha0⟩, ⟨Nat.lt_succ_self cur, hb0⟩⟩⟩ h4,
        fun β hβ ↦ ?_⟩
      obtain ⟨hAlgA, hAlgB⟩ := cswapBit_algebra (β ctrl) (β (regA 0)) (β (regB 0))
      have had : regA 0 ≠ dk := wire_ne_of_lt (ha_lt 0)
      have hbd : regB 0 ≠ dk := wire_ne_of_lt (hb_lt 0)
      have hs012_eq : ∀ w : Wire M, s012 β w = if w = dk then β ctrl * (β (regA 0) + β (regB 0))
          else if w = regA 0 then if β ctrl = 1 then β (regB 0) else β (regA 0)
          else if w = regB 0 then if β ctrl = 1 then β (regA 0) else β (regB 0) else β w :=
        fun w ↦ by
          dsimp only [s012, cPost, cPre]
          simp only [seq_eval_w, cnot_eval_w, upd_app, had, had.symm, hbd,
            (hab 0).symm, hca 0, zmod2_cancel_right, ↓reduceIte]
          rcases eq_or_ne w dk with rfl | hwd
          · simp [hbd.symm, had.symm]
          · rcases eq_or_ne w (regA 0) with rfl | hwa
            · simp only [hab 0, had, ↓reduceIte]
              rw [← hAlgA, ← add_assoc, add_comm (β (regA 0) + β (regB 0)), zmod2_swap_b]
            · rcases eq_or_ne w (regB 0) with rfl | hwb
              · simp [hbd, (hab 0).symm, hAlgB]
              · simp [hwd, hwa, hwb]
      obtain ⟨hcl4, hkeep4, hA4, hB4⟩ := hSpec4 (s012 β) fun w hw ↦ by
        rw [hs012_eq,
          ite_neg (wire_ne_of_gt (lt_of_lt_of_le (Nat.lt_succ_self cur) (by omega))),
          ite_neg (wire_ne_of_gt (lt_of_lt_of_le ha0 (by omega))),
          ite_neg (wire_ne_of_gt (lt_of_lt_of_le hb0 (by omega)))]
        exact hβ w (by omega)
      have hc_eq : s012 β ctrl = β ctrl := by
        rw [hs012_eq, ite_neg (wire_ne_of_lt hc_lt), ite_neg (hca 0), ite_neg (hcb 0)]
      have hAk : ∀ k : Fin W, s012 β (regA k.succ) = β (regA k.succ) := fun k ↦ by
        rw [hs012_eq, ite_neg (wire_ne_of_lt (ha_lt k.succ)),
          ite_neg (fun h ↦ Fin.succ_ne_zero k (hinjA h)), ite_neg (hdisjAB k.succ 0)]
      have hBk : ∀ k : Fin W, s012 β (regB k.succ) = β (regB k.succ) := fun k ↦ by
        rw [hs012_eq, ite_neg (wire_ne_of_lt (hb_lt k.succ)),
          ite_neg (fun h ↦ hdisjAB 0 k.succ h.symm),
          ite_neg (fun h ↦ Fin.succ_ne_zero k (hinjB h))]
      refine ⟨by simpa [Nat.add_assoc, Nat.add_comm 1 W] using hcl4,
        fun w hw hneA hneB ↦ ?_, fun j ↦ ?_, fun j ↦ ?_⟩
      · dsimp only
        rw [hkeep4 w (by omega) (fun j ↦ hneA j.succ) (fun j ↦ hneB j.succ),
          hs012_eq, ite_neg (wire_ne_of_lt hw), ite_neg (hneA 0), ite_neg (hneB 0)]
      · dsimp only
        rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨k, rfl⟩
        · rw [hkeep4 (regA 0) ha0 (fun k h ↦ Fin.succ_ne_zero k (hinjA h.symm))
              (fun k ↦ hdisjAB 0 k.succ), hs012_eq, ite_neg had, ite_pos rfl]
        · rw [hA4 k, hc_eq, hBk k, hAk k]
      · dsimp only
        rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨k, rfl⟩
        · rw [hkeep4 (regB 0) hb0 (fun k ↦ (hdisjAB k.succ 0).symm)
              (fun k h ↦ Fin.succ_ne_zero k (hinjB h.symm)),
            hs012_eq, ite_neg hbd, ite_neg (hab 0).symm, ite_pos rfl]
        · rw [hB4 k, hc_eq, hAk k, hBk k]
def ctxMinMaxInPlace {M : ℕ} (W cur : ℕ) (hcur : cur + 2 * W + 1 ≤ M) (regA regB : Fin W → Wire M)
    (hab : ∀ i, regA i ≠ regB i)
    (ha_lt : ∀ i, (regA i).val < cur) (hb_lt : ∀ i, (regB i).val < cur) : TempCtx M :=
  (ctxLtCompLoop W cur (by omega) regB regA (fun i ↦ (hab i).symm) hb_lt ha_lt).append
    (ctxDeltaSwapReg W (cur + W + 1) (by omega) ⟨cur + W, by omega⟩ regA regB hab
      (fun i ↦ wire_ne_of_gt (Nat.lt_add_right W (ha_lt i))) (Nat.lt_succ_self (cur + W))
      (fun i ↦ lt_of_lt_of_le (ha_lt i) (by omega))
      (fun i ↦ lt_of_lt_of_le (hb_lt i) (by omega)))
@[simp] theorem ctxMinMaxInPlace_countTempAnd {M : ℕ} (W cur : ℕ) (hcur : cur + 2 * W + 1 ≤ M) (regA
    regB : Fin W → Wire M) (hab : ∀ i, regA i ≠ regB i)
    (ha_lt : ∀ i, (regA i).val < cur) (hb_lt : ∀ i,
      (regB i).val < cur) : (ctxMinMaxInPlace W cur hcur regA regB hab ha_lt hb_lt).countTempAnd = 2
      * W := by
  have hp := TempCtx.plug_countTempAnd
    (ctxLtCompLoop W cur (by omega) regB regA (fun i ↦ (hab i).symm) hb_lt ha_lt) .nil
  rw [ctxLtCompLoop_plug, withLtCompLoop_countTempAnd] at hp
  dsimp [TempPhaseProg.countTempAnd] at hp
  rw [ctxMinMaxInPlace, tempCtx_append_count, ctxDeltaSwapReg_countTempAnd]
  omega
private theorem ScopedBlock.ctxMinMaxInPlace_block {M : ℕ} (W cur : ℕ)
    (hcur : cur + 2 * W + 1 ≤ M) (regA regB : Fin W → Wire M) (hab : ∀ i, regA i ≠ regB i)
    (hinjA : Function.Injective regA) (hinjB : Function.Injective regB) (hdisjAB : ∀ i j,
      regA i ≠ regB j) (ha_lt : ∀ i, (regA i).val < cur)
    (hb_lt : ∀ i, (regB i).val < cur) (leaf body : TempPhaseProg M) (sBody : BitAssignment M →
      BitAssignment M)
    (hBody : ScopedBlock M (M - (cur + 2 * W + 1)) sBody leaf body) : ∃ setup : BitAssignment M →
      BitAssignment M, ScopedBlock M (M - cur)
    (fun β ↦ sBody (setup β)) leaf ((ctxMinMaxInPlace W cur hcur regA regB hab ha_lt hb_lt).plug
      body) ∧ ∀ β : BitAssignment M, cleanRem M (M - cur) β →
    cleanRem M (M - (cur + 2 * W + 1)) (setup β) ∧ (∀ w : Wire M, w.val < cur → (∀ j,
      w ≠ regA j) → (∀ j, w ≠ regB j) → setup β w = β w) ∧
    bitsVal (fun j ↦ setup β (regA j)) = min (bitsVal (fun j ↦ β (regA j))) (bitsVal (fun j ↦ β
      (regB j))) ∧ bitsVal (fun j ↦ setup β (regB j)) =
    max (bitsVal (fun j ↦ β (regA j))) (bitsVal (fun j ↦ β (regB j))) := by
  let ltWire : Wire M := ⟨cur + W, by omega⟩
  obtain ⟨sSwap, hSwap, hSpecSwap⟩ := ScopedBlock.ctxDeltaSwapReg_block W (cur + W + 1)
    (by omega) ltWire regA regB hab (fun i ↦ wire_ne_of_gt (Nat.lt_add_right W (ha_lt i)))
    (fun i ↦ wire_ne_of_gt (Nat.lt_add_right W (hb_lt i))) hinjA hinjB hdisjAB
    (Nat.lt_succ_self (cur + W)) (fun i ↦ lt_of_lt_of_le (ha_lt i) (by omega))
    (fun i ↦ lt_of_lt_of_le (hb_lt i) (by omega)) leaf body sBody (hBody.cast_rem (by omega))
  obtain ⟨sCmp, hCmp, hSpecCmp⟩ := ScopedBlock.withLtCompLoop_block W cur (by omega)
    regB regA (fun i ↦ (hab i).symm) hb_lt ha_lt leaf _ (fun β ↦ sBody (sSwap β)) hSwap
  have hBlk : ScopedBlock M (M - cur) (fun β ↦ sBody (sSwap (sCmp β))) leaf ((ctxMinMaxInPlace W cur
    hcur regA regB hab ha_lt hb_lt).plug body) := by
    dsimp only [ctxMinMaxInPlace]
    rw [TempCtx.append_plug, ctxLtCompLoop_plug]
    exact ⟨validCleanRem_mono (by omega) hCmp.valid,
      fun β hβ ↦ hCmp.bits β (cleanRem_anti (by omega) hβ),
      fun β hβ ↦ hCmp.sign β (cleanRem_anti (by omega) hβ)⟩
  refine ⟨fun β ↦ sSwap (sCmp β), hBlk, fun β hβ ↦ ?_⟩
  obtain ⟨hcl1, hbelow1, hlt_iff⟩ := hSpecCmp β (cleanRem_anti (by omega) hβ)
  have hcur0 : β ⟨cur, by omega⟩ = 0 := hβ _ (show M - (M - cur) ≤ cur by omega)
  obtain ⟨hcl2, hkeep2, hA2, hB2⟩ := hSpecSwap (sCmp β) hcl1
  refine ⟨by simpa [show cur + W + 1 + W = cur + 2 * W + 1 by omega] using hcl2,
    fun w hw hneA hneB ↦ (hkeep2 w (by omega) hneA hneB).trans (hbelow1 w hw), ?_⟩
  dsimp only
  by_cases hlt1 : sCmp β ltWire = 1
  · have hba : bitsVal (fun j ↦ β (regB j)) < bitsVal (fun j ↦ β (regA j)) := by
      simpa [hcur0] using hlt_iff.mp hlt1
    rw [show (fun j ↦ sSwap (sCmp β) (regA j)) = fun j ↦ β (regB j) from
        funext fun j ↦ by rw [hA2 j, ite_pos hlt1, hbelow1 _ (hb_lt j)],
      show (fun j ↦ sSwap (sCmp β) (regB j)) = fun j ↦ β (regA j) from
        funext fun j ↦ by rw [hB2 j, ite_pos hlt1, hbelow1 _ (ha_lt j)]]
    exact ⟨by omega, by omega⟩
  · have hge : bitsVal (fun j ↦ β (regA j)) ≤ bitsVal (fun j ↦ β (regB j)) :=
      not_lt.mp fun h ↦ hlt1 (hlt_iff.mpr (Or.inl h))
    rw [show (fun j ↦ sSwap (sCmp β) (regA j)) = fun j ↦ β (regA j) from
        funext fun j ↦ by rw [hA2 j, ite_neg hlt1, hbelow1 _ (ha_lt j)],
      show (fun j ↦ sSwap (sCmp β) (regB j)) = fun j ↦ β (regB j) from
        funext fun j ↦ by rw [hB2 j, ite_neg hlt1, hbelow1 _ (hb_lt j)]]
    exact ⟨by omega, by omega⟩
theorem supportsBelowCtx_mono {M c₁ c₂ : ℕ} (hle : c₁ ≤ c₂) :
    ∀ {K : TempCtx M}, K.SupportsBelowCtx c₁ → K.SupportsBelowCtx c₂
  | .hole, _ => trivial
  | .seqPre _ _, ⟨h₁, h₂⟩ =>
      ⟨CliffProg.supportsBelow_mono hle h₁, supportsBelowCtx_mono hle h₂⟩
  | .seqPost _ _, ⟨h₁, h₂⟩ =>
      ⟨supportsBelowCtx_mono hle h₁, CliffProg.supportsBelow_mono hle h₂⟩
  | .tempAnd _ _ _ _ _ _ _, ⟨h₁, h₂⟩ => ⟨lt_of_lt_of_le h₁ hle, supportsBelowCtx_mono hle h₂⟩
theorem TempCtx.fwdBits_mut {M : ℕ} {mutW : Wire M → Prop} :
    ∀ {K : TempCtx M}, K.DisjointFrom mutW → ∀ (β : BitAssignment M) {w : Wire M},
      mutW w → K.fwdBits β w = β w
  | .hole, _, _, _, _ => rfl
  | .seqPre c _, hD, β, _, hw => (fwdBits_mut hD.2 (c.eval β) hw).trans (hD.1.eval_mut β hw)
  | .seqPost _ _, hD, β, _, hw => fwdBits_mut hD.1 β hw
  | .tempAnd _ _ _ _ _ _ _, hD, β, _, hw =>
      (fwdBits_mut hD.2.2.2 _ hw).trans
        (Function.update_of_ne (fun e ↦ hD.2.2.1 (by rwa [← e])) _ _)
def fanoutCnot {M : ℕ} : (W : ℕ) → (ctrl : Wire M) → (dst : Fin W → Wire M) →
    (∀ j, ctrl ≠ dst j) → CliffProg M
  | 0, _, _, _ => .nil
  | W + 1, ctrl, dst, hne =>
      .seq (.cnot ctrl (dst 0) (hne 0))
        (fanoutCnot W ctrl (fun j ↦ dst j.succ) (fun j ↦ hne j.succ))
theorem fanoutCnot_supportsBelow {M : ℕ} : ∀ (W : ℕ) (ctrl : Wire M) (dst : Fin W → Wire M)
    (hne : ∀ j, ctrl ≠ dst j) (c : ℕ), ctrl.val < c → (∀ j, (dst j).val < c) →
    (fanoutCnot W ctrl dst hne).SupportsBelow c
  | 0, _, _, _, _, _, _ => trivial
  | W + 1, ctrl, dst, hne, c, hc, hd =>
      ⟨⟨hc, hd 0⟩, fanoutCnot_supportsBelow W ctrl (fun j ↦ dst j.succ)
        (fun j ↦ hne j.succ) c hc (fun j ↦ hd j.succ)⟩
theorem fanoutCnot_eval {M : ℕ} : ∀ (W : ℕ) (ctrl : Wire M) (dst : Fin W → Wire M)
    (hne : ∀ j, ctrl ≠ dst j), Function.Injective dst → ∀ (β : BitAssignment M) (w : Wire M),
    (fanoutCnot W ctrl dst hne).eval β w = if ∃ j, w = dst j then β w + β ctrl else β w
  | 0, _, _, _, _, _, _ => by simp [fanoutCnot, CliffProg.eval]
  | W + 1, ctrl, dst, hne, hinj, β, w => by
      dsimp only [fanoutCnot, CliffProg.eval]
      let β₁ := Function.update β (dst 0) (β (dst 0) + β ctrl)
      rw [fanoutCnot_eval W ctrl (fun j ↦ dst j.succ) (fun j ↦ hne j.succ)
        (hinj.comp (Fin.succ_injective W)) β₁ w,
        show β₁ ctrl = β ctrl from Function.update_of_ne (hne 0) _ _]
      rcases eq_or_ne w (dst 0) with rfl | h0
      · have hnone : ¬ ∃ j : Fin W, dst 0 = dst j.succ :=
          fun ⟨j, hj⟩ ↦ Fin.succ_ne_zero j (hinj hj.symm)
        simp [hnone, show ∃ i, dst 0 = dst i from ⟨0, rfl⟩, β₁, Function.update_self]
      · by_cases hs : ∃ j : Fin W, w = dst j.succ
        · obtain ⟨j, rfl⟩ := hs
          simp [show ∃ j' : Fin W, dst j.succ = dst j'.succ from ⟨j, rfl⟩,
            show ∃ i, dst j.succ = dst i from ⟨j.succ, rfl⟩, β₁, Function.update_of_ne h0]
        · have hall : ¬ ∃ i, w = dst i := fun ⟨i, hi⟩ ↦
            Fin.cases (fun h : w = dst 0 ↦ h0 h) (fun j h ↦ hs ⟨j, h⟩) i hi
          simp [hs, hall, β₁, Function.update_of_ne h0]
def ctxAndNotVec {M : ℕ} : (W cur : ℕ) → (cur + W ≤ M) → (ctrl : Wire M) →
    (src : Fin W → Wire M) → (∀ k, ctrl ≠ src k) → ctrl.val < cur →
    (∀ k, (src k).val < cur) → TempCtx M
  | 0, _, _, _, _, _, _, _ => .hole
  | W + 1, cur, _, ctrl, src, hc_src, hc_lt, hs_lt =>
      (ctxCliffAlloc (.x (src 0))).append ((ctxTempBit ctrl (src 0) ⟨cur, by omega⟩ (hc_src 0)
        (wire_ne_of_lt hc_lt) (wire_ne_of_lt (hs_lt 0))).append
          ((ctxCliffAlloc (.x (src 0))).append (ctxAndNotVec W (cur + 1) (by omega) ctrl
            (fun k ↦ src k.succ) (fun k ↦ hc_src k.succ)
            (lt_trans hc_lt (Nat.lt_succ_self cur))
            (fun k ↦ lt_trans (hs_lt k.succ) (Nat.lt_succ_self cur)))))
@[simp] theorem ctxAndNotVec_countTempAnd {M : ℕ} : ∀ (W cur : ℕ) (hcur : cur + W ≤ M)
    (ctrl : Wire M) (src : Fin W → Wire M) (hc_src : ∀ k, ctrl ≠ src k)
    (hc_lt : ctrl.val < cur) (hs_lt : ∀ k, (src k).val < cur),
    (ctxAndNotVec W cur hcur ctrl src hc_src hc_lt hs_lt).countTempAnd = W
  | 0, _, _, _, _, _, _, _ => rfl
  | W + 1, cur, _, _, _, _, _, _ => by
      simp only [ctxAndNotVec, tempCtx_append_count, ctxCliffAlloc, ctxTempBit,
        TempCtx.countTempAnd]
      rw [ctxAndNotVec_countTempAnd W (cur + 1)]
      omega
private theorem ScopedBlock.ctxAndNotVec_block {M : ℕ} : ∀ (W cur : ℕ) (hcur : cur + W ≤ M)
    (ctrl : Wire M) (src : Fin W → Wire M) (hc_src : ∀ k, ctrl ≠ src k)
    (hc_lt : ctrl.val < cur) (hs_lt : ∀ k, (src k).val < cur) (leaf body : TempPhaseProg M)
    (sBody : BitAssignment M → BitAssignment M),
    ScopedBlock M (M - (cur + W)) sBody leaf body →
    ∃ setup : BitAssignment M → BitAssignment M, ScopedBlock M (M - cur)
      (fun β ↦ sBody (setup β)) leaf
      ((ctxAndNotVec W cur hcur ctrl src hc_src hc_lt hs_lt).plug body) ∧
      ∀ β : BitAssignment M, cleanRem M (M - cur) β →
      cleanRem M (M - (cur + W)) (setup β) ∧ (∀ w : Wire M, w.val < cur → setup β w = β w) ∧
      ∀ k : Fin W, setup β ⟨cur + k.val, by omega⟩ = β ctrl * (β (src k) + 1)
  | 0, _, _, _, _, _, _, _, _, _, _, hBody =>
      ⟨id, hBody, fun _ hβ ↦ ⟨by simpa using hβ, fun _ _ ↦ rfl, fun k ↦ Fin.elim0 k⟩⟩
  | W + 1, cur, _, ctrl, src, hc_src, hc_lt, hs_lt, leaf, body, sBody, hBody => by
      let dst : Wire M := ⟨cur, by omega⟩
      obtain ⟨sTail, h4, hSpec4⟩ := ScopedBlock.ctxAndNotVec_block W (cur + 1) (by omega)
        ctrl (fun k ↦ src k.succ) (fun k ↦ hc_src k.succ)
        (lt_trans hc_lt (Nat.lt_succ_self cur))
        (fun k ↦ lt_trans (hs_lt k.succ) (Nat.lt_succ_self cur))
        leaf body sBody (hBody.cast_rem (by omega))
      let cx := CliffProg.x (src 0)
      let step0 : BitAssignment M → BitAssignment M := fun β ↦
        cx.eval (Function.update (cx.eval β) dst (cx.eval β ctrl * cx.eval β (src 0)))
      refine ⟨fun β ↦ sTail (step0 β),
        ScopedBlock.ctxSandwich_append (by omega) cx cx ctrl (src 0) (hc_src 0)
          hc_lt (hs_lt 0) (wire_ne_of_lt hc_lt) (wire_ne_of_lt (hs_lt 0))
          (hs_lt 0) (lt_trans (hs_lt 0) (Nat.lt_succ_self cur)) h4,
        fun β hβ ↦ ?_⟩
      have hs0d : src 0 ≠ dst := wire_ne_of_lt (hs_lt 0)
      have hstep0 : step0 β = Function.update β dst (β ctrl * (β (src 0) + 1)) := by
        funext w
        dsimp only [step0, cx]
        simp only [x_eval_w, upd_app, hc_src 0, hs0d, ↓reduceIte]
        rcases eq_or_ne w (src 0) with rfl | hws
        · simp [hs0d]
        · simp [hws]
      obtain ⟨hclT, hbelowT, hbitsT⟩ := hSpec4 (step0 β) fun w hw ↦ by
        rw [hstep0, Function.update_of_ne
          (wire_ne_of_gt (lt_of_lt_of_le (Nat.lt_succ_self cur) (by omega)))]
        exact hβ w (by omega)
      refine ⟨by simpa [Nat.add_assoc, Nat.add_comm 1 W] using hclT, fun w hw ↦ ?_, ?_⟩
      · dsimp only
        rw [hbelowT w (by omega), hstep0, Function.update_of_ne (wire_ne_of_lt hw)]
      · refine Fin.cases ?_ fun j ↦ ?_
        · dsimp only
          rw [show (⟨cur + (0 : Fin (W + 1)).val, by omega⟩ : Wire M) = dst from Fin.ext rfl,
            hbelowT dst (Nat.lt_succ_self cur), hstep0, Function.update_self]
        · dsimp only
          rw [show (⟨cur + j.succ.val, by omega⟩ : Wire M) = ⟨cur + 1 + j.val, by omega⟩ from
              Fin.ext (show cur + (j.val + 1) = cur + 1 + j.val by omega),
            hbitsT j, hstep0, Function.update_of_ne (wire_ne_of_lt hc_lt),
            Function.update_of_ne (wire_ne_of_lt (hs_lt j.succ))]
private theorem fold7_bits_val : ∀ z : Fin 128,
    (bitsVal (fun k : Fin 7 ↦ basisBits 7 z k + basisBits 7 z 6) +
      (basisBits 7 z 6).val) % 128 =
      if z.val ≤ 64 then z.val else 128 - z.val := by decide
private theorem ite_le64_eq_min128 (z : ℕ) : (if z ≤ 64 then z else 128 - z) = min z (128 - z) := by
  rw [min_def]
  split_ifs <;> omega
private theorem sub_mod128_eq {u v : ℕ} (hu : u < 128) (hv : v < 128) : (u + 128 - v) % 128 = if u <
    v then u + 128 - v else u - v := by
  split_ifs with h
  · exact Nat.mod_eq_of_lt (by omega)
  · rw [show u + 128 - v = (u - v) + 128 by omega, Nat.add_mod_right]
    exact Nat.mod_eq_of_lt (by omega)
private theorem foldMag128_symm_sub {a b : ℕ} (ha : a < 128) (hb : b < 128) :
    (let z₂ := (b + 128 - a) % 128; if z₂ ≤ 64 then z₂ else 128 - z₂) =
    (let z₁ := (a + 128 - b) % 128; if z₁ ≤ 64 then z₁ else 128 - z₁) := by
  dsimp only
  rw [sub_mod128_eq hb ha, sub_mod128_eq ha hb]
  split_ifs <;> omega
theorem bits_eq_basisBits_of_val {W : ℕ} (f : Fin W → ZMod 2) : f = basisBits W ⟨bitsVal f,
    bitsVal_lt_two_pow f⟩ :=
  bitsVal_injective (bitsVal_basisBits ⟨bitsVal f, bitsVal_lt_two_pow f⟩).symm
theorem bitsVal_padZeroRight {W : ℕ} : ∀ {K : ℕ} (f : Fin W → ZMod 2),
    bitsVal (fun j : Fin (W + K) ↦ if hj : j.val < W then f ⟨j.val, hj⟩ else 0) = bitsVal f
  | 0, f => Finset.sum_congr rfl fun j _ ↦ by simp
  | K + 1, f => by
      change bitsVal (fun j : Fin ((W + K) + 1) ↦
        if hj : j.val < W then f ⟨j.val, hj⟩ else 0) = bitsVal f
      unfold bitsVal
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, show ¬ (Fin.last (W + K)).val < W by simp, ↓reduceDIte,
        ZMod.val_zero, zero_mul, add_zero]
      exact bitsVal_padZeroRight (K := K) f
def wS0 : Wire 303 := ⟨0, by decide⟩
def wB0 (ax : Fin 3) : Wire 303 := ⟨1 + ax.val, by omega⟩
def wB1 (ax : Fin 3) : Wire 303 := ⟨4 + ax.val, by omega⟩
def wY0 (ax : Fin 3) (j : Fin 6) : Wire 303 := ⟨7 + 6 * ax.val + j.val, by omega⟩
def wYP (ax : Fin 3) (j : Fin 6) : Wire 303 := ⟨25 + 6 * ax.val + j.val, by omega⟩
def wZero : Wire 303 := ⟨59, by decide⟩
private theorem andNot6_val : ∀ (s : ZMod 2) (z : Fin 64),
    bitsVal (fun k : Fin 6 ↦ s * (basisBits 6 z k + 1)) =
      if s = 1 then 63 - bitsVal (basisBits 6 z) else 0 := by decide
private theorem stage1a_val : ∀ (sw : Bool) (s0 b0 b1 : ZMod 2),
    (b1 + s0 * b0).val + 2 * (if sw then s0 + (s0 + s0 * b0) * b1
      else s0 + s0 * b0 + s0 * b0 * b1).val =
      if s0 = 1 then (if sw then b0.val + 2 - b1.val else b1.val + 2 - b0.val)
      else b1.val := by decide
theorem ScopedBlock.withCliffCur {M cur curIn : ℕ} (hIn : curIn ≤ M) (hle : cur ≤ curIn)
    (c : CliffProg M) (hc : c.SupportsBelow curIn) {sBody : BitAssignment M → BitAssignment M}
    {leaf body : TempPhaseProg M} (hBody : ScopedBlock M (M - curIn) sBody leaf body) :
    ScopedBlock M (M - cur) (sBody ∘ c.eval) leaf (withCliffAlloc c body) :=
  ScopedBlock.withCliffAlloc_block (M := M) (rem := M - cur) (remIn := M - curIn)
    (by omega) (by omega) c (by rw [show M - (M - curIn) = curIn by omega]; exact hc) hBody
theorem CliffProg.eval_update_above {M bound : ℕ} :
    ∀ (c : CliffProg M), c.SupportsBelow bound →
      ∀ (γ : BitAssignment M) (anc : Wire M), bound ≤ anc.val → ∀ (v : ZMod 2),
        c.eval (Function.update γ anc v) = Function.update (c.eval γ) anc v
  | .nil, _, _, _, _, _ => rfl
  | .x q, hq, _, _, hanc, _ => by
      have hqa : q ≠ _ := wire_ne_of_lt (lt_of_lt_of_le hq hanc)
      dsimp [CliffProg.eval]
      rw [Function.update_of_ne hqa, upd_comm hqa.symm]
  | .cnot ctrl t _, ⟨hc, ht⟩, _, _, hanc, _ => by
      have hca : ctrl ≠ _ := wire_ne_of_lt (lt_of_lt_of_le hc hanc)
      have hta : t ≠ _ := wire_ne_of_lt (lt_of_lt_of_le ht hanc)
      dsimp [CliffProg.eval]
      rw [Function.update_of_ne hta, Function.update_of_ne hca, upd_comm hta.symm]
  | .seq c₁ c₂, ⟨h₁, h₂⟩, γ, anc, hanc, v => by
      dsimp [CliffProg.eval]
      rw [eval_update_above c₁ h₁ γ anc hanc v, eval_update_above c₂ h₂ (c₁.eval γ) anc hanc v]
def cnotSwap {M : ℕ} (a b : Wire M) (hab : a ≠ b) : CliffProg M :=
  .seq (.cnot b a hab.symm) (.seq (.cnot a b hab) (.cnot b a hab.symm))
private theorem cnotSwap_eval {M : ℕ} (a b : Wire M) (hab : a ≠ b) (γ : BitAssignment M) (w : Wire
    M) :
    (cnotSwap a b hab).eval γ w = if w = a then γ b else if w = b then γ a else γ w := by
  dsimp only [cnotSwap]
  simp only [seq_eval_w, cnot_eval_w, hab, hab.symm, ↓reduceIte]
  rcases eq_or_ne w a with rfl | hwa
  · simp [zmod2_swap_a]
  · rcases eq_or_ne w b with rfl | hwb
    · simp [hab.symm, zmod2_swap_b]
    · simp [hwa, hwb]
def fReg (ax : Fin 3) (k : Fin 7) : Wire 303 := ⟨60 + 20 * ax.val + 1 + k.val, by omega⟩
def ctxAxisBit0Carry (slot2SwappedTo0 : Bool) (ax : Fin 3) : TempCtx 303 :=
  have _hax := ax.isLt
  let base := 60 + 20 * ax.val
  let pW : Wire 303 := ⟨base, by omega⟩
  let z0 : Wire 303 := ⟨base + 1, by omega⟩
  have hpz : pW ≠ z0 := wire_ne_of_lt (Nat.lt_succ_self base)
  have hs0p : wS0 ≠ pW := wire_ne_of_lt (by dsimp [wS0, pW, base]; omega)
  have hs0z : wS0 ≠ z0 := wire_ne_of_lt (by dsimp [wS0, z0, base]; omega)
  have hb0p : wB0 ax ≠ pW := wire_ne_of_lt (by dsimp [wB0, pW, base]; omega)
  have hb1p : wB1 ax ≠ pW := wire_ne_of_lt (by dsimp [wB1, pW, base]; omega)
  have hb1z : wB1 ax ≠ z0 := wire_ne_of_lt (by dsimp [wB1, z0, base]; omega)
  have hs0b0 : wS0 ≠ wB0 ax := wire_ne_of_lt (by dsimp [wS0, wB0]; omega)
  if slot2SwappedTo0 then
    (ctxTempBit wS0 (wB0 ax) pW hs0b0 hs0p hb0p).append
      ((ctxCliffAlloc (.cnot wS0 pW hs0p)).append
        ((ctxTempBit pW (wB1 ax) z0 hb1p.symm hpz hb1z).append
          (ctxCliffAlloc (.seq (.cnot wS0 pW hs0p) (.seq (.cnot (wB1 ax) pW hb1p)
            (.seq (.cnot wS0 z0 hs0z) (cnotSwap pW z0 hpz)))))))
  else
    (ctxTempBit wS0 (wB0 ax) pW hs0b0 hs0p hb0p).append
      ((ctxTempBit pW (wB1 ax) z0 hb1p.symm hpz hb1z).append
        (ctxCliffAlloc (.seq (.cnot wS0 z0 hs0z)
          (.seq (.cnot pW z0 hpz) (.seq (.cnot (wB1 ax) pW hb1p) (cnotSwap pW z0 hpz))))))
@[simp] theorem ctxAxisBit0Carry_countTempAnd (slot2SwappedTo0 : Bool) (ax : Fin 3) :
    (ctxAxisBit0Carry slot2SwappedTo0 ax).countTempAnd = 2 := by
  cases slot2SwappedTo0 <;>
    simp [ctxAxisBit0Carry, tempCtx_append_count, ctxCliffAlloc, ctxTempBit, TempCtx.countTempAnd]
def ctxFoldDiffHi6 (base : ℕ) (hbase : base + 20 ≤ 303) (hlo59 : 59 < base) (regD6 regX6 : Fin 6 →
    Wire 303) (hX_s0 : ∀ k, wS0 ≠ regX6 k)
    (hD_lt : ∀ k, (regD6 k).val < base) (hX_lt : ∀ k, (regX6 k).val < base) : TempCtx 303 :=
  let pWire : Wire 303 := ⟨base, by omega⟩
  let mReg : Fin 7 → Wire 303 := fun k ↦ ⟨base + 1 + k.val, by omega⟩
  let mHi : Fin 6 → Wire 303 := fun j ↦ ⟨base + 2 + j.val, by omega⟩
  let sgn : Wire 303 := ⟨base + 13, by omega⟩
  let cFoldPre : CliffProg 303 :=
    .seq (.cnot (mReg 6) sgn (wire_ne_of_lt (by dsimp [mReg, sgn]; omega)))
      (fanoutCnot 7 sgn mReg (fun _ ↦ wire_ne_of_gt (by dsimp [mReg, sgn]; omega)))
  (ctxAndNotVec 6 (base + 2) (by omega) wS0 regX6 hX_s0 (by dsimp [wS0]; omega)
    (fun k ↦ lt_trans (hX_lt k) (by omega))).append
    ((ctxAddMod2Pow 5 (base + 8) (by omega) regD6 mHi pWire
      (fun i _ ↦ wire_ne_of_lt (lt_trans (hD_lt i) (by dsimp [mHi]; omega)))
      (fun i ↦ wire_ne_of_lt (hD_lt i)) (fun _ ↦ wire_ne_of_gt (by dsimp [mHi, pWire]; omega))
      (fun i ↦ lt_trans (hD_lt i) (by omega)) (fun _ ↦ by dsimp [mHi]; omega)
      (by dsimp [pWire]; omega)).append
      ((ctxCliffAlloc cFoldPre).append
        (ctxAddMod2Pow 6 (base + 14) (by omega) (fun _ ↦ wZero) mReg sgn
          (fun _ _ ↦ wire_ne_of_lt (by dsimp [wZero, mReg]; omega))
          (fun _ ↦ wire_ne_of_lt (by dsimp [wZero, sgn]; omega))
          (fun _ ↦ wire_ne_of_lt (by dsimp [mReg, sgn]; omega))
          (fun _ ↦ by dsimp [wZero]; omega) (fun _ ↦ by dsimp [mReg]; omega)
          (by dsimp [sgn]; omega))))
def ctxAxisFold7 (slot2SwappedTo0 : Bool) (ax : Fin 3) : TempCtx 303 :=
  have _hax := ax.isLt
  let base := 60 + 20 * ax.val
  if slot2SwappedTo0 then
    (ctxAxisBit0Carry true ax).append
      (ctxFoldDiffHi6 base (by omega) (by omega) (wY0 ax) (wYP ax)
        (fun _ ↦ wire_ne_of_lt (by dsimp [wS0, wYP]; omega))
        (fun k ↦ by have := k.isLt; dsimp [wY0, base]; omega)
        (fun k ↦ by have := k.isLt; dsimp [wYP, base]; omega))
  else
    (ctxAxisBit0Carry false ax).append
      (ctxFoldDiffHi6 base (by omega) (by omega) (wYP ax) (wY0 ax)
        (fun _ ↦ wire_ne_of_lt (by dsimp [wS0, wY0]; omega))
        (fun k ↦ by have := k.isLt; dsimp [wYP, base]; omega)
        (fun k ↦ by have := k.isLt; dsimp [wY0, base]; omega))
@[simp] theorem ctxAxisFold7_countTempAnd (slot2SwappedTo0 : Bool) (ax : Fin 3) : (ctxAxisFold7
    slot2SwappedTo0 ax).countTempAnd = 19 := by
  cases slot2SwappedTo0 <;>
    simp [ctxAxisFold7, ctxFoldDiffHi6, tempCtx_append_count, ctxCliffAlloc, TempCtx.countTempAnd]
def coreViewOf303 (β : BitAssignment 303) : BitAssignment posCoreWires := fun i ↦
  if i.val = 3948 then β wS0
  else if h0 : 3957 ≤ i.val ∧ i.val < 3960 then β (wB0 ⟨i.val - 3957, by omega⟩)
  else if h1 : 3954 ≤ i.val ∧ i.val < 3957 then β (wB1 ⟨i.val - 3954, by omega⟩)
  else if hy : i.val < 18 then β (wY0 ⟨i.val / 6, by omega⟩ ⟨5 - i.val % 6, by omega⟩)
  else 0
def partnerViewOf303 (β : BitAssignment 303) : BitAssignment 18 := fun i ↦
  β (wYP ⟨i.val / 6, by omega⟩ ⟨5 - i.val % 6, by omega⟩)
theorem coreViewOf303_reads (β : BitAssignment 303) :
    let rCoreL := QRegExt.ofFin posCoreWires
    let rP18L := QRegExt.ofFin 18
    coreViewOf303 β (wSlot0Core rCoreL) = β wS0 ∧
    (∀ ax : Fin 3, coreViewOf303 β (rCosetB0 rCoreL ax) = β (wB0 ax)) ∧
    (∀ ax : Fin 3, coreViewOf303 β (rCosetB1 rCoreL ax) = β (wB1 ax)) ∧
    (∀ (ax : Fin 3) (j : Fin 6),
      coreViewOf303 β (axisBitRev6 (rElecSlot rCoreL 0) ax j) = β (wY0 ax j)) ∧
    (∀ (ax : Fin 3) (j : Fin 6),
      partnerViewOf303 β (axisBitRev6 rP18L ax j) = β (wYP ax j)) := by
  refine ⟨rfl, fun ax ↦ ?_, fun ax ↦ ?_, fun ax j ↦ ?_, fun ax j ↦ ?_⟩
  · fin_cases ax <;> rfl
  · fin_cases ax <;> rfl
  · fin_cases ax <;> fin_cases j <;> rfl
  · fin_cases ax <;> fin_cases j <;> rfl
theorem ScopedBlock.ctxAxisFold7_block (slot2SwappedTo0 : Bool) (ax : Fin 3)
    (leaf body : TempPhaseProg 303) (sBody : BitAssignment 303 → BitAssignment 303) (hBody :
    ScopedBlock 303 (303 - (60 + 20 * (ax.val + 1))) sBody leaf body) : ∃ setup :
    BitAssignment 303 → BitAssignment 303, ScopedBlock 303 (303 - (60 + 20 * ax.val))
    (fun β ↦ sBody (setup β)) leaf ((ctxAxisFold7 slot2SwappedTo0 ax).plug body) ∧ ∀ β :
    BitAssignment 303,
      cleanRem 303 (303 - (60 + 20 * ax.val)) β → β wZero = 0 → cleanRem 303 (303 - (60 + 20 *
      (ax.val + 1))) (setup β) ∧
    (∀ w : Wire 303, w.val < 60 + 20 * ax.val → setup β w = β w) ∧ bitsVal (fun k ↦ setup β (fReg ax
      k)) = (foldMag128 (rawOrbitCoord128 slot2SwappedTo0
    (coreViewOf303 β) (partnerViewOf303 β) ax)).val := by
  have _hax := ax.isLt
  let base := 60 + 20 * ax.val
  have hbase : base + 20 ≤ 303 := by dsimp [base]; omega
  have hlo59 : 59 < base := by dsimp [base]; omega
  let pWire : Wire 303 := ⟨base, by omega⟩
  let z0 : Wire 303 := ⟨base + 1, by omega⟩
  let mReg : Fin 7 → Wire 303 := fun k ↦ ⟨base + 1 + k.val, by omega⟩
  let mHi : Fin 6 → Wire 303 := fun j ↦ ⟨base + 2 + j.val, by omega⟩
  let sgn : Wire 303 := ⟨base + 13, by omega⟩
  let regD : Fin 6 → Wire 303 := if slot2SwappedTo0 then wY0 ax else wYP ax
  let regX : Fin 6 → Wire 303 := if slot2SwappedTo0 then wYP ax else wY0 ax
  have hX_s0 : ∀ k, wS0 ≠ regX k := fun k ↦ by
    cases slot2SwappedTo0 <;>
      exact wire_ne_of_lt (by have := k.isLt; dsimp [regX, wS0, wY0, wYP]; omega)
  have hD_lt : ∀ k, (regD k).val < base := fun k ↦ by
    cases slot2SwappedTo0 <;> (have := k.isLt; dsimp [regD, wY0, wYP, base]; omega)
  have hX_lt : ∀ k, (regX k).val < base := fun k ↦ by
    cases slot2SwappedTo0 <;> (have := k.isLt; dsimp [regX, wY0, wYP, base]; omega)
  have hm_inj : Function.Injective mReg := fun i j h ↦
    Fin.ext (by have hv := congrArg Fin.val h; dsimp [mReg] at hv; omega)
  have hmHi_inj : Function.Injective mHi := fun i j h ↦
    Fin.ext (by have hv := congrArg Fin.val h; dsimp [mHi] at hv; omega)
  let cFoldPre : CliffProg 303 :=
    .seq (.cnot (mReg 6) sgn (wire_ne_of_lt (by dsimp [mReg, sgn]; omega)))
      (fanoutCnot 7 sgn mReg (fun _ ↦ wire_ne_of_gt (by dsimp [mReg, sgn]; omega)))
  obtain ⟨s4, h4, hSpec4⟩ := ScopedBlock.ctxAddMod2Pow_block (M := 303) 6 (base + 14)
    (by omega) (fun _ ↦ wZero) mReg sgn
    (fun _ _ ↦ wire_ne_of_lt (by dsimp [wZero, mReg]; omega))
    (fun _ ↦ wire_ne_of_lt (by dsimp [wZero, sgn]; omega))
    (fun _ ↦ wire_ne_of_lt (by dsimp [mReg, sgn]; omega)) hm_inj
    (fun _ ↦ by dsimp [wZero]; omega) (fun _ ↦ by dsimp [mReg]; omega) (by dsimp [sgn]; omega)
    leaf body sBody (hBody.cast_rem (by dsimp [base]; omega))
  have h3 := ScopedBlock.ctxCliff_append (by omega) (cur := base + 13) (by omega) cFoldPre
    ⟨⟨by dsimp [mReg]; omega, by dsimp [sgn]; omega⟩,
      fanoutCnot_supportsBelow 7 sgn mReg _ (base + 14) (by dsimp [sgn]; omega)
        (fun _ ↦ by dsimp [mReg]; omega)⟩ h4
  obtain ⟨s2, h2, hSpec2⟩ := ScopedBlock.ctxAddMod2Pow_block (M := 303) 5 (base + 8)
    (by omega) regD mHi pWire
    (fun i _ ↦ wire_ne_of_lt (lt_trans (hD_lt i) (by dsimp [mHi]; omega)))
    (fun i ↦ wire_ne_of_lt (hD_lt i)) (fun _ ↦ wire_ne_of_gt (by dsimp [mHi, pWire]; omega))
    hmHi_inj (fun i ↦ lt_trans (hD_lt i) (by omega)) (fun _ ↦ by dsimp [mHi]; omega)
    (by dsimp [pWire]; omega) leaf _ (fun γ ↦ sBody (s4 (cFoldPre.eval γ))) h3
  obtain ⟨s1, h1, hSpec1⟩ := ScopedBlock.ctxAndNotVec_block (M := 303) 6 (base + 2)
    (by omega) wS0 regX hX_s0 (by dsimp [wS0]; omega) (fun k ↦ lt_trans (hX_lt k) (by omega))
    leaf _ (fun γ ↦ sBody (s4 (cFoldPre.eval (s2 γ)))) h2
  have hFoldBlk : ScopedBlock 303 (303 - (base + 2)) (fun γ ↦ sBody (s4 (cFoldPre.eval (s2 (s1
    γ))))) leaf
      ((ctxFoldDiffHi6 base hbase hlo59 regD regX hX_s0 hD_lt hX_lt).plug body) :=
    ⟨h1.valid, h1.bits, fun β hβ ↦ by
      dsimp only [ctxFoldDiffHi6]
      rw [TempCtx.append_plug, TempCtx.append_plug]
      exact h1.sign β hβ⟩
  have ⟨s1a, h1a, hstep1a⟩ : ∃ s1a : BitAssignment 303 → BitAssignment 303,
    ScopedBlock 303 (303 - base)
      (fun β ↦ sBody (s4 (cFoldPre.eval (s2 (s1 (s1a β)))))) leaf (((ctxAxisBit0Carry
        slot2SwappedTo0 ax).append
      (ctxFoldDiffHi6 base hbase hlo59 regD regX hX_s0 hD_lt hX_lt)).plug body) ∧ ∀ (β :
        BitAssignment 303) (w : Wire 303), s1a β w = if w = pWire then
      if slot2SwappedTo0 then β wS0 + (β wS0 + β wS0 * β (wB0 ax)) * β (wB1 ax) else β wS0 + β wS0 *
        β (wB0 ax) + (β wS0 * β (wB0 ax)) * β (wB1 ax)
      else if w = z0 then β (wB1 ax) + β wS0 * β (wB0 ax) else β w := by
    rw [TempCtx.append_plug]
    have hpz : pWire ≠ z0 := wire_ne_of_lt (Nat.lt_succ_self base)
    have hs0_lt : wS0.val < base := by dsimp [wS0, base]; omega
    have hb0_lt : (wB0 ax).val < base := by dsimp [wB0, base]; omega
    have hb1_lt : (wB1 ax).val < base := by dsimp [wB1, base]; omega
    have hp_lt2 : pWire.val < base + 2 := by dsimp [pWire]; omega
    have hs0p : wS0 ≠ pWire := wire_ne_of_lt hs0_lt
    have hs0z : wS0 ≠ z0 := wire_ne_of_lt (lt_trans hs0_lt (Nat.lt_succ_self base))
    have hb0p : wB0 ax ≠ pWire := wire_ne_of_lt hb0_lt
    have hb1p : wB1 ax ≠ pWire := wire_ne_of_lt hb1_lt
    have hb1z : wB1 ax ≠ z0 := wire_ne_of_lt (lt_trans hb1_lt (Nat.lt_succ_self base))
    have hs0b0 : wS0 ≠ wB0 ax := wire_ne_of_lt (by dsimp [wS0, wB0]; omega)
    have hsw_s : (cnotSwap pWire z0 hpz).SupportsBelow (base + 2) := ⟨⟨Nat.lt_succ_self _,
      hp_lt2⟩, ⟨⟨hp_lt2, Nat.lt_succ_self _⟩, ⟨Nat.lt_succ_self _, hp_lt2⟩⟩⟩
    cases slot2SwappedTo0 with
    | false =>
        let cPost : CliffProg 303 := .seq (.cnot wS0 z0 hs0z) (.seq (.cnot pWire z0 hpz)
          (.seq (.cnot (wB1 ax) pWire hb1p) (cnotSwap pWire z0 hpz)))
        let sF : BitAssignment 303 → BitAssignment 303 := fun β ↦
          let γ1 := Function.update β pWire (β wS0 * β (wB0 ax))
          cPost.eval (Function.update γ1 z0 (γ1 pWire * γ1 (wB1 ax)))
        refine ⟨sF, by
          dsimp only [ctxAxisBit0Carry]
          exact ScopedBlock.ctxTemp_append (cur := base) (by omega) wS0 (wB0 ax) hs0b0
            hs0_lt hb0_lt hs0p hb0p
            (ScopedBlock.ctxTemp_append (cur := base + 1) (by omega) pWire (wB1 ax) hb1p.symm
              (Nat.lt_succ_self base) (lt_trans hb1_lt (Nat.lt_succ_self base)) hpz hb1z
              (ScopedBlock.ctxCliff_single (cur := base + 2) (curIn := base + 2) (by omega)
                le_rfl cPost ⟨⟨lt_trans hs0_lt hp_lt2, Nat.lt_succ_self _⟩,
                  ⟨⟨hp_lt2, Nat.lt_succ_self _⟩,
                    ⟨⟨lt_trans hb1_lt hp_lt2, hp_lt2⟩, hsw_s⟩⟩⟩ hFoldBlk)),
          fun β w ↦ ?_⟩
        dsimp only [sF, cPost]
        simp only [Bool.false_eq_true, seq_eval_w, cnotSwap_eval, cnot_eval_w, upd_app, hpz,
          hpz.symm, hs0p, hs0z, hb1p, hb1z, ↓reduceIte]
        rcases eq_or_ne w pWire with rfl | hwp
        · simp only [↓reduceIte]
          ring
        · rcases eq_or_ne w z0 with rfl | hwz
          · simp only [hpz.symm, ↓reduceIte]
            ring
          · simp [hwp, hwz]
    | true =>
        let cMid : CliffProg 303 := .cnot wS0 pWire hs0p
        let cPost : CliffProg 303 := .seq (.cnot wS0 pWire hs0p) (.seq (.cnot (wB1 ax) pWire
          hb1p) (.seq (.cnot wS0 z0 hs0z) (cnotSwap pWire z0 hpz)))
        let sT : BitAssignment 303 → BitAssignment 303 := fun β ↦
          let γ1 := cMid.eval (Function.update β pWire (β wS0 * β (wB0 ax)))
          cPost.eval (Function.update γ1 z0 (γ1 pWire * γ1 (wB1 ax)))
        refine ⟨sT, by
          dsimp only [ctxAxisBit0Carry]
          exact ScopedBlock.ctxTemp_append (cur := base) (by omega) wS0 (wB0 ax) hs0b0
            hs0_lt hb0_lt hs0p hb0p
            (ScopedBlock.ctxCliff_append (cur := base + 1) (curIn := base + 1) (by omega)
              le_rfl cMid ⟨lt_trans hs0_lt (Nat.lt_succ_self base), Nat.lt_succ_self base⟩
              (ScopedBlock.ctxTemp_append (cur := base + 1) (by omega) pWire (wB1 ax) hb1p.symm
                (Nat.lt_succ_self base) (lt_trans hb1_lt (Nat.lt_succ_self base)) hpz hb1z
                (ScopedBlock.ctxCliff_single (cur := base + 2) (curIn := base + 2) (by omega)
                  le_rfl cPost ⟨⟨lt_trans hs0_lt hp_lt2, hp_lt2⟩,
                    ⟨⟨lt_trans hb1_lt hp_lt2, hp_lt2⟩,
                      ⟨⟨lt_trans hs0_lt hp_lt2, Nat.lt_succ_self _⟩, hsw_s⟩⟩⟩ hFoldBlk))),
          fun β w ↦ ?_⟩
        dsimp only [sT, cPost, cMid]
        simp only [seq_eval_w, cnotSwap_eval, cnot_eval_w, upd_app, hpz, hpz.symm, hs0p,
          hs0z, hb1p, hb1z, ↓reduceIte]
        rcases eq_or_ne w pWire with rfl | hwp
        · simp only [↓reduceIte]
          ring
        · rcases eq_or_ne w z0 with rfl | hwz
          · simp only [hpz.symm, ↓reduceIte]
            exact zmod2_axis_true_p _ _ _
          · simp [hwp, hwz]
  have hplug : (ctxAxisFold7 slot2SwappedTo0 ax).plug body = ((ctxAxisBit0Carry slot2SwappedTo0
    ax).append
      (ctxFoldDiffHi6 base hbase hlo59 regD regX hX_s0 hD_lt hX_lt)).plug body := by
    cases slot2SwappedTo0 <;> rfl
  refine ⟨fun β ↦ s4 (cFoldPre.eval (s2 (s1 (s1a β)))), (by rwa [hplug]), fun β hβ hz0 ↦ ?_⟩
  have hkeep1a : ∀ w : Wire 303, w.val < base → s1a β w = β w := fun w hw ↦ by
    rw [hstep1a β w, ite_neg (wire_ne_of_lt hw),
      ite_neg (wire_ne_of_lt (show w.val < base + 1 by omega))]
  have hcl1a : cleanRem 303 (303 - (base + 2)) (s1a β) := fun w hw ↦ by
    rw [hstep1a β w, ite_neg (wire_ne_of_gt (show base < w.val by omega)),
      ite_neg (wire_ne_of_gt (show base + 1 < w.val by omega))]
    exact hβ w (by omega)
  obtain ⟨hcl1, hkeep1, hbits1⟩ := hSpec1 (s1a β) hcl1a
  obtain ⟨hcl2, hkeep2, hval2⟩ := hSpec2 (s1 (s1a β)) hcl1
  let γ₂ := s2 (s1 (s1a β))
  let β₃ := cFoldPre.eval γ₂
  have hsgn0 : γ₂ sgn = 0 := hcl2 sgn (show 303 - (303 - (base + 8 + 5)) ≤ base + 13 by omega)
  have hβ₃_eq : ∀ w : Wire 303, β₃ w = if w = sgn then γ₂ (mReg 6)
      else if ∃ k : Fin 7, w = mReg k then γ₂ w + γ₂ (mReg 6) else γ₂ w := fun w ↦ by
    dsimp only [β₃, cFoldPre, CliffProg.eval]
    rw [fanoutCnot_eval _ _ _ _ hm_inj, Function.update_self, hsgn0, zero_add]
    rcases eq_or_ne w sgn with rfl | hws
    · have hnm : ¬ ∃ k : Fin 7, sgn = mReg k := fun ⟨k, hk⟩ ↦
        wire_ne_of_gt (by have := k.isLt; dsimp [mReg, sgn]; omega) hk
      simp only [↓reduceIte, hnm, Function.update_self]
    · simp only [hws, ↓reduceIte, Function.update_of_ne hws]
  obtain ⟨hcl4, hkeep4, hval4⟩ := hSpec4 β₃ fun w hw ↦ by
    rw [hβ₃_eq, ite_neg (wire_ne_of_gt (by dsimp [sgn]; omega)),
      ite_neg (fun ⟨k, hk⟩ ↦ by subst hk; dsimp [mReg] at hw; omega)]
    exact hcl2 w (by omega)
  refine ⟨by simpa [show base + 14 + 6 = 60 + 20 * (ax.val + 1) by dsimp [base]; omega]
    using hcl4, fun w hw ↦ ?_, ?_⟩
  · have hnmw : ∀ j : Fin 7, w ≠ mReg j := fun _ ↦ wire_ne_of_lt (by dsimp [mReg]; omega)
    change s4 β₃ w = β w
    rw [hkeep4 w (by omega) hnmw, hβ₃_eq, ite_neg (wire_ne_of_lt (by dsimp [sgn]; omega)),
      ite_neg (fun ⟨k, hk⟩ ↦ hnmw k hk)]
    dsimp only [γ₂]
    rw [hkeep2 w (by omega) (fun _ ↦ wire_ne_of_lt (by dsimp [mHi]; omega)),
      hkeep1 w (by omega), hkeep1a w hw]
  · let xFin : Fin 64 := ⟨bitsVal (fun j ↦ β (regX j)), bitsVal_lt_two_pow _⟩
    have hx_bits := bits_eq_basisBits_of_val (fun j ↦ β (regX j))
    have hs1_mHi : bitsVal (fun j : Fin 6 ↦ s1 (s1a β) (mHi j)) = if β wS0 = 1 then 63 - xFin.val
      else 0 := by
      refine (congrArg bitsVal (funext fun j ↦ ?_)).trans
        ((andNot6_val (β wS0) xFin).trans (by rw [bitsVal_basisBits]))
      rw [hbits1 j, hkeep1a wS0 (by dsimp [wS0, base]; omega), hkeep1a (regX j) (hX_lt j),
        congrFun hx_bits j]
    have hm0 : γ₂ (mReg 0) = β (wB1 ax) + β wS0 * β (wB0 ax) := by
      dsimp only [γ₂]
      rw [hkeep2 (mReg 0) (by dsimp [mReg]; omega)
          (fun _ ↦ wire_ne_of_lt (by dsimp [mReg, mHi]; omega)),
        hkeep1 (mReg 0) (by dsimp [mReg]; omega), hstep1a β (mReg 0),
        ite_neg (wire_ne_of_gt (Nat.lt_succ_self base)),
        ite_pos (Fin.ext (by dsimp [mReg, z0]) : mReg 0 = z0)]
    have hp_val : s1 (s1a β) pWire = if slot2SwappedTo0 then β wS0 + (β wS0 + β wS0 * β (wB0 ax)) *
      β (wB1 ax)
        else β wS0 + β wS0 * β (wB0 ax) + (β wS0 * β (wB0 ax)) * β (wB1 ax) := by
      rw [hkeep1 pWire (by dsimp [pWire]; omega), hstep1a β pWire, ite_pos rfl]
    have hs2_val : bitsVal (fun k : Fin 7 ↦ γ₂ (mReg k)) = ((β (wB1 ax) + β wS0 * β (wB0 ax)).val +
        2 * (bitsVal (fun j ↦ β (regD j)) + (if β wS0 = 1 then 63 - xFin.val else 0) + (s1 (s1a β)
          pWire).val)) % 128 := by
      have htail : (fun j : Fin 6 ↦ γ₂ (mReg j.succ)) = fun j ↦ γ₂ (mHi j) :=
        funext fun j ↦ congrArg γ₂ (Fin.ext (by dsimp [mReg, mHi]; omega))
      have hs1_D : (fun j : Fin 6 ↦ s1 (s1a β) (regD j)) = fun j ↦ β (regD j) :=
        funext fun j ↦ (hkeep1 _ (lt_trans (hD_lt j) (by omega))).trans (hkeep1a _ (hD_lt j))
      rw [bitsVal_succ_split, hm0, htail]
      dsimp only [γ₂]
      rw [hval2, hs1_D, hs1_mHi, show (2 : ℕ) ^ (5 + 1) = 64 by decide]
      have hm0_lt := ZMod.val_lt (β (wB1 ax) + β wS0 * β (wB0 ax))
      have hp_lt := ZMod.val_lt (s1 (s1a β) pWire)
      omega
    let zFin : Fin 128 := ⟨bitsVal (fun k ↦ γ₂ (mReg k)), bitsVal_lt_two_pow _⟩
    have hz_bits := bits_eq_basisBits_of_val (fun k : Fin 7 ↦ γ₂ (mReg k))
    have hβ₃_z0 : (fun _ : Fin 7 ↦ β₃ wZero) = fun _ ↦ (0 : ZMod 2) := funext fun _ ↦ by
      rw [hβ₃_eq, ite_neg (wire_ne_of_lt (by dsimp [wZero, sgn]; omega)),
        ite_neg (fun ⟨k, hk⟩ ↦ by
          have hv := congrArg Fin.val hk; dsimp [wZero, mReg] at hv; omega)]
      dsimp only [γ₂]
      rw [hkeep2 wZero (by dsimp [wZero]; omega)
          (fun _ ↦ wire_ne_of_lt (by dsimp [wZero, mHi]; omega)),
        hkeep1 wZero (by dsimp [wZero]; omega), hkeep1a wZero hlo59, hz0]
    have hβ₃_m : (fun k : Fin 7 ↦ β₃ (mReg k)) =
        fun k : Fin 7 ↦ basisBits 7 zFin k + basisBits 7 zFin 6 := funext fun k ↦ by
      rw [hβ₃_eq, ite_neg (wire_ne_of_lt (by dsimp [mReg, sgn]; omega)), ite_pos ⟨k, rfl⟩,
        congrFun hz_bits k, congrFun hz_bits 6]
    change bitsVal (fun k ↦ s4 β₃ (mReg k)) = _
    rw [hval4, show (2 : ℕ) ^ (6 + 1) = 128 by decide, hβ₃_z0,
      show bitsVal (fun _ : Fin 7 ↦ (0 : ZMod 2)) = 0 by simp [bitsVal], zero_add, hβ₃_m,
      show β₃ sgn = basisBits 7 zFin 6 by rw [hβ₃_eq, ite_pos rfl, congrFun hz_bits 6],
      fold7_bits_val zFin]
    obtain ⟨hs0_r, hb0_r, hb1_r, hy0_r, hyp_r⟩ := coreViewOf303_reads β
    have hy0_eq : bitsVal (fun j ↦ β (wY0 ax j)) = regVal (axisBitRev6 (rElecSlot (QRegExt.ofFin
      posCoreWires) 0) ax) (coreViewOf303 β) :=
      congrArg bitsVal (funext fun j ↦ (hy0_r ax j).symm)
    have hyp_eq : bitsVal (fun j ↦ β (wYP ax j)) = regVal (axisBitRev6 (QRegExt.ofFin 18) ax)
      (partnerViewOf303 β) :=
      congrArg bitsVal (funext fun j ↦ (hyp_r ax j).symm)
    set y0 := regVal (axisBitRev6 (rElecSlot (QRegExt.ofFin posCoreWires) 0) ax)
      (coreViewOf303 β)
    set yP := regVal (axisBitRev6 (QRegExt.ofFin 18) ax) (partnerViewOf303 β)
    have _ : y0 < 64 ∧ yP < 64 := ⟨regVal_lt_two_pow _ _, regVal_lt_two_pow _ _⟩
    have hb0_vlt := ZMod.val_lt (β (wB0 ax))
    have hb1_vlt := ZMod.val_lt (β (wB1 ax))
    have hdecBit : ∀ b : ZMod 2, (if decide (b = 1) then 1 else 0) = b.val := fun b ↦ by
      rcases bit_cases b with rfl | rfl <;> rfl
    have hraw : (rawOrbitCoord128 slot2SwappedTo0 (coreViewOf303 β) (partnerViewOf303 β) ax).val =
        if β wS0 = 1 then ((2 * y0 + (β (wB0 ax)).val) + 128 - (2 * yP + (β (wB1 ax)).val)) % 128
        else 2 * (if slot2SwappedTo0 then y0 else yP) + (β (wB1 ax)).val := by
      dsimp only [rawOrbitCoord128, PosSlots24PartnerMux288.rawOrbitCoord128]
      rw [hs0_r]
      rcases bit_cases (β wS0) with hs00 | hs01
      · rw [hs00]
        simp only [zero_ne_one, ↓reduceIte]
        change 2 * (if slot2SwappedTo0 then y0 else yP) +
          (if decide (coreViewOf303 β (rCosetB1 (QRegExt.ofFin posCoreWires) ax) = 1)
            then 1 else 0) = _
        rw [hb1_r ax, hdecBit (β (wB1 ax))]
      · rw [hs01]
        simp only [↓reduceIte]
        change ((2 * y0 + (if decide (coreViewOf303 β
          (rCosetB0 (QRegExt.ofFin posCoreWires) ax) = 1) then 1 else 0)) + 128 -
          (2 * yP + (if decide (coreViewOf303 β
            (rCosetB1 (QRegExt.ofFin posCoreWires) ax) = 1) then 1 else 0))) % 128 = _
        rw [hb0_r ax, hb1_r ax, hdecBit (β (wB0 ax)), hdecBit (β (wB1 ax))]
    change (if zFin.val ≤ 64 then zFin.val else 128 - zFin.val) = _
    dsimp only [foldMag128]
    rw [hraw, ← ite_le64_eq_min128, show zFin.val = _ from hs2_val, hp_val]
    dsimp only [xFin]
    have h1s := stage1a_val slot2SwappedTo0 (β wS0) (β (wB0 ax)) (β (wB1 ax))
    rcases bit_cases (β wS0) with hs0 | hs0
    · cases slot2SwappedTo0
      · simp only [regD, hs0, zero_ne_one, Bool.false_eq_true, ↓reduceIte]
          at h1s ⊢
        exact congrArg (fun z ↦ if z ≤ 64 then z else 128 - z) (by omega)
      · simp only [regD, hs0, zero_ne_one, ↓reduceIte] at h1s ⊢
        exact congrArg (fun z ↦ if z ≤ 64 then z else 128 - z) (by omega)
    · cases slot2SwappedTo0
      · simp only [regD, regX, hs0, Bool.false_eq_true, ↓reduceIte, hy0_eq, hyp_eq] at h1s ⊢
        rw [← foldMag128_symm_sub (by omega) (by omega)]
        exact congrArg (fun z ↦ if z ≤ 64 then z else 128 - z) (congrArg (· % 128) (by omega))
      · simp only [regD, regX, hs0, ↓reduceIte, hy0_eq, hyp_eq] at h1s ⊢
        exact congrArg (fun z ↦ if z ≤ 64 then z else 128 - z) (congrArg (· % 128) (by omega))
def fReg6 (ax : Fin 3) (i : Fin 6) : Wire 303 := fReg ax i.castSucc
private theorem fReg6_injective (ax : Fin 3) : Function.Injective (fReg6 ax) := fun i j h ↦
  Fin.ext (by have hv := congrArg Fin.val h; dsimp [fReg6, fReg] at hv; omega)
theorem fReg6_disj {ax₁ ax₂ : Fin 3} (hax : ax₁ ≠ ax₂) (i j : Fin 6) :
    fReg6 ax₁ i ≠ fReg6 ax₂ j := fun h ↦ by
  have hv := congrArg Fin.val h
  dsimp [fReg6, fReg] at hv
  exact absurd (Fin.ext (by omega : ax₁.val = ax₂.val)) hax
def cFan3 (ctrl : Fin 3 → Wire 303) (hne : ∀ (ax : Fin 3) (i : Fin 6),
    ctrl ax ≠ fReg6 ax i) : CliffProg 303 :=
  .seq (fanoutCnot 6 (ctrl 0) (fReg6 0) (hne 0))
    (.seq (fanoutCnot 6 (ctrl 1) (fReg6 1) (hne 1)) (fanoutCnot 6 (ctrl 2) (fReg6 2) (hne 2)))
private theorem cFan3_supportsBelow (ctrl : Fin 3 → Wire 303) (hne : ∀ (ax₁ ax₂ : Fin 3) (i : Fin
    6), ctrl ax₁ ≠ fReg6 ax₂ i)
    (bound : ℕ) (hbound : 120 ≤ bound) (hc_lt : ∀ ax,
      (ctrl ax).val < bound) : (cFan3 ctrl (fun ax i ↦ hne ax ax i)).SupportsBelow bound :=
  have hf : ∀ (ax : Fin 3) (i : Fin 6), (fReg6 ax i).val < bound :=
    fun _ _ ↦ by dsimp [fReg6, fReg]; omega
  ⟨fanoutCnot_supportsBelow 6 (ctrl 0) (fReg6 0) _ bound (hc_lt 0) (hf 0),
    ⟨fanoutCnot_supportsBelow 6 (ctrl 1) (fReg6 1) _ bound (hc_lt 1) (hf 1),
      fanoutCnot_supportsBelow 6 (ctrl 2) (fReg6 2) _ bound (hc_lt 2) (hf 2)⟩⟩
private theorem cFan3_eval (ctrl : Fin 3 → Wire 303) (hne : ∀ (ax₁ ax₂ : Fin 3) (i : Fin 6),
    ctrl ax₁ ≠ fReg6 ax₂ i) (γ : BitAssignment 303) :
    (∀ ax i, (cFan3 ctrl (fun a j ↦ hne a a j)).eval γ (fReg6 ax i) = γ (fReg6 ax i) + γ (ctrl ax))
      ∧ (∀ w, (∀ ax i, w ≠ fReg6 ax i) →
    (cFan3 ctrl (fun a j ↦ hne a a j)).eval γ w = γ w) := by
  let γ₁ := (fanoutCnot 6 (ctrl 0) (fReg6 0) (hne 0 0)).eval γ
  let γ₂ := (fanoutCnot 6 (ctrl 1) (fReg6 1) (hne 1 1)).eval γ₁
  have h1 : ∀ w, γ₁ w = if ∃ j, w = fReg6 0 j then γ w + γ (ctrl 0) else γ w :=
    fanoutCnot_eval 6 (ctrl 0) (fReg6 0) (hne 0 0) (fReg6_injective 0) γ
  have hc1 : ∀ ax, γ₁ (ctrl ax) = γ (ctrl ax) := fun ax ↦ by
    rw [h1, ite_neg (fun ⟨j, hj⟩ ↦ hne ax 0 j hj)]
  have h2 : ∀ w, γ₂ w = if ∃ j, w = fReg6 1 j then γ₁ w + γ (ctrl 1) else γ₁ w := fun w ↦ by
    dsimp only [γ₂]
    rw [fanoutCnot_eval 6 (ctrl 1) (fReg6 1) (hne 1 1) (fReg6_injective 1) γ₁ w, hc1 1]
  have hc2 : γ₂ (ctrl 2) = γ (ctrl 2) := by
    rw [h2, ite_neg (fun ⟨j, hj⟩ ↦ hne 2 1 j hj), hc1 2]
  have h3 : ∀ w, (cFan3 ctrl (fun a j ↦ hne a a j)).eval γ w =
      if ∃ j, w = fReg6 2 j then γ₂ w + γ (ctrl 2) else γ₂ w := fun w ↦ by
    change (fanoutCnot 6 (ctrl 2) (fReg6 2) (hne 2 2)).eval γ₂ w = _
    rw [fanoutCnot_eval 6 (ctrl 2) (fReg6 2) (hne 2 2) (fReg6_injective 2) γ₂ w, hc2]
  have hdisj (a b : Fin 3) (hab : a ≠ b) (i : Fin 6) : ¬ ∃ j, fReg6 a i = fReg6 b j :=
    fun ⟨j, hj⟩ ↦ fReg6_disj hab i j hj
  have hhit (a : Fin 3) (i : Fin 6) : ∃ j, fReg6 a i = fReg6 a j := ⟨i, rfl⟩
  refine ⟨fun ax i ↦ ?_, fun w hw ↦ ?_⟩
  · rcases fin3_cases ax with rfl | rfl | rfl
    · rw [h3, ite_neg (hdisj 0 2 (by decide) i), h2, ite_neg (hdisj 0 1 (by decide) i), h1,
        ite_pos (hhit 0 i)]
    · rw [h3, ite_neg (hdisj 1 2 (by decide) i), h2, ite_pos (hhit 1 i), h1,
        ite_neg (hdisj 1 0 (by decide) i)]
    · rw [h3, ite_pos (hhit 2 i), h2, ite_neg (hdisj 2 1 (by decide) i), h1,
        ite_neg (hdisj 2 0 (by decide) i)]
  · rw [h3, ite_neg (fun ⟨j, hj⟩ ↦ hw 2 j hj), h2, ite_neg (fun ⟨j, hj⟩ ↦ hw 1 j hj),
      h1, ite_neg (fun ⟨j, hj⟩ ↦ hw 0 j hj)]
private theorem clamp65_lo_val : ∀ x : Fin 65,
    bitsVal (fun i : Fin 6 ↦ basisBits 7 ⟨x.val, lt_trans x.isLt (by decide)⟩ i.castSucc +
      basisBits 7 ⟨x.val, lt_trans x.isLt (by decide)⟩ 6) = min x.val 63 := by decide
private theorem clamp65_msb_eq : ∀ x : Fin 65,
    basisBits 7 ⟨x.val, lt_trans x.isLt (by decide)⟩ 6 =
      if x.val = 64 then 1 else 0 := by decide
private theorem unclamp65_val : ∀ y : Fin 65,
    bitsVal (fun k : Fin 7 ↦ if hk : k.val < 6 then
      basisBits 6 ⟨min y.val 63, by omega⟩ ⟨k.val, hk⟩ + (if y.val = 64 then 1 else 0)
      else (if y.val = 64 then 1 else 0)) = y.val := by decide
def wV6 : Wire 303 := ⟨159, by decide⟩
def wW6 : Wire 303 := ⟨160, by decide⟩
def wU6 : Wire 303 := ⟨161, by decide⟩
def ctxSort3Bits : TempCtx 303 :=
  let a6 := fReg 0 6
  let b6 := fReg 1 6
  let c6 := fReg 2 6
  let cPre : CliffProg 303 := .seq (.cnot a6 b6 (by decide)) (.cnot a6 c6 (by decide))
  let cMid : CliffProg 303 := .seq (.cnot a6 c6 (by decide)) (.seq (.cnot a6 b6 (by decide))
    (.seq (.cnot a6 wV6 (by decide)) (.seq (.cnot a6 wW6 (by decide))
      (.seq (.cnot b6 wW6 (by decide)) (.cnot c6 wW6 (by decide))))))
  let cPost : CliffProg 303 := .seq (.cnot wV6 wW6 (by decide)) (.cnot wU6 wW6 (by decide))
  (ctxCliffAlloc cPre).append
    ((ctxTempBit b6 c6 wV6 (by decide) (by decide) (by decide)).append
      ((ctxCliffAlloc cMid).append ((ctxTempBit wV6 wW6 wU6 (by decide) (by decide)
        (by decide)).append (ctxCliffAlloc cPost))))
@[simp] theorem ctxSort3Bits_countTempAnd : ctxSort3Bits.countTempAnd = 2 := by
  simp [ctxSort3Bits, tempCtx_append_count, ctxCliffAlloc, ctxTempBit, TempCtx.countTempAnd]
def ctrlClamp (ax : Fin 3) : Wire 303 := fReg ax 6
def ctrlUnclamp : Fin 3 → Wire 303 := ![wU6, wV6, wW6]
theorem ctrlClamp_ne_fReg6 (ax₁ ax₂ : Fin 3) (i : Fin 6) : ctrlClamp ax₁ ≠ fReg6 ax₂ i := by
  fin_cases ax₁ <;> fin_cases ax₂ <;> fin_cases i <;> decide
theorem ctrlUnclamp_ne_fReg6 (ax₁ ax₂ : Fin 3) (i : Fin 6) : ctrlUnclamp ax₁ ≠ fReg6 ax₂ i := by
  fin_cases ax₁ <;> fin_cases ax₂ <;> fin_cases i <;> decide
def u7Wire (k : Fin 7) : Wire 303 := if hk : k.val < 6 then fReg6 0 ⟨k.val, hk⟩ else wU6
def v7Wire (k : Fin 7) : Wire 303 := if hk : k.val < 6 then fReg6 1 ⟨k.val, hk⟩ else wV6
def w7Wire (k : Fin 7) : Wire 303 := if hk : k.val < 6 then fReg6 2 ⟨k.val, hk⟩ else wW6
def ctxSort3Clamp65 : TempCtx 303 :=
  let cClamp := cFan3 ctrlClamp (fun ax i ↦ ctrlClamp_ne_fReg6 ax ax i)
  let cUnclamp := cFan3 ctrlUnclamp (fun ax i ↦ ctrlUnclamp_ne_fReg6 ax ax i)
  let mm0 := ctxMinMaxInPlace 6 120 (by decide) (fReg6 0) (fReg6 1)
    (fun i ↦ fReg6_disj (by decide) i i)
    (fun _ ↦ by dsimp [fReg6, fReg]; omega) (fun _ ↦ by dsimp [fReg6, fReg]; omega)
  let mm1 := ctxMinMaxInPlace 6 133 (by decide) (fReg6 1) (fReg6 2)
    (fun i ↦ fReg6_disj (by decide) i i)
    (fun _ ↦ by dsimp [fReg6, fReg]; omega) (fun _ ↦ by dsimp [fReg6, fReg]; omega)
  let mm2 := ctxMinMaxInPlace 6 146 (by decide) (fReg6 0) (fReg6 1)
    (fun i ↦ fReg6_disj (by decide) i i)
    (fun _ ↦ by dsimp [fReg6, fReg]; omega) (fun _ ↦ by dsimp [fReg6, fReg]; omega)
  (ctxCliffAlloc cClamp).append
    (mm0.append (mm1.append (mm2.append (ctxSort3Bits.append (ctxCliffAlloc cUnclamp)))))
@[simp] theorem ctxSort3Clamp65_countTempAnd : ctxSort3Clamp65.countTempAnd = 38 := by
  simp [ctxSort3Clamp65, tempCtx_append_count, ctxCliffAlloc, TempCtx.countTempAnd]
theorem ScopedBlock.ctxSort3Clamp65_block
    (leaf body : TempPhaseProg 303) (sBody : BitAssignment 303 → BitAssignment 303)
    (hBody : ScopedBlock 303 (303 - 162) sBody leaf body) :
    ∃ setup : BitAssignment 303 → BitAssignment 303,
      ScopedBlock 303 (303 - 120) (fun β ↦ sBody (setup β)) leaf (ctxSort3Clamp65.plug body) ∧
      ∀ (β₃ : BitAssignment 303) (x : Fin 3 → Fin 65), cleanRem 303 (303 - 120) β₃ →
        (∀ ax : Fin 3, bitsVal (fun k ↦ β₃ (fReg ax k)) = (x ax).val) →
        let canon := sortTriple x
        cleanRem 303 (303 - 162) (setup β₃) ∧
        (∀ w : Wire 303, w.val < 60 → setup β₃ w = β₃ w) ∧
        bitsVal (fun k ↦ setup β₃ (u7Wire k)) = (canon 0).val ∧
        bitsVal (fun k ↦ setup β₃ (v7Wire k)) = (canon 1).val ∧
        bitsVal (fun k ↦ setup β₃ (w7Wire k)) = (canon 2).val := by
  let cClamp := cFan3 ctrlClamp (fun ax i ↦ ctrlClamp_ne_fReg6 ax ax i)
  let cUnclamp := cFan3 ctrlUnclamp (fun ax i ↦ ctrlUnclamp_ne_fReg6 ax ax i)
  let a6 := fReg 0 6
  let b6 := fReg 1 6
  let c6 := fReg 2 6
  let cPreS : CliffProg 303 := .seq (.cnot a6 b6 (by decide)) (.cnot a6 c6 (by decide))
  let cMidS : CliffProg 303 := .seq (.cnot a6 c6 (by decide)) (.seq (.cnot a6 b6 (by decide))
    (.seq (.cnot a6 wV6 (by decide)) (.seq (.cnot a6 wW6 (by decide))
      (.seq (.cnot b6 wW6 (by decide)) (.cnot c6 wW6 (by decide))))))
  let cPostS : CliffProg 303 := .seq (.cnot wV6 wW6 (by decide)) (.cnot wU6 wW6 (by decide))
  have hUnclamp := ScopedBlock.ctxCliff_single (M := 303) (cur := 162) (curIn := 162)
    (by decide) le_rfl cUnclamp
    (cFan3_supportsBelow ctrlUnclamp ctrlUnclamp_ne_fReg6 162 (by decide)
      (fun ax ↦ by fin_cases ax <;> decide)) hBody
  let sSort3 : BitAssignment 303 → BitAssignment 303 := fun γ ↦
    let s2 := cMidS.eval
      (Function.update (cPreS.eval γ) wV6 (cPreS.eval γ b6 * cPreS.eval γ c6))
    cPostS.eval (Function.update s2 wU6 (s2 wV6 * s2 wW6))
  have hSort3 : ScopedBlock 303 (303 - 159) (fun β ↦ sBody (cUnclamp.eval (sSort3 β))) leaf
    ((ctxSort3Bits.append (ctxCliffAlloc cUnclamp)).plug body) := by
    rw [TempCtx.append_plug]
    exact ScopedBlock.ctxCliff_append (M := 303) (cur := 159) (curIn := 159)
      (by decide) le_rfl cPreS (by dsimp [cPreS, CliffProg.SupportsBelow]; decide)
      (ScopedBlock.ctxTemp_append (cur := 159) (by decide) b6 c6 (by decide) (by decide)
        (by decide) (by decide) (by decide)
        (ScopedBlock.ctxCliff_append (cur := 160) (curIn := 161) (by decide) (by decide)
          cMidS (by dsimp [cMidS, CliffProg.SupportsBelow]; decide)
          (ScopedBlock.ctxTemp_append (cur := 161) (by decide) wV6 wW6 (by decide) (by decide)
            (by decide) (by decide) (by decide)
            (ScopedBlock.ctxCliff_single (cur := 162) (curIn := 162) (by decide) le_rfl
              cPostS (by dsimp [cPostS, CliffProg.SupportsBelow]; decide) hUnclamp))))
  have hf_lt : ∀ (ax : Fin 3) (i : Fin 6) (c : ℕ), 120 ≤ c → (fReg6 ax i).val < c :=
    fun _ _ _ hc ↦ by dsimp [fReg6, fReg]; omega
  obtain ⟨sMM2, hMM2, hSpecMM2⟩ := ScopedBlock.ctxMinMaxInPlace_block (M := 303)
    6 146 (by decide) (fReg6 0) (fReg6 1) (fun i ↦ fReg6_disj (by decide) i i)
    (fReg6_injective 0) (fReg6_injective 1) (fReg6_disj (by decide))
    (fun i ↦ hf_lt 0 i 146 (by decide)) (fun i ↦ hf_lt 1 i 146 (by decide)) leaf _ _ hSort3
  obtain ⟨sMM1, hMM1, hSpecMM1⟩ := ScopedBlock.ctxMinMaxInPlace_block (M := 303)
    6 133 (by decide) (fReg6 1) (fReg6 2) (fun i ↦ fReg6_disj (by decide) i i)
    (fReg6_injective 1) (fReg6_injective 2) (fReg6_disj (by decide))
    (fun i ↦ hf_lt 1 i 133 (by decide)) (fun i ↦ hf_lt 2 i 133 (by decide)) leaf _ _ hMM2
  obtain ⟨sMM0, hMM0, hSpecMM0⟩ := ScopedBlock.ctxMinMaxInPlace_block (M := 303)
    6 120 (by decide) (fReg6 0) (fReg6 1) (fun i ↦ fReg6_disj (by decide) i i)
    (fReg6_injective 0) (fReg6_injective 1) (fReg6_disj (by decide))
    (fun i ↦ hf_lt 0 i 120 le_rfl) (fun i ↦ hf_lt 1 i 120 le_rfl) leaf _ _ hMM1
  have hClamp := ScopedBlock.ctxCliff_append (M := 303) (cur := 120) (curIn := 120)
    (by decide) le_rfl cClamp (cFan3_supportsBelow ctrlClamp ctrlClamp_ne_fReg6 120 le_rfl
      (fun ax ↦ by dsimp [ctrlClamp, fReg]; omega))
    (by
      rw [← TempCtx.append_plug, ← TempCtx.append_plug, ← TempCtx.append_plug] at hMM0
      exact hMM0)
  refine ⟨fun β ↦ cUnclamp.eval (sSort3 (sMM2 (sMM1 (sMM0 (cClamp.eval β))))),
    hClamp, fun β₃ x hcl3 hx_val ↦ ?_⟩
  obtain ⟨hClampF, hClampOth⟩ := cFan3_eval ctrlClamp ctrlClamp_ne_fReg6 β₃
  let γ₀ := cClamp.eval β₃
  have hbits7 : ∀ ax : Fin 3, (fun k : Fin 7 ↦ β₃ (fReg ax k)) =
      basisBits 7 ⟨(x ax).val, lt_trans (x ax).isLt (by decide)⟩ := fun ax ↦
    (bits_eq_basisBits_of_val _).trans (congrArg (basisBits 7) (Fin.ext (hx_val ax)))
  have hγ₀_lo : ∀ ax : Fin 3,
      bitsVal (fun i : Fin 6 ↦ γ₀ (fReg6 ax i)) = min (x ax).val 63 := fun ax ↦
    (congrArg bitsVal (funext fun i ↦ (hClampF ax i).trans
      (congrArg₂ (· + ·) (congrFun (hbits7 ax) i.castSucc) (congrFun (hbits7 ax) 6)))).trans
      (clamp65_lo_val (x ax))
  have hγ₀_msb : ∀ ax : Fin 3,
      γ₀ (fReg ax 6) = if (x ax).val = 64 then 1 else 0 := fun ax ↦ by
    dsimp only [γ₀, cClamp]
    rw [hClampOth (fReg ax 6) (ctrlClamp_ne_fReg6 ax), congrFun (hbits7 ax) 6]
    exact clamp65_msb_eq (x ax)
  obtain ⟨hcl1, hkeep1, hmin0, hmax0⟩ := hSpecMM0 γ₀ fun w hw ↦ by
    dsimp only [γ₀, cClamp]
    rw [hClampOth w (fun _ _ ↦ wire_ne_of_gt (by dsimp [fReg6, fReg]; omega))]
    exact hcl3 w hw
  obtain ⟨hcl2, hkeep2, hmin1, hmax1⟩ := hSpecMM1 (sMM0 γ₀) hcl1
  obtain ⟨hcl3', hkeep3', hmin2, hmax2⟩ := hSpecMM2 (sMM1 (sMM0 γ₀)) hcl2
  let γ₃ := sMM2 (sMM1 (sMM0 γ₀))
  have hγ₁_f2 : (fun i ↦ sMM0 γ₀ (fReg6 2 i)) = fun i ↦ γ₀ (fReg6 2 i) := funext fun i ↦
    hkeep1 _ (hf_lt 2 i 120 le_rfl) (fReg6_disj (by decide) i) (fReg6_disj (by decide) i)
  have hγ₂_f0 : (fun i ↦ sMM1 (sMM0 γ₀) (fReg6 0 i)) = fun i ↦ sMM0 γ₀ (fReg6 0 i) :=
    funext fun i ↦ hkeep2 _ (hf_lt 0 i 133 (by decide)) (fReg6_disj (by decide) i)
      (fReg6_disj (by decide) i)
  have hγ₃_f2 : (fun i ↦ γ₃ (fReg6 2 i)) = fun i ↦ sMM1 (sMM0 γ₀) (fReg6 2 i) :=
    funext fun i ↦ hkeep3' _ (hf_lt 2 i 146 (by decide)) (fReg6_disj (by decide) i)
      (fReg6_disj (by decide) i)
  have hkeep03 : ∀ w : Wire 303, w.val < 120 → (∀ ax i, w ≠ fReg6 ax i) → γ₃ w = γ₀ w :=
    fun w hw hne ↦ (hkeep3' w (by omega) (hne 0) (hne 1)).trans
      ((hkeep2 w (by omega) (hne 1) (hne 2)).trans (hkeep1 w hw (hne 0) (hne 1)))
  let γ₄ := sSort3 γ₃
  have hSortEq : ∀ w : Wire 303, γ₄ w =
      if w = wU6 then ((γ₃ b6 + γ₃ a6) * (γ₃ c6 + γ₃ a6) + γ₃ a6) * (γ₃ a6 + γ₃ b6 + γ₃ c6)
      else if w = wV6 then (γ₃ b6 + γ₃ a6) * (γ₃ c6 + γ₃ a6) + γ₃ a6
      else if w = wW6 then (γ₃ a6 + γ₃ b6 + γ₃ c6) +
        ((γ₃ b6 + γ₃ a6) * (γ₃ c6 + γ₃ a6) + γ₃ a6) +
        (((γ₃ b6 + γ₃ a6) * (γ₃ c6 + γ₃ a6) + γ₃ a6) * (γ₃ a6 + γ₃ b6 + γ₃ c6))
      else γ₃ w := fun w ↦ by
    have hwW0 : γ₃ wW6 = 0 := hcl3' wW6 (by decide)
    have hv : a6.val = 67 ∧ b6.val = 87 ∧ c6.val = 107 ∧
        wV6.val = 159 ∧ wW6.val = 160 ∧ wU6.val = 161 := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
    let s2 := cMidS.eval
      (Function.update (cPreS.eval γ₃) wV6 (cPreS.eval γ₃ b6 * cPreS.eval γ₃ c6))
    have hs2 : ∀ q : Wire 303, s2 q =
        if q = wV6 then (γ₃ b6 + γ₃ a6) * (γ₃ c6 + γ₃ a6) + γ₃ a6
        else if q = wW6 then γ₃ a6 + γ₃ b6 + γ₃ c6 else γ₃ q := fun q ↦ by
      dsimp only [s2, cMidS, cPreS]
      rcases eq_or_ne q wV6 with rfl | hqv
      · simp [seq_eval_w, cnot_eval_w, wire303_eq_iff, hv]
      · rcases eq_or_ne q wW6 with rfl | hqw
        · simp [seq_eval_w, cnot_eval_w, wire303_eq_iff, hv, hwW0]
        · rcases eq_or_ne q b6 with rfl | hqb
          · simp [seq_eval_w, cnot_eval_w, wire303_eq_iff, hv]
          · rcases eq_or_ne q c6 with rfl | hqc
            · simp [seq_eval_w, cnot_eval_w, wire303_eq_iff, hv]
            · simp [seq_eval_w, cnot_eval_w, hqv, hqw, hqb, hqc]
    change cPostS.eval (Function.update s2 wU6 (s2 wV6 * s2 wW6)) w = _
    dsimp only [cPostS]
    rcases eq_or_ne w wU6 with rfl | hwu
    · simp [seq_eval_w, cnot_eval_w, hs2, wire303_eq_iff, hv]
    · rcases eq_or_ne w wV6 with rfl | hwv
      · simp [seq_eval_w, cnot_eval_w, hs2, wire303_eq_iff, hv]
      · rcases eq_or_ne w wW6 with rfl | hww
        · simp [seq_eval_w, cnot_eval_w, hs2, wire303_eq_iff, hv]
        · simp [seq_eval_w, cnot_eval_w, hs2, hwu, hwv, hww]
  have hkeep4 : ∀ w : Wire 303, w.val < 159 → γ₄ w = γ₃ w := fun w hw ↦ by
    rw [hSortEq w, ite_neg (wire_ne_of_lt (by dsimp [wU6]; omega)),
      ite_neg (wire_ne_of_lt (by dsimp [wV6]; omega)),
      ite_neg (wire_ne_of_lt (by dsimp [wW6]; omega))]
  let γ₅ := cUnclamp.eval γ₄
  obtain ⟨hUnclampF, hUnclampOth⟩ := cFan3_eval ctrlUnclamp ctrlUnclamp_ne_fReg6 γ₄
  have hValMin {a b : Fin 65} : (min a b).val = min a.val b.val := by
    by_cases h : a ≤ b <;> simp [min_def, h]
  have hValMax {a b : Fin 65} : (max a b).val = max a.val b.val := by
    by_cases h : a ≤ b <;> simp [max_def, h]
  let canon := sortTriple x
  have hcu : (canon 0).val = min (min (x 0).val (x 1).val) (min (max (x 0).val (x 1).val) (x 2).val)
    := by
    change (min (min (x 0) (x 1)) (min (max (x 0) (x 1)) (x 2))).val = _
    simp only [hValMin, hValMax]
  have hcv : (canon 1).val = max (min (x 0).val (x 1).val) (min (max (x 0).val (x 1).val) (x 2).val)
    := by
    change (max (min (x 0) (x 1)) (min (max (x 0) (x 1)) (x 2))).val = _
    simp only [hValMin, hValMax]
  have hcw : (canon 2).val = max (max (x 0).val (x 1).val) (x 2).val := by
    change (max (max (x 0) (x 1)) (x 2)).val = _
    simp only [hValMax]
  have hγ₄_f : ∀ ax : Fin 3, (fun i ↦ γ₄ (fReg6 ax i)) = fun i ↦ γ₃ (fReg6 ax i) :=
    fun ax ↦ funext fun i ↦ hkeep4 _ (hf_lt ax i 159 (by decide))
  have hlo : ∀ ax : Fin 3,
      bitsVal (fun i : Fin 6 ↦ γ₄ (fReg6 ax i)) = min (canon ax).val 63 := fun ax ↦ by
    rcases fin3_cases ax with rfl | rfl | rfl
    · rw [hγ₄_f 0]
      dsimp only [γ₃]
      rw [hmin2, hγ₂_f0, hmin0, hmin1, hmax0, hγ₁_f2, hγ₀_lo 0, hγ₀_lo 1, hγ₀_lo 2, hcu]
      omega
    · rw [hγ₄_f 1]
      dsimp only [γ₃]
      rw [hmax2, hγ₂_f0, hmin0, hmin1, hmax0, hγ₁_f2, hγ₀_lo 0, hγ₀_lo 1, hγ₀_lo 2, hcv]
      omega
    · rw [hγ₄_f 2, hγ₃_f2, hmax1, hγ₁_f2, hmax0, hγ₀_lo 0, hγ₀_lo 1, hγ₀_lo 2, hcw]
      omega
  have hγ₃_msb : ∀ ax : Fin 3, γ₃ (fReg ax 6) = if (x ax).val = 64 then 1 else 0 := fun ax ↦
    (hkeep03 (fReg ax 6) (by dsimp [fReg]; omega) (ctrlClamp_ne_fReg6 ax)).trans (hγ₀_msb ax)
  have hmsb4 : ∀ ax : Fin 3, γ₄ (ctrlUnclamp ax) = if (canon ax).val = 64 then 1 else 0 :=
    fun ax ↦ by
      have hbool : ∀ b0 b1 b2 : Bool,
          let a : ZMod 2 := if b0 then 1 else 0
          let b : ZMod 2 := if b1 then 1 else 0
          let c : ZMod 2 := if b2 then 1 else 0
          let m : ZMod 2 := (b + a) * (c + a) + a
          m * (a + b + c) = (if b0 && b1 && b2 then 1 else 0) ∧
          m = (if b0 && b1 || b0 && b2 || b1 && b2 then 1 else 0) ∧
          ((a + b + c) + m + m * (a + b + c) = if b0 || b1 || b2 then 1 else 0) := by decide
      have h012 := hbool (decide ((x 0).val = 64)) (decide ((x 1).val = 64))
        (decide ((x 2).val = 64))
      have hx0 := (x 0).isLt
      have hx1 := (x 1).isLt
      have hx2 := (x 2).isLt
      dsimp only at h012
      simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h012
      rcases fin3_cases ax with rfl | rfl | rfl
      · rw [show ctrlUnclamp 0 = wU6 from rfl, hSortEq wU6, ite_pos rfl]
        dsimp only [a6, b6, c6]
        rw [hγ₃_msb 0, hγ₃_msb 1, hγ₃_msb 2, h012.1, hcu]
        exact if_congr (by omega) rfl rfl
      · rw [show ctrlUnclamp 1 = wV6 from rfl, hSortEq wV6, ite_neg (by decide : wV6 ≠ wU6),
          ite_pos rfl]
        dsimp only [a6, b6, c6]
        rw [hγ₃_msb 0, hγ₃_msb 1, hγ₃_msb 2, h012.2.1, hcv]
        exact if_congr (by omega) rfl rfl
      · rw [show ctrlUnclamp 2 = wW6 from rfl, hSortEq wW6, ite_neg (by decide : wW6 ≠ wU6),
          ite_neg (by decide : wW6 ≠ wV6), ite_pos rfl]
        dsimp only [a6, b6, c6]
        rw [hγ₃_msb 0, hγ₃_msb 1, hγ₃_msb 2, h012.2.2, hcw]
        exact if_congr (by omega) rfl rfl
  have hunclamp : ∀ (ax : Fin 3) (w7 : Fin 7 → Wire 303),
      (∀ k : Fin 7, w7 k = if hk : k.val < 6 then fReg6 ax ⟨k.val, hk⟩ else ctrlUnclamp ax) →
      bitsVal (fun k ↦ γ₅ (w7 k)) = (canon ax).val := fun ax w7 hw7 ↦ by
    have hbb : (fun i : Fin 6 ↦ γ₄ (fReg6 ax i)) = basisBits 6 ⟨min (canon ax).val 63, by omega⟩ :=
      (bits_eq_basisBits_of_val _).trans (congrArg (basisBits 6) (Fin.ext (hlo ax)))
    refine (congrArg bitsVal (funext fun k ↦ ?_)).trans (unclamp65_val (canon ax))
    rw [hw7 k]
    by_cases hk : k.val < 6
    · rw [dite_pos hk, dite_pos hk]
      exact (hUnclampF ax ⟨k.val, hk⟩).trans
        (congrArg₂ (· + ·) (congrFun hbb ⟨k.val, hk⟩) (hmsb4 ax))
    · rw [dite_neg hk, dite_neg hk]
      exact (hUnclampOth (ctrlUnclamp ax) (ctrlUnclamp_ne_fReg6 ax)).trans (hmsb4 ax)
  refine ⟨fun w hw ↦ ?_, fun w hw ↦ ?_,
    hunclamp 0 u7Wire (fun _ ↦ rfl), hunclamp 1 v7Wire (fun _ ↦ rfl),
    hunclamp 2 w7Wire (fun _ ↦ rfl)⟩
  · change (cFan3 ctrlUnclamp (fun a j ↦ ctrlUnclamp_ne_fReg6 a a j)).eval γ₄ w = 0
    rw [hUnclampOth w (fun _ _ ↦ wire_ne_of_gt (by dsimp [fReg6, fReg]; omega)), hSortEq w,
      ite_neg (wire_ne_of_gt (by dsimp [wU6]; omega)),
      ite_neg (wire_ne_of_gt (by dsimp [wV6]; omega)),
      ite_neg (wire_ne_of_gt (by dsimp [wW6]; omega))]
    exact hcl3' w (by omega)
  · have hne : ∀ ax i, w ≠ fReg6 ax i :=
      fun _ _ ↦ wire_ne_of_lt (by dsimp [fReg6, fReg]; omega)
    exact (hUnclampOth w hne).trans
      ((hkeep4 w (by omega)).trans ((hkeep03 w (by omega) hne).trans (hClampOth w hne)))
theorem list_map_eq_of_forall {α β : Type*} {f g : α → β} :
    ∀ {xs : List α}, (∀ x ∈ xs, f x = g x) → xs.map f = xs.map g
  | [], _ => rfl
  | x :: _, h =>
      congrArg₂ List.cons (h x (by simp))
        (list_map_eq_of_forall fun y hy ↦ h y (List.mem_cons_of_mem x hy))
theorem snoc_forall {α : Type*} {xs : List α} {a : α} {P : α → Prop} (hxs : ∀ x ∈ xs,
    P x) (ha : P a) : ∀ x ∈ xs ++ [a], P x :=
  fun x hx ↦ (List.mem_append.mp hx).elim (hxs x) fun h ↦ by rwa [List.mem_singleton.mp h]
def maskXorBits : ℕ → List (ZMod 2) → ZMod 2
  | _, [] => 0
  | mask, b :: bs => (if mask % 2 == 1 then b else 0) + maskXorBits (mask / 2) bs
@[simp] theorem maskXorBits_nil (m : ℕ) : maskXorBits m [] = 0 := by cases m <;> rfl
def xorMaskedList {M : ℕ} (dst : Wire M) :
    (mask : ℕ) → (accW : List (Wire M)) → (∀ w ∈ accW, w ≠ dst) → CliffProg M
  | _, [], _ => .nil
  | mask, w :: ws, hne =>
      let rest :=
        xorMaskedList dst (mask / 2) ws (fun u hu ↦ hne u (List.mem_cons_of_mem w hu))
      if mask % 2 == 1 then .seq (.cnot w dst (hne w (by simp))) rest else rest
theorem xorMaskedList_disjoint {M : ℕ} {mutW : Wire M → Prop}
    (dst : Wire M) (hnd : ¬ mutW dst) :
    ∀ (mask : ℕ) (accW : List (Wire M)) (hne : ∀ w ∈ accW, w ≠ dst),
      (∀ w ∈ accW, ¬ mutW w) → CliffDisjoint mutW (xorMaskedList dst mask accW hne)
  | _, [], _, _ => trivial
  | mask, w :: ws, hne, hnw => by
      dsimp only [xorMaskedList]
      have hr := xorMaskedList_disjoint dst hnd (mask / 2) ws
        (fun u hu ↦ hne u (List.mem_cons_of_mem w hu))
        (fun u hu ↦ hnw u (List.mem_cons_of_mem w hu))
      split_ifs
      · exact ⟨⟨hnw w (by simp), hnd⟩, hr⟩
      · exact hr
theorem xorMaskedList_supportsBelow {M : ℕ}
    (dst : Wire M) (bound : ℕ) (hd_lt : dst.val < bound) :
    ∀ (mask : ℕ) (accW : List (Wire M)) (hne : ∀ w ∈ accW, w ≠ dst),
      (∀ w ∈ accW, w.val < bound) → (xorMaskedList dst mask accW hne).SupportsBelow bound
  | _, [], _, _ => trivial
  | mask, w :: ws, hne, hlt => by
      dsimp only [xorMaskedList]
      have hr := xorMaskedList_supportsBelow dst bound hd_lt (mask / 2) ws
        (fun u hu ↦ hne u (List.mem_cons_of_mem w hu))
        (fun u hu ↦ hlt u (List.mem_cons_of_mem w hu))
      split_ifs
      · exact ⟨⟨hlt w (by simp), hd_lt⟩, hr⟩
      · exact hr
theorem xorMaskedList_eval {M : ℕ} (dst : Wire M) :
    ∀ (mask : ℕ) (accW : List (Wire M)) (hne : ∀ w ∈ accW, w ≠ dst) (γ : BitAssignment M),
      (xorMaskedList dst mask accW hne).eval γ =
        Function.update γ dst (γ dst + maskXorBits mask (accW.map γ))
  | _, [], _, γ => funext fun q ↦ by
      rcases eq_or_ne q dst with rfl | hq
      · simp [xorMaskedList, CliffProg.eval]
      · simp [xorMaskedList, CliffProg.eval, hq]
  | mask, w :: ws, hne, γ => by
      dsimp only [xorMaskedList, List.map, maskXorBits]
      have hne_r : ∀ u ∈ ws, u ≠ dst := fun u hu ↦ hne u (List.mem_cons_of_mem w hu)
      split_ifs
      · dsimp only [CliffProg.eval]
        let γ₁ := Function.update γ dst (γ dst + γ w)
        rw [xorMaskedList_eval dst (mask / 2) ws hne_r γ₁,
          list_map_eq_of_forall (f := γ₁) (g := γ)
            fun u hu ↦ Function.update_of_ne (hne_r u hu) _ _]
        funext q
        simp only [γ₁, upd_app]
        split_ifs
        · exact add_assoc _ _ _
        · rfl
      · rw [xorMaskedList_eval dst (mask / 2) ws hne_r γ, zero_add]
theorem xorMaskedList_inv_self {M : ℕ} (dst : Wire M) (mask : ℕ) (accW : List (Wire M)) (hne : ∀ w ∈
    accW, w ≠ dst) (γ : BitAssignment M) :
    (xorMaskedList dst mask accW hne).eval ((xorMaskedList dst mask accW hne).eval γ) = γ := by
  have h1 := xorMaskedList_eval dst mask accW hne γ
  rw [xorMaskedList_eval dst mask accW hne, h1,
    list_map_eq_of_forall (f := Function.update γ dst _) (g := γ)
      fun u hu ↦ Function.update_of_ne (hne u hu) _ _]
  funext q
  simp only [upd_app]
  rcases eq_or_ne q dst with rfl | hq
  · simp
  · simp [hq]
def evalLinAndSteps : List (ℕ × ℕ) → List (ZMod 2) → List (ZMod 2)
  | [], acc => acc
  | (ma, mb) :: rest, acc =>
      evalLinAndSteps rest (acc ++ [maskXorBits ma acc * maskXorBits mb acc])
def ancList {M : ℕ} : (start len : ℕ) → start + len ≤ M → List (Wire M)
  | _, 0, _ => []
  | start, len + 1, _ => ⟨start, by omega⟩ :: ancList (start + 1) len (by omega)
theorem ancList_mem_bounds {M : ℕ} : ∀ (start len : ℕ) (h : start + len ≤ M) (w : Wire M),
    w ∈ ancList start len h → start ≤ w.val ∧ w.val < start + len
  | _, 0, _, _, hw => by simp [ancList] at hw
  | start, len + 1, _, w, hw => by
      rcases List.mem_cons.mp hw with rfl | hrest
      · exact ⟨le_rfl, by dsimp; omega⟩
      · have hb := ancList_mem_bounds (start + 1) len (by omega) w hrest
        exact ⟨by omega, by omega⟩
def ctxLinAndSteps {M : ℕ} : (cur : ℕ) → (steps : List (ℕ × ℕ)) → (cur + steps.length ≤ M) →
    (scrL scrR : Wire M) → scrL ≠ scrR → scrL.val < cur → scrR.val < cur →
    (accW : List (Wire M)) → (∀ w ∈ accW, w.val < cur) → (∀ w ∈ accW, w ≠ scrL) →
    (∀ w ∈ accW, w ≠ scrR) → TempCtx M
  | _, [], _, _, _, _, _, _, _, _, _, _ => .hole
  | cur, (ma, mb) :: rest, hcur, scrL, scrR, hLR, hL_lt, hR_lt, accW,
    hacc_lt, hacc_neL, hacc_neR =>
      let anc : Wire M := ⟨cur, by dsimp [List.length] at hcur; omega⟩
      let cL := xorMaskedList scrL ma accW hacc_neL
      let cR := xorMaskedList scrR mb accW hacc_neR
      (ctxCliffAlloc (.seq cL cR)).append
        ((ctxTempBit scrL scrR anc hLR (wire_ne_of_lt hL_lt) (wire_ne_of_lt hR_lt)).append
          ((ctxCliffAlloc (.seq cR cL)).append
            (ctxLinAndSteps (cur + 1) rest (by dsimp [List.length] at hcur; omega)
              scrL scrR hLR (lt_trans hL_lt (Nat.lt_succ_self cur))
              (lt_trans hR_lt (Nat.lt_succ_self cur)) (accW ++ [anc])
              (snoc_forall (fun w h ↦ lt_trans (hacc_lt w h) (Nat.lt_succ_self cur))
                (Nat.lt_succ_self cur))
              (snoc_forall hacc_neL (wire_ne_of_gt hL_lt))
              (snoc_forall hacc_neR (wire_ne_of_gt hR_lt)))))
@[simp] theorem ctxLinAndSteps_countTempAnd {M : ℕ} :
    ∀ (steps : List (ℕ × ℕ)) (cur : ℕ) (hcur : cur + steps.length ≤ M)
      (scrL scrR : Wire M) (hLR : scrL ≠ scrR) (hL_lt : scrL.val < cur)
      (hR_lt : scrR.val < cur) (accW : List (Wire M)) (hacc_lt : ∀ w ∈ accW, w.val < cur)
      (hacc_neL : ∀ w ∈ accW, w ≠ scrL) (hacc_neR : ∀ w ∈ accW, w ≠ scrR),
      (ctxLinAndSteps cur steps hcur scrL scrR hLR hL_lt hR_lt
        accW hacc_lt hacc_neL hacc_neR).countTempAnd = steps.length
  | [], _, _, _, _, _, _, _, _, _, _, _ => rfl
  | (_, _) :: rest, cur, _, _, _, _, _, _, _, _, _, _ => by
      simp only [ctxLinAndSteps, tempCtx_append_count, ctxCliffAlloc, ctxTempBit,
        TempCtx.countTempAnd, List.length]
      rw [ctxLinAndSteps_countTempAnd rest (cur + 1)]
      omega
theorem ctxLinAndSteps_disj {M : ℕ} {mutW : Wire M → Prop} :
    ∀ (steps : List (ℕ × ℕ)) (cur : ℕ) (hcur : cur + steps.length ≤ M)
      (scrL scrR : Wire M) (hLR : scrL ≠ scrR) (hL_lt : scrL.val < cur)
      (hR_lt : scrR.val < cur) (accW : List (Wire M)) (hacc_lt : ∀ w ∈ accW, w.val < cur)
      (hacc_neL : ∀ w ∈ accW, w ≠ scrL) (hacc_neR : ∀ w ∈ accW, w ≠ scrR),
      ¬ mutW scrL → ¬ mutW scrR → (∀ w ∈ accW, ¬ mutW w) →
      (∀ w : Wire M, cur ≤ w.val → ¬ mutW w) →
      (ctxLinAndSteps cur steps hcur scrL scrR hLR hL_lt hR_lt
        accW hacc_lt hacc_neL hacc_neR).DisjointFrom mutW
  | [], _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => trivial
  | (ma, mb) :: rest, cur, hcur, scrL, scrR, hLR, hL_lt, hR_lt,
    accW, hacc_lt, hacc_neL, hacc_neR, hnL, hnR, hnAcc, hnCur => by
      let anc : Wire M := ⟨cur, by dsimp [List.length] at hcur; omega⟩
      have hnAnc : ¬ mutW anc := hnCur anc le_rfl
      have hdL := xorMaskedList_disjoint scrL hnL ma accW hacc_neL hnAcc
      have hdR := xorMaskedList_disjoint scrR hnR mb accW hacc_neR hnAcc
      have hdRest := ctxLinAndSteps_disj rest (cur + 1)
        (by dsimp [List.length] at hcur; omega) scrL scrR hLR
        (lt_trans hL_lt (Nat.lt_succ_self cur)) (lt_trans hR_lt (Nat.lt_succ_self cur))
        (accW ++ [anc])
        (snoc_forall (fun w h ↦ lt_trans (hacc_lt w h) (Nat.lt_succ_self cur))
          (Nat.lt_succ_self cur))
        (snoc_forall hacc_neL (wire_ne_of_gt hL_lt))
        (snoc_forall hacc_neR (wire_ne_of_gt hR_lt))
        hnL hnR (snoc_forall hnAcc hnAnc) (fun w hw ↦ hnCur w (by omega))
      exact TempCtx.disjointFrom_append (ctxCliffAlloc_disjoint ⟨hdL, hdR⟩)
        (TempCtx.disjointFrom_append ⟨hnL, hnR, hnAnc, trivial⟩
          (TempCtx.disjointFrom_append (ctxCliffAlloc_disjoint ⟨hdR, hdL⟩) hdRest))
theorem ScopedBlock.ctxLinAndSteps_block {M : ℕ} :
    ∀ (steps : List (ℕ × ℕ)) (cur : ℕ) (hcur : cur + steps.length ≤ M)
      (scrL scrR : Wire M) (hLR : scrL ≠ scrR) (hL_lt : scrL.val < cur)
      (hR_lt : scrR.val < cur) (accW : List (Wire M)) (hacc_lt : ∀ w ∈ accW, w.val < cur)
      (hacc_neL : ∀ w ∈ accW, w ≠ scrL) (hacc_neR : ∀ w ∈ accW, w ≠ scrR)
      (leaf body : TempPhaseProg M) (sBody : BitAssignment M → BitAssignment M),
      ScopedBlock M (M - (cur + steps.length)) sBody leaf body →
      ∃ setup : BitAssignment M → BitAssignment M,
        ScopedBlock M (M - cur) (fun β ↦ sBody (setup β)) leaf
          ((ctxLinAndSteps cur steps hcur scrL scrR hLR hL_lt hR_lt
            accW hacc_lt hacc_neL hacc_neR).plug body) ∧
        ∀ γ : BitAssignment M, cleanRem M (M - cur) γ → γ scrL = 0 → γ scrR = 0 →
          cleanRem M (M - (cur + steps.length)) (setup γ) ∧
          (∀ w : Wire M, w.val < cur → setup γ w = γ w) ∧
          (accW ++ ancList cur steps.length hcur).map (setup γ) =
            evalLinAndSteps steps (accW.map γ)
  | [], _, _, _, _, _, _, _, _, _, _, _, _, _, _, hBody =>
      ⟨id, hBody, fun _ hcl _ _ ↦ ⟨hcl, fun _ _ ↦ rfl, by simp [ancList, evalLinAndSteps]⟩⟩
  | (ma, mb) :: rest, cur, hcur, scrL, scrR, hLR, hL_lt, hR_lt,
    accW, hacc_lt, hacc_neL, hacc_neR, leaf, body, sBody, hBody => by
      have hcur1 : cur + 1 ≤ M := by dsimp [List.length] at hcur; omega
      have hcur' : (cur + 1) + rest.length ≤ M := by dsimp [List.length] at hcur; omega
      let anc : Wire M := ⟨cur, hcur1⟩
      let cL := xorMaskedList scrL ma accW hacc_neL
      let cR := xorMaskedList scrR mb accW hacc_neR
      have hsL := xorMaskedList_supportsBelow scrL cur hL_lt ma accW hacc_neL hacc_lt
      have hsR := xorMaskedList_supportsBelow scrR cur hR_lt mb accW hacc_neR hacc_lt
      obtain ⟨sTail, h4, hSpec4⟩ := ScopedBlock.ctxLinAndSteps_block rest (cur + 1) hcur'
        scrL scrR hLR (lt_trans hL_lt (Nat.lt_succ_self cur))
        (lt_trans hR_lt (Nat.lt_succ_self cur)) (accW ++ [anc])
        (snoc_forall (fun w h ↦ lt_trans (hacc_lt w h) (Nat.lt_succ_self cur))
          (Nat.lt_succ_self cur))
        (snoc_forall hacc_neL (wire_ne_of_gt hL_lt))
        (snoc_forall hacc_neR (wire_ne_of_gt hR_lt))
        leaf body sBody (hBody.cast_rem (by dsimp [List.length]; omega))
      let s012 : BitAssignment M → BitAssignment M := fun γ ↦ (.seq cR cL : CliffProg M).eval
        (Function.update ((.seq cL cR : CliffProg M).eval γ) anc
          ((.seq cL cR : CliffProg M).eval γ scrL * (.seq cL cR : CliffProg M).eval γ scrR))
      refine ⟨fun γ ↦ sTail (s012 γ),
        ScopedBlock.ctxSandwich_append hcur1 (.seq cL cR) (.seq cR cL) scrL scrR hLR
          hL_lt hR_lt (wire_ne_of_lt hL_lt) (wire_ne_of_lt hR_lt) ⟨hsL, hsR⟩
          ⟨CliffProg.supportsBelow_mono (by omega) hsR,
            CliffProg.supportsBelow_mono (by omega) hsL⟩ h4,
        fun γ hcl hL0 hR0 ↦ ?_⟩
      let bit := maskXorBits ma (accW.map γ) * maskXorBits mb (accW.map γ)
      have hs012_eq : s012 γ = Function.update γ anc bit := by
        have hcL : cL.eval γ = Function.update γ scrL (maskXorBits ma (accW.map γ)) := by
          rw [xorMaskedList_eval, hL0, zero_add]
        have hcPre : (CliffProg.seq cL cR).eval γ = Function.update (cL.eval γ) scrR (maskXorBits mb
          (accW.map γ)) := by
          change cR.eval (cL.eval γ) = _
          rw [xorMaskedList_eval, hcL, Function.update_of_ne hLR.symm, hR0, zero_add,
            list_map_eq_of_forall (f := Function.update γ scrL _) (g := γ)
              (fun u hu ↦ Function.update_of_ne (hacc_neL u hu) _ _)]
        have hprod : (CliffProg.seq cL cR).eval γ scrL * (CliffProg.seq cL cR).eval γ scrR = bit :=
          by
          rw [hcPre, Function.update_of_ne hLR, Function.update_self, hcL, Function.update_self]
        dsimp only [s012]
        rw [hprod, CliffProg.eval_update_above (.seq cR cL) ⟨hsR, hsL⟩ _ anc le_rfl bit]
        change Function.update (cL.eval (cR.eval (cR.eval (cL.eval γ)))) anc bit = _
        rw [xorMaskedList_inv_self, xorMaskedList_inv_self]
      obtain ⟨hclT, hkeepT, hmapT⟩ := hSpec4 (s012 γ)
        (fun w hw ↦ by
          rw [hs012_eq, Function.update_of_ne
            (wire_ne_of_gt (lt_of_lt_of_le (Nat.lt_succ_self cur) (by omega)))]
          exact hcl w (by omega))
        (by rw [hs012_eq, Function.update_of_ne (wire_ne_of_lt hL_lt), hL0])
        (by rw [hs012_eq, Function.update_of_ne (wire_ne_of_lt hR_lt), hR0])
      refine ⟨by simpa [List.length, Nat.add_assoc, Nat.add_comm 1 rest.length] using hclT,
        fun w hw ↦ ?_, ?_⟩
      · dsimp only
        rw [hkeepT w (by omega), hs012_eq, Function.update_of_ne (wire_ne_of_lt hw)]
      · dsimp only
        rw [show accW ++ ancList cur ((ma, mb) :: rest).length hcur =
            (accW ++ [anc]) ++ ancList (cur + 1) rest.length hcur' by
              simp [ancList, anc, List.append_assoc],
          hmapT, List.map_append, hs012_eq, list_map_eq_of_forall
            (f := Function.update γ anc bit) (g := γ)
            (fun u hu ↦ Function.update_of_ne (wire_ne_of_lt (hacc_lt u hu)) _ _)]
        simp [bit, Function.update_self, evalLinAndSteps]
def writeLinAndOuts {M : ℕ} (fullAccW : List (Wire M)) : (W outBase : ℕ) → outBase + W ≤ M →
    (∀ w ∈ fullAccW, w.val < outBase) → (Fin W → ℕ) → CliffProg M
  | 0, _, _, _, _ => .nil
  | W + 1, outBase, _, hacc_lt, masks =>
      .seq (xorMaskedList ⟨outBase, by omega⟩ (masks 0) fullAccW
        (fun w hw ↦ wire_ne_of_lt (hacc_lt w hw)))
        (writeLinAndOuts fullAccW W (outBase + 1) (by omega)
          (fun w hw ↦ lt_trans (hacc_lt w hw) (Nat.lt_succ_self outBase))
          (fun j ↦ masks j.succ))
theorem writeLinAndOuts_disjoint {M : ℕ} {mutW : Wire M → Prop}
    (fullAccW : List (Wire M)) (hnAcc : ∀ w ∈ fullAccW, ¬ mutW w) :
    ∀ (W outBase : ℕ) (hout : outBase + W ≤ M)
      (hacc_lt : ∀ w ∈ fullAccW, w.val < outBase) (masks : Fin W → ℕ),
      (∀ w : Wire M, outBase ≤ w.val → ¬ mutW w) →
      CliffDisjoint mutW (writeLinAndOuts fullAccW W outBase hout hacc_lt masks)
  | 0, _, _, _, _, _ => trivial
  | W + 1, outBase, _, hacc_lt, masks, hnOut =>
      ⟨xorMaskedList_disjoint ⟨outBase, by omega⟩ (hnOut _ le_rfl) (masks 0) fullAccW
          (fun w hw ↦ wire_ne_of_lt (hacc_lt w hw)) hnAcc,
        writeLinAndOuts_disjoint fullAccW hnAcc W (outBase + 1) (by omega)
          (fun w hw ↦ lt_trans (hacc_lt w hw) (Nat.lt_succ_self outBase))
          (fun j ↦ masks j.succ) (fun w hw ↦ hnOut w (by omega))⟩
theorem writeLinAndOuts_supportsBelow {M : ℕ} (fullAccW : List (Wire M)) :
    ∀ (W outBase : ℕ) (hout : outBase + W ≤ M)
      (hacc_lt : ∀ w ∈ fullAccW, w.val < outBase) (masks : Fin W → ℕ),
      (writeLinAndOuts fullAccW W outBase hout hacc_lt masks).SupportsBelow (outBase + W)
  | 0, _, _, _, _ => trivial
  | W + 1, outBase, _, hacc_lt, masks =>
      ⟨xorMaskedList_supportsBelow ⟨outBase, by omega⟩ (outBase + (W + 1))
          (show outBase < outBase + (W + 1) by omega) (masks 0) fullAccW
          (fun w hw ↦ wire_ne_of_lt (hacc_lt w hw))
          (fun w hw ↦ lt_trans (hacc_lt w hw) (by omega)),
        by
          rw [show outBase + (W + 1) = (outBase + 1) + W by omega]
          exact writeLinAndOuts_supportsBelow fullAccW W (outBase + 1) (by omega)
            (fun w hw ↦ lt_trans (hacc_lt w hw) (Nat.lt_succ_self outBase))
            (fun j ↦ masks j.succ)⟩
private theorem writeLinAndOuts_eval {M : ℕ} (fullAccW : List (Wire M)) :
    ∀ (W outBase : ℕ) (hout : outBase + W ≤ M) (hacc_lt : ∀ w ∈ fullAccW, w.val < outBase)
      (masks : Fin W → ℕ) (γ : BitAssignment M) (q : Wire M),
      (writeLinAndOuts fullAccW W outBase hout hacc_lt masks).eval γ q =
        if h : outBase ≤ q.val ∧ q.val < outBase + W then
          γ q + maskXorBits (masks ⟨q.val - outBase, by omega⟩) (fullAccW.map γ) else γ q
  | 0, _, _, _, _, _, _ => by simp [writeLinAndOuts, CliffProg.eval]
  | W + 1, outBase, _, hacc_lt, masks, γ, q => by
      dsimp only [writeLinAndOuts, CliffProg.eval]
      let dst0 : Wire M := ⟨outBase, by omega⟩
      have hne0 : ∀ w ∈ fullAccW, w ≠ dst0 := fun w hw ↦ wire_ne_of_lt (hacc_lt w hw)
      let γ₁ := Function.update γ dst0 (γ dst0 + maskXorBits (masks 0) (fullAccW.map γ))
      rw [xorMaskedList_eval dst0 (masks 0) fullAccW hne0 γ,
        writeLinAndOuts_eval fullAccW W (outBase + 1) (by omega)
          (fun w hw ↦ lt_trans (hacc_lt w hw) (Nat.lt_succ_self outBase))
          (fun j ↦ masks j.succ) γ₁ q,
        list_map_eq_of_forall (f := γ₁) (g := γ)
          (fun u hu ↦ Function.update_of_ne (hne0 u hu) _ _)]
      rcases eq_or_ne q dst0 with rfl | h0
      · dsimp only [γ₁, dst0]
        rw [dite_neg (show ¬ (outBase + 1 ≤ outBase ∧ outBase < (outBase + 1) + W) by omega),
          dite_pos (show outBase ≤ outBase ∧ outBase < outBase + (W + 1) by omega),
          Function.update_self,
          show (⟨outBase - outBase, by omega⟩ : Fin (W + 1)) = 0 from
            Fin.ext (Nat.sub_self outBase)]
      · have hq_ne : q.val ≠ outBase := fun hv ↦ h0 (Fin.ext hv)
        dsimp only [γ₁]
        by_cases h1 : outBase + 1 ≤ q.val ∧ q.val < (outBase + 1) + W
        · rw [dite_pos h1, dite_pos (by omega), Function.update_of_ne h0,
            show (⟨q.val - (outBase + 1), by omega⟩ : Fin W).succ =
              ⟨q.val - outBase, by omega⟩ from
              Fin.ext (show q.val - (outBase + 1) + 1 = q.val - outBase by omega)]
        · rw [dite_neg h1, dite_neg (by omega), Function.update_of_ne h0]
theorem fullAccW_lt {M : ℕ} (cur : ℕ) (inW : List (Wire M)) (S : ℕ) (hS : cur + 2 + S ≤ M) (hin_lt :
    ∀ w ∈ inW, w.val < cur) :
    ∀ w ∈ inW ++ ancList (cur + 2) S (by omega), w.val < cur + 2 + S :=
  fun w hw ↦ (List.mem_append.mp hw).elim (fun h ↦ lt_trans (hin_lt w h) (by omega))
    (fun h ↦ (ancList_mem_bounds (cur + 2) S (by omega) w h).2)
def ctxLinAndLut {M : ℕ} (W cur : ℕ) (inW : List (Wire M)) (steps : List (ℕ × ℕ)) (outMasks : Fin W
    → ℕ) (hcur : cur + 2 + steps.length + W ≤ M)
    (hin_lt : ∀ w ∈ inW, w.val < cur) : TempCtx M :=
  let scrL : Wire M := ⟨cur, by omega⟩
  let scrR : Wire M := ⟨cur + 1, by omega⟩
  (ctxLinAndSteps (cur + 2) steps (by omega) scrL scrR
      (wire_ne_of_lt (Nat.lt_succ_self cur))
      (by dsimp [scrL]; omega) (Nat.lt_succ_self (cur + 1)) inW
      (fun w hw ↦ lt_trans (hin_lt w hw) (by omega)) (fun w hw ↦ wire_ne_of_lt (hin_lt w hw))
      (fun w hw ↦ wire_ne_of_lt (lt_trans (hin_lt w hw) (Nat.lt_succ_self cur)))).append
    (ctxCliffAlloc (writeLinAndOuts (inW ++ ancList (cur + 2) steps.length (by omega)) W
      (cur + 2 + steps.length) (by omega)
      (fullAccW_lt cur inW steps.length (by omega) hin_lt) outMasks))
@[simp] theorem ctxLinAndLut_countTempAnd {M : ℕ} (W cur : ℕ) (inW : List (Wire M)) (steps : List (ℕ
    × ℕ)) (outMasks : Fin W → ℕ)
    (hcur : cur + 2 + steps.length + W ≤ M) (hin_lt : ∀ w ∈ inW, w.val < cur) :
    (ctxLinAndLut W cur inW steps outMasks hcur hin_lt).countTempAnd = steps.length := by
  simp [ctxLinAndLut, tempCtx_append_count, ctxCliffAlloc, TempCtx.countTempAnd]
theorem ctxLinAndLut_disj {M : ℕ} {mutW : Wire M → Prop} (W cur : ℕ) (inW : List (Wire M))
    (steps : List (ℕ × ℕ)) (outMasks : Fin W → ℕ) (hcur : cur + 2 + steps.length + W ≤ M) (hin_lt :
      ∀ w ∈ inW, w.val < cur) (hnIn : ∀ w ∈ inW, ¬ mutW w)
    (hnCur : ∀ w : Wire M,
      cur ≤ w.val → ¬ mutW w) : (ctxLinAndLut W cur inW steps outMasks hcur hin_lt).DisjointFrom
      mutW :=
  TempCtx.disjointFrom_append
    (ctxLinAndSteps_disj steps (cur + 2) (by omega) ⟨cur, by omega⟩ ⟨cur + 1, by omega⟩
      (wire_ne_of_lt (Nat.lt_succ_self cur))
      (by dsimp; omega) (Nat.lt_succ_self (cur + 1)) inW
      (fun w hw ↦ lt_trans (hin_lt w hw) (by omega)) (fun w hw ↦ wire_ne_of_lt (hin_lt w hw))
      (fun w hw ↦ wire_ne_of_lt (lt_trans (hin_lt w hw) (Nat.lt_succ_self cur)))
      (hnCur _ le_rfl) (hnCur _ (Nat.le_succ cur)) hnIn (fun w hw ↦ hnCur w (by omega)))
    (ctxCliffAlloc_disjoint (writeLinAndOuts_disjoint _
      (fun w hw ↦ (List.mem_append.mp hw).elim (hnIn w)
        (fun h ↦ hnCur w (le_trans (by omega) (ancList_mem_bounds (cur + 2) _ _ w h).1)))
      W (cur + 2 + steps.length) (by omega)
      (fullAccW_lt cur inW steps.length (by omega) hin_lt)
      outMasks (fun w hw ↦ hnCur w (by omega))))
theorem ScopedBlock.ctxLinAndLut_block {M : ℕ} (W cur : ℕ) (inW : List (Wire M))
    (steps : List (ℕ × ℕ)) (outMasks : Fin W → ℕ) (hcur : cur + 2 + steps.length + W ≤ M) (hin_lt :
      ∀ w ∈ inW, w.val < cur) (leaf body : TempPhaseProg M)
    (sBody : BitAssignment M → BitAssignment M) (hBody : ScopedBlock M (M - (cur + 2 + steps.length
      + W)) sBody leaf body) :
    ∃ setup : BitAssignment M → BitAssignment M,
      ScopedBlock M (M - cur) (fun β ↦ sBody (setup β)) leaf
    ((ctxLinAndLut W cur inW steps outMasks hcur hin_lt).plug body) ∧ ∀ γ : BitAssignment M,
      cleanRem M (M - cur) γ →
    cleanRem M (M - (cur + 2 + steps.length + W)) (setup γ) ∧ (∀ w : Wire M,
      w.val < cur → setup γ w = γ w) ∧
    ∀ j : Fin W, setup γ ⟨cur + 2 + steps.length + j.val,
      by omega⟩ = maskXorBits (outMasks j) (evalLinAndSteps steps (inW.map γ)) := by
  let fullAccW : List (Wire M) := inW ++ ancList (cur + 2) steps.length (by omega)
  let cOut := writeLinAndOuts fullAccW W (cur + 2 + steps.length) (by omega)
    (fullAccW_lt cur inW steps.length (by omega) hin_lt) outMasks
  have hOut := ScopedBlock.withCliffCur (M := M)
    (cur := cur + 2 + steps.length) (curIn := cur + 2 + steps.length + W)
    hcur (by omega) cOut
    (writeLinAndOuts_supportsBelow fullAccW W (cur + 2 + steps.length) (by omega)
      (fullAccW_lt cur inW steps.length (by omega) hin_lt) outMasks)
    hBody
  obtain ⟨sSteps, hSteps0, hSpecSteps⟩ := ScopedBlock.ctxLinAndSteps_block
    steps (cur + 2) (by omega) ⟨cur, by omega⟩ ⟨cur + 1, by omega⟩
    (wire_ne_of_lt (Nat.lt_succ_self cur)) (show cur < cur + 2 by omega)
    (Nat.lt_succ_self (cur + 1)) inW (fun w hw ↦ lt_trans (hin_lt w hw) (by omega))
    (fun w hw ↦ wire_ne_of_lt (hin_lt w hw))
    (fun w hw ↦ wire_ne_of_lt (lt_trans (hin_lt w hw) (Nat.lt_succ_self cur)))
    leaf _ (sBody ∘ cOut.eval) hOut
  have hSteps : ScopedBlock M (M - cur) (fun β ↦ sBody (cOut.eval (sSteps β))) leaf ((ctxLinAndLut W
    cur inW steps outMasks hcur hin_lt).plug body) := by
    dsimp only [ctxLinAndLut]
    rw [TempCtx.append_plug, ctxCliffAlloc_plug]
    exact ⟨validCleanRem_mono (by omega) hSteps0.valid,
      fun β hβ ↦ hSteps0.bits β (cleanRem_anti (by omega) hβ),
      fun β hβ ↦ hSteps0.sign β (cleanRem_anti (by omega) hβ)⟩
  refine ⟨fun γ ↦ cOut.eval (sSteps γ), hSteps, fun γ hcl ↦ ?_⟩
  have hL0 : γ ⟨cur, by omega⟩ = 0 := hcl _ (show M - (M - cur) ≤ cur by omega)
  have hR0 : γ ⟨cur + 1, by omega⟩ = 0 := hcl _ (show M - (M - cur) ≤ cur + 1 by omega)
  obtain ⟨hclS, hkeepS, hmapS⟩ := hSpecSteps γ (cleanRem_anti (by omega) hcl) hL0 hR0
  refine ⟨fun w hw ↦ ?_, fun w hw ↦ ?_, fun j ↦ ?_⟩
  · dsimp only [cOut]
    rw [writeLinAndOuts_eval, dite_neg (by omega)]
    exact hclS w (by omega)
  · dsimp only [cOut]
    rw [writeLinAndOuts_eval, dite_neg (by omega)]
    exact hkeepS w (by omega)
  · dsimp only [cOut]
    have hj_lt := j.isLt
    let b := cur + 2 + steps.length
    have _ : b + W ≤ M := hcur
    let outJ : Wire M := ⟨b + j.val, by omega⟩
    change (writeLinAndOuts fullAccW W b _ _ outMasks).eval (sSteps γ) outJ = _
    rw [writeLinAndOuts_eval, dite_pos (show b ≤ b + j.val ∧ b + j.val < b + W by omega),
      hclS outJ (show M - (M - b) ≤ b + j.val by omega), zero_add, hmapS,
      show (⟨outJ.val - b, by dsimp [outJ]; omega⟩ : Fin W) = j from
        Fin.ext (Nat.add_sub_cancel_left b _)]
def b2z (b : Bool) : ZMod 2 := if b then 1 else 0
theorem b2z_xor (a b : Bool) : b2z (xor a b) = b2z a + b2z b := by cases a <;> cases b <;> rfl
theorem b2z_and (a b : Bool) : b2z (a && b) = b2z a * b2z b := by cases a <;> cases b <;> rfl
def maskXorBool : ℕ → List Bool → Bool
  | _, [] => false
  | mask, b :: bs => xor (if mask % 2 == 1 then b else false) (maskXorBool (mask / 2) bs)
theorem b2z_maskXorBool (mask : ℕ) : ∀ bs : List Bool,
    b2z (maskXorBool mask bs) = maskXorBits mask (bs.map b2z)
  | [] => rfl
  | _ :: bs => by
      dsimp only [maskXorBool, maskXorBits, List.map]
      rw [b2z_xor, b2z_maskXorBool (mask / 2) bs]
      split_ifs <;> rfl
def evalLinAndBool : List (ℕ × ℕ) → List Bool → List Bool
  | [], acc => acc
  | (ma, mb) :: rest, acc =>
      match maskXorBool ma acc && maskXorBool mb acc with
      | true => evalLinAndBool rest (acc ++ [true])
      | false => evalLinAndBool rest (acc ++ [false])
theorem map_b2z_evalLinAndBool : ∀ (steps : List (ℕ × ℕ)) (bs : List Bool),
    (evalLinAndBool steps bs).map b2z = evalLinAndSteps steps (bs.map b2z)
  | [], _ => rfl
  | (ma, mb) :: rest, bs => by
      dsimp only [evalLinAndBool, evalLinAndSteps]
      rw [← b2z_maskXorBool, ← b2z_maskXorBool, ← b2z_and]
      cases maskXorBool ma bs && maskXorBool mb bs <;>
        simp only [map_b2z_evalLinAndBool rest, List.map_append, List.map]
def packBoolFn : {W : ℕ} → (Fin W → Bool) → ℕ
  | 0, _ => 0
  | _ + 1, f => (if f 0 then 1 else 0) + 2 * packBoolFn (fun j ↦ f j.succ)
theorem bitsVal_b2z_eq_packBoolFn : ∀ {W : ℕ} (f : Fin W → Bool),
    bitsVal (fun j : Fin W ↦ b2z (f j)) = packBoolFn f
  | 0, _ => by simp [bitsVal, packBoolFn]
  | _ + 1, f => by
      rw [bitsVal_succ_split, packBoolFn, ← bitsVal_b2z_eq_packBoolFn (fun j ↦ f j.succ)]
      cases f 0 <;> rfl
def inBool7 (x : ℕ) : List Bool :=
  [x.testBit 0, x.testBit 1, x.testBit 2, x.testBit 3, x.testBit 4, x.testBit 5, x.testBit 6]
theorem inBool7_map_b2z : ∀ x : Fin 65,
    let z : Fin 128 := ⟨x.val, lt_trans x.isLt (by decide)⟩
    (inBool7 x.val).map b2z = [basisBits 7 z 0, basisBits 7 z 1, basisBits 7 z 2,
      basisBits 7 z 3, basisBits 7 z 4, basisBits 7 z 5, basisBits 7 z 6] := by decide
def tetSteps29List : List (ℕ × ℕ) :=
  [(1,8),(1,4),(8,4),(1,2),(8,2),(4,2),(1,512),(1,2048),(1,4096),(8,4096),(1,65536),(16,36),
    (16,1),(36,66060),(17,164900),(170685,465156),(329744,262656),(19642,476810),
    (366885,498178),(457236,133412),(113811,465958),(396071,315779),(431647,274560),
    (63932,425984),(309034,422018),(391442,430116),(131001,346112),(502568,518146),
    (279570,327716)]
def tetOuts16 : Fin 16 → ℕ := ![1025, 1280, 34182, 660616, 2966684, 3657298865, 61424994,
  6488102470, 3242395964, 29468473207, 52045450405, 49048509576, 3256204006, 9502788,
  5482319104, 8388672]
set_option maxRecDepth 20000 in
theorem tetLut29_bool_val : ∀ w : Fin 65,
    let acc := evalLinAndBool tetSteps29List (inBool7 w.val)
    packBoolFn (fun j : Fin 16 ↦ maskXorBool (tetOuts16 j) acc) = tetNum w.val := by decide
theorem triNum_le_2080 : ∀ v : Fin 65, triNum v.val ≤ 2080 := by decide
def probeFwd {M : ℕ} (K : TempCtx M) (β : BitAssignment M) (w : Wire M) : ZMod 2 :=
  (K.plug (.z w)).evalSign β
theorem scopedBlock_probeFwd {M rem : ℕ} (K : TempCtx M) (h : ∀ q : Wire M, ∃ s :
    BitAssignment M → BitAssignment M, ScopedBlock M rem s (.z q) (K.plug (.z q))) : ∀ q : Wire M,
      ScopedBlock M rem (probeFwd K) (.z q) (K.plug (.z q)) :=
  fun q ↦ let ⟨_, hq⟩ := h q; ⟨hq.valid, hq.bits, fun _ _ ↦ rfl⟩
set_option allowUnsafeReducibility true in
attribute [local irreducible]
  ctxLinAndLut ctxAddMod2Pow bitsVal ctxAxisFold7 ctxSort3Clamp65 probeFwd
set_option allowUnsafeReducibility true in
def sel59Val (i : Fin 59) : ℕ :=
  if i.val = 0 then 3948 else if i.val < 4 then 3957 + (i.val - 1)
  else if i.val < 7 then 3954 + (i.val - 4)
  else if i.val < 25 then 6 * ((i.val - 7) / 6) + (5 - (i.val - 7) % 6)
  else if i.val < 43 then posCoreWires + 6 * ((i.val - 25) / 6) + (5 - (i.val - 25) % 6)
  else (posCoreWires + 18) + (i.val - 43)
theorem sel59Val_lt : ∀ i : Fin 59, sel59Val i < (posCoreWires + 18) + 16 := by decide
def sel59Idx (i : Fin 59) : Fin ((posCoreWires + 18) + 16) := ⟨sel59Val i, sel59Val_lt i⟩
theorem sel59Idx_injective : Function.Injective sel59Idx := by decide
def sel59Reg : QRegister 59 ((posCoreWires + 18) + 16) := ⟨⟨sel59Idx, sel59Idx_injective⟩⟩
theorem sel59Reg_s0 : sel59Reg ⟨0, by decide⟩ =
    Fin.castAdd 16 (Fin.castAdd 18 (wSlot0Core (QRegExt.ofFin posCoreWires))) := by decide
theorem sel59Reg_b0 : ∀ ax : Fin 3, sel59Reg ⟨1 + ax.val, by omega⟩ =
    Fin.castAdd 16 (Fin.castAdd 18 (rCosetB0 (QRegExt.ofFin posCoreWires) ax)) := by decide
theorem sel59Reg_b1 : ∀ ax : Fin 3, sel59Reg ⟨4 + ax.val, by omega⟩ =
    Fin.castAdd 16 (Fin.castAdd 18 (rCosetB1 (QRegExt.ofFin posCoreWires) ax)) := by decide
theorem sel59Reg_y0 : ∀ (ax : Fin 3) (j : Fin 6),
    sel59Reg ⟨7 + 6 * ax.val + j.val, by omega⟩ =
      Fin.castAdd 16 (Fin.castAdd 18 (axisBitRev6 (rElecSlot (QRegExt.ofFin posCoreWires) 0)
        ax j)) := by decide
theorem sel59Reg_yp : ∀ (ax : Fin 3) (j : Fin 6),
    sel59Reg ⟨25 + 6 * ax.val + j.val, by omega⟩ =
      Fin.castAdd 16
        (Fin.natAdd posCoreWires (axisBitRev6 (QRegExt.ofFin 18) ax j)) := by decide
set_option allowUnsafeReducibility true in
attribute [local irreducible] PosSlots24PartnerMux288.permSignUnitary
set_option allowUnsafeReducibility true in
theorem matrix_ext_ket {k : ℕ} {A B : Matrix (Fin (2 ^ k)) (Fin (2 ^ k)) ℂ} (h : ∀ β : BitAssignment
    k, A.mulVec (ket β) = B.mulVec (ket β)) : A = B := by
  ext i g
  have hket : ket (basisBits k g) = (Pi.single g (1 : ℂ) : Fin (2 ^ k) → ℂ) :=
    funext fun _ ↦ by simp [ket, basisState]
  have h1 := congrFun (h (basisBits k g)) i
  rwa [hket, Matrix.mulVec_single_one, Matrix.mulVec_single_one] at h1
theorem sel59Reg_lt_of_lt43 :
    ∀ i : Fin 59, i.val < 43 → (sel59Reg i).val < posCoreWires + 18 := by decide
end PosSlots24OrbitToggleFast288
end
end ModPosSlots24OrbitToggleFast288

end QuantumComputation.Specs.StoppingPowerSolution
