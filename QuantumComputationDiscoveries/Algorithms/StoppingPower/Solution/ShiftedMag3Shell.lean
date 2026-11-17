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

public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.BoothProd57Hoist

set_option Elab.async false

@[expose] public section
set_option allowUnsafeReducibility true

namespace QuantumComputation.Specs.StoppingPowerSolution

section ModShiftedMagS1
@[expose] public section
namespace ShiftedMagS1
section ConfigShiftedMagS1
set_option exponentiation.threshold 256
set_option backward.isDefEq.respectTransparency true
local instance (priority := 1000000) instNeZeroTwoPowShiftedMagS1 (k : Nat) : NeZero (2 ^ k) :=
  ⟨Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos k)⟩
open Operator Matrix QProg Circuit _root_.DynamicCircuit DynCircuitExt Real LocalClassicalPerm
open PosSlots24PartnerMux288 (permSignUnitary invPermMat permMatrix_mem_unitaryGroup)
open ModWrapCoarse8PureMomentum (coarseRadCeilVal7)
open Slot5MatrixAndScaleCert (signBit3)
open MomSlots35Slot3ProjNuclear (shellMu3 shellMu3_lt_seven shellMagCoord3 shellMagCoord3_lt
  validShellNu3 coarseGood3Computable)
open MomSlot0CircuitHalf (padZeroBits phaseDiagUnitary)
open scoped Matrix BigOperators Matrix.Norms.L2Operator
theorem itePos {c : Prop} [Decidable c] {α : Sort _} (hc : c) {t e : α} :
    ite c t e = t := ite_eq_left hc
theorem iteNeg {c : Prop} [Decidable c] {α : Sort _} (hnc : ¬ c) {t e : α} :
    ite c t e = e := ite_eq_right hnc
theorem ditePos {c : Prop} [Decidable c] {α : Sort _} (hc : c)
    {t : c → α} {e : ¬ c → α} : dite c t e = t hc := dite_eq_left hc
theorem diteNeg {c : Prop} [Decidable c] {α : Sort _} (hnc : ¬ c)
    {t : c → α} {e : ¬ c → α} : dite c t e = e hnc := dite_eq_right hnc
theorem disjConcatLeft {k m p n : ℕ} {r : QRegister k n} {s : QRegister m n}
    {w : QRegister p n} {hrs : r.DisjointWires s} (hrw : r.DisjointWires w)
    (hsw : s.DisjointWires w) : (r.concat s hrs).DisjointWires w := by
  rw [QRegister.disjoint_iff]
  intro i j
  cases h : finSumFinEquiv.symm i with
  | inl i₁ => simpa [QRegister.concat, h] using hrw.ne i₁ j
  | inr i₂ => simpa [QRegister.concat, h] using hsw.ne i₂ j
theorem ltTrans {a b c : ℕ} (h1 : a < b) (h2 : b < c) : a < c := Nat.lt_trans h1 h2
theorem testBit_div_two_powAux (x : ℕ) (k i : ℕ) :
    (x / 2 ^ k).testBit i = x.testBit (k + i) := by
  rw [Nat.testBit_div_two_pow, add_comm]
theorem testBit_two_pow_mulAux (k x i : ℕ) :
    (2 ^ k * x).testBit i = (decide (k ≤ i) && x.testBit (i - k)) := by
  rw [Nat.testBit_two_pow_mul]
theorem testBit_mod_two_powAux (m x i : ℕ) :
    (x % 2 ^ m).testBit i = (decide (i < m) && x.testBit i) :=
  Nat.testBit_mod_two_pow x m i
def shiftedMag3 (u22 : Fin 4194304) (w : Fin 3) : ℕ :=
  2 ^ (6 - shellMu3 u22) * shellMagCoord3 u22 w
theorem shiftedMag3_lt_128 (u22 : Fin 4194304) (w : Fin 3) : shiftedMag3 u22 w < 128 := by
  have hμ := shellMu3_lt_seven u22
  exact (Nat.mul_lt_mul_of_pos_left (shellMagCoord3_lt u22 w)
    (Nat.two_pow_pos (6 - shellMu3 u22))).trans_eq ((pow_add 2 _ _).symm.trans
    (congrArg (2 ^ ·) (by omega : 6 - shellMu3 u22 + (shellMu3 u22 + 1) = 7)))
theorem shiftedMag3_eq_zero_iff (u22 : Fin 4194304) (w : Fin 3) :
    shiftedMag3 u22 w = 0 ↔ shellMagCoord3 u22 w = 0 := by
  simp [shiftedMag3]
theorem shiftedMag3_testBit (u22 : Fin 4194304) (w : Fin 3) (b : Fin 7) :
    (shiftedMag3 u22 w).testBit b.val = if 6 - b.val ≤ shellMu3 u22 then u22.val.testBit
    (w.val * (shellMu3 u22 + 1) + (b.val - (6 - shellMu3 u22))) else false := by
  have hμ := shellMu3_lt_seven u22
  have hb := b.isLt
  unfold shiftedMag3 shellMagCoord3
  rw [testBit_two_pow_mulAux, testBit_mod_two_powAux, testBit_div_two_powAux]
  by_cases hle : 6 - b.val ≤ shellMu3 u22
  · simp [hle, show 6 - shellMu3 u22 ≤ b.val by omega,
      show b.val - (6 - shellMu3 u22) < shellMu3 u22 + 1 by omega]
  · simp [hle, show ¬(6 - shellMu3 u22 ≤ b.val) by omega]
theorem shiftedMag3_testBit_six (u22 : Fin 4194304) (w : Fin 3) :
    (shiftedMag3 u22 w).testBit 6 = decide (2 ^ shellMu3 u22 ≤ shellMagCoord3 u22 w) := by
  have hm := shellMagCoord3_lt u22 w
  have hμ := shellMu3_lt_seven u22
  unfold shiftedMag3
  rw [testBit_two_pow_mulAux, decide_eq_true (by omega : 6 - shellMu3 u22 ≤ 6), Bool.true_and,
    show 6 - (6 - shellMu3 u22) = shellMu3 u22 by omega,
    ← Nat.add_zero (shellMu3 u22), ← testBit_div_two_powAux, Nat.testBit_zero]
  rw [pow_succ] at hm
  have hdiv : shellMagCoord3 u22 w / 2 ^ shellMu3 u22 < 2 := Nat.div_lt_of_lt_mul hm
  by_cases hge : 2 ^ shellMu3 u22 ≤ shellMagCoord3 u22 w
  · have hge1 : 1 ≤ shellMagCoord3 u22 w / 2 ^ shellMu3 u22 :=
      (Nat.le_div_iff_mul_le (Nat.two_pow_pos _)).mpr (by simpa using hge)
    simp [hge, show shellMagCoord3 u22 w / 2 ^ shellMu3 u22 = 1 by omega]
  · simp [hge, Nat.div_eq_of_lt (Nat.lt_of_not_ge hge)]
def top7Mu (t : ℕ) : ℕ := if t < 2 then 0 else if t < 4 then 1 else if t < 8 then 2 else
    if t < 16 then 3 else if t < 32 then 4 else if t < 64 then 5 else 6
theorem top7Mu_eq_shellMu3 (u22 : Fin 4194304) :
    top7Mu (u22.val / 32768) = shellMu3 u22 := by
  have hlt := u22.isLt
  unfold top7Mu shellMu3
  split_ifs <;> omega
theorem validShellNu3_eq_shifted (u22 : Fin 4194304) (s3 : Fin 8) :
    validShellNu3 u22 s3 =
      (decide (0 < u22.val / 32768) &&
        ((shiftedMag3 u22 0).testBit 6 || (shiftedMag3 u22 1).testBit 6 ||
          (shiftedMag3 u22 2).testBit 6) &&
        !(decide (shiftedMag3 u22 0 = 0) && decide (signBit3 s3 0 = 1)) &&
        !(decide (shiftedMag3 u22 1 = 0) && decide (signBit3 s3 1 = 1)) &&
        !(decide (shiftedMag3 u22 2 = 0) && decide (signBit3 s3 2 = 1))) := by
  unfold validShellNu3
  rw [shiftedMag3_testBit_six u22 0, shiftedMag3_testBit_six u22 1,
    shiftedMag3_testBit_six u22 2,
    show decide (32768 ≤ u22.val) = decide (0 < u22.val / 32768) from
      decide_eq_decide.mpr (by omega),
    show decide (2 ^ shellMu3 u22 ≤
        max (shellMagCoord3 u22 0) (max (shellMagCoord3 u22 1) (shellMagCoord3 u22 2))) =
      (decide (2 ^ shellMu3 u22 ≤ shellMagCoord3 u22 0) ||
        decide (2 ^ shellMu3 u22 ≤ shellMagCoord3 u22 1) ||
        decide (2 ^ shellMu3 u22 ≤ shellMagCoord3 u22 2)) from
      Bool.eq_iff_iff.mpr (by simp [Bool.or_eq_true, decide_eq_true_eq, le_max_iff, or_assoc]),
    show decide (∀ w : Fin 3, ¬(shellMagCoord3 u22 w = 0 ∧ signBit3 s3 w = 1)) =
      (!(decide (shiftedMag3 u22 0 = 0) && decide (signBit3 s3 0 = 1)) &&
       !(decide (shiftedMag3 u22 1 = 0) && decide (signBit3 s3 1 = 1)) &&
       !(decide (shiftedMag3 u22 2 = 0) && decide (signBit3 s3 2 = 1))) from
      Bool.eq_iff_iff.mpr (by
        simp only [Fin.forall_fin_succ, Fin.isValue, IsEmpty.forall_iff, Bool.and_eq_true,
          Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_true_eq, decide_eq_false_iff_not,
          shiftedMag3_eq_zero_iff]
        tauto)]
  simp only [Bool.and_assoc]
def sTilde3 (u22 : Fin 4194304) : ℕ :=
  (shiftedMag3 u22 0) ^ 2 + (shiftedMag3 u22 1) ^ 2 + (shiftedMag3 u22 2) ^ 2
def thr16 (c : Fin 256) : ℕ :=
  if c.val = 0 then 65535 else min 65535 (1044190 / c.val + 1)
theorem sTilde3_eq_scale (u22 : Fin 4194304) : sTilde3 u22 = 4 ^ (6 - shellMu3 u22) *
    ((shellMagCoord3 u22 0) ^ 2 + (shellMagCoord3 u22 1) ^ 2 + (shellMagCoord3 u22 2) ^ 2) := by
  have h4 : (2 ^ (6 - shellMu3 u22)) ^ 2 = 4 ^ (6 - shellMu3 u22) :=
    (pow_mul 2 _ 2).symm.trans ((congrArg (2 ^ ·) (mul_comm _ 2)).trans (pow_mul 2 2 _))
  unfold sTilde3 shiftedMag3
  rw [← h4]
  ring
theorem sTilde3_le_48387 (u22 : Fin 4194304) : sTilde3 u22 ≤ 48387 := by
  unfold sTilde3
  nlinarith [shiftedMag3_lt_128 u22 0, shiftedMag3_lt_128 u22 1, shiftedMag3_lt_128 u22 2]
theorem coarseRadCeilVal7_eq_div {μ : ℕ} (hμ : μ < 7) :
    coarseRadCeilVal7 μ = 1044190 / 4 ^ (6 - μ) := by decide +revert
theorem sTilde_lt_Thr16_iff {μ s : ℕ} (hμ : μ < 7) (hs : 4 ^ (6 - μ) * s ≤ 48387)
    (c : Fin 256) : 4 ^ (6 - μ) * s < thr16 c ↔ c.val * s < coarseRadCeilVal7 μ + 1 := by
  rw [coarseRadCeilVal7_eq_div hμ]
  set K := 4 ^ (6 - μ)
  have hK : 0 < K := by positivity
  unfold thr16
  by_cases hc0 : c.val = 0
  · simp [hc0, show K * s < 65535 by omega]
  · rw [iteNeg hc0]
    have hc_pos : 0 < c.val := Nat.pos_of_ne_zero hc0
    by_cases hcap : 65535 ≤ 1044190 / c.val + 1
    · rw [Nat.min_eq_left hcap]
      have hmul_c : 65534 * c.val ≤ 1044190 := (Nat.le_div_iff_mul_le hc_pos).mp (by omega)
      exact ⟨fun _ ↦ Nat.lt_succ_of_le ((Nat.le_div_iff_mul_le hK).mpr (by nlinarith)),
        fun _ ↦ by omega⟩
    · rw [Nat.min_eq_right (by omega)]
      rw [Nat.lt_succ_iff, Nat.le_div_iff_mul_le hc_pos,
        show (K * s) * c.val = (c.val * s) * K by ring, ← Nat.le_div_iff_mul_le hK,
        ← Nat.lt_succ_iff]
theorem coarseGood3Computable_eq_sTilde (u22 : Fin 4194304) (s3 : Fin 8) (c8 : Fin 256) :
    coarseGood3Computable u22 s3 c8 =
      (validShellNu3 u22 s3 && decide (sTilde3 u22 < thr16 c8)) := by
  change (validShellNu3 u22 s3 && decide (c8.val * (shellMagCoord3 u22 0 ^ 2 +
    shellMagCoord3 u22 1 ^ 2 + shellMagCoord3 u22 2 ^ 2) <
      coarseRadCeilVal7 (shellMu3 u22) + 1)) = _
  have hs := sTilde3_le_48387 u22
  rw [sTilde3_eq_scale] at hs ⊢
  exact congrArg (validShellNu3 u22 s3 && ·)
    (decide_eq_decide.mpr (sTilde_lt_Thr16_iff (shellMu3_lt_seven u22) hs c8).symm)
theorem bitsVal_eq_of_testBit {W : ℕ} (f : Fin W → ZMod 2) (v : ℕ) (hv : v < 2 ^ W)
    (h : ∀ j : Fin W, f j = if v.testBit j.val then 1 else 0) : bitsVal f = v :=
  Slot3MicroEngineAux.bitsVal_eq_of_testBit f v hv h
def xVec {M : ℕ} : (W : ℕ) → (Fin W → Wire M) → CliffProg M
  | 0, _ => .nil
  | W + 1, dst => .seq (.x (dst 0)) (xVec W (fun j ↦ dst j.succ))
theorem xVec_supportsBelow {M bound : ℕ} : ∀ (W : ℕ) (dst : Fin W → Wire M),
    (∀ j, (dst j).val < bound) → (xVec W dst).SupportsBelow bound
  | 0, _, _ => trivial
  | W + 1, _, h => ⟨h 0, xVec_supportsBelow W _ (fun j ↦ h j.succ)⟩
theorem xVec_eval {M : ℕ} :
    ∀ (W : ℕ) (dst : Fin W → Wire M) (_ : Function.Injective dst) (β : BitAssignment M)
      (w : Wire M), (xVec W dst).eval β w = if ∃ j, w = dst j then β w + 1 else β w
  | 0, _, _, _, _ => by simp [xVec, CliffProg.eval]
  | W + 1, dst, hinj, β, w => by
      dsimp only [xVec, CliffProg.eval]
      rw [xVec_eval W (fun j ↦ dst j.succ) (hinj.comp (Fin.succ_injective W)) _ w]
      by_cases h0 : w = dst 0
      · subst h0
        simp [show ¬∃ j : Fin W, dst 0 = dst j.succ from
          fun ⟨j, hj⟩ ↦ Fin.succ_ne_zero j (hinj hj.symm),
          show ∃ i : Fin (W + 1), dst 0 = dst i from ⟨0, rfl⟩, Function.update_self]
      · have heq : (∃ j : Fin W, w = dst j.succ) ↔ (∃ i : Fin (W + 1), w = dst i) :=
          ⟨fun ⟨j, hj⟩ ↦ ⟨j.succ, hj⟩,
            fun ⟨i, hi⟩ ↦ Fin.cases (fun h ↦ False.elim (h0 h)) (fun j h ↦ ⟨j, h⟩) i hi⟩
        simp [heq, Function.update_of_ne h0]
theorem TempCtx.fwdBits_mut {M : ℕ} {mutW : Wire M → Prop} {K : TempCtx M}
    (hDisj : K.DisjointFrom mutW) : ∀ (β : BitAssignment M) {w : Wire M}, mutW w →
      K.fwdBits β w = β w := Slot3MicroEngineAux.TempCtx.fwdBits_mut hDisj
theorem TempCtx.supportsBelowCtx_mono {M b₁ b₂ : ℕ} (hle : b₁ ≤ b₂) {K : TempCtx M} :
    K.SupportsBelowCtx b₁ → K.SupportsBelowCtx b₂ :=
  Slot3MicroEngineAux.TempCtx.supportsBelowCtx_mono hle
theorem TempCtx.append_countTempAnd {M : ℕ} (F G : TempCtx M) :
    (F.append G).countTempAnd = F.countTempAnd + G.countTempAnd :=
  Slot3MicroEngineAux.TempCtx.append_countTempAnd F G
theorem TempCtx.append_fwdBits {M : ℕ} (F G : TempCtx M) (β : BitAssignment M) :
    (F.append G).fwdBits β = G.fwdBits (F.fwdBits β) :=
  Slot3MicroEngineAux.TempCtx.append_fwdBits F G β
theorem TempCtx.scopedBlock_fwdBits {M rem : ℕ} (K : TempCtx M)
    (hEx : ∀ q : Wire M, ∃ sQ, ScopedBlock M rem sQ (.z q) (K.plug (.z q))) (q : Wire M) :
    ScopedBlock M rem K.fwdBits (.z q) (K.plug (.z q)) :=
  Slot3MicroEngineAux.TempCtx.scopedBlock_fwdBits K hEx q
theorem TempCtx.fwdBits_eq_of_block {M rem : ℕ} (K : TempCtx M) (u : Wire M)
    {sU : BitAssignment M → BitAssignment M}
    (hBlk : ScopedBlock M rem sU (.z u) (K.plug (.z u))) (β : BitAssignment M)
    (hβ : cleanRem M rem β) : K.fwdBits β u = sU β u :=
  Slot3MicroEngineAux.TempCtx.fwdBits_eq_of_block K u hBlk β hβ
def TempCtxLiftEx {M : ℕ} (cur next : ℕ) (K : TempCtx M) : Prop :=
  ∀ {leaf body : TempPhaseProg M} {sBody : BitAssignment M → BitAssignment M},
    ScopedBlock M (M - next) sBody leaf body →
    ∃ sOut, ScopedBlock M (M - cur) sOut leaf (K.plug body)
theorem TempCtxLiftEx.probe {M cur next : ℕ} {K : TempCtx M} (hK : TempCtxLiftEx cur next K)
    (q : Wire M) : ScopedBlock M (M - cur) K.fwdBits (.z q) (K.plug (.z q)) :=
  Slot3MicroEngineAux.TempCtxLiftEx.probe hK q
theorem TempCtxLiftEx.mono {M cur₀ cur₁ next₀ next₁ : ℕ} {K : TempCtx M}
    (hK : TempCtxLiftEx cur₁ next₀ K) (hc : cur₀ ≤ cur₁) (hn : next₀ ≤ next₁) (hM : next₁ ≤ M) :
    TempCtxLiftEx cur₀ next₁ K := Slot3MicroEngineAux.TempCtxLiftEx.mono hK hc hn hM
theorem TempCtxLiftEx.append {M cur mid next : ℕ} {F G : TempCtx M}
    (hF : TempCtxLiftEx cur mid F) (hG : TempCtxLiftEx mid next G) :
    TempCtxLiftEx cur next (F.append G) := Slot3MicroEngineAux.TempCtxLiftEx.append hF hG
theorem TempCtxLiftEx.cliff {M : ℕ} (cur : ℕ) (hcur : cur ≤ M) (c : CliffProg M)
    (hc : c.SupportsBelow cur) : TempCtxLiftEx cur cur (ctxCliffAlloc c) :=
  Slot3MicroEngineAux.TempCtxLiftEx.cliff cur hcur c hc
theorem TempCtxLiftEx.tempBit {M : ℕ} (cur : ℕ) (hcur : cur + 1 ≤ M) (c₁ c₂ : Wire M)
    (h12 : c₁ ≠ c₂) (hc1 : c₁.val < cur) (hc2 : c₂.val < cur) : TempCtxLiftEx cur (cur + 1)
    (ctxTempBit c₁ c₂ ⟨cur, hcur⟩ h12 (wire_ne_of_lt hc1) (wire_ne_of_lt hc2)) :=
  Slot3MicroEngineAux.TempCtxLiftEx.tempBit cur hcur c₁ c₂ h12 hc1 hc2
def ctxLtStep {M : ℕ} (cur : ℕ) (hcur : cur + 1 ≤ M) (a b prev : Wire M) (hab : a ≠ b)
    (ha : a.val < cur) (hb : b.val < cur) (hp : prev.val < cur) (hbp : b ≠ prev) : TempCtx M :=
  let out : Wire M := ⟨cur, by omega⟩
  (ctxCliffAlloc (.seq (.cnot b a hab.symm) (.cnot prev b hbp.symm))).append
    ((ctxTempBit a b out hab (wire_ne_of_lt ha) (wire_ne_of_lt hb)).append
      (ctxCliffAlloc (.seq (.cnot prev b hbp.symm)
        (.seq (.cnot b a hab.symm) (.cnot prev out (wire_ne_of_lt hp))))))
def ctxLtCompLoop {M : ℕ} : (W cur : ℕ) → (hcur : cur + W + 1 ≤ M) →
    (a b : Fin W → Wire M) → (hab : ∀ j, a j ≠ b j) →
    (ha : ∀ j, (a j).val < cur) → (hb : ∀ j, (b j).val < cur) → TempCtx M
  | 0, _, _, _, _, _, _, _ => .hole
  | W + 1, cur, _, a, b, hab, ha, hb =>
      (ctxLtStep (cur + 1) (by omega) (a 0) (b 0) ⟨cur, by omega⟩ (hab 0)
        (ltTrans (ha 0) (by omega)) (ltTrans (hb 0) (by omega))
        (Nat.lt_succ_self cur) (wire_ne_of_lt (hb 0))).append
        (ctxLtCompLoop W (cur + 1) (by omega) (fun j ↦ a j.succ) (fun j ↦ b j.succ)
          (fun j ↦ hab j.succ) (fun j ↦ ltTrans (ha j.succ) (by omega))
          (fun j ↦ ltTrans (hb j.succ) (by omega)))
theorem slim_ctxLtCompLoop_eq {M : ℕ} :
    ∀ (W cur : ℕ) (hcur : cur + W + 1 ≤ M) (a b : Fin W → Wire M) (hab : ∀ j, a j ≠ b j)
      (ha : ∀ j, (a j).val < cur) (hb : ∀ j, (b j).val < cur),
      ctxLtCompLoop W cur hcur a b hab ha hb =
        Slot3MicroEngineAux.ctxLtCompLoop W cur hcur a b hab ha hb
  | 0, _, _, _, _, _, _, _ => rfl
  | W + 1, cur, _, _, _, _, _, _ => by
      dsimp only [ctxLtCompLoop, Slot3MicroEngineAux.ctxLtCompLoop]
      exact congr (congrArg TempCtx.append rfl)
        (slim_ctxLtCompLoop_eq W (cur + 1) _ _ _ _ _ _)
theorem TempCtx.fwdBits_outside {M B : ℕ} {K : TempCtx M} (hSupp : K.SupportsBelowCtx B) :
    ∀ (β : BitAssignment M) (w : Wire M), B ≤ w.val → K.fwdBits β w = β w :=
  Slot3MicroEngineAux.TempCtx.fwdBits_outside hSupp
theorem TempCtx.cleanRem_of_supports {M : ℕ} (cur next : ℕ) {K : TempCtx M}
    (hle : cur ≤ next) (hSupp : K.SupportsBelowCtx next)
    {β : BitAssignment M} (hβ : cleanRem M (M - cur) β) : cleanRem M (M - next) (K.fwdBits β) :=
  Slot3MicroEngineAux.TempCtx.cleanRem_of_supports cur next hle hSupp hβ
theorem TempCtxLiftEx.ltCompLoop {M : ℕ} (W cur : ℕ) (hcur : cur + W + 1 ≤ M)
    (a b : Fin W → Wire M) (hab : ∀ j, a j ≠ b j)
    (ha : ∀ j, (a j).val < cur) (hb : ∀ j, (b j).val < cur) :
    TempCtxLiftEx cur (cur + W + 1) (ctxLtCompLoop W cur hcur a b hab ha hb) := by
  rw [slim_ctxLtCompLoop_eq]
  exact Slot3MicroEngineAux.TempCtxLiftEx.ltCompLoop W cur hcur a b hab ha hb
inductive MicroOp where
  | notW (a : ℕ) | cnotW (a b : ℕ) | andAlloc (a b : ℕ) | zeroAlloc
def microAllocs : List MicroOp → ℕ
  | [] => 0 | .notW _ :: r => microAllocs r | .cnotW _ _ :: r => microAllocs r
  | .andAlloc _ _ :: r => 1 + microAllocs r | .zeroAlloc :: r => 1 + microAllocs r
def microAnds : List MicroOp → ℕ
  | [] => 0 | .notW _ :: r => microAnds r | .cnotW _ _ :: r => microAnds r
  | .andAlloc _ _ :: r => 1 + microAnds r | .zeroAlloc :: r => microAnds r
def microValid : ℕ → List MicroOp → Bool
  | _, [] => true
  | top, .notW a :: r => decide (a < top) && microValid top r
  | top, .cnotW a b :: r => decide (a < top) && decide (b < top) && decide (a ≠ b) &&
      microValid top r
  | top, .andAlloc a b :: r => decide (a < top) && decide (b < top) && decide (a ≠ b) &&
      microValid (top + 1) r
  | top, .zeroAlloc :: r => microValid (top + 1) r
theorem microValid_notW {top a : ℕ} {rest : List MicroOp}
    (hv : microValid top (.notW a :: rest) = true) : a < top ∧ microValid top rest = true := by
  simpa [microValid, Bool.and_eq_true, decide_eq_true_eq] using hv
theorem microValid_cnotW {top a b : ℕ} {rest : List MicroOp}
    (hv : microValid top (.cnotW a b :: rest) = true) :
    a < top ∧ b < top ∧ a ≠ b ∧ microValid top rest = true := by
  simpa [microValid, Bool.and_eq_true, decide_eq_true_eq, and_assoc] using hv
theorem microValid_andAlloc {top a b : ℕ} {rest : List MicroOp}
    (hv : microValid top (.andAlloc a b :: rest) = true) :
    a < top ∧ b < top ∧ a ≠ b ∧ microValid (top + 1) rest = true := by
  simpa [microValid, Bool.and_eq_true, decide_eq_true_eq, and_assoc] using hv
def boolToZMod2 (b : Bool) : ZMod 2 := if b then 1 else 0
/-- Map local `MicroOp` to `Slot3MicroEngineAux.MicroOp`. -/
def slim_toS3Op : MicroOp → Slot3MicroEngineAux.MicroOp
  | .notW a => .notW a | .cnotW a b => .cnotW a b
  | .andAlloc a b => .andAlloc a b | .zeroAlloc => .zeroAlloc
theorem slim_microAllocs_eq : ∀ ops : List MicroOp,
    microAllocs ops = Slot3MicroEngineAux.microAllocs (ops.map slim_toS3Op)
  | [] => rfl | .notW _ :: r => slim_microAllocs_eq r
  | .cnotW _ _ :: r => slim_microAllocs_eq r
  | .andAlloc _ _ :: r => congrArg (1 + ·) (slim_microAllocs_eq r)
  | .zeroAlloc :: r => congrArg (1 + ·) (slim_microAllocs_eq r)
theorem slim_microAnds_eq : ∀ ops : List MicroOp,
    microAnds ops = Slot3MicroEngineAux.microAnds (ops.map slim_toS3Op)
  | [] => rfl | .notW _ :: r => slim_microAnds_eq r
  | .cnotW _ _ :: r => slim_microAnds_eq r | .zeroAlloc :: r => slim_microAnds_eq r
  | .andAlloc _ _ :: r => congrArg (1 + ·) (slim_microAnds_eq r)
theorem slim_microValid_eq : ∀ (ops : List MicroOp) (top : ℕ),
    microValid top ops = Slot3MicroEngineAux.microValid top (ops.map slim_toS3Op)
  | [], _ => rfl | .zeroAlloc :: r, top => slim_microValid_eq r (top + 1)
  | .notW _ :: r, top => congrArg _ (slim_microValid_eq r top)
  | .cnotW _ _ :: r, top => congrArg _ (slim_microValid_eq r top)
  | .andAlloc _ _ :: r, top => congrArg _ (slim_microValid_eq r (top + 1))
theorem zmod2_eq_boolToZMod2 (z : ZMod 2) : z = boolToZMod2 (decide (z = 1)) :=
  Slot3MicroEngineAux.zmod2_eq_boolToZMod2 z
def getBoolAt : List Bool → ℕ → Bool
  | [], _ => false | b :: _, 0 => b | _ :: bs, k + 1 => getBoolAt bs k
theorem slim_getBoolAt_eq : ∀ (st : List Bool) (k : ℕ),
    getBoolAt st k = Slot3MicroEngineAux.getBoolAt st k
  | [], _ => rfl | _ :: _, 0 => rfl | _ :: bs, k + 1 => slim_getBoolAt_eq bs k
def setBoolAt : List Bool → ℕ → Bool → List Bool
  | [], _, _ => [] | _ :: bs, 0, v => v :: bs | b :: bs, k + 1, v => b :: setBoolAt bs k v
theorem slim_setBoolAt_eq : ∀ (st : List Bool) (k : ℕ) (v : Bool),
    setBoolAt st k v = Slot3MicroEngineAux.setBoolAt st k v
  | [], _, _ => rfl | _ :: _, 0, _ => rfl
  | b :: bs, k + 1, v => congrArg (b :: ·) (slim_setBoolAt_eq bs k v)
def evalMicroList : ℕ → List MicroOp → List Bool → List Bool
  | _, [], st => st
  | top, .notW a :: r, st => evalMicroList top r (setBoolAt st a (!getBoolAt st a))
  | top, .cnotW a b :: r, st =>
      evalMicroList top r (setBoolAt st b (xor (getBoolAt st b) (getBoolAt st a)))
  | top, .andAlloc a b :: r, st =>
      evalMicroList (top + 1) r (setBoolAt st top (getBoolAt st a && getBoolAt st b))
  | top, .zeroAlloc :: r, st => evalMicroList (top + 1) r (setBoolAt st top false)
theorem slim_evalMicroList_eq : ∀ (ops : List MicroOp) (top : ℕ) (st : List Bool),
    evalMicroList top ops st = Slot3MicroEngineAux.evalMicroList top (ops.map slim_toS3Op) st
  | [], _, _ => rfl
  | .notW _ :: r, top, _ => by
      simpa [evalMicroList, slim_toS3Op, Slot3MicroEngineAux.evalMicroList,
        slim_getBoolAt_eq, slim_setBoolAt_eq] using slim_evalMicroList_eq r top _
  | .cnotW _ _ :: r, top, _ => by
      simpa [evalMicroList, slim_toS3Op, Slot3MicroEngineAux.evalMicroList,
        slim_getBoolAt_eq, slim_setBoolAt_eq] using slim_evalMicroList_eq r top _
  | .andAlloc _ _ :: r, top, _ => by
      simpa [evalMicroList, slim_toS3Op, Slot3MicroEngineAux.evalMicroList,
        slim_getBoolAt_eq, slim_setBoolAt_eq] using slim_evalMicroList_eq r (top + 1) _
  | .zeroAlloc :: r, top, _ => by
      simpa [evalMicroList, slim_toS3Op, Slot3MicroEngineAux.evalMicroList,
        slim_setBoolAt_eq] using slim_evalMicroList_eq r (top + 1) _
def mkBoolList (nIn mask off : ℕ) : ℕ → List Bool
  | 0 => []
  | rem + 1 => (decide (off < nIn) && mask.testBit off) :: mkBoolList nIn mask (off + 1) rem
theorem slim_mkBoolList_eq (nIn mask : ℕ) : ∀ (off rem : ℕ),
    mkBoolList nIn mask off rem = Slot3MicroEngineAux.mkBoolList nIn mask off rem
  | _, 0 => rfl
  | off, rem + 1 => congrArg (_ :: ·) (slim_mkBoolList_eq nIn mask (off + 1) rem)
def initBoolList (nIn len mask : ℕ) : List Bool := mkBoolList nIn mask 0 len
structure BTree where val : ℕ → Bool
def BTree.get (t : BTree) (s : ℕ) : Bool := t.val s
def runMicroTree (nIn len mask : ℕ) (ops : List MicroOp) : BTree :=
  ⟨fun s ↦ getBoolAt (evalMicroList nIn ops (initBoolList nIn len mask)) s⟩
theorem runMicroTree_get_eq (nIn len mask : ℕ) (ops : List MicroOp)
    (_hv : microValid nIn ops = true) (_ha : nIn + microAllocs ops = len) (s : ℕ)
    (_hs : s < len) : (runMicroTree nIn len mask ops).get s =
      getBoolAt (evalMicroList nIn ops (initBoolList nIn len mask)) s := rfl
def getNatAt : List ℕ → ℕ → ℕ
  | [], _ => 0 | x :: _, 0 => x | _ :: xs, k + 1 => getNatAt xs k
def allBelowFrom (pred : ℕ → Bool) : ℕ → ℕ → Bool
  | _, 0 => true | off, rem + 1 => pred off && allBelowFrom pred (off + 1) rem
theorem slim_allBelowFrom_eq (pred : ℕ → Bool) : ∀ (off rem : ℕ),
    allBelowFrom pred off rem = Slot3MicroEngineAux.allBelowFrom pred off rem
  | _, 0 => rfl
  | off, rem + 1 => congrArg (_ && ·) (slim_allBelowFrom_eq pred (off + 1) rem)
def allBelow (bound : ℕ) (pred : ℕ → Bool) : Bool := allBelowFrom pred 0 bound
theorem allBelow_iff (bound : ℕ) (pred : ℕ → Bool) :
    allBelow bound pred = true ↔ ∀ m < bound, pred m = true := by
  dsimp only [allBelow]
  rw [slim_allBelowFrom_eq]
  exact Slot3MicroEngineAux.allBelow_iff bound pred
def microWire {M nIn : ℕ} (inW : Fin nIn → Wire M) (cur s : ℕ)
    (hs : nIn ≤ s → cur + (s - nIn) < M) : Wire M :=
  if h : s < nIn then inW ⟨s, h⟩ else ⟨cur + (s - nIn), hs (Nat.le_of_not_lt h)⟩
theorem microWire_val_lt {M nIn : ℕ} (inW : Fin nIn → Wire M) (cur : ℕ)
    (hin_lt : ∀ i, (inW i).val < cur) {s top : ℕ} (hn : nIn ≤ top) (hs : s < top)
    (hM : cur + (top - nIn) ≤ M) :
    (microWire inW cur s (fun hge ↦ by omega)).val < cur + (top - nIn) :=
  Slot3MicroEngineAux.microWire_val_lt inW cur hin_lt hn hs hM
theorem microWire_ne {M nIn : ℕ} (inW : Fin nIn → Wire M) (hin_inj : Function.Injective inW)
    (cur : ℕ) (hin_lt : ∀ i, (inW i).val < cur) {s₁ s₂ : ℕ} (hne : s₁ ≠ s₂)
    (hb₁ : nIn ≤ s₁ → cur + (s₁ - nIn) < M) (hb₂ : nIn ≤ s₂ → cur + (s₂ - nIn) < M) :
    microWire inW cur s₁ hb₁ ≠ microWire inW cur s₂ hb₂ :=
  Slot3MicroEngineAux.microWire_ne inW hin_inj cur hin_lt hne hb₁ hb₂
def ctxMicroRun {M nIn : ℕ} (inW : Fin nIn → Wire M) (hin_inj : Function.Injective inW)
    (cur : ℕ) (hin_lt : ∀ i, (inW i).val < cur) : (top : ℕ) → (hn : nIn ≤ top) →
    (ops : List MicroOp) → (hv : microValid top ops = true) →
    (hcur : cur + (top - nIn) + microAllocs ops ≤ M) → TempCtx M
  | _, _, [], _, _ => .hole
  | top, hn, .notW a :: rest, hv, hcur =>
      have hc0 : cur + (top - nIn) + microAllocs rest ≤ M := hcur
      have ha := (microValid_notW hv).1
      (ctxCliffAlloc (.x (microWire inW cur a (fun _ ↦ by omega)))).append
        (ctxMicroRun inW hin_inj cur hin_lt top hn rest (microValid_notW hv).2 hc0)
  | top, hn, .cnotW a b :: rest, hv, hcur =>
      have hc0 : cur + (top - nIn) + microAllocs rest ≤ M := hcur
      let h := microValid_cnotW hv
      have := h.1
      have := h.2.1
      (ctxCliffAlloc (.cnot (microWire inW cur a (fun _ ↦ by omega))
        (microWire inW cur b (fun _ ↦ by omega))
        (microWire_ne inW hin_inj cur hin_lt h.2.2.1 _ _))).append
        (ctxMicroRun inW hin_inj cur hin_lt top hn rest h.2.2.2 hc0)
  | top, hn, .andAlloc a b :: rest, hv, hcur =>
      have hc1 : cur + (top - nIn) + (1 + microAllocs rest) ≤ M := hcur
      let h := microValid_andAlloc hv
      have := h.1
      have := h.2.1
      let wA := microWire inW cur a (fun _ ↦ by omega)
      let wB := microWire inW cur b (fun _ ↦ by omega)
      (ctxTempBit wA wB ⟨cur + (top - nIn), by omega⟩
        (microWire_ne inW hin_inj cur hin_lt h.2.2.1 _ _)
        (wire_ne_of_lt (microWire_val_lt inW cur hin_lt hn h.1 (by omega)))
        (wire_ne_of_lt (microWire_val_lt inW cur hin_lt hn h.2.1 (by omega)))).append
        (ctxMicroRun inW hin_inj cur hin_lt (top + 1) (by omega) rest h.2.2.2 (by omega))
  | top, _, .zeroAlloc :: rest, hv, hcur =>
      have hc1 : cur + (top - nIn) + (1 + microAllocs rest) ≤ M := hcur
      ctxMicroRun inW hin_inj cur hin_lt (top + 1) (by omega) rest
        (by simpa [microValid] using hv) (by omega)
theorem slim_ctxMicroRun_eq {M nIn : ℕ} (inW : Fin nIn → Wire M)
    (hin_inj : Function.Injective inW) (cur : ℕ) (hin_lt : ∀ i, (inW i).val < cur) :
    ∀ (ops : List MicroOp) (top : ℕ) (hn : nIn ≤ top) (hv : microValid top ops = true)
      (hcur : cur + (top - nIn) + microAllocs ops ≤ M)
      (hv' : Slot3MicroEngineAux.microValid top (ops.map slim_toS3Op) = true)
      (hcur' : cur + (top - nIn) + Slot3MicroEngineAux.microAllocs (ops.map slim_toS3Op) ≤ M),
      ctxMicroRun inW hin_inj cur hin_lt top hn ops hv hcur =
        Slot3MicroEngineAux.ctxMicroRun inW hin_inj cur hin_lt top hn
          (ops.map slim_toS3Op) hv' hcur'
  | [], _, _, _, _, _, _ => rfl
  | .notW _ :: r, top, hn, _, _, _, _ => by
      dsimp only [ctxMicroRun, Slot3MicroEngineAux.ctxMicroRun, List.map, slim_toS3Op]
      exact congr (congrArg TempCtx.append rfl)
        (slim_ctxMicroRun_eq inW hin_inj cur hin_lt r top hn _ _ _ _)
  | .cnotW _ _ :: r, top, hn, _, _, _, _ => by
      dsimp only [ctxMicroRun, Slot3MicroEngineAux.ctxMicroRun, List.map, slim_toS3Op]
      exact congr (congrArg TempCtx.append rfl)
        (slim_ctxMicroRun_eq inW hin_inj cur hin_lt r top hn _ _ _ _)
  | .andAlloc _ _ :: r, top, _, _, _, _, _ => by
      dsimp only [ctxMicroRun, Slot3MicroEngineAux.ctxMicroRun, List.map, slim_toS3Op]
      exact congr (congrArg TempCtx.append rfl)
        (slim_ctxMicroRun_eq inW hin_inj cur hin_lt r (top + 1) _ _ _ _ _)
  | .zeroAlloc :: r, top, _, _, _, _, _ =>
      slim_ctxMicroRun_eq inW hin_inj cur hin_lt r (top + 1) _ _ _ _ _
def ctxMicro {M nIn : ℕ} (inW : Fin nIn → Wire M) (hin_inj : Function.Injective inW)
    (cur nAlloc nAnd : ℕ) (hin_lt : ∀ i, (inW i).val < cur) (ops : List MicroOp) (hMeta :
    microValid nIn ops = true ∧ microAllocs ops = nAlloc ∧ microAnds ops = nAnd)
    (hcur : cur + nAlloc ≤ M) : TempCtx M :=
  ctxMicroRun inW hin_inj cur hin_lt nIn le_rfl ops hMeta.1
    (by
      have hA := hMeta.2.1
      omega)
theorem bitsVal_testBit_eq {W : ℕ} (g : Fin W → ZMod 2) (i : Fin W) :
    (bitsVal g).testBit i.val = decide (g i = 1) :=
  Slot3MicroEngineAux.bitsVal_testBit_eq g i
theorem ctxMicro_scoped {M nIn : ℕ} (inW : Fin nIn → Wire M) (hin_inj : Function.Injective inW)
    (cur nAlloc nAnd : ℕ) (hin_lt : ∀ i, (inW i).val < cur) (ops : List MicroOp)
    (hMeta : microValid nIn ops = true ∧ microAllocs ops = nAlloc ∧ microAnds ops = nAnd)
    (hcur : cur + nAlloc ≤ M) :
    let K := ctxMicro inW hin_inj cur nAlloc nAnd hin_lt ops hMeta hcur
    K.countTempAnd = nAnd ∧
    (∀ {mutW : Wire M → Prop},
      (∀ i, ¬ mutW (inW i)) → (∀ w : Wire M, cur ≤ w.val → ¬ mutW w) →
      K.DisjointFrom mutW ∧ K.SupportsBelowCtx (cur + nAlloc)) ∧
    TempCtxLiftEx cur (cur + nAlloc) K ∧
    (∀ β : BitAssignment M, cleanRem M (M - cur) β →
      let m := bitsVal (fun i ↦ β (inW i))
      let stOut := evalMicroList nIn ops (initBoolList nIn (nIn + nAlloc) m)
      cleanRem M (M - (cur + nAlloc)) (K.fwdBits β) ∧
      (allBelow nIn (fun i ↦ getBoolAt stOut i == m.testBit i) = true →
        ∀ w : Wire M, w.val < cur → K.fwdBits β w = β w) ∧
      (∀ (s : ℕ) (hlo : nIn ≤ s) (hhi : s < nIn + nAlloc),
        K.fwdBits β ⟨cur + (s - nIn), by omega⟩ = boolToZMod2 (getBoolAt stOut s))) := by
  dsimp only
  let ops' := ops.map slim_toS3Op
  have hMeta' : Slot3MicroEngineAux.microValid nIn ops' = true ∧
      Slot3MicroEngineAux.microAllocs ops' = nAlloc ∧ Slot3MicroEngineAux.microAnds ops' = nAnd :=
    ⟨slim_microValid_eq ops nIn ▸ hMeta.1,
      slim_microAllocs_eq ops ▸ hMeta.2.1,
      slim_microAnds_eq ops ▸ hMeta.2.2⟩
  obtain ⟨hCnt, hProps, hLift, hEval⟩ :=
    Slot3MicroEngineAux.ctxMicro_scoped inW hin_inj cur nAlloc nAnd hin_lt ops' hMeta' hcur
  have hK : ctxMicro inW hin_inj cur nAlloc nAnd hin_lt ops hMeta hcur =
      Slot3MicroEngineAux.ctxMicro inW hin_inj cur nAlloc nAnd hin_lt ops' hMeta' hcur :=
    slim_ctxMicroRun_eq inW hin_inj cur hin_lt ops nIn le_rfl hMeta.1 _ hMeta'.1 _
  rw [← hK] at hCnt hProps hLift hEval
  refine ⟨hCnt, hProps, hLift, fun β hβ ↦ ?_⟩
  obtain ⟨hcl, hpres, hout⟩ := hEval β hβ
  have hst : evalMicroList nIn ops (initBoolList nIn (nIn + nAlloc) (bitsVal (fun i ↦ β (inW i)))) =
      Slot3MicroEngineAux.evalMicroList nIn ops'
        (Slot3MicroEngineAux.initBoolList nIn (nIn + nAlloc) (bitsVal (fun i ↦ β (inW i)))) := by
    dsimp only [initBoolList, Slot3MicroEngineAux.initBoolList, ops']
    rw [slim_mkBoolList_eq, slim_evalMicroList_eq]
  refine ⟨hcl, fun hall ↦ hpres ?_, fun s hlo hhi ↦ ?_⟩
  · simpa only [allBelow, Slot3MicroEngineAux.allBelow, ← slim_allBelowFrom_eq, ← hst,
      ← slim_getBoolAt_eq] using hall
  · rw [hst, slim_getBoolAt_eq]
    exact hout s hlo hhi
set_option maxRecDepth 8192
local macro "M48" : term => `(((33 + 15) + 273))
theorem padZeroBits_ltAux {kAct mClean : ℕ} (α : BitAssignment kAct)
    (w : Wire (kAct + mClean)) (hw : w.val < kAct) : padZeroBits α w = α ⟨w.val, hw⟩ := by
  simpa only [padZeroBits, Fin.addCases_left] using
    congrArg (padZeroBits α) (Fin.ext (by simp) : w = Fin.castAdd mClean ⟨w.val, hw⟩)
theorem padZeroBits_cleanRem {kAct mClean : ℕ} (α : BitAssignment kAct) :
    cleanRem (kAct + mClean) mClean (padZeroBits α) := fun w ↦
  Fin.addCases (fun i hi ↦ absurd hi (by simp [Fin.val_castAdd]))
    (fun j _ ↦ by simp only [padZeroBits, Fin.addCases_right]) w
def mkWireVec (M n : ℕ) (L : List ℕ)
    (hM : allBelow n (fun i ↦ decide (getNatAt L i < M)) = true) (i : Fin n) : Wire M :=
  ⟨getNatAt L i.val, of_decide_eq_true ((allBelow_iff n _).mp hM i.val i.isLt)⟩
theorem boolToZMod2_decide_eq_one (b : Bool) : decide (boolToZMod2 b = 1) = b := by
  cases b <;> rfl
theorem ctxMicro_eval_strict {M nIn : ℕ} (inW : Fin nIn → Wire M)
    (hin_inj : Function.Injective inW) (cur nAlloc nAnd : ℕ) (hin_lt : ∀ i, (inW i).val < cur)
    (ops : List MicroOp)
    (hMeta : microValid nIn ops = true ∧ microAllocs ops = nAlloc ∧ microAnds ops = nAnd)
    (hcur : cur + nAlloc ≤ M) {β δ : BitAssignment M}
    (hδ : δ = (ctxMicro inW hin_inj cur nAlloc nAnd hin_lt ops hMeta hcur).fwdBits β)
    (hβ : cleanRem M (M - cur) β) (inBits : Fin nIn → Bool)
    (hIn : ∀ i : Fin nIn, β (inW i) = boolToZMod2 (inBits i)) :
    let m := bitsVal (fun i ↦ β (inW i))
    let trOut := runMicroTree nIn (nIn + nAlloc) m ops
    m < 2 ^ nIn ∧ (∀ i : Fin nIn, m.testBit i.val = inBits i) ∧
      cleanRem M (M - (cur + nAlloc)) δ ∧
      (allBelow nIn (fun i ↦ trOut.get i == m.testBit i) = true →
        ∀ w : Wire M, w.val < cur → δ w = β w) ∧
      (∀ (s : ℕ) (hlo : nIn ≤ s) (hhi : s < nIn + nAlloc),
        δ ⟨cur + (s - nIn), by omega⟩ = boolToZMod2 (trOut.get s)) := by
  subst hδ
  obtain ⟨hcl, hpres, hout⟩ :=
    (ctxMicro_scoped inW hin_inj cur nAlloc nAnd hin_lt ops hMeta hcur).2.2.2 β hβ
  have halloc : nIn + microAllocs ops = nIn + nAlloc := congrArg (nIn + ·) hMeta.2.1
  have htr := fun s hs ↦ runMicroTree_get_eq nIn (nIn + nAlloc)
    (bitsVal (fun i ↦ β (inW i))) ops hMeta.1 halloc s hs
  refine ⟨bitsVal_lt_two_pow _, fun i ↦ ?_, hcl, fun hall ↦ hpres ?_,
    fun s hlo hhi ↦ (hout s hlo hhi).trans (congrArg boolToZMod2 (htr s hhi).symm)⟩
  · rw [bitsVal_testBit_eq (fun j ↦ β (inW j)) i, hIn i, boolToZMod2_decide_eq_one]
  · rw [allBelow_iff] at hall ⊢
    exact fun k hk ↦ htr k (by omega) ▸ hall k hk
theorem ctxMicro_step {M nIn : ℕ} (inW : Fin nIn → Wire M) (hin_inj : Function.Injective inW)
    (cur nAlloc nAnd : ℕ) (hin_lt : ∀ i, (inW i).val < cur) (ops : List MicroOp)
    (hMeta : microValid nIn ops = true ∧ microAllocs ops = nAlloc ∧ microAnds ops = nAnd)
    (hcur : cur + nAlloc ≤ M) (β : BitAssignment M) (hβ : cleanRem M (M - cur) β) :
    let K := ctxMicro inW hin_inj cur nAlloc nAnd hin_lt ops hMeta hcur
    let m := bitsVal (fun i ↦ β (inW i))
    let trOut := runMicroTree nIn (nIn + nAlloc) m ops
    m < 2 ^ nIn ∧ (∀ i : Fin nIn, m.testBit i.val = decide (β (inW i) = 1)) ∧
      cleanRem M (M - (cur + nAlloc)) (K.fwdBits β) ∧
      (allBelow nIn (fun i ↦ trOut.get i == m.testBit i) = true →
        ∀ w : Wire M, w.val < cur → K.fwdBits β w = β w) ∧
      (∀ (s : ℕ) (hlo : nIn ≤ s) (hhi : s < nIn + nAlloc),
        K.fwdBits β ⟨cur + (s - nIn), by omega⟩ = boolToZMod2 (trOut.get s)) :=
  ctxMicro_eval_strict inW hin_inj cur nAlloc nAnd hin_lt ops hMeta hcur rfl hβ
    (fun i ↦ decide (β (inW i) = 1)) (fun i ↦ zmod2_eq_boolToZMod2 (β (inW i)))
def s2Top7InList : List ℕ := [15,16,17,18,19,20,21]
theorem embedUnitary_permSignUnitary_mulVec_single {n k : ℕ} (rAct : QRegister k n)
    (perm : Equiv.Perm (Fin (2 ^ k))) (phase : Fin (2 ^ k) → Bool) (g : Fin (2 ^ n)) :
    (rAct.embedUnitary (permSignUnitary perm phase)).1.mulVec (Pi.single g 1) =
    (if phase (rAct.extractIndex g) then (-1 : ℂ) else 1) • Pi.single
    (rAct.replaceIndex g (perm (rAct.extractIndex g))) 1 := by
  let hpU : Unitary (2 ^ k) := ⟨invPermMat perm, permMatrix_mem_unitaryGroup perm.symm⟩
  rw [show permSignUnitary perm phase = hpU * diagSignUnitary phase from Subtype.ext rfl,
    QRegister.embedUnitary_mul, Submonoid.coe_mul, ← Matrix.mulVec_mulVec,
    embedUnitary_diagSignUnitary_mulVec_single, Matrix.mulVec_smul]
  congr 1
  let hTarget := rAct.replaceIndex g (perm (rAct.extractIndex g))
  have hSplit : rAct.basisSplitEquiv hTarget =
      (perm (rAct.extractIndex g), (rAct.basisSplitEquiv g).2) :=
    rAct.basisSplitEquiv_replaceIndex g (perm (rAct.extractIndex g))
  funext i
  rw [Matrix.mulVec_single_one]
  change rAct.embedMatrix (invPermMat perm) i g =
    (Pi.single hTarget (1 : ℂ) : Fin (2 ^ n) → ℂ) i
  rw [QRegister.embedMatrix_apply]
  by_cases hi : i = hTarget
  · subst hi
    simp [hTarget, rAct.extractIndex_replaceIndex, invPermMat,
      Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply]
  · rw [Pi.single_eq_of_ne hi]
    by_cases henv : (rAct.basisSplitEquiv i).2 = (rAct.basisSplitEquiv g).2
    · simp only [henv, ↓reduceIte, mul_one, invPermMat, Equiv.Perm.permMatrix,
        PEquiv.toMatrix_apply, ite_eq_right_iff, Equiv.toPEquiv_apply, Option.mem_def,
        Option.some.injEq]
      exact fun hmem ↦ (hi <| rAct.basisSplitEquiv.injective <| Prod.ext
        (by simpa [QRegister.basisSplitEquiv_apply_fst, hSplit] using congrArg perm hmem)
        (henv.trans (congrArg Prod.snd hSplit).symm)).elim
    · simp [henv]
theorem phaseDiag_eq {kAct : ℕ} (pred : BitAssignment kAct → ZMod 2) :
    MomSlot0CircuitHalf.phaseDiagUnitary pred =
      MomSlots35Slot3ProjNuclear.Slot3CleanPrim.phaseDiagUnitary pred := Subtype.ext rfl
set_option allowUnsafeReducibility true in
theorem realizesEmbedded_seq {Var : Type} [Fintype Var] [DecidableEq Var] {kAct mWork n : ℕ}
    [NeZero (2 ^ n)] (rAct : QRegister kAct n) (rWork : QRegister mWork n)
    (hDisj : rAct.DisjointWires rWork) {u₁ u₂ : Unitary (2 ^ kAct)}
    {d₁ d₂ : DynamicCircuit Var n}
    (h₁ : DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace rAct rWork u₁ d₁)
    (h₂ : DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace rAct rWork u₂ d₂) :
    DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace rAct rWork
      (u₂ * u₁) (.seq d₁ d₂) := h₁.seq hDisj h₂
theorem realizesEmbedded_compose {Var : Type} [Fintype Var] [DecidableEq Var]
    {kSub kBig mWork n : ℕ} [NeZero (2 ^ n)] (rBig : QRegister kBig n)
    (sel : QRegister kSub kBig) (rWork : QRegister mWork n) {uSub : Unitary (2 ^ kSub)}
    {d : DynamicCircuit Var n}
    (hSub : DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace
      (rBig.compose sel) rWork uSub d) :
    DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace
      rBig rWork (sel.embedUnitary uSub) d := hSub.widenActive
set_option maxRecDepth 2000
end ConfigShiftedMagS1

end ShiftedMagS1
end
end ModShiftedMagS1

end QuantumComputation.Specs.StoppingPowerSolution
