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

public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.GivensFramesCascade

@[expose] public section

namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.CircuitModular.UnsignedGivens
open QuantumComputation.Specs QuantumComputation.Specs.P450

open Operator QProg Matrix
open QuantumComputation.Specs QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution
open QuantumComputation.Specs.P450
open CircuitModular GivensOps
open scoped Matrix ComplexOrder MatrixOrder BigOperators Circuit.Notation

/-! ## Section 4B-2a: Binary/Angle Helpers, Shared Plane/Apex Wrappers & Family 1 (`Lac = 1`) Givens
-/

section Phase4B2a

/-! ### 1. Gate-Count, Binary Decomposition & `givensLeafAngle` Bridges -/

@[simp]
theorem count_onRegister {k n m : ℕ} (c : Circuit k) (r : QRegister k n) (g : PrimitiveGate m) :
    (c.onRegister r).count g = c.count g := by
  induction c with
  | identity => rfl
  | seq c₁ c₂ ih₁ ih₂ => simp [Circuit.onRegister, Circuit.count, ih₁, ih₂]
  | gate _ _ => rfl

theorem zmod2_mul_val (a b : ZMod 2) : (a * b).val = a.val * b.val := by
  fin_cases a <;> fin_cases b <;> decide

theorem bitSeqVal_mod_two_pow {B : ℕ} (K : ℕ) :
    bitSeqVal (fun j : Fin B => ((K / 2 ^ j.val % 2 : ℕ) : ZMod 2)) = K % 2 ^ B := by
  apply nat_eq_of_lt_two_pow_of_div_mod_eq (bitSeqVal_lt _) (Nat.mod_lt K (Nat.two_pow_pos B))
  intro j
  have h1 := congrArg ZMod.val
    (bitSeqVal_div_pow_mod_two (fun i : Fin B => ((K / 2 ^ i.val % 2 : ℕ) : ZMod 2)) j)
  rw [zmod2_natCast_mod_two_val, zmod2_natCast_mod_two_val] at h1
  rw [h1]
  have hdvd : 2 ^ (j.val + 1) ∣ 2 ^ B := Nat.pow_dvd_pow 2 j.isLt
  have hdm : ∀ m : ℕ, m / 2 ^ j.val % 2 = (m % 2 ^ (j.val + 1)) / 2 ^ j.val := by
    intro m; rw [pow_succ, Nat.mod_mul_right_div_self]
  rw [hdm (K % 2 ^ B), Nat.mod_mod_of_dvd _ hdvd, ← hdm]

theorem nat_decomp_13bit {K : ℕ} (hK : K < 8192) :
    K % 2 ^ 11 + 2 ^ 11 * (K / 2 ^ 11 % 2) + 2 ^ (11 + 1) * (K / 2 ^ 12 % 2) = K := by
  omega

theorem nat_decomp_apex {k₀ : ℕ} (hlo : 2048 ≤ k₀) (hhi : k₀ < 6144) :
    k₀ % 2 ^ 10 + 2 ^ 10 * (k₀ / 2 ^ 10 % 2) + 2 ^ (10 + 1) * (k₀ / 2 ^ 12 % 2) +
      2 ^ (10 + 1) * 1 = k₀ := by
  omega

theorem angle_13bit_eq_givensLeafAngle {N : ℕ} (k : Fin N → ℤ) (p : ℕ) (hp : p < N)
    (K : ℕ) (hk : k ⟨p, hp⟩ = (K : ℤ)) :
    2 * Real.pi * (K : ℝ) / (2 : ℝ) ^ (11 + 3) = GivensOps.givensLeafAngle N 15 k p := by
  simp only [GivensOps.givensLeafAngle, hp, ↓reduceDIte, hk, Int.cast_natCast]
  norm_num
  ring

theorem angle_apex_eq_two_mul_givensLeafAngle {N : ℕ} (hN : 1 < N) (k : Fin N → ℤ)
    (k₀ : ℕ) (hk0 : k ⟨0, by omega⟩ = (k₀ : ℤ)) :
    2 * Real.pi * (k₀ : ℝ) / (2 : ℝ) ^ (10 + 3) = 2 * GivensOps.givensLeafAngle N 15 k 0 := by
  have h0 : 0 < N := by omega
  simp only [GivensOps.givensLeafAngle, h0, ↓reduceDIte, hk0, Int.cast_natCast]
  norm_num
  ring

theorem embedUnitary_one_eq {k n : ℕ} (r : QRegister k n) :
    r.embedUnitary 1 = 1 := by
  apply Subtype.ext
  change r.embedMatrix (1 : Operator (2 ^ k)) = 1
  exact r.embedMatrix_one

theorem embedUnitary_mul_eq {k n : ℕ} (r : QRegister k n) (A B : Unitary (2 ^ k)) :
    r.embedUnitary (A * B) = r.embedUnitary A * r.embedUnitary B := by
  apply Subtype.ext
  change r.embedMatrix (A.1 * B.1) = r.embedMatrix A.1 * r.embedMatrix B.1
  exact r.embedMatrix_mul A.1 B.1

/-! ### 2. Register Disjointness Extractors & Catalyst Lifting Helpers -/

section DisjointnessExtractors

theorem ne_spin_ctrl {n N k_ctrl : ℕ} {rSpin : QRegister N n} {rCtrl : QRegister k_ctrl n}
    (hsc : rSpin.DisjointWires rCtrl) (i : Fin N) (j : Fin k_ctrl) : rSpin i ≠ rCtrl j :=
  QRegister.disjoint_iff.mp hsc i j

theorem ne_spin_cat {n N k_ctrl b_cat : ℕ} {rSpin : QRegister N n} {rCtrl : QRegister k_ctrl n}
    (hsc : rSpin.DisjointWires rCtrl) {rCat : QRegister b_cat n}
    (hac : (rSpin.concat rCtrl hsc).DisjointWires rCat)
    (i : Fin N) (j : Fin b_cat) : rSpin i ≠ rCat j := by
  have h := QRegister.disjoint_iff.mp hac (Fin.castAdd k_ctrl i) j
  simpa only [QRegister.concat_apply_left] using h

theorem ne_ctrl_cat {n N k_ctrl b_cat : ℕ} {rSpin : QRegister N n} {rCtrl : QRegister k_ctrl n}
    (hsc : rSpin.DisjointWires rCtrl) {rCat : QRegister b_cat n}
    (hac : (rSpin.concat rCtrl hsc).DisjointWires rCat)
    (i : Fin k_ctrl) (j : Fin b_cat) : rCtrl i ≠ rCat j := by
  have h := QRegister.disjoint_iff.mp hac (Fin.natAdd N i) j
  simpa only [QRegister.concat_apply_right] using h

theorem ne_spin_work {n N k_ctrl b_cat m : ℕ} {rSpin : QRegister N n} {rCtrl : QRegister k_ctrl n}
    (hsc : rSpin.DisjointWires rCtrl) {rCat : QRegister b_cat n}
    (hac : (rSpin.concat rCtrl hsc).DisjointWires rCat) {rWork : QRegister m n}
    (hdisj : ((rSpin.concat rCtrl hsc).concat rCat hac).DisjointWires rWork)
    (i : Fin N) (j : Fin m) : rSpin i ≠ rWork j := by
  have h := QRegister.disjoint_iff.mp hdisj (Fin.castAdd b_cat (Fin.castAdd k_ctrl i)) j
  simpa only [QRegister.concat_apply_left] using h

theorem ne_ctrl_work {n N k_ctrl b_cat m : ℕ} {rSpin : QRegister N n} {rCtrl : QRegister k_ctrl n}
    (hsc : rSpin.DisjointWires rCtrl) {rCat : QRegister b_cat n}
    (hac : (rSpin.concat rCtrl hsc).DisjointWires rCat) {rWork : QRegister m n}
    (hdisj : ((rSpin.concat rCtrl hsc).concat rCat hac).DisjointWires rWork)
    (i : Fin k_ctrl) (j : Fin m) : rCtrl i ≠ rWork j := by
  have h := QRegister.disjoint_iff.mp hdisj (Fin.castAdd b_cat (Fin.natAdd N i)) j
  simpa only [QRegister.concat_apply_left, QRegister.concat_apply_right] using h

theorem ne_cat_work {n N k_ctrl b_cat m : ℕ} {rSpin : QRegister N n} {rCtrl : QRegister k_ctrl n}
    (hsc : rSpin.DisjointWires rCtrl) {rCat : QRegister b_cat n}
    (hac : (rSpin.concat rCtrl hsc).DisjointWires rCat) {rWork : QRegister m n}
    (hdisj : ((rSpin.concat rCtrl hsc).concat rCat hac).DisjointWires rWork)
    (i : Fin b_cat) (j : Fin m) : rCat i ≠ rWork j := by
  have h := QRegister.disjoint_iff.mp hdisj (Fin.natAdd (N + k_ctrl) i) j
  simpa only [QRegister.concat_apply_right] using h

theorem disj_sub_ctrl {n N k_ctrl k_sub : ℕ} {rSpin : QRegister N n} {rCtrl : QRegister k_ctrl n}
    (hsc : rSpin.DisjointWires rCtrl) (sel : QRegister k_sub N) :
    (rSpin.compose sel).DisjointWires rCtrl := by
  rw [QRegister.disjoint_iff]
  intro i j
  exact ne_spin_ctrl hsc (sel i) j

theorem disj_sub_cat {n N k_ctrl b_cat k_sub : ℕ} {rSpin : QRegister N n} {rCtrl : QRegister k_ctrl
    n}
    (hsc : rSpin.DisjointWires rCtrl) {rCat : QRegister b_cat n}
    (hac : (rSpin.concat rCtrl hsc).DisjointWires rCat) (sel : QRegister k_sub N) :
    ((rSpin.compose sel).concat rCtrl (disj_sub_ctrl hsc sel)).DisjointWires rCat := by
  rw [QRegister.disjoint_iff]
  intro idx j
  refine Fin.addCases (fun i => ?_) (fun l => ?_) idx
  · simp only [QRegister.concat_apply_left, QRegister.compose_apply]
    exact ne_spin_cat hsc hac (sel i) j
  · simp only [QRegister.concat_apply_right]
    exact ne_ctrl_cat hsc hac l j

theorem disj_sub_work {n N k_ctrl b_cat m k_sub : ℕ} {rSpin : QRegister N n} {rCtrl : QRegister
    k_ctrl n}
    (hsc : rSpin.DisjointWires rCtrl) {rCat : QRegister b_cat n}
    (hac : (rSpin.concat rCtrl hsc).DisjointWires rCat) {rWork : QRegister m n}
    (hdisj : ((rSpin.concat rCtrl hsc).concat rCat hac).DisjointWires rWork)
    (sel : QRegister k_sub N) :
    (((rSpin.compose sel).concat rCtrl (disj_sub_ctrl hsc sel)).concat rCat
      (disj_sub_cat hsc hac sel)).DisjointWires rWork := by
  rw [QRegister.disjoint_iff]
  intro idx w
  refine Fin.addCases (fun ic => ?_) (fun c => ?_) idx
  · simp only [QRegister.concat_apply_left]
    refine Fin.addCases (fun i => ?_) (fun l => ?_) ic
    · simp only [QRegister.concat_apply_left, QRegister.compose_apply]
      exact ne_spin_work hsc hac hdisj (sel i) w
    · simp only [QRegister.concat_apply_right]
      exact ne_ctrl_work hsc hac hdisj l w
  · simp only [QRegister.concat_apply_right]
    exact ne_cat_work hsc hac hdisj c w

theorem disj_sub_cat_comp {n N k_ctrl b_cat k_sub b_sub : ℕ}
    {rSpin : QRegister N n} {rCtrl : QRegister k_ctrl n}
    (hsc : rSpin.DisjointWires rCtrl) {rCat : QRegister b_cat n}
    (hac : (rSpin.concat rCtrl hsc).DisjointWires rCat)
    (sel : QRegister k_sub N) (selCat : QRegister b_sub b_cat) :
    ((rSpin.compose sel).concat rCtrl (disj_sub_ctrl hsc sel)).DisjointWires
      (rCat.compose selCat) := by
  rw [QRegister.disjoint_iff]
  intro idx j
  exact QRegister.disjoint_iff.mp (disj_sub_cat hsc hac sel) idx (selCat j)

end DisjointnessExtractors

theorem slice_image_subset {n m off len : ℕ} (r : QRegister m n) (h : off + len ≤ m) :
    (r.slice off len h).image ⊆ r.image := by
  intro q hq
  rw [QRegister.mem_image] at hq ⊢
  obtain ⟨i, rfl⟩ := hq
  exact ⟨⟨off + i.val, by omega⟩, QRegister.slice_apply r off len h i⟩

theorem slice_disjoint_of_nonoverlap {n m o₁ l₁ o₂ l₂ : ℕ} (r : QRegister m n)
    (h₁ : o₁ + l₁ ≤ m) (h₂ : o₂ + l₂ ≤ m) (hord : o₁ + l₁ ≤ o₂) :
    (r.slice o₁ l₁ h₁).DisjointWires (r.slice o₂ l₂ h₂) := by
  rw [QRegister.disjoint_iff]
  intro i j hij
  rw [QRegister.slice_apply, QRegister.slice_apply] at hij
  have hv := congrArg Fin.val (r.wires.injective hij)
  dsimp at hv
  omega

/-! ### 3. Shared Workspace-Widened Phase-Kick & Plane / Apex Framing Wrappers -/

/-- Positive Clifford-framed plane wrapper (`0` extra `T`, `0` extra `TOFF`). -/
def framedPlanePosDyn {Var : Type} {n N : ℕ} (p : ℕ) (hp : p + 1 < N)
    (rSpin : QRegister N n) (dKick : DynamicCircuit Var n) : DynamicCircuit Var n :=
  let rPair := rSpin.compose (GivensOps.pairAdj N p hp)
  .seq (.circuit (cliffPrePos.onRegister rPair))
    (.seq dKick (.circuit (cliffPostPos.onRegister rPair)))

/-- Negative Clifford-framed plane wrapper (`0` extra `T`, `0` extra `TOFF`). -/
def framedPlaneNegDyn {Var : Type} {n N : ℕ} (p : ℕ) (hp : p + 1 < N)
    (rSpin : QRegister N n) (dKick : DynamicCircuit Var n) : DynamicCircuit Var n :=
  let rPair := rSpin.compose (GivensOps.pairAdj N p hp)
  .seq (.circuit (cliffPreNeg.onRegister rPair))
    (.seq dKick (.circuit (cliffPostNeg.onRegister rPair)))

@[simp] theorem count_framedPlanePosDyn_toff {Var : Type} {n N : ℕ} (p : ℕ) (hp : p + 1 < N)
    (rSpin : QRegister N n) (dKick : DynamicCircuit Var n) :
    (framedPlanePosDyn p hp rSpin dKick).count .TOFF = dKick.count .TOFF := by
  simp [framedPlanePosDyn]

@[simp] theorem count_framedPlanePosDyn_t {Var : Type} {n N : ℕ} (p : ℕ) (hp : p + 1 < N)
    (rSpin : QRegister N n) (dKick : DynamicCircuit Var n) :
    (framedPlanePosDyn p hp rSpin dKick).count .T = dKick.count .T := by
  simp [framedPlanePosDyn]

@[simp] theorem count_framedPlaneNegDyn_toff {Var : Type} {n N : ℕ} (p : ℕ) (hp : p + 1 < N)
    (rSpin : QRegister N n) (dKick : DynamicCircuit Var n) :
    (framedPlaneNegDyn p hp rSpin dKick).count .TOFF = dKick.count .TOFF := by
  simp [framedPlaneNegDyn]

@[simp] theorem count_framedPlaneNegDyn_t {Var : Type} {n N : ℕ} (p : ℕ) (hp : p + 1 < N)
    (rSpin : QRegister N n) (dKick : DynamicCircuit Var n) :
    (framedPlaneNegDyn p hp rSpin dKick).count .T = dKick.count .T := by
  simp [framedPlaneNegDyn]

/-- Wire-controlled fused apex wrapper (`+4 T` via `directBitStep (rCtrl actIdx) (rPair0 1) w_act1`,
followed by `czCircuit (rCtrl actIdx) (rPair0 0)`). -/
def framedCtrlApexDyn {Var : Type} {n N k_ctrl : ℕ} (v : Var) (hN : 1 < N)
    (rSpin : QRegister N n) (rCtrl : QRegister k_ctrl n) (hsc : rSpin.DisjointWires rCtrl)
    (actIdx : Fin k_ctrl) (w_act1 : Wire n)
    (hact_w1 : rCtrl actIdx ≠ w_act1)
    (hp1_w1 : rSpin ⟨1, hN⟩ ≠ w_act1)
    (hp0_w1 : rSpin ⟨0, by omega⟩ ≠ w_act1)
    (dKick10 : DynamicCircuit Var n) : DynamicCircuit Var n :=
  let rPair0 := rSpin.compose (GivensOps.pairAdj N 0 hN)
  have hp0_w1' : rPair0 0 ≠ w_act1 := hp0_w1
  have hp1_w1' : rPair0 1 ≠ w_act1 := hp1_w1
  have hact_p1 : rCtrl actIdx ≠ rPair0 1 := (ne_spin_ctrl hsc ⟨1, hN⟩ actIdx).symm
  let cOff := Circuit.S w_act1 ;;ᶜ czCircuit (rPair0 0) w_act1 hp0_w1'
  let sAct := directBitStep (rCtrl actIdx) (rPair0 1) w_act1 hact_p1 hact_w1 hp1_w1'
  let dWrapped := sAct.wrapDynamic v (DynamicCircuit.seq (.circuit cOff) dKick10)
  let dGivens := DynamicCircuit.seq (.circuit (cliffPrePos.onRegister rPair0))
    (DynamicCircuit.seq dWrapped (.circuit (cliffPostPos.onRegister rPair0)))
  have hne_cz : rCtrl actIdx ≠ rPair0 0 := (ne_spin_ctrl hsc ⟨0, by omega⟩ actIdx).symm
  DynamicCircuit.seq dGivens (.circuit (czCircuit (rCtrl actIdx) (rPair0 0) hne_cz))

@[simp] theorem count_framedCtrlApexDyn_toff {Var : Type} {n N k_ctrl : ℕ} (v : Var) (hN : 1 < N)
    (rSpin : QRegister N n) (rCtrl : QRegister k_ctrl n) (hsc : rSpin.DisjointWires rCtrl)
    (actIdx : Fin k_ctrl) (w_act1 : Wire n)
    (hact_w1 : rCtrl actIdx ≠ w_act1) (hp1_w1 : rSpin ⟨1, hN⟩ ≠ w_act1)
    (hp0_w1 : rSpin ⟨0, by omega⟩ ≠ w_act1)
    (dKick10 : DynamicCircuit Var n) :
    (framedCtrlApexDyn v hN rSpin rCtrl hsc actIdx w_act1 hact_w1 hp1_w1 hp0_w1 dKick10).count .TOFF
      =
      dKick10.count .TOFF := by
  simp [framedCtrlApexDyn,
    PhasedStep.count_wrapDynamic_toff _ _ _ (isCleanBitStep_directBitStep _ _ _ _ _ _).clifford]

@[simp] theorem count_framedCtrlApexDyn_t {Var : Type} {n N k_ctrl : ℕ} (v : Var) (hN : 1 < N)
    (rSpin : QRegister N n) (rCtrl : QRegister k_ctrl n) (hsc : rSpin.DisjointWires rCtrl)
    (actIdx : Fin k_ctrl) (w_act1 : Wire n)
    (hact_w1 : rCtrl actIdx ≠ w_act1) (hp1_w1 : rSpin ⟨1, hN⟩ ≠ w_act1)
    (hp0_w1 : rSpin ⟨0, by omega⟩ ≠ w_act1)
    (dKick10 : DynamicCircuit Var n) :
    (framedCtrlApexDyn v hN rSpin rCtrl hsc actIdx w_act1 hact_w1 hp1_w1 hp0_w1 dKick10).count .T =
      4 + dKick10.count .T := by
  simp [framedCtrlApexDyn,
    PhasedStep.count_wrapDynamic_t _ _ _ (isCleanBitStep_directBitStep _ _ _ _ _ _).clifford]

/-! ### 4. Family 1 (`Lac = 1`): Raw Unsigned `13`-Bit Quantum-Register Givens (`98 T` / `90 T` /
`94 T`) -/

/-! #### Gate Counts (`0 TOFF`, Exact `T` Counts — Polymorphic over Bare `{Var : Type}`) -/

/-! #### Catalytic Soundness Theorems for Family 1 (`Lac = 1`) -/

end Phase4B2a

end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.CircuitModular.UnsignedGivens

end
