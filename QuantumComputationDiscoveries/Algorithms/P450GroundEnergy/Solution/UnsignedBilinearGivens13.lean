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

public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.UnsignedRegGivens

@[expose] public section

namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.CircuitModular.UnsignedGivens

open Operator QProg Matrix
open QuantumComputation.Specs QuantumComputation.Specs.P450
open CircuitModular GivensOps
open scoped Matrix ComplexOrder MatrixOrder BigOperators Circuit.Notation

/-! ## Family 2 (`Lac = 2`) In-Place Streaming Bilinear Givens (`102 T` / `94 T` / `98 T`) -/

section BilinearLac2

/-! ### 1. One-Hot / At-Most-One-Hot Algebra & `bilinearBitFormula` -/

/-- At most one bit of `hbits : Fin G → ZMod 2` is nonzero (covers all-zero and one-hot states). -/
def AtMostOneHotBits {G : ℕ} (hbits : Fin G → ZMod 2) : Prop :=
  ∀ g₁ g₂ : Fin G, g₁ ≠ g₂ → hbits g₁ = 0 ∨ hbits g₂ = 0

/-- Unique index `g₀ : Fin G` has `hbits g₀ = 1` and all `g ≠ g₀` have `hbits g = 0`. -/
def IsOneHotBits {G : ℕ} (g₀ : Fin G) (hbits : Fin G → ZMod 2) : Prop :=
  hbits g₀ = 1 ∧ ∀ g : Fin G, g ≠ g₀ → hbits g = 0

theorem IsOneHotBits.atMostOneHot {G : ℕ} {g₀ : Fin G} {hbits : Fin G → ZMod 2}
    (h : IsOneHotBits g₀ hbits) : AtMostOneHotBits hbits := by
  intro g₁ g₂ hne
  by_cases h1 : g₁ = g₀
  · subst h1; exact Or.inr (h.2 g₂ hne.symm)
  · exact Or.inl (h.2 g₁ h1)

/-- Pure `ZMod 2` masked dot product matching `maskSumBit`. -/
def maskBitSum {G : ℕ} (hbits : Fin G → ZMod 2) (m : Fin G → Bool) : ZMod 2 :=
  ∑ g : Fin G, if m g then hbits g else 0

theorem maskBitSum_zero {G : ℕ} (m : Fin G → Bool) :
    maskBitSum (fun _ : Fin G => (0 : ZMod 2)) m = 0 := by
  unfold maskBitSum
  refine Finset.sum_eq_zero fun g _ => ?_
  split_ifs <;> rfl

theorem maskBitSum_of_isOneHot {G : ℕ} {g₀ : Fin G} {hbits : Fin G → ZMod 2}
    (h : IsOneHotBits g₀ hbits) (m : Fin G → Bool) :
    maskBitSum hbits m = if m g₀ then 1 else 0 := by
  unfold maskBitSum
  rw [Finset.sum_eq_single g₀]
  · rw [h.1]
  · intro g _ hne; rw [h.2 g hne, ite_self]
  · intro hg; exact absurd (Finset.mem_univ g₀) hg

theorem maskBitSum_and_eq_mul_of_atMostOneHot {G : ℕ} {hbits : Fin G → ZMod 2}
    (h : AtMostOneHotBits hbits) (b0 b1 : Fin G → Bool) :
    maskBitSum hbits (fun g => b0 g && b1 g) = maskBitSum hbits b0 * maskBitSum hbits b1 := by
  by_cases hall : ∀ g : Fin G, hbits g = 0
  · have hfun : hbits = fun _ => 0 := funext hall
    rw [hfun, maskBitSum_zero, maskBitSum_zero, maskBitSum_zero, mul_zero]
  · push Not at hall
    obtain ⟨g₀, hg₀⟩ := hall
    have hg1 : hbits g₀ = 1 := by
      rcases zmod2_eq_zero_or_one (hbits g₀) with h0 | h1
      · exact absurd h0 hg₀
      · exact h1
    have hoh : IsOneHotBits g₀ hbits := ⟨hg1, fun g hne => by
      rcases h g₀ g hne.symm with h0 | h0
      · exact absurd h0 hg₀
      · exact h0⟩
    rw [maskBitSum_of_isOneHot hoh, maskBitSum_of_isOneHot hoh, maskBitSum_of_isOneHot hoh]
    cases b0 g₀ <;> cases b1 g₀ <;> rfl

/-- Pure `ZMod 2` rank-2 bilinear bit formula `(u + M_1) * (v + M_0) + M_{01}` across `2^G`
states. -/
def bilinearBitFormula {G : ℕ} (u_val v_val : ZMod 2) (hbits : Fin G → ZMod 2)
    (b0 b1 : Fin G → Bool) : ZMod 2 :=
  (u_val + maskBitSum hbits b1) * (v_val + maskBitSum hbits b0) +
    maskBitSum hbits (fun g => b0 g && b1 g)

theorem bilinearBitFormula_zero_of_atMostOneHot {G : ℕ} {hbits : Fin G → ZMod 2}
    (h : AtMostOneHotBits hbits) (b0 b1 : Fin G → Bool) :
    bilinearBitFormula 0 0 hbits b0 b1 = 0 := by
  unfold bilinearBitFormula
  rw [zero_add, zero_add, maskBitSum_and_eq_mul_of_atMostOneHot h b0 b1, mul_comm, zmod2_add_self]

theorem bilinearBitFormula_one_of_isOneHot {G : ℕ} {g₀ : Fin G} {hbits : Fin G → ZMod 2}
    (h : IsOneHotBits g₀ hbits) (s_bit : ZMod 2) (b0 b1 : Fin G → Bool) :
    bilinearBitFormula (1 + s_bit) s_bit hbits b0 b1 =
      if (if s_bit = 0 then b0 g₀ else b1 g₀) then 1 else 0 := by
  unfold bilinearBitFormula
  rw [maskBitSum_of_isOneHot h b1, maskBitSum_of_isOneHot h b0,
    maskBitSum_of_isOneHot h (fun g => b0 g && b1 g)]
  rcases zmod2_eq_zero_or_one s_bit with rfl | rfl <;>
    cases b0 g₀ <;> cases b1 g₀ <;> decide

/-- Boolean bit mask for bit `bit` of `row g sub` in a `Lac = 2` angle table row. -/
def rowBitMask {G : ℕ} (row : Fin G → Bool → ℕ) (sub : Bool) (bit : ℕ) (g : Fin G) : Bool :=
  decide (row g sub / 2 ^ bit % 2 = 1)

theorem ite_rowBitMask_sub {G : ℕ} (row : Fin G → Bool → ℕ) (s_bit : ZMod 2)
    (bit : ℕ) (g₀ : Fin G) :
    (if s_bit = 0 then rowBitMask row false bit g₀ else rowBitMask row true bit g₀) =
      rowBitMask row (decide (s_bit = 1)) bit g₀ := by
  rcases zmod2_eq_zero_or_one s_bit with rfl | rfl
  · have h01 : ¬ ((0 : ZMod 2) = 1) := by decide
    simp [h01]
  · have h10 : (1 : ZMod 2) ≠ 0 := by decide
    simp [h10]

theorem ite_rowBitMask_eq_natCast {G : ℕ} (row : Fin G → Bool → ℕ) (sub : Bool)
    (bit : ℕ) (g₀ : Fin G) :
    (if rowBitMask row sub bit g₀ then (1 : ZMod 2) else 0) =
      ((row g₀ sub / 2 ^ bit % 2 : ℕ) : ZMod 2) := by
  unfold rowBitMask
  rcases Nat.mod_two_eq_zero_or_one (row g₀ sub / 2 ^ bit) with h | h <;> simp [h]

/-- Effective `B`-bit low integer loaded by `bilinearLac2KickDyn` at `(qc, s_bit, hbits)`. -/
noncomputable def bilinearRowLo (B : ℕ) {G : ℕ} (row : Fin G → Bool → ℕ)
    (qc s_bit : ZMod 2) (hbits : Fin G → ZMod 2) : ℕ :=
  bitSeqVal (fun j : Fin B =>
    bilinearBitFormula (qc * (1 + s_bit)) (qc * s_bit) hbits
      (rowBitMask row false j.val) (rowBitMask row true j.val))

/-- Effective single bit (`0` or `1`) loaded by `bilinearLac2KickDyn` for bit index `idx`. -/
def bilinearRowBit (idx : ℕ) {G : ℕ} (row : Fin G → Bool → ℕ)
    (qc s_bit : ZMod 2) (hbits : Fin G → ZMod 2) : ℕ :=
  (bilinearBitFormula (qc * (1 + s_bit)) (qc * s_bit) hbits
    (rowBitMask row false idx) (rowBitMask row true idx)).val

theorem bilinearRowLo_lt (B : ℕ) {G : ℕ} (row : Fin G → Bool → ℕ)
    (qc s_bit : ZMod 2) (hbits : Fin G → ZMod 2) :
    bilinearRowLo B row qc s_bit hbits < 2 ^ B :=
  bitSeqVal_lt _

theorem bilinearRowBit_lt (idx : ℕ) {G : ℕ} (row : Fin G → Bool → ℕ)
    (qc s_bit : ZMod 2) (hbits : Fin G → ZMod 2) :
    bilinearRowBit idx row qc s_bit hbits < 2 :=
  ZMod.val_lt _

theorem bilinearRowLo_zero_of_atMostOneHot (B : ℕ) {G : ℕ} (row : Fin G → Bool → ℕ)
    (s_bit : ZMod 2) {hbits : Fin G → ZMod 2} (h : AtMostOneHotBits hbits) :
    bilinearRowLo B row 0 s_bit hbits = 0 := by
  unfold bilinearRowLo
  have hfun : (fun j : Fin B =>
      bilinearBitFormula (0 * (1 + s_bit)) (0 * s_bit) hbits
        (rowBitMask row false j.val) (rowBitMask row true j.val)) =
      (fun _ : Fin B => (0 : ZMod 2)) := by
    funext j
    rw [zero_mul, zero_mul, bilinearBitFormula_zero_of_atMostOneHot h]
  rw [hfun, bitSeqVal_zero]

theorem bilinearRowBit_zero_of_atMostOneHot (idx : ℕ) {G : ℕ} (row : Fin G → Bool → ℕ)
    (s_bit : ZMod 2) {hbits : Fin G → ZMod 2} (h : AtMostOneHotBits hbits) :
    bilinearRowBit idx row 0 s_bit hbits = 0 := by
  unfold bilinearRowBit
  rw [zero_mul, zero_mul, bilinearBitFormula_zero_of_atMostOneHot h, zmod2_val_zero]

theorem bilinearRowLo_one_of_isOneHot (B : ℕ) {G : ℕ} (row : Fin G → Bool → ℕ)
    (s_bit : ZMod 2) {g₀ : Fin G} {hbits : Fin G → ZMod 2} (h : IsOneHotBits g₀ hbits) :
    bilinearRowLo B row 1 s_bit hbits = row g₀ (decide (s_bit = 1)) % 2 ^ B := by
  unfold bilinearRowLo
  have hfun : (fun j : Fin B =>
      bilinearBitFormula (1 * (1 + s_bit)) (1 * s_bit) hbits
        (rowBitMask row false j.val) (rowBitMask row true j.val)) =
      (fun j : Fin B => ((row g₀ (decide (s_bit = 1)) / 2 ^ j.val % 2 : ℕ) : ZMod 2)) := by
    funext j
    rw [one_mul, one_mul, bilinearBitFormula_one_of_isOneHot h, ite_rowBitMask_sub,
      ite_rowBitMask_eq_natCast]
  rw [hfun, bitSeqVal_mod_two_pow]

theorem bilinearRowBit_one_of_isOneHot (idx : ℕ) {G : ℕ} (row : Fin G → Bool → ℕ)
    (s_bit : ZMod 2) {g₀ : Fin G} {hbits : Fin G → ZMod 2} (h : IsOneHotBits g₀ hbits) :
    bilinearRowBit idx row 1 s_bit hbits = row g₀ (decide (s_bit = 1)) / 2 ^ idx % 2 := by
  unfold bilinearRowBit
  rw [one_mul, one_mul, bilinearBitFormula_one_of_isOneHot h, ite_rowBitMask_sub,
    ite_rowBitMask_eq_natCast, zmod2_natCast_mod_two_val]

/-! ### 2. Catalytic Soundness & One-Hot Fiber Evaluation for Family 2 (`Lac = 2`) -/

/-- Control-register bit vector extracted at `selHot : QRegister G k_ctrl`. -/
def ctrlHotBits {k_ctrl G : ℕ} (selHot : QRegister G k_ctrl) (c : Fin (2 ^ k_ctrl)) :
    Fin G → ZMod 2 :=
  fun g => basisBits k_ctrl c (selHot g)

theorem compose_hot_bits_eq {n k_ctrl G : ℕ} (rCtrl : QRegister k_ctrl n)
    (selHot : QRegister G k_ctrl) (β : BitAssignment n) :
    (fun g : Fin G => β ((rCtrl.compose selHot) g)) = ctrlHotBits selHot (localIdx rCtrl β) := by
  funext g
  dsimp only [ctrlHotBits, QRegister.compose_apply]
  exact (congrFun (basisBits_symm_eq (fun j => β (rCtrl j))) (selHot g)).symm

/-- Effective `13`-bit unsigned integer produced on a non-apex plane at `(qc, c)`. -/
noncomputable def bilinearPlaneEffK {k_ctrl G : ℕ} (row : Fin G → Bool → ℕ)
    (selHot : QRegister G k_ctrl) (subIdx : Fin k_ctrl)
    (qc : ZMod 2) (c : Fin (2 ^ k_ctrl)) : ℕ :=
  let s_bit := basisBits k_ctrl c subIdx
  let hbits := ctrlHotBits selHot c
  bilinearRowLo 11 row qc s_bit hbits +
    2 ^ 11 * bilinearRowBit 11 row qc s_bit hbits +
    2 ^ (11 + 1) * bilinearRowBit 12 row qc s_bit hbits

/-- Effective `13`-bit apex integer produced at `(qc, c)`. -/
noncomputable def bilinearApexEffK {k_ctrl G : ℕ} (row0 : Fin G → Bool → ℕ)
    (selHot : QRegister G k_ctrl) (subIdx : Fin k_ctrl)
    (qc : ZMod 2) (c : Fin (2 ^ k_ctrl)) : ℕ :=
  let s_bit := basisBits k_ctrl c subIdx
  let hbits := ctrlHotBits selHot c
  bilinearRowLo 10 row0 qc s_bit hbits +
    2 ^ 10 * bilinearRowBit 10 row0 qc s_bit hbits +
    2 ^ (10 + 1) * bilinearRowBit 12 row0 qc s_bit hbits +
    2 ^ (10 + 1) * qc.val

theorem bilinearPlaneEffK_zero_of_atMostOneHot {k_ctrl G : ℕ} (row : Fin G → Bool → ℕ)
    (selHot : QRegister G k_ctrl) (subIdx : Fin k_ctrl) {c : Fin (2 ^ k_ctrl)}
    (h : AtMostOneHotBits (ctrlHotBits selHot c)) :
    bilinearPlaneEffK row selHot subIdx 0 c = 0 := by
  dsimp only [bilinearPlaneEffK]
  rw [bilinearRowLo_zero_of_atMostOneHot _ _ _ h,
    bilinearRowBit_zero_of_atMostOneHot _ _ _ h,
    bilinearRowBit_zero_of_atMostOneHot _ _ _ h]
  simp

theorem bilinearPlaneEffK_one_of_isOneHot {k_ctrl G : ℕ} (row : Fin G → Bool → ℕ)
    (selHot : QRegister G k_ctrl) (subIdx : Fin k_ctrl)
    {g₀ : Fin G} {c : Fin (2 ^ k_ctrl)}
    (h : IsOneHotBits g₀ (ctrlHotBits selHot c))
    (hlt : row g₀ (decide (basisBits k_ctrl c subIdx = 1)) < 8192) :
    bilinearPlaneEffK row selHot subIdx 1 c =
      row g₀ (decide (basisBits k_ctrl c subIdx = 1)) := by
  dsimp only [bilinearPlaneEffK]
  rw [bilinearRowLo_one_of_isOneHot _ _ _ h,
    bilinearRowBit_one_of_isOneHot _ _ _ h,
    bilinearRowBit_one_of_isOneHot _ _ _ h]
  exact nat_decomp_13bit hlt

theorem bilinearApexEffK_zero_of_atMostOneHot {k_ctrl G : ℕ} (row0 : Fin G → Bool → ℕ)
    (selHot : QRegister G k_ctrl) (subIdx : Fin k_ctrl) {c : Fin (2 ^ k_ctrl)}
    (h : AtMostOneHotBits (ctrlHotBits selHot c)) :
    bilinearApexEffK row0 selHot subIdx 0 c = 0 := by
  dsimp only [bilinearApexEffK]
  rw [bilinearRowLo_zero_of_atMostOneHot _ _ _ h,
    bilinearRowBit_zero_of_atMostOneHot _ _ _ h,
    bilinearRowBit_zero_of_atMostOneHot _ _ _ h,
    zmod2_val_zero]
  simp

theorem bilinearApexEffK_one_of_isOneHot {k_ctrl G : ℕ} (row0 : Fin G → Bool → ℕ)
    (selHot : QRegister G k_ctrl) (subIdx : Fin k_ctrl)
    {g₀ : Fin G} {c : Fin (2 ^ k_ctrl)}
    (h : IsOneHotBits g₀ (ctrlHotBits selHot c))
    (hlo : 2048 ≤ row0 g₀ (decide (basisBits k_ctrl c subIdx = 1)))
    (hhi : row0 g₀ (decide (basisBits k_ctrl c subIdx = 1)) < 6144) :
    bilinearApexEffK row0 selHot subIdx 1 c =
      row0 g₀ (decide (basisBits k_ctrl c subIdx = 1)) := by
  dsimp only [bilinearApexEffK]
  have hv1 : (1 : ZMod 2).val = 1 := rfl
  rw [bilinearRowLo_one_of_isOneHot _ _ _ h,
    bilinearRowBit_one_of_isOneHot _ _ _ h,
    bilinearRowBit_one_of_isOneHot _ _ _ h, hv1]
  exact nat_decomp_apex hlo hhi

/-- Family 2 (`Lac = 2`) Active-1 cascade unitary specification (`2 * (N - 2) * 102 + 94` `T`). -/
noncomputable def unsignedBilinearLac2CascadeActiveUnitary {N k_ctrl G : ℕ} (hN : 1 < N)
    (table : Fin G → Bool → Fin N → ℕ)
    (selHot : QRegister G k_ctrl) (subIdx : Fin k_ctrl) (c : Fin (2 ^ k_ctrl)) :
    Unitary (2 ^ N) :=
  let z0 : Fin N := ⟨0, by omega⟩
  let α_plane : ZMod 2 → ℕ → ℝ := fun b₁ p =>
    if hp : p + 1 < N then
      2 * Real.pi *
        (bilinearPlaneEffK (fun g b => table g b ⟨p, by omega⟩) selHot subIdx b₁ c : ℝ) /
        (2 : ℝ) ^ 14
    else 0
  let α₀_apex := 2 * Real.pi *
    (bilinearApexEffK (fun g b => table g b ⟨0, by omega⟩) selHot subIdx 0 c : ℝ) /
    (2 : ℝ) ^ 13
  let α₁_apex := 2 * Real.pi *
    (bilinearApexEffK (fun g b => table g b ⟨0, by omega⟩) selHot subIdx 1 c : ℝ) /
    (2 : ℝ) ^ 13
  let U_tail := genTailUnitary N (α_plane 0) (α_plane 1) (N - 2) (by omega)
  let U_apex := (QRegister.singleton z0).embedUnitary Qubit.Z *
    (GivensOps.pairAdj N 0 hN).embedUnitary (genGivensPosUnitary α₀_apex α₁_apex)
  U_tail⁻¹ * U_apex * U_tail

/-- Family 2 (`Lac = 2`) wire-controlled cascade unitary (`2 * (N - 2) * 102 + 98` `T`). -/
noncomputable def unsignedBilinearLac2CascadeCtrlUnitary {N k_ctrl G : ℕ} (hN : 1 < N)
    (table : Fin G → Bool → Fin N → ℕ)
    (actIdx : Fin k_ctrl) (selHot : QRegister G k_ctrl) (subIdx : Fin k_ctrl)
    (c : Fin (2 ^ k_ctrl)) : Unitary (2 ^ N) :=
  let z0 : Fin N := ⟨0, by omega⟩
  let act := basisBits k_ctrl c actIdx
  let α_plane : ZMod 2 → ℕ → ℝ := fun b₁ p =>
    if hp : p + 1 < N then
      2 * Real.pi *
        (bilinearPlaneEffK (fun g b => table g b ⟨p, by omega⟩) selHot subIdx b₁ c : ℝ) /
        (2 : ℝ) ^ 14
    else 0
  let α₀_apex := 2 * Real.pi *
    (bilinearApexEffK (fun g b => table g b ⟨0, by omega⟩) selHot subIdx (act * 0) c : ℝ) /
    (2 : ℝ) ^ 13
  let α₁_apex := 2 * Real.pi *
    (bilinearApexEffK (fun g b => table g b ⟨0, by omega⟩) selHot subIdx (act * 1) c : ℝ) /
    (2 : ℝ) ^ 13
  let U_tail := genTailUnitary N (α_plane 0) (α_plane 1) (N - 2) (by omega)
  let U_apex := (if act = 0 then 1 else (QRegister.singleton z0).embedUnitary Qubit.Z) *
    (GivensOps.pairAdj N 0 hN).embedUnitary (genGivensPosUnitary α₀_apex α₁_apex)
  U_tail⁻¹ * U_apex * U_tail

/-- Fiber evaluation when `act = 0` and `AtMostOneHotBits (ctrlHotBits selHot c)`:
the entire `Lac = 2` wire-controlled cascade cancels identically to `1`! -/
theorem unsignedBilinearLac2CascadeCtrlUnitary_eq_one_of_act_zero
    {N k_ctrl G : ℕ} (hN : 1 < N)
    (table : Fin G → Bool → Fin N → ℕ)
    (actIdx : Fin k_ctrl) (selHot : QRegister G k_ctrl) (subIdx : Fin k_ctrl)
    {c : Fin (2 ^ k_ctrl)}
    (hact0 : basisBits k_ctrl c actIdx = 0)
    (hatmost : AtMostOneHotBits (ctrlHotBits selHot c)) :
    unsignedBilinearLac2CascadeCtrlUnitary hN table actIdx selHot subIdx c = 1 := by
  dsimp only [unsignedBilinearLac2CascadeCtrlUnitary]
  have h0_eff : bilinearApexEffK (fun g b => table g b ⟨0, by omega⟩) selHot subIdx 0 c = 0 :=
    bilinearApexEffK_zero_of_atMostOneHot _ selHot subIdx hatmost
  have hα0 : 2 * Real.pi *
      (bilinearApexEffK (fun g b => table g b ⟨0, by omega⟩) selHot subIdx
        (basisBits k_ctrl c actIdx * 0) c : ℝ) / (2 : ℝ) ^ 13 = 0 := by
    rw [hact0, zero_mul, h0_eff, Nat.cast_zero, mul_zero, zero_div]
  have hα1 : 2 * Real.pi *
      (bilinearApexEffK (fun g b => table g b ⟨0, by omega⟩) selHot subIdx
        (basisBits k_ctrl c actIdx * 1) c : ℝ) / (2 : ℝ) ^ 13 = 0 := by
    rw [hact0, zero_mul, h0_eff, Nat.cast_zero, mul_zero, zero_div]
  rw [ite_eq_left_of_eq_true _ _ (eq_true hact0), hα0, hα1,
    genGivensPosUnitary_zero_zero, embedUnitary_one_eq, one_mul, mul_one, inv_mul_cancel]

/-- Fiber evaluation of `unsignedBilinearLac2CascadeActiveUnitary` on a one-hot control state
`g₀`. -/
theorem unsignedBilinearLac2CascadeActiveUnitary_eq_singleSpinReflection
    {N k_ctrl G : ℕ} (hN : 1 < N)
    (table : Fin G → Bool → Fin N → ℕ)
    (selHot : QRegister G k_ctrl) (subIdx : Fin k_ctrl)
    {g₀ : Fin G} {c : Fin (2 ^ k_ctrl)}
    (hoh : IsOneHotBits g₀ (ctrlHotBits selHot c))
    (hlt : ∀ (p : ℕ) (hp : p + 1 < N),
      table g₀ (decide (basisBits k_ctrl c subIdx = 1)) ⟨p, by omega⟩ < 8192)
    (hlo0 : 2048 ≤ table g₀ (decide (basisBits k_ctrl c subIdx = 1)) ⟨0, by omega⟩)
    (hhi0 : table g₀ (decide (basisBits k_ctrl c subIdx = 1)) ⟨0, by omega⟩ < 6144) :
    let b_sel := decide (basisBits k_ctrl c subIdx = 1)
    let k : Fin N → ℤ := fun j => (table g₀ b_sel j : ℤ)
    unsignedBilinearLac2CascadeActiveUnitary hN table selHot subIdx c =
      singleSpinReflectionUnitary N hN 15 k := by
  intro b_sel k
  dsimp only [unsignedBilinearLac2CascadeActiveUnitary, singleSpinReflectionUnitary]
  have hatmost := hoh.atMostOneHot
  have htail : genTailUnitary N
      (fun p => if hp : p + 1 < N then
        2 * Real.pi *
          (bilinearPlaneEffK (fun g b => table g b ⟨p, by omega⟩) selHot subIdx 0 c : ℝ) /
          (2 : ℝ) ^ 14 else 0)
      (fun p => if hp : p + 1 < N then
        2 * Real.pi *
          (bilinearPlaneEffK (fun g b => table g b ⟨p, by omega⟩) selHot subIdx 1 c : ℝ) /
          (2 : ℝ) ^ 14 else 0)
      (N - 2) (by omega) =
      GivensOps.givensCascadeTail N (GivensOps.givensLeafAngle N 15 k) (N - 2) (by omega) := by
    apply genTailUnitary_eq_givensCascadeTail
    · intro p _ hpt
      have hp : p + 1 < N := by omega
      simp only [hp, ↓reduceDIte,
        bilinearPlaneEffK_zero_of_atMostOneHot (fun g b => table g b ⟨p, by omega⟩) selHot subIdx
          hatmost,
        Nat.cast_zero, mul_zero, zero_div]
    · intro p _ hpt
      have hp : p + 1 < N := by omega
      simp only [hp, ↓reduceDIte]
      rw [bilinearPlaneEffK_one_of_isOneHot (fun g b => table g b ⟨p, by omega⟩) selHot subIdx hoh
        (hlt p hp)]
      exact angle_13bit_eq_givensLeafAngle k p (by omega) _ rfl
  have hapex0 : 2 * Real.pi *
      (bilinearApexEffK (fun g b => table g b ⟨0, by omega⟩) selHot subIdx 0 c : ℝ) /
      (2 : ℝ) ^ 13 = 0 := by
    rw [bilinearApexEffK_zero_of_atMostOneHot _ selHot subIdx hatmost,
      Nat.cast_zero, mul_zero, zero_div]
  have hapex1 : 2 * Real.pi *
      (bilinearApexEffK (fun g b => table g b ⟨0, by omega⟩) selHot subIdx 1 c : ℝ) /
      (2 : ℝ) ^ 13 = 2 * GivensOps.givensLeafAngle N 15 k 0 := by
    rw [bilinearApexEffK_one_of_isOneHot _ selHot subIdx hoh hlo0 hhi0]
    exact angle_apex_eq_two_mul_givensLeafAngle hN k _ rfl
  rw [htail, hapex0, hapex1, genGivensPosUnitary_zero_left]
  rfl

/-- Fiber evaluation of `unsignedBilinearLac2CascadeCtrlUnitary` when `act = 1` and
`IsOneHotBits g₀`. -/
theorem unsignedBilinearLac2CascadeCtrlUnitary_eq_singleSpinReflection
    {N k_ctrl G : ℕ} (hN : 1 < N)
    (table : Fin G → Bool → Fin N → ℕ)
    (actIdx : Fin k_ctrl) (selHot : QRegister G k_ctrl) (subIdx : Fin k_ctrl)
    {g₀ : Fin G} {c : Fin (2 ^ k_ctrl)}
    (hact1 : basisBits k_ctrl c actIdx = 1)
    (hoh : IsOneHotBits g₀ (ctrlHotBits selHot c))
    (hlt : ∀ (p : ℕ) (hp : p + 1 < N),
      table g₀ (decide (basisBits k_ctrl c subIdx = 1)) ⟨p, by omega⟩ < 8192)
    (hlo0 : 2048 ≤ table g₀ (decide (basisBits k_ctrl c subIdx = 1)) ⟨0, by omega⟩)
    (hhi0 : table g₀ (decide (basisBits k_ctrl c subIdx = 1)) ⟨0, by omega⟩ < 6144) :
    let b_sel := decide (basisBits k_ctrl c subIdx = 1)
    let k : Fin N → ℤ := fun j => (table g₀ b_sel j : ℤ)
    unsignedBilinearLac2CascadeCtrlUnitary hN table actIdx selHot subIdx c =
      singleSpinReflectionUnitary N hN 15 k := by
  have h10 : (1 : ZMod 2) ≠ 0 := by decide
  have heq : unsignedBilinearLac2CascadeCtrlUnitary hN table actIdx selHot subIdx c =
      unsignedBilinearLac2CascadeActiveUnitary hN table selHot subIdx c := by
    dsimp only [unsignedBilinearLac2CascadeCtrlUnitary, unsignedBilinearLac2CascadeActiveUnitary]
    rw [hact1, mul_zero, mul_one, ite_eq_right_of_eq_false _ _ (eq_false h10)]
  rw [heq]
  exact unsignedBilinearLac2CascadeActiveUnitary_eq_singleSpinReflection hN table selHot subIdx
    hoh hlt hlo0 hhi0

/-! ### 3. Certified P450 DFTHC `Lac = 2` Angle Tables (`G = 131`, `G = 29`, `G = 160`) -/

/-- Raw leaf entry `μ < 261`, padded with `0` at unused index `j = 57`. -/
def p450LeafEntry (μ : ℕ) (j : Fin 58) : ℕ :=
  if j.val < 57 then (DataArrays.leafAngleTableArr.getD μ #[]).getD j.val 0 else 0

/-- Raw one-body entry `ℓ < 58`, padded with `0` at unused index `j = 57`. -/
def p450OneBodyEntry (ℓ : ℕ) (j : Fin 58) : ℕ :=
  if j.val < 57 then (DataArrays.oneBodyAngleTableArr.getD ℓ #[]).getD j.val 0 else 0

theorem p450LeafEntry_bounds {μ : ℕ} (hμ : μ < 261) :
    (∀ (p : ℕ) (hp : p + 1 < 58), p450LeafEntry μ ⟨p, by omega⟩ < 8192) ∧
    2048 ≤ p450LeafEntry μ ⟨0, by omega⟩ ∧
    p450LeafEntry μ ⟨0, by omega⟩ < 6144 := by
  have hc := dfthc_leafAngleTable_bounds
  refine ⟨fun p hp => ?_, ?_, ?_⟩
  · have hp57 : p < 57 := by omega
    simp only [p450LeafEntry, hp57, ↓reduceIte]
    exact hc.2.2.1 μ hμ p hp57
  · simp only [p450LeafEntry, show (0 : ℕ) < 57 by omega, ↓reduceIte]
    exact (hc.2.2.2 μ hμ).1
  · simp only [p450LeafEntry, show (0 : ℕ) < 57 by omega, ↓reduceIte]
    exact (hc.2.2.2 μ hμ).2

theorem p450OneBodyEntry_bounds {ℓ : ℕ} (hℓ : ℓ < 58) :
    (∀ (p : ℕ) (hp : p + 1 < 58), p450OneBodyEntry ℓ ⟨p, by omega⟩ < 8192) ∧
    2048 ≤ p450OneBodyEntry ℓ ⟨0, by omega⟩ ∧
    p450OneBodyEntry ℓ ⟨0, by omega⟩ < 6144 := by
  have hc := dfthc_oneBodyAngleTable_bounds
  refine ⟨fun p hp => ?_, ?_, ?_⟩
  · have hp57 : p < 57 := by omega
    simp only [p450OneBodyEntry, hp57, ↓reduceIte]
    exact hc.2.2.1 ℓ hℓ p hp57
  · simp only [p450OneBodyEntry, show (0 : ℕ) < 57 by omega, ↓reduceIte]
    exact (hc.2.2.2 ℓ hℓ).1
  · simp only [p450OneBodyEntry, show (0 : ℕ) < 57 by omega, ↓reduceIte]
    exact (hc.2.2.2 ℓ hℓ).2

/-- Two-body `261`-leaf `Lac = 2` table (`G = 131` pairs; unused `(130, true)` clamped to leaf
`260`). -/
def p450LeafLac2Table (g : Fin 131) (b : Bool) (j : Fin 58) : ℕ :=
  let μ := 2 * g.val + (if b then 1 else 0)
  p450LeafEntry (if μ < 261 then μ else 260) j

/-- One-body `58`-orbital `Lac = 2` table (`G = 29` pairs). -/
def p450OneBodyLac2Table (g : Fin 29) (b : Bool) (j : Fin 58) : ℕ :=
  p450OneBodyEntry (2 * g.val + (if b then 1 else 0)) j

/-- Split `29 + 131 = 160`-pair `Lac = 2` table (`g < 29` one-body, `29 ≤ g` two-body leaves). -/
def p450Split160Lac2Table (g : Fin 160) (b : Bool) (j : Fin 58) : ℕ :=
  if hg : g.val < 29 then p450OneBodyLac2Table ⟨g.val, hg⟩ b j
  else p450LeafLac2Table ⟨g.val - 29, by omega⟩ b j

theorem p450LeafLac2Table_bounds (g : Fin 131) (b : Bool) :
    (∀ (p : ℕ) (hp : p + 1 < 58), p450LeafLac2Table g b ⟨p, by omega⟩ < 8192) ∧
    2048 ≤ p450LeafLac2Table g b ⟨0, by omega⟩ ∧
    p450LeafLac2Table g b ⟨0, by omega⟩ < 6144 := by
  unfold p450LeafLac2Table
  dsimp only
  set μ := 2 * g.val + (if b then 1 else 0)
  by_cases h1 : μ < 261
  · simp only [h1, ↓reduceIte]
    exact p450LeafEntry_bounds h1
  · simp only [h1, ↓reduceIte]
    exact p450LeafEntry_bounds (by omega)

theorem p450OneBodyLac2Table_bounds (g : Fin 29) (b : Bool) :
    (∀ (p : ℕ) (hp : p + 1 < 58), p450OneBodyLac2Table g b ⟨p, by omega⟩ < 8192) ∧
    2048 ≤ p450OneBodyLac2Table g b ⟨0, by omega⟩ ∧
    p450OneBodyLac2Table g b ⟨0, by omega⟩ < 6144 := by
  unfold p450OneBodyLac2Table
  exact p450OneBodyEntry_bounds (by have := g.isLt; cases b <;> simp <;> omega)

theorem p450Split160Lac2Table_bounds (g : Fin 160) (b : Bool) :
    (∀ (p : ℕ) (hp : p + 1 < 58), p450Split160Lac2Table g b ⟨p, by omega⟩ < 8192) ∧
    2048 ≤ p450Split160Lac2Table g b ⟨0, by omega⟩ ∧
    p450Split160Lac2Table g b ⟨0, by omega⟩ < 6144 := by
  unfold p450Split160Lac2Table
  by_cases hg : g.val < 29
  · simp only [hg, ↓reduceDIte]
    exact p450OneBodyLac2Table_bounds ⟨g.val, hg⟩ b
  · simp only [hg, ↓reduceDIte]
    exact p450LeafLac2Table_bounds ⟨g.val - 29, by omega⟩ b

theorem p450LeafLac2Table_eq_leafEntry {μ : ℕ} (hμ : μ < 261) (j : Fin 58) :
    p450LeafLac2Table ⟨μ / 2, by omega⟩ (decide (μ % 2 = 1)) j = p450LeafEntry μ j := by
  unfold p450LeafLac2Table
  dsimp only
  have hrec : 2 * (μ / 2) + (if decide (μ % 2 = 1) then 1 else 0) = μ := by
    rcases Nat.mod_two_eq_zero_or_one μ with h | h <;> simp [h] <;> omega
  simp only [hrec, hμ, ↓reduceIte]

theorem p450OneBodyLac2Table_eq_oneBodyEntry {ℓ : ℕ} (hℓ : ℓ < 58) (j : Fin 58) :
    p450OneBodyLac2Table ⟨ℓ / 2, by omega⟩ (decide (ℓ % 2 = 1)) j = p450OneBodyEntry ℓ j := by
  unfold p450OneBodyLac2Table
  dsimp only
  have hrec : 2 * (ℓ / 2) + (if decide (ℓ % 2 = 1) then 1 else 0) = ℓ := by
    rcases Nat.mod_two_eq_zero_or_one ℓ with h | h <;> simp [h] <;> omega
  rw [hrec]

end BilinearLac2

end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.CircuitModular.UnsignedGivens

end
