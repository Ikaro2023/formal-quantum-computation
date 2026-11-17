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

public import QuantumComputation.Circuits.Toffoli
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.ModularDefs
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.CleanAncillaToffoli
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.CatalystCleanBridge
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.SeamAdapters
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.SpinSegregationGivens
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.GivensDataCerts
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.PhasedGivensBridge

/-!
# Raw Unsigned `13`-Bit Rank-2 Bilinear Givens & `94-T`/`98-T` Apex Engine
Zero-Toffoli (`TOFF = 0`) catalytic Givens plane and `57`-plane
cascade circuits plugging directly into `GivensOps.givensPlaneUnitary` and
`GivensOps.givensCascadeTail_conj_fusedApex` (`SpinSegregationGivens`):

- **Unified `(B + 2)`-Bit Raw Unsigned Phase-Kickback (`rawUnsignedPhaseKickDyn`)**:
  - Reads raw unsigned `13`-bit integers `k ∈ [0, 8192)` directly from `P450.leafAngleTable` and
    `P450.oneBodyAngleTable` (`GivensDataCerts`), with zero sign-magnitude table conversion,
    zero `s_curr` wire, and zero `Δ_s` wire.
  - Conjugates `rCat : QRegister B n` (`phaseGradientLowSlice B 3`) by `cnotFanoutReg B w_p rCat`
    around a `B`-bit in-place Gidney carry-out adder + `parityTCircuit c_B w_p` (`4 * B + 1` `T`,
    `B` carry wires), preceded by immediate compute-kick-uncompute of top bits `a_{B+1}` (`4 T`)
    and `a_B` (`5 T`) onto `rA 0` before loading `a_0 .. a_{B-1}` (`4 * B` `T`, `B` mask wires).
- **Exact Per-Plane Resource Counts (`0 TOFF`)**:
  - Rank-2 Bilinear `Lac = 2` general plane `p = 1..56` (`B = 11` on `rCat11`):
    **`102 T`**, **`23` clean scratch wires** (`wV + rA:11 + rC:11`), realizing both
    `GivensOps.givensPlaneUnitary (+φ)` (`negAngle = false`) and
    `GivensOps.givensPlaneUnitary (-φ)` (`negAngle = true`) at `102 T` cost.
  - Rank-2 Bilinear `Lac = 2` shifted apex `p = 0` (`B = 10` on `rCat11.slice 1 10`, using
    `apex_double_angle_decomp` `2 * k_0 = 4096 + 4096 b_{12} + 2048 b_{10} + 2 (k_0 % 1024)`):
    **`94 T`** (`active = 1`, `21` scratch wires) and **`98 T`** (wire-controlled `active`,
    `22` scratch wires).
  - Standalone quantum-angle-register (`rK : QRegister 13 n` / `12` apex wires):
    **`98 T`** general plane (`22` scratch wires), **`90 T`** active-1 apex (`20` scratch wires),
    and **`94 T`** wire-controlled apex (`21` scratch wires).
-/

@[expose] public section

namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.CircuitModular.UnsignedGivens
open QuantumComputation.Specs QuantumComputation.Specs.P450

open Operator QProg Matrix QuantumComputation.Specs Solution QuantumComputation.Specs.P450 Solution
open Solution.CircuitModular Solution.GivensOps
open scoped Matrix ComplexOrder MatrixOrder BigOperators Circuit.Notation

/-! ## Section 1: `cnotFanoutReg`, `regVal`, Binary Uniqueness & `carryAt` Arithmetic -/

section FanoutAndCarryArithmetic

variable {n : ℕ}

private theorem slice_one_apply_eq_succ' {B : ℕ} (r : QRegister (B + 1) n) (j : Fin B) :
    (r.slice 1 B (by omega)) j = r j.succ := by
  simp only [QRegister.slice_apply]
  congr 1; ext; dsimp [QRegister.block]; omega

/-- Fanout `CNOT` from `ctrl` to every wire of `rDst` (`0 T`, `0 TOFF`), computing one's-complement
`y ↦ (2^B - 1) - y` on `rDst` when `ctrl = 1` and identity when `ctrl = 0`. -/
def cnotFanoutReg : (B : ℕ) → (ctrl : Wire n) → (rDst : QRegister B n) →
    (hdisj : ∀ j, ctrl ≠ rDst j) → Circuit n
  | 0, _, _, _ => .identity
  | B + 1, ctrl, rDst, hdisj =>
      Circuit.CNOT ctrl (rDst 0) (hdisj 0) ;;ᶜ
        cnotFanoutReg B ctrl (rDst.slice 1 B (by omega))
          (fun j => by rw [slice_one_apply_eq_succ']; exact hdisj j.succ)

@[simp] theorem count_cnotFanoutReg_t (B : ℕ) (ctrl : Wire n) (rDst : QRegister B n)
    (hdisj : ∀ j, ctrl ≠ rDst j) :
    (cnotFanoutReg B ctrl rDst hdisj).count .T = 0 := by
  induction B with
  | zero => simp [cnotFanoutReg]
  | succ B ih => simp [cnotFanoutReg, ih]

@[simp] theorem count_cnotFanoutReg_toff (B : ℕ) (ctrl : Wire n) (rDst : QRegister B n)
    (hdisj : ∀ j, ctrl ≠ rDst j) :
    (cnotFanoutReg B ctrl rDst hdisj).count .TOFF = 0 := by
  induction B with
  | zero => simp [cnotFanoutReg]
  | succ B ih => simp [cnotFanoutReg, ih]

theorem evolve_cnotFanoutReg_ket (B : ℕ) (ctrl : Wire n)
    (rDst : QRegister B n) (hdisj : ∀ j, ctrl ≠ rDst j) (β : BitAssignment n) :
    (cnotFanoutReg B ctrl rDst hdisj).eval.1.mulVec (ket β) =
      ket (fun w => if w ∈ Set.range rDst.wires then β w + β ctrl else β w) := by
  induction B generalizing β with
  | zero =>
      rw [cnotFanoutReg, eval_identity_mulVec]
      apply congrArg ket; funext w
      have hnot : w ∉ Set.range rDst.wires := by rintro ⟨j, _⟩; exact Fin.elim0 j
      simp only [hnot, ↓reduceIte]
  | succ B ih =>
      let rRest := rDst.slice 1 B (by omega)
      rw [cnotFanoutReg, eval_seq_mulVec, evolve_CNOT_ket, ih rRest]
      apply congrArg ket; funext w
      have hctrl_eq : Function.update β (rDst 0) (β (rDst 0) + β ctrl) ctrl = β ctrl :=
        Function.update_of_ne (hdisj 0) _ _
      by_cases hw0 : w = rDst 0
      · subst hw0
        have hnot_rest : rDst 0 ∉ Set.range rRest.wires := by
          rintro ⟨j, hj⟩
          have hidx : rRest j = rDst j.succ := slice_one_apply_eq_succ' rDst j
          exact Fin.succ_ne_zero j (rDst.wires.injective (hidx.symm.trans hj))
        have hmem : rDst 0 ∈ Set.range rDst.wires := ⟨0, rfl⟩
        simp [hnot_rest, hmem]
      · by_cases hwr : w ∈ Set.range rRest.wires
        · obtain ⟨j, rfl⟩ := hwr
          have hmem : rRest j ∈ Set.range rDst.wires :=
            ⟨j.succ, (slice_one_apply_eq_succ' rDst j).symm⟩
          have hmem' : rRest j ∈ Set.range rRest.wires := ⟨j, rfl⟩
          have hw0' : rRest.wires j ≠ rDst.wires 0 := hw0
          simp only [hmem, hmem', ↓reduceIte]
          rw [Function.update_of_ne hw0', hctrl_eq]
        · have hnot_all : w ∉ Set.range rDst.wires := by
            rintro ⟨k, rfl⟩
            rcases Fin.eq_zero_or_eq_succ k with rfl | ⟨j, rfl⟩
            · exact hw0 rfl
            · exact hwr ⟨j, slice_one_apply_eq_succ' rDst j⟩
          have hw0' : w ≠ rDst.wires 0 := hw0
          simp only [hwr, hnot_all, ↓reduceIte]
          rw [Function.update_of_ne hw0']

/-- Little-endian natural-number value `∈ [0, 2^B)` held by `r` in basis state `β`. -/
noncomputable def regVal {B : ℕ} (r : QRegister B n) (β : BitAssignment n) : ℕ :=
  (localIdx r β).val

theorem regVal_lt {B : ℕ} (r : QRegister B n) (β : BitAssignment n) :
    regVal r β < 2 ^ B :=
  (localIdx r β).isLt

theorem zmod2_natCast_mod_two_val (x : ℕ) : ((x % 2 : ℕ) : ZMod 2).val = x % 2 := by
  rcases Nat.mod_two_eq_zero_or_one x with h | h <;> simp [h]

theorem zmod2_eq_natCast_mod_two (b : ZMod 2) : ((b.val : ℕ) : ZMod 2) = b := by
  rcases zmod2_eq_zero_or_one b with rfl | rfl <;> rfl

theorem regVal_div_pow_mod_two {B : ℕ} (r : QRegister B n) (β : BitAssignment n) (j : Fin B) :
    regVal r β / 2 ^ j.val % 2 = (β (r j)).val := by
  have hb := congrFun (basisBits_symm_eq (fun i => β (r i))) j
  dsimp only [regVal, localIdx]
  rw [basisBits_eq_div_mod] at hb
  have hv := congrArg ZMod.val hb
  simpa only [zmod2_natCast_mod_two_val] using hv

theorem reg_bit_eq_natCast_regVal {B : ℕ} (r : QRegister B n) (β : BitAssignment n) (j : Fin B) :
    β (r j) = ((regVal r β / 2 ^ j.val % 2 : ℕ) : ZMod 2) := by
  rw [regVal_div_pow_mod_two, zmod2_eq_natCast_mod_two]

theorem nat_eq_of_lt_two_pow_of_div_mod_eq :
    ∀ {B x y : ℕ}, x < 2 ^ B → y < 2 ^ B →
      (∀ j : Fin B, x / 2 ^ j.val % 2 = y / 2 ^ j.val % 2) → x = y
  | 0, x, y, hx, hy, _ => by simp at hx hy; omega
  | B + 1, x, y, hx, hy, hbits => by
      have h0 := hbits ⟨0, by omega⟩
      simp only [_root_.pow_zero, Nat.div_one] at h0
      have hdiv : x / 2 = y / 2 := by
        apply nat_eq_of_lt_two_pow_of_div_mod_eq (B := B)
        · rw [Nat.pow_succ] at hx; omega
        · rw [Nat.pow_succ] at hy; omega
        · intro j
          have hj := hbits j.succ
          simpa only [Fin.val_succ, pow_add, pow_one, mul_comm (2 ^ j.val) 2,
            ← Nat.div_div_eq_div_mul] using hj
      omega

theorem onesComp_div_pow_mod_two :
    ∀ {k B y : ℕ}, k < B → y < 2 ^ B →
      (2 ^ B - 1 - y) / 2 ^ k % 2 = 1 - y / 2 ^ k % 2
  | 0, B, y, hk, hy => by
      obtain ⟨d, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : B ≠ 0)
      simp only [_root_.pow_zero, Nat.div_one]
      have hpow : 2 ^ (d + 1) = 2 * 2 ^ d := by ring
      omega
  | k + 1, B, y, hk, hy => by
      obtain ⟨d, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : B ≠ 0)
      have hpow : 2 ^ (d + 1) = 2 * 2 ^ d := by ring
      have hdiv1 : (2 ^ (d + 1) - 1 - y) / 2 ^ (k + 1) = (2 ^ d - 1 - y / 2) / 2 ^ k := by
        rw [show 2 ^ (k + 1) = 2 * 2 ^ k by ring, ← Nat.div_div_eq_div_mul]
        congr 1
        omega
      have hdiv2 : y / 2 ^ (k + 1) = (y / 2) / 2 ^ k := by
        rw [show 2 ^ (k + 1) = 2 * 2 ^ k by ring, ← Nat.div_div_eq_div_mul]
      rw [hdiv1, hdiv2]
      exact onesComp_div_pow_mod_two (by omega) (by omega)

theorem regVal_after_fanout {B : ℕ} (r : QRegister B n) (β : BitAssignment n) (c : ZMod 2) :
    regVal r (fun w => if w ∈ Set.range r.wires then β w + c else β w) =
      if c = 0 then regVal r β else (2 ^ B - 1) - regVal r β := by
  let β' : BitAssignment n := fun w => if w ∈ Set.range r.wires then β w + c else β w
  rcases zmod2_eq_zero_or_one c with rfl | rfl
  · simp only [↓reduceIte]
    apply nat_eq_of_lt_two_pow_of_div_mod_eq (regVal_lt r β') (regVal_lt r β)
    intro j
    rw [regVal_div_pow_mod_two, regVal_div_pow_mod_two]
    simp [β']
  · have h10 : (1 : ZMod 2) ≠ 0 := by decide
    simp only [h10, ↓reduceIte]
    have hlt_comp : (2 ^ B - 1) - regVal r β < 2 ^ B := by
      have := Nat.two_pow_pos B; omega
    apply nat_eq_of_lt_two_pow_of_div_mod_eq (regVal_lt r β') hlt_comp
    intro j
    rw [regVal_div_pow_mod_two, onesComp_div_pow_mod_two j.isLt (regVal_lt r β),
      regVal_div_pow_mod_two]
    have hflip : ∀ b : ZMod 2, (b + 1).val = 1 - b.val := by
      intro b; rcases zmod2_eq_zero_or_one b with rfl | rfl <;> decide
    simpa [β'] using hflip (β (r j))

/-- Closed-form ripple carry `(yc % 2^k + a % 2^k) / 2^k ∈ {0, 1}` at bit position `k`. -/
def carryAt (yc a k : ℕ) : ℕ :=
  (yc % 2 ^ k + a % 2 ^ k) / 2 ^ k

@[simp] theorem carryAt_zero (yc a : ℕ) : carryAt yc a 0 = 0 := by
  unfold carryAt; omega

theorem carryAt_lt_two (yc a k : ℕ) : carryAt yc a k < 2 := by
  unfold carryAt
  have h1 : yc % 2 ^ k < 2 ^ k := Nat.mod_lt _ (Nat.two_pow_pos k)
  have h2 : a % 2 ^ k < 2 ^ k := Nat.mod_lt _ (Nat.two_pow_pos k)
  have hsum : yc % 2 ^ k + a % 2 ^ k < 2 ^ k * 2 := by omega
  exact Nat.div_lt_of_lt_mul hsum

theorem carryAt_of_lt {B yc a : ℕ} (hyc : yc < 2 ^ B) (ha : a < 2 ^ B) :
    carryAt yc a B = (yc + a) / 2 ^ B := by
  simp [carryAt, Nat.mod_eq_of_lt hyc, Nat.mod_eq_of_lt ha]

private theorem mod_pow_succ_eq (x k : ℕ) :
    x % 2 ^ (k + 1) = x % 2 ^ k + 2 ^ k * (x / 2 ^ k % 2) := by
  have h1 := Nat.mod_add_div (x % 2 ^ (k + 1)) (2 ^ k)
  have hmod : (x % 2 ^ (k + 1)) % 2 ^ k = x % 2 ^ k := by
    rw [pow_succ, Nat.mod_mul_right_mod]
  have hdiv : (x % 2 ^ (k + 1)) / 2 ^ k = x / 2 ^ k % 2 := by
    rw [pow_succ, Nat.mod_mul_right_div_self]
  rw [← h1, hmod, hdiv]

theorem carryAt_succ (yc a k : ℕ) :
    carryAt yc a (k + 1) = (carryAt yc a k + yc / 2 ^ k % 2 + a / 2 ^ k % 2) / 2 := by
  unfold carryAt
  rw [mod_pow_succ_eq yc k, mod_pow_succ_eq a k, pow_succ, ← Nat.div_div_eq_div_mul]
  congr 1
  have hpos : 0 < 2 ^ k := Nat.two_pow_pos k
  have hsum :
      yc % 2 ^ k + 2 ^ k * (yc / 2 ^ k % 2) + (a % 2 ^ k + 2 ^ k * (a / 2 ^ k % 2)) =
      (yc % 2 ^ k + a % 2 ^ k) + 2 ^ k * (yc / 2 ^ k % 2 + a / 2 ^ k % 2) := by ring
  rw [hsum, Nat.add_mul_div_left _ _ hpos]
  omega

theorem add_div_pow_mod_two (yc a k : ℕ) :
    (yc + a) / 2 ^ k % 2 = (carryAt yc a k + yc / 2 ^ k % 2 + a / 2 ^ k % 2) % 2 := by
  have hy := Nat.mod_add_div yc (2 ^ k)
  have ha := Nat.mod_add_div a (2 ^ k)
  have hpos : 0 < 2 ^ k := Nat.two_pow_pos k
  have hsum : yc + a = (yc % 2 ^ k + a % 2 ^ k) + 2 ^ k * (yc / 2 ^ k + a / 2 ^ k) := by
    linarith
  have hdiv : (yc + a) / 2 ^ k = carryAt yc a k + (yc / 2 ^ k + a / 2 ^ k) := by
    rw [hsum, Nat.add_mul_div_left _ _ hpos]; rfl
  rw [hdiv]
  omega

theorem gidney_maj_zmod2 {cy by_ ba : ℕ} (hcy : cy < 2) (hby : by_ < 2) (hba : ba < 2) :
    let cz : ZMod 2 := (cy : ZMod 2)
    let yz : ZMod 2 := (by_ : ZMod 2)
    let az : ZMod 2 := (ba : ZMod 2)
    cz + (yz + cz) * (az + cz) = (((cy + by_ + ba) / 2 : ℕ) : ZMod 2) := by
  rcases (by omega : cy = 0 ∨ cy = 1) with rfl | rfl <;>
    rcases (by omega : by_ = 0 ∨ by_ = 1) with rfl | rfl <;>
    rcases (by omega : ba = 0 ∨ ba = 1) with rfl | rfl <;>
    decide

theorem gidney_sum_zmod2 (cy by_ ba : ℕ) :
    let cz : ZMod 2 := (cy : ZMod 2)
    let yz : ZMod 2 := (by_ : ZMod 2)
    let az : ZMod 2 := (ba : ZMod 2)
    (yz + cz) + az = (((cy + by_ + ba) % 2 : ℕ) : ZMod 2) := by
  intro cz yz az
  have hcast : (((cy + by_ + ba) % 2 : ℕ) : ZMod 2) = ((cy + by_ + ba : ℕ) : ZMod 2) := by
    rw [← ZMod.natCast_mod (cy + by_ + ba) 2]
  rw [hcast]
  push_cast
  ring

end FanoutAndCarryArithmetic

/-! ## Section 2: `B`-Bit In-Place Carry-Out Gidney Adder + `parityTCircuit` Kickback (`4 * B + 1`
  `T`) -/

section GidneyCarryOutAdder

variable {Var : Type} {n : ℕ}

namespace GidneyKickDisjoint

variable {B : ℕ} {rCat rA rC : QRegister B n} {w_p : Wire n}

theorem ne_C_C (rC : QRegister B n) {i j : Fin B} (hij : i ≠ j) : rC i ≠ rC j :=
  fun heq => hij (rC.wires.injective heq)

end GidneyKickDisjoint

end GidneyCarryOutAdder

/-! ## Section 3: Parametric Clean Bit-Loaders & Unified `(B + 2)`-Bit Raw Unsigned Phase Kickback
-/

section RawUnsignedPhaseKick

variable {Var : Type} {n : ℕ}

/-- Specification that `s : PhasedStep n` cleanly computes `bitVal β : ZMod 2` onto `s.anc`,
touching only `insert s.anc S_ctrl`, and restores every wire on exit. -/
structure IsCleanBitStep (s : PhasedStep n) (bitVal : BitAssignment n → ZMod 2)
    (S_ctrl : Finset (Wire n)) : Prop where
  clifford : s.IsCliffordWrapper
  anc_not_mem_ctrl : s.anc ∉ S_ctrl
  anc_not_mem_pre : s.anc ∉ s.pre.support
  pre_sub : s.pre.support ⊆ S_ctrl
  c1_mem : s.c₁ ∈ S_ctrl
  c2_mem : s.c₂ ∈ S_ctrl
  midPre_sub : s.midPre.support ⊆ insert s.anc S_ctrl
  pre_mid_perm : PhasedPerm
    (s.pre ;;ᶜ Circuit.TOFF s.c₁ s.c₂ s.anc s.h₁₂ s.h₁a s.h₂a ;;ᶜ s.midPre)
    (fun _ => 1)
    (fun β => Function.update β s.anc (β s.anc + bitVal β))
  mid_post_inv : ∀ β : BitAssignment n,
    (s.midPost ;;ᶜ Circuit.TOFF s.c₁ s.c₂ s.anc s.h₁₂ s.h₁a s.h₂a ;;ᶜ s.post).eval.1.mulVec
      (ket β) = ket (Function.update β s.anc (β s.anc + bitVal β))
  bitVal_congr : ∀ β₁ β₂ : BitAssignment n, (∀ w ∈ S_ctrl, β₁ w = β₂ w) → bitVal β₁ = bitVal β₂
  body_perm : ∀ (c_in : Circuit n) (φ_in : BitAssignment n → ℂ)
      (f_in : BitAssignment n → BitAssignment n),
    PhasedPerm c_in φ_in f_in →
    (∀ β, f_in β s.anc = β s.anc) →
    (∀ β w, w ∈ S_ctrl → f_in β w = β w) →
    ∃ φ_b f_b, PhasedPerm (s.midPre ;;ᶜ c_in ;;ᶜ s.midPost) φ_b f_b ∧
      (∀ β, f_b β s.c₁ = β s.c₁) ∧
      (∀ β, f_b β s.c₂ = β s.c₂) ∧
      (∀ β, f_b β s.anc = β s.anc)

/-- Standalone `directBitStep (ctrl src anc)` (`4 T`, `0 TOFF`), loading `β ctrl * β src` onto
  `anc`. -/
def directBitStep (ctrl src anc : Wire n)
    (hcs : ctrl ≠ src) (hca : ctrl ≠ anc) (hsa : src ≠ anc) : PhasedStep n where
  c₁ := ctrl
  c₂ := src
  anc := anc
  h₁₂ := hcs
  h₁a := hca
  h₂a := hsa
  pre := .identity
  midPre := .identity
  midPost := .identity
  post := .identity

theorem isCleanBitStep_directBitStep (ctrl src anc : Wire n)
    (hcs : ctrl ≠ src) (hca : ctrl ≠ anc) (hsa : src ≠ anc) :
    IsCleanBitStep (directBitStep ctrl src anc hcs hca hsa)
      (fun β => β ctrl * β src) ({ctrl, src} : Finset (Wire n)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [directBitStep, PhasedStep.IsCliffordWrapper]
  · simp [directBitStep, hca.symm, hsa.symm]
  · simp [directBitStep]
  · simp [directBitStep]
  · simp [directBitStep]
  · simp [directBitStep]
  · simp [directBitStep]
  · intro β
    let s := directBitStep ctrl src anc hcs hca hsa
    have hpre : s.pre = .identity := rfl
    have hmidPre : s.midPre = .identity := rfl
    simp only [eval_seq_mulVec, one_smul]
    change s.midPre.eval.1.mulVec
        ((Circuit.TOFF s.c₁ s.c₂ s.anc s.h₁₂ s.h₁a s.h₂a).eval.1.mulVec
          (s.pre.eval.1.mulVec (ket β))) = _
    simp only [hpre, hmidPre, eval_identity_mulVec]
    rw [evolve_TOFF_ket]
    rfl
  · intro β
    let s := directBitStep ctrl src anc hcs hca hsa
    have hmidPost : s.midPost = .identity := rfl
    have hpost : s.post = .identity := rfl
    simp only [eval_seq_mulVec]
    change s.post.eval.1.mulVec
        ((Circuit.TOFF s.c₁ s.c₂ s.anc s.h₁₂ s.h₁a s.h₂a).eval.1.mulVec
          (s.midPost.eval.1.mulVec (ket β))) = _
    simp only [hmidPost, hpost, eval_identity_mulVec]
    rw [evolve_TOFF_ket]
    rfl
  · intro β₁ β₂ h; rw [h ctrl (by simp), h src (by simp)]
  · intro c_in φ_in f_in hperm hfa hfc
    refine ⟨φ_in, f_in, ?_, ?_, ?_, hfa⟩
    · intro β
      dsimp only [directBitStep]
      simp only [eval_seq_mulVec, eval_identity_mulVec]
      exact hperm β
    · intro β; exact hfc β ctrl (by simp)
    · intro β; exact hfc β src (by simp)

/-- Universal composition lemma for `IsCleanBitStep`: wrapping any `PhasedPerm` circuit `c_in` that
fixes `s.anc` and `S_ctrl` produces a `PhasedPerm` circuit fixing `s.anc` and `S_ctrl` and
evaluating
`c_in` on `Function.update β s.anc (β s.anc + bitVal β)`, while preserving zero-ancilla QHL. -/
theorem cleanBitStep_wrap_spec
    {s : PhasedStep n} {bitVal : BitAssignment n → ZMod 2} {S_ctrl : Finset (Wire n)}
    (hs : IsCleanBitStep s bitVal S_ctrl)
    {c_in : Circuit n} {φ_in : BitAssignment n → ℂ} {f_in : BitAssignment n → BitAssignment n}
    (hperm_in : PhasedPerm c_in φ_in f_in)
    (hfix_anc : ∀ β, f_in β s.anc = β s.anc)
    (hfix_ctrl : ∀ β w, w ∈ S_ctrl → f_in β w = β w) :
    let φ_out : BitAssignment n → ℂ :=
      fun β => φ_in (Function.update β s.anc (β s.anc + bitVal β))
    let f_out : BitAssignment n → BitAssignment n :=
      fun β => Function.update (f_in (Function.update β s.anc (β s.anc + bitVal β))) s.anc (β s.anc)
    PhasedPerm (s.wrapCircuit c_in) φ_out f_out ∧
    (∀ β, f_out β s.anc = β s.anc) ∧
    (∀ β w, w ∈ S_ctrl → f_out β w = β w) ∧
    (let P₀ := (QRegister.singleton s.anc).basisOutcomeProjector 0
     let T_anc := (Circuit.TOFF s.c₁ s.c₂ s.anc s.h₁₂ s.h₁a s.h₂a).eval.1
     P₀ * (T_anc * (s.midPre ;;ᶜ c_in ;;ᶜ s.midPost).eval.1 * T_anc * P₀) =
       T_anc * (s.midPre ;;ᶜ c_in ;;ᶜ s.midPost).eval.1 * T_anc * P₀) := by
  intro φ_out f_out
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro β
    let β₁ := Function.update β s.anc (β s.anc + bitVal β)
    have hstep1 := hs.pre_mid_perm β
    have hstep3 := hs.mid_post_inv (f_in β₁)
    dsimp only [PhasedStep.wrapCircuit]
    simp only [eval_seq_mulVec, one_smul] at hstep1 hstep3 ⊢
    rw [hstep1, hperm_in β₁]
    simp only [Matrix.mulVec_smul]
    rw [hstep3]
    congr 1
    apply congrArg ket
    have hbv : bitVal (f_in β₁) = bitVal β := by
      apply hs.bitVal_congr
      intro w hw
      rw [hfix_ctrl β₁ w hw]
      exact Function.update_of_ne (by rintro rfl; exact hs.anc_not_mem_ctrl hw) _ _
    rw [hbv, hfix_anc β₁]
    dsimp [β₁, f_out]
    rw [Function.update_self, zmod2_add_cancel_right]
  · intro β; dsimp [f_out]; exact Function.update_self _ _ _
  · intro β w hw
    dsimp [f_out]
    have hne : w ≠ s.anc := by rintro rfl; exact hs.anc_not_mem_ctrl hw
    rw [Function.update_of_ne hne, hfix_ctrl _ w hw, Function.update_of_ne hne]
  · obtain ⟨φ_b, f_b, hpb, hc1, hc2, hca⟩ := hs.body_perm c_in φ_in f_in hperm_in hfix_anc hfix_ctrl
    exact toffoli_conj_preserves_zero_ancilla_of_phasedPerm s.c₁ s.c₂ s.anc s.h₁₂ s.h₁a s.h₂a
      _ _ _ hpb hc1 hc2 hca

end RawUnsignedPhaseKick

/-! ## Section 3b: `RealizesCleanRef`, `rawUnsignedPhaseKickRef_spec` & `phaseGradientFineLow`
  Bridge -/

section RawUnsignedPhaseKickBridge

variable {Var : Type} {n : ℕ}

/-- Clean-workspace reference-circuit bridge:
1. `c_ref` maps `rWork = 0` back into `rWork = 0` (`c_ref * P₀ = P₀ * c_ref * P₀`),
2. For every constant postcondition `fun _ => M`, `d` preserves store-independence and matches
   `c_ref` under `P₀ * · * P₀`. -/
def RealizesCleanRef [Fintype Var] [DecidableEq Var] [NeZero (2 ^ n)] {m : ℕ}
    (rWork : QRegister m n) (c_ref : Circuit n) (d : DynamicCircuit Var n) : Prop :=
  (c_ref.eval.1 * rWork.basisOutcomeProjector 0 =
    rWork.basisOutcomeProjector 0 * c_ref.eval.1 * rWork.basisOutcomeProjector 0) ∧
  ∀ M : Observable (Fin (2 ^ n)), ∃ M' : Observable (Fin (2 ^ n)),
    wp d.compile (fun _ => M) = (fun _ => M') ∧
    rWork.basisOutcomeProjector 0 * M'.1.1 * rWork.basisOutcomeProjector 0 =
      rWork.basisOutcomeProjector 0 * (c_ref.eval.1ᴴ * M.1.1 * c_ref.eval.1) *
        rWork.basisOutcomeProjector 0

theorem cleanProjector_of_phasedPerm_fix {m : ℕ}
    (rWork : QRegister m n) (c : Circuit n)
    {φ : BitAssignment n → ℂ} {f : BitAssignment n → BitAssignment n}
    (hperm : PhasedPerm c φ f)
    (hfix : ∀ (β : BitAssignment n) (i : Fin m), β (rWork i) = 0 → f β (rWork i) = 0) :
    c.eval.1 * rWork.basisOutcomeProjector 0 =
      rWork.basisOutcomeProjector 0 * c.eval.1 * rWork.basisOutcomeProjector 0 := by
  apply matrix_ext_ket
  intro β
  simp only [← Matrix.mulVec_mulVec, register_basisOutcomeProjector_zero_ket]
  by_cases h0 : ∀ i : Fin m, β (rWork i) = 0
  · have hf0 : ∀ i : Fin m, f β (rWork i) = 0 := fun i => hfix β i (h0 i)
    rw [ite_eq_left_of_eq_true _ _ (eq_true h0), hperm β, Matrix.mulVec_smul,
      register_basisOutcomeProjector_zero_ket, ite_eq_left_of_eq_true _ _ (eq_true hf0)]
  · rw [ite_eq_right_of_eq_false _ _ (eq_false h0), Matrix.mulVec_zero, Matrix.mulVec_zero]

theorem basisOutcomeProjector_zero_absorb_of_image_subset {m₁ m₂ : ℕ}
    (r₁ : QRegister m₁ n) (r₂ : QRegister m₂ n) (hsub : r₁.image ⊆ r₂.image) :
    r₂.basisOutcomeProjector 0 * r₁.basisOutcomeProjector 0 = r₂.basisOutcomeProjector 0 ∧
      r₁.basisOutcomeProjector 0 * r₂.basisOutcomeProjector 0 = r₂.basisOutcomeProjector 0 := by
  have himp : ∀ g : Fin (2 ^ n), r₂.extractIndex g = 0 → r₁.extractIndex g = 0 := by
    intro g h₂
    rw [QRegister.extractIndex_eq_zero_iff] at h₂ ⊢
    intro i
    have hmem : r₁ i ∈ r₂.image := hsub (QRegister.mem_image r₁ (r₁ i) |>.mpr ⟨i, rfl⟩)
    obtain ⟨j, hj⟩ := QRegister.mem_image r₂ (r₁ i) |>.mp hmem
    rw [← hj]
    exact h₂ j
  constructor
  · rw [QRegister.basisOutcomeProjector_eq_diagonal, QRegister.basisOutcomeProjector_eq_diagonal,
      Matrix.diagonal_mul_diagonal]
    congr 1; funext g
    by_cases h₂ : r₂.extractIndex g = 0
    · simp [h₂, himp g h₂]
    · simp [h₂]
  · rw [QRegister.basisOutcomeProjector_eq_diagonal, QRegister.basisOutcomeProjector_eq_diagonal,
      Matrix.diagonal_mul_diagonal]
    congr 1; funext g
    by_cases h₂ : r₂.extractIndex g = 0
    · simp [h₂, himp g h₂]
    · simp [h₂]

theorem RealizesCleanRef.of_circuit [Fintype Var] [DecidableEq Var] [NeZero (2 ^ n)] {m : ℕ}
    (rWork : QRegister m n) (c : Circuit n)
    (hclean : c.eval.1 * rWork.basisOutcomeProjector 0 =
      rWork.basisOutcomeProjector 0 * c.eval.1 * rWork.basisOutcomeProjector 0) :
    RealizesCleanRef (Var := Var) rWork c (.circuit c) := by
  refine ⟨hclean, fun M => ⟨qcQAssignObsMap c.eval M, ?_, ?_⟩⟩
  · funext σ; simp [DynamicCircuit.compile_circuit, qcWpQAssign]
  · simp [qcQAssignObsMap, Matrix.star_eq_conjTranspose, Matrix.mul_assoc]

theorem RealizesCleanRef.of_disjoint_circuit [Fintype Var] [DecidableEq Var] [NeZero (2 ^ n)] {m :
    ℕ}
    (rWork : QRegister m n) (c : Circuit n) (hdisj : Disjoint c.support rWork.image) :
    RealizesCleanRef (Var := Var) rWork c (.circuit c) := by
  apply RealizesCleanRef.of_circuit
  have hcomm := eval_comm_basisOutcomeProjector_of_disjoint_support c rWork hdisj 0
  have hidem : rWork.basisOutcomeProjector 0 * rWork.basisOutcomeProjector 0 =
      rWork.basisOutcomeProjector 0 :=
    (basisOutcomeProjector_zero_absorb_of_image_subset rWork rWork Finset.Subset.rfl).1
  calc
    c.eval.1 * rWork.basisOutcomeProjector 0
        = c.eval.1 * (rWork.basisOutcomeProjector 0 * rWork.basisOutcomeProjector 0) := by
          rw [hidem]
    _ = (c.eval.1 * rWork.basisOutcomeProjector 0) * rWork.basisOutcomeProjector 0 := by
        simp only [Matrix.mul_assoc]
    _ = rWork.basisOutcomeProjector 0 * c.eval.1 * rWork.basisOutcomeProjector 0 := by rw [hcomm]

theorem RealizesCleanRef.seq [Fintype Var] [DecidableEq Var] [NeZero (2 ^ n)] {m : ℕ}
    {rWork : QRegister m n} {c₁ c₂ : Circuit n} {d₁ d₂ : DynamicCircuit Var n}
    (h₁ : RealizesCleanRef rWork c₁ d₁) (h₂ : RealizesCleanRef rWork c₂ d₂) :
    RealizesCleanRef rWork (c₁ ;;ᶜ c₂) (.seq d₁ d₂) := by
  let P₀ := rWork.basisOutcomeProjector 0
  have hP₀_herm : P₀ᴴ = P₀ := rWork.basisOutcomeProjector_conjTranspose 0
  have hc₁ : c₁.eval.1 * P₀ = P₀ * c₁.eval.1 * P₀ := h₁.1
  have hc₂ : c₂.eval.1 * P₀ = P₀ * c₂.eval.1 * P₀ := h₂.1
  have hc₁_adj : P₀ * c₁.eval.1ᴴ = P₀ * c₁.eval.1ᴴ * P₀ := by
    have h := congrArg Matrix.conjTranspose hc₁
    simpa only [P₀, Matrix.conjTranspose_mul, hP₀_herm, Matrix.mul_assoc] using h
  refine ⟨?_, fun M => ?_⟩
  · change (c₂.eval.1 * c₁.eval.1) * P₀ = P₀ * (c₂.eval.1 * c₁.eval.1) * P₀
    calc
      (c₂.eval.1 * c₁.eval.1) * P₀
          = c₂.eval.1 * (c₁.eval.1 * P₀) := by simp only [Matrix.mul_assoc]
      _ = c₂.eval.1 * (P₀ * c₁.eval.1 * P₀) := by rw [hc₁]
      _ = (c₂.eval.1 * P₀) * c₁.eval.1 * P₀ := by simp only [Matrix.mul_assoc]
      _ = (P₀ * c₂.eval.1 * P₀) * c₁.eval.1 * P₀ := by rw [hc₂]
      _ = P₀ * c₂.eval.1 * (P₀ * c₁.eval.1 * P₀) := by simp only [Matrix.mul_assoc]
      _ = P₀ * c₂.eval.1 * (c₁.eval.1 * P₀) := by rw [← hc₁]
      _ = P₀ * (c₂.eval.1 * c₁.eval.1) * P₀ := by simp only [Matrix.mul_assoc]
  · obtain ⟨M₂, hwp₂, hproj₂⟩ := h₂.2 M
    obtain ⟨M₁, hwp₁, hproj₁⟩ := h₁.2 M₂
    refine ⟨M₁, by simp only [DynamicCircuit.compile_seq, wp, hwp₂, hwp₁], ?_⟩
    change P₀ * M₁.1.1 * P₀ = P₀ * ((c₂.eval.1 * c₁.eval.1)ᴴ * M.1.1 * (c₂.eval.1 * c₁.eval.1)) * P₀
    calc
      P₀ * M₁.1.1 * P₀
          = P₀ * (c₁.eval.1ᴴ * M₂.1.1 * c₁.eval.1) * P₀ := hproj₁
      _ = (P₀ * c₁.eval.1ᴴ) * M₂.1.1 * (c₁.eval.1 * P₀) := by simp only [Matrix.mul_assoc]
      _ = (P₀ * c₁.eval.1ᴴ * P₀) * M₂.1.1 * (P₀ * c₁.eval.1 * P₀) := by
          conv_lhs => rw [hc₁_adj, hc₁]
      _ = (P₀ * c₁.eval.1ᴴ) * (P₀ * M₂.1.1 * P₀) * (c₁.eval.1 * P₀) := by
          simp only [Matrix.mul_assoc]
      _ = (P₀ * c₁.eval.1ᴴ) * (P₀ * (c₂.eval.1ᴴ * M.1.1 * c₂.eval.1) * P₀) * (c₁.eval.1 * P₀) := by
          rw [hproj₂]
      _ = (P₀ * c₁.eval.1ᴴ * P₀) * (c₂.eval.1ᴴ * M.1.1 * c₂.eval.1) * (P₀ * c₁.eval.1 * P₀) := by
          simp only [Matrix.mul_assoc]
      _ = (P₀ * c₁.eval.1ᴴ) * (c₂.eval.1ᴴ * M.1.1 * c₂.eval.1) * (c₁.eval.1 * P₀) := by
          conv_lhs => rw [← hc₁_adj, ← hc₁]
      _ = P₀ * ((c₂.eval.1 * c₁.eval.1)ᴴ * M.1.1 * (c₂.eval.1 * c₁.eval.1)) * P₀ := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]

theorem RealizesCleanRef.widenImage [Fintype Var] [DecidableEq Var] [NeZero (2 ^ n)]
    {m₁ m₂ : ℕ} {r₁ : QRegister m₁ n} {r₂ : QRegister m₂ n}
    {c_ref : Circuit n} {d : DynamicCircuit Var n}
    (hd : RealizesCleanRef r₁ c_ref d)
    (hsub : r₁.image ⊆ r₂.image)
    (hclean : c_ref.eval.1 * r₂.basisOutcomeProjector 0 =
      r₂.basisOutcomeProjector 0 * c_ref.eval.1 * r₂.basisOutcomeProjector 0) :
    RealizesCleanRef r₂ c_ref d := by
  refine ⟨hclean, fun M => ?_⟩
  obtain ⟨M', hwp, hproj⟩ := hd.2 M
  refine ⟨M', hwp, ?_⟩
  obtain ⟨hL, hR⟩ := basisOutcomeProjector_zero_absorb_of_image_subset r₁ r₂ hsub
  calc
    r₂.basisOutcomeProjector 0 * M'.1.1 * r₂.basisOutcomeProjector 0
        = (r₂.basisOutcomeProjector 0 * r₁.basisOutcomeProjector 0) * M'.1.1 *
            (r₁.basisOutcomeProjector 0 * r₂.basisOutcomeProjector 0) := by
          rw [hL, hR]
    _ = r₂.basisOutcomeProjector 0 *
          (r₁.basisOutcomeProjector 0 * M'.1.1 * r₁.basisOutcomeProjector 0) *
          r₂.basisOutcomeProjector 0 := by simp only [Matrix.mul_assoc]
    _ = r₂.basisOutcomeProjector 0 *
          (r₁.basisOutcomeProjector 0 * (c_ref.eval.1ᴴ * M.1.1 * c_ref.eval.1) *
            r₁.basisOutcomeProjector 0) *
          r₂.basisOutcomeProjector 0 := by rw [hproj]
    _ = (r₂.basisOutcomeProjector 0 * r₁.basisOutcomeProjector 0) *
          (c_ref.eval.1ᴴ * M.1.1 * c_ref.eval.1) *
          (r₁.basisOutcomeProjector 0 * r₂.basisOutcomeProjector 0) := by
          simp only [Matrix.mul_assoc]
    _ = r₂.basisOutcomeProjector 0 * (c_ref.eval.1ᴴ * M.1.1 * c_ref.eval.1) *
          r₂.basisOutcomeProjector 0 := by rw [hL, hR]

theorem RealizesCleanRef.wrapDynamic [Fintype Var] [DecidableEq Var] [NeZero (2 ^ n)] {m : ℕ}
    (v : Var) (s : PhasedStep n) (inner : DynamicCircuit Var n) (c_inner : Circuit n)
    (rRest : QRegister m n)
    (hdisj_anc : (QRegister.singleton s.anc).DisjointWires rRest)
    (hpre_anc : s.anc ∉ s.pre.support)
    (hpre_rest : Disjoint s.pre.support rRest.image)
    (hc₁_rest : s.c₁ ∉ rRest.image)
    (hc₂_rest : s.c₂ ∉ rRest.image)
    (hmidPre_rest : Disjoint s.midPre.support rRest.image)
    (hc_body :
      let P₀ := (QRegister.singleton s.anc).basisOutcomeProjector 0
      let T_anc := (Circuit.TOFF s.c₁ s.c₂ s.anc s.h₁₂ s.h₁a s.h₂a).eval.1
      P₀ * (T_anc * (s.midPre ;;ᶜ c_inner ;;ᶜ s.midPost).eval.1 * T_anc * P₀) =
        T_anc * (s.midPre ;;ᶜ c_inner ;;ᶜ s.midPost).eval.1 * T_anc * P₀)
    (h_inner : RealizesCleanRef rRest c_inner inner)
    (hclean_wrap :
      let rTotal := (QRegister.singleton s.anc).concat rRest hdisj_anc
      (s.wrapCircuit c_inner).eval.1 * rTotal.basisOutcomeProjector 0 =
        rTotal.basisOutcomeProjector 0 * (s.wrapCircuit c_inner).eval.1 *
          rTotal.basisOutcomeProjector 0) :
    RealizesCleanRef ((QRegister.singleton s.anc).concat rRest hdisj_anc)
      (s.wrapCircuit c_inner) (s.wrapDynamic v inner) := by
  let rTotal := (QRegister.singleton s.anc).concat rRest hdisj_anc
  have hstore_in : PreservesStoreConst inner := fun N => by
    obtain ⟨N', hN', _⟩ := h_inner.2 N
    exact ⟨N', hN'⟩
  have hstore_wrap : PreservesStoreConst (s.wrapDynamic v inner) :=
    PhasedStep.preservesStoreConst_wrapDynamic v s hstore_in
  refine ⟨hclean_wrap, fun M => ?_⟩
  obtain ⟨M_out, hM_out⟩ := hstore_wrap M
  refine ⟨M_out, hM_out, ?_⟩
  have hanc_not_rest : s.anc ∉ rRest.image := by
    have hd := (disjointWires_iff_disjoint_image (QRegister.singleton s.anc) rRest).mp hdisj_anc
    simpa [QRegister.image_singleton] using hd
  have hpre_total : Disjoint s.pre.support rTotal.image := by
    rw [image_concat_eq, Finset.disjoint_union_right, QRegister.image_singleton,
      Finset.disjoint_singleton_right]
    exact ⟨hpre_anc, hpre_rest⟩
  have hand_rest :
      Disjoint (Circuit.andCompute s.c₁ s.c₂ s.anc s.h₁a s.h₂a).support rRest.image := by
    rw [Circuit.support_andCompute]
    simp only [Finset.disjoint_insert_left, Finset.disjoint_singleton_left]
    exact ⟨hc₁_rest, hc₂_rest, hanc_not_rest⟩
  let M₁ : Observable (Fin (2 ^ n)) := qcQAssignObsMap s.post.eval M
  have hΘ₁_eq : qcWpQAssign s.post.eval (fun _ : Store Var => M) = (fun _ => M₁) := rfl
  obtain ⟨M₂, hM₂⟩ := PreservesStoreConst.andUncompute (Var := Var) v s.c₁ s.c₂ s.anc s.h₁₂ M₁
  let M₃ : Observable (Fin (2 ^ n)) := qcQAssignObsMap s.midPost.eval M₂
  have hΨ_eq : qcWpQAssign s.midPost.eval
      (wp (DynamicCircuit.andUncompute v s.c₁ s.c₂ s.anc s.h₁₂).compile (fun _ : Store Var => M₁)) =
      (fun _ => M₃) := by
    rw [hM₂]; rfl
  obtain ⟨M₄, hwp₄, hproj₄⟩ := h_inner.2 M₃
  have h_in_assert :
      restrictAssertionToZeroAncilla (wp inner.compile (fun _ : Store Var => M₃)) rRest =
      restrictAssertionToZeroAncilla (qcWpQAssign c_inner.eval (fun _ : Store Var => M₃)) rRest :=
        by
    funext σ; apply Subtype.ext; apply HermitianMat.ext
    rw [hwp₄]
    change rRest.basisOutcomeProjector 0 * M₄.1.mat * rRest.basisOutcomeProjector 0 =
      rRest.basisOutcomeProjector 0 * (c_inner.eval.1ᴴ * M₃.1.mat * c_inner.eval.1) *
        rRest.basisOutcomeProjector 0 at hproj₄
    simp only [restrictAssertionToZeroAncilla_coe, qcWpQAssign, qcQAssignObsMap,
      Observable.conjUnitary, Observable.conj_coe, HermitianMat.conj_apply_mat,
      Unitary.coe_star, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose,
      QRegister.basisOutcomeProjector_conjTranspose, Matrix.mul_assoc] at hproj₄ ⊢
    exact hproj₄
  let middle : DynamicCircuit Var n :=
    .seq (DynamicCircuit.andCompute s.c₁ s.c₂ s.anc s.h₁a s.h₂a)
      (.seq (.seq (.circuit s.midPre) (.seq inner (.circuit s.midPost)))
        (DynamicCircuit.andUncompute v s.c₁ s.c₂ s.anc s.h₁₂))
  let c_body := s.midPre ;;ᶜ c_inner ;;ᶜ s.midPost
  have hlhs_expand :
      wp (s.wrapDynamic v inner).compile (fun _ : Store Var => M) =
        qcWpQAssign s.pre.eval (wp middle.compile (fun _ => M₁)) := by
    simp [PhasedStep.wrapDynamic, middle, hΘ₁_eq, wp]
  have hrhs_expand :
      qcWpQAssign (s.wrapCircuit c_inner).eval (fun _ : Store Var => M) =
        qcWpQAssign s.pre.eval
          (qcWpQAssign
            (Circuit.TOFF s.c₁ s.c₂ s.anc s.h₁₂ s.h₁a s.h₂a ;;ᶜ
              c_body ;;ᶜ
              Circuit.TOFF s.c₁ s.c₂ s.anc s.h₁₂ s.h₁a s.h₂a).eval
            (fun _ => M₁)) := by
    simp only [PhasedStep.wrapCircuit, c_body, hΘ₁_eq.symm, Circuit.eval_seq, qc_wp_qAssign_comp,
      mul_assoc]
  have hmid_wp :
      wp middle.compile (fun _ : Store Var => M₁) =
        qcWpQAssign (Circuit.andCompute s.c₁ s.c₂ s.anc s.h₁a s.h₂a).eval
          (qcWpQAssign s.midPre.eval (wp inner.compile (fun _ => M₃))) := by
    simp [middle, DynamicCircuit.andCompute, wp, hΨ_eq]
  have hmid_c_wp :
      qcWpQAssign (Circuit.andCompute s.c₁ s.c₂ s.anc s.h₁a s.h₂a).eval
        (qcWpQAssign s.midPre.eval (qcWpQAssign c_inner.eval (fun _ : Store Var => M₃))) =
      wp (DynamicCircuit.seq (DynamicCircuit.andCompute s.c₁ s.c₂ s.anc s.h₁a s.h₂a)
        (DynamicCircuit.seq (.circuit c_body)
          (DynamicCircuit.andUncompute v s.c₁ s.c₂ s.anc s.h₁₂))).compile (fun _ => M₁) := by
    simp [c_body, DynamicCircuit.andCompute, wp,
      qc_wp_qAssign_comp, ← hΨ_eq]
  have heq_assert :
      restrictAssertionToZeroAncilla (wp (s.wrapDynamic v inner).compile (fun _ : Store Var =>
        M)) rTotal =
      restrictAssertionToZeroAncilla (qcWpQAssign (s.wrapCircuit c_inner).eval (fun _ : Store Var =>
        M)) rTotal := by
    rw [hlhs_expand, hrhs_expand,
      restrictAssertionToZeroAncilla_wp_qAssign_comm_of_disjoint s.pre rTotal hpre_total,
      restrictAssertionToZeroAncilla_wp_qAssign_comm_of_disjoint s.pre rTotal hpre_total]
    congr 1
    rw [restrictAssertionToZeroAncilla_concat _ (QRegister.singleton s.anc) rRest hdisj_anc,
      restrictAssertionToZeroAncilla_concat _ (QRegister.singleton s.anc) rRest hdisj_anc,
      restrictAssertionToZeroAncilla_comm _ (QRegister.singleton s.anc) rRest,
      hmid_wp,
      restrictAssertionToZeroAncilla_wp_qAssign_comm_of_disjoint _ rRest hand_rest,
      restrictAssertionToZeroAncilla_wp_qAssign_comm_of_disjoint s.midPre rRest hmidPre_rest,
      h_in_assert,
      ← restrictAssertionToZeroAncilla_wp_qAssign_comm_of_disjoint s.midPre rRest hmidPre_rest,
      ← restrictAssertionToZeroAncilla_wp_qAssign_comm_of_disjoint _ rRest hand_rest,
      hmid_c_wp,
      restrictAssertionToZeroAncilla_comm _ rRest (QRegister.singleton s.anc),
      DynamicCircuit.qc_wp_andCompute_circuit_andUncompute_of_update_eq
        v s.c₁ s.c₂ s.anc s.h₁₂ s.h₁a s.h₂a c_body hc_body (fun _ => M₁) (fun _ _ => rfl)]
  let σ₀ : Store Var := fun _ => 0
  have heq_mat := congrArg (fun A => (A σ₀).1.mat) heq_assert
  rw [hM_out] at heq_mat
  change rTotal.basisOutcomeProjector 0 * M_out.1.mat * rTotal.basisOutcomeProjector 0 =
    rTotal.basisOutcomeProjector 0 *
      ((s.wrapCircuit c_inner).eval.1ᴴ * M.1.mat * (s.wrapCircuit c_inner).eval.1) *
      rTotal.basisOutcomeProjector 0
  simp only [rTotal, restrictAssertionToZeroAncilla_coe, qcWpQAssign, qcQAssignObsMap,
    Observable.conjUnitary, Observable.conj_coe, HermitianMat.conj_apply_mat,
    Unitary.coe_star, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose,
    QRegister.basisOutcomeProjector_conjTranspose, Matrix.mul_assoc] at heq_mat ⊢
  exact heq_mat

theorem RealizesCleanRef.toEmbeddedUnitary [Fintype Var] [DecidableEq Var] [NeZero (2 ^ n)]
    {k m : ℕ} {rAct : QRegister k n} {rWork : QRegister m n}
    {U : Unitary (2 ^ k)} {c_ref : Circuit n} {d : DynamicCircuit Var n}
    (hd : RealizesCleanRef rWork c_ref d)
    (hcol : c_ref.eval.1 * rWork.basisOutcomeProjector 0 =
      (rAct.embedUnitary U).1 * rWork.basisOutcomeProjector 0) :
    DynamicCircuit.RealizesEmbeddedUnitaryWithCleanWorkspace rAct rWork U d := by
  intro M
  obtain ⟨M', hwp, hproj⟩ := hd.2 M
  refine ⟨M', hwp, ?_⟩
  let P₀ := rWork.basisOutcomeProjector 0
  have hrow : P₀ * c_ref.eval.1ᴴ = P₀ * (rAct.embedUnitary U).1ᴴ := by
    have h := congrArg Matrix.conjTranspose hcol
    simpa only [P₀, Matrix.conjTranspose_mul, rWork.basisOutcomeProjector_conjTranspose 0] using h
  calc
    P₀ * M'.1.1 * P₀ = P₀ * (c_ref.eval.1ᴴ * M.1.1 * c_ref.eval.1) * P₀ := hproj
    _ = (P₀ * c_ref.eval.1ᴴ) * M.1.1 * (c_ref.eval.1 * P₀) := by simp only [Matrix.mul_assoc]
    _ = (P₀ * (rAct.embedUnitary U).1ᴴ) * M.1.1 * ((rAct.embedUnitary U).1 * P₀) := by
          rw [hrow, hcol]
    _ = P₀ * ((rAct.embedUnitary U).1ᴴ * M.1.1 * (rAct.embedUnitary U).1) * P₀ := by
          simp only [Matrix.mul_assoc]

/-- Little-endian natural number `< 2 ^ B` encoded by a `B`-bit `ZMod 2` sequence. -/
noncomputable def bitSeqVal {B : ℕ} (bits : Fin B → ZMod 2) : ℕ :=
  ((basisBits B).symm bits).val

theorem bitSeqVal_lt {B : ℕ} (bits : Fin B → ZMod 2) : bitSeqVal bits < 2 ^ B :=
  ((basisBits B).symm bits).isLt

@[simp]
theorem bitSeqVal_div_pow_mod_two {B : ℕ} (bits : Fin B → ZMod 2) (j : Fin B) :
    ((bitSeqVal bits / 2 ^ j.val % 2 : ℕ) : ZMod 2) = bits j := by
  dsimp [bitSeqVal]
  rw [← basisBits_eq_div_mod, basisBits_symm_eq]

@[simp]
theorem bitSeqVal_zero (B : ℕ) : bitSeqVal (fun _ : Fin B => (0 : ZMod 2)) = 0 := by
  have h : (basisBits B).symm (fun _ => 0) = 0 := by
    apply (basisBits B).injective
    rw [(basisBits B).apply_symm_apply]
    funext j
    exact (basisBits_zero_at B j).symm
  exact congrArg Fin.val h

@[simp]
private theorem update_update_self_eq {α : Type*} {γ : α → Type*} [DecidableEq α]
    (f : (a : α) → γ a) (a : α) (x : γ a) :
    Function.update (Function.update f a x) a (f a) = f := by
  funext b
  by_cases h : b = a
  · subst h; simp
  · simp [h]

private theorem nat_lt_two_cases {m : ℕ} (hm : m < 2) : m = 0 ∨ m = 1 := by omega

/-- Bidirectional modular shift on `Fin (2 ^ B)` induced by `fan ;; (+ a_lo) ;; fan`:
- when `wp = 0`: `y ↦ (y + a_lo) % 2^B`,
- when `wp = 1`: `y ↦ 2^B - 1 - ((2^B - 1 - y + a_lo) % 2^B)`, which is the exact inverse. -/
def addModEquiv (B a_lo : ℕ) (ha : a_lo < 2 ^ B) : Equiv.Perm (Fin (2 ^ B)) where
  toFun y := ⟨(y.val + a_lo) % 2 ^ B, Nat.mod_lt _ (Nat.two_pow_pos B)⟩
  invFun z := ⟨2 ^ B - 1 - ((2 ^ B - 1 - z.val + a_lo) % 2 ^ B), by
    have := Nat.mod_lt (2 ^ B - 1 - z.val + a_lo) (Nat.two_pow_pos B)
    omega⟩
  left_inv y := by
    ext; dsimp only
    have hy := y.isLt
    have h1 := Nat.div_add_mod (y.val + a_lo) (2 ^ B)
    have hc1 : (y.val + a_lo) / 2 ^ B < 2 :=
      (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos B)).mpr (by omega)
    set z := (y.val + a_lo) % 2 ^ B
    have hz : z < 2 ^ B := Nat.mod_lt _ (Nat.two_pow_pos B)
    have h2 := Nat.div_add_mod (2 ^ B - 1 - z + a_lo) (2 ^ B)
    have hc2 : (2 ^ B - 1 - z + a_lo) / 2 ^ B < 2 :=
      (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos B)).mpr (by omega)
    rcases nat_lt_two_cases hc1 with h | h <;>
      rcases nat_lt_two_cases hc2 with h' | h'
    · rw [h] at h1; rw [h'] at h2; simp only [mul_zero, zero_add] at h1 h2; omega
    · rw [h] at h1; rw [h'] at h2; simp only [mul_zero, mul_one, zero_add] at h1 h2; omega
    · rw [h] at h1; rw [h'] at h2; simp only [mul_zero, mul_one, zero_add] at h1 h2; omega
    · rw [h] at h1; rw [h'] at h2; simp only [mul_one] at h1 h2; omega
  right_inv z := by
    ext; dsimp only
    have hz := z.isLt
    have h1 := Nat.div_add_mod (2 ^ B - 1 - z.val + a_lo) (2 ^ B)
    have hc1 : (2 ^ B - 1 - z.val + a_lo) / 2 ^ B < 2 :=
      (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos B)).mpr (by omega)
    set s := (2 ^ B - 1 - z.val + a_lo) % 2 ^ B
    have hs : s < 2 ^ B := Nat.mod_lt _ (Nat.two_pow_pos B)
    have h2 := Nat.div_add_mod (2 ^ B - 1 - s + a_lo) (2 ^ B)
    have hc2 : (2 ^ B - 1 - s + a_lo) / 2 ^ B < 2 :=
      (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos B)).mpr (by omega)
    rcases nat_lt_two_cases hc1 with h | h <;>
      rcases nat_lt_two_cases hc2 with h' | h'
    · rw [h] at h1; rw [h'] at h2; simp only [mul_zero, zero_add] at h1 h2; omega
    · rw [h] at h1; rw [h'] at h2; simp only [mul_zero, mul_one, zero_add] at h1 h2; omega
    · rw [h] at h1; rw [h'] at h2; simp only [mul_zero, mul_one, zero_add] at h1 h2; omega
    · rw [h] at h1; rw [h'] at h2; simp only [mul_one] at h1 h2; omega

@[simp] theorem addModEquiv_apply_val (B a_lo : ℕ) (ha : a_lo < 2 ^ B) (y : Fin (2 ^ B)) :
    (addModEquiv B a_lo ha y).val = (y.val + a_lo) % 2 ^ B := rfl

@[simp] theorem addModEquiv_symm_apply_val (B a_lo : ℕ) (ha : a_lo < 2 ^ B) (z : Fin (2 ^ B)) :
    ((addModEquiv B a_lo ha).symm z).val =
      2 ^ B - 1 - ((2 ^ B - 1 - z.val + a_lo) % 2 ^ B) := rfl

def signedAddModPerm (B a_lo : ℕ) (ha : a_lo < 2 ^ B) (wp : ZMod 2) : Equiv.Perm (Fin (2 ^ B)) :=
  if wp = 0 then addModEquiv B a_lo ha else (addModEquiv B a_lo ha).symm

/-- Exact phase-step amplitude produced by `rawUnsignedPhaseKickRef` on `(y : Fin (2 ^ B))`. -/
noncomputable def rawPhaseStepVal (B a_lo b_mid b_top : ℕ) (wp : ZMod 2) (y : Fin (2 ^ B)) : ℂ :=
  let yc := if wp = 0 then y.val else 2 ^ B - 1 - y.val
  let c := (yc + a_lo) / 2 ^ B
  let φ_top := Complex.I ^ b_top * (-1 : ℂ) ^ (wp.val * b_top)
  let φ_mid := omega8 ^ ((((b_mid : ℕ) : ZMod 2) + wp).val) * (-Complex.I) ^ wp.val
  let φ_lo := omega8 ^ ((((c : ℕ) : ZMod 2) + wp).val)
  φ_top * (φ_mid * φ_lo)

private theorem norm_omega8 : ‖omega8‖ = 1 := by
  dsimp [omega8]
  have harg : Complex.I * ↑Real.pi / 4 = ↑(Real.pi / 4) * Complex.I := by push_cast; ring
  rw [harg, Complex.norm_exp_ofReal_mul_I]

theorem star_mul_self_rawPhaseStepVal (B a_lo b_mid b_top : ℕ) (wp : ZMod 2) (y : Fin (2 ^ B)) :
    star (rawPhaseStepVal B a_lo b_mid b_top wp y) * rawPhaseStepVal B a_lo b_mid b_top wp y =
        1 := by
  have hnorm : ‖rawPhaseStepVal B a_lo b_mid b_top wp y‖ = 1 := by
    dsimp [rawPhaseStepVal]
    simp only [norm_mul, norm_pow, Complex.norm_I, norm_neg, norm_one, norm_omega8, one_pow,
      mul_one]
  rw [mul_comm, RCLike.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, hnorm, one_pow,
    Complex.ofReal_one]

private theorem exp_pi_div_two_I : Complex.exp (Complex.I * Real.pi / 2) = Complex.I := by
  have h : Complex.I * ↑Real.pi / 2 = ↑(Real.pi / 2) * Complex.I := by push_cast; ring
  rw [h, Complex.exp_mul_I]
  simp [Complex.cos_pi_div_two, Complex.sin_pi_div_two]

private theorem exp_neg_pi_div_two_I : Complex.exp (-(Complex.I * Real.pi / 2)) = -Complex.I := by
  have h : -(Complex.I * ↑Real.pi / 2) = ↑(-(Real.pi / 2)) * Complex.I := by push_cast; ring
  rw [h, Complex.exp_mul_I, Complex.ofReal_neg]
  simp [Complex.cos_neg, Complex.sin_neg, Complex.cos_pi_div_two, Complex.sin_pi_div_two]

/-- Core phase-gradient eigenrelation of `rawPhaseStepVal` on `phaseGradientFineLow B 3`:
for BOTH `wp = 0` and `wp = 1`, the carry bit `c` cancels identically against the modular shift
`signedAddModPerm B a_lo ha wp y`, leaving `exp((±1) * 2πi * K / 2^(B + 3))`. -/
theorem rawPhaseStepVal_mul_phaseGradientFineLow
    (B a_lo b_mid b_top : ℕ) (ha : a_lo < 2 ^ B) (hmid : b_mid < 2) (htop : b_top < 2)
    (wp : ZMod 2) (y : Fin (2 ^ B)) :
    let K := a_lo + 2 ^ B * b_mid + 2 ^ (B + 1) * b_top
    let sgn : ℂ := if wp = 0 then 1 else -1
    rawPhaseStepVal B a_lo b_mid b_top wp y * phaseGradientFineLow B 3 y =
      Complex.exp (sgn * (2 * Real.pi * Complex.I * (K : ℂ)) / 2 ^ (B + 3)) *
        phaseGradientFineLow B 3 (signedAddModPerm B a_lo ha wp y) := by
  intro K sgn
  have hy := y.isLt
  have hpowB3 : (2 : ℂ) ^ (B + 3) = (2 : ℂ) ^ B * 8 := by rw [pow_add]; norm_num
  have hpowB1 : (2 : ℂ) ^ (B + 1) = (2 : ℂ) ^ B * 2 := by rw [pow_add]; norm_num
  have homega_pow : ∀ m : ℕ, omega8 ^ m = Complex.exp ((m : ℂ) * (Complex.I * Real.pi / 4)) := by
    intro m; dsimp [omega8]; rw [← Complex.exp_nat_mul]
  rcases zmod2_eq_zero_or_one wp with rfl | rfl
  · -- `wp = 0`: `yc = y.val`, `y_out = (y.val + a_lo) % 2^B`
    set c := (y.val + a_lo) / 2 ^ B with hc_def
    have hc_lt : c < 2 := (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos B)).mpr (by omega)
    have hdiv_mod : 2 ^ B * c + (y.val + a_lo) % 2 ^ B = y.val + a_lo :=
      Nat.div_add_mod (y.val + a_lo) (2 ^ B)
    have hdivC : (2 : ℂ) ^ B * (c : ℂ) + (((y.val + a_lo) % 2 ^ B : ℕ) : ℂ) =
        (y.val : ℂ) + (a_lo : ℂ) := by exact_mod_cast hdiv_mod
    have htop_exp : (Complex.I ^ b_top : ℂ) =
        Complex.exp (((2 * b_top : ℕ) : ℂ) * (Complex.I * Real.pi / 4)) := by
      rcases nat_lt_two_cases htop with rfl | rfl
      · simp
      · push_cast
        have harg : (2 : ℂ) * (Complex.I * ↑Real.pi / 4) = Complex.I * ↑Real.pi / 2 := by ring
        rw [pow_one, harg, exp_pi_div_two_I]
    have hmid_val : (((b_mid : ℕ) : ZMod 2) + 0).val = b_mid := by
      rcases nat_lt_two_cases hmid with h | h <;> rw [h] <;> rfl
    have hc_val : (((c : ℕ) : ZMod 2) + 0).val = c := by
      rcases nat_lt_two_cases hc_lt with h | h <;> rw [h] <;> rfl
    change (Complex.I ^ b_top * (-1 : ℂ) ^ (0 * b_top)) *
        (omega8 ^ (((b_mid : ℕ) : ZMod 2) + 0).val * (-Complex.I) ^ 0 *
          omega8 ^ (((c : ℕ) : ZMod 2) + 0).val) *
        ((Real.sqrt (2 ^ B) : ℂ)⁻¹ *
          Complex.exp (-(2 * ↑Real.pi * Complex.I * ↑y.val) / 2 ^ (B + 3))) =
      Complex.exp (1 * (2 * ↑Real.pi * Complex.I * ↑K) / 2 ^ (B + 3)) *
        ((Real.sqrt (2 ^ B) : ℂ)⁻¹ *
          Complex.exp (-(2 * ↑Real.pi * Complex.I * ↑((y.val + a_lo) % 2 ^ B)) / 2 ^ (B + 3)))
    rw [zero_mul, pow_zero, mul_one, pow_zero, mul_one, hmid_val, hc_val, htop_exp,
      homega_pow, homega_pow, ← Complex.exp_add, ← Complex.exp_add]
    rw [← mul_assoc, mul_comm _ ((Real.sqrt (2 ^ B) : ℂ)⁻¹), mul_assoc, ← Complex.exp_add]
    conv_rhs => rw [← mul_assoc, mul_comm _ ((Real.sqrt (2 ^ B) : ℂ)⁻¹), mul_assoc,
      ← Complex.exp_add]
    congr 1; congr 1
    dsimp [K]
    push_cast
    rw [hpowB3, hpowB1]
    have ha_eq : (a_lo : ℂ) =
        (2 : ℂ) ^ B * (c : ℂ) + (((y.val + a_lo) % 2 ^ B : ℕ) : ℂ) - (y.val : ℂ) := by
      linear_combination -hdivC
    rw [ha_eq]
    have hB_ne : (2 : ℂ) ^ B ≠ 0 := pow_ne_zero _ two_ne_zero
    field_simp [hB_ne]
    ring
  · -- `wp = 1`: `yc = 2^B - 1 - y.val`, `y_out = 2^B - 1 - ((yc + a_lo) % 2^B)`
    set yc := 2 ^ B - 1 - y.val
    set c := (yc + a_lo) / 2 ^ B
    set ysum := (yc + a_lo) % 2 ^ B
    set yout := 2 ^ B - 1 - ysum
    have hyc_lt : yc < 2 ^ B := by dsimp [yc]; omega
    have hc_lt : c < 2 := (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos B)).mpr (by omega)
    have hysum_lt : ysum < 2 ^ B := Nat.mod_lt _ (Nat.two_pow_pos B)
    have hdiv_mod : 2 ^ B * c + ysum = yc + a_lo := Nat.div_add_mod (yc + a_lo) (2 ^ B)
    have hrel_nat : y.val + 2 ^ B * c = yout + a_lo := by
      dsimp [yc, yout] at hdiv_mod ⊢; omega
    have hrelC : (y.val : ℂ) + (2 : ℂ) ^ B * (c : ℂ) = (yout : ℂ) + (a_lo : ℂ) := by
      exact_mod_cast hrel_nat
    have htop_exp : Complex.I ^ b_top * (-1 : ℂ) ^ (1 * b_top) =
        Complex.exp (-((2 * b_top : ℕ) : ℂ) * (Complex.I * Real.pi / 4)) := by
      rcases nat_lt_two_cases htop with rfl | rfl
      · simp
      · simp only [one_mul, pow_one]
        push_cast
        have harg : -(2 : ℂ) * (Complex.I * ↑Real.pi / 4) = -(Complex.I * ↑Real.pi / 2) := by ring
        rw [harg, exp_neg_pi_div_two_I]; ring
    have hmid_lo_exp :
        omega8 ^ (((b_mid : ℕ) : ZMod 2) + 1).val * (-Complex.I) ^ 1 *
          omega8 ^ (((c : ℕ) : ZMod 2) + 1).val =
        Complex.exp (-((b_mid + c : ℕ) : ℂ) * (Complex.I * Real.pi / 4)) := by
      have ho_inv : omega8 * Complex.exp (-(Complex.I * Real.pi / 4)) = 1 := by
        dsimp [omega8]; rw [← Complex.exp_add]; simp
      have hII : Complex.I * (-Complex.I) = 1 := by simp
      rcases nat_lt_two_cases hmid with hm | hm <;>
        rcases nat_lt_two_cases hc_lt with hc | hc <;>
        rw [hm, hc]
      · change omega8 ^ 1 * (-Complex.I) ^ 1 * omega8 ^ 1 = _
        have hsq : omega8 * (-Complex.I) * omega8 = omega8 ^ 2 * (-Complex.I) := by ring
        simp only [pow_one, hsq, omega8_sq, hII, zero_add, Nat.cast_zero, neg_zero, zero_mul,
          Complex.exp_zero]
      · change omega8 ^ 1 * (-Complex.I) ^ 1 * omega8 ^ 0 = _
        simp only [pow_one, pow_zero, mul_one, zero_add, Nat.cast_one, neg_one_mul]
        calc
          omega8 * -Complex.I
              = omega8 * (-Complex.I) * (omega8 * Complex.exp (-(Complex.I * ↑Real.pi / 4))) := by
                rw [ho_inv, mul_one]
          _ = (omega8 ^ 2 * (-Complex.I)) * Complex.exp (-(Complex.I * ↑Real.pi / 4)) := by ring
          _ = Complex.exp (-(Complex.I * ↑Real.pi / 4)) := by rw [omega8_sq, hII, one_mul]
      · change omega8 ^ 0 * (-Complex.I) ^ 1 * omega8 ^ 1 = _
        simp only [pow_zero, pow_one, one_mul, add_zero, Nat.cast_one, neg_one_mul]
        calc
          -Complex.I * omega8
              = (-Complex.I * omega8) * (omega8 * Complex.exp (-(Complex.I * ↑Real.pi / 4))) := by
                rw [ho_inv, mul_one]
          _ = (omega8 ^ 2 * (-Complex.I)) * Complex.exp (-(Complex.I * ↑Real.pi / 4)) := by ring
          _ = Complex.exp (-(Complex.I * ↑Real.pi / 4)) := by rw [omega8_sq, hII, one_mul]
      · change omega8 ^ 0 * (-Complex.I) ^ 1 * omega8 ^ 0 = _
        simp only [pow_zero, one_mul, pow_one, mul_one]
        push_cast
        have harg : -(2 : ℂ) * (Complex.I * ↑Real.pi / 4) = -(Complex.I * ↑Real.pi / 2) := by ring
        rw [harg, exp_neg_pi_div_two_I]
    change (Complex.I ^ b_top * (-1 : ℂ) ^ (1 * b_top)) *
        (omega8 ^ (((b_mid : ℕ) : ZMod 2) + 1).val * (-Complex.I) ^ 1 *
          omega8 ^ (((c : ℕ) : ZMod 2) + 1).val) *
        ((Real.sqrt (2 ^ B) : ℂ)⁻¹ *
          Complex.exp (-(2 * ↑Real.pi * Complex.I * ↑y.val) / 2 ^ (B + 3))) =
      Complex.exp (-1 * (2 * ↑Real.pi * Complex.I * ↑K) / 2 ^ (B + 3)) *
        ((Real.sqrt (2 ^ B) : ℂ)⁻¹ *
          Complex.exp (-(2 * ↑Real.pi * Complex.I * ↑yout) / 2 ^ (B + 3)))
    rw [htop_exp, hmid_lo_exp, ← Complex.exp_add]
    rw [← mul_assoc, mul_comm _ ((Real.sqrt (2 ^ B) : ℂ)⁻¹), mul_assoc, ← Complex.exp_add]
    conv_rhs => rw [← mul_assoc, mul_comm _ ((Real.sqrt (2 ^ B) : ℂ)⁻¹), mul_assoc,
      ← Complex.exp_add]
    congr 1; congr 1
    dsimp [K]
    push_cast
    rw [hpowB3, hpowB1]
    have ha_eq : (a_lo : ℂ) =
        (y.val : ℂ) + (2 : ℂ) ^ B * (c : ℂ) - (yout : ℂ) := by
      linear_combination -hrelC
    rw [ha_eq]
    have hB_ne : (2 : ℂ) ^ B ≠ 0 := pow_ne_zero _ two_ne_zero
    field_simp [hB_ne]
    ring

/-- Construct a `Unitary d` directly from a unit-modulus diagonal `f : Fin d → ℂ`. -/
noncomputable def phaseDiagUnitary {d : ℕ} (f : Fin d → ℂ) (hf : ∀ x, star (f x) * f x = 1) :
    Unitary d :=
  ⟨Matrix.diagonal f, by
    rw [Matrix.mem_unitaryGroup_iff']
    rw [Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases hij : i = j
    · subst hij
      simp only [Matrix.diagonal_apply_eq, Pi.star_apply, Matrix.one_apply_eq]
      exact hf i
    · simp [hij]⟩

@[simp]
theorem phaseDiagUnitary_mulVec {d : ℕ} (f : Fin d → ℂ) (hf : ∀ x, star (f x) * f x = 1)
    (ψ : Fin d → ℂ) (x : Fin d) :
    (phaseDiagUnitary f hf).1.mulVec ψ x = f x * ψ x := by
  simp [phaseDiagUnitary, Matrix.mulVec_diagonal]

end RawUnsignedPhaseKickBridge

end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.CircuitModular.UnsignedGivens

end
