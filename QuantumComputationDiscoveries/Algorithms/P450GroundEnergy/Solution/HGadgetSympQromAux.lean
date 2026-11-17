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

public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.Keep9Symp14Tables
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.Outer8TwoRotWalk

@[expose] public section

/-! # Grouped Hadamard-Gadget Symplectic `14`-Plane QROM Loader (`HGadgetSympQromAux`)
`(60 + 2 * R + 2 * G)`-`T`, `0`-`TOFF`, `33 ≤ sScr` loader on `keep9Symp14Spec` (Babbush et al.,
*Phys. Rev. X* **8**, 041015, 2018; Gidney, *Quantum* **2**, 74, 2018; Low, Kliuchnikov, and
Schaeffer, *Quantum* **8**, 1375, 2024, DOI: `10.22331/q-2024-06-17-1375`). -/
namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.HGadgetSympQrom
open QuantumComputation.Specs QuantumComputation.Specs.P450
section HGadgetImpl
open Operator QProg Matrix Circuit Real HermitianMat BlockEncodingCore BlockEncodingCircuit
  QuantumComputation.Specs Solution QuantumComputation.Specs.P450 Solution CoherentAlias AliasPrep
  Solution.Mobius126OneHot MidReflCtxRetain StepBound148Borrow
  Tuned162ScheduledSympQrom21 Tuned162StepSympAnfQrom21 StepAnfAndCoin14Core StepKeep9Symp14Data
open Solution.StepOuter8Pi145Outer (predProj_mulVec_ket)
open _root_.Function (update update_of_ne update_self update_idem update_eq_self)
open Solution.CircuitModular.UnsignedGivens (evolve_CNOT_ket)
open Solution.GroupUnary (predProj predProj_conjTranspose)
open Solution.CompactOuterAlias (eval_h_mul_self)
open Solution.XMeasCircuit (ket_H sqrtHalf sqrtHalf_mul_sqrtHalf bitSign_zero xorWireUnitary
  xorWireUnitary_mulVec_ket phaseFlipUnitary phaseFlipUnitary_mulVec_ket xMeasUnloadWireDyn
  count_xMeasUnloadWireDyn_toff count_xMeasUnloadWireDyn_t wp_xMeasUnloadWireDyn_update_self
  cleanFinsetProj restrictAssertionToCleanFinset restrictAssertionToCleanFinset_coe
  restrictAssertionToCleanFinset_wp_xorWireUnitary_xMeasUnloadWireDyn)
open Solution.SelectSwapQROM (zeroProjOn zeroProjOn_mulVec_ket
  zeroProjOn_conjTranspose bitSign bitSign_add bit_cases basisBits_symm ket_Z czCircuit
  ket_czCircuit czMaskCircuit count_czMaskCircuit_toff count_czMaskCircuit_t ket_czMaskCircuit
  monoEval monoEval_zero anfCoeffs sum_anfCoeffs_mul_monoEval disjoint_image_of_disjointWires)
open scoped Matrix BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator Circuit.Notation
theorem ite_t {p : Prop} [Decidable p] {α} {a b : α} (h : p) : (if p then a else b) = a :=
  ite_eq_left h
theorem ite_f {p : Prop} [Decidable p] {α} {a b : α} (h : ¬p) : (if p then a else b) = b :=
  ite_eq_right h
theorem ket_sdk_eq {n : ℕ} (β : BitAssignment n) : Solution.XMeasCircuit.ket β =
  SelectSwapQROM.ket β := rfl
theorem bitSign_zero2 : bitSign 0 = 1 := rfl
/-- `Bool` to `ZMod 2`. -/
def b2z (b : Bool) : ZMod 2 := if b then 1 else 0
/-- `ZMod 2` to `Bool`. -/
def z2b (x : ZMod 2) : Bool := decide (x = 1)
theorem b2z_true : b2z true = 1 := rfl
theorem b2z_false : b2z false = 0 := rfl
theorem b2z_z2b (x : ZMod 2) : b2z (z2b x) = x := by rcases bit_cases x with rfl | rfl <;> rfl
theorem z2b_b2z (b : Bool) : z2b (b2z b) = b := by cases b <;> rfl
theorem b2z_xor (a b : Bool) : b2z (xor a b) = b2z a + b2z b := by cases a <;> cases b <;> rfl
theorem b2z_and (a b : Bool) : b2z (a && b) = b2z a * b2z b := by cases a <;> cases b <;> rfl
theorem b2z_xor_true (a : Bool) : b2z a + 1 = b2z (xor a true) := by cases a <;> rfl
theorem not_xor_left (a b : Bool) : xor (!a) b = !(xor a b) := by cases a <;> cases b <;> rfl
/-- 8th root `(1 + i) / √2`. -/
noncomputable def omega8C : ℂ := (1 + Complex.I) / (√2 : ℂ)
theorem omega8C_eq : omega8C = (1 + Complex.I) * sqrtHalf := by
  dsimp only [omega8C, sqrtHalf]
  have h2 : (√2 : ℂ) ≠ 0 := by exact_mod_cast Real.sqrt_ne_zero'.mpr (by norm_num)
  have hmul : (√(1 / 2 : ℝ) : ℂ) * (√2 : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, ← Real.sqrt_mul (by norm_num)]
    norm_num
  rw [div_eq_iff h2, mul_assoc, hmul, mul_one]
theorem sqrtHalf_sq_3 : sqrtHalf ^ 2 = 1 / 2 := by linear_combination sqrtHalf_mul_sqrtHalf
theorem i_pow3_2 : Complex.I ^ 3 = -Complex.I := by linear_combination Complex.I * Complex.I_sq
theorem i_pow4_2 : Complex.I ^ 4 = 1 := by linear_combination (Complex.I ^ 2 - 1) * Complex.I_sq
/-- Phase `i^b`. -/
noncomputable def bitPhaseI (b : ZMod 2) : ℂ := if b = 0 then 1 else Complex.I
/-- Phase `ω_8^b`. -/
noncomputable def bitPhaseT (b : ZMod 2) : ℂ := if b = 0 then 1 else omega8C
theorem eval_seq_mv {n : ℕ} (c₁ c₂ : Circuit n) (ψ : Fin (2 ^ n) → ℂ) : (c₁ ;;ᶜ c₂).eval.1.mulVec ψ
  = c₂.eval.1.mulVec (c₁.eval.1.mulVec ψ) := by
  rw [Circuit.eval_seq, Submonoid.coe_mul, ← mulVec_mulVec]
theorem ket_embedDiag1 {n : ℕ} (q : Wire n) (z : ℂ) (β : BitAssignment n) : ((QRegister.singleton
  q).embedMatrix (Matrix.diagonal fun i : Fin 2 ↦
    if i = 1 then z else 1)).mulVec (Solution.XMeasCircuit.ket β)
  = (if β q = 0 then 1 else z) • Solution.XMeasCircuit.ket β := by
  rw [Solution.XMeasCircuit.singleton_embedMatrix_mulVec_ket]
  have e := update_eq_self q β
  rcases bit_cases (β q) with hb | hb <;> rw [hb] at e <;> simp [hb, e]
theorem ket_S_3 {n : ℕ} (q : Wire n) (β : BitAssignment n) : (Circuit.S q).eval.1.mulVec
  (Solution.XMeasCircuit.ket β) = bitPhaseI (β q) • Solution.XMeasCircuit.ket β := by
  rw [Circuit.eval_single, QRegister.embedUnitary_val, PrimitiveGate.eval_s_val]
  exact ket_embedDiag1 q Complex.I β
theorem ket_T_3 {n : ℕ} (q : Wire n) (β : BitAssignment n) : (Circuit.T q).eval.1.mulVec
  (Solution.XMeasCircuit.ket β) = bitPhaseT (β q) • Solution.XMeasCircuit.ket β := by
  rw [Circuit.eval_single, QRegister.embedUnitary_val, PrimitiveGate.eval_t_val]
  exact ket_embedDiag1 q omega8C β
/-- Single-qubit `S† = Z ;; S` (`0 T`, `0 TOFF`). -/
def sDagC {n : ℕ} (q : Wire n) : Circuit n :=
  Circuit.Z q ;;ᶜ Circuit.S q
@[simp] theorem count_sDagCirc_toff {n : ℕ} (q : Wire n) : (sDagC q).count .TOFF = 0 := rfl
@[simp] theorem count_sDagCirc_t {n : ℕ} (q : Wire n) : (sDagC q).count .T = 0 := rfl
theorem ket_sDagCirc {n : ℕ} (q : Wire n) (β : BitAssignment n) : (sDagC q).eval.1.mulVec
  (Solution.XMeasCircuit.ket β) = (bitSign (β q) * bitPhaseI (β q)) •
      Solution.XMeasCircuit.ket β := by
  rw [sDagC, eval_seq_mv, ket_sdk_eq _, ket_Z, ← ket_sdk_eq _, mulVec_smul, ket_S_3, smul_smul]
/-- Single-qubit `T† = Z ;; S ;; T` (`1 T`, `0 TOFF`). -/
def tDagC {n : ℕ} (q : Wire n) : Circuit n
  := Circuit.Z q ;;ᶜ Circuit.S q ;;ᶜ Circuit.T q
@[simp] theorem count_tDagCirc_toff {n : ℕ} (q : Wire n) : (tDagC q).count .TOFF = 0 := rfl
@[simp] theorem count_tDagCirc_t {n : ℕ} (q : Wire n) : (tDagC q).count .T = 1 := rfl
theorem ket_tDagCirc {n : ℕ} (q : Wire n) (β : BitAssignment n) : (tDagC q).eval.1.mulVec
  (Solution.XMeasCircuit.ket β) = (bitSign (β q) * (bitPhaseI (β q) * bitPhaseT (β q))) •
    Solution.XMeasCircuit.ket β
  := by
  rw [tDagC, eval_seq_mv, eval_seq_mv, ket_sdk_eq _, ket_Z, ← ket_sdk_eq _, mulVec_smul, ket_S_3,
    mulVec_smul, mulVec_smul, ket_T_3, smul_smul, smul_smul, mul_assoc]
attribute [irreducible] sDagC tDagC
/-- Control wire bundled with non-aliasing proof `c ≠ t`. -/
abbrev CtrlWire (n : ℕ) (t : Wire n) :
  Type := { c : Wire n // c ≠ t }
/-- Affine Boolean form `(cbit, vars)` over `V`. -/
abbrev AffForm (V : Type) : Type := Bool × List
  V
/-- Pair of affine Boolean forms over `V`. -/
abbrev AffPair (V : Type) : Type := AffForm V ×
  AffForm V
/-- CNOT fan-in from typed control wires into target `t` (`0 T`, `0 TOFF`). -/
def pLinsC {n : ℕ} (t
  : Wire n) : List (CtrlWire n t) → Circuit n
  | [] => .identity
  | c :: cs => Circuit.CNOT c.1 t c.2 ;;ᶜ pLinsC t cs
/-- Affine parity step `pLinsC t lins` followed by `X t` when `cbit = true`. -/
def pStepC {n : ℕ}
  (t : Wire n) (cbit : Bool) (lins : List (CtrlWire n t)) : Circuit n := pLinsC t lins ;;ᶜ if cbit
  then Circuit.X t else .identity
/-- Signed Hadamard-gadget steps (`neg = false`: `T`, `neg = true`: `tDagC`). -/
def hSignC (neg :
  Bool) {n : ℕ} (t : Wire n) : List (AffForm (CtrlWire n t)) → Circuit n
  | [] => .identity
  | st :: sts => (pStepC t st.1 st.2 ;;ᶜ if neg then tDagC t else Circuit.T t) ;;ᶜ hSignC neg t sts
/-- Complete `(ps.length + ns.length)`-`T` Hadamard gadget on wire `t`. -/
def hGadC {n : ℕ} (t :
  Wire n) (ps ns : List (AffForm (CtrlWire n t))) (uc : Bool) (ul : List (CtrlWire n t)) : Circuit n
  := Circuit.H t ;;ᶜ (hSignC false t ps ;;ᶜ (hSignC true t ns ;;ᶜ (pStepC t uc ul ;;ᶜ (Circuit.H t
  ;;ᶜ sDagC t))))
@[simp] theorem count_parLinsCirc_toff {n} (t : Wire n) (ls) : (pLinsC t ls).count .TOFF = 0 := by
  induction ls with
  | nil => rfl
  | cons _ _ ih => simp [pLinsC, ih]
@[simp] theorem count_parLinsCirc_t {n} (t : Wire n) (ls) : (pLinsC t ls).count .T = 0 := by
  induction ls with
  | nil => rfl
  | cons _ _ ih => simp [pLinsC, ih]
@[simp] theorem count_parStepCirc_toff {n} (t : Wire n) (c ls) : (pStepC t c ls).count .TOFF = 0
  := by cases c <;> simp [pStepC]
@[simp] theorem count_parStepCirc_t {n} (t : Wire n) (c ls) : (pStepC t c ls).count .T = 0 := by
  cases c <;> simp [pStepC]
@[simp] theorem count_hSignCirc_toff (neg) {n} (t : Wire n) (sts) : (hSignC neg t sts).count .TOFF =
  0 := by
  induction sts with
  | nil => rfl
  | cons _ _ ih => cases neg <;> simp [hSignC, ih]
@[simp] theorem count_hSignCirc_t (neg) {n} (t : Wire n) (s) : (hSignC neg t s).count .T = s.length
  := by
  induction s with
  | nil => rfl
  | cons _ _ ih => cases neg <;> simp [hSignC, ih, Nat.add_comm 1]
@[simp] theorem count_hGadgetCirc_toff {n} (t : Wire n) (ps ns uc ul) : (hGadC t ps ns uc ul).count
  .TOFF = 0 := by simp [hGadC]
@[simp] theorem count_hGadgetCirc_t {n} (t : Wire n) (ps ns uc ul) : (hGadC t ps ns uc ul).count .T
  = ps.length + ns.length := by simp [hGadC]
/-- Mod-8 phase addition (`neg = false`: `+1`, `neg = true`: `+7`). -/
def addZ8 (neg s0 s1 s2 a :
  Bool) : Bool × Bool × Bool :=
  let c0 := s0 && a
  let s1_a := xor s1 c0
  let s2_a := xor s2 (s1 && c0)
  if neg then (xor s0 a, xor s1_a a, xor (xor s2_a (s1_a && a)) a) else (xor s0 a, s1_a, s2_a)
/-- Generic XOR of `f c` over `c ∈ lins`. -/
def evLin {α : Type} (f : α → Bool) : List α → Bool
  | [] => false
  | c :: cs => xor (f c) (evLin f cs)
/-- Generic affine parity `cbit ⊕ ⨁_{c ∈ lins} f c`. -/
def evStep {α : Type} (f : α → Bool) (st :
  AffForm α) : Bool := xor (evLin f st.2) st.1
/-- Run signed Hadamard-gadget steps on `(acc, (s0, s1, s2))`. -/
def runSignG (neg : Bool) {α :
  Type} (f : α → Bool) : List (AffForm α) → Bool → (Bool × Bool × Bool) → Bool × (Bool × Bool ×
  Bool)
  | [], acc, s => (acc, s)
  | st :: sts, acc, s =>
      let acc' := xor acc (evStep f st)
      runSignG neg f sts acc' (addZ8 neg s.1 s.2.1 s.2.2 acc')
/-- Evaluate `(acc, s0, s1, s2)` for a bundled Hadamard gadget. -/
def evalHGad {α : Type} (f : α →
  Bool) (ps ns : List (AffForm α)) (uc : Bool) (ul : List α) : Bool × Bool × Bool × Bool :=
  let r1 := runSignG false f ps false (false, false, false)
  let r2 := runSignG true f ns r1.1 r1.2
  (xor r2.1 (evStep f (uc, ul)), r2.2.1, r2.2.2.1, r2.2.2.2)
/-- Branch-`1` (`!acc'`) signed mod-8 phase accumulator. -/
def runSignB1 (neg : Bool) {α : Type} (f
  : α → Bool) : List (AffForm α) → Bool → (Bool × Bool × Bool) → Bool × Bool × Bool
  | [], _, p => p
  | st :: sts, acc, p =>
      let acc' := xor acc (evStep f st)
      runSignB1 neg f sts acc' (addZ8 neg p.1 p.2.1 p.2.2 (!acc'))
/-- 3-bit value `s0 + 2 * s1 + 4 * s2` in `ZMod 8`. -/
def val8 (s : Bool × Bool × Bool) : ZMod 8 :=
  (if s.1 then 1 else 0) + 2 * (if s.2.1 then 1 else 0) + 4 * (if s.2.2 then 1 else 0)
theorem val8_addZ8_sum (neg : Bool) (s p : Bool × Bool × Bool) (a : Bool) : val8 (addZ8 neg s.1
  s.2.1 s.2.2 a) + val8 (addZ8 neg p.1 p.2.1 p.2.2 (!a)) = val8 s + val8 p + if neg then 7 else 1
  := by
  rcases s with ⟨s0, s1, s2⟩
  rcases p with ⟨p0, p1, p2⟩
  revert neg s0 s1 s2 p0 p1 p2 a
  decide
theorem runSign_v8 (neg : Bool) {α : Type} (f : α → Bool) : ∀ (sts : List (AffForm α)) (acc : Bool)
  (s p : Bool × Bool × Bool), val8 (runSignG neg f sts acc s).2 + val8 (runSignB1 neg f sts acc p) =
  val8 s + val8 p + (if neg then 7 else 1) * (sts.length : ZMod 8)
  | [], _, _, _ => by simp [runSignG, runSignB1]
  | _ :: sts, _, _, _ => by
      simp only [runSignG, runSignB1, List.length_cons, runSign_v8 neg f sts, val8_addZ8_sum,
        Nat.cast_add, Nat.cast_one]
      ring
theorem neg_bits_val8 (s1 s2 : Bool) (p : Bool × Bool × Bool) (h : val8 (false, s1, s2) + val8 p =
  0) : p = (false, s1, xor s2 s1) := by
  rcases p with ⟨p0, p1, p2⟩
  revert s1 s2 p0 p1 p2 h
  decide
/-- 8th root of unity `ω_8^(s0 + 2 * s1 + 4 * s2)`. -/
noncomputable def omega8Bits (s : Bool × Bool
  × Bool) : ℂ := (if s.1 then omega8C else 1) * (if s.2.1 then Complex.I else 1) * (if s.2.2 then -1
  else 1)
/-- Two-branch Hadamard-gadget state on wire `t`. -/
noncomputable def hState {n : ℕ} (β :
  BitAssignment n) (t : Wire n) (acc : Bool) (s p : Bool × Bool × Bool) : Fin (2 ^ n) → ℂ :=
  sqrtHalf • (omega8Bits s • Solution.XMeasCircuit.ket (update β t (b2z acc)) + omega8Bits p •
    Solution.XMeasCircuit.ket
  (update β t (b2z (!acc))))
theorem ket_H_eq_hState {n : ℕ} (t : Wire n) (β : BitAssignment n) (ht0 : β t = 0) : (Circuit.H
  t).eval.1.mulVec (Solution.XMeasCircuit.ket β) = hState β t false (false, false, false) (false,
    false, false)
  := by
  rw [ket_H, ht0]
  simp [hState, omega8Bits, b2z, Solution.XMeasCircuit.bitSign]
theorem ket_parLinsCirc_upd {n} (t : Wire n) (ls β a) :
    (pLinsC t ls).eval.1.mulVec (Solution.XMeasCircuit.ket
  (update β t (b2z a))) = Solution.XMeasCircuit.ket (update β t (b2z (xor a (evLin (fun c ↦
    z2b (β c.1)) ls))))
  := by
  induction ls generalizing a with
  | nil => rw [pLinsC, Circuit.eval_identity, Submonoid.coe_one, one_mulVec, evLin, Bool.xor_false]
  | cons c _ ih =>
      rw [pLinsC, eval_seq_mv, evolve_CNOT_ket, update_self, update_of_ne c.2, update_idem, ←
        b2z_z2b (β c.1), ← b2z_xor, ih (xor a (z2b (β c.1))), evLin, Bool.xor_assoc]
theorem ket_parStepCirc_upd {n} (t : Wire n) (cbit ls β a) : (pStepC t cbit ls).eval.1.mulVec
  (Solution.XMeasCircuit.ket (update β t (b2z a))) =
    Solution.XMeasCircuit.ket (update β t (b2z (xor a (evStep (fun c ↦
  z2b (β c.1)) (cbit, ls))))) := by
  rw [pStepC, eval_seq_mv, ket_parLinsCirc_upd t ls β a]
  cases cbit
  · simp only [Bool.false_eq_true, ↓reduceIte, Circuit.eval_identity, Submonoid.coe_one, one_mulVec,
      evStep, Bool.xor_false]
  · simp only [↓reduceIte, Solution.XMeasCircuit.ket_X, update_self, update_idem, b2z_xor_true,
      evStep,
      Bool.xor_assoc]
theorem hState_parStepCirc {n} (t : Wire n) (cbit ls β acc s p) : (pStepC t cbit ls).eval.1.mulVec
  (hState β t acc s p) = hState β t (xor acc (evStep (fun c ↦ z2b (β c.1)) (cbit, ls))) s p := by
  simp only [hState, mulVec_smul, mulVec_add, ket_parStepCirc_upd, not_xor_left]
attribute [irreducible] pLinsC pStepC
theorem omega8_phase (neg : Bool) (s : Bool × Bool × Bool) (a : Bool) : omega8Bits s * (if neg then
  bitSign (b2z a) * (bitPhaseI (b2z a) * bitPhaseT (b2z a)) else bitPhaseT (b2z a)) = omega8Bits
  (addZ8 neg s.1 s.2.1 s.2.2 a) := by
  rcases s with ⟨s0, s1, s2⟩
  have hi2 : Complex.I ^ 2 = -1 := Complex.I_sq
  cases neg <;> cases s0 <;> cases s1 <;> cases s2 <;> cases a <;> simp only [addZ8, omega8Bits,
    bitSign, bitPhaseI, bitPhaseT, omega8C_eq, b2z, one_ne_zero, Bool.false_eq_true, Bool.not_false,
    ↓reduceIte, Bool.and_self, Bool.and_true, Bool.and_false, Bool.xor_self, Bool.true_xor,
    Bool.false_xor] <;> ring_nf <;> simp only [sqrtHalf_sq_3, hi2, i_pow3_2, i_pow4_2] <;> ring
theorem hState_phase (neg : Bool) {n : ℕ} (t : Wire n) (β : BitAssignment n) (acc : Bool) (s p :
  Bool × Bool × Bool) : (if neg then tDagC t else Circuit.T t).eval.1.mulVec (hState β t acc s p) =
  hState β t acc (addZ8 neg s.1 s.2.1 s.2.2 acc) (addZ8 neg p.1 p.2.1 p.2.2 (!acc)) := by
  have h0 := omega8_phase false
  have h1 := omega8_phase true
  simp only [Bool.false_eq_true, ↓reduceIte] at h0 h1
  cases neg <;> simp only [Bool.false_eq_true, ↓reduceIte, hState, mulVec_smul, mulVec_add,
    ket_T_3, ket_tDagCirc, update_self, smul_smul, h0, h1]
theorem hState_hSign (neg : Bool) {n : ℕ} (t : Wire n) (sts : List (AffForm (CtrlWire n t))) (β :
  BitAssignment n) (acc : Bool) (s p : Bool × Bool × Bool) : (hSignC neg t sts).eval.1.mulVec
  (hState β t acc s p) = hState β t (runSignG neg (fun c ↦ z2b (β c.1)) sts acc s).1 (runSignG neg
  (fun c ↦ z2b (β c.1)) sts acc s).2 (runSignB1 neg (fun c ↦ z2b (β c.1)) sts acc p) := by
  induction sts generalizing acc s p with
  | nil => rw [hSignC, Circuit.eval_identity, Submonoid.coe_one, one_mulVec, runSignG, runSignB1]
  | cons _ _ ih => simp only [hSignC, eval_seq_mv, hState_parStepCirc, hState_phase, ih, runSignG,
      runSignB1]
attribute [irreducible] hSignC
theorem ket_HsDag_hState {n : ℕ} (t : Wire n) (β : BitAssignment n) (s1 s2 : Bool) : (Circuit.H t
  ;;ᶜ sDagC t).eval.1.mulVec (hState β t false (false, s1, s2) (false, s1, xor s2 s1)) = bitSign
  (b2z s2) • Solution.XMeasCircuit.ket (update β t (b2z s1)) := by
  have hk0 : (sDagC t).eval.1.mulVec (Solution.XMeasCircuit.ket (update β t 0)) =
    Solution.XMeasCircuit.ket (update β t 0)
    := by
    rw [ket_sDagCirc, update_self]
    simp [bitSign, bitPhaseI]
  have hk1 : (sDagC t).eval.1.mulVec (Solution.XMeasCircuit.ket (update β t 1)) = (-Complex.I) •
    Solution.XMeasCircuit.ket
    (update β t 1) := by
    rw [ket_sDagCirc, update_self]
    simp [bitSign, bitPhaseI]
  rw [eval_seq_mv, hState]
  simp only [b2z, Bool.false_eq_true, Bool.not_false, ↓reduceIte, mulVec_smul, mulVec_add, ket_H,
    update_self, update_idem, Solution.XMeasCircuit.bitSign, one_ne_zero, hk0, hk1]
  have hi2 : Complex.I ^ 2 = -1 := Complex.I_sq
  cases s1 <;> cases s2 <;> ext i <;> simp only [omega8Bits, bitSign, Bool.false_eq_true,
    Bool.xor_false, Bool.xor_true, Bool.not_false, Bool.not_true,
    ↓reduceIte, one_ne_zero, Pi.add_apply, Pi.smul_apply, smul_eq_mul] <;> ring_nf <;> simp only
    [sqrtHalf_sq_3, hi2] <;> ring
theorem ket_hGad_zero {n : ℕ} (t : Wire n) (ps ns : List (AffForm (CtrlWire n t))) (uc : Bool) (ul :
  List (CtrlWire n t)) (hlen : (ps.length : ZMod 8) + 7 * (ns.length : ZMod 8) = 0) (β :
  BitAssignment n) (ht0 : β t = 0) (hacc : (evalHGad (fun c ↦ z2b (β c.1)) ps ns uc ul).1 = false)
  (hs0 : (evalHGad (fun c ↦ z2b (β c.1)) ps ns uc ul).2.1 = false) : (hGadC t ps ns uc
  ul).eval.1.mulVec (Solution.XMeasCircuit.ket β) = bitSign (b2z (evalHGad (fun c ↦
    z2b (β c.1)) ps ns uc
  ul).2.2.2) • Solution.XMeasCircuit.ket (update β t (b2z (evalHGad (fun c ↦
    z2b (β c.1)) ps ns uc ul).2.2.1))
  := by
  let f := fun c : CtrlWire n t ↦ z2b (β c.1)
  let r1 := runSignG false f ps false (false, false, false)
  let p1 := runSignB1 false f ps false (false, false, false)
  let r2 := runSignG true f ns r1.1 r1.2
  let p2 := runSignB1 true f ns r1.1 p1
  let ev := evalHGad f ps ns uc ul
  have hr2 : r2.2 = (false, ev.2.2.1, ev.2.2.2) := Prod.ext hs0 (Prod.ext rfl rfl)
  have hp2 : p2 = (false, ev.2.2.1, xor ev.2.2.2 ev.2.2.1) := by
    apply neg_bits_val8
    rw [← hr2]
    dsimp only [r2, p2, r1, p1]
    rw [runSign_v8, runSign_v8]
    simp only [Bool.false_eq_true, ↓reduceIte, one_mul]
    have hv0 : val8 (false, false, false) = 0 := rfl
    rw [hv0, zero_add, zero_add]
    exact hlen
  have hundo : xor r2.1 (evStep f (uc, ul)) = false := hacc
  unfold hGadC
  rw [eval_seq_mv, eval_seq_mv, eval_seq_mv, eval_seq_mv, ket_H_eq_hState t β ht0, hState_hSign,
    hState_hSign, hState_parStepCirc]
  change (Circuit.H t ;;ᶜ sDagC t).eval.1.mulVec (hState β t (xor r2.1 (evStep f (uc, ul))) r2.2 p2)
    = _
  rw [hundo, hr2, hp2]
  exact ket_HsDag_hState t β ev.2.2.1 ev.2.2.2
attribute [irreducible] hGadC
/-- CZ fan-out from `lins` to `t` (`0 T`). -/
def czLinsC {n : ℕ} (t : Wire n) : List (CtrlWire n t)
  → Circuit n
  | [] => .identity
  | c :: cs => czCircuit c.1 t c.2 ;;ᶜ czLinsC t cs
/-- Affine CZ phase on `t` (`0 T`). -/
def czStepC {n : ℕ} (t : Wire n) (cbit : Bool) (lins : List
  (CtrlWire n t)) : Circuit n := czLinsC t lins ;;ᶜ if cbit then Circuit.Z t else .identity
@[simp] theorem count_czLinsCirc_toff {n} (t : Wire n) (ls) : (czLinsC t ls).count .TOFF = 0 := by
  induction ls with
  | nil => rfl
  | cons _ _ ih => simp [czLinsC, ih]
@[simp] theorem count_czLinsCirc_t {n} (t : Wire n) (ls) : (czLinsC t ls).count .T = 0 := by
  induction ls with
  | nil => rfl
  | cons _ _ ih => simp [czLinsC, ih]
@[simp] theorem count_czStepCirc_toff {n} (t : Wire n) (c ls) : (czStepC t c ls).count .TOFF = 0
  := by cases c <;> simp [czStepC]
@[simp] theorem count_czStepCirc_t {n} (t : Wire n) (c ls) : (czStepC t c ls).count .T = 0 := by
  cases c <;> simp [czStepC]
theorem ket_czLins_upd {n} (t : Wire n) (ls β a) :
    (czLinsC t ls).eval.1.mulVec (Solution.XMeasCircuit.ket
  (update β t (b2z a))) = bitSign (b2z (a && evLin (fun c ↦
    z2b (β c.1)) ls)) • Solution.XMeasCircuit.ket
  (update β t (b2z a)) := by
  induction ls with
  | nil =>
      rw [czLinsC, Circuit.eval_identity, Submonoid.coe_one, one_mulVec, evLin, Bool.and_false,
        b2z_false, bitSign_zero2, one_smul]
  | cons c cs ih =>
      rw [czLinsC, eval_seq_mv, ket_sdk_eq _, ket_czCircuit, ← ket_sdk_eq _, mulVec_smul, ih,
        smul_smul, ← bitSign_add, update_of_ne c.2, update_self, ← b2z_z2b (β c.1)]
      have hmul : b2z (z2b (β c.1)) * b2z a + b2z (a && evLin (fun d ↦ z2b (β d.1)) cs) = b2z (a &&
        evLin (fun d ↦ z2b (β d.1)) (c :: cs)) := by
        dsimp only [evLin]
        cases a <;> cases z2b (β c.1) <;> cases evLin (fun d ↦ z2b (β d.1)) cs <;> decide
      rw [hmul]
theorem ket_czStep_upd {n} (t : Wire n) (cbit ls β a) : (czStepC t cbit ls).eval.1.mulVec
  (Solution.XMeasCircuit.ket (update β t (b2z a))) = bitSign (b2z (a && evStep (fun c ↦
    z2b (β c.1)) (cbit,
  ls))) • Solution.XMeasCircuit.ket (update β t (b2z a)) := by
  rw [czStepC, eval_seq_mv, ket_czLins_upd, mulVec_smul]
  cases cbit
  · simp only [Bool.false_eq_true, ↓reduceIte, Circuit.eval_identity, Submonoid.coe_one, one_mulVec,
      evStep, Bool.xor_false]
  · simp only [↓reduceIte]
    rw [ket_sdk_eq _, ket_Z, ← ket_sdk_eq _, update_self, smul_smul, ←
      bitSign_add, evStep]
    have hmul : b2z (a && evLin (fun d ↦ z2b (β d.1)) ls) + b2z a = b2z (a && xor (evLin (fun d ↦
      z2b (β d.1)) ls) true) := by cases a <;> cases evLin (fun d ↦ z2b (β d.1)) ls <;> decide
    rw [hmul]
attribute [irreducible] czLinsC czStepC
/-- Toggle variable `v` in a duplicate-free linear-form list mod 2. -/
def togVar {V : Type}
  [DecidableEq V] (v : V) : List V → List V
  | [] => [v]
  | x :: xs => if v = x then xs else x :: togVar v xs
/-- Symmetric-difference XOR of two linear-form variable lists. -/
def xorLin {V : Type}
  [DecidableEq V] (l1 l2 : List V) : List V := l1.foldr togVar l2
/-- Zero affine form `(false, [])`. -/
def zeroAff {V : Type} : AffForm V := (false, [])
/-- Pointwise XOR of two affine forms over `V`. -/
def xorAff {V : Type} [DecidableEq V] (a b :
  AffForm V) : AffForm V := (xor a.1 b.1, xorLin a.2 b.2)
theorem evalLin_toggle {V : Type} [DecidableEq V] (f : V → Bool) (v : V) : ∀ l : List V, evLin f
  (togVar v l) = xor (f v) (evLin f l)
  | [] => by simp [togVar, evLin]
  | x :: xs => by
      dsimp only [togVar]
      by_cases h : v = x
      · subst h
        simp only [↓reduceIte, evLin, ← Bool.xor_assoc, Bool.xor_self, Bool.false_xor]
      · simp only [h, ↓reduceIte, evLin, evalLin_toggle f v xs, ← Bool.xor_assoc, Bool.xor_comm (f
          v) (f x)]
theorem evalLin_xorLin {V : Type} [DecidableEq V] (f : V → Bool) : ∀ l1 l2 : List V, evLin f (xorLin
  l1 l2) = xor (evLin f l1) (evLin f l2)
  | [], _ => by simp [xorLin, evLin]
  | x :: xs, l2 => by
      change evLin f (togVar x (xorLin xs l2)) = _
      rw [evalLin_toggle, evalLin_xorLin f xs l2, evLin, Bool.xor_assoc]
theorem evalStep_xorAff {V : Type} [DecidableEq V] (f : V → Bool) (a b : AffForm V) : evStep f
  (xorAff a b) = xor (evStep f a) (evStep f b) := by
  dsimp only [evStep, xorAff]
  rw [evalLin_xorLin]
  cases evLin f a.2 <;> cases evLin f b.2 <;> cases a.1 <;> cases b.1 <;> rfl
/-- Positive target parities `(pref ⊕ u_k) ⊕ v_k` for telescoping Lempel schedule. -/
def posTail {V
  : Type} [DecidableEq V] (pref : AffForm V) : List (AffPair V) → List (AffForm V)
  | [] => []
  | (u, v) :: ps => xorAff (xorAff pref u) v :: posTail (xorAff pref u) ps
/-- Negative target parities `pref ⊕ v_k` for telescoping Lempel schedule. -/
def negTail {V : Type}
  [DecidableEq V] (pref : AffForm V) : List (AffPair V) → List (AffForm V)
  | [] => []
  | (u, v) :: ps => xorAff pref v :: negTail (xorAff pref u) ps
/-- Total `u`-sum `pref ⊕ u_0 ⊕ ... ⊕ u_{r-1}`. -/
def sumU {V : Type} [DecidableEq V] (pref :
  AffForm V) : List (AffPair V) → AffForm V
  | [] => pref
  | (u, _) :: ps => sumU (xorAff pref u) ps
/-- Convert target parities into sequential delta steps from `prev`. -/
def dFrom {V : Type}
  [DecidableEq V] (prev : AffForm V) : List (AffForm V) → List (AffForm V)
  | [] => []
  | t :: ts => xorAff prev t :: dFrom t ts
/-- Final accumulated parity after `dFrom prev ts`. -/
def lastFrom {V : Type} (prev : AffForm V) :
  List (AffForm V) → AffForm V
  | [] => prev
  | t :: ts => lastFrom t ts
/-- `(2r + 2)`-`T` Lempel gadget schedule `(pos, neg, undo)`. -/
def lempelSch {V : Type}
  [DecidableEq V] (pairs : List (AffPair V)) : List (AffForm V) × List (AffForm V) × AffForm V :=
  (dFrom zeroAff (zeroAff :: posTail zeroAff pairs), dFrom (lastFrom zeroAff (zeroAff :: posTail
  zeroAff pairs)) (sumU zeroAff pairs :: negTail zeroAff pairs), lastFrom (lastFrom zeroAff (zeroAff
  :: posTail zeroAff pairs)) (sumU zeroAff pairs :: negTail zeroAff pairs))
theorem len_pos {V : Type} [DecidableEq V] : ∀ (pref : AffForm V) (ps : List (AffPair V)), (posTail
  pref ps).length = ps.length
  | _, [] => rfl
  | pref, (u, _) :: ps => by simp [posTail, len_pos (xorAff pref u) ps]
theorem len_neg {V : Type} [DecidableEq V] : ∀ (pref : AffForm V) (ps : List (AffPair V)), (negTail
  pref ps).length = ps.length
  | _, [] => rfl
  | pref, (u, _) :: ps => by simp [negTail, len_neg (xorAff pref u) ps]
theorem len_deltas {V : Type} [DecidableEq V] : ∀ (prev : AffForm V) (ts : List (AffForm V)), (dFrom
  prev ts).length = ts.length
  | _, [] => rfl
  | _, t :: ts => by simp [dFrom, len_deltas t ts]
theorem lempel_lens {V : Type} [DecidableEq V] (pairs : List (AffPair V)) : (lempelSch
  pairs).1.length = pairs.length + 1 ∧ (lempelSch pairs).2.1.length = pairs.length + 1 := by
  simp [lempelSch, len_deltas, len_pos, len_neg]
/-- Map an affine form across `emb : V → α`. -/
def mapAff {V α : Type} (emb : V → α) (a : AffForm
  V) : AffForm α := (a.1, a.2.map emb)
/-- Embed `Bool` into `ZMod 4` as `0` or `1`. -/
def b4 (b : Bool) : ZMod 4 := if b then 1 else 0
/-- 2-bit projection `s0 + 2 * s1` in `ZMod 4`. -/
def val4 (s : Bool × Bool × Bool) : ZMod 4 := b4
  s.1 + 2 * b4 s.2.1
/-- Sum of `b4 (evStep f t)` over a target list `ts`. -/
def sumB4 {V : Type} (f : V → Bool) : List
  (AffForm V) → ZMod 4
  | [] => 0
  | t :: ts => b4 (evStep f t) + sumB4 f ts
/-- Boolean inner product over `pairs`. -/
def xorPairs {V : Type} (f : V → Bool) : List (AffPair V)
  → Bool
  | [] => false
  | (u, v) :: ps => xor (evStep f u && evStep f v) (xorPairs f ps)
theorem val4_addZ8 (neg : Bool) (s : Bool × Bool × Bool) (a : Bool) : val4 (addZ8 neg s.1 s.2.1
  s.2.2 a) = val4 s + (if neg then -1 else 1) * b4 a := by
  rcases s with ⟨s0, s1, s2⟩
  revert neg s0 s1 s2 a
  decide
theorem runSign_deltas (neg : Bool) {V : Type} [DecidableEq V] (f : V → Bool) : ∀ (ts : List
  (AffForm V)) (prev : AffForm V) (s : Bool × Bool × Bool), (runSignG neg f (dFrom prev ts) (evStep
  f prev) s).1 = evStep f (lastFrom prev ts) ∧ val4 (runSignG neg f (dFrom prev ts) (evStep f prev)
  s).2 = val4 s + (if neg then -1 else 1) * sumB4 f ts
  | [], _, _ => ⟨rfl, by simp [runSignG, dFrom, sumB4]⟩
  | t :: ts, prev, s => by
      have hxor : xor (evStep f prev) (evStep f (xorAff prev t)) = evStep f t := by
        rw [evalStep_xorAff, ← Bool.xor_assoc, Bool.xor_self, Bool.false_xor]
      simp only [dFrom, runSignG, hxor, lastFrom, sumB4]
      obtain ⟨h1, h2⟩ := runSign_deltas neg f ts t (addZ8 neg s.1 s.2.1 s.2.2 (evStep f t))
      refine ⟨h1, ?_⟩
      rw [h2, val4_addZ8]
      ring
theorem b4_two_xor (a b : Bool) : 2 * b4 (xor a b) = 2 * b4 a + 2 * b4 b := by
  revert a b
  decide
theorem b4_step_telescope (p u v : Bool) : b4 (xor (xor p u) v) - b4 (xor p v) = b4 (xor p u) - b4 p
  + 2 * b4 (u && v) := by
  revert p u v
  decide
theorem sumB4_pos_neg {V : Type} [DecidableEq V] (f : V → Bool) : ∀ (ps : List (AffPair V)) (pref :
  AffForm V), sumB4 f (posTail pref ps) - sumB4 f (negTail pref ps) = b4 (evStep f (sumU pref ps)) -
  b4 (evStep f pref) + 2 * b4 (xorPairs f ps)
  | [], _ => by
      simp only [posTail, negTail, sumU, sumB4, xorPairs, sub_self, show b4 false = 0 from rfl,
        mul_zero, add_zero]
  | (u, v) :: ps, pref => by
      simp only [posTail, negTail, sumU, sumB4, xorPairs]
      have ih := sumB4_pos_neg f ps (xorAff pref u)
      have htel := b4_step_telescope (evStep f pref) (evStep f u) (evStep f v)
      simp only [evalStep_xorAff] at ih ⊢
      rw [b4_two_xor]
      linear_combination ih + htel
theorem bits_of_val4 (s : Bool × Bool × Bool) (y : Bool) (h : val4 s = 2 * b4 y) : s.1 = false ∧
  s.2.1 = y := by
  rcases s with ⟨s0, s1, s2⟩
  revert s0 s1 s2 y h
  decide
theorem evalHGad_lempel {V : Type} [DecidableEq V] (f : V → Bool) (pairs : List (AffPair V)) :
  (evalHGad f (lempelSch pairs).1 (lempelSch pairs).2.1 (lempelSch pairs).2.2.1 (lempelSch
  pairs).2.2.2).1 = false ∧ (evalHGad f (lempelSch pairs).1 (lempelSch pairs).2.1 (lempelSch
  pairs).2.2.1 (lempelSch pairs).2.2.2).2.1 = false ∧ (evalHGad f (lempelSch pairs).1 (lempelSch
  pairs).2.1 (lempelSch pairs).2.2.1 (lempelSch pairs).2.2.2).2.2.1 = xorPairs f pairs := by
  dsimp only [lempelSch, evalHGad]
  set pTgts := zeroAff :: posTail zeroAff pairs
  set nTgts := sumU zeroAff pairs :: negTail zeroAff pairs
  set r1 := runSignG false f (dFrom zeroAff pTgts) false (false, false, false)
  set r2 := runSignG true f (dFrom (lastFrom zeroAff pTgts) nTgts) r1.1 r1.2
  obtain ⟨hp1, hp2⟩ := runSign_deltas false f pTgts zeroAff (false, false, false)
  change r1.1 = evStep f (lastFrom zeroAff pTgts) at hp1
  change val4 r1.2 = val4 (false, false, false) + (if false then -1 else 1) * sumB4 f pTgts at hp2
  obtain ⟨hn1, hn2⟩ := runSign_deltas true f nTgts (lastFrom zeroAff pTgts) r1.2
  rw [← hp1] at hn1 hn2
  change r2.1 = evStep f (lastFrom (lastFrom zeroAff pTgts) nTgts) at hn1
  change val4 r2.2 = val4 r1.2 + (if true then -1 else 1) * sumB4 f nTgts at hn2
  simp only [Bool.false_eq_true, ↓reduceIte, one_mul, neg_one_mul] at hp2 hn2
  have hacc : xor r2.1 (evStep f (lastFrom (lastFrom zeroAff pTgts) nTgts)) = false := by
    rw [hn1, Bool.xor_self]
  have hv4 : val4 r2.2 = 2 * b4 (xorPairs f pairs) := by
    have hv0 : val4 (false, false, false) = 0 := rfl
    have hb0 : b4 (evStep f zeroAff) = 0 := rfl
    rw [hn2, hp2, hv0, zero_add, ← sub_eq_add_neg]
    dsimp only [pTgts, nTgts, sumB4]
    have htel := sumB4_pos_neg f pairs zeroAff
    rw [hb0] at htel ⊢
    linear_combination htel
  obtain ⟨hs0, hs1⟩ := bits_of_val4 r2.2 (xorPairs f pairs) hv4
  exact ⟨hacc, hs0, hs1⟩
theorem evalLinGen_map {V α : Type} (f : α → Bool) (emb : V → α) : ∀ l : List V, evLin f (l.map emb)
  = evLin (f ∘ emb) l
  | [] => rfl
  | _ :: xs => by simp [evLin, evalLinGen_map f emb xs]
theorem evalStep_map {V α : Type} (f : α → Bool) (emb : V → α) (a : AffForm V) : evStep f (mapAff
  emb a) = evStep (f ∘ emb) a := by
  dsimp only [evStep, mapAff]
  rw [evalLinGen_map]
theorem runSignG_map (neg : Bool) {V α : Type} (f : α → Bool) (emb : V → α) : ∀ (sts : List (AffForm
  V)) (acc : Bool) (s : Bool × Bool × Bool), runSignG neg f (sts.map (mapAff emb)) acc s = runSignG
  neg (f ∘ emb) sts acc s
  | [], _, _ => rfl
  | _ :: sts, _, _ => by simp [runSignG, evalStep_map, runSignG_map neg f emb sts]
theorem evalHGad_map {V α : Type} (f : α → Bool) (emb : V → α) (pos neg : List (AffForm V)) (undo :
  AffForm V) : evalHGad f (pos.map (mapAff emb)) (neg.map (mapAff emb)) undo.1 (undo.2.map emb) =
  evalHGad (f ∘ emb) pos neg undo.1 undo.2 := by
  simp only [evalHGad, runSignG_map]
  rw [← evalStep_map f emb undo]
  rfl
theorem xorPairs_map {V α : Type} (f : α → Bool) (emb : V → α) : ∀ ps : List (AffPair V), xorPairs f
  (ps.map fun p ↦ (mapAff emb p.1, mapAff emb p.2)) = xorPairs (f ∘ emb) ps
  | [] => rfl
  | _ :: ps => by simp [xorPairs, evalStep_map, xorPairs_map f emb ps]
/-- `0-T` phase `(-1)^{xorPairs}` via clean wire `t`. -/
def andPairsC {n : ℕ} (t : Wire n) : List
  (AffPair (CtrlWire n t)) → Circuit n
  | [] => .identity
  | (u, v) :: ps => (pStepC t u.1 u.2 ;;ᶜ czStepC t v.1 v.2 ;;ᶜ pStepC t u.1 u.2) ;;ᶜ andPairsC t ps
@[simp] theorem count_andPairsCirc_toff {n} (t : Wire n) (ps) : (andPairsC t ps).count .TOFF = 0
  := by
  induction ps with
  | nil => rfl
  | cons _ _ ih => simp [andPairsC, ih]
@[simp] theorem count_andPairsCirc_t {n} (t : Wire n) (ps) : (andPairsC t ps).count .T = 0 := by
  induction ps with
  | nil => rfl
  | cons _ _ ih => simp [andPairsC, ih]
theorem ket_andPairsCirc_zero {n : ℕ} (t : Wire n) (ps : List (AffPair (CtrlWire n t))) (β :
  BitAssignment n) (ht0 : β t = 0) : (andPairsC t ps).eval.1.mulVec (Solution.XMeasCircuit.ket β) =
    bitSign
  (b2z (xorPairs (fun c ↦ z2b (β c.1)) ps)) • Solution.XMeasCircuit.ket β := by
  induction ps with
  | nil =>
      rw [andPairsC, Circuit.eval_identity, Submonoid.coe_one, one_mulVec, xorPairs, b2z_false,
        bitSign_zero2, one_smul]
  | cons p _ ih =>
      rcases p with ⟨_, _⟩
      have hβ0 : update β t (b2z false) = β := by rw [b2z_false, ← ht0, update_eq_self]
      rw [andPairsC, eval_seq_mv, eval_seq_mv, eval_seq_mv, ← hβ0, ket_parStepCirc_upd,
        Bool.false_xor, ket_czStep_upd, mulVec_smul, ket_parStepCirc_upd, Bool.xor_self, hβ0,
        mulVec_smul, ih, smul_smul, ← bitSign_add, ← b2z_xor, xorPairs]
attribute [irreducible] andPairsC
/-- `126` row + `31` ANF monomial variable indices. -/
abbrev Var157 : Type := Sum (Fin 126) (Fin
  31)
/-- Map `Var157` to its physical wire in `(rH, rM)`. -/
def vWire {N : ℕ} (rH : QRegister 128 N) (rM
  : QRegister 31 N) : Var157 → Wire N
  | .inl j => rH ⟨j.val, by omega⟩
  | .inr u => rM u
/-- Map `Var157` to a typed `CtrlWire N t` disjoint from target `t`. -/
def vCtrl {N : ℕ} (rH :
  QRegister 128 N) (rM : QRegister 31 N) (t : Wire N) (hHT : ∀ c : Fin 128, rH c ≠ t) (hMT : ∀ u :
  Fin 31, rM u ≠ t) : Var157 → CtrlWire N t
  | .inl j => ⟨rH ⟨j.val, by omega⟩, hHT ⟨j.val, by omega⟩⟩
  | .inr u => ⟨rM u, hMT u⟩
/-- Ideal Boolean value of `Var157` on sector `(rc : Fin 128, x : Fin (2 ^ 5))`. -/
def idEnv (rc :
  Fin 128) (x : Fin (2 ^ 5)) : Var157 → Bool
  | .inl j => decide (j.val = rc.val)
  | .inr u => z2b (monoEval 5 (basisBits 5 x) ⟨u.val + 1, by omega⟩)
/-- ANF coefficients of `extCol24Bool colMask` over `5`-bit column index `x`. -/
def colMaskAnf
  (colMask : Fin 30 → Bool) : Fin 32 → ZMod 2 := anfCoeffs 5 (fun x ↦ b2z (extCol24Bool colMask x))
/-- Prefix list of active row variables `j < m` with `rowMask j = true`. -/
def rowVars (rowMask :
  Fin 126 → Bool) : (m : ℕ) → m ≤ 126 → List Var157
  | 0, _ => []
  | m + 1, hm =>
      if rowMask ⟨m, hm⟩ then Sum.inl ⟨m, hm⟩ :: rowVars rowMask m (Nat.le_of_succ_le hm)
      else rowVars rowMask m (Nat.le_of_succ_le hm)
/-- Prefix list of non-constant ANF variables `u < m` with `colAnf (u + 1) = 1`. -/
def monoVars
  (colAnf : Fin 32 → ZMod 2) : (m : ℕ) → m ≤ 31 → List Var157
  | 0, _ => []
  | m + 1, hm =>
      if z2b (colAnf ⟨m + 1, by omega⟩) then
        Sum.inr ⟨m, hm⟩ :: monoVars colAnf m (Nat.le_of_succ_le hm)
      else monoVars colAnf m (Nat.le_of_succ_le hm)
/-- Affine `Var157` form for `(rowMask, colMask)`. -/
def rcColAff (rowMask : Fin 126 → Bool)
  (colMask : Fin 30 → Bool) : AffForm Var157 := (z2b (colMaskAnf colMask ⟨0, by decide⟩), rowVars
  rowMask 126 le_rfl ++ monoVars (colMaskAnf colMask) 31 le_rfl)
theorem evalLin_append {α : Type} (f : α → Bool) : ∀ l1 l2 : List α, evLin f (l1 ++ l2) = xor (evLin
  f l1) (evLin f l2)
  | [], _ => by simp [evLin]
  | _ :: xs, l2 => by simp [evLin, evalLin_append f xs l2]
theorem b2z_rowVars (rowMask : Fin 126 → Bool) (f : Var157 → Bool) : ∀ (m : ℕ) (hm : m ≤ 126), b2z
  (evLin f (rowVars rowMask m hm)) = ∑ j : Fin m, b2z (rowMask ⟨j.val, j.isLt.trans_le hm⟩) * b2z (f
  (Sum.inl ⟨j.val, j.isLt.trans_le hm⟩))
  | 0, _ => rfl
  | m + 1, hm => by
      rw [Fin.sum_univ_castSucc]
      dsimp only [rowVars]
      by_cases hr : rowMask ⟨m, hm⟩
      · simp only [hr, ↓reduceIte, evLin, b2z_xor, Fin.val_castSucc, Fin.val_last, b2z_true,
          one_mul, b2z_rowVars rowMask f m (Nat.le_of_succ_le hm)]
        exact add_comm _ _
      · simp only [hr, Bool.false_eq_true, ↓reduceIte, Fin.val_castSucc, Fin.val_last, b2z_false,
          zero_mul, add_zero, b2z_rowVars rowMask f m (Nat.le_of_succ_le hm)]
theorem b2z_monoVars (colAnf : Fin 32 → ZMod 2) (f : Var157 → Bool) : ∀ (m : ℕ) (hm : m ≤ 31), b2z
  (evLin f (monoVars colAnf m hm)) = ∑ u : Fin m, colAnf ⟨u.val + 1, Nat.succ_lt_succ
  (u.isLt.trans_le hm)⟩ * b2z (f (Sum.inr ⟨u.val, u.isLt.trans_le hm⟩))
  | 0, _ => rfl
  | m + 1, hm => by
      rw [Fin.sum_univ_castSucc]
      dsimp only [monoVars]
      set c := colAnf ⟨m + 1, by omega⟩
      by_cases hc : z2b c
      · simp only [hc, ↓reduceIte, evLin, b2z_xor, Fin.val_castSucc, Fin.val_last, b2z_monoVars
          colAnf f m (Nat.le_of_succ_le hm)]
        change b2z (f _) + _ = _ + c * b2z (f _)
        rw [of_decide_eq_true hc, one_mul, add_comm]
      · have hc0 : c = 0 := (bit_cases c).elim id fun h1 ↦ False.elim (hc (decide_eq_true h1))
        simp only [hc, Bool.false_eq_true, ↓reduceIte, Fin.val_castSucc, Fin.val_last, b2z_monoVars
          colAnf f m (Nat.le_of_succ_le hm)]
        change _ = _ + c * _
        rw [hc0, zero_mul, add_zero]
theorem anf5_decomp (g : Fin (2 ^ 5) → ZMod 2) (x : Fin (2 ^ 5)) : anfCoeffs 5 g ⟨0, by decide⟩ + (∑
  u : Fin 31, anfCoeffs 5 g ⟨u.val + 1, by omega⟩ * monoEval 5 (basisBits 5 x) ⟨u.val + 1,
  by omega⟩) = g x := by
  have hsum := sum_anfCoeffs_mul_monoEval 5 g (basisBits 5 x)
  rw [Solution.XMeasCircuit.basisBitsEquiv_symm_basisBits x] at hsum
  have hsp : (∑ i : Fin (2 ^ 5), anfCoeffs 5 g i * monoEval 5 (basisBits 5 x) i) = anfCoeffs 5 g ⟨0,
    by decide⟩ * monoEval 5 (basisBits 5 x) ⟨0, by decide⟩ + ∑ u : Fin 31, anfCoeffs 5 g ⟨u.val + 1,
    by omega⟩ * monoEval 5 (basisBits 5 x) ⟨u.val + 1, by omega⟩ := Fin.sum_univ_succ (n := 31) (fun
    i : Fin 32 ↦ anfCoeffs 5 g i * monoEval 5 (basisBits 5 x) i)
  have hm0 : monoEval 5 (basisBits 5 x) ⟨0, by decide⟩ = 1 := monoEval_zero 5 (basisBits 5 x)
  rw [hsp, hm0, mul_one] at hsum
  exact hsum
theorem evalStep_rcColAff (rowMask : Fin 126 → Bool) (colMask : Fin 30 → Bool) (rc : Fin 128) (x :
  Fin (2 ^ 5)) : evStep (idEnv rc x) (rcColAff rowMask colMask) = xor (if h : rc.val < 126 then
  rowMask ⟨rc.val, h⟩ else false) (extCol24Bool colMask x) := by
  rw [← z2b_b2z (evStep _ _), ← z2b_b2z (xor _ _)]
  congr 1
  dsimp only [evStep, rcColAff]
  rw [b2z_xor, evalLin_append, b2z_xor, b2z_z2b, b2z_rowVars, b2z_monoVars, b2z_xor]
  have hrow : (∑ j : Fin 126, b2z (rowMask j) * b2z (idEnv rc x (Sum.inl j))) = b2z (if h : rc.val <
    126 then rowMask ⟨rc.val, h⟩ else false) := by
    by_cases hrc : rc.val < 126
    · simp only [hrc, ↓reduceDIte]
      rw [Finset.sum_eq_single ⟨rc.val, hrc⟩]
      · simp [idEnv, b2z]
      · intro j _ hj
        have hne : j.val ≠ rc.val := fun hv ↦ hj (Fin.ext hv)
        simp [idEnv, hne, b2z]
      · intro h
        exact False.elim (h (Finset.mem_univ _))
    · simp only [hrc, ↓reduceDIte, b2z, Bool.false_eq_true, ↓reduceIte]
      refine Finset.sum_eq_zero fun j _ ↦ ?_
      have hne : j.val ≠ rc.val := Nat.ne_of_lt (j.isLt.trans_le (Nat.not_lt.mp hrc))
      simp [idEnv, hne]
  have hcol : colMaskAnf colMask ⟨0, by decide⟩ +
      (∑ u : Fin 31, colMaskAnf colMask ⟨u.val + 1, by omega⟩ *
        b2z (idEnv rc x (Sum.inr u))) = b2z (extCol24Bool colMask x) := by
    dsimp only [colMaskAnf, idEnv]
    simp_rw [b2z_z2b]
    exact anf5_decomp (fun y ↦ b2z (extCol24Bool colMask y)) x
  rw [hrow]
  linear_combination hcol
/-- Raw `ZMod 2` phase polynomial evaluated by `fix128C` on `γ`. -/
def rFixP {N : ℕ} (rH :
  QRegister 128 N) (rM : QRegister 31 N) (φ : Fin 128 → Fin (2 ^ 5) → ZMod 2) (γ : BitAssignment N)
  : ZMod 2 := ∑ c : Fin 128, γ (rH c) * (anfCoeffs 5 (φ c) ⟨0, by decide⟩ + ∑ u : Fin 31, anfCoeffs
  5 (φ c) ⟨u.val + 1, by omega⟩ * γ (rM u))
/-- `0-T` 128-sector diagonal phase fixup circuit. -/
def fix128C {N : ℕ} (rH : QRegister 128 N) (rM
  : QRegister 31 N) (hHM : ∀ c u, rH c ≠ rM u) (φ : Fin 128 → Fin (2 ^ 5) → ZMod 2) : Circuit N :=
  hotCtxPhaseLoop 31 128 rH rM hHM (fun c ↦ anfCoeffs 5 (φ c) ⟨0, by decide⟩) (fun c u ↦ anfCoeffs 5
  (φ c) ⟨u.val + 1, by omega⟩) 128 le_rfl
@[simp] theorem count_fix128Circ_toff {N} (rH : QRegister 128 N) (rM : QRegister 31 N) (hHM φ) :
  (fix128C rH rM hHM φ).count .TOFF = 0 := count_hotCtxPhaseLoop_toff2 rH rM hHM _ _ 128 le_rfl
@[simp] theorem count_fix128Circ_t {N} (rH : QRegister 128 N) (rM : QRegister 31 N) (hHM φ) :
  (fix128C rH rM hHM φ).count .T = 0 := count_hotCtxPhaseLoop_t2 rH rM hHM _ _ 128 le_rfl
theorem ket_fix128Circ {N : ℕ} (rH : QRegister 128 N) (rM : QRegister 31 N) (hHM : ∀ c u, rH c ≠ rM
  u) (φ : Fin 128 → Fin (2 ^ 5) → ZMod 2) (γ : BitAssignment N) : (fix128C rH rM hHM
  φ).eval.1.mulVec (Solution.XMeasCircuit.ket γ) = bitSign (rFixP rH rM φ γ) •
    Solution.XMeasCircuit.ket γ :=
  ket_hotCtxPhaseLoop rH rM hHM _ _ 128 le_rfl γ
attribute [irreducible] fix128C
/-- Prefix sum `∑_{i < g} groupLen i` (`g ≤ G`). -/
def prefLen {G : ℕ} (groupLen : Fin G → ℕ) : (g
  : ℕ) → g ≤ G → ℕ
  | 0, _ => 0
  | g + 1, hg => prefLen groupLen g (Nat.le_of_succ_le hg) + groupLen ⟨g, hg⟩
theorem pref_sum {G : ℕ} (groupLen : Fin G → ℕ) : ∀ (g : ℕ) (hg : g ≤ G), prefLen groupLen g hg = ∑
  i : Fin g, groupLen ⟨i.val, i.isLt.trans_le hg⟩
  | 0, _ => rfl
  | g + 1, hg => by
      rw [prefLen, pref_sum groupLen g (Nat.le_of_succ_le hg), Fin.sum_univ_castSucc]
      rfl
theorem pref_full {G : ℕ} (f : Fin G → ℕ) : prefLen f G le_rfl = ∑ g : Fin G, f g := by
  rw [pref_sum]
theorem pref_mono {G : ℕ} (f : Fin G → ℕ) : ∀ {a b : ℕ} (hb : b ≤ G) (hab : a ≤ b), prefLen f a
  (Nat.le_trans hab hb) ≤ prefLen f b hb
  | _, 0, _, hab => by
      cases Nat.eq_zero_of_le_zero hab
      rfl
  | _, _ + 1, hb, hab => by
      rcases Nat.of_le_succ hab with hle | rfl
      · exact Nat.le_trans (pref_mono f (Nat.le_of_succ_le hb) hle) (Nat.le_add_right _ _)
      · rfl
/-- Grouped `14`-plane Hadamard-gadget symplectic QROM plan. -/
structure HGadgetSymp14Plan (R G :
  ℕ) where
  groupLen : Fin G → ℕ
  sum_groupLen : (∑ g : Fin G, groupLen g) = R
  groupW : Fin G → Fin 14 → Bool
  stepA : Fin R → Fin 126 → Bool
  stepB : Fin R → Fin 126 → Bool
  stepC : Fin R → Fin 30 → Bool
  stepD : Fin R → Fin 30 → Bool
  rowDiag : Fin 14 → Fin 126 → Bool
  colDiag : Fin 14 → Fin 30 → Bool
theorem HGadgetSymp14Plan.step_lt {R G : ℕ} (P : HGadgetSymp14Plan R G) (g : Fin G) (j : Fin
  (P.groupLen g)) : prefLen P.groupLen g.val (Nat.le_of_lt g.isLt) + j.val < R := by
  have h1 := pref_mono P.groupLen le_rfl g.isLt
  rw [pref_full, P.sum_groupLen] at h1
  dsimp only [prefLen] at h1
  simp only [Fin.eta] at h1
  have := j.isLt
  omega
/-- Step index `prefLen g + j : Fin R`. -/
def HGadgetSymp14Plan.stepIdx {R G : ℕ} (P :
  HGadgetSymp14Plan R G) (g : Fin G) (j : Fin (P.groupLen g)) : Fin R := ⟨prefLen P.groupLen g.val
  (Nat.le_of_lt g.isLt) + j.val, P.step_lt g j⟩
/-- `Var157` affine pairs of group `g`. -/
def HGadgetSymp14Plan.affPairs {R G : ℕ} (P :
  HGadgetSymp14Plan R G) (g : Fin G) : List (AffPair Var157) := (List.finRange (P.groupLen g)).map
  fun j ↦ (rcColAff (P.stepA (P.stepIdx g j)) (P.stepC (P.stepIdx g j)), rcColAff (P.stepB
  (P.stepIdx g j)) (P.stepD (P.stepIdx g j)))
/-- Group-`g` inner product on `(rc, x)`. -/
def HGadgetSymp14Plan.grpBit {R G : ℕ} (P :
  HGadgetSymp14Plan R G) (g : Fin G) (rc : Fin 128) (x : Fin (2 ^ 5)) : Bool := xorPairs (idEnv rc
  x) (P.affPairs g)
/-- Prefix XOR of groups `< n` on plane `k`. -/
def HGadgetSymp14Plan.prefBool {R G : ℕ} (P :
  HGadgetSymp14Plan R G) (k : Fin 14) (rc : Fin 128) (x : Fin (2 ^ 5)) : (n : ℕ) → n ≤ G → Bool
  | 0, _ => false
  | n + 1, hn =>
      xor (P.prefBool k rc x n (Nat.le_of_succ_le hn))
        (P.groupW ⟨n, hn⟩ k && P.grpBit ⟨n, hn⟩ rc x)
/-- `128 × 32 × 14` Boolean target table of `P`. -/
def HGadgetSymp14Plan.targetBoolTable {R G : ℕ}
  (P : HGadgetSymp14Plan R G) (rc : Fin 128) (x : Fin (2 ^ 5)) (k : Fin 14) : Bool := xor
  (P.prefBool k rc x G le_rfl) (xor (if h : rc.val < 126 then P.rowDiag k ⟨rc.val, h⟩ else false)
  (extCol24Bool (P.colDiag k) x))
/-- Bundled registers and pairwise non-aliasing proofs for `midDyn`. -/
structure MidLayout (N : ℕ)
  where
  rHot : QRegister 128 N
  rMono : QRegister 31 N
  wG : Wire N
  rOut : QRegister 14 N
  hHotMono : ∀ c u, rHot c ≠ rMono u
  hHotG : ∀ c, rHot c ≠ wG
  hMonoG : ∀ u, rMono u ≠ wG
  hGOut : ∀ k, wG ≠ rOut k
  hHotOut : ∀ c k, rHot c ≠ rOut k
  hMonoOut : ∀ u k, rMono u ≠ rOut k
/-- Wire environment `Var157 → Bool` read from `(M.rHot, M.rMono)` on `γ`. -/
def vEnv {N : ℕ} (M :
  MidLayout N) (γ : BitAssignment N) : Var157 → Bool := fun v ↦ z2b (γ (vWire M.rHot M.rMono v))
theorem v157_upd {N : ℕ} (M : MidLayout N) {w : Wire N} (hHot : ∀ c, M.rHot c ≠ w) (hMono : ∀ u,
  M.rMono u ≠ w) (γ : BitAssignment N) (b : ZMod 2) : vEnv M (update γ w b) = vEnv M γ := by
  funext v
  rcases v with j | u
  · exact congrArg z2b (update_of_ne (hHot ⟨j.val, by omega⟩) b γ)
  · exact congrArg z2b (update_of_ne (hMono u) b γ)
theorem ctrl_v157 {N : ℕ} (M : MidLayout N) (t : Wire N) (hHot : ∀ c, M.rHot c ≠ t) (hMono : ∀ u,
  M.rMono u ≠ t) (γ : BitAssignment N) : (fun c : CtrlWire N t ↦ z2b (γ c.1)) ∘ vCtrl M.rHot M.rMono
  t hHot hMono = vEnv M γ := by
  funext x
  rcases x with _ | _ <;> rfl
/-- Raw Boolean inner-product bit `s1_g(γ)` of group `g` on `γ : BitAssignment N`. -/
def rgBit {R G
  N : ℕ} (P : HGadgetSymp14Plan R G) (g : Fin G) (M : MidLayout N) (γ : BitAssignment N) : Bool :=
  xorPairs (vEnv M γ) (P.affPairs g)
/-- Raw Boolean carry bit `s2_g(γ)` of group `g` on `γ : BitAssignment N`. -/
def rgCarry {R G N :
  ℕ} (P : HGadgetSymp14Plan R G) (g : Fin G) (M : MidLayout N) (γ : BitAssignment N) : Bool :=
  let sch := lempelSch (P.affPairs g)
  (evalHGad (vEnv M γ) sch.1 sch.2.1 sch.2.2.1 sch.2.2.2).2.2.2
/-- Ideal Boolean carry bit `s2_g(rc, x)` of group `g`. -/
def idCarry {R G : ℕ} (P :
  HGadgetSymp14Plan R G) (g : Fin G) (rc : Fin 128) (x : Fin (2 ^ 5)) : Bool :=
  let sch := lempelSch (P.affPairs g)
  (evalHGad (idEnv rc x) sch.1 sch.2.1 sch.2.2.1 sch.2.2.2).2.2.2
/-- Raw diagonal phase of group `g` on `γ`. -/
def rgPhase {R G N : ℕ} (P : HGadgetSymp14Plan R G)
  (g : Fin G) (M : MidLayout N) (γ : BitAssignment N) : ZMod 2 := b2z (rgCarry P g M γ) + b2z (rgBit
  P g M γ) * ∑ k : Fin 14, b2z (P.groupW g k) * γ (M.rOut k)
/-- Total ideal sector carry phase `∑_{g : Fin G} b2z (s2_g(rc, x))` in `ZMod 2`. -/
def totPhi {R G
  : ℕ} (P : HGadgetSymp14Plan R G) (rc : Fin 128) (x : Fin (2 ^ 5)) : ZMod 2 := ∑ g : Fin G, b2z
  (idCarry P g rc x)
/-- Compute-and-CZ-fanout circuit of group `g`. -/
def grpCompC {R G N : ℕ} (P : HGadgetSymp14Plan R
  G) (g : Fin G) (M : MidLayout N) : Circuit N :=
  let sch := lempelSch (P.affPairs g)
  let emb := vCtrl M.rHot M.rMono M.wG M.hHotG M.hMonoG
  hGadC M.wG (sch.1.map (mapAff emb)) (sch.2.1.map (mapAff emb))
      sch.2.2.1 (sch.2.2.2.map emb) ;;ᶜ
    czMaskCircuit M.wG 14 M.rOut M.hGOut (fun k ↦ b2z (P.groupW g k))
/-- `(2 * groupLen g + 2)`-`T` diagonal circuit of group `g`. -/
def grpStepD {Var : Type} {R G N :
  ℕ} (v : Var) (P : HGadgetSymp14Plan R G) (g : Fin G) (M : MidLayout N) : DynamicCircuit Var N :=
  .seq (.circuit (grpCompC P g M)) (xMeasUnloadWireDyn v M.wG (.circuit (andPairsC M.wG ((P.affPairs
  g).map fun p ↦ (mapAff (vCtrl M.rHot M.rMono M.wG M.hHotG M.hMonoG) p.1, mapAff (vCtrl M.rHot
  M.rMono M.wG M.hHotG M.hMonoG) p.2)))))
@[simp] theorem count_grpStepDyn_toff {Var R G N} (v : Var) (P : HGadgetSymp14Plan R G) (g M) :
  (grpStepD v P g (M : MidLayout N)).count .TOFF = 0 := by
  simp [grpStepD, grpCompC, DynamicCircuit.count, count_xMeasUnloadWireDyn_toff]
@[simp] theorem count_grpStepDyn_t {Var R G N} (v : Var) (P : HGadgetSymp14Plan R G) (g M) :
  (grpStepD v P g (M : MidLayout N)).count .T = 2 * P.groupLen g + 2 := by
  have hl := lempel_lens (P.affPairs g)
  have hp : (P.affPairs g).length = P.groupLen g := by simp [HGadgetSymp14Plan.affPairs]
  simp only [grpStepD, grpCompC, DynamicCircuit.count, Circuit.count_seq, count_hGadgetCirc_t,
    List.length_map, hl.1, hl.2, hp, count_czMaskCircuit_t, count_xMeasUnloadWireDyn_t,
    count_andPairsCirc_t]
  omega
theorem rZero_wp_coe {Var : Type} [Fintype Var] {n : ℕ} (U : Unitary (2 ^ n)) (Φ : QCAssertion Var
  (2 ^ n)) (S : Finset (Wire n)) (σ : Store Var) : (SelectSwapQROM.restrictZeroSet (qcWpQAssign U
  Φ) S σ).1 = (Φ σ).1.conj (zeroProjOn S * U.1ᴴ) := by
  simp only [SelectSwapQROM.restrictZeroSet_coe, qcWpQAssign, qcQAssignObsMap,
    Observable.conj_coe, Unitary.coe_star, star_eq_conjTranspose, conj_conj]
theorem wpZeroSet_grpStepDyn {Var : Type} [Fintype Var] [DecidableEq Var] {R G N : ℕ} (v : Var) (P :
  HGadgetSymp14Plan R G) (g : Fin G) (M : MidLayout N) (S : Finset (Wire N)) (hwS : M.wG ∈ S) :
  WpZeroSet v S (diagKetUnitary (rgPhase P g M)) (grpStepD v P g M) := by
  let f1 := fun γ ↦ b2z (rgBit P g M γ)
  have hf1G : ∀ β b, f1 (update β M.wG b) = f1 β := fun _ _ ↦ by
    simp only [f1, rgBit, v157_upd M M.hHotG M.hMonoG]
  set U_w := xorWireUnitary M.wG f1 hf1G
  set D_g := diagKetUnitary (rgPhase P g M)
  set U_pre := U_w * D_g
  set cComp := grpCompC P g M
  set emb := vCtrl M.rHot M.rMono M.wG M.hHotG M.hMonoG
  set mappedPairs := (P.affPairs g).map fun p ↦ (mapAff emb p.1, mapAff emb p.2)
  set cFix := andPairsC M.wG mappedPairs
  have hCompWp : WpZeroSet v S U_pre (.circuit cComp) := by
    refine WpZeroSet.congr_unitary (WpZeroSet.of_circuit v S cComp (by simp [cComp, grpCompC])) fun
      γ hS0 ↦ ?_
    have hg0 : γ M.wG = 0 := hS0 M.wG hwS
    obtain ⟨hacc, hs0, hs1⟩ := evalHGad_lempel (vEnv M γ) (P.affPairs g)
    set sch := lempelSch (P.affPairs g)
    let pSt := sch.1.map (mapAff emb)
    let nSt := sch.2.1.map (mapAff emb)
    have hevMap : evalHGad (fun c ↦ z2b (γ c.1)) pSt nSt sch.2.2.1 (sch.2.2.2.map emb) = evalHGad
      (vEnv M γ) sch.1 sch.2.1 sch.2.2.1 sch.2.2.2 := by
      simpa [pSt, nSt, emb, ctrl_v157] using evalHGad_map (fun c ↦ z2b (γ c.1)) emb sch.1 sch.2.1
        sch.2.2
    have hlen8 : (pSt.length : ZMod 8) + 7 * (nSt.length : ZMod 8) = 0 := by
      have hl := lempel_lens (P.affPairs g)
      dsimp only [pSt, nSt, sch]
      rw [List.length_map, List.length_map, hl.1, hl.2]
      have h8 (x : ZMod 8) : x + 7 * x = 0 := by
        calc x + 7 * x = 8 * x := by ring
          _ = 0 := by rw [show (8 : ZMod 8) = 0 from rfl, zero_mul]
      exact h8 _
    have hG1 := ket_hGad_zero M.wG pSt nSt sch.2.2.1 (sch.2.2.2.map emb) hlen8 γ hg0
      (by rwa [hevMap]) (by rwa [hevMap])
    rw [hevMap] at hG1
    have hs1_eq : b2z (evalHGad (vEnv M γ) sch.1 sch.2.1 sch.2.2.1 sch.2.2.2).2.2.1 = f1 γ :=
      congrArg b2z hs1
    dsimp only [cComp, grpCompC]
    change (hGadC M.wG pSt nSt sch.2.2.1 (sch.2.2.2.map emb) ;;ᶜ czMaskCircuit M.wG 14 M.rOut
      M.hGOut (fun k ↦ b2z (P.groupW g k))).eval.1.mulVec (Solution.XMeasCircuit.ket γ) = _
    rw [eval_seq_mv, hG1, hs1_eq, mulVec_smul, ket_sdk_eq (update γ M.wG (f1 γ)), ket_czMaskCircuit,
      ← ket_sdk_eq (update γ M.wG (f1 γ)), smul_smul, ← bitSign_add, update_self]
    dsimp only [U_pre, D_g, U_w]
    rw [Submonoid.coe_mul, ← mulVec_mulVec, ket_sdk_eq γ, diagKetUnitary_mulVec_ket, ← ket_sdk_eq γ,
      mulVec_smul, xorWireUnitary_mulVec_ket, hg0, zero_add]
    refine congrArg (· • Solution.XMeasCircuit.ket (update γ M.wG (f1 γ))) (congrArg bitSign ?_)
    dsimp only [rgPhase, rgCarry, f1, sch]
    refine congrArg₂ (· + ·) rfl (congrArg₂ (· * ·) rfl ?_)
    exact Finset.sum_congr rfl fun k _ ↦ by rw [update_of_ne (M.hGOut k).symm]
  have hFixWp : WpZeroSet v S (phaseFlipUnitary f1) (.circuit cFix) := by
    refine WpZeroSet.congr_unitary (WpZeroSet.of_circuit v S cFix (by simp [cFix])) fun γ hS0 ↦ ?_
    dsimp only [cFix]
    rw [ket_andPairsCirc_zero M.wG mappedPairs γ (hS0 M.wG hwS), phaseFlipUnitary_mulVec_ket]
    refine congrArg (· • Solution.XMeasCircuit.ket γ) (congrArg bitSign ?_)
    dsimp only [mappedPairs, emb, f1, rgBit]
    rw [xorPairs_map, ctrl_v157]
  have hZP : zeroProjOn S = cleanFinsetProj S := by
    unfold zeroProjOn cleanFinsetProj
    congr 1
  have hR2Z (Ψ : QCAssertion Var (2 ^ N)) : SelectSwapQROM.restrictZeroSet Ψ S =
    restrictAssertionToCleanFinset Ψ S := funext fun σ ↦ Subtype.ext
    (by rw [SelectSwapQROM.restrictZeroSet_coe, restrictAssertionToCleanFinset_coe, hZP])
  refine ⟨count_grpStepDyn_toff v P g M, fun Θ _ σ val ↦ ?_, fun Θ hΘ ↦ ?_⟩
  · dsimp only [grpStepD]
    rw [DynamicCircuit.compile_seq, wp_qSeq, DynamicCircuit.compile_circuit,
      DynamicCircuit.qc_wp_circuit_compile (Var := Var)]
    simp only [qcWpQAssign, wp_xMeasUnloadWireDyn_update_self]
  · set Ψ := wp (xMeasUnloadWireDyn v M.wG (.circuit cFix)).compile Θ
    have hΨ : IsVInv14 v Ψ := fun σ val ↦ wp_xMeasUnloadWireDyn_update_self v M.wG (.circuit cFix)
      Θ σ val
    have hSeq : wp (grpStepD v P g M).compile Θ = wp (DynamicCircuit.circuit cComp).compile Ψ := by
      dsimp only [grpStepD, cComp, cFix, mappedPairs, emb]
      rw [DynamicCircuit.compile_seq, wp_qSeq]
    rw [hSeq, hCompWp.2.2 Ψ hΨ]
    dsimp only [U_pre]
    rw [← qc_wp_qAssign_comp D_g U_w Ψ]
    have hCommDH : zeroProjOn S * D_g.1ᴴ = D_g.1ᴴ * zeroProjOn S := by
      have hCommD : zeroProjOn S * D_g.1 = D_g.1 * zeroProjOn S := by
        refine Solution.XMeasCircuit.matrix_ext_ket fun β ↦ ?_
        rw [← mulVec_mulVec, ← mulVec_mulVec, ket_sdk_eq β, zeroProjOn_mulVec_ket]
        dsimp only [D_g]
        rw [diagKetUnitary_mulVec_ket, mulVec_smul, zeroProjOn_mulVec_ket]
        by_cases h0 : ∀ w ∈ S, β w = 0
        · rw [ite_t (h0), diagKetUnitary_mulVec_ket]
        · rw [ite_f (h0), mulVec_zero, smul_zero]
      simpa only [conjTranspose_mul, zeroProjOn_conjTranspose] using (congrArg (·ᴴ) hCommD).symm
    have hMbu := restrictAssertionToCleanFinset_wp_xorWireUnitary_xMeasUnloadWireDyn v M.wG S hwS f1
      hf1G (.circuit cFix) Θ hΘ ((hR2Z _).symm.trans ((hFixWp.2.2 Θ hΘ).trans (hR2Z _)))
    rw [← hR2Z, ← hR2Z] at hMbu
    funext σ
    apply Subtype.ext
    rw [rZero_wp_coe, rZero_wp_coe, hCommDH, ← conj_conj, ← conj_conj, ←
      SelectSwapQROM.restrictZeroSet_coe, ← SelectSwapQROM.restrictZeroSet_coe]
    dsimp only [U_w, Ψ]
    rw [hMbu]
attribute [irreducible] grpCompC grpStepD
end HGadgetImpl
end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.HGadgetSympQrom
