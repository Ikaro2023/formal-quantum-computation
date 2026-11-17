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

public import
  QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.ZeroCmp20OuterAnfParam

@[expose] public section

/-!
# `AnfAndCoin14Core`: `14-T` Dyadic Coin, Power-of-2 Fast-Zeta ANF, & Symplectic QROM Loaders

Core primitives for the `2,504-T` (`0` extra error) `ZeroCmp20` inner walk engine:

1. **`14-T` Dyadic Packet Coin + `60-T` (`19 ≤ s`) Fused Mux-Swap:**
   `23`-gate (`7 × ctrlH = 14 T`, `2 × H`, `14 × CNOT`, `0 TOFF`) exact dyadic state preparation
   `optCoin9Circuit : Circuit 4` whose trailing `CNOT`s align the `4` `AGL(4, 2)` split planes
   onto coordinate wires `0..3`, yielding an `18`-op (`9`-AND = `36 T`) packet multiplexer
   (`mux9Formula`) and `60 T` fused mux-swap.
2. **Power-of-2 One-Hot + Upward Fast Zeta ANF Wrapper (`StepPow2Layout K n`):**
   Exact `4 * (2 ^ K - 1)` `T`, `0-TOFF` `(K + 1) → 2 ^ (K + 1)` one-hot wrapper
   (`withStepOneHotPow2Dyn`) using a `0-T` `3`-gate linear root init/uninit and `0-T` upward
   binary fast-zeta `CNOT` butterfly (`withStepAnfPow2Dyn`), supplying all `2 ^ (K + 1) - 1`
   non-empty `GF(2)` monomials (`60 T` at `M = 5`, `28 T` at `M = 4`, `12 T` at `M = 3`).
3. **Preloaded One-Hot Symplectic QROM Loader & Phase-Fixup Unloader:**
   - `qromOpt162SympW5FromHot128LoadDyn` (`708 T = 60 + 648 T`, `0 TOFF`, `35 ≤ sScr`) for
     forward `PREP_mid`.
   - `qromXMeasW3FromHotCtxAliasUnloadDyn` (`44 T = 12 + 4 + 28 T`, `0 TOFF`, `0 ≤ sScr`) for
     turnaround X-measurement unload.

## References
- G. H. Low, R. King, D. W. Berry, Q. Han, A. E. DePrince III, A. White, R. Babbush, R. D. Somma,
  and N. C. Rubin, *Phys. Rev. X* **15**, 041016 (2025), DOI: `10.1103/PhysRevX.15.041016`.
- R. Babbush, C. Gidney, D. W. Berry, N. Wiebe, J. McClean, A. Paler, A. Fowler, and H. Neven,
  *Phys. Rev. X* **8**, 041015 (2018), DOI: `10.1103/PhysRevX.8.041015`.
- C. Gidney, *Quantum* **2**, 74 (2018), DOI: `10.22331/q-2018-06-18-74`.
- D. W. Berry, C. Gidney, M. Motta, J. R. McClean, and R. Babbush, *Quantum* **3**, 208 (2019),
  DOI: `10.22331/q-2019-12-02-208`.
- G. H. Low, V. Kliuchnikov, and L. Schaeffer, *Quantum* **8**, 1375 (2024),
  DOI: `10.22331/q-2024-06-17-1375`.
-/

namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.StepAnfAndCoin14Core
open QuantumComputation.Specs QuantumComputation.Specs.P450

section CoreImpl

set_option exponentiation.threshold 512

open Operator QProg Matrix Circuit Real HermitianMat
open QuantumComputation.Specs QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution
open QuantumComputation.Specs.P450
open BlockEncodingCore BlockEncodingCircuit
open CoherentAlias
open AliasPrep
open Phase2MidSandwich
open CompactBilinearPrep
open MidReflCtxRetain
open OptFactoredMag30AndCoin9
open Cat11CompactPhase2Bridge
open ReordOuter13Bridge
open ZeroRcHotPrepMid21Fast
open OptXMeasUnload21
open Tuned162ScheduledSympQrom21
open Tuned162StepSympAnfQrom21
open OptStepSympAnfQrom21
open OptU2Grover184PrepOut13
open TopIntegrationBridge
open MobiusOptSubcube163Walk
open CompactTuned162StepWalk
open CompactTuned162StepZeroCmp20
open CompactZeroCmp20OuterParam
open CompactStepZeroCmp20OuterParam
open scoped Matrix BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator Circuit.Notation

local instance (priority := 1000000) instNeZeroTwoPowAnf14 (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩

/-! ## Section 1: `14-T` Dyadic Packet Coin + `60-T` (`19 ≤ s`) Fused Mux-Swap -/

/-- Exact `23`-gate (`7 × ctrlH = 14 T`, `0 TOFF`) `4`-qubit dyadic packet coin preparing weights
`(256, 128, 64, 32, 16, 8, 4, 2, 1, 1)` out of `512` aligned to single-wire split planes. -/
def optCoin9Circuit : Circuit 4 :=
  Circuit.H 0 ;;ᶜ
  ctrlH.onRegister (QRegister.pair 0 1 (by decide)) ;;ᶜ
  ctrlH.onRegister (QRegister.pair 1 2 (by decide)) ;;ᶜ
  ctrlH.onRegister (QRegister.pair 2 1 (by decide)) ;;ᶜ
  ctrlH.onRegister (QRegister.pair 1 3 (by decide)) ;;ᶜ
  Circuit.CNOT 2 3 (by decide) ;;ᶜ
  Circuit.CNOT 1 2 (by decide) ;;ᶜ
  ctrlH.onRegister (QRegister.pair 3 1 (by decide)) ;;ᶜ
  Circuit.CNOT 1 2 (by decide) ;;ᶜ
  Circuit.CNOT 2 3 (by decide) ;;ᶜ
  Circuit.CNOT 2 0 (by decide) ;;ᶜ
  ctrlH.onRegister (QRegister.pair 1 2 (by decide)) ;;ᶜ
  Circuit.CNOT 2 0 (by decide) ;;ᶜ
  Circuit.CNOT 2 3 (by decide) ;;ᶜ
  Circuit.CNOT 1 0 (by decide) ;;ᶜ
  ctrlH.onRegister (QRegister.pair 3 1 (by decide)) ;;ᶜ
  Circuit.CNOT 1 0 (by decide) ;;ᶜ
  Circuit.CNOT 2 3 (by decide) ;;ᶜ
  Circuit.CNOT 3 1 (by decide) ;;ᶜ
  Circuit.H 3 ;;ᶜ
  Circuit.CNOT 3 1 (by decide) ;;ᶜ
  Circuit.CNOT 0 1 (by decide) ;;ᶜ
  Circuit.CNOT 1 3 (by decide)

/-- Exact `23`-gate (`14 T`, `0 TOFF`) reverse `4`-qubit circuit for `optCoin9Circuit`. -/
def optCoin9InvCircuit : Circuit 4 :=
  Circuit.CNOT 1 3 (by decide) ;;ᶜ
  Circuit.CNOT 0 1 (by decide) ;;ᶜ
  Circuit.CNOT 3 1 (by decide) ;;ᶜ
  Circuit.H 3 ;;ᶜ
  Circuit.CNOT 3 1 (by decide) ;;ᶜ
  Circuit.CNOT 2 3 (by decide) ;;ᶜ
  Circuit.CNOT 1 0 (by decide) ;;ᶜ
  ctrlH.onRegister (QRegister.pair 3 1 (by decide)) ;;ᶜ
  Circuit.CNOT 1 0 (by decide) ;;ᶜ
  Circuit.CNOT 2 3 (by decide) ;;ᶜ
  Circuit.CNOT 2 0 (by decide) ;;ᶜ
  ctrlH.onRegister (QRegister.pair 1 2 (by decide)) ;;ᶜ
  Circuit.CNOT 2 0 (by decide) ;;ᶜ
  Circuit.CNOT 2 3 (by decide) ;;ᶜ
  Circuit.CNOT 1 2 (by decide) ;;ᶜ
  ctrlH.onRegister (QRegister.pair 3 1 (by decide)) ;;ᶜ
  Circuit.CNOT 1 2 (by decide) ;;ᶜ
  Circuit.CNOT 2 3 (by decide) ;;ᶜ
  ctrlH.onRegister (QRegister.pair 1 3 (by decide)) ;;ᶜ
  ctrlH.onRegister (QRegister.pair 2 1 (by decide)) ;;ᶜ
  ctrlH.onRegister (QRegister.pair 1 2 (by decide)) ;;ᶜ
  ctrlH.onRegister (QRegister.pair 0 1 (by decide)) ;;ᶜ
  Circuit.H 0

/-- `4`-qubit ideal packet coin unitary realized by `optCoin9Circuit`. -/
noncomputable def optCoin9Unitary : Unitary (2 ^ 4) := optCoin9Circuit.eval

@[simp] theorem countOptCoin9Circuit_toff : optCoin9Circuit.count .TOFF = 0 := rfl

@[simp] theorem countOptCoin9Circuit_t : optCoin9Circuit.count .T = 14 := rfl

@[simp] theorem countOptCoin9InvCircuit_toff : optCoin9InvCircuit.count .TOFF = 0 := rfl

@[simp] theorem countOptCoin9InvCircuit_t : optCoin9InvCircuit.count .T = 14 := rfl

private theorem eval_H_inv9 (w : Wire 4) : (Circuit.H w).eval⁻¹ = (Circuit.H w).eval :=
  (Circuit.eval_inverse (Circuit.H w)).symm

private theorem eval_CNOT_inv9 (c t : Wire 4) (h : c ≠ t) :
    (Circuit.CNOT c t h).eval⁻¹ = (Circuit.CNOT c t h).eval :=
  (Circuit.eval_inverse (Circuit.CNOT c t h)).symm

theorem evalOptCoin9InvCircuit : optCoin9InvCircuit.eval = optCoin9Circuit.eval⁻¹ := by
  have hh : Qubit.H⁻¹ = Qubit.H := (eq_inv_of_mul_eq_one_left Qubit.H_sq).symm
  simp only [optCoin9Circuit, optCoin9InvCircuit, Circuit.eval_seq, Circuit.eval_onRegister,
    eval_ctrlH, _root_.mul_inv_rev, ← QRegister.embedUnitary_inv, predCtrlUnitary_inv, hh,
    eval_CNOT_inv9, eval_H_inv9, mul_assoc]

/-- Relocated `14 T`, `0 TOFF` forward packet coin dynamic circuit (`0` scratch wires needed). -/
def optCoin9Dyn {Var : Type} {N : ℕ} (rPkt : QRegister 4 N) : DynamicCircuit Var N :=
  .circuit (optCoin9Circuit.onRegister rPkt)

/-- Relocated `14 T`, `0 TOFF` inverse packet coin dynamic circuit (`0` scratch wires needed). -/
def optCoin9InvDyn {Var : Type} {N : ℕ} (rPkt : QRegister 4 N) : DynamicCircuit Var N :=
  .circuit (optCoin9InvCircuit.onRegister rPkt)

@[simp] theorem countOptCoin9Dyn_toff {Var : Type} {N : ℕ} (rPkt : QRegister 4 N) :
    (optCoin9Dyn (Var := Var) rPkt).count .TOFF = 0 := by
  simp [optCoin9Dyn]

@[simp] theorem countOptCoin9Dyn_t {Var : Type} {N : ℕ} (rPkt : QRegister 4 N) :
    (optCoin9Dyn (Var := Var) rPkt).count .T = 14 := by
  simp [optCoin9Dyn]

@[simp] theorem countOptCoin9InvDyn_toff {Var : Type} {N : ℕ} (rPkt : QRegister 4 N) :
    (optCoin9InvDyn (Var := Var) rPkt).count .TOFF = 0 := by
  simp [optCoin9InvDyn]

@[simp] theorem countOptCoin9InvDyn_t {Var : Type} {N : ℕ} (rPkt : QRegister 4 N) :
    (optCoin9InvDyn (Var := Var) rPkt).count .T = 14 := by
  simp [optCoin9InvDyn]

theorem cleanRealizesOptCoin9Dyn {Var : Type} [Fintype Var] [DecidableEq Var]
    {N s : ℕ} (v : Var) (rPkt : QRegister 4 N) (rScr : QRegister s N)
    (hdisj : rPkt.DisjointWires rScr) :
    CleanDyn.CleanRealizes v rPkt rScr optCoin9Unitary (optCoin9Dyn rPkt) :=
  CleanDyn.CleanRealizes.circuit v rPkt rScr hdisj optCoin9Circuit
    countOptCoin9Circuit_toff

theorem cleanRealizesOptCoin9InvDyn {Var : Type} [Fintype Var] [DecidableEq Var]
    {N s : ℕ} (v : Var) (rPkt : QRegister 4 N) (rScr : QRegister s N)
    (hdisj : rPkt.DisjointWires rScr) :
    CleanDyn.CleanRealizes v rPkt rScr optCoin9Unitary⁻¹ (optCoin9InvDyn rPkt) := by
  have hc := CleanDyn.CleanRealizes.circuit v rPkt rScr hdisj optCoin9InvCircuit
    countOptCoin9InvCircuit_toff
  rwa [evalOptCoin9InvCircuit] at hc

/-- Toggle bit `w` of a `4`-qubit computational basis index. -/
private def flipBit4C (w : Wire 4) (j : Fin (2 ^ 4)) : Fin (2 ^ 4) :=
  setBitIdx j w (basisBits 4 j w + 1)

/-- Action of `CNOT c t` on `4`-qubit computational basis indices. -/
private def cnot4FlipC (c t : Wire 4) (j : Fin (2 ^ 4)) : Fin (2 ^ 4) :=
  setBitIdx j t (basisBits 4 j t + basisBits 4 j c)

private theorem cnot4FlipC_involutive (c t : Wire 4) (h : c ≠ t) (j : Fin (2 ^ 4)) :
    cnot4FlipC c t (cnot4FlipC c t j) = j := by
  revert j h t c; decide

/-- Dyadic `(p.1 + p.2 * √2) / 32` amplitude representation in `ℤ[√2] / 32`. -/
private noncomputable def amp32ValC (p : ℤ × ℤ) : ℂ :=
  ((((p.1 : ℝ) + (p.2 : ℝ) * √2) / 32 : ℝ) : ℂ)

/-- State vector assembled from `16` dyadic `ℤ[√2] / 32` amplitudes. -/
private noncomputable def evalAmp32C (st : Fin (2 ^ 4) → ℤ × ℤ) : Fin (2 ^ 4) → ℂ :=
  ∑ j : Fin (2 ^ 4), amp32ValC (st j) • basisState j

private theorem evalAmp32C_apply (st : Fin (2 ^ 4) → ℤ × ℤ) (x : Fin (2 ^ 4)) :
    evalAmp32C st x = amp32ValC (st x) := by
  dsimp only [evalAmp32C]
  rw [Finset.sum_apply, Finset.sum_eq_single x]
  · simp [basisState]
  · intro j _ hjx; simp [basisState, Pi.single_eq_of_ne hjx.symm]
  · simp

private theorem mulVec_perm_amp32C {M : Operator (2 ^ 4)} {f : Fin (2 ^ 4) → Fin (2 ^ 4)}
    (hf : ∀ j, f (f j) = j) (hM : ∀ j, M *ᵥ basisState j = basisState (f j))
    (st : Fin (2 ^ 4) → ℤ × ℤ) :
    M *ᵥ evalAmp32C st = evalAmp32C (fun x ↦ st (f x)) := by
  funext x; rw [evalAmp32C_apply]; dsimp only [evalAmp32C]
  rw [Matrix.mulVec_sum, Finset.sum_apply, Finset.sum_eq_single (f x)]
  · rw [Matrix.mulVec_smul, hM, hf]; simp [basisState]
  · intro j _ hjf
    have hne : f j ≠ x := fun h ↦ hjf (by rw [← h, hf])
    rw [Matrix.mulVec_smul, hM]; simp [basisState, Pi.single_eq_of_ne hne.symm]
  · simp

private theorem eval_CNOT_amp32C (c t : Wire 4) (h : c ≠ t) (st : Fin (2 ^ 4) → ℤ × ℤ) :
    (Circuit.CNOT c t h).eval.1 *ᵥ evalAmp32C st =
      evalAmp32C (fun x ↦ st (cnot4FlipC c t x)) :=
  mulVec_perm_amp32C (cnot4FlipC_involutive c t h) (fun j ↦ by
    have hj : basisState j = CoherentAlias.ket (basisBits 4 j) :=
      (congrArg basisState (symm_basisBits_apply j)).symm
    rw [hj, CoherentAlias.ket_CNOT]; rfl) st

private theorem qubit_H_entries9 :
    Qubit.H.1 0 0 = ((1 / √2 : ℝ) : ℂ) ∧ Qubit.H.1 1 0 = ((1 / √2 : ℝ) : ℂ) ∧
    Qubit.H.1 0 1 = ((1 / √2 : ℝ) : ℂ) ∧ Qubit.H.1 1 1 = -((1 / √2 : ℝ) : ℂ) := by
  simp [Qubit.H, Complex.real_smul, one_div]

private theorem amp32ValC_mul_pos (p : ℤ × ℤ) (hp : p.1 % 2 = 0) :
    amp32ValC p * ((1 / √2 : ℝ) : ℂ) = amp32ValC (p.2, p.1 / 2) := by
  have h2 : p.1 = 2 * (p.1 / 2) := (Int.mul_ediv_cancel' (Int.dvd_of_emod_eq_zero hp)).symm
  have h2r : (p.1 : ℝ) = 2 * ((p.1 / 2 : ℤ) : ℝ) := by exact_mod_cast h2
  have hsq : √2 ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
  have hs0 : (√2 : ℝ) ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num)
  dsimp only [amp32ValC]; rw [← Complex.ofReal_mul]; congr 1
  rw [h2r]; field_simp [hs0]; linear_combination -((p.1 / 2 : ℤ) : ℝ) * hsq

private theorem amp32ValC_add_pos (p q : ℤ × ℤ) (hp : p.1 % 2 = 0) (hq : q.1 % 2 = 0) :
    amp32ValC p * ((1 / √2 : ℝ) : ℂ) + amp32ValC q * ((1 / √2 : ℝ) : ℂ) =
      amp32ValC (p.2 + q.2, p.1 / 2 + q.1 / 2) := by
  rw [amp32ValC_mul_pos p hp, amp32ValC_mul_pos q hq]
  dsimp only [amp32ValC]; rw [← Complex.ofReal_add]; congr 1; push_cast; ring

private theorem amp32ValC_sub_pos (p1 p0 : ℤ × ℤ) (h1 : p1.1 % 2 = 0) (h0 : p0.1 % 2 = 0) :
    amp32ValC p1 * -((1 / √2 : ℝ) : ℂ) + amp32ValC p0 * ((1 / √2 : ℝ) : ℂ) =
      amp32ValC (p0.2 - p1.2, p0.1 / 2 - p1.1 / 2) := by
  have hneg : amp32ValC p1 * -((1 / √2 : ℝ) : ℂ) = -(amp32ValC p1 * ((1 / √2 : ℝ) : ℂ)) := by
    ring
  rw [hneg, amp32ValC_mul_pos p1 h1, amp32ValC_mul_pos p0 h0]
  dsimp only [amp32ValC]; rw [← Complex.ofReal_neg, ← Complex.ofReal_add]; congr 1; push_cast; ring

private theorem eval_H0_zero9 :
    (Circuit.H (0 : Wire 4)).eval.1 *ᵥ basisState 0 =
      evalAmp32C (fun j ↦ if j.val == 0 || j.val == 1 then (0, 16) else (0, 0)) := by
  have hb0 : basisState (0 : Fin (2 ^ 4)) = CoherentAlias.ket (basisBits 4 0) :=
    (congrArg basisState (symm_basisBits_apply 0)).symm
  rw [hb0, Circuit.H, Circuit.eval_single, QRegister.embedUnitary_val, PrimitiveGate.eval,
    singleton_embedMatrix_mulVec_ket]
  have hb00 : basisBits 4 (0 : Fin (2 ^ 4)) 0 = 0 := by decide
  have hu0 : CoherentAlias.ket (Function.update (basisBits 4 (0 : Fin (2 ^ 4))) 0 0) =
      basisState 0 := by
    change basisState (setBitIdx 0 0 0) = basisState 0; congr 1
  have hu1 : CoherentAlias.ket (Function.update (basisBits 4 (0 : Fin (2 ^ 4))) 0 1) =
      basisState 1 := by
    change basisState (setBitIdx 0 0 1) = basisState 1; congr 1
  simp only [hb00, ↓reduceIte, qubit_H_entries9.1, qubit_H_entries9.2.1, hu0, hu1]
  have hr2 : ((1 / √2 : ℝ) : ℂ) = amp32ValC (0, 16) := by
    have hsq : √2 ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
    have hs0 : (√2 : ℝ) ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num)
    dsimp only [amp32ValC]; congr 1; push_cast; field_simp [hs0]; linear_combination -16 * hsq
  funext x; rw [evalAmp32C_apply, hr2]
  fin_cases x <;> simp [basisState, amp32ValC]

private theorem pair_ctrl_fires9 (c t : Wire 4) (h : c ≠ t) (j : Fin (2 ^ 4)) :
    ((((QRegister.pair c t h).compose (QRegister.block 0 1 (by omega))).extractIndex j).val == 1) =
      j.val.testBit c.val := by
  revert h j t c; decide

private theorem setBitIdx_other_ne9 (t : Wire 4) (j x : Fin (2 ^ 4))
    (hjx : j ≠ x) (hjy : j ≠ flipBit4C t x) :
    setBitIdx j t 0 ≠ x ∧ setBitIdx j t 1 ≠ x := by
  revert hjy hjx x j t; decide

private theorem flipBit4C_props (c t : Wire 4) (h : c ≠ t) (x : Fin (2 ^ 4)) :
    flipBit4C t x ≠ x ∧ (flipBit4C t x).val.testBit c.val = x.val.testBit c.val ∧
    (x.val.testBit t.val = false → basisBits 4 x t = 0 ∧ setBitIdx x t 0 = x ∧
      setBitIdx x t 1 = flipBit4C t x ∧ basisBits 4 (flipBit4C t x) t = 1 ∧
      setBitIdx (flipBit4C t x) t 0 = x ∧ setBitIdx (flipBit4C t x) t 1 = flipBit4C t x) ∧
    (x.val.testBit t.val = true → basisBits 4 x t = 1 ∧ setBitIdx x t 0 = flipBit4C t x ∧
      setBitIdx x t 1 = x ∧ basisBits 4 (flipBit4C t x) t = 0 ∧
      setBitIdx (flipBit4C t x) t 0 = flipBit4C t x ∧ setBitIdx (flipBit4C t x) t 1 = x) := by
  revert h x t c; decide

/-- Check that `st j` has an even rational part whenever control bit `c` is `1`. -/
private def evenCtrlHC (c : Wire 4) (st : Fin (2 ^ 4) → ℤ × ℤ) : Bool :=
  (List.finRange (2 ^ 4)).all fun j ↦
    if j.val.testBit c.val then decide ((st j).1 % 2 = 0) else true

/-- Symbolic `ℤ[√2] / 32` update under `ctrlH` with control `c` and target `t`. -/
private def stepCtrlHAmpC (c t : Wire 4) (st : Fin (2 ^ 4) → ℤ × ℤ) (x : Fin (2 ^ 4)) : ℤ × ℤ :=
  if x.val.testBit c.val then
    let p0 := st (setBitIdx x t 0)
    let p1 := st (setBitIdx x t 1)
    if x.val.testBit t.val then
      (p0.2 - p1.2, p0.1 / 2 - p1.1 / 2)
    else
      (p0.2 + p1.2, p0.1 / 2 + p1.1 / 2)
  else
    st x

private theorem eval_ctrlH_amp32C (c t : Wire 4) (h : c ≠ t) (st : Fin (2 ^ 4) → ℤ × ℤ)
    (heven : evenCtrlHC c st = true) :
    (ctrlH.onRegister (QRegister.pair c t h)).eval.1 *ᵥ evalAmp32C st =
      evalAmp32C (stepCtrlHAmpC c t st) := by
  rw [Circuit.eval_onRegister, eval_ctrlH, QRegister.embedUnitary_val]
  dsimp only [ctrlUnitary, predCtrlUnitary]
  have ht_last : QRegister.pair c t h (Fin.last 1) = t := rfl
  funext x; rw [evalAmp32C_apply]; dsimp only [evalAmp32C]
  rw [Matrix.mulVec_sum, Finset.sum_apply]
  obtain ⟨hyx, hcy, hxt0, hxt1⟩ := flipBit4C_props c t h x
  set y := flipBit4C t x
  have hother (j : Fin (2 ^ 4)) (hjx : j ≠ x) (hjy : j ≠ y) :
      (((QRegister.pair c t h).embedMatrix
          (predCtrlMatrix (fun u : Fin 2 ↦ u.val == 1) Qubit.H.1)) *ᵥ
        (amp32ValC (st j) • basisState j)) x = 0 := by
    rw [Matrix.mulVec_smul, embed_predCtrlMatrix_mulVec_basisState]
    obtain ⟨hn0, hn1⟩ := setBitIdx_other_ne9 t j x hjx hjy
    by_cases hcf :
        (((QRegister.pair c t h).compose (QRegister.block 0 1 (by omega))).extractIndex j).val == 1
    · simp only [hcf, ↓reduceIte, ht_last, Pi.smul_apply, Pi.add_apply, basisState,
        Pi.single_eq_of_ne hn0.symm, Pi.single_eq_of_ne hn1.symm, smul_zero, add_zero]
    · simp only [hcf, Bool.false_eq_true, ↓reduceIte, Pi.smul_apply, basisState,
        Pi.single_eq_of_ne hjx.symm, smul_zero]
  rw [(Finset.add_sum_erase _ _ (Finset.mem_univ x)).symm,
    (Finset.add_sum_erase _ _ (Finset.mem_erase.mpr ⟨hyx, Finset.mem_univ y⟩)).symm,
    Finset.sum_eq_zero (fun j hj ↦ by
      have hj1 := Finset.mem_erase.mp hj
      have hj2 := Finset.mem_erase.mp hj1.2
      exact hother j hj2.1 hj1.1), add_zero]
  rw [Matrix.mulVec_smul, Matrix.mulVec_smul, embed_predCtrlMatrix_mulVec_basisState,
    embed_predCtrlMatrix_mulVec_basisState]
  rw [pair_ctrl_fires9 c t h x, pair_ctrl_fires9 c t h y, hcy]
  dsimp only [stepCtrlHAmpC]
  cases hc : x.val.testBit c.val
  · simp only [Bool.false_eq_true, ↓reduceIte, Pi.smul_apply, smul_eq_mul,
      basisState, Pi.single_eq_same, Pi.single_eq_of_ne hyx.symm, mul_one, mul_zero, add_zero]
  · have hex : (st x).1 % 2 = 0 := by
      have hx := List.all_eq_true.mp heven x (List.mem_finRange x)
      simp only [hc, ↓reduceIte, decide_eq_true_eq] at hx
      exact hx
    have hey : (st y).1 % 2 = 0 := by
      have hy := List.all_eq_true.mp heven y (List.mem_finRange y)
      simp only [hcy, hc, ↓reduceIte, decide_eq_true_eq] at hy
      exact hy
    cases ht : x.val.testBit t.val
    · obtain ⟨hbt, hs0, hs1, hyt, hys0, hys1⟩ := hxt0 ht
      simp only [Bool.false_eq_true, ↓reduceIte, ht_last, hbt, hyt, hs0, hs1, hys0, hys1,
        show (1 : ZMod 2) ≠ 0 by decide, qubit_H_entries9.1, qubit_H_entries9.2.2.1,
        Pi.smul_apply, Pi.add_apply, smul_eq_mul, basisState, Pi.single_eq_same,
        Pi.single_eq_of_ne hyx.symm, mul_one, mul_zero, add_zero]
      exact amp32ValC_add_pos (st x) (st y) hex hey
    · obtain ⟨hbt, hs0, hs1, hyt, hys0, hys1⟩ := hxt1 ht
      simp only [↓reduceIte, ht_last, hbt, hyt, hs0, hs1, hys0, hys1,
        show (1 : ZMod 2) ≠ 0 by decide, qubit_H_entries9.2.2.2, qubit_H_entries9.2.1,
        Pi.smul_apply, Pi.add_apply, smul_eq_mul, basisState, Pi.single_eq_same,
        Pi.single_eq_of_ne hyx.symm, mul_one, mul_zero, zero_add]
      exact amp32ValC_sub_pos (st x) (st y) hex hey

/-- Check that `st j` has an even rational part on all `16` computational basis states. -/
private def evenHAmpC (st : Fin (2 ^ 4) → ℤ × ℤ) : Bool :=
  (List.finRange (2 ^ 4)).all fun j ↦ decide ((st j).1 % 2 = 0)

/-- Symbolic `ℤ[√2] / 32` update under an uncontrolled Hadamard `Circuit.H t`. -/
private def stepHAmpC (t : Wire 4) (st : Fin (2 ^ 4) → ℤ × ℤ) (x : Fin (2 ^ 4)) : ℤ × ℤ :=
  let p0 := st (setBitIdx x t 0)
  let p1 := st (setBitIdx x t 1)
  if x.val.testBit t.val then
    (p0.2 - p1.2, p0.1 / 2 - p1.1 / 2)
  else
    (p0.2 + p1.2, p0.1 / 2 + p1.1 / 2)

private theorem eval_H_amp32C (t : Wire 4) (st : Fin (2 ^ 4) → ℤ × ℤ)
    (heven : evenHAmpC st = true) :
    (Circuit.H t).eval.1 *ᵥ evalAmp32C st = evalAmp32C (stepHAmpC t st) := by
  have hc_ex : ∃ c : Wire 4, c ≠ t := by
    by_cases h0 : (0 : Wire 4) = t
    · exact ⟨1, fun h1 ↦ absurd (h0.trans h1.symm) (by decide)⟩
    · exact ⟨0, h0⟩
  obtain ⟨c, hct⟩ := hc_ex
  funext x; rw [evalAmp32C_apply]; dsimp only [evalAmp32C]
  rw [Matrix.mulVec_sum, Finset.sum_apply]
  obtain ⟨hyx, _, hxt0, hxt1⟩ := flipBit4C_props c t hct x
  set y := flipBit4C t x
  have hketH (j : Fin (2 ^ 4)) :
      (Circuit.H t).eval.1 *ᵥ basisState j =
        (if basisBits 4 j t = 0 then
          Qubit.H.1 0 0 • basisState (setBitIdx j t 0) +
            Qubit.H.1 1 0 • basisState (setBitIdx j t 1)
         else
          Qubit.H.1 0 1 • basisState (setBitIdx j t 0) +
            Qubit.H.1 1 1 • basisState (setBitIdx j t 1)) := by
    have hj : basisState j = CoherentAlias.ket (basisBits 4 j) :=
      (congrArg basisState (symm_basisBits_apply j)).symm
    have hs0 : CoherentAlias.ket (Function.update (basisBits 4 j) t 0) =
        basisState (setBitIdx j t 0) := rfl
    have hs1 : CoherentAlias.ket (Function.update (basisBits 4 j) t 1) =
        basisState (setBitIdx j t 1) := rfl
    rw [hj, Circuit.H, Circuit.eval_single, QRegister.embedUnitary_val, PrimitiveGate.eval,
      singleton_embedMatrix_mulVec_ket, hs0, hs1]
    by_cases hbj : basisBits 4 j t = 0 <;> simp [hbj]
  have hother (j : Fin (2 ^ 4)) (hjx : j ≠ x) (hjy : j ≠ y) :
      ((Circuit.H t).eval.1 *ᵥ (amp32ValC (st j) • basisState j)) x = 0 := by
    rw [Matrix.mulVec_smul, hketH j]
    obtain ⟨hn0, hn1⟩ := setBitIdx_other_ne9 t j x hjx hjy
    by_cases hbj : basisBits 4 j t = 0 <;>
      simp [hbj, basisState, Pi.single_eq_of_ne hn0.symm, Pi.single_eq_of_ne hn1.symm]
  rw [(Finset.add_sum_erase _ _ (Finset.mem_univ x)).symm,
    (Finset.add_sum_erase _ _ (Finset.mem_erase.mpr ⟨hyx, Finset.mem_univ y⟩)).symm,
    Finset.sum_eq_zero (fun j hj ↦ by
      have hj1 := Finset.mem_erase.mp hj
      have hj2 := Finset.mem_erase.mp hj1.2
      exact hother j hj2.1 hj1.1), add_zero]
  rw [Matrix.mulVec_smul, Matrix.mulVec_smul, hketH x, hketH y]
  have hex : (st x).1 % 2 = 0 :=
    of_decide_eq_true (List.all_eq_true.mp heven x (List.mem_finRange x))
  have hey : (st y).1 % 2 = 0 :=
    of_decide_eq_true (List.all_eq_true.mp heven y (List.mem_finRange y))
  dsimp only [stepHAmpC]
  cases ht : x.val.testBit t.val
  · obtain ⟨hbt, hs0, hs1, hyt, hys0, hys1⟩ := hxt0 ht
    simp only [Bool.false_eq_true, ↓reduceIte, hbt, hyt, hs0, hs1, hys0, hys1,
      show (1 : ZMod 2) ≠ 0 by decide, qubit_H_entries9.1, qubit_H_entries9.2.2.1,
      Pi.smul_apply, Pi.add_apply, smul_eq_mul, basisState, Pi.single_eq_same,
      Pi.single_eq_of_ne hyx.symm, mul_one, mul_zero, add_zero]
    exact amp32ValC_add_pos (st x) (st y) hex hey
  · obtain ⟨hbt, hs0, hs1, hyt, hys0, hys1⟩ := hxt1 ht
    simp only [↓reduceIte, hbt, hyt, hs0, hs1, hys0, hys1,
      show (1 : ZMod 2) ≠ 0 by decide, qubit_H_entries9.2.2.2, qubit_H_entries9.2.1,
      Pi.smul_apply, Pi.add_apply, smul_eq_mul, basisState, Pi.single_eq_same,
      Pi.single_eq_of_ne hyx.symm, mul_one, mul_zero, zero_add]
    exact amp32ValC_sub_pos (st x) (st y) hex hey

/-- Scaled amplitude table `st1_2` along `optCoin9Circuit`. -/
private def st1_2 : Fin (2 ^ 4) → ℤ × ℤ :=
  fun j ↦ if j.val == 0 || j.val == 1 then (0, 16) else (0, 0)
/-- Scaled amplitude table `st2_2` along `optCoin9Circuit`. -/
private def st2_2 : Fin (2 ^ 4) → ℤ × ℤ := stepCtrlHAmpC 0 1 st1_2
/-- Scaled amplitude table `st3_2` along `optCoin9Circuit`. -/
private def st3_2 : Fin (2 ^ 4) → ℤ × ℤ := stepCtrlHAmpC 1 2 st2_2
/-- Scaled amplitude table `st4` along `optCoin9Circuit`. -/
private def st4 : Fin (2 ^ 4) → ℤ × ℤ := stepCtrlHAmpC 2 1 st3_2
/-- Scaled amplitude table `st5` along `optCoin9Circuit`. -/
private def st5 : Fin (2 ^ 4) → ℤ × ℤ := stepCtrlHAmpC 1 3 st4
/-- Scaled amplitude table `st6` along `optCoin9Circuit`. -/
private def st6 : Fin (2 ^ 4) → ℤ × ℤ := fun x ↦ st5 (cnot4FlipC 2 3 (cnot4FlipC 1 2 x))
/-- Scaled amplitude table `st7` along `optCoin9Circuit`. -/
private def st7 : Fin (2 ^ 4) → ℤ × ℤ := stepCtrlHAmpC 3 1 st6
/-- Scaled amplitude table `st8` along `optCoin9Circuit`. -/
private def st8 : Fin (2 ^ 4) → ℤ × ℤ :=
  fun x ↦ st7 (cnot4FlipC 1 2 (cnot4FlipC 2 3 (cnot4FlipC 2 0 x)))
/-- Scaled amplitude table `st9` along `optCoin9Circuit`. -/
private def st9 : Fin (2 ^ 4) → ℤ × ℤ := stepCtrlHAmpC 1 2 st8
/-- Scaled amplitude table `st10` along `optCoin9Circuit`. -/
private def st10 : Fin (2 ^ 4) → ℤ × ℤ :=
  fun x ↦ st9 (cnot4FlipC 2 0 (cnot4FlipC 2 3 (cnot4FlipC 1 0 x)))
/-- Scaled amplitude table `st11` along `optCoin9Circuit`. -/
private def st11 : Fin (2 ^ 4) → ℤ × ℤ := stepCtrlHAmpC 3 1 st10
/-- Scaled amplitude table `st12` along `optCoin9Circuit`. -/
private def st12 : Fin (2 ^ 4) → ℤ × ℤ :=
  fun x ↦ st11 (cnot4FlipC 1 0 (cnot4FlipC 2 3 (cnot4FlipC 3 1 x)))
/-- Scaled amplitude table `st13` along `optCoin9Circuit`. -/
private def st13 : Fin (2 ^ 4) → ℤ × ℤ := stepHAmpC 3 st12
/-- Scaled amplitude table `st14` along `optCoin9Circuit`. -/
private def st14 : Fin (2 ^ 4) → ℤ × ℤ :=
  fun x ↦ st13 (cnot4FlipC 3 1 (cnot4FlipC 0 1 (cnot4FlipC 1 3 x)))

/-- Exact integer packet weights (`sum = 512`) for `optCoin9Unitary`. -/
def coin9Weight : Fin (2 ^ 4) → ℕ :=
  ![128, 0, 128, 32, 1, 1, 1, 1, 2, 64, 2, 64, 4, 16, 4, 64]

theorem sumCoin9Weight : ∑ pkt : Fin (2 ^ 4), coin9Weight pkt = 512 := by decide

private theorem optCoin9_mulVec_zero_eq :
    optCoin9Unitary.1 *ᵥ basisState 0 = evalAmp32C st14 := by
  dsimp only [optCoin9Unitary, optCoin9Circuit]
  simp only [Circuit.eval_seq, Submonoid.coe_mul, ← Matrix.mulVec_mulVec]
  rw [eval_H0_zero9]
  rw [show (fun j : Fin (2 ^ 4) ↦ if (j.val == 0 || j.val == 1) = true then ((0 : ℤ), (16 : ℤ))
    else (0, 0)) = st1_2 from rfl]
  rw [eval_ctrlH_amp32C 0 1 (by decide) st1_2 (by decide),
    show stepCtrlHAmpC 0 1 st1_2 = st2_2 from rfl]
  rw [eval_ctrlH_amp32C 1 2 (by decide) st2_2 (by decide),
    show stepCtrlHAmpC 1 2 st2_2 = st3_2 from rfl]
  rw [eval_ctrlH_amp32C 2 1 (by decide) st3_2 (by decide),
    show stepCtrlHAmpC 2 1 st3_2 = st4 from rfl]
  rw [eval_ctrlH_amp32C 1 3 (by decide) st4 (by decide),
    show stepCtrlHAmpC 1 3 st4 = st5 from rfl]
  rw [eval_CNOT_amp32C 2 3 (by decide) st5, eval_CNOT_amp32C 1 2 (by decide),
    show (fun x ↦ st5 (cnot4FlipC 2 3 (cnot4FlipC 1 2 x))) = st6 from rfl]
  rw [eval_ctrlH_amp32C 3 1 (by decide) st6 (by decide),
    show stepCtrlHAmpC 3 1 st6 = st7 from rfl]
  rw [eval_CNOT_amp32C 1 2 (by decide) st7, eval_CNOT_amp32C 2 3 (by decide),
    eval_CNOT_amp32C 2 0 (by decide),
    show (fun x ↦ st7 (cnot4FlipC 1 2 (cnot4FlipC 2 3 (cnot4FlipC 2 0 x)))) = st8 from rfl]
  rw [eval_ctrlH_amp32C 1 2 (by decide) st8 (by decide),
    show stepCtrlHAmpC 1 2 st8 = st9 from rfl]
  rw [eval_CNOT_amp32C 2 0 (by decide) st9, eval_CNOT_amp32C 2 3 (by decide),
    eval_CNOT_amp32C 1 0 (by decide),
    show (fun x ↦ st9 (cnot4FlipC 2 0 (cnot4FlipC 2 3 (cnot4FlipC 1 0 x)))) = st10 from rfl]
  rw [eval_ctrlH_amp32C 3 1 (by decide) st10 (by decide),
    show stepCtrlHAmpC 3 1 st10 = st11 from rfl]
  rw [eval_CNOT_amp32C 1 0 (by decide) st11, eval_CNOT_amp32C 2 3 (by decide),
    eval_CNOT_amp32C 3 1 (by decide),
    show (fun x ↦ st11 (cnot4FlipC 1 0 (cnot4FlipC 2 3 (cnot4FlipC 3 1 x)))) = st12 from rfl]
  rw [eval_H_amp32C 3 st12 (by decide),
    show stepHAmpC 3 st12 = st13 from rfl]
  rw [eval_CNOT_amp32C 3 1 (by decide) st13, eval_CNOT_amp32C 0 1 (by decide),
    eval_CNOT_amp32C 1 3 (by decide)]
  rfl

private theorem normSq_amp32ValC_of_eq (p : ℤ × ℤ) (w : ℕ)
    (horth : p.1 * p.2 = 0) (hw : p.1 * p.1 + 2 * (p.2 * p.2) = 2 * (w : ℤ)) :
    Complex.normSq (amp32ValC p) = (w : ℝ) / 512 := by
  dsimp only [amp32ValC]; rw [Complex.normSq_ofReal]
  have hsq : √2 * √2 = (2 : ℝ) := Real.mul_self_sqrt (by norm_num)
  have ho : (p.1 : ℝ) * (p.2 : ℝ) = 0 := by exact_mod_cast horth
  have hwr : (p.1 : ℝ) * (p.1 : ℝ) + 2 * ((p.2 : ℝ) * (p.2 : ℝ)) = 2 * (w : ℝ) := by
    exact_mod_cast hw
  calc (((p.1 : ℝ) + (p.2 : ℝ) * √2) / 32) * (((p.1 : ℝ) + (p.2 : ℝ) * √2) / 32)
      = ((p.1 : ℝ) * (p.1 : ℝ) + (p.2 : ℝ) * (p.2 : ℝ) * (√2 * √2) +
          2 * ((p.1 : ℝ) * (p.2 : ℝ)) * √2) / 1024 := by ring
    _ = (w : ℝ) / 512 := by rw [hsq, ho]; linarith

private theorem st14_weight_check :
    ((List.finRange (2 ^ 4)).all fun pkt ↦
      decide ((st14 pkt).1 * (st14 pkt).2 = 0 ∧
        (st14 pkt).1 * (st14 pkt).1 + 2 * ((st14 pkt).2 * (st14 pkt).2) =
          2 * (coin9Weight pkt : ℤ))) = true := by decide

theorem optCoin9Unitary_col_zero_normSq (pkt : Fin (2 ^ 4)) :
    Complex.normSq (optCoin9Unitary.1 pkt 0) = (coin9Weight pkt : ℝ) / 512 := by
  have h0 : optCoin9Unitary.1 pkt 0 = (optCoin9Unitary.1 *ᵥ basisState 0) pkt := by
    simp [basisState]
  have hc := of_decide_eq_true (List.all_eq_true.mp st14_weight_check pkt (List.mem_finRange pkt))
  rw [h0, optCoin9_mulVec_zero_eq, evalAmp32C_apply]
  exact normSq_amp32ValC_of_eq (st14 pkt) (coin9Weight pkt) hc.1 hc.2

attribute [irreducible] optCoin9Unitary optCoin9Dyn optCoin9InvDyn

/-- Closed-form Boolean expression for the `9`-AND dyadic packet multiplexer. -/
def mux9Formula (p0 p1 p2 p3 k0 k1 k2 k3 k4 k5 k6 k7 k8 : Bool) : Bool :=
  let w13 := xor (xor false k5) k8
  let w14 := p0 && w13
  let w15 := p0 && k0
  let w16 := xor (xor false k1) w15
  let w17 := p1 && w16
  let w18 := xor (xor (xor (xor false k1) k8) w14) w17
  let w19 := p2 && w18
  let w20 := xor (xor false k2) k3
  let w21 := p2 && w20
  let w22 := xor (xor false k4) k6
  let w23 := p2 && w22
  let w24 := xor (xor (xor false k6) k7) w23
  let w25 := p1 && w24
  let w26 := xor (xor (xor (xor (xor false k2) k6) w21) w23) w25
  let w27 := p0 && w26
  let w28 := xor (xor (xor (xor (xor (xor false k2) k8) w14) w19) w21) w27
  let w29 := p3 && w28
  xor (xor (xor (xor true k8) w14) w19) w29

/-- Exact `9`-bit swap decision bit `mux9Bit pkt keep` (`false` = keep primary, `true` = swap to
`alt`). -/
def mux9Bit (pkt : Fin (2 ^ 4)) (keep : Fin (2 ^ 9)) : Bool :=
  mux9Formula
    (bitsOfFin 4 pkt 0) (bitsOfFin 4 pkt 1) (bitsOfFin 4 pkt 2) (bitsOfFin 4 pkt 3)
    (bitsOfFin 9 keep 0) (bitsOfFin 9 keep 1) (bitsOfFin 9 keep 2) (bitsOfFin 9 keep 3)
    (bitsOfFin 9 keep 4) (bitsOfFin 9 keep 5) (bitsOfFin 9 keep 6) (bitsOfFin 9 keep 7)
    (bitsOfFin 9 keep 8)

/-- Computable binary digit test `(n / d) % 2 == 1`. -/
private def bitNat9 (n d : ℕ) : Bool := Nat.beq ((n / d) % 2) 1

private theorem bitsOfFin_eq_bitNat9 {b : ℕ} (c : Fin (2 ^ b)) (j : Fin b) :
    bitsOfFin b c j = bitNat9 c.val (2 ^ j.val) := by
  dsimp only [bitNat9]; rw [bitsOfFin_eq_div_mod]
  by_cases h : (c.val / 2 ^ j.val) % 2 = 1
  · simp [h]
  · have hbeq : Nat.beq ((c.val / 2 ^ j.val) % 2) 1 = false :=
      Bool.eq_false_iff.mpr (mt Nat.beq_eq.mp h)
    simp [h, hbeq]

private theorem mux9Bit_eq_fast (pkt : Fin (2 ^ 4)) (keep : Fin (2 ^ 9)) :
    mux9Bit pkt keep = mux9Formula
      (bitNat9 pkt.val 1) (bitNat9 pkt.val 2) (bitNat9 pkt.val 4) (bitNat9 pkt.val 8)
      (bitNat9 keep.val 1) (bitNat9 keep.val 2) (bitNat9 keep.val 4) (bitNat9 keep.val 8)
      (bitNat9 keep.val 16) (bitNat9 keep.val 32) (bitNat9 keep.val 64)
      (bitNat9 keep.val 128) (bitNat9 keep.val 256) := by
  dsimp only [mux9Bit]
  rw [bitsOfFin_eq_bitNat9 pkt 0, bitsOfFin_eq_bitNat9 pkt 1,
    bitsOfFin_eq_bitNat9 pkt 2, bitsOfFin_eq_bitNat9 pkt 3,
    bitsOfFin_eq_bitNat9 keep 0, bitsOfFin_eq_bitNat9 keep 1,
    bitsOfFin_eq_bitNat9 keep 2, bitsOfFin_eq_bitNat9 keep 3,
    bitsOfFin_eq_bitNat9 keep 4, bitsOfFin_eq_bitNat9 keep 5,
    bitsOfFin_eq_bitNat9 keep 6, bitsOfFin_eq_bitNat9 keep 7,
    bitsOfFin_eq_bitNat9 keep 8]
  rfl

/-- Explicit `16`-element sum over `Fin (2 ^ 4)` for `decide`. -/
private def sum16Coin9 (f : Fin (2 ^ 4) → ℕ) : ℕ :=
  f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 +
  f 8 + f 9 + f 10 + f 11 + f 12 + f 13 + f 14 + f 15

private theorem finset_sum16Coin9_eq (f : Fin (2 ^ 4) → ℕ) :
    (∑ pkt : Fin (2 ^ 4), f pkt) = sum16Coin9 f := by
  have huniv : (Finset.univ : Finset (Fin (2 ^ 4))) =
      {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15} := by decide
  rw [huniv]
  repeat rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_singleton]; dsimp only [sum16Coin9]; omega

/-- Computable predicate verifying `mux9Formula` fiber weights at index `k < 4096`. -/
private def mux9FastPred9 (k : ℕ) : Bool :=
  let k0 := bitNat9 k 1;   let k1 := bitNat9 k 2;   let k2 := bitNat9 k 4
  let k3 := bitNat9 k 8;   let k4 := bitNat9 k 16;  let k5 := bitNat9 k 32
  let k6 := bitNat9 k 64;  let k7 := bitNat9 k 128; let k8 := bitNat9 k 256
  Nat.beq
    (cond (mux9Formula false false false false k0 k1 k2 k3 k4 k5 k6 k7 k8) 0 128 +
     0 +
     cond (mux9Formula false true  false false k0 k1 k2 k3 k4 k5 k6 k7 k8) 0 128 +
     cond (mux9Formula true  true  false false k0 k1 k2 k3 k4 k5 k6 k7 k8) 0 32 +
     cond (mux9Formula false false true  false k0 k1 k2 k3 k4 k5 k6 k7 k8) 0 1 +
     cond (mux9Formula true  false true  false k0 k1 k2 k3 k4 k5 k6 k7 k8) 0 1 +
     cond (mux9Formula false true  true  false k0 k1 k2 k3 k4 k5 k6 k7 k8) 0 1 +
     cond (mux9Formula true  true  true  false k0 k1 k2 k3 k4 k5 k6 k7 k8) 0 1 +
     cond (mux9Formula false false false true  k0 k1 k2 k3 k4 k5 k6 k7 k8) 0 2 +
     cond (mux9Formula true  false false true  k0 k1 k2 k3 k4 k5 k6 k7 k8) 0 64 +
     cond (mux9Formula false true  false true  k0 k1 k2 k3 k4 k5 k6 k7 k8) 0 2 +
     cond (mux9Formula true  true  false true  k0 k1 k2 k3 k4 k5 k6 k7 k8) 0 64 +
     cond (mux9Formula false false true  true  k0 k1 k2 k3 k4 k5 k6 k7 k8) 0 4 +
     cond (mux9Formula true  false true  true  k0 k1 k2 k3 k4 k5 k6 k7 k8) 0 16 +
     cond (mux9Formula false true  true  true  k0 k1 k2 k3 k4 k5 k6 k7 k8) 0 4 +
     cond (mux9Formula true  true  true  true  k0 k1 k2 k3 k4 k5 k6 k7 k8) 0 64)
    k

private theorem mux9Fast9_all : allPow2 9 0 mux9FastPred9 = true := by decide

theorem mux9_fiber_weight (keep : Fin (2 ^ 9)) :
    (∑ pkt : Fin (2 ^ 4), if mux9Bit pkt keep = false then coin9Weight pkt else 0) =
      keep.val := by
  have hall := Nat.beq_eq.mp (allPow2_zero_true mux9Fast9_all keep.val keep.isLt)
  have hcongr : (fun pkt : Fin (2 ^ 4) ↦
        if mux9Bit pkt keep = false then coin9Weight pkt else 0) =
      (fun pkt : Fin (2 ^ 4) ↦ cond (mux9Bit pkt keep) 0 (coin9Weight pkt)) :=
    funext fun pkt ↦ by cases mux9Bit pkt keep <;> rfl
  have hz (b : Bool) : cond b 0 0 = 0 := by cases b <;> rfl
  rw [hcongr, finset_sum16Coin9_eq]
  dsimp only [sum16Coin9]
  simp only [coin9Weight, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, hz,
    mux9Bit_eq_fast]
  exact hall

theorem mux9_fiber_weight_true (keep : Fin (2 ^ 9)) :
    (∑ pkt : Fin (2 ^ 4), if mux9Bit pkt keep = true then coin9Weight pkt else 0) =
      512 - keep.val := by
  have hsplit : (∑ pkt : Fin (2 ^ 4), coin9Weight pkt) =
      (∑ pkt : Fin (2 ^ 4), if mux9Bit pkt keep = false then coin9Weight pkt else 0) +
      (∑ pkt : Fin (2 ^ 4), if mux9Bit pkt keep = true then coin9Weight pkt else 0) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun pkt _ ↦ ?_
    cases mux9Bit pkt keep <;> simp
  have hf := mux9_fiber_weight keep
  have hs := sumCoin9Weight
  omega

/-- Subspace-restricted computational-basis operator mapping `ket β ↦ f β` when `S β` holds. -/
private noncomputable def ketMapOp14 {n : ℕ} (S : BitAssignment n → Prop)
    (f : BitAssignment n → (Fin (2 ^ n) → ℂ)) : Operator (2 ^ n) :=
  open Classical in
  Matrix.of fun i j ↦ if S (basisBits n j) then f (basisBits n j) i else 0

private theorem ketMapOp14_mulVec_ket {n : ℕ} (S : BitAssignment n → Prop) [DecidablePred S]
    (f : BitAssignment n → (Fin (2 ^ n) → ℂ)) (β : BitAssignment n) :
    (ketMapOp14 S f).mulVec (XMeasCircuit.ket β) = if S β then f β else 0 := by
  classical
  ext i
  have h1 : (ketMapOp14 S f).mulVec (XMeasCircuit.ket β) i =
      ketMapOp14 S f i ((basisBits n).symm β) := by
    simp [XMeasCircuit.ket, basisState]
  rw [h1]
  simp only [ketMapOp14, Matrix.of_apply, XMeasCircuit.basisBits_basisBitsEquiv_symm]
  split_ifs <;> simp

private theorem mul_ketMapOp14 {n : ℕ} (A : Operator (2 ^ n)) (S : BitAssignment n → Prop)
    (f : BitAssignment n → (Fin (2 ^ n) → ℂ)) :
    A * ketMapOp14 S f = ketMapOp14 S (fun β ↦ A.mulVec (f β)) := by
  classical
  refine XMeasCircuit.matrix_ext_ket fun β ↦ ?_
  rw [← Matrix.mulVec_mulVec, ketMapOp14_mulVec_ket, ketMapOp14_mulVec_ket]
  split_ifs <;> simp

private theorem smul_ketMapOp14 {n : ℕ} (c : ℂ) (S : BitAssignment n → Prop)
    (f : BitAssignment n → (Fin (2 ^ n) → ℂ)) :
    c • ketMapOp14 S f = ketMapOp14 S (fun β ↦ c • f β) := by
  classical
  refine XMeasCircuit.matrix_ext_ket fun β ↦ ?_
  rw [Matrix.smul_mulVec, ketMapOp14_mulVec_ket, ketMapOp14_mulVec_ket]
  split_ifs <;> simp

private theorem ketMapOp14_congr {n : ℕ} {S : BitAssignment n → Prop}
    {f g : BitAssignment n → (Fin (2 ^ n) → ℂ)} (h : ∀ β, S β → f β = g β) :
    ketMapOp14 S f = ketMapOp14 S g := by
  classical
  refine XMeasCircuit.matrix_ext_ket fun β ↦ ?_
  rw [ketMapOp14_mulVec_ket, ketMapOp14_mulVec_ket]
  by_cases hS : S β
  · simp [hS, h β hS]
  · simp [hS]

/-- Classical store `v`-invariance predicate for dynamic-circuit `wp` assertions. -/
abbrev IsVInv14 {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    (v : Var) (Θ : QCAssertion Var (2 ^ n)) : Prop :=
  ∀ σ val, Θ (Function.update σ v val) = Θ σ

/-- Compositional `wp` conjugation step from subspace operator `R₀` to `R₁`. -/
private def SubspaceStepV14 {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    (v : Var) (R₀ R₁ : Operator (2 ^ n)) (d : DynamicCircuit Var n) : Prop :=
  d.count .TOFF = 0 ∧
    ∀ Θ : QCAssertion Var (2 ^ n), IsVInv14 v Θ →
      IsVInv14 v (wp d.compile Θ) ∧
        ∀ σ : Store Var, R₀ᴴ * (wp d.compile Θ σ).1.1 * R₀ = R₁ᴴ * (Θ σ).1.1 * R₁

private theorem SubspaceStepV14.congr {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    {v : Var} {R₀ R₀' R₁ R₁' : Operator (2 ^ n)} {d : DynamicCircuit Var n}
    (h₀ : R₀ = R₀') (h₁ : R₁ = R₁') (h : SubspaceStepV14 v R₀ R₁ d) :
    SubspaceStepV14 v R₀' R₁' d := by
  subst h₀; subst h₁; exact h

private theorem SubspaceStepV14.mul_right {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    {v : Var} {R₀ R₁ : Operator (2 ^ n)} {d : DynamicCircuit Var n} (A : Operator (2 ^ n))
    (h : SubspaceStepV14 v R₀ R₁ d) :
    SubspaceStepV14 v (R₀ * A) (R₁ * A) d :=
  ⟨h.1, fun Θ hΘ ↦
    let ⟨hInv, heq⟩ := h.2 Θ hΘ
    ⟨hInv, fun σ ↦ by
      calc (R₀ * A)ᴴ * (wp d.compile Θ σ).1.1 * (R₀ * A)
          = Aᴴ * (R₀ᴴ * (wp d.compile Θ σ).1.1 * R₀) * A := by
              rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
        _ = Aᴴ * (R₁ᴴ * (Θ σ).1.1 * R₁) * A := by rw [heq σ]
        _ = (R₁ * A)ᴴ * (Θ σ).1.1 * (R₁ * A) := by
              rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]⟩⟩

private theorem SubspaceStepV14.seq {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    {v : Var} {R₀ R₁ R₂ : Operator (2 ^ n)} {d₁ d₂ : DynamicCircuit Var n}
    (h₁ : SubspaceStepV14 v R₀ R₁ d₁) (h₂ : SubspaceStepV14 v R₁ R₂ d₂) :
    SubspaceStepV14 v R₀ R₂ (.seq d₁ d₂) :=
  ⟨by simp [DynamicCircuit.count, h₁.1, h₂.1], fun Θ hΘ ↦ by
    obtain ⟨hInv₂, heq₂⟩ := h₂.2 Θ hΘ
    obtain ⟨hInv₁, heq₁⟩ := h₁.2 (wp d₂.compile Θ) hInv₂
    have hseq : wp (d₁.seq d₂).compile Θ = wp d₁.compile (wp d₂.compile Θ) := by
      rw [DynamicCircuit.compile_seq, wp_qSeq]
    rw [hseq]
    exact ⟨hInv₁, fun σ ↦ (heq₁ σ).trans (heq₂ σ)⟩⟩

private theorem SubspaceStepV14.of_circuit {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    {v : Var} {R₀ R₁ : Operator (2 ^ n)} (c : Circuit n)
    (hc0 : c.count .TOFF = 0) (hc : c.eval.1 * R₀ = R₁) :
    SubspaceStepV14 v R₀ R₁ (.circuit c) :=
  ⟨hc0, fun Θ hΘ ↦ by
    have hwp (σ : Store Var) : wp (DynamicCircuit.circuit c).compile Θ σ =
        qcQAssignObsMap c.eval (Θ σ) := by
      rw [DynamicCircuit.compile_circuit, DynamicCircuit.qc_wp_circuit_compile (Var := Var),
        qcWpQAssign]
    refine ⟨fun σ val ↦ by rw [hwp, hwp, hΘ σ val], fun σ ↦ ?_⟩
    have hM : (qcQAssignObsMap c.eval (Θ σ)).1.1 = c.eval.1ᴴ * (Θ σ).1.1 * c.eval.1 := by
      simp [qcQAssignObsMap, Matrix.star_eq_conjTranspose]
    have hadj : R₀ᴴ * c.eval.1ᴴ = R₁ᴴ := by
      simpa only [Matrix.conjTranspose_mul] using congrArg Matrix.conjTranspose hc
    rw [hwp, hM]
    calc R₀ᴴ * (c.eval.1ᴴ * (Θ σ).1.1 * c.eval.1) * R₀
        = (R₀ᴴ * c.eval.1ᴴ) * (Θ σ).1.1 * (c.eval.1 * R₀) := by simp only [Matrix.mul_assoc]
      _ = R₁ᴴ * (Θ σ).1.1 * R₁ := by rw [hadj, hc]⟩

private theorem SubspaceStepV14.remeasure {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    {v : Var} {R₀ R₁ : Operator (2 ^ n)} (q : Wire n) (onOne : DynamicCircuit Var n)
    (h0 : (QRegister.singleton q).basisOutcomeProjector 0 * R₀ = XMeasCircuit.sqrtHalf • R₁)
    (h1 : SubspaceStepV14 v ((QRegister.singleton q).basisOutcomeProjector 1 * R₀)
      (XMeasCircuit.sqrtHalf • R₁) onOne) :
    SubspaceStepV14 v R₀ R₁ (XMeasCircuit.remeasureIfDyn v q onOne) :=
  ⟨by simp [h1.1], fun Θ hΘ ↦ by
    obtain ⟨hInv₁, heq₁⟩ := h1.2 Θ hΘ
    refine ⟨fun σ val ↦ XMeasCircuit.wp_remeasureIfDyn_update_self v q onOne Θ σ val, fun σ ↦ ?_⟩
    let P₀ := (QRegister.singleton q).basisOutcomeProjector 0
    let P₁ := (QRegister.singleton q).basisOutcomeProjector 1
    have hP₀h : P₀ᴴ = P₀ := QRegister.basisOutcomeProjector_conjTranspose _ 0
    have hP₁h : P₁ᴴ = P₁ := QRegister.basisOutcomeProjector_conjTranspose _ 1
    have hM' : (wp (XMeasCircuit.remeasureIfDyn v q onOne).compile Θ σ).1.1 =
        P₀ * (Θ σ).1.1 * P₀ᴴ + P₁ * (wp onOne.compile Θ σ).1.1 * P₁ᴴ := by
      have hv := XMeasCircuit.wp_remeasureIfDyn_apply v q onOne Θ σ
      rw [hΘ σ 0, hInv₁ σ 1] at hv
      exact congrArg Subtype.val hv
    have h0Eq : (P₀ * R₀)ᴴ * (Θ σ).1.1 * (P₀ * R₀) =
        (XMeasCircuit.sqrtHalf • R₁)ᴴ * (Θ σ).1.1 * (XMeasCircuit.sqrtHalf • R₁) := by rw [h0]
    have hsum : R₀ᴴ * (wp (XMeasCircuit.remeasureIfDyn v q onOne).compile Θ σ).1.1 * R₀ =
        (P₀ * R₀)ᴴ * (Θ σ).1.1 * (P₀ * R₀) +
          (P₁ * R₀)ᴴ * (wp onOne.compile Θ σ).1.1 * (P₁ * R₀) := by
      rw [hM', hP₀h, hP₁h, Matrix.mul_add, Matrix.add_mul]
      simp only [Matrix.conjTranspose_mul, hP₀h, hP₁h, Matrix.mul_assoc]
    rw [hsum, h0Eq, heq₁ σ]
    simp only [Matrix.conjTranspose_smul, XMeasCircuit.star_sqrtHalf, Matrix.smul_mul,
      Matrix.mul_smul, smul_smul, ← add_smul, XMeasCircuit.sqrtHalf_mul_sqrtHalf]
    norm_num⟩

private theorem SubspaceStepV14.xMeasUnload_circuit {Var : Type} [Fintype Var] [DecidableEq Var]
    {n : ℕ} {v : Var} {R₁ : Operator (2 ^ n)} (q : Wire n)
    (f : BitAssignment n → ZMod 2) (hf : ∀ β b, f (Function.update β q b) = f β)
    (cFix : Circuit n) (hcFix0 : cFix.count .TOFF = 0)
    (hcFix : cFix.eval = XMeasCircuit.phaseFlipUnitary f)
    (hClean : XMeasCircuit.cleanFinsetProj {q} * R₁ = R₁) :
    SubspaceStepV14 v ((XMeasCircuit.xorWireUnitary q f hf).1 * R₁) R₁
      (XMeasCircuit.xMeasUnloadWireDyn v q (.circuit cFix)) := by
  let Uxor := (XMeasCircuit.xorWireUnitary q f hf).1
  let Hq := (Circuit.H q).eval.1
  let Xq := (Circuit.X q).eval.1
  let P₀ := (QRegister.singleton q).basisOutcomeProjector 0
  let P₁ := (QRegister.singleton q).basisOutcomeProjector 1
  have hmem : q ∈ ({q} : Finset (Wire n)) := Finset.mem_singleton_self q
  refine SubspaceStepV14.seq (SubspaceStepV14.of_circuit (Circuit.H q) rfl rfl)
    (SubspaceStepV14.remeasure q _ ?_ ?_)
  · calc P₀ * (Hq * (Uxor * R₁))
        = ((P₀ * Hq) * Uxor * XMeasCircuit.cleanFinsetProj {q}) * R₁ := by
            nth_rw 1 [← hClean]; simp only [Matrix.mul_assoc]
      _ = (XMeasCircuit.sqrtHalf • XMeasCircuit.cleanFinsetProj {q}) * R₁ := by
            rw [XMeasCircuit.xMeas_kraus_zero q {q} hmem f hf]
      _ = XMeasCircuit.sqrtHalf • R₁ := by rw [Matrix.smul_mul, hClean]
  · refine SubspaceStepV14.seq (SubspaceStepV14.of_circuit (Circuit.X q) rfl rfl)
      (SubspaceStepV14.of_circuit cFix hcFix0 ?_)
    have hkr1 : (Xq * P₁ * Hq) * Uxor * XMeasCircuit.cleanFinsetProj {q} =
        XMeasCircuit.sqrtHalf • (XMeasCircuit.cleanFinsetProj {q} *
          (XMeasCircuit.phaseFlipUnitary f).1) :=
      XMeasCircuit.xMeas_kraus_one q {q} hmem f hf
    have hsq : (XMeasCircuit.phaseFlipUnitary f).1 * (XMeasCircuit.phaseFlipUnitary f).1 = 1 :=
      congrArg Subtype.val (XMeasCircuit.phaseFlipUnitary_mul_self f)
    calc cFix.eval.1 * (Xq * (P₁ * (Hq * (Uxor * R₁))))
        = cFix.eval.1 * (((Xq * P₁ * Hq) * Uxor * XMeasCircuit.cleanFinsetProj {q}) * R₁) := by
            nth_rw 1 [← hClean]; simp only [Matrix.mul_assoc]
      _ = (XMeasCircuit.phaseFlipUnitary f).1 *
            ((XMeasCircuit.sqrtHalf • (XMeasCircuit.cleanFinsetProj {q} *
              (XMeasCircuit.phaseFlipUnitary f).1)) * R₁) := by rw [hcFix, hkr1]
      _ = XMeasCircuit.sqrtHalf •
            (((XMeasCircuit.phaseFlipUnitary f).1 *
              (XMeasCircuit.cleanFinsetProj {q} * (XMeasCircuit.phaseFlipUnitary f).1)) * R₁) := by
            rw [Matrix.smul_mul, Matrix.mul_smul, ← Matrix.mul_assoc]
      _ = XMeasCircuit.sqrtHalf • R₁ := by
            rw [← Matrix.mul_assoc (XMeasCircuit.phaseFlipUnitary f).1,
              XMeasCircuit.phaseFlipUnitary_comm_cleanFinsetProj f {q},
              Matrix.mul_assoc (XMeasCircuit.cleanFinsetProj {q}), hsq, Matrix.mul_one, hClean]

/-- Primitive `8`-th root of unity `(1 + i) / √2` for `T`-gate ket evolution. -/
private noncomputable def omega8Cn : ℂ := (1 + Complex.I) / (√2 : ℂ)

private theorem omega8Cn_eq : omega8Cn = (1 + Complex.I) * XMeasCircuit.sqrtHalf := by
  dsimp only [omega8Cn, XMeasCircuit.sqrtHalf]
  have h2 : (√2 : ℂ) ≠ 0 := by exact_mod_cast Real.sqrt_ne_zero'.mpr (by norm_num)
  have hmul : (√(1 / 2 : ℝ) : ℂ) * (√2 : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, ← Real.sqrt_mul (by norm_num)]; norm_num
  rw [div_eq_iff h2, mul_assoc, hmul, mul_one]

private theorem sqrtHalf_sq2 : XMeasCircuit.sqrtHalf ^ 2 = 1 / 2 := by
  linear_combination XMeasCircuit.sqrtHalf_mul_sqrtHalf

private theorem sqrtHalf_pow3 : XMeasCircuit.sqrtHalf ^ 3 = (1 / 2) * XMeasCircuit.sqrtHalf := by
  linear_combination XMeasCircuit.sqrtHalf * sqrtHalf_sq2

private theorem sqrtHalf_pow4 : XMeasCircuit.sqrtHalf ^ 4 = 1 / 4 := by
  linear_combination (XMeasCircuit.sqrtHalf ^ 2 + 1 / 2) * sqrtHalf_sq2

private theorem i_pow3 : Complex.I ^ 3 = -Complex.I := by
  linear_combination Complex.I * Complex.I_sq

private theorem i_pow4 : Complex.I ^ 4 = 1 := by
  linear_combination (Complex.I ^ 2 - 1) * Complex.I_sq

private theorem ket_S2 {n : ℕ} (q : Wire n) (β : BitAssignment n) :
    (Circuit.S q).eval.1.mulVec (XMeasCircuit.ket β) =
      (if β q = 0 then (1 : ℂ) else Complex.I) • XMeasCircuit.ket β := by
  rw [Circuit.eval_single, QRegister.embedUnitary_val, PrimitiveGate.eval]
  change ((QRegister.singleton q).embedMatrix !![1, 0; 0, Complex.I]).mulVec _ = _
  rw [XMeasCircuit.singleton_embedMatrix_mulVec_ket]
  have e := Function.update_eq_self q β
  rcases CircuitModular.UnsignedGivens.zmod2_eq_zero_or_one (β q) with hb | hb <;>
    rw [hb] at e <;> simp [hb, e]

private theorem ket_T2 {n : ℕ} (q : Wire n) (β : BitAssignment n) :
    (Circuit.T q).eval.1.mulVec (XMeasCircuit.ket β) =
      (if β q = 0 then (1 : ℂ) else omega8Cn) • XMeasCircuit.ket β := by
  rw [Circuit.eval_single, QRegister.embedUnitary_val, PrimitiveGate.eval]
  change ((QRegister.singleton q).embedMatrix !![1, 0; 0, omega8Cn]).mulVec _ = _
  rw [XMeasCircuit.singleton_embedMatrix_mulVec_ket]
  have e := Function.update_eq_self q β
  rcases CircuitModular.UnsignedGivens.zmod2_eq_zero_or_one (β q) with hb | hb <;>
    rw [hb] at e <;> simp [hb, e]

private theorem ket_CNOT2 {n : ℕ} (c t : Wire n) (h : c ≠ t) (β : BitAssignment n) :
    (Circuit.CNOT c t h).eval.1.mulVec (XMeasCircuit.ket β) =
      XMeasCircuit.ket (Function.update β t (β t + β c)) :=
  CircuitModular.UnsignedGivens.evolve_CNOT_ket c t h β

private theorem eval_seq_mulVec2 {n : ℕ} (c₁ c₂ : Circuit n) (ψ : Fin (2 ^ n) → ℂ) :
    (c₁ ;;ᶜ c₂).eval.1.mulVec ψ = c₂.eval.1.mulVec (c₁.eval.1.mulVec ψ) := by
  rw [Circuit.eval_seq, Submonoid.coe_mul, ← Matrix.mulVec_mulVec]

private theorem wSplitPair4_mulVec_ket_00 {n : ℕ} (a b : Wire n) (h : a ≠ b)
    {β : BitAssignment n} (ha : β a = 0) (hb : β b = 0) :
    (wSplitPair4 a b h).eval.1.mulVec (XMeasCircuit.ket β) = XMeasCircuit.ket β := by
  have hub0 : Function.update β b 0 = β := Function.update_eq_self_iff.mpr hb.symm
  have hua0 : Function.update β a 0 = β := Function.update_eq_self_iff.mpr ha.symm
  have h10 : ((1 : ZMod 2) = 0) = False := by decide
  simp only [wSplitPair4, eval_seq_mulVec2, ket_S2, ket_T2, XMeasCircuit.ket_H,
    XMeasCircuit.ket_Z, ket_CNOT2, Matrix.mulVec_smul, Matrix.mulVec_add, ha, hb, h10, ↓reduceIte,
    one_smul, add_zero, zero_add, Function.update_self, Function.update_idem,
    Function.update_of_ne h, hub0, hua0, XMeasCircuit.bitSign, smul_add, smul_smul]
  rw [add_add_add_comm, ← add_smul, ← add_smul]
  refine (congrArg₂ (· + ·) (congrArg (· • _) (?_ : _ = (1 : ℂ)))
    (congrArg (· • _) (?_ : _ = (0 : ℂ)))).trans (by simp)
  · rw [omega8Cn_eq]; ring_nf; simp only [sqrtHalf_sq2, sqrtHalf_pow4, Complex.I_sq,
      i_pow3]; ring
  · rw [omega8Cn_eq]; ring_nf
    simp only [sqrtHalf_sq2, sqrtHalf_pow4, Complex.I_sq, i_pow3, i_pow4]; ring

private theorem wSplitPair4_mulVec_ket_10 {n : ℕ} (a b : Wire n) (h : a ≠ b)
    {β : BitAssignment n} (ha : β a = 1) (hb : β b = 0) :
    (wSplitPair4 a b h).eval.1.mulVec (XMeasCircuit.ket β) =
      XMeasCircuit.sqrtHalf • XMeasCircuit.ket β +
        XMeasCircuit.sqrtHalf • XMeasCircuit.ket (Function.update (Function.update β a 0) b 1) := by
  have hub0 : Function.update β b 0 = β := Function.update_eq_self_iff.mpr hb.symm
  have hua1 : Function.update β a 1 = β := Function.update_eq_self_iff.mpr ha.symm
  have h11 : (1 : ZMod 2) + 1 = 0 := rfl
  have h10 : ((1 : ZMod 2) = 0) = False := by decide
  have hcomm : Function.update (Function.update β b 1) a 0 =
      Function.update (Function.update β a 0) b 1 := Function.update_comm h.symm 1 0 β
  simp only [wSplitPair4, eval_seq_mulVec2, ket_S2, ket_T2, XMeasCircuit.ket_H,
    XMeasCircuit.ket_Z, ket_CNOT2, Matrix.mulVec_smul, Matrix.mulVec_add, ha, hb, h11, h10,
    ↓reduceIte, one_smul, zero_add, add_zero, Function.update_self, Function.update_idem,
    Function.update_of_ne h, hub0, hua1, XMeasCircuit.bitSign, hcomm, smul_add, smul_smul]
  rw [add_add_add_comm, ← add_smul, ← add_smul]
  refine congrArg₂ (· + ·) (congrArg (· • _) ?_) (congrArg (· • _) ?_)
  · rw [omega8Cn_eq]; ring_nf; simp only [sqrtHalf_pow3, Complex.I_sq]; ring
  · rw [omega8Cn_eq]; ring_nf; simp only [sqrtHalf_pow3, Complex.I_sq, i_pow3]; ring

/-- Register layout for the `4 * (2 ^ K - 1)` `T`, `0-TOFF` `(K + 1) → 2 ^ (K + 1)`
one-hot encoder and MBU decoder (`2` blocks of size `2 ^ K` with `0-T` affine root split). -/
structure StepPow2Layout (K n : ℕ) where
  rCtx : QRegister (K + 1) n
  rHot : QRegister (2 ^ (K + 1)) n
  qEnc : Wire n
  hCtxHot : rCtx.DisjointWires rHot
  hCtxEnc : ∀ i : Fin (K + 1), rCtx i ≠ qEnc
  hHotEnc : ∀ g : Fin (2 ^ (K + 1)), rHot g ≠ qEnc

theorem leaf2_idx_lt {K : ℕ} (b : Fin 2) (p : Fin (2 ^ K)) :
    2 ^ K * b.val + p.val < 2 ^ (K + 1) := by
  have hp := p.isLt
  have hb01 : b.val = 0 ∨ b.val = 1 := by have := b.isLt; omega
  rcases hb01 with hb | hb <;> (rw [hb, Nat.pow_succ]; omega)

/-- Leaf wire `(b, p) ∈ Fin 2 × Fin (2 ^ K)` inside `L.rHot` (`2 ^ K * b + p < 2 ^ (K + 1)`). -/
abbrev wLeaf2 {K n : ℕ} (L : StepPow2Layout K n) (b : Fin 2) (p : Fin (2 ^ K)) : Wire n :=
  L.rHot ⟨2 ^ K * b.val + p.val, leaf2_idx_lt b p⟩

theorem wLeaf2_inj {K n : ℕ} (L : StepPow2Layout K n) {b₁ b₂ : Fin 2} {p₁ p₂ : Fin (2 ^ K)}
    (h : wLeaf2 L b₁ p₁ = wLeaf2 L b₂ p₂) : b₁ = b₂ ∧ p₁ = p₂ := by
  have hv := congrArg Fin.val (L.rHot.wires.injective h)
  dsimp only at hv
  have hp1 := p₁.isLt; have hp2 := p₂.isLt
  have hb1_01 : b₁.val = 0 ∨ b₁.val = 1 := by have := b₁.isLt; omega
  have hb2_01 : b₂.val = 0 ∨ b₂.val = 1 := by have := b₂.isLt; omega
  rcases hb1_01 with hb1 | hb1 <;>
    rcases hb2_01 with hb2 | hb2 <;>
    (rw [hb1, hb2] at hv; simp only [Nat.mul_zero, Nat.mul_one, zero_add] at hv;
      exact ⟨Fin.ext (by omega), Fin.ext (by omega)⟩)

theorem wLeaf2_ne_ctx {K n : ℕ} (L : StepPow2Layout K n) (b : Fin 2) (p : Fin (2 ^ K))
    (i : Fin (K + 1)) : wLeaf2 L b p ≠ L.rCtx i :=
  (QRegister.disjoint_iff.mp L.hCtxHot i _).symm

theorem wLeaf2_ne_qEnc {K n : ℕ} (L : StepPow2Layout K n) (b : Fin 2) (p : Fin (2 ^ K)) :
    wLeaf2 L b p ≠ L.qEnc :=
  L.hHotEnc _

/-- `3`-gate (`0-T`, `0-TOFF`) affine root split from `u_K = L.rCtx K` into `(w[0,0], w[1,0])`. -/
def wRoot2LinCirc {K n : ℕ} (L : StepPow2Layout K n) : Circuit n :=
  let uTop := L.rCtx ⟨K, Nat.lt_succ_self K⟩
  let z0 : Fin (2 ^ K) := ⟨0, Nat.two_pow_pos K⟩
  let w0 := wLeaf2 L 0 z0
  let w1 := wLeaf2 L 1 z0
  Circuit.CNOT uTop w1 (wLeaf2_ne_ctx L 1 z0 _).symm ;;ᶜ
  Circuit.X w0 ;;ᶜ
  Circuit.CNOT uTop w0 (wLeaf2_ne_ctx L 0 z0 _).symm

/-- Exact `3`-gate (`0-T`, `0-TOFF`) reverse of `wRoot2LinCirc`. -/
def wRoot2UninitLinCirc {K n : ℕ} (L : StepPow2Layout K n) : Circuit n :=
  let uTop := L.rCtx ⟨K, Nat.lt_succ_self K⟩
  let z0 : Fin (2 ^ K) := ⟨0, Nat.two_pow_pos K⟩
  let w0 := wLeaf2 L 0 z0
  let w1 := wLeaf2 L 1 z0
  Circuit.CNOT uTop w0 (wLeaf2_ne_ctx L 0 z0 _).symm ;;ᶜ
  Circuit.X w0 ;;ᶜ
  Circuit.CNOT uTop w1 (wLeaf2_ne_ctx L 1 z0 _).symm

@[simp] theorem count_wRoot2LinCirc_toff {K n : ℕ} (L : StepPow2Layout K n) :
    (wRoot2LinCirc L).count .TOFF = 0 := by simp [wRoot2LinCirc]

@[simp] theorem count_wRoot2LinCirc_t {K n : ℕ} (L : StepPow2Layout K n) :
    (wRoot2LinCirc L).count .T = 0 := by simp [wRoot2LinCirc]

@[simp] theorem count_wRoot2UninitLinCirc_toff {K n : ℕ} (L : StepPow2Layout K n) :
    (wRoot2UninitLinCirc L).count .TOFF = 0 := by simp [wRoot2UninitLinCirc]

@[simp] theorem count_wRoot2UninitLinCirc_t {K n : ℕ} (L : StepPow2Layout K n) :
    (wRoot2UninitLinCirc L).count .T = 0 := by simp [wRoot2UninitLinCirc]

theorem two_mul_two_pow_le {K : ℕ} (r : Fin K) : 2 * 2 ^ r.val ≤ 2 ^ K := by
  have hr : r.val + 1 ≤ K := r.isLt
  calc 2 * 2 ^ r.val = 2 ^ (r.val + 1) := by ring
    _ ≤ 2 ^ K := Nat.pow_le_pow_right (by omega) hr

/-- `m`-split prefix of block `b < 2` at binary tree level `r < K` (`m ≤ 2 ^ r`). -/
def wSplitBlockFrom2 {K n : ℕ} (L : StepPow2Layout K n) (r : Fin K) (b : Fin 2) :
    (m : ℕ) → m ≤ 2 ^ r.val → Circuit n
  | 0, _ => Circuit.identity
  | m + 1, hm =>
      have hr : 2 * 2 ^ r.val ≤ 2 ^ K := two_mul_two_pow_le r
      have hne : wLeaf2 L b ⟨m, by omega⟩ ≠ wLeaf2 L b ⟨m + 2 ^ r.val, by omega⟩ :=
        fun h ↦ by
          have hv := congrArg Fin.val (wLeaf2_inj L h).2
          have hp := Nat.two_pow_pos r.val
          dsimp at hv; omega
      wSplitBlockFrom2 L r b m (by omega) ;;ᶜ
        wSplitPair4 (wLeaf2 L b ⟨m, by omega⟩) (wLeaf2 L b ⟨m + 2 ^ r.val, by omega⟩) hne

/-- `B`-block prefix at binary tree level `r < K` (`B ≤ 2`). -/
def wSplitLevelBlocks2 {K n : ℕ} (L : StepPow2Layout K n) (r : Fin K) :
    (B : ℕ) → B ≤ 2 → Circuit n
  | 0, _ => Circuit.identity
  | B + 1, hB =>
      wSplitLevelBlocks2 L r B (by omega) ;;ᶜ
        wSplitBlockFrom2 L r ⟨B, hB⟩ (2 ^ r.val) le_rfl

/-- `R`-level `2 × 2 ^ K` `W`-state tree prefix (`R ≤ K`, `4 * (2 ^ K - 1)` `T` at `R = K`). -/
def wTreePrefixLevels2 {K n : ℕ} (L : StepPow2Layout K n) :
    (R : ℕ) → R ≤ K → Circuit n
  | 0, _ => Circuit.identity
  | R + 1, hR =>
      wTreePrefixLevels2 L R (by omega) ;;ᶜ wSplitLevelBlocks2 L ⟨R, hR⟩ 2 le_rfl

private theorem count_wSplitBlockFrom2_toff {K n : ℕ} (L : StepPow2Layout K n) (r : Fin K)
    (b : Fin 2) : ∀ (m : ℕ) (hm : m ≤ 2 ^ r.val), (wSplitBlockFrom2 L r b m hm).count .TOFF = 0 :=
  by
  intro m hm; induction m with
  | zero => rfl
  | succ m ih => simp [wSplitBlockFrom2, ih (by omega)]

private theorem count_wSplitBlockFrom2_t {K n : ℕ} (L : StepPow2Layout K n) (r : Fin K)
    (b : Fin 2) : ∀ (m : ℕ) (hm : m ≤ 2 ^ r.val), (wSplitBlockFrom2 L r b m hm).count .T = 2 * m :=
  by
  intro m hm; induction m with
  | zero => rfl
  | succ m ih => simp [wSplitBlockFrom2, ih (by omega)]; omega

private theorem count_wSplitLevelBlocks2_toff {K n : ℕ} (L : StepPow2Layout K n) (r : Fin K) :
    ∀ (B : ℕ) (hB : B ≤ 2), (wSplitLevelBlocks2 L r B hB).count .TOFF = 0 := by
  intro B hB; induction B with
  | zero => rfl
  | succ B ih => simp [wSplitLevelBlocks2, ih (by omega), count_wSplitBlockFrom2_toff]

private theorem count_wSplitLevelBlocks2_t {K n : ℕ} (L : StepPow2Layout K n) (r : Fin K) :
    ∀ (B : ℕ) (hB : B ≤ 2), (wSplitLevelBlocks2 L r B hB).count .T = B * (2 * 2 ^ r.val) := by
  intro B hB; induction B with
  | zero => simp [wSplitLevelBlocks2]
  | succ B ih => simp [wSplitLevelBlocks2, ih (by omega), count_wSplitBlockFrom2_t]; ring

private theorem count_wTreePrefixLevels2_toff {K n : ℕ} (L : StepPow2Layout K n) :
    ∀ (R : ℕ) (hR : R ≤ K), (wTreePrefixLevels2 L R hR).count .TOFF = 0 := by
  intro R hR; induction R with
  | zero => rfl
  | succ R ih => simp [wTreePrefixLevels2, ih (by omega), count_wSplitLevelBlocks2_toff]

private theorem count_wTreePrefixLevels2_t {K n : ℕ} (L : StepPow2Layout K n) :
    ∀ (R : ℕ) (hR : R ≤ K), (wTreePrefixLevels2 L R hR).count .T = 4 * (2 ^ R - 1) := by
  intro R hR; induction R with
  | zero => rfl
  | succ R ih =>
      have hp : 1 ≤ 2 ^ R := Nat.two_pow_pos R
      have h2 : 2 ^ (R + 1) = 2 ^ R + 2 ^ R := by ring
      simp only [wTreePrefixLevels2, Circuit.count_seq, ih (by omega),
        count_wSplitLevelBlocks2_t]
      omega

theorem insertBitBound2 {K : ℕ} (d : Fin K) (s : Fin (2 ^ (K - 1))) :
    s.val % 2 ^ d.val + 2 ^ (d.val + 1) * (s.val / 2 ^ d.val) + 2 ^ d.val < 2 ^ K := by
  have hd : d.val ≤ K - 1 := Nat.le_sub_one_of_lt d.isLt
  have hpow : 2 ^ (K - 1) = 2 ^ d.val * 2 ^ (K - 1 - d.val) := by
    rw [← Nat.pow_add, Nat.add_sub_of_le hd]
  have hdiv : s.val / 2 ^ d.val < 2 ^ (K - 1 - d.val) := by
    have hmul : 2 ^ d.val * (s.val / 2 ^ d.val) ≤ s.val := Nat.mul_div_le s.val (2 ^ d.val)
    have hlt : 2 ^ d.val * (s.val / 2 ^ d.val) < 2 ^ d.val * 2 ^ (K - 1 - d.val) :=
      Nat.lt_of_le_of_lt hmul (hpow ▸ s.isLt)
    exact (Nat.mul_lt_mul_left (Nat.two_pow_pos d.val)).mp hlt
  have hmod : s.val % 2 ^ d.val < 2 ^ d.val := Nat.mod_lt _ (Nat.two_pow_pos d.val)
  have hstep : 2 ^ (d.val + 1) * (s.val / 2 ^ d.val + 1) ≤ 2 ^ K := by
    have h1 : (d.val + 1) + (K - 1 - d.val) = K := by omega
    calc 2 ^ (d.val + 1) * (s.val / 2 ^ d.val + 1)
        ≤ 2 ^ (d.val + 1) * 2 ^ (K - 1 - d.val) := Nat.mul_le_mul_left _ hdiv
      _ = 2 ^ K := by rw [← Nat.pow_add, h1]
  rw [Nat.mul_succ] at hstep
  have hd1 : 2 ^ (d.val + 1) = 2 ^ d.val + 2 ^ d.val := by ring
  omega

/-- Insert a `0` bit at position `d < K` into `s < 2 ^ (K - 1)`. -/
def insertZeroBit2 (K : ℕ) (d : Fin K) (s : Fin (2 ^ (K - 1))) : Fin (2 ^ K) :=
  ⟨s.val % 2 ^ d.val + 2 ^ (d.val + 1) * (s.val / 2 ^ d.val),
    Nat.lt_of_le_of_lt (Nat.le_add_right _ _) (insertBitBound2 d s)⟩

/-- Set bit `d < K` to `1` on `insertZeroBit2 K d s`. -/
def insertOneBit2 (K : ℕ) (d : Fin K) (s : Fin (2 ^ (K - 1))) : Fin (2 ^ K) :=
  ⟨(insertZeroBit2 K d s).val + 2 ^ d.val, insertBitBound2 d s⟩

/-- Odd-bit-`d` parity fan-in from `L.rHot` + `L.rCtx d` into `L.qEnc`. -/
def shiftParityCirc2 {K n : ℕ} (L : StepPow2Layout K n) (d : Fin K) : Circuit n :=
  CircuitModular.UnsignedGivens.cnotMaskReg (2 ^ (K + 1)) L.rHot L.qEnc
    (fun g ↦ decide ((g.val % 2 ^ K) / 2 ^ d.val % 2 = 1)) L.hHotEnc ;;ᶜ
  Circuit.CNOT (L.rCtx ⟨d.val, by omega⟩) L.qEnc (L.hCtxEnc ⟨d.val, by omega⟩)

/-- Bit-`d` barrel-swap circuit in block `b < 2` (`m ≤ 2 ^ (K - 1)` disjoint `SWAP`s, `0 T`). -/
def bswapBlockFrom2 {K n : ℕ} (L : StepPow2Layout K n) (d : Fin K) (b : Fin 2) :
    (m : ℕ) → m ≤ 2 ^ (K - 1) → Circuit n
  | 0, _ => Circuit.identity
  | m + 1, hm =>
      let s : Fin (2 ^ (K - 1)) := ⟨m, hm⟩
      have hne : wLeaf2 L b (insertZeroBit2 K d s) ≠ wLeaf2 L b (insertOneBit2 K d s) :=
        fun h ↦ by
          have hv := congrArg Fin.val (wLeaf2_inj L h).2
          have hd : 0 < 2 ^ d.val := Nat.two_pow_pos d.val
          dsimp [insertOneBit2] at hv; omega
      bswapBlockFrom2 L d b m (by omega) ;;ᶜ
        Circuit.SWAP (wLeaf2 L b (insertZeroBit2 K d s)) (wLeaf2 L b (insertOneBit2 K d s)) hne

/-- `B`-block barrel-swap circuit at bit `d < K` (`B ≤ 2`). -/
def bswapLevelBlocks2 {K n : ℕ} (L : StepPow2Layout K n) (d : Fin K) :
    (B : ℕ) → B ≤ 2 → Circuit n
  | 0, _ => Circuit.identity
  | B + 1, hB =>
      bswapLevelBlocks2 L d B (by omega) ;;ᶜ
        bswapBlockFrom2 L d ⟨B, hB⟩ (2 ^ (K - 1)) le_rfl

/-- `K`-stage `0-T`, `0-TOFF` `Z`-measurement barrel-shift dynamic circuit (`D ≤ K`). -/
def wShiftFromDyn2 {Var : Type} {K n : ℕ} (v : Var) (L : StepPow2Layout K n) :
    (D : ℕ) → D ≤ K → DynamicCircuit Var n
  | 0, _ => .circuit Circuit.identity
  | D + 1, hD =>
      let d : Fin K := ⟨K - (D + 1), by omega⟩
      .seq
        (.seq (.circuit (shiftParityCirc2 L d))
          (XMeasCircuit.remeasureIfDyn v L.qEnc
            (.circuit (Circuit.X L.qEnc ;;ᶜ bswapLevelBlocks2 L d 2 le_rfl))))
        (wShiftFromDyn2 v L D (by omega))

private theorem count_bswapBlockFrom2 {K n k : ℕ} (L : StepPow2Layout K n) (d : Fin K)
    (b : Fin 2) (g : PrimitiveGate k)
    (hSwap : ∀ (x y : Wire n) (h : x ≠ y), (Circuit.SWAP x y h).count g = 0) :
    ∀ (m : ℕ) (hm : m ≤ 2 ^ (K - 1)), (bswapBlockFrom2 L d b m hm).count g = 0 := by
  intro m hm; induction m with
  | zero => rfl
  | succ m ih => rw [bswapBlockFrom2, Circuit.count_seq, ih (by omega), hSwap, add_zero]

private theorem count_bswapLevelBlocks2 {K n k : ℕ} (L : StepPow2Layout K n) (d : Fin K)
    (g : PrimitiveGate k)
    (hSwap : ∀ (x y : Wire n) (h : x ≠ y), (Circuit.SWAP x y h).count g = 0) :
    ∀ (B : ℕ) (hB : B ≤ 2), (bswapLevelBlocks2 L d B hB).count g = 0 := by
  intro B hB; induction B with
  | zero => rfl
  | succ B ih =>
      rw [bswapLevelBlocks2, Circuit.count_seq, ih (by omega),
        count_bswapBlockFrom2 L d _ g hSwap _ le_rfl, add_zero]

@[simp] private theorem count_bswapLevelBlocks2_toff {K n : ℕ} (L : StepPow2Layout K n)
    (d : Fin K) : (bswapLevelBlocks2 L d 2 le_rfl).count .TOFF = 0 :=
  count_bswapLevelBlocks2 L d .TOFF (fun _ _ _ ↦ rfl) 2 le_rfl

@[simp] private theorem count_bswapLevelBlocks2_t {K n : ℕ} (L : StepPow2Layout K n) (d : Fin K) :
    (bswapLevelBlocks2 L d 2 le_rfl).count .T = 0 :=
  count_bswapLevelBlocks2 L d .T (fun _ _ _ ↦ rfl) 2 le_rfl

private theorem count_wShiftFromDyn2_toff {Var : Type} {K n : ℕ} (v : Var)
    (L : StepPow2Layout K n) :
    ∀ (D : ℕ) (hD : D ≤ K), (wShiftFromDyn2 v L D hD).count .TOFF = 0 := by
  intro D hD; induction D with
  | zero => rfl
  | succ D ih =>
      simp [wShiftFromDyn2, shiftParityCirc2, XMeasCircuit.remeasureIfDyn, DynamicCircuit.count,
        ih (by omega)]

private theorem count_wShiftFromDyn2_t {Var : Type} {K n : ℕ} (v : Var)
    (L : StepPow2Layout K n) :
    ∀ (D : ℕ) (hD : D ≤ K), (wShiftFromDyn2 v L D hD).count .T = 0 := by
  intro D hD; induction D with
  | zero => rfl
  | succ D ih =>
      simp [wShiftFromDyn2, shiftParityCirc2, XMeasCircuit.remeasureIfDyn, DynamicCircuit.count,
        ih (by omega)]

/-- Fold CNOTs `CNOT w[b, s + 2^d] w[b, s]` for `s < m` (`m ≤ 2^d`) in block `b < 2`. -/
def wFoldBlockFrom2 {K n : ℕ} (L : StepPow2Layout K n) (d : Fin K) (b : Fin 2) :
    (m : ℕ) → m ≤ 2 ^ d.val → Circuit n
  | 0, _ => Circuit.identity
  | m + 1, hm =>
      have hd : 2 * 2 ^ d.val ≤ 2 ^ K := two_mul_two_pow_le d
      have hne : wLeaf2 L b ⟨m + 2 ^ d.val, by omega⟩ ≠ wLeaf2 L b ⟨m, by omega⟩ :=
        fun h ↦ by
          have hv := congrArg Fin.val (wLeaf2_inj L h).2
          have hp := Nat.two_pow_pos d.val
          dsimp at hv; omega
      wFoldBlockFrom2 L d b m (by omega) ;;ᶜ
        Circuit.CNOT (wLeaf2 L b ⟨m + 2 ^ d.val, by omega⟩) (wLeaf2 L b ⟨m, by omega⟩) hne

/-- `B`-block fold CNOTs at level `d < K` (`B ≤ 2`). -/
def wFoldLevelBlocks2 {K n : ℕ} (L : StepPow2Layout K n) (d : Fin K) :
    (B : ℕ) → B ≤ 2 → Circuit n
  | 0, _ => Circuit.identity
  | B + 1, hB =>
      wFoldLevelBlocks2 L d B (by omega) ;;ᶜ wFoldBlockFrom2 L d ⟨B, hB⟩ (2 ^ d.val) le_rfl

/-- `0-T`, `0-TOFF` X-measurement unload of `w[b, s + 2^d]` (`s < m`) with `CZ(w[b, s], u_d)`. -/
def wUnloadBlockFrom2 {Var : Type} {K n : ℕ} (v : Var) (L : StepPow2Layout K n)
    (d : Fin K) (b : Fin 2) : (m : ℕ) → m ≤ 2 ^ d.val → DynamicCircuit Var n
  | 0, _ => .circuit Circuit.identity
  | m + 1, _ =>
      have hd : 2 * 2 ^ d.val ≤ 2 ^ K := two_mul_two_pow_le d
      .seq (wUnloadBlockFrom2 v L d b m (by omega))
        (XMeasCircuit.xMeasUnloadWireDyn v (wLeaf2 L b ⟨m + 2 ^ d.val, by omega⟩)
          (.circuit (SelectSwapQROM.czCircuit (wLeaf2 L b ⟨m, by omega⟩)
            (L.rCtx ⟨d.val, by omega⟩)
            (wLeaf2_ne_ctx L b ⟨m, by omega⟩ ⟨d.val, by omega⟩))))

/-- `B`-block X-measurement unload at level `d < K` (`B ≤ 2`). -/
def wUnloadLevelBlocks2 {Var : Type} {K n : ℕ} (v : Var) (L : StepPow2Layout K n) (d : Fin K) :
    (B : ℕ) → B ≤ 2 → DynamicCircuit Var n
  | 0, _ => .circuit Circuit.identity
  | B + 1, hB =>
      .seq (wUnloadLevelBlocks2 v L d B (by omega))
        (wUnloadBlockFrom2 v L d ⟨B, hB⟩ (2 ^ d.val) le_rfl)

/-- `R`-level MBU tree decoder (`R ≤ K`, running `d = R - 1` down to `0`, `0 T`, `0 TOFF`). -/
def wUncompTreeLevels2 {Var : Type} {K n : ℕ} (v : Var) (L : StepPow2Layout K n) :
    (R : ℕ) → R ≤ K → DynamicCircuit Var n
  | 0, _ => .circuit Circuit.identity
  | R + 1, hR =>
      let d : Fin K := ⟨R, hR⟩
      .seq
        (.seq (.circuit (wFoldLevelBlocks2 L d 2 le_rfl))
          (wUnloadLevelBlocks2 v L d 2 le_rfl))
        (wUncompTreeLevels2 v L R (by omega))

private theorem count_wFoldBlockFrom2 {K n k : ℕ} (L : StepPow2Layout K n) (d : Fin K)
    (b : Fin 2) (g : PrimitiveGate k)
    (hCnot : ∀ (x y : Wire n) (h : x ≠ y), (Circuit.CNOT x y h).count g = 0) :
    ∀ (m : ℕ) (hm : m ≤ 2 ^ d.val), (wFoldBlockFrom2 L d b m hm).count g = 0 := by
  intro m hm; induction m with
  | zero => rfl
  | succ m ih => rw [wFoldBlockFrom2, Circuit.count_seq, ih (by omega), hCnot, add_zero]

private theorem count_wFoldLevelBlocks2 {K n k : ℕ} (L : StepPow2Layout K n) (d : Fin K)
    (g : PrimitiveGate k)
    (hCnot : ∀ (x y : Wire n) (h : x ≠ y), (Circuit.CNOT x y h).count g = 0) :
    ∀ (B : ℕ) (hB : B ≤ 2), (wFoldLevelBlocks2 L d B hB).count g = 0 := by
  intro B hB; induction B with
  | zero => rfl
  | succ B ih =>
      rw [wFoldLevelBlocks2, Circuit.count_seq, ih (by omega),
        count_wFoldBlockFrom2 L d _ g hCnot _ le_rfl, add_zero]

private theorem count_wUnloadBlockFrom2_toff {Var : Type} {K n : ℕ} (v : Var)
    (L : StepPow2Layout K n) (d : Fin K) (b : Fin 2) :
    ∀ (m : ℕ) (hm : m ≤ 2 ^ d.val), (wUnloadBlockFrom2 v L d b m hm).count .TOFF = 0 := by
  intro m hm; induction m with
  | zero => rfl
  | succ m ih =>
      have hcz : ∀ (x y : Wire n) (h : x ≠ y), (SelectSwapQROM.czCircuit x y h).count .TOFF = 0 :=
        fun _ _ _ ↦ rfl
      simp [wUnloadBlockFrom2, DynamicCircuit.count, XMeasCircuit.xMeasUnloadWireDyn, hcz,
        ih (by omega)]

private theorem count_wUnloadBlockFrom2_t {Var : Type} {K n : ℕ} (v : Var)
    (L : StepPow2Layout K n) (d : Fin K) (b : Fin 2) :
    ∀ (m : ℕ) (hm : m ≤ 2 ^ d.val), (wUnloadBlockFrom2 v L d b m hm).count .T = 0 := by
  intro m hm; induction m with
  | zero => rfl
  | succ m ih =>
      have hcz : ∀ (x y : Wire n) (h : x ≠ y), (SelectSwapQROM.czCircuit x y h).count .T = 0 :=
        fun _ _ _ ↦ rfl
      simp [wUnloadBlockFrom2, DynamicCircuit.count, XMeasCircuit.xMeasUnloadWireDyn, hcz,
        ih (by omega)]

private theorem count_wUnloadLevelBlocks2_toff {Var : Type} {K n : ℕ} (v : Var)
    (L : StepPow2Layout K n) (d : Fin K) :
    ∀ (B : ℕ) (hB : B ≤ 2), (wUnloadLevelBlocks2 v L d B hB).count .TOFF = 0 := by
  intro B hB; induction B with
  | zero => rfl
  | succ B ih =>
      simp [wUnloadLevelBlocks2, DynamicCircuit.count, ih (by omega),
        count_wUnloadBlockFrom2_toff]

private theorem count_wUnloadLevelBlocks2_t {Var : Type} {K n : ℕ} (v : Var)
    (L : StepPow2Layout K n) (d : Fin K) :
    ∀ (B : ℕ) (hB : B ≤ 2), (wUnloadLevelBlocks2 v L d B hB).count .T = 0 := by
  intro B hB; induction B with
  | zero => rfl
  | succ B ih =>
      simp [wUnloadLevelBlocks2, DynamicCircuit.count, ih (by omega), count_wUnloadBlockFrom2_t]

private theorem count_wUncompTreeLevels2_toff {Var : Type} {K n : ℕ} (v : Var)
    (L : StepPow2Layout K n) :
    ∀ (R : ℕ) (hR : R ≤ K), (wUncompTreeLevels2 v L R hR).count .TOFF = 0 := by
  intro R hR; induction R with
  | zero => rfl
  | succ R ih =>
      have hf : (wFoldLevelBlocks2 L ⟨R, hR⟩ 2 le_rfl).count .TOFF = 0 :=
        count_wFoldLevelBlocks2 L _ .TOFF (fun _ _ _ ↦ rfl) 2 le_rfl
      simp [wUncompTreeLevels2, DynamicCircuit.count, hf, count_wUnloadLevelBlocks2_toff,
        ih (by omega)]

private theorem count_wUncompTreeLevels2_t {Var : Type} {K n : ℕ} (v : Var)
    (L : StepPow2Layout K n) :
    ∀ (R : ℕ) (hR : R ≤ K), (wUncompTreeLevels2 v L R hR).count .T = 0 := by
  intro R hR; induction R with
  | zero => rfl
  | succ R ih =>
      have hf : (wFoldLevelBlocks2 L ⟨R, hR⟩ 2 le_rfl).count .T = 0 :=
        count_wFoldLevelBlocks2 L _ .T (fun _ _ _ ↦ rfl) 2 le_rfl
      simp [wUncompTreeLevels2, DynamicCircuit.count, hf, count_wUnloadLevelBlocks2_t,
        ih (by omega)]

/-- `4 * (2 ^ K - 1)` `T`, `0-TOFF` `(K + 1) → 2 ^ (K + 1)` one-hot encoder. -/
def stepOneHotEncPow2Dyn {Var : Type} {K n : ℕ} (v : Var) (L : StepPow2Layout K n) :
    DynamicCircuit Var n :=
  .seq (.circuit (wRoot2LinCirc L ;;ᶜ wTreePrefixLevels2 L K le_rfl))
    (wShiftFromDyn2 v L K le_rfl)

/-- `0-T`, `0-TOFF` MBU `2 ^ (K + 1) → (K + 1)` one-hot decoder. -/
def stepOneHotDecPow2Dyn {Var : Type} {K n : ℕ} (v : Var) (L : StepPow2Layout K n) :
    DynamicCircuit Var n :=
  .seq (wUncompTreeLevels2 v L K le_rfl) (.circuit (wRoot2UninitLinCirc L))

/-- `4 * (2 ^ K - 1) + mid.count .T` `T`, `mid.count .TOFF` `TOFF` one-hot wrapper. -/
def withStepOneHotPow2Dyn {Var : Type} {K n : ℕ} (v : Var) (L : StepPow2Layout K n)
    (mid : DynamicCircuit Var n) : DynamicCircuit Var n :=
  .seq (stepOneHotEncPow2Dyn v L) (.seq mid (stepOneHotDecPow2Dyn v L))

@[simp] theorem count_stepOneHotEncPow2Dyn_toff {Var : Type} {K n : ℕ} (v : Var)
    (L : StepPow2Layout K n) : (stepOneHotEncPow2Dyn v L).count .TOFF = 0 := by
  simp [stepOneHotEncPow2Dyn, DynamicCircuit.count, count_wTreePrefixLevels2_toff,
    count_wShiftFromDyn2_toff]

@[simp] theorem count_stepOneHotEncPow2Dyn_t {Var : Type} {K n : ℕ} (v : Var)
    (L : StepPow2Layout K n) :
    (stepOneHotEncPow2Dyn v L).count .T = 4 * (2 ^ K - 1) := by
  simp [stepOneHotEncPow2Dyn, DynamicCircuit.count, count_wTreePrefixLevels2_t,
    count_wShiftFromDyn2_t]

@[simp] theorem count_stepOneHotDecPow2Dyn_toff {Var : Type} {K n : ℕ} (v : Var)
    (L : StepPow2Layout K n) : (stepOneHotDecPow2Dyn v L).count .TOFF = 0 := by
  simp [stepOneHotDecPow2Dyn, DynamicCircuit.count, count_wUncompTreeLevels2_toff]

@[simp] theorem count_stepOneHotDecPow2Dyn_t {Var : Type} {K n : ℕ} (v : Var)
    (L : StepPow2Layout K n) : (stepOneHotDecPow2Dyn v L).count .T = 0 := by
  simp [stepOneHotDecPow2Dyn, DynamicCircuit.count, count_wUncompTreeLevels2_t]

@[simp] theorem count_withStepOneHotPow2Dyn_toff {Var : Type} {K n : ℕ} (v : Var)
    (L : StepPow2Layout K n) (mid : DynamicCircuit Var n) :
    (withStepOneHotPow2Dyn v L mid).count .TOFF = mid.count .TOFF := by
  simp [withStepOneHotPow2Dyn, DynamicCircuit.count]

@[simp] theorem count_withStepOneHotPow2Dyn_t {Var : Type} {K n : ℕ} (v : Var)
    (L : StepPow2Layout K n) (mid : DynamicCircuit Var n) :
    (withStepOneHotPow2Dyn v L mid).count .T = 4 * (2 ^ K - 1) + mid.count .T := by
  simp [withStepOneHotPow2Dyn, DynamicCircuit.count]
private theorem k15_cases {K : ℕ} (h1 : 1 ≤ K) (h5 : K ≤ 5) :
    K = 1 ∨ K = 2 ∨ K = 3 ∨ K = 4 ∨ K = 5 := by omega

private theorem mod_two_pow_lt_powK {K : ℕ} (x r : ℕ) (hr : r ≤ K) : x % 2 ^ r < 2 ^ K :=
  Nat.lt_of_lt_of_le (Nat.mod_lt x (Nat.two_pow_pos r)) (Nat.pow_le_pow_right (by omega) hr)

private theorem ite_pos2 {c : Prop} [Decidable c] (hc : c) {α : Sort*} {t e : α} :
    ite c t e = t := by simp [hc]

private theorem ite_neg2 {c : Prop} [Decidable c] (hnc : ¬ c) {α : Sort*} {t e : α} :
    ite c t e = e := by simp [hnc]

private theorem czCircuit_eval_eq_phaseFlip2 {n : ℕ} (w₁ w₂ : Wire n) (h : w₁ ≠ w₂) :
    (SelectSwapQROM.czCircuit w₁ w₂ h).eval =
      XMeasCircuit.phaseFlipUnitary (fun β ↦ β w₁ * β w₂) := by
  apply Subtype.ext; refine SelectSwapQROM.matrix_ext_ket fun β ↦ ?_
  have hket : SelectSwapQROM.ket β = XMeasCircuit.ket β := rfl
  have hbs : SelectSwapQROM.bitSign (β w₁ * β w₂) = XMeasCircuit.bitSign (β w₁ * β w₂) := by
    generalize β w₁ * β w₂ = x; fin_cases x <;> rfl
  rw [SelectSwapQROM.ket_czCircuit w₁ w₂ h β, hket, hbs,
    ← XMeasCircuit.phaseFlipUnitary_mulVec_ket (fun β ↦ β w₁ * β w₂) β]

private theorem cnot_eval_mul_self2 {n : ℕ} (c t : Wire n) (h : c ≠ t) :
    (Circuit.CNOT c t h).eval * (Circuit.CNOT c t h).eval = 1 := by
  apply Subtype.ext; refine XMeasCircuit.matrix_ext_ket fun β ↦ ?_
  rw [Submonoid.coe_mul, ← Matrix.mulVec_mulVec, ket_CNOT2, ket_CNOT2, Submonoid.coe_one,
    Matrix.one_mulVec]
  congr 1; funext w
  by_cases hw : w = t
  · subst hw; simp [Function.update_of_ne h, add_assoc, CharTwo.add_self_eq_zero]
  · simp [Function.update_of_ne hw]

private theorem x_eval_mul_self2 {n : ℕ} (q : Wire n) :
    (Circuit.X q).eval * (Circuit.X q).eval = 1 := by
  apply Subtype.ext; refine XMeasCircuit.matrix_ext_ket fun β ↦ ?_
  rw [Submonoid.coe_mul, ← Matrix.mulVec_mulVec, XMeasCircuit.ket_X, XMeasCircuit.ket_X,
    Submonoid.coe_one, Matrix.one_mulVec]
  congr 1; funext w
  by_cases hw : w = q
  · subst hw; simp [add_assoc, CharTwo.add_self_eq_zero]
  · simp [Function.update_of_ne hw]

private theorem wRoot2Uninit_mul_wRoot2Lin {K n : ℕ} (L : StepPow2Layout K n) :
    (wRoot2UninitLinCirc L).eval * (wRoot2LinCirc L).eval = 1 := by
  have hc {c t : Wire n} (h : c ≠ t) (y : Unitary (2 ^ n)) :
      (Circuit.CNOT c t h).eval * ((Circuit.CNOT c t h).eval * y) = y := by
    rw [← mul_assoc, cnot_eval_mul_self2, one_mul]
  have hx (q : Wire n) (y : Unitary (2 ^ n)) :
      (Circuit.X q).eval * ((Circuit.X q).eval * y) = y := by
    rw [← mul_assoc, x_eval_mul_self2, one_mul]
  dsimp only [wRoot2UninitLinCirc, wRoot2LinCirc]
  simp only [Circuit.eval_seq, mul_assoc, hc, hx, cnot_eval_mul_self2]

/-- Entry clean-wire predicate for `StepPow2Layout K n`: `L.rHot` and `L.qEnc` are `|0⟩`. -/
private def sEncValid2 {K n : ℕ} (L : StepPow2Layout K n) (β : BitAssignment n) : Prop :=
  (∀ g : Fin (2 ^ (K + 1)), β (L.rHot g) = 0) ∧ β L.qEnc = 0

/-- Top address bit `u_K ∈ Fin 2` selecting block `0` or `1` of `L.rHot`. -/
private noncomputable def bZeroOf2 {K n : ℕ} (L : StepPow2Layout K n) (β : BitAssignment n) :
    Fin 2 :=
  ⟨(CircuitModular.UnsignedGivens.localIdx L.rCtx β).val / 2 ^ K, by
    have hlt : (CircuitModular.UnsignedGivens.localIdx L.rCtx β).val < 2 ^ K * 2 :=
      (CircuitModular.UnsignedGivens.localIdx L.rCtx β).isLt.trans_eq (Nat.pow_succ 2 K)
    have hle := Nat.mul_div_le (CircuitModular.UnsignedGivens.localIdx L.rCtx β).val (2 ^ K)
    by_contra hge
    have h2 : 2 ^ K * 2 ≤ 2 ^ K * ((CircuitModular.UnsignedGivens.localIdx L.rCtx β).val / 2 ^ K) :=
      Nat.mul_le_mul_left _ (by omega)
    omega⟩

/-- Lower `K`-bit offset `lo ∈ Fin (2 ^ K)` inside block `bZeroOf2 L β`. -/
private noncomputable def loOf2 {K n : ℕ} (L : StepPow2Layout K n) (β : BitAssignment n) :
    Fin (2 ^ K) :=
  ⟨(CircuitModular.UnsignedGivens.localIdx L.rCtx β).val % 2 ^ K, Nat.mod_lt _ (Nat.two_pow_pos K)⟩

/-- One-hot encoded bit assignment setting `wLeaf2 L (bZeroOf2 L β) (loOf2 L β)` to `1`. -/
private noncomputable def encAssign2 {K n : ℕ} (L : StepPow2Layout K n)
    (β : BitAssignment n) : BitAssignment n :=
  Function.update β (wLeaf2 L (bZeroOf2 L β) (loOf2 L β)) 1

private theorem wLeaf2_bZero_lo {K n : ℕ} (L : StepPow2Layout K n) (β : BitAssignment n) :
    wLeaf2 L (bZeroOf2 L β) (loOf2 L β) = L.rHot (CircuitModular.UnsignedGivens.localIdx L.rCtx
      β) :=
  congrArg L.rHot (Fin.ext (by dsimp [bZeroOf2, loOf2]; exact Nat.div_add_mod _ _))

private theorem basisBits_pow2_eq_div_mod {K : ℕ} (hK1 : 1 ≤ K) (hK5 : K ≤ 5) :
    ∀ (x : Fin (2 ^ (K + 1))) (i : Fin (K + 1)),
      basisBits (K + 1) x i = if x.val / 2 ^ i.val % 2 = 1 then 1 else 0 := by
  rcases k15_cases hK1 hK5 with rfl | rfl | rfl | rfl | rfl <;> decide

private theorem ctx_bit_eq2 {K n : ℕ} (hK1 : 1 ≤ K) (hK5 : K ≤ 5) (L : StepPow2Layout K n)
    (β : BitAssignment n) (i : Fin (K + 1)) :
    β (L.rCtx i) =
      if (CircuitModular.UnsignedGivens.localIdx L.rCtx β).val / 2 ^ i.val % 2 =
        1 then 1 else 0 := by
  have hb : basisBits (K + 1) (CircuitModular.UnsignedGivens.localIdx L.rCtx β) i = β (L.rCtx i) :=
    congrFun (CircuitModular.UnsignedGivens.basisBits_symm_eq (fun k ↦ β (L.rCtx k))) i
  rw [← hb, basisBits_pow2_eq_div_mod hK1 hK5]

private theorem ctx_low_bit2 {K : ℕ} (hK1 : 1 ≤ K) (hK5 : K ≤ 5) :
    ∀ (x : Fin (2 ^ (K + 1))) (d : Fin K),
      x.val / 2 ^ d.val % 2 = (x.val % 2 ^ K) / 2 ^ d.val % 2 := by
  rcases k15_cases hK1 hK5 with rfl | rfl | rfl | rfl | rfl <;> decide

private theorem wRoot2LinCirc_ket {K n : ℕ} (hK1 : 1 ≤ K) (hK5 : K ≤ 5)
    (L : StepPow2Layout K n) {β : BitAssignment n} (hS : sEncValid2 L β) :
    (wRoot2LinCirc L).eval.1.mulVec (XMeasCircuit.ket β) =
      XMeasCircuit.ket (Function.update β (wLeaf2 L (bZeroOf2 L β) ⟨0, Nat.two_pow_pos K⟩) 1) := by
  have hw0 (b : Fin 2) : β (wLeaf2 L b ⟨0, Nat.two_pow_pos K⟩) = 0 := hS.1 _
  have hneLeaf {a b : Fin 2} (hab : a ≠ b) :
      wLeaf2 L a ⟨0, Nat.two_pow_pos K⟩ ≠ wLeaf2 L b ⟨0, Nat.two_pow_pos K⟩ :=
    fun h ↦ hab (wLeaf2_inj L h).1
  have hbTop : β (L.rCtx ⟨K, Nat.lt_succ_self K⟩) =
      if (bZeroOf2 L β).val = 1 then 1 else 0 := by
    rw [ctx_bit_eq2 hK1 hK5 L β ⟨K, Nat.lt_succ_self K⟩]
    have hbLt : (bZeroOf2 L β).val < 2 := (bZeroOf2 L β).isLt
    have hmod : (CircuitModular.UnsignedGivens.localIdx L.rCtx β).val / 2 ^ K % 2 =
        (bZeroOf2 L β).val := Nat.mod_eq_of_lt hbLt
    dsimp only; rw [hmod]
  have hupLeaf (γ : BitAssignment n) (a b : Fin 2) (v : ZMod 2) :
      Function.update γ (wLeaf2 L a ⟨0, Nat.two_pow_pos K⟩) v
          (wLeaf2 L b ⟨0, Nat.two_pow_pos K⟩) =
        if b = a then v else γ (wLeaf2 L b ⟨0, Nat.two_pow_pos K⟩) := by
    by_cases h : b = a
    · subst h; simp
    · rw [ite_eq_right h]; exact Function.update_of_ne (hneLeaf h) v γ
  have hupCtx (γ : BitAssignment n) (a : Fin 2) (v : ZMod 2) (i : Fin (K + 1)) :
      Function.update γ (wLeaf2 L a ⟨0, Nat.two_pow_pos K⟩) v (L.rCtx i) = γ (L.rCtx i) :=
    Function.update_of_ne (wLeaf2_ne_ctx L a ⟨0, Nat.two_pow_pos K⟩ i).symm _ _
  dsimp only [wRoot2LinCirc]
  simp only [eval_seq_mulVec2, ket_CNOT2, XMeasCircuit.ket_X]
  congr 1; funext w
  by_cases hw : ∃ k : Fin 2, w = wLeaf2 L k ⟨0, Nat.two_pow_pos K⟩
  · obtain ⟨k, rfl⟩ := hw
    simp only [hupLeaf, hupCtx, hw0, hbTop]
    generalize bZeroOf2 L β = q2; revert k q2; decide
  · have hupNe (γ : BitAssignment n) (a : Fin 2) (v : ZMod 2) :
        Function.update γ (wLeaf2 L a ⟨0, Nat.two_pow_pos K⟩) v w = γ w :=
      Function.update_of_ne (fun h ↦ hw ⟨a, h⟩) v γ
    simp only [hupNe]

private theorem wRoot2UninitLinCirc_ket {K n : ℕ} (hK1 : 1 ≤ K) (hK5 : K ≤ 5)
    (L : StepPow2Layout K n) {β : BitAssignment n} (hS : sEncValid2 L β) :
    (wRoot2UninitLinCirc L).eval.1.mulVec
        (XMeasCircuit.ket
          (Function.update β (wLeaf2 L (bZeroOf2 L β) ⟨0, Nat.two_pow_pos K⟩) 1)) =
      XMeasCircuit.ket β := by
  have hm := congrArg Subtype.val (wRoot2Uninit_mul_wRoot2Lin L)
  rw [← wRoot2LinCirc_ket hK1 hK5 L hS, Matrix.mulVec_mulVec]
  simpa only [Submonoid.coe_mul, Submonoid.coe_one, Matrix.one_mulVec] using
    congrArg (fun M : Operator (2 ^ n) ↦ M.mulVec _) hm

/-- Uniform superposition state after `R` levels (`R ≤ K`) of `wTreePrefixLevels2`. -/
private noncomputable def wTreeVec2 {K n : ℕ} (L : StepPow2Layout K n) (R : ℕ) (hR : R ≤ K)
    (β : BitAssignment n) : Fin (2 ^ n) → ℂ :=
  have _ : 2 ^ R ≤ 2 ^ K := Nat.pow_le_pow_right (by omega) hR
  (XMeasCircuit.sqrtHalf ^ R) •
    ∑ t : Fin (2 ^ R),
      XMeasCircuit.ket (Function.update β (wLeaf2 L (bZeroOf2 L β) ⟨t.val, by omega⟩) 1)

private theorem wSplitBlockFrom2_ket_fix {K n : ℕ} (L : StepPow2Layout K n) (r : Fin K)
    (b b₀ : Fin 2) (p₀ : Fin (2 ^ K)) {β : BitAssignment n} (hS : sEncValid2 L β) :
    ∀ (m : ℕ) (hm : m ≤ 2 ^ r.val),
      (b ≠ b₀ ∨ ∀ k < m, k ≠ p₀.val ∧ k + 2 ^ r.val ≠ p₀.val) →
      (wSplitBlockFrom2 L r b m hm).eval.1.mulVec
          (XMeasCircuit.ket (Function.update β (wLeaf2 L b₀ p₀) 1)) =
        XMeasCircuit.ket (Function.update β (wLeaf2 L b₀ p₀) 1) := by
  intro m hm hdisj; induction m with
  | zero =>
      simp only [wSplitBlockFrom2, Circuit.eval_identity, Submonoid.coe_one, Matrix.one_mulVec]
  | succ m ih =>
      have hr : 2 * 2 ^ r.val ≤ 2 ^ K := two_mul_two_pow_le r
      have hprev := ih (by omega) (hdisj.imp id fun hk k hlt ↦ hk k (by omega))
      have hne1 : wLeaf2 L b ⟨m, by omega⟩ ≠ wLeaf2 L b₀ p₀ := fun heq ↦ by
        obtain ⟨rfl, hp⟩ := wLeaf2_inj L heq
        rcases hdisj with hb | hk
        · exact hb rfl
        · exact (hk m (by omega)).1 (congrArg Fin.val hp)
      have hne2 : wLeaf2 L b ⟨m + 2 ^ r.val, by omega⟩ ≠ wLeaf2 L b₀ p₀ := fun heq ↦ by
        obtain ⟨rfl, hp⟩ := wLeaf2_inj L heq
        rcases hdisj with hb | hk
        · exact hb rfl
        · exact (hk m (by omega)).2 (congrArg Fin.val hp)
      rw [wSplitBlockFrom2, eval_seq_mulVec2, hprev]
      exact wSplitPair4_mulVec_ket_00 _ _ _
        (by rw [Function.update_of_ne hne1]; exact hS.1 _)
        (by rw [Function.update_of_ne hne2]; exact hS.1 _)

private theorem wSplitBlockFrom2_ket_split {K n : ℕ} (L : StepPow2Layout K n) (r : Fin K)
    (b₀ : Fin 2) (t : Fin (2 ^ r.val)) {β : BitAssignment n} (hS : sEncValid2 L β) :
    have _ : 2 * 2 ^ r.val ≤ 2 ^ K := two_mul_two_pow_le r
    ∀ (m : ℕ) (hm : m ≤ 2 ^ r.val), t.val < m →
      (wSplitBlockFrom2 L r b₀ m hm).eval.1.mulVec
          (XMeasCircuit.ket (Function.update β (wLeaf2 L b₀ ⟨t.val, by omega⟩) 1)) =
        XMeasCircuit.sqrtHalf •
            XMeasCircuit.ket (Function.update β (wLeaf2 L b₀ ⟨t.val, by omega⟩) 1) +
          XMeasCircuit.sqrtHalf •
            XMeasCircuit.ket (Function.update β (wLeaf2 L b₀ ⟨t.val + 2 ^ r.val, by omega⟩) 1) := by
  intro hr m hm hlt; induction m with
  | zero => omega
  | succ m ih =>
      have _ := t.isLt
      have hpos := Nat.two_pow_pos r.val
      rw [wSplitBlockFrom2, eval_seq_mulVec2]
      by_cases hmt : m = t.val
      · have hfix := wSplitBlockFrom2_ket_fix L r b₀ b₀ ⟨t.val, by omega⟩ hS m (by omega)
          (Or.inr fun k hk ↦ ⟨by dsimp; omega, by dsimp; omega⟩)
        have hmEq : (⟨m, by omega⟩ : Fin (2 ^ K)) = ⟨t.val, by omega⟩ := Fin.ext hmt
        have hmEq2 : (⟨m + 2 ^ r.val, by omega⟩ : Fin (2 ^ K)) =
            ⟨t.val + 2 ^ r.val, by omega⟩ := Fin.ext (by dsimp; omega)
        have hne12 : wLeaf2 L b₀ ⟨m + 2 ^ r.val, by omega⟩ ≠ wLeaf2 L b₀ ⟨t.val, by omega⟩ :=
          fun h ↦ by have hv := congrArg Fin.val (wLeaf2_inj L h).2; dsimp at hv; omega
        rw [hfix, wSplitPair4_mulVec_ket_10 _ _ _ (by rw [hmEq, Function.update_self])
          (by rw [Function.update_of_ne hne12]; exact hS.1 _)]
        have hclr : Function.update (Function.update β (wLeaf2 L b₀ ⟨t.val, by omega⟩) 1)
            (wLeaf2 L b₀ ⟨m, by omega⟩) 0 = β := by
          rw [hmEq, Function.update_idem]
          exact Function.update_eq_self_iff.mpr (hS.1 _).symm
        rw [hclr, hmEq2]
      · have hprev := ih (by omega) (by omega)
        have hneA1 : wLeaf2 L b₀ ⟨m, by omega⟩ ≠ wLeaf2 L b₀ ⟨t.val, by omega⟩ :=
          fun h ↦ hmt (congrArg Fin.val (wLeaf2_inj L h).2)
        have hneA2 : wLeaf2 L b₀ ⟨m + 2 ^ r.val, by omega⟩ ≠ wLeaf2 L b₀ ⟨t.val, by omega⟩ :=
          fun h ↦ by have hv := congrArg Fin.val (wLeaf2_inj L h).2; dsimp at hv; omega
        have hneB1 : wLeaf2 L b₀ ⟨m, by omega⟩ ≠ wLeaf2 L b₀ ⟨t.val + 2 ^ r.val, by omega⟩ :=
          fun h ↦ by have hv := congrArg Fin.val (wLeaf2_inj L h).2; dsimp at hv; omega
        have hneB2 : wLeaf2 L b₀ ⟨m + 2 ^ r.val, by omega⟩ ≠
            wLeaf2 L b₀ ⟨t.val + 2 ^ r.val, by omega⟩ :=
          fun h ↦ by have hv := congrArg Fin.val (wLeaf2_inj L h).2; dsimp at hv; omega
        rw [hprev, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
          wSplitPair4_mulVec_ket_00 _ _ _
            (by rw [Function.update_of_ne hneA1]; exact hS.1 _)
            (by rw [Function.update_of_ne hneA2]; exact hS.1 _),
          wSplitPair4_mulVec_ket_00 _ _ _
            (by rw [Function.update_of_ne hneB1]; exact hS.1 _)
            (by rw [Function.update_of_ne hneB2]; exact hS.1 _)]

private theorem wSplitLevelBlocks2_ket {K n : ℕ} (L : StepPow2Layout K n) (r : Fin K)
    (t : Fin (2 ^ r.val)) {β : BitAssignment n} (hS : sEncValid2 L β) :
    have _ : 2 * 2 ^ r.val ≤ 2 ^ K := two_mul_two_pow_le r
    ∀ (B : ℕ) (hB : B ≤ 2),
      (wSplitLevelBlocks2 L r B hB).eval.1.mulVec
          (XMeasCircuit.ket (Function.update β (wLeaf2 L (bZeroOf2 L β) ⟨t.val, by omega⟩) 1)) =
        if (bZeroOf2 L β).val < B then
          XMeasCircuit.sqrtHalf •
              XMeasCircuit.ket (Function.update β (wLeaf2 L (bZeroOf2 L β) ⟨t.val, by omega⟩) 1) +
            XMeasCircuit.sqrtHalf •
              XMeasCircuit.ket
                (Function.update β (wLeaf2 L (bZeroOf2 L β) ⟨t.val + 2 ^ r.val, by omega⟩) 1)
        else XMeasCircuit.ket (Function.update β (wLeaf2 L (bZeroOf2 L β) ⟨t.val, by omega⟩) 1) :=
  by
  intro hr B hB; induction B with
  | zero =>
      simp only [wSplitLevelBlocks2, Circuit.eval_identity, Submonoid.coe_one, Matrix.one_mulVec,
        Nat.not_lt_zero, ↓reduceIte]
  | succ B ih =>
      rw [wSplitLevelBlocks2, eval_seq_mulVec2, ih (by omega)]
      by_cases hlt : (bZeroOf2 L β).val < B
      · have hlt' : (bZeroOf2 L β).val < B + 1 := by omega
        have hne : (⟨B, hB⟩ : Fin 2) ≠ bZeroOf2 L β := fun h ↦ by
          have hv := congrArg Fin.val h; dsimp at hv; omega
        simp only [hlt, hlt', ↓reduceIte, Matrix.mulVec_add, Matrix.mulVec_smul]
        rw [wSplitBlockFrom2_ket_fix L r _ _ _ hS _ _ (Or.inl hne),
          wSplitBlockFrom2_ket_fix L r _ _ _ hS _ _ (Or.inl hne)]
      · simp only [hlt, ↓reduceIte]
        by_cases heq : (bZeroOf2 L β).val = B
        · have hlt' : (bZeroOf2 L β).val < B + 1 := by omega
          have hbEq : (⟨B, hB⟩ : Fin 2) = bZeroOf2 L β := Fin.ext heq.symm
          simp only [hlt', ↓reduceIte, hbEq]
          exact wSplitBlockFrom2_ket_split L r (bZeroOf2 L β) t hS (2 ^ r.val) le_rfl t.isLt
        · have hnlt' : ¬ (bZeroOf2 L β).val < B + 1 := by omega
          have hne : (⟨B, hB⟩ : Fin 2) ≠ bZeroOf2 L β := fun h ↦ heq (congrArg Fin.val h).symm
          simp only [hnlt', ↓reduceIte]
          exact wSplitBlockFrom2_ket_fix L r _ _ _ hS _ _ (Or.inl hne)

private theorem sum_fin_two_pow_split {M : Type*} [AddCommMonoid M] (R : ℕ)
    (f : Fin (2 ^ (R + 1)) → M) :
    (∑ t : Fin (2 ^ (R + 1)), f t) =
      ∑ s : Fin (2 ^ R),
        (f ⟨s.val, by have := s.isLt; rw [Nat.pow_succ]; omega⟩ +
          f ⟨s.val + 2 ^ R, by have := s.isLt; rw [Nat.pow_succ]; omega⟩) := by
  have heq : 2 ^ (R + 1) = 2 ^ R + 2 ^ R := by ring
  rw [← Equiv.sum_comp (finCongr heq).symm, Fin.sum_univ_add, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s _ ↦ congrArg₂ (· + ·)
    (congrArg f (Fin.ext (by simp [finCongr])))
    (congrArg f (Fin.ext (by simp [finCongr])))

private theorem wTreePrefixLevels2_ket {K n : ℕ} (L : StepPow2Layout K n) {β : BitAssignment n}
    (hS : sEncValid2 L β) :
    let z0 : Fin (2 ^ K) := ⟨0, Nat.two_pow_pos K⟩
    ∀ (R : ℕ) (hR : R ≤ K),
      (wTreePrefixLevels2 L R hR).eval.1.mulVec
          (XMeasCircuit.ket (Function.update β (wLeaf2 L (bZeroOf2 L β) z0) 1)) =
        wTreeVec2 L R hR β := by
  intro z0 R hR; induction R with
  | zero =>
      dsimp only [wTreePrefixLevels2, wTreeVec2]
      rw [Circuit.eval_identity, Submonoid.coe_one, Matrix.one_mulVec, _root_.pow_zero, one_smul]
      change _ = ∑ t : Fin 1, _
      rw [Fin.sum_univ_one]; rfl
  | succ R ih =>
      rw [wTreePrefixLevels2, eval_seq_mulVec2, ih (by omega)]
      dsimp only [wTreeVec2]
      rw [Matrix.mulVec_smul, Matrix.mulVec_sum]
      have hpow1 : 2 * 2 ^ R ≤ 2 ^ K := two_mul_two_pow_le (⟨R, hR⟩ : Fin K)
      have hterm (t : Fin (2 ^ R)) :
          (wSplitLevelBlocks2 L ⟨R, hR⟩ 2 le_rfl).eval.1.mulVec
              (XMeasCircuit.ket (Function.update β (wLeaf2 L (bZeroOf2 L β)
                ⟨t.val, by have := t.isLt; omega⟩) 1)) =
            XMeasCircuit.sqrtHalf • (
              XMeasCircuit.ket (Function.update β (wLeaf2 L (bZeroOf2 L β)
                ⟨t.val, by have := t.isLt; omega⟩) 1) +
              XMeasCircuit.ket (Function.update β (wLeaf2 L (bZeroOf2 L β)
                ⟨t.val + 2 ^ R, by have := t.isLt; omega⟩) 1)) := by
        have hsp := wSplitLevelBlocks2_ket L ⟨R, hR⟩ t hS 2 le_rfl
        have hlt2 : (bZeroOf2 L β).val < 2 := (bZeroOf2 L β).isLt
        simpa only [hlt2, ↓reduceIte, smul_add] using hsp
      simp_rw [hterm]
      rw [← Finset.smul_sum, smul_smul, ← _root_.pow_succ]
      exact congrArg (_ • ·) (sum_fin_two_pow_split R (fun t : Fin (2 ^ (R + 1)) ↦
        XMeasCircuit.ket (Function.update β (wLeaf2 L (bZeroOf2 L β)
          ⟨t.val,
            lt_of_lt_of_le (t.isLt.trans_eq (by ring : 2 ^ (R + 1) = 2 * 2 ^ R)) hpow1⟩) 1))).symm

private theorem shrinkBit2_lt {K : ℕ} (d : Fin K) (p : Fin (2 ^ K)) :
    p.val % 2 ^ d.val + 2 ^ d.val * (p.val / 2 ^ (d.val + 1)) < 2 ^ (K - 1) := by
  have hd : d.val ≤ K - 1 := Nat.le_sub_one_of_lt d.isLt
  have h1 : (d.val + 1) + (K - 1 - d.val) = K := by omega
  have hpow : 2 ^ K = 2 ^ (d.val + 1) * 2 ^ (K - 1 - d.val) := by rw [← Nat.pow_add, h1]
  have hdiv : p.val / 2 ^ (d.val + 1) < 2 ^ (K - 1 - d.val) := by
    have hmul : 2 ^ (d.val + 1) * (p.val / 2 ^ (d.val + 1)) ≤ p.val :=
      Nat.mul_div_le p.val (2 ^ (d.val + 1))
    have hlt : 2 ^ (d.val + 1) * (p.val / 2 ^ (d.val + 1)) <
        2 ^ (d.val + 1) * 2 ^ (K - 1 - d.val) := Nat.lt_of_le_of_lt hmul (hpow ▸ p.isLt)
    exact (Nat.mul_lt_mul_left (Nat.two_pow_pos (d.val + 1))).mp hlt
  have hmod : p.val % 2 ^ d.val < 2 ^ d.val := Nat.mod_lt _ (Nat.two_pow_pos d.val)
  have hstep : 2 ^ d.val * (p.val / 2 ^ (d.val + 1) + 1) ≤ 2 ^ (K - 1) := by
    calc 2 ^ d.val * (p.val / 2 ^ (d.val + 1) + 1)
        ≤ 2 ^ d.val * 2 ^ (K - 1 - d.val) := Nat.mul_le_mul_left _ hdiv
      _ = 2 ^ (K - 1) := by rw [← Nat.pow_add, Nat.add_sub_of_le hd]
  rw [Nat.mul_succ] at hstep; omega

/-- Delete bit `d < K` from `p < 2 ^ K` to obtain an index `< 2 ^ (K - 1)`. -/
private def shrinkBit2 (K : ℕ) (d : Fin K) (p : Fin (2 ^ K)) : Fin (2 ^ (K - 1)) :=
  ⟨p.val % 2 ^ d.val + 2 ^ d.val * (p.val / 2 ^ (d.val + 1)), shrinkBit2_lt d p⟩

/-- Flip bit `d < K` of `p < 2 ^ K`. -/
private def flipLeafBit2 (K : ℕ) (d : Fin K) (p : Fin (2 ^ K)) : Fin (2 ^ K) :=
  if p.val / 2 ^ d.val % 2 = 0 then insertOneBit2 K d (shrinkBit2 K d p)
  else insertZeroBit2 K d (shrinkBit2 K d p)

private theorem shrinkBit2_insertZero {K : ℕ} (hK1 : 1 ≤ K) (hK5 : K ≤ 5) :
    ∀ (d : Fin K) (s : Fin (2 ^ (K - 1))),
      shrinkBit2 K d (insertZeroBit2 K d s) = s := by
  rcases k15_cases hK1 hK5 with rfl | rfl | rfl | rfl | rfl <;> decide

private theorem shrinkBit2_insertOne {K : ℕ} (hK1 : 1 ≤ K) (hK5 : K ≤ 5) :
    ∀ (d : Fin K) (s : Fin (2 ^ (K - 1))),
      shrinkBit2 K d (insertOneBit2 K d s) = s := by
  rcases k15_cases hK1 hK5 with rfl | rfl | rfl | rfl | rfl <;> decide

private theorem shrinkBit2_flipLeafBit {K : ℕ} (hK1 : 1 ≤ K) (hK5 : K ≤ 5) :
    ∀ (d : Fin K) (p : Fin (2 ^ K)),
      shrinkBit2 K d (flipLeafBit2 K d p) = shrinkBit2 K d p := by
  rcases k15_cases hK1 hK5 with rfl | rfl | rfl | rfl | rfl <;> decide

private theorem insert_shrinkBit2_cases {K : ℕ} (hK1 : 1 ≤ K) (hK5 : K ≤ 5) :
    ∀ (d : Fin K) (p : Fin (2 ^ K)),
      (insertZeroBit2 K d (shrinkBit2 K d p) = p ∧
        insertOneBit2 K d (shrinkBit2 K d p) = flipLeafBit2 K d p) ∨
      (insertOneBit2 K d (shrinkBit2 K d p) = p ∧
        insertZeroBit2 K d (shrinkBit2 K d p) = flipLeafBit2 K d p) := by
  rcases k15_cases hK1 hK5 with rfl | rfl | rfl | rfl | rfl <;> decide

private theorem insertZeroBit2_div_mod {K : ℕ} (hK1 : 1 ≤ K) (hK5 : K ≤ 5) :
    ∀ (d : Fin K) (s : Fin (2 ^ (K - 1))),
      (insertZeroBit2 K d s).val / 2 ^ d.val % 2 = 0 := by
  rcases k15_cases hK1 hK5 with rfl | rfl | rfl | rfl | rfl <;> decide

private theorem insertOneBit2_div_mod {K : ℕ} (hK1 : 1 ≤ K) (hK5 : K ≤ 5) :
    ∀ (d : Fin K) (s : Fin (2 ^ (K - 1))),
      (insertOneBit2 K d s).val / 2 ^ d.val % 2 = 1 := by
  rcases k15_cases hK1 hK5 with rfl | rfl | rfl | rfl | rfl <;> decide

private theorem flipLeafBit2_insertZero {K : ℕ} (hK1 : 1 ≤ K) (hK5 : K ≤ 5) :
    ∀ (d : Fin K) (s : Fin (2 ^ (K - 1))),
      flipLeafBit2 K d (insertZeroBit2 K d s) = insertOneBit2 K d s := by
  rcases k15_cases hK1 hK5 with rfl | rfl | rfl | rfl | rfl <;> decide

private theorem flipLeafBit2_insertOne {K : ℕ} (hK1 : 1 ≤ K) (hK5 : K ≤ 5) :
    ∀ (d : Fin K) (s : Fin (2 ^ (K - 1))),
      flipLeafBit2 K d (insertOneBit2 K d s) = insertZeroBit2 K d s := by
  rcases k15_cases hK1 hK5 with rfl | rfl | rfl | rfl | rfl <;> decide

private theorem insert_of_div_mod2 {K : ℕ} (hK1 : 1 ≤ K) (hK5 : K ≤ 5) :
    ∀ (d : Fin K) (p : Fin (2 ^ K)),
      (p.val / 2 ^ d.val % 2 = 0 → insertZeroBit2 K d (shrinkBit2 K d p) = p) ∧
      (p.val / 2 ^ d.val % 2 = 1 → insertOneBit2 K d (shrinkBit2 K d p) = p) := by
  rcases k15_cases hK1 hK5 with rfl | rfl | rfl | rfl | rfl <;> decide

private theorem mod_succ_pow_props2 {K : ℕ} (hK1 : 1 ≤ K) (hK5 : K ≤ 5) :
    ∀ (d : Fin K) (lo : Fin (2 ^ K)),
      (lo.val % 2 ^ (d.val + 1)) % 2 ^ d.val = lo.val % 2 ^ d.val ∧
      (lo.val % 2 ^ (d.val + 1)) / 2 ^ d.val % 2 = lo.val / 2 ^ d.val % 2 := by
  rcases k15_cases hK1 hK5 with rfl | rfl | rfl | rfl | rfl <;> decide

private theorem ket_SWAP {n : ℕ} (a b : Wire n) (hab : a ≠ b) (γ : BitAssignment n) :
    (Circuit.SWAP a b hab).eval.1.mulVec (XMeasCircuit.ket γ) =
      XMeasCircuit.ket (Function.update (Function.update γ a (γ b)) b (γ a)) :=
  CircuitModular.UnsignedGivens.evolve_SWAP_ket a b hab γ

private theorem swap_ket_zero_zero {n : ℕ} (a b : Wire n) (hab : a ≠ b) {γ : BitAssignment n}
    (ha : γ a = 0) (hb : γ b = 0) :
    (Circuit.SWAP a b hab).eval.1.mulVec (XMeasCircuit.ket γ) = XMeasCircuit.ket γ := by
  rw [ket_SWAP, ha, hb]
  congr 1; funext w
  by_cases hwb : w = b
  · subst hwb; simp [hb]
  · by_cases hwa : w = a
    · subst hwa; simp [Function.update_of_ne hwb, ha]
    · simp [Function.update_of_ne hwb, Function.update_of_ne hwa]

private theorem swap_ket_one_zero_update {n : ℕ} (a b : Wire n) (hab : a ≠ b)
    {β : BitAssignment n} (ha : β a = 0) (hb : β b = 0) :
    (Circuit.SWAP a b hab).eval.1.mulVec (XMeasCircuit.ket (Function.update β a 1)) =
      XMeasCircuit.ket (Function.update β b 1) ∧
    (Circuit.SWAP a b hab).eval.1.mulVec (XMeasCircuit.ket (Function.update β b 1)) =
      XMeasCircuit.ket (Function.update β a 1) := by
  constructor
  · rw [ket_SWAP]
    congr 1; funext w
    by_cases hwb : w = b
    · subst hwb; simp
    · by_cases hwa : w = a
      · subst hwa; simp [Function.update_of_ne hwb, Function.update_of_ne hab.symm, ha, hb]
      · simp [Function.update_of_ne hwb, Function.update_of_ne hwa]
  · rw [ket_SWAP]
    congr 1; funext w
    by_cases hwb : w = b
    · subst hwb
      rw [Function.update_self, Function.update_of_ne hab, ha, Function.update_of_ne hab.symm, hb]
    · by_cases hwa : w = a
      · subst hwa; simp [Function.update_of_ne hwb]
      · simp [Function.update_of_ne hwb, Function.update_of_ne hwa]

private theorem bswapBlockFrom2_ket {K n : ℕ} (hK1 : 1 ≤ K) (hK5 : K ≤ 5)
    (L : StepPow2Layout K n) (d : Fin K) (b b₀ : Fin 2)
    (p₀ : Fin (2 ^ K)) {β : BitAssignment n} (hOh : ∀ g : Fin (2 ^ (K + 1)), β (L.rHot g) = 0) :
    ∀ (m : ℕ) (hm : m ≤ 2 ^ (K - 1)),
      (bswapBlockFrom2 L d b m hm).eval.1.mulVec
          (XMeasCircuit.ket (Function.update β (wLeaf2 L b₀ p₀) 1)) =
        if b = b₀ ∧ (shrinkBit2 K d p₀).val < m then
          XMeasCircuit.ket (Function.update β (wLeaf2 L b₀ (flipLeafBit2 K d p₀)) 1)
        else XMeasCircuit.ket (Function.update β (wLeaf2 L b₀ p₀) 1) := by
  intro m hm; induction m with
  | zero =>
      simp only [bswapBlockFrom2, Circuit.eval_identity, Submonoid.coe_one, Matrix.one_mulVec,
        Nat.not_lt_zero, and_false, ↓reduceIte]
  | succ m ih =>
      let s : Fin (2 ^ (K - 1)) := ⟨m, hm⟩
      rw [bswapBlockFrom2, Circuit.eval_seq, Submonoid.coe_mul, ← Matrix.mulVec_mulVec,
        ih (by omega)]
      by_cases hprev : b = b₀ ∧ (shrinkBit2 K d p₀).val < m
      · rw [ite_pos2 hprev, ite_pos2 ⟨hprev.1, by omega⟩]
        have hns : s ≠ shrinkBit2 K d (flipLeafBit2 K d p₀) := by
          rw [shrinkBit2_flipLeafBit hK1 hK5]
          intro heq; have hv := congrArg Fin.val heq; dsimp [s] at hv; omega
        have hn0 : wLeaf2 L b (insertZeroBit2 K d s) ≠ wLeaf2 L b₀ (flipLeafBit2 K d p₀) :=
          fun h ↦ hns (by rw [← shrinkBit2_insertZero hK1 hK5 d s, (wLeaf2_inj L h).2])
        have hn1 : wLeaf2 L b (insertOneBit2 K d s) ≠ wLeaf2 L b₀ (flipLeafBit2 K d p₀) :=
          fun h ↦ hns (by rw [← shrinkBit2_insertOne hK1 hK5 d s, (wLeaf2_inj L h).2])
        exact swap_ket_zero_zero _ _ _
          (by rw [Function.update_of_ne hn0]; exact hOh _)
          (by rw [Function.update_of_ne hn1]; exact hOh _)
      · rw [ite_neg2 hprev]
        by_cases hcur : b = b₀ ∧ (shrinkBit2 K d p₀).val = m
        · obtain ⟨rfl, hsm⟩ := hcur
          have hsEq : s = shrinkBit2 K d p₀ := Fin.ext hsm.symm
          rw [ite_pos2 ⟨rfl, by omega⟩]
          rcases insert_shrinkBit2_cases hK1 hK5 d p₀ with ⟨hz, ho⟩ | ⟨ho, hz⟩
          · have hz' : p₀ = insertZeroBit2 K d s := by rw [hsEq, hz]
            have ho' : flipLeafBit2 K d p₀ = insertOneBit2 K d s := by rw [hsEq, ho]
            rw [ho', hz']
            exact (swap_ket_one_zero_update _ _ _ (hOh _) (hOh _)).1
          · have ho' : p₀ = insertOneBit2 K d s := by rw [hsEq, ho]
            have hz' : flipLeafBit2 K d p₀ = insertZeroBit2 K d s := by rw [hsEq, hz]
            rw [hz', ho']
            exact (swap_ket_one_zero_update _ _ _ (hOh _) (hOh _)).2
        · have hnNext : ¬ (b = b₀ ∧ (shrinkBit2 K d p₀).val < m + 1) := fun ⟨hb, hlt⟩ ↦
            by_cases (fun heq : (shrinkBit2 K d p₀).val = m ↦ hcur ⟨hb, heq⟩)
              (fun hne ↦ hprev ⟨hb, by omega⟩)
          rw [ite_neg2 hnNext]
          have hn0 : wLeaf2 L b (insertZeroBit2 K d s) ≠ wLeaf2 L b₀ p₀ := fun h ↦ by
            obtain ⟨rfl, hp⟩ := wLeaf2_inj L h
            exact hcur ⟨rfl, by rw [← hp, shrinkBit2_insertZero hK1 hK5]⟩
          have hn1 : wLeaf2 L b (insertOneBit2 K d s) ≠ wLeaf2 L b₀ p₀ := fun h ↦ by
            obtain ⟨rfl, hp⟩ := wLeaf2_inj L h
            exact hcur ⟨rfl, by rw [← hp, shrinkBit2_insertOne hK1 hK5]⟩
          exact swap_ket_zero_zero _ _ _
            (by rw [Function.update_of_ne hn0]; exact hOh _)
            (by rw [Function.update_of_ne hn1]; exact hOh _)

private theorem bswapLevelBlocks2_ket {K n : ℕ} (hK1 : 1 ≤ K) (hK5 : K ≤ 5)
    (L : StepPow2Layout K n) (d : Fin K) (b₀ : Fin 2)
    (p₀ : Fin (2 ^ K)) {β : BitAssignment n} (hOh : ∀ g : Fin (2 ^ (K + 1)), β (L.rHot g) = 0) :
    ∀ (B : ℕ) (hB : B ≤ 2),
      (bswapLevelBlocks2 L d B hB).eval.1.mulVec
          (XMeasCircuit.ket (Function.update β (wLeaf2 L b₀ p₀) 1)) =
        if b₀.val < B then XMeasCircuit.ket (Function.update β (wLeaf2 L b₀ (flipLeafBit2 K d p₀))
          1)
        else XMeasCircuit.ket (Function.update β (wLeaf2 L b₀ p₀) 1) := by
  intro B hB; induction B with
  | zero =>
      simp only [bswapLevelBlocks2, Circuit.eval_identity, Submonoid.coe_one, Matrix.one_mulVec,
        Nat.not_lt_zero, ↓reduceIte]
  | succ B ih =>
      rw [bswapLevelBlocks2, Circuit.eval_seq, Submonoid.coe_mul, ← Matrix.mulVec_mulVec,
        ih (by omega)]
      by_cases hlt : b₀.val < B
      · have hne : (⟨B, hB⟩ : Fin 2) ≠ b₀ := fun h ↦ by
          have hv := congrArg Fin.val h; dsimp at hv; omega
        rw [ite_pos2 hlt, bswapBlockFrom2_ket hK1 hK5 L d _ _ _ hOh _ le_rfl,
          ite_neg2 (fun h ↦ hne h.1), ite_pos2 (by omega)]
      · rw [ite_neg2 hlt, bswapBlockFrom2_ket hK1 hK5 L d _ _ _ hOh _ le_rfl]
        by_cases heq : b₀.val = B
        · rw [ite_pos2 ⟨Fin.ext heq.symm, (shrinkBit2 K d p₀).isLt⟩, ite_pos2 (by omega)]
        · have hne : (⟨B, hB⟩ : Fin 2) ≠ b₀ := fun h ↦ heq (congrArg Fin.val h).symm
          rw [ite_neg2 (fun h ↦ hne h.1), ite_neg2 (by omega)]

/-- Leaf index `lo % 2^(K - D) + 2^(K - D) * t` during the `K`-stage barrel shift. -/
private def shiftLeafIdx2 (K D : ℕ) (hD : D ≤ K) (lo : Fin (2 ^ K)) (t : Fin (2 ^ D)) :
    Fin (2 ^ K) :=
  ⟨lo.val % 2 ^ (K - D) + 2 ^ (K - D) * t.val, by
    have hmul : 2 ^ (K - D) * (t.val + 1) ≤ 2 ^ (K - D) * 2 ^ D :=
      Nat.mul_le_mul_left _ t.isLt
    rw [← Nat.pow_add, Nat.sub_add_cancel hD] at hmul
    have hmod : lo.val % 2 ^ (K - D) < 2 ^ (K - D) := Nat.mod_lt _ (Nat.two_pow_pos _)
    have hmul' : 2 ^ (K - D) * t.val + 2 ^ (K - D) ≤ 2 ^ K := by simpa [Nat.mul_add] using hmul
    omega⟩

/-- Superposition state with `D` remaining barrel-shift stages (`D ≤ K`). -/
private noncomputable def wShiftVec2 {K n : ℕ} (L : StepPow2Layout K n) (D : ℕ) (hD : D ≤ K)
    (β : BitAssignment n) : Fin (2 ^ n) → ℂ :=
  (XMeasCircuit.sqrtHalf ^ D) •
    ∑ t : Fin (2 ^ D),
      XMeasCircuit.ket (Function.update β
        (wLeaf2 L (bZeroOf2 L β) (shiftLeafIdx2 K D hD (loOf2 L β) t)) 1)

/-- Even/odd index bijection `Fin (2 ^ D) ⊕ Fin (2 ^ D) ≃ Fin (2 ^ (D + 1))`. -/
private def finTwoPowEvenOdd (D : ℕ) : Fin (2 ^ D) ⊕ Fin (2 ^ D) ≃ Fin (2 ^ (D + 1)) where
  toFun
    | .inl s => ⟨2 * s.val, by have := s.isLt; rw [Nat.pow_succ]; omega⟩
    | .inr s => ⟨1 + 2 * s.val, by have := s.isLt; rw [Nat.pow_succ]; omega⟩
  invFun t :=
    if t.val % 2 = 0 then
      .inl ⟨t.val / 2, by have ht : t.val < 2 ^ D * 2 := t.isLt.trans_eq (Nat.pow_succ 2 D); omega⟩
    else
      .inr ⟨t.val / 2, by have ht : t.val < 2 ^ D * 2 := t.isLt.trans_eq (Nat.pow_succ 2 D); omega⟩
  left_inv x := by
    cases x with
    | inl s =>
        dsimp only; rw [ite_pos2 (by omega)]; exact congrArg Sum.inl (Fin.ext (by dsimp; omega))
    | inr s =>
        dsimp only; rw [ite_neg2 (by omega)]; exact congrArg Sum.inr (Fin.ext (by dsimp; omega))
  right_inv t := by
    dsimp only; split_ifs with h <;> exact Fin.ext (by dsimp; omega)

private theorem sum_fin_two_pow_even_odd {M : Type*} [AddCommMonoid M] (D : ℕ)
    (f : Fin (2 ^ (D + 1)) → M) :
    (∑ t : Fin (2 ^ (D + 1)), f t) =
      ∑ s : Fin (2 ^ D),
        (f ⟨2 * s.val, by have := s.isLt; rw [Nat.pow_succ]; omega⟩ +
          f ⟨1 + 2 * s.val, by have := s.isLt; rw [Nat.pow_succ]; omega⟩) := by
  rw [← Equiv.sum_comp (finTwoPowEvenOdd D) f, Fintype.sum_sum_type,
    ← Finset.sum_add_distrib]
  rfl

private theorem ket_cnotMaskReg2 {n : ℕ} (G : ℕ) (rSrc : QRegister G n) (dst : Wire n)
    (mask : Fin G → Bool) (hdisj : ∀ g, rSrc g ≠ dst) (β : BitAssignment n) :
    (CircuitModular.UnsignedGivens.cnotMaskReg G rSrc dst mask hdisj).eval.1.mulVec
      (XMeasCircuit.ket β) =
      XMeasCircuit.ket (Function.update β dst (β dst + CircuitModular.UnsignedGivens.maskSumBit rSrc
        mask β)) :=
  CircuitModular.UnsignedGivens.evolve_cnotMaskReg_ket G rSrc dst mask hdisj β

private theorem shiftParityCirc2_ket {K n : ℕ} (hK1 : 1 ≤ K) (hK5 : K ≤ 5)
    (L : StepPow2Layout K n) (d : Fin K) (p₀ : Fin (2 ^ K))
    {β : BitAssignment n} (hS : sEncValid2 L β) :
    (shiftParityCirc2 L d).eval.1.mulVec
        (XMeasCircuit.ket (Function.update β (wLeaf2 L (bZeroOf2 L β) p₀) 1)) =
      XMeasCircuit.ket (Function.update (Function.update β (wLeaf2 L (bZeroOf2 L β) p₀) 1) L.qEnc
        ((if p₀.val / 2 ^ d.val % 2 = 1 then 1 else 0) +
          (if (loOf2 L β).val / 2 ^ d.val % 2 = 1 then 1 else 0))) := by
  let γ := Function.update β (wLeaf2 L (bZeroOf2 L β) p₀) 1
  have hq0 : γ L.qEnc = 0 := by
    dsimp only [γ]; rw [Function.update_of_ne (wLeaf2_ne_qEnc L _ _).symm]; exact hS.2
  let g₀ : Fin (2 ^ (K + 1)) := ⟨2 ^ K * (bZeroOf2 L β).val + p₀.val,
    leaf2_idx_lt (bZeroOf2 L β) p₀⟩
  have hmask : CircuitModular.UnsignedGivens.maskSumBit L.rHot
      (fun g ↦ decide ((g.val % 2 ^ K) / 2 ^ d.val % 2 = 1)) γ =
      if p₀.val / 2 ^ d.val % 2 = 1 then 1 else 0 := by
    dsimp only [CircuitModular.UnsignedGivens.maskSumBit]
    have hite (g : Fin (2 ^ (K + 1))) :
        (if decide ((g.val % 2 ^ K) / 2 ^ d.val % 2 = 1) then γ (L.rHot g) else 0) =
          if g = g₀ then (if p₀.val / 2 ^ d.val % 2 = 1 then (1 : ZMod 2) else 0) else 0 := by
      by_cases hg : g = g₀
      · subst hg
        have hmod : (2 ^ K * (bZeroOf2 L β).val + p₀.val) % 2 ^ K = p₀.val := by
          rw [Nat.mul_add_mod, Nat.mod_eq_of_lt p₀.isLt]
        have hγ1 : γ (L.rHot g₀) = 1 := Function.update_self _ _ _
        rw [ite_pos2 rfl, hγ1]; dsimp only [g₀]; rw [hmod]
        by_cases hb : p₀.val / 2 ^ d.val % 2 = 1
        · simp only [hb, decide_true, ↓reduceIte]
        · simp only [hb, decide_false, Bool.false_eq_true, ↓reduceIte]
      · have hne : L.rHot g ≠ wLeaf2 L (bZeroOf2 L β) p₀ := L.rHot.wires.injective.ne hg
        have hγ0 : γ (L.rHot g) = 0 := by
          dsimp only [γ]; rw [Function.update_of_ne hne]; exact hS.1 g
        rw [ite_neg2 hg, hγ0, ite_self]
    simp_rw [hite]
    rw [Finset.sum_ite_eq' Finset.univ g₀, ite_pos2 (Finset.mem_univ g₀)]
  have hbit : γ (L.rCtx ⟨d.val, by omega⟩) =
      if (loOf2 L β).val / 2 ^ d.val % 2 = 1 then 1 else 0 := by
    dsimp only [γ]
    rw [Function.update_of_ne (wLeaf2_ne_ctx L _ _ _).symm, ctx_bit_eq2 hK1 hK5 L β _,
      ctx_low_bit2 hK1 hK5 (CircuitModular.UnsignedGivens.localIdx L.rCtx β) d]
    rfl
  change (shiftParityCirc2 L d).eval.1.mulVec (XMeasCircuit.ket γ) =
    XMeasCircuit.ket (Function.update γ L.qEnc
      ((if p₀.val / 2 ^ d.val % 2 = 1 then 1 else 0) +
        (if (loOf2 L β).val / 2 ^ d.val % 2 = 1 then 1 else 0)))
  rw [shiftParityCirc2, eval_seq_mulVec2, ket_cnotMaskReg2, hq0, zero_add, hmask, ket_CNOT2,
    Function.update_self, Function.update_of_ne (L.hCtxEnc _), Function.update_idem, hbit]

private theorem shift_even_odd_props2 {K : ℕ} (hK1 : 1 ≤ K) (hK5 : K ≤ 5) :
    ∀ (d : Fin K) (lo : Fin (2 ^ K)) (s : Fin (2 ^ (K - 1)))
      (he : lo.val % 2 ^ d.val + 2 ^ d.val * (2 * s.val) < 2 ^ K)
      (ho : lo.val % 2 ^ d.val + 2 ^ d.val * (1 + 2 * s.val) < 2 ^ K)
      (hn : lo.val % 2 ^ (d.val + 1) + 2 ^ (d.val + 1) * s.val < 2 ^ K),
      let pe : Fin (2 ^ K) := ⟨lo.val % 2 ^ d.val + 2 ^ d.val * (2 * s.val), he⟩
      let po : Fin (2 ^ K) := ⟨lo.val % 2 ^ d.val + 2 ^ d.val * (1 + 2 * s.val), ho⟩
      let pn : Fin (2 ^ K) := ⟨lo.val % 2 ^ (d.val + 1) + 2 ^ (d.val + 1) * s.val, hn⟩
      pe.val / 2 ^ d.val % 2 = 0 ∧ po.val / 2 ^ d.val % 2 = 1 ∧
        (lo.val / 2 ^ d.val % 2 = 0 → pe = pn ∧ flipLeafBit2 K d po = pn) ∧
        (lo.val / 2 ^ d.val % 2 = 1 → po = pn ∧ flipLeafBit2 K d pe = pn) := by
  intro d lo s he ho hn pe po pn
  have hpn_mul : pn.val = lo.val % 2 ^ (d.val + 1) + 2 ^ d.val * (2 * s.val) := by
    dsimp [pn]; rw [Nat.pow_succ]; ring
  have hpn_mod : pn.val % 2 ^ d.val = lo.val % 2 ^ d.val := by
    rw [hpn_mul, Nat.add_mul_mod_self_left, (mod_succ_pow_props2 hK1 hK5 d lo).1]
  have hpn_div1 : pn.val / 2 ^ (d.val + 1) = s.val := by
    dsimp [pn]
    rw [Nat.add_mul_div_left _ _ (Nat.two_pow_pos (d.val + 1)),
      Nat.div_eq_of_lt (Nat.mod_lt _ (Nat.two_pow_pos (d.val + 1))), zero_add]
  have hq_val : (shrinkBit2 K d pn).val = lo.val % 2 ^ d.val + 2 ^ d.val * s.val := by
    dsimp [shrinkBit2]; rw [hpn_mod, hpn_div1]
  have hq_mod : (shrinkBit2 K d pn).val % 2 ^ d.val = lo.val % 2 ^ d.val := by
    rw [hq_val, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt (Nat.mod_lt _ (Nat.two_pow_pos d.val))]
  have hq_div : (shrinkBit2 K d pn).val / 2 ^ d.val = s.val := by
    rw [hq_val, Nat.add_mul_div_left _ _ (Nat.two_pow_pos d.val),
      Nat.div_eq_of_lt (Nat.mod_lt _ (Nat.two_pow_pos d.val)), zero_add]
  have hpe : pe = insertZeroBit2 K d (shrinkBit2 K d pn) := by
    apply Fin.ext; dsimp [pe, insertZeroBit2]
    rw [hq_mod, hq_div, Nat.pow_succ]; ring
  have hpo : po = insertOneBit2 K d (shrinkBit2 K d pn) := by
    apply Fin.ext; dsimp [po, insertOneBit2, insertZeroBit2]
    rw [hq_mod, hq_div, Nat.pow_succ]; ring
  have hpn_bit : pn.val / 2 ^ d.val % 2 = lo.val / 2 ^ d.val % 2 := by
    rw [hpn_mul, Nat.add_mul_div_left _ _ (Nat.two_pow_pos d.val), Nat.add_mul_mod_self_left,
      (mod_succ_pow_props2 hK1 hK5 d lo).2]
  refine ⟨by rw [hpe]; exact insertZeroBit2_div_mod hK1 hK5 d _,
    by rw [hpo]; exact insertOneBit2_div_mod hK1 hK5 d _,
    fun h0 ↦ ?_, fun h1 ↦ ?_⟩
  · have hz := (insert_of_div_mod2 hK1 hK5 d pn).1 (hpn_bit.trans h0)
    exact ⟨hpe.trans hz, by rw [hpo, flipLeafBit2_insertOne hK1 hK5, hz]⟩
  · have ho1 := (insert_of_div_mod2 hK1 hK5 d pn).2 (hpn_bit.trans h1)
    exact ⟨hpo.trans ho1, by rw [hpe, flipLeafBit2_insertZero hK1 hK5, ho1]⟩

private theorem wShiftFromDyn2_step {Var : Type} [Fintype Var] [DecidableEq Var] {K n : ℕ}
    (hK1 : 1 ≤ K) (hK5 : K ≤ 5) (v : Var) (L : StepPow2Layout K n) :
    ∀ (D : ℕ) (hD : D ≤ K),
      SubspaceStepV14 v (ketMapOp14 (sEncValid2 L) (wShiftVec2 L D hD))
        (ketMapOp14 (sEncValid2 L) (wShiftVec2 L 0 (by omega)))
        (wShiftFromDyn2 v L D hD) := by
  intro D hD; induction D with
  | zero =>
      exact SubspaceStepV14.of_circuit Circuit.identity rfl
        (by rw [Circuit.eval_identity, Submonoid.coe_one, Matrix.one_mul])
  | succ D ih =>
      let d : Fin K := ⟨K - (D + 1), by omega⟩
      have hd_eq : K - (D + 1) = d.val := rfl
      have hd1_eq : K - D = d.val + 1 := by omega
      have hsp0 : (shiftParityCirc2 L d).count .TOFF = 0 := by simp [shiftParityCirc2]
      have hbr0 : (Circuit.X L.qEnc ;;ᶜ bswapLevelBlocks2 L d 2 le_rfl).count .TOFF = 0 := by simp
      refine SubspaceStepV14.seq
        (SubspaceStepV14.seq
          (SubspaceStepV14.of_circuit (shiftParityCirc2 L d) hsp0
            (R₁ := ketMapOp14 (sEncValid2 L) fun β ↦
              (XMeasCircuit.sqrtHalf ^ (D + 1)) • ∑ t : Fin (2 ^ (D + 1)),
                (shiftParityCirc2 L d).eval.1.mulVec
                  (XMeasCircuit.ket (Function.update β
                    (wLeaf2 L (bZeroOf2 L β) (shiftLeafIdx2 K (D + 1) hD (loOf2 L β) t)) 1))) ?_)
          (SubspaceStepV14.remeasure L.qEnc _ ?_ ?_))
        (ih (by omega))
      · rw [mul_ketMapOp14]
        refine ketMapOp14_congr fun β _ ↦ ?_
        dsimp only [wShiftVec2]
        rw [Matrix.mulVec_smul, Matrix.mulVec_sum]
      · rw [mul_ketMapOp14, smul_ketMapOp14]
        refine ketMapOp14_congr fun β hS ↦ ?_
        have hq0 : β L.qEnc = 0 := hS.2
        rw [Matrix.mulVec_smul, Matrix.mulVec_sum, sum_fin_two_pow_even_odd D]
        dsimp only [wShiftVec2]
        rw [smul_smul, _root_.pow_succ, mul_comm (XMeasCircuit.sqrtHalf ^ D)]
        refine congrArg (_ • ·) (Finset.sum_congr rfl fun s _ ↦ ?_)
        have hsLt : s.val < 2 ^ (K - 1) :=
          Nat.lt_of_lt_of_le s.isLt (Nat.pow_le_pow_right (by omega) (by omega : D ≤ K - 1))
        let pe := shiftLeafIdx2 K (D + 1) hD (loOf2 L β)
          ⟨2 * s.val, by have := s.isLt; rw [Nat.pow_succ]; omega⟩
        let po := shiftLeafIdx2 K (D + 1) hD (loOf2 L β)
          ⟨1 + 2 * s.val, by have := s.isLt; rw [Nat.pow_succ]; omega⟩
        let pn := shiftLeafIdx2 K D (by omega) (loOf2 L β) s
        have he : (loOf2 L β).val % 2 ^ d.val + 2 ^ d.val * (2 * s.val) < 2 ^ K := by
          simpa only [pe, shiftLeafIdx2, hd_eq] using pe.isLt
        have ho : (loOf2 L β).val % 2 ^ d.val + 2 ^ d.val * (1 + 2 * s.val) < 2 ^ K := by
          simpa only [po, shiftLeafIdx2, hd_eq] using po.isLt
        have hn : (loOf2 L β).val % 2 ^ (d.val + 1) + 2 ^ (d.val + 1) * s.val < 2 ^ K := by
          simpa only [pn, shiftLeafIdx2, hd1_eq] using pn.isLt
        have hp := shift_even_odd_props2 hK1 hK5 d (loOf2 L β) ⟨s.val, hsLt⟩ he ho hn
        have hpeEq : (⟨(loOf2 L β).val % 2 ^ d.val + 2 ^ d.val * (2 * s.val), he⟩ :
            Fin (2 ^ K)) = pe := Fin.ext (by simp [pe, shiftLeafIdx2, hd_eq])
        have hpoEq : (⟨(loOf2 L β).val % 2 ^ d.val + 2 ^ d.val * (1 + 2 * s.val), ho⟩ :
            Fin (2 ^ K)) = po := Fin.ext (by simp [po, shiftLeafIdx2, hd_eq])
        have hpnEq : (⟨(loOf2 L β).val % 2 ^ (d.val + 1) + 2 ^ (d.val + 1) * s.val, hn⟩ :
            Fin (2 ^ K)) = pn := Fin.ext (by simp [pn, shiftLeafIdx2, hd1_eq])
        rw [hpeEq, hpoEq, hpnEq] at hp
        rw [shiftParityCirc2_ket hK1 hK5 L d pe hS, shiftParityCirc2_ket hK1 hK5 L d po hS,
          hp.1, hp.2.1, XMeasCircuit.ket_projector_zero, XMeasCircuit.ket_projector_zero]
        rcases Nat.mod_two_eq_zero_or_one ((loOf2 L β).val / 2 ^ d.val) with hlo0 | hlo1
        · obtain ⟨hpe_pn, _⟩ := hp.2.2.1 hlo0
          simp only [hlo0, Nat.zero_ne_one, ↓reduceIte, add_zero, Function.update_self,
            one_ne_zero]
          have hclr : Function.update (Function.update β (wLeaf2 L (bZeroOf2 L β) pe) 1) L.qEnc 0 =
              Function.update β (wLeaf2 L (bZeroOf2 L β) pn) 1 := by
            rw [hpe_pn]; funext w
            by_cases hw : w = L.qEnc
            · subst hw; rw [Function.update_self, Function.update_of_ne (wLeaf2_ne_qEnc L _ _).symm,
                hq0]
            · exact Function.update_of_ne hw _ _
          rw [hclr]
        · obtain ⟨hpo_pn, _⟩ := hp.2.2.2 hlo1
          simp only [hlo1, Nat.zero_ne_one, ↓reduceIte, zero_add, CharTwo.add_self_eq_zero,
            Function.update_self, one_ne_zero]
          have hclr : Function.update (Function.update β (wLeaf2 L (bZeroOf2 L β) po) 1) L.qEnc 0 =
              Function.update β (wLeaf2 L (bZeroOf2 L β) pn) 1 := by
            rw [hpo_pn]; funext w
            by_cases hw : w = L.qEnc
            · subst hw; rw [Function.update_self, Function.update_of_ne (wLeaf2_ne_qEnc L _ _).symm,
                hq0]
            · exact Function.update_of_ne hw _ _
          rw [hclr]
      · refine SubspaceStepV14.of_circuit _ hbr0 ?_
        rw [mul_ketMapOp14, mul_ketMapOp14, smul_ketMapOp14]
        refine ketMapOp14_congr fun β hS ↦ ?_
        have hq0 : β L.qEnc = 0 := hS.2
        rw [Matrix.mulVec_smul, Matrix.mulVec_sum, Matrix.mulVec_smul, Matrix.mulVec_sum,
          sum_fin_two_pow_even_odd D]
        dsimp only [wShiftVec2]
        rw [smul_smul, _root_.pow_succ, mul_comm (XMeasCircuit.sqrtHalf ^ D)]
        refine congrArg (_ • ·) (Finset.sum_congr rfl fun s _ ↦ ?_)
        have hsLt : s.val < 2 ^ (K - 1) :=
          Nat.lt_of_lt_of_le s.isLt (Nat.pow_le_pow_right (by omega) (by omega : D ≤ K - 1))
        let pe := shiftLeafIdx2 K (D + 1) hD (loOf2 L β)
          ⟨2 * s.val, by have := s.isLt; rw [Nat.pow_succ]; omega⟩
        let po := shiftLeafIdx2 K (D + 1) hD (loOf2 L β)
          ⟨1 + 2 * s.val, by have := s.isLt; rw [Nat.pow_succ]; omega⟩
        let pn := shiftLeafIdx2 K D (by omega) (loOf2 L β) s
        have he : (loOf2 L β).val % 2 ^ d.val + 2 ^ d.val * (2 * s.val) < 2 ^ K := by
          simpa only [pe, shiftLeafIdx2, hd_eq] using pe.isLt
        have ho : (loOf2 L β).val % 2 ^ d.val + 2 ^ d.val * (1 + 2 * s.val) < 2 ^ K := by
          simpa only [po, shiftLeafIdx2, hd_eq] using po.isLt
        have hn : (loOf2 L β).val % 2 ^ (d.val + 1) + 2 ^ (d.val + 1) * s.val < 2 ^ K := by
          simpa only [pn, shiftLeafIdx2, hd1_eq] using pn.isLt
        have hp := shift_even_odd_props2 hK1 hK5 d (loOf2 L β) ⟨s.val, hsLt⟩ he ho hn
        have hpeEq : (⟨(loOf2 L β).val % 2 ^ d.val + 2 ^ d.val * (2 * s.val), he⟩ :
            Fin (2 ^ K)) = pe := Fin.ext (by simp [pe, shiftLeafIdx2, hd_eq])
        have hpoEq : (⟨(loOf2 L β).val % 2 ^ d.val + 2 ^ d.val * (1 + 2 * s.val), ho⟩ :
            Fin (2 ^ K)) = po := Fin.ext (by simp [po, shiftLeafIdx2, hd_eq])
        have hpnEq : (⟨(loOf2 L β).val % 2 ^ (d.val + 1) + 2 ^ (d.val + 1) * s.val, hn⟩ :
            Fin (2 ^ K)) = pn := Fin.ext (by simp [pn, shiftLeafIdx2, hd1_eq])
        rw [hpeEq, hpoEq, hpnEq] at hp
        rw [shiftParityCirc2_ket hK1 hK5 L d pe hS, shiftParityCirc2_ket hK1 hK5 L d po hS,
          hp.1, hp.2.1, XMeasCircuit.ket_projector_one, XMeasCircuit.ket_projector_one]
        rcases Nat.mod_two_eq_zero_or_one ((loOf2 L β).val / 2 ^ d.val) with hlo0 | hlo1
        · obtain ⟨_, hpo_fl⟩ := hp.2.2.1 hlo0
          simp only [hlo0, ↓reduceIte, add_zero, zero_add,
            Function.update_self, zero_ne_one, Matrix.mulVec_zero]
          rw [eval_seq_mulVec2, XMeasCircuit.ket_X]
          have hclr : Function.update
              (Function.update (Function.update β (wLeaf2 L (bZeroOf2 L β) po) 1) L.qEnc 1) L.qEnc
              (Function.update (Function.update β (wLeaf2 L (bZeroOf2 L β) po) 1) L.qEnc 1 L.qEnc +
                1) = Function.update β (wLeaf2 L (bZeroOf2 L β) po) 1 := by
            funext w
            by_cases hw : w = L.qEnc
            · subst hw; simp [Function.update_of_ne (wLeaf2_ne_qEnc L _ _).symm, hq0]
            · simp [Function.update_of_ne hw]
          rw [hclr, bswapLevelBlocks2_ket hK1 hK5 L d _ _ hS.1 2 le_rfl,
            ite_pos2 (bZeroOf2 L β).isLt, hpo_fl]
        · obtain ⟨_, hpe_fl⟩ := hp.2.2.2 hlo1
          simp only [hlo1, ↓reduceIte, zero_add, CharTwo.add_self_eq_zero,
            Function.update_self, zero_ne_one, Matrix.mulVec_zero, add_zero]
          rw [eval_seq_mulVec2, XMeasCircuit.ket_X]
          have hclr : Function.update
              (Function.update (Function.update β (wLeaf2 L (bZeroOf2 L β) pe) 1) L.qEnc 1) L.qEnc
              (Function.update (Function.update β (wLeaf2 L (bZeroOf2 L β) pe) 1) L.qEnc 1 L.qEnc +
                1) = Function.update β (wLeaf2 L (bZeroOf2 L β) pe) 1 := by
            funext w
            by_cases hw : w = L.qEnc
            · subst hw; simp [Function.update_of_ne (wLeaf2_ne_qEnc L _ _).symm, hq0]
            · simp [Function.update_of_ne hw]
          rw [hclr, bswapLevelBlocks2_ket hK1 hK5 L d _ _ hS.1 2 le_rfl,
            ite_pos2 (bZeroOf2 L β).isLt, hpe_fl]
/-- Lower `d`-bit mask `lo % 2^d` inside `Fin (2 ^ K)`. -/
private def pCur2 (K : ℕ) (d : Fin K) (lo : Fin (2 ^ K)) : Fin (2 ^ K) :=
  ⟨lo.val % 2 ^ d.val, mod_two_pow_lt_powK lo.val d.val (by omega)⟩

/-- Upper `d`-bit partner `(lo % 2^d) + 2^d` inside `Fin (2 ^ K)`. -/
private def pHi2 (K : ℕ) (d : Fin K) (lo : Fin (2 ^ K)) : Fin (2 ^ K) :=
  ⟨lo.val % 2 ^ d.val + 2 ^ d.val, by
    have := Nat.mod_lt lo.val (Nat.two_pow_pos d.val)
    have := two_mul_two_pow_le d
    omega⟩

/-- `(d + 1)`-bit mask `lo % 2^(d + 1)` inside `Fin (2 ^ K)`. -/
private def pNextOf2 (K : ℕ) (d : Fin K) (lo : Fin (2 ^ K)) : Fin (2 ^ K) :=
  ⟨lo.val % 2 ^ (d.val + 1), mod_two_pow_lt_powK lo.val (d.val + 1) (by omega)⟩

private theorem lo_mod_succ_val2 {K : ℕ} (hK1 : 1 ≤ K) (hK5 : K ≤ 5) :
    ∀ (d : Fin K) (lo : Fin (2 ^ K)),
      (lo.val / 2 ^ d.val % 2 = 0 ∧ lo.val % 2 ^ (d.val + 1) = (pCur2 K d lo).val) ∨
      (lo.val / 2 ^ d.val % 2 = 1 ∧ lo.val % 2 ^ (d.val + 1) = (pHi2 K d lo).val) := by
  rcases k15_cases hK1 hK5 with rfl | rfl | rfl | rfl | rfl <;> decide

private theorem lo_mod_succ_cases2 {K : ℕ} (hK1 : 1 ≤ K) (hK5 : K ≤ 5)
    (d : Fin K) (lo : Fin (2 ^ K)) :
    (lo.val / 2 ^ d.val % 2 = 0 ∧ pNextOf2 K d lo = pCur2 K d lo) ∨
    (lo.val / 2 ^ d.val % 2 = 1 ∧ pNextOf2 K d lo = pHi2 K d lo) := by
  rcases lo_mod_succ_val2 hK1 hK5 d lo with ⟨h0, hv⟩ | ⟨h1, hv⟩
  · exact Or.inl ⟨h0, Fin.ext hv⟩
  · exact Or.inr ⟨h1, Fin.ext hv⟩

/-- Post-unload bit assignment at tree level `d < K`. -/
private noncomputable def gammaBase2 {K n : ℕ} (L : StepPow2Layout K n) (d : Fin K)
    (β : BitAssignment n) : BitAssignment n :=
  Function.update β (wLeaf2 L (bZeroOf2 L β) (pCur2 K d (loOf2 L β))) 1

/-- Post-fold bit assignment at tree level `d < K`. -/
private noncomputable def gammaFold2 {K n : ℕ} (L : StepPow2Layout K n) (d : Fin K)
    (β : BitAssignment n) : BitAssignment n :=
  Function.update (gammaBase2 L d β) (wLeaf2 L (bZeroOf2 L β) (pHi2 K d (loOf2 L β)))
    (β (L.rCtx ⟨d.val, by omega⟩))

private theorem wFoldBlockFrom2_ket {K n : ℕ} (hK1 : 1 ≤ K) (hK5 : K ≤ 5)
    (L : StepPow2Layout K n) (d : Fin K) (b : Fin 2)
    {β : BitAssignment n} (hS : sEncValid2 L β) :
    ∀ (m : ℕ) (hm : m ≤ 2 ^ d.val),
      (wFoldBlockFrom2 L d b m hm).eval.1.mulVec
          (XMeasCircuit.ket
            (Function.update β (wLeaf2 L (bZeroOf2 L β) (pNextOf2 K d (loOf2 L β))) 1)) =
        if b = bZeroOf2 L β ∧ (pCur2 K d (loOf2 L β)).val < m then
          XMeasCircuit.ket (gammaFold2 L d β)
        else XMeasCircuit.ket
          (Function.update β (wLeaf2 L (bZeroOf2 L β) (pNextOf2 K d (loOf2 L β))) 1) := by
  intro m hm; induction m with
  | zero =>
      simp only [wFoldBlockFrom2, Circuit.eval_identity, Submonoid.coe_one, Matrix.one_mulVec,
        Nat.not_lt_zero, and_false, ↓reduceIte]
  | succ m ih =>
      have hd : 2 * 2 ^ d.val ≤ 2 ^ K := two_mul_two_pow_le d
      have hbit : β (L.rCtx ⟨d.val, by omega⟩) =
          if (loOf2 L β).val / 2 ^ d.val % 2 = 1 then 1 else 0 := by
        rw [ctx_bit_eq2 hK1 hK5 L β _, ctx_low_bit2 hK1 hK5 (CircuitModular.UnsignedGivens.localIdx
          L.rCtx β) d]
        rfl
      rw [wFoldBlockFrom2, eval_seq_mulVec2, ih (by omega)]
      by_cases hprev : b = bZeroOf2 L β ∧ (pCur2 K d (loOf2 L β)).val < m
      · rw [ite_pos2 hprev, ite_pos2 ⟨hprev.1, by omega⟩, ket_CNOT2]
        have hne1 : wLeaf2 L b ⟨m + 2 ^ d.val, by omega⟩ ≠
            wLeaf2 L (bZeroOf2 L β) (pHi2 K d (loOf2 L β)) := fun h ↦ by
          have hv := congrArg Fin.val (wLeaf2_inj L h).2
          dsimp [pHi2, pCur2] at hv hprev; omega
        have hne2 : wLeaf2 L b ⟨m + 2 ^ d.val, by omega⟩ ≠
            wLeaf2 L (bZeroOf2 L β) (pCur2 K d (loOf2 L β)) := fun h ↦ by
          have hv := congrArg Fin.val (wLeaf2_inj L h).2
          have hlt := Nat.mod_lt (loOf2 L β).val (Nat.two_pow_pos d.val)
          dsimp [pCur2] at hv; omega
        have hsrc0 : gammaFold2 L d β (wLeaf2 L b ⟨m + 2 ^ d.val, by omega⟩) = 0 := by
          dsimp only [gammaFold2, gammaBase2]
          rw [Function.update_of_ne hne1, Function.update_of_ne hne2]; exact hS.1 _
        rw [hsrc0, add_zero, Function.update_eq_self]
      · rw [ite_neg2 hprev, ket_CNOT2]
        by_cases hcur : b = bZeroOf2 L β ∧ (pCur2 K d (loOf2 L β)).val = m
        · obtain ⟨rfl, hpm⟩ := hcur
          rw [ite_pos2 ⟨rfl, by omega⟩]
          rcases lo_mod_succ_cases2 hK1 hK5 d (loOf2 L β) with ⟨h0, hpEq⟩ | ⟨h1, hpEq⟩
          · have hneSrc : wLeaf2 L (bZeroOf2 L β) ⟨m + 2 ^ d.val, by omega⟩ ≠
                wLeaf2 L (bZeroOf2 L β) (pNextOf2 K d (loOf2 L β)) := fun h ↦ by
              have hv := congrArg Fin.val (wLeaf2_inj L h).2
              have hp0 := Nat.two_pow_pos d.val
              rw [hpEq] at hv; dsimp [pCur2] at hv hpm; omega
            have hsrc0 : Function.update β (wLeaf2 L (bZeroOf2 L β) (pNextOf2 K d (loOf2 L β))) 1
                (wLeaf2 L (bZeroOf2 L β) ⟨m + 2 ^ d.val, by omega⟩) = 0 := by
              rw [Function.update_of_ne hneSrc]; exact hS.1 _
            rw [hsrc0, add_zero, Function.update_eq_self, hpEq]
            congr 1; funext w
            dsimp only [gammaFold2, gammaBase2]
            rw [hbit, ite_neg2 (by omega)]
            by_cases hw : w = wLeaf2 L (bZeroOf2 L β) (pHi2 K d (loOf2 L β))
            · subst hw
              have hneHi : wLeaf2 L (bZeroOf2 L β) (pHi2 K d (loOf2 L β)) ≠
                  wLeaf2 L (bZeroOf2 L β) (pCur2 K d (loOf2 L β)) := fun h ↦ by
                have hv := congrArg Fin.val (wLeaf2_inj L h).2
                have hd0 := Nat.two_pow_pos d.val; dsimp [pHi2, pCur2] at hv; omega
              rw [Function.update_self, Function.update_of_ne hneHi]; exact hS.1 _
            · exact (Function.update_of_ne hw _ _).symm
          · have hmEq : (⟨m + 2 ^ d.val, by omega⟩ : Fin (2 ^ K)) = pHi2 K d (loOf2 L β) :=
              Fin.ext (by dsimp [pHi2, pCur2] at hpm ⊢; omega)
            have hcEq : (⟨m, by omega⟩ : Fin (2 ^ K)) = pCur2 K d (loOf2 L β) := Fin.ext hpm.symm
            have hneCurHi : wLeaf2 L (bZeroOf2 L β) (pCur2 K d (loOf2 L β)) ≠
                wLeaf2 L (bZeroOf2 L β) (pHi2 K d (loOf2 L β)) := fun h ↦ by
              have hv := congrArg Fin.val (wLeaf2_inj L h).2
              have hd0 := Nat.two_pow_pos d.val; dsimp [pHi2, pCur2] at hv; omega
            rw [hpEq, hmEq, hcEq, Function.update_self, Function.update_of_ne hneCurHi,
              hS.1 _, zero_add]
            congr 1; funext w
            dsimp only [gammaFold2, gammaBase2]
            rw [hbit, ite_pos2 h1]
            by_cases hw1 : w = wLeaf2 L (bZeroOf2 L β) (pCur2 K d (loOf2 L β))
            · subst hw1; rw [Function.update_self, Function.update_of_ne hneCurHi,
                Function.update_self]
            · rw [Function.update_of_ne hw1]
              by_cases hw2 : w = wLeaf2 L (bZeroOf2 L β) (pHi2 K d (loOf2 L β))
              · subst hw2; simp
              · simp [Function.update_of_ne hw2, Function.update_of_ne hw1]
        · have hnNext : ¬ (b = bZeroOf2 L β ∧ (pCur2 K d (loOf2 L β)).val < m + 1) :=
            fun ⟨hb, hlt⟩ ↦ by_cases (fun heq : (pCur2 K d (loOf2 L β)).val = m ↦ hcur ⟨hb, heq⟩)
              (fun hne ↦ hprev ⟨hb, by omega⟩)
          rw [ite_neg2 hnNext]
          have hneSrc : wLeaf2 L b ⟨m + 2 ^ d.val, by omega⟩ ≠
              wLeaf2 L (bZeroOf2 L β) (pNextOf2 K d (loOf2 L β)) := fun h ↦ by
            obtain ⟨rfl, hp⟩ := wLeaf2_inj L h
            rcases lo_mod_succ_cases2 hK1 hK5 d (loOf2 L β) with ⟨_, hpEq⟩ | ⟨_, hpEq⟩
            · have hv := congrArg Fin.val (hp.trans hpEq)
              have hlt := Nat.mod_lt (loOf2 L β).val (Nat.two_pow_pos d.val)
              dsimp [pCur2] at hv; omega
            · have hv := congrArg Fin.val (hp.trans hpEq)
              dsimp [pHi2] at hv
              exact hcur ⟨rfl, by dsimp [pCur2]; omega⟩
          have hsrc0 : Function.update β (wLeaf2 L (bZeroOf2 L β) (pNextOf2 K d (loOf2 L β))) 1
              (wLeaf2 L b ⟨m + 2 ^ d.val, by omega⟩) = 0 := by
            rw [Function.update_of_ne hneSrc]; exact hS.1 _
          rw [hsrc0, add_zero, Function.update_eq_self]

private theorem wFoldLevelBlocks2_ket {K n : ℕ} (hK1 : 1 ≤ K) (hK5 : K ≤ 5)
    (L : StepPow2Layout K n) (d : Fin K) {β : BitAssignment n} (hS : sEncValid2 L β) :
    ∀ (B : ℕ) (hB : B ≤ 2),
      (wFoldLevelBlocks2 L d B hB).eval.1.mulVec
          (XMeasCircuit.ket
            (Function.update β (wLeaf2 L (bZeroOf2 L β) (pNextOf2 K d (loOf2 L β))) 1)) =
        if (bZeroOf2 L β).val < B then XMeasCircuit.ket (gammaFold2 L d β)
        else XMeasCircuit.ket
          (Function.update β (wLeaf2 L (bZeroOf2 L β) (pNextOf2 K d (loOf2 L β))) 1) := by
  intro B hB; induction B with
  | zero =>
      simp only [wFoldLevelBlocks2, Circuit.eval_identity, Submonoid.coe_one, Matrix.one_mulVec,
        Nat.not_lt_zero, ↓reduceIte]
  | succ B ih =>
      rw [wFoldLevelBlocks2, eval_seq_mulVec2, ih (by omega)]
      by_cases hlt : (bZeroOf2 L β).val < B
      · have hne : (⟨B, hB⟩ : Fin 2) ≠ bZeroOf2 L β := fun h ↦ by
          have hv := congrArg Fin.val h; dsimp at hv; omega
        rw [ite_pos2 hlt, ite_pos2 (by omega)]
        have hfix : ∀ (m : ℕ) (hm : m ≤ 2 ^ d.val),
            (wFoldBlockFrom2 L d ⟨B, hB⟩ m hm).eval.1.mulVec (XMeasCircuit.ket (gammaFold2 L d β)) =
              XMeasCircuit.ket (gammaFold2 L d β) := by
          intro m hm; induction m with
          | zero =>
              simp only [wFoldBlockFrom2, Circuit.eval_identity, Submonoid.coe_one,
                Matrix.one_mulVec]
          | succ m ihm =>
              have _ : 2 * 2 ^ d.val ≤ 2 ^ K := two_mul_two_pow_le d
              rw [wFoldBlockFrom2, eval_seq_mulVec2, ihm (by omega), ket_CNOT2]
              have hne1 : wLeaf2 L ⟨B, hB⟩ ⟨m + 2 ^ d.val, by omega⟩ ≠
                  wLeaf2 L (bZeroOf2 L β) (pHi2 K d (loOf2 L β)) := fun h ↦ hne (wLeaf2_inj L h).1
              have hne2 : wLeaf2 L ⟨B, hB⟩ ⟨m + 2 ^ d.val, by omega⟩ ≠
                  wLeaf2 L (bZeroOf2 L β) (pCur2 K d (loOf2 L β)) := fun h ↦ hne (wLeaf2_inj L h).1
              have hsrc0 : gammaFold2 L d β (wLeaf2 L ⟨B, hB⟩ ⟨m + 2 ^ d.val, by omega⟩) = 0 := by
                dsimp only [gammaFold2, gammaBase2]
                rw [Function.update_of_ne hne1, Function.update_of_ne hne2]; exact hS.1 _
              rw [hsrc0, add_zero, Function.update_eq_self]
        exact hfix (2 ^ d.val) le_rfl
      · rw [ite_neg2 hlt, wFoldBlockFrom2_ket hK1 hK5 L d ⟨B, hB⟩ hS (2 ^ d.val) le_rfl]
        by_cases heq : (bZeroOf2 L β).val = B
        · have hbEq : (⟨B, hB⟩ : Fin 2) = bZeroOf2 L β := Fin.ext heq.symm
          have hcurLt : (pCur2 K d (loOf2 L β)).val < 2 ^ d.val :=
            Nat.mod_lt _ (Nat.two_pow_pos _)
          rw [ite_pos2 ⟨hbEq, hcurLt⟩, ite_pos2 (by omega)]
        · have hne : (⟨B, hB⟩ : Fin 2) ≠ bZeroOf2 L β := fun h ↦ heq (congrArg Fin.val h).symm
          rw [ite_neg2 (fun h ↦ hne h.1), ite_neg2 (by omega)]

/-- Intermediate bit assignment after unloading `(B, m)` leaves at tree level `d < K`. -/
private noncomputable def gammaUnload2 {K n : ℕ} (L : StepPow2Layout K n) (d : Fin K)
    (B : ℕ) (m : ℕ) (β : BitAssignment n) : BitAssignment n :=
  if (bZeroOf2 L β).val < B ∨ ((bZeroOf2 L β).val = B ∧ (pCur2 K d (loOf2 L β)).val < m) then
    gammaBase2 L d β
  else gammaFold2 L d β

private theorem cleanFinset_singleton_ketMapOp {n : ℕ} (q : Wire n) (S : BitAssignment n → Prop)
    (g : BitAssignment n → BitAssignment n) (hg : ∀ β, S β → g β q = 0) :
    XMeasCircuit.cleanFinsetProj {q} * ketMapOp14 S (fun β ↦ XMeasCircuit.ket (g β)) =
      ketMapOp14 S (fun β ↦ XMeasCircuit.ket (g β)) := by
  have himg : (QRegister.singleton q).image = {q} := by ext w; simp
  rw [← himg, ← XMeasCircuit.basisOutcomeProjector_zero_eq_cleanFinsetProj, mul_ketMapOp14]
  refine ketMapOp14_congr fun β hS ↦ ?_
  rw [XMeasCircuit.ket_projector_zero, ite_pos2 (hg β hS)]

private theorem wUnloadBlockFrom2_step {Var : Type} [Fintype Var] [DecidableEq Var] {K n : ℕ}
    (v : Var) (L : StepPow2Layout K n) (d : Fin K) (b : Fin 2) :
    ∀ (m : ℕ) (hm : m ≤ 2 ^ d.val),
      SubspaceStepV14 v
        (ketMapOp14 (sEncValid2 L) (fun β ↦ XMeasCircuit.ket (gammaUnload2 L d b.val 0 β)))
        (ketMapOp14 (sEncValid2 L) (fun β ↦ XMeasCircuit.ket (gammaUnload2 L d b.val m β)))
        (wUnloadBlockFrom2 v L d b m hm) := by
  intro m hm; induction m with
  | zero =>
      exact SubspaceStepV14.of_circuit Circuit.identity rfl
        (by rw [Circuit.eval_identity, Submonoid.coe_one, Matrix.one_mul])
  | succ m ih =>
      have _ : 2 * 2 ^ d.val ≤ 2 ^ K := two_mul_two_pow_le d
      have hp0 := Nat.two_pow_pos d.val
      let q := wLeaf2 L b ⟨m + 2 ^ d.val, by omega⟩
      let wLo := wLeaf2 L b ⟨m, by omega⟩
      let wBit := L.rCtx ⟨d.val, by omega⟩
      let f : BitAssignment n → ZMod 2 := fun γ ↦ γ wLo * γ wBit
      have hqLo : wLo ≠ q := fun h ↦ by
        have hv := congrArg Fin.val (wLeaf2_inj L h).2; dsimp at hv; omega
      have hqBit : wBit ≠ q := (wLeaf2_ne_ctx L b ⟨m + 2 ^ d.val, by omega⟩ _).symm
      have hf : ∀ γ val, f (Function.update γ q val) = f γ := fun γ val ↦ by
        dsimp only [f]; rw [Function.update_of_ne hqLo, Function.update_of_ne hqBit]
      have hClean : XMeasCircuit.cleanFinsetProj {q} *
          ketMapOp14 (sEncValid2 L) (fun β ↦ XMeasCircuit.ket (gammaUnload2 L d b.val (m +
            1) β)) =
          ketMapOp14 (sEncValid2 L) (fun β ↦ XMeasCircuit.ket (gammaUnload2 L d b.val (m +
            1) β)) :=
        cleanFinset_singleton_ketMapOp q (sEncValid2 L) _ fun β hS ↦ by
          have hneCur : q ≠ wLeaf2 L (bZeroOf2 L β) (pCur2 K d (loOf2 L β)) := fun h ↦ by
            have hv := congrArg Fin.val (wLeaf2_inj L h).2
            have hlt := Nat.mod_lt (loOf2 L β).val (Nat.two_pow_pos d.val)
            dsimp [pCur2] at hv; omega
          dsimp only [gammaUnload2]
          split_ifs with hc
          · dsimp only [gammaBase2]; rw [Function.update_of_ne hneCur]; exact hS.1 _
          · have hneHi : q ≠ wLeaf2 L (bZeroOf2 L β) (pHi2 K d (loOf2 L β)) := fun h ↦ by
              obtain ⟨hb, hp⟩ := wLeaf2_inj L h
              have hv := congrArg Fin.val hp; dsimp [pHi2] at hv
              exact hc (Or.inr ⟨congrArg Fin.val hb.symm, by dsimp [pCur2]; omega⟩)
            dsimp only [gammaFold2, gammaBase2]
            rw [Function.update_of_ne hneHi, Function.update_of_ne hneCur]; exact hS.1 _
      have hXor : (XMeasCircuit.xorWireUnitary q f hf).1 *
          ketMapOp14 (sEncValid2 L) (fun β ↦ XMeasCircuit.ket (gammaUnload2 L d b.val (m +
            1) β)) =
          ketMapOp14 (sEncValid2 L) (fun β ↦ XMeasCircuit.ket (gammaUnload2 L d b.val m β)) := by
        rw [mul_ketMapOp14]
        refine ketMapOp14_congr fun β hS ↦ ?_
        rw [XMeasCircuit.xorWireUnitary_mulVec_ket]
        congr 1
        by_cases hhit : (bZeroOf2 L β).val = b.val ∧ (pCur2 K d (loOf2 L β)).val = m
        · obtain ⟨hbv, hpm⟩ := hhit
          have hbEq : bZeroOf2 L β = b := Fin.ext hbv
          have hpEq : pCur2 K d (loOf2 L β) = ⟨m, by omega⟩ := Fin.ext hpm
          have hqEq : q = wLeaf2 L (bZeroOf2 L β) (pHi2 K d (loOf2 L β)) := by
            dsimp only [q]; rw [hbEq]
            exact congrArg (wLeaf2 L b) (Fin.ext (by dsimp [pHi2, pCur2] at hpm ⊢; omega))
          have h1 : gammaUnload2 L d b.val (m + 1) β = gammaBase2 L d β :=
            ite_pos2 (Or.inr ⟨hbv, by omega⟩)
          have h0 : gammaUnload2 L d b.val m β = gammaFold2 L d β := ite_neg2 (by omega)
          have hwLo : gammaBase2 L d β wLo = 1 := by
            dsimp only [gammaBase2, wLo]; rw [hbEq, hpEq, Function.update_self]
          have hwBit : gammaBase2 L d β wBit = β wBit :=
            Function.update_of_ne (wLeaf2_ne_ctx L _ _ _).symm _ _
          have hq0 : gammaBase2 L d β q = 0 := by
            dsimp only [gammaBase2]; rw [hbEq, hpEq, Function.update_of_ne hqLo.symm]; exact hS.1 _
          rw [h1, h0]; dsimp only [f]; rw [hq0, hwLo, hwBit, zero_add, one_mul, hqEq]; rfl
        · have heqUnl : gammaUnload2 L d b.val (m + 1) β = gammaUnload2 L d b.val m β := by
            dsimp only [gammaUnload2]
            have hiff : ((bZeroOf2 L β).val < b.val ∨
                ((bZeroOf2 L β).val = b.val ∧ (pCur2 K d (loOf2 L β)).val < m + 1)) ↔
              ((bZeroOf2 L β).val < b.val ∨
                ((bZeroOf2 L β).val = b.val ∧ (pCur2 K d (loOf2 L β)).val < m)) := by omega
            by_cases hc : (bZeroOf2 L β).val < b.val ∨
                ((bZeroOf2 L β).val = b.val ∧ (pCur2 K d (loOf2 L β)).val < m)
            · rw [ite_pos2 (hiff.mpr hc), ite_pos2 hc]
            · rw [ite_neg2 (mt hiff.mp hc), ite_neg2 hc]
          have hwLo0 : gammaUnload2 L d b.val m β wLo = 0 := by
            have hneCur : wLo ≠ wLeaf2 L (bZeroOf2 L β) (pCur2 K d (loOf2 L β)) := fun h ↦ by
              obtain ⟨hb, hp⟩ := wLeaf2_inj L h
              exact hhit ⟨congrArg Fin.val hb.symm, (congrArg Fin.val hp).symm⟩
            have hneHi : wLo ≠ wLeaf2 L (bZeroOf2 L β) (pHi2 K d (loOf2 L β)) := fun h ↦ by
              have hv := congrArg Fin.val (wLeaf2_inj L h).2
              dsimp [pHi2] at hv; omega
            dsimp only [gammaUnload2, gammaFold2, gammaBase2]
            split_ifs
            · rw [Function.update_of_ne hneCur]; exact hS.1 _
            · rw [Function.update_of_ne hneHi, Function.update_of_ne hneCur]; exact hS.1 _
          rw [heqUnl]; dsimp only [f]; rw [hwLo0, zero_mul, add_zero, Function.update_eq_self]
      exact SubspaceStepV14.seq (ih (by omega))
        (SubspaceStepV14.congr hXor rfl
          (SubspaceStepV14.xMeasUnload_circuit q f hf _ rfl
            (czCircuit_eval_eq_phaseFlip2 wLo wBit _) hClean))

private theorem wUnloadLevelBlocks2_step {Var : Type} [Fintype Var] [DecidableEq Var] {K n : ℕ}
    (v : Var) (L : StepPow2Layout K n) (d : Fin K) :
    ∀ (B : ℕ) (hB : B ≤ 2),
      SubspaceStepV14 v
        (ketMapOp14 (sEncValid2 L) (fun β ↦ XMeasCircuit.ket (gammaFold2 L d β)))
        (ketMapOp14 (sEncValid2 L) (fun β ↦ XMeasCircuit.ket (gammaUnload2 L d B 0 β)))
        (wUnloadLevelBlocks2 v L d B hB) := by
  intro B hB; induction B with
  | zero =>
      refine SubspaceStepV14.of_circuit Circuit.identity rfl ?_
      rw [Circuit.eval_identity, Submonoid.coe_one, Matrix.one_mul]
      exact ketMapOp14_congr fun β _ ↦ congrArg XMeasCircuit.ket (ite_neg2 (by omega)).symm
  | succ B ih =>
      have hEnd : ketMapOp14 (sEncValid2 L)
            (fun β ↦ XMeasCircuit.ket (gammaUnload2 L d B (2 ^ d.val) β)) =
          ketMapOp14 (sEncValid2 L) (fun β ↦ XMeasCircuit.ket (gammaUnload2 L d (B +
            1) 0 β)) := by
        refine ketMapOp14_congr fun β _ ↦ congrArg XMeasCircuit.ket ?_
        have hcurLt : (pCur2 K d (loOf2 L β)).val < 2 ^ d.val := Nat.mod_lt _ (Nat.two_pow_pos _)
        have hiff : ((bZeroOf2 L β).val < B ∨
            ((bZeroOf2 L β).val = B ∧ (pCur2 K d (loOf2 L β)).val < 2 ^ d.val)) ↔
          ((bZeroOf2 L β).val < B + 1 ∨
            ((bZeroOf2 L β).val = B + 1 ∧ (pCur2 K d (loOf2 L β)).val < 0)) := by omega
        dsimp only [gammaUnload2]
        by_cases hc : (bZeroOf2 L β).val < B + 1 ∨
            ((bZeroOf2 L β).val = B + 1 ∧ (pCur2 K d (loOf2 L β)).val < 0)
        · rw [ite_pos2 (hiff.mpr hc), ite_pos2 hc]
        · rw [ite_neg2 (mt hiff.mp hc), ite_neg2 hc]
      exact SubspaceStepV14.seq (ih (by omega))
        (SubspaceStepV14.congr rfl hEnd
          (wUnloadBlockFrom2_step v L d ⟨B, hB⟩ (2 ^ d.val) le_rfl))

/-- Intermediate one-hot state with `R` uncomputed tree levels remaining (`R ≤ K`). -/
private noncomputable def wDecAssign2 {K n : ℕ} (L : StepPow2Layout K n) (R : ℕ) (hR : R ≤ K)
    (β : BitAssignment n) : BitAssignment n :=
  Function.update β (wLeaf2 L (bZeroOf2 L β)
    ⟨(loOf2 L β).val % 2 ^ R, mod_two_pow_lt_powK _ _ hR⟩) 1

private theorem wUncompTreeLevels2_step {Var : Type} [Fintype Var] [DecidableEq Var] {K n : ℕ}
    (hK1 : 1 ≤ K) (hK5 : K ≤ 5) (v : Var) (L : StepPow2Layout K n) :
    ∀ (R : ℕ) (hR : R ≤ K),
      SubspaceStepV14 v
        (ketMapOp14 (sEncValid2 L) (fun β ↦ XMeasCircuit.ket (wDecAssign2 L R hR β)))
        (ketMapOp14 (sEncValid2 L) (fun β ↦ XMeasCircuit.ket (wDecAssign2 L 0 (by omega) β)))
        (wUncompTreeLevels2 v L R hR) := by
  intro R hR; induction R with
  | zero =>
      exact SubspaceStepV14.of_circuit Circuit.identity rfl
        (by rw [Circuit.eval_identity, Submonoid.coe_one, Matrix.one_mul])
  | succ R ih =>
      let d : Fin K := ⟨R, hR⟩
      have hf0 : (wFoldLevelBlocks2 L d 2 le_rfl).count .TOFF = 0 :=
        count_wFoldLevelBlocks2 L d .TOFF (fun _ _ _ ↦ rfl) 2 le_rfl
      have hFold : (wFoldLevelBlocks2 L d 2 le_rfl).eval.1 *
          ketMapOp14 (sEncValid2 L) (fun β ↦ XMeasCircuit.ket (wDecAssign2 L (R + 1) hR β)) =
          ketMapOp14 (sEncValid2 L) (fun β ↦ XMeasCircuit.ket (gammaFold2 L d β)) := by
        rw [mul_ketMapOp14]
        refine ketMapOp14_congr fun β hS ↦ ?_
        simpa only [wDecAssign2, pNextOf2, ite_pos2 (bZeroOf2 L β).isLt] using
          wFoldLevelBlocks2_ket hK1 hK5 L d hS 2 le_rfl
      have hUnl2 : ketMapOp14 (sEncValid2 L) (fun β ↦ XMeasCircuit.ket (gammaUnload2 L d 2 0 β)) =
          ketMapOp14 (sEncValid2 L) (fun β ↦ XMeasCircuit.ket (wDecAssign2 L R (by omega) β)) :=
        ketMapOp14_congr fun β _ ↦
          congrArg XMeasCircuit.ket (ite_pos2 (Or.inl (bZeroOf2 L β).isLt))
      exact SubspaceStepV14.seq
        (SubspaceStepV14.seq
          (SubspaceStepV14.of_circuit (wFoldLevelBlocks2 L d 2 le_rfl) hf0 hFold)
          (SubspaceStepV14.congr rfl hUnl2 (wUnloadLevelBlocks2_step v L d 2 le_rfl)))
        (ih (by omega))

private theorem encPow2_step {Var : Type} [Fintype Var] [DecidableEq Var] {K n : ℕ}
    (hK1 : 1 ≤ K) (hK5 : K ≤ 5) (v : Var) (L : StepPow2Layout K n) :
    SubspaceStepV14 v
      (ketMapOp14 (sEncValid2 L) XMeasCircuit.ket)
      (ketMapOp14 (sEncValid2 L) (fun β ↦ XMeasCircuit.ket (encAssign2 L β)))
      (stepOneHotEncPow2Dyn v L) := by
  have hrt0 : (wRoot2LinCirc L ;;ᶜ wTreePrefixLevels2 L K le_rfl).count .TOFF = 0 := by
    rw [Circuit.count_seq, count_wRoot2LinCirc_toff, count_wTreePrefixLevels2_toff]
  have hTree : (wRoot2LinCirc L ;;ᶜ wTreePrefixLevels2 L K le_rfl).eval.1 *
      ketMapOp14 (sEncValid2 L) XMeasCircuit.ket =
      ketMapOp14 (sEncValid2 L) (wShiftVec2 L K le_rfl) := by
    rw [mul_ketMapOp14]
    refine ketMapOp14_congr fun β hS ↦ ?_
    rw [eval_seq_mulVec2, wRoot2LinCirc_ket hK1 hK5 L hS,
      wTreePrefixLevels2_ket L hS K le_rfl]
    dsimp only [wTreeVec2, wShiftVec2]
    refine congrArg (_ • ·) (Finset.sum_congr rfl fun t _ ↦ ?_)
    exact congrArg (fun p ↦ XMeasCircuit.ket (Function.update β (wLeaf2 L (bZeroOf2 L β) p) 1))
      (Fin.ext (by
        dsimp [shiftLeafIdx2]
        simp only [Nat.sub_self, _root_.pow_zero, Nat.mod_one, one_mul, zero_add]))
  have hEnd : ketMapOp14 (sEncValid2 L) (wShiftVec2 L 0 (by omega)) =
      ketMapOp14 (sEncValid2 L) (fun β ↦ XMeasCircuit.ket (encAssign2 L β)) := by
    refine ketMapOp14_congr fun β _ ↦ ?_
    dsimp only [wShiftVec2, encAssign2]
    rw [_root_.pow_zero, one_smul]
    change (∑ t : Fin 1, _) = _
    rw [Fin.sum_univ_one]
    exact congrArg (fun p ↦ XMeasCircuit.ket (Function.update β (wLeaf2 L (bZeroOf2 L β) p) 1))
      (Fin.ext (by dsimp [shiftLeafIdx2]; exact Nat.mod_eq_of_lt (loOf2 L β).isLt))
  exact SubspaceStepV14.congr rfl hEnd
    (SubspaceStepV14.seq (SubspaceStepV14.of_circuit _ hrt0 hTree)
      (wShiftFromDyn2_step hK1 hK5 v L K le_rfl))

private theorem decPow2_step {Var : Type} [Fintype Var] [DecidableEq Var] {K n : ℕ}
    (hK1 : 1 ≤ K) (hK5 : K ≤ 5) (v : Var) (L : StepPow2Layout K n) :
    SubspaceStepV14 v
      (ketMapOp14 (sEncValid2 L) (fun β ↦ XMeasCircuit.ket (encAssign2 L β)))
      (ketMapOp14 (sEncValid2 L) XMeasCircuit.ket)
      (stepOneHotDecPow2Dyn v L) := by
  have hStart : ketMapOp14 (sEncValid2 L) (fun β ↦ XMeasCircuit.ket (wDecAssign2 L K le_rfl β)) =
      ketMapOp14 (sEncValid2 L) (fun β ↦ XMeasCircuit.ket (encAssign2 L β)) :=
    ketMapOp14_congr fun β _ ↦ congrArg
      (fun p ↦ XMeasCircuit.ket (Function.update β (wLeaf2 L (bZeroOf2 L β) p) 1))
      (Fin.ext (Nat.mod_eq_of_lt (loOf2 L β).isLt))
  have hun0 : (wRoot2UninitLinCirc L).count .TOFF = 0 := count_wRoot2UninitLinCirc_toff L
  have hUninit : (wRoot2UninitLinCirc L).eval.1 *
      ketMapOp14 (sEncValid2 L) (fun β ↦ XMeasCircuit.ket (wDecAssign2 L 0 (by omega) β)) =
      ketMapOp14 (sEncValid2 L) XMeasCircuit.ket := by
    rw [mul_ketMapOp14]
    refine ketMapOp14_congr fun β hS ↦ ?_
    have hd0 : wDecAssign2 L 0 (by omega) β =
        Function.update β (wLeaf2 L (bZeroOf2 L β) ⟨0, Nat.two_pow_pos K⟩) 1 :=
      congrArg (fun p ↦ Function.update β (wLeaf2 L (bZeroOf2 L β) p) 1)
        (Fin.ext (by dsimp; omega))
    rw [hd0, wRoot2UninitLinCirc_ket hK1 hK5 L hS]
  exact SubspaceStepV14.congr hStart rfl
    (SubspaceStepV14.seq (wUncompTreeLevels2_step hK1 hK5 v L K le_rfl)
      (SubspaceStepV14.of_circuit _ hun0 hUninit))
/-! ## Section 2B: `0-T` Upward Fast-Zeta ANF Butterfly + `WpZeroSet` Lifting -/

/-- `m`-pair prefix of upward binary fast-zeta stage `d < M` (`CNOT` from `1`-bit to `0`-bit). -/
def zetaPhaseFrom {n : ℕ} (M : ℕ) (rHot : QRegister (2 ^ M) n) (d : Fin M) :
    (m : ℕ) → m ≤ 2 ^ (M - 1) → Circuit n
  | 0, _ => Circuit.identity
  | m + 1, hm =>
      let s : Fin (2 ^ (M - 1)) := ⟨m, hm⟩
      have hne : rHot (insertOneBit2 M d s) ≠ rHot (insertZeroBit2 M d s) :=
        rHot.wires.injective.ne <| Fin.ne_of_val_ne <| by
          have hd := Nat.two_pow_pos d.val
          dsimp [insertOneBit2]; omega
      zetaPhaseFrom M rHot d m (by omega) ;;ᶜ
        Circuit.CNOT (rHot (insertOneBit2 M d s)) (rHot (insertZeroBit2 M d s)) hne

/-- Exact reverse of `zetaPhaseFrom M rHot d m hm`. -/
def zetaPhaseRev {n : ℕ} (M : ℕ) (rHot : QRegister (2 ^ M) n) (d : Fin M) :
    (m : ℕ) → m ≤ 2 ^ (M - 1) → Circuit n
  | 0, _ => Circuit.identity
  | m + 1, hm =>
      let s : Fin (2 ^ (M - 1)) := ⟨m, hm⟩
      have hne : rHot (insertOneBit2 M d s) ≠ rHot (insertZeroBit2 M d s) :=
        rHot.wires.injective.ne <| Fin.ne_of_val_ne <| by
          have hd := Nat.two_pow_pos d.val
          dsimp [insertOneBit2]; omega
      Circuit.CNOT (rHot (insertOneBit2 M d s)) (rHot (insertZeroBit2 M d s)) hne ;;ᶜ
        zetaPhaseRev M rHot d m (by omega)

/-- `R`-stage upward fast-zeta `CNOT` butterfly (`R ≤ M`, `0 T`, `0 TOFF`). -/
def zetaUpPrefixes {n : ℕ} (M : ℕ) (rHot : QRegister (2 ^ M) n) :
    (R : ℕ) → R ≤ M → Circuit n
  | 0, _ => Circuit.identity
  | R + 1, hR =>
      zetaUpPrefixes M rHot R (by omega) ;;ᶜ
        zetaPhaseFrom M rHot ⟨R, hR⟩ (2 ^ (M - 1)) le_rfl

/-- Exact `R`-stage reverse downward fast-zeta `CNOT` butterfly (`R ≤ M`, `0 T`, `0 TOFF`). -/
def zetaDownPrefixes {n : ℕ} (M : ℕ) (rHot : QRegister (2 ^ M) n) :
    (R : ℕ) → R ≤ M → Circuit n
  | 0, _ => Circuit.identity
  | R + 1, hR =>
      zetaPhaseRev M rHot ⟨R, hR⟩ (2 ^ (M - 1)) le_rfl ;;ᶜ
        zetaDownPrefixes M rHot R (by omega)

private theorem count_zetaPhaseFrom {n k : ℕ} (M : ℕ) (rHot : QRegister (2 ^ M) n) (d : Fin M)
    (g : PrimitiveGate k)
    (hCnot : ∀ (x y : Wire n) (h : x ≠ y), (Circuit.CNOT x y h).count g = 0) :
    ∀ (m : ℕ) (hm : m ≤ 2 ^ (M - 1)), (zetaPhaseFrom M rHot d m hm).count g = 0 := by
  intro m hm; induction m with
  | zero => rfl
  | succ m ih => rw [zetaPhaseFrom, Circuit.count_seq, ih (by omega), hCnot, add_zero]

private theorem count_zetaPhaseRev {n k : ℕ} (M : ℕ) (rHot : QRegister (2 ^ M) n) (d : Fin M)
    (g : PrimitiveGate k)
    (hCnot : ∀ (x y : Wire n) (h : x ≠ y), (Circuit.CNOT x y h).count g = 0) :
    ∀ (m : ℕ) (hm : m ≤ 2 ^ (M - 1)), (zetaPhaseRev M rHot d m hm).count g = 0 := by
  intro m hm; induction m with
  | zero => rfl
  | succ m ih => rw [zetaPhaseRev, Circuit.count_seq, hCnot, ih (by omega), add_zero]

private theorem count_zetaUpPrefixes {n k : ℕ} (M : ℕ) (rHot : QRegister (2 ^ M) n)
    (g : PrimitiveGate k)
    (hCnot : ∀ (x y : Wire n) (h : x ≠ y), (Circuit.CNOT x y h).count g = 0) :
    ∀ (R : ℕ) (hR : R ≤ M), (zetaUpPrefixes M rHot R hR).count g = 0 := by
  intro R hR; induction R with
  | zero => rfl
  | succ R ih =>
      rw [zetaUpPrefixes, Circuit.count_seq, ih (by omega),
        count_zetaPhaseFrom M rHot _ g hCnot _ le_rfl, add_zero]

private theorem count_zetaDownPrefixes {n k : ℕ} (M : ℕ) (rHot : QRegister (2 ^ M) n)
    (g : PrimitiveGate k)
    (hCnot : ∀ (x y : Wire n) (h : x ≠ y), (Circuit.CNOT x y h).count g = 0) :
    ∀ (R : ℕ) (hR : R ≤ M), (zetaDownPrefixes M rHot R hR).count g = 0 := by
  intro R hR; induction R with
  | zero => rfl
  | succ R ih =>
      rw [zetaDownPrefixes, Circuit.count_seq,
        count_zetaPhaseRev M rHot _ g hCnot _ le_rfl, ih (by omega), add_zero]

private theorem zetaPhaseRev_mul_from {n : ℕ} (M : ℕ) (rHot : QRegister (2 ^ M) n) (d : Fin M) :
    ∀ (m : ℕ) (hm : m ≤ 2 ^ (M - 1)),
      (zetaPhaseRev M rHot d m hm).eval * (zetaPhaseFrom M rHot d m hm).eval = 1 := by
  intro m hm; induction m with
  | zero => simp [zetaPhaseRev, zetaPhaseFrom]
  | succ m ih =>
      have hne : rHot (insertOneBit2 M d ⟨m, hm⟩) ≠ rHot (insertZeroBit2 M d ⟨m, hm⟩) :=
        rHot.wires.injective.ne <| Fin.ne_of_val_ne <| by
          have hd := Nat.two_pow_pos d.val
          dsimp [insertOneBit2]; omega
      let g := (Circuit.CNOT (rHot (insertOneBit2 M d ⟨m, hm⟩))
        (rHot (insertZeroBit2 M d ⟨m, hm⟩)) hne).eval
      rw [zetaPhaseRev, zetaPhaseFrom, Circuit.eval_seq, Circuit.eval_seq]
      calc ((zetaPhaseRev M rHot d m (by omega)).eval * g) *
              (g * (zetaPhaseFrom M rHot d m (by omega)).eval)
          = (zetaPhaseRev M rHot d m (by omega)).eval *
              (g * g) * (zetaPhaseFrom M rHot d m (by omega)).eval := by
              simp only [mul_assoc]
        _ = (zetaPhaseRev M rHot d m (by omega)).eval *
              (zetaPhaseFrom M rHot d m (by omega)).eval := by
              rw [cnot_eval_mul_self2, mul_one]
        _ = 1 := ih (by omega)

private theorem zetaDown_mul_zetaUp {n : ℕ} (M : ℕ) (rHot : QRegister (2 ^ M) n) :
    ∀ (R : ℕ) (hR : R ≤ M),
      (zetaDownPrefixes M rHot R hR).eval * (zetaUpPrefixes M rHot R hR).eval = 1 := by
  intro R hR; induction R with
  | zero => simp [zetaDownPrefixes, zetaUpPrefixes]
  | succ R ih =>
      rw [zetaDownPrefixes, zetaUpPrefixes, Circuit.eval_seq, Circuit.eval_seq]
      calc ((zetaDownPrefixes M rHot R (by omega)).eval *
              (zetaPhaseRev M rHot ⟨R, hR⟩ _ le_rfl).eval) *
            ((zetaPhaseFrom M rHot ⟨R, hR⟩ _ le_rfl).eval *
              (zetaUpPrefixes M rHot R (by omega)).eval)
          = (zetaDownPrefixes M rHot R (by omega)).eval *
              ((zetaPhaseRev M rHot ⟨R, hR⟩ _ le_rfl).eval *
                (zetaPhaseFrom M rHot ⟨R, hR⟩ _ le_rfl).eval) *
              (zetaUpPrefixes M rHot R (by omega)).eval := by
              simp only [mul_assoc]
        _ = (zetaDownPrefixes M rHot R (by omega)).eval *
              (zetaUpPrefixes M rHot R (by omega)).eval := by
              rw [zetaPhaseRev_mul_from, mul_one]
        _ = 1 := ih (by omega)

/-- Computable `m`-pair vector step of upward fast-zeta stage `d < M`. -/
private def zetaPhaseStepVec (M : ℕ) (d : Fin M) (x : Fin (2 ^ M) → ZMod 2) :
    (m : ℕ) → m ≤ 2 ^ (M - 1) → Fin (2 ^ M) → ZMod 2
  | 0, _ => x
  | m + 1, hm =>
      let s : Fin (2 ^ (M - 1)) := ⟨m, hm⟩
      let y := zetaPhaseStepVec M d x m (by omega)
      Function.update y (insertZeroBit2 M d s)
        (y (insertZeroBit2 M d s) + y (insertOneBit2 M d s))

/-- Computable `R`-stage upward fast-zeta transform on `Fin (2 ^ M) → ZMod 2`. -/
private def zetaUpVec (M : ℕ) (x : Fin (2 ^ M) → ZMod 2) :
    (R : ℕ) → R ≤ M → Fin (2 ^ M) → ZMod 2
  | 0, _ => x
  | R + 1, hR =>
      zetaPhaseStepVec M ⟨R, hR⟩ (zetaUpVec M x R (by omega)) (2 ^ (M - 1)) le_rfl

private theorem update_writeReg {G n : ℕ} (β : BitAssignment n) (r : QRegister G n)
    (y : Fin G → ZMod 2) (i₀ : Fin G) (v : ZMod 2) :
    Function.update (CoherentAlias.writeReg β r y) (r i₀) v =
      CoherentAlias.writeReg β r (Function.update y i₀ v) := by
  funext w
  by_cases hw : w ∈ Set.range r.wires
  · obtain ⟨g, rfl⟩ := hw
    rw [CoherentAlias.writeReg_apply_reg]
    by_cases hg : g = i₀
    · subst hg; simp
    · rw [Function.update_of_ne (r.wires.injective.ne hg), Function.update_of_ne hg,
        CoherentAlias.writeReg_apply_reg]
  · have hne : w ≠ r i₀ := fun h ↦ hw ⟨i₀, h.symm⟩
    rw [Function.update_of_ne hne, CoherentAlias.writeReg_apply_of_not_mem _ _ _ _ hw,
      CoherentAlias.writeReg_apply_of_not_mem _ _ _ _ hw]

private theorem zetaPhaseFrom_ket {n : ℕ} (M : ℕ) (rHot : QRegister (2 ^ M) n) (d : Fin M)
    (β : BitAssignment n) (x : Fin (2 ^ M) → ZMod 2) :
    ∀ (m : ℕ) (hm : m ≤ 2 ^ (M - 1)),
      (zetaPhaseFrom M rHot d m hm).eval.1.mulVec
          (XMeasCircuit.ket (CoherentAlias.writeReg β rHot x)) =
        XMeasCircuit.ket (CoherentAlias.writeReg β rHot (zetaPhaseStepVec M d x m hm)) := by
  intro m hm; induction m with
  | zero =>
      rw [zetaPhaseFrom, zetaPhaseStepVec, Circuit.eval_identity, Submonoid.coe_one,
        Matrix.one_mulVec]
  | succ m ih =>
      rw [zetaPhaseFrom, eval_seq_mulVec2, ih (by omega), ket_CNOT2,
        CoherentAlias.writeReg_apply_reg, CoherentAlias.writeReg_apply_reg, update_writeReg]
      rfl

private theorem zetaUpPrefixes_ket {n : ℕ} (M : ℕ) (rHot : QRegister (2 ^ M) n)
    (β : BitAssignment n) (x : Fin (2 ^ M) → ZMod 2) :
    ∀ (R : ℕ) (hR : R ≤ M),
      (zetaUpPrefixes M rHot R hR).eval.1.mulVec
          (XMeasCircuit.ket (CoherentAlias.writeReg β rHot x)) =
        XMeasCircuit.ket (CoherentAlias.writeReg β rHot (zetaUpVec M x R hR)) := by
  intro R hR; induction R with
  | zero =>
      rw [zetaUpPrefixes, zetaUpVec, Circuit.eval_identity, Submonoid.coe_one,
        Matrix.one_mulVec]
  | succ R ih =>
      rw [zetaUpPrefixes, eval_seq_mulVec2, ih (by omega), zetaPhaseFrom_ket]
      rfl

private theorem zetaPhaseStepVec_apply {M : ℕ} (hM1 : 1 ≤ M) (hM5 : M ≤ 5)
    (d : Fin M) (x : Fin (2 ^ M) → ZMod 2) :
    ∀ (m : ℕ) (hm : m ≤ 2 ^ (M - 1)) (p : Fin (2 ^ M)),
      zetaPhaseStepVec M d x m hm p =
        if p.val / 2 ^ d.val % 2 = 0 ∧ (shrinkBit2 M d p).val < m then
          x p + x (flipLeafBit2 M d p)
        else x p := by
  intro m; induction m with
  | zero => intro _ _; simp [zetaPhaseStepVec]
  | succ m ih =>
      intro hm p
      let s : Fin (2 ^ (M - 1)) := ⟨m, hm⟩
      dsimp only [zetaPhaseStepVec]
      by_cases hp : p = insertZeroBit2 M d s
      · subst hp
        have hdiv0 := insertZeroBit2_div_mod hM1 hM5 d s
        have hsh0 := shrinkBit2_insertZero hM1 hM5 d s
        have hdiv1 := insertOneBit2_div_mod hM1 hM5 d s
        have hfl0 := flipLeafBit2_insertZero hM1 hM5 d s
        rw [Function.update_self, ih (by omega) (insertZeroBit2 M d s),
          ih (by omega) (insertOneBit2 M d s), hsh0, hfl0,
          ite_neg2 (fun h ↦ Nat.lt_irrefl m h.2),
          ite_neg2 (fun h ↦ by rw [hdiv1] at h; exact absurd h.1 (by decide)),
          ite_pos2 ⟨hdiv0, Nat.lt_succ_self m⟩]
      · rw [Function.update_of_ne hp, ih (by omega) p]
        by_cases hprev : p.val / 2 ^ d.val % 2 = 0 ∧ (shrinkBit2 M d p).val < m
        · rw [ite_pos2 hprev, ite_pos2 ⟨hprev.1, by omega⟩]
        · have hprev' : ¬(p.val / 2 ^ d.val % 2 = 0 ∧ (shrinkBit2 M d p).val < m + 1) := by
            rintro ⟨h0, hlt⟩
            by_cases heq : (shrinkBit2 M d p).val = m
            · have hsEq : shrinkBit2 M d p = s := Fin.ext heq
              have hpEq : insertZeroBit2 M d s = p := by
                rw [← hsEq]; exact (insert_of_div_mod2 hM1 hM5 d p).1 h0
              exact hp hpEq.symm
            · exact hprev ⟨h0, by omega⟩
          rw [ite_neg2 hprev, ite_neg2 hprev']

/-- Pointwise depth-`R` upward fast-zeta transform on `Fin (2 ^ M) → ZMod 2`. -/
private def zetaFastUpVec (M : ℕ) (x : Fin (2 ^ M) → ZMod 2) :
    (R : ℕ) → R ≤ M → Fin (2 ^ M) → ZMod 2
  | 0, _ => x
  | R + 1, hR =>
      let y := zetaFastUpVec M x R (by omega)
      fun p ↦ if p.val / 2 ^ R % 2 = 0 then y p + y (flipLeafBit2 M ⟨R, hR⟩ p) else y p

private theorem zetaUpVec_eq_fast {M : ℕ} (hM1 : 1 ≤ M) (hM5 : M ≤ 5)
    (x : Fin (2 ^ M) → ZMod 2) :
    ∀ (R : ℕ) (hR : R ≤ M), zetaUpVec M x R hR = zetaFastUpVec M x R hR := by
  intro R hR; induction R with
  | zero => rfl
  | succ R ih =>
      funext p
      rw [zetaUpVec, ih (by omega), zetaPhaseStepVec_apply hM1 hM5 ⟨R, hR⟩ _ _ le_rfl p]
      dsimp only [zetaFastUpVec]
      by_cases hb : p.val / 2 ^ R % 2 = 0
      · rw [ite_pos2 ⟨hb, (shrinkBit2 M ⟨R, hR⟩ p).isLt⟩, ite_pos2 hb]
      · rw [ite_neg2 (fun h ↦ hb h.1), ite_neg2 hb]

private theorem zetaFastUpVec_oneHot_eq_monoEval {M : ℕ} (hM1 : 1 ≤ M) (hM5 : M ≤ 5) :
    ∀ (g₀ m : Fin (2 ^ M)),
      zetaFastUpVec M (fun g ↦ if g = g₀ then 1 else 0) M le_rfl m =
        SelectSwapQROM.monoEval M (basisBits M g₀) m := by
  rcases k15_cases hM1 hM5 with rfl | rfl | rfl | rfl | rfl <;> decide

private theorem zetaUpVec_oneHot_eq_monoEval {M : ℕ} (hM1 : 1 ≤ M) (hM5 : M ≤ 5) :
    ∀ (g₀ m : Fin (2 ^ M)),
      zetaUpVec M (fun g ↦ if g = g₀ then 1 else 0) M le_rfl m =
        SelectSwapQROM.monoEval M (basisBits M g₀) m := by
  intro g₀ m
  rw [zetaUpVec_eq_fast hM1 hM5, zetaFastUpVec_oneHot_eq_monoEval hM1 hM5]

/-- `4 * (2 ^ K - 1)` `T`, `0-TOFF` upward fast-zeta ANF encoder populating `L.rHot m`
with `SelectSwapQROM.monoEval (K + 1) (fun i ↦ β (L.rCtx i)) m`. -/
def stepAnfEncPow2Dyn {Var : Type} {K n : ℕ} (v : Var) (L : StepPow2Layout K n) :
    DynamicCircuit Var n :=
  .seq (stepOneHotEncPow2Dyn v L) (.circuit (zetaUpPrefixes (K + 1) L.rHot (K + 1) le_rfl))

/-- `0-T`, `0-TOFF` downward fast-zeta + MBU ANF decoder. -/
def stepAnfDecPow2Dyn {Var : Type} {K n : ℕ} (v : Var) (L : StepPow2Layout K n) :
    DynamicCircuit Var n :=
  .seq (.circuit (zetaDownPrefixes (K + 1) L.rHot (K + 1) le_rfl)) (stepOneHotDecPow2Dyn v L)

/-- `4 * (2 ^ K - 1) + mid.count .T` `T`, `mid.count .TOFF` `TOFF` fast-zeta ANF wrapper. -/
def withStepAnfPow2Dyn {Var : Type} {K n : ℕ} (v : Var) (L : StepPow2Layout K n)
    (mid : DynamicCircuit Var n) : DynamicCircuit Var n :=
  .seq (stepAnfEncPow2Dyn v L) (.seq mid (stepAnfDecPow2Dyn v L))

@[simp] theorem count_stepAnfEncPow2Dyn_toff {Var : Type} {K n : ℕ} (v : Var)
    (L : StepPow2Layout K n) : (stepAnfEncPow2Dyn v L).count .TOFF = 0 := by
  have hz : (zetaUpPrefixes (K + 1) L.rHot (K + 1) le_rfl).count .TOFF = 0 :=
    count_zetaUpPrefixes _ _ .TOFF (fun _ _ _ ↦ rfl) _ le_rfl
  simp [stepAnfEncPow2Dyn, DynamicCircuit.count, hz]

@[simp] theorem count_stepAnfEncPow2Dyn_t {Var : Type} {K n : ℕ} (v : Var)
    (L : StepPow2Layout K n) :
    (stepAnfEncPow2Dyn v L).count .T = 4 * (2 ^ K - 1) := by
  have hz : (zetaUpPrefixes (K + 1) L.rHot (K + 1) le_rfl).count .T = 0 :=
    count_zetaUpPrefixes _ _ .T (fun _ _ _ ↦ rfl) _ le_rfl
  simp [stepAnfEncPow2Dyn, DynamicCircuit.count, hz]

@[simp] theorem count_stepAnfDecPow2Dyn_toff {Var : Type} {K n : ℕ} (v : Var)
    (L : StepPow2Layout K n) : (stepAnfDecPow2Dyn v L).count .TOFF = 0 := by
  have hz : (zetaDownPrefixes (K + 1) L.rHot (K + 1) le_rfl).count .TOFF = 0 :=
    count_zetaDownPrefixes _ _ .TOFF (fun _ _ _ ↦ rfl) _ le_rfl
  simp [stepAnfDecPow2Dyn, DynamicCircuit.count, hz]

@[simp] theorem count_stepAnfDecPow2Dyn_t {Var : Type} {K n : ℕ} (v : Var)
    (L : StepPow2Layout K n) : (stepAnfDecPow2Dyn v L).count .T = 0 := by
  have hz : (zetaDownPrefixes (K + 1) L.rHot (K + 1) le_rfl).count .T = 0 :=
    count_zetaDownPrefixes _ _ .T (fun _ _ _ ↦ rfl) _ le_rfl
  simp [stepAnfDecPow2Dyn, DynamicCircuit.count, hz]

@[simp] theorem count_withStepAnfPow2Dyn_toff {Var : Type} {K n : ℕ} (v : Var)
    (L : StepPow2Layout K n) (mid : DynamicCircuit Var n) :
    (withStepAnfPow2Dyn v L mid).count .TOFF = mid.count .TOFF := by
  simp [withStepAnfPow2Dyn, DynamicCircuit.count]

@[simp] theorem count_withStepAnfPow2Dyn_t {Var : Type} {K n : ℕ} (v : Var)
    (L : StepPow2Layout K n) (mid : DynamicCircuit Var n) :
    (withStepAnfPow2Dyn v L mid).count .T = 4 * (2 ^ K - 1) + mid.count .T := by
  simp [withStepAnfPow2Dyn, DynamicCircuit.count]

/-- ANF-populated bit assignment writing `monoEval (K + 1) (fun i ↦ β (L.rCtx i))` to `L.rHot`. -/
noncomputable def anfEncAssign2 {K n : ℕ} (L : StepPow2Layout K n)
    (β : BitAssignment n) : BitAssignment n :=
  CoherentAlias.writeReg β L.rHot
    (fun m ↦ SelectSwapQROM.monoEval (K + 1) (fun i ↦ β (L.rCtx i)) m)

theorem anfEncAssign2_apply_hot {K n : ℕ} (L : StepPow2Layout K n) (β : BitAssignment n)
    (m : Fin (2 ^ (K + 1))) :
    anfEncAssign2 L β (L.rHot m) =
      SelectSwapQROM.monoEval (K + 1) (fun i ↦ β (L.rCtx i)) m :=
  CoherentAlias.writeReg_apply_reg β L.rHot _ m

theorem anfEncAssign2_apply_reg {K n : ℕ} (L : StepPow2Layout K n) (β : BitAssignment n)
    (m : Fin (2 ^ (K + 1))) :
    anfEncAssign2 L β (L.rHot m) =
      SelectSwapQROM.monoEval (K + 1) (fun i ↦ β (L.rCtx i)) m :=
  anfEncAssign2_apply_hot L β m

theorem anfEncAssign2_apply_of_not_mem {K n : ℕ} (L : StepPow2Layout K n) (β : BitAssignment n)
    {w : Wire n} (hw : w ∉ L.rHot.image) :
    anfEncAssign2 L β w = β w :=
  CoherentAlias.writeReg_apply_of_not_mem β L.rHot _ w
    (fun ⟨g, hg⟩ ↦ hw ((QRegister.mem_image L.rHot w).mpr ⟨g, hg⟩))

private theorem encAssign2_eq_writeReg_oneHot {K n : ℕ} (L : StepPow2Layout K n)
    {β : BitAssignment n} (hS : sEncValid2 L β) :
    encAssign2 L β = CoherentAlias.writeReg β L.rHot
      (fun g ↦ if g = CircuitModular.UnsignedGivens.localIdx L.rCtx β then 1 else 0) := by
  funext w
  dsimp only [encAssign2]
  rw [wLeaf2_bZero_lo]
  by_cases hw : w ∈ Set.range L.rHot.wires
  · obtain ⟨g, rfl⟩ := hw
    rw [CoherentAlias.writeReg_apply_reg]
    by_cases hg : g = CircuitModular.UnsignedGivens.localIdx L.rCtx β
    · subst hg; simp
    · rw [Function.update_of_ne (L.rHot.wires.injective.ne hg), hS.1 g, ite_neg2 hg]
  · have hne : w ≠ L.rHot (CircuitModular.UnsignedGivens.localIdx L.rCtx β) := fun h ↦ hw ⟨_,
      h.symm⟩
    rw [Function.update_of_ne hne, CoherentAlias.writeReg_apply_of_not_mem _ _ _ _ hw]

private theorem zetaUp_encAssign2_ket {K n : ℕ} (hK4 : K ≤ 4) (L : StepPow2Layout K n)
    {β : BitAssignment n} (hS : sEncValid2 L β) :
    (zetaUpPrefixes (K + 1) L.rHot (K + 1) le_rfl).eval.1.mulVec
        (XMeasCircuit.ket (encAssign2 L β)) =
      XMeasCircuit.ket (anfEncAssign2 L β) := by
  rw [encAssign2_eq_writeReg_oneHot L hS, zetaUpPrefixes_ket]
  congr 1; congr 1; funext m
  rw [zetaUpVec_oneHot_eq_monoEval (by omega) (by omega) _ m]
  exact congrArg (fun f ↦ SelectSwapQROM.monoEval (K + 1) f m)
    (CircuitModular.UnsignedGivens.basisBits_symm_eq (fun i ↦ β (L.rCtx i)))

private theorem anfEncPow2_step {Var : Type} [Fintype Var] [DecidableEq Var] {K n : ℕ}
    (hK1 : 1 ≤ K) (hK4 : K ≤ 4) (v : Var) (L : StepPow2Layout K n) :
    SubspaceStepV14 v
      (ketMapOp14 (sEncValid2 L) XMeasCircuit.ket)
      (ketMapOp14 (sEncValid2 L) (fun β ↦ XMeasCircuit.ket (anfEncAssign2 L β)))
      (stepAnfEncPow2Dyn v L) := by
  have hz0 : (zetaUpPrefixes (K + 1) L.rHot (K + 1) le_rfl).count .TOFF = 0 :=
    count_zetaUpPrefixes _ _ .TOFF (fun _ _ _ ↦ rfl) _ le_rfl
  refine SubspaceStepV14.seq (encPow2_step hK1 (by omega) v L)
    (SubspaceStepV14.of_circuit _ hz0 ?_)
  rw [mul_ketMapOp14]
  exact ketMapOp14_congr fun β hS ↦ zetaUp_encAssign2_ket hK4 L hS

private theorem anfDecPow2_step {Var : Type} [Fintype Var] [DecidableEq Var] {K n : ℕ}
    (hK1 : 1 ≤ K) (hK4 : K ≤ 4) (v : Var) (L : StepPow2Layout K n) :
    SubspaceStepV14 v
      (ketMapOp14 (sEncValid2 L) (fun β ↦ XMeasCircuit.ket (anfEncAssign2 L β)))
      (ketMapOp14 (sEncValid2 L) XMeasCircuit.ket)
      (stepAnfDecPow2Dyn v L) := by
  have hz0 : (zetaDownPrefixes (K + 1) L.rHot (K + 1) le_rfl).count .TOFF = 0 :=
    count_zetaDownPrefixes _ _ .TOFF (fun _ _ _ ↦ rfl) _ le_rfl
  refine SubspaceStepV14.seq (SubspaceStepV14.of_circuit _ hz0 ?_)
    (decPow2_step hK1 (by omega) v L)
  rw [mul_ketMapOp14]
  refine ketMapOp14_congr fun β hS ↦ ?_
  have hm := congrArg Subtype.val (zetaDown_mul_zetaUp (K + 1) L.rHot (K + 1) le_rfl)
  rw [← zetaUp_encAssign2_ket hK4 L hS, Matrix.mulVec_mulVec]
  simpa only [Submonoid.coe_mul, Submonoid.coe_one, Matrix.one_mulVec] using
    congrArg (fun M : Operator (2 ^ n) ↦ M.mulVec _) hm

/-- Clean-finset `wp` specification (`0 TOFF`, `v`-invariance, and `restrictZeroSet` match). -/
def WpZeroSet {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    (v : Var) (S : Finset (Wire n)) (U : Unitary (2 ^ n)) (d : DynamicCircuit Var n) : Prop :=
  d.count .TOFF = 0 ∧
    (∀ Θ : QCAssertion Var (2 ^ n), IsVInv14 v Θ → IsVInv14 v (wp d.compile Θ)) ∧
    (∀ Θ : QCAssertion Var (2 ^ n), IsVInv14 v Θ →
      SelectSwapQROM.restrictZeroSet (wp d.compile Θ) S =
        SelectSwapQROM.restrictZeroSet (qcWpQAssign U Θ) S)

theorem WpZeroSet.of_cleanRealizesSet {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    {v : Var} {S : Finset (Wire n)} {U : Unitary (2 ^ n)} {d : DynamicCircuit Var n}
    (h : SelectSwapQROM.CleanRealizesSet v S U d) : WpZeroSet v S U d :=
  ⟨h.1, h.2.1, h.2.2.1⟩

theorem WpZeroSet.to_cleanRealizes {Var : Type} [Fintype Var] [DecidableEq Var] {n mAct s : ℕ}
    {v : Var} {rAct : QRegister mAct n} {rScr : QRegister s n}
    (hdisj : rAct.DisjointWires rScr) {U : Unitary (2 ^ mAct)} {d : DynamicCircuit Var n}
    (h : WpZeroSet v rScr.image (rAct.embedUnitary U) d) :
    CleanDyn.CleanRealizes v rAct rScr U d := by
  have himg (Ψ : Store Var → Observable (Fin (2 ^ n))) :
      restrictAssertionToZeroAncilla Ψ rScr = SelectSwapQROM.restrictZeroSet Ψ rScr.image := by
    funext σ; apply Subtype.ext
    rw [restrictAssertionToZeroAncilla_coe, SelectSwapQROM.restrictZeroSet_coe,
      SelectSwapQROM.basisOutcomeProjector_zero_eq_zeroProjOn]
  refine CleanDyn.CleanRealizes.mk_of_disjoint v rAct rScr hdisj U d h.1 h.2.1 fun Θ hΘ ↦ ?_
  rw [himg, himg]; exact h.2.2 Θ hΘ

theorem WpZeroSet.of_circuit {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    (v : Var) (S : Finset (Wire n)) (c : Circuit n) (hc0 : c.count .TOFF = 0) :
    WpZeroSet v S c.eval (.circuit c) := by
  have hwp (Θ : QCAssertion Var (2 ^ n)) :
      wp (DynamicCircuit.circuit c).compile Θ = qcWpQAssign c.eval Θ := by
    rw [DynamicCircuit.compile_circuit, DynamicCircuit.qc_wp_circuit_compile (Var := Var)]
  refine ⟨hc0, fun Θ hΘ σ val ↦ ?_, fun Θ _ ↦ by rw [hwp]⟩
  rw [hwp]; simp only [qcWpQAssign, hΘ σ val]

theorem WpZeroSet.congr_unitary {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    {v : Var} {S : Finset (Wire n)} {U₁ U₂ : Unitary (2 ^ n)} {d : DynamicCircuit Var n}
    (h : WpZeroSet v S U₁ d)
    (hKet : ∀ β : BitAssignment n, (∀ w ∈ S, β w = 0) →
      U₁.1.mulVec (XMeasCircuit.ket β) = U₂.1.mulVec (XMeasCircuit.ket β)) :
    WpZeroSet v S U₂ d := by
  let P_S := SelectSwapQROM.zeroProjOn S
  have hPSH : P_Sᴴ = P_S := SelectSwapQROM.zeroProjOn_conjTranspose S
  have hUPS : U₁.1 * P_S = U₂.1 * P_S := by
    classical
    refine XMeasCircuit.matrix_ext_ket fun β ↦ ?_
    have hk : XMeasCircuit.ket β = SelectSwapQROM.ket β := rfl
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hk,
      SelectSwapQROM.zeroProjOn_mulVec_ket]
    split_ifs with h0
    · exact hKet β h0
    · simp only [Matrix.mulVec_zero]
  refine ⟨h.1, h.2.1, fun Θ hΘ ↦ (h.2.2 Θ hΘ).trans ?_⟩
  funext σ; apply Subtype.ext; apply HermitianMat.ext
  simp only [SelectSwapQROM.restrictZeroSet_coe, qcWpQAssign, qcQAssignObsMap,
    Observable.conj_coe, HermitianMat.conj_apply_mat, Unitary.coe_star,
    Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose,
    SelectSwapQROM.zeroProjOn_conjTranspose]
  change P_S * (U₁.1ᴴ * (Θ σ).1.1 * U₁.1) * P_S = P_S * (U₂.1ᴴ * (Θ σ).1.1 * U₂.1) * P_S
  calc P_S * (U₁.1ᴴ * (Θ σ).1.1 * U₁.1) * P_S
      = (U₁.1 * P_S)ᴴ * (Θ σ).1.1 * (U₁.1 * P_S) := by
          rw [Matrix.conjTranspose_mul U₁.1 P_S, hPSH]; simp only [Matrix.mul_assoc]
    _ = (U₂.1 * P_S)ᴴ * (Θ σ).1.1 * (U₂.1 * P_S) := by rw [hUPS]
    _ = P_S * (U₂.1ᴴ * (Θ σ).1.1 * U₂.1) * P_S := by
          rw [Matrix.conjTranspose_mul U₂.1 P_S, hPSH]; simp only [Matrix.mul_assoc]

private theorem restrictZeroSet_mat {Var : Type} [Fintype Var] {n : ℕ}
    (M : QCAssertion Var (2 ^ n)) (S : Finset (Wire n)) (σ : Store Var) :
    (SelectSwapQROM.restrictZeroSet M S σ).1.1 =
      SelectSwapQROM.zeroProjOn S * (M σ).1.1 * SelectSwapQROM.zeroProjOn S := by
  have h : ((M σ).1.conj (SelectSwapQROM.zeroProjOn S)).1 =
      SelectSwapQROM.zeroProjOn S * (M σ).1.1 * SelectSwapQROM.zeroProjOn S := by
    simp [SelectSwapQROM.zeroProjOn_conjTranspose]
  exact (congrArg Subtype.val (SelectSwapQROM.restrictZeroSet_coe M S σ)).trans h

private theorem wp_qAssign_mat {Var : Type} [Fintype Var] {n : ℕ}
    (U : Unitary (2 ^ n)) (Θ : QCAssertion Var (2 ^ n)) (σ : Store Var) :
    (qcWpQAssign U Θ σ).1.1 = U.1ᴴ * (Θ σ).1.1 * U.1 := by
  simp [qcWpQAssign, qcQAssignObsMap, Matrix.star_eq_conjTranspose]

theorem WpZeroSet.seq_diag_left {Var : Type} [Fintype Var] [DecidableEq Var]
    {n : ℕ} [NeZero (2 ^ n)] {v : Var} {S : Finset (Wire n)} {φ : BitAssignment n → ZMod 2}
    {U₂ : Unitary (2 ^ n)} {d₁ d₂ : DynamicCircuit Var n}
    (h₁ : WpZeroSet v S (diagKetUnitary φ) d₁) (h₂ : WpZeroSet v S U₂ d₂) :
    WpZeroSet v S (U₂ * diagKetUnitary φ) (.seq d₁ d₂) := by
  let U₁ := diagKetUnitary φ
  let P_S := SelectSwapQROM.zeroProjOn S
  have hPSH : P_Sᴴ = P_S := SelectSwapQROM.zeroProjOn_conjTranspose S
  have hPres : P_S * (U₁.1 * P_S) = U₁.1 * P_S := by
    classical
    refine SelectSwapQROM.matrix_ext_ket fun β ↦ ?_
    simp only [← Matrix.mulVec_mulVec, P_S, SelectSwapQROM.zeroProjOn_mulVec_ket]
    split_ifs with h0
    · rw [diagKetUnitary_mulVec_ket, Matrix.mulVec_smul, SelectSwapQROM.zeroProjOn_mulVec_ket,
        ite_pos2 h0]
    · simp only [Matrix.mulVec_zero]
  refine ⟨by simp [DynamicCircuit.count, h₁.1, h₂.1], fun Θ hΘ ↦ ?_, fun Θ hΘ ↦ ?_⟩
  · have hSeq : wp (d₁.seq d₂).compile Θ = wp d₁.compile (wp d₂.compile Θ) := by
      rw [DynamicCircuit.compile_seq, wp_qSeq]
    rw [hSeq]; exact h₁.2.1 _ (h₂.2.1 Θ hΘ)
  · funext σ; apply Subtype.ext; apply Subtype.ext
    let Ψ₂ := wp d₂.compile Θ
    have hΨ₂ : IsVInv14 v Ψ₂ := h₂.2.1 Θ hΘ
    have hSeq : wp (d₁.seq d₂).compile Θ = wp d₁.compile Ψ₂ := by
      simp [Ψ₂, DynamicCircuit.compile_seq, wp_qSeq]
    have hM₁ : P_S * (wp d₁.compile Ψ₂ σ).1.1 * P_S =
        P_S * (U₁.1ᴴ * (Ψ₂ σ).1.1 * U₁.1) * P_S := by
      have hv := congrArg (fun x : Observable (Fin (2 ^ n)) ↦ x.1.1)
        (congrFun (h₁.2.2 Ψ₂ hΨ₂) σ)
      rwa [restrictZeroSet_mat, restrictZeroSet_mat, wp_qAssign_mat] at hv
    have hM₂ : P_S * (Ψ₂ σ).1.1 * P_S = P_S * (U₂.1ᴴ * (Θ σ).1.1 * U₂.1) * P_S := by
      have hv := congrArg (fun x : Observable (Fin (2 ^ n)) ↦ x.1.1)
        (congrFun (h₂.2.2 Θ hΘ) σ)
      rwa [restrictZeroSet_mat, restrictZeroSet_mat, wp_qAssign_mat] at hv
    rw [hSeq, restrictZeroSet_mat, restrictZeroSet_mat, wp_qAssign_mat]
    change P_S * (wp d₁.compile Ψ₂ σ).1.1 * P_S =
      P_S * ((U₂.1 * U₁.1)ᴴ * (Θ σ).1.1 * (U₂.1 * U₁.1)) * P_S
    calc P_S * (wp d₁.compile Ψ₂ σ).1.1 * P_S
        = (P_S * (U₁.1 * P_S))ᴴ * (Ψ₂ σ).1.1 * (P_S * (U₁.1 * P_S)) := by
            rw [hM₁, hPres, Matrix.conjTranspose_mul U₁.1 P_S, hPSH]; simp only [Matrix.mul_assoc]
      _ = (U₁.1 * P_S)ᴴ * (P_S * (Ψ₂ σ).1.1 * P_S) * (U₁.1 * P_S) := by
            rw [Matrix.conjTranspose_mul P_S (U₁.1 * P_S), hPSH]; simp only [Matrix.mul_assoc]
      _ = (U₁.1 * P_S)ᴴ * (P_S * (U₂.1ᴴ * (Θ σ).1.1 * U₂.1) * P_S) * (U₁.1 * P_S) := by rw [hM₂]
      _ = (P_S * (U₁.1 * P_S))ᴴ * (U₂.1ᴴ * (Θ σ).1.1 * U₂.1) * (P_S * (U₁.1 * P_S)) := by
            rw [Matrix.conjTranspose_mul P_S (U₁.1 * P_S), hPSH]; simp only [Matrix.mul_assoc]
      _ = P_S * ((U₂.1 * U₁.1)ᴴ * (Θ σ).1.1 * (U₂.1 * U₁.1)) * P_S := by
            rw [hPres, Matrix.conjTranspose_mul U₁.1 P_S, Matrix.conjTranspose_mul U₂.1 U₁.1, hPSH]
            simp only [Matrix.mul_assoc]

/-- Generic subspace-sandwich lifting theorem for `WpZeroSet`. -/
private theorem WpZeroSet.of_subspace_sandwich {Var : Type} [Fintype Var] [DecidableEq Var]
    {n : ℕ} {v : Var} (S_enc : BitAssignment n → Prop)
    (eAssign : BitAssignment n → BitAssignment n)
    (S_hot S_clean : Finset (Wire n))
    (G W : Unitary (2 ^ n))
    (enc mid dec : DynamicCircuit Var n)
    (hEnc : SubspaceStepV14 v (ketMapOp14 S_enc XMeasCircuit.ket)
      (ketMapOp14 S_enc (fun β ↦ XMeasCircuit.ket (eAssign β))) enc)
    (hDec : SubspaceStepV14 v (ketMapOp14 S_enc (fun β ↦ XMeasCircuit.ket (eAssign β)))
      (ketMapOp14 S_enc XMeasCircuit.ket) dec)
    (hValid : ∀ β, (∀ w ∈ S_hot ∪ S_clean, β w = 0) → S_enc β)
    (hCleanE : ∀ β, (∀ w ∈ S_hot ∪ S_clean, β w = 0) → ∀ w ∈ S_clean, eAssign β w = 0)
    (hMid : WpZeroSet v S_clean W mid)
    (hGP : ∀ β, (∀ w ∈ S_hot ∪ S_clean, β w = 0) →
      (ketMapOp14 S_enc XMeasCircuit.ket).mulVec (G.1.mulVec (XMeasCircuit.ket β)) =
        G.1.mulVec (XMeasCircuit.ket β))
    (hInter : ∀ β, (∀ w ∈ S_hot ∪ S_clean, β w = 0) →
      (ketMapOp14 S_enc (fun γ ↦ XMeasCircuit.ket (eAssign γ))).mulVec
        (G.1.mulVec (XMeasCircuit.ket β)) = W.1.mulVec (XMeasCircuit.ket (eAssign β))) :
    WpZeroSet v (S_hot ∪ S_clean) G (.seq enc (.seq mid dec)) := by
  classical
  let P_out := SelectSwapQROM.zeroProjOn (S_hot ∪ S_clean)
  let P_S := SelectSwapQROM.zeroProjOn S_clean
  let P_enc := ketMapOp14 S_enc XMeasCircuit.ket
  let E_enc := ketMapOp14 S_enc (fun β ↦ XMeasCircuit.ket (eAssign β))
  have hPoutH : P_outᴴ = P_out := SelectSwapQROM.zeroProjOn_conjTranspose _
  have hPSH : P_Sᴴ = P_S := SelectSwapQROM.zeroProjOn_conjTranspose _
  have hket (γ : BitAssignment n) : XMeasCircuit.ket γ = SelectSwapQROM.ket γ := rfl
  have hPencOut : P_enc * P_out = P_out := by
    refine XMeasCircuit.matrix_ext_ket fun β ↦ ?_
    rw [← Matrix.mulVec_mulVec, hket, SelectSwapQROM.zeroProjOn_mulVec_ket]
    split_ifs with h0
    · rw [← hket, ketMapOp14_mulVec_ket, ite_pos2 (hValid β h0)]
    · exact Matrix.mulVec_zero _
  have hPSEnc : P_S * (E_enc * P_out) = E_enc * P_out := by
    refine XMeasCircuit.matrix_ext_ket fun β ↦ ?_
    simp only [← Matrix.mulVec_mulVec]
    rw [hket β, SelectSwapQROM.zeroProjOn_mulVec_ket]
    split_ifs with h0
    · rw [← hket β, ketMapOp14_mulVec_ket, ite_pos2 (hValid β h0),
        hket (eAssign β), SelectSwapQROM.zeroProjOn_mulVec_ket, ite_pos2 (hCleanE β h0)]
    · simp only [Matrix.mulVec_zero]
  have hGP_mat : P_enc * (G.1 * P_out) = G.1 * P_out := by
    refine XMeasCircuit.matrix_ext_ket fun β ↦ ?_
    simp only [← Matrix.mulVec_mulVec]
    rw [hket β, SelectSwapQROM.zeroProjOn_mulVec_ket]
    split_ifs with h0
    · exact hGP β h0
    · simp only [Matrix.mulVec_zero]
  have hInter_mat : E_enc * (G.1 * P_out) = W.1 * (P_S * (E_enc * P_out)) := by
    rw [hPSEnc]
    refine XMeasCircuit.matrix_ext_ket fun β ↦ ?_
    simp only [← Matrix.mulVec_mulVec]
    rw [hket β, SelectSwapQROM.zeroProjOn_mulVec_ket]
    split_ifs with h0
    · rw [← hket β, ketMapOp14_mulVec_ket, ite_pos2 (hValid β h0)]
      exact hInter β h0
    · simp only [Matrix.mulVec_zero]
  refine ⟨by simp [DynamicCircuit.count, hEnc.1, hMid.1, hDec.1], fun Θ hΘ ↦ ?_, fun Θ hΘ ↦ ?_⟩
  · have h1 := (hDec.2 Θ hΘ).1
    have h2 := hMid.2.1 _ h1
    have h3 := (hEnc.2 _ h2).1
    simpa only [DynamicCircuit.compile_seq, wp_qSeq] using h3
  · funext σ; apply Subtype.ext; apply Subtype.ext
    let Ψ_dec := wp dec.compile Θ
    have hΨ_dec : IsVInv14 v Ψ_dec := (hDec.2 Θ hΘ).1
    have hΨ_mid : IsVInv14 v (wp mid.compile Ψ_dec) := hMid.2.1 Ψ_dec hΨ_dec
    have hMidMat : P_S * (wp mid.compile Ψ_dec σ).1.1 * P_S =
        P_S * (W.1ᴴ * (Ψ_dec σ).1.1 * W.1) * P_S := by
      have hv := congrArg (fun x : Observable (Fin (2 ^ n)) ↦ x.1.1)
        (congrFun (hMid.2.2 Ψ_dec hΨ_dec) σ)
      rwa [restrictZeroSet_mat, restrictZeroSet_mat, wp_qAssign_mat] at hv
    have hEncEq := ((hEnc.mul_right P_out).2 (wp mid.compile Ψ_dec) hΨ_mid).2 σ
    have hDecEq := ((hDec.mul_right (G.1 * P_out)).2 Θ hΘ).2 σ
    have hSeq : wp (DynamicCircuit.seq enc (DynamicCircuit.seq mid dec)).compile Θ =
        wp enc.compile (wp mid.compile Ψ_dec) := by
      simp [Ψ_dec, DynamicCircuit.compile_seq, wp_qSeq]
    rw [hSeq, restrictZeroSet_mat, restrictZeroSet_mat, wp_qAssign_mat]
    change P_out * (wp enc.compile (wp mid.compile Ψ_dec) σ).1.1 * P_out =
      P_out * (G.1ᴴ * (Θ σ).1.1 * G.1) * P_out
    calc P_out * (wp enc.compile (wp mid.compile Ψ_dec) σ).1.1 * P_out
        = (P_enc * P_out)ᴴ * (wp enc.compile (wp mid.compile Ψ_dec) σ).1.1 * (P_enc * P_out) := by
            rw [hPencOut, hPoutH]
      _ = (E_enc * P_out)ᴴ * (wp mid.compile Ψ_dec σ).1.1 * (E_enc * P_out) := hEncEq
      _ = (E_enc * P_out)ᴴ * (P_S * (wp mid.compile Ψ_dec σ).1.1 * P_S) * (E_enc * P_out) := by
            conv_lhs => rw [← hPSEnc]
            rw [Matrix.conjTranspose_mul P_S (E_enc * P_out), hPSH]; simp only [Matrix.mul_assoc]
      _ = (E_enc * P_out)ᴴ * (P_S * (W.1ᴴ * (Ψ_dec σ).1.1 * W.1) * P_S) * (E_enc * P_out) := by
            rw [hMidMat]
      _ = (E_enc * (G.1 * P_out))ᴴ * (Ψ_dec σ).1.1 * (E_enc * (G.1 * P_out)) := by
            rw [hInter_mat, Matrix.conjTranspose_mul W.1 (P_S * (E_enc * P_out)),
              Matrix.conjTranspose_mul P_S (E_enc * P_out), hPSH]; simp only [Matrix.mul_assoc]
      _ = (P_enc * (G.1 * P_out))ᴴ * (Θ σ).1.1 * (P_enc * (G.1 * P_out)) := hDecEq
      _ = P_out * (G.1ᴴ * (Θ σ).1.1 * G.1) * P_out := by
            rw [hGP_mat, Matrix.conjTranspose_mul G.1 P_out, hPoutH]; simp only [Matrix.mul_assoc]
open Mobius126OneHot

/-! ## Section 3: `WpZeroSet` Lifting Corollaries & `708 T` (`35 ≤ sScr`) Preloaded Loader -/

/-- Public one-hot encoded bit assignment writing `1` at `localIdx L.rCtx β` on `L.rHot`. -/
noncomputable def oneHotEncAssign2 {K n : ℕ} (L : StepPow2Layout K n) (β : BitAssignment n) :
    BitAssignment n :=
  CoherentAlias.writeReg β L.rHot
    (fun g ↦ if g = CircuitModular.UnsignedGivens.localIdx L.rCtx β then 1 else 0)

theorem oneHotEncAssign2_apply_reg {K n : ℕ} (L : StepPow2Layout K n) (β : BitAssignment n)
    (g : Fin (2 ^ (K + 1))) :
    oneHotEncAssign2 L β (L.rHot g) =
      if g = CircuitModular.UnsignedGivens.localIdx L.rCtx β then 1 else 0 :=
  CoherentAlias.writeReg_apply_reg β L.rHot _ g

theorem oneHotEncAssign2_apply_of_not_mem {K n : ℕ} (L : StepPow2Layout K n) (β : BitAssignment n)
    {w : Wire n} (hw : w ∉ L.rHot.image) :
    oneHotEncAssign2 L β w = β w :=
  CoherentAlias.writeReg_apply_of_not_mem β L.rHot _ w
    (fun ⟨g, hg⟩ ↦ hw ((QRegister.mem_image L.rHot w).mpr ⟨g, hg⟩))

/-- Lift a diagonal `WpZeroSet` body across `withStepOneHotPow2Dyn` (`1 ≤ K ≤ 5`). -/
theorem WpZeroSet.withStepOneHotPow2_diag {Var : Type} [Fintype Var] [DecidableEq Var]
    {K n : ℕ} (hK1 : 1 ≤ K) (hK5 : K ≤ 5) {v : Var} (L : StepPow2Layout K n)
    (S_clean : Finset (Wire n)) (hqS : L.qEnc ∈ S_clean)
    (hDisjHotS : Disjoint L.rHot.image S_clean)
    {W : Unitary (2 ^ n)} {φ : BitAssignment n → ZMod 2} {mid : DynamicCircuit Var n}
    (hMid : WpZeroSet v S_clean W mid)
    (hKet : ∀ γ : BitAssignment n, (∀ w ∈ S_clean, γ w = 0) →
      W.1.mulVec (XMeasCircuit.ket γ) = SelectSwapQROM.bitSign (φ γ) • XMeasCircuit.ket γ) :
    WpZeroSet v (L.rHot.image ∪ S_clean)
      (diagKetUnitary (fun β ↦ φ (oneHotEncAssign2 L β)))
      (withStepOneHotPow2Dyn v L mid) := by
  classical
  have hket (γ : BitAssignment n) : XMeasCircuit.ket γ = SelectSwapQROM.ket γ := rfl
  have hValid (β : BitAssignment n) (h0 : ∀ w ∈ L.rHot.image ∪ S_clean, β w = 0) :
      sEncValid2 L β :=
    ⟨fun g ↦ h0 _ (Finset.mem_union_left _ ((QRegister.mem_image L.rHot _).mpr ⟨g, rfl⟩)),
     h0 _ (Finset.mem_union_right _ hqS)⟩
  have hCleanE (β : BitAssignment n) (h0 : ∀ w ∈ L.rHot.image ∪ S_clean, β w = 0)
      (w : Wire n) (hw : w ∈ S_clean) : encAssign2 L β w = 0 := by
    rw [encAssign2_eq_writeReg_oneHot L (hValid β h0)]
    change oneHotEncAssign2 L β w = 0
    rw [oneHotEncAssign2_apply_of_not_mem L β (Finset.disjoint_right.mp hDisjHotS hw)]
    exact h0 w (Finset.mem_union_right _ hw)
  refine WpZeroSet.of_subspace_sandwich (sEncValid2 L) (encAssign2 L) L.rHot.image S_clean
    (diagKetUnitary (fun β ↦ φ (oneHotEncAssign2 L β))) W
    (stepOneHotEncPow2Dyn v L) mid (stepOneHotDecPow2Dyn v L)
    (encPow2_step hK1 hK5 v L) (decPow2_step hK1 hK5 v L) hValid hCleanE hMid
    (fun β h0 ↦ ?_) (fun β h0 ↦ ?_)
  · rw [hket β, diagKetUnitary_mulVec_ket, ← hket β, Matrix.mulVec_smul, ketMapOp14_mulVec_ket,
      ite_pos2 (hValid β h0)]
  · have hEq : oneHotEncAssign2 L β = encAssign2 L β :=
      (encAssign2_eq_writeReg_oneHot L (hValid β h0)).symm
    rw [hket β, diagKetUnitary_mulVec_ket, ← hket β, Matrix.mulVec_smul, ketMapOp14_mulVec_ket,
      ite_pos2 (hValid β h0), hEq]
    exact (hKet (encAssign2 L β) (hCleanE β h0)).symm

/-- Lift a diagonal `WpZeroSet` body across `withStepAnfPow2Dyn` (`1 ≤ K ≤ 4`). -/
theorem WpZeroSet.withStepAnfPow2_diag {Var : Type} [Fintype Var] [DecidableEq Var]
    {K n : ℕ} (hK1 : 1 ≤ K) (hK4 : K ≤ 4) {v : Var} (L : StepPow2Layout K n)
    (S_clean : Finset (Wire n)) (hqS : L.qEnc ∈ S_clean)
    (hDisjHotS : Disjoint L.rHot.image S_clean)
    {W : Unitary (2 ^ n)} {φ : BitAssignment n → ZMod 2} {mid : DynamicCircuit Var n}
    (hMid : WpZeroSet v S_clean W mid)
    (hKet : ∀ γ : BitAssignment n, (∀ w ∈ S_clean, γ w = 0) →
      W.1.mulVec (XMeasCircuit.ket γ) = SelectSwapQROM.bitSign (φ γ) • XMeasCircuit.ket γ) :
    WpZeroSet v (L.rHot.image ∪ S_clean)
      (diagKetUnitary (fun β ↦ φ (anfEncAssign2 L β)))
      (withStepAnfPow2Dyn v L mid) := by
  classical
  have hket (γ : BitAssignment n) : XMeasCircuit.ket γ = SelectSwapQROM.ket γ := rfl
  have hValid (β : BitAssignment n) (h0 : ∀ w ∈ L.rHot.image ∪ S_clean, β w = 0) :
      sEncValid2 L β :=
    ⟨fun g ↦ h0 _ (Finset.mem_union_left _ ((QRegister.mem_image L.rHot _).mpr ⟨g, rfl⟩)),
     h0 _ (Finset.mem_union_right _ hqS)⟩
  have hCleanE (β : BitAssignment n) (h0 : ∀ w ∈ L.rHot.image ∪ S_clean, β w = 0)
      (w : Wire n) (hw : w ∈ S_clean) : anfEncAssign2 L β w = 0 := by
    rw [anfEncAssign2_apply_of_not_mem L β (Finset.disjoint_right.mp hDisjHotS hw)]
    exact h0 w (Finset.mem_union_right _ hw)
  refine WpZeroSet.of_subspace_sandwich (sEncValid2 L) (anfEncAssign2 L) L.rHot.image S_clean
    (diagKetUnitary (fun β ↦ φ (anfEncAssign2 L β))) W
    (stepAnfEncPow2Dyn v L) mid (stepAnfDecPow2Dyn v L)
    (anfEncPow2_step hK1 hK4 v L) (anfDecPow2_step hK1 hK4 v L) hValid hCleanE hMid
    (fun β h0 ↦ ?_) (fun β h0 ↦ ?_)
  · rw [hket β, diagKetUnitary_mulVec_ket, ← hket β, Matrix.mulVec_smul, ketMapOp14_mulVec_ket,
      ite_pos2 (hValid β h0)]
  · rw [hket β, diagKetUnitary_mulVec_ket, ← hket β, Matrix.mulVec_smul, ketMapOp14_mulVec_ket,
      ite_pos2 (hValid β h0)]
    exact (hKet (anfEncAssign2 L β) (hCleanE β h0)).symm

theorem count_hotCtxPhaseLoop_toff2 {N M L_ctx : ℕ}
    (rHotCtx : QRegister L_ctx N) (rAll : QRegister M N)
    (hHotNotAll : ∀ (c : Fin L_ctx) (u : Fin M), rHotCtx c ≠ rAll u)
    (c0 : Fin L_ctx → ZMod 2) (cPos : Fin L_ctx → Fin M → ZMod 2)
    (n : ℕ) (hn : n ≤ L_ctx) :
    (MidReflCtxRetain.hotCtxPhaseLoop M L_ctx rHotCtx rAll hHotNotAll c0 cPos n hn).count .TOFF =
      0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [MidReflCtxRetain.hotCtxPhaseLoop, Circuit.count_seq,
      SelectSwapQROM.count_czMaskCircuit_toff, add_zero]
    rw [ih (Nat.le_of_succ_le hn), zero_add]
    split_ifs <;> simp [Circuit.Z, Circuit.single]

theorem count_hotCtxPhaseLoop_t2 {N M L_ctx : ℕ}
    (rHotCtx : QRegister L_ctx N) (rAll : QRegister M N)
    (hHotNotAll : ∀ (c : Fin L_ctx) (u : Fin M), rHotCtx c ≠ rAll u)
    (c0 : Fin L_ctx → ZMod 2) (cPos : Fin L_ctx → Fin M → ZMod 2)
    (n : ℕ) (hn : n ≤ L_ctx) :
    (MidReflCtxRetain.hotCtxPhaseLoop M L_ctx rHotCtx rAll hHotNotAll c0 cPos n hn).count .T =
      0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [MidReflCtxRetain.hotCtxPhaseLoop, Circuit.count_seq,
      SelectSwapQROM.count_czMaskCircuit_t, add_zero]
    rw [ih (Nat.le_of_succ_le hn), zero_add]
    split_ifs <;> simp [Circuit.Z, Circuit.single]

theorem ket_hotCtxPhaseLoop {N M L_ctx : ℕ}
    (rHotCtx : QRegister L_ctx N) (rAll : QRegister M N)
    (hHotNotAll : ∀ (c : Fin L_ctx) (u : Fin M), rHotCtx c ≠ rAll u)
    (c0 : Fin L_ctx → ZMod 2) (cPos : Fin L_ctx → Fin M → ZMod 2)
    (n : ℕ) (hn : n ≤ L_ctx) (γ : BitAssignment N) :
    (MidReflCtxRetain.hotCtxPhaseLoop M L_ctx rHotCtx rAll hHotNotAll c0 cPos n hn).eval.1.mulVec
      (SelectSwapQROM.ket γ) =
    SelectSwapQROM.bitSign
      (∑ j : Fin n,
        let c : Fin L_ctx := ⟨j.val, Nat.lt_of_lt_of_le j.isLt hn⟩
        γ (rHotCtx c) * (c0 c + ∑ u : Fin M, cPos c u * γ (rAll u))) •
      SelectSwapQROM.ket γ := by
  induction n with
  | zero =>
    rw [MidReflCtxRetain.hotCtxPhaseLoop, SelectSwapQROM.ket_identity]
    simp [SelectSwapQROM.bitSign]
  | succ n ih =>
    let c : Fin L_ctx := ⟨n, hn⟩
    have hZ : (if c0 c = 1 then Circuit.Z (rHotCtx c) else .identity).eval.1.mulVec
        (SelectSwapQROM.ket γ) =
        SelectSwapQROM.bitSign (γ (rHotCtx c) * c0 c) • SelectSwapQROM.ket γ := by
      rcases SelectSwapQROM.bit_cases (c0 c) with h0 | h1
      · rw [h0, ite_neg2 (by decide : (0 : ZMod 2) ≠ 1), SelectSwapQROM.ket_identity, mul_zero]
        simp [SelectSwapQROM.bitSign]
      · rw [h1, ite_pos2 rfl, SelectSwapQROM.ket_Z, mul_one]
    simp only [MidReflCtxRetain.hotCtxPhaseLoop, SelectSwapQROM.eval_seq_mulVec]
    rw [ih (Nat.le_of_succ_le hn), Matrix.mulVec_smul, hZ, smul_smul, Matrix.mulVec_smul,
      SelectSwapQROM.ket_czMaskCircuit, smul_smul,
      ← SelectSwapQROM.bitSign_add, ← SelectSwapQROM.bitSign_add]
    congr 2
    rw [Fin.sum_univ_castSucc]
    dsimp only [c]
    rw [add_assoc, ← mul_add]
    rfl

private theorem option_map_eq_some14 {α β : Type*} {f : α → β} {o : Option α} {y : β}
    (h : o.map f = some y) : ∃ x, o = some x ∧ f x = y := by
  cases o with
  | none => cases h
  | some x => exact ⟨x, rfl, Option.some.inj h⟩

private theorem optWireBit_map_eq_optMono3 {N : ℕ} (γ : BitAssignment N) (r : QRegister 7 N)
    (zB : Fin (2 ^ 3))
    (h : ∀ u : Fin 7,
      γ (r u) = SelectSwapQROM.monoEval 3 (basisBits 3 zB) ⟨u.val + 1, by omega⟩)
    (jp : Option (Fin 7)) : optWireBit γ (jp.map r) = optMono3 zB jp := by
  cases jp with
  | none => rfl
  | some u => exact h u

private theorem optWireBit_map_eq_optMono214 {N : ℕ} (γ : BitAssignment N) (r : QRegister 3 N)
    (zC : Fin (2 ^ 2))
    (h : ∀ u : Fin 3,
      γ (r u) = SelectSwapQROM.monoEval 2 (basisBits 2 zC) ⟨u.val + 1, by omega⟩)
    (kp : Option (Fin 3)) : optWireBit γ (kp.map r) = optMono2 zC kp := by
  cases kp with
  | none => rfl
  | some u => exact h u

private theorem count_lStepLoop7_toff {Var : Type} {N L_ctx : ℕ} (v : Var)
    (P_slice : Fin L_ctx → Fin (2 ^ 3) → Fin (2 ^ 2) → ZMod 2)
    (rHotCtx : QRegister L_ctx N) (rAllB : QRegister 7 N) (rAllC : QRegister 3 N) (wAnc : Wire N)
    (hHB : rHotCtx.DisjointWires rAllB) (hHC : rHotCtx.DisjointWires rAllC)
    (hBC : rAllB.DisjointWires rAllC)
    (hAncH : ∀ c, wAnc ≠ rHotCtx c) (hAncB : ∀ j, wAnc ≠ rAllB j) (hAncC : ∀ k, wAnc ≠ rAllC k)
    (s : ℕ) (hs : s ≤ 7) :
    (lStepLoop7 v P_slice rHotCtx rAllB rAllC wAnc hHB hHC hBC hAncH hAncB hAncC s hs).count
      .TOFF = 0 := by
  induction s with
  | zero => rfl
  | succ s ih =>
      dsimp only [lStepLoop7, DynamicCircuit.count]
      rw [ih (Nat.le_of_lt hs), count_lStepInPlaceDyn_toff, add_zero]

private theorem count_lStepLoop7_t {Var : Type} {N L_ctx : ℕ} (v : Var)
    (P_slice : Fin L_ctx → Fin (2 ^ 3) → Fin (2 ^ 2) → ZMod 2)
    (rHotCtx : QRegister L_ctx N) (rAllB : QRegister 7 N) (rAllC : QRegister 3 N) (wAnc : Wire N)
    (hHB : rHotCtx.DisjointWires rAllB) (hHC : rHotCtx.DisjointWires rAllC)
    (hBC : rAllB.DisjointWires rAllC)
    (hAncH : ∀ c, wAnc ≠ rHotCtx c) (hAncB : ∀ j, wAnc ≠ rAllB j) (hAncC : ∀ k, wAnc ≠ rAllC k)
    (s : ℕ) (hs : s ≤ 7) :
    (lStepLoop7 v P_slice rHotCtx rAllB rAllC wAnc hHB hHC hBC hAncH hAncB hAncC s hs).count .T =
      4 * s := by
  induction s with
  | zero => rfl
  | succ s ih =>
      dsimp only [lStepLoop7, DynamicCircuit.count]
      rw [ih (Nat.le_of_lt hs), count_lStepInPlaceDyn_t]; omega

/-- Single-step L-triple phase exponent at step `t : Fin 7`. -/
private def lStep2KetPhase {N L_ctx : ℕ}
    (P_slice : Fin L_ctx → Fin (2 ^ 3) → Fin (2 ^ 2) → ZMod 2)
    (rHotCtx : QRegister L_ctx N) (rAllB : QRegister 7 N) (rAllC : QRegister 3 N) (t : Fin 7)
    (γ : BitAssignment N) : ZMod 2 :=
  let j := (canonLeg2 t).1
  let k := (canonLeg2 t).2.1
  let jp := (canonLeg2 t).2.2.1
  let kp := (canonLeg2 t).2.2.2
  let msk := leg2Masks P_slice t
  lStepPhase rHotCtx (rAllB j) (rAllC k) (jp.map rAllB) (kp.map rAllC) msk.1 msk.2.1 msk.2.2 γ

private theorem cleanRealizesSet_lStepLoop7 {Var : Type} [Fintype Var] [DecidableEq Var]
    {N L_ctx : ℕ} [NeZero (2 ^ N)] (v : Var) (S₀ : Finset (Wire N))
    (P_slice : Fin L_ctx → Fin (2 ^ 3) → Fin (2 ^ 2) → ZMod 2)
    (rHotCtx : QRegister L_ctx N) (rAllB : QRegister 7 N) (rAllC : QRegister 3 N) (wAnc : Wire N)
    (hHB : rHotCtx.DisjointWires rAllB) (hHC : rHotCtx.DisjointWires rAllC)
    (hBC : rAllB.DisjointWires rAllC)
    (hAncH : ∀ c, wAnc ≠ rHotCtx c) (hAncB : ∀ j, wAnc ≠ rAllB j) (hAncC : ∀ k, wAnc ≠ rAllC k)
    (hAncS : wAnc ∈ S₀) (hBNotS : ∀ j, rAllB j ∉ S₀) (hCNotS : ∀ k, rAllC k ∉ S₀)
    (s : ℕ) (hs : s ≤ 7) :
    SelectSwapQROM.CleanRealizesSet v S₀
      (diagKetUnitary (fun γ ↦ ∑ i : Fin s,
        lStep2KetPhase P_slice rHotCtx rAllB rAllC ⟨i.val, Nat.lt_of_lt_of_le i.isLt hs⟩ γ))
      (lStepLoop7 v P_slice rHotCtx rAllB rAllC wAnc hHB hHC hBC hAncH hAncB hAncC s hs) := by
  induction s with
  | zero =>
      dsimp only [lStepLoop7]; simp_rw [Fin.sum_univ_zero]
      rw [diagKetUnitary_zero]; exact SelectSwapQROM.CleanRealizesSet.identity v S₀
  | succ s ih =>
      dsimp only [lStepLoop7]
      let t : Fin 7 := ⟨s, hs⟩
      have hPrev := ih (Nat.le_of_lt hs)
      have hStep := cleanRealizesSet_lStepInPlaceDyn v S₀ rHotCtx (rAllB (canonLeg2 t).1)
        (rAllC (canonLeg2 t).2.1) wAnc ((canonLeg2 t).2.2.1.map rAllB)
        ((canonLeg2 t).2.2.2.map rAllC) (leg2Masks P_slice t).1 (leg2Masks P_slice t).2.1
        (leg2Masks P_slice t).2.2 (hBC.ne _ _) (hAncB _).symm (hAncC _).symm
        (fun c ↦ hHB.ne c _) (fun c ↦ hHC.ne c _) hAncH
        (option_map_ne_of_ne rAllB _ wAnc hAncB)
        (option_map_ne_of_ne rAllC _ wAnc hAncC)
        (fun w hw hEq ↦ by
          obtain ⟨j', hj', rfl⟩ := option_map_eq_some14 hw
          exact canonLeg2_j_ne_jp t j' hj' (rAllB.wires.injective hEq))
        (fun w hw ↦ by
          obtain ⟨j', _, rfl⟩ := option_map_eq_some14 hw
          exact (hBC.ne j' _).symm)
        (fun w hw ↦ by
          obtain ⟨k', _, rfl⟩ := option_map_eq_some14 hw
          exact hBC.ne _ k')
        (fun w hw hEq ↦ by
          obtain ⟨k', hk', rfl⟩ := option_map_eq_some14 hw
          exact canonLeg2_k_ne_kp t k' hk' (rAllC.wires.injective hEq))
        hAncS (hBNotS _) (hCNotS _)
      have hComb := hPrev.seq hStep
      rw [diagKetUnitary_mul] at hComb
      refine hComb.congr_unitary fun γ _ ↦ ?_
      rw [diagKetUnitary_mulVec_ket, diagKetUnitary_mulVec_ket, Fin.sum_univ_castSucc, add_comm]
      rfl

private theorem sum_concat_7_3 {N : ℕ} (rAllB : QRegister 7 N) (rAllC : QRegister 3 N)
    (hBC : rAllB.DisjointWires rAllC) (fB : Fin 7 → ZMod 2) (fC : Fin 3 → ZMod 2)
    (γ : BitAssignment N) :
    (∑ u : Fin (7 + 3),
      (if hu : u.val < 7 then fB ⟨u.val, hu⟩ else fC ⟨u.val - 7, by omega⟩) *
        γ ((rAllB.concat rAllC hBC) u)) =
    (∑ uB : Fin 7, fB uB * γ (rAllB uB)) + (∑ uC : Fin 3, fC uC * γ (rAllC uC)) := by
  rw [← Equiv.sum_comp (finSumFinEquiv (m := 7) (n := 3)), Fintype.sum_sum_type]
  refine congrArg₂ (· + ·) (Finset.sum_congr rfl fun uB _ ↦ ?_)
    (Finset.sum_congr rfl fun uC _ ↦ ?_)
  · have hu : ((finSumFinEquiv (m := 7) (n := 3)) (Sum.inl uB)).val < 7 := by
      rw [finSumFinEquiv_apply_left]; exact uB.isLt
    rw [dite_eq_left hu]
    simp only [finSumFinEquiv_apply_left, rAllB.concat_apply_left rAllC hBC uB]
    rfl
  · have hu : ¬ (((finSumFinEquiv (m := 7) (n := 3)) (Sum.inr uC)).val < 7) := by
      rw [finSumFinEquiv_apply_right, Fin.val_natAdd]; omega
    rw [dite_eq_right hu]
    simp only [finSumFinEquiv_apply_right, rAllB.concat_apply_right rAllC hBC uC]
    exact congrArg (· * γ (rAllC uC)) (congrArg fC (Fin.ext (by simp)))

private theorem ket_hotResidualClifford {N L_ctx outBits : ℕ}
    (F : Fin L_ctx → Fin (2 ^ 5) → Fin outBits → Bool) (m : Fin (2 ^ outBits))
    (rHotCtx : QRegister L_ctx N) (rAllB : QRegister 7 N) (rAllC : QRegister 3 N)
    (hHB : rHotCtx.DisjointWires rAllB) (hHC : rHotCtx.DisjointWires rAllC)
    (hBC : rAllB.DisjointWires rAllC) (γ : BitAssignment N) :
    (hotResidualClifford F m rHotCtx rAllB rAllC hHB hHC hBC).eval.1.mulVec
        (SelectSwapQROM.ket γ) =
      SelectSwapQROM.bitSign
        ((∑ uB : Fin 7, γ (rAllB uB) * ∑ uC : Fin 3, bg2Coeff uB uC * γ (rAllC uC)) +
         (∑ c : Fin L_ctx, γ (rHotCtx c) *
           (anf2DCoeffs (hotRes2DCube F m c) ⟨0, by decide⟩ ⟨0, by decide⟩ +
            (∑ uB : Fin 7,
              anf2DCoeffs (hotRes2DCube F m c) ⟨uB.val + 1, by omega⟩ ⟨0, by decide⟩ *
                γ (rAllB uB)) +
            (∑ uC : Fin 3,
              anf2DCoeffs (hotRes2DCube F m c) ⟨0, by decide⟩ ⟨uC.val + 1, by omega⟩ *
                γ (rAllC uC))))) •
        SelectSwapQROM.ket γ := by
  dsimp only [hotResidualClifford]
  rw [SelectSwapQROM.eval_seq_mulVec, FreeAltInnerPrepMid.ket_czBilinearCircuit,
    Matrix.mulVec_smul, ket_hotCtxPhaseLoop, smul_smul, ← SelectSwapQROM.bitSign_add]
  refine congrArg (· • SelectSwapQROM.ket γ) (congrArg SelectSwapQROM.bitSign ?_)
  congr 1; refine Finset.sum_congr rfl fun c _ ↦ ?_
  dsimp only; congr 1
  rw [sum_concat_7_3 rAllB rAllC hBC
    (fun uB ↦ anf2DCoeffs (hotRes2DCube F m c) ⟨uB.val + 1, by omega⟩ ⟨0, by decide⟩)
    (fun uC ↦ anf2DCoeffs (hotRes2DCube F m c) ⟨0, by decide⟩ ⟨uC.val + 1, by omega⟩) γ,
    ← add_assoc]

/-- `44 T` (`12 T` `3 → 8` ANF wrapper + `4 T` `2`-bit `monoSandwichDyn` + `28 T` `7`-step
L-triple phase loop), `0 TOFF`, `10`-wire `(3, 2)` turnaround phase fixup. -/
def hotPhaseFixupW3Dyn {Var : Type} {N : ℕ} (v : Var)
    (L_ctx outBits : ℕ)
    (F : Fin L_ctx → Fin (2 ^ 5) → Fin outBits → Bool)
    (m : Fin (2 ^ outBits))
    (rIdx : QRegister 5 N) (rHotCtx : QRegister L_ctx N) (rScr10 : QRegister 10 N)
    (hIdxHot : rIdx.DisjointWires rHotCtx)
    (hIdxScr : rIdx.DisjointWires rScr10)
    (hHotScr : rHotCtx.DisjointWires rScr10) : DynamicCircuit Var N :=
  let rB3 : QRegister (2 + 1) N := rIdx.slice 1 3 (by decide)
  let rC2 := rIdx.compose c2In5Reg
  let rHotB8 : QRegister (2 ^ (2 + 1)) N := rScr10.slice 0 8 (by decide)
  let rAllB : QRegister 7 N := rHotB8.slice 1 7 (by decide)
  let rMC := rScr10.slice 8 (SelectSwapQROM.anfScratchWidth 2) (by decide)
  let wAnc : Wire N := rScr10 ⟨9, by decide⟩
  have hCtxHot : rB3.DisjointWires rHotB8 := (hIdxScr.compose_left _).compose_right _
  have hCtxEnc : ∀ i : Fin 3, rB3 i ≠ wAnc :=
    fun i ↦ (hIdxScr.compose_left _).ne i ⟨9, by decide⟩
  have hHotEnc : ∀ g : Fin 8, rHotB8 g ≠ wAnc := fun g hEq ↦ by
    have hv := congrArg Fin.val (rScr10.wires.injective hEq)
    have := g.isLt; dsimp [rHotB8, wAnc, QRegister.slice] at hv; omega
  let L : StepPow2Layout 2 N := ⟨rB3, rHotB8, wAnc, hCtxHot, hCtxEnc, hHotEnc⟩
  have hCM : rC2.DisjointWires rMC := (hIdxScr.compose_left _).compose_right _
  let rAllC := SelectSwapQROM.allMonoReg 2 rC2 rMC hCM
  have hHB : rHotCtx.DisjointWires rAllB :=
    (hHotScr.compose_right (QRegister.block 0 8 (by decide))).compose_right
      (QRegister.block 1 7 (by decide))
  have hHC : rHotCtx.DisjointWires rAllC :=
    OptXMeasUnload21.disjointWires_of_disjoint_image
      (Disjoint.mono_right (SelectSwapQROM.allMonoReg_image_subset rC2 rMC hCM)
        (Finset.disjoint_union_right.mpr
          ⟨Disjoint.mono_right (rIdx.image_compose_subset _)
             (SelectSwapQROM.disjoint_image_of_disjointWires hIdxHot).symm,
           Disjoint.mono_right (rScr10.image_compose_subset _)
             (SelectSwapQROM.disjoint_image_of_disjointWires hHotScr)⟩))
  have hBC : rAllB.DisjointWires rAllC :=
    OptXMeasUnload21.disjointWires_of_disjoint_image
      (Disjoint.mono_right (SelectSwapQROM.allMonoReg_image_subset rC2 rMC hCM)
        (Finset.disjoint_union_right.mpr
          ⟨Disjoint.mono ((rHotB8.image_compose_subset _).trans (rScr10.image_compose_subset _))
             (rIdx.image_compose_subset _)
             (SelectSwapQROM.disjoint_image_of_disjointWires hIdxScr).symm,
           SelectSwapQROM.disjoint_image_of_disjointWires
             ((rScr10.slice_disjoint_of_le 0 8 8 1
                (by decide) (by decide) (by decide)).compose_left _)⟩))
  have hAncH : ∀ c : Fin L_ctx, wAnc ≠ rHotCtx c :=
    fun c ↦ (hHotScr.ne c ⟨9, by decide⟩).symm
  have hAncB : ∀ j : Fin 7, wAnc ≠ rAllB j := fun j hEq ↦ by
    have hv := congrArg Fin.val (rScr10.wires.injective hEq)
    have := j.isLt; dsimp [rAllB, rHotB8, wAnc, QRegister.slice] at hv; omega
  have hAncC : ∀ k : Fin 3, wAnc ≠ rAllC k := fun k hEq ↦ by
    rcases Finset.mem_union.mp (SelectSwapQROM.allMonoReg_image_subset rC2 rMC hCM
      (hEq ▸ (QRegister.mem_image rAllC _).mpr ⟨k, rfl⟩)) with h1 | h2
    · obtain ⟨i, hi⟩ := (QRegister.mem_image rC2 _).mp h1
      exact hIdxScr.ne _ ⟨9, by decide⟩ hi
    · obtain ⟨i, hi⟩ := (QRegister.mem_image rMC _).mp h2
      have hv := congrArg Fin.val (rScr10.wires.injective hi)
      simp only [QRegister.block_apply_val] at hv; have : i.val < 1 := i.isLt; omega
  withStepAnfPow2Dyn v L
    (SelectSwapQROM.monoSandwichDyn v 2 rC2 rMC hCM
      ((lStepLoop7 v (hotSlice2DCube F m) rHotCtx rAllB rAllC wAnc hHB hHC hBC
          hAncH hAncB hAncC 7 le_rfl).seq
        (.circuit (hotResidualClifford F m rHotCtx rAllB rAllC hHB hHC hBC))))

@[simp]
theorem count_hotPhaseFixupW3Dyn_toff {Var : Type} {N : ℕ} (v : Var)
    (L_ctx outBits : ℕ) (F : Fin L_ctx → Fin (2 ^ 5) → Fin outBits → Bool)
    (m : Fin (2 ^ outBits)) (rIdx : QRegister 5 N) (rHotCtx : QRegister L_ctx N)
    (rScr10 : QRegister 10 N) (hIdxHot : rIdx.DisjointWires rHotCtx)
    (hIdxScr : rIdx.DisjointWires rScr10) (hHotScr : rHotCtx.DisjointWires rScr10) :
    (hotPhaseFixupW3Dyn v L_ctx outBits F m rIdx rHotCtx rScr10 hIdxHot hIdxScr hHotScr).count
      .TOFF = 0 := by
  dsimp only [hotPhaseFixupW3Dyn]
  rw [count_withStepAnfPow2Dyn_toff, SelectSwapQROM.count_monoSandwichDyn_toff]
  dsimp only [DynamicCircuit.count]
  rw [count_lStepLoop7_toff, count_hotResidualClifford_toff, add_zero]

@[simp]
theorem count_hotPhaseFixupW3Dyn_t {Var : Type} {N : ℕ} (v : Var)
    (L_ctx outBits : ℕ) (F : Fin L_ctx → Fin (2 ^ 5) → Fin outBits → Bool)
    (m : Fin (2 ^ outBits)) (rIdx : QRegister 5 N) (rHotCtx : QRegister L_ctx N)
    (rScr10 : QRegister 10 N) (hIdxHot : rIdx.DisjointWires rHotCtx)
    (hIdxScr : rIdx.DisjointWires rScr10) (hHotScr : rHotCtx.DisjointWires rScr10) :
    (hotPhaseFixupW3Dyn v L_ctx outBits F m rIdx rHotCtx rScr10 hIdxHot hIdxScr hHotScr).count
      .T = 44 := by
  dsimp only [hotPhaseFixupW3Dyn]
  rw [count_withStepAnfPow2Dyn_t, SelectSwapQROM.count_monoSandwichDyn_t]
  dsimp only [DynamicCircuit.count]
  rw [count_lStepLoop7_t, count_hotResidualClifford_t]
  decide

theorem wpZeroSet_hotPhaseFixupW3Dyn {Var : Type} [Fintype Var] [DecidableEq Var]
    {N : ℕ} [NeZero (2 ^ N)] (v : Var) (S : Finset (Wire N))
    (L_ctx outBits : ℕ) (F : Fin L_ctx → Fin (2 ^ 5) → Fin outBits → Bool)
    (m : Fin (2 ^ outBits)) (rIdx : QRegister 5 N) (rHotCtx : QRegister L_ctx N)
    (rScr10 : QRegister 10 N) (hIdxHot : rIdx.DisjointWires rHotCtx)
    (hIdxScr : rIdx.DisjointWires rScr10) (hHotScr : rHotCtx.DisjointWires rScr10)
    (hScrSubS : rScr10.image ⊆ S) (hDisjIdxS : Disjoint rIdx.image S) :
    WpZeroSet v S
      (diagKetUnitary (hotFixup12KetPhase F m rIdx rHotCtx))
      (hotPhaseFixupW3Dyn v L_ctx outBits F m rIdx rHotCtx rScr10 hIdxHot hIdxScr hHotScr) := by
  let rB3 : QRegister (2 + 1) N := rIdx.slice 1 3 (by decide)
  let rC2 := rIdx.compose c2In5Reg
  let rHotB8 : QRegister (2 ^ (2 + 1)) N := rScr10.slice 0 8 (by decide)
  let rAllB : QRegister 7 N := rHotB8.slice 1 7 (by decide)
  let rMC := rScr10.slice 8 (SelectSwapQROM.anfScratchWidth 2) (by decide)
  let wAnc : Wire N := rScr10 ⟨9, by decide⟩
  have hCtxHot : rB3.DisjointWires rHotB8 := (hIdxScr.compose_left _).compose_right _
  have hCtxEnc : ∀ i : Fin 3, rB3 i ≠ wAnc :=
    fun i ↦ (hIdxScr.compose_left _).ne i ⟨9, by decide⟩
  have hHotEnc : ∀ g : Fin 8, rHotB8 g ≠ wAnc := fun g hEq ↦ by
    have hv := congrArg Fin.val (rScr10.wires.injective hEq)
    have := g.isLt; dsimp [rHotB8, wAnc, QRegister.slice] at hv; omega
  let L : StepPow2Layout 2 N := ⟨rB3, rHotB8, wAnc, hCtxHot, hCtxEnc, hHotEnc⟩
  have hCM : rC2.DisjointWires rMC := (hIdxScr.compose_left _).compose_right _
  let rAllC := SelectSwapQROM.allMonoReg 2 rC2 rMC hCM
  have hHB : rHotCtx.DisjointWires rAllB :=
    (hHotScr.compose_right (QRegister.block 0 8 (by decide))).compose_right
      (QRegister.block 1 7 (by decide))
  have hHC : rHotCtx.DisjointWires rAllC :=
    OptXMeasUnload21.disjointWires_of_disjoint_image
      (Disjoint.mono_right (SelectSwapQROM.allMonoReg_image_subset rC2 rMC hCM)
        (Finset.disjoint_union_right.mpr
          ⟨Disjoint.mono_right (rIdx.image_compose_subset _)
             (SelectSwapQROM.disjoint_image_of_disjointWires hIdxHot).symm,
           Disjoint.mono_right (rScr10.image_compose_subset _)
             (SelectSwapQROM.disjoint_image_of_disjointWires hHotScr)⟩))
  have hBC : rAllB.DisjointWires rAllC :=
    OptXMeasUnload21.disjointWires_of_disjoint_image
      (Disjoint.mono_right (SelectSwapQROM.allMonoReg_image_subset rC2 rMC hCM)
        (Finset.disjoint_union_right.mpr
          ⟨Disjoint.mono ((rHotB8.image_compose_subset _).trans (rScr10.image_compose_subset _))
             (rIdx.image_compose_subset _)
             (SelectSwapQROM.disjoint_image_of_disjointWires hIdxScr).symm,
           SelectSwapQROM.disjoint_image_of_disjointWires
             ((rScr10.slice_disjoint_of_le 0 8 8 1
                (by decide) (by decide) (by decide)).compose_left _)⟩))
  have hAncH : ∀ c : Fin L_ctx, wAnc ≠ rHotCtx c :=
    fun c ↦ (hHotScr.ne c ⟨9, by decide⟩).symm
  have hAncB : ∀ j : Fin 7, wAnc ≠ rAllB j := fun j hEq ↦ by
    have hv := congrArg Fin.val (rScr10.wires.injective hEq)
    have := j.isLt; dsimp [rAllB, rHotB8, wAnc, QRegister.slice] at hv; omega
  have hAncC : ∀ k : Fin 3, wAnc ≠ rAllC k := fun k hEq ↦ by
    rcases Finset.mem_union.mp (SelectSwapQROM.allMonoReg_image_subset rC2 rMC hCM
      (hEq ▸ (QRegister.mem_image rAllC _).mpr ⟨k, rfl⟩)) with h1 | h2
    · obtain ⟨i, hi⟩ := (QRegister.mem_image rC2 _).mp h1
      exact hIdxScr.ne _ ⟨9, by decide⟩ hi
    · obtain ⟨i, hi⟩ := (QRegister.mem_image rMC _).mp h2
      have hv := congrArg Fin.val (rScr10.wires.injective hi)
      simp only [QRegister.block_apply_val] at hv; have : i.val < 1 := i.isLt; omega
  let S₁ := S \ rHotB8.image
  let S₂ := S₁ \ rMC.image
  have hDisjHotMC : Disjoint rHotB8.image rMC.image :=
    SelectSwapQROM.disjoint_image_of_disjointWires
      (rScr10.slice_disjoint_of_le 0 8 8 (SelectSwapQROM.anfScratchWidth 2)
        (by decide) (by decide) (by decide))
  have hAncNotM : wAnc ∉ rHotB8.image ∧ wAnc ∉ rMC.image := by
    refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
    · obtain ⟨g, hg⟩ := (QRegister.mem_image rHotB8 _).mp h
      have hv := congrArg Fin.val (rScr10.wires.injective hg)
      simp only [QRegister.block_apply_val] at hv; have : g.val < 8 := g.isLt; omega
    · obtain ⟨i, hi⟩ := (QRegister.mem_image rMC _).mp h
      have hv := congrArg Fin.val (rScr10.wires.injective hi)
      simp only [QRegister.block_apply_val] at hv; have : i.val < 1 := i.isLt; omega
  have hAncS₁ : wAnc ∈ S₁ := Finset.mem_sdiff.mpr
    ⟨hScrSubS ((QRegister.mem_image rScr10 _).mpr ⟨⟨9, by decide⟩, rfl⟩), hAncNotM.1⟩
  have hAncS₂ : wAnc ∈ S₂ := Finset.mem_sdiff.mpr ⟨hAncS₁, hAncNotM.2⟩
  have hBNotS₂ (j : Fin 7) : rAllB j ∉ S₂ := fun hs₂ ↦
    (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hs₂).1).2
      (rHotB8.image_compose_subset _ ((QRegister.mem_image rAllB _).mpr ⟨j, rfl⟩))
  have hCNotS₂ (k : Fin 3) : rAllC k ∉ S₂ := fun hs₂ ↦ by
    rcases Finset.mem_union.mp (SelectSwapQROM.allMonoReg_image_subset rC2 rMC hCM
      ((QRegister.mem_image rAllC _).mpr ⟨k, rfl⟩)) with h1 | h2
    · exact Finset.disjoint_left.mp hDisjIdxS (rIdx.image_compose_subset _ h1)
        (Finset.sdiff_subset (Finset.sdiff_subset hs₂))
    · exact (Finset.mem_sdiff.mp hs₂).2 h2
  let cliff := hotResidualClifford F m rHotCtx rAllB rAllC hHB hHC hBC
  have hLoop := cleanRealizesSet_lStepLoop7 v S₂ (hotSlice2DCube F m) rHotCtx rAllB rAllC wAnc
    hHB hHC hBC hAncH hAncB hAncC hAncS₂ hBNotS₂ hCNotS₂ 7 le_rfl
  have hCliff : SelectSwapQROM.CleanRealizesSet v S₂ cliff.eval (.circuit cliff) := by
    refine SelectSwapQROM.CleanRealizesSet.ofCircuit v S₂ cliff
      (count_hotResidualClifford_toff _ _ _ _ _ _ _ _) fun γ hγ ↦ ?_
    rw [ket_hotResidualClifford, Matrix.mulVec_smul, SelectSwapQROM.zeroProjOn_mulVec_ket,
      ite_pos2 hγ]
  have hInner := hLoop.seq hCliff
  let cliffExp (γ : BitAssignment N) : ZMod 2 :=
    (∑ uB : Fin 7, γ (rAllB uB) * ∑ uC : Fin 3, bg2Coeff uB uC * γ (rAllC uC)) +
    (∑ c : Fin L_ctx, γ (rHotCtx c) *
      (anf2DCoeffs (hotRes2DCube F m c) ⟨0, by decide⟩ ⟨0, by decide⟩ +
       (∑ uB : Fin 7,
         anf2DCoeffs (hotRes2DCube F m c) ⟨uB.val + 1, by omega⟩ ⟨0, by decide⟩ *
           γ (rAllB uB)) +
       (∑ uC : Fin 3,
         anf2DCoeffs (hotRes2DCube F m c) ⟨0, by decide⟩ ⟨uC.val + 1, by omega⟩ *
           γ (rAllC uC))))
  have hkInner (γ : BitAssignment N) :
      (cliff.eval * diagKetUnitary
        (fun δ ↦ ∑ t : Fin 7,
          lStep2KetPhase (hotSlice2DCube F m) rHotCtx rAllB rAllC t δ)).1.mulVec
        (SelectSwapQROM.ket γ) =
      SelectSwapQROM.bitSign
        ((∑ t : Fin 7, lStep2KetPhase (hotSlice2DCube F m) rHotCtx rAllB rAllC t γ) +
          cliffExp γ) • SelectSwapQROM.ket γ := by
    rw [Submonoid.coe_mul, ← Matrix.mulVec_mulVec, diagKetUnitary_mulVec_ket, Matrix.mulVec_smul,
      ket_hotResidualClifford, smul_smul, ← SelectSwapQROM.bitSign_add, add_comm]
  have hMCSubS₁ : rMC.image ⊆ S₁ := fun w hw ↦ Finset.mem_sdiff.mpr
    ⟨hScrSubS (rScr10.image_compose_subset _ hw), Finset.disjoint_right.mp hDisjHotMC hw⟩
  obtain ⟨U_C, popC, hCrC, hkC⟩ :=
    SelectSwapQROM.cleanRealizesSet_monoSandwichDyn_diag v S₁ rC2 rMC hCM hMCSubS₁
      (Disjoint.mono (rIdx.image_compose_subset _) Finset.sdiff_subset hDisjIdxS)
      hInner (fun γ _ ↦ hkInner γ)
  have hDisjHotS₁ : Disjoint rHotB8.image S₁ := disjoint_sdiff_self_right
  have hHotSubS : rHotB8.image ⊆ S := (rScr10.image_compose_subset _).trans hScrSubS
  have hUnionS : rHotB8.image ∪ S₁ = S := Finset.union_sdiff_of_subset hHotSubS
  have hket (γ : BitAssignment N) : XMeasCircuit.ket γ = SelectSwapQROM.ket γ := rfl
  have hWpFull := WpZeroSet.withStepAnfPow2_diag (by decide) (by decide) L S₁ hAncS₁ hDisjHotS₁
    (WpZeroSet.of_cleanRealizesSet hCrC)
    (fun γ hγ ↦ by rw [hket γ]; exact (hkC γ hγ).1)
  rw [hUnionS] at hWpFull
  refine hWpFull.congr_unitary fun β hβ ↦ ?_
  have hCleanS₁ : ∀ w ∈ S₁, anfEncAssign2 L β w = 0 := fun w hw ↦ by
    rw [anfEncAssign2_apply_of_not_mem L β (Finset.mem_sdiff.mp hw).2]
    exact hβ w (Finset.mem_sdiff.mp hw).1
  obtain ⟨_, hOutC, hAllC⟩ := hkC (anfEncAssign2 L β) hCleanS₁
  rw [hket β, diagKetUnitary_mulVec_ket, diagKetUnitary_mulVec_ket]
  refine congrArg (· • SelectSwapQROM.ket β) (congrArg SelectSwapQROM.bitSign ?_)
  set δ := popC (anfEncAssign2 L β)
  let zB : Fin (2 ^ 3) := (basisBits 3).symm (fun i ↦ β (rB3 i))
  let zC : Fin (2 ^ 2) := (basisBits 2).symm (fun i ↦ β (rC2 i))
  have hzB (i : Fin 3) : basisBits 3 zB i = β (rB3 i) :=
    congrFun (SelectSwapQROM.basisBits_symm _) i
  have hzC (i : Fin 2) : basisBits 2 zC i = β (rC2 i) :=
    congrFun (SelectSwapQROM.basisBits_symm _) i
  have hIdxNotScr {w : Wire N} (hwI : w ∈ rIdx.image) (hwS : w ∈ rScr10.image) : False :=
    Finset.disjoint_left.mp (SelectSwapQROM.disjoint_image_of_disjointWires hIdxScr) hwI hwS
  have hHotNotScr (c : Fin L_ctx) {w : Wire N} (hwEq : rHotCtx c = w) (hwS : w ∈ rScr10.image) :
      False :=
    hHotScr.apply_not_mem_right c (hwEq ▸ hwS)
  have hδHot (c : Fin L_ctx) : δ (rHotCtx c) = β (rHotCtx c) := by
    rw [hOutC _ (fun hm ↦ hHotNotScr c rfl (rScr10.image_compose_subset _ hm)),
      anfEncAssign2_apply_of_not_mem L β
        (fun hm ↦ hHotNotScr c rfl (rScr10.image_compose_subset _ hm))]
  have hδB (uB : Fin 7) :
      δ (rAllB uB) = SelectSwapQROM.monoEval 3 (basisBits 3 zB) ⟨uB.val + 1, by omega⟩ := by
    have hnC : rAllB uB ∉ rMC.image := fun hm ↦
      Finset.disjoint_left.mp hDisjHotMC
        (rHotB8.image_compose_subset _ ((QRegister.mem_image rAllB _).mpr ⟨uB, rfl⟩)) hm
    have hrw : rAllB uB = rHotB8 ⟨uB.val + 1, by omega⟩ :=
      congrArg rHotB8 (Fin.ext (by dsimp [rAllB, QRegister.slice]; omega))
    rw [hOutC _ hnC, hrw, anfEncAssign2_apply_reg L β ⟨uB.val + 1, by omega⟩]
    exact congrArg (fun f ↦ SelectSwapQROM.monoEval 3 f _) (funext fun i ↦ (hzB i).symm)
  have hδC (uC : Fin 3) :
      δ (rAllC uC) = SelectSwapQROM.monoEval 2 (basisBits 2 zC) ⟨uC.val + 1, by omega⟩ := by
    rw [hAllC uC]
    refine congrArg (fun f ↦ SelectSwapQROM.monoEval 2 f _) (funext fun i ↦ ?_)
    rw [anfEncAssign2_apply_of_not_mem L β (fun hm ↦ hIdxNotScr
      (rIdx.image_compose_subset _ ((QRegister.mem_image rC2 _).mpr ⟨i, rfl⟩))
      (rScr10.image_compose_subset _ hm)), (hzC i).symm]
  have hStepEq (t : Fin 7) :
      lStep2KetPhase (hotSlice2DCube F m) rHotCtx rAllB rAllC t δ =
        let j := (canonLeg2 t).1
        let k := (canonLeg2 t).2.1
        let jp := (canonLeg2 t).2.2.1
        let kp := (canonLeg2 t).2.2.2
        let msk := leg2Masks (hotSlice2DCube F m) t
        (SelectSwapQROM.monoEval 3 (basisBits 3 zB) ⟨j.val + 1, by omega⟩ +
          ∑ c : Fin L_ctx, msk.1 c * β (rHotCtx c)) *
        (SelectSwapQROM.monoEval 2 (basisBits 2 zC) ⟨k.val + 1, by omega⟩ +
          ∑ c : Fin L_ctx, msk.2.1 c * β (rHotCtx c)) *
        ((∑ c : Fin L_ctx, msk.2.2 c * β (rHotCtx c)) + optMono3 zB jp + optMono2 zC kp) := by
    dsimp only [lStep2KetPhase, lStepPhase]
    rw [hδB, hδC, optWireBit_map_eq_optMono3 δ rAllB zB hδB,
      optWireBit_map_eq_optMono214 δ rAllC zC hδC]
    simp_rw [hδHot]
  dsimp only [hotFixup12KetPhase, cliffExp]
  simp_rw [hStepEq, hδB, hδC, hδHot]
  rfl

private theorem predProj_mulVec_ket2 {N : ℕ} (H : BitAssignment N → Bool) (β : BitAssignment N) :
    (GroupUnary.predProj H).mulVec (SelectSwapQROM.ket β) =
      if H β = true then SelectSwapQROM.ket β else 0 := by
  dsimp [GroupUnary.predProj, SelectSwapQROM.ket, basisState]
  rw [Matrix.diagonal_mulVec_single, SelectSwapQROM.basisBits_symm]
  cases H β <;> simp

private theorem zeroProjOn_comm_predProj {N : ℕ} (S : Finset (Wire N))
    (H : BitAssignment N → Bool) :
    SelectSwapQROM.zeroProjOn S * GroupUnary.predProj H =
      GroupUnary.predProj H * SelectSwapQROM.zeroProjOn S := by
  have hz : SelectSwapQROM.zeroProjOn S =
      GroupUnary.predProj (fun β ↦ decide (∀ w ∈ S, β w = 0)) := by
    ext i j
    simp only [SelectSwapQROM.zeroProjOn, GroupUnary.predProj, Matrix.diagonal_apply]
    by_cases hij : i = j
    · subst hij; by_cases h : ∀ w ∈ S, basisBits N i w = 0 <;> simp [h]
    · simp [hij]
  rw [hz, GroupUnary.predProj_comm]

private theorem cleanPredProj_conjTranspose2 {N : ℕ} (S : Finset (Wire N))
    (H : BitAssignment N → Bool) :
    (Mobius126OneHot.cleanPredProj S H)ᴴ = Mobius126OneHot.cleanPredProj S H := by
  dsimp only [Mobius126OneHot.cleanPredProj]
  rw [conjTranspose_mul, GroupUnary.predProj_conjTranspose,
    SelectSwapQROM.zeroProjOn_conjTranspose, ← zeroProjOn_comm_predProj]

private theorem oneHotPred_update_of_not_mem {N L_ctx : ℕ} (rHotCtx : QRegister L_ctx N)
    {w : Wire N} (hw : w ∉ rHotCtx.image) (β : BitAssignment N) (val : ZMod 2) :
    oneHotPred rHotCtx (Function.update β w val) = oneHotPred rHotCtx β := by
  dsimp only [oneHotPred]
  congr 1; apply propext
  refine exists_congr fun c₀ ↦ forall_congr' fun c ↦ ?_
  rw [Function.update_of_ne (fun hEq ↦ hw ((QRegister.mem_image rHotCtx w).mpr ⟨c, hEq⟩))]

private theorem wp_qAssign_one2 {Var : Type} [Fintype Var] {d : ℕ}
    (Θ : QCAssertion Var d) : qcWpQAssign (1 : Unitary d) Θ = Θ := by
  funext σ; apply Subtype.ext; apply HermitianMat.ext
  simp [qcWpQAssign, qcQAssignObsMap]

theorem wp_hotPhaseFixupW3Dyn_oneHot {Var : Type} [Fintype Var] [DecidableEq Var]
    {N : ℕ} [NeZero (2 ^ N)] (v : Var) (S : Finset (Wire N))
    (L_ctx outBits : ℕ) (F : Fin L_ctx → Fin (2 ^ 5) → Fin outBits → Bool)
    (hVan30 : ∀ (c : Fin L_ctx) (k : Fin outBits),
      SelectSwapQROM.anfCoeffs 5
        (fun x ↦ if F c x k then (1 : ZMod 2) else 0) ⟨30, by decide⟩ = 0)
    (hVan31 : ∀ (c : Fin L_ctx) (k : Fin outBits),
      SelectSwapQROM.anfCoeffs 5
        (fun x ↦ if F c x k then (1 : ZMod 2) else 0) ⟨31, by decide⟩ = 0)
    (m : Fin (2 ^ outBits)) (rIdx : QRegister 5 N) (rHotCtx : QRegister L_ctx N)
    (rScr10 : QRegister 10 N) (hIdxHot : rIdx.DisjointWires rHotCtx)
    (hIdxScr : rIdx.DisjointWires rScr10) (hHotScr : rHotCtx.DisjointWires rScr10)
    (hScrSubS : rScr10.image ⊆ S) (hDisjIdxS : Disjoint rIdx.image S) :
    let D_m : Unitary (2 ^ N) :=
      (rIdx.concat rHotCtx hIdxHot).embedUnitary
        (SelectSwapQROM.diagPhaseUnitary (5 + L_ctx) (2 ^ (5 + L_ctx))
          (SelectSwapQROM.parityPhaseTable outBits
            (MidReflCtxRetain.hotLinearBoolTable 5 L_ctx outBits F) m))
    ∀ Θ : QCAssertion Var (2 ^ N), (∀ σ val, Θ (Function.update σ v val) = Θ σ) →
      ∀ σ : Store Var,
        ((wp (hotPhaseFixupW3Dyn v L_ctx outBits F m rIdx rHotCtx rScr10
          hIdxHot hIdxScr hHotScr).compile Θ σ).1).conj
            (Mobius126OneHot.cleanPredProj S (oneHotPred rHotCtx)) =
        ((qcWpQAssign D_m Θ σ).1).conj
          (Mobius126OneHot.cleanPredProj S (oneHotPred rHotCtx)) := by
  intro D_m Θ hΘ σ
  have hWp := wpZeroSet_hotPhaseFixupW3Dyn v S L_ctx outBits F m rIdx rHotCtx rScr10
    hIdxHot hIdxScr hHotScr hScrSubS hDisjIdxS
  have hMat : (diagKetUnitary (hotFixup12KetPhase F m rIdx rHotCtx)).1 *
      Mobius126OneHot.cleanPredProj S (oneHotPred rHotCtx) =
      D_m.1 * Mobius126OneHot.cleanPredProj S (oneHotPred rHotCtx) := by
    apply SelectSwapQROM.matrix_ext_ket; intro β
    dsimp only [Mobius126OneHot.cleanPredProj]
    simp only [← Matrix.mulVec_mulVec, predProj_mulVec_ket2]
    by_cases hH : oneHotPred rHotCtx β = true
    · rw [ite_pos2 hH, SelectSwapQROM.zeroProjOn_mulVec_ket]
      by_cases hS : ∀ x ∈ S, β x = 0
      · rw [ite_pos2 hS, diagKetUnitary_mulVec_ket,
          SelectSwapQROM.embed_diagPhaseUnitary_mulVec_ket,
          hotFixup12KetPhase_eq_of_oneHot F hVan30 hVan31 m rIdx rHotCtx hIdxHot β hH]
        congr 1
        let a := (basisBits (5 + L_ctx)).symm (fun k ↦ β ((rIdx.concat rHotCtx hIdxHot) k))
        have haLt : a.val < 2 ^ (5 + L_ctx) := a.isLt
        change SelectSwapQROM.bitSign (if _ then 1 else 0) = if a.val < _ ∧ _ then -1 else 1
        simp only [haLt, true_and]
        cases SelectSwapQROM.parityPhaseTable outBits
          (MidReflCtxRetain.hotLinearBoolTable 5 L_ctx outBits F) m a.val <;>
          simp [SelectSwapQROM.bitSign]
      · simp [hS]
    · simp [hH]
  have hAdj : Mobius126OneHot.cleanPredProj S (oneHotPred rHotCtx) *
      (diagKetUnitary (hotFixup12KetPhase F m rIdx rHotCtx)).1ᴴ =
      Mobius126OneHot.cleanPredProj S (oneHotPred rHotCtx) * D_m.1ᴴ := by
    simpa only [conjTranspose_mul, cleanPredProj_conjTranspose2] using congrArg conjTranspose hMat
  have hWpS := congrArg (fun A : QCAssertion Var (2 ^ N) ↦
    (A σ).1.conj (GroupUnary.predProj (oneHotPred rHotCtx))) (hWp.2.2 Θ hΘ)
  rw [SelectSwapQROM.restrictZeroSet_coe, SelectSwapQROM.restrictZeroSet_coe,
    conj_conj, conj_conj, ← zeroProjOn_comm_predProj] at hWpS
  change ((wp _ Θ σ).1).conj (Mobius126OneHot.cleanPredProj S (oneHotPred rHotCtx)) =
    ((qcWpQAssign _ Θ σ).1).conj (Mobius126OneHot.cleanPredProj S (oneHotPred rHotCtx)) at hWpS
  rw [hWpS]
  simp only [qcWpQAssign, qcQAssignObsMap, Observable.conj_coe, Unitary.coe_star,
    Matrix.star_eq_conjTranspose, conj_conj, hAdj]

attribute [irreducible] hotPhaseFixupW3Dyn

/-- `44 T`, `0 TOFF` `rHotCtx`-assisted X-measurement QROM unload at `idxBits = 5` using `10`
clean scratch wires `rScr10`. -/
def qromXMeasW3FromHotCtxUnloadDyn {Var : Type} {N : ℕ} (v : Var)
    (L_ctx outBits : ℕ)
    (F : Fin L_ctx → Fin (2 ^ 5) → Fin outBits → Bool)
    (rIdx : QRegister 5 N) (rHotCtx : QRegister L_ctx N)
    (rMeas : QRegister outBits N) (rScr10 : QRegister 10 N)
    (hIdxHot : rIdx.DisjointWires rHotCtx)
    (hIdxScr : rIdx.DisjointWires rScr10)
    (hHotScr : rHotCtx.DisjointWires rScr10) : DynamicCircuit Var N :=
  SelectSwapQROM.measureXResetAndBranch v outBits rMeas
    (fun m ↦ hotPhaseFixupW3Dyn v L_ctx outBits F m
      rIdx rHotCtx rScr10 hIdxHot hIdxScr hHotScr)

@[simp]
theorem count_qromXMeasW3FromHotCtxUnloadDyn_toff {Var : Type} {N : ℕ} (v : Var)
    (L_ctx outBits : ℕ) (F : Fin L_ctx → Fin (2 ^ 5) → Fin outBits → Bool)
    (rIdx : QRegister 5 N) (rHotCtx : QRegister L_ctx N)
    (rMeas : QRegister outBits N) (rScr10 : QRegister 10 N)
    (hIdxHot : rIdx.DisjointWires rHotCtx) (hIdxScr : rIdx.DisjointWires rScr10)
    (hHotScr : rHotCtx.DisjointWires rScr10) :
    (qromXMeasW3FromHotCtxUnloadDyn v L_ctx outBits F
      rIdx rHotCtx rMeas rScr10 hIdxHot hIdxScr hHotScr).count .TOFF = 0 :=
  SelectSwapQROM.count_measureXResetAndBranch_toff v outBits rMeas _
    (fun m ↦ count_hotPhaseFixupW3Dyn_toff v L_ctx outBits F m
      rIdx rHotCtx rScr10 hIdxHot hIdxScr hHotScr)

@[simp]
theorem count_qromXMeasW3FromHotCtxUnloadDyn_t {Var : Type} {N : ℕ} (v : Var)
    (L_ctx outBits : ℕ) (F : Fin L_ctx → Fin (2 ^ 5) → Fin outBits → Bool)
    (rIdx : QRegister 5 N) (rHotCtx : QRegister L_ctx N)
    (rMeas : QRegister outBits N) (rScr10 : QRegister 10 N)
    (hIdxHot : rIdx.DisjointWires rHotCtx) (hIdxScr : rIdx.DisjointWires rScr10)
    (hHotScr : rHotCtx.DisjointWires rScr10) :
    (qromXMeasW3FromHotCtxUnloadDyn v L_ctx outBits F
      rIdx rHotCtx rMeas rScr10 hIdxHot hIdxScr hHotScr).count .T = 44 :=
  SelectSwapQROM.count_measureXResetAndBranch_t_eq v outBits 44 rMeas _
    (fun m ↦ count_hotPhaseFixupW3Dyn_t v L_ctx outBits F m
      rIdx rHotCtx rScr10 hIdxHot hIdxScr hHotScr)

theorem wp_qromXMeasW3FromHotCtxUnloadDyn_update_self {Var : Type} [Finite Var] [DecidableEq Var]
    {N : ℕ} [NeZero (2 ^ N)] (v : Var) (L_ctx outBits : ℕ)
    (F : Fin L_ctx → Fin (2 ^ 5) → Fin outBits → Bool)
    (rIdx : QRegister 5 N) (rHotCtx : QRegister L_ctx N)
    (rMeas : QRegister outBits N) (rScr10 : QRegister 10 N)
    (hIdxHot : rIdx.DisjointWires rHotCtx) (hIdxScr : rIdx.DisjointWires rScr10)
    (hHotScr : rHotCtx.DisjointWires rScr10)
    (Θ : QCAssertion Var (2 ^ N)) (hΘ : ∀ σ val, Θ (Function.update σ v val) = Θ σ)
    (σ : Store Var) (val : ℤ) :
    wp (qromXMeasW3FromHotCtxUnloadDyn v L_ctx outBits F
      rIdx rHotCtx rMeas rScr10 hIdxHot hIdxScr hHotScr).compile Θ (Function.update σ v val) =
    wp (qromXMeasW3FromHotCtxUnloadDyn v L_ctx outBits F
      rIdx rHotCtx rMeas rScr10 hIdxHot hIdxScr hHotScr).compile Θ σ := by
  cases nonempty_fintype Var
  dsimp only [qromXMeasW3FromHotCtxUnloadDyn]
  exact wp_measureXResetAndBranch_update_self v outBits rMeas _
    (fun m Ψ hΨ τ b ↦ (wpZeroSet_hotPhaseFixupW3Dyn v rScr10.image L_ctx outBits F m
      rIdx rHotCtx rScr10 hIdxHot hIdxScr hHotScr Finset.Subset.rfl
      (SelectSwapQROM.disjoint_image_of_disjointWires hIdxScr)).2.1 Ψ hΨ τ b) Θ hΘ σ val

theorem wp_qromXMeasW3FromHotCtxUnloadDyn_oneHot {Var : Type} [Fintype Var] [DecidableEq Var]
    {N : ℕ} [NeZero (2 ^ N)] (v : Var) (S : Finset (Wire N))
    (L_ctx outBits : ℕ) (F : Fin L_ctx → Fin (2 ^ 5) → Fin outBits → Bool)
    (hVan30 : ∀ (c : Fin L_ctx) (k : Fin outBits),
      SelectSwapQROM.anfCoeffs 5
        (fun x ↦ if F c x k then (1 : ZMod 2) else 0) ⟨30, by decide⟩ = 0)
    (hVan31 : ∀ (c : Fin L_ctx) (k : Fin outBits),
      SelectSwapQROM.anfCoeffs 5
        (fun x ↦ if F c x k then (1 : ZMod 2) else 0) ⟨31, by decide⟩ = 0)
    (rIdx : QRegister 5 N) (rHotCtx : QRegister L_ctx N)
    (rMeas : QRegister outBits N) (rScr10 : QRegister 10 N)
    (hIdxHot : rIdx.DisjointWires rHotCtx)
    (hAddrMeas : (rIdx.concat rHotCtx hIdxHot).DisjointWires rMeas)
    (hIdxScr : rIdx.DisjointWires rScr10) (hHotScr : rHotCtx.DisjointWires rScr10)
    (hMeasSubS : rMeas.image ⊆ S) (hScrSubS : rScr10.image ⊆ S)
    (hDisjIdxS : Disjoint rIdx.image S)
    (Θ : QCAssertion Var (2 ^ N)) (hΘ : ∀ σ val, Θ (Function.update σ v val) = Θ σ)
    (σ : Store Var) :
    ((qcWpQAssign (((rIdx.concat rHotCtx hIdxHot).concat rMeas hAddrMeas).embedUnitary
        (SelectSwapQROM.xorLoadUnitary (5 + L_ctx) outBits (2 ^ (5 + L_ctx))
          (MidReflCtxRetain.hotLinearBoolTable 5 L_ctx outBits F)))
      (wp (qromXMeasW3FromHotCtxUnloadDyn v L_ctx outBits F
        rIdx rHotCtx rMeas rScr10 hIdxHot hIdxScr hHotScr).compile Θ) σ).1).conj
      (Mobius126OneHot.cleanPredProj S (oneHotPred rHotCtx)) =
    ((Θ σ).1).conj (Mobius126OneHot.cleanPredProj S (oneHotPred rHotCtx)) := by
  have hHotMeas : rHotCtx.DisjointWires rMeas :=
    QRegister.disjoint_iff.mpr fun c j hij ↦
      hAddrMeas.ne (Fin.natAdd 5 c) j ((rIdx.concat_apply_right rHotCtx hIdxHot c).trans hij)
  have hUn := wp_measureXResetAndBranch_unload_cleanPredProj v S (oneHotPred rHotCtx) outBits
    (2 ^ (5 + L_ctx)) (MidReflCtxRetain.hotLinearBoolTable 5 L_ctx outBits F)
    (rIdx.concat rHotCtx hIdxHot) rMeas hAddrMeas hMeasSubS
    (fun q hq β val ↦ oneHotPred_update_of_not_mem rHotCtx
      (Finset.disjoint_right.mp (SelectSwapQROM.disjoint_image_of_disjointWires hHotMeas) hq)
      β val) 1
    (fun m ↦ hotPhaseFixupW3Dyn v L_ctx outBits F m rIdx rHotCtx rScr10 hIdxHot hIdxScr hHotScr)
    (fun m Ψ hΨ τ ↦ by
      rw [one_mul]
      exact wp_hotPhaseFixupW3Dyn_oneHot v S L_ctx outBits F hVan30 hVan31 m
        rIdx rHotCtx rScr10 hIdxHot hIdxScr hHotScr hScrSubS hDisjIdxS Ψ hΨ τ)
    Θ hΘ σ
  dsimp only [qromXMeasW3FromHotCtxUnloadDyn]
  rwa [wp_qAssign_one2] at hUn

attribute [irreducible] qromXMeasW3FromHotCtxUnloadDyn

/-- Pooled `44 T`, `0 TOFF` `rHotCtx`-assisted X-measurement QROM unload on
`CoherentAlias.aliasActBits 5 L_ctx b payBits`: pools freshly reset `aliasOutReg` wires with `rScr`
to supply `10` scratch wires (`0 ≤ sScr` at `b = 9, payBits = 1`, where `aliasOutBits = 16`). -/
def qromXMeasW3FromHotCtxAliasUnloadDyn {Var : Type} {N L_ctx b payBits sScr : ℕ} (v : Var)
    (F : Fin L_ctx → Fin (2 ^ 5) → Fin (CoherentAlias.aliasOutBits 5 b payBits) → Bool)
    (rAlias : QRegister (CoherentAlias.aliasActBits 5 L_ctx b payBits) N)
    (rScr : QRegister sScr N)
    (hFit : 10 ≤ CoherentAlias.aliasOutBits 5 b payBits + sScr)
    (hdisj : rAlias.DisjointWires rScr) : DynamicCircuit Var N :=
  let M := CoherentAlias.aliasOutBits 5 b payBits
  let rIdx := rAlias.compose (CoherentAlias.aliasIdxReg 5 L_ctx b payBits)
  let rHotCtx := rAlias.compose (CoherentAlias.aliasCtxReg 5 L_ctx b payBits)
  let rMeas := rAlias.compose (AliasPrep.aliasOutReg 5 L_ctx b payBits)
  let rPool := rMeas.concat rScr (CoherentAlias.compose_disjointWires_left _ hdisj)
  let hScrLe : 0 + 10 ≤ M + sScr := by omega
  let rScr10 := rPool.slice 0 10 hScrLe
  have hIdxHot : rIdx.DisjointWires rHotCtx :=
    QRegister.disjoint_iff.mpr fun i c hij ↦ by
      have hv := congrArg Fin.val (rAlias.wires.injective hij)
      simp only [CoherentAlias.aliasIdxReg, CoherentAlias.aliasCtxReg,
        QRegister.block_apply_val] at hv
      have := i.isLt; omega
  have hIdxMeas : rIdx.DisjointWires rMeas :=
    QRegister.disjoint_iff.mpr fun i j hij ↦ by
      have hv := congrArg Fin.val (rAlias.wires.injective hij)
      simp only [CoherentAlias.aliasIdxReg, AliasPrep.aliasOutReg,
        QRegister.block_apply_val] at hv
      have := i.isLt; omega
  have hHotMeas : rHotCtx.DisjointWires rMeas :=
    QRegister.disjoint_iff.mpr fun c j hij ↦ by
      have hv := congrArg Fin.val (rAlias.wires.injective hij)
      simp only [CoherentAlias.aliasCtxReg, AliasPrep.aliasOutReg,
        QRegister.block_apply_val] at hv
      have := c.isLt; omega
  have hIdxPool : rIdx.DisjointWires rPool :=
    QRegister.disjointWires_concat_right (CoherentAlias.compose_disjointWires_left _ hdisj)
      hIdxMeas (CoherentAlias.compose_disjointWires_left _ hdisj)
  have hHotPool : rHotCtx.DisjointWires rPool :=
    QRegister.disjointWires_concat_right (CoherentAlias.compose_disjointWires_left _ hdisj)
      hHotMeas (CoherentAlias.compose_disjointWires_left _ hdisj)
  qromXMeasW3FromHotCtxUnloadDyn v L_ctx M F rIdx rHotCtx rMeas rScr10 hIdxHot
    (hIdxPool.compose_right (QRegister.block 0 10 hScrLe))
    (hHotPool.compose_right (QRegister.block 0 10 hScrLe))

@[simp]
theorem count_qromXMeasW3FromHotCtxAliasUnloadDyn_toff {Var : Type}
    {N L_ctx b payBits sScr : ℕ} (v : Var)
    (F : Fin L_ctx → Fin (2 ^ 5) → Fin (CoherentAlias.aliasOutBits 5 b payBits) → Bool)
    (rAlias : QRegister (CoherentAlias.aliasActBits 5 L_ctx b payBits) N)
    (rScr : QRegister sScr N)
    (hFit : 10 ≤ CoherentAlias.aliasOutBits 5 b payBits + sScr)
    (hdisj : rAlias.DisjointWires rScr) :
    (qromXMeasW3FromHotCtxAliasUnloadDyn v F rAlias rScr hFit hdisj).count .TOFF = 0 :=
  count_qromXMeasW3FromHotCtxUnloadDyn_toff _ _ _ _ _ _ _ _ _ _ _

@[simp]
theorem count_qromXMeasW3FromHotCtxAliasUnloadDyn_t {Var : Type}
    {N L_ctx b payBits sScr : ℕ} (v : Var)
    (F : Fin L_ctx → Fin (2 ^ 5) → Fin (CoherentAlias.aliasOutBits 5 b payBits) → Bool)
    (rAlias : QRegister (CoherentAlias.aliasActBits 5 L_ctx b payBits) N)
    (rScr : QRegister sScr N)
    (hFit : 10 ≤ CoherentAlias.aliasOutBits 5 b payBits + sScr)
    (hdisj : rAlias.DisjointWires rScr) :
    (qromXMeasW3FromHotCtxAliasUnloadDyn v F rAlias rScr hFit hdisj).count .T = 44 :=
  count_qromXMeasW3FromHotCtxUnloadDyn_t _ _ _ _ _ _ _ _ _ _ _

theorem wp_qromXMeasW3FromHotCtxAliasUnloadDyn_update_self
    {Var : Type} [Finite Var] [DecidableEq Var] {N L_ctx b payBits sScr : ℕ} [NeZero (2 ^ N)]
    (v : Var) (F : Fin L_ctx → Fin (2 ^ 5) → Fin (CoherentAlias.aliasOutBits 5 b payBits) → Bool)
    (rAlias : QRegister (CoherentAlias.aliasActBits 5 L_ctx b payBits) N)
    (rScr : QRegister sScr N) (hFit : 10 ≤ CoherentAlias.aliasOutBits 5 b payBits + sScr)
    (hdisj : rAlias.DisjointWires rScr)
    (Θ : QCAssertion Var (2 ^ N)) (hΘ : ∀ σ val, Θ (Function.update σ v val) = Θ σ)
    (σ : Store Var) (val : ℤ) :
    wp (qromXMeasW3FromHotCtxAliasUnloadDyn v F rAlias rScr hFit hdisj).compile Θ
      (Function.update σ v val) =
    wp (qromXMeasW3FromHotCtxAliasUnloadDyn v F rAlias rScr hFit hdisj).compile Θ σ :=
  wp_qromXMeasW3FromHotCtxUnloadDyn_update_self _ _ _ _ _ _ _ _ _ _ _ Θ hΘ σ val

theorem wp_qromXMeasW3FromHotCtxAliasUnloadDyn_oneHot
    {Var : Type} [Fintype Var] [DecidableEq Var] {N L_ctx b payBits sScr : ℕ} [NeZero (2 ^ N)]
    (v : Var) (F : Fin L_ctx → Fin (2 ^ 5) → Fin (CoherentAlias.aliasOutBits 5 b payBits) → Bool)
    (hVan30 : ∀ (c : Fin L_ctx) (k : Fin (CoherentAlias.aliasOutBits 5 b payBits)),
      SelectSwapQROM.anfCoeffs 5
        (fun x ↦ if F c x k then (1 : ZMod 2) else 0) ⟨30, by decide⟩ = 0)
    (hVan31 : ∀ (c : Fin L_ctx) (k : Fin (CoherentAlias.aliasOutBits 5 b payBits)),
      SelectSwapQROM.anfCoeffs 5
        (fun x ↦ if F c x k then (1 : ZMod 2) else 0) ⟨31, by decide⟩ = 0)
    (rAlias : QRegister (CoherentAlias.aliasActBits 5 L_ctx b payBits) N)
    (rScr : QRegister sScr N)
    (hFit : 10 ≤ CoherentAlias.aliasOutBits 5 b payBits + sScr)
    (hdisj : rAlias.DisjointWires rScr)
    (Θ : QCAssertion Var (2 ^ N)) (hΘ : ∀ σ val, Θ (Function.update σ v val) = Θ σ)
    (σ : Store Var) :
    let S := rScr.image ∪ (rAlias.compose (AliasPrep.aliasOutReg 5 L_ctx b payBits)).image
    let H := oneHotPred (rAlias.compose (CoherentAlias.aliasCtxReg 5 L_ctx b payBits))
    ((qcWpQAssign ((rAlias.compose (CoherentAlias.aliasQromReg 5 L_ctx b payBits)).embedUnitary
        (CoherentAlias.aliasTableXorUnitary (5 + L_ctx)
          (CoherentAlias.aliasOutBits 5 b payBits)
          (MidReflCtxRetain.hotLinearTargetFn 5 L_ctx
            (CoherentAlias.aliasOutBits 5 b payBits) F)))
      (wp (qromXMeasW3FromHotCtxAliasUnloadDyn v F rAlias rScr hFit hdisj).compile Θ) σ).1).conj
      (Mobius126OneHot.cleanPredProj S H) =
    ((Θ σ).1).conj (Mobius126OneHot.cleanPredProj S H) := by
  intro S H
  let M := CoherentAlias.aliasOutBits 5 b payBits
  let rIdx := rAlias.compose (CoherentAlias.aliasIdxReg 5 L_ctx b payBits)
  let rHotCtx := rAlias.compose (CoherentAlias.aliasCtxReg 5 L_ctx b payBits)
  let rMeas := rAlias.compose (AliasPrep.aliasOutReg 5 L_ctx b payBits)
  let rPool := rMeas.concat rScr (CoherentAlias.compose_disjointWires_left _ hdisj)
  have hPoolSub : rPool.image ⊆ S := by
    rw [QRegister.image_concat]
    exact Finset.union_subset Finset.subset_union_right Finset.subset_union_left
  have hIdxHot : rIdx.DisjointWires rHotCtx :=
    QRegister.disjoint_iff.mpr fun i c hij ↦ by
      have hv := congrArg Fin.val (rAlias.wires.injective hij)
      simp only [CoherentAlias.aliasIdxReg, CoherentAlias.aliasCtxReg,
        QRegister.block_apply_val] at hv
      have := i.isLt; omega
  have hIdxMeas : rIdx.DisjointWires rMeas :=
    QRegister.disjoint_iff.mpr fun i j hij ↦ by
      have hv := congrArg Fin.val (rAlias.wires.injective hij)
      simp only [CoherentAlias.aliasIdxReg, AliasPrep.aliasOutReg,
        QRegister.block_apply_val] at hv
      have := i.isLt; omega
  have hHotMeas : rHotCtx.DisjointWires rMeas :=
    QRegister.disjoint_iff.mpr fun c j hij ↦ by
      have hv := congrArg Fin.val (rAlias.wires.injective hij)
      simp only [CoherentAlias.aliasCtxReg, AliasPrep.aliasOutReg,
        QRegister.block_apply_val] at hv
      have := c.isLt; omega
  have hAddrMeas : (rIdx.concat rHotCtx hIdxHot).DisjointWires rMeas :=
    QRegister.disjointWires_concat_left hIdxHot hIdxMeas hHotMeas
  have hDisjIdxS : Disjoint rIdx.image S :=
    Finset.disjoint_union_right.mpr
      ⟨SelectSwapQROM.disjoint_image_of_disjointWires
         (CoherentAlias.compose_disjointWires_left _ hdisj),
       SelectSwapQROM.disjoint_image_of_disjointWires hIdxMeas⟩
  have hConcat : (rIdx.concat rHotCtx hIdxHot).concat rMeas hAddrMeas =
      rAlias.compose (CoherentAlias.aliasQromReg 5 L_ctx b payBits) := by
    apply CoherentAlias.qreg_ext; intro k
    by_cases hkA : k.val < 5 + L_ctx
    · rw [show k = Fin.castAdd M ⟨k.val, hkA⟩ from rfl,
        (rIdx.concat rHotCtx hIdxHot).concat_apply_left rMeas hAddrMeas ⟨k.val, hkA⟩]
      by_cases hk5 : k.val < 5
      · rw [show (⟨k.val, hkA⟩ : Fin (5 + L_ctx)) = Fin.castAdd L_ctx ⟨k.val, hk5⟩ from rfl,
          rIdx.concat_apply_left rHotCtx hIdxHot ⟨k.val, hk5⟩]
        exact congrArg (fun x ↦ (rAlias x).val)
          (Fin.ext (by simp [CoherentAlias.aliasIdxReg, CoherentAlias.aliasQromReg]))
      · let c : Fin L_ctx := ⟨k.val - 5, by omega⟩
        rw [show (⟨k.val, hkA⟩ : Fin (5 + L_ctx)) = Fin.natAdd 5 c from
            Fin.ext (by dsimp [c]; omega),
          rIdx.concat_apply_right rHotCtx hIdxHot c]
        exact congrArg (fun x ↦ (rAlias x).val)
          (Fin.ext (by simp [CoherentAlias.aliasCtxReg, CoherentAlias.aliasQromReg, c]))
    · let j : Fin M := ⟨k.val - (5 + L_ctx), by have := k.isLt; omega⟩
      rw [show k = Fin.natAdd (5 + L_ctx) j from Fin.ext (by dsimp [j]; omega),
        (rIdx.concat rHotCtx hIdxHot).concat_apply_right rMeas hAddrMeas j]
      exact congrArg (fun x ↦ (rAlias x).val)
        (Fin.ext (by simp [AliasPrep.aliasOutReg, CoherentAlias.aliasQromReg, j]))
  have hEmb : ((rIdx.concat rHotCtx hIdxHot).concat rMeas hAddrMeas).embedUnitary
      (SelectSwapQROM.xorLoadUnitary (5 + L_ctx) M (2 ^ (5 + L_ctx))
        (MidReflCtxRetain.hotLinearBoolTable 5 L_ctx M F)) =
      (rAlias.compose (CoherentAlias.aliasQromReg 5 L_ctx b payBits)).embedUnitary
        (CoherentAlias.aliasTableXorUnitary (5 + L_ctx) M
          (MidReflCtxRetain.hotLinearTargetFn 5 L_ctx M F)) := by
    rw [hConcat, AliasPrep.xorLoadUnitary_eq_aliasTableXorUnitary]; rfl
  rw [← hEmb]
  dsimp only [qromXMeasW3FromHotCtxAliasUnloadDyn]
  exact wp_qromXMeasW3FromHotCtxUnloadDyn_oneHot v S L_ctx M F hVan30 hVan31
    rIdx rHotCtx rMeas _ hIdxHot hAddrMeas _ _ Finset.subset_union_right
    ((rPool.image_compose_subset _).trans hPoolSub) hDisjIdxS Θ hΘ σ

attribute [irreducible] qromXMeasW3FromHotCtxAliasUnloadDyn

end CoreImpl

end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.StepAnfAndCoin14Core
