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
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.LowBitPi145Select
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.QuantizedFactoredMag30

/-!
# `wInner2 = 18` `14`-Plane `Symp14` Walk, `Mux23Bundle` & `28-T` `SiZero` Spin Cancellation

Eliminates `wNegIn` (`2` wires per `PREP_mid` leg) by shrinking the inner state-preparation
ancilla width from `wInner2 = 20` (`mMidUB 20 = 26`) to `wInner2 = 18` (`mMidUB 18 = 24`), and
exports:
1. The ancilla-free `72-T` (`31 + 31 + 10`, `0 TOFF`) factored `L = 30` magnitude splitter
   `factoredMag30T72Circuit` (`L¹ ≤ 8835 / 10 ^ 13`).
2. The `wInner2 = 18` register geometry (`0..4` = `idx`, `5..9` = `alt`, `10..18` = `keep`,
   `19..22` = `pkt`, `23` = `sig_in`), `swap5PairsUnitary` (`5` swap pairs = `20 T` vs `24 T`),
   and parametric `Mux23Bundle`.
3. Parametric `Symp14Spec R` bit-level algebra and `wInner2 = 18` `(alt : 5, keep : 9)` `PREP_mid`
   forward circuits (`14 + tMux + tQr + cMag` `T`, e.g. `708 T` at `w = 4` and `672 T` at `w = 5`
   for `R = 153`), plus one-hot `wp` congruence hooks for `hGadget` / `E1` QROM loaders.
4. `wInner2 = 18` state-dependent reflection `reflMidDyn` (`32 T` vs `36 T` at `wInner2 = 20`) and
   ancilla-free `5`-pair coherent swap (`20 T` vs `24 T` per leg).

## References
- C. Gidney, "Halving the cost of quantum addition," *Quantum* **2**, 74 (2018),
  DOI: 10.22331/q-2018-06-18-74.
- R. Babbush, C. Gidney, D. W. Berry, N. Wiebe, J. McClean, A. Paler, A. Fowler, and H. Neven,
  "Encoding Electronic Spectra in Quantum Circuits with Linear T Complexity,"
  *Phys. Rev. X* **8**, 041015 (2018), DOI: 10.1103/PhysRevX.8.041015.
- G. H. Low, V. Kliuchnikov, and L. Schaeffer, "Trading T gates for dirty qubits in state
  preparation and unitary synthesis," *Quantum* **8**, 1375 (2024),
  DOI: 10.22331/q-2024-06-17-1375.
- J. Lee, D. W. Berry, C. Gidney, W. J. Huggins, J. R. McClean, N. Wiebe, and R. Babbush,
  "Even More Efficient Quantum Computations of Chemistry Through Tensor Hypercontraction,"
  *PRX Quantum* **2**, 030305 (2021), DOI: 10.1103/PRXQuantum.2.030305.
-/

@[expose] public section

namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.Inner18Symp14Walk
open QuantumComputation.Specs QuantumComputation.Specs.P450

open Operator QProg Matrix Circuit Real HermitianMat BlockEncodingCore BlockEncodingCircuit
open QuantumComputation.Specs QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution
open QuantumComputation.Specs.P450 CoherentAlias CleanDyn AliasPrep
open CircuitModular GivensOps
open MidReflCtxRetain Phase2MidSandwich OptFactoredMag30AndCoin9 QuantizedFactoredMag30
open Cat11CompactPhase2Bridge ReordOuter13Bridge ZeroRcHotPrepMid21Fast OptXMeasUnload21
open Tuned162ScheduledSympQrom21 Tuned162StepSympAnfQrom21 OptStepSympAnfQrom21 TopIntegrationBridge
open MobiusOptSubcube163Walk CompactTuned162StepZeroCmp20 CompactZeroCmp20OuterParam
open CompactStepZeroCmp20OuterParam StepAnfAndCoin14Core CompactStepCompact2504ZeroCmp20
open Pi145SOSPermBridge StepOuter8Pi145Outer StepOuter8Pi145L1 StepKeep9Symp14Data
open StepBound148Borrow Tuned155Hot128SympQrom20 CompactOuter9Bound50Core
open LowBitPi145Select BellSingletCSwap58 FastUniform
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.CircuitModular.UnsignedGivens (
  maskSumBit basisBits_symm_eq cnotMaskReg
  evolve_cnotMaskReg_ket eval_identity_mulVec)
open Function (update update_of_ne update_self update_apply)
open Observable (conj_coe)
open Unitary (coe_star)
open Submonoid (coe_mul)
open DynamicCircuit (qc_wp_circuit_compile compile_circuit)
open scoped Matrix BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator Circuit.Notation

local instance (priority := 1000000) instNeZeroTwoPowSymp18 (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩

/-! ## Section 1: Ancilla-Free `72-T` Factored `L = 30` Splitter (`factoredMag30T72Circuit`) -/

/-- Exact reduced `CyclotomicMat2` matrix for `m45T31W` (`k = 17`). -/
def m45T31RawMat : CliffordT.CyclotomicMat2 :=
  ⟨17, ⟨122, 74, 153, -203⟩, ⟨-14, 112, -177, -45⟩, ⟨-112, 14, -45, -177⟩, ⟨74, 122, 203, -153⟩⟩

/-- Balanced `8`-gate-leaf `GateTrace` for `p = 4/5` (`31 T`, `0 TOFF`). -/
def m45T31W : CliffordT.GateTrace :=
  let l0 := CliffordT.GateTrace.leaf [.Z, .S, .X, .S, .H, .T, .Z, .H]
    ⟨2, ⟨0, 0, 1, 1⟩, ⟨0, 0, -1, 1⟩, ⟨0, 0, 1, -1⟩, ⟨0, 0, -1, -1⟩⟩ 0
  let l1 := CliffordT.GateTrace.leaf [.T, .S, .Z, .H, .T, .S, .Z, .H]
    ⟨3, ⟨1, 0, 2, 1⟩, ⟨-1, 0, 0, -1⟩, ⟨-1, 0, 0, -1⟩, ⟨-1, -2, 0, -1⟩⟩ 1
  let l2 := CliffordT.GateTrace.leaf [.T, .Z, .H, .T, .S, .Z, .H, .T]
    ⟨4, ⟨2, 1, 1, 2⟩, ⟨0, -1, -1, 2⟩, ⟨0, -2, 1, 1⟩, ⟨-2, 2, 1, 1⟩⟩ 1
  let l3 := CliffordT.GateTrace.leaf [.S, .Z, .H, .T, .Z, .H, .T, .S]
    ⟨5, ⟨-1, 2, 2, -1⟩, ⟨-1, 4, 2, -1⟩, ⟨-2, -4, 1, -1⟩, ⟨2, 2, -1, 1⟩⟩ 1
  let l4 := CliffordT.GateTrace.leaf [.Z, .H, .T, .Z, .H, .T, .Z, .H]
    ⟨6, ⟨1, 3, 0, -1⟩, ⟨-2, 2, -3, -6⟩, ⟨-2, 6, 3, -2⟩, ⟨-1, -1, 0, 3⟩⟩ 2
  let l5 := CliffordT.GateTrace.leaf [.T, .Z, .H, .T, .Z, .H, .T, .S]
    ⟨7, ⟨6, -3, -4, -4⟩, ⟨5, -4, 3, 1⟩, ⟨4, -5, 1, 3⟩, ⟨-3, 6, 4, 4⟩⟩ 1
  let l6 := CliffordT.GateTrace.leaf [.Z, .H, .T, .S, .Z, .H, .T, .S]
    ⟨8, ⟨8, -6, -9, 0⟩, ⟨1, 7, -4, -3⟩, ⟨-3, -4, 7, 1⟩, ⟨0, 9, 6, -8⟩⟩ 1
  let l7 := CliffordT.GateTrace.leaf [.Z, .H, .T, .Z, .H, .T, .Z, .H]
    ⟨10, ⟨-22, 0, 5, -9⟩, ⟨-6, -14, -9, -11⟩, ⟨14, 6, -11, -9⟩, ⟨0, -22, 9, -5⟩⟩ 1
  let l8 := CliffordT.GateTrace.leaf [.T, .S, .Z, .H, .T, .Z, .H, .T]
    ⟨11, ⟨27, -13, -10, -2⟩, ⟨-7, -15, -14, 24⟩, ⟨-14, -15, -7, -24⟩, ⟨10, 13, -27, -2⟩⟩ 1
  let l9 := CliffordT.GateTrace.leaf [.Z, .H, .T, .Z, .H, .T, .Z, .H]
    ⟨12, ⟨10, -39, 5, 35⟩, ⟨-5, 4, 20, 28⟩, ⟨5, 28, 20, 4⟩, ⟨10, -35, -5, 39⟩⟩ 2
  let l10 := CliffordT.GateTrace.leaf [.T, .S, .Z, .H, .T, .Z, .H, .T]
    ⟨13, ⟨-15, 73, 14, -5⟩, ⟨-34, 24, 3, 26⟩, ⟨24, -34, -26, -3⟩, ⟨-73, 15, -5, 14⟩⟩ 1
  let l11 := CliffordT.GateTrace.leaf [.Z, .H, .T, .Z, .H, .T, .Z, .H]
    ⟨15, ⟨99, -88, 30, -27⟩, ⟨75, 78, 42, -11⟩, ⟨-11, 42, 78, 75⟩, ⟨27, -30, 88, -99⟩⟩ 1
  let l12 := CliffordT.GateTrace.leaf [.T, .S, .Z, .H, .T, .S, .Z, .H]
    ⟨16, ⟨9, 21, -64, 46⟩, ⟨225, -3, 82, -38⟩, ⟨-3, 225, 38, -82⟩, ⟨-21, -9, 46, -64⟩⟩ 1
  let l13 := CliffordT.GateTrace.leaf [.T, .S, .Z, .H, .T, .Z, .H]
    ⟨17, ⟨122, 74, 153, -203⟩, ⟨-14, 112, -177, -45⟩, ⟨-112, 14, -45, -177⟩, ⟨74, 122, 203, -153⟩⟩ 1
  .cat (.cat (.cat l0 (.cat l1 l2)) (.cat (.cat l3 l4) (.cat l5 l6)))
    (.cat (.cat l7 (.cat l8 l9)) (.cat (.cat l10 l11) (.cat l12 l13)))

theorem ns_45_31 : Complex.normSq (m45T31W.toCircuit.eval.1 0 0) =
    ((84978 : ℤ) + (14057 : ℤ) * √2) / (2 : ℝ) ^ 17 :=
  traceCircuit_normSq_zero_zero m45T31W m45T31RawMat 84978 14057 rfl rfl
theorem m45T31_toff : m45T31W.toCircuit.count .TOFF = 0 := m45T31W.toCircuit_count_toff
theorem m45T31_t : m45T31W.toCircuit.count .T = 31 := m45T31W.toCircuit_count_t

/-- Exact reduced `CyclotomicMat2` matrix for `m23T31W` (`k = 17`). -/
def m23T31RawMat : CliffordT.CyclotomicMat2 :=
  ⟨17, ⟨22, -214, -23, 235⟩, ⟨-85, -127, -28, -70⟩, ⟨127, 85, -70, -28⟩, ⟨-214, 22, -235, 23⟩⟩

/-- Balanced `8`-gate-leaf `GateTrace` for `p = 2/3` (`31 T`, `0 TOFF`). -/
def m23T31W : CliffordT.GateTrace :=
  let l0 := CliffordT.GateTrace.leaf [.S, .H, .X, .Z, .T, .H, .T, .H]
    ⟨2, ⟨0, 1, 0, 0⟩, ⟨1, -1, -1, 0⟩, ⟨-1, 0, -1, -1⟩, ⟨0, 0, 0, -1⟩⟩ 1
  let l1 := CliffordT.GateTrace.leaf [.T, .H, .S, .T, .H, .T, .H, .S]
    ⟨4, ⟨2, -1, 1, 0⟩, ⟨1, 0, 0, -3⟩, ⟨3, 0, 0, -1⟩, ⟨0, 1, -1, 2⟩⟩ 1
  let l2 := CliffordT.GateTrace.leaf [.T, .H, .T, .H, .T, .H, .T, .H]
    ⟨6, ⟨4, 4, -1, 1⟩, ⟨5, -1, 2, 0⟩, ⟨0, 2, -1, 5⟩, ⟨-1, 1, -4, -4⟩⟩ 2
  let l3 := CliffordT.GateTrace.leaf [.T, .H, .T, .H, .T, .H, .T, .H]
    ⟨8, ⟨-3, 7, 6, 2⟩, ⟨8, 6, -7, 3⟩, ⟨-3, 7, -6, -8⟩, ⟨2, 6, 7, -3⟩⟩ 2
  let l4 := CliffordT.GateTrace.leaf [.T, .H, .S, .T, .H, .S, .T, .H]
    ⟨9, ⟨-4, -8, -1, 0⟩, ⟨6, 13, -1, 15⟩, ⟨-1, 13, 6, -15⟩, ⟨1, 8, 4, 0⟩⟩ 2
  let l5 := CliffordT.GateTrace.leaf [.T, .H, .T, .H, .T, .H, .S, .T]
    ⟨11, ⟨-17, 6, -6, 9⟩, ⟨16, -3, 21, 30⟩, ⟨-16, 30, 21, -3⟩, ⟨-17, -9, 6, -6⟩⟩ 1
  let l6 := CliffordT.GateTrace.leaf [.H, .S, .T, .H, .T, .H, .S, .T]
    ⟨12, ⟨-8, 3, 6, 16⟩, ⟨1, -11, -3, 60⟩, ⟨-60, 3, 11, -1⟩, ⟨16, 6, 3, -8⟩⟩ 2
  let l7 := CliffordT.GateTrace.leaf [.H, .T, .H, .T, .H, .T, .H, .T]
    ⟨14, ⟨-49, -29, 40, 45⟩, ⟨-69, 36, -56, 18⟩, ⟨18, -56, 36, -69⟩, ⟨-45, -40, 29, 49⟩⟩ 2
  let l8 := CliffordT.GateTrace.leaf [.H, .T, .H, .T, .H, .T, .H, .T]
    ⟨16, ⟨-24, -121, -75, 75⟩, ⟨-160, -52, 93, -46⟩, ⟨46, -93, 52, 160⟩, ⟨75, -75, -121, -24⟩⟩ 2
  let l9 := CliffordT.GateTrace.leaf [.H, .S]
    ⟨17, ⟨22, -214, -23, 235⟩, ⟨-85, -127, -28, -70⟩, ⟨127, 85, -70, -28⟩, ⟨-214, 22, -235, 23⟩⟩ 0
  .cat (.cat (.cat l0 l1) (.cat l2 (.cat l3 l4)))
    (.cat (.cat l5 l6) (.cat l7 (.cat l8 l9)))

theorem ns_23_31 : Complex.normSq (m23T31W.toCircuit.eval.1 0 0) =
    ((102034 : ℤ) + (-10361 : ℤ) * √2) / (2 : ℝ) ^ 17 :=
  traceCircuit_normSq_zero_zero m23T31W m23T31RawMat 102034 (-10361) rfl rfl
theorem m23T31_toff : m23T31W.toCircuit.count .TOFF = 0 := m23T31W.toCircuit_count_toff
theorem m23T31_t : m23T31W.toCircuit.count .T = 31 := m23T31W.toCircuit_count_t

/-- Ancilla-free `5`-qubit `72-T` (`31 + 31 + 10`, `0 TOFF`) `L = 30` splitter. -/
def factoredMag30T72Circuit : Circuit 5 :=
  factoredMag30Of m45T31W.toCircuit m23T31W.toCircuit
/-- Syntactic inverse `5`-qubit `72-T` (`0 TOFF`) circuit for `factoredMag30T72Circuit`. -/
def unprepFactoredMag30T72Circuit : Circuit 5 := factoredMag30T72Circuit.inverse
/-- `0`-scratch dynamic wrapper for `factoredMag30T72Circuit` (`72 T`, `0 TOFF`). -/
def factoredMag30T72Dyn {Var : Type} {N : ℕ} (r : QRegister 5 N) : DynamicCircuit Var N :=
  .circuit (factoredMag30T72Circuit.onRegister r)
/-- `0`-scratch inverse dynamic wrapper for `unprepFactoredMag30T72Circuit` (`72 T`, `0 TOFF`). -/
def unprepFactoredMag30T72Dyn {Var : Type} {N : ℕ} (r : QRegister 5 N) : DynamicCircuit Var N :=
  .circuit (unprepFactoredMag30T72Circuit.onRegister r)

@[simp] theorem factoredMag30T72Circuit_toff : factoredMag30T72Circuit.count .TOFF = 0 :=
  factoredMag30Of_count_toff _ _ m45T31_toff m23T31_toff
@[simp] theorem unprepFactoredMag30T72Circuit_toff :
    unprepFactoredMag30T72Circuit.count .TOFF = 0 := by simp [unprepFactoredMag30T72Circuit]
@[simp] theorem factoredMag30T72Circuit_t : factoredMag30T72Circuit.count .T = 72 := by
  rw [factoredMag30T72Circuit, factoredMag30Of_count_t, m45T31_t, m23T31_t]
@[simp] theorem unprepFactoredMag30T72Circuit_t :
    unprepFactoredMag30T72Circuit.count .T = 72 := by simp [unprepFactoredMag30T72Circuit]
@[simp] theorem countFactoredMag30T72Dyn_toff {Var : Type} {N : ℕ} (r : QRegister 5 N) :
    (factoredMag30T72Dyn (Var := Var) r).count .TOFF = 0 := by simp [factoredMag30T72Dyn]
@[simp] theorem countUnprepFactoredMag30T72Dyn_toff {Var : Type} {N : ℕ} (r : QRegister 5 N) :
    (unprepFactoredMag30T72Dyn (Var := Var) r).count .TOFF = 0 := by
  simp [unprepFactoredMag30T72Dyn]
@[simp] theorem countFactoredMag30T72Dyn_t {Var : Type} {N : ℕ} (r : QRegister 5 N) :
    (factoredMag30T72Dyn (Var := Var) r).count .T = 72 := by simp [factoredMag30T72Dyn]
@[simp] theorem countUnprepFactoredMag30T72Dyn_t {Var : Type} {N : ℕ} (r : QRegister 5 N) :
    (unprepFactoredMag30T72Dyn (Var := Var) r).count .T = 72 := by
  simp [unprepFactoredMag30T72Dyn]

theorem cleanRealizesFactoredMag30T72Dyn {Var : Type} [Fintype Var] [DecidableEq Var]
    {N sScr : ℕ} (v : Var) (r : QRegister 5 N) (rScr : QRegister sScr N)
    (hdisj : r.DisjointWires rScr) :
    CleanDyn.CleanRealizes v r rScr factoredMag30T72Circuit.eval (factoredMag30T72Dyn r) :=
  CleanDyn.CleanRealizes.circuit v r rScr hdisj factoredMag30T72Circuit
    factoredMag30T72Circuit_toff
theorem cleanRealizesUnprepFactoredMag30T72Dyn {Var : Type} [Fintype Var] [DecidableEq Var]
    {N sScr : ℕ} (v : Var) (r : QRegister 5 N) (rScr : QRegister sScr N)
    (hdisj : r.DisjointWires rScr) :
    CleanDyn.CleanRealizes v r rScr factoredMag30T72Circuit.eval⁻¹
      (unprepFactoredMag30T72Dyn r) := by
  rw [← Circuit.eval_inverse]
  exact CleanDyn.CleanRealizes.circuit v r rScr hdisj unprepFactoredMag30T72Circuit
    unprepFactoredMag30T72Circuit_toff
theorem factoredMag30T72Circuit_vanish (x : Fin (2 ^ 5)) (hx : 30 ≤ x.val) :
    (factoredMag30T72Circuit.eval.1 *ᵥ basisState 0) x = 0 :=
  factoredMag30Of_mulVec_zero_eq_zero_of_ge _ _ x hx

theorem factoredMag30T72Circuit_l1_le :
    (∑ x : Fin 30, |Complex.normSq
      ((factoredMag30T72Circuit.eval.1 *ᵥ basisState 0) ⟨x.val, by omega⟩) - 1 / 30|) ≤
      8835 / 10 ^ 13 := by
  obtain ⟨s2_lo, s2_hi⟩ := sqrt2_bounds
  have hp5 : Complex.normSq (m45T31W.toCircuit.eval.1 0 0) =
      ((84978 : ℝ) + (14057 : ℝ) * √2) / (2 : ℝ) ^ 17 := by simpa using ns_45_31
  have hp3 : Complex.normSq (m23T31W.toCircuit.eval.1 0 0) =
      ((102034 : ℝ) + (-10361 : ℝ) * √2) / (2 : ℝ) ^ 17 := by simpa using ns_23_31
  exact factoredMag30Of_l1_of_ns m45T31W.toCircuit m23T31W.toCircuit hp5 hp3
    (η5 := 353079 / 10 ^ 15) (η3 := 404977 / 10 ^ 15) (b1 := 88597 / 10 ^ 15)
    (b2 := 316382 / 10 ^ 15) (b3 := 441675 / 10 ^ 15) (b4 := 36699 / 10 ^ 15)
    (abs_le.mpr ⟨by linarith, by linarith⟩) (abs_le.mpr ⟨by linarith, by linarith⟩)
    (abs_le.mpr ⟨by linarith, by linarith⟩) (abs_le.mpr ⟨by linarith, by linarith⟩)
    (abs_le.mpr ⟨by linarith, by linarith⟩) (abs_le.mpr ⟨by linarith, by linarith⟩) (by norm_num)

attribute [irreducible] m45T31W m23T31W factoredMag30T72Circuit
  unprepFactoredMag30T72Circuit factoredMag30T72Dyn unprepFactoredMag30T72Dyn

/-! ## Section 2: `wInner2 = 18` Register Geometry & `23`-Wire `MuxSwap` (`Mux23Bundle`) -/

/-- `5`-wire index register `0..4` inside the `23`-wire `wNegIn`-free inner core
(`wInner2 = 18`). -/
def core23IdxReg : QRegister 5 23 := QRegister.block 0 5 (by decide)
/-- `14`-wire QROM output register `5..18` (`alt : 5`, `keep : 9`) inside `23`. -/
def core23Out14Reg : QRegister 14 23 := QRegister.block 5 14 (by decide)
/-- `19`-wire QROM register `0..18` (`idx : 5 ++ out : 14`) inside `23`. -/
def core23Qrom19Reg : QRegister 19 23 := QRegister.block 0 19 (by decide)
/-- `4`-wire packet register `19..22` inside `23`. -/
def core23PktReg : QRegister 4 23 := QRegister.block 19 4 (by decide)

/-- `(10 + 13)`-wire permutation register inside `23` (`idx ++ alt ++ pkt ++ keep`). -/
def core23MuxSwap23Reg : QRegister (10 + 13) 23 :=
  mkReg (fun i ↦ if i.val < 10 then i.val else if i.val < 14 then i.val + 9 else i.val - 4)
    (fun i ↦ by
      have := i.isLt
      split_ifs <;> omega)
    (fun i j h ↦ by
      have := i.isLt
      have := j.isLt
      split_ifs at h <;> omega)

/-- `23`-wire `wNegIn`-free core subregister `0..22` inside `mMidUB 18 = 24`. -/
def mid18Core23Reg : QRegister 23 (mMidUB 18) := QRegister.block 0 23 (by decide)
/-- `14`-wire alias output subregister `5..18` inside `mMidUB 18 = 24`. -/
def mid18AliasOutReg : QRegister 14 (mMidUB 18) := QRegister.block 5 14 (by decide)
/-- `24`-wire `mMidUB 18` prefix subregister `0..23` inside `mMidUB 18 + cBits`. -/
def midGen18MidReg (cBits : ℕ) : QRegister (mMidUB 18) (mMidUB 18 + cBits) :=
  QRegister.block 0 (mMidUB 18) (by omega)
/-- `cBits`-wire context suffix subregister `24..(24 + cBits - 1)` inside `mMidUB 18 + cBits`. -/
def midGen18CtxReg (cBits : ℕ) : QRegister cBits (mMidUB 18 + cBits) :=
  QRegister.block (mMidUB 18) cBits (by omega)

theorem midGen18Ctx_disjoint_mid (cBits : ℕ) :
    (midGen18CtxReg cBits).DisjointWires (midGen18MidReg cBits) :=
  QRegister.disjoint_iff.mpr fun _ j hij ↦ by
    have hv := congrArg Fin.val hij
    simp only [midGen18CtxReg, midGen18MidReg, QRegister.block_apply_val] at hv
    have := j.isLt
    omega

/-- `5`-wire `rBLoc 18` index subregister `0..4` inside `mMidUB 18 + cBits`. -/
def midGen18Idx5Reg (cBits : ℕ) : QRegister 5 (mMidUB 18 + cBits) :=
  (midGen18MidReg cBits).compose (mid18Core23Reg.compose core23IdxReg)
/-- `14`-wire alias output subregister `5..18` inside `mMidUB 18 + cBits`. -/
def midGen18AliasOutReg (cBits : ℕ) : QRegister 14 (mMidUB 18 + cBits) :=
  (midGen18MidReg cBits).compose mid18AliasOutReg
/-- `4`-wire packet coin subregister `19..22` inside `mMidUB 18 + cBits`. -/
def midGen18Pkt4Reg (cBits : ℕ) : QRegister 4 (mMidUB 18 + cBits) :=
  (midGen18MidReg cBits).compose (mid18Core23Reg.compose core23PktReg)
/-- `23`-wire fused `MuxSwap` subregister inside `mMidUB 18 + cBits`. -/
def midGen18MuxSwap23Reg (cBits : ℕ) : QRegister (10 + 13) (mMidUB 18 + cBits) :=
  (midGen18MidReg cBits).compose (mid18Core23Reg.compose core23MuxSwap23Reg)
/-- `1`-wire `sig_in` subregister (`23`) inside `mMidUB 18 + cBits`. -/
def midGen18Sig1Reg (cBits : ℕ) : QRegister 1 (mMidUB 18 + cBits) :=
  (midGen18MidReg cBits).compose (rSigInLoc 18)

/-- Wire index map for `midGen18QromReg` (`idx(0..4) ++ ctxSub ++ out(5..18)`). -/
def midGen18QromWire (cBits addrCtx : ℕ) (ctxSub : QRegister addrCtx cBits)
    (i : Fin (5 + addrCtx + 14)) : Wire (mMidUB 18 + cBits) :=
  if h1 : i.val < 5 then ⟨i.val, show i.val < 24 + cBits by omega⟩
  else if h2 : i.val < 5 + addrCtx then
    ⟨mMidUB 18 + (ctxSub ⟨i.val - 5, by omega⟩).val, by
      have := (ctxSub ⟨i.val - 5, by omega⟩).isLt
      omega⟩
  else ⟨5 + (i.val - (5 + addrCtx)), show 5 + (i.val - (5 + addrCtx)) < 24 + cBits by omega⟩

/-- `(5 + addrCtx + 14)`-wire QROM subregister `idx(0..4) ++ ctxSub ++ out(5..18)` inside
`mMidUB 18 + cBits`. -/
def midGen18QromReg (cBits addrCtx : ℕ) (ctxSub : QRegister addrCtx cBits) :
    QRegister (5 + addrCtx + 14) (mMidUB 18 + cBits) :=
  ⟨⟨midGen18QromWire cBits addrCtx ctxSub, fun i j hij ↦ by
    have hv := congrArg Fin.val hij
    have hi := i.isLt
    have hj := j.isLt
    dsimp only [midGen18QromWire, mMidUB] at hv
    by_cases h1i : i.val < 5 <;> by_cases h1j : j.val < 5
    · simp only [h1i, h1j, ↓reduceDIte] at hv
      exact Fin.ext hv
    · by_cases h2j : j.val < 5 + addrCtx <;> simp only [h1i, h1j, h2j, ↓reduceDIte] at hv <;> omega
    · by_cases h2i : i.val < 5 + addrCtx <;> simp only [h1i, h1j, h2i, ↓reduceDIte] at hv <;> omega
    · by_cases h2i : i.val < 5 + addrCtx <;> by_cases h2j : j.val < 5 + addrCtx
      · simp only [h1i, h1j, h2i, h2j, ↓reduceDIte] at hv
        have hcEq : (ctxSub ⟨i.val - 5, by omega⟩).val =
            (ctxSub ⟨j.val - 5, by omega⟩).val := by omega
        have hc := congrArg Fin.val (ctxSub.wires.injective (Fin.ext hcEq))
        simp only at hc
        exact Fin.ext (by omega)
      · simp only [h1i, h1j, h2i, h2j, ↓reduceDIte] at hv
        dsimp [mMidUB] at hv
        omega
      · simp only [h1i, h1j, h2i, h2j, ↓reduceDIte] at hv
        dsimp [mMidUB] at hv
        omega
      · simp only [h1i, h1j, h2i, h2j, ↓reduceDIte] at hv
        exact Fin.ext (by omega)⟩⟩

@[simp] theorem midGen18QromReg_apply_val (cBits addrCtx : ℕ) (ctxSub : QRegister addrCtx cBits)
    (i : Fin (5 + addrCtx + 14)) :
    (midGen18QromReg cBits addrCtx ctxSub i).val =
      if h1 : i.val < 5 then i.val
      else if h2 : i.val < 5 + addrCtx then mMidUB 18 + (ctxSub ⟨i.val - 5, by omega⟩).val
      else 5 + (i.val - (5 + addrCtx)) := by
  change (midGen18QromWire cBits addrCtx ctxSub i).val = _
  dsimp only [midGen18QromWire]
  split_ifs <;> rfl

theorem qromGen18_eq_muxUnitary {cBits addrCtx : ℕ} (ctxSub : QRegister addrCtx cBits)
    (F : Fin (2 ^ (5 + addrCtx)) → BitAssignment 14) :
    (midGen18QromReg cBits addrCtx ctxSub).embedUnitary
        (aliasTableXorUnitary (5 + addrCtx) 14 F) =
      muxUnitary (midGen18CtxReg cBits) (midGen18MidReg cBits) (midGen18Ctx_disjoint_mid cBits)
        (fun c ↦ (mid18Core23Reg.compose core23Qrom19Reg).embedUnitary
          (aliasTableXorUnitary 5 14 (fun x ↦ F (combineAddr x (ctxSub.extractIndex c))))) := by
  refine Subtype.ext (matrix_ext_ket fun β ↦ ?_)
  let g₀ := (basisBits (mMidUB 18 + cBits)).symm β
  let c₀ := (midGen18CtxReg cBits).extractIndex g₀
  have hg₀ (g' : Fin (2 ^ (mMidUB 18 + cBits)))
      (h : (midGen18CtxReg cBits).extractIndex g' ≠ c₀) : CoherentAlias.ket β g' = 0 := by
    change basisState g₀ g' = 0
    rw [basisState, Pi.single_eq_of_ne]
    rintro rfl
    exact h rfl
  rw [muxUnitary_mulVec_of_proj (midGen18CtxReg cBits) (midGen18MidReg cBits)
    (midGen18Ctx_disjoint_mid cBits) _ c₀ _ hg₀, ← QRegister.embedUnitary_val,
    ← QRegister.embedUnitary_compose]
  let rQ19 : QRegister 19 (mMidUB 18 + cBits) :=
    QRegister.block 0 19 (show 0 + 19 ≤ 24 + cBits by omega)
  have hrQ19_eq : (midGen18MidReg cBits).compose (mid18Core23Reg.compose core23Qrom19Reg) = rQ19 :=
    CoherentAlias.qreg_ext fun _ ↦ by simp [midGen18MidReg, mid18Core23Reg, core23Qrom19Reg, rQ19]
  rw [hrQ19_eq, aliasTableXorUnitary, aliasTableXorUnitary,
    embedUnitary_bitPermUnitary_mulVec_ket, embedUnitary_bitPermUnitary_mulVec_ket]
  dsimp only [Equiv.coe_fn_mk]
  let x₀ : Fin (2 ^ 5) :=
    (basisBits 5).symm fun i ↦ β ⟨i.val, show i.val < 24 + cBits by omega⟩
  have hc₀_b (j : Fin addrCtx) : basisBits addrCtx (ctxSub.extractIndex c₀) j =
      β ⟨mMidUB 18 + (ctxSub j).val, by
        have := (ctxSub j).isLt
        omega⟩ := by
    rw [QRegister.basisBits_extractIndex, QRegister.basisBits_extractIndex, basisBits_symm_apply]
    exact congrArg β (Fin.ext (by simp [midGen18CtxReg]))
  have haddr : (basisBits (5 + addrCtx)).symm
      (fun i ↦ β ((midGen18QromReg cBits addrCtx ctxSub) ⟨i.val, by omega⟩)) =
      combineAddr x₀ (ctxSub.extractIndex c₀) := by
    dsimp only [combineAddr]
    refine congrArg (basisBits (5 + addrCtx)).symm (funext fun i ↦ ?_)
    have hx₀_b : basisBits 5 x₀ = fun j ↦ β ⟨j.val, show j.val < 24 + cBits by omega⟩ :=
      basisBits_symm_apply _
    by_cases h1 : i.val < 5
    · simp only [h1, ↓reduceDIte, hx₀_b]
      exact congrArg β (Fin.ext (by simp [h1]))
    · simp only [h1, ↓reduceDIte, hc₀_b]
      have h2 : i.val < 5 + addrCtx := i.isLt
      exact congrArg β (Fin.ext (by simp [h1, h2]))
  refine congrArg CoherentAlias.ket (funext fun w ↦ ?_)
  by_cases hw1 : w ∈ Set.range (midGen18QromReg cBits addrCtx ctxSub).wires
  · obtain ⟨i, rfl⟩ := hw1
    rw [writeReg_apply_reg]
    dsimp only [aliasTableXorBits]
    by_cases hi : 5 + addrCtx ≤ i.val
    · let k : Fin 14 := ⟨i.val - (5 + addrCtx), by omega⟩
      have hrw : midGen18QromReg cBits addrCtx ctxSub i = rQ19 ⟨5 + k.val, by omega⟩ :=
        Fin.ext (by simp [rQ19, k, show ¬ i.val < 5 by omega, show ¬ i.val < 5 + addrCtx by omega])
      rw [hrw, writeReg_apply_reg]
      dsimp only [aliasTableXorBits]
      have hge5 : 5 ≤ (⟨5 + k.val, by omega⟩ : Wire 19).val := show 5 ≤ 5 + k.val by omega
      have hxEq : (basisBits 5).symm (fun b ↦ β (rQ19 ⟨b.val, by omega⟩)) = x₀ := rfl
      simp only [hi, hge5, ↓reduceDIte, haddr, hxEq]
      exact congrArg₂ (· + ·) rfl (congrArg (F (combineAddr x₀ (ctxSub.extractIndex c₀)))
        (Fin.ext (by
          dsimp [k]
          omega)))
    · simp only [hi, ↓reduceDIte]
      by_cases hi5 : i.val < 5
      · have hrw : midGen18QromReg cBits addrCtx ctxSub i = rQ19 ⟨i.val, by omega⟩ :=
          Fin.ext (by simp [rQ19, hi5])
        rw [hrw, writeReg_apply_reg]
        dsimp only [aliasTableXorBits]
        have hn5 : ¬ (5 ≤ (⟨i.val, by omega⟩ : Wire 19).val) := show ¬ 5 ≤ i.val by omega
        simp only [hn5, ↓reduceDIte]
      · have hnot : midGen18QromReg cBits addrCtx ctxSub i ∉ Set.range rQ19.wires := by
          rintro ⟨u, hu⟩
          have hv := congrArg Fin.val hu
          simp [rQ19, hi5, show i.val < 5 + addrCtx by omega, mMidUB] at hv
          have := u.isLt
          omega
        exact (writeReg_apply_of_not_mem _ _ _ _ hnot).symm
  · rw [writeReg_apply_of_not_mem _ _ _ _ hw1]
    have hnot : w ∉ Set.range rQ19.wires := fun ⟨u, hu⟩ ↦ by
      subst hu
      apply hw1
      by_cases hu5 : u.val < 5
      · exact ⟨⟨u.val, by omega⟩, Fin.ext (by simp [rQ19, hu5])⟩
      · exact ⟨⟨5 + addrCtx + (u.val - 5), by omega⟩, Fin.ext (by
            simp [rQ19, show ¬ (5 + addrCtx + (u.val - 5) < 5) by omega,
              show ¬ (5 + addrCtx + (u.val - 5) < 5 + addrCtx) by omega]
            omega)⟩
    exact (writeReg_apply_of_not_mem _ _ _ _ hnot).symm

/-- `7`-wire `xo[0..6]` prefix inside `(7 + 128)`. -/
def mid159Xo7InCtx : QRegister 7 (7 + 128) := QRegister.block 0 7 (by decide)
/-- `7`-wire `xo[0..6]` subregister (`24..30`) inside `mMidUB 18 + (7 + 128) = 159`. -/
def mid159Xo7Reg : QRegister 7 (mMidUB 18 + (7 + 128)) :=
  (midGen18CtxReg (7 + 128)).compose mid159Xo7InCtx
/-- `128`-wire `rHot128` subregister (`31..158`) inside `mMidUB 18 + (7 + 128) = 159`. -/
def mid159Hot128Reg : QRegister 128 (mMidUB 18 + (7 + 128)) :=
  (midGen18CtxReg (7 + 128)).compose mid161Hot128InCtx
/-- `147`-wire (`5 + 128 + 14`) QROM subregister inside `mMidUB 18 + (7 + 128) = 159`. -/
def mid159QroReg : QRegister (5 + 128 + 14) (mMidUB 18 + (7 + 128)) :=
  midGen18QromReg (7 + 128) 128 mid161Hot128InCtx
/-- `5`-wire `rBLoc 18` index subregister inside `mMidUB 18 + (7 + 128) = 159`. -/
abbrev mid159Idx5Reg : QRegister 5 (mMidUB 18 + (7 + 128)) := midGen18Idx5Reg (7 + 128)
/-- `14`-wire alias output subregister inside `mMidUB 18 + (7 + 128) = 159`. -/
abbrev mid159AliasOutReg : QRegister 14 (mMidUB 18 + (7 + 128)) := midGen18AliasOutReg (7 + 128)
/-- `157`-wire coherent-alias subregister (`aliasActBits 5 128 9 0`) inside `159`. -/
def mid159ToAlias157 : QRegister (CoherentAlias.aliasActBits 5 128 9 0) (mMidUB 18 + (7 + 128)) :=
  mkReg (fun u ↦ if u.val < 5 then u.val else if u.val < 133 then 26 + u.val else u.val - 128)
    (fun u ↦ by
      have := u.isLt
      dsimp [aliasActBits, aliasQromBits, aliasOutBits] at this
      change _ < 159
      split_ifs <;> omega)
    (fun i j hij ↦ by
      have hi := i.isLt
      have hj := j.isLt
      dsimp [aliasActBits, aliasQromBits, aliasOutBits] at hi hj
      split_ifs at hij <;> omega)
theorem mid159ToAlias157_compose_qrom :
    mid159ToAlias157.compose (CoherentAlias.aliasQromReg 5 128 9 0) = mid159QroReg :=
  CoherentAlias.qreg_ext (by decide)
theorem mid159ToAlias157_compose_out :
    mid159ToAlias157.compose (AliasPrep.aliasOutReg 5 128 9 0) = mid159AliasOutReg :=
  CoherentAlias.qreg_ext (by decide)
theorem mid159ToAlias157_compose_ctx :
    mid159ToAlias157.compose (CoherentAlias.aliasCtxReg 5 128 9 0) = mid159Hot128Reg :=
  CoherentAlias.qreg_ext (by decide)

/-- `12`-wire `(idx:5 ++ rc:7)` address subregister `0..4 ++ 24..30` inside `mMidUB 18 + 7 = 31`. -/
def mid31IdxCtx12Reg : QRegister 12 (mMidUB 18 + 7) :=
  ⟨⟨fun i ↦ if i.val < 5 then ⟨i.val, show i.val < 24 + 7 by omega⟩
    else ⟨19 + i.val, show 19 + i.val < 24 + 7 by omega⟩, by decide⟩⟩
/-- `26`-wire (`5 + 7 + 14`) QROM subregister inside `mMidUB 18 + 7 = 31`. -/
def mid31Qrom26Reg : QRegister (5 + 7 + 14) (mMidUB 18 + 7) :=
  midGen18QromReg 7 7 (QRegister.whole 7)
/-- `5`-wire `rBLoc 18` index subregister inside `mMidUB 18 + 7 = 31`. -/
abbrev mid31Idx5Reg : QRegister 5 (mMidUB 18 + 7) := midGen18Idx5Reg 7
/-- `14`-wire alias output subregister inside `mMidUB 18 + 7 = 31`. -/
abbrev mid31AliasOutReg : QRegister 14 (mMidUB 18 + 7) := midGen18AliasOutReg 7
theorem mid31IdxCtx12_disjoint_aliasOut : mid31IdxCtx12Reg.DisjointWires mid31AliasOutReg :=
  QRegister.disjoint_iff.mpr (by decide)

/-- `5`-pair swap bit map on `10` wires (`0..4 ↔ 5..9`). -/
def swap5PairsBits (β : BitAssignment 10) : BitAssignment 10 :=
  fun w ↦ if h : w.val < 5 then β ⟨5 + w.val, by omega⟩ else β ⟨w.val - 5, by omega⟩
theorem swap5PairsBits_invol : Function.Involutive swap5PairsBits := fun β ↦ funext fun w ↦ by
  have hw := w.isLt
  dsimp only [swap5PairsBits]
  by_cases h : w.val < 5
  · have hn : ¬ (5 + w.val < 5) := by omega
    simp only [h, hn, ↓reduceDIte]
    exact congrArg β (Fin.ext (show 5 + w.val - 5 = w.val by omega))
  · have hy : w.val - 5 < 5 := by omega
    simp only [h, hy, ↓reduceDIte]
    exact congrArg β (Fin.ext (show 5 + (w.val - 5) = w.val by omega))
/-- Involutive bit-permutation equivalence for `swap5PairsBits`. -/
def swap5PairsPerm : Equiv.Perm (BitAssignment 10) :=
  ⟨swap5PairsBits, swap5PairsBits, swap5PairsBits_invol, swap5PairsBits_invol⟩
@[simp] theorem swap5PairsPerm_apply (β : BitAssignment 10) :
    swap5PairsPerm β = swap5PairsBits β := rfl
/-- Unconditional `5`-pair bit-permutation unitary on `10` wires. -/
noncomputable def swap5PairsUnitary : Unitary (2 ^ 10) := bitPermUnitary swap5PairsPerm

theorem swap5PairsUnitary_sq : swap5PairsUnitary * swap5PairsUnitary = 1 := by
  refine Subtype.ext (matrix_ext_ket fun β ↦ ?_)
  rw [Submonoid.coe_mul, ← Matrix.mulVec_mulVec, swap5PairsUnitary,
    ← QRegister.whole_embedUnitary (bitPermUnitary swap5PairsPerm),
    embedUnitary_bitPermUnitary_mulVec_ket, embedUnitary_bitPermUnitary_mulVec_ket,
    Submonoid.coe_one, Matrix.one_mulVec]
  refine congrArg CoherentAlias.ket (funext fun u ↦ ?_)
  have hw (q : Wire 10) : (QRegister.whole 10).wires q = q := rfl
  have h1 : (fun i : Fin 10 ↦
      writeReg β (QRegister.whole 10) (swap5PairsPerm fun j ↦ β ((QRegister.whole 10).wires j))
        ((QRegister.whole 10).wires i)) = swap5PairsPerm β :=
    funext fun i ↦ by
      rw [writeReg_apply_reg]
      rfl
  conv_lhs => rw [← hw u, writeReg_apply_reg]
  rw [h1, swap5PairsPerm_apply, swap5PairsPerm_apply, swap5PairsBits_invol β]

/-- Parametric `(10 + 13)`-wire (`10` swap targets `++` `4` packet `++` `9` keep) mux-swap unitary
for any `muxBit : Fin (2 ^ 4) → Fin (2 ^ 9) → Bool`. -/
noncomputable def pktMuxSwap23Unitary (muxBit : Fin (2 ^ 4) → Fin (2 ^ 9) → Bool) :
    Unitary (2 ^ (10 + 13)) :=
  muxOnAct 10 13 (fun x ↦
    if muxBit (finOfBits 4 fun i ↦ x ⟨i.val, by omega⟩)
        (finOfBits 9 fun j ↦ x ⟨4 + j.val, by omega⟩) then swap5PairsUnitary else 1)

/-- Exact bit-permutation action of `pktMuxSwap23Unitary muxBit` on `BitAssignment (10 + 13)`. -/
def pktMuxSwap23Bits (muxBit : Fin (2 ^ 4) → Fin (2 ^ 9) → Bool)
    (β : BitAssignment (10 + 13)) : BitAssignment (10 + 13) :=
  let sw := muxBit (finOfBits 4 fun i ↦ decide (β ⟨10 + i.val, by omega⟩ = 1))
    (finOfBits 9 fun j ↦ decide (β ⟨14 + j.val, by omega⟩ = 1))
  fun u ↦
    if h1 : u.val < 5 then if sw then β ⟨5 + u.val, by omega⟩ else β u
    else if h2 : u.val < 10 then if sw then β ⟨u.val - 5, by omega⟩ else β u
    else β u

theorem pktMuxSwap23Bits_invol (muxBit : Fin (2 ^ 4) → Fin (2 ^ 9) → Bool) :
    Function.Involutive (pktMuxSwap23Bits muxBit) := fun β ↦ funext fun u ↦ by
  have hu := u.isLt
  have hge10 (q : Wire (10 + 13)) (hq : 10 ≤ q.val) : pktMuxSwap23Bits muxBit β q = β q := by
    dsimp only [pktMuxSwap23Bits]
    simp [show ¬ q.val < 5 by omega, show ¬ q.val < 10 by omega]
  have hp : (fun i : Fin 4 ↦ decide (pktMuxSwap23Bits muxBit β ⟨10 + i.val, by omega⟩ = 1)) =
      fun i : Fin 4 ↦ decide (β ⟨10 + i.val, by omega⟩ = 1) :=
    funext fun i ↦ congrArg (fun z ↦ decide (z = 1)) (hge10 _ (show 10 ≤ 10 + i.val by omega))
  have hk : (fun j : Fin 9 ↦ decide (pktMuxSwap23Bits muxBit β ⟨14 + j.val, by omega⟩ = 1)) =
      fun j : Fin 9 ↦ decide (β ⟨14 + j.val, by omega⟩ = 1) :=
    funext fun j ↦ congrArg (fun z ↦ decide (z = 1)) (hge10 _ (show 10 ≤ 14 + j.val by omega))
  conv_lhs => rw [pktMuxSwap23Bits]
  dsimp only
  rw [hp, hk]
  by_cases h1 : u.val < 5
  · simp only [h1, ↓reduceDIte]
    cases hsw : muxBit (finOfBits 4 fun i ↦ decide (β ⟨10 + i.val, by omega⟩ = 1))
        (finOfBits 9 fun j ↦ decide (β ⟨14 + j.val, by omega⟩ = 1))
    · simp [pktMuxSwap23Bits, hsw]
    · simp only [↓reduceIte]
      dsimp only [pktMuxSwap23Bits]
      simp only [show ¬ 5 + u.val < 5 by omega, show 5 + u.val < 10 by omega, ↓reduceDIte, hsw,
        ↓reduceIte]
      exact congrArg β (Fin.ext (show 5 + u.val - 5 = u.val by omega))
  · by_cases h2 : u.val < 10
    · simp only [h1, h2, ↓reduceDIte]
      cases hsw : muxBit (finOfBits 4 fun i ↦ decide (β ⟨10 + i.val, by omega⟩ = 1))
          (finOfBits 9 fun j ↦ decide (β ⟨14 + j.val, by omega⟩ = 1))
      · simp [pktMuxSwap23Bits, hsw]
      · simp only [↓reduceIte]
        dsimp only [pktMuxSwap23Bits]
        simp only [show u.val - 5 < 5 by omega, ↓reduceDIte, hsw, ↓reduceIte]
        exact congrArg β (Fin.ext (show 5 + (u.val - 5) = u.val by omega))
    · simp only [h1, h2, ↓reduceDIte]
      exact hge10 u (by omega)

/-- Involutive bit-permutation equivalence for `pktMuxSwap23Bits muxBit`. -/
def pktMuxSwap23Perm (muxBit : Fin (2 ^ 4) → Fin (2 ^ 9) → Bool) :
    Equiv.Perm (BitAssignment (10 + 13)) :=
  ⟨pktMuxSwap23Bits muxBit, pktMuxSwap23Bits muxBit,
    pktMuxSwap23Bits_invol muxBit, pktMuxSwap23Bits_invol muxBit⟩
@[simp] theorem pktMuxSwap23Perm_apply (muxBit : Fin (2 ^ 4) → Fin (2 ^ 9) → Bool)
    (β : BitAssignment (10 + 13)) :
    pktMuxSwap23Perm muxBit β = pktMuxSwap23Bits muxBit β := rfl

theorem pktMuxSwap23Unitary_mulVec_ket (muxBit : Fin (2 ^ 4) → Fin (2 ^ 9) → Bool)
    (β : BitAssignment (10 + 13)) :
    (pktMuxSwap23Unitary muxBit).1 *ᵥ CoherentAlias.ket β =
      CoherentAlias.ket (pktMuxSwap23Bits muxBit β) := by
  let c := (QRegister.block 10 13 (by omega)).extractIndex ((basisBits (10 + 13)).symm β)
  have hL : (pktMuxSwap23Unitary muxBit).1 *ᵥ CoherentAlias.ket β =
      ((QRegister.block 0 10 (by omega)).embedMatrix
        (if muxBit (finOfBits 4 fun i ↦ bitsOfFin 13 c ⟨i.val, by omega⟩)
            (finOfBits 9 fun j ↦ bitsOfFin 13 c ⟨4 + j.val, by omega⟩) then
          swap5PairsUnitary else 1).1) *ᵥ CoherentAlias.ket β := by
    dsimp only [pktMuxSwap23Unitary, muxOnAct]
    exact muxUnitary_mulVec_of_proj (QRegister.block 10 13 (by omega))
      (QRegister.block 0 10 (by omega)) _ _ c (CoherentAlias.ket β) (fun q hq ↦ by
        rw [CoherentAlias.ket, basisState, Pi.single_eq_of_ne]
        rintro rfl
        exact hq rfl)
  have hc : bitsOfFin 13 c = fun u ↦ decide (β ⟨10 + u.val, by omega⟩ = 1) := funext fun u ↦ by
    dsimp only [bitsOfFin, c]
    rw [QRegister.basisBits_extractIndex, basisBits_symm_apply]
    rfl
  rw [hL, hc]
  have hkEq : (fun j : Fin 9 ↦ decide (β ⟨10 + (4 + j.val), by omega⟩ = 1)) =
      fun j : Fin 9 ↦ decide (β ⟨14 + j.val, by omega⟩ = 1) :=
    funext fun j ↦ congrArg (fun q ↦ decide (β q = 1))
      (Fin.ext (show 10 + (4 + j.val) = 14 + j.val by omega))
  rw [hkEq]
  let sw := muxBit (finOfBits 4 fun i ↦ decide (β ⟨10 + i.val, by omega⟩ = 1))
    (finOfBits 9 fun j ↦ decide (β ⟨14 + j.val, by omega⟩ = 1))
  by_cases hsw : sw = true
  · rw [ite_eq_left hsw, ← QRegister.embedUnitary_val, swap5PairsUnitary,
      embedUnitary_bitPermUnitary_mulVec_ket, swap5PairsPerm_apply]
    refine congrArg CoherentAlias.ket (funext fun u ↦ ?_)
    have hu := u.isLt
    by_cases h10 : u.val < 10
    · have hj : QRegister.block 0 10 (by omega) ⟨u.val, h10⟩ = u := Fin.ext (by simp)
      conv_lhs => rw [← hj, writeReg_apply_reg]
      dsimp only [swap5PairsBits, pktMuxSwap23Bits]
      have hswt : muxBit (finOfBits 4 fun i ↦ decide (β ⟨10 + i.val, by omega⟩ = 1))
          (finOfBits 9 fun j ↦ decide (β ⟨14 + j.val, by omega⟩ = 1)) = true := hsw
      by_cases h5 : u.val < 5
      · simp only [h5, ↓reduceDIte, hswt, ↓reduceIte]
        exact congrArg β (Fin.ext (by simp))
      · simp only [h5, h10, ↓reduceDIte, hswt, ↓reduceIte]
        exact congrArg β (Fin.ext (by simp))
    · have hnm : u ∉ Set.range (QRegister.block 0 10 (by omega)).wires := by
        rintro ⟨j, hj⟩
        have hv := congrArg Fin.val hj
        simp at hv
        omega
      rw [writeReg_apply_of_not_mem _ _ _ _ hnm]
      dsimp only [pktMuxSwap23Bits]
      have n5 : ¬ (u.val < 5) := by omega
      simp only [n5, h10, ↓reduceDIte]
  · rw [ite_eq_right hsw, Submonoid.coe_one, QRegister.embedMatrix_one, Matrix.one_mulVec]
    refine congrArg CoherentAlias.ket (funext fun u ↦ ?_)
    dsimp only [pktMuxSwap23Bits]
    have hswf : sw = false := Bool.eq_false_iff.mpr hsw
    by_cases h5 : u.val < 5
    · simp only [h5, ↓reduceDIte, show muxBit _ _ = false from hswf, Bool.false_eq_true, ↓reduceIte]
    · by_cases h10 : u.val < 10
      · simp only [h5, h10, ↓reduceDIte, show muxBit _ _ = false from hswf, Bool.false_eq_true,
          ↓reduceIte]
      · simp only [h5, h10, ↓reduceDIte]

theorem pktMuxSwap23Unitary_eq_bitPermUnitary (muxBit : Fin (2 ^ 4) → Fin (2 ^ 9) → Bool) :
    pktMuxSwap23Unitary muxBit = bitPermUnitary (pktMuxSwap23Perm muxBit) := by
  rw [← QRegister.whole_embedUnitary (bitPermUnitary (pktMuxSwap23Perm muxBit))]
  refine Subtype.ext (matrix_ext_ket fun β ↦ ?_)
  rw [pktMuxSwap23Unitary_mulVec_ket muxBit β, embedUnitary_bitPermUnitary_mulVec_ket]
  refine congrArg CoherentAlias.ket (funext fun u ↦ ?_)
  have hw : (QRegister.whole (10 + 13)).wires u = u := rfl
  conv_rhs => rw [← hw, writeReg_apply_reg]
  rfl
theorem pktMuxSwap23Unitary_inv (muxBit : Fin (2 ^ 4) → Fin (2 ^ 9) → Bool) :
    (pktMuxSwap23Unitary muxBit)⁻¹ = pktMuxSwap23Unitary muxBit := by
  refine (eq_inv_of_mul_eq_one_left ?_).symm
  dsimp only [pktMuxSwap23Unitary, muxOnAct]
  rw [muxUnitary_mul]
  have h1 : (fun c : Fin (2 ^ 13) ↦
      (if muxBit (finOfBits 4 fun i ↦ bitsOfFin 13 c ⟨i.val, by omega⟩)
          (finOfBits 9 fun j ↦ bitsOfFin 13 c ⟨4 + j.val, by omega⟩) then
        swap5PairsUnitary else 1) *
      (if muxBit (finOfBits 4 fun i ↦ bitsOfFin 13 c ⟨i.val, by omega⟩)
          (finOfBits 9 fun j ↦ bitsOfFin 13 c ⟨4 + j.val, by omega⟩) then
        swap5PairsUnitary else 1)) = fun _ ↦ 1 := funext fun c ↦ by
    cases muxBit (finOfBits 4 fun i ↦ bitsOfFin 13 c ⟨i.val, by omega⟩)
      (finOfBits 9 fun j ↦ bitsOfFin 13 c ⟨4 + j.val, by omega⟩)
    · simp
    · simpa only [↓reduceIte] using swap5PairsUnitary_sq
  rw [h1]
  apply Subtype.ext
  dsimp only [muxUnitary]
  simp only [Submonoid.coe_one, QRegister.embedMatrix_one, mul_one]
  exact QRegister.sum_basisOutcomeProjector _

/-- `14`-bit `wNegIn`-free slice target function on `(rc : Fin 128, x : Fin 32)` for
`keep9Hot24BoolTable`. -/
noncomputable def keep9SliceTargetFn14 (rc : Fin (2 ^ 7)) (x : Fin (2 ^ 5)) : BitAssignment 14 :=
  fun k ↦ if keep9Hot24BoolTable rc x k then 1 else 0
theorem hotLinearTargetFnKeep9Hot24BoolTable_oneHot (rc : Fin (2 ^ 7)) (cHot : Fin (2 ^ 128))
    (hcHot : ∀ c : Fin 128, basisBits 128 cHot c = if c = rc then 1 else 0) (x : Fin (2 ^ 5)) :
    MidReflCtxRetain.hotLinearTargetFn 5 128 14 keep9Hot24BoolTable
      (CoherentAlias.combineAddr x cHot) = keep9SliceTargetFn14 rc x :=
  MidReflCtxRetain.hotLinearTargetFn_combineAddr_oneHot keep9Hot24BoolTable x rc cHot hcHot
/-- Combined `23`-wire QROM + fused `pktMuxSwap23Unitary muxBit` permutation unitary. -/
noncomputable def coin9Perm23 (muxBit : Fin (2 ^ 4) → Fin (2 ^ 9) → Bool)
    (f : Fin (2 ^ 5) → BitAssignment 14) : Unitary (2 ^ 23) :=
  core23MuxSwap23Reg.embedUnitary (pktMuxSwap23Unitary muxBit) *
    core23Qrom19Reg.embedUnitary (aliasTableXorUnitary 5 14 f)
/-- `23`-wire `wNegIn`-free inner core unitary prior to spin `H` on wire `23`. -/
noncomputable def core23 (muxBit : Fin (2 ^ 4) → Fin (2 ^ 9) → Bool)
    (sliceFn : Fin (2 ^ 7) → Fin (2 ^ 5) → BitAssignment 14) (uIdx : Unitary (2 ^ 5))
    (rc : Fin (2 ^ 7)) : Unitary (2 ^ 23) :=
  coin9Perm23 muxBit (sliceFn rc) *
    (core23PktReg.embedUnitary optCoin9Unitary * core23IdxReg.embedUnitary uIdx)
/-- `24`-wire (`mMidUB 18`) `wNegIn`-free `PREP_mid` unitary family parameterized by `muxBit`
and `sliceFn`. -/
noncomputable def prepMid18FromSlice (muxBit : Fin (2 ^ 4) → Fin (2 ^ 9) → Bool)
    (sliceFn : Fin (2 ^ 7) → Fin (2 ^ 5) → BitAssignment 14) (uIdx : Unitary (2 ^ 5))
    (rc : Fin (2 ^ 7)) : Unitary (2 ^ mMidUB 18) :=
  (rSigInLoc 18).embedUnitary (Circuit.H 0).eval *
    mid18Core23Reg.embedUnitary (core23 muxBit sliceFn uIdx rc)
/-- Direct `rXo7UB`-controlled `PREP_mid` mux for `prepMid18FromSlice` at `wInner2 = 18`. -/
noncomputable abbrev directXo7Mux18Of (wOuter : ℕ) (muxBit : Fin (2 ^ 4) → Fin (2 ^ 9) → Bool)
    (sliceFn : Fin (2 ^ 7) → Fin (2 ^ 5) → BitAssignment 14) (uIdx : Unitary (2 ^ 5)) :
    Unitary (2 ^ nUB wOuter 18) :=
  muxUnitary (rXo7UB wOuter 18) (rMidUB wOuter 18) (disjoint_rXo7UB_rMidUB wOuter 18)
    (prepMid18FromSlice muxBit sliceFn uIdx)
/-- `π128`-permuted `14`-bit slice table `rc ↦ sliceFn (π128 rc)`. -/
abbrev genPi128SliceFn14 (sliceFn : Fin (2 ^ 7) → Fin (2 ^ 5) → BitAssignment 14)
    (π128 : Equiv.Perm (Fin (2 ^ 7))) : Fin (2 ^ 7) → Fin (2 ^ 5) → BitAssignment 14 :=
  fun rc ↦ sliceFn (π128 rc)
/-- `π128`-permuted `24`-wire (`mMidUB 18`) `PREP_mid` unitary family. -/
noncomputable abbrev genPi128PrepMid18Of (muxBit : Fin (2 ^ 4) → Fin (2 ^ 9) → Bool)
    (sliceFn : Fin (2 ^ 7) → Fin (2 ^ 5) → BitAssignment 14) (π128 : Equiv.Perm (Fin (2 ^ 7)))
    (uIdx : Unitary (2 ^ 5)) : Fin (2 ^ 7) → Unitary (2 ^ mMidUB 18) :=
  prepMid18FromSlice muxBit (genPi128SliceFn14 sliceFn π128) uIdx
/-- Direct `rXo7UB`-controlled `PREP_mid` mux for `genPi128PrepMid18Of` at `wInner2 = 18`. -/
noncomputable abbrev genPi128DirectXo7Mux18Of (wOuter : ℕ)
    (muxBit : Fin (2 ^ 4) → Fin (2 ^ 9) → Bool)
    (sliceFn : Fin (2 ^ 7) → Fin (2 ^ 5) → BitAssignment 14) (π128 : Equiv.Perm (Fin (2 ^ 7)))
    (uIdx : Unitary (2 ^ 5)) : Unitary (2 ^ nUB wOuter 18) :=
  directXo7Mux18Of wOuter muxBit (genPi128SliceFn14 sliceFn π128) uIdx
/-- Concrete `keep9SliceTargetFn14` `π128`-permuted `rXo7UB` mux at `wInner2 = 18`. -/
noncomputable abbrev pi128DirectXo7Mux18Of (wOuter : ℕ) (muxBit : Fin (2 ^ 4) → Fin (2 ^ 9) → Bool)
    (π128 : Equiv.Perm (Fin (2 ^ 7))) (uIdx : Unitary (2 ^ 5)) : Unitary (2 ^ nUB wOuter 18) :=
  genPi128DirectXo7Mux18Of wOuter muxBit keep9SliceTargetFn14 π128 uIdx
/-- Single-slice `24`-wire `PREP_mid` unitary at `wInner2 = 18` parameterized by `sliceAt`. -/
noncomputable abbrev branch18Of (muxBit : Fin (2 ^ 4) → Fin (2 ^ 9) → Bool)
    (uIdx : Unitary (2 ^ 5)) (sliceAt : Fin (2 ^ 5) → BitAssignment 14) : Unitary (2 ^ mMidUB 18) :=
  prepMid18FromSlice muxBit (fun _ ↦ sliceAt) uIdx 0
/-- `159`-wire (`mMidUB 18 + (7 + 128)`) one-hot branch unitary for `prepMid18FromSlice`. -/
noncomputable def hotBranch18Of (muxBit : Fin (2 ^ 4) → Fin (2 ^ 9) → Bool)
    (uIdx : Unitary (2 ^ 5)) (f133 : Fin (2 ^ (5 + 128)) → BitAssignment 14)
    (ctrl : Fin (7 + 128) → Bool) : Unitary (2 ^ mMidUB 18) :=
  branch18Of muxBit uIdx (fun x ↦ f133 (combineAddr x
    (finOfBits 128 (fun j ↦ ctrl (Fin.natAdd 7 j)))))

theorem genMux18_eq {cBits addrCtx : ℕ} (muxBit : Fin (2 ^ 4) → Fin (2 ^ 9) → Bool)
    (ctxSub : QRegister addrCtx cBits) (uIdx : Unitary (2 ^ 5))
    (F : Fin (2 ^ (5 + addrCtx)) → BitAssignment 14) :
    (midGen18Sig1Reg cBits).embedUnitary (Circuit.H 0).eval *
      ((midGen18MuxSwap23Reg cBits).embedUnitary (pktMuxSwap23Unitary muxBit) *
        ((midGen18QromReg cBits addrCtx ctxSub).embedUnitary
            (aliasTableXorUnitary (5 + addrCtx) 14 F) *
          ((midGen18Pkt4Reg cBits).embedUnitary optCoin9Unitary *
            (midGen18Idx5Reg cBits).embedUnitary uIdx))) =
      muxOnAct (mMidUB 18) cBits (fun y ↦ branch18Of muxBit uIdx
        (fun x ↦ F (combineAddr x (ctxSub.extractIndex (finOfBits cBits y))))) := by
  have hmEq := muxOnAct_finOfBits_eq_muxUnitary (k_t := mMidUB 18) (k_c := cBits)
    (fun c ↦ branch18Of muxBit uIdx (fun x ↦ F (combineAddr x (ctxSub.extractIndex c))))
  have embConst (A : Unitary (2 ^ mMidUB 18)) :
      (midGen18MidReg cBits).embedUnitary A =
        muxUnitary (midGen18CtxReg cBits) (midGen18MidReg cBits)
          (midGen18Ctx_disjoint_mid cBits) (fun _ ↦ A) := by
    apply Subtype.ext
    dsimp only [muxUnitary, QRegister.embedUnitary_val]
    rw [← Finset.sum_mul, (midGen18CtxReg cBits).sum_basisOutcomeProjector, one_mul]
  dsimp only [midGen18Sig1Reg, midGen18MuxSwap23Reg, midGen18Pkt4Reg, midGen18Idx5Reg]
  rw [hmEq, QRegister.embedUnitary_compose (midGen18MidReg cBits),
    QRegister.embedUnitary_compose (midGen18MidReg cBits),
    QRegister.embedUnitary_compose (midGen18MidReg cBits),
    QRegister.embedUnitary_compose (midGen18MidReg cBits),
    qromGen18_eq_muxUnitary ctxSub F, embConst _, embConst _, embConst _, embConst _,
    muxUnitary_mul, muxUnitary_mul, muxUnitary_mul, muxUnitary_mul]
  refine muxUnitary_congr _ _ fun c ↦ ?_
  dsimp only [branch18Of, prepMid18FromSlice, core23, coin9Perm23]
  simp only [QRegister.embedUnitary_mul, QRegister.embedUnitary_compose, mul_assoc]
theorem mux159_eq (muxBit : Fin (2 ^ 4) → Fin (2 ^ 9) → Bool) (uIdx : Unitary (2 ^ 5))
    (f133 : Fin (2 ^ (5 + 128)) → BitAssignment 14) :
    (midGen18Sig1Reg (7 + 128)).embedUnitary (Circuit.H 0).eval *
      ((midGen18MuxSwap23Reg (7 + 128)).embedUnitary (pktMuxSwap23Unitary muxBit) *
        (mid159QroReg.embedUnitary (aliasTableXorUnitary (5 + 128) 14 f133) *
          ((midGen18Pkt4Reg (7 + 128)).embedUnitary optCoin9Unitary *
            mid159Idx5Reg.embedUnitary uIdx))) =
      muxOnAct (mMidUB 18) (7 + 128) (hotBranch18Of muxBit uIdx f133) := by
  have hEx (y : Fin (7 + 128) → Bool) :
      mid161Hot128InCtx.extractIndex (finOfBits (7 + 128) y) =
        finOfBits 128 (fun j ↦ y (Fin.natAdd 7 j)) := by
    refine (basisBits 128).injective (funext fun j ↦ ?_)
    rw [QRegister.basisBits_extractIndex, finOfBits, finOfBits,
      SelectSwapQROM.basisBits_symm, SelectSwapQROM.basisBits_symm]
    rw [show mid161Hot128InCtx j = Fin.natAdd 7 j from
      Fin.ext (by simp [mid161Hot128InCtx, Fin.val_natAdd])]
  dsimp only [mid159QroReg, mid159Idx5Reg]
  rw [genMux18_eq muxBit mid161Hot128InCtx uIdx f133]
  refine congrArg (muxOnAct (mMidUB 18) (7 + 128)) (funext fun y ↦ ?_)
  dsimp only [hotBranch18Of]
  rw [hEx y]
theorem mux31_eq (muxBit : Fin (2 ^ 4) → Fin (2 ^ 9) → Bool) (uIdx : Unitary (2 ^ 5))
    (sliceFn : Fin (2 ^ 7) → Fin (2 ^ 5) → BitAssignment 14)
    (F : Fin (2 ^ (5 + 7)) → BitAssignment 14)
    (hF : ∀ (rc : Fin (2 ^ 7)) (x : Fin (2 ^ 5)), F (combineAddr x rc) = sliceFn rc x) :
    (midGen18Sig1Reg 7).embedUnitary (Circuit.H 0).eval *
      ((midGen18MuxSwap23Reg 7).embedUnitary (pktMuxSwap23Unitary muxBit) *
        (mid31Qrom26Reg.embedUnitary (aliasTableXorUnitary (5 + 7) 14 F) *
          ((midGen18Pkt4Reg 7).embedUnitary optCoin9Unitary *
            mid31Idx5Reg.embedUnitary uIdx))) =
      muxOnAct (mMidUB 18) 7
        (fun y ↦ prepMid18FromSlice muxBit sliceFn uIdx (finOfBits 7 y)) := by
  have hEx (y : Fin 7 → Bool) :
      (QRegister.whole 7).extractIndex (finOfBits 7 y) = finOfBits 7 y := by
    refine (basisBits 7).injective (funext fun j ↦ ?_)
    rw [QRegister.basisBits_extractIndex]
    rfl
  dsimp only [mid31Qrom26Reg, mid31Idx5Reg]
  rw [genMux18_eq muxBit (QRegister.whole 7) uIdx F]
  refine congrArg (muxOnAct (mMidUB 18) 7) (funext fun y ↦ ?_)
  rw [hEx y]
  simp_rw [hF]
  rfl

/-- One-hot `14`-bit slice-table contract `F (combineAddr x cHot) = sliceFn rc x` at `|e_rc⟩`. -/
abbrev HotTableSpec14 (F : Fin (2 ^ (5 + 128)) → BitAssignment 14)
    (sliceFn : Fin (2 ^ 7) → Fin (2 ^ 5) → BitAssignment 14) : Prop :=
  ∀ (rc : Fin (2 ^ 7)) (cHot : Fin (2 ^ 128)),
    (∀ c : Fin 128, basisBits 128 cHot c = if c = rc then 1 else 0) →
    ∀ x : Fin (2 ^ 5), F (combineAddr x cHot) = sliceFn rc x
theorem hotBranch18Of_stepOneHot_eq (muxBit : Fin (2 ^ 4) → Fin (2 ^ 9) → Bool)
    (uIdx : Unitary (2 ^ 5)) (sliceFn : Fin (2 ^ 7) → Fin (2 ^ 5) → BitAssignment 14)
    (f133 : Fin (2 ^ (5 + 128)) → BitAssignment 14) (hf : HotTableSpec14 f133 sliceFn)
    (y : Fin 7 → Bool) :
    hotBranch18Of muxBit uIdx f133 (stepOneHotCtrlBits y) =
      prepMid18FromSlice muxBit sliceFn uIdx (finOfBits 7 y) := by
  let rc := finOfBits 7 y
  let cHot := finOfBits 128 fun j ↦ stepOneHotCtrlBits y (Fin.natAdd 7 j)
  have hcHot (c : Fin 128) : basisBits 128 cHot c = if c = rc then 1 else 0 := by
    change basisBits 128 ((basisBits 128).symm _) c = _
    rw [SelectSwapQROM.basisBits_symm]
    dsimp only [stepOneHotCtrlBits]
    have hn : ¬ ((Fin.natAdd 7 c).val < 7) := show ¬ (7 + c.val < 7) by omega
    have hsub : (Fin.natAdd 7 c).val - 7 = c.val := show 7 + c.val - 7 = c.val by omega
    simp only [hn, ↓reduceDIte, hsub]
    by_cases h : c = rc
    · subst h
      simp [rc]
    · simp [h, show c.val ≠ rc.val from fun hv ↦ h (Fin.ext hv), rc]
  dsimp only [hotBranch18Of, branch18Of]
  unfold prepMid18FromSlice core23
  rw [show (fun x : Fin (2 ^ 5) ↦ f133 (combineAddr x cHot)) = sliceFn rc from
    funext (hf rc cHot hcHot)]
theorem hotBranch18OfCtrlPerstepOneHot_eq (muxBit : Fin (2 ^ 4) → Fin (2 ^ 9) → Bool)
    (sliceFn : Fin (2 ^ 7) → Fin (2 ^ 5) → BitAssignment 14) (π128 : Equiv.Perm (Fin (2 ^ 7)))
    (uIdx : Unitary (2 ^ 5)) (f133 : Fin (2 ^ (5 + 128)) → BitAssignment 14)
    (hf : HotTableSpec14 f133 sliceFn) (y : Fin 7 → Bool) :
    hotBranch18Of muxBit uIdx f133 (fun k ↦ stepOneHotCtrlBits y (ctrlPer π128 k)) =
      genPi128PrepMid18Of muxBit sliceFn π128 uIdx (finOfBits 7 y) := by
  let y' : Fin 7 → Bool := bitsOfFin 7 (π128 (finOfBits 7 y))
  have hHotEq (j : Fin 128) : stepOneHotCtrlBits y (ctrlPer π128 (Fin.natAdd 7 j)) =
      stepOneHotCtrlBits y' (Fin.natAdd 7 j) := by
    have hp : ctrlPer π128 (Fin.natAdd 7 j) = Fin.natAdd 7 (π128.symm j) := by
      change ctrlPer π128 (finSumFinEquiv (Sum.inr j)) =
        finSumFinEquiv (Sum.inr (π128.symm j))
      simp [ctrlPer]
    have hn (c : Fin 128) : ¬ ((Fin.natAdd 7 c).val < 7) ∧ (Fin.natAdd 7 c).val - 7 = c.val :=
      show ¬ (7 + c.val < 7) ∧ 7 + c.val - 7 = c.val by omega
    rw [hp]
    dsimp only [stepOneHotCtrlBits]
    simp only [(hn _).1, ↓reduceDIte, (hn _).2, y', finOfBits_bitsOfFin]
    exact decide_eq_decide.mpr (by
      simp only [← Fin.ext_iff]
      exact ⟨fun h ↦ by rw [← h, π128.apply_symm_apply],
        fun h ↦ by rw [h, π128.symm_apply_apply]⟩)
  have hBr : hotBranch18Of muxBit uIdx f133
      (fun k ↦ stepOneHotCtrlBits y (ctrlPer π128 k)) =
      hotBranch18Of muxBit uIdx f133 (stepOneHotCtrlBits y') := by
    dsimp only [hotBranch18Of]
    simp_rw [hHotEq]
  rw [hBr, hotBranch18Of_stepOneHot_eq muxBit uIdx sliceFn f133 hf y']
  dsimp only [y']
  rw [finOfBits_bitsOfFin]
  rfl
theorem crSet_of {Var : Type} [Fintype Var] [DecidableEq Var] {k N sScr : ℕ} {v : Var}
    {r : QRegister k N} {rScr : QRegister sScr N} {U : Unitary (2 ^ k)} {P : DynamicCircuit Var N}
    (h : CleanDyn.CleanRealizes v r rScr U P) :
    SelectSwapQROM.CleanRealizesSet v rScr.image (r.embedUnitary U) P :=
  (SelectSwapQROM.cleanRealizes_iff_set v r rScr U P).mp
    ((AliasPrep.cleanRealizes_sbx_iff v r rScr U P).mpr h)
theorem cr_of_compose {Var : Type} [Fintype Var] [DecidableEq Var] {M k N sScr : ℕ} {v : Var}
    {r : QRegister M N} {ri : QRegister k M} {rScr : QRegister sScr N} {U : Unitary (2 ^ k)}
    {P : DynamicCircuit Var N} (h : CleanDyn.CleanRealizes v (r.compose ri) rScr U P) :
    CleanDyn.CleanRealizes v r rScr (ri.embedUnitary U) P := by
  have hSet := crSet_of h
  rw [QRegister.embedUnitary_compose] at hSet
  exact (AliasPrep.cleanRealizes_sbx_iff v r rScr (ri.embedUnitary U) P).mp
    ((SelectSwapQROM.cleanRealizes_iff_set v r rScr (ri.embedUnitary U) P).mpr hSet)

/-! ## Section 3: Parametric `wInner2 = 18` `PREP_mid` & `44-T` `w = 3` One-Hot Alias Unloader -/

/-! ## Section 4: Parametric `14`-Plane `Symp14Spec R` Shared Symplectic Core (`4 * R` `T`) -/

end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.Inner18Symp14Walk
