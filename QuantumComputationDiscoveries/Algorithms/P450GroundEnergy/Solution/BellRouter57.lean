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

public import QuantumComputationSpecs.Algorithms.P450DFTHCData
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.Defs
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.LowBitPi145Select

/-!
# `57`-AND `π145` `SiZero` Router (`State24` Specification)

Defines the `57`-AND (`14 + 43`) `π145` `SiZero` router on `RouterStep 23` (`stepsA57`,
`stepsB57`) and proves its `State24` specification (`runSteps24StepsA57`,
`runSteps24StepsB57`), clean borrow return (`specA57_get24_23`, `specB57_borrows_false`),
and active-pair bound (`ctrl10_pair8_lt145_2`).

## References
- C. Jones, "Low-overhead constructions for the fault-tolerant Toffoli gate," *Phys. Rev. A* **87**,
  022328 (2013), DOI: `10.1103/PhysRevA.87.022328`.
- C. Gidney, "Halving the cost of quantum addition," *Quantum* **2**, 74 (2018),
  DOI: `10.22331/q-2018-06-18-74`.
- R. Babbush, C. Gidney, D. W. Berry, N. Wiebe, J. McClean, A. Paler, A. Fowler, and H. Neven,
  "Encoding Electronic Spectra in Quantum Circuits with Linear T Complexity," *Phys. Rev. X* **8**,
  041015 (2018), DOI: `10.1103/PhysRevX.8.041015`.
- D. W. Berry, C. Gidney, M. Motta, J. R. McClean, and R. Babbush, "Qubitization of Arbitrary
  Basis Quantum Chemistry Leveraging Sparsity and Low Rank Factorization," *Quantum* **3**, 208
  (2019), DOI: `10.22331/q-2019-12-02-208`.
- J. Lee, D. W. Berry, C. Gidney, W. J. Huggins, J. R. McClean, N. Wiebe, and R. Babbush,
  "Even More Efficient Quantum Computations of Chemistry Through Tensor Hypercontraction,"
  *PRX Quantum* **2**, 030305 (2021), DOI: `10.1103/PRXQuantum.2.030305`.
-/

@[expose] public section

namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.BellRouter57
open QuantumComputation.Specs QuantumComputation.Specs.P450

open Operator QProg Matrix HermitianMat Real CoherentAlias CleanDyn
open QuantumComputation.Specs QuantumComputation.Specs.P450
open CircuitModular GivensOps
open BlockEncodingCore BlockEncodingCircuit
open SelectSwapQROM GivensCascade
open SelectRouter10 TopIntegrationBridge
open Lac2Fused184Select Lac2Fused184SelectWrap Router10Lac2Select
open Phase2MidSandwich PolymorphicFused184Select Lac2ZeroPar183Select
open CompactFoldedSelect ReordOuter13Bridge CompactStepFast176Select
open StepEncK StepDecK CompactStepFast175Core
open CompactOuter9Bound50Core CompactOuter9Bound50Select MobiusOptSubcube163Walk
open CompactTuned162StepWalk CompactTuned162StepZeroCmp20
open CompactZeroCmp20OuterParam CompactStepZeroCmp20OuterParam
open Balanced160Select Pi145SOSPermBridge OneHotSimulates LowBitPi145Select
open ZeroRcHotPrepMid21Fast WalkQPEBridge WalkQPEBridgeXMeas WalkQPEFlexBridge
open scoped Matrix BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator Circuit.Notation

/-- Pass-1 (`oddPass = false`) dyad sign mask for `57`-AND `π145` `SiZero`. -/
def negMaskPi145Fwd57 (g : Fin 145) : Bool :=
  !decide (g.val = 15 ∨ g.val = 31 ∨ g.val = 62 ∨ g.val = 63 ∨
    g.val = 94 ∨ g.val = 95 ∨ g.val = 111 ∨ g.val = 143)
/-- Pass-2 (`oddPass = true`) dyad sign mask for `57`-AND `π145` `SiZero`. -/
def negMaskPi145Bwd57 (g : Fin 145) : Bool :=
  !decide (g.val = 15 ∨ g.val = 31 ∨ g.val = 47 ∨
    g.val = 94 ∨ g.val = 126 ∨ g.val = 143 ∨ g.val = 144)
/-- Pass-indexed dyad sign mask (`false` Pass 1, `true` Pass 2). -/
def negMaskPi14557 (oddPass : Bool) : Fin 145 → Bool :=
  if oddPass then negMaskPi145Bwd57 else negMaskPi145Fwd57
/-- Raw `ℕ` Pass-1 `(g, s) → 0..318` orbital lookup for `57`-AND `π145` `SiZero`. -/
def orbitalNatFwd57 (g : ℕ) (s : Bool) : ℕ :=
  if g == 15 && !s then 21 else if g == 15 && s then 1 else
  if g == 30 && !s then 31 else if g == 30 && s then 34 else
  if g == 31 && !s then 14 else if g == 31 && s then 0 else
  if g == 47 && !s then 47 else if g == 47 && s then 40 else
  if g == 62 && !s then 23 else if g == 62 && s then 15 else
  if g == 63 && !s then 13 else if g == 63 && s then 29 else
  if g == 79 && !s then 48 else if g == 79 && s then 46 else
  if g == 94 && !s then 16 else if g == 94 && s then 9 else
  if g == 95 && !s then 27 else if g == 95 && s then 26 else
  if g == 111 && !s then 5 else if g == 111 && s then 3 else
  if g == 126 && !s then 57 else if g == 126 && s then 32 else
  if g == 127 && !s then 52 else if g == 127 && s then 49 else
  if g == 142 && s then 55 else if g == 143 && !s then 6 else
  if g == 143 && s then 7 else if g == 144 && !s then 45 else
  if g == 144 && s then 41 else
  if (g == 14 || g == 46 || g == 78 || g == 110) && s then 58 + 29 * (g / 16 + 1) + 28
  else 58 + 29 * (g / 16) + 2 * (g % 16) + (if s then 1 else 0)
/-- Pass-1 `(Fin 145, Bool) → Fin 319` orbital lookup table for `57`-AND `π145` `SiZero`. -/
def orbitalOfPi145Fwd57 (g : Fin 145) (s : Bool) : Fin 319 :=
  ⟨orbitalNatFwd57 g.val s % 319, Nat.mod_lt _ (by decide)⟩
/-- Raw `ℕ` Pass-2 `(g, s) → 0..318` orbital lookup for `57`-AND `π145` `SiZero`. -/
def orbitalNatBwd57 (g : ℕ) (s : Bool) : ℕ :=
  if g == 15 && !s then 12 else if g == 15 && s then 28 else
  if g == 30 && !s then 37 else if g == 30 && s then 36 else
  if g == 31 && !s then 22 else if g == 31 && s then 10 else
  if g == 47 && !s then 18 else if g == 47 && s then 11 else
  if g == 62 && !s then 38 else if g == 62 && s then 56 else
  if g == 63 && !s then 53 else if g == 63 && s then 35 else
  if g == 79 && !s then 44 else if g == 79 && s then 42 else
  if g == 94 && !s then 17 else if g == 94 && s then 25 else
  if g == 95 && !s then 33 else if g == 95 && s then 30 else
  if g == 111 && !s then 39 else if g == 111 && s then 54 else
  if g == 126 && !s then 19 else if g == 126 && s then 20 else
  if g == 127 && !s then 51 else if g == 127 && s then 43 else
  if g == 142 && s then 50 else if g == 143 && !s then 24 else
  if g == 143 && s then 4 else if g == 144 && !s then 8 else
  if g == 144 && s then 2 else
  if (g == 14 || g == 46 || g == 78 || g == 110) && s then 58 + 29 * (g / 16 + 1) + 28
  else 58 + 29 * (g / 16) + 2 * (g % 16) + (if s then 1 else 0)
/-- Pass-2 `(Fin 145, Bool) → Fin 319` orbital lookup table for `57`-AND `π145` `SiZero`. -/
def orbitalOfPi145Bwd57 (g : Fin 145) (s : Bool) : Fin 319 :=
  ⟨orbitalNatBwd57 g.val s % 319, Nat.mod_lt _ (by decide)⟩
/-- Pass-indexed `(Fin 145, Bool) → Fin 319` orbital table (`false` Pass 1, `true` Pass 2). -/
def orbitalOfPi14557 (oddPass : Bool) : Fin 145 → Bool → Fin 319 :=
  if oddPass then orbitalOfPi145Bwd57 else orbitalOfPi145Fwd57

abbrev x_7 (a : Wire 23) : RouterStep 23 := .x a
abbrev c_4 (c t : Wire 23) (h : c ≠ t := by decide) : RouterStep 23 := .cnot c t h
abbrev a_10 (a b c : Wire 23) (h1 : a ≠ b := by decide) (h2 : a ≠ c := by decide)
    (h3 : b ≠ c := by decide) : RouterStep 23 := .andAlloc a b c h1 h2 h3
abbrev f_4 (a b c : Wire 23) (h1 : a ≠ b := by decide) (h2 : a ≠ c := by decide)
    (h3 : b ≠ c := by decide) : RouterStep 23 := .andFree a b c h1 h2 h3

/-- Shared `14`-AND Stage-A prefix on `23` router wires. -/
def stepsA57 : List (RouterStep 23) := [
  a_10 2 3 18, a_10 18 4 19, x_7 8, a_10 8 19 0, x_7 8, f_4 18 4 19, f_4 2 3 18, c_4 0 2, c_4 0 3,
  c_4 0 4, a_10 0 5 20, a_10 20 6 19, a_10 19 7 18, c_4 18 8, c_4 18 1, f_4 20 6 19, c_4 20 2,
  c_4 20 5, f_4 0 2 20, a_10 0 6 20, c_4 20 3, c_4 20 6, f_4 0 3 20, a_10 0 7 20, c_4 20 4,
  c_4 20 7, f_4 0 4 20]
/-- Pass-1 `6`-AND Stage-B prefix before `7`-CSWAP. -/
def preBFwd57 : List (RouterStep 23) := [
  c_4 8 18, a_10 18 4 19, c_4 19 6, f_4 18 4 19, c_4 6 2, a_10 5 2 19, c_4 19 3, c_4 19 4,
  f_4 5 2 19, c_4 6 2, c_4 2 4, c_4 5 4, a_10 3 4 19, c_4 19 2, f_4 3 4 19, c_4 5 4, c_4 2 4,
  c_4 18 5, c_4 2 3, c_4 4 2, c_4 3 4, c_4 4 3, c_4 3 4, c_4 6 2, x_7 2, c_4 8 18, c_4 0 2]
/-- Pass-2 `4`-AND Stage-B prefix before `7`-CSWAP. -/
def preBBwd57 : List (RouterStep 23) := [
  c_4 8 5, c_4 18 5, x_7 5, a_10 3 5 19, x_7 5, c_4 19 2, x_7 5, f_4 3 5 19, x_7 5, c_4 6 4,
  a_10 2 4 19, c_4 19 3, f_4 2 4 19, c_4 6 4, c_4 2 3, x_7 3, x_7 4, c_4 2 3, c_4 3 2, c_4 2 3,
  c_4 2 4, c_4 4 2, c_4 2 4, c_4 0 2, c_4 0 3, x_7 3, c_4 0 3]
/-- First half (`6` ANDs) of `w8`-controlled `7`-CSWAP. -/
def midCsA57 : List (RouterStep 23) := [
  c_4 3 10, a_10 8 10 19, c_4 19 3, f_4 8 10 19, c_4 3 10, c_4 9 15, a_10 8 15 19, c_4 19 9,
  f_4 8 15 19, c_4 9 15, x_7 9, c_4 9 14, a_10 8 14 19, c_4 19 9, f_4 8 14 19, c_4 9 14]
/-- Pass-1 second half (`8` ANDs) of `7`-CSWAP (`22` steps). -/
def midCsBFwd57 : List (RouterStep 23) := [
  c_4 2 11, a_10 8 11 19, c_4 19 2, f_4 8 11 19, c_4 2 11, c_4 4 7, a_10 8 7 19, c_4 19 4,
  f_4 8 7 19, c_4 4 7, x_7 1, x_7 4, c_4 1 12, a_10 8 12 19, c_4 19 1, f_4 8 12 19, c_4 1 12,
  c_4 4 13, a_10 8 13 19, c_4 19 4, f_4 8 13 19, c_4 4 13]
/-- Pass-2 second half (`8` ANDs) of `7`-CSWAP (`21` steps). -/
def midCsBBwd57 : List (RouterStep 23) := [
  c_4 2 11, a_10 8 11 19, c_4 19 2, f_4 8 11 19, c_4 2 11, c_4 4 7, a_10 8 7 19, c_4 19 4,
  f_4 8 7 19, c_4 4 7, x_7 4, c_4 1 12, a_10 8 12 19, c_4 19 1, f_4 8 12 19, c_4 1 12, c_4 4 13,
  a_10 8 13 19, c_4 19 4, f_4 8 13 19, c_4 4 13]
/-- Pass-1 `23`-AND Stage-B post-router. -/
def postBFwd57 : List (RouterStep 23) := [
  a_10 14 13 19, x_7 11, a_10 12 11 17, x_7 11, a_10 19 17 20, x_7 11, f_4 12 11 17, x_7 11,
  a_10 20 8 17, x_7 5, a_10 6 5 22, x_7 5, a_10 17 22 21, x_7 5, f_4 6 5 22, x_7 5, f_4 20 8 17,
  c_4 21 0, c_4 21 6, c_4 21 18, c_4 21 20, a_10 21 7 17, c_4 17 5, c_4 17 7, c_4 17 14,
  c_4 17 13, c_4 17 12, c_4 17 19, c_4 21 11, c_4 17 11, f_4 21 5 17, c_4 5 11, f_4 18 11 21,
  c_4 5 11, c_4 5 10, a_10 20 10 21, x_7 22, c_4 8 22, c_4 0 22, c_4 18 22, a_10 22 21 17,
  c_4 17 5, f_4 22 21 17, c_4 18 22, c_4 0 22, c_4 8 22, x_7 22, f_4 8 0 18, a_10 0 21 17,
  c_4 17 8, f_4 0 21 17, f_4 20 10 21, c_4 5 10, x_7 11, a_10 12 11 17, x_7 11, f_4 19 17 20,
  x_7 11, f_4 12 11 17, x_7 11, f_4 14 13 19]
/-- Pass-2 `25`-AND Stage-B post-router. -/
def postBBwd57 : List (RouterStep 23) := [
  a_10 14 13 19, x_7 11, a_10 12 11 17, x_7 11, a_10 19 17 20, x_7 11, f_4 12 11 17, x_7 11,
  a_10 20 8 17, x_7 5, x_7 6, a_10 6 5 22, x_7 5, x_7 6, a_10 17 22 21, x_7 5, x_7 6, f_4 6 5 22,
  x_7 5, x_7 6, f_4 20 8 17, c_4 21 0, a_10 21 7 17, c_4 17 5, c_4 17 7, c_4 17 14, c_4 17 13,
  c_4 17 12, c_4 17 19, c_4 17 20, c_4 17 21, c_4 21 18, x_7 10, a_10 21 10 22, x_7 10,
  c_4 22 11, c_4 22 20, x_7 10, f_4 21 10 22, x_7 10, c_4 10 11, f_4 18 11 21, c_4 10 11,
  c_4 17 18, f_4 18 5 17, c_4 5 10, a_10 20 10 21, x_7 22, c_4 8 22, c_4 0 22, c_4 18 22,
  a_10 22 21 17, c_4 17 5, f_4 22 21 17, c_4 18 22, c_4 0 22, c_4 8 22, x_7 22, f_4 8 0 18,
  a_10 0 21 17, c_4 17 8, f_4 0 21 17, f_4 20 10 21, c_4 5 10, x_7 11, a_10 12 11 17, x_7 11,
  f_4 19 17 20, x_7 11, f_4 12 11 17, x_7 11, f_4 14 13 19]

/-- Pass-indexed Stage-B prefix before `7`-CSWAP. -/
def preB57 (oddPass : Bool) : List (RouterStep 23) :=
  if oddPass then preBBwd57 else preBFwd57
/-- Pass-indexed second half of `7`-CSWAP. -/
def midCsB57 (oddPass : Bool) : List (RouterStep 23) :=
  if oddPass then midCsBBwd57 else midCsBFwd57
/-- Pass-indexed Stage-B post-router. -/
def postB57 (oddPass : Bool) : List (RouterStep 23) :=
  if oddPass then postBBwd57 else postBFwd57
/-- Complete `43`-AND Stage-B router (`false` Pass 1, `true` Pass 2). -/
def stepsB57 (oddPass : Bool) : List (RouterStep 23) :=
  (preB57 oddPass ++ (midCsA57 ++ midCsB57 oddPass)) ++ postB57 oddPass
/-- Pass-1 `43`-AND Stage-B router alias. -/
abbrev stepsBFwd57 : List (RouterStep 23) := stepsB57 false
/-- Pass-2 `43`-AND Stage-B router alias. -/
abbrev stepsBBwd57 : List (RouterStep 23) := stepsB57 true

@[simp] theorem numRouterAndsStepsA57 : numRouterAnds stepsA57 = 14 := by decide
@[simp] theorem numRouterAndsStepsB57 (oddPass : Bool) :
    numRouterAnds (stepsB57 oddPass) = 43 := by cases oddPass <;> decide

/-- Active-wire mask `[0..8, 18..20]` of `stepsA57`. -/
def maskA2 (i : Fin 24) : Bool := i.val ≤ 8 || (18 ≤ i.val && i.val ≤ 20)
/-- Stage-A `State24` specification of `stepsA57` on `initState23 x16`. -/
def specA57 (x16 : Fin 16 → Bool) : State24 :=
  let st0 := initState23 x16
  mergeState24 maskA2 (step24_2 stepsA57 (canonA st0)) st0
/-- Literal-constructor merge for `maskA2` (`rfl`-equal to `mergeState24 maskA2`). -/
def fastMergeMaskA (a b : State24) : State24 :=
  ⟨a.q0, ⟨a.q1.b0, b.q1.b1, b.q1.b2, b.q1.b3, b.q1.b4, b.q1.b5, b.q1.b6, b.q1.b7⟩,
   ⟨b.q2.b0, b.q2.b1, a.q2.b2, a.q2.b3, a.q2.b4, b.q2.b5, b.q2.b6, b.q2.b7⟩⟩
/-- Strictly evaluate `specA57 x16` once in CPS and pass it to `k`. -/
def fastWithSpecA {α : Type} (x16 : Fin 16 → Bool) (k : State24 → α) : α :=
  strictState24 (initState23 x16) fun st0 ↦
    fastWithRun24 stepsA57 (canonA st0) fun sA ↦ k (fastMergeMaskA sA st0)
theorem fastWithSpecA_eq {α : Type} (x16 : Fin 16 → Bool) (k : State24 → α) :
    fastWithSpecA x16 k = k (specA57 x16) := by
  dsimp only [fastWithSpecA, specA57]; rw [strictState24_eq, fastWithRun24_eq]; rfl

/-- Active-wire mask `[0..8, 18, 19]` of `preB57`. -/
def maskPre (i : Fin 24) : Bool := i.val ≤ 8 || i.val == 18 || i.val == 19
/-- Canonical `9`-bit projection onto `[0..8]` with `w18 = w8 && w0` and `w19 = false`. -/
def canonPre (st : State24) : State24 :=
  ⟨st.q0, ⟨st.q1.b0, false, false, false, false, false, false, false⟩,
   ⟨false, false, st.q1.b0 && st.q0.b0, false, false, false, false, false⟩⟩
/-- Active-wire mask `[3, 8, 9, 10, 14, 15, 19]` of `midCsA57`. -/
def maskCsA (i : Fin 24) : Bool :=
  i.val == 3 || i.val == 8 || i.val == 9 || i.val == 10 || i.val == 14 || i.val == 15 || i.val == 19
/-- Canonical `6`-bit projection onto `[3, 8, 9, 10, 14, 15]` (`w19 = false`). -/
def canonCsA (st : State24) : State24 :=
  ⟨⟨false, false, false, st.q0.b3, false, false, false, false⟩,
   ⟨st.q1.b0, st.q1.b1, st.q1.b2, false, false, false, st.q1.b6, st.q1.b7⟩, zeroState8⟩
/-- Active-wire mask `[1, 2, 4, 7, 8, 11, 12, 13, 19]` of `midCsB57`. -/
def maskCsB (i : Fin 24) : Bool :=
  i.val == 1 || i.val == 2 || i.val == 4 || i.val == 7 || i.val == 8 ||
    i.val == 11 || i.val == 12 || i.val == 13 || i.val == 19
/-- Canonical `8`-bit projection onto `[1, 2, 4, 7, 8, 11, 12, 13]` (`w19 = false`). -/
def canonCsB (st : State24) : State24 :=
  ⟨⟨false, st.q0.b1, st.q0.b2, false, st.q0.b4, false, false, st.q0.b7⟩,
   ⟨st.q1.b0, false, false, st.q1.b3, st.q1.b4, st.q1.b5, false, false⟩, zeroState8⟩
/-- Canonical `10`-bit projection onto `[0, 5..8, 10..14]` with `w18 = w8 && w0`. -/
def canonPost (st : State24) : State24 :=
  ⟨⟨st.q0.b0, false, false, false, false, st.q0.b5, st.q0.b6, st.q0.b7⟩,
   ⟨st.q1.b0, false, st.q1.b2, st.q1.b3, st.q1.b4, st.q1.b5, st.q1.b6, false⟩,
   ⟨false, false, st.q1.b0 && st.q0.b0, false, false, false, false, false⟩⟩
/-- Stage-B `State24` after `preB57`. -/
def phase1_2 (oddPass : Bool) (st0 : State24) : State24 :=
  mergeState24 maskPre (step24_2 (preB57 oddPass) (canonPre st0)) st0
/-- Stage-B `State24` after `midCsA57`. -/
def phase2 (st1 : State24) : State24 :=
  mergeState24 maskCsA (step24_2 midCsA57 (canonCsA st1)) st1
/-- Stage-B `State24` after `preB57 ++ midCsA57 ++ midCsB57`. -/
def phasePre3 (oddPass : Bool) (st0 : State24) : State24 :=
  let st2 := phase2 (phase1_2 oddPass st0)
  mergeState24 maskCsB (step24_2 (midCsB57 oddPass) (canonCsB st2)) st2
/-- Four-slice Stage-B `State24` specification of `stepsB57 oddPass`. -/
def specB57 (oddPass : Bool) (st0 : State24) : State24 :=
  let st3 := phasePre3 oddPass st0
  mergeState24 maskPost (step24_2 (postB57 oddPass) (canonPost st3)) st3

theorem mergeCanonPre (st : State24) (hw18 : st.get24 18 = (st.get24 8 && st.get24 0))
    (h19 : st.get24 19 = false) : mergeState24 maskPre (canonPre st) st = st := by
  rcases st with ⟨⟨_, _, _, _, _, _, _, _⟩, ⟨_, _, _, _, _, _, _, _⟩, ⟨_, _, _, _, _, _, _, _⟩⟩
  dsimp [State24.get24, State8.get8] at hw18 h19; subst hw18 h19; rfl
theorem mergeCanonCsA (st : State24) (h19 : st.get24 19 = false) :
    mergeState24 maskCsA (canonCsA st) st = st := by
  rcases st with ⟨⟨_, _, _, _, _, _, _, _⟩, ⟨_, _, _, _, _, _, _, _⟩, ⟨_, _, _, _, _, _, _, _⟩⟩
  dsimp [State24.get24, State8.get8] at h19; subst h19; rfl
theorem mergeCanonCsB (st : State24) (h19 : st.get24 19 = false) :
    mergeState24 maskCsB (canonCsB st) st = st := by
  rcases st with ⟨⟨_, _, _, _, _, _, _, _⟩, ⟨_, _, _, _, _, _, _, _⟩, ⟨_, _, _, _, _, _, _, _⟩⟩
  dsimp [State24.get24, State8.get8] at h19; subst h19; rfl
theorem mergeCanonPost (st : State24) (h17 : st.get24 17 = false)
    (hw18 : st.get24 18 = (st.get24 8 && st.get24 0)) (h19 : st.get24 19 = false)
    (h20 : st.get24 20 = false) (h21 : st.get24 21 = false) (h22 : st.get24 22 = false) :
    mergeState24 maskPost (canonPost st) st = st := by
  rcases st with ⟨⟨_, _, _, _, _, _, _, _⟩, ⟨_, _, _, _, _, _, _, _⟩, ⟨_, _, _, _, _, _, _, _⟩⟩
  dsimp [State24.get24, State8.get8] at h17 hw18 h19 h20 h21 h22
  subst h17 hw18 h19 h20 h21 h22; rfl

/-- Boolean check of `stepsA57` on `8` canonical input bits. -/
def checkRunA (a0 a1 a2 a3 a4 a5 a6 a7 : Bool) : Bool :=
  let s0 : State24 := ⟨⟨false, a0, a1, a2, a3, a4, a5, a6⟩,
    ⟨a7, false, false, false, false, false, false, false⟩, zeroState8⟩
  fastCheckRun24 stepsA57 s0 fun s1 ↦
    !s1.get24 17 && (s1.get24 18 == (s1.get24 8 && s1.get24 0)) && !s1.get24 19 && !s1.get24 20
theorem runA_bool : ∀ a0 a1 a2 a3 a4 a5 a6 a7 : Bool,
    checkRunA a0 a1 a2 a3 a4 a5 a6 a7 = true := by decide +kernel
theorem runA_ok2 (a0 a1 a2 a3 a4 a5 a6 a7 : Bool) :
    let s0 : State24 := ⟨⟨false, a0, a1, a2, a3, a4, a5, a6⟩,
      ⟨a7, false, false, false, false, false, false, false⟩, zeroState8⟩
    let s1 := step24_2 stepsA57 s0
    runSteps24 hk23Le24 stepsA57 s0 = some s1 ∧ s1.get24 17 = false ∧
      s1.get24 18 = (s1.get24 8 && s1.get24 0) ∧ s1.get24 19 = false ∧ s1.get24 20 = false := by
  obtain ⟨hr, hp⟩ := fastCheckRun24_iff hk23Le24 (runA_bool a0 a1 a2 a3 a4 a5 a6 a7)
  dsimp only [step24_2] at hp ⊢; generalize (runSteps24 _ _ _).getD _ = s1 at hr hp ⊢
  simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at hp
  exact ⟨hr, hp.1.1.1, hp.1.1.2, hp.1.2, hp.2⟩

/-- Boolean check of `preB57`. -/
def checkRunPre (oddPass b0 b1 b2 b3 b4 b5 b6 b7 b8 : Bool) : Bool :=
  let s0 : State24 := ⟨⟨b0, b1, b2, b3, b4, b5, b6, b7⟩,
    ⟨b8, false, false, false, false, false, false, false⟩,
    ⟨false, false, b8 && b0, false, false, false, false, false⟩⟩
  fastCheckRun24 (preB57 oddPass) s0 fun s1 ↦
    (s1.get24 8 == b8) && (s1.get24 18 == (s1.get24 8 && s1.get24 0)) && !s1.get24 19
theorem runPre_bool : ∀ oddPass b0 b1 b2 b3 b4 b5 b6 b7 b8 : Bool,
    checkRunPre oddPass b0 b1 b2 b3 b4 b5 b6 b7 b8 = true := by decide +kernel
theorem runPre_ok (oddPass b0 b1 b2 b3 b4 b5 b6 b7 b8 : Bool) :
    let s0 : State24 := ⟨⟨b0, b1, b2, b3, b4, b5, b6, b7⟩,
      ⟨b8, false, false, false, false, false, false, false⟩,
      ⟨false, false, b8 && b0, false, false, false, false, false⟩⟩
    let s1 := step24_2 (preB57 oddPass) s0
    runSteps24 hk23Le24 (preB57 oddPass) s0 = some s1 ∧ s1.get24 8 = b8 ∧
      s1.get24 18 = (s1.get24 8 && s1.get24 0) ∧ s1.get24 19 = false := by
  obtain ⟨hr, hp⟩ := fastCheckRun24_iff hk23Le24 (runPre_bool oddPass b0 b1 b2 b3 b4 b5 b6 b7 b8)
  dsimp only [step24_2] at hp ⊢; generalize (runSteps24 _ _ _).getD _ = s1 at hr hp ⊢
  simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at hp
  exact ⟨hr, hp.1.1, hp.1.2, hp.2⟩

/-- Boolean check of `midCsA57`. -/
def checkCsA (b3 b8 b9 b10 b14 b15 : Bool) : Bool :=
  let s0 : State24 := ⟨⟨false, false, false, b3, false, false, false, false⟩,
    ⟨b8, b9, b10, false, false, false, b14, b15⟩, zeroState8⟩
  fastCheckRun24 midCsA57 s0 fun s1 ↦
    (s1.get24 8 == b8) && !s1.get24 19 &&
      (b8 || ((s1.get24 10 == b10) && (s1.get24 14 == b14) && (s1.get24 15 == b15))) &&
      (!b8 || ((s1.get24 10 == b3) && (s1.get24 14 == !b15) && (s1.get24 15 == b9)))
theorem runCsA_bool : ∀ b3 b8 b9 b10 b14 b15 : Bool,
    checkCsA b3 b8 b9 b10 b14 b15 = true := by decide +kernel
theorem runCsA_ok (b3 b8 b9 b10 b14 b15 : Bool) :
    let s0 : State24 := ⟨⟨false, false, false, b3, false, false, false, false⟩,
      ⟨b8, b9, b10, false, false, false, b14, b15⟩, zeroState8⟩
    let s1 := step24_2 midCsA57 s0
    runSteps24 hk23Le24 midCsA57 s0 = some s1 ∧ s1.get24 8 = b8 ∧ s1.get24 19 = false ∧
      (b8 = false → s1.get24 10 = b10 ∧ s1.get24 14 = b14 ∧ s1.get24 15 = b15) ∧
      (b8 = true → s1.get24 10 = b3 ∧ s1.get24 14 = !b15 ∧ s1.get24 15 = b9) := by
  obtain ⟨hr, hp⟩ := fastCheckRun24_iff hk23Le24 (runCsA_bool b3 b8 b9 b10 b14 b15)
  dsimp only [step24_2] at hp ⊢; generalize (runSteps24 _ _ _).getD _ = s1 at hr hp ⊢
  cases b8 <;> simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_true, Bool.not_false,
    Bool.not_eq_true', beq_iff_eq] at hp
  · have hc := hp.1.2.resolve_left Bool.false_ne_true
    exact ⟨hr, hp.1.1.1, hp.1.1.2, fun _ ↦ ⟨hc.1.1, hc.1.2, hc.2⟩, fun h ↦ Bool.noConfusion h⟩
  · have hc := hp.2.resolve_left Bool.false_ne_true
    exact ⟨hr, hp.1.1.1, hp.1.1.2, fun h ↦ Bool.noConfusion h, fun _ ↦ ⟨hc.1.1, hc.1.2, hc.2⟩⟩

/-- Boolean check of `midCsB57`. -/
def checkCsB (oddPass b1 b2 b4 b7 b8 b11 b12 b13 : Bool) : Bool :=
  let s0 : State24 := ⟨⟨false, b1, b2, false, b4, false, false, b7⟩,
    ⟨b8, false, false, b11, b12, b13, false, false⟩, zeroState8⟩
  fastCheckRun24 (midCsB57 oddPass) s0 fun s1 ↦
    (s1.get24 8 == b8) && !s1.get24 19 &&
      (b8 || ((s1.get24 7 == b7) && (s1.get24 11 == b11) && (s1.get24 12 == b12) &&
        (s1.get24 13 == b13))) &&
      (!b8 || ((s1.get24 7 == b4) && (s1.get24 11 == b2) &&
        (s1.get24 12 == xor b1 (!oddPass)) && (s1.get24 13 == !b7)))
theorem runCsB_bool : ∀ oddPass b1 b2 b4 b7 b8 b11 b12 b13 : Bool,
    checkCsB oddPass b1 b2 b4 b7 b8 b11 b12 b13 = true := by decide +kernel
theorem runCsB_ok (oddPass b1 b2 b4 b7 b8 b11 b12 b13 : Bool) :
    let s0 : State24 := ⟨⟨false, b1, b2, false, b4, false, false, b7⟩,
      ⟨b8, false, false, b11, b12, b13, false, false⟩, zeroState8⟩
    let s1 := step24_2 (midCsB57 oddPass) s0
    runSteps24 hk23Le24 (midCsB57 oddPass) s0 = some s1 ∧ s1.get24 8 = b8 ∧ s1.get24 19 = false ∧
      (b8 = false → s1.get24 7 = b7 ∧ s1.get24 11 = b11 ∧ s1.get24 12 = b12 ∧ s1.get24 13 = b13) ∧
      (b8 = true → s1.get24 7 = b4 ∧ s1.get24 11 = b2 ∧ s1.get24 12 = xor b1 (!oddPass) ∧
        s1.get24 13 = !b7) := by
  obtain ⟨hr, hp⟩ := fastCheckRun24_iff hk23Le24 (runCsB_bool oddPass b1 b2 b4 b7 b8 b11 b12 b13)
  dsimp only [step24_2] at hp ⊢; generalize (runSteps24 _ _ _).getD _ = s1 at hr hp ⊢
  cases b8 <;> simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_true, Bool.not_false,
    Bool.not_eq_true', beq_iff_eq] at hp
  · have hc := hp.1.2.resolve_left Bool.false_ne_true
    exact ⟨hr, hp.1.1.1, hp.1.1.2, fun _ ↦ ⟨hc.1.1.1, hc.1.1.2, hc.1.2, hc.2⟩,
      fun h ↦ Bool.noConfusion h⟩
  · have hc := hp.2.resolve_left Bool.false_ne_true
    exact ⟨hr, hp.1.1.1, hp.1.1.2, fun h ↦ Bool.noConfusion h,
      fun _ ↦ ⟨hc.1.1.1, hc.1.1.2, hc.1.2, hc.2⟩⟩

theorem runSteps24StepsA57 (x16 : Fin 16 → Bool) :
    runSteps24 hk23Le24 stepsA57 (initState23 x16) = some (specA57 x16) := by
  have hAll : stepsA57.all (routerStepInMask24 hk23Le24 maskA2) = true := by decide +kernel
  have hm : mergeState24 maskA2 (canonA (initState23 x16)) (initState23 x16) = initState23 x16 :=
    rfl
  have hok := (runA_ok2 (x16 0) (x16 1) (x16 2) (x16 3) (x16 4) (x16 5) (x16 6) (x16 7)).1
  dsimp only [specA57]; conv_lhs => rw [← hm]
  exact runSteps24_merge hk23Le24 maskA2 stepsA57 hAll _ _ (initState23 x16) hok
theorem specA57_borrows (x16 : Fin 16 → Bool) :
    let s := specA57 x16
    s.get24 17 = false ∧ s.get24 18 = (s.get24 8 && s.get24 0) ∧
      (∀ k : Fin 5, s.get24 ⟨19 + k.val, by omega⟩ = false) := by
  intro s
  have hok := (runA_ok2 (x16 0) (x16 1) (x16 2) (x16 3) (x16 4) (x16 5) (x16 6) (x16 7)).2
  dsimp only [s, specA57, canonA, initState23]
  generalize step24_2 stepsA57 _ = s1 at hok ⊢
  refine ⟨rfl, hok.2.1, fun k ↦ ?_⟩
  fin_cases k <;> [exact hok.2.2.1; exact hok.2.2.2; rfl; rfl; rfl]

/-- Stage-B `27`-step prefix state on canonical `xo'` input. -/
def sPre_3 (oddPass : Bool) (xo' : Fin 256) : State24 :=
  step24_2 (preB57 oddPass) (canonPre (specA57 (pack16 xo' false 0 false false)))
/-- Strictly evaluate `sPre_3 oddPass xo'` once in CPS and pass it to `k`. -/
def fastWithSPre {α : Type} (oddPass : Bool) (xo' : Fin 256) (k : State24 → α) : α :=
  fastWithSpecA (pack16 xo' false 0 false false) fun st0 ↦
    fastWithRun24 (preB57 oddPass) (canonPre st0) k
theorem fastWithSPre_eq {α : Type} (oddPass : Bool) (xo' : Fin 256) (k : State24 → α) :
    fastWithSPre oddPass xo' k = k (sPre_3 oddPass xo') := by
  dsimp only [fastWithSPre, sPre_3]; rw [fastWithSpecA_eq, fastWithRun24_eq]

/-- Post-CSWAP `11`-wire canonical input for `126 ≤ xo'` and `si : Bool` given `sPre`. -/
def ge126PostIn (oddPass : Bool) (sPre : State24) (si : Bool) : State24 :=
  ⟨⟨sPre.q0.b0, false, false, false, false, sPre.q0.b5, sPre.q0.b6, sPre.q0.b4⟩,
   ⟨true, false, sPre.q0.b3, sPre.q0.b2, xor sPre.q0.b1 (!oddPass), !sPre.q0.b7, !si, false⟩,
   ⟨false, false, sPre.q0.b0, false, false, false, false, false⟩⟩
/-- Routed `10`-bit Stage-2 control word for `126 ≤ xo'` sectors (`57`-AND). -/
def ctrl10OneBody (oddPass : Bool) (xo' : Fin 256) (si : Bool) : Fin 10 → Bool :=
  ctrl10OfState24 (step24_2 (postB57 oddPass) (ge126PostIn oddPass (sPre_3 oddPass xo') si))

/-- Boolean check of wire `w8 = decide (126 ≤ xo'.val)` and `r : Fin 9` bits on `xo' < 126`. -/
def checkXoW8 (oddPass : Bool) (xo' : Fin 256) : Bool :=
  let d := decide (126 ≤ xo'.val)
  let r := rDiv14OfRc (rcBitsOfXo (pi145XoEquiv xo'))
  fastWithSpecA (pack16 xo' false 0 false false) fun st0 ↦ (st0.q1.b0 == d) &&
    fastWithRun24 (preB57 oddPass) (canonPre st0) fun sp ↦ (sp.q1.b0 == d) &&
      (d || ((sp.q0.b0 == (r.val / 8 % 2 == 1)) && (sp.q0.b5 == (r.val % 2 == 1)) &&
        (sp.q0.b6 == (r.val / 2 % 2 == 1)) && (sp.q0.b7 == (r.val / 4 % 2 == 1))))
theorem xoW8_even_ok : BlockEncodingCircuit.allPow2 8 0 (fun x ↦
    checkXoW8 false ⟨x % 256, Nat.mod_lt _ (by decide)⟩) = true := by decide +kernel
theorem xoW8_odd_ok : BlockEncodingCircuit.allPow2 8 0 (fun x ↦
    checkXoW8 true ⟨x % 256, Nat.mod_lt _ (by decide)⟩) = true := by decide +kernel
theorem xoW8_full2 (oddPass : Bool) (xo' : Fin 256) :
    let r := rDiv14OfRc (rcBitsOfXo (pi145XoEquiv xo'))
    let sp := sPre_3 oddPass xo'
    (specA57 (pack16 xo' false 0 false false)).get24 8 = decide (126 ≤ xo'.val) ∧
      sp.get24 8 = decide (126 ≤ xo'.val) ∧
      (xo'.val < 126 → sp.q0.b0 = (r.val / 8 % 2 == 1) ∧ sp.q0.b5 = (r.val % 2 == 1) ∧
        sp.q0.b6 = (r.val / 2 % 2 == 1) ∧ sp.q0.b7 = (r.val / 4 % 2 == 1)) := by
  have hm : (⟨xo'.val % 256, Nat.mod_lt _ (by decide)⟩ : Fin 256) = xo' :=
    Fin.ext (Nat.mod_eq_of_lt xo'.isLt)
  have h : checkXoW8 oddPass xo' = true := by
    cases oddPass
    · simpa only [hm] using BlockEncodingCircuit.allPow2_zero_true xoW8_even_ok xo'.val xo'.isLt
    · simpa only [hm] using BlockEncodingCircuit.allPow2_zero_true xoW8_odd_ok xo'.val xo'.isLt
  dsimp only [checkXoW8] at h; rw [fastWithSpecA_eq, fastWithRun24_eq] at h
  change ((specA57 (pack16 xo' false 0 false false)).get24 8 == decide (126 ≤ xo'.val) &&
    (((sPre_3 oddPass xo').get24 8 == decide (126 ≤ xo'.val)) && _)) = true at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h; refine ⟨h.1, h.2.1, fun hlt ↦ ?_⟩
  have hd : decide (126 ≤ xo'.val) = false := decide_eq_false (by omega)
  have hr := h.2.2; rw [hd, Bool.false_or] at hr; simp only [Bool.and_eq_true, beq_iff_eq] at hr
  exact ⟨hr.1.1.1, hr.1.1.2, hr.1.2, hr.2⟩
theorem xoW8_ok (oddPass : Bool) (xo' : Fin 256) :
    (specA57 (pack16 xo' false 0 false false)).get24 8 = decide (126 ≤ xo'.val) ∧
      (sPre_3 oddPass xo').get24 8 = decide (126 ≤ xo'.val) :=
  ⟨(xoW8_full2 oddPass xo').1, (xoW8_full2 oddPass xo').2.1⟩
theorem twoBodyPostIn_eq_rIn (oddPass : Bool) (xo' : Fin 256) (hxo' : xo'.val < 126)
    (b : Fin 32) : twoBodyPostIn (sPre_3 oddPass xo') b =
      twoBodyRIn (rDiv14OfRc (rcBitsOfXo (pi145XoEquiv xo'))) b := by
  obtain ⟨hb0, hb5, hb6, hb7⟩ := (xoW8_full2 oddPass xo').2.2 hxo'
  dsimp only [twoBodyPostIn, twoBodyRIn]; rw [hb0, hb5, hb6, hb7]

/-- Pure boolean check that `postB57 oddPass` succeeds with clean borrows & `pair8 < 145`. -/
def checkPost (oddPass : Bool) (s0 : State24) : Bool :=
  fastCheckRun24 (postB57 oddPass) s0 fun s1 ↦
    !s1.q2.b1 && !s1.q2.b2 && !s1.q2.b3 && !s1.q2.b4 && !s1.q2.b5 && !s1.q2.b6 &&
      lt145Nat (pair8NatOf10 (fastCtrl10 s1))
theorem unpack_checkPost {oddPass : Bool} {s0 : State24} (h : checkPost oddPass s0 = true) :
    let sb := postB57 oddPass
    let s1 := step24_2 sb s0
    runSteps24 hk23Le24 sb s0 = some s1 ∧ s1.get24 17 = false ∧ s1.get24 18 = false ∧
      s1.get24 19 = false ∧ s1.get24 20 = false ∧ s1.get24 21 = false ∧ s1.get24 22 = false ∧
      pair8NatOf10 (ctrl10OfState24 s1) < 145 := by
  obtain ⟨hr, hp⟩ := fastCheckRun24_iff hk23Le24 h
  rw [fastCtrl10_eq] at hp; dsimp only [step24_2, lt145Nat] at hp ⊢
  generalize (runSteps24 _ _ _).getD _ = s1 at hr hp ⊢
  simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hp
  exact ⟨hr, hp.1.1.1.1.1.1, hp.1.1.1.1.1.2, hp.1.1.1.1.2, hp.1.1.1.2, hp.1.1.2, hp.1.2, hp.2⟩

theorem post2B_even_ok : BlockEncodingCircuit.allPow2 4 0 (fun r ↦
    if hr : r < 9 then BlockEncodingCircuit.allPow2 5 0 (fun b ↦
      checkPost false (twoBodyRIn ⟨r, hr⟩ ⟨b % 32, Nat.mod_lt _ (by decide)⟩))
    else true) = true := by decide +kernel
theorem post2B_odd_ok : BlockEncodingCircuit.allPow2 4 0 (fun r ↦
    if hr : r < 9 then BlockEncodingCircuit.allPow2 5 0 (fun b ↦
      checkPost true (twoBodyRIn ⟨r, hr⟩ ⟨b % 32, Nat.mod_lt _ (by decide)⟩))
    else true) = true := by decide +kernel
theorem post2B_ok (oddPass : Bool) (xo' : Fin 256) (hxo' : xo'.val < 126) (b : Fin 32) :
    checkPost oddPass (twoBodyPostIn (sPre_3 oddPass xo') b) = true := by
  rw [twoBodyPostIn_eq_rIn oddPass xo' hxo' b]
  set r := rDiv14OfRc (rcBitsOfXo (pi145XoEquiv xo'))
  have hr4 : r.val < 2 ^ 4 := by have := r.isLt; omega
  have hbr : (⟨b.val % 32, Nat.mod_lt _ (by decide)⟩ : Fin 32) = b :=
    Fin.ext (Nat.mod_eq_of_lt b.isLt)
  cases oddPass
  · have h1 := BlockEncodingCircuit.allPow2_zero_true post2B_even_ok r.val hr4
    rw [dite_eq_left r.isLt] at h1
    have h2 := BlockEncodingCircuit.allPow2_zero_true h1 b.val b.isLt
    rwa [hbr] at h2
  · have h1 := BlockEncodingCircuit.allPow2_zero_true post2B_odd_ok r.val hr4
    rw [dite_eq_left r.isLt] at h1
    have h2 := BlockEncodingCircuit.allPow2_zero_true h1 b.val b.isLt
    rwa [hbr] at h2

theorem post1B_even_ok : BlockEncodingCircuit.allPow2 8 0 (fun q ↦
    if 126 ≤ q then fastWithSPre false ⟨q % 256, Nat.mod_lt _ (by decide)⟩ fun sp ↦
      checkPost false (ge126PostIn false sp false) &&
        checkPost false (ge126PostIn false sp true)
    else true) = true := by decide +kernel
theorem post1B_odd_ok : BlockEncodingCircuit.allPow2 8 0 (fun q ↦
    if 126 ≤ q then fastWithSPre true ⟨q % 256, Nat.mod_lt _ (by decide)⟩ fun sp ↦
      checkPost true (ge126PostIn true sp false) &&
        checkPost true (ge126PostIn true sp true)
    else true) = true := by decide +kernel
theorem post1B_ok (oddPass : Bool) (xo' : Fin 256) (h126 : 126 ≤ xo'.val) (si : Bool) :
    checkPost oddPass (ge126PostIn oddPass (sPre_3 oddPass xo') si) = true := by
  have hxq : (⟨xo'.val % 256, Nat.mod_lt _ (by decide)⟩ : Fin 256) = xo' :=
    Fin.ext (Nat.mod_eq_of_lt xo'.isLt)
  cases oddPass
  · have h1 := BlockEncodingCircuit.allPow2_zero_true post1B_even_ok xo'.val xo'.isLt
    rw [ite_eq_left h126, hxq, fastWithSPre_eq, Bool.and_eq_true] at h1
    cases si <;> [exact h1.1; exact h1.2]
  · have h1 := BlockEncodingCircuit.allPow2_zero_true post1B_odd_ok xo'.val xo'.isLt
    rw [ite_eq_left h126, hxq, fastWithSPre_eq, Bool.and_eq_true] at h1
    cases si <;> [exact h1.1; exact h1.2]

theorem specA57_low9_pack16 (xo' : Fin 256) (so : Bool) (b : Fin 32) (si neg : Bool) :
    canonPre (specA57 (pack16 xo' so b si neg)) =
      canonPre (specA57 (pack16 xo' false 0 false false)) ∧
    (specA57 (pack16 xo' so b si neg)).get24 8 =
      (specA57 (pack16 xo' false 0 false false)).get24 8 := by
  have hc : canonA (initState23 (pack16 xo' so b si neg)) =
      canonA (initState23 (pack16 xo' false 0 false false)) := by
    dsimp only [canonA, initState23, pack16]; rfl
  dsimp only [canonPre, specA57]; rw [hc]
  generalize step24_2 stepsA57 _ = sA; exact ⟨rfl, rfl⟩

theorem maskPre_all (oddPass : Bool) :
    (preB57 oddPass).all (routerStepInMask24 hk23Le24 maskPre) = true := by
  cases oddPass <;> decide +kernel
theorem maskCsA_all : midCsA57.all (routerStepInMask24 hk23Le24 maskCsA) = true := by
  decide +kernel
theorem maskCsB_all (oddPass : Bool) :
    (midCsB57 oddPass).all (routerStepInMask24 hk23Le24 maskCsB) = true := by
  cases oddPass <;> decide +kernel
theorem maskPost_all (oddPass : Bool) :
    (postB57 oddPass).all (routerStepInMask24 hk23Le24 maskPost) = true := by
  cases oddPass <;> decide +kernel

theorem phasePre3_run (oddPass : Bool) (st0 : State24) (h17_0 : st0.get24 17 = false)
    (hw18_0 : st0.get24 18 = (st0.get24 8 && st0.get24 0))
    (hb0 : ∀ k : Fin 5, st0.get24 ⟨19 + k.val, by omega⟩ = false) :
    let st3 := phasePre3 oddPass st0
    runSteps24 hk23Le24 (preB57 oddPass ++ (midCsA57 ++ midCsB57 oddPass)) st0 = some st3 ∧
      mergeState24 maskPost (canonPost st3) st3 = st3 := by
  intro st3; have hm1 := mergeCanonPre st0 hw18_0 (hb0 ⟨0, by decide⟩)
  have hok1 := runPre_ok oddPass st0.q0.b0 st0.q0.b1 st0.q0.b2 st0.q0.b3 st0.q0.b4 st0.q0.b5
    st0.q0.b6 st0.q0.b7 st0.q1.b0
  have hr1 : runSteps24 hk23Le24 (preB57 oddPass) st0 = some (phase1_2 oddPass st0) := by
    dsimp only [phase1_2]; conv_lhs => rw [← hm1]
    exact runSteps24_merge hk23Le24 maskPre _ (maskPre_all oddPass) _ _ st0 hok1.1
  have hw18_1 : (phase1_2 oddPass st0).get24 18 =
      ((phase1_2 oddPass st0).get24 8 && (phase1_2 oddPass st0).get24 0) := hok1.2.2.1
  have h19_1 : (phase1_2 oddPass st0).get24 19 = false := hok1.2.2.2
  have h17_1 : (phase1_2 oddPass st0).get24 17 = false := h17_0
  have hb1 : ∀ k : Fin 3, (phase1_2 oddPass st0).get24 ⟨20 + k.val, by omega⟩ = false :=
    fun k ↦ by have hk0 := hb0 ⟨1 + k.val, by omega⟩; fin_cases k <;> exact hk0
  generalize hst1 : phase1_2 oddPass st0 = st1 at hr1 hw18_1 h19_1 h17_1 hb1
  have hm2 := mergeCanonCsA st1 h19_1
  have hok2 := runCsA_ok st1.q0.b3 st1.q1.b0 st1.q1.b1 st1.q1.b2 st1.q1.b6 st1.q1.b7
  have hr2 : runSteps24 hk23Le24 midCsA57 st1 = some (phase2 st1) := by
    dsimp only [phase2]; conv_lhs => rw [← hm2]
    exact runSteps24_merge hk23Le24 maskCsA _ maskCsA_all _ _ st1 hok2.1
  have h19_2 : (phase2 st1).get24 19 = false := hok2.2.2.1
  have hw8_2 : (phase2 st1).get24 8 = st1.get24 8 := hok2.2.1
  have hw18_2 : (phase2 st1).get24 18 = ((phase2 st1).get24 8 && (phase2 st1).get24 0) := by
    change st1.get24 18 = ((phase2 st1).get24 8 && st1.get24 0); rw [hw8_2]; exact hw18_1
  have h17_2 : (phase2 st1).get24 17 = false := h17_1
  have hb2 : ∀ k : Fin 3, (phase2 st1).get24 ⟨20 + k.val, by omega⟩ = false :=
    fun k ↦ by have hk1 := hb1 k; fin_cases k <;> exact hk1
  have hst3Eq : st3 = mergeState24 maskCsB
      (step24_2 (midCsB57 oddPass) (canonCsB (phase2 st1))) (phase2 st1) := by
    dsimp only [st3, phasePre3]; rw [hst1]
  generalize phase2 st1 = st2 at hr2 h19_2 hw18_2 h17_2 hb2 hst3Eq
  have hm3 := mergeCanonCsB st2 h19_2
  have hok3 := runCsB_ok oddPass st2.q0.b1 st2.q0.b2 st2.q0.b4 st2.q0.b7 st2.q1.b0
    st2.q1.b3 st2.q1.b4 st2.q1.b5
  have hr3 : runSteps24 hk23Le24 (midCsB57 oddPass) st2 = some st3 := by
    rw [hst3Eq]; conv_lhs => rw [← hm3]
    exact runSteps24_merge hk23Le24 maskCsB _ (maskCsB_all oddPass) _ _ st2 hok3.1
  have h19_3 : st3.get24 19 = false := by rw [hst3Eq]; exact hok3.2.2.1
  have hw8_3 : st3.get24 8 = st2.get24 8 := by rw [hst3Eq]; exact hok3.2.1
  have h17_3 : st3.get24 17 = false := by rw [hst3Eq]; exact h17_2
  have hw18_3 : st3.get24 18 = (st3.get24 8 && st3.get24 0) := by
    have hg18 : st3.get24 18 = st2.get24 18 := by rw [hst3Eq]; rfl
    have hg0 : st3.get24 0 = st2.get24 0 := by rw [hst3Eq]; rfl
    rw [hg18, hw8_3, hg0]; exact hw18_2
  have hb3 : ∀ k : Fin 3, st3.get24 ⟨20 + k.val, by omega⟩ = false :=
    fun k ↦ by have hk2 := hb2 k; rw [hst3Eq]; fin_cases k <;> exact hk2
  exact ⟨by rw [runSteps24_append hk23Le24 _ _ st0 st1 hr1,
    runSteps24_append hk23Le24 _ _ st1 st2 hr2, hr3],
    mergeCanonPost st3 h17_3 hw18_3 h19_3 (hb3 0) (hb3 1) (hb3 2)⟩

theorem phasePre3_of_w8_false (oddPass : Bool) (st0 sp : State24)
    (hsp : step24_2 (preB57 oddPass) (canonPre st0) = sp) (hw8S : sp.q1.b0 = false) :
    (phasePre3 oddPass st0).get24 15 = st0.q1.b7 ∧
      canonPost (phasePre3 oddPass st0) = canonPost (mergeState24 maskPre sp st0) := by
  have hst1Eq : phase1_2 oddPass st0 = mergeState24 maskPre sp st0 := by
    dsimp only [phase1_2]; rw [hsp]
  have hw8_1 : (phase1_2 oddPass st0).q1.b0 = false := by rw [hst1Eq]; exact hw8S
  let stM := mergeState24 maskPre sp st0
  have hq0_1 : (phase1_2 oddPass st0).q0 = stM.q0 := congrArg State24.q0 hst1Eq
  have hq1_1 : (phase1_2 oddPass st0).q1 = stM.q1 := congrArg State24.q1 hst1Eq
  generalize hst1 : phase1_2 oddPass st0 = st1 at hw8_1 hq0_1 hq1_1
  have hb0f : ∀ (f : State8 → Bool), f st1.q0 = f stM.q0 := fun f ↦ congrArg f hq0_1
  have hb1f : ∀ (f : State8 → Bool), f st1.q1 = f stM.q1 := fun f ↦ congrArg f hq1_1
  have hok2 := runCsA_ok st1.q0.b3 st1.q1.b0 st1.q1.b1 st1.q1.b2 st1.q1.b6 st1.q1.b7
  have hcA := hok2.2.2.2.1 hw8_1
  have hw8_2 : (phase2 st1).q1.b0 = false := hok2.2.1.trans hw8_1
  have h10_2 : (phase2 st1).q1.b2 = stM.q1.b2 := hcA.1.trans (hb1f State8.b2)
  have h14_2 : (phase2 st1).q1.b6 = stM.q1.b6 := hcA.2.1.trans (hb1f State8.b6)
  have h15_2 : (phase2 st1).q1.b7 = stM.q1.b7 := hcA.2.2.trans (hb1f State8.b7)
  have e0 : (phase2 st1).q0.b0 = stM.q0.b0 := hb0f State8.b0
  have e5 : (phase2 st1).q0.b5 = stM.q0.b5 := hb0f State8.b5
  have e6 : (phase2 st1).q0.b6 = stM.q0.b6 := hb0f State8.b6
  have e7 : (phase2 st1).q0.b7 = stM.q0.b7 := hb0f State8.b7
  have e11 : (phase2 st1).q1.b3 = stM.q1.b3 := hb1f State8.b3
  have e12 : (phase2 st1).q1.b4 = stM.q1.b4 := hb1f State8.b4
  have e13 : (phase2 st1).q1.b5 = stM.q1.b5 := hb1f State8.b5
  have hst3Eq : phasePre3 oddPass st0 = mergeState24 maskCsB
      (step24_2 (midCsB57 oddPass) (canonCsB (phase2 st1))) (phase2 st1) := by
    dsimp only [phasePre3]; rw [hst1]
  generalize phase2 st1 = st2 at hw8_2 h10_2 h14_2 h15_2 e0 e5 e6 e7 e11 e12 e13 hst3Eq
  have hok3 := runCsB_ok oddPass st2.q0.b1 st2.q0.b2 st2.q0.b4 st2.q0.b7 st2.q1.b0
    st2.q1.b3 st2.q1.b4 st2.q1.b5
  have hcB := hok3.2.2.2.1 hw8_2
  let st3R := mergeState24 maskCsB (step24_2 (midCsB57 oddPass) (canonCsB st2)) st2
  have hw8_3 : st3R.q1.b0 = false := hok3.2.1.trans hw8_2
  have hw8M : stM.q1.b0 = false := by dsimp only [stM]; exact hw8S
  have h15M : stM.q1.b7 = st0.q1.b7 := rfl
  have hFinal : ∀ sF : State24, sF.q0.b0 = stM.q0.b0 → sF.q0.b5 = stM.q0.b5 →
      sF.q0.b6 = stM.q0.b6 → sF.q0.b7 = stM.q0.b7 → sF.q1.b0 = false → sF.q1.b2 = stM.q1.b2 →
      sF.q1.b3 = stM.q1.b3 → sF.q1.b4 = stM.q1.b4 → sF.q1.b5 = stM.q1.b5 → sF.q1.b6 = stM.q1.b6 →
      sF.q1.b7 = st0.q1.b7 → sF.get24 15 = st0.q1.b7 ∧ canonPost sF = canonPost stM := by
    intro sF a0 a5 a6 a7 aw8 a10 a11 a12 a13 a14 a15; refine ⟨a15, ?_⟩
    dsimp only [canonPost, State24.get24, State8.get8]
    rw [a0, a5, a6, a7, aw8, a10, a11, a12, a13, a14, hw8M]
  rw [hst3Eq]
  exact hFinal st3R e0 e5 e6 (hcB.1.trans e7) hw8_3 h10_2 (hcB.2.1.trans e11)
    (hcB.2.2.1.trans e12) (hcB.2.2.2.trans e13) h14_2 (h15_2.trans h15M)

theorem phasePre3_of_w8_true (oddPass : Bool) (st0 sp : State24)
    (hsp : step24_2 (preB57 oddPass) (canonPre st0) = sp) (hw8S : sp.q1.b0 = true) :
    (phasePre3 oddPass st0).get24 15 = st0.q1.b1 ∧
      canonPost (phasePre3 oddPass st0) = ge126PostIn oddPass sp st0.q1.b7 := by
  have hst1Eq : phase1_2 oddPass st0 = mergeState24 maskPre sp st0 := by
    dsimp only [phase1_2]; rw [hsp]
  have hw8_1 : (phase1_2 oddPass st0).q1.b0 = true := by rw [hst1Eq]; exact hw8S
  have h9_1 : (phase1_2 oddPass st0).q1.b1 = st0.q1.b1 := by rw [hst1Eq]; rfl
  have h15_1 : (phase1_2 oddPass st0).q1.b7 = st0.q1.b7 := by rw [hst1Eq]; rfl
  have hq0_1 : (phase1_2 oddPass st0).q0 = sp.q0 := by
    rw [hst1Eq]; rcases sp with ⟨⟨_, _, _, _, _, _, _, _⟩, _, _⟩; rfl
  generalize hst1 : phase1_2 oddPass st0 = st1 at hw8_1 h9_1 h15_1 hq0_1
  have hb : ∀ (f : State8 → Bool), f st1.q0 = f sp.q0 := fun f ↦ congrArg f hq0_1
  have hok2 := runCsA_ok st1.q0.b3 st1.q1.b0 st1.q1.b1 st1.q1.b2 st1.q1.b6 st1.q1.b7
  have hcA := hok2.2.2.2.2 hw8_1
  have hw8_2 : (phase2 st1).q1.b0 = true := hok2.2.1.trans hw8_1
  have h10_2 : (phase2 st1).q1.b2 = sp.q0.b3 := hcA.1.trans (hb State8.b3)
  have h14_2 : (phase2 st1).q1.b6 = !st0.q1.b7 := hcA.2.1.trans (congrArg Bool.not h15_1)
  have h15_2 : (phase2 st1).q1.b7 = st0.q1.b1 := hcA.2.2.trans h9_1
  have b0 : (phase2 st1).q0.b0 = sp.q0.b0 := hb State8.b0
  have b1 : (phase2 st1).q0.b1 = sp.q0.b1 := hb State8.b1
  have b2 : (phase2 st1).q0.b2 = sp.q0.b2 := hb State8.b2
  have b4 : (phase2 st1).q0.b4 = sp.q0.b4 := hb State8.b4
  have b5 : (phase2 st1).q0.b5 = sp.q0.b5 := hb State8.b5
  have b6 : (phase2 st1).q0.b6 = sp.q0.b6 := hb State8.b6
  have b7 : (phase2 st1).q0.b7 = sp.q0.b7 := hb State8.b7
  have hst3Eq : phasePre3 oddPass st0 = mergeState24 maskCsB
      (step24_2 (midCsB57 oddPass) (canonCsB (phase2 st1))) (phase2 st1) := by
    dsimp only [phasePre3]; rw [hst1]
  generalize phase2 st1 = st2 at hw8_2 h10_2 h14_2 h15_2 b0 b1 b2 b4 b5 b6 b7 hst3Eq
  have hok3 := runCsB_ok oddPass st2.q0.b1 st2.q0.b2 st2.q0.b4 st2.q0.b7 st2.q1.b0
    st2.q1.b3 st2.q1.b4 st2.q1.b5
  have hcB := hok3.2.2.2.2 hw8_2
  let st3R := mergeState24 maskCsB (step24_2 (midCsB57 oddPass) (canonCsB st2)) st2
  have hw8_3 : st3R.q1.b0 = true := hok3.2.1.trans hw8_2
  have hFinal : ∀ sF : State24, sF.q0.b0 = sp.q0.b0 → sF.q0.b5 = sp.q0.b5 →
      sF.q0.b6 = sp.q0.b6 → sF.q0.b7 = sp.q0.b4 → sF.q1.b0 = true → sF.q1.b2 = sp.q0.b3 →
      sF.q1.b3 = sp.q0.b2 → sF.q1.b4 = xor sp.q0.b1 (!oddPass) → sF.q1.b5 = !sp.q0.b7 →
      sF.q1.b6 = !st0.q1.b7 → sF.q1.b7 = st0.q1.b1 →
      sF.get24 15 = st0.q1.b1 ∧ canonPost sF = ge126PostIn oddPass sp st0.q1.b7 := by
    intro sF e0 e5 e6 e7 ew8 e10 e11 e12 e13 e14 e15; refine ⟨e15, ?_⟩
    dsimp only [canonPost, ge126PostIn, State24.get24, State8.get8]
    rw [e0, e5, e6, e7, ew8, e10, e11, e12, e13, e14, Bool.true_and]
  rw [hst3Eq]
  exact hFinal st3R b0 b5 b6 (hcB.1.trans b4) hw8_3 h10_2 (hcB.2.1.trans b2)
    (hcB.2.2.1.trans (congrArg (fun u ↦ xor u (!oddPass)) b1))
    (hcB.2.2.2.trans (congrArg Bool.not b7)) h14_2 h15_2

theorem pre3_pack16_2 (oddPass : Bool) (xo' : Fin 256) (so : Bool) (b : Fin 32) (si neg : Bool) :
    let st0 := specA57 (pack16 xo' so b si neg)
    let st3 := phasePre3 oddPass st0
    runSteps24 hk23Le24 (preB57 oddPass ++ (midCsA57 ++ midCsB57 oddPass)) st0 = some st3 ∧
      mergeState24 maskPost (canonPost st3) st3 = st3 ∧
      (xo'.val < 126 → st0.get24 8 = false ∧ st3.get24 15 = si ∧ st0.get24 16 = neg ∧
        canonPost st3 = twoBodyPostIn (sPre_3 oddPass xo') b) ∧
      (126 ≤ xo'.val → st0.get24 8 = true ∧ st3.get24 15 = so ∧
        canonPost st3 = ge126PostIn oddPass (sPre_3 oddPass xo') si) := by
  intro st0 st3; obtain ⟨hPreEq, hg8⟩ := specA57_low9_pack16 xo' so b si neg
  obtain ⟨h17_0, hw18_0, hb0⟩ := specA57_borrows (pack16 xo' so b si neg)
  obtain ⟨hrPre3, hm4⟩ := phasePre3_run oddPass st0 h17_0 hw18_0 hb0
  have hsPre : step24_2 (preB57 oddPass) (canonPre st0) = sPre_3 oddPass xo' := by
    dsimp only [sPre_3, st0]; rw [hPreEq]
  refine ⟨hrPre3, hm4, fun hxo' ↦ ?_, fun h126 ↦ ?_⟩
  · have hw8_0 : st0.get24 8 = false :=
      hg8.trans ((xoW8_ok oddPass xo').1.trans (decide_eq_false (by omega)))
    have hw8S : (sPre_3 oddPass xo').q1.b0 = false :=
      (xoW8_ok oddPass xo').2.trans (decide_eq_false (by omega))
    obtain ⟨h15, hPost⟩ := phasePre3_of_w8_false oddPass st0 (sPre_3 oddPass xo') hsPre hw8S
    have hsi : st0.q1.b7 = si := by
      dsimp only [st0, specA57]; generalize step24_2 _ _ = sA; rfl
    have h16 : st0.get24 16 = neg := by
      dsimp only [st0, specA57]; generalize step24_2 _ _ = sA; rfl
    refine ⟨hw8_0, h15.trans hsi, h16, hPost.trans ?_⟩
    dsimp only [st0, specA57]; generalize step24_2 _ _ = sA
    generalize sPre_3 oddPass xo' = sp at hw8S ⊢
    dsimp only [canonPost, twoBodyPostIn, zeroState8, mergeState24, mergeState8, maskPre,
      maskA2, fastMergeMaskA, State24.get24, State8.get8, initState23, pack16]
    rw [hw8S]; rfl
  · have hw8_0 : st0.get24 8 = true :=
      hg8.trans ((xoW8_ok oddPass xo').1.trans (decide_eq_true h126))
    have hw8S : (sPre_3 oddPass xo').q1.b0 = true :=
      (xoW8_ok oddPass xo').2.trans (decide_eq_true h126)
    obtain ⟨h15, hPost⟩ := phasePre3_of_w8_true oddPass st0 (sPre_3 oddPass xo') hsPre hw8S
    have hso : st0.q1.b1 = so := by
      dsimp only [st0, specA57]; generalize step24_2 _ _ = sA; rfl
    have hsi : st0.q1.b7 = si := by
      dsimp only [st0, specA57]; generalize step24_2 _ _ = sA; rfl
    exact ⟨hw8_0, h15.trans hso, hPost.trans (by rw [hsi])⟩

theorem post_spec_all (oddPass : Bool) (x16 : Fin 16 → Bool) :
    let st0 := specA57 x16
    runSteps24 hk23Le24 (stepsB57 oddPass) st0 = some (specB57 oddPass st0) ∧
      (∀ k : Fin 6, (specB57 oddPass st0).get24 ⟨17 + k.val, by omega⟩ = false) ∧
      pair8NatOf10 (ctrl10OfState24 (specB57 oddPass st0)) < 145 := by
  have hx16 := pack16_eq_self_bound50 x16
  set xo' := finOfBits 8 fun i ↦ x16 ⟨i.val, by omega⟩
  set b := finOfBits 5 fun j ↦ x16 ⟨9 + j.val, by omega⟩
  intro st0
  have hst0 : st0 = specA57 (pack16 xo' (x16 8) b (x16 14) (x16 15)) :=
    congrArg specA57 hx16.symm
  obtain ⟨hrPre3, hm4, h2B, h1B⟩ := pre3_pack16_2 oddPass xo' (x16 8) b (x16 14) (x16 15)
  rw [← hst0] at hrPre3 hm4 h2B h1B
  let st3 := phasePre3 oddPass st0
  have hPostChk : checkPost oddPass (canonPost st3) = true := by
    by_cases hxo' : xo'.val < 126
    · rw [(h2B hxo').2.2.2]; exact post2B_ok oddPass xo' hxo' b
    · rw [(h1B (by omega)).2.2]; exact post1B_ok oddPass xo' (by omega) (x16 14)
  have hok4 := unpack_checkPost hPostChk
  have hr4 : runSteps24 hk23Le24 (postB57 oddPass) st3 = some (specB57 oddPass st0) := by
    dsimp only [specB57, st3]; conv_lhs => rw [← hm4]
    exact runSteps24_merge hk23Le24 maskPost _ (maskPost_all oddPass) _ _ st3 hok4.1
  refine ⟨by rw [stepsB57, runSteps24_append hk23Le24 _ _ st0 st3 hrPre3, hr4], fun k ↦ ?_, ?_⟩
  · dsimp only [specB57]; rw [borrow_mergeMaskPost]
    fin_cases k <;> [exact hok4.2.1; exact hok4.2.2.1; exact hok4.2.2.2.1; exact hok4.2.2.2.2.1;
      exact hok4.2.2.2.2.2.1; exact hok4.2.2.2.2.2.2.1]
  · dsimp only [specB57]; rw [ctrl10_mergeMaskPost]; exact hok4.2.2.2.2.2.2.2

theorem runSteps24StepsB57 (oddPass : Bool) (x16 : Fin 16 → Bool) :
    runSteps24 hk23Le24 (stepsB57 oddPass) (specA57 x16) =
      some (specB57 oddPass (specA57 x16)) := (post_spec_all oddPass x16).1
theorem specB57_borrows_false (oddPass : Bool) (x16 : Fin 16 → Bool) (k : Fin 6) :
    (specB57 oddPass (specA57 x16)).get24 ⟨17 + k.val, by omega⟩ = false :=
  (post_spec_all oddPass x16).2.1 k
theorem ctrl10_pair8_lt145_2 (oddPass : Bool) (x16 : Fin 16 → Bool) :
    pair8NatOf10 (ctrl10OfState24 (specB57 oddPass (specA57 x16))) < 145 :=
  (post_spec_all oddPass x16).2.2

end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.BellRouter57
end
