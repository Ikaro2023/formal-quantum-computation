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

public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.NestedCtxWRouter

set_option linter.style.longLine false
set_option Elab.async false
set_option compiler.extract_closed false

@[expose] public section
set_option allowUnsafeReducibility true

namespace QuantumComputation.Specs.StoppingPowerSolution

noncomputable section STrue18Compact113

section
namespace STrue18Compact113
section ConfigK5
set_option maxRecDepth 65536
set_option exponentiation.threshold 5000
set_option backward.isDefEq.respectTransparency false
local instance (priority := 10) instNeZeroTwoPowSC (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩
noncomputable section
open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt HermitianMat Real
open scoped Matrix ComplexOrder MatrixOrder BigOperators Matrix.Norms.L2Operator
open SpecsAux SpecsAux.SpecMirror
-- Root solution namespace already active.
open MeasureBranchHadamardSem (bit_cases)
open MomSlots35Slot3ProjNuclear (shellMu3 shellMu3_lt_seven shellMagCoord3)
open StepBBlock0 (TempCtxLiftEx IsMutBlock u22_testBit_eq_wire)
open Prod57BoothHoist StepBOuter
open Slot3Outer2344AndRelayWide.PosPhase246 (progSupportsBelowB truncateCtxB)
open Slot3Outer2344AndRelayWide.Slot3MidKickWidthWide (progDisjointBad)
open Slot3Outer2344AndRelayWide.Slot3Exact216PrunedAccAndCore (magUnpack63_275 magUnpack63_275_spec
  mu3OneHot7GeFastOps mu3OneHot7GeFast_meta3 mu3OneHot7GeFastCheck mu3OneHot7GeFast_eval_ok)
open Slot3ZRetCore
open True18Compact99
open Slot3Norm1s36CoreWide
open Leaf3Slot3ZRet193
open Leaf3Slot3ZRetOuter
/-- 5-input (`32`-state) dual `b0`-mux: allocates 4 wires (`zA, zB, tzA, tzB`) using `2`
  `TempAnd`s. -/
def b0Mux2Ops : List Slot3MicroEngineAux.MicroOp := [
  .cnotW 1 2, .andAlloc 0 2, .cnotW 1 2, .cnotW 1 5,
  .cnotW 3 4, .andAlloc 0 4, .cnotW 3 4, .cnotW 3 6,
  .zeroAlloc, .cnotW 5 7, .cnotW 1 7, .cnotW 2 7,
  .zeroAlloc, .cnotW 6 8, .cnotW 3 8, .cnotW 4 8
]
theorem b0Mux2_meta :
    Slot3MicroEngineAux.microValid 5 b0Mux2Ops = true ∧
      Slot3MicroEngineAux.microAllocs b0Mux2Ops = 4 ∧
      Slot3MicroEngineAux.microAnds b0Mux2Ops = 2 := by decide
def b0Mux2Check (x : ℕ) : Bool :=
  let st := Slot3MicroEngineAux.evalMicroList 5 b0Mux2Ops (Slot3MicroEngineAux.initBoolList 5 9 x)
  let b0 := x.testBit 0
  Slot3MicroEngineAux.allBelow 5 (fun i ↦ Slot3MicroEngineAux.getBoolAt st i == x.testBit i) &&
    (Slot3MicroEngineAux.getBoolAt st 5 == (if b0 then x.testBit 2 else x.testBit 1)) &&
    (Slot3MicroEngineAux.getBoolAt st 6 == (if b0 then x.testBit 4 else x.testBit 3)) &&
    (Slot3MicroEngineAux.getBoolAt st 7 == (if b0 then x.testBit 1 else x.testBit 2)) &&
    (Slot3MicroEngineAux.getBoolAt st 8 == (if b0 then x.testBit 3 else x.testBit 4))
theorem b0Mux2_eval_ok : Slot3MicroEngineAux.allBelow 32 b0Mux2Check = true := by decide
/-- 6-input (`64`-state) 4-to-1 mux on `(b1, b2)` and `(d0, d1, d2, d3)` using `3` `TempAnd`s. -/
def mux4Ops : List Slot3MicroEngineAux.MicroOp := [
  .cnotW 2 3, .andAlloc 0 3, .cnotW 2 3, .cnotW 2 6,
  .cnotW 4 5, .andAlloc 0 5, .cnotW 4 5, .cnotW 4 7,
  .cnotW 6 7, .andAlloc 1 7, .cnotW 6 8
]
theorem mux4_meta :
    Slot3MicroEngineAux.microValid 6 mux4Ops = true ∧
      Slot3MicroEngineAux.microAllocs mux4Ops = 3 ∧
      Slot3MicroEngineAux.microAnds mux4Ops = 3 := by decide
def mux4Bool (b1 b2 d0 d1 d2 d3 : Bool) : Bool :=
  if b2 then (if b1 then d3 else d2) else (if b1 then d1 else d0)
def mux4Check (x : ℕ) : Bool :=
  let st := Slot3MicroEngineAux.evalMicroList 6 mux4Ops (Slot3MicroEngineAux.initBoolList 6 9 x)
  Slot3MicroEngineAux.allBelow 6 (fun i ↦ Slot3MicroEngineAux.getBoolAt st i == x.testBit i) &&
    (Slot3MicroEngineAux.getBoolAt st 8 ==
      mux4Bool (x.testBit 0) (x.testBit 1) (x.testBit 2) (x.testBit 3) (x.testBit 4) (x.testBit 5))
theorem mux4_eval_ok : Slot3MicroEngineAux.allBelow 64 mux4Check = true := by decide
/-- 6-input (`64`-state) 3-pair dot product with cumulative `ge` differences `(geA ⊕ geB, geB ⊕
  geC, geC)` using `3` `TempAnd`s. -/
def mux3GeOps : List Slot3MicroEngineAux.MicroOp := [
  .cnotW 1 0, .cnotW 2 1,
  .andAlloc 0 3, .andAlloc 1 4, .andAlloc 2 5,
  .cnotW 6 8, .cnotW 7 8,
  .cnotW 2 1, .cnotW 1 0
]
theorem mux3Ge_meta :
    Slot3MicroEngineAux.microValid 6 mux3GeOps = true ∧
      Slot3MicroEngineAux.microAllocs mux3GeOps = 3 ∧
      Slot3MicroEngineAux.microAnds mux3GeOps = 3 := by decide
def mux3GeBool (geA geB geC d0 d1 d2 : Bool) : Bool :=
  xor ((xor geA geB) && d0) (xor ((xor geB geC) && d1) (geC && d2))
def mux3GeCheck (x : ℕ) : Bool :=
  let st := Slot3MicroEngineAux.evalMicroList 6 mux3GeOps (Slot3MicroEngineAux.initBoolList 6 9 x)
  Slot3MicroEngineAux.allBelow 6 (fun i ↦ Slot3MicroEngineAux.getBoolAt st i == x.testBit i) &&
    (Slot3MicroEngineAux.getBoolAt st 8 ==
      mux3GeBool (x.testBit 0) (x.testBit 1) (x.testBit 2) (x.testBit 3) (x.testBit 4) (x.testBit
        5))
theorem mux3Ge_eval_ok : Slot3MicroEngineAux.allBelow 64 mux3GeCheck = true := by decide
/-- 6-input (`64`-state) 3-pair dot product with `(selA, geB ⊕ geC, geC)` using `3` `TempAnd`s. -/
def mux3SelGeOps : List Slot3MicroEngineAux.MicroOp := [
  .cnotW 2 1,
  .andAlloc 0 3, .andAlloc 1 4, .andAlloc 2 5,
  .cnotW 6 8, .cnotW 7 8,
  .cnotW 2 1
]
theorem mux3SelGe_meta :
    Slot3MicroEngineAux.microValid 6 mux3SelGeOps = true ∧
      Slot3MicroEngineAux.microAllocs mux3SelGeOps = 3 ∧
      Slot3MicroEngineAux.microAnds mux3SelGeOps = 3 := by decide
def mux3SelGeBool (selA geB geC d0 d1 d2 : Bool) : Bool :=
  xor (selA && d0) (xor ((xor geB geC) && d1) (geC && d2))
def mux3SelGeCheck (x : ℕ) : Bool :=
  let st :=
    Slot3MicroEngineAux.evalMicroList 6 mux3SelGeOps (Slot3MicroEngineAux.initBoolList 6 9 x)
  Slot3MicroEngineAux.allBelow 6 (fun i ↦ Slot3MicroEngineAux.getBoolAt st i == x.testBit i) &&
    (Slot3MicroEngineAux.getBoolAt st 8 ==
      mux3SelGeBool (x.testBit 0) (x.testBit 1) (x.testBit 2) (x.testBit 3) (x.testBit 4) (x.testBit
        5))
theorem mux3SelGe_eval_ok : Slot3MicroEngineAux.allBelow 64 mux3SelGeCheck = true := by decide
/-- 4-input (`16`-state) 2-pair dot product with `(geB ⊕ geC, geC)` using `2` `TempAnd`s. -/
def mux2GeOps : List Slot3MicroEngineAux.MicroOp := [
  .cnotW 1 0,
  .andAlloc 0 2, .andAlloc 1 3,
  .cnotW 4 5,
  .cnotW 1 0
]
theorem mux2Ge_meta :
    Slot3MicroEngineAux.microValid 4 mux2GeOps = true ∧
      Slot3MicroEngineAux.microAllocs mux2GeOps = 2 ∧
      Slot3MicroEngineAux.microAnds mux2GeOps = 2 := by decide
def mux2GeBool (geB geC d1 d2 : Bool) : Bool := xor ((xor geB geC) && d1) (geC && d2)
def mux2GeCheck (x : ℕ) : Bool :=
  let st := Slot3MicroEngineAux.evalMicroList 4 mux2GeOps (Slot3MicroEngineAux.initBoolList 4 6 x)
  Slot3MicroEngineAux.allBelow 4 (fun i ↦ Slot3MicroEngineAux.getBoolAt st i == x.testBit i) &&
    (Slot3MicroEngineAux.getBoolAt st 5 ==
      mux2GeBool (x.testBit 0) (x.testBit 1) (x.testBit 2) (x.testBit 3))
theorem mux2Ge_eval_ok : Slot3MicroEngineAux.allBelow 16 mux2GeCheck = true := by decide
/-- 5-input (`32`-state) tail for rows `b = 5` and `b = 6` using `3` `TempAnd`s. -/
def tail56Ops : List Slot3MicroEngineAux.MicroOp := [
  .andAlloc 0 2, .andAlloc 1 3, .cnotW 5 6,
  .andAlloc 1 4
]
theorem tail56_meta :
    Slot3MicroEngineAux.microValid 5 tail56Ops = true ∧
      Slot3MicroEngineAux.microAllocs tail56Ops = 3 ∧
      Slot3MicroEngineAux.microAnds tail56Ops = 3 := by decide
def tail56Bool5 (sel5 ge6 uA uB : Bool) : Bool := xor (sel5 && uA) (ge6 && uB)
def tail56Check (x : ℕ) : Bool :=
  let st := Slot3MicroEngineAux.evalMicroList 5 tail56Ops (Slot3MicroEngineAux.initBoolList 5 8 x)
  Slot3MicroEngineAux.allBelow 5 (fun i ↦ Slot3MicroEngineAux.getBoolAt st i == x.testBit i) &&
    (Slot3MicroEngineAux.getBoolAt st 6 ==
      tail56Bool5 (x.testBit 0) (x.testBit 1) (x.testBit 2) (x.testBit 3)) &&
    (Slot3MicroEngineAux.getBoolAt st 7 == (x.testBit 1 && x.testBit 4))
theorem tail56_eval_ok : Slot3MicroEngineAux.allBelow 32 tail56Check = true := by decide
/-- 6-input (`64`-state) 3-pair dot product `(s0*d0) ⊕ (s1*d1) ⊕ (s2*d2)` using `3` `TempAnd`s. -/
def dot3Ops : List Slot3MicroEngineAux.MicroOp := [
  .andAlloc 0 3, .andAlloc 1 4, .andAlloc 2 5,
  .cnotW 6 8, .cnotW 7 8
]
theorem dot3_meta :
    Slot3MicroEngineAux.microValid 6 dot3Ops = true ∧
      Slot3MicroEngineAux.microAllocs dot3Ops = 3 ∧
      Slot3MicroEngineAux.microAnds dot3Ops = 3 := by decide
def dot3Bool (s0 s1 s2 d0 d1 d2 : Bool) : Bool := xor (s0 && d0) (xor (s1 && d1) (s2 && d2))
def dot3Check (x : ℕ) : Bool :=
  let st := Slot3MicroEngineAux.evalMicroList 6 dot3Ops (Slot3MicroEngineAux.initBoolList 6 9 x)
  Slot3MicroEngineAux.allBelow 6 (fun i ↦ Slot3MicroEngineAux.getBoolAt st i == x.testBit i) &&
    (Slot3MicroEngineAux.getBoolAt st 8 ==
      dot3Bool (x.testBit 0) (x.testBit 1) (x.testBit 2) (x.testBit 3) (x.testBit 4) (x.testBit 5))
theorem dot3_eval_ok : Slot3MicroEngineAux.allBelow 64 dot3Check = true := by decide
/-- 5-input (`32`-state) 2-pair dot product plus accumulator `acc ⊕ (s0*d0) ⊕ (s1*d1)` using `2`
  `TempAnd`s. -/
def dot2XorOps : List Slot3MicroEngineAux.MicroOp := [
  .andAlloc 0 2, .andAlloc 1 3,
  .cnotW 4 6, .cnotW 5 6
]
theorem dot2Xor_meta :
    Slot3MicroEngineAux.microValid 5 dot2XorOps = true ∧
      Slot3MicroEngineAux.microAllocs dot2XorOps = 2 ∧
      Slot3MicroEngineAux.microAnds dot2XorOps = 2 := by decide
def dot2XorBool (s0 s1 d0 d1 acc : Bool) : Bool := xor acc (xor (s0 && d0) (s1 && d1))
def dot2XorCheck (x : ℕ) : Bool :=
  let st := Slot3MicroEngineAux.evalMicroList 5 dot2XorOps (Slot3MicroEngineAux.initBoolList 5 7 x)
  Slot3MicroEngineAux.allBelow 5 (fun i ↦ Slot3MicroEngineAux.getBoolAt st i == x.testBit i) &&
    (Slot3MicroEngineAux.getBoolAt st 6 ==
      dot2XorBool (x.testBit 0) (x.testBit 1) (x.testBit 2) (x.testBit 3) (x.testBit 4))
theorem dot2Xor_eval_ok : Slot3MicroEngineAux.allBelow 32 dot2XorCheck = true := by decide
-- Input wire vectors
def kb1In5W : Fin 5 → Wire 437 := ![muW 0, u22WAux 1, u22WAux 2, u22WAux 3, u22WAux 4]
def kb2In5W : Fin 5 → Wire 437 := ![muW 0, u22WAux 5, u22WAux 6, u22WAux 7, u22WAux 8]
def kb3In5W : Fin 5 → Wire 437 := ![muW 0, u22WAux 9, u22WAux 10, u22WAux 13, u22WAux 15]
def kb4In5W : Fin 5 → Wire 437 := ![muW 0, u22WAux 2, u22WAux 4, u22WAux 6, u22WAux 8]
def kb5In5W : Fin 5 → Wire 437 := ![muW 0, u22WAux 10, u22WAux 12, u22WAux 14, u22WAux 16]
theorem kb1In5W_inj : Function.Injective kb1In5W := by decide
theorem kb2In5W_inj : Function.Injective kb2In5W := by decide
theorem kb3In5W_inj : Function.Injective kb3In5W := by decide
theorem kb4In5W_inj : Function.Injective kb4In5W := by decide
theorem kb5In5W_inj : Function.Injective kb5In5W := by decide
def kw1_0In6W : Fin 6 → Wire 437 :=
  ![muW 1, muW 2, ⟨296, by decide⟩, ⟨297, by decide⟩, ⟨300, by decide⟩, u22WAux 7]
def kw2_0In6W : Fin 6 → Wire 437 :=
  ![muW 1, muW 2, ⟨308, by decide⟩, ⟨309, by decide⟩, ⟨312, by decide⟩, u22WAux 14]
def kw1_1In6W : Fin 6 → Wire 437 :=
  ![magGeW 1, magGeW 3, magGeW 5, ⟨299, by decide⟩, ⟨302, by decide⟩, ⟨303, by decide⟩]
def kw1_2In6W : Fin 6 → Wire 437 :=
  ![magGeW 2, magGeW 4, magGeW 6, ⟨300, by decide⟩, ⟨301, by decide⟩, u22WAux 9]
def kw1_3In4W : Fin 4 → Wire 437 :=
  ![magGeW 3, magGeW 5, ⟨303, by decide⟩, ⟨306, by decide⟩]
def kw1_4In4W : Fin 4 → Wire 437 :=
  ![magGeW 4, magGeW 6, ⟨304, by decide⟩, u22WAux 11]
def kw1_56In5W : Fin 5 → Wire 437 :=
  ![magSel7W 5, magGeW 6, u22WAux 11, u22WAux 12, u22WAux 13]
def kw2_1aIn6W : Fin 6 → Wire 437 :=
  ![magSel7W 1, magSel7W 2, magSel7W 3, u22WAux 5, u22WAux 7, u22WAux 9]
def kw2_1bIn5W : Fin 5 → Wire 437 :=
  ![magSel7W 4, magGeW 5, u22WAux 11, ⟨307, by decide⟩, ⟨337, by decide⟩]
def kw2_2In6W : Fin 6 → Wire 437 :=
  ![magSel7W 2, magGeW 3, magGeW 5, u22WAux 8, ⟨314, by decide⟩, ⟨315, by decide⟩]
def kw2_3In6W : Fin 6 → Wire 437 :=
  ![magSel7W 3, magGeW 4, magGeW 6, u22WAux 11, ⟨305, by decide⟩, u22WAux 17]
def kw2_4In4W : Fin 4 → Wire 437 :=
  ![magGeW 4, magGeW 6, ⟨313, by decide⟩, u22WAux 18]
def kw2_56In5W : Fin 5 → Wire 437 :=
  ![magSel7W 5, magGeW 6, u22WAux 17, u22WAux 19, u22WAux 20]
theorem kw1_0In6W_inj : Function.Injective kw1_0In6W := by decide
theorem kw2_0In6W_inj : Function.Injective kw2_0In6W := by decide
theorem kw1_1In6W_inj : Function.Injective kw1_1In6W := by decide
theorem kw1_2In6W_inj : Function.Injective kw1_2In6W := by decide
theorem kw1_3In4W_inj : Function.Injective kw1_3In4W := by decide
theorem kw1_4In4W_inj : Function.Injective kw1_4In4W := by decide
theorem kw1_56In5W_inj : Function.Injective kw1_56In5W := by decide
theorem kw2_1aIn6W_inj : Function.Injective kw2_1aIn6W := by decide
theorem kw2_1bIn5W_inj : Function.Injective kw2_1bIn5W := by decide
theorem kw2_2In6W_inj : Function.Injective kw2_2In6W := by decide
theorem kw2_3In6W_inj : Function.Injective kw2_3In6W := by decide
theorem kw2_4In4W_inj : Function.Injective kw2_4In4W := by decide
theorem kw2_56In5W_inj : Function.Injective kw2_56In5W := by decide
def magSrc21Fast : Fin 21 → Wire 437 :=
  ![⟨289, by decide⟩, ⟨290, by decide⟩, ⟨291, by decide⟩, ⟨292, by decide⟩,
    ⟨293, by decide⟩, ⟨294, by decide⟩, ⟨295, by decide⟩,
    ⟨318, by decide⟩, ⟨324, by decide⟩, ⟨327, by decide⟩, ⟨329, by decide⟩,
    ⟨331, by decide⟩, ⟨333, by decide⟩, ⟨334, by decide⟩,
    ⟨321, by decide⟩, ⟨339, by decide⟩, ⟨342, by decide⟩, ⟨345, by decide⟩,
    ⟨347, by decide⟩, ⟨349, by decide⟩, ⟨350, by decide⟩]
def ctxMagHead6 : TempCtx 437 :=
  let k1 := Slot3MicroEngineAux.ctxMicro muQuadIn6W muQuadIn6W_inj 275 14 0
    (fun i ↦ by revert i; decide)
    mu3OneHot7GeFromQuadOps mu3OneHot7GeFromQuad_meta (by decide)
  let k2 := ctxCliffAlloc (.cnot (u22WAux 0) ⟨289, by decide⟩ (by decide))
  let k3 := Slot3MicroEngineAux.ctxAndPairs 6 290 (by decide)
    (fun i : Fin 6 ↦ magGeW ⟨i.val + 1, by omega⟩)
    (fun i : Fin 6 ↦ u22WAux ⟨i.val + 1, by omega⟩)
    (fun i ↦ wire_ne_of_gt (by
      have hb := Slot3MicroEngineAux.mu3GeSlots_bounds ⟨i.val + 1, by omega⟩
      dsimp at hb; dsimp [magGeW, u22WAux]; omega))
    (fun i ↦ by
      have hb := Slot3MicroEngineAux.mu3GeSlots_bounds ⟨i.val + 1, by omega⟩
      dsimp at hb; dsimp [magGeW]; omega)
    (fun i ↦ by dsimp [u22WAux]; omega)
  k1.append (k2.append k3)
def ctxKb1 : TempCtx 437 :=
  Slot3MicroEngineAux.ctxMicro kb1In5W kb1In5W_inj 296 4 2
    (fun i ↦ by revert i; decide) b0Mux2Ops b0Mux2_meta (by decide)
def ctxKb2 : TempCtx 437 :=
  Slot3MicroEngineAux.ctxMicro kb2In5W kb2In5W_inj 300 4 2
    (fun i ↦ by revert i; decide) b0Mux2Ops b0Mux2_meta (by decide)
def ctxKb3 : TempCtx 437 :=
  Slot3MicroEngineAux.ctxMicro kb3In5W kb3In5W_inj 304 4 2
    (fun i ↦ by revert i; decide) b0Mux2Ops b0Mux2_meta (by decide)
def ctxKb4 : TempCtx 437 :=
  Slot3MicroEngineAux.ctxMicro kb4In5W kb4In5W_inj 308 4 2
    (fun i ↦ by revert i; decide) b0Mux2Ops b0Mux2_meta (by decide)
def ctxKb5 : TempCtx 437 :=
  Slot3MicroEngineAux.ctxMicro kb5In5W kb5In5W_inj 312 4 2
    (fun i ↦ by revert i; decide) b0Mux2Ops b0Mux2_meta (by decide)
def ctxMagB0_10 : TempCtx 437 :=
  ctxKb1.append (ctxKb2.append (ctxKb3.append (ctxKb4.append ctxKb5)))
def ctxKw1_0 : TempCtx 437 :=
  Slot3MicroEngineAux.ctxMicro kw1_0In6W kw1_0In6W_inj 316 3 3
    (fun i ↦ by revert i; decide) mux4Ops mux4_meta (by decide)
def ctxKw2_0 : TempCtx 437 :=
  Slot3MicroEngineAux.ctxMicro kw2_0In6W kw2_0In6W_inj 319 3 3
    (fun i ↦ by revert i; decide) mux4Ops mux4_meta (by decide)
def ctxKw1_1 : TempCtx 437 :=
  Slot3MicroEngineAux.ctxMicro kw1_1In6W kw1_1In6W_inj 322 3 3
    (fun i ↦ by revert i; decide) mux3GeOps mux3Ge_meta (by decide)
def ctxKw1_2 : TempCtx 437 :=
  Slot3MicroEngineAux.ctxMicro kw1_2In6W kw1_2In6W_inj 325 3 3
    (fun i ↦ by revert i; decide) mux3GeOps mux3Ge_meta (by decide)
def ctxKw1_3 : TempCtx 437 :=
  Slot3MicroEngineAux.ctxMicro kw1_3In4W kw1_3In4W_inj 328 2 2
    (fun i ↦ by revert i; decide) mux2GeOps mux2Ge_meta (by decide)
def ctxKw1_4 : TempCtx 437 :=
  Slot3MicroEngineAux.ctxMicro kw1_4In4W kw1_4In4W_inj 330 2 2
    (fun i ↦ by revert i; decide) mux2GeOps mux2Ge_meta (by decide)
def ctxKw1_56 : TempCtx 437 :=
  Slot3MicroEngineAux.ctxMicro kw1_56In5W kw1_56In5W_inj 332 3 3
    (fun i ↦ by revert i; decide) tail56Ops tail56_meta (by decide)
def ctxKw2_1a : TempCtx 437 :=
  Slot3MicroEngineAux.ctxMicro kw2_1aIn6W kw2_1aIn6W_inj 335 3 3
    (fun i ↦ by revert i; decide) dot3Ops dot3_meta (by decide)
def ctxKw2_1b : TempCtx 437 :=
  Slot3MicroEngineAux.ctxMicro kw2_1bIn5W kw2_1bIn5W_inj 338 2 2
    (fun i ↦ by revert i; decide) dot2XorOps dot2Xor_meta (by decide)
def ctxKw2_2 : TempCtx 437 :=
  Slot3MicroEngineAux.ctxMicro kw2_2In6W kw2_2In6W_inj 340 3 3
    (fun i ↦ by revert i; decide) mux3SelGeOps mux3SelGe_meta (by decide)
def ctxKw2_3 : TempCtx 437 :=
  Slot3MicroEngineAux.ctxMicro kw2_3In6W kw2_3In6W_inj 343 3 3
    (fun i ↦ by revert i; decide) mux3SelGeOps mux3SelGe_meta (by decide)
def ctxKw2_4 : TempCtx 437 :=
  Slot3MicroEngineAux.ctxMicro kw2_4In4W kw2_4In4W_inj 346 2 2
    (fun i ↦ by revert i; decide) mux2GeOps mux2Ge_meta (by decide)
def ctxKw2_56 : TempCtx 437 :=
  Slot3MicroEngineAux.ctxMicro kw2_56In5W kw2_56In5W_inj 348 3 3
    (fun i ↦ by revert i; decide) tail56Ops tail56_meta (by decide)
def ctxMagRows35 : TempCtx 437 :=
  ctxKw1_0.append (ctxKw2_0.append (ctxKw1_1.append (ctxKw1_2.append (ctxKw1_3.append
    (ctxKw1_4.append
    (ctxKw1_56.append (ctxKw2_1a.append (ctxKw2_1b.append (ctxKw2_2.append (ctxKw2_3.append
      (ctxKw2_4.append ctxKw2_56)))))))))))
def magUnpackFromRetQuad51_275Ctx : TempCtx 437 :=
  ctxMagHead6.append (ctxMagB0_10.append ctxMagRows35)
def magUnpackFromRetQuad51_275 : TempPhaseProg 437 :=
  xorBlockProg 21 magDest21 magSrc21Fast
    (fun idx ↦ by dsimp [magDest21, p57MW]; omega)
    (fun idx ↦ by revert idx; decide)
    magUnpackFromRetQuad51_275Ctx
abbrev mutMagDest21 (q : Wire 437) : Prop := ∃ idx, q = magDest21 idx
private theorem not_mutMagDest21_of_outside (q : Wire 437)
    (hq : decide (q.val < 177 ∨ 198 ≤ q.val) = true) : ¬ mutMagDest21 q := by
  rintro ⟨idx, rfl⟩
  have h := of_decide_eq_true hq
  dsimp [magDest21, p57MW] at h
  omega
private theorem not_mutMagDest21_ge275 (q : Wire 437) (hq : 275 ≤ q.val) : ¬ mutMagDest21 q := by
  rintro ⟨idx, rfl⟩; dsimp [magDest21, p57MW] at hq; omega
private theorem boolToZMod2_decide_eq_oneAux (B : Bool) :
    decide (Slot3MicroEngineAux.boolToZMod2 B = 1) = B := by
  cases B <;> rfl
private theorem tb_in {K : ℕ} (inW : Fin K → Wire 437) (γ : BitAssignment 437)
    (i : Fin K) {B : Bool} (hB : γ (inW i) = Slot3MicroEngineAux.boolToZMod2 B) :
    (bitsVal (fun j ↦ γ (inW j))).testBit i.val = B := by
  rw [Slot3MicroEngineAux.bitsVal_testBit_eq, hB, boolToZMod2_decide_eq_oneAux]
structure MagCtxPkg (base endB ands : ℕ) (ctx : TempCtx 437) : Prop where
  hle : base ≤ endB
  cnt : ctx.countTempAnd = ands
  disj : ctx.DisjointFrom mutMagDest21
  supp : ctx.SupportsBelowCtx endB
  lift : Slot3MicroEngineAux.TempCtxLiftEx base endB ctx
  clean : ∀ γ, cleanRem 437 (437 - base) γ → cleanRem 437 (437 - endB) (ctx.fwdBits γ)
  pres : ∀ γ, cleanRem 437 (437 - base) γ → ∀ q : Wire 437, q.val < base → ctx.fwdBits γ q = γ q
theorem MagCtxPkg.append {b0 b1 b2 a1 a2 : ℕ} {c1 c2 : TempCtx 437}
    (h1 : MagCtxPkg b0 b1 a1 c1) (h2 : MagCtxPkg b1 b2 a2 c2) :
    MagCtxPkg b0 b2 (a1 + a2) (c1.append c2) where
  hle := le_trans h1.hle h2.hle
  cnt := by rw [Slot3MicroEngineAux.TempCtx.append_countTempAnd, h1.cnt, h2.cnt]
  disj := TempCtx.disjointFrom_append h1.disj h2.disj
  supp := TempCtx.supportsBelowCtx_append h2.hle h1.supp h2.supp
  lift := Slot3MicroEngineAux.TempCtxLiftEx.append h1.lift h2.lift
  clean γ hγ := by
    rw [Slot3MicroEngineAux.TempCtx.append_fwdBits]
    exact h2.clean _ (h1.clean γ hγ)
  pres γ hγ q hq := by
    have hq1 : q.val < b1 := lt_of_lt_of_le hq h1.hle
    rw[Slot3MicroEngineAux.TempCtx.append_fwdBits, h2.pres (c1.fwdBits γ) (h1.clean γ hγ) q hq1,
        h1.pres γ hγ q hq]
private theorem ctxB0Mux2_spec (inW : Fin 5 → Wire 437) (hinj : Function.Injective inW)
    (base : ℕ) (hbase : base + 4 ≤ 437) (h275 : 275 ≤ base)
    (hin : ∀ i, (inW i).val < base)
    (hmut : ∀ i, decide ((inW i).val < 177 ∨ 198 ≤ (inW i).val) = true) :
    let ctx := Slot3MicroEngineAux.ctxMicro inW hinj base 4 2 hin b0Mux2Ops b0Mux2_meta hbase
    MagCtxPkg base (base + 4) 2 ctx ∧
      (∀ (γ : BitAssignment 437) (b0 a0 b0' a1 b1' : Bool),
        cleanRem 437 (437 - base) γ →
        γ (inW 0) = Slot3MicroEngineAux.boolToZMod2 b0 →
        γ (inW 1) = Slot3MicroEngineAux.boolToZMod2 a0 →
        γ (inW 2) = Slot3MicroEngineAux.boolToZMod2 b0' →
        γ (inW 3) = Slot3MicroEngineAux.boolToZMod2 a1 →
        γ (inW 4) = Slot3MicroEngineAux.boolToZMod2 b1' →
        ctx.fwdBits γ ⟨base, by omega⟩ = Slot3MicroEngineAux.boolToZMod2 (if b0 then b0' else a0) ∧
        ctx.fwdBits γ ⟨base + 1,
          by omega⟩ = Slot3MicroEngineAux.boolToZMod2 (if b0 then b1' else a1) ∧
        ctx.fwdBits γ ⟨base + 2,
          by omega⟩ = Slot3MicroEngineAux.boolToZMod2 (if b0 then a0 else b0') ∧
        ctx.fwdBits γ ⟨base + 3,
          by omega⟩ = Slot3MicroEngineAux.boolToZMod2 (if b0 then a1 else b1')) := by
  obtain ⟨hCnt, hProps, hLift, hEval⟩ :=
    Slot3MicroEngineAux.ctxMicro_scoped inW hinj base 4 2 hin b0Mux2Ops b0Mux2_meta hbase
  obtain ⟨hd, hs⟩ := hProps (mutW := mutMagDest21)
    (fun i ↦ not_mutMagDest21_of_outside (inW i) (hmut i))
    (fun q hq ↦ not_mutMagDest21_ge275 q (by omega))
  have hAll : ∀ γ : BitAssignment 437, cleanRem 437 (437 - base) γ →
      let x := bitsVal (fun i ↦ γ (inW i))
      let st :=
        Slot3MicroEngineAux.evalMicroList 5 b0Mux2Ops (Slot3MicroEngineAux.initBoolList 5 9 x)
      let b0 := x.testBit 0
      Slot3MicroEngineAux.allBelow 5 (fun i ↦
        Slot3MicroEngineAux.getBoolAt st i == x.testBit i) = true ∧
      Slot3MicroEngineAux.getBoolAt st 5 = (if b0 then x.testBit 2 else x.testBit 1) ∧
      Slot3MicroEngineAux.getBoolAt st 6 = (if b0 then x.testBit 4 else x.testBit 3) ∧
      Slot3MicroEngineAux.getBoolAt st 7 = (if b0 then x.testBit 1 else x.testBit 2) ∧
      Slot3MicroEngineAux.getBoolAt st 8 = (if b0 then x.testBit 3 else x.testBit 4) := fun γ _ ↦ by
    have hx_lt : bitsVal (fun i ↦ γ (inW i)) < 32 := bitsVal_lt_two_pow _
    have hchk := (Slot3MicroEngineAux.allBelow_iff 32 b0Mux2Check).mp b0Mux2_eval_ok _ hx_lt
    dsimp only [b0Mux2Check] at hchk
    simp only [Bool.and_eq_true, beq_iff_eq] at hchk
    exact ⟨hchk.1.1.1.1, hchk.1.1.1.2, hchk.1.1.2, hchk.1.2, hchk.2⟩
  refine ⟨⟨by omega, hCnt, hd, hs, hLift, fun γ hcl ↦ (hEval γ hcl).1,
      fun γ hcl ↦ (hEval γ hcl).2.1 (hAll γ hcl).1⟩,
    fun γ b0 a0 b0' a1 b1' hcl h0 h1 h2 h3 h4 ↦ ?_⟩
  obtain ⟨_, _, hsOut⟩ := hEval γ hcl
  obtain ⟨_, ho5, ho6, ho7, ho8⟩ := hAll γ hcl
  have ht0 := tb_in inW γ 0 h0
  have ht1 := tb_in inW γ 1 h1
  have ht2 := tb_in inW γ 2 h2
  have ht3 := tb_in inW γ 3 h3
  have ht4 := tb_in inW γ 4 h4
  dsimp only [Fin.val_zero, Fin.val_one, Fin.val_two] at ht0 ht1 ht2
  change (bitsVal (fun j ↦ γ (inW j))).testBit 3 = a1 at ht3
  change (bitsVal (fun j ↦ γ (inW j))).testBit 4 = b1' at ht4
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hw : (⟨base, by omega⟩ : Wire 437) = ⟨base + (5 - 5), by omega⟩ := Fin.ext rfl
    rw [hw, hsOut 5 (by decide) (by decide), ho5, ht0, ht1, ht2]
  · have hw : (⟨base + 1, by omega⟩ : Wire 437) = ⟨base + (6 - 5), by omega⟩ := Fin.ext rfl
    rw [hw, hsOut 6 (by decide) (by decide), ho6, ht0, ht3, ht4]
  · have hw : (⟨base + 2, by omega⟩ : Wire 437) = ⟨base + (7 - 5), by omega⟩ := Fin.ext rfl
    rw [hw, hsOut 7 (by decide) (by decide), ho7, ht0, ht1, ht2]
  · have hw : (⟨base + 3, by omega⟩ : Wire 437) = ⟨base + (8 - 5), by omega⟩ := Fin.ext rfl
    rw [hw, hsOut 8 (by decide) (by decide), ho8, ht0, ht3, ht4]
private theorem ctxMicro6_out8_spec (ops : List Slot3MicroEngineAux.MicroOp)
    (hmeta : Slot3MicroEngineAux.microValid 6 ops = true ∧
      Slot3MicroEngineAux.microAllocs ops = 3 ∧
      Slot3MicroEngineAux.microAnds ops = 3)
    (fnBool : Bool → Bool → Bool → Bool → Bool → Bool → Bool)
    (checkFn : ℕ → Bool)
    (hcheck_def : ∀ x : ℕ, checkFn x =
      (Slot3MicroEngineAux.allBelow 6 (fun i ↦
        Slot3MicroEngineAux.getBoolAt (Slot3MicroEngineAux.evalMicroList 6 ops
          (Slot3MicroEngineAux.initBoolList 6 9 x)) i == x.testBit i) &&
       (Slot3MicroEngineAux.getBoolAt (Slot3MicroEngineAux.evalMicroList 6 ops
         (Slot3MicroEngineAux.initBoolList 6 9 x)) 8 ==
        fnBool (x.testBit 0) (x.testBit 1) (x.testBit 2) (x.testBit 3) (x.testBit 4) (x.testBit
          5))))
    (hok : Slot3MicroEngineAux.allBelow 64 checkFn = true)
    (inW : Fin 6 → Wire 437) (hinj : Function.Injective inW)
    (base : ℕ) (hbase : base + 3 ≤ 437) (h275 : 275 ≤ base)
    (hin : ∀ i, (inW i).val < base)
    (hmut : ∀ i, decide ((inW i).val < 177 ∨ 198 ≤ (inW i).val) = true) :
    let ctx := Slot3MicroEngineAux.ctxMicro inW hinj base 3 3 hin ops hmeta hbase
    MagCtxPkg base (base + 3) 3 ctx ∧
      (∀ (γ : BitAssignment 437) (b0 b1 b2 b3 b4 b5 : Bool),
        cleanRem 437 (437 - base) γ →
        γ (inW 0) = Slot3MicroEngineAux.boolToZMod2 b0 →
        γ (inW 1) = Slot3MicroEngineAux.boolToZMod2 b1 →
        γ (inW 2) = Slot3MicroEngineAux.boolToZMod2 b2 →
        γ (inW 3) = Slot3MicroEngineAux.boolToZMod2 b3 →
        γ (inW 4) = Slot3MicroEngineAux.boolToZMod2 b4 →
        γ (inW 5) = Slot3MicroEngineAux.boolToZMod2 b5 →
        ctx.fwdBits γ ⟨base + 2, by omega⟩ =
          Slot3MicroEngineAux.boolToZMod2 (fnBool b0 b1 b2 b3 b4 b5)) := by
  obtain ⟨hCnt, hProps, hLift, hEval⟩ :=
    Slot3MicroEngineAux.ctxMicro_scoped inW hinj base 3 3 hin ops hmeta hbase
  obtain ⟨hd, hs⟩ := hProps (mutW := mutMagDest21)
    (fun i ↦ not_mutMagDest21_of_outside (inW i) (hmut i))
    (fun q hq ↦ not_mutMagDest21_ge275 q (by omega))
  have hAll : ∀ γ : BitAssignment 437, cleanRem 437 (437 - base) γ →
      let x := bitsVal (fun i ↦ γ (inW i))
      let st := Slot3MicroEngineAux.evalMicroList 6 ops (Slot3MicroEngineAux.initBoolList 6 9 x)
      Slot3MicroEngineAux.allBelow 6 (fun i ↦
        Slot3MicroEngineAux.getBoolAt st i == x.testBit i) = true ∧
      Slot3MicroEngineAux.getBoolAt st 8 =
        fnBool (x.testBit 0) (x.testBit 1) (x.testBit 2) (x.testBit 3) (x.testBit 4) (x.testBit 5)
          := fun γ _ ↦ by
    have hx_lt : bitsVal (fun i ↦ γ (inW i)) < 64 := bitsVal_lt_two_pow _
    have hchk := (Slot3MicroEngineAux.allBelow_iff 64 checkFn).mp hok _ hx_lt
    rw [hcheck_def] at hchk
    simp only [Bool.and_eq_true, beq_iff_eq] at hchk
    exact hchk
  refine ⟨⟨by omega, hCnt, hd, hs, hLift, fun γ hcl ↦ (hEval γ hcl).1,
      fun γ hcl ↦ (hEval γ hcl).2.1 (hAll γ hcl).1⟩,
    fun γ b0 b1 b2 b3 b4 b5 hcl h0 h1 h2 h3 h4 h5 ↦ ?_⟩
  obtain ⟨_, _, hsOut⟩ := hEval γ hcl
  obtain ⟨_, ho8⟩ := hAll γ hcl
  have ht0 := tb_in inW γ 0 h0
  have ht1 := tb_in inW γ 1 h1
  have ht2 := tb_in inW γ 2 h2
  have ht3 := tb_in inW γ 3 h3
  have ht4 := tb_in inW γ 4 h4
  have ht5 := tb_in inW γ 5 h5
  dsimp only [Fin.val_zero, Fin.val_one, Fin.val_two] at ht0 ht1 ht2
  change (bitsVal (fun j ↦ γ (inW j))).testBit 3 = b3 at ht3
  change (bitsVal (fun j ↦ γ (inW j))).testBit 4 = b4 at ht4
  change (bitsVal (fun j ↦ γ (inW j))).testBit 5 = b5 at ht5
  have hw : (⟨base + 2, by omega⟩ : Wire 437) = ⟨base + (8 - 6), by omega⟩ := Fin.ext rfl
  rw [hw, hsOut 8 (by decide) (by decide), ho8, ht0, ht1, ht2, ht3, ht4, ht5]
private theorem ctxMux2Ge_spec (inW : Fin 4 → Wire 437) (hinj : Function.Injective inW)
    (base : ℕ) (hbase : base + 2 ≤ 437) (h275 : 275 ≤ base)
    (hin : ∀ i, (inW i).val < base)
    (hmut : ∀ i, decide ((inW i).val < 177 ∨ 198 ≤ (inW i).val) = true) :
    let ctx := Slot3MicroEngineAux.ctxMicro inW hinj base 2 2 hin mux2GeOps mux2Ge_meta hbase
    MagCtxPkg base (base + 2) 2 ctx ∧
      (∀ (γ : BitAssignment 437) (b0 b1 b2 b3 : Bool),
        cleanRem 437 (437 - base) γ →
        γ (inW 0) = Slot3MicroEngineAux.boolToZMod2 b0 →
        γ (inW 1) = Slot3MicroEngineAux.boolToZMod2 b1 →
        γ (inW 2) = Slot3MicroEngineAux.boolToZMod2 b2 →
        γ (inW 3) = Slot3MicroEngineAux.boolToZMod2 b3 →
        ctx.fwdBits γ ⟨base + 1, by omega⟩ =
          Slot3MicroEngineAux.boolToZMod2 (mux2GeBool b0 b1 b2 b3)) := by
  obtain ⟨hCnt, hProps, hLift, hEval⟩ :=
    Slot3MicroEngineAux.ctxMicro_scoped inW hinj base 2 2 hin mux2GeOps mux2Ge_meta hbase
  obtain ⟨hd, hs⟩ := hProps (mutW := mutMagDest21)
    (fun i ↦ not_mutMagDest21_of_outside (inW i) (hmut i))
    (fun q hq ↦ not_mutMagDest21_ge275 q (by omega))
  have hAll : ∀ γ : BitAssignment 437, cleanRem 437 (437 - base) γ →
      let x := bitsVal (fun i ↦ γ (inW i))
      let st :=
        Slot3MicroEngineAux.evalMicroList 4 mux2GeOps (Slot3MicroEngineAux.initBoolList 4 6 x)
      Slot3MicroEngineAux.allBelow 4 (fun i ↦
        Slot3MicroEngineAux.getBoolAt st i == x.testBit i) = true ∧
      Slot3MicroEngineAux.getBoolAt st 5 =
        mux2GeBool (x.testBit 0) (x.testBit 1) (x.testBit 2) (x.testBit 3) := fun γ _ ↦ by
    have hx_lt : bitsVal (fun i ↦ γ (inW i)) < 16 := bitsVal_lt_two_pow _
    have hchk := (Slot3MicroEngineAux.allBelow_iff 16 mux2GeCheck).mp mux2Ge_eval_ok _ hx_lt
    dsimp only [mux2GeCheck] at hchk
    simp only [Bool.and_eq_true, beq_iff_eq] at hchk
    exact hchk
  refine ⟨⟨by omega, hCnt, hd, hs, hLift, fun γ hcl ↦ (hEval γ hcl).1,
      fun γ hcl ↦ (hEval γ hcl).2.1 (hAll γ hcl).1⟩,
    fun γ b0 b1 b2 b3 hcl h0 h1 h2 h3 ↦ ?_⟩
  obtain ⟨_, _, hsOut⟩ := hEval γ hcl
  obtain ⟨_, ho5⟩ := hAll γ hcl
  have ht0 := tb_in inW γ 0 h0
  have ht1 := tb_in inW γ 1 h1
  have ht2 := tb_in inW γ 2 h2
  have ht3 := tb_in inW γ 3 h3
  dsimp only [Fin.val_zero, Fin.val_one, Fin.val_two] at ht0 ht1 ht2
  change (bitsVal (fun j ↦ γ (inW j))).testBit 3 = b3 at ht3
  have hw : (⟨base + 1, by omega⟩ : Wire 437) = ⟨base + (5 - 4), by omega⟩ := Fin.ext rfl
  rw [hw, hsOut 5 (by decide) (by decide), ho5, ht0, ht1, ht2, ht3]
private theorem ctxTail56_spec (inW : Fin 5 → Wire 437) (hinj : Function.Injective inW)
    (base : ℕ) (hbase : base + 3 ≤ 437) (h275 : 275 ≤ base)
    (hin : ∀ i, (inW i).val < base)
    (hmut : ∀ i, decide ((inW i).val < 177 ∨ 198 ≤ (inW i).val) = true) :
    let ctx := Slot3MicroEngineAux.ctxMicro inW hinj base 3 3 hin tail56Ops tail56_meta hbase
    MagCtxPkg base (base + 3) 3 ctx ∧
      (∀ (γ : BitAssignment 437) (b0 b1 b2 b3 b4 : Bool),
        cleanRem 437 (437 - base) γ →
        γ (inW 0) = Slot3MicroEngineAux.boolToZMod2 b0 →
        γ (inW 1) = Slot3MicroEngineAux.boolToZMod2 b1 →
        γ (inW 2) = Slot3MicroEngineAux.boolToZMod2 b2 →
        γ (inW 3) = Slot3MicroEngineAux.boolToZMod2 b3 →
        γ (inW 4) = Slot3MicroEngineAux.boolToZMod2 b4 →
        ctx.fwdBits γ ⟨base + 1, by omega⟩ =
          Slot3MicroEngineAux.boolToZMod2 (tail56Bool5 b0 b1 b2 b3) ∧
        ctx.fwdBits γ ⟨base + 2, by omega⟩ =
          Slot3MicroEngineAux.boolToZMod2 (b1 && b4)) := by
  obtain ⟨hCnt, hProps, hLift, hEval⟩ :=
    Slot3MicroEngineAux.ctxMicro_scoped inW hinj base 3 3 hin tail56Ops tail56_meta hbase
  obtain ⟨hd, hs⟩ := hProps (mutW := mutMagDest21)
    (fun i ↦ not_mutMagDest21_of_outside (inW i) (hmut i))
    (fun q hq ↦ not_mutMagDest21_ge275 q (by omega))
  have hAll : ∀ γ : BitAssignment 437, cleanRem 437 (437 - base) γ →
      let x := bitsVal (fun i ↦ γ (inW i))
      let st :=
        Slot3MicroEngineAux.evalMicroList 5 tail56Ops (Slot3MicroEngineAux.initBoolList 5 8 x)
      Slot3MicroEngineAux.allBelow 5 (fun i ↦
        Slot3MicroEngineAux.getBoolAt st i == x.testBit i) = true ∧
      Slot3MicroEngineAux.getBoolAt st 6 =
        tail56Bool5 (x.testBit 0) (x.testBit 1) (x.testBit 2) (x.testBit 3) ∧
      Slot3MicroEngineAux.getBoolAt st 7 = (x.testBit 1 && x.testBit 4) := fun γ _ ↦ by
    have hx_lt : bitsVal (fun i ↦ γ (inW i)) < 32 := bitsVal_lt_two_pow _
    have hchk := (Slot3MicroEngineAux.allBelow_iff 32 tail56Check).mp tail56_eval_ok _ hx_lt
    dsimp only [tail56Check] at hchk
    simp only [Bool.and_eq_true, beq_iff_eq] at hchk
    exact ⟨hchk.1.1, hchk.1.2, hchk.2⟩
  refine ⟨⟨by omega, hCnt, hd, hs, hLift, fun γ hcl ↦ (hEval γ hcl).1,
      fun γ hcl ↦ (hEval γ hcl).2.1 (hAll γ hcl).1⟩,
    fun γ b0 b1 b2 b3 b4 hcl h0 h1 h2 h3 h4 ↦ ?_⟩
  obtain ⟨_, _, hsOut⟩ := hEval γ hcl
  obtain ⟨_, ho6, ho7⟩ := hAll γ hcl
  have ht0 := tb_in inW γ 0 h0
  have ht1 := tb_in inW γ 1 h1
  have ht2 := tb_in inW γ 2 h2
  have ht3 := tb_in inW γ 3 h3
  have ht4 := tb_in inW γ 4 h4
  dsimp only [Fin.val_zero, Fin.val_one, Fin.val_two] at ht0 ht1 ht2
  change (bitsVal (fun j ↦ γ (inW j))).testBit 3 = b3 at ht3
  change (bitsVal (fun j ↦ γ (inW j))).testBit 4 = b4 at ht4
  refine ⟨?_, ?_⟩
  · have hw : (⟨base + 1, by omega⟩ : Wire 437) = ⟨base + (6 - 5), by omega⟩ := Fin.ext rfl
    rw [hw, hsOut 6 (by decide) (by decide), ho6, ht0, ht1, ht2, ht3]
  · have hw : (⟨base + 2, by omega⟩ : Wire 437) = ⟨base + (7 - 5), by omega⟩ := Fin.ext rfl
    rw [hw, hsOut 7 (by decide) (by decide), ho7, ht1, ht4]
private theorem ctxDot2Xor_spec (inW : Fin 5 → Wire 437) (hinj : Function.Injective inW)
    (base : ℕ) (hbase : base + 2 ≤ 437) (h275 : 275 ≤ base)
    (hin : ∀ i, (inW i).val < base)
    (hmut : ∀ i, decide ((inW i).val < 177 ∨ 198 ≤ (inW i).val) = true) :
    let ctx := Slot3MicroEngineAux.ctxMicro inW hinj base 2 2 hin dot2XorOps dot2Xor_meta hbase
    MagCtxPkg base (base + 2) 2 ctx ∧
      (∀ (γ : BitAssignment 437) (b0 b1 b2 b3 b4 : Bool),
        cleanRem 437 (437 - base) γ →
        γ (inW 0) = Slot3MicroEngineAux.boolToZMod2 b0 →
        γ (inW 1) = Slot3MicroEngineAux.boolToZMod2 b1 →
        γ (inW 2) = Slot3MicroEngineAux.boolToZMod2 b2 →
        γ (inW 3) = Slot3MicroEngineAux.boolToZMod2 b3 →
        γ (inW 4) = Slot3MicroEngineAux.boolToZMod2 b4 →
        ctx.fwdBits γ ⟨base + 1, by omega⟩ =
          Slot3MicroEngineAux.boolToZMod2 (dot2XorBool b0 b1 b2 b3 b4)) := by
  obtain ⟨hCnt, hProps, hLift, hEval⟩ :=
    Slot3MicroEngineAux.ctxMicro_scoped inW hinj base 2 2 hin dot2XorOps dot2Xor_meta hbase
  obtain ⟨hd, hs⟩ := hProps (mutW := mutMagDest21)
    (fun i ↦ not_mutMagDest21_of_outside (inW i) (hmut i))
    (fun q hq ↦ not_mutMagDest21_ge275 q (by omega))
  have hAll : ∀ γ : BitAssignment 437, cleanRem 437 (437 - base) γ →
      let x := bitsVal (fun i ↦ γ (inW i))
      let st :=
        Slot3MicroEngineAux.evalMicroList 5 dot2XorOps (Slot3MicroEngineAux.initBoolList 5 7 x)
      Slot3MicroEngineAux.allBelow 5 (fun i ↦
        Slot3MicroEngineAux.getBoolAt st i == x.testBit i) = true ∧
      Slot3MicroEngineAux.getBoolAt st 6 =
        dot2XorBool (x.testBit 0) (x.testBit 1) (x.testBit 2) (x.testBit 3) (x.testBit 4) :=
          fun γ _ ↦ by
    have hx_lt : bitsVal (fun i ↦ γ (inW i)) < 32 := bitsVal_lt_two_pow _
    have hchk := (Slot3MicroEngineAux.allBelow_iff 32 dot2XorCheck).mp dot2Xor_eval_ok _ hx_lt
    dsimp only [dot2XorCheck] at hchk
    simp only [Bool.and_eq_true, beq_iff_eq] at hchk
    exact hchk
  refine ⟨⟨by omega, hCnt, hd, hs, hLift, fun γ hcl ↦ (hEval γ hcl).1,
      fun γ hcl ↦ (hEval γ hcl).2.1 (hAll γ hcl).1⟩,
    fun γ b0 b1 b2 b3 b4 hcl h0 h1 h2 h3 h4 ↦ ?_⟩
  obtain ⟨_, _, hsOut⟩ := hEval γ hcl
  obtain ⟨_, ho6⟩ := hAll γ hcl
  have ht0 := tb_in inW γ 0 h0
  have ht1 := tb_in inW γ 1 h1
  have ht2 := tb_in inW γ 2 h2
  have ht3 := tb_in inW γ 3 h3
  have ht4 := tb_in inW γ 4 h4
  dsimp only [Fin.val_zero, Fin.val_one, Fin.val_two] at ht0 ht1 ht2
  change (bitsVal (fun j ↦ γ (inW j))).testBit 3 = b3 at ht3
  change (bitsVal (fun j ↦ γ (inW j))).testBit 4 = b4 at ht4
  have hw : (⟨base + 1, by omega⟩ : Wire 437) = ⟨base + (6 - 5), by omega⟩ := Fin.ext rfl
  rw [hw, hsOut 6 (by decide) (by decide), ho6, ht0, ht1, ht2, ht3, ht4]
private theorem magRows14_bool_eq (μ : ℕ) (hμ : μ < 7) (u : ℕ → Bool) :
    let b0 := μ.testBit 0
    let b1 := μ.testBit 1
    let b2 := μ.testBit 2
    let sel := fun a : ℕ ↦ decide (μ = a)
    let ge := fun a : ℕ ↦ decide (a ≤ μ)
    let z1 := if b0 then u 2 else u 1
    let z3 := if b0 then u 4 else u 3
    let tz3 := if b0 then u 3 else u 4
    let z5 := if b0 then u 6 else u 5
    let z7 := if b0 then u 8 else u 7
    let tz5 := if b0 then u 5 else u 6
    let tz7 := if b0 then u 7 else u 8
    let z9 := if b0 then u 10 else u 9
    let o13 := if b0 then u 15 else u 13
    let tz9 := if b0 then u 9 else u 10
    let to13 := if b0 then u 13 else u 15
    let e2 := if b0 then u 4 else u 2
    let e6 := if b0 then u 8 else u 6
    let e10 := if b0 then u 12 else u 10
    let e14 := if b0 then u 16 else u 14
    let te10 := if b0 then u 10 else u 12
    let te14 := if b0 then u 14 else u 16
    let t123 := dot3Bool (sel 1) (sel 2) (sel 3) (u 5) (u 7) (u 9)
    mux4Bool b1 b2 z1 z3 z5 (u 7) = (ge 0 && u (1 * (μ + 1) + 0)) ∧
    mux3GeBool (ge 1) (ge 3) (ge 5) tz3 tz5 tz7 = (ge 1 && u (1 * (μ + 1) + 1)) ∧
    mux3GeBool (ge 2) (ge 4) (ge 6) z5 z7 (u 9) = (ge 2 && u (1 * (μ + 1) + 2)) ∧
    mux2GeBool (ge 3) (ge 5) tz7 tz9 = (ge 3 && u (1 * (μ + 1) + 3)) ∧
    mux2GeBool (ge 4) (ge 6) z9 (u 11) = (ge 4 && u (1 * (μ + 1) + 4)) ∧
    tail56Bool5 (sel 5) (ge 6) (u 11) (u 12) = (ge 5 && u (1 * (μ + 1) + 5)) ∧
    (ge 6 && u 13) = (ge 6 && u (1 * (μ + 1) + 6)) ∧
    mux4Bool b1 b2 e2 e6 e10 (u 14) = (ge 0 && u (2 * (μ + 1) + 0)) ∧
    dot2XorBool (sel 4) (ge 5) (u 11) to13 t123 = (ge 1 && u (2 * (μ + 1) + 1)) ∧
    mux3SelGeBool (sel 2) (ge 3) (ge 5) (u 8) te10 te14 = (ge 2 && u (2 * (μ + 1) + 2)) ∧
    mux3SelGeBool (sel 3) (ge 4) (ge 6) (u 11) o13 (u 17) = (ge 3 && u (2 * (μ + 1) + 3)) ∧
    mux2GeBool (ge 4) (ge 6) e14 (u 18) = (ge 4 && u (2 * (μ + 1) + 4)) ∧
    tail56Bool5 (sel 5) (ge 6) (u 17) (u 19) = (ge 5 && u (2 * (μ + 1) + 5)) ∧
    (ge 6 && u 20) = (ge 6 && u (2 * (μ + 1) + 6)) := by
  have hc : μ = 0 ∨ μ = 1 ∨ μ = 2 ∨ μ = 3 ∨ μ = 4 ∨ μ = 5 ∨ μ = 6 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    (dsimp only [mux4Bool, mux3GeBool, mux3SelGeBool, mux2GeBool, tail56Bool5, dot3Bool,
      dot2XorBool, Nat.testBit]; simp)
private theorem ctxMagB0_10_spec :
    MagCtxPkg 296 316 10 ctxMagB0_10 ∧
      ∀ (γ : BitAssignment 437) (b0 : Bool) (u : ℕ → Bool),
        cleanRem 437 (437 - 296) γ →
        γ (muW 0) = Slot3MicroEngineAux.boolToZMod2 b0 →
        (∀ i : Fin 22, γ (u22WAux i) = Slot3MicroEngineAux.boolToZMod2 (u i.val)) →
        let δ := ctxMagB0_10.fwdBits γ
        δ ⟨296, by decide⟩ = Slot3MicroEngineAux.boolToZMod2 (if b0 then u 2 else u 1) ∧
        δ ⟨297, by decide⟩ = Slot3MicroEngineAux.boolToZMod2 (if b0 then u 4 else u 3) ∧
        δ ⟨299, by decide⟩ = Slot3MicroEngineAux.boolToZMod2 (if b0 then u 3 else u 4) ∧
        δ ⟨300, by decide⟩ = Slot3MicroEngineAux.boolToZMod2 (if b0 then u 6 else u 5) ∧
        δ ⟨301, by decide⟩ = Slot3MicroEngineAux.boolToZMod2 (if b0 then u 8 else u 7) ∧
        δ ⟨302, by decide⟩ = Slot3MicroEngineAux.boolToZMod2 (if b0 then u 5 else u 6) ∧
        δ ⟨303, by decide⟩ = Slot3MicroEngineAux.boolToZMod2 (if b0 then u 7 else u 8) ∧
        δ ⟨304, by decide⟩ = Slot3MicroEngineAux.boolToZMod2 (if b0 then u 10 else u 9) ∧
        δ ⟨305, by decide⟩ = Slot3MicroEngineAux.boolToZMod2 (if b0 then u 15 else u 13) ∧
        δ ⟨306, by decide⟩ = Slot3MicroEngineAux.boolToZMod2 (if b0 then u 9 else u 10) ∧
        δ ⟨307, by decide⟩ = Slot3MicroEngineAux.boolToZMod2 (if b0 then u 13 else u 15) ∧
        δ ⟨308, by decide⟩ = Slot3MicroEngineAux.boolToZMod2 (if b0 then u 4 else u 2) ∧
        δ ⟨309, by decide⟩ = Slot3MicroEngineAux.boolToZMod2 (if b0 then u 8 else u 6) ∧
        δ ⟨312, by decide⟩ = Slot3MicroEngineAux.boolToZMod2 (if b0 then u 12 else u 10) ∧
        δ ⟨313, by decide⟩ = Slot3MicroEngineAux.boolToZMod2 (if b0 then u 16 else u 14) ∧
        δ ⟨314, by decide⟩ = Slot3MicroEngineAux.boolToZMod2 (if b0 then u 10 else u 12) ∧
        δ ⟨315, by decide⟩ = Slot3MicroEngineAux.boolToZMod2 (if b0 then u 14 else u 16) := by
  obtain ⟨hP1, hE1⟩ := ctxB0Mux2_spec kb1In5W kb1In5W_inj 296 (by decide) (by decide)
    (fun i ↦ by revert i; decide) (fun i ↦ by revert i; decide)
  obtain ⟨hP2, hE2⟩ := ctxB0Mux2_spec kb2In5W kb2In5W_inj 300 (by decide) (by decide)
    (fun i ↦ by revert i; decide) (fun i ↦ by revert i; decide)
  obtain ⟨hP3, hE3⟩ := ctxB0Mux2_spec kb3In5W kb3In5W_inj 304 (by decide) (by decide)
    (fun i ↦ by revert i; decide) (fun i ↦ by revert i; decide)
  obtain ⟨hP4, hE4⟩ := ctxB0Mux2_spec kb4In5W kb4In5W_inj 308 (by decide) (by decide)
    (fun i ↦ by revert i; decide) (fun i ↦ by revert i; decide)
  obtain ⟨hP5, hE5⟩ := ctxB0Mux2_spec kb5In5W kb5In5W_inj 312 (by decide) (by decide)
    (fun i ↦ by revert i; decide) (fun i ↦ by revert i; decide)
  change MagCtxPkg 296 _ _ ctxKb1 at hP1
  change MagCtxPkg 300 _ _ ctxKb2 at hP2
  change MagCtxPkg 304 _ _ ctxKb3 at hP3
  change MagCtxPkg 308 _ _ ctxKb4 at hP4
  change MagCtxPkg 312 _ _ ctxKb5 at hP5
  have hP45 := hP4.append hP5
  have hP35 := hP3.append hP45
  have hP25 := hP2.append hP35
  have hP15 := hP1.append hP25
  refine ⟨hP15, fun γ b0 u hcl0 hb0 hu ↦ ?_⟩
  let γ₁ := ctxKb1.fwdBits γ
  have hcl1 := hP1.clean γ hcl0
  have hp1 : ∀ q : Wire 437, q.val < 296 → γ₁ q = γ q := hP1.pres γ hcl0
  let γ₂ := ctxKb2.fwdBits γ₁
  have hcl2 := hP2.clean γ₁ hcl1
  have hp2 : ∀ q : Wire 437, q.val < 296 → γ₂ q = γ q :=
    fun q hq ↦ (hP2.pres γ₁ hcl1 q (by omega)).trans (hp1 q hq)
  let γ₃ := ctxKb3.fwdBits γ₂
  have hcl3 := hP3.clean γ₂ hcl2
  have hp3 : ∀ q : Wire 437, q.val < 296 → γ₃ q = γ q :=
    fun q hq ↦ (hP3.pres γ₂ hcl2 q (by omega)).trans (hp2 q hq)
  let γ₄ := ctxKb4.fwdBits γ₃
  have hcl4 := hP4.clean γ₃ hcl3
  have hp4 : ∀ q : Wire 437, q.val < 296 → γ₄ q = γ q :=
    fun q hq ↦ (hP4.pres γ₃ hcl3 q (by omega)).trans (hp3 q hq)
  have h1 := hE1 γ b0 (u 1) (u 2) (u 3) (u 4) hcl0 hb0 (hu 1) (hu 2) (hu 3) (hu 4)
  have h2 := hE2 γ₁ b0 (u 5) (u 6) (u 7) (u 8) hcl1 ((hp1 _ (by decide)).trans hb0)
      ((hp1 _ (by decide)).trans (hu 5)) ((hp1 _ (by decide)).trans (hu 6))
      ((hp1 _ (by decide)).trans (hu 7)) ((hp1 _ (by decide)).trans (hu 8))
  have h3 := hE3 γ₂ b0 (u 9) (u 10) (u 13) (u 15) hcl2 ((hp2 _ (by decide)).trans hb0)
      ((hp2 _ (by decide)).trans (hu 9)) ((hp2 _ (by decide)).trans (hu 10))
      ((hp2 _ (by decide)).trans (hu 13)) ((hp2 _ (by decide)).trans (hu 15))
  have h4 := hE4 γ₃ b0 (u 2) (u 4) (u 6) (u 8) hcl3 ((hp3 _ (by decide)).trans hb0)
      ((hp3 _ (by decide)).trans (hu 2)) ((hp3 _ (by decide)).trans (hu 4))
      ((hp3 _ (by decide)).trans (hu 6)) ((hp3 _ (by decide)).trans (hu 8))
  have h5 := hE5 γ₄ b0 (u 10) (u 12) (u 14) (u 16) hcl4 ((hp4 _ (by decide)).trans hb0)
      ((hp4 _ (by decide)).trans (hu 10)) ((hp4 _ (by decide)).trans (hu 12))
      ((hp4 _ (by decide)).trans (hu 14)) ((hp4 _ (by decide)).trans (hu 16))
  have heq1 : ctxMagB0_10.fwdBits γ =
    (ctxKb2.append (ctxKb3.append (ctxKb4.append ctxKb5))).fwdBits γ₁ :=
    Slot3MicroEngineAux.TempCtx.append_fwdBits ctxKb1 _ γ
  have heq2 : ctxMagB0_10.fwdBits γ = (ctxKb3.append (ctxKb4.append ctxKb5)).fwdBits γ₂ :=
    heq1.trans (Slot3MicroEngineAux.TempCtx.append_fwdBits ctxKb2 _ γ₁)
  have heq3 : ctxMagB0_10.fwdBits γ = (ctxKb4.append ctxKb5).fwdBits γ₃ :=
    heq2.trans (Slot3MicroEngineAux.TempCtx.append_fwdBits ctxKb3 _ γ₂)
  have heq4 : ctxMagB0_10.fwdBits γ = ctxKb5.fwdBits γ₄ :=
    heq3.trans (Slot3MicroEngineAux.TempCtx.append_fwdBits ctxKb4 _ γ₃)
  have hf1 : ∀ q : Wire 437, q.val < 300 → ctxMagB0_10.fwdBits γ q = γ₁ q :=
    fun q hq ↦ (congrFun heq1 q).trans (hP25.pres γ₁ hcl1 q hq)
  have hf2 : ∀ q : Wire 437, q.val < 304 → ctxMagB0_10.fwdBits γ q = γ₂ q :=
    fun q hq ↦ (congrFun heq2 q).trans (hP35.pres γ₂ hcl2 q hq)
  have hf3 : ∀ q : Wire 437, q.val < 308 → ctxMagB0_10.fwdBits γ q = γ₃ q :=
    fun q hq ↦ (congrFun heq3 q).trans (hP45.pres γ₃ hcl3 q hq)
  have hf4 : ∀ q : Wire 437, q.val < 312 → ctxMagB0_10.fwdBits γ q = γ₄ q :=
    fun q hq ↦ (congrFun heq4 q).trans (hP5.pres γ₄ hcl4 q hq)
  have hf5 : ∀ q : Wire 437, ctxMagB0_10.fwdBits γ q = ctxKb5.fwdBits γ₄ q :=
    fun q ↦ congrFun heq4 q
  exact ⟨(hf1 _ (by decide)).trans h1.1, (hf1 _ (by decide)).trans h1.2.1, (hf1 _
    (by decide)).trans h1.2.2.2, (hf2 _ (by decide)).trans h2.1, (hf2 _ (by decide)).trans
    h2.2.1, (hf2 _ (by decide)).trans h2.2.2.1, (hf2 _ (by decide)).trans h2.2.2.2, (hf3 _
    (by decide)).trans h3.1, (hf3 _ (by decide)).trans h3.2.1, (hf3 _ (by decide)).trans
    h3.2.2.1, (hf3 _ (by decide)).trans h3.2.2.2, (hf4 _ (by decide)).trans h4.1, (hf4 _
    (by decide)).trans h4.2.1, (hf5 _).trans h5.1, (hf5 _).trans h5.2.1, (hf5 _).trans
    h5.2.2.1, (hf5 _).trans h5.2.2.2⟩
private theorem ctxMagRows35_spec :
    MagCtxPkg 316 351 35 ctxMagRows35 ∧
      ∀ (δ : BitAssignment 437) (μ : ℕ) (hμ : μ < 7) (u : ℕ → Bool),
        let b0 := μ.testBit 0
        cleanRem 437 (437 - 316) δ →
        (∀ j : Fin 3, δ (muW j) = Slot3MicroEngineAux.boolToZMod2 (μ.testBit j.val)) →
        (∀ i : Fin 22, δ (u22WAux i) = Slot3MicroEngineAux.boolToZMod2 (u i.val)) →
        (∀ a : Fin 7, δ (magSel7W a) = Slot3MicroEngineAux.boolToZMod2 (decide (μ = a.val))) →
        (∀ a : Fin 7, δ (magGeW a) = Slot3MicroEngineAux.boolToZMod2 (decide (a.val ≤ μ))) →
        δ ⟨296, by decide⟩ = Slot3MicroEngineAux.boolToZMod2 (if b0 then u 2 else u 1) →
        δ ⟨297, by decide⟩ = Slot3MicroEngineAux.boolToZMod2 (if b0 then u 4 else u 3) →
        δ ⟨299, by decide⟩ = Slot3MicroEngineAux.boolToZMod2 (if b0 then u 3 else u 4) →
        δ ⟨300, by decide⟩ = Slot3MicroEngineAux.boolToZMod2 (if b0 then u 6 else u 5) →
        δ ⟨301, by decide⟩ = Slot3MicroEngineAux.boolToZMod2 (if b0 then u 8 else u 7) →
        δ ⟨302, by decide⟩ = Slot3MicroEngineAux.boolToZMod2 (if b0 then u 5 else u 6) →
        δ ⟨303, by decide⟩ = Slot3MicroEngineAux.boolToZMod2 (if b0 then u 7 else u 8) →
        δ ⟨304, by decide⟩ = Slot3MicroEngineAux.boolToZMod2 (if b0 then u 10 else u 9) →
        δ ⟨305, by decide⟩ = Slot3MicroEngineAux.boolToZMod2 (if b0 then u 15 else u 13) →
        δ ⟨306, by decide⟩ = Slot3MicroEngineAux.boolToZMod2 (if b0 then u 9 else u 10) →
        δ ⟨307, by decide⟩ = Slot3MicroEngineAux.boolToZMod2 (if b0 then u 13 else u 15) →
        δ ⟨308, by decide⟩ = Slot3MicroEngineAux.boolToZMod2 (if b0 then u 4 else u 2) →
        δ ⟨309, by decide⟩ = Slot3MicroEngineAux.boolToZMod2 (if b0 then u 8 else u 6) →
        δ ⟨312, by decide⟩ = Slot3MicroEngineAux.boolToZMod2 (if b0 then u 12 else u 10) →
        δ ⟨313, by decide⟩ = Slot3MicroEngineAux.boolToZMod2 (if b0 then u 16 else u 14) →
        δ ⟨314, by decide⟩ = Slot3MicroEngineAux.boolToZMod2 (if b0 then u 10 else u 12) →
        δ ⟨315, by decide⟩ = Slot3MicroEngineAux.boolToZMod2 (if b0 then u 14 else u 16) →
        let η := ctxMagRows35.fwdBits δ
        (∀ b : Fin 7,
          η (magSrc21Fast ⟨7 + b.val, by omega⟩) =
            Slot3MicroEngineAux.boolToZMod2 (decide (b.val ≤ μ) && u (1 * (μ + 1) + b.val))) ∧
        (∀ b : Fin 7,
          η (magSrc21Fast ⟨14 + b.val, by omega⟩) =
            Slot3MicroEngineAux.boolToZMod2 (decide (b.val ≤ μ) && u (2 * (μ + 1) + b.val))) := by
  obtain ⟨hP1, hE1⟩ := ctxMicro6_out8_spec mux4Ops mux4_meta mux4Bool mux4Check (fun _ ↦
    rfl) mux4_eval_ok
    kw1_0In6W kw1_0In6W_inj 316 (by
      decide) (by decide) (fun i ↦ by revert i; decide) (fun i ↦ by revert i; decide)
  obtain ⟨hP2, hE2⟩ := ctxMicro6_out8_spec mux4Ops mux4_meta mux4Bool mux4Check (fun _ ↦
    rfl) mux4_eval_ok
    kw2_0In6W kw2_0In6W_inj 319 (by
      decide) (by decide) (fun i ↦ by revert i; decide) (fun i ↦ by revert i; decide)
  obtain ⟨hP3, hE3⟩ := ctxMicro6_out8_spec mux3GeOps mux3Ge_meta mux3GeBool mux3GeCheck (fun _ ↦
    rfl) mux3Ge_eval_ok
    kw1_1In6W kw1_1In6W_inj 322 (by
      decide) (by decide) (fun i ↦ by revert i; decide) (fun i ↦ by revert i; decide)
  obtain ⟨hP4, hE4⟩ := ctxMicro6_out8_spec mux3GeOps mux3Ge_meta mux3GeBool mux3GeCheck (fun _ ↦
    rfl) mux3Ge_eval_ok
    kw1_2In6W kw1_2In6W_inj 325 (by
      decide) (by decide) (fun i ↦ by revert i; decide) (fun i ↦ by revert i; decide)
  obtain ⟨hP5, hE5⟩ := ctxMux2Ge_spec kw1_3In4W kw1_3In4W_inj 328 (by decide) (by decide)
    (fun i ↦ by revert i; decide) (fun i ↦ by revert i; decide)
  obtain ⟨hP6, hE6⟩ := ctxMux2Ge_spec kw1_4In4W kw1_4In4W_inj 330 (by decide) (by decide)
    (fun i ↦ by revert i; decide) (fun i ↦ by revert i; decide)
  obtain ⟨hP7, hE7⟩ := ctxTail56_spec kw1_56In5W kw1_56In5W_inj 332 (by decide) (by decide)
    (fun i ↦ by revert i; decide) (fun i ↦ by revert i; decide)
  obtain ⟨hP8, hE8⟩ := ctxMicro6_out8_spec dot3Ops dot3_meta dot3Bool dot3Check (fun _ ↦
    rfl) dot3_eval_ok
    kw2_1aIn6W kw2_1aIn6W_inj 335 (by
      decide) (by decide) (fun i ↦ by revert i; decide) (fun i ↦ by revert i; decide)
  obtain ⟨hP9, hE9⟩ := ctxDot2Xor_spec kw2_1bIn5W kw2_1bIn5W_inj 338 (by decide) (by decide)
    (fun i ↦ by revert i; decide) (fun i ↦ by revert i; decide)
  obtain ⟨hP10, hE10⟩ :=
    ctxMicro6_out8_spec mux3SelGeOps mux3SelGe_meta mux3SelGeBool mux3SelGeCheck (fun _ ↦
    rfl) mux3SelGe_eval_ok
    kw2_2In6W kw2_2In6W_inj 340 (by
      decide) (by decide) (fun i ↦ by revert i; decide) (fun i ↦ by revert i; decide)
  obtain ⟨hP11, hE11⟩ :=
    ctxMicro6_out8_spec mux3SelGeOps mux3SelGe_meta mux3SelGeBool mux3SelGeCheck (fun _ ↦
    rfl) mux3SelGe_eval_ok
    kw2_3In6W kw2_3In6W_inj 343 (by
      decide) (by decide) (fun i ↦ by revert i; decide) (fun i ↦ by revert i; decide)
  obtain ⟨hP12, hE12⟩ := ctxMux2Ge_spec kw2_4In4W kw2_4In4W_inj 346 (by decide) (by decide)
    (fun i ↦ by revert i; decide) (fun i ↦ by revert i; decide)
  obtain ⟨hP13, hE13⟩ := ctxTail56_spec kw2_56In5W kw2_56In5W_inj 348 (by decide) (by decide)
    (fun i ↦ by revert i; decide) (fun i ↦ by revert i; decide)
  change MagCtxPkg 316 _ _ ctxKw1_0 at hP1
  change MagCtxPkg 319 _ _ ctxKw2_0 at hP2
  change MagCtxPkg 322 _ _ ctxKw1_1 at hP3
  change MagCtxPkg 325 _ _ ctxKw1_2 at hP4
  change MagCtxPkg 328 _ _ ctxKw1_3 at hP5
  change MagCtxPkg 330 _ _ ctxKw1_4 at hP6
  change MagCtxPkg 332 _ _ ctxKw1_56 at hP7
  change MagCtxPkg 335 _ _ ctxKw2_1a at hP8
  change MagCtxPkg 338 _ _ ctxKw2_1b at hP9
  change MagCtxPkg 340 _ _ ctxKw2_2 at hP10
  change MagCtxPkg 343 _ _ ctxKw2_3 at hP11
  change MagCtxPkg 346 _ _ ctxKw2_4 at hP12
  change MagCtxPkg 348 _ _ ctxKw2_56 at hP13
  have hR12 := hP12.append hP13
  have hR11 := hP11.append hR12
  have hR10 := hP10.append hR11
  have hR9 := hP9.append hR10
  have hR8 := hP8.append hR9
  have hR7 := hP7.append hR8
  have hR6 := hP6.append hR7
  have hR5 := hP5.append hR6
  have hR4 := hP4.append hR5
  have hR3 := hP3.append hR4
  have hR2 := hP2.append hR3
  have hR1 := hP1.append hR2
  refine ⟨hR1, fun δ μ hμ u hcl0 hmu hu hsel hge
      hz1 hz3 htz3 hz5 hz7 htz5 htz7 hz9 ho13 htz9 hto13 he2 he6 he10 he14 hte10 hte14 ↦ ?_⟩
  let γ₁ := ctxKw1_0.fwdBits δ
  have hcl1 := hP1.clean δ hcl0
  have hp1 : ∀ q : Wire 437, q.val < 316 → γ₁ q = δ q := hP1.pres δ hcl0
  let γ₂ := ctxKw2_0.fwdBits γ₁
  have hcl2 := hP2.clean γ₁ hcl1
  have hp2 : ∀ q : Wire 437, q.val < 316 → γ₂ q = δ q := fun q hq ↦ (hP2.pres γ₁ hcl1 q (by
    omega)).trans (hp1 q hq)
  let γ₃ := ctxKw1_1.fwdBits γ₂
  have hcl3 := hP3.clean γ₂ hcl2
  have hp3 : ∀ q : Wire 437, q.val < 316 → γ₃ q = δ q := fun q hq ↦ (hP3.pres γ₂ hcl2 q (by
    omega)).trans (hp2 q hq)
  let γ₄ := ctxKw1_2.fwdBits γ₃
  have hcl4 := hP4.clean γ₃ hcl3
  have hp4 : ∀ q : Wire 437, q.val < 316 → γ₄ q = δ q := fun q hq ↦ (hP4.pres γ₃ hcl3 q (by
    omega)).trans (hp3 q hq)
  let γ₅ := ctxKw1_3.fwdBits γ₄
  have hcl5 := hP5.clean γ₄ hcl4
  have hp5 : ∀ q : Wire 437, q.val < 316 → γ₅ q = δ q := fun q hq ↦ (hP5.pres γ₄ hcl4 q (by
    omega)).trans (hp4 q hq)
  let γ₆ := ctxKw1_4.fwdBits γ₅
  have hcl6 := hP6.clean γ₅ hcl5
  have hp6 : ∀ q : Wire 437, q.val < 316 → γ₆ q = δ q := fun q hq ↦ (hP6.pres γ₅ hcl5 q (by
    omega)).trans (hp5 q hq)
  let γ₇ := ctxKw1_56.fwdBits γ₆
  have hcl7 := hP7.clean γ₆ hcl6
  have hp7 : ∀ q : Wire 437, q.val < 316 → γ₇ q = δ q := fun q hq ↦ (hP7.pres γ₆ hcl6 q (by
    omega)).trans (hp6 q hq)
  let γ₈ := ctxKw2_1a.fwdBits γ₇
  have hcl8 := hP8.clean γ₇ hcl7
  have hp8 : ∀ q : Wire 437, q.val < 316 → γ₈ q = δ q := fun q hq ↦ (hP8.pres γ₇ hcl7 q (by
    omega)).trans (hp7 q hq)
  let γ₉ := ctxKw2_1b.fwdBits γ₈
  have hcl9 := hP9.clean γ₈ hcl8
  have hp9 : ∀ q : Wire 437, q.val < 316 → γ₉ q = δ q := fun q hq ↦ (hP9.pres γ₈ hcl8 q (by
    omega)).trans (hp8 q hq)
  let γ₁₀ := ctxKw2_2.fwdBits γ₉
  have hcl10 := hP10.clean γ₉ hcl9
  have hp10 : ∀ q : Wire 437, q.val < 316 → γ₁₀ q = δ q := fun q hq ↦ (hP10.pres γ₉ hcl9 q (by
    omega)).trans (hp9 q hq)
  let γ₁₁ := ctxKw2_3.fwdBits γ₁₀
  have hcl11 := hP11.clean γ₁₀ hcl10
  have hp11 : ∀ q : Wire 437, q.val < 316 → γ₁₁ q = δ q := fun q hq ↦ (hP11.pres γ₁₀ hcl10 q (by
    omega)).trans (hp10 q hq)
  let γ₁₂ := ctxKw2_4.fwdBits γ₁₁
  have hcl12 := hP12.clean γ₁₁ hcl11
  have hp12 : ∀ q : Wire 437, q.val < 316 → γ₁₂ q = δ q := fun q hq ↦ (hP12.pres γ₁₁ hcl11 q (by
    omega)).trans (hp11 q hq)
  have hb := magRows14_bool_eq μ hμ u
  have ho1 := hE1 δ (μ.testBit 1) (μ.testBit 2) _ _ _ _ hcl0 (hmu 1) (hmu 2) hz1 hz3 hz5 (hu 7)
  have ho2 := hE2 γ₁ (μ.testBit 1) (μ.testBit 2) _ _ _ _ hcl1
    ((hp1 _ (by decide)).trans (hmu 1)) ((hp1 _ (by decide)).trans (hmu 2))
    ((hp1 _ (by decide)).trans he2) ((hp1 _ (by decide)).trans he6)
    ((hp1 _ (by decide)).trans he10) ((hp1 _ (by decide)).trans (hu 14))
  have ho3 := hE3 γ₂ _ _ _ _ _ _ hcl2
    ((hp2 _ (by
      decide)).trans (hge 1)) ((hp2 _ (by
      decide)).trans (hge 3)) ((hp2 _ (by decide)).trans (hge 5))
    ((hp2 _ (by
      decide)).trans htz3) ((hp2 _ (by decide)).trans htz5) ((hp2 _ (by decide)).trans htz7)
  have ho4 := hE4 γ₃ _ _ _ _ _ _ hcl3
    ((hp3 _ (by
      decide)).trans (hge 2)) ((hp3 _ (by
      decide)).trans (hge 4)) ((hp3 _ (by decide)).trans (hge 6))
    ((hp3 _ (by
      decide)).trans hz5) ((hp3 _ (by decide)).trans hz7) ((hp3 _ (by decide)).trans (hu 9))
  have ho5 := hE5 γ₄ _ _ _ _ hcl4
    ((hp4 _ (by decide)).trans (hge 3)) ((hp4 _ (by decide)).trans (hge 5))
    ((hp4 _ (by decide)).trans htz7) ((hp4 _ (by decide)).trans htz9)
  have ho6 := hE6 γ₅ _ _ _ _ hcl5
    ((hp5 _ (by decide)).trans (hge 4)) ((hp5 _ (by decide)).trans (hge 6))
    ((hp5 _ (by decide)).trans hz9) ((hp5 _ (by decide)).trans (hu 11))
  have ho7 := hE7 γ₆ _ _ _ _ _ hcl6
    ((hp6 _ (by decide)).trans (hsel 5)) ((hp6 _ (by decide)).trans (hge 6))
    ((hp6 _ (by
      decide)).trans (hu 11)) ((hp6 _ (by
      decide)).trans (hu 12)) ((hp6 _ (by decide)).trans (hu 13))
  have ho8 := hE8 γ₇ _ _ _ _ _ _ hcl7
    ((hp7 _ (by
      decide)).trans (hsel 1)) ((hp7 _ (by
      decide)).trans (hsel 2)) ((hp7 _ (by decide)).trans (hsel 3))
    ((hp7 _ (by
      decide)).trans (hu 5)) ((hp7 _ (by decide)).trans (hu 7)) ((hp7 _ (by decide)).trans (hu 9))
  have ho9 := hE9 γ₈ _ _ _ _ _ hcl8
    ((hp8 _ (by decide)).trans (hsel 4)) ((hp8 _ (by decide)).trans (hge 5))
    ((hp8 _ (by decide)).trans (hu 11)) ((hp8 _ (by decide)).trans hto13) ho8
  have ho10 := hE10 γ₉ _ _ _ _ _ _ hcl9
    ((hp9 _ (by
      decide)).trans (hsel 2)) ((hp9 _ (by
      decide)).trans (hge 3)) ((hp9 _ (by decide)).trans (hge 5))
    ((hp9 _ (by
      decide)).trans (hu 8)) ((hp9 _ (by decide)).trans hte10) ((hp9 _ (by decide)).trans hte14)
  have ho11 := hE11 γ₁₀ _ _ _ _ _ _ hcl10
    ((hp10 _ (by
      decide)).trans (hsel 3)) ((hp10 _ (by
      decide)).trans (hge 4)) ((hp10 _ (by decide)).trans (hge 6))
    ((hp10 _ (by
      decide)).trans (hu 11)) ((hp10 _ (by decide)).trans ho13) ((hp10 _ (by decide)).trans (hu 17))
  have ho12 := hE12 γ₁₁ _ _ _ _ hcl11
    ((hp11 _ (by decide)).trans (hge 4)) ((hp11 _ (by decide)).trans (hge 6))
    ((hp11 _ (by decide)).trans he14) ((hp11 _ (by decide)).trans (hu 18))
  have ho13 := hE13 γ₁₂ _ _ _ _ _ hcl12
    ((hp12 _ (by decide)).trans (hsel 5)) ((hp12 _ (by decide)).trans (hge 6))
    ((hp12 _ (by
      decide)).trans (hu 17)) ((hp12 _ (by
      decide)).trans (hu 19)) ((hp12 _ (by decide)).trans (hu 20))
  have heq1 : ctxMagRows35.fwdBits δ =
      (ctxKw2_0.append (ctxKw1_1.append (ctxKw1_2.append (ctxKw1_3.append (ctxKw1_4.append
        (ctxKw1_56.append (ctxKw2_1a.append (ctxKw2_1b.append (ctxKw2_2.append (ctxKw2_3.append
          (ctxKw2_4.append ctxKw2_56))))))))))).fwdBits γ₁ :=
    Slot3MicroEngineAux.TempCtx.append_fwdBits ctxKw1_0 _ δ
  have heq2 : ctxMagRows35.fwdBits δ =
      (ctxKw1_1.append (ctxKw1_2.append (ctxKw1_3.append (ctxKw1_4.append
        (ctxKw1_56.append (ctxKw2_1a.append (ctxKw2_1b.append (ctxKw2_2.append (ctxKw2_3.append
          (ctxKw2_4.append ctxKw2_56)))))))))).fwdBits γ₂ :=
    heq1.trans (Slot3MicroEngineAux.TempCtx.append_fwdBits ctxKw2_0 _ γ₁)
  have heq3 : ctxMagRows35.fwdBits δ =
      (ctxKw1_2.append (ctxKw1_3.append (ctxKw1_4.append
        (ctxKw1_56.append (ctxKw2_1a.append (ctxKw2_1b.append (ctxKw2_2.append (ctxKw2_3.append
          (ctxKw2_4.append ctxKw2_56))))))))).fwdBits γ₃ :=
    heq2.trans (Slot3MicroEngineAux.TempCtx.append_fwdBits ctxKw1_1 _ γ₂)
  have heq4 : ctxMagRows35.fwdBits δ =
      (ctxKw1_3.append (ctxKw1_4.append
        (ctxKw1_56.append (ctxKw2_1a.append (ctxKw2_1b.append (ctxKw2_2.append (ctxKw2_3.append
          (ctxKw2_4.append ctxKw2_56)))))))).fwdBits γ₄ :=
    heq3.trans (Slot3MicroEngineAux.TempCtx.append_fwdBits ctxKw1_2 _ γ₃)
  have heq5 : ctxMagRows35.fwdBits δ =
      (ctxKw1_4.append (ctxKw1_56.append (ctxKw2_1a.append (ctxKw2_1b.append (ctxKw2_2.append
        (ctxKw2_3.append (ctxKw2_4.append ctxKw2_56))))))).fwdBits γ₅ :=
    heq4.trans (Slot3MicroEngineAux.TempCtx.append_fwdBits ctxKw1_3 _ γ₄)
  have heq6 : ctxMagRows35.fwdBits δ =
      (ctxKw1_56.append (ctxKw2_1a.append (ctxKw2_1b.append (ctxKw2_2.append (ctxKw2_3.append
        (ctxKw2_4.append ctxKw2_56)))))).fwdBits γ₆ :=
    heq5.trans (Slot3MicroEngineAux.TempCtx.append_fwdBits ctxKw1_4 _ γ₅)
  have heq7 : ctxMagRows35.fwdBits δ =
      (ctxKw2_1a.append (ctxKw2_1b.append (ctxKw2_2.append (ctxKw2_3.append (ctxKw2_4.append
        ctxKw2_56))))).fwdBits γ₇ :=
    heq6.trans (Slot3MicroEngineAux.TempCtx.append_fwdBits ctxKw1_56 _ γ₆)
  have heq8 : ctxMagRows35.fwdBits δ =
      (ctxKw2_1b.append (ctxKw2_2.append (ctxKw2_3.append (ctxKw2_4.append ctxKw2_56)))).fwdBits γ₈
        :=
    heq7.trans (Slot3MicroEngineAux.TempCtx.append_fwdBits ctxKw2_1a _ γ₇)
  have heq9 : ctxMagRows35.fwdBits δ =
      (ctxKw2_2.append (ctxKw2_3.append (ctxKw2_4.append ctxKw2_56))).fwdBits γ₉ :=
    heq8.trans (Slot3MicroEngineAux.TempCtx.append_fwdBits ctxKw2_1b _ γ₈)
  have heq10 : ctxMagRows35.fwdBits δ = (ctxKw2_3.append (ctxKw2_4.append ctxKw2_56)).fwdBits
      γ₁₀ := heq9.trans (Slot3MicroEngineAux.TempCtx.append_fwdBits ctxKw2_2 _ γ₉)
  have heq11 : ctxMagRows35.fwdBits δ = (ctxKw2_4.append ctxKw2_56).fwdBits γ₁₁ := heq10.trans
      (Slot3MicroEngineAux.TempCtx.append_fwdBits ctxKw2_3 _ γ₁₀)
  have heq12 : ctxMagRows35.fwdBits δ = ctxKw2_56.fwdBits γ₁₂ :=
    heq11.trans (Slot3MicroEngineAux.TempCtx.append_fwdBits ctxKw2_4 _ γ₁₁)
  have hf1 : ctxMagRows35.fwdBits δ ⟨318, by decide⟩ = γ₁ ⟨318, by decide⟩ :=
    (congrFun heq1 _).trans (hR2.pres γ₁ hcl1 _ (by decide))
  have hf2 : ctxMagRows35.fwdBits δ ⟨321, by decide⟩ = γ₂ ⟨321, by decide⟩ :=
    (congrFun heq2 _).trans (hR3.pres γ₂ hcl2 _ (by decide))
  have hf3 : ctxMagRows35.fwdBits δ ⟨324, by decide⟩ = γ₃ ⟨324, by decide⟩ :=
    (congrFun heq3 _).trans (hR4.pres γ₃ hcl3 _ (by decide))
  have hf4 : ctxMagRows35.fwdBits δ ⟨327, by decide⟩ = γ₄ ⟨327, by decide⟩ :=
    (congrFun heq4 _).trans (hR5.pres γ₄ hcl4 _ (by decide))
  have hf5 : ctxMagRows35.fwdBits δ ⟨329, by decide⟩ = γ₅ ⟨329, by decide⟩ :=
    (congrFun heq5 _).trans (hR6.pres γ₅ hcl5 _ (by decide))
  have hf6 : ctxMagRows35.fwdBits δ ⟨331, by decide⟩ = γ₆ ⟨331, by decide⟩ :=
    (congrFun heq6 _).trans (hR7.pres γ₆ hcl6 _ (by decide))
  have hf7a : ctxMagRows35.fwdBits δ ⟨333, by decide⟩ = γ₇ ⟨333, by decide⟩ :=
    (congrFun heq7 _).trans (hR8.pres γ₇ hcl7 _ (by decide))
  have hf7b : ctxMagRows35.fwdBits δ ⟨334, by decide⟩ = γ₇ ⟨334, by decide⟩ :=
    (congrFun heq7 _).trans (hR8.pres γ₇ hcl7 _ (by decide))
  have hf9 : ctxMagRows35.fwdBits δ ⟨339, by decide⟩ = γ₉ ⟨339, by decide⟩ :=
    (congrFun heq9 _).trans (hR10.pres γ₉ hcl9 _ (by decide))
  have hf10 : ctxMagRows35.fwdBits δ ⟨342, by decide⟩ = γ₁₀ ⟨342, by decide⟩ :=
    (congrFun heq10 _).trans (hR11.pres γ₁₀ hcl10 _ (by decide))
  have hf11 : ctxMagRows35.fwdBits δ ⟨345, by decide⟩ = γ₁₁ ⟨345, by decide⟩ :=
    (congrFun heq11 _).trans (hR12.pres γ₁₁ hcl11 _ (by decide))
  have hf12 : ctxMagRows35.fwdBits δ ⟨347, by decide⟩ = γ₁₂ ⟨347, by decide⟩ :=
    (congrFun heq12 _).trans (hP13.pres γ₁₂ hcl12 _ (by decide))
  have hf13 : ∀ q : Wire 437, ctxMagRows35.fwdBits δ q = ctxKw2_56.fwdBits γ₁₂ q :=
    fun q ↦ congrFun heq12 q
  refine ⟨fun b ↦ ?_, fun b ↦ ?_⟩
  · fin_cases b
    · exact (hf1.trans ho1).trans (congrArg Slot3MicroEngineAux.boolToZMod2 hb.1)
    · exact (hf3.trans ho3).trans (congrArg Slot3MicroEngineAux.boolToZMod2 hb.2.1)
    · exact (hf4.trans ho4).trans (congrArg Slot3MicroEngineAux.boolToZMod2 hb.2.2.1)
    · exact (hf5.trans ho5).trans (congrArg Slot3MicroEngineAux.boolToZMod2 hb.2.2.2.1)
    · exact (hf6.trans ho6).trans (congrArg Slot3MicroEngineAux.boolToZMod2 hb.2.2.2.2.1)
    · exact (hf7a.trans ho7.1).trans (congrArg Slot3MicroEngineAux.boolToZMod2 hb.2.2.2.2.2.1)
    · exact (hf7b.trans ho7.2).trans (congrArg Slot3MicroEngineAux.boolToZMod2 hb.2.2.2.2.2.2.1)
  · fin_cases b
    · exact (hf2.trans ho2).trans (congrArg Slot3MicroEngineAux.boolToZMod2 hb.2.2.2.2.2.2.2.1)
    · exact (hf9.trans ho9).trans (congrArg Slot3MicroEngineAux.boolToZMod2 hb.2.2.2.2.2.2.2.2.1)
    · exact (hf10.trans ho10).trans (congrArg Slot3MicroEngineAux.boolToZMod2
        hb.2.2.2.2.2.2.2.2.2.1)
    · exact (hf11.trans ho11).trans (congrArg Slot3MicroEngineAux.boolToZMod2
        hb.2.2.2.2.2.2.2.2.2.2.1)
    · exact (hf12.trans ho12).trans (congrArg Slot3MicroEngineAux.boolToZMod2
        hb.2.2.2.2.2.2.2.2.2.2.2.1)
    · exact ((hf13 _).trans ho13.1).trans (congrArg Slot3MicroEngineAux.boolToZMod2
        hb.2.2.2.2.2.2.2.2.2.2.2.2.1)
    · exact ((hf13 _).trans ho13.2).trans (congrArg Slot3MicroEngineAux.boolToZMod2
        hb.2.2.2.2.2.2.2.2.2.2.2.2.2)
private theorem p5af {a b : Bool} (h : (!a || b) = true) (ha : a = true) : b = true := by
  subst ha; exact h
private theorem p5b0 (a b : ZMod 2) :
    decide (a * b = 1) = (decide (a = 1) && decide (b = 1)) := by
  revert a b; decide
private theorem p5b1 (g : Fin 3 → ZMod 2) : (if decide (g 0 = 1) then 1 else 0) + 2 *
    (if decide (g 1 = 1) then 1 else 0) + 4 * (if decide (g 2 = 1) then 1 else 0) = bitsVal g
    := by
  revert g; decide
private theorem zmod2_eq_boolToZMod2_decide (z : ZMod 2) :
    z = Slot3MicroEngineAux.boolToZMod2 (decide (z = 1)) := by
  rcases bit_cases z with rfl | rfl <;> rfl
theorem magUnpackFromRetQuad51_275_spec :
    IsMutBlock 437 (437 - 275) (fun q ↦ ∃ w b, q = p57MW w b) magUnpackFromRetQuad51_275 ∧
      magUnpackFromRetQuad51_275.countTempAnd = 51 ∧
      (∀ β : BitAssignment 437, cleanRem 437 (437 - 275) β →
        InvMuQuad3 β →
        let u22 : Fin 4194304 := ⟨bitsVal (fun i ↦ β (u22WAux i)), bitsVal_lt_two_pow _⟩
        bitsVal (fun i ↦ β (muW i)) = shellMu3 u22 →
        magUnpackFromRetQuad51_275.evalBits β = magUnpack63_275.evalBits β) := by
  have hnot_u22 : ∀ i : Fin 22, ¬ mutMagDest21 (u22WAux i) := by
    rintro i ⟨idx, h⟩; have hv := congrArg Fin.val h; dsimp [u22WAux, magDest21, p57MW] at hv; omega
  let hinQ : ∀ i, (muQuadIn6W i).val < 275 := fun i ↦ by revert i; decide
  let hinF : ∀ i, (muW i).val < 275 := fun i ↦ by dsimp [muW]; omega
  obtain ⟨hCnt1, hProps1, hLift1, hEvalQ⟩ :=
    Slot3MicroEngineAux.ctxMicro_scoped muQuadIn6W muQuadIn6W_inj 275 14 0 hinQ
      mu3OneHot7GeFromQuadOps mu3OneHot7GeFromQuad_meta (by decide)
  obtain ⟨_, _, _, hEvalF⟩ := Slot3MicroEngineAux.ctxMicro_scoped muW muW_inj 275 14 3
      hinF mu3OneHot7GeFastOps mu3OneHot7GeFast_meta3 (by decide)
  obtain ⟨hd1, hs1⟩ := hProps1 (mutW := mutMagDest21)
    (fun i ↦ not_mutMagDest21_of_outside (muQuadIn6W i) (by revert i; decide))
    not_mutMagDest21_ge275
  let c2 : CliffProg 437 := .cnot (u22WAux 0) ⟨289, by decide⟩ (by decide)
  have hc2_supp : c2.SupportsBelow 290 := ⟨by dsimp [u22WAux]; omega, by dsimp; omega⟩
  have hd2 : (ctxCliffAlloc c2).DisjointFrom mutMagDest21 :=
    ctxCliffAlloc_disjoint ⟨hnot_u22 0, not_mutMagDest21_ge275 _ (by dsimp; omega)⟩
  have hs2 : (ctxCliffAlloc c2).SupportsBelowCtx 290 := ctxCliffAlloc_supports hc2_supp
  have hLift2 : Slot3MicroEngineAux.TempCtxLiftEx 289 290 (ctxCliffAlloc c2) :=
    Slot3MicroEngineAux.TempCtxLiftEx.mono
      (Slot3MicroEngineAux.TempCtxLiftEx.cliff 290 (by decide) c2 hc2_supp)
      (by decide) le_rfl (by decide)
  let l3 : Fin 6 → Wire 437 := fun i ↦ magGeW ⟨i.val + 1, by omega⟩
  let r3 : Fin 6 → Wire 437 := fun i ↦ u22WAux ⟨i.val + 1, by omega⟩
  have hne3 : ∀ i, l3 i ≠ r3 i := fun i ↦ wire_ne_of_gt (by
    have hb := Slot3MicroEngineAux.mu3GeSlots_bounds ⟨i.val + 1, by omega⟩
    dsimp at hb; dsimp [l3, r3, magGeW, u22WAux]; omega)
  have hl3 : ∀ i, (l3 i).val < 290 := fun i ↦ by
    have hb := Slot3MicroEngineAux.mu3GeSlots_bounds ⟨i.val + 1, by omega⟩
    dsimp at hb; dsimp [l3, magGeW]; omega
  have hr3 : ∀ i, (r3 i).val < 290 := fun i ↦ by dsimp [r3, u22WAux]; omega
  have hCnt3 := Slot3MicroEngineAux.ctxAndPairs_countTempAnd (M := 437) 6 290 (by
    decide) l3 r3 hne3 hl3 hr3
  obtain ⟨hd3, hs3⟩ := Slot3MicroEngineAux.ctxAndPairs_props (mutW := mutMagDest21) 6 290 (by
    decide)
    l3 r3 hne3 hl3 hr3
    (fun i ↦ not_mutMagDest21_ge275 _ (by dsimp [l3, magGeW]; omega))
    (fun i ↦ hnot_u22 _)
    (fun q hq ↦ not_mutMagDest21_ge275 q (by omega))
  obtain ⟨hLift3, hEval3⟩ := Slot3MicroEngineAux.ctxAndPairs_scoped (M := 437) 6 290 (by
    decide) l3 r3 hne3 hl3 hr3
  obtain ⟨hPkgB0, hEvalB0⟩ := ctxMagB0_10_spec
  obtain ⟨hPkgRows, hEvalRows⟩ := ctxMagRows35_spec
  have hPkgTail := hPkgB0.append hPkgRows
  have hDisjHead : ctxMagHead6.DisjointFrom mutMagDest21 :=
    TempCtx.disjointFrom_append hd1 (TempCtx.disjointFrom_append hd2 hd3)
  have hSuppHead : ctxMagHead6.SupportsBelowCtx 296 :=
    TempCtx.supportsBelowCtx_append (by
      decide) hs1 (TempCtx.supportsBelowCtx_append (by decide) hs2 hs3)
  have hLiftHead : Slot3MicroEngineAux.TempCtxLiftEx 275 296 ctxMagHead6 :=
    Slot3MicroEngineAux.TempCtxLiftEx.append hLift1 (Slot3MicroEngineAux.TempCtxLiftEx.append hLift2
      hLift3)
  have hDisjAll : magUnpackFromRetQuad51_275Ctx.DisjointFrom mutMagDest21 :=
    TempCtx.disjointFrom_append hDisjHead hPkgTail.disj
  have hSuppAll : magUnpackFromRetQuad51_275Ctx.SupportsBelowCtx 351 :=
    TempCtx.supportsBelowCtx_append (by decide) hSuppHead hPkgTail.supp
  have hLiftAll : Slot3MicroEngineAux.TempCtxLiftEx 275 351 magUnpackFromRetQuad51_275Ctx :=
    Slot3MicroEngineAux.TempCtxLiftEx.append hLiftHead hPkgTail.lift
  obtain ⟨hB, hCnt, hEv⟩ := xorBlock275_spec (curEnd := 351) (by decide) (by decide)
    magDest21 magSrc21Fast
    (fun idx ↦ by dsimp [magDest21, p57MW]; omega) magDest21_inj
    (fun idx ↦ by revert idx; decide)
    magUnpackFromRetQuad51_275Ctx hDisjAll hSuppAll hLiftAll
  have hCntTot : magUnpackFromRetQuad51_275Ctx.countTempAnd = 51 := by
    dsimp only [magUnpackFromRetQuad51_275Ctx, ctxMagHead6]
    rw[Slot3MicroEngineAux.TempCtx.append_countTempAnd,
        Slot3MicroEngineAux.TempCtx.append_countTempAnd,
        Slot3MicroEngineAux.TempCtx.append_countTempAnd, hCnt1, hCnt3, hPkgTail.cnt]
    rfl
  have hB' : IsMutBlock 437 (437 - 275) (fun q ↦ ∃ w b, q = p57MW w b) magUnpackFromRetQuad51_275 :=
    ⟨hB.1, hB.2.1, hB.2.2.1, fun β hβ q hq ↦ hB.2.2.2 β hβ q
      (fun ⟨idx, h⟩ ↦ hq ⟨⟨idx.val / 7, by omega⟩, ⟨idx.val % 7, by omega⟩, h⟩)⟩
  obtain ⟨hB63, _, hEv63⟩ := magUnpack63_275_spec
  refine ⟨hB', hCnt.trans hCntTot, fun β hβ hQ hmu ↦ ?_⟩
  funext q
  by_cases hq : ∃ w b, q = p57MW w b
  · obtain ⟨w, b, rfl⟩ := hq
    set u22 : Fin 4194304 := ⟨bitsVal (fun i ↦ β (u22WAux i)), bitsVal_lt_two_pow _⟩
    have h63 : magUnpack63_275.evalBits β (p57MW w b) = β (p57MW w b) + if
        (shellMagCoord3 u22 w).testBit b.val then 1 else 0 := hEv63 β hβ hmu w b
    have huBitAll : ∀ i : Fin 22,
      β (u22WAux i) = Slot3MicroEngineAux.boolToZMod2 (u22.val.testBit i.val) :=
      u22_testBit_eq_wire u22WAux β u22 rfl
    clear_value u22
    set μ := shellMu3 u22
    have hμ7 : μ < 7 := shellMu3_lt_seven u22
    have hμ_lt7 : bitsVal (fun i ↦ β (muW i)) < 7 := hmu.symm ▸ hμ7
    let idx : Fin 21 := ⟨7 * w.val + b.val, by have := w.isLt; have := b.isLt; omega⟩
    have hdest : magDest21 idx = p57MW w b :=
      Fin.ext (by have := b.isLt; dsimp [magDest21, p57MW, idx]; omega)
    rw [← hdest]
    dsimp only [magUnpackFromRetQuad51_275]
    rw [hEv β hβ idx, hdest, h63]
    refine congrArg (β (p57MW w b) + ·) ?_
    obtain ⟨hclQ, hpresQ, hsOutQ⟩ := hEvalQ β hβ
    obtain ⟨hclF, hpresF, hsOutF⟩ := hEvalF β hβ
    have hx_lt : bitsVal (fun i ↦ β (muQuadIn6W i)) < 64 := bitsVal_lt_two_pow _
    have hchkQ := (Slot3MicroEngineAux.allBelow_iff 64 mu3OneHot7GeFromQuadEqCheck).mp
      mu3OneHot7GeFromQuadEq_eval_ok _ hx_lt
    dsimp only [mu3OneHot7GeFromQuadEqCheck] at hchkQ
    have hchkQ12 := (Bool.and_eq_true _ _).mp hchkQ
    have hchkF := (Slot3MicroEngineAux.allBelow_iff 7 mu3OneHot7GeFastCheck).mp
      mu3OneHot7GeFast_eval_ok _ hμ_lt7
    dsimp only [mu3OneHot7GeFastCheck] at hchkF
    have hchkF12 := (Bool.and_eq_true _ _).mp hchkF
    have hchkF1 := (Bool.and_eq_true _ _).mp hchkF12.1
    have ht : ∀ i : Fin 6, (bitsVal (fun j ↦ β (muQuadIn6W j))).testBit i.val = decide
        (β (muQuadIn6W i) = 1) := Slot3MicroEngineAux.bitsVal_testBit_eq _
    have hm_eq : (if (bitsVal (fun j ↦ β (muQuadIn6W j))).testBit 0 then 1 else 0) +
        2 * (if (bitsVal (fun j ↦ β (muQuadIn6W j))).testBit 1 then 1 else 0) +
        4 * (if (bitsVal (fun j ↦ β (muQuadIn6W j))).testBit 2 then 1 else 0) =
        bitsVal (fun i ↦ β (muW i)) := by
      rw [show (bitsVal (fun j ↦ β (muQuadIn6W j))).testBit 0 = _ from ht 0,
        show (bitsVal (fun j ↦ β (muQuadIn6W j))).testBit 1 = _ from ht 1,
        show (bitsVal (fun j ↦ β (muQuadIn6W j))).testBit 2 = _ from ht 2]
      exact p5b1 (fun i ↦ β (muW i))
    have hq3 : ((bitsVal (fun j ↦ β (muQuadIn6W j))).testBit 3 ==
        ((bitsVal (fun j ↦ β (muQuadIn6W j))).testBit 0 &&
         (bitsVal (fun j ↦ β (muQuadIn6W j))).testBit 1)) = true := by
      rw [beq_iff_eq,
        show (bitsVal (fun j ↦ β (muQuadIn6W j))).testBit 3 = _ from ht 3,
        show (bitsVal (fun j ↦ β (muQuadIn6W j))).testBit 0 = _ from ht 0,
        show (bitsVal (fun j ↦ β (muQuadIn6W j))).testBit 1 = _ from ht 1]
      change decide (β (retMuQuadW 0) = 1) = (decide (β (muW 0) = 1) && decide (β (muW 1) = 1))
      rw [hQ 0]; exact p5b0 (β (muW 0)) (β (muW 1))
    have hq4 : ((bitsVal (fun j ↦ β (muQuadIn6W j))).testBit 4 ==
        ((bitsVal (fun j ↦ β (muQuadIn6W j))).testBit 0 &&
         (bitsVal (fun j ↦ β (muQuadIn6W j))).testBit 2)) = true := by
      rw [beq_iff_eq,
        show (bitsVal (fun j ↦ β (muQuadIn6W j))).testBit 4 = _ from ht 4,
        show (bitsVal (fun j ↦ β (muQuadIn6W j))).testBit 0 = _ from ht 0,
        show (bitsVal (fun j ↦ β (muQuadIn6W j))).testBit 2 = _ from ht 2]
      change decide (β (retMuQuadW 1) = 1) = (decide (β (muW 0) = 1) && decide (β (muW 2) = 1))
      rw [hQ 1]; exact p5b0 (β (muW 0)) (β (muW 2))
    have hq5 : ((bitsVal (fun j ↦ β (muQuadIn6W j))).testBit 5 ==
        ((bitsVal (fun j ↦ β (muQuadIn6W j))).testBit 1 &&
         (bitsVal (fun j ↦ β (muQuadIn6W j))).testBit 2)) = true := by
      rw [beq_iff_eq,
        show (bitsVal (fun j ↦ β (muQuadIn6W j))).testBit 5 = _ from ht 5,
        show (bitsVal (fun j ↦ β (muQuadIn6W j))).testBit 1 = _ from ht 1,
        show (bitsVal (fun j ↦ β (muQuadIn6W j))).testBit 2 = _ from ht 2]
      change decide (β (retMuQuadW 2) = 1) = (decide (β (muW 1) = 1) && decide (β (muW 2) = 1))
      rw [hQ 2]; exact p5b0 (β (muW 1)) (β (muW 2))
    have hCond : (decide (((if (bitsVal (fun j ↦ β (muQuadIn6W j))).testBit 0 then 1 else 0) +
        2 * (if (bitsVal (fun j ↦ β (muQuadIn6W j))).testBit 1 then 1 else 0) + 4 * (if
        (bitsVal (fun j ↦ β (muQuadIn6W j))).testBit 2 then 1 else 0)) < 7) && ((bitsVal (fun
        j ↦ β (muQuadIn6W j))).testBit 3 == ((bitsVal (fun j ↦ β (muQuadIn6W j))).testBit 0 &&
        (bitsVal (fun j ↦ β (muQuadIn6W j))).testBit 1)) && ((bitsVal (fun j ↦ β (muQuadIn6W
        j))).testBit 4 == ((bitsVal (fun j ↦ β (muQuadIn6W j))).testBit 0 && (bitsVal (fun j ↦
        β (muQuadIn6W j))).testBit 2)) && ((bitsVal (fun j ↦ β (muQuadIn6W j))).testBit 5 ==
        ((bitsVal (fun j ↦ β (muQuadIn6W j))).testBit 1 && (bitsVal (fun j ↦ β (muQuadIn6W
        j))).testBit 2))) = true := by
      rw [hm_eq, decide_eq_true hμ_lt7, hq3, hq4, hq5]; rfl
    have hSlotsEq := p5af hchkQ12.2 hCond
    let k1Q := Slot3MicroEngineAux.ctxMicro muQuadIn6W muQuadIn6W_inj 275 14 0 hinQ
      mu3OneHot7GeFromQuadOps mu3OneHot7GeFromQuad_meta (by decide)
    let k1F := Slot3MicroEngineAux.ctxMicro muW muW_inj 275 14 3 hinF
      mu3OneHot7GeFastOps mu3OneHot7GeFast_meta3 (by decide)
    have hk1_eq : k1Q.fwdBits β = k1F.fwdBits β := by
      funext w₀
      by_cases hw275 : w₀.val < 275
      · exact (hpresQ hchkQ12.1 w₀ hw275).trans (hpresF hchkF1.1 w₀ hw275).symm
      · by_cases hw289 : w₀.val < 289
        · let k := w₀.val - 275
          have hk14 : k < 14 := by omega
          have hw_q : w₀ = ⟨275 + (6 + k - 6), by omega⟩ := Fin.ext (by dsimp [k]; omega)
          have hw_f : w₀ = ⟨275 + (3 + k - 3), by omega⟩ := Fin.ext (by dsimp [k]; omega)
          have hq_out := hsOutQ (6 + k) (by omega) (by omega)
          have hf_out := hsOutF (3 + k) (by omega) (by omega)
          have hbe := (Slot3MicroEngineAux.allBelow_iff 14 _).mp hSlotsEq k hk14
          simp only [beq_iff_eq, hm_eq] at hbe
          exact (congrArg _ hw_q).trans (hq_out.trans ((congrArg Slot3MicroEngineAux.boolToZMod2
            hbe).trans (hf_out.symm.trans (congrArg _ hw_f.symm))))
        · exact (hclQ w₀ (by omega)).trans (hclF w₀ (by omega)).symm
    set β₁ := k1F.fwdBits β
    have hu_β₁ : ∀ i : Fin 22, β₁ (u22WAux i) = β (u22WAux i) :=
      fun i ↦ hpresF hchkF1.1 (u22WAux i) (by dsimp [u22WAux]; omega)
    have hmu_β₁ : ∀ j : Fin 3, β₁ (muW j) = β (muW j) :=
      fun j ↦ hpresF hchkF1.1 (muW j) (by dsimp [muW]; omega)
    have hsel_β₁ : ∀ a : Fin 7,
      β₁ (magSel7W a) = Slot3MicroEngineAux.boolToZMod2 (decide (μ = a.val)) := fun a ↦ by
      have hb := Slot3MicroEngineAux.mu3Sel7Slots_bounds a
      have ha := (Slot3MicroEngineAux.allBelow_iff 7 _).mp hchkF1.2 a.val a.isLt
      simp only [beq_iff_eq] at ha
      dsimp only [magSel7W]
      rw [hsOutF _ hb.1 hb.2, ha, hmu]
    have hge_β₁ : ∀ a : Fin 7,
      β₁ (magGeW a) = Slot3MicroEngineAux.boolToZMod2 (decide (a.val ≤ μ)) := fun a ↦ by
      have hb := Slot3MicroEngineAux.mu3GeSlots_bounds a
      have ha := (Slot3MicroEngineAux.allBelow_iff 7 _).mp hchkF12.2 a.val a.isLt
      simp only [beq_iff_eq] at ha
      dsimp only [magGeW]
      rw [hsOutF _ hb.1 hb.2, ha, hmu, decide_eq_true hμ7, Bool.and_true]
    have hcl1_cut : cleanRem 437 (437 - 290) β₁ := cleanRem_anti (by decide) hclF
    have hfwd2 := Slot3MicroEngineAux.ctxCliffAlloc_fwdBits 290 (by decide) c2 hc2_supp β₁ hcl1_cut
    set β₂ := c2.eval β₁
    have hz289 : β₁ ⟨289, by decide⟩ = 0 := hclF ⟨289, by decide⟩ (by dsimp; omega)
    have hcl2 : cleanRem 437 (437 - 290) β₂ := fun q₀ hq₀ ↦ by
      dsimp only [β₂, c2, CliffProg.eval]
      rw [Function.update_of_ne (wire_ne_of_gt (by dsimp; omega))]
      exact hcl1_cut q₀ hq₀
    have hlt289_β₂ : ∀ q₀ : Wire 437, q₀.val < 289 → β₂ q₀ = β₁ q₀ := fun q₀ hq₀ ↦ by
      dsimp only [β₂, c2, CliffProg.eval]
      exact Function.update_of_ne (wire_ne_of_lt (by dsimp; omega)) _ _
    have hw289_β₂ : β₂ ⟨289, by decide⟩ = β (u22WAux 0) := by
      dsimp only [β₂, c2, CliffProg.eval]
      rw [Function.update_self, hz289, zero_add, hu_β₁ 0]
    let k3 := Slot3MicroEngineAux.ctxAndPairs 6 290 (by decide) l3 r3 hne3 hl3 hr3
    obtain ⟨hcl3, hpres3, hpair3⟩ := hEval3 β₂ hcl2
    set β₃ := k3.fwdBits β₂
    have hHead_eq : ctxMagHead6.fwdBits β = β₃ := by
      dsimp only [ctxMagHead6]
      rw [Slot3MicroEngineAux.TempCtx.append_fwdBits, Slot3MicroEngineAux.TempCtx.append_fwdBits,
        hk1_eq]
      exact congrArg k3.fwdBits hfwd2
    have hmu_β₃ : ∀ j : Fin 3, β₃ (muW j) = Slot3MicroEngineAux.boolToZMod2 (μ.testBit j.val) :=
      fun j ↦ by
      rw [hpres3 _ (by dsimp [muW]; omega), hlt289_β₂ _ (by dsimp [muW]; omega), hmu_β₁ j]
      have htb := Slot3MicroEngineAux.bitsVal_testBit_eq (fun k ↦ β (muW k)) j
      rw [hmu] at htb
      rw [htb]
      exact zmod2_eq_boolToZMod2_decide (β (muW j))
    have hu_β₃ : ∀ i : Fin 22,
      β₃ (u22WAux i) = Slot3MicroEngineAux.boolToZMod2 (u22.val.testBit i.val) := fun i ↦ by
      rw [hpres3 _ (by
        dsimp [u22WAux]; omega), hlt289_β₂ _ (by dsimp [u22WAux]; omega), hu_β₁ i, huBitAll i]
    have hsel_β₃ : ∀ a : Fin 7,
      β₃ (magSel7W a) = Slot3MicroEngineAux.boolToZMod2 (decide (μ = a.val)) := fun a ↦ by
      have := Slot3MicroEngineAux.mu3Sel7Slots_bounds a
      rw [hpres3 _ (by
        dsimp [magSel7W]; omega), hlt289_β₂ _ (by dsimp [magSel7W]; omega), hsel_β₁ a]
    have hge_β₃ : ∀ a : Fin 7,
      β₃ (magGeW a) = Slot3MicroEngineAux.boolToZMod2 (decide (a.val ≤ μ)) := fun a ↦ by
      have := Slot3MicroEngineAux.mu3GeSlots_bounds a
      rw [hpres3 _ (by dsimp [magGeW]; omega), hlt289_β₂ _ (by dsimp [magGeW]; omega), hge_β₁ a]
    set β₄ := ctxMagB0_10.fwdBits β₃
    have hcl4 : cleanRem 437 (437 - 316) β₄ := hPkgB0.clean β₃ hcl3
    have hpres4 : ∀ q₀ : Wire 437, q₀.val < 296 → β₄ q₀ = β₃ q₀ := hPkgB0.pres β₃ hcl3
    have hB0_out := hEvalB0 β₃ (μ.testBit 0) (fun k ↦ u22.val.testBit k) hcl3 (hmu_β₃ 0) hu_β₃
    have hmu_β₄ : ∀ j : Fin 3, β₄ (muW j) = Slot3MicroEngineAux.boolToZMod2 (μ.testBit j.val) :=
      fun j ↦ (hpres4 _ (by dsimp [muW]; omega)).trans (hmu_β₃ j)
    have hu_β₄ : ∀ i : Fin 22,
      β₄ (u22WAux i) = Slot3MicroEngineAux.boolToZMod2 (u22.val.testBit i.val) :=
      fun i ↦ (hpres4 _ (by dsimp [u22WAux]; omega)).trans (hu_β₃ i)
    have hsel_β₄ : ∀ a : Fin 7,
      β₄ (magSel7W a) = Slot3MicroEngineAux.boolToZMod2 (decide (μ = a.val)) := fun a ↦ by
      have := Slot3MicroEngineAux.mu3Sel7Slots_bounds a
      exact (hpres4 _ (by dsimp [magSel7W]; omega)).trans (hsel_β₃ a)
    have hge_β₄ : ∀ a : Fin 7,
      β₄ (magGeW a) = Slot3MicroEngineAux.boolToZMod2 (decide (a.val ≤ μ)) := fun a ↦ by
      have := Slot3MicroEngineAux.mu3GeSlots_bounds a
      exact (hpres4 _ (by dsimp [magGeW]; omega)).trans (hge_β₃ a)
    obtain ⟨hRows1, hRows2⟩ := hEvalRows β₄ μ hμ7 (fun k ↦ u22.val.testBit k) hcl4 hmu_β₄
        hu_β₄ hsel_β₄ hge_β₄ hB0_out.1 hB0_out.2.1 hB0_out.2.2.1 hB0_out.2.2.2.1
        hB0_out.2.2.2.2.1 hB0_out.2.2.2.2.2.1 hB0_out.2.2.2.2.2.2.1 hB0_out.2.2.2.2.2.2.2.1
        hB0_out.2.2.2.2.2.2.2.2.1 hB0_out.2.2.2.2.2.2.2.2.2.1 hB0_out.2.2.2.2.2.2.2.2.2.2.1
        hB0_out.2.2.2.2.2.2.2.2.2.2.2.1 hB0_out.2.2.2.2.2.2.2.2.2.2.2.2.1
        hB0_out.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hB0_out.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
        hB0_out.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hB0_out.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    have hAllFwd : magUnpackFromRetQuad51_275Ctx.fwdBits β = ctxMagRows35.fwdBits β₄ := by
      dsimp only [magUnpackFromRetQuad51_275Ctx]
      rw [Slot3MicroEngineAux.TempCtx.append_fwdBits, Slot3MicroEngineAux.TempCtx.append_fwdBits,
        hHead_eq]
    have hw_cases : w = 0 ∨ w = 1 ∨ w = 2 := by
      rcases w with ⟨_ | _ | _ | n, hn⟩
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)
      · omega
    rcases hw_cases with rfl | rfl | rfl
    · have hsrc0 : magSrc21Fast idx = ⟨289 + b.val, by have := b.isLt; omega⟩ := by
        fin_cases b <;> rfl
      rw [hsrc0]
      have hpres_tail : magUnpackFromRetQuad51_275Ctx.fwdBits β ⟨289 + b.val, by
        have := b.isLt; omega⟩ =
          β₃ ⟨289 + b.val, by have := b.isLt; omega⟩ := by
        dsimp only [magUnpackFromRetQuad51_275Ctx]
        rw [Slot3MicroEngineAux.TempCtx.append_fwdBits, hHead_eq]
        exact hPkgTail.pres β₃ hcl3 _ (by have := b.isLt; dsimp; omega)
      rw [hpres_tail]
      by_cases hb0 : b.val = 0
      · have hb_eq : b = 0 := Fin.ext hb0
        subst hb_eq
        have hw_eq : (⟨289 + (0 : Fin 7).val, by omega⟩ : Wire 437) = ⟨289, by decide⟩ := rfl
        rw [hw_eq, hpres3 _ (by dsimp; omega), hw289_β₂, huBitAll 0, shellMagCoord3_testBit_eq]
        simp [Slot3MicroEngineAux.boolToZMod2]
      · let i : Fin 6 := ⟨b.val - 1, by have := b.isLt; omega⟩
        have hw_eq : (⟨289 + b.val, by have := b.isLt; omega⟩ : Wire 437) =
            ⟨290 + i.val, by omega⟩ := Fin.ext (by dsimp [i]; omega)
        have hi1 : (⟨i.val + 1, by omega⟩ : Fin 7) = b := Fin.ext (by dsimp [i]; omega)
        have hi22 : (⟨i.val + 1, by omega⟩ : Fin 22) = ⟨b.val, by have := b.isLt; omega⟩ :=
          Fin.ext (by dsimp [i]; omega)
        rw [hw_eq, hpair3 i]
        dsimp only [l3, r3]
        have h1_lt : (magGeW ⟨i.val + 1, by omega⟩).val < 289 := by
          have hb := Slot3MicroEngineAux.mu3GeSlots_bounds ⟨i.val + 1, by omega⟩
          dsimp at hb; dsimp [magGeW]; omega
        have h2_lt : (u22WAux ⟨i.val + 1, by omega⟩).val < 289 := by dsimp [u22WAux]; omega
        rw [hlt289_β₂ _ h1_lt, hlt289_β₂ _ h2_lt,
          hge_β₁, hu_β₁, huBitAll, hi1, hi22, shellMagCoord3_testBit_eq]
        have h0mul : (0 : Fin 3).val * (shellMu3 u22 + 1) + b.val = b.val := by
          change 0 * (shellMu3 u22 + 1) + b.val = b.val; omega
        have h22v : (⟨b.val, by have := b.isLt; omega⟩ : Fin 22).val = b.val := rfl
        rw [h0mul, h22v]
        by_cases hle : b.val ≤ μ <;>
          by_cases htb : u22.val.testBit b.val = true <;>
          simp [Slot3MicroEngineAux.boolToZMod2, μ, hle, htb]
    · have hidx1 : idx = ⟨7 + b.val, by omega⟩ := Fin.ext rfl
      rw [hAllFwd, hidx1, hRows1 b, shellMagCoord3_testBit_eq]
      rfl
    · have hidx2 : idx = ⟨14 + b.val, by omega⟩ := Fin.ext rfl
      rw [hAllFwd, hidx2, hRows2 b, shellMagCoord3_testBit_eq]
      rfl
  · exact (hB'.2.2.2 β hβ q hq).trans (hB63.2.2.2 β hβ q hq).symm
/-!
## Section 2: `< 374`-Wire `sTrue18` Split (`K_ph1_82_374` `82` `TempAnd`s + `K_ph2_60_374` `60`
`TempAnd`s)
-/
def localSqAx0Ph1A : List LocalStep := [
  .tempAnd (.cons false (.cons false (.cons false (.cons false (.cons false (.cons false .nil))))))
    (.cons false (.cons false (.cons false (.cons true (.cons false (.cons false .nil)))))) (.cons
    false (.cons false (.cons true (.cons false (.cons false (.cons false .nil)))))),
  .tempAnd (.cons false (.cons false (.cons false (.cons false (.cons false (.cons false .nil))))))
    (.cons false (.cons false (.cons false (.cons true (.cons false (.cons true .nil)))))) (.cons
    false (.cons false (.cons true (.cons false (.cons false (.cons true .nil)))))),
  .tempAnd (.cons false (.cons false (.cons false (.cons false (.cons false (.cons true .nil))))))
    (.cons false (.cons false (.cons false (.cons true (.cons false (.cons false .nil)))))) (.cons
    false (.cons false (.cons true (.cons false (.cons true (.cons false .nil)))))),
  .tempAnd (.cons false (.cons false (.cons false (.cons false (.cons false (.cons false .nil))))))
    (.cons false (.cons false (.cons false (.cons true (.cons true (.cons false .nil)))))) (.cons
    false (.cons false (.cons true (.cons false (.cons true (.cons true .nil)))))),
  .tempAnd (.cons false (.cons false (.cons false (.cons false (.cons false (.cons true .nil))))))
    (.cons false (.cons false (.cons false (.cons true (.cons false (.cons true .nil)))))) (.cons
    false (.cons false (.cons true (.cons true (.cons false (.cons false .nil)))))),
  .tempAnd (.cons false (.cons false (.cons false (.cons false (.cons true (.cons false .nil))))))
    (.cons false (.cons false (.cons false (.cons true (.cons false (.cons false .nil)))))) (.cons
    false (.cons false (.cons true (.cons true (.cons false (.cons true .nil)))))),
  .tempAnd (.cons false (.cons false (.cons false (.cons false (.cons true (.cons true .nil))))))
    (.cons false (.cons false (.cons false (.cons true (.cons false (.cons true .nil)))))) (.cons
    false (.cons false (.cons true (.cons true (.cons true (.cons false .nil)))))),
  .tempAnd (.cons false (.cons false (.cons false (.cons false (.cons true (.cons false .nil))))))
    (.cons false (.cons false (.cons false (.cons true (.cons true (.cons true .nil)))))) (.cons
    false (.cons false (.cons true (.cons true (.cons true (.cons true .nil)))))),
  .tempAnd (.cons false (.cons false (.cons false (.cons false (.cons true (.cons true .nil))))))
    (.cons false (.cons false (.cons false (.cons true (.cons true (.cons false .nil)))))) (.cons
    false (.cons true (.cons false (.cons false (.cons false (.cons false .nil)))))),
  .tempAnd (.cons false (.cons false (.cons false (.cons false (.cons true (.cons true .nil))))))
    (.cons false (.cons false (.cons false (.cons true (.cons true (.cons true .nil)))))) (.cons
    false (.cons true (.cons false (.cons false (.cons false (.cons true .nil)))))),
  .x (.cons false (.cons false (.cons false (.cons false (.cons true (.cons true .nil)))))),
  .x (.cons false (.cons false (.cons false (.cons false (.cons true (.cons false .nil)))))),
  .tempAnd (.cons false (.cons false (.cons false (.cons false (.cons true (.cons true .nil))))))
    (.cons false (.cons false (.cons false (.cons false (.cons true (.cons false .nil)))))) (.cons
    false (.cons true (.cons false (.cons false (.cons true (.cons false .nil)))))),
  .x (.cons false (.cons false (.cons false (.cons false (.cons true (.cons false .nil)))))),
  .x (.cons false (.cons false (.cons false (.cons false (.cons true (.cons true .nil)))))),
  .x (.cons false (.cons false (.cons false (.cons false (.cons false (.cons true .nil)))))),
  .x (.cons false (.cons false (.cons false (.cons false (.cons false (.cons false .nil)))))),
  .tempAnd (.cons false (.cons false (.cons false (.cons false (.cons false (.cons true .nil))))))
    (.cons false (.cons false (.cons false (.cons false (.cons false (.cons false .nil)))))) (.cons
    false (.cons true (.cons false (.cons false (.cons true (.cons true .nil)))))),
  .x (.cons false (.cons false (.cons false (.cons false (.cons false (.cons false .nil)))))),
  .x (.cons false (.cons false (.cons false (.cons false (.cons false (.cons true .nil)))))),
  .x (.cons false (.cons false (.cons false (.cons false (.cons true (.cons true .nil)))))),
  .cnot (.cons false (.cons true (.cons false (.cons false (.cons true (.cons true .nil)))))) (.cons
    false (.cons false (.cons false (.cons false (.cons true (.cons true .nil)))))),
  .cnot (.cons false (.cons false (.cons false (.cons false (.cons true (.cons false .nil))))))
    (.cons false (.cons false (.cons false (.cons false (.cons false (.cons false .nil)))))),
  .cnot (.cons false (.cons true (.cons false (.cons false (.cons true (.cons true .nil)))))) (.cons
    false (.cons false (.cons false (.cons false (.cons false (.cons false .nil)))))),
  .tempAnd (.cons false (.cons false (.cons false (.cons false (.cons true (.cons true .nil))))))
    (.cons false (.cons false (.cons false (.cons false (.cons false (.cons false .nil)))))) (.cons
    false (.cons true (.cons false (.cons true (.cons false (.cons false .nil)))))),
  .cnot (.cons false (.cons true (.cons false (.cons false (.cons true (.cons true .nil)))))) (.cons
    false (.cons false (.cons false (.cons false (.cons false (.cons false .nil)))))),
  .cnot (.cons false (.cons false (.cons false (.cons false (.cons true (.cons false .nil))))))
    (.cons false (.cons false (.cons false (.cons false (.cons false (.cons false .nil)))))),
  .cnot (.cons false (.cons true (.cons false (.cons false (.cons true (.cons true .nil)))))) (.cons
    false (.cons false (.cons false (.cons false (.cons true (.cons true .nil)))))),
  .x (.cons false (.cons false (.cons false (.cons false (.cons true (.cons true .nil)))))),
  .cnot (.cons false (.cons false (.cons false (.cons false (.cons true (.cons true .nil))))))
    (.cons false (.cons false (.cons false (.cons false (.cons true (.cons false .nil)))))),
  .cnot (.cons false (.cons true (.cons false (.cons false (.cons true (.cons true .nil)))))) (.cons
    false (.cons false (.cons false (.cons false (.cons true (.cons false .nil)))))),
  .cnot (.cons false (.cons false (.cons false (.cons false (.cons false (.cons true .nil))))))
    (.cons false (.cons false (.cons false (.cons false (.cons false (.cons false .nil)))))),
  .cnot (.cons false (.cons true (.cons false (.cons true (.cons false (.cons false .nil))))))
    (.cons false (.cons false (.cons false (.cons false (.cons false (.cons false .nil)))))),
  .tempAnd (.cons false (.cons false (.cons false (.cons false (.cons true (.cons false .nil))))))
    (.cons false (.cons false (.cons false (.cons false (.cons false (.cons false .nil)))))) (.cons
    false (.cons true (.cons false (.cons true (.cons false (.cons true .nil)))))),
  .cnot (.cons false (.cons true (.cons false (.cons true (.cons false (.cons false .nil))))))
    (.cons false (.cons false (.cons false (.cons false (.cons false (.cons false .nil)))))),
  .cnot (.cons false (.cons false (.cons false (.cons false (.cons false (.cons true .nil))))))
    (.cons false (.cons false (.cons false (.cons false (.cons false (.cons false .nil)))))),
  .cnot (.cons false (.cons true (.cons false (.cons false (.cons true (.cons true .nil)))))) (.cons
    false (.cons false (.cons false (.cons false (.cons true (.cons false .nil)))))),
  .cnot (.cons false (.cons false (.cons false (.cons false (.cons true (.cons true .nil))))))
    (.cons false (.cons false (.cons false (.cons false (.cons true (.cons false .nil)))))),
  .x (.cons false (.cons true (.cons false (.cons true (.cons false (.cons true .nil)))))),
  .cnot (.cons false (.cons false (.cons false (.cons false (.cons true (.cons true .nil))))))
    (.cons false (.cons true (.cons false (.cons true (.cons false (.cons true .nil)))))),
  .cnot (.cons false (.cons false (.cons false (.cons false (.cons false (.cons true .nil))))))
    (.cons false (.cons true (.cons false (.cons false (.cons true (.cons false .nil)))))),
  .cnot (.cons false (.cons false (.cons false (.cons false (.cons true (.cons true .nil))))))
    (.cons false (.cons true (.cons false (.cons false (.cons true (.cons false .nil)))))),
  .tempAnd (.cons false (.cons true (.cons false (.cons true (.cons false (.cons true .nil))))))
    (.cons false (.cons true (.cons false (.cons false (.cons true (.cons false .nil)))))) (.cons
    false (.cons true (.cons false (.cons true (.cons true (.cons false .nil)))))),
  .cnot (.cons false (.cons false (.cons false (.cons false (.cons true (.cons true .nil))))))
    (.cons false (.cons true (.cons false (.cons false (.cons true (.cons false .nil)))))),
  .cnot (.cons false (.cons false (.cons false (.cons false (.cons false (.cons true .nil))))))
    (.cons false (.cons true (.cons false (.cons false (.cons true (.cons false .nil)))))),
  .cnot (.cons false (.cons false (.cons false (.cons false (.cons true (.cons true .nil))))))
    (.cons false (.cons true (.cons false (.cons true (.cons false (.cons true .nil)))))),
  .x (.cons false (.cons true (.cons false (.cons true (.cons false (.cons true .nil)))))),
  .cnot (.cons false (.cons true (.cons false (.cons true (.cons true (.cons false .nil)))))) (.cons
    false (.cons true (.cons false (.cons true (.cons false (.cons true .nil)))))),
  .cnot (.cons false (.cons true (.cons false (.cons true (.cons true (.cons false .nil)))))) (.cons
    false (.cons true (.cons false (.cons true (.cons false (.cons false .nil)))))),
  .cnot (.cons false (.cons true (.cons false (.cons true (.cons true (.cons false .nil)))))) (.cons
    false (.cons true (.cons false (.cons false (.cons true (.cons false .nil)))))),
  .cnot (.cons false (.cons true (.cons false (.cons true (.cons true (.cons false .nil)))))) (.cons
    false (.cons false (.cons false (.cons false (.cons true (.cons true .nil)))))),
  .cnot (.cons false (.cons true (.cons false (.cons true (.cons false (.cons true .nil)))))) (.cons
    false (.cons true (.cons false (.cons true (.cons true (.cons false .nil)))))),
  .cnot (.cons false (.cons true (.cons false (.cons true (.cons false (.cons true .nil)))))) (.cons
    false (.cons true (.cons false (.cons true (.cons false (.cons false .nil)))))),
  .cnot (.cons false (.cons true (.cons false (.cons true (.cons false (.cons true .nil)))))) (.cons
    false (.cons true (.cons false (.cons false (.cons true (.cons true .nil)))))),
  .cnot (.cons false (.cons true (.cons false (.cons true (.cons false (.cons true .nil)))))) (.cons
    false (.cons true (.cons false (.cons false (.cons true (.cons false .nil)))))),
  .cnot (.cons false (.cons true (.cons false (.cons true (.cons false (.cons true .nil)))))) (.cons
    false (.cons false (.cons false (.cons false (.cons true (.cons true .nil)))))),
  .cnot (.cons false (.cons true (.cons false (.cons true (.cons false (.cons true .nil)))))) (.cons
    false (.cons false (.cons false (.cons false (.cons false (.cons true .nil)))))),
  .cnot (.cons false (.cons true (.cons false (.cons true (.cons false (.cons false .nil))))))
    (.cons false (.cons true (.cons false (.cons true (.cons false (.cons true .nil)))))),
  .cnot (.cons false (.cons true (.cons false (.cons true (.cons false (.cons false .nil))))))
    (.cons false (.cons true (.cons false (.cons false (.cons true (.cons true .nil)))))),
  .cnot (.cons false (.cons true (.cons false (.cons false (.cons true (.cons true .nil)))))) (.cons
    false (.cons true (.cons false (.cons true (.cons true (.cons false .nil)))))),
  .cnot (.cons false (.cons true (.cons false (.cons false (.cons true (.cons true .nil)))))) (.cons
    false (.cons true (.cons false (.cons true (.cons false (.cons true .nil)))))),
  .cnot (.cons false (.cons true (.cons false (.cons false (.cons true (.cons true .nil)))))) (.cons
    false (.cons false (.cons false (.cons false (.cons true (.cons true .nil)))))),
  .cnot (.cons false (.cons true (.cons false (.cons false (.cons true (.cons true .nil)))))) (.cons
    false (.cons false (.cons false (.cons false (.cons true (.cons false .nil)))))),
  .cnot (.cons false (.cons true (.cons false (.cons true (.cons false (.cons false .nil))))))
    (.cons false (.cons true (.cons false (.cons false (.cons true (.cons true .nil)))))),
  .cnot (.cons false (.cons true (.cons false (.cons false (.cons true (.cons true .nil)))))) (.cons
    false (.cons true (.cons false (.cons true (.cons false (.cons false .nil)))))),
  .cnot (.cons false (.cons true (.cons false (.cons true (.cons false (.cons false .nil))))))
    (.cons false (.cons true (.cons false (.cons false (.cons true (.cons true .nil)))))),
  .cnot (.cons false (.cons true (.cons false (.cons false (.cons true (.cons false .nil))))))
    (.cons false (.cons false (.cons false (.cons false (.cons true (.cons false .nil)))))),
  .cnot (.cons false (.cons true (.cons false (.cons true (.cons false (.cons false .nil))))))
    (.cons false (.cons true (.cons false (.cons false (.cons true (.cons false .nil)))))),
  .cnot (.cons false (.cons true (.cons false (.cons false (.cons true (.cons false .nil))))))
    (.cons false (.cons true (.cons false (.cons true (.cons false (.cons false .nil)))))),
  .cnot (.cons false (.cons true (.cons false (.cons true (.cons false (.cons false .nil))))))
    (.cons false (.cons true (.cons false (.cons false (.cons true (.cons false .nil)))))),
  .cnot (.cons false (.cons false (.cons false (.cons false (.cons true (.cons true .nil))))))
    (.cons false (.cons true (.cons false (.cons true (.cons true (.cons false .nil)))))),
  .cnot (.cons false (.cons true (.cons false (.cons true (.cons false (.cons true .nil)))))) (.cons
    false (.cons false (.cons false (.cons false (.cons true (.cons true .nil)))))),
  .cnot (.cons false (.cons false (.cons false (.cons false (.cons true (.cons true .nil))))))
    (.cons false (.cons true (.cons false (.cons true (.cons false (.cons true .nil)))))),
  .cnot (.cons false (.cons true (.cons false (.cons true (.cons false (.cons true .nil)))))) (.cons
    false (.cons false (.cons false (.cons false (.cons true (.cons true .nil)))))),
  .cnot (.cons false (.cons false (.cons false (.cons false (.cons true (.cons false .nil))))))
    (.cons false (.cons true (.cons false (.cons true (.cons false (.cons true .nil)))))),
  .cnot (.cons false (.cons false (.cons false (.cons false (.cons true (.cons false .nil))))))
    (.cons false (.cons true (.cons false (.cons false (.cons true (.cons false .nil)))))),
  .cnot (.cons false (.cons false (.cons false (.cons false (.cons true (.cons true .nil))))))
    (.cons false (.cons false (.cons false (.cons false (.cons true (.cons false .nil)))))),
  .cnot (.cons false (.cons false (.cons false (.cons false (.cons true (.cons false .nil))))))
    (.cons false (.cons false (.cons false (.cons false (.cons true (.cons true .nil)))))),
  .cnot (.cons false (.cons false (.cons false (.cons false (.cons true (.cons true .nil))))))
    (.cons false (.cons false (.cons false (.cons false (.cons true (.cons false .nil)))))),
  .cnot (.cons false (.cons false (.cons false (.cons false (.cons false (.cons true .nil))))))
    (.cons false (.cons true (.cons false (.cons true (.cons false (.cons false .nil)))))),
  .cnot (.cons false (.cons false (.cons false (.cons false (.cons false (.cons true .nil))))))
    (.cons false (.cons false (.cons false (.cons false (.cons true (.cons false .nil)))))),
  .cnot (.cons false (.cons false (.cons false (.cons false (.cons false (.cons false .nil))))))
    (.cons false (.cons true (.cons false (.cons false (.cons true (.cons true .nil)))))),
  .cnot (.cons false (.cons false (.cons false (.cons false (.cons false (.cons false .nil))))))
    (.cons false (.cons false (.cons false (.cons false (.cons true (.cons false .nil)))))),
  .x (.cons false (.cons false (.cons false (.cons false (.cons false (.cons true .nil)))))),
  .x (.cons false (.cons false (.cons false (.cons false (.cons true (.cons true .nil)))))),
  .x (.cons false (.cons true (.cons false (.cons false (.cons true (.cons false .nil)))))),
  .x (.cons false (.cons true (.cons false (.cons true (.cons false (.cons true .nil)))))),
  .x (.cons false (.cons false (.cons false (.cons true (.cons true (.cons true .nil)))))),
  .x (.cons false (.cons false (.cons false (.cons true (.cons true (.cons false .nil)))))),
  .tempAnd (.cons false (.cons false (.cons false (.cons true (.cons true (.cons true .nil))))))
    (.cons false (.cons false (.cons false (.cons true (.cons true (.cons false .nil)))))) (.cons
    false (.cons true (.cons false (.cons true (.cons true (.cons true .nil)))))),
  .x (.cons false (.cons false (.cons false (.cons true (.cons true (.cons false .nil)))))),
  .x (.cons false (.cons false (.cons false (.cons true (.cons true (.cons true .nil)))))),
  .x (.cons false (.cons false (.cons false (.cons true (.cons false (.cons true .nil)))))),
  .x (.cons false (.cons false (.cons false (.cons true (.cons false (.cons false .nil)))))),
  .tempAnd (.cons false (.cons false (.cons false (.cons true (.cons false (.cons true .nil))))))
    (.cons false (.cons false (.cons false (.cons true (.cons false (.cons false .nil)))))) (.cons
    false (.cons true (.cons true (.cons false (.cons false (.cons false .nil)))))),
  .x (.cons false (.cons false (.cons false (.cons true (.cons false (.cons false .nil)))))),
  .x (.cons false (.cons false (.cons false (.cons true (.cons false (.cons true .nil)))))),
  .x (.cons false (.cons false (.cons false (.cons true (.cons true (.cons true .nil)))))),
  .cnot (.cons false (.cons true (.cons true (.cons false (.cons false (.cons false .nil))))))
    (.cons false (.cons false (.cons false (.cons true (.cons true (.cons true .nil)))))),
  .cnot (.cons false (.cons false (.cons false (.cons true (.cons true (.cons false .nil))))))
    (.cons false (.cons false (.cons false (.cons true (.cons false (.cons false .nil)))))),
  .cnot (.cons false (.cons true (.cons true (.cons false (.cons false (.cons false .nil))))))
    (.cons false (.cons false (.cons false (.cons true (.cons false (.cons false .nil)))))),
  .tempAnd (.cons false (.cons false (.cons false (.cons true (.cons true (.cons true .nil))))))
    (.cons false (.cons false (.cons false (.cons true (.cons false (.cons false .nil)))))) (.cons
    false (.cons true (.cons true (.cons false (.cons false (.cons true .nil)))))),
  .cnot (.cons false (.cons true (.cons true (.cons false (.cons false (.cons false .nil))))))
    (.cons false (.cons false (.cons false (.cons true (.cons false (.cons false .nil)))))),
  .cnot (.cons false (.cons false (.cons false (.cons true (.cons true (.cons false .nil))))))
    (.cons false (.cons false (.cons false (.cons true (.cons false (.cons false .nil)))))),
  .cnot (.cons false (.cons true (.cons true (.cons false (.cons false (.cons false .nil))))))
    (.cons false (.cons false (.cons false (.cons true (.cons true (.cons true .nil)))))),
  .x (.cons false (.cons false (.cons false (.cons true (.cons true (.cons true .nil)))))),
  .cnot (.cons false (.cons false (.cons false (.cons true (.cons true (.cons true .nil)))))) (.cons
    false (.cons false (.cons false (.cons true (.cons true (.cons false .nil)))))),
  .cnot (.cons false (.cons true (.cons true (.cons false (.cons false (.cons false .nil))))))
    (.cons false (.cons false (.cons false (.cons true (.cons true (.cons false .nil)))))),
  .cnot (.cons false (.cons false (.cons false (.cons true (.cons false (.cons true .nil))))))
    (.cons false (.cons false (.cons false (.cons true (.cons false (.cons false .nil)))))),
  .cnot (.cons false (.cons true (.cons true (.cons false (.cons false (.cons true .nil)))))) (.cons
    false (.cons false (.cons false (.cons true (.cons false (.cons false .nil)))))),
  .tempAnd (.cons false (.cons false (.cons false (.cons true (.cons true (.cons false .nil))))))
    (.cons false (.cons false (.cons false (.cons true (.cons false (.cons false .nil)))))) (.cons
    false (.cons true (.cons true (.cons false (.cons true (.cons false .nil)))))),
  .cnot (.cons false (.cons true (.cons true (.cons false (.cons false (.cons true .nil)))))) (.cons
    false (.cons false (.cons false (.cons true (.cons false (.cons false .nil)))))),
  .cnot (.cons false (.cons false (.cons false (.cons true (.cons false (.cons true .nil))))))
    (.cons false (.cons false (.cons false (.cons true (.cons false (.cons false .nil)))))),
  .cnot (.cons false (.cons true (.cons true (.cons false (.cons false (.cons false .nil))))))
    (.cons false (.cons false (.cons false (.cons true (.cons true (.cons false .nil)))))),
  .cnot (.cons false (.cons false (.cons false (.cons true (.cons true (.cons true .nil)))))) (.cons
    false (.cons false (.cons false (.cons true (.cons true (.cons false .nil)))))),
  .x (.cons false (.cons true (.cons true (.cons false (.cons true (.cons false .nil)))))),
  .cnot (.cons false (.cons false (.cons false (.cons true (.cons true (.cons true .nil)))))) (.cons
    false (.cons true (.cons true (.cons false (.cons true (.cons false .nil)))))),
  .cnot (.cons false (.cons false (.cons false (.cons true (.cons false (.cons true .nil))))))
    (.cons false (.cons true (.cons false (.cons true (.cons true (.cons true .nil)))))),
  .cnot (.cons false (.cons false (.cons false (.cons true (.cons true (.cons true .nil)))))) (.cons
    false (.cons true (.cons false (.cons true (.cons true (.cons true .nil)))))),
  .tempAnd (.cons false (.cons true (.cons true (.cons false (.cons true (.cons false .nil))))))
    (.cons false (.cons true (.cons false (.cons true (.cons true (.cons true .nil)))))) (.cons
    false (.cons true (.cons true (.cons false (.cons true (.cons true .nil))))))
]
def localSqAx0Ph1B : List LocalStep := [
  .cnot (.cons false (.cons false (.cons false (.cons true (.cons true (.cons true .nil)))))) (.cons
    false (.cons true (.cons false (.cons true (.cons true (.cons true .nil)))))),
  .cnot (.cons false (.cons false (.cons false (.cons true (.cons false (.cons true .nil))))))
    (.cons false (.cons true (.cons false (.cons true (.cons true (.cons true .nil)))))),
  .cnot (.cons false (.cons false (.cons false (.cons true (.cons true (.cons true .nil)))))) (.cons
    false (.cons true (.cons true (.cons false (.cons true (.cons false .nil)))))),
  .x (.cons false (.cons true (.cons true (.cons false (.cons true (.cons false .nil)))))),
  .cnot (.cons false (.cons true (.cons true (.cons false (.cons true (.cons true .nil)))))) (.cons
    false (.cons true (.cons true (.cons false (.cons true (.cons false .nil)))))),
  .cnot (.cons false (.cons true (.cons true (.cons false (.cons true (.cons true .nil)))))) (.cons
    false (.cons true (.cons true (.cons false (.cons false (.cons true .nil)))))),
  .cnot (.cons false (.cons true (.cons true (.cons false (.cons true (.cons true .nil)))))) (.cons
    false (.cons true (.cons false (.cons true (.cons true (.cons true .nil)))))),
  .cnot (.cons false (.cons true (.cons true (.cons false (.cons true (.cons true .nil)))))) (.cons
    false (.cons false (.cons false (.cons true (.cons true (.cons true .nil)))))),
  .cnot (.cons false (.cons true (.cons true (.cons false (.cons true (.cons false .nil)))))) (.cons
    false (.cons true (.cons true (.cons false (.cons true (.cons true .nil)))))),
  .cnot (.cons false (.cons true (.cons true (.cons false (.cons true (.cons false .nil)))))) (.cons
    false (.cons true (.cons true (.cons false (.cons false (.cons true .nil)))))),
  .cnot (.cons false (.cons true (.cons true (.cons false (.cons true (.cons false .nil)))))) (.cons
    false (.cons true (.cons true (.cons false (.cons false (.cons false .nil)))))),
  .cnot (.cons false (.cons true (.cons true (.cons false (.cons true (.cons false .nil)))))) (.cons
    false (.cons true (.cons false (.cons true (.cons true (.cons true .nil)))))),
  .cnot (.cons false (.cons true (.cons true (.cons false (.cons true (.cons false .nil)))))) (.cons
    false (.cons false (.cons false (.cons true (.cons true (.cons true .nil)))))),
  .cnot (.cons false (.cons true (.cons true (.cons false (.cons true (.cons false .nil)))))) (.cons
    false (.cons false (.cons false (.cons true (.cons false (.cons true .nil)))))),
  .cnot (.cons false (.cons true (.cons true (.cons false (.cons false (.cons true .nil)))))) (.cons
    false (.cons true (.cons true (.cons false (.cons true (.cons false .nil)))))),
  .cnot (.cons false (.cons true (.cons true (.cons false (.cons false (.cons true .nil)))))) (.cons
    false (.cons true (.cons true (.cons false (.cons false (.cons false .nil)))))),
  .cnot (.cons false (.cons true (.cons true (.cons false (.cons false (.cons false .nil))))))
    (.cons false (.cons true (.cons true (.cons false (.cons true (.cons true .nil)))))),
  .cnot (.cons false (.cons true (.cons true (.cons false (.cons false (.cons false .nil))))))
    (.cons false (.cons true (.cons true (.cons false (.cons true (.cons false .nil)))))),
  .cnot (.cons false (.cons true (.cons true (.cons false (.cons false (.cons false .nil))))))
    (.cons false (.cons false (.cons false (.cons true (.cons true (.cons true .nil)))))),
  .cnot (.cons false (.cons true (.cons true (.cons false (.cons false (.cons false .nil))))))
    (.cons false (.cons false (.cons false (.cons true (.cons true (.cons false .nil)))))),
  .cnot (.cons false (.cons true (.cons true (.cons false (.cons false (.cons true .nil)))))) (.cons
    false (.cons true (.cons true (.cons false (.cons false (.cons false .nil)))))),
  .cnot (.cons false (.cons true (.cons true (.cons false (.cons false (.cons false .nil))))))
    (.cons false (.cons true (.cons true (.cons false (.cons false (.cons true .nil)))))),
  .cnot (.cons false (.cons true (.cons true (.cons false (.cons false (.cons true .nil)))))) (.cons
    false (.cons true (.cons true (.cons false (.cons false (.cons false .nil)))))),
  .cnot (.cons false (.cons true (.cons false (.cons true (.cons true (.cons true .nil)))))) (.cons
    false (.cons false (.cons false (.cons true (.cons true (.cons false .nil)))))),
  .cnot (.cons false (.cons true (.cons true (.cons false (.cons false (.cons true .nil)))))) (.cons
    false (.cons true (.cons false (.cons true (.cons true (.cons true .nil)))))),
  .cnot (.cons false (.cons true (.cons false (.cons true (.cons true (.cons true .nil)))))) (.cons
    false (.cons true (.cons true (.cons false (.cons false (.cons true .nil)))))),
  .cnot (.cons false (.cons true (.cons true (.cons false (.cons false (.cons true .nil)))))) (.cons
    false (.cons true (.cons false (.cons true (.cons true (.cons true .nil)))))),
  .cnot (.cons false (.cons false (.cons false (.cons true (.cons true (.cons true .nil)))))) (.cons
    false (.cons true (.cons true (.cons false (.cons true (.cons true .nil)))))),
  .cnot (.cons false (.cons true (.cons true (.cons false (.cons true (.cons false .nil)))))) (.cons
    false (.cons false (.cons false (.cons true (.cons true (.cons true .nil)))))),
  .cnot (.cons false (.cons false (.cons false (.cons true (.cons true (.cons true .nil)))))) (.cons
    false (.cons true (.cons true (.cons false (.cons true (.cons false .nil)))))),
  .cnot (.cons false (.cons true (.cons true (.cons false (.cons true (.cons false .nil)))))) (.cons
    false (.cons false (.cons false (.cons true (.cons true (.cons true .nil)))))),
  .cnot (.cons false (.cons false (.cons false (.cons true (.cons true (.cons false .nil))))))
    (.cons false (.cons true (.cons true (.cons false (.cons true (.cons false .nil)))))),
  .cnot (.cons false (.cons false (.cons false (.cons true (.cons true (.cons false .nil))))))
    (.cons false (.cons true (.cons false (.cons true (.cons true (.cons true .nil)))))),
  .cnot (.cons false (.cons false (.cons false (.cons true (.cons true (.cons true .nil)))))) (.cons
    false (.cons false (.cons false (.cons true (.cons true (.cons false .nil)))))),
  .cnot (.cons false (.cons false (.cons false (.cons true (.cons true (.cons false .nil))))))
    (.cons false (.cons false (.cons false (.cons true (.cons true (.cons true .nil)))))),
  .cnot (.cons false (.cons false (.cons false (.cons true (.cons true (.cons true .nil)))))) (.cons
    false (.cons false (.cons false (.cons true (.cons true (.cons false .nil)))))),
  .cnot (.cons false (.cons false (.cons false (.cons true (.cons false (.cons true .nil))))))
    (.cons false (.cons true (.cons true (.cons false (.cons false (.cons true .nil)))))),
  .cnot (.cons false (.cons false (.cons false (.cons true (.cons false (.cons true .nil))))))
    (.cons false (.cons false (.cons false (.cons true (.cons true (.cons false .nil)))))),
  .cnot (.cons false (.cons false (.cons false (.cons true (.cons false (.cons false .nil))))))
    (.cons false (.cons true (.cons true (.cons false (.cons false (.cons false .nil)))))),
  .cnot (.cons false (.cons false (.cons false (.cons true (.cons false (.cons false .nil))))))
    (.cons false (.cons false (.cons false (.cons true (.cons true (.cons false .nil)))))),
  .x (.cons false (.cons false (.cons false (.cons true (.cons false (.cons true .nil)))))),
  .x (.cons false (.cons false (.cons false (.cons true (.cons true (.cons true .nil)))))),
  .x (.cons false (.cons true (.cons false (.cons true (.cons true (.cons true .nil)))))),
  .x (.cons false (.cons true (.cons true (.cons false (.cons true (.cons false .nil))))))
]
def localSqAx0Ph2 : List LocalStep := [
  .tempAnd (.cons false (.cons false (.cons false (.cons false (.cons false (.cons false .nil))))))
    (.cons false (.cons false (.cons false (.cons true (.cons true (.cons true .nil)))))) (.cons
    false (.cons false (.cons true (.cons false (.cons false (.cons false .nil)))))),
  .tempAnd (.cons false (.cons false (.cons false (.cons false (.cons false (.cons true .nil))))))
    (.cons false (.cons false (.cons false (.cons true (.cons true (.cons false .nil)))))) (.cons
    false (.cons false (.cons true (.cons false (.cons false (.cons true .nil)))))),
  .tempAnd (.cons false (.cons false (.cons false (.cons false (.cons true (.cons false .nil))))))
    (.cons false (.cons false (.cons false (.cons true (.cons false (.cons true .nil)))))) (.cons
    false (.cons false (.cons true (.cons false (.cons true (.cons false .nil)))))),
  .tempAnd (.cons false (.cons false (.cons false (.cons false (.cons true (.cons true .nil))))))
    (.cons false (.cons false (.cons false (.cons true (.cons false (.cons false .nil)))))) (.cons
    false (.cons false (.cons true (.cons false (.cons true (.cons true .nil)))))),
  .tempAnd (.cons false (.cons false (.cons false (.cons false (.cons false (.cons true .nil))))))
    (.cons false (.cons false (.cons false (.cons true (.cons true (.cons true .nil)))))) (.cons
    false (.cons false (.cons true (.cons true (.cons false (.cons false .nil)))))),
  .tempAnd (.cons false (.cons false (.cons false (.cons false (.cons true (.cons false .nil))))))
    (.cons false (.cons false (.cons false (.cons true (.cons true (.cons false .nil)))))) (.cons
    false (.cons false (.cons true (.cons true (.cons false (.cons true .nil))))))
]
def localSqAx1Ph1A : List LocalStep := [
  .tempAnd (.cons false (.cons false (.cons false (.cons false (.cons false (.cons false .nil))))))
    (.cons false (.cons false (.cons false (.cons true (.cons false (.cons false .nil)))))) (.cons
    false (.cons false (.cons true (.cons false (.cons false (.cons false .nil)))))),
  .tempAnd (.cons false (.cons false (.cons false (.cons false (.cons false (.cons false .nil))))))
    (.cons false (.cons false (.cons false (.cons true (.cons false (.cons true .nil)))))) (.cons
    false (.cons false (.cons true (.cons false (.cons false (.cons true .nil)))))),
  .tempAnd (.cons false (.cons false (.cons false (.cons false (.cons false (.cons true .nil))))))
    (.cons false (.cons false (.cons false (.cons true (.cons false (.cons false .nil)))))) (.cons
    false (.cons false (.cons true (.cons false (.cons true (.cons false .nil)))))),
  .tempAnd (.cons false (.cons false (.cons false (.cons false (.cons false (.cons false .nil))))))
    (.cons false (.cons false (.cons false (.cons true (.cons true (.cons false .nil)))))) (.cons
    false (.cons false (.cons true (.cons false (.cons true (.cons true .nil)))))),
  .tempAnd (.cons false (.cons false (.cons false (.cons false (.cons false (.cons true .nil))))))
    (.cons false (.cons false (.cons false (.cons true (.cons false (.cons true .nil)))))) (.cons
    false (.cons false (.cons true (.cons true (.cons false (.cons false .nil)))))),
  .tempAnd (.cons false (.cons false (.cons false (.cons false (.cons true (.cons false .nil))))))
    (.cons false (.cons false (.cons false (.cons true (.cons false (.cons false .nil)))))) (.cons
    false (.cons false (.cons true (.cons true (.cons false (.cons true .nil)))))),
  .x (.cons false (.cons false (.cons false (.cons false (.cons true (.cons true .nil)))))),
  .x (.cons false (.cons false (.cons false (.cons false (.cons true (.cons false .nil)))))),
  .tempAnd (.cons false (.cons false (.cons false (.cons false (.cons true (.cons true .nil))))))
    (.cons false (.cons false (.cons false (.cons false (.cons true (.cons false .nil)))))) (.cons
    false (.cons false (.cons true (.cons true (.cons true (.cons false .nil)))))),
  .x (.cons false (.cons false (.cons false (.cons false (.cons true (.cons false .nil)))))),
  .x (.cons false (.cons false (.cons false (.cons false (.cons true (.cons true .nil)))))),
  .x (.cons false (.cons false (.cons false (.cons false (.cons false (.cons true .nil)))))),
  .x (.cons false (.cons false (.cons false (.cons false (.cons false (.cons false .nil)))))),
  .tempAnd (.cons false (.cons false (.cons false (.cons false (.cons false (.cons true .nil))))))
    (.cons false (.cons false (.cons false (.cons false (.cons false (.cons false .nil)))))) (.cons
    false (.cons false (.cons true (.cons true (.cons true (.cons true .nil)))))),
  .x (.cons false (.cons false (.cons false (.cons false (.cons false (.cons false .nil)))))),
  .x (.cons false (.cons false (.cons false (.cons false (.cons false (.cons true .nil)))))),
  .x (.cons false (.cons false (.cons false (.cons false (.cons true (.cons true .nil)))))),
  .cnot (.cons false (.cons false (.cons true (.cons true (.cons true (.cons true .nil)))))) (.cons
    false (.cons false (.cons false (.cons false (.cons true (.cons true .nil)))))),
  .cnot (.cons false (.cons false (.cons false (.cons false (.cons true (.cons false .nil))))))
    (.cons false (.cons false (.cons false (.cons false (.cons false (.cons false .nil)))))),
  .cnot (.cons false (.cons false (.cons true (.cons true (.cons true (.cons true .nil)))))) (.cons
    false (.cons false (.cons false (.cons false (.cons false (.cons false .nil)))))),
  .tempAnd (.cons false (.cons false (.cons false (.cons false (.cons true (.cons true .nil))))))
    (.cons false (.cons false (.cons false (.cons false (.cons false (.cons false .nil)))))) (.cons
    false (.cons true (.cons false (.cons false (.cons false (.cons false .nil)))))),
  .cnot (.cons false (.cons false (.cons true (.cons true (.cons true (.cons true .nil)))))) (.cons
    false (.cons false (.cons false (.cons false (.cons false (.cons false .nil)))))),
  .cnot (.cons false (.cons false (.cons false (.cons false (.cons true (.cons false .nil))))))
    (.cons false (.cons false (.cons false (.cons false (.cons false (.cons false .nil)))))),
  .cnot (.cons false (.cons false (.cons true (.cons true (.cons true (.cons true .nil)))))) (.cons
    false (.cons false (.cons false (.cons false (.cons true (.cons true .nil)))))),
  .x (.cons false (.cons false (.cons false (.cons false (.cons true (.cons true .nil)))))),
  .cnot (.cons false (.cons false (.cons false (.cons false (.cons true (.cons true .nil))))))
    (.cons false (.cons false (.cons false (.cons false (.cons true (.cons false .nil)))))),
  .cnot (.cons false (.cons false (.cons true (.cons true (.cons true (.cons true .nil)))))) (.cons
    false (.cons false (.cons false (.cons false (.cons true (.cons false .nil)))))),
  .cnot (.cons false (.cons false (.cons false (.cons false (.cons false (.cons true .nil))))))
    (.cons false (.cons false (.cons false (.cons false (.cons false (.cons false .nil)))))),
  .cnot (.cons false (.cons true (.cons false (.cons false (.cons false (.cons false .nil))))))
    (.cons false (.cons false (.cons false (.cons false (.cons false (.cons false .nil)))))),
  .tempAnd (.cons false (.cons false (.cons false (.cons false (.cons true (.cons false .nil))))))
    (.cons false (.cons false (.cons false (.cons false (.cons false (.cons false .nil)))))) (.cons
    false (.cons true (.cons false (.cons false (.cons false (.cons true .nil)))))),
  .cnot (.cons false (.cons true (.cons false (.cons false (.cons false (.cons false .nil))))))
    (.cons false (.cons false (.cons false (.cons false (.cons false (.cons false .nil)))))),
  .cnot (.cons false (.cons false (.cons false (.cons false (.cons false (.cons true .nil))))))
    (.cons false (.cons false (.cons false (.cons false (.cons false (.cons false .nil)))))),
  .cnot (.cons false (.cons false (.cons true (.cons true (.cons true (.cons true .nil)))))) (.cons
    false (.cons false (.cons false (.cons false (.cons true (.cons false .nil)))))),
  .cnot (.cons false (.cons false (.cons false (.cons false (.cons true (.cons true .nil))))))
    (.cons false (.cons false (.cons false (.cons false (.cons true (.cons false .nil)))))),
  .x (.cons false (.cons true (.cons false (.cons false (.cons false (.cons true .nil)))))),
  .cnot (.cons false (.cons false (.cons false (.cons false (.cons true (.cons true .nil))))))
    (.cons false (.cons true (.cons false (.cons false (.cons false (.cons true .nil)))))),
  .cnot (.cons false (.cons false (.cons false (.cons false (.cons false (.cons true .nil))))))
    (.cons false (.cons false (.cons true (.cons true (.cons true (.cons false .nil)))))),
  .cnot (.cons false (.cons false (.cons false (.cons false (.cons true (.cons true .nil))))))
    (.cons false (.cons false (.cons true (.cons true (.cons true (.cons false .nil)))))),
  .tempAnd (.cons false (.cons true (.cons false (.cons false (.cons false (.cons true .nil))))))
    (.cons false (.cons false (.cons true (.cons true (.cons true (.cons false .nil)))))) (.cons
    false (.cons true (.cons false (.cons false (.cons true (.cons false .nil)))))),
  .cnot (.cons false (.cons false (.cons false (.cons false (.cons true (.cons true .nil))))))
    (.cons false (.cons false (.cons true (.cons true (.cons true (.cons false .nil)))))),
  .cnot (.cons false (.cons false (.cons false (.cons false (.cons false (.cons true .nil))))))
    (.cons false (.cons false (.cons true (.cons true (.cons true (.cons false .nil)))))),
  .cnot (.cons false (.cons false (.cons false (.cons false (.cons true (.cons true .nil))))))
    (.cons false (.cons true (.cons false (.cons false (.cons false (.cons true .nil)))))),
  .x (.cons false (.cons true (.cons false (.cons false (.cons false (.cons true .nil)))))),
  .cnot (.cons false (.cons true (.cons false (.cons false (.cons true (.cons false .nil))))))
    (.cons false (.cons true (.cons false (.cons false (.cons false (.cons true .nil)))))),
  .cnot (.cons false (.cons true (.cons false (.cons false (.cons true (.cons false .nil))))))
    (.cons false (.cons true (.cons false (.cons false (.cons false (.cons false .nil)))))),
  .cnot (.cons false (.cons true (.cons false (.cons false (.cons true (.cons false .nil))))))
    (.cons false (.cons false (.cons true (.cons true (.cons true (.cons false .nil)))))),
  .cnot (.cons false (.cons true (.cons false (.cons false (.cons true (.cons false .nil))))))
    (.cons false (.cons false (.cons false (.cons false (.cons true (.cons true .nil)))))),
  .cnot (.cons false (.cons true (.cons false (.cons false (.cons false (.cons true .nil))))))
    (.cons false (.cons true (.cons false (.cons false (.cons true (.cons false .nil)))))),
  .cnot (.cons false (.cons true (.cons false (.cons false (.cons false (.cons true .nil))))))
    (.cons false (.cons true (.cons false (.cons false (.cons false (.cons false .nil)))))),
  .cnot (.cons false (.cons true (.cons false (.cons false (.cons false (.cons true .nil))))))
    (.cons false (.cons false (.cons true (.cons true (.cons true (.cons true .nil)))))),
  .cnot (.cons false (.cons true (.cons false (.cons false (.cons false (.cons true .nil))))))
    (.cons false (.cons false (.cons true (.cons true (.cons true (.cons false .nil)))))),
  .cnot (.cons false (.cons true (.cons false (.cons false (.cons false (.cons true .nil))))))
    (.cons false (.cons false (.cons false (.cons false (.cons true (.cons true .nil)))))),
  .cnot (.cons false (.cons true (.cons false (.cons false (.cons false (.cons true .nil))))))
    (.cons false (.cons false (.cons false (.cons false (.cons false (.cons true .nil)))))),
  .cnot (.cons false (.cons true (.cons false (.cons false (.cons false (.cons false .nil))))))
    (.cons false (.cons true (.cons false (.cons false (.cons false (.cons true .nil)))))),
  .cnot (.cons false (.cons true (.cons false (.cons false (.cons false (.cons false .nil))))))
    (.cons false (.cons false (.cons true (.cons true (.cons true (.cons true .nil)))))),
  .cnot (.cons false (.cons false (.cons true (.cons true (.cons true (.cons true .nil)))))) (.cons
    false (.cons true (.cons false (.cons false (.cons true (.cons false .nil)))))),
  .cnot (.cons false (.cons false (.cons true (.cons true (.cons true (.cons true .nil)))))) (.cons
    false (.cons true (.cons false (.cons false (.cons false (.cons true .nil)))))),
  .cnot (.cons false (.cons false (.cons true (.cons true (.cons true (.cons true .nil)))))) (.cons
    false (.cons false (.cons false (.cons false (.cons true (.cons true .nil)))))),
  .cnot (.cons false (.cons false (.cons true (.cons true (.cons true (.cons true .nil)))))) (.cons
    false (.cons false (.cons false (.cons false (.cons true (.cons false .nil)))))),
  .cnot (.cons false (.cons true (.cons false (.cons false (.cons false (.cons false .nil))))))
    (.cons false (.cons false (.cons true (.cons true (.cons true (.cons true .nil)))))),
  .cnot (.cons false (.cons false (.cons true (.cons true (.cons true (.cons true .nil)))))) (.cons
    false (.cons true (.cons false (.cons false (.cons false (.cons false .nil)))))),
  .cnot (.cons false (.cons true (.cons false (.cons false (.cons false (.cons false .nil))))))
    (.cons false (.cons false (.cons true (.cons true (.cons true (.cons true .nil)))))),
  .cnot (.cons false (.cons false (.cons true (.cons true (.cons true (.cons false .nil)))))) (.cons
    false (.cons false (.cons false (.cons false (.cons true (.cons false .nil)))))),
  .cnot (.cons false (.cons true (.cons false (.cons false (.cons false (.cons false .nil))))))
    (.cons false (.cons false (.cons true (.cons true (.cons true (.cons false .nil)))))),
  .cnot (.cons false (.cons false (.cons true (.cons true (.cons true (.cons false .nil)))))) (.cons
    false (.cons true (.cons false (.cons false (.cons false (.cons false .nil)))))),
  .cnot (.cons false (.cons true (.cons false (.cons false (.cons false (.cons false .nil))))))
    (.cons false (.cons false (.cons true (.cons true (.cons true (.cons false .nil)))))),
  .cnot (.cons false (.cons false (.cons false (.cons false (.cons true (.cons true .nil))))))
    (.cons false (.cons true (.cons false (.cons false (.cons true (.cons false .nil)))))),
  .cnot (.cons false (.cons true (.cons false (.cons false (.cons false (.cons true .nil))))))
    (.cons false (.cons false (.cons false (.cons false (.cons true (.cons true .nil)))))),
  .cnot (.cons false (.cons false (.cons false (.cons false (.cons true (.cons true .nil))))))
    (.cons false (.cons true (.cons false (.cons false (.cons false (.cons true .nil)))))),
  .cnot (.cons false (.cons true (.cons false (.cons false (.cons false (.cons true .nil))))))
    (.cons false (.cons false (.cons false (.cons false (.cons true (.cons true .nil)))))),
  .cnot (.cons false (.cons false (.cons false (.cons false (.cons true (.cons false .nil))))))
    (.cons false (.cons true (.cons false (.cons false (.cons false (.cons true .nil)))))),
  .cnot (.cons false (.cons false (.cons false (.cons false (.cons true (.cons false .nil))))))
    (.cons false (.cons false (.cons true (.cons true (.cons true (.cons false .nil)))))),
  .cnot (.cons false (.cons false (.cons false (.cons false (.cons true (.cons true .nil))))))
    (.cons false (.cons false (.cons false (.cons false (.cons true (.cons false .nil)))))),
  .cnot (.cons false (.cons false (.cons false (.cons false (.cons true (.cons false .nil))))))
    (.cons false (.cons false (.cons false (.cons false (.cons true (.cons true .nil)))))),
  .cnot (.cons false (.cons false (.cons false (.cons false (.cons true (.cons true .nil))))))
    (.cons false (.cons false (.cons false (.cons false (.cons true (.cons false .nil)))))),
  .cnot (.cons false (.cons false (.cons false (.cons false (.cons false (.cons true .nil))))))
    (.cons false (.cons true (.cons false (.cons false (.cons false (.cons false .nil)))))),
  .cnot (.cons false (.cons false (.cons false (.cons false (.cons false (.cons true .nil))))))
    (.cons false (.cons false (.cons false (.cons false (.cons true (.cons false .nil)))))),
  .cnot (.cons false (.cons false (.cons false (.cons false (.cons false (.cons false .nil))))))
    (.cons false (.cons false (.cons true (.cons true (.cons true (.cons true .nil)))))),
  .cnot (.cons false (.cons false (.cons false (.cons false (.cons false (.cons false .nil))))))
    (.cons false (.cons false (.cons false (.cons false (.cons true (.cons false .nil)))))),
  .x (.cons false (.cons false (.cons false (.cons false (.cons false (.cons true .nil)))))),
  .x (.cons false (.cons false (.cons false (.cons false (.cons true (.cons true .nil)))))),
  .x (.cons false (.cons false (.cons true (.cons true (.cons true (.cons false .nil)))))),
  .x (.cons false (.cons true (.cons false (.cons false (.cons false (.cons true .nil)))))),
  .x (.cons false (.cons false (.cons false (.cons true (.cons true (.cons true .nil)))))),
  .x (.cons false (.cons false (.cons false (.cons true (.cons true (.cons false .nil)))))),
  .tempAnd (.cons false (.cons false (.cons false (.cons true (.cons true (.cons true .nil))))))
    (.cons false (.cons false (.cons false (.cons true (.cons true (.cons false .nil)))))) (.cons
    false (.cons true (.cons false (.cons false (.cons true (.cons true .nil)))))),
  .x (.cons false (.cons false (.cons false (.cons true (.cons true (.cons false .nil)))))),
  .x (.cons false (.cons false (.cons false (.cons true (.cons true (.cons true .nil)))))),
  .x (.cons false (.cons false (.cons false (.cons true (.cons false (.cons true .nil)))))),
  .x (.cons false (.cons false (.cons false (.cons true (.cons false (.cons false .nil)))))),
  .tempAnd (.cons false (.cons false (.cons false (.cons true (.cons false (.cons true .nil))))))
    (.cons false (.cons false (.cons false (.cons true (.cons false (.cons false .nil)))))) (.cons
    false (.cons true (.cons false (.cons true (.cons false (.cons false .nil)))))),
  .x (.cons false (.cons false (.cons false (.cons true (.cons false (.cons false .nil)))))),
  .x (.cons false (.cons false (.cons false (.cons true (.cons false (.cons true .nil)))))),
  .x (.cons false (.cons false (.cons false (.cons true (.cons true (.cons true .nil)))))),
  .cnot (.cons false (.cons true (.cons false (.cons true (.cons false (.cons false .nil))))))
    (.cons false (.cons false (.cons false (.cons true (.cons true (.cons true .nil)))))),
  .cnot (.cons false (.cons false (.cons false (.cons true (.cons true (.cons false .nil))))))
    (.cons false (.cons false (.cons false (.cons true (.cons false (.cons false .nil)))))),
  .cnot (.cons false (.cons true (.cons false (.cons true (.cons false (.cons false .nil))))))
    (.cons false (.cons false (.cons false (.cons true (.cons false (.cons false .nil)))))),
  .tempAnd (.cons false (.cons false (.cons false (.cons true (.cons true (.cons true .nil))))))
    (.cons false (.cons false (.cons false (.cons true (.cons false (.cons false .nil)))))) (.cons
    false (.cons true (.cons false (.cons true (.cons false (.cons true .nil)))))),
  .cnot (.cons false (.cons true (.cons false (.cons true (.cons false (.cons false .nil))))))
    (.cons false (.cons false (.cons false (.cons true (.cons false (.cons false .nil)))))),
  .cnot (.cons false (.cons false (.cons false (.cons true (.cons true (.cons false .nil))))))
    (.cons false (.cons false (.cons false (.cons true (.cons false (.cons false .nil)))))),
  .cnot (.cons false (.cons true (.cons false (.cons true (.cons false (.cons false .nil))))))
    (.cons false (.cons false (.cons false (.cons true (.cons true (.cons true .nil)))))),
  .x (.cons false (.cons false (.cons false (.cons true (.cons true (.cons true .nil)))))),
  .cnot (.cons false (.cons false (.cons false (.cons true (.cons true (.cons true .nil)))))) (.cons
    false (.cons false (.cons false (.cons true (.cons true (.cons false .nil)))))),
  .cnot (.cons false (.cons true (.cons false (.cons true (.cons false (.cons false .nil))))))
    (.cons false (.cons false (.cons false (.cons true (.cons true (.cons false .nil)))))),
  .cnot (.cons false (.cons false (.cons false (.cons true (.cons false (.cons true .nil))))))
    (.cons false (.cons false (.cons false (.cons true (.cons false (.cons false .nil)))))),
  .cnot (.cons false (.cons true (.cons false (.cons true (.cons false (.cons true .nil)))))) (.cons
    false (.cons false (.cons false (.cons true (.cons false (.cons false .nil)))))),
  .tempAnd (.cons false (.cons false (.cons false (.cons true (.cons true (.cons false .nil))))))
    (.cons false (.cons false (.cons false (.cons true (.cons false (.cons false .nil)))))) (.cons
    false (.cons true (.cons false (.cons true (.cons true (.cons false .nil)))))),
  .cnot (.cons false (.cons true (.cons false (.cons true (.cons false (.cons true .nil)))))) (.cons
    false (.cons false (.cons false (.cons true (.cons false (.cons false .nil)))))),
  .cnot (.cons false (.cons false (.cons false (.cons true (.cons false (.cons true .nil))))))
    (.cons false (.cons false (.cons false (.cons true (.cons false (.cons false .nil)))))),
  .cnot (.cons false (.cons true (.cons false (.cons true (.cons false (.cons false .nil))))))
    (.cons false (.cons false (.cons false (.cons true (.cons true (.cons false .nil)))))),
  .cnot (.cons false (.cons false (.cons false (.cons true (.cons true (.cons true .nil)))))) (.cons
    false (.cons false (.cons false (.cons true (.cons true (.cons false .nil)))))),
  .x (.cons false (.cons true (.cons false (.cons true (.cons true (.cons false .nil)))))),
  .cnot (.cons false (.cons false (.cons false (.cons true (.cons true (.cons true .nil)))))) (.cons
    false (.cons true (.cons false (.cons true (.cons true (.cons false .nil)))))),
  .cnot (.cons false (.cons false (.cons false (.cons true (.cons false (.cons true .nil))))))
    (.cons false (.cons true (.cons false (.cons false (.cons true (.cons true .nil)))))),
  .cnot (.cons false (.cons false (.cons false (.cons true (.cons true (.cons true .nil)))))) (.cons
    false (.cons true (.cons false (.cons false (.cons true (.cons true .nil)))))),
  .tempAnd (.cons false (.cons true (.cons false (.cons true (.cons true (.cons false .nil))))))
    (.cons false (.cons true (.cons false (.cons false (.cons true (.cons true .nil)))))) (.cons
    false (.cons true (.cons false (.cons true (.cons true (.cons true .nil)))))),
  .cnot (.cons false (.cons false (.cons false (.cons true (.cons true (.cons true .nil)))))) (.cons
    false (.cons true (.cons false (.cons false (.cons true (.cons true .nil)))))),
  .cnot (.cons false (.cons false (.cons false (.cons true (.cons false (.cons true .nil))))))
    (.cons false (.cons true (.cons false (.cons false (.cons true (.cons true .nil)))))),
  .cnot (.cons false (.cons false (.cons false (.cons true (.cons true (.cons true .nil)))))) (.cons
    false (.cons true (.cons false (.cons true (.cons true (.cons false .nil)))))),
  .x (.cons false (.cons true (.cons false (.cons true (.cons true (.cons false .nil))))))
]
def localSqAx1Ph1B : List LocalStep := [
  .cnot (.cons false (.cons true (.cons false (.cons true (.cons true (.cons true .nil)))))) (.cons
    false (.cons true (.cons false (.cons true (.cons true (.cons false .nil)))))),
  .cnot (.cons false (.cons true (.cons false (.cons true (.cons true (.cons true .nil)))))) (.cons
    false (.cons true (.cons false (.cons true (.cons false (.cons true .nil)))))),
  .cnot (.cons false (.cons true (.cons false (.cons true (.cons true (.cons true .nil)))))) (.cons
    false (.cons true (.cons false (.cons false (.cons true (.cons true .nil)))))),
  .cnot (.cons false (.cons true (.cons false (.cons true (.cons true (.cons true .nil)))))) (.cons
    false (.cons false (.cons false (.cons true (.cons true (.cons true .nil)))))),
  .cnot (.cons false (.cons true (.cons false (.cons true (.cons true (.cons false .nil)))))) (.cons
    false (.cons true (.cons false (.cons true (.cons true (.cons true .nil)))))),
  .cnot (.cons false (.cons true (.cons false (.cons true (.cons true (.cons false .nil)))))) (.cons
    false (.cons true (.cons false (.cons true (.cons false (.cons true .nil)))))),
  .cnot (.cons false (.cons true (.cons false (.cons true (.cons true (.cons false .nil)))))) (.cons
    false (.cons true (.cons false (.cons true (.cons false (.cons false .nil)))))),
  .cnot (.cons false (.cons true (.cons false (.cons true (.cons true (.cons false .nil)))))) (.cons
    false (.cons true (.cons false (.cons false (.cons true (.cons true .nil)))))),
  .cnot (.cons false (.cons true (.cons false (.cons true (.cons true (.cons false .nil)))))) (.cons
    false (.cons false (.cons false (.cons true (.cons true (.cons true .nil)))))),
  .cnot (.cons false (.cons true (.cons false (.cons true (.cons true (.cons false .nil)))))) (.cons
    false (.cons false (.cons false (.cons true (.cons false (.cons true .nil)))))),
  .cnot (.cons false (.cons true (.cons false (.cons true (.cons false (.cons true .nil)))))) (.cons
    false (.cons true (.cons false (.cons true (.cons true (.cons false .nil)))))),
  .cnot (.cons false (.cons true (.cons false (.cons true (.cons false (.cons true .nil)))))) (.cons
    false (.cons true (.cons false (.cons true (.cons false (.cons false .nil)))))),
  .cnot (.cons false (.cons true (.cons false (.cons true (.cons false (.cons false .nil))))))
    (.cons false (.cons true (.cons false (.cons true (.cons true (.cons true .nil)))))),
  .cnot (.cons false (.cons true (.cons false (.cons true (.cons false (.cons false .nil))))))
    (.cons false (.cons true (.cons false (.cons true (.cons true (.cons false .nil)))))),
  .cnot (.cons false (.cons true (.cons false (.cons true (.cons false (.cons false .nil))))))
    (.cons false (.cons false (.cons false (.cons true (.cons true (.cons true .nil)))))),
  .cnot (.cons false (.cons true (.cons false (.cons true (.cons false (.cons false .nil))))))
    (.cons false (.cons false (.cons false (.cons true (.cons true (.cons false .nil)))))),
  .cnot (.cons false (.cons true (.cons false (.cons true (.cons false (.cons true .nil)))))) (.cons
    false (.cons true (.cons false (.cons true (.cons false (.cons false .nil)))))),
  .cnot (.cons false (.cons true (.cons false (.cons true (.cons false (.cons false .nil))))))
    (.cons false (.cons true (.cons false (.cons true (.cons false (.cons true .nil)))))),
  .cnot (.cons false (.cons true (.cons false (.cons true (.cons false (.cons true .nil)))))) (.cons
    false (.cons true (.cons false (.cons true (.cons false (.cons false .nil)))))),
  .cnot (.cons false (.cons true (.cons false (.cons false (.cons true (.cons true .nil)))))) (.cons
    false (.cons false (.cons false (.cons true (.cons true (.cons false .nil)))))),
  .cnot (.cons false (.cons true (.cons false (.cons true (.cons false (.cons true .nil)))))) (.cons
    false (.cons true (.cons false (.cons false (.cons true (.cons true .nil)))))),
  .cnot (.cons false (.cons true (.cons false (.cons false (.cons true (.cons true .nil)))))) (.cons
    false (.cons true (.cons false (.cons true (.cons false (.cons true .nil)))))),
  .cnot (.cons false (.cons true (.cons false (.cons true (.cons false (.cons true .nil)))))) (.cons
    false (.cons true (.cons false (.cons false (.cons true (.cons true .nil)))))),
  .cnot (.cons false (.cons false (.cons false (.cons true (.cons true (.cons true .nil)))))) (.cons
    false (.cons true (.cons false (.cons true (.cons true (.cons true .nil)))))),
  .cnot (.cons false (.cons true (.cons false (.cons true (.cons true (.cons false .nil)))))) (.cons
    false (.cons false (.cons false (.cons true (.cons true (.cons true .nil)))))),
  .cnot (.cons false (.cons false (.cons false (.cons true (.cons true (.cons true .nil)))))) (.cons
    false (.cons true (.cons false (.cons true (.cons true (.cons false .nil)))))),
  .cnot (.cons false (.cons true (.cons false (.cons true (.cons true (.cons false .nil)))))) (.cons
    false (.cons false (.cons false (.cons true (.cons true (.cons true .nil)))))),
  .cnot (.cons false (.cons false (.cons false (.cons true (.cons true (.cons false .nil))))))
    (.cons false (.cons true (.cons false (.cons true (.cons true (.cons false .nil)))))),
  .cnot (.cons false (.cons false (.cons false (.cons true (.cons true (.cons false .nil))))))
    (.cons false (.cons true (.cons false (.cons false (.cons true (.cons true .nil)))))),
  .cnot (.cons false (.cons false (.cons false (.cons true (.cons true (.cons true .nil)))))) (.cons
    false (.cons false (.cons false (.cons true (.cons true (.cons false .nil)))))),
  .cnot (.cons false (.cons false (.cons false (.cons true (.cons true (.cons false .nil))))))
    (.cons false (.cons false (.cons false (.cons true (.cons true (.cons true .nil)))))),
  .cnot (.cons false (.cons false (.cons false (.cons true (.cons true (.cons true .nil)))))) (.cons
    false (.cons false (.cons false (.cons true (.cons true (.cons false .nil)))))),
  .cnot (.cons false (.cons false (.cons false (.cons true (.cons false (.cons true .nil))))))
    (.cons false (.cons true (.cons false (.cons true (.cons false (.cons true .nil)))))),
  .cnot (.cons false (.cons false (.cons false (.cons true (.cons false (.cons true .nil))))))
    (.cons false (.cons false (.cons false (.cons true (.cons true (.cons false .nil)))))),
  .cnot (.cons false (.cons false (.cons false (.cons true (.cons false (.cons false .nil))))))
    (.cons false (.cons true (.cons false (.cons true (.cons false (.cons false .nil)))))),
  .cnot (.cons false (.cons false (.cons false (.cons true (.cons false (.cons false .nil))))))
    (.cons false (.cons false (.cons false (.cons true (.cons true (.cons false .nil)))))),
  .x (.cons false (.cons false (.cons false (.cons true (.cons false (.cons true .nil)))))),
  .x (.cons false (.cons false (.cons false (.cons true (.cons true (.cons true .nil)))))),
  .x (.cons false (.cons true (.cons false (.cons false (.cons true (.cons true .nil)))))),
  .x (.cons false (.cons true (.cons false (.cons true (.cons true (.cons false .nil))))))
]
def localSqAx1Ph2 : List LocalStep := [
  .tempAnd (.cons false (.cons false (.cons false (.cons false (.cons false (.cons false .nil))))))
    (.cons false (.cons false (.cons false (.cons true (.cons true (.cons true .nil)))))) (.cons
    false (.cons false (.cons true (.cons false (.cons false (.cons false .nil)))))),
  .tempAnd (.cons false (.cons false (.cons false (.cons false (.cons false (.cons true .nil))))))
    (.cons false (.cons false (.cons false (.cons true (.cons true (.cons false .nil)))))) (.cons
    false (.cons false (.cons true (.cons false (.cons false (.cons true .nil)))))),
  .tempAnd (.cons false (.cons false (.cons false (.cons false (.cons true (.cons false .nil))))))
    (.cons false (.cons false (.cons false (.cons true (.cons false (.cons true .nil)))))) (.cons
    false (.cons false (.cons true (.cons false (.cons true (.cons false .nil)))))),
  .tempAnd (.cons false (.cons false (.cons false (.cons false (.cons true (.cons true .nil))))))
    (.cons false (.cons false (.cons false (.cons true (.cons false (.cons false .nil)))))) (.cons
    false (.cons false (.cons true (.cons false (.cons true (.cons true .nil)))))),
  .tempAnd (.cons false (.cons false (.cons false (.cons false (.cons false (.cons true .nil))))))
    (.cons false (.cons false (.cons false (.cons true (.cons true (.cons true .nil)))))) (.cons
    false (.cons false (.cons true (.cons true (.cons false (.cons false .nil)))))),
  .tempAnd (.cons false (.cons false (.cons false (.cons false (.cons true (.cons false .nil))))))
    (.cons false (.cons false (.cons false (.cons true (.cons true (.cons false .nil)))))) (.cons
    false (.cons false (.cons true (.cons true (.cons false (.cons true .nil)))))),
  .tempAnd (.cons false (.cons false (.cons false (.cons false (.cons true (.cons true .nil))))))
    (.cons false (.cons false (.cons false (.cons true (.cons false (.cons true .nil)))))) (.cons
    false (.cons false (.cons true (.cons true (.cons true (.cons false .nil)))))),
  .tempAnd (.cons false (.cons false (.cons false (.cons false (.cons true (.cons false .nil))))))
    (.cons false (.cons false (.cons false (.cons true (.cons true (.cons true .nil)))))) (.cons
    false (.cons false (.cons true (.cons true (.cons true (.cons true .nil)))))),
  .tempAnd (.cons false (.cons false (.cons false (.cons false (.cons true (.cons true .nil))))))
    (.cons false (.cons false (.cons false (.cons true (.cons true (.cons false .nil)))))) (.cons
    false (.cons true (.cons false (.cons false (.cons false (.cons false .nil)))))),
  .tempAnd (.cons false (.cons false (.cons false (.cons false (.cons true (.cons true .nil))))))
    (.cons false (.cons false (.cons false (.cons true (.cons true (.cons true .nil)))))) (.cons
    false (.cons true (.cons false (.cons false (.cons false (.cons true .nil))))))
]
def localSqAx2Ph1 : List LocalStep := [
  .tempAnd (.cons false (.cons false (.cons false (.cons false (.cons false (.cons false .nil))))))
    (.cons false (.cons false (.cons false (.cons true (.cons false (.cons false .nil)))))) (.cons
    false (.cons false (.cons true (.cons false (.cons false (.cons false .nil)))))),
  .tempAnd (.cons false (.cons false (.cons false (.cons false (.cons false (.cons false .nil))))))
    (.cons false (.cons false (.cons false (.cons true (.cons false (.cons true .nil)))))) (.cons
    false (.cons false (.cons true (.cons false (.cons false (.cons true .nil)))))),
  .tempAnd (.cons false (.cons false (.cons false (.cons false (.cons false (.cons true .nil))))))
    (.cons false (.cons false (.cons false (.cons true (.cons false (.cons false .nil)))))) (.cons
    false (.cons false (.cons true (.cons false (.cons true (.cons false .nil)))))),
  .tempAnd (.cons false (.cons false (.cons false (.cons false (.cons false (.cons false .nil))))))
    (.cons false (.cons false (.cons false (.cons true (.cons true (.cons false .nil)))))) (.cons
    false (.cons false (.cons true (.cons false (.cons true (.cons true .nil)))))),
  .tempAnd (.cons false (.cons false (.cons false (.cons false (.cons false (.cons true .nil))))))
    (.cons false (.cons false (.cons false (.cons true (.cons false (.cons true .nil)))))) (.cons
    false (.cons false (.cons true (.cons true (.cons false (.cons false .nil)))))),
  .tempAnd (.cons false (.cons false (.cons false (.cons false (.cons true (.cons false .nil))))))
    (.cons false (.cons false (.cons false (.cons true (.cons false (.cons false .nil)))))) (.cons
    false (.cons false (.cons true (.cons true (.cons false (.cons true .nil)))))),
  .x (.cons false (.cons false (.cons false (.cons false (.cons true (.cons true .nil)))))),
  .x (.cons false (.cons false (.cons false (.cons false (.cons true (.cons false .nil)))))),
  .tempAnd (.cons false (.cons false (.cons false (.cons false (.cons true (.cons true .nil))))))
    (.cons false (.cons false (.cons false (.cons false (.cons true (.cons false .nil)))))) (.cons
    false (.cons false (.cons true (.cons true (.cons true (.cons false .nil)))))),
  .x (.cons false (.cons false (.cons false (.cons false (.cons true (.cons false .nil)))))),
  .x (.cons false (.cons false (.cons false (.cons false (.cons true (.cons true .nil)))))),
  .x (.cons false (.cons false (.cons false (.cons false (.cons false (.cons true .nil)))))),
  .x (.cons false (.cons false (.cons false (.cons false (.cons false (.cons false .nil)))))),
  .tempAnd (.cons false (.cons false (.cons false (.cons false (.cons false (.cons true .nil))))))
    (.cons false (.cons false (.cons false (.cons false (.cons false (.cons false .nil)))))) (.cons
    false (.cons false (.cons true (.cons true (.cons true (.cons true .nil)))))),
  .x (.cons false (.cons false (.cons false (.cons false (.cons false (.cons false .nil)))))),
  .x (.cons false (.cons false (.cons false (.cons false (.cons false (.cons true .nil)))))),
  .x (.cons false (.cons false (.cons false (.cons false (.cons true (.cons true .nil)))))),
  .cnot (.cons false (.cons false (.cons true (.cons true (.cons true (.cons true .nil)))))) (.cons
    false (.cons false (.cons false (.cons false (.cons true (.cons true .nil)))))),
  .cnot (.cons false (.cons false (.cons false (.cons false (.cons true (.cons false .nil))))))
    (.cons false (.cons false (.cons false (.cons false (.cons false (.cons false .nil)))))),
  .cnot (.cons false (.cons false (.cons true (.cons true (.cons true (.cons true .nil)))))) (.cons
    false (.cons false (.cons false (.cons false (.cons false (.cons false .nil)))))),
  .tempAnd (.cons false (.cons false (.cons false (.cons false (.cons true (.cons true .nil))))))
    (.cons false (.cons false (.cons false (.cons false (.cons false (.cons false .nil)))))) (.cons
    false (.cons true (.cons false (.cons false (.cons false (.cons false .nil)))))),
  .cnot (.cons false (.cons false (.cons true (.cons true (.cons true (.cons true .nil)))))) (.cons
    false (.cons false (.cons false (.cons false (.cons false (.cons false .nil)))))),
  .cnot (.cons false (.cons false (.cons false (.cons false (.cons true (.cons false .nil))))))
    (.cons false (.cons false (.cons false (.cons false (.cons false (.cons false .nil)))))),
  .cnot (.cons false (.cons false (.cons true (.cons true (.cons true (.cons true .nil)))))) (.cons
    false (.cons false (.cons false (.cons false (.cons true (.cons true .nil)))))),
  .x (.cons false (.cons false (.cons false (.cons false (.cons true (.cons true .nil)))))),
  .cnot (.cons false (.cons false (.cons false (.cons false (.cons true (.cons true .nil))))))
    (.cons false (.cons false (.cons false (.cons false (.cons true (.cons false .nil)))))),
  .cnot (.cons false (.cons false (.cons true (.cons true (.cons true (.cons true .nil)))))) (.cons
    false (.cons false (.cons false (.cons false (.cons true (.cons false .nil)))))),
  .cnot (.cons false (.cons false (.cons false (.cons false (.cons false (.cons true .nil))))))
    (.cons false (.cons false (.cons false (.cons false (.cons false (.cons false .nil)))))),
  .cnot (.cons false (.cons true (.cons false (.cons false (.cons false (.cons false .nil))))))
    (.cons false (.cons false (.cons false (.cons false (.cons false (.cons false .nil)))))),
  .tempAnd (.cons false (.cons false (.cons false (.cons false (.cons true (.cons false .nil))))))
    (.cons false (.cons false (.cons false (.cons false (.cons false (.cons false .nil)))))) (.cons
    false (.cons true (.cons false (.cons false (.cons false (.cons true .nil)))))),
  .cnot (.cons false (.cons true (.cons false (.cons false (.cons false (.cons false .nil))))))
    (.cons false (.cons false (.cons false (.cons false (.cons false (.cons false .nil)))))),
  .cnot (.cons false (.cons false (.cons false (.cons false (.cons false (.cons true .nil))))))
    (.cons false (.cons false (.cons false (.cons false (.cons false (.cons false .nil)))))),
  .cnot (.cons false (.cons false (.cons true (.cons true (.cons true (.cons true .nil)))))) (.cons
    false (.cons false (.cons false (.cons false (.cons true (.cons false .nil)))))),
  .cnot (.cons false (.cons false (.cons false (.cons false (.cons true (.cons true .nil))))))
    (.cons false (.cons false (.cons false (.cons false (.cons true (.cons false .nil)))))),
  .x (.cons false (.cons true (.cons false (.cons false (.cons false (.cons true .nil)))))),
  .cnot (.cons false (.cons false (.cons false (.cons false (.cons true (.cons true .nil))))))
    (.cons false (.cons true (.cons false (.cons false (.cons false (.cons true .nil)))))),
  .cnot (.cons false (.cons false (.cons false (.cons false (.cons false (.cons true .nil))))))
    (.cons false (.cons false (.cons true (.cons true (.cons true (.cons false .nil)))))),
  .cnot (.cons false (.cons false (.cons false (.cons false (.cons true (.cons true .nil))))))
    (.cons false (.cons false (.cons true (.cons true (.cons true (.cons false .nil)))))),
  .tempAnd (.cons false (.cons true (.cons false (.cons false (.cons false (.cons true .nil))))))
    (.cons false (.cons false (.cons true (.cons true (.cons true (.cons false .nil)))))) (.cons
    false (.cons true (.cons false (.cons false (.cons true (.cons false .nil)))))),
  .cnot (.cons false (.cons false (.cons false (.cons false (.cons true (.cons true .nil))))))
    (.cons false (.cons false (.cons true (.cons true (.cons true (.cons false .nil)))))),
  .cnot (.cons false (.cons false (.cons false (.cons false (.cons false (.cons true .nil))))))
    (.cons false (.cons false (.cons true (.cons true (.cons true (.cons false .nil)))))),
  .cnot (.cons false (.cons false (.cons false (.cons false (.cons true (.cons true .nil))))))
    (.cons false (.cons true (.cons false (.cons false (.cons false (.cons true .nil)))))),
  .x (.cons false (.cons true (.cons false (.cons false (.cons false (.cons true .nil)))))),
  .cnot (.cons false (.cons true (.cons false (.cons false (.cons true (.cons false .nil))))))
    (.cons false (.cons true (.cons false (.cons false (.cons false (.cons true .nil)))))),
  .cnot (.cons false (.cons true (.cons false (.cons false (.cons true (.cons false .nil))))))
    (.cons false (.cons true (.cons false (.cons false (.cons false (.cons false .nil)))))),
  .cnot (.cons false (.cons true (.cons false (.cons false (.cons true (.cons false .nil))))))
    (.cons false (.cons false (.cons true (.cons true (.cons true (.cons false .nil)))))),
  .cnot (.cons false (.cons true (.cons false (.cons false (.cons true (.cons false .nil))))))
    (.cons false (.cons false (.cons false (.cons false (.cons true (.cons true .nil)))))),
  .cnot (.cons false (.cons true (.cons false (.cons false (.cons false (.cons true .nil))))))
    (.cons false (.cons true (.cons false (.cons false (.cons true (.cons false .nil)))))),
  .cnot (.cons false (.cons true (.cons false (.cons false (.cons false (.cons true .nil))))))
    (.cons false (.cons true (.cons false (.cons false (.cons false (.cons false .nil)))))),
  .cnot (.cons false (.cons true (.cons false (.cons false (.cons false (.cons true .nil))))))
    (.cons false (.cons false (.cons true (.cons true (.cons true (.cons true .nil)))))),
  .cnot (.cons false (.cons true (.cons false (.cons false (.cons false (.cons true .nil))))))
    (.cons false (.cons false (.cons true (.cons true (.cons true (.cons false .nil)))))),
  .cnot (.cons false (.cons true (.cons false (.cons false (.cons false (.cons true .nil))))))
    (.cons false (.cons false (.cons false (.cons false (.cons true (.cons true .nil)))))),
  .cnot (.cons false (.cons true (.cons false (.cons false (.cons false (.cons true .nil))))))
    (.cons false (.cons false (.cons false (.cons false (.cons false (.cons true .nil)))))),
  .cnot (.cons false (.cons true (.cons false (.cons false (.cons false (.cons false .nil))))))
    (.cons false (.cons true (.cons false (.cons false (.cons false (.cons true .nil)))))),
  .cnot (.cons false (.cons true (.cons false (.cons false (.cons false (.cons false .nil))))))
    (.cons false (.cons false (.cons true (.cons true (.cons true (.cons true .nil)))))),
  .cnot (.cons false (.cons false (.cons true (.cons true (.cons true (.cons true .nil)))))) (.cons
    false (.cons true (.cons false (.cons false (.cons true (.cons false .nil)))))),
  .cnot (.cons false (.cons false (.cons true (.cons true (.cons true (.cons true .nil)))))) (.cons
    false (.cons true (.cons false (.cons false (.cons false (.cons true .nil)))))),
  .cnot (.cons false (.cons false (.cons true (.cons true (.cons true (.cons true .nil)))))) (.cons
    false (.cons false (.cons false (.cons false (.cons true (.cons true .nil)))))),
  .cnot (.cons false (.cons false (.cons true (.cons true (.cons true (.cons true .nil)))))) (.cons
    false (.cons false (.cons false (.cons false (.cons true (.cons false .nil)))))),
  .cnot (.cons false (.cons true (.cons false (.cons false (.cons false (.cons false .nil))))))
    (.cons false (.cons false (.cons true (.cons true (.cons true (.cons true .nil)))))),
  .cnot (.cons false (.cons false (.cons true (.cons true (.cons true (.cons true .nil)))))) (.cons
    false (.cons true (.cons false (.cons false (.cons false (.cons false .nil)))))),
  .cnot (.cons false (.cons true (.cons false (.cons false (.cons false (.cons false .nil))))))
    (.cons false (.cons false (.cons true (.cons true (.cons true (.cons true .nil)))))),
  .cnot (.cons false (.cons false (.cons true (.cons true (.cons true (.cons false .nil)))))) (.cons
    false (.cons false (.cons false (.cons false (.cons true (.cons false .nil)))))),
  .cnot (.cons false (.cons true (.cons false (.cons false (.cons false (.cons false .nil))))))
    (.cons false (.cons false (.cons true (.cons true (.cons true (.cons false .nil)))))),
  .cnot (.cons false (.cons false (.cons true (.cons true (.cons true (.cons false .nil)))))) (.cons
    false (.cons true (.cons false (.cons false (.cons false (.cons false .nil)))))),
  .cnot (.cons false (.cons true (.cons false (.cons false (.cons false (.cons false .nil))))))
    (.cons false (.cons false (.cons true (.cons true (.cons true (.cons false .nil)))))),
  .cnot (.cons false (.cons false (.cons false (.cons false (.cons true (.cons true .nil))))))
    (.cons false (.cons true (.cons false (.cons false (.cons true (.cons false .nil)))))),
  .cnot (.cons false (.cons true (.cons false (.cons false (.cons false (.cons true .nil))))))
    (.cons false (.cons false (.cons false (.cons false (.cons true (.cons true .nil)))))),
  .cnot (.cons false (.cons false (.cons false (.cons false (.cons true (.cons true .nil))))))
    (.cons false (.cons true (.cons false (.cons false (.cons false (.cons true .nil)))))),
  .cnot (.cons false (.cons true (.cons false (.cons false (.cons false (.cons true .nil))))))
    (.cons false (.cons false (.cons false (.cons false (.cons true (.cons true .nil)))))),
  .cnot (.cons false (.cons false (.cons false (.cons false (.cons true (.cons false .nil))))))
    (.cons false (.cons true (.cons false (.cons false (.cons false (.cons true .nil)))))),
  .cnot (.cons false (.cons false (.cons false (.cons false (.cons true (.cons false .nil))))))
    (.cons false (.cons false (.cons true (.cons true (.cons true (.cons false .nil)))))),
  .cnot (.cons false (.cons false (.cons false (.cons false (.cons true (.cons true .nil))))))
    (.cons false (.cons false (.cons false (.cons false (.cons true (.cons false .nil)))))),
  .cnot (.cons false (.cons false (.cons false (.cons false (.cons true (.cons false .nil))))))
    (.cons false (.cons false (.cons false (.cons false (.cons true (.cons true .nil)))))),
  .cnot (.cons false (.cons false (.cons false (.cons false (.cons true (.cons true .nil))))))
    (.cons false (.cons false (.cons false (.cons false (.cons true (.cons false .nil)))))),
  .cnot (.cons false (.cons false (.cons false (.cons false (.cons false (.cons true .nil))))))
    (.cons false (.cons true (.cons false (.cons false (.cons false (.cons false .nil)))))),
  .cnot (.cons false (.cons false (.cons false (.cons false (.cons false (.cons true .nil))))))
    (.cons false (.cons false (.cons false (.cons false (.cons true (.cons false .nil)))))),
  .cnot (.cons false (.cons false (.cons false (.cons false (.cons false (.cons false .nil))))))
    (.cons false (.cons false (.cons true (.cons true (.cons true (.cons true .nil)))))),
  .cnot (.cons false (.cons false (.cons false (.cons false (.cons false (.cons false .nil))))))
    (.cons false (.cons false (.cons false (.cons false (.cons true (.cons false .nil)))))),
  .x (.cons false (.cons false (.cons false (.cons false (.cons false (.cons true .nil)))))),
  .x (.cons false (.cons false (.cons false (.cons false (.cons true (.cons true .nil)))))),
  .x (.cons false (.cons false (.cons true (.cons true (.cons true (.cons false .nil)))))),
  .x (.cons false (.cons true (.cons false (.cons false (.cons false (.cons true .nil))))))
]
def localSqAx2Ph2 : List LocalStep := [
  .tempAnd (.cons false (.cons false (.cons false (.cons false (.cons false (.cons false .nil))))))
    (.cons false (.cons false (.cons false (.cons true (.cons true (.cons true .nil)))))) (.cons
    false (.cons false (.cons true (.cons false (.cons false (.cons false .nil)))))),
  .tempAnd (.cons false (.cons false (.cons false (.cons false (.cons false (.cons true .nil))))))
    (.cons false (.cons false (.cons false (.cons true (.cons true (.cons false .nil)))))) (.cons
    false (.cons false (.cons true (.cons false (.cons false (.cons true .nil)))))),
  .tempAnd (.cons false (.cons false (.cons false (.cons false (.cons true (.cons false .nil))))))
    (.cons false (.cons false (.cons false (.cons true (.cons false (.cons true .nil)))))) (.cons
    false (.cons false (.cons true (.cons false (.cons true (.cons false .nil)))))),
  .tempAnd (.cons false (.cons false (.cons false (.cons false (.cons true (.cons true .nil))))))
    (.cons false (.cons false (.cons false (.cons true (.cons false (.cons false .nil)))))) (.cons
    false (.cons false (.cons true (.cons false (.cons true (.cons true .nil)))))),
  .tempAnd (.cons false (.cons false (.cons false (.cons false (.cons false (.cons true .nil))))))
    (.cons false (.cons false (.cons false (.cons true (.cons true (.cons true .nil)))))) (.cons
    false (.cons false (.cons true (.cons true (.cons false (.cons false .nil)))))),
  .tempAnd (.cons false (.cons false (.cons false (.cons false (.cons true (.cons false .nil))))))
    (.cons false (.cons false (.cons false (.cons true (.cons true (.cons false .nil)))))) (.cons
    false (.cons false (.cons true (.cons true (.cons false (.cons true .nil)))))),
  .tempAnd (.cons false (.cons false (.cons false (.cons false (.cons true (.cons true .nil))))))
    (.cons false (.cons false (.cons false (.cons true (.cons false (.cons true .nil)))))) (.cons
    false (.cons false (.cons true (.cons true (.cons true (.cons false .nil)))))),
  .tempAnd (.cons false (.cons false (.cons false (.cons false (.cons true (.cons false .nil))))))
    (.cons false (.cons false (.cons false (.cons true (.cons true (.cons true .nil)))))) (.cons
    false (.cons false (.cons true (.cons true (.cons true (.cons true .nil)))))),
  .tempAnd (.cons false (.cons false (.cons false (.cons false (.cons true (.cons true .nil))))))
    (.cons false (.cons false (.cons false (.cons true (.cons true (.cons false .nil)))))) (.cons
    false (.cons true (.cons false (.cons false (.cons false (.cons false .nil)))))),
  .tempAnd (.cons false (.cons false (.cons false (.cons false (.cons true (.cons true .nil))))))
    (.cons false (.cons false (.cons false (.cons true (.cons true (.cons true .nil)))))) (.cons
    false (.cons true (.cons false (.cons false (.cons false (.cons true .nil)))))),
  .x (.cons false (.cons false (.cons false (.cons true (.cons true (.cons true .nil)))))),
  .x (.cons false (.cons false (.cons false (.cons true (.cons true (.cons false .nil)))))),
  .tempAnd (.cons false (.cons false (.cons false (.cons true (.cons true (.cons true .nil))))))
    (.cons false (.cons false (.cons false (.cons true (.cons true (.cons false .nil)))))) (.cons
    false (.cons true (.cons false (.cons false (.cons true (.cons false .nil)))))),
  .x (.cons false (.cons false (.cons false (.cons true (.cons true (.cons false .nil)))))),
  .x (.cons false (.cons false (.cons false (.cons true (.cons true (.cons true .nil)))))),
  .x (.cons false (.cons false (.cons false (.cons true (.cons false (.cons true .nil)))))),
  .x (.cons false (.cons false (.cons false (.cons true (.cons false (.cons false .nil)))))),
  .tempAnd (.cons false (.cons false (.cons false (.cons true (.cons false (.cons true .nil))))))
    (.cons false (.cons false (.cons false (.cons true (.cons false (.cons false .nil)))))) (.cons
    false (.cons true (.cons false (.cons false (.cons true (.cons true .nil)))))),
  .x (.cons false (.cons false (.cons false (.cons true (.cons false (.cons false .nil)))))),
  .x (.cons false (.cons false (.cons false (.cons true (.cons false (.cons true .nil)))))),
  .x (.cons false (.cons false (.cons false (.cons true (.cons true (.cons true .nil)))))),
  .cnot (.cons false (.cons true (.cons false (.cons false (.cons true (.cons true .nil)))))) (.cons
    false (.cons false (.cons false (.cons true (.cons true (.cons true .nil)))))),
  .cnot (.cons false (.cons false (.cons false (.cons true (.cons true (.cons false .nil))))))
    (.cons false (.cons false (.cons false (.cons true (.cons false (.cons false .nil)))))),
  .cnot (.cons false (.cons true (.cons false (.cons false (.cons true (.cons true .nil)))))) (.cons
    false (.cons false (.cons false (.cons true (.cons false (.cons false .nil)))))),
  .tempAnd (.cons false (.cons false (.cons false (.cons true (.cons true (.cons true .nil))))))
    (.cons false (.cons false (.cons false (.cons true (.cons false (.cons false .nil)))))) (.cons
    false (.cons true (.cons false (.cons true (.cons false (.cons false .nil)))))),
  .cnot (.cons false (.cons true (.cons false (.cons false (.cons true (.cons true .nil)))))) (.cons
    false (.cons false (.cons false (.cons true (.cons false (.cons false .nil)))))),
  .cnot (.cons false (.cons false (.cons false (.cons true (.cons true (.cons false .nil))))))
    (.cons false (.cons false (.cons false (.cons true (.cons false (.cons false .nil)))))),
  .cnot (.cons false (.cons true (.cons false (.cons false (.cons true (.cons true .nil)))))) (.cons
    false (.cons false (.cons false (.cons true (.cons true (.cons true .nil)))))),
  .x (.cons false (.cons false (.cons false (.cons true (.cons true (.cons true .nil)))))),
  .cnot (.cons false (.cons false (.cons false (.cons true (.cons true (.cons true .nil)))))) (.cons
    false (.cons false (.cons false (.cons true (.cons true (.cons false .nil)))))),
  .cnot (.cons false (.cons true (.cons false (.cons false (.cons true (.cons true .nil)))))) (.cons
    false (.cons false (.cons false (.cons true (.cons true (.cons false .nil)))))),
  .cnot (.cons false (.cons false (.cons false (.cons true (.cons false (.cons true .nil))))))
    (.cons false (.cons false (.cons false (.cons true (.cons false (.cons false .nil)))))),
  .cnot (.cons false (.cons true (.cons false (.cons true (.cons false (.cons false .nil))))))
    (.cons false (.cons false (.cons false (.cons true (.cons false (.cons false .nil)))))),
  .tempAnd (.cons false (.cons false (.cons false (.cons true (.cons true (.cons false .nil))))))
    (.cons false (.cons false (.cons false (.cons true (.cons false (.cons false .nil)))))) (.cons
    false (.cons true (.cons false (.cons true (.cons false (.cons true .nil)))))),
  .cnot (.cons false (.cons true (.cons false (.cons true (.cons false (.cons false .nil))))))
    (.cons false (.cons false (.cons false (.cons true (.cons false (.cons false .nil)))))),
  .cnot (.cons false (.cons false (.cons false (.cons true (.cons false (.cons true .nil))))))
    (.cons false (.cons false (.cons false (.cons true (.cons false (.cons false .nil)))))),
  .cnot (.cons false (.cons true (.cons false (.cons false (.cons true (.cons true .nil)))))) (.cons
    false (.cons false (.cons false (.cons true (.cons true (.cons false .nil)))))),
  .cnot (.cons false (.cons false (.cons false (.cons true (.cons true (.cons true .nil)))))) (.cons
    false (.cons false (.cons false (.cons true (.cons true (.cons false .nil)))))),
  .x (.cons false (.cons true (.cons false (.cons true (.cons false (.cons true .nil)))))),
  .cnot (.cons false (.cons false (.cons false (.cons true (.cons true (.cons true .nil)))))) (.cons
    false (.cons true (.cons false (.cons true (.cons false (.cons true .nil)))))),
  .cnot (.cons false (.cons false (.cons false (.cons true (.cons false (.cons true .nil))))))
    (.cons false (.cons true (.cons false (.cons false (.cons true (.cons false .nil)))))),
  .cnot (.cons false (.cons false (.cons false (.cons true (.cons true (.cons true .nil)))))) (.cons
    false (.cons true (.cons false (.cons false (.cons true (.cons false .nil)))))),
  .tempAnd (.cons false (.cons true (.cons false (.cons true (.cons false (.cons true .nil))))))
    (.cons false (.cons true (.cons false (.cons false (.cons true (.cons false .nil)))))) (.cons
    false (.cons true (.cons false (.cons true (.cons true (.cons false .nil)))))),
  .cnot (.cons false (.cons false (.cons false (.cons true (.cons true (.cons true .nil)))))) (.cons
    false (.cons true (.cons false (.cons false (.cons true (.cons false .nil)))))),
  .cnot (.cons false (.cons false (.cons false (.cons true (.cons false (.cons true .nil))))))
    (.cons false (.cons true (.cons false (.cons false (.cons true (.cons false .nil)))))),
  .cnot (.cons false (.cons false (.cons false (.cons true (.cons true (.cons true .nil)))))) (.cons
    false (.cons true (.cons false (.cons true (.cons false (.cons true .nil)))))),
  .x (.cons false (.cons true (.cons false (.cons true (.cons false (.cons true .nil)))))),
  .cnot (.cons false (.cons true (.cons false (.cons true (.cons true (.cons false .nil)))))) (.cons
    false (.cons true (.cons false (.cons true (.cons false (.cons true .nil)))))),
  .cnot (.cons false (.cons true (.cons false (.cons true (.cons true (.cons false .nil)))))) (.cons
    false (.cons true (.cons false (.cons true (.cons false (.cons false .nil)))))),
  .cnot (.cons false (.cons true (.cons false (.cons true (.cons true (.cons false .nil)))))) (.cons
    false (.cons true (.cons false (.cons false (.cons true (.cons false .nil)))))),
  .cnot (.cons false (.cons true (.cons false (.cons true (.cons true (.cons false .nil)))))) (.cons
    false (.cons false (.cons false (.cons true (.cons true (.cons true .nil)))))),
  .cnot (.cons false (.cons true (.cons false (.cons true (.cons false (.cons true .nil)))))) (.cons
    false (.cons true (.cons false (.cons true (.cons true (.cons false .nil)))))),
  .cnot (.cons false (.cons true (.cons false (.cons true (.cons false (.cons true .nil)))))) (.cons
    false (.cons true (.cons false (.cons true (.cons false (.cons false .nil)))))),
  .cnot (.cons false (.cons true (.cons false (.cons true (.cons false (.cons true .nil)))))) (.cons
    false (.cons true (.cons false (.cons false (.cons true (.cons true .nil)))))),
  .cnot (.cons false (.cons true (.cons false (.cons true (.cons false (.cons true .nil)))))) (.cons
    false (.cons true (.cons false (.cons false (.cons true (.cons false .nil)))))),
  .cnot (.cons false (.cons true (.cons false (.cons true (.cons false (.cons true .nil)))))) (.cons
    false (.cons false (.cons false (.cons true (.cons true (.cons true .nil)))))),
  .cnot (.cons false (.cons true (.cons false (.cons true (.cons false (.cons true .nil)))))) (.cons
    false (.cons false (.cons false (.cons true (.cons false (.cons true .nil)))))),
  .cnot (.cons false (.cons true (.cons false (.cons true (.cons false (.cons false .nil))))))
    (.cons false (.cons true (.cons false (.cons true (.cons false (.cons true .nil)))))),
  .cnot (.cons false (.cons true (.cons false (.cons true (.cons false (.cons false .nil))))))
    (.cons false (.cons true (.cons false (.cons false (.cons true (.cons true .nil)))))),
  .cnot (.cons false (.cons true (.cons false (.cons false (.cons true (.cons true .nil)))))) (.cons
    false (.cons true (.cons false (.cons true (.cons true (.cons false .nil)))))),
  .cnot (.cons false (.cons true (.cons false (.cons false (.cons true (.cons true .nil)))))) (.cons
    false (.cons true (.cons false (.cons true (.cons false (.cons true .nil)))))),
  .cnot (.cons false (.cons true (.cons false (.cons false (.cons true (.cons true .nil)))))) (.cons
    false (.cons false (.cons false (.cons true (.cons true (.cons true .nil)))))),
  .cnot (.cons false (.cons true (.cons false (.cons false (.cons true (.cons true .nil)))))) (.cons
    false (.cons false (.cons false (.cons true (.cons true (.cons false .nil)))))),
  .cnot (.cons false (.cons true (.cons false (.cons true (.cons false (.cons false .nil))))))
    (.cons false (.cons true (.cons false (.cons false (.cons true (.cons true .nil)))))),
  .cnot (.cons false (.cons true (.cons false (.cons false (.cons true (.cons true .nil)))))) (.cons
    false (.cons true (.cons false (.cons true (.cons false (.cons false .nil)))))),
  .cnot (.cons false (.cons true (.cons false (.cons true (.cons false (.cons false .nil))))))
    (.cons false (.cons true (.cons false (.cons false (.cons true (.cons true .nil)))))),
  .cnot (.cons false (.cons true (.cons false (.cons false (.cons true (.cons false .nil))))))
    (.cons false (.cons false (.cons false (.cons true (.cons true (.cons false .nil)))))),
  .cnot (.cons false (.cons true (.cons false (.cons true (.cons false (.cons false .nil))))))
    (.cons false (.cons true (.cons false (.cons false (.cons true (.cons false .nil)))))),
  .cnot (.cons false (.cons true (.cons false (.cons false (.cons true (.cons false .nil))))))
    (.cons false (.cons true (.cons false (.cons true (.cons false (.cons false .nil)))))),
  .cnot (.cons false (.cons true (.cons false (.cons true (.cons false (.cons false .nil))))))
    (.cons false (.cons true (.cons false (.cons false (.cons true (.cons false .nil)))))),
  .cnot (.cons false (.cons false (.cons false (.cons true (.cons true (.cons true .nil)))))) (.cons
    false (.cons true (.cons false (.cons true (.cons true (.cons false .nil)))))),
  .cnot (.cons false (.cons true (.cons false (.cons true (.cons false (.cons true .nil)))))) (.cons
    false (.cons false (.cons false (.cons true (.cons true (.cons true .nil)))))),
  .cnot (.cons false (.cons false (.cons false (.cons true (.cons true (.cons true .nil)))))) (.cons
    false (.cons true (.cons false (.cons true (.cons false (.cons true .nil)))))),
  .cnot (.cons false (.cons true (.cons false (.cons true (.cons false (.cons true .nil)))))) (.cons
    false (.cons false (.cons false (.cons true (.cons true (.cons true .nil)))))),
  .cnot (.cons false (.cons false (.cons false (.cons true (.cons true (.cons false .nil))))))
    (.cons false (.cons true (.cons false (.cons true (.cons false (.cons true .nil)))))),
  .cnot (.cons false (.cons false (.cons false (.cons true (.cons true (.cons false .nil))))))
    (.cons false (.cons true (.cons false (.cons false (.cons true (.cons false .nil)))))),
  .cnot (.cons false (.cons false (.cons false (.cons true (.cons true (.cons true .nil)))))) (.cons
    false (.cons false (.cons false (.cons true (.cons true (.cons false .nil)))))),
  .cnot (.cons false (.cons false (.cons false (.cons true (.cons true (.cons false .nil))))))
    (.cons false (.cons false (.cons false (.cons true (.cons true (.cons true .nil)))))),
  .cnot (.cons false (.cons false (.cons false (.cons true (.cons true (.cons true .nil)))))) (.cons
    false (.cons false (.cons false (.cons true (.cons true (.cons false .nil)))))),
  .cnot (.cons false (.cons false (.cons false (.cons true (.cons false (.cons true .nil))))))
    (.cons false (.cons true (.cons false (.cons true (.cons false (.cons false .nil)))))),
  .cnot (.cons false (.cons false (.cons false (.cons true (.cons false (.cons true .nil))))))
    (.cons false (.cons false (.cons false (.cons true (.cons true (.cons false .nil)))))),
  .cnot (.cons false (.cons false (.cons false (.cons true (.cons false (.cons false .nil))))))
    (.cons false (.cons true (.cons false (.cons false (.cons true (.cons true .nil)))))),
  .cnot (.cons false (.cons false (.cons false (.cons true (.cons false (.cons false .nil))))))
    (.cons false (.cons false (.cons false (.cons true (.cons true (.cons false .nil)))))),
  .x (.cons false (.cons false (.cons false (.cons true (.cons false (.cons true .nil)))))),
  .x (.cons false (.cons false (.cons false (.cons true (.cons true (.cons true .nil)))))),
  .x (.cons false (.cons true (.cons false (.cons false (.cons true (.cons false .nil)))))),
  .x (.cons false (.cons true (.cons false (.cons true (.cons false (.cons true .nil))))))
]
/-- Axis-`0` Phase-1 local squarer embedding (`278..297`, `L = 28`). -/
def embAx0Ph1 : BAddr 6 → ℕ := mkAxisEmb 0 278
/-- Axis-`1` Phase-1 local squarer embedding (`298..313`, `L = 24`). -/
def embAx1Ph1 : BAddr 6 → ℕ := mkAxisEmb 1 298
/-- Axis-`2` Phase-1 local squarer embedding (`314..324`, `L = 19`). -/
def embAx2Ph1 : BAddr 6 → ℕ := mkAxisEmb 2 314
/-- Axis-`0` Phase-2 local squarer embedding (`278..283`, `L = 14`). -/
def embAx0Ph2 : BAddr 6 → ℕ := mkAxisEmb 0 278
/-- Axis-`1` Phase-2 local squarer embedding (`284..293`, `L = 18`). -/
def embAx1Ph2 : BAddr 6 → ℕ := mkAxisEmb 1 284
/-- Axis-`2` Phase-2 local squarer embedding (`294..308`, `L = 23`). -/
def embAx2Ph2 : BAddr 6 → ℕ := mkAxisEmb 2 294
def K_ax0Ph1A : TempCtx 437 := buildP57Ctx (localSqAx0Ph1A.map (mapLocalStep embAx0Ph1))
def K_ax0Ph1B : TempCtx 437 := buildP57Ctx (localSqAx0Ph1B.map (mapLocalStep embAx0Ph1))
def K_ax0Ph1 : TempCtx 437 := K_ax0Ph1A.append K_ax0Ph1B
def K_ax1Ph1A : TempCtx 437 := buildP57Ctx (localSqAx1Ph1A.map (mapLocalStep embAx1Ph1))
def K_ax1Ph1B : TempCtx 437 := buildP57Ctx (localSqAx1Ph1B.map (mapLocalStep embAx1Ph1))
def K_ax1Ph1 : TempCtx 437 := K_ax1Ph1A.append K_ax1Ph1B
def K_ax2Ph1 : TempCtx 437 := buildP57Ctx (localSqAx2Ph1.map (mapLocalStep embAx2Ph1))
def K_ax0Ph2 : TempCtx 437 := buildP57Ctx (localSqAx0Ph2.map (mapLocalStep embAx0Ph2))
def K_ax1Ph2 : TempCtx 437 := buildP57Ctx (localSqAx1Ph2.map (mapLocalStep embAx1Ph2))
def K_ax2Ph2 : TempCtx 437 := buildP57Ctx (localSqAx2Ph2.map (mapLocalStep embAx2Ph2))
def colRedOps35_ph1 : List ColRedOp := [
  .fa 2 178 179 185 325, .fa 2 178 186 192 326, .fa 3 326 325 180 327,
  .fa 3 326 187 194 328, .fa 4 328 327 288 329, .fa 4 328 304 320 330,
  .fa 5 330 329 289 331, .fa 5 330 278 305 332, .fa 5 330 298 321 333,
  .fa 6 333 332 331 334, .fa 6 333 290 279 335, .fa 6 333 280 306 336,
  .fa 6 333 299 300 337, .fa 6 333 322 315 338, .fa 7 338 337 336 339,
  .fa 7 338 335 334 340, .fa 7 338 291 281 341, .fa 7 338 282 283 342,
  .fa 7 338 307 301 343, .fa 7 338 302 303 344, .fa 7 338 323 317 345,
  .fa 7 338 318 319 346, .fa 8 346 345 344 347, .fa 8 346 343 342 348,
  .fa 8 346 341 340 349, .fa 9 349 348 347 350, .fa 10 350 182 183 351,
  .fa 10 350 285 286 352, .fa 10 350 189 190 353, .fa 11 353 352 351 354,
  .fa 11 353 275 287 355, .fa 12 355 354 293 356, .fa 13 356 294 310 357,
  .fa 14 357 295 311 358, .fa 15 358 296 312 359
]
def K_red35_ph1 : TempCtx 437 := buildColRedCtx colRedOps35_ph1
def K_ph1_82 : TempCtx 437 := K_ax0Ph1.append (K_ax1Ph1.append (K_ax2Ph1.append K_red35_ph1))
def colRedOps29_ph2 : List ColRedOp := [
  .fa 8 181 278 279 309, .fa 8 181 280 281 310, .fa 8 181 188 284 311,
  .fa 8 181 285 286 312, .fa 8 181 287 195 313, .fa 8 181 294 295 314,
  .fa 8 181 296 297 315, .fa 9 315 314 313 316, .fa 9 315 312 311 317,
  .fa 9 315 310 309 318, .fa 9 315 282 283 319, .fa 9 315 288 289 320,
  .fa 9 315 290 298 321, .fa 9 315 299 300 322, .fa 10 322 321 320 323,
  .fa 10 322 319 318 324, .fa 10 322 317 316 325, .fa 10 322 291 292 326,
  .fa 10 322 301 302 327, .fa 10 322 196 197 328, .fa 11 328 327 326 329,
  .fa 11 328 325 324 330, .fa 11 328 323 293 331, .fa 11 328 303 277 332,
  .fa 12 332 331 330 333, .fa 12 332 329 304 334, .fa 13 334 333 305 335,
  .ha 14 335 306 336, .ha 15 336 307 337
]
def K_red29_ph2 : TempCtx 437 := buildColRedCtx colRedOps29_ph2
def K_ph2_60 : TempCtx 437 := K_ax0Ph2.append (K_ax1Ph2.append (K_ax2Ph2.append K_red29_ph2))
def K_ph1_82_374 : TempCtx 374 := truncateCtxB 374 K_ph1_82 (by decide)
def K_ph2_60_374 : TempCtx 374 := truncateCtxB 374 K_ph2_60 (by decide)
def ph1A15_82 : Fin 15 → Wire 374
  | ⟨0, _⟩ => ⟨178, by decide⟩
  | ⟨1, _⟩ => ⟨326, by decide⟩
  | ⟨2, _⟩ => ⟨328, by decide⟩
  | ⟨3, _⟩ => ⟨330, by decide⟩
  | ⟨4, _⟩ => ⟨333, by decide⟩
  | ⟨5, _⟩ => ⟨338, by decide⟩
  | ⟨6, _⟩ => ⟨346, by decide⟩
  | ⟨7, _⟩ => ⟨349, by decide⟩
  | ⟨8, _⟩ => ⟨350, by decide⟩
  | ⟨9, _⟩ => ⟨353, by decide⟩
  | ⟨10, _⟩ => ⟨355, by decide⟩
  | ⟨11, _⟩ => ⟨356, by decide⟩
  | ⟨12, _⟩ => ⟨357, by decide⟩
  | ⟨13, _⟩ => ⟨358, by decide⟩
  | ⟨14, _⟩ => ⟨359, by decide⟩
  | ⟨_ + 15, h⟩ => absurd h (by omega)
def ph1B15_82 : Fin 15 → Wire 374
  | ⟨0, _⟩ => ⟨193, by decide⟩
  | ⟨1, _⟩ => ⟨371, by decide⟩
  | ⟨2, _⟩ => ⟨371, by decide⟩
  | ⟨3, _⟩ => ⟨314, by decide⟩
  | ⟨4, _⟩ => ⟨316, by decide⟩
  | ⟨5, _⟩ => ⟨371, by decide⟩
  | ⟨6, _⟩ => ⟨339, by decide⟩
  | ⟨7, _⟩ => ⟨284, by decide⟩
  | ⟨8, _⟩ => ⟨371, by decide⟩
  | ⟨9, _⟩ => ⟨276, by decide⟩
  | ⟨10, _⟩ => ⟨309, by decide⟩
  | ⟨11, _⟩ => ⟨371, by decide⟩
  | ⟨12, _⟩ => ⟨371, by decide⟩
  | ⟨13, _⟩ => ⟨371, by decide⟩
  | ⟨14, _⟩ => ⟨371, by decide⟩
  | ⟨_ + 15, h⟩ => absurd h (by omega)
theorem ph1A15_82_ne_ph1Dst15 (i j : Fin 15) : ph1A15_82 i ≠ ph1Dst15 j := by
  revert i j; decide
theorem ph1B15_82_ne_ph1Dst15 (i j : Fin 15) : ph1B15_82 i ≠ ph1Dst15 j := by
  revert i j; decide
def ph1XorCliff_82 : CliffProg 374 :=
  .seq (cnotVec 15 ph1A15_82 ph1Dst15 (fun k ↦ ph1A15_82_ne_ph1Dst15 k k))
    (cnotVec 15 ph1B15_82 ph1Dst15 (fun k ↦ ph1B15_82_ne_ph1Dst15 k k))
def ph1MajStep_82 (i : Fin 14) : TempPhaseProg 374 :=
  apexMajAt 372 (by decide)
    (ph1CarryW i.castSucc) (ph1A15_82 i.castSucc) (ph1B15_82 i.castSucc) (ph1Dst15 i.succ)
    (by revert i; decide) (by revert i; decide) (by revert i; decide) (by revert i; decide)
    (by revert i; decide) (by revert i; decide) (by revert i; decide) (by revert i; decide)
def ph1BuildLoop_82 : (m : ℕ) → m ≤ 14 → TempPhaseProg 374
  | 0, _ => .nil
  | m + 1, hm => .seq (ph1BuildLoop_82 m (by omega)) (ph1MajStep_82 ⟨m, hm⟩)
def ph1InnerFwd_82 : TempPhaseProg 374 :=
  .seq (ph1BuildLoop_82 14 le_rfl) (.cliff ph1XorCliff_82)
def ph1Fwd113_374 : TempPhaseProg 374 := K_ph1_82_374.plug ph1InnerFwd_82
def ph2B374Aux : Fin 9 → Wire 374
  | ⟨0, _⟩ => ⟨181, by decide⟩
  | ⟨1, _⟩ => ⟨315, by decide⟩
  | ⟨2, _⟩ => ⟨322, by decide⟩
  | ⟨3, _⟩ => ⟨328, by decide⟩
  | ⟨4, _⟩ => ⟨332, by decide⟩
  | ⟨5, _⟩ => ⟨334, by decide⟩
  | ⟨6, _⟩ => ⟨335, by decide⟩
  | ⟨7, _⟩ => ⟨336, by decide⟩
  | ⟨8, _⟩ => ⟨337, by decide⟩
  | ⟨_ + 9, h⟩ => absurd h (by omega)
/-- Phase 2 `10`-wire padded addend (`ph2B374Aux` extended with clean wire `339` at bit `9`). -/
def ph2B374 : Fin 10 → Wire 374 :=
  Fin.snoc ph2B374Aux ⟨339, by decide⟩
/-- `10`-bit high destination slice `sTrue18W374[8..17]` (`cols 8..17`). -/
def ph2Dst10 (k : Fin 10) : Wire 374 :=
  sTrue18W374 ⟨8 + k.val, by omega⟩
/-- Inner `9`-`TempAnd` modular adder for Phase 2 (`cur = 340..348 < 374`, `cin = 338`). -/
def ph2InnerFwd_60 : TempPhaseProg 374 :=
  inPlaceAddMod1 9 340 (by decide) ph2B374 ph2Dst10 ⟨338, by decide⟩
    (fun j ↦ by revert j; decide) (fun j ↦ by revert j; decide) (fun j ↦ by revert j; decide)
    (fun j ↦ by revert j; decide) (fun j ↦ by revert j; decide) (by decide)
/-- `69`-`TempAnd` (`60 + 9`) Phase 2 forward circuit (`sTrue18W374[8..17] += ph2Target374`). -/
def ph2Fwd113_374 : TempPhaseProg 374 := K_ph2_60_374.plug ph2InnerFwd_60
def sTrue18InnerFwd113_374 : TempPhaseProg 374 :=
  .seq ph0Fwd374 (.seq ph1Fwd113_374 ph2Fwd113_374)
def sTrue18Fwd113_374 : TempPhaseProg 374 := K_wrapLin_374.plug sTrue18InnerFwd113_374
/-- `437`-wire `166`-`TempAnd` (`664 T`, `-24 T`) forward `sTrue18` circuit supported strictly on
  `< 374` wires. -/
def sTrue18Fwd113_275 : TempPhaseProg 437 := padProg437 sTrue18Fwd113_374
theorem sTrue18Fwd113_275_supportsBelow374 : progSupportsBelowB 374 sTrue18Fwd113_275 = true := by
  have hDef : sTrue18Fwd113_275 = padProg437 sTrue18Fwd113_374 := rfl
  rw [hDef]
  exact progSupportsBelowB_padProg437 sTrue18Fwd113_374
/-- Stage-1 `< 374`-wire tail (`magUnpackFromRetQuad51_275` through `sTrue18Fwd113_275`). -/
def pStep1CompactTail113_275 : TempPhaseProg 437 := .seq magUnpackFromRetQuad51_275 (.seq
    zMag3Ret18_275 (.seq validStaticFromZ28_275 (.seq axisStep3_fast321_275
    sTrue18Fwd113_275)))
/-- `315`-`TempAnd` (`1,260 T`, `-60 T` vs `pStep1Compact99_275`'s `1,320 T`) `< 374`-wire
  Stage-1 forward preparation program. -/
def pStep1Compact113_275 : TempPhaseProg 437 :=
  .seq coinOkXor275 (.seq muAndQuadXor5_275 pStep1CompactTail113_275)
set_option maxRecDepth 65536 in
theorem pStep1Compact113_275_supports374 :
    progSupportsBelowB 374 pStep1Compact113_275 = true := by
  have h1 : progSupportsBelowB 374 coinOkXor275 = true := by decide
  have h2 : progSupportsBelowB 374 muAndQuadXor5_275 = true := by decide
  have h3 : progSupportsBelowB 374 magUnpackFromRetQuad51_275 = true := by decide
  have h4 : progSupportsBelowB 374 zMag3Ret18_275 = true := by decide
  have h5 : progSupportsBelowB 374 validStaticFromZ28_275 = true := by decide
  have h6 : progSupportsBelowB 374 axisStep3_fast321_275 = true := by decide
  have h7 := sTrue18Fwd113_275_supportsBelow374
  dsimp only [pStep1Compact113_275, pStep1CompactTail113_275, progSupportsBelowB]
  rw [h1, h2, h3, h4, h5, h6, h7]
  rfl
set_option maxRecDepth 65536 in
theorem pStep1Compact113_275_disjoint324 :
    progDisjointBad (isBadXM 374 (isBad374W 324)) pStep1Compact113_275 = true := by
  have h1 : progDisjointBad (isBadXM 374 (isBad374W 324)) coinOkXor275 = true := by decide
  have h2 : progDisjointBad (isBadXM 374 (isBad374W 324)) muAndQuadXor5_275 = true := by decide
  have h3 : progDisjointBad (isBadXM 374 (isBad374W 324)) magUnpackFromRetQuad51_275 = true := by
    decide
  have h4 : progDisjointBad (isBadXM 374 (isBad374W 324)) zMag3Ret18_275 = true := by decide
  have h5 : progDisjointBad (isBadXM 374 (isBad374W 324)) validStaticFromZ28_275 = true := by decide
  have h6 : progDisjointBad (isBadXM 374 (isBad374W 324)) axisStep3_fast321_275 = true := by decide
  have h7 : progDisjointBad (isBadXM 374 (isBad374W 324)) sTrue18Fwd113_275 = true := by decide
  dsimp only [pStep1Compact113_275, pStep1CompactTail113_275, progDisjointBad]
  rw [h1, h2, h3, h4, h5, h6, h7]
  rfl
attribute [irreducible]
  magUnpackFromRetQuad51_275 ph1Fwd113_374 K_ph1_82_374 ph2Fwd113_374 K_ph2_60_374
  sTrue18Fwd113_374 sTrue18Fwd113_275 pStep1Compact113_275
end
end ConfigK5
end STrue18Compact113
end
end STrue18Compact113

noncomputable section FastSTrue18XorSq

section
namespace FastSTrue18XorSq
section ConfigK4
set_option maxRecDepth 65536
set_option exponentiation.threshold 5000
set_option backward.isDefEq.respectTransparency false
local instance (priority := 10) instNeZeroTwoPowAuxa (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩
noncomputable section
open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt HermitianMat Real
open PrimitiveGate (TOFF T)
open scoped Matrix ComplexOrder MatrixOrder BigOperators Matrix.Norms.L2Operator
open SpecsAux
open SpecsAux.SpecMirror
-- Root solution namespace already active.
open MeasureBranchHadamardSem (bit_cases matrix_ext_ket RealizesCleanUnitary)
open StreamingBchComparator (PreservesStoreConst)
open MomSlots35Slot3ProjNuclear (shellMu3 shellMu3_lt_seven)
open StepBBlock0 (TempCtxLiftEx padZeroBits149_clean seqClean_spec bitsVal_injective)
open Prod57BoothHoist
open StepBOuter
open Slot3Exact216Oracle80 (sTrue18WDefault216_bounds top7_eq_shellMu3_216)
open Slot3Outer2344AndRelayWide
open Slot3Outer2344AndRelayWide.PosPhase246 (cliffSupportsBelowB progSupportsBelowB
  ctxSupportsBelowB truncateCliffB truncateProgB truncateCtxB truncateProgB_countTempAnd
  truncateCtxB_countTempAnd ctxSupportsBelowB_plug truncateCtxB_plug truncateCtxB_fwdBits
  truncateProgB_evalBits truncateProgB_evalSign truncateProgB_validCleanRem castAssign castAssign_lt
  cleanRem_castAssign_iff)
open Slot3Outer2344AndRelayWide.Slot3MidKickWidthWide (truncateProgB_onRegister_eq cliffDisjointBad
  progDisjointBad progDisjointBad_eval permOfInvol permReg st0 st1)
open Slot3Outer2344AndRelayWide.Slot3RevUncompDynPruned (InvAxis1 InvAxis1_congr)
open Slot3ZRetCore
open True18Compact99
open Slot3Norm1s36_161w (Norm1sTier)
open Slot3Norm1s36CoreWide
open Leaf3Slot3ZRet193
open Leaf3Slot3ZRetOuter
open STrue18Compact113
/-- Involutive wire relay mapping clean retained wires `[201 .. 201 + (388 - topW))`
onto `[topW .. 388)` for `338 ≤ topW ∧ topW ≤ 388` (`topW ∈ {339, 342}`). -/
def swap388 (topW x : ℕ) : ℕ :=
  if 201 ≤ x ∧ x < 201 + (388 - topW) then topW + (x - 201)
  else if topW ≤ x ∧ x < 388 then 201 + (x - topW)
  else x
/-- Bad-wire predicate for `swap388 topW`, marking `[201 .. 201 + (388 - topW))`. -/
def isBad388 (topW x : ℕ) : Bool :=
  decide (201 ≤ x ∧ x < 201 + (388 - topW))
theorem swap388_involutive {topW : ℕ} (hlo : 338 ≤ topW) (hhi : topW ≤ 388) (x : ℕ) :
    swap388 topW (swap388 topW x) = x := by
  unfold swap388
  split_ifs with h1 h2 h3 h4 h5 <;> omega
theorem swap388_bad_ge_topW {topW x : ℕ} (hlo : 338 ≤ topW) (hhi : topW ≤ 388)
    (hbad : isBad388 topW x = true) :
    topW ≤ swap388 topW x ∧ swap388 topW x < 388 := by
  simp only [isBad388, decide_eq_true_eq] at hbad
  unfold swap388
  (split_ifs; omega)
theorem swap388_out_lt_topW {topW x : ℕ} (hlo : 338 ≤ topW) (hhi : topW ≤ 388)
    (hge : topW ≤ x) (hlt : x < 388) :
    isBad388 topW (swap388 topW x) = true ∧ swap388 topW x < topW := by
  simp only [isBad388, decide_eq_true_eq]
  unfold swap388
  split_ifs <;> omega
theorem swap388_fix_good {topW x : ℕ} (_hlo : 338 ≤ topW) (_hhi : topW ≤ 388)
    (hgood : isBad388 topW x = false) (hlt : x < topW) :
    swap388 topW x = x := by
  simp only [isBad388, decide_eq_false_iff_not] at hgood
  unfold swap388
  split_ifs <;> omega
theorem swap388_lt_437 {topW x : ℕ} (hlo : 338 ≤ topW) (hhi : topW ≤ 388) (hx : x < 437) :
    swap388 topW x < 437 := by
  unfold swap388
  split_ifs <;> omega
/-- Bundled `Wire 437` relay permutation for `swap388 topW` (`338 ≤ topW ≤ 388`). -/
def swap388W (topW : ℕ) (hlo : 338 ≤ topW) (hhi : topW ≤ 388) (w : Wire 437) : Wire 437 :=
  ⟨swap388 topW w.val, swap388_lt_437 hlo hhi w.isLt⟩
/-- Bundled `Wire 437` bad-wire mask for `isBad388 topW`. -/
def isBad388W (topW : ℕ) (w : Wire 437) : Bool :=
  isBad388 topW w.val
theorem validSwapRelayWM_388 {topW : ℕ} (hlo : 338 ≤ topW) (hhi : topW ≤ 388) :
    ValidSwapRelayWM topW 388 (swap388W topW hlo hhi) (isBad388W topW) where
  h275 := by omega
  htopM := hhi
  hM437 := by decide
  invol w := Fin.ext (swap388_involutive hlo hhi w.val)
  fix_ge_M w hw := Fin.ext (by dsimp only [swap388W]; unfold swap388; split_ifs <;> omega)
  fix_not_bad_lt w hlt hnb := Fin.ext (swap388_fix_good hlo hhi hnb hlt)
  bad_lt275 w hb := by
    simp only [isBad388W, isBad388, decide_eq_true_eq] at hb; omega
  bad_swap_range w := by
    constructor
    · exact swap388_bad_ge_topW hlo hhi
    · rintro ⟨h1, h2⟩
      have h := (swap388_out_lt_topW hlo hhi h1 h2).1
      have hinv : swap388 topW (swap388 topW w.val) = w.val := swap388_involutive hlo hhi w.val
      dsimp only [isBad388W]; dsimp only [swap388W] at h; rwa [hinv] at h
  range_swap_bad w := by
    constructor
    · exact fun ⟨h1, h2⟩ ↦ (swap388_out_lt_topW hlo hhi h1 h2).1
    · intro hb
      have h := swap388_bad_ge_topW hlo hhi hb
      have hinv : swap388 topW (swap388 topW w.val) = w.val := swap388_involutive hlo hhi w.val
      dsimp only [swap388W] at h; rwa [hinv] at h
/-!
## Section 2: `388 ↔ 437` Truncation & Lifting, `K_wrapLin_388`, & Phase 0 (`ph0Fwd388` /
`dPh0Rev388`)
-/
/-- `388`-wire `sTrue18` output slice matching `sTrue18WDefault`. -/
def sTrue18W388 (j : Fin 18) : Wire 388 :=
  ⟨(sTrue18WDefault j).val, by revert j; decide⟩
theorem sTrue18W388_injective : Function.Injective sTrue18W388 := fun i j h ↦ by
  apply sTrue18WDefault_injective
  ext; exact congrArg (Fin.val (n := 388)) h
/-- Mutable `18`-wire predicate on `Wire 388`. -/
def mutSTrue388 (q : Wire 388) : Prop := ∃ j : Fin 18, q = sTrue18W388 j
local instance instDecidablePredMutSTrue388 : DecidablePred mutSTrue388 :=
  fun _ ↦ Fintype.decidableExistsFintype
theorem mutSTrue388_iff (q : Wire 388) :
    mutSTrue388 q ↔ mutSTrue ⟨q.val, by omega⟩ := by
  constructor
  · rintro ⟨j, rfl⟩; exact ⟨j, Fin.ext rfl⟩
  · rintro ⟨j, hj⟩; exact ⟨j, Fin.ext (congrArg (Fin.val (n := 437)) hj)⟩
/-- Embed a `388`-wire Clifford program into `437` wires. -/
def padCliff388_437 : CliffProg 388 → CliffProg 437
  | .nil => .nil
  | .x q => .x ⟨q.val, by omega⟩
  | .cnot c t hct =>
      .cnot ⟨c.val, by omega⟩ ⟨t.val, by omega⟩
        (fun h ↦ hct (Fin.ext (congrArg (Fin.val (n := 437)) h)))
  | .seq c₁ c₂ => .seq (padCliff388_437 c₁) (padCliff388_437 c₂)
/-- Embed a `388`-wire `TempPhaseProg` into `437` wires. -/
def padProg388_437 : TempPhaseProg 388 → TempPhaseProg 437
  | .nil => .nil
  | .cliff c => .cliff (padCliff388_437 c)
  | .z q => .z ⟨q.val, by omega⟩
  | .seq p₁ p₂ => .seq (padProg388_437 p₁) (padProg388_437 p₂)
  | .tempAnd c₁ c₂ anc h₁₂ h₁a h₂a body =>
      .tempAnd ⟨c₁.val, by omega⟩ ⟨c₂.val, by omega⟩ ⟨anc.val, by omega⟩
        (fun h ↦ h₁₂ (Fin.ext (congrArg (Fin.val (n := 437)) h)))
        (fun h ↦ h₁a (Fin.ext (congrArg (Fin.val (n := 437)) h)))
        (fun h ↦ h₂a (Fin.ext (congrArg (Fin.val (n := 437)) h)))
        (padProg388_437 body)
theorem cliffSupportsBelowB_padCliff388_437 :
    ∀ c : CliffProg 388, cliffSupportsBelowB 388 (padCliff388_437 c) = true
  | .nil => rfl
  | .x q => decide_eq_true q.isLt
  | .cnot c t _ => Bool.and_eq_true _ _ |>.mpr ⟨decide_eq_true c.isLt, decide_eq_true t.isLt⟩
  | .seq c₁ c₂ =>
      Bool.and_eq_true _ _ |>.mpr
        ⟨cliffSupportsBelowB_padCliff388_437 c₁, cliffSupportsBelowB_padCliff388_437 c₂⟩
theorem progSupportsBelowB_padProg388_437 :
    ∀ p : TempPhaseProg 388, progSupportsBelowB 388 (padProg388_437 p) = true
  | .nil => rfl
  | .cliff c => cliffSupportsBelowB_padCliff388_437 c
  | .z q => decide_eq_true q.isLt
  | .seq p₁ p₂ =>
      Bool.and_eq_true _ _ |>.mpr
        ⟨progSupportsBelowB_padProg388_437 p₁, progSupportsBelowB_padProg388_437 p₂⟩
  | .tempAnd c₁ c₂ anc _ _ _ body =>
      Bool.and_eq_true _ _ |>.mpr ⟨decide_eq_true c₁.isLt,
        Bool.and_eq_true _ _ |>.mpr ⟨decide_eq_true c₂.isLt,
          Bool.and_eq_true _ _ |>.mpr ⟨decide_eq_true anc.isLt,
            progSupportsBelowB_padProg388_437 body⟩⟩⟩
theorem truncateCliffB_padCliff388_437 :
    ∀ (c : CliffProg 388) (hc : cliffSupportsBelowB 388 (padCliff388_437 c) = true),
      truncateCliffB 388 (padCliff388_437 c) hc = c
  | .nil, _ => rfl
  | .x _, _ => rfl
  | .cnot _ _ _, _ => rfl
  | .seq c₁ c₂, _ => by
      dsimp only [padCliff388_437, truncateCliffB]
      rw [truncateCliffB_padCliff388_437 c₁, truncateCliffB_padCliff388_437 c₂]
theorem truncateProgB_padProg388_437 :
    ∀ (p : TempPhaseProg 388) (hp : progSupportsBelowB 388 (padProg388_437 p) = true),
      truncateProgB 388 (padProg388_437 p) hp = p
  | .nil, _ => rfl
  | .cliff c, hc => by
      dsimp only [padProg388_437, truncateProgB]
      rw [truncateCliffB_padCliff388_437 c hc]
  | .z _, _ => rfl
  | .seq p₁ p₂, _ => by
      dsimp only [padProg388_437, truncateProgB]
      rw [truncateProgB_padProg388_437 p₁, truncateProgB_padProg388_437 p₂]
  | .tempAnd _ _ _ _ _ _ body, _ => by
      dsimp only [padProg388_437, truncateProgB]
      rw [truncateProgB_padProg388_437 body]
theorem padProg388_437_countTempAnd (p : TempPhaseProg 388) :
    (padProg388_437 p).countTempAnd = p.countTempAnd := by
  have h := truncateProgB_countTempAnd (padProg388_437 p) (progSupportsBelowB_padProg388_437 p)
  rw [truncateProgB_padProg388_437] at h
  exact h.symm
theorem padProg388_437_onRegister_eq {n : ℕ} (r : QRegister 437 n) (p : TempPhaseProg 388) :
    (padProg388_437 p).onRegister r =
      p.onRegister (r.compose (QRegister.block 0 388 (by decide))) := by
  have h := truncateProgB_onRegister_eq (by decide : 0 + 388 ≤ 437) r
    (padProg388_437 p) (progSupportsBelowB_padProg388_437 p)
  rw [truncateProgB_padProg388_437] at h
  exact h.symm
theorem cliffDisjointBad_of_supportsBelow388 {bad : Wire 437 → Bool}
    (hbad : ∀ w : Wire 437, w.val < 388 → bad w = false) :
    ∀ (c : CliffProg 437), cliffSupportsBelowB 388 c = true → cliffDisjointBad bad c = true
  | .nil, _ => rfl
  | .x q, hq => by
      dsimp only [cliffDisjointBad]
      rw [hbad q (of_decide_eq_true hq)]; rfl
  | .cnot c t _, h => by
      obtain ⟨hc, ht⟩ := Bool.and_eq_true _ _ |>.mp h
      dsimp only [cliffDisjointBad]
      rw [hbad c (of_decide_eq_true hc), hbad t (of_decide_eq_true ht)]; rfl
  | .seq c₁ c₂, h => by
      obtain ⟨h1, h2⟩ := Bool.and_eq_true _ _ |>.mp h
      exact Bool.and_eq_true _ _ |>.mpr
        ⟨cliffDisjointBad_of_supportsBelow388 hbad c₁ h1,
          cliffDisjointBad_of_supportsBelow388 hbad c₂ h2⟩
theorem progDisjointBad_of_supportsBelow388 {bad : Wire 437 → Bool}
    (hbad : ∀ w : Wire 437, w.val < 388 → bad w = false) :
    ∀ (p : TempPhaseProg 437), progSupportsBelowB 388 p = true → progDisjointBad bad p = true
  | .nil, _ => rfl
  | .cliff c, hc => cliffDisjointBad_of_supportsBelow388 hbad c hc
  | .z q, hq => by
      dsimp only [progDisjointBad]
      rw [hbad q (of_decide_eq_true hq)]; rfl
  | .seq p₁ p₂, h => by
      obtain ⟨h1, h2⟩ := Bool.and_eq_true _ _ |>.mp h
      exact Bool.and_eq_true _ _ |>.mpr
        ⟨progDisjointBad_of_supportsBelow388 hbad p₁ h1,
          progDisjointBad_of_supportsBelow388 hbad p₂ h2⟩
  | .tempAnd c₁ c₂ anc _ _ _ body, h => by
      obtain ⟨h1, hr1⟩ := Bool.and_eq_true _ _ |>.mp h
      obtain ⟨h2, hr2⟩ := Bool.and_eq_true _ _ |>.mp hr1
      obtain ⟨h3, hbody⟩ := Bool.and_eq_true _ _ |>.mp hr2
      dsimp only [progDisjointBad]
      rw [hbad c₁ (of_decide_eq_true h1), hbad c₂ (of_decide_eq_true h2),
        hbad anc (of_decide_eq_true h3),
        progDisjointBad_of_supportsBelow388 hbad body hbody]
      rfl
theorem padProg388_437_validCleanRem {rem : ℕ} (hrem : rem ≤ 388) (p : TempPhaseProg 388)
    (hv : ValidCleanRem 388 rem p) :
    ValidCleanRem 437 (rem + 49) (padProg388_437 p) := by
  induction p generalizing rem with
  | nil => trivial
  | cliff _ => trivial
  | z _ => trivial
  | seq p₁ p₂ ih₁ ih₂ =>
      obtain ⟨remMid, hmid, hv₁, hv₂, hpres⟩ := hv
      refine ⟨remMid + 49, by omega, ih₁ hrem hv₁, ih₂ hmid hv₂, fun γ hγ ↦ ?_⟩
      let β : BitAssignment 388 := fun w ↦ γ ⟨w.val, by omega⟩
      have hEq0 : ∀ w : Wire 437, decide (388 ≤ w.val) = false → γ w = castAssign (M := 437) β w :=
        fun w hw ↦ by
          have hlt : w.val < 388 := Nat.lt_of_not_le (of_decide_eq_false hw)
          exact (castAssign_lt β w hlt).symm
      have hd1 := progDisjointBad_of_supportsBelow388 (bad := fun w ↦ decide (388 ≤ w.val))
        (fun w hw ↦ decide_eq_false (by
          omega)) (padProg388_437 p₁) (progSupportsBelowB_padProg388_437 p₁)
      obtain ⟨_, hEq1, hTop1⟩ :=
        progDisjointBad_eval _ (padProg388_437 p₁) hd1 γ (castAssign β) hEq0
      have hβ : cleanRem 388 rem β := fun u hu ↦ hγ ⟨u.val, by omega⟩ (by dsimp; omega)
      have hclMid := hpres β hβ
      intro w hw
      by_cases hlt : w.val < 388
      · rw [hEq1 w (decide_eq_false (by omega))]
        have htr := truncateProgB_evalBits (by decide : 388 ≤ 437)
          (padProg388_437 p₁) (progSupportsBelowB_padProg388_437 p₁) β
        rw [truncateProgB_padProg388_437] at htr
        rw [← congrFun htr w, castAssign_lt _ w hlt]
        exact hclMid ⟨w.val, hlt⟩ (by dsimp; omega)
      · rw [hTop1 w (decide_eq_true (by omega))]
        exact hγ w (by omega)
  | tempAnd c₁ c₂ anc h₁₂ h₁a h₂a body ih =>
      obtain ⟨hanc_lo, hvBody, hpresBody⟩ := hv
      have hremB : 388 - (anc.val + 1) ≤ 388 := by omega
      have ihB := ih hremB hvBody
      have h49 : (388 - (anc.val + 1)) + 49 = 437 - (anc.val + 1) := by omega
      rw [h49] at ihB
      refine ⟨by dsimp; omega, ihB, fun γ₁ hγ₁ ↦ ?_⟩
      let β₁ : BitAssignment 388 := fun w ↦ γ₁ ⟨w.val, by omega⟩
      have hEq0 : ∀ w : Wire 437, decide (388 ≤ w.val) = false →
          γ₁ w = castAssign (M := 437) β₁ w :=
        fun w hw ↦ by
          have hlt : w.val < 388 := Nat.lt_of_not_le (of_decide_eq_false hw)
          exact (castAssign_lt β₁ w hlt).symm
      have hdB := progDisjointBad_of_supportsBelow388 (bad := fun w ↦ decide (388 ≤ w.val))
        (fun w hw ↦ decide_eq_false (by omega))
        (padProg388_437 body) (progSupportsBelowB_padProg388_437 body)
      obtain ⟨_, hEqB, _⟩ :=
        progDisjointBad_eval _ (padProg388_437 body) hdB γ₁ (castAssign β₁) hEq0
      have hβ₁ : cleanRem 388 (388 - (anc.val + 1)) β₁ :=
        fun u hu ↦ hγ₁ ⟨u.val, by omega⟩ (by dsimp; omega)
      obtain ⟨hp1, hp2, hp3⟩ := hpresBody β₁ hβ₁
      have htr := truncateProgB_evalBits (by decide : 388 ≤ 437)
        (padProg388_437 body) (progSupportsBelowB_padProg388_437 body) β₁
      rw [truncateProgB_padProg388_437] at htr
      have evalAt (u : Wire 388) :
          (padProg388_437 body).evalBits γ₁ ⟨u.val, by omega⟩ = (body.evalBits β₁) u := by
        let u437 : Wire 437 := ⟨u.val, by omega⟩
        calc (padProg388_437 body).evalBits γ₁ u437
            = (padProg388_437 body).evalBits (castAssign β₁) u437 :=
              hEqB u437 (decide_eq_false (by dsimp [u437]; omega))
          _ = castAssign (body.evalBits β₁) u437 := (congrFun htr u437).symm
          _ = (body.evalBits β₁) u := castAssign_lt (body.evalBits β₁) u437 u.isLt
      exact ⟨(evalAt c₁).trans hp1, (evalAt c₂).trans hp2, (evalAt anc).trans hp3⟩
/-- `388`-wire prefix restriction of a `437`-wire bit assignment. -/
def truncAssign388 (β : BitAssignment 437) : BitAssignment 388 :=
  fun w ↦ β ⟨w.val, by omega⟩
theorem padProg388_437_eval (p : TempPhaseProg 388) (β : BitAssignment 437) :
    (padProg388_437 p).evalSign β = p.evalSign (truncAssign388 β) ∧
      (∀ w : Wire 437, ∀ hlt : w.val < 388,
        (padProg388_437 p).evalBits β w = p.evalBits (truncAssign388 β) ⟨w.val, hlt⟩) ∧
      (∀ w : Wire 437, 388 ≤ w.val → (padProg388_437 p).evalBits β w = β w) := by
  have hEq0 : ∀ w : Wire 437, decide (388 ≤ w.val) = false →
      β w = castAssign (M := 437) (truncAssign388 β) w := fun w hw ↦ by
    have hlt : w.val < 388 := Nat.lt_of_not_le (of_decide_eq_false hw)
    exact (castAssign_lt (truncAssign388 β) w hlt).symm
  have hd := progDisjointBad_of_supportsBelow388 (bad := fun w ↦ decide (388 ≤ w.val))
    (fun w hw ↦ decide_eq_false (by omega)) (padProg388_437 p) (progSupportsBelowB_padProg388_437 p)
  obtain ⟨hsgn, hEq1, hTop1⟩ :=
    progDisjointBad_eval _ (padProg388_437 p) hd β (castAssign (truncAssign388 β)) hEq0
  have htrS := truncateProgB_evalSign (by decide : 388 ≤ 437)
    (padProg388_437 p) (progSupportsBelowB_padProg388_437 p) (truncAssign388 β)
  have htrB := truncateProgB_evalBits (by decide : 388 ≤ 437)
    (padProg388_437 p) (progSupportsBelowB_padProg388_437 p) (truncAssign388 β)
  rw [truncateProgB_padProg388_437] at htrS htrB
  refine ⟨hsgn.trans htrS.symm, fun w hlt ↦ ?_, fun w hge ↦ hTop1 w (decide_eq_true hge)⟩
  rw [hEq1 w (decide_eq_false (by omega)), ← congrFun htrB w, castAssign_lt _ w hlt]
theorem truncateCliffB_disjointFrom_sTrue388 :
    ∀ (c : CliffProg 437) (hc : cliffSupportsBelowB 388 c = true),
      CliffDisjoint mutSTrue c → CliffDisjoint mutSTrue388 (truncateCliffB 388 c hc)
  | .nil, _, _ => trivial
  | .x _, _, hd => fun h ↦ hd ((mutSTrue388_iff _).mp h)
  | .cnot _ _ _, _, ⟨hdc, hdt⟩ =>
      ⟨fun hc' ↦ hdc ((mutSTrue388_iff _).mp hc'),
        fun ht' ↦ hdt ((mutSTrue388_iff _).mp ht')⟩
  | .seq c₁ c₂, _, ⟨hd₁, hd₂⟩ =>
      ⟨truncateCliffB_disjointFrom_sTrue388 c₁ _ hd₁,
        truncateCliffB_disjointFrom_sTrue388 c₂ _ hd₂⟩
theorem truncateCtxB_disjointFrom_sTrue388 :
    ∀ (K : TempCtx 437) (hK : ctxSupportsBelowB 388 K = true),
      K.DisjointFrom mutSTrue → (truncateCtxB 388 K hK).DisjointFrom mutSTrue388
  | .hole, _, _ => trivial
  | .seqPre c K, _, ⟨hd₁, hd₂⟩ =>
      ⟨truncateCliffB_disjointFrom_sTrue388 c _ hd₁, truncateCtxB_disjointFrom_sTrue388 K _ hd₂⟩
  | .seqPost K c, _, ⟨hd₁, hd₂⟩ =>
      ⟨truncateCtxB_disjointFrom_sTrue388 K _ hd₁, truncateCliffB_disjointFrom_sTrue388 c _ hd₂⟩
  | .tempAnd _ _ _ _ _ _ K, _, ⟨h1, h2, h3, hdK⟩ =>
      ⟨fun x ↦ h1 ((mutSTrue388_iff _).mp x),
        fun x ↦ h2 ((mutSTrue388_iff _).mp x),
        fun x ↦ h3 ((mutSTrue388_iff _).mp x),
        truncateCtxB_disjointFrom_sTrue388 K _ hdK⟩
theorem truncateCliffB_supportsBelow388 {bound : ℕ} :
    ∀ (c : CliffProg 437) (hc : cliffSupportsBelowB 388 c = true),
      c.SupportsBelow bound → (truncateCliffB 388 c hc).SupportsBelow bound
  | .nil, _, _ => trivial
  | .x _, _, hs => hs
  | .cnot _ _ _, _, ⟨hs1, hs2⟩ => ⟨hs1, hs2⟩
  | .seq c₁ c₂, _, ⟨hs1, hs2⟩ =>
      ⟨truncateCliffB_supportsBelow388 c₁ _ hs1, truncateCliffB_supportsBelow388 c₂ _ hs2⟩
theorem truncateCtxB_supportsBelowCtx388 {bound : ℕ} :
    ∀ (K : TempCtx 437) (hK : ctxSupportsBelowB 388 K = true),
      K.SupportsBelowCtx bound → (truncateCtxB 388 K hK).SupportsBelowCtx bound
  | .hole, _, _ => trivial
  | .seqPre c K, _, ⟨hs1, hs2⟩ =>
      ⟨truncateCliffB_supportsBelow388 c _ hs1, truncateCtxB_supportsBelowCtx388 K _ hs2⟩
  | .seqPost K c, _, ⟨hs1, hs2⟩ =>
      ⟨truncateCtxB_supportsBelowCtx388 K _ hs1, truncateCliffB_supportsBelow388 c _ hs2⟩
  | .tempAnd _ _ _ _ _ _ K, _, ⟨hs1, hs2⟩ =>
      ⟨hs1, truncateCtxB_supportsBelowCtx388 K _ hs2⟩
/-- `388`-wire context package extracted from `P57CtxPkg` via `truncateCtxB 388`. -/
structure CtxPkg388 (cur₀ cur₁ cnt : ℕ) (K : TempCtx 388) : Prop where
  cnt_eq : K.countTempAnd = cnt
  disj : K.DisjointFrom mutSTrue388
  supp : K.SupportsBelowCtx cur₁
  probe : ∀ q : Wire 388, ScopedBlock 388 (388 - cur₀) K.fwdBits (.z q) (K.plug (.z q))
  clean : ∀ β : BitAssignment 388,
    cleanRem 388 (388 - cur₀) β → cleanRem 388 (388 - cur₁) (K.fwdBits β)
theorem toCtxPkg388 {cur₀ cur₁ cnt : ℕ} {K : TempCtx 437}
    (hpkg : P57CtxPkg cur₀ cur₁ cnt K) (hc₀ : cur₀ ≤ cur₁) (hc₁ : cur₁ ≤ 388)
    (hK : ctxSupportsBelowB 388 K = true) :
    CtxPkg388 cur₀ cur₁ cnt (truncateCtxB 388 K hK) where
  cnt_eq := (truncateCtxB_countTempAnd K hK).trans hpkg.cnt_eq
  disj := truncateCtxB_disjointFrom_sTrue388 K hK hpkg.disj
  supp := truncateCtxB_supportsBelowCtx388 K hK hpkg.supp
  probe q := by
    let q437 : Wire 437 := ⟨q.val, by omega⟩
    have hqB : progSupportsBelowB 388 (.z q437) = true := decide_eq_true q.isLt
    have hPlug : (truncateCtxB 388 K hK).plug (.z q) =
        truncateProgB 388 (K.plug (.z q437)) (ctxSupportsBelowB_plug hK hqB) :=
      truncateCtxB_plug K hK (.z q437) hqB
    have hBlk := StepBBlock0.TempCtxLiftEx.probe hpkg.lift q437
    have hrem₀ : (437 - cur₀) - (437 - 388) = 388 - cur₀ := by omega
    refine ⟨?_, fun β hβ ↦ ?_, fun β _ ↦ (truncateCtxB 388 K hK).plug_evalSign (.z q) β⟩
    · rw [hPlug]
      have hv := truncateProgB_validCleanRem (by decide : 388 ≤ 437)
        (K.plug (.z q437)) (ctxSupportsBelowB_plug hK hqB) (437 - cur₀) hBlk.valid
      rwa [hrem₀] at hv
    · rw [hPlug]
      have hcl437 : cleanRem 437 (437 - cur₀) (castAssign β) := by
        apply (cleanRem_castAssign_iff (by decide : 388 ≤ 437) (437 - cur₀) β).mp
        rwa [hrem₀]
      have hev := truncateProgB_evalBits (by decide : 388 ≤ 437)
        (K.plug (.z q437)) (ctxSupportsBelowB_plug hK hqB) β
      funext u
      let u437 : Wire 437 := ⟨u.val, by omega⟩
      exact (castAssign_lt _ u437 u.isLt).symm.trans
        ((congrFun hev u437).trans
          ((congrFun (hBlk.bits (castAssign β) hcl437) u437).trans
            (castAssign_lt β u437 u.isLt)))
  clean β hβ := by
    have hrem₀ : (437 - cur₀) - (437 - 388) = 388 - cur₀ := by omega
    have hrem₁ : (437 - cur₁) - (437 - 388) = 388 - cur₁ := by omega
    have hcl437 : cleanRem 437 (437 - cur₀) (castAssign β) := by
      apply (cleanRem_castAssign_iff (by decide : 388 ≤ 437) (437 - cur₀) β).mp
      rwa [hrem₀]
    have hclOut := hpkg.clean (castAssign β) hcl437
    rw [← truncateCtxB_fwdBits (by decide : 388 ≤ 437) K hK β,
      ← cleanRem_castAssign_iff (by decide : 388 ≤ 437) (437 - cur₁)] at hclOut
    rwa [hrem₁] at hclOut
/-- `388`-wire truncation of `0`-`TempAnd` linear wrap context `K_wrapLin` (`275 -> 278`). -/
def K_wrapLin_388 : TempCtx 388 :=
  truncateCtxB 388 K_wrapLin (by decide)
theorem K_wrapLin_388_pkg : CtxPkg388 275 278 0 K_wrapLin_388 :=
  toCtxPkg388 K_wrapLin_pkg (by decide) (by decide) (by decide)
theorem d8Wire_lt388 (w : Fin 3) (k : Fin 8) : (d8Wire w k).val < 388 := by
  revert w k; decide
theorem d8Wire_not_mutSTrue388 (w : Fin 3) (k : Fin 8) :
    ¬ mutSTrue388 ⟨(d8Wire w k).val, d8Wire_lt388 w k⟩ := by
  revert w k; decide
/-- `8`-bit axis magnitude read on `388`-wire assignment `δ` after `K_wrapLin_388`. -/
def dVal388 (w : Fin 3) (δ : BitAssignment 388) : ℕ :=
  bitsVal (fun k : Fin 8 ↦ δ ⟨(d8Wire w k).val, d8Wire_lt388 w k⟩)
theorem dVal388_mod_two (w : Fin 3) (δ : BitAssignment 388) :
    dVal388 w δ % 2 = (δ ⟨(d8Wire w 0).val, d8Wire_lt388 w 0⟩).val := by
  unfold dVal388
  rw [bitsVal_succ_split]
  have hlt : (δ ⟨(d8Wire w 0).val, d8Wire_lt388 w 0⟩).val < 2 := ZMod.val_lt _
  omega
theorem dVal388_sq_div4_le (w : Fin 3) (δ : BitAssignment 388) :
    (dVal388 w δ * dVal388 w δ) / 4 ≤ 16256 := by
  have hd : dVal388 w δ < 256 := bitsVal_lt_two_pow _
  have hsq : dVal388 w δ * dVal388 w δ ≤ 255 * 255 := Nat.mul_le_mul (by omega) (by omega)
  omega
/-- `388`-wire squared-displacement sum at `.hole` of `K_wrapLin_388`. -/
theorem sq_eq_mod_two_add_four_div (d : ℕ) :
    d * d = d % 2 + 4 * ((d * d) / 4) := by
  have hq := Nat.div_add_mod d 2
  rcases (by omega : d % 2 = 0 ∨ d % 2 = 1) with hr | hr <;> {
    have hsq : d * d = 4 * ((d / 2) * (d / 2) + (d / 2) * (d % 2)) + (d % 2) * (d % 2) := by
      nlinarith
    rw [hr] at hsq ⊢
    omega
  }

def sTrueRawVal388 (γ : BitAssignment 388) : ℕ :=
  dVal388 0 γ * dVal388 0 γ + dVal388 1 γ * dVal388 1 γ + dVal388 2 γ * dVal388 2 γ
theorem sTrueRawVal388_split (γ : BitAssignment 388) :
    sTrueRawVal388 γ =
      (dVal388 0 γ % 2 + dVal388 1 γ % 2 + dVal388 2 γ % 2) +
        4 * ((dVal388 0 γ * dVal388 0 γ) / 4 + (dVal388 1 γ * dVal388 1 γ) / 4 +
          (dVal388 2 γ * dVal388 2 γ) / 4) := by
  unfold sTrueRawVal388
  have h0 := sq_eq_mod_two_add_four_div (dVal388 0 γ)
  have h1 := sq_eq_mod_two_add_four_div (dVal388 1 γ)
  have h2 := sq_eq_mod_two_add_four_div (dVal388 2 γ)
  omega
theorem castAssign_truncAssign388 (β : BitAssignment 437) (w : Wire 437)
    (hw : w.val < 388) :
    castAssign (truncAssign388 β) w = β w :=
  (castAssign_lt (truncAssign388 β) w hw).trans (congrArg β (Fin.ext rfl))
theorem invWrapLin_castAssign_trunc388 {β : BitAssignment 437} (hW : InvWrapLin β) :
    InvWrapLin (castAssign (truncAssign388 β)) := fun w ↦ by
  have hp0 : (p57ProjW w 0).val < 388 := by revert w; decide
  have hb0 : (p57PBufW w 0).val < 388 := by revert w; decide
  have hm0 : (p57MW w 0).val < 388 := by revert w; decide
  have hp7 : (p57ProjW w ⟨7, by decide⟩).val < 388 := by revert w; decide
  have hb7 : (p57PBufW w ⟨7, by decide⟩).val < 388 := by revert w; decide
  have hs3 : (p57S3W w).val < 388 := by revert w; decide
  rw [castAssign_truncAssign388 β _ hp0, castAssign_truncAssign388 β _ hb0,
    castAssign_truncAssign388 β _ hm0, castAssign_truncAssign388 β _ hp7,
    castAssign_truncAssign388 β _ hb7, castAssign_truncAssign388 β _ hs3]
  exact hW w
theorem sTrueRawValPBuf_castAssign_trunc388 (β : BitAssignment 437) :
    sTrueRawValPBuf (castAssign (truncAssign388 β)) = sTrueRawValPBuf β := by
  unfold sTrueRawValPBuf
  refine Finset.sum_congr rfl fun w _ ↦ ?_
  have hp7 : (p57ProjW w ⟨7, by decide⟩).val < 388 := by revert w; decide
  have hb7 : (p57PBufW w ⟨7, by decide⟩).val < 388 := by revert w; decide
  have hs3 : (p57S3W w).val < 388 := by revert w; decide
  have hmw : (fun b : Fin 7 ↦ castAssign (truncAssign388 β) (p57MW w b)) =
      fun b ↦ β (p57MW w b) :=
    funext fun b ↦ castAssign_truncAssign388 β _
      (((show ∀ (w' : Fin 3) (b' : Fin 7), (p57MW w' b').val < 388 by decide) w b))
  rw [castAssign_truncAssign388 β _ hp7, castAssign_truncAssign388 β _ hb7,
    castAssign_truncAssign388 β _ hs3, hmw]
theorem sTrueRawVal388_eq_sTrueRawValPBuf {β : BitAssignment 437}
    (hβ : cleanRem 388 (388 - 275) (truncAssign388 β)) (hW : InvWrapLin β) :
    sTrueRawVal388 (K_wrapLin_388.fwdBits (truncAssign388 β)) = sTrueRawValPBuf β := by
  let β₀ : BitAssignment 437 := castAssign (truncAssign388 β)
  have hcl₀ : cleanRem 437 (437 - 275) β₀ :=
    (cleanRem_castAssign_iff (by decide : 388 ≤ 437) (437 - 275) (truncAssign388 β)).mp hβ
  have hLinEq : K_wrapLin.fwdBits β₀ = K_wrap.fwdBits β₀ :=
    K_wrapLin_fwdBits_eq β₀ hcl₀ (invWrapLin_castAssign_trunc388 hW)
  have hTr : castAssign (M := 437) (K_wrapLin_388.fwdBits (truncAssign388 β)) =
      K_wrapLin.fwdBits β₀ :=
    truncateCtxB_fwdBits (by decide : 388 ≤ 437) K_wrapLin (by decide) (truncAssign388 β)
  obtain ⟨_, hd_wrap⟩ := K_wrap_spec β₀ hcl₀
  have hdEq : ∀ w : Fin 3,
      dVal388 w (K_wrapLin_388.fwdBits (truncAssign388 β)) =
        bitsVal (fun k : Fin 8 ↦ (K_wrap.fwdBits β₀) (d8Wire w k)) := fun w ↦ by
    unfold dVal388
    refine congrArg bitsVal (funext fun k ↦ ?_)
    have h1 := (castAssign_lt (M := 437) (K_wrapLin_388.fwdBits (truncAssign388 β))
      (d8Wire w k) (d8Wire_lt388 w k)).symm
    exact h1.trans (congrFun (hTr.trans hLinEq) (d8Wire w k))
  unfold sTrueRawVal388
  rw [hdEq 0, hdEq 1, hdEq 2, hd_wrap 0, hd_wrap 1, hd_wrap 2,
    ← sTrueRawValPBuf_castAssign_trunc388 β]
  unfold sTrueRawValPBuf
  rw [Fin.sum_univ_three]
/-- Axis `0` LSB wire `177` on `Wire 388`. -/
def ph0X0_388 : Wire 388 := ⟨177, by decide⟩
/-- Axis `1` LSB wire `184` on `Wire 388`. -/
def ph0X1_388 : Wire 388 := ⟨184, by decide⟩
/-- Axis `2` LSB wire `191` on `Wire 388`. -/
def ph0X2_388 : Wire 388 := ⟨191, by decide⟩
/-- Phase 0 LSB XOR Clifford `sTrue18[0] ⊕= d_0[0] + d_1[0] + d_2[0]` on `Wire 388`. -/
def ph0XorCliff388 : CliffProg 388 :=
  cXor3M ph0X0_388 ph0X1_388 ph0X2_388 (sTrue18W388 0) (by decide) (by decide) (by decide)
/-- Phase 0 majority `TempPhaseProg` `sTrue18[1] ⊕= maj(d_0[0], d_1[0], d_2[0])` at `cur = 278`. -/
def ph0MajProg388 : TempPhaseProg 388 :=
  apexMajAt 278 (by decide) ph0X0_388 ph0X1_388 ph0X2_388 (sTrue18W388 1)
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
/-- Phase 0 forward `1`-`TempAnd` program setting `sTrue18[0..1] = d_0 % 2 + d_1 % 2 + d_2 % 2`. -/
def ph0Fwd388 : TempPhaseProg 388 :=
  .seq ph0MajProg388 (.cliff ph0XorCliff388)
/-- Phase 0 static reverse `1`-`TempAnd` program clearing `sTrue18[0..1]`. -/
def ph0RevStatic388 : TempPhaseProg 388 :=
  .seq (.cliff ph0XorCliff388) ph0MajProg388
/-- Phase 0 `0-T`, `0`-Toffoli dynamic uncomputer clearing `sTrue18[0..1]`. -/
def dPh0Rev388 {Var : Type} {n : ℕ} (v : Var) (rComb : QRegister 388 n) :
    DynamicCircuit Var n :=
  .seq (.circuit ((ph0XorCliff388.onRegister rComb).toCircuit))
    (dApexMajAt v rComb ph0X0_388 ph0X1_388 ph0X2_388 (sTrue18W388 1)
      (by decide) (by decide) (by decide) (by decide))
/-- Phase 0 reverse invariant `s_0 + 2 * s_1 = d_0 % 2 + d_1 % 2 + d_2 % 2` on `Wire 388`. -/
def InvPh0Rev388 (δ : BitAssignment 388) : Prop :=
  (δ (sTrue18W388 0)).val + 2 * (δ (sTrue18W388 1)).val =
    dVal388 0 δ % 2 + dVal388 1 δ % 2 + dVal388 2 δ % 2
theorem ph0XorCliff388_supportsBelow : ph0XorCliff388.SupportsBelow 278 := by
  dsimp [ph0XorCliff388, cXor3M, ph0X0_388, ph0X1_388, ph0X2_388, sTrue18W388,
    CliffProg.SupportsBelow]
  decide
theorem dPh0Rev388_count_t {Var : Type} {n : ℕ} (v : Var) (rComb : QRegister 388 n) :
    (dPh0Rev388 v rComb).count T = 0 := by
  dsimp only [dPh0Rev388]
  simp [DynamicCircuit.count, dApexMajAt_count_t]
theorem dPh0Rev388_count_toff {Var : Type} {n : ℕ} (v : Var) (rComb : QRegister 388 n) :
    (dPh0Rev388 v rComb).count TOFF = 0 := by
  dsimp only [dPh0Rev388]
  simp [DynamicCircuit.count, dApexMajAt_count_toff]
theorem dPh0Rev388_preservesStore {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    (v : Var) (rComb : QRegister 388 n) :
    PreservesStoreConst (dPh0Rev388 v rComb) :=
  PreservesStoreConst.seq (PreservesStoreConst.circuit _)
    (dApexMajAt_preservesStore v rComb _ _ _ _ _ _ _ _)
theorem ph0Fwd388_spec :
    ValidCleanRem 388 (388 - 278) ph0Fwd388 ∧
      ph0Fwd388.countTempAnd = 1 ∧
      (∀ δ : BitAssignment 388, cleanRem 388 (388 - 278) δ →
        ph0Fwd388.evalSign δ = 0 ∧
        cleanRem 388 (388 - 278) (ph0Fwd388.evalBits δ) ∧
        (∀ u : Wire 388, u ≠ sTrue18W388 0 → u ≠ sTrue18W388 1 →
          ph0Fwd388.evalBits δ u = δ u) ∧
        (δ (sTrue18W388 0) = 0 → δ (sTrue18W388 1) = 0 → InvPh0Rev388 (ph0Fwd388.evalBits δ))) := by
  obtain ⟨hvM, hcM, _, hsM, hbM⟩ := apexMajAt_spec (M := 388) 278 (by decide)
    ph0X0_388 ph0X1_388 ph0X2_388 (sTrue18W388 1)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
  change ValidCleanRem 388 (388 - 278) ph0MajProg388 at hvM
  change ph0MajProg388.countTempAnd = 1 at hcM
  have hvAll : ValidCleanRem 388 (388 - 278) ph0Fwd388 :=
    ⟨388 - 278, by decide, hvM, trivial, fun δ hδ ↦ (hbM δ hδ).1⟩
  refine ⟨hvAll, by dsimp [ph0Fwd388, TempPhaseProg.countTempAnd]; rw [hcM], fun δ hδ ↦ ?_⟩
  obtain ⟨hcl1, heq1⟩ := hbM δ hδ
  change ph0MajProg388.evalBits δ = _ at heq1
  have hev : ph0Fwd388.evalBits δ =
      Function.update
        (Function.update δ (sTrue18W388 1)
          (δ (sTrue18W388 1) + (δ ph0X0_388 + (δ ph0X1_388 + δ ph0X0_388) * (δ ph0X2_388 +
            δ ph0X0_388))))
        (sTrue18W388 0)
        (δ (sTrue18W388 0) + (δ ph0X0_388 + δ ph0X1_388 + δ ph0X2_388)) := by
    dsimp only [ph0Fwd388, TempPhaseProg.evalBits, ph0XorCliff388]
    rw [heq1, cXor3M_eval]
    simp only [Function.update_of_ne (by decide : sTrue18W388 0 ≠ sTrue18W388 1),
      Function.update_of_ne (by decide : ph0X0_388 ≠ sTrue18W388 1),
      Function.update_of_ne (by decide : ph0X1_388 ≠ sTrue18W388 1),
      Function.update_of_ne (by decide : ph0X2_388 ≠ sTrue18W388 1)]
  have hnon : ∀ u : Wire 388, u ≠ sTrue18W388 0 → u ≠ sTrue18W388 1 →
      ph0Fwd388.evalBits δ u = δ u := fun u h0 h1 ↦ by
    rw [hev, Function.update_of_ne h0, Function.update_of_ne h1]
  refine ⟨by dsimp [ph0Fwd388, ph0MajProg388, TempPhaseProg.evalSign]; rw [hsM δ hδ]; rfl,
    fun w hw ↦ by
      rw [hnon w
        (wire_ne_of_gt (lt_of_lt_of_le (by decide : (sTrue18W388 0).val < 278) (by omega)))
        (wire_ne_of_gt (lt_of_lt_of_le (by decide : (sTrue18W388 1).val < 278) (by omega)))]
      exact hδ w hw,
    hnon, fun hz0 hz1 ↦ ?_⟩
  dsimp only [InvPh0Rev388]
  have hd_eq : ∀ w : Fin 3, dVal388 w (ph0Fwd388.evalBits δ) = dVal388 w δ := fun w ↦ by
    unfold dVal388
    refine congrArg bitsVal (funext fun k ↦ hnon _ ?_ ?_) <;> (revert w k; decide)
  rw [hd_eq 0, hd_eq 1, hd_eq 2, dVal388_mod_two, dVal388_mod_two, dVal388_mod_two, hev]
  rw [Function.update_self,
    Function.update_of_ne (by decide : sTrue18W388 1 ≠ sTrue18W388 0),
    Function.update_self, hz0, hz1, zero_add, zero_add]
  exact ph0_fwd_val (δ ph0X0_388) (δ ph0X1_388) (δ ph0X2_388)
theorem ph0RevStatic388_spec :
    ValidCleanRem 388 (388 - 278) ph0RevStatic388 ∧
      (∀ r, ValidCleanRem 388 r ph0RevStatic388 → 388 - 278 ≤ r) ∧
      (∀ δ : BitAssignment 388, cleanRem 388 (388 - 278) δ →
        ph0RevStatic388.evalSign δ = 0 ∧
        cleanRem 388 (388 - 278) (ph0RevStatic388.evalBits δ) ∧
        (∀ u : Wire 388, u ≠ sTrue18W388 0 → u ≠ sTrue18W388 1 →
          ph0RevStatic388.evalBits δ u = δ u) ∧
        (InvPh0Rev388 δ →
          ph0RevStatic388.evalBits δ (sTrue18W388 0) = 0 ∧
          ph0RevStatic388.evalBits δ (sTrue18W388 1) = 0)) := by
  obtain ⟨hvM, _, hleM, hsM, hbM⟩ := apexMajAt_spec (M := 388) 278 (by decide)
    ph0X0_388 ph0X1_388 ph0X2_388 (sTrue18W388 1)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
  change ValidCleanRem 388 (388 - 278) ph0MajProg388 at hvM
  have hclPre : ∀ δ : BitAssignment 388, cleanRem 388 (388 - 278) δ →
      cleanRem 388 (388 - 278) (ph0XorCliff388.eval δ) := fun δ hδ w hw ↦ by
    rw [ph0XorCliff388.eval_outside ph0XorCliff388_supportsBelow δ w (by omega)]
    exact hδ w hw
  have hvAll : ValidCleanRem 388 (388 - 278) ph0RevStatic388 :=
    ⟨388 - 278, by decide, trivial, hvM, hclPre⟩
  have hleAll : ∀ r, ValidCleanRem 388 r ph0RevStatic388 → 388 - 278 ≤ r := fun r hr ↦
    validCleanRem_cliff_seq_le (by
      decide : 278 < 388) ph0XorCliff388 ph0XorCliff388_supportsBelow hleM hr
  refine ⟨hvAll, hleAll, fun δ hδ ↦ ?_⟩
  have hcl1 := hclPre δ hδ
  obtain ⟨hcl2, heq2⟩ := hbM (ph0XorCliff388.eval δ) hcl1
  change ph0MajProg388.evalBits (ph0XorCliff388.eval δ) = _ at heq2
  have hev : ph0RevStatic388.evalBits δ =
      Function.update
        (Function.update δ (sTrue18W388 0)
          (δ (sTrue18W388 0) + (δ ph0X0_388 + δ ph0X1_388 + δ ph0X2_388)))
        (sTrue18W388 1)
        (δ (sTrue18W388 1) + (δ ph0X0_388 + (δ ph0X1_388 + δ ph0X0_388) * (δ ph0X2_388 +
          δ ph0X0_388))) := by
    dsimp only [ph0RevStatic388, TempPhaseProg.evalBits]
    rw [heq2]
    dsimp only [ph0XorCliff388]
    rw [cXor3M_eval]
    simp only [Function.update_of_ne (by decide : sTrue18W388 1 ≠ sTrue18W388 0),
      Function.update_of_ne (by decide : ph0X0_388 ≠ sTrue18W388 0),
      Function.update_of_ne (by decide : ph0X1_388 ≠ sTrue18W388 0),
      Function.update_of_ne (by decide : ph0X2_388 ≠ sTrue18W388 0)]
  refine ⟨by
    dsimp [ph0RevStatic388, ph0MajProg388, TempPhaseProg.evalSign, TempPhaseProg.evalBits]
    rw [hsM _ hcl1]; rfl,
    hcl2, fun u h0 h1 ↦ by rw [hev, Function.update_of_ne h1, Function.update_of_ne h0],
    fun hInv ↦ ?_⟩
  dsimp only [InvPh0Rev388] at hInv
  rw [dVal388_mod_two, dVal388_mod_two, dVal388_mod_two] at hInv
  obtain ⟨hs0, hs1⟩ := ph0_sum_bits_eq (δ ph0X0_388) (δ ph0X1_388) (δ ph0X2_388)
    (δ (sTrue18W388 0)) (δ (sTrue18W388 1)) hInv
  rw [hev]
  refine ⟨?_, ?_⟩
  · rw [Function.update_of_ne (by decide : sTrue18W388 0 ≠ sTrue18W388 1),
      Function.update_self, hs0, CharTwo.add_self_eq_zero]
  · rw [Function.update_self, hs1, CharTwo.add_self_eq_zero]
theorem dPh0Rev388_realizes
    {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)]
    (v : Var) (rComb : QRegister 388 n)
    (Inv : BitAssignment 388 → Prop)
    (hInv : ∀ δ : BitAssignment 388, cleanRem 388 (388 - 278) δ → Inv δ → InvPh0Rev388 δ) :
    RealizesCleanUnitary v (p57CleanDiagProj rComb (388 - 278) (by decide) Inv)
      (dPh0Rev388 v rComb)
      ((((ph0RevStatic388.onRegister rComb).toToffCircuit).eval)) := by
  let InvMaj : BitAssignment 388 → Prop := fun δ₁ ↦
    δ₁ (sTrue18W388 1) = δ₁ ph0X0_388 + (δ₁ ph0X1_388 + δ₁ ph0X0_388) * (δ₁ ph0X2_388 +
      δ₁ ph0X0_388)
  have hStep1 : ∀ δ : BitAssignment 388, cleanRem 388 (388 - 278) δ → Inv δ →
      cleanRem 388 (388 - 278) ((TempPhaseProg.cliff ph0XorCliff388).evalBits δ) ∧
        InvMaj ((TempPhaseProg.cliff ph0XorCliff388).evalBits δ) := by
    intro δ hcl hi
    have hInv0 := hInv δ hcl hi
    dsimp only [InvPh0Rev388] at hInv0
    rw [dVal388_mod_two, dVal388_mod_two, dVal388_mod_two] at hInv0
    obtain ⟨_, hs1⟩ := ph0_sum_bits_eq (δ ph0X0_388) (δ ph0X1_388) (δ ph0X2_388)
      (δ (sTrue18W388 0)) (δ (sTrue18W388 1)) hInv0
    refine ⟨fun w hw ↦ by
      rw [TempPhaseProg.evalBits, ph0XorCliff388.eval_outside ph0XorCliff388_supportsBelow δ w (by
        omega)]
      exact hcl w hw, ?_⟩
    dsimp only [InvMaj, TempPhaseProg.evalBits, ph0XorCliff388]
    rw [cXor3M_eval]
    simp only [Function.update_of_ne (by decide : sTrue18W388 1 ≠ sTrue18W388 0),
      Function.update_of_ne (by decide : ph0X0_388 ≠ sTrue18W388 0),
      Function.update_of_ne (by decide : ph0X1_388 ≠ sTrue18W388 0),
      Function.update_of_ne (by decide : ph0X2_388 ≠ sTrue18W388 0)]
    exact hs1
  have hMaj := dApexMajAt_realizes v rComb 278 (by decide)
    ph0X0_388 ph0X1_388 ph0X2_388 (sTrue18W388 1)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    InvMaj (fun _ _ hi ↦ hi)
  change RealizesCleanUnitary v _ _ (((ph0MajProg388.onRegister rComb).toToffCircuit).eval) at hMaj
  have hSeq := RealizesCleanUnitary_seq_asym
    (p57CleanDiagProj_conjTranspose rComb (388 - 278) (by decide) Inv)
    (p57CleanDiagProj_conjTranspose rComb (388 - 278) (by decide) InvMaj)
    (RealizesCleanUnitary.circuit v _ ((ph0XorCliff388.onRegister rComb).toCircuit))
    hMaj (p57SeqClean_prog_inv rComb (.cliff ph0XorCliff388) (by decide) (by decide) hStep1)
  have hMul : ((ph0MajProg388.onRegister rComb).toToffCircuit).eval *
      ((ph0XorCliff388.onRegister rComb).toCircuit).eval =
      ((((ph0RevStatic388.onRegister rComb).toToffCircuit).eval)) := by
    simp [ph0RevStatic388, ph0MajProg388, TempPhaseProg.onRegister, TempPhaseProg.toToffCircuit,
      Circuit.eval_seq]
  dsimp only [dPh0Rev388]
  rwa [hMul] at hSeq
/-!
## Section 3: `107`-`TempAnd` Single-Phase XOR-Complement CSA Context `K_xorSq` (`278 -> 385`)
-/
/-- Read-only shifted Boolean term over `< 278` axis magnitude wires. -/
inductive RoTerm : Type
  | wire (u : ℕ)
  | notW (u : ℕ)
  | xnorW (u v : ℕ)
/-- Operand to an XOR-complement full adder: either a mutable scratch wire or a read-only term. -/
inductive SqOperand : Type
  | mutW (u : ℕ)
  | ro (t : RoTerm)
/-- Schedule operations for `16`-bit modular XOR-complement CSA reduction (`105` ops total). -/
inductive XorSqOp : Type
  | orHa (col a b cout : ℕ)
  | faGen (col a : ℕ) (opB opC : SqOperand) (cout : ℕ)
  | flip15 (a : ℕ)
/-- Computable Boolean equality on `RoTerm`. -/
def RoTerm.beq : RoTerm → RoTerm → Bool
  | .wire u, .wire u' => u == u'
  | .notW u, .notW u' => u == u'
  | .xnorW u v, .xnorW u' v' => (u == u') && (v == v')
  | _, _ => false
theorem RoTerm.beq_eq_true_iff : ∀ a b : RoTerm, RoTerm.beq a b = true ↔ a = b
  | .wire u, .wire u' => by simp [RoTerm.beq]
  | .notW u, .notW u' => by simp [RoTerm.beq]
  | .xnorW u v, .xnorW u' v' => by simp [RoTerm.beq]
  | .wire _, .notW _ => by simp [RoTerm.beq]
  | .wire _, .xnorW _ _ => by simp [RoTerm.beq]
  | .notW _, .wire _ => by simp [RoTerm.beq]
  | .notW _, .xnorW _ _ => by simp [RoTerm.beq]
  | .xnorW _ _, .wire _ => by simp [RoTerm.beq]
  | .xnorW _ _, .notW _ => by simp [RoTerm.beq]
/-- Computable Boolean equality on `(col, wire)` mutable pairs. -/
def eqMut (p q : ℕ × ℕ) : Bool := (p.1 == q.1) && (p.2 == q.2)
theorem eqMut_eq_true_iff (p q : ℕ × ℕ) : eqMut p q = true ↔ p = q := by
  rcases p with ⟨p1, p2⟩; rcases q with ⟨q1, q2⟩
  simp [eqMut]
/-- Computable Boolean equality on `(col, RoTerm)` read-only pairs. -/
def eqRo (p q : ℕ × RoTerm) : Bool := (p.1 == q.1) && RoTerm.beq p.2 q.2
theorem eqRo_eq_true_iff (p q : ℕ × RoTerm) : eqRo p q = true ↔ p = q := by
  rcases p with ⟨p1, p2⟩; rcases q with ⟨q1, q2⟩
  simp [eqRo, RoTerm.beq_eq_true_iff]
/-- Read wire `q` (`0` if `q ≥ 437`) on `437`-wire bit assignment `γ`. -/
def rb437 (q : ℕ) (γ : BitAssignment 437) : ZMod 2 := readBit437 γ q
theorem rb437_lt (γ : BitAssignment 437) {q : ℕ} (hq : q < 437) :
    rb437 q γ = γ ⟨q, hq⟩ := readBit437_lt γ hq
/-- Weighted sum `∑ 2^c * γ[q]` over mutable `(col, wire)` pairs. -/
def mutListSum : List (ℕ × ℕ) → BitAssignment 437 → ℕ
  | [], _ => 0
  | (c, q) :: rest, γ => 2 ^ c * (rb437 q γ).val + mutListSum rest γ
/-- Evaluate a `RoTerm` on `437`-wire bit assignment `γ`. -/
def evalRoTerm (γ : BitAssignment 437) : RoTerm → ZMod 2
  | .wire u => rb437 u γ
  | .notW u => 1 + rb437 u γ
  | .xnorW u v => 1 + rb437 u γ + rb437 v γ
/-- Weighted sum of `(col, RoTerm)` items. -/
def roListSum : List (ℕ × RoTerm) → BitAssignment 437 → ℕ
  | [], _ => 0
  | (c, t) :: rest, γ => 2 ^ c * (evalRoTerm γ t).val + roListSum rest γ
theorem roListSum_append :
    ∀ (xs ys : List (ℕ × RoTerm)) (γ : BitAssignment 437),
      roListSum (xs ++ ys) γ = roListSum xs γ + roListSum ys γ
  | [], _, _ => by simp [roListSum]
  | _ :: xs, ys, γ => by simp only [List.cons_append, roListSum, roListSum_append xs ys γ]; omega
/-- Remove the first occurrence matching `eqf x` from `L`, returning `none` if absent. -/
def popElem {α : Type} (eqf : α → α → Bool) (x : α) : List α → Option (List α)
  | [] => none
  | y :: ys =>
      match eqf x y with
      | true => some ys
      | false =>
          match popElem eqf x ys with
          | none => none
          | some ys' => some (y :: ys')
theorem popElem_sub {α : Type} {eqf : α → α → Bool} {x : α} :
    ∀ {L L' : List α}, popElem eqf x L = some L' → ∀ y ∈ L', y ∈ L
  | [], _, h, _, _ => by cases h
  | y :: ys, L', h, z, hz => by
      dsimp only [popElem] at h
      cases hxy : eqf x y with
      | true =>
          rw [hxy] at h; injection h with h'; subst h'
          exact List.mem_cons_of_mem y hz
      | false =>
          rw [hxy] at h
          cases hp : popElem eqf x ys with
          | none => rw [hp] at h; cases h
          | some ys' =>
              rw [hp] at h; injection h with h'; subst h'
              rcases List.mem_cons.mp hz with rfl | hzy
              · exact List.mem_cons_self
              · exact List.mem_cons_of_mem y (popElem_sub hp z hzy)
theorem popElem_mutListSum {x : ℕ × ℕ} :
    ∀ {L L' : List (ℕ × ℕ)}, popElem eqMut x L = some L' → ∀ δ : BitAssignment 437,
      mutListSum L δ = 2 ^ x.1 * (rb437 x.2 δ).val + mutListSum L' δ
  | [], _, h, _ => by cases h
  | y :: ys, L', h, δ => by
      dsimp only [popElem] at h
      cases hxy : eqMut x y with
      | true =>
          rw [hxy] at h; injection h with h'
          have heq : x = y := (eqMut_eq_true_iff x y).mp hxy
          subst h' heq
          rfl
      | false =>
          rw [hxy] at h
          cases hp : popElem eqMut x ys with
          | none => rw [hp] at h; cases h
          | some ys' =>
              rw [hp] at h; injection h with h'; subst h'
              dsimp only [mutListSum]
              rw [popElem_mutListSum hp δ]
              omega
theorem popElem_roListSum {x : ℕ × RoTerm} :
    ∀ {L L' : List (ℕ × RoTerm)}, popElem eqRo x L = some L' → ∀ γ : BitAssignment 437,
      roListSum L γ = 2 ^ x.1 * (evalRoTerm γ x.2).val + roListSum L' γ
  | [], _, h, _ => by cases h
  | y :: ys, L', h, γ => by
      dsimp only [popElem] at h
      cases hxy : eqRo x y with
      | true =>
          rw [hxy] at h; injection h with h'
          have heq : x = y := (eqRo_eq_true_iff x y).mp hxy
          subst h' heq
          rfl
      | false =>
          rw [hxy] at h
          cases hp : popElem eqRo x ys with
          | none => rw [hp] at h; cases h
          | some ys' =>
              rw [hp] at h; injection h with h'; subst h'
              dsimp only [roListSum]
              rw [popElem_roListSum hp γ]
              omega
/-- Target wire holding the prepared bit of a `SqOperand`. -/
def opTarget : SqOperand → ℕ
  | .mutW u => u
  | .ro (.wire u) => u
  | .ro (.notW u) => u
  | .ro (.xnorW _ v) => v
/-- Wire-support membership test for a `SqOperand`. -/
def inOpSupp (q : ℕ) : SqOperand → Bool
  | .mutW u => q == u
  | .ro (.wire u) => q == u
  | .ro (.notW u) => q == u
  | .ro (.xnorW u v) => (q == u) || (q == v)
/-- Disjointness of wire supports of two `SqOperand`s. -/
def opSuppDisj (op1 op2 : SqOperand) : Bool :=
  match op1 with
  | .mutW u => !inOpSupp u op2
  | .ro (.wire u) => !inOpSupp u op2
  | .ro (.notW u) => !inOpSupp u op2
  | .ro (.xnorW u v) => !inOpSupp u op2 && !inOpSupp v op2
theorem opSuppDisj_spec {op1 op2 : SqOperand} (h : opSuppDisj op1 op2 = true)
    {q : ℕ} (hq1 : inOpSupp q op1 = true) : inOpSupp q op2 = false := by
  cases op1 with
  | mutW u =>
      simp only [inOpSupp, beq_iff_eq] at hq1; subst hq1
      simpa [opSuppDisj] using h
  | ro t =>
      cases t with
      | wire u =>
          simp only [inOpSupp, beq_iff_eq] at hq1; subst hq1
          simpa [opSuppDisj] using h
      | notW u =>
          simp only [inOpSupp, beq_iff_eq] at hq1; subst hq1
          simpa [opSuppDisj] using h
      | xnorW u v =>
          simp only [opSuppDisj, Bool.and_eq_true, Bool.not_eq_true'] at h
          simp only [inOpSupp, Bool.or_eq_true, beq_iff_eq] at hq1
          rcases hq1 with rfl | rfl
          · exact h.1
          · exact h.2
/-- Well-formedness of a `SqOperand` at scratch frontier `cur`. -/
def wfOperand (cur : ℕ) : SqOperand → Bool
  | .mutW u => decide (278 ≤ u) && decide (u < cur)
  | .ro (.wire u) => decide (u < 278)
  | .ro (.notW u) => decide (u < 278)
  | .ro (.xnorW u v) => decide (u < 278) && decide (v < 278) && (u != v)
theorem opTarget_in_supp (op : SqOperand) : inOpSupp (opTarget op) op = true := by
  cases op with
  | mutW u => simp [opTarget, inOpSupp]
  | ro t => cases t <;> simp [opTarget, inOpSupp]
theorem opTarget_lt_cur {cur : ℕ} {op : SqOperand} (h : wfOperand cur op = true)
    (h278 : 278 ≤ cur) : opTarget op < cur := by
  cases op with
  | mutW u =>
      simp only [wfOperand, Bool.and_eq_true, decide_eq_true_eq] at h
      exact h.2
  | ro t =>
      cases t <;>
        (dsimp [wfOperand, opTarget] at h ⊢;
          simp only [Bool.and_eq_true, decide_eq_true_eq] at h; omega)
/-- Reversible Clifford preparation steps for a `SqOperand`. -/
def opPrepSteps : SqOperand → List P57Step
  | .mutW _ => []
  | .ro (.wire _) => []
  | .ro (.notW u) => [.x u]
  | .ro (.xnorW u v) => [.cnot u v, .x v]
/-- Reversible Clifford unpreparation steps for a `SqOperand`. -/
def opUnprepSteps : SqOperand → List P57Step
  | .mutW _ => []
  | .ro (.wire _) => []
  | .ro (.notW u) => [.x u]
  | .ro (.xnorW u v) => [.x v, .cnot u v]
/-- Core 6-step `1`-`TempAnd` OR-half-adder (`1 + a + b = (1 + a + b) + 2 * (a | b)`). -/
def orHaCoreSteps (a b cout : ℕ) : List P57Step :=
  [.x a, .x b, .tempAnd a b cout, .x cout, .x b, .cnot b a]
/-- Core 6-step `1`-`TempAnd` full adder (`a + b + c`, overwriting `a` with sum and `cout` with
  carry, restoring `b, c`). -/
def faCoreSteps (a b c cout : ℕ) : List P57Step :=
  [.cnot c a, .cnot c b, .tempAnd a b cout, .cnot c b, .cnot b a, .cnot c cout]
/-- Expand an `XorSqOp` into primitive `P57Step`s. -/
def xorSqOpSteps : XorSqOp → List P57Step
  | .orHa _ a b cout => orHaCoreSteps a b cout
  | .faGen _ a opB opC cout =>
      opPrepSteps opB ++ opPrepSteps opC ++
        faCoreSteps a (opTarget opB) (opTarget opC) cout ++
        opUnprepSteps opC ++ opUnprepSteps opB
  | .flip15 a => [.x a]
/-- Initial `15`-step (`3`-`TempAnd`) allocation of `z0_w = (1 + d_w[0]) * (1 + d_w[1])` at wires
  `278, 279, 280`. -/
def xorSqZ0Steps : List P57Step := [
  .x 177, .x 178, .tempAnd 177 178 278, .x 178, .x 177,
  .x 184, .x 185, .tempAnd 184 185 279, .x 185, .x 184,
  .x 191, .x 192, .tempAnd 191 192 280, .x 192, .x 191
]
/-- The `105` XOR-complement CSA operations (`102` `faGen`, `2` `orHa`, `1` `flip15`). -/
def xorSqOps105 : List XorSqOp := [
  .orHa 0 278 279 281, .faGen 0 280 (.ro (.notW 179)) (.ro (.notW 186)) 282,
  .faGen 0 278 (.ro (.notW 193)) (.ro (.xnorW 177 179)) 283,
    .faGen 0 280 (.ro (.xnorW 184 186)) (.ro (.xnorW 191 193)) 284,
  .faGen 1 281 (.ro (.notW 180)) (.ro (.notW 187)) 285,
    .faGen 1 282 (.ro (.notW 194)) (.ro (.xnorW 177 180)) 286,
  .faGen 1 283 (.ro (.xnorW 184 187)) (.ro (.xnorW 191 194)) 287,
    .faGen 1 284 (.ro (.xnorW 178 179)) (.ro (.xnorW 185 186)) 288,
  .faGen 1 281 (.ro (.xnorW 192 193)) (.mutW 282) 289, .faGen 1 283 (.mutW 284) (.mutW 281) 290,
  .faGen 2 285 (.ro (.notW 181)) (.ro (.notW 188)) 291,
    .faGen 2 286 (.ro (.notW 195)) (.ro (.xnorW 177 181)) 292,
  .faGen 2 287 (.ro (.xnorW 184 188)) (.ro (.xnorW 191 195)) 293,
    .faGen 2 288 (.ro (.xnorW 178 180)) (.ro (.xnorW 185 187)) 294,
  .faGen 2 289 (.ro (.xnorW 192 194)) (.mutW 290) 295, .faGen 2 285 (.mutW 286) (.mutW 287) 296,
  .faGen 2 288 (.mutW 289) (.mutW 285) 297, .faGen 3 291 (.ro (.notW 182)) (.ro (.notW 189)) 298,
  .faGen 3 292 (.ro (.notW 196)) (.ro (.xnorW 177 182)) 299,
    .faGen 3 293 (.ro (.xnorW 184 189)) (.ro (.xnorW 191 196)) 300,
  .faGen 3 294 (.ro (.xnorW 178 181)) (.ro (.xnorW 185 188)) 301,
    .faGen 3 295 (.ro (.xnorW 192 195)) (.ro (.xnorW 179 180)) 302,
  .faGen 3 296 (.ro (.xnorW 186 187)) (.ro (.xnorW 193 194)) 303,
    .faGen 3 297 (.mutW 291) (.mutW 292) 304,
  .faGen 3 293 (.mutW 294) (.mutW 295) 305, .faGen 3 296 (.mutW 297) (.mutW 293) 306,
  .faGen 4 298 (.ro (.notW 183)) (.ro (.notW 190)) 307,
    .faGen 4 299 (.ro (.notW 197)) (.ro (.xnorW 177 183)) 308,
  .faGen 4 300 (.ro (.xnorW 184 190)) (.ro (.xnorW 191 197)) 309,
    .faGen 4 301 (.ro (.xnorW 178 182)) (.ro (.xnorW 185 189)) 310,
  .faGen 4 302 (.ro (.xnorW 192 196)) (.ro (.xnorW 179 181)) 311,
    .faGen 4 303 (.ro (.xnorW 186 188)) (.ro (.xnorW 193 195)) 312,
  .faGen 4 304 (.mutW 305) (.mutW 306) 313, .faGen 4 298 (.mutW 299) (.mutW 300) 314,
  .faGen 4 301 (.mutW 302) (.mutW 303) 315, .faGen 4 304 (.mutW 298) (.mutW 301) 316,
  .faGen 5 307 (.ro (.notW 275)) (.ro (.notW 276)) 317,
    .faGen 5 308 (.ro (.notW 277)) (.ro (.xnorW 177 275)) 318,
  .faGen 5 309 (.ro (.xnorW 184 276)) (.ro (.xnorW 191 277)) 319,
    .faGen 5 310 (.ro (.xnorW 178 183)) (.ro (.xnorW 185 190)) 320,
  .faGen 5 311 (.ro (.xnorW 192 197)) (.ro (.xnorW 179 182)) 321,
    .faGen 5 312 (.ro (.xnorW 186 189)) (.ro (.xnorW 193 196)) 322,
  .faGen 5 313 (.ro (.xnorW 180 181)) (.ro (.xnorW 187 188)) 323,
    .faGen 5 314 (.ro (.xnorW 194 195)) (.mutW 315) 324,
  .faGen 5 316 (.mutW 307) (.mutW 308) 325, .faGen 5 309 (.mutW 310) (.mutW 311) 326,
  .faGen 5 312 (.mutW 313) (.mutW 314) 327, .faGen 5 316 (.mutW 309) (.mutW 312) 328,
  .faGen 6 317 (.ro (.wire 177)) (.ro (.wire 184)) 329,
    .faGen 6 318 (.ro (.wire 191)) (.ro (.xnorW 178 275)) 330,
  .faGen 6 319 (.ro (.xnorW 185 276)) (.ro (.xnorW 192 277)) 331,
    .faGen 6 320 (.ro (.xnorW 179 183)) (.ro (.xnorW 186 190)) 332,
  .faGen 6 321 (.ro (.xnorW 193 197)) (.ro (.xnorW 180 182)) 333,
    .faGen 6 322 (.ro (.xnorW 187 189)) (.ro (.xnorW 194 196)) 334,
  .faGen 6 323 (.mutW 324) (.mutW 325) 335, .faGen 6 326 (.mutW 327) (.mutW 328) 336,
  .faGen 6 317 (.mutW 318) (.mutW 319) 337, .faGen 6 320 (.mutW 321) (.mutW 322) 338,
  .faGen 6 323 (.mutW 326) (.mutW 317) 339, .faGen 7 329 (.ro (.wire 178)) (.ro (.wire 185)) 340,
  .faGen 7 330 (.ro (.wire 192)) (.ro (.xnorW 179 275)) 341,
    .faGen 7 331 (.ro (.xnorW 186 276)) (.ro (.xnorW 193 277)) 342,
  .faGen 7 332 (.ro (.xnorW 180 183)) (.ro (.xnorW 187 190)) 343,
    .faGen 7 333 (.ro (.xnorW 194 197)) (.ro (.xnorW 181 182)) 344,
  .faGen 7 334 (.ro (.xnorW 188 189)) (.ro (.xnorW 195 196)) 345,
    .faGen 7 335 (.mutW 336) (.mutW 337) 346,
  .faGen 7 338 (.mutW 339) (.mutW 329) 347, .faGen 7 330 (.mutW 331) (.mutW 332) 348,
  .faGen 7 333 (.mutW 334) (.mutW 335) 349, .faGen 7 338 (.mutW 330) (.mutW 333) 350,
  .faGen 8 340 (.ro (.wire 179)) (.ro (.wire 186)) 351,
    .faGen 8 341 (.ro (.wire 193)) (.ro (.xnorW 180 275)) 352,
  .faGen 8 342 (.ro (.xnorW 187 276)) (.ro (.xnorW 194 277)) 353,
    .faGen 8 343 (.ro (.xnorW 181 183)) (.ro (.xnorW 188 190)) 354,
  .faGen 8 344 (.ro (.xnorW 195 197)) (.mutW 345) 355, .faGen 8 346 (.mutW 347) (.mutW 348) 356,
  .faGen 8 349 (.mutW 350) (.mutW 340) 357, .faGen 8 341 (.mutW 342) (.mutW 343) 358,
  .faGen 8 344 (.mutW 346) (.mutW 349) 359, .faGen 9 351 (.ro (.wire 180)) (.ro (.wire 187)) 360,
  .faGen 9 352 (.ro (.wire 194)) (.ro (.xnorW 181 275)) 361,
    .faGen 9 353 (.ro (.xnorW 188 276)) (.ro (.xnorW 195 277)) 362,
  .faGen 9 354 (.ro (.xnorW 182 183)) (.ro (.xnorW 189 190)) 363,
    .faGen 9 355 (.ro (.xnorW 196 197)) (.mutW 356) 364,
  .faGen 9 357 (.mutW 358) (.mutW 359) 365, .faGen 9 351 (.mutW 352) (.mutW 353) 366,
  .faGen 9 354 (.mutW 355) (.mutW 357) 367, .faGen 10 360 (.ro (.wire 181)) (.ro (.wire 188)) 368,
  .faGen 10 361 (.ro (.wire 195)) (.ro (.xnorW 182 275)) 369,
    .faGen 10 362 (.ro (.xnorW 189 276)) (.ro (.xnorW 196 277)) 370,
  .faGen 10 363 (.mutW 364) (.mutW 365) 371, .faGen 10 366 (.mutW 367) (.mutW 360) 372,
  .faGen 10 361 (.mutW 362) (.mutW 363) 373, .faGen 11 368 (.ro (.wire 182)) (.ro (.wire 189)) 374,
  .faGen 11 369 (.ro (.wire 196)) (.ro (.xnorW 183 275)) 375,
    .faGen 11 370 (.ro (.xnorW 190 276)) (.ro (.xnorW 197 277)) 376,
  .faGen 11 371 (.mutW 372) (.mutW 373) 377, .faGen 11 368 (.mutW 369) (.mutW 370) 378,
  .faGen 12 374 (.ro (.wire 183)) (.ro (.wire 190)) 379,
    .faGen 12 375 (.ro (.wire 197)) (.mutW 376) 380,
  .faGen 12 377 (.mutW 378) (.mutW 374) 381, .faGen 13 379 (.ro (.wire 275)) (.ro (.wire 276)) 382,
  .faGen 13 380 (.ro (.wire 277)) (.mutW 381) 383, .orHa 14 382 383 384,
  .flip15 384
]
/-- Complete `1,000`-step (`107`-`TempAnd`) `P57Step` program for `K_xorSq` (`278 -> 385`). -/
def xorSqSteps : List P57Step :=
  xorSqZ0Steps ++ xorSqOps105.flatMap xorSqOpSteps
/-- `437`-wire `107`-`TempAnd` XOR-complement CSA context (`278 -> 385`). -/
def K_xorSq : TempCtx 437 :=
  buildP57Ctx xorSqSteps
theorem K_xorSq_pkg : P57CtxPkg 278 385 107 K_xorSq :=
  buildP57Ctx_pkg (by decide : wfP57Steps 278 xorSqSteps = some (385, 107))
/-- Fast flat `P57Step` support test below `bound`. -/
def stepBelowB (bound : ℕ) : P57Step → Bool
  | .x q => decide (q < bound)
  | .cnot c t => decide (c < bound) && decide (t < bound)
  | .tempAnd a b dst => decide (a < bound) && decide (b < bound) && decide (dst < bound)
theorem ctxSupportsBelowB_append {M : ℕ} (bound : ℕ) :
    ∀ (F G : TempCtx M),
      ctxSupportsBelowB bound F = true → ctxSupportsBelowB bound G = true →
        ctxSupportsBelowB bound (F.append G) = true
  | .hole, _, _, hG => hG
  | .seqPre c K, G, hF, hG => by
      obtain ⟨h1, h2⟩ := Bool.and_eq_true _ _ |>.mp hF
      exact Bool.and_eq_true _ _ |>.mpr ⟨h1, ctxSupportsBelowB_append bound K G h2 hG⟩
  | .seqPost K c, G, hF, hG => by
      obtain ⟨h1, h2⟩ := Bool.and_eq_true _ _ |>.mp hF
      exact Bool.and_eq_true _ _ |>.mpr ⟨ctxSupportsBelowB_append bound K G h1 hG, h2⟩
  | .tempAnd _ _ _ _ _ _ K, G, hF, hG => by
      obtain ⟨h1, hr1⟩ := Bool.and_eq_true _ _ |>.mp hF
      obtain ⟨h2, hr2⟩ := Bool.and_eq_true _ _ |>.mp hr1
      obtain ⟨h3, hK⟩ := Bool.and_eq_true _ _ |>.mp hr2
      exact Bool.and_eq_true _ _ |>.mpr ⟨h1,
        Bool.and_eq_true _ _ |>.mpr ⟨h2,
          Bool.and_eq_true _ _ |>.mpr ⟨h3, ctxSupportsBelowB_append bound K G hK hG⟩⟩⟩
theorem ctxSupportsBelowB_stepToSingleCtx (bound : ℕ) (s : P57Step)
    (hs : stepBelowB bound s = true) :
    ctxSupportsBelowB bound (stepToSingleCtx s) = true := by
  cases s with
  | x q =>
      simp only [stepBelowB, decide_eq_true_eq] at hs
      dsimp only [stepToSingleCtx]
      split_ifs with hq
      · simp [ctxCliffAlloc, ctxSupportsBelowB, cliffSupportsBelowB, CliffProg.inv, hs]
      · rfl
  | cnot c t =>
      simp only [stepBelowB, Bool.and_eq_true, decide_eq_true_eq] at hs
      dsimp only [stepToSingleCtx]
      split_ifs with h
      · simp [ctxCliffAlloc, ctxSupportsBelowB, cliffSupportsBelowB, CliffProg.inv, hs.1, hs.2]
      · rfl
  | tempAnd a b dst =>
      simp only [stepBelowB, Bool.and_eq_true, decide_eq_true_eq] at hs
      dsimp only [stepToSingleCtx]
      split_ifs with h
      · simp [ctxTempBit, ctxSupportsBelowB, hs.1.1, hs.1.2, hs.2]
      · rfl
theorem ctxSupportsBelowB_buildP57Ctx (bound : ℕ) :
    ∀ (ss : List P57Step),
      ss.all (stepBelowB bound) = true → ctxSupportsBelowB bound (buildP57Ctx ss) = true
  | [], _ => rfl
  | s :: ss, h => by
      simp only [List.all_cons, Bool.and_eq_true] at h
      exact ctxSupportsBelowB_append bound _ _
        (ctxSupportsBelowB_stepToSingleCtx bound s h.1)
        (ctxSupportsBelowB_buildP57Ctx bound ss h.2)
theorem K_xorSq_supportsBelow388 : ctxSupportsBelowB 388 K_xorSq = true :=
  ctxSupportsBelowB_buildP57Ctx 388 xorSqSteps (by decide)
/-- `388`-wire truncation of `K_xorSq` (`278 -> 385`, `107` `TempAnd`s). -/
def K_xorSq_388 : TempCtx 388 :=
  truncateCtxB 388 K_xorSq K_xorSq_supportsBelow388
theorem K_xorSq_388_pkg : CtxPkg388 278 385 107 K_xorSq_388 :=
  toCtxPkg388 K_xorSq_pkg (by decide) (by decide) K_xorSq_supportsBelow388
/-!
### Section 3B: Modular Algebraic Soundness of `K_xorSq` (`evalP57Steps`)
-/
theorem evalP57Steps_append :
    ∀ (xs ys : List P57Step) (β : BitAssignment 437),
      evalP57Steps (xs ++ ys) β = evalP57Steps ys (evalP57Steps xs β)
  | [], _, _ => rfl
  | s :: xs, ys, β => evalP57Steps_append xs ys (evalP57Step s β)
theorem zmod2_add_one_cancel (x : ZMod 2) : x + 1 + 1 = x := by
  rcases bit_cases x with rfl | rfl <;> decide
theorem zmod2_cnot_cancel (x y : ZMod 2) : x + y + y = x := by
  rcases bit_cases x with rfl | rfl <;> rcases bit_cases y with rfl | rfl <;> decide
/-- Logical evaluation of a `SqOperand` against current `δ` (for `.mutW`) and initial `γ₀` (for
  `.ro`). -/
def evalSqOperand (δ γ₀ : BitAssignment 437) : SqOperand → ZMod 2
  | .mutW u => rb437 u δ
  | .ro t => evalRoTerm γ₀ t
theorem opPrep_spec {cur : ℕ} {op : SqOperand} (hwf : wfOperand cur op = true)
    (_h278 : 278 ≤ cur) (_hcur : cur ≤ 437)
    (δ γ₀ β : BitAssignment 437)
    (hLow : ∀ w : Wire 437, inOpSupp w.val op = true → w.val < 278 → β w = γ₀ w)
    (hMut : ∀ u : ℕ, op = .mutW u → rb437 u β = rb437 u δ) :
    let β' := evalP57Steps (opPrepSteps op) β
    (∀ w : Wire 437, inOpSupp w.val op = false → β' w = β w) ∧
      rb437 (opTarget op) β' = evalSqOperand δ γ₀ op ∧
      (∀ η : BitAssignment 437,
        (∀ w : Wire 437, inOpSupp w.val op = true → η w = β' w) →
        (∀ w : Wire 437, inOpSupp w.val op = false →
          evalP57Steps (opUnprepSteps op) η w = η w) ∧
        (∀ w : Wire 437, inOpSupp w.val op = true →
          evalP57Steps (opUnprepSteps op) η w = β w)) := by
  cases op with
  | mutW u =>
      refine ⟨fun _ _ ↦ rfl, hMut u rfl, fun η hη ↦ ⟨fun _ _ ↦ rfl, hη⟩⟩
  | ro t =>
      cases t with
      | wire u =>
          simp only [wfOperand, decide_eq_true_eq] at hwf
          have hu437 : u < 437 := by omega
          have hbu : rb437 u β = rb437 u γ₀ := by
            rw [rb437_lt _ hu437, rb437_lt _ hu437]
            exact hLow ⟨u, hu437⟩ (by simp [inOpSupp]) hwf
          exact ⟨fun _ _ ↦ rfl, hbu, fun η hη ↦ ⟨fun _ _ ↦ rfl, hη⟩⟩
      | notW u =>
          simp only [wfOperand, decide_eq_true_eq] at hwf
          have hu437 : u < 437 := by omega
          dsimp only [opPrepSteps, opUnprepSteps, evalP57Steps, evalP57Step]
          rw [dite_eq_left hu437]
          refine ⟨fun w hw ↦ ?_, ?_, fun η hη ↦ ?_⟩
          · simp only [inOpSupp, beq_eq_false_iff_ne] at hw
            exact Function.update_of_ne (wire_ne_val hw) _ _
          · dsimp only [opTarget, evalSqOperand, evalRoTerm]
            rw [rb437_lt _ hu437, rb437_lt _ hu437, Function.update_self,
              hLow ⟨u, hu437⟩ (by simp [inOpSupp]) hwf, add_comm]
          · rw [dite_eq_left hu437]
            refine ⟨fun w hw ↦ ?_, fun w hw ↦ ?_⟩
            · simp only [inOpSupp, beq_eq_false_iff_ne] at hw
              exact Function.update_of_ne (wire_ne_val hw) _ _
            · simp only [inOpSupp, beq_iff_eq] at hw
              have hwu : w = ⟨u, hu437⟩ := Fin.ext hw
              rw [hwu, Function.update_self, hη ⟨u, hu437⟩ (by simp [inOpSupp]),
                Function.update_self, zmod2_add_one_cancel]
      | xnorW u v =>
          simp only [wfOperand, Bool.and_eq_true, bne_iff_ne, decide_eq_true_eq] at hwf
          obtain ⟨⟨hu278, hv278⟩, huv⟩ := hwf
          have hu437 : u < 437 := by omega
          have hv437 : v < 437 := by omega
          have hcond : u < 437 ∧ v < 437 ∧ u ≠ v := ⟨hu437, hv437, huv⟩
          dsimp only [opPrepSteps, opUnprepSteps, evalP57Steps, evalP57Step]
          rw [dite_eq_left hcond, dite_eq_left hv437]
          let β₁ := Function.update (Function.update β ⟨v, hv437⟩ (β ⟨v, hv437⟩ + β ⟨u, hu437⟩))
            ⟨v, hv437⟩ (Function.update β ⟨v, hv437⟩ (β ⟨v, hv437⟩ + β ⟨u, hu437⟩) ⟨v, hv437⟩ + 1)
          have hβ₁_v : β₁ ⟨v, hv437⟩ = β ⟨v, hv437⟩ + β ⟨u, hu437⟩ + 1 := by
            dsimp only [β₁]; rw [Function.update_self, Function.update_self]
          have hβ₁_u : β₁ ⟨u, hu437⟩ = β ⟨u, hu437⟩ := by
            dsimp only [β₁]
            rw [Function.update_of_ne (wire_ne_val huv), Function.update_of_ne (wire_ne_val huv)]
          refine ⟨fun w hw ↦ ?_, ?_, fun η hη ↦ ?_⟩
          · simp only [inOpSupp, Bool.or_eq_false_iff, beq_eq_false_iff_ne] at hw
            rw [Function.update_of_ne (wire_ne_val hw.2), Function.update_of_ne (wire_ne_val hw.2)]
          · dsimp only [opTarget, evalSqOperand, evalRoTerm]
            rw [rb437_lt _ hv437, rb437_lt _ hu437, rb437_lt _ hv437]
            change β₁ ⟨v, hv437⟩ = 1 + γ₀ ⟨u, hu437⟩ + γ₀ ⟨v, hv437⟩
            rw [hβ₁_v,
              hLow ⟨u, hu437⟩ (by simp [inOpSupp]) hu278,
              hLow ⟨v, hv437⟩ (by simp [inOpSupp]) hv278]
            abel
          · rw [dite_eq_left hv437]
            let η₁ := Function.update η ⟨v, hv437⟩ (η ⟨v, hv437⟩ + 1)
            change (∀ w : Wire 437, inOpSupp w.val (.ro (.xnorW u v)) = false →
                (if h : u < 437 ∧ v < 437 ∧ u ≠ v then
                  Function.update η₁ ⟨v, h.2.1⟩ (η₁ ⟨v, h.2.1⟩ + η₁ ⟨u, h.1⟩) else η₁) w = η w) ∧ _
            rw [dite_eq_left hcond]
            have hηu : η ⟨u, hu437⟩ = β ⟨u, hu437⟩ :=
              (hη ⟨u, hu437⟩ (by simp [inOpSupp])).trans hβ₁_u
            have hηv : η ⟨v, hv437⟩ = β ⟨v, hv437⟩ + β ⟨u, hu437⟩ + 1 :=
              (hη ⟨v, hv437⟩ (by simp [inOpSupp])).trans hβ₁_v
            refine ⟨fun w hw ↦ ?_, fun w hw ↦ ?_⟩
            · simp only [inOpSupp, Bool.or_eq_false_iff, beq_eq_false_iff_ne] at hw
              rw [Function.update_of_ne (wire_ne_val hw.2)]
              exact Function.update_of_ne (wire_ne_val hw.2) _ _
            · simp only [inOpSupp, Bool.or_eq_true, beq_iff_eq] at hw
              rcases hw with hwu | hwv
              · have hw_eq : w = ⟨u, hu437⟩ := Fin.ext hwu
                rw [hw_eq, Function.update_of_ne (wire_ne_val huv)]
                dsimp only [η₁]
                rw [Function.update_of_ne (wire_ne_val huv)]
                exact hηu
              · have hw_eq : w = ⟨v, hv437⟩ := Fin.ext hwv
                rw [hw_eq, Function.update_self]
                dsimp only [η₁]
                rw [Function.update_self, Function.update_of_ne (wire_ne_val huv),
                  hηv, hηu, zmod2_add_one_cancel, zmod2_cnot_cancel]
theorem orHaCoreSteps_eval {a b cout : ℕ}
    (ha : a < 437) (hb : b < 437) (hc : cout < 437)
    (hab : a ≠ b) (hac : a ≠ cout) (hbc : b ≠ cout)
    (δ : BitAssignment 437) (h0 : δ ⟨cout, hc⟩ = 0) :
    let δ' := evalP57Steps (orHaCoreSteps a b cout) δ
    rb437 a δ' = 1 + rb437 a δ + rb437 b δ ∧
      rb437 cout δ' = 1 + (1 + rb437 a δ) * (1 + rb437 b δ) ∧
      (∀ w : Wire 437, w.val ≠ a → w.val ≠ cout → δ' w = δ w) := by
  have ht : a < 437 ∧ b < 437 ∧ cout < 437 ∧ a ≠ b ∧ a ≠ cout ∧ b ≠ cout :=
    ⟨ha, hb, hc, hab, hac, hbc⟩
  have hba : b < 437 ∧ a < 437 ∧ b ≠ a := ⟨hb, ha, hab.symm⟩
  dsimp only [orHaCoreSteps, evalP57Steps, evalP57Step]
  rw [dite_eq_left ha, dite_eq_left hb, dite_eq_left ht, dite_eq_left hc, dite_eq_left hb,
    dite_eq_left hba]
  let wa : Wire 437 := ⟨a, ha⟩
  let wb : Wire 437 := ⟨b, hb⟩
  let wc : Wire 437 := ⟨cout, hc⟩
  have hwa_wb : wa ≠ wb := wire_ne_val hab
  have hwa_wc : wa ≠ wc := wire_ne_val hac
  have hwb_wc : wb ≠ wc := wire_ne_val hbc
  let s1 := Function.update δ wa (δ wa + 1)
  let s2 := Function.update s1 wb (s1 wb + 1)
  let s3 := Function.update s2 wc (s2 wc + s2 wa * s2 wb)
  let s4 := Function.update s3 wc (s3 wc + 1)
  let s5 := Function.update s4 wb (s4 wb + 1)
  let s6 := Function.update s5 wa (s5 wa + s5 wb)
  have hs2_a : s2 wa = δ wa + 1 := by
    dsimp [s2, s1]; rw [Function.update_of_ne hwa_wb, Function.update_self]
  have hs2_b : s2 wb = δ wb + 1 := by
    dsimp [s2, s1]; rw [Function.update_self, Function.update_of_ne hwa_wb.symm]
  have hs2_c : s2 wc = 0 := by
    dsimp [s2, s1]; rw [Function.update_of_ne hwb_wc.symm, Function.update_of_ne hwa_wc.symm, h0]
  have hs4_c : s4 wc = 1 + (1 + δ wa) * (1 + δ wb) := by
    dsimp [s4, s3]; rw [Function.update_self, Function.update_self, hs2_c, hs2_a, hs2_b, zero_add]
    ring
  have hs5_b : s5 wb = δ wb := by
    dsimp [s5, s4, s3]
    rw [Function.update_self, Function.update_of_ne hwb_wc, Function.update_of_ne hwb_wc,
      hs2_b, zmod2_add_one_cancel]
  have hs5_a : s5 wa = δ wa + 1 := by
    dsimp [s5, s4, s3]
    rw [Function.update_of_ne hwa_wb, Function.update_of_ne hwa_wc, Function.update_of_ne hwa_wc,
      hs2_a]
  refine ⟨?_, ?_, fun w hna hnc ↦ ?_⟩
  · rw [rb437_lt _ ha, rb437_lt _ ha, rb437_lt _ hb]
    change s6 wa = 1 + δ wa + δ wb
    dsimp [s6]; rw [Function.update_self, hs5_a, hs5_b]; abel
  · rw [rb437_lt _ hc, rb437_lt _ ha, rb437_lt _ hb]
    change s6 wc = 1 + (1 + δ wa) * (1 + δ wb)
    dsimp [s6, s5]; rw [Function.update_of_ne hwa_wc.symm, Function.update_of_ne hwb_wc.symm, hs4_c]
  · change s6 w = δ w
    have hw_a : w ≠ wa := wire_ne_val hna
    have hw_c : w ≠ wc := wire_ne_val hnc
    by_cases hwb : w = wb
    · rw [hwb]; dsimp [s6]; rw [Function.update_of_ne hwa_wb.symm, hs5_b]
    · dsimp [s6, s5, s4, s3, s2, s1]
      rw [Function.update_of_ne hw_a, Function.update_of_ne hwb, Function.update_of_ne hw_c,
        Function.update_of_ne hw_c, Function.update_of_ne hwb, Function.update_of_ne hw_a]
theorem faCoreSteps_eval {a b c cout : ℕ}
    (ha : a < 437) (hb : b < 437) (hc : c < 437) (hd : cout < 437)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ cout)
    (hbc : b ≠ c) (hbd : b ≠ cout) (hcd : c ≠ cout)
    (β : BitAssignment 437) (h0 : β ⟨cout, hd⟩ = 0) :
    let η := evalP57Steps (faCoreSteps a b c cout) β
    rb437 a η = rb437 a β + rb437 b β + rb437 c β ∧
      rb437 cout η =
        (rb437 a β + rb437 c β) * (rb437 b β + rb437 c β) + rb437 c β ∧
      (∀ w : Wire 437, w.val ≠ a → w.val ≠ cout → η w = β w) := by
  have hca : c < 437 ∧ a < 437 ∧ c ≠ a := ⟨hc, ha, hac.symm⟩
  have hcb : c < 437 ∧ b < 437 ∧ c ≠ b := ⟨hc, hb, hbc.symm⟩
  have ht : a < 437 ∧ b < 437 ∧ cout < 437 ∧ a ≠ b ∧ a ≠ cout ∧ b ≠ cout :=
    ⟨ha, hb, hd, hab, had, hbd⟩
  have hba : b < 437 ∧ a < 437 ∧ b ≠ a := ⟨hb, ha, hab.symm⟩
  have hcd' : c < 437 ∧ cout < 437 ∧ c ≠ cout := ⟨hc, hd, hcd⟩
  dsimp only [faCoreSteps, evalP57Steps, evalP57Step]
  rw [dite_eq_left hca, dite_eq_left hcb, dite_eq_left ht, dite_eq_left hcb, dite_eq_left hba,
    dite_eq_left hcd']
  let wa : Wire 437 := ⟨a, ha⟩
  let wb : Wire 437 := ⟨b, hb⟩
  let wc : Wire 437 := ⟨c, hc⟩
  let wd : Wire 437 := ⟨cout, hd⟩
  have hwa_wb : wa ≠ wb := wire_ne_val hab
  have hwa_wc : wa ≠ wc := wire_ne_val hac
  have hwa_wd : wa ≠ wd := wire_ne_val had
  have hwb_wc : wb ≠ wc := wire_ne_val hbc
  have hwb_wd : wb ≠ wd := wire_ne_val hbd
  have hwc_wd : wc ≠ wd := wire_ne_val hcd
  let s1 := Function.update β wa (β wa + β wc)
  let s2 := Function.update s1 wb (s1 wb + s1 wc)
  let s3 := Function.update s2 wd (s2 wd + s2 wa * s2 wb)
  let s4 := Function.update s3 wb (s3 wb + s3 wc)
  let s5 := Function.update s4 wa (s4 wa + s4 wb)
  let s6 := Function.update s5 wd (s5 wd + s5 wc)
  have hs2_a : s2 wa = β wa + β wc := by
    dsimp [s2, s1]; rw [Function.update_of_ne hwa_wb, Function.update_self]
  have hs2_b : s2 wb = β wb + β wc := by
    dsimp [s2, s1]
    rw [Function.update_self, Function.update_of_ne hwa_wb.symm, Function.update_of_ne hwa_wc.symm]
  have hs2_c : s2 wc = β wc := by
    dsimp [s2, s1]
    rw [Function.update_of_ne hwb_wc.symm, Function.update_of_ne hwa_wc.symm]
  have hs2_d : s2 wd = 0 := by
    dsimp [s2, s1]
    rw [Function.update_of_ne hwb_wd.symm, Function.update_of_ne hwa_wd.symm, h0]
  have hs3_d : s3 wd = (β wa + β wc) * (β wb + β wc) := by
    dsimp [s3]; rw [Function.update_self, hs2_d, hs2_a, hs2_b, zero_add]
  have hs4_b : s4 wb = β wb := by
    dsimp [s4, s3]
    rw [Function.update_self, Function.update_of_ne hwb_wd, Function.update_of_ne hwc_wd,
      hs2_b, hs2_c, zmod2_cnot_cancel]
  have hs4_a : s4 wa = β wa + β wc := by
    dsimp [s4, s3]
    rw [Function.update_of_ne hwa_wb, Function.update_of_ne hwa_wd, hs2_a]
  have hs5_a : s5 wa = β wa + β wb + β wc := by
    dsimp [s5]; rw [Function.update_self, hs4_a, hs4_b]; abel
  have hs5_c : s5 wc = β wc := by
    dsimp [s5, s4, s3]
    rw [Function.update_of_ne hwa_wc.symm, Function.update_of_ne hwb_wc.symm,
      Function.update_of_ne hwc_wd, hs2_c]
  have hs5_d : s5 wd = (β wa + β wc) * (β wb + β wc) := by
    dsimp [s5, s4]
    rw [Function.update_of_ne hwa_wd.symm, Function.update_of_ne hwb_wd.symm, hs3_d]
  refine ⟨?_, ?_, fun w hna hnd ↦ ?_⟩
  · rw [rb437_lt _ ha, rb437_lt _ ha, rb437_lt _ hb, rb437_lt _ hc]
    change s6 wa = β wa + β wb + β wc
    dsimp [s6]; rw [Function.update_of_ne hwa_wd, hs5_a]
  · rw [rb437_lt _ hd, rb437_lt _ ha, rb437_lt _ hb, rb437_lt _ hc]
    change s6 wd = (β wa + β wc) * (β wb + β wc) + β wc
    dsimp [s6]; rw [Function.update_self, hs5_d, hs5_c]
  · change s6 w = β w
    have hw_a : w ≠ wa := wire_ne_val hna
    have hw_d : w ≠ wd := wire_ne_val hnd
    by_cases hwb : w = wb
    · rw [hwb]; dsimp [s6, s5];
        rw [Function.update_of_ne hwb_wd, Function.update_of_ne hwa_wb.symm, hs4_b]
    · by_cases hwc : w = wc
      · rw [hwc]; dsimp [s6]; rw [Function.update_of_ne hwc_wd, hs5_c]
      · dsimp [s6, s5, s4, s3, s2, s1]
        rw [Function.update_of_ne hw_d, Function.update_of_ne hw_a, Function.update_of_ne hwb,
          Function.update_of_ne hw_d, Function.update_of_ne hwb, Function.update_of_ne hw_a]
theorem orHa_bit_val (x y : ZMod 2) :
    (1 + x + y).val + 2 * (1 + (1 + x) * (1 + y)).val = 1 + x.val + y.val := by
  rcases bit_cases x with rfl | rfl <;> rcases bit_cases y with rfl | rfl <;> decide
theorem fa_bit_val (x y z : ZMod 2) :
    (x + y + z).val + 2 * ((x + z) * (y + z) + z).val = x.val + y.val + z.val := by
  rcases bit_cases x with rfl | rfl <;> rcases bit_cases y with rfl | rfl <;>
    rcases bit_cases z with rfl | rfl <;> decide
theorem flip15_bit_val (x : ZMod 2) :
    (32768 + 32768 * x.val) % 65536 = (32768 * (x + 1).val) % 65536 := by
  rcases bit_cases x with rfl | rfl <;> decide
/-- Pop a single `SqOperand` at column `col` from `(muts, ros)`. -/
def popOperand (col : ℕ) (op : SqOperand)
    (muts : List (ℕ × ℕ)) (ros : List (ℕ × RoTerm)) :
    Option (List (ℕ × ℕ) × List (ℕ × RoTerm)) :=
  match op with
  | .mutW u =>
      match popElem eqMut (col, u) muts with
      | none => none
      | some m' => some (m', ros)
  | .ro t =>
      match popElem eqRo (col, t) ros with
      | none => none
      | some r' => some (muts, r')
theorem popOperand_sum {col : ℕ} {op : SqOperand}
    {muts m' : List (ℕ × ℕ)} {ros r' : List (ℕ × RoTerm)}
    (h : popOperand col op muts ros = some (m', r'))
    (δ γ₀ : BitAssignment 437) :
    (∀ p ∈ m', p ∈ muts) ∧
      mutListSum muts δ + roListSum ros γ₀ =
        2 ^ col * (evalSqOperand δ γ₀ op).val + (mutListSum m' δ + roListSum r' γ₀) := by
  cases op with
  | mutW u =>
      dsimp only [popOperand] at h
      cases hp : popElem eqMut (col, u) muts with
      | none => rw [hp] at h; cases h
      | some m1 =>
          rw [hp] at h; injection h with h'; injection h' with hm hr; subst hm hr
          refine ⟨popElem_sub hp, ?_⟩
          rw [popElem_mutListSum hp δ, evalSqOperand]
          dsimp only; omega
  | ro t =>
      dsimp only [popOperand] at h
      cases hp : popElem eqRo (col, t) ros with
      | none => rw [hp] at h; cases h
      | some r1 =>
          rw [hp] at h; injection h with h'; injection h' with hm hr; subst hm hr
          refine ⟨fun _ hp' ↦ hp', ?_⟩
          rw [popElem_roListSum hp γ₀, evalSqOperand]
          dsimp only; omega
/-- Mutable-item scratch range invariant `[278, cur)`. -/
def wfMuts (cur : ℕ) (muts : List (ℕ × ℕ)) : Bool :=
  muts.all (fun p ↦ decide (278 ≤ p.2) && decide (p.2 < cur))
theorem mutListSum_congr :
    ∀ (L : List (ℕ × ℕ)) {δ₁ δ₂ : BitAssignment 437},
      (∀ p ∈ L, rb437 p.2 δ₁ = rb437 p.2 δ₂) →
      mutListSum L δ₁ = mutListSum L δ₂
  | [], _, _, _ => rfl
  | p :: ps, δ₁, δ₂, h => by
      dsimp only [mutListSum]
      rw [h p List.mem_cons_self,
        mutListSum_congr ps (fun q hq ↦ h q (List.mem_cons_of_mem p hq))]
/-- Verified symbolic state transition for a single `XorSqOp` modulo `65536`. -/
def applyXorSqOp (cur cval : ℕ) (muts : List (ℕ × ℕ)) (ros : List (ℕ × RoTerm)) :
    XorSqOp → Option (ℕ × ℕ × List (ℕ × ℕ) × List (ℕ × RoTerm))
  | .orHa col a b cout =>
      match decide (col < 16) && decide (2 ^ col ≤ cval) &&
          decide (278 ≤ a) && decide (a < cur) &&
          decide (278 ≤ b) && decide (b < cur) && (a != b) &&
          (cout == cur) && decide (cur < 385) with
      | false => none
      | true =>
          match popElem eqMut (col, a) muts with
          | none => none
          | some m1 =>
              match popElem eqMut (col, b) m1 with
              | none => none
              | some m2 =>
                  match m2.all (fun p ↦ (p.2 != a) && (p.2 != cout)) with
                  | false => none
                  | true =>
                      let mOut :=
                        (col, a) :: cond (decide (col + 1 < 16)) [(col + 1, cout)] [] ++ m2
                      some (cur + 1, cval - 2 ^ col, mOut, ros)
  | .faGen col a opB opC cout =>
      match decide (col < 16) && decide (278 ≤ a) && decide (a < cur) &&
          wfOperand cur opB && wfOperand cur opC &&
          opSuppDisj opB opC &&
          !inOpSupp a opB && !inOpSupp a opC &&
          !inOpSupp cout opB && !inOpSupp cout opC &&
          (cout == cur) && decide (cur < 385) with
      | false => none
      | true =>
          match popElem eqMut (col, a) muts with
          | none => none
          | some m1 =>
              match popOperand col opB m1 ros with
              | none => none
              | some (m2, r2) =>
                  match popOperand col opC m2 r2 with
                  | none => none
                  | some (m3, r3) =>
                      match m3.all (fun p ↦ (p.2 != a) && (p.2 != cout) &&
                          !inOpSupp p.2 opB && !inOpSupp p.2 opC) with
                      | false => none
                      | true =>
                          let mOut :=
                            (col, a) :: cond (decide (col + 1 < 16)) [(col + 1, cout)] [] ++ m3
                          some (cur + 1, cval, mOut, r3)
  | .flip15 a =>
      match decide (32768 ≤ cval) && decide (278 ≤ a) && decide (a < cur) && decide (cur ≤ 385) with
      | false => none
      | true =>
          match popElem eqMut (15, a) muts with
          | none => none
          | some m1 =>
              match m1.all (fun p ↦ p.2 != a) with
              | false => none
              | true =>
                  some (cur, cval - 32768, (15, a) :: m1, ros)
/-- Iterate `applyXorSqOp` across a list of `XorSqOp`s. -/
def applyXorSqOps : ℕ → ℕ → List (ℕ × ℕ) → List (ℕ × RoTerm) → List XorSqOp →
    Option (ℕ × ℕ × List (ℕ × ℕ) × List (ℕ × RoTerm))
  | cur, cval, muts, ros, [] => some (cur, cval, muts, ros)
  | cur, cval, muts, ros, op :: rest =>
      match applyXorSqOp cur cval muts ros op with
      | none => none
      | some (cur1, cval1, muts1, ros1) => applyXorSqOps cur1 cval1 muts1 ros1 rest
theorem carry_col_mod65536 (col : ℕ) (hcol : col < 16) (s c : ℕ) :
    (2 ^ col * s + (if col + 1 < 16 then 2 ^ (col + 1) * c else 0)) % 65536 =
      (2 ^ col * (s + 2 * c)) % 65536 := by
  by_cases h15 : col + 1 < 16
  · rw [ite_eq_left h15]
    have hp : 2 ^ (col + 1) * c = 2 ^ col * (2 * c) := by ring
    rw [hp, ← mul_add]
  · have hc15 : col = 15 := by omega
    subst hc15
    rw [ite_eq_right h15, add_zero]
    have hp : 2 ^ 15 * (s + 2 * c) = 2 ^ 15 * s + 65536 * c := by ring
    rw [hp, Nat.add_mul_mod_self_left]
private theorem wfMuts_push_col {cur col a : ℕ} {m : List (ℕ × ℕ)}
    (ha278 : 278 ≤ a) (hacur : a < cur) (hwf : ∀ p ∈ m, 278 ≤ p.2 ∧ p.2 < cur + 1) :
    wfMuts (cur + 1) ((col, a) :: cond (decide (col + 1 < 16)) [(col + 1, cur)] [] ++ m) =
      true := by
  unfold wfMuts
  rw [List.all_eq_true]
  intro p hp
  simp only [List.cons_append, List.mem_cons, List.mem_append, Bool.and_eq_true,
    decide_eq_true_eq] at hp ⊢
  rcases hp with rfl | hmid | hm
  · exact ⟨ha278, by omega⟩
  · cases h15 : decide (col + 1 < 16) <;>
      simp only [h15, Bool.cond_false, Bool.cond_true, List.not_mem_nil, List.mem_singleton] at hmid
    subst hmid
    exact ⟨by omega, by omega⟩
  · exact hwf p hm

private theorem mutListSum_push_col (col a cur : ℕ) (m : List (ℕ × ℕ)) (δ : BitAssignment 437) :
    mutListSum ((col, a) :: cond (decide (col + 1 < 16)) [(col + 1, cur)] [] ++ m) δ =
      2 ^ col * (rb437 a δ).val +
        (if col + 1 < 16 then 2 ^ (col + 1) * (rb437 cur δ).val else 0) + mutListSum m δ := by
  by_cases h15 : col + 1 < 16 <;> simp [h15, mutListSum]
  omega

private theorem carry_col_sum_mod65536 {col sBit cBit tot rest lhs : ℕ} (hcol : col < 16)
    (hBit : sBit + 2 * cBit = tot) (hlhs : lhs = 2 ^ col * tot + rest) :
    (rest + (2 ^ col * sBit + (if col + 1 < 16 then 2 ^ (col + 1) * cBit else 0))) % 65536 =
      lhs % 65536 := by
  have hMod := carry_col_mod65536 col hcol sBit cBit
  rw [hBit] at hMod
  rw [Nat.add_comm rest, hlhs, Nat.add_mod, hMod, ← Nat.add_mod]

theorem applyXorSqOp_sound {cur cval cur' cval' : ℕ}
    {muts muts' : List (ℕ × ℕ)} {ros ros' : List (ℕ × RoTerm)} {op : XorSqOp}
    (h278 : 278 ≤ cur) (hwfM : wfMuts cur muts = true)
    (hApp : applyXorSqOp cur cval muts ros op = some (cur', cval', muts', ros'))
    (γ₀ δ : BitAssignment 437)
    (hcl : cleanRem 437 (437 - cur) δ)
    (hLow : ∀ w : Wire 437, w.val < 278 → δ w = γ₀ w) :
    let δ' := evalP57Steps (xorSqOpSteps op) δ
    278 ≤ cur' ∧ cur' ≤ 385 ∧ wfMuts cur' muts' = true ∧
      cleanRem 437 (437 - cur') δ' ∧
      (∀ w : Wire 437, w.val < 278 → δ' w = γ₀ w) ∧
      (cval' + mutListSum muts' δ' + roListSum ros' γ₀) % 65536 =
        (cval + mutListSum muts δ + roListSum ros γ₀) % 65536 := by
  cases op with
  | orHa col a b cout =>
      dsimp only [applyXorSqOp] at hApp
      have hg : (decide (col < 16) && decide (2 ^ col ≤ cval) &&
          decide (278 ≤ a) && decide (a < cur) &&
          decide (278 ≤ b) && decide (b < cur) && (a != b) &&
          (cout == cur) && decide (cur < 385)) = true := by
        cases h : (decide (col < 16) && decide (2 ^ col ≤ cval) &&
          decide (278 ≤ a) && decide (a < cur) &&
          decide (278 ≤ b) && decide (b < cur) && (a != b) &&
          (cout == cur) && decide (cur < 385)) <;> rw [h] at hApp
        cases hApp
      rw [hg] at hApp; dsimp only at hApp
      cases hp1 : popElem eqMut (col, a) muts with
      | none => rw [hp1] at hApp; cases hApp
      | some m1 =>
          rw [hp1] at hApp; dsimp only at hApp
          cases hp2 : popElem eqMut (col, b) m1 with
          | none => rw [hp2] at hApp; cases hApp
          | some m2 =>
              rw [hp2] at hApp; dsimp only at hApp
              have hall : m2.all (fun p ↦ (p.2 != a) && (p.2 != cout)) = true := by
                cases h : m2.all (fun p ↦ (p.2 != a) && (p.2 != cout)) <;> rw [h] at hApp
                cases hApp
              rw [hall] at hApp; dsimp only at hApp
              injection hApp with ht1
              rcases Prod.mk.inj ht1 with ⟨hcur', ht2⟩
              rcases Prod.mk.inj ht2 with ⟨hcval', ht3⟩
              rcases Prod.mk.inj ht3 with ⟨hmuts', hros'⟩
              subst hcur' hcval' hmuts' hros'
              simp only [Bool.and_eq_true, bne_iff_ne, beq_iff_eq, decide_eq_true_eq] at hg
              obtain ⟨⟨⟨⟨⟨⟨⟨⟨hcol, hcval⟩, ha278⟩, hacur⟩, hb278⟩, hbcur⟩, hab⟩, hcout⟩, hcur385⟩ :=
                hg
              subst cout
              have ha437 : a < 437 := by omega
              have hb437 : b < 437 := by omega
              have hc437 : cur < 437 := by omega
              have h0cur : δ ⟨cur, hc437⟩ = 0 := hcl ⟨cur, hc437⟩ (by dsimp; omega)
              obtain ⟨hEvA, hEvC, hEvOut⟩ := orHaCoreSteps_eval ha437 hb437 hc437
                hab (by omega) (by omega) δ h0cur
              let δ' := evalP57Steps (orHaCoreSteps a b cur) δ
              have hm2_sub : ∀ p ∈ m2, p ∈ muts :=
                fun p hp ↦ popElem_sub hp1 p (popElem_sub hp2 p hp)
              have hwf_m2 : ∀ p ∈ m2, 278 ≤ p.2 ∧ p.2 < cur + 1 := fun p hp ↦ by
                have hm := List.all_eq_true.mp hwfM p (hm2_sub p hp)
                simp only [Bool.and_eq_true, decide_eq_true_eq] at hm
                exact ⟨hm.1, by omega⟩
              have hm2_sum : mutListSum m2 δ' = mutListSum m2 δ :=
                mutListSum_congr m2 fun p hp ↦ by
                  have hp_ne := List.all_eq_true.mp hall p hp
                  simp only [Bool.and_eq_true, bne_iff_ne] at hp_ne
                  have hp_lt : p.2 < 437 := by
                    have := (hwf_m2 p hp).2
                    omega
                  rw [rb437_lt _ hp_lt, rb437_lt _ hp_lt]
                  exact hEvOut ⟨p.2, hp_lt⟩ hp_ne.1 hp_ne.2
              have hPopSum : mutListSum muts δ =
                  2 ^ col * (rb437 a δ).val + 2 ^ col * (rb437 b δ).val + mutListSum m2 δ := by
                rw [popElem_mutListSum hp1 δ, popElem_mutListSum hp2 δ]
                dsimp only
                omega
              dsimp only
              refine ⟨by omega, by omega, wfMuts_push_col ha278 hacur hwf_m2,
                fun w hw ↦ (hEvOut w (by omega) (by omega)).trans (hcl w (by omega)),
                fun w hw ↦ (hEvOut w (by omega) (by omega)).trans (hLow w hw), ?_⟩
              change ((cval - 2 ^ col) + mutListSum _ δ' + roListSum ros γ₀) % 65536 = _
              let sB := (1 + rb437 a δ + rb437 b δ).val
              let cB := (1 + (1 + rb437 a δ) * (1 + rb437 b δ)).val
              rw [mutListSum_push_col, hm2_sum, hEvA, hEvC]
              change ((cval - 2 ^ col) + (2 ^ col * sB +
                (if col + 1 < 16 then 2 ^ (col + 1) * cB else 0) + mutListSum m2 δ) +
                roListSum ros γ₀) % 65536 = _
              rw [show (cval - 2 ^ col) + (2 ^ col * sB +
                  (if col + 1 < 16 then 2 ^ (col + 1) * cB else 0) + mutListSum m2 δ) +
                  roListSum ros γ₀ = ((cval - 2 ^ col) + mutListSum m2 δ + roListSum ros γ₀) +
                  (2 ^ col * sB + (if col + 1 < 16 then 2 ^ (col + 1) * cB else 0)) by omega]
              exact carry_col_sum_mod65536 hcol (orHa_bit_val (rb437 a δ) (rb437 b δ)) (by
                rw [hPopSum]
                have hd : 2 ^ col * (1 + (rb437 a δ).val + (rb437 b δ).val) =
                    2 ^ col + 2 ^ col * (rb437 a δ).val + 2 ^ col * (rb437 b δ).val := by ring
                omega)
  | faGen col a opB opC cout =>
      dsimp only [applyXorSqOp] at hApp
      have hg : (decide (col < 16) && decide (278 ≤ a) && decide (a < cur) &&
          wfOperand cur opB && wfOperand cur opC &&
          opSuppDisj opB opC &&
          !inOpSupp a opB && !inOpSupp a opC &&
          !inOpSupp cout opB && !inOpSupp cout opC &&
          (cout == cur) && decide (cur < 385)) = true := by
        cases h : (decide (col < 16) && decide (278 ≤ a) && decide (a < cur) &&
          wfOperand cur opB && wfOperand cur opC &&
          opSuppDisj opB opC &&
          !inOpSupp a opB && !inOpSupp a opC &&
          !inOpSupp cout opB && !inOpSupp cout opC &&
          (cout == cur) && decide (cur < 385)) <;> rw [h] at hApp
        cases hApp
      rw [hg] at hApp; dsimp only at hApp
      cases hp1 : popElem eqMut (col, a) muts with
      | none => rw [hp1] at hApp; cases hApp
      | some m1 =>
          rw [hp1] at hApp; dsimp only at hApp
          cases hpB : popOperand col opB m1 ros with
          | none => rw [hpB] at hApp; cases hApp
          | some mr2 =>
              rcases mr2 with ⟨m2, r2⟩
              rw [hpB] at hApp; dsimp only at hApp
              cases hpC : popOperand col opC m2 r2 with
              | none => rw [hpC] at hApp; cases hApp
              | some mr3 =>
                  rcases mr3 with ⟨m3, r3⟩
                  rw [hpC] at hApp; dsimp only at hApp
                  have hall : m3.all (fun p ↦ (p.2 != a) && (p.2 != cout) &&
                      !inOpSupp p.2 opB && !inOpSupp p.2 opC) = true := by
                    cases h : m3.all (fun p ↦ (p.2 != a) && (p.2 != cout) &&
                        !inOpSupp p.2 opB && !inOpSupp p.2 opC) <;> rw [h] at hApp
                    cases hApp
                  rw [hall] at hApp; dsimp only at hApp
                  injection hApp with ht1
                  rcases Prod.mk.inj ht1 with ⟨hcur', ht2⟩
                  rcases Prod.mk.inj ht2 with ⟨hcval', ht3⟩
                  rcases Prod.mk.inj ht3 with ⟨hmuts', hros'⟩
                  subst hcur' hcval' hmuts' hros'
                  simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq,
                    decide_eq_true_eq] at hg
                  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hcol, ha278⟩, hacur⟩, hwfB⟩, hwfC⟩, hdisjBC⟩,
                    ha_nB⟩, ha_nC⟩, hc_nB⟩, hc_nC⟩, hcout⟩, hcur385⟩ := hg
                  subst cout
                  have hcur437 : cur ≤ 437 := by omega
                  let b := opTarget opB
                  let c := opTarget opC
                  have hb_in : inOpSupp b opB = true := opTarget_in_supp opB
                  have hc_in : inOpSupp c opC = true := opTarget_in_supp opC
                  have hb_nC : inOpSupp b opC = false := opSuppDisj_spec hdisjBC hb_in
                  have hb_lt_cur : b < cur := opTarget_lt_cur hwfB h278
                  have hc_lt_cur : c < cur := opTarget_lt_cur hwfC h278
                  have ha437 : a < 437 := by omega
                  have hb437 : b < 437 := by omega
                  have hc437 : c < 437 := by omega
                  have hd437 : cur < 437 := by omega
                  have hab : a ≠ b := fun h ↦ by rw [h, hb_in] at ha_nB; cases ha_nB
                  have hac : a ≠ c := fun h ↦ by rw [h, hc_in] at ha_nC; cases ha_nC
                  have hbc : b ≠ c := fun h ↦ by rw [h, hc_in] at hb_nC; cases hb_nC
                  -- Step 1: Prep opB on δ -> β₁
                  obtain ⟨hB_out, hB_val, hB_un⟩ := opPrep_spec hwfB h278 hcur437 δ γ₀ δ
                    (fun w _ hw ↦ hLow w hw) (fun _ _ ↦ rfl)
                  let β₁ := evalP57Steps (opPrepSteps opB) δ
                  -- Step 2: Prep opC on β₁ -> β₂
                  have hC_low : ∀ w : Wire 437,
                    inOpSupp w.val opC = true → w.val < 278 → β₁ w = γ₀ w :=
                    fun w hwC hw278 ↦ by
                      have hw_nB : inOpSupp w.val opB = false := by
                        by_contra h1
                        have h1t : inOpSupp w.val opB = true := Bool.eq_true_of_not_eq_false h1
                        rw [opSuppDisj_spec hdisjBC h1t] at hwC; cases hwC
                      exact (hB_out w hw_nB).trans (hLow w hw278)
                  have hC_mut : ∀ u : ℕ, opC = .mutW u → rb437 u β₁ = rb437 u δ :=
                    fun u huC ↦ by
                      subst huC
                      have hu_lt : u < 437 := by
                        simp only [wfOperand, Bool.and_eq_true, decide_eq_true_eq] at hwfC; omega
                      have hu_nB : inOpSupp u opB = false := by
                        by_contra h1
                        have h1t : inOpSupp u opB = true := Bool.eq_true_of_not_eq_false h1
                        have := opSuppDisj_spec hdisjBC h1t
                        simp [inOpSupp] at this
                      rw [rb437_lt _ hu_lt, rb437_lt _ hu_lt]
                      exact hB_out ⟨u, hu_lt⟩ hu_nB
                  obtain ⟨hC_out, hC_val, hC_un⟩ :=
                    opPrep_spec hwfC h278 hcur437 δ γ₀ β₁ hC_low hC_mut
                  let β₂ := evalP57Steps (opPrepSteps opC) β₁
                  have hβ₂_a : rb437 a β₂ = rb437 a δ := by
                    rw [rb437_lt _ ha437, rb437_lt _ ha437]
                    exact (hC_out ⟨a, ha437⟩ ha_nC).trans (hB_out ⟨a, ha437⟩ ha_nB)
                  have hβ₂_b : rb437 b β₂ = evalSqOperand δ γ₀ opB := by
                    have h1 : rb437 b β₂ = rb437 b β₁ := by
                      rw [rb437_lt _ hb437, rb437_lt _ hb437]
                      exact hC_out ⟨b, hb437⟩ hb_nC
                    exact h1.trans hB_val
                  have hβ₂_cur : β₂ ⟨cur, hd437⟩ = 0 :=
                    (hC_out ⟨cur, hd437⟩ hc_nC).trans
                      ((hB_out ⟨cur, hd437⟩ hc_nB).trans (hcl ⟨cur, hd437⟩ (by dsimp; omega)))
                  -- Step 3: Core FA on β₂ -> η
                  obtain ⟨hFA_a, hFA_d, hFA_out⟩ := faCoreSteps_eval ha437 hb437 hc437 hd437
                    hab hac (by omega) hbc (by omega) (by omega) β₂ hβ₂_cur
                  let η := evalP57Steps (faCoreSteps a b c cur) β₂
                  -- Step 4: Unprep opC on η -> η₁
                  have hη_on_C : ∀ w : Wire 437, inOpSupp w.val opC = true → η w = β₂ w :=
                    fun w hwC ↦ hFA_out w
                      (fun hwa ↦ by rw [hwa, ha_nC] at hwC; cases hwC)
                      (fun hwd ↦ by rw [hwd, hc_nC] at hwC; cases hwC)
                  obtain ⟨hUnC_out, hUnC_in⟩ := hC_un η hη_on_C
                  let η₁ := evalP57Steps (opUnprepSteps opC) η
                  -- Step 5: Unprep opB on η₁ -> δ'
                  have hη₁_on_B : ∀ w : Wire 437, inOpSupp w.val opB = true → η₁ w = β₁ w :=
                    fun w hwB ↦ by
                      have hw_nC : inOpSupp w.val opC = false := opSuppDisj_spec hdisjBC hwB
                      dsimp only [η₁]
                      rw [hUnC_out w hw_nC]
                      dsimp only [η]
                      rw [hFA_out w (fun hwa ↦ by rw [hwa, ha_nB] at hwB; cases hwB)
                          (fun hwd ↦ by rw [hwd, hc_nB] at hwB; cases hwB)]
                      exact hC_out w hw_nC
                  obtain ⟨hUnB_out, hUnB_in⟩ := hB_un η₁ hη₁_on_B
                  let δ' := evalP57Steps (opUnprepSteps opB) η₁
                  have hStepsEq : evalP57Steps (xorSqOpSteps (.faGen col a opB opC cur)) δ = δ' :=
                    by
                    dsimp only [xorSqOpSteps]
                    repeat rw [evalP57Steps_append]
                  have hδ'_a : rb437 a δ' =
                      rb437 a δ + evalSqOperand δ γ₀ opB + evalSqOperand δ γ₀ opC := by
                    have h1 : δ' ⟨a, ha437⟩ = η ⟨a, ha437⟩ :=
                      (hUnB_out ⟨a, ha437⟩ ha_nB).trans (hUnC_out ⟨a, ha437⟩ ha_nC)
                    rw [rb437_lt _ ha437, h1, ← rb437_lt η ha437, hFA_a,
                      hβ₂_a, hβ₂_b, hC_val]
                  have hδ'_d : rb437 cur δ' =
                      (rb437 a δ + evalSqOperand δ γ₀ opC) *
                        (evalSqOperand δ γ₀ opB + evalSqOperand δ γ₀ opC) +
                        evalSqOperand δ γ₀ opC := by
                    have h1 : δ' ⟨cur, hd437⟩ = η ⟨cur, hd437⟩ :=
                      (hUnB_out ⟨cur, hd437⟩ hc_nB).trans (hUnC_out ⟨cur, hd437⟩ hc_nC)
                    rw [rb437_lt _ hd437, h1, ← rb437_lt η hd437, hFA_d,
                      hβ₂_a, hβ₂_b, hC_val]
                  have hδ'_other : ∀ w : Wire 437, w.val ≠ a → w.val ≠ cur → δ' w = δ w :=
                    fun w hna hnd ↦ by
                      by_cases hwB : inOpSupp w.val opB = true
                      · exact hUnB_in w hwB
                      · have hwBf : inOpSupp w.val opB = false := Bool.eq_false_iff.mpr hwB
                        dsimp only [δ']
                        rw [hUnB_out w hwBf]
                        by_cases hwC : inOpSupp w.val opC = true
                        · exact (hUnC_in w hwC).trans (hB_out w hwBf)
                        · have hwCf : inOpSupp w.val opC = false := Bool.eq_false_iff.mpr hwC
                          dsimp only [η₁]
                          rw [hUnC_out w hwCf]
                          dsimp only [η]
                          rw [hFA_out w hna hnd]
                          exact (hC_out w hwCf).trans (hB_out w hwBf)
                  obtain ⟨hSubB, hSumB⟩ := popOperand_sum hpB δ γ₀
                  obtain ⟨hSubC, hSumC⟩ := popOperand_sum hpC δ γ₀
                  have hm3_sub : ∀ p ∈ m3, p ∈ muts :=
                    fun p hp ↦ popElem_sub hp1 p (hSubB p (hSubC p hp))
                  have hwf_m3 : ∀ p ∈ m3, 278 ≤ p.2 ∧ p.2 < cur + 1 := fun p hp ↦ by
                    have hm := List.all_eq_true.mp hwfM p (hm3_sub p hp)
                    simp only [Bool.and_eq_true, decide_eq_true_eq] at hm
                    exact ⟨hm.1, by omega⟩
                  have hm3_sum : mutListSum m3 δ' = mutListSum m3 δ :=
                    mutListSum_congr m3 fun p hp ↦ by
                      have hp_ne := List.all_eq_true.mp hall p hp
                      simp only [Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne] at hp_ne
                      have hp_lt : p.2 < 437 := by
                        have := (hwf_m3 p hp).2
                        omega
                      rw [rb437_lt _ hp_lt, rb437_lt _ hp_lt]
                      exact hδ'_other ⟨p.2, hp_lt⟩ hp_ne.1.1.1 hp_ne.1.1.2
                  have hPopAll : mutListSum muts δ + roListSum ros γ₀ =
                      2 ^ col * ((rb437 a δ).val + (evalSqOperand δ γ₀ opB).val +
                        (evalSqOperand δ γ₀ opC).val) + (mutListSum m3 δ + roListSum r3 γ₀) := by
                    rw [popElem_mutListSum hp1 δ, add_assoc, hSumB, hSumC]
                    ring
                  dsimp only
                  rw [hStepsEq]
                  refine ⟨by omega, by omega, wfMuts_push_col ha278 hacur hwf_m3,
                    fun w hw ↦ (hδ'_other w (by omega) (by omega)).trans (hcl w (by omega)),
                    fun w hw ↦ (hδ'_other w (by omega) (by omega)).trans (hLow w hw), ?_⟩
                  let vB := evalSqOperand δ γ₀ opB
                  let vC := evalSqOperand δ γ₀ opC
                  let sF := (rb437 a δ + vB + vC).val
                  let cF := ((rb437 a δ + vC) * (vB + vC) + vC).val
                  rw [mutListSum_push_col, hm3_sum, hδ'_a, hδ'_d]
                  change (cval + (2 ^ col * sF +
                    (if col + 1 < 16 then 2 ^ (col + 1) * cF else 0) + mutListSum m3 δ) +
                    roListSum r3 γ₀) % 65536 = _
                  rw [show cval + (2 ^ col * sF +
                      (if col + 1 < 16 then 2 ^ (col + 1) * cF else 0) + mutListSum m3 δ) +
                      roListSum r3 γ₀ = (cval + (mutListSum m3 δ + roListSum r3 γ₀)) +
                      (2 ^ col * sF + (if col + 1 < 16 then 2 ^ (col + 1) * cF else 0)) by omega]
                  exact carry_col_sum_mod65536 hcol (fa_bit_val (rb437 a δ) vB vC) (by
                    have := hPopAll
                    dsimp only [vB, vC]
                    omega)
  | flip15 a =>
      dsimp only [applyXorSqOp] at hApp
      have hg : (decide (32768 ≤ cval) && decide (278 ≤ a) && decide (a < cur) && decide (cur ≤
        385)) = true := by
        cases h : (decide (32768 ≤ cval) && decide (278 ≤ a) && decide (a < cur) && decide (cur ≤
          385)) <;>
          rw [h] at hApp
        cases hApp
      rw [hg] at hApp; dsimp only at hApp
      cases hp1 : popElem eqMut (15, a) muts with
      | none => rw [hp1] at hApp; cases hApp
      | some m1 =>
          rw [hp1] at hApp; dsimp only at hApp
          have hall : m1.all (fun p ↦ p.2 != a) = true := by
            cases h : m1.all (fun p ↦ p.2 != a) <;> rw [h] at hApp
            cases hApp
          rw [hall] at hApp; dsimp only at hApp
          injection hApp with ht1
          rcases Prod.mk.inj ht1 with ⟨hcur', ht2⟩
          rcases Prod.mk.inj ht2 with ⟨hcval', ht3⟩
          rcases Prod.mk.inj ht3 with ⟨hmuts', hros'⟩
          subst hcur' hcval' hmuts' hros'
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hg
          obtain ⟨⟨⟨hcval, ha278⟩, hacur⟩, hcur385⟩ := hg
          have ha437 : a < 437 := by omega
          dsimp only [xorSqOpSteps, evalP57Steps, evalP57Step]
          rw [dite_eq_left ha437]
          let δ' := Function.update δ ⟨a, ha437⟩ (δ ⟨a, ha437⟩ + 1)
          have hwf_out : wfMuts cur ((15, a) :: m1) = true := by
            unfold wfMuts
            rw [List.all_eq_true]
            intro p hp
            rcases List.mem_cons.mp hp with rfl | hm1
            · simp [ha278, hacur]
            · exact List.all_eq_true.mp hwfM p (popElem_sub hp1 p hm1)
          have hcl' : cleanRem 437 (437 - cur) δ' := fun w hw ↦ by
            dsimp only [δ']
            rw [Function.update_of_ne (wire_ne_of_gt (by dsimp; omega))]
            exact hcl w hw
          have hLow' : ∀ w : Wire 437, w.val < 278 → δ' w = γ₀ w := fun w hw ↦ by
            dsimp only [δ']
            rw [Function.update_of_ne (wire_ne_of_lt (by dsimp; omega))]
            exact hLow w hw
          have hm1_sum : mutListSum m1 δ' = mutListSum m1 δ := by
            refine mutListSum_congr m1 fun p hp ↦ ?_
            have hp_ne : p.2 ≠ a := by
              have h := List.all_eq_true.mp hall p hp
              simpa [bne_iff_ne] using h
            have hm := List.all_eq_true.mp hwfM p (popElem_sub hp1 p hp)
            simp only [Bool.and_eq_true, decide_eq_true_eq] at hm
            have hp437 : p.2 < 437 := by omega
            rw [rb437_lt _ hp437, rb437_lt _ hp437]
            exact Function.update_of_ne (wire_ne_val hp_ne) _ _
          refine ⟨h278, hcur385, hwf_out, hcl', hLow', ?_⟩
          dsimp only [mutListSum]
          rw [hm1_sum, popElem_mutListSum hp1 δ, rb437_lt δ' ha437, rb437_lt δ ha437]
          have hSelf : δ' ⟨a, ha437⟩ = δ ⟨a, ha437⟩ + 1 := Function.update_self _ _ _
          rw [hSelf]
          have hBit := flip15_bit_val (δ ⟨a, ha437⟩)
          have hp15 : (2 : ℕ) ^ 15 = 32768 := by decide
          rw [hp15]
          have hR1 : (cval - 32768) + (32768 * (δ ⟨a,
            ha437⟩ + 1).val + mutListSum m1 δ) + roListSum ros γ₀ =
              (32768 * (δ ⟨a,
                ha437⟩ + 1).val) + ((cval - 32768) + mutListSum m1 δ + roListSum ros γ₀) := by omega
          have hR2 : cval + (32768 * (δ ⟨a, ha437⟩).val + mutListSum m1 δ) + roListSum ros γ₀ =
              (32768 + 32768 * (δ ⟨a,
                ha437⟩).val) + ((cval - 32768) + mutListSum m1 δ + roListSum ros γ₀) := by omega
          rw [hR1, hR2, Nat.add_mod (32768 * _), ← hBit, ← Nat.add_mod]
theorem applyXorSqOps_sound :
    ∀ (ops : List XorSqOp) {cur cval cur' cval' : ℕ}
      {muts muts' : List (ℕ × ℕ)} {ros ros' : List (ℕ × RoTerm)}
      (_h278 : 278 ≤ cur) (_hcur385 : cur ≤ 385) (_hwfM : wfMuts cur muts = true)
      (_hApp : applyXorSqOps cur cval muts ros ops = some (cur', cval', muts', ros'))
      (γ₀ δ : BitAssignment 437)
      (_hcl : cleanRem 437 (437 - cur) δ)
      (_hLow : ∀ w : Wire 437, w.val < 278 → δ w = γ₀ w),
      let δ' := evalP57Steps (ops.flatMap xorSqOpSteps) δ
      cleanRem 437 (437 - cur') δ' ∧
        (∀ w : Wire 437, w.val < 278 → δ' w = γ₀ w) ∧
        (cval' + mutListSum muts' δ' + roListSum ros' γ₀) % 65536 =
          (cval + mutListSum muts δ + roListSum ros γ₀) % 65536
  | [], _, _, _, _, _, _, _, _, _, _, _, hApp, _, δ, hcl, hLow => by
      dsimp only [applyXorSqOps] at hApp
      injection hApp with ht1
      rcases Prod.mk.inj ht1 with ⟨rfl, ht2⟩
      rcases Prod.mk.inj ht2 with ⟨rfl, ht3⟩
      rcases Prod.mk.inj ht3 with ⟨rfl, rfl⟩
      exact ⟨hcl, hLow, rfl⟩
  | op :: rest, cur, cval, cur', cval', muts, muts', ros, ros', h278, _, hwfM, hApp, γ₀, δ, hcl,
    hLow => by
      dsimp only [applyXorSqOps] at hApp
      cases h1 : applyXorSqOp cur cval muts ros op with
      | none => rw [h1] at hApp; cases hApp
      | some st1 =>
          rcases st1 with ⟨cur1, cval1, muts1, ros1⟩
          rw [h1] at hApp; dsimp only at hApp
          obtain ⟨h278_1, h385_1, hwf1, hcl1, hLow1, hSum1⟩ :=
            applyXorSqOp_sound h278 hwfM h1 γ₀ δ hcl hLow
          obtain ⟨hcl2, hLow2, hSum2⟩ :=
            applyXorSqOps_sound rest h278_1 h385_1 hwf1 hApp γ₀
              (evalP57Steps (xorSqOpSteps op) δ) hcl1 hLow1
          have hFlat : (op :: rest).flatMap xorSqOpSteps =
              xorSqOpSteps op ++ rest.flatMap xorSqOpSteps := rfl
          dsimp only
          rw [hFlat, evalP57Steps_append]
          exact ⟨hcl2, hLow2, hSum2.trans hSum1⟩
/-- Single `5`-step NOR gadget allocating `(1 + u0) * (1 + u1)` into clean scratch wire `dst`. -/
def z0SingleSteps (u0 u1 dst : ℕ) : List P57Step :=
  [.x u0, .x u1, .tempAnd u0 u1 dst, .x u1, .x u0]
theorem z0SingleSteps_eval {u0 u1 dst : ℕ}
    (hu0 : u0 < 437) (hu1 : u1 < 437) (hd : dst < 437)
    (h01 : u0 ≠ u1) (h0d : u0 ≠ dst) (h1d : u1 ≠ dst)
    (β : BitAssignment 437) (h0 : β ⟨dst, hd⟩ = 0) :
    evalP57Steps (z0SingleSteps u0 u1 dst) β =
      Function.update β ⟨dst, hd⟩ ((1 + β ⟨u0, hu0⟩) * (1 + β ⟨u1, hu1⟩)) := by
  have ht : u0 < 437 ∧ u1 < 437 ∧ dst < 437 ∧ u0 ≠ u1 ∧ u0 ≠ dst ∧ u1 ≠ dst :=
    ⟨hu0, hu1, hd, h01, h0d, h1d⟩
  dsimp only [z0SingleSteps, evalP57Steps, evalP57Step]
  rw [dite_eq_left hu0, dite_eq_left hu1, dite_eq_left ht, dite_eq_left hu1, dite_eq_left hu0]
  let w0 : Wire 437 := ⟨u0, hu0⟩
  let w1 : Wire 437 := ⟨u1, hu1⟩
  let wd : Wire 437 := ⟨dst, hd⟩
  have hw01 : w0 ≠ w1 := wire_ne_val h01
  have hw0d : w0 ≠ wd := wire_ne_val h0d
  have hw1d : w1 ≠ wd := wire_ne_val h1d
  funext w
  by_cases hwd : w = wd
  · rw [hwd, Function.update_of_ne hw0d.symm, Function.update_of_ne hw1d.symm,
      Function.update_self, Function.update_of_ne hw1d.symm, Function.update_of_ne hw0d.symm,
      Function.update_of_ne hw01, Function.update_self, Function.update_self,
      Function.update_of_ne hw01.symm, Function.update_self, h0, zero_add]
    ring
  · by_cases hw0 : w = w0
    · rw [hw0, Function.update_self, Function.update_of_ne hw01, Function.update_of_ne hw0d,
        Function.update_of_ne hw01, Function.update_self, Function.update_of_ne hw0d,
        zmod2_add_one_cancel]
    · by_cases hw1 : w = w1
      · rw [hw1, Function.update_of_ne hw01.symm, Function.update_self, Function.update_of_ne hw1d,
          Function.update_self, Function.update_of_ne hw1d, zmod2_add_one_cancel,
          Function.update_of_ne hw01.symm]
      · rw [Function.update_of_ne hw0, Function.update_of_ne hw1, Function.update_of_ne hwd,
          Function.update_of_ne hw1, Function.update_of_ne hw0, Function.update_of_ne hwd]
/-- Convert `ZMod 2` bit to `Bool`. -/
def z2bP6 (x : ZMod 2) : Bool := decide (x = 1)
theorem cond_z2bP6 (x : ZMod 2) : cond (z2bP6 x) 1 0 = x.val := by
  rcases bit_cases x with rfl | rfl <;> decide
theorem cond_not_z2bP6 (x : ZMod 2) : cond (!z2bP6 x) 1 0 = (1 + x).val := by
  rcases bit_cases x with rfl | rfl <;> decide
theorem cond_xnor_z2bP6 (x y : ZMod 2) : cond (z2bP6 x == z2bP6 y) 1 0 = (1 + x + y).val := by
  rcases bit_cases x with rfl | rfl <;> rcases bit_cases y with rfl | rfl <;> decide
theorem cond_z0_z2bP6 (x y : ZMod 2) :
    cond ((!z2bP6 x) && (!z2bP6 y)) 1 0 = ((1 + x) * (1 + y)).val := by
  rcases bit_cases x with rfl | rfl <;> rcases bit_cases y with rfl | rfl <;> decide
/-- `8`-bit unsigned value on `Bool` inputs. -/
def bool8ValAux (b0 b1 b2 b3 b4 b5 b6 b7 : Bool) : ℕ :=
  cond b0 1 0 + 2 * cond b1 1 0 + 4 * cond b2 1 0 + 8 * cond b3 1 0 +
    16 * cond b4 1 0 + 32 * cond b5 1 0 + 64 * cond b6 1 0 + 128 * cond b7 1 0
theorem bool8Val_eq_bitsValAux (f : Fin 8 → ZMod 2) :
    bool8ValAux (z2bP6 (f 0)) (z2bP6 (f 1)) (z2bP6 (f 2)) (z2bP6 (f 3))
      (z2bP6 (f 4)) (z2bP6 (f 5)) (z2bP6 (f 6)) (z2bP6 (f 7)) = bitsVal f := by
  unfold bitsVal bool8ValAux
  simp only [Fin.sum_univ_eight, cond_z2bP6]
  dsimp
  ring
/-- Per-axis `z0` term on `Bool` inputs. -/
def axisZ0Bool (b0 b1 : Bool) : ℕ :=
  cond ((!b0) && (!b1)) 1 0
/-- Per-axis shifted `RoTerm` sum on `Bool` inputs (`41` terms). -/
def axisRoSumBool (b0 b1 b2 b3 b4 b5 b6 b7 : Bool) : ℕ :=
    1 * cond (!b2) 1 0 + 2 * cond (!b3) 1 0 + 4 * cond (!b4) 1 0 + 8 * cond (!b5) 1 0 +
    16 * cond (!b6) 1 0 + 32 * cond (!b7) 1 0 + 64 * cond b0 1 0 + 128 * cond b1 1 0 +
    256 * cond b2 1 0 + 512 * cond b3 1 0 + 1024 * cond b4 1 0 + 2048 * cond b5 1 0 +
    4096 * cond b6 1 0 + 8192 * cond b7 1 0 + 1 * cond (b0 == b2) 1 0 + 2 * cond (b0 == b3) 1 0 +
    4 * cond (b0 == b4) 1 0 + 8 * cond (b0 == b5) 1 0 + 16 * cond (b0 == b6) 1 0 + 32 * cond (b0 ==
      b7) 1 0 +
    2 * cond (b1 == b2) 1 0 + 4 * cond (b1 == b3) 1 0 + 8 * cond (b1 == b4) 1 0 + 16 * cond (b1 ==
      b5) 1 0 +
    32 * cond (b1 == b6) 1 0 + 64 * cond (b1 == b7) 1 0 + 8 * cond (b2 == b3) 1 0 + 16 * cond (b2 ==
      b4) 1 0 +
    32 * cond (b2 == b5) 1 0 + 64 * cond (b2 == b6) 1 0 + 128 * cond (b2 == b7) 1 0 + 32 *
      cond (b3 == b4) 1 0 +
    64 * cond (b3 == b5) 1 0 + 128 * cond (b3 == b6) 1 0 + 256 * cond (b3 == b7) 1 0 + 128 *
      cond (b4 == b5) 1 0 +
    256 * cond (b4 == b6) 1 0 + 512 * cond (b4 == b7) 1 0 + 512 * cond (b5 == b6) 1 0 + 1024 *
      cond (b5 == b7) 1 0 +
    2048 * cond (b6 == b7) 1 0
theorem axisXorSqBool_eq (b0 b1 b2 b3 b4 b5 b6 b7 : Bool) :
    axisZ0Bool b0 b1 + axisRoSumBool b0 b1 b2 b3 b4 b5 b6 b7 =
      (bool8ValAux b0 b1 b2 b3 b4 b5 b6 b7 * bool8ValAux b0 b1 b2 b3 b4 b5 b6 b7) / 4 + 5461 := by
  revert b0 b1 b2 b3 b4 b5 b6 b7
  decide
/-- Build `41`-element initial `RoTerm` list from `8` wire indices. -/
def mkInitRosAxis (u0 u1 u2 u3 u4 u5 u6 u7 : ℕ) : List (ℕ × RoTerm) :=
  [(0, .notW u2), (1, .notW u3), (2, .notW u4), (3, .notW u5), (4, .notW u6), (5, .notW u7),
   (6, .wire u0), (7, .wire u1), (8, .wire u2), (9, .wire u3), (10, .wire u4), (11, .wire u5),
   (12, .wire u6), (13, .wire u7), (0, .xnorW u0 u2), (1, .xnorW u0 u3), (2, .xnorW u0 u4),
   (3, .xnorW u0 u5), (4, .xnorW u0 u6), (5, .xnorW u0 u7), (1, .xnorW u1 u2), (2, .xnorW u1 u3),
   (3, .xnorW u1 u4), (4, .xnorW u1 u5), (5, .xnorW u1 u6), (6, .xnorW u1 u7), (3, .xnorW u2 u3),
   (4, .xnorW u2 u4), (5, .xnorW u2 u5), (6, .xnorW u2 u6), (7, .xnorW u2 u7), (5, .xnorW u3 u4),
   (6, .xnorW u3 u5), (7, .xnorW u3 u6), (8, .xnorW u3 u7), (7, .xnorW u4 u5), (8, .xnorW u4 u6),
   (9, .xnorW u4 u7), (9, .xnorW u5 u6), (10, .xnorW u5 u7), (11, .xnorW u6 u7)]
/-- Initial `41`-element read-only list for axis `0`. -/
def initRosAxis0 : List (ℕ × RoTerm) := mkInitRosAxis 177 178 179 180 181 182 183 275
/-- Initial `41`-element read-only list for axis `1`. -/
def initRosAxis1 : List (ℕ × RoTerm) := mkInitRosAxis 184 185 186 187 188 189 190 276
/-- Initial `41`-element read-only list for axis `2`. -/
def initRosAxis2 : List (ℕ × RoTerm) := mkInitRosAxis 191 192 193 194 195 196 197 277
/-- Initial `41`-element read-only list for axis `w`. -/
def initRosAxis (w : Fin 3) : List (ℕ × RoTerm) :=
  match w.val with | 0 => initRosAxis0 | 1 => initRosAxis1 | _ => initRosAxis2
private theorem roListSum_mkInitRosAxis (u0 u1 u2 u3 u4 u5 u6 u7 : ℕ) (γ : BitAssignment 437) :
    roListSum (mkInitRosAxis u0 u1 u2 u3 u4 u5 u6 u7) γ =
      axisRoSumBool (z2bP6 (rb437 u0 γ)) (z2bP6 (rb437 u1 γ)) (z2bP6 (rb437 u2 γ))
        (z2bP6 (rb437 u3 γ)) (z2bP6 (rb437 u4 γ)) (z2bP6 (rb437 u5 γ))
        (z2bP6 (rb437 u6 γ)) (z2bP6 (rb437 u7 γ)) := by
  dsimp only [mkInitRosAxis, roListSum, evalRoTerm, axisRoSumBool]
  simp only [← cond_xnor_z2bP6]
  simp only [← cond_not_z2bP6]
  simp only [← cond_z2bP6]
  ring
theorem initRosAxis_sum_eq (w : Fin 3) (γ : BitAssignment 437) :
    ((1 + γ (d8Wire w 0)) * (1 + γ (d8Wire w 1))).val + roListSum (initRosAxis w) γ =
      (bitsVal (fun k : Fin 8 ↦ γ (d8Wire w k)) *
        bitsVal (fun k : Fin 8 ↦ γ (d8Wire w k))) / 4 + 5461 := by
  let f : Fin 8 → ZMod 2 := fun k ↦ γ (d8Wire w k)
  have hBool := axisXorSqBool_eq (z2bP6 (f 0)) (z2bP6 (f 1)) (z2bP6 (f 2)) (z2bP6 (f 3))
    (z2bP6 (f 4)) (z2bP6 (f 5)) (z2bP6 (f 6)) (z2bP6 (f 7))
  rw [bool8Val_eq_bitsValAux f] at hBool
  have hrb (w0 : Fin 3) (u : ℕ) (k : Fin 8) (hu : u < 437)
      (he : (⟨u, hu⟩ : Wire 437) = d8Wire w0 k) : rb437 u γ = γ (d8Wire w0 k) :=
    (rb437_lt γ hu).trans (congrArg γ he)
  have hro : roListSum (initRosAxis w) γ = axisRoSumBool (z2bP6 (f 0)) (z2bP6 (f 1))
      (z2bP6 (f 2)) (z2bP6 (f 3)) (z2bP6 (f 4)) (z2bP6 (f 5)) (z2bP6 (f 6)) (z2bP6 (f 7)) := by
    dsimp only [f]
    rcases w with ⟨_ | _ | _ | _, hn⟩
    · exact (roListSum_mkInitRosAxis 177 178 179 180 181 182 183 275 γ).trans (by
        rw [hrb 0 177 0 (by decide) (by decide), hrb 0 178 1 (by decide) (by decide),
          hrb 0 179 2 (by decide) (by decide), hrb 0 180 3 (by decide) (by decide),
          hrb 0 181 4 (by decide) (by decide), hrb 0 182 5 (by decide) (by decide),
          hrb 0 183 6 (by decide) (by decide), hrb 0 275 7 (by decide) (by decide)]
        rfl)
    · exact (roListSum_mkInitRosAxis 184 185 186 187 188 189 190 276 γ).trans (by
        rw [hrb 1 184 0 (by decide) (by decide), hrb 1 185 1 (by decide) (by decide),
          hrb 1 186 2 (by decide) (by decide), hrb 1 187 3 (by decide) (by decide),
          hrb 1 188 4 (by decide) (by decide), hrb 1 189 5 (by decide) (by decide),
          hrb 1 190 6 (by decide) (by decide), hrb 1 276 7 (by decide) (by decide)]
        rfl)
    · exact (roListSum_mkInitRosAxis 191 192 193 194 195 196 197 277 γ).trans (by
        rw [hrb 2 191 0 (by decide) (by decide), hrb 2 192 1 (by decide) (by decide),
          hrb 2 193 2 (by decide) (by decide), hrb 2 194 3 (by decide) (by decide),
          hrb 2 195 4 (by decide) (by decide), hrb 2 196 5 (by decide) (by decide),
          hrb 2 197 6 (by decide) (by decide), hrb 2 277 7 (by decide) (by decide)]
        rfl)
    · omega
  rw [← cond_z0_z2bP6 (f 0) (f 1), hro]
  exact hBool
/-- Initial `3` mutable wires `(0, 278), (0, 279), (0, 280)` after `xorSqZ0Steps`. -/
def initMutsXorSq : List (ℕ × ℕ) := [(0, 278), (0, 279), (0, 280)]
/-- Initial `123` read-only terms across axes `0, 1, 2`. -/
def initRosXorSq : List (ℕ × RoTerm) :=
  initRosAxis0 ++ initRosAxis1 ++ initRosAxis2
/-- Final `24` mutable `(col, wire)` pairs at `cur = 385` after `xorSqOps105`. -/
def finalMuts24 : List (ℕ × ℕ) :=
  [(15, 384), (14, 382), (13, 380), (13, 379), (12, 377), (12, 375), (11, 368), (11, 371), (10,
  361), (10, 366), (9, 354), (9, 351), (8, 344), (8, 341), (7, 338), (6, 323), (6, 320), (5, 316),
  (4, 304), (3, 296), (2, 288), (1, 283), (0, 280), (0, 278)]
theorem xorSqZ0Steps_spec (γ₀ : BitAssignment 437) (hcl : cleanRem 437 (437 - 278) γ₀) :
    let δ₀ := evalP57Steps xorSqZ0Steps γ₀
    cleanRem 437 (437 - 281) δ₀ ∧
      (∀ w : Wire 437, w.val < 278 → δ₀ w = γ₀ w) ∧
      (49153 + mutListSum initMutsXorSq δ₀ + roListSum initRosXorSq γ₀) % 65536 =
        ((bitsVal (fun k : Fin 8 ↦ γ₀ (d8Wire 0 k)) * bitsVal (fun k : Fin 8 ↦
          γ₀ (d8Wire 0 k))) / 4 +
         (bitsVal (fun k : Fin 8 ↦ γ₀ (d8Wire 1 k)) * bitsVal (fun k : Fin 8 ↦
           γ₀ (d8Wire 1 k))) / 4 +
         (bitsVal (fun k : Fin 8 ↦ γ₀ (d8Wire 2 k)) * bitsVal (fun k : Fin 8 ↦
           γ₀ (d8Wire 2 k))) / 4) % 65536 := by
  have hSplit : xorSqZ0Steps =
      z0SingleSteps 177 178 278 ++ (z0SingleSteps 184 185 279 ++ z0SingleSteps 191 192 280) := rfl
  let s1 := evalP57Steps (z0SingleSteps 177 178 278) γ₀
  have hs1 : s1 = Function.update γ₀ ⟨278, by decide⟩
      ((1 + γ₀ ⟨177, by decide⟩) * (1 + γ₀ ⟨178, by decide⟩)) :=
    z0SingleSteps_eval (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      γ₀ (hcl ⟨278, by decide⟩ (by decide))
  let s2 := evalP57Steps (z0SingleSteps 184 185 279) s1
  have hs1_279 : s1 ⟨279, by decide⟩ = 0 := by
    rw [hs1, Function.update_of_ne (by decide)]; exact hcl ⟨279, by decide⟩ (by decide)
  have hs2 : s2 = Function.update s1 ⟨279, by decide⟩
      ((1 + s1 ⟨184, by decide⟩) * (1 + s1 ⟨185, by decide⟩)) :=
    z0SingleSteps_eval (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      s1 hs1_279
  let s3 := evalP57Steps (z0SingleSteps 191 192 280) s2
  have hs2_280 : s2 ⟨280, by decide⟩ = 0 := by
    rw [hs2, Function.update_of_ne (by decide), hs1, Function.update_of_ne (by decide)]
    exact hcl ⟨280, by decide⟩ (by decide)
  have hs3 : s3 = Function.update s2 ⟨280, by decide⟩
      ((1 + s2 ⟨191, by decide⟩) * (1 + s2 ⟨192, by decide⟩)) :=
    z0SingleSteps_eval (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      s2 hs2_280
  have hAll : evalP57Steps xorSqZ0Steps γ₀ = s3 := by
    rw [hSplit, evalP57Steps_append, evalP57Steps_append]
  rw [hAll]
  have hs3_low : ∀ w : Wire 437, w.val < 278 → s3 w = γ₀ w := fun w hw ↦ by
    rw [hs3, Function.update_of_ne (wire_ne_of_lt (by dsimp; omega)),
      hs2, Function.update_of_ne (wire_ne_of_lt (by dsimp; omega)),
      hs1, Function.update_of_ne (wire_ne_of_lt (by dsimp; omega))]
  have hs3_cl : cleanRem 437 (437 - 281) s3 := fun w hw ↦ by
    rw [hs3, Function.update_of_ne (wire_ne_of_gt (by dsimp at hw ⊢; omega)),
      hs2, Function.update_of_ne (wire_ne_of_gt (by dsimp at hw ⊢; omega)),
      hs1, Function.update_of_ne (wire_ne_of_gt (by dsimp at hw ⊢; omega))]
    exact hcl w (by omega)
  have hv278 : rb437 278 s3 = (1 + γ₀ (d8Wire 0 0)) * (1 + γ₀ (d8Wire 0 1)) := by
    rw [rb437_lt _ (by decide), hs3, Function.update_of_ne (by decide),
      hs2, Function.update_of_ne (by decide), hs1, Function.update_self]
    rfl
  have hv279 : rb437 279 s3 = (1 + γ₀ (d8Wire 1 0)) * (1 + γ₀ (d8Wire 1 1)) := by
    rw [rb437_lt _ (by decide), hs3, Function.update_of_ne (by decide),
      hs2, Function.update_self, hs1,
      Function.update_of_ne (by decide), Function.update_of_ne (by decide)]
    rfl
  have hv280 : rb437 280 s3 = (1 + γ₀ (d8Wire 2 0)) * (1 + γ₀ (d8Wire 2 1)) := by
    rw [rb437_lt _ (by decide), hs3, Function.update_self,
      hs2, Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      hs1, Function.update_of_ne (by decide), Function.update_of_ne (by decide)]
    rfl
  refine ⟨hs3_cl, hs3_low, ?_⟩
  dsimp only [initMutsXorSq, initRosXorSq, mutListSum]
  simp only [Nat.pow_zero]
  rw [roListSum_append, roListSum_append, hv278, hv279, hv280]
  have hA0 := initRosAxis_sum_eq 0 γ₀
  have hA1 := initRosAxis_sum_eq 1 γ₀
  have hA2 := initRosAxis_sum_eq 2 γ₀
  change _ + roListSum initRosAxis0 γ₀ = _ at hA0
  change _ + roListSum initRosAxis1 γ₀ = _ at hA1
  change _ + roListSum initRosAxis2 γ₀ = _ at hA2
  have hTot : 49153 + (1 * ((1 + γ₀ (d8Wire 0 0)) * (1 + γ₀ (d8Wire 0 1))).val +
        (1 * ((1 + γ₀ (d8Wire 1 0)) * (1 + γ₀ (d8Wire 1 1))).val +
          (1 * ((1 + γ₀ (d8Wire 2 0)) * (1 + γ₀ (d8Wire 2 1))).val + 0))) +
      (roListSum initRosAxis0 γ₀ + roListSum initRosAxis1 γ₀ + roListSum initRosAxis2 γ₀) =
      ((bitsVal (fun k : Fin 8 ↦ γ₀ (d8Wire 0 k)) * bitsVal (fun k : Fin 8 ↦ γ₀ (d8Wire 0 k))) / 4 +
       (bitsVal (fun k : Fin 8 ↦ γ₀ (d8Wire 1 k)) * bitsVal (fun k : Fin 8 ↦ γ₀ (d8Wire 1 k))) / 4 +
       (bitsVal (fun k : Fin 8 ↦ γ₀ (d8Wire 2 k)) * bitsVal (fun k : Fin 8 ↦
         γ₀ (d8Wire 2 k))) / 4) +
      65536 * 1 := by omega
  rw [hTot, Nat.add_mul_mod_self_left]
theorem K_xorSq_spec (γ₀ : BitAssignment 437) (hcl : cleanRem 437 (437 - 278) γ₀) :
    cleanRem 437 (437 - 385) (K_xorSq.fwdBits γ₀) ∧
      (mutListSum finalMuts24 (K_xorSq.fwdBits γ₀)) % 65536 =
        ((bitsVal (fun k : Fin 8 ↦ γ₀ (d8Wire 0 k)) * bitsVal (fun k : Fin 8 ↦
          γ₀ (d8Wire 0 k))) / 4 +
         (bitsVal (fun k : Fin 8 ↦ γ₀ (d8Wire 1 k)) * bitsVal (fun k : Fin 8 ↦
           γ₀ (d8Wire 1 k))) / 4 +
         (bitsVal (fun k : Fin 8 ↦ γ₀ (d8Wire 2 k)) * bitsVal (fun k : Fin 8 ↦
           γ₀ (d8Wire 2 k))) / 4) % 65536 := by
  obtain ⟨hcl0, hLow0, hSum0⟩ := xorSqZ0Steps_spec γ₀ hcl
  have hRun : applyXorSqOps 281 49153 initMutsXorSq initRosXorSq xorSqOps105 =
      some (385, 0, finalMuts24, []) := rfl
  obtain ⟨hclF, _, hSumF⟩ := applyXorSqOps_sound xorSqOps105
    (by decide : 278 ≤ 281) (by decide : 281 ≤ 385)
    (by decide : wfMuts 281 initMutsXorSq = true)
    hRun
    γ₀ (evalP57Steps xorSqZ0Steps γ₀) hcl0 hLow0
  have hFwd : K_xorSq.fwdBits γ₀ =
      evalP57Steps (xorSqOps105.flatMap xorSqOpSteps) (evalP57Steps xorSqZ0Steps γ₀) := by
    dsimp only [K_xorSq, xorSqSteps]
    rw [buildP57Ctx_fwdBits, evalP57Steps_append]
  rw [hFwd]
  refine ⟨hclF, ?_⟩
  dsimp only [roListSum] at hSumF
  rw [zero_add, add_zero] at hSumF
  exact hSumF.trans hSum0
/-!
## Section 4: `16`-Bit Ripple Carry + `0-T` Modular Peel (`ph1Fwd16_388` / `dPh1Rev16_388`) & `<
388`-Wire `sTrue18`
-/
/-- Phase 1 column-`A` `16`-wire vector (`cols 2..17`, all `< 385`). -/
def ph1A16 : Fin 16 → Wire 388
  | ⟨0, _⟩ => ⟨278, by decide⟩
  | ⟨1, _⟩ => ⟨283, by decide⟩
  | ⟨2, _⟩ => ⟨288, by decide⟩
  | ⟨3, _⟩ => ⟨296, by decide⟩
  | ⟨4, _⟩ => ⟨304, by decide⟩
  | ⟨5, _⟩ => ⟨316, by decide⟩
  | ⟨6, _⟩ => ⟨320, by decide⟩
  | ⟨7, _⟩ => ⟨338, by decide⟩
  | ⟨8, _⟩ => ⟨341, by decide⟩
  | ⟨9, _⟩ => ⟨351, by decide⟩
  | ⟨10, _⟩ => ⟨366, by decide⟩
  | ⟨11, _⟩ => ⟨371, by decide⟩
  | ⟨12, _⟩ => ⟨375, by decide⟩
  | ⟨13, _⟩ => ⟨379, by decide⟩
  | ⟨14, _⟩ => ⟨382, by decide⟩
  | ⟨15, _⟩ => ⟨384, by decide⟩
  | ⟨_ + 16, h⟩ => absurd h (by omega)
/-- Phase 1 column-`B` `16`-wire vector (`cols 2..17`, reading clean zero wire `385` on 1-item
  cols). -/
def ph1B16 : Fin 16 → Wire 388
  | ⟨0, _⟩ => ⟨280, by decide⟩
  | ⟨1, _⟩ => ⟨385, by decide⟩
  | ⟨2, _⟩ => ⟨385, by decide⟩
  | ⟨3, _⟩ => ⟨385, by decide⟩
  | ⟨4, _⟩ => ⟨385, by decide⟩
  | ⟨5, _⟩ => ⟨385, by decide⟩
  | ⟨6, _⟩ => ⟨323, by decide⟩
  | ⟨7, _⟩ => ⟨385, by decide⟩
  | ⟨8, _⟩ => ⟨344, by decide⟩
  | ⟨9, _⟩ => ⟨354, by decide⟩
  | ⟨10, _⟩ => ⟨361, by decide⟩
  | ⟨11, _⟩ => ⟨368, by decide⟩
  | ⟨12, _⟩ => ⟨377, by decide⟩
  | ⟨13, _⟩ => ⟨380, by decide⟩
  | ⟨14, _⟩ => ⟨385, by decide⟩
  | ⟨15, _⟩ => ⟨385, by decide⟩
  | ⟨_ + 16, h⟩ => absurd h (by omega)
/-- Phase 1 `16`-bit destination slice `sTrue18W388[2..17]`. -/
def ph1Dst16_388 (k : Fin 16) : Wire 388 :=
  sTrue18W388 ⟨2 + k.val, by omega⟩
/-- Phase 1 carry-in wire `⟨385, _⟩` at `k = 0` and `ph1Dst16_388 k` at `k > 0`. -/
def ph1CarryW16 (k : Fin 16) : Wire 388 :=
  if k.val = 0 then ⟨385, by decide⟩ else ph1Dst16_388 k
theorem ph1Dst16_388_injective : Function.Injective ph1Dst16_388 := fun i j h ↦ by
  have hv := congrArg Fin.val (sTrue18W388_injective h)
  dsimp at hv
  exact Fin.ext (by omega)
theorem ph1A16_ne_ph1Dst16 (i j : Fin 16) : ph1A16 i ≠ ph1Dst16_388 j := by
  revert i j; decide
theorem ph1B16_ne_ph1Dst16 (i j : Fin 16) : ph1B16 i ≠ ph1Dst16_388 j := by
  revert i j; decide
theorem finalMuts24_eq_bitsVal (η : BitAssignment 388) (h385 : η ⟨385, by decide⟩ = 0) :
    mutListSum finalMuts24 (castAssign η) =
      bitsVal (fun k : Fin 16 ↦ η (ph1A16 k)) + bitsVal (fun k : Fin 16 ↦ η (ph1B16 k)) := by
  dsimp only [finalMuts24, mutListSum]
  repeat rw [rb437_lt _ (by decide)]
  repeat rw [castAssign_lt _ _ (by decide)]
  unfold bitsVal
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  dsimp only [ph1A16, ph1B16, Fin.succ, Fin.val_zero, Fin.val_succ]
  rw [h385]
  have hz : (0 : ZMod 2).val = 0 := rfl
  rw [hz]
  ring
theorem K_xorSq_388_spec (γ : BitAssignment 388) (hγ : cleanRem 388 (388 - 278) γ) :
    cleanRem 388 (388 - 385) (K_xorSq_388.fwdBits γ) ∧
      (K_xorSq_388.fwdBits γ) ⟨385, by decide⟩ = 0 ∧
      (bitsVal (fun k : Fin 16 ↦ (K_xorSq_388.fwdBits γ) (ph1A16 k)) +
        bitsVal (fun k : Fin 16 ↦ (K_xorSq_388.fwdBits γ) (ph1B16 k))) % 65536 =
        (dVal388 0 γ * dVal388 0 γ) / 4 + (dVal388 1 γ * dVal388 1 γ) / 4 +
          (dVal388 2 γ * dVal388 2 γ) / 4 := by
  have hclOut := K_xorSq_388_pkg.clean γ hγ
  have h385 : (K_xorSq_388.fwdBits γ) ⟨385, by decide⟩ = 0 :=
    hclOut ⟨385, by decide⟩ (by decide)
  have hcl437 : cleanRem 437 (437 - 278) (castAssign γ) :=
    (cleanRem_castAssign_iff (by decide : 388 ≤ 437) (437 - 278) γ).mp hγ
  obtain ⟨_, hSum⟩ := K_xorSq_spec (castAssign γ) hcl437
  have hFwd : K_xorSq.fwdBits (castAssign γ) = castAssign (K_xorSq_388.fwdBits γ) :=
    (truncateCtxB_fwdBits (by decide : 388 ≤ 437) K_xorSq K_xorSq_supportsBelow388 γ).symm
  rw [hFwd] at hSum
  have hdVal : ∀ w : Fin 3,
      bitsVal (fun k : Fin 8 ↦ castAssign γ (d8Wire w k)) = dVal388 w γ := fun w ↦ by
    unfold dVal388
    exact congrArg bitsVal (funext fun k ↦ castAssign_lt γ (d8Wire w k) (d8Wire_lt388 w k))
  rw [hdVal 0, hdVal 1, hdVal 2, finalMuts24_eq_bitsVal (K_xorSq_388.fwdBits γ) h385] at hSum
  have hb0 := dVal388_sq_div4_le 0 γ
  have hb1 := dVal388_sq_div4_le 1 γ
  have hb2 := dVal388_sq_div4_le 2 γ
  have hModLt : ((dVal388 0 γ * dVal388 0 γ) / 4 + (dVal388 1 γ * dVal388 1 γ) / 4 +
      (dVal388 2 γ * dVal388 2 γ) / 4) % 65536 =
      (dVal388 0 γ * dVal388 0 γ) / 4 + (dVal388 1 γ * dVal388 1 γ) / 4 +
      (dVal388 2 γ * dVal388 2 γ) / 4 :=
    Nat.mod_eq_of_lt (by omega)
  rw [hModLt] at hSum
  exact ⟨hclOut, h385, hSum⟩
/-- Phase 1 `32`-CNOT sum layer `ph1Dst16_388 ⊕= ph1A16 + ph1B16`. -/
def ph1XorCliff16 : CliffProg 388 :=
  .seq (cnotVec 16 ph1A16 ph1Dst16_388 (fun k ↦ ph1A16_ne_ph1Dst16 k k))
    (cnotVec 16 ph1B16 ph1Dst16_388 (fun k ↦ ph1B16_ne_ph1Dst16 k k))
theorem ph1XorCliff16_supportsBelow : ph1XorCliff16.SupportsBelow 386 :=
  ⟨cnotVec_supportsBelow 16 ph1A16 ph1Dst16_388 _
      (fun i ↦ by revert i; decide) (fun i ↦ by revert i; decide),
    cnotVec_supportsBelow 16 ph1B16 ph1Dst16_388 _
      (fun i ↦ by revert i; decide) (fun i ↦ by revert i; decide)⟩
theorem ph1XorCliff16_eval (δ : BitAssignment 388) :
    (∀ u : Wire 388, (∀ k : Fin 16, u ≠ ph1Dst16_388 k) → ph1XorCliff16.eval δ u = δ u) ∧
      (∀ k : Fin 16,
        ph1XorCliff16.eval δ (ph1Dst16_388 k) = δ (ph1Dst16_388 k) + δ (ph1A16 k) + δ (ph1B16 k)) :=
          by
  let δ1 := (cnotVec 16 ph1A16 ph1Dst16_388 (fun k ↦ ph1A16_ne_ph1Dst16 k k)).eval δ
  have hδ1_non : ∀ u : Wire 388, (∀ k : Fin 16, u ≠ ph1Dst16_388 k) → δ1 u = δ u := fun u hu ↦ by
    dsimp only [δ1]
    rw [cnotVec_eval 16 ph1A16 ph1Dst16_388 _ ph1Dst16_388_injective ph1A16_ne_ph1Dst16 δ u]
    have hnex : ¬ ∃ k : Fin 16, u = ph1Dst16_388 k := fun ⟨k, hk⟩ ↦ hu k hk
    simp [hnex]
  have hδ1_dst : ∀ k : Fin 16, δ1 (ph1Dst16_388 k) = δ (ph1Dst16_388 k) + δ (ph1A16 k) := fun k ↦ by
    dsimp only [δ1]
    rw [cnotVec_eval 16 ph1A16 ph1Dst16_388 _ ph1Dst16_388_injective ph1A16_ne_ph1Dst16 δ
      (ph1Dst16_388 k)]
    have hex : ∃ j : Fin 16, ph1Dst16_388 k = ph1Dst16_388 j := ⟨k, rfl⟩
    have hch : hex.choose = k := ph1Dst16_388_injective hex.choose_spec.symm
    simp [hex, hch]
  refine ⟨fun u hu ↦ ?_, fun k ↦ ?_⟩
  · dsimp only [ph1XorCliff16, CliffProg.eval]
    rw [cnotVec_eval 16 ph1B16 ph1Dst16_388 _ ph1Dst16_388_injective ph1B16_ne_ph1Dst16 δ1 u]
    have hnex : ¬ ∃ j : Fin 16, u = ph1Dst16_388 j := fun ⟨j, hj⟩ ↦ hu j hj
    simp only [hnex, ↓reduceDIte]
    exact hδ1_non u hu
  · dsimp only [ph1XorCliff16, CliffProg.eval]
    rw [cnotVec_eval 16 ph1B16 ph1Dst16_388 _ ph1Dst16_388_injective ph1B16_ne_ph1Dst16 δ1
      (ph1Dst16_388 k)]
    have hex : ∃ j : Fin 16, ph1Dst16_388 k = ph1Dst16_388 j := ⟨k, rfl⟩
    have hch : hex.choose = k := ph1Dst16_388_injective hex.choose_spec.symm
    simp only [hex, ↓reduceDIte, hch]
    rw [hδ1_dst k, hδ1_non (ph1B16 k) (fun j ↦ ph1B16_ne_ph1Dst16 k j)]
/-- Single ripple-majority step `ph1Dst16_388 i.succ ⊕= maj(ph1CarryW16 i, ph1A16 i, ph1B16 i)`
  using `386, 387`. -/
def ph1MajStep16 (i : Fin 15) : TempPhaseProg 388 :=
  apexMajAt 386 (by decide)
    (ph1CarryW16 i.castSucc) (ph1A16 i.castSucc) (ph1B16 i.castSucc) (ph1Dst16_388 i.succ)
    (by revert i; decide) (by revert i; decide) (by revert i; decide) (by revert i; decide)
    (by revert i; decide) (by revert i; decide) (by revert i; decide) (by revert i; decide)
/-- `0-T` dynamic uncomputer for `ph1MajStep16 i`. -/
def dPh1MajStep16 {Var : Type} {n : ℕ} (v : Var) (rComb : QRegister 388 n) (i : Fin 15) :
    DynamicCircuit Var n :=
  dApexMajAt v rComb
    (ph1CarryW16 i.castSucc) (ph1A16 i.castSucc) (ph1B16 i.castSucc) (ph1Dst16_388 i.succ)
    (by revert i; decide) (by revert i; decide) (by revert i; decide) (by revert i; decide)
theorem ph1MajStep16_spec (i : Fin 15) :
    ValidCleanRem 388 (388 - 386) (ph1MajStep16 i) ∧
      (ph1MajStep16 i).countTempAnd = 1 ∧
      (∀ r, ValidCleanRem 388 r (ph1MajStep16 i) → 388 - 386 ≤ r) ∧
      (∀ δ : BitAssignment 388, cleanRem 388 (388 - 386) δ → (ph1MajStep16 i).evalSign δ = 0) ∧
      (∀ δ : BitAssignment 388, cleanRem 388 (388 - 386) δ →
        cleanRem 388 (388 - 386) ((ph1MajStep16 i).evalBits δ) ∧
        (ph1MajStep16 i).evalBits δ =
          Function.update δ (ph1Dst16_388 i.succ)
            (δ (ph1Dst16_388 i.succ) +
              (δ (ph1CarryW16 i.castSucc) +
                (δ (ph1A16 i.castSucc) + δ (ph1CarryW16 i.castSucc)) *
                  (δ (ph1B16 i.castSucc) + δ (ph1CarryW16 i.castSucc))))) :=
  apexMajAt_spec 386 (by decide)
    (ph1CarryW16 i.castSucc) (ph1A16 i.castSucc) (ph1B16 i.castSucc) (ph1Dst16_388 i.succ)
    (by revert i; decide) (by revert i; decide) (by revert i; decide) (by revert i; decide)
    (by revert i; decide) (by revert i; decide)
    (by revert i; decide) (by revert i; decide) (by revert i; decide) (by revert i; decide)
/-- Forward `m`-step ripple-carry build loop (`m ≤ 15`). -/
def ph1BuildLoop16 : (m : ℕ) → m ≤ 15 → TempPhaseProg 388
  | 0, _ => .nil
  | m + 1, hm => .seq (ph1BuildLoop16 m (by omega)) (ph1MajStep16 ⟨m, hm⟩)
theorem ph1BuildLoop16_spec :
    ∀ (m : ℕ) (hm : m ≤ 15),
      ValidCleanRem 388 (388 - 386) (ph1BuildLoop16 m hm) ∧
        (ph1BuildLoop16 m hm).countTempAnd = m ∧
        (∀ δ : BitAssignment 388, cleanRem 388 (388 - 386) δ →
          (ph1BuildLoop16 m hm).evalSign δ = 0 ∧
          cleanRem 388 (388 - 386) ((ph1BuildLoop16 m hm).evalBits δ) ∧
          (∀ u : Wire 388, (∀ k : Fin 16, 1 ≤ k.val → k.val ≤ m → u ≠ ph1Dst16_388 k) →
            (ph1BuildLoop16 m hm).evalBits δ u = δ u) ∧
          (δ ⟨385, by decide⟩ = 0 →
            (∀ k : Fin 16, k.val ≤ m → δ (ph1Dst16_388 k) = 0) →
            ∀ k : Fin 16, k.val ≤ m →
              (ph1BuildLoop16 m hm).evalBits δ (ph1Dst16_388 k) =
                rippleCarry (fun j ↦ δ (ph1A16 j)) (fun j ↦ δ (ph1B16 j)) 0 k.castSucc))
  | 0, _ => by
      refine ⟨trivial, rfl, fun δ hδ ↦ ⟨rfl, hδ, fun _ _ ↦ rfl, fun _ h0 k hk ↦ ?_⟩⟩
      have hk0 : k = 0 := Fin.ext (by omega)
      subst hk0
      dsimp only [ph1BuildLoop16, TempPhaseProg.evalBits]
      have hc0 : (0 : Fin 16).castSucc = (0 : Fin 17) := rfl
      rw [h0 0 (by decide), hc0, rippleCarry_zero]
  | m + 1, hm => by
      obtain ⟨hv1, hc1, h1⟩ := ph1BuildLoop16_spec m (by omega)
      let im : Fin 15 := ⟨m, hm⟩
      obtain ⟨hv2, hc2, _, hs2, hb2⟩ := ph1MajStep16_spec im
      have hpres1 : ∀ δ : BitAssignment 388, cleanRem 388 (388 - 386) δ →
          cleanRem 388 (388 - 386) ((ph1BuildLoop16 m (by omega)).evalBits δ) :=
        fun δ hδ ↦ (h1 δ hδ).2.1
      refine ⟨⟨388 - 386, by decide, hv1, hv2, hpres1⟩,
        by dsimp [ph1BuildLoop16, TempPhaseProg.countTempAnd]; rw [hc1, hc2],
        fun δ hδ ↦ ?_⟩
      obtain ⟨hs1, hcl1, hnon1, hcar1⟩ := h1 δ hδ
      let δ₁ := (ph1BuildLoop16 m (by omega)).evalBits δ
      obtain ⟨hcl2, heq2⟩ := hb2 δ₁ hcl1
      refine ⟨by dsimp [ph1BuildLoop16, TempPhaseProg.evalSign]; rw [hs1, hs2 δ₁ hcl1]; rfl,
        hcl2, fun u hu ↦ ?_, fun h385 h0 k hk ↦ ?_⟩
      · dsimp only [ph1BuildLoop16, TempPhaseProg.evalBits]
        rw [heq2, Function.update_of_ne (hu im.succ (by dsimp [im]; omega) (by dsimp [im]; omega))]
        exact hnon1 u (fun k hk1 hkm ↦ hu k hk1 (by omega))
      · have hA_eq : ∀ j : Fin 16, δ₁ (ph1A16 j) = δ (ph1A16 j) :=
          fun j ↦ hnon1 (ph1A16 j) (fun k _ _ ↦ ph1A16_ne_ph1Dst16 j k)
        have hB_eq : ∀ j : Fin 16, δ₁ (ph1B16 j) = δ (ph1B16 j) :=
          fun j ↦ hnon1 (ph1B16 j) (fun k _ _ ↦ ph1B16_ne_ph1Dst16 j k)
        have hCar_im : δ₁ (ph1CarryW16 im.castSucc) =
            rippleCarry (fun j ↦ δ (ph1A16 j)) (fun j ↦ δ (ph1B16 j)) 0 (im.castSucc).castSucc := by
          by_cases hm0 : m = 0
          · have hcw : ph1CarryW16 im.castSucc = ⟨385, by decide⟩ := by simp [ph1CarryW16, im, hm0]
            have hcs0 : (im.castSucc).castSucc = (0 : Fin 17) := Fin.ext (by dsimp [im]; omega)
            have hlt385 : ∀ j' : Fin 16, (ph1Dst16_388 j').val < 385 := by decide
            dsimp only [δ₁]
            rw [hcw, hcs0, rippleCarry_zero,
              hnon1 ⟨385, by decide⟩ (fun j _ _ ↦ wire_ne_of_gt (hlt385 j)), h385]
          · have hcw : ph1CarryW16 im.castSucc = ph1Dst16_388 im.castSucc := by
              simp [ph1CarryW16, im, hm0]
            rw [hcw]
            exact hcar1 h385 (fun j hj ↦ h0 j (by omega)) im.castSucc (by dsimp [im]; omega)
        dsimp only [ph1BuildLoop16, TempPhaseProg.evalBits]
        rw [heq2]
        by_cases hkm : k = im.succ
        · subst hkm
          have hdst0 : δ₁ (ph1Dst16_388 im.succ) = 0 := by
            dsimp only [δ₁]
            rw [hnon1 (ph1Dst16_388 im.succ) (fun j _ hjm ↦ fun h ↦ by
              have := congrArg Fin.val (ph1Dst16_388_injective h); dsimp [im] at this; omega)]
            exact h0 im.succ (by dsimp [im]; omega)
          have hsucc_eq : (im.succ : Fin 16).castSucc = (im.castSucc : Fin 16).succ := Fin.ext rfl
          rw [Function.update_self, hdst0, zero_add, hCar_im, hA_eq, hB_eq, hsucc_eq,
            ← rippleCarry_step (fun j ↦ δ (ph1A16 j)) (fun j ↦ δ (ph1B16 j)) 0 im.castSucc]
        · rw [Function.update_of_ne (ph1Dst16_388_injective.ne hkm)]
          have hle_m : k.val ≤ m := by
            have hne_val : k.val ≠ m + 1 := fun hv ↦ hkm (Fin.ext hv)
            omega
          exact hcar1 h385 (fun j hj ↦ h0 j (by omega)) k hle_m
/-- Inner `15`-`TempAnd` forward Phase 1 body (`ph1BuildLoop16 15` followed by `ph1XorCliff16`). -/
def ph1InnerFwd16 : TempPhaseProg 388 :=
  .seq (ph1BuildLoop16 15 le_rfl) (.cliff ph1XorCliff16)
/-- `122`-`TempAnd` (`107 + 15`) Phase 1 forward (`sTrue18W388[2..17] ← (d_0^2 + d_1^2 + d_2^2) /
  4`). -/
def ph1Fwd16_388 : TempPhaseProg 388 :=
  K_xorSq_388.plug ph1InnerFwd16
theorem ph1Fwd16_388_spec :
    ValidCleanRem 388 (388 - 278) ph1Fwd16_388 ∧
      ph1Fwd16_388.countTempAnd = 122 ∧
      (∀ γ : BitAssignment 388, cleanRem 388 (388 - 278) γ → ph1Fwd16_388.evalSign γ = 0) ∧
      (∀ γ : BitAssignment 388, cleanRem 388 (388 - 278) γ →
        cleanRem 388 (388 - 278) (ph1Fwd16_388.evalBits γ) ∧
        (∀ w : Wire 388, (∀ k : Fin 16, w ≠ ph1Dst16_388 k) → ph1Fwd16_388.evalBits γ w = γ w) ∧
        ((∀ k : Fin 16, γ (ph1Dst16_388 k) = 0) →
          bitsVal (fun k : Fin 16 ↦ ph1Fwd16_388.evalBits γ (ph1Dst16_388 k)) =
            (dVal388 0 γ * dVal388 0 γ) / 4 + (dVal388 1 γ * dVal388 1 γ) / 4 +
              (dVal388 2 γ * dVal388 2 γ) / 4)) := by
  obtain ⟨hvL, hcL, hL⟩ := ph1BuildLoop16_spec 15 le_rfl
  have hvIn : ValidCleanRem 388 (388 - 386) ph1InnerFwd16 :=
    ⟨388 - 386, by decide, hvL, trivial, fun δ hδ ↦ (hL δ hδ).2.1⟩
  have hInNon : ∀ δ : BitAssignment 388, cleanRem 388 (388 - 386) δ →
      ∀ w : Wire 388, (∀ k : Fin 16, w ≠ ph1Dst16_388 k) → ph1InnerFwd16.evalBits δ w = δ w := by
    intro δ hδ w hw
    dsimp only [ph1InnerFwd16, TempPhaseProg.evalBits]
    rw [(ph1XorCliff16_eval _).1 w hw]
    exact (hL δ hδ).2.2.1 w (fun k _ _ ↦ hw k)
  have hInNonMut : ∀ δ : BitAssignment 388, cleanRem 388 (388 - 386) δ →
      ∀ w : Wire 388, ¬ mutSTrue388 w → ph1InnerFwd16.evalBits δ w = δ w :=
    fun δ hδ w hnw ↦ hInNon δ hδ w (fun k hk ↦ hnw ⟨⟨2 + k.val, by omega⟩, hk⟩)
  have hpkg := K_xorSq_388_pkg
  have hSupp386 : K_xorSq_388.SupportsBelowCtx 386 :=
    StepBBlock0.TempCtx.supportsBelowCtx_mono (by decide : 385 ≤ 386) hpkg.supp
  obtain ⟨hvP, hcP, hsP, hbP⟩ :=
    ScopedBlock.graft_mutating_clean (M := 388) (rem := 388 - 278) (curHole := 386)
      mutSTrue388 K_xorSq_388 hpkg.disj hSupp386 (by decide) K_xorSq_388.fwdBits hpkg.probe
      ph1InnerFwd16 hvIn hInNonMut
  have hDef : ph1Fwd16_388 = K_xorSq_388.plug ph1InnerFwd16 := rfl
  have hInDef : ph1InnerFwd16 = .seq (ph1BuildLoop16 15 le_rfl) (.cliff ph1XorCliff16) := rfl
  have hCnt : ph1Fwd16_388.countTempAnd = 122 := by
    rw [hDef, hcP, hpkg.cnt_eq, hInDef]
    dsimp only [TempPhaseProg.countTempAnd]
    rw [hcL]
  refine ⟨hvP, hCnt, fun γ hγ ↦ ?_, fun γ hγ ↦ ?_⟩
  · have hcl386 : cleanRem 388 (388 - 386) (K_xorSq_388.fwdBits γ) :=
      cleanRem_anti (by decide) (hpkg.clean γ hγ)
    rw [hDef, hsP γ hγ, hInDef, evalSign_seq, (hL _ hcl386).1]; rfl
  · obtain ⟨hcl385, h385, hAB⟩ := K_xorSq_388_spec γ hγ
    have hcl386 : cleanRem 388 (388 - 386) (K_xorSq_388.fwdBits γ) := cleanRem_anti (by
      decide) hcl385
    have hNon : ∀ w : Wire 388, (∀ k : Fin 16, w ≠ ph1Dst16_388 k) →
        ph1Fwd16_388.evalBits γ w = γ w := fun w hw ↦ by
      rw [hDef, hbP γ hγ w]
      by_cases hm : mutSTrue388 w
      · simp only [hm, ↓reduceIte]
        exact (hInNon _ hcl386 w hw).trans (TempCtx.fwdBits_mut hpkg.disj γ hm)
      · simp only [hm, ↓reduceIte]
    refine ⟨fun w hw ↦ by
      rw [hNon w (fun k ↦ wire_ne_of_gt
        (lt_of_lt_of_le (by revert k; decide : (ph1Dst16_388 k).val < 278) (by omega)))]
      exact hγ w hw,
      hNon, fun hZero ↦ ?_⟩
    let δ := K_xorSq_388.fwdBits γ
    have hZδ : ∀ k : Fin 16, δ (ph1Dst16_388 k) = 0 := fun k ↦
      (TempCtx.fwdBits_mut hpkg.disj γ ⟨⟨2 + k.val, by omega⟩, rfl⟩).trans (hZero k)
    obtain ⟨_, _, hL_non, hL_car⟩ := hL δ hcl386
    let δ₁ := (ph1BuildLoop16 15 le_rfl).evalBits δ
    have hA_δ₁ : ∀ k : Fin 16, δ₁ (ph1A16 k) = δ (ph1A16 k) :=
      fun k ↦ hL_non (ph1A16 k) (fun j _ _ ↦ ph1A16_ne_ph1Dst16 k j)
    have hB_δ₁ : ∀ k : Fin 16, δ₁ (ph1B16 k) = δ (ph1B16 k) :=
      fun k ↦ hL_non (ph1B16 k) (fun j _ _ ↦ ph1B16_ne_ph1Dst16 k j)
    have hCar_δ₁ : ∀ k : Fin 16, δ₁ (ph1Dst16_388 k) =
        rippleCarry (fun j ↦ δ (ph1A16 j)) (fun j ↦ δ (ph1B16 j)) 0 k.castSucc :=
      fun k ↦ hL_car h385 (fun j _ ↦ hZδ j) k (by omega)
    have hFnEq : (fun k : Fin 16 ↦ ph1Fwd16_388.evalBits γ (ph1Dst16_388 k)) =
        fun k : Fin 16 ↦ δ (ph1A16 k) + δ (ph1B16 k) +
          rippleCarry (fun j ↦ δ (ph1A16 j)) (fun j ↦ δ (ph1B16 j)) 0 k.castSucc := by
      funext k
      have hm : mutSTrue388 (ph1Dst16_388 k) := ⟨⟨2 + k.val, by omega⟩, rfl⟩
      rw [hDef, hbP γ hγ (ph1Dst16_388 k), ite_eq_left hm, hInDef, evalBits_seq]
      change ph1XorCliff16.eval δ₁ (ph1Dst16_388 k) = _
      rw [(ph1XorCliff16_eval δ₁).2 k, hA_δ₁ k, hB_δ₁ k, hCar_δ₁ k]
      abel
    rw [hFnEq]
    have hrc := rippleCarry_bitsVal (fun j ↦ δ (ph1A16 j)) (fun j ↦ δ (ph1B16 j)) 0
    have hz : (0 : ZMod 2).val = 0 := rfl
    rw [hz, add_zero] at hrc
    have hltS : bitsVal (fun k : Fin 16 ↦ δ (ph1A16 k) + δ (ph1B16 k) +
        rippleCarry (fun j ↦ δ (ph1A16 j)) (fun j ↦ δ (ph1B16 j)) 0 k.castSucc) < 65536 :=
      bitsVal_lt_two_pow _
    have hModS : (bitsVal (fun k : Fin 16 ↦ δ (ph1A16 k)) +
        bitsVal (fun k : Fin 16 ↦ δ (ph1B16 k))) % 65536 =
        bitsVal (fun k : Fin 16 ↦ δ (ph1A16 k) + δ (ph1B16 k) +
          rippleCarry (fun j ↦ δ (ph1A16 j)) (fun j ↦ δ (ph1B16 j)) 0 k.castSucc) := by
      have hp16 : (2 : ℕ) ^ 16 = 65536 := by decide
      rw [← hrc, hp16, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hltS]
    exact hModS.symm.trans hAB
/-- Reverse `m`-step static ripple-carry peel loop (`m ≤ 15`). -/
def ph1PeelLoopStatic16 : (m : ℕ) → m ≤ 15 → TempPhaseProg 388
  | 0, _ => .nil
  | m + 1, hm => .seq (ph1MajStep16 ⟨m, hm⟩) (ph1PeelLoopStatic16 m (by omega))
/-- `0-T` dynamic ripple-carry peel loop realizing `ph1PeelLoopStatic16 m hm`. -/
def dPh1PeelLoop16 {Var : Type} {n : ℕ} (v : Var) (rComb : QRegister 388 n) :
    (m : ℕ) → m ≤ 15 → DynamicCircuit Var n
  | 0, _ => .circuit .identity
  | m + 1, hm => .seq (dPh1MajStep16 v rComb ⟨m, hm⟩) (dPh1PeelLoop16 v rComb m (by omega))
/-- Intermediate `16`-bit ripple-peel invariant after clearing `ph1Dst16_388` above index `m`. -/
def InvPeel16 (m : ℕ) (η : BitAssignment 388) : Prop :=
  η ⟨385, by decide⟩ = 0 ∧
    ∀ k : Fin 16,
      η (ph1Dst16_388 k) =
        if k.val ≤ m then
          rippleCarry (fun j ↦ η (ph1A16 j)) (fun j ↦ η (ph1B16 j)) 0 k.castSucc
        else 0
theorem dPh1PeelLoop16_count_t {Var : Type} {n : ℕ} (v : Var) (rComb : QRegister 388 n) :
    ∀ (m : ℕ) (hm : m ≤ 15), (dPh1PeelLoop16 v rComb m hm).count T = 0
  | 0, _ => by simp [dPh1PeelLoop16]
  | m + 1, hm => by
      dsimp only [dPh1PeelLoop16, dPh1MajStep16]
      simp [DynamicCircuit.count, dApexMajAt_count_t, dPh1PeelLoop16_count_t v rComb m]
theorem dPh1PeelLoop16_count_toff {Var : Type} {n : ℕ} (v : Var) (rComb : QRegister 388 n) :
    ∀ (m : ℕ) (hm : m ≤ 15), (dPh1PeelLoop16 v rComb m hm).count TOFF = 0
  | 0, _ => by simp [dPh1PeelLoop16]
  | m + 1, hm => by
      dsimp only [dPh1PeelLoop16, dPh1MajStep16]
      simp [DynamicCircuit.count, dApexMajAt_count_toff, dPh1PeelLoop16_count_toff v rComb m]
theorem dPh1PeelLoop16_preservesStore {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    (v : Var) (rComb : QRegister 388 n) :
    ∀ (m : ℕ) (hm : m ≤ 15), PreservesStoreConst (dPh1PeelLoop16 v rComb m hm)
  | 0, _ => PreservesStoreConst.circuit .identity
  | m + 1, hm =>
      PreservesStoreConst.seq (dApexMajAt_preservesStore v rComb _ _ _ _ _ _ _ _)
        (dPh1PeelLoop16_preservesStore v rComb m (by omega))
theorem invPeel16_step {m : ℕ} (hm : m + 1 ≤ 15) {η : BitAssignment 388}
    (hcl : cleanRem 388 (388 - 386) η) (hInv : InvPeel16 (m + 1) η) :
    (η (ph1Dst16_388 (⟨m, hm⟩ : Fin 15).succ) =
      η (ph1CarryW16 (⟨m, hm⟩ : Fin 15).castSucc) +
        (η (ph1A16 (⟨m, hm⟩ : Fin 15).castSucc) + η (ph1CarryW16 (⟨m, hm⟩ : Fin 15).castSucc)) *
          (η (ph1B16 (⟨m, hm⟩ : Fin 15).castSucc) + η (ph1CarryW16 (⟨m, hm⟩ : Fin 15).castSucc))) ∧
      cleanRem 388 (388 - 386) ((ph1MajStep16 ⟨m, hm⟩).evalBits η) ∧
      InvPeel16 m ((ph1MajStep16 ⟨m, hm⟩).evalBits η) := by
  let im : Fin 15 := ⟨m, hm⟩
  obtain ⟨h385, hDst⟩ := hInv
  obtain ⟨_, _, _, _, hbM⟩ := ph1MajStep16_spec im
  obtain ⟨hcl', heq'⟩ := hbM η hcl
  have hCar : η (ph1CarryW16 im.castSucc) =
      rippleCarry (fun j ↦ η (ph1A16 j)) (fun j ↦ η (ph1B16 j)) 0 (im.castSucc).castSucc := by
    by_cases hm0 : m = 0
    · have hcw : ph1CarryW16 im.castSucc = ⟨385, by decide⟩ := by simp [ph1CarryW16, im, hm0]
      have hcs0 : (im.castSucc).castSucc = (0 : Fin 17) := Fin.ext (by dsimp [im]; omega)
      rw [hcw, hcs0, rippleCarry_zero, h385]
    · have hcw : ph1CarryW16 im.castSucc = ph1Dst16_388 im.castSucc := by
        simp [ph1CarryW16, im, hm0]
      rw [hcw, hDst im.castSucc, ite_eq_left (by dsimp [im]; omega)]
  have hMajEq : η (ph1Dst16_388 im.succ) =
      η (ph1CarryW16 im.castSucc) +
        (η (ph1A16 im.castSucc) + η (ph1CarryW16 im.castSucc)) *
          (η (ph1B16 im.castSucc) + η (ph1CarryW16 im.castSucc)) := by
    have hsucc_eq : (im.succ : Fin 16).castSucc = (im.castSucc : Fin 16).succ := Fin.ext rfl
    rw [hDst im.succ, ite_eq_left (by dsimp [im]; omega), hsucc_eq, rippleCarry_step, ← hCar]
  refine ⟨hMajEq, hcl', ?_, fun k ↦ ?_⟩
  · rw [heq', Function.update_of_ne (wire_ne_of_gt
      (((show ∀ i : Fin 15, (ph1Dst16_388 i.succ).val < 385 by decide) im)))]
    exact h385
  · have hA_eq : (fun j ↦ ((ph1MajStep16 im).evalBits η) (ph1A16 j)) = fun j ↦ η (ph1A16 j) := by
      funext j; rw [heq', Function.update_of_ne (ph1A16_ne_ph1Dst16 j im.succ)]
    have hB_eq : (fun j ↦ ((ph1MajStep16 im).evalBits η) (ph1B16 j)) = fun j ↦ η (ph1B16 j) := by
      funext j; rw [heq', Function.update_of_ne (ph1B16_ne_ph1Dst16 j im.succ)]
    rw [hA_eq, hB_eq, heq']
    by_cases hkm : k = im.succ
    · subst hkm
      rw [Function.update_self, hMajEq, CharTwo.add_self_eq_zero, ite_eq_right (by
        dsimp [im]; omega)]
    · rw [Function.update_of_ne (ph1Dst16_388_injective.ne hkm), hDst k]
      have hne_val : k.val ≠ m + 1 := fun hv ↦ hkm (Fin.ext hv)
      by_cases hle : k.val ≤ m
      · rw [ite_eq_left hle, ite_eq_left (by omega)]
      · rw [ite_eq_right hle, ite_eq_right (by omega)]
theorem ph1PeelLoopStatic16_spec :
    ∀ (m : ℕ) (hm : m ≤ 15),
      ValidCleanRem 388 (388 - 386) (ph1PeelLoopStatic16 m hm) ∧
        (∀ η : BitAssignment 388, cleanRem 388 (388 - 386) η →
          (ph1PeelLoopStatic16 m hm).evalSign η = 0 ∧
          cleanRem 388 (388 - 386) ((ph1PeelLoopStatic16 m hm).evalBits η) ∧
          (∀ u : Wire 388, (∀ k : Fin 16, u ≠ ph1Dst16_388 k) →
            (ph1PeelLoopStatic16 m hm).evalBits η u = η u) ∧
          (InvPeel16 m η → ∀ k : Fin 16,
            (ph1PeelLoopStatic16 m hm).evalBits η (ph1Dst16_388 k) = 0))
  | 0, _ => by
      refine ⟨trivial, fun η hη ↦ ⟨rfl, hη, fun _ _ ↦ rfl, fun ⟨_, hDst⟩ k ↦ ?_⟩⟩
      dsimp only [ph1PeelLoopStatic16, TempPhaseProg.evalBits]
      rw [hDst k]
      by_cases hk0 : k.val ≤ 0
      · have hk_eq : k.castSucc = (0 : Fin 17) := Fin.ext (by simp; omega)
        rw [ite_eq_left hk0, hk_eq, rippleCarry_zero]
      · rw [ite_eq_right hk0]
  | m + 1, hm => by
      let im : Fin 15 := ⟨m, hm⟩
      obtain ⟨hv1, _, _, hs1, hb1⟩ := ph1MajStep16_spec im
      obtain ⟨hv2, h2⟩ := ph1PeelLoopStatic16_spec m (by omega)
      refine ⟨⟨388 - 386, by decide, hv1, hv2, fun η hη ↦ (hb1 η hη).1⟩, fun η hη ↦ ?_⟩
      obtain ⟨hcl1, heq1⟩ := hb1 η hη
      obtain ⟨hs2, hcl2, hnon2, hzero2⟩ := h2 _ hcl1
      refine ⟨by dsimp [ph1PeelLoopStatic16, TempPhaseProg.evalSign]; rw [hs1 η hη, hs2]; rfl,
        hcl2, fun u hu ↦ ?_, fun hInv k ↦ ?_⟩
      · dsimp only [ph1PeelLoopStatic16, TempPhaseProg.evalBits]
        rw [hnon2 u hu, heq1, Function.update_of_ne (hu im.succ)]
      · dsimp only [ph1PeelLoopStatic16, TempPhaseProg.evalBits]
        exact hzero2 (invPeel16_step hm hη hInv).2.2 k
theorem dPh1MajStep16_realizes
    {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)]
    (v : Var) (rComb : QRegister 388 n) (i : Fin 15)
    (Inv : BitAssignment 388 → Prop)
    (hInv : ∀ η : BitAssignment 388, cleanRem 388 (388 - 386) η → Inv η →
      η (ph1Dst16_388 i.succ) =
        η (ph1CarryW16 i.castSucc) +
          (η (ph1A16 i.castSucc) + η (ph1CarryW16 i.castSucc)) *
            (η (ph1B16 i.castSucc) + η (ph1CarryW16 i.castSucc))) :
    RealizesCleanUnitary v (p57CleanDiagProj rComb (388 - 386) (by decide) Inv)
      (dPh1MajStep16 v rComb i)
      ((((ph1MajStep16 i).onRegister rComb).toToffCircuit).eval) :=
  dApexMajAt_realizes v rComb 386 (by decide)
    (ph1CarryW16 i.castSucc) (ph1A16 i.castSucc) (ph1B16 i.castSucc) (ph1Dst16_388 i.succ)
    (by clear hInv; revert i; decide) (by clear hInv; revert i; decide)
    (by clear hInv; revert i; decide) (by clear hInv; revert i; decide)
    (by clear hInv; revert i; decide) (by clear hInv; revert i; decide)
    (by clear hInv; revert i; decide) (by clear hInv; revert i; decide)
    (by clear hInv; revert i; decide) (by clear hInv; revert i; decide)
    Inv hInv
theorem dPh1PeelLoop16_realizes
    {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)]
    (v : Var) (rComb : QRegister 388 n) :
    ∀ (m : ℕ) (hm : m ≤ 15) (Inv : BitAssignment 388 → Prop),
      (∀ η : BitAssignment 388, cleanRem 388 (388 - 386) η → Inv η → InvPeel16 m η) →
      RealizesCleanUnitary v (p57CleanDiagProj rComb (388 - 386) (by decide) Inv)
        (dPh1PeelLoop16 v rComb m hm)
        ((((ph1PeelLoopStatic16 m hm).onRegister rComb).toToffCircuit).eval)
  | 0, _, Inv, _ =>
      RealizesCleanUnitary.circuit v
        (p57CleanDiagProj rComb (388 - 386) (by decide) Inv) .identity
  | m + 1, hm, Inv, hInv => by
      dsimp only [dPh1PeelLoop16, ph1PeelLoopStatic16]
      let im : Fin 15 := ⟨m, hm⟩
      have hStep1 := dPh1MajStep16_realizes v rComb im Inv
        (fun η hcl hi ↦ (invPeel16_step hm hcl (hInv η hcl hi)).1)
      have hStep2 := dPh1PeelLoop16_realizes v rComb m (by omega) (InvPeel16 m) (fun _ _ hi ↦ hi)
      have hPres := p57SeqClean_prog_inv rComb (ph1MajStep16 im) (by decide) (by decide)
        (fun η hcl hi ↦ (invPeel16_step hm hcl (hInv η hcl hi)).2)
      have hSeq := RealizesCleanUnitary_seq_asym
        (p57CleanDiagProj_conjTranspose rComb (388 - 386) (by decide) Inv)
        (p57CleanDiagProj_conjTranspose rComb (388 - 386) (by decide) (InvPeel16 m))
        hStep1 hStep2 hPres
      have hMul : (((ph1PeelLoopStatic16 m (by omega)).onRegister rComb).toToffCircuit).eval *
          (((ph1MajStep16 im).onRegister rComb).toToffCircuit).eval =
          ((((TempPhaseProg.seq (ph1MajStep16 im)
            (ph1PeelLoopStatic16 m (by omega))).onRegister rComb).toToffCircuit).eval) := by
        simp [TempPhaseProg.onRegister, TempPhaseProg.toToffCircuit, Circuit.eval_seq]
      rwa [hMul] at hSeq
/-- Inner `15`-`TempAnd` static reverse Phase 1 body (`ph1XorCliff16` then `ph1PeelLoopStatic16
  15`). -/
def ph1InnerRevStatic16 : TempPhaseProg 388 :=
  .seq (.cliff ph1XorCliff16) (ph1PeelLoopStatic16 15 le_rfl)
/-- `0-T` dynamic inner reverse Phase 1 body (`0 T`, `0` Toffoli). -/
def dPh1InnerRev16 {Var : Type} {n : ℕ} (v : Var) (rComb : QRegister 388 n) :
    DynamicCircuit Var n :=
  .seq (.circuit ((ph1XorCliff16.onRegister rComb).toCircuit))
    (dPh1PeelLoop16 v rComb 15 le_rfl)
/-- `122`-`TempAnd` static Phase 1 reverse circuit. -/
def ph1RevStatic16_388 : TempPhaseProg 388 :=
  K_xorSq_388.plug ph1InnerRevStatic16
/-- `428 T` (`107`-`TempAnd`, `0` Toffoli) dynamic Phase 1 reverse circuit. -/
def dPh1Rev16_388 {Var : Type} {n : ℕ} (v : Var) (rComb : QRegister 388 n) :
    DynamicCircuit Var n :=
  p57ToDynWith v rComb (dPh1InnerRev16 v rComb) K_xorSq_388
/-- `.hole` invariant for modular `16`-bit Phase 1 reverse. -/
def InvPh1Hole16 (δ : BitAssignment 388) : Prop :=
  δ ⟨385, by decide⟩ = 0 ∧
    bitsVal (fun k : Fin 16 ↦ δ (ph1Dst16_388 k)) =
      (bitsVal (fun k : Fin 16 ↦ δ (ph1A16 k)) +
        bitsVal (fun k : Fin 16 ↦ δ (ph1B16 k))) % 65536
/-- Phase 1 reverse precondition: `ph1Dst16_388` holds `(d_0^2)/4 + (d_1^2)/4 + (d_2^2)/4`. -/
def InvPh1Rev16 (γ : BitAssignment 388) : Prop :=
  bitsVal (fun k : Fin 16 ↦ γ (ph1Dst16_388 k)) =
    (dVal388 0 γ * dVal388 0 γ) / 4 + (dVal388 1 γ * dVal388 1 γ) / 4 +
      (dVal388 2 γ * dVal388 2 γ) / 4
theorem ph1InnerRevStatic16_valid_le (r : ℕ) (hr : ValidCleanRem 388 r ph1InnerRevStatic16) :
    388 - 386 ≤ r := by
  have hUnf : ph1InnerRevStatic16 =
      .seq (.cliff ph1XorCliff16)
        (.seq (ph1MajStep16 ⟨14, by decide⟩) (ph1PeelLoopStatic16 14 (by decide))) := rfl
  rw [hUnf] at hr
  refine validCleanRem_cliff_seq_le (by decide : 386 < 388) _ ph1XorCliff16_supportsBelow
    (fun r' hr' ↦ ?_) hr
  obtain ⟨_, _, hv1, _, _⟩ := hr'
  exact (ph1MajStep16_spec ⟨14, by decide⟩).2.2.1 r' hv1
theorem invPh1Hole16_to_invPeel15 {δ : BitAssignment 388} (hHole : InvPh1Hole16 δ) :
    InvPeel16 15 (ph1XorCliff16.eval δ) := by
  obtain ⟨h385, hSum⟩ := hHole
  obtain ⟨hNonX, hDstX⟩ := ph1XorCliff16_eval δ
  have hrc := rippleCarry_bitsVal (fun j ↦ δ (ph1A16 j)) (fun j ↦ δ (ph1B16 j)) 0
  have hz : (0 : ZMod 2).val = 0 := rfl
  rw [hz, add_zero] at hrc
  have hltS : bitsVal (fun k : Fin 16 ↦ δ (ph1A16 k) + δ (ph1B16 k) +
      rippleCarry (fun j ↦ δ (ph1A16 j)) (fun j ↦ δ (ph1B16 j)) 0 k.castSucc) < 65536 :=
    bitsVal_lt_two_pow _
  have hEqVal : bitsVal (fun k : Fin 16 ↦ δ (ph1Dst16_388 k)) =
      bitsVal (fun k : Fin 16 ↦ δ (ph1A16 k) + δ (ph1B16 k) +
        rippleCarry (fun j ↦ δ (ph1A16 j)) (fun j ↦ δ (ph1B16 j)) 0 k.castSucc) := by
    have hp16 : (2 : ℕ) ^ 16 = 65536 := by decide
    rw [hSum, ← hrc, hp16, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hltS]
  have hBitEq := Slot3MicroEngineAux.bitsVal_injective hEqVal
  have hcancel : ∀ x y z : ZMod 2, x + y + z + x + y = z := by decide
  refine ⟨(hNonX ⟨385, by decide⟩ (fun k ↦ wire_ne_of_gt (by revert k; decide))).trans h385,
    fun k ↦ ?_⟩
  have hA_eq : (fun j ↦ ph1XorCliff16.eval δ (ph1A16 j)) = fun j ↦ δ (ph1A16 j) :=
    funext fun j ↦ hNonX (ph1A16 j) (fun i ↦ ph1A16_ne_ph1Dst16 j i)
  have hB_eq : (fun j ↦ ph1XorCliff16.eval δ (ph1B16 j)) = fun j ↦ δ (ph1B16 j) :=
    funext fun j ↦ hNonX (ph1B16 j) (fun i ↦ ph1B16_ne_ph1Dst16 j i)
  rw [hA_eq, hB_eq, ite_eq_left (by omega : k.val ≤ 15), hDstX k, congrFun hBitEq k, hcancel]
theorem dPh1Rev16_388_count_t {Var : Type} {n : ℕ} (v : Var) (rComb : QRegister 388 n) :
    (dPh1Rev16_388 v rComb).count T = 428 := by
  dsimp only [dPh1Rev16_388, dPh1InnerRev16]
  rw [p57ToDynWith_count_t, K_xorSq_388_pkg.cnt_eq]
  simp [DynamicCircuit.count, dPh1PeelLoop16_count_t]
theorem dPh1Rev16_388_count_toff {Var : Type} {n : ℕ} (v : Var) (rComb : QRegister 388 n) :
    (dPh1Rev16_388 v rComb).count TOFF = 0 := by
  refine p57ToDynWith_count_toff v rComb _ ?_ K_xorSq_388
  dsimp only [dPh1InnerRev16]
  simp [DynamicCircuit.count, dPh1PeelLoop16_count_toff]
theorem dPh1Rev16_388_preservesStore {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    (v : Var) (rComb : QRegister 388 n) :
    PreservesStoreConst (dPh1Rev16_388 v rComb) :=
  p57ToDynWith_preservesStore v rComb _
    (PreservesStoreConst.seq (PreservesStoreConst.circuit _)
      (dPh1PeelLoop16_preservesStore v rComb 15 le_rfl))
    K_xorSq_388
theorem ph1RevStatic16_388_spec :
    ValidCleanRem 388 (388 - 278) ph1RevStatic16_388 ∧
      (∀ γ : BitAssignment 388, cleanRem 388 (388 - 278) γ →
        ph1RevStatic16_388.evalSign γ = 0 ∧
        cleanRem 388 (388 - 278) (ph1RevStatic16_388.evalBits γ) ∧
        (∀ w : Wire 388, (∀ k : Fin 16, w ≠ ph1Dst16_388 k) →
          ph1RevStatic16_388.evalBits γ w = γ w) ∧
        (InvPh1Rev16 γ → ∀ k : Fin 16, ph1RevStatic16_388.evalBits γ (ph1Dst16_388 k) = 0)) := by
  obtain ⟨hvP, hP⟩ := ph1PeelLoopStatic16_spec 15 le_rfl
  have hclX : ∀ δ : BitAssignment 388, cleanRem 388 (388 - 386) δ →
      cleanRem 388 (388 - 386) (ph1XorCliff16.eval δ) := fun δ hδ w hw ↦ by
    rw [ph1XorCliff16.eval_outside ph1XorCliff16_supportsBelow δ w (by omega)]
    exact hδ w hw
  have hvIn : ValidCleanRem 388 (388 - 386) ph1InnerRevStatic16 :=
    ⟨388 - 386, by decide, trivial, hvP, hclX⟩
  have hInNon : ∀ δ : BitAssignment 388, cleanRem 388 (388 - 386) δ →
      ∀ w : Wire 388, (∀ k : Fin 16, w ≠ ph1Dst16_388 k) → ph1InnerRevStatic16.evalBits δ w = δ w :=
        by
    intro δ hδ w hw
    dsimp only [ph1InnerRevStatic16, TempPhaseProg.evalBits]
    rw [(hP _ (hclX δ hδ)).2.2.1 w hw, (ph1XorCliff16_eval δ).1 w hw]
  have hpkg := K_xorSq_388_pkg
  have hSupp386 : K_xorSq_388.SupportsBelowCtx 386 :=
    StepBBlock0.TempCtx.supportsBelowCtx_mono (by decide : 385 ≤ 386) hpkg.supp
  obtain ⟨hvPlug, _, hsPlug, hbPlug⟩ :=
    ScopedBlock.graft_mutating_clean (M := 388) (rem := 388 - 278) (curHole := 386)
      mutSTrue388 K_xorSq_388 hpkg.disj hSupp386 (by decide) K_xorSq_388.fwdBits hpkg.probe
      ph1InnerRevStatic16 hvIn
      (fun δ hδ w hnw ↦ hInNon δ hδ w (fun k hk ↦ hnw ⟨⟨2 + k.val, by omega⟩, hk⟩))
  have hDef : ph1RevStatic16_388 = K_xorSq_388.plug ph1InnerRevStatic16 := rfl
  have hInDef : ph1InnerRevStatic16 = .seq (.cliff ph1XorCliff16) (ph1PeelLoopStatic16 15 le_rfl) :=
    rfl
  refine ⟨hvPlug, fun γ hγ ↦ ?_⟩
  obtain ⟨hcl385, h385, hAB⟩ := K_xorSq_388_spec γ hγ
  have hcl386 : cleanRem 388 (388 - 386) (K_xorSq_388.fwdBits γ) := cleanRem_anti (by decide) hcl385
  have hNon : ∀ w : Wire 388, (∀ k : Fin 16, w ≠ ph1Dst16_388 k) →
      ph1RevStatic16_388.evalBits γ w = γ w := fun w hw ↦ by
    rw [hDef, hbPlug γ hγ w]
    by_cases hm : mutSTrue388 w
    · simp only [hm, ↓reduceIte]
      exact (hInNon _ hcl386 w hw).trans (TempCtx.fwdBits_mut hpkg.disj γ hm)
    · simp only [hm, ↓reduceIte]
  refine ⟨by
    rw [hDef, hsPlug γ hγ, hInDef, evalSign_seq]
    rw [show (TempPhaseProg.cliff ph1XorCliff16).evalBits (K_xorSq_388.fwdBits γ) =
      ph1XorCliff16.eval (K_xorSq_388.fwdBits γ) from rfl, (hP _ (hclX _ hcl386)).1]; rfl,
    fun w hw ↦ by
      rw [hNon w (fun k ↦ wire_ne_of_gt
        (lt_of_lt_of_le (by revert k; decide : (ph1Dst16_388 k).val < 278) (by omega)))]
      exact hγ w hw,
    hNon, fun hInv k ↦ ?_⟩
  have hm : mutSTrue388 (ph1Dst16_388 k) := ⟨⟨2 + k.val, by omega⟩, rfl⟩
  rw [hDef, hbPlug γ hγ (ph1Dst16_388 k), ite_eq_left hm, hInDef, evalBits_seq,
    show (TempPhaseProg.cliff ph1XorCliff16).evalBits (K_xorSq_388.fwdBits γ) =
      ph1XorCliff16.eval (K_xorSq_388.fwdBits γ) from rfl]
  have hMutDst : (fun j : Fin 16 ↦ (K_xorSq_388.fwdBits γ) (ph1Dst16_388 j)) =
      fun j ↦ γ (ph1Dst16_388 j) :=
    funext fun j ↦ TempCtx.fwdBits_mut hpkg.disj γ ⟨⟨2 + j.val, by omega⟩, rfl⟩
  have hHole : InvPh1Hole16 (K_xorSq_388.fwdBits γ) :=
    ⟨h385, by rw [hMutDst, hInv, ← hAB]⟩
  exact (hP _ (hclX _ hcl386)).2.2.2 (invPh1Hole16_to_invPeel15 hHole) k
theorem dPh1Rev16_388_realizes
    {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)]
    (v : Var) (rComb : QRegister 388 n)
    (Inv : BitAssignment 388 → Prop)
    (hInv : ∀ γ : BitAssignment 388, cleanRem 388 (388 - 278) γ → Inv γ → InvPh1Rev16 γ) :
    RealizesCleanUnitary v (p57CleanDiagProj rComb (388 - 278) (by decide) Inv)
      (dPh1Rev16_388 v rComb)
      ((((ph1RevStatic16_388.onRegister rComb).toToffCircuit).eval)) := by
  have hStep1 : ∀ δ : BitAssignment 388, cleanRem 388 (388 - 386) δ → InvPh1Hole16 δ →
      cleanRem 388 (388 - 386) ((TempPhaseProg.cliff ph1XorCliff16).evalBits δ) ∧
        InvPeel16 15 ((TempPhaseProg.cliff ph1XorCliff16).evalBits δ) := fun δ hcl hh ↦
    ⟨fun w hw ↦ by
      rw [TempPhaseProg.evalBits, ph1XorCliff16.eval_outside ph1XorCliff16_supportsBelow δ w (by
        omega)]
      exact hcl w hw, invPh1Hole16_to_invPeel15 hh⟩
  have hInSeq := RealizesCleanUnitary_seq_asym
    (p57CleanDiagProj_conjTranspose rComb (388 - 386) (by decide) InvPh1Hole16)
    (p57CleanDiagProj_conjTranspose rComb (388 - 386) (by decide) (InvPeel16 15))
    (RealizesCleanUnitary.circuit v _ ((ph1XorCliff16.onRegister rComb).toCircuit))
    (dPh1PeelLoop16_realizes v rComb 15 le_rfl (InvPeel16 15) (fun _ _ hi ↦ hi))
    (p57SeqClean_prog_inv rComb (.cliff ph1XorCliff16) (by decide) (by decide) hStep1)
  have hMulIn : (((ph1PeelLoopStatic16 15 le_rfl).onRegister rComb).toToffCircuit).eval *
      ((ph1XorCliff16.onRegister rComb).toCircuit).eval =
      (((ph1InnerRevStatic16.onRegister rComb).toToffCircuit).eval) := by
    simp [ph1InnerRevStatic16, TempPhaseProg.onRegister, TempPhaseProg.toToffCircuit,
      Circuit.eval_seq]
  rw [hMulIn] at hInSeq
  have hDDef : dPh1Rev16_388 v rComb = p57ToDynWith v rComb (dPh1InnerRev16 v rComb) K_xorSq_388 :=
    rfl
  have hSDef : ph1RevStatic16_388 = K_xorSq_388.plug ph1InnerRevStatic16 := rfl
  rw [hDDef, hSDef]
  refine p57ToDynWith_realizes_inv v rComb ph1InnerRevStatic16 (dPh1InnerRev16 v rComb)
    InvPh1Hole16 (388 - 386) (by decide) hInSeq ph1InnerRevStatic16_valid_le
    K_xorSq_388 (388 - 278) (by decide) Inv
    ph1RevStatic16_388_spec.1 (fun γ hcr hi ↦ ?_)
  obtain ⟨_, h385, hAB⟩ := K_xorSq_388_spec γ hcr
  have hMutDst : (fun j : Fin 16 ↦ (K_xorSq_388.fwdBits γ) (ph1Dst16_388 j)) =
      fun j ↦ γ (ph1Dst16_388 j) :=
    funext fun j ↦ TempCtx.fwdBits_mut K_xorSq_388_pkg.disj γ ⟨⟨2 + j.val, by omega⟩, rfl⟩
  exact ⟨h385, by rw [hMutDst, hInv γ hcr hi, ← hAB]⟩
theorem bitsVal_sTrue18_split16 (f : Fin 18 → ZMod 2) :
    bitsVal f =
      (f 0).val + 2 * (f 1).val + 4 * bitsVal (fun k : Fin 16 ↦ f ⟨2 + k.val, by omega⟩) := by
  rw [bitsVal_succ_split, bitsVal_succ_split]
  have h1 : f (Fin.succ 0) = f 1 := congrArg f (Fin.ext rfl)
  have hmid : (fun k : Fin 16 ↦ f k.succ.succ) = fun k : Fin 16 ↦ f ⟨2 + k.val, by omega⟩ :=
    funext fun k ↦ congrArg f (Fin.ext (by simp; omega))
  rw [h1, hmid]
  ring
/-- Combined `18`-bit invariant at `.hole` of `K_wrapLin_388`. -/
def InvSTrueXorSqHole (δ : BitAssignment 388) : Prop :=
  bitsVal (fun j : Fin 18 ↦ δ (sTrue18W388 j)) = sTrueRawVal388 δ
theorem invSTrueXorSqHole_iff (δ : BitAssignment 388) :
    InvSTrueXorSqHole δ ↔ InvPh0Rev388 δ ∧ InvPh1Rev16 δ := by
  unfold InvSTrueXorSqHole InvPh0Rev388 InvPh1Rev16
  rw [bitsVal_sTrue18_split16 (fun j ↦ δ (sTrue18W388 j)), sTrueRawVal388_split δ]
  dsimp only [ph1Dst16_388]
  have hs0 : (δ (sTrue18W388 0)).val < 2 := ZMod.val_lt _
  have hs1 : (δ (sTrue18W388 1)).val < 2 := ZMod.val_lt _
  have hm0 : dVal388 0 δ % 2 < 2 := Nat.mod_lt _ (by decide)
  have hm1 : dVal388 1 δ % 2 < 2 := Nat.mod_lt _ (by decide)
  have hm2 : dVal388 2 δ % 2 < 2 := Nat.mod_lt _ (by decide)
  omega
/-- Inner `123`-`TempAnd` forward body (`ph0Fwd388 ; ph1Fwd16_388`). -/
def sTrue18InnerFwdXorSq_388 : TempPhaseProg 388 :=
  .seq ph0Fwd388 ph1Fwd16_388
/-- `123`-`TempAnd` (`492 T`) `< 388`-wire forward `sTrue18` circuit (`275..387` clean). -/
def sTrue18FwdXorSq_388 : TempPhaseProg 388 :=
  K_wrapLin_388.plug sTrue18InnerFwdXorSq_388
/-- Inner static reverse body (`ph1RevStatic16_388 ; ph0RevStatic388`). -/
def sTrue18InnerRevXorSq_388 : TempPhaseProg 388 :=
  .seq ph1RevStatic16_388 ph0RevStatic388
/-- Static `< 388`-wire reverse `sTrue18` circuit (`275..387` clean). -/
def sTrue18RevXorSq_388 : TempPhaseProg 388 :=
  K_wrapLin_388.plug sTrue18InnerRevXorSq_388
/-- Inner `428 T` (`0` Toffoli) dynamic uncomputer (`dPh1Rev16_388 ; dPh0Rev388`). -/
def dSTrue18InnerRevXorSq_388 {Var : Type} {n : ℕ} (v : Var) (rComb : QRegister 388 n) :
    DynamicCircuit Var n :=
  .seq (dPh1Rev16_388 v rComb) (dPh0Rev388 v rComb)
/-- `428 T` (`0` Toffoli) `< 388`-wire dynamic `sTrue18` uncomputer (`113` clean scratch wires
  `275..387`). -/
def dSTrue18RevXorSq_388 {Var : Type} {n : ℕ} (v : Var) (rComb : QRegister 388 n) :
    DynamicCircuit Var n :=
  p57ToDynWith v rComb (dSTrue18InnerRevXorSq_388 v rComb) K_wrapLin_388
theorem dSTrue18RevXorSq_388_count_t {Var : Type} {n : ℕ} (v : Var) (rComb : QRegister 388 n) :
    (dSTrue18RevXorSq_388 v rComb).count T = 428 := by
  dsimp only [dSTrue18RevXorSq_388, dSTrue18InnerRevXorSq_388]
  rw [p57ToDynWith_count_t, K_wrapLin_388_pkg.cnt_eq]
  simp [DynamicCircuit.count, dPh1Rev16_388_count_t, dPh0Rev388_count_t]
theorem dSTrue18RevXorSq_388_count_toff {Var : Type} {n : ℕ} (v : Var) (rComb : QRegister 388 n) :
    (dSTrue18RevXorSq_388 v rComb).count TOFF = 0 := by
  refine p57ToDynWith_count_toff v rComb _ ?_ K_wrapLin_388
  dsimp only [dSTrue18InnerRevXorSq_388]
  simp [DynamicCircuit.count, dPh1Rev16_388_count_toff, dPh0Rev388_count_toff]
theorem dSTrue18RevXorSq_388_preservesStore {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    (v : Var) (rComb : QRegister 388 n) :
    PreservesStoreConst (dSTrue18RevXorSq_388 v rComb) :=
  p57ToDynWith_preservesStore v rComb _
    (PreservesStoreConst.seq (dPh1Rev16_388_preservesStore v rComb)
      (dPh0Rev388_preservesStore v rComb))
    K_wrapLin_388
theorem sTrue18FwdXorSq_388_spec :
    ValidCleanRem 388 (388 - 275) sTrue18FwdXorSq_388 ∧
      sTrue18FwdXorSq_388.countTempAnd = 123 ∧
      (∀ β : BitAssignment 388, cleanRem 388 (388 - 275) β → sTrue18FwdXorSq_388.evalSign β = 0) ∧
      (∀ β : BitAssignment 388, cleanRem 388 (388 - 275) β →
        cleanRem 388 (388 - 275) (sTrue18FwdXorSq_388.evalBits β) ∧
        (∀ w : Wire 388, ¬ mutSTrue388 w → sTrue18FwdXorSq_388.evalBits β w = β w) ∧
        ((∀ j : Fin 18, β (sTrue18W388 j) = 0) →
          bitsVal (fun j : Fin 18 ↦ sTrue18FwdXorSq_388.evalBits β (sTrue18W388 j)) =
            sTrueRawVal388 (K_wrapLin_388.fwdBits β))) := by
  obtain ⟨hv0, hc0, h0⟩ := ph0Fwd388_spec
  obtain ⟨hv1, hc1, hs1, h1⟩ := ph1Fwd16_388_spec
  have hDef : sTrue18FwdXorSq_388 = K_wrapLin_388.plug sTrue18InnerFwdXorSq_388 := rfl
  have hInDef : sTrue18InnerFwdXorSq_388 = .seq ph0Fwd388 ph1Fwd16_388 := rfl
  have hvIn : ValidCleanRem 388 (388 - 278) sTrue18InnerFwdXorSq_388 :=
    ⟨388 - 278, by decide, hv0, hv1, fun δ hδ ↦ (h0 δ hδ).2.1⟩
  have hInNon : ∀ δ : BitAssignment 388, cleanRem 388 (388 - 278) δ →
      ∀ w : Wire 388, ¬ mutSTrue388 w → sTrue18InnerFwdXorSq_388.evalBits δ w = δ w := by
    intro δ hδ w hnw
    have hcl1 := (h0 δ hδ).2.1
    rw [hInDef, evalBits_seq,
      (h1 _ hcl1).2.1 w (fun k hk ↦ hnw ⟨⟨2 + k.val, by omega⟩, hk⟩),
      (h0 δ hδ).2.2.1 w (fun hk ↦ hnw ⟨0, hk⟩) (fun hk ↦ hnw ⟨1, hk⟩)]
  have hpkg := K_wrapLin_388_pkg
  obtain ⟨hvP, hcP, hsP, hbP⟩ :=
    ScopedBlock.graft_mutating_clean (M := 388) (rem := 388 - 275) (curHole := 278)
      mutSTrue388 K_wrapLin_388 hpkg.disj hpkg.supp (by decide) K_wrapLin_388.fwdBits hpkg.probe
      sTrue18InnerFwdXorSq_388 hvIn hInNon
  have hCnt : sTrue18FwdXorSq_388.countTempAnd = 123 := by
    rw [hDef, hcP, hpkg.cnt_eq, hInDef, countTempAnd_seq, hc0, hc1]
  refine ⟨hvP, hCnt, fun β hβ ↦ ?_, fun β hβ ↦ ?_⟩
  · have hcl0 := hpkg.clean β hβ
    have hcl1 := (h0 _ hcl0).2.1
    rw [hDef, hsP β hβ, hInDef, evalSign_seq, (h0 _ hcl0).1, hs1 _ hcl1]; rfl
  · have hNon : ∀ w : Wire 388, ¬ mutSTrue388 w → sTrue18FwdXorSq_388.evalBits β w = β w :=
      fun w hnw ↦ by rw [hDef, hbP β hβ w, ite_eq_right hnw]
    refine ⟨fun w hw ↦ by
      rw [hNon w (fun ⟨j, hj⟩ ↦ by
        have hlt : (sTrue18W388 j).val < 275 :=
          ((show ∀ j' : Fin 18, (sTrue18W388 j').val < 275 by decide) j)
        rw [hj] at hw; omega)]
      exact hβ w hw, hNon, fun hZero ↦ ?_⟩
    have hcl0 : cleanRem 388 (388 - 278) (K_wrapLin_388.fwdBits β) := hpkg.clean β hβ
    have hδ0 : ∀ j : Fin 18, (K_wrapLin_388.fwdBits β) (sTrue18W388 j) = 0 := fun j ↦
      (TempCtx.fwdBits_mut hpkg.disj β ⟨j, rfl⟩).trans (hZero j)
    have hFnOut : (fun j : Fin 18 ↦ sTrue18FwdXorSq_388.evalBits β (sTrue18W388 j)) =
        fun j : Fin 18 ↦ ph1Fwd16_388.evalBits
          (ph0Fwd388.evalBits (K_wrapLin_388.fwdBits β)) (sTrue18W388 j) := by
      funext j
      rw [hDef, hbP β hβ (sTrue18W388 j), ite_eq_left ⟨j, rfl⟩, hInDef, evalBits_seq]
    generalize hδ_def : K_wrapLin_388.fwdBits β = δ at hcl0 hδ0 hFnOut ⊢
    have h0_spec := h0 δ hcl0
    generalize hδ₁_def : ph0Fwd388.evalBits δ = δ₁ at h0_spec hFnOut
    have hcl1 : cleanRem 388 (388 - 278) δ₁ := h0_spec.2.1
    have hPh0_1 : InvPh0Rev388 δ₁ := h0_spec.2.2.2 (hδ0 0) (hδ0 1)
    have hδ₁_dst16 : ∀ k : Fin 16, δ₁ (ph1Dst16_388 k) = 0 := fun k ↦
      (h0_spec.2.2.1 (ph1Dst16_388 k)
        (by revert k; decide) (by revert k; decide)).trans (hδ0 ⟨2 + k.val, by omega⟩)
    have hd1 : ∀ w : Fin 3, dVal388 w δ₁ = dVal388 w δ := fun w ↦ by
      unfold dVal388
      refine congrArg bitsVal (funext fun k ↦ h0_spec.2.2.1 _ ?_ ?_) <;> (revert w k; decide)
    have h1_spec := h1 δ₁ hcl1
    generalize hδ₂_def : ph1Fwd16_388.evalBits δ₁ = δ₂ at h1_spec hFnOut
    have hDst16_2 : InvPh1Rev16 δ₂ := by
      unfold InvPh1Rev16
      have hd2 : ∀ w : Fin 3, dVal388 w δ₂ = dVal388 w δ₁ := fun w ↦ by
        unfold dVal388
        exact congrArg bitsVal (funext fun k ↦ h1_spec.2.1 _
          (fun m hm ↦ d8Wire_not_mutSTrue388 w k ⟨⟨2 + m.val, by omega⟩, hm⟩))
      rw [h1_spec.2.2 hδ₁_dst16, hd2 0, hd2 1, hd2 2]
    have hPh0_2 : InvPh0Rev388 δ₂ := by
      unfold InvPh0Rev388
      have hd2 : ∀ w : Fin 3, dVal388 w δ₂ = dVal388 w δ₁ := fun w ↦ by
        unfold dVal388
        exact congrArg bitsVal (funext fun k ↦ h1_spec.2.1 _
          (fun m hm ↦ d8Wire_not_mutSTrue388 w k ⟨⟨2 + m.val, by omega⟩, hm⟩))
      rw [h1_spec.2.1 (sTrue18W388 0) (fun k ↦ by revert k; decide),
        h1_spec.2.1 (sTrue18W388 1) (fun k ↦ by revert k; decide),
        hd2 0, hd2 1, hd2 2]
      exact hPh0_1
    have hHole2 : InvSTrueXorSqHole δ₂ := (invSTrueXorSqHole_iff δ₂).mpr ⟨hPh0_2, hDst16_2⟩
    unfold InvSTrueXorSqHole at hHole2
    have hd_all : ∀ w : Fin 3, dVal388 w δ₂ = dVal388 w δ := fun w ↦ by
      have hd2 : dVal388 w δ₂ = dVal388 w δ₁ :=
        congrArg bitsVal (funext fun k ↦ h1_spec.2.1 _
          (fun m hm ↦ d8Wire_not_mutSTrue388 w k ⟨⟨2 + m.val, by omega⟩, hm⟩))
      exact hd2.trans (hd1 w)
    have hRawEq : sTrueRawVal388 δ₂ = sTrueRawVal388 δ := by
      unfold sTrueRawVal388; rw [hd_all 0, hd_all 1, hd_all 2]
    rw [hFnOut, hHole2, hRawEq]
theorem sTrue18RevXorSq_388_spec :
    ValidCleanRem 388 (388 - 275) sTrue18RevXorSq_388 ∧
      (∀ γ : BitAssignment 388, cleanRem 388 (388 - 275) γ →
        sTrue18RevXorSq_388.evalSign γ = 0 ∧
        cleanRem 388 (388 - 275) (sTrue18RevXorSq_388.evalBits γ) ∧
        (∀ w : Wire 388, ¬ mutSTrue388 w → sTrue18RevXorSq_388.evalBits γ w = γ w) ∧
        (bitsVal (fun j : Fin 18 ↦ γ (sTrue18W388 j)) = sTrueRawVal388 (K_wrapLin_388.fwdBits γ) →
          ∀ j : Fin 18, sTrue18RevXorSq_388.evalBits γ (sTrue18W388 j) = 0)) := by
  obtain ⟨hv1, h1⟩ := ph1RevStatic16_388_spec
  obtain ⟨hv0, _, h0⟩ := ph0RevStatic388_spec
  have hDef : sTrue18RevXorSq_388 = K_wrapLin_388.plug sTrue18InnerRevXorSq_388 := rfl
  have hInDef : sTrue18InnerRevXorSq_388 = .seq ph1RevStatic16_388 ph0RevStatic388 := rfl
  have hvIn : ValidCleanRem 388 (388 - 278) sTrue18InnerRevXorSq_388 :=
    ⟨388 - 278, by decide, hv1, hv0, fun δ hδ ↦ (h1 δ hδ).2.1⟩
  have hInNon : ∀ δ : BitAssignment 388, cleanRem 388 (388 - 278) δ →
      ∀ w : Wire 388, ¬ mutSTrue388 w → sTrue18InnerRevXorSq_388.evalBits δ w = δ w := by
    intro δ hδ w hnw
    have hcl1 := (h1 δ hδ).2.1
    rw [hInDef, evalBits_seq,
      (h0 _ hcl1).2.2.1 w (fun hk ↦ hnw ⟨0, hk⟩) (fun hk ↦ hnw ⟨1, hk⟩),
      (h1 δ hδ).2.2.1 w (fun k hk ↦ hnw ⟨⟨2 + k.val, by omega⟩, hk⟩)]
  have hpkg := K_wrapLin_388_pkg
  obtain ⟨hvP, _, hsP, hbP⟩ :=
    ScopedBlock.graft_mutating_clean (M := 388) (rem := 388 - 275) (curHole := 278)
      mutSTrue388 K_wrapLin_388 hpkg.disj hpkg.supp (by decide) K_wrapLin_388.fwdBits hpkg.probe
      sTrue18InnerRevXorSq_388 hvIn hInNon
  refine ⟨hvP, fun γ hγ ↦ ?_⟩
  have hcl0 := hpkg.clean γ hγ
  have hcl1 := (h1 _ hcl0).2.1
  have hNon : ∀ w : Wire 388, ¬ mutSTrue388 w → sTrue18RevXorSq_388.evalBits γ w = γ w :=
    fun w hnw ↦ by rw [hDef, hbP γ hγ w, ite_eq_right hnw]
  refine ⟨by
    rw [hDef, hsP γ hγ, hInDef, evalSign_seq, (h1 _ hcl0).1, (h0 _ hcl1).1]; rfl,
    fun w hw ↦ by
      rw [hNon w (fun ⟨j, hj⟩ ↦ by
        have hlt : (sTrue18W388 j).val < 275 :=
          ((show ∀ j' : Fin 18, (sTrue18W388 j').val < 275 by decide) j)
        rw [hj] at hw; omega)]
      exact hγ w hw,
    hNon, fun hVal j ↦ ?_⟩
  rw [hDef, hbP γ hγ (sTrue18W388 j), ite_eq_left ⟨j, rfl⟩, hInDef, evalBits_seq]
  have hMutAll : (fun i : Fin 18 ↦ (K_wrapLin_388.fwdBits γ) (sTrue18W388 i)) =
      fun i ↦ γ (sTrue18W388 i) :=
    funext fun i ↦ TempCtx.fwdBits_mut hpkg.disj γ ⟨i, rfl⟩
  generalize hδ_def : K_wrapLin_388.fwdBits γ = δ at hcl0 hcl1 hMutAll hVal ⊢
  have hHole : InvSTrueXorSqHole δ := by
    unfold InvSTrueXorSqHole; rwa [hMutAll]
  obtain ⟨hPh0_0, hPh1_0⟩ := (invSTrueXorSqHole_iff δ).mp hHole
  have h1_spec := h1 δ hcl0
  generalize hδ₁_def : ph1RevStatic16_388.evalBits δ = δ₁ at hcl1 h1_spec ⊢
  have h16_1 := h1_spec.2.2.2 hPh1_0
  have hd1 : ∀ w : Fin 3, dVal388 w δ₁ = dVal388 w δ := fun w ↦ by
    unfold dVal388
    exact congrArg bitsVal (funext fun k ↦ h1_spec.2.2.1 _
      (fun m hm ↦ d8Wire_not_mutSTrue388 w k ⟨⟨2 + m.val, by omega⟩, hm⟩))
  have hPh0_1 : InvPh0Rev388 δ₁ := by
    unfold InvPh0Rev388
    rw [h1_spec.2.2.1 (sTrue18W388 0) (fun k ↦ by revert k; decide),
      h1_spec.2.2.1 (sTrue18W388 1) (fun k ↦ by revert k; decide),
      hd1 0, hd1 1, hd1 2]
    exact hPh0_0
  obtain ⟨hz0, hz1⟩ := (h0 δ₁ hcl1).2.2.2 hPh0_1
  by_cases hj0 : j = 0
  · subst hj0; exact hz0
  · by_cases hj1 : j = 1
    · subst hj1; exact hz1
    · have h0ne : sTrue18W388 j ≠ sTrue18W388 0 := fun he ↦ hj0 (sTrue18W388_injective he)
      have h1ne : sTrue18W388 j ≠ sTrue18W388 1 := fun he ↦ hj1 (sTrue18W388_injective he)
      rw [(h0 δ₁ hcl1).2.2.1 (sTrue18W388 j) h0ne h1ne]
      have hj_ge2 : 2 ≤ j.val ∧ j.val < 18 := by
        have := j.isLt
        have hne0 : j.val ≠ 0 := fun h ↦ hj0 (Fin.ext h)
        have hne1 : j.val ≠ 1 := fun h ↦ hj1 (Fin.ext h)
        omega
      have heq_dst : sTrue18W388 j = ph1Dst16_388 ⟨j.val - 2, by omega⟩ := by
        dsimp only [ph1Dst16_388]
        exact congrArg sTrue18W388 (Fin.ext (by dsimp; omega))
      rw [heq_dst]
      exact h16_1 ⟨j.val - 2, by omega⟩
theorem dSTrue18RevXorSq_388_realizes
    {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)]
    (v : Var) (rComb : QRegister 388 n)
    (Inv : BitAssignment 388 → Prop)
    (hInv : ∀ γ : BitAssignment 388, cleanRem 388 (388 - 275) γ → Inv γ →
      bitsVal (fun j : Fin 18 ↦ γ (sTrue18W388 j)) = sTrueRawVal388 (K_wrapLin_388.fwdBits γ)) :
    RealizesCleanUnitary v (p57CleanDiagProj rComb (388 - 275) (by decide) Inv)
      (dSTrue18RevXorSq_388 v rComb)
      ((((sTrue18RevXorSq_388.onRegister rComb).toToffCircuit).eval)) := by
  obtain ⟨_, h1⟩ := ph1RevStatic16_388_spec
  have hStep10 : ∀ δ : BitAssignment 388, cleanRem 388 (388 - 278) δ → InvSTrueXorSqHole δ →
      cleanRem 388 (388 - 278) (ph1RevStatic16_388.evalBits δ) ∧
        InvPh0Rev388 (ph1RevStatic16_388.evalBits δ) := by
    intro δ hcl hh
    obtain ⟨hPh0, _⟩ := (invSTrueXorSqHole_iff δ).mp hh
    have hd1 : ∀ w : Fin 3, dVal388 w (ph1RevStatic16_388.evalBits δ) = dVal388 w δ := fun w ↦ by
      unfold dVal388
      exact congrArg bitsVal (funext fun k ↦ (h1 δ hcl).2.2.1 _
        (fun m hm ↦ d8Wire_not_mutSTrue388 w k ⟨⟨2 + m.val, by omega⟩, hm⟩))
    refine ⟨(h1 δ hcl).2.1, ?_⟩
    unfold InvPh0Rev388
    rw [(h1 δ hcl).2.2.1 (sTrue18W388 0) (fun k ↦ by revert k; decide),
      (h1 δ hcl).2.2.1 (sTrue18W388 1) (fun k ↦ by revert k; decide),
      hd1 0, hd1 1, hd1 2]
    exact hPh0
  have hR10 := RealizesCleanUnitary_seq_asym
    (p57CleanDiagProj_conjTranspose rComb (388 - 278) (by decide) InvSTrueXorSqHole)
    (p57CleanDiagProj_conjTranspose rComb (388 - 278) (by decide) InvPh0Rev388)
    (dPh1Rev16_388_realizes v rComb InvSTrueXorSqHole (fun δ _ hh ↦
      ((invSTrueXorSqHole_iff δ).mp hh).2))
    (dPh0Rev388_realizes v rComb InvPh0Rev388 (fun _ _ hi ↦ hi))
    (p57SeqClean_prog_inv rComb ph1RevStatic16_388 (by decide) (by decide) hStep10)
  have hMul : (((ph0RevStatic388.onRegister rComb).toToffCircuit).eval) *
      (((ph1RevStatic16_388.onRegister rComb).toToffCircuit).eval) =
      (((sTrue18InnerRevXorSq_388.onRegister rComb).toToffCircuit).eval) := by
    simp [sTrue18InnerRevXorSq_388, TempPhaseProg.onRegister, TempPhaseProg.toToffCircuit,
      Circuit.eval_seq]
  rw [hMul] at hR10
  have hDDef : dSTrue18RevXorSq_388 v rComb =
      p57ToDynWith v rComb (dSTrue18InnerRevXorSq_388 v rComb) K_wrapLin_388 := rfl
  have hSDef : sTrue18RevXorSq_388 = K_wrapLin_388.plug sTrue18InnerRevXorSq_388 := rfl
  rw [hDDef, hSDef]
  refine p57ToDynWith_realizes_zero_and v rComb sTrue18InnerRevXorSq_388 (dSTrue18InnerRevXorSq_388
    v rComb)
    InvSTrueXorSqHole (388 - 278) (by decide) hR10
    K_wrapLin_388 K_wrapLin_388_pkg.cnt_eq (388 - 275) (by decide) Inv
    sTrue18RevXorSq_388_spec.1 (fun γ hcr hi ↦ ⟨K_wrapLin_388_pkg.clean γ hcr, ?_⟩)
  unfold InvSTrueXorSqHole
  have hMutAll : (fun i : Fin 18 ↦ (K_wrapLin_388.fwdBits γ) (sTrue18W388 i)) =
      fun i ↦ γ (sTrue18W388 i) :=
    funext fun i ↦ TempCtx.fwdBits_mut K_wrapLin_388_pkg.disj γ ⟨i, rfl⟩
  rw [hMutAll]
  exact hInv γ hcr hi
/-!
## Section 5: `437`-Wire Wrappers, `pStep1XorSq_275` (`272` `TempAnd`s = `1,088 T`),
`stepBundleW_step1XorSq`, & `stepBundleW_dSTrue18RevXorSq` (`338 ≤ topW ≤ 388`)
-/
/-- `437`-wire `123`-`TempAnd` (`492 T`, `-172 T` vs `sTrue18Fwd113_275`) forward `sTrue18`
  circuit supported strictly on `< 388` wires. -/
def sTrue18FwdXorSq_275 : TempPhaseProg 437 :=
  padProg388_437 sTrue18FwdXorSq_388
/-- `437`-wire static reverse `sTrue18` circuit supported strictly on `< 388` wires. -/
def sTrue18RevXorSq_275 : TempPhaseProg 437 :=
  padProg388_437 sTrue18RevXorSq_388
/-- `437`-wire `428 T` (`-172 T` vs `dSTrue18Rev113_275`, `0` Toffoli) dynamic `sTrue18`
  uncomputer touching only wires `< 388`. -/
def dSTrue18RevXorSq_275 {Var : Type} {n : ℕ} (v : Var) (rComb : QRegister 437 n) :
    DynamicCircuit Var n :=
  dSTrue18RevXorSq_388 v (rComb.compose (QRegister.block 0 388 (by decide)))
theorem sTrue18FwdXorSq_275_countTempAnd : sTrue18FwdXorSq_275.countTempAnd = 123 := by
  have hDef : sTrue18FwdXorSq_275 = padProg388_437 sTrue18FwdXorSq_388 := rfl
  rw [hDef, padProg388_437_countTempAnd, sTrue18FwdXorSq_388_spec.2.1]
theorem sTrue18FwdXorSq_275_supportsBelow388 : progSupportsBelowB 388 sTrue18FwdXorSq_275 = true :=
  progSupportsBelowB_padProg388_437 sTrue18FwdXorSq_388
theorem sTrue18FwdXorSq_275_validCleanRem : ValidCleanRem 437 (437 - 275) sTrue18FwdXorSq_275 :=
  padProg388_437_validCleanRem (by decide) sTrue18FwdXorSq_388 sTrue18FwdXorSq_388_spec.1
theorem dSTrue18RevXorSq_275_count_t {Var : Type} {n : ℕ} (v : Var) (rComb : QRegister 437 n) :
    (dSTrue18RevXorSq_275 v rComb).count T = 428 :=
  dSTrue18RevXorSq_388_count_t v (rComb.compose (QRegister.block 0 388 (by decide)))
theorem dSTrue18RevXorSq_275_count_toff {Var : Type} {n : ℕ} (v : Var) (rComb : QRegister 437 n) :
    (dSTrue18RevXorSq_275 v rComb).count TOFF = 0 :=
  dSTrue18RevXorSq_388_count_toff v (rComb.compose (QRegister.block 0 388 (by decide)))
theorem dSTrue18RevXorSq_275_preservesStore {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    (v : Var) (rComb : QRegister 437 n) :
    PreservesStoreConst (dSTrue18RevXorSq_275 v rComb) :=
  dSTrue18RevXorSq_388_preservesStore v (rComb.compose (QRegister.block 0 388 (by decide)))
theorem sTrue18FwdXorSq_275_spec (β : BitAssignment 437)
    (hβ : cleanRem 388 (388 - 275) (truncAssign388 β)) :
    sTrue18FwdXorSq_275.evalSign β = 0 ∧
      cleanRem 388 (388 - 275) (truncAssign388 (sTrue18FwdXorSq_275.evalBits β)) ∧
      (∀ q : Wire 437, ¬ mutSTrue q → sTrue18FwdXorSq_275.evalBits β q = β q) ∧
      (InvWrapLin β → (∀ j : Fin 18, β (sTrue18WDefault j) = 0) →
        bitsVal (fun j : Fin 18 ↦ sTrue18FwdXorSq_275.evalBits β (sTrue18WDefault j)) =
          sTrueRawValPBuf β) := by
  have hDef : sTrue18FwdXorSq_275 = padProg388_437 sTrue18FwdXorSq_388 := rfl
  rw [hDef]
  obtain ⟨_, _, hs388, hb388⟩ := sTrue18FwdXorSq_388_spec
  obtain ⟨hsP, hbLt, hbGe⟩ := padProg388_437_eval sTrue18FwdXorSq_388 β
  obtain ⟨hclOut, hNon388, hSum388⟩ := hb388 (truncAssign388 β) hβ
  have hTrOut : truncAssign388 ((padProg388_437 sTrue18FwdXorSq_388).evalBits β) =
      sTrue18FwdXorSq_388.evalBits (truncAssign388 β) := by
    funext u
    dsimp only [truncAssign388]
    rw [hbLt ⟨u.val, by omega⟩ u.isLt]
  refine ⟨hsP.trans (hs388 _ hβ), by rw [hTrOut]; exact hclOut, fun q hnq ↦ ?_, fun hW hZero ↦ ?_⟩
  · by_cases hlt : q.val < 388
    · rw [hbLt q hlt]
      exact hNon388 ⟨q.val, hlt⟩ (fun hm ↦ hnq ((mutSTrue388_iff _).mp hm))
    · exact hbGe q (by omega)
  · have hFn : (fun j : Fin 18 ↦
      (padProg388_437 sTrue18FwdXorSq_388).evalBits β (sTrue18WDefault j)) =
        fun j : Fin 18 ↦ sTrue18FwdXorSq_388.evalBits (truncAssign388 β) (sTrue18W388 j) := by
      funext j
      have hlt : (sTrue18WDefault j).val < 388 :=
        ((show ∀ j' : Fin 18, (sTrue18WDefault j').val < 388 by decide) j)
      rw [hbLt (sTrue18WDefault j) hlt]
      exact congrArg (sTrue18FwdXorSq_388.evalBits (truncAssign388 β)) (Fin.ext rfl)
    have hZ388 : ∀ j : Fin 18, truncAssign388 β (sTrue18W388 j) = 0 := fun j ↦ hZero j
    rw [hFn, hSum388 hZ388, sTrueRawVal388_eq_sTrueRawValPBuf hβ hW]
theorem sTrue18FwdXorSq_275_eq_orig (β : BitAssignment 437)
    (hβ : cleanRem 437 (437 - 275) β) (hW : InvWrapLin β)
    (hZero : ∀ j : Fin 18, β (sTrue18WDefault j) = 0) :
    sTrue18FwdXorSq_275.evalBits β = sTrue18FwdPBuf275.evalBits β := by
  have hβ388 : cleanRem 388 (388 - 275) (truncAssign388 β) :=
    fun u hu ↦ hβ ⟨u.val, by omega⟩ (by dsimp; omega)
  obtain ⟨_, _, hNon1, hVal1⟩ := sTrue18FwdXorSq_275_spec β hβ388
  obtain ⟨_, hNon2, hVal2⟩ := sTrue18FwdPBuf275_spec.2.2.2 β hβ
  have hEqBits := Slot3MicroEngineAux.bitsVal_injective ((hVal1 hW hZero).trans (hVal2 hZero).symm)
  funext q
  by_cases hq : mutSTrue q
  · obtain ⟨j, rfl⟩ := hq
    exact congrFun hEqBits j
  · exact (hNon1 q hq).trans (hNon2 q (fun j hj ↦ hq ⟨j, hj⟩)).symm
theorem sTrue18RevXorSq_275_spec (γ : BitAssignment 437)
    (hγ : cleanRem 388 (388 - 275) (truncAssign388 γ)) :
    sTrue18RevXorSq_275.evalSign γ = 0 ∧
      cleanRem 388 (388 - 275) (truncAssign388 (sTrue18RevXorSq_275.evalBits γ)) ∧
      (∀ q : Wire 437, ¬ mutSTrue q → sTrue18RevXorSq_275.evalBits γ q = γ q) ∧
      (InvWrapLin γ →
        bitsVal (fun j : Fin 18 ↦ γ (sTrue18WDefault j)) = sTrueRawValPBuf γ →
        ∀ j : Fin 18, sTrue18RevXorSq_275.evalBits γ (sTrue18WDefault j) = 0) := by
  have hDef : sTrue18RevXorSq_275 = padProg388_437 sTrue18RevXorSq_388 := rfl
  rw [hDef]
  obtain ⟨_, h388⟩ := sTrue18RevXorSq_388_spec
  obtain ⟨hsP, hbLt, hbGe⟩ := padProg388_437_eval sTrue18RevXorSq_388 γ
  obtain ⟨hs388, hclOut, hNon388, hZero388⟩ := h388 (truncAssign388 γ) hγ
  have hTrOut : truncAssign388 ((padProg388_437 sTrue18RevXorSq_388).evalBits γ) =
      sTrue18RevXorSq_388.evalBits (truncAssign388 γ) := by
    funext u
    dsimp only [truncAssign388]
    rw [hbLt ⟨u.val, by omega⟩ u.isLt]
  refine ⟨hsP.trans hs388, by rw [hTrOut]; exact hclOut, fun q hnq ↦ ?_, fun hW hVal j ↦ ?_⟩
  · by_cases hlt : q.val < 388
    · rw [hbLt q hlt]
      exact hNon388 ⟨q.val, hlt⟩ (fun hm ↦ hnq ((mutSTrue388_iff _).mp hm))
    · exact hbGe q (by omega)
  · have hlt : (sTrue18WDefault j).val < 388 :=
      ((show ∀ j' : Fin 18, (sTrue18WDefault j').val < 388 by decide) j)
    have hj : (⟨(sTrue18WDefault j).val, hlt⟩ : Wire 388) = sTrue18W388 j := Fin.ext rfl
    rw [hbLt (sTrue18WDefault j) hlt, hj]
    exact hZero388 (hVal.trans (sTrueRawVal388_eq_sTrueRawValPBuf hγ hW).symm) j
theorem dSTrue18RevXorSq_275_realizes_388
    {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)]
    (v : Var) (rComb : QRegister 437 n)
    (Inv388 : BitAssignment 388 → Prop)
    (hInv : ∀ γ388 : BitAssignment 388, cleanRem 388 (388 - 275) γ388 → Inv388 γ388 →
      bitsVal (fun j : Fin 18 ↦ γ388 (sTrue18W388 j)) =
        sTrueRawVal388 (K_wrapLin_388.fwdBits γ388)) :
    RealizesCleanUnitary v
      (p57CleanDiagProj (rComb.compose (QRegister.block 0 388 (by decide)))
        (388 - 275) (by decide) Inv388)
      (dSTrue18RevXorSq_275 v rComb)
      ((((sTrue18RevXorSq_275.onRegister rComb).toToffCircuit).eval)) := by
  have hDDef : dSTrue18RevXorSq_275 v rComb =
      dSTrue18RevXorSq_388 v (rComb.compose (QRegister.block 0 388 (by decide))) := rfl
  have hSDef : sTrue18RevXorSq_275 = padProg388_437 sTrue18RevXorSq_388 := rfl
  rw [hDDef, hSDef, padProg388_437_onRegister_eq]
  exact dSTrue18RevXorSq_388_realizes v (rComb.compose (QRegister.block 0 388 (by decide)))
    Inv388 hInv
/-- Bad-zone predicate `201 ≤ w < 251` on `Wire 388`. -/
def bad251_388 (w : Wire 388) : Bool := decide (201 ≤ w.val ∧ w.val < 251)
/-- Bad-zone predicate `201 ≤ w < 251` on `Wire 437`. -/
def bad251_437 (w : Wire 437) : Bool := decide (201 ≤ w.val ∧ w.val < 251)
/-- Disjointness of a `388`-wire Clifford program from `201..250`. -/
def cliffDisjoint251_388 : CliffProg 388 → Bool
  | .nil => true
  | .x q => !bad251_388 q
  | .cnot c t _ => !bad251_388 c && !bad251_388 t
  | .seq c₁ c₂ => cliffDisjoint251_388 c₁ && cliffDisjoint251_388 c₂
/-- Disjointness of a `388`-wire `TempPhaseProg` from `201..250`. -/
def progDisjoint251_388 : TempPhaseProg 388 → Bool
  | .nil => true
  | .cliff c => cliffDisjoint251_388 c
  | .z q => !bad251_388 q
  | .seq p₁ p₂ => progDisjoint251_388 p₁ && progDisjoint251_388 p₂
  | .tempAnd c₁ c₂ anc _ _ _ body =>
      !bad251_388 c₁ && !bad251_388 c₂ && !bad251_388 anc && progDisjoint251_388 body
/-- Disjointness of a `388`-wire `TempCtx` from `201..250`. -/
def ctxDisjoint251_388 : TempCtx 388 → Bool
  | .hole => true
  | .seqPre c K => cliffDisjoint251_388 c && ctxDisjoint251_388 K
  | .seqPost K c => ctxDisjoint251_388 K && cliffDisjoint251_388 c
  | .tempAnd c₁ c₂ anc _ _ _ K =>
      !bad251_388 c₁ && !bad251_388 c₂ && !bad251_388 anc && ctxDisjoint251_388 K
/-- Disjointness of a `437`-wire `TempCtx` from `201..250`. -/
def ctxDisjoint251_437 : TempCtx 437 → Bool
  | .hole => true
  | .seqPre c K => cliffDisjointBad bad251_437 c && ctxDisjoint251_437 K
  | .seqPost K c => ctxDisjoint251_437 K && cliffDisjointBad bad251_437 c
  | .tempAnd c₁ c₂ anc _ _ _ K =>
      !bad251_437 c₁ && !bad251_437 c₂ && !bad251_437 anc && ctxDisjoint251_437 K
/-- Disjointness of a `P57Step` from `201..250`. -/
def stepDisjoint251 : P57Step → Bool
  | .x q => !decide (201 ≤ q ∧ q < 251)
  | .cnot c t => !decide (201 ≤ c ∧ c < 251) && !decide (201 ≤ t ∧ t < 251)
  | .tempAnd a b dst =>
      !decide (201 ≤ a ∧ a < 251) && !decide (201 ≤ b ∧ b < 251) && !decide (201 ≤ dst ∧ dst < 251)
theorem ctxDisjoint251_437_append :
    ∀ (F G : TempCtx 437),
      ctxDisjoint251_437 F = true → ctxDisjoint251_437 G = true →
      ctxDisjoint251_437 (F.append G) = true
  | .hole, _, _, hG => hG
  | .seqPre _ K, G, hF, hG => by
      obtain ⟨hc, hK⟩ := Bool.and_eq_true _ _ |>.mp hF
      exact Bool.and_eq_true _ _ |>.mpr ⟨hc, ctxDisjoint251_437_append K G hK hG⟩
  | .seqPost K _, G, hF, hG => by
      obtain ⟨hK, hc⟩ := Bool.and_eq_true _ _ |>.mp hF
      exact Bool.and_eq_true _ _ |>.mpr ⟨ctxDisjoint251_437_append K G hK hG, hc⟩
  | .tempAnd _ _ _ _ _ _ K, G, hF, hG => by
      obtain ⟨h123, hK⟩ := Bool.and_eq_true _ _ |>.mp hF
      obtain ⟨h12, h3⟩ := Bool.and_eq_true _ _ |>.mp h123
      obtain ⟨h1, h2⟩ := Bool.and_eq_true _ _ |>.mp h12
      exact Bool.and_eq_true _ _ |>.mpr
        ⟨Bool.and_eq_true _ _ |>.mpr ⟨Bool.and_eq_true _ _ |>.mpr ⟨h1, h2⟩, h3⟩,
          ctxDisjoint251_437_append K G hK hG⟩
theorem ctxDisjoint251_437_stepToSingleCtx (s : P57Step) (hs : stepDisjoint251 s = true) :
    ctxDisjoint251_437 (stepToSingleCtx s) = true := by
  cases s with
  | x q =>
      simp only [stepDisjoint251, Bool.not_eq_true', decide_eq_false_iff_not] at hs
      dsimp only [stepToSingleCtx]
      split_ifs with hq
      · simp [ctxCliffAlloc, ctxDisjoint251_437, cliffDisjointBad, CliffProg.inv, bad251_437, hs]
      · rfl
  | cnot c t =>
      simp only [stepDisjoint251, Bool.and_eq_true, Bool.not_eq_true',
        decide_eq_false_iff_not] at hs
      dsimp only [stepToSingleCtx]
      split_ifs with h
      · simp [ctxCliffAlloc, ctxDisjoint251_437, cliffDisjointBad, CliffProg.inv, bad251_437, hs.1,
          hs.2]
      · rfl
  | tempAnd a b dst =>
      simp only [stepDisjoint251, Bool.and_eq_true, Bool.not_eq_true',
        decide_eq_false_iff_not] at hs
      dsimp only [stepToSingleCtx]
      split_ifs with h
      · simp [ctxTempBit, ctxDisjoint251_437, bad251_437, hs.1.1, hs.1.2, hs.2]
      · rfl
theorem ctxDisjoint251_437_buildP57Ctx :
    ∀ (ss : List P57Step),
      ss.all stepDisjoint251 = true → ctxDisjoint251_437 (buildP57Ctx ss) = true
  | [], _ => rfl
  | s :: ss, h => by
      simp only [List.all_cons, Bool.and_eq_true] at h
      exact ctxDisjoint251_437_append _ _
        (ctxDisjoint251_437_stepToSingleCtx s h.1)
        (ctxDisjoint251_437_buildP57Ctx ss h.2)
theorem cliffDisjoint251_truncateCliffB :
    ∀ (c : CliffProg 437) (hc : cliffSupportsBelowB 388 c = true),
      cliffDisjointBad bad251_437 c = true → cliffDisjoint251_388 (truncateCliffB 388 c hc) = true
  | .nil, _, _ => rfl
  | .x _, _, h => h
  | .cnot _ _ _, _, h => h
  | .seq c₁ c₂, _, h => by
      obtain ⟨h1, h2⟩ := Bool.and_eq_true _ _ |>.mp h
      exact Bool.and_eq_true _ _ |>.mpr
        ⟨cliffDisjoint251_truncateCliffB c₁ _ h1, cliffDisjoint251_truncateCliffB c₂ _ h2⟩
theorem ctxDisjoint251_truncateCtxB :
    ∀ (K : TempCtx 437) (hK : ctxSupportsBelowB 388 K = true),
      ctxDisjoint251_437 K = true → ctxDisjoint251_388 (truncateCtxB 388 K hK) = true
  | .hole, _, _ => rfl
  | .seqPre c K, _, h => by
      obtain ⟨hc, hK'⟩ := Bool.and_eq_true _ _ |>.mp h
      exact Bool.and_eq_true _ _ |>.mpr
        ⟨cliffDisjoint251_truncateCliffB c _ hc, ctxDisjoint251_truncateCtxB K _ hK'⟩
  | .seqPost K c, _, h => by
      obtain ⟨hK', hc⟩ := Bool.and_eq_true _ _ |>.mp h
      exact Bool.and_eq_true _ _ |>.mpr
        ⟨ctxDisjoint251_truncateCtxB K _ hK', cliffDisjoint251_truncateCliffB c _ hc⟩
  | .tempAnd _ _ _ _ _ _ K, _, h => by
      obtain ⟨h123, hK'⟩ := Bool.and_eq_true _ _ |>.mp h
      exact Bool.and_eq_true _ _ |>.mpr ⟨h123, ctxDisjoint251_truncateCtxB K _ hK'⟩
theorem progDisjoint251_388_plug :
    ∀ (K : TempCtx 388) (p : TempPhaseProg 388),
      ctxDisjoint251_388 K = true → progDisjoint251_388 p = true →
      progDisjoint251_388 (K.plug p) = true
  | .hole, _, _, hp => hp
  | .seqPre _ K, p, hK, hp => by
      obtain ⟨hc, hK'⟩ := Bool.and_eq_true _ _ |>.mp hK
      exact Bool.and_eq_true _ _ |>.mpr ⟨hc, progDisjoint251_388_plug K p hK' hp⟩
  | .seqPost K _, p, hK, hp => by
      obtain ⟨hK', hc⟩ := Bool.and_eq_true _ _ |>.mp hK
      exact Bool.and_eq_true _ _ |>.mpr ⟨progDisjoint251_388_plug K p hK' hp, hc⟩
  | .tempAnd _ _ _ _ _ _ K, p, hK, hp => by
      obtain ⟨h123, hK'⟩ := Bool.and_eq_true _ _ |>.mp hK
      exact Bool.and_eq_true _ _ |>.mpr ⟨h123, progDisjoint251_388_plug K p hK' hp⟩
theorem not_isBadX_of_not_bad251 (q : Wire 388) (hq : (!bad251_388 q) = true) :
    (!isBadXM 388 (isBad388W 338) ⟨q.val, by omega⟩) = true := by
  simp only [bad251_388, Bool.not_eq_true', decide_eq_false_iff_not] at hq
  simp only [isBadXM, isBad388W, isBad388, Bool.not_eq_true', Bool.or_eq_false_iff,
    decide_eq_false_iff_not]
  have := q.isLt
  omega
theorem cliffDisjointBad_padCliff388_437 :
    ∀ (c : CliffProg 388),
      cliffDisjoint251_388 c = true →
      cliffDisjointBad (isBadXM 388 (isBad388W 338)) (padCliff388_437 c) = true
  | .nil, _ => rfl
  | .x q, h => not_isBadX_of_not_bad251 q h
  | .cnot c t _, h => by
      obtain ⟨hc, ht⟩ := Bool.and_eq_true _ _ |>.mp h
      exact Bool.and_eq_true _ _ |>.mpr
        ⟨not_isBadX_of_not_bad251 c hc, not_isBadX_of_not_bad251 t ht⟩
  | .seq c₁ c₂, h => by
      obtain ⟨h1, h2⟩ := Bool.and_eq_true _ _ |>.mp h
      exact Bool.and_eq_true _ _ |>.mpr
        ⟨cliffDisjointBad_padCliff388_437 c₁ h1, cliffDisjointBad_padCliff388_437 c₂ h2⟩
theorem progDisjointBad_padProg388_437 :
    ∀ (p : TempPhaseProg 388),
      progDisjoint251_388 p = true →
      progDisjointBad (isBadXM 388 (isBad388W 338)) (padProg388_437 p) = true
  | .nil, _ => rfl
  | .cliff c, h => cliffDisjointBad_padCliff388_437 c h
  | .z q, h => not_isBadX_of_not_bad251 q h
  | .seq p₁ p₂, h => by
      obtain ⟨h1, h2⟩ := Bool.and_eq_true _ _ |>.mp h
      exact Bool.and_eq_true _ _ |>.mpr
        ⟨progDisjointBad_padProg388_437 p₁ h1, progDisjointBad_padProg388_437 p₂ h2⟩
  | .tempAnd c₁ c₂ anc _ _ _ body, h => by
      obtain ⟨h123, hb⟩ := Bool.and_eq_true _ _ |>.mp h
      obtain ⟨h12, h3⟩ := Bool.and_eq_true _ _ |>.mp h123
      obtain ⟨h1, h2⟩ := Bool.and_eq_true _ _ |>.mp h12
      dsimp only [padProg388_437, progDisjointBad]
      rw [not_isBadX_of_not_bad251 c₁ h1,
        not_isBadX_of_not_bad251 c₂ h2,
        not_isBadX_of_not_bad251 anc h3,
        progDisjointBad_padProg388_437 body hb]
      rfl
theorem sTrue18FwdXorSq_275_disjoint338 :
    progDisjointBad (isBadXM 388 (isBad388W 338)) sTrue18FwdXorSq_275 = true := by
  apply progDisjointBad_padProg388_437
  apply progDisjoint251_388_plug K_wrapLin_388 _ (by decide)
  dsimp only [sTrue18InnerFwdXorSq_388, progDisjoint251_388]
  refine Bool.and_eq_true _ _ |>.mpr ⟨by decide, ?_⟩
  apply progDisjoint251_388_plug K_xorSq_388 _
    (ctxDisjoint251_truncateCtxB K_xorSq K_xorSq_supportsBelow388
      (ctxDisjoint251_437_buildP57Ctx xorSqSteps (by decide)))
  decide
theorem sTrue18RevXorSq_275_disjoint338 :
    progDisjointBad (isBadXM 388 (isBad388W 338)) sTrue18RevXorSq_275 = true := by
  apply progDisjointBad_padProg388_437
  apply progDisjoint251_388_plug K_wrapLin_388 _ (by decide)
  dsimp only [sTrue18InnerRevXorSq_388, progDisjoint251_388]
  refine Bool.and_eq_true _ _ |>.mpr ⟨?_, by decide⟩
  apply progDisjoint251_388_plug K_xorSq_388 _
    (ctxDisjoint251_truncateCtxB K_xorSq K_xorSq_supportsBelow388
      (ctxDisjoint251_437_buildP57Ctx xorSqSteps (by decide)))
  decide
theorem cliffSupportsBelowB_mono {b₁ b₂ : ℕ} (hb : b₁ ≤ b₂) :
    ∀ (c : CliffProg 437), cliffSupportsBelowB b₁ c = true → cliffSupportsBelowB b₂ c = true
  | .nil, _ => rfl
  | .x q, h => decide_eq_true (Nat.lt_of_lt_of_le (of_decide_eq_true h) hb)
  | .cnot c t _, h => by
      obtain ⟨hc, ht⟩ := Bool.and_eq_true _ _ |>.mp h
      exact Bool.and_eq_true _ _ |>.mpr
        ⟨decide_eq_true (Nat.lt_of_lt_of_le (of_decide_eq_true hc) hb),
          decide_eq_true (Nat.lt_of_lt_of_le (of_decide_eq_true ht) hb)⟩
  | .seq c₁ c₂, h => by
      obtain ⟨h1, h2⟩ := Bool.and_eq_true _ _ |>.mp h
      exact Bool.and_eq_true _ _ |>.mpr
        ⟨cliffSupportsBelowB_mono hb c₁ h1, cliffSupportsBelowB_mono hb c₂ h2⟩
theorem progSupportsBelowB_mono {b₁ b₂ : ℕ} (hb : b₁ ≤ b₂) :
    ∀ (p : TempPhaseProg 437), progSupportsBelowB b₁ p = true → progSupportsBelowB b₂ p = true
  | .nil, _ => rfl
  | .cliff c, h => cliffSupportsBelowB_mono hb c h
  | .z q, h => decide_eq_true (Nat.lt_of_lt_of_le (of_decide_eq_true h) hb)
  | .seq p₁ p₂, h => by
      obtain ⟨h1, h2⟩ := Bool.and_eq_true _ _ |>.mp h
      exact Bool.and_eq_true _ _ |>.mpr
        ⟨progSupportsBelowB_mono hb p₁ h1, progSupportsBelowB_mono hb p₂ h2⟩
  | .tempAnd c₁ c₂ anc _ _ _ body, h => by
      obtain ⟨h1, hr1⟩ := Bool.and_eq_true _ _ |>.mp h
      obtain ⟨h2, hr2⟩ := Bool.and_eq_true _ _ |>.mp hr1
      obtain ⟨h3, hbody⟩ := Bool.and_eq_true _ _ |>.mp hr2
      exact Bool.and_eq_true _ _ |>.mpr
        ⟨decide_eq_true (Nat.lt_of_lt_of_le (of_decide_eq_true h1) hb),
          Bool.and_eq_true _ _ |>.mpr
            ⟨decide_eq_true (Nat.lt_of_lt_of_le (of_decide_eq_true h2) hb),
              Bool.and_eq_true _ _ |>.mpr
                ⟨decide_eq_true (Nat.lt_of_lt_of_le (of_decide_eq_true h3) hb),
                  progSupportsBelowB_mono hb body hbody⟩⟩⟩
/-- Stage-1 `< 388`-wire tail (`magUnpackFromRetQuad51_275` through `sTrue18FwdXorSq_275`). -/
def pStep1XorSqTail_275 : TempPhaseProg 437 :=
  .seq magUnpackFromRetQuad51_275
    (.seq zMag3Ret18_275
      (.seq validStaticFromZ28_275
        (.seq axisStep3_fast321_275 sTrue18FwdXorSq_275)))
/-- `272`-`TempAnd` (`1,088 T`, `-172 T` vs `pStep1Compact113_275`'s `1,260 T`) `< 388`-wire
  Stage-1 forward preparation program. -/
def pStep1XorSq_275 : TempPhaseProg 437 :=
  .seq coinOkXor275 (.seq muAndQuadXor5_275 pStep1XorSqTail_275)
theorem pStep1XorSq_275_count : pStep1XorSq_275.countTempAnd = 272 := by
  have h1 : coinOkXor275.countTempAnd = 2 := by decide
  have h2 := muAndQuadXor5_275_spec.2.1
  have h3 := magUnpackFromRetQuad51_275_spec.2.1
  have h4 := zMag3Ret18_275_countTempAnd
  have h5 := validStaticFromZ28_275_spec.2.1
  have h6 := axisStep3_fast321_275_spec.2.1
  have h7 := sTrue18FwdXorSq_275_countTempAnd
  dsimp only [pStep1XorSq_275, pStep1XorSqTail_275, TempPhaseProg.countTempAnd]
  omega
theorem pStep1XorSq_275_clean_spec :
    ValidCleanRem 437 (437 - 275) pStep1XorSq_275 ∧
      (∀ β, cleanRem 437 (437 - 275) β → pStep1XorSq_275.evalSign β = 0) ∧
      (∀ β, cleanRem 437 (437 - 275) β → cleanRem 437 (437 - 275) (pStep1XorSq_275.evalBits β)) :=
        by
  obtain ⟨hB1, _⟩ := coinOkXor275_spec
  obtain ⟨hB2, _, _⟩ := muAndQuadXor5_275_spec
  obtain ⟨hB3, _, _⟩ := magUnpackFromRetQuad51_275_spec
  obtain ⟨hB4, _, _⟩ := zMag3Ret18_275_spec
  obtain ⟨hB5, _, _⟩ := validStaticFromZ28_275_spec
  obtain ⟨hB6, _, _⟩ := axisStep3_fast321_275_spec
  have hv7 := sTrue18FwdXorSq_275_validCleanRem
  have hs7 : ∀ β, cleanRem 437 (437 - 275) β → sTrue18FwdXorSq_275.evalSign β = 0 :=
    fun β hβ ↦ (sTrue18FwdXorSq_275_spec β (fun u hu ↦ hβ ⟨u.val, by omega⟩ (by dsimp; omega))).1
  have hcl7 : ∀ β, cleanRem 437 (437 - 275) β →
      cleanRem 437 (437 - 275) (sTrue18FwdXorSq_275.evalBits β) := fun β hβ w hw ↦ by
    have hnon := (sTrue18FwdXorSq_275_spec β (fun u hu ↦ hβ ⟨u.val, by
      omega⟩ (by dsimp; omega))).2.2.1
    rw [hnon w (fun ⟨j, hj⟩ ↦ by subst hj; have := sTrue18WDefault216_bounds j; omega)]
    exact hβ w hw
  obtain ⟨hv67, _, hs67, hcl67, _⟩ := seqClean_spec (by decide)
    hB6.1 hv7 hB6.2.1 hs7 hB6.2.2.1 hcl7
  obtain ⟨hv57, _, hs57, hcl57, _⟩ := seqClean_spec (by decide)
    hB5.1 hv67 hB5.2.1 hs67 hB5.2.2.1 hcl67
  obtain ⟨hv47, _, hs47, hcl47, _⟩ := seqClean_spec (by decide)
    hB4.1 hv57 hB4.2.1 hs57 hB4.2.2.1 hcl57
  obtain ⟨hv37, _, hs37, hcl37, _⟩ := seqClean_spec (by decide)
    hB3.1 hv47 hB3.2.1 hs47 hB3.2.2.1 hcl47
  obtain ⟨hv27, _, hs27, hcl27, _⟩ := seqClean_spec (by decide)
    hB2.1 hv37 hB2.2.1 hs37 hB2.2.2.1 hcl37
  obtain ⟨hv17, _, hs17, hcl17, _⟩ := seqClean_spec (by decide)
    hB1.1 hv27 hB1.2.1 hs27 hB1.2.2.1 hcl27
  exact ⟨hv17, hs17, hcl17⟩
theorem pStep1XorSq_275_evalBits_st0 (α : BitAssignment 149) :
    pStep1XorSq_275.evalBits (st0 α) = putQZ (st1 α) := by
  change pStep1XorSq_275.evalBits (st0 α) = st1QZ α
  rw [← pStep1Fast316_ZQuadRet30_evalBits_st0 α]
  obtain ⟨hBC, _⟩ := coinOkXor275_spec
  obtain ⟨hB2, _, hEvM⟩ := muAndQuadXor5_275_spec
  obtain ⟨hB1, hE1⟩ := coinMuXor275_spec
  obtain ⟨hB3, _, _⟩ := magUnpackFromRetQuad60_275_spec
  obtain ⟨hB4, _, _⟩ := zMag3Ret18_275_spec
  obtain ⟨hB5, _, _⟩ := validStaticFromZ28_275_spec
  obtain ⟨hB6, _, hE6⟩ := Slot3Outer2344AndRelayWide.Slot3Exact216TruncBr31.axisStep3_fast_275_spec
  obtain ⟨β₀, hβ₀⟩ := zretStepWitness (st0 α)
  obtain ⟨β₁, hβ₁⟩ := zretStepWitness (coinOkXor275.evalBits β₀)
  obtain ⟨β₂, hβ₂⟩ := zretStepWitness (muAndQuadXor5_275.evalBits β₁)
  obtain ⟨β₃, hβ₃⟩ := zretStepWitness (magUnpackFromRetQuad60_275.evalBits β₂)
  obtain ⟨β₃', hβ₃'⟩ := zretStepWitness (zMag3Ret18_275.evalBits β₃)
  obtain ⟨β₄, hβ₄⟩ := zretStepWitness (validStaticFromZ28_275.evalBits β₃')
  obtain ⟨β₅, hβ₅⟩ :=
    zretStepWitness (Slot3Outer2344AndRelayWide.Slot3Exact216TruncBr31.axisStep3_fast_275.evalBits
    β₄)
  obtain ⟨γ₁, hγ₁⟩ := zretStepWitness (muXor275.evalBits β₁)
  have hγ₁_eq : γ₁ = coinMuXor275.evalBits β₀ := by rw [hγ₁, hβ₁]; rfl
  have hcl₀ : cleanRem 437 (437 - 275) β₀ :=
    hβ₀ ▸ cleanRem_anti (by decide) (padZeroBits149_clean α)
  have hz₀ : ∀ q : Wire 437, 149 ≤ q.val → β₀ q = 0 :=
    fun q hq ↦ by rw [hβ₀]; exact padZeroBits149_clean α q (by omega)
  have hcl₁ : cleanRem 437 (437 - 275) β₁ := hβ₁ ▸ hBC.2.2.1 β₀ hcl₀
  have hcl₂ : cleanRem 437 (437 - 275) β₂ := hβ₂ ▸ hB2.2.2.1 β₁ hcl₁
  have hcl₃ : cleanRem 437 (437 - 275) β₃ := hβ₃ ▸ hB3.2.2.1 β₂ hcl₂
  have hcl₃' : cleanRem 437 (437 - 275) β₃' := hβ₃' ▸ hB4.2.2.1 β₃ hcl₃
  have hcl₄ : cleanRem 437 (437 - 275) β₄ := hβ₄ ▸ hB5.2.2.1 β₃' hcl₃'
  have hcl₅ : cleanRem 437 (437 - 275) β₅ := hβ₅ ▸ hB6.2.2.1 β₄ hcl₄
  have hcl_γ₁ : cleanRem 437 (437 - 275) γ₁ := hγ₁_eq ▸ hB1.2.2.1 β₀ hcl₀
  have hmu0_c : ∀ j : Fin 3, β₁ (muW j) = 0 := fun j ↦ by
    rw [hβ₁, hBC.2.2.2 β₀ hcl₀ (muW j) (wire_ne_of_lt (by dsimp [muW, coinOkW]; omega))]
    exact hz₀ (muW j) (by dsimp [muW]; omega)
  have hp_γ₁ : ∀ q : Wire 437, q.val ≠ 198 → ¬(174 ≤ q.val ∧ q.val < 177) → γ₁ q = β₀ q :=
    fun q hc hm ↦ by
      rw [hγ₁_eq]
      exact hB1.2.2.2 β₀ hcl₀ q (fun h ↦ by
        rcases h with rfl | ⟨j, rfl⟩
        · exact hc rfl
        · exact hm ⟨by dsimp [muW]; omega, by dsimp [muW]; omega⟩)
  have hzQ₁ : ∀ j : Fin 3, γ₁ (retMuQuadW j) = 0 := fun j ↦
    (hp_γ₁ _ (by revert j; decide) (by revert j; decide)).trans (hz₀ _ (by revert j; decide))
  have hEqM : β₂ = putQ3 γ₁ := by
    have h1 := hEvM β₁ hcl₁ hmu0_c
    rw [tempPhaseProg437_seq_evalBits, ← hβ₂, ← hγ₁] at h1
    exact h1.trans (muQuad3Ret3_evalBits_of_zero hcl_γ₁ hzQ₁)
  have hmu_γ₁ : ∀ j : Fin 3, γ₁ (muW j) = if (shellMu3 (getU22 β₀)).testBit j.val then 1 else 0 :=
    by
    intro j
    rw [hγ₁_eq, (hE1 β₀ hcl₀).2 j, hz₀ _ (by dsimp [muW]; omega), zero_add, top7_eq_shellMu3_216 β₀]
  have hmu_val₁ : bitsVal (fun j ↦ γ₁ (muW j)) = shellMu3 (getU22 β₀) :=
    Slot3MicroEngineAux.bitsVal_eq_of_testBit _ _ (lt_trans (shellMu3_lt_seven _) (by
      decide)) hmu_γ₁
  have hu22_eq : (⟨bitsVal (fun i ↦ putQ3 γ₁ (u22WAux i)), bitsVal_lt_two_pow _⟩ : Fin 4194304) =
      getU22 β₀ := by
    ext; dsimp [getU22]
    apply congrArg bitsVal; funext i
    rw [putQ3_of_not_bad (by dsimp [isBadQ3, u22WAux]; exact decide_eq_false (by omega))]
    exact hp_γ₁ _ (by dsimp [u22WAux]; omega) (by dsimp [u22WAux]; omega)
  have hmu_putQ3 : bitsVal (fun j ↦ putQ3 γ₁ (muW j)) =
      shellMu3 ⟨bitsVal (fun i ↦ putQ3 γ₁ (u22WAux i)), bitsVal_lt_two_pow _⟩ := by
    have hfn : (fun j ↦ putQ3 γ₁ (muW j)) = fun j ↦ γ₁ (muW j) :=
      funext fun j ↦ putQ3_of_not_bad (by dsimp [isBadQ3, muW]; exact decide_eq_false (by omega))
    rw [hfn, hu22_eq, hmu_val₁]
  have hmu_lt7 : bitsVal (fun j ↦ putQ3 γ₁ (muW j)) < 7 := by
    rw [hmu_putQ3]; exact shellMu3_lt_seven _
  have hMagEq : magUnpackFromRetQuad51_275.evalBits β₂ = β₃ := by
    rw [hβ₃, hEqM,
      magUnpackFromRetQuad51_275_spec.2.2 (putQ3 γ₁) (cleanRem_putQ3 hcl_γ₁) (invMuQuad3_putQ3 γ₁)
        hmu_putQ3,
      magUnpackFromRetQuad60_275_spec.2.2 (putQ3 γ₁) (cleanRem_putQ3 hcl_γ₁) (invMuQuad3_putQ3 γ₁)
        hmu_lt7]
  have hpPre : ∀ q : Wire 437, 149 ≤ q.val →
      q.val ≠ 198 → ¬(174 ≤ q.val ∧ q.val < 198) → ¬(251 ≤ q.val ∧ q.val < 257) → q.val ≠ 258 →
      β₄ q = 0 := fun q h149 h198 h174 h251 h258 ↦ by
    have e5 : β₄ q = β₃' q := by
      rw [hβ₄]; exact hB5.2.2.2 β₃' hcl₃' q (fun h ↦ h258 (by subst h; rfl))
    have e4 : β₃' q = β₃ q := by
      rw [hβ₃']; exact hB4.2.2.2 β₃ hcl₃ q
        (fun ⟨w, h⟩ ↦ h251 ⟨by
          subst h; dsimp [retZeroMW]; omega, by subst h; dsimp [retZeroMW]; omega⟩)
    have e3 : β₃ q = β₂ q := by
      rw [hβ₃]; exact hB3.2.2.2 β₂ hcl₂ q
        (fun ⟨w, b, h⟩ ↦ h174 ⟨by subst h; dsimp [p57MW]; omega, by subst h; dsimp [p57MW]; omega⟩)
    have e2 : β₂ q = β₁ q := by
      rw [hβ₂]; exact hB2.2.2.2 β₁ hcl₁ q (fun ⟨i, h⟩ ↦ by
        subst h; fin_cases i <;>
          (first | exact h174 ⟨by dsimp [muQuadIn6W, muW]; omega, by dsimp [muQuadIn6W, muW]; omega⟩
                 | exact h251 ⟨by decide, by decide⟩))
    have e1 : β₁ q = β₀ q := by
      rw [hβ₁]; exact hBC.2.2.2 β₀ hcl₀ q (fun h ↦ h198 (by subst h; rfl))
    exact e5.trans (e4.trans (e3.trans (e2.trans (e1.trans (hz₀ q h149)))))
  have hp6 : ∀ q : Wire 437, ¬(150 ≤ q.val ∧ q.val < 174) → β₅ q = β₄ q :=
    fun q hp ↦ by
      rw [hβ₅]; exact hB6.2.2.2 β₄ hcl₄ q
        (fun ⟨w, b, h⟩ ↦ hp ⟨by subst h; dsimp [pBufW]; omega, by subst h; dsimp [pBufW]; omega⟩)
  have hAx5 : ∀ w : Fin 3, InvAxis1 w β₅ := fun w b ↦ by
    have hz : β₄ (pBufW w b) = 0 := hpPre _
      (by dsimp [pBufW]; omega) (by dsimp [pBufW]; omega)
      (by dsimp [pBufW]; omega) (by dsimp [pBufW]; omega) (by dsimp [pBufW]; omega)
    have hproj : (fun j ↦ β₅ (p57ProjW w j)) = fun j ↦ β₄ (p57ProjW w j) :=
      funext fun j ↦ hp6 _ (by dsimp [p57ProjW]; omega)
    have hm : (fun j ↦ β₅ (p57MW w j)) = fun j ↦ β₄ (p57MW w j) :=
      funext fun j ↦ hp6 _ (by dsimp [p57MW]; omega)
    have hs3 : β₅ (p57S3W w) = β₄ (p57S3W w) := hp6 _ (by dsimp [p57S3W]; omega)
    have hev := hE6 β₄ hcl₄ w b
    rw [← hβ₅, hz, zero_add] at hev
    have hval : axisFastVal ⟨bitsVal (fun j ↦ β₄ (p57ProjW w j)), bitsVal_lt_two_pow _⟩
          (bitsVal (fun j ↦ β₄ (p57MW w j))) (β₄ (p57S3W w)).val =
        axisFastVal ⟨bitsVal (fun j ↦ β₅ (p57ProjW w j)), bitsVal_lt_two_pow _⟩
          (bitsVal (fun j ↦ β₅ (p57MW w j))) (β₅ (p57S3W w)).val :=
      congr (congrArg₂ axisFastVal (Fin.ext (congrArg bitsVal hproj.symm))
        (congrArg bitsVal hm.symm)) (congrArg ZMod.val hs3.symm)
    exact hev.trans (congrArg (fun n : ℕ ↦ if n.testBit b.val then (1 : ZMod 2) else 0) hval)
  have hzST5 : ∀ j : Fin 18, β₅ (sTrue18WDefault j) = 0 := fun j ↦ by
    have hb := sTrue18WDefault216_bounds j
    exact (hp6 _ (by omega)).trans
      (hpPre _ (by omega) (by omega) (by omega) (by omega) (by omega))
  rw [pStep1XorSq_275, pStep1XorSqTail_275, pStep1Fast316_ZQuadRet30,
    pStep1Tail294_ZQuadRet30]
  repeat rw [tempPhaseProg437_seq_evalBits]
  rw [← hβ₀, ← hβ₁, ← hβ₂, hMagEq, ← hβ₃, ← hβ₃', ← hβ₄, ← hβ₅]
  rw [axisStep3_fast321_275_spec.2.2 β₄ hcl₄, ← hβ₅]
  exact (sTrue18FwdXorSq_275_eq_orig β₅ hcl₅ (InvWrapLin_of_invAxis β₅ hAx5) hzST5).trans
    (sTrue18FwdPBuf_fast158_275_eq_orig β₅ hcl₅ (InvWrapLin_of_invAxis β₅ hAx5)).symm
theorem pStep1XorSq_275_supports388 :
    progSupportsBelowB 388 pStep1XorSq_275 = true := by
  have h113 := pStep1Compact113_275_supports374
  unfold pStep1Compact113_275 pStep1CompactTail113_275 at h113
  dsimp only [progSupportsBelowB] at h113
  obtain ⟨h1, hr1⟩ := Bool.and_eq_true _ _ |>.mp h113
  obtain ⟨h2, hr2⟩ := Bool.and_eq_true _ _ |>.mp hr1
  obtain ⟨h3, hr3⟩ := Bool.and_eq_true _ _ |>.mp hr2
  obtain ⟨h4, hr4⟩ := Bool.and_eq_true _ _ |>.mp hr3
  obtain ⟨h5, hr5⟩ := Bool.and_eq_true _ _ |>.mp hr4
  obtain ⟨h6, _⟩ := Bool.and_eq_true _ _ |>.mp hr5
  have hle : (374 : ℕ) ≤ 388 := by decide
  dsimp only [pStep1XorSq_275, pStep1XorSqTail_275, progSupportsBelowB]
  rw [progSupportsBelowB_mono hle _ h1,
    progSupportsBelowB_mono hle _ h2,
    progSupportsBelowB_mono hle _ h3,
    progSupportsBelowB_mono hle _ h4,
    progSupportsBelowB_mono hle _ h5,
    progSupportsBelowB_mono hle _ h6,
    sTrue18FwdXorSq_275_supportsBelow388]
  rfl
theorem pStep1XorSq_275_disjoint338 :
    progDisjointBad (isBadXM 388 (isBad388W 338)) pStep1XorSq_275 = true := by
  have h113 := pStep1Compact113_275_disjoint324
  unfold pStep1Compact113_275 pStep1CompactTail113_275 at h113
  dsimp only [progDisjointBad] at h113
  obtain ⟨h1, hr1⟩ := Bool.and_eq_true _ _ |>.mp h113
  obtain ⟨h2, hr2⟩ := Bool.and_eq_true _ _ |>.mp hr1
  obtain ⟨h3, hr3⟩ := Bool.and_eq_true _ _ |>.mp hr2
  obtain ⟨h4, hr4⟩ := Bool.and_eq_true _ _ |>.mp hr3
  obtain ⟨h5, hr5⟩ := Bool.and_eq_true _ _ |>.mp hr4
  obtain ⟨h6, _⟩ := Bool.and_eq_true _ _ |>.mp hr5
  have hAnti : ∀ w : Wire 437,
      isBadXM 388 (isBad388W 338) w = true → isBadXM 374 (isBad374W 324) w = true := by
    intro w hw
    simp only [isBadXM, isBad388W, isBad388, isBad374W, isBad374, Bool.or_eq_true,
      decide_eq_true_eq] at hw ⊢
    omega
  dsimp only [pStep1XorSq_275, pStep1XorSqTail_275, progDisjointBad]
  rw [progDisjointBad_antitone hAnti _ h1,
    progDisjointBad_antitone hAnti _ h2,
    progDisjointBad_antitone hAnti _ h3,
    progDisjointBad_antitone hAnti _ h4,
    progDisjointBad_antitone hAnti _ h5,
    progDisjointBad_antitone hAnti _ h6,
    sTrue18FwdXorSq_275_disjoint338]
  rfl
theorem stepBundleW_step1XorSq {topW : ℕ} (hlo : 338 ≤ topW) (hhi : topW ≤ 388)
    {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)]
    (v : Var) (rCombBase : QRegister 437 n) :
    StepBundleW topW v rCombBase st0 (fun α ↦ putQZ (st1 α)) (fun _ ↦ 0)
      ((pStep1XorSq_275.onRegister
        (rCombBase.compose (permReg (permOfInvol (swap388W topW hlo hhi)
          (validSwapRelayWM_388 hlo hhi).invol)))).toDyn v) := by
  have hpBad : progDisjointBad (isBadXM 388 (isBad388W topW)) pStep1XorSq_275 = true :=
    progDisjointBad_antitone
      (fun w hw ↦ by
        simp only [isBadXM, isBad388W, isBad388, Bool.or_eq_true, decide_eq_true_eq] at hw ⊢
        omega)
      pStep1XorSq_275 pStep1XorSq_275_disjoint338
  have hcl_in : ∀ α, cleanRem 437 (437 - 275) (st0 α) :=
    fun α ↦ cleanRem_anti (by decide) (padZeroBits149_clean α)
  have hz_in : ∀ α w, isBad388W topW w = true → st0 α w = 0 := fun α w hw ↦ by
    simp only [isBad388W, isBad388, decide_eq_true_eq] at hw
    exact padZeroBits149_clean α w (by omega)
  have hz_out : ∀ α w, isBad388W topW w = true → putQZ (st1 α) w = 0 := fun α w hw ↦ by
    simp only [isBad388W, isBad388, decide_eq_true_eq] at hw
    rw [putQZ_eq_of_lt251 (by omega)]
    obtain ⟨hInv1, _, _, hOut1⟩ := n1s_st1_props α
    by_cases h233 : w.val < 233
    · have hw_eq : w = ⟨201 + (w.val - 201), by omega⟩ := Fin.ext (by dsimp; omega)
      rw [hw_eq]
      exact hOut1 ⟨w.val - 201, by omega⟩
    · exact hInv1.hz233 w (by omega) (by omega)
  exact stepBundleW_of_relayWM_static v rCombBase (validSwapRelayWM_388 hlo hhi)
    st0 (fun α ↦ putQZ (st1 α)) (fun _ ↦ 0)
    pStep1XorSq_275 pStep1XorSq_275_supports388 hpBad
    pStep1XorSq_275_clean_spec.1
    (fun α ↦ ⟨hcl_in α, hz_in α⟩)
    (fun α ↦ (pStep1XorSq_275_evalBits_st0 α).symm)
    (fun α ↦ pStep1XorSq_275_clean_spec.2.1 (st0 α) (hcl_in α))
    (fun α ↦ ⟨cleanRem_putQZ (n1s_st1_props α).1.hcl, hz_out α⟩)
theorem stepBundleW_dSTrue18RevXorSq (t : Norm1sTier) (cfg : SpecsAux.SpecMirror.Configuration)
    {topW : ℕ} (hlo : 338 ≤ topW) (hhi : topW ≤ 388)
    {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)]
    (v : Var) (rCombBase : QRegister 437 n) :
    StepBundleW topW v rCombBase
      (putQZ ∘ n1sSt5 t cfg)
      (putQZ ∘ n1sSt6 t cfg)
      (fun _ ↦ 0)
      (dSTrue18RevXorSq_275 v
        (rCombBase.compose (permReg (permOfInvol (swap388W topW hlo hhi)
          (validSwapRelayWM_388 hlo hhi).invol)))) := by
  let hsr := validSwapRelayWM_388 hlo hhi
  let rCombX := rCombBase.compose (permReg (permOfInvol (swap388W topW hlo hhi) hsr.invol))
  let Inv388 : BitAssignment 388 → Prop := fun γ388 ↦
    bitsVal (fun j : Fin 18 ↦ γ388 (sTrue18W388 j)) =
      sTrueRawVal388 (K_wrapLin_388.fwdBits γ388)
  let InvX : BitAssignment 437 → Prop := fun γ ↦ Inv388 (truncAssign388 γ)
  have hBase := dSTrue18RevXorSq_275_realizes_388 v rCombX Inv388 (fun _ _ hi ↦ hi)
  let r388 := rCombX.compose (QRegister.block 0 388 (by decide))
  have hAbsorb : p57CleanDiagProj r388 (388 - 275) (by decide) Inv388 *
      p57RangeDiagProj rCombX 275 388 InvX =
      p57RangeDiagProj rCombX 275 388 InvX := by
    apply matrix_ext_ket; intro β
    rw [mul_mulVec_prog, p57RangeDiagProj, ket_p57DiagProj]
    by_cases hR : (∀ w : Wire 437, 275 ≤ w.val → w.val < 388 → β (rCombX w) = 0) ∧
        InvX (fun idx ↦ β (rCombX idx))
    · rw [ite_eq_left hR, ket_p57CleanDiagProj]
      have hComp : (fun idx : Fin 388 ↦ β (r388 idx)) =
          truncAssign388 (fun idx ↦ β (rCombX idx)) := by
        funext idx
        dsimp only [r388, QRegister.compose_apply, truncAssign388]
        exact congrArg (fun q ↦ β (rCombX q)) (Fin.ext (by simp))
      have hcl388 : cleanRem 388 (388 - 275) (truncAssign388 (fun idx ↦ β (rCombX idx))) :=
        fun u hu ↦ hR.1 ⟨u.val, by omega⟩ (by dsimp; omega) (by dsimp; omega)
      rw [hComp, ite_eq_left ⟨hcl388, hR.2⟩]
    · rw [ite_eq_right hR, Matrix.mulVec_zero]
  have hRealRange : RealizesCleanUnitary v (p57RangeDiagProj rCombX 275 388 InvX)
      (dSTrue18RevXorSq_275 v rCombX)
      (((sTrue18RevXorSq_275.onRegister rCombX).toToffCircuit).eval) :=
    RealizesCleanUnitary.mono_proj
      (p57CleanDiagProj_conjTranspose r388 (388 - 275) (by decide) Inv388)
      (p57DiagProj_conjTranspose rCombX _)
      hAbsorb hBase
  have hpBad : progDisjointBad (isBadXM 388 (isBad388W topW)) sTrue18RevXorSq_275 = true :=
    progDisjointBad_antitone
      (fun w hw ↦ by
        simp only [isBadXM, isBad388W, isBad388, Bool.or_eq_true, decide_eq_true_eq] at hw ⊢
        omega)
      sTrue18RevXorSq_275 sTrue18RevXorSq_275_disjoint338
  let δ_in : BitAssignment 149 → BitAssignment 437 := putQZ ∘ n1sSt5 t cfg
  let δ_out : BitAssignment 149 → BitAssignment 437 := putQZ ∘ n1sSt6 t cfg
  have hcl_in : ∀ α, cleanRem 437 (437 - 275) (δ_in α) :=
    fun α ↦ cleanRem_putQZ (n1s_st5_props t cfg α).1.hcl
  have hz_in : ∀ α w, isBad388W topW w = true → δ_in α w = 0 := fun α w hw ↦ by
    simp only [isBad388W, isBad388, decide_eq_true_eq] at hw
    dsimp only [δ_in, Function.comp_apply]
    rw [putQZ_of_lt251 (by omega)]
    exact (n1s_st5_props t cfg α).2.2.2 w (by omega) (by omega)
  have hTail6 : ∀ α, cleanRem 437 (437 - 275) (n1sSt6 t cfg α) ∧
      (∀ w : Wire 437, 201 ≤ w.val → w.val < 251 → n1sSt6 t cfg α w = 0) := fun α ↦ by
    obtain ⟨hInv5, hPerm5, hAcc5, hOut5⟩ := n1s_st5_props t cfg α
    have hcl6 := (n1s_revTail_eq_st0 (corePerm149_norm1s t cfg α) rfl hInv5 hPerm5 hAcc5 hOut5).1
    refine ⟨hcl6, fun w h1 h2 ↦ ?_⟩
    have hnon6 := (sTrue18RevPBuf275_spec.2.2.2 (n1sSt5 t cfg α) hInv5.hcl).2.1 w
      (fun j hj ↦ by subst hj; have := sTrue18WDefault216_bounds j; omega)
    exact hnon6.trans (hOut5 w h1 (by omega))
  have hcl_out : ∀ α, cleanRem 437 (437 - 275) (δ_out α) :=
    fun α ↦ cleanRem_putQZ (hTail6 α).1
  have hz_out : ∀ α w, isBad388W topW w = true → δ_out α w = 0 := fun α w hw ↦ by
    simp only [isBad388W, isBad388, decide_eq_true_eq] at hw
    dsimp only [δ_out, Function.comp_apply]
    rw [putQZ_of_lt251 (by omega)]
    exact (hTail6 α).2 w (by omega) (by omega)
  have hAx_in : ∀ α (w : Fin 3), InvAxis1 w (δ_in α) := fun α w ↦ by
    have hInv5 := (n1s_st5_props t cfg α).1
    have hAx5 : InvAxis1 w (n1sSt5 t cfg α) := fun b ↦ by
      rw [hInv5.m_val w]; exact hInv5.hpbuf w b
    exact (InvAxis1_congr w
      (fun b ↦ putQZ_of_lt251 (by dsimp [p57ProjW]; omega))
      (fun b ↦ putQZ_of_lt251 (by dsimp [p57MW]; omega))
      (putQZ_of_lt251 (by dsimp [p57S3W]; omega))
      (fun b ↦ putQZ_of_lt251 (by dsimp [pBufW]; omega))).mpr hAx5
  have hVal_in : ∀ α,
      bitsVal (fun j : Fin 18 ↦ δ_in α (sTrue18WDefault j)) = sTrueRawValPBuf (δ_in α) :=
    fun α ↦ by
      have hInv5 := (n1s_st5_props t cfg α).1
      have hst_fn : (fun j : Fin 18 ↦ δ_in α (sTrue18WDefault j)) =
          fun j ↦ n1sSt5 t cfg α (sTrue18WDefault j) := funext fun j ↦ by
        rcases sTrue18WDefault216_bounds j with h1 | h2
        · dsimp only [δ_in, Function.comp_apply]; exact putQZ_of_lt251 (by omega)
        · dsimp only [δ_in, Function.comp_apply]; exact putQZ_of_ge257 (by omega)
      rw [hst_fn, sTrueRawValPBuf_congr_lt201 (γ₁ := δ_in α) (γ₂ := n1sSt5 t cfg α)
        (fun w hw ↦ by dsimp only [δ_in, Function.comp_apply]; exact putQZ_of_lt251 (by omega))]
      exact hInv5.hstrue.trans
        (elecsTrueRawValPBuf_eq (n1sSt5 t cfg α) hInv5.m_val
          (fun w ↦ hInv5.hpbuf w ⟨7, by decide⟩)).symm
  have hOut_eq : ∀ α, δ_out α = sTrue18RevXorSq_275.evalBits (δ_in α) := fun α ↦ by
    have hInv5 := (n1s_st5_props t cfg α).1
    have hcl388_in : cleanRem 388 (388 - 275) (truncAssign388 (δ_in α)) :=
      fun u hu ↦ hcl_in α ⟨u.val, by omega⟩ (by dsimp; omega)
    obtain ⟨_, _, hNonX, hZeroX⟩ := sTrue18RevXorSq_275_spec (δ_in α) hcl388_in
    obtain ⟨_, hNonOrig, hZeroOrig⟩ := sTrue18RevPBuf275_spec.2.2.2 (n1sSt5 t cfg α) hInv5.hcl
    have hVal5 : bitsVal (fun j ↦ n1sSt5 t cfg α (sTrue18WDefault j)) =
        sTrueRawValPBuf (n1sSt5 t cfg α) :=
      hInv5.hstrue.trans
        (elecsTrueRawValPBuf_eq (n1sSt5 t cfg α) hInv5.m_val
          (fun w ↦ hInv5.hpbuf w ⟨7, by decide⟩)).symm
    have hpz6 : ∀ w : Wire 437, 251 ≤ w.val → w.val < 257 →
        δ_out α w = δ_in α w := fun w h251 h257 ↦ by
      have hu22 : ∀ i : Fin 22, n1sSt6 t cfg α (u22WAux i) = n1sSt5 t cfg α (u22WAux i) :=
        fun i ↦ hNonOrig (u22WAux i)
          (fun j hj ↦ by
            have := sTrue18WDefault216_bounds j
            rw [← hj] at this; dsimp [u22WAux] at this; omega)
      have hmu : ∀ k : Fin 3, putZ3 (n1sSt6 t cfg α) (muW k) = putZ3 (n1sSt5 t cfg α) (muW k) :=
        fun k ↦ by
          rw [putZ3_of_not_bad (by dsimp [isBadZ3, muW]; exact decide_eq_false (by omega)),
            putZ3_of_not_bad (by dsimp [isBadZ3, muW]; exact decide_eq_false (by omega))]
          exact hNonOrig (muW k)
            (fun j hj ↦ by
              have := sTrue18WDefault216_bounds j
              rw [← hj] at this; dsimp [muW] at this; omega)
      dsimp only [δ_out, δ_in, Function.comp_apply, putQZ, putQ3]
      by_cases h254 : w.val < 254
      · rw [dite_eq_left ⟨h251, h254⟩, dite_eq_left ⟨h251, h254⟩]
        obtain ⟨hl, hr⟩ := quad3_congr_of_mu hmu ⟨w.val - 251, by omega⟩
        exact congrArg₂ (· * ·) hl hr
      · rw [dite_eq_right (by omega), dite_eq_right (by omega)]
        dsimp only [putZ3]
        rw [dite_eq_left ⟨by omega, h257⟩, dite_eq_left ⟨by omega, h257⟩]
        exact zMagBit_congr_u22 hu22 _
    funext q
    by_cases hq : mutSTrue q
    · obtain ⟨j, rfl⟩ := hq
      have h0_X := hZeroX (InvWrapLin_of_invAxis (δ_in α) (hAx_in α)) (hVal_in α) j
      have h0_6 : δ_out α (sTrue18WDefault j) = 0 := by
        dsimp only [δ_out, Function.comp_apply]
        rcases sTrue18WDefault216_bounds j with h1 | h2
        · rw [putQZ_of_lt251 (by omega)]; exact hZeroOrig hVal5 j
        · rw [putQZ_of_ge257 (by omega)]; exact hZeroOrig hVal5 j
      exact h0_6.trans h0_X.symm
    · rw [hNonX q hq]
      by_cases h251 : 251 ≤ q.val ∧ q.val < 257
      · exact hpz6 q h251.1 h251.2
      · dsimp only [δ_out, δ_in, Function.comp_apply]
        by_cases hlt251 : q.val < 251
        · rw [putQZ_of_lt251 hlt251, putQZ_of_lt251 hlt251]
          exact hNonOrig q (fun j hj ↦ hq ⟨j, hj⟩)
        · rw [putQZ_of_ge257 (by omega), putQZ_of_ge257 (by omega)]
          exact hNonOrig q (fun j hj ↦ hq ⟨j, hj⟩)
  refine stepBundleW_of_relayWM_dyn v rCombBase hsr δ_in δ_out (fun _ ↦ 0)
    sTrue18RevXorSq_275 (dSTrue18RevXorSq_275 v rCombX)
    (dSTrue18RevXorSq_275_preservesStore v rCombX) InvX hRealRange hpBad
    (fun α ↦ ⟨hcl_in α, hz_in α⟩) hOut_eq
    (fun α ↦ (sTrue18RevXorSq_275_spec (δ_in α)
      (fun u hu ↦ hcl_in α ⟨u.val, by omega⟩ (by dsimp; omega))).1)
    (fun α ↦ ⟨hcl_out α, hz_out α⟩)
    (fun γ α hclX hEq ↦ ?_)
  let ξ : BitAssignment 437 := fun w ↦ γ (swap388W topW hlo hhi w)
  have hcl388_ξ : cleanRem 388 (388 - 275) (truncAssign388 ξ) :=
    fun u hu ↦ hclX ⟨u.val, by omega⟩ hu u.isLt
  have hag_good : ∀ w : Wire 437, w.val < 388 → ¬(201 ≤ w.val ∧ w.val < 251) →
      ξ w = δ_in α w := fun w hw388 hnb ↦
    hEq w (by simp only [isBadXM, isBad388W, isBad388, Bool.or_eq_false_iff,
      decide_eq_false_iff_not]; omega)
  have hAx_ξ : ∀ w : Fin 3, InvAxis1 w ξ := fun w ↦
    (InvAxis1_congr w
      (fun b ↦ hag_good _ (by dsimp [p57ProjW]; omega) (by dsimp [p57ProjW]; omega))
      (fun b ↦ hag_good _ (by dsimp [p57MW]; omega) (by dsimp [p57MW]; omega))
      (hag_good _ (by dsimp [p57S3W]; omega) (by dsimp [p57S3W]; omega))
      (fun b ↦ hag_good _ (by dsimp [pBufW]; omega) (by dsimp [pBufW]; omega))).mpr
        (hAx_in α w)
  have hst_ξ : bitsVal (fun j : Fin 18 ↦ truncAssign388 ξ (sTrue18W388 j)) =
      bitsVal (fun j : Fin 18 ↦ δ_in α (sTrue18WDefault j)) :=
    congrArg bitsVal (funext fun j ↦ by
      have hb := sTrue18WDefault216_bounds j
      have hlt : (sTrue18WDefault j).val < 388 := by omega
      have hnb : ¬(201 ≤ (sTrue18WDefault j).val ∧ (sTrue18WDefault j).val < 251) := by omega
      have hj : (sTrue18W388 j : Wire 388) = ⟨(sTrue18WDefault j).val, hlt⟩ := Fin.ext rfl
      rw [hj]
      exact hag_good (sTrue18WDefault j) hlt hnb)
  change bitsVal (fun j : Fin 18 ↦ truncAssign388 ξ (sTrue18W388 j)) =
    sTrueRawVal388 (K_wrapLin_388.fwdBits (truncAssign388 ξ))
  rw [hst_ξ, hVal_in α,
    sTrueRawVal388_eq_sTrueRawValPBuf hcl388_ξ (InvWrapLin_of_invAxis ξ hAx_ξ)]
  exact (sTrueRawValPBuf_congr_lt201 (fun w hw ↦ hag_good w (by omega) (by omega))).symm
end
end ConfigK4
end FastSTrue18XorSq
end
end FastSTrue18XorSq

noncomputable section GF8Code18Core

section
set_option backward.isDefEq.respectTransparency false
namespace GF8Code18Guard19300
section ConfigGF8Core
set_option maxRecDepth 262144
set_option exponentiation.threshold 256
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup
local instance (priority := 1000000) instNeZeroTwoPowK7 (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩
open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt SpecsAux
open SpecsAux.SpecMirror
open GridGuard654ReflAux hiding disjointWires_concat_left
open Slots01AndGridGuardBridge (elecAxisWord6 projAxisWord8)
open SixSlotEndpointJunctionBridge (gridValidBool gridValidBool_eq_true_iff
  isGridState_iff_axisWords_ne_minInt)
/-- Packed `11,772`-bit GMP `Nat` storing all `654` 18-bit columns at `18`-bit stride (`O(1)`
  shift). -/
def colsGF8Packed : ℕ :=
  0xd8ceed98f25f562bff70db734492a399ef79de9aaee7454cb9a995621f48ba3c1aa6d6afd95ce4ba2535d63e79a6698f09cb8189a1af273fed7366cd4b6ea44a7b5bc5297ae57c7539d7cbcd39ef7d6fa63fa2e12e7d27c442a3177a4351e912a2dfd86e4230fe4e2d6d092d3181794064f007c52a669d57de60bb1478430cf0bce98aecc32c605b21ec9439fc151b64f9bb7393ff9825c43f4686d442cf7875e6165efc25378af3827f592de5dda726aff21fb23dc94691c1dbcc4251445462062347348234c3056082e954817290663618a16218ea0e0b921076d04ffb0e895283cdb03ad0da247ee404fdb139b2d9b56c89828fe8624e204b214bf015a51baebd55653475eba73ecc6159d54b850deee145487be8e547df0ddf223331835f82f9a167a3d7774f0bd26a6ed543f98cd83a458b33a2742bc30948a328322b85f780e790f5991e5c9a726c98f8fca6127a8b33e96bcb7519cc7c74f51753046bd1f4a4555e0ed06d6c66e40e450ce9e98b8d3b26d7dd6a2aa4e3fb8db3c1b8a0491eb7cd62be9d49127f66f9ff6ab1ea3b0bde774aead771fe7b09c634a350950ab4a629560f4fc0a86da526defe48f6ba849a63f5506cc5677f4eaa3d6ccac8d78e7296477951a33c5de147477e54bccfb39003a801a6001e10c28838c086391a9a8729f13728c969a97513656d022da067ec4424a18d90c3f839f987dc435ce02af3143538d19ad573dae8bf3dc5813b10d9e86c81fb91dc7c5cf54a4bb6fe16f6577f7952399edf50c2dc21631462a9b69df6dd44948ed5cadabf64c864890c9b44b7f0529446f20a466d8d4fd429ba7d92351250a6de8e9906f520f7244d739a688caafd4209d14558413125cb52cc9d8d6fdcfbddcd234617f885360fa90ee559ac9defcc6ec1bc10250e36e1154dbeef8d3efa0b7b0e94216dfe824708273412796ccae918cb732edb95a48e56d94900efc0ca4007dda08ab867a1e73faafaf7e271d036b0026701be2ae607e6a0cabc23397045760df02f2b12bc81ca2ff4f923ef91556f91a476edcb75f5f4e332a2b95f8af2425f20670c92e3c9186494a973f78dda3bc5b1304b98259f54f6fbd09d1ab5237326f73670dd2c015740ecb03668926e6edee4159f465de1e5dc94284a022d238a8247904d986cf4f9d6b39cf46c634b683e42156ef86ef95ee2ee159eef1a5577d3eb13b947559161ef363472085123133b9f968b7d524efe4949db29387ec42a9c8e56d29aee517877cb0bc341c068447b91cbb359d2f95ab4257616e90696990edc95fd4876f41a46842552d8d7a426b207f4b50ec9821da8152f44d941ad7a5fa55f35eb8ab43d058284c140fdd0cddaa9e879c129286f682d2757077e21b9cc54939a499f24c4cf9f0b96634b10427e58c4ca0b7c014f006ec011a60b83059843a2343dd5742fb5712ec6a75bbeb157d27a8f69ca90b4fddf550ae635252865e90cef4450304a105dc50f51144c5f5f08a2880144008e002e95c6ab355cbe0f9e04d7015341f1aca819e60fad2b3ee5e1872ed407ef468b70d13189f940b7e8e9d3a15bc3e7ad576a096d459f90464010c8144a0795f16b303f2a12487affb592571290de921e7b02a2e1bcc8ffe42d20f9b0d2a4157e1866efbe6ebaa0ba3c79f40cb862426cd8d5c81fb707db40c908aae6fc86d5f44998fc114c82a6517252e969d192bb780a7700a2807a14e03ea2347f0c47a670f7e8529133436a6afe61902a09170d83407b4c1bfa8291fbe7751c7accb5a066da0e6d8c89c7d67aa72b0af2c629ea0f67a23e050701c56061ee018ec080f030920b9243b6d83c116b0c49471b29d3cd631c766f925e5ffcaf6cbc570cf420d6a8be8295c3db908da7986bde3b51056f9deccb522ea91fc0c364209716587e65abce3dcd699f929da94c6a32f4e64667e25e192569b3954be11e8852af0f7626bd0333a398b94277e82f52162f08d6e1eb18519bd1ae2ce5f8d3a472b4a267fbc5c471a70c2b011d57c58750ee4feb28cfae119e07b1e149d88ddc00325026c804d91cedc4c94157f6d4c6fcc0e4d41
/-- Raw `Nat`-indexed 18-bit column lookup (`< 2^18`). -/
def colsGF8Nat (f : ℕ) : ℕ := (colsGF8Packed >>> (18 * f)) % 262144
/-- The `654` 18-bit parity-check columns of `[218, 212, 4]_{GF(8)}` with optimized `GL(3, 2)`
  bases. -/
def colsGF8_654 (f : Fin 654) : ℕ := colsGF8Nat f.val
theorem colsGF8Nat_lt (k : ℕ) : colsGF8Nat k < 2 ^ 18 := Nat.mod_lt _ (by decide)
/-- Parity-check matrix bit `H_{r, f}` (`r : Fin 18`, `f : Fin 654`). -/
def gf8Code18Bit (r : Fin 18) (f : Fin 654) : Bool := (colsGF8_654 f).testBit r.val
/-- `r`-th `GF(2)` syndrome bit (`r : Fin 18`) of a 654-field badness vector `bad : Fin 654 →
  Bool`. -/
def gf8SynBitOfBad (bad : Fin 654 → Bool) (r : Fin 18) : Bool :=
  (List.finRange 654).foldr (fun f acc ↦ xor (bad f && gf8Code18Bit r f) acc) false
/-- Column parity `∑_{r < 18} meas r · H_{r, f}` (`f : Fin 654`) after X-basis syndrome
  measurement. -/
def gf8Col18Parity (meas : Fin 18 → Bool) (f : Fin 654) : Bool :=
  (List.finRange 18).foldr (fun r acc ↦ xor (meas r && gf8Code18Bit r f) acc) false
/-- `18`-bit burst contribution of electron `i : Fin 218` for 3-bit badness mask `m : Fin 8`. -/
def elecMaskSyn18 (i : Fin 218) (m : Fin 8) : ℕ := ((if m.val.testBit 0 then colsGF8Nat (3 *
    i.val) else 0) ^^^ (if m.val.testBit 1 then colsGF8Nat (3 * i.val + 1) else 0)) ^^^
    (if m.val.testBit 2 then colsGF8Nat (3 * i.val + 2) else 0)
/-- `18`-bit syndrome contribution of electron `i : Fin 218` on system state `x`. -/
def elecSyn18 (x : Fin (2 ^ SpecsAux.SpecMirror.systemQubits)) (i : Fin
    SpecsAux.SpecMirror.numElectrons) : ℕ :=
  ((if (elecAxisWord6 x i 0).val = 32 then colsGF8Nat (3 * i.val) else 0) ^^^
   (if (elecAxisWord6 x i 1).val = 32 then colsGF8Nat (3 * i.val + 1) else 0)) ^^^
   (if (elecAxisWord6 x i 2).val = 32 then colsGF8Nat (3 * i.val + 2) else 0)
/-- Full `18`-bit electron syndrome `⊕_{i < 218} elecSyn18 x i`. -/
def fullSyndrome18 (x : Fin (2 ^ SpecsAux.SpecMirror.systemQubits)) : ℕ :=
  (List.finRange SpecsAux.SpecMirror.numElectrons).foldr (fun i acc ↦ elecSyn18 x i ^^^ acc) 0
/-- `[218, 212, 4]_{GF(8)}` 18-bit syndrome + 3-axis projectile validity predicate on
  `systemQubits`. -/
def bValidGF8Code18 (x : Fin (2 ^ SpecsAux.SpecMirror.systemQubits)) : Bool :=
  decide (fullSyndrome18 x = 0 ∧ ∀ w : Fin 3, (projAxisWord8 x w).val ≠ 128)
def gf8Red3 (p : ℕ) : ℕ := if p.testBit 3 then p ^^^ 11 else p
def gf8Red4 (p : ℕ) : ℕ := gf8Red3 (if p.testBit 4 then p ^^^ 22 else p)
/-- Multiplication in `GF(8) = 𝔽₂[x]/(x³ + x + 1)` (`0b1011 = 11`). -/
def gf8MulLimb (s x : Fin 8) : Fin 8 := ⟨(gf8Red4 ((if s.val.testBit 0 then x.val else 0) ^^^
    (if s.val.testBit 1 then x.val <<< 1 else 0) ^^^ (if s.val.testBit 2 then x.val <<< 2 else
    0))) % 8, Nat.mod_lt _ (by decide)⟩
theorem gf8MulLimb_xor_check :
    (List.finRange 8).all (fun s ↦
      (List.finRange 8).all (fun a ↦
        (List.finRange 8).all (fun b ↦
          decide ((gf8MulLimb s ⟨(a.val ^^^ b.val) % 8, Nat.mod_lt _ (by decide)⟩).val =
            ((gf8MulLimb s a).val ^^^ (gf8MulLimb s b).val))))) = true := by decide
theorem gf8MulLimb_xor (s a b : Fin 8) :
    (gf8MulLimb s ⟨(a.val ^^^ b.val) % 8, Nat.mod_lt _ (by decide)⟩).val =
      ((gf8MulLimb s a).val ^^^ (gf8MulLimb s b).val) := by
  have h1 := List.all_eq_true.mp gf8MulLimb_xor_check s (List.mem_finRange s)
  have h2 := List.all_eq_true.mp h1 a (List.mem_finRange a)
  have h3 := List.all_eq_true.mp h2 b (List.mem_finRange b)
  exact of_decide_eq_true h3
/-- Extract octal coordinate `j` (`3`-bit slice `[3*j .. 3*j+2]`) of `v : ℕ`. -/
def gf8Limb (v j : ℕ) : Fin 8 := ⟨(v / 2 ^ (3 * j)) % 8, Nat.mod_lt _ (by decide)⟩
/-- Componentwise `GF(8)` scalar multiplication on `GF(8)^6` (`18`-bit `Nat`). -/
def gf8ScaleVec (s : Fin 8) (v : ℕ) : ℕ := (gf8MulLimb s (gf8Limb v 0)).val + 8 * ((gf8MulLimb
    s (gf8Limb v 1)).val + 8 * ((gf8MulLimb s (gf8Limb v 2)).val + 8 * ((gf8MulLimb s (gf8Limb
    v 3)).val + 8 * ((gf8MulLimb s (gf8Limb v 4)).val + 8 * (gf8MulLimb s (gf8Limb v
    5)).val))))
theorem add_two_pow_mul_testBit (d : ℕ) {a B : ℕ} (ha : a < 2 ^ d) (k : ℕ) :
    (a + 2 ^ d * B).testBit k = if k < d then a.testBit k else B.testBit (k - d) := by
  split_ifs with hk
  · have hmod : (a + 2 ^ d * B) % 2 ^ d = a := by
      rw [Nat.mul_comm (2 ^ d) B, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt ha]
    have htb := congrArg (fun n ↦ n.testBit k) hmod
    rw [Nat.testBit_mod_two_pow] at htb
    simpa [hk] using htb
  · have hdiv : (a + 2 ^ d * B) / 2 ^ d = B := by
      rw [Nat.add_mul_div_left _ _ (Nat.two_pow_pos d), Nat.div_eq_of_lt ha, zero_add]
    have htb := congrArg (fun n ↦ n.testBit (k - d)) hdiv
    rw [Nat.testBit_div_two_pow] at htb
    simpa [show d + (k - d) = k by omega, show k - d + d = k by omega] using htb
theorem add_two_pow_mul_xor (d : ℕ) {a₁ a₂ B₁ B₂ : ℕ} (ha₁ : a₁ < 2 ^ d) (ha₂ : a₂ < 2 ^ d) :
    ((a₁ + 2 ^ d * B₁) ^^^ (a₂ + 2 ^ d * B₂)) = (a₁ ^^^ a₂) + 2 ^ d * (B₁ ^^^ B₂) := by
  have ha12 : (a₁ ^^^ a₂) < 2 ^ d := Nat.xor_lt_two_pow ha₁ ha₂
  apply Nat.eq_of_testBit_eq
  intro k
  rw [Nat.testBit_xor, add_two_pow_mul_testBit d ha₁, add_two_pow_mul_testBit d ha₂,
      add_two_pow_mul_testBit d ha12]
  split_ifs <;> simp [Nat.testBit_xor]
theorem add_eight_mul_xor {a₁ a₂ B₁ B₂ : ℕ} (ha₁ : a₁ < 8) (ha₂ : a₂ < 8) :
    ((a₁ + 8 * B₁) ^^^ (a₂ + 8 * B₂)) = (a₁ ^^^ a₂) + 8 * (B₁ ^^^ B₂) :=
  add_two_pow_mul_xor 3 ha₁ ha₂
theorem gf8Limb_xor (u v j : ℕ) :
    gf8Limb (u ^^^ v) j = ⟨((gf8Limb u j).val ^^^ (gf8Limb v j).val) % 8, Nat.mod_lt _ (by
      decide)⟩ := by
  ext
  dsimp only [gf8Limb]
  have hmod : ∀ w : ℕ, ((w / 2 ^ (3 * j)) % 8) < 2 ^ 3 := fun w ↦ Nat.mod_lt _ (by decide)
  have hxor_lt : (((u / 2 ^ (3 * j)) % 8) ^^^ ((v / 2 ^ (3 * j)) % 8)) < 8 :=
    Nat.xor_lt_two_pow (hmod u) (hmod v)
  rw [Nat.mod_eq_of_lt hxor_lt]
  apply Nat.eq_of_testBit_eq
  intro b
  rw [Nat.testBit_xor]
  by_cases hb : b < 3
  · have htb : ∀ w : ℕ, ((w / 2 ^ (3 * j)) % 8).testBit b = w.testBit (3 * j + b) := by
      intro w
      change ((w / 2 ^ (3 * j)) % 2 ^ 3).testBit b = _
      rw [Nat.testBit_mod_two_pow, decide_eq_true hb, Bool.true_and, Nat.testBit_div_two_pow]
      simp [Nat.add_comm]
    rw [htb (u ^^^ v), htb u, htb v, Nat.testBit_xor]
  · have hlt8 : ∀ w : ℕ, (w / 2 ^ (3 * j)) % 8 < 2 ^ b := fun w ↦
      Nat.lt_of_lt_of_le (hmod w) (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 3 ≤ b))
    rw [Nat.testBit_lt_two_pow (hlt8 (u ^^^ v)), Nat.testBit_lt_two_pow (hlt8 u),
        Nat.testBit_lt_two_pow (hlt8 v)]
    rfl
theorem gf8ScaleVec_xor (s : Fin 8) (u v : ℕ) :
    gf8ScaleVec s (u ^^^ v) = gf8ScaleVec s u ^^^ gf8ScaleVec s v := by
  unfold gf8ScaleVec
  simp only [gf8Limb_xor, gf8MulLimb_xor]
  have hlt : ∀ a : Fin 8, (gf8MulLimb s a).val < 8 := fun a ↦ (gf8MulLimb s a).isLt
  rw[add_eight_mul_xor (hlt _) (hlt _), add_eight_mul_xor (hlt _) (hlt _),
      add_eight_mul_xor (hlt _) (hlt _), add_eight_mul_xor (hlt _) (hlt _),
      add_eight_mul_xor (hlt _) (hlt _)]
/-- Flat `262,144`-bit (`2^18`) GMP `Nat` bitmap encoding the `1,526`-element
single-electron burst-syndrome set in `{0 .. 2^18 - 1}`. -/
def span18Bitmap : ℕ :=
  0x80000000000200000008000800000000000000004000080000000000000000000004000000000000000002000000000000000000000000000004010000000000000000000000000000000000040000000000000002000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000400000000000000080000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000008000000400000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000004000000400000000000000000000000000000400000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000800000000000000000000000001000000000000000000000000000000000000000000000000000000000000010000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000002000000000000000000004000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000002000000000000000000000000880000000008000000000008001000000000000000000000000000000000000000000080000000000000000000000020000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000004000000040000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000004000080000002000000100000000000000002000000000000000000000800000000000000000000010000a0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000400000000000000000800000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000080000000000000000000800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001000040000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000000000000000000000000040000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000020000000000000100000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000004020000000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000008000000000008000000000000000000000000000000000000000000002000000000000000000000000000000000000020000000000000000000000000001000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000008000000000000000000000000050000000000000000000000000000000000000000001000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000200000008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001010000000000000000000000040000000000000000000000000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000010000000400000000000000000002000000000001000000000000000000000000000000000000000000000000000400000200000000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000000004000000000000000000040000000000000000002000000000000000000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000002000000000000000000000000000000000000000000000000000000000008000000000000400000000000000200000000000000000000000000000020000000000000020000000000000000000000000000010000000100000000000040020000000100000000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000002000000000000000400000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000040000000000000000000000000020000000000004000000000000000000000000000000000000000000000000000002000000000000000000000000000000000080000000000000000000000000000000000000000000400000000000100000000000000000000000000000008000000800000000000000400000000008000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000400000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000081000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000040000000000000200000000000000000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000040000000000000000020000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000800000084000000000000000000000000000000000000000000000000000000000001000000000000000000000000000002000000000000000000000000010000000000000000000000000000000000200000000000000000000400000000000000000000000000008000000000000000000000000000000000000200000000000000000080000000000000000000000000000000000000000000000000000001000000000000000000000100000000000000000000000000000000000000000020000000000000000000000000100000000000000000000000002000000000000000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000400000000000009000000000000480000000000000010000000000200000000000000000000000000800000000000000000000001000000000000000000000000000000000000000000000000000008000000000000000000004002000000000000000000000000000000000000000004000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000020000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000010000200000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000010000000000000000000000000000000000001000000000000000000000008000000000000000000800000000000000000000000000000000000000000000000000000000000000000000000000001000800000000100000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000400000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000030000000000000008000000000000000000400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000100000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000002000000000000000000000000000000000000000000000000040000000002000000000000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000001000000000020004000000000000000000000000200000000000000000000000000081000000000000000001000001000000000000000000000000000000000002000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000000000100000000100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000200002000000000100000000000000000200000000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000800000008000000000000000000000000000000000002000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000010000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000004100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000400000000800000000000000000040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000080000000000800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000010000040000800000000000008000000000000000000000080000000000000000000001000002000000000000000000000000000000000000000000000000000000000000010000000000000000000000000200000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000020000000000000000020000000000000000000000000000000000001000000000000000100010000000000008000000000000000000000000800000000200000000000000000000200000000000000000200000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000001000200000000000000000000000000000000000000000000000100000000000000000000000000002000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000002000000000000000000200000000080000000000000000000000000000000000000000000000000000000000000000000000001000000000000020000000000000002000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000200000000000000000000000800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000040000000000000000000000000000800000000000000000000000000000000000000000000000000200000000000004000000101000000000000000000000000000000000000000000000000000000000000000000000500000000400000000000000004000000000008000000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000800000000800000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000001000000000000002000000000000001000000000000000000000000000000000000000000000000000001000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000004040000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000040004000000000000000000000000000000000000100003000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000040000040000000000000000000000000000800000000000000000000000000000000002000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000020000000000000000040000000000000000000000000800000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000000000000000000000000002000000000000000080020000000000000000000000004000000000080000040000000000000000080000000000001000000000000000001000000000000000000000000000000000000000000800000000020000000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000800000000000000000000011000000000000000000000000000040000000000000000000000400000000000000000200000000000018000000200000000000000000000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000040000000000000000000000000000002000000000000000000008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000010000000000000000020000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000008000000000000000000000010000000000020000000000000000000000000020000000000000000000000200000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000008001000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000200000000000004000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000040000000000000000000040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000080000000000000000000000060000000000000000000000000000000000000000000000000200000000008000000000000000000000000000000400000400000000000000000020000000000000000000000000002000000000000080000000000000010000000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000400000000000000000000001001000000000000000000001000000000000000000000000000000000000000000000001000000000000000000000000000000000020000000000000000000000100000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000010000000000000000000004000000000000000000000000000800000040000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000002000000000000000001000001000000000000000000000000008000040000000000000000000000000100000000040000000000000000000000000000000000000000000000000080000000000400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000400000000000000000100000000000000010010000000000400000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000800000004000000000000000000000000000000000004000000000400000000000000010002000000000040000000000000400000000000000000000000000000000008000000000000000000000000000000000000000000000100000800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000000000000000080000000000000001000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000100000000000000100000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002000000000000000000020000000000000000000000000000000000000000000000000000000000000000000000000000200000000400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000804080000000000000080000000000000000000000000000400000000000000000000000000000000020000000008000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000008000000000000000000020000100000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000008000000000000010000000000000000002000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001000000000000000000200000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000004000000000000000100000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000011000008080000000000000000000000000000000000000000000000000000000000000020000020000000000000000000000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000004000000000000000800000000000020000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000800080000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000800000000002000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000021000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000020400080000000000000000000000008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002000000000000000000080000000000000000000000000000000000000000080000000000000000000000004000000000000000000000000000000000000000008000000000000000000000000000020000000000000000000000000000000000000000000000000000000000040000000000400000000000000000000000000000000000000000000000000000000000000000020000000000800000000000000000000000400000020000000000000044000000000000000000000000000000000000000000000000000008000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000800000000000000000020000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000800000000000000000000000024000000000010000000000000000000000400000000000000000000000200000000000000040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000008000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001000000000000000010000000000000000000000000004000000000000000100000000000000000000000000000000000000000000000000000000000000000000000000000000000008000000000000000000000000800000000000001000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000040000000000000000000000100000000000000000000000000000000000000000000001020000000000000000000000000000000000000000008001000000000000000000040000000000004000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000800000000000000000000000100000000000000000080000000000000000000000000004000000000000000000c0000000000000000020000000410000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000020000000000000000040020000000000000001000000000000000000000000004000002000004000000000000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000800008000000000000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000800000000000000000040000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000080000000000000000000000080000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000200021000000000040000000000000800000000000000000020000000000000000000000000000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001100000000000000000000000000000000000000000400000000000000000008000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000004000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000040000000000000000000000400000000000020000000000000000000000000200000000000000000000002000002000000000008100000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010001000000000000000000000400000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000000008040000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000004000000000000000010000000000000000000000200020000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000004000000800000000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000001000000000000000000000000000000000200000000000020000000000000000000000000000000000000000000000000000000000000000000000000000000020000000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000008000000000000000020002000000000000000000004000000010000000000000000000000400000000000002000040000000000000000000000000000000000000000000000000000000020000000000000000000000000000008000000000000000000000000000000000000000000000010000000000000000000000000000000000008000000000000000000000000000000000000000000000000000010080000000400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000000000000001000000000000001000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000001000000000000000000000000000000000020000000000000000000000000000000020000000000000000000800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000002000008010000000000000000000000008000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000002000000000000000000000000000000000100000000000000000080000000000000042000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000008000000000000000000000000000200000000000000000100000000000000000000000000000000000200000000000000000000000000002000200000000000012000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000008008000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000080000000000000020000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000200000000000000040000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000080000000040000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000002000400000000000000000000000000000000800000000000000000000040000000000000000000000000000000000000400000000000000000040000000000400000010000000000000000000000000000000000000000000000000000004000080000000000000000000100000000010000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000004000000000004000000000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000001000080000000000000000000000000000000010000800000000000000000000000000000000000000000000000000000080000000080000000000000000000800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000008000004000000000000000000000000000000000000000000000000000000000000000000000000108000000000000000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000020000000000000100000000000000000000000000000000000000000000000000048000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000002000000000000000004000000000000000004000000000001000000000000000000600000000000000000000000000000000000000030080000000000000000000200000000000000000000000000000000000000000000000000000000000008000000000000000000000000000004000000000000000000000010000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000200000000000000000200000000000000400000000000000000000000000000000010000000040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000040000000000000000040000000000081000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000009000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000400000000000000000001000000000000000000000000000008000000000000000000000000000000000000000000400000000000000000000000000000000040000000020000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000400000000000000000000000000000000000000000000000004000000000000000000000000000000080000040000000000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000040000000000000000000000000000000840000000200000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000004400001000000000000020000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000100000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002000000000000000000040000000000000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000008000000000000000000000000000000000000001000000002001000000000000400040000000000000000000000001000000040000000000040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000002000000000020000000000000000000000000000000000000000000000000000000000000000000000000000020000000400000000000000000000000200000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000040000000400000008000000000000000000000000000c000000000000000000000000000000000000000000020000000040000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000008000000000000000000000000000000000000000000000000000200000000000000000000000000000000200000000000000000000004000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000100000000000000000100000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000020000000000000000000000000000000000040000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000000000000004000000000001000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000100000000000002000000000000000000000000000000000000000000000000000000000000000000000000000000000200000000001000000000000000000000080000000000000002000000000000000000000000000002000000000000080000008000000000000000000000000000000000000000000000000000000000000100000000004000400000004000000000000000080000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000000000100000000000100000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000100000000000080000010000000000000800000400000000000000000000000000000000000000001010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000008000000000000010000000000000000000000000000000000000000000100000000000000000000080000000000000000000000004000000000000000000000000000020000000000000000000000000000000000000008000000000000000000000000000000000000120000000000000000000000000000000000000000000000000000000000000000100008000000000000000200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000008000000000000000000000008000000000000000000000000000000000000000200000000000000000000000000000000000000020000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000100000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000020040001000000000000000000000000000000000000000000000000000000000000000000000000000000000020200000000000000000000000000000000000000000400000000000000000000000000000000000000000000210000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000100000100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000800000008000000000000000000000000000000008000000000100000000000000000000000000000000002020000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000500000000000080000000000020000000000000000000000000000000000000000200000000000000140000000000000000000000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000200000000000010040000000000000000000000000800000000000000000000000000000000000010000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000020000000000000080000000010000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000100000000000000000000001000000000000400000000200000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000040400000000000000000000000000000000000000000000000000000000000000000000000008000000000000000041000000000000000000000000000000000000000000000000000000000000800000800000000000000000000000200000000000000000000000000000000100000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000000000001000000200000000000000000000000000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000002000000000000000000000000100000000000008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000020000000000000000000100000000000000000000000000000000000000000000000000000000000000808000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000401000000000002000000000000000000000000000000002000000200000000000000004000000000000000000000000000002800000000000000000020000000000000000000000000008000400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000010000000000000000000000040000000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001000000000100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000004000000000100000000000000000000040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000080000000000020000004000000000000000000000000000000000080000000000000000001000000000000000000000000000000000000000000000000000400000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000020000080100000000000001000008000000000001000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000000000000000800000000000000080000000000000000000000000001000000000000004000000100000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000001000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000020002000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000000000000000000000040000000080000000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000200000000000000000000000000000000000000080000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000020000000000000000100000000000000000000000001000002000010000000080000000000000000000000000000000002800000400000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002000000000000000040000000000000000080000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000000040000002000000200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000010000000000000000000000000002000000000000000000000000080000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000500000000000000000000000000000000000000000000000000000000000000000000020010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000020000000000000000002000000000000000000001000000000000000000000000000000800000000000000000000002000000000000000000000200000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000200000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010000000020000000000000000002000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000000100000000000000002000000100000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000202000000000000000000000000000020000000000200000000008000400000000400000000000000000000000000000000000000000080000000000000000400000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000001000040000000000000000000000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000010000000000000000000000000000000000000000000000004000000000000010000000000000000000000000000000000000000000000000800000000000000000000000000000800000000000000000000000008000000000000004000000000000000000000000000000202000000000000000000000000000000000000024000000000000000000001000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000080000000000000100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000008000000000200000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000000000000000000000020000000000000000000000800000000000000000002000000000000000000000000000000000000000000000100000000000000000000400000000000000000400000000000000000000000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000010000000010000000000000000000000000000000000000000000000000000000000000000000001000000000000000000800000000000000000000000000000000000000000220000000000000000000000000800008000000000000000000021000000000000000000040000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000000000000800000000000000000000004000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000080000000008000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000100000000000000000000000000000000000000000000000000000000008000000000001000000000000000000000000080000000000010000000000010000000000000000000000000400000000010000000000000000002000000010100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000200000000000000000000000800000100000000000000800000000000000000000100000000000000020000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000010000000000000000000000000001000000000100000000000000000000100000000000000000000000000000000000000000000000000000000000000000000000000000000000000002000002000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000090000000000008000000040000000000040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000200000040000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000200000000000400000004000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010000000000004000000000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000040000000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000400000820000000000000000000000000000000000020000000000000080000080000000000000000000000000000004000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002000000000000000000000002000200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002004000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000400000000000000000000000008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000020080000000200000000000000000000000000000000000000080000000000000040000000000000000000000200000000000000000000000000000000000000000000000000000000000000000000000000000000000030000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000100000000000040000000000000000000000000000000020000000000000000000000000000000000000800000000000000000000010000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000080000000040000000000000000000000000000000000800000400000000000000000000000000000000000000000000000000000000000400000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000002000800000000000800000000000000000000000000000000000000000000000000000000000000000000200002000000000400020000000000000000000000000000020000000000000000000000000000000000008000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000080000000000000000000000000000000000040000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000090000000004000000000000000000000040000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000080000000040000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000002000000000000000000000000000000000000000100000000000000000000000000000000000800000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000040004000000000080010000000000000000000000000000000000080000000000000000000000000020000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000000000000200080000000000000000000000000000000000000000000000000000000000000000000000010000000000000000800000000010000000800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000100000000000000000000000000000040000000000000000000000000000000000000000020000000000008000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000001000000000000000000200000808000000000800000000000000000000000000000000800000000000000000000000002100000000000000000000000000010000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000400000000000000000000000000000000000208000000000000000000000000000000000000000000000000000000000001000000000000000000000000100000000000000000008000000000000000000000000000008000000000000000000000100000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000000000000000000000010000000000400010000000000004000000000000000a00000000000000000000008000000000000020000000000000000000010008100000000000000000000000000000000000000000000000000004000000000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000800000010000000000000000000001000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000500000000000000000000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000080000000000000000000000004000000000000000000000000000000000000000000000000000800000000000000040000000000000000200000000020000000000000000000400000000080000000001800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000010000000000000000000000000000000000008000000000000000000000000000000000000000000800000400000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000001000000400000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000400000000000010000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000014000000008000000000800000000040000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000004000000000000000040000000000000000000010000000000000000000000000000000000000000000000200000000000000000000000000000000020000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000020000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000020200000000480000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000080000000000000000000000000000000000000000008000000000000000000000000000000000800000000000000000040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000100000000000000000000000402000000000000000000000000000001020000000000000000000000000000000000000000000000000000000000000000000000000010000200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000088000000000000000000001000000000000000000000000000040000000000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000001000000001000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000280000000000000000000000000200000000000000010000000000000000000000000000000000000000000000000008000200000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000240000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000004080000080000000000000000002200000000000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000800000000000004000000000000000000000000000000800000000000000000000000000000000000000000000000800000000000000000000000000000000000000000100000000000000000000000000000000000000000000001200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000020000000000000000040000000000000000000000000000000000000000000000100000000000000000000040004000000000000000000000000000000600000000000000000008000000000000000000000000000000000004000000080000000000000000000000000000000000000000000000020000000000000000000000000000200000000000000000000000002000000000000000000000000000000000000000000000000000000020000000000400000000000000008000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000040000000000000000200000000000008000000000000000000000000000000000400000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000a0000000000000000002000000000000000000000000000000000010000000100000000000000000000000000000000000000000000000000000000000000000000000000000820000000000000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000040000000000000000000000000000000020000000008000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000020000000000000000000400000000000000000000000c000000000000200000000000000000000000400040000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000008000000000000000000000020000000000000040000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000100000000000002000000000000000200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000060000000000000000000000000000000000000000000400000000000000000000000000080000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000000000004000000000000800000000000000000000000000800000000000040000000010000000000000000000020000000000000000002000000000000000000000
/-- `O(1)` GMP `Nat.testBit` membership predicate in the `1,526`-element single-electron
  burst-syndrome set. -/
def inSpan18 (x : ℕ) : Bool := span18Bitmap.testBit x
/-- For each electron `i ∈ [0..218)`, `(c_min, [7 nonzero GF(8)-multiples])`. -/
def linesScaled : List (ℕ × List ℕ) :=
  [(39303, [39303, 75717, 114242, 150849, 185542, 223876, 258819]), (6505, [6505, 9802, 16163,
    19604, 22013, 27358, 29623]), (805, [805, 1241, 2044, 2482, 2711, 3435, 3662]), (42400, [42400,
    84440, 126072, 145264, 168656, 229032, 252680]), (54672, [54672, 72160, 117872, 141144, 193224,
    212664, 256808]), (5817, [5817, 11562, 15251, 20172, 22645, 25574, 30047]), (7813, [7813, 11009,
    13700, 17090, 23623, 27075, 30534]), (59676, [59676, 95987, 106479, 155070, 177314, 207693,
    246353]), (59198, [59198, 97519, 105425, 155533, 178355, 205666, 246876]), (48163, [48163,
    93726, 119357, 162359, 181780, 201769, 239626]), (50737, [50737, 80954, 129547, 159276, 174109,
    217622, 234535]), (35484, [35484, 66355, 100783, 132350, 167522, 198605, 232785]), (53693,
    [53693, 70121, 114772, 139594, 192759, 209059, 254238]), (58706, [58706, 96356, 105782, 153243,
    177097, 208639, 248749]), (50381, [50381, 80273, 130396, 157666, 172847, 220787, 236222]),
    (51450, [51450, 79788, 130902, 159179, 173361, 219751, 234141]), (58332, [58332, 95603, 104111,
    153726, 179106, 208141, 249553]), (4999, [4999, 9669, 13890, 18753, 23238, 27780, 32515]),
    (55159, [55159, 72829, 117514, 143017, 195038, 209620, 255395]), (41487, [41487, 82965, 124442,
    145441, 170542, 228404, 253499]), (34081, [34081, 67802, 101883, 133044, 164501, 200558,
    232015]), (63004, [63004, 89139, 109103, 138814, 190498, 213517, 242705]), (37783, [37783,
    75237, 112242, 149849, 187086, 224444, 261931]), (47778, [47778, 90908, 121278, 161011, 183889,
    202735, 240973]), (4459, [4459, 8270, 12581, 16535, 20988, 24793, 29106]), (37428, [37428,
    74811, 112143, 149550, 186906, 224277, 261665]), (61488, [61488, 86072, 106504, 135208, 188440,
    213008, 241696]), (32900, [32900, 65795, 98695, 131270, 163906, 197061, 229697]), (48138,
    [48138, 93716, 119326, 162339, 181801, 201783, 239677]), (46379, [46379, 92366, 122341, 161687,
    180924, 204633, 240242]), (34294, [34294, 67967, 101513, 132717, 164763, 200466, 232164]),
    (55153, [55153, 72826, 117515, 143020, 195037, 209622, 255399]), (5286, [5286, 10527, 15801,
    18165, 21075, 28650, 31564]), (37232, [37232, 73848, 110856, 147624, 184792, 221392, 258464]),
    (55962, [55962, 70452, 117166, 140539, 196193, 210895, 257365]), (45219, [45219, 90398, 119229,
    159991, 180308, 201193, 237898]), (64136, [64136, 86800, 108952, 136416, 192104, 215024,
    245112]), (40990, [40990, 81975, 122921, 143421, 167971, 225290, 249876]), (60897, [60897,
    98138, 103099, 154228, 178069, 206126, 248015]), (42561, [42561, 85122, 125635, 147204, 170309,
    226182, 251335]), (64939, [64939, 90062, 107109, 138071, 190204, 214169, 244018]), (40501,
    [40501, 76345, 111628, 148010, 187423, 223251, 259622]), (55820, [55820, 70163, 116767, 140326,
    196138, 210485, 257081]), (7278, [7278, 11919, 13025, 19221, 22395, 26010, 31220]), (62412,
    [62412, 87379, 108191, 137318, 191402, 216373, 245497]), (33766, [33766, 66911, 100025, 133237,
    166803, 199978, 233164]), (54802, [54802, 72740, 117302, 142875, 194569, 209471, 255021]),
    (42039, [42039, 84029, 125962, 144937, 168478, 228884, 252451]), (37853, [37853, 75121, 112300,
    149626, 187303, 224523, 261846]), (58566, [58566, 96647, 105793, 153541, 176899, 208450,
    248452]), (7171, [7171, 11782, 12805, 18951, 22020, 25601, 30722]), (47047, [47047, 93509,
    121474, 163393, 182662, 201476, 238787]), (48302, [48302, 93967, 119713, 162517, 181883, 202202,
    239988]), (50727, [50727, 80925, 129594, 159281, 174102, 217644, 234507]), (41331, [41331,
    82046, 123149, 143535, 168412, 225489, 250274]), (63834, [63834, 87668, 110382, 138427, 189921,
    215759, 242581]), (49309, [49309, 78129, 127404, 155898, 172135, 217547, 233814]), (6560, [6560,
    10200, 15992, 19824, 21712, 27304, 29448]), (63091, [63091, 89278, 109261, 139055, 190812,
    213905, 243170]), (41472, [41472, 82944, 124416, 145408, 170496, 228352, 253440]), (49655,
    [49655, 78205, 127114, 155753, 172446, 217364, 233699]), (41221, [41221, 82113, 123332, 143746,
    168071, 225603, 249926]), (61252, [61252, 96835, 103687, 152198, 179650, 207045, 247681]),
    (52702, [52702, 81783, 127657, 158333, 173987, 218378, 235732]), (43275, [43275, 83670, 126941,
    146855, 169132, 228209, 250490]), (47898, [47898, 90868, 121326, 161211, 183969, 202575,
    240725]), (63148, [63148, 89355, 109479, 138966, 190586, 213981, 243057]), (35944, [35944,
    69256, 99040, 133904, 165752, 198040, 231920]), (85, [85, 161, 244, 282, 335, 443, 494]),
    (34229, [34229, 68089, 101452, 132970, 164575, 200339, 232230]), (63984, [63984, 87928, 110216,
    138344, 189848, 215824, 242400]), (37651, [37651, 74982, 112629, 149919, 187020, 224633,
    261738]), (52162, [52162, 78660, 129158, 156739, 176001, 218887, 236741]), (36287, [36287,
    69613, 98898, 133961, 165622, 197796, 231707]), (43942, [43942, 82911, 125049, 144757, 171731,
    226986, 253196]), (36293, [36293, 69441, 98948, 133698, 165767, 197891, 231622]), (59150,
    [59150, 97495, 105433, 155557, 178347, 205682, 246908]), (6441, [6441, 9930, 16355, 19860,
    21693, 27486, 29303]), (63792, [63792, 87800, 110536, 138664, 189592, 215888, 242272]), (46645,
    [46645, 93241, 121356, 163370, 182303, 201235, 238630]), (8174, [8174, 11087, 13473, 16981,
    23995, 26906, 30452]), (60873, [60873, 98130, 103067, 154212, 178093, 206134, 248063]), (63175,
    [63175, 89477, 109378, 139201, 190726, 213572, 242819]), (63676, [63676, 87851, 110487, 138446,
    189554, 216037, 242521]), (34949, [34949, 67329, 102276, 134338, 164935, 199619, 230214]),
    (63717, [63717, 87961, 110460, 138738, 189719, 215659, 242318]), (36438, [36438, 68263, 99569,
    131869, 167243, 199098, 231404]), (37823, [37823, 75245, 112210, 149833, 187126, 224420,
    261915]), (47061, [47061, 93537, 121524, 163418, 182671, 201531, 238830]), (64504, [64504,
    86888, 108688, 136264, 192432, 214816, 244952]), (57582, [57582, 94607, 102753, 152021, 176443,
    204890, 245940]), (47348, [47348, 92091, 122703, 163310, 181530, 203349, 238241]), (54927,
    [54927, 72981, 117658, 143073, 194670, 209908, 255355]), (34139, [34139, 67702, 101677, 132799,
    164836, 200393, 232338]), (62572, [62572, 88203, 109799, 136982, 189306, 216989, 244721]),
    (49442, [49442, 78044, 127486, 156083, 172177, 217455, 233549]), (37928, [37928, 75784, 113696,
    149008, 184888, 224792, 260656]), (7337, [7337, 12042, 13219, 19156, 22141, 26078, 31095]),
    (39835, [39835, 74742, 112749, 148863, 188132, 222857, 261394]), (63936, [63936, 87872, 110208,
    138304, 189824, 215808, 242368]), (39900, [39900, 74611, 112815, 148606, 188322, 222989,
    261329]), (64420, [64420, 87003, 108671, 136566, 192210, 214701, 245001]), (4838, [4838, 9631,
    14201, 18933, 23315, 27754, 32396]), (40802, [40802, 76380, 111934, 148147, 187857, 223471,
    259981]), (33718, [33718, 67071, 99913, 133485, 166619, 199826, 233252]), (60476, [60476, 97835,
    102935, 154126, 177714, 205861, 247833]), (50474, [50474, 80076, 130534, 157587, 172729, 221023,
    236149]), (65426, [65426, 89060, 107638, 136027, 191689, 215231, 243501]), (55009, [55009,
    73114, 117627, 143348, 194837, 209518, 255119]), (57550, [57550, 94615, 102745, 152037, 176427,
    204914, 245948]), (59439, [59439, 95757, 106018, 154641, 177214, 207388, 246323]), (33996,
    [33996, 67987, 101727, 133094, 164650, 200309, 232121]), (45074, [45074, 90148, 118838, 159771,
    180233, 200767, 237613]), (52173, [52173, 78673, 129180, 156770, 176047, 218931, 236798]),
    (6779, [6779, 8878, 14549, 17679, 24436, 26529, 32218]), (61376, [61376, 97088, 103552, 152128,
    179584, 207104, 247488]), (58733, [58733, 96329, 105764, 153234, 177151, 208603, 248758]),
    (44689, [44689, 84770, 124339, 144092, 171085, 227838, 251759]), (56374, [56374, 73279, 115209,
    141869, 194075, 209938, 256036]), (34231, [34231, 68093, 101450, 132969, 164574, 200340,
    232227]), (54255, [54255, 70989, 116386, 141393, 195518, 212252, 257779]), (35656, [35656,
    66128, 100632, 132256, 167912, 198384, 232888]), (60181, [60181, 94945, 104948, 152986, 179855,
    206715, 248942]), (51246, [51246, 79375, 130593, 158741, 173115, 219674, 234036]), (43983,
    [43983, 82773, 125082, 144481, 171950, 227124, 253179]), (38701, [38701, 77001, 113636, 151442,
    186559, 222043, 259190]), (4199, [4199, 8349, 12538, 16689, 20822, 25004, 29131]), (50041,
    [50041, 78954, 128787, 157836, 175093, 220390, 237471]), (42695, [42695, 85381, 125762, 147393,
    170246, 225860, 251011]), (37545, [37545, 75018, 112547, 149716, 187005, 224734, 262007]),
    (38819, [38819, 77278, 113277, 151415, 186580, 221865, 259338]), (5285, [5285, 10521, 15804,
    18162, 21079, 28651, 31566]), (7579, [7579, 12278, 12909, 19327, 22244, 25737, 30994]), (44459,
    [44459, 85966, 123493, 146263, 169724, 226457, 252210]), (41546, [41546, 83092, 124638, 145699,
    170857, 228791, 253949]), (4564, [4564, 8547, 12471, 16478, 20874, 24893, 28905]), (42259,
    [42259, 84198, 126453, 145311, 168588, 229241, 252522]), (38075, [38075, 76078, 114069, 149199,
    184948, 225249, 260954]), (8121, [8121, 11242, 13395, 17228, 23797, 26790, 30495]), (45419,
    [45419, 90190, 119077, 159895, 180732, 200921, 238002]), (39038, [39038, 75439, 114385, 150797,
    185715, 224162, 259036]), (43980, [43980, 82771, 125087, 144486, 171946, 227125, 253177]),
    (50040, [50040, 78952, 128784, 157832, 175088, 220384, 237464]), (33976, [33976, 67880, 101776,
    132808, 164464, 200672, 232280]), (46721, [46721, 93442, 121731, 163524, 182341, 201670,
    238919]), (41765, [41765, 83161, 124924, 145842, 170647, 228715, 253518]), (49492, [49492,
    77923, 127287, 155806, 172490, 217341, 233897]), (34344, [34344, 68616, 100896, 134672, 165944,
    197144, 230448]), (49159, [49159, 77829, 126978, 155649, 172038, 217092, 233475]), (54951,
    [54951, 72989, 117690, 143089, 194646, 209900, 255307]), (8026, [8026, 10868, 13614, 17083,
    24033, 26831, 30613]), (55182, [55182, 73175, 117337, 143205, 194795, 209586, 255292]), (50535,
    [50535, 79965, 130362, 157361, 173014, 220908, 236427]), (61988, [61988, 87067, 108095, 137270,
    190994, 216109, 245257]), (37540, [37540, 75035, 112575, 149750, 186962, 224749, 261961]),
    (34747, [34747, 69102, 100949, 134991, 166132, 197281, 230682]), (43850, [43850, 82516, 125214,
    144547, 172009, 227063, 253373]), (46266, [46266, 92460, 122262, 161483, 180849, 204775,
    240477]), (46525, [46525, 92649, 121940, 161610, 180983, 204451, 240414]), (39763, [39763,
    74342, 112949, 148639, 188364, 222969, 261546]), (56414, [56414, 73399, 115433, 142141, 194403,
    210314, 256468]), (53805, [53805, 70665, 116260, 141330, 195135, 211995, 257590]), (51614,
    [51614, 79863, 130665, 159101, 173283, 219786, 234260]), (43697, [43697, 82746, 125323, 144620,
    171613, 227286, 253287]), (37001, [37001, 74002, 111003, 147684, 184429, 221686, 258431]),
    (63684, [63684, 87939, 110407, 138694, 189698, 215621, 242305]), (51143, [51143, 81221, 129666,
    159297, 174470, 217860, 234691]), (49068, [49068, 93131, 119911, 160598, 183546, 202909,
    239409]), (39160, [39160, 75688, 114512, 150984, 185648, 223840, 258712]), (44854, [44854,
    84735, 124361, 144301, 171163, 227666, 251492]), (59280, [59280, 97760, 105072, 155480, 178376,
    205496, 247080]), (36632, [36632, 68336, 99816, 132024, 167072, 198984, 230992]), (55354,
    [55354, 71212, 118294, 142347, 193585, 211495, 254493]), (65123, [65123, 88734, 107773, 135991,
    191828, 215465, 243658]), (62941, [62941, 88433, 109740, 136826, 189351, 216843, 244438]),
    (36044, [36044, 69523, 99167, 134118, 165674, 197749, 231609]), (56818, [56818, 73596, 115342,
    141931, 194457, 210199, 256229]), (64035, [64035, 86558, 108605, 136247, 192020, 214569,
    244746]), (48881, [48881, 93114, 120139, 160748, 183581, 202838, 239271]), (45722, [45722,
    91444, 120750, 162043, 182881, 204239, 241493]), (57629, [57629, 94449, 102892, 151994, 176295,
    205131, 245846]), (35867, [35867, 69174, 98861, 133695, 165412, 197641, 231442]), (46701,
    [46701, 93321, 121572, 163602, 182655, 201627, 239094]), (5110, [5110, 9599, 13961, 18541,
    23451, 27922, 32484]), (34404, [34404, 68763, 101119, 134966, 166226, 197549, 230857]), (37831,
    [37831, 75077, 112258, 149569, 187270, 224516, 261827]), (34362, [34362, 68652, 100886, 134667,
    165937, 197159, 230429]), (59976, [59976, 94864, 104664, 152864, 180072, 206768, 249336]),
    (33332, [33332, 66619, 99855, 133166, 166426, 199701, 232993]), (53709, [53709, 69969, 114844,
    139362, 192943, 209203, 254206]), (8175, [8175, 11085, 13474, 16977, 23998, 26908, 30451]),
    (63269, [63269, 89305, 109564, 139186, 190615, 213867, 242766]), (46999, [46999, 93669, 121458,
    163673, 182478, 201404, 238891]), (61336, [61336, 97264, 103528, 152440, 179424, 206984,
    247568]), (41530, [41530, 82988, 124438, 145419, 170545, 228391, 253469]), (56868, [56868,
    72219, 115775, 139830, 195602, 210989, 255497]), (57298, [57298, 72548, 115894, 139867, 195977,
    211263, 255725]), (46662, [46662, 93319, 121537, 163589, 182595, 201602, 239044]), (58104,
    [58104, 95656, 104272, 154056, 178992, 207968, 249496]), (7431, [7431, 11973, 13250, 19329,
    22150, 25924, 30787]), (59283, [59283, 97766, 105077, 155487, 178380, 205497, 247082]), (50693,
    [50693, 80897, 129540, 159234, 174087, 217603, 234502]), (33983, [33983, 67885, 101778, 132809,
    164470, 200676, 232283]), (39792, [39792, 74360, 112904, 148648, 188376, 222928, 261536]),
    (8010, [8010, 10836, 13598, 17059, 24041, 26871, 30653]), (65163, [65163, 88854, 107933, 135911,
    191596, 215537, 243578]), (48339, [48339, 94118, 119669, 162783, 182028, 201849, 239786]),
    (59231, [59231, 97397, 105258, 155321, 178662, 205516, 247187]), (38335, [38335, 76269, 113746,
    149321, 185078, 224932, 260891]), (40191, [40191, 77741, 111442, 150473, 186166, 222308,
    260251]), (61596, [61596, 86323, 106927, 135422, 188514, 213453, 242001]), (42975, [42975,
    85365, 125610, 147065, 170406, 226060, 251091]), (40205, [40205, 77521, 111580, 150434, 186031,
    222579, 260222]), (35747, [35747, 66526, 100477, 132471, 167636, 198313, 232714]), (64187,
    [64187, 86830, 108949, 136399, 192116, 215009, 245082]), (43238, [43238, 83871, 126841, 146933,
    169235, 227946, 250508]), (56539, [56539, 73654, 115565, 142335, 194340, 209993, 256146]),
    (38869, [38869, 77153, 113332, 151130, 186767, 222011, 259310])]
def lineMin (i : Fin 218) : ℕ := (linesScaled.getD i.val (0, [])).1
def lineSet (i : Fin 218) : List ℕ := (linesScaled.getD i.val (0, [])).2
def checkPairRow (c : ℕ) : List (ℕ × List ℕ) → Bool
  | [] => true
  | (_, ds) :: rest => (ds.all fun d ↦ !(inSpan18 (c ^^^ d))) && checkPairRow c rest
def checkRangeSpan : ℕ → List (ℕ × List ℕ) → Bool
  | 0, _ => true
  | _, [] => true
  | n + 1, (c, _) :: rest => checkPairRow c rest && checkRangeSpan n rest
theorem cert_span_0 : checkRangeSpan 32 linesScaled = true := by decide
theorem cert_span_1 : checkRangeSpan 38 (linesScaled.drop 32) = true := by decide
theorem cert_span_2 : checkRangeSpan 48 (linesScaled.drop 70) = true := by decide
theorem cert_span_3 : checkRangeSpan 100 (linesScaled.drop 118) = true := by decide
theorem checkPairRow_sound (c : ℕ) :
    ∀ (ps : List (ℕ × List ℕ)),
      checkPairRow c ps = true →
      ∀ k : ℕ, k < ps.length →
        ∀ d ∈ (ps.getD k (0, [])).2, inSpan18 (c ^^^ d) = false
  | [], _, k, hk => absurd hk (Nat.not_lt_zero k)
  | (_, ds) :: rest, hok, 0, _ => by
      intro d hd
      simp only [List.getD_cons_zero] at hd
      have hall := List.all_eq_true.mp (Bool.and_eq_true_iff.mp hok).1 d hd
      simpa using hall
  | (_, _ds) :: rest, hok, k + 1, hk => by
      simp only [List.getD_cons_succ]
      exact checkPairRow_sound c rest (Bool.and_eq_true_iff.mp hok).2 k (Nat.lt_of_succ_lt_succ hk)
theorem checkRangeSpan_sound :
    ∀ (n : ℕ) (ps : List (ℕ × List ℕ)),
      checkRangeSpan n ps = true →
      ∀ j k : ℕ, j < n → j < k → k < ps.length →
        ∀ d ∈ (ps.getD k (0, [])).2, inSpan18 ((ps.getD j (0, [])).1 ^^^ d) = false
  | 0, _, _, j, _, hjn, _, _ => absurd hjn (Nat.not_lt_zero j)
  | _ + 1, [], _, _, k, _, _, hk => absurd hk (Nat.not_lt_zero k)
  | _ + 1, (c, _) :: rest, hok, 0, k + 1, _, _, hk => by
      simp only [List.getD_cons_zero, List.getD_cons_succ]
      exact checkPairRow_sound c rest (Bool.and_eq_true_iff.mp hok).1 k (Nat.lt_of_succ_lt_succ hk)
  | n + 1, (_, _) :: rest, hok, j + 1, k + 1, hjn, hjk, hk => by
      simp only [List.getD_cons_succ]
      exact checkRangeSpan_sound n rest (Bool.and_eq_true_iff.mp hok).2 j k
        (by omega) (by omega) (Nat.lt_of_succ_lt_succ hk)
theorem getD_drop_eq {α : Type} (dflt : α) :
    ∀ (a : ℕ) (ps : List α) (m : ℕ), (ps.drop a).getD m dflt = ps.getD (a + m) dflt
  | 0, _, _ => by simp
  | a + 1, [], _ => by simp
  | a + 1, _ :: rest, m => by
      simp only [List.drop_succ_cons, getD_drop_eq dflt a rest m, Nat.succ_add, List.getD_cons_succ]
theorem linesScaled_length : linesScaled.length = 218 := by decide
theorem linesScaled_getD_eq (i : Fin 218) :
    linesScaled.getD i.val (0, []) = (lineMin i, lineSet i) := rfl
theorem inSpan18_xor_false_of_lt {i₁ i₂ : Fin 218} (hlt : i₁ < i₂) {w₂ : ℕ}
    (hw₂ : w₂ ∈ lineSet i₂) : inSpan18 (lineMin i₁ ^^^ w₂) = false := by
  have hi₂ : i₂.val < 218 := i₂.isLt
  have h12 : i₁.val < i₂.val := hlt
  have hlen : linesScaled.length = 218 := linesScaled_length
  by_cases h32 : i₁.val < 32
  · have hs := checkRangeSpan_sound 32 linesScaled cert_span_0 i₁.val i₂.val
      h32 h12 (by omega)
    rw [linesScaled_getD_eq i₁, linesScaled_getD_eq i₂] at hs
    exact hs w₂ hw₂
  · by_cases h70 : i₁.val < 70
    · have hs := checkRangeSpan_sound 38 (linesScaled.drop 32) cert_span_1
        (i₁.val - 32) (i₂.val - 32) (by omega) (by omega)
        (by
          rw [List.length_drop]
          omega)
      rw [getD_drop_eq, getD_drop_eq,
          show 32 + (i₁.val - 32) = i₁.val by omega,
          show 32 + (i₂.val - 32) = i₂.val by omega,
          linesScaled_getD_eq i₁, linesScaled_getD_eq i₂] at hs
      exact hs w₂ hw₂
    · by_cases h118 : i₁.val < 118
      · have hs := checkRangeSpan_sound 48 (linesScaled.drop 70) cert_span_2
          (i₁.val - 70) (i₂.val - 70) (by omega) (by omega)
          (by
            rw [List.length_drop]
            omega)
        rw [getD_drop_eq, getD_drop_eq,
            show 70 + (i₁.val - 70) = i₁.val by omega,
            show 70 + (i₂.val - 70) = i₂.val by omega,
            linesScaled_getD_eq i₁, linesScaled_getD_eq i₂] at hs
        exact hs w₂ hw₂
      · have hs := checkRangeSpan_sound 100 (linesScaled.drop 118) cert_span_3
          (i₁.val - 118) (i₂.val - 118) (by omega) (by omega)
          (by
            rw [List.length_drop]
            omega)
        rw [getD_drop_eq, getD_drop_eq,
            show 118 + (i₁.val - 118) = i₁.val by omega,
            show 118 + (i₂.val - 118) = i₂.val by omega,
            linesScaled_getD_eq i₁, linesScaled_getD_eq i₂] at hs
        exact hs w₂ hw₂
def gf8Scales7 : List (Fin 8) := [1, 2, 3, 4, 5, 6, 7]
def checkOneLine (i : Fin 218) (c : ℕ) (vs : List ℕ) : Bool :=
  decide (c ∈ vs) &&
  inSpan18 (c ^^^ gf8ScaleVec 2 c) &&
  (List.finRange 8).all (fun m ↦
    decide (m.val = 0) || (decide (elecMaskSyn18 i m ≠ 0) && decide (elecMaskSyn18 i m ∈ vs))) &&
  vs.all fun v ↦
    inSpan18 v &&
    decide (v < 2 ^ 18) &&
    decide (c ≤ v) &&
    gf8Scales7.any (fun s ↦ decide (s.val ≠ 0 ∧ gf8ScaleVec s v = c)) &&
    (List.finRange 8).all (fun s ↦ decide (s.val = 0) || decide (gf8ScaleVec s v ∈ vs))
def checkLinePropsList : ℕ → List (ℕ × List ℕ) → Bool
  | _, [] => true
  | idx, (c, vs) :: rest =>
      (if h : idx < 218 then checkOneLine ⟨idx, h⟩ c vs else false) &&
        checkLinePropsList (idx + 1) rest
set_option maxHeartbeats 1600000 in
-- Decide 218-electron GF(8) scaled line-property certificate.
theorem cert_line_props : checkLinePropsList 0 linesScaled = true := by decide
theorem checkLinePropsList_sound :
    ∀ (idx : ℕ) (ps : List (ℕ × List ℕ)),
      checkLinePropsList idx ps = true →
      ∀ (k : ℕ), k < ps.length → ∀ (hidx : idx + k < 218),
        checkOneLine ⟨idx + k, hidx⟩ (ps.getD k (0, [])).1 (ps.getD k (0, [])).2 = true
  | _, [], _, k, hk, _ => absurd hk (Nat.not_lt_zero k)
  | idx, (_, _) :: _, hok, 0, _, hidx => by
      have h1 := (Bool.and_eq_true_iff.mp hok).1
      have hi : idx < 218 := by omega
      rw [dite_eq_left hi] at h1
      simpa [Nat.add_zero] using h1
  | idx, (_, _) :: rest, hok, k + 1, hk, hidx => by
      simp only [List.getD_cons_succ]
      have h2 := checkLinePropsList_sound (idx + 1) rest (Bool.and_eq_true_iff.mp hok).2 k
        (Nat.lt_of_succ_lt_succ hk) (by omega)
      simpa [Nat.add_assoc, Nat.add_comm 1 k] using h2
theorem checkOneLine_true (i : Fin 218) : checkOneLine i (lineMin i) (lineSet i) = true := by
  have hlen : linesScaled.length = 218 := linesScaled_length
  have hi : i.val < 218 := i.isLt
  have hs := checkLinePropsList_sound 0 linesScaled cert_line_props i.val
    (by omega) (by simp [hi])
  simpa [lineMin, lineSet] using hs
theorem elecMaskSyn18_mem_lineSet (i : Fin 218) (m : Fin 8) (hm : m.val ≠ 0) :
    elecMaskSyn18 i m ≠ 0 ∧ elecMaskSyn18 i m ∈ lineSet i := by
  have hi := checkOneLine_true i
  unfold checkOneLine at hi
  simp only [Bool.and_eq_true] at hi
  rcases hi with ⟨⟨⟨_, _⟩, hm_all⟩, _⟩
  have hm_prop := List.all_eq_true.mp hm_all m (List.mem_finRange m)
  simp only [hm, decide_false, Bool.false_or, Bool.and_eq_true, decide_eq_true_iff] at hm_prop
  exact hm_prop
theorem lineSet_props (i : Fin 218) {v : ℕ} (hv : v ∈ lineSet i) : v < 2 ^ 18 ∧ inSpan18 v =
    true ∧ lineMin i ≤ v ∧ (∃ s : Fin 8, s.val ≠ 0 ∧ gf8ScaleVec s v = lineMin i) ∧
    (∀ s : Fin 8, s.val ≠ 0 → gf8ScaleVec s v ∈ lineSet i) := by
  have hi := checkOneLine_true i
  unfold checkOneLine at hi
  simp only [Bool.and_eq_true] at hi
  rcases hi with ⟨_, hvs_all⟩
  have hv_prop := List.all_eq_true.mp hvs_all v hv
  simp only [Bool.and_eq_true, List.any_eq_true, List.all_eq_true] at hv_prop
  rcases hv_prop with ⟨⟨⟨⟨hsp, hvlt⟩, hle⟩, ⟨s, _, hs⟩⟩, hall_s⟩
  refine ⟨of_decide_eq_true hvlt, hsp, of_decide_eq_true hle,
    ⟨s, of_decide_eq_true hs⟩, fun s' hs' ↦ ?_⟩
  have h1 := hall_s s' (List.mem_finRange s')
  simp only [hs', decide_false, Bool.false_or, decide_eq_true_iff] at h1
  exact h1
theorem lineMin_inj (i₁ i₂ : Fin 218) (h : lineMin i₁ = lineMin i₂) : i₁ = i₂ := by
  rcases lt_trichotomy i₁ i₂ with hlt | heq | hgt
  · exfalso
    have hi₂ := checkOneLine_true i₂
    unfold checkOneLine at hi₂
    simp only [Bool.and_eq_true, decide_eq_true_iff] at hi₂
    rcases hi₂ with ⟨⟨⟨hc₂_mem, hsp₂⟩, _⟩, _⟩
    have hw₂ : gf8ScaleVec 2 (lineMin i₂) ∈ lineSet i₂ :=
      (lineSet_props i₂ hc₂_mem).2.2.2.2 2 (by decide)
    have hf := inSpan18_xor_false_of_lt hlt hw₂
    rw [h, hsp₂] at hf
    exact Bool.false_ne_true hf.symm
  · exact heq
  · exfalso
    have hi₁ := checkOneLine_true i₁
    unfold checkOneLine at hi₁
    simp only [Bool.and_eq_true, decide_eq_true_iff] at hi₁
    rcases hi₁ with ⟨⟨⟨hc₁_mem, hsp₁⟩, _⟩, _⟩
    have hw₁ : gf8ScaleVec 2 (lineMin i₁) ∈ lineSet i₁ :=
      (lineSet_props i₁ hc₁_mem).2.2.2.2 2 (by decide)
    have hf := inSpan18_xor_false_of_lt hgt hw₁
    rw [← h, hsp₁] at hf
    exact Bool.false_ne_true hf.symm
theorem nat_eq_of_xor_eq_zero {a b : ℕ} (h : (a ^^^ b) = 0) : a = b := by
  apply Nat.eq_of_testBit_eq
  intro k
  have hk : (a ^^^ b).testBit k = false := by rw [h, Nat.zero_testBit]
  rw [Nat.testBit_xor] at hk
  cases ha : a.testBit k <;> cases hb : b.testBit k <;> simp_all
theorem elecBadPred_iff_mask (x : Fin (2 ^ SpecsAux.SpecMirror.systemQubits)) (i : Fin 218) :
    ((elecAxisWord6 x i 0).val = 32 ∨ (elecAxisWord6 x i 1).val = 32 ∨ (elecAxisWord6 x i 2).val =
      32) →
      ∃ m : Fin 8, m.val ≠ 0 ∧ elecSyn18 x i = elecMaskSyn18 i m := by
  intro hbad
  let b0 := decide ((elecAxisWord6 x i 0).val = 32)
  let b1 := decide ((elecAxisWord6 x i 1).val = 32)
  let b2 := decide ((elecAxisWord6 x i 2).val = 32)
  let m : Fin 8 := ⟨(if b0 then 1 else 0) + 2 * (if b1 then 1 else 0) + 4 * (if b2 then 1 else 0),
    by split_ifs <;> omega⟩
  refine ⟨m, ?_, ?_⟩
  · rcases hbad with h0 | h1 | h2
    · have hb : b0 = true := decide_eq_true h0
      dsimp only [m]
      rw [ite_eq_left hb]
      split_ifs <;> omega
    · have hb : b1 = true := decide_eq_true h1
      dsimp only [m]
      rw [ite_eq_left hb]
      split_ifs <;> omega
    · have hb : b2 = true := decide_eq_true h2
      dsimp only [m]
      rw [ite_eq_left hb]
      split_ifs <;> omega
  · have hm_bits : ∀ (c0 c1 c2 : Bool),
        let mv := (if c0 then 1 else 0) + 2 * (if c1 then 1 else 0) + 4 * (if c2 then 1 else 0)
        mv.testBit 0 = c0 ∧ mv.testBit 1 = c1 ∧ mv.testBit 2 = c2 := by decide
    obtain ⟨ht0, ht1, ht2⟩ := hm_bits b0 b1 b2
    unfold elecSyn18 elecMaskSyn18
    dsimp only [m]
    rw [ht0, ht1, ht2]
    dsimp only [b0, b1, b2]
    by_cases c0 : (elecAxisWord6 x i 0).val = 32 <;>
    by_cases c1 : (elecAxisWord6 x i 1).val = 32 <;>
    by_cases c2 : (elecAxisWord6 x i 2).val = 32 <;>
    simp [c0, c1, c2]
theorem foldr_elecSyn18_filter (x : Fin (2 ^ SpecsAux.SpecMirror.systemQubits)) :
    ∀ (L : List (Fin 218)),
      L.foldr (fun i acc ↦ elecSyn18 x i ^^^ acc) 0 =
        (L.filter fun i ↦ decide ((elecAxisWord6 x i 0).val = 32 ∨
          (elecAxisWord6 x i 1).val = 32 ∨ (elecAxisWord6 x i 2).val = 32)).foldr
          (fun i acc ↦ elecSyn18 x i ^^^ acc) 0
  | [] => rfl
  | i :: rest => by
      simp only [List.foldr_cons, List.filter_cons]
      by_cases hp : (elecAxisWord6 x i 0).val = 32 ∨
          (elecAxisWord6 x i 1).val = 32 ∨ (elecAxisWord6 x i 2).val = 32
      · simp [hp, foldr_elecSyn18_filter x rest]
      · have hp0 : (elecAxisWord6 x i 0).val ≠ 32 := fun h ↦ hp (Or.inl h)
        have hp1 : (elecAxisWord6 x i 1).val ≠ 32 := fun h ↦ hp (Or.inr (Or.inl h))
        have hp2 : (elecAxisWord6 x i 2).val ≠ 32 := fun h ↦ hp (Or.inr (Or.inr h))
        have hz : elecSyn18 x i = 0 := by simp [elecSyn18, hp0, hp1, hp2]
        simp [hp, hz, foldr_elecSyn18_filter x rest]
theorem burst_syndrome_ne_zero_of_nonempty_le_three (x : Fin (2 ^ SpecsAux.SpecMirror.systemQubits))
    (L : List (Fin 218)) (hsorted : L.Pairwise (· < ·)) (hbad_mem : ∀ i ∈ L, (elecAxisWord6 x
    i 0).val = 32 ∨ (elecAxisWord6 x i 1).val = 32 ∨ (elecAxisWord6 x i 2).val = 32)
    (hne : L ≠ []) (hle : L.length ≤ 3) : L.foldr (fun i acc ↦ elecSyn18 x i ^^^ acc) 0 ≠ 0
    := by
  match L with
  | [i₁] =>
      obtain ⟨m₁, hm₁, heq₁⟩ := elecBadPred_iff_mask x i₁ (hbad_mem i₁ (List.mem_singleton_self _))
      simp only [List.foldr_cons, List.foldr_nil, Nat.xor_zero, heq₁]
      exact (elecMaskSyn18_mem_lineSet i₁ m₁ hm₁).1
  | [i₁, i₂] =>
      have hi₁₂ : i₁ < i₂ := (List.pairwise_cons.mp hsorted).1 i₂ (List.mem_singleton_self _)
      obtain ⟨m₁, hm₁, heq₁⟩ := elecBadPred_iff_mask x i₁ (hbad_mem i₁ (by simp))
      obtain ⟨m₂, hm₂, heq₂⟩ := elecBadPred_iff_mask x i₂ (hbad_mem i₂ (by simp))
      simp only [List.foldr_cons, List.foldr_nil, Nat.xor_zero, heq₁, heq₂]
      intro hzero
      have hv_eq : elecMaskSyn18 i₁ m₁ = elecMaskSyn18 i₂ m₂ := nat_eq_of_xor_eq_zero hzero
      have hv₁ := (elecMaskSyn18_mem_lineSet i₁ m₁ hm₁).2
      have hv₂ := (elecMaskSyn18_mem_lineSet i₂ m₂ hm₂).2
      obtain ⟨_, _, _, ⟨s₁, hs₁, hsc₁⟩, _⟩ := lineSet_props i₁ hv₁
      obtain ⟨_, _, _, ⟨s₂, hs₂, hsc₂⟩, _⟩ := lineSet_props i₂ hv₂
      have hm₂_in₁ : lineMin i₂ ∈ lineSet i₁ := by
        rw [← hsc₂, ← hv_eq]
        exact (lineSet_props i₁ hv₁).2.2.2.2 s₂ hs₂
      have hm₁_in₂ : lineMin i₁ ∈ lineSet i₂ := by
        rw [← hsc₁, hv_eq]
        exact (lineSet_props i₂ hv₂).2.2.2.2 s₁ hs₁
      have hle₁₂ : lineMin i₁ ≤ lineMin i₂ := (lineSet_props i₁ hm₂_in₁).2.2.1
      have hle₂₁ : lineMin i₂ ≤ lineMin i₁ := (lineSet_props i₂ hm₁_in₂).2.2.1
      have heq_i := lineMin_inj i₁ i₂ (Nat.le_antisymm hle₁₂ hle₂₁)
      exact absurd heq_i (ne_of_lt hi₁₂)
  | [i₁, i₂, i₃] =>
      rcases List.pairwise_cons.mp hsorted with ⟨h₁_lt, _⟩
      have hi₁₂ : i₁ < i₂ := h₁_lt i₂ (by simp)
      obtain ⟨m₁, hm₁, heq₁⟩ := elecBadPred_iff_mask x i₁ (hbad_mem i₁ (by simp))
      obtain ⟨m₂, hm₂, heq₂⟩ := elecBadPred_iff_mask x i₂ (hbad_mem i₂ (by simp))
      obtain ⟨m₃, hm₃, heq₃⟩ := elecBadPred_iff_mask x i₃ (hbad_mem i₃ (by simp))
      simp only [List.foldr_cons, List.foldr_nil, Nat.xor_zero, heq₁, heq₂, heq₃]
      intro hzero
      have hv₁ := (elecMaskSyn18_mem_lineSet i₁ m₁ hm₁).2
      have hv₂ := (elecMaskSyn18_mem_lineSet i₂ m₂ hm₂).2
      have hv₃ := (elecMaskSyn18_mem_lineSet i₃ m₃ hm₃).2
      have hv₃_eq : elecMaskSyn18 i₃ m₃ = elecMaskSyn18 i₁ m₁ ^^^ elecMaskSyn18 i₂ m₂ := by
        have h' : ((elecMaskSyn18 i₁ m₁ ^^^ elecMaskSyn18 i₂ m₂) ^^^ elecMaskSyn18 i₃ m₃) = 0 := by
          rwa [Nat.xor_assoc]
        exact (nat_eq_of_xor_eq_zero h').symm
      obtain ⟨_, _, _, ⟨s₁, hs₁, hsc₁⟩, _⟩ := lineSet_props i₁ hv₁
      have hw₂_mem : gf8ScaleVec s₁ (elecMaskSyn18 i₂ m₂) ∈ lineSet i₂ :=
        (lineSet_props i₂ hv₂).2.2.2.2 s₁ hs₁
      have hw₃_mem : gf8ScaleVec s₁ (elecMaskSyn18 i₃ m₃) ∈ lineSet i₃ :=
        (lineSet_props i₃ hv₃).2.2.2.2 s₁ hs₁
      have htb_true : inSpan18 (gf8ScaleVec s₁ (elecMaskSyn18 i₃ m₃)) = true :=
        (lineSet_props i₃ hw₃_mem).2.1
      have hsc₃_eq : gf8ScaleVec s₁ (elecMaskSyn18 i₃ m₃) =
          lineMin i₁ ^^^ gf8ScaleVec s₁ (elecMaskSyn18 i₂ m₂) := by
        rw [hv₃_eq, gf8ScaleVec_xor, hsc₁]
      rw [hsc₃_eq, inSpan18_xor_false_of_lt hi₁₂ hw₂_mem] at htb_true
      exact Bool.false_ne_true htb_true
  | _ :: _ :: _ :: _ :: _ =>
      simp only [List.length_cons] at hle
      omega
/-- Agreement between `bValidGF8Code18` and `gridValidBool` on the `≤ 3`-bad-electron subspace. -/
theorem hbValidGF8Code18_core : ∀ x : Fin (2 ^ SpecsAux.SpecMirror.systemQubits),
    (Finset.univ.filter fun i : Fin SpecsAux.SpecMirror.numElectrons ↦ decide ((elecAxisWord6 x i
    0).val = 32 ∨ (elecAxisWord6 x i 1).val = 32 ∨ (elecAxisWord6 x i 2).val = 32)).card ≤ 3 →
    bValidGF8Code18 x = gridValidBool x := by
  intro x hbad
  apply Bool.eq_iff_iff.mpr
  rw [gridValidBool_eq_true_iff, isGridState_iff_axisWords_ne_minInt]
  unfold bValidGF8Code18
  rw [decide_eq_true_iff]
  constructor
  · rintro ⟨hsyn0, hproj⟩
    refine ⟨fun i₀ w ↦ ?_, hproj⟩
    intro h32
    let pBad : Fin 218 → Bool := fun i ↦ decide ((elecAxisWord6 x i 0).val = 32 ∨
      (elecAxisWord6 x i 1).val = 32 ∨ (elecAxisWord6 x i 2).val = 32)
    let Lbad := (List.finRange 218).filter pBad
    have hsorted : Lbad.Pairwise (· < ·) := (List.pairwise_lt_finRange 218).filter _
    have hnodup : Lbad.Nodup := (List.nodup_finRange 218).filter _
    have hi₀_bad : pBad i₀ = true := by
      dsimp [pBad]
      rw [decide_eq_true_iff]
      rcases (by fin_cases w <;> decide : w = 0 ∨ w = 1 ∨ w = 2) with rfl | rfl | rfl
      · exact Or.inl h32
      · exact Or.inr (Or.inl h32)
      · exact Or.inr (Or.inr h32)
    have hne : Lbad ≠ [] :=
      List.ne_nil_of_mem (List.mem_filter.mpr ⟨List.mem_finRange i₀, hi₀_bad⟩)
    have hsub : Lbad.toFinset ⊆ Finset.univ.filter (fun i : Fin SpecsAux.SpecMirror.numElectrons ↦
        decide ((elecAxisWord6 x i 0).val = 32 ∨ (elecAxisWord6 x i 1).val = 32 ∨
        (elecAxisWord6 x i 2).val = 32)) := by
      intro i hi
      rw [List.mem_toFinset, List.mem_filter] at hi
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi.2⟩
    have hlen_le : Lbad.length ≤ 3 := by
      rw [← List.toFinset_card_of_nodup hnodup]
      exact (Finset.card_le_card hsub).trans hbad
    have hmem_bad : ∀ i ∈ Lbad, (elecAxisWord6 x i 0).val = 32 ∨
        (elecAxisWord6 x i 1).val = 32 ∨ (elecAxisWord6 x i 2).val = 32 :=
      fun i hi ↦ of_decide_eq_true (List.mem_filter.mp hi).2
    have hne0 := burst_syndrome_ne_zero_of_nonempty_le_three x Lbad hsorted hmem_bad hne hlen_le
    have hfold : fullSyndrome18 x = Lbad.foldr (fun i acc ↦ elecSyn18 x i ^^^ acc) 0 :=
      foldr_elecSyn18_filter x (List.finRange 218)
    exact hne0 (hfold ▸ hsyn0)
  · rintro ⟨helec, hproj⟩
    refine ⟨?_, hproj⟩
    rw [fullSyndrome18, foldr_elecSyn18_filter x (List.finRange 218)]
    have hnil : ((List.finRange 218).filter fun i : Fin 218 ↦
        decide ((elecAxisWord6 x i 0).val = 32 ∨
          (elecAxisWord6 x i 1).val = 32 ∨ (elecAxisWord6 x i 2).val = 32)) = [] := by
      rw [List.filter_eq_nil_iff]
      intro i _
      simp [helec i 0, helec i 1, helec i 2]
    rw [hnil]
    rfl
-- ============================================================================
-- Section 3: Bit-Level Syndrome Decomposition & `f2Parity` Fold
-- ============================================================================
theorem elecFieldIdx_lt (i : Fin 218) (w : Fin 3) : 3 * i.val + w.val < 654 := by
  have := i.isLt
  have := w.isLt
  omega
theorem elecSyn18_lt (x : Fin (2 ^ SpecsAux.SpecMirror.systemQubits)) (i : Fin 218) :
    elecSyn18 x i < 2 ^ 18 := by
  unfold elecSyn18
  apply Nat.xor_lt_two_pow
  · apply Nat.xor_lt_two_pow
    · split_ifs
      · exact colsGF8Nat_lt _
      · decide
    · split_ifs
      · exact colsGF8Nat_lt _
      · decide
  · split_ifs
    · exact colsGF8Nat_lt _
    · decide
theorem foldr_elecSyn18_lt (x : Fin (2 ^ SpecsAux.SpecMirror.systemQubits)) (L : List (Fin 218)) :
    L.foldr (fun i acc ↦ elecSyn18 x i ^^^ acc) 0 < 2 ^ 18 := by
  induction L with
  | nil =>
      simp only [List.foldr_nil]
      decide
  | cons i tl ih => exact Nat.xor_lt_two_pow (elecSyn18_lt x i) ih
def finPrefix (N : ℕ) : ∀ k : ℕ, k ≤ N → List (Fin N)
  | 0, _ => []
  | k + 1, hk => finPrefix N k (by omega) ++ [⟨k, hk⟩]
theorem finPrefix_length (N : ℕ) : ∀ (k : ℕ) (hk : k ≤ N), (finPrefix N k hk).length = k := by
  intro k
  induction k with
  | zero =>
      intro _
      rfl
  | succ k ih =>
      intro hk
      simp [finPrefix, ih (by omega)]
theorem finPrefix_getElem (N : ℕ) :
    ∀ (k : ℕ) (hk : k ≤ N) (i : ℕ) (hi : i < (finPrefix N k hk).length),
      (finPrefix N k hk)[i] = ⟨i, (finPrefix_length N k hk ▸ hi).trans_le hk⟩ := by
  intro k
  induction k with
  | zero =>
      intro _ i hi
      simp [finPrefix] at hi
  | succ k ih =>
      intro hk i hi
      simp only [finPrefix]
      by_cases hik : i < k
      · rw [List.getElem_append_left (by simpa [finPrefix_length] using hik)]
        exact ih (by omega) i (by simpa [finPrefix_length] using hik)
      · have hieq : i = k := by
          rw [finPrefix_length] at hi
          omega
        subst hieq
        rw [List.getElem_append_right (by simp [finPrefix_length])]
        simp [finPrefix_length]
theorem finPrefix_full (N : ℕ) : finPrefix N N le_rfl = List.finRange N := by
  apply List.ext_getElem
  · simp [finPrefix_length]
  · intro i h1 h2
    rw [finPrefix_getElem]
    ext
    simp
theorem foldr_xor_init {α : Type*} (L : List α) (h : α → Bool) (init : Bool) :
    L.foldr (fun a acc ↦ xor (h a) acc) init =
      xor (L.foldr (fun a acc ↦ xor (h a) acc) false) init := by
  induction L with
  | nil => simp
  | cons a tl ih =>
      simp only [List.foldr_cons, ih]
      cases h a <;> cases tl.foldr (fun b acc ↦ xor (h b) acc) false <;> cases init <;> rfl
theorem foldr_nat_xor_init {α : Type*} (L : List α) (h : α → ℕ) (init : ℕ) : L.foldr
    (fun a acc ↦ h a ^^^ acc) init = (L.foldr (fun a acc ↦ h a ^^^ acc) 0) ^^^ init := by
  induction L with
  | nil => simp
  | cons a tl ih =>
      simp only [List.foldr_cons, ih]
      ac_rfl
def foldPrefix {N : ℕ} (g : Fin N → Bool) : ∀ k : ℕ, k ≤ N → Bool
  | 0, _ => false
  | k + 1, hk => xor (g ⟨k, hk⟩) (foldPrefix g k (by omega))
theorem foldr_finPrefix_eq_foldPrefix {N : ℕ} (g : Fin N → Bool) : ∀ (k : ℕ) (hk : k ≤ N),
    (finPrefix N k hk).foldr (fun f acc ↦ xor (g f) acc) false = foldPrefix g k hk := by
  intro k
  induction k with
  | zero =>
      intro _
      rfl
  | succ k ih =>
      intro hk
      simp only [finPrefix, List.foldr_append, List.foldr_cons, List.foldr_nil, Bool.xor_false]
      rw [foldr_xor_init, ih (by omega), foldPrefix, Bool.xor_comm]
def synBitRange (bad : Fin 654 → Bool) (r : Fin 18) (k : ℕ) (hk : k ≤ 654) : Bool :=
  foldPrefix (fun f ↦ bad f && gf8Code18Bit r f) k hk
theorem synXor18_triples_gen (x : Fin (2 ^ SpecsAux.SpecMirror.systemQubits)) (bad : Fin 654 → Bool)
    (hbad : ∀ (i : Fin 218) (w : Fin 3), bad ⟨3 * i.val + w.val, elecFieldIdx_lt i w⟩ = decide
    ((elecAxisWord6 x i w).val = 32)) (r : Fin 18) : ∀ (m : ℕ) (hm : m ≤ 218), ((finPrefix 218
    m hm).foldr (fun i acc ↦ elecSyn18 x i ^^^ acc) 0).testBit r.val = synBitRange bad r
    (3 * m) (by omega) := by
  intro m
  induction m with
  | zero =>
      intro _
      simp [finPrefix, synBitRange, foldPrefix]
  | succ m ih =>
      intro hm
      simp only [finPrefix, List.foldr_append, List.foldr_cons, List.foldr_nil, Nat.xor_zero]
      rw [foldr_nat_xor_init, Nat.testBit_xor, ih (by omega)]
      have hstep : synBitRange bad r (3 * (m + 1)) (by omega) =
          xor (bad ⟨3 * m + 2, by omega⟩ && gf8Code18Bit r ⟨3 * m + 2, by omega⟩)
            (xor (bad ⟨3 * m + 1, by omega⟩ && gf8Code18Bit r ⟨3 * m + 1, by omega⟩)
              (xor (bad ⟨3 * m, by omega⟩ && gf8Code18Bit r ⟨3 * m, by omega⟩)
                (synBitRange bad r (3 * m) (by omega)))) := by
        unfold synBitRange
        change foldPrefix _ ((3 * m + 2) + 1) _ = _
        simp only [foldPrefix]
      rw [hstep]
      have hb0 : bad ⟨3 * m, by omega⟩ = decide ((elecAxisWord6 x ⟨m, hm⟩ 0).val = 32) := by
        simpa using hbad ⟨m, hm⟩ 0
      have hb1 : bad ⟨3 * m + 1, by omega⟩ = decide ((elecAxisWord6 x ⟨m, hm⟩ 1).val = 32) := by
        simpa using hbad ⟨m, hm⟩ 1
      have hb2 : bad ⟨3 * m + 2, by omega⟩ = decide ((elecAxisWord6 x ⟨m, hm⟩ 2).val = 32) := by
        simpa using hbad ⟨m, hm⟩ 2
      have hite_tb : ∀ (c : Prop) [Decidable c] (v : ℕ),
          (if c then v else 0).testBit r.val = (decide c && v.testBit r.val) := by
        intro c _ v
        split_ifs with hc <;> simp [hc]
      have hel : (elecSyn18 x ⟨m, hm⟩).testBit r.val =
          xor (xor (bad ⟨3 * m, by omega⟩ && gf8Code18Bit r ⟨3 * m, by omega⟩)
                   (bad ⟨3 * m + 1, by omega⟩ && gf8Code18Bit r ⟨3 * m + 1, by omega⟩))
              (bad ⟨3 * m + 2, by omega⟩ && gf8Code18Bit r ⟨3 * m + 2, by omega⟩) := by
        unfold elecSyn18 gf8Code18Bit colsGF8_654
        dsimp only
        rw [Nat.testBit_xor, Nat.testBit_xor, hite_tb, hite_tb, hite_tb, hb0, hb1, hb2]
      rw [hel]
      generalize (bad ⟨3 * m, by omega⟩ && gf8Code18Bit r ⟨3 * m, by omega⟩) = u0
      generalize (bad ⟨3 * m + 1, by omega⟩ && gf8Code18Bit r ⟨3 * m + 1, by omega⟩) = u1
      generalize (bad ⟨3 * m + 2, by omega⟩ && gf8Code18Bit r ⟨3 * m + 2, by omega⟩) = u2
      generalize (synBitRange bad r (3 * m) (by omega)) = acc
      cases u0 <;> cases u1 <;> cases u2 <;> cases acc <;> rfl
theorem fullSyndrome18_testBit_eq_of_bad (x : Fin (2 ^ SpecsAux.SpecMirror.systemQubits))
    (bad : Fin 654 → Bool) (hbad : ∀ (i : Fin 218) (w : Fin 3), bad ⟨3 * i.val + w.val,
    elecFieldIdx_lt i w⟩ = decide ((elecAxisWord6 x i w).val = 32)) (r : Fin 18) :
    (fullSyndrome18 x).testBit r.val = gf8SynBitOfBad bad r := by
  have h1 := synXor18_triples_gen x bad hbad r 218 le_rfl
  rw [finPrefix_full 218] at h1
  change (fullSyndrome18 x).testBit r.val = _ at h1
  have h2 := foldr_finPrefix_eq_foldPrefix (fun f : Fin 654 ↦ bad f && gf8Code18Bit r f) 654 le_rfl
  rw [finPrefix_full 654] at h2
  exact h1.trans h2.symm
theorem xor_foldr_zip {α : Type} (L : List α) (g₁ g₂ : α → Bool) : xor
    (L.foldr (fun x a ↦ xor (g₁ x) a) false) (L.foldr (fun x a ↦ xor (g₂ x) a) false) =
    L.foldr (fun x a ↦ xor (xor (g₁ x) (g₂ x)) a) false := by
  induction L with
  | nil => rfl
  | cons x tl ih =>
      simp only [List.foldr_cons, ← ih]
      cases g₁ x <;> cases g₂ x <;>
        cases tl.foldr (fun y a ↦ xor (g₁ y) a) false <;>
        cases tl.foldr (fun y a ↦ xor (g₂ y) a) false <;> rfl
theorem foldr_xor_swap {α β : Type} (L₁ : List α) (L₂ : List β) (h : α → β → Bool) :
    L₁.foldr (fun x acc ↦ xor (L₂.foldr (fun y a ↦ xor (h x y) a) false) acc) false =
      L₂.foldr (fun y acc ↦ xor (L₁.foldr (fun x a ↦ xor (h x y) a) false) acc) false := by
  induction L₁ with
  | nil =>
      simp only [List.foldr_nil]
      induction L₂ with
      | nil => rfl
      | cons _ tl ih2 => simp [List.foldr_cons]
  | cons x tl ih =>
      simp only [List.foldr_cons, ih, xor_foldr_zip]
theorem f2Parity_gf8Syn_eq_foldr_colParity (meas : Fin 18 → Bool) (bad : Fin 654 → Bool)
    (syn : Fin (2 ^ 18)) (hsyn : ∀ r : Fin 18, decide (basisBits 18 syn r ≠ 0) =
    gf8SynBitOfBad bad r) : f2Parity 18 meas syn = (List.finRange 654).foldr
    (fun f acc ↦ xor (bad f && gf8Col18Parity meas f) acc) false := by
  unfold f2Parity
  have hcongr : (List.finRange 18).foldr (fun r acc ↦
    xor (meas r && decide (basisBits 18 syn r ≠ 0)) acc) false =
      (List.finRange 18).foldr (fun r acc ↦ xor (meas r && gf8SynBitOfBad bad r) acc) false := by
    congr 1
    funext r acc
    rw [hsyn r]
  rw [hcongr]
  have hand_fold : ∀ (c : Bool) {α : Type} (L : List α) (g : α → Bool),
      (c && L.foldr (fun x a ↦ xor (g x) a) false) =
        L.foldr (fun x a ↦ xor (c && g x) a) false := by
    intro c _ L g
    induction L with
    | nil => simp
    | cons x tl ih =>
        simp only [List.foldr_cons, ← ih]
        cases c <;> cases g x <;> cases tl.foldr (fun y a ↦ xor (g y) a) false <;> rfl
  have h1 : (List.finRange 18).foldr (fun r acc ↦ xor (meas r && gf8SynBitOfBad bad r) acc) false =
      (List.finRange 18).foldr (fun r acc ↦
        xor ((List.finRange 654).foldr (fun f a ↦
          xor (meas r && (bad f && gf8Code18Bit r f)) a) false) acc) false := by
    congr 1
    funext r acc
    unfold gf8SynBitOfBad
    rw [hand_fold (meas r) (List.finRange 654) (fun (f : Fin 654) ↦ bad f && gf8Code18Bit r f)]
  rw [h1, foldr_xor_swap]
  congr 1
  funext f acc
  congr 1
  unfold gf8Col18Parity
  rw [hand_fold (bad f) (List.finRange 18) (fun (r : Fin 18) ↦ meas r && gf8Code18Bit r f)]
  congr 1
  funext r a
  congr 1
  cases meas r <;> cases bad f <;> cases gf8Code18Bit r f <;> rfl
-- ============================================================================
-- Section 4: Base-`1024` Mod-`1023` Dual Code Weight Certificates (`2^18` Masks)
-- ============================================================================
/-- Base-`1024` packed bit-row for parity-check row `r ∈ [0..18)`. -/
def rowMask18Nat : ℕ → ℕ
  | 0 => 0x4010040100401000010000000001004010040100400004010000000001004000000000400004010040100400004010040100400000000000000401004000040000400004010000000000004010040000401004010040000400000000000100400000000040000401004000040000400000000000000001004000040000001004000000100401004000000100000004000000000001004000000100000000010000000401004000040000001000000000000000000010040000000000010040100400004010040100400000010000100001000010000100000004010000100400004010040100000004010040000400000010040100000000000040100401004010000100001000000000100001004010040000400000000000000000000010000100000000010000100401000010040100001004010000100400004010000100401004000040000001000000040000400000000040100001004010040100001004010040000400000000000100001000000040000400004010000100001000000000000001000010000000401004000000100401000010000000401000000040100001004010040000001000010040100001004010040100001000000000100400004000040000000004010040100400004000040000401004010040100401000000000100001004010000000400004010000100401000010040000400000010000000001004000040000000004000000100401004000040000001000000040100001000010040000000004000040100400000000000100401000010040000401004000000000400004010040000400000000000000400000000000000400004010040000001004010000100401000010040100401004010000000001004000000100401000000040000400004000040000401004000000000401000000040000001004000000000000004010000000001000000000000001004000000100401004000000100401004010040000000000010040100400004000000100400004010040100000000010040000001004000040000400004010040100400000010000000001004010000100400004000000100401000000040100401004010040000000000000000100001004000040000401
  | 1 => 0x4010000100000004000040000400000010000100401000000040000401004010040000001000000040100401004010000100001000000000000400000010000100001000010040000000004010000000001000010040000001000000000000401000010000000400000010000000001000000000100401000000040100400000000040100000004000040100401000000040000401004000040000001000010040100001000000040100001000000000000000000000040000000004010040100000004000040000400004010000000401004010040100400004000040100401000010000100001000010000100401004010040100401004010000000400000010000100400000000000000401000010000100000000000000000000000010040100400004000040000400004000000000400004010040000400004010040000001000010000000400000010040100400004000000000400000000040100000000010040100401000000000000401004000040000001004000000100400000000000100400004010000100001000010040100000000010040000400000010000100000004000000100000000000040100401004000000100000000000000000400000010040000000000000040000400000000040100400004000040100000000000000100400004000000000401004010040100001004000000100001000000040000400000010040000000000000040000401000000040000400000010000100400004010040000000000000040100401000000000000400004010000100401004010000100400000000040000001000000000000001000000000000401004000040100400004010040000400004000000000001000010000100400004010040100400004010040100001004000000100001004000040000400000010000100001000010040000000000010040000400000000000000401000010040000400000010000000001000000040000000004010040100001004000040000400004000040000401004010000100000004010000100400004000000100001000010040100401004010040100401004010000000400000010040100400004000040000000000000000000400004000000100400
  | 2 => 0x10040100400004000000100401004000000100000004000040100001004010000100400000010040000401000010000000001000000000100001004010000000401004000000000000004000040100401000010000100401000000000000400004000040100000000000040100401000000000100000000010000000401000010040000400004010000000400004010040100400004010040100400004010040000400000010000000401000000000000000004000000000000000000040100401004010000100001000000040100000004000000100001004000000000400004010000000400004010000000401000010000100001000010000100400004000040000400000000000000001004010000000001000000000000000004000040000001004000000000401004000040000401004000000000401004000000000401004000000100001004000000100001004010040100400004000000000400000010000000001000000000100401004010040100000000000040000001000000000000400004010040100000000010000000001004000000100401004010040100400000010000000400004010040000401000000040000401000000000000001004010040000000000010000100401004010000100000000010040000400000000000000001004000040100401000010000000001000000040000401004000000100001004010040000000004010040100400000010000100000004010000100401004010000000000000010040100000000000000100000000000040000400004000040100001000010000100400000000000100401000000000100400004000000100000004000000000401000010000000401004000040000400004010000000401004000040100000004010000100401004010000100400004000040100400000000040000000000010000100000000000000100001004000040100000000000040000400000010040000000004000040000400000010040100001000010040100400000000040100400000000040100401004010000100000004000000100001004000000100001000010040000001004000040100000004010000000000000000000100000004010040100000
  | 3 => 0x4010000100401000010040000400004000040100000000010000100001004000000000400004000040000400004000000000401004010040000401000000000100000000000000100000000000000000401004010040100400000010000100000004000000100000000000040000001000000040000401000000000000001004000000100401004000000100001000000040100001000000040000400004010000100401004000000100400000010000100000000010040100401004010000000000000000000100400004010040100400000010000000400004010040000001004000000000001000010000000400000010040000400000010040000400004010040000000000010040100400000000040000000004000000100000004000000000001004010000100400004000000100000000000040100000000010000100401000000040000401000010000000000000010000100000004010040100000000010040100401000000040100401004000000000400000000040100001000000000100400004010040000401004000040000001004010000000400000000040100401004000040000001004010040000001004010040000401000000000100400004010000100401000010000100001004000040100400004000040100000004000040100400004010000100000004000000000000000010000000000000010000000400000000040000001004000040000001000000000100401000000040000000000010000000400004010040100401000010040100400004010000100001000010000000000000000000000401000000000100401004000000100001004000040100000000010040000400000000000000000000000000100000000010040100401000010040000401004000000000001004010040100001000000000100001004010040000400004000040000400004000000100401004010000100401004000040100400000000000100000004010040100000000010040000401000010040000401004010000100001000000000100401000010000100000000010000100400004000000000400000010000000001004000040000000004000000100400004010000000001000000040000000
  | 4 => 0x4000040100000000010000100001004000000000400004010000100000004010040000001004010040100400000000040000001000010000000400000000000000400000000000100400000000000000001000010040000401004010000100401004010000100401004000000100400000010040100400000000000100400000000040100000004000040000401004010000000400004010040000401000010000100400000010000100000004000000100001000000040100400004000000000000000000000000400004000000100000004010040100001004010000000400004000040000400004000000100401004010040000401004000040100000004000000000000004010040000001000010040000000000010000100400000010000100001000010040100401000000040100001004000000000401004000040000001000010040100001004000000000000000000040100401000000040100400000000040100400004010040000400004010040000001004010040100400000000000100000004000040100001004000000100400004000040100001000010000100001000000040100000004000000100001004000000100400000000000000400004010040000001004000040100000000000040000400004010000100400004000000100401004000000000001000010040000000004010000000000000000040100401004000040100000004010040000400000000000000001000010000000000000010040100401004000040000401000010000100001004010040100000004000040000000000000000100400000000000100001004010040000001000000040100001000000040000001000000000000000000000000100401004010000100400000000040000400000010000000401004000000100401000000000000401000000040000001000010000100400000010040000001004010040000400004010040000400000000000100001000010000000001004010040000001004000000100001004010040100400000000000100001000010040000400000010040100001000010000000001000010040100400004000000000000004010040000400004010040000401004010040000000
  | 5 => 0x4000000100400004010040100400004010040100401004010040000401004010000100400004010000000001000010040100400004000000100001000000000100401000000000000401000000000100401000010000100000004010040000001004010040000400000010000100001004000000000400000000000000401000010040000400004010000000001000010040100000004000000100401000000040100000004000040100401004000040100400004000000100001004000040000000000000000100001004000040100001004000000100000000010040100400000010040100000000000040000401000010000100400004000000000001000000040000000004010000100001004000000000000004000040000001000000040100400000000040100001004010000100401004010000100400000010040000401004010000000001000000040000000004000040000001004000000100401004000040000401004000040000401000000040100000004000000000001000000000000401004010000100000004010040100000004010040100000004010040000001004010000000400000000040000400000000040100000000000000000001004000040100001000000040000401004010000100401004000000100001000010000100000004000040100400004000040000000004000040000000004000000100000004010000000401004000000100001000000000000401004010000000000004000000100000004000000000400004000000000001000010000100400004000000000000000000000000400000000000000001004010000100401000010040100400004000040100000000000000000000000000000100001004000000000401004010000100401000010040100400000000040100000000000000100401004000000100001004010000100001004010000000400000010000100000000010040100401000000000000401004010000100401004000040100401004000040000400000010000000001000000000100400004000040100001004000000000001004010040100000004000000000400000010040000000000010000100401004000040100400004000040000000
  | 6 => 0x40100401004010040100000004000000000400004010000000400004000040000401000010040100400000010040000400000010000100400000000000000401004010040000001000010000100400000000000000000004010040100001004000000000401004010040000000000000040000000004000040100000000010040000400000000000100400004000000100401000000000100401004010040100400000010040000000004010000000400004010000100000004010040100400004010000100001000000040100001000000000000001000010000000401004010040000401004010000100001000000000100001000000040000401000010040000000000000000000400000000040000001000000040000001004010040100001004010000000001000010000100401000010000100000004000000000401000010000100001004000000000001004000040000400000010040100001000000000000401004010000100001004000000000000000000040100001004010000100000004000000000000000010000000000000000040100000004010000100400000000000000001004000040000400004000000100400000010040000001004010040000000000010000000401000010040100401000010040000401004000040000401000010000100001004000040100001004010040100000004010040100001000000000100400000000040000400004000000000001000010040000001004000000100000004010040100000004000000100001000000040100000004000040000401004000040000400000000000100400004010040000401004010000100001000000000000001000010040000000004000000100401000000000000000004000040100400000010040000000000000000100400000000040000400000000000100001004010040000001000010040100400004010040100000004010000000000004010000000000000000000100000004000000100000000000000000401000000000100400000010040100001004000000000001004000040000401000000040000000000000000100000000000040100400004010000000001004010040000001000000040100001
  | 7 => 0x10040100000004000000000001000010040100001000000040100001004000000100400004000000100401004010040100400004010000100000000000000000001004000040100000004000000000400000000000000000004000040000400004010000000400000000040000000000010040000000000000040000001004010040100001000000000000001000000040100000000000000100001004000040000400004000000000000004000040100401000010040100401004010000100000000000040000401000010040000401000000000100401004010040100400000010000100000000000040000401000000000000001004010000100401000000040000000000000000100400000010040000401000010040100001004000000000401000010040100001000010040000401004000040000401000010000100000004010000100000004000040000400004010040100000000010000100000000000000100000004000040000401004010040000000004010040100400000010000100401004010040000000004010000000000004000000100400004000000000401000000000100000000010040000401004000040000400000000040100401000010000000000004000040100400000010000000001004000000000400004000000000001004000040100400000000040100000000000040000400000010000100000000000000000001004010000100401000010000000400004010000000401004010000100400004000040000400004010040100000000010000000400000000040100000004000000000001000000000000401000000040100001004010040000401000000000100001004000000000000004000040000400000000000000000004000000000401004010040000000000000000100001000010000000001000000000100401004010000000400004000040000400004000040000401000000040000000000010040000000000000000000001004000040100001000000000100001000000000100401000000040000401000010000000401000010000000001004000000000000000000000100401000010040000400000000040000401000010000000401004010040100000
  | 8 => 0x4010040100400000010000000401000010000000401004000040000001000010040000400000000040000401000000040000401000010040100401000000000100001000000040000400000010040100001000000000000000004010000100400004010040100000004000040000000004000000000000000010000100401000000040100000000000000100001004010040100001000000000000401000010040000401004010000000000000010000000401000010000000001000010000100401004000040000400004010000100000000000000000401000000040000001004010000000001000010000000400000000000100401000010000100001004010040000000000000000100401004000000100000004010040100400004010000100401000000040100400004010040100001000010040100400004010040000001000000040000400000010040100000000000040000401004000040000400000000000100400000000040100401000000040000000004000000000001000010040100001000010000000000000010040000000000010000100001004000040100000000000000000400000010000100001004010000100401004010000000400000010040000000000000040100000004010040000400004000040100401000010000100001004010000100000000010040100400000010040100401000010040000400000000000100001000010040100000004000040100000000000040100000000010040100401004000000100401000010000100401004010000000401004010000000001000010040100400000000000100000000010000100000000010000000400000000000100400000010000000000004010000000001000000000000000004010040000001000010000000000000000000000400004000040100000000000000000001004000040100000000010000100401004000000000400004000000000000004010040000000000000000100401000010040100400000000000000400000000000100000004000040000001000000040100401000000040100400004010000000000000000000100001004000040000401004000040100001000010040100400004000040000401
  | 9 => 0x4000040100400000010040100400000010040100001000010000000000000010040100000004000040000401004010000100000000010000100400004000000000400004000040100400000000040100400004000040000401004010000100401004010040000401000000000100000000010000100401000000040000401004010040100400004010000000000004000040100000000010040000400000010040100001000000040000401004000000100001004000000000401000010000100001004010040000000004000000000400004000000100000000010000100401004010040000401004010040100400004010000000001004010040100000000000040000000000000040000000004010000000401000000040100400004010000000401000000000100400000010000100000000000000100000004000000000401000010000000001000000040000001000000040000000004000040000400004010000000400004010000000401004010000000400000010040100400004010000000401000010000000000004010040100001000000000100000004000040100001004000000000401004010000100400004000040100401004010040100401004000000000001000000000100000000010000000001004010040000000000010000100401004000000100401004000000100400000010040100000004000040100001004000000100400000000040100000004010000000400000010040100000000000040000001000000040000000004000040100000004000000100000004000000100401000000000000000004000000000400004000000000000004000000000000004000040100401004000040000401004010040000400000010000100400004000000000401004000040000400000000040100400004000000000401000000000000401000000000100401000000000100400000000040100400004010040100001000000000000000000000040000000000010000000400000010040100400004010000000401004010000000401004010000100001000010000000000000010040000401000010040100001000000040000001000000040100400000000040100000004000000000400
  | 10 => 0x40000001000010000100000000000040100400004010000000000004010000100001004010040100001004000000000401004010000100000004010040100001004000000100001004000040000400004010000100401000000040100400000010040000400000000000000400004000000000401000010040000400004010000000401000010000000000004010040000001004010000000401004000000100401000010040000400000000040000401004010040000001004000040100400004000040000000000000040100001004010000100400004010040100001000010000100000000010000000400000010040100400000010000100001004010000000000004000000000000000000040100401000010040100401000000040100000000000000100401000010040100001000000000000401000010000100000004010000000400000010040000400004000000000000004010000100401004010040100401004000040100000000010040000001004010000100401000010000100001004010000000000000010000000401000000000100400000010040100000004010000100401000010000000001000010040000001000010000100001004010000100000000000000100401004000040000401004000040000000004010040000401000000040100001000010040000401004000000000400000010040100000004010000000001004010000100400004000040100400004010000100001004000000000400000010000000000000010040000401000010040000400004010000000001000000000000000000010000000001004010040000000000010040000000004010000000400000010040100000004000000000401004000040100001000010040000400004000000100400004010000100001004010000100000000000000100001000000000000001000000000000400000010000100001004000000100000000000000000000000010040000000004000000100401004000000000400004010040000001004010040000400000000040000001000010040000000000000040100000004010040000001000010040100000004000000000400004000040000001000010040100001
  | 11 => 0x10000100000004010040100001004010000000001004010040000000004000000100401004010000100401004000040000400000010040100401000000040000401004010000100401004010040100001000000040000400004000040100001004010000100000000000000000401000000040100001004010040100400000010000000001004000040000000004000000000400000010000100401004000040000001004010040100001004010040000400000000040100000004010000000400004010000000000000010000100400004010040100001000000040100000004010000000001004010000100001004000000000400000000040000401004000000000000000010000000000000010000100001004010040100001004000000000400000000000100001004010040100401000000000100400004010040000001000000040100001004000000100000004010040000000000010000100000004000000000001000000040000400000010000100000000010000100000000010040100000004010040000000004000000000400000000000100001004000000100400004000040100400004000040100000000010000000400004000000000401000000040000400000000000100400004000000100001000010040000000004000000000400000010040000401004000040100000000000040100401004010040000400000000040100001000010040100401004000000100001000000040000401000010000100001004010000000000000000040000400004000040000401004000040000401000000000000000000000040100401004010000000000004000040000000000000040000401004010040000001000000040100400000000040100000000010000100401004010000000001004000000000400004010040000400000000000000400000000000000401000000000100401004010000000001004010000000401000000000000000004000000000000000000040000401004000040000401000010000100001004000000100000004000000000400004000000000000004000040000400004010000100401004000040100401000010040100401004010000000400000010000000001
  | 12 => 0x10040000001000000040000400000000000100000000010040100000004010040000001004010000100400004010000000401000010040000000000010040000401000010040000400000000040100001000000040000400004010040100401000010040000400004000040000000004010040000000000000040000000004010040100400000000000000001000000040100401004000040000401000000000100400000000040100401000000000000400004000040100400000000040000401000000040100400000000040000400000010000100400000000040100001000010000100000000000000100400000000040000400004010000100001004000040100000000000000100001000010000000401000000000100401000000040100001000010000100401000000040100000004000040100400004000040000400004000000100401000000040100401004000000000400004000000100401004010000100000000000000100401000000000000001000000040000400004000000100000004000040100001000000000000401000010000000001004000040100400004000000000000000010000100400004010000000400000010040000401004000040100001000010000000001000000000100000000010040100401004000040100401004000000000000000000040000000000010000000400004000040100000004000000000401004000000100401000000000100400000000000100401000000040100000000000000000000000000000000401004010000100400004010040100400000000040100401000000040000001004000040100000000000040000401000010040100001004000040000400004010000000400000010000000400000000000100400000010040000400004010000000400004000040000401000010000100400004010000100401000010000100000004010040000000004000000000001000000000000401000000040100401004000040000400004000000000000000010000100400004010000100400004010000000400004010000000001000000000100401004000000100401000010040100000004010040000401000000040000000004000040100400
  | 13 => 0x4000000100001004010040100001000000000000400000010000100401000000040100401000010040100401004000000000001000000040000000000000040000001004010040000401004000040000401004000000000001004000040100400004000040100400000010000000000000010000000000000010040000000004010000000401000000000100000004010000100000000010000100000000000000000400000010040000001000000000100401000010000000401000010000000400004000000000400000010040100001004010040000401000010040000001004000000100001000000000000400004010000000401004000000100400000010040000401000000000000401004000000100401000000000000400004000040000401004000040000400004010040100001004010000000400004010000100400000000040000401000010040000001000010040100000000010040000401004010040000400000000000000400000000000100001004010040100001000010040100401000010040000001000000000000001000010040100401000010040000401004010000000000004010040000001000010000100001000000040100000000010040000400004000040000401000000000100401004000000100000004000000000401000000040000000000010000000000004010000100001000010040100400004010000000400000000040000401000000000000401000000000000400004000000100400000000000000000000000000000001004010040000401004000000000401000010040000401004000040100400004000000100401000010000000001000000040000401000010040100400000010000000401004000040100401000000000000401004010040100400000010000100000004000000100000004010040000400000010040000001000000040100401004000040000000000010000000401000000000100401000010040000401004010000100401000000040000000004000000100401004010040000001000000040100401004000040100401000000000000400004010000000400004010000000401004000040100400004000040000000004000000000400
  | 14 => 0x4010000000400000010040100400000000000100401004000000100400000010000100000004010040000401004000040100400004010000000000004000000100001000010000100000004010040000400004010000100401004010000100001000000040100401000000040000000004010000000000004010040000000000010000000001000000000000401000010040100001000010040100001000000000000401004010040100000000000000000401004010000000400004010040100001000010040100001004010000100400004000000000001004010040000401000000040000400000000000100001004000040100400000010040100401000010000000001000000000000001000000040100001000000000000401000010000100401004000000000401000010000100401000000040000401000000040100001000010000100400004000000000401004010000000401000000040100400004000000100001000000000000401000000000100400004000000000401004010000100001000000040100401000000000100401004000000000401004000000100000004000040000000000010040100000004000040000001004010000100001004010040000001000000040100001000000000100400004000040000400000010000000400000010040000000004010000000000004000040000401004010040100401000000040100000004010040100400000000000100401000000000100400000010000100401000000000000000000000000100400000010000100000000010000100401004000040100001000010000100001000010040100001004010000100401004000040100401004010040100001004000040100400000000040000001000000000000001000010000000001004000040100001000010000000400004010000000401000010000000401004000040100400004000000000000000000040100001000000000100001004000000000001004010040000401004010000000000004010040100000004000000100001004000000000001004010040100001000000000000401000010040000001004000000100400004010000100000004010000000000004010040100401
  | 15 => 0x10040000400004010000100001004010000100000000000040100401004010040000001000000040100000004000000000000000010040000400004010000100400000000000100400000010000000400004010000000401000000040000401004000040000000000000040100000000000040100400000000040100000000000000000400000010040000400004000040000001000010000100001004010000000400000010040100000000000040000001004010040100400004000040100000004000000100400000010000000001004000000000001000000040000400004000040000001004000000100400004010000100401000010040000000000010000100400004010000100401004010000000400000010000100400004000000100001000000040000000000000040000001000000000100000000010040000000000000000100401000000040100400000000040000000004000000100000004000040000001000000040000401004000040100400004010000000001000010000000000004010040100400004000040100000004010000000401000010040000001000000040000401000010000000000000010000000400000000040000401000000000100001004010000000401004010040100400000000040100001004000000000001004000000100001000010000000001004010000100001000010000000000004010040000400000000000000001000010000100001000010000000401000000040100400000010040000000004000000000001004000040100001000000040000001000010000000001004000000100400000000000100400000010000000400004010040100000004000000000000000010040000400004010040000001004000000000401000000000000001004010000100000000000040000001004000040000400000000040000401000010000000000004000000000401000010040100400004000040100401000000040000000000000040000400000000040100000004010000100000000000000000401000010040100000000000040100001004000040100400004000040100400004010040000000000000000100000004000000000000000000000100400
  | 16 => 0x4000000000401000010040000401004000040000400004000000000001000000040100401000010000000001000000040000000000000040100401000010040100401000000000100001004000000100401004010040100401004000000000001004000000000000004000000000400000010040100000000010040000001000000000100001000000040100400004010040000401000000040100400000010000000001004000000000401004010000100400004010000000401000010040000401004010040000400004010000000400004010000100401000010040100000004010000000400004000040000400000010040000400004000040000000004010040100000004000040100001000000040100000004010040100401000010000000401004010040000000004010040100401000000000000401000000040000000000000000000401000010040000401004000000000000000010040100400004010000000401004010040100000000010000100401004000000100000000000040000000004000040100000004000000100001004000040000400004010040100400004010040100401004010040000000004010040100001004010040100000000000000000400000010000100400004000000000400004010040000001004010000100000000000040100400004000000100400000010040100400000000040000000000010000100400000000000000400004010040100401004000000100401004000000000001004010000000000004010040100401000000040100000004010040000400004000040100401000010000000401000000000100000004000000100401000010040100400004010000000000000000040000401000000040000401000010040000400000000000000401000010000000001000010000100001004010000000001004000040100000000000040000000000010040000001004010000000400004010040000400000010040000000000010040100401004010040000401004010040000400000000000000400004010000000400004000000100000004010000100401000010000100000000000040000000000000000100401004010000000000000000000000400
  | 17 => 0x4010000100001000000040100000000000040100401000010040000400000010000100000004000000000400000010040000000004010000100400000010000100000000000000100401000010040000401004000000000400000010040100000000010000000000000010000000401004000000000001004010040100401000000000100000004010040100401004000000100400004010000100000000000040100001004010000000001000010040100000004000040000400004000000000001000010000100001000000040100401004010040000401004010040100401004010040100000000010040100001004000000000001004000000000000000010040100401004010040100400000010000000001000000040100001000000040100401000010040000000000010000100000000000000100400004000040000000000000000100400004000000100401004010040000000000000040100401000000040100401004000040000400004010000100001000000040100400004000040000000004010000000401004010040100400004010040100401000000040100001000010040100400000010040000000000010040000001004000040100001000000000000001004010040100000000010000100401000010000100400004010040100400000010040100000004010040100001004010040000001004000000000000000010040100401000000000100001000000040100400004010040100001000010000000401000000040000000000010000100001000010040100400000010040100000000000040100000000000040100000000000000000401004010040000401000010000000001000000040000000004010040100400000010000100401000010000100401000000000100400004000040100401004000040100400000010000100001004010040000001004000040000000004000040100400004010040100401004010000100400004000000000000004000000000401000010000100400000010000100401000000000100000004010040100001000010000100401000000040100001000000040000401000010000000000000000000100400000000040000000000000000100401
  | _ => 0
def leafAll7 (acc : ℕ) : Bool :=
  Nat.ble (acc % 1023) 358 ||
  (Nat.ble (acc % 1023) 373 &&
   Nat.ble ((acc >>> 40) % 1023) 370 &&
   Nat.ble ((acc >>> 70) % 1023) 368 &&
   Nat.ble ((acc >>> 130) % 1023) 363 &&
   Nat.ble ((acc >>> 170) % 1023) 362 &&
   Nat.ble ((acc >>> 240) % 1023) 360 &&
   Nat.ble ((acc >>> 280) % 1023) 358)
def checkDualTree18 : ℕ → ℕ → Bool
  | 0, acc => leafAll7 acc
  | k + 1, acc => checkDualTree18 k acc && checkDualTree18 k (acc ^^^ rowMask18Nat k)
theorem cert_dual_0 : checkDualTree18 15 0 = true := by decide
theorem cert_dual_1 : checkDualTree18 15 (rowMask18Nat 15) = true := by decide
theorem cert_dual_2 : checkDualTree18 15 (rowMask18Nat 16) = true := by decide
theorem cert_dual_3 : checkDualTree18 15 (rowMask18Nat 15 ^^^ rowMask18Nat 16) = true := by decide
theorem cert_dual_4 : checkDualTree18 15 (rowMask18Nat 17) = true := by decide
theorem cert_dual_5 : checkDualTree18 15 (rowMask18Nat 15 ^^^ rowMask18Nat 17) = true := by decide
theorem cert_dual_6 : checkDualTree18 15 (rowMask18Nat 16 ^^^ rowMask18Nat 17) = true := by decide
theorem cert_dual_7 : checkDualTree18 15 (rowMask18Nat 15 ^^^ rowMask18Nat 16 ^^^ rowMask18Nat 17) =
    true := by decide
/-- `dite`-free `Nat`-indexed base-`1024` packer for fast kernel verification of `rowMask18Nat`. -/
def packRangeNat (g : ℕ → Bool) : ℕ → ℕ → ℕ
  | _, 0 => 0
  | lo, k + 1 => (if g lo then 1 else 0) + 1024 * packRangeNat g (lo + 1) k
def packRange (g : Fin 654 → Bool) : ℕ → ℕ → ℕ
  | _, 0 => 0
  | lo, k + 1 =>
      (if h : lo < 654 then (if g ⟨lo, h⟩ then 1 else 0) else 0) +
        1024 * packRange g (lo + 1) k
theorem packRangeNat_eq_packRange (r : Fin 18) :
    ∀ (lo k : ℕ), lo + k ≤ 654 →
      packRangeNat (fun j ↦ (colsGF8Nat j).testBit r.val) lo k = packRange (gf8Code18Bit r) lo k
  | _, 0, _ => rfl
  | lo, k + 1, hle => by
      have hlo : lo < 654 := by omega
      simp only [packRangeNat, packRange, dite_eq_left hlo,
        packRangeNat_eq_packRange r (lo + 1) k (by omega), gf8Code18Bit, colsGF8_654]
def countRange (g : Fin 654 → Bool) : ℕ → ℕ → ℕ
  | _, 0 => 0
  | lo, k + 1 =>
      (if h : lo < 654 then (if g ⟨lo, h⟩ then 1 else 0) else 0) +
        countRange g (lo + 1) k
theorem packRange_false : ∀ lo k : ℕ, packRange (fun _ ↦ false) lo k = 0
  | _, 0 => rfl
  | lo, k + 1 => by simp [packRange, packRange_false (lo + 1) k]
theorem packRange_xor (g₁ g₂ : Fin 654 → Bool) :
    ∀ lo k : ℕ, (packRange g₁ lo k ^^^ packRange g₂ lo k) =
      packRange (fun f ↦ xor (g₁ f) (g₂ f)) lo k
  | _, 0 => Nat.xor_self 0
  | lo, k + 1 => by
      simp only [packRange]
      have ha1 : (if h : lo < 654 then (if g₁ ⟨lo, h⟩ then 1 else 0) else 0) < 2 ^ 10 := by
        split_ifs <;> decide
      have ha2 : (if h : lo < 654 then (if g₂ ⟨lo, h⟩ then 1 else 0) else 0) < 2 ^ 10 := by
        split_ifs <;> decide
      change ((_ + 2 ^ 10 * _) ^^^ (_ + 2 ^ 10 * _)) = _ + 2 ^ 10 * _
      rw [add_two_pow_mul_xor 10 ha1 ha2, packRange_xor g₁ g₂ (lo + 1) k]
      congr 1
      by_cases hlo : lo < 654
      · rw [dite_eq_left hlo, dite_eq_left hlo, dite_eq_left hlo]
        have hbit : ∀ b₁ b₂ : Bool,
            (((if b₁ then 1 else 0) : ℕ) ^^^ (if b₂ then 1 else 0)) =
              if xor b₁ b₂ then 1 else 0 := by decide
        exact hbit (g₁ ⟨lo, hlo⟩) (g₂ ⟨lo, hlo⟩)
      · rw [dite_eq_right hlo, dite_eq_right hlo, dite_eq_right hlo]
        exact Nat.xor_self 0
theorem packRange_div_pow (g : Fin 654 → Bool) :
    ∀ (p lo k : ℕ), p ≤ k →
      packRange g lo k / 1024 ^ p = packRange g (lo + p) (k - p)
  | 0, lo, k, _ => by simp
  | p + 1, lo, 0, hp => absurd hp (by omega)
  | p + 1, lo, k + 1, hp => by
      have hstep : packRange g lo (k + 1) / 1024 = packRange g (lo + 1) k := by
        simp only [packRange]
        have ha : (if h : lo < 654 then (if g ⟨lo, h⟩ then 1 else 0) else 0) < 1024 := by
          split_ifs <;> decide
        rw [Nat.add_mul_div_left _ _ (by decide : 0 < 1024), Nat.div_eq_of_lt ha, zero_add]
      rw [pow_succ', ← Nat.div_div_eq_div_mul, hstep,
          packRange_div_pow g p (lo + 1) k (by omega)]
      congr 1 <;> omega
theorem packRange_shiftRight (g : Fin 654 → Bool) (p : ℕ) (hp : p ≤ 654) :
    (packRange g 0 654) >>> (10 * p) = packRange g p (654 - p) := by
  rw [Nat.shiftRight_eq_div_pow, pow_mul, show (2 ^ 10 : ℕ) = 1024 from rfl,
      packRange_div_pow g p 0 654 hp, zero_add]
theorem countRange_le (g : Fin 654 → Bool) : ∀ lo k : ℕ, countRange g lo k ≤ k
  | _, 0 => le_rfl
  | lo, k + 1 => by
      simp only [countRange]
      have ih := countRange_le g (lo + 1) k
      split_ifs <;> omega
theorem packRange_mod_1023 (g : Fin 654 → Bool) :
    ∀ lo k : ℕ, packRange g lo k % 1023 = countRange g lo k % 1023
  | _, 0 => rfl
  | lo, k + 1 => by
      simp only [packRange, countRange]
      let a := if h : lo < 654 then (if g ⟨lo, h⟩ then 1 else 0) else 0
      let B := packRange g (lo + 1) k
      change (a + 1024 * B) % 1023 = (a + countRange g (lo + 1) k) % 1023
      have h1024 : a + 1024 * B = (a + B) + 1023 * B := by ring
      rw [h1024, Nat.add_mul_mod_self_left, Nat.add_mod, packRange_mod_1023 g (lo + 1) k,
        ← Nat.add_mod]
theorem packRange_shift_mod_eq_countRange (g : Fin 654 → Bool) (p : ℕ) (hp : p ≤ 654) :
    ((packRange g 0 654) >>> (10 * p)) % 1023 = countRange g p (654 - p) := by
  rw [packRange_shiftRight g p hp, packRange_mod_1023]
  exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (countRange_le g p (654 - p)) (by omega))
theorem countRange_add (g : Fin 654 → Bool) :
    ∀ (a d₁ d₂ : ℕ), countRange g a d₁ + countRange g (a + d₁) d₂ = countRange g a (d₁ + d₂) := by
  intro a d₁ d₂
  induction d₁ generalizing a with
  | zero => simp [countRange]
  | succ d₁ ih =>
      rw [show d₁ + 1 + d₂ = (d₁ + d₂) + 1 by omega]
      simp only [countRange]
      have h := ih (a + 1)
      rw [show a + 1 + d₁ = a + (d₁ + 1) by omega] at h
      rw [Nat.add_assoc, h]
theorem countRange_mono_suffix (g : Fin 654 → Bool) {p : ℕ} (hp : p ≤ 654) :
    countRange g p (654 - p) ≤ countRange g 0 654 := by
  have h := countRange_add g 0 p (654 - p)
  rw [zero_add, Nat.add_sub_cancel' hp] at h
  omega
theorem countRange_one (g : Fin 654 → Bool) (k : ℕ) (hk : k < 654) :
    countRange g k 1 = if g ⟨k, hk⟩ then 1 else 0 := by
  simp [countRange, hk]
theorem countRange_eq_filter_len (g : Fin 654 → Bool) (p : ℕ) (hp : p ≤ 654) : countRange g p
    (654 - p) = ((List.finRange 654).filter fun f ↦ decide (p ≤ f.val) && g f).length := by
  have haux : ∀ (k : ℕ) (hk : k ≤ 654), p ≤ k → ((finPrefix 654 k hk).filter fun f ↦ decide (p
      ≤ f.val) && g f).length = countRange g p (k - p) := by
    intro k
    induction k with
    | zero =>
        intro _ hp0
        have hpz : p = 0 := by omega
        subst hpz
        rfl
    | succ k ih =>
        intro hk hpk1
        by_cases hpk : p ≤ k
        · simp only [finPrefix, List.filter_append, List.length_append, List.filter_cons,
            List.filter_nil, ih (by omega) hpk]
          rw [show k + 1 - p = (k - p) + 1 by omega, ← countRange_add g p (k - p) 1,
              Nat.add_sub_cancel' hpk, countRange_one g k hk]
          congr 1
          by_cases hgk : g ⟨k, hk⟩ = true <;> simp [hpk, hgk]
        · have hpeq : p = k + 1 := by omega
          subst hpeq
          have hnil : ((finPrefix 654 (k + 1) hk).filter fun f ↦
            decide (k + 1 ≤ f.val) && g f) = [] := by
            rw [List.filter_eq_nil_iff]
            intro f hf
            obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hf
            rw [finPrefix_getElem]
            rw [finPrefix_length] at hi
            simp
            omega
          rw [hnil, Nat.sub_self]
          rfl
  have hfull := haux 654 le_rfl hp
  rw [finPrefix_full 654] at hfull
  exact hfull.symm
/-- Bundled dual-codeword weight bound on unheld fields `[p_held .. 654)`. -/
def ValidGF8HeldPair (p_held wt_max : ℕ) : Prop := p_held ≤ 654 ∧ ∀ meas : Fin 18 → Bool,
    ((List.finRange 654).filter fun f ↦ decide (p_held ≤ f.val) && gf8Col18Parity meas
    f).length ≤ wt_max
theorem rowMask18Nat_eq_packRangeNat_check :
    (List.finRange 18).all (fun r ↦
      decide (rowMask18Nat r.val = packRangeNat (fun j ↦
        (colsGF8Nat j).testBit r.val) 0 654)) = true := by
  decide
theorem rowMask18Nat_eq_packRange (r : Fin 18) :
    rowMask18Nat r.val = packRange (gf8Code18Bit r) 0 654 := by
  have hc :=
    of_decide_eq_true (List.all_eq_true.mp rowMask18Nat_eq_packRangeNat_check r (List.mem_finRange
    r))
  exact hc.trans (packRangeNat_eq_packRange r 0 654 (by decide))
def rowXorBelow : ℕ → (ℕ → Bool) → ℕ
  | 0, _ => 0
  | k + 1, m => (if m k then rowMask18Nat k else 0) ^^^ rowXorBelow k m
theorem checkDualTree18_sound :
    ∀ (k acc : ℕ), checkDualTree18 k acc = true →
      ∀ (m : ℕ → Bool), leafAll7 (acc ^^^ rowXorBelow k m) = true
  | 0, acc, hok, _ => by simpa [checkDualTree18, rowXorBelow] using hok
  | k + 1, acc, hok, m => by
      obtain ⟨h0, h1⟩ := Bool.and_eq_true_iff.mp hok
      simp only [rowXorBelow]
      cases hmk : m k
      · simp only [Bool.false_eq_true, ↓reduceIte, Nat.zero_xor]
        exact checkDualTree18_sound k acc h0 m
      · simp only [↓reduceIte, ← Nat.xor_assoc]
        exact checkDualTree18_sound k (acc ^^^ rowMask18Nat k) h1 m
theorem leafAll7_rowXorBelow_18 (m : ℕ → Bool) : leafAll7 (rowXorBelow 18 m) = true := by
  have hsplit : rowXorBelow 18 m = ((if m 15 then rowMask18Nat 15 else 0) ^^^ (if m 16 then
      rowMask18Nat 16 else 0) ^^^ (if m 17 then rowMask18Nat 17 else 0)) ^^^ rowXorBelow 15 m
      := by
    simp only [rowXorBelow]
    ac_rfl
  rw [hsplit]
  cases m 15 <;> cases m 16 <;> cases m 17 <;>
    simp only [Bool.false_eq_true, ↓reduceIte, Nat.zero_xor, Nat.xor_zero]
  · simpa [Nat.zero_xor] using checkDualTree18_sound 15 0 cert_dual_0 m
  · exact checkDualTree18_sound 15 (rowMask18Nat 17) cert_dual_4 m
  · exact checkDualTree18_sound 15 (rowMask18Nat 16) cert_dual_2 m
  · exact checkDualTree18_sound 15 (rowMask18Nat 16 ^^^ rowMask18Nat 17) cert_dual_6 m
  · exact checkDualTree18_sound 15 (rowMask18Nat 15) cert_dual_1 m
  · exact checkDualTree18_sound 15 (rowMask18Nat 15 ^^^ rowMask18Nat 17) cert_dual_5 m
  · exact checkDualTree18_sound 15 (rowMask18Nat 15 ^^^ rowMask18Nat 16) cert_dual_3 m
  · exact checkDualTree18_sound 15 (rowMask18Nat 15 ^^^ rowMask18Nat 16 ^^^ rowMask18Nat 17)
      cert_dual_7 m
def colParPrefix (meas : Fin 18 → Bool) (k : ℕ) (hk : k ≤ 18) (f : Fin 654) : Bool :=
  foldPrefix (fun r ↦ meas r && gf8Code18Bit r f) k hk
theorem rowXorBelow_eq_packRange (meas : Fin 18 → Bool) : ∀ (k : ℕ) (hk : k ≤ 18), rowXorBelow
    k (fun r ↦ if hr : r < 18 then meas ⟨r, hr⟩ else false) = packRange
    (colParPrefix meas k hk) 0 654 := by
  intro k
  induction k with
  | zero =>
      intro _
      exact (packRange_false 0 654).symm
  | succ k ih =>
      intro hk
      have hk' : k < 18 := hk
      simp only [rowXorBelow, dite_eq_left hk', ih (by omega)]
      have hrm := rowMask18Nat_eq_packRange ⟨k, hk'⟩
      dsimp only at hrm
      have hlhs : (if meas ⟨k, hk'⟩ then rowMask18Nat k else 0) =
          packRange (fun f ↦ meas ⟨k, hk'⟩ && gf8Code18Bit ⟨k, hk'⟩ f) 0 654 := by
        cases meas ⟨k, hk'⟩
        · simp [packRange_false]
        · simpa using hrm
      rw [hlhs, packRange_xor]
      rfl
theorem colParPrefix_18_eq_gf8Col18Parity (meas : Fin 18 → Bool) (f : Fin 654) :
    colParPrefix meas 18 le_rfl f = gf8Col18Parity meas f := by
  have h1 := foldr_finPrefix_eq_foldPrefix (fun r : Fin 18 ↦ meas r && gf8Code18Bit r f) 18 le_rfl
  rw [finPrefix_full 18] at h1
  exact h1.symm
theorem dual_weights_all7 (meas : Fin 18 → Bool) :
    let P := gf8Col18Parity meas
    ((List.finRange 654).filter fun f ↦ decide (28 ≤ f.val) && P f).length ≤ 358 ∧
    ((List.finRange 654).filter fun f ↦ decide (24 ≤ f.val) && P f).length ≤ 360 ∧
    ((List.finRange 654).filter fun f ↦ decide (17 ≤ f.val) && P f).length ≤ 362 ∧
    ((List.finRange 654).filter fun f ↦ decide (13 ≤ f.val) && P f).length ≤ 363 ∧
    ((List.finRange 654).filter fun f ↦ decide (7  ≤ f.val) && P f).length ≤ 368 ∧
    ((List.finRange 654).filter fun f ↦ decide (4  ≤ f.val) && P f).length ≤ 370 ∧
    ((List.finRange 654).filter fun f ↦ decide (0  ≤ f.val) && P f).length ≤ 373 := by
  intro P
  have hleaf := leafAll7_rowXorBelow_18 (fun r ↦ if hr : r < 18 then meas ⟨r, hr⟩ else false)
  rw [rowXorBelow_eq_packRange meas 18 le_rfl,
      show colParPrefix meas 18 le_rfl =
        P from funext (colParPrefix_18_eq_gf8Col18Parity meas)] at hleaf
  unfold leafAll7 at hleaf
  have h0  := packRange_shift_mod_eq_countRange P 0  (by decide)
  have h4  := packRange_shift_mod_eq_countRange P 4  (by decide)
  have h7  := packRange_shift_mod_eq_countRange P 7  (by decide)
  have h13 := packRange_shift_mod_eq_countRange P 13 (by decide)
  have h17 := packRange_shift_mod_eq_countRange P 17 (by decide)
  have h24 := packRange_shift_mod_eq_countRange P 24 (by decide)
  have h28 := packRange_shift_mod_eq_countRange P 28 (by decide)
  change (Nat.ble (_ % 1023) 358 ||
    (Nat.ble (_ % 1023) 373 &&
     Nat.ble (((_ >>> (10 * 4)) % 1023)) 370 &&
     Nat.ble (((_ >>> (10 * 7)) % 1023)) 368 &&
     Nat.ble (((_ >>> (10 * 13)) % 1023)) 363 &&
     Nat.ble (((_ >>> (10 * 17)) % 1023)) 362 &&
     Nat.ble (((_ >>> (10 * 24)) % 1023)) 360 &&
     Nat.ble (((_ >>> (10 * 28)) % 1023)) 358)) = true at hleaf
  rw [show (packRange P 0 654) % 1023 = ((packRange P 0 654) >>> (10 * 0)) % 1023 from rfl,
      h0, h4, h7, h13, h17, h24, h28] at hleaf
  rw[← countRange_eq_filter_len P 28 (by decide), ← countRange_eq_filter_len P 24 (by decide),
      ← countRange_eq_filter_len P 17 (by decide),
      ← countRange_eq_filter_len P 13 (by decide), ← countRange_eq_filter_len P 7 (by decide),
      ← countRange_eq_filter_len P 4 (by decide), ← countRange_eq_filter_len P 0 (by decide)]
  simp only [Bool.or_eq_true, Bool.and_eq_true, Nat.ble_eq] at hleaf
  rcases hleaf with hfast | ⟨⟨⟨⟨⟨⟨hw0, hw4⟩, hw7⟩, hw13⟩, hw17⟩, hw24⟩, hw28⟩
  · have hfast' : countRange P 0 654 ≤ 358 := hfast
    exact ⟨(countRange_mono_suffix P (p := 28) (by decide)).trans hfast',
           (countRange_mono_suffix P (p := 24) (by decide)).trans (hfast'.trans (by decide)),
           (countRange_mono_suffix P (p := 17) (by decide)).trans (hfast'.trans (by decide)),
           (countRange_mono_suffix P (p := 13) (by decide)).trans (hfast'.trans (by decide)),
           (countRange_mono_suffix P (p := 7)  (by decide)).trans (hfast'.trans (by decide)),
           (countRange_mono_suffix P (p := 4)  (by decide)).trans (hfast'.trans (by decide)),
           hfast.trans (by decide)⟩
  · exact ⟨hw28, hw24, hw17, hw13, hw7, hw4, hw0⟩
/-- `p_held = 28` (`112` held ancillas): max suffix dual weight `358` (`19,216 T` floor). -/
theorem validGF8HeldPair_13_363 : ValidGF8HeldPair 13 363 :=
  ⟨by decide, fun meas ↦ (dual_weights_all7 meas).2.2.2.1⟩
end ConfigGF8Core
end GF8Code18Guard19300
end
end GF8Code18Core

end QuantumComputation.Specs.StoppingPowerSolution
end
