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

public import QuantumComputation.Circuits.DynamicCircuit

import QuantumComputation.Circuits.ResourceCounting
import QuantumComputation.Circuits.Examples.Bell

/-!
# Examples of gate counting

Per-gate counts and total sizes of small circuits, including inverses (which are counted through
their implementation in primitive gates) and relocated subcircuits.
-/

@[expose] public section

open scoped Circuit.Notation

namespace Circuit.ResourceCountingExamples

/-! ## Bell circuit -/

example : Examples.Bell.circuit.count PrimitiveGate.H = 1 := by simp [Examples.Bell.circuit]

example : Examples.Bell.circuit.count PrimitiveGate.CNOT = 1 := by simp [Examples.Bell.circuit]

example : Examples.Bell.circuit.count PrimitiveGate.T = 0 := by simp [Examples.Bell.circuit]

example : Examples.Bell.circuit.size = 2 := by simp [Examples.Bell.circuit]

/-- Uncomputing the Bell circuit uses the same gates. -/
example : Examples.Bell.circuit.inverse.size = 2 := by
  simp [Examples.Bell.circuit, inverseGate]

/-! ## Inverses are counted through their primitive implementation -/

/-- `T†` is implemented as `Z·S·T`: one `T`, one `S`, one `Z`. -/
example (q : Wire 1) : (T q).inverse.count PrimitiveGate.T = 1 := by
  simp [inverseGate, sequence]

example (q : Wire 1) : (T q).inverse.count PrimitiveGate.S = 1 := by
  simp [inverseGate, sequence]

example (q : Wire 1) : (T q).inverse.count PrimitiveGate.Z = 1 := by
  simp [inverseGate, sequence]

example (q : Wire 1) : (T q).inverse.size = 3 := by
  simp [inverseGate, sequence]

/-! ## A mixed circuit -/

/-- `H`, `T` and `CNOT`, followed by `T†` on the target. -/
def mixed : Circuit 2 :=
  H 0 ;;ᶜ T 0 ;;ᶜ CNOT 0 1 (by decide) ;;ᶜ (T 1).inverse

example : mixed.count PrimitiveGate.T = 2 := by simp [mixed, inverseGate, sequence]

example : mixed.count PrimitiveGate.CNOT = 1 := by simp [mixed, inverseGate, sequence]

example : mixed.size = 6 := by simp [mixed, inverseGate, sequence]

/-- Repeating `mixed` a thousand times: counts scale linearly. -/
example : (sequence (List.replicate 1000 mixed)).count PrimitiveGate.T = 2000 := by
  rw [count_replicate]
  simp [mixed, inverseGate, sequence]

/-- Relocating `mixed` onto wires `2, 0` of a three-qubit machine keeps its counts. -/
example : (mixed.onRegister (QRegister.pair 2 0 (by decide) : QRegister 2 3)).count
    PrimitiveGate.T = 2 := by
  simp [mixed, inverseGate, sequence]

/-! ## Toffoli is a primitive, not a decomposition -/

/-- The `T` count only sees `T` gates literally present in the circuit. -/
example : (TOFF (0 : Wire 3) 1 2 (by decide) (by decide) (by decide)).count
    PrimitiveGate.T = 0 := by
  simp

example : (TOFF (0 : Wire 3) 1 2 (by decide) (by decide) (by decide)).count
    PrimitiveGate.TOFF = 1 := by
  simp

/-- Uncomputing uses as many Toffolis as computing (via `count_inverse_of_ne`). -/
example {n : ℕ} (c : Circuit n) : c.inverse.count PrimitiveGate.TOFF = c.count .TOFF := by
  simp

/-! ## Dynamic circuits: measurements are free, `qIf` takes the worse branch -/

/-- Compute an AND with a Toffoli, measure the target, and apply a classically controlled
fixup (`CNOT`, or `T` on the other branch). -/
def andMeasureFixup {Var : Type} (x : Var) : DynamicCircuit Var 3 :=
  .seq (.circuit (TOFF 0 1 2 (by decide) (by decide) (by decide)))
    (.seq (.measure x (QRegister.singleton 2))
      (.qIf (fun s ↦ s x = 1) (.circuit (CNOT 0 1 (by decide))) (.circuit (T 0))))

variable {Var : Type}

example (x : Var) : (andMeasureFixup x).count PrimitiveGate.TOFF = 1 := by
  simp [andMeasureFixup]

example (x : Var) : (andMeasureFixup x).count PrimitiveGate.T = 1 := by
  simp [andMeasureFixup]

example (x : Var) : (andMeasureFixup x).count PrimitiveGate.CNOT = 1 := by
  simp [andMeasureFixup]

/-! ## Cody Jones' 4-`T` Toffoli (`jonesToffoli`, `andCompute`, `andUncompute`) -/

example :
    (DynamicCircuit.andCompute (Var := Var) (0 : Wire 3) 1 2
      (by decide) (by decide)).count PrimitiveGate.T = 4 := by
  simp

example :
    (DynamicCircuit.andCompute (Var := Var) (0 : Wire 3) 1 2
      (by decide) (by decide)).count PrimitiveGate.TOFF = 0 := by
  simp

example (v : Var) :
    (DynamicCircuit.andUncompute v (0 : Wire 3) 1 2 (by decide)).count PrimitiveGate.T = 0 := by
  simp

example (v : Var) :
    (DynamicCircuit.andUncompute v (0 : Wire 3) 1 2 (by decide)).count PrimitiveGate.TOFF = 0 := by
  simp

example (v : Var) :
    (DynamicCircuit.jonesToffoli v (0 : Wire 4) 1 2 3
      (by decide) (by decide) (by decide) (by decide)).count PrimitiveGate.T = 4 := by
  simp

example (v : Var) :
    (DynamicCircuit.jonesToffoli v (0 : Wire 4) 1 2 3
      (by decide) (by decide) (by decide) (by decide)).count PrimitiveGate.TOFF = 0 := by
  simp

example (v : Var) :
    (DynamicCircuit.jonesToffoli v (0 : Wire 4) 1 2 3
      (by decide) (by decide) (by decide) (by decide)).support.card = 4 := by
  simp

end Circuit.ResourceCountingExamples
