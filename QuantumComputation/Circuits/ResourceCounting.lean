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

public import QuantumComputation.Circuits.Combinators
public import QuantumComputation.Circuits.DynamicCircuit
public import QuantumComputation.Circuits.Toffoli

/-!
# Gate counting

`Circuit.count g c` is the number of occurrences of the primitive gate `g` in the circuit `c`,
and `Circuit.size c` is the total number of primitive gates in `c`.  `DynamicCircuit.count g p`
is the worst-case number of occurrences of `g` in the dynamic circuit `p`.

Both are purely syntactic counts: no cost weights are involved.  Derived circuits such as
`c.inverse` or `c.onRegister p` are ordinary circuits of primitive gates, so they are counted
like any other circuit.  For example `T†` is implemented by `inverseGate` as `Z·S·T`, so it
contributes one `T`, one `S` and one `Z`.
-/

@[expose] public section

namespace Circuit

variable {n k a : ℕ}

/-! ## Definitions -/

/-- Number of occurrences of the primitive gate `g` in a circuit. -/
def count (g : PrimitiveGate a) : Circuit n → ℕ
  | .identity => 0
  | .gate g' _ => if (⟨_, g'⟩ : Σ b, PrimitiveGate b) = ⟨a, g⟩ then 1 else 0
  | .seq c₁ c₂ => count g c₁ + count g c₂

/-- Total number of primitive gates in a circuit. -/
def size : Circuit n → ℕ
  | .identity => 0
  | .gate _ _ => 1
  | .seq c₁ c₂ => size c₁ + size c₂

/-! ## `count` -/

@[simp]
theorem count_identity (g : PrimitiveGate a) : (identity : Circuit n).count g = 0 := rfl

@[simp]
theorem count_gate (g : PrimitiveGate a) {m : ℕ} (g' : PrimitiveGate m) (r : QRegister m n) :
    (gate g' r).count g = if (⟨m, g'⟩ : Σ b, PrimitiveGate b) = ⟨a, g⟩ then 1 else 0 := rfl

@[simp]
theorem count_seq (g : PrimitiveGate a) (c₁ c₂ : Circuit n) :
    (seq c₁ c₂).count g = c₁.count g + c₂.count g := rfl

theorem count_gate_self (g : PrimitiveGate a) (r : QRegister a n) :
    (gate g r).count g = 1 := ite_eq_left rfl

theorem count_gate_of_ne (g : PrimitiveGate a) {m : ℕ} (g' : PrimitiveGate m)
    (r : QRegister m n) (h : (⟨m, g'⟩ : Σ b, PrimitiveGate b) ≠ ⟨a, g⟩) :
    (gate g' r).count g = 0 := ite_eq_right h

@[simp]
theorem count_sequence (g : PrimitiveGate a) (cs : List (Circuit n)) :
    (sequence cs).count g = (cs.map (count g)).sum := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simp [ih]

/-- Repeating a circuit `reps` times multiplies each gate count by `reps`. -/
theorem count_replicate (g : PrimitiveGate a) (reps : ℕ) (c : Circuit n) :
    (sequence (List.replicate reps c)).count g = reps * c.count g := by
  simp

/-- Relocating a `k`-wire circuit onto an `n`-wire register preserves every gate count. -/
@[simp]
theorem count_onRegister (g : PrimitiveGate a) (placement : QRegister k n) (c : Circuit k) :
    (c.onRegister placement).count g = c.count g := by
  induction c with
  | identity => rfl
  | gate g' r => rfl
  | seq c₁ c₂ ih₁ ih₂ => simp [onRegister_seq, ih₁, ih₂]

/-! ### Counts of inverse circuits

`inverseGate` implements `S† = Z·S` and `T† = Z·S·T` and leaves every other primitive
unchanged.  Inversion therefore preserves the count of every gate except `S` and `Z`. -/

/-- Inversion preserves the count of every primitive other than `S` and `Z`.  As a `simp` lemma
its side conditions are discharged automatically, e.g. for `T` and `TOFF`. -/
@[simp]
theorem count_inverse_of_ne (g : PrimitiveGate a)
    (hs : (⟨a, g⟩ : Σ b, PrimitiveGate b) ≠ ⟨1, .s⟩)
    (hz : (⟨a, g⟩ : Σ b, PrimitiveGate b) ≠ ⟨1, .z⟩) (c : Circuit n) :
    c.inverse.count g = c.count g := by
  induction c with
  | identity => rfl
  | gate g' r =>
      cases g' <;>
        simp only [inverse_gate, inverseGate, sequence, count_seq, count_gate, count_identity,
          ite_eq_right hs.symm, ite_eq_right hz.symm, Nat.add_zero]
  | seq c₁ c₂ ih₁ ih₂ => simp only [inverse_seq, count_seq, ih₁, ih₂, Nat.add_comm]

@[simp]
theorem count_inverse_s (c : Circuit n) :
    c.inverse.count PrimitiveGate.S = c.count .S + c.count .T := by
  induction c with
  | identity => rfl
  | gate g r => cases g <;> simp [inverseGate, sequence]
  | seq c₁ c₂ ih₁ ih₂ => simp only [inverse_seq, count_seq, ih₁, ih₂]; omega

@[simp]
theorem count_inverse_z (c : Circuit n) :
    c.inverse.count PrimitiveGate.Z = c.count .Z + c.count .S + c.count .T := by
  induction c with
  | identity => rfl
  | gate g r => cases g <;> simp [inverseGate, sequence]
  | seq c₁ c₂ ih₁ ih₂ => simp only [inverse_seq, count_seq, ih₁, ih₂]; omega

/-! ## `size` -/

@[simp] theorem size_identity : (identity : Circuit n).size = 0 := rfl

@[simp]
theorem size_gate {m : ℕ} (g : PrimitiveGate m) (r : QRegister m n) : (gate g r).size = 1 := rfl

@[simp]
theorem size_seq (c₁ c₂ : Circuit n) : (seq c₁ c₂).size = c₁.size + c₂.size := rfl

@[simp]
theorem size_sequence (cs : List (Circuit n)) : (sequence cs).size = (cs.map size).sum := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simp [ih]

/-- Repeating a circuit `reps` times multiplies its size by `reps`. -/
theorem size_replicate (reps : ℕ) (c : Circuit n) :
    (sequence (List.replicate reps c)).size = reps * c.size := by
  simp

/-- Relocating a `k`-wire circuit onto an `n`-wire register preserves its size. -/
@[simp]
theorem size_onRegister (placement : QRegister k n) (c : Circuit k) :
    (c.onRegister placement).size = c.size := by
  induction c with
  | identity => rfl
  | gate g r => rfl
  | seq c₁ c₂ ih₁ ih₂ => simp [onRegister_seq, ih₁, ih₂]

/-- The size of a circuit is the sum of the counts of the nine primitive gates. -/
theorem size_eq_sum_count (c : Circuit n) :
    c.size = c.count PrimitiveGate.X + c.count .Y + c.count .Z + c.count .H + c.count .S +
      c.count .T + c.count .CNOT + c.count .SWAP + c.count .TOFF := by
  induction c with
  | identity => rfl
  | gate g r => cases g <;> simp
  | seq c₁ c₂ ih₁ ih₂ => simp only [size_seq, count_seq, ih₁, ih₂]; omega

/-- Inverting `S` adds one `Z`, and inverting `T` adds one `S` and one `Z`. -/
@[simp]
theorem size_inverse (c : Circuit n) :
    c.inverse.size = c.size + c.count PrimitiveGate.S + 2 * c.count .T := by
  induction c with
  | identity => rfl
  | gate g r => cases g <;> simp [inverseGate, sequence]
  | seq c₁ c₂ ih₁ ih₂ => simp only [inverse_seq, size_seq, count_seq, ih₁, ih₂]; omega

/-- The 3-wire temporary-AND compute circuit uses `4` `T` gates. -/
@[simp]
theorem count_andCompute_t (control₁ control₂ ancilla : Wire n)
    (h₁a : control₁ ≠ ancilla) (h₂a : control₂ ≠ ancilla) :
    (andCompute control₁ control₂ ancilla h₁a h₂a).count PrimitiveGate.T = 4 := by
  simp [andCompute, inverseGate, sequence]

/-- The 3-wire temporary-AND compute circuit uses `0` primitive `TOFF` gates. -/
@[simp]
theorem count_andCompute_toff (control₁ control₂ ancilla : Wire n)
    (h₁a : control₁ ≠ ancilla) (h₂a : control₂ ≠ ancilla) :
    (andCompute control₁ control₂ ancilla h₁a h₂a).count PrimitiveGate.TOFF = 0 := by
  simp [andCompute, inverseGate, sequence]

end Circuit

/-- Worst-case number of occurrences of `g` in a `DynamicCircuit`: measurements are free and
`qIf` takes the worse branch.  Tagged `@[simp]` so that its equation lemmas reduce counts of
dynamic circuits to `Circuit.count`. -/
@[simp]
def DynamicCircuit.count {Var : Type} {n a : ℕ} (g : PrimitiveGate a) :
    DynamicCircuit Var n → ℕ
  | .circuit c => c.count g
  | .measure _ _ => 0
  | @DynamicCircuit.qIf _ _ _ _ t f => max (t.count g) (f.count g)
  | .seq p₁ p₂ => p₁.count g + p₂.count g

namespace DynamicCircuit

variable {Var : Type} {n : ℕ}

/-- The 3-wire temporary-AND compute gadget uses `4` `T` gates. -/
@[simp]
theorem count_andCompute_t (control₁ control₂ ancilla : Wire n)
    (h₁a : control₁ ≠ ancilla) (h₂a : control₂ ≠ ancilla) :
    (andCompute (Var := Var) control₁ control₂ ancilla h₁a h₂a).count PrimitiveGate.T = 4 := by
  simp [andCompute]

/-- The 3-wire temporary-AND compute gadget uses `0` primitive `TOFF` gates. -/
@[simp]
theorem count_andCompute_toff (control₁ control₂ ancilla : Wire n)
    (h₁a : control₁ ≠ ancilla) (h₂a : control₂ ≠ ancilla) :
    (andCompute (Var := Var) control₁ control₂ ancilla h₁a h₂a).count
      PrimitiveGate.TOFF = 0 := by
  simp [andCompute]

/-- The 3-wire measurement-assisted temporary-AND uncompute gadget uses `0` `T` gates. -/
@[simp]
theorem count_andUncompute_t (v : Var) (control₁ control₂ ancilla : Wire n)
    (h₁₂ : control₁ ≠ control₂) :
    (andUncompute v control₁ control₂ ancilla h₁₂).count PrimitiveGate.T = 0 := by
  simp [andUncompute, Circuit.andUncomputeFixup]

/-- The 3-wire measurement-assisted temporary-AND uncompute gadget uses `0` primitive `TOFF`
gates. -/
@[simp]
theorem count_andUncompute_toff (v : Var) (control₁ control₂ ancilla : Wire n)
    (h₁₂ : control₁ ≠ control₂) :
    (andUncompute v control₁ control₂ ancilla h₁₂).count PrimitiveGate.TOFF = 0 := by
  simp [andUncompute, Circuit.andUncomputeFixup]

/-- Cody Jones' 4-`T` Toffoli construction uses `4` `T` gates. -/
@[simp]
theorem count_jonesToffoli_t (v : Var) (control₁ control₂ target ancilla : Wire n)
    (h₁₂ : control₁ ≠ control₂)
    (h₁a : control₁ ≠ ancilla) (h₂a : control₂ ≠ ancilla) (hta : target ≠ ancilla) :
    (jonesToffoli v control₁ control₂ target ancilla h₁₂ h₁a h₂a hta).count
      PrimitiveGate.T = 4 := by
  simp [jonesToffoli, Circuit.CNOT]

/-- Cody Jones' 4-`T` Toffoli construction uses `0` primitive `TOFF` gates. -/
@[simp]
theorem count_jonesToffoli_toff (v : Var) (control₁ control₂ target ancilla : Wire n)
    (h₁₂ : control₁ ≠ control₂)
    (h₁a : control₁ ≠ ancilla) (h₂a : control₂ ≠ ancilla) (hta : target ≠ ancilla) :
    (jonesToffoli v control₁ control₂ target ancilla h₁₂ h₁a h₂a hta).count
      PrimitiveGate.TOFF = 0 := by
  simp [jonesToffoli, Circuit.CNOT]

end DynamicCircuit

