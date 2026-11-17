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

public import QuantumComputationDiscoveries.Primitives.Arcsin.Solution.PolyBoundA

@[expose] public section

namespace QuantumComputation.Specs

namespace ArcsinImpl

open Function Real Finset

def spPos27_4 (b : Bool) (v9 v10 v11 v12 v13 v14 v15 : ℕ) : ℕ :=
  cond b ((v9 + 2 * v10 + 4 * v11 + 8 * v12 + 16 * v13 + 32 * v14 + 64 * v15) * 1) 0
def spNeg27_4 (b : Bool) (v9 v10 v11 v12 v13 v14 v15 : ℕ) : ℕ :=
  cond (!b) ((v9 + 2 * v10 + 4 * v11 + 8 * v12 + 16 * v13 + 32 * v14 + 64 * v15) * 1) 0
theorem spPos27_4_eq (kv u s4 : ℕ) :
    spPos27_4 (kv.testBit 4) (cond (uRotBit u s4 9) 1 0) (cond (uRotBit u s4 10) 1 0)
      (cond (uRotBit u s4 11) 1 0) (cond (uRotBit u s4 12) 1 0) (cond (uRotBit u s4 13) 1 0)
      (cond (uRotBit u s4 14) 1 0) (cond (uRotBit u s4 15) 1 0) =
    slopeTermPos27 kv 4 9 7 1 s4 u := by
  unfold spPos27_4 slopeTermPos27
  cases kv.testBit 4
  · simp only [Bool.cond_false]
  · simp only [evalBits, Bool.cond_true, shiftLeft_eq_mul_pow]
    ring
theorem spNeg27_4_eq (kv u s4 : ℕ) :
    spNeg27_4 (kv.testBit 4) (cond (uRotBit u s4 9) 1 0) (cond (uRotBit u s4 10) 1 0)
      (cond (uRotBit u s4 11) 1 0) (cond (uRotBit u s4 12) 1 0) (cond (uRotBit u s4 13) 1 0)
      (cond (uRotBit u s4 14) 1 0) (cond (uRotBit u s4 15) 1 0) =
    slopeTermNeg27 kv 4 9 7 1 s4 u := by
  unfold spNeg27_4 slopeTermNeg27
  cases kv.testBit 4
  · simp only [evalBits, Bool.not_false, Bool.cond_true, shiftLeft_eq_mul_pow]
    ring
  · simp only [Bool.not_true, Bool.cond_false]
theorem spPos27_4_lin (b : Bool) (v9 v10 v11 v12 v13 v14 v15 : ℕ) :
    spPos27_4 b v9 v10 v11 v12 v13 v14 v15 =
      spPos27_4 b 1 0 0 0 0 0 0 * v9 +
      spPos27_4 b 0 1 0 0 0 0 0 * v10 +
      spPos27_4 b 0 0 1 0 0 0 0 * v11 +
      spPos27_4 b 0 0 0 1 0 0 0 * v12 +
      spPos27_4 b 0 0 0 0 1 0 0 * v13 +
      spPos27_4 b 0 0 0 0 0 1 0 * v14 +
      spPos27_4 b 0 0 0 0 0 0 1 * v15 := by
  unfold spPos27_4
  cases b <;> simp only [Bool.cond_true, Bool.cond_false] <;> ring
theorem spNeg27_4_lin (b : Bool) (v9 v10 v11 v12 v13 v14 v15 : ℕ) :
    spNeg27_4 b v9 v10 v11 v12 v13 v14 v15 =
      spNeg27_4 b 1 0 0 0 0 0 0 * v9 +
      spNeg27_4 b 0 1 0 0 0 0 0 * v10 +
      spNeg27_4 b 0 0 1 0 0 0 0 * v11 +
      spNeg27_4 b 0 0 0 1 0 0 0 * v12 +
      spNeg27_4 b 0 0 0 0 1 0 0 * v13 +
      spNeg27_4 b 0 0 0 0 0 1 0 * v14 +
      spNeg27_4 b 0 0 0 0 0 0 1 * v15 := by
  unfold spNeg27_4
  cases b <;>
    simp only [Bool.not_true, Bool.not_false, Bool.cond_true, Bool.cond_false] <;>
    ring
theorem spPos27_4_zero (b : Bool) : spPos27_4 b 0 0 0 0 0 0 0 = 0 := by
  unfold spPos27_4
  cases b <;> simp
theorem spNeg27_4_zero (b : Bool) : spNeg27_4 b 0 0 0 0 0 0 0 = 0 := by
  unfold spNeg27_4
  cases b <;> simp
def spPos27_5 (b : Bool) (v8 v9 v10 v11 v12 v13 v14 v15 : ℕ) : ℕ :=
  cond b ((v8 + 2 * v9 + 4 * v10 + 8 * v11 + 16 * v12 + 32 * v13 + 64 * v14 + 128 * v15) * 1) 0
def spNeg27_5 (b : Bool) (v8 v9 v10 v11 v12 v13 v14 v15 : ℕ) : ℕ :=
  cond (!b) ((v8 + 2 * v9 + 4 * v10 + 8 * v11 + 16 * v12 + 32 * v13 + 64 * v14 + 128 * v15) * 1) 0
theorem spPos27_5_eq (kv u s4 : ℕ) :
    spPos27_5 (kv.testBit 5) (cond (uRotBit u s4 8) 1 0) (cond (uRotBit u s4 9) 1 0)
      (cond (uRotBit u s4 10) 1 0) (cond (uRotBit u s4 11) 1 0) (cond (uRotBit u s4 12) 1 0)
      (cond (uRotBit u s4 13) 1 0) (cond (uRotBit u s4 14) 1 0) (cond (uRotBit u s4 15) 1 0) =
    slopeTermPos27 kv 5 8 8 1 s4 u := by
  unfold spPos27_5 slopeTermPos27
  cases kv.testBit 5
  · simp only [Bool.cond_false]
  · simp only [evalBits, Bool.cond_true, shiftLeft_eq_mul_pow]
    ring
theorem spNeg27_5_eq (kv u s4 : ℕ) :
    spNeg27_5 (kv.testBit 5) (cond (uRotBit u s4 8) 1 0) (cond (uRotBit u s4 9) 1 0)
      (cond (uRotBit u s4 10) 1 0) (cond (uRotBit u s4 11) 1 0) (cond (uRotBit u s4 12) 1 0)
      (cond (uRotBit u s4 13) 1 0) (cond (uRotBit u s4 14) 1 0) (cond (uRotBit u s4 15) 1 0) =
    slopeTermNeg27 kv 5 8 8 1 s4 u := by
  unfold spNeg27_5 slopeTermNeg27
  cases kv.testBit 5
  · simp only [evalBits, Bool.not_false, Bool.cond_true, shiftLeft_eq_mul_pow]
    ring
  · simp only [Bool.not_true, Bool.cond_false]
theorem spPos27_5_lin (b : Bool) (v8 v9 v10 v11 v12 v13 v14 v15 : ℕ) :
    spPos27_5 b v8 v9 v10 v11 v12 v13 v14 v15 =
      spPos27_5 b 1 0 0 0 0 0 0 0 * v8 +
      spPos27_5 b 0 1 0 0 0 0 0 0 * v9 +
      spPos27_5 b 0 0 1 0 0 0 0 0 * v10 +
      spPos27_5 b 0 0 0 1 0 0 0 0 * v11 +
      spPos27_5 b 0 0 0 0 1 0 0 0 * v12 +
      spPos27_5 b 0 0 0 0 0 1 0 0 * v13 +
      spPos27_5 b 0 0 0 0 0 0 1 0 * v14 +
      spPos27_5 b 0 0 0 0 0 0 0 1 * v15 := by
  unfold spPos27_5
  cases b <;> simp only [Bool.cond_true, Bool.cond_false] <;> ring
theorem spNeg27_5_lin (b : Bool) (v8 v9 v10 v11 v12 v13 v14 v15 : ℕ) :
    spNeg27_5 b v8 v9 v10 v11 v12 v13 v14 v15 =
      spNeg27_5 b 1 0 0 0 0 0 0 0 * v8 +
      spNeg27_5 b 0 1 0 0 0 0 0 0 * v9 +
      spNeg27_5 b 0 0 1 0 0 0 0 0 * v10 +
      spNeg27_5 b 0 0 0 1 0 0 0 0 * v11 +
      spNeg27_5 b 0 0 0 0 1 0 0 0 * v12 +
      spNeg27_5 b 0 0 0 0 0 1 0 0 * v13 +
      spNeg27_5 b 0 0 0 0 0 0 1 0 * v14 +
      spNeg27_5 b 0 0 0 0 0 0 0 1 * v15 := by
  unfold spNeg27_5
  cases b <;>
    simp only [Bool.not_true, Bool.not_false, Bool.cond_true, Bool.cond_false] <;>
    ring
theorem spPos27_5_zero (b : Bool) : spPos27_5 b 0 0 0 0 0 0 0 0 = 0 := by
  unfold spPos27_5
  cases b <;> simp
theorem spNeg27_5_zero (b : Bool) : spNeg27_5 b 0 0 0 0 0 0 0 0 = 0 := by
  unfold spNeg27_5
  cases b <;> simp
def spPos27_6 (b : Bool) (v7 v8 v9 v10 v11 v12 v13 v14 v15 : ℕ) : ℕ :=
  cond b ((v7 + 2 * v8 + 4 * v9 + 8 * v10 + 16 * v11 + 32 * v12 + 64 * v13 + 128 * v14 +
    256 * v15) * 1) 0
def spNeg27_6 (b : Bool) (v7 v8 v9 v10 v11 v12 v13 v14 v15 : ℕ) : ℕ :=
  cond (!b) ((v7 + 2 * v8 + 4 * v9 + 8 * v10 + 16 * v11 + 32 * v12 + 64 * v13 + 128 * v14 +
    256 * v15) * 1) 0
theorem spPos27_6_eq (kv u s4 : ℕ) :
    spPos27_6 (kv.testBit 6) (cond (uRotBit u s4 7) 1 0) (cond (uRotBit u s4 8) 1 0)
      (cond (uRotBit u s4 9) 1 0) (cond (uRotBit u s4 10) 1 0) (cond (uRotBit u s4 11) 1 0)
      (cond (uRotBit u s4 12) 1 0) (cond (uRotBit u s4 13) 1 0) (cond (uRotBit u s4 14) 1 0)
      (cond (uRotBit u s4 15) 1 0) =
    slopeTermPos27 kv 6 7 9 1 s4 u := by
  unfold spPos27_6 slopeTermPos27
  cases kv.testBit 6
  · simp only [Bool.cond_false]
  · simp only [evalBits, Bool.cond_true, shiftLeft_eq_mul_pow]
    ring
theorem spNeg27_6_eq (kv u s4 : ℕ) :
    spNeg27_6 (kv.testBit 6) (cond (uRotBit u s4 7) 1 0) (cond (uRotBit u s4 8) 1 0)
      (cond (uRotBit u s4 9) 1 0) (cond (uRotBit u s4 10) 1 0) (cond (uRotBit u s4 11) 1 0)
      (cond (uRotBit u s4 12) 1 0) (cond (uRotBit u s4 13) 1 0) (cond (uRotBit u s4 14) 1 0)
      (cond (uRotBit u s4 15) 1 0) =
    slopeTermNeg27 kv 6 7 9 1 s4 u := by
  unfold spNeg27_6 slopeTermNeg27
  cases kv.testBit 6
  · simp only [evalBits, Bool.not_false, Bool.cond_true, shiftLeft_eq_mul_pow]
    ring
  · simp only [Bool.not_true, Bool.cond_false]
theorem spPos27_6_lin (b : Bool) (v7 v8 v9 v10 v11 v12 v13 v14 v15 : ℕ) :
    spPos27_6 b v7 v8 v9 v10 v11 v12 v13 v14 v15 =
      spPos27_6 b 1 0 0 0 0 0 0 0 0 * v7 +
      spPos27_6 b 0 1 0 0 0 0 0 0 0 * v8 +
      spPos27_6 b 0 0 1 0 0 0 0 0 0 * v9 +
      spPos27_6 b 0 0 0 1 0 0 0 0 0 * v10 +
      spPos27_6 b 0 0 0 0 1 0 0 0 0 * v11 +
      spPos27_6 b 0 0 0 0 0 1 0 0 0 * v12 +
      spPos27_6 b 0 0 0 0 0 0 1 0 0 * v13 +
      spPos27_6 b 0 0 0 0 0 0 0 1 0 * v14 +
      spPos27_6 b 0 0 0 0 0 0 0 0 1 * v15 := by
  unfold spPos27_6
  cases b <;> simp only [Bool.cond_true, Bool.cond_false] <;> ring
theorem spNeg27_6_lin (b : Bool) (v7 v8 v9 v10 v11 v12 v13 v14 v15 : ℕ) :
    spNeg27_6 b v7 v8 v9 v10 v11 v12 v13 v14 v15 =
      spNeg27_6 b 1 0 0 0 0 0 0 0 0 * v7 +
      spNeg27_6 b 0 1 0 0 0 0 0 0 0 * v8 +
      spNeg27_6 b 0 0 1 0 0 0 0 0 0 * v9 +
      spNeg27_6 b 0 0 0 1 0 0 0 0 0 * v10 +
      spNeg27_6 b 0 0 0 0 1 0 0 0 0 * v11 +
      spNeg27_6 b 0 0 0 0 0 1 0 0 0 * v12 +
      spNeg27_6 b 0 0 0 0 0 0 1 0 0 * v13 +
      spNeg27_6 b 0 0 0 0 0 0 0 1 0 * v14 +
      spNeg27_6 b 0 0 0 0 0 0 0 0 1 * v15 := by
  unfold spNeg27_6
  cases b <;>
    simp only [Bool.not_true, Bool.not_false, Bool.cond_true, Bool.cond_false] <;>
    ring
theorem spPos27_6_zero (b : Bool) : spPos27_6 b 0 0 0 0 0 0 0 0 0 = 0 := by
  unfold spPos27_6
  cases b <;> simp
theorem spNeg27_6_zero (b : Bool) : spNeg27_6 b 0 0 0 0 0 0 0 0 0 = 0 := by
  unfold spNeg27_6
  cases b <;> simp
def spPos27_7 (b : Bool) (v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 : ℕ) : ℕ :=
  cond b ((v6 + 2 * v7 + 4 * v8 + 8 * v9 + 16 * v10 + 32 * v11 + 64 * v12 + 128 * v13 +
    256 * v14 + 512 * v15) * 1) 0
def spNeg27_7 (b : Bool) (v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 : ℕ) : ℕ :=
  cond (!b) ((v6 + 2 * v7 + 4 * v8 + 8 * v9 + 16 * v10 + 32 * v11 + 64 * v12 + 128 * v13 +
    256 * v14 + 512 * v15) * 1) 0
theorem spPos27_7_eq (kv u s4 : ℕ) :
    spPos27_7 (kv.testBit 7) (cond (uRotBit u s4 6) 1 0) (cond (uRotBit u s4 7) 1 0)
      (cond (uRotBit u s4 8) 1 0) (cond (uRotBit u s4 9) 1 0) (cond (uRotBit u s4 10) 1 0)
      (cond (uRotBit u s4 11) 1 0) (cond (uRotBit u s4 12) 1 0) (cond (uRotBit u s4 13) 1 0)
      (cond (uRotBit u s4 14) 1 0) (cond (uRotBit u s4 15) 1 0) =
    slopeTermPos27 kv 7 6 10 1 s4 u := by
  unfold spPos27_7 slopeTermPos27
  cases kv.testBit 7
  · simp only [Bool.cond_false]
  · simp only [evalBits, Bool.cond_true, shiftLeft_eq_mul_pow]
    ring
theorem spNeg27_7_eq (kv u s4 : ℕ) :
    spNeg27_7 (kv.testBit 7) (cond (uRotBit u s4 6) 1 0) (cond (uRotBit u s4 7) 1 0)
      (cond (uRotBit u s4 8) 1 0) (cond (uRotBit u s4 9) 1 0) (cond (uRotBit u s4 10) 1 0)
      (cond (uRotBit u s4 11) 1 0) (cond (uRotBit u s4 12) 1 0) (cond (uRotBit u s4 13) 1 0)
      (cond (uRotBit u s4 14) 1 0) (cond (uRotBit u s4 15) 1 0) =
    slopeTermNeg27 kv 7 6 10 1 s4 u := by
  unfold spNeg27_7 slopeTermNeg27
  cases kv.testBit 7
  · simp only [evalBits, Bool.not_false, Bool.cond_true, shiftLeft_eq_mul_pow]
    ring
  · simp only [Bool.not_true, Bool.cond_false]
theorem spPos27_7_lin (b : Bool) (v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 : ℕ) :
    spPos27_7 b v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 =
      spPos27_7 b 1 0 0 0 0 0 0 0 0 0 * v6 +
      spPos27_7 b 0 1 0 0 0 0 0 0 0 0 * v7 +
      spPos27_7 b 0 0 1 0 0 0 0 0 0 0 * v8 +
      spPos27_7 b 0 0 0 1 0 0 0 0 0 0 * v9 +
      spPos27_7 b 0 0 0 0 1 0 0 0 0 0 * v10 +
      spPos27_7 b 0 0 0 0 0 1 0 0 0 0 * v11 +
      spPos27_7 b 0 0 0 0 0 0 1 0 0 0 * v12 +
      spPos27_7 b 0 0 0 0 0 0 0 1 0 0 * v13 +
      spPos27_7 b 0 0 0 0 0 0 0 0 1 0 * v14 +
      spPos27_7 b 0 0 0 0 0 0 0 0 0 1 * v15 := by
  unfold spPos27_7
  cases b <;> simp only [Bool.cond_true, Bool.cond_false] <;> ring
theorem spNeg27_7_lin (b : Bool) (v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 : ℕ) :
    spNeg27_7 b v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 =
      spNeg27_7 b 1 0 0 0 0 0 0 0 0 0 * v6 +
      spNeg27_7 b 0 1 0 0 0 0 0 0 0 0 * v7 +
      spNeg27_7 b 0 0 1 0 0 0 0 0 0 0 * v8 +
      spNeg27_7 b 0 0 0 1 0 0 0 0 0 0 * v9 +
      spNeg27_7 b 0 0 0 0 1 0 0 0 0 0 * v10 +
      spNeg27_7 b 0 0 0 0 0 1 0 0 0 0 * v11 +
      spNeg27_7 b 0 0 0 0 0 0 1 0 0 0 * v12 +
      spNeg27_7 b 0 0 0 0 0 0 0 1 0 0 * v13 +
      spNeg27_7 b 0 0 0 0 0 0 0 0 1 0 * v14 +
      spNeg27_7 b 0 0 0 0 0 0 0 0 0 1 * v15 := by
  unfold spNeg27_7
  cases b <;>
    simp only [Bool.not_true, Bool.not_false, Bool.cond_true, Bool.cond_false] <;>
    ring
theorem spPos27_7_zero (b : Bool) : spPos27_7 b 0 0 0 0 0 0 0 0 0 0 = 0 := by
  unfold spPos27_7
  cases b <;> simp
theorem spNeg27_7_zero (b : Bool) : spNeg27_7 b 0 0 0 0 0 0 0 0 0 0 = 0 := by
  unfold spNeg27_7
  cases b <;> simp
def spPos27_8 (b : Bool) (v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 : ℕ) : ℕ :=
  cond b ((v5 + 2 * v6 + 4 * v7 + 8 * v8 + 16 * v9 + 32 * v10 + 64 * v11 + 128 * v12 +
    256 * v13 + 512 * v14 + 1024 * v15) * 1) 0
def spNeg27_8 (b : Bool) (v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 : ℕ) : ℕ :=
  cond (!b) ((v5 + 2 * v6 + 4 * v7 + 8 * v8 + 16 * v9 + 32 * v10 + 64 * v11 + 128 * v12 +
    256 * v13 + 512 * v14 + 1024 * v15) * 1) 0
theorem spPos27_8_eq (kv u s4 : ℕ) :
    spPos27_8 (kv.testBit 8) (cond (uRotBit u s4 5) 1 0) (cond (uRotBit u s4 6) 1 0)
      (cond (uRotBit u s4 7) 1 0) (cond (uRotBit u s4 8) 1 0) (cond (uRotBit u s4 9) 1 0)
      (cond (uRotBit u s4 10) 1 0) (cond (uRotBit u s4 11) 1 0) (cond (uRotBit u s4 12) 1 0)
      (cond (uRotBit u s4 13) 1 0) (cond (uRotBit u s4 14) 1 0) (cond (uRotBit u s4 15) 1 0) =
    slopeTermPos27 kv 8 5 11 1 s4 u := by
  unfold spPos27_8 slopeTermPos27
  cases kv.testBit 8
  · simp only [Bool.cond_false]
  · simp only [evalBits, Bool.cond_true, shiftLeft_eq_mul_pow]
    ring
theorem spNeg27_8_eq (kv u s4 : ℕ) :
    spNeg27_8 (kv.testBit 8) (cond (uRotBit u s4 5) 1 0) (cond (uRotBit u s4 6) 1 0)
      (cond (uRotBit u s4 7) 1 0) (cond (uRotBit u s4 8) 1 0) (cond (uRotBit u s4 9) 1 0)
      (cond (uRotBit u s4 10) 1 0) (cond (uRotBit u s4 11) 1 0) (cond (uRotBit u s4 12) 1 0)
      (cond (uRotBit u s4 13) 1 0) (cond (uRotBit u s4 14) 1 0) (cond (uRotBit u s4 15) 1 0) =
    slopeTermNeg27 kv 8 5 11 1 s4 u := by
  unfold spNeg27_8 slopeTermNeg27
  cases kv.testBit 8
  · simp only [evalBits, Bool.not_false, Bool.cond_true, shiftLeft_eq_mul_pow]
    ring
  · simp only [Bool.not_true, Bool.cond_false]
theorem spPos27_8_lin (b : Bool) (v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 : ℕ) :
    spPos27_8 b v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 =
      spPos27_8 b 1 0 0 0 0 0 0 0 0 0 0 * v5 +
      spPos27_8 b 0 1 0 0 0 0 0 0 0 0 0 * v6 +
      spPos27_8 b 0 0 1 0 0 0 0 0 0 0 0 * v7 +
      spPos27_8 b 0 0 0 1 0 0 0 0 0 0 0 * v8 +
      spPos27_8 b 0 0 0 0 1 0 0 0 0 0 0 * v9 +
      spPos27_8 b 0 0 0 0 0 1 0 0 0 0 0 * v10 +
      spPos27_8 b 0 0 0 0 0 0 1 0 0 0 0 * v11 +
      spPos27_8 b 0 0 0 0 0 0 0 1 0 0 0 * v12 +
      spPos27_8 b 0 0 0 0 0 0 0 0 1 0 0 * v13 +
      spPos27_8 b 0 0 0 0 0 0 0 0 0 1 0 * v14 +
      spPos27_8 b 0 0 0 0 0 0 0 0 0 0 1 * v15 := by
  unfold spPos27_8
  cases b <;> simp only [Bool.cond_true, Bool.cond_false] <;> ring
theorem spNeg27_8_lin (b : Bool) (v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 : ℕ) :
    spNeg27_8 b v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 =
      spNeg27_8 b 1 0 0 0 0 0 0 0 0 0 0 * v5 +
      spNeg27_8 b 0 1 0 0 0 0 0 0 0 0 0 * v6 +
      spNeg27_8 b 0 0 1 0 0 0 0 0 0 0 0 * v7 +
      spNeg27_8 b 0 0 0 1 0 0 0 0 0 0 0 * v8 +
      spNeg27_8 b 0 0 0 0 1 0 0 0 0 0 0 * v9 +
      spNeg27_8 b 0 0 0 0 0 1 0 0 0 0 0 * v10 +
      spNeg27_8 b 0 0 0 0 0 0 1 0 0 0 0 * v11 +
      spNeg27_8 b 0 0 0 0 0 0 0 1 0 0 0 * v12 +
      spNeg27_8 b 0 0 0 0 0 0 0 0 1 0 0 * v13 +
      spNeg27_8 b 0 0 0 0 0 0 0 0 0 1 0 * v14 +
      spNeg27_8 b 0 0 0 0 0 0 0 0 0 0 1 * v15 := by
  unfold spNeg27_8
  cases b <;>
    simp only [Bool.not_true, Bool.not_false, Bool.cond_true, Bool.cond_false] <;>
    ring
theorem spPos27_8_zero (b : Bool) : spPos27_8 b 0 0 0 0 0 0 0 0 0 0 0 = 0 := by
  unfold spPos27_8
  cases b <;> simp
theorem spNeg27_8_zero (b : Bool) : spNeg27_8 b 0 0 0 0 0 0 0 0 0 0 0 = 0 := by
  unfold spNeg27_8
  cases b <;> simp
def spPos27_9 (b : Bool) (v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 : ℕ) : ℕ :=
  cond b ((v4 + 2 * v5 + 4 * v6 + 8 * v7 + 16 * v8 + 32 * v9 + 64 * v10 + 128 * v11 +
    256 * v12 + 512 * v13 + 1024 * v14 + 2048 * v15) * 1) 0
def spNeg27_9 (b : Bool) (v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 : ℕ) : ℕ :=
  cond (!b) ((v4 + 2 * v5 + 4 * v6 + 8 * v7 + 16 * v8 + 32 * v9 + 64 * v10 + 128 * v11 +
    256 * v12 + 512 * v13 + 1024 * v14 + 2048 * v15) * 1) 0
theorem spPos27_9_eq (kv u s4 : ℕ) :
    spPos27_9 (kv.testBit 9) (cond (uRotBit u s4 4) 1 0) (cond (uRotBit u s4 5) 1 0)
      (cond (uRotBit u s4 6) 1 0) (cond (uRotBit u s4 7) 1 0) (cond (uRotBit u s4 8) 1 0)
      (cond (uRotBit u s4 9) 1 0) (cond (uRotBit u s4 10) 1 0) (cond (uRotBit u s4 11) 1 0)
      (cond (uRotBit u s4 12) 1 0) (cond (uRotBit u s4 13) 1 0) (cond (uRotBit u s4 14) 1 0)
      (cond (uRotBit u s4 15) 1 0) =
    slopeTermPos27 kv 9 4 12 1 s4 u := by
  unfold spPos27_9 slopeTermPos27
  cases kv.testBit 9
  · simp only [Bool.cond_false]
  · simp only [evalBits, Bool.cond_true, shiftLeft_eq_mul_pow]
    ring
theorem spNeg27_9_eq (kv u s4 : ℕ) :
    spNeg27_9 (kv.testBit 9) (cond (uRotBit u s4 4) 1 0) (cond (uRotBit u s4 5) 1 0)
      (cond (uRotBit u s4 6) 1 0) (cond (uRotBit u s4 7) 1 0) (cond (uRotBit u s4 8) 1 0)
      (cond (uRotBit u s4 9) 1 0) (cond (uRotBit u s4 10) 1 0) (cond (uRotBit u s4 11) 1 0)
      (cond (uRotBit u s4 12) 1 0) (cond (uRotBit u s4 13) 1 0) (cond (uRotBit u s4 14) 1 0)
      (cond (uRotBit u s4 15) 1 0) =
    slopeTermNeg27 kv 9 4 12 1 s4 u := by
  unfold spNeg27_9 slopeTermNeg27
  cases kv.testBit 9
  · simp only [evalBits, Bool.not_false, Bool.cond_true, shiftLeft_eq_mul_pow]
    ring
  · simp only [Bool.not_true, Bool.cond_false]
theorem spPos27_9_lin (b : Bool) (v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 : ℕ) :
    spPos27_9 b v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 =
      spPos27_9 b 1 0 0 0 0 0 0 0 0 0 0 0 * v4 +
      spPos27_9 b 0 1 0 0 0 0 0 0 0 0 0 0 * v5 +
      spPos27_9 b 0 0 1 0 0 0 0 0 0 0 0 0 * v6 +
      spPos27_9 b 0 0 0 1 0 0 0 0 0 0 0 0 * v7 +
      spPos27_9 b 0 0 0 0 1 0 0 0 0 0 0 0 * v8 +
      spPos27_9 b 0 0 0 0 0 1 0 0 0 0 0 0 * v9 +
      spPos27_9 b 0 0 0 0 0 0 1 0 0 0 0 0 * v10 +
      spPos27_9 b 0 0 0 0 0 0 0 1 0 0 0 0 * v11 +
      spPos27_9 b 0 0 0 0 0 0 0 0 1 0 0 0 * v12 +
      spPos27_9 b 0 0 0 0 0 0 0 0 0 1 0 0 * v13 +
      spPos27_9 b 0 0 0 0 0 0 0 0 0 0 1 0 * v14 +
      spPos27_9 b 0 0 0 0 0 0 0 0 0 0 0 1 * v15 := by
  unfold spPos27_9
  cases b <;> simp only [Bool.cond_true, Bool.cond_false] <;> ring
theorem spNeg27_9_lin (b : Bool) (v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 : ℕ) :
    spNeg27_9 b v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 =
      spNeg27_9 b 1 0 0 0 0 0 0 0 0 0 0 0 * v4 +
      spNeg27_9 b 0 1 0 0 0 0 0 0 0 0 0 0 * v5 +
      spNeg27_9 b 0 0 1 0 0 0 0 0 0 0 0 0 * v6 +
      spNeg27_9 b 0 0 0 1 0 0 0 0 0 0 0 0 * v7 +
      spNeg27_9 b 0 0 0 0 1 0 0 0 0 0 0 0 * v8 +
      spNeg27_9 b 0 0 0 0 0 1 0 0 0 0 0 0 * v9 +
      spNeg27_9 b 0 0 0 0 0 0 1 0 0 0 0 0 * v10 +
      spNeg27_9 b 0 0 0 0 0 0 0 1 0 0 0 0 * v11 +
      spNeg27_9 b 0 0 0 0 0 0 0 0 1 0 0 0 * v12 +
      spNeg27_9 b 0 0 0 0 0 0 0 0 0 1 0 0 * v13 +
      spNeg27_9 b 0 0 0 0 0 0 0 0 0 0 1 0 * v14 +
      spNeg27_9 b 0 0 0 0 0 0 0 0 0 0 0 1 * v15 := by
  unfold spNeg27_9
  cases b <;>
    simp only [Bool.not_true, Bool.not_false, Bool.cond_true, Bool.cond_false] <;>
    ring
theorem spPos27_9_zero (b : Bool) : spPos27_9 b 0 0 0 0 0 0 0 0 0 0 0 0 = 0 := by
  unfold spPos27_9
  cases b <;> simp
theorem spNeg27_9_zero (b : Bool) : spNeg27_9 b 0 0 0 0 0 0 0 0 0 0 0 0 = 0 := by
  unfold spNeg27_9
  cases b <;> simp
def spPos27_10 (b : Bool) (v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 : ℕ) : ℕ :=
  cond b ((v3 + 2 * v4 + 4 * v5 + 8 * v6 + 16 * v7 + 32 * v8 + 64 * v9 + 128 * v10 +
    256 * v11 + 512 * v12 + 1024 * v13 + 2048 * v14 + 4096 * v15) * 1) 0
def spNeg27_10 (b : Bool) (v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 : ℕ) : ℕ :=
  cond (!b) ((v3 + 2 * v4 + 4 * v5 + 8 * v6 + 16 * v7 + 32 * v8 + 64 * v9 + 128 * v10 +
    256 * v11 + 512 * v12 + 1024 * v13 + 2048 * v14 + 4096 * v15) * 1) 0
theorem spPos27_10_eq (kv u s4 : ℕ) :
    spPos27_10 (kv.testBit 10) (cond (uRotBit u s4 3) 1 0) (cond (uRotBit u s4 4) 1 0)
      (cond (uRotBit u s4 5) 1 0) (cond (uRotBit u s4 6) 1 0) (cond (uRotBit u s4 7) 1 0)
      (cond (uRotBit u s4 8) 1 0) (cond (uRotBit u s4 9) 1 0) (cond (uRotBit u s4 10) 1 0)
      (cond (uRotBit u s4 11) 1 0) (cond (uRotBit u s4 12) 1 0) (cond (uRotBit u s4 13) 1 0)
      (cond (uRotBit u s4 14) 1 0) (cond (uRotBit u s4 15) 1 0) =
    slopeTermPos27 kv 10 3 13 1 s4 u := by
  unfold spPos27_10 slopeTermPos27
  cases kv.testBit 10
  · simp only [Bool.cond_false]
  · simp only [evalBits, Bool.cond_true, shiftLeft_eq_mul_pow]
    ring
theorem spNeg27_10_eq (kv u s4 : ℕ) :
    spNeg27_10 (kv.testBit 10) (cond (uRotBit u s4 3) 1 0) (cond (uRotBit u s4 4) 1 0)
      (cond (uRotBit u s4 5) 1 0) (cond (uRotBit u s4 6) 1 0) (cond (uRotBit u s4 7) 1 0)
      (cond (uRotBit u s4 8) 1 0) (cond (uRotBit u s4 9) 1 0) (cond (uRotBit u s4 10) 1 0)
      (cond (uRotBit u s4 11) 1 0) (cond (uRotBit u s4 12) 1 0) (cond (uRotBit u s4 13) 1 0)
      (cond (uRotBit u s4 14) 1 0) (cond (uRotBit u s4 15) 1 0) =
    slopeTermNeg27 kv 10 3 13 1 s4 u := by
  unfold spNeg27_10 slopeTermNeg27
  cases kv.testBit 10
  · simp only [evalBits, Bool.not_false, Bool.cond_true, shiftLeft_eq_mul_pow]
    ring
  · simp only [Bool.not_true, Bool.cond_false]
theorem spPos27_10_lin (b : Bool) (v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 : ℕ) :
    spPos27_10 b v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 =
      spPos27_10 b 1 0 0 0 0 0 0 0 0 0 0 0 0 * v3 +
      spPos27_10 b 0 1 0 0 0 0 0 0 0 0 0 0 0 * v4 +
      spPos27_10 b 0 0 1 0 0 0 0 0 0 0 0 0 0 * v5 +
      spPos27_10 b 0 0 0 1 0 0 0 0 0 0 0 0 0 * v6 +
      spPos27_10 b 0 0 0 0 1 0 0 0 0 0 0 0 0 * v7 +
      spPos27_10 b 0 0 0 0 0 1 0 0 0 0 0 0 0 * v8 +
      spPos27_10 b 0 0 0 0 0 0 1 0 0 0 0 0 0 * v9 +
      spPos27_10 b 0 0 0 0 0 0 0 1 0 0 0 0 0 * v10 +
      spPos27_10 b 0 0 0 0 0 0 0 0 1 0 0 0 0 * v11 +
      spPos27_10 b 0 0 0 0 0 0 0 0 0 1 0 0 0 * v12 +
      spPos27_10 b 0 0 0 0 0 0 0 0 0 0 1 0 0 * v13 +
      spPos27_10 b 0 0 0 0 0 0 0 0 0 0 0 1 0 * v14 +
      spPos27_10 b 0 0 0 0 0 0 0 0 0 0 0 0 1 * v15 := by
  unfold spPos27_10
  cases b <;> simp only [Bool.cond_true, Bool.cond_false] <;> ring
theorem spNeg27_10_lin (b : Bool) (v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 : ℕ) :
    spNeg27_10 b v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 =
      spNeg27_10 b 1 0 0 0 0 0 0 0 0 0 0 0 0 * v3 +
      spNeg27_10 b 0 1 0 0 0 0 0 0 0 0 0 0 0 * v4 +
      spNeg27_10 b 0 0 1 0 0 0 0 0 0 0 0 0 0 * v5 +
      spNeg27_10 b 0 0 0 1 0 0 0 0 0 0 0 0 0 * v6 +
      spNeg27_10 b 0 0 0 0 1 0 0 0 0 0 0 0 0 * v7 +
      spNeg27_10 b 0 0 0 0 0 1 0 0 0 0 0 0 0 * v8 +
      spNeg27_10 b 0 0 0 0 0 0 1 0 0 0 0 0 0 * v9 +
      spNeg27_10 b 0 0 0 0 0 0 0 1 0 0 0 0 0 * v10 +
      spNeg27_10 b 0 0 0 0 0 0 0 0 1 0 0 0 0 * v11 +
      spNeg27_10 b 0 0 0 0 0 0 0 0 0 1 0 0 0 * v12 +
      spNeg27_10 b 0 0 0 0 0 0 0 0 0 0 1 0 0 * v13 +
      spNeg27_10 b 0 0 0 0 0 0 0 0 0 0 0 1 0 * v14 +
      spNeg27_10 b 0 0 0 0 0 0 0 0 0 0 0 0 1 * v15 := by
  unfold spNeg27_10
  cases b <;>
    simp only [Bool.not_true, Bool.not_false, Bool.cond_true, Bool.cond_false] <;>
    ring
theorem spPos27_10_zero (b : Bool) : spPos27_10 b 0 0 0 0 0 0 0 0 0 0 0 0 0 = 0 := by
  unfold spPos27_10
  cases b <;> simp
theorem spNeg27_10_zero (b : Bool) : spNeg27_10 b 0 0 0 0 0 0 0 0 0 0 0 0 0 = 0 := by
  unfold spNeg27_10
  cases b <;> simp
def spPos27_11 (b : Bool) (v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 : ℕ) : ℕ :=
  cond b ((v2 + 2 * v3 + 4 * v4 + 8 * v5 + 16 * v6 + 32 * v7 + 64 * v8 + 128 * v9 +
    256 * v10 + 512 * v11 + 1024 * v12 + 2048 * v13 + 4096 * v14 + 8192 * v15) * 1) 0
def spNeg27_11 (b : Bool) (v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 : ℕ) : ℕ :=
  cond (!b) ((v2 + 2 * v3 + 4 * v4 + 8 * v5 + 16 * v6 + 32 * v7 + 64 * v8 + 128 * v9 +
    256 * v10 + 512 * v11 + 1024 * v12 + 2048 * v13 + 4096 * v14 + 8192 * v15) * 1) 0
theorem spPos27_11_eq (kv u s4 : ℕ) :
    spPos27_11 (kv.testBit 11) (cond (uRotBit u s4 2) 1 0) (cond (uRotBit u s4 3) 1 0)
      (cond (uRotBit u s4 4) 1 0) (cond (uRotBit u s4 5) 1 0) (cond (uRotBit u s4 6) 1 0)
      (cond (uRotBit u s4 7) 1 0) (cond (uRotBit u s4 8) 1 0) (cond (uRotBit u s4 9) 1 0)
      (cond (uRotBit u s4 10) 1 0) (cond (uRotBit u s4 11) 1 0) (cond (uRotBit u s4 12) 1 0)
      (cond (uRotBit u s4 13) 1 0) (cond (uRotBit u s4 14) 1 0) (cond (uRotBit u s4 15) 1 0) =
    slopeTermPos27 kv 11 2 14 1 s4 u := by
  unfold spPos27_11 slopeTermPos27
  cases kv.testBit 11
  · simp only [Bool.cond_false]
  · simp only [evalBits, Bool.cond_true, shiftLeft_eq_mul_pow]
    ring
theorem spNeg27_11_eq (kv u s4 : ℕ) :
    spNeg27_11 (kv.testBit 11) (cond (uRotBit u s4 2) 1 0) (cond (uRotBit u s4 3) 1 0)
      (cond (uRotBit u s4 4) 1 0) (cond (uRotBit u s4 5) 1 0) (cond (uRotBit u s4 6) 1 0)
      (cond (uRotBit u s4 7) 1 0) (cond (uRotBit u s4 8) 1 0) (cond (uRotBit u s4 9) 1 0)
      (cond (uRotBit u s4 10) 1 0) (cond (uRotBit u s4 11) 1 0) (cond (uRotBit u s4 12) 1 0)
      (cond (uRotBit u s4 13) 1 0) (cond (uRotBit u s4 14) 1 0) (cond (uRotBit u s4 15) 1 0) =
    slopeTermNeg27 kv 11 2 14 1 s4 u := by
  unfold spNeg27_11 slopeTermNeg27
  cases kv.testBit 11
  · simp only [evalBits, Bool.not_false, Bool.cond_true, shiftLeft_eq_mul_pow]
    ring
  · simp only [Bool.not_true, Bool.cond_false]
theorem spPos27_11_lin (b : Bool) (v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 : ℕ) :
    spPos27_11 b v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 =
      spPos27_11 b 1 0 0 0 0 0 0 0 0 0 0 0 0 0 * v2 +
      spPos27_11 b 0 1 0 0 0 0 0 0 0 0 0 0 0 0 * v3 +
      spPos27_11 b 0 0 1 0 0 0 0 0 0 0 0 0 0 0 * v4 +
      spPos27_11 b 0 0 0 1 0 0 0 0 0 0 0 0 0 0 * v5 +
      spPos27_11 b 0 0 0 0 1 0 0 0 0 0 0 0 0 0 * v6 +
      spPos27_11 b 0 0 0 0 0 1 0 0 0 0 0 0 0 0 * v7 +
      spPos27_11 b 0 0 0 0 0 0 1 0 0 0 0 0 0 0 * v8 +
      spPos27_11 b 0 0 0 0 0 0 0 1 0 0 0 0 0 0 * v9 +
      spPos27_11 b 0 0 0 0 0 0 0 0 1 0 0 0 0 0 * v10 +
      spPos27_11 b 0 0 0 0 0 0 0 0 0 1 0 0 0 0 * v11 +
      spPos27_11 b 0 0 0 0 0 0 0 0 0 0 1 0 0 0 * v12 +
      spPos27_11 b 0 0 0 0 0 0 0 0 0 0 0 1 0 0 * v13 +
      spPos27_11 b 0 0 0 0 0 0 0 0 0 0 0 0 1 0 * v14 +
      spPos27_11 b 0 0 0 0 0 0 0 0 0 0 0 0 0 1 * v15 := by
  unfold spPos27_11
  cases b <;> simp only [Bool.cond_true, Bool.cond_false] <;> ring
theorem spNeg27_11_lin (b : Bool) (v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 : ℕ) :
    spNeg27_11 b v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 =
      spNeg27_11 b 1 0 0 0 0 0 0 0 0 0 0 0 0 0 * v2 +
      spNeg27_11 b 0 1 0 0 0 0 0 0 0 0 0 0 0 0 * v3 +
      spNeg27_11 b 0 0 1 0 0 0 0 0 0 0 0 0 0 0 * v4 +
      spNeg27_11 b 0 0 0 1 0 0 0 0 0 0 0 0 0 0 * v5 +
      spNeg27_11 b 0 0 0 0 1 0 0 0 0 0 0 0 0 0 * v6 +
      spNeg27_11 b 0 0 0 0 0 1 0 0 0 0 0 0 0 0 * v7 +
      spNeg27_11 b 0 0 0 0 0 0 1 0 0 0 0 0 0 0 * v8 +
      spNeg27_11 b 0 0 0 0 0 0 0 1 0 0 0 0 0 0 * v9 +
      spNeg27_11 b 0 0 0 0 0 0 0 0 1 0 0 0 0 0 * v10 +
      spNeg27_11 b 0 0 0 0 0 0 0 0 0 1 0 0 0 0 * v11 +
      spNeg27_11 b 0 0 0 0 0 0 0 0 0 0 1 0 0 0 * v12 +
      spNeg27_11 b 0 0 0 0 0 0 0 0 0 0 0 1 0 0 * v13 +
      spNeg27_11 b 0 0 0 0 0 0 0 0 0 0 0 0 1 0 * v14 +
      spNeg27_11 b 0 0 0 0 0 0 0 0 0 0 0 0 0 1 * v15 := by
  unfold spNeg27_11
  cases b <;>
    simp only [Bool.not_true, Bool.not_false, Bool.cond_true, Bool.cond_false] <;>
    ring
theorem spPos27_11_zero (b : Bool) : spPos27_11 b 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = 0 := by
  unfold spPos27_11
  cases b <;> simp
theorem spNeg27_11_zero (b : Bool) : spNeg27_11 b 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = 0 := by
  unfold spNeg27_11
  cases b <;> simp
def spPos27_12 (b : Bool) (v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 : ℕ) : ℕ :=
  cond b ((v1 + 2 * v2 + 4 * v3 + 8 * v4 + 16 * v5 + 32 * v6 + 64 * v7 + 128 * v8 +
    256 * v9 + 512 * v10 + 1024 * v11 + 2048 * v12 + 4096 * v13 + 8192 * v14 + 16384 * v15) * 1) 0
def spNeg27_12 (b : Bool) (v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 : ℕ) : ℕ :=
  cond (!b) ((v1 + 2 * v2 + 4 * v3 + 8 * v4 + 16 * v5 + 32 * v6 + 64 * v7 + 128 * v8 +
    256 * v9 + 512 * v10 + 1024 * v11 + 2048 * v12 + 4096 * v13 + 8192 * v14 + 16384 * v15) * 1) 0
theorem spPos27_12_eq (kv u s4 : ℕ) :
    spPos27_12 (kv.testBit 12) (cond (uRotBit u s4 1) 1 0) (cond (uRotBit u s4 2) 1 0)
      (cond (uRotBit u s4 3) 1 0) (cond (uRotBit u s4 4) 1 0) (cond (uRotBit u s4 5) 1 0)
      (cond (uRotBit u s4 6) 1 0) (cond (uRotBit u s4 7) 1 0) (cond (uRotBit u s4 8) 1 0)
      (cond (uRotBit u s4 9) 1 0) (cond (uRotBit u s4 10) 1 0) (cond (uRotBit u s4 11) 1 0)
      (cond (uRotBit u s4 12) 1 0) (cond (uRotBit u s4 13) 1 0) (cond (uRotBit u s4 14) 1 0)
      (cond (uRotBit u s4 15) 1 0) =
    slopeTermPos27 kv 12 1 15 1 s4 u := by
  unfold spPos27_12 slopeTermPos27
  cases kv.testBit 12
  · simp only [Bool.cond_false]
  · simp only [evalBits, Bool.cond_true, shiftLeft_eq_mul_pow]
    ring
theorem spNeg27_12_eq (kv u s4 : ℕ) :
    spNeg27_12 (kv.testBit 12) (cond (uRotBit u s4 1) 1 0) (cond (uRotBit u s4 2) 1 0)
      (cond (uRotBit u s4 3) 1 0) (cond (uRotBit u s4 4) 1 0) (cond (uRotBit u s4 5) 1 0)
      (cond (uRotBit u s4 6) 1 0) (cond (uRotBit u s4 7) 1 0) (cond (uRotBit u s4 8) 1 0)
      (cond (uRotBit u s4 9) 1 0) (cond (uRotBit u s4 10) 1 0) (cond (uRotBit u s4 11) 1 0)
      (cond (uRotBit u s4 12) 1 0) (cond (uRotBit u s4 13) 1 0) (cond (uRotBit u s4 14) 1 0)
      (cond (uRotBit u s4 15) 1 0) =
    slopeTermNeg27 kv 12 1 15 1 s4 u := by
  unfold spNeg27_12 slopeTermNeg27
  cases kv.testBit 12
  · simp only [evalBits, Bool.not_false, Bool.cond_true, shiftLeft_eq_mul_pow]
    ring
  · simp only [Bool.not_true, Bool.cond_false]
theorem spPos27_12_lin (b : Bool) (v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 : ℕ) :
    spPos27_12 b v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 =
      spPos27_12 b 1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 * v1 +
      spPos27_12 b 0 1 0 0 0 0 0 0 0 0 0 0 0 0 0 * v2 +
      spPos27_12 b 0 0 1 0 0 0 0 0 0 0 0 0 0 0 0 * v3 +
      spPos27_12 b 0 0 0 1 0 0 0 0 0 0 0 0 0 0 0 * v4 +
      spPos27_12 b 0 0 0 0 1 0 0 0 0 0 0 0 0 0 0 * v5 +
      spPos27_12 b 0 0 0 0 0 1 0 0 0 0 0 0 0 0 0 * v6 +
      spPos27_12 b 0 0 0 0 0 0 1 0 0 0 0 0 0 0 0 * v7 +
      spPos27_12 b 0 0 0 0 0 0 0 1 0 0 0 0 0 0 0 * v8 +
      spPos27_12 b 0 0 0 0 0 0 0 0 1 0 0 0 0 0 0 * v9 +
      spPos27_12 b 0 0 0 0 0 0 0 0 0 1 0 0 0 0 0 * v10 +
      spPos27_12 b 0 0 0 0 0 0 0 0 0 0 1 0 0 0 0 * v11 +
      spPos27_12 b 0 0 0 0 0 0 0 0 0 0 0 1 0 0 0 * v12 +
      spPos27_12 b 0 0 0 0 0 0 0 0 0 0 0 0 1 0 0 * v13 +
      spPos27_12 b 0 0 0 0 0 0 0 0 0 0 0 0 0 1 0 * v14 +
      spPos27_12 b 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1 * v15 := by
  unfold spPos27_12
  cases b <;> simp only [Bool.cond_true, Bool.cond_false] <;> ring
theorem spNeg27_12_lin (b : Bool) (v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 : ℕ) :
    spNeg27_12 b v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 =
      spNeg27_12 b 1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 * v1 +
      spNeg27_12 b 0 1 0 0 0 0 0 0 0 0 0 0 0 0 0 * v2 +
      spNeg27_12 b 0 0 1 0 0 0 0 0 0 0 0 0 0 0 0 * v3 +
      spNeg27_12 b 0 0 0 1 0 0 0 0 0 0 0 0 0 0 0 * v4 +
      spNeg27_12 b 0 0 0 0 1 0 0 0 0 0 0 0 0 0 0 * v5 +
      spNeg27_12 b 0 0 0 0 0 1 0 0 0 0 0 0 0 0 0 * v6 +
      spNeg27_12 b 0 0 0 0 0 0 1 0 0 0 0 0 0 0 0 * v7 +
      spNeg27_12 b 0 0 0 0 0 0 0 1 0 0 0 0 0 0 0 * v8 +
      spNeg27_12 b 0 0 0 0 0 0 0 0 1 0 0 0 0 0 0 * v9 +
      spNeg27_12 b 0 0 0 0 0 0 0 0 0 1 0 0 0 0 0 * v10 +
      spNeg27_12 b 0 0 0 0 0 0 0 0 0 0 1 0 0 0 0 * v11 +
      spNeg27_12 b 0 0 0 0 0 0 0 0 0 0 0 1 0 0 0 * v12 +
      spNeg27_12 b 0 0 0 0 0 0 0 0 0 0 0 0 1 0 0 * v13 +
      spNeg27_12 b 0 0 0 0 0 0 0 0 0 0 0 0 0 1 0 * v14 +
      spNeg27_12 b 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1 * v15 := by
  unfold spNeg27_12
  cases b <;>
    simp only [Bool.not_true, Bool.not_false, Bool.cond_true, Bool.cond_false] <;>
    ring
theorem spPos27_12_zero (b : Bool) : spPos27_12 b 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = 0 := by
  unfold spPos27_12
  cases b <;> simp
theorem spNeg27_12_zero (b : Bool) : spNeg27_12 b 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = 0 := by
  unfold spNeg27_12
  cases b <;> simp
def spPos27_13 (b : Bool) (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 : ℕ) : ℕ :=
  cond b ((v0 + 2 * v1 + 4 * v2 + 8 * v3 + 16 * v4 + 32 * v5 + 64 * v6 + 128 * v7 +
    256 * v8 + 512 * v9 + 1024 * v10 + 2048 * v11 + 4096 * v12 + 8192 * v13 + 16384 * v14 +
    32768 * v15) * 1) 0
def spNeg27_13 (b : Bool) (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 : ℕ) : ℕ :=
  cond (!b) ((v0 + 2 * v1 + 4 * v2 + 8 * v3 + 16 * v4 + 32 * v5 + 64 * v6 + 128 * v7 +
    256 * v8 + 512 * v9 + 1024 * v10 + 2048 * v11 + 4096 * v12 + 8192 * v13 + 16384 * v14 +
    32768 * v15) * 1) 0
theorem spPos27_13_eq (kv u s4 : ℕ) :
    spPos27_13 (kv.testBit 13) (cond (uRotBit u s4 0) 1 0) (cond (uRotBit u s4 1) 1 0)
      (cond (uRotBit u s4 2) 1 0) (cond (uRotBit u s4 3) 1 0) (cond (uRotBit u s4 4) 1 0)
      (cond (uRotBit u s4 5) 1 0) (cond (uRotBit u s4 6) 1 0) (cond (uRotBit u s4 7) 1 0)
      (cond (uRotBit u s4 8) 1 0) (cond (uRotBit u s4 9) 1 0) (cond (uRotBit u s4 10) 1 0)
      (cond (uRotBit u s4 11) 1 0) (cond (uRotBit u s4 12) 1 0) (cond (uRotBit u s4 13) 1 0)
      (cond (uRotBit u s4 14) 1 0) (cond (uRotBit u s4 15) 1 0) =
    slopeTermPos27 kv 13 0 16 1 s4 u := by
  unfold spPos27_13 slopeTermPos27
  cases kv.testBit 13
  · simp only [Bool.cond_false]
  · simp only [evalBits, Bool.cond_true, shiftLeft_eq_mul_pow]
    ring
theorem spNeg27_13_eq (kv u s4 : ℕ) :
    spNeg27_13 (kv.testBit 13) (cond (uRotBit u s4 0) 1 0) (cond (uRotBit u s4 1) 1 0)
      (cond (uRotBit u s4 2) 1 0) (cond (uRotBit u s4 3) 1 0) (cond (uRotBit u s4 4) 1 0)
      (cond (uRotBit u s4 5) 1 0) (cond (uRotBit u s4 6) 1 0) (cond (uRotBit u s4 7) 1 0)
      (cond (uRotBit u s4 8) 1 0) (cond (uRotBit u s4 9) 1 0) (cond (uRotBit u s4 10) 1 0)
      (cond (uRotBit u s4 11) 1 0) (cond (uRotBit u s4 12) 1 0) (cond (uRotBit u s4 13) 1 0)
      (cond (uRotBit u s4 14) 1 0) (cond (uRotBit u s4 15) 1 0) =
    slopeTermNeg27 kv 13 0 16 1 s4 u := by
  unfold spNeg27_13 slopeTermNeg27
  cases kv.testBit 13
  · simp only [evalBits, Bool.not_false, Bool.cond_true, shiftLeft_eq_mul_pow]
    ring
  · simp only [Bool.not_true, Bool.cond_false]
theorem spPos27_13_lin (b : Bool) (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 : ℕ) :
    spPos27_13 b v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 =
      spPos27_13 b 1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 * v0 +
      spPos27_13 b 0 1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 * v1 +
      spPos27_13 b 0 0 1 0 0 0 0 0 0 0 0 0 0 0 0 0 * v2 +
      spPos27_13 b 0 0 0 1 0 0 0 0 0 0 0 0 0 0 0 0 * v3 +
      spPos27_13 b 0 0 0 0 1 0 0 0 0 0 0 0 0 0 0 0 * v4 +
      spPos27_13 b 0 0 0 0 0 1 0 0 0 0 0 0 0 0 0 0 * v5 +
      spPos27_13 b 0 0 0 0 0 0 1 0 0 0 0 0 0 0 0 0 * v6 +
      spPos27_13 b 0 0 0 0 0 0 0 1 0 0 0 0 0 0 0 0 * v7 +
      spPos27_13 b 0 0 0 0 0 0 0 0 1 0 0 0 0 0 0 0 * v8 +
      spPos27_13 b 0 0 0 0 0 0 0 0 0 1 0 0 0 0 0 0 * v9 +
      spPos27_13 b 0 0 0 0 0 0 0 0 0 0 1 0 0 0 0 0 * v10 +
      spPos27_13 b 0 0 0 0 0 0 0 0 0 0 0 1 0 0 0 0 * v11 +
      spPos27_13 b 0 0 0 0 0 0 0 0 0 0 0 0 1 0 0 0 * v12 +
      spPos27_13 b 0 0 0 0 0 0 0 0 0 0 0 0 0 1 0 0 * v13 +
      spPos27_13 b 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1 0 * v14 +
      spPos27_13 b 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1 * v15 := by
  unfold spPos27_13
  cases b <;> simp only [Bool.cond_true, Bool.cond_false] <;> ring
theorem spNeg27_13_lin (b : Bool) (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 : ℕ) :
    spNeg27_13 b v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 =
      spNeg27_13 b 1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 * v0 +
      spNeg27_13 b 0 1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 * v1 +
      spNeg27_13 b 0 0 1 0 0 0 0 0 0 0 0 0 0 0 0 0 * v2 +
      spNeg27_13 b 0 0 0 1 0 0 0 0 0 0 0 0 0 0 0 0 * v3 +
      spNeg27_13 b 0 0 0 0 1 0 0 0 0 0 0 0 0 0 0 0 * v4 +
      spNeg27_13 b 0 0 0 0 0 1 0 0 0 0 0 0 0 0 0 0 * v5 +
      spNeg27_13 b 0 0 0 0 0 0 1 0 0 0 0 0 0 0 0 0 * v6 +
      spNeg27_13 b 0 0 0 0 0 0 0 1 0 0 0 0 0 0 0 0 * v7 +
      spNeg27_13 b 0 0 0 0 0 0 0 0 1 0 0 0 0 0 0 0 * v8 +
      spNeg27_13 b 0 0 0 0 0 0 0 0 0 1 0 0 0 0 0 0 * v9 +
      spNeg27_13 b 0 0 0 0 0 0 0 0 0 0 1 0 0 0 0 0 * v10 +
      spNeg27_13 b 0 0 0 0 0 0 0 0 0 0 0 1 0 0 0 0 * v11 +
      spNeg27_13 b 0 0 0 0 0 0 0 0 0 0 0 0 1 0 0 0 * v12 +
      spNeg27_13 b 0 0 0 0 0 0 0 0 0 0 0 0 0 1 0 0 * v13 +
      spNeg27_13 b 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1 0 * v14 +
      spNeg27_13 b 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1 * v15 := by
  unfold spNeg27_13
  cases b <;>
    simp only [Bool.not_true, Bool.not_false, Bool.cond_true, Bool.cond_false] <;>
    ring
def spPos27_14 (b : Bool) (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 : ℕ) : ℕ :=
  cond b ((v0 + 2 * v1 + 4 * v2 + 8 * v3 + 16 * v4 + 32 * v5 + 64 * v6 + 128 * v7 +
    256 * v8 + 512 * v9 + 1024 * v10 + 2048 * v11 + 4096 * v12 + 8192 * v13 + 16384 * v14 +
    32768 * v15) * 2) 0
def spNeg27_14 (b : Bool) (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 : ℕ) : ℕ :=
  cond (!b) ((v0 + 2 * v1 + 4 * v2 + 8 * v3 + 16 * v4 + 32 * v5 + 64 * v6 + 128 * v7 +
    256 * v8 + 512 * v9 + 1024 * v10 + 2048 * v11 + 4096 * v12 + 8192 * v13 + 16384 * v14 +
    32768 * v15) * 2) 0
theorem spPos27_14_eq (kv u s4 : ℕ) :
    spPos27_14 (kv.testBit 14) (cond (uRotBit u s4 0) 1 0) (cond (uRotBit u s4 1) 1 0)
      (cond (uRotBit u s4 2) 1 0) (cond (uRotBit u s4 3) 1 0) (cond (uRotBit u s4 4) 1 0)
      (cond (uRotBit u s4 5) 1 0) (cond (uRotBit u s4 6) 1 0) (cond (uRotBit u s4 7) 1 0)
      (cond (uRotBit u s4 8) 1 0) (cond (uRotBit u s4 9) 1 0) (cond (uRotBit u s4 10) 1 0)
      (cond (uRotBit u s4 11) 1 0) (cond (uRotBit u s4 12) 1 0) (cond (uRotBit u s4 13) 1 0)
      (cond (uRotBit u s4 14) 1 0) (cond (uRotBit u s4 15) 1 0) =
    slopeTermPos27 kv 14 0 16 2 s4 u := by
  unfold spPos27_14 slopeTermPos27
  cases kv.testBit 14
  · simp only [Bool.cond_false]
  · simp only [evalBits, Bool.cond_true, shiftLeft_eq_mul_pow]
    ring
theorem spNeg27_14_eq (kv u s4 : ℕ) :
    spNeg27_14 (kv.testBit 14) (cond (uRotBit u s4 0) 1 0) (cond (uRotBit u s4 1) 1 0)
      (cond (uRotBit u s4 2) 1 0) (cond (uRotBit u s4 3) 1 0) (cond (uRotBit u s4 4) 1 0)
      (cond (uRotBit u s4 5) 1 0) (cond (uRotBit u s4 6) 1 0) (cond (uRotBit u s4 7) 1 0)
      (cond (uRotBit u s4 8) 1 0) (cond (uRotBit u s4 9) 1 0) (cond (uRotBit u s4 10) 1 0)
      (cond (uRotBit u s4 11) 1 0) (cond (uRotBit u s4 12) 1 0) (cond (uRotBit u s4 13) 1 0)
      (cond (uRotBit u s4 14) 1 0) (cond (uRotBit u s4 15) 1 0) =
    slopeTermNeg27 kv 14 0 16 2 s4 u := by
  unfold spNeg27_14 slopeTermNeg27
  cases kv.testBit 14
  · simp only [evalBits, Bool.not_false, Bool.cond_true, shiftLeft_eq_mul_pow]
    ring
  · simp only [Bool.not_true, Bool.cond_false]
theorem spPos27_14_lin (b : Bool) (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 : ℕ) :
    spPos27_14 b v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 =
      spPos27_14 b 1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 * v0 +
      spPos27_14 b 0 1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 * v1 +
      spPos27_14 b 0 0 1 0 0 0 0 0 0 0 0 0 0 0 0 0 * v2 +
      spPos27_14 b 0 0 0 1 0 0 0 0 0 0 0 0 0 0 0 0 * v3 +
      spPos27_14 b 0 0 0 0 1 0 0 0 0 0 0 0 0 0 0 0 * v4 +
      spPos27_14 b 0 0 0 0 0 1 0 0 0 0 0 0 0 0 0 0 * v5 +
      spPos27_14 b 0 0 0 0 0 0 1 0 0 0 0 0 0 0 0 0 * v6 +
      spPos27_14 b 0 0 0 0 0 0 0 1 0 0 0 0 0 0 0 0 * v7 +
      spPos27_14 b 0 0 0 0 0 0 0 0 1 0 0 0 0 0 0 0 * v8 +
      spPos27_14 b 0 0 0 0 0 0 0 0 0 1 0 0 0 0 0 0 * v9 +
      spPos27_14 b 0 0 0 0 0 0 0 0 0 0 1 0 0 0 0 0 * v10 +
      spPos27_14 b 0 0 0 0 0 0 0 0 0 0 0 1 0 0 0 0 * v11 +
      spPos27_14 b 0 0 0 0 0 0 0 0 0 0 0 0 1 0 0 0 * v12 +
      spPos27_14 b 0 0 0 0 0 0 0 0 0 0 0 0 0 1 0 0 * v13 +
      spPos27_14 b 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1 0 * v14 +
      spPos27_14 b 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1 * v15 := by
  unfold spPos27_14
  cases b <;> simp only [Bool.cond_true, Bool.cond_false] <;> ring
theorem spNeg27_14_lin (b : Bool) (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 : ℕ) :
    spNeg27_14 b v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 =
      spNeg27_14 b 1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 * v0 +
      spNeg27_14 b 0 1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 * v1 +
      spNeg27_14 b 0 0 1 0 0 0 0 0 0 0 0 0 0 0 0 0 * v2 +
      spNeg27_14 b 0 0 0 1 0 0 0 0 0 0 0 0 0 0 0 0 * v3 +
      spNeg27_14 b 0 0 0 0 1 0 0 0 0 0 0 0 0 0 0 0 * v4 +
      spNeg27_14 b 0 0 0 0 0 1 0 0 0 0 0 0 0 0 0 0 * v5 +
      spNeg27_14 b 0 0 0 0 0 0 1 0 0 0 0 0 0 0 0 0 * v6 +
      spNeg27_14 b 0 0 0 0 0 0 0 1 0 0 0 0 0 0 0 0 * v7 +
      spNeg27_14 b 0 0 0 0 0 0 0 0 1 0 0 0 0 0 0 0 * v8 +
      spNeg27_14 b 0 0 0 0 0 0 0 0 0 1 0 0 0 0 0 0 * v9 +
      spNeg27_14 b 0 0 0 0 0 0 0 0 0 0 1 0 0 0 0 0 * v10 +
      spNeg27_14 b 0 0 0 0 0 0 0 0 0 0 0 1 0 0 0 0 * v11 +
      spNeg27_14 b 0 0 0 0 0 0 0 0 0 0 0 0 1 0 0 0 * v12 +
      spNeg27_14 b 0 0 0 0 0 0 0 0 0 0 0 0 0 1 0 0 * v13 +
      spNeg27_14 b 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1 0 * v14 +
      spNeg27_14 b 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1 * v15 := by
  unfold spNeg27_14
  cases b <;>
    simp only [Bool.not_true, Bool.not_false, Bool.cond_true, Bool.cond_false] <;>
    ring
def posSlope27Fast (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 : Bool)
    (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 : ℕ) : ℕ :=
  spBase27 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 +
  spPos27_0 b0 v13 v14 v15 +
  spPos27_1 b1 v12 v13 v14 v15 +
  spPos27_2 b2 v11 v12 v13 v14 v15 +
  spPos27_3 b3 v10 v11 v12 v13 v14 v15 +
  spPos27_4 b4 v9 v10 v11 v12 v13 v14 v15 +
  spPos27_5 b5 v8 v9 v10 v11 v12 v13 v14 v15 +
  spPos27_6 b6 v7 v8 v9 v10 v11 v12 v13 v14 v15 +
  spPos27_7 b7 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 +
  spPos27_8 b8 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 +
  spPos27_9 b9 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 +
  spPos27_10 b10 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 +
  spPos27_11 b11 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 +
  spPos27_12 b12 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 +
  spPos27_13 b13 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 +
  spPos27_14 b14 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
def negSlope27Fast (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 : Bool)
    (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 : ℕ) : ℕ :=
  spNeg27_0 b0 v13 v14 v15 +
  spNeg27_1 b1 v12 v13 v14 v15 +
  spNeg27_2 b2 v11 v12 v13 v14 v15 +
  spNeg27_3 b3 v10 v11 v12 v13 v14 v15 +
  spNeg27_4 b4 v9 v10 v11 v12 v13 v14 v15 +
  spNeg27_5 b5 v8 v9 v10 v11 v12 v13 v14 v15 +
  spNeg27_6 b6 v7 v8 v9 v10 v11 v12 v13 v14 v15 +
  spNeg27_7 b7 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 +
  spNeg27_8 b8 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 +
  spNeg27_9 b9 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 +
  spNeg27_10 b10 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 +
  spNeg27_11 b11 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 +
  spNeg27_12 b12 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 +
  spNeg27_13 b13 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 +
  spNeg27_14 b14 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
theorem posSlope27Fast_eq (kv u s4 : ℕ) :
    posSlope27Fast (kv.testBit 0) (kv.testBit 1) (kv.testBit 2) (kv.testBit 3) (kv.testBit 4)
      (kv.testBit 5) (kv.testBit 6) (kv.testBit 7) (kv.testBit 8) (kv.testBit 9)
      (kv.testBit 10) (kv.testBit 11) (kv.testBit 12) (kv.testBit 13) (kv.testBit 14)
      (cond (uRotBit u s4 0) 1 0) (cond (uRotBit u s4 1) 1 0) (cond (uRotBit u s4 2) 1 0)
      (cond (uRotBit u s4 3) 1 0) (cond (uRotBit u s4 4) 1 0) (cond (uRotBit u s4 5) 1 0)
      (cond (uRotBit u s4 6) 1 0) (cond (uRotBit u s4 7) 1 0) (cond (uRotBit u s4 8) 1 0)
      (cond (uRotBit u s4 9) 1 0) (cond (uRotBit u s4 10) 1 0) (cond (uRotBit u s4 11) 1 0)
      (cond (uRotBit u s4 12) 1 0) (cond (uRotBit u s4 13) 1 0) (cond (uRotBit u s4 14) 1 0)
      (cond (uRotBit u s4 15) 1 0) = posSlope27 kv s4 u := by
  unfold posSlope27Fast posSlope27
  rw [spBase27_eq, spPos27_0_eq, spPos27_1_eq, spPos27_2_eq, spPos27_3_eq, spPos27_4_eq,
    spPos27_5_eq, spPos27_6_eq, spPos27_7_eq, spPos27_8_eq, spPos27_9_eq, spPos27_10_eq,
    spPos27_11_eq, spPos27_12_eq, spPos27_13_eq, spPos27_14_eq]

theorem negSlope27Fast_eq (kv u s4 : ℕ) :
    negSlope27Fast (kv.testBit 0) (kv.testBit 1) (kv.testBit 2) (kv.testBit 3) (kv.testBit 4)
      (kv.testBit 5) (kv.testBit 6) (kv.testBit 7) (kv.testBit 8) (kv.testBit 9)
      (kv.testBit 10) (kv.testBit 11) (kv.testBit 12) (kv.testBit 13) (kv.testBit 14)
      (cond (uRotBit u s4 0) 1 0) (cond (uRotBit u s4 1) 1 0) (cond (uRotBit u s4 2) 1 0)
      (cond (uRotBit u s4 3) 1 0) (cond (uRotBit u s4 4) 1 0) (cond (uRotBit u s4 5) 1 0)
      (cond (uRotBit u s4 6) 1 0) (cond (uRotBit u s4 7) 1 0) (cond (uRotBit u s4 8) 1 0)
      (cond (uRotBit u s4 9) 1 0) (cond (uRotBit u s4 10) 1 0) (cond (uRotBit u s4 11) 1 0)
      (cond (uRotBit u s4 12) 1 0) (cond (uRotBit u s4 13) 1 0) (cond (uRotBit u s4 14) 1 0)
      (cond (uRotBit u s4 15) 1 0) = negSlope27 kv s4 u := by
  unfold negSlope27Fast negSlope27
  rw [spNeg27_0_eq, spNeg27_1_eq, spNeg27_2_eq, spNeg27_3_eq, spNeg27_4_eq, spNeg27_5_eq,
    spNeg27_6_eq, spNeg27_7_eq, spNeg27_8_eq, spNeg27_9_eq, spNeg27_10_eq, spNeg27_11_eq,
    spNeg27_12_eq, spNeg27_13_eq, spNeg27_14_eq]

def linComb16 (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
    v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 : ℕ) : ℕ :=
  Nat.add (Nat.mul w0 v0) (Nat.add (Nat.mul w1 v1)
    (Nat.add (Nat.mul w2 v2) (Nat.add (Nat.mul w3 v3)
      (Nat.add (Nat.mul w4 v4) (Nat.add (Nat.mul w5 v5)
        (Nat.add (Nat.mul w6 v6) (Nat.add (Nat.mul w7 v7)
          (Nat.add (Nat.mul w8 v8) (Nat.add (Nat.mul w9 v9)
            (Nat.add (Nat.mul w10 v10) (Nat.add (Nat.mul w11 v11)
              (Nat.add (Nat.mul w12 v12) (Nat.add (Nat.mul w13 v13)
                (Nat.add (Nat.mul w14 v14) (Nat.mul w15 v15)))))))))))))))

theorem linComb16_posSlope27Fast (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 : Bool)
    (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 : ℕ) :
    linComb16
      (posSlope27Fast b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14
        1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
      (posSlope27Fast b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14
        0 1 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
      (posSlope27Fast b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14
        0 0 1 0 0 0 0 0 0 0 0 0 0 0 0 0)
      (posSlope27Fast b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14
        0 0 0 1 0 0 0 0 0 0 0 0 0 0 0 0)
      (posSlope27Fast b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14
        0 0 0 0 1 0 0 0 0 0 0 0 0 0 0 0)
      (posSlope27Fast b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14
        0 0 0 0 0 1 0 0 0 0 0 0 0 0 0 0)
      (posSlope27Fast b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14
        0 0 0 0 0 0 1 0 0 0 0 0 0 0 0 0)
      (posSlope27Fast b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14
        0 0 0 0 0 0 0 1 0 0 0 0 0 0 0 0)
      (posSlope27Fast b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14
        0 0 0 0 0 0 0 0 1 0 0 0 0 0 0 0)
      (posSlope27Fast b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14
        0 0 0 0 0 0 0 0 0 1 0 0 0 0 0 0)
      (posSlope27Fast b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14
        0 0 0 0 0 0 0 0 0 0 1 0 0 0 0 0)
      (posSlope27Fast b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14
        0 0 0 0 0 0 0 0 0 0 0 1 0 0 0 0)
      (posSlope27Fast b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14
        0 0 0 0 0 0 0 0 0 0 0 0 1 0 0 0)
      (posSlope27Fast b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14
        0 0 0 0 0 0 0 0 0 0 0 0 0 1 0 0)
      (posSlope27Fast b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14
        0 0 0 0 0 0 0 0 0 0 0 0 0 0 1 0)
      (posSlope27Fast b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14
        0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1)
      v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 =
    posSlope27Fast b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14
      v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 := by
  unfold linComb16 posSlope27Fast
  rw [spBase27_lin v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15,
      spPos27_0_lin b0 v13 v14 v15,
      spPos27_1_lin b1 v12 v13 v14 v15,
      spPos27_2_lin b2 v11 v12 v13 v14 v15,
      spPos27_3_lin b3 v10 v11 v12 v13 v14 v15,
      spPos27_4_lin b4 v9 v10 v11 v12 v13 v14 v15,
      spPos27_5_lin b5 v8 v9 v10 v11 v12 v13 v14 v15,
      spPos27_6_lin b6 v7 v8 v9 v10 v11 v12 v13 v14 v15,
      spPos27_7_lin b7 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15,
      spPos27_8_lin b8 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15,
      spPos27_9_lin b9 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15,
      spPos27_10_lin b10 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15,
      spPos27_11_lin b11 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15,
      spPos27_12_lin b12 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15,
      spPos27_13_lin b13 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15,
      spPos27_14_lin b14 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15]
  simp only [nat_add_eq, nat_mul_eq, spPos27_0_zero b0, spPos27_1_zero b1, spPos27_2_zero b2,
    spPos27_3_zero b3, spPos27_4_zero b4, spPos27_5_zero b5, spPos27_6_zero b6,
    spPos27_7_zero b7, spPos27_8_zero b8, spPos27_9_zero b9, spPos27_10_zero b10,
    spPos27_11_zero b11, spPos27_12_zero b12]
  ring

theorem linComb16_negSlope27Fast (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 : Bool)
    (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 : ℕ) :
    linComb16
      (negSlope27Fast b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14
        1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
      (negSlope27Fast b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14
        0 1 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
      (negSlope27Fast b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14
        0 0 1 0 0 0 0 0 0 0 0 0 0 0 0 0)
      (negSlope27Fast b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14
        0 0 0 1 0 0 0 0 0 0 0 0 0 0 0 0)
      (negSlope27Fast b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14
        0 0 0 0 1 0 0 0 0 0 0 0 0 0 0 0)
      (negSlope27Fast b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14
        0 0 0 0 0 1 0 0 0 0 0 0 0 0 0 0)
      (negSlope27Fast b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14
        0 0 0 0 0 0 1 0 0 0 0 0 0 0 0 0)
      (negSlope27Fast b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14
        0 0 0 0 0 0 0 1 0 0 0 0 0 0 0 0)
      (negSlope27Fast b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14
        0 0 0 0 0 0 0 0 1 0 0 0 0 0 0 0)
      (negSlope27Fast b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14
        0 0 0 0 0 0 0 0 0 1 0 0 0 0 0 0)
      (negSlope27Fast b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14
        0 0 0 0 0 0 0 0 0 0 1 0 0 0 0 0)
      (negSlope27Fast b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14
        0 0 0 0 0 0 0 0 0 0 0 1 0 0 0 0)
      (negSlope27Fast b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14
        0 0 0 0 0 0 0 0 0 0 0 0 1 0 0 0)
      (negSlope27Fast b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14
        0 0 0 0 0 0 0 0 0 0 0 0 0 1 0 0)
      (negSlope27Fast b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14
        0 0 0 0 0 0 0 0 0 0 0 0 0 0 1 0)
      (negSlope27Fast b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14
        0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1)
      v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 =
    negSlope27Fast b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14
      v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 := by
  unfold linComb16 negSlope27Fast
  rw [spNeg27_0_lin b0 v13 v14 v15,
      spNeg27_1_lin b1 v12 v13 v14 v15,
      spNeg27_2_lin b2 v11 v12 v13 v14 v15,
      spNeg27_3_lin b3 v10 v11 v12 v13 v14 v15,
      spNeg27_4_lin b4 v9 v10 v11 v12 v13 v14 v15,
      spNeg27_5_lin b5 v8 v9 v10 v11 v12 v13 v14 v15,
      spNeg27_6_lin b6 v7 v8 v9 v10 v11 v12 v13 v14 v15,
      spNeg27_7_lin b7 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15,
      spNeg27_8_lin b8 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15,
      spNeg27_9_lin b9 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15,
      spNeg27_10_lin b10 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15,
      spNeg27_11_lin b11 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15,
      spNeg27_12_lin b12 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15,
      spNeg27_13_lin b13 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15,
      spNeg27_14_lin b14 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15]
  simp only [nat_add_eq, nat_mul_eq, spNeg27_0_zero b0, spNeg27_1_zero b1, spNeg27_2_zero b2,
    spNeg27_3_zero b3, spNeg27_4_zero b4, spNeg27_5_zero b5, spNeg27_6_zero b6,
    spNeg27_7_zero b7, spNeg27_8_zero b8, spNeg27_9_zero b9, spNeg27_10_zero b10,
    spNeg27_11_zero b11, spNeg27_12_zero b12]
  ring

def stepPt0_25Fast4 (zPos zNeg XA : ℕ) (g gn : GS) (k : GS → GS → Bool) : Bool :=
  match adv XA advFuel g gn with
  | (g1, gn1) =>
    forceNatBool (Nat.sub zPos zNeg) fun wBase =>
    forceNatBool (Nat.div wBase 16) fun z25 =>
    forceNatBool (Nat.mul z25 SCALE37) fun z37 =>
    cond (and (Nat.ble zNeg zPos)
          (and (Nat.blt z25 16777216)
          (and (Nat.ble g1.su XA)
          (and (Nat.ble z37 (Nat.add ckEPS25 (loB0Fast g1 gn1 XA)))
               (Nat.ble (hiBFast g1 gn1 XA) (Nat.add z37 ckEPS25))))))
      (k g1 gn1)
      false

theorem stepPt0_25Fast4_eq (zPos zNeg XA : ℕ) (g gn : GS) (k : GS → GS → Bool) :
    stepPt0_25Fast4 zPos zNeg XA g gn k = stepPt0_25 zPos zNeg XA g gn k := by
  unfold stepPt0_25Fast4 stepPt0_25
  simp only [forceNatBool_eq, loB0Fast_eq, hiBFast_eq, nat_add_eq, nat_sub_eq, nat_mul_eq,
    nat_div_eq, Bool.and_assoc]

def stepPtsSub_25Fast4 (zPos zNeg blk dMax wMax gBlk1 dMin33 blkEps XA XB : ℕ)
    (g gn : GS) (k : GS → GS → Bool) : Bool :=
  match adv XA advFuel g gn with
  | (g1, gn1) =>
    match adv XB advFuel g1 gn1 with
    | (g2, gn2) =>
      forceNatBool (Nat.sub zPos zNeg) fun wBase =>
      forceNatBool (Nat.mul blk wBase) fun blkW =>
      cond (and (Nat.ble zNeg zPos)
            (and (Nat.blt (Nat.add wBase wMax) 268435456)
            (and (Nat.ble g1.su XA)
            (and (Nat.ble (Nat.mul (Nat.add blkW dMax) SCALE33)
                (Nat.mul blk (Nat.add ckEPS25 (loBFast g1 XA))))
            (and (Nat.ble (Nat.mul (Nat.add (Nat.add blkW gBlk1) dMax) SCALE33)
                (Nat.mul blk (Nat.add ckEPS25 (loBFast g1 XB))))
            (and (Nat.ble (Nat.add (Nat.mul blk (hiBFast g1 gn1 XA)) dMin33)
                (Nat.mul blk (Nat.add (Nat.mul wBase SCALE33) ckEPS25)))
              (Nat.ble (Nat.add (Nat.mul blk (hiBFast g2 gn2 XB)) dMin33)
                (Nat.add (Nat.mul (Nat.add blkW gBlk1) SCALE33) blkEps))))))))
        (k g2 gn2)
        false

theorem stepPtsSub_25Fast4_eq (zPos zNeg blk gNum dMax dMinAbs wMax XA XB : ℕ)
    (g gn : GS) (k : GS → GS → Bool) :
    stepPtsSub_25Fast4 zPos zNeg blk dMax wMax
      (gNum * (blk - 1))
      ((dMinAbs + 15 * blk) * SCALE33)
      (blk * ckEPS25) XA XB g gn k =
    stepPtsSub_25 zPos zNeg blk gNum dMax dMinAbs wMax XA XB g gn k := by
  unfold stepPtsSub_25Fast4 stepPtsSub_25
  simp only [forceNatBool_eq, loBFast_eq, hiBFast_eq, nat_add_eq, nat_sub_eq, nat_mul_eq,
    Bool.and_assoc]

def walkLeafPos25Aux4 (L : Leaf25)
    (lc0 lc1 lc2 lc3 lc4 lc5 lc6 lc7 : Bool)
    (blk dMax wMax gBlk1 dMin33 blkEps
     wp0 wp1 wp2 wp3 wp4 wp5 wp6 wp7 wp8 wp9 wp10 wp11 wp12 wp13 wp14 wp15
     wn0 wn1 wn2 wn3 wn4 wn5 wn6 wn7 wn8 wn9 wn10 wn11 wn12 wn13 wn14 wn15
     w0 w1 w2 w3 w4 w5 w6 w7 w8
     s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 : ℕ) :
    ℕ → ℕ → GS → GS → (GS → GS → Bool) → Bool
  | 0, _, g, gn, k => k g gn
  | n + 1, u, g, gn, k =>
      forceNatBool (uRotBitFast4 u s0) fun v0 =>
      forceNatBool (uRotBitFast4 u s1) fun v1 =>
      forceNatBool (uRotBitFast4 u s2) fun v2 =>
      forceNatBool (uRotBitFast4 u s3) fun v3 =>
      forceNatBool (uRotBitFast4 u s4) fun v4 =>
      forceNatBool (uRotBitFast4 u s5) fun v5 =>
      forceNatBool (uRotBitFast4 u s6) fun v6 =>
      forceNatBool (uRotBitFast4 u s7) fun v7 =>
      forceNatBool (uRotBitFast4 u s8) fun v8 =>
      forceNatBool (uRotBitFast4 u s9) fun v9 =>
      forceNatBool (uRotBitFast4 u s10) fun v10 =>
      forceNatBool (uRotBitFast4 u s11) fun v11 =>
      forceNatBool (uRotBitFast4 u s12) fun v12 =>
      forceNatBool (uRotBitFast4 u s13) fun v13 =>
      forceNatBool (uRotBitFast4 u s14) fun v14 =>
      forceNatBool (uRotBitFast4 u s15) fun v15 =>
      forceNatBool (d9Fast4 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15) fun d9 =>
      forceNatBool (sq9ValFast4 w0 w1 w2 w3 w4 w5 w6 w7 w8 d9) fun sq9 =>
      forceNatBool (curvFromSq9Fast4 lc0 lc1 lc2 lc3 lc4 lc5 lc6 lc7 sq9) fun curv =>
      forceNatBool (Nat.add (Nat.add (Nat.add (Nat.mul 16 u) L.b_base)
        (linComb16 wp0 wp1 wp2 wp3 wp4 wp5 wp6 wp7 wp8 wp9 wp10 wp11 wp12 wp13 wp14 wp15
                   v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15))
        curv) fun zp =>
      forceNatBool (Nat.add 1024
        (linComb16 wn0 wn1 wn2 wn3 wn4 wn5 wn6 wn7 wn8 wn9 wn10 wn11 wn12 wn13 wn14 wn15
                   v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15)) fun zn =>
      forceNatBool (Nat.mul u SCALE37) fun xa =>
      forceNatBool (Nat.add u blk) fun u_next =>
      cond (Nat.beq L.b_sub 0)
        (stepPt0_25Fast4 zp zn xa g gn fun g' gn' =>
          walkLeafPos25Aux4 L lc0 lc1 lc2 lc3 lc4 lc5 lc6 lc7 blk dMax wMax gBlk1 dMin33 blkEps
            wp0 wp1 wp2 wp3 wp4 wp5 wp6 wp7 wp8 wp9 wp10 wp11 wp12 wp13 wp14 wp15
            wn0 wn1 wn2 wn3 wn4 wn5 wn6 wn7 wn8 wn9 wn10 wn11 wn12 wn13 wn14 wn15
            w0 w1 w2 w3 w4 w5 w6 w7 w8
            s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15
            n u_next g' gn' k)
        (forceNatBool (Nat.mul (Nat.sub u_next 1) SCALE37) fun xb =>
         stepPtsSub_25Fast4 zp zn blk dMax wMax gBlk1 dMin33 blkEps xa xb g gn fun g' gn' =>
          walkLeafPos25Aux4 L lc0 lc1 lc2 lc3 lc4 lc5 lc6 lc7 blk dMax wMax gBlk1 dMin33 blkEps
            wp0 wp1 wp2 wp3 wp4 wp5 wp6 wp7 wp8 wp9 wp10 wp11 wp12 wp13 wp14 wp15
            wn0 wn1 wn2 wn3 wn4 wn5 wn6 wn7 wn8 wn9 wn10 wn11 wn12 wn13 wn14 wn15
            w0 w1 w2 w3 w4 w5 w6 w7 w8
            s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15
            n u_next g' gn' k)

theorem walkLeafPos25Aux4_eq (L : Leaf25) :
    ∀ (n u : ℕ) (g gn : GS) (k : GS → GS → Bool),
      let b0 := L.kv.testBit 0
      let b1 := L.kv.testBit 1
      let b2 := L.kv.testBit 2
      let b3 := L.kv.testBit 3
      let b4 := L.kv.testBit 4
      let b5 := L.kv.testBit 5
      let b6 := L.kv.testBit 6
      let b7 := L.kv.testBit 7
      let b8 := L.kv.testBit 8
      let b9 := L.kv.testBit 9
      let b10 := L.kv.testBit 10
      let b11 := L.kv.testBit 11
      let b12 := L.kv.testBit 12
      let b13 := L.kv.testBit 13
      let b14 := L.kv.testBit 14
      walkLeafPos25Aux4 L
        (L.lv.testBit 0) (L.lv.testBit 1) (L.lv.testBit 2) (L.lv.testBit 3)
        (L.lv.testBit 4) (L.lv.testBit 5) (L.lv.testBit 6) (L.lv.testBit 7)
        (Nat.shiftLeft 1 L.b_sub)
        (dMaxSum27 L.kv L.s4 (Nat.shiftLeft 1 L.b_sub) L.gNum L.b_sub)
        (wBitMaxSum27 L.kv L.s4 L.b_sub)
        (Nat.mul L.gNum (Nat.sub (Nat.shiftLeft 1 L.b_sub) 1))
        (Nat.mul
          (Nat.add (dMinAbsSum27 L.kv L.s4 (Nat.shiftLeft 1 L.b_sub) L.gNum L.b_sub)
            (Nat.mul 15 (Nat.shiftLeft 1 L.b_sub)))
          SCALE33)
        (Nat.mul (Nat.shiftLeft 1 L.b_sub) ckEPS25)
        (posSlope27Fast b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14
          1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
      (posSlope27Fast b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14
        0 1 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
      (posSlope27Fast b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14
        0 0 1 0 0 0 0 0 0 0 0 0 0 0 0 0)
      (posSlope27Fast b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14
        0 0 0 1 0 0 0 0 0 0 0 0 0 0 0 0)
      (posSlope27Fast b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14
        0 0 0 0 1 0 0 0 0 0 0 0 0 0 0 0)
      (posSlope27Fast b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14
        0 0 0 0 0 1 0 0 0 0 0 0 0 0 0 0)
      (posSlope27Fast b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14
        0 0 0 0 0 0 1 0 0 0 0 0 0 0 0 0)
      (posSlope27Fast b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14
        0 0 0 0 0 0 0 1 0 0 0 0 0 0 0 0)
      (posSlope27Fast b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14
        0 0 0 0 0 0 0 0 1 0 0 0 0 0 0 0)
      (posSlope27Fast b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14
        0 0 0 0 0 0 0 0 0 1 0 0 0 0 0 0)
      (posSlope27Fast b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14
        0 0 0 0 0 0 0 0 0 0 1 0 0 0 0 0)
      (posSlope27Fast b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14
        0 0 0 0 0 0 0 0 0 0 0 1 0 0 0 0)
      (posSlope27Fast b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14
        0 0 0 0 0 0 0 0 0 0 0 0 1 0 0 0)
      (posSlope27Fast b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14
        0 0 0 0 0 0 0 0 0 0 0 0 0 1 0 0)
      (posSlope27Fast b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14
        0 0 0 0 0 0 0 0 0 0 0 0 0 0 1 0)
      (posSlope27Fast b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14
        0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1)
        (negSlope27Fast b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14
          1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
      (negSlope27Fast b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14
        0 1 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
      (negSlope27Fast b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14
        0 0 1 0 0 0 0 0 0 0 0 0 0 0 0 0)
      (negSlope27Fast b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14
        0 0 0 1 0 0 0 0 0 0 0 0 0 0 0 0)
      (negSlope27Fast b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14
        0 0 0 0 1 0 0 0 0 0 0 0 0 0 0 0)
      (negSlope27Fast b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14
        0 0 0 0 0 1 0 0 0 0 0 0 0 0 0 0)
      (negSlope27Fast b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14
        0 0 0 0 0 0 1 0 0 0 0 0 0 0 0 0)
      (negSlope27Fast b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14
        0 0 0 0 0 0 0 1 0 0 0 0 0 0 0 0)
      (negSlope27Fast b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14
        0 0 0 0 0 0 0 0 1 0 0 0 0 0 0 0)
      (negSlope27Fast b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14
        0 0 0 0 0 0 0 0 0 1 0 0 0 0 0 0)
      (negSlope27Fast b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14
        0 0 0 0 0 0 0 0 0 0 1 0 0 0 0 0)
      (negSlope27Fast b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14
        0 0 0 0 0 0 0 0 0 0 0 1 0 0 0 0)
      (negSlope27Fast b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14
        0 0 0 0 0 0 0 0 0 0 0 0 1 0 0 0)
      (negSlope27Fast b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14
        0 0 0 0 0 0 0 0 0 0 0 0 0 1 0 0)
      (negSlope27Fast b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14
        0 0 0 0 0 0 0 0 0 0 0 0 0 0 1 0)
      (negSlope27Fast b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14
        0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1)
        (sq9Words.getD 0 0) (sq9Words.getD 1 0) (sq9Words.getD 2 0) (sq9Words.getD 3 0)
        (sq9Words.getD 4 0) (sq9Words.getD 5 0) (sq9Words.getD 6 0)
        (sq9Words.getD 7 0) (sq9Words.getD 8 0)
        (uRotSrc L.s4 0) (uRotSrc L.s4 1) (uRotSrc L.s4 2) (uRotSrc L.s4 3)
        (uRotSrc L.s4 4) (uRotSrc L.s4 5) (uRotSrc L.s4 6) (uRotSrc L.s4 7)
        (uRotSrc L.s4 8) (uRotSrc L.s4 9) (uRotSrc L.s4 10) (uRotSrc L.s4 11)
        (uRotSrc L.s4 12) (uRotSrc L.s4 13) (uRotSrc L.s4 14) (uRotSrc L.s4 15)
        n u g gn k =
      walkLeafPos25 L n u g gn k
  | 0, _, _, _, _ => rfl
  | n + 1, u, g, gn, k => by
      dsimp only
      unfold walkLeafPos25Aux4 walkLeafPos25 stepBlockPos25
      simp only [forceNatBool_eq, linComb16_posSlope27Fast, linComb16_negSlope27Fast,
        uRotBitFast4_eq, d9Fast4_eq, sq9ValFast4_eq, curvFromSq9Fast4_eq,
        stepPt0_25Fast4_eq, stepPtsSub_25Fast4_eq,
        shiftLeft_eq_mul_pow, one_mul, nat_add_eq, nat_sub_eq, nat_mul_eq]
      simp only [posSlope27Fast_eq, negSlope27Fast_eq]
      dsimp only [zPos27, zNeg27, curvVal27]
      cases Nat.beq L.b_sub 0 <;> dsimp only [cond] <;> congr 1 <;> funext g' gn' <;>
        simpa only [shiftLeft_eq_mul_pow, one_mul, nat_add_eq, nat_sub_eq, nat_mul_eq] using
          walkLeafPos25Aux4_eq L n (u + Nat.shiftLeft 1 L.b_sub) g' gn' k

def walkLeavesPos25Fast4 : List Leaf25 → GS → GS → Bool
  | [], _, _ => true
  | L :: ls, g, gn =>
      forceBoolBool (L.kv.testBit 0) fun b0 =>
      forceBoolBool (L.kv.testBit 1) fun b1 =>
      forceBoolBool (L.kv.testBit 2) fun b2 =>
      forceBoolBool (L.kv.testBit 3) fun b3 =>
      forceBoolBool (L.kv.testBit 4) fun b4 =>
      forceBoolBool (L.kv.testBit 5) fun b5 =>
      forceBoolBool (L.kv.testBit 6) fun b6 =>
      forceBoolBool (L.kv.testBit 7) fun b7 =>
      forceBoolBool (L.kv.testBit 8) fun b8 =>
      forceBoolBool (L.kv.testBit 9) fun b9 =>
      forceBoolBool (L.kv.testBit 10) fun b10 =>
      forceBoolBool (L.kv.testBit 11) fun b11 =>
      forceBoolBool (L.kv.testBit 12) fun b12 =>
      forceBoolBool (L.kv.testBit 13) fun b13 =>
      forceBoolBool (L.kv.testBit 14) fun b14 =>
      forceBoolBool (L.lv.testBit 0) fun lc0 =>
      forceBoolBool (L.lv.testBit 1) fun lc1 =>
      forceBoolBool (L.lv.testBit 2) fun lc2 =>
      forceBoolBool (L.lv.testBit 3) fun lc3 =>
      forceBoolBool (L.lv.testBit 4) fun lc4 =>
      forceBoolBool (L.lv.testBit 5) fun lc5 =>
      forceBoolBool (L.lv.testBit 6) fun lc6 =>
      forceBoolBool (L.lv.testBit 7) fun lc7 =>
      forceNatBool (Nat.shiftLeft 1 L.b_sub) fun blk =>
      forceNatBool (dMaxSum27 L.kv L.s4 blk L.gNum L.b_sub) fun dMax =>
      forceNatBool (dMinAbsSum27 L.kv L.s4 blk L.gNum L.b_sub) fun dMinAbs =>
      forceNatBool (wBitMaxSum27 L.kv L.s4 L.b_sub) fun wMax =>
      forceNatBool (Nat.mul L.gNum (Nat.sub blk 1)) fun gBlk1 =>
      forceNatBool (Nat.mul (Nat.add dMinAbs (Nat.mul 15 blk)) SCALE33) fun dMin33 =>
      forceNatBool (Nat.mul blk ckEPS25) fun blkEps =>
      forceNatBool
        (posSlope27Fast b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14
          1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) fun wp0 =>
      forceNatBool
        (posSlope27Fast b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14
          0 1 0 0 0 0 0 0 0 0 0 0 0 0 0 0) fun wp1 =>
      forceNatBool
        (posSlope27Fast b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14
          0 0 1 0 0 0 0 0 0 0 0 0 0 0 0 0) fun wp2 =>
      forceNatBool
        (posSlope27Fast b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14
          0 0 0 1 0 0 0 0 0 0 0 0 0 0 0 0) fun wp3 =>
      forceNatBool
        (posSlope27Fast b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14
          0 0 0 0 1 0 0 0 0 0 0 0 0 0 0 0) fun wp4 =>
      forceNatBool
        (posSlope27Fast b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14
          0 0 0 0 0 1 0 0 0 0 0 0 0 0 0 0) fun wp5 =>
      forceNatBool
        (posSlope27Fast b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14
          0 0 0 0 0 0 1 0 0 0 0 0 0 0 0 0) fun wp6 =>
      forceNatBool
        (posSlope27Fast b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14
          0 0 0 0 0 0 0 1 0 0 0 0 0 0 0 0) fun wp7 =>
      forceNatBool
        (posSlope27Fast b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14
          0 0 0 0 0 0 0 0 1 0 0 0 0 0 0 0) fun wp8 =>
      forceNatBool
        (posSlope27Fast b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14
          0 0 0 0 0 0 0 0 0 1 0 0 0 0 0 0) fun wp9 =>
      forceNatBool
        (posSlope27Fast b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14
          0 0 0 0 0 0 0 0 0 0 1 0 0 0 0 0) fun wp10 =>
      forceNatBool
        (posSlope27Fast b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14
          0 0 0 0 0 0 0 0 0 0 0 1 0 0 0 0) fun wp11 =>
      forceNatBool
        (posSlope27Fast b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14
          0 0 0 0 0 0 0 0 0 0 0 0 1 0 0 0) fun wp12 =>
      forceNatBool
        (posSlope27Fast b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14
          0 0 0 0 0 0 0 0 0 0 0 0 0 1 0 0) fun wp13 =>
      forceNatBool
        (posSlope27Fast b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14
          0 0 0 0 0 0 0 0 0 0 0 0 0 0 1 0) fun wp14 =>
      forceNatBool
        (posSlope27Fast b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14
          0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1) fun wp15 =>
      forceNatBool
        (negSlope27Fast b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14
          1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0) fun wn0 =>
      forceNatBool
        (negSlope27Fast b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14
          0 1 0 0 0 0 0 0 0 0 0 0 0 0 0 0) fun wn1 =>
      forceNatBool
        (negSlope27Fast b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14
          0 0 1 0 0 0 0 0 0 0 0 0 0 0 0 0) fun wn2 =>
      forceNatBool
        (negSlope27Fast b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14
          0 0 0 1 0 0 0 0 0 0 0 0 0 0 0 0) fun wn3 =>
      forceNatBool
        (negSlope27Fast b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14
          0 0 0 0 1 0 0 0 0 0 0 0 0 0 0 0) fun wn4 =>
      forceNatBool
        (negSlope27Fast b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14
          0 0 0 0 0 1 0 0 0 0 0 0 0 0 0 0) fun wn5 =>
      forceNatBool
        (negSlope27Fast b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14
          0 0 0 0 0 0 1 0 0 0 0 0 0 0 0 0) fun wn6 =>
      forceNatBool
        (negSlope27Fast b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14
          0 0 0 0 0 0 0 1 0 0 0 0 0 0 0 0) fun wn7 =>
      forceNatBool
        (negSlope27Fast b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14
          0 0 0 0 0 0 0 0 1 0 0 0 0 0 0 0) fun wn8 =>
      forceNatBool
        (negSlope27Fast b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14
          0 0 0 0 0 0 0 0 0 1 0 0 0 0 0 0) fun wn9 =>
      forceNatBool
        (negSlope27Fast b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14
          0 0 0 0 0 0 0 0 0 0 1 0 0 0 0 0) fun wn10 =>
      forceNatBool
        (negSlope27Fast b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14
          0 0 0 0 0 0 0 0 0 0 0 1 0 0 0 0) fun wn11 =>
      forceNatBool
        (negSlope27Fast b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14
          0 0 0 0 0 0 0 0 0 0 0 0 1 0 0 0) fun wn12 =>
      forceNatBool
        (negSlope27Fast b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14
          0 0 0 0 0 0 0 0 0 0 0 0 0 1 0 0) fun wn13 =>
      forceNatBool
        (negSlope27Fast b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14
          0 0 0 0 0 0 0 0 0 0 0 0 0 0 1 0) fun wn14 =>
      forceNatBool
        (negSlope27Fast b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14
          0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1) fun wn15 =>
      forceNatBool (sq9Words.getD 0 0) fun w0 =>
      forceNatBool (sq9Words.getD 1 0) fun w1 =>
      forceNatBool (sq9Words.getD 2 0) fun w2 =>
      forceNatBool (sq9Words.getD 3 0) fun w3 =>
      forceNatBool (sq9Words.getD 4 0) fun w4 =>
      forceNatBool (sq9Words.getD 5 0) fun w5 =>
      forceNatBool (sq9Words.getD 6 0) fun w6 =>
      forceNatBool (sq9Words.getD 7 0) fun w7 =>
      forceNatBool (sq9Words.getD 8 0) fun w8 =>
      forceNatBool (uRotSrc L.s4 0) fun s0 =>
      forceNatBool (uRotSrc L.s4 1) fun s1 =>
      forceNatBool (uRotSrc L.s4 2) fun s2 =>
      forceNatBool (uRotSrc L.s4 3) fun s3 =>
      forceNatBool (uRotSrc L.s4 4) fun s4 =>
      forceNatBool (uRotSrc L.s4 5) fun s5 =>
      forceNatBool (uRotSrc L.s4 6) fun s6 =>
      forceNatBool (uRotSrc L.s4 7) fun s7 =>
      forceNatBool (uRotSrc L.s4 8) fun s8 =>
      forceNatBool (uRotSrc L.s4 9) fun s9 =>
      forceNatBool (uRotSrc L.s4 10) fun s10 =>
      forceNatBool (uRotSrc L.s4 11) fun s11 =>
      forceNatBool (uRotSrc L.s4 12) fun s12 =>
      forceNatBool (uRotSrc L.s4 13) fun s13 =>
      forceNatBool (uRotSrc L.s4 14) fun s14 =>
      forceNatBool (uRotSrc L.s4 15) fun s15 =>
      walkLeafPos25Aux4 L lc0 lc1 lc2 lc3 lc4 lc5 lc6 lc7 blk dMax wMax gBlk1 dMin33 blkEps
        wp0 wp1 wp2 wp3 wp4 wp5 wp6 wp7 wp8 wp9 wp10 wp11 wp12 wp13 wp14 wp15
        wn0 wn1 wn2 wn3 wn4 wn5 wn6 wn7 wn8 wn9 wn10 wn11 wn12 wn13 wn14 wn15
        w0 w1 w2 w3 w4 w5 w6 w7 w8
        s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15
        L.nsteps L.us g gn fun g' gn' =>
          walkLeavesPos25Fast4 ls g' gn'

theorem walkLeavesPos25Fast4_eq : ∀ (ls : List Leaf25) (g gn : GS),
    walkLeavesPos25Fast4 ls g gn = walkLeavesPos25 ls g gn
  | [], _, _ => rfl
  | L :: ls, g, gn => by
      unfold walkLeavesPos25Fast4 walkLeavesPos25
      simp only [forceNatBool_eq, forceBoolBool_eq]
      rw [walkLeafPos25Aux4_eq]
      congr 1; funext g' gn'
      exact walkLeavesPos25Fast4_eq ls g' gn'

def gCk_0 : GS := g0
theorem inv_gCk_0 : Inv gCk_0 (gstep gCk_0) := inv_g0
def gCk_1 : GS :=
  ⟨3072, 27019123931003641, 27019123931010026, 1152604859753292026, 1152604859753301375⟩
theorem gCk_1_eq : stepN 3072 gCk_0 = gCk_1 := by decide +kernel
theorem inv_gCk_1 : Inv gCk_1 (gstep gCk_1) := gCk_1_eq ▸ stepN_inv 3072 gCk_0 inv_gCk_0
def gCk_2 : GS :=
  ⟨6146, 54040979349292321, 54040979349305379, 1151654274657052952, 1151654274657071844⟩
theorem gCk_2_eq : stepN 3074 gCk_1 = gCk_2 := by decide +kernel
theorem inv_gCk_2 : Inv gCk_2 (gstep gCk_2) := gCk_2_eq ▸ stepN_inv 3074 gCk_1 inv_gCk_1
def gCk_3 : GS :=
  ⟨9223, 81059434866031411, 81059434866051552, 1150068417010084153, 1150068417010112843⟩
theorem gCk_3_eq : stepN 3077 gCk_2 = gCk_3 := by decide +kernel
theorem inv_gCk_3 : Inv gCk_3 (gstep gCk_3) := gCk_3_eq ▸ stepN_inv 3077 gCk_2 inv_gCk_2
def gCk_4 : GS :=
  ⟨12306, 108085764327325525, 108085764327353142, 1147843832293681981, 1147843832293720690⟩
theorem gCk_4_eq : stepN 3083 gCk_3 = gCk_4 := by decide +kernel
theorem inv_gCk_4 : Inv gCk_4 (gstep gCk_4) := gCk_4_eq ▸ stepN_inv 3083 gCk_3 inv_gCk_3
def gCk_5 : GS :=
  ⟨15395, 135104710378149320, 135104710378184778, 1144978040408850544, 1144978040408899557⟩
theorem gCk_5_eq : stepN 3089 gCk_4 = gCk_5 := by decide +kernel
theorem inv_gCk_5 : Inv gCk_5 (gstep gCk_5) := gCk_5_eq ▸ stepN_inv 3089 gCk_4 inv_gCk_4
def gCk_6 : GS :=
  ⟨18493, 162126999580970800, 162126999581014557, 1141465212694505501, 1141465212694565100⟩
theorem gCk_6_eq : stepN 3098 gCk_5 = gCk_6 := by decide +kernel
theorem inv_gCk_6 : Inv gCk_6 (gstep gCk_6) := gCk_6_eq ▸ stepN_inv 3098 gCk_5 inv_gCk_5
def gCk_7 : GS :=
  ⟨21663, 189683437175628039, 189683437175680679, 1137210705826349990, 1137210705826420669⟩
theorem gCk_7_eq : stepN 3170 gCk_6 = gCk_7 := by decide +kernel
theorem inv_gCk_7 : Inv gCk_7 (gstep gCk_7) := gCk_7_eq ▸ stepN_inv 3170 gCk_6 inv_gCk_6
def gCk_8 : GS :=
  ⟨24722, 216169957073100046, 216169957073161600, 1132474523088190423, 1132474523088271999⟩
theorem gCk_8_eq : stepN 3059 gCk_7 = gCk_8 := by decide +kernel
theorem inv_gCk_8 : Inv gCk_8 (gstep gCk_8) := gCk_8_eq ▸ stepN_inv 3059 gCk_7 inv_gCk_7
def gCk_9 : GS :=
  ⟨27857, 243192242056040749, 243192242056111844, 1126980713760688059, 1126980713760781116⟩
theorem gCk_9_eq : stepN 3135 gCk_8 = gCk_9 := by decide +kernel
theorem inv_gCk_9 : Inv gCk_9 (gstep gCk_9) := gCk_9_eq ▸ stepN_inv 3135 gCk_8 inv_gCk_8
def gCk_10 : GS :=
  ⟨31008, 270212228289609305, 270212228289690392, 1120809237768649295, 1120809237768754159⟩
theorem gCk_10_eq : stepN 3151 gCk_9 = gCk_10 := by decide +kernel
theorem inv_gCk_10 : Inv gCk_10 (gstep gCk_10) := gCk_10_eq ▸ stepN_inv 3151 gCk_9 inv_gCk_9
def gCk_11 : GS :=
  ⟨34178, 297237536873615735, 297237536873707347, 1113946965729546873, 1113946965729663926⟩
theorem gCk_11_eq : stepN 3170 gCk_10 = gCk_11 := by decide +kernel
theorem inv_gCk_11 : Inv gCk_11 (gstep gCk_11) := gCk_11_eq ▸ stepN_inv 3170 gCk_10 inv_gCk_10
def gCk_12 : GS :=
  ⟨37368, 324257817398338219, 324257817398440818, 1106383687352992944, 1106383687353122555⟩
theorem gCk_12_eq : stepN 3190 gCk_11 = gCk_12 := by decide +kernel
theorem inv_gCk_12 : Inv gCk_12 (gstep gCk_12) := gCk_12_eq ▸ stepN_inv 3190 gCk_11 inv_gCk_11
def gCk_13 : GS :=
  ⟨40568, 351169823076489913, 351169823076603929, 1098138311482276899, 1098138311482419408⟩
theorem gCk_13_eq : stepN 3200 gCk_12 = gCk_13 := by decide +kernel
theorem inv_gCk_13 : Inv gCk_13 (gstep gCk_13) := gCk_13_eq ▸ stepN_inv 3200 gCk_12 inv_gCk_12
def gCk_14 : GS :=
  ⟨40581, 351278737044632250, 351278737044746314, 1098103476310428340, 1098103476310570902⟩
theorem gCk_14_eq : stepN 13 gCk_13 = gCk_14 := by decide +kernel
theorem inv_gCk_14 : Inv gCk_14 (gstep gCk_14) := gCk_14_eq ▸ stepN_inv 13 gCk_13 inv_gCk_13
def gCk_15 : GS :=
  ⟨43781, 377980556752830791, 377980556752956734, 1089200943123682199, 1089200943123837980⟩
theorem gCk_15_eq : stepN 3200 gCk_14 = gCk_15 := by decide +kernel
theorem inv_gCk_15 : Inv gCk_15 (gstep gCk_15) := gCk_15_eq ▸ stepN_inv 3200 gCk_14 inv_gCk_14
def gCk_16 : GS :=
  ⟨43819, 378296318724740569, 378296318724866657, 1089091314364414522, 1089091314364570458⟩
theorem gCk_16_eq : stepN 38 gCk_15 = gCk_16 := by decide +kernel
theorem inv_gCk_16 : Inv gCk_16 (gstep gCk_16) := gCk_16_eq ▸ stepN_inv 38 gCk_15 inv_gCk_15
def gCk_17 : GS :=
  ⟨47019, 404770085337785928, 404770085337924368, 1079531923474391080, 1079531923474560525⟩
theorem gCk_17_eq : stepN 3200 gCk_16 = gCk_17 := by decide +kernel
theorem inv_gCk_17 : Inv gCk_17 (gstep gCk_17) := gCk_17_eq ▸ stepN_inv 3200 gCk_16 inv_gCk_16
def gCk_18 : GS :=
  ⟨47086, 405321856153588610, 405321856153727310, 1079324876350437056, 1079324876350606783⟩
theorem gCk_18_eq : stepN 67 gCk_17 = gCk_18 := by decide +kernel
theorem inv_gCk_18 : Inv gCk_18 (gstep gCk_18) := gCk_18_eq ▸ stepN_inv 67 gCk_17 inv_gCk_17
def gCk_19 : GS :=
  ⟨50286, 431549154186840868, 431549154186992379, 1069108658324904122, 1069108658325087730⟩
theorem gCk_19_eq : stepN 3200 gCk_18 = gCk_19 := by decide +kernel
theorem inv_gCk_19 : Inv gCk_19 (gstep gCk_19) := gCk_19_eq ▸ stepN_inv 3200 gCk_18 inv_gCk_18
def gCk_20 : GS :=
  ⟨50383, 432340231159954838, 432340231160106745, 1068788997092134396, 1068788997092318424⟩
theorem gCk_20_eq : stepN 97 gCk_19 = gCk_20 := by decide +kernel
theorem inv_gCk_20 : Inv gCk_20 (gstep gCk_20) := gCk_20_eq ▸ stepN_inv 97 gCk_19 inv_gCk_19
def gCk_21 : GS :=
  ⟨53583, 458302279427332196, 458302279427497399, 1057916356077521902, 1057916356077720147⟩
theorem gCk_21_eq : stepN 3200 gCk_20 = gCk_21 := by decide +kernel
theorem inv_gCk_21 : Inv gCk_21 (gstep gCk_21) := gCk_21_eq ▸ stepN_inv 3200 gCk_20 inv_gCk_20
def gCk_22 : GS :=
  ⟨53714, 459359385577132863, 459359385577298623, 1057457777250150361, 1057457777250349195⟩
theorem gCk_22_eq : stepN 131 gCk_21 = gCk_22 := by decide +kernel
theorem inv_gCk_22 : Inv gCk_22 (gstep gCk_22) := gCk_22_eq ▸ stepN_inv 131 gCk_21 inv_gCk_21
def gCk_23 : GS :=
  ⟨56914, 485036768280542824, 485036768280722409, 1045928931237955904, 1045928931238169328⟩
theorem gCk_23_eq : stepN 3200 gCk_22 = gCk_23 := by decide +kernel
theorem inv_gCk_23 : Inv gCk_23 (gstep gCk_23) := gCk_23_eq ▸ stepN_inv 3200 gCk_22 inv_gCk_22
def gCk_24 : GS :=
  ⟨57083, 486384951682740722, 486384951682921056, 1045302671268557678, 1045302671268771895⟩
theorem gCk_24_eq : stepN 169 gCk_23 = gCk_24 := by decide +kernel
theorem inv_gCk_24 : Inv gCk_24 (gstep gCk_24) := gCk_24_eq ▸ stepN_inv 169 gCk_23 inv_gCk_23
def gCk_25 : GS :=
  ⟨60283, 511757554501868266, 511757554502062882, 1033117709263976858, 1033117709264206007⟩
theorem gCk_25_eq : stepN 3200 gCk_24 = gCk_25 := by decide +kernel
theorem inv_gCk_25 : Inv gCk_25 (gstep gCk_25) := gCk_25_eq ▸ stepN_inv 3200 gCk_24 inv_gCk_24
def gCk_26 : GS :=
  ⟨60492, 513404254298167027, 513404254298362581, 1032300376563488955, 1032300376563719090⟩
theorem gCk_26_eq : stepN 209 gCk_25 = gCk_26 := by decide +kernel
theorem inv_gCk_26 : Inv gCk_26 (gstep gCk_26) := gCk_26_eq ▸ stepN_inv 209 gCk_25 inv_gCk_25
def gCk_27 : GS :=
  ⟨63692, 538451397835782533, 538451397835992828, 1019459703937945927, 1019459703938191413⟩
theorem gCk_27_eq : stepN 3200 gCk_26 = gCk_27 := by decide +kernel
theorem inv_gCk_27 : Inv gCk_27 (gstep gCk_27) := gCk_27_eq ▸ stepN_inv 3200 gCk_26 inv_gCk_26
def gCk_28 : GS :=
  ⟨63947, 540433731952259541, 540433731952471025, 1018410220467520511, 1018410220467767231⟩
theorem gCk_28_eq : stepN 255 gCk_27 = gCk_28 := by decide +kernel
theorem inv_gCk_28 : Inv gCk_28 (gstep gCk_28) := gCk_28_eq ▸ stepN_inv 255 gCk_27 inv_gCk_27
def gCk_29 : GS :=
  ⟨66275, 558435758857486462, 558435758857709034, 1008651326779375540, 1008651326779633649⟩
theorem gCk_29_eq : stepN 2328 gCk_28 = gCk_29 := by decide +kernel
theorem inv_gCk_29 : Inv gCk_29 (gstep gCk_29) := gCk_29_eq ▸ stepN_inv 2328 gCk_28 inv_gCk_28
def gCk_30 : GS :=
  ⟨69221, 580963446140506797, 580963446140743771, 995846107605514103, 995846107605786899⟩
theorem gCk_30_eq : stepN 2946 gCk_29 = gCk_30 := by decide +kernel
theorem inv_gCk_30 : Inv gCk_30 (gstep gCk_30) := gCk_30_eq ▸ stepN_inv 2946 gCk_29 inv_gCk_29
def gCk_31 : GS :=
  ⟨71006, 594471053829134889, 594471053829380783, 987842174612811945, 987842174613093809⟩
theorem gCk_31_eq : stepN 1785 gCk_30 = gCk_31 := by decide +kernel
theorem inv_gCk_31 : Inv gCk_31 (gstep gCk_31) := gCk_31_eq ▸ stepN_inv 1785 gCk_30 inv_gCk_30
def gCk_32 : GS :=
  ⟨72806, 607980519653288737, 607980519653543804, 979585465136448826, 979585465136739940⟩
theorem gCk_32_eq : stepN 1800 gCk_31 = gCk_32 := by decide +kernel
theorem inv_gCk_32 : Inv gCk_32 (gstep gCk_32) := gCk_32_eq ▸ stepN_inv 1800 gCk_31 inv_gCk_31
def gCk_33 : GS :=
  ⟨74603, 621353098632627690, 621353098632892060, 971158237675041345, 971158237675341779⟩
theorem gCk_33_eq : stepN 1797 gCk_32 = gCk_33 := by decide +kernel
theorem inv_gCk_33 : Inv gCk_33 (gstep gCk_33) := gCk_33_eq ▸ stepN_inv 1797 gCk_32 inv_gCk_32
def gCk_34 : GS :=
  ⟨75841, 630498020986173381, 630498020986444248, 965246207615947007, 965246207616253958⟩
theorem gCk_34_eq : stepN 1238 gCk_33 = gCk_34 := by decide +kernel
theorem inv_gCk_34 : Inv gCk_34 (gstep gCk_34) := gCk_34_eq ▸ stepN_inv 1238 gCk_33 inv_gCk_33
def gCk_35 : GS :=
  ⟨77684, 644007548536073526, 644007548536354226, 956285665067185506, 956285665067502249⟩
theorem gCk_35_eq : stepN 1843 gCk_34 = gCk_35 := by decide +kernel
theorem inv_gCk_35 : Inv gCk_35 (gstep gCk_35) := gCk_35_eq ▸ stepN_inv 1843 gCk_34 inv_gCk_34
def gCk_36 : GS :=
  ⟨79545, 657519813956191645, 657519813956482412, 947045769770094347, 947045769770421135⟩
theorem gCk_36_eq : stepN 1861 gCk_35 = gCk_36 := by decide +kernel
theorem inv_gCk_36 : Inv gCk_36 (gstep gCk_36) := gCk_36_eq ▸ stepN_inv 1861 gCk_35 inv_gCk_35
def gCk_37 : GS :=
  ⟨81425, 671035439196145477, 671035439196446568, 937517698567463947, 937517698567801016⟩
theorem gCk_37_eq : stepN 1880 gCk_36 = gCk_37 := by decide +kernel
theorem inv_gCk_37 : Inv gCk_37 (gstep gCk_37) := gCk_37_eq ▸ stepN_inv 1880 gCk_36 inv_gCk_36
def gCk_38 : GS :=
  ⟨83323, 684540422288565706, 684540422288877411, 927702757372948855, 927702757373296421⟩
theorem gCk_38_eq : stepN 1898 gCk_37 = gCk_38 := by decide +kernel
theorem inv_gCk_38 : Inv gCk_38 (gstep gCk_38) := gCk_38_eq ▸ stepN_inv 1898 gCk_37 inv_gCk_37
def gCk_39 : GS :=
  ⟨85243, 698055890252653079, 698055890252975683, 917576138458241494, 917576138458599898⟩
theorem gCk_39_eq : stepN 1920 gCk_38 = gCk_39 := by decide +kernel
theorem inv_gCk_39 : Inv gCk_39 (gstep gCk_39) := gCk_39_eq ▸ stepN_inv 1920 gCk_38 inv_gCk_38
def gCk_40 : GS :=
  ⟨85464, 699602018893556581, 699602018893880462, 916397845340341028, 916397845340700681⟩
theorem gCk_40_eq : stepN 221 gCk_39 = gCk_40 := by decide +kernel
theorem inv_gCk_40 : Inv gCk_40 (gstep gCk_40) := gCk_40_eq ▸ stepN_inv 221 gCk_39 inv_gCk_39
def gCk_41 : GS :=
  ⟨87184, 711566922773150269, 711566922773484147, 907138638907798338, 907138638908167790⟩
theorem gCk_41_eq : stepN 1720 gCk_40 = gCk_41 := by decide +kernel
theorem inv_gCk_41 : Inv gCk_41 (gstep gCk_41) := gCk_41_eq ▸ stepN_inv 1720 gCk_40 inv_gCk_40
def gCk_42 : GS :=
  ⟨89148, 725079217709678013, 725079217710023456, 896374990631624915, 896374990632005688⟩
theorem gCk_42_eq : stepN 1964 gCk_41 = gCk_42 := by decide +kernel
theorem inv_gCk_42 : Inv gCk_42 (gstep gCk_42) := gCk_42_eq ▸ stepN_inv 1964 gCk_41 inv_gCk_41
def gCk_43 : GS :=
  ⟨91135, 738584074793898276, 738584074794255626, 885280498059878210, 885280498060270622⟩
theorem gCk_43_eq : stepN 1987 gCk_42 = gCk_43 := by decide +kernel
theorem inv_gCk_43 : Inv gCk_43 (gstep gCk_43) := gCk_43_eq ▸ stepN_inv 1987 gCk_42 inv_gCk_42
def gCk_44 : GS :=
  ⟨93149, 752099217307838017, 752099217308207637, 873827650689323360, 873827650689727771⟩
theorem gCk_44_eq : stepN 2014 gCk_43 = gCk_44 := by decide +kernel
theorem inv_gCk_44 : Inv gCk_44 (gstep gCk_44) := gCk_44_eq ▸ stepN_inv 2014 gCk_43 inv_gCk_43
def gCk_45 : GS :=
  ⟨94506, 761105563529842456, 761105563530220493, 865994409305390387, 865994409305802958⟩
theorem gCk_45_eq : stepN 1357 gCk_44 = gCk_45 := by decide +kernel
theorem inv_gCk_45 : Inv gCk_45 (gstep gCk_45) := gCk_45_eq ▸ stepN_inv 1357 gCk_44 inv_gCk_44
def gCk_46 : GS :=
  ⟨96565, 774614936638872000, 774614936639262970, 853931903444417837, 853931903444842957⟩
theorem gCk_46_eq : stepN 2059 gCk_45 = gCk_46 := by decide +kernel
theorem inv_gCk_46 : Inv gCk_46 (gstep gCk_46) := gCk_46_eq ▸ stepN_inv 2059 gCk_45 inv_gCk_45
def gCk_47 : GS :=
  ⟨98654, 788125781482594764, 788125781482999090, 841478311275268798, 841478311275706821⟩
theorem gCk_47_eq : stepN 2089 gCk_46 = gCk_47 := by decide +kernel
theorem inv_gCk_47 : Inv gCk_47 (gstep gCk_47) := gCk_47_eq ▸ stepN_inv 2089 gCk_46 inv_gCk_46
def gCk_48 : GS :=
  ⟨100775, 801638758413473991, 801638758413892123, 828615288776106832, 828615288776558109⟩
theorem gCk_48_eq : stepN 2121 gCk_47 = gCk_48 := by decide +kernel
theorem inv_gCk_48 : Inv gCk_48 (gstep gCk_48) := gCk_48_eq ▸ stepN_inv 2121 gCk_47 inv_gCk_47
def gCk_49 : GS :=
  ⟨102929, 815147128017099365, 815147128017531746, 815330089883636770, 815330089884101762⟩
theorem gCk_49_eq : stepN 2154 gCk_48 = gCk_49 := by decide +kernel
theorem inv_gCk_49 : Inv gCk_49 (gstep gCk_49) := gCk_49_eq ▸ stepN_inv 2154 gCk_48 inv_gCk_48
def gCk_50 : GS :=
  ⟨105120, 828661670381413056, 828661670381860178, 801590813211359050, 801590813211838219⟩
theorem gCk_50_eq : stepN 2191 gCk_49 = gCk_50 := by decide +kernel
theorem inv_gCk_50 : Inv gCk_50 (gstep gCk_50) := gCk_50_eq ▸ stepN_inv 2191 gCk_49 inv_gCk_49
def gCk_51 : GS :=
  ⟨107349, 842172980766205436, 842172980766667850, 787383430262221402, 787383430262715241⟩
theorem gCk_51_eq : stepN 2229 gCk_50 = gCk_51 := by decide +kernel
theorem inv_gCk_51 : Inv gCk_51 (gstep gCk_51) := gCk_51_eq ▸ stepN_inv 2229 gCk_50 inv_gCk_50
def gCk_52 : GS :=
  ⟨109619, 855682479861800634, 855682479862278883, 772680716364574992, 772680716365083973⟩
theorem gCk_52_eq : stepN 2270 gCk_51 = gCk_52 := by decide +kernel
theorem inv_gCk_52 : Inv gCk_52 (gstep gCk_52) := gCk_52_eq ▸ stepN_inv 2270 gCk_51 inv_gCk_51
def gCk_53 : GS :=
  ⟨111933, 869189654881529455, 869189654882024163, 757454513242225292, 757454513242749991⟩
theorem gCk_53_eq : stepN 2314 gCk_52 = gCk_53 := by decide +kernel
theorem inv_gCk_53 : Inv gCk_53 (gstep gCk_53) := gCk_53_eq ▸ stepN_inv 2314 gCk_52 inv_gCk_52
def gCk_54 : GS :=
  ⟨114296, 882703254156694089, 882703254157205897, 741662295715001191, 741662295715542198⟩
theorem gCk_54_eq : stepN 2363 gCk_53 = gCk_54 := by decide +kernel
theorem inv_gCk_54 : Inv gCk_54 (gstep gCk_54) := gCk_54_eq ▸ stepN_inv 2363 gCk_53 inv_gCk_53
def gCk_55 : GS :=
  ⟨116710, 896212240429016715, 896212240429546345, 725280370539034476, 725280370539592421⟩
theorem gCk_55_eq : stepN 2414 gCk_54 = gCk_55 := by decide +kernel
theorem inv_gCk_55 : Inv gCk_55 (gstep gCk_55) := gCk_55_eq ▸ stepN_inv 2414 gCk_54 inv_gCk_54
def gCk_56 : GS :=
  ⟨118558, 906348642017226565, 906348642017770049, 712572897953287185, 712572897953858293⟩
theorem gCk_56_eq : stepN 1848 gCk_55 = gCk_56 := by decide +kernel
theorem inv_gCk_56 : Inv gCk_56 (gstep gCk_56) := gCk_56_eq ▸ stepN_inv 1848 gCk_55 inv_gCk_55
def gCk_57 : GS :=
  ⟨120862, 918733669500819764, 918733669501380787, 696531722400028076, 696531722400615831⟩
theorem gCk_57_eq : stepN 2304 gCk_56 = gCk_57 := by decide +kernel
theorem inv_gCk_57 : Inv gCk_57 (gstep gCk_57) := gCk_57_eq ▸ stepN_inv 2304 gCk_56 inv_gCk_56
def gCk_58 : GS :=
  ⟨122625, 928019065253576952, 928019065254151612, 684111548148289305, 684111548148889988⟩
theorem gCk_58_eq : stepN 1763 gCk_57 = gCk_58 := by decide +kernel
theorem inv_gCk_58 : Inv gCk_58 (gstep gCk_58) := gCk_58_eq ▸ stepN_inv 1763 gCk_57 inv_gCk_57
def gCk_59 : GS :=
  ⟨124752, 938997961039724585, 938997961040315937, 668962498909459251, 668962498910075699⟩
theorem gCk_59_eq : stepN 2127 gCk_58 = gCk_59 := by decide +kernel
theorem inv_gCk_59 : Inv gCk_59 (gstep gCk_59) := gCk_59_eq ▸ stepN_inv 2127 gCk_58 inv_gCk_58
def gCk_60 : GS :=
  ⟨126085, 945752621763851590, 945752621764453547, 659378475695662018, 659378475696288521⟩
theorem gCk_60_eq : stepN 1333 gCk_59 = gCk_60 := by decide +kernel
theorem inv_gCk_60 : Inv gCk_60 (gstep gCk_60) := gCk_60_eq ▸ stepN_inv 1333 gCk_59 inv_gCk_59
def gCk_61 : GS :=
  ⟨127438, 952508594777250091, 952508594777862922, 649580920793850833, 649580920794487599⟩
theorem gCk_61_eq : stepN 1353 gCk_60 = gCk_61 := by decide +kernel
theorem inv_gCk_61 : Inv gCk_61 (gstep gCk_61) := gCk_61_eq ▸ stepN_inv 1353 gCk_60 inv_gCk_60
def gCk_62 : GS :=
  ⟨128812, 959265554646163827, 959265554646787798, 639560467394046505, 639560467394693800⟩
theorem gCk_62_eq : stepN 1374 gCk_61 = gCk_62 := by decide +kernel
theorem inv_gCk_62 : Inv gCk_62 (gstep gCk_62) := gCk_62_eq ▸ stepN_inv 1374 gCk_61 inv_gCk_61
def gCk_63 : GS :=
  ⟨130207, 966017942429627274, 966017942430262676, 629314969381721789, 629314969382379892⟩
theorem gCk_63_eq : stepN 1395 gCk_62 = gCk_63 := by decide +kernel
theorem inv_gCk_63 : Inv gCk_63 (gstep gCk_63) := gCk_63_eq ▸ stepN_inv 1395 gCk_62 inv_gCk_62
def gCk_64 : GS :=
  ⟨131626, 972774232598521827, 972774232599168959, 618820077386173244, 618820077386842442⟩
theorem gCk_64_eq : stepN 1419 gCk_63 = gCk_64 := by decide +kernel
theorem inv_gCk_64 : Inv gCk_64 (gstep gCk_64) := gCk_64_eq ▸ stepN_inv 1419 gCk_63 inv_gCk_63
def gCk_65 : GS :=
  ⟨133070, 979532507363599643, 979532507364258841, 608065837555306344, 608065837555986944⟩
theorem gCk_65_eq : stepN 1444 gCk_64 = gCk_65 := by decide +kernel
theorem inv_gCk_65 : Inv gCk_65 (gstep gCk_65) := gCk_65_eq ▸ stepN_inv 1444 gCk_64 inv_gCk_64
def gCk_66 : GS :=
  ⟨134539, 986285792730157239, 986285792730828889, 597049688755036261, 597049688755728579⟩
theorem gCk_66_eq : stepN 1469 gCk_65 = gCk_66 := by decide +kernel
theorem inv_gCk_66 : Inv gCk_66 (gstep gCk_66) := gCk_66_eq ▸ stepN_inv 1469 gCk_65 inv_gCk_65
def gCk_67 : GS :=
  ⟨136036, 993040343764144479, 993040343764828960, 585746422473593605, 585746422474297978⟩
theorem gCk_67_eq : stepN 1497 gCk_66 = gCk_67 := by decide +kernel
theorem inv_gCk_67 : Inv gCk_67 (gstep gCk_67) := gCk_67_eq ▸ stepN_inv 1497 gCk_66 inv_gCk_66
def gCk_68 : GS :=
  ⟨137563, 999796796089301537, 999796796089999239, 574137929694054126, 574137929694770925⟩
theorem gCk_68_eq : stepN 1527 gCk_67 = gCk_68 := by decide +kernel
theorem inv_gCk_68 : Inv gCk_68 (gstep gCk_68) := gCk_68_eq ▸ stepN_inv 1527 gCk_67 inv_gCk_67
def gCk_69 : GS :=
  ⟨139121, 1006550550987965442, 1006550550988676756, 562213468434911410, 562213468435641058⟩
theorem gCk_69_eq : stepN 1558 gCk_68 = gCk_69 := by decide +kernel
theorem inv_gCk_69 : Inv gCk_69 (gstep gCk_69) := gCk_69_eq ▸ stepN_inv 1558 gCk_68 inv_gCk_68
def gCk_70 : GS :=
  ⟨140714, 1013308976528784503, 1013308976529509918, 549939009227350405, 549939009228093324⟩
theorem gCk_70_eq : stepN 1593 gCk_69 = gCk_70 := by decide +kernel
theorem inv_gCk_70 : Inv gCk_70 (gstep gCk_70) := gCk_70_eq ▸ stepN_inv 1593 gCk_69 inv_gCk_69
def gCk_71 : GS :=
  ⟨142342, 1020061241291645387, 1020061241292385391, 537310952613384138, 537310952614140759⟩
theorem gCk_71_eq : stepN 1628 gCk_70 = gCk_71 := by decide +kernel
theorem inv_gCk_71 : Inv gCk_71 (gstep gCk_71) := gCk_71_eq ▸ stepN_inv 1628 gCk_70 inv_gCk_70
def gCk_72 : GS :=
  ⟨144011, 1026820187889890240, 1026820187890645380, 524278835664293303, 524278835665064128⟩
theorem gCk_72_eq : stepN 1669 gCk_71 = gCk_72 := by decide +kernel
theorem inv_gCk_72 : Inv gCk_72 (gstep gCk_72) := gCk_72_eq ▸ stepN_inv 1669 gCk_71 inv_gCk_71
def gCk_73 : GS :=
  ⟨145721, 1033572490564332942, 1033572490565103770, 510838430946967795, 510838430947753346⟩
theorem gCk_73_eq : stepN 1710 gCk_72 = gCk_73 := by decide +kernel
theorem inv_gCk_73 : Inv gCk_73 (gstep gCk_73) := gCk_73_eq ▸ stepN_inv 1710 gCk_72 inv_gCk_72
def gCk_74 : GS :=
  ⟨147479, 1040330927511628785, 1040330927512415920, 496930132962867758, 496930132963668609⟩
theorem gCk_74_eq : stepN 1758 gCk_73 = gCk_74 := by decide +kernel
theorem inv_gCk_74 : Inv gCk_74 (gstep gCk_74) := gCk_74_eq ▸ stepN_inv 1758 gCk_73 inv_gCk_73
def gCk_75 : GS :=
  ⟨149287, 1047086365380782568, 1047086365381586731, 482533044689524070, 482533044690340921⟩
theorem gCk_75_eq : stepN 1808 gCk_74 = gCk_75 := by decide +kernel
theorem inv_gCk_75 : Inv gCk_75 (gstep gCk_75) := gCk_75_eq ▸ stepN_inv 1808 gCk_74 inv_gCk_74
def gCk_76 : GS :=
  ⟨151150, 1053838880592774318, 1053838880593596246, 467601977684684881, 467601977685518377⟩
theorem gCk_76_eq : stepN 1863 gCk_75 = gCk_76 := by decide +kernel
theorem inv_gCk_76 : Inv gCk_76 (gstep gCk_76) := gCk_76_eq ▸ stepN_inv 1863 gCk_75 inv_gCk_75
def gCk_77 : GS :=
  ⟨152761, 1059506411128671043, 1059506411129508500, 454614298676236942, 454614298677085006⟩
theorem gCk_77_eq : stepN 1611 gCk_76 = gCk_77 := by decide +kernel
theorem inv_gCk_77 : Inv gCk_77 (gstep gCk_77) := gCk_77_eq ▸ stepN_inv 1611 gCk_76 inv_gCk_76
def gCk_78 : GS :=
  ⟨154397, 1065098087747064704, 1065098087747918113, 441354799748651522, 441354799749514530⟩
theorem gCk_78_eq : stepN 1636 gCk_77 = gCk_78 := by decide +kernel
theorem inv_gCk_78 : Inv gCk_78 (gstep gCk_78) := gCk_78_eq ▸ stepN_inv 1636 gCk_77 inv_gCk_77
def gCk_79 : GS :=
  ⟨156442, 1071854241715420364, 1071854241716294002, 424683976976134977, 424683976977016945⟩
theorem gCk_79_eq : stepN 2045 gCk_78 = gCk_79 := by decide +kernel
theorem inv_gCk_79 : Inv gCk_79 (gstep gCk_79) := gCk_79_eq ▸ stepN_inv 2045 gCk_78 inv_gCk_78
def gCk_80 : GS :=
  ⟨158438, 1078196915424238516, 1078196915425132164, 408312879239979638, 408312879240880350⟩
theorem gCk_80_eq : stepN 1996 gCk_79 = gCk_80 := by decide +kernel
theorem inv_gCk_80 : Inv gCk_80 (gstep gCk_80) := gCk_80_eq ▸ stepN_inv 1996 gCk_79 inv_gCk_79
def gCk_81 : GS :=
  ⟨159670, 1081987132280319223, 1081987132281225372, 398160572336567875, 398160572337480274⟩
theorem gCk_81_eq : stepN 1232 gCk_80 = gCk_81 := by decide +kernel
theorem inv_gCk_81 : Inv gCk_81 (gstep gCk_81) := gCk_81_eq ▸ stepN_inv 1232 gCk_80 inv_gCk_80
def gCk_82 : GS :=
  ⟨160795, 1085364675676645218, 1085364675677562868, 388859250342449457, 388859250343372635⟩
theorem gCk_82_eq : stepN 1125 gCk_81 = gCk_82 := by decide +kernel
theorem inv_gCk_82 : Inv gCk_82 (gstep gCk_82) := gCk_82_eq ▸ stepN_inv 1125 gCk_81 inv_gCk_81
def gCk_83 : GS :=
  ⟨161948, 1088743313117111141, 1088743313118040691, 379296709617056490, 379296709617990785⟩
theorem gCk_83_eq : stepN 1153 gCk_82 = gCk_83 := by decide +kernel
theorem inv_gCk_83 : Inv gCk_83 (gstep gCk_83) := gCk_83_eq ▸ stepN_inv 1153 gCk_82 inv_gCk_82
def gCk_84 : GS :=
  ⟨163131, 1092122292308923101, 1092122292309864915, 369454861147395239, 369454861148341056⟩
theorem gCk_84_eq : stepN 1183 gCk_83 = gCk_84 := by decide +kernel
theorem inv_gCk_84 : Inv gCk_84 (gstep gCk_84) := gCk_84_eq ▸ stepN_inv 1183 gCk_83 inv_gCk_83
def gCk_85 : GS :=
  ⟨164346, 1095500062902510626, 1095500062903465144, 359315471367601195, 359315471368558929⟩
theorem gCk_85_eq : stepN 1215 gCk_84 = gCk_85 := by decide +kernel
theorem inv_gCk_85 : Inv gCk_85 (gstep gCk_85) := gCk_85_eq ▸ stepN_inv 1215 gCk_84 inv_gCk_84
def gCk_86 : GS :=
  ⟨165596, 1098876893127725227, 1098876893128692950, 348851787344528444, 348851787345498544⟩
theorem gCk_86_eq : stepN 1250 gCk_85 = gCk_86 := by decide +kernel
theorem inv_gCk_86 : Inv gCk_86 (gstep gCk_86) := gCk_86_eq ▸ stepN_inv 1250 gCk_85 inv_gCk_85
def gCk_87 : GS :=
  ⟨166885, 1102254409765752674, 1102254409766734138, 338028418828142405, 338028418829125369⟩
theorem gCk_87_eq : stepN 1289 gCk_86 = gCk_87 := by decide +kernel
theorem inv_gCk_87 : Inv gCk_87 (gstep gCk_87) := gCk_87_eq ▸ stepN_inv 1289 gCk_86 inv_gCk_86
def gCk_88 : GS :=
  ⟨168217, 1105632598623229715, 1105632598624225493, 326809658127071881, 326809658128068273⟩
theorem gCk_88_eq : stepN 1332 gCk_87 = gCk_88 := by decide +kernel
theorem inv_gCk_88 : Inv gCk_88 (gstep gCk_88) := gCk_88_eq ▸ stepN_inv 1332 gCk_87 inv_gCk_87
def gCk_89 : GS :=
  ⟨169596, 1109009687668587893, 1109009687669598637, 315159496827713806, 315159496828724213⟩
theorem gCk_89_eq : stepN 1379 gCk_88 = gCk_89 := by decide +kernel
theorem inv_gCk_89 : Inv gCk_89 (gstep gCk_89) := gCk_89_eq ▸ stepN_inv 1379 gCk_88 inv_gCk_88
def gCk_90 : GS :=
  ⟨171029, 1112388954704556061, 1112388954705582515, 303016186423710142, 303016186424735257⟩
theorem gCk_90_eq : stepN 1433 gCk_89 = gCk_90 := by decide +kernel
theorem inv_gCk_90 : Inv gCk_90 (gstep gCk_90) := gCk_90_eq ▸ stepN_inv 1433 gCk_89 inv_gCk_89
def gCk_91 : GS :=
  ⟨172525, 1115774922860659560, 1115774922861702568, 290300391489125166, 290300391490165794⟩
theorem gCk_91_eq : stepN 1496 gCk_90 = gCk_91 := by decide +kernel
theorem inv_gCk_91 : Inv gCk_91 (gstep gCk_91) := gCk_91_eq ▸ stepN_inv 1496 gCk_90 inv_gCk_90
def gCk_92 : GS :=
  ⟨173553, 1118017413478181827, 1118017413479236318, 281540510305350593, 281540510306401980⟩
theorem gCk_92_eq : stepN 1028 gCk_91 = gCk_92 := by decide +kernel
theorem inv_gCk_92 : Inv gCk_92 (gstep gCk_92) := gCk_92_eq ▸ stepN_inv 1028 gCk_91 inv_gCk_91
def gCk_93 : GS :=
  ⟨174349, 1119706581030087825, 1119706581031151262, 274745642697651241, 274745642698711014⟩
theorem gCk_93_eq : stepN 796 gCk_92 = gCk_93 := by decide +kernel
theorem inv_gCk_93 : Inv gCk_93 (gstep gCk_93) := gCk_93_eq ▸ stepN_inv 796 gCk_92 inv_gCk_92
def gCk_94 : GS :=
  ⟨175165, 1121395323911633924, 1121395323912706580, 267769533914052023, 267769533915120426⟩
theorem gCk_94_eq : stepN 816 gCk_93 = gCk_94 := by decide +kernel
theorem inv_gCk_94 : Inv gCk_94 (gstep gCk_94) := gCk_94_eq ▸ stepN_inv 816 gCk_93 inv_gCk_93
def gCk_95 : GS :=
  ⟨176003, 1123084359731920329, 1123084359733002506, 260594544664623438, 260594544665700790⟩
theorem gCk_95_eq : stepN 838 gCk_94 = gCk_95 := by decide +kernel
theorem inv_gCk_95 : Inv gCk_95 (gstep gCk_95) := gCk_95_eq ▸ stepN_inv 838 gCk_94 inv_gCk_94
def gCk_96 : GS :=
  ⟨176865, 1124773870235115006, 1124773870236207014, 253202955392967835, 253202955394054444⟩
theorem gCk_96_eq : stepN 862 gCk_95 = gCk_96 := by decide +kernel
theorem inv_gCk_96 : Inv gCk_96 (gstep gCk_96) := gCk_96_eq ▸ stepN_inv 862 gCk_95 inv_gCk_95
def gCk_97 : GS :=
  ⟨177752, 1126461595702991055, 1126461595704093230, 245585563886960455, 245585563888056619⟩
theorem gCk_97_eq : stepN 887 gCk_96 = gCk_97 := by decide +kernel
theorem inv_gCk_97 : Inv gCk_97 (gstep gCk_97) := gCk_97_eq ▸ stepN_inv 887 gCk_96 inv_gCk_96
def gCk_98 : GS :=
  ⟨178668, 1128150354890088285, 1128150354891201059, 237707325391468550, 237707325392574654⟩
theorem gCk_98_eq : stepN 916 gCk_97 = gCk_98 := by decide +kernel
theorem inv_gCk_98 : Inv gCk_98 (gstep gCk_98) := gCk_98_eq ▸ stepN_inv 916 gCk_97 inv_gCk_97
def gCk_99 : GS :=
  ⟨179616, 1129840090128521542, 1129840090129645320, 229541644417226180, 229541644418342642⟩
theorem gCk_99_eq : stepN 948 gCk_98 = gCk_99 := by decide +kernel
theorem inv_gCk_99 : Inv gCk_99 (gstep gCk_99) := gCk_99_eq ▸ stepN_inv 948 gCk_98 inv_gCk_98
def gCk_100 : GS :=
  ⟨180598, 1131528105655090845, 1131528105656226119, 221070445550697057, 221070445551824310⟩
theorem gCk_100_eq : stepN 982 gCk_99 = gCk_100 := by decide +kernel
theorem inv_gCk_100 : Inv gCk_100 (gstep gCk_100) := gCk_100_eq ▸ stepN_inv 982 gCk_99 inv_gCk_99
def gCk_101 : GS :=
  ⟨181620, 1133217431211190171, 1133217431212337488, 212241017200930280, 212241017202068849⟩
theorem gCk_101_eq : stepN 1022 gCk_100 = gCk_101 := by decide +kernel
theorem inv_gCk_101 : Inv gCk_101 (gstep gCk_101) := gCk_101_eq ▸ stepN_inv 1022 gCk_100 inv_gCk_100
def gCk_102 : GS :=
  ⟨182686, 1134906076573831839, 1134906076574991815, 203017716318447506, 203017716319597963⟩
theorem gCk_102_eq : stepN 1066 gCk_101 = gCk_102 := by decide +kernel
theorem inv_gCk_102 : Inv gCk_102 (gstep gCk_102) := gCk_102_eq ▸ stepN_inv 1066 gCk_101 inv_gCk_101
def gCk_103 : GS :=
  ⟨183803, 1136594968390061643, 1136594968391234981, 193338753522805737, 193338753523968763⟩
theorem gCk_103_eq : stepN 1117 gCk_102 = gCk_103 := by decide +kernel
theorem inv_gCk_103 : Inv gCk_103 (gstep gCk_103) := gCk_103_eq ▸ stepN_inv 1117 gCk_102 inv_gCk_102
def gCk_104 : GS :=
  ⟨184979, 1138283865362402589, 1138283865363590114, 183133387559386576, 183133387560562938⟩
theorem gCk_104_eq : stepN 1176 gCk_103 = gCk_104 := by decide +kernel
theorem inv_gCk_104 : Inv gCk_104 (gstep gCk_104) := gCk_104_eq ▸ stepN_inv 1176 gCk_103 inv_gCk_103
def gCk_105 : GS :=
  ⟨186012, 1139691803993014288, 1139691803994214361, 174156790549464338, 174156790550652486⟩
theorem gCk_105_eq : stepN 1033 gCk_104 = gCk_105 := by decide +kernel
theorem inv_gCk_105 : Inv gCk_105 (gstep gCk_105) := gCk_105_eq ▸ stepN_inv 1033 gCk_104 inv_gCk_104
def gCk_106 : GS :=
  ⟨186658, 1140536305644973879, 1140536305646181835, 168537625736959432, 168537625738154972⟩
theorem gCk_106_eq : stepN 646 gCk_105 = gCk_106 := by decide +kernel
theorem inv_gCk_106 : Inv gCk_106 (gstep gCk_106) := gCk_106_eq ▸ stepN_inv 646 gCk_105 inv_gCk_105
def gCk_107 : GS :=
  ⟨187326, 1141380431157101990, 1141380431158318121, 162722792364683809, 162722792365887061⟩
theorem gCk_107_eq : stepN 668 gCk_106 = gCk_107 := by decide +kernel
theorem inv_gCk_107 : Inv gCk_107 (gstep gCk_107) := gCk_107_eq ▸ stepN_inv 668 gCk_106 inv_gCk_106
def gCk_108 : GS :=
  ⟨188019, 1142224817146911458, 1142224817148136126, 156685873252925807, 156685873254137080⟩
theorem gCk_108_eq : stepN 693 gCk_107 = gCk_108 := by decide +kernel
theorem inv_gCk_108 : Inv gCk_108 (gstep gCk_108) := gCk_108_eq ▸ stepN_inv 693 gCk_107 inv_gCk_107
def gCk_109 : GS :=
  ⟨188740, 1143069428334838211, 1143069428336071805, 150400391587218077, 150400391588437756⟩
theorem gCk_109_eq : stepN 721 gCk_108 = gCk_109 := by decide +kernel
theorem inv_gCk_109 : Inv gCk_109 (gstep gCk_109) := gCk_109_eq ▸ stepN_inv 721 gCk_108 inv_gCk_108
def gCk_110 : GS :=
  ⟨189492, 1143913503507412873, 1143913503508655850, 143839814643628693, 143839814644857163⟩
theorem gCk_110_eq : stepN 752 gCk_109 = gCk_110 := by decide +kernel
theorem inv_gCk_110 : Inv gCk_110 (gstep gCk_110) := gCk_110_eq ▸ stepN_inv 752 gCk_109 inv_gCk_109
def gCk_111 : GS :=
  ⟨190281, 1144758630245513933, 1144758630246766772, 136951357283259210, 136951357284496964⟩
theorem gCk_111_eq : stepN 789 gCk_110 = gCk_111 := by decide +kernel
theorem inv_gCk_111 : Inv gCk_111 (gstep gCk_111) := gCk_111_eq ▸ stepN_inv 789 gCk_110 inv_gCk_110
def gCk_112 : GS :=
  ⟨191111, 1145602902967866430, 1145602902969129693, 129699593271930163, 129699593273177731⟩
theorem gCk_112_eq : stepN 830 gCk_111 = gCk_112 := by decide +kernel
theorem inv_gCk_112 : Inv gCk_112 (gstep gCk_112) := gCk_112_eq ▸ stepN_inv 830 gCk_111 inv_gCk_111
def gCk_113 : GS :=
  ⟨191990, 1146446931901039610, 1146446931902314006, 122014048855016820, 122014048856274844⟩
theorem gCk_113_eq : stepN 879 gCk_112 = gCk_113 := by decide +kernel
theorem inv_gCk_113 : Inv gCk_113 (gstep gCk_113) := gCk_113_eq ▸ stepN_inv 879 gCk_112 inv_gCk_112
def gCk_114 : GS :=
  ⟨192930, 1147292482049514540, 1147292482050800900, 113789087420367361, 113789087421636629⟩
theorem gCk_114_eq : stepN 940 gCk_113 = gCk_114 := by decide +kernel
theorem inv_gCk_114 : Inv gCk_114 (gstep gCk_114) := gCk_114_eq ▸ stepN_inv 940 gCk_113 inv_gCk_113
def gCk_115 : GS :=
  ⟨193946, 1148140037846751277, 1148140037848050676, 104892560634918970, 104892560636200477⟩
theorem gCk_115_eq : stepN 1016 gCk_114 = gCk_115 := by decide +kernel
theorem inv_gCk_115 : Inv gCk_115 (gstep gCk_115) := gCk_115_eq ▸ stepN_inv 1016 gCk_114 inv_gCk_114
def gCk_116 : GS :=
  ⟨194666, 1148698904559540568, 1148698904560849245, 98584088203913260, 98584088205203498⟩
theorem gCk_116_eq : stepN 720 gCk_115 = gCk_116 := by decide +kernel
theorem inv_gCk_116 : Inv gCk_116 (gstep gCk_116) := gCk_116_eq ▸ stepN_inv 720 gCk_115 inv_gCk_115
def gCk_117 : GS :=
  ⟨195242, 1149121042257331347, 1149121042258647483, 93535159296954739, 93535159298251978⟩
theorem gCk_117_eq : stepN 576 gCk_116 = gCk_117 := by decide +kernel
theorem inv_gCk_117 : Inv gCk_117 (gstep gCk_117) := gCk_117_eq ▸ stepN_inv 576 gCk_116 inv_gCk_116
def gCk_118 : GS :=
  ⟨195851, 1149543229566476812, 1149543229567800866, 88195006327757460, 88195006329062147⟩
theorem gCk_118_eq : stepN 609 gCk_117 = gCk_118 := by decide +kernel
theorem inv_gCk_118 : Inv gCk_118 (gstep gCk_118) := gCk_118_eq ▸ stepN_inv 609 gCk_117 inv_gCk_117
def gCk_119 : GS :=
  ⟨196500, 1149965831613157084, 1149965831614489607, 82502011524176196, 82502011525488871⟩
theorem gCk_119_eq : stepN 649 gCk_118 = gCk_119 := by decide +kernel
theorem inv_gCk_119 : Inv gCk_119 (gstep gCk_119) := gCk_119_eq ▸ stepN_inv 649 gCk_118 inv_gCk_118
def gCk_120 : GS :=
  ⟨197196, 1150387707474177181, 1150387707475518824, 76394491133710081, 76394491135031338⟩
theorem gCk_120_eq : stepN 696 gCk_119 = gCk_120 := by decide +kernel
theorem inv_gCk_120 : Inv gCk_120 (gstep gCk_120) := gCk_120_eq ▸ stepN_inv 696 gCk_119 inv_gCk_119
def gCk_121 : GS :=
  ⟨197954, 1150810263801102186, 1150810263802453822, 69740465393523158, 69740465394853832⟩
theorem gCk_121_eq : stepN 758 gCk_120 = gCk_121 := by decide +kernel
theorem inv_gCk_121 : Inv gCk_121 (gstep gCk_121) := gCk_121_eq ▸ stepN_inv 758 gCk_120 inv_gCk_120
def gCk_122 : GS :=
  ⟨198792, 1151232621560746307, 1151232621562109035, 62381462291572538, 62381462292913663⟩
theorem gCk_122_eq : stepN 838 gCk_121 = gCk_122 := by decide +kernel
theorem inv_gCk_122 : Inv gCk_122 (gstep gCk_122) := gCk_122_eq ▸ stepN_inv 838 gCk_121 inv_gCk_121
def gCk_123 : GS :=
  ⟨199742, 1151654515368063696, 1151654515369439095, 54035849355859282, 54035849357212316⟩
theorem gCk_123_eq : stepN 950 gCk_122 = gCk_123 := by decide +kernel
theorem inv_gCk_123 : Inv gCk_123 (gstep gCk_123) := gCk_123_eq ▸ stepN_inv 950 gCk_122 inv_gCk_122
def gCk_124 : GS :=
  ⟨200870, 1152076892884570215, 1152076892885960746, 44122881418693239, 44122881420060524⟩
theorem gCk_124_eq : stepN 1128 gCk_123 = gCk_124 := by decide +kernel
theorem inv_gCk_124 : Inv gCk_124 (gstep gCk_124) := gCk_124_eq ▸ stepN_inv 1128 gCk_123 inv_gCk_123
def gCk_125 : GS :=
  ⟨202414, 1152516706834154224, 1152516706835565647, 30548915715668408, 30548915717055368⟩
theorem gCk_125_eq : stepN 1544 gCk_124 = gCk_125 := by decide +kernel
theorem inv_gCk_125 : Inv gCk_125 (gstep gCk_125) := gCk_125_eq ▸ stepN_inv 1544 gCk_124 inv_gCk_124
def gCk_126 : GS :=
  ⟨204532, 1152859860532468736, 1152859860533909192, 11922154012388469, 11922154013802794⟩
theorem gCk_126_eq : stepN 2118 gCk_125 = gCk_126 := by decide +kernel
theorem inv_gCk_126 : Inv gCk_126 (gstep gCk_126) := gCk_126_eq ▸ stepN_inv 2118 gCk_125 inv_gCk_125
def gCk_127 : GS :=
  ⟨205425, 1152914329713264730, 1152914329714717529, 4067446993953055, 4067446995379026⟩
theorem gCk_127_eq : stepN 893 gCk_126 = gCk_127 := by decide +kernel
theorem inv_gCk_127 : Inv gCk_127 (gstep gCk_127) := gCk_127_eq ▸ stepN_inv 893 gCk_126 inv_gCk_126

theorem chunkPos25_0 :
    walkLeavesPos25 ((leafData25.drop 0).take 98) gCk_0 (gstepS gCk_0) = true := by
  rw [← walkLeavesPos25Fast4_eq]; decide +kernel
theorem chunkPos25_1 :
    walkLeavesPos25 ((leafData25.drop 98).take 13) gCk_1 (gstepS gCk_1) = true := by
  rw [← walkLeavesPos25Fast4_eq]; decide +kernel
theorem chunkPos25_2 :
    walkLeavesPos25 ((leafData25.drop 111).take 3) gCk_2 (gstepS gCk_2) = true := by
  rw [← walkLeavesPos25Fast4_eq]; decide +kernel
theorem chunkPos25_3 :
    walkLeavesPos25 ((leafData25.drop 114).take 11) gCk_3 (gstepS gCk_3) = true := by
  rw [← walkLeavesPos25Fast4_eq]; decide +kernel
theorem chunkPos25_4 :
    walkLeavesPos25 ((leafData25.drop 125).take 22) gCk_4 (gstepS gCk_4) = true := by
  rw [← walkLeavesPos25Fast4_eq]; decide +kernel
theorem chunkPos25_5 :
    walkLeavesPos25 ((leafData25.drop 147).take 13) gCk_5 (gstepS gCk_5) = true := by
  rw [← walkLeavesPos25Fast4_eq]; decide +kernel
theorem chunkPos25_6 :
    walkLeavesPos25 ((leafData25.drop 160).take 9) gCk_6 (gstepS gCk_6) = true := by
  rw [← walkLeavesPos25Fast4_eq]; decide +kernel
theorem chunkPos25_7 :
    walkLeavesPos25 ((leafData25.drop 169).take 5) gCk_7 (gstepS gCk_7) = true := by
  rw [← walkLeavesPos25Fast4_eq]; decide +kernel
theorem chunkPos25_8 :
    walkLeavesPos25 ((leafData25.drop 174).take 3) gCk_8 (gstepS gCk_8) = true := by
  rw [← walkLeavesPos25Fast4_eq]; decide +kernel
theorem chunkPos25_9 :
    walkLeavesPos25 ((leafData25.drop 177).take 18) gCk_9 (gstepS gCk_9) = true := by
  rw [← walkLeavesPos25Fast4_eq]; decide +kernel
theorem chunkPos25_10 :
    walkLeavesPos25 ((leafData25.drop 195).take 5) gCk_10 (gstepS gCk_10) = true := by
  rw [← walkLeavesPos25Fast4_eq]; decide +kernel
theorem chunkPos25_11 :
    walkLeavesPos25 ((leafData25.drop 200).take 3) gCk_11 (gstepS gCk_11) = true := by
  rw [← walkLeavesPos25Fast4_eq]; decide +kernel
theorem chunkPos25_12 :
    walkLeavesPos25 ((leafData25.drop 203).take 7) gCk_12 (gstepS gCk_12) = true := by
  rw [← walkLeavesPos25Fast4_eq]; decide +kernel
theorem chunkPos25_13 :
    walkLeavesPos25 ((leafData25.drop 210).take 3) gCk_14 (gstepS gCk_14) = true := by
  rw [← walkLeavesPos25Fast4_eq]; decide +kernel
theorem chunkPos25_14 :
    walkLeavesPos25 ((leafData25.drop 213).take 4) gCk_16 (gstepS gCk_16) = true := by
  rw [← walkLeavesPos25Fast4_eq]; decide +kernel
theorem chunkPos25_15 :
    walkLeavesPos25 ((leafData25.drop 217).take 4) gCk_18 (gstepS gCk_18) = true := by
  rw [← walkLeavesPos25Fast4_eq]; decide +kernel
theorem chunkPos25_16 :
    walkLeavesPos25 ((leafData25.drop 221).take 13) gCk_20 (gstepS gCk_20) = true := by
  rw [← walkLeavesPos25Fast4_eq]; decide +kernel
theorem chunkPos25_17 :
    walkLeavesPos25 ((leafData25.drop 234).take 5) gCk_22 (gstepS gCk_22) = true := by
  rw [← walkLeavesPos25Fast4_eq]; decide +kernel
theorem chunkPos25_18 :
    walkLeavesPos25 ((leafData25.drop 239).take 7) gCk_24 (gstepS gCk_24) = true := by
  rw [← walkLeavesPos25Fast4_eq]; decide +kernel
theorem chunkPos25_19 :
    walkLeavesPos25 ((leafData25.drop 246).take 12) gCk_26 (gstepS gCk_26) = true := by
  rw [← walkLeavesPos25Fast4_eq]; decide +kernel
theorem chunkPos25_20 :
    walkLeavesPos25 ((leafData25.drop 258).take 14) gCk_28 (gstepS gCk_28) = true := by
  rw [← walkLeavesPos25Fast4_eq]; decide +kernel
theorem chunkPos25_21 :
    walkLeavesPos25 ((leafData25.drop 272).take 4) gCk_29 (gstepS gCk_29) = true := by
  rw [← walkLeavesPos25Fast4_eq]; decide +kernel
theorem chunkPos25_22 :
    walkLeavesPos25 ((leafData25.drop 276).take 10) gCk_30 (gstepS gCk_30) = true := by
  rw [← walkLeavesPos25Fast4_eq]; decide +kernel
theorem chunkPos25_23 :
    walkLeavesPos25 ((leafData25.drop 286).take 3) gCk_31 (gstepS gCk_31) = true := by
  rw [← walkLeavesPos25Fast4_eq]; decide +kernel
theorem chunkPos25_24 :
    walkLeavesPos25 ((leafData25.drop 289).take 20) gCk_32 (gstepS gCk_32) = true := by
  rw [← walkLeavesPos25Fast4_eq]; decide +kernel
theorem chunkPos25_25 :
    walkLeavesPos25 ((leafData25.drop 309).take 3) gCk_33 (gstepS gCk_33) = true := by
  rw [← walkLeavesPos25Fast4_eq]; decide +kernel
theorem chunkPos25_26 :
    walkLeavesPos25 ((leafData25.drop 312).take 5) gCk_34 (gstepS gCk_34) = true := by
  rw [← walkLeavesPos25Fast4_eq]; decide +kernel
theorem chunkPos25_27 :
    walkLeavesPos25 ((leafData25.drop 317).take 7) gCk_35 (gstepS gCk_35) = true := by
  rw [← walkLeavesPos25Fast4_eq]; decide +kernel
theorem chunkPos25_28 :
    walkLeavesPos25 ((leafData25.drop 324).take 7) gCk_36 (gstepS gCk_36) = true := by
  rw [← walkLeavesPos25Fast4_eq]; decide +kernel
theorem chunkPos25_29 :
    walkLeavesPos25 ((leafData25.drop 331).take 3) gCk_37 (gstepS gCk_37) = true := by
  rw [← walkLeavesPos25Fast4_eq]; decide +kernel
theorem chunkPos25_30 :
    walkLeavesPos25 ((leafData25.drop 334).take 35) gCk_38 (gstepS gCk_38) = true := by
  rw [← walkLeavesPos25Fast4_eq]; decide +kernel
theorem chunkPos25_31 :
    walkLeavesPos25 ((leafData25.drop 369).take 13) gCk_39 (gstepS gCk_39) = true := by
  rw [← walkLeavesPos25Fast4_eq]; decide +kernel
theorem chunkPos25_32 :
    walkLeavesPos25 ((leafData25.drop 382).take 4) gCk_40 (gstepS gCk_40) = true := by
  rw [← walkLeavesPos25Fast4_eq]; decide +kernel
theorem chunkPos25_33 :
    walkLeavesPos25 ((leafData25.drop 386).take 9) gCk_41 (gstepS gCk_41) = true := by
  rw [← walkLeavesPos25Fast4_eq]; decide +kernel
theorem chunkPos25_34 :
    walkLeavesPos25 ((leafData25.drop 395).take 13) gCk_42 (gstepS gCk_42) = true := by
  rw [← walkLeavesPos25Fast4_eq]; decide +kernel
theorem chunkPos25_35 :
    walkLeavesPos25 ((leafData25.drop 408).take 20) gCk_43 (gstepS gCk_43) = true := by
  rw [← walkLeavesPos25Fast4_eq]; decide +kernel
theorem chunkPos25_36 :
    walkLeavesPos25 ((leafData25.drop 428).take 10) gCk_44 (gstepS gCk_44) = true := by
  rw [← walkLeavesPos25Fast4_eq]; decide +kernel
theorem chunkPos25_37 :
    walkLeavesPos25 ((leafData25.drop 438).take 3) gCk_45 (gstepS gCk_45) = true := by
  rw [← walkLeavesPos25Fast4_eq]; decide +kernel
theorem chunkPos25_38 :
    walkLeavesPos25 ((leafData25.drop 441).take 7) gCk_46 (gstepS gCk_46) = true := by
  rw [← walkLeavesPos25Fast4_eq]; decide +kernel
theorem chunkPos25_39 :
    walkLeavesPos25 ((leafData25.drop 448).take 3) gCk_47 (gstepS gCk_47) = true := by
  rw [← walkLeavesPos25Fast4_eq]; decide +kernel
theorem chunkPos25_40 :
    walkLeavesPos25 ((leafData25.drop 451).take 3) gCk_48 (gstepS gCk_48) = true := by
  rw [← walkLeavesPos25Fast4_eq]; decide +kernel
theorem chunkPos25_41 :
    walkLeavesPos25 ((leafData25.drop 454).take 8) gCk_49 (gstepS gCk_49) = true := by
  rw [← walkLeavesPos25Fast4_eq]; decide +kernel
theorem chunkPos25_42 :
    walkLeavesPos25 ((leafData25.drop 462).take 7) gCk_50 (gstepS gCk_50) = true := by
  rw [← walkLeavesPos25Fast4_eq]; decide +kernel
theorem chunkPos25_43 :
    walkLeavesPos25 ((leafData25.drop 469).take 3) gCk_51 (gstepS gCk_51) = true := by
  rw [← walkLeavesPos25Fast4_eq]; decide +kernel
theorem chunkPos25_44 :
    walkLeavesPos25 ((leafData25.drop 472).take 10) gCk_52 (gstepS gCk_52) = true := by
  rw [← walkLeavesPos25Fast4_eq]; decide +kernel
theorem chunkPos25_45 :
    walkLeavesPos25 ((leafData25.drop 482).take 4) gCk_53 (gstepS gCk_53) = true := by
  rw [← walkLeavesPos25Fast4_eq]; decide +kernel
theorem chunkPos25_46 :
    walkLeavesPos25 ((leafData25.drop 486).take 11) gCk_54 (gstepS gCk_54) = true := by
  rw [← walkLeavesPos25Fast4_eq]; decide +kernel
theorem chunkPos25_47 :
    walkLeavesPos25 ((leafData25.drop 497).take 21) gCk_55 (gstepS gCk_55) = true := by
  rw [← walkLeavesPos25Fast4_eq]; decide +kernel
theorem chunkPos25_48 :
    walkLeavesPos25 ((leafData25.drop 518).take 3) gCk_56 (gstepS gCk_56) = true := by
  rw [← walkLeavesPos25Fast4_eq]; decide +kernel
theorem chunkPos25_49 :
    walkLeavesPos25 ((leafData25.drop 521).take 14) gCk_57 (gstepS gCk_57) = true := by
  rw [← walkLeavesPos25Fast4_eq]; decide +kernel
theorem chunkPos25_50 :
    walkLeavesPos25 ((leafData25.drop 535).take 12) gCk_58 (gstepS gCk_58) = true := by
  rw [← walkLeavesPos25Fast4_eq]; decide +kernel
theorem chunkPos25_51 :
    walkLeavesPos25 ((leafData25.drop 547).take 3) gCk_59 (gstepS gCk_59) = true := by
  rw [← walkLeavesPos25Fast4_eq]; decide +kernel
theorem chunkPos25_52 :
    walkLeavesPos25 ((leafData25.drop 550).take 11) gCk_60 (gstepS gCk_60) = true := by
  rw [← walkLeavesPos25Fast4_eq]; decide +kernel
theorem chunkPos25_53 :
    walkLeavesPos25 ((leafData25.drop 561).take 7) gCk_61 (gstepS gCk_61) = true := by
  rw [← walkLeavesPos25Fast4_eq]; decide +kernel
theorem chunkPos25_54 :
    walkLeavesPos25 ((leafData25.drop 568).take 3) gCk_62 (gstepS gCk_62) = true := by
  rw [← walkLeavesPos25Fast4_eq]; decide +kernel
theorem chunkPos25_55 :
    walkLeavesPos25 ((leafData25.drop 571).take 3) gCk_63 (gstepS gCk_63) = true := by
  rw [← walkLeavesPos25Fast4_eq]; decide +kernel
theorem chunkPos25_56 :
    walkLeavesPos25 ((leafData25.drop 574).take 11) gCk_64 (gstepS gCk_64) = true := by
  rw [← walkLeavesPos25Fast4_eq]; decide +kernel
theorem chunkPos25_57 :
    walkLeavesPos25 ((leafData25.drop 585).take 3) gCk_65 (gstepS gCk_65) = true := by
  rw [← walkLeavesPos25Fast4_eq]; decide +kernel
theorem chunkPos25_58 :
    walkLeavesPos25 ((leafData25.drop 588).take 5) gCk_66 (gstepS gCk_66) = true := by
  rw [← walkLeavesPos25Fast4_eq]; decide +kernel
theorem chunkPos25_59 :
    walkLeavesPos25 ((leafData25.drop 593).take 3) gCk_67 (gstepS gCk_67) = true := by
  rw [← walkLeavesPos25Fast4_eq]; decide +kernel
theorem chunkPos25_60 :
    walkLeavesPos25 ((leafData25.drop 596).take 8) gCk_68 (gstepS gCk_68) = true := by
  rw [← walkLeavesPos25Fast4_eq]; decide +kernel
theorem chunkPos25_61 :
    walkLeavesPos25 ((leafData25.drop 604).take 11) gCk_69 (gstepS gCk_69) = true := by
  rw [← walkLeavesPos25Fast4_eq]; decide +kernel
theorem chunkPos25_62 :
    walkLeavesPos25 ((leafData25.drop 615).take 7) gCk_70 (gstepS gCk_70) = true := by
  rw [← walkLeavesPos25Fast4_eq]; decide +kernel
theorem chunkPos25_63 :
    walkLeavesPos25 ((leafData25.drop 622).take 4) gCk_71 (gstepS gCk_71) = true := by
  rw [← walkLeavesPos25Fast4_eq]; decide +kernel
theorem chunkPos25_64 :
    walkLeavesPos25 ((leafData25.drop 626).take 6) gCk_72 (gstepS gCk_72) = true := by
  rw [← walkLeavesPos25Fast4_eq]; decide +kernel
theorem chunkPos25_65 :
    walkLeavesPos25 ((leafData25.drop 632).take 8) gCk_73 (gstepS gCk_73) = true := by
  rw [← walkLeavesPos25Fast4_eq]; decide +kernel
theorem chunkPos25_66 :
    walkLeavesPos25 ((leafData25.drop 640).take 3) gCk_74 (gstepS gCk_74) = true := by
  rw [← walkLeavesPos25Fast4_eq]; decide +kernel
theorem chunkPos25_67 :
    walkLeavesPos25 ((leafData25.drop 643).take 5) gCk_75 (gstepS gCk_75) = true := by
  rw [← walkLeavesPos25Fast4_eq]; decide +kernel
theorem chunkPos25_68 :
    walkLeavesPos25 ((leafData25.drop 648).take 8) gCk_76 (gstepS gCk_76) = true := by
  rw [← walkLeavesPos25Fast4_eq]; decide +kernel
theorem chunkPos25_69 :
    walkLeavesPos25 ((leafData25.drop 656).take 12) gCk_77 (gstepS gCk_77) = true := by
  rw [← walkLeavesPos25Fast4_eq]; decide +kernel
theorem chunkPos25_70 :
    walkLeavesPos25 ((leafData25.drop 668).take 4) gCk_78 (gstepS gCk_78) = true := by
  rw [← walkLeavesPos25Fast4_eq]; decide +kernel
theorem chunkPos25_71 :
    walkLeavesPos25 ((leafData25.drop 672).take 23) gCk_79 (gstepS gCk_79) = true := by
  rw [← walkLeavesPos25Fast4_eq]; decide +kernel
theorem chunkPos25_72 :
    walkLeavesPos25 ((leafData25.drop 695).take 11) gCk_80 (gstepS gCk_80) = true := by
  rw [← walkLeavesPos25Fast4_eq]; decide +kernel
theorem chunkPos25_73 :
    walkLeavesPos25 ((leafData25.drop 706).take 7) gCk_81 (gstepS gCk_81) = true := by
  rw [← walkLeavesPos25Fast4_eq]; decide +kernel
theorem chunkPos25_74 :
    walkLeavesPos25 ((leafData25.drop 713).take 5) gCk_82 (gstepS gCk_82) = true := by
  rw [← walkLeavesPos25Fast4_eq]; decide +kernel
theorem chunkPos25_75 :
    walkLeavesPos25 ((leafData25.drop 718).take 10) gCk_83 (gstepS gCk_83) = true := by
  rw [← walkLeavesPos25Fast4_eq]; decide +kernel
theorem chunkPos25_76 :
    walkLeavesPos25 ((leafData25.drop 728).take 3) gCk_84 (gstepS gCk_84) = true := by
  rw [← walkLeavesPos25Fast4_eq]; decide +kernel
theorem chunkPos25_77 :
    walkLeavesPos25 ((leafData25.drop 731).take 16) gCk_85 (gstepS gCk_85) = true := by
  rw [← walkLeavesPos25Fast4_eq]; decide +kernel
theorem chunkPos25_78 :
    walkLeavesPos25 ((leafData25.drop 747).take 7) gCk_86 (gstepS gCk_86) = true := by
  rw [← walkLeavesPos25Fast4_eq]; decide +kernel
theorem chunkPos25_79 :
    walkLeavesPos25 ((leafData25.drop 754).take 12) gCk_87 (gstepS gCk_87) = true := by
  rw [← walkLeavesPos25Fast4_eq]; decide +kernel
theorem chunkPos25_80 :
    walkLeavesPos25 ((leafData25.drop 766).take 3) gCk_88 (gstepS gCk_88) = true := by
  rw [← walkLeavesPos25Fast4_eq]; decide +kernel
theorem chunkPos25_81 :
    walkLeavesPos25 ((leafData25.drop 769).take 3) gCk_89 (gstepS gCk_89) = true := by
  rw [← walkLeavesPos25Fast4_eq]; decide +kernel
theorem chunkPos25_82 :
    walkLeavesPos25 ((leafData25.drop 772).take 11) gCk_90 (gstepS gCk_90) = true := by
  rw [← walkLeavesPos25Fast4_eq]; decide +kernel
theorem chunkPos25_83 :
    walkLeavesPos25 ((leafData25.drop 783).take 8) gCk_91 (gstepS gCk_91) = true := by
  rw [← walkLeavesPos25Fast4_eq]; decide +kernel
theorem chunkPos25_84 :
    walkLeavesPos25 ((leafData25.drop 791).take 6) gCk_92 (gstepS gCk_92) = true := by
  rw [← walkLeavesPos25Fast4_eq]; decide +kernel
theorem chunkPos25_85 :
    walkLeavesPos25 ((leafData25.drop 797).take 6) gCk_93 (gstepS gCk_93) = true := by
  rw [← walkLeavesPos25Fast4_eq]; decide +kernel
theorem chunkPos25_86 :
    walkLeavesPos25 ((leafData25.drop 803).take 7) gCk_94 (gstepS gCk_94) = true := by
  rw [← walkLeavesPos25Fast4_eq]; decide +kernel
theorem chunkPos25_87 :
    walkLeavesPos25 ((leafData25.drop 810).take 9) gCk_95 (gstepS gCk_95) = true := by
  rw [← walkLeavesPos25Fast4_eq]; decide +kernel
theorem chunkPos25_88 :
    walkLeavesPos25 ((leafData25.drop 819).take 6) gCk_96 (gstepS gCk_96) = true := by
  rw [← walkLeavesPos25Fast4_eq]; decide +kernel
theorem chunkPos25_89 :
    walkLeavesPos25 ((leafData25.drop 825).take 8) gCk_97 (gstepS gCk_97) = true := by
  rw [← walkLeavesPos25Fast4_eq]; decide +kernel
theorem chunkPos25_90 :
    walkLeavesPos25 ((leafData25.drop 833).take 3) gCk_98 (gstepS gCk_98) = true := by
  rw [← walkLeavesPos25Fast4_eq]; decide +kernel
theorem chunkPos25_91 :
    walkLeavesPos25 ((leafData25.drop 836).take 3) gCk_99 (gstepS gCk_99) = true := by
  rw [← walkLeavesPos25Fast4_eq]; decide +kernel
theorem chunkPos25_92 :
    walkLeavesPos25 ((leafData25.drop 839).take 8) gCk_100 (gstepS gCk_100) = true := by
  rw [← walkLeavesPos25Fast4_eq]; decide +kernel
theorem chunkPos25_93 :
    walkLeavesPos25 ((leafData25.drop 847).take 4) gCk_101 (gstepS gCk_101) = true := by
  rw [← walkLeavesPos25Fast4_eq]; decide +kernel
theorem chunkPos25_94 :
    walkLeavesPos25 ((leafData25.drop 851).take 3) gCk_102 (gstepS gCk_102) = true := by
  rw [← walkLeavesPos25Fast4_eq]; decide +kernel
theorem chunkPos25_95 :
    walkLeavesPos25 ((leafData25.drop 854).take 11) gCk_103 (gstepS gCk_103) = true := by
  rw [← walkLeavesPos25Fast4_eq]; decide +kernel
theorem chunkPos25_96 :
    walkLeavesPos25 ((leafData25.drop 865).take 8) gCk_104 (gstepS gCk_104) = true := by
  rw [← walkLeavesPos25Fast4_eq]; decide +kernel
theorem chunkPos25_97 :
    walkLeavesPos25 ((leafData25.drop 873).take 5) gCk_105 (gstepS gCk_105) = true := by
  rw [← walkLeavesPos25Fast4_eq]; decide +kernel
theorem chunkPos25_98 :
    walkLeavesPos25 ((leafData25.drop 878).take 6) gCk_106 (gstepS gCk_106) = true := by
  rw [← walkLeavesPos25Fast4_eq]; decide +kernel
theorem chunkPos25_99 :
    walkLeavesPos25 ((leafData25.drop 884).take 4) gCk_107 (gstepS gCk_107) = true := by
  rw [← walkLeavesPos25Fast4_eq]; decide +kernel
theorem chunkPos25_100 :
    walkLeavesPos25 ((leafData25.drop 888).take 3) gCk_108 (gstepS gCk_108) = true := by
  rw [← walkLeavesPos25Fast4_eq]; decide +kernel
theorem chunkPos25_101 :
    walkLeavesPos25 ((leafData25.drop 891).take 3) gCk_109 (gstepS gCk_109) = true := by
  rw [← walkLeavesPos25Fast4_eq]; decide +kernel
theorem chunkPos25_102 :
    walkLeavesPos25 ((leafData25.drop 894).take 7) gCk_110 (gstepS gCk_110) = true := by
  rw [← walkLeavesPos25Fast4_eq]; decide +kernel
theorem chunkPos25_103 :
    walkLeavesPos25 ((leafData25.drop 901).take 11) gCk_111 (gstepS gCk_111) = true := by
  rw [← walkLeavesPos25Fast4_eq]; decide +kernel
theorem chunkPos25_104 :
    walkLeavesPos25 ((leafData25.drop 912).take 6) gCk_112 (gstepS gCk_112) = true := by
  rw [← walkLeavesPos25Fast4_eq]; decide +kernel
theorem chunkPos25_105 :
    walkLeavesPos25 ((leafData25.drop 918).take 7) gCk_113 (gstepS gCk_113) = true := by
  rw [← walkLeavesPos25Fast4_eq]; decide +kernel
theorem chunkPos25_106 :
    walkLeavesPos25 ((leafData25.drop 925).take 8) gCk_114 (gstepS gCk_114) = true := by
  rw [← walkLeavesPos25Fast4_eq]; decide +kernel
theorem chunkPos25_107 :
    walkLeavesPos25 ((leafData25.drop 933).take 5) gCk_115 (gstepS gCk_115) = true := by
  rw [← walkLeavesPos25Fast4_eq]; decide +kernel
theorem chunkPos25_108 :
    walkLeavesPos25 ((leafData25.drop 938).take 3) gCk_116 (gstepS gCk_116) = true := by
  rw [← walkLeavesPos25Fast4_eq]; decide +kernel
theorem chunkPos25_109 :
    walkLeavesPos25 ((leafData25.drop 941).take 3) gCk_117 (gstepS gCk_117) = true := by
  rw [← walkLeavesPos25Fast4_eq]; decide +kernel
theorem chunkPos25_110 :
    walkLeavesPos25 ((leafData25.drop 944).take 3) gCk_118 (gstepS gCk_118) = true := by
  rw [← walkLeavesPos25Fast4_eq]; decide +kernel
theorem chunkPos25_111 :
    walkLeavesPos25 ((leafData25.drop 947).take 3) gCk_119 (gstepS gCk_119) = true := by
  rw [← walkLeavesPos25Fast4_eq]; decide +kernel
theorem chunkPos25_112 :
    walkLeavesPos25 ((leafData25.drop 950).take 4) gCk_120 (gstepS gCk_120) = true := by
  rw [← walkLeavesPos25Fast4_eq]; decide +kernel
theorem chunkPos25_113 :
    walkLeavesPos25 ((leafData25.drop 954).take 6) gCk_121 (gstepS gCk_121) = true := by
  rw [← walkLeavesPos25Fast4_eq]; decide +kernel
theorem chunkPos25_114 :
    walkLeavesPos25 ((leafData25.drop 960).take 6) gCk_122 (gstepS gCk_122) = true := by
  rw [← walkLeavesPos25Fast4_eq]; decide +kernel
theorem chunkPos25_115 :
    walkLeavesPos25 ((leafData25.drop 966).take 10) gCk_123 (gstepS gCk_123) = true := by
  rw [← walkLeavesPos25Fast4_eq]; decide +kernel
theorem chunkPos25_116 :
    walkLeavesPos25 ((leafData25.drop 976).take 17) gCk_124 (gstepS gCk_124) = true := by
  rw [← walkLeavesPos25Fast4_eq]; decide +kernel
theorem chunkPos25_117 :
    walkLeavesPos25 ((leafData25.drop 993).take 25) gCk_125 (gstepS gCk_125) = true := by
  rw [← walkLeavesPos25Fast4_eq]; decide +kernel
theorem chunkPos25_118 :
    walkLeavesPos25 ((leafData25.drop 1018).take 25) gCk_126 (gstepS gCk_126) = true := by
  rw [← walkLeavesPos25Fast4_eq]; decide +kernel
theorem chunkPos25_119 :
    walkLeavesPos25 ((leafData25.drop 1043).take 21) gCk_127 (gstepS gCk_127) = true := by
  rw [← walkLeavesPos25Fast4_eq]; decide +kernel

theorem walkLeafPos25_sound {L : Leaf25} (hL : L ∈ leafData25) :
    ∀ (n u : ℕ) (g gn : GS) (_ : Inv g gn) (k : GS → GS → Bool),
      L.us ≤ u → u + n * 2 ^ L.b_sub ≤ L.ue → u % 2 ^ L.b_sub = 0 →
      walkLeafPos25 L n u g gn k = true →
      ∃ g' gn', Inv g' gn' ∧ k g' gn' = true ∧ ∀ i < n * 2 ^ L.b_sub, PtPosOK25 L (u + i)
  | 0, _, g, gn, hinv, _, _, _, _, hr =>
      ⟨g, gn, hinv, hr, fun _ _ => by omega⟩
  | n + 1, u, g, gn, hinv, k, hu1, hu2, hmod, hr => by
      have hmul : (n + 1) * 2 ^ L.b_sub = 2 ^ L.b_sub + n * 2 ^ L.b_sub := by ring
      have hr' : stepBlockPos25 u L g gn (fun g' gn' =>
          walkLeafPos25 L n (u + 2 ^ L.b_sub) g' gn' k) = true := by
        dsimp only [walkLeafPos25] at hr
        rwa [shiftLeft_eq_mul_pow, one_mul] at hr
      obtain ⟨g1, gn1, hinv1, hr1, hblk0⟩ :=
        stepBlockPos25_sound hL hu1 (by omega) hmod hinv hr'
      obtain ⟨g2, gn2, hinv2, hr2, hblk_rest⟩ :=
        walkLeafPos25_sound hL n (u + 2 ^ L.b_sub) g1 gn1 hinv1 k (by omega) (by omega)
          (by rw [Nat.add_mod, hmod, Nat.mod_self, Nat.zero_mod]) hr1
      refine ⟨g2, gn2, hinv2, hr2, fun i hi => ?_⟩
      by_cases hlt : i < 2 ^ L.b_sub
      · exact hblk0 i hlt
      · have h2 := hblk_rest (i - 2 ^ L.b_sub) (by omega)
        rwa [show u + 2 ^ L.b_sub + (i - 2 ^ L.b_sub) = u + i by omega] at h2

theorem walkLeavesPos25_sound :
    ∀ (ls : List Leaf25) (g gn : GS) (_ : Inv g gn),
      (∀ L ∈ ls, L ∈ leafData25) →
      walkLeavesPos25 ls g gn = true →
      ∀ L ∈ ls, ∀ u, L.us ≤ u → u < L.ue → PtPosOK25 L u
  | [], _, _, _, _, _, _, hmem, _, _, _ => absurd hmem List.not_mem_nil
  | L :: ls, g, gn, hinv, hsub, hr, L', hmem, u, hu1, hu2 => by
      have hL_in : L ∈ leafData25 := hsub L (List.mem_cons.mpr (Or.inl rfl))
      obtain ⟨hnsteps, _, hus_mod, _, _⟩ := leafOK25_spec leafData25 leafOK25_leafData L hL_in
      obtain ⟨g', gn', hinv', hr', hpts⟩ :=
        walkLeafPos25_sound hL_in L.nsteps L.us g gn hinv _ le_rfl (by omega) hus_mod hr
      rcases List.mem_cons.mp hmem with h_eq | htail
      · rw [h_eq] at hu1 hu2 ⊢
        have h := hpts (u - L.us) (by omega)
        rwa [show L.us + (u - L.us) = u by omega] at h
      · exact walkLeavesPos25_sound ls g' gn' hinv'
          (fun x hx => hsub x (List.mem_cons_of_mem _ hx)) hr' L' htail u hu1 hu2

theorem mem_leafData25_of_slice {a b : ℕ} {L : Leaf25}
    (h : L ∈ (leafData25.drop a).take b) : L ∈ leafData25 :=
  List.mem_of_mem_drop (List.mem_of_mem_take h)

theorem take_append_drop_eq {α : Type*} : ∀ (n : ℕ) (xs : List α), xs.take n ++ xs.drop n = xs
  | 0, _ => rfl
  | _ + 1, [] => rfl
  | n + 1, x :: xs => congrArg (x :: ·) (take_append_drop_eq n xs)

theorem drop_drop_eq {α : Type*} : ∀ (a b : ℕ) (xs : List α), (xs.drop a).drop b = xs.drop (b + a)
  | 0, _, _ => rfl
  | _ + 1, 0, [] => rfl
  | _ + 1, _ + 1, [] => rfl
  | a + 1, b, _ :: xs => drop_drop_eq a b xs

theorem mem_drop_take_or_drop {α : Type*} (a b : ℕ) {x : α} {xs : List α} (h : x ∈ xs.drop a) :
    x ∈ (xs.drop a).take b ∨ x ∈ xs.drop (b + a) := by
  rw [← take_append_drop_eq b (xs.drop a)] at h
  rcases List.mem_append.mp h with h1 | h2
  · exact Or.inl h1
  · rw [drop_drop_eq] at h2
    exact Or.inr h2


theorem leafData25_drop_end : (leafData25.drop 1064).isEmpty = true := by
  decide +kernel

theorem ptPosOK25_from_90 (L : Leaf25) (hL : L ∈ leafData25.drop 833)
    (u : ℕ) (h1 : L.us ≤ u) (h2 : u < L.ue) :
    PtPosOK25 L u := by
  rcases mem_drop_take_or_drop 833 3 hL with hL | hL
  · exact walkLeavesPos25_sound _ _ _ (inv_gstepS inv_gCk_98)
      (fun _ => mem_leafData25_of_slice) chunkPos25_90 L hL u h1 h2
  rcases mem_drop_take_or_drop 836 3 hL with hL | hL
  · exact walkLeavesPos25_sound _ _ _ (inv_gstepS inv_gCk_99)
      (fun _ => mem_leafData25_of_slice) chunkPos25_91 L hL u h1 h2
  rcases mem_drop_take_or_drop 839 8 hL with hL | hL
  · exact walkLeavesPos25_sound _ _ _ (inv_gstepS inv_gCk_100)
      (fun _ => mem_leafData25_of_slice) chunkPos25_92 L hL u h1 h2
  rcases mem_drop_take_or_drop 847 4 hL with hL | hL
  · exact walkLeavesPos25_sound _ _ _ (inv_gstepS inv_gCk_101)
      (fun _ => mem_leafData25_of_slice) chunkPos25_93 L hL u h1 h2
  rcases mem_drop_take_or_drop 851 3 hL with hL | hL
  · exact walkLeavesPos25_sound _ _ _ (inv_gstepS inv_gCk_102)
      (fun _ => mem_leafData25_of_slice) chunkPos25_94 L hL u h1 h2
  rcases mem_drop_take_or_drop 854 11 hL with hL | hL
  · exact walkLeavesPos25_sound _ _ _ (inv_gstepS inv_gCk_103)
      (fun _ => mem_leafData25_of_slice) chunkPos25_95 L hL u h1 h2
  rcases mem_drop_take_or_drop 865 8 hL with hL | hL
  · exact walkLeavesPos25_sound _ _ _ (inv_gstepS inv_gCk_104)
      (fun _ => mem_leafData25_of_slice) chunkPos25_96 L hL u h1 h2
  rcases mem_drop_take_or_drop 873 5 hL with hL | hL
  · exact walkLeavesPos25_sound _ _ _ (inv_gstepS inv_gCk_105)
      (fun _ => mem_leafData25_of_slice) chunkPos25_97 L hL u h1 h2
  rcases mem_drop_take_or_drop 878 6 hL with hL | hL
  · exact walkLeavesPos25_sound _ _ _ (inv_gstepS inv_gCk_106)
      (fun _ => mem_leafData25_of_slice) chunkPos25_98 L hL u h1 h2
  rcases mem_drop_take_or_drop 884 4 hL with hL | hL
  · exact walkLeavesPos25_sound _ _ _ (inv_gstepS inv_gCk_107)
      (fun _ => mem_leafData25_of_slice) chunkPos25_99 L hL u h1 h2
  rcases mem_drop_take_or_drop 888 3 hL with hL | hL
  · exact walkLeavesPos25_sound _ _ _ (inv_gstepS inv_gCk_108)
      (fun _ => mem_leafData25_of_slice) chunkPos25_100 L hL u h1 h2
  rcases mem_drop_take_or_drop 891 3 hL with hL | hL
  · exact walkLeavesPos25_sound _ _ _ (inv_gstepS inv_gCk_109)
      (fun _ => mem_leafData25_of_slice) chunkPos25_101 L hL u h1 h2
  rcases mem_drop_take_or_drop 894 7 hL with hL | hL
  · exact walkLeavesPos25_sound _ _ _ (inv_gstepS inv_gCk_110)
      (fun _ => mem_leafData25_of_slice) chunkPos25_102 L hL u h1 h2
  rcases mem_drop_take_or_drop 901 11 hL with hL | hL
  · exact walkLeavesPos25_sound _ _ _ (inv_gstepS inv_gCk_111)
      (fun _ => mem_leafData25_of_slice) chunkPos25_103 L hL u h1 h2
  rcases mem_drop_take_or_drop 912 6 hL with hL | hL
  · exact walkLeavesPos25_sound _ _ _ (inv_gstepS inv_gCk_112)
      (fun _ => mem_leafData25_of_slice) chunkPos25_104 L hL u h1 h2
  rcases mem_drop_take_or_drop 918 7 hL with hL | hL
  · exact walkLeavesPos25_sound _ _ _ (inv_gstepS inv_gCk_113)
      (fun _ => mem_leafData25_of_slice) chunkPos25_105 L hL u h1 h2
  rcases mem_drop_take_or_drop 925 8 hL with hL | hL
  · exact walkLeavesPos25_sound _ _ _ (inv_gstepS inv_gCk_114)
      (fun _ => mem_leafData25_of_slice) chunkPos25_106 L hL u h1 h2
  rcases mem_drop_take_or_drop 933 5 hL with hL | hL
  · exact walkLeavesPos25_sound _ _ _ (inv_gstepS inv_gCk_115)
      (fun _ => mem_leafData25_of_slice) chunkPos25_107 L hL u h1 h2
  rcases mem_drop_take_or_drop 938 3 hL with hL | hL
  · exact walkLeavesPos25_sound _ _ _ (inv_gstepS inv_gCk_116)
      (fun _ => mem_leafData25_of_slice) chunkPos25_108 L hL u h1 h2
  rcases mem_drop_take_or_drop 941 3 hL with hL | hL
  · exact walkLeavesPos25_sound _ _ _ (inv_gstepS inv_gCk_117)
      (fun _ => mem_leafData25_of_slice) chunkPos25_109 L hL u h1 h2
  rcases mem_drop_take_or_drop 944 3 hL with hL | hL
  · exact walkLeavesPos25_sound _ _ _ (inv_gstepS inv_gCk_118)
      (fun _ => mem_leafData25_of_slice) chunkPos25_110 L hL u h1 h2
  rcases mem_drop_take_or_drop 947 3 hL with hL | hL
  · exact walkLeavesPos25_sound _ _ _ (inv_gstepS inv_gCk_119)
      (fun _ => mem_leafData25_of_slice) chunkPos25_111 L hL u h1 h2
  rcases mem_drop_take_or_drop 950 4 hL with hL | hL
  · exact walkLeavesPos25_sound _ _ _ (inv_gstepS inv_gCk_120)
      (fun _ => mem_leafData25_of_slice) chunkPos25_112 L hL u h1 h2
  rcases mem_drop_take_or_drop 954 6 hL with hL | hL
  · exact walkLeavesPos25_sound _ _ _ (inv_gstepS inv_gCk_121)
      (fun _ => mem_leafData25_of_slice) chunkPos25_113 L hL u h1 h2
  rcases mem_drop_take_or_drop 960 6 hL with hL | hL
  · exact walkLeavesPos25_sound _ _ _ (inv_gstepS inv_gCk_122)
      (fun _ => mem_leafData25_of_slice) chunkPos25_114 L hL u h1 h2
  rcases mem_drop_take_or_drop 966 10 hL with hL | hL
  · exact walkLeavesPos25_sound _ _ _ (inv_gstepS inv_gCk_123)
      (fun _ => mem_leafData25_of_slice) chunkPos25_115 L hL u h1 h2
  rcases mem_drop_take_or_drop 976 17 hL with hL | hL
  · exact walkLeavesPos25_sound _ _ _ (inv_gstepS inv_gCk_124)
      (fun _ => mem_leafData25_of_slice) chunkPos25_116 L hL u h1 h2
  rcases mem_drop_take_or_drop 993 25 hL with hL | hL
  · exact walkLeavesPos25_sound _ _ _ (inv_gstepS inv_gCk_125)
      (fun _ => mem_leafData25_of_slice) chunkPos25_117 L hL u h1 h2
  rcases mem_drop_take_or_drop 1018 25 hL with hL | hL
  · exact walkLeavesPos25_sound _ _ _ (inv_gstepS inv_gCk_126)
      (fun _ => mem_leafData25_of_slice) chunkPos25_118 L hL u h1 h2
  rcases mem_drop_take_or_drop 1043 21 hL with hL | hL
  · exact walkLeavesPos25_sound _ _ _ (inv_gstepS inv_gCk_127)
      (fun _ => mem_leafData25_of_slice) chunkPos25_119 L hL u h1 h2
  cases hend : leafData25.drop 1064
  · rw [hend] at hL; cases hL
  · have hfalse := leafData25_drop_end; rw [hend] at hfalse; cases hfalse

theorem ptPosOK25_from_60 (L : Leaf25) (hL : L ∈ leafData25.drop 596)
    (u : ℕ) (h1 : L.us ≤ u) (h2 : u < L.ue) :
    PtPosOK25 L u := by
  rcases mem_drop_take_or_drop 596 8 hL with hL | hL
  · exact walkLeavesPos25_sound _ _ _ (inv_gstepS inv_gCk_68)
      (fun _ => mem_leafData25_of_slice) chunkPos25_60 L hL u h1 h2
  rcases mem_drop_take_or_drop 604 11 hL with hL | hL
  · exact walkLeavesPos25_sound _ _ _ (inv_gstepS inv_gCk_69)
      (fun _ => mem_leafData25_of_slice) chunkPos25_61 L hL u h1 h2
  rcases mem_drop_take_or_drop 615 7 hL with hL | hL
  · exact walkLeavesPos25_sound _ _ _ (inv_gstepS inv_gCk_70)
      (fun _ => mem_leafData25_of_slice) chunkPos25_62 L hL u h1 h2
  rcases mem_drop_take_or_drop 622 4 hL with hL | hL
  · exact walkLeavesPos25_sound _ _ _ (inv_gstepS inv_gCk_71)
      (fun _ => mem_leafData25_of_slice) chunkPos25_63 L hL u h1 h2
  rcases mem_drop_take_or_drop 626 6 hL with hL | hL
  · exact walkLeavesPos25_sound _ _ _ (inv_gstepS inv_gCk_72)
      (fun _ => mem_leafData25_of_slice) chunkPos25_64 L hL u h1 h2
  rcases mem_drop_take_or_drop 632 8 hL with hL | hL
  · exact walkLeavesPos25_sound _ _ _ (inv_gstepS inv_gCk_73)
      (fun _ => mem_leafData25_of_slice) chunkPos25_65 L hL u h1 h2
  rcases mem_drop_take_or_drop 640 3 hL with hL | hL
  · exact walkLeavesPos25_sound _ _ _ (inv_gstepS inv_gCk_74)
      (fun _ => mem_leafData25_of_slice) chunkPos25_66 L hL u h1 h2
  rcases mem_drop_take_or_drop 643 5 hL with hL | hL
  · exact walkLeavesPos25_sound _ _ _ (inv_gstepS inv_gCk_75)
      (fun _ => mem_leafData25_of_slice) chunkPos25_67 L hL u h1 h2
  rcases mem_drop_take_or_drop 648 8 hL with hL | hL
  · exact walkLeavesPos25_sound _ _ _ (inv_gstepS inv_gCk_76)
      (fun _ => mem_leafData25_of_slice) chunkPos25_68 L hL u h1 h2
  rcases mem_drop_take_or_drop 656 12 hL with hL | hL
  · exact walkLeavesPos25_sound _ _ _ (inv_gstepS inv_gCk_77)
      (fun _ => mem_leafData25_of_slice) chunkPos25_69 L hL u h1 h2
  rcases mem_drop_take_or_drop 668 4 hL with hL | hL
  · exact walkLeavesPos25_sound _ _ _ (inv_gstepS inv_gCk_78)
      (fun _ => mem_leafData25_of_slice) chunkPos25_70 L hL u h1 h2
  rcases mem_drop_take_or_drop 672 23 hL with hL | hL
  · exact walkLeavesPos25_sound _ _ _ (inv_gstepS inv_gCk_79)
      (fun _ => mem_leafData25_of_slice) chunkPos25_71 L hL u h1 h2
  rcases mem_drop_take_or_drop 695 11 hL with hL | hL
  · exact walkLeavesPos25_sound _ _ _ (inv_gstepS inv_gCk_80)
      (fun _ => mem_leafData25_of_slice) chunkPos25_72 L hL u h1 h2
  rcases mem_drop_take_or_drop 706 7 hL with hL | hL
  · exact walkLeavesPos25_sound _ _ _ (inv_gstepS inv_gCk_81)
      (fun _ => mem_leafData25_of_slice) chunkPos25_73 L hL u h1 h2
  rcases mem_drop_take_or_drop 713 5 hL with hL | hL
  · exact walkLeavesPos25_sound _ _ _ (inv_gstepS inv_gCk_82)
      (fun _ => mem_leafData25_of_slice) chunkPos25_74 L hL u h1 h2
  rcases mem_drop_take_or_drop 718 10 hL with hL | hL
  · exact walkLeavesPos25_sound _ _ _ (inv_gstepS inv_gCk_83)
      (fun _ => mem_leafData25_of_slice) chunkPos25_75 L hL u h1 h2
  rcases mem_drop_take_or_drop 728 3 hL with hL | hL
  · exact walkLeavesPos25_sound _ _ _ (inv_gstepS inv_gCk_84)
      (fun _ => mem_leafData25_of_slice) chunkPos25_76 L hL u h1 h2
  rcases mem_drop_take_or_drop 731 16 hL with hL | hL
  · exact walkLeavesPos25_sound _ _ _ (inv_gstepS inv_gCk_85)
      (fun _ => mem_leafData25_of_slice) chunkPos25_77 L hL u h1 h2
  rcases mem_drop_take_or_drop 747 7 hL with hL | hL
  · exact walkLeavesPos25_sound _ _ _ (inv_gstepS inv_gCk_86)
      (fun _ => mem_leafData25_of_slice) chunkPos25_78 L hL u h1 h2
  rcases mem_drop_take_or_drop 754 12 hL with hL | hL
  · exact walkLeavesPos25_sound _ _ _ (inv_gstepS inv_gCk_87)
      (fun _ => mem_leafData25_of_slice) chunkPos25_79 L hL u h1 h2
  rcases mem_drop_take_or_drop 766 3 hL with hL | hL
  · exact walkLeavesPos25_sound _ _ _ (inv_gstepS inv_gCk_88)
      (fun _ => mem_leafData25_of_slice) chunkPos25_80 L hL u h1 h2
  rcases mem_drop_take_or_drop 769 3 hL with hL | hL
  · exact walkLeavesPos25_sound _ _ _ (inv_gstepS inv_gCk_89)
      (fun _ => mem_leafData25_of_slice) chunkPos25_81 L hL u h1 h2
  rcases mem_drop_take_or_drop 772 11 hL with hL | hL
  · exact walkLeavesPos25_sound _ _ _ (inv_gstepS inv_gCk_90)
      (fun _ => mem_leafData25_of_slice) chunkPos25_82 L hL u h1 h2
  rcases mem_drop_take_or_drop 783 8 hL with hL | hL
  · exact walkLeavesPos25_sound _ _ _ (inv_gstepS inv_gCk_91)
      (fun _ => mem_leafData25_of_slice) chunkPos25_83 L hL u h1 h2
  rcases mem_drop_take_or_drop 791 6 hL with hL | hL
  · exact walkLeavesPos25_sound _ _ _ (inv_gstepS inv_gCk_92)
      (fun _ => mem_leafData25_of_slice) chunkPos25_84 L hL u h1 h2
  rcases mem_drop_take_or_drop 797 6 hL with hL | hL
  · exact walkLeavesPos25_sound _ _ _ (inv_gstepS inv_gCk_93)
      (fun _ => mem_leafData25_of_slice) chunkPos25_85 L hL u h1 h2
  rcases mem_drop_take_or_drop 803 7 hL with hL | hL
  · exact walkLeavesPos25_sound _ _ _ (inv_gstepS inv_gCk_94)
      (fun _ => mem_leafData25_of_slice) chunkPos25_86 L hL u h1 h2
  rcases mem_drop_take_or_drop 810 9 hL with hL | hL
  · exact walkLeavesPos25_sound _ _ _ (inv_gstepS inv_gCk_95)
      (fun _ => mem_leafData25_of_slice) chunkPos25_87 L hL u h1 h2
  rcases mem_drop_take_or_drop 819 6 hL with hL | hL
  · exact walkLeavesPos25_sound _ _ _ (inv_gstepS inv_gCk_96)
      (fun _ => mem_leafData25_of_slice) chunkPos25_88 L hL u h1 h2
  rcases mem_drop_take_or_drop 825 8 hL with hL | hL
  · exact walkLeavesPos25_sound _ _ _ (inv_gstepS inv_gCk_97)
      (fun _ => mem_leafData25_of_slice) chunkPos25_89 L hL u h1 h2
  exact ptPosOK25_from_90 L hL u h1 h2

theorem ptPosOK25_from_30 (L : Leaf25) (hL : L ∈ leafData25.drop 334)
    (u : ℕ) (h1 : L.us ≤ u) (h2 : u < L.ue) :
    PtPosOK25 L u := by
  rcases mem_drop_take_or_drop 334 35 hL with hL | hL
  · exact walkLeavesPos25_sound _ _ _ (inv_gstepS inv_gCk_38)
      (fun _ => mem_leafData25_of_slice) chunkPos25_30 L hL u h1 h2
  rcases mem_drop_take_or_drop 369 13 hL with hL | hL
  · exact walkLeavesPos25_sound _ _ _ (inv_gstepS inv_gCk_39)
      (fun _ => mem_leafData25_of_slice) chunkPos25_31 L hL u h1 h2
  rcases mem_drop_take_or_drop 382 4 hL with hL | hL
  · exact walkLeavesPos25_sound _ _ _ (inv_gstepS inv_gCk_40)
      (fun _ => mem_leafData25_of_slice) chunkPos25_32 L hL u h1 h2
  rcases mem_drop_take_or_drop 386 9 hL with hL | hL
  · exact walkLeavesPos25_sound _ _ _ (inv_gstepS inv_gCk_41)
      (fun _ => mem_leafData25_of_slice) chunkPos25_33 L hL u h1 h2
  rcases mem_drop_take_or_drop 395 13 hL with hL | hL
  · exact walkLeavesPos25_sound _ _ _ (inv_gstepS inv_gCk_42)
      (fun _ => mem_leafData25_of_slice) chunkPos25_34 L hL u h1 h2
  rcases mem_drop_take_or_drop 408 20 hL with hL | hL
  · exact walkLeavesPos25_sound _ _ _ (inv_gstepS inv_gCk_43)
      (fun _ => mem_leafData25_of_slice) chunkPos25_35 L hL u h1 h2
  rcases mem_drop_take_or_drop 428 10 hL with hL | hL
  · exact walkLeavesPos25_sound _ _ _ (inv_gstepS inv_gCk_44)
      (fun _ => mem_leafData25_of_slice) chunkPos25_36 L hL u h1 h2
  rcases mem_drop_take_or_drop 438 3 hL with hL | hL
  · exact walkLeavesPos25_sound _ _ _ (inv_gstepS inv_gCk_45)
      (fun _ => mem_leafData25_of_slice) chunkPos25_37 L hL u h1 h2
  rcases mem_drop_take_or_drop 441 7 hL with hL | hL
  · exact walkLeavesPos25_sound _ _ _ (inv_gstepS inv_gCk_46)
      (fun _ => mem_leafData25_of_slice) chunkPos25_38 L hL u h1 h2
  rcases mem_drop_take_or_drop 448 3 hL with hL | hL
  · exact walkLeavesPos25_sound _ _ _ (inv_gstepS inv_gCk_47)
      (fun _ => mem_leafData25_of_slice) chunkPos25_39 L hL u h1 h2
  rcases mem_drop_take_or_drop 451 3 hL with hL | hL
  · exact walkLeavesPos25_sound _ _ _ (inv_gstepS inv_gCk_48)
      (fun _ => mem_leafData25_of_slice) chunkPos25_40 L hL u h1 h2
  rcases mem_drop_take_or_drop 454 8 hL with hL | hL
  · exact walkLeavesPos25_sound _ _ _ (inv_gstepS inv_gCk_49)
      (fun _ => mem_leafData25_of_slice) chunkPos25_41 L hL u h1 h2
  rcases mem_drop_take_or_drop 462 7 hL with hL | hL
  · exact walkLeavesPos25_sound _ _ _ (inv_gstepS inv_gCk_50)
      (fun _ => mem_leafData25_of_slice) chunkPos25_42 L hL u h1 h2
  rcases mem_drop_take_or_drop 469 3 hL with hL | hL
  · exact walkLeavesPos25_sound _ _ _ (inv_gstepS inv_gCk_51)
      (fun _ => mem_leafData25_of_slice) chunkPos25_43 L hL u h1 h2
  rcases mem_drop_take_or_drop 472 10 hL with hL | hL
  · exact walkLeavesPos25_sound _ _ _ (inv_gstepS inv_gCk_52)
      (fun _ => mem_leafData25_of_slice) chunkPos25_44 L hL u h1 h2
  rcases mem_drop_take_or_drop 482 4 hL with hL | hL
  · exact walkLeavesPos25_sound _ _ _ (inv_gstepS inv_gCk_53)
      (fun _ => mem_leafData25_of_slice) chunkPos25_45 L hL u h1 h2
  rcases mem_drop_take_or_drop 486 11 hL with hL | hL
  · exact walkLeavesPos25_sound _ _ _ (inv_gstepS inv_gCk_54)
      (fun _ => mem_leafData25_of_slice) chunkPos25_46 L hL u h1 h2
  rcases mem_drop_take_or_drop 497 21 hL with hL | hL
  · exact walkLeavesPos25_sound _ _ _ (inv_gstepS inv_gCk_55)
      (fun _ => mem_leafData25_of_slice) chunkPos25_47 L hL u h1 h2
  rcases mem_drop_take_or_drop 518 3 hL with hL | hL
  · exact walkLeavesPos25_sound _ _ _ (inv_gstepS inv_gCk_56)
      (fun _ => mem_leafData25_of_slice) chunkPos25_48 L hL u h1 h2
  rcases mem_drop_take_or_drop 521 14 hL with hL | hL
  · exact walkLeavesPos25_sound _ _ _ (inv_gstepS inv_gCk_57)
      (fun _ => mem_leafData25_of_slice) chunkPos25_49 L hL u h1 h2
  rcases mem_drop_take_or_drop 535 12 hL with hL | hL
  · exact walkLeavesPos25_sound _ _ _ (inv_gstepS inv_gCk_58)
      (fun _ => mem_leafData25_of_slice) chunkPos25_50 L hL u h1 h2
  rcases mem_drop_take_or_drop 547 3 hL with hL | hL
  · exact walkLeavesPos25_sound _ _ _ (inv_gstepS inv_gCk_59)
      (fun _ => mem_leafData25_of_slice) chunkPos25_51 L hL u h1 h2
  rcases mem_drop_take_or_drop 550 11 hL with hL | hL
  · exact walkLeavesPos25_sound _ _ _ (inv_gstepS inv_gCk_60)
      (fun _ => mem_leafData25_of_slice) chunkPos25_52 L hL u h1 h2
  rcases mem_drop_take_or_drop 561 7 hL with hL | hL
  · exact walkLeavesPos25_sound _ _ _ (inv_gstepS inv_gCk_61)
      (fun _ => mem_leafData25_of_slice) chunkPos25_53 L hL u h1 h2
  rcases mem_drop_take_or_drop 568 3 hL with hL | hL
  · exact walkLeavesPos25_sound _ _ _ (inv_gstepS inv_gCk_62)
      (fun _ => mem_leafData25_of_slice) chunkPos25_54 L hL u h1 h2
  rcases mem_drop_take_or_drop 571 3 hL with hL | hL
  · exact walkLeavesPos25_sound _ _ _ (inv_gstepS inv_gCk_63)
      (fun _ => mem_leafData25_of_slice) chunkPos25_55 L hL u h1 h2
  rcases mem_drop_take_or_drop 574 11 hL with hL | hL
  · exact walkLeavesPos25_sound _ _ _ (inv_gstepS inv_gCk_64)
      (fun _ => mem_leafData25_of_slice) chunkPos25_56 L hL u h1 h2
  rcases mem_drop_take_or_drop 585 3 hL with hL | hL
  · exact walkLeavesPos25_sound _ _ _ (inv_gstepS inv_gCk_65)
      (fun _ => mem_leafData25_of_slice) chunkPos25_57 L hL u h1 h2
  rcases mem_drop_take_or_drop 588 5 hL with hL | hL
  · exact walkLeavesPos25_sound _ _ _ (inv_gstepS inv_gCk_66)
      (fun _ => mem_leafData25_of_slice) chunkPos25_58 L hL u h1 h2
  rcases mem_drop_take_or_drop 593 3 hL with hL | hL
  · exact walkLeavesPos25_sound _ _ _ (inv_gstepS inv_gCk_67)
      (fun _ => mem_leafData25_of_slice) chunkPos25_59 L hL u h1 h2
  exact ptPosOK25_from_60 L hL u h1 h2

theorem ptPosOK25_all (L : Leaf25) (hL : L ∈ leafData25) (u : ℕ) (h1 : L.us ≤ u) (h2 : u < L.ue) :
    PtPosOK25 L u := by
  have hL : L ∈ leafData25.drop 0 := hL
  rcases mem_drop_take_or_drop 0 98 hL with hL | hL
  · exact walkLeavesPos25_sound _ _ _ (inv_gstepS inv_gCk_0)
      (fun _ => mem_leafData25_of_slice) chunkPos25_0 L hL u h1 h2
  rcases mem_drop_take_or_drop 98 13 hL with hL | hL
  · exact walkLeavesPos25_sound _ _ _ (inv_gstepS inv_gCk_1)
      (fun _ => mem_leafData25_of_slice) chunkPos25_1 L hL u h1 h2
  rcases mem_drop_take_or_drop 111 3 hL with hL | hL
  · exact walkLeavesPos25_sound _ _ _ (inv_gstepS inv_gCk_2)
      (fun _ => mem_leafData25_of_slice) chunkPos25_2 L hL u h1 h2
  rcases mem_drop_take_or_drop 114 11 hL with hL | hL
  · exact walkLeavesPos25_sound _ _ _ (inv_gstepS inv_gCk_3)
      (fun _ => mem_leafData25_of_slice) chunkPos25_3 L hL u h1 h2
  rcases mem_drop_take_or_drop 125 22 hL with hL | hL
  · exact walkLeavesPos25_sound _ _ _ (inv_gstepS inv_gCk_4)
      (fun _ => mem_leafData25_of_slice) chunkPos25_4 L hL u h1 h2
  rcases mem_drop_take_or_drop 147 13 hL with hL | hL
  · exact walkLeavesPos25_sound _ _ _ (inv_gstepS inv_gCk_5)
      (fun _ => mem_leafData25_of_slice) chunkPos25_5 L hL u h1 h2
  rcases mem_drop_take_or_drop 160 9 hL with hL | hL
  · exact walkLeavesPos25_sound _ _ _ (inv_gstepS inv_gCk_6)
      (fun _ => mem_leafData25_of_slice) chunkPos25_6 L hL u h1 h2
  rcases mem_drop_take_or_drop 169 5 hL with hL | hL
  · exact walkLeavesPos25_sound _ _ _ (inv_gstepS inv_gCk_7)
      (fun _ => mem_leafData25_of_slice) chunkPos25_7 L hL u h1 h2
  rcases mem_drop_take_or_drop 174 3 hL with hL | hL
  · exact walkLeavesPos25_sound _ _ _ (inv_gstepS inv_gCk_8)
      (fun _ => mem_leafData25_of_slice) chunkPos25_8 L hL u h1 h2
  rcases mem_drop_take_or_drop 177 18 hL with hL | hL
  · exact walkLeavesPos25_sound _ _ _ (inv_gstepS inv_gCk_9)
      (fun _ => mem_leafData25_of_slice) chunkPos25_9 L hL u h1 h2
  rcases mem_drop_take_or_drop 195 5 hL with hL | hL
  · exact walkLeavesPos25_sound _ _ _ (inv_gstepS inv_gCk_10)
      (fun _ => mem_leafData25_of_slice) chunkPos25_10 L hL u h1 h2
  rcases mem_drop_take_or_drop 200 3 hL with hL | hL
  · exact walkLeavesPos25_sound _ _ _ (inv_gstepS inv_gCk_11)
      (fun _ => mem_leafData25_of_slice) chunkPos25_11 L hL u h1 h2
  rcases mem_drop_take_or_drop 203 7 hL with hL | hL
  · exact walkLeavesPos25_sound _ _ _ (inv_gstepS inv_gCk_12)
      (fun _ => mem_leafData25_of_slice) chunkPos25_12 L hL u h1 h2
  rcases mem_drop_take_or_drop 210 3 hL with hL | hL
  · exact walkLeavesPos25_sound _ _ _ (inv_gstepS inv_gCk_14)
      (fun _ => mem_leafData25_of_slice) chunkPos25_13 L hL u h1 h2
  rcases mem_drop_take_or_drop 213 4 hL with hL | hL
  · exact walkLeavesPos25_sound _ _ _ (inv_gstepS inv_gCk_16)
      (fun _ => mem_leafData25_of_slice) chunkPos25_14 L hL u h1 h2
  rcases mem_drop_take_or_drop 217 4 hL with hL | hL
  · exact walkLeavesPos25_sound _ _ _ (inv_gstepS inv_gCk_18)
      (fun _ => mem_leafData25_of_slice) chunkPos25_15 L hL u h1 h2
  rcases mem_drop_take_or_drop 221 13 hL with hL | hL
  · exact walkLeavesPos25_sound _ _ _ (inv_gstepS inv_gCk_20)
      (fun _ => mem_leafData25_of_slice) chunkPos25_16 L hL u h1 h2
  rcases mem_drop_take_or_drop 234 5 hL with hL | hL
  · exact walkLeavesPos25_sound _ _ _ (inv_gstepS inv_gCk_22)
      (fun _ => mem_leafData25_of_slice) chunkPos25_17 L hL u h1 h2
  rcases mem_drop_take_or_drop 239 7 hL with hL | hL
  · exact walkLeavesPos25_sound _ _ _ (inv_gstepS inv_gCk_24)
      (fun _ => mem_leafData25_of_slice) chunkPos25_18 L hL u h1 h2
  rcases mem_drop_take_or_drop 246 12 hL with hL | hL
  · exact walkLeavesPos25_sound _ _ _ (inv_gstepS inv_gCk_26)
      (fun _ => mem_leafData25_of_slice) chunkPos25_19 L hL u h1 h2
  rcases mem_drop_take_or_drop 258 14 hL with hL | hL
  · exact walkLeavesPos25_sound _ _ _ (inv_gstepS inv_gCk_28)
      (fun _ => mem_leafData25_of_slice) chunkPos25_20 L hL u h1 h2
  rcases mem_drop_take_or_drop 272 4 hL with hL | hL
  · exact walkLeavesPos25_sound _ _ _ (inv_gstepS inv_gCk_29)
      (fun _ => mem_leafData25_of_slice) chunkPos25_21 L hL u h1 h2
  rcases mem_drop_take_or_drop 276 10 hL with hL | hL
  · exact walkLeavesPos25_sound _ _ _ (inv_gstepS inv_gCk_30)
      (fun _ => mem_leafData25_of_slice) chunkPos25_22 L hL u h1 h2
  rcases mem_drop_take_or_drop 286 3 hL with hL | hL
  · exact walkLeavesPos25_sound _ _ _ (inv_gstepS inv_gCk_31)
      (fun _ => mem_leafData25_of_slice) chunkPos25_23 L hL u h1 h2
  rcases mem_drop_take_or_drop 289 20 hL with hL | hL
  · exact walkLeavesPos25_sound _ _ _ (inv_gstepS inv_gCk_32)
      (fun _ => mem_leafData25_of_slice) chunkPos25_24 L hL u h1 h2
  rcases mem_drop_take_or_drop 309 3 hL with hL | hL
  · exact walkLeavesPos25_sound _ _ _ (inv_gstepS inv_gCk_33)
      (fun _ => mem_leafData25_of_slice) chunkPos25_25 L hL u h1 h2
  rcases mem_drop_take_or_drop 312 5 hL with hL | hL
  · exact walkLeavesPos25_sound _ _ _ (inv_gstepS inv_gCk_34)
      (fun _ => mem_leafData25_of_slice) chunkPos25_26 L hL u h1 h2
  rcases mem_drop_take_or_drop 317 7 hL with hL | hL
  · exact walkLeavesPos25_sound _ _ _ (inv_gstepS inv_gCk_35)
      (fun _ => mem_leafData25_of_slice) chunkPos25_27 L hL u h1 h2
  rcases mem_drop_take_or_drop 324 7 hL with hL | hL
  · exact walkLeavesPos25_sound _ _ _ (inv_gstepS inv_gCk_36)
      (fun _ => mem_leafData25_of_slice) chunkPos25_28 L hL u h1 h2
  rcases mem_drop_take_or_drop 331 3 hL with hL | hL
  · exact walkLeavesPos25_sound _ _ _ (inv_gstepS inv_gCk_37)
      (fun _ => mem_leafData25_of_slice) chunkPos25_29 L hL u h1 h2
  exact ptPosOK25_from_30 L hL u h1 h2

end ArcsinImpl

end QuantumComputation.Specs
