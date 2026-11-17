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

public import QuantumComputationDiscoveries.Primitives.Arcsin.Solution.PolyTables

@[expose] public section

namespace QuantumComputation.Specs.ArcsinImpl

open Operator Matrix QProg Function Step
open scoped Matrix ComplexOrder MatrixOrder

def evalBits (g : ℕ → Bool) (start : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => evalBits g start n + Nat.shiftLeft (cond (g (start + n)) 1 0) n

def uRotSrc (s4 j : ℕ) : ℕ := (j + 22 - s4) % 22

def uRotBit (u s4 j : ℕ) : Bool :=
  u.testBit (uRotSrc s4 j)

def sq9Val (d9 : ℕ) : ℕ :=
  evalBits (fun k => (sq9Words.getD k 0).testBit d9) 0 9

def d9Val (u s4 : ℕ) : ℕ :=
  let raw9 := evalBits (uRotBit u s4) 6 9
  cond (uRotBit u s4 15) raw9 (511 - raw9)

def curvTerm (lv c_idx div_pow mask sq9 : ℕ) : ℕ :=
  let sl := sq9 / div_pow
  cond (lv.testBit c_idx) (mask - sl) sl

def curvFromSq9 (lv sq9 : ℕ) : ℕ :=
  2 * sq9 +
  curvTerm lv 0 128 3 sq9 +
  curvTerm lv 1 64 7 sq9 +
  curvTerm lv 2 32 15 sq9 +
  curvTerm lv 3 16 31 sq9 +
  curvTerm lv 4 8 63 sq9 +
  curvTerm lv 5 4 127 sq9 +
  curvTerm lv 6 2 255 sq9 +
  curvTerm lv 7 1 511 sq9

def curvVal27 (lv d9 : ℕ) : ℕ :=
  curvFromSq9 lv (sq9Val d9)

def slopeTermPos27 (kv bit_idx b_min len mul_pow s4 u : ℕ) : ℕ :=
  cond (kv.testBit bit_idx) (evalBits (uRotBit u s4) b_min len * mul_pow) 0

def slopeTermNeg27 (kv bit_idx b_min len mul_pow s4 u : ℕ) : ℕ :=
  cond (!kv.testBit bit_idx) (evalBits (uRotBit u s4) b_min len * mul_pow) 0

def posSlope27 (kv s4 u : ℕ) : ℕ :=
  4 * evalBits (uRotBit u s4) 0 16 +
  slopeTermPos27 kv 0 13 3 1 s4 u +
  slopeTermPos27 kv 1 12 4 1 s4 u +
  slopeTermPos27 kv 2 11 5 1 s4 u +
  slopeTermPos27 kv 3 10 6 1 s4 u +
  slopeTermPos27 kv 4 9 7 1 s4 u +
  slopeTermPos27 kv 5 8 8 1 s4 u +
  slopeTermPos27 kv 6 7 9 1 s4 u +
  slopeTermPos27 kv 7 6 10 1 s4 u +
  slopeTermPos27 kv 8 5 11 1 s4 u +
  slopeTermPos27 kv 9 4 12 1 s4 u +
  slopeTermPos27 kv 10 3 13 1 s4 u +
  slopeTermPos27 kv 11 2 14 1 s4 u +
  slopeTermPos27 kv 12 1 15 1 s4 u +
  slopeTermPos27 kv 13 0 16 1 s4 u +
  slopeTermPos27 kv 14 0 16 2 s4 u

def negSlope27 (kv s4 u : ℕ) : ℕ :=
  slopeTermNeg27 kv 0 13 3 1 s4 u +
  slopeTermNeg27 kv 1 12 4 1 s4 u +
  slopeTermNeg27 kv 2 11 5 1 s4 u +
  slopeTermNeg27 kv 3 10 6 1 s4 u +
  slopeTermNeg27 kv 4 9 7 1 s4 u +
  slopeTermNeg27 kv 5 8 8 1 s4 u +
  slopeTermNeg27 kv 6 7 9 1 s4 u +
  slopeTermNeg27 kv 7 6 10 1 s4 u +
  slopeTermNeg27 kv 8 5 11 1 s4 u +
  slopeTermNeg27 kv 9 4 12 1 s4 u +
  slopeTermNeg27 kv 10 3 13 1 s4 u +
  slopeTermNeg27 kv 11 2 14 1 s4 u +
  slopeTermNeg27 kv 12 1 15 1 s4 u +
  slopeTermNeg27 kv 13 0 16 1 s4 u +
  slopeTermNeg27 kv 14 0 16 2 s4 u
def zPos27 (b_base kv lv s4 u : ℕ) : ℕ :=
  16 * u + b_base + posSlope27 kv s4 u + curvVal27 lv (d9Val u s4)

def zNeg27 (kv s4 u : ℕ) : ℕ :=
  1024 + negSlope27 kv s4 u

def diff27 (b_base kv lv s4 u : ℕ) : ℕ :=
  zPos27 b_base kv lv s4 u - zNeg27 kv s4 u

def deltaPos25 (b_base kv lv s4 u : ℕ) : ℕ :=
  diff27 b_base kv lv s4 u / 16


def slopeTermConst27 (kv bit_idx len sh_out : ℕ) : ℕ :=
  cond (!kv.testBit bit_idx) ((2 ^ len - 1) * 2 ^ sh_out) 0

def slopeConst27 (kv : ℕ) : ℕ :=
  slopeTermConst27 kv 0 3 0 +
  slopeTermConst27 kv 1 4 0 +
  slopeTermConst27 kv 2 5 0 +
  slopeTermConst27 kv 3 6 0 +
  slopeTermConst27 kv 4 7 0 +
  slopeTermConst27 kv 5 8 0 +
  slopeTermConst27 kv 6 9 0 +
  slopeTermConst27 kv 7 10 0 +
  slopeTermConst27 kv 8 11 0 +
  slopeTermConst27 kv 9 12 0 +
  slopeTermConst27 kv 10 13 0 +
  slopeTermConst27 kv 11 14 0 +
  slopeTermConst27 kv 12 15 0 +
  slopeTermConst27 kv 13 16 0 +
  slopeTermConst27 kv 14 16 1


end QuantumComputation.Specs.ArcsinImpl
