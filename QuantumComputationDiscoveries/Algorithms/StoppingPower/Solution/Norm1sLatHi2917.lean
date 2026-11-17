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

public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.CanonQftHad128

@[expose] public section
set_option allowUnsafeReducibility true
set_option exponentiation.threshold 256

namespace QuantumComputation.Specs.StoppingPowerSolution
open SpecsAux

section Slot3Norm1s36LatticeHiT2917
local instance (priority := 1000000) instNeZeroTwoPow_Slot3Norm1s36LatticeHiT2917 (k : ℕ) :
    NeZero (2 ^ k) := ⟨(Nat.two_pow_pos k).ne'⟩

public section

/-
Exact `decide +kernel` octant chunk certificate `n1s_chunk_t29_17_hi` (shells k in 64..127)
for `Norm1sTier.t29_17`.
-/

namespace Slot3Norm1s36LatticeHiT2917

section ConfigSlot3Norm1s36LatticeHiT2917

set_option maxRecDepth 4096

open ModWrapCoarse8PureMomentum (max2Nat log2Fast127)
open Slot3Norm1s36LatticeBase
  (n1sCbv n1sCbv_eq n1sCbv2 n1sCbv2_eq n1sShiftIdx n1sNatSumFast n1sHoistedTerm
    n1sDispatchShell n1sMax2Fast_eq_max2Nat n1sOctCPosMaxLit n1sOctCPosMax n1sOctBPosBM1
    n1sOctBPosP11 n1sOctBPosP10 n1sOctBPosP01 n1sOctBPosP00 n1sOctBPosB01 n1sOctBStep
    n1sOctShellK1 n1sOctShellK0 n1sOctShellBody n1sOctShellFast n1sChunkHi)

/-- Fast 8-point alias maximum using `max2Nat` (`8` lookup tree walks per interior point). -/
def hiT2917CPosMaxLit (callS : ℕ → ℕ) (p00 p01 p10 p11 c0 c1 : ℕ) : ℕ :=
  max2Nat
    (max2Nat (max2Nat (callS (Nat.add p00 c0)) (callS (Nat.add p00 c1)))
      (max2Nat (callS (Nat.add p01 c0)) (callS (Nat.add p01 c1))))
    (max2Nat (max2Nat (callS (Nat.add p10 c0)) (callS (Nat.add p10 c1)))
      (max2Nat (callS (Nat.add p11 c0)) (callS (Nat.add p11 c1))))

/-- Unweighted 8-point alias maximum for `c = j + 1 > 0` sharing `(c0, c1)` pointers. -/
def hiT2917CPosMax (callS : ℕ → ℕ) (p00 p01 p10 p11 j : ℕ) : ℕ :=
  hiT2917CPosMaxLit callS p00 p01 p10 p11
    (Nat.mul (Nat.add j 1) (Nat.add j 1)) (Nat.mul (Nat.sub 254 j) (Nat.sub 254 j))

/-- Stage 5 of `hiT2917BStep`: evaluates `c = 0..b` sum once `bm1 = b - 1` is a `LitVal`. -/
def hiT2917BPosBM1 (callS : ℕ → ℕ) (wVal p00 p01 p10 p11 bm1 : ℕ) : ℕ := Nat.mul
    (Nat.mul 8 wVal) (Nat.add (Nat.add (hiT2917CPosMax callS p00 p01 p10 p11 bm1) (max2Nat
    (max2Nat (callS p00) (callS p01)) (max2Nat (callS p10) (callS p11)))) (Nat.mul 2
    (n1sNatSumFast bm1 (hiT2917CPosMax callS p00 p01 p10 p11))))

/-- Stage 4 of `hiT2917BStep`: binds `bm1 = b - 1` once `p00..p11` are `LitVal`s. -/
def hiT2917BPosP11 (callS : ℕ → ℕ) (wVal b p00 p01 p10 p11 : ℕ) : ℕ :=
  n1sCbv (hiT2917BPosBM1 callS wVal p00 p01 p10 p11) (Nat.sub b 1)

/-- Stage 3 of `hiT2917BStep`: binds `p11 = k1 + b1`. -/
def hiT2917BPosP10 (callS : ℕ → ℕ) (wVal k1 b1 b p00 p01 p10 : ℕ) : ℕ :=
  n1sCbv (hiT2917BPosP11 callS wVal b p00 p01 p10) (Nat.add k1 b1)

/-- Stage 2 of `hiT2917BStep`: binds `p10 = k1 + b0`. -/
def hiT2917BPosP01 (callS : ℕ → ℕ) (wVal k1 b0 b1 b p00 p01 : ℕ) : ℕ :=
  n1sCbv (hiT2917BPosP10 callS wVal k1 b1 b p00 p01) (Nat.add k1 b0)

/-- Stage 1 of `hiT2917BStep`: binds `p01 = k0 + b1`. -/
def hiT2917BPosP00 (callS : ℕ → ℕ) (wVal k0 k1 b0 b1 b p00 : ℕ) : ℕ :=
  n1sCbv (hiT2917BPosP01 callS wVal k1 b0 b1 b p00) (Nat.add k0 b1)

/-- Stage 0 of `hiT2917BStep`: binds `p00 = k0 + b0` once `(b0, b1)` are `LitVal`s. -/
def hiT2917BPosB01 (callS : ℕ → ℕ) (wVal k0 k1 b b0 b1 : ℕ) : ℕ :=
  n1sCbv (hiT2917BPosP00 callS wVal k0 k1 b0 b1 b) (Nat.add k0 b0)

/-- Outer `b`-step summand for `0 ≤ b < k` using `hiT2917BPosB01`. -/
def hiT2917BStep (callS : ℕ → ℕ) (wVal k0 k1 b : ℕ) : ℕ :=
  bif Nat.beq b 0 then Nat.mul (Nat.mul 2 (max2Nat (callS k0) (callS k1))) wVal
  else
    n1sCbv2 (hiT2917BPosB01 callS wVal k0 k1 b)
      (Nat.mul b b) (Nat.mul (Nat.sub 255 b) (Nat.sub 255 b))

/-- Stage 2 of `hiT2917ShellBody`: evaluates shell `k` once `(k0, k1)` are `LitVal`s. -/
def hiT2917ShellK1 (k : ℕ) (callS : ℕ → ℕ) (wVal k0 k1 : ℕ) : ℕ :=
  Nat.add
    (Nat.add (n1sHoistedTerm callS wVal k0 k1 k k)
      (Nat.mul 3 (n1sNatSumFast k (n1sHoistedTerm callS wVal k0 k1 k))))
    (Nat.mul 3 (n1sNatSumFast k (hiT2917BStep callS wVal k0 k1)))

/-- Stage 1 of `hiT2917ShellBody`: binds `k1 = (255 - k)^2`. -/
def hiT2917ShellK0 (k : ℕ) (callS : ℕ → ℕ) (wVal k0 : ℕ) : ℕ :=
  n1sCbv (hiT2917ShellK1 k callS wVal k0) (Nat.mul (Nat.sub 255 k) (Nat.sub 255 k))

/-- Flat shell-`k` body binding `(k0, k1)` once per shell. -/
def hiT2917ShellBody (k : ℕ) (callS : ℕ → ℕ) (wVal : ℕ) : ℕ :=
  n1sCbv (hiT2917ShellK0 k callS wVal) (Nat.mul k k)

/-- Hoisted shell-`k` evaluator for `Norm1sTier.t29_17`. -/
def hiT2917ShellFast (k : ℕ) : ℕ :=
  bif Nat.beq k 0 then 0 else n1sDispatchShell .t29_17 (log2Fast127 k) (hiT2917ShellBody k)

/-- Fast octant chunk evaluator (shells k in 64..127) for `Norm1sTier.t29_17`. -/
def hiT2917Chunk : ℕ := n1sNatSumFast 64 (n1sShiftIdx 64 hiT2917ShellFast)

set_option maxHeartbeats 400000 in
-- Octant chunk certificate evaluation over shells 64..127.
theorem n1s_chunk_t29_17_hi : Nat.beq (n1sChunkHi .t29_17) 7622735330 = true := by
  have hEq : hiT2917Chunk = n1sChunkHi .t29_17 := by
    have hCPos : hiT2917CPosMax = n1sOctCPosMax := by
      funext callS p00 p01 p10 p11 j
      simp only [hiT2917CPosMax, n1sOctCPosMax, hiT2917CPosMaxLit, n1sOctCPosMaxLit,
        n1sMax2Fast_eq_max2Nat]
    have hBStep : hiT2917BStep = n1sOctBStep := by
      funext callS wVal k0 k1 b
      simp only [n1sCbv2_eq, n1sCbv_eq, hiT2917BStep, n1sOctBStep, hiT2917BPosB01, n1sOctBPosB01,
        hiT2917BPosP00, n1sOctBPosP00, hiT2917BPosP01, n1sOctBPosP01, hiT2917BPosP10, n1sOctBPosP10,
        hiT2917BPosP11, n1sOctBPosP11, hiT2917BPosBM1, n1sOctBPosBM1, hCPos]
    have hBody : hiT2917ShellBody = n1sOctShellBody := by
      funext k callS wVal
      simp only [n1sCbv_eq, hiT2917ShellBody, n1sOctShellBody, hiT2917ShellK0, n1sOctShellK0,
        hiT2917ShellK1, n1sOctShellK1, hBStep]
    have hShell : hiT2917ShellFast = n1sOctShellFast .t29_17 := by
      funext k
      simp only [hiT2917ShellFast, n1sOctShellFast, hBody]
    simp only [hiT2917Chunk, n1sChunkHi, hShell]
  rw [← hEq]
  decide +kernel

set_option maxRecDepth 2000

end ConfigSlot3Norm1s36LatticeHiT2917

end Slot3Norm1s36LatticeHiT2917
end
end Slot3Norm1s36LatticeHiT2917

end QuantumComputation.Specs.StoppingPowerSolution
