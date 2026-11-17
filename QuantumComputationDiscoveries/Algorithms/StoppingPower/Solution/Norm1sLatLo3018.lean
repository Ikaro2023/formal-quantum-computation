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

namespace QuantumComputation.Specs.StoppingPowerSolution

noncomputable section Gqsp1_Slot3T3018LoA

section
namespace Gqsp1_Slot3T3018LoA
set_option maxRecDepth 4096
open ModWrapCoarse8PureMomentum (max2Nat log2Fast127 natSum_add_split)
open Slot3Norm1s36LatticeBase
  (n1sCbv n1sCbv2 n1sShiftIdx n1sShiftIdx_eq n1sNatSumFast n1sNatSumFast_eq n1sHoistedTerm
   n1sDispatchShell n1sMax2Fast_eq_max2Nat n1sOctCPosMaxLit n1sOctCPosMax n1sOctBPosBM1
   n1sOctBPosP11 n1sOctBPosP10 n1sOctBPosP01 n1sOctBPosP00 n1sOctBPosB01 n1sOctBStep
   n1sOctShellK1 n1sOctShellK0 n1sOctShellBody n1sOctShellFast)
/-- Fast 8-point alias maximum using `max2Nat`. -/
def loT3018CPosMaxLit (callS : ℕ → ℕ) (p00 p01 p10 p11 c0 c1 : ℕ) : ℕ := max2Nat (max2Nat
    (max2Nat (callS (Nat.add p00 c0)) (callS (Nat.add p00 c1))) (max2Nat (callS (Nat.add p01
    c0)) (callS (Nat.add p01 c1)))) (max2Nat (max2Nat (callS (Nat.add p10 c0)) (callS (Nat.add
    p10 c1))) (max2Nat (callS (Nat.add p11 c0)) (callS (Nat.add p11 c1))))
/-- Unweighted 8-point alias maximum for `c = j + 1 > 0`. -/
def loT3018CPosMax (callS : ℕ → ℕ) (p00 p01 p10 p11 j : ℕ) : ℕ := loT3018CPosMaxLit callS p00
    p01 p10 p11 (Nat.mul (Nat.add j 1) (Nat.add j 1))
    (Nat.mul (Nat.sub 254 j) (Nat.sub 254 j))
/-- Stage 5 of `loT3018BStep`. -/
def loT3018BPosBM1 (callS : ℕ → ℕ) (wVal p00 p01 p10 p11 bm1 : ℕ) : ℕ := Nat.mul
    (Nat.mul 8 wVal) (Nat.add (Nat.add (loT3018CPosMax callS p00 p01 p10 p11 bm1) (max2Nat
    (max2Nat (callS p00) (callS p01)) (max2Nat (callS p10) (callS p11)))) (Nat.mul 2
    (n1sNatSumFast bm1 (loT3018CPosMax callS p00 p01 p10 p11))))
/-- Stage 4 of `loT3018BStep`. -/
def loT3018BPosP11 (callS : ℕ → ℕ) (wVal b p00 p01 p10 p11 : ℕ) : ℕ :=
  n1sCbv (loT3018BPosBM1 callS wVal p00 p01 p10 p11) (Nat.sub b 1)
/-- Stage 3 of `loT3018BStep`. -/
def loT3018BPosP10 (callS : ℕ → ℕ) (wVal k1 b1 b p00 p01 p10 : ℕ) : ℕ :=
  n1sCbv (loT3018BPosP11 callS wVal b p00 p01 p10) (Nat.add k1 b1)
/-- Stage 2 of `loT3018BStep`. -/
def loT3018BPosP01 (callS : ℕ → ℕ) (wVal k1 b0 b1 b p00 p01 : ℕ) : ℕ :=
  n1sCbv (loT3018BPosP10 callS wVal k1 b1 b p00 p01) (Nat.add k1 b0)
/-- Stage 1 of `loT3018BStep`. -/
def loT3018BPosP00 (callS : ℕ → ℕ) (wVal k0 k1 b0 b1 b p00 : ℕ) : ℕ :=
  n1sCbv (loT3018BPosP01 callS wVal k1 b0 b1 b p00) (Nat.add k0 b1)
/-- Stage 0 of `loT3018BStep`. -/
def loT3018BPosB01 (callS : ℕ → ℕ) (wVal k0 k1 b b0 b1 : ℕ) : ℕ :=
  n1sCbv (loT3018BPosP00 callS wVal k0 k1 b0 b1 b) (Nat.add k0 b0)
/-- Outer `b`-step summand for `0 ≤ b < k`. -/
def loT3018BStep (callS : ℕ → ℕ) (wVal k0 k1 b : ℕ) : ℕ := bif Nat.beq b 0 then Nat.mul
    (Nat.mul 2 (max2Nat (callS k0) (callS k1))) wVal else n1sCbv2
    (loT3018BPosB01 callS wVal k0 k1 b) (Nat.mul b b)
    (Nat.mul (Nat.sub 255 b) (Nat.sub 255 b))
/-- Stage 2 of `loT3018ShellBody`. -/
def loT3018ShellK1 (k : ℕ) (callS : ℕ → ℕ) (wVal k0 k1 : ℕ) : ℕ := Nat.add (Nat.add
    (n1sHoistedTerm callS wVal k0 k1 k k) (Nat.mul 3 (n1sNatSumFast k (n1sHoistedTerm callS
    wVal k0 k1 k)))) (Nat.mul 3 (n1sNatSumFast k (loT3018BStep callS wVal k0 k1)))
/-- Stage 1 of `loT3018ShellBody`. -/
def loT3018ShellK0 (k : ℕ) (callS : ℕ → ℕ) (wVal k0 : ℕ) : ℕ :=
  n1sCbv (loT3018ShellK1 k callS wVal k0) (Nat.mul (Nat.sub 255 k) (Nat.sub 255 k))
/-- Flat shell-`k` body binding `(k0, k1)` once per shell. -/
def loT3018ShellBody (k : ℕ) (callS : ℕ → ℕ) (wVal : ℕ) : ℕ :=
  n1sCbv (loT3018ShellK0 k callS wVal) (Nat.mul k k)
/-- Hoisted shell-`k` evaluator for `Norm1sTier.t30_18`. -/
def loT3018ShellFast (k : ℕ) : ℕ := bif Nat.beq k 0 then 0 else n1sDispatchShell .t30_18
    (log2Fast127 k) (loT3018ShellBody k)
theorem loT3018ShellFast_eq : loT3018ShellFast = n1sOctShellFast .t30_18 := by
  have h1 : loT3018CPosMaxLit = n1sOctCPosMaxLit := by
    funext callS p00 p01 p10 p11 c0 c1
    unfold loT3018CPosMaxLit n1sOctCPosMaxLit
    simp only [n1sMax2Fast_eq_max2Nat]
  have h2 : loT3018CPosMax = n1sOctCPosMax := by
    funext callS p00 p01 p10 p11 j; unfold loT3018CPosMax n1sOctCPosMax; rw [h1]
  have h3 : loT3018BPosBM1 = n1sOctBPosBM1 := by
    funext callS wVal p00 p01 p10 p11 bm1; unfold loT3018BPosBM1 n1sOctBPosBM1; rw [h2]
  have h4 : loT3018BPosP11 = n1sOctBPosP11 := by
    funext callS wVal b p00 p01 p10 p11; unfold loT3018BPosP11 n1sOctBPosP11; rw [h3]
  have h5 : loT3018BPosP10 = n1sOctBPosP10 := by
    funext callS wVal k1 b1 b p00 p01 p10; unfold loT3018BPosP10 n1sOctBPosP10; rw [h4]
  have h6 : loT3018BPosP01 = n1sOctBPosP01 := by
    funext callS wVal k1 b0 b1 b p00 p01; unfold loT3018BPosP01 n1sOctBPosP01; rw [h5]
  have h7 : loT3018BPosP00 = n1sOctBPosP00 := by
    funext callS wVal k0 k1 b0 b1 b p00; unfold loT3018BPosP00 n1sOctBPosP00; rw [h6]
  have h8 : loT3018BPosB01 = n1sOctBPosB01 := by
    funext callS wVal k0 k1 b b0 b1; unfold loT3018BPosB01 n1sOctBPosB01; rw [h7]
  have h9 : loT3018BStep = n1sOctBStep := by
    funext callS wVal k0 k1 b; unfold loT3018BStep n1sOctBStep; rw [h8]
  have h10 : loT3018ShellK1 = n1sOctShellK1 := by
    funext k callS wVal k0 k1; unfold loT3018ShellK1 n1sOctShellK1; rw [h9]
  have h11 : loT3018ShellK0 = n1sOctShellK0 := by
    funext k callS wVal k0; unfold loT3018ShellK0 n1sOctShellK0; rw [h10]
  have h12 : loT3018ShellBody = n1sOctShellBody := by
    funext k callS wVal; unfold loT3018ShellBody n1sOctShellBody; rw [h11]
  funext k; unfold loT3018ShellFast n1sOctShellFast; rw [h12]
theorem n1sShiftIdx_zero (g : ℕ → ℕ) : n1sShiftIdx 0 g = g := by
  rw [n1sShiftIdx_eq]; funext j; rw [Nat.zero_add]
theorem n1sShiftIdx_shift (c1 c2 : ℕ) (g : ℕ → ℕ) :
    (fun j ↦ g (c1 + (c2 + j))) = n1sShiftIdx (c1 + c2) g := by
  rw [n1sShiftIdx_eq]; funext j; rw [Nat.add_assoc]
theorem n1sNatSumFast_add_split (c a b : ℕ) (g : ℕ → ℕ) :
    n1sNatSumFast (a + b) (n1sShiftIdx c g) =
      n1sNatSumFast a (n1sShiftIdx c g) + n1sNatSumFast b (n1sShiftIdx (c + a) g) := by
  rw [n1sNatSumFast_eq, n1sNatSumFast_eq, n1sNatSumFast_eq,
    n1sShiftIdx_eq c g, natSum_add_split a b, ← n1sShiftIdx_shift c a g]
theorem loT3018_0_31 :
    Nat.beq (n1sNatSumFast 32 loT3018ShellFast) 2732327104 = true := by decide +kernel
end Gqsp1_Slot3T3018LoA
end
end Gqsp1_Slot3T3018LoA

end QuantumComputation.Specs.StoppingPowerSolution
end
