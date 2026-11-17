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

noncomputable section Gqsp1_Slot3T3018HiA

section
namespace Gqsp1_Slot3T3018HiA
set_option maxRecDepth 4096
open ModWrapCoarse8PureMomentum (max2Nat log2Fast127 natSum_add_split)
open Slot3Norm1s36LatticeBase (n1sCbv n1sCbv2 n1sShiftIdx n1sShiftIdx_eq
  n1sNatSumFast n1sNatSumFast_eq n1sHoistedTerm n1sDispatchShell n1sMax2Fast_eq_max2Nat
  n1sOctCPosMaxLit n1sOctCPosMax n1sOctBPosBM1 n1sOctBPosP11 n1sOctBPosP10 n1sOctBPosP01
  n1sOctBPosP00 n1sOctBPosB01 n1sOctBStep n1sOctShellK1 n1sOctShellK0 n1sOctShellBody
  n1sOctShellFast)
/-- Fast 8-point alias maximum using `max2Nat` (`8` lookup tree walks per interior point). -/
def hiT3018CPosMaxLit (callS : ℕ → ℕ) (p00 p01 p10 p11 c0 c1 : ℕ) : ℕ := max2Nat (max2Nat
    (max2Nat (callS (Nat.add p00 c0)) (callS (Nat.add p00 c1))) (max2Nat (callS (Nat.add p01
    c0)) (callS (Nat.add p01 c1)))) (max2Nat (max2Nat (callS (Nat.add p10 c0)) (callS (Nat.add
    p10 c1))) (max2Nat (callS (Nat.add p11 c0)) (callS (Nat.add p11 c1))))
/-- Unweighted 8-point alias maximum for `c = j + 1 > 0` sharing `(c0, c1)` pointers. -/
def hiT3018CPosMax (callS : ℕ → ℕ) (p00 p01 p10 p11 j : ℕ) : ℕ := hiT3018CPosMaxLit callS p00
    p01 p10 p11 (Nat.mul (Nat.add j 1) (Nat.add j 1))
    (Nat.mul (Nat.sub 254 j) (Nat.sub 254 j))
/-- Stage 5 of `hiT3018BStep`: evaluates `c = 0..b` sum once `bm1 = b - 1` is a `LitVal`. -/
def hiT3018BPosBM1 (callS : ℕ → ℕ) (wVal p00 p01 p10 p11 bm1 : ℕ) : ℕ := Nat.mul
    (Nat.mul 8 wVal) (Nat.add (Nat.add (hiT3018CPosMax callS p00 p01 p10 p11 bm1) (max2Nat
    (max2Nat (callS p00) (callS p01)) (max2Nat (callS p10) (callS p11)))) (Nat.mul 2
    (n1sNatSumFast bm1 (hiT3018CPosMax callS p00 p01 p10 p11))))
/-- Stage 4 of `hiT3018BStep`: binds `bm1 = b - 1` once `p00..p11` are `LitVal`s. -/
def hiT3018BPosP11 (callS : ℕ → ℕ) (wVal b p00 p01 p10 p11 : ℕ) : ℕ :=
  n1sCbv (hiT3018BPosBM1 callS wVal p00 p01 p10 p11) (Nat.sub b 1)
/-- Stage 3 of `hiT3018BStep`: binds `p11 = k1 + b1`. -/
def hiT3018BPosP10 (callS : ℕ → ℕ) (wVal k1 b1 b p00 p01 p10 : ℕ) : ℕ :=
  n1sCbv (hiT3018BPosP11 callS wVal b p00 p01 p10) (Nat.add k1 b1)
/-- Stage 2 of `hiT3018BStep`: binds `p10 = k1 + b0`. -/
def hiT3018BPosP01 (callS : ℕ → ℕ) (wVal k1 b0 b1 b p00 p01 : ℕ) : ℕ :=
  n1sCbv (hiT3018BPosP10 callS wVal k1 b1 b p00 p01) (Nat.add k1 b0)
/-- Stage 1 of `hiT3018BStep`: binds `p01 = k0 + b1`. -/
def hiT3018BPosP00 (callS : ℕ → ℕ) (wVal k0 k1 b0 b1 b p00 : ℕ) : ℕ :=
  n1sCbv (hiT3018BPosP01 callS wVal k1 b0 b1 b p00) (Nat.add k0 b1)
/-- Stage 0 of `hiT3018BStep`: binds `p00 = k0 + b0` once `(b0, b1)` are `LitVal`s. -/
def hiT3018BPosB01 (callS : ℕ → ℕ) (wVal k0 k1 b b0 b1 : ℕ) : ℕ :=
  n1sCbv (hiT3018BPosP00 callS wVal k0 k1 b0 b1 b) (Nat.add k0 b0)
/-- Outer `b`-step summand for `0 ≤ b < k` using `hiT3018BPosB01`. -/
def hiT3018BStep (callS : ℕ → ℕ) (wVal k0 k1 b : ℕ) : ℕ := bif Nat.beq b 0 then Nat.mul
    (Nat.mul 2 (max2Nat (callS k0) (callS k1))) wVal else n1sCbv2
    (hiT3018BPosB01 callS wVal k0 k1 b) (Nat.mul b b)
    (Nat.mul (Nat.sub 255 b) (Nat.sub 255 b))
/-- Stage 2 of `hiT3018ShellBody`: evaluates shell `k` once `(k0, k1)` are `LitVal`s. -/
def hiT3018ShellK1 (k : ℕ) (callS : ℕ → ℕ) (wVal k0 k1 : ℕ) : ℕ := Nat.add (Nat.add
    (n1sHoistedTerm callS wVal k0 k1 k k) (Nat.mul 3 (n1sNatSumFast k (n1sHoistedTerm callS
    wVal k0 k1 k)))) (Nat.mul 3 (n1sNatSumFast k (hiT3018BStep callS wVal k0 k1)))
/-- Stage 1 of `hiT3018ShellBody`: binds `k1 = (255 - k)^2`. -/
def hiT3018ShellK0 (k : ℕ) (callS : ℕ → ℕ) (wVal k0 : ℕ) : ℕ :=
  n1sCbv (hiT3018ShellK1 k callS wVal k0) (Nat.mul (Nat.sub 255 k) (Nat.sub 255 k))
/-- Flat shell-`k` body binding `(k0, k1)` once per shell. -/
def hiT3018ShellBody (k : ℕ) (callS : ℕ → ℕ) (wVal : ℕ) : ℕ :=
  n1sCbv (hiT3018ShellK0 k callS wVal) (Nat.mul k k)
/-- Hoisted shell-`k` evaluator for `Norm1sTier.t30_18`. -/
def hiT3018ShellFast (k : ℕ) : ℕ := bif Nat.beq k 0 then 0 else n1sDispatchShell .t30_18
    (log2Fast127 k) (hiT3018ShellBody k)
theorem hiT3018ShellFast_eq : hiT3018ShellFast = n1sOctShellFast .t30_18 := by
  have h1 : hiT3018CPosMaxLit = n1sOctCPosMaxLit := by
    funext callS p00 p01 p10 p11 c0 c1
    unfold hiT3018CPosMaxLit n1sOctCPosMaxLit
    simp only [n1sMax2Fast_eq_max2Nat]
  have h2 : hiT3018CPosMax = n1sOctCPosMax := by
    funext callS p00 p01 p10 p11 j; unfold hiT3018CPosMax n1sOctCPosMax; rw [h1]
  have h3 : hiT3018BPosBM1 = n1sOctBPosBM1 := by
    funext callS wVal p00 p01 p10 p11 bm1; unfold hiT3018BPosBM1 n1sOctBPosBM1; rw [h2]
  have h4 : hiT3018BPosP11 = n1sOctBPosP11 := by
    funext callS wVal b p00 p01 p10 p11; unfold hiT3018BPosP11 n1sOctBPosP11; rw [h3]
  have h5 : hiT3018BPosP10 = n1sOctBPosP10 := by
    funext callS wVal k1 b1 b p00 p01 p10; unfold hiT3018BPosP10 n1sOctBPosP10; rw [h4]
  have h6 : hiT3018BPosP01 = n1sOctBPosP01 := by
    funext callS wVal k1 b0 b1 b p00 p01; unfold hiT3018BPosP01 n1sOctBPosP01; rw [h5]
  have h7 : hiT3018BPosP00 = n1sOctBPosP00 := by
    funext callS wVal k0 k1 b0 b1 b p00; unfold hiT3018BPosP00 n1sOctBPosP00; rw [h6]
  have h8 : hiT3018BPosB01 = n1sOctBPosB01 := by
    funext callS wVal k0 k1 b b0 b1; unfold hiT3018BPosB01 n1sOctBPosB01; rw [h7]
  have h9 : hiT3018BStep = n1sOctBStep := by
    funext callS wVal k0 k1 b; unfold hiT3018BStep n1sOctBStep; rw [h8]
  have h10 : hiT3018ShellK1 = n1sOctShellK1 := by
    funext k callS wVal k0 k1; unfold hiT3018ShellK1 n1sOctShellK1; rw [h9]
  have h11 : hiT3018ShellK0 = n1sOctShellK0 := by
    funext k callS wVal k0; unfold hiT3018ShellK0 n1sOctShellK0; rw [h10]
  have h12 : hiT3018ShellBody = n1sOctShellBody := by
    funext k callS wVal; unfold hiT3018ShellBody n1sOctShellBody; rw [h11]
  funext k; unfold hiT3018ShellFast n1sOctShellFast; rw [h12]
theorem n1sShiftIdx_shift (c1 c2 : ℕ) (g : ℕ → ℕ) :
    (fun j ↦ g (c1 + (c2 + j))) = n1sShiftIdx (c1 + c2) g := by
  rw [n1sShiftIdx_eq]; funext j; rw [Nat.add_assoc]
theorem n1sNatSumFast_add_split (c a b : ℕ) (g : ℕ → ℕ) :
    n1sNatSumFast (a + b) (n1sShiftIdx c g) =
      n1sNatSumFast a (n1sShiftIdx c g) + n1sNatSumFast b (n1sShiftIdx (c + a) g) := by
  rw [n1sNatSumFast_eq, n1sNatSumFast_eq, n1sNatSumFast_eq,
    n1sShiftIdx_eq c g, natSum_add_split a b, ← n1sShiftIdx_shift c a g]
theorem t3018_hi_64_73 :
    Nat.beq (n1sNatSumFast 10 (n1sShiftIdx 64 hiT3018ShellFast)) 544197622 = true := by
      decide +kernel
theorem t3018_hi_74_81 :
    Nat.beq (n1sNatSumFast 8 (n1sShiftIdx 74 hiT3018ShellFast)) 559460226 = true := by
      decide +kernel
theorem t3018_hi_82_88 :
    Nat.beq (n1sNatSumFast 7 (n1sShiftIdx 82 hiT3018ShellFast)) 577280506 = true := by
      decide +kernel
theorem t3018_hi_89_94 :
    Nat.beq (n1sNatSumFast 6 (n1sShiftIdx 89 hiT3018ShellFast)) 565827982 = true := by
      decide +kernel
private theorem nat_beq_of_eq {a b : ℕ} (h : a = b) : Nat.beq a b = true := h ▸ Nat.beq_refl a
private theorem combine_64_94 (g : ℕ → ℕ) {v0 v1 v2 v3 tot : ℕ}
    (h0 : Nat.beq (n1sNatSumFast 10 (n1sShiftIdx 64 g)) v0 = true)
    (h1 : Nat.beq (n1sNatSumFast 8 (n1sShiftIdx 74 g)) v1 = true)
    (h2 : Nat.beq (n1sNatSumFast 7 (n1sShiftIdx 82 g)) v2 = true)
    (h3 : Nat.beq (n1sNatSumFast 6 (n1sShiftIdx 89 g)) v3 = true)
    (htot : ((v0 + v1) + v2) + v3 = tot) :
    Nat.beq (n1sNatSumFast 31 (n1sShiftIdx 64 g)) tot = true := by
  refine nat_beq_of_eq ?_
  have e0 := Nat.eq_of_beq_eq_true h0
  have e1 := Nat.eq_of_beq_eq_true h1
  have e2 := Nat.eq_of_beq_eq_true h2
  have e3 := Nat.eq_of_beq_eq_true h3
  have s18 : n1sNatSumFast 18 (n1sShiftIdx 64 g) = v0 + v1 := by
    rw [n1sNatSumFast_add_split 64 10 8 g, e0, e1]
  have s25 : n1sNatSumFast 25 (n1sShiftIdx 64 g) = (v0 + v1) + v2 := by
    rw [n1sNatSumFast_add_split 64 18 7 g, s18, e2]
  rw [n1sNatSumFast_add_split 64 25 6 g, s25, e3, htot]
theorem t3018_hi_64_94 : Nat.beq (n1sNatSumFast 31 (n1sShiftIdx 64 hiT3018ShellFast))
    2246766336 = true := combine_64_94 hiT3018ShellFast t3018_hi_64_73 t3018_hi_74_81
    t3018_hi_82_88 t3018_hi_89_94 rfl
end Gqsp1_Slot3T3018HiA
end
end Gqsp1_Slot3T3018HiA

end QuantumComputation.Specs.StoppingPowerSolution
end
