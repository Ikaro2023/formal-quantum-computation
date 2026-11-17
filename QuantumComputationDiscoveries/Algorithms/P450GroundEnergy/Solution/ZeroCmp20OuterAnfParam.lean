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

public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.ZeroCmp20OuterParam

/-!
# `W`-Split Primitive & `7 → 128` One-Hot Layout

Defines the `2-T`, `0-TOFF` `W`-split gate sequence (`wSplitPair4`) and the `7 → 128` one-hot
encoder/decoder register layout (`StepOneHotLayout`, `stepOneHotCtrlBits`, `stepScrLayout`) for
the `4 × 32` `W`-state barrel-shift and measurement-based uncomputation wrapper.

## References
- G. H. Low, R. King, D. W. Berry, Q. Han, A. E. DePrince III, A. White, R. Babbush, R. D. Somma,
  and N. C. Rubin, *Phys. Rev. X* **15**, 041016 (2025), DOI: `10.1103/PhysRevX.15.041016`.
- R. Babbush, C. Gidney, D. W. Berry, N. Wiebe, J. McClean, A. Paler, A. Fowler, and H. Neven,
  *Phys. Rev. X* **8**, 041015 (2018), DOI: `10.1103/PhysRevX.8.041015`.
- C. Gidney, *Quantum* **2**, 74 (2018), DOI: `10.22331/q-2018-06-18-74`.
- G. H. Low, V. Kliuchnikov, and L. Schaeffer, *Quantum* **8**, 1375 (2024),
  DOI: `10.22331/q-2024-06-17-1375`.
-/

set_option exponentiation.threshold 512

@[expose] public section

namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution
namespace CompactStepZeroCmp20OuterParam

open Operator QProg Matrix Circuit Real HermitianMat
open QuantumComputation.Specs QuantumComputation.Specs.P450
open BlockEncodingCore BlockEncodingCircuit CoherentAlias AliasPrep Phase2MidSandwich
open CompactBilinearPrep MidReflCtxRetain OptFactoredMag30AndCoin9 Cat11CompactPhase2Bridge
open ReordOuter13Bridge ZeroRcHotPrepMid21Fast OptXMeasUnload21 Tuned162ScheduledSympQrom21
open Tuned162StepSympAnfQrom21 OptStepSympAnfQrom21 OptU2Grover184PrepOut13
open TopIntegrationBridge MobiusOptSubcube163Walk CompactTuned162StepWalk
open CompactTuned162StepZeroCmp20 CompactZeroCmp20OuterParam
open scoped Matrix BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator Circuit.Notation

local instance (priority := 1000000) instNeZeroTwoPowStep (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩

/-- `2-T`, `0-TOFF` `W`-split primitive mapping `|0, 0⟩ ↦ |0, 0⟩` and
`|1, 0⟩ ↦ (|1, 0⟩ + |0, 1⟩) / √2` on distinct wires `(a, b)`. -/
def wSplitPair4 {n : ℕ} (a b : Wire n) (h : a ≠ b) : Circuit n :=
  Circuit.S b ;;ᶜ Circuit.H b ;;ᶜ Circuit.T b ;;ᶜ
  Circuit.CNOT a b h ;;ᶜ
  Circuit.Z b ;;ᶜ Circuit.S b ;;ᶜ Circuit.T b ;;ᶜ
  Circuit.H b ;;ᶜ Circuit.Z b ;;ᶜ Circuit.S b ;;ᶜ
  Circuit.CNOT b a h.symm

@[simp] theorem count_wSplitPair4_toff {n : ℕ} (a b : Wire n) (h : a ≠ b) :
    (wSplitPair4 a b h).count .TOFF = 0 := rfl

@[simp] theorem count_wSplitPair4_t {n : ℕ} (a b : Wire n) (h : a ≠ b) :
    (wSplitPair4 a b h).count .T = 2 := rfl

/-- Register layout for the `252-T`, `0-TOFF` `7 → 128` one-hot encoder and MBU decoder:
`rCtx` (`7`-wire binary address), `rHot` (`128`-wire one-hot target), and `qEnc` (`1` clean wire
reset to `|0⟩` before the inner body executes). -/
structure StepOneHotLayout (n : ℕ) where
  rCtx : QRegister 7 n
  rHot : QRegister 128 n
  qEnc : Wire n
  hCtxHot : rCtx.DisjointWires rHot
  hCtxEnc : ∀ i : Fin 7, rCtx i ≠ qEnc
  hHotEnc : ∀ g : Fin 128, rHot g ≠ qEnc

/-- Full-`128` `(7 + 128)`-bit control assignment extending `y : Fin 7 → Bool` with exact one-hot
indicator `i = finOfBits 7 y` on `Fin 128`. -/
def stepOneHotCtrlBits (y : Fin 7 → Bool) : Fin (7 + 128) → Bool :=
  fun idx ↦ if h : idx.val < 7 then y ⟨idx.val, h⟩
    else decide (idx.val - 7 = (finOfBits 7 y).val)

/-- Canonical `StepOneHotLayout` from `rCtx : QRegister 7 N` and `rScr : QRegister sScr N`
(`129 ≤ sScr`), placing `rHot = rScr.slice 0 128` and `qEnc = rScr 128`. -/
def stepScrLayout {N sScr : ℕ} (rCtx : QRegister 7 N) (rScr : QRegister sScr N)
    (hScr : 129 ≤ sScr) (hCtxScr : rCtx.DisjointWires rScr) : StepOneHotLayout N where
  rCtx := rCtx
  rHot := rScr.slice 0 128 (by omega)
  qEnc := rScr ⟨128, by omega⟩
  hCtxHot := hCtxScr.compose_right _
  hCtxEnc i := QRegister.disjoint_iff.mp hCtxScr i ⟨128, by omega⟩
  hHotEnc g := by
    rw [QRegister.slice_apply]
    exact rScr.wires.injective.ne (Fin.ne_of_val_ne (by dsimp; omega))

end CompactStepZeroCmp20OuterParam
end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution
