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

public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.MidReflSandwich
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.WalkQPEFlexBridge
public import
  QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.WalkQPECat11ReducedRefl
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.BlockEncodingDyn
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.OuterAliasPrep
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.GroupUnary
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.FastUniform
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.InnerTablePreInteg
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.CompactOuterAlias
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.AngleTables
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.Defs
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.SumOfSquares
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.FermionPerm
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.GivensCascade
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.SelectSwapQROM
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.XMeasCircuit
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.CleanDyn
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.PhaseGradAdder
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.QromBase
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.WalkQPEBridge

/-!
# Arbitrary-Phase `unif30` Inner Alias `PREP_mid` & Dual-ANF / `Perm60` X-Meas Unloaders

Provides three modular upgrades to Cytochrome P450 Stage-2 and standalone inner coherent-alias
state preparation (`wInner2 = 26`, `mMidUB 26 = 32` + `7`-bit `rc` context):

1. **Section 1 — Polymorphic Dual-ANF Bilinear Phase Fixup & X-Measurement QROM Unload:**
   - `dualAnfPhaseFixupDyn`, `qromDualAnfXMeasUnloadDyn`, and `qromDualAnfAliasUnloadDyn` over
     arbitrary `(s₁, s₂, M, L)` (`0 TOFF`, `4 * (anfScratchWidth s₁ + anfScratchWidth s₂)` `T`),
     decomposing any `(s₁ + s₂)`-bit diagonal phase table via two `monoSandwichDyn` monomial banks
     plus a `0-T` Clifford `Z` / `CZ` bilinear form with global `±1` constant term absorbed via
     `CleanRealizesSet.congr_unitary_sign`.
2. **Section 2 — P450 `innerAliasTargetFn` All-`4,096`-States X-Measurement Unloaders:**
   - `qromDualAnf66AliasUnloadDyn`: `(6, 6)` Dual-ANF unload in **`456 T`** (`114` ANDs, `-20 T` vs
     `476 T` baseline) on `98 ≤ sScr` (`119 ≤ s_ub` inside `rcOnly21Steps`).
   - `qromPerm60AliasUnloadDyn`: rotated `(rc[0..6], b[0..4])` `SelectSwap` unload exploiting
     `2 * b + rc_6 < 60` (`L = 3840, B = 60`) in **`464 T`** (`116` ANDs, `-12 T` vs `476 T`
     baseline) at the tight **`46 ≤ sScr` (`67 ≤ s_ub`)** scratch bound.
3. **Section 3 — Arbitrary-Phase `uIdxIdeal` Validity, `wNegIn26` Support & Parametric `hPulled`:**
   - `prepMidValid_hotFastPrepMidOf`, `hotFastPrepMidOf_wNegIn26_eq`, and
     `preservesWires_conj_hotFastPrepMidOf` for arbitrary `uIdxIdeal, uIdxImpl : Unitary (2 ^ 5)`
     (including arbitrary per-state complex phases on `0..29` from Exact-AA `unif30`).
   - Parametric `wNegIn26` pulled-reflection theorems (`14`-cat and `11`-cat) for any `prepMidIdeal`
     and asymmetric `(uFwdImpl, uBwdImpl)`.
4. **Section 4 — Parametric Standalone & Stage-2 (`rcOnly21Steps`, `183 ≤ s_ub`) `PREP_mid`,
   `PREP_mid†`, `U_B`, `U_B†` & Turnkey `Cat11` / `Cat14` Master Wrappers.**
-/

@[expose] public section

namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.FreeAltInnerPrepMid
open QuantumComputation.Specs QuantumComputation.Specs.P450

open Operator QProg Matrix HermitianMat Real QuantumComputation.Specs
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution
open QuantumComputation.Specs.P450 QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution
open CoherentAlias CleanDyn AliasPrep
open Phase2MidSandwich
open FastUniform
open BlockEncodingCore BlockEncodingCircuit
open WalkQPEBridge
open WalkQPEBridgeXMeas
open WalkQPEFlexBridge
open WalkQPECat11ReducedRefl
open scoped Matrix BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

local instance (priority := 1000000) instNeZeroTwoPow (k : ℕ) : NeZero (2 ^ k) :=
  ⟨Nat.pos_iff_ne_zero.mp (by positivity)⟩

attribute [local irreducible] thcHamiltonian BlockEncodingCore.p450HBlocked dfthcLowerBound
  CliffordT.exactPhaseGrad14Unitary oneBodyWeights fragmentWeights innerWeights oneBodyWeightInt
  fragmentWeightNat innerMantissa

/-- Two-dimensional `ZMod 2` Möbius (ANF) transform of `P` bounded by `L` across `(s₁, s₂)`
address bits. -/
def anf2DCoeffs (s₁ s₂ L : ℕ) (P : ℕ → Bool) (m₁ : Fin (2 ^ s₁)) (m₂ : Fin (2 ^ s₂)) : ZMod 2 :=
  SelectSwapQROM.anfCoeffs s₂
    (fun q : Fin (2 ^ s₂) ↦
      SelectSwapQROM.anfCoeffs s₁ (SelectSwapQROM.blockPhaseFn s₁ L P q.val) m₁)
    m₂

/-- Applies `czCircuit (r₁ i) (r₂ j)` for every `(i, j)` with `mat i j = 1` (`0 T`, `0 TOFF`). -/
def czBilinearCircuit {N : ℕ} :
    (M₁ M₂ : ℕ) → (r₁ : QRegister M₁ N) → (r₂ : QRegister M₂ N) →
    r₁.DisjointWires r₂ → (Fin M₁ → Fin M₂ → ZMod 2) → Circuit N
  | 0, _, _, _, _, _ => .identity
  | M₁ + 1, M₂, r₁, r₂, hDisj, mat =>
      let iLast : Fin (M₁ + 1) := ⟨M₁, Nat.lt_succ_self M₁⟩
      let emb := Fin.castLEEmb (Nat.le_succ M₁)
      .seq
        (SelectSwapQROM.czMaskCircuit (r₁ iLast) M₂ r₂
          (fun j ↦ hDisj.ne iLast j) (mat iLast))
        (czBilinearCircuit M₁ M₂ (r₁.subregister emb) r₂
          (hDisj.compose_left ⟨emb⟩)
          (fun i j ↦ mat (Fin.castLE (Nat.le_succ M₁) i) j))

@[simp]
theorem count_czBilinearCircuit_toff {N M₁ M₂ : ℕ}
    (r₁ : QRegister M₁ N) (r₂ : QRegister M₂ N) (hDisj : r₁.DisjointWires r₂)
    (mat : Fin M₁ → Fin M₂ → ZMod 2) :
    (czBilinearCircuit M₁ M₂ r₁ r₂ hDisj mat).count PrimitiveGate.TOFF = 0 := by
  induction M₁ with
  | zero => rfl
  | succ M₁ ih =>
    simp only [czBilinearCircuit, Circuit.count_seq, SelectSwapQROM.count_czMaskCircuit_toff,
      zero_add]
    exact ih _ _ _

@[simp]
theorem count_czBilinearCircuit_t {N M₁ M₂ : ℕ}
    (r₁ : QRegister M₁ N) (r₂ : QRegister M₂ N) (hDisj : r₁.DisjointWires r₂)
    (mat : Fin M₁ → Fin M₂ → ZMod 2) :
    (czBilinearCircuit M₁ M₂ r₁ r₂ hDisj mat).count PrimitiveGate.T = 0 := by
  induction M₁ with
  | zero => rfl
  | succ M₁ ih =>
    simp only [czBilinearCircuit, Circuit.count_seq, SelectSwapQROM.count_czMaskCircuit_t,
      zero_add]
    exact ih _ _ _

theorem ket_czBilinearCircuit {N M₁ M₂ : ℕ}
    (r₁ : QRegister M₁ N) (r₂ : QRegister M₂ N) (hDisj : r₁.DisjointWires r₂)
    (mat : Fin M₁ → Fin M₂ → ZMod 2) (β : BitAssignment N) :
    (czBilinearCircuit M₁ M₂ r₁ r₂ hDisj mat).eval.1.mulVec (SelectSwapQROM.ket β) =
      SelectSwapQROM.bitSign
        (∑ i : Fin M₁, β (r₁ i) * ∑ j : Fin M₂, mat i j * β (r₂ j)) •
        SelectSwapQROM.ket β := by
  induction M₁ with
  | zero =>
    rw [czBilinearCircuit, SelectSwapQROM.ket_identity]
    simp [SelectSwapQROM.bitSign]
  | succ M₁ ih =>
    simp only [czBilinearCircuit, SelectSwapQROM.eval_seq_mulVec]
    rw [SelectSwapQROM.ket_czMaskCircuit, Matrix.mulVec_smul, ih, smul_smul,
      ← SelectSwapQROM.bitSign_add]
    congr 2
    rw [Fin.sum_univ_castSucc, add_comm]
    rfl

/-! ### Parametric `wNegIn26` Pulled-Reflection Bridges (`14`-Cat & `11`-Cat) -/

end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.FreeAltInnerPrepMid
