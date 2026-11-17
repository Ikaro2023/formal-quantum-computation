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
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.GroupUnary
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.FastCleanUnif184
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.BlockEncodingDyn
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.FastUniform
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.OuterAliasPrep
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.InnerTablePreInteg
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.CompactOuterAlias
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.CompactBilinearPrep
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.TopIntegrationBridge
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.ParamDyadicOuter13

/-!
# Berry `3`-AND Paired `Lac = 4` Forward & X-Measurement `wOuter = 13` Outer `PREP`

Constructs the `wOuter = 13` (`mOutUB 13 = 22` active qubits, `74 ≤ sScr` clean scratch qubits,
`0 TOFF`) outer state-preparation pair for the P450 block encoding:

- **Shared `46`-AND (`184 T`) `Lac = 4` base computation (`base46Prog`):**
  Computes the `46`-wire one-hot group indicator `rHot` on `x[2..7]` (`45` ANDs via `32`-way binary
  splitting plus `14` split steps at layer `5`) together with `wS01 = x₀ ∧ x₁` (`1` AND).
- **Berry `3`-AND-per-pair (`12 T`/pair) rank-2 `GF(2)` column evaluation (`pairedLac4Prog`):**
  Evaluates any `2 * P` output columns in `P` pairs using `3 * P` ANDs (`4` pairs = `12` ANDs =
  `48 T` for `alt : 8`, and `5` pairs = `15` ANDs = `60 T` for `keep : 10`) by exploiting the
  one-hot orthogonality of `rHot` (`U(rHot) * V(rHot) = (u ⊙ v)(rHot)`), so each masked product
  `(U(rHot) + b_U) * (V(rHot) + b_V)` produces two cross-terms at `1` `AND` gate.
- **Forward `PREP_out` (`dyadicBerryPrepOut13Dyn`, `554 T`, `0 TOFF`, `74 ≤ sScr`):**
  `152 T` `prepUniform184RotDyn` (borrowing `dyadicCmpWire` as the 9th Grover qubit, disjoint
  from `dyadicAltLoc`) + `0 T` `H` + `38 T` `pktCoinPrepDyn` + `184 T` `base46Prog` + `48 T`
  `alt:8` + `60 T` `keep:10` + `40 T` `pktMux10Dyn` + `32 T` `8`-bit `fredkinRegDyn`.
- **X-Measurement `PREP_out†` (`dyadicXMeasPrepOut13InvDyn`, `506 T`, `0 TOFF`, `74 ≤ sScr`):**
  `32 T` `8`-bit `fredkinRegDyn` + `0 T` `8`-wire `measureXResetAndBranch` on `dyadicAltLoc`
  resetting `dyadicAltLoc` (`kZeroOut = 8`, `-32 T` walk reflection reduction) and running a single
  `184 T` `base46Prog` sandwich per branch wrapping both the `0 T` `Z`/`CZ` phase fixup
  (`lac4PhaseFixCircuit`) and the `60 T` `keep:10` + `40 T` `pktMux10Dyn` comparator uncomputation
  + `38 T` `pktCoinUnprepDyn` + `0 T` `H` + `152 T` `unprepUniform184RotDyn`.
-/

@[expose] public section

namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.DyadicXMeasPrepOut13
open QuantumComputation.Specs QuantumComputation.Specs.P450

open Operator QProg Matrix HermitianMat Real QuantumComputation.Specs Solution
open QuantumComputation.Specs.P450 Solution CoherentAlias
open Solution.BlockEncodingCore Solution.BlockEncodingCircuit
open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator BigOperators Circuit.Notation

local instance (priority := 1000000) instNeZeroTwoPow (k : ℕ) : NeZero (2 ^ k) :=
  ⟨Nat.pos_iff_ne_zero.mp (by positivity)⟩

attribute [local irreducible] oneBodyWeights fragmentWeights Solution.DataArrays.oneBodyWeightsArr
  Solution.DataArrays.fragmentWeightsArr oneBodyWeightInt fragmentWeightNat

/-! ## Section 1: `46`-AND `base46Prog`, `3 * P`-AND `pairedLac4Prog`, and `lac4PhaseFixCircuit` -/

/-- Effective `46`-group index for `idx = x / 4`: equals `idx % 64` for `idx % 64 < 46` (which
covers all `x < 184`) and wraps to `idx % 32` for `46 ≤ idx % 64 < 64`. -/
def effGroup (idx : ℕ) : Fin 46 :=
  ⟨if idx % 64 < 46 then idx % 64 else idx % 32, by split_ifs <;> omega⟩

@[simp]
theorem effGroup_of_lt {idx : ℕ} (h : idx < 46) :
    effGroup idx = ⟨idx, h⟩ := by
  have hm : idx % 64 = idx := Nat.mod_eq_of_lt (by omega)
  ext
  simp only [effGroup, hm, h, ↓reduceIte]

/-- Single `keep` bit column `Fin 184 → Bool` for bit `j : Fin 10`. -/
def keepColBool (outerTable : Fin 184 → OuterWeights.AliasEntry 184) (j : Fin 10) (q : Fin 184) :
  Bool :=
  decide (basisBits 10 ⟨(outerTable q).keep % 1024, Nat.mod_lt _ (by decide)⟩ j = 1)

/-- `Lac = 4` coefficient `c = b₀₀` (`ZMod 2`) for group `i : Fin 46`. -/
def lac4MaskC (B : Fin 184 → Bool) (i : Fin 46) : ZMod 2 :=
  if B ⟨4 * i.val, by omega⟩ then 1 else 0

/-- `Lac = 4` coefficient `a = b₀₀ + b₁₀` (`ZMod 2`) for group `i : Fin 46`. -/
def lac4MaskA (B : Fin 184 → Bool) (i : Fin 46) : ZMod 2 :=
  (if B ⟨4 * i.val, by omega⟩ then 1 else 0) +
    (if B ⟨4 * i.val + 1, by omega⟩ then 1 else 0)

/-- `Lac = 4` coefficient `e = b₀₀ + b₀₁` (`ZMod 2`) for group `i : Fin 46`. -/
def lac4MaskE (B : Fin 184 → Bool) (i : Fin 46) : ZMod 2 :=
  (if B ⟨4 * i.val, by omega⟩ then 1 else 0) +
    (if B ⟨4 * i.val + 2, by omega⟩ then 1 else 0)

/-- `Lac = 4` coefficient `d = b₀₀ + b₁₀ + b₀₁ + b₁₁` (`ZMod 2`) for group `i : Fin 46`. -/
def lac4MaskD (B : Fin 184 → Bool) (i : Fin 46) : ZMod 2 :=
  (if B ⟨4 * i.val, by omega⟩ then 1 else 0) +
    (if B ⟨4 * i.val + 1, by omega⟩ then 1 else 0) +
    (if B ⟨4 * i.val + 2, by omega⟩ then 1 else 0) +
    (if B ⟨4 * i.val + 3, by omega⟩ then 1 else 0)

/-- Zero-AND CNOT fan-in XORing `∑_{i < n} mask i * rHot[i]` into `wDst`. -/
def hotXorProg {N : ℕ} (rHot : QRegister 46 N) (wDst : Wire N)
    (hne : ∀ i : Fin 46, rHot i ≠ wDst) (mask : Fin 46 → ZMod 2) :
    (n : ℕ) → n ≤ 46 → GroupUnary.RevCompute N
  | 0, _ => .id
  | n + 1, hn =>
      .seq (hotXorProg rHot wDst hne mask n (by omega))
        (if mask ⟨n, hn⟩ = 1 then .cnot (rHot ⟨n, hn⟩) wDst (hne ⟨n, hn⟩) else .id)

@[simp]
theorem numAnd_hotXorProg {N : ℕ} (rHot : QRegister 46 N) (wDst : Wire N)
    (hne : ∀ i : Fin 46, rHot i ≠ wDst) (mask : Fin 46 → ZMod 2) (n : ℕ) (hn : n ≤ 46) :
    (hotXorProg rHot wDst hne mask n hn).numAnd = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [hotXorProg, GroupUnary.RevCompute.numAnd, ih (by omega), zero_add]
      split_ifs <;> rfl

theorem usesOnly_hotXorProg {N : ℕ} (rHot : QRegister 46 N) (wDst : Wire N)
    (hne : ∀ i : Fin 46, rHot i ≠ wDst) (mask : Fin 46 → ZMod 2) {W : Set (Wire N)}
    (hHot : ∀ i : Fin 46, rHot i ∈ W) (hDst : wDst ∈ W) (n : ℕ) (hn : n ≤ 46) :
    (hotXorProg rHot wDst hne mask n hn).UsesOnly W := by
  induction n with
  | zero => trivial
  | succ n ih =>
      refine ⟨ih (by omega), ?_⟩
      split_ifs
      · exact ⟨hHot ⟨n, hn⟩, hDst⟩
      · trivial

/-- `1`-AND masked product evaluator computing `(∑ mU rHot + wBitU) * (∑ mV rHot + wBitV)` into
clean `wDst` using two shared clean temporary wires `wU, wV`, restoring `wU = 0` and `wV = 0`. -/
def andLin2Prog {N : ℕ} (rHot : QRegister 46 N) (wBitU wBitV wU wV wDst : Wire N)
    (hHotU : ∀ i : Fin 46, rHot i ≠ wU) (hHotV : ∀ i : Fin 46, rHot i ≠ wV)
    (hBitU_U : wBitU ≠ wU) (hBitV_V : wBitV ≠ wV)
    (hUV : wU ≠ wV) (hUDst : wU ≠ wDst) (hVDst : wV ≠ wDst)
    (mU mV : Fin 46 → ZMod 2) : GroupUnary.RevCompute N :=
  let prep : GroupUnary.RevCompute N :=
    .seq (hotXorProg rHot wU hHotU mU 46 le_rfl)
      (.seq (.cnot wBitU wU hBitU_U)
        (.seq (hotXorProg rHot wV hHotV mV 46 le_rfl)
          (.cnot wBitV wV hBitV_V)))
  let unprep : GroupUnary.RevCompute N :=
    .seq (.cnot wBitV wV hBitV_V)
      (.seq (hotXorProg rHot wV hHotV mV 46 le_rfl)
        (.seq (.cnot wBitU wU hBitU_U)
          (hotXorProg rHot wU hHotU mU 46 le_rfl)))
  .seq prep (.seq (.andGate wU wV wDst hUV hUDst hVDst) unprep)

@[simp]
theorem numAnd_andLin2Prog {N : ℕ} (rHot : QRegister 46 N) (wBitU wBitV wU wV wDst : Wire N)
    (hHotU : ∀ i : Fin 46, rHot i ≠ wU) (hHotV : ∀ i : Fin 46, rHot i ≠ wV)
    (hBitU_U : wBitU ≠ wU) (hBitV_V : wBitV ≠ wV)
    (hUV : wU ≠ wV) (hUDst : wU ≠ wDst) (hVDst : wV ≠ wDst)
    (mU mV : Fin 46 → ZMod 2) :
    (andLin2Prog rHot wBitU wBitV wU wV wDst hHotU hHotV hBitU_U hBitV_V
      hUV hUDst hVDst mU mV).numAnd = 1 := by
  simp [andLin2Prog, GroupUnary.RevCompute.numAnd]

theorem usesOnly_andLin2Prog {N : ℕ} (rHot : QRegister 46 N) (wBitU wBitV wU wV wDst : Wire N)
    (hHotU : ∀ i : Fin 46, rHot i ≠ wU) (hHotV : ∀ i : Fin 46, rHot i ≠ wV)
    (hBitU_U : wBitU ≠ wU) (hBitV_V : wBitV ≠ wV)
    (hUV : wU ≠ wV) (hUDst : wU ≠ wDst) (hVDst : wV ≠ wDst)
    (mU mV : Fin 46 → ZMod 2) {W : Set (Wire N)}
    (hHot : ∀ i : Fin 46, rHot i ∈ W)
    (hbU : wBitU ∈ W) (hbV : wBitV ∈ W) (hwU : wU ∈ W) (hwV : wV ∈ W) (hwDst : wDst ∈ W) :
    (andLin2Prog rHot wBitU wBitV wU wV wDst hHotU hHotV hBitU_U hBitV_V
      hUV hUDst hVDst mU mV).UsesOnly W :=
  ⟨⟨usesOnly_hotXorProg rHot wU hHotU mU hHot hwU 46 le_rfl,
      ⟨hbU, hwU⟩,
      usesOnly_hotXorProg rHot wV hHotV mV hHot hwV 46 le_rfl,
      ⟨hbV, hwV⟩⟩,
    ⟨⟨hwU, hwV, hwDst⟩,
      ⟨⟨hbV, hwV⟩,
        usesOnly_hotXorProg rHot wV hHotV mV hHot hwV 46 le_rfl,
        ⟨hbU, hwU⟩,
        usesOnly_hotXorProg rHot wU hHotU mU hHot hwU 46 le_rfl⟩⟩⟩

/-- Berry `3`-AND evaluator for a single pair of `Lac = 4` columns `(B₁, B₂)` into clean wires
`wSlot0, wSlot1, wAux` using shared clean linear-combination wires `wU, wV`. -/
def onePairLac4Prog {N : ℕ} (rHot : QRegister 46 N) (wX0 wX1 wS01 : Wire N)
    (wSlot0 wSlot1 wAux wU wV : Wire N)
    (hHotU : ∀ i : Fin 46, rHot i ≠ wU) (hHotV : ∀ i : Fin 46, rHot i ≠ wV)
    (hHot0 : ∀ i : Fin 46, rHot i ≠ wSlot0) (hHot1 : ∀ i : Fin 46, rHot i ≠ wSlot1)
    (hX0U : wX0 ≠ wU) (hX0V : wX0 ≠ wV) (hX1U : wX1 ≠ wU) (hX1V : wX1 ≠ wV)
    (hSU : wS01 ≠ wU) (hSV : wS01 ≠ wV)
    (hUV : wU ≠ wV)
    (hU0 : wU ≠ wSlot0) (hV0 : wV ≠ wSlot0)
    (hU1 : wU ≠ wSlot1) (hV1 : wV ≠ wSlot1)
    (hUA : wU ≠ wAux) (hVA : wV ≠ wAux)
    (hA0 : wAux ≠ wSlot0) (hA1 : wAux ≠ wSlot1)
    (B₁ B₂ : Fin 184 → Bool) : GroupUnary.RevCompute N :=
  let c₁ := lac4MaskC B₁; let a₁ := lac4MaskA B₁; let e₁ := lac4MaskE B₁; let d₁ := lac4MaskD B₁
  let c₂ := lac4MaskC B₂; let a₂ := lac4MaskA B₂; let e₂ := lac4MaskE B₂; let d₂ := lac4MaskD B₂
  let step1 := andLin2Prog rHot wX1 wX0 wU wV wSlot0 hHotU hHotV hX1U hX0V
    hUV hU0 hV0 (fun i ↦ a₁ i + a₂ i) e₁
  let step2 := andLin2Prog rHot wS01 wX1 wU wV wSlot1 hHotU hHotV hSU hX1V
    hUV hU1 hV1 e₂ (fun i ↦ d₁ i + d₂ i)
  let step3 := andLin2Prog rHot wX0 wS01 wU wV wAux hHotU hHotV hX0U hSV
    hUV hUA hVA d₁ a₂
  let c₁' : Fin 46 → ZMod 2 := fun i ↦ c₁ i + (a₁ i + a₂ i) * e₁ i + d₁ i * a₂ i
  let c₂' : Fin 46 → ZMod 2 := fun i ↦ c₂ i + e₂ i * (d₁ i + d₂ i) + d₁ i * a₂ i
  .seq step1
    (.seq step2
      (.seq step3
        (.seq (.cnot wAux wSlot0 hA0)
          (.seq (.cnot wAux wSlot1 hA1)
            (.seq (hotXorProg rHot wSlot0 hHot0 c₁' 46 le_rfl)
              (hotXorProg rHot wSlot1 hHot1 c₂' 46 le_rfl))))))

@[simp]
theorem numAnd_onePairLac4Prog {N : ℕ} (rHot : QRegister 46 N) (wX0 wX1 wS01 : Wire N)
    (wSlot0 wSlot1 wAux wU wV : Wire N)
    (hHotU : ∀ i : Fin 46, rHot i ≠ wU) (hHotV : ∀ i : Fin 46, rHot i ≠ wV)
    (hHot0 : ∀ i : Fin 46, rHot i ≠ wSlot0) (hHot1 : ∀ i : Fin 46, rHot i ≠ wSlot1)
    (hX0U : wX0 ≠ wU) (hX0V : wX0 ≠ wV) (hX1U : wX1 ≠ wU) (hX1V : wX1 ≠ wV)
    (hSU : wS01 ≠ wU) (hSV : wS01 ≠ wV)
    (hUV : wU ≠ wV)
    (hU0 : wU ≠ wSlot0) (hV0 : wV ≠ wSlot0)
    (hU1 : wU ≠ wSlot1) (hV1 : wV ≠ wSlot1)
    (hUA : wU ≠ wAux) (hVA : wV ≠ wAux)
    (hA0 : wAux ≠ wSlot0) (hA1 : wAux ≠ wSlot1)
    (B₁ B₂ : Fin 184 → Bool) :
    (onePairLac4Prog rHot wX0 wX1 wS01 wSlot0 wSlot1 wAux wU wV
      hHotU hHotV hHot0 hHot1 hX0U hX0V hX1U hX1V hSU hSV
      hUV hU0 hV0 hU1 hV1 hUA hVA hA0 hA1 B₁ B₂).numAnd = 3 := by
  simp [onePairLac4Prog, GroupUnary.RevCompute.numAnd]

theorem usesOnly_onePairLac4Prog {N : ℕ} (rHot : QRegister 46 N) (wX0 wX1 wS01 : Wire N)
    (wSlot0 wSlot1 wAux wU wV : Wire N)
    (hHotU : ∀ i : Fin 46, rHot i ≠ wU) (hHotV : ∀ i : Fin 46, rHot i ≠ wV)
    (hHot0 : ∀ i : Fin 46, rHot i ≠ wSlot0) (hHot1 : ∀ i : Fin 46, rHot i ≠ wSlot1)
    (hX0U : wX0 ≠ wU) (hX0V : wX0 ≠ wV) (hX1U : wX1 ≠ wU) (hX1V : wX1 ≠ wV)
    (hSU : wS01 ≠ wU) (hSV : wS01 ≠ wV)
    (hUV : wU ≠ wV)
    (hU0 : wU ≠ wSlot0) (hV0 : wV ≠ wSlot0)
    (hU1 : wU ≠ wSlot1) (hV1 : wV ≠ wSlot1)
    (hUA : wU ≠ wAux) (hVA : wV ≠ wAux)
    (hA0 : wAux ≠ wSlot0) (hA1 : wAux ≠ wSlot1)
    (B₁ B₂ : Fin 184 → Bool) {W : Set (Wire N)}
    (hHot : ∀ i : Fin 46, rHot i ∈ W)
    (hx0 : wX0 ∈ W) (hx1 : wX1 ∈ W) (hs : wS01 ∈ W)
    (hw0 : wSlot0 ∈ W) (hw1 : wSlot1 ∈ W) (hwa : wAux ∈ W) (hwu : wU ∈ W) (hwv : wV ∈ W) :
    (onePairLac4Prog rHot wX0 wX1 wS01 wSlot0 wSlot1 wAux wU wV
      hHotU hHotV hHot0 hHot1 hX0U hX0V hX1U hX1V hSU hSV
      hUV hU0 hV0 hU1 hV1 hUA hVA hA0 hA1 B₁ B₂).UsesOnly W :=
  ⟨usesOnly_andLin2Prog rHot wX1 wX0 wU wV wSlot0 hHotU hHotV hX1U hX0V
      hUV hU0 hV0 _ _ hHot hx1 hx0 hwu hwv hw0,
    usesOnly_andLin2Prog rHot wS01 wX1 wU wV wSlot1 hHotU hHotV hSU hX1V
      hUV hU1 hV1 _ _ hHot hs hx1 hwu hwv hw1,
    usesOnly_andLin2Prog rHot wX0 wS01 wU wV wAux hHotU hHotV hX0U hSV
      hUV hUA hVA _ _ hHot hx0 hs hwu hwv hwa,
    ⟨hwa, hw0⟩,
    ⟨hwa, hw1⟩,
    usesOnly_hotXorProg rHot wSlot0 hHot0 _ hHot hw0 46 le_rfl,
    usesOnly_hotXorProg rHot wSlot1 hHot1 _ hHot hw1 46 le_rfl⟩

/-- `P`-pair (`3 * P` `andGate`s) Berry `Lac = 4` evaluator writing `2 * P` columns `cols` into
`rSlot : QRegister (2 * P) N` using `rAux` and `wU, wV` inside `rPairScr : QRegister (3 * P + 2) N`
(`0..2P-1` = slots, `2P..3P-1` = aux, `3P, 3P+1` = `wU, wV`). -/
def pairedLac4Loop {N P : ℕ} (rHot : QRegister 46 N) (wX0 wX1 wS01 : Wire N)
    (rPairScr : QRegister (3 * P + 2) N)
    (hHotScr : rHot.DisjointWires rPairScr)
    (hX0Scr : ∀ j : Fin (3 * P + 2), wX0 ≠ rPairScr j)
    (hX1Scr : ∀ j : Fin (3 * P + 2), wX1 ≠ rPairScr j)
    (hSScr : ∀ j : Fin (3 * P + 2), wS01 ≠ rPairScr j)
    (cols : Fin (2 * P) → Fin 184 → Bool) :
    (p : ℕ) → p ≤ P → GroupUnary.RevCompute N
  | 0, _ => .id
  | p + 1, hp =>
      let i0 : Fin (3 * P + 2) := ⟨2 * p, by omega⟩
      let i1 : Fin (3 * P + 2) := ⟨2 * p + 1, by omega⟩
      let iA : Fin (3 * P + 2) := ⟨2 * P + p, by omega⟩
      let iU : Fin (3 * P + 2) := ⟨3 * P, by omega⟩
      let iV : Fin (3 * P + 2) := ⟨3 * P + 1, by omega⟩
      have hne_idx {a b : Fin (3 * P + 2)} (hab : a.val ≠ b.val) : rPairScr a ≠ rPairScr b :=
        fun h ↦ hab (congrArg Fin.val (rPairScr.wires.injective h))
      .seq (pairedLac4Loop rHot wX0 wX1 wS01 rPairScr hHotScr hX0Scr hX1Scr hSScr cols p (by omega))
        (onePairLac4Prog rHot wX0 wX1 wS01
          (rPairScr i0) (rPairScr i1) (rPairScr iA) (rPairScr iU) (rPairScr iV)
          (fun i ↦ hHotScr.ne i iU) (fun i ↦ hHotScr.ne i iV)
          (fun i ↦ hHotScr.ne i i0) (fun i ↦ hHotScr.ne i i1)
          (hX0Scr iU) (hX0Scr iV) (hX1Scr iU) (hX1Scr iV) (hSScr iU) (hSScr iV)
          (hne_idx (by dsimp [iU, iV]; omega))
          (hne_idx (by dsimp [iU, i0]; omega)) (hne_idx (by dsimp [iV, i0]; omega))
          (hne_idx (by dsimp [iU, i1]; omega)) (hne_idx (by dsimp [iV, i1]; omega))
          (hne_idx (by dsimp [iU, iA]; omega)) (hne_idx (by dsimp [iV, iA]; omega))
          (hne_idx (by dsimp [iA, i0]; omega)) (hne_idx (by dsimp [iA, i1]; omega))
          (cols ⟨2 * p, by omega⟩) (cols ⟨2 * p + 1, by omega⟩))

@[simp]
theorem numAnd_pairedLac4Loop {N P : ℕ} (rHot : QRegister 46 N) (wX0 wX1 wS01 : Wire N)
    (rPairScr : QRegister (3 * P + 2) N)
    (hHotScr : rHot.DisjointWires rPairScr)
    (hX0Scr : ∀ j : Fin (3 * P + 2), wX0 ≠ rPairScr j)
    (hX1Scr : ∀ j : Fin (3 * P + 2), wX1 ≠ rPairScr j)
    (hSScr : ∀ j : Fin (3 * P + 2), wS01 ≠ rPairScr j)
    (cols : Fin (2 * P) → Fin 184 → Bool) (p : ℕ) (hp : p ≤ P) :
    (pairedLac4Loop rHot wX0 wX1 wS01 rPairScr hHotScr hX0Scr hX1Scr hSScr cols p hp).numAnd =
      3 * p := by
  induction p with
  | zero => rfl
  | succ p ih =>
      simp only [pairedLac4Loop, GroupUnary.RevCompute.numAnd, ih (by omega),
        numAnd_onePairLac4Prog]
      omega

theorem usesOnly_pairedLac4Loop {N P : ℕ} (rHot : QRegister 46 N) (wX0 wX1 wS01 : Wire N)
    (rPairScr : QRegister (3 * P + 2) N)
    (hHotScr : rHot.DisjointWires rPairScr)
    (hX0Scr : ∀ j : Fin (3 * P + 2), wX0 ≠ rPairScr j)
    (hX1Scr : ∀ j : Fin (3 * P + 2), wX1 ≠ rPairScr j)
    (hSScr : ∀ j : Fin (3 * P + 2), wS01 ≠ rPairScr j)
    (cols : Fin (2 * P) → Fin 184 → Bool) {W : Set (Wire N)}
    (hHot : ∀ i : Fin 46, rHot i ∈ W)
    (hx0 : wX0 ∈ W) (hx1 : wX1 ∈ W) (hs : wS01 ∈ W)
    (hScr : ∀ j : Fin (3 * P + 2), rPairScr j ∈ W) (p : ℕ) (hp : p ≤ P) :
    (pairedLac4Loop rHot wX0 wX1 wS01 rPairScr hHotScr hX0Scr hX1Scr
      hSScr cols p hp).UsesOnly W := by
  induction p with
  | zero => trivial
  | succ p ih =>
      exact ⟨ih (by omega),
        usesOnly_onePairLac4Prog _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
          hHot hx0 hx1 hs (hScr _) (hScr _) (hScr _) (hScr _) (hScr _)⟩

/-! ### `46`-AND `base46Prog` (`rHot : 46` + `wS01 : 1`) -/

/-! ### `88`-Wire `keep + pktMux10` (`100 T`) & X-Measurement Leaf (`284 T`, `0 TOFF`, `74` scr) -/

/-- Relocate a fixed-width `(k + s₀)`-wire dynamic circuit onto `(rAct, rScr.slice 0 s₀)`. -/
def placeWithScr {Var : Type} {N k s₀ s : ℕ} (rAct : QRegister k N)
    (rScr : QRegister s N) (hs : s₀ ≤ s) (hDisj : rAct.DisjointWires rScr)
    (P_loc : DynamicCircuit Var (k + s₀)) : DynamicCircuit Var N :=
  let rScr₀ : QRegister s₀ N := rScr.slice 0 s₀ (by simpa using hs)
  P_loc.onRegister (rAct.concat rScr₀ (hDisj.compose_right _))

@[simp]
theorem count_placeWithScr {Var : Type} {N k s₀ s a : ℕ} (g : PrimitiveGate a)
    (rAct : QRegister k N) (rScr : QRegister s N) (hs : s₀ ≤ s) (hDisj : rAct.DisjointWires rScr)
    (P_loc : DynamicCircuit Var (k + s₀)) :
    (placeWithScr rAct rScr hs hDisj P_loc).count g = P_loc.count g :=
  DynamicCircuit.count_onRegister g _ P_loc

theorem support_placeWithScr_subset {Var : Type} {N k s₀ s : ℕ}
    (rAct : QRegister k N) (rScr : QRegister s N) (hs : s₀ ≤ s) (hDisj : rAct.DisjointWires rScr)
    (P_loc : DynamicCircuit Var (k + s₀)) :
    (placeWithScr rAct rScr hs hDisj P_loc).support ⊆ rAct.image ∪ rScr.image := by
  let rScr₀ : QRegister s₀ N := rScr.slice 0 s₀ (by simpa using hs)
  refine (DynamicCircuit.support_onRegister_subset _ P_loc).trans ?_
  rw [QRegister.image_concat]
  exact Finset.union_subset_union_right (rScr.image_compose_subset _)

theorem cleanRealizes_placeWithScr {Var : Type} [Fintype Var] [DecidableEq Var]
    {N k s₀ s : ℕ} [NeZero (2 ^ N)] {v : Var}
    (rAct : QRegister k N) (rScr : QRegister s N) (hs : s₀ ≤ s) (hDisj : rAct.DisjointWires rScr)
    {U : Unitary (2 ^ k)} {P_loc : DynamicCircuit Var (k + s₀)}
    (h : Solution.CleanDyn.CleanRealizes v
      (QRegister.block 0 k (by omega))
      (QRegister.block k s₀ (by omega)) U P_loc) :
    Solution.CleanDyn.CleanRealizes v rAct rScr U (placeWithScr rAct rScr hs hDisj P_loc) := by
  let rScr₀ : QRegister s₀ N := rScr.slice 0 s₀ (by simpa using hs)
  let rPlace := rAct.concat rScr₀ (hDisj.compose_right _)
  have h1 := h.onRegister rPlace
  have hActEq : rPlace.compose (QRegister.block 0 k (by omega)) = rAct := by
    apply CoherentAlias.qreg_ext; intro i
    have hi : (QRegister.block 0 k (by omega)) i = Fin.castAdd s₀ i := Fin.ext (by simp)
    exact congrArg Fin.val ((congrArg rPlace.wires hi).trans (QRegister.concat_apply_left ..))
  have hScrEq : rPlace.compose (QRegister.block k s₀ (by omega)) = rScr₀ := by
    apply CoherentAlias.qreg_ext; intro j
    have hj : (QRegister.block k s₀ (by omega)) j = Fin.natAdd k j := Fin.ext (by simp)
    exact congrArg Fin.val ((congrArg rPlace.wires hj).trans (QRegister.concat_apply_right ..))
  rw [hActEq, hScrEq] at h1
  exact h1.extend_scr hDisj (rScr.image_compose_subset _)

end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.DyadicXMeasPrepOut13

end
