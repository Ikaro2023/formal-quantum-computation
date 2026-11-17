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

public import QuantumComputationDiscoveries.Algorithms.Photochemistry.Solution.Mux48CtrlSafeOracleBase

open QuantumComputation.Specs.PhotochemistrySolution.SpecDefs
open QuantumComputation.Specs.PhotochemistrySolution.QhlAux
open QuantumComputation.Specs.PhotochemistrySolution.PgBase
open QuantumComputation.Specs.PhotochemistrySolution.SelectBase
@[expose] public section

/-!
# `Stage4SubCoinSplice`: Width-Parametric Port-B Slice Specs & `K_sp`-Bit Coin-Splicing Wrapper

Provides:
1. `PhotochemistrySolution.Stage25PolyMCoin` core width-parametric Port-B structures
   (`ReflPotSliceSpecN`, `Stage4ReflCoinPotOraclePortBInPlace`,
   `Stage4ReflCoin23PotOraclePortBInPlace`).
2. `PhotochemistrySolution.Stage4SubCoinSplice`: generic multi-target disjoint-control XOR whitening
   (`cWhitenMulti`) and parametric `K_sp`-bit (`K_sp ≤ 22`) outer-coin splicing wrapper
   (`wrapStage4PortBSubCoin`), mapping any `24`-bit `3`-port potential oracle fixing
   `z24[0 .. 2 + K_sp - 1]` onto `(24 - K_sp)` inner coin wires and `(17 + K_sp)` outer coin wires
   with `0` extra `T` or `TOFF` gates.
-/

noncomputable section
set_option autoImplicit false
set_option exponentiation.threshold 8192
namespace QuantumComputation.Specs.PhotochemistrySolution.Stage25PolyMCoin

open Operator QProg Matrix Circuit Qubit PrimitiveGate PhotochemistrySolution
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt (writeReg)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.QubitizationWalkSem (bitSign)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SelectCsa64ProvSpec (SubspaceStep)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.FineLegendre (mkKetOpW)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SelectOracles (DynWires)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.PotSelectWiring (PotExpectFn
    speciesOfBits2 coordOfReg24)
open scoped Matrix BigOperators

local instance : NeZero 2 := ⟨two_ne_zero⟩
local instance {k : ℕ} : NeZero (2 ^ k) := ⟨pow_ne_zero k two_ne_zero⟩

theorem potBNIdx0_lt {nInner W : ℕ} : 0 < (81 + nInner) + W := by omega
theorem potBNIdx1_lt {nInner W : ℕ} : 1 < (81 + nInner) + W := by omega
theorem potBNIdx2_lt {nInner W : ℕ} : 2 < (81 + nInner) + W := by omega
theorem potBNIdx4_lt {nInner W : ℕ} : 4 < (81 + nInner) + W := by omega
theorem potBNIdx5_lt {nInner W : ℕ} : 5 < (81 + nInner) + W := by omega
theorem potBNIdx6_lt {nInner W : ℕ} : 6 < (81 + nInner) + W := by omega
theorem potBNIdx7_lt {nInner W : ℕ} : 7 < (81 + nInner) + W := by omega
theorem potBNIdx8_lt {nInner W : ℕ} : 8 < (81 + nInner) + W := by omega
theorem potBNBlkNucA_le {nInner W : ℕ} : 9 + 24 ≤ (81 + nInner) + W := by omega
theorem potBNBlkElecA_le {nInner W : ℕ} : 33 + 24 ≤ (81 + nInner) + W := by omega
theorem potBNBlkPortB_le {nInner W : ℕ} : 57 + 24 ≤ (81 + nInner) + W := by omega
theorem potBNBlkCoin_le {nInner W : ℕ} : 81 + nInner ≤ (81 + nInner) + W := by omega
theorem potBNBlkWork_le {nInner W : ℕ} : (81 + nInner) + W ≤ (81 + nInner) + W := le_rfl

abbrev wPotBNLocQ {nInner W n : ℕ} (r : QRegister ((81 + nInner) + W) n) : Wire n :=
  r ⟨0, potBNIdx0_lt⟩
abbrev wPotBNIsScreen {nInner W n : ℕ} (r : QRegister ((81 + nInner) + W) n) : Wire n :=
  r ⟨1, potBNIdx1_lt⟩
abbrev wPotBNIsPot {nInner W n : ℕ} (r : QRegister ((81 + nInner) + W) n) : Wire n :=
  r ⟨2, potBNIdx2_lt⟩
abbrev wPotBNIsNN {nInner W n : ℕ} (r : QRegister ((81 + nInner) + W) n) : Wire n :=
  r ⟨4, potBNIdx4_lt⟩
abbrev wPotBNSp1B0 {nInner W n : ℕ} (r : QRegister ((81 + nInner) + W) n) : Wire n :=
  r ⟨5, potBNIdx5_lt⟩
abbrev wPotBNSp1B1 {nInner W n : ℕ} (r : QRegister ((81 + nInner) + W) n) : Wire n :=
  r ⟨6, potBNIdx6_lt⟩
abbrev wPotBNSp2B0 {nInner W n : ℕ} (r : QRegister ((81 + nInner) + W) n) : Wire n :=
  r ⟨7, potBNIdx7_lt⟩
abbrev wPotBNSp2B1 {nInner W n : ℕ} (r : QRegister ((81 + nInner) + W) n) : Wire n :=
  r ⟨8, potBNIdx8_lt⟩
abbrev rPotBNNucA {nInner W n : ℕ} (r : QRegister ((81 + nInner) + W) n) : QRegister 24 n :=
  r.compose (QRegister.block 9 24 potBNBlkNucA_le)
abbrev rPotBNElecA {nInner W n : ℕ} (r : QRegister ((81 + nInner) + W) n) : QRegister 24 n :=
  r.compose (QRegister.block 33 24 potBNBlkElecA_le)
abbrev rPotBNPortB {nInner W n : ℕ} (r : QRegister ((81 + nInner) + W) n) : QRegister 24 n :=
  r.compose (QRegister.block 57 24 potBNBlkPortB_le)
abbrev rPotBCoinN {nInner W n : ℕ} (r : QRegister ((81 + nInner) + W) n) : QRegister nInner n :=
  r.compose (QRegister.block 81 nInner potBNBlkCoin_le)
abbrev rPotBWorkN {nInner W n : ℕ} (r : QRegister ((81 + nInner) + W) n) : QRegister W n :=
  r.compose (QRegister.block (81 + nInner) W potBNBlkWork_le)

abbrev PotBPhaseBitNFn (nInner : ℕ) : Type :=
  Bool → Bool → Fin 4 → Fin 4 →
    (Fin 3 → Fin 256) → (Fin 3 → Fin 256) → (Fin 3 → Fin 256) → (Fin 3 → Fin 256) →
    BitAssignment nInner → ZMod 2

abbrev PotBCoinSwapNFn (nInner : ℕ) : Type :=
  Bool → Bool → Fin 4 → Fin 4 →
    (Fin 3 → Fin 256) → (Fin 3 → Fin 256) → (Fin 3 → Fin 256) → (Fin 3 → Fin 256) →
    BitAssignment nInner → BitAssignment nInner

/-- Port-B flag invariants (`isPot = 0 → isScreen = 0 ∧ isNN = 0`, `isScreen = 0 → isNN = 0`). -/
def ValidPotBFlagsN {nInner W n : ℕ} (r : QRegister ((81 + nInner) + W) n)
    (β : BitAssignment n) : Prop :=
  (β (wPotBNIsPot r) = 0 → β (wPotBNIsScreen r) = 0 ∧ β (wPotBNIsNN r) = 0) ∧
    (β (wPotBNIsScreen r) = 0 → β (wPotBNIsNN r) = 0)

/-- Conditional XOR of `NucA` into `PortB` when `isScreen = 0`. -/
def xorPortBNNotScr {nInner W n : ℕ} (r : QRegister ((81 + nInner) + W) n) (β : BitAssignment n) :
    BitAssignment n :=
  writeReg β (rPotBNPortB r) fun i ↦
    β (rPotBNPortB r i) + (1 + β (wPotBNIsScreen r)) * β (rPotBNNucA r i)

abbrev potOraclePortBNBitEval {nInner W n : ℕ} (phaseBit : PotBPhaseBitNFn nInner)
    (r : QRegister ((81 + nInner) + W) n) (δ : BitAssignment n) : ZMod 2 :=
  phaseBit (δ (wPotBNIsScreen r) == 1) (δ (wPotBNIsNN r) == 1)
    (speciesOfBits2 (δ (wPotBNSp1B0 r)) (δ (wPotBNSp1B1 r)))
    (speciesOfBits2 (δ (wPotBNSp2B0 r)) (δ (wPotBNSp2B1 r)))
    (coordOfReg24 (rPotBNNucA r) δ)
    (if δ (wPotBNIsNN r) == 1 then coordOfReg24 (rPotBNPortB r) δ else 0)
    (coordOfReg24 (rPotBNElecA r) δ)
    (if δ (wPotBNIsNN r) == 1 then 0 else coordOfReg24 (rPotBNPortB r) δ)
    (fun k ↦ δ (rPotBCoinN r k))

abbrev potOraclePortBNCoinEval {nInner W n : ℕ} (coinSwap : PotBCoinSwapNFn nInner)
    (r : QRegister ((81 + nInner) + W) n) (δ : BitAssignment n) : BitAssignment nInner :=
  coinSwap (δ (wPotBNIsScreen r) == 1) (δ (wPotBNIsNN r) == 1)
    (speciesOfBits2 (δ (wPotBNSp1B0 r)) (δ (wPotBNSp1B1 r)))
    (speciesOfBits2 (δ (wPotBNSp2B0 r)) (δ (wPotBNSp2B1 r)))
    (coordOfReg24 (rPotBNNucA r) δ)
    (if δ (wPotBNIsNN r) == 1 then coordOfReg24 (rPotBNPortB r) δ else 0)
    (coordOfReg24 (rPotBNElecA r) δ)
    (if δ (wPotBNIsNN r) == 1 then 0 else coordOfReg24 (rPotBNPortB r) δ)
    (fun k ↦ δ (rPotBCoinN r k))

/-- Whether the Stage-4 potential reflection gate is active on state `δ`. -/
def potBNGateActive {nInner W n : ℕ} (isCsel : Bool)
    (r : QRegister ((81 + nInner) + W) n) (δ : BitAssignment n) : Bool :=
  if isCsel then (δ (wPotBNLocQ r) == 1) && (δ (wPotBNIsPot r) == 1) else (δ (wPotBNIsPot r) == 1)

/-- Post-reflection basis-state map for an `nInner`-coin Port-B potential oracle. -/
def potReflPortBStN {nInner kCoin W n : ℕ}
    (coinSwapK : BitAssignment kCoin → PotBCoinSwapNFn nInner) (isCsel : Bool)
    (r : QRegister ((81 + nInner) + W) n) (rCoin : QRegister kCoin n)
    (st : BitAssignment n → BitAssignment n) (δ : BitAssignment n) : BitAssignment n :=
  if potBNGateActive isCsel r (st δ) then
    writeReg (st δ) (rPotBCoinN r)
      (potOraclePortBNCoinEval (coinSwapK (fun j ↦ st δ (rCoin j))) r (st δ))
  else st δ

/-- Post-reflection phase-bit map for an `nInner`-coin Port-B potential oracle. -/
def potReflPortBPh0_N {nInner kCoin W n : ℕ}
    (phaseBitK : BitAssignment kCoin → PotBPhaseBitNFn nInner) (isCsel : Bool)
    (r : QRegister ((81 + nInner) + W) n) (rCoin : QRegister kCoin n)
    (st : BitAssignment n → BitAssignment n) (δ : BitAssignment n) : ZMod 2 :=
  (if isCsel then st δ (wPotBNLocQ r) * st δ (wPotBNIsPot r) else st δ (wPotBNIsPot r)) *
    potOraclePortBNBitEval (phaseBitK (fun j ↦ st δ (rCoin j))) r (st δ)

/-- Width-parametric `nInner`-coin potential reflection slice specification. -/
structure ReflPotSliceSpecN (nInner : ℕ) (potExpect : PotExpectFn) where
  phaseBit : PotBPhaseBitNFn nInner
  coinSwap : PotBCoinSwapNFn nInner
  coinSwap_invol : ∀ s nn sp1 sp2 nA nB eA eB z,
    coinSwap s nn sp1 sp2 nA nB eA eB (coinSwap s nn sp1 sp2 nA nB eA eB z) = z
  phaseBit_coinSwap : ∀ s nn sp1 sp2 nA nB eA eB z,
    phaseBit s nn sp1 sp2 nA nB eA eB (coinSwap s nn sp1 sp2 nA nB eA eB z) =
      phaseBit s nn sp1 sp2 nA nB eA eB z
  phaseBit_port : ∀ s nn sp1 sp2 nA nB eA eB z,
    phaseBit s nn sp1 sp2 nA (if nn then nB else 0) eA (if nn then 0 else eB) z =
      phaseBit s nn sp1 sp2 nA nB eA eB z
  coinSwap_port : ∀ s nn sp1 sp2 nA nB eA eB z,
    coinSwap s nn sp1 sp2 nA (if nn then nB else 0) eA (if nn then 0 else eB) z =
      coinSwap s nn sp1 sp2 nA nB eA eB z
  avg_coinN : ∀ (isScreen isNN : Bool) (sp1 sp2 : Fin 4) (nA nB eA eB : Fin 3 → Fin 256),
    (2 ^ nInner : ℂ)⁻¹ *
      (∑ z : BitAssignment nInner, bitSign (phaseBit isScreen isNN sp1 sp2 nA nB eA eB z)) =
      (potExpect isScreen isNN sp1 sp2 nA nB eA eB : ℂ)

theorem of3PortN_port_eq {nInner : ℕ} {α : Type*}
    (f3 : Bool → Bool → Fin 4 → Fin 4 → (Fin 3 → Fin 256) → (Fin 3 → Fin 256) →
      (Fin 3 → Fin 256) → BitAssignment nInner → α) (s nn : Bool) (sp1 sp2 : Fin 4)
    (nA nB eA eB : Fin 3 → Fin 256) (z : BitAssignment nInner) :
    f3 s nn sp1 sp2 nA (if nn then (if nn then nB else 0) else (if nn then 0 else eB)) eA z =
      f3 s nn sp1 sp2 nA (if nn then nB else eB) eA z := by cases nn <;> rfl

/-- Constructs a `ReflPotSliceSpecN` from 3-coordinate `(nA, pB, eA)` maps. -/
def ReflPotSliceSpecN.of3Port {nInner : ℕ} {potExpect : PotExpectFn}
    (phaseBit3 : Bool → Bool → Fin 4 → Fin 4 →
      (Fin 3 → Fin 256) → (Fin 3 → Fin 256) → (Fin 3 → Fin 256) → BitAssignment nInner → ZMod 2)
    (coinSwap3 : Bool → Bool → Fin 4 → Fin 4 →
      (Fin 3 → Fin 256) → (Fin 3 → Fin 256) → (Fin 3 → Fin 256) →
      BitAssignment nInner → BitAssignment nInner)
    (hInv : ∀ s nn sp1 sp2 nA pB eA z,
      coinSwap3 s nn sp1 sp2 nA pB eA (coinSwap3 s nn sp1 sp2 nA pB eA z) = z)
    (hPh : ∀ s nn sp1 sp2 nA pB eA z,
      phaseBit3 s nn sp1 sp2 nA pB eA (coinSwap3 s nn sp1 sp2 nA pB eA z) =
        phaseBit3 s nn sp1 sp2 nA pB eA z)
    (hAvg : ∀ (s nn : Bool) (sp1 sp2 : Fin 4) (nA nB eA eB : Fin 3 → Fin 256),
      (2 ^ nInner : ℂ)⁻¹ *
        (∑ z : BitAssignment nInner,
          bitSign (phaseBit3 s nn sp1 sp2 nA (if nn then nB else eB) eA z)) =
        (potExpect s nn sp1 sp2 nA nB eA eB : ℂ)) :
    ReflPotSliceSpecN nInner potExpect where
  phaseBit s nn sp1 sp2 nA nB eA eB z :=
    phaseBit3 s nn sp1 sp2 nA (if nn then nB else eB) eA z
  coinSwap s nn sp1 sp2 nA nB eA eB z :=
    coinSwap3 s nn sp1 sp2 nA (if nn then nB else eB) eA z
  coinSwap_invol _ _ _ _ _ _ _ _ z := hInv _ _ _ _ _ _ _ z
  phaseBit_coinSwap _ _ _ _ _ _ _ _ z := hPh _ _ _ _ _ _ _ z
  phaseBit_port := of3PortN_port_eq phaseBit3
  coinSwap_port := of3PortN_port_eq coinSwap3
  avg_coinN := hAvg

/-- Width-parametric in-place Port-B Stage-4 potential reflection oracle bundle. -/
structure Stage4ReflCoinPotOraclePortBInPlace (nInner kCoin Wp tPotU tPotC : ℕ)
    (potExpectK : BitAssignment kCoin → PotExpectFn) where
  sliceSpec : ∀ γ : BitAssignment kCoin, ReflPotSliceSpecN nInner (potExpectK γ)
  pCsel : ∀ {Var : Type} {n : ℕ},
    Var → QRegister ((81 + nInner) + Wp) n → QRegister kCoin n → DynamicCircuit Var n
  pUsel : ∀ {Var : Type} {n : ℕ},
    Var → QRegister ((81 + nInner) + Wp) n → QRegister kCoin n → DynamicCircuit Var n
  step_and_counts : ∀ {Var : Type} [Fintype Var] [DecidableEq Var]
    {m n : ℕ} [NeZero (2 ^ n)] (v : Var) (rW : QRegister m n)
    (r : QRegister ((81 + nInner) + Wp) n) (rCoin : QRegister kCoin n)
    (_ : r.DisjointWires rCoin) (isCsel : Bool)
    (st : BitAssignment n → BitAssignment n),
    (∀ δ, (∀ q : Fin m, δ (rW q) = 0) → ValidPotBFlagsN r (st δ)) →
    (∀ δ (u : Fin Wp), (∀ q : Fin m, δ (rW q) = 0) → st δ (rPotBWorkN r u) = 0) →
    (∀ δ (i : Fin 24), (∀ q : Fin m, δ (rW q) = 0) →
      st δ (wPotBNIsScreen r) = 0 → st δ (rPotBNPortB r i) = 0) →
    let p := if isCsel then pCsel v r rCoin else pUsel v r rCoin
    SubspaceStep (mkKetOpW rW st (fun _ ↦ 0))
      (mkKetOpW rW
        (fun δ ↦ xorPortBNNotScr r
          (potReflPortBStN (fun γ ↦ (sliceSpec γ).coinSwap) isCsel r rCoin st δ))
        (potReflPortBPh0_N (fun γ ↦ (sliceSpec γ).phaseBit) isCsel r rCoin st)) p ∧
    p.count .T = (if isCsel then tPotC else tPotU) ∧
    p.count .TOFF = 0
  dynWires : ∀ {Var : Type} {n : ℕ} (S : Wire n → Prop) (v : Var)
    (r : QRegister ((81 + nInner) + Wp) n) (rCoin : QRegister kCoin n),
    (∀ i : Fin ((81 + nInner) + Wp), S (r i)) → (∀ j : Fin kCoin, S (rCoin j)) →
    DynWires S (pCsel v r rCoin) ∧ DynWires S (pUsel v r rCoin)

abbrev Stage4ReflCoin23PotOraclePortBInPlace := Stage4ReflCoinPotOraclePortBInPlace 23

end QuantumComputation.Specs.PhotochemistrySolution.Stage25PolyMCoin
end

noncomputable section
set_option autoImplicit false
set_option exponentiation.threshold 8192
namespace QuantumComputation.Specs.PhotochemistrySolution.Stage4SubCoinSplice

open Operator QProg Matrix Circuit Qubit PrimitiveGate PhotochemistrySolution
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt (writeReg writeReg_apply_reg
  writeReg_apply_of_not_mem)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.QubitizationWalkSem (bitSign)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB (ComputeProg)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SelectCsa64ProvSpec (SubspaceStep
    stepCB)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SubregMBUCore (wrapDynOnReg onRegCP
    counts_wrapDynOnReg)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SelectOracles (DynWires
    dynWires_wrapDyn)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.PotOracleGen (disj_of_ne
    subspaceStep_wrapOnReg_vprog2 cpw_onRegCP_clean)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Stage4FineMbu (subspaceStep_of_eq_post)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.FineLegendre (mkKetOpW mkKetOpW_congr)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Coin70Lift (liftFinDyn_c70
    liftFinDyn_eq_c70)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.WStateMux48 (DynCtrlSafe)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.PotSelectWiring (PotExpectFn
    coordOfReg24)
open PhotochemistrySolution.Stage25PolyMCoin
open scoped BigOperators

local instance : NeZero 2 := ⟨two_ne_zero⟩
local instance {k : ℕ} : NeZero (2 ^ k) := ⟨pow_ne_zero k two_ne_zero⟩

/-! ### 1. Disjoint-Control Multi-Target CNOT Whitening -/

/-- Parity sum over a list of control wire indices in `Fin C`. -/
def otpSum {C : ℕ} (cs : List (Fin C)) (γ : Fin C → ZMod 2) : ZMod 2 :=
  cs.foldr (fun c acc ↦ γ c + acc) 0

/-- CNOT fan-in from controls in `0 .. C - 1` onto a disjoint target wire `tgt ≥ C`. -/
def cnotCtrlList {C K : ℕ} (tgt : Fin (C + K)) (hTgt : C ≤ tgt.val) :
    List (Fin C) → ComputeProg (C + K)
  | [] => .id
  | c :: cs =>
      .seq (.cnot ⟨c.val, by omega⟩ tgt (Fin.ne_of_val_ne (by
          dsimp
          omega)))
        (cnotCtrlList tgt hTgt cs)

theorem numAnd_cnotCtrlList {C K : ℕ} (tgt : Fin (C + K)) (hTgt : C ≤ tgt.val) :
    ∀ cs : List (Fin C), (cnotCtrlList tgt hTgt cs).numAnd = 0 :=
  List.rec rfl fun _ _ ih ↦ by simp [cnotCtrlList, ComputeProg.numAnd, ih]

theorem validProg_cnotCtrlList {C K : ℕ} (tgt : Fin (C + K)) (hTgt : C ≤ tgt.val) :
    ∀ cs : List (Fin C), (cnotCtrlList tgt hTgt cs).ValidProg ∅ ∅ :=
  List.rec trivial fun _ _ ih ↦
    ⟨⟨Finset.notMem_empty _, Finset.notMem_empty _, Or.inl (Finset.notMem_empty _)⟩, ih⟩

theorem fwdBits_cnotCtrlList {C K : ℕ} (tgt : Fin (C + K)) (hTgt : C ≤ tgt.val) :
    ∀ (cs : List (Fin C)) (γ : BitAssignment (C + K)) (u : Fin (C + K)),
      (cnotCtrlList tgt hTgt cs).fwdBits γ u =
        if u = tgt then γ tgt + otpSum cs (fun c ↦ γ ⟨c.val, by omega⟩) else γ u
  | [], _, u => by by_cases hu : u = tgt <;> simp [cnotCtrlList, otpSum, ComputeProg.fwdBits, hu]
  | c :: cs, γ, u => by
      simp only [cnotCtrlList, ComputeProg.fwdBits, fwdBits_cnotCtrlList tgt hTgt cs,
        show (fun j : Fin C ↦ Function.update γ tgt _ ⟨j.val, by omega⟩) = fun j ↦ γ ⟨j.val, _⟩ from
          funext fun j ↦
              Function.update_of_ne (Fin.ne_of_val_ne (lt_of_lt_of_le j.isLt hTgt).ne) _ _]
      by_cases hu : u = tgt <;> simp [otpSum, hu, add_assoc]

/-- Prefix of `m ≤ K` disjoint-target CNOT fan-ins on wires `C .. C + m - 1`. -/
def cWhitenAux {C K : ℕ} (masks : Fin K → List (Fin C)) :
    (m : ℕ) → m ≤ K → ComputeProg (C + K)
  | 0, _ => .id
  | m + 1, hm =>
      .seq (cWhitenAux masks m (Nat.le_of_succ_le hm))
        (cnotCtrlList ⟨C + m, by omega⟩ (Nat.le_add_right C m) (masks ⟨m, hm⟩))

/-- Multi-target CNOT whitening from controls `0 .. C - 1` onto targets `C .. C + K - 1`. -/
def cWhitenMulti {C K : ℕ} (masks : Fin K → List (Fin C)) : ComputeProg (C + K) :=
  cWhitenAux masks K le_rfl

theorem numAnd_cWhitenAux {C K : ℕ} (masks : Fin K → List (Fin C)) :
    ∀ (m : ℕ) (hm : m ≤ K), (cWhitenAux masks m hm).numAnd = 0
  | 0, _ => rfl
  | m + 1, hm =>
        by simp [cWhitenAux, ComputeProg.numAnd, numAnd_cWhitenAux masks m, numAnd_cnotCtrlList]

theorem finalClean_empty {M : ℕ} : ∀ p : ComputeProg M, p.finalClean ∅ = ∅
  | .id | .x _ | .cnot _ _ _ => rfl
  | .andGate _ _ _ _ _ _ => Finset.erase_empty _
  | .seq p₁ p₂ => (congrArg p₂.finalClean (finalClean_empty p₁)).trans (finalClean_empty p₂)

theorem validProg_cWhitenAux {C K : ℕ} (masks : Fin K → List (Fin C)) :
    ∀ (m : ℕ) (hm : m ≤ K), (cWhitenAux masks m hm).ValidProg ∅ ∅
  | 0, _ => trivial
  | m + 1, hm => ⟨validProg_cWhitenAux masks m _,
      (finalClean_empty _).symm ▸ validProg_cnotCtrlList ⟨C + m, by omega⟩ (Nat.le_add_right C m) _⟩

theorem fwdBits_cWhitenMulti {C K : ℕ} (masks : Fin K → List (Fin C))
    (γ : BitAssignment (C + K)) (u : Fin (C + K)) :
    (cWhitenMulti masks).fwdBits γ u = if _ : u.val < C then γ u
      else γ u + otpSum (masks ⟨u.val - C, by omega⟩) (fun c ↦ γ ⟨c.val, by omega⟩) := by
  have aux (m : ℕ) : ∀ (hm : m ≤ K) (v : Fin (C + K)), (cWhitenAux masks m hm).fwdBits γ v =
      if _ : v.val < C then γ v else if _ : v.val < C + m then
        γ v + otpSum (masks ⟨v.val - C, by omega⟩) (fun c ↦ γ ⟨c.val, by omega⟩) else γ v := by
    induction m with
    | zero =>
        exact fun _ v ↦ by
          by_cases hlo : v.val < C <;> simp [cWhitenAux, ComputeProg.fwdBits, hlo]
    | succ m ih =>
        intro hm v
        have ih' := ih (Nat.le_of_succ_le hm)
        simp only [cWhitenAux, ComputeProg.fwdBits, fwdBits_cnotCtrlList,
          show (fun c : Fin C ↦ (cWhitenAux masks m (Nat.le_of_succ_le hm)).fwdBits γ
            ⟨c.val, by omega⟩) = fun c ↦ γ ⟨c.val, by omega⟩ from
              funext fun c ↦ by simp [ih', c.isLt]]
        rcases eq_or_ne v ⟨C + m, by omega⟩ with rfl | hv
        · simpa only [↓reduceIte, ih', show ¬ C + m < C by omega, show ¬ C + m < C + m by omega,
            show C + m < C + (m + 1) by omega, ↓reduceDIte] using
              congrArg (γ _ + otpSum · _)
                  (congrArg masks (Fin.ext (Nat.add_sub_cancel_left C m).symm))
        · have : v.val ≠ C + m := Fin.val_ne_of_ne hv
          by_cases hlo : v.val < C <;> by_cases hhi : v.val < C + m <;>
            simp [hv, ih', hlo, hhi, show (v.val < C + (m + 1)) ↔ v.val < C + m by omega]
  by_cases hlo : u.val < C <;> simp [cWhitenMulti, aux K le_rfl u, hlo, u.isLt]

/-! ### 2. Parametric `(kCtrl, K_sp)`-Bit Splicing into `BitAssignment 24` -/

/-- Packs `γOut[0 .. kCtrl - 1]` and `z0, z1` into a `(kCtrl + 2)`-wire OTP control vector. -/
def whitenCtrl {kCtrl K_sp : ℕ} (γOut : BitAssignment (kCtrl + K_sp)) (z0 z1 : ZMod 2)
    (c : Fin (kCtrl + 2)) : ZMod 2 :=
  if hc : c.val < kCtrl then γOut ⟨c.val, by omega⟩
  else if c.val = kCtrl then z0
  else z1

/-- Restricts a `(kCtrl + K_sp)`-wire outer coin (`17 ≤ kCtrl`) to its base `17` wires. -/
def take17OfOut {kCtrl K_sp : ℕ} (hk17 : 17 ≤ kCtrl)
    (γOut : BitAssignment (kCtrl + K_sp)) : BitAssignment 17 :=
  fun j ↦ γOut ⟨j.val, by omega⟩

/-- Splices `K_sp` whitened outer coin bits `γOut[kCtrl..]` into `z24[2 .. 2 + K_sp - 1]`. -/
def splicedZ24 {kCtrl K_sp : ℕ} (hK : K_sp ≤ 22) (masks : Fin K_sp → List (Fin (kCtrl + 2)))
    (γOut : BitAssignment (kCtrl + K_sp)) (zN : BitAssignment (24 - K_sp)) : BitAssignment 24 :=
  fun ⟨kv, _⟩ ↦
    if _hk2 : kv < 2 then zN ⟨kv, by omega⟩
    else if _hkSp : kv < 2 + K_sp then
      γOut ⟨kCtrl + (kv - 2), by omega⟩ +
        otpSum (masks ⟨kv - 2, by omega⟩)
          (whitenCtrl γOut (zN ⟨0, by omega⟩) (zN ⟨1, by omega⟩))
    else zN ⟨kv - K_sp, by omega⟩

/-- Drops the spliced window `z24[2 .. 2 + K_sp - 1]` back to `BitAssignment (24 - K_sp)`. -/
def unspliceZN {K_sp : ℕ} (hK : K_sp ≤ 22) (z24 : BitAssignment 24) :
    BitAssignment (24 - K_sp) :=
  fun ⟨iv, _⟩ ↦
    if iv < 2 then z24 ⟨iv, by omega⟩
    else z24 ⟨iv + K_sp, by omega⟩

/-- `3`-port `(24 - K_sp)`-coin swap induced by splicing into a `24`-bit `3`-port coin swap. -/
def subCoinSwap3 {kCtrl K_sp : ℕ} (hk17 : 17 ≤ kCtrl) (hK : K_sp ≤ 22)
    (masks : Fin K_sp → List (Fin (kCtrl + 2)))
    (coinSwap24 : BitAssignment 17 → Bool → Bool → Fin 4 → Fin 4 →
      (Fin 3 → Fin 256) → (Fin 3 → Fin 256) → (Fin 3 → Fin 256) →
      BitAssignment 24 → BitAssignment 24)
    (γOut : BitAssignment (kCtrl + K_sp)) (s nn : Bool) (sp1 sp2 : Fin 4)
    (nA pB eA : Fin 3 → Fin 256) (zN : BitAssignment (24 - K_sp)) : BitAssignment (24 - K_sp) :=
  unspliceZN hK
    (coinSwap24 (take17OfOut hk17 γOut) s nn sp1 sp2 nA pB eA (splicedZ24 hK masks γOut zN))

/-- `3`-port `(24 - K_sp)`-coin phase bit induced by splicing into a `24`-bit `3`-port phase bit. -/
def subPhaseBit3 {kCtrl K_sp : ℕ} (hk17 : 17 ≤ kCtrl) (hK : K_sp ≤ 22)
    (masks : Fin K_sp → List (Fin (kCtrl + 2)))
    (phaseBit24 : BitAssignment 17 → Bool → Bool → Fin 4 → Fin 4 →
      (Fin 3 → Fin 256) → (Fin 3 → Fin 256) → (Fin 3 → Fin 256) →
      BitAssignment 24 → ZMod 2)
    (γOut : BitAssignment (kCtrl + K_sp)) (s nn : Bool) (sp1 sp2 : Fin 4)
    (nA pB eA : Fin 3 → Fin 256) (zN : BitAssignment (24 - K_sp)) : ZMod 2 :=
  phaseBit24 (take17OfOut hk17 γOut) s nn sp1 sp2 nA pB eA (splicedZ24 hK masks γOut zN)

theorem spliced_subCoinSwap3 {kCtrl K_sp : ℕ} (hk17 : 17 ≤ kCtrl) (hK : K_sp ≤ 22) (masks)
    (coinSwap24) (hLo24 : ∀ γ17 s nn sp1 sp2 nA pB eA z24 {k : Fin 24},
      k.val < 2 + K_sp → coinSwap24 γ17 s nn sp1 sp2 nA pB eA z24 k = z24 k)
    (γOut : BitAssignment (kCtrl + K_sp)) (s nn : Bool) (sp1 sp2 : Fin 4)
    (nA pB eA : Fin 3 → Fin 256) (zN : BitAssignment (24 - K_sp)) :
    splicedZ24 hK masks γOut (subCoinSwap3 hk17 hK masks coinSwap24 γOut s nn sp1 sp2 nA pB eA zN) =
      coinSwap24 (take17OfOut hk17 γOut) s nn sp1 sp2 nA pB eA (splicedZ24 hK masks γOut zN) := by
  funext ⟨kv, hkv⟩
  have h01 (b : ℕ) (hb : b < 2) : coinSwap24 (take17OfOut hk17 γOut) s nn sp1 sp2 nA pB eA
      (splicedZ24 hK masks γOut zN) ⟨b, by omega⟩ = zN ⟨b, by omega⟩ :=
    (hLo24 _ _ _ _ _ _ _ _ _ (k := ⟨b, by omega⟩)
        (show b < 2 + K_sp by omega)).trans (by simp [splicedZ24, hb])
  by_cases hk2 : kv < 2
  · conv_lhs => unfold splicedZ24
    simp only [hk2, ↓reduceDIte, subCoinSwap3, unspliceZN, ↓reduceIte]
  · by_cases hkSp : kv < 2 + K_sp
    · rw [hLo24 _ _ _ _ _ _ _ _ _ (k := ⟨kv, hkv⟩) hkSp]
      conv_lhs => unfold splicedZ24
      conv_rhs => unfold splicedZ24
      simp only [hk2, hkSp, ↓reduceDIte, subCoinSwap3, unspliceZN, show (0 : ℕ) < 2 by omega,
        show (1 : ℕ) < 2 by omega, ↓reduceIte, h01 0 (by omega), h01 1 (by omega)]
    · conv_lhs => unfold splicedZ24
      simpa [subCoinSwap3, unspliceZN, hk2, hkSp, show ¬ kv - K_sp < 2 by omega] using
        congrArg _ (Fin.ext (Nat.sub_add_cancel (by omega)))

theorem subCoinSwap3_invol {kCtrl K_sp : ℕ} (hk17 : 17 ≤ kCtrl) (hK : K_sp ≤ 22) (masks)
    (coinSwap24) (hInv24 : ∀ γ17 s nn sp1 sp2 nA pB eA z24,
      coinSwap24 γ17 s nn sp1 sp2 nA pB eA (coinSwap24 γ17 s nn sp1 sp2 nA pB eA z24) = z24)
    (hLo24 : ∀ γ17 s nn sp1 sp2 nA pB eA z24 {k : Fin 24},
      k.val < 2 + K_sp → coinSwap24 γ17 s nn sp1 sp2 nA pB eA z24 k = z24 k)
    (γOut : BitAssignment (kCtrl + K_sp)) (s nn sp1 sp2 nA pB eA)
    (zN : BitAssignment (24 - K_sp)) :
    subCoinSwap3 hk17 hK masks coinSwap24 γOut s nn sp1 sp2 nA pB eA
      (subCoinSwap3 hk17 hK masks coinSwap24 γOut s nn sp1 sp2 nA pB eA zN) = zN := by
  conv_lhs => rw [subCoinSwap3]
  rw [spliced_subCoinSwap3 hk17 hK masks coinSwap24 hLo24, hInv24]
  funext ⟨iv, _⟩
  by_cases hi : iv < 2
  · simp [unspliceZN, splicedZ24, hi]
  · simpa only [unspliceZN, splicedZ24, hi, show ¬ iv + K_sp < 2 by omega,
      show ¬ iv + K_sp < 2 + K_sp by omega, ↓reduceIte, ↓reduceDIte] using
      congrArg zN (Fin.ext (Nat.add_sub_cancel iv K_sp))

theorem subPhaseBit3_coinSwap {kCtrl K_sp : ℕ} (hk17 : 17 ≤ kCtrl) (hK : K_sp ≤ 22) (masks)
    (phaseBit24 coinSwap24) (hPh24 : ∀ γ17 s nn sp1 sp2 nA pB eA z24,
      phaseBit24 γ17 s nn sp1 sp2 nA pB eA (coinSwap24 γ17 s nn sp1 sp2 nA pB eA z24) =
        phaseBit24 γ17 s nn sp1 sp2 nA pB eA z24)
    (hLo24 : ∀ γ17 s nn sp1 sp2 nA pB eA z24 {k : Fin 24},
      k.val < 2 + K_sp → coinSwap24 γ17 s nn sp1 sp2 nA pB eA z24 k = z24 k)
    (γOut : BitAssignment (kCtrl + K_sp)) (s nn sp1 sp2 nA pB eA zN) :
    subPhaseBit3 hk17 hK masks phaseBit24 γOut s nn sp1 sp2 nA pB eA
      (subCoinSwap3 hk17 hK masks coinSwap24 γOut s nn sp1 sp2 nA pB eA zN) =
      subPhaseBit3 hk17 hK masks phaseBit24 γOut s nn sp1 sp2 nA pB eA zN := by
  exact (congrArg _ (spliced_subCoinSwap3 hk17 hK masks coinSwap24 hLo24 _ _ _ _ _ _ _ _ _)).trans
      (hPh24 _ _ _ _ _ _ _ _ _)

/-- Expectation function averaged over the `(24 - K_sp)` inner coin wires. -/
def potExpectSub {kCtrl K_sp : ℕ} (hk17 : 17 ≤ kCtrl) (hK : K_sp ≤ 22)
    (masks : Fin K_sp → List (Fin (kCtrl + 2)))
    (phaseBit24 : BitAssignment 17 → Bool → Bool → Fin 4 → Fin 4 →
      (Fin 3 → Fin 256) → (Fin 3 → Fin 256) → (Fin 3 → Fin 256) →
      BitAssignment 24 → ZMod 2)
    (γOut : BitAssignment (kCtrl + K_sp)) : PotExpectFn :=
  fun s nn sp1 sp2 nA nB eA eB ↦
    (2 ^ (24 - K_sp) : ℝ)⁻¹ *
      ∑ zN : BitAssignment (24 - K_sp),
        if subPhaseBit3 hk17 hK masks phaseBit24 γOut s nn sp1 sp2
            nA (if nn then nB else eB) eA zN = 1
        then (-1 : ℝ) else 1

theorem subPhaseBit3_avg_coinN {kCtrl K_sp : ℕ} (hk17 : 17 ≤ kCtrl) (hK : K_sp ≤ 22)
    (masks phaseBit24) (γOut : BitAssignment (kCtrl + K_sp)) (s nn sp1 sp2)
    (nA nB eA eB : Fin 3 → Fin 256) :
    (2 ^ (24 - K_sp) : ℂ)⁻¹ * (∑ zN : BitAssignment (24 - K_sp),
        bitSign (subPhaseBit3 hk17 hK masks phaseBit24 γOut s nn sp1 sp2
          nA (if nn then nB else eB) eA zN)) =
      (potExpectSub hk17 hK masks phaseBit24 γOut s nn sp1 sp2 nA nB eA eB : ℂ) := by
  simp_rw [show ∀ x : ZMod 2, bitSign x = ((if x = 1 then (-1 : ℝ) else 1 : ℝ) : ℂ) from
    fun x ↦ by rcases DynCircExt.bit_cases x with rfl | rfl <;> norm_num [bitSign]]
  simp [potExpectSub]

/-- Spliced `(24 - K_sp)`-coin `ReflPotSliceSpecN` induced by a `24`-bit `3`-port slice. -/
def subReflPotSliceSpecN {kCtrl K_sp : ℕ} (hk17 : 17 ≤ kCtrl) (hK : K_sp ≤ 22)
    (masks : Fin K_sp → List (Fin (kCtrl + 2)))
    (phaseBit24 : BitAssignment 17 → Bool → Bool → Fin 4 → Fin 4 →
      (Fin 3 → Fin 256) → (Fin 3 → Fin 256) → (Fin 3 → Fin 256) →
      BitAssignment 24 → ZMod 2)
    (coinSwap24 : BitAssignment 17 → Bool → Bool → Fin 4 → Fin 4 →
      (Fin 3 → Fin 256) → (Fin 3 → Fin 256) → (Fin 3 → Fin 256) →
      BitAssignment 24 → BitAssignment 24)
    (hInv24 : ∀ γ17 s nn sp1 sp2 nA pB eA z24,
      coinSwap24 γ17 s nn sp1 sp2 nA pB eA (coinSwap24 γ17 s nn sp1 sp2 nA pB eA z24) = z24)
    (hPh24 : ∀ γ17 s nn sp1 sp2 nA pB eA z24,
      phaseBit24 γ17 s nn sp1 sp2 nA pB eA (coinSwap24 γ17 s nn sp1 sp2 nA pB eA z24) =
        phaseBit24 γ17 s nn sp1 sp2 nA pB eA z24)
    (hLo24 : ∀ γ17 s nn sp1 sp2 nA pB eA z24 {k : Fin 24},
      k.val < 2 + K_sp → coinSwap24 γ17 s nn sp1 sp2 nA pB eA z24 k = z24 k)
    (γOut : BitAssignment (kCtrl + K_sp)) :
    ReflPotSliceSpecN (24 - K_sp) (potExpectSub hk17 hK masks phaseBit24 γOut) :=
  ReflPotSliceSpecN.of3Port
    (subPhaseBit3 hk17 hK masks phaseBit24 γOut)
    (subCoinSwap3 hk17 hK masks coinSwap24 γOut)
    (subCoinSwap3_invol hk17 hK masks coinSwap24 hInv24 hLo24 γOut)
    (subPhaseBit3_coinSwap hk17 hK masks phaseBit24 coinSwap24 hPh24 hLo24 γOut)
    (subPhaseBit3_avg_coinN hk17 hK masks phaseBit24 γOut)

/-! ### 3. Spliced `QRegister` Embeddings & Disjointness -/

/-- Base `17`-wire coin subregister of `rCoin : QRegister (kCtrl + K_sp) n` (`17 ≤ kCtrl`). -/
def rCoin17OfOut {kCtrl K_sp n : ℕ} (hk17 : 17 ≤ kCtrl)
    (rCoin : QRegister (kCtrl + K_sp) n) : QRegister 17 n :=
  rCoin.compose (QRegister.block 0 17 (by omega))

/-- Wire-index map splicing `rCoin[kCtrl .. kCtrl + K_sp - 1]` into `r24[83 .. 83 + K_sp - 1]`. -/
def f24OfSub {kCtrl K_sp Wp n : ℕ} (hK : K_sp ≤ 22)
    (r : QRegister ((81 + (24 - K_sp)) + Wp) n) (rCoin : QRegister (kCtrl + K_sp) n)
    (i : Fin ((81 + 24) + Wp)) : Wire n :=
  if _hi83 : i.val < 83 then r ⟨i.val, by omega⟩
  else if _hiSp : i.val < 83 + K_sp then rCoin ⟨kCtrl + (i.val - 83), by omega⟩
  else r ⟨i.val - K_sp, by omega⟩

/-- Inverse index helper on `r` for `f24OfSub`. -/
def invR24Sub (K_sp k : ℕ) : ℕ := if k < 83 then k else k + K_sp

/-- Inverse index helper on `rCoin` for `f24OfSub`. -/
def invC24Sub (kCtrl j : ℕ) : ℕ := 83 + (j - kCtrl)

theorem f24OfSub_tag {kCtrl K_sp Wp n : ℕ} (hK : K_sp ≤ 22)
    (r : QRegister ((81 + (24 - K_sp)) + Wp) n) (rCoin : QRegister (kCtrl + K_sp) n) (i) :
    (∃ k, f24OfSub hK r rCoin i = r k ∧ invR24Sub K_sp k.val = i.val) ∨
    (∃ j, f24OfSub hK r rCoin i = rCoin j ∧ kCtrl ≤ j.val ∧ invC24Sub kCtrl j.val = i.val) := by
  unfold f24OfSub invR24Sub invC24Sub
  split_ifs with h1 h2
  · exact .inl ⟨⟨i.val, by omega⟩, rfl, ite_eq_left h1⟩
  · exact .inr ⟨⟨kCtrl + (i.val - 83), by omega⟩, rfl, by dsimp; omega, by dsimp; omega⟩
  · exact .inl ⟨⟨i.val - K_sp, by omega⟩, rfl, by dsimp; split_ifs <;> omega⟩

theorem f24OfSub_inj {kCtrl K_sp Wp n : ℕ} (hK : K_sp ≤ 22)
    (r : QRegister ((81 + (24 - K_sp)) + Wp) n) (rCoin : QRegister (kCtrl + K_sp) n)
    (hd : r.DisjointWires rCoin) : Function.Injective (f24OfSub hK r rCoin) := fun a b hab ↦ by
  rcases f24OfSub_tag hK r rCoin a with ⟨_, ha, ia⟩ | ⟨_, ha, _, ia⟩ <;>
    rcases f24OfSub_tag hK r rCoin b with ⟨_, hb, ib⟩ | ⟨_, hb, _, ib⟩ <;> rw [ha, hb] at hab <;>
    first | exact Fin.ext (ia ▸ ib ▸ congrArg (invR24Sub K_sp ∘ Fin.val) (r.wires.injective hab))
          | exact Fin.ext (ia ▸ ib ▸ congrArg (invC24Sub kCtrl ∘ Fin.val)
                (rCoin.wires.injective hab))
          | exact absurd hab (QRegister.disjoint_iff.mp hd _ _)
          | exact absurd hab.symm (QRegister.disjoint_iff.mp hd _ _)

/-- Spliced `((81 + 24) + Wp)`-wire Port-B register fed to the inner `24`-coin oracle. -/
def r24OfSub {kCtrl K_sp Wp n : ℕ} (hK : K_sp ≤ 22)
    (r : QRegister ((81 + (24 - K_sp)) + Wp) n) (rCoin : QRegister (kCtrl + K_sp) n)
    (hd : r.DisjointWires rCoin) : QRegister ((81 + 24) + Wp) n :=
  ⟨⟨f24OfSub hK r rCoin, f24OfSub_inj hK r rCoin hd⟩⟩

theorem disj_r24OfSub_rCoin17 {kCtrl K_sp Wp n : ℕ} (hk17 : 17 ≤ kCtrl) (hK : K_sp ≤ 22)
    (r : QRegister ((81 + (24 - K_sp)) + Wp) n) (rCoin : QRegister (kCtrl + K_sp) n)
    (hd : r.DisjointWires rCoin) :
    (r24OfSub hK r rCoin hd).DisjointWires (rCoin17OfOut hk17 rCoin) :=
  disj_of_ne fun i j hEq ↦ (f24OfSub_tag hK r rCoin i).elim
    (fun ⟨k, hk, _⟩ ↦ QRegister.disjoint_iff.mp hd k ⟨0 + j.val, by omega⟩ (hk.symm.trans hEq))
    (fun ⟨jc, hjc, _, _⟩ ↦ rCoin.wires.injective.ne
      (Fin.ne_of_val_ne (show jc.val ≠ 0 + j.val by omega)) (hjc.symm.trans hEq))

/-- Wire-index map for the `((kCtrl + 2) + K_sp)`-wire whitening subregister. -/
def fWhitenSub {kCtrl K_sp Wp n : ℕ} (hK : K_sp ≤ 22)
    (r : QRegister ((81 + (24 - K_sp)) + Wp) n) (rCoin : QRegister (kCtrl + K_sp) n)
    (u : Fin ((kCtrl + 2) + K_sp)) : Wire n :=
  if _huC : u.val < kCtrl then rCoin ⟨u.val, by omega⟩
  else if _huC2 : u.val < kCtrl + 2 then r ⟨81 + (u.val - kCtrl), by omega⟩
  else rCoin ⟨kCtrl + (u.val - (kCtrl + 2)), by omega⟩

/-- Inverse index helper on `r` for `fWhitenSub`. -/
def invRWhiten (kCtrl k : ℕ) : ℕ := kCtrl + (k - 81)

/-- Inverse index helper on `rCoin` for `fWhitenSub`. -/
def invCWhiten (kCtrl j : ℕ) : ℕ := if j < kCtrl then j else j + 2

theorem fWhitenSub_tag {kCtrl K_sp Wp n : ℕ} (hK : K_sp ≤ 22)
    (r : QRegister ((81 + (24 - K_sp)) + Wp) n) (rCoin : QRegister (kCtrl + K_sp) n) (u) :
    (∃ k, fWhitenSub hK r rCoin u = r k ∧ invRWhiten kCtrl k.val = u.val) ∨
    (∃ j, fWhitenSub hK r rCoin u = rCoin j ∧ invCWhiten kCtrl j.val = u.val) := by
  unfold fWhitenSub invRWhiten invCWhiten
  split_ifs with h1 h2
  · exact .inr ⟨⟨u.val, by omega⟩, rfl, ite_eq_left h1⟩
  · exact .inl ⟨⟨81 + (u.val - kCtrl), by omega⟩, rfl, by dsimp only; omega⟩
  · exact .inr ⟨⟨kCtrl + (u.val - (kCtrl + 2)), by omega⟩, rfl, by dsimp; split_ifs <;> omega⟩

theorem fWhitenSub_inj {kCtrl K_sp Wp n : ℕ} (hK : K_sp ≤ 22)
    (r : QRegister ((81 + (24 - K_sp)) + Wp) n) (rCoin : QRegister (kCtrl + K_sp) n)
    (hd : r.DisjointWires rCoin) : Function.Injective (fWhitenSub hK r rCoin) := fun a b hab ↦ by
  rcases fWhitenSub_tag hK r rCoin a with ⟨_, ha, ia⟩ | ⟨_, ha, ia⟩ <;>
    rcases fWhitenSub_tag hK r rCoin b with ⟨_, hb, ib⟩ | ⟨_, hb, ib⟩ <;> rw [ha, hb] at hab <;>
    first | exact Fin.ext (ia ▸ ib ▸ congrArg (invRWhiten kCtrl ∘ Fin.val) (r.wires.injective hab))
          | exact Fin.ext (ia ▸ ib ▸ congrArg (invCWhiten kCtrl ∘ Fin.val)
                (rCoin.wires.injective hab))
          | exact absurd hab (QRegister.disjoint_iff.mp hd _ _)
          | exact absurd hab.symm (QRegister.disjoint_iff.mp hd _ _)

/-- `((kCtrl + 2) + K_sp)`-wire whitening subregister (`rCoin[0..kCtrl-1]`, `z[0..1]`, targets). -/
def rWhitenSub {kCtrl K_sp Wp n : ℕ} (hK : K_sp ≤ 22)
    (r : QRegister ((81 + (24 - K_sp)) + Wp) n) (rCoin : QRegister (kCtrl + K_sp) n)
    (hd : r.DisjointWires rCoin) : QRegister ((kCtrl + 2) + K_sp) n :=
  ⟨⟨fWhitenSub hK r rCoin, fWhitenSub_inj hK r rCoin hd⟩⟩

theorem stepCB_cWhitenMulti_spliced {kCtrl K_sp Wp n : ℕ}
    (hK : K_sp ≤ 22)
    (masks : Fin K_sp → List (Fin (kCtrl + 2))) (r : QRegister ((81 + (24 - K_sp)) + Wp) n)
    (rCoin : QRegister (kCtrl + K_sp) n) (hd : r.DisjointWires rCoin)
    (β) (s : Fin K_sp) :
    stepCB (rWhitenSub hK r rCoin hd) (cWhitenMulti masks).fwdBits β
      (rCoin ⟨kCtrl + s.val, by omega⟩) = β (rCoin ⟨kCtrl + s.val, by omega⟩) + otpSum (masks s)
        (whitenCtrl (fun j ↦ β (rCoin j)) (β (r ⟨81, by omega⟩)) (β (r ⟨82, by omega⟩))) := by
  have hTgt : rWhitenSub hK r rCoin hd ⟨(kCtrl + 2) + s.val, by omega⟩ = rCoin ⟨kCtrl + s.val,
      by omega⟩ :=
    (dite_eq_right (by dsimp; omega)).trans ((dite_eq_right (by dsimp; omega)).trans
      (congrArg rCoin (Fin.ext (congrArg (kCtrl + ·) (Nat.add_sub_cancel_left _ _)))))
  rw [← hTgt, stepCB, writeReg_apply_reg, fwdBits_cWhitenMulti, dite_eq_right (by dsimp; omega),
    hTgt, show (⟨_, _⟩ : Fin K_sp) = s from Fin.ext (Nat.add_sub_cancel_left _ _)]
  refine congrArg (β _ + otpSum (masks s) ·) (funext fun c ↦ ?_)
  by_cases hcC : c.val < kCtrl <;> by_cases hcEq : c.val = kCtrl <;>
    simp [rWhitenSub, fWhitenSub, whitenCtrl, hcC, hcEq, c.isLt,
      show ¬c.val < kCtrl → c.val ≠ kCtrl → 81 + (c.val - kCtrl) = 82 by omega]

theorem stepCB_cWhitenMulti_other {kCtrl K_sp Wp n : ℕ} (hK : K_sp ≤ 22)
    (masks : Fin K_sp → List (Fin (kCtrl + 2))) (r : QRegister ((81 + (24 - K_sp)) + Wp) n)
    (rCoin : QRegister (kCtrl + K_sp) n) (hd : r.DisjointWires rCoin) (β) {w : Wire n}
    (hw : ∀ s : Fin K_sp, w ≠ rCoin ⟨kCtrl + s.val, by omega⟩) :
    stepCB (rWhitenSub hK r rCoin hd) (cWhitenMulti masks).fwdBits β w = β w := by
  by_cases hwMem : ∃ u, rWhitenSub hK r rCoin hd u = w
  · obtain ⟨u, rfl⟩ := hwMem
    rw [stepCB, writeReg_apply_reg, fwdBits_cWhitenMulti]
    by_cases huC2 : u.val < kCtrl + 2
    · simp [huC2]
    · exact absurd (by simp [rWhitenSub, fWhitenSub, huC2, show ¬ u.val < kCtrl by omega])
        (hw ⟨u.val - (kCtrl + 2), by omega⟩)
  · exact writeReg_apply_of_not_mem _ _ _ _ hwMem

/-! ### 4. Parametric Port-B `DynamicCircuit` Wrapper & `SubspaceStep` Proof -/

/-- Wraps a `24`-inner / `17`-outer Port-B oracle with `(kCtrl, K_sp)` coin splicing. -/
def pStage4WrapSub {Var : Type} {kCtrl K_sp Wp tPotU tPotC n : ℕ}
    (hk17 : 17 ≤ kCtrl) (hK : K_sp ≤ 22)
    (masks : Fin K_sp → List (Fin (kCtrl + 2))) {pe17 : BitAssignment 17 → PotExpectFn}
    (o24 : Stage4ReflCoinPotOraclePortBInPlace 24 17 Wp tPotU tPotC pe17)
    (isCsel : Bool) (v : Var)
    (r : QRegister ((81 + (24 - K_sp)) + Wp) n) (rCoin : QRegister (kCtrl + K_sp) n) :
    DynamicCircuit Var n :=
  liftFinDyn_c70 fun [Fintype Var] [DecidableEq Var] ↦
    @dite _ (r.DisjointWires rCoin) (Classical.dec _)
      (fun hd ↦
        let r24 := r24OfSub hK r rCoin hd
        let rC17 := rCoin17OfOut hk17 rCoin
        let pMid := if isCsel then o24.pCsel v r24 rC17 else o24.pUsel v r24 rC17
        wrapDynOnReg v (rWhitenSub hK r rCoin hd) (cWhitenMulti masks) pMid)
      (fun _ ↦ .circuit .identity)

theorem dynWires_pStage4WrapSub {Var : Type} {kCtrl K_sp Wp tPotU tPotC n : ℕ} {S : Wire n → Prop}
    (hk17 : 17 ≤ kCtrl) (hK : K_sp ≤ 22) (masks : Fin K_sp → List (Fin (kCtrl + 2)))
    {pe17 : BitAssignment 17 → PotExpectFn}
    (o24 : Stage4ReflCoinPotOraclePortBInPlace 24 17 Wp tPotU tPotC pe17) (isCsel : Bool) (v : Var)
    (r : QRegister ((81 + (24 - K_sp)) + Wp) n) (rCoin : QRegister (kCtrl + K_sp) n)
    (hSr : ∀ i, S (r i)) (hSc : ∀ j, S (rCoin j)) :
    DynWires S (pStage4WrapSub hk17 hK masks o24 isCsel v r rCoin) := by
  refine (DynCtrlSafe.liftFinDyn (S_ctrl := S) (S_tgt := S) _ ?_).to_dynWires
  intro _ _
  by_cases hd : r.DisjointWires rCoin
  · simp only [hd, ↓reduceDIte]
    have hSr24 (i) : S (f24OfSub hK r rCoin i) := (f24OfSub_tag hK r rCoin i).elim
      (fun ⟨_, hk, _⟩ ↦ hk.symm ▸ hSr _) (fun ⟨_, hj, _, _⟩ ↦ hj.symm ▸ hSc _)
    have hSw (u) : S (fWhitenSub hK r rCoin u) := (fWhitenSub_tag hK r rCoin u).elim
      (fun ⟨_, hk, _⟩ ↦ hk.symm ▸ hSr _) (fun ⟨_, hj, _⟩ ↦ hj.symm ▸ hSc _)
    let r2 := r24OfSub hK r rCoin hd
    let rW := rWhitenSub hK r rCoin hd
    obtain ⟨dwC, dwU⟩ := o24.dynWires (fun w ↦ S w ∧ S w) v r2 (rCoin17OfOut hk17 rCoin)
      (fun i ↦ ⟨hSr24 i, hSr24 i⟩) (fun j ↦ ⟨hSc ⟨0 + j.val, by omega⟩, hSc _⟩)
    obtain ⟨_, _, fMid⟩ := o24.step_and_counts v (QRegExt.empty n) r2 _
      (disj_r24OfSub_rCoin17 hk17 hK r rCoin hd) isCsel (fun _ _ ↦ 0)
      (fun _ _ ↦ ⟨fun _ ↦ ⟨rfl, rfl⟩, fun _ ↦ rfl⟩) (fun _ _ _ ↦ rfl) (fun _ _ _ _ ↦ rfl)
    refine .of_dynWires ?_ ((counts_wrapDynOnReg v rW (cWhitenMulti masks) _).2.trans fMid)
    unfold wrapDynOnReg
    exact dynWires_wrapDyn v (onRegCP rW (cWhitenMulti masks)) _
      (cpw_onRegCP_clean (S := fun w ↦ S w ∧ S w) rW (fun u ↦ ⟨hSw u, hSw u⟩) _)
      (by cases isCsel <;> assumption)
  · simpa only [hd, ↓reduceDIte] using .identity S S

set_option maxHeartbeats 800000 in
-- 3-port coin-splicing SubspaceStep and wire-framing proof across pre/oracle/post phases
theorem step_and_counts_pStage4WrapSub {Var : Type} [Fintype Var] [DecidableEq Var]
    {m kCtrl K_sp Wp tPotU tPotC n : ℕ} [NeZero (2 ^ n)]
    (hk17 : 17 ≤ kCtrl) (hK : K_sp ≤ 22) (masks : Fin K_sp → List (Fin (kCtrl + 2)))
    {pe17 : BitAssignment 17 → PotExpectFn} (phaseBit24 coinSwap24)
    (hInv24 : ∀ γ17 s nn sp1 sp2 nA pB eA z24,
      coinSwap24 γ17 s nn sp1 sp2 nA pB eA (coinSwap24 γ17 s nn sp1 sp2 nA pB eA z24) = z24)
    (hPh24 : ∀ γ17 s nn sp1 sp2 nA pB eA z24,
      phaseBit24 γ17 s nn sp1 sp2 nA pB eA (coinSwap24 γ17 s nn sp1 sp2 nA pB eA z24) =
        phaseBit24 γ17 s nn sp1 sp2 nA pB eA z24)
    (hAvg24 : ∀ (γ17 : BitAssignment 17) (s nn : Bool) (sp1 sp2 : Fin 4)
      (nA nB eA eB : Fin 3 → Fin 256), (2 ^ 24 : ℂ)⁻¹ * (∑ z24 : BitAssignment 24,
          bitSign (phaseBit24 γ17 s nn sp1 sp2 nA (if nn then nB else eB) eA z24)) =
        (pe17 γ17 s nn sp1 sp2 nA nB eA eB : ℂ))
    (hLo24 : ∀ γ17 s nn sp1 sp2 nA pB eA z24 {k : Fin 24},
      k.val < 2 + K_sp → coinSwap24 γ17 s nn sp1 sp2 nA pB eA z24 k = z24 k)
    (o24 : Stage4ReflCoinPotOraclePortBInPlace 24 17 Wp tPotU tPotC pe17)
    (hSlice : ∀ γ17, o24.sliceSpec γ17 = ReflPotSliceSpecN.of3Port (phaseBit24 γ17)
      (coinSwap24 γ17) (hInv24 γ17) (hPh24 γ17) (hAvg24 γ17))
    (v : Var) (rW : QRegister m n) (r : QRegister ((81 + (24 - K_sp)) + Wp) n)
    (rCoin : QRegister (kCtrl + K_sp) n) (hd : r.DisjointWires rCoin) (isCsel : Bool)
    (st : BitAssignment n → BitAssignment n)
    (hFlags : ∀ δ, (∀ q : Fin m, δ (rW q) = 0) → ValidPotBFlagsN r (st δ))
    (hWorkCln : ∀ δ (u : Fin Wp), (∀ q : Fin m, δ (rW q) = 0) → st δ (rPotBWorkN r u) = 0)
    (hPB0 : ∀ δ (i : Fin 24), (∀ q : Fin m, δ (rW q) = 0) →
      st δ (wPotBNIsScreen r) = 0 → st δ (rPotBNPortB r i) = 0) :
    let sliceSub := subReflPotSliceSpecN hk17 hK masks phaseBit24 coinSwap24 hInv24 hPh24 hLo24
    let p := if isCsel then pStage4WrapSub hk17 hK masks o24 true v r rCoin
             else pStage4WrapSub hk17 hK masks o24 false v r rCoin
    SubspaceStep (mkKetOpW rW st (fun _ ↦ 0)) (mkKetOpW rW
      (fun δ ↦ xorPortBNNotScr r
        (potReflPortBStN (fun γ ↦ (sliceSub γ).coinSwap) isCsel r rCoin st δ))
      (potReflPortBPh0_N (fun γ ↦ (sliceSub γ).phaseBit) isCsel r rCoin st)) p ∧
    p.count .T = (if isCsel then tPotC else tPotU) ∧ p.count .TOFF = 0 := by
  intro sliceSub p
  let r24 := r24OfSub hK r rCoin hd
  let rC17 := rCoin17OfOut hk17 rCoin
  let rWh := rWhitenSub hK r rCoin hd
  let pMid := if isCsel then o24.pCsel v r24 rC17 else o24.pUsel v r24 rC17
  rw [show p = wrapDynOnReg v rWh (cWhitenMulti masks) pMid by
    cases isCsel <;> simp only [p, pMid, ↓reduceIte, Bool.false_eq_true, pStage4WrapSub] <;>
      rw [liftFinDyn_eq_c70] <;> simp only [hd, ↓reduceDIte] <;> rfl]
  let st1 := fun δ ↦ stepCB rWh (cWhitenMulti masks).fwdBits (st δ)
  let stPost := fun δ ↦
      xorPortBNNotScr r (potReflPortBStN (fun γ ↦ (sliceSub γ).coinSwap) isCsel r rCoin st δ)
  let phPost := potReflPortBPh0_N (fun γ ↦ (sliceSub γ).phaseBit) isCsel r rCoin st
  have hDisj := QRegister.disjoint_iff.mp hd
  have hSt1_r (δ i) : st1 δ (r i) = st δ (r i) :=
    stepCB_cWhitenMulti_other hK masks r rCoin hd (st δ) fun _ ↦ hDisj i _
  have hLt83 (m0 : ℕ) (hm0 : m0 < 83 := by
    omega) : r24 ⟨m0, by omega⟩ = r ⟨m0, by omega⟩ := dite_eq_left hm0
  have hBlk : rPotBNNucA r24 = rPotBNNucA r ∧ rPotBNElecA r24 = rPotBNElecA r ∧ rPotBNPortB r24 =
      rPotBNPortB r :=
    ⟨QRegister.ext (Function.Embedding.ext fun i ↦ hLt83 (9 + i.val)),
     QRegister.ext (Function.Embedding.ext fun i ↦ hLt83 (33 + i.val)),
     QRegister.ext (Function.Embedding.ext fun i ↦ hLt83 (57 + i.val))⟩
  have hSt1_lt83 (δ) (m0 : ℕ) (hm0 : m0 < 83 := by
    omega) : st1 δ (r24 ⟨m0, by omega⟩) = st δ (r ⟨m0, by omega⟩) :=
    (congrArg (st1 δ) (hLt83 m0 hm0)).trans (hSt1_r δ _)
  obtain ⟨sMidRaw, tMid, fMid⟩ := o24.step_and_counts v rW r24 rC17
    (disj_r24OfSub_rCoin17 hk17 hK r rCoin hd) isCsel st1
    (fun δ hz ↦
        by simpa only [ValidPotBFlagsN, hSt1_lt83 δ 1, hSt1_lt83 δ 2,
             hSt1_lt83 δ 4] using hFlags δ hz)
    (fun δ u hz ↦ (congrArg (st1 δ)
        ((dite_eq_right (by dsimp; omega)).trans ((dite_eq_right (by dsimp; omega)).trans
      (congrArg r (Fin.ext (by dsimp; omega)))))).trans ((hSt1_r δ _).trans (hWorkCln δ u hz)))
    (fun δ i hz hs ↦ (congrArg (st1 δ <| · i) hBlk.2.2).trans
      ((hSt1_r δ _).trans (hPB0 δ i hz ((hSt1_lt83 δ 1).symm.trans hs))))
  have hCS (δ) : (fun k : Fin 24 ↦ st1 δ (rPotBCoinN r24 k)) =
      splicedZ24 hK masks (fun j ↦ st δ (rCoin j)) (fun i ↦ st δ (rPotBCoinN r i)) :=
    funext fun ⟨kv, _⟩ ↦ by
      change st1 δ (f24OfSub hK r rCoin ⟨81 + kv, by omega⟩) = _
      dsimp only [f24OfSub, splicedZ24]
      by_cases hk2 : kv < 2
      · simp only [show 81 + kv < 83 by omega, hk2, ↓reduceDIte]
        exact hSt1_r δ _
      · by_cases hkSp : kv < 2 + K_sp
        · simp only [show ¬ 81 + kv < 83 by omega, show 81 + kv < 83 + K_sp by omega, hk2, hkSp,
              ↓reduceDIte,
            show rCoin ⟨kCtrl + (81 + kv - 83), by omega⟩ = rCoin ⟨kCtrl + (kv - 2), by omega⟩ from
              congrArg rCoin (Fin.ext (by dsimp; omega))]
          exact stepCB_cWhitenMulti_spliced hK masks r rCoin hd (st δ) ⟨kv - 2, by omega⟩
        · simp only [show ¬ 81 + kv < 83 by omega, show ¬ 81 + kv < 83 + K_sp by omega, hk2, hkSp,
              ↓reduceDIte,
            show r ⟨81 + kv - K_sp, by omega⟩ = r ⟨81 + (kv - K_sp), by omega⟩ from
              congrArg r (Fin.ext (by dsimp; omega))]
          exact hSt1_r δ _
  have hG17 (δ) : (fun j : Fin 17 ↦ st1 δ (rC17 j)) = take17OfOut hk17 (fun j ↦ st δ (rCoin j)) :=
    funext fun j ↦ (congrArg (st1 δ) (congrArg rCoin (Fin.ext (Nat.zero_add j.val)))).trans
      (stepCB_cWhitenMulti_other hK masks r rCoin hd (st δ) fun s ↦
        rCoin.wires.injective.ne (Fin.ne_of_val_ne (show j.val ≠ kCtrl + s.val by omega)))
  have hGate (δ) : potBNGateActive isCsel r24 (st1 δ) = potBNGateActive isCsel r (st δ) := by
    simp only [potBNGateActive, hSt1_lt83 δ 0, hSt1_lt83 δ 2]
  have hCoord (δ) {rA rB : QRegister 24 n} (h : rA = rB) (hs : ∀ q, st1 δ (rB q) = st δ (rB q)) :
      coordOfReg24 rA (st1 δ) = coordOfReg24 rB (st δ) :=
    (congrArg (coordOfReg24 · (st1 δ)) h).trans (funext fun _ ↦ congrArg _ (funext fun _ ↦ hs _))
  have hCoords (δ) : _ ∧ _ ∧ _ := ⟨hCoord δ hBlk.1 fun _ ↦ hSt1_r δ _,
    hCoord δ hBlk.2.1 fun _ ↦ hSt1_r δ _, hCoord δ hBlk.2.2 fun _ ↦ hSt1_r δ _⟩
  have hSl (γ17) := congrArg ReflPotSliceSpecN.coinSwap (hSlice γ17)
  have hNC {nI kC csF} (rX : QRegister ((81 + nI) + Wp) n) (rCX : QRegister kC n) {stX δ}
      (i : Fin ((81 + nI) + Wp))
          (hi : i.val < 81) : potReflPortBStN csF isCsel rX rCX stX δ (rX i) = stX δ (rX i) := by
    dsimp only [potReflPortBStN]
    split_ifs
    · exact writeReg_apply_of_not_mem _ _ _ _ fun ⟨k, hk⟩ ↦
        (show 81 + k.val ≠ i.val by omega) (congrArg Fin.val (rX.wires.injective hk))
    · rfl
  have hL81 (δ) (m0 : ℕ) (hm0 : m0 < 81 := by omega) :
      potReflPortBStN (fun γ ↦ (o24.sliceSpec γ).coinSwap) isCsel r24 rC17 st1 δ
        (r ⟨m0, hm0.trans_le ((Nat.le_add_right 81 _).trans (Nat.le_add_right _ _))⟩) =
      potReflPortBStN (fun γ ↦ (sliceSub γ).coinSwap) isCsel r rCoin st δ
        (r ⟨m0, hm0.trans_le ((Nat.le_add_right 81 _).trans (Nat.le_add_right _ _))⟩) :=
    (congrArg _ (hLt83 m0).symm).trans ((hNC r24 rC17 _ hm0).trans
      ((hSt1_lt83 δ m0).trans (hNC r rCoin _ hm0).symm))
  have sMid : SubspaceStep (mkKetOpW rW st1 (fun _ ↦ 0))
      (mkKetOpW rW (fun δ ↦ stepCB rWh (cWhitenMulti masks).fwdBits (stPost δ)) phPost) pMid := by
    refine subspaceStep_of_eq_post sMidRaw (mkKetOpW_congr rW (fun δ _ ↦ funext fun w ↦ ?_)
        (fun δ _ ↦ ?_))
    · have hPc (j) : stPost δ (rCoin j) = st δ (rCoin j) := by
        dsimp only [stPost, xorPortBNNotScr, potReflPortBStN]
        rw [writeReg_apply_of_not_mem _ _ _ _ fun ⟨_, hi⟩ ↦ hDisj _ _ hi]
        split_ifs
        · exact writeReg_apply_of_not_mem _ _ _ _ fun ⟨_, hk⟩ ↦ hDisj _ _ hk
        · rfl
      have hPz (b : ℕ) (hb : b < 2) : stPost δ (r ⟨81 + b, by omega⟩) = st δ (r ⟨81 + b, by omega⟩)
          := by
        dsimp only [stPost, xorPortBNNotScr, potReflPortBStN]
        rw [writeReg_apply_of_not_mem _ _ _ _ fun ⟨i, hi⟩ ↦
          (show 57 + i.val ≠ 81 + b by omega) (congrArg Fin.val (r.wires.injective hi))]
        split_ifs
        · rw [show r ⟨81 + b, _⟩ = rPotBCoinN r ⟨b, by omega⟩ from rfl, writeReg_apply_reg]
          simp only [potOraclePortBNCoinEval, sliceSub, subReflPotSliceSpecN,
              ReflPotSliceSpecN.of3Port,
            subCoinSwap3, unspliceZN, hb, ↓reduceIte,
            hLo24 _ _ _ _ _ _ _ _ _ (k := ⟨b, by omega⟩) (by dsimp; omega), splicedZ24,
                ↓reduceDIte]
        · rfl
      by_cases hwSp : ∃ s : Fin K_sp, w = rCoin ⟨kCtrl + s.val, by omega⟩
      · obtain ⟨s, rfl⟩ := hwSp
        rw [stepCB_cWhitenMulti_spliced hK masks r rCoin hd (stPost δ) s]
        simp_rw [hPc, hPz 0 (by omega), hPz 1 (by omega)]
        dsimp only [xorPortBNNotScr, potReflPortBStN]
        rw [writeReg_apply_of_not_mem _ _ _ _ fun ⟨_, hi⟩ ↦ hDisj _ _ (hBlk.2.2 ▸ hi), hSl, hGate δ]
        refine Eq.trans ?_ (stepCB_cWhitenMulti_spliced hK masks r rCoin hd (st δ) s)
        split_ifs
        · have hcSp : rCoin ⟨kCtrl + s.val, by omega⟩ = rPotBCoinN r24 ⟨2 + s.val, by omega⟩ := by
            change rCoin _ = f24OfSub hK r rCoin ⟨81 + (2 + s.val), _⟩
            simpa only [f24OfSub, show ¬ 81 + (2 + s.val) < 83 by omega,
              show 81 + (2 + s.val) < 83 + K_sp by omega,
                  ↓reduceDIte] using congrArg rCoin (Fin.ext (by dsimp; omega))
          rw [hcSp, writeReg_apply_reg]
          exact hLo24 _ _ _ _ _ _ _ _ _ (show 2 + s.val < 2 + K_sp by omega)
        · rfl
      · simp only [not_exists] at hwSp
        rw [stepCB_cWhitenMulti_other hK masks r rCoin hd (stPost δ) hwSp]
        dsimp only [stPost, xorPortBNNotScr]
        rw [hBlk.1, hBlk.2.2]
        by_cases hwPB : ∃ i, rPotBNPortB r i = w
        · obtain ⟨i, rfl⟩ := hwPB
          rw [writeReg_apply_reg, writeReg_apply_reg, show rPotBNPortB r i =
              r ⟨57 + i.val, by omega⟩ from rfl,
            show rPotBNNucA r i = r ⟨9 + i.val, by omega⟩ from rfl, hL81 δ (57 + i.val),
                hL81 δ (9 + i.val),
            (congrArg _ (hLt83 1)).trans (hL81 δ 1)]
        · dsimp only [potReflPortBStN]
          rw [writeReg_apply_of_not_mem _ _ _ _ hwPB, writeReg_apply_of_not_mem _ _ _ _ hwPB, hSl,
              hGate δ]
          split_ifs
          · by_cases hwCN : ∃ i, rPotBCoinN r i = w
            · obtain ⟨i, rfl⟩ := hwCN
              let k24 : Fin 24 := if i.val < 2 then ⟨i.val, by omega⟩ else ⟨i.val + K_sp, by omega⟩
              have hwEq24 : rPotBCoinN r i = rPotBCoinN r24 k24 := by
                change r ⟨81 + i.val, _⟩ = f24OfSub hK r rCoin ⟨81 + k24.val, _⟩
                by_cases hi2 : i.val < 2
                · simp [f24OfSub, k24, hi2, show 81 + i.val < 83 by omega]
                · simpa only [f24OfSub, k24, hi2, ↓reduceIte, show ¬ 81 + (i.val + K_sp) <
                      83 by omega,
                    show ¬ 81 + (i.val + K_sp) < 83 + K_sp by omega, ↓reduceDIte] using
                      congrArg r (Fin.ext (by dsimp; omega))
              rw [writeReg_apply_reg, hwEq24, writeReg_apply_reg]
              unfold potOraclePortBNCoinEval
              rw [(hCoords δ).1, (hCoords δ).2.1, (hCoords δ).2.2, hSt1_lt83 δ 1, hSt1_lt83 δ 4,
                hSt1_lt83 δ 5, hSt1_lt83 δ 6, hSt1_lt83 δ 7, hSt1_lt83 δ 8, hG17 δ, hCS δ]
              rcases i with ⟨iv, _⟩
              by_cases hi2 : iv < 2 <;> simp [sliceSub, subReflPotSliceSpecN,
                ReflPotSliceSpecN.of3Port, subCoinSwap3, unspliceZN, k24, hi2]
            · rw [writeReg_apply_of_not_mem _ _ _ _ hwCN,
                writeReg_apply_of_not_mem _ _ _ _ fun ⟨k, hk⟩ ↦
                  (f24OfSub_tag hK r rCoin ⟨81 + k.val, by omega⟩).elim
                    (fun ⟨kr, hkr, hir⟩ ↦ hwCN ⟨⟨kr.val - 81, by
                        dsimp [invR24Sub] at hir; split_ifs at hir <;> omega⟩,
                      (congrArg r (Fin.ext (by
                        dsimp [invR24Sub] at hir ⊢; split_ifs at hir <;> omega))).trans
                        (hkr.symm.trans hk)⟩)
                    (fun ⟨jc, hjc, hkc, _⟩ ↦ hwSp ⟨jc.val - kCtrl, by omega⟩
                      (hk.symm.trans (hjc.trans
                        (congrArg rCoin (Fin.ext (Nat.add_sub_of_le hkc)).symm))))]
              exact stepCB_cWhitenMulti_other hK masks r rCoin hd (st δ) hwSp
          · exact stepCB_cWhitenMulti_other hK masks r rCoin hd (st δ) hwSp
    · dsimp only [phPost, potReflPortBPh0_N, potOraclePortBNBitEval]
      rw [hSlice _, hSt1_lt83 δ 0, hSt1_lt83 δ 2, (hCoords δ).1, (hCoords δ).2.1, (hCoords δ).2.2,
        hSt1_lt83 δ 1, hSt1_lt83 δ 4, hSt1_lt83 δ 5, hSt1_lt83 δ 6, hSt1_lt83 δ 7, hSt1_lt83 δ 8,
        hG17 δ, hCS δ]
      rfl
  obtain ⟨sWrap, tWrap, fWrap, _⟩ := subspaceStep_wrapOnReg_vprog2 v rW rWh ∅ (cWhitenMulti masks) 0
    (validProg_cWhitenAux masks K_sp le_rfl) (numAnd_cWhitenAux masks K_sp le_rfl) st stPost
    (fun _ ↦ 0) phPost pMid (fun _ h ↦ absurd h (Finset.notMem_empty _))
    (fun _ h ↦ absurd h (Finset.notMem_empty _)) sMid
  exact ⟨sWrap, (by simpa using tWrap : _ = pMid.count .T).trans tMid, fWrap.trans fMid⟩

/-- Turnkey Port-B oracle bundle splicing `K_sp` outer coin wires (`kCtrl ≥ 17`) into `z24`. -/
def wrapStage4PortBSubCoin {kCtrl K_sp Wp tPotU tPotC : ℕ}
    (hk17 : 17 ≤ kCtrl) (hK : K_sp ≤ 22) (masks : Fin K_sp → List (Fin (kCtrl + 2)))
    {pe17 : BitAssignment 17 → PotExpectFn}
    (phaseBit24 : BitAssignment 17 → Bool → Bool → Fin 4 → Fin 4 →
      (Fin 3 → Fin 256) → (Fin 3 → Fin 256) → (Fin 3 → Fin 256) →
      BitAssignment 24 → ZMod 2)
    (coinSwap24 : BitAssignment 17 → Bool → Bool → Fin 4 → Fin 4 →
      (Fin 3 → Fin 256) → (Fin 3 → Fin 256) → (Fin 3 → Fin 256) →
      BitAssignment 24 → BitAssignment 24)
    (hInv24 : ∀ γ17 s nn sp1 sp2 nA pB eA z24,
      coinSwap24 γ17 s nn sp1 sp2 nA pB eA (coinSwap24 γ17 s nn sp1 sp2 nA pB eA z24) = z24)
    (hPh24 : ∀ γ17 s nn sp1 sp2 nA pB eA z24,
      phaseBit24 γ17 s nn sp1 sp2 nA pB eA (coinSwap24 γ17 s nn sp1 sp2 nA pB eA z24) =
        phaseBit24 γ17 s nn sp1 sp2 nA pB eA z24)
    (hAvg24 : ∀ (γ17 : BitAssignment 17) (s nn : Bool) (sp1 sp2 : Fin 4)
      (nA nB eA eB : Fin 3 → Fin 256),
      (2 ^ 24 : ℂ)⁻¹ *
        (∑ z24 : BitAssignment 24,
          bitSign (phaseBit24 γ17 s nn sp1 sp2 nA (if nn then nB else eB) eA z24)) =
        (pe17 γ17 s nn sp1 sp2 nA nB eA eB : ℂ))
    (hLo24 : ∀ γ17 s nn sp1 sp2 nA pB eA z24 {k : Fin 24},
      k.val < 2 + K_sp → coinSwap24 γ17 s nn sp1 sp2 nA pB eA z24 k = z24 k)
    (o24 : Stage4ReflCoinPotOraclePortBInPlace 24 17 Wp tPotU tPotC pe17)
    (hSlice : ∀ γ17, o24.sliceSpec γ17 =
      ReflPotSliceSpecN.of3Port (phaseBit24 γ17) (coinSwap24 γ17)
        (hInv24 γ17) (hPh24 γ17) (hAvg24 γ17)) :
    Stage4ReflCoinPotOraclePortBInPlace (24 - K_sp) (kCtrl + K_sp) Wp tPotU tPotC
      (potExpectSub hk17 hK masks phaseBit24) where
  sliceSpec := subReflPotSliceSpecN hk17 hK masks phaseBit24 coinSwap24 hInv24 hPh24 hLo24
  pCsel v r rCoin := pStage4WrapSub hk17 hK masks o24 true v r rCoin
  pUsel v r rCoin := pStage4WrapSub hk17 hK masks o24 false v r rCoin
  step_and_counts v rW r rCoin hd isCsel st hFlags hWorkCln hPB0 :=
    step_and_counts_pStage4WrapSub hk17 hK masks phaseBit24 coinSwap24 hInv24 hPh24 hAvg24 hLo24
      o24 hSlice v rW r rCoin hd isCsel st hFlags hWorkCln hPB0
  dynWires _S v r rCoin hSr hSc :=
    ⟨dynWires_pStage4WrapSub hk17 hK masks o24 true v r rCoin hSr hSc,
     dynWires_pStage4WrapSub hk17 hK masks o24 false v r rCoin hSr hSc⟩

end QuantumComputation.Specs.PhotochemistrySolution.Stage4SubCoinSplice
end
