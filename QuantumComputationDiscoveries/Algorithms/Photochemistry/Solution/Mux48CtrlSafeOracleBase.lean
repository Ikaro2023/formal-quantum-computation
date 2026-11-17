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
public import QuantumComputationDiscoveries.Algorithms.Photochemistry.Solution.WStateHalfBellCollapse

open QuantumComputation.Specs.PhotochemistrySolution.SpecDefs
open QuantumComputation.Specs.PhotochemistrySolution.QhlAux
open QuantumComputation.Specs.PhotochemistrySolution.PgBase
open QuantumComputation.Specs.PhotochemistrySolution.SelectBase
@[expose] public section
set_option exponentiation.threshold 256
set_option allowUnsafeReducibility true
set_option autoImplicit false

noncomputable section
namespace QuantumComputation.Specs.PhotochemistrySolution.WStateMux48
open scoped BigOperators
open Operator QProg Matrix Circuit Qubit PrimitiveGate QuantumComputation.Specs
  PhotochemistrySolution
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
open PhotochemistrySolution.FineLegendre PhotochemistrySolution.InPlaceModAdd
  PhotochemistrySolution.Stage4FineMbu PhotochemistrySolution.QubitizationWalkSem
open PhotochemistrySolution.SelectCsa64ProvSpec PhotochemistrySolution.Coin70Lift
  PhotochemistrySolution.ReflStage4
open PhotochemistrySolution.SelectOracles PhotochemistrySolution.Poly28Sub254
  PhotochemistrySolution.PotOracleGen PhotochemistrySolution.PotSelectWiring
open PhotochemistrySolution.ZeroNEremSpec PhotochemistrySolution.SubregMBUCore
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt (writeReg writeReg_apply_reg
  writeReg_apply_of_not_mem)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB (ComputeProg)
section Safety
attribute [local semireducible] PhotochemistrySolution.SubregMBUCore.wrapDynOnReg

/- Section 1A: Control-only safety (`DynCtrlSafe`) and `35`-inner-coin `PortB` oracle contract. -/

/--
Reversible `ComputeProg` control/target wire discipline: controls lie in `S_ctrl`, while all
modified targets lie in `S_ctrl ∩ S_tgt`.
-/
def ComputeProgCtrlSafe {n : ℕ} (S_ctrl S_tgt : Wire n → Prop) : ComputeProg n → Prop
  | .id => True
  | .x u => S_ctrl u ∧ S_tgt u
  | .cnot c tgt _ => S_ctrl c ∧ S_ctrl tgt ∧ S_tgt tgt
  | .andGate c₁ c₂ a _ _ _ => S_ctrl c₁ ∧ S_ctrl c₂ ∧ S_ctrl a ∧ S_tgt a
  | .seq p₁ p₂ => ComputeProgCtrlSafe S_ctrl S_tgt p₁ ∧ ComputeProgCtrlSafe S_ctrl S_tgt p₂

theorem ComputeProgCtrlSafe.of_all {n : ℕ} {S_ctrl S_tgt : Wire n → Prop}
    (hAll : ∀ u : Wire n, S_ctrl u ∧ S_tgt u) :
    ∀ cp : ComputeProg n, ComputeProgCtrlSafe S_ctrl S_tgt cp
  | .id => trivial
  | .x u => hAll u
  | .cnot c tgt _ => ⟨(hAll c).1, (hAll tgt).1, (hAll tgt).2⟩
  | .andGate c₁ c₂ a _ _ _ => ⟨(hAll c₁).1, (hAll c₂).1, (hAll a).1, (hAll a).2⟩
  | .seq p₁ p₂ => ⟨of_all hAll p₁, of_all hAll p₂⟩

inductive DynCtrlSafe {Var : Type} {n : ℕ} (S_ctrl S_tgt : Wire n → Prop) :
    DynamicCircuit Var n → Prop
  | of_dynWires {p : DynamicCircuit Var n} :
      DynWires (fun w ↦ S_ctrl w ∧ S_tgt w) p → p.count .TOFF = 0 →
      DynCtrlSafe S_ctrl S_tgt p
  | seq {p₁ p₂ : DynamicCircuit Var n} :
      DynCtrlSafe S_ctrl S_tgt p₁ → DynCtrlSafe S_ctrl S_tgt p₂ →
      DynCtrlSafe S_ctrl S_tgt (p₁.seq p₂)
  | wrapOnReg (v : Var) {w : ℕ} (reg : QRegister w n) (cp : ComputeProg w)
      {mid : DynamicCircuit Var n} :
      (∀ u, S_ctrl (reg u)) →
      ComputeProgCtrlSafe (fun u ↦ S_ctrl (reg u)) (fun u ↦ S_tgt (reg u)) cp →
      DynCtrlSafe S_ctrl S_tgt mid →
      DynCtrlSafe S_ctrl S_tgt (wrapDynOnReg v reg cp mid)

theorem dynWires_mono_local {Var : Type} {n : ℕ} {P Q : Wire n → Prop} (hPQ : ∀ w, P w → Q w) :
    ∀ {p : DynamicCircuit Var n}, DynWires P p → DynWires Q p := by
  intro p hp
  induction p with
  | circuit c =>
      induction c with
      | identity => exact trivial
      | gate _ _ => exact fun i ↦ hPQ _ (hp i)
      | seq _ _ ih1 ih2 => exact ⟨ih1 hp.1, ih2 hp.2⟩
  | measure _ _ => exact fun i ↦ hPQ _ (hp i)
  | qIf _ _ _ ih1 ih2 | seq _ _ ih1 ih2 => exact ⟨ih1 hp.1, ih2 hp.2⟩

theorem DynCtrlSafe.to_dynWires {Var : Type} {n : ℕ} {S : Wire n → Prop}
    {p : DynamicCircuit Var n} (hp : DynCtrlSafe S S p) : DynWires S p := by
  induction hp with
  | of_dynWires hw _ => exact dynWires_mono_local (fun _ h ↦ h.1) hw
  | seq _ _ ih1 ih2 => exact ⟨ih1, ih2⟩
  | wrapOnReg v reg cp hReg _ _ ih =>
      exact PhotochemistrySolution.Stage4FineFast.dynWires_wrapDynOnReg v reg hReg cp ih

theorem DynCtrlSafe.identity {Var : Type} {n : ℕ} (S_ctrl S_tgt : Wire n → Prop) :
    DynCtrlSafe (Var := Var) S_ctrl S_tgt (.circuit .identity) :=
  .of_dynWires trivial rfl

theorem DynCtrlSafe.liftFinDyn {Var : Type} {n : ℕ} {S_ctrl S_tgt : Wire n → Prop}
    (f : [Fintype Var] → [DecidableEq Var] → DynamicCircuit Var n)
    (hf : ∀ [Fintype Var] [DecidableEq Var], DynCtrlSafe S_ctrl S_tgt f) :
    DynCtrlSafe S_ctrl S_tgt (liftFinDyn_c70 f) := by
  unfold liftFinDyn_c70
  exact match Classical.dec (Finite Var) with
    | .isFalse _ => .identity S_ctrl S_tgt
    | .isTrue hfin => @hf (@Fintype.ofFinite Var hfin) (Classical.decEq Var)

/-- `locQ` wire `r[0]` of a `(116 + W)`-wire `35`-coin `PortB` register. -/
abbrev wPotB35LocQ {W n : ℕ} (r : QRegister (116 + W) n) : Wire n := r ⟨0, by omega⟩
/-- `isScreen` wire `r[1]` of a `(116 + W)`-wire `35`-coin `PortB` register. -/
abbrev wPotB35IsScreen {W n : ℕ} (r : QRegister (116 + W) n) : Wire n := r ⟨1, by omega⟩
/-- `isPot` wire `r[2]` of a `(116 + W)`-wire `35`-coin `PortB` register. -/
abbrev wPotB35IsPot {W n : ℕ} (r : QRegister (116 + W) n) : Wire n := r ⟨2, by omega⟩
/-- `isNN` wire `r[4]` of a `(116 + W)`-wire `35`-coin `PortB` register. -/
abbrev wPotB35IsNN {W n : ℕ} (r : QRegister (116 + W) n) : Wire n := r ⟨4, by omega⟩
/-- `sp1` bit-0 wire `r[5]` of a `(116 + W)`-wire `35`-coin `PortB` register. -/
abbrev wPotB35Sp1B0 {W n : ℕ} (r : QRegister (116 + W) n) : Wire n := r ⟨5, by omega⟩
/-- `sp1` bit-1 wire `r[6]` of a `(116 + W)`-wire `35`-coin `PortB` register. -/
abbrev wPotB35Sp1B1 {W n : ℕ} (r : QRegister (116 + W) n) : Wire n := r ⟨6, by omega⟩
/-- `sp2` bit-0 wire `r[7]` of a `(116 + W)`-wire `35`-coin `PortB` register. -/
abbrev wPotB35Sp2B0 {W n : ℕ} (r : QRegister (116 + W) n) : Wire n := r ⟨7, by omega⟩
/-- `sp2` bit-1 wire `r[8]` of a `(116 + W)`-wire `35`-coin `PortB` register. -/
abbrev wPotB35Sp2B1 {W n : ℕ} (r : QRegister (116 + W) n) : Wire n := r ⟨8, by omega⟩
/-- `24`-wire `NucA` block `r[9..32]`. -/
abbrev rPotB35NucA {W n : ℕ} (r : QRegister (116 + W) n) : QRegister 24 n :=
  r.compose (QRegister.block 9 24 (by omega))
/-- `24`-wire `ElecA` block `r[33..56]`. -/
abbrev rPotB35ElecA {W n : ℕ} (r : QRegister (116 + W) n) : QRegister 24 n :=
  r.compose (QRegister.block 33 24 (by omega))
/-- `24`-wire packed `PortB` block `r[57..80]`. -/
abbrev rPotB35PortB {W n : ℕ} (r : QRegister (116 + W) n) : QRegister 24 n :=
  r.compose (QRegister.block 57 24 (by omega))
/-- `35`-wire inner coin block `r[81..115]` (`dLayout[7256..7290]`). -/
abbrev rPotBCoin35 {W n : ℕ} (r : QRegister (116 + W) n) : QRegister 35 n :=
  r.compose (QRegister.block 81 35 (by omega))
/-- `W`-wire clean work block `r[116..116 + W - 1]`. -/
abbrev rPotBWork35 {W n : ℕ} (r : QRegister (116 + W) n) : QRegister W n :=
  r.compose (QRegister.block 116 W le_rfl)

/-- `35`-inner-coin phase bit function `(isScreen, isNN, sp1, sp2, nA, nB, eA, eB, z35) → bit`. -/
abbrev PotBPhaseBit35Fn : Type :=
  Bool → Bool → Fin 4 → Fin 4 →
    (Fin 3 → Fin 256) → (Fin 3 → Fin 256) →
    (Fin 3 → Fin 256) → (Fin 3 → Fin 256) → BitAssignment 35 → ZMod 2

/-- `35`-inner-coin involutive swap `(isScreen, isNN, sp1, sp2, nA, nB, eA, eB, z35) → z35'`. -/
abbrev PotBCoinSwap35Fn : Type :=
  Bool → Bool → Fin 4 → Fin 4 →
    (Fin 3 → Fin 256) → (Fin 3 → Fin 256) →
    (Fin 3 → Fin 256) → (Fin 3 → Fin 256) → BitAssignment 35 → BitAssignment 35

/-- Routed Stage-4 flag validity on `r : QRegister (116 + W) n`. -/
def ValidPotBFlags35 {W n : ℕ} (r : QRegister (116 + W) n) (β : BitAssignment n) : Prop :=
  (β (wPotB35IsPot r) = 0 → β (wPotB35IsScreen r) = 0 ∧ β (wPotB35IsNN r) = 0) ∧
    (β (wPotB35IsScreen r) = 0 → β (wPotB35IsNN r) = 0)

/-- `35`-coin 3-port phase bit read from `r : QRegister (116 + W) n`. -/
abbrev potOraclePortB35BitEval {W n : ℕ} (phaseBit : PotBPhaseBit35Fn)
    (r : QRegister (116 + W) n) (δ : BitAssignment n) : ZMod 2 :=
  phaseBit (δ (wPotB35IsScreen r) == 1) (δ (wPotB35IsNN r) == 1)
    (speciesOfBits2 (δ (wPotB35Sp1B0 r)) (δ (wPotB35Sp1B1 r)))
    (speciesOfBits2 (δ (wPotB35Sp2B0 r)) (δ (wPotB35Sp2B1 r)))
    (coordOfReg24 (rPotB35NucA r) δ)
    (if δ (wPotB35IsNN r) == 1 then coordOfReg24 (rPotB35PortB r) δ else 0)
    (coordOfReg24 (rPotB35ElecA r) δ)
    (if δ (wPotB35IsNN r) == 1 then 0 else coordOfReg24 (rPotB35PortB r) δ)
    (fun k ↦ δ (rPotBCoin35 r k))

/-- `35`-coin 3-port inner-coin permutation read from `r : QRegister (116 + W) n`. -/
abbrev potOraclePortB35CoinEval {W n : ℕ} (coinSwap : PotBCoinSwap35Fn)
    (r : QRegister (116 + W) n) (δ : BitAssignment n) : BitAssignment 35 :=
  coinSwap (δ (wPotB35IsScreen r) == 1) (δ (wPotB35IsNN r) == 1)
    (speciesOfBits2 (δ (wPotB35Sp1B0 r)) (δ (wPotB35Sp1B1 r)))
    (speciesOfBits2 (δ (wPotB35Sp2B0 r)) (δ (wPotB35Sp2B1 r)))
    (coordOfReg24 (rPotB35NucA r) δ)
    (if δ (wPotB35IsNN r) == 1 then coordOfReg24 (rPotB35PortB r) δ else 0)
    (coordOfReg24 (rPotB35ElecA r) δ)
    (if δ (wPotB35IsNN r) == 1 then 0 else coordOfReg24 (rPotB35PortB r) δ)
    (fun k ↦ δ (rPotBCoin35 r k))

/-- Active gate boolean on `r : QRegister (116 + W) n`. -/
def potB35GateActive {W n : ℕ} (isCsel : Bool) (r : QRegister (116 + W) n) (δ : BitAssignment n) :
    Bool :=
  if isCsel then (δ (wPotB35LocQ r) == 1) && (δ (wPotB35IsPot r) == 1)
  else (δ (wPotB35IsPot r) == 1)

/-- Post-state of a reflected `35`-coin 3-port potential oracle on `mkKetOpW rW st 0`. -/
def potReflPortBSt35 {kCoin W n : ℕ} (coinSwapK : BitAssignment kCoin → PotBCoinSwap35Fn)
    (isCsel : Bool) (r : QRegister (116 + W) n) (rCoin : QRegister kCoin n)
    (st : BitAssignment n → BitAssignment n) (δ : BitAssignment n) : BitAssignment n :=
  if potB35GateActive isCsel r (st δ) then
    writeReg (st δ) (rPotBCoin35 r)
      (potOraclePortB35CoinEval (coinSwapK (fun j ↦ st δ (rCoin j))) r (st δ))
  else st δ

/-- Post-phase of a reflected `35`-coin 3-port potential oracle starting from zero phase. -/
def potReflPortBPh0_35 {kCoin W n : ℕ} (phaseBitK : BitAssignment kCoin → PotBPhaseBit35Fn)
    (isCsel : Bool) (r : QRegister (116 + W) n) (rCoin : QRegister kCoin n)
    (st : BitAssignment n → BitAssignment n) (δ : BitAssignment n) : ZMod 2 :=
  (if isCsel then st δ (wPotB35LocQ r) * st δ (wPotB35IsPot r) else st δ (wPotB35IsPot r)) *
    potOraclePortB35BitEval (phaseBitK (fun j ↦ st δ (rCoin j))) r (st δ)

/-- Per-fiber reflected Stage-4 potential slice specification on `35` inner coin wires. -/
structure ReflPotSliceSpec35 (potExpect : PotExpectFn) where
  phaseBit : PotBPhaseBit35Fn
  coinSwap : PotBCoinSwap35Fn
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
  avg_coin35 : ∀ (isScreen isNN : Bool) (sp1 sp2 : Fin 4) (nA nB eA eB : Fin 3 → Fin 256),
    (2 ^ 35 : ℂ)⁻¹ *
      (∑ z : BitAssignment 35, bitSign (phaseBit isScreen isNN sp1 sp2 nA nB eA eB z)) =
      (potExpect isScreen isNN sp1 sp2 nA nB eA eB : ℂ)

/--
Reflected `35`-inner-coin 3-port `PortB` Stage-4 potential oracle with asymmetric
`(tPotU, tPotC)` `T`-counts on `r : QRegister (116 + Wp) n`.
-/
structure Stage4ReflCoin35PotOraclePortB (kCoin Wp tPotU tPotC : ℕ)
    (potExpectK : BitAssignment kCoin → PotExpectFn) where
  phaseBitK : BitAssignment kCoin → PotBPhaseBit35Fn
  coinSwapK : BitAssignment kCoin → PotBCoinSwap35Fn
  pCsel : ∀ {Var : Type} {n : ℕ}, Var → QRegister (116 + Wp) n → QRegister kCoin n →
      DynamicCircuit Var n
  pUsel : ∀ {Var : Type} {n : ℕ}, Var → QRegister (116 + Wp) n → QRegister kCoin n →
      DynamicCircuit Var n
  coinSwap_invol : ∀ γ s nn sp1 sp2 nA nB eA eB z,
    coinSwapK γ s nn sp1 sp2 nA nB eA eB (coinSwapK γ s nn sp1 sp2 nA nB eA eB z) = z
  phaseBit_coinSwap : ∀ γ s nn sp1 sp2 nA nB eA eB z,
    phaseBitK γ s nn sp1 sp2 nA nB eA eB (coinSwapK γ s nn sp1 sp2 nA nB eA eB z) =
      phaseBitK γ s nn sp1 sp2 nA nB eA eB z
  phaseBit_port : ∀ γ s nn sp1 sp2 nA nB eA eB z,
    phaseBitK γ s nn sp1 sp2 nA (if nn then nB else 0) eA (if nn then 0 else eB) z =
      phaseBitK γ s nn sp1 sp2 nA nB eA eB z
  coinSwap_port : ∀ γ s nn sp1 sp2 nA nB eA eB z,
    coinSwapK γ s nn sp1 sp2 nA (if nn then nB else 0) eA (if nn then 0 else eB) z =
      coinSwapK γ s nn sp1 sp2 nA nB eA eB z
  step_and_counts : ∀ {Var : Type} [Fintype Var] [DecidableEq Var]
    {m n : ℕ} [NeZero (2 ^ n)] (v : Var) (rW : QRegister m n)
    (r : QRegister (116 + Wp) n) (rCoin : QRegister kCoin n)
    (_ : r.DisjointWires rCoin) (isCsel : Bool) (st : BitAssignment n → BitAssignment n),
    (∀ δ, (∀ q : Fin m, δ (rW q) = 0) → ValidPotBFlags35 r (st δ)) →
    (∀ δ (u : Fin Wp), (∀ q : Fin m, δ (rW q) = 0) → st δ (rPotBWork35 r u) = 0) →
    let p := if isCsel then pCsel v r rCoin else pUsel v r rCoin
    SubspaceStep (mkKetOpW rW st (fun _ ↦ 0))
      (mkKetOpW rW (potReflPortBSt35 coinSwapK isCsel r rCoin st)
        (potReflPortBPh0_35 phaseBitK isCsel r rCoin st)) p ∧
    p.count .T = (if isCsel then tPotC else tPotU) ∧
    p.count .TOFF = 0
  dynWires : ∀ {Var : Type} {n : ℕ} (S : Wire n → Prop) (v : Var)
    (r : QRegister (116 + Wp) n) (rCoin : QRegister kCoin n),
    (∀ i : Fin (116 + Wp), S (r i)) → (∀ j : Fin kCoin, S (rCoin j)) →
    DynWires S (pCsel v r rCoin) ∧ DynWires S (pUsel v r rCoin)
  avg_coin35 : ∀ (γ : BitAssignment kCoin) (isScreen isNN : Bool) (sp1 sp2 : Fin 4)
    (nA nB eA eB : Fin 3 → Fin 256),
    (2 ^ 35 : ℂ)⁻¹ *
      (∑ zc : BitAssignment 35, bitSign (phaseBitK γ isScreen isNN sp1 sp2 nA nB eA eB zc)) =
      (potExpectK γ isScreen isNN sp1 sp2 nA nB eA eB : ℂ)

/-- Extract the per-`γ` `ReflPotSliceSpec35` from a `Stage4ReflCoin35PotOraclePortB`. -/
def Stage4ReflCoin35PotOraclePortB.slice {kCoin Wp tPotU tPotC : ℕ}
    {potExpectK : BitAssignment kCoin → PotExpectFn}
    (o : Stage4ReflCoin35PotOraclePortB kCoin Wp tPotU tPotC potExpectK)
    (γ : BitAssignment kCoin) : ReflPotSliceSpec35 (potExpectK γ) where
  phaseBit := o.phaseBitK γ
  coinSwap := o.coinSwapK γ
  coinSwap_invol := o.coinSwap_invol γ
  phaseBit_coinSwap := o.phaseBit_coinSwap γ
  phaseBit_port := o.phaseBit_port γ
  coinSwap_port := o.coinSwap_port γ
  avg_coin35 := o.avg_coin35 γ
end Safety

/-
Section 1B: Standalone `CLB(6, 5)` coin embedding and `CoulOWPkg21` interface (`0` legacy stack
imports).
-/

/-- Shared `6`-bit low prefix `γ_6` of `wp = w ^^^ 1365` (`wp[10..5]` bit-reversed). -/
def clbGam6 (w : ℕ) : ℕ :=
  let wp := w ^^^ 1365
  ((wp / 1024) % 2) + 2 * ((wp / 512) % 2) + 4 * ((wp / 256) % 2) +
  8 * ((wp / 128) % 2) + 16 * ((wp / 64) % 2) + 32 * ((wp / 32) % 2)
theorem clbGam6_lt (w : ℕ) : clbGam6 w < 64 := by unfold clbGam6; dsimp only; omega

theorem mux_le14_30 : 14 ≤ 30 := by decide

/- Section 2A: Parametric `(Leg1, Leg2, Mid)` package and `35`-coin reflected arithmetic. -/

/-- Stage-4 `(v1Fin8, v2Fin8)` radial table bundle for `Mux48`. -/
structure OWLegsMidPkg (isU10 : Bool) (tLeg1 tLeg2 kMid tMid : ℕ) where
  v1Fin8 : Bool → Bool → Fin 4 → Fin 8 → ℕ
  v2Fin8 : Bool → Bool → Fin 4 → Fin 8 → ℕ

theorem refl16_invol_and_div {u : ℕ} (hu : u < 2 ^ 16) (s : ℕ) :
    let u' := 2 ^ 16 - 1 - (u + s) % 2 ^ 16
    u' < 2 ^ 16 ∧ 2 ^ 16 - 1 - (u' + s) % 2 ^ 16 = u ∧ (u' + s) / 2 ^ 16 = (u + s) / 2 ^ 16 := by
  dsimp only
  omega

theorem finBitsVal_of_testBit : ∀ (m u : ℕ),
    finBitsVal (fun j : Fin m ↦ if u.testBit j.val then (1 : ZMod 2) else 0) = u % 2 ^ m
  | 0, _ => by simp [finBitsVal, Nat.mod_one]
  | m + 1, u => by
      unfold finBitsVal
      rw [show (if u.testBit (0 : Fin (m + 1)).val then (1 : ZMod 2) else 0).val = u % 2 by
          rw [Fin.val_zero, Nat.testBit_zero]
          rcases Nat.mod_two_eq_zero_or_one u with h | h <;> simp only [h] <;> decide,
        show (fun i : Fin m ↦ if u.testBit i.succ.val then (1 : ZMod 2) else 0) =
          fun i : Fin m ↦ if (u / 2).testBit i.val then (1 : ZMod 2) else 0 from
          funext fun i ↦ by rw [Fin.val_succ, Nat.testBit_add, pow_one],
        finBitsVal_of_testBit m (u / 2), pow_succ']
      have hu2 : u = (u % 2 + 2 * ((u / 2) % 2 ^ m)) + (2 * 2 ^ m) * ((u / 2) / 2 ^ m) := by
        conv_lhs => rw [(Nat.mod_add_div u 2).symm, (Nat.mod_add_div (u / 2) (2 ^ m)).symm]
        ring
      have := Nat.mod_lt (u / 2) (Nat.two_pow_pos m)
      conv_rhs => rw [hu2, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]

theorem natOfZModBits_of_testBit (m u : ℕ) :
    natOfZModBits m (fun j : Fin m ↦ if u.testBit j.val then (1 : ZMod 2) else 0) = u % 2 ^ m := by
  rw [← finBitsVal_eq_natOfZModBits, finBitsVal_of_testBit]

/- Section 3: `r41Of35` / `rC21Of35` adapters, `Wtop` pool layout, and `Mux48` sub-registers. -/

/-- Effective non-gate clean pool width (`Wp - 1` on `Csel`, `Wp` on `Usel`). -/
def Wtop (Wp : ℕ) (isCsel : Bool) : ℕ := if isCsel then Wp - 1 else Wp

theorem wtop_ge192 {Wp : ℕ} (h193 : 193 ≤ Wp) (isCsel : Bool) : 192 ≤ Wtop Wp isCsel := by
  unfold Wtop; cases isCsel <;> simp only [↓reduceIte, Bool.false_eq_true] <;> omega
theorem wtop_le_wp (Wp : ℕ) (isCsel : Bool) : Wtop Wp isCsel ≤ Wp := by
  unfold Wtop; cases isCsel <;> simp only [↓reduceIte, Bool.false_eq_true] <;> omega
theorem wp_sub1_le_wtop (Wp : ℕ) (isCsel : Bool) : Wp - 1 ≤ Wtop Wp isCsel := by
  unfold Wtop; cases isCsel <;> simp only [↓reduceIte, Bool.false_eq_true] <;> omega

def IsNonNucPortB41Idx (m : ℕ) : Prop := m < 9 ∨ (33 ≤ m ∧ m < 57) ∨ 81 ≤ m

theorem r41_ne {Wp n : ℕ} (r41 : QRegister (122 + Wp) n) {a b : ℕ} (ha : a < 122 + Wp)
    (hb : b < 122 + Wp) (hne : a ≠ b) :
    r41 ⟨a, ha⟩ ≠ r41 ⟨b, hb⟩ := fun e ↦ hne (congrArg Fin.val (r41.wires.injective e))
theorem r41_idx_ne {Wp n : ℕ} (r41 : QRegister (122 + Wp) n) (i j : Fin (122 + Wp))
    (hne : i.val ≠ j.val) :
    r41 i ≠ r41 j := fun e ↦ hne (congrArg Fin.val (r41.wires.injective e))
theorem r41_blk_ne_blk {Wp a₁ b₁ a₂ b₂ n : ℕ} (r41 : QRegister (122 + Wp) n)
    {h₁ : a₁ + b₁ ≤ 122 + Wp} {h₂ : a₂ + b₂ ≤ 122 + Wp}
    (i : Fin b₁) (j : Fin b₂) (hne : a₁ + i.val ≠ a₂ + j.val) :
    (r41.compose (QRegister.block a₁ b₁ h₁)) i ≠ (r41.compose (QRegister.block a₂ b₂ h₂)) j :=
  r41_idx_ne r41 _ _ (by rwa [QRegister.block_apply_val, QRegister.block_apply_val])
theorem r41_blk_ne_wire {Wp a b n : ℕ} (r41 : QRegister (122 + Wp) n) {h : a + b ≤ 122 + Wp}
    (i : Fin b) {m : ℕ} (hm : m < 122 + Wp) (hne : a + i.val ≠ m) :
    (r41.compose (QRegister.block a b h)) i ≠ r41 ⟨m, hm⟩ :=
  r41_idx_ne r41 _ _ (by rwa [QRegister.block_apply_val])
theorem r41_wire_ne_blk {Wp a b n : ℕ} (r41 : QRegister (122 + Wp) n) {m : ℕ} (hm : m < 122 + Wp)
    {h : a + b ≤ 122 + Wp} (i : Fin b) (hne : m ≠ a + i.val) : r41 ⟨m, hm⟩ ≠
      (r41.compose (QRegister.block a b h)) i :=
  (r41_blk_ne_wire r41 i hm hne.symm).symm
theorem r41_blk_tgt {Wp a b n : ℕ} {S_tgt : Wire n → Prop} (r41 : QRegister (122 + Wp) n)
    {h : a + b ≤ 122 + Wp} (hTr : ∀ k : Fin (122 + Wp), IsNonNucPortB41Idx k.val → S_tgt (r41 k))
    (i : Fin b) (hi : a + i.val < 9 ∨ (33 ≤ a + i.val ∧ a + i.val < 57) ∨ 81 ≤ a + i.val) :
    S_tgt ((r41.compose (QRegister.block a b h)) i) :=
  hTr ((QRegister.block a b h) i) (by rwa [QRegister.block_apply_val])
theorem r41_blk_st {Wp a b n : ℕ} {S_ctrl S_tgt : Wire n → Prop} (r41 : QRegister (122 + Wp) n)
    {h : a + b ≤ 122 + Wp}
    (hST : ∀ k : Fin (122 + Wp), IsNonNucPortB41Idx k.val → S_ctrl (r41 k) ∧ S_tgt (r41 k))
    (i : Fin b) (hi : a + i.val < 9 ∨ (33 ≤ a + i.val ∧ a + i.val < 57) ∨ 81 ≤ a + i.val) :
    S_ctrl ((r41.compose (QRegister.block a b h)) i) ∧
        S_tgt ((r41.compose (QRegister.block a b h)) i) :=
  hST ((QRegister.block a b h) i) (by rwa [QRegister.block_apply_val])

/-- `16`-wire high-coin block `r41[106..121]` (`Z[14..29]`). -/
abbrev rMuxZ16 {Wp n : ℕ} (r41 : QRegister (122 + Wp) n) : QRegister 16 n :=
  r41.compose (QRegister.block 106 16 (by omega))
/-- Active gate wire on `r41` (`r41[122 + Wp - 1]` on `Csel`, `r41[2]` on `Usel`). -/
abbrev wMuxGate {Wp n : ℕ} (h193 : 193 ≤ Wp) (isCsel : Bool) (r41 : QRegister (122 + Wp) n) :
    Wire n :=
  if isCsel then r41 ⟨122 + Wp - 1, by omega⟩ else r41 ⟨2, by omega⟩
/-- Clean scratch bit `r41[122]` shared as temporary XOR wire during `Mux2`. -/
abbrev wMuxScr0 {Wp n : ℕ} (h193 : 193 ≤ Wp) (r41 : QRegister (122 + Wp) n) : Wire n :=
  r41 ⟨122, by omega⟩
/-- `18`-wire `d^2` block `r41[122..139]`. -/
abbrev rMuxD2_18 {Wp n : ℕ} (h193 : 193 ≤ Wp) (r41 : QRegister (122 + Wp) n) : QRegister 18 n :=
  r41.compose (QRegister.block 122 18 (by omega))
abbrev rMuxCopy24 {Wp n : ℕ} (h193 : 193 ≤ Wp) (r41 : QRegister (122 + Wp) n) : QRegister 24 n :=
  r41.compose (QRegister.block 242 24 (by omega))
/-- `24`-wire `Mux1` target block `r41[122 + Wtop - 48 .. 122 + Wtop - 25]`. -/
abbrev rMuxM1 {Wp n : ℕ} (h193 : 193 ≤ Wp) (isCsel : Bool) (r41 : QRegister (122 + Wp) n) :
    QRegister 24 n :=
  r41.compose (QRegister.block (122 + Wtop Wp isCsel - 48) 24
    (by have := wtop_ge192 h193 isCsel; have := wtop_le_wp Wp isCsel; omega))
/-- `24`-wire `Mux2` target block `r41[122 + Wtop - 24 .. 122 + Wtop - 1]`. -/
abbrev rMuxM2 {Wp n : ℕ} (h193 : 193 ≤ Wp) (isCsel : Bool) (r41 : QRegister (122 + Wp) n) :
    QRegister 24 n :=
  r41.compose (QRegister.block (122 + Wtop Wp isCsel - 24) 24
    (by have := wtop_ge192 h193 isCsel; have := wtop_le_wp Wp isCsel; omega))

def idxMuxLeg1Hdr5 (Wp : ℕ) (isCsel : Bool) (u : Fin 5) : ℕ :=
  match u.val with
  | 0 => if isCsel then 122 + Wp - 1 else 2
  | 1 => if isCsel then 240 else 1
  | 2 => if isCsel then 241 else 4
  | 3 => 5
  | _ => 6

theorem idxMuxLeg1Hdr5_lt {Wp : ℕ} (h193 : 193 ≤ Wp) (isCsel : Bool) (u : Fin 5) :
    idxMuxLeg1Hdr5 Wp isCsel u < 122 + Wp := by
  fin_cases u <;> cases isCsel <;> simp only [idxMuxLeg1Hdr5, ↓reduceIte, Bool.false_eq_true] <;>
      omega

theorem fMuxLeg1Hdr5_inj {Wp : ℕ} (h193 : 193 ≤ Wp) (isCsel : Bool) :
    Function.Injective (fun u : Fin 5 ↦
      (⟨idxMuxLeg1Hdr5 Wp isCsel u, idxMuxLeg1Hdr5_lt h193 isCsel u⟩ : Fin (122 + Wp))) := by
  intro a b heq
  have hv := congrArg Fin.val heq
  fin_cases a <;> fin_cases b <;> cases isCsel <;>
    simp only [idxMuxLeg1Hdr5, ↓reduceIte, Bool.false_eq_true] at hv ⊢ <;> omega

/-- `5`-wire Leg 1 header register on `r41`. -/
def rMuxLeg1Hdr5 {Wp n : ℕ} (h193 : 193 ≤ Wp) (isCsel : Bool) (r41 : QRegister (122 + Wp) n) :
    QRegister 5 n :=
  r41.compose ⟨⟨fun u ↦ ⟨idxMuxLeg1Hdr5 Wp isCsel u, idxMuxLeg1Hdr5_lt h193 isCsel u⟩,
    fMuxLeg1Hdr5_inj h193 isCsel⟩⟩

def idxMuxMid (Wp : ℕ) (isCsel : Bool) (u : ℕ) : ℕ :=
  if u = 0 then (if isCsel then 122 + Wp - 1 else 2)
  else if u = 1 then 1 else if u = 2 then 4 else if u = 3 then 5 else if u = 4 then 6
  else if u < 41 then 140 + (u - 5) else if u < 71 then 92 + (u - 41) else 176 + (u - 71)

theorem idxMuxMid_lt {Wp kMid kRest M : ℕ} (h193 : 193 ≤ Wp) (isCsel : Bool) (_hM : M ≤ 24)
    (hCap : 54 + kRest + (48 - M) ≤ Wtop Wp isCsel) (hkM : kMid ≤ kRest) (u : Fin (71 + kMid)) :
    idxMuxMid Wp isCsel u.val < 122 + Wp := by
  have hw := wtop_le_wp Wp isCsel
  unfold idxMuxMid
  split_ifs <;> omega

theorem fMuxMid_inj {Wp kMid kRest M : ℕ} (h193 : 193 ≤ Wp) (isCsel : Bool) (hM : M ≤ 24)
    (hCap : 54 + kRest + (48 - M) ≤ Wtop Wp isCsel) (hkM : kMid ≤ kRest) :
    Function.Injective (fun u : Fin (71 + kMid) ↦
      (⟨idxMuxMid Wp isCsel u.val, idxMuxMid_lt h193 isCsel hM hCap hkM u⟩ : Fin (122 + Wp))) := by
  let inv (x : ℕ) := if x = (if isCsel then 122 + Wp - 1 else 2) then 0
    else if x = 1 then 1 else if x = 4 then 2 else if x = 5 then 3 else if x = 6 then 4
    else if x < 122 then 41 + (x - 92) else if x < 176 then 5 + (x - 140) else 71 + (x - 176)
  have hinv (u : Fin (71 + kMid)) : inv (idxMuxMid Wp isCsel u.val) = u.val := by
    have := u.isLt
    unfold idxMuxMid
    cases isCsel <;> simp only [Wtop, Bool.false_eq_true, ↓reduceIte] at hCap ⊢ <;>
      split_ifs <;> dsimp only [inv] <;> simp only [Bool.false_eq_true, ↓reduceIte] <;>
      (try split_ifs) <;> omega
  exact fun a b h ↦ Fin.ext ((hinv a).symm.trans ((congrArg (inv ∘ Fin.val) h).trans (hinv b)))

/-- `(71 + kMid)`-wire `Mid_OW` register on `r41`. -/
def rMuxMid {Wp kMid kRest M n : ℕ} (h193 : 193 ≤ Wp) (isCsel : Bool) (hM : M ≤ 24)
    (hCap : 54 + kRest + (48 - M) ≤ Wtop Wp isCsel) (hkM : kMid ≤ kRest)
    (r41 : QRegister (122 + Wp) n) : QRegister (71 + kMid) n :=
  r41.compose ⟨⟨fun u ↦ ⟨idxMuxMid Wp isCsel u.val, idxMuxMid_lt h193 isCsel hM hCap hkM u⟩,
    fMuxMid_inj h193 isCsel hM hCap hkM⟩⟩

section PrimsA
attribute [local semireducible]
  PhotochemistrySolution.KinB.ComputeProg.finalClean
  PhotochemistrySolution.KinB.ComputeProg.ValidProg
  PhotochemistrySolution.KinB.ComputeProg.numAnd
  PhotochemistrySolution.KinB.ComputeProg.fwdBits

/- Section 4A: Small tuple registers, reversible `ComputeProg` gadgets, and `writeSub24`. -/

theorem subspaceStep_of_eq_pre_local {Var : Type} [Fintype Var] [DecidableEq Var]
    {n : ℕ} [NeZero (2 ^ n)] {A A' B : Operator (2 ^ n)} {p : DynamicCircuit Var n}
    (hEq : A = A') (h : SubspaceStep A' B p) : SubspaceStep A B p :=
  hEq ▸ h

/-- `2`-wire tuple register `[w0, w1]`. -/
def rReg2 {n : ℕ} (w0 w1 : Wire n) (h01 : w0 ≠ w1) : QRegister 2 n :=
  ⟨⟨fun i ↦ if i.val = 0 then w0 else w1, fun a b hab ↦ by
    fin_cases a <;> fin_cases b <;> first | rfl | exact False.elim (by simp_all)⟩⟩

/-- `3`-wire tuple register `[w0, w1, w2]`. -/
def rReg3 {n : ℕ} (w0 w1 w2 : Wire n) (h01 : w0 ≠ w1) (h02 : w0 ≠ w2)
    (h12 : w1 ≠ w2) : QRegister 3 n :=
  ⟨⟨fun i ↦ if i.val = 0 then w0 else if i.val = 1 then w1 else w2, fun a b hab ↦ by
    fin_cases a <;> fin_cases b <;> first | rfl | exact False.elim (by simp_all)⟩⟩

/-- `4`-wire tuple register `[w0, w1, w2, w3]`. -/
def rReg4 {n : ℕ} (w0 w1 w2 w3 : Wire n)
    (h01 : w0 ≠ w1) (h02 : w0 ≠ w2) (h03 : w0 ≠ w3)
    (h12 : w1 ≠ w2) (h13 : w1 ≠ w3) (h23 : w2 ≠ w3) : QRegister 4 n :=
  ⟨⟨fun i ↦ if i.val = 0 then w0 else if i.val = 1 then w1 else if i.val = 2 then w2 else w3,
    fun a b hab ↦ by fin_cases a <;> fin_cases b <;> first | rfl | exact False.elim (by simp_all)⟩⟩

/-- `5`-wire tuple register `[w0, w1, w2, w3, w4]`. -/
def rReg5 {n : ℕ} (w0 w1 w2 w3 w4 : Wire n)
    (h01 : w0 ≠ w1) (h02 : w0 ≠ w2) (h03 : w0 ≠ w3) (h04 : w0 ≠ w4)
    (h12 : w1 ≠ w2) (h13 : w1 ≠ w3) (h14 : w1 ≠ w4)
    (h23 : w2 ≠ w3) (h24 : w2 ≠ w4) (h34 : w3 ≠ w4) : QRegister 5 n :=
  ⟨⟨fun i ↦ if i.val = 0 then w0 else if i.val = 1 then w1 else if i.val = 2 then w2
      else if i.val = 3 then w3 else w4,
    fun a b hab ↦ by fin_cases a <;> fin_cases b <;> first | rfl | exact False.elim (by simp_all)⟩⟩

theorem stepCB_apply_reg {m n : ℕ} (r : QRegister m n) (f : BitAssignment m → BitAssignment m)
    (δ : BitAssignment n) (j : Fin m) : stepCB r f δ (r j) = f (fun k ↦ δ (r k)) j :=
  writeReg_apply_reg δ r _ j

theorem stepCB_apply_out {m n : ℕ} (r : QRegister m n) (f : BitAssignment m → BitAssignment m)
    (δ : BitAssignment n) {w : Wire n} (hw : ∀ k : Fin m, w ≠ r k) : stepCB r f δ w = δ w :=
  writeReg_apply_of_not_mem δ r _ w (fun ⟨k, hk⟩ ↦ hw k hk.symm)

theorem stepCB_apply_ne {m n : ℕ} (r : QRegister m n) (f : BitAssignment m →
  BitAssignment m)
    (δ : BitAssignment n) (t : Fin m) (hKeep : ∀ u : Fin m, u ≠ t → f (fun k ↦ δ
      (r k)) u = δ (r u))
    {w : Wire n} (hw : w ≠ r t) : stepCB r f δ w = δ w := by
  if hm : ∃ u : Fin m, r u = w then
    obtain ⟨u, rfl⟩ := hm
    exact (stepCB_apply_reg r f δ u).trans (hKeep u fun h ↦ hw (congrArg r.wires h))
  else exact stepCB_apply_out r f δ fun u h ↦ hm ⟨u, h.symm⟩

theorem writeReg_eq_of_reg_out {m n : ℕ} (r : QRegister m n) (vals : Fin m → ZMod 2)
    (δ γ : BitAssignment n) (hReg : ∀ u : Fin m, vals u = γ (r u))
    (hOut : ∀ w : Wire n, (∀ u : Fin m, w ≠ r u) → δ w = γ w) : writeReg δ r vals = γ := by
  funext w
  if hm : ∃ u : Fin m, r u = w then
    obtain ⟨u, rfl⟩ := hm
    exact (writeReg_apply_reg δ r vals u).trans (hReg u)
  else
    exact (writeReg_apply_of_not_mem δ r vals w fun ⟨u, hu⟩ ↦ hm ⟨u, hu⟩).trans
      (hOut w fun u h ↦ hm ⟨u, h.symm⟩)

/-- `0`-AND reversible `CNOT(0, 1)` program on `Wire 2`. -/
def cpCnot2 : ComputeProg 2 := .cnot 0 1 (by decide)
theorem cpCnot2_vp : cpCnot2.ValidProg ∅ ∅ := by dsimp only [cpCnot2, ComputeProg.ValidProg]; decide
theorem cpCnot2_and : cpCnot2.numAnd = 0 := rfl
theorem cpCnot2_fwd (b : BitAssignment 2) :
    cpCnot2.fwdBits b 0 = b 0 ∧ cpCnot2.fwdBits b 1 = b 1 + b 0 := by
  simp [cpCnot2, ComputeProg.fwdBits]

/-- `1`-AND reversible `AND(0, 1 -> 2)` program on `Wire 3`. -/
def cpAnd3 : ComputeProg 3 := .andGate 0 1 2 (by decide) (by decide) (by decide)
theorem cpAnd3_vp : cpAnd3.ValidProg ∅ ({2} : Finset (Wire 3)) := by
  dsimp only [cpAnd3, ComputeProg.ValidProg]; decide
theorem cpAnd3_and : cpAnd3.numAnd = 1 := rfl
theorem cpAnd3_fwd (b : BitAssignment 3) :
    cpAnd3.fwdBits b 0 = b 0 ∧ cpAnd3.fwdBits b 1 = b 1 ∧ cpAnd3.fwdBits b 2 = b 2 + b 0 * b 1 := by
  simp [cpAnd3, ComputeProg.fwdBits]

/-- `2`-AND `Csel` header cascade `s0G := g & s0; n0G := s0G & n0` on `Wire 5`. -/
def cpHdr2 : ComputeProg 5 :=
  .seq (.andGate 0 1 3 (by decide) (by decide) (by decide))
    (.andGate 3 2 4 (by decide) (by decide) (by decide))
theorem cpHdr2_vp : cpHdr2.ValidProg ∅ ({3, 4} : Finset (Wire 5)) := by
  dsimp only [cpHdr2, ComputeProg.ValidProg, ComputeProg.finalClean]; decide
theorem cpHdr2_and : cpHdr2.numAnd = 2 := rfl
theorem cpHdr2_fwd (b : BitAssignment 5) :
    cpHdr2.fwdBits b 0 = b 0 ∧ cpHdr2.fwdBits b 1 = b 1 ∧ cpHdr2.fwdBits b 2 = b 2 ∧
    cpHdr2.fwdBits b 3 = b 3 + b 0 * b 1 ∧ cpHdr2.fwdBits b 4 = b 4 + (b 3 + b 0 * b 1) * b 2 := by
  simp [cpHdr2, ComputeProg.fwdBits]

def writeSub24 {n : ℕ} (β : BitAssignment n) (rDst : QRegister 24 n) (m k : ℕ)
    (f : Fin 24 → ZMod 2) :
    BitAssignment n :=
  writeReg β rDst (fun i ↦ if m ≤ i.val ∧ i.val < m + k then f i else β (rDst i))

theorem writeSub24_apply_reg {n : ℕ} (β : BitAssignment n) (rDst : QRegister 24 n)
    (m k : ℕ) (f : Fin 24 → ZMod 2) (i : Fin 24) :
    writeSub24 β rDst m k f (rDst i) = if m ≤ i.val ∧ i.val < m + k then f i else β (rDst i) :=
  writeReg_apply_reg β rDst _ i

theorem writeSub24_apply_out {n : ℕ} (β : BitAssignment n) (rDst : QRegister 24 n)
    (m k : ℕ) (f : Fin 24 → ZMod 2) {w : Wire n} (hw : ∀ i : Fin 24, w ≠ rDst i) :
    writeSub24 β rDst m k f w = β w :=
  writeReg_apply_of_not_mem β rDst _ w (fun ⟨i, hi⟩ ↦ hw i hi.symm)

theorem writeSub24_zero {n : ℕ} (β : BitAssignment n) (rDst : QRegister 24 n) (m : ℕ)
    (f : Fin 24 → ZMod 2) :
    writeSub24 β rDst m 0 f = β := by
  unfold writeSub24
  exact writeReg_eq_of_reg_out rDst _ β β (fun _ ↦ by split_ifs <;> first | omega | rfl)
      (fun _ _ ↦ rfl)

theorem writeSub24_full {n : ℕ} (β : BitAssignment n) (rDst : QRegister 24 n)
    (f : Fin 24 → ZMod 2) :
    writeSub24 β rDst 0 24 f = writeReg β rDst f := by
  unfold writeSub24
  exact congrArg (writeReg β rDst) (funext fun i ↦ ite_eq_left ⟨Nat.zero_le _, i.isLt⟩)

theorem writeSub24_succ_of_step {n : ℕ} (β β' : BitAssignment n) (rDst : QRegister 24 n)
    (m k : ℕ) (hm : m + k < 24) (f : Fin 24 → ZMod 2)
    (hOut : ∀ w : Wire n, w ≠ rDst ⟨m + k, hm⟩ → β' w = β w)
    (hHit : β' (rDst ⟨m + k, hm⟩) = f ⟨m + k, hm⟩) :
    writeSub24 β' rDst m k f = writeSub24 β rDst m (k + 1) f := by
  funext w
  if hw : ∃ i : Fin 24, rDst i = w then
    obtain ⟨i, rfl⟩ := hw
    rw [writeSub24_apply_reg, writeSub24_apply_reg]
    split_ifs
    · rfl
    · omega
    · rw [show i = ⟨m + k, hm⟩ from Fin.ext (by dsimp; omega)]
      exact hHit
    · exact hOut _ fun e ↦ (show i.val ≠ m + k by omega) (congrArg Fin.val (rDst.wires.injective e))
  else
    have hno (i : Fin 24) (h : w = rDst i) : False := hw ⟨i, h.symm⟩
    exact (writeSub24_apply_out _ _ _ _ _ hno).trans
      ((hOut w (hno _)).trans (writeSub24_apply_out _ _ _ _ _ hno).symm)

/--
`1`-AND `Mux1` `Dist18` gadget `CNOT 1 2 ; AND 0 2 3 ; CNOT 1 2 ; CNOT 2 3`
(`0, 1` control-only; `2` restored; `3` receives `b 3 + b 0 * (b 2 + b 1) + b 2`).
-/
def cpMux1Dist4 : ComputeProg 4 :=
  .seq (.cnot 1 2 (by decide))
    (.seq (.andGate 0 2 3 (by decide) (by decide) (by decide))
      (.seq (.cnot 1 2 (by decide)) (.cnot 2 3 (by decide))))
theorem cpMux1Dist4_vp : cpMux1Dist4.ValidProg ∅ ({3} : Finset (Wire 4)) := by
  dsimp only [cpMux1Dist4, ComputeProg.ValidProg, ComputeProg.finalClean]; decide
theorem cpMux1Dist4_and : cpMux1Dist4.numAnd = 1 := rfl
theorem cpMux1Dist4_fwd (b : BitAssignment 4) :
    cpMux1Dist4.fwdBits b 0 = b 0 ∧ cpMux1Dist4.fwdBits b 1 = b 1 ∧
    cpMux1Dist4.fwdBits b 2 = b 2 ∧ cpMux1Dist4.fwdBits b 3 = b 3 + b 0 * (b 2 + b 1) + b 2 := by
  have h22 (x y : ZMod 2) : (x + y) + y = x := by
    rcases DynCircExt.bit_cases x with rfl | rfl <;>
      rcases DynCircExt.bit_cases y with rfl | rfl <;> rfl
  simp [cpMux1Dist4, ComputeProg.fwdBits, h22]

/--
`0` -AND `Leg2` XOR-flip gadget `CNOT 0 2 ; CNOT 1 2` (`0, 1` control-only; `2` receives
`b 2 + b 0 + b 1` ).
-/
def cpFlipLeg2_3 : ComputeProg 3 := .seq (.cnot 0 2 (by decide)) (.cnot 1 2 (by decide))
theorem cpFlipLeg2_3_vp : cpFlipLeg2_3.ValidProg ∅ ∅ := by
  dsimp only [cpFlipLeg2_3, ComputeProg.ValidProg, ComputeProg.finalClean]; decide
theorem cpFlipLeg2_3_and : cpFlipLeg2_3.numAnd = 0 := rfl
theorem cpFlipLeg2_3_fwd (b : BitAssignment 3) :
    cpFlipLeg2_3.fwdBits b 0 = b 0 ∧ cpFlipLeg2_3.fwdBits b 1 = b 1 ∧
    cpFlipLeg2_3.fwdBits b 2 = (b 2 + b 0) + b 1 := by
  simp [cpFlipLeg2_3, ComputeProg.fwdBits]
end PrimsA

/- Section 4B: Generic `24`-bit range wrapper and instantiated `Mux48` / header gadgets. -/

theorem coordOfReg24_congr {n : ℕ} (rA rB : QRegister 24 n) (s1 s2 : BitAssignment n)
    (h : ∀ i : Fin 24, s1 (rA i) = s2 (rB i)) : coordOfReg24 rA s1 = coordOfReg24 rB s2 := by
  funext ax; dsimp only [coordOfReg24]; congr 1; funext k; exact h _

theorem coordOfReg24_ite {n : ℕ} (c : Bool) (rDst rT rF : QRegister 24 n)
    (sDst sTF : BitAssignment n)
    (h : ∀ i : Fin 24, sDst (rDst i) = if c then sTF (rT i) else sTF (rF i)) :
    coordOfReg24 rDst sDst = if c then coordOfReg24 rT sTF else coordOfReg24 rF sTF := by
  cases c <;> simp only [Bool.false_eq_true, ↓reduceIte] <;>
    exact coordOfReg24_congr _ _ _ _ fun i ↦ by simpa using h i

theorem mux1Dist_bit_eq_ite (nn n e : ZMod 2) :
    (0 : ZMod 2) + (nn * (e + n) + e) = if nn == 1 then n else e := by
  rcases DynCircExt.bit_cases nn with rfl | rfl <;>
    rcases DynCircExt.bit_cases n with rfl | rfl <;>
    rcases DynCircExt.bit_cases e with rfl | rfl <;> decide

theorem mux1Leg2_bit_eq_ite (nn n e : ZMod 2) :
    (if nn == 1 then n else e) + (n + e) = if nn == 1 then e else n := by
  rcases DynCircExt.bit_cases nn with rfl | rfl <;>
    rcases DynCircExt.bit_cases n with rfl | rfl <;>
    rcases DynCircExt.bit_cases e with rfl | rfl <;> decide

def wrapBitRange24 {Var : Type} {w n : ℕ} (v : Var)
    (rAt : Fin 24 → QRegister w n) (cp : ComputeProg w)
    (mid : DynamicCircuit Var n) (m : ℕ) : ∀ (k : ℕ), m + k ≤ 24 → DynamicCircuit Var n
  | 0, _ => mid
  | k + 1, hk =>
      wrapDynOnReg v (rAt ⟨m + k, hk⟩) cp
        (wrapBitRange24 v rAt cp mid m k (Nat.le_of_succ_le hk))

theorem ctrlSafe_wrapBitRange24 {Var : Type} {w n : ℕ} {S_ctrl S_tgt : Wire n → Prop}
    (v : Var) (rAt : Fin 24 → QRegister w n) (cp : ComputeProg w) (mid : DynamicCircuit Var n)
    (m : ℕ) (hCtrl : ∀ (i : Fin 24) (u : Wire w), S_ctrl (rAt i u))
    (hCP : ∀ i : Fin 24, ComputeProgCtrlSafe (fun u ↦ S_ctrl (rAt i u))
        (fun u ↦ S_tgt (rAt i u)) cp)
    (hMid : DynCtrlSafe S_ctrl S_tgt mid) :
    ∀ (k : ℕ) (hk : m + k ≤ 24), DynCtrlSafe S_ctrl S_tgt (wrapBitRange24 v rAt cp mid m k hk)
  | 0, _ => hMid
  | k + 1, hk =>
      .wrapOnReg v (rAt ⟨m + k, hk⟩) cp (hCtrl _) (hCP _)
        (ctrlSafe_wrapBitRange24 v rAt cp mid m hCtrl hCP hMid k (Nat.le_of_succ_le hk))

theorem writeSub24_congr_slice {n : ℕ} (β : BitAssignment n) (rDst : QRegister 24 n)
    (m k : ℕ) (f g : Fin 24 → ZMod 2) (hfg : ∀ i : Fin 24, m ≤ i.val ∧ i.val < m + k → f i = g i) :
    writeSub24 β rDst m k f = writeSub24 β rDst m k g := by
  unfold writeSub24
  exact congrArg (writeReg β rDst)
      (funext fun i ↦ by split_ifs with h <;> first | exact hfg i h | rfl)

theorem step_wrapBitRange24 {Var : Type} [Fintype Var] [DecidableEq Var] {W w n : ℕ}
    [NeZero (2 ^ n)]
    (v : Var) (rWork : QRegister W n) (rAt : Fin 24 → QRegister w n) (rDst : QRegister 24 n)
    (sLoc : Finset (Wire w)) (cp : ComputeProg w) (nAnd : ℕ)
    (hVp : cp.ValidProg ∅ sLoc) (hAnd : cp.numAnd = nAnd)
    (bitFn : BitAssignment n → Fin 24 → ZMod 2)
    (hLocEq : ∀ (i : Fin 24) (u : Wire w), u ∈ sLoc → rAt i u = rDst i)
    (hStepOut : ∀ (β : BitAssignment n) (i : Fin 24) (x : Wire n),
      x ≠ rDst i → stepCB (rAt i) cp.fwdBits β x = β x)
    (hStepHit : ∀ (β : BitAssignment n) (i : Fin 24),
      stepCB (rAt i) cp.fwdBits β (rDst i) = β (rDst i) + bitFn β i)
    (hBitOut : ∀ (β β' : BitAssignment n) (j : Fin 24),
      (∀ x, x ≠ rDst j → β' x = β x) → bitFn β' = bitFn β)
    (mid : DynamicCircuit Var n) (m : ℕ) :
    ∀ (k : ℕ) (hk : m + k ≤ 24) (stPre stPost : BitAssignment n → BitAssignment n)
      (phPre phPost : BitAssignment n → ZMod 2),
      (∀ u ∈ sLoc, ∀ δ (i : Fin 24), m ≤ i.val ∧ i.val < m + k → (∀ q, δ (rWork q) = 0) →
        stPre δ (rDst i) = 0 ∧ stPost δ (rDst i) = 0) →
      SubspaceStep
        (mkKetOpW rWork (fun δ ↦ writeSub24 (stPre δ) rDst m k (fun i ↦ stPre δ (rDst i) +
            bitFn (stPre δ) i)) phPre)
        (mkKetOpW rWork (fun δ ↦ writeSub24 (stPost δ) rDst m k (fun i ↦ stPost δ (rDst i) +
            bitFn (stPost δ) i)) phPost)
        mid →
      SubspaceStep (mkKetOpW rWork stPre phPre) (mkKetOpW rWork stPost phPost)
          (wrapBitRange24 v rAt cp mid m k hk) ∧
      (wrapBitRange24 v rAt cp mid m k hk).count .T = 4 * nAnd * k + mid.count .T ∧
      (wrapBitRange24 v rAt cp mid m k hk).count .TOFF = mid.count .TOFF := by
  intro k
  induction k with
  | zero =>
      intro _ stPre stPost _ _ _ hMid
      rw [funext fun δ ↦ writeSub24_zero (stPre δ) rDst m _,
        funext fun δ ↦ writeSub24_zero (stPost δ) rDst m _] at hMid
      exact ⟨hMid, (zero_add _).symm, rfl⟩
  | succ k ih =>
      intro hk stPre stPost phPre phPost hCln hMid
      let jk : Fin 24 := ⟨m + k, hk⟩
      have hNe (i : Fin 24) (hi : i.val < m + k) : rDst i ≠ rDst jk :=
        fun e ↦ Nat.ne_of_lt hi (congrArg Fin.val (rDst.wires.injective e))
      let stp := stepCB (rAt jk) cp.fwdBits
      have hFold (β : BitAssignment n) :
          writeSub24 (stp β) rDst m k (fun i ↦ stp β (rDst i) + bitFn (stp β) i) =
          writeSub24 β rDst m (k + 1) (fun i ↦ β (rDst i) + bitFn β i) := by
        rw [show stp = stepCB (rAt jk) cp.fwdBits from rfl, hBitOut β _ jk (hStepOut β jk)]
        exact (writeSub24_congr_slice _ rDst m k _ _ fun i hi ↦ by
            rw [hStepOut β jk _ (hNe i hi.2)]).trans
          (writeSub24_succ_of_step β _ rDst m k hk _ (hStepOut β jk) (hStepHit β jk))
      simp only [← hFold] at hMid
      obtain ⟨sIn, tIn, fIn⟩ := ih (Nat.le_of_succ_le hk) (stp ∘ stPre) (stp ∘ stPost)
        phPre phPost (fun u hu δ i hi hz ↦
          ⟨(hStepOut (stPre δ) jk _ (hNe i hi.2)).trans
             (hCln u hu δ i ⟨hi.1, Nat.lt_succ_of_lt hi.2⟩ hz).1,
           (hStepOut (stPost δ) jk _ (hNe i hi.2)).trans
             (hCln u hu δ i ⟨hi.1, Nat.lt_succ_of_lt hi.2⟩ hz).2⟩) hMid
      have hjk : m ≤ jk.val ∧ jk.val < m + (k + 1) := ⟨Nat.le_add_right m k, Nat.lt_succ_self _⟩
      obtain ⟨sOut, tOut, fOut, _⟩ := subspaceStep_wrapOnReg_vprog2 v rWork (rAt jk)
        sLoc cp nAnd hVp hAnd stPre stPost phPre phPost (wrapBitRange24 v rAt cp mid m k _)
        (fun u hu δ hz ↦ hLocEq jk u hu ▸ (hCln u hu δ jk hjk hz).1)
        (fun u hu δ hz ↦ hLocEq jk u hu ▸ (hCln u hu δ jk hjk hz).2) sIn
      exact ⟨sOut, tOut.trans (tIn ▸ by ring), fOut.trans fIn⟩

/-- `0`-T `24`-bit CNOT copy wrapper `rSrc -> rMuxCopy24` (`rSrc` control-only). -/
def wrapCopy24 {Var : Type} {Wp n : ℕ} (h193 : 193 ≤ Wp) (v : Var)
    (rSrc : QRegister 24 n) (r41 : QRegister (122 + Wp) n)
    (hd : rSrc.DisjointWires (rMuxCopy24 h193 r41)) (mid : DynamicCircuit Var n) :
        DynamicCircuit Var n :=
  wrapBitRange24 v (fun i ↦ rReg2 (rSrc i) (rMuxCopy24 h193 r41 i)
      (disj_ne hd i i)) cpCnot2 mid 0 24 (Nat.le_refl 24)

theorem ctrlSafe_wrapCopy24 {Var : Type} {Wp n : ℕ} {S_ctrl S_tgt : Wire n → Prop}
    (h193 : 193 ≤ Wp) (v : Var) (rSrc : QRegister 24 n) (r41 : QRegister (122 + Wp) n)
    (hd : rSrc.DisjointWires (rMuxCopy24 h193 r41)) (mid : DynamicCircuit Var n)
    (hSrc : ∀ i, S_ctrl (rSrc i))
    (hCopy : ∀ i, S_ctrl (rMuxCopy24 h193 r41 i) ∧ S_tgt (rMuxCopy24 h193 r41 i))
    (hMid : DynCtrlSafe S_ctrl S_tgt mid) :
        DynCtrlSafe S_ctrl S_tgt (wrapCopy24 h193 v rSrc r41 hd mid) :=
  ctrlSafe_wrapBitRange24 v _ cpCnot2 mid 0
    (fun i u ↦ by fin_cases u <;> first | exact hSrc i | exact (hCopy i).1)
    (fun i ↦ ⟨hSrc i, (hCopy i).1, (hCopy i).2⟩) hMid 24 (Nat.le_refl 24)

theorem step_wrapCopy24 {Var : Type} [Fintype Var] [DecidableEq Var] {W Wp n : ℕ} [NeZero (2 ^ n)]
    (h193 : 193 ≤ Wp) (v : Var) (rWork : QRegister W n)
    (rSrc : QRegister 24 n) (r41 : QRegister (122 + Wp) n)
    (hd : rSrc.DisjointWires (rMuxCopy24 h193 r41))
    (stPre stPost : BitAssignment n → BitAssignment n) (phPre phPost : BitAssignment n → ZMod 2)
    (mid : DynamicCircuit Var n)
    (hCln : ∀ δ (i : Fin 24), (∀ q, δ (rWork q) = 0) →
      stPre δ (rMuxCopy24 h193 r41 i) = 0 ∧ stPost δ (rMuxCopy24 h193 r41 i) = 0)
    (hMid : SubspaceStep
      (mkKetOpW rWork (fun δ ↦ writeReg (stPre δ) (rMuxCopy24 h193 r41)
          (fun i ↦ stPre δ (rSrc i))) phPre)
      (mkKetOpW rWork (fun δ ↦ writeReg (stPost δ) (rMuxCopy24 h193 r41)
          (fun i ↦ stPost δ (rSrc i))) phPost) mid) :
    SubspaceStep (mkKetOpW rWork stPre phPre) (mkKetOpW rWork stPost phPost)
        (wrapCopy24 h193 v rSrc r41 hd mid) ∧
    (wrapCopy24 h193 v rSrc r41 hd mid).count .T = mid.count .T ∧
    (wrapCopy24 h193 v rSrc r41 hd mid).count .TOFF = mid.count .TOFF := by
  let rC := rMuxCopy24 h193 r41
  have hWr (β : BitAssignment n) (h0 : ∀ i, β (rC i) = 0) :
      writeSub24 β rC 0 24 (fun i ↦ β (rC i) + β (rSrc i)) = writeReg β rC (fun i ↦ β (rSrc i)) :=
    (writeSub24_full β rC _).trans (congrArg _ (funext fun i ↦ by rw [h0 i, zero_add]))
  obtain ⟨s, t, f⟩ := step_wrapBitRange24 v rWork
    (fun i ↦ rReg2 (rSrc i) (rC i) (disj_ne hd i i)) rC ∅ cpCnot2 0 cpCnot2_vp cpCnot2_and
    (fun β i ↦ β (rSrc i)) (by simp)
    (fun β _ _ hx ↦ stepCB_apply_ne _ cpCnot2.fwdBits β 1
      (fun u hu ↦ by fin_cases u <;> first | exact (cpCnot2_fwd _).1 | exact absurd rfl hu) hx)
    (fun β _ ↦ (stepCB_apply_reg _ cpCnot2.fwdBits β 1).trans (cpCnot2_fwd _).2)
    (fun _ _ j hOut ↦ funext fun i ↦ hOut _ (disj_ne hd i j))
    mid 0 24 le_rfl stPre stPost phPre phPost (by simp)
    (subspaceStep_of_eq_pre_local
      (mkKetOpW_congr rWork (fun δ hz ↦ hWr _ fun i ↦ (hCln δ i hz).1) fun _ _ ↦ rfl)
      (subspaceStep_of_eq_post hMid
        (mkKetOpW_congr rWork (fun δ hz ↦ (hWr _ fun i ↦ (hCln δ i hz).2).symm) fun _ _ ↦ rfl)))
  exact ⟨s, t.trans (by omega), f⟩

/--
`0` -T `24` -bit `Leg 2` XOR-flip wrapper `(NucA + ElecA) -> rMuxM1` (`NucA, ElecA` control-only).
-/
def wrapFlipLeg2 {Var : Type} {Wp n : ℕ} (h193 : 193 ≤ Wp) (isCsel : Bool) (v : Var)
    (r41 : QRegister (122 + Wp) n) (mid : DynamicCircuit Var n) : DynamicCircuit Var n :=
  wrapBitRange24 v
    (fun i ↦
      have hw := wtop_ge192 h193 isCsel
      rReg3 (rPotBNucA r41 i) (rPotBElecA r41 i) (rMuxM1 h193 isCsel r41 i)
        (r41_blk_ne_blk r41 i i (by omega))
        (r41_blk_ne_blk r41 i i (by omega))
        (r41_blk_ne_blk r41 i i (by omega)))
    cpFlipLeg2_3 mid 0 24 (Nat.le_refl 24)

theorem ctrlSafe_wrapFlipLeg2 {Var : Type} {Wp n : ℕ} {S_ctrl S_tgt : Wire n → Prop}
    (h193 : 193 ≤ Wp) (isCsel : Bool) (v : Var) (r41 : QRegister (122 + Wp) n)
        (mid : DynamicCircuit Var n)
    (hSr : ∀ k, S_ctrl (r41 k)) (hM1 : ∀ i, S_tgt (rMuxM1 h193 isCsel r41 i))
    (hMid : DynCtrlSafe S_ctrl S_tgt mid) :
        DynCtrlSafe S_ctrl S_tgt (wrapFlipLeg2 h193 isCsel v r41 mid) :=
  ctrlSafe_wrapBitRange24 v _ cpFlipLeg2_3 mid 0
    (fun _ u ↦ by fin_cases u <;> exact hSr _)
    (fun i ↦ ⟨⟨hSr _, hSr _, hM1 i⟩, ⟨hSr _, hSr _, hM1 i⟩⟩) hMid 24 (Nat.le_refl 24)

theorem step_wrapFlipLeg2 {Var : Type} [Fintype Var] [DecidableEq Var] {W Wp n : ℕ} [NeZero (2 ^ n)]
    (h193 : 193 ≤ Wp) (isCsel : Bool) (v : Var) (rWork : QRegister W n)
        (r41 : QRegister (122 + Wp) n)
    (stPre stPost : BitAssignment n → BitAssignment n) (phPre phPost : BitAssignment n → ZMod 2)
    (mid : DynamicCircuit Var n)
    (hMid : SubspaceStep
      (mkKetOpW rWork (fun δ ↦ writeReg (stPre δ) (rMuxM1 h193 isCsel r41)
        (fun i ↦ stPre δ (rMuxM1 h193 isCsel r41 i) + (stPre δ (rPotBNucA r41 i) +
            stPre δ (rPotBElecA r41 i)))) phPre)
      (mkKetOpW rWork (fun δ ↦ writeReg (stPost δ) (rMuxM1 h193 isCsel r41)
        (fun i ↦ stPost δ (rMuxM1 h193 isCsel r41 i) + (stPost δ (rPotBNucA r41 i) +
            stPost δ (rPotBElecA r41 i)))) phPost)
      mid) :
    SubspaceStep (mkKetOpW rWork stPre phPre) (mkKetOpW rWork stPost phPost)
        (wrapFlipLeg2 h193 isCsel v r41 mid) ∧
    (wrapFlipLeg2 h193 isCsel v r41 mid).count .T = mid.count .T ∧
    (wrapFlipLeg2 h193 isCsel v r41 mid).count .TOFF = mid.count .TOFF := by
  have hw := wtop_ge192 h193 isCsel
  obtain ⟨s, t, f⟩ := step_wrapBitRange24 v rWork
    (fun i ↦ rReg3 (rPotBNucA r41 i) (rPotBElecA r41 i) (rMuxM1 h193 isCsel r41 i)
      (r41_blk_ne_blk r41 i i (by omega)) (r41_blk_ne_blk r41 i i (by omega))
      (r41_blk_ne_blk r41 i i (by omega)))
    (rMuxM1 h193 isCsel r41) ∅ cpFlipLeg2_3 0 cpFlipLeg2_3_vp cpFlipLeg2_3_and
    (fun β i ↦ β (rPotBNucA r41 i) + β (rPotBElecA r41 i)) (by simp)
    (fun β _ _ hx ↦ stepCB_apply_ne _ cpFlipLeg2_3.fwdBits β 2 (fun u hu ↦ by
      fin_cases u <;> first | exact (cpFlipLeg2_3_fwd _).1 | exact (cpFlipLeg2_3_fwd _).2.1 |
        exact absurd rfl hu) hx)
    (fun β _ ↦ ((stepCB_apply_reg _ cpFlipLeg2_3.fwdBits β 2).trans
      (cpFlipLeg2_3_fwd _).2.2).trans (add_assoc _ _ _))
    (fun _ _ j hOut ↦ funext fun i ↦ by
      rw [hOut _ (r41_blk_ne_blk r41 i j (by omega)), hOut _ (r41_blk_ne_blk r41 i j (by omega))])
    mid 0 24 le_rfl stPre stPost phPre phPost (by simp)
    (by simpa only [writeSub24_full] using hMid)
  exact ⟨s, t.trans (by omega), f⟩

/-- `Mux1` `Dist18` target bit `nn * (e + n) + e` on `r41`. -/
def mux1DistBit {Wp n : ℕ} (r41 : QRegister (122 + Wp) n) (β : BitAssignment n)
    (i : Fin 24) : ZMod 2 :=
  β (wPotBIsNN r41) * (β (rPotBElecA r41 i) + β (rPotBNucA r41 i)) + β (rPotBElecA r41 i)

/-- `4 * k`-T slice `[m, m + k)` `Mux1` `Dist18` wrapper (`isNN, NucA` control-only). -/
def wrapMux1Dist {Var : Type} {Wp n : ℕ} (h193 : 193 ≤ Wp) (isCsel : Bool) (v : Var)
    (r41 : QRegister (122 + Wp) n) (m k : ℕ) (hk : m + k ≤ 24) (mid : DynamicCircuit Var n) :
        DynamicCircuit Var n :=
  wrapBitRange24 v
    (fun i ↦
      have hw := wtop_ge192 h193 isCsel
      rReg4 (wPotBIsNN r41) (rPotBNucA r41 i) (rPotBElecA r41 i) (rMuxM1 h193 isCsel r41 i)
        (r41_wire_ne_blk r41 _ i (by omega)) (r41_wire_ne_blk r41 _ i (by omega))
        (r41_wire_ne_blk r41 _ i (by omega)) (r41_blk_ne_blk r41 i i (by omega))
        (r41_blk_ne_blk r41 i i (by omega)) (r41_blk_ne_blk r41 i i (by omega)))
    cpMux1Dist4 mid m k hk

theorem ctrlSafe_wrapMux1Dist {Var : Type} {Wp n : ℕ} {S_ctrl S_tgt : Wire n → Prop}
    (h193 : 193 ≤ Wp) (isCsel : Bool) (v : Var) (r41 : QRegister (122 + Wp) n)
    (m k : ℕ) (hk : m + k ≤ 24) (mid : DynamicCircuit Var n)
    (hSr : ∀ j, S_ctrl (r41 j)) (hTr : ∀ j : Fin (122 + Wp), IsNonNucPortB41Idx j.val →
        S_tgt (r41 j))
    (hMid : DynCtrlSafe S_ctrl S_tgt mid) :
        DynCtrlSafe S_ctrl S_tgt (wrapMux1Dist h193 isCsel v r41 m k hk mid) := by
  have hw := wtop_ge192 h193 isCsel
  have hEl : ∀ i, S_tgt (rPotBElecA r41 i) := fun i ↦ r41_blk_tgt r41 hTr i (by omega)
  have hM1 : ∀ i, S_tgt (rMuxM1 h193 isCsel r41 i) := fun i ↦ r41_blk_tgt r41 hTr i (by omega)
  exact ctrlSafe_wrapBitRange24 v _ cpMux1Dist4 mid m
    (fun _ u ↦ by fin_cases u <;> exact hSr _)
    (fun i ↦ ⟨⟨hSr _, hSr _, hEl i⟩, ⟨⟨hSr _, hSr _, hSr _, hM1 i⟩, ⟨⟨hSr _, hSr _, hEl i⟩,
        ⟨hSr _, hSr _, hM1 i⟩⟩⟩⟩)
    hMid k hk

theorem step_wrapMux1Dist {Var : Type} [Fintype Var] [DecidableEq Var] {W Wp n : ℕ} [NeZero (2 ^ n)]
    (h193 : 193 ≤ Wp) (isCsel : Bool) (v : Var) (rWork : QRegister W n)
        (r41 : QRegister (122 + Wp) n)
    (m k : ℕ) (hk : m + k ≤ 24)
    (stPre stPost : BitAssignment n → BitAssignment n) (phPre phPost : BitAssignment n → ZMod 2)
    (mid : DynamicCircuit Var n)
    (hCln : ∀ δ (i : Fin 24), m ≤ i.val ∧ i.val < m + k → (∀ q, δ (rWork q) = 0) →
      stPre δ (rMuxM1 h193 isCsel r41 i) = 0 ∧ stPost δ (rMuxM1 h193 isCsel r41 i) = 0)
    (hMid : SubspaceStep
      (mkKetOpW rWork (fun δ ↦ writeSub24 (stPre δ)
          (rMuxM1 h193 isCsel r41) m k (mux1DistBit r41 (stPre δ))) phPre)
      (mkKetOpW rWork (fun δ ↦ writeSub24 (stPost δ)
          (rMuxM1 h193 isCsel r41) m k (mux1DistBit r41 (stPost δ))) phPost)
      mid) :
    SubspaceStep (mkKetOpW rWork stPre phPre) (mkKetOpW rWork stPost phPost)
        (wrapMux1Dist h193 isCsel v r41 m k hk mid) ∧
    (wrapMux1Dist h193 isCsel v r41 m k hk mid).count .T = 4 * k + mid.count .T ∧
    (wrapMux1Dist h193 isCsel v r41 m k hk mid).count .TOFF = mid.count .TOFF := by
  have hw := wtop_ge192 h193 isCsel
  let rM := rMuxM1 h193 isCsel r41
  have hSl (β : BitAssignment n) (h0 : ∀ i, m ≤ i.val ∧ i.val < m + k → β (rM i) = 0) :=
    writeSub24_congr_slice β rM m k (fun i ↦ β (rM i) + mux1DistBit r41 β i)
      (mux1DistBit r41 β) fun i hi ↦ by rw [h0 i hi, zero_add]
  obtain ⟨s, t, f⟩ := step_wrapBitRange24 v rWork
    (fun i ↦ rReg4 (wPotBIsNN r41) (rPotBNucA r41 i) (rPotBElecA r41 i) (rM i)
      (r41_wire_ne_blk r41 _ i (by omega)) (r41_wire_ne_blk r41 _ i (by omega))
      (r41_wire_ne_blk r41 _ i (by omega)) (r41_blk_ne_blk r41 i i (by omega))
      (r41_blk_ne_blk r41 i i (by omega)) (r41_blk_ne_blk r41 i i (by omega)))
    rM ({3} : Finset (Wire 4)) cpMux1Dist4 1 cpMux1Dist4_vp cpMux1Dist4_and (mux1DistBit r41)
    (fun _ u hu ↦ by
      rw [Finset.mem_singleton.mp hu]
      rfl)
    (fun β _ _ hx ↦ stepCB_apply_ne _ cpMux1Dist4.fwdBits β 3 (fun u hu ↦ by
      fin_cases u <;> first | exact (cpMux1Dist4_fwd _).1 | exact (cpMux1Dist4_fwd _).2.1 |
        exact (cpMux1Dist4_fwd _).2.2.1 | exact absurd rfl hu) hx)
    (fun β _ ↦ ((stepCB_apply_reg _ cpMux1Dist4.fwdBits β 3).trans
      (cpMux1Dist4_fwd _).2.2.2).trans (add_assoc _ _ _))
    (fun _ _ j hOut ↦ funext fun i ↦ by
      unfold mux1DistBit
      rw [hOut _ (r41_wire_ne_blk r41 _ j (by omega)), hOut _ (r41_blk_ne_blk r41 i j (by omega)),
          hOut _ (r41_blk_ne_blk r41 i j (by omega))])
    mid m k hk stPre stPost phPre phPost (fun _ _ ↦ hCln)
    (subspaceStep_of_eq_pre_local
      (mkKetOpW_congr rWork (fun δ hz ↦ hSl _ fun i hi ↦ (hCln δ i hi hz).1) fun _ _ ↦ rfl)
      (subspaceStep_of_eq_post hMid
        (mkKetOpW_congr rWork (fun δ hz ↦ (hSl _ fun i hi ↦ (hCln δ i hi hz).2).symm) fun _ _ ↦
            rfl)))
  exact ⟨s, t.trans (by omega), f⟩

/-
Section 5A: Gate/header wrappers, `muxSt` state invariant, and `pMuxStage4` circuit + `DynCtrlSafe`
.
-/

/--
`4` -T `Csel` active-gate wrapper `locQ & isPot -> r41[122 + Wp - 1]` (`0`-T identity on `Usel` ).
-/
def wrapGateCsel {Var : Type} {Wp n : ℕ} (h193 : 193 ≤ Wp) (isCsel : Bool) (v : Var)
    (r41 : QRegister (122 + Wp) n) (mid : DynamicCircuit Var n) : DynamicCircuit Var n :=
  if isCsel then
    wrapDynOnReg v
      (rReg3 (wPotBLocQ r41) (wPotBIsPot r41) (r41 ⟨122 + Wp - 1, by omega⟩)
        (r41_ne r41 _ _ (by omega)) (r41_ne r41 _ _ (by omega)) (r41_ne r41 _ _ (by omega)))
      cpAnd3 mid
  else mid

theorem ctrlSafe_wrapGateCsel {Var : Type} {Wp n : ℕ} {S_ctrl S_tgt : Wire n → Prop}
    (h193 : 193 ≤ Wp) (isCsel : Bool) (v : Var) (r41 : QRegister (122 + Wp) n)
        (mid : DynamicCircuit Var n)
    (hSr : ∀ k, S_ctrl (r41 k)) (hTr : ∀ k : Fin (122 + Wp), IsNonNucPortB41Idx k.val →
        S_tgt (r41 k))
    (hMid : DynCtrlSafe S_ctrl S_tgt mid) :
        DynCtrlSafe S_ctrl S_tgt (wrapGateCsel h193 isCsel v r41 mid) := by
  cases isCsel
  · exact hMid
  · exact .wrapOnReg v _ cpAnd3 (fun u ↦ by fin_cases u <;> exact hSr _)
      ⟨hSr _, hSr _, hSr _, hTr _ (Or.inr (Or.inr (Nat.le_sub_one_of_lt (by omega))))⟩ hMid

/--
`8` -T `Csel` header cascade `s0G := g & s0; n0G := s0G & n0` on `r41[240..241]` (`0`-T on `Usel` ).
-/
def wrapHdrCascade2 {Var : Type} {Wp n : ℕ} (h193 : 193 ≤ Wp) (isCsel : Bool) (v : Var)
    (r41 : QRegister (122 + Wp) n) (mid : DynamicCircuit Var n) : DynamicCircuit Var n :=
  if isCsel then
    wrapDynOnReg v
      (rReg5 (r41 ⟨122 + Wp - 1, by omega⟩) (wPotBIsScreen r41) (wPotBIsNN r41)
        (r41 ⟨240, by omega⟩) (r41 ⟨241, by omega⟩)
        (r41_ne r41 _ _ (by omega)) (r41_ne r41 _ _ (by omega))
        (r41_ne r41 _ _ (by omega)) (r41_ne r41 _ _ (by omega))
        (r41_ne r41 _ _ (by omega)) (r41_ne r41 _ _ (by omega))
        (r41_ne r41 _ _ (by omega)) (r41_ne r41 _ _ (by omega))
        (r41_ne r41 _ _ (by omega)) (r41_ne r41 _ _ (by omega)))
      cpHdr2 mid
  else mid

theorem ctrlSafe_wrapHdrCascade2 {Var : Type} {Wp n : ℕ} {S_ctrl S_tgt : Wire n → Prop}
    (h193 : 193 ≤ Wp) (isCsel : Bool) (v : Var) (r41 : QRegister (122 + Wp) n)
        (mid : DynamicCircuit Var n)
    (hSr : ∀ k, S_ctrl (r41 k)) (hTr : ∀ k : Fin (122 + Wp), IsNonNucPortB41Idx k.val →
        S_tgt (r41 k))
    (hMid : DynCtrlSafe S_ctrl S_tgt mid) :
        DynCtrlSafe S_ctrl S_tgt (wrapHdrCascade2 h193 isCsel v r41 mid) := by
  cases isCsel
  · exact hMid
  · exact .wrapOnReg v _ cpHdr2 (fun u ↦ by fin_cases u <;> exact hSr _)
      ⟨⟨hSr _, hSr _, hSr _, hTr _ (Or.inr (Or.inr (show 81 ≤ 240 by omega)))⟩,
       ⟨hSr _, hSr _, hSr _, hTr _ (Or.inr (Or.inr (show 81 ≤ 241 by omega)))⟩⟩ hMid

theorem muxDisj_m1_d2 {Wp n : ℕ} (h193 : 193 ≤ Wp) (isCsel : Bool) (r41 : QRegister (122 + Wp) n) :
    (rMuxM1 h193 isCsel r41).DisjointWires (rMuxD2_18 h193 r41) := by
  have hw := wtop_ge192 h193 isCsel
  exact owCompose_disj r41 fun _ _ ↦ by simp only [QRegister.block_apply_val]; omega

/-
Section 5B: Canonical `muxSt` state invariant and `pMuxLegsBlock` / `pMuxStageA` `SubspaceStep` .
-/

/-- Squared distance stored in `rMuxD2_18` (`d^2(if nn then nA else eA, if s then pB else nA)`). -/
def muxD2Val {Wp n : ℕ} (r41 : QRegister (122 + Wp) n) (β : BitAssignment n) : ℕ :=
  openCoordDistSq
    (if β (wPotBIsNN r41) == 1 then coordOfReg24 (rPotBNucA r41) β else coordOfReg24 (rPotBElecA
        r41) β)
    (if β (wPotBIsScreen r41) == 1 then coordOfReg24 (rPotBPortB r41) β else coordOfReg24 (rPotBNucA
        r41) β)

theorem muxD2Val_le {Wp n : ℕ} (r41 : QRegister (122 + Wp) n) (β : BitAssignment n) :
    muxD2Val r41 β ≤ 195075 := openCoordDistSq_le_195075 _ _

theorem muxD2Val_eq_sector {Wp n : ℕ} (r41 : QRegister (122 + Wp) n) {β : BitAssignment n}
    (hV : ValidPotBFlags r41 β) :
    muxD2Val r41 β = sectorDist3DSq3 (β (wPotBIsScreen r41) == 1) (β (wPotBIsNN r41) == 1)
      (coordOfReg24 (rPotBNucA r41) β) (coordOfReg24 (rPotBPortB r41) β)
          (coordOfReg24 (rPotBElecA r41) β) := by
  unfold muxD2Val
  rcases DynCircExt.bit_cases (β (wPotBIsScreen r41)) with hs | hs
  · simp only [hs, hV.2 hs, (by decide : ((0 : ZMod 2) == 1) = false),
      Bool.false_eq_true, ↓reduceIte, sectorDist3DSq3, Bool.cond_false]
    exact owOpenCoordDistSq_comm _ _
  · simp only [hs, (by decide : ((1 : ZMod 2) == 1) = true), ↓reduceIte]
    cases (β (wPotBIsNN r41) == 1) <;> rfl

/-- Work-pool bit assignment on `rPotBWork r41` at stage boundary `(m0, hasD2)`. -/
def muxWorkVal {Wp n : ℕ} (_h193 : 193 ≤ Wp) (isCsel : Bool) (r41 : QRegister (122 + Wp) n)
    (m0 : ℕ) (hasD2 : Bool) (β : BitAssignment n) (u : Fin Wp) : ZMod 2 :=
  let wt := Wtop Wp isCsel
  if isCsel && decide (u.val = Wp - 1) then
    β (wPotBLocQ r41) * β (wPotBIsPot r41)
  else if hasD2 && decide (u.val < 18) then
    if (muxD2Val r41 β).testBit u.val then 1 else 0
  else if wt - 48 + m0 ≤ u.val ∧ u.val < wt - 24 then
    if β (wPotBIsNN r41) == 1 then
      β (rPotBNucA r41 ⟨(u.val - (wt - 48)) % 24, Nat.mod_lt _ (by decide)⟩)
    else
      β (rPotBElecA r41 ⟨(u.val - (wt - 48)) % 24, Nat.mod_lt _ (by decide)⟩)
  else if wt - 24 ≤ u.val ∧ u.val < wt then
    if β (wPotBIsScreen r41) == 1 then
      β (rPotBPortB r41 ⟨(u.val - (wt - 24)) % 24, Nat.mod_lt _ (by decide)⟩)
    else
      β (rPotBNucA r41 ⟨(u.val - (wt - 24)) % 24, Nat.mod_lt _ (by decide)⟩)
  else 0

/-- Canonical `Mux48` stage-boundary state updating `rMuxZ16 r41` and `rPotBWork r41`. -/
def muxSt {Wp n : ℕ} (h193 : 193 ≤ Wp) (isCsel : Bool) (r41 : QRegister (122 + Wp) n)
    (m0 : ℕ) (hasD2 : Bool) (z16 : Fin 16 → ZMod 2) (β : BitAssignment n) : BitAssignment n :=
  writeReg (writeReg β (rMuxZ16 r41) z16) (rPotBWork r41) (muxWorkVal h193 isCsel r41 m0 hasD2 β)

theorem eq_of_r41_parts {Wp n : ℕ} (r41 : QRegister (122 + Wp) n) {α γ : BitAssignment n}
    (hOut : ∀ w, (∀ k : Fin (122 + Wp), w ≠ r41 k) → α w = γ w)
    (hLo : ∀ m (hm : m < 106), α (r41 ⟨m, by omega⟩) = γ (r41 ⟨m, by omega⟩))
    (hZ : ∀ j : Fin 16, α (rMuxZ16 r41 j) = γ (rMuxZ16 r41 j))
    (hWk : ∀ u : Fin Wp, α (rPotBWork r41 u) = γ (rPotBWork r41 u)) : α = γ := by
  funext w
  if hw : ∃ k : Fin (122 + Wp), r41 k = w then
    obtain ⟨k, rfl⟩ := hw
    if hk1 : k.val < 106 then exact hLo k.val hk1
    else if hk2 : k.val < 122 then
      rw [show r41 k = rMuxZ16 r41 ⟨k.val - 106, by omega⟩ from
        congrArg r41.wires (Fin.ext (by
          simp only [QRegister.block_apply_val]
          omega))]
      exact hZ _
    else
      rw [show r41 k = rPotBWork r41 ⟨k.val - 122, by omega⟩ from
        congrArg r41.wires (Fin.ext (by
          simp only [QRegister.block_apply_val]
          omega))]
      exact hWk _
  else exact hOut w fun k h ↦ hw ⟨k, h.symm⟩

theorem muxSt_work {Wp n : ℕ} (h193 : 193 ≤ Wp) (isCsel : Bool) (r41 : QRegister (122 + Wp) n)
    (m0 : ℕ) (hasD2 : Bool) (z16 : Fin 16 → ZMod 2) (β : BitAssignment n) (u : Fin Wp) :
    muxSt h193 isCsel r41 m0 hasD2 z16 β (rPotBWork r41 u) =
        muxWorkVal h193 isCsel r41 m0 hasD2 β u :=
  writeReg_apply_reg _ _ _ u

theorem muxSt_r122 {Wp n : ℕ} (h193 : 193 ≤ Wp) (isCsel : Bool) (r41 : QRegister (122 + Wp) n)
    (m0 : ℕ) (hasD2 : Bool) (z16 : Fin 16 → ZMod 2) (β : BitAssignment n) (u : Fin Wp) :
    muxSt h193 isCsel r41 m0 hasD2 z16 β (r41 ⟨122 + u.val, by omega⟩) =
      muxWorkVal h193 isCsel r41 m0 hasD2 β u := by
  rw [show r41 ⟨122 + u.val, by omega⟩ = rPotBWork r41 u from
      congrArg r41.wires (Fin.ext (by simp only [QRegister.block_apply_val])), muxSt_work]

theorem muxWorkVal_hi {Wp n : ℕ} (h193 : 193 ≤ Wp) (isCsel : Bool) (r41 : QRegister (122 + Wp) n)
    (m0 : ℕ) (hasD2 : Bool) (β : BitAssignment n) {u : Fin Wp} (h18 : 18 ≤ u.val)
        (hut : u.val < Wtop Wp isCsel) :
    muxWorkVal h193 isCsel r41 m0 hasD2 β u =
      if Wtop Wp isCsel - 48 + m0 ≤ u.val ∧ u.val < Wtop Wp isCsel - 24 then
        if β (wPotBIsNN r41) == 1 then β (rPotBNucA r41 ⟨(u.val - (Wtop Wp isCsel - 48)) % 24,
            Nat.mod_lt _ (by decide)⟩)
        else β (rPotBElecA r41 ⟨(u.val - (Wtop Wp isCsel - 48)) % 24, Nat.mod_lt _ (by decide)⟩)
      else if Wtop Wp isCsel - 24 ≤ u.val ∧ u.val < Wtop Wp isCsel then
        if β (wPotBIsScreen r41) == 1 then β (rPotBPortB r41 ⟨(u.val - (Wtop Wp isCsel - 24)) % 24,
            Nat.mod_lt _ (by decide)⟩)
        else β (rPotBNucA r41 ⟨(u.val - (Wtop Wp isCsel - 24)) % 24, Nat.mod_lt _ (by decide)⟩)
      else 0 := by
  have hc1 : (isCsel && decide (u.val = Wp - 1)) = false := by
    cases isCsel <;> simp only [Wtop, ↓reduceIte, Bool.false_and, Bool.true_and,
        decide_eq_false_iff_not] at hut ⊢
    omega
  have hc2 : (hasD2 && decide (u.val < 18)) = false := by simp [show ¬ u.val < 18 by omega]
  unfold muxWorkVal
  simp only [hc1, hc2, Bool.false_eq_true, ↓reduceIte]

theorem muxSt_m1 {Wp n : ℕ} (h193 : 193 ≤ Wp) (isCsel : Bool) (r41 : QRegister (122 + Wp) n)
    (m0 : ℕ) (hasD2 : Bool) (z16 : Fin 16 → ZMod 2) (β : BitAssignment n) (i : Fin 24) :
    muxSt h193 isCsel r41 m0 hasD2 z16 β (rMuxM1 h193 isCsel r41 i) =
      if m0 ≤
          i.val then (if β (wPotBIsNN r41) == 1 then β (rPotBNucA r41 i) else β (rPotBElecA r41 i))
          else 0 := by
  have := And.intro (wtop_ge192 h193 isCsel) (wtop_le_wp Wp isCsel)
  let u0 := Wtop Wp isCsel - 48 + i.val
  rw [show rMuxM1 h193 isCsel r41 i = r41 ⟨122 + u0, by omega⟩ from
        congrArg r41.wires (Fin.ext (by
          simp only [QRegister.block_apply_val, u0]
          omega)),
      muxSt_r122 h193 isCsel r41 m0 hasD2 z16 β ⟨u0, by omega⟩,
      muxWorkVal_hi h193 isCsel r41 m0 hasD2 β (show 18 ≤ u0 by omega)
          (show u0 < Wtop Wp isCsel by omega)]
  have hi : (⟨(u0 - (Wtop Wp isCsel - 48)) % 24, Nat.mod_lt _ (by decide)⟩ : Fin 24) = i :=
    Fin.ext (by simp [u0, Nat.mod_eq_of_lt i.isLt])
  dsimp only [u0] at hi ⊢
  split_ifs <;> first | rfl | omega | rw [hi]

theorem muxSt_m2 {Wp n : ℕ} (h193 : 193 ≤ Wp) (isCsel : Bool) (r41 : QRegister (122 + Wp) n)
    (m0 : ℕ) (hasD2 : Bool) (z16 : Fin 16 → ZMod 2) (β : BitAssignment n) (i : Fin 24) :
    muxSt h193 isCsel r41 m0 hasD2 z16 β (rMuxM2 h193 isCsel r41 i) =
      if β (wPotBIsScreen r41) == 1 then β (rPotBPortB r41 i) else β (rPotBNucA r41 i) := by
  have := And.intro (wtop_ge192 h193 isCsel) (wtop_le_wp Wp isCsel)
  let u0 := Wtop Wp isCsel - 24 + i.val
  rw [show rMuxM2 h193 isCsel r41 i = r41 ⟨122 + u0, by omega⟩ from
        congrArg r41.wires (Fin.ext (by
          simp only [QRegister.block_apply_val, u0]
          omega)),
      muxSt_r122 h193 isCsel r41 m0 hasD2 z16 β ⟨u0, by omega⟩,
      muxWorkVal_hi h193 isCsel r41 m0 hasD2 β (show 18 ≤ u0 by omega)
          (show u0 < Wtop Wp isCsel by omega)]
  have hi : (⟨(u0 - (Wtop Wp isCsel - 24)) % 24, Nat.mod_lt _ (by decide)⟩ : Fin 24) = i :=
    Fin.ext (by simp [u0, Nat.mod_eq_of_lt i.isLt])
  dsimp only [u0] at hi ⊢
  split_ifs <;> first | omega | rw [hi]

/- Section 5C1: `z16AddVal`, `phAddVal`, `v1Mux`, `v2Mux`, and `step_wrapHdrCascade2`. -/

/-- `16`-bit modular addition result on `Fin 16 → ZMod 2`. -/
def z16AddVal (z16 : Fin 16 → ZMod 2) (v : ℕ) : Fin 16 → ZMod 2 :=
  fun j ↦ if ((finBitsVal z16 + v % 2 ^ 16) % 2 ^ 16).testBit j.val then 1 else 0

/-- `17`-bit carry kick phase bit from `(z16, v)`. -/
def phAddVal (z16 : Fin 16 → ZMod 2) (v : ℕ) : ZMod 2 :=
  (((finBitsVal z16 + v % 2 ^ 16) / 2 ^ 16 + v / 2 ^ 16 : ℕ) : ZMod 2)

theorem finBitsVal_z16AddVal (z16 : Fin 16 → ZMod 2) (v : ℕ) :
    finBitsVal (z16AddVal z16 v) = (finBitsVal z16 + v % 2 ^ 16) % 2 ^ 16 := by
  unfold z16AddVal
  rw [finBitsVal_of_testBit, Nat.mod_mod]

theorem z16AddVal_zero (z16 : Fin 16 → ZMod 2) : z16AddVal z16 0 = z16 :=
  finBitsVal_inj <|
      by rw [finBitsVal_z16AddVal, Nat.zero_mod, add_zero, Nat.mod_eq_of_lt (finBitsVal_lt z16)]

theorem phAddVal_zero (z16 : Fin 16 → ZMod 2) : phAddVal z16 0 = 0 := by
  unfold phAddVal
  rw [show (finBitsVal z16 + 0 % 2 ^ 16) / 2 ^ 16 + 0 / 2 ^ 16 =
      0 by have := finBitsVal_lt z16; omega, Nat.cast_zero]

theorem stOWZ16_apply_reg {n : ℕ} (rZ16 : QRegister 16 n) (vFn : BitAssignment n → ℕ)
    (stX : BitAssignment n → BitAssignment n) (δ : BitAssignment n) (j : Fin 16) :
    stOWZ16 rZ16 vFn stX δ (rZ16 j) = z16AddVal (fun i ↦ stX δ (rZ16 i)) (vFn δ) j := by
  apply congrFun (finBitsVal_inj _) j
  rw [stOWZ16_val, finBitsVal_z16AddVal]

/-- Effective Leg 1 `17`-bit value on `r41`. -/
def v1Mux {isU10 : Bool} {Wp tLeg1 tLeg2 kMid tMid n : ℕ} (isCsel : Bool)
    (pkgLM : OWLegsMidPkg isU10 tLeg1 tLeg2 kMid tMid) (r41 : QRegister (122 + Wp) n)
        (β : BitAssignment n) : ℕ :=
  if potBGateActive isCsel r41 β then
    pkgLM.v1Fin8 (β (wPotBIsScreen r41) == 1) (β (wPotBIsNN r41) == 1)
      (speciesOfBits2 (β (wPotBSp1B0 r41)) (β (wPotBSp1B1 r41)))
      (fin8Bin (openCoordDistSq (coordOfReg24 (rPotBNucA r41) β) (coordOfReg24 (rPotBElecA r41) β)))
  else 0

/-- Effective Leg 2 `17`-bit value on `r41`. -/
def v2Mux {isU10 : Bool} {Wp tLeg1 tLeg2 kMid tMid n : ℕ} (isCsel : Bool)
    (pkgLM : OWLegsMidPkg isU10 tLeg1 tLeg2 kMid tMid) (r41 : QRegister (122 + Wp) n)
        (β : BitAssignment n) : ℕ :=
  if potBGateActive isCsel r41 β then
    pkgLM.v2Fin8 (β (wPotBIsScreen r41) == 1) (β (wPotBIsNN r41) == 1)
      (speciesOfBits2 (β (wPotBSp2B0 r41)) (β (wPotBSp2B1 r41)))
      (owB2Of3Port (β (wPotBIsNN r41) == 1) (coordOfReg24 (rPotBNucA r41) β)
        (coordOfReg24 (rPotBPortB r41) β) (coordOfReg24 (rPotBElecA r41) β))
  else 0

theorem routed_or_of_validFlags {Wp n : ℕ} {r41 : QRegister (122 + Wp) n}
    {β : BitAssignment n} (hV : ValidPotBFlags r41 β) :
    let g := β (wPotBIsPot r41) == 1
    let s0 := β (wPotBIsScreen r41) == 1
    let n0 := β (wPotBIsNN r41) == 1
    (g = false ∧ s0 = false ∧ n0 = false) ∨ (g = true ∧ (s0 = false → n0 = false)) := by
  dsimp only
  rcases DynCircExt.bit_cases (β (wPotBIsPot r41)) with hp | hp
  · obtain ⟨hs, hn⟩ := hV.1 hp
    exact .inl ⟨by simp [hp], by simp [hs], by simp [hn]⟩
  · refine .inr ⟨by simp [hp], fun hs ↦ ?_⟩
    rcases DynCircExt.bit_cases (β (wPotBIsScreen r41)) with hs0 | hs1 <;> simp_all [hV.2]

/-- State update performed by `wrapHdrCascade2` on `r41[240..241]` when `isCsel = true`. -/
def hdrWrapMux {Wp n : ℕ} (h193 : 193 ≤ Wp) (isCsel : Bool) (r41 : QRegister (122 + Wp) n)
    (β : BitAssignment n) : BitAssignment n :=
  if isCsel then
    Function.update (Function.update β
      (r41 ⟨240, by omega⟩) (β (r41 ⟨122 + Wp - 1, by omega⟩) * β (wPotBIsScreen r41)))
      (r41 ⟨241, by omega⟩)
      ((β (r41 ⟨122 + Wp - 1, by omega⟩) * β (wPotBIsScreen r41)) * β (wPotBIsNN r41))
  else β

theorem hdrWrapMux_keep {Wp n : ℕ} (h193 : 193 ≤ Wp) (isCsel : Bool) (r41 : QRegister (122 + Wp) n)
    (β : BitAssignment n) (m : ℕ) (hm : m < 122 + Wp) (h0 : m ≠ 240) (h1 : m ≠ 241) :
    hdrWrapMux h193 isCsel r41 β (r41 ⟨m, hm⟩) = β (r41 ⟨m, hm⟩) := by
  unfold hdrWrapMux
  cases isCsel <;> simp only [↓reduceIte, Bool.false_eq_true]
  rw [Function.update_of_ne (r41_ne r41 hm _ h1), Function.update_of_ne (r41_ne r41 hm _ h0)]

theorem step_wrapHdrCascade2 {Var : Type} [Fintype Var] [DecidableEq Var]
    {W Wp n : ℕ} [NeZero (2 ^ n)] (h193 : 193 ≤ Wp) (isCsel : Bool)
    (v : Var) (rWork : QRegister W n) (r41 : QRegister (122 + Wp) n)
    (stPre stPost : BitAssignment n → BitAssignment n) (phPre phPost : BitAssignment n → ZMod 2)
    (mid : DynamicCircuit Var n)
    (hCln240 : ∀ δ, (∀ q, δ (rWork q) = 0) →
      stPre δ (r41 ⟨240, by omega⟩) = 0 ∧ stPost δ (r41 ⟨240, by omega⟩) = 0)
    (hCln241 : ∀ δ, (∀ q, δ (rWork q) = 0) →
      stPre δ (r41 ⟨241, by omega⟩) = 0 ∧ stPost δ (r41 ⟨241, by omega⟩) = 0)
    (hMid : SubspaceStep
      (mkKetOpW rWork (fun δ ↦ hdrWrapMux h193 isCsel r41 (stPre δ)) phPre)
      (mkKetOpW rWork (fun δ ↦ hdrWrapMux h193 isCsel r41 (stPost δ)) phPost) mid) :
    SubspaceStep (mkKetOpW rWork stPre phPre) (mkKetOpW rWork stPost phPost)
      (wrapHdrCascade2 h193 isCsel v r41 mid) ∧
    (wrapHdrCascade2 h193 isCsel v r41 mid).count .T = (if isCsel then 8 else 0) + mid.count .T ∧
    (wrapHdrCascade2 h193 isCsel v r41 mid).count .TOFF = mid.count .TOFF := by
  unfold wrapHdrCascade2
  cases isCsel
  · exact ⟨hMid, (zero_add _).symm, rfl⟩
  · simp only [↓reduceIte]
    let hn {a b : ℕ} {ha : a < 122 + Wp} {hb : b < 122 + Wp} (h : a ≠ b := by omega) :=
      r41_ne r41 ha hb h
    let reg5 := rReg5 (r41 ⟨122 + Wp - 1, by omega⟩) (wPotBIsScreen r41) (wPotBIsNN r41)
      (r41 ⟨240, by omega⟩) (r41 ⟨241, by omega⟩) hn hn hn hn hn hn hn hn hn hn
    have hEq (β : BitAssignment n) (h0 : β (r41 ⟨240, by omega⟩) = 0)
        (h1 : β (r41 ⟨241, by omega⟩) = 0) :
        stepCB reg5 cpHdr2.fwdBits β = hdrWrapMux h193 true r41 β :=
      writeReg_eq_of_reg_out reg5 _ β _
        (fun u ↦ by
          have hf := cpHdr2_fwd (fun k ↦ β (reg5 k))
          have hk {m : ℕ} {hm : m < 122 + Wp} (e0 : m ≠ 240 := by omega)
              (e1 : m ≠ 241 := by omega) := (hdrWrapMux_keep h193 true r41 β m hm e0 e1).symm
          fin_cases u
          · exact hf.1.trans hk
          · exact hf.2.1.trans hk
          · exact hf.2.2.1.trans hk
          · simpa [hdrWrapMux, reg5, rReg5, hn, h0] using hf.2.2.2.1
          · simpa [hdrWrapMux, reg5, rReg5, h0, h1] using hf.2.2.2.2)
        (fun _ hw ↦ ((Function.update_of_ne (hw 4) _ _).trans
          (Function.update_of_ne (hw 3) _ β)).symm)
    obtain ⟨s, t, f, _⟩ := subspaceStep_wrapOnReg_vprog2 v rWork reg5
      ({3, 4} : Finset (Wire 5)) cpHdr2 2 cpHdr2_vp cpHdr2_and stPre stPost phPre phPost mid
      (fun u hu δ hz ↦ by fin_cases u <;> simp_all [reg5, rReg5])
      (fun u hu δ hz ↦ by fin_cases u <;> simp_all [reg5, rReg5])
      (subspaceStep_of_eq_pre_local
        (mkKetOpW_congr rWork (fun δ hz ↦ hEq _ (hCln240 δ hz).1 (hCln241 δ hz).1) fun _ _ ↦ rfl)
        (subspaceStep_of_eq_post hMid
          (mkKetOpW_congr rWork (fun δ hz ↦ (hEq _ (hCln240 δ hz).2 (hCln241 δ hz).2).symm)
            fun _ _ ↦ rfl)))
    exact ⟨s, t, f⟩

theorem rMuxLeg1Hdr5_0_false {Wp n : ℕ} (h193 : 193 ≤ Wp) (r41 : QRegister (122 + Wp) n) :
    rMuxLeg1Hdr5 h193 false r41 ⟨0, ow0_lt5⟩ = r41 ⟨2, by omega⟩ := rfl
theorem rMuxLeg1Hdr5_1_false {Wp n : ℕ} (h193 : 193 ≤ Wp) (r41 : QRegister (122 + Wp) n) :
    rMuxLeg1Hdr5 h193 false r41 ⟨1, ow1_lt5⟩ = r41 ⟨1, by omega⟩ := rfl
theorem rMuxLeg1Hdr5_2_false {Wp n : ℕ} (h193 : 193 ≤ Wp) (r41 : QRegister (122 + Wp) n) :
    rMuxLeg1Hdr5 h193 false r41 ⟨2, ow2_lt5⟩ = r41 ⟨4, by omega⟩ := rfl
theorem rMuxLeg1Hdr5_0_true {Wp n : ℕ} (h193 : 193 ≤ Wp) (r41 : QRegister (122 + Wp) n) :
    rMuxLeg1Hdr5 h193 true r41 ⟨0, ow0_lt5⟩ = r41 ⟨122 + Wp - 1, by omega⟩ := rfl
theorem rMuxLeg1Hdr5_1_true {Wp n : ℕ} (h193 : 193 ≤ Wp) (r41 : QRegister (122 + Wp) n) :
    rMuxLeg1Hdr5 h193 true r41 ⟨1, ow1_lt5⟩ = r41 ⟨240, by omega⟩ := rfl
theorem rMuxLeg1Hdr5_2_true {Wp n : ℕ} (h193 : 193 ≤ Wp) (r41 : QRegister (122 + Wp) n) :
    rMuxLeg1Hdr5 h193 true r41 ⟨2, ow2_lt5⟩ = r41 ⟨241, by omega⟩ := rfl
theorem rMuxLeg1Hdr5_3 {Wp n : ℕ} (h193 : 193 ≤ Wp) (isCsel : Bool) (r41 : QRegister (122 + Wp) n) :
    rMuxLeg1Hdr5 h193 isCsel r41 ⟨3, ow3_lt5⟩ = r41 ⟨5, by omega⟩ := rfl
theorem rMuxLeg1Hdr5_4 {Wp n : ℕ} (h193 : 193 ≤ Wp) (isCsel : Bool) (r41 : QRegister (122 + Wp) n) :
    rMuxLeg1Hdr5 h193 isCsel r41 ⟨4, ow4_lt5⟩ = r41 ⟨6, by omega⟩ := rfl

/- Section 5D1: `muxSt` distance-register helpers, `step_pMuxStageA`, and `step_pMuxStageC`. -/

theorem coordOfReg24_muxSt_m1 {Wp n : ℕ} (h193 : 193 ≤ Wp) (isCsel : Bool)
    (r41 : QRegister (122 + Wp) n) (hasD2 : Bool) (z16 : Fin 16 → ZMod 2) (β : BitAssignment n) :
    coordOfReg24 (rMuxM1 h193 isCsel r41) (muxSt h193 isCsel r41 0 hasD2 z16 β) =
      if β (wPotBIsNN r41) == 1 then coordOfReg24 (rPotBNucA r41) β else coordOfReg24 (rPotBElecA
          r41) β :=
  coordOfReg24_ite (β (wPotBIsNN r41) == 1) _ _ _ _ _ fun i ↦ by
    rw [muxSt_m1]
    simp only [Nat.zero_le, ↓reduceIte]

theorem coordOfReg24_muxSt_m2 {Wp n : ℕ} (h193 : 193 ≤ Wp) (isCsel : Bool)
    (r41 : QRegister (122 + Wp) n) (m0 : ℕ) (hasD2 : Bool) (z16 : Fin 16 → ZMod 2)
        (β : BitAssignment n) :
    coordOfReg24 (rMuxM2 h193 isCsel r41) (muxSt h193 isCsel r41 m0 hasD2 z16 β) =
      if β (wPotBIsScreen r41) == 1 then coordOfReg24 (rPotBPortB r41) β else coordOfReg24
          (rPotBNucA r41) β :=
  coordOfReg24_ite (β (wPotBIsScreen r41) == 1) _ _ _ _ _ (muxSt_m2 h193 isCsel r41 m0 hasD2 z16 β)

theorem openCoordDistSq_muxSt_m1_m2 {Wp n : ℕ} (h193 : 193 ≤ Wp) (isCsel : Bool)
    (r41 : QRegister (122 + Wp) n) (hasD2 : Bool) (z16 : Fin 16 → ZMod 2) (β : BitAssignment n) :
    openCoordDistSq (coordOfReg24 (rMuxM1 h193 isCsel r41) (muxSt h193 isCsel r41 0 hasD2 z16 β))
      (coordOfReg24 (rMuxM2 h193 isCsel r41) (muxSt h193 isCsel r41 0 hasD2 z16 β)) =
          muxD2Val r41 β := by
  rw [coordOfReg24_muxSt_m1, coordOfReg24_muxSt_m2]; rfl

/- Section 5D2: `midWOfMode_congr_div8`, `rMidZHi_rMuxMid`, and `step_pMuxStageB`. -/

theorem idxMuxMid_y (Wp : ℕ) (isCsel : Bool) (k : Fin 36) :
    idxMuxMid Wp isCsel (5 + k.val) = 122 + (18 + k.val) := by
  unfold idxMuxMid; have := k.isLt; split_ifs <;> omega
theorem idxMuxMid_zLo (Wp : ℕ) (isCsel : Bool) (i : Fin 14) :
    idxMuxMid Wp isCsel (41 + i.val) = 92 + i.val := by
  unfold idxMuxMid; have := i.isLt; split_ifs <;> omega
theorem idxMuxMid_zHi (Wp : ℕ) (isCsel : Bool) (j : Fin 16) :
    idxMuxMid Wp isCsel (41 + (14 + j.val)) = 106 + j.val := by
  unfold idxMuxMid; have := j.isLt; split_ifs <;> omega
theorem idxMuxMid_zHi' (Wp : ℕ) (isCsel : Bool) (j : Fin 16) :
    idxMuxMid Wp isCsel (41 + 14 + j.val) = 106 + j.val := by
  unfold idxMuxMid; have := j.isLt; split_ifs <;> omega
theorem idxMuxMid_cln (Wp : ℕ) (isCsel : Bool) (j : ℕ) :
    idxMuxMid Wp isCsel (71 + j) = 122 + (54 + j) := by
  unfold idxMuxMid; split_ifs <;> omega
theorem rMidZHi_rMuxMid {Wp kMid kRest M n : ℕ} (h193 : 193 ≤ Wp) (isCsel : Bool)
    (hM : M ≤ 24) (hCap : 54 + kRest + (48 - M) ≤ Wtop Wp isCsel) (hkM : kMid ≤ kRest)
    (r41 : QRegister (122 + Wp) n) :
    MidOWCore.rMidZHi 14 kMid mux_le14_30 (rMuxMid h193 isCsel hM hCap hkM r41) = rMuxZ16 r41 :=
  QRegister.ext (Function.Embedding.ext fun j ↦
      congrArg r41.wires (Fin.ext (idxMuxMid_zHi' Wp isCsel j)))

/- Section 5E1: Outer `wrapGateCsel + wrapMux1Dist + wrapMux2_24` assembly and `step_pMuxCore`. -/

theorem writeReg_self_z16 {Wp n : ℕ} (r41 : QRegister (122 + Wp) n) (β : BitAssignment n) :
    writeReg β (rMuxZ16 r41) (fun j ↦ β (rMuxZ16 r41 j)) = β :=
  writeReg_eq_of_reg_out (rMuxZ16 r41) _ β β (fun _ ↦ rfl) (fun _ _ ↦ rfl)

/-- State update performed by `wrapGateCsel` on `r41[122 + Wp - 1]`. -/
def gateWrapMux {Wp n : ℕ} (h193 : 193 ≤ Wp) (isCsel : Bool) (r41 : QRegister (122 + Wp) n)
    (β : BitAssignment n) : BitAssignment n :=
  if isCsel then
    Function.update β (r41 ⟨122 + Wp - 1, by omega⟩) (β (wPotBLocQ r41) * β (wPotBIsPot r41))
  else β

theorem step_wrapGateCsel {Var : Type} [Fintype Var] [DecidableEq Var]
    {W Wp n : ℕ} [NeZero (2 ^ n)] (h193 : 193 ≤ Wp) (isCsel : Bool)
    (v : Var) (rWork : QRegister W n) (r41 : QRegister (122 + Wp) n)
    (stPre stPost : BitAssignment n → BitAssignment n) (phPre phPost : BitAssignment n → ZMod 2)
    (mid : DynamicCircuit Var n)
    (hCln : ∀ δ, (∀ q, δ (rWork q) = 0) →
      stPre δ (r41 ⟨122 + Wp - 1, by omega⟩) = 0 ∧ stPost δ (r41 ⟨122 + Wp - 1, by omega⟩) = 0)
    (hMid : SubspaceStep
      (mkKetOpW rWork (fun δ ↦ gateWrapMux h193 isCsel r41 (stPre δ)) phPre)
      (mkKetOpW rWork (fun δ ↦ gateWrapMux h193 isCsel r41 (stPost δ)) phPost) mid) :
    SubspaceStep (mkKetOpW rWork stPre phPre) (mkKetOpW rWork stPost phPost)
      (wrapGateCsel h193 isCsel v r41 mid) ∧
    (wrapGateCsel h193 isCsel v r41 mid).count .T = (if isCsel then 4 else 0) + mid.count .T ∧
    (wrapGateCsel h193 isCsel v r41 mid).count .TOFF = mid.count .TOFF := by
  unfold gateWrapMux at hMid
  unfold wrapGateCsel
  cases isCsel
  · exact ⟨hMid, (zero_add _).symm, rfl⟩
  · simp only [↓reduceIte] at hMid ⊢
    let hn {a b : ℕ} {ha : a < 122 + Wp} {hb : b < 122 + Wp} (h : a ≠ b := by omega) :=
      r41_ne r41 ha hb h
    let reg3 := rReg3 (wPotBLocQ r41) (wPotBIsPot r41) (r41 ⟨122 + Wp - 1, by omega⟩) hn hn hn
    have hEq (β : BitAssignment n) (h0 : β (r41 ⟨122 + Wp - 1, by omega⟩) = 0) :
        stepCB reg3 cpAnd3.fwdBits β =
          Function.update β (r41 ⟨122 + Wp - 1, by omega⟩) (β (wPotBLocQ r41) * β (wPotBIsPot r41))
              :=
      writeReg_eq_of_reg_out reg3 _ β _
        (fun u ↦ by
          have hf := cpAnd3_fwd (fun k ↦ β (reg3 k))
          fin_cases u
          · exact hf.1.trans (Function.update_of_ne hn _ β).symm
          · exact hf.2.1.trans (Function.update_of_ne hn _ β).symm
          · refine hf.2.2.trans ?_
            change β (r41 ⟨122 + Wp - 1, by omega⟩) + β (wPotBLocQ r41) * β (wPotBIsPot r41) =
              Function.update β _ _ (r41 ⟨122 + Wp - 1, by omega⟩)
            rw [Function.update_self, h0, zero_add])
        (fun _ hw ↦ (Function.update_of_ne (hw 2) _ β).symm)
    obtain ⟨s, t, f, _⟩ := subspaceStep_wrapOnReg_vprog2 v rWork reg3
      ({2} : Finset (Wire 3)) cpAnd3 1 cpAnd3_vp cpAnd3_and stPre stPost phPre phPost mid
      (fun _ hu δ hz ↦ Finset.mem_singleton.mp hu ▸ (hCln δ hz).1)
      (fun _ hu δ hz ↦ Finset.mem_singleton.mp hu ▸ (hCln δ hz).2)
      (subspaceStep_of_eq_pre_local
        (mkKetOpW_congr rWork (fun δ hz ↦ hEq _ (hCln δ hz).1) fun _ _ ↦ rfl)
        (subspaceStep_of_eq_post hMid
          (mkKetOpW_congr rWork (fun δ hz ↦ (hEq _ (hCln δ hz).2).symm) fun _ _ ↦ rfl)))
    exact ⟨s, t, f⟩
end QuantumComputation.Specs.PhotochemistrySolution.WStateMux48
end

noncomputable section
namespace QuantumComputation.Specs.PhotochemistrySolution.CtrlSafeOracleBase.Qrom
open PhotochemistrySolution PhotochemistrySolution.Stage4FineLoad65
  PhotochemistrySolution.ZeroNEremAxisSq18 PhotochemistrySolution.ZeroNEremCsa36Kick
open PhotochemistrySolution.CoulombFast PhotochemistrySolution.PopBernstein
  PhotochemistrySolution.BandEnc12Sync
def blkTblDualLegLo (k : ℕ) : ℕ :=
    cond (fastLtPopB k 32) ( cond (fastLtPopB k 16) ( cond (fastLtPopB k 8) ( cond (fastLtPopB k 4)
    ( cond (fastLtPopB k 2) ( cond (fastLtPopB k 1)
    ( pack4Words 0xab72ddec0 0xab0091580 0xaa8f9ba80 0xaa1fefac0 )
    ( pack4Words 0xaa1fefac0 0xa9b043bc0 0xa941e1980 0xa8d4bce80 ) ) ( cond (fastLtPopB k 3)
    ( pack4Words 0xa8d4bce80 0xa86798340 0xa7fbb1040 0xa790fb880 )
    ( pack4Words 0xa790fb880 0xa726461c0 0xa6bcc2500 0xa65465340 ) ) ) ( cond (fastLtPopB k 6)
    ( cond (fastLtPopB k 5) ( pack4Words 0xa65465340 0xa5ec081c0 0xa584d1a40 0xa51eb7300 )
    ( pack4Words 0xa51eb7300 0xa4b89cdc0 0xa4539e7c0 0xa3efb2240 ) ) ( cond (fastLtPopB k 7)
    ( pack4Words 0xa3efb2240 0xa38bc5d40 0xa328eb900 0xa2c719c80 )
    ( pack4Words 0xa2c719c80 0xa26548080 0xa2047eac0 0xa1a4b4c80 ) ) ) ) ( cond (fastLtPopB k 12)
    ( cond (fastLtPopB k 10) ( cond (fastLtPopB k 9)
    ( pack4Words 0xa1a4b4c80 0xa144eaec0 0xa0e620640 0xa0884ca00 )
    ( pack4Words 0xa0884ca00 0xa02a78e80 0x9fcd9be80 0x9f71ad5c0 ) ) ( cond (fastLtPopB k 11)
    ( pack4Words 0x9f71ad5c0 0x9f15bec40 0x9ebabed40 0x9e60a5680 )
    ( pack4Words 0x9e60a5680 0x9e068c000 0x9dad593c0 0x9d5505900 ) ) ) ( cond (fastLtPopB k 14)
    ( cond (fastLtPopB k 13) ( pack4Words 0x9d5505900 0x9cfcb1ec0 0x9ca53d540 0x9c4ea0bc0 )
    ( pack4Words 0x9c4ea0bc0 0x9bf8042c0 0x9ba23f740 0x9b4d4be40 ) ) ( cond (fastLtPopB k 15)
    ( pack4Words 0x9b4d4be40 0x9af858400 0x9aa435d40 0x9a50ddd00 )
    ( pack4Words 0x9a50ddd00 0x99fd85e80 0x99aaf8800 0x99592f4c0 ) ) ) ) ) ( cond (fastLtPopB k 24)
    ( cond (fastLtPopB k 20) ( cond (fastLtPopB k 18) ( cond (fastLtPopB k 17)
    ( pack4Words 0x99592f4c0 0x9907662c0 0x98b661300 0x98661a980 )
    ( pack4Words 0x98661a980 0x9815d3fc0 0x97c64b980 0x97777bb80 ) ) ( cond (fastLtPopB k 19)
    ( pack4Words 0x97777bb80 0x9728abd80 0x96da94980 0x968d30280 )
    ( pack4Words 0x968d30280 0x963fcbd40 0x95f31a980 0x95a716ec0 ) ) ) ( cond (fastLtPopB k 22)
    ( cond (fastLtPopB k 21) ( pack4Words 0x95a716ec0 0x955b13500 0x950fbd780 0x94c510380 )
    ( pack4Words 0x94c510380 0x947a63140 0x94305e780 0x93e6fdb80 ) ) ( cond (fastLtPopB k 23)
    ( pack4Words 0x93e6fdb80 0x939d9d040 0x9354e01c0 0x930cc2540 )
    ( pack4Words 0x930cc2540 0x92c4a4700 0x927d25d80 0x923641cc0 ) ) ) ) ( cond (fastLtPopB k 28)
    ( cond (fastLtPopB k 26) ( cond (fastLtPopB k 25)
    ( pack4Words 0x923641cc0 0x91ef5ddc0 0x91a914780 0x916361780 )
    ( pack4Words 0x916361780 0x911dae7c0 0x90d891d40
  0x9094075c0 ) ) ( cond (fastLtPopB k 27)
      ( pack4Words 0x9094075c0 0x904f7cf00 0x900b84b00 0x8fc81aac0 )
      ( pack4Words 0x8fc81aac0 0x8f84b0ac0 0x8f41d4e80 0x8eff83780 ) ) ) ( cond (fastLtPopB k 30)
      ( cond (fastLtPopB k 29) ( pack4Words 0x8eff83780 0x8ebd32040 0x8e7b6b0c0 0x8e3a2ac80 )
      ( pack4Words 0x8e3a2ac80 0x8df8ea7c0 0x8db830d80 0x8d77fa680 ) ) ( cond (fastLtPopB k 31)
      ( pack4Words 0x8d77fa680 0x8d37c3ec0 0x8cf810a00 0x8cb8dd0c0 )
      ( pack4Words 0x8cb8dd0c0 0x8c79a97c0 0x8c3af5900 0x8bfcbe240 ) ) ) ) ) )
      ( cond (fastLtPopB k 48) ( cond (fastLtPopB k 40) ( cond (fastLtPopB k 36)
      ( cond (fastLtPopB k 34) ( cond (fastLtPopB k 33)
      ( pack4Words 0x8bfcbe240 0x8bbe86b00 0x8b80cbb40 0x8b4389e40 )
      ( pack4Words 0x8b4389e40 0x8b06482c0 0x8ac97f980 0x8a8d2d3c0 ) ) ( cond (fastLtPopB k 35)
      ( pack4Words 0x8a8d2d3c0 0x8a50dae00 0x8a14feb00 0x89d995bc0 )
      ( pack4Words 0x89d995bc0 0x899e2cb80 0x896336f40 0x8928b1880 ) ) ) ( cond (fastLtPopB k 38)
      ( cond (fastLtPopB k 37) ( pack4Words 0x8928b1880 0x88ee2c340 0x88b417180 0x887a6f980 )
      ( pack4Words 0x887a6f980 0x8840c8240 0x88078e340 0x87cebf4c0 ) ) ( cond (fastLtPopB k 39)
      ( pack4Words 0x87cebf4c0 0x8795f0580 0x875d8c440 0x872590a40 )
      ( pack4Words 0x872590a40 0x86ed94f80 0x86b6019c0 0x867ed4280 ) ) ) ) ( cond (fastLtPopB k 44)
      ( cond (fastLtPopB k 42) ( cond (fastLtPopB k 41)
      ( pack4Words 0x867ed4280 0x8647a6b00 0x8610df180 0x85da7ae80 )
      ( pack4Words 0x85da7ae80 0x85a416d40 0x856e16180 0x853876780 ) ) ( cond (fastLtPopB k 43)
      ( pack4Words 0x853876780 0x8502d6e80 0x84cd98700 0x8498b8d40 )
      ( pack4Words 0x8498b8d40 0x8463d9480 0x842f588c0 0x83fb34800 ) ) ) ( cond (fastLtPopB k 46)
      ( cond (fastLtPopB k 45) ( pack4Words 0x83fb34800 0x83c7107c0 0x8393492c0 0x835fdc5c0 )
      ( pack4Words 0x835fdc5c0 0x832c6f980 0x82f95d700 0x82c6a3c40 ) ) ( cond (fastLtPopB k 47)
      ( pack4Words 0x82c6a3c40 0x8293ea180 0x826189080 0x822f7e640 )
      ( pack4Words 0x822f7e640 0x81fd73d40 0x81cbbfd40 0x819a60740 ) ) ) ) )
      ( cond (fastLtPopB k 56) ( cond (fastLtPopB k 52) ( cond (fastLtPopB k 50)
      ( cond (fastLtPopB k 49) ( pack4Words 0x819a60740 0x816901180 0x8137f6580 0x81073e500 )
      ( pack4Words 0x81073e500 0x80d686580 0x80a621340 0x80760cf40 ) ) ( cond (fastLtPopB k 51)
      ( pack4Words 0x80760cf40 0x8045f8b40 0x801635740 0x7fe6c16c0 )
      ( pack4Words 0x7fe6c16c0 0x7fb74d540 0x7f8828980 0x7f5951440 ) ) ) ( cond (fastLtPopB k 54)
      ( cond (fastLtPopB k 53) ( pack4Words
  0x7f5951440 0x7f2a79f80 0x7efbf0480 0x7ecdb2540 )
      ( pack4Words 0x7ecdb2540 0x7e9f74740 0x7e71827c0 0x7e43dab80 ) ) ( cond (fastLtPopB k 55)
      ( pack4Words 0x7e43dab80 0x7e16330c0 0x7de8d5900 0x7dbbc0dc0 )
      ( pack4Words 0x7dbbc0dc0 0x7d8eac200 0x7d61e0280 0x7d355b6c0 ) ) ) ) ( cond (fastLtPopB k 60)
      ( cond (fastLtPopB k 58) ( cond (fastLtPopB k 57)
      ( pack4Words 0x7d355b6c0 0x7d08d6b80 0x7cdc992c0 0x7cb0a1680 )
      ( pack4Words 0x7cb0a1680 0x7c84a9b00 0x7c58f79c0 0x7c2d89f80 ) ) ( cond (fastLtPopB k 59)
      ( pack4Words 0x7c2d89f80 0x7c021c540 0x7bd6f3080 0x7bac0ca80 )
      ( pack4Words 0x7bac0ca80 0x7b8126500 0x7b5682f00 0x7b2c21340 ) ) ) ( cond (fastLtPopB k 62)
      ( cond (fastLtPopB k 61) ( pack4Words 0x7b2c21340 0x7b01bf680 0x7ad79f5c0 0x7aadbf700 )
      ( pack4Words 0x7aadbf700 0x7a83df900 0x7a5a401c0 0x7a30dfa00 ) ) ( cond (fastLtPopB k 63)
      ( pack4Words 0x7a30dfa00 0x7a077f200 0x79de5dcc0 0x79b57a240 )
      ( pack4Words 0x79b57a240 0x798c96900 0x7963f0cc0 0x793b87940 ) ) ) ) ) )
def blkTblDualLeg (k : ℕ) : ℕ :=
    cond (fastLtPopB k 64) (blkTblDualLegLo k) ( cond (fastLtPopB k 128) ( cond (fastLtPopB k 96)
    ( cond (fastLtPopB k 80) ( cond (fastLtPopB k 72) ( cond (fastLtPopB k 68)
    ( cond (fastLtPopB k 66) ( cond (fastLtPopB k 65)
    ( pack4Words 0x793b87940 0x78eab5440 0x789ad5540 0x784bde900 )
    ( pack4Words 0x784bde900 0x77fce7dc0 0x77aeda5c0 0x7761ad4c0 ) ) ( cond (fastLtPopB k 67)
    ( pack4Words 0x7761ad4c0 0x771480440 0x76c833a80 0x767cbf4c0 )
    ( pack4Words 0x767cbf4c0 0x76314afc0 0x75e6aec40 0x759ce2e40 ) ) ) ( cond (fastLtPopB k 70)
    ( cond (fastLtPopB k 69) ( pack4Words 0x759ce2e40 0x755317040 0x750a1b900 0x74c1e8e40 )
    ( pack4Words 0x74c1e8e40 0x7479b6300 0x74324c780 0x73eba4700 ) ) ( cond (fastLtPopB k 71)
    ( pack4Words 0x73eba4700 0x73a4fc700 0x735f16340 0x7319eaf80 )
    ( pack4Words 0x7319eaf80 0x72d4bfc00 0x72904f9c0 0x724c93f00 ) ) ) ) ( cond (fastLtPopB k 76)
    ( cond (fastLtPopB k 74) ( cond (fastLtPopB k 73)
    ( pack4Words 0x724c93f00 0x7208d85c0 0x71c5d1500 0x718378d00 )
    ( pack4Words 0x718378d00 0x7141204c0 0x70ff76340 0x70be74cc0 ) ) ( cond (fastLtPopB k 75)
    ( pack4Words 0x70be74cc0 0x707d73700 0x703d1a940 0x6ffd64ec0 )
    ( pack4Words 0x6ffd64ec0 0x6fbdaf300 0x6f7e9c900 0x6f4027bc0 ) ) ) ( cond (fastLtPopB k 78)
    ( cond (fastLtPopB k 77) ( pack4Words 0x6f4027bc0 0x6f01b2d40 0x6ec3dbc40 0x6e869d640 )
    ( pack4Words 0x6e869d640 0x6e495ef00 0x6e0cb9440 0x6dd0a7680 ) ) ( cond (fastLtPopB k 79)
    ( pack4Words 0x6dd0a7680 0x6d9495880 0x6d5917840 0x6d1e28b80 )
    ( pack4Words 0x6d1e28b80 0x6ce339e80 0x6ca8da500 0x6c6f05840 ) ) ) ) ) ( cond (fastLtPopB k 88)
    ( cond (fastLtPopB k 84) ( cond (fastLtPopB k 82) ( cond (fastLtPopB k 81)
    ( pack4Words 0x6c6f05840 0x6c3530b40 0x6bfbe6a40 0x6bc3232c0 )
    ( pack4Words 0x6bc3232c0 0x6b8a5fb80 0x6b5222bc0 0x6b1a683c0 ) ) ( cond (fastLtPopB k 83)
    ( pack4Words 0x6b1a683c0 0x6ae2adcc0 0x6aab75b80 0x6a74bc4c0 )
    ( pack4Words 0x6a74bc4c0 0x6a3e02dc0 0x6a07c7f80 0x69d207fc0 ) ) ) ( cond (fastLtPopB k 86)
    ( cond (fastLtPopB k 85) ( pack4Words 0x69d207fc0 0x699c48000 0x696702c80 0x693234e40 )
    ( pack4Words 0x693234e40 0x68fd67040 0x68c9104c0 0x68952d800 ) ) ( cond (fastLtPopB k 87)
    ( pack4Words 0x68952d800 0x68614ab40 0x682ddbb40 0x67fadd440 )
    ( pack4Words 0x67fadd440 0x67c7ded00 0x679550d80 0x676330440 ) ) ) ) ( cond (fastLtPopB k 92)
    ( cond (fastLtPopB k 90) ( cond (fastLtPopB k 89) ( pack4Words 0x676330440 0x67310fac0
  0x66ff5c800 0x66ce13980 ) ( pack4Words 0x66ce13980 0x669ccaa80 0x666bec100 0x663b74e00 ) )
      ( cond (fastLtPopB k 91) ( pack4Words 0x663b74e00 0x660afda80 0x65daeddc0 0x65ab42980 )
      ( pack4Words 0x65ab42980 0x657b97440 0x654c50b40 0x651d6bcc0 ) ) ) ( cond (fastLtPopB k 94)
      ( cond (fastLtPopB k 93) ( pack4Words 0x651d6bcc0 0x64ee86f40 0x64c004080 0x6491e0480 )
      ( pack4Words 0x6491e0480 0x6463bc8c0 0x6435f8080 0x6408904c0 ) ) ( cond (fastLtPopB k 95)
      ( pack4Words 0x6408904c0 0x63db28900 0x63ae1d980 0x63816cdc0 )
      ( pack4Words 0x63816cdc0 0x6354bc240 0x632865dc0 0x62fc67600 ) ) ) ) ) )
      ( cond (fastLtPopB k 112) ( cond (fastLtPopB k 104) ( cond (fastLtPopB k 100)
      ( cond (fastLtPopB k 98) ( cond (fastLtPopB k 97)
      ( pack4Words 0x62fc67600 0x62d069080 0x62a4c2840 0x627971d80 )
      ( pack4Words 0x627971d80 0x624e21200 0x6223263c0 0x61f87ed00 ) ) ( cond (fastLtPopB k 99)
      ( pack4Words 0x61f87ed00 0x61cdd7640 0x61a383900 0x617981340 )
      ( pack4Words 0x617981340 0x614f7ecc0 0x6125cdf40 0x60fc6c740 ) ) ) ( cond (fastLtPopB k 102)
      ( cond (fastLtPopB k 101) ( pack4Words 0x60fc6c740 0x60d30b040 0x60a9f8f40 0x608134780 )
      ( pack4Words 0x608134780 0x60586ff00 0x602ff8e80 0x6007cd7c0 ) ) ( cond (fastLtPopB k 103)
      ( pack4Words 0x6007cd7c0 0x5fdfa2140 0x5fb7c2400 0x5f902c3c0 )
      ( pack4Words 0x5f902c3c0 0x5f6896200 0x5f4149f40 0x5f1a45c00 ) ) ) ) ( cond (fastLtPopB k 108)
      ( cond (fastLtPopB k 106) ( cond (fastLtPopB k 105)
      ( pack4Words 0x5f1a45c00 0x5ef341880 0x5ecc855c0 0x5ea60f7c0 )
      ( pack4Words 0x5ea60f7c0 0x5e7f99a00 0x5e596a180 0x5e337f340 ) ) ( cond (fastLtPopB k 107)
      ( pack4Words 0x5e337f340 0x5e0d94600 0x5de7ee180 0x5dc28b0c0 )
      ( pack4Words 0x5dc28b0c0 0x5d9d27e40 0x5d7807f80 0x5d5329700 ) ) ) ( cond (fastLtPopB k 110)
      ( cond (fastLtPopB k 109) ( pack4Words 0x5d5329700 0x5d2e4af80 0x5d09ae000 0x5ce551140 )
      ( pack4Words 0x5ce551140 0x5cc0f4380 0x5c9cd7580 0x5c78f9200 ) ) ( cond (fastLtPopB k 111)
      ( pack4Words 0x5c78f9200 0x5c551ae40 0x5c317b340 0x5c0e18c80 )
      ( pack4Words 0x5c0e18c80 0x5beab65c0 0x5bc791200 0x5ba4a7b80 ) ) ) ) )
      ( cond (fastLtPopB k 120) ( cond (fastLtPopB k 116) ( cond (fastLtPopB k 114)
      ( cond (fastLtPopB k 113) ( pack4Words 0x5ba4a7b80 0x5b81be580 0x5b5f10d00 0x5b3c9dc00 )
      ( pack4Words 0x5b3c9dc00 0x5b1a2ac00 0x5af7f2440 0x5ad5f3080 ) ) ( cond (fastLtPopB k 115)
      ( pack4Words 0x5ad5f3080 0x5ab3f3cc0 0x5a922dd40 0x5a709fd80 )
      ( pack4Words 0x5a709fd80 0x5a4f11f40
  0x5a2dbbf40 0x5a0c9cd80 ) ) ) ( cond (fastLtPopB k 118) ( cond (fastLtPopB k 117)
      ( pack4Words 0x5a0c9cd80 0x59eb7db80 0x59ca95680 0x59a9e2c40 )
      ( pack4Words 0x59a9e2c40 0x598930280 0x5968b3240 0x59486aa80 ) ) ( cond (fastLtPopB k 119)
      ( pack4Words 0x59486aa80 0x592822300 0x59080e480 0x58e82dbc0 )
      ( pack4Words 0x58e82dbc0 0x58c84d380 0x58a8a0240 0x5889256c0 ) ) ) ) ( cond (fastLtPopB k 124)
      ( cond (fastLtPopB k 122) ( cond (fastLtPopB k 121)
      ( pack4Words 0x5889256c0 0x5869aaac0 0x584a62600 0x582b4b500 )
      ( pack4Words 0x582b4b500 0x580c34500 0x57ed4e980 0x57ce99400 ) ) ( cond (fastLtPopB k 123)
      ( pack4Words 0x57ce99400 0x57afe3e80 0x57915ecc0 0x577309240 )
      ( pack4Words 0x577309240 0x5754b36c0 0x57368d1c0 0x571895280 ) ) ) ( cond (fastLtPopB k 126)
      ( cond (fastLtPopB k 125) ( pack4Words 0x571895280 0x56fa9d380 0x56dcd3ac0 0x56bf379c0 )
      ( pack4Words 0x56bf379c0 0x56a19b980 0x56842cfc0 0x5666eafc0 ) ) ( cond (fastLtPopB k 127)
      ( pack4Words 0x5666eafc0 0x5649a8e80 0x562c93900 0x560fa9d40 )
      ( pack4Words 0x560fa9d40 0x55f2c0300 0x55d602180 0x55b96ef80 ) ) ) ) ) ) ) 0)
abbrev word512DualLeg (idx : ℕ) : ℕ := wordFromPack4 blkTblDualLeg idx

private theorem word512DualLeg_lt_chk :
    ((List.range 512).all (fun idx ↦ decide (word512DualLeg idx < 2 ^ 36))) = true := by
      decide +kernel

theorem word512DualLeg_lt_pow36 (idx : ℕ) (hIdx : idx < 512) : word512DualLeg idx < 2 ^ 36 :=
  of_decide_eq_true (List.all_eq_true.mp word512DualLeg_lt_chk idx (List.mem_range.mpr hIdx))

private theorem word512DualLeg_lo6_chk :
    ((List.range 512).all (fun idx ↦ (List.range 6).all (fun j ↦
        !(word512DualLeg idx).testBit j))) = true := by
  decide +kernel

theorem word512DualLeg_lo6_zero {idx j : ℕ} (hIdx : idx < 512) (hj : j < 6) :
    (word512DualLeg idx).testBit j = false := by
  simpa [hIdx,
      hj] using List.all_eq_true.mp (List.all_eq_true.mp word512DualLeg_lo6_chk _ (by simpa)) _
      (by simpa)

/-- Depth-`d` binary-tree bit packer packing `2 ^ d` bits `f (base + 0) .. f (base + 2 ^ d - 1)`. -/
def packColPow2 : ℕ → ℕ → (ℕ → Bool) → ℕ
  | 0, base, f => cond (f base) 1 0
  | d + 1, base, f => packColPow2 d base f ||| (packColPow2 d (base + (1 <<< d)) f <<< (1 <<< d))

private theorem packColPow2_testBit (d base idx : ℕ) (f : ℕ → Bool) :
    (packColPow2 d base f).testBit idx = (decide (idx < 2 ^ d) && f (base + idx)) := by
  induction d generalizing base idx with
  | zero =>
        rcases idx with _ | idx <;> cases hf : f base <;> simp [packColPow2, hf, Nat.testBit_zero,
        Nat.testBit_succ]
  | succ d ih =>
    simp only [packColPow2, Nat.one_shiftLeft, Nat.testBit_or, Nat.testBit_shiftLeft, ih]
    by_cases h : idx < 2 ^ d
    · simp [h, show idx < 2 ^ (d + 1) by omega, show ¬(idx ≥ 2 ^ d) by omega]
    · simp [h, show idx ≥ 2 ^ d by omega, show (idx - 2 ^ d < 2 ^ d) ↔ idx < 2 ^ (d + 1) by omega,
        show base + 2 ^ d + (idx - 2 ^ d) = base + idx by omega]

/-- `36` `512`-bit column masks transposing `word512DualLeg`. -/
def dualLegExpCols36 : List ℕ :=
  (List.range 36).map (fun j ↦ packColPow2 9 0 (fun idx ↦ (word512DualLeg idx).testBit j))

theorem word512DualLeg_testBit_eq_expCols36 {idx j : ℕ} (hIdx : idx < 512) (hj : j < 36) :
    (dualLegExpCols36.getD j 0).testBit idx = (word512DualLeg idx).testBit j := by
  simp [dualLegExpCols36, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj,
      packColPow2_testBit, hIdx]

def word512DualLegLo6 (i : ℕ) : ℕ := (word512DualLeg i / 64) * 64
end QuantumComputation.Specs.PhotochemistrySolution.CtrlSafeOracleBase.Qrom

namespace QuantumComputation.Specs.PhotochemistrySolution.CtrlSafeOracleBase.Legs
open PhotochemistrySolution PhotochemistrySolution.ZeroNEremSpec PhotochemistrySolution.Sh14P5Mux17
/-- Base `m_ee` integer profile `[0, 116, 91, 64, 48, 24]` on `Pre5` `[2, 4, 8, 16, 48]`. -/
def mEEU10Pre5 (b : Fin 6) : ℤ :=
  match b.val with
  | 0 => 0
  | 1 => 116
  | 2 => 91
  | 3 => 64
  | 4 => 48
  | _ => 24
/--
Species-independent `m_nn` integer profile `[0, 175, 85, 40, 0, 0]` (`nn_unit = 187`) on `Pre5` .
-/
def mNNU10Pre5 (b : Fin 6) : ℤ :=
  match b.val with
  | 0 => 0
  | 1 => 175
  | 2 => 84
  | 3 => 38
  | _ => 0
/-- Scaled `187 * m_ee` `.ee` radial increments for `0.0000`-ULP Bezout cancellation. -/
def dEEU10Pre5 (b : Fin 6) : ℤ := 187 * mEEU10Pre5 b
/--
Scaled `187 * m_nn` `.nn` radial increments (`nn_unit = 187`) for `0.0000` -ULP Bezout cancellation.
-/
def dNNU10Pre5 (b : Fin 6) : ℤ := 187 * mNNU10Pre5 b
/--
Exact uniform-`U10` (`gain = 10`) `.en` radial increments cancelling `.ee` and `.nn` to `0` ULP.
-/
def dENU10Pre5 (sp : Fin 4) (b : Fin 6) : ℤ :=
  (10 * (372 * dEEU10Pre5 b + (187 - (speciesZ sp : ℤ)) * dNNU10Pre5 b)) / 374
/-- Leg-1 `.ee` signed table `cEE1[b] = (5580 + d_ee[b]) * 2^14`. -/
def cEE1U10Pre5 (b : Fin 6) : ℤ := (5580 + dEEU10Pre5 b) * 16384
/-- Leg-2 `.ee` signed table `cEE2[b] = (5580 + d_ee[b]) * 2^14` (`dc_ee = 0`). -/
def cEE2U10Pre5 (b : Fin 6) : ℤ := (5580 + dEEU10Pre5 b) * 16384
/-- Shared `.nn` signed table `cNN[b] = (-869 + d_nn[b]) * 2^14`. -/
def cNNU10Pre5 (b : Fin 6) : ℤ := (-865 + dNNU10Pre5 b) * 16384
/-- Uniform-`U10` `.en` signed table `cEN[sp][b] = (33713 + d_en[sp][b]) * 2^14`. -/
def cENU10Pre5 (sp : Fin 4) (b : Fin 6) : ℤ := (33757 + dENU10Pre5 sp b) * 16384
/-- Full `31`-bit modular Leg-1 shift `(2^29 - tbl1) mod 2^31` before `>>> 14` factoring. -/
def leg1Shift31U10Pre5 (s0 n0 : Bool) (sp : Fin 4) (b5 : Fin 6) : ℕ :=
  cond (Bool.not s0) (mod31OfInt ((536870912 : ℤ) - cENU10Pre5 sp b5))
    (cond (Bool.not n0) (mod31OfInt ((536870912 : ℤ) - cEE1U10Pre5 b5))
      (mod31OfInt ((536870912 : ℤ) - cNNU10Pre5 b5)))
/-- Full `31`-bit modular Leg-2 shift `(-tbl2) mod 2^31` before `>>> 14` factoring. -/
def leg2Shift31U10Pre5 (s0 n0 : Bool) (_sp : Fin 4) (b5 : Fin 6) : ℕ :=
  cond (Bool.not s0) 0 (cond (Bool.not n0) (mod31OfInt (-cEE2U10Pre5 b5))
      (mod31OfInt (-cNNU10Pre5 b5)))
/-- `17`-bit (`col_0..16`, bits `14..30`) uniform-`U10` Leg-1 target word. -/
def v1U10Pre5 (s0 n0 : Bool) (sp : Fin 4) (b5 : Fin 6) : ℕ := leg1Shift31U10Pre5 s0 n0 sp b5 >>> 14
/-- `17`-bit (`col_0..16`, bits `14..30`) uniform-`U10` Leg-2 target word. -/
def v2U10Pre5 (s0 n0 : Bool) (sp : Fin 4) (b5 : Fin 6) : ℕ := leg2Shift31U10Pre5 s0 n0 sp b5 >>> 14
/-- `Fin 8` uniform-`U10` Leg-1 `17`-bit target word on `fin8Bin`. -/
def v1Fin8U10Local (s0 n0 : Bool) (sp : Fin 4) (b : Fin 8) : ℕ := v1U10Pre5 s0 n0 sp (pre5OfFin8 b)
/-- `Fin 8` uniform-`U10` Leg-2 `17`-bit target word on `fin8Bin`. -/
def v2Fin8U10Local (s0 n0 : Bool) (sp : Fin 4) (b : Fin 8) : ℕ := v2U10Pre5 s0 n0 sp (pre5OfFin8 b)
end QuantumComputation.Specs.PhotochemistrySolution.CtrlSafeOracleBase.Legs

namespace QuantumComputation.Specs.PhotochemistrySolution.CtrlSafeOracleBase.MidOW60
open QProg DynamicCircuit Qubit PhotochemistrySolution PhotochemistrySolution.InPlaceModAdd
  PhotochemistrySolution.Poly28Sub254 PhotochemistrySolution.ScreenFermatCore
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt
open PhotochemistrySolution.MidOWCore
theorem gh16_finBitsVal_eq_zero {m : ℕ} (f : Fin m → ZMod 2) (h : ∀ j : Fin m, f j = 0) :
    finBitsVal f = 0 :=
  (congrArg finBitsVal (funext h)).trans (finBitsVal_zero_fun m)

theorem gh16_finBitsVal_fin1 (f : Fin 1 → ZMod 2) : finBitsVal f = (f 0).val := by
  rw [finBitsVal_succ, gh16_finBitsVal_eq_zero _ (fun i ↦ Fin.elim0 i), mul_zero, add_zero]

theorem ctrl_finBitsVal_fin1_local (f : Fin 1 → ZMod 2) : finBitsVal f = (f 0).val :=
    gh16_finBitsVal_fin1 f
theorem gh16_eq_of_finBitsVal_eq {m : ℕ} {f g : Fin m → ZMod 2} (h : finBitsVal f = finBitsVal g)
    (j : Fin m) :
    f j = g j := congrFun (finBitsVal_inj h) j
theorem gh16_zmod2_ite_beq_one (b : ZMod 2) : (if b == 1 then (1 : ZMod 2) else 0) = b := by
  rcases DynCircExt.bit_cases b with rfl | rfl <;> rfl

theorem gh16_majCarryBit_13_eq_14 (fA fB : Fin 14 → ZMod 2) (i : Fin 13) :
    majCarryBit (finBitsVal (fun k : Fin 13 ↦ fA ⟨k.val, by omega⟩))
      (finBitsVal (fun k : Fin 13 ↦ fB ⟨k.val, by omega⟩)) 0 i.val =
    majCarryBit (finBitsVal fA) (finBitsVal fB) 0 i.val := by
  simp only [majCarryBit, show ∀ f : Fin 14 → ZMod 2, finBitsVal f % 2 ^ (i.val + 1) =
      finBitsVal (fun k : Fin 13 ↦ f ⟨k.val, by omega⟩) % 2 ^ (i.val + 1) from fun f ↦ by
    rw [finBitsVal_split 13 1 f, show (2 ^ 13 : ℕ) = 2 ^ (i.val + 1) * 2 ^ (12 - i.val) by
      rw [← pow_add, show i.val + 1 + (12 - i.val) = 13 by omega], mul_assoc,
          Nat.add_mul_mod_self_left]]

theorem gh16_seam_maj_val (fA fB : Fin 14 → ZMod 2) (c8 : ZMod 2)
    (hc8 : c8.val = (finBitsVal (fun k : Fin 13 ↦ fA ⟨k.val, by omega⟩) +
      finBitsVal (fun k : Fin 13 ↦ fB ⟨k.val, by omega⟩)) / 2 ^ 13) :
    (((fA ⟨13, by omega⟩ + c8) * (fB ⟨13, by omega⟩ + c8) + c8).val) =
      (finBitsVal fA + finBitsVal fB) / 2 ^ 14 := by
  have ⟨hA, hB, hm, hlt⟩ : _ ∧ _ ∧ _ ∧ _ := ⟨finBitsVal_split 13 1 fA, finBitsVal_split 13 1 fB,
    zmod2_maj_id (fA ⟨13, by omega⟩) (fB ⟨13, by omega⟩) c8, ZMod.val_lt (fA ⟨13, by omega⟩ +
        fB ⟨13, by omega⟩ + c8)⟩
  simp only [gh16_finBitsVal_fin1, Fin.val_zero, Nat.add_zero] at hA hB
  omega

theorem gh16_two_pass_hi16 (zLo zHi w1Lo w1Hi w2Lo w2Hi : ℕ) :
    let cA9 := (zLo + w1Lo) / 2 ^ 14
    let sLo := (zLo + w1Lo) % 2 ^ 14
    let zHiA := (zHi + w1Hi + cA9) % 2 ^ 16
    let cB9 := (sLo + w2Lo) / 2 ^ 14
    let tot := (zLo + 2 ^ 14 * zHi) + (w1Lo + 2 ^ 14 * w1Hi) + (w2Lo + 2 ^ 14 * w2Hi)
    (zHiA + w2Hi + cB9) % 2 ^ 16 = (tot / 2 ^ 14) % 2 ^ 16 ∧
    (((zHi + w1Hi + cA9) / 2 ^ 16 : ℕ) : ZMod 2) + (((zHiA + w2Hi + cB9) / 2 ^ 16 : ℕ) : ZMod 2) =
      ((tot / 2 ^ 30 : ℕ) : ZMod 2) :=
  ⟨by omega, (Nat.cast_add _ _).symm.trans (congrArg Nat.cast (by omega))⟩

/-- Stage-4 `Mid_OW` (`isU10`) cost/pool index marker. -/
structure MidOWU10Pkg (isU10 : Bool) (lZ kMid tMid : ℕ) : Type where
end QuantumComputation.Specs.PhotochemistrySolution.CtrlSafeOracleBase.MidOW60

namespace QuantumComputation.Specs.PhotochemistrySolution.CtrlSafeOracleBase.CoulBase
open QProg Qubit PhotochemistrySolution CtrlSafeOracleBase.Qrom PhotochemistrySolution.FineLegendre
open PhotochemistrySolution.ZeroNEremAxisSq18 PhotochemistrySolution.PotOracleGen
  PhotochemistrySolution.EvenOctB70 PhotochemistrySolution.Coin70Lift
open _root_.QuantumComputation.Specs.PhotochemistrySolution.BandEnc12Sync (natOfZModBits_lt)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.PopBernstein (pAnd pCnot idx7OfParts
    t11OfParts parts_popBern_bounds dom22Bit rIdx7Of22 rK4Of22 compOutIdx pX95 evalPrimTree95_x)
def cmpBorrowStep (c t prev dst : ℕ) : PrimTree :=
  .node (.node (.node (pCnot prev c) (pCnot prev t)) (pAnd c t dst))
    (.node (.node (pCnot prev c) (pCnot prev t)) (pCnot t dst))

theorem evalPrimTree95_x_xor {d : ℕ} (hd : d < 96) (st i : ℕ) :
    (evalPrimTree 95 st (pX95 d)).testBit i = xor (st.testBit i) (decide (i = d)) := by
  by_cases h : i = d <;> simp [evalPrimTree95_x hd, h]

theorem out22_t11_bits {n : ℕ} (rOut22 : QRegister 22 n) (β : BitAssignment n)
    (isNN : Bool) {d2 : ℕ} (hd2 : d2 < 262144)
    (hOut : ∀ j : Fin 22, β (rOut22 j) = if dom22Bit (evenOctIdxT10K isNN d2) j then 1 else 0) :
    let p := evenOctIdxT10K isNN d2
    t11OfParts p < 2048 ∧
    (∀ b : Fin 11, (β (rOut22 (compOutIdx b.val)) == 1) = (t11OfParts p).testBit b.val) ∧
    (∀ i : Fin 7, β (rIdx7Of22 rOut22 i) = if (idx7OfParts p).testBit i.val then 1 else 0) ∧
    (∀ i : Fin 4, β (rK4Of22 rOut22 i) = if p.2.2.testBit i.val then 1 else 0) := by
  have ⟨hb, hbnd⟩ : _ ∧ _ := ⟨evenOctIdxT10K_bounds isNN hd2, parts_popBern_bounds isNN hd2⟩
  dsimp only at hb hbnd ⊢
  set p := evenOctIdxT10K isNN d2
  have hB (c : Bool) : ((if c then (1 : ZMod 2) else 0) == 1) = c := by cases c <;> rfl
  refine ⟨hbnd.2.1, fun b ↦ ?_,
    fun i ↦ (hOut ⟨1 + i.val, by omega⟩).trans (congrArg (if · = true then (1 : ZMod 2) else 0) ?_),
    fun i ↦
        (hOut ⟨18 + i.val, by omega⟩).trans (congrArg (if · = true then (1 : ZMod 2) else 0) ?_)⟩
  · by_cases hb10 : b.val < 10
    · rw [compOutIdx, ditePos hb10, hOut ⟨8 + b.val, by omega⟩, hB]
      dsimp only [dom22Bit, t11OfParts]
      rw [iteNeg (by omega), itePos (by omega), show 8 + b.val - 8 = b.val by omega,
        Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq]
      exact congrArg (decide <| · = 1) (by fin_cases b <;> dsimp only at hb10 ⊢ <;> omega)
    · rw [show b.val = 10 by omega, show compOutIdx 10 = ⟨0, by decide⟩ from rfl,
          hOut ⟨0, by decide⟩, hB]
      dsimp only [dom22Bit, t11OfParts]
      rw [itePos (by decide), Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq]
      exact congrArg (decide <| · = 1) (by omega)
  · dsimp only [dom22Bit, idx7OfParts]
    rw [itePos (by omega), Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq,
      Nat.div_div_eq_div_mul, show 2 * 2 ^ i.val = 2 ^ (1 + i.val) by rw [Nat.pow_add, Nat.pow_one]]
  · dsimp only [dom22Bit]
    rw [iteNeg (by omega), iteNeg (by omega), show 18 + i.val - 18 = i.val by omega]

def mask30 (x32 : ℕ) : ℕ := (x32 >>> 2) <<< 2

theorem mask30_testBit (x32 i : ℕ) : (mask30 x32).testBit i = (decide (2 ≤ i) && x32.testBit i)
    := by
  rw [mask30, Nat.testBit_shiftLeft, Nat.testBit_shiftRight]
  exact if h2 : 2 ≤ i then by simp [h2, show 2 + (i - 2) = i by omega] else by simp [h2]

theorem mask30_shl4_word512DualLeg (idx : ℕ) : (mask30 (word512DualLeg idx >>> 4)) <<< 4 =
    word512DualLegLo6 idx := by
  simp only [mask30, word512DualLegLo6, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  omega

theorem natOfZModBits36_div8_eq_shr3 (f : Fin 36 → ZMod 2) (y : ℕ) (hy : y < 2 ^ 36)
    (hHi : ∀ b : Fin 36, 3 ≤ b.val → f b = if y.testBit b.val then 1 else 0) :
    natOfZModBits 36 f / 8 = y / 8 := by
  have := natOfZModBits_lt 3 fun i : Fin 3 ↦ f ⟨i.val, by omega⟩
  rw [PhotochemistrySolution.OddDivEval.natOfZModBits_split 3 33 f,
    show (fun j : Fin 33 ↦ f ⟨3 + j.val, by omega⟩) = fun j : Fin 33 ↦
        if (y >>> 3).testBit j.val then 1 else 0 from
      funext fun j ↦
          (hHi ⟨3 + j.val, by omega⟩
          (Nat.le_add_right 3 j.val)).trans (by rw [Nat.testBit_shiftRight]),
    natOfZModBits_ite_testBit_local 33 (y >>> 3)
        ((Nat.shiftRight_eq_div_pow y 3).trans_lt (Nat.div_lt_of_lt_mul (by omega))),
    Nat.shiftRight_eq_div_pow y 3]
  change (natOfZModBits 3 (fun i : Fin 3 ↦ f ⟨i.val, by omega⟩) + 8 * (y / 8)) / 8 = y / 8
  omega
end QuantumComputation.Specs.PhotochemistrySolution.CtrlSafeOracleBase.CoulBase
end

end
