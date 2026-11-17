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

public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.RankReducedPrepMidData
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
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.AliasComparator
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.MidReflCtxRetain
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.DyadicPacketInnerPrep
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.FreeAltInnerPrepMid
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.XMeasUnload21
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.Mobius126OneHot
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.ZeroRcHotPrepMid21Fast

@[expose] public section

/-!
# `162`-Toffoli Symplectic QROM & L-Triple Unloaders (`SympAnfQrom21`)

Combined `wInner2 = 21` inner Walker-alias QROM module:
1. `Tuned162ScheduledSympQrom21`: zero-`L1`-loss (`ε_in = 0`) `126 × 30` inner Walker-alias data,
   `162`-step shared-Toffoli symplectic loader (`744 T`, `0 TOFF`, `27 ≤ sScr`), and `96 T`
   (`0 TOFF`, `8 ≤ sScr`) `24`-monomial X-measurement unloader.
2. `Tuned162StepSympAnfQrom21` (also exported under `OptStepSympAnfQrom21`): `12`-AND (`48 T`,
   `0 TOFF`, `0 ≤ sScr`) hot `(3, 2)` L-triple QROM unloader for turnaround, `73`-AND (`292 T`,
   `0 TOFF`, `25 ≤ sScr`) cold `(5, 4, 3)` L-triple QROM unloader for terminal unload, and
   `oneHotPred`
   `wp` congruence bridges for `withMobiusOneHotDyn` and `withMobiusOneHot126Dyn`
   (Babbush et al., *Phys. Rev. X* **8**, 041015, 2018; Gidney, *Quantum* **2**, 74, 2018;
   Berry et al., *Quantum* **3**, 208, 2019; Jones, *Phys. Rev. A* **87**, 022328, 2013;
   Low et al., *Quantum* **8**, 1375, 2024).
-/

namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.Tuned162ScheduledSympQrom21
open QuantumComputation.Specs QuantumComputation.Specs.P450

section DataSection

open QuantumComputation.Specs QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution
open QuantumComputation.Specs.P450
open BlockEncodingCore

/-- Prefix XOR parity over the first `n ≤ 15` even indices `2 * t < 30` of `col`. -/
def evenColParityPrefix (col : Fin 30 → Bool) : (n : ℕ) → n ≤ 15 → Bool
  | 0, _ => false
  | n + 1, hn => xor (evenColParityPrefix col n (by omega)) (col ⟨2 * n, by omega⟩)

/-- Prefix XOR parity over the first `n ≤ 15` odd indices `2 * t + 1 < 30` of `col`. -/
def oddColParityPrefix (col : Fin 30 → Bool) : (n : ℕ) → n ≤ 15 → Bool
  | 0, _ => false
  | n + 1, hn => xor (oddColParityPrefix col n (by omega)) (col ⟨2 * n + 1, by omega⟩)

/-- XOR parity over all `15` even indices `y < 30` (`y = 0, 2, …, 28`) of `col`. -/
def evenColParity30 (col : Fin 30 → Bool) : Bool := evenColParityPrefix col 15 le_rfl

/-- XOR parity over all `15` odd indices `y < 30` (`y = 1, 3, …, 29`) of `col`. -/
def oddColParity30 (col : Fin 30 → Bool) : Bool := oddColParityPrefix col 15 le_rfl

/-- Unique `32`-point extension of `col : Fin 30 → Bool` whose `5`-bit ANF coefficients at masks
`30` (`11110₂`) and `31` (`11111₂`) both vanish (`x = 30` is even-index parity, `x = 31` is
odd-index parity). -/
def extCol24Bool (col : Fin 30 → Bool) (x : Fin (2 ^ 5)) : Bool :=
  if hx : x.val < 30 then col ⟨x.val, hx⟩
  else if x.val = 30 then evenColParity30 col
  else oddColParity30 col

/-- `ZMod 2` column lookup induced by `extCol24Bool col` on `Fin (2 ^ 5)`. -/
def col24ZMod5 (col : Fin 30 → Bool) (x : Fin (2 ^ 5)) : ZMod 2 :=
  if extCol24Bool col x then 1 else 0

/-- `5`-bit ANF coefficients of `col24ZMod5 col` (vanishing at masks `30` and `31`). -/
def col24Anf5 (col : Fin 30 → Bool) : Fin (2 ^ 5) → ZMod 2 :=
  SelectSwapQROM.anfCoeffs 5 (col24ZMod5 col)

theorem extCol24Bool_of_lt (col : Fin 30 → Bool) {x : Fin (2 ^ 5)} (hx : x.val < 30) :
    extCol24Bool col x = col ⟨x.val, hx⟩ := dite_eq_left hx

theorem extCol24Bool_30 (col : Fin 30 → Bool) :
    extCol24Bool col ⟨30, by decide⟩ = evenColParity30 col := rfl

theorem extCol24Bool_31 (col : Fin 30 → Bool) :
    extCol24Bool col ⟨31, by decide⟩ = oddColParity30 col := rfl

private theorem bool_xor_zmod2_data (a b : Bool) :
    (if xor a b then (1 : ZMod 2) else 0) = (if a then 1 else 0) + (if b then 1 else 0) := by
  cases a <;> cases b <;> decide

theorem anfCoeffs_zero_local :
    ∀ (s : ℕ) (m : Fin (2 ^ s)), SelectSwapQROM.anfCoeffs s 0 m = 0
  | 0, _ => rfl
  | s + 1, m => by
      dsimp only [SelectSwapQROM.anfCoeffs]
      have h1 : (fun u : Fin (2 ^ s) ↦ (0 : ZMod 2) + 0) = 0 := funext fun _ ↦ add_zero 0
      split_ifs with hm
      · exact anfCoeffs_zero_local s ⟨m.val, hm⟩
      · rw [show (fun u : Fin (2 ^ s) ↦ (0 : Fin (2 ^ (s + 1)) → ZMod 2) _ +
            (0 : Fin (2 ^ (s + 1)) → ZMod 2) _) = 0 from h1]
        exact anfCoeffs_zero_local s _

theorem anfCoeffs_add_local :
    ∀ (s : ℕ) (f g : Fin (2 ^ s) → ZMod 2) (m : Fin (2 ^ s)),
      SelectSwapQROM.anfCoeffs s (f + g) m =
        SelectSwapQROM.anfCoeffs s f m + SelectSwapQROM.anfCoeffs s g m
  | 0, _, _, _ => rfl
  | s + 1, f, g, m => by
      dsimp only [SelectSwapQROM.anfCoeffs]
      split_ifs with hm
      · exact anfCoeffs_add_local s _ _ ⟨m.val, hm⟩
      · have hfg : (fun u : Fin (2 ^ s) ↦
            (f + g) ⟨u.val, by have := u.isLt; rw [pow_succ']; omega⟩ +
              (f + g) ⟨2 ^ s + u.val, by have := u.isLt; rw [pow_succ']; omega⟩) =
            (fun u : Fin (2 ^ s) ↦
              f ⟨u.val, by have := u.isLt; rw [pow_succ']; omega⟩ +
                f ⟨2 ^ s + u.val, by have := u.isLt; rw [pow_succ']; omega⟩) +
            (fun u : Fin (2 ^ s) ↦
              g ⟨u.val, by have := u.isLt; rw [pow_succ']; omega⟩ +
                g ⟨2 ^ s + u.val, by have := u.isLt; rw [pow_succ']; omega⟩) :=
          funext fun u ↦ by dsimp only [Pi.add_apply]; ring
        rw [hfg]
        exact anfCoeffs_add_local s _ _ _

private theorem evenColParityPrefix_zmod2 (col : Fin 30 → Bool) :
    ∀ (n : ℕ) (hn : n ≤ 15),
      (if evenColParityPrefix col n hn then (1 : ZMod 2) else 0) =
        ∑ t : Fin n, col24ZMod5 col ⟨2 * t.val, by omega⟩
  | 0, _ => rfl
  | n + 1, hn => by
      rw [evenColParityPrefix, bool_xor_zmod2_data, evenColParityPrefix_zmod2 col n (by omega),
        Fin.sum_univ_castSucc]
      have hlt : 2 * n < 30 := by omega
      have hcol : (if col ⟨2 * n, hlt⟩ then (1 : ZMod 2) else 0) =
          col24ZMod5 col ⟨2 * n, by omega⟩ := by
        simp [col24ZMod5, extCol24Bool, hlt]
      rw [hcol]; rfl

private theorem oddColParityPrefix_zmod2 (col : Fin 30 → Bool) :
    ∀ (n : ℕ) (hn : n ≤ 15),
      (if oddColParityPrefix col n hn then (1 : ZMod 2) else 0) =
        ∑ t : Fin n, col24ZMod5 col ⟨2 * t.val + 1, by omega⟩
  | 0, _ => rfl
  | n + 1, hn => by
      rw [oddColParityPrefix, bool_xor_zmod2_data, oddColParityPrefix_zmod2 col n (by omega),
        Fin.sum_univ_castSucc]
      have hlt : 2 * n + 1 < 30 := by omega
      have hcol : (if col ⟨2 * n + 1, hlt⟩ then (1 : ZMod 2) else 0) =
          col24ZMod5 col ⟨2 * n + 1, by omega⟩ := by
        simp [col24ZMod5, extCol24Bool, hlt]
      rw [hcol]; rfl

theorem col24Anf5_30 (col : Fin 30 → Bool) : col24Anf5 col ⟨30, by decide⟩ = 0 := by
  let g := col24ZMod5 col
  let ev := g ⟨0, by decide⟩ + g ⟨2, by decide⟩ + g ⟨4, by decide⟩ + g ⟨6, by decide⟩ +
      g ⟨8, by decide⟩ + g ⟨10, by decide⟩ + g ⟨12, by decide⟩ + g ⟨14, by decide⟩ +
      g ⟨16, by decide⟩ + g ⟨18, by decide⟩ + g ⟨20, by decide⟩ + g ⟨22, by decide⟩ +
      g ⟨24, by decide⟩ + g ⟨26, by decide⟩ + g ⟨28, by decide⟩
  have hAnf : SelectSwapQROM.anfCoeffs 5 g ⟨30, by decide⟩ = ev + g ⟨30, by decide⟩ := by
    dsimp [SelectSwapQROM.anfCoeffs, ev]; ring
  have hSum : (∑ t : Fin 15, g ⟨2 * t.val, by omega⟩) = ev := by
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero, Fin.val_succ,
      Nat.reduceAdd, Nat.reduceMul, ev]
    ring
  have hg30 : g ⟨30, by decide⟩ = ev :=
    (evenColParityPrefix_zmod2 col 15 le_rfl).trans hSum
  change SelectSwapQROM.anfCoeffs 5 g ⟨30, by decide⟩ = 0
  rw [hAnf, hg30]
  exact CharTwo.add_self_eq_zero _

theorem col24Anf5_31 (col : Fin 30 → Bool) : col24Anf5 col ⟨31, by decide⟩ = 0 := by
  let g := col24ZMod5 col
  let ev := g ⟨0, by decide⟩ + g ⟨2, by decide⟩ + g ⟨4, by decide⟩ + g ⟨6, by decide⟩ +
      g ⟨8, by decide⟩ + g ⟨10, by decide⟩ + g ⟨12, by decide⟩ + g ⟨14, by decide⟩ +
      g ⟨16, by decide⟩ + g ⟨18, by decide⟩ + g ⟨20, by decide⟩ + g ⟨22, by decide⟩ +
      g ⟨24, by decide⟩ + g ⟨26, by decide⟩ + g ⟨28, by decide⟩
  let od := g ⟨1, by decide⟩ + g ⟨3, by decide⟩ + g ⟨5, by decide⟩ + g ⟨7, by decide⟩ +
      g ⟨9, by decide⟩ + g ⟨11, by decide⟩ + g ⟨13, by decide⟩ + g ⟨15, by decide⟩ +
      g ⟨17, by decide⟩ + g ⟨19, by decide⟩ + g ⟨21, by decide⟩ + g ⟨23, by decide⟩ +
      g ⟨25, by decide⟩ + g ⟨27, by decide⟩ + g ⟨29, by decide⟩
  have hAnf : SelectSwapQROM.anfCoeffs 5 g ⟨31, by decide⟩ =
      (ev + od) + (g ⟨30, by decide⟩ + g ⟨31, by decide⟩) := by
    dsimp [SelectSwapQROM.anfCoeffs, ev, od]; ring
  have hSumEv : (∑ t : Fin 15, g ⟨2 * t.val, by omega⟩) = ev := by
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero, Fin.val_succ,
      Nat.reduceAdd, Nat.reduceMul, ev]
    ring
  have hSumOd : (∑ t : Fin 15, g ⟨2 * t.val + 1, by omega⟩) = od := by
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero, Fin.val_succ,
      Nat.reduceAdd, Nat.reduceMul, od]
    ring
  have hg30 : g ⟨30, by decide⟩ = ev :=
    (evenColParityPrefix_zmod2 col 15 le_rfl).trans hSumEv
  have hg31 : g ⟨31, by decide⟩ = od :=
    (oddColParityPrefix_zmod2 col 15 le_rfl).trans hSumOd
  change SelectSwapQROM.anfCoeffs 5 g ⟨31, by decide⟩ = 0
  rw [hAnf, hg30, hg31]
  exact CharTwo.add_self_eq_zero _

end DataSection

section CoreSection

open Operator QProg Matrix Real QuantumComputation.Specs
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution
open QuantumComputation.Specs.P450 QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution
open CoherentAlias QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.CleanDyn AliasPrep
open CompactBilinearPrep
open RankReducedPrepMid
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.BlockEncodingCore
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.BlockEncodingCircuit
open scoped Matrix BigOperators

local instance (priority := 1000000) instNeZeroTwoPowSharedCore (k : ℕ) : NeZero (2 ^ k) :=
  ⟨Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos k)⟩

/-! ## Section 1: `24`-Scratch `29`-Monomial Register & `96 T` Temporary-AND Sandwich -/

/-! ## Section 2: `173`-Wire Shared-Toffoli Symplectic `GF(2)` Core (`162 TOFF` = `648 T`) -/

attribute [local irreducible] col24Anf5


end CoreSection

section MainSection

open Operator QProg Matrix Circuit Real QuantumComputation.Specs
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution
open QuantumComputation.Specs.P450 QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution
open CoherentAlias QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.CleanDyn AliasPrep
open CompactBilinearPrep
open MidReflCtxRetain RankReducedPrepMid
open DyadicPacketInnerPrep
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.BlockEncodingCore
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.BlockEncodingCircuit
open scoped Matrix BigOperators Matrix.Norms.L2Operator

local instance (priority := 1000000) instNeZeroTwoPowSharedMain (k : ℕ) : NeZero (2 ^ k) :=
  ⟨Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos k)⟩

attribute [irreducible] col24Anf5


/-! ## Section 3: `96 T`, `8 ≤ sScr` X-Measurement QROM Unload (`24` `b`-Monomials) -/

/-- Linearity of `SelectSwapQROM.anfCoeffs` through `MidReflCtxRetain.parityLinComb`: if every
bitplane `k` has vanishing ANF coefficient at `mask`, then `parityLinComb` does as well. -/
theorem anfCoeffs_parityLinComb_vanish (s : ℕ) (mask : Fin (2 ^ s)) :
    ∀ (outBits : ℕ) (m : Fin (2 ^ outBits)) (w : Fin (2 ^ s) → Fin outBits → ZMod 2),
      (∀ k : Fin outBits, SelectSwapQROM.anfCoeffs s (fun x ↦ w x k) mask = 0) →
      SelectSwapQROM.anfCoeffs s
        (fun x ↦ MidReflCtxRetain.parityLinComb outBits m (w x)) mask = 0
  | 0, _, _, _ => anfCoeffs_zero_local s mask
  | b + 1, m, w, hw => by
      dsimp only [MidReflCtxRetain.parityLinComb]
      split_ifs with hm
      · exact anfCoeffs_parityLinComb_vanish s mask b ⟨m.val, hm⟩
          (fun x j ↦ w x (Fin.castLE (Nat.le_succ b) j))
          (fun j ↦ hw (Fin.castLE (Nat.le_succ b) j))
      · have hlt : m.val - 2 ^ b < 2 ^ b := by have := m.isLt; omega
        have hfn : (fun x ↦
            w x ⟨b, Nat.lt_succ_self b⟩ +
              MidReflCtxRetain.parityLinComb b ⟨m.val - 2 ^ b, hlt⟩
                (fun j ↦ w x (Fin.castLE (Nat.le_succ b) j))) =
            (fun x ↦ w x ⟨b, Nat.lt_succ_self b⟩) +
            (fun x ↦ MidReflCtxRetain.parityLinComb b ⟨m.val - 2 ^ b, hlt⟩
              (fun j ↦ w x (Fin.castLE (Nat.le_succ b) j))) := rfl
        rw [hfn, anfCoeffs_add_local, hw ⟨b, Nat.lt_succ_self b⟩,
          anfCoeffs_parityLinComb_vanish s mask b ⟨m.val - 2 ^ b, hlt⟩
            (fun x j ↦ w x (Fin.castLE (Nat.le_succ b) j))
            (fun j ↦ hw (Fin.castLE (Nat.le_succ b) j)),
          add_zero]

theorem anfCoeffs_sliceParityFn_of_vanish {L_ctx outBits : ℕ}
    (F : Fin L_ctx → Fin (2 ^ 5) → Fin outBits → Bool)
    (m : Fin (2 ^ outBits)) (c : Fin L_ctx) (mask : Fin (2 ^ 5))
    (hVan : ∀ k : Fin outBits,
      SelectSwapQROM.anfCoeffs 5 (fun x ↦ if F c x k then (1 : ZMod 2) else 0) mask = 0) :
    SelectSwapQROM.anfCoeffs 5
      (MidReflCtxRetain.sliceParityFn 5 L_ctx outBits F m c) mask = 0 :=
  anfCoeffs_parityLinComb_vanish 5 mask outBits m (fun x k ↦ if F c x k then 1 else 0) hVan

end MainSection

end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.Tuned162ScheduledSympQrom21

namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.Tuned162StepSympAnfQrom21
open QuantumComputation.Specs QuantumComputation.Specs.P450

open Operator QProg Matrix Circuit HermitianMat QuantumComputation.Specs
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution
open QuantumComputation.Specs.P450 QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution
open CoherentAlias CleanDyn AliasPrep
open Phase2MidSandwich
open CompactBilinearPrep DyadicPacketInnerPrep
open RankReducedPrepMid MidReflCtxRetain
open OptFactoredMag30AndCoin9
open FreeAltInnerPrepMid Tuned162ScheduledSympQrom21 ZeroRcHotPrepMid21Fast OptXMeasUnload21
open Mobius126OneHot
open BlockEncodingCore BlockEncodingCircuit
open scoped Matrix BigOperators

local instance (priority := 1000000) instNeZeroTwoPowStep (k : ℕ) : NeZero (2 ^ k) :=
  ⟨Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos k)⟩

/-! ## Section 1: `extCol24Bool` & `effRc126` Table Identities -/

private theorem evenColParityPrefix_eq_xorFin (col : Fin 30 → Bool) :
    ∀ (n : ℕ) (hn : n ≤ 15),
      evenColParityPrefix col n hn =
        OptXMeasUnload21.xorFin n (fun j ↦ col ⟨2 * j.val, by omega⟩)
  | 0, _ => rfl
  | n + 1, hn => by
      dsimp only [evenColParityPrefix, OptXMeasUnload21.xorFin]
      rw [evenColParityPrefix_eq_xorFin col n (by omega)]
      rfl

private theorem oddColParityPrefix_eq_xorFin (col : Fin 30 → Bool) :
    ∀ (n : ℕ) (hn : n ≤ 15),
      oddColParityPrefix col n hn =
        OptXMeasUnload21.xorFin n (fun j ↦ col ⟨2 * j.val + 1, by omega⟩)
  | 0, _ => rfl
  | n + 1, hn => by
      dsimp only [oddColParityPrefix, OptXMeasUnload21.xorFin]
      rw [oddColParityPrefix_eq_xorFin col n (by omega)]
      rfl

/-- `4,096`-entry Boolean table extending every row `rc : Fin 128` (`0..127`) from `Fin 30` to
`Fin 32` via `extCol24Bool` (`b = 30` even parity, `b = 31` odd parity). -/
def ext24InnerBoolTable (rows128 : Fin 128 → Fin 30 → Fin 16 → Bool) (idx : ℕ) (k : Fin 16) :
    Bool :=
  if h : idx / 32 < 128 then
    extCol24Bool (fun y ↦ rows128 ⟨idx / 32, h⟩ y k) ⟨idx % 32, Nat.mod_lt _ (by decide)⟩
  else
    false

private theorem sum_zmod2_add_xorFin_w3 :
    ∀ (n : ℕ) (f : Fin n → Bool),
      (∑ j : Fin n, if f j then (1 : ZMod 2) else 0) +
        (if OptXMeasUnload21.xorFin n f then 1 else 0) = 0
  | 0, _ => by simp [OptXMeasUnload21.xorFin]
  | n + 1, f => by
      rw [Fin.sum_univ_castSucc, OptXMeasUnload21.xorFin]
      have hxor : (if xor (OptXMeasUnload21.xorFin n fun i ↦ f (Fin.castSucc i))
            (f (Fin.last n)) then (1 : ZMod 2) else 0) =
          (if OptXMeasUnload21.xorFin n fun i ↦ f (Fin.castSucc i) then 1 else 0) +
            (if f (Fin.last n) then 1 else 0) := by
        cases OptXMeasUnload21.xorFin n fun i ↦ f (Fin.castSucc i) <;>
          cases f (Fin.last n) <;> decide
      rw [hxor]
      have ih := sum_zmod2_add_xorFin_w3 n (fun i ↦ f (Fin.castSucc i))
      calc ((∑ i : Fin n, if f (Fin.castSucc i) then (1 : ZMod 2) else 0) +
              if f (Fin.last n) then 1 else 0) +
            ((if OptXMeasUnload21.xorFin n fun i ↦ f (Fin.castSucc i) then 1 else 0) +
              if f (Fin.last n) then 1 else 0)
          = ((∑ i : Fin n, if f (Fin.castSucc i) then (1 : ZMod 2) else 0) +
              (if OptXMeasUnload21.xorFin n fun i ↦ f (Fin.castSucc i) then 1 else 0)) +
            ((if f (Fin.last n) then (1 : ZMod 2) else 0) +
              (if f (Fin.last n) then 1 else 0)) := by ring
        _ = 0 := by rw [ih, CharTwo.add_self_eq_zero, add_zero]

theorem ext24InnerBoolTable_sum_even_odd (rows128 : Fin 128 → Fin 30 → Fin 16 → Bool)
    (rc : Fin 128) (b₀ : Fin 2) (k : Fin 16) :
    (∑ v : Fin 16,
      if ext24InnerBoolTable rows128 (32 * rc.val + 2 * v.val + b₀.val) k
        then (1 : ZMod 2) else 0) = 0 := by
  rw [Fin.sum_univ_castSucc]
  have hCell (v : Fin 16) :
      ext24InnerBoolTable rows128 (32 * rc.val + 2 * v.val + b₀.val) k =
        extCol24Bool (fun y ↦ rows128 rc y k)
          ⟨2 * v.val + b₀.val, by have := v.isLt; have := b₀.isLt; omega⟩ := by
    have hv := v.isLt; have hb := b₀.isLt; have hrc := rc.isLt
    have hdiv : (32 * rc.val + 2 * v.val + b₀.val) / 32 = rc.val := by omega
    have hmod : (32 * rc.val + 2 * v.val + b₀.val) % 32 = 2 * v.val + b₀.val := by omega
    have h128 : (32 * rc.val + 2 * v.val + b₀.val) / 32 < 128 := by omega
    dsimp only [ext24InnerBoolTable]
    rw [dite_eq_left h128]
    have hrcEq : (⟨(32 * rc.val + 2 * v.val + b₀.val) / 32, h128⟩ : Fin 128) = rc := Fin.ext hdiv
    rw [hrcEq]
    exact congrArg (extCol24Bool _) (Fin.ext hmod)
  simp_rw [hCell]
  fin_cases b₀
  · have hLo : (∑ j : Fin 15,
        if extCol24Bool (fun y ↦ rows128 rc y k) ⟨2 * (Fin.castSucc j).val + 0, by omega⟩
          then (1 : ZMod 2) else 0) =
        ∑ j : Fin 15, if rows128 rc ⟨2 * j.val, by omega⟩ k then 1 else 0 :=
      Finset.sum_congr rfl fun j _ ↦ by
        rw [extCol24Bool_of_lt _ (by dsimp; have := j.isLt; omega)]; rfl
    have hHi : extCol24Bool (fun y ↦ rows128 rc y k) ⟨2 * (Fin.last 15).val + 0, by decide⟩ =
        OptXMeasUnload21.xorFin 15 (fun j ↦ rows128 rc ⟨2 * j.val, by omega⟩ k) := by
      change extCol24Bool _ ⟨30, by decide⟩ = _
      rw [extCol24Bool_30]; dsimp only [evenColParity30]
      exact evenColParityPrefix_eq_xorFin _ 15 le_rfl
    rw [hLo, hHi]
    exact sum_zmod2_add_xorFin_w3 15 _
  · have hLo : (∑ j : Fin 15,
        if extCol24Bool (fun y ↦ rows128 rc y k) ⟨2 * (Fin.castSucc j).val + 1, by omega⟩
          then (1 : ZMod 2) else 0) =
        ∑ j : Fin 15, if rows128 rc ⟨2 * j.val + 1, by omega⟩ k then 1 else 0 :=
      Finset.sum_congr rfl fun j _ ↦ by
        rw [extCol24Bool_of_lt _ (by dsimp; have := j.isLt; omega)]; rfl
    have hHi : extCol24Bool (fun y ↦ rows128 rc y k) ⟨2 * (Fin.last 15).val + 1, by decide⟩ =
        OptXMeasUnload21.xorFin 15 (fun j ↦ rows128 rc ⟨2 * j.val + 1, by omega⟩ k) := by
      change extCol24Bool _ ⟨31, by decide⟩ = _
      rw [extCol24Bool_31]; dsimp only [oddColParity30]
      exact oddColParityPrefix_eq_xorFin _ 15 le_rfl
    rw [hLo, hHi]
    exact sum_zmod2_add_xorFin_w3 15 _

/-! ## Section 2: Shared In-Place L-Step Primitive (`lStepInPlaceDyn`, `4 T`, `0 TOFF`) -/

/-- Global diagonal computational-basis phase unitary `|γ⟩ ↦ bitSign (φ γ) • |γ⟩`. -/
noncomputable def diagKetUnitary {N : ℕ} (φ : BitAssignment N → ZMod 2) : Unitary (2 ^ N) :=
  ⟨Matrix.diagonal (fun idx : Fin (2 ^ N) ↦ SelectSwapQROM.bitSign (φ (basisBits N idx))), by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
      Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases hij : i = j
    · subst hij
      rcases SelectSwapQROM.bit_cases (φ (basisBits N i)) with h | h <;>
        simp [SelectSwapQROM.bitSign, h]
    · simp [hij]⟩

theorem diagKetUnitary_mulVec_ket {N : ℕ} (φ : BitAssignment N → ZMod 2) (γ : BitAssignment N) :
    (diagKetUnitary φ).1.mulVec (SelectSwapQROM.ket γ) =
      SelectSwapQROM.bitSign (φ γ) • SelectSwapQROM.ket γ := by
  funext g
  rw [diagKetUnitary, Matrix.mulVec_diagonal]
  by_cases hg : g = (basisBits N).symm γ
  · subst hg
    simp [SelectSwapQROM.ket, basisState]
  · simp [SelectSwapQROM.ket, basisState, Pi.single_eq_of_ne hg]

theorem diagKetUnitary_mul {N : ℕ} (φ₁ φ₂ : BitAssignment N → ZMod 2) :
    diagKetUnitary φ₁ * diagKetUnitary φ₂ = diagKetUnitary (fun γ ↦ φ₁ γ + φ₂ γ) := by
  apply Subtype.ext
  refine SelectSwapQROM.matrix_ext_ket fun γ ↦ ?_
  simp only [Submonoid.coe_mul, ← Matrix.mulVec_mulVec, diagKetUnitary_mulVec_ket,
    Matrix.mulVec_smul, smul_smul, ← SelectSwapQROM.bitSign_add, add_comm]

theorem diagKetUnitary_zero {N : ℕ} : diagKetUnitary (fun _ : BitAssignment N ↦ 0) = 1 := by
  apply Subtype.ext
  refine SelectSwapQROM.matrix_ext_ket fun γ ↦ ?_
  rw [diagKetUnitary_mulVec_ket, Submonoid.coe_one, Matrix.one_mulVec]
  simp [SelectSwapQROM.bitSign]

/-- Prefix CNOT fan-in XORing `∑_{u < k} mask u * γ (rSrc u)` onto `wTgt` (`0 T`, `0 TOFF`). -/
def cnotMaskLoop {N M : ℕ} (wTgt : Wire N) (rSrc : QRegister M N)
    (hNe : ∀ u : Fin M, rSrc u ≠ wTgt) (mask : Fin M → ZMod 2) : (k : ℕ) → k ≤ M → Circuit N
  | 0, _ => .identity
  | k + 1, hk =>
      let u : Fin M := ⟨k, hk⟩
      .seq (cnotMaskLoop wTgt rSrc hNe mask k (Nat.le_of_lt hk))
        (if mask u = 1 then Circuit.CNOT (rSrc u) wTgt (hNe u) else .identity)

/-- Full `M`-wire CNOT fan-in onto `wTgt` (`0 T`, `0 TOFF`). -/
def cnotMaskW3Circuit {N M : ℕ} (wTgt : Wire N) (rSrc : QRegister M N)
    (hNe : ∀ u : Fin M, rSrc u ≠ wTgt) (mask : Fin M → ZMod 2) : Circuit N :=
  cnotMaskLoop wTgt rSrc hNe mask M le_rfl

private theorem count_cnotMaskLoop_toff {N M : ℕ} (wTgt : Wire N) (rSrc : QRegister M N)
    (hNe : ∀ u : Fin M, rSrc u ≠ wTgt) (mask : Fin M → ZMod 2) :
    ∀ (k : ℕ) (hk : k ≤ M), (cnotMaskLoop wTgt rSrc hNe mask k hk).count .TOFF = 0
  | 0, _ => rfl
  | k + 1, hk => by
      simp only [cnotMaskLoop, Circuit.count_seq]
      rw [count_cnotMaskLoop_toff wTgt rSrc hNe mask k (Nat.le_of_lt hk), zero_add]
      split_ifs <;> simp [Circuit.CNOT]

private theorem count_cnotMaskLoop_t {N M : ℕ} (wTgt : Wire N) (rSrc : QRegister M N)
    (hNe : ∀ u : Fin M, rSrc u ≠ wTgt) (mask : Fin M → ZMod 2) :
    ∀ (k : ℕ) (hk : k ≤ M), (cnotMaskLoop wTgt rSrc hNe mask k hk).count .T = 0
  | 0, _ => rfl
  | k + 1, hk => by
      simp only [cnotMaskLoop, Circuit.count_seq]
      rw [count_cnotMaskLoop_t wTgt rSrc hNe mask k (Nat.le_of_lt hk), zero_add]
      split_ifs <;> simp [Circuit.CNOT]

@[simp]
theorem count_cnotMaskW3Circuit_toff {N M : ℕ} (wTgt : Wire N) (rSrc : QRegister M N)
    (hNe : ∀ u : Fin M, rSrc u ≠ wTgt) (mask : Fin M → ZMod 2) :
    (cnotMaskW3Circuit wTgt rSrc hNe mask).count .TOFF = 0 :=
  count_cnotMaskLoop_toff wTgt rSrc hNe mask M le_rfl

@[simp]
theorem count_cnotMaskW3Circuit_t {N M : ℕ} (wTgt : Wire N) (rSrc : QRegister M N)
    (hNe : ∀ u : Fin M, rSrc u ≠ wTgt) (mask : Fin M → ZMod 2) :
    (cnotMaskW3Circuit wTgt rSrc hNe mask).count .T = 0 :=
  count_cnotMaskLoop_t wTgt rSrc hNe mask M le_rfl

private theorem ket_cnotMaskLoop {N M : ℕ} (wTgt : Wire N) (rSrc : QRegister M N)
    (hNe : ∀ u : Fin M, rSrc u ≠ wTgt) (mask : Fin M → ZMod 2) :
    ∀ (k : ℕ) (hk : k ≤ M) (γ : BitAssignment N),
      (cnotMaskLoop wTgt rSrc hNe mask k hk).eval.1.mulVec (SelectSwapQROM.ket γ) =
        SelectSwapQROM.ket (Function.update γ wTgt
          (γ wTgt + ∑ j : Fin k, mask ⟨j.val, Nat.lt_of_lt_of_le j.isLt hk⟩ *
            γ (rSrc ⟨j.val, Nat.lt_of_lt_of_le j.isLt hk⟩)))
  | 0, _, γ => by rw [cnotMaskLoop, SelectSwapQROM.ket_identity]; simp
  | k + 1, hk, γ => by
      dsimp only [cnotMaskLoop]
      rw [SelectSwapQROM.eval_seq_mulVec, ket_cnotMaskLoop wTgt rSrc hNe mask k (Nat.le_of_lt hk)]
      let u : Fin M := ⟨k, hk⟩
      set s := ∑ j : Fin k, mask ⟨j.val, Nat.lt_of_lt_of_le j.isLt (Nat.le_of_lt hk)⟩ *
        γ (rSrc ⟨j.val, Nat.lt_of_lt_of_le j.isLt (Nat.le_of_lt hk)⟩)
      have hSum : (∑ j : Fin (k + 1), mask ⟨j.val, Nat.lt_of_lt_of_le j.isLt hk⟩ *
          γ (rSrc ⟨j.val, Nat.lt_of_lt_of_le j.isLt hk⟩)) = s + mask u * γ (rSrc u) := by
        rw [Fin.sum_univ_castSucc]; rfl
      rw [hSum]
      rcases SelectSwapQROM.bit_cases (mask u) with hm0 | hm1
      · rw [hm0, ite_eq_right (by decide : (0 : ZMod 2) ≠ 1), SelectSwapQROM.ket_identity]
        simp
      · rw [hm1, ite_eq_left rfl, one_mul, SelectSwapQROM.ket_CNOT, Function.update_self,
          Function.update_of_ne (hNe u), Function.update_idem, add_assoc]

theorem ket_cnotMaskW3Circuit {N M : ℕ} (wTgt : Wire N) (rSrc : QRegister M N)
    (hNe : ∀ u : Fin M, rSrc u ≠ wTgt) (mask : Fin M → ZMod 2) (γ : BitAssignment N) :
    (cnotMaskW3Circuit wTgt rSrc hNe mask).eval.1.mulVec (SelectSwapQROM.ket γ) =
      SelectSwapQROM.ket (Function.update γ wTgt (γ wTgt + ∑ u : Fin M, mask u * γ (rSrc u))) :=
  ket_cnotMaskLoop wTgt rSrc hNe mask M le_rfl γ

/-- Bit evaluation of an optional wire (`0` when `none`). -/
def optWireBit {N : ℕ} (γ : BitAssignment N) : Option (Wire N) → ZMod 2
  | none => 0
  | some w => γ w

/-- Optional `CZ` gate controlled on `wAnc` (`0 T`, `0 TOFF`). -/
def optCzW3Circuit {N : ℕ} (wAnc : Wire N) :
    (wOpt : Option (Wire N)) → (∀ w, wOpt = some w → wAnc ≠ w) → Circuit N
  | none, _ => .identity
  | some w, hNe =>
      SelectSwapQROM.czMaskCircuit wAnc 1 (QRegister.singleton w)
        (fun j ↦ by rw [QRegister.singleton_apply]; exact hNe w rfl) (fun _ ↦ 1)

@[simp]
theorem count_optCzW3Circuit_toff {N : ℕ} (wAnc : Wire N) (wOpt : Option (Wire N))
    (hNe : ∀ w, wOpt = some w → wAnc ≠ w) :
    (optCzW3Circuit wAnc wOpt hNe).count .TOFF = 0 := by
  cases wOpt with
  | none => rfl
  | some w => exact SelectSwapQROM.count_czMaskCircuit_toff _ _ _ _

@[simp]
theorem count_optCzW3Circuit_t {N : ℕ} (wAnc : Wire N) (wOpt : Option (Wire N))
    (hNe : ∀ w, wOpt = some w → wAnc ≠ w) :
    (optCzW3Circuit wAnc wOpt hNe).count .T = 0 := by
  cases wOpt with
  | none => rfl
  | some w => exact SelectSwapQROM.count_czMaskCircuit_t _ _ _ _

theorem ket_optCzW3Circuit {N : ℕ} (wAnc : Wire N) (wOpt : Option (Wire N))
    (hNe : ∀ w, wOpt = some w → wAnc ≠ w) (γ : BitAssignment N) :
    (optCzW3Circuit wAnc wOpt hNe).eval.1.mulVec (SelectSwapQROM.ket γ) =
      SelectSwapQROM.bitSign (γ wAnc * optWireBit γ wOpt) • SelectSwapQROM.ket γ := by
  cases wOpt with
  | none =>
      rw [optCzW3Circuit, optWireBit, mul_zero, SelectSwapQROM.ket_identity]
      simp [SelectSwapQROM.bitSign]
  | some w =>
      dsimp only [optCzW3Circuit, optWireBit]
      rw [SelectSwapQROM.ket_czMaskCircuit, Fin.sum_univ_one, one_mul, QRegister.singleton_apply]

/-- In-place L-triple phase step (`4 T`, `0 TOFF`, `1` clean ancilla wire `wAnc`): conjugates
`wB` and `wC` by `c1`/`c2` parities of `rSrc`, computes `wB ∧ wC` into `wAnc`, applies `CZ` onto
`c3 · rSrc + wBp + wCp`, uncomputes `wAnc` via X-measurement, and restores `wB, wC`. -/
def lStepInPlaceDyn {Var : Type} {N M : ℕ} (v : Var)
    (rSrc : QRegister M N) (wB wC wAnc : Wire N) (wBp wCp : Option (Wire N))
    (c1 c2 c3 : Fin M → ZMod 2)
    (hBC : wB ≠ wC) (hBAnc : wB ≠ wAnc) (hCAnc : wC ≠ wAnc)
    (hBSrc : ∀ u, rSrc u ≠ wB) (hCSrc : ∀ u, rSrc u ≠ wC) (hAncSrc : ∀ u, wAnc ≠ rSrc u)
    (hAncBp : ∀ w, wBp = some w → wAnc ≠ w) (hAncCp : ∀ w, wCp = some w → wAnc ≠ w) :
    DynamicCircuit Var N :=
  let pre := Circuit.seq (cnotMaskW3Circuit wB rSrc hBSrc c1) (cnotMaskW3Circuit wC rSrc hCSrc c2)
  let czCore := Circuit.seq (SelectSwapQROM.czMaskCircuit wAnc M rSrc hAncSrc c3)
    (Circuit.seq (optCzW3Circuit wAnc wBp hAncBp) (optCzW3Circuit wAnc wCp hAncCp))
  DynamicCircuit.seq (.circuit pre)
    (DynamicCircuit.seq (SelectSwapQROM.andSandwichDyn v wB wC wAnc hBC hBAnc hCAnc
      (.circuit czCore)) (.circuit pre))

@[simp]
theorem count_lStepInPlaceDyn_toff {Var : Type} {N M : ℕ} (v : Var)
    (rSrc : QRegister M N) (wB wC wAnc : Wire N) (wBp wCp : Option (Wire N))
    (c1 c2 c3 : Fin M → ZMod 2)
    (hBC : wB ≠ wC) (hBAnc : wB ≠ wAnc) (hCAnc : wC ≠ wAnc)
    (hBSrc : ∀ u, rSrc u ≠ wB) (hCSrc : ∀ u, rSrc u ≠ wC) (hAncSrc : ∀ u, wAnc ≠ rSrc u)
    (hAncBp : ∀ w, wBp = some w → wAnc ≠ w) (hAncCp : ∀ w, wCp = some w → wAnc ≠ w) :
    (lStepInPlaceDyn v rSrc wB wC wAnc wBp wCp c1 c2 c3 hBC hBAnc hCAnc
      hBSrc hCSrc hAncSrc hAncBp hAncCp).count .TOFF = 0 := by
  simp [lStepInPlaceDyn]

@[simp]
theorem count_lStepInPlaceDyn_t {Var : Type} {N M : ℕ} (v : Var)
    (rSrc : QRegister M N) (wB wC wAnc : Wire N) (wBp wCp : Option (Wire N))
    (c1 c2 c3 : Fin M → ZMod 2)
    (hBC : wB ≠ wC) (hBAnc : wB ≠ wAnc) (hCAnc : wC ≠ wAnc)
    (hBSrc : ∀ u, rSrc u ≠ wB) (hCSrc : ∀ u, rSrc u ≠ wC) (hAncSrc : ∀ u, wAnc ≠ rSrc u)
    (hAncBp : ∀ w, wBp = some w → wAnc ≠ w) (hAncCp : ∀ w, wCp = some w → wAnc ≠ w) :
    (lStepInPlaceDyn v rSrc wB wC wAnc wBp wCp c1 c2 c3 hBC hBAnc hCAnc
      hBSrc hCSrc hAncSrc hAncBp hAncCp).count .T = 4 := by
  simp [lStepInPlaceDyn]

/-- Phase polynomial contributed by a single in-place L-step. -/
def lStepPhase {N M : ℕ} (rSrc : QRegister M N) (wB wC : Wire N) (wBp wCp : Option (Wire N))
    (c1 c2 c3 : Fin M → ZMod 2) (γ : BitAssignment N) : ZMod 2 :=
  (γ wB + ∑ u : Fin M, c1 u * γ (rSrc u)) *
    (γ wC + ∑ u : Fin M, c2 u * γ (rSrc u)) *
    (∑ u : Fin M, c3 u * γ (rSrc u) + optWireBit γ wBp + optWireBit γ wCp)

private theorem optWireBit_update_of_ne {N : ℕ} (γ : BitAssignment N) (w : Wire N) (v : ZMod 2)
    (wOpt : Option (Wire N)) (hNe : ∀ w', wOpt = some w' → w ≠ w') :
    optWireBit (Function.update γ w v) wOpt = optWireBit γ wOpt := by
  cases wOpt with
  | none => rfl
  | some w' => exact Function.update_of_ne (hNe w' rfl).symm _ _

theorem cleanRealizesSet_lStepInPlaceDyn {Var : Type} [Fintype Var] [DecidableEq Var]
    {N M : ℕ} [NeZero (2 ^ N)] (v : Var) (S : Finset (Wire N))
    (rSrc : QRegister M N) (wB wC wAnc : Wire N) (wBp wCp : Option (Wire N))
    (c1 c2 c3 : Fin M → ZMod 2)
    (hBC : wB ≠ wC) (hBAnc : wB ≠ wAnc) (hCAnc : wC ≠ wAnc)
    (hBSrc : ∀ u, rSrc u ≠ wB) (hCSrc : ∀ u, rSrc u ≠ wC) (hAncSrc : ∀ u, wAnc ≠ rSrc u)
    (hAncBp : ∀ w, wBp = some w → wAnc ≠ w) (hAncCp : ∀ w, wCp = some w → wAnc ≠ w)
    (hBBp : ∀ w, wBp = some w → wB ≠ w) (hCBp : ∀ w, wBp = some w → wC ≠ w)
    (hBCp : ∀ w, wCp = some w → wB ≠ w) (hCCp : ∀ w, wCp = some w → wC ≠ w)
    (hAncS : wAnc ∈ S) (hBNotS : wB ∉ S) (hCNotS : wC ∉ S) :
    SelectSwapQROM.CleanRealizesSet v S
      (diagKetUnitary (lStepPhase rSrc wB wC wBp wCp c1 c2 c3))
      (lStepInPlaceDyn v rSrc wB wC wAnc wBp wCp c1 c2 c3 hBC hBAnc hCAnc
        hBSrc hCSrc hAncSrc hAncBp hAncCp) := by
  let pre := Circuit.seq (cnotMaskW3Circuit wB rSrc hBSrc c1) (cnotMaskW3Circuit wC rSrc hCSrc c2)
  let czCore := Circuit.seq (SelectSwapQROM.czMaskCircuit wAnc M rSrc hAncSrc c3)
    (Circuit.seq (optCzW3Circuit wAnc wBp hAncBp) (optCzW3Circuit wAnc wCp hAncCp))
  have hPreKet (γ : BitAssignment N) :
      pre.eval.1.mulVec (SelectSwapQROM.ket γ) =
        SelectSwapQROM.ket (Function.update
          (Function.update γ wB (γ wB + ∑ u, c1 u * γ (rSrc u)))
          wC (γ wC + ∑ u, c2 u * γ (rSrc u))) := by
    dsimp only [pre]
    rw [SelectSwapQROM.eval_seq_mulVec, ket_cnotMaskW3Circuit, ket_cnotMaskW3Circuit]
    congr 1; congr 1
    rw [Function.update_of_ne hBC.symm]
    congr 1; refine Finset.sum_congr rfl fun u _ ↦ ?_
    rw [Function.update_of_ne (hBSrc u)]
  have hPre : SelectSwapQROM.CleanRealizesSet v S pre.eval (.circuit pre) := by
    refine SelectSwapQROM.CleanRealizesSet.ofCircuit v S pre (by simp [pre]) fun γ hγ ↦ ?_
    rw [hPreKet, SelectSwapQROM.zeroProjOn_mulVec_ket, ite_eq_left]
    intro w hw
    rw [Function.update_of_ne (by rintro rfl; exact hCNotS hw),
      Function.update_of_ne (by rintro rfl; exact hBNotS hw)]
    exact hγ w hw
  have hCzKet (δ : BitAssignment N) :
      czCore.eval.1.mulVec (SelectSwapQROM.ket δ) =
        SelectSwapQROM.bitSign (δ wAnc *
          (∑ u, c3 u * δ (rSrc u) + optWireBit δ wBp + optWireBit δ wCp)) •
          SelectSwapQROM.ket δ := by
    dsimp only [czCore]
    rw [SelectSwapQROM.eval_seq_mulVec, SelectSwapQROM.ket_czMaskCircuit, Matrix.mulVec_smul,
      SelectSwapQROM.eval_seq_mulVec, ket_optCzW3Circuit, Matrix.mulVec_smul,
      ket_optCzW3Circuit, smul_smul, smul_smul, ← SelectSwapQROM.bitSign_add,
      ← SelectSwapQROM.bitSign_add]
    exact congrArg (· • SelectSwapQROM.ket δ) (congrArg SelectSwapQROM.bitSign (by ring))
  have hCz : SelectSwapQROM.CleanRealizesSet v (S.erase wAnc) czCore.eval (.circuit czCore) := by
    refine SelectSwapQROM.CleanRealizesSet.ofCircuit v (S.erase wAnc) czCore
      (by simp [czCore]) fun δ hδ ↦ ?_
    rw [hCzKet δ, Matrix.mulVec_smul, SelectSwapQROM.zeroProjOn_mulVec_ket, ite_eq_left hδ]
  let T_anc := (Circuit.TOFF wB wC wAnc hBC hBAnc hCAnc).eval
  have hSandKet (δ : BitAssignment N) (hδ0 : δ wAnc = 0) :
      (T_anc * czCore.eval * T_anc).1.mulVec (SelectSwapQROM.ket δ) =
        SelectSwapQROM.bitSign (δ wB * δ wC *
          (∑ u, c3 u * δ (rSrc u) + optWireBit δ wBp + optWireBit δ wCp)) •
          SelectSwapQROM.ket δ := by
    simp only [T_anc, Submonoid.coe_mul, ← Matrix.mulVec_mulVec, SelectSwapQROM.ket_TOFF]
    rw [hCzKet, Matrix.mulVec_smul, SelectSwapQROM.ket_TOFF]
    set δ' := Function.update δ wAnc (δ wAnc + δ wB * δ wC)
    have hδ'_anc : δ' wAnc = δ wB * δ wC := by dsimp [δ']; rw [Function.update_self, hδ0, zero_add]
    have hδ'_B : δ' wB = δ wB := Function.update_of_ne hBAnc _ _
    have hδ'_C : δ' wC = δ wC := Function.update_of_ne hCAnc _ _
    have hδ'_src (u : Fin M) : δ' (rSrc u) = δ (rSrc u) :=
      Function.update_of_ne (hAncSrc u).symm _ _
    have hδ'_bp : optWireBit δ' wBp = optWireBit δ wBp :=
      optWireBit_update_of_ne δ wAnc _ wBp hAncBp
    have hδ'_cp : optWireBit δ' wCp = optWireBit δ wCp :=
      optWireBit_update_of_ne δ wAnc _ wCp hAncCp
    have hRest : Function.update δ' wAnc (δ' wAnc + δ' wB * δ' wC) = δ := by
      rw [hδ'_anc, hδ'_B, hδ'_C, CharTwo.add_self_eq_zero]
      dsimp [δ']; rw [Function.update_idem]
      funext q; by_cases hq : q = wAnc
      · subst hq; rw [Function.update_self, hδ0]
      · exact Function.update_of_ne hq _ _
    rw [hRest, hδ'_anc, hδ'_bp, hδ'_cp]
    congr 2; congr 1; congr 1; congr 1
    exact Finset.sum_congr rfl fun u _ ↦ by rw [hδ'_src u]
  have hSand := SelectSwapQROM.CleanRealizesSet.andSandwich hBC hBAnc hCAnc hAncS hBNotS hCNotS
    hCz fun δ hδ ↦ by
      dsimp only
      change ((QRegister.singleton wAnc).basisOutcomeProjector 0).mulVec
        ((T_anc * czCore.eval * T_anc).1.mulVec (SelectSwapQROM.ket δ)) =
        (T_anc * czCore.eval * T_anc).1.mulVec (SelectSwapQROM.ket δ)
      rw [hSandKet δ (hδ wAnc hAncS), Matrix.mulVec_smul]
      have h0 : ((QRegister.singleton wAnc).basisOutcomeProjector 0).mulVec
          (SelectSwapQROM.ket δ) = SelectSwapQROM.ket δ := by
        rw [SelectSwapQROM.basisOutcomeProjector_zero_eq_zeroProjOn, QRegister.image_singleton,
          SelectSwapQROM.zeroProjOn_mulVec_ket, ite_eq_left]
        intro w hw; rw [Finset.mem_singleton.mp hw]; exact hδ wAnc hAncS
      rw [h0]
  have hSeq := hPre.seq (hSand.seq hPre)
  refine hSeq.congr_unitary fun γ hγ ↦ ?_
  rw [diagKetUnitary_mulVec_ket]
  simp only [Submonoid.coe_mul, ← Matrix.mulVec_mulVec]
  rw [hPreKet γ]
  set δ := Function.update (Function.update γ wB (γ wB + ∑ u, c1 u * γ (rSrc u)))
    wC (γ wC + ∑ u, c2 u * γ (rSrc u))
  have hδ0 : δ wAnc = 0 := by
    dsimp [δ]
    rw [Function.update_of_ne hCAnc.symm, Function.update_of_ne hBAnc.symm]
    exact hγ wAnc hAncS
  have hSandExpanded : T_anc.1.mulVec (czCore.eval.1.mulVec
      (T_anc.1.mulVec (SelectSwapQROM.ket δ))) =
      SelectSwapQROM.bitSign
        (δ wB * δ wC * ((∑ u, c3 u * δ (rSrc u)) + optWireBit δ wBp + optWireBit δ wCp)) •
        SelectSwapQROM.ket δ := by
    simpa only [Submonoid.coe_mul, ← Matrix.mulVec_mulVec] using hSandKet δ hδ0
  rw [hSandExpanded, Matrix.mulVec_smul, hPreKet δ]
  have hδSrc (u : Fin M) : δ (rSrc u) = γ (rSrc u) := by
    dsimp [δ]; rw [Function.update_of_ne (hCSrc u), Function.update_of_ne (hBSrc u)]
  have hδB : δ wB = γ wB + ∑ u, c1 u * γ (rSrc u) := by
    dsimp [δ]; rw [Function.update_of_ne hBC, Function.update_self]
  have hδC : δ wC = γ wC + ∑ u, c2 u * γ (rSrc u) := Function.update_self _ _ _
  have hδBp : optWireBit δ wBp = optWireBit γ wBp :=
    (optWireBit_update_of_ne _ wC _ wBp hCBp).trans (optWireBit_update_of_ne _ wB _ wBp hBBp)
  have hδCp : optWireBit δ wCp = optWireBit γ wCp :=
    (optWireBit_update_of_ne _ wC _ wCp hCCp).trans (optWireBit_update_of_ne _ wB _ wCp hBCp)
  have hIdem : Function.update (Function.update δ wB (δ wB + ∑ u, c1 u * δ (rSrc u)))
      wC (δ wC + ∑ u, c2 u * δ (rSrc u)) = γ := by
    have hs1 : (∑ u, c1 u * δ (rSrc u)) = ∑ u, c1 u * γ (rSrc u) :=
      Finset.sum_congr rfl fun u _ ↦ by rw [hδSrc u]
    have hs2 : (∑ u, c2 u * δ (rSrc u)) = ∑ u, c2 u * γ (rSrc u) :=
      Finset.sum_congr rfl fun u _ ↦ by rw [hδSrc u]
    rw [hs1, hs2, hδB, hδC, add_assoc, CharTwo.add_self_eq_zero, add_zero,
      add_assoc, CharTwo.add_self_eq_zero, add_zero]
    funext q
    by_cases hqC : q = wC
    · subst hqC; rw [Function.update_self]
    · rw [Function.update_of_ne hqC]
      by_cases hqB : q = wB
      · subst hqB; rw [Function.update_self]
      · rw [Function.update_of_ne hqB]
        dsimp [δ]; rw [Function.update_of_ne hqC, Function.update_of_ne hqB]
  rw [hIdem, hδB, hδC, hδBp, hδCp]
  congr 2; dsimp only [lStepPhase]; congr 1; congr 1; congr 1
  exact Finset.sum_congr rfl fun u _ ↦ by rw [hδSrc u]

attribute [irreducible] lStepInPlaceDyn

/-! ### ANF Linearity & Orthogonality Helpers -/

private theorem anfCoeffs_add :
    ∀ (s : ℕ) (f g : Fin (2 ^ s) → ZMod 2) (m : Fin (2 ^ s)),
      SelectSwapQROM.anfCoeffs s (fun u ↦ f u + g u) m =
        SelectSwapQROM.anfCoeffs s f m + SelectSwapQROM.anfCoeffs s g m
  | 0, _, _, _ => rfl
  | s + 1, f, g, m => by
      simp only [SelectSwapQROM.anfCoeffs]
      split_ifs with hm
      · exact anfCoeffs_add s _ _ _
      · refine (congrArg (fun h ↦ SelectSwapQROM.anfCoeffs s h _) (funext fun u ↦ ?_)).trans
          (anfCoeffs_add s _ _ _)
        ring

private theorem anfCoeffs_smul :
    ∀ (s : ℕ) (c : ZMod 2) (f : Fin (2 ^ s) → ZMod 2) (m : Fin (2 ^ s)),
      SelectSwapQROM.anfCoeffs s (fun u ↦ c * f u) m = c * SelectSwapQROM.anfCoeffs s f m
  | 0, _, _, _ => rfl
  | s + 1, c, f, m => by
      simp only [SelectSwapQROM.anfCoeffs]
      split_ifs with hm
      · exact anfCoeffs_smul s c _ _
      · refine (congrArg (fun h ↦ SelectSwapQROM.anfCoeffs s h _) (funext fun u ↦ ?_)).trans
          (anfCoeffs_smul s c _ _)
        ring

private theorem anfCoeffs_zero_fn :
    ∀ (s : ℕ) (m : Fin (2 ^ s)), SelectSwapQROM.anfCoeffs s (fun _ ↦ (0 : ZMod 2)) m = 0
  | 0, _ => rfl
  | s + 1, m => by
      simp only [SelectSwapQROM.anfCoeffs, add_zero]
      split_ifs <;> exact anfCoeffs_zero_fn s _

private theorem anfCoeffs_sum_fin :
    ∀ (n s : ℕ) (F : Fin n → Fin (2 ^ s) → ZMod 2) (m : Fin (2 ^ s)),
      SelectSwapQROM.anfCoeffs s (fun u ↦ ∑ i : Fin n, F i u) m =
        ∑ i : Fin n, SelectSwapQROM.anfCoeffs s (F i) m
  | 0, s, _, m => by simp [anfCoeffs_zero_fn]
  | n + 1, s, F, m => by
      simp_rw [Fin.sum_univ_castSucc]
      rw [anfCoeffs_add, anfCoeffs_sum_fin n s]

private theorem anfCoeffs_const_pos :
    ∀ (s : ℕ) (c : ZMod 2) (m : Fin (2 ^ s)), 0 < m.val →
      SelectSwapQROM.anfCoeffs s (fun _ ↦ c) m = 0
  | 0, _, m, hm => by have := m.isLt; omega
  | s + 1, c, m, hm => by
      simp only [SelectSwapQROM.anfCoeffs]
      split_ifs with hlt
      · exact anfCoeffs_const_pos s c ⟨m.val, hlt⟩ hm
      · simp_rw [CharTwo.add_self_eq_zero]
        exact anfCoeffs_zero_fn s _

private theorem anfCoeffs_monoEval2 (m₀ m : Fin (2 ^ 2)) :
    SelectSwapQROM.anfCoeffs 2
      (fun z ↦ SelectSwapQROM.monoEval 2 (basisBits 2 z) m₀) m =
      if m = m₀ then 1 else 0 := by
  revert m₀ m; decide

private theorem anfCoeffs_monoEval3 (m₀ m : Fin (2 ^ 3)) :
    SelectSwapQROM.anfCoeffs 3
      (fun z ↦ SelectSwapQROM.monoEval 3 (basisBits 3 z) m₀) m =
      if m = m₀ then 1 else 0 := by
  revert m₀ m; decide

/-! ## Section 3: Cold `(5, 4, 3)` L-Triple Unloader (`73` ANDs = `292 T`, `25 ≤ sScr`) -/

private theorem split_pow3_7 (f : Fin (2 ^ 3) → ZMod 2) :
    (∑ m : Fin (2 ^ 3), f m) =
      f ⟨0, by decide⟩ + ∑ u : Fin 7, f ⟨u.val + 1, by omega⟩ := by
  let e : Fin (2 ^ 3) ≃ Fin (7 + 1) := finCongr rfl
  rw [← Equiv.sum_comp e.symm, Fin.sum_univ_succ]
  rfl

/-- Optional `4`-bit non-zero monomial evaluation (`0` when `none`). -/
def optMono4 (zB : Fin (2 ^ 4)) : Option (Fin 14) → ZMod 2
  | none => 0
  | some j => SelectSwapQROM.monoEval 4 (basisBits 4 zB) ⟨j.val + 1, by omega⟩

/-- Optional `3`-bit non-zero monomial evaluation (`0` when `none`). -/
def optMono3 (zC : Fin (2 ^ 3)) : Option (Fin 7) → ZMod 2
  | none => 0
  | some k => SelectSwapQROM.monoEval 3 (basisBits 3 zC) ⟨k.val + 1, by omega⟩

private theorem anfCoeffs3_optMono3_pos (kp : Option (Fin 7)) (uC : Fin 7) :
    SelectSwapQROM.anfCoeffs 3 (fun zC ↦ optMono3 zC kp) ⟨uC.val + 1, by omega⟩ =
      if kp = some uC then 1 else 0 := by
  revert kp uC; decide

private theorem lStep_zmod2_decomp (b g a1 a2 a3 bp gp : ZMod 2) :
    (b + a1) * (g + a2) * (a3 + bp + gp) =
      ((a3 * b * g + a1 * bp * g) + a2 * b * gp) +
      ((b * g * (bp + gp) + (b * (a3 + bp) + a1 * bp) * a2) +
       a1 * (g + a2) * (a3 + gp)) := by
  ring

private theorem anf_expand_1d (s : ℕ) (f : Fin (2 ^ s) → ZMod 2) (z : Fin (2 ^ s)) :
    ∃ c : Fin (2 ^ s) → ZMod 2,
      (∀ m, c m = SelectSwapQROM.anfCoeffs s f m) ∧
      f z = ∑ m : Fin (2 ^ s), c m * SelectSwapQROM.monoEval s (basisBits s z) m :=
  ⟨SelectSwapQROM.anfCoeffs s f, fun _ ↦ rfl, by
    have h := (SelectSwapQROM.sum_anfCoeffs_mul_monoEval s f (basisBits s z)).symm
    rwa [SelectSwapQROM.symm_basisBits] at h⟩

theorem option_map_ne_of_ne {α β : Type*} (f : α → β) :
    ∀ (o : Option α) (x : β), (∀ a, x ≠ f a) → ∀ w, o.map f = some w → x ≠ w
  | none, _, _, _, hw => by cases hw
  | some a, _, h, _, hw => Option.some.inj hw ▸ h a

private theorem zmod2_ite_xor_w3 (a b : Bool) :
    (if (a != b) then (1 : ZMod 2) else 0) =
      (if a then (1 : ZMod 2) else 0) + (if b then (1 : ZMod 2) else 0) := by
  cases a <;> cases b <;> decide

/-! ## Section 4: Hot `(3, 2)` L-Triple Unloader (`12` ANDs = `48 T`, `0 TOFF`, `0 ≤ sScr`)
    and Turnkey One-Hot Möbius Congruence Bridges -/

/-- Computational-basis predicate asserting that `rHotCtx` holds a weight-`1` one-hot bitstring
(`∃ c₀ : Fin L_ctx, ∀ c : Fin L_ctx, β (rHotCtx c) = if c = c₀ then 1 else 0`). -/
def oneHotPred {N L_ctx : ℕ} (rHotCtx : QRegister L_ctx N) (β : BitAssignment N) : Bool :=
  decide (∃ c₀ : Fin L_ctx, ∀ c : Fin L_ctx, β (rHotCtx c) = if c = c₀ then 1 else 0)

private theorem sum_mul_oneHot {L_ctx : ℕ} (M : Fin L_ctx → ZMod 2) (c₀ : Fin L_ctx)
    {f : Fin L_ctx → ZMod 2} (hf : ∀ c : Fin L_ctx, f c = if c = c₀ then 1 else 0) :
    (∑ c : Fin L_ctx, M c * f c) = M c₀ := by
  rw [Finset.sum_eq_single c₀]
  · rw [hf c₀, ite_eq_left rfl, mul_one]
  · intro c _ hne; rw [hf c, ite_eq_right hne, mul_zero]
  · intro h; exact absurd (Finset.mem_univ c₀) h

/-- Index map extracting `(b_0, b_4)` from a `5`-bit address register. -/
def c2In5Idx : Fin 2 → Fin 5
  | ⟨0, _⟩ => ⟨0, by decide⟩
  | ⟨1, _⟩ => ⟨4, by decide⟩

theorem c2In5Idx_inj : Function.Injective c2In5Idx := by decide

/-- `2`-wire subregister `(b_0, b_4)` inside `Fin 5`. -/
def c2In5Reg : QRegister 2 5 := ⟨⟨c2In5Idx, c2In5Idx_inj⟩⟩

/-- Address reconstruction `Fin (2 ^ 3) × Fin (2 ^ 2) → Fin (2 ^ 5)` from `(b_1..b_3)` and
`(b_0, b_4)`. -/
def cubeAddr5 (zB : Fin (2 ^ 3)) (zC : Fin (2 ^ 2)) : Fin (2 ^ 5) :=
  ⟨(zC.val % 2) + 2 * zB.val + 16 * (zC.val / 2),
    by have := zB.isLt; have := zC.isLt; omega⟩

private theorem basisBits5_cubeAddr5_b (zB : Fin (2 ^ 3)) (zC : Fin (2 ^ 2)) (i : Fin 3) :
    basisBits 5 (cubeAddr5 zB zC) ⟨1 + i.val, by omega⟩ = basisBits 3 zB i := by
  revert zB zC i; decide

private theorem basisBits5_cubeAddr5_c (zB : Fin (2 ^ 3)) (zC : Fin (2 ^ 2)) (i : Fin 2) :
    basisBits 5 (cubeAddr5 zB zC) (c2In5Idx i) = basisBits 2 zC i := by
  revert zB zC i; decide

private theorem symm5_eq_cubeAddr5 (x : Fin 5 → ZMod 2) :
    (basisBits 5).symm x =
      cubeAddr5
        ((basisBits 3).symm (fun i ↦ x ⟨1 + i.val, by omega⟩))
        ((basisBits 2).symm (fun i ↦ x (c2In5Idx i))) := by
  apply (basisBits 5).injective
  funext q
  rw [SelectSwapQROM.basisBits_symm]
  by_cases hq0 : q.val = 0
  · have hq : q = c2In5Idx ⟨0, by decide⟩ := Fin.ext hq0
    rw [hq, basisBits5_cubeAddr5_c]; dsimp; rw [SelectSwapQROM.basisBits_symm]
  · by_cases hq4 : q.val < 4
    · let i : Fin 3 := ⟨q.val - 1, by omega⟩
      have hq : q = ⟨1 + i.val, by omega⟩ := Fin.ext (by dsimp [i]; omega)
      rw [hq, basisBits5_cubeAddr5_b]; dsimp; rw [SelectSwapQROM.basisBits_symm]
    · have hq4e : q.val = 4 := by have := q.isLt; omega
      have hq : q = c2In5Idx ⟨1, by decide⟩ := Fin.ext hq4e
      rw [hq, basisBits5_cubeAddr5_c]; dsimp; rw [SelectSwapQROM.basisBits_symm]

/-- `2D` `(3, 2)` ANF coefficients on `Fin (2 ^ 3) × Fin (2 ^ 2)`. -/
def anf2DCoeffs (g : Fin (2 ^ 3) → Fin (2 ^ 2) → ZMod 2)
    (mB : Fin (2 ^ 3)) (mC : Fin (2 ^ 2)) : ZMod 2 :=
  SelectSwapQROM.anfCoeffs 3
    (fun zB ↦ SelectSwapQROM.anfCoeffs 2 (fun zC ↦ g zB zC) mC) mB

private theorem anf2DCoeffs_add (f g : Fin (2 ^ 3) → Fin (2 ^ 2) → ZMod 2)
    (mB : Fin (2 ^ 3)) (mC : Fin (2 ^ 2)) :
    anf2DCoeffs (fun zB zC ↦ f zB zC + g zB zC) mB mC =
      anf2DCoeffs f mB mC + anf2DCoeffs g mB mC := by
  dsimp only [anf2DCoeffs]
  have h1 (zB : Fin (2 ^ 3)) := anfCoeffs_add 2 (fun zC ↦ f zB zC) (fun zC ↦ g zB zC) mC
  simp_rw [h1]; exact anfCoeffs_add 3 _ _ mB

private theorem anf2DCoeffs_smul (c : ZMod 2) (f : Fin (2 ^ 3) → Fin (2 ^ 2) → ZMod 2)
    (mB : Fin (2 ^ 3)) (mC : Fin (2 ^ 2)) :
    anf2DCoeffs (fun zB zC ↦ c * f zB zC) mB mC = c * anf2DCoeffs f mB mC := by
  dsimp only [anf2DCoeffs]
  have h1 (zB : Fin (2 ^ 3)) := anfCoeffs_smul 2 c (fun zC ↦ f zB zC) mC
  simp_rw [h1]; exact anfCoeffs_smul 3 c _ mB

private theorem anf2DCoeffs_sum_fin :
    ∀ (n : ℕ) (F : Fin n → Fin (2 ^ 3) → Fin (2 ^ 2) → ZMod 2)
      (mB : Fin (2 ^ 3)) (mC : Fin (2 ^ 2)),
      anf2DCoeffs (fun zB zC ↦ ∑ t : Fin n, F t zB zC) mB mC =
        ∑ t : Fin n, anf2DCoeffs (F t) mB mC
  | 0, _, mB, mC => by
      dsimp only [anf2DCoeffs]
      simp_rw [Fin.sum_univ_zero, anfCoeffs_zero_fn]
  | n + 1, F, mB, mC => by
      simp_rw [Fin.sum_univ_castSucc]
      rw [anf2DCoeffs_add, anf2DCoeffs_sum_fin n]

private theorem anf2DCoeffs_sep (fB : Fin (2 ^ 3) → ZMod 2) (fC : Fin (2 ^ 2) → ZMod 2)
    (mB : Fin (2 ^ 3)) (mC : Fin (2 ^ 2)) :
    anf2DCoeffs (fun zB zC ↦ fB zB * fC zC) mB mC =
      SelectSwapQROM.anfCoeffs 3 fB mB * SelectSwapQROM.anfCoeffs 2 fC mC := by
  dsimp only [anf2DCoeffs]
  have h1 (zB : Fin (2 ^ 3)) := anfCoeffs_smul 2 (fB zB) fC mC
  simp_rw [h1, mul_comm _ (SelectSwapQROM.anfCoeffs 2 fC mC), anfCoeffs_smul 3]

private theorem anf2DCoeffs_cubeAddr5_7_2_delta (u : Fin (2 ^ 5)) :
    anf2DCoeffs (fun zB zC ↦ if cubeAddr5 zB zC = u then (1 : ZMod 2) else 0)
      ⟨7, by decide⟩ ⟨2, by decide⟩ =
      SelectSwapQROM.anfCoeffs 5 (fun x ↦ if x = u then 1 else 0) ⟨30, by decide⟩ := by
  revert u; decide

private theorem anf2DCoeffs_cubeAddr5_7_3_delta (u : Fin (2 ^ 5)) :
    anf2DCoeffs (fun zB zC ↦ if cubeAddr5 zB zC = u then (1 : ZMod 2) else 0)
      ⟨7, by decide⟩ ⟨3, by decide⟩ =
      SelectSwapQROM.anfCoeffs 5 (fun x ↦ if x = u then 1 else 0) ⟨31, by decide⟩ := by
  revert u; decide

private theorem fn5_eq_sum_delta (f : Fin (2 ^ 5) → ZMod 2) (x : Fin (2 ^ 5)) :
    f x = ∑ u : Fin (2 ^ 5), f u * (if x = u then 1 else 0) := by
  rw [Finset.sum_eq_single x]
  · simp
  · intro u _ hne; simp [Ne.symm hne]
  · intro h; exact absurd (Finset.mem_univ x) h

private theorem anf2DCoeffs_cubeAddr5_7_2 (f : Fin (2 ^ 5) → ZMod 2) :
    anf2DCoeffs (fun zB zC ↦ f (cubeAddr5 zB zC)) ⟨7, by decide⟩ ⟨2, by decide⟩ =
      SelectSwapQROM.anfCoeffs 5 f ⟨30, by decide⟩ := by
  have hfL : (fun zB zC ↦ f (cubeAddr5 zB zC)) =
      (fun zB zC ↦ ∑ u : Fin (2 ^ 5), f u * (if cubeAddr5 zB zC = u then 1 else 0)) :=
    funext fun zB ↦ funext fun zC ↦ fn5_eq_sum_delta f (cubeAddr5 zB zC)
  have hfR : f = fun x ↦ ∑ u : Fin (2 ^ 5), f u * (if x = u then 1 else 0) :=
    funext (fn5_eq_sum_delta f)
  rw [hfL, anf2DCoeffs_sum_fin (2 ^ 5) (fun u zB zC ↦ f u * if cubeAddr5 zB zC = u then 1 else 0)]
  conv_rhs => rw [hfR, anfCoeffs_sum_fin (2 ^ 5) 5 (fun u x ↦ f u * if x = u then 1 else 0)]
  refine Finset.sum_congr rfl fun u _ ↦ ?_
  rw [anf2DCoeffs_smul, anfCoeffs_smul 5, anf2DCoeffs_cubeAddr5_7_2_delta u]

private theorem anf2DCoeffs_cubeAddr5_7_3 (f : Fin (2 ^ 5) → ZMod 2) :
    anf2DCoeffs (fun zB zC ↦ f (cubeAddr5 zB zC)) ⟨7, by decide⟩ ⟨3, by decide⟩ =
      SelectSwapQROM.anfCoeffs 5 f ⟨31, by decide⟩ := by
  have hfL : (fun zB zC ↦ f (cubeAddr5 zB zC)) =
      (fun zB zC ↦ ∑ u : Fin (2 ^ 5), f u * (if cubeAddr5 zB zC = u then 1 else 0)) :=
    funext fun zB ↦ funext fun zC ↦ fn5_eq_sum_delta f (cubeAddr5 zB zC)
  have hfR : f = fun x ↦ ∑ u : Fin (2 ^ 5), f u * (if x = u then 1 else 0) :=
    funext (fn5_eq_sum_delta f)
  rw [hfL, anf2DCoeffs_sum_fin (2 ^ 5) (fun u zB zC ↦ f u * if cubeAddr5 zB zC = u then 1 else 0)]
  conv_rhs => rw [hfR, anfCoeffs_sum_fin (2 ^ 5) 5 (fun u x ↦ f u * if x = u then 1 else 0)]
  refine Finset.sum_congr rfl fun u _ ↦ ?_
  rw [anf2DCoeffs_smul, anfCoeffs_smul 5, anf2DCoeffs_cubeAddr5_7_3_delta u]

private theorem split_pow2_3 (f : Fin (2 ^ 2) → ZMod 2) :
    (∑ m : Fin (2 ^ 2), f m) =
      f ⟨0, by decide⟩ + ∑ u : Fin 3, f ⟨u.val + 1, by omega⟩ := by
  let e : Fin (2 ^ 2) ≃ Fin (3 + 1) := finCongr rfl
  rw [← Equiv.sum_comp e.symm, Fin.sum_univ_succ]
  rfl

/-- Exact `7`-step L-triple partition of `Fin 7 × Fin 3 \ {(6, 1), (6, 2)}`. -/
def canonLeg2 : Fin 7 → Fin 7 × Fin 3 × Option (Fin 7) × Option (Fin 3)
  | ⟨0, _⟩ => (⟨0, by decide⟩, ⟨2, by decide⟩, some ⟨5, by decide⟩, some ⟨0, by decide⟩)
  | ⟨1, _⟩ => (⟨5, by decide⟩, ⟨1, by decide⟩, some ⟨0, by decide⟩, some ⟨0, by decide⟩)
  | ⟨2, _⟩ => (⟨1, by decide⟩, ⟨0, by decide⟩, some ⟨4, by decide⟩, none)
  | ⟨3, _⟩ => (⟨3, by decide⟩, ⟨1, by decide⟩, some ⟨1, by decide⟩, some ⟨0, by decide⟩)
  | ⟨4, _⟩ => (⟨2, by decide⟩, ⟨2, by decide⟩, some ⟨1, by decide⟩, some ⟨1, by decide⟩)
  | ⟨5, _⟩ => (⟨2, by decide⟩, ⟨0, by decide⟩, some ⟨6, by decide⟩, none)
  | ⟨6, _⟩ => (⟨4, by decide⟩, ⟨2, by decide⟩, some ⟨3, by decide⟩, some ⟨1, by decide⟩)

theorem canonLeg2_j_ne_jp (t : Fin 7) :
    ∀ j' : Fin 7, (canonLeg2 t).2.2.1 = some j' → (canonLeg2 t).1 ≠ j' := by
  revert t; decide

theorem canonLeg2_k_ne_kp (t : Fin 7) :
    ∀ k' : Fin 3, (canonLeg2 t).2.2.2 = some k' → (canonLeg2 t).2.1 ≠ k' := by
  revert t; decide

/-- `ZMod 2` indicator of the `2` or `3` pairs in `Fin 7 × Fin 3` covered by step `t`. -/
def stepCoverZMod2 (t : Fin 7) (uB : Fin 7) (uC : Fin 3) : ZMod 2 :=
  let s := canonLeg2 t
  (if uB = s.1 ∧ uC = s.2.1 then 1 else 0) +
  (if s.2.2.1 = some uB ∧ uC = s.2.1 then 1 else 0) +
  (if uB = s.1 ∧ s.2.2.2 = some uC then 1 else 0)

private theorem sum_stepCoverZMod2_eq (uB : Fin 7) (uC : Fin 3) :
    (∑ t : Fin 7, stepCoverZMod2 t uB uC) =
      if (uB.val = 6 ∧ uC.val = 1) ∨ (uB.val = 6 ∧ uC.val = 2) then 0 else 1 := by
  revert uB uC; decide

/-- Optional `2`-bit monomial evaluation (`0` when `none`). -/
def optMono2 (zC : Fin (2 ^ 2)) : Option (Fin 3) → ZMod 2
  | none => 0
  | some k => SelectSwapQROM.monoEval 2 (basisBits 2 zC) ⟨k.val + 1, by omega⟩

private theorem anfCoeffs2_optMono2_pos (kp : Option (Fin 3)) (uC : Fin 3) :
    SelectSwapQROM.anfCoeffs 2 (fun zC ↦ optMono2 zC kp) ⟨uC.val + 1, by omega⟩ =
      if kp = some uC then 1 else 0 := by
  cases kp with
  | none => exact anfCoeffs_zero_fn 2 _
  | some k' =>
      dsimp only [optMono2]; rw [anfCoeffs_monoEval2]
      by_cases h : k' = uC
      · subst h; simp
      · have hne : (⟨uC.val + 1, by omega⟩ : Fin 4) ≠ ⟨k'.val + 1, by omega⟩ :=
          fun he ↦ h (Fin.ext (by have := congrArg Fin.val he; dsimp at this; omega))
        simp [h, hne]

/-- Cubic background phase term `b_j(zB) * g_k(zC) * (bp_{jp}(zB) + gp_{kp}(zC))` at step `t`. -/
def bg2Cube (t : Fin 7) (zB : Fin (2 ^ 3)) (zC : Fin (2 ^ 2)) : ZMod 2 :=
  let j := (canonLeg2 t).1
  let k := (canonLeg2 t).2.1
  let jp := (canonLeg2 t).2.2.1
  let kp := (canonLeg2 t).2.2.2
  SelectSwapQROM.monoEval 3 (basisBits 3 zB) ⟨j.val + 1, by omega⟩ *
    SelectSwapQROM.monoEval 2 (basisBits 2 zC) ⟨k.val + 1, by omega⟩ *
    (optMono3 zB jp + optMono2 zC kp)

/-- Sum of the `7` slice-independent cubic background terms `bg2Cube t`. -/
def bg2Sum (zB : Fin (2 ^ 3)) (zC : Fin (2 ^ 2)) : ZMod 2 :=
  ∑ t : Fin 7, bg2Cube t zB zC

/-- `2D` bilinear `CZ` coefficients cancelling `bg2Sum` on `rAllB × rAllC` (`0 T`). -/
def bg2Coeff (uB : Fin 7) (uC : Fin 3) : ZMod 2 :=
  anf2DCoeffs bg2Sum ⟨uB.val + 1, by omega⟩ ⟨uC.val + 1, by omega⟩

private theorem bg2Sum_eq_bilinear (zB : Fin (2 ^ 3)) (zC : Fin (2 ^ 2)) :
    bg2Sum zB zC =
      ∑ uB : Fin 7, SelectSwapQROM.monoEval 3 (basisBits 3 zB) ⟨uB.val + 1, by omega⟩ *
        ∑ uC : Fin 3, bg2Coeff uB uC *
          SelectSwapQROM.monoEval 2 (basisBits 2 zC) ⟨uC.val + 1, by omega⟩ := by
  revert zB zC; decide

/-- Per-slice L-step masks `(c1, c2, c3)` on `Fin L_ctx` for step `t : Fin 7`. -/
def leg2Masks {L_ctx : ℕ} (P_slice : Fin L_ctx → Fin (2 ^ 3) → Fin (2 ^ 2) → ZMod 2)
    (t : Fin 7) : (Fin L_ctx → ZMod 2) × (Fin L_ctx → ZMod 2) × (Fin L_ctx → ZMod 2) :=
  let j := (canonLeg2 t).1
  let k := (canonLeg2 t).2.1
  let jp := (canonLeg2 t).2.2.1
  let kp := (canonLeg2 t).2.2.2
  (fun c ↦ match jp with
    | none => 0
    | some j' => anf2DCoeffs (P_slice c) ⟨j'.val + 1, by omega⟩ ⟨k.val + 1, by omega⟩,
   fun c ↦ match kp with
    | none => 0
    | some k' => anf2DCoeffs (P_slice c) ⟨j.val + 1, by omega⟩ ⟨k'.val + 1, by omega⟩,
   fun c ↦ anf2DCoeffs (P_slice c) ⟨j.val + 1, by omega⟩ ⟨k.val + 1, by omega⟩)

/-- Per-slice residual phase term at step `t` after subtracting `bg2Cube t`. -/
def lin2Term (a1 a2 a3 : ZMod 2) (t : Fin 7) (zB : Fin (2 ^ 3)) (zC : Fin (2 ^ 2)) : ZMod 2 :=
  let j := (canonLeg2 t).1
  let k := (canonLeg2 t).2.1
  let jp := (canonLeg2 t).2.2.1
  let kp := (canonLeg2 t).2.2.2
  (SelectSwapQROM.monoEval 3 (basisBits 3 zB) ⟨j.val + 1, by omega⟩ + a1) *
    (SelectSwapQROM.monoEval 2 (basisBits 2 zC) ⟨k.val + 1, by omega⟩ + a2) *
    (a3 + optMono3 zB jp + optMono2 zC kp) +
  bg2Cube t zB zC

private theorem anf2DCoeffs_lin2Term_bilinear {L_ctx : ℕ}
    (P_slice : Fin L_ctx → Fin (2 ^ 3) → Fin (2 ^ 2) → ZMod 2) (c : Fin L_ctx)
    (t : Fin 7) (uB : Fin 7) (uC : Fin 3) :
    let msk := leg2Masks P_slice t
    anf2DCoeffs (lin2Term (msk.1 c) (msk.2.1 c) (msk.2.2 c) t)
      ⟨uB.val + 1, by omega⟩ ⟨uC.val + 1, by omega⟩ =
      stepCoverZMod2 t uB uC *
        anf2DCoeffs (P_slice c) ⟨uB.val + 1, by omega⟩ ⟨uC.val + 1, by omega⟩ := by
  intro msk
  let a1 := msk.1 c; let a2 := msk.2.1 c; let a3 := msk.2.2 c
  let b (zB : Fin (2 ^ 3)) :=
    SelectSwapQROM.monoEval 3 (basisBits 3 zB) ⟨(canonLeg2 t).1.val + 1, by omega⟩
  let bp (zB : Fin (2 ^ 3)) := optMono3 zB (canonLeg2 t).2.2.1
  let g (zC : Fin (2 ^ 2)) :=
    SelectSwapQROM.monoEval 2 (basisBits 2 zC) ⟨(canonLeg2 t).2.1.val + 1, by omega⟩
  let gp (zC : Fin (2 ^ 2)) := optMono2 zC (canonLeg2 t).2.2.2
  let mB : Fin (2 ^ 3) := ⟨uB.val + 1, by omega⟩
  let mC : Fin (2 ^ 2) := ⟨uC.val + 1, by omega⟩
  have hDecomp : lin2Term a1 a2 a3 t = fun zB zC ↦
      ((a3 * b zB) * g zC + (a1 * bp zB) * g zC + (a2 * b zB) * gp zC) +
      ((b zB * (a3 + bp zB) + a1 * bp zB) * a2) +
      (a1 * (g zC + a2) * (a3 + gp zC)) := by
    funext zB zC
    dsimp only [lin2Term, bg2Cube, b, bp, g, gp]
    have hL := lStep_zmod2_decomp (b zB) (g zC) a1 a2 a3 (bp zB) (gp zC)
    rw [hL]
    have hR (x y z w : ZMod 2) : x + ((y + z) + w) + y = (y + y) + (x + z + w) := by ring
    rw [hR, CharTwo.add_self_eq_zero, zero_add]
  rw [hDecomp, anf2DCoeffs_add, anf2DCoeffs_add, anf2DCoeffs_add, anf2DCoeffs_add]
  have hzC : anf2DCoeffs (fun zB _ ↦ (b zB * (a3 + bp zB) + a1 * bp zB) * a2) mB mC = 0 := by
    dsimp only [anf2DCoeffs]
    have h0 (zB : Fin (2 ^ 3)) :
        SelectSwapQROM.anfCoeffs 2
          (fun _ ↦ (b zB * (a3 + bp zB) + a1 * bp zB) * a2) mC = 0 :=
      anfCoeffs_const_pos 2 _ mC (by dsimp [mC]; omega)
    simp_rw [h0]; exact anfCoeffs_zero_fn 3 mB
  have hzB : anf2DCoeffs (fun _ zC ↦ a1 * (g zC + a2) * (a3 + gp zC)) mB mC = 0 :=
    anfCoeffs_const_pos 3 _ mB (by dsimp [mB]; omega)
  rw [hzC, hzB, add_zero, add_zero, anf2DCoeffs_sep, anf2DCoeffs_sep, anf2DCoeffs_sep,
    anfCoeffs_smul 3, anfCoeffs_smul 3, anfCoeffs_smul 3]
  dsimp only [b, bp, g, gp, mB, mC]
  rw [anfCoeffs_monoEval3, anfCoeffs_monoEval2, anfCoeffs3_optMono3_pos, anfCoeffs2_optMono2_pos]
  have hbEq : ((⟨uB.val + 1, by omega⟩ : Fin 8) = ⟨(canonLeg2 t).1.val + 1, by omega⟩) ↔
      uB = (canonLeg2 t).1 :=
    ⟨fun h ↦ Fin.ext (by have := congrArg Fin.val h; dsimp at this; omega), fun h ↦ by subst h; rfl⟩
  have hgEq : ((⟨uC.val + 1, by omega⟩ : Fin 4) = ⟨(canonLeg2 t).2.1.val + 1, by omega⟩) ↔
      uC = (canonLeg2 t).2.1 :=
    ⟨fun h ↦ Fin.ext (by have := congrArg Fin.val h; dsimp at this; omega), fun h ↦ by subst h; rfl⟩
  simp only [hbEq, hgEq]
  have hT1 : a3 * (if uB = (canonLeg2 t).1 then 1 else 0) *
      (if uC = (canonLeg2 t).2.1 then 1 else 0) =
      (if uB = (canonLeg2 t).1 ∧ uC = (canonLeg2 t).2.1 then 1 else 0) *
        anf2DCoeffs (P_slice c) ⟨uB.val + 1, by omega⟩ ⟨uC.val + 1, by omega⟩ := by
    dsimp only [a3, msk, leg2Masks]
    by_cases hB : uB = (canonLeg2 t).1 <;> by_cases hC : uC = (canonLeg2 t).2.1 <;>
      simp [hB, hC, mul_comm]
  have hT2 : a1 * (if (canonLeg2 t).2.2.1 = some uB then 1 else 0) *
      (if uC = (canonLeg2 t).2.1 then 1 else 0) =
      (if (canonLeg2 t).2.2.1 = some uB ∧ uC = (canonLeg2 t).2.1 then 1 else 0) *
        anf2DCoeffs (P_slice c) ⟨uB.val + 1, by omega⟩ ⟨uC.val + 1, by omega⟩ := by
    dsimp only [a1, msk, leg2Masks]
    cases hjp : (canonLeg2 t).2.2.1 with
    | none => simp
    | some j' =>
      by_cases hj' : j' = uB <;> by_cases hC : uC = (canonLeg2 t).2.1 <;>
        simp [hj', hC, mul_comm]
  have hT3 : a2 * (if uB = (canonLeg2 t).1 then 1 else 0) *
      (if (canonLeg2 t).2.2.2 = some uC then 1 else 0) =
      (if uB = (canonLeg2 t).1 ∧ (canonLeg2 t).2.2.2 = some uC then 1 else 0) *
        anf2DCoeffs (P_slice c) ⟨uB.val + 1, by omega⟩ ⟨uC.val + 1, by omega⟩ := by
    dsimp only [a2, msk, leg2Masks]
    cases hkp : (canonLeg2 t).2.2.2 with
    | none => simp
    | some k' =>
      by_cases hB : uB = (canonLeg2 t).1 <;> by_cases hk' : k' = uC <;>
        simp [hB, hk', mul_comm]
  rw [hT1, hT2, hT3]
  dsimp only [stepCoverZMod2]; ring

private theorem anf2DCoeffs_def (g : Fin (2 ^ 3) → Fin (2 ^ 2) → ZMod 2)
    (mB : Fin (2 ^ 3)) (mC : Fin (2 ^ 2)) :
    anf2DCoeffs g mB mC =
      SelectSwapQROM.anfCoeffs 3
        (fun zB ↦ SelectSwapQROM.anfCoeffs 2 (fun zC ↦ g zB zC) mC) mB := rfl

attribute [irreducible] anf2DCoeffs leg2Masks bg2Coeff

private theorem anf2DCoeffs_eval_residual
    (R : Fin (2 ^ 3) → Fin (2 ^ 2) → ZMod 2)
    (hBi : ∀ (uB : Fin 7) (uC : Fin 3),
      anf2DCoeffs R ⟨uB.val + 1, by omega⟩ ⟨uC.val + 1, by omega⟩ = 0)
    (zB : Fin (2 ^ 3)) (zC : Fin (2 ^ 2)) :
    R zB zC =
      anf2DCoeffs R ⟨0, by decide⟩ ⟨0, by decide⟩ +
      (∑ uB : Fin 7, anf2DCoeffs R ⟨uB.val + 1, by omega⟩ ⟨0, by decide⟩ *
        SelectSwapQROM.monoEval 3 (basisBits 3 zB) ⟨uB.val + 1, by omega⟩) +
      (∑ uC : Fin 3, anf2DCoeffs R ⟨0, by decide⟩ ⟨uC.val + 1, by omega⟩ *
        SelectSwapQROM.monoEval 2 (basisBits 2 zC) ⟨uC.val + 1, by omega⟩) := by
  obtain ⟨α₀, hα₀⟩ :
      ∃ α₀ : Fin 7 → ZMod 2,
        α₀ = fun uB ↦ SelectSwapQROM.monoEval 3 (basisBits 3 zB) ⟨uB.val + 1, by omega⟩ :=
    ⟨_, rfl⟩
  obtain ⟨γ₀, hγ₀⟩ :
      ∃ γ₀ : Fin 3 → ZMod 2,
        γ₀ = fun uC ↦ SelectSwapQROM.monoEval 2 (basisBits 2 zC) ⟨uC.val + 1, by omega⟩ :=
    ⟨_, rfl⟩
  have hαM (uB : Fin 7) (h : uB.val + 1 < 2 ^ 3) :
      SelectSwapQROM.monoEval 3 (basisBits 3 zB) ⟨uB.val + 1, h⟩ = α₀ uB := by
    rw [hα₀]
  have hγM (uC : Fin 3) (h : uC.val + 1 < 2 ^ 2) :
      SelectSwapQROM.monoEval 2 (basisBits 2 zC) ⟨uC.val + 1, h⟩ = γ₀ uC := by
    rw [hγ₀]
  obtain ⟨F2, hF2Def, hF2Eval⟩ :
      ∃ F2 : Fin (2 ^ 2) → ZMod 2,
        (∀ mC, F2 mC = SelectSwapQROM.anfCoeffs 2 (fun zC' ↦ R zB zC') mC) ∧
        R zB zC = ∑ mC : Fin (2 ^ 2), F2 mC * SelectSwapQROM.monoEval 2 (basisBits 2 zC) mC :=
    anf_expand_1d 2 (fun zC' ↦ R zB zC') zC
  have eB (mC : Fin (2 ^ 2)) :
      F2 mC = anf2DCoeffs R ⟨0, by decide⟩ mC +
        ∑ uB : Fin 7, anf2DCoeffs R ⟨uB.val + 1, by omega⟩ mC * α₀ uB := by
    obtain ⟨c3, hc3Def, hc3Eval⟩ := anf_expand_1d 3
      (fun zB' ↦ SelectSwapQROM.anfCoeffs 2 (fun zC' ↦ R zB' zC') mC) zB
    rw [hF2Def mC, hc3Eval, split_pow3_7, SelectSwapQROM.monoEval_zero, mul_one]
    refine congrArg₂ (· + ·) (by rw [hc3Def, ← anf2DCoeffs_def])
      (Finset.sum_congr rfl fun uB _ ↦ ?_)
    rw [hc3Def, ← anf2DCoeffs_def, hαM]
  clear hF2Def
  rw [hF2Eval, split_pow2_3, SelectSwapQROM.monoEval_zero, mul_one, eB ⟨0, by decide⟩]
  refine congrArg₂ (· + ·) ?_ (Finset.sum_congr rfl fun uC _ ↦ ?_)
  · refine congrArg₂ (· + ·) rfl (Finset.sum_congr rfl fun uB _ ↦ ?_)
    rw [hαM]
  · rw [eB, hγM]
    have hz : (∑ uB : Fin 7,
        anf2DCoeffs R ⟨uB.val + 1, by omega⟩ ⟨uC.val + 1, by omega⟩ * α₀ uB) = 0 :=
      Finset.sum_eq_zero fun uB _ ↦ by rw [hBi uB uC, zero_mul]
    rw [hz, add_zero]

/-- Sequential `7`-step L-triple phase loop (`28 T`, `0 TOFF`, `1` clean ancilla `wAnc`) for
turnaround phase fixup. -/
def lStepLoop7 {Var : Type} {N L_ctx : ℕ} (v : Var)
    (P_slice : Fin L_ctx → Fin (2 ^ 3) → Fin (2 ^ 2) → ZMod 2)
    (rHotCtx : QRegister L_ctx N) (rAllB : QRegister 7 N) (rAllC : QRegister 3 N) (wAnc : Wire N)
    (hHB : rHotCtx.DisjointWires rAllB) (hHC : rHotCtx.DisjointWires rAllC)
    (hBC : rAllB.DisjointWires rAllC)
    (hAncH : ∀ c, wAnc ≠ rHotCtx c) (hAncB : ∀ j, wAnc ≠ rAllB j) (hAncC : ∀ k, wAnc ≠ rAllC k) :
    (s : ℕ) → s ≤ 7 → DynamicCircuit Var N
  | 0, _ => .identity
  | s + 1, hs =>
      let t : Fin 7 := ⟨s, hs⟩
      let j := (canonLeg2 t).1
      let k := (canonLeg2 t).2.1
      let jp := (canonLeg2 t).2.2.1
      let kp := (canonLeg2 t).2.2.2
      let msk := leg2Masks P_slice t
      .seq (lStepLoop7 v P_slice rHotCtx rAllB rAllC wAnc hHB hHC hBC hAncH hAncB hAncC s
          (Nat.le_of_lt hs))
        (lStepInPlaceDyn v rHotCtx (rAllB j) (rAllC k) wAnc (jp.map rAllB) (kp.map rAllC)
          msk.1 msk.2.1 msk.2.2
          (hBC.ne j k) (hAncB j).symm (hAncC k).symm
          (fun c ↦ hHB.ne c j) (fun c ↦ hHC.ne c k) hAncH
          (option_map_ne_of_ne rAllB jp wAnc hAncB)
          (option_map_ne_of_ne rAllC kp wAnc hAncC))

private theorem count_hotCtxPhaseLoop_toff_w3 {N M L_ctx : ℕ}
    (rHotCtx : QRegister L_ctx N) (rAll : QRegister M N)
    (hHotNotAll : ∀ (c : Fin L_ctx) (u : Fin M), rHotCtx c ≠ rAll u)
    (c0 : Fin L_ctx → ZMod 2) (cPos : Fin L_ctx → Fin M → ZMod 2)
    (n : ℕ) (hn : n ≤ L_ctx) :
    (MidReflCtxRetain.hotCtxPhaseLoop M L_ctx rHotCtx rAll hHotNotAll c0 cPos n hn).count .TOFF =
      0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [MidReflCtxRetain.hotCtxPhaseLoop, Circuit.count_seq,
      SelectSwapQROM.count_czMaskCircuit_toff, add_zero]
    rw [ih (Nat.le_of_succ_le hn), zero_add]
    split_ifs <;> simp [Circuit.Z, Circuit.single]

private theorem count_hotCtxPhaseLoop_t_w3 {N M L_ctx : ℕ}
    (rHotCtx : QRegister L_ctx N) (rAll : QRegister M N)
    (hHotNotAll : ∀ (c : Fin L_ctx) (u : Fin M), rHotCtx c ≠ rAll u)
    (c0 : Fin L_ctx → ZMod 2) (cPos : Fin L_ctx → Fin M → ZMod 2)
    (n : ℕ) (hn : n ≤ L_ctx) :
    (MidReflCtxRetain.hotCtxPhaseLoop M L_ctx rHotCtx rAll hHotNotAll c0 cPos n hn).count .T =
      0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [MidReflCtxRetain.hotCtxPhaseLoop, Circuit.count_seq,
      SelectSwapQROM.count_czMaskCircuit_t, add_zero]
    rw [ih (Nat.le_of_succ_le hn), zero_add]
    split_ifs <;> simp [Circuit.Z, Circuit.single]

/-- Per-slice `2D` cube for turnaround measurement outcome `m`. -/
def hotSlice2DCube {L_ctx outBits : ℕ} (F : Fin L_ctx → Fin (2 ^ 5) → Fin outBits → Bool)
    (m : Fin (2 ^ outBits)) (c : Fin L_ctx) (zB : Fin (2 ^ 3)) (zC : Fin (2 ^ 2)) : ZMod 2 :=
  MidReflCtxRetain.sliceParityFn 5 L_ctx outBits F m c (cubeAddr5 zB zC)

/-- Residual per-slice `2D` cube after subtracting `∑_{t : Fin 7} lin2Term`. -/
def hotRes2DCube {L_ctx outBits : ℕ} (F : Fin L_ctx → Fin (2 ^ 5) → Fin outBits → Bool)
    (m : Fin (2 ^ outBits)) (c : Fin L_ctx) (zB : Fin (2 ^ 3)) (zC : Fin (2 ^ 2)) : ZMod 2 :=
  let P_slice := hotSlice2DCube F m
  P_slice c zB zC + ∑ t : Fin 7,
    let msk := leg2Masks P_slice t
    lin2Term (msk.1 c) (msk.2.1 c) (msk.2.2 c) t zB zC

private theorem hotRes2DCube_def {L_ctx outBits : ℕ}
    (F : Fin L_ctx → Fin (2 ^ 5) → Fin outBits → Bool)
    (m : Fin (2 ^ outBits)) (c : Fin L_ctx) :
    hotRes2DCube F m c = fun zB zC ↦
      hotSlice2DCube F m c zB zC + ∑ t : Fin 7,
        lin2Term ((leg2Masks (hotSlice2DCube F m) t).1 c)
          ((leg2Masks (hotSlice2DCube F m) t).2.1 c)
          ((leg2Masks (hotSlice2DCube F m) t).2.2 c) t zB zC := rfl

attribute [irreducible] hotRes2DCube

/-- `0-T` residual Clifford circuit for turnaround unload: cancels `bg2Sum` via
`czBilinearCircuit 7 3`
and applies the `1`-block residual phases `hotRes2DCube` via `hotCtxPhaseLoop (7 + 3)`. -/
def hotResidualClifford {N L_ctx outBits : ℕ}
    (F : Fin L_ctx → Fin (2 ^ 5) → Fin outBits → Bool) (m : Fin (2 ^ outBits))
    (rHotCtx : QRegister L_ctx N) (rAllB : QRegister 7 N) (rAllC : QRegister 3 N)
    (hHB : rHotCtx.DisjointWires rAllB) (hHC : rHotCtx.DisjointWires rAllC)
    (hBC : rAllB.DisjointWires rAllC) : Circuit N :=
  let rAll10 : QRegister (7 + 3) N := rAllB.concat rAllC hBC
  have hHotDisj10 : rHotCtx.DisjointWires rAll10 :=
    QRegister.disjointWires_concat_right hBC hHB hHC
  let c0 (c : Fin L_ctx) : ZMod 2 :=
    anf2DCoeffs (hotRes2DCube F m c) ⟨0, by decide⟩ ⟨0, by decide⟩
  let cPos (c : Fin L_ctx) (u : Fin (7 + 3)) : ZMod 2 :=
    if hu : u.val < 7 then
      anf2DCoeffs (hotRes2DCube F m c) ⟨u.val + 1, by omega⟩ ⟨0, by decide⟩
    else
      anf2DCoeffs (hotRes2DCube F m c) ⟨0, by decide⟩ ⟨u.val - 7 + 1, by omega⟩
  .seq (czBilinearCircuit 7 3 rAllB rAllC hBC bg2Coeff)
    (MidReflCtxRetain.hotCtxPhaseLoop (7 + 3) L_ctx rHotCtx rAll10
      (fun c u ↦ hHotDisj10.ne c u) c0 cPos L_ctx le_rfl)

@[simp]
theorem count_hotResidualClifford_toff {N L_ctx outBits : ℕ}
    (F : Fin L_ctx → Fin (2 ^ 5) → Fin outBits → Bool) (m : Fin (2 ^ outBits))
    (rHotCtx : QRegister L_ctx N) (rAllB : QRegister 7 N) (rAllC : QRegister 3 N)
    (hHB : rHotCtx.DisjointWires rAllB) (hHC : rHotCtx.DisjointWires rAllC)
    (hBC : rAllB.DisjointWires rAllC) :
    (hotResidualClifford F m rHotCtx rAllB rAllC hHB hHC hBC).count .TOFF = 0 := by
  dsimp only [hotResidualClifford]
  rw [Circuit.count_seq, count_czBilinearCircuit_toff, count_hotCtxPhaseLoop_toff_w3, add_zero]

@[simp]
theorem count_hotResidualClifford_t {N L_ctx outBits : ℕ}
    (F : Fin L_ctx → Fin (2 ^ 5) → Fin outBits → Bool) (m : Fin (2 ^ outBits))
    (rHotCtx : QRegister L_ctx N) (rAllB : QRegister 7 N) (rAllC : QRegister 3 N)
    (hHB : rHotCtx.DisjointWires rAllB) (hHC : rHotCtx.DisjointWires rAllC)
    (hBC : rAllB.DisjointWires rAllC) :
    (hotResidualClifford F m rHotCtx rAllB rAllC hHB hHC hBC).count .T = 0 := by
  dsimp only [hotResidualClifford]
  rw [Circuit.count_seq, count_czBilinearCircuit_t, count_hotCtxPhaseLoop_t_w3, add_zero]

private theorem parityLinComb_sum_w3 {ι : Type*} (s : Finset ι) :
    ∀ (b : ℕ) (m : Fin (2 ^ b)) (a : ι → ZMod 2) (g : ι → Fin b → ZMod 2),
      MidReflCtxRetain.parityLinComb b m (fun j ↦ ∑ c ∈ s, a c * g c j) =
        ∑ c ∈ s, a c * MidReflCtxRetain.parityLinComb b m (g c)
  | 0, _, _, _ => by simp [MidReflCtxRetain.parityLinComb]
  | b + 1, m, a, g => by
      dsimp only [MidReflCtxRetain.parityLinComb]
      split_ifs with hm
      · exact parityLinComb_sum_w3 s b ⟨m.val, hm⟩ a
          (fun c j ↦ g c (Fin.castLE (Nat.le_succ b) j))
      · rw [parityLinComb_sum_w3 s b _ a (fun c j ↦ g c (Fin.castLE (Nat.le_succ b) j)),
          ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun c _ ↦ (mul_add _ _ _).symm

private theorem zmod2_if_beq_one_w3 (z : ZMod 2) :
    (if (z == 1) = true then (1 : ZMod 2) else 0) = z := by
  rcases SelectSwapQROM.bit_cases z with rfl | rfl <;> decide

private theorem zmod2_of_parityPhaseTable_w3 :
    ∀ (b : ℕ) (T : ℕ → (Fin b → Bool)) (m : Fin (2 ^ b)) (idx : ℕ),
      (if SelectSwapQROM.parityPhaseTable b T m idx then (1 : ZMod 2) else 0) =
        MidReflCtxRetain.parityLinComb b m (fun j ↦ if T idx j then 1 else 0)
  | 0, _, _, _ => rfl
  | b + 1, T, m, idx => by
      by_cases hm : m.val < 2 ^ b
      · simp only [SelectSwapQROM.parityPhaseTable, MidReflCtxRetain.parityLinComb,
          hm, ↓reduceDIte]
        exact zmod2_of_parityPhaseTable_w3 b
          (fun q j ↦ T q (Fin.castLE (Nat.le_succ b) j)) ⟨m.val, hm⟩ idx
      · simp only [SelectSwapQROM.parityPhaseTable, MidReflCtxRetain.parityLinComb,
          hm, ↓reduceDIte]
        rw [zmod2_ite_xor_w3, zmod2_of_parityPhaseTable_w3 b
          (fun q j ↦ T q (Fin.castLE (Nat.le_succ b) j))]

/-- Exact `ZMod 2` computational-basis phase exponent realized by `hotPhaseFixup12Dyn` on states
with clean `rScr6`. -/
def hotFixup12KetPhase {N L_ctx outBits : ℕ}
    (F : Fin L_ctx → Fin (2 ^ 5) → Fin outBits → Bool) (m : Fin (2 ^ outBits))
    (rIdx : QRegister 5 N) (rHotCtx : QRegister L_ctx N) (β : BitAssignment N) : ZMod 2 :=
  let zB : Fin (2 ^ 3) := (basisBits 3).symm (fun i ↦ β ((rIdx.slice 1 3 (by decide)) i))
  let zC : Fin (2 ^ 2) := (basisBits 2).symm (fun i ↦ β ((rIdx.compose c2In5Reg) i))
  let αB (uB : Fin 7) : ZMod 2 :=
    SelectSwapQROM.monoEval 3 (basisBits 3 zB) ⟨uB.val + 1, by omega⟩
  let αC (uC : Fin 3) : ZMod 2 :=
    SelectSwapQROM.monoEval 2 (basisBits 2 zC) ⟨uC.val + 1, by omega⟩
  (∑ t : Fin 7,
    let j := (canonLeg2 t).1
    let k := (canonLeg2 t).2.1
    let jp := (canonLeg2 t).2.2.1
    let kp := (canonLeg2 t).2.2.2
    let msk := leg2Masks (hotSlice2DCube F m) t
    (αB j + ∑ c : Fin L_ctx, msk.1 c * β (rHotCtx c)) *
      (αC k + ∑ c : Fin L_ctx, msk.2.1 c * β (rHotCtx c)) *
      ((∑ c : Fin L_ctx, msk.2.2 c * β (rHotCtx c)) + optMono3 zB jp + optMono2 zC kp)) +
  ((∑ uB : Fin 7, αB uB * ∑ uC : Fin 3, bg2Coeff uB uC * αC uC) +
   (∑ c : Fin L_ctx, β (rHotCtx c) *
     (anf2DCoeffs (hotRes2DCube F m c) ⟨0, by decide⟩ ⟨0, by decide⟩ +
      (∑ uB : Fin 7,
        anf2DCoeffs (hotRes2DCube F m c) ⟨uB.val + 1, by omega⟩ ⟨0, by decide⟩ * αB uB) +
      (∑ uC : Fin 3,
        anf2DCoeffs (hotRes2DCube F m c) ⟨0, by decide⟩ ⟨uC.val + 1, by omega⟩ * αC uC))))

private theorem predProj_mulVec_ket_w3 {N : ℕ} (H : BitAssignment N → Bool) (β : BitAssignment N) :
    (GroupUnary.predProj H).mulVec (SelectSwapQROM.ket β) =
      if H β = true then SelectSwapQROM.ket β else 0 := by
  dsimp [GroupUnary.predProj, SelectSwapQROM.ket, basisState]
  rw [Matrix.diagonal_mulVec_single, SelectSwapQROM.basisBits_symm]
  cases H β <;> simp

private theorem zeroProjOn_eq_predProj_w3 {N : ℕ} (S : Finset (Wire N)) :
    SelectSwapQROM.zeroProjOn S =
      GroupUnary.predProj (fun β ↦ decide (∀ w ∈ S, β w = 0)) := by
  ext i j
  simp only [SelectSwapQROM.zeroProjOn, GroupUnary.predProj, Matrix.diagonal_apply]
  by_cases hij : i = j
  · subst hij; by_cases h : ∀ w ∈ S, basisBits N i w = 0 <;> simp [h]
  · simp [hij]

private theorem zeroProjOn_comm_predProj_w3 {N : ℕ} (S : Finset (Wire N))
    (H : BitAssignment N → Bool) :
    SelectSwapQROM.zeroProjOn S * GroupUnary.predProj H =
      GroupUnary.predProj H * SelectSwapQROM.zeroProjOn S := by
  rw [zeroProjOn_eq_predProj_w3, GroupUnary.predProj_comm]

private theorem cleanPredProj_conjTranspose_w3 {N : ℕ} (S : Finset (Wire N))
    (H : BitAssignment N → Bool) :
    (Mobius126OneHot.cleanPredProj S H)ᴴ = Mobius126OneHot.cleanPredProj S H := by
  dsimp only [Mobius126OneHot.cleanPredProj]
  rw [conjTranspose_mul, GroupUnary.predProj_conjTranspose,
    SelectSwapQROM.zeroProjOn_conjTranspose, ← zeroProjOn_comm_predProj_w3]

theorem hotFixup12KetPhase_eq_of_oneHot {N L_ctx outBits : ℕ}
    (F : Fin L_ctx → Fin (2 ^ 5) → Fin outBits → Bool)
    (hVan30 : ∀ (c : Fin L_ctx) (k : Fin outBits),
      SelectSwapQROM.anfCoeffs 5
        (fun x ↦ if F c x k then (1 : ZMod 2) else 0) ⟨30, by decide⟩ = 0)
    (hVan31 : ∀ (c : Fin L_ctx) (k : Fin outBits),
      SelectSwapQROM.anfCoeffs 5
        (fun x ↦ if F c x k then (1 : ZMod 2) else 0) ⟨31, by decide⟩ = 0)
    (m : Fin (2 ^ outBits)) (rIdx : QRegister 5 N) (rHotCtx : QRegister L_ctx N)
    (hIdxHot : rIdx.DisjointWires rHotCtx) (β : BitAssignment N)
    (hHot : oneHotPred rHotCtx β = true) :
    hotFixup12KetPhase F m rIdx rHotCtx β =
      if SelectSwapQROM.parityPhaseTable outBits
          (MidReflCtxRetain.hotLinearBoolTable 5 L_ctx outBits F) m
          ((basisBits (5 + L_ctx)).symm (fun k ↦ β ((rIdx.concat rHotCtx hIdxHot) k))).val
        then 1 else 0 := by
  obtain ⟨c₀, hc₀⟩ := of_decide_eq_true hHot
  let zB : Fin (2 ^ 3) := (basisBits 3).symm (fun i ↦ β ((rIdx.slice 1 3 (by decide)) i))
  let zC : Fin (2 ^ 2) := (basisBits 2).symm (fun i ↦ β ((rIdx.compose c2In5Reg) i))
  have hStepOneHot (t : Fin 7) :
      (SelectSwapQROM.monoEval 3 (basisBits 3 zB) ⟨(canonLeg2 t).1.val + 1, by omega⟩ +
        ∑ c : Fin L_ctx, (leg2Masks (hotSlice2DCube F m) t).1 c * β (rHotCtx c)) *
      (SelectSwapQROM.monoEval 2 (basisBits 2 zC) ⟨(canonLeg2 t).2.1.val + 1, by omega⟩ +
        ∑ c : Fin L_ctx, (leg2Masks (hotSlice2DCube F m) t).2.1 c * β (rHotCtx c)) *
      ((∑ c : Fin L_ctx, (leg2Masks (hotSlice2DCube F m) t).2.2 c * β (rHotCtx c)) +
        optMono3 zB (canonLeg2 t).2.2.1 + optMono2 zC (canonLeg2 t).2.2.2) =
      lin2Term ((leg2Masks (hotSlice2DCube F m) t).1 c₀)
        ((leg2Masks (hotSlice2DCube F m) t).2.1 c₀)
        ((leg2Masks (hotSlice2DCube F m) t).2.2 c₀) t zB zC + bg2Cube t zB zC := by
    rw [sum_mul_oneHot _ c₀ hc₀, sum_mul_oneHot _ c₀ hc₀, sum_mul_oneHot _ c₀ hc₀]
    dsimp only [lin2Term]
    rw [add_assoc _ (bg2Cube t zB zC) (bg2Cube t zB zC), CharTwo.add_self_eq_zero, add_zero]
  have hBi (uB : Fin 7) (uC : Fin 3) :
      anf2DCoeffs (hotRes2DCube F m c₀) ⟨uB.val + 1, by omega⟩ ⟨uC.val + 1, by omega⟩ = 0 := by
    rw [hotRes2DCube_def, anf2DCoeffs_add, anf2DCoeffs_sum_fin 7]
    simp_rw [anf2DCoeffs_lin2Term_bilinear (hotSlice2DCube F m) c₀ _ uB uC]
    rw [← Finset.sum_mul, sum_stepCoverZMod2_eq uB uC]
    by_cases hEx : (uB.val = 6 ∧ uC.val = 1) ∨ (uB.val = 6 ∧ uC.val = 2)
    · rw [ite_eq_left hEx, zero_mul, add_zero]
      rcases hEx with ⟨hB6, hC1⟩ | ⟨hB6, hC2⟩
      · have hmB : (⟨uB.val + 1, by omega⟩ : Fin 8) = ⟨7, by decide⟩ := Fin.ext (by dsimp; omega)
        have hmC : (⟨uC.val + 1, by omega⟩ : Fin 4) = ⟨2, by decide⟩ := Fin.ext (by dsimp; omega)
        rw [hmB, hmC]
        change anf2DCoeffs (fun zB' zC' ↦
          MidReflCtxRetain.sliceParityFn 5 L_ctx outBits F m c₀ (cubeAddr5 zB' zC')) _ _ = 0
        rw [anf2DCoeffs_cubeAddr5_7_2]
        exact Tuned162ScheduledSympQrom21.anfCoeffs_sliceParityFn_of_vanish F m c₀
          ⟨30, by decide⟩ (hVan30 c₀)
      · have hmB : (⟨uB.val + 1, by omega⟩ : Fin 8) = ⟨7, by decide⟩ := Fin.ext (by dsimp; omega)
        have hmC : (⟨uC.val + 1, by omega⟩ : Fin 4) = ⟨3, by decide⟩ := Fin.ext (by dsimp; omega)
        rw [hmB, hmC]
        change anf2DCoeffs (fun zB' zC' ↦
          MidReflCtxRetain.sliceParityFn 5 L_ctx outBits F m c₀ (cubeAddr5 zB' zC')) _ _ = 0
        rw [anf2DCoeffs_cubeAddr5_7_3]
        exact Tuned162ScheduledSympQrom21.anfCoeffs_sliceParityFn_of_vanish F m c₀
          ⟨31, by decide⟩ (hVan31 c₀)
    · rw [ite_eq_right hEx, one_mul, CharTwo.add_self_eq_zero]
  have hResEval := anf2DCoeffs_eval_residual (hotRes2DCube F m c₀) hBi zB zC
  have hCliffHot :
      (∑ c : Fin L_ctx, β (rHotCtx c) *
        (anf2DCoeffs (hotRes2DCube F m c) ⟨0, by decide⟩ ⟨0, by decide⟩ +
         (∑ uB : Fin 7, anf2DCoeffs (hotRes2DCube F m c) ⟨uB.val + 1, by omega⟩ ⟨0, by decide⟩ *
           SelectSwapQROM.monoEval 3 (basisBits 3 zB) ⟨uB.val + 1, by omega⟩) +
         (∑ uC : Fin 3, anf2DCoeffs (hotRes2DCube F m c) ⟨0, by decide⟩ ⟨uC.val + 1, by omega⟩ *
           SelectSwapQROM.monoEval 2 (basisBits 2 zC) ⟨uC.val + 1, by omega⟩))) =
      hotRes2DCube F m c₀ zB zC := by
    rw [Finset.sum_eq_single c₀]
    · rw [hc₀ c₀, ite_eq_left rfl, one_mul, ← hResEval]
    · intro c _ hne; rw [hc₀ c, ite_eq_right hne, zero_mul]
    · intro h; exact absurd (Finset.mem_univ c₀) h
  dsimp only [hotFixup12KetPhase]
  refine Eq.trans (congrArg₂ (· + ·)
    (Finset.sum_congr rfl fun t _ ↦ Eq.trans rfl (hStepOneHot t)) rfl) ?_
  rw [Finset.sum_add_distrib, ← bg2Sum_eq_bilinear zB zC, hCliffHot, hotRes2DCube_def]
  dsimp only [bg2Sum]
  have hR (s bg p : ZMod 2) : (s + bg) + (bg + (p + s)) = (bg + bg) + (s + s) + p := by ring
  rw [hR, CharTwo.add_self_eq_zero, CharTwo.add_self_eq_zero, add_zero, zero_add]
  dsimp only [hotSlice2DCube]
  have hCube : cubeAddr5 zB zC = (basisBits 5).symm (fun q ↦ β (rIdx q)) :=
    (symm5_eq_cubeAddr5 (fun q ↦ β (rIdx q))).symm
  rw [hCube]
  let a := (basisBits (5 + L_ctx)).symm (fun k ↦ β ((rIdx.concat rHotCtx hIdxHot) k))
  let x := (basisBits 5).symm (fun q ↦ β (rIdx q))
  have haLo : (basisBits 5).symm (fun i ↦ basisBits (5 + L_ctx) a (Fin.castAdd L_ctx i)) =
      x := by
    congr 1; funext i; dsimp only [a]
    rw [SelectSwapQROM.basisBits_symm, rIdx.concat_apply_left rHotCtx hIdxHot i]
  have haHi (c : Fin L_ctx) : basisBits (5 + L_ctx) a (Fin.natAdd 5 c) = β (rHotCtx c) := by
    dsimp only [a]; rw [SelectSwapQROM.basisBits_symm, rIdx.concat_apply_right rHotCtx hIdxHot c]
  rw [zmod2_of_parityPhaseTable_w3]
  change _ = MidReflCtxRetain.parityLinComb outBits m
    (fun k ↦ if MidReflCtxRetain.hotLinearBoolTable 5 L_ctx outBits F a.val k then 1 else 0)
  have hTbl (k : Fin outBits) :
      (if MidReflCtxRetain.hotLinearBoolTable 5 L_ctx outBits F a.val k then
        (1 : ZMod 2) else 0) =
        ∑ c : Fin L_ctx,
          basisBits (5 + L_ctx) a (Fin.natAdd 5 c) * (if F c x k then 1 else 0) := by
    dsimp only [MidReflCtxRetain.hotLinearBoolTable]
    have haLt : a.val < 2 ^ (5 + L_ctx) := a.isLt
    have haFin : (⟨a.val, haLt⟩ : Fin (2 ^ (5 + L_ctx))) = a := Fin.ext rfl
    simp only [haLt, ↓reduceDIte, haFin, haLo]
    exact zmod2_if_beq_one_w3 _
  simp_rw [hTbl]
  rw [parityLinComb_sum_w3 Finset.univ outBits m
    (fun c ↦ basisBits (5 + L_ctx) a (Fin.natAdd 5 c))
    (fun c k ↦ if F c x k then 1 else 0)]
  rw [Finset.sum_eq_single c₀]
  · rw [haHi c₀, hc₀ c₀, ite_eq_left rfl, one_mul]; rfl
  · intro c _ hne; rw [haHi c, hc₀ c, ite_eq_right hne, zero_mul]
  · intro h; exact absurd (Finset.mem_univ c₀) h

/-! ### Section 4B: `measureXResetAndBranch` One-Hot Congruence, Direct `0 ≤ sScr` Unload,
& Turnkey `withMobiusOneHot126Dyn` / `withMobiusOneHotDyn` Congruence Bridges -/

private theorem wp_measureXReset1AndBranch_apply_w3 {Var : Type} [Finite Var] [DecidableEq Var]
    {N : ℕ} [NeZero (2 ^ N)] (v : Var) (w : Wire N) (k₀ k₁ : DynamicCircuit Var N)
    (Θ : QCAssertion Var (2 ^ N)) (σ : Store Var) :
    let P₀ := (QRegister.singleton w).basisOutcomeProjector 0
    let P₁ := (QRegister.singleton w).basisOutcomeProjector 1
    let L₀ := P₀ * (Circuit.H w).eval.1
    let L₁ := (Circuit.X w).eval.1 * P₁ * (Circuit.H w).eval.1
    (wp (SelectSwapQROM.measureXReset1AndBranch v w k₀ k₁).compile Θ σ).1 =
      (wp k₀.compile Θ (Function.update σ v 0)).1.conj L₀ᴴ +
        (wp k₁.compile Θ (Function.update σ v 1)).1.conj L₁ᴴ := by
  cases nonempty_fintype Var
  intro P₀ P₁ L₀ L₁
  let U := Circuit.H w
  let Xw := Circuit.X w
  have hmeas_apply :
      (wp (.qSeq (QProg.measureRegister v (QRegister.singleton w))
          (qcQIf (fun σ'' ↦ σ'' v) (.qSeq Xw.compile k₁.compile) k₀.compile)) Θ σ).1 =
        (wp k₀.compile Θ (Function.update σ v 0)).1.conj P₀ᴴ +
          ((wp k₁.compile Θ (Function.update σ v 1)).1.conj Xw.eval.1ᴴ).conj P₁ᴴ := by
    have hsubst0 : σ.subst v 0 = Function.update σ v 0 := by
      funext y; simp [Store.subst, Function.update]
    have hsubst1 : σ.subst v 1 = Function.update σ v 1 := by
      funext y; simp [Store.subst, Function.update]
    simp only [wp_qSeq, wp_qIf, qc_wp_qMeasure', QProg.measureRegister, qc_wp_qMeasure_apply,
      qc_qMeasure_obs_map_coe,
      QCAssertion.subst_apply]
    change ∑ o : Fin 2, _ = _
    rw [Fin.sum_univ_two]
    simp [qc_qMeasure_outcome_herm_eq_conj, hsubst0, hsubst1,
      qcWpQAssign, qcQAssignObsMap, Observable.conj_coe, Unitary.coe_star,
      Matrix.star_eq_conjTranspose, QRegister.computationalBasisMeasurement_apply, P₀, P₁, Xw]
  change (wp U.compile
      (wp (.qSeq (QProg.measureRegister v (QRegister.singleton w))
        (qcQIf (fun σ'' ↦ σ'' v) (.qSeq Xw.compile k₁.compile) k₀.compile)) Θ) σ).1 = _
  rw [DynamicCircuit.qc_wp_circuit_compile]
  simp only [qcWpQAssign, qcQAssignObsMap, Observable.conj_coe, Unitary.coe_star,
    Matrix.star_eq_conjTranspose]
  rw [hmeas_apply, map_add, conj_conj, conj_conj, conj_conj]
  dsimp only [L₀, L₁, U, Xw]
  simp only [Matrix.mul_assoc, conjTranspose_mul]

private theorem cleanPredProj_mulVec_ket_w3 {N : ℕ} (S : Finset (Wire N))
    (H : BitAssignment N → Bool) (β : BitAssignment N) :
    (Mobius126OneHot.cleanPredProj S H).mulVec (SelectSwapQROM.ket β) =
      if H β = true ∧ ∀ x ∈ S, β x = 0 then SelectSwapQROM.ket β else 0 := by
  dsimp only [Mobius126OneHot.cleanPredProj]
  rw [← Matrix.mulVec_mulVec, predProj_mulVec_ket_w3]
  by_cases hH : H β = true
  · rw [ite_eq_left hH, SelectSwapQROM.zeroProjOn_mulVec_ket]
    by_cases hS : ∀ x ∈ S, β x = 0 <;> simp [hH, hS]
  · simp [hH]

/-- Classical-store `v`-invariance of `measureXResetAndBranch` whenever all leaf continuations are
`v`-invariant. -/
theorem wp_measureXResetAndBranch_update_self {Var : Type} [Finite Var] [DecidableEq Var]
    {N : ℕ} [NeZero (2 ^ N)] (v : Var) (b : ℕ) (rMeas : QRegister b N)
    (k : Fin (2 ^ b) → DynamicCircuit Var N)
    (hk : ∀ (m : Fin (2 ^ b)) (Θ : QCAssertion Var (2 ^ N)),
      (∀ σ val, Θ (Function.update σ v val) = Θ σ) →
      ∀ σ val, wp (k m).compile Θ (Function.update σ v val) = wp (k m).compile Θ σ)
    (Θ : QCAssertion Var (2 ^ N)) (hΘ : ∀ σ val, Θ (Function.update σ v val) = Θ σ)
    (σ : Store Var) (val : ℤ) :
    wp (SelectSwapQROM.measureXResetAndBranch v b rMeas k).compile Θ
      (Function.update σ v val) =
    wp (SelectSwapQROM.measureXResetAndBranch v b rMeas k).compile Θ σ := by
  induction b with
  | zero =>
    simp only [SelectSwapQROM.measureXResetAndBranch]
    exact hk _ Θ hΘ σ val
  | succ b _ =>
    apply Subtype.ext
    simp only [SelectSwapQROM.measureXResetAndBranch]
    rw [wp_measureXReset1AndBranch_apply_w3, wp_measureXReset1AndBranch_apply_w3,
      Function.update_idem, Function.update_idem]

private theorem embed_xorLoadUnitary_zero_width_w3 {N nAddr L : ℕ}
    (rAddr : QRegister nAddr N) (rOut : QRegister 0 N) (hDisj : rAddr.DisjointWires rOut)
    (T : ℕ → (Fin 0 → Bool)) :
    (rAddr.concat rOut hDisj).embedUnitary (SelectSwapQROM.xorLoadUnitary nAddr 0 L T) = 1 := by
  apply Subtype.ext; apply SelectSwapQROM.matrix_ext_ket; intro β
  simp only [Submonoid.coe_one, Matrix.one_mulVec]
  rw [SelectSwapQROM.embed_xorLoadUnitary_mulVec_ket]; congr 1

private theorem embed_xorLoadUnitary_split_last_w3 {N nAddr b L : ℕ}
    (rAddr : QRegister nAddr N) (rMeas : QRegister (b + 1) N)
    (hDisj : rAddr.DisjointWires rMeas) (T : ℕ → (Fin (b + 1) → Bool)) :
    let iLast : Fin (b + 1) := ⟨b, Nat.lt_succ_self b⟩
    let rLo := rMeas.subregister (Fin.castLEEmb (Nat.le_succ b))
    let hAddrLo : rAddr.DisjointWires rLo := hDisj.compose_right ⟨Fin.castLEEmb (Nat.le_succ b)⟩
    let hAddrSing : rAddr.DisjointWires (QRegister.singleton (rMeas iLast)) :=
      QRegister.disjoint_iff.mpr fun i j ↦ by fin_cases j; exact hDisj.ne i iLast
    (rAddr.concat rMeas hDisj).embedUnitary (SelectSwapQROM.xorLoadUnitary nAddr (b + 1) L T) =
      ((rAddr.concat rLo hAddrLo).embedUnitary
        (SelectSwapQROM.xorLoadUnitary nAddr b L
          (fun idx j ↦ T idx (Fin.castLE (Nat.le_succ b) j)))) *
      ((rAddr.concat (QRegister.singleton (rMeas iLast)) hAddrSing).embedUnitary
        (SelectSwapQROM.xorLoadUnitary nAddr 1 L (fun idx _ ↦ T idx iLast))) := by
  intro iLast rLo hAddrLo hAddrSing
  have hwNotLo : rMeas iLast ∉ rLo.image := fun hm ↦ by
    obtain ⟨j, hj⟩ := (QRegister.mem_image rLo _).mp hm
    exact Nat.ne_of_lt j.isLt (congrArg Fin.val (rMeas.wires.injective hj))
  apply Subtype.ext; apply SelectSwapQROM.matrix_ext_ket; intro β
  simp only [Submonoid.coe_mul, ← Matrix.mulVec_mulVec,
    SelectSwapQROM.embed_xorLoadUnitary_mulVec_ket]
  let idx := (basisBits nAddr).symm (fun i ↦ β (rAddr i))
  have hIdxEq : (basisBits nAddr).symm (fun i ↦
      SelectSwapQROM.xorRegBits β (QRegister.singleton (rMeas iLast))
        (fun _ ↦ decide (idx.val < L ∧ T idx.val iLast)) (rAddr i)) = idx := by
    congr 1; funext i
    exact SelectSwapQROM.xorRegBits_apply_of_not_mem _ _ _ _ (hAddrSing.apply_not_mem_right i)
  change SelectSwapQROM.ket (SelectSwapQROM.xorRegBits β rMeas
      (fun j ↦ decide (idx.val < L ∧ T idx.val j))) =
    SelectSwapQROM.ket (SelectSwapQROM.xorRegBits
      (SelectSwapQROM.xorRegBits β (QRegister.singleton (rMeas iLast))
        (fun _ ↦ decide (idx.val < L ∧ T idx.val iLast))) rLo _)
  rw [hIdxEq]; congr 1; funext q
  by_cases hq : q ∈ rMeas.image
  · obtain ⟨j, rfl⟩ := (QRegister.mem_image rMeas q).mp hq
    by_cases hj : j.val < b
    · let jLo : Fin b := ⟨j.val, hj⟩
      have hrLo : rLo jLo = rMeas j := congrArg rMeas (Fin.ext rfl)
      have hneW : rMeas j ≠ rMeas iLast := fun h ↦
        Nat.ne_of_lt hj (congrArg Fin.val (rMeas.wires.injective h))
      have hNotSing : rMeas j ∉ (QRegister.singleton (rMeas iLast)).image := by simp [hneW]
      rw [SelectSwapQROM.xorRegBits_apply_reg, ← hrLo, SelectSwapQROM.xorRegBits_apply_reg,
        hrLo, SelectSwapQROM.xorRegBits_apply_of_not_mem _ _ _ _ hNotSing]
      have hCast : Fin.castLE (Nat.le_succ b) jLo = j := Fin.ext rfl
      rw [hCast]
    · have hjEq : j = iLast := Fin.ext (by dsimp [iLast]; omega)
      subst hjEq
      rw [SelectSwapQROM.xorRegBits_apply_of_not_mem _ rLo _ _ hwNotLo,
        SelectSwapQROM.xorRegBits_apply_reg]
      change _ = SelectSwapQROM.xorRegBits β (QRegister.singleton (rMeas iLast)) _
        (QRegister.singleton (rMeas iLast) 0)
      rw [SelectSwapQROM.xorRegBits_apply_reg, QRegister.singleton_apply]
  · have hNotLo : q ∉ rLo.image := fun hm ↦ hq ((rMeas.image_compose_subset _) hm)
    have hNotSing : q ∉ (QRegister.singleton (rMeas iLast)).image := fun hm ↦ by
      simp only [QRegister.image_singleton, Finset.mem_singleton] at hm
      exact hq (hm ▸ (QRegister.mem_image rMeas _).mpr ⟨iLast, rfl⟩)
    rw [SelectSwapQROM.xorRegBits_apply_of_not_mem _ rMeas _ q hq,
      SelectSwapQROM.xorRegBits_apply_of_not_mem _ rLo _ q hNotLo,
      SelectSwapQROM.xorRegBits_apply_of_not_mem _ _ _ q hNotSing]

private theorem wp_qAssign_one_w3 {Var : Type} [Fintype Var] {d : ℕ}
    (Θ : QCAssertion Var d) : qcWpQAssign (1 : Unitary d) Θ = Θ := by
  funext σ; apply Subtype.ext; simp [qcWpQAssign]

private theorem diagPhaseUnitary_false_w3 (nIdx L : ℕ) :
    SelectSwapQROM.diagPhaseUnitary nIdx L (fun _ ↦ false) = 1 := by
  apply Subtype.ext; ext i j
  by_cases hij : i = j
  · subst hij; simp [SelectSwapQROM.diagPhaseUnitary]
  · simp [SelectSwapQROM.diagPhaseUnitary, hij]

private theorem diagPhaseUnitary_xor_w3 (nIdx L : ℕ) (P₁ P₂ : ℕ → Bool) :
    SelectSwapQROM.diagPhaseUnitary nIdx L (fun idx ↦ xor (P₁ idx) (P₂ idx)) =
      SelectSwapQROM.diagPhaseUnitary nIdx L P₁ *
        SelectSwapQROM.diagPhaseUnitary nIdx L P₂ := by
  apply Subtype.ext
  simp only [SelectSwapQROM.diagPhaseUnitary, Submonoid.coe_mul, Matrix.diagonal_mul_diagonal]
  congr 1; funext idx
  by_cases hL : idx.val < L
  · simp only [hL, true_and]; cases P₁ idx.val <;> cases P₂ idx.val <;> simp
  · simp [hL]

/-- Structural `wp` unload theorem on `cleanPredProj S H` (`rMeas.image ⊆ S`): proves that
`measureXResetAndBranch` unloads `xorLoadUnitary nAddr b L T` into `U_base` whenever leaf `k m`
matches `U_base * rAddr.embedUnitary (diagPhaseUnitary ... m)` on `cleanPredProj S H` (valid with
`0` external scratch wires whenever `rMeas` itself supplies the leaf scratch!). -/
theorem wp_measureXResetAndBranch_unload_cleanPredProj {Var : Type} [Fintype Var] [DecidableEq Var]
    {N nAddr : ℕ} [NeZero (2 ^ N)] (v : Var) (S : Finset (Wire N))
    (H : BitAssignment N → Bool) (b L : ℕ) (T : ℕ → (Fin b → Bool))
    (rAddr : QRegister nAddr N) (rMeas : QRegister b N)
    (hAddrMeas : rAddr.DisjointWires rMeas) (hMeasSubS : rMeas.image ⊆ S)
    (hHMeas : ∀ q ∈ rMeas.image, ∀ (β : BitAssignment N) (val : ZMod 2),
      H (Function.update β q val) = H β)
    (U_base : Unitary (2 ^ N))
    (k : Fin (2 ^ b) → DynamicCircuit Var N)
    (hk : ∀ (m : Fin (2 ^ b)) (Θ : QCAssertion Var (2 ^ N)),
      (∀ σ val, Θ (Function.update σ v val) = Θ σ) →
      ∀ σ : Store Var,
        ((wp (k m).compile Θ σ).1).conj (Mobius126OneHot.cleanPredProj S H) =
        ((qcWpQAssign (U_base * rAddr.embedUnitary
          (SelectSwapQROM.diagPhaseUnitary nAddr L
            (SelectSwapQROM.parityPhaseTable b T m))) Θ σ).1).conj
          (Mobius126OneHot.cleanPredProj S H))
    (Θ : QCAssertion Var (2 ^ N)) (hΘ : ∀ σ val, Θ (Function.update σ v val) = Θ σ)
    (σ : Store Var) :
    ((qcWpQAssign ((rAddr.concat rMeas hAddrMeas).embedUnitary
        (SelectSwapQROM.xorLoadUnitary nAddr b L T))
      (wp (SelectSwapQROM.measureXResetAndBranch v b rMeas k).compile Θ) σ).1).conj
        (Mobius126OneHot.cleanPredProj S H) =
    ((qcWpQAssign U_base Θ σ).1).conj (Mobius126OneHot.cleanPredProj S H) := by
  induction b generalizing U_base σ with
  | zero =>
    have hP0 : SelectSwapQROM.parityPhaseTable 0 T ⟨0, by simp⟩ = fun _ ↦ false := rfl
    have hLeaf := hk ⟨0, by simp⟩ Θ hΘ σ
    rw [hP0, diagPhaseUnitary_false_w3, QRegister.embedUnitary_one, mul_one] at hLeaf
    simp only [SelectSwapQROM.measureXResetAndBranch]
    rw [embed_xorLoadUnitary_zero_width_w3, wp_qAssign_one_w3]
    exact hLeaf
  | succ b ih =>
    let iLast : Fin (b + 1) := ⟨b, Nat.lt_succ_self b⟩
    let w := rMeas iLast
    let rLo := rMeas.subregister (Fin.castLEEmb (Nat.le_succ b))
    let T_lo : ℕ → (Fin b → Bool) := fun idx j ↦ T idx (Fin.castLE (Nat.le_succ b) j)
    let T_last : ℕ → (Fin 1 → Bool) := fun idx _ ↦ T idx iLast
    let P_last : ℕ → Bool := fun idx ↦ T idx iLast
    let D_last := rAddr.embedUnitary (SelectSwapQROM.diagPhaseUnitary nAddr L P_last)
    have hwMeas : w ∈ rMeas.image := (QRegister.mem_image rMeas w).mpr ⟨iLast, rfl⟩
    have hwS : w ∈ S := hMeasSubS hwMeas
    have hLoSub : rLo.image ⊆ rMeas.image := rMeas.image_compose_subset _
    have hAddrLo : rAddr.DisjointWires rLo :=
      hAddrMeas.compose_right ⟨Fin.castLEEmb (Nat.le_succ b)⟩
    have hAddrSing : rAddr.DisjointWires (QRegister.singleton w) :=
      QRegister.disjoint_iff.mpr fun i j ↦ by fin_cases j; exact hAddrMeas.ne i iLast
    have hLoSing : rLo.DisjointWires (QRegister.singleton w) :=
      QRegister.disjoint_iff.mpr fun j q hEq ↦ by
        fin_cases q
        exact Nat.ne_of_lt j.isLt (congrArg Fin.val (rMeas.wires.injective hEq))
    have hCombSing : (rAddr.concat rLo hAddrLo).DisjointWires (QRegister.singleton w) :=
      QRegister.disjointWires_concat_left hAddrLo hAddrSing hLoSing
    let W_lo := (rAddr.concat rLo hAddrLo).embedUnitary
      (SelectSwapQROM.xorLoadUnitary nAddr b L T_lo)
    let W_w := (rAddr.concat (QRegister.singleton w) hAddrSing).embedUnitary
      (SelectSwapQROM.xorLoadUnitary nAddr 1 L T_last)
    let P₀ := (QRegister.singleton w).basisOutcomeProjector 0
    let P₁ := (QRegister.singleton w).basisOutcomeProjector 1
    let L₀ := P₀ * (Circuit.H w).eval.1
    let L₁ := (Circuit.X w).eval.1 * P₁ * (Circuit.H w).eval.1
    have hSingComm (M : Operator 2) :
        ((QRegister.singleton w).embedMatrix M) * W_lo.1 =
          W_lo.1 * ((QRegister.singleton w).embedMatrix M) :=
      QRegister.embedMatrix_comm_of_disjoint (QRegister.singleton w) (rAddr.concat rLo hAddrLo)
        (QRegister.disjoint_comm.mp hCombSing) M _
    have hCommH : (Circuit.H w).eval.1 * W_lo.1 = W_lo.1 * (Circuit.H w).eval.1 :=
      hSingComm PrimitiveGate.H.eval.1
    have hCommX : (Circuit.X w).eval.1 * W_lo.1 = W_lo.1 * (Circuit.X w).eval.1 :=
      hSingComm PrimitiveGate.X.eval.1
    have hCommP₀ : P₀ * W_lo.1 = W_lo.1 * P₀ := hSingComm _
    have hCommP₁ : P₁ * W_lo.1 = W_lo.1 * P₁ := hSingComm _
    have hL₀Wlo : W_lo.1ᴴ * L₀ᴴ = L₀ᴴ * W_lo.1ᴴ := by
      have h : L₀ * W_lo.1 = W_lo.1 * L₀ := by
        dsimp only [L₀]
        rw [Matrix.mul_assoc, hCommH, ← Matrix.mul_assoc, hCommP₀, Matrix.mul_assoc]
      simpa only [conjTranspose_mul] using congrArg conjTranspose h
    have hL₁Wlo : W_lo.1ᴴ * L₁ᴴ = L₁ᴴ * W_lo.1ᴴ := by
      have h : L₁ * W_lo.1 = W_lo.1 * L₁ := by
        dsimp only [L₁]
        calc (Circuit.X w).eval.1 * P₁ * (Circuit.H w).eval.1 * W_lo.1
            = (Circuit.X w).eval.1 * P₁ * ((Circuit.H w).eval.1 * W_lo.1) := by
                simp only [Matrix.mul_assoc]
          _ = (Circuit.X w).eval.1 * (P₁ * W_lo.1) * (Circuit.H w).eval.1 := by
                rw [hCommH]; simp only [Matrix.mul_assoc]
          _ = ((Circuit.X w).eval.1 * W_lo.1) * P₁ * (Circuit.H w).eval.1 := by
                rw [hCommP₁]; simp only [Matrix.mul_assoc]
          _ = W_lo.1 * ((Circuit.X w).eval.1 * P₁ * (Circuit.H w).eval.1) := by
                rw [hCommX]; simp only [Matrix.mul_assoc]
      simpa only [conjTranspose_mul] using congrArg conjTranspose h
    let bitFn (β : BitAssignment N) : Bool :=
      decide (((basisBits nAddr).symm (fun i ↦ β (rAddr i))).val < L ∧
        P_last ((basisBits nAddr).symm (fun i ↦ β (rAddr i))).val)
    have hWwKet (β : BitAssignment N) :
        W_w.1.mulVec (SelectSwapQROM.ket β) =
          SelectSwapQROM.ket (Function.update β w (β w + if bitFn β then 1 else 0)) := by
      dsimp only [W_w]; rw [SelectSwapQROM.embed_xorLoadUnitary_mulVec_ket]
      congr 1; funext x
      by_cases hx : x = w
      · subst hx
        change SelectSwapQROM.xorRegBits β (QRegister.singleton w) _
          (QRegister.singleton w 0) = _
        rw [SelectSwapQROM.xorRegBits_apply_reg, QRegister.singleton_apply, Function.update_self]
      · have hxNot : x ∉ (QRegister.singleton w).image := by simp [hx]
        rw [SelectSwapQROM.xorRegBits_apply_of_not_mem _ _ _ x hxNot, Function.update_of_ne hx]
    have hDwKet (β : BitAssignment N) :
        D_last.1.mulVec (SelectSwapQROM.ket β) =
          (if bitFn β then (-1 : ℂ) else 1) • SelectSwapQROM.ket β := by
      dsimp only [D_last]; rw [SelectSwapQROM.embed_diagPhaseUnitary_mulVec_ket]
      congr 1; simp only [bitFn, decide_eq_true_eq]
    have hDwComm : D_last.1 * Mobius126OneHot.cleanPredProj S H =
        Mobius126OneHot.cleanPredProj S H * D_last.1 := by
      apply SelectSwapQROM.matrix_ext_ket; intro β
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, cleanPredProj_mulVec_ket_w3]
      by_cases hβ : H β = true ∧ ∀ x ∈ S, β x = 0
      · rw [ite_eq_left hβ, hDwKet, Matrix.mulVec_smul, cleanPredProj_mulVec_ket_w3,
          ite_eq_left hβ]
      · rw [ite_eq_right hβ, Matrix.mulVec_zero, hDwKet, Matrix.mulVec_smul,
          cleanPredProj_mulVec_ket_w3, ite_eq_right hβ, smul_zero]
    have hKraus0 : L₀ * W_w.1 * Mobius126OneHot.cleanPredProj S H =
        SelectSwapQROM.sqrtHalf • Mobius126OneHot.cleanPredProj S H := by
      apply SelectSwapQROM.matrix_ext_ket; intro β
      simp only [L₀, P₀, ← Matrix.mulVec_mulVec, Matrix.smul_mulVec, cleanPredProj_mulVec_ket_w3]
      by_cases hβ : H β = true ∧ ∀ x ∈ S, β x = 0
      · have hβw : β w = 0 := hβ.2 w hwS
        have hupd0 : Function.update β w 0 = β := by rw [← hβw]; exact Function.update_eq_self w β
        have hupd1 : Function.update β w 1 w ≠ 0 := by simp
        rw [ite_eq_left hβ, hWwKet, hβw, zero_add, SelectSwapQROM.ket_H, Matrix.mulVec_smul,
          Matrix.mulVec_add, Matrix.mulVec_smul, Function.update_idem, Function.update_idem,
          Function.update_self, SelectSwapQROM.singleton_projector_zero_mulVec_ket,
          SelectSwapQROM.singleton_projector_zero_mulVec_ket, hupd0, ite_eq_left hβw,
          ite_eq_right hupd1, smul_zero, add_zero]
      · simp [hβ]
    have hKraus1 : L₁ * W_w.1 * Mobius126OneHot.cleanPredProj S H =
        SelectSwapQROM.sqrtHalf • (Mobius126OneHot.cleanPredProj S H * D_last.1) := by
      rw [← hDwComm]
      apply SelectSwapQROM.matrix_ext_ket; intro β
      simp only [L₁, P₁, ← Matrix.mulVec_mulVec, Matrix.smul_mulVec, cleanPredProj_mulVec_ket_w3]
      by_cases hβ : H β = true ∧ ∀ x ∈ S, β x = 0
      · have hβw : β w = 0 := hβ.2 w hwS
        have h01 : ((0 : ZMod 2) = 1) = False := by decide
        have hupd0 : Function.update β w 0 = β := by rw [← hβw]; exact Function.update_eq_self w β
        rw [ite_eq_left hβ, hWwKet, hβw, zero_add, SelectSwapQROM.ket_H]
        simp only [Matrix.mulVec_smul, Matrix.mulVec_add, Function.update_idem,
          SelectSwapQROM.singleton_projector_one_mulVec_ket, Function.update_self, h01,
          ↓reduceIte, zero_add, SelectSwapQROM.ket_X, SelectSwapQROM.one_add_one_zmod2]
        rw [hupd0, hDwKet β]
        cases bitFn β <;> simp [SelectSwapQROM.bitSign]
      · simp [hβ]
    have hKraus0Adj : Mobius126OneHot.cleanPredProj S H * W_w.1ᴴ * L₀ᴴ =
        SelectSwapQROM.sqrtHalf • Mobius126OneHot.cleanPredProj S H := by
      simpa only [conjTranspose_mul, conjTranspose_smul, SelectSwapQROM.star_sqrtHalf,
        cleanPredProj_conjTranspose_w3, ← Matrix.mul_assoc] using congrArg conjTranspose hKraus0
    have hKraus1Adj : Mobius126OneHot.cleanPredProj S H * W_w.1ᴴ * L₁ᴴ =
        SelectSwapQROM.sqrtHalf • (D_last.1ᴴ * Mobius126OneHot.cleanPredProj S H) := by
      simpa only [conjTranspose_mul, conjTranspose_smul, SelectSwapQROM.star_sqrtHalf,
        cleanPredProj_conjTranspose_w3, ← Matrix.mul_assoc] using congrArg conjTranspose hKraus1
    have hDwAdjComm : D_last.1ᴴ * Mobius126OneHot.cleanPredProj S H =
        Mobius126OneHot.cleanPredProj S H * D_last.1ᴴ := by
      simpa only [conjTranspose_mul, cleanPredProj_conjTranspose_w3] using
        congrArg conjTranspose hDwComm.symm
    have hDwAdjSq : D_last.1ᴴ * D_last.1ᴴ = 1 := by
      have hSq : D_last * D_last = 1 := by
        dsimp only [D_last]
        rw [← QRegister.embedUnitary_mul, SelectSwapQROM.diagPhaseUnitary_mul_self,
          QRegister.embedUnitary_one]
      simpa only [Submonoid.coe_mul, Submonoid.coe_one, conjTranspose_mul, conjTranspose_one] using
        congrArg (fun u : Unitary (2 ^ N) ↦ u.1ᴴ) hSq
    let k₀ : Fin (2 ^ b) → DynamicCircuit Var N :=
      fun mLo ↦ k ⟨mLo.val, by have := mLo.isLt; rw [pow_succ']; omega⟩
    let k₁ : Fin (2 ^ b) → DynamicCircuit Var N :=
      fun mLo ↦ k ⟨2 ^ b + mLo.val, by have := mLo.isLt; rw [pow_succ']; omega⟩
    have hB₀ := ih T_lo rLo hAddrLo (hLoSub.trans hMeasSubS)
      (fun q hq ↦ hHMeas q (hLoSub hq)) U_base k₀
      (fun mLo Ψ hΨ τ ↦ by
        have hPar : SelectSwapQROM.parityPhaseTable (b + 1) T
            ⟨mLo.val, by have := mLo.isLt; rw [pow_succ']; omega⟩ =
            SelectSwapQROM.parityPhaseTable b T_lo mLo := by
          funext idx; dsimp only [SelectSwapQROM.parityPhaseTable]; exact dite_eq_left mLo.isLt
        dsimp only [k₀]
        rw [← hPar]
        exact hk _ Ψ hΨ τ)
      (Function.update σ v 0)
    have hB₁ := ih T_lo rLo hAddrLo (hLoSub.trans hMeasSubS)
      (fun q hq ↦ hHMeas q (hLoSub hq)) (U_base * D_last) k₁
      (fun mLo Ψ hΨ τ ↦ by
        have hNotLt : ¬(2 ^ b + mLo.val < 2 ^ b) := by omega
        have hPar : SelectSwapQROM.parityPhaseTable (b + 1) T
            ⟨2 ^ b + mLo.val, by have := mLo.isLt; rw [pow_succ']; omega⟩ =
            fun idx ↦ xor (P_last idx) (SelectSwapQROM.parityPhaseTable b T_lo mLo idx) := by
          funext idx; dsimp only [SelectSwapQROM.parityPhaseTable]; rw [dite_eq_right hNotLt]
          have hFin : (⟨2 ^ b + mLo.val - 2 ^ b, by have := mLo.isLt; omega⟩ : Fin (2 ^ b)) =
              mLo := Fin.ext (by dsimp; omega)
          rw [hFin]
        have hLeaf := hk ⟨2 ^ b + mLo.val, by have := mLo.isLt; rw [pow_succ']; omega⟩ Ψ hΨ τ
        rw [hPar, diagPhaseUnitary_xor_w3, QRegister.embedUnitary_mul,
          ← mul_assoc] at hLeaf
        exact hLeaf)
      (Function.update σ v 1)
    rw [embed_xorLoadUnitary_split_last_w3 rAddr rMeas hAddrMeas T, ← qc_wp_qAssign_comp]
    simp only [SelectSwapQROM.measureXResetAndBranch]
    have hStepLo :
        (qcWpQAssign W_lo (wp (SelectSwapQROM.measureXReset1AndBranch v w
          (SelectSwapQROM.measureXResetAndBranch v b rLo k₀)
          (SelectSwapQROM.measureXResetAndBranch v b rLo k₁)).compile Θ) σ).1 =
        (qcWpQAssign W_lo (wp (SelectSwapQROM.measureXResetAndBranch v b rLo k₀).compile Θ)
          (Function.update σ v 0)).1.conj L₀ᴴ +
        (qcWpQAssign W_lo (wp (SelectSwapQROM.measureXResetAndBranch v b rLo k₁).compile Θ)
          (Function.update σ v 1)).1.conj L₁ᴴ := by
      simp only [qcWpQAssign, qcQAssignObsMap, Observable.conj_coe, Unitary.coe_star,
        Matrix.star_eq_conjTranspose]
      rw [wp_measureXReset1AndBranch_apply_w3, map_add, conj_conj, conj_conj, hL₀Wlo, hL₁Wlo,
        ← conj_conj, ← conj_conj]
    ext1
    have hOuter :
        ((qcWpQAssign W_w (qcWpQAssign W_lo
          (wp (SelectSwapQROM.measureXReset1AndBranch v w
            (SelectSwapQROM.measureXResetAndBranch v b rLo k₀)
            (SelectSwapQROM.measureXResetAndBranch v b rLo k₁)).compile Θ)) σ).1).conj
          (Mobius126OneHot.cleanPredProj S H) =
        (qcWpQAssign W_lo (wp (SelectSwapQROM.measureXResetAndBranch v b rLo k₀).compile Θ)
          (Function.update σ v 0)).1.conj
            (SelectSwapQROM.sqrtHalf • Mobius126OneHot.cleanPredProj S H) +
        (qcWpQAssign W_lo (wp (SelectSwapQROM.measureXResetAndBranch v b rLo k₁).compile Θ)
          (Function.update σ v 1)).1.conj
            (SelectSwapQROM.sqrtHalf •
              (D_last.1ᴴ * Mobius126OneHot.cleanPredProj S H)) := by
      have hWw (Ψ : QCAssertion Var (2 ^ N)) :
          ((qcWpQAssign W_w Ψ σ).1).conj (Mobius126OneHot.cleanPredProj S H) =
          (((Ψ σ).1).conj W_w.1ᴴ).conj (Mobius126OneHot.cleanPredProj S H) := by
        simp only [qcWpQAssign, qcQAssignObsMap, Observable.conj_coe, Unitary.coe_star,
          Matrix.star_eq_conjTranspose]
      rw [hWw, hStepLo, map_add, map_add, conj_conj, conj_conj, conj_conj, conj_conj,
        hKraus0Adj, hKraus1Adj]
    have h0Mat := congrArg HermitianMat.mat hB₀
    simp only [qcWpQAssign, qcQAssignObsMap, Observable.conj_coe, Unitary.coe_star,
      Matrix.star_eq_conjTranspose, hΘ σ 0] at h0Mat
    have hTerm0 :
        ((qcWpQAssign W_lo (wp (SelectSwapQROM.measureXResetAndBranch v b rLo k₀).compile Θ)
          (Function.update σ v 0)).1.conj
            (SelectSwapQROM.sqrtHalf • Mobius126OneHot.cleanPredProj S H)).mat =
        (1 / 2 : ℂ) •
          (((Θ σ).1.conj U_base.1ᴴ).conj (Mobius126OneHot.cleanPredProj S H)).mat := by
      dsimp only [W_lo]
      simp only [qcWpQAssign, qcQAssignObsMap, Observable.conj_coe, Unitary.coe_star,
        Matrix.star_eq_conjTranspose, conj_apply_mat, conjTranspose_smul,
        SelectSwapQROM.star_sqrtHalf, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
        SelectSwapQROM.sqrtHalf_mul_sqrtHalf] at h0Mat ⊢
      rw [h0Mat]
    have hCollapse : D_last.1ᴴ *
        (Mobius126OneHot.cleanPredProj S H * (U_base * D_last).1ᴴ) =
        Mobius126OneHot.cleanPredProj S H * U_base.1ᴴ := by
      simp only [Submonoid.coe_mul, conjTranspose_mul]
      calc D_last.1ᴴ * (Mobius126OneHot.cleanPredProj S H * (D_last.1ᴴ * U_base.1ᴴ))
          = (D_last.1ᴴ * Mobius126OneHot.cleanPredProj S H) * D_last.1ᴴ * U_base.1ᴴ := by
              simp only [Matrix.mul_assoc]
        _ = Mobius126OneHot.cleanPredProj S H * (D_last.1ᴴ * D_last.1ᴴ) * U_base.1ᴴ := by
              rw [hDwAdjComm, Matrix.mul_assoc (Mobius126OneHot.cleanPredProj S H)]
        _ = Mobius126OneHot.cleanPredProj S H * U_base.1ᴴ := by
              rw [hDwAdjSq, Matrix.mul_one]
    have h1Conj :
        ((qcWpQAssign W_lo (wp (SelectSwapQROM.measureXResetAndBranch v b rLo k₁).compile Θ)
          (Function.update σ v 1)).1.conj
            (D_last.1ᴴ * Mobius126OneHot.cleanPredProj S H)).mat =
        (((Θ σ).1.conj U_base.1ᴴ).conj (Mobius126OneHot.cleanPredProj S H)).mat := by
      have h' := congrArg (fun M : HermitianMat (Fin (2 ^ N)) ℂ ↦ (M.conj D_last.1ᴴ).mat) hB₁
      dsimp only [W_lo]
      simp only [qcWpQAssign, qcQAssignObsMap, Observable.conj_coe, Unitary.coe_star,
        Matrix.star_eq_conjTranspose, hΘ σ 1, conj_conj, Matrix.mul_assoc, hCollapse] at h' ⊢
      exact h'
    have hTerm1 :
        ((qcWpQAssign W_lo (wp (SelectSwapQROM.measureXResetAndBranch v b rLo k₁).compile Θ)
          (Function.update σ v 1)).1.conj
            (SelectSwapQROM.sqrtHalf •
              (D_last.1ᴴ * Mobius126OneHot.cleanPredProj S H))).mat =
        (1 / 2 : ℂ) •
          (((Θ σ).1.conj U_base.1ᴴ).conj (Mobius126OneHot.cleanPredProj S H)).mat := by
      simp only [conj_apply_mat, conjTranspose_smul, SelectSwapQROM.star_sqrtHalf,
        Matrix.smul_mul, Matrix.mul_smul, smul_smul,
        SelectSwapQROM.sqrtHalf_mul_sqrtHalf] at h1Conj ⊢
      rw [h1Conj]
    have hRhs :
        (((qcWpQAssign U_base Θ σ).1).conj (Mobius126OneHot.cleanPredProj S H)).mat =
          (((Θ σ).1.conj U_base.1ᴴ).conj (Mobius126OneHot.cleanPredProj S H)).mat := by
      simp [qcWpQAssign, qcQAssignObsMap, Observable.conj_coe, Unitary.coe_star,
        Matrix.star_eq_conjTranspose]
    rw [congrArg HermitianMat.mat hOuter, HermitianMat.mat_add, hTerm0, hTerm1, ← add_smul, hRhs]
    norm_num

export QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.Tuned162ScheduledSympQrom21 (
  evenColParityPrefix oddColParityPrefix evenColParity30 oddColParity30 extCol24Bool col24ZMod5
  col24Anf5 extCol24Bool_of_lt extCol24Bool_30 extCol24Bool_31 anfCoeffs_zero_local
  anfCoeffs_add_local col24Anf5_30 col24Anf5_31 anfCoeffs_parityLinComb_vanish
  anfCoeffs_sliceParityFn_of_vanish
)

end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.Tuned162StepSympAnfQrom21

namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.OptStepSympAnfQrom21
open QuantumComputation.Specs QuantumComputation.Specs.P450

export QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.Tuned162StepSympAnfQrom21 (
  ext24InnerBoolTable ext24InnerBoolTable_sum_even_odd diagKetUnitary diagKetUnitary_mulVec_ket
  diagKetUnitary_mul diagKetUnitary_zero cnotMaskLoop cnotMaskW3Circuit
  count_cnotMaskW3Circuit_toff count_cnotMaskW3Circuit_t ket_cnotMaskW3Circuit optWireBit
  optCzW3Circuit count_optCzW3Circuit_toff count_optCzW3Circuit_t ket_optCzW3Circuit
  lStepInPlaceDyn count_lStepInPlaceDyn_toff count_lStepInPlaceDyn_t lStepPhase
  cleanRealizesSet_lStepInPlaceDyn optMono4 optMono3 option_map_ne_of_ne oneHotPred c2In5Idx
  c2In5Idx_inj c2In5Reg cubeAddr5 anf2DCoeffs canonLeg2 canonLeg2_j_ne_jp canonLeg2_k_ne_kp
  stepCoverZMod2 optMono2 bg2Cube bg2Sum bg2Coeff leg2Masks lin2Term lStepLoop7 hotSlice2DCube
  hotRes2DCube hotResidualClifford count_hotResidualClifford_toff count_hotResidualClifford_t
  hotFixup12KetPhase hotFixup12KetPhase_eq_of_oneHot wp_measureXResetAndBranch_update_self
  wp_measureXResetAndBranch_unload_cleanPredProj
)

end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.OptStepSympAnfQrom21
