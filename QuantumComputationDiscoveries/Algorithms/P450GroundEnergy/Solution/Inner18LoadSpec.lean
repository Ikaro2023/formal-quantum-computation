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

public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.Pi145Select24Aux
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.ThreeGearBellSuper
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.Inner18Symp14Walk
public import
  QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.NoNegSOSAndSuperWalk

/-!
# `{Var : Type}`-Computable `wInner2 = 18` `StageB` Walk Packages 

Modular loader interfaces and constructors for `wInner2 = 18`:
1. `OneHot14LoadCirc` and `OneHot14LoadBundle2`: `{Var : Type}`-computable `128 × 14` one-hot QROM
   loader package unifying full-space `Symp14` loaders (`.sympW4` `708 T`, `.sympW5` `672 T`) and
   `hotLinearTargetFn` H-gadget loaders (`.ofLinearClean`, `.ofKeep9LinearClean`) via
   `HotTableSpec14` and `CleanPredRealizes` on `oneHotPred`.
2. `Mag30Circ` / `Mag30Bundle` (`.t72`, `.quant66`, `.quant56`) and `SdMux23Circ` / `SdMux23Bundle`
   (`56 T`, `19` scratch, plus plug-in interface for `46-T` Hadamard W-state mux-swap).
3. `rXo7`-borrowing `14`-plane QROM wrapper (`qromXoBorrowLoad14GenDyn`), forward `PREP_mid`
   (`prepMid18BorrowGenDyn`), and generic X-measurement `PREP_mid†` (`genPrepMid18InvDyn`).

## References
- C. Gidney, *Quantum* **2**, 74 (2018), DOI: `10.22331/q-2018-06-18-74`.
- D. W. Berry et al., *Quantum* **3**, 208 (2019), DOI: `10.22331/q-2019-12-02-208`.
- G. H. Low, V. Kliuchnikov, and L. Schaeffer, *Quantum* **8**, 1375 (2024),
  DOI: `10.22331/q-2024-06-17-1375`.
-/
@[expose] public section
namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.Inner18Load
open QuantumComputation.Specs QuantumComputation.Specs.P450
local instance (priority := 999998) instNeZeroTwoPowLoad18 (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩
open Operator QProg Matrix Circuit Real HermitianMat BlockEncodingCore BlockEncodingCircuit
open QuantumComputation.Specs Solution QuantumComputation.Specs.P450 CoherentAlias Solution.CleanDyn
open AliasPrep
open Solution.CircuitModular Solution.GivensOps
open MidReflCtxRetain Phase2MidSandwich OptFactoredMag30AndCoin9 QuantizedFactoredMag30
open Cat11CompactPhase2Bridge ReordOuter13Bridge ZeroRcHotPrepMid21Fast OptXMeasUnload21
open Tuned162ScheduledSympQrom21 Tuned162StepSympAnfQrom21 OptStepSympAnfQrom21 TopIntegrationBridge
open MobiusOptSubcube163Walk CompactTuned162StepZeroCmp20 CompactZeroCmp20OuterParam
open CompactStepZeroCmp20OuterParam StepAnfAndCoin14Core CompactStepCompact2504ZeroCmp20
open Pi145SOSPermBridge StepOuter8Pi145Outer StepOuter8Pi145L1 StepKeep9Symp14Data
open StepBound148Borrow Tuned155Hot128SympQrom20 CompactOuter9Bound50Core
open LowBitPi145Select BellSingletCSwap58 FastUniform
open Inner18Symp14Walk QRegister InnerTable SelectSwapQROM GroupUnary
open Solution.CircuitModular.UnsignedGivens (maskSumBit basisBits_symm_eq cnotMaskReg
  evolve_cnotMaskReg_ket eval_identity_mulVec)
open Function (update update_of_ne update_self update_apply)
open Observable (conj_coe)
open Unitary (coe_star)
open Submonoid (coe_mul)
open DynamicCircuit (qc_wp_circuit_compile compile_circuit)
open scoped Matrix BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator Circuit.Notation
/-! ## Section 1: Generalized `{Var : Type}` `128 × 14` One-Hot QROM Loader Package -/
section OneHot14LoadBundle
/-- Computable `{Var : Type}` `128 × 14` one-hot QROM loader circuit carrier
(`tLoad14` `T`, `0 TOFF`, `sQrom ≤ sScr`). -/
structure OneHot14LoadCirc (Var : Type) (sQrom tLoad14 : ℕ) where
  loadDyn : ∀ {N sScr : ℕ}, Var → (rQrom : QRegister (5 + 128 + 14) N) →
    (rScr : QRegister sScr N) → sQrom ≤ sScr → rQrom.DisjointWires rScr → DynamicCircuit Var N
  count_toff : ∀ {N sScr : ℕ} (v : Var) (rQrom : QRegister (5 + 128 + 14) N)
    (rScr : QRegister sScr N) (hs : sQrom ≤ sScr) (hdisj : rQrom.DisjointWires rScr),
    (loadDyn v rQrom rScr hs hdisj).count .TOFF = 0
  count_t : ∀ {N sScr : ℕ} (v : Var) (rQrom : QRegister (5 + 128 + 14) N)
    (rScr : QRegister sScr N) (hs : sQrom ≤ sScr) (hdisj : rQrom.DisjointWires rScr),
    (loadDyn v rQrom rScr hs hdisj).count .T = tLoad14
/-- Certified `128 × 14` one-hot QROM loader package (`tLoad14` `T`, `0 TOFF`, `sQrom ≤ sScr`),
unifying full-space `Symp14` loaders and `hotLinearTargetFn` H-gadget loaders via `HotTableSpec14`
and `CleanPredRealizes` on `oneHotPred`. -/
structure OneHot14LoadBundle2 (Var : Type) (sQrom tLoad14 : ℕ)
    (F133 : Fin (2 ^ (5 + 128)) → BitAssignment 14)
    (sliceFn : Fin (2 ^ 7) → Fin (2 ^ 5) → BitAssignment 14)
    extends OneHot14LoadCirc Var sQrom tLoad14 where
  spec14 : HotTableSpec14 F133 sliceFn
  clean2 : ∀ [Fintype Var] [DecidableEq Var] {N sScr : ℕ} (v : Var)
    (rQrom : QRegister (5 + 128 + 14) N) (rScr : QRegister sScr N) (hs : sQrom ≤ sScr)
    (hdisj : rQrom.DisjointWires rScr), CleanPredRealizes v
      (Mobius126OneHot.cleanPredProj rScr.image (oneHotPred (rQrom.slice 5 128 (by decide))))
      (rQrom.embedUnitary (aliasTableXorUnitary (5 + 128) 14 F133))
      (loadDyn v rQrom rScr hs hdisj)
/-- Construct `OneHot14LoadBundle2` from any `hotLinearTargetFn 5 128 14 boolTbl` one-hot loader. -/
noncomputable def OneHot14LoadBundle2.ofLinearClean {Var : Type} {sQrom tLoad14 : ℕ}
    (c : OneHot14LoadCirc Var sQrom tLoad14) (boolTbl : Fin 128 → Fin (2 ^ 5) → Fin 14 → Bool)
    (hSi : ∀ [Fintype Var] [DecidableEq Var] {N sScr : ℕ} (v : Var)
      (rQrom : QRegister (5 + 128 + 14) N) (rScr : QRegister sScr N) (hs : sQrom ≤ sScr)
      (hdisj : rQrom.DisjointWires rScr), CleanPredRealizes v
        (Mobius126OneHot.cleanPredProj rScr.image (oneHotPred (rQrom.slice 5 128 (by decide))))
        (rQrom.embedUnitary
          (aliasTableXorUnitary (5 + 128) 14 (hotLinearTargetFn 5 128 14 boolTbl)))
        (c.loadDyn v rQrom rScr hs hdisj)) :
    OneHot14LoadBundle2 Var sQrom tLoad14 (hotLinearTargetFn 5 128 14 boolTbl)
      (fun rc x k ↦ if boolTbl rc x k then 1 else 0) where
  toOneHot14LoadCirc := c
  spec14 rc cHot hcHot x := hotLinearTargetFn_combineAddr_oneHot boolTbl x rc cHot hcHot
  clean2 := hSi
/-- Specialized `keep9Hot24BoolTable` adapter producing `keep9SliceTargetFn14`. -/
noncomputable def OneHot14LoadBundle2.ofKeep9LinearClean {Var : Type} {sQrom tLoad14 : ℕ}
    (c : OneHot14LoadCirc Var sQrom tLoad14)
    (hSi : ∀ [Fintype Var] [DecidableEq Var] {N sScr : ℕ} (v : Var)
      (rQrom : QRegister (5 + 128 + 14) N) (rScr : QRegister sScr N) (hs : sQrom ≤ sScr)
      (hdisj : rQrom.DisjointWires rScr), CleanPredRealizes v
        (Mobius126OneHot.cleanPredProj rScr.image (oneHotPred (rQrom.slice 5 128 (by decide))))
        (rQrom.embedUnitary
          (aliasTableXorUnitary (5 + 128) 14 (hotLinearTargetFn 5 128 14 keep9Hot24BoolTable)))
        (c.loadDyn v rQrom rScr hs hdisj)) :
    OneHot14LoadBundle2 Var sQrom tLoad14 (hotLinearTargetFn 5 128 14 keep9Hot24BoolTable)
      keep9SliceTargetFn14 := OneHot14LoadBundle2.ofLinearClean c keep9Hot24BoolTable hSi
end OneHot14LoadBundle
/-! ## Section 2: `{Var : Type}` `Mag30Circ` / `Mag30Bundle` & `SdMux23Circ` / `SdMux23Bundle` -/
/-- Computable `{Var : Type}` `0`-scratch `5`-wire `L = 30` index-magnitude circuit carrier
(`tMag` `T`, `0 TOFF`). -/
structure Mag30Circ (Var : Type) (tMag : ℕ) where
  fwdDyn : ∀ {N : ℕ}, QRegister 5 N → DynamicCircuit Var N
  invDyn : ∀ {N : ℕ}, QRegister 5 N → DynamicCircuit Var N
  count_fwd_toff : ∀ {N : ℕ} (r : QRegister 5 N), (fwdDyn r).count .TOFF = 0
  count_inv_toff : ∀ {N : ℕ} (r : QRegister 5 N), (invDyn r).count .TOFF = 0
  count_fwd_t : ∀ {N : ℕ} (r : QRegister 5 N), (fwdDyn r).count .T = tMag
  count_inv_t : ∀ {N : ℕ} (r : QRegister 5 N), (invDyn r).count .T = tMag
  support_fwd_sub : ∀ {N : ℕ} (r : QRegister 5 N), (fwdDyn r).support ⊆ r.image
  support_inv_sub : ∀ {N : ℕ} (r : QRegister 5 N), (invDyn r).support ⊆ r.image
/-- Computable `72-T` (`0 TOFF`) `Mag30Circ` backed by `factoredMag30T72Circuit`. -/
def Mag30Circ.t72 (Var : Type) : Mag30Circ Var 72 where
  fwdDyn r := factoredMag30T72Dyn r
  invDyn r := unprepFactoredMag30T72Dyn r
  count_fwd_toff := countFactoredMag30T72Dyn_toff
  count_inv_toff := countUnprepFactoredMag30T72Dyn_toff
  count_fwd_t := countFactoredMag30T72Dyn_t
  count_inv_t := countUnprepFactoredMag30T72Dyn_t
  support_fwd_sub r := by
    unfold factoredMag30T72Dyn
    exact DynamicCircuit.circuit_support_onRegister_subset r _
  support_inv_sub r := by
    unfold unprepFactoredMag30T72Dyn
    exact DynamicCircuit.circuit_support_onRegister_subset r _
/-- Certified `0`-scratch `5`-wire `L = 30` index-magnitude package (`tMag` `T`, `0 TOFF`). -/
structure Mag30Bundle (Var : Type) (tMag : ℕ) (uIdx : Unitary (2 ^ 5))
    extends Mag30Circ Var tMag where
  clean_fwd : ∀ [Fintype Var] [DecidableEq Var] {N s : ℕ} (v : Var) (r : QRegister 5 N)
    (rScr : QRegister s N), r.DisjointWires rScr →
      Solution.CleanDyn.CleanRealizes v r rScr uIdx (fwdDyn r)
  clean_inv : ∀ [Fintype Var] [DecidableEq Var] {N s : ℕ} (v : Var) (r : QRegister 5 N)
    (rScr : QRegister s N), r.DisjointWires rScr →
      Solution.CleanDyn.CleanRealizes v r rScr uIdx⁻¹ (invDyn r)
  vanish_ge30 : ∀ (x : Fin (2 ^ 5)), 30 ≤ x.val → (uIdx.1 *ᵥ basisState 0) x = 0
/-- `72-T` (`0 TOFF`) `Mag30Bundle` backed by `factoredMag30T72Circuit`. -/
noncomputable def Mag30Bundle.t72 (Var : Type) :
    Mag30Bundle Var 72 factoredMag30T72Circuit.eval where
  toMag30Circ := Mag30Circ.t72 Var
  clean_fwd := cleanRealizesFactoredMag30T72Dyn
  clean_inv := cleanRealizesUnprepFactoredMag30T72Dyn
  vanish_ge30 := factoredMag30T72Circuit_vanish
/-! ## Section 3: `rXo7`-Borrowing `PREP_mid` & `w = 3` `PREP_mid†` SDK -/
end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.Inner18Load
end
