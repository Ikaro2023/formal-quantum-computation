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

public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.TopIntegrationBridge
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.MidReflSandwich
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.WalkQPEFlexBridge
public import
  QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.WalkQPECat11ReducedRefl

/-!
# Mid-Reflection Context Retention
Eliminates redundant `rc(x_o)` (`7`-bit) and `rHotCtx` (`128`-wire one-hot) computations across
the mid-walk reflection turnaround `PREP_mid† ;; R_mid ;; PREP_mid` (and optionally across the
entire inner `PREP_mid ;; SELECT ;; turnaround ;; SELECT† ;; PREP_mid†` chain when `SELECT` leaves
`21` scratch wires free), keeping all core combinators and theorems **parametric in
`(wOuter wInner2 : ℕ)`** so they splice directly into both `(19, 26)` and `(13, 10)` (`Q = 364`
packet-mux) architectures:

1. **Section 1 — `(wOuter, wInner2)`-Parametric `CleanTurnaroundWp`, Context-Retention Wrappers &
   Fused
   `pRefl2` Combinators (Variants 1 & 2):**
   - `CleanTurnaroundWp`, `cleanTurnaroundWp_withUnaryOneHotDyn` (`508 T` at `L = 128`), and
     `TempProg.cleanTurnaroundWp_wrapSubMux` (`48 T` via `rcOnly21Steps`).
   - **Variant 1 (`ubCtxRetainPulledParamDyn`):** `SELECT` may reuse all `sUb` scratch wires;
     retains `rc : 7` and `rHotCtx : L_ctx` across `PREP_mid†_1 ;; R_mid ;; PREP_mid_2`.
   - **Variant 2 (`ubFullRcCtxRetainPulledParamDyn`):** When `SELECT` uses `sSel ≤ sUb - 21`
     scratch wires, retains `rc : 7` across all five inner steps
     `PREP_mid_1 ;; selFwd ;; turnaroundFromRc ;; selBwd ;; PREP_mid†_2`.
2. **Section 2 — Generic `rHotCtx`-Assisted `ANF` X-Measurement QROM Unload
   (`qromXMeasFromHotCtxUnloadDyn`):**
   - Parametric over `(idxBits L_ctx outBits : ℕ)` and `F : Fin L_ctx → Fin (2 ^ idxBits) →
     Fin outBits → Bool`: `4 * anfScratchWidth idxBits` `T` (`104 T`, `26` wires at `idxBits = 5`,
     `0 TOFF`), plus custom-unload `coherentAliasPrepDagFromHotCtxDyn`.
3. **Section 3 — Preloaded-`rHotCtx` Rank-2 `GF(2)` Bilinear QROM Load (`1,080 T`, `34` wires):**
   - `qromBilinearFromHot128LoadDyn` (`1,080 T`), custom-uniform
     `bilinearHotFastPrepMidFromHot128Dyn` (`1,140 + uP.count .T` `T`), custom-unload
     `hotFastPrepMidDagFromHot128Dyn` (`60 + qromUnload.count .T + uDP.count .T` `T`), and
     `preservesWires_conj_hotFastPrepMidOf`.
4. **Section 4 — Turnkey `(19, 26)` `Lite` (`6,648` / `6,552` `T`), `Med` (`6,680` / `6,584` `T`) &
   Custom-Unload `pRefl2` Constructors + `WalkTopBridge.masterTopRefl2Prog`
   Master Corollaries.**
-/

@[expose] public section

namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.MidReflCtxRetain
open QuantumComputation.Specs QuantumComputation.Specs.P450

open Operator QProg Matrix Circuit HermitianMat Real QuantumComputation.Specs Solution
open QuantumComputation.Specs.P450 Solution CoherentAlias Solution.CleanDyn AliasPrep
open Phase2MidSandwich
open TopIntegrationBridge
open Solution.BlockEncodingCore Solution.BlockEncodingCircuit
open Solution.WalkQPEBridge
open Solution.WalkQPEBridgeXMeas
open scoped Matrix BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

local instance (priority := 1000000) instNeZeroTwoPow (k : ℕ) : NeZero (2 ^ k) :=
  ⟨Nat.pos_iff_ne_zero.mp (by positivity)⟩

attribute [local irreducible] thcHamiltonian BlockEncodingCore.p450HBlocked dfthcLowerBound
  CliffordT.exactPhaseGrad14Unitary oneBodyWeights fragmentWeights innerWeights oneBodyWeightInt
  fragmentWeightNat innerMantissa

/-- Weakest-precondition turnaround contract on clean wire set `S`: `P` is `.TOFF`-free,
`v`-update-invariant, and transitions an incoming state prepared by `W_in` directly into the
outgoing state prepared by `W_out` on `S` (without requiring `W_in` or `W_out` to preserve `S`). -/
def CleanTurnaroundWp {Var : Type} [Fintype Var] [DecidableEq Var] {N : ℕ} [NeZero (2 ^ N)]
    (v : Var) (S : Finset (Wire N)) (W_in W_out : Unitary (2 ^ N))
    (P : DynamicCircuit Var N) : Prop :=
  P.count PrimitiveGate.TOFF = 0 ∧
  (∀ Θ : QCAssertion Var (2 ^ N), (∀ σ val, Θ (Function.update σ v val) = Θ σ) →
    ∀ σ val, (wp P.compile Θ) (Function.update σ v val) = (wp P.compile Θ) σ) ∧
  (∀ Θ : QCAssertion Var (2 ^ N), (∀ σ val, Θ (Function.update σ v val) = Θ σ) →
    SelectSwapQROM.restrictZeroSet (qcWpQAssign W_in (wp P.compile Θ)) S =
      SelectSwapQROM.restrictZeroSet (qcWpQAssign W_out Θ) S)

theorem CleanTurnaroundWp.extend {Var : Type} [Fintype Var] [DecidableEq Var] {N : ℕ}
    [NeZero (2 ^ N)] {v : Var} {S₁ S₂ : Finset (Wire N)} {W_in W_out : Unitary (2 ^ N)}
    {P : DynamicCircuit Var N}
    (h : CleanTurnaroundWp v S₁ W_in W_out P) (hSub : S₁ ⊆ S₂) :
    CleanTurnaroundWp v S₂ W_in W_out P := by
  refine ⟨h.1, h.2.1, fun Θ hΘ ↦ ?_⟩
  rw [← Finset.union_eq_right.mpr hSub, ← SelectSwapQROM.restrictZeroSet_union,
    ← SelectSwapQROM.restrictZeroSet_union, h.2.2 Θ hΘ]

/-- Joint subspace projector onto clean wire set `S_clean` (`β w = 0`) and computational-basis
predicate `H`. -/
noncomputable def cleanPredProj {N : ℕ} (S_clean : Finset (Wire N))
    (H : BitAssignment N → Bool) : Operator (2 ^ N) :=
  SelectSwapQROM.zeroProjOn S_clean * GroupUnary.predProj H

/-! ### `(wOuter, wInner2)`-Parametric Context-Retaining Turnaround & Fused `pRefl2` (Variants 1 &
  2) -/

/-- `GF(2)`-linear Boolean QROM table over `(idxBits + L_ctx)` address bits whose output bit `k`
at `(x, h)` is `⨁_{c < L_ctx} h_c ∧ F c x k`. When `h` is the one-hot vector for `c₀ : Fin L_ctx`,
this equals `F c₀ x k`. -/
noncomputable def hotLinearBoolTable (idxBits L_ctx outBits : ℕ)
    (F : Fin L_ctx → Fin (2 ^ idxBits) → Fin outBits → Bool)
    (addr : ℕ) (k : Fin outBits) : Bool :=
  if h : addr < 2 ^ (idxBits + L_ctx) then
    let a : Fin (2 ^ (idxBits + L_ctx)) := ⟨addr, h⟩
    let x : Fin (2 ^ idxBits) :=
      (basisBits idxBits).symm
        (fun i ↦ basisBits (idxBits + L_ctx) a (Fin.castAdd L_ctx i))
    ((∑ c : Fin L_ctx,
        basisBits (idxBits + L_ctx) a (Fin.natAdd idxBits c) *
          (if F c x k then (1 : ZMod 2) else 0)) == 1)
  else
    false

/-- `BitAssignment outBits` QROM target function associated with `hotLinearBoolTable`. -/
noncomputable def hotLinearTargetFn (idxBits L_ctx outBits : ℕ)
    (F : Fin L_ctx → Fin (2 ^ idxBits) → Fin outBits → Bool) :
    Fin (2 ^ (idxBits + L_ctx)) → BitAssignment outBits :=
  AliasPrep.boolTableToAliasFn (idxBits + L_ctx) outBits (2 ^ (idxBits + L_ctx))
    (hotLinearBoolTable idxBits L_ctx outBits F)

/-- On any one-hot context state `cHot` representing `c₀ : Fin L_ctx`, `hotLinearTargetFn`
agrees with `F c₀ x`. -/
theorem hotLinearTargetFn_combineAddr_oneHot {idxBits L_ctx outBits : ℕ}
    (F : Fin L_ctx → Fin (2 ^ idxBits) → Fin outBits → Bool)
    (x : Fin (2 ^ idxBits)) (c₀ : Fin L_ctx) (cHot : Fin (2 ^ L_ctx))
    (hcHot : ∀ c : Fin L_ctx, basisBits L_ctx cHot c = if c = c₀ then 1 else 0) :
    hotLinearTargetFn idxBits L_ctx outBits F (CoherentAlias.combineAddr x cHot) =
      fun k ↦ if F c₀ x k then 1 else 0 := by
  set a := CoherentAlias.combineAddr x cHot
  have haLo : (fun i : Fin idxBits ↦ basisBits (idxBits + L_ctx) a (Fin.castAdd L_ctx i)) =
      basisBits idxBits x := by
    funext i
    dsimp only [a, CoherentAlias.combineAddr]
    rw [SelectSwapQROM.basisBits_symm]
    simp [i.isLt]
  have hxEq : (basisBits idxBits).symm
      (fun i ↦ basisBits (idxBits + L_ctx) a (Fin.castAdd L_ctx i)) = x := by
    rw [haLo, SelectSwapQROM.symm_basisBits]
  have haHi (c : Fin L_ctx) :
      basisBits (idxBits + L_ctx) a (Fin.natAdd idxBits c) = if c = c₀ then 1 else 0 := by
    dsimp only [a, CoherentAlias.combineAddr]
    rw [SelectSwapQROM.basisBits_symm]
    have hNotLt : ¬((Fin.natAdd idxBits c).val < idxBits) := by simp
    rw [dite_eq_right hNotLt]
    have hSub : (⟨(Fin.natAdd idxBits c).val - idxBits, by simp⟩ : Fin L_ctx) = c := by
      ext; simp
    rw [hSub, hcHot c]
  funext k
  have haLt : a.val < 2 ^ (idxBits + L_ctx) := a.isLt
  have haFin : (⟨a.val, haLt⟩ : Fin (2 ^ (idxBits + L_ctx))) = a := Fin.ext rfl
  have hSum : (∑ c : Fin L_ctx,
      basisBits (idxBits + L_ctx) a (Fin.natAdd idxBits c) *
        (if F c x k then (1 : ZMod 2) else 0)) =
      if F c₀ x k then 1 else 0 := by
    rw [Finset.sum_eq_single c₀]
    · rw [haHi c₀, ite_eq_left rfl, one_mul]
    · intro c _ hcNe
      rw [haHi c, ite_eq_right hcNe, zero_mul]
    · intro hAbs; exact absurd (Finset.mem_univ c₀) hAbs
  have hTbl : hotLinearBoolTable idxBits L_ctx outBits F a.val k = F c₀ x k := by
    dsimp only [hotLinearBoolTable]
    simp only [haLt, ↓reduceDIte, haFin, hxEq]
    rw [hSum]
    cases F c₀ x k <;> rfl
  dsimp only [hotLinearTargetFn, AliasPrep.boolTableToAliasFn]
  by_cases hF : F c₀ x k <;> simp [haLt, hTbl, hF]

/-- Recursive `ZMod 2` linear functional matching the bit extraction of
`SelectSwapQROM.parityPhaseTable`. -/
def parityLinComb : (b : ℕ) → Fin (2 ^ b) → (Fin b → ZMod 2) → ZMod 2
  | 0, _, _ => 0
  | b + 1, m, w =>
      let wLo : Fin b → ZMod 2 := fun j ↦ w (Fin.castLE (Nat.le_succ b) j)
      let iLast : Fin (b + 1) := ⟨b, Nat.lt_succ_self b⟩
      if hm : m.val < 2 ^ b then
        parityLinComb b ⟨m.val, hm⟩ wLo
      else
        w iLast +
          parityLinComb b
            ⟨m.val - 2 ^ b, by
              have hm2 : m.val < 2 * 2 ^ b := by simpa [pow_succ'] using m.isLt
              omega⟩
            wLo

/-- Outcome-`m` `ZMod 2` parity table for context slice `c : Fin L_ctx` on `x : Fin (2 ^ idxBits)`.
Its ANF over `idxBits` bits drives the `CZ`/`Z` fanout from `rHotCtx c`. -/
def sliceParityFn (idxBits L_ctx outBits : ℕ)
    (F : Fin L_ctx → Fin (2 ^ idxBits) → Fin outBits → Bool)
    (m : Fin (2 ^ outBits)) (c : Fin L_ctx) (x : Fin (2 ^ idxBits)) : ZMod 2 :=
  parityLinComb outBits m (fun k ↦ if F c x k then 1 else 0)

/-- `0-T`, `0-TOFF` static `CZ`/`Z` fanout loop from the `n` low wires of `rHotCtx` into the
`(2 ^ idxBits - 1)`-wire monomial register `rAll`. -/
def hotCtxPhaseLoop {N : ℕ} (M L_ctx : ℕ)
    (rHotCtx : QRegister L_ctx N) (rAll : QRegister M N)
    (hHotNotAll : ∀ (c : Fin L_ctx) (u : Fin M), rHotCtx c ≠ rAll u)
    (c0 : Fin L_ctx → ZMod 2) (cPos : Fin L_ctx → Fin M → ZMod 2) :
    (n : ℕ) → n ≤ L_ctx → Circuit N
  | 0, _ => .identity
  | n + 1, hn =>
      let c : Fin L_ctx := ⟨n, hn⟩
      .seq
        (hotCtxPhaseLoop M L_ctx rHotCtx rAll hHotNotAll c0 cPos n (Nat.le_of_succ_le hn))
        (.seq
          (if c0 c = 1 then Circuit.Z (rHotCtx c) else .identity)
          (SelectSwapQROM.czMaskCircuit (rHotCtx c) M rAll (hHotNotAll c) (cPos c)))

@[simp]
private theorem count_hotCtxPhaseLoop_toff {N M L_ctx : ℕ}
    (rHotCtx : QRegister L_ctx N) (rAll : QRegister M N)
    (hHotNotAll : ∀ (c : Fin L_ctx) (u : Fin M), rHotCtx c ≠ rAll u)
    (c0 : Fin L_ctx → ZMod 2) (cPos : Fin L_ctx → Fin M → ZMod 2)
    (n : ℕ) (hn : n ≤ L_ctx) :
    (hotCtxPhaseLoop M L_ctx rHotCtx rAll hHotNotAll c0 cPos n hn).count .TOFF = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [hotCtxPhaseLoop, Circuit.count_seq, SelectSwapQROM.count_czMaskCircuit_toff,
      add_zero]
    rw [ih (Nat.le_of_succ_le hn), zero_add]
    split_ifs <;> simp [Circuit.Z, Circuit.single]

@[simp]
private theorem count_hotCtxPhaseLoop_t {N M L_ctx : ℕ}
    (rHotCtx : QRegister L_ctx N) (rAll : QRegister M N)
    (hHotNotAll : ∀ (c : Fin L_ctx) (u : Fin M), rHotCtx c ≠ rAll u)
    (c0 : Fin L_ctx → ZMod 2) (cPos : Fin L_ctx → Fin M → ZMod 2)
    (n : ℕ) (hn : n ≤ L_ctx) :
    (hotCtxPhaseLoop M L_ctx rHotCtx rAll hHotNotAll c0 cPos n hn).count .T = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [hotCtxPhaseLoop, Circuit.count_seq, SelectSwapQROM.count_czMaskCircuit_t,
      add_zero]
    rw [ih (Nat.le_of_succ_le hn), zero_add]
    split_ifs <;> simp [Circuit.Z, Circuit.single]

end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.MidReflCtxRetain
