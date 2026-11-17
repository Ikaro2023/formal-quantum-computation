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

public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.HybridStream288
public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.NucTwistCatLem

@[expose] public section
set_option exponentiation.threshold 256

namespace QuantumComputation.Specs.StoppingPowerSolution
open SpecsAux

section BiGqspVerifierCore
local instance (priority := 1000000) instNeZeroTwoPow_BiGqspVerifierCore (k : ℕ) :
    NeZero (2 ^ k) := ⟨(Nat.two_pow_pos k).ne'⟩

public section

namespace SpecsAux

open Operator

variable {Var : Type}

open SpecsAux.SpecMirror

set_option allowUnsafeReducibility true in
attribute [reducible] Function.Injective Function.Involutive

namespace GridStatesGuard
open Matrix QProg HermitianMat Circuit
open scoped Matrix ComplexOrder MatrixOrder QHLExpectation
variable {Var : Type}
section SeqRangeCombinator
@[simp]
theorem compile_seq {n : ℕ} (p₁ p₂ : DynamicCircuit Var n) :
    (DynamicCircuit.seq p₁ p₂).compile = p₁.compile.qSeq p₂.compile := rfl
end SeqRangeCombinator
end GridStatesGuard

end SpecsAux
local instance (priority := 1000000)
    instLoc_BiGqspVerifierCore_1InstNeZeroTwoPowBiGqsp (k : Nat) :
    NeZero (2 ^ k) := ⟨(Nat.two_pow_pos k).ne'⟩
namespace PhaseGradSignalRot
open Operator Matrix Circuit Function
open scoped Matrix
variable {n k : ℕ}
@[simp]
theorem localIdx_writeReg (β : BitAssignment n) (r : QRegister k n) (γ : BitAssignment k) :
    localIdx r (writeReg β r γ) = (basisBitsEquiv k).symm γ := by
  simp [localIdx]
end PhaseGradSignalRot
namespace CatalyzedLaurentGQSP
open Operator Matrix Circuit Function PhaseGradSignalRot
open TFreeLaurentGQSP
open scoped Matrix
variable {n : ℕ}
section ReflectionEvaluation
theorem eval_comm_embedMatrix_of_disjoint_support {k : ℕ} (c : Circuit n) (r : QRegister k n)
    (hdisj : Disjoint c.support r.image) (M : Operator (2 ^ k)) :
    c.eval.1 * r.embedMatrix M = r.embedMatrix M * c.eval.1 := by
  induction c with
  | identity => simp
  | gate g reg =>
    rw [Circuit.support_gate] at hdisj
    rw [Circuit.eval_gate, QRegister.embedUnitary_val]
    refine reg.embedMatrix_comm_of_disjoint r (QRegister.disjoint_iff.mpr fun i j hij ↦ ?_) _ M
    exact Finset.disjoint_left.mp hdisj ((QRegister.mem_image reg _).mpr ⟨i, rfl⟩)
      ((QRegister.mem_image r _).mpr ⟨j, hij.symm⟩)
  | seq c₁ c₂ ih₁ ih₂ =>
    simp only [Circuit.support_seq, Finset.disjoint_union_left] at hdisj
    rw [Circuit.eval_seq, Submonoid.coe_mul, Matrix.mul_assoc, ih₁ hdisj.1, ← Matrix.mul_assoc,
      ih₂ hdisj.2, Matrix.mul_assoc]
end ReflectionEvaluation
end CatalyzedLaurentGQSP
namespace BidirectionalCatalyzedGQSP
open Operator Matrix Circuit Function PhaseGradSignalRot
open TFreeLaurentGQSP CatalyzedLaurentGQSP
open scoped Matrix
variable {n : ℕ}
section ZeroFlagAndCZFlag
theorem eval_H_mul_self (w : Wire n) : (Circuit.H w).eval.1 * (Circuit.H w).eval.1 = 1 := by
  let rW := QRegister.singleton w
  have hH : (Circuit.H w).eval.1 = rW.embedMatrix Qubit.H.1 := by
    rw [Circuit.eval_single, QRegister.embedUnitary_val]
    rfl
  have hH2 : Qubit.H.1 * Qubit.H.1 = 1 := congrArg Subtype.val Qubit.H_sq
  rw [hH, ← rW.embedMatrix_mul, hH2, rW.embedMatrix_one]
end ZeroFlagAndCZFlag
end BidirectionalCatalyzedGQSP
end
end BiGqspVerifierCore

section HybridStream1300
local instance (priority := 1000000) instNeZeroTwoPow_HybridStream1300 (k : ℕ) :
    NeZero (2 ^ k) := ⟨(Nat.two_pow_pos k).ne'⟩

public section

namespace HybridStream1300

section ConfigHybridStream1300

open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt
open scoped Matrix BigOperators Circuit.Notation

open SpecsAux.SpecMirror
open DyadicQft64 hiding dyadicTurn phaseGradKet optBitVal
open InPlaceFullAddSlice InPlaceStepEngine
open SinglePassNuclearTwist288
open HybridStream288Aux

local instance (priority := 1000000)
    instLoc_HybridStream1300_1InstNeZeroTwoPowHybridStre (k : ℕ) : NeZero (2 ^ k) :=
  ⟨Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos k)⟩

/-! ## Section 1: Generalized 3-Plane CSA `WeightedCsa3GenSpec`
(`B₀ + B₁ + B₂` Inputs of Weights `{1, 2, 4}`) -/

/-- Initial weight list for `(B₀, B₁, B₂)` 3-plane inputs (`B₀` of weight `1`, `B₁` of weight `2`,
`B₂` of weight `4`) followed by `S` clean carry wires of weight `0`. -/
def init3PlaneGenWeights (B₀ B₁ B₂ S : ℕ) : List ℕ :=
  List.replicate B₀ 1 ++ List.replicate B₁ 2 ++ List.replicate B₂ 4 ++ List.replicate S 0

structure WeightedCsa3GenSpec (B₀ B₁ B₂ K S : ℕ) where
  steps : List InPlaceStep
  outWires : Fin K → Wire ((B₀ + B₁ + B₂) + S)
  cinWire : Option (Wire ((B₀ + B₁ + B₂) + S))
  hLen : steps.length = S
  hValid : validInPlaceSteps (B₀ + B₁ + B₂) steps = true
  hOutInj : Function.Injective outWires
  hCinNe : ∀ cw k, cinWire = some cw → cw ≠ outWires k
  hRun : runWeightList (B₀ + B₁ + B₂) steps (init3PlaneGenWeights B₀ B₁ B₂ S) =
    some (expectedOutWeightsCin outWires cinWire)

def WeightedCsa3GenSpec.outWire {B₀ B₁ B₂ K S M : ℕ} (spec : WeightedCsa3GenSpec B₀ B₁ B₂ K S)
    (cur : ℕ) (inWires : Fin (B₀ + B₁ + B₂) → Wire M) (hbound : cur + S ≤ M)
    (k : Fin K) : Wire M :=
  embedPopWire cur inWires hbound (spec.outWires k)

def WeightedCsa3GenSpec.cinOutWire {B₀ B₁ B₂ K S M : ℕ} (spec : WeightedCsa3GenSpec B₀ B₁ B₂ K S)
    (cur : ℕ) (inWires : Fin (B₀ + B₁ + B₂) → Wire M) (hbound : cur + S ≤ M) : Option (Wire M) :=
  spec.cinWire.map (embedPopWire cur inWires hbound)

theorem WeightedCsa3GenSpec.outWire_lt {B₀ B₁ B₂ K S M : ℕ}
    (spec : WeightedCsa3GenSpec B₀ B₁ B₂ K S)
    (cur : ℕ) (inWires : Fin (B₀ + B₁ + B₂) → Wire M)
    (hLt : ∀ i : Fin (B₀ + B₁ + B₂), (inWires i).val < cur) (hbound : cur + S ≤ M) (k : Fin K) :
    (spec.outWire cur inWires hbound k).val < cur + S :=
  embedPopWire_lt cur inWires hLt hbound (spec.outWires k)

theorem WeightedCsa3GenSpec.outWire_ge {B₀ B₁ B₂ K S M targetEnd : ℕ}
    (spec : WeightedCsa3GenSpec B₀ B₁ B₂ K S) (cur : ℕ)
    (inWires : Fin (B₀ + B₁ + B₂) → Wire M)
    (hGe : ∀ i : Fin (B₀ + B₁ + B₂), targetEnd ≤ (inWires i).val) (hCurGe : targetEnd ≤ cur)
    (hbound : cur + S ≤ M) (k : Fin K) : targetEnd ≤ (spec.outWire cur inWires hbound k).val
    := embedPopWire_ge_of_above cur inWires hGe hCurGe hbound (spec.outWires k)

def withWeightedCsa3Gen {B₀ B₁ B₂ K S M : ℕ} (spec : WeightedCsa3GenSpec B₀ B₁ B₂ K S)
    (cur : ℕ) (inWires : Fin (B₀ + B₁ + B₂) → Wire M) (hInj : Function.Injective inWires)
    (hLt : ∀ i : Fin (B₀ + B₁ + B₂), (inWires i).val < cur) (hbound : cur + S ≤ M)
    (body : InPlaceFullAddSlice.TempPhaseProg M) : InPlaceFullAddSlice.TempPhaseProg M :=
  withInPlaceSteps cur (remapSteps cur inWires spec.steps)
    (by simp [spec.hLen, hbound])
    (remapSteps_valid_aux cur inWires hInj hLt 0 spec.steps (by simpa using spec.hValid))
    body

@[simp] theorem withWeightedCsa3Gen_countTempAnd {B₀ B₁ B₂ K S M : ℕ}
    (spec : WeightedCsa3GenSpec B₀ B₁ B₂ K S) (cur : ℕ)
    (inWires : Fin (B₀ + B₁ + B₂) → Wire M) (hInj : Function.Injective inWires)
    (hLt : ∀ i : Fin (B₀ + B₁ + B₂), (inWires i).val < cur) (hbound : cur + S ≤ M)
    (body : InPlaceFullAddSlice.TempPhaseProg M) : (withWeightedCsa3Gen spec cur inWires hInj
    hLt hbound body).countTempAnd = S + body.countTempAnd := by
  simp [withWeightedCsa3Gen, spec.hLen]

def evalWeightedCsa3Gen {B₀ B₁ B₂ K S M : ℕ} (spec : WeightedCsa3GenSpec B₀ B₁ B₂ K S)
    (cur : ℕ) (inWires : Fin (B₀ + B₁ + B₂) → Wire M)
    (hInj : Function.Injective inWires) (hLt : ∀ i : Fin (B₀ + B₁ + B₂), (inWires i).val < cur)
    (hbound : cur + S ≤ M) (β : BitAssignment M) : BitAssignment M :=
  evalInPlaceSteps cur (remapSteps cur inWires spec.steps)
    (by simp [spec.hLen, hbound])
    (remapSteps_valid_aux cur inWires hInj hLt 0 spec.steps (by simpa using spec.hValid))
    β

theorem TargetBlock.withWeightedCsa3Gen_block {B₀ B₁ B₂ K S M targetEnd : ℕ}
    (spec : WeightedCsa3GenSpec B₀ B₁ B₂ K S) (cur : ℕ)
    (inWires : Fin (B₀ + B₁ + B₂) → Wire M) (hInj : Function.Injective inWires)
    (hGe : ∀ i : Fin (B₀ + B₁ + B₂), targetEnd ≤ (inWires i).val)
    (hLt : ∀ i : Fin (B₀ + B₁ + B₂), (inWires i).val < cur) (hCurGe : targetEnd ≤ cur)
    (hbound : cur + S ≤ M) {fBody : BitAssignment M → BitAssignment M}
    {sBody : BitAssignment M → ZMod 2} {body : InPlaceFullAddSlice.TempPhaseProg M}
    (hBody : TargetBlock M targetEnd (M - (cur + S)) fBody sBody body) : TargetBlock M
    targetEnd (M - cur) (fun β ↦ fBody (evalWeightedCsa3Gen spec cur inWires hInj hLt hbound
    β)) (fun β ↦ sBody (evalWeightedCsa3Gen spec cur inWires hInj hLt hbound β))
    (withWeightedCsa3Gen spec cur inWires hInj hLt hbound body) := by
  have hBody' : TargetBlock M targetEnd (M - (cur + (remapSteps cur inWires spec.steps).length))
      fBody sBody body := by
    simpa [spec.hLen] using hBody
  exact TargetBlock.withInPlaceSteps_block cur _ _ _
    (remapSteps_above cur inWires hGe hCurGe spec.steps) hBody'

/-! ## Section 3: Generalized 3-Plane Weighted Modular Addition (`dWeightedGenModAdd`) -/

end ConfigHybridStream1300

end HybridStream1300

end
end HybridStream1300

section TempPhaseProg
local instance (priority := 1000000) instNeZeroTwoPow_TempPhaseProg (k : ℕ) :
    NeZero (2 ^ k) := ⟨(Nat.two_pow_pos k).ne'⟩

/-
# Clean-Workspace Temporary-AND Phase Programs (`TempPhaseProg`)

General, algorithm-independent combinators for synthesizing zero-`.TOFF` clean-workspace
`DynamicCircuit` phase oracles (`phaseDiagUnitary pred`) at `4` `T` gates per temporary AND
(`DynamicCircuit.andCompute` + `0`-`T` `DynamicCircuit.andUncompute`), with arbitrary clean-wire
allocation and `0`-`T` Clifford scratch recycling across sequential stages.

Key exports in `StoppingPowerSolution`:
- `CliffProg`: pure-Clifford reversible sub-language (`nil`, `x`, `cnot`, `seq`) with `.inv`
  (`0` `T`, `0` `.TOFF`).
- `TempPhaseProg`: structured reversible + phase AST (`nil`, `cliff`, `z`, `seq`, `tempAnd`)
  compiling to `DynamicCircuit` with `count .TOFF = 0` and exact `count .T = 4 * countTempAnd`.
- `ValidCleanRem`, `ScopedBlock`, `realizes_of_validCleanRem`, and
  `realizes_phaseDiagUnitary_cleanWorkspace`: asymmetric clean-tail invariant supporting both
  `0`-`T` buffer allocation/deallocation and `4`-`T` temporary-AND uncomputation, plus one-call
  QHL bridge to `DynamicCircuit.RealizesEmbeddedUnitaryWithCleanWorkspace` over arbitrary
  `[Fintype Var] [DecidableEq Var]`.
- Verified arithmetic, logic, and lookup combinators (`ScopedBlock` + exact `countTempAnd`):
  `withCliffAlloc`, `ScopedBlock.withSelfInvCompute`, `withTempBit`, `andXor`, `withHalfAdd`,
  `withFullAdd`, `withRippleAdd`, `withLtCompLoop`, `withAndChain`, `withUnarySplit`,
  `withUnaryTree`, `fanoutUnaryBit`, and `withSelectSwapB2`.
-/

public section

section SharedScope

open Operator Matrix _root_.DynamicCircuit DynCircuitExt QProg HermitianMat
open MeasureBranchHadamardSem
open StreamingBchComparator
open scoped Matrix ComplexOrder MatrixOrder Circuit.Notation

/-- 5-CNOT in-place Gidney full-adder scope (`1` `tempAnd` = `4 T`, `0` `T` measurement uncompute,
allocates **only one** clean carry wire `coutWire = ⟨cur, hcur⟩` instead of two clean wires:
`b ↦ a + b + c`, `coutWire ↦ (b + a) * (c + a) + a = maj3(a, b, c)`, leaving `a, c` intact). -/
def withInPlaceFullAdd {M : ℕ} (cur : ℕ) (hcur : cur + 1 ≤ M) (a b c : Wire M) (hab : a ≠ b)
    (hac : a ≠ c) (hbc : b ≠ c) (ha : a.val < cur) (hb : b.val < cur) (hc : c.val < cur)
    (body : TempPhaseProg M) : TempPhaseProg M :=
  let coutWire : Wire M := ⟨cur, hcur⟩
  let cPre : CliffProg M := .seq (.cnot a b hab) (.cnot a c hac)
  let cInner : CliffProg M :=
    .seq (.cnot a coutWire (wire_ne_of_lt (by dsimp [coutWire]; omega)))
      (.seq (.cnot a c hac) (.cnot c b hbc.symm))
  withCliffAlloc cPre
    (withTempBit b c coutWire hbc
      (wire_ne_of_lt (by dsimp [coutWire]; omega))
      (wire_ne_of_lt (by dsimp [coutWire]; omega))
      (withCliffAlloc cInner body))

@[simp] theorem withInPlaceFullAdd_countTempAnd {M : ℕ} (cur : ℕ) (hcur : cur + 1 ≤ M)
    (a b c : Wire M) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (ha : a.val < cur)
    (hb : b.val < cur) (hc : c.val < cur) (body : TempPhaseProg M) : (withInPlaceFullAdd cur
    hcur a b c hab hac hbc ha hb hc body).countTempAnd = 1 + body.countTempAnd := by
  simp [withInPlaceFullAdd]

/-- Exact wire transformation of `withInPlaceFullAdd`: `b` receives `a + b + c` in place and
`⟨cur, hcur⟩` receives `maj3(a, b, c) = (b + a) * (c + a) + a`, with all other wires untouched. -/
def inPlaceFullAddSetup {M : ℕ} (cur : ℕ) (hcur : cur + 1 ≤ M) (a b c : Wire M)
    (β : BitAssignment M) : BitAssignment M := Function.update
    (Function.update β b (β a + β b + β c)) ⟨cur, hcur⟩ ((β b + β a) * (β c + β a) + β a)

theorem ScopedBlock.withInPlaceFullAdd_block {M : ℕ} (cur : ℕ) (hcur : cur + 1 ≤ M)
    (a b c : Wire M) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (ha : a.val < cur)
    (hb : b.val < cur) (hc : c.val < cur) {sBody : BitAssignment M → BitAssignment M}
    {leaf body : TempPhaseProg M} (hBody : ScopedBlock M (M - (cur + 1)) sBody leaf body) :
    ScopedBlock M (M - cur) (sBody ∘ inPlaceFullAddSetup cur hcur a b c) leaf
      (withInPlaceFullAdd cur hcur a b c hab hac hbc ha hb hc body) := by
  let coutWire : Wire M := ⟨cur, hcur⟩
  let cPre : CliffProg M := .seq (.cnot a b hab) (.cnot a c hac)
  let cInner : CliffProg M := .seq (.cnot a coutWire (wire_ne_of_lt ha))
      (.seq (.cnot a c hac) (.cnot c b hbc.symm))
  have h1 := ScopedBlock.withCliffAlloc_block (rem := M - (cur + 1)) (by omega) le_rfl cInner
    ⟨⟨by omega, by dsimp [coutWire]; omega⟩, ⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩ hBody
  have h2 := ScopedBlock.withTempBit_block (M := M) cur hcur b c hbc hb hc h1
  have h3 := ScopedBlock.withCliffAlloc_block (M := M) (rem := M - cur) (remIn := M - cur)
    (by omega) le_rfl cPre ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩ h2
  refine ⟨h3.valid, h3.bits, fun β hβ ↦ (h3.sign β hβ).trans ?_⟩
  dsimp only [Function.comp_apply, inPlaceFullAddSetup, cPre, cInner, CliffProg.eval]
  congr 2
  have hacout : a ≠ coutWire := wire_ne_of_lt ha
  have hbcout : b ≠ coutWire := wire_ne_of_lt hb
  have hccout : c ≠ coutWire := wire_ne_of_lt hc
  dsimp only [coutWire] at hacout hbcout hccout ⊢
  funext w
  rcases eq_or_ne w ⟨cur, hcur⟩ with rfl | hw_co
  · simp only [Function.update_self, Function.update_of_ne, ne_eq, not_false_eq_true,
      hacout, hbcout, hbcout.symm, hccout, hccout.symm, hab, hac, hbc, hbc.symm]
  · rcases eq_or_ne w b with rfl | hw_b
    · simp only [Function.update_self, Function.update_of_ne, ne_eq, not_false_eq_true,
        hw_co, hacout, hccout, hab, hac, hbc, hbc.symm,
        add_assoc, CharTwo.add_self_eq_zero, add_zero]
      ring
    · rcases eq_or_ne w c with rfl | hw_c
      · simp only [Function.update_self, Function.update_of_ne, ne_eq, not_false_eq_true,
          hw_co, hw_b, Ne.symm hw_b, hacout, hbcout, hab, hac,
          add_assoc, CharTwo.add_self_eq_zero, add_zero]
      · simp only [Function.update_of_ne, ne_eq, not_false_eq_true, hw_co, hw_b, hw_c]

end SharedScope
end
end TempPhaseProg

section MomSlot0LocalAndMomCombine288
local instance (priority := 1000000) instNeZeroTwoPow_MomSlot0LocalAndMomCombine288 (k : ℕ) :
    NeZero (2 ^ k) := ⟨(Nat.two_pow_pos k).ne'⟩

public section

/-
# Hoisted Local `Slot 0`, Fast `Slot 1`, and 4-Slot Momentum Combiner (`mWork <= 288`, `0` `TOFF`)

Provides the self-contained momentum local-oracle and combiner
(polymorphic across every `{mPayload : ℕ}` with `hmPay : 80 ≤ mPayload`, covering both
`mPayload = 80` and `mPayload = 158` by definitional `rfl`):

1. Reusable clean-workspace `TempPhaseProg` combinators:
   - `withInPlaceFullAdd` / `withInPlaceAddCarry`: pure-`ScopedBlock` Gidney in-place unsigned
     adder updating a `(W + 1)`-wire accumulator register inside `body` using only `W` clean
     carry wires (`0` uncompute `T` gates, `4 * W` `T` gates total, `evalBits = id`).
   - `XorScope` / `xorLoadB2` / `ScopedBlock.withXorLoadB2_block`: `B = 2` `SELECTSWAP` classical
     table XOR-loader directly reusing `TempPhaseProg.withUnaryTree` and immediately releasing all
     `2 ^ d + 2` scratch wires back to `|0⟩` at `0` uncompute `T` gates (`2 ^ d - 1 + W`
     `tempAnd`s, `evalSign = 0`, self-inverse on clean inputs).
   - `withMuxBit` / `withMuxReg`: pure-`ScopedBlock` clean register multiplexers (`1`
     `tempAnd`/bit).
2. `swapElec0Bits`, `uSlot0Local`, and `dSlot0LocalDyn`:
   - `rElec[0]`-local `Slot 0` (`coin = 4`) electron kinetic phase circuit at `mClean = 288 ≤ 288`,
     `T = 960`, and `0` `TOFF`, together with exact on-coin and global conjugation
     `unitaryConj (uBarrel cfg) (uSlot0Local hmPay w_eff) = slot0SelectUnitary hmPay w_eff`.
3. `dSlot1FastDyn` and `slot1FastMomOracleSym` / `slot1FastMomOracle` / `slot1FastMomOracle158`:
   - `4-T/tempAnd` `TempPhaseProg` projectile kinetic phase circuit for `Slot 1` (`coin = 5`) at
     `mClean = 270 ≤ 288`, `T = 4624`, `0` `TOFF`,
     realizing the exact `slot1SelectUnitary hmPay w_eff cfg` unconditionally for all `w_eff : ℝ`,
     plus automatic high-wire commutation with any `uBarrel` preserving `q ≥ 3924`.
4. `MomLocalSlotData`, `slot0LocalData`, `slot1FastData`, `liftOracleWithIdOnCoin`,
   `slot5WrapCoreLocalData`, `CombinedLocalMomData`, and `combineFourLocalMomSlots`:
   - Single-pass sequential combiner producing all `HoistedMomLocalBundle` fields
     (`tMomLocal = t0 + t1 + t3 + t5`,
     `mWorkSelect ≥ max`, `0` `TOFF`, `hCoin4..hCoin7`) plus global conjugation equality against
     `FullSysMomSlots0135Concrete.combineFourMomSlotOracles`.
-/

namespace MomSlot0LocalAndMomCombine288

open Real Operator Matrix _root_.DynamicCircuit DynCircuitExt QProg HermitianMat
open MomSlots01Slot1ProjKinetic hiding padZeroBits phaseDiagUnitary
open scoped Matrix ComplexOrder MatrixOrder BigOperators

/- ## Section 1: Reusable `TempPhaseProg` Combinators
(`withInPlaceAddCarry`, `xorLoadB2`, `withMuxReg`) -/

/-- Setup transformation of one Gidney in-place full-adder step: replaces `b` by `a + b + cin`,
places `cin + (a + cin) * (b + cin)` on clean carry wire `⟨cur, hcur⟩`,
and leaves every other wire unchanged. -/
def inPlaceFullAddSetup {M : ℕ} (cur : ℕ) (hcur : cur + 1 ≤ M) (a b cin : Wire M)
    (β : BitAssignment M) : BitAssignment M := Function.update
    (Function.update β b (β a + β b + β cin)) ⟨cur, hcur⟩
    (β cin + (β a + β cin) * (β b + β cin))

/-- Pure-`ScopedBlock` Gidney in-place full-adder step (`1` `tempAnd` = `4 T`,
allocates `1` clean wire
`cout = ⟨cur, hcur⟩`, sets `b ↦ a + b + cin` and `cout ↦ carry` inside `body`,
and restores all wires
including `b` and `cout` at `0` extra `T` gates when `body` exits). -/
def withInPlaceFullAdd {M : ℕ} (cur : ℕ) (hcur : cur + 1 ≤ M) (a b cin : Wire M) (hab : a ≠ b)
    (hac : a ≠ cin) (hbc : b ≠ cin) (ha : a.val < cur) (hb : b.val < cur) (hc : cin.val < cur)
    (body : TempPhaseProg M) : TempPhaseProg M :=
  let cout : Wire M := ⟨cur, hcur⟩
  let cPre : CliffProg M := .seq (.cnot cin a hac.symm) (.cnot cin b hbc.symm)
  let cInner : CliffProg M := .seq (.cnot cin a hac.symm)
      (.seq (.cnot a b hab) (.cnot cin cout (wire_ne_of_lt hc)))
  withCliffAlloc cPre
    (withTempBit a b cout hab (wire_ne_of_lt ha) (wire_ne_of_lt hb)
      (withCliffAlloc cInner body))

@[simp] theorem withInPlaceFullAdd_countTempAnd {M : ℕ} (cur : ℕ) (hcur : cur + 1 ≤ M)
    (a b cin : Wire M) (hab : a ≠ b) (hac : a ≠ cin) (hbc : b ≠ cin) (ha : a.val < cur)
    (hb : b.val < cur) (hc : cin.val < cur) (body : TempPhaseProg M) : (withInPlaceFullAdd cur
    hcur a b cin hab hac hbc ha hb hc body).countTempAnd = 1 + body.countTempAnd := by
  simp [withInPlaceFullAdd]

theorem ScopedBlock.withInPlaceFullAdd_block {M : ℕ} (cur : ℕ) (hcur : cur + 1 ≤ M)
    (a b cin : Wire M) (hab : a ≠ b) (hac : a ≠ cin) (hbc : b ≠ cin) (ha : a.val < cur)
    (hb : b.val < cur) (hc : cin.val < cur) {sBody : BitAssignment M → BitAssignment M}
    {leaf body : TempPhaseProg M} (hBody : ScopedBlock M (M - (cur + 1)) sBody leaf body) :
    ScopedBlock M (M - cur) (sBody ∘ inPlaceFullAddSetup cur hcur a b cin) leaf
      (withInPlaceFullAdd cur hcur a b cin hab hac hbc ha hb hc body) := by
  let cout : Wire M := ⟨cur, hcur⟩
  let cPre : CliffProg M := .seq (.cnot cin a hac.symm) (.cnot cin b hbc.symm)
  let cInner : CliffProg M := .seq (.cnot cin a hac.symm)
      (.seq (.cnot a b hab) (.cnot cin cout (wire_ne_of_lt hc)))
  have h1 := ScopedBlock.withCliffAlloc_block (rem := M - (cur + 1)) (by omega) le_rfl cInner
    ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩, ⟨by omega, by dsimp [cout]; omega⟩⟩ hBody
  have h2 := ScopedBlock.withTempBit_block (M := M) cur hcur a b hab ha hb h1
  have h3 := ScopedBlock.withCliffAlloc_block (M := M) (rem := M - cur) (remIn := M - cur)
    (by omega) le_rfl cPre ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩ h2
  refine ⟨h3.valid, h3.bits, fun β hβ ↦ (h3.sign β hβ).trans ?_⟩
  dsimp only [Function.comp_apply, inPlaceFullAddSetup, cPre, cInner, CliffProg.eval]
  congr 2
  have hacout : a ≠ cout := wire_ne_of_lt ha
  have hbcout : b ≠ cout := wire_ne_of_lt hb
  have hccout : cin ≠ cout := wire_ne_of_lt hc
  dsimp only [cout] at hacout hbcout hccout ⊢
  funext w
  rcases eq_or_ne w ⟨cur, hcur⟩ with rfl | hwo
  · simp only [Function.update_self, Function.update_of_ne, ne_eq, not_false_eq_true,
      hacout, hacout.symm, hbcout, hbcout.symm, hccout, hab, hab.symm, hac.symm, hbc.symm]
    ring
  · rcases eq_or_ne w b with rfl | hwb
    · simp only [Function.update_self, Function.update_of_ne, ne_eq, not_false_eq_true,
        hwo, Ne.symm hwo, hacout, hacout.symm, hccout, hab, hab.symm, hac.symm, hbc.symm,
        add_assoc, CharTwo.add_self_eq_zero, add_zero]
      ring
    · rcases eq_or_ne w a with rfl | hwa
      · simp only [Function.update_self, Function.update_of_ne, ne_eq, not_false_eq_true,
          hwo, Ne.symm hwo, hwb, Ne.symm hwb, hbcout, hbcout.symm, hccout, hac.symm, hbc.symm,
          add_assoc, CharTwo.add_self_eq_zero, add_zero]
      · simp only [Function.update_of_ne, ne_eq, not_false_eq_true, hwo, hwb, hwa]

open MeasureBranchHadamardSem hiding ket matrix_ext_ket
open scoped Circuit.Notation

attribute [local irreducible] withLtCompLoop

/-! ### Sub-Block 4: `dPhaseAnf8`, `slot1PreProg`, & `dSlot1FastDyn` (`2752 T`, `mWork >= 270`) -/

/- ## Section 4: `MomLocalSlotData`, Per-Slot Turnkey Wrappers & `combineFourLocalMomSlots` -/

end MomSlot0LocalAndMomCombine288
end
end MomSlot0LocalAndMomCombine288

end QuantumComputation.Specs.StoppingPowerSolution
