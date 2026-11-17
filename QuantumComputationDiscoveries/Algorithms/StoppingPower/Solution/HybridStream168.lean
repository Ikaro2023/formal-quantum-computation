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

public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.InterWalkSum42Hoist

set_option Elab.async false

@[expose] public section

namespace QuantumComputation.Specs.StoppingPowerSolution
open SpecsAux

section ModHybridStream168
@[expose] public section
namespace HybridStream168Aux
section ConfigHybridStream168
set_option exponentiation.threshold 256
set_option maxRecDepth 4096
open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt
open scoped Matrix BigOperators Circuit.Notation
open SpecsAux.SpecMirror
open DyadicQft64 hiding dyadicTurn phaseGradKet optBitVal
open FullSysCatSegmentBridge (fullSysCoreWires)
open InPlaceFullAddSlice InPlaceStepEngine
open NuclearTwistRealizes
open SinglePassNuclearTwist288
open HybridStream288Aux
local instance (priority := 1000000) instNeZeroTwoPowHybridStream168 (k : ℕ) : NeZero (2 ^ k) :=
  ⟨Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos k)⟩
def init3PlaneGenWeights (B₀ B₁ B₂ S : ℕ) : List ℕ :=
  List.replicate B₀ 1 ++ List.replicate B₁ 2 ++ List.replicate B₂ 4 ++ List.replicate S 0
theorem listGet_init3PlaneGenWeights (B₀ B₁ B₂ S : ℕ) (q : Wire ((B₀ + B₁ + B₂) + S)) :
    listGet (init3PlaneGenWeights B₀ B₁ B₂ S) q.val = if q.val < B₀ then 1 else if q.val < B₀
    + B₁ then 2 else if q.val < B₀ + B₁ + B₂ then 4 else 0 := by
  have _hq := q.isLt
  unfold init3PlaneGenWeights
  simp only [listGet_append, List.length_append, List.length_replicate]
  split_ifs <;> first | omega | exact listGet_replicate _ _ _ (by omega)
theorem wSum_init3PlaneGenWeights {B₀ B₁ B₂ S : ℕ} (β₀ : BitAssignment ((B₀ + B₁ + B₂) + S)) :
    wSum (init3PlaneGenWeights B₀ B₁ B₂ S) β₀ =
      (∑ i : Fin B₀, (β₀ ⟨i.val, by omega⟩).val) +
        (∑ i : Fin B₁, 2 * (β₀ ⟨B₀ + i.val, by omega⟩).val) +
        (∑ i : Fin B₂, 4 * (β₀ ⟨(B₀ + B₁) + i.val, by omega⟩).val) := by
  unfold wSum
  simp_rw [listGet_init3PlaneGenWeights B₀ B₁ B₂ S]
  rw [Fin.sum_univ_add, Fin.sum_univ_add, Fin.sum_univ_add]
  rw [Finset.sum_eq_zero fun (i : Fin S) _ ↦ by
    have : (Fin.natAdd (B₀ + B₁ + B₂) i).val = (B₀ + B₁ + B₂) + i.val := rfl
    split_ifs <;> omega, add_zero]
  refine congrArg₂ (· + ·) (congrArg₂ (· + ·)
    (Finset.sum_congr rfl fun i _ ↦ ?_) (Finset.sum_congr rfl fun i _ ↦ ?_))
    (Finset.sum_congr rfl fun i _ ↦ ?_)
  · rw [show Fin.castAdd S (Fin.castAdd B₂ (Fin.castAdd B₁ i)) = ⟨i.val, by omega⟩ from
      Fin.ext rfl]
    simp only [i.isLt, ↓reduceIte, one_mul]
  · rw [show Fin.castAdd S (Fin.castAdd B₂ (Fin.natAdd B₀ i)) = ⟨B₀ + i.val, by omega⟩ from
      Fin.ext rfl]
    simp only [show ¬B₀ + i.val < B₀ by omega,
      show B₀ + i.val < B₀ + B₁ by omega, ↓reduceIte]
  · rw [show Fin.castAdd S (Fin.natAdd (B₀ + B₁) i) = ⟨(B₀ + B₁) + i.val, by omega⟩ from
      Fin.ext rfl]
    simp only [show ¬(B₀ + B₁) + i.val < B₀ by omega,
      show ¬(B₀ + B₁) + i.val < B₀ + B₁ by omega,
      show (B₀ + B₁) + i.val < B₀ + B₁ + B₂ by omega, ↓reduceIte]
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
    (cur : ℕ) (inWires : Fin (B₀ + B₁ + B₂) → Wire M) (hbound : cur + S ≤ M) (k : Fin K) : Wire M :=
  embedPopWire cur inWires hbound (spec.outWires k)
def WeightedCsa3GenSpec.cinOutWire {B₀ B₁ B₂ K S M : ℕ} (spec : WeightedCsa3GenSpec B₀ B₁ B₂ K S)
    (cur : ℕ) (inWires : Fin (B₀ + B₁ + B₂) → Wire M) (hbound : cur + S ≤ M) : Option (Wire M) :=
  spec.cinWire.map (embedPopWire cur inWires hbound)
theorem WeightedCsa3GenSpec.outWire_injective {B₀ B₁ B₂ K S M : ℕ}
    (spec : WeightedCsa3GenSpec B₀ B₁ B₂ K S) (cur : ℕ)
    (inWires : Fin (B₀ + B₁ + B₂) → Wire M) (hInj : Function.Injective inWires)
    (hLt : ∀ i : Fin (B₀ + B₁ + B₂), (inWires i).val < cur) (hbound : cur + S ≤ M) :
    Function.Injective (spec.outWire cur inWires hbound) :=
  (embedPopWire_injective cur inWires hInj hLt hbound).comp spec.hOutInj
theorem WeightedCsa3GenSpec.outWire_lt {B₀ B₁ B₂ K S M : ℕ}
    (spec : WeightedCsa3GenSpec B₀ B₁ B₂ K S) (cur : ℕ) (inWires : Fin (B₀ + B₁ + B₂) → Wire M)
    (hLt : ∀ i : Fin (B₀ + B₁ + B₂), (inWires i).val < cur) (hbound : cur + S ≤ M) (k : Fin K) :
    (spec.outWire cur inWires hbound k).val < cur + S :=
  embedPopWire_lt cur inWires hLt hbound (spec.outWires k)
theorem WeightedCsa3GenSpec.outWire_ge {B₀ B₁ B₂ K S M targetEnd : ℕ}
    (spec : WeightedCsa3GenSpec B₀ B₁ B₂ K S) (cur : ℕ) (inWires : Fin (B₀ + B₁ + B₂) → Wire M)
    (hGe : ∀ i : Fin (B₀ + B₁ + B₂), targetEnd ≤ (inWires i).val) (hCurGe : targetEnd ≤ cur)
    (hbound : cur + S ≤ M) (k : Fin K) : targetEnd ≤ (spec.outWire cur inWires hbound k).val :=
  embedPopWire_ge_of_above cur inWires hGe hCurGe hbound (spec.outWires k)
theorem WeightedCsa3GenSpec.cinOutWire_eq_some {B₀ B₁ B₂ K S M : ℕ}
    (spec : WeightedCsa3GenSpec B₀ B₁ B₂ K S) (cur : ℕ)
    (inWires : Fin (B₀ + B₁ + B₂) → Wire M) (hbound : cur + S ≤ M) {c : Wire M}
    (hc : spec.cinOutWire cur inWires hbound = some c) :
    ∃ cw, spec.cinWire = some cw ∧ c = embedPopWire cur inWires hbound cw := by
  obtain ⟨cw, hcw, rfl⟩ := Option.map_eq_some_iff.mp hc
  exact ⟨cw, hcw, rfl⟩
theorem WeightedCsa3GenSpec.cinOutWire_lt {B₀ B₁ B₂ K S M : ℕ}
    (spec : WeightedCsa3GenSpec B₀ B₁ B₂ K S) (cur : ℕ)
    (inWires : Fin (B₀ + B₁ + B₂) → Wire M)
    (hLt : ∀ i : Fin (B₀ + B₁ + B₂), (inWires i).val < cur) (hbound : cur + S ≤ M) {c : Wire M}
    (hc : spec.cinOutWire cur inWires hbound = some c) : c.val < cur + S := by
  obtain ⟨cw, _, rfl⟩ := spec.cinOutWire_eq_some cur inWires hbound hc
  exact embedPopWire_lt cur inWires hLt hbound cw
theorem WeightedCsa3GenSpec.cinOutWire_ge {B₀ B₁ B₂ K S M targetEnd : ℕ}
    (spec : WeightedCsa3GenSpec B₀ B₁ B₂ K S) (cur : ℕ)
    (inWires : Fin (B₀ + B₁ + B₂) → Wire M)
    (hGe : ∀ i : Fin (B₀ + B₁ + B₂), targetEnd ≤ (inWires i).val) (hCurGe : targetEnd ≤ cur)
    (hbound : cur + S ≤ M) {c : Wire M} (hc : spec.cinOutWire cur inWires hbound = some c) :
    targetEnd ≤ c.val := by
  obtain ⟨cw, _, rfl⟩ := spec.cinOutWire_eq_some cur inWires hbound hc
  exact embedPopWire_ge_of_above cur inWires hGe hCurGe hbound cw
theorem WeightedCsa3GenSpec.cinOutWire_ne_outWire {B₀ B₁ B₂ K S M : ℕ}
    (spec : WeightedCsa3GenSpec B₀ B₁ B₂ K S) (cur : ℕ)
    (inWires : Fin (B₀ + B₁ + B₂) → Wire M) (hInj : Function.Injective inWires)
    (hLt : ∀ i : Fin (B₀ + B₁ + B₂), (inWires i).val < cur) (hbound : cur + S ≤ M) {c : Wire M}
    (hc : spec.cinOutWire cur inWires hbound = some c) (k : Fin K) : c ≠ spec.outWire cur
    inWires hbound k := by
  obtain ⟨cw, hcw, rfl⟩ := spec.cinOutWire_eq_some cur inWires hbound hc
  exact (embedPopWire_injective cur inWires hInj hLt hbound).ne (spec.hCinNe cw k hcw)
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
  exact TargetBlock.withInPlaceSteps_block cur _ _ _
    (remapSteps_above cur inWires hGe hCurGe spec.steps) (by simpa [spec.hLen] using hBody)
theorem evalWeightedCsa3Gen_sum_eq {B₀ B₁ B₂ K S M : ℕ}
    (spec : WeightedCsa3GenSpec B₀ B₁ B₂ K S)
    (cur : ℕ) (inWires : Fin (B₀ + B₁ + B₂) → Wire M)
    (hInj : Function.Injective inWires) (hLt : ∀ i : Fin (B₀ + B₁ + B₂), (inWires i).val < cur)
    (hbound : cur + S ≤ M) (β : BitAssignment M) :
    (∑ k : Fin K, 2 ^ k.val *
        (evalWeightedCsa3Gen spec cur inWires hInj hLt hbound β
          (spec.outWire cur inWires hbound k)).val) +
      optBitVal (spec.cinOutWire cur inWires hbound)
        (evalWeightedCsa3Gen spec cur inWires hInj hLt hbound β) =
      (∑ i : Fin B₀, (β (inWires ⟨i.val, by omega⟩)).val) +
        (∑ i : Fin B₁, 2 * (β (inWires ⟨B₀ + i.val, by omega⟩)).val) +
        (∑ i : Fin B₂, 4 * (β (inWires ⟨(B₀ + B₁) + i.val, by omega⟩)).val) := by
  let φ := embedPopWire cur inWires hbound
  have hsim := (evalInPlaceSteps_remap_sim cur inWires hInj hLt hbound 0 spec.steps
    (by simp [spec.hLen]) (by simpa using spec.hValid) β).1
  have hpull (k : Fin K) :
      evalWeightedCsa3Gen spec cur inWires hInj hLt hbound β (spec.outWire cur inWires hbound k) =
        evalInPlaceSteps (B₀ + B₁ + B₂) spec.steps (by simp [spec.hLen]) spec.hValid (β ∘ φ)
          (spec.outWires k) := by
    simpa [evalWeightedCsa3Gen, WeightedCsa3GenSpec.outWire,
      φ] using congrFun hsim (spec.outWires k)
  have hpullCin : optBitVal (spec.cinOutWire cur inWires hbound)
      (evalWeightedCsa3Gen spec cur inWires hInj hLt hbound β) = optBitVal spec.cinWire
      (evalInPlaceSteps (B₀ + B₁ + B₂) spec.steps (by simp [spec.hLen]) spec.hValid (β ∘ φ)) := by
    rcases hcw : spec.cinWire with _ | cw
    · simp [WeightedCsa3GenSpec.cinOutWire, hcw, optBitVal]
    · simpa [WeightedCsa3GenSpec.cinOutWire, hcw, optBitVal, evalWeightedCsa3Gen, φ] using
        congrArg ZMod.val (congrFun hsim cw)
  simp_rw [hpull]
  rw [hpullCin, ← wSum_expectedOutWeightsCin spec.outWires spec.cinWire,
    runWeightList_preserves_wSum (B₀ + B₁ + B₂) spec.steps (by simp [spec.hLen]) spec.hValid
      (init3PlaneGenWeights B₀ B₁ B₂ S) (expectedOutWeightsCin spec.outWires spec.cinWire)
      (by simp only [init3PlaneGenWeights, List.length_append, List.length_replicate])
      spec.hRun (β ∘ φ), wSum_init3PlaneGenWeights]
  refine congrArg₂ (· + ·) (congrArg₂ (· + ·) (Finset.sum_congr rfl ?_) (Finset.sum_congr rfl ?_))
    (Finset.sum_congr rfl ?_)
  all_goals
    intro i _
    dsimp only [Function.comp_apply, φ, embedPopWire]
    rw [dite_eq_left (by omega)]
theorem evalWeightedCsa3Gen_untouched {B₀ B₁ B₂ K S M : ℕ}
    (spec : WeightedCsa3GenSpec B₀ B₁ B₂ K S) (cur : ℕ)
    (inWires : Fin (B₀ + B₁ + B₂) → Wire M) (hInj : Function.Injective inWires)
    (hLt : ∀ i : Fin (B₀ + B₁ + B₂), (inWires i).val < cur) (hbound : cur + S ≤ M)
    (β : BitAssignment M) (w : Wire M) (hNotIn : ∀ i : Fin (B₀ + B₁ + B₂), w ≠ inWires i)
    (hNotCarry : ¬(cur ≤ w.val ∧ w.val < cur + S)) : evalWeightedCsa3Gen spec cur inWires hInj
    hLt hbound β w = β w := by
  refine (evalInPlaceSteps_remap_sim cur inWires hInj hLt hbound 0 spec.steps
    (by simp [spec.hLen]) (by simpa using spec.hValid) β).2 w fun u heq ↦ ?_
  dsimp [embedPopWire] at heq
  split_ifs at heq with hu
  · exact hNotIn ⟨u.val, hu⟩ heq
  · simp only [Fin.ext_iff] at heq
    omega
section Csa168Specs
set_option maxRecDepth 200000
theorem fin_injective_of_decide {K M : ℕ} (f : Fin K → Wire M)
    (h : decide (∀ i j : Fin K, f i = f j → i = j) = true) : Function.Injective f :=
  fun i j hij ↦ of_decide_eq_true h i j hij
theorem some_cinNe_of_decide {K M : ℕ} (outW : Fin K → Wire M) (cw₀ : Wire M)
    (h : decide (∀ k : Fin K, cw₀ ≠ outW k) = true) :
    ∀ cw k, some cw₀ = some cw → cw ≠ outW k := by
  intro cw k hcw
  cases hcw
  exact of_decide_eq_true h k
def csa168Step1OutWires : Fin 8 → Wire 336
  | 0 => ⟨55, by decide⟩ | 1 => ⟨198, by decide⟩ | 2 => ⟨229, by decide⟩
  | 3 => ⟨298, by decide⟩ | 4 => ⟨323, by decide⟩ | 5 => ⟨326, by decide⟩
  | 6 => ⟨333, by decide⟩ | 7 => ⟨335, by decide⟩
set_option maxHeartbeats 1600000 in -- elevated heartbeats for large proof
def csa168Step1Spec : WeightedCsa3GenSpec 91 80 1 8 164 where
  steps :=
    [.fa 0 1 2, .fa 3 4 5, .fa 6 7 8, .fa 9 10 11, .fa 12 13 14, .fa 15 16 17, .fa 18 19 20,
      .fa 21 22 23, .fa 24 25 26, .fa 27 28 29, .fa 30 31 32, .fa 33 34 35, .fa 36 37 38,
      .fa 39 40 41, .fa 42 43 44, .fa 45 46 47,
     .fa 48 49 50, .fa 51 52 53, .fa 54 55 56, .fa 57 58 59, .fa 60 61 62, .fa 63 64 65,
       .fa 66 67 68, .fa 69 70 71, .fa 72 73 74, .fa 75 76 77, .fa 78 79 80, .fa 81 82 83,
       .fa 84 85 86, .fa 87 88 89, .fa 90 1 4,
     .fa 7 10 13, .fa 16 19 22, .fa 25 28 31, .fa 34 37 40, .fa 43 46 49, .fa 52 55 58,
       .fa 61 64 67, .fa 70 73 76, .fa 79 82 85, .fa 88 1 10, .fa 19 28 37, .fa 46 55 64,
       .fa 73 82 1, .fa 28 55 82, .fa 91 92 93,
     .fa 94 95 96, .fa 97 98 99, .fa 100 101 102, .fa 103 104 105, .fa 106 107 108, .fa 109 110 111,
       .fa 112 113 114, .fa 115 116 117, .fa 118 119 120, .fa 121 122 123, .fa 124 125 126,
       .fa 127 128 129, .fa 130 131 132,
     .fa 133 134 135, .fa 136 137 138, .fa 139 140 141, .fa 142 143 144, .fa 145 146 147,
       .fa 148 149 150, .fa 151 152 153, .fa 154 155 156, .fa 157 158 159, .fa 160 161 162,
       .fa 163 164 165, .fa 166 167 168,
     .fa 169 170 172, .fa 173 174 175, .fa 176 177 178, .fa 179 180 181, .fa 182 183 184,
       .fa 185 186 187, .fa 188 189 190, .fa 191 192 193, .fa 194 195 196, .fa 197 198 199,
       .fa 200 201 202, .fa 203 204 205,
     .fa 206 207 208, .fa 209 210 211, .fa 212 213 214, .fa 215 216 92, .fa 95 98 101,
       .fa 104 107 110, .fa 113 116 119, .fa 122 125 128, .fa 131 134 137, .fa 140 143 146,
       .fa 149 152 155, .fa 158 161 164, .fa 167 170 174,
     .fa 177 180 183, .fa 186 189 192, .fa 195 198 201, .fa 204 207 210, .fa 213 216 98,
       .fa 107 116 125, .fa 134 143 152, .fa 161 170 180, .fa 189 198 207, .fa 216 116 143,
       .fa 170 198 116, .fa 171 217 218, .fa 219 220 221,
     .fa 222 223 224, .fa 225 226 227, .fa 228 229 230, .fa 231 232 233, .fa 234 235 236,
       .fa 237 238 239, .fa 240 241 242, .fa 243 244 245, .fa 246 247 248, .fa 249 250 251,
       .fa 252 253 254, .fa 255 256 257,
     .fa 258 259 260, .fa 261 262 263, .fa 264 265 266, .fa 267 268 269, .fa 270 271 272,
       .fa 273 274 275, .fa 276 277 278, .fa 217 220 223, .fa 226 229 232, .fa 235 238 241,
       .fa 244 247 250, .fa 253 256 259,
     .fa 262 265 268, .fa 271 274 277, .fa 220 229 238, .fa 247 256 265, .fa 274 229 256,
       .fa 279 280 281, .fa 282 283 284, .fa 285 286 287, .fa 288 289 290, .fa 291 292 293,
       .fa 294 295 296, .fa 297 298 299,
     .fa 300 301 302, .fa 303 304 305, .fa 306 307 308, .fa 309 280 283, .fa 286 289 292,
       .fa 295 298 301, .fa 304 307 280, .fa 289 298 307, .fa 310 311 312, .fa 313 314 315,
       .fa 316 317 318, .fa 319 320 321,
     .fa 322 323 324, .fa 311 314 317, .fa 320 323 314, .fa 325 326 327, .fa 328 329 330,
       .fa 331 326 329, .fa 332 333 334]
  outWires := csa168Step1OutWires
  cinWire := none
  hLen := rfl
  hValid := rfl
  hOutInj := fin_injective_of_decide csa168Step1OutWires (by decide)
  hCinNe := fun _ _ h ↦ by cases h
  hRun := rfl
def csa168StepAOutWires : Fin 8 → Wire 319
  | 0 => ⟨16, by decide⟩ | 1 => ⟨181, by decide⟩ | 2 => ⟨212, by decide⟩
  | 3 => ⟨281, by decide⟩ | 4 => ⟨306, by decide⟩ | 5 => ⟨309, by decide⟩
  | 6 => ⟨316, by decide⟩ | 7 => ⟨318, by decide⟩
set_option maxHeartbeats 1600000 in -- elevated heartbeats for large proof
def csa168StepASpec : WeightedCsa3GenSpec 92 62 10 8 155 where
  steps :=
    [.fa 0 1 2, .fa 3 4 5, .fa 6 7 8, .fa 9 10 11, .fa 12 13 14, .fa 15 16 17, .fa 18 19 20,
      .fa 21 22 23, .fa 24 25 26, .fa 27 28 29, .fa 30 31 32, .fa 33 34 35, .fa 36 37 38,
      .fa 39 40 41, .fa 42 43 44, .fa 45 46 47,
     .fa 48 49 50, .fa 51 52 53, .fa 54 55 56, .fa 57 58 59, .fa 60 61 62, .fa 63 64 65,
       .fa 66 67 68, .fa 69 70 71, .fa 72 73 74, .fa 75 76 77, .fa 78 79 80, .fa 81 82 83,
       .fa 84 85 86, .fa 87 88 89, .fa 90 91 1,
     .fa 4 7 10, .fa 13 16 19, .fa 22 25 28, .fa 31 34 37, .fa 40 43 46, .fa 49 52 55, .fa 58 61 64,
       .fa 67 70 73, .fa 76 79 82, .fa 85 88 91, .fa 7 16 25, .fa 34 43 52, .fa 61 70 79,
       .fa 88 16 43, .fa 92 93 94,
     .fa 95 96 97, .fa 98 99 100, .fa 101 102 103, .fa 104 105 106, .fa 107 108 109,
       .fa 110 111 112, .fa 113 114 115, .fa 116 117 118, .fa 119 120 121, .fa 122 123 124,
       .fa 125 126 127, .fa 128 129 130, .fa 131 132 133,
     .fa 134 135 136, .fa 137 138 139, .fa 140 141 142, .fa 143 144 145, .fa 146 147 148,
       .fa 149 150 151, .fa 152 153 164, .fa 165 166 167, .fa 168 169 170, .fa 171 172 173,
       .fa 174 175 176, .fa 177 178 179,
     .fa 180 181 182, .fa 183 184 185, .fa 186 187 188, .fa 189 190 191, .fa 192 193 194,
       .fa 195 196 197, .fa 198 199 200, .fa 201 202 203, .fa 204 205 206, .fa 207 208 93,
       .fa 96 99 102, .fa 105 108 111, .fa 114 117 120,
     .fa 123 126 129, .fa 132 135 138, .fa 141 144 147, .fa 150 153 166, .fa 169 172 175,
       .fa 178 181 184, .fa 187 190 193, .fa 196 199 202, .fa 205 208 99, .fa 108 117 126,
       .fa 135 144 153, .fa 172 181 190, .fa 199 208 117,
     .fa 144 181 208, .fa 154 155 156, .fa 157 158 159, .fa 160 161 162, .fa 163 209 210,
       .fa 211 212 213, .fa 214 215 216, .fa 217 218 219, .fa 220 221 222, .fa 223 224 225,
       .fa 226 227 228, .fa 229 230 231,
     .fa 232 233 234, .fa 235 236 237, .fa 238 239 240, .fa 241 242 243, .fa 244 245 246,
       .fa 247 248 249, .fa 250 251 252, .fa 253 254 255, .fa 256 257 258, .fa 259 260 261,
       .fa 155 158 161, .fa 209 212 215,
     .fa 218 221 224, .fa 227 230 233, .fa 236 239 242, .fa 245 248 251, .fa 254 257 260,
       .fa 158 212 221, .fa 230 239 248, .fa 257 212 239, .fa 262 263 264, .fa 265 266 267,
       .fa 268 269 270, .fa 271 272 273,
     .fa 274 275 276, .fa 277 278 279, .fa 280 281 282, .fa 283 284 285, .fa 286 287 288,
       .fa 289 290 291, .fa 292 263 266, .fa 269 272 275, .fa 278 281 284, .fa 287 290 263,
       .fa 272 281 290, .fa 293 294 295,
     .fa 296 297 298, .fa 299 300 301, .fa 302 303 304, .fa 305 306 307, .fa 294 297 300,
       .fa 303 306 297, .fa 308 309 310, .fa 311 312 313, .fa 314 309 312, .fa 315 316 317]
  outWires := csa168StepAOutWires
  cinWire := some ⟨70, by decide⟩
  hLen := rfl
  hValid := rfl
  hOutInj := fin_injective_of_decide csa168StepAOutWires (by decide)
  hCinNe := some_cinNe_of_decide csa168StepAOutWires ⟨70, by decide⟩ (by decide)
  hRun := rfl
def csa168StepBOutWires : Fin 9 → Wire 318
  | 0 => ⟨4, by decide⟩ | 1 => ⟨21, by decide⟩ | 2 => ⟨180, by decide⟩
  | 3 => ⟨211, by decide⟩ | 4 => ⟨280, by decide⟩ | 5 => ⟨305, by decide⟩
  | 6 => ⟨308, by decide⟩ | 7 => ⟨315, by decide⟩ | 8 => ⟨317, by decide⟩
set_option maxHeartbeats 1600000 in -- elevated heartbeats for large proof
def csa168StepBSpec : WeightedCsa3GenSpec 8 60 96 9 154 where
  steps :=
    [.fa 0 1 2, .fa 3 4 5, .fa 6 7 1, .fa 8 9 10, .fa 11 12 13, .fa 14 15 16, .fa 17 18 19,
      .fa 20 21 22, .fa 23 24 25, .fa 26 27 28, .fa 29 30 31, .fa 32 33 34, .fa 35 36 37,
      .fa 38 39 40, .fa 41 42 43, .fa 44 45 46,
     .fa 47 48 49, .fa 50 51 52, .fa 53 54 55, .fa 56 57 58, .fa 59 60 61, .fa 62 63 64,
       .fa 65 66 67, .fa 164 165 166, .fa 9 12 15, .fa 18 21 24, .fa 27 30 33, .fa 36 39 42,
       .fa 45 48 51, .fa 54 57 60, .fa 63 66 165,
     .fa 12 21 30, .fa 39 48 57, .fa 66 21 48, .fa 68 69 70, .fa 71 72 73, .fa 74 75 76,
       .fa 77 78 79, .fa 80 81 82, .fa 83 84 85, .fa 86 87 88, .fa 89 90 91, .fa 92 93 94,
       .fa 95 96 97, .fa 98 99 100, .fa 101 102 103,
     .fa 104 105 106, .fa 107 108 109, .fa 110 111 112, .fa 113 114 115, .fa 116 117 118,
       .fa 119 120 121, .fa 122 123 124, .fa 125 126 127, .fa 128 129 130, .fa 131 132 133,
       .fa 134 135 136, .fa 137 138 139,
     .fa 140 141 142, .fa 143 144 145, .fa 146 147 148, .fa 149 150 151, .fa 152 153 154,
       .fa 155 156 157, .fa 158 159 160, .fa 161 162 163, .fa 167 168 169, .fa 170 171 172,
       .fa 173 174 175, .fa 176 177 178,
     .fa 179 180 181, .fa 182 183 184, .fa 185 186 187, .fa 188 189 190, .fa 191 192 193,
       .fa 194 195 196, .fa 197 69 72, .fa 75 78 81, .fa 84 87 90, .fa 93 96 99, .fa 102 105 108,
       .fa 111 114 117, .fa 120 123 126,
     .fa 129 132 135, .fa 138 141 144, .fa 147 150 153, .fa 156 159 162, .fa 168 171 174,
       .fa 177 180 183, .fa 186 189 192, .fa 195 69 78, .fa 87 96 105, .fa 114 123 132,
       .fa 141 150 159, .fa 171 180 189, .fa 69 96 123,
     .fa 150 180 96, .fa 198 199 200, .fa 201 202 203, .fa 204 205 206, .fa 207 208 209,
       .fa 210 211 212, .fa 213 214 215, .fa 216 217 218, .fa 219 220 221, .fa 222 223 224,
       .fa 225 226 227, .fa 228 229 230, .fa 231 232 233,
     .fa 234 235 236, .fa 237 238 239, .fa 240 241 242, .fa 243 244 245, .fa 246 247 248,
       .fa 249 250 251, .fa 252 253 254, .fa 255 256 257, .fa 258 259 260, .fa 199 202 205,
       .fa 208 211 214, .fa 217 220 223,
     .fa 226 229 232, .fa 235 238 241, .fa 244 247 250, .fa 253 256 259, .fa 202 211 220,
       .fa 229 238 247, .fa 256 211 238, .fa 261 262 263, .fa 264 265 266, .fa 267 268 269,
       .fa 270 271 272, .fa 273 274 275,
     .fa 276 277 278, .fa 279 280 281, .fa 282 283 284, .fa 285 286 287, .fa 288 289 290,
       .fa 291 262 265, .fa 268 271 274, .fa 277 280 283, .fa 286 289 262, .fa 271 280 289,
       .fa 292 293 294, .fa 295 296 297,
     .fa 298 299 300, .fa 301 302 303, .fa 304 305 306, .fa 293 296 299, .fa 302 305 296,
       .fa 307 308 309, .fa 310 311 312, .fa 313 308 311, .fa 314 315 316]
  outWires := csa168StepBOutWires
  cinWire := some ⟨7, by decide⟩
  hLen := rfl
  hValid := rfl
  hOutInj := fin_injective_of_decide csa168StepBOutWires (by decide)
  hCinNe := some_cinNe_of_decide csa168StepBOutWires ⟨7, by decide⟩ (by decide)
  hRun := rfl
def csa168Step4OutWires : Fin 9 → Wire 300
  | 0 => ⟨13, by decide⟩ | 1 => ⟨154, by decide⟩ | 2 => ⟨149, by decide⟩
  | 3 => ⟨233, by decide⟩ | 4 => ⟨262, by decide⟩ | 5 => ⟨287, by decide⟩
  | 6 => ⟨290, by decide⟩ | 7 => ⟨297, by decide⟩ | 8 => ⟨299, by decide⟩
def csa168Step4Spec : WeightedCsa3GenSpec 27 16 111 9 146 where
  steps :=
    [.fa 0 1 2, .fa 3 4 5, .fa 6 7 8, .fa 9 10 11, .fa 12 13 14, .fa 15 16 17, .fa 18 19 20,
      .fa 21 22 23, .fa 24 25 26, .fa 1 4 7, .fa 10 13 16, .fa 19 22 25, .fa 4 13 22, .fa 27 28 29,
      .fa 30 31 32, .fa 33 34 35,
     .fa 36 37 38, .fa 39 40 41, .fa 42 154 155, .fa 156 157 158, .fa 159 160 161, .fa 162 163 164,
       .fa 165 166 28, .fa 31 34 37, .fa 40 154 157, .fa 160 163 166, .fa 34 154 163, .fa 43 44 45,
       .fa 46 47 48, .fa 49 50 51,
     .fa 52 53 54, .fa 55 56 57, .fa 58 59 60, .fa 61 62 63, .fa 64 65 66, .fa 67 68 69,
       .fa 70 71 72, .fa 73 74 75, .fa 76 77 78, .fa 79 80 81, .fa 82 83 84, .fa 85 86 87,
       .fa 88 89 90, .fa 91 92 93, .fa 94 95 96,
     .fa 97 98 99, .fa 100 101 102, .fa 103 104 105, .fa 106 107 108, .fa 109 110 111,
       .fa 112 113 114, .fa 115 116 117, .fa 118 119 120, .fa 121 122 123, .fa 124 125 126,
       .fa 127 128 129, .fa 130 131 132, .fa 133 134 135,
     .fa 136 137 138, .fa 139 140 141, .fa 142 143 144, .fa 145 146 147, .fa 148 149 150,
       .fa 151 152 153, .fa 167 168 169, .fa 170 171 172, .fa 173 174 175, .fa 176 177 178,
       .fa 179 180 44, .fa 47 50 53, .fa 56 59 62,
     .fa 65 68 71, .fa 74 77 80, .fa 83 86 89, .fa 92 95 98, .fa 101 104 107, .fa 110 113 116,
       .fa 119 122 125, .fa 128 131 134, .fa 137 140 143, .fa 146 149 152, .fa 168 171 174,
       .fa 177 180 50, .fa 59 68 77, .fa 86 95 104,
     .fa 113 122 131, .fa 140 149 171, .fa 180 68 95, .fa 122 149 68, .fa 181 182 183,
       .fa 184 185 186, .fa 187 188 189, .fa 190 191 192, .fa 193 194 195, .fa 196 197 198,
       .fa 199 200 201, .fa 202 203 204, .fa 205 206 207,
     .fa 208 209 210, .fa 211 212 213, .fa 214 215 216, .fa 217 218 219, .fa 220 221 222,
       .fa 223 224 225, .fa 226 227 228, .fa 229 230 231, .fa 232 233 234, .fa 235 236 237,
       .fa 238 239 240, .fa 241 242 182,
     .fa 185 188 191, .fa 194 197 200, .fa 203 206 209, .fa 212 215 218, .fa 221 224 227,
       .fa 230 233 236, .fa 239 242 188, .fa 197 206 215, .fa 224 233 242, .ha 206 233,
       .fa 243 244 245, .fa 246 247 248, .fa 249 250 251,
     .fa 252 253 254, .fa 255 256 257, .fa 258 259 260, .fa 261 262 263, .fa 264 265 266,
       .fa 267 268 269, .fa 270 271 272, .fa 273 244 247, .fa 250 253 256, .fa 259 262 265,
       .fa 268 271 244, .fa 253 262 271,
     .fa 274 275 276, .fa 277 278 279, .fa 280 281 282, .fa 283 284 285, .fa 286 287 288,
       .fa 275 278 281, .fa 284 287 278, .fa 289 290 291, .fa 292 293 294, .fa 295 290 293,
       .fa 296 297 298]
  outWires := csa168Step4OutWires
  cinWire := none
  hLen := rfl
  hValid := rfl
  hOutInj := fin_injective_of_decide csa168Step4OutWires (by decide)
  hCinNe := fun _ _ h ↦ by cases h
  hRun := rfl
def csa168Step5OutWires : Fin 8 → Wire 320
  | 0 => ⟨52, by decide⟩ | 1 => ⟨138, by decide⟩ | 2 => ⟨213, by decide⟩
  | 3 => ⟨282, by decide⟩ | 4 => ⟨307, by decide⟩ | 5 => ⟨310, by decide⟩
  | 6 => ⟨317, by decide⟩ | 7 => ⟨319, by decide⟩
set_option maxHeartbeats 1600000 in -- elevated heartbeats for large proof
def csa168Step5Spec : WeightedCsa3GenSpec 80 81 3 8 156 where
  steps :=
    [.fa 0 1 2, .fa 3 4 5, .fa 6 7 8, .fa 9 10 11, .fa 12 13 14, .fa 15 16 17, .fa 18 19 20,
      .fa 21 22 23, .fa 24 25 26, .fa 27 28 29, .fa 30 31 32, .fa 33 34 35, .fa 36 37 38,
      .fa 39 40 41, .fa 42 43 44, .fa 45 46 47,
     .fa 48 49 50, .fa 51 52 53, .fa 54 55 56, .fa 57 58 59, .fa 60 61 62, .fa 63 64 65,
       .fa 66 67 68, .fa 69 70 71, .fa 72 73 74, .fa 75 76 77, .fa 78 79 1, .fa 4 7 10,
       .fa 13 16 19, .fa 22 25 28, .fa 31 34 37,
     .fa 40 43 46, .fa 49 52 55, .fa 58 61 64, .fa 67 70 73, .fa 76 79 7, .fa 16 25 34,
       .fa 43 52 61, .fa 70 79 25, .fa 80 81 82, .fa 83 84 85, .fa 86 87 88, .fa 89 90 91,
       .fa 92 93 94, .fa 95 96 97, .fa 98 99 100,
     .fa 101 102 103, .fa 104 105 106, .fa 107 108 109, .fa 110 111 112, .fa 113 114 115,
       .fa 116 117 118, .fa 119 120 121, .fa 122 123 124, .fa 125 126 127, .fa 128 129 130,
       .fa 131 132 133, .fa 134 135 136,
     .fa 137 138 139, .fa 140 141 142, .fa 143 144 145, .fa 146 147 148, .fa 149 150 151,
       .fa 152 153 154, .fa 155 156 157, .fa 158 159 160, .fa 164 165 166, .fa 167 168 169,
       .fa 170 171 172, .fa 173 174 175,
     .fa 176 177 178, .fa 179 180 181, .fa 182 183 184, .fa 185 186 187, .fa 188 189 190,
       .fa 191 192 193, .fa 194 195 196, .fa 197 198 199, .fa 200 201 202, .fa 81 84 87,
       .fa 90 93 96, .fa 99 102 105, .fa 108 111 114,
     .fa 117 120 123, .fa 126 129 132, .fa 135 138 141, .fa 144 147 150, .fa 153 156 159,
       .fa 165 168 171, .fa 174 177 180, .fa 183 186 189, .fa 192 195 198, .fa 201 84 93,
       .fa 102 111 120, .fa 129 138 147, .fa 156 168 177,
     .fa 186 195 84, .fa 111 138 168, .ha 195 138, .fa 161 162 163, .fa 203 204 205,
       .fa 206 207 208, .fa 209 210 211, .fa 212 213 214, .fa 215 216 217, .fa 218 219 220,
       .fa 221 222 223, .fa 224 225 226, .fa 227 228 229,
     .fa 230 231 232, .fa 233 234 235, .fa 236 237 238, .fa 239 240 241, .fa 242 243 244,
       .fa 245 246 247, .fa 248 249 250, .fa 251 252 253, .fa 254 255 256, .fa 257 258 259,
       .fa 260 261 262, .fa 162 204 207,
     .fa 210 213 216, .fa 219 222 225, .fa 228 231 234, .fa 237 240 243, .fa 246 249 252,
       .fa 255 258 261, .fa 204 213 222, .fa 231 240 249, .fa 258 213 240, .fa 263 264 265,
       .fa 266 267 268, .fa 269 270 271,
     .fa 272 273 274, .fa 275 276 277, .fa 278 279 280, .fa 281 282 283, .fa 284 285 286,
       .fa 287 288 289, .fa 290 291 292, .fa 293 264 267, .fa 270 273 276, .fa 279 282 285,
       .fa 288 291 264, .fa 273 282 291,
     .fa 294 295 296, .fa 297 298 299, .fa 300 301 302, .fa 303 304 305, .fa 306 307 308,
       .fa 295 298 301, .fa 304 307 298, .fa 309 310 311, .fa 312 313 314, .fa 315 310 313,
       .fa 316 317 318]
  outWires := csa168Step5OutWires
  cinWire := some ⟨79, by decide⟩
  hLen := rfl
  hValid := rfl
  hOutInj := fin_injective_of_decide csa168Step5OutWires (by decide)
  hCinNe := some_cinNe_of_decide csa168Step5OutWires ⟨79, by decide⟩ (by decide)
  hRun := rfl
def csa168Step8OutWires : Fin 9 → Wire 315
  | 0 => ⟨16, by decide⟩ | 1 => ⟨169, by decide⟩ | 2 => ⟨159, by decide⟩
  | 3 => ⟨248, by decide⟩ | 4 => ⟨277, by decide⟩ | 5 => ⟨302, by decide⟩
  | 6 => ⟨305, by decide⟩ | 7 => ⟨312, by decide⟩ | 8 => ⟨314, by decide⟩
set_option maxHeartbeats 1600000 in -- elevated heartbeats for large proof
def csa168Step8Spec : WeightedCsa3GenSpec 38 15 109 9 153 where
  steps :=
    [.fa 0 1 2, .fa 3 4 5, .fa 6 7 8, .fa 9 10 11, .fa 12 13 14, .fa 15 16 17, .fa 18 19 20,
      .fa 21 22 23, .fa 24 25 26, .fa 27 28 29, .fa 30 31 32, .fa 33 34 35, .fa 36 37 1, .fa 4 7 10,
      .fa 13 16 19, .fa 22 25 28,
     .fa 31 34 37, .fa 7 16 25, .fa 38 39 40, .fa 41 42 43, .fa 44 45 46, .fa 47 48 49,
       .fa 50 51 52, .fa 162 163 164, .fa 165 166 167, .fa 168 169 170, .fa 171 172 173,
       .fa 174 175 176, .fa 177 178 179, .fa 39 42 45,
     .fa 48 51 163, .fa 166 169 172, .fa 175 178 42, .fa 51 169 178, .fa 53 54 55, .fa 56 57 58,
       .fa 59 60 61, .fa 62 63 64, .fa 65 66 67, .fa 68 69 70, .fa 71 72 73, .fa 74 75 76,
       .fa 77 78 79, .fa 80 81 82, .fa 83 84 85,
     .fa 86 87 88, .fa 89 90 91, .fa 92 93 94, .fa 95 96 97, .fa 98 99 100, .fa 101 102 103,
       .fa 104 105 106, .fa 107 108 109, .fa 110 111 112, .fa 113 114 115, .fa 116 117 118,
       .fa 119 120 121, .fa 122 123 124,
     .fa 125 126 127, .fa 128 129 130, .fa 131 132 133, .fa 134 135 136, .fa 137 138 139,
       .fa 140 141 142, .fa 143 144 145, .fa 146 147 148, .fa 149 150 151, .fa 152 153 154,
       .fa 155 156 157, .fa 158 159 160,
     .fa 161 180 181, .fa 182 183 184, .fa 185 186 187, .fa 188 189 190, .fa 191 192 193,
       .fa 194 195 54, .fa 57 60 63, .fa 66 69 72, .fa 75 78 81, .fa 84 87 90, .fa 93 96 99,
       .fa 102 105 108, .fa 111 114 117,
     .fa 120 123 126, .fa 129 132 135, .fa 138 141 144, .fa 147 150 153, .fa 156 159 180,
       .fa 183 186 189, .fa 192 195 60, .fa 69 78 87, .fa 96 105 114, .fa 123 132 141,
       .fa 150 159 186, .fa 195 78 105, .fa 132 159 78,
     .fa 196 197 198, .fa 199 200 201, .fa 202 203 204, .fa 205 206 207, .fa 208 209 210,
       .fa 211 212 213, .fa 214 215 216, .fa 217 218 219, .fa 220 221 222, .fa 223 224 225,
       .fa 226 227 228, .fa 229 230 231,
     .fa 232 233 234, .fa 235 236 237, .fa 238 239 240, .fa 241 242 243, .fa 244 245 246,
       .fa 247 248 249, .fa 250 251 252, .fa 253 254 255, .fa 256 257 197, .fa 200 203 206,
       .fa 209 212 215, .fa 218 221 224,
     .fa 227 230 233, .fa 236 239 242, .fa 245 248 251, .fa 254 257 203, .fa 212 221 230,
       .fa 239 248 257, .ha 221 248, .fa 258 259 260, .fa 261 262 263, .fa 264 265 266,
       .fa 267 268 269, .fa 270 271 272, .fa 273 274 275,
     .fa 276 277 278, .fa 279 280 281, .fa 282 283 284, .fa 285 286 287, .fa 288 259 262,
       .fa 265 268 271, .fa 274 277 280, .fa 283 286 259, .fa 268 277 286, .fa 289 290 291,
       .fa 292 293 294, .fa 295 296 297,
     .fa 298 299 300, .fa 301 302 303, .fa 290 293 296, .fa 299 302 293, .fa 304 305 306,
       .fa 307 308 309, .fa 310 305 308, .fa 311 312 313]
  outWires := csa168Step8OutWires
  cinWire := some ⟨34, by decide⟩
  hLen := rfl
  hValid := rfl
  hOutInj := fin_injective_of_decide csa168Step8OutWires (by decide)
  hCinNe := some_cinNe_of_decide csa168Step8OutWires ⟨34, by decide⟩ (by decide)
  hRun := rfl
end Csa168Specs
def weightedGenBatchVal {B₀ B₁ B₂ kCore : ℕ} (inCore : Fin (B₀ + B₁ + B₂) → Wire kCore)
    (γ : BitAssignment kCore) : ℕ :=
  (∑ i : Fin B₀, (γ (inCore ⟨i.val, by omega⟩)).val) +
    (∑ i : Fin B₁, 2 * (γ (inCore ⟨B₀ + i.val, by omega⟩)).val) +
    (∑ i : Fin B₂, 4 * (γ (inCore ⟨(B₀ + B₁) + i.val, by omega⟩)).val)
theorem sum_mul_zmod2_le (c B : ℕ) (f : Fin B → ZMod 2) :
    (∑ i : Fin B, c * (f i).val) ≤ c * B := by
  calc (∑ i : Fin B, c * (f i).val)
    _ ≤ ∑ _i : Fin B, c * 1 := Finset.sum_le_sum fun i _ ↦
        Nat.mul_le_mul_left c (Nat.le_of_lt_succ (ZMod.val_lt (f i)))
    _ = c * B := by simp [Nat.mul_comm]
theorem weightedGenBatchVal_le {B₀ B₁ B₂ kCore : ℕ} (inCore : Fin (B₀ + B₁ + B₂) → Wire kCore)
    (γ : BitAssignment kCore) : weightedGenBatchVal inCore γ ≤ B₀ + 2 * B₁ + 4 * B₂ := by
  unfold weightedGenBatchVal
  have h0 : (∑ i : Fin B₀, (γ (inCore ⟨i.val, by omega⟩)).val) ≤ B₀ := by
    simpa using sum_mul_zmod2_le 1 B₀ (fun i ↦ γ (inCore ⟨i.val, by omega⟩))
  have h1 := sum_mul_zmod2_le 2 B₁ (fun i ↦ γ (inCore ⟨B₀ + i.val, by omega⟩))
  have h2 := sum_mul_zmod2_le 4 B₂ (fun i ↦ γ (inCore ⟨(B₀ + B₁) + i.val, by omega⟩))
  omega
noncomputable def weightedGenModAddProg {B₀ B₁ B₂ K S kCore W : ℕ}
    (spec : WeightedCsa3GenSpec B₀ B₁ B₂ K S) (_hW : 0 < W)
    (inCore : Fin (B₀ + B₁ + B₂) → Wire kCore) (hInj : Function.Injective inCore) :
    InPlaceFullAddSlice.TempPhaseProg ((W + kCore) + (S + (W - 1))) :=
  let cur₀ := W + kCore
  let inComb := inCombWire (W := W) (S := S) (q := W - 1) inCore
  let hb₀ := cur0_add_S_le_M W kCore S (W - 1)
  withWeightedCsa3Gen spec cur₀ inComb (inCombWire_injective hInj) (inCombWire_lt_cur0 inCore) hb₀
    (inPlaceModAddRec ((W + kCore) + (S + (W - 1))) (W - 1) (cur₀ + S)
      (popMsbMap (spec.outWire cur₀ inComb hb₀) W) (spec.cinOutWire cur₀ inComb hb₀))
noncomputable def dWeightedGenModAdd {Var : Type} {B₀ B₁ B₂ K S kCore W mWork n : ℕ} (v : Var)
    (spec : WeightedCsa3GenSpec B₀ B₁ B₂ K S) (rCore : QRegister kCore n)
    (rAcc : QRegister W n) (rWork : QRegister mWork n) (hCA : rCore.DisjointWires rAcc)
    (hCW : rCore.DisjointWires rWork) (hAW : rAcc.DisjointWires rWork) (hW : 0 < W)
    (hmWork : S + (W - 1) ≤ mWork) (inCore : Fin (B₀ + B₁ + B₂) → Wire kCore)
    (hInj : Function.Injective inCore) : DynamicCircuit Var n :=
  ((weightedGenModAddProg spec hW inCore hInj).onRegister
    (mkModAddCombReg rCore rAcc rWork hCA hCW hAW hmWork)).toDyn v
noncomputable def dWeightedGenModInv {Var : Type} {B₀ B₁ B₂ K S kCore W mWork n : ℕ} (v : Var)
    (spec : WeightedCsa3GenSpec B₀ B₁ B₂ K S) (rCore : QRegister kCore n)
    (rAcc : QRegister W n) (rWork : QRegister mWork n) (hCA : rCore.DisjointWires rAcc)
    (hCW : rCore.DisjointWires rWork) (hAW : rAcc.DisjointWires rWork) (hW : 0 < W)
    (hmWork : S + (W - 1) ≤ mWork) (inCore : Fin (B₀ + B₁ + B₂) → Wire kCore)
    (hInj : Function.Injective inCore) : DynamicCircuit Var n :=
  ((invertModAddProg (w_le_comb W kCore (S + (W - 1)))
    (weightedGenModAddProg spec hW inCore hInj)).onRegister
    (mkModAddCombReg rCore rAcc rWork hCA hCW hAW hmWork)).toDyn v
theorem dWeightedGenModAdd_counts {Var : Type} {B₀ B₁ B₂ K S kCore W mWork n : ℕ}
    (v : Var) (spec : WeightedCsa3GenSpec B₀ B₁ B₂ K S)
    (rCore : QRegister kCore n) (rAcc : QRegister W n) (rWork : QRegister mWork n)
    (hCA : rCore.DisjointWires rAcc) (hCW : rCore.DisjointWires rWork)
    (hAW : rAcc.DisjointWires rWork) (hW : 0 < W) (hmWork : S + (W - 1) ≤ mWork)
    (inCore : Fin (B₀ + B₁ + B₂) → Wire kCore) (hInj : Function.Injective inCore) :
    let dFwd := dWeightedGenModAdd v spec rCore rAcc rWork hCA hCW hAW hW hmWork inCore hInj
    let dInv := dWeightedGenModInv v spec rCore rAcc rWork hCA hCW hAW hW hmWork inCore hInj
    dFwd.count PrimitiveGate.TOFF = 0 ∧ dInv.count PrimitiveGate.TOFF = 0 ∧
      dFwd.count PrimitiveGate.T ≤ 4 * (S + (W - 1)) ∧
      dInv.count PrimitiveGate.T ≤ 4 * (S + (W - 1)) := by
  intro dFwd dInv
  have hCnt : (weightedGenModAddProg spec hW inCore hInj).countTempAnd ≤ S + (W - 1) := by
    rw [weightedGenModAddProg, withWeightedCsa3Gen_countTempAnd]
    exact Nat.add_le_add_left (inPlaceModAddRec_countTempAnd_le _ _ _ _ _) S
  refine ⟨InPlaceFullAddSlice.TempPhaseProg.toDyn_count_toff v _,
    InPlaceFullAddSlice.TempPhaseProg.toDyn_count_toff v _, ?_, ?_⟩ <;>
  · simp only [dFwd, dInv, dWeightedGenModAdd, dWeightedGenModInv,
      InPlaceFullAddSlice.TempPhaseProg.toDyn_count_t,
      InPlaceFullAddSlice.TempPhaseProg.onRegister_countTempAnd, invertModAddProg_countTempAnd]
    omega
theorem popMsbMap_eq_some_168 {K M : ℕ} (outW : Fin K → Wire M) (W m : ℕ) {w : Wire M}
    (hw : popMsbMap outW W m = some w) : ∃ h : W - 1 - m < K, w = outW ⟨W - 1 - m, h⟩ := by
  dsimp [popMsbMap] at hw
  split_ifs at hw with h1 h2
  exact ⟨h2, Option.some.inj hw.symm⟩
theorem dWeightedGenModAdd_realizesPair
    {Var : Type} [Fintype Var] [DecidableEq Var] {B₀ B₁ B₂ K S kCore W mWork n : ℕ} [NeZero (2 ^ n)]
    (v : Var) (spec : WeightedCsa3GenSpec B₀ B₁ B₂ K S)
    (rCore : QRegister kCore n) (rAcc : QRegister W n) (rWork : QRegister mWork n)
    (hCA : rCore.DisjointWires rAcc) (hCW : rCore.DisjointWires rWork)
    (hAW : rAcc.DisjointWires rWork)
    (hW : 0 < W) (hmWork : S + (W - 1) ≤ mWork)
    (inCore : Fin (B₀ + B₁ + B₂) → Wire kCore) (hInj : Function.Injective inCore) :
    let dFwd := dWeightedGenModAdd v spec rCore rAcc rWork hCA hCW hAW hW hmWork inCore hInj
    let dInv := dWeightedGenModInv v spec rCore rAcc rWork hCA hCW hAW hW hmWork inCore hInj
    RealizesCleanPair (rCore.concat rAcc hCA) rWork
      (catModAddUnitary kCore W (weightedGenBatchVal inCore)) dFwd dInv := by
  let q := W - 1
  have hq1 : q + 1 = W := by omega
  let mClean := S + q
  let M := (W + kCore) + mClean
  let cur₀ := W + kCore
  let cur₁ := cur₀ + S
  let inComb : Fin (B₀ + B₁ + B₂) → Wire M := inCombWire (W := W) (S := S) (q := q) inCore
  have hInjComb : Function.Injective inComb := inCombWire_injective hInj
  have hGeW (i : Fin (B₀ + B₁ + B₂)) : W ≤ (inComb i).val := by dsimp [inComb, inCombWire]; omega
  have hLtComb : ∀ i : Fin (B₀ + B₁ + B₂), (inComb i).val < cur₀ := inCombWire_lt_cur0 inCore
  have hb₀ : cur₀ + S ≤ M := cur0_add_S_le_M W kCore S q
  let outW : Fin K → Wire M := spec.outWire cur₀ inComb hb₀
  let cinOut : Option (Wire M) := spec.cinOutWire cur₀ inComb hb₀
  have hOutGeW (k : Fin K) : W ≤ (outW k).val :=
    spec.outWire_ge cur₀ inComb hGeW (Nat.le_add_right W kCore) hb₀ k
  have hOutLt (k : Fin K) : (outW k).val < cur₁ := spec.outWire_lt cur₀ inComb hLtComb hb₀ k
  have hOutInj : Function.Injective outW := spec.outWire_injective cur₀ inComb hInjComb hLtComb hb₀
  obtain ⟨fMod, hTBMod, hValMod⟩ := inPlaceModAddRec_spec (M := M) q cur₁
    (by
      dsimp [cur₁, cur₀, q]
      omega)
    (by
      dsimp [M, mClean, cur₁, cur₀]
      omega)
    (popMsbMap outW W)
    (fun m w _ hw ↦ by
      obtain ⟨h2, rfl⟩ := popMsbMap_eq_some_168 outW W m hw
      exact Nat.le_trans (by omega) (hOutGeW ⟨W - 1 - m, h2⟩))
    (fun m w _ hw ↦ (popMsbMap_eq_some_168 outW W m hw).2 ▸ hOutLt _)
    (fun m₁ m₂ w₁ w₂ h₁₂ hm₂ hw₁ hw₂ heq ↦ by
      obtain ⟨_, rfl⟩ := popMsbMap_eq_some_168 outW W m₁ hw₁
      obtain ⟨_, rfl⟩ := popMsbMap_eq_some_168 outW W m₂ hw₂
      have hidx := congrArg Fin.val (hOutInj heq)
      dsimp at hidx
      omega)
    cinOut
    (fun c hc ↦ Nat.le_trans (by omega)
      (spec.cinOutWire_ge cur₀ inComb hGeW (Nat.le_add_right W kCore) hb₀ hc))
    (fun c hc ↦ spec.cinOutWire_lt cur₀ inComb hLtComb hb₀ hc)
    (fun m w c _ hw hc ↦ (popMsbMap_eq_some_168 outW W m hw).2 ▸
      spec.cinOutWire_ne_outWire cur₀ inComb hInjComb hLtComb hb₀ hc _)
  have hTBFull := TargetBlock.withWeightedCsa3Gen_block (targetEnd := q + 1) spec cur₀ inComb
    hInjComb (fun i ↦ Nat.le_trans (by omega) (hGeW i)) hLtComb
    (Nat.le_trans (by omega) (Nat.le_add_right W kCore)) hb₀ hTBMod
  rw [hq1, show M - cur₀ = mClean from Nat.add_sub_cancel_left _ _] at hTBFull
  let fFull : BitAssignment M → BitAssignment M := fun β ↦
    fMod (evalWeightedCsa3Gen spec cur₀ inComb hInjComb hLtComb hb₀ β)
  refine (TargetBlock.toCatModAddPair v rCore rAcc rWork hCA hCW hAW hmWork
    (weightedGenBatchVal inCore) hTBFull fun β hβ ↦ ?_).1
  let βcsa := evalWeightedCsa3Gen spec cur₀ inComb hInjComb hLtComb hb₀ β
  have hCleanCsa : InPlaceFullAddSlice.cleanRem M (M - cur₁) βcsa := fun w hw ↦ by
    dsimp only [βcsa]
    rw [evalWeightedCsa3Gen_untouched spec cur₀ inComb hInjComb hLtComb hb₀ β w
      (fun i ↦
        wire_ne_of_gt (by dsimp [inComb, inCombWire]; dsimp [M, mClean, cur₁, cur₀] at hw; omega))
      (by dsimp [M, mClean, cur₁, cur₀] at hw ⊢; omega)]
    exact hβ w (by dsimp [M, mClean, cur₁, cur₀] at hw ⊢; omega)
  have hAccUntouched : msbPrefixVal W (by omega) βcsa = msbPrefixVal W (by omega) β :=
    msbPrefixVal_congr (by omega) fun w hw ↦
      evalWeightedCsa3Gen_untouched spec cur₀ inComb hInjComb hLtComb hb₀ β w
        (fun _ ↦ wire_ne_of_lt (by dsimp [inComb, inCombWire]; omega)) (by dsimp [cur₀]; omega)
  have hModStep' : msbPrefixVal W (by omega) (fFull β) = (msbPrefixVal W (by omega) βcsa +
      optMsbVal (popMsbMap outW W) W βcsa + optBitVal cinOut βcsa) % 2 ^ W := by
    simpa only [hq1, fFull, βcsa] using hValMod βcsa hCleanCsa
  rw [hModStep', hAccUntouched, Nat.add_assoc, Nat.add_mod (msbPrefixVal W _ β),
    Nat.add_mod (optMsbVal _ _ _), optMsbVal_popMsbMap_mod_eq W βcsa K outW,
    ← Nat.add_mod (∑ k : Fin K, _),
      evalWeightedCsa3Gen_sum_eq spec cur₀ inComb hInjComb hLtComb hb₀ β,
    ← Nat.add_mod]
  rfl
def threePlaneGenChunkWire {mPayload : ℕ} (w : Fin 3) (pBase : ℕ)
    (eOff₀ B₀ eOff₁ B₁ eOff₂ B₂ : ℕ) (hp : pBase + 3 ≤ 6) (he₀ : eOff₀ + B₀ ≤ 218)
    (he₁ : eOff₁ + B₁ ≤ 218) (he₂ : eOff₂ + B₂ ≤ 218) (u : Fin (B₀ + B₁ + B₂)) : Wire
    (fullSysCoreWires mPayload) :=
  if _h1 : u.val < B₀ then
    elecAxisBitWire w ⟨pBase, by omega⟩
      ⟨eOff₀ + u.val, by dsimp [SpecsAux.SpecMirror.numElectrons]; omega⟩
  else if _h2 : u.val < B₀ + B₁ then
    elecAxisBitWire w ⟨pBase + 1, by omega⟩
      ⟨eOff₁ + (u.val - B₀), by dsimp [SpecsAux.SpecMirror.numElectrons]; omega⟩
  else
    elecAxisBitWire w ⟨pBase + 2, by omega⟩
      ⟨eOff₂ + (u.val - (B₀ + B₁)), by dsimp [SpecsAux.SpecMirror.numElectrons]; omega⟩
theorem threePlaneGenChunkWire_injective {mPayload : ℕ} (w : Fin 3) (pBase : ℕ)
    (eOff₀ B₀ eOff₁ B₁ eOff₂ B₂ : ℕ) (hp : pBase + 3 ≤ 6)
    (he₀ : eOff₀ + B₀ ≤ 218) (he₁ : eOff₁ + B₁ ≤ 218) (he₂ : eOff₂ + B₂ ≤ 218) :
    Function.Injective
      (threePlaneGenChunkWire (mPayload :=
        mPayload) w pBase eOff₀ B₀ eOff₁ B₁ eOff₂ B₂ hp he₀ he₁ he₂) := by
  intro u₁ u₂ h
  have hu₁ := u₁.isLt
  have hu₂ := u₂.isLt
  have hv := congrArg Fin.val h
  dsimp only [threePlaneGenChunkWire] at hv
  split_ifs at hv <;> {
    simp only [elecAxisBitWire_val] at hv
    exact Fin.ext (by omega)
  }
noncomputable def step1Xor8Prog168 {kCore : ℕ}
    (inCore : Fin (91 + 80 + 1) → Wire kCore) (hInj : Function.Injective inCore) :
    InPlaceFullAddSlice.TempPhaseProg ((8 + kCore) + 164) :=
  let cur₀ := 8 + kCore
  let inComb := inCombWire (W := 8) (S := 164) (q := 0) inCore
  let hb₀ : cur₀ + 164 ≤ (8 + kCore) + 164 := le_rfl
  let outW := csa168Step1Spec.outWire cur₀ inComb hb₀
  let hOutGe : ∀ k : Fin 8, 8 ≤ (outW k).val :=
    fun k ↦ csa168Step1Spec.outWire_ge cur₀ inComb
      (fun _ ↦ by dsimp [inComb, inCombWire]; omega) (Nat.le_add_right 8 kCore) hb₀ k
  withWeightedCsa3Gen csa168Step1Spec cur₀ inComb
    (inCombWire_injective hInj) (inCombWire_lt_cur0 inCore) hb₀
    (xorOutLoop (by omega) outW hOutGe 8 le_rfl)
noncomputable def dStep1Xor8_168 {Var : Type} {kCore mWork n : ℕ}
    (v : Var) (rCore : QRegister kCore n) (rAcc : QRegister 8 n) (rWork : QRegister mWork n)
    (hCA : rCore.DisjointWires rAcc) (hCW : rCore.DisjointWires rWork)
    (hAW : rAcc.DisjointWires rWork) (hmWork : 164 ≤ mWork)
    (inCore : Fin (91 + 80 + 1) → Wire kCore) (hInj : Function.Injective inCore) :
    DynamicCircuit Var n :=
  let rComb := mkModAddCombReg rCore rAcc rWork hCA hCW hAW hmWork
  ((step1Xor8Prog168 inCore hInj).onRegister rComb).toDyn v
theorem dStep1Xor8_168_counts {Var : Type} {kCore mWork n : ℕ}
    (v : Var) (rCore : QRegister kCore n) (rAcc : QRegister 8 n) (rWork : QRegister mWork n)
    (hCA : rCore.DisjointWires rAcc) (hCW : rCore.DisjointWires rWork)
    (hAW : rAcc.DisjointWires rWork) (hmWork : 164 ≤ mWork)
    (inCore : Fin (91 + 80 + 1) → Wire kCore) (hInj : Function.Injective inCore) :
    let dyn := dStep1Xor8_168 v rCore rAcc rWork hCA hCW hAW hmWork inCore hInj
    dyn.count PrimitiveGate.TOFF = 0 ∧ dyn.count PrimitiveGate.T = 656 := by
  intro dyn
  refine ⟨InPlaceFullAddSlice.TempPhaseProg.toDyn_count_toff v _, ?_⟩
  dsimp [dyn, dStep1Xor8_168]
  rw [InPlaceFullAddSlice.TempPhaseProg.toDyn_count_t,
    InPlaceFullAddSlice.TempPhaseProg.onRegister_countTempAnd]
  simp [step1Xor8Prog168]
theorem dStep1Xor8_168_realizesPair
    {Var : Type} [Fintype Var] [DecidableEq Var] {kCore mWork n : ℕ} [NeZero (2 ^ n)]
    (v : Var) (rCore : QRegister kCore n) (rAcc : QRegister 8 n) (rWork : QRegister mWork n)
    (hCA : rCore.DisjointWires rAcc) (hCW : rCore.DisjointWires rWork)
    (hAW : rAcc.DisjointWires rWork) (hmWork : 164 ≤ mWork)
    (inCore : Fin (91 + 80 + 1) → Wire kCore) (hInj : Function.Injective inCore) :
    let dyn := dStep1Xor8_168 v rCore rAcc rWork hCA hCW hAW hmWork inCore hInj
    RealizesCleanPair (rCore.concat rAcc hCA) rWork
      (uBitXor kCore 8 (weightedGenBatchVal inCore)) dyn dyn := by
  let M := (8 + kCore) + 164
  let cur₀ := 8 + kCore
  let inComb : Fin (91 + 80 + 1) → Wire M := inCombWire (W := 8) (S := 164) (q := 0) inCore
  have hInjComb : Function.Injective inComb := inCombWire_injective hInj
  have hGe8 (i : Fin (91 + 80 + 1)) : 8 ≤ (inComb i).val := by dsimp [inComb, inCombWire]; omega
  have hLtComb : ∀ i : Fin (91 + 80 + 1), (inComb i).val < cur₀ := inCombWire_lt_cur0 inCore
  have hb₀ : cur₀ + 164 ≤ M := le_rfl
  let outW : Fin 8 → Wire M := csa168Step1Spec.outWire cur₀ inComb hb₀
  have hOutGe8 (k : Fin 8) : 8 ≤ (outW k).val :=
    csa168Step1Spec.outWire_ge cur₀ inComb hGe8 (Nat.le_add_right 8 kCore) hb₀ k
  have hTB1 := TargetBlock.withWeightedCsa3Gen_block (targetEnd := 8) csa168Step1Spec cur₀ inComb
    hInjComb hGe8 hLtComb (Nat.le_add_right 8 kCore) hb₀
    (xorOutLoop_spec (M := M) (W := 8) (rem := M - (cur₀ + 164)) (by omega)
      (by dsimp [M, cur₀]; omega) outW hOutGe8
      (fun k ↦ by have :=
        csa168Step1Spec.outWire_lt cur₀ inComb hLtComb hb₀ k; dsimp [M, cur₀]; omega)
      8 le_rfl)
  rw [show M - cur₀ = 164 from Nat.add_sub_cancel_left _ _] at hTB1
  refine TargetBlock.toBitXorPair v rCore rAcc rWork hCA hCW hAW hmWork
    (weightedGenBatchVal inCore) hTB1 fun β _ j ↦ ?_
  let βcsa := evalWeightedCsa3Gen csa168Step1Spec cur₀ inComb hInjComb hLtComb hb₀ β
  have hj8 : 8 - 1 - j.val < 8 := by omega
  have hkm : 8 - 1 - (8 - 1 - j.val) < 8 := by omega
  dsimp only
  simp only [hj8, hkm, ↓reduceDIte]
  rw [show (⟨8 - 1 - (8 - 1 - j.val), by omega⟩ : Fin 8) = j from Fin.ext (by dsimp; omega)]
  rw [show evalWeightedCsa3Gen csa168Step1Spec cur₀ inComb hInjComb hLtComb hb₀ β
      ⟨8 - 1 - j.val, _⟩ = β ⟨8 - 1 - j.val, by omega⟩ from
    evalWeightedCsa3Gen_untouched csa168Step1Spec cur₀ inComb hInjComb hLtComb hb₀ β _
      (fun i ↦ wire_ne_of_lt (lt_of_lt_of_le hj8 (hGe8 i))) (by
        dsimp [cur₀]
        omega)]
  let xCore : BitAssignment kCore := fun q ↦ β (Fin.castAdd 164 (Fin.natAdd 8 q))
  have hSumEq := evalWeightedCsa3Gen_sum_eq csa168Step1Spec cur₀ inComb hInjComb hLtComb hb₀ β
  rw [show optBitVal (csa168Step1Spec.cinOutWire cur₀ inComb hb₀) βcsa = 0 from rfl,
    add_zero] at hSumEq
  refine congrArg (β ⟨8 - 1 - j.val, by omega⟩ + ·) (congrFun
    (show (fun k : Fin 8 ↦ βcsa (outW k)) = fun k : Fin 8 ↦
      if (weightedGenBatchVal inCore xCore).testBit k.val then 1 else 0 from
    bitsVal_injective ?_) j)
  rw [show bitsVal (fun k : Fin 8 ↦ βcsa (outW k)) = ∑ k : Fin 8, 2 ^ k.val * (βcsa (outW k)).val
    from Finset.sum_congr rfl fun _ _ ↦ mul_comm _ _, hSumEq,
    bitsVal_eq_of_testBit 8 _ ((weightedGenBatchVal_le inCore xCore).trans_lt (by decide))]
  rfl
theorem accInvar_step1_bitXor8 {kCore n : ℕ} [NeZero (2 ^ n)] (rCore : QRegister kCore n)
    (rSum14 : QRegister 14 n) (hCSum : rCore.DisjointWires rSum14)
    (V : BitAssignment kCore → ℕ) (β₀ : BitAssignment n) (hInv0 : accInvar rSum14 0 β₀ β₀)
    (hVlt : V (fun q ↦ β₀ (rCore q)) < 2 ^ 8) : ∃ β₁ : BitAssignment n, ((rCore.concat rSum14
    hCSum).embedUnitary ((selCoreSlice kCore 0 8 (by decide)).embedUnitary (uBitXor kCore 8
    V))).1.mulVec (basisKet β₀) = basisKet β₁ ∧ accInvar rSum14 (V (fun q ↦ β₀ (rCore q))) β₀
    β₁ := by
  let hSlice8 : 0 + 8 ≤ 14 := by decide
  let rSlice8 := rSum14.slice 0 8 hSlice8
  let xCore : BitAssignment kCore := fun q ↦ β₀ (rCore q)
  let β₁ : BitAssignment n := fun z ↦ if hz : z ∈ rSum14.image then if (V xCore).testBit
      (Classical.choose ((QRegister.mem_image rSum14 z).mp hz)).val then 1 else 0 else β₀ z
  have hin14 (i : Fin 14) : β₁ (rSum14 i) = if (V xCore).testBit i.val then 1 else 0 := by
    have hm : rSum14 i ∈ rSum14.image := (QRegister.mem_image rSum14 _).mpr ⟨i, rfl⟩
    simp only [β₁, hm, ↓reduceDIte,
      rSum14.wires.injective
        (Classical.choose_spec ((QRegister.mem_image rSum14 (rSum14 i)).mp hm))]
  refine ⟨β₁, ?_, fun _ hz ↦ dite_eq_right hz, hin14⟩
  rw [embedUnitary_selCoreSlice_val]
  refine uBitXor_mulVec_basisKet rCore rSlice8 (disj_slice14 hCSum 0 8 hSlice8) V β₀ β₁
    (fun z hz8 ↦ ?_) (fun j ↦ ?_)
  · by_cases hz14 : z ∈ rSum14.image
    · obtain ⟨i, rfl⟩ := (QRegister.mem_image rSum14 z).mp hz14
      have hge8 : 8 ≤ i.val := Nat.le_of_not_lt fun hlt ↦ hz8 <|
        (QRegister.mem_image rSlice8 _).mpr ⟨⟨i.val, hlt⟩, by simp [rSlice8]⟩
      rw [hin14 i, Nat.testBit_lt_two_pow (lt_of_lt_of_le hVlt
        (Nat.pow_le_pow_right (by decide) hge8)), show β₀ (rSum14 i) = 0 by simpa using hInv0.2 i]
      rfl
    · exact dite_eq_right hz14
  · rw [show rSlice8 j = rSum14 ⟨j.val, by omega⟩ by simp [rSlice8],
      hin14 ⟨j.val, by omega⟩,
      show β₀ (rSum14 ⟨j.val, by omega⟩) = 0 by simpa using hInv0.2 ⟨j.val, by omega⟩, zero_add]
theorem sum_fin218_split4 {a b c d ab abc : ℕ}
    (hab : a + b = ab) (habc : ab + c = abc) (h : abc + d = 218)
    (f : Fin numElectrons → ℕ) :
    (∑ i : Fin a, f ⟨0 + i.val, by dsimp [SpecsAux.SpecMirror.numElectrons]; omega⟩) +
      (∑ i : Fin b, f ⟨a + i.val, by dsimp [SpecsAux.SpecMirror.numElectrons]; omega⟩) +
      (∑ i : Fin c, f ⟨ab + i.val, by dsimp [SpecsAux.SpecMirror.numElectrons]; omega⟩) +
      (∑ i : Fin d, f ⟨abc + i.val, by dsimp [SpecsAux.SpecMirror.numElectrons]; omega⟩) =
      ∑ e : Fin numElectrons, f e := by
  subst hab
  subst habc
  let e218 : Fin (((a + b) + c) + d) ≃ Fin numElectrons := finCongr h
  rw [← Equiv.sum_comp e218, Fin.sum_univ_add, Fin.sum_univ_add, Fin.sum_univ_add]
  refine congrArg₂ (· + ·) (congrArg₂ (· + ·) (congrArg₂ (· + ·) ?_ ?_) ?_) ?_
  all_goals refine Finset.sum_congr rfl fun i _ ↦ congrArg f (Fin.ext (by simp [e218]))
theorem weightedGenBatchVal_threePlaneGenChunk {mPayload : ℕ} (w : Fin 3) (pBase : ℕ)
    (eOff₀ B₀ eOff₁ B₁ eOff₂ B₂ : ℕ) (hp : pBase + 3 ≤ 6)
    (he₀ : eOff₀ + B₀ ≤ 218) (he₁ : eOff₁ + B₁ ≤ 218) (he₂ : eOff₂ + B₂ ≤ 218)
    (γ : BitAssignment (fullSysCoreWires mPayload)) :
    weightedGenBatchVal
        (threePlaneGenChunkWire (mPayload :=
          mPayload) w pBase eOff₀ B₀ eOff₁ B₁ eOff₂ B₂ hp he₀ he₁ he₂) γ =
      (∑ i : Fin B₀,
        (γ (elecAxisBitWire (mPayload := mPayload) w ⟨pBase, by omega⟩
          ⟨eOff₀ + i.val, by dsimp [SpecsAux.SpecMirror.numElectrons]; omega⟩)).val) +
      (∑ i : Fin B₁,
        2 * (γ (elecAxisBitWire (mPayload := mPayload) w ⟨pBase + 1, by omega⟩
          ⟨eOff₁ + i.val, by dsimp [SpecsAux.SpecMirror.numElectrons]; omega⟩)).val) +
      (∑ i : Fin B₂,
        4 * (γ (elecAxisBitWire (mPayload := mPayload) w ⟨pBase + 2, by omega⟩
          ⟨eOff₂ + i.val, by dsimp [SpecsAux.SpecMirror.numElectrons]; omega⟩)).val) := by
  unfold weightedGenBatchVal
  refine congrArg₂ (· + ·) (congrArg₂ (· + ·)
    (Finset.sum_congr rfl fun i _ ↦ ?_) (Finset.sum_congr rfl fun i _ ↦ ?_))
    (Finset.sum_congr rfl fun i _ ↦ ?_)
  · rw [threePlaneGenChunkWire, dite_eq_left i.isLt]
  · have := i.isLt
    rw [threePlaneGenChunkWire, dite_eq_right (show ¬B₀ + i.val < B₀ by omega),
      dite_eq_left (show B₀ + i.val < B₀ + B₁ by omega)]
    exact congrArg (fun e ↦ 2 * (γ (elecAxisBitWire w _ e)).val) (Fin.ext (by simp))
  · have := i.isLt
    rw [threePlaneGenChunkWire, dite_eq_right (show ¬(B₀ + B₁) + i.val < B₀ by omega),
      dite_eq_right (show ¬(B₀ + B₁) + i.val < B₀ + B₁ by omega)]
    exact congrArg (fun e ↦ 4 * (γ (elecAxisBitWire w _ e)).val) (Fin.ext (by simp))
abbrev chunk168 {mPayload : ℕ} (w : Fin 3) (p e₀ B₀ e₁ B₁ e₂ B₂ : ℕ)
    (hp : p + 3 ≤ 6 := by decide) (h₀ : e₀ + B₀ ≤ 218 := by decide)
    (h₁ : e₁ + B₁ ≤ 218 := by decide) (h₂ : e₂ + B₂ ≤ 218 := by decide) :
    Fin (B₀ + B₁ + B₂) → Wire (fullSysCoreWires mPayload) :=
  threePlaneGenChunkWire w p e₀ B₀ e₁ B₁ e₂ B₂ hp h₀ h₁ h₂
theorem hybrid168EightBatch_eq_slot2AxisSum {mPayload : ℕ} (w : Fin 3)
    (γ : BitAssignment (fullSysCoreWires mPayload)) :
    (((((((weightedGenBatchVal (chunk168 w 0 0 91 0 80 0 1) γ +
      2 ^ 0 * weightedGenBatchVal (chunk168 w 0 91 92 80 62 1 10) γ) +
      2 ^ 0 * weightedGenBatchVal (chunk168 w 0 183 8 142 60 11 96) γ) +
      2 ^ 0 * weightedGenBatchVal (chunk168 w 0 191 27 202 16 107 111) γ) +
      2 ^ 3 * weightedGenBatchVal (chunk168 w 3 0 80 0 81 0 3) γ) +
      2 ^ 3 * weightedGenBatchVal (chunk168 w 3 80 92 81 62 3 10) γ) +
      2 ^ 3 * weightedGenBatchVal (chunk168 w 3 172 8 143 60 13 96) γ) +
      2 ^ 3 * weightedGenBatchVal (chunk168 w 3 180 38 203 15 109 109) γ) =
      slot2AxisSum w γ := by
  dsimp only [chunk168]
  simp only [Nat.pow_zero, one_mul, weightedGenBatchVal_threePlaneGenChunk,
    show ∀ h, (⟨0, h⟩ : Fin 6) = 0 from fun _ ↦ rfl,
    show ∀ h, (⟨0 + 1, h⟩ : Fin 6) = 1 from fun _ ↦ rfl,
    show ∀ h, (⟨0 + 2, h⟩ : Fin 6) = 2 from fun _ ↦ rfl,
    show ∀ h, (⟨3, h⟩ : Fin 6) = 3 from fun _ ↦ rfl,
    show ∀ h, (⟨3 + 1, h⟩ : Fin 6) = 4 from fun _ ↦ rfl,
    show ∀ h, (⟨3 + 2, h⟩ : Fin 6) = 5 from fun _ ↦ rfl]
  have hp (a b c d ab abc : ℕ) (h1 : a + b = ab) (h2 : ab + c = abc) (h3 : abc + d = 218)
      (p : Fin 6) := sum_fin218_split4 h1 h2 h3 fun e ↦ (γ (elecAxisBitWire w p e)).val
  rw [slot2AxisSum_eq_bitPlane_sum w γ, Fin.sum_univ_six,
    ← hp 91 92 8 27 183 191 rfl rfl rfl 0, ← hp 80 62 60 16 142 202 rfl rfl rfl 1,
    ← hp 1 10 96 111 11 107 rfl rfl rfl 2, ← hp 80 92 8 38 172 180 rfl rfl rfl 3,
    ← hp 81 62 60 15 143 203 rfl rfl rfl 4, ← hp 3 10 96 109 13 109 rfl rfl rfl 5]
  simp only [← Finset.mul_sum, show (0 : Fin 6).val = 0 from rfl,
    show (1 : Fin 6).val = 1 from rfl, show (2 : Fin 6).val = 2 from rfl,
    show (3 : Fin 6).val = 3 from rfl, show (4 : Fin 6).val = 4 from rfl,
    show (5 : Fin 6).val = 5 from rfl]
  ring
noncomputable abbrev stepAdd168 {Var : Type} {B₀ B₁ B₂ K S mPayload mWork n : ℕ} (v : Var)
    (spec : WeightedCsa3GenSpec B₀ B₁ B₂ K S) (off W : ℕ)
    (rCore : QRegister (fullSysCoreWires mPayload) n) (rSum14 : QRegister 14 n)
    (rWork : QRegister mWork n) (hCSum : rCore.DisjointWires rSum14)
    (hCW : rCore.DisjointWires rWork) (hSW : rSum14.DisjointWires rWork) (w : Fin 3)
      (p e₀ e₁ e₂ : ℕ)
    (hSl : off + W ≤ 14 := by decide) (hW : 0 < W := by decide) (hm : S + (W - 1) ≤ mWork :=
      by omega)
    (hp : p + 3 ≤ 6 := by decide) (h₀ : e₀ + B₀ ≤ 218 := by decide)
    (h₁ : e₁ + B₁ ≤ 218 := by decide) (h₂ : e₂ + B₂ ≤ 218 := by decide) : DynamicCircuit Var n :=
  dWeightedGenModAdd v spec rCore (rSum14.slice off W hSl) rWork (disj_slice14 hCSum off W hSl)
    hCW (disj_slice14_work hSW off W hSl) hW hm
      (threePlaneGenChunkWire w p e₀ B₀ e₁ B₁ e₂ B₂ hp h₀ h₁ h₂)
    (threePlaneGenChunkWire_injective w p e₀ B₀ e₁ B₁ e₂ B₂ hp h₀ h₁ h₂)
noncomputable abbrev stepInv168 {Var : Type} {B₀ B₁ B₂ K S mPayload mWork n : ℕ} (v : Var)
    (spec : WeightedCsa3GenSpec B₀ B₁ B₂ K S) (off W : ℕ)
    (rCore : QRegister (fullSysCoreWires mPayload) n) (rSum14 : QRegister 14 n)
    (rWork : QRegister mWork n) (hCSum : rCore.DisjointWires rSum14)
    (hCW : rCore.DisjointWires rWork) (hSW : rSum14.DisjointWires rWork) (w : Fin 3)
      (p e₀ e₁ e₂ : ℕ)
    (hSl : off + W ≤ 14 := by decide) (hW : 0 < W := by decide) (hm : S + (W - 1) ≤ mWork :=
      by omega)
    (hp : p + 3 ≤ 6 := by decide) (h₀ : e₀ + B₀ ≤ 218 := by decide)
    (h₁ : e₁ + B₁ ≤ 218 := by decide) (h₂ : e₂ + B₂ ≤ 218 := by decide) : DynamicCircuit Var n :=
  dWeightedGenModInv v spec rCore (rSum14.slice off W hSl) rWork (disj_slice14 hCSum off W hSl)
    hCW (disj_slice14_work hSW off W hSl) hW hm
      (threePlaneGenChunkWire w p e₀ B₀ e₁ B₁ e₂ B₂ hp h₀ h₁ h₂)
    (threePlaneGenChunkWire_injective w p e₀ B₀ e₁ B₁ e₂ B₂ hp h₀ h₁ h₂)
theorem step168_counts {Var : Type} {B₀ B₁ B₂ K S mPayload mWork n : ℕ} (v : Var)
    (spec : WeightedCsa3GenSpec B₀ B₁ B₂ K S) (off W : ℕ)
    (rCore : QRegister (fullSysCoreWires mPayload) n) (rSum14 : QRegister 14 n)
    (rWork : QRegister mWork n) (hCSum : rCore.DisjointWires rSum14)
    (hCW : rCore.DisjointWires rWork) (hSW : rSum14.DisjointWires rWork) (w : Fin 3)
      (p e₀ e₁ e₂ : ℕ)
    (hSl : off + W ≤ 14 := by decide) (hW : 0 < W := by decide) (hm : S + (W - 1) ≤ mWork :=
      by omega)
    (hp : p + 3 ≤ 6 := by decide) (h₀ : e₀ + B₀ ≤ 218 := by decide)
    (h₁ : e₁ + B₁ ≤ 218 := by decide) (h₂ : e₂ + B₂ ≤ 218 := by decide) :
    (stepAdd168 v spec off W rCore rSum14 rWork hCSum hCW hSW w p e₀ e₁ e₂ hSl hW hm hp h₀ h₁
      h₂).count PrimitiveGate.TOFF = 0 ∧
      (stepInv168 v spec off W rCore rSum14 rWork hCSum hCW hSW w p e₀ e₁ e₂ hSl hW hm hp h₀ h₁
        h₂).count PrimitiveGate.TOFF = 0 ∧
      (stepAdd168 v spec off W rCore rSum14 rWork hCSum hCW hSW w p e₀ e₁ e₂ hSl hW hm hp h₀ h₁
        h₂).count PrimitiveGate.T ≤ 4 * (S + (W - 1)) ∧
      (stepInv168 v spec off W rCore rSum14 rWork hCSum hCW hSW w p e₀ e₁ e₂ hSl hW hm hp h₀ h₁
        h₂).count PrimitiveGate.T ≤ 4 * (S + (W - 1)) :=
  dWeightedGenModAdd_counts v spec rCore (rSum14.slice off W hSl) rWork
    (disj_slice14 hCSum off W hSl) hCW (disj_slice14_work hSW off W hSl) hW hm _
    (threePlaneGenChunkWire_injective w p e₀ B₀ e₁ B₁ e₂ B₂ hp h₀ h₁ h₂)
theorem step168_pair {Var : Type} [Fintype Var] [DecidableEq Var]
    {B₀ B₁ B₂ K S mPayload mWork n : ℕ} [NeZero (2 ^ n)] (v : Var)
    (spec : WeightedCsa3GenSpec B₀ B₁ B₂ K S) (off W : ℕ)
    (rCore : QRegister (fullSysCoreWires mPayload) n) (rSum14 : QRegister 14 n)
    (rWork : QRegister mWork n) (hCSum : rCore.DisjointWires rSum14)
    (hCW : rCore.DisjointWires rWork) (hSW : rSum14.DisjointWires rWork) (w : Fin 3)
      (p e₀ e₁ e₂ : ℕ)
    (hSl : off + W ≤ 14 := by decide) (hW : 0 < W := by decide) (hm : S + (W - 1) ≤ mWork :=
      by omega)
    (hp : p + 3 ≤ 6 := by decide) (h₀ : e₀ + B₀ ≤ 218 := by decide)
    (h₁ : e₁ + B₁ ≤ 218 := by decide) (h₂ : e₂ + B₂ ≤ 218 := by decide) :
    RealizesCleanPair (rCore.concat rSum14 hCSum) rWork
      ((selCoreSlice (fullSysCoreWires mPayload) off W hSl).embedUnitary
        (catModAddUnitary (fullSysCoreWires mPayload) W
          (weightedGenBatchVal (chunk168 w p e₀ B₀ e₁ B₁ e₂ B₂ hp h₀ h₁ h₂))))
      (stepAdd168 v spec off W rCore rSum14 rWork hCSum hCW hSW w p e₀ e₁ e₂ hSl hW hm hp h₀ h₁ h₂)
      (stepInv168 v spec off W rCore rSum14 rWork hCSum hCW hSW w p e₀ e₁ e₂ hSl hW hm hp h₀ h₁ h₂)
        :=
  liftCleanPair_slice14 hCSum off W hSl
    (dWeightedGenModAdd_realizesPair v spec rCore (rSum14.slice off W hSl) rWork
      (disj_slice14 hCSum off W hSl) hCW (disj_slice14_work hSW off W hSl) hW hm _
      (threePlaneGenChunkWire_injective w p e₀ B₀ e₁ B₁ e₂ B₂ hp h₀ h₁ h₂))
noncomputable def dCleanHybridStreamAdd164 {Var : Type} {mPayload mWork n : ℕ} (v : Var)
    (w : Fin 3) (rCore : QRegister (fullSysCoreWires mPayload) n) (rSum14 : QRegister 14 n)
    (rWork : QRegister mWork n) (hCSum : rCore.DisjointWires rSum14)
    (hCW : rCore.DisjointWires rWork) (hSW : rSum14.DisjointWires rWork)
    (hmWork : 164 ≤ mWork) : DynamicCircuit Var n :=
  let s1 := dStep1Xor8_168 v rCore (rSum14.slice 0 8 (by decide)) rWork
    (disj_slice14 hCSum 0 8 (by decide)) hCW (disj_slice14_work hSW 0 8 (by decide)) hmWork
    (chunk168 w 0 0 91 0 80 0 1)
    (threePlaneGenChunkWire_injective w 0 0 91 0 80 0 1 (by decide) (by decide) (by decide)
      (by decide))
  let s2 := stepAdd168 v csa168StepASpec 0 9 rCore rSum14 rWork hCSum hCW hSW w 0 91 80 1
  let s3 := stepAdd168 v csa168StepBSpec 0 10 rCore rSum14 rWork hCSum hCW hSW w 0 183 142 11
  let s4 := stepAdd168 v csa168Step4Spec 0 11 rCore rSum14 rWork hCSum hCW hSW w 0 191 202 107
  let s5 := stepAdd168 v csa168Step5Spec 3 9 rCore rSum14 rWork hCSum hCW hSW w 3 0 0 0
  let s6 := stepAdd168 v csa168StepASpec 3 10 rCore rSum14 rWork hCSum hCW hSW w 3 80 81 3
  let s7 := stepAdd168 v csa168StepBSpec 3 11 rCore rSum14 rWork hCSum hCW hSW w 3 172 143 13
  let s8 := stepAdd168 v csa168Step8Spec 3 11 rCore rSum14 rWork hCSum hCW hSW w 3 180 203 109
  ((((((s1.seq s2).seq s3).seq s4).seq s5).seq s6).seq s7).seq s8
noncomputable def dCleanHybridStreamInv164 {Var : Type} {mPayload mWork n : ℕ} (v : Var)
    (w : Fin 3) (rCore : QRegister (fullSysCoreWires mPayload) n) (rSum14 : QRegister 14 n)
    (rWork : QRegister mWork n) (hCSum : rCore.DisjointWires rSum14)
    (hCW : rCore.DisjointWires rWork) (hSW : rSum14.DisjointWires rWork)
    (hmWork : 164 ≤ mWork) : DynamicCircuit Var n :=
  let i1 := dStep1Xor8_168 v rCore (rSum14.slice 0 8 (by decide)) rWork
    (disj_slice14 hCSum 0 8 (by decide)) hCW (disj_slice14_work hSW 0 8 (by decide)) hmWork
    (chunk168 w 0 0 91 0 80 0 1)
    (threePlaneGenChunkWire_injective w 0 0 91 0 80 0 1 (by decide) (by decide) (by decide)
      (by decide))
  let i2 := stepInv168 v csa168StepASpec 0 9 rCore rSum14 rWork hCSum hCW hSW w 0 91 80 1
  let i3 := stepInv168 v csa168StepBSpec 0 10 rCore rSum14 rWork hCSum hCW hSW w 0 183 142 11
  let i4 := stepInv168 v csa168Step4Spec 0 11 rCore rSum14 rWork hCSum hCW hSW w 0 191 202 107
  let i5 := stepInv168 v csa168Step5Spec 3 9 rCore rSum14 rWork hCSum hCW hSW w 3 0 0 0
  let i6 := stepInv168 v csa168StepASpec 3 10 rCore rSum14 rWork hCSum hCW hSW w 3 80 81 3
  let i7 := stepInv168 v csa168StepBSpec 3 11 rCore rSum14 rWork hCSum hCW hSW w 3 172 143 13
  let i8 := stepInv168 v csa168Step8Spec 3 11 rCore rSum14 rWork hCSum hCW hSW w 3 180 203 109
  i8.seq (i7.seq (i6.seq (i5.seq (i4.seq (i3.seq (i2.seq i1))))))
theorem dCleanHybridStream164_counts {Var : Type} {mPayload mWork n : ℕ}
    (v : Var) (w : Fin 3) (rCore : QRegister (fullSysCoreWires mPayload) n)
    (rSum14 : QRegister 14 n) (rWork : QRegister mWork n)
    (hCSum : rCore.DisjointWires rSum14) (hCW : rCore.DisjointWires rWork)
    (hSW : rSum14.DisjointWires rWork) (hmWork : 164 ≤ mWork) :
    let dFwd := dCleanHybridStreamAdd164 v w rCore rSum14 rWork hCSum hCW hSW hmWork
    let dInv := dCleanHybridStreamInv164 v w rCore rSum14 rWork hCSum hCW hSW hmWork
    dFwd.count PrimitiveGate.TOFF = 0 ∧ dInv.count PrimitiveGate.TOFF = 0 ∧
      dFwd.count PrimitiveGate.T ≤ 5204 ∧ dInv.count PrimitiveGate.T ≤ 5204 := by
  obtain ⟨t1, h1⟩ := dStep1Xor8_168_counts v rCore (rSum14.slice 0 8 (by decide)) rWork
    (disj_slice14 hCSum 0 8 (by decide)) hCW (disj_slice14_work hSW 0 8 (by decide)) hmWork
    (chunk168 w 0 0 91 0 80 0 1)
    (threePlaneGenChunkWire_injective w 0 0 91 0 80 0 1 (by decide) (by decide) (by decide)
      (by decide))
  obtain ⟨t2, i2, h2, g2⟩ :=
    step168_counts v csa168StepASpec 0 9 rCore rSum14 rWork hCSum hCW hSW w 0 91 80 1
  obtain ⟨t3, i3, h3, g3⟩ :=
    step168_counts v csa168StepBSpec 0 10 rCore rSum14 rWork hCSum hCW hSW w 0 183 142 11
  obtain ⟨t4, i4, h4, g4⟩ :=
    step168_counts v csa168Step4Spec 0 11 rCore rSum14 rWork hCSum hCW hSW w 0 191 202 107
  obtain ⟨t5, i5, h5, g5⟩ :=
    step168_counts v csa168Step5Spec 3 9 rCore rSum14 rWork hCSum hCW hSW w 3 0 0 0
  obtain ⟨t6, i6, h6, g6⟩ :=
    step168_counts v csa168StepASpec 3 10 rCore rSum14 rWork hCSum hCW hSW w 3 80 81 3
  obtain ⟨t7, i7, h7, g7⟩ :=
    step168_counts v csa168StepBSpec 3 11 rCore rSum14 rWork hCSum hCW hSW w 3 172 143 13
  obtain ⟨t8, i8, h8, g8⟩ :=
    step168_counts v csa168Step8Spec 3 11 rCore rSum14 rWork hCSum hCW hSW w 3 180 203 109
  dsimp only [dCleanHybridStreamAdd164, dCleanHybridStreamInv164]
  simp only [count_seq_eq, t1, t2, t3, t4, t5, t6, t7, t8, i2, i3, i4, i5, i6, i7, i8]
  exact ⟨trivial, trivial, by omega, by omega⟩
noncomputable def uHybridStream164 {mPayload : ℕ} (w : Fin 3) :
    Unitary (2 ^ (fullSysCoreWires mPayload + 14)) :=
  let kC := fullSysCoreWires mPayload
  let uAdd {B₀ B₁ B₂ : ℕ} (off len : ℕ) (inC : Fin (B₀ + B₁ + B₂) → Wire kC)
      (h : off + len ≤ 14 := by decide) :=
    (selCoreSlice kC off len h).embedUnitary (catModAddUnitary kC len (weightedGenBatchVal inC))
  uAdd 3 11 (chunk168 w 3 180 38 203 15 109 109) *
    (uAdd 3 11 (chunk168 w 3 172 8 143 60 13 96) *
      (uAdd 3 10 (chunk168 w 3 80 92 81 62 3 10) *
        (uAdd 3 9 (chunk168 w 3 0 80 0 81 0 3) *
          (uAdd 0 11 (chunk168 w 0 191 27 202 16 107 111) *
            (uAdd 0 10 (chunk168 w 0 183 8 142 60 11 96) *
              (uAdd 0 9 (chunk168 w 0 91 92 80 62 1 10) *
                (selCoreSlice kC 0 8 (by decide)).embedUnitary
                  (uBitXor kC 8 (weightedGenBatchVal (chunk168 w 0 0 91 0 80 0 1)))))))))
theorem uHybridStream164_compute_ket {mPayload n : ℕ} [NeZero (2 ^ n)] (w : Fin 3)
    (rCore : QRegister (fullSysCoreWires mPayload) n) (rSum14 : QRegister 14 n)
    (hCSum : rCore.DisjointWires rSum14) : ∀ β₀ : Fin n → ZMod 2,
    (∀ i : Fin 14, β₀ (rSum14 i) = 0) → ∃ β : Fin n → ZMod 2, ((rCore.concat rSum14
    hCSum).embedUnitary (uHybridStream164 w)).1.mulVec (basisKet β₀) = basisKet β ∧
    (∀ g : Fin n, g ∉ rSum14.image → β g = β₀ g) ∧ (∀ i : Fin 14, β (rSum14 i) = if
    (slot2AxisSum w (fun q ↦ β₀ (rCore q))).testBit i.val then 1 else 0) := by
  intro β₀ hz
  let w1 := chunk168 (mPayload := mPayload) w 0 0 91 0 80 0 1
  let w2 := chunk168 (mPayload := mPayload) w 0 91 92 80 62 1 10
  let w3 := chunk168 (mPayload := mPayload) w 0 183 8 142 60 11 96
  let w4 := chunk168 (mPayload := mPayload) w 0 191 27 202 16 107 111
  let w5 := chunk168 (mPayload := mPayload) w 3 0 80 0 81 0 3
  let w6 := chunk168 (mPayload := mPayload) w 3 80 92 81 62 3 10
  let w7 := chunk168 (mPayload := mPayload) w 3 172 8 143 60 13 96
  let w8 := chunk168 (mPayload := mPayload) w 3 180 38 203 15 109 109
  have hb1 : weightedGenBatchVal w1 (fun q ↦ β₀ (rCore q)) ≤ 255 := weightedGenBatchVal_le w1 _
  have hb2 : weightedGenBatchVal w2 (fun q ↦ β₀ (rCore q)) ≤ 256 := weightedGenBatchVal_le w2 _
  have hb3 : weightedGenBatchVal w3 (fun q ↦ β₀ (rCore q)) ≤ 512 := weightedGenBatchVal_le w3 _
  have hb4 : weightedGenBatchVal w4 (fun q ↦ β₀ (rCore q)) ≤ 503 := weightedGenBatchVal_le w4 _
  have hb5 : weightedGenBatchVal w5 (fun q ↦ β₀ (rCore q)) ≤ 254 := weightedGenBatchVal_le w5 _
  have hb6 : weightedGenBatchVal w6 (fun q ↦ β₀ (rCore q)) ≤ 256 := weightedGenBatchVal_le w6 _
  have hb7 : weightedGenBatchVal w7 (fun q ↦ β₀ (rCore q)) ≤ 512 := weightedGenBatchVal_le w7 _
  have hb8 : weightedGenBatchVal w8 (fun q ↦ β₀ (rCore q)) ≤ 504 := weightedGenBatchVal_le w8 _
  obtain ⟨β₁, hket₁, hInv₁⟩ := accInvar_step1_bitXor8 rCore rSum14 hCSum (weightedGenBatchVal w1)
    β₀ (accInvar_zero rSum14 β₀ hz) (by omega)
  obtain ⟨β₂, hket₂, hInv₂⟩ := accInvar_step_sliceModAdd rCore rSum14 hCSum 0 9 (by decide)
    (weightedGenBatchVal w2) _ β₀ β₁ hInv₁ (by omega) (by omega)
  obtain ⟨β₃, hket₃, hInv₃⟩ := accInvar_step_sliceModAdd rCore rSum14 hCSum 0 10 (by decide)
    (weightedGenBatchVal w3) _ β₀ β₂ hInv₂ (by omega) (by omega)
  obtain ⟨β₄, hket₄, hInv₄⟩ := accInvar_step_sliceModAdd rCore rSum14 hCSum 0 11 (by decide)
    (weightedGenBatchVal w4) _ β₀ β₃ hInv₃ (by omega) (by omega)
  obtain ⟨β₅, hket₅, hInv₅⟩ := accInvar_step_sliceModAdd rCore rSum14 hCSum 3 9 (by decide)
    (weightedGenBatchVal w5) _ β₀ β₄ hInv₄ (by omega) (by omega)
  obtain ⟨β₆, hket₆, hInv₆⟩ := accInvar_step_sliceModAdd rCore rSum14 hCSum 3 10 (by decide)
    (weightedGenBatchVal w6) _ β₀ β₅ hInv₅ (by omega) (by omega)
  obtain ⟨β₇, hket₇, hInv₇⟩ := accInvar_step_sliceModAdd rCore rSum14 hCSum 3 11 (by decide)
    (weightedGenBatchVal w7) _ β₀ β₆ hInv₆ (by omega) (by omega)
  obtain ⟨β₈, hket₈, hInv₈⟩ := accInvar_step_sliceModAdd rCore rSum14 hCSum 3 11 (by decide)
    (weightedGenBatchVal w8) _ β₀ β₇ hInv₇ (by omega) (by omega)
  rw [hybrid168EightBatch_eq_slot2AxisSum w (fun q ↦ β₀ (rCore q))] at hInv₈
  refine ⟨β₈, ?_, hInv₈.1, hInv₈.2⟩
  simp only [uHybridStream164, QRegister.embedUnitary_mul, Submonoid.coe_mul,
    ← Matrix.mulVec_mulVec]
  rw [hket₁, hket₂, hket₃, hket₄, hket₅, hket₆, hket₇, hket₈]
theorem dCleanHybridStream164_cleanPair_explicit {Var : Type} [Fintype Var] [DecidableEq Var]
    {mPayload mWork n : ℕ} [NeZero (2 ^ n)] (v : Var) (w : Fin 3)
    (rCore : QRegister (fullSysCoreWires mPayload) n) (rSum14 : QRegister 14 n)
    (rWork : QRegister mWork n) (hCSum : rCore.DisjointWires rSum14)
    (hCW : rCore.DisjointWires rWork) (hSW : rSum14.DisjointWires rWork)
    (hmWork : 164 ≤ mWork) : CleanComputePair rCore rSum14 rWork hCSum (uHybridStream164 w)
    (fun xCore i ↦ if (slot2AxisSum w xCore).testBit i.val then 1 else 0)
    (dCleanHybridStreamAdd164 v w rCore rSum14 rWork hCSum hCW hSW hmWork)
    (dCleanHybridStreamInv164 v w rCore rSum14 rWork hCSum hCW hSW hmWork) := by
  have hActW : (rCore.concat rSum14 hCSum).DisjointWires rWork :=
    QRegExt.disjointWires_concat_left hCW hSW
  have p1 := liftCleanPair_slice14 hCSum 0 8 (by decide)
    (dStep1Xor8_168_realizesPair v rCore (rSum14.slice 0 8 (by decide)) rWork
      (disj_slice14 hCSum 0 8 (by decide)) hCW (disj_slice14_work hSW 0 8 (by decide)) hmWork
      (chunk168 w 0 0 91 0 80 0 1)
      (threePlaneGenChunkWire_injective w 0 0 91 0 80 0 1 (by decide) (by decide) (by decide)
        (by decide)))
  have p2 := step168_pair v csa168StepASpec 0 9 rCore rSum14 rWork hCSum hCW hSW w 0 91 80 1
  have p3 := step168_pair v csa168StepBSpec 0 10 rCore rSum14 rWork hCSum hCW hSW w 0 183 142 11
  have p4 := step168_pair v csa168Step4Spec 0 11 rCore rSum14 rWork hCSum hCW hSW w 0 191 202 107
  have p5 := step168_pair v csa168Step5Spec 3 9 rCore rSum14 rWork hCSum hCW hSW w 3 0 0 0
  have p6 := step168_pair v csa168StepASpec 3 10 rCore rSum14 rWork hCSum hCW hSW w 3 80 81 3
  have p7 := step168_pair v csa168StepBSpec 3 11 rCore rSum14 rWork hCSum hCW hSW w 3 172 143 13
  have p8 := step168_pair v csa168Step8Spec 3 11 rCore rSum14 rWork hCSum hCW hSW w 3 180 203 109
  have pAll :=
    ((((((p1.seq hActW p2).seq hActW p3).seq hActW p4).seq hActW p5).seq hActW p6).seq hActW p7).seq
    hActW p8
  change RealizesCleanPair (rCore.concat rSum14 hCSum) rWork (uHybridStream164 w) _ _ at pAll
  exact ⟨pAll, uHybridStream164_compute_ket w rCore rSum14 hCSum⟩
attribute [local irreducible] dCleanHybridStreamAdd164 dCleanHybridStreamInv164
end ConfigHybridStream168
end HybridStream168Aux
end
end ModHybridStream168

end QuantumComputation.Specs.StoppingPowerSolution
