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

public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.PosPass2UnbarHarm
set_option Elab.async false

@[expose] public section
set_option allowUnsafeReducibility true
set_option exponentiation.threshold 256

namespace QuantumComputation.Specs.StoppingPowerSolution
open SpecsAux

section Leaf3Prep179Spec
local instance (priority := 1000000) instNeZeroTwoPow_Leaf3Prep179Spec (k : ℕ) :
    NeZero (2 ^ k) := ⟨(Nat.two_pow_pos k).ne'⟩

/-
# `165`-Wire `3,242 T` RT Catalyst-Free Slot-3 State Preparation

Compact, catalyst-free Slot-3 `216`-shell state-preparation pair `(dPrep3_216_179,
dPrep3_216Inv_179)`
(and `165`-wire / polymorphic `165 ≤ mPrep` specializations) on `rCore : QRegister (momCoreWires 80)
n`
and clean workspace `rWork`:
- **Stage 1 (`progStage1Kc49`, `68` `TempAnd`s = `272 T` forward + `88 T` `PhaseQrom8BitPruned22`
  X-measurement uncompute = `360 T`)**: computes the `16`-bit shell threshold `kc(c8)` into `16`
  ancilla wires `[33..49)` using `68` clean scratch wires (`68 ≤ 149`), uncomputing the `68` scratch
  wires at `0 T`.
- **Stage 2 (`progStage2Unpack71`, `64` `TempAnd`s = `256 T` forward + `256 T` reverse = `512 T`)**:
  unpacks `z7` + `3 × 7`-bit `shiftedMag3 u22` into `22` ancilla wires `[49..71)` using `64` clean
  scratch wires (`64 ≤ 127`), uncomputing the `64` scratch wires at `0 T`.
- **Stage 3 + Stage 4 (`ssaKick198`, `27 + 100 = 127` `TempAnd`s = `508 T`)**: evaluates the
`27`-AND
  shell validity flag `validWire` (`97`) and `100`-AND carry-save threshold sum `carry16Wire`
  (`197`)
  on `71 + 127 = 198` total wires (`33` active + `165` workspace), kicking the target phase via a
  `0-T` `CZ` gate before Stage 2 uncomputes `[49..71)` and `PhaseQrom8BitPruned22` uncomputes
  `[33..49)`.
- **OAA + `3`-Qutrit Closure (`1,380 + 124 + 117 = 1,621 T` each way, `3,242 T` RT, `0` `.TOFF`)**:
  combines `dCoarseGood33_165` (`1,380 T`), `progNotZero33Cz` (`124 T`, `33 ≤ 165`),
  `hadamardPayloadDyn`,
  and catalyst-free `cQutrit3Core` (`117 T` directly on `rCore`).
-/

public section

namespace Leaf3Prep179Spec

section ConfigLeaf3Prep179Spec

set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 2000

local instance (priority :=
  10) instLoc_Leaf3Prep179Spec_1InstNeZeroTwoPowW7Prep179 (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩

open scoped Matrix ComplexOrder MatrixOrder BigOperators Matrix.Norms.L2Operator Circuit.Notation
open Operator Matrix QProg Circuit _root_.DynamicCircuit DynCircuitExt Real LocalClassicalPerm
open MeasureBranchHadamardSem (bit_cases ket)
open _root_.QuantumComputation.Specs.StoppingPowerSolution (ValidCleanRem TempPhaseProg TempCtx
  cleanRem)
open _root_.QuantumComputation.Specs.StoppingPowerSolution (validCleanRem_mono wire_ne_of_lt
  wire_ne_of_gt CliffProg)
open MomSlot0CircuitHalf (padZeroBits phaseDiagUnitary)
open MomSlot1GeomPriority288 (RawSsa SsaProg phaseDiagAct compileSsaCzDyn)
open MomSlot1GeomPriority288 (compileSsaCzDyn_count_toff)
open MomSlot1GeomPriority288 (compileSsaCzDyn_count_t b2z)
open MomSlots35Slot3ProjNuclear (s3Bound_0_22 s3Bound_22_3)
open MomSlots35Slot3ProjNuclear (s3Bound_25_8 predCoarseGood33)
open MomSlots35Slot3ProjNuclear (shellMu3 validShellNu3)
open MomSlots35Slot3ProjNuclear (coarseGood3Computable)
open Slot5MatrixAndScaleCert (signBit3)
open FullSysMomSlots0135Concrete (momCoreWires)
open ShiftedMagS1 (shiftedMag3 shiftedMag3_lt_128 shiftedMag3_testBit)
open ShiftedMagS1 (validShellNu3_eq_shifted sTilde3 sTilde3_le_48387)
open ShiftedMagS1 (thr16 coarseGood3Computable_eq_sTilde itePos)
open ShiftedMagS1 (iteNeg ditePos diteNeg)
open ShiftedMagS1 (bitsVal_eq_of_testBit testBit_div_two_powAux)
open ShiftedMagS1 (testBit_mod_two_powAux top7Mu)
open ShiftedMagS1 (top7Mu_eq_shellMu3)
open ShiftedMagS1 (embedUnitary_permSignUnitary_mulVec_single)
open PosSlots24PartnerMux288 (permSignUnitary)
open Slot3Exact216Oracle80 (cPrepQutrit2 cPrepQutrit2_count_toff)
open Slot3Exact216Oracle80 (cPrepQutrit2_count_t s3QutritPairCore)
open Slot3Exact216Oracle80 (uQutrit3 s3EmbedUnitary_mul)

theorem zmod2_add_cancel_right (a b : ZMod 2) : a + b + b = a := by
  rcases bit_cases a with rfl | rfl <;> rcases bit_cases b with rfl | rfl <;> decide
theorem b2z_not (x : Bool) : b2z (Bool.not x) = b2z x + 1 := by
  cases x <;> decide
theorem b2z_xor (x y : Bool) : b2z (xor x y) = b2z x + b2z y := by
  cases x <;> cases y <;> decide
theorem b2z_and (x y : Bool) : b2z (x && y) = b2z x * b2z y := by
  cases x <;> cases y <;> decide
theorem zmod2_eq_b2z (z : ZMod 2) : z = b2z (decide (z = 1)) := by
  rcases bit_cases z with rfl | rfl <;> decide
theorem b2z_val (b : Bool) : (b2z b).val = if b then 1 else 0 := by
  cases b <;> rfl
theorem bool_beq_iff (a b : Bool) : (a == b) = true ↔ a = b := by
  cases a <;> cases b <;> decide
/-- Bridge equality `phaseDiagAct_eq_unitary` for `Leaf3Prep179Spec`. -/
theorem phaseDiagAct_eq_unitary {kAct : ℕ} (pred : BitAssignment kAct → ZMod 2) :
    phaseDiagAct pred = phaseDiagUnitary pred :=
  Subtype.ext rfl

/-- Helper `checkOpt` for compact `165`-wire Slot-3 state preparation. -/
def checkOpt {α : Type} (x : Option α) (f : α → Bool) : Bool :=
  match x with
  | none => false
  | some v => f v
theorem checkOpt_sound {α : Type} {x : Option α} {f : α → Bool}
    (h : checkOpt x f = true) : ∃ v, x = some v ∧ f v = true := by
  cases x with
  | none => cases h
  | some v => exact ⟨v, rfl, h⟩
theorem padZeroBits_lt {k m : ℕ} (α : BitAssignment k) (w : Wire (k + m)) (hw : w.val < k) :
    padZeroBits (kAct := k) (mClean := m) α w = α ⟨w.val, hw⟩ := by
  have h : w = Fin.castAdd m ⟨w.val, hw⟩ := Fin.ext rfl
  conv_lhs => rw [h]
  exact Fin.addCases_left ⟨w.val, hw⟩
theorem padZeroBits_ge {k m : ℕ} (α : BitAssignment k) (w : Wire (k + m)) (hw : k ≤ w.val) :
    padZeroBits (kAct := k) (mClean := m) α w = 0 := by
  have h : w = Fin.natAdd k ⟨w.val - k, by omega⟩ := Fin.ext (by dsimp; omega)
  conv_lhs => rw [h]
  exact Fin.addCases_right ⟨w.val - k, by omega⟩
theorem dynCount_seq {Var : Type} {n k : ℕ} (d₁ d₂ : DynamicCircuit Var n) (g : PrimitiveGate k) :
    (DynamicCircuit.seq d₁ d₂).count g = d₁.count g + d₂.count g := rfl
/-- Helper `MicroStep` for compact `165`-wire Slot-3 state preparation. -/
inductive MicroStep where
  | nW (a : ℕ)
  | cW (a b : ℕ)
  | aW (a b : ℕ)
/-- End scratch-cursor index after executing `MicroStep` list. -/
@[reducible] def microEnd : ℕ → List MicroStep → ℕ
  | c, [] => c
  | c, .nW _ :: rest => microEnd c rest
  | c, .cW _ _ :: rest => microEnd c rest
  | c, .aW _ _ :: rest => microEnd (c + 1) rest
/-- Helper `microAllocs` for compact `165`-wire Slot-3 state preparation. -/
def microAllocs : List MicroStep → ℕ
  | [] => 0
  | .nW _ :: rest => microAllocs rest
  | .cW _ _ :: rest => microAllocs rest
  | .aW _ _ :: rest => 1 + microAllocs rest
theorem microEnd_eq_add : ∀ (ops : List MicroStep) (c : ℕ),
    microEnd c ops = c + microAllocs ops
  | [], c => by simp [microEnd, microAllocs]
  | .nW _ :: rest, c => microEnd_eq_add rest c
  | .cW _ _ :: rest, c => microEnd_eq_add rest c
  | .aW _ _ :: rest, c => by
      dsimp only [microEnd, microAllocs]
      rw [microEnd_eq_add rest (c + 1)]
      omega
/-- Helper `microValid` for compact `165`-wire Slot-3 state preparation. -/
def microValid : ℕ → List MicroStep → Bool
  | _, [] => true
  | top, .nW a :: rest => decide (a < top) && microValid top rest
  | top, .cW a b :: rest =>
      decide (a < top) && decide (b < top) && decide (a ≠ b) && microValid top rest
  | top, .aW a b :: rest =>
      decide (a < top) && decide (b < top) && decide (a ≠ b) && microValid (top + 1) rest
theorem microValid_nW {top a : ℕ} {rest : List MicroStep}
    (hv : microValid top (.nW a :: rest) = true) : a < top ∧ microValid top rest = true := by
  simpa [microValid, Bool.and_eq_true, decide_eq_true_eq] using hv
theorem microValid_cW {top a b : ℕ} {rest : List MicroStep}
    (hv : microValid top (.cW a b :: rest) = true) :
    a < top ∧ b < top ∧ a ≠ b ∧ microValid top rest = true := by
  simpa [microValid, Bool.and_eq_true, decide_eq_true_eq, and_assoc] using hv
theorem microValid_aW {top a b : ℕ} {rest : List MicroStep}
    (hv : microValid top (.aW a b :: rest) = true) :
    a < top ∧ b < top ∧ a ≠ b ∧ microValid (top + 1) rest = true := by
  simpa [microValid, Bool.and_eq_true, decide_eq_true_eq, and_assoc] using hv
/-- Helper `getBoolAt` for compact `165`-wire Slot-3 state preparation. -/
def getBoolAt : List Bool → ℕ → Bool
  | [], _ => false
  | b :: _, 0 => b
  | _ :: bs, k + 1 => getBoolAt bs k
/-- Helper `setBoolAt` for compact `165`-wire Slot-3 state preparation. -/
def setBoolAt : List Bool → ℕ → Bool → List Bool
  | [], _, _ => []
  | _ :: bs, 0, v => v :: bs
  | b :: bs, k + 1, v => b :: setBoolAt bs k v
theorem length_setBoolAt : ∀ (st : List Bool) (k : ℕ) (v : Bool),
    (setBoolAt st k v).length = st.length
  | [], _, _ => rfl
  | _ :: _, 0, _ => rfl
  | _ :: bs, k + 1, v => by simp [setBoolAt, length_setBoolAt bs k v]
theorem getBoolAt_setBoolAt : ∀ (st : List Bool) (k i : ℕ),
    k < st.length → ∀ (v : Bool),
    getBoolAt (setBoolAt st k v) i = if i = k then v else getBoolAt st i
  | [], _, _, hk, _ => absurd hk (Nat.not_lt_zero _)
  | _ :: _, 0, 0, _, _ => rfl
  | _ :: _, 0, _ + 1, _, _ => rfl
  | _ :: _, _ + 1, 0, _, _ => rfl
  | _ :: bs, k + 1, i + 1, hk, v => by
      dsimp only [setBoolAt, getBoolAt]
      rw [getBoolAt_setBoolAt bs k i (by simp at hk; omega) v]
      by_cases h : i = k <;> simp [h]
/-- Helper `evalMicroList` for compact `165`-wire Slot-3 state preparation. -/
def evalMicroList : ℕ → List MicroStep → List Bool → List Bool
  | _, [], st => st
  | top, .nW a :: rest, st =>
      evalMicroList top rest (setBoolAt st a (Bool.not (getBoolAt st a)))
  | top, .cW a b :: rest, st =>
      evalMicroList top rest (setBoolAt st b (xor (getBoolAt st b) (getBoolAt st a)))
  | top, .aW a b :: rest, st =>
      evalMicroList (top + 1) rest (setBoolAt st top (getBoolAt st a && getBoolAt st b))
/-- Helper `mkBoolList` for compact `165`-wire Slot-3 state preparation. -/
def mkBoolList (nIn mask off : ℕ) : ℕ → List Bool
  | 0 => []
  | rem + 1 => (decide (off < nIn) && mask.testBit off) :: mkBoolList nIn mask (off + 1) rem
theorem length_mkBoolList (nIn mask off : ℕ) : ∀ rem : ℕ,
    (mkBoolList nIn mask off rem).length = rem
  | 0 => rfl
  | rem + 1 => by simp [mkBoolList, length_mkBoolList nIn mask (off + 1) rem]
theorem getBoolAt_mkBoolList (nIn mask : ℕ) :
    ∀ (off rem k : ℕ), k < rem →
      getBoolAt (mkBoolList nIn mask off rem) k =
        (decide (off + k < nIn) && mask.testBit (off + k))
  | _, 0, _, hk => absurd hk (Nat.not_lt_zero _)
  | off, _ + 1, 0, _ => by simp [mkBoolList, getBoolAt]
  | off, rem + 1, k + 1, hk => by
      dsimp only [mkBoolList, getBoolAt]
      rw [getBoolAt_mkBoolList nIn mask (off + 1) rem k (by omega)]
      have heq : off + 1 + k = off + (k + 1) := by omega
      rw [heq]
/-- Helper `initBoolList` for compact `165`-wire Slot-3 state preparation. -/
def initBoolList (nIn len mask : ℕ) : List Bool := mkBoolList nIn mask 0 len
/-- Helper `microSlotWire` for compact `165`-wire Slot-3 state preparation. -/
def microSlotWire {M nIn : ℕ} (inW : Fin nIn → Wire M) (cur s : ℕ)
    (hs : nIn ≤ s → cur + (s - nIn) < M) : Wire M :=
  if h : s < nIn then inW ⟨s, h⟩ else ⟨cur + (s - nIn), hs (Nat.le_of_not_lt h)⟩
theorem microSlotWire_lt_in {M nIn : ℕ} (inW : Fin nIn → Wire M) (cur s : ℕ) (hs : s < nIn)
    (hb : nIn ≤ s → cur + (s - nIn) < M) : microSlotWire inW cur s hb = inW ⟨s, hs⟩ := by
  dsimp [microSlotWire]; exact ditePos hs
theorem microSlotWire_ge_in {M nIn : ℕ} (inW : Fin nIn → Wire M) (cur s : ℕ) (hs : nIn ≤ s)
    (hb : nIn ≤ s → cur + (s - nIn) < M) :
    microSlotWire inW cur s hb = ⟨cur + (s - nIn), hb hs⟩ := by
  dsimp [microSlotWire]; exact diteNeg (by omega)
/-- Helper `ssaCastEnd` for compact `165`-wire Slot-3 state preparation. -/
def ssaCastEnd {M cur c₁ c₂ : ℕ} (h : c₁ = c₂) (P : SsaProg M cur c₁) : SsaProg M cur c₂ :=
  h ▸ P
theorem ssaCastEnd_countAnd {M cur c₁ c₂ : ℕ} (h : c₁ = c₂) (P : SsaProg M cur c₁) :
    (ssaCastEnd h P).countAnd = P.countAnd := by
  subst h; rfl
theorem ssaCastEnd_eval {M cur c₁ c₂ : ℕ} (h : c₁ =
    c₂) (P : SsaProg M cur c₁) (β : BitAssignment M) :
    (ssaCastEnd h P).eval β = P.eval β := by
  subst h; rfl
theorem microSlotBound {M nIn cur₀ top cur s : ℕ}
    (hrel : nIn + cur = cur₀ + top ∧ nIn ≤ top) (hs : s < top) (hce : cur ≤ M) :
    nIn ≤ s → cur₀ + (s - nIn) < M := fun _ ↦ by
  obtain ⟨_, _⟩ := hrel; omega
theorem microSlotWire_val_lt {M nIn : ℕ} (inW : Fin nIn → Wire M) (cur₀ : ℕ)
    (hin_lt : ∀ i, (inW i).val < cur₀) {top cur s : ℕ}
    (hrel : nIn + cur = cur₀ + top ∧ nIn ≤ top) (hs : s < top)
    (hb : nIn ≤ s → cur₀ + (s - nIn) < M) : (microSlotWire inW cur₀ s hb).val < cur := by
  obtain ⟨_, _⟩ := hrel
  by_cases hlt : s < nIn
  · rw [microSlotWire_lt_in inW cur₀ s hlt]
    have := hin_lt ⟨s, hlt⟩; omega
  · rw [microSlotWire_ge_in inW cur₀ s (by omega)]
    dsimp; omega
theorem microSlotWire_ne {M nIn : ℕ} (inW : Fin nIn → Wire M) (hin_inj : Function.Injective inW)
    (cur : ℕ) (hin_lt : ∀ i, (inW i).val < cur)
    {s₁ s₂ : ℕ} (hne : s₁ ≠ s₂)
    (hb₁ : nIn ≤ s₁ → cur + (s₁ - nIn) < M) (hb₂ : nIn ≤ s₂ → cur + (s₂ - nIn) < M) :
    microSlotWire inW cur s₁ hb₁ ≠ microSlotWire inW cur s₂ hb₂ := by
  by_cases h1 : s₁ < nIn <;> by_cases h2 : s₂ < nIn
  · rw [microSlotWire_lt_in inW cur s₁ h1, microSlotWire_lt_in inW cur s₂ h2]
    intro heq; exact hne (congrArg Fin.val (hin_inj heq))
  · rw [microSlotWire_lt_in inW cur s₁ h1, microSlotWire_ge_in inW cur s₂ (by omega)]
    exact wire_ne_of_lt (by have := hin_lt ⟨s₁, h1⟩; dsimp; omega)
  · rw [microSlotWire_ge_in inW cur s₁ (by omega), microSlotWire_lt_in inW cur s₂ h2]
    exact wire_ne_of_gt (by have := hin_lt ⟨s₂, h2⟩; dsimp; omega)
  · rw [microSlotWire_ge_in inW cur s₁ (by omega), microSlotWire_ge_in inW cur s₂ (by omega)]
    intro heq; have hv := congrArg Fin.val heq; dsimp at hv; omega
/-- Helper `ssaMicroRun` for compact `165`-wire Slot-3 state preparation. -/
def ssaMicroRun {M nIn : ℕ} (inW : Fin nIn → Wire M)
    (hin_inj : Function.Injective inW) (cur₀ : ℕ) (hin_lt : ∀ i, (inW i).val < cur₀) :
    (top cur : ℕ) → (hrel : nIn + cur = cur₀ + top ∧ nIn ≤ top) → (ops : List MicroStep) →
    (hv : microValid top ops = true) →
    (hM : microEnd cur ops ≤ M) →
    SsaProg M cur (microEnd cur ops)
  | _, cur, _, [], _, _ => .done cur
  | top, cur, hrel, .nW a :: rest, hv, hM =>
      have ha : a < top := (microValid_nW hv).1
      have hM' : microEnd cur rest ≤ M := hM
      have hce : cur ≤ M := by have := microEnd_eq_add rest cur; omega
      let wA := microSlotWire inW cur₀ a (microSlotBound hrel ha hce)
      .x wA (microSlotWire_val_lt inW cur₀ hin_lt hrel ha _)
        (ssaMicroRun inW hin_inj cur₀ hin_lt top cur hrel rest (microValid_nW hv).2 hM)
  | top, cur, hrel, .cW a b :: rest, hv, hM =>
      have h := microValid_cW hv
      have hM' : microEnd cur rest ≤ M := hM
      have hce : cur ≤ M := by have := microEnd_eq_add rest cur; omega
      let wA := microSlotWire inW cur₀ a (microSlotBound hrel h.1 hce)
      let wB := microSlotWire inW cur₀ b (microSlotBound hrel h.2.1 hce)
      .cnot wA wB (microSlotWire_ne inW hin_inj cur₀ hin_lt h.2.2.1 _ _)
        (microSlotWire_val_lt inW cur₀ hin_lt hrel h.1 _)
        (microSlotWire_val_lt inW cur₀ hin_lt hrel h.2.1 _)
        (ssaMicroRun inW hin_inj cur₀ hin_lt top cur hrel rest h.2.2.2 hM)
  | top, cur, hrel, .aW a b :: rest, hv, hM =>
      have h := microValid_aW hv
      have hM' : microEnd (cur + 1) rest ≤ M := hM
      have hcur : cur < M := by
        have := microEnd_eq_add rest (cur + 1); omega
      have hce : cur ≤ M := Nat.le_of_lt hcur
      let wA := microSlotWire inW cur₀ a (microSlotBound hrel h.1 hce)
      let wB := microSlotWire inW cur₀ b (microSlotBound hrel h.2.1 hce)
      .andClean hcur wA wB (microSlotWire_ne inW hin_inj cur₀ hin_lt h.2.2.1 _ _)
        (microSlotWire_val_lt inW cur₀ hin_lt hrel h.1 _)
        (microSlotWire_val_lt inW cur₀ hin_lt hrel h.2.1 _)
        (ssaMicroRun inW hin_inj cur₀ hin_lt (top + 1) (cur + 1)
          ⟨by obtain ⟨_, _⟩ := hrel; omega, by obtain ⟨_, _⟩ := hrel; omega⟩ rest h.2.2.2 hM)
private theorem wire_ne_microSlotWire_of_lt_not_in {M nIn : ℕ} (inW : Fin nIn → Wire M)
    (cur₀ : ℕ) {w : Wire M} (hw : w.val < cur₀) (hni : ∀ i, w ≠ inW i)
    (s : ℕ) (hb : nIn ≤ s → cur₀ + (s - nIn) < M) :
    w ≠ microSlotWire inW cur₀ s hb := by
  by_cases hlt : s < nIn
  · rw [microSlotWire_lt_in inW cur₀ s hlt hb]
    exact hni ⟨s, hlt⟩
  · rw [microSlotWire_ge_in inW cur₀ s (by omega) hb]
    exact wire_ne_of_lt (by dsimp; omega)

private theorem clean_ge_update_lt {M cur : ℕ} {β : BitAssignment M} {q : Wire M} (v : ZMod 2)
    (hq : q.val < cur) (hcl : ∀ w : Wire M, cur ≤ w.val → β w = 0) :
    ∀ w : Wire M, cur ≤ w.val → Function.update β q v w = 0 := fun w hw ↦ by
  rw [Function.update_of_ne (wire_ne_of_gt (by omega))]
  exact hcl w hw

private theorem microSlotWire_update_setBoolAt {M nIn top cur cur₀ : ℕ} (inW : Fin nIn → Wire M)
    (hin_inj : Function.Injective inW) (hin_lt : ∀ i, (inW i).val < cur₀)
    (hrel : nIn + cur = cur₀ + top ∧ nIn ≤ top) (hce : cur ≤ M)
    {β : BitAssignment M} {st : List Bool} (hlen : top ≤ st.length)
    (hst : ∀ (s : ℕ) (hs : s < top),
      β (microSlotWire inW cur₀ s (microSlotBound hrel hs hce)) = b2z (getBoolAt st s))
    {t : ℕ} (ht : t < top) (v : ZMod 2) (bv : Bool) (hv : v = b2z bv) :
    ∀ (s : ℕ) (hs : s < top),
      Function.update β (microSlotWire inW cur₀ t (microSlotBound hrel ht hce)) v
        (microSlotWire inW cur₀ s (microSlotBound hrel hs hce)) =
        b2z (getBoolAt (setBoolAt st t bv) s) := fun s hs ↦ by
  rw [getBoolAt_setBoolAt st t s (by omega)]
  by_cases hst_eq : s = t
  · subst hst_eq
    rw [Function.update_self, itePos rfl, hv]
  · rw [Function.update_of_ne (microSlotWire_ne inW hin_inj cur₀ hin_lt hst_eq _ _),
      iteNeg hst_eq, hst s hs]

theorem ssaMicroRun_spec {M nIn : ℕ} (inW : Fin nIn → Wire M)
    (hin_inj : Function.Injective inW) (cur₀ : ℕ) (hin_lt : ∀ i, (inW i).val < cur₀) :
    ∀ (ops : List MicroStep) (top cur : ℕ) (hrel : nIn + cur = cur₀ + top ∧ nIn ≤ top)
      (hv : microValid top ops = true)
      (hM : microEnd cur ops ≤ M),
      (ssaMicroRun inW hin_inj cur₀ hin_lt top cur hrel ops hv hM).countAnd = microAllocs ops ∧
      (∀ (β : BitAssignment M) (st : List Bool),
        (∀ w : Wire M, cur ≤ w.val → β w = 0) →
        st.length = top + microAllocs ops →
        (∀ (s : ℕ) (hs : s < top),
          β (microSlotWire inW cur₀ s
            (microSlotBound hrel hs (by have := microEnd_eq_add ops cur; omega))) =
            b2z (getBoolAt st s)) →
        (∀ w : Wire M, microEnd cur ops ≤ w.val →
          (ssaMicroRun inW hin_inj cur₀ hin_lt top cur hrel ops hv hM).eval β w = 0) ∧
        (∀ w : Wire M, w.val < cur₀ → (∀ i, w ≠ inW i) →
          (ssaMicroRun inW hin_inj cur₀ hin_lt top cur hrel ops hv hM).eval β w = β w) ∧
        (∀ (s : ℕ) (hs : s < top + microAllocs ops),
          (ssaMicroRun inW hin_inj cur₀ hin_lt top cur hrel ops hv hM).eval β
            (microSlotWire inW cur₀ s
              (microSlotBound (top := top + microAllocs ops) (cur := microEnd cur ops)
                ⟨by obtain ⟨_, _⟩ := hrel; have := microEnd_eq_add ops cur; omega,
                 by obtain ⟨_, _⟩ := hrel; omega⟩ hs hM)) =
            b2z (getBoolAt (evalMicroList top ops st) s))) := by
  intro ops
  induction ops with
  | nil =>
      intro top cur hrel hv hM
      dsimp only [ssaMicroRun, microAllocs, microEnd, evalMicroList]
      simp only [SsaProg.countAnd_done, SsaProg.eval_done]
      exact ⟨trivial, fun β st hcl _ hst ↦ ⟨hcl, fun _ _ _ ↦ trivial, fun s hs ↦ hst s (by omega)⟩⟩
  | cons op rest ih =>
      cases op with
      | nW a =>
          intro top cur hrel hv hM
          obtain ⟨ha, hvR⟩ := microValid_nW hv
          obtain ⟨hCnt, hEv⟩ := ih top cur hrel hvR hM
          refine ⟨by dsimp only [ssaMicroRun, microAllocs]; rw [SsaProg.countAnd_x, hCnt],
            fun β st hcl hlen hst ↦ ?_⟩
          dsimp only [ssaMicroRun, evalMicroList, microAllocs, microEnd] at *
          simp only [SsaProg.eval_x]
          have hce : cur ≤ M := by
            have : microEnd cur rest ≤ M := hM; have := microEnd_eq_add rest cur; omega
          let wA := microSlotWire inW cur₀ a (microSlotBound hrel ha hce)
          obtain ⟨hcO, hpO, hsO⟩ := hEv _ _
            (clean_ge_update_lt _ (microSlotWire_val_lt inW cur₀ hin_lt hrel ha _) hcl)
            (by rw [length_setBoolAt]; exact hlen)
            (microSlotWire_update_setBoolAt inW hin_inj hin_lt hrel hce (by omega) hst ha
              (β wA + 1) (!getBoolAt st a) (by rw [hst a ha, b2z_not]))
          refine ⟨hcO, fun w hw hni ↦ (hpO w hw hni).trans ?_, hsO⟩
          exact Function.update_of_ne (wire_ne_microSlotWire_of_lt_not_in inW cur₀ hw hni a _) _ _
      | cW a b =>
          intro top cur hrel hv hM
          obtain ⟨ha, hb, _, hvR⟩ := microValid_cW hv
          obtain ⟨hCnt, hEv⟩ := ih top cur hrel hvR hM
          refine ⟨by dsimp only [ssaMicroRun, microAllocs]; rw [SsaProg.countAnd_cnot, hCnt],
            fun β st hcl hlen hst ↦ ?_⟩
          dsimp only [ssaMicroRun, evalMicroList, microAllocs, microEnd] at *
          simp only [SsaProg.eval_cnot]
          have hce : cur ≤ M := by
            have : microEnd cur rest ≤ M := hM; have := microEnd_eq_add rest cur; omega
          let wA := microSlotWire inW cur₀ a (microSlotBound hrel ha hce)
          let wB := microSlotWire inW cur₀ b (microSlotBound hrel hb hce)
          obtain ⟨hcO, hpO, hsO⟩ := hEv _ _
            (clean_ge_update_lt _ (microSlotWire_val_lt inW cur₀ hin_lt hrel hb _) hcl)
            (by rw [length_setBoolAt]; exact hlen)
            (microSlotWire_update_setBoolAt inW hin_inj hin_lt hrel hce (by omega) hst hb
              (β wB + β wA) (xor (getBoolAt st b) (getBoolAt st a))
              (by rw [hst b hb, hst a ha, b2z_xor]))
          refine ⟨hcO, fun w hw hni ↦ (hpO w hw hni).trans ?_, hsO⟩
          exact Function.update_of_ne (wire_ne_microSlotWire_of_lt_not_in inW cur₀ hw hni b _) _ _
      | aW a b =>
          intro top cur hrel hv hM
          obtain ⟨ha, hb, hab, hvR⟩ := microValid_aW hv
          have hrel' : nIn + (cur + 1) = cur₀ + (top + 1) ∧ nIn ≤ top + 1 :=
            ⟨by obtain ⟨_, _⟩ := hrel; omega, by obtain ⟨_, _⟩ := hrel; omega⟩
          have hM' : microEnd (cur + 1) rest ≤ M := hM
          obtain ⟨hCnt, hEv⟩ := ih (top + 1) (cur + 1) hrel' hvR hM'
          refine ⟨by
              dsimp only [ssaMicroRun, microAllocs]
              rw [SsaProg.countAnd_andClean, hCnt],
            fun β st hcl hlen hst ↦ ?_⟩
          dsimp only [ssaMicroRun, evalMicroList, microAllocs, microEnd] at *
          simp only [SsaProg.eval_andClean]
          have hcur : cur < M := by
            have := microEnd_eq_add rest (cur + 1); omega
          have hce : cur ≤ M := Nat.le_of_lt hcur
          let wA := microSlotWire inW cur₀ a (microSlotBound hrel ha hce)
          let wB := microSlotWire inW cur₀ b (microSlotBound hrel hb hce)
          let anc : Wire M := ⟨cur, hcur⟩
          have hanc0 : β anc = 0 := hcl anc le_rfl
          set β₁ := Function.update β anc (β anc + β wA * β wB)
          set st₁ := setBoolAt st top (getBoolAt st a && getBoolAt st b)
          have hcl₁ : ∀ w : Wire M, cur + 1 ≤ w.val → β₁ w = 0 := fun w hw ↦ by
            dsimp only [β₁]
            rw [Function.update_of_ne (wire_ne_of_gt (by dsimp [anc]; omega))]
            exact hcl w (by omega)
          have hce' : cur + 1 ≤ M := by omega
          have hst₁ : ∀ (s : ℕ) (hs : s < top + 1),
              β₁ (microSlotWire inW cur₀ s (microSlotBound hrel' hs hce')) =
                b2z (getBoolAt st₁ s) := fun s hs ↦ by
            dsimp only [β₁, st₁]
            rw [getBoolAt_setBoolAt st top s (by omega)]
            by_cases hstop : s = top
            · subst hstop
              have hmw : microSlotWire inW cur₀ s (microSlotBound hrel' hs hce') = anc := by
                rw [microSlotWire_ge_in inW cur₀ s (by obtain ⟨_, _⟩ := hrel; omega)]
                exact Fin.ext (by obtain ⟨_, _⟩ := hrel; dsimp [anc]; omega)
              rw [hmw, Function.update_self, hanc0, zero_add, itePos rfl,
                hst a ha, hst b hb, b2z_and]
            · have hs_lt : s < top := by omega
              have hne_anc : microSlotWire inW cur₀ s (microSlotBound hrel' hs hce') ≠ anc :=
                wire_ne_of_lt (microSlotWire_val_lt inW cur₀ hin_lt hrel hs_lt (microSlotBound hrel'
                  hs hce'))
              rw [Function.update_of_ne hne_anc, iteNeg hstop, hst s hs_lt]
          obtain ⟨hcO, hpO, hsO⟩ := hEv β₁ st₁ hcl₁ (by rw [length_setBoolAt]; omega) hst₁
          refine ⟨hcO, fun w hw hni ↦ ?_, fun s hs ↦ hsO s (by omega)⟩
          rw [hpO w hw hni]; dsimp only [β₁]
          exact Function.update_of_ne
            (wire_ne_of_lt (by obtain ⟨_, _⟩ := hrel; dsimp [anc]; omega)) _ _
/-- Helper `ssaMicro` for compact `165`-wire Slot-3 state preparation. -/
def ssaMicro {M nIn : ℕ} (inW : Fin nIn → Wire M) (hin_inj : Function.Injective inW)
    (cur endCur nAlloc : ℕ) (hin_lt : ∀ i, (inW i).val < cur) (ops : List MicroStep) (hMeta :
    microValid nIn ops = true ∧ microAllocs ops = nAlloc ∧ cur + nAlloc = endCur)
    (hEnd : endCur ≤ M) : SsaProg M cur endCur :=
  have hEq : microEnd cur ops = endCur := by
    rw [microEnd_eq_add, hMeta.2.1, hMeta.2.2]
  ssaCastEnd hEq (ssaMicroRun inW hin_inj cur hin_lt nIn cur ⟨Nat.add_comm nIn cur, le_rfl⟩ ops
    hMeta.1 (by rw [hEq]; exact hEnd))
theorem bitsVal_testBit_eq {W : ℕ} (g : Fin W → ZMod 2) (i : Fin W) :
    (bitsVal g).testBit i.val = decide (g i = 1) := by
  let h : Fin W → ZMod 2 := fun j ↦ if (bitsVal g).testBit j.val then 1 else 0
  have hh : bitsVal h = bitsVal g :=
    bitsVal_eq_of_testBit h (bitsVal g) (bitsVal_lt_two_pow g) (fun _ ↦ rfl)
  have hb_succ : ∀ {q : ℕ} (f : Fin (q + 1) → ZMod 2),
      bitsVal f = (f 0).val + 2 * bitsVal (fun j ↦ f j.succ) := fun {q} f ↦ by
    rw [bitsVal, Fin.sum_univ_succ]
    simp only [Fin.val_zero, _root_.pow_zero, mul_one, bitsVal, Finset.mul_sum]
    congr 1; refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [Fin.val_succ, pow_succ]; ring
  have h_inj : ∀ {q : ℕ} {f₁ f₂ : Fin q → ZMod 2}, bitsVal f₁ = bitsVal f₂ → f₁ = f₂ := by
    intro q; induction q with
    | zero => intro f₁ f₂ _; funext j; exact Fin.elim0 j
    | succ q ih =>
        intro f₁ f₂ heq
        rw [hb_succ f₁, hb_succ f₂] at heq
        have h0 : f₁ 0 = f₂ 0 := by
          rcases bit_cases (f₁ 0) with a0 | a1 <;> rcases bit_cases (f₂ 0) with b0 | b1
          · rw [a0, b0]
          · rw [a0, b1] at heq; change 0 + _ = 1 + _ at heq; omega
          · rw [a1, b0] at heq; change 1 + _ = 0 + _ at heq; omega
          · rw [a1, b1]
        have htail := ih (f₁ := fun j ↦ f₁ j.succ) (f₂ := fun j ↦
          f₂ j.succ) (by rw [h0] at heq; omega)
        funext j; cases j using Fin.cases with
        | zero => exact h0
        | succ k => exact congrFun htail k
  have hi : g i = if (bitsVal g).testBit i.val then 1 else 0 := congrFun (h_inj hh.symm) i
  rw [hi]
  cases (bitsVal g).testBit i.val <;> decide
/-- Helper `allBelowFrom` for compact `165`-wire Slot-3 state preparation. -/
def allBelowFrom (pred : ℕ → Bool) : ℕ → ℕ → Bool
  | _, 0 => true
  | off, rem + 1 => Bool.casesOn (pred off) false (allBelowFrom pred (off + 1) rem)
theorem allBelowFrom_iff (pred : ℕ → Bool) :
    ∀ (off rem : ℕ), allBelowFrom pred off rem = true ↔ ∀ k < rem, pred (off + k) = true
  | _, 0 => by simp [allBelowFrom]
  | off, rem + 1 => by
      dsimp only [allBelowFrom]
      cases hp : pred off
      · simp only [Bool.false_eq_true, false_iff, not_forall]
        exact ⟨0, by omega, by simpa using hp⟩
      · dsimp only
        rw [allBelowFrom_iff pred (off + 1) rem]
        constructor
        · intro hrest k hk
          rcases k with _ | k'
          · simpa using hp
          · have := hrest k' (by omega)
            simpa [Nat.add_assoc, Nat.add_comm 1 k'] using this
        · intro h k' hk'
          have := h (k' + 1) (by omega)
          simpa [Nat.add_assoc, Nat.add_comm 1 k'] using this
/-- Helper `allBelow` for compact `165`-wire Slot-3 state preparation. -/
def allBelow (bound : ℕ) (pred : ℕ → Bool) : Bool := allBelowFrom pred 0 bound
theorem allBelow_iff (bound : ℕ) (pred : ℕ → Bool) :
    allBelow bound pred = true ↔ ∀ m < bound, pred m = true := by
  simpa [allBelow] using allBelowFrom_iff pred 0 bound
theorem ssaMicro_spec {M nIn : ℕ} (inW : Fin nIn → Wire M) (hin_inj : Function.Injective inW)
    (cur endCur nAlloc : ℕ) (hin_lt : ∀ i, (inW i).val < cur)
    (ops : List MicroStep)
    (hMeta : microValid nIn ops = true ∧ microAllocs ops = nAlloc ∧ cur + nAlloc = endCur)
    (hEnd : endCur ≤ M) :
    (ssaMicro inW hin_inj cur endCur nAlloc hin_lt ops hMeta hEnd).countAnd = nAlloc ∧
    (∀ β : BitAssignment M,
      (∀ w : Wire M, cur ≤ w.val → β w = 0) →
      let m := bitsVal (fun i ↦ β (inW i))
      let stOut := evalMicroList nIn ops (initBoolList nIn (nIn + nAlloc) m)
      (∀ w : Wire M, endCur ≤ w.val →
        (ssaMicro inW hin_inj cur endCur nAlloc hin_lt ops hMeta hEnd).eval β w = 0) ∧
      ((∀ i < nIn, getBoolAt stOut i = m.testBit i) →
        ∀ w : Wire M, w.val < cur →
          (ssaMicro inW hin_inj cur endCur nAlloc hin_lt ops hMeta hEnd).eval β w = β w) ∧
      (∀ (s : ℕ) (hlo : nIn ≤ s) (hhi : s < nIn + nAlloc),
        (ssaMicro inW hin_inj cur endCur nAlloc hin_lt ops hMeta hEnd).eval β
          ⟨cur + (s - nIn), by have := hMeta.2.2; omega⟩ = b2z (getBoolAt stOut s))) := by
  have hEq : microEnd cur ops = endCur := by
    rw [microEnd_eq_add, hMeta.2.1, hMeta.2.2]
  obtain ⟨hCnt, hEv⟩ := ssaMicroRun_spec inW hin_inj cur hin_lt ops nIn cur
    ⟨Nat.add_comm nIn cur, le_rfl⟩ hMeta.1 (by rw [hEq]; exact hEnd)
  dsimp only [ssaMicro]
  refine ⟨(ssaCastEnd_countAnd _ _).trans (hCnt.trans hMeta.2.1), fun β hcl ↦ ?_⟩
  let m := bitsVal (fun i ↦ β (inW i))
  let st₀ := initBoolList nIn (nIn + nAlloc) m
  have hst₀ : ∀ (s : ℕ) (hs : s < nIn),
      β (microSlotWire inW cur s (fun hle ↦ absurd hle (Nat.not_le_of_lt hs))) =
        b2z (getBoolAt st₀ s) := fun s hs ↦ by
    rw [microSlotWire_lt_in inW cur s hs]
    dsimp [st₀, initBoolList]
    rw [getBoolAt_mkBoolList nIn m 0 (nIn + nAlloc) s (by omega)]
    simp only [Nat.zero_add, hs, decide_true, Bool.true_and]
    have htb := bitsVal_testBit_eq (fun i ↦ β (inW i)) ⟨s, hs⟩
    dsimp at htb
    rw [htb, ← zmod2_eq_b2z]
  obtain ⟨hcO, hpO, hsO⟩ := hEv β st₀ hcl
    (by dsimp [st₀, initBoolList]; rw [length_mkBoolList]; have := hMeta.2.1; omega) hst₀
  simp only [ssaCastEnd_eval]
  refine ⟨fun w hw ↦ hcO w (by rw [hEq]; exact hw), fun hrest w hw ↦ ?_, fun s hlo hhi ↦ ?_⟩
  · by_cases hmem : ∃ i, w = inW i
    · obtain ⟨i, rfl⟩ := hmem
      have ho := hsO i.val (by omega)
      rw [microSlotWire_lt_in inW cur i.val i.isLt] at ho
      rw [ho, hrest i.val i.isLt, bitsVal_testBit_eq (fun j ↦ β (inW j)) i, ← zmod2_eq_b2z]
    · exact hpO w hw (fun i h ↦ hmem ⟨i, h⟩)
  · have ho := hsO s (by have := hMeta.2.1; omega)
    rwa [microSlotWire_ge_in inW cur s hlo] at ho
attribute [local irreducible] ssaMicro
theorem nat_beq_iff : ∀ (a b : ℕ), Nat.beq a b = true ↔ a = b
  | 0, 0 => by simp [Nat.beq]
  | 0, _ + 1 => by simp [Nat.beq]
  | _ + 1, 0 => by simp [Nat.beq]
  | a + 1, b + 1 => by simp [Nat.beq, nat_beq_iff a b]
theorem nat_ble_iff : ∀ (a b : ℕ), Nat.ble a b = true ↔ a ≤ b
  | 0, _ => by simp [Nat.ble]
  | _ + 1, 0 => by simp [Nat.ble]
  | a + 1, b + 1 => by simp [Nat.ble, nat_ble_iff a b]
/-- Helper `pow2Small` for compact `165`-wire Slot-3 state preparation. -/
def pow2Small (d : ℕ) : ℕ := 2 ^ d
theorem pow2Small_eq (d : ℕ) : pow2Small d = 2 ^ d := rfl
theorem decide_iff {p q : Prop} {dp : Decidable p} [dq : Decidable q] (h : p ↔ q) : @decide p
    dp = @decide q dq := decide_eq_decide.mpr h
theorem decide_iff_both {p q : Prop} {dp : Decidable p} {dq : Decidable q} (h : p ↔ q) :
    @decide p dp = @decide q dq := decide_eq_decide.mpr h
theorem testBit_two_pow (k i : ℕ) : (2 ^ k).testBit i = decide (i = k) := by
  rw [Nat.testBit_two_pow]; exact decide_iff_both eq_comm
theorem two_pow_sub_one_succ (n : ℕ) : 2 ^ (n + 1) - 1 = 1 + 2 * (2 ^ n - 1) := by
  have hpos : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  rw [pow_succ']; omega
theorem testBit_allMask : ∀ (n r : ℕ), (Nat.sub (Nat.pow 2 n) 1).testBit r = decide (r < n)
  | 0, r => by change (0 : ℕ).testBit r = decide (r < 0); simp
  | n + 1, 0 => by
      change (2 ^ (n + 1) - 1).testBit 0 = decide (0 < n + 1)
      rw [two_pow_sub_one_succ n]; simp [Nat.testBit_zero]
  | n + 1, r + 1 => by
      change (2 ^ (n + 1) - 1).testBit (r + 1) = decide (r + 1 < n + 1)
      rw [two_pow_sub_one_succ n, Nat.testBit_succ]
      have hdiv : (1 + 2 * (2 ^ n - 1)) / 2 = 2 ^ n - 1 := by omega
      rw [hdiv]
      have ih := testBit_allMask n r
      change (2 ^ n - 1).testBit r = decide (r < n) at ih
      rw [ih]; simp
/-- Helper `allMaskFast` for compact `165`-wire Slot-3 state preparation. -/
def allMaskFast : ℕ → ℕ → ℕ
  | 0, acc => Nat.sub acc 1
  | k + 1, acc => allMaskFast k (Nat.add acc acc)
theorem allMaskFast_eq : ∀ (k acc : ℕ), allMaskFast k acc = acc * 2 ^ k - 1
  | 0, acc => by simp [allMaskFast]
  | k + 1, acc => by
      dsimp only [allMaskFast]
      change allMaskFast k (acc + acc) = acc * 2 ^ (k + 1) - 1
      rw [allMaskFast_eq k (acc + acc), pow_succ']
      have h : (acc + acc) * 2 ^ k = acc * (2 * 2 ^ k) := by ring
      rw [h]
theorem testBit_allMaskFast {nRows r : ℕ} (hr : r < nRows) :
    (allMaskFast nRows 1).testBit r = true := by
  rw [allMaskFast_eq, one_mul]
  have h := testBit_allMask nRows r
  change (2 ^ nRows - 1).testBit r = decide (r < nRows) at h
  rw [h, decide_eq_true hr]
/-- Helper `hasMaskBit` for compact `165`-wire Slot-3 state preparation. -/
def hasMaskBit (x mask : ℕ) : Bool := Nat.beq (Nat.land x mask) mask
theorem hasMaskBit_pow2 (x i : ℕ) : hasMaskBit x (2 ^ i) = x.testBit i := by
  dsimp only [hasMaskBit]
  have hland : ∀ k : ℕ, (Nat.land x (2 ^ i)).testBit k =
      (if x.testBit i then (2 ^ i).testBit k else (0 : ℕ).testBit k) := fun k ↦ by
    change (x &&& 2 ^ i).testBit k = _
    rw [Nat.testBit_and, testBit_two_pow]
    by_cases hki : k = i
    · subst hki; cases x.testBit k <;> simp
    · simp [hki]
  by_cases hxi : x.testBit i = true
  · rw [hxi]
    apply (nat_beq_iff _ _).mpr
    apply Nat.eq_of_testBit_eq
    intro k; rw [hland k, hxi]; simp
  · have hxf : x.testBit i = false := Bool.eq_false_iff.mpr hxi
    rw [hxf]
    apply Bool.eq_false_iff.mpr
    intro heq
    have h0 : Nat.land x (2 ^ i) = 0 := by
      apply Nat.eq_of_testBit_eq; intro k; rw [hland k, hxf]; simp
    have hpow := ((nat_beq_iff _ _).mp heq).symm.trans h0
    have hpos : 0 < 2 ^ i := Nat.two_pow_pos i
    omega
/-- Helper `fastBitSmall` for compact `165`-wire Slot-3 state preparation. -/
def fastBitSmall (x i : ℕ) : Bool := hasMaskBit x (pow2Small i)
theorem fastBitSmall_eq_testBit (x i : ℕ) : fastBitSmall x i = x.testBit i := by
  dsimp only [fastBitSmall]; rw [pow2Small_eq, hasMaskBit_pow2]
/-- Helper `packPredLoop` for compact `165`-wire Slot-3 state preparation. -/
def packPredLoop (f : ℕ → Bool) : ℕ → ℕ → ℕ → ℕ → ℕ
  | 0, _, _, acc => acc
  | k + 1, r, p, acc =>
      packPredLoop f k (Nat.add r 1) (Nat.add p p)
        (Bool.casesOn (f r) acc (Nat.lor acc p))
theorem testBit_packPredLoop (f : ℕ → Bool) :
    ∀ (k r acc i : ℕ),
      (packPredLoop f k r (2 ^ r) acc).testBit i =
        (acc.testBit i || (decide (r ≤ i ∧ i < r + k) && f i))
  | 0, r, acc, i => by
      dsimp only [packPredLoop]
      rw [decide_eq_false (by omega : ¬ (r ≤ i ∧ i < r + 0))]; simp
  | k + 1, r, acc, i => by
      dsimp only [packPredLoop]
      have hr1 : Nat.add r 1 = r + 1 := rfl
      have hp1 : Nat.add (2 ^ r) (2 ^ r) = 2 ^ (r + 1) := by
        change (2 ^ r) + (2 ^ r) = 2 ^ (r + 1); rw [pow_succ]; omega
      rw [hr1, hp1, testBit_packPredLoop f k (r + 1) _ i]
      cases hfr : f r <;> dsimp only
      · by_cases hir : i = r
        · subst hir
          rw [decide_eq_false (by omega : ¬ (i + 1 ≤ i ∧ i < i + 1 + k)), hfr]; simp
        · rw [decide_iff (by omega : (r + 1 ≤ i ∧ i < r + 1 + k) ↔ (r ≤ i ∧ i < r + (k + 1)))]
      · change ((acc ||| 2 ^ r).testBit i || _) = _
        rw [Nat.testBit_or, testBit_two_pow]
        by_cases hir : i = r
        · subst hir
          rw [decide_eq_true (by omega : i ≤ i ∧ i < i + (k + 1)), hfr]; simp
        · rw [decide_eq_false hir,
            decide_iff (by omega : (r + 1 ≤ i ∧ i < r + 1 + k) ↔ (r ≤ i ∧ i < r + (k + 1)))]
          simp
theorem testBit_packPredLoop_zero (f : ℕ → Bool) (k i : ℕ) (hi : i < k) :
    (packPredLoop f k 0 1 0).testBit i = f i := by
  have h := testBit_packPredLoop f k 0 0 i
  dsimp only [Nat.pow_zero] at h
  rw [h, decide_eq_true ⟨Nat.zero_le i, by omega⟩]
  simp
/-- Helper `colMaskFast` for compact `165`-wire Slot-3 state preparation. -/
def colMaskFast (nRows bit : ℕ) : ℕ := packPredLoop (fun r ↦ fastBitSmall r bit) nRows 0 1 0
theorem testBit_colMaskFast (nRows bit r : ℕ) :
    (colMaskFast nRows bit).testBit r = (decide (r < nRows) && r.testBit bit) := by
  dsimp only [colMaskFast]
  rw [show (1 : ℕ) = 2 ^ 0 from rfl,
    testBit_packPredLoop (fun x ↦ fastBitSmall x bit) nRows 0 0 r, fastBitSmall_eq_testBit,
    decide_iff (by omega : (0 ≤ r ∧ r < 0 + nRows) ↔ r < nRows)]
  simp
/-- Helper `PTree` for compact `165`-wire Slot-3 state preparation. -/
inductive PTree (α : Type) where
  | leaf : α → PTree α
  | node : PTree α → PTree α → PTree α
/-- Helper `PTree` for compact `165`-wire Slot-3 state preparation. -/
def PTree.hasDepth {α : Type} : ℕ → PTree α → Prop
  | 0, .leaf _ => True
  | 0, .node _ _ => False
  | _ + 1, .leaf _ => False
  | d + 1, .node l r => PTree.hasDepth d l ∧ PTree.hasDepth d r
/-- Helper `PTree` for compact `165`-wire Slot-3 state preparation. -/
def PTree.withVal {α β : Type} (t : PTree α) (f : PTree α → β) : β :=
  PTree.casesOn t (fun v ↦ f (.leaf v)) (fun l r ↦ f (.node l r))
theorem PTree.withVal_eq {α β : Type} (t : PTree α) (f : PTree α → β) :
    PTree.withVal t f = f t := by
  cases t <;> rfl
/-- Helper `forceNat` for compact `165`-wire Slot-3 state preparation. -/
def forceNat {α : Type} (v : ℕ) (k : ℕ → α) : α :=
  Nat.casesOn v (k 0) (fun p ↦ k (Nat.succ p))
theorem forceNat_eq {α : Type} (v : ℕ) (k : ℕ → α) : forceNat v k = k v := by
  cases v <;> rfl
/-- Helper `pconst` for compact `165`-wire Slot-3 state preparation. -/
def pconst {α : Type} (dflt : α) : ℕ → PTree α
  | 0 => .leaf dflt
  | d + 1 => .node (pconst dflt d) (pconst dflt d)
/-- Helper `pget` for compact `165`-wire Slot-3 state preparation. -/
def pget {α : Type} (dflt : α) : ℕ → PTree α → ℕ → α
  | 0, t, _ => PTree.casesOn t (fun v ↦ v) (fun _ _ ↦ dflt)
  | d + 1, t, k =>
      PTree.casesOn t (fun v ↦ v) fun l r ↦
        let half := pow2Small d
        Bool.casesOn (Nat.ble half k)
          (pget dflt d l k)
          (pget dflt d r (Nat.sub k half))
/-- Helper `pset` for compact `165`-wire Slot-3 state preparation. -/
def pset {α : Type} : ℕ → PTree α → ℕ → α → PTree α
  | 0, _, _, v => .leaf v
  | d + 1, t, k, v =>
      PTree.casesOn t (fun x ↦ .leaf x) fun l r ↦
        let half := pow2Small d
        Bool.casesOn (Nat.ble half k)
          (PTree.withVal (pset d l k v) fun l' ↦ .node l' r)
          (PTree.withVal (pset d r (Nat.sub k half) v) fun r' ↦ .node l r')
/-- Helper `psetNat` for compact `165`-wire Slot-3 state preparation. -/
def psetNat (d : ℕ) (t : PTree ℕ) (k v : ℕ) : PTree ℕ := forceNat v (pset d t k)
theorem psetNat_eq (d : ℕ) (t : PTree ℕ) (k v : ℕ) : psetNat d t k v = pset d t k v :=
  forceNat_eq v (pset d t k)
theorem pconst_hasDepth {α : Type} (dflt : α) : ∀ d : ℕ, PTree.hasDepth d (pconst dflt d)
  | 0 => trivial
  | d + 1 => ⟨pconst_hasDepth dflt d, pconst_hasDepth dflt d⟩
theorem pget_pconst {α : Type} (dflt : α) : ∀ (d i : ℕ),
    i < 2 ^ d → pget dflt d (pconst dflt d) i = dflt
  | 0, _, _ => rfl
  | d + 1, i, hi => by
      dsimp only [pget, pconst]
      rw [pow2Small_eq d]
      change Bool.casesOn (Nat.ble (2 ^ d) i)
        (pget dflt d (pconst dflt d) i) (pget dflt d (pconst dflt d) (i - 2 ^ d)) = dflt
      by_cases hle : 2 ^ d ≤ i
      · rw [(nat_ble_iff (2 ^ d) i).mpr hle]
        exact pget_pconst dflt d (i - 2 ^ d) (by rw [pow_succ'] at hi; omega)
      · have hbf : Nat.ble (2 ^ d) i = false :=
          Bool.eq_false_iff.mpr (fun ht ↦ hle ((nat_ble_iff (2 ^ d) i).mp ht))
        rw [hbf]
        exact pget_pconst dflt d i (by omega)
theorem pset_hasDepth {α : Type} : ∀ (d : ℕ) (t : PTree α), PTree.hasDepth d t →
    ∀ k < 2 ^ d, ∀ v, PTree.hasDepth d (pset d t k v)
  | 0, _, _, _, _, _ => trivial
  | _ + 1, .leaf _, ht, _, _, _ => False.elim ht
  | d + 1, .node l r, ⟨hl, hr⟩, k, hk, v => by
      dsimp only [pset]
      rw [pow2Small_eq d, PTree.withVal_eq, PTree.withVal_eq]
      change PTree.hasDepth (d + 1) (Bool.casesOn (Nat.ble (2 ^ d) k)
        (.node (pset d l k v) r) (.node l (pset d r (k - 2 ^ d) v)))
      by_cases hle : 2 ^ d ≤ k
      · rw [(nat_ble_iff (2 ^ d) k).mpr hle]
        exact ⟨hl, pset_hasDepth d r hr (k - 2 ^ d) (by rw [pow_succ'] at hk; omega) v⟩
      · have hbf : Nat.ble (2 ^ d) k = false :=
          Bool.eq_false_iff.mpr (fun ht ↦ hle ((nat_ble_iff (2 ^ d) k).mp ht))
        rw [hbf]
        exact ⟨pset_hasDepth d l hl k (by omega) v, hr⟩
theorem pget_pset {α : Type} (dflt : α) : ∀ (d : ℕ) (t : PTree α), PTree.hasDepth d t →
    ∀ k < 2 ^ d, ∀ i < 2 ^ d, ∀ v,
      pget dflt d (pset d t k v) i = if i = k then v else pget dflt d t i
  | 0, .node _ _, ht, _, _, _, _, _ => False.elim ht
  | 0, .leaf _, _, k, hk, i, hi, _ => by
      obtain rfl : k = 0 := by omega
      obtain rfl : i = 0 := by omega
      rfl
  | _ + 1, .leaf _, ht, _, _, _, _, _ => False.elim ht
  | d + 1, .node l r, ⟨hl, hr⟩, k, hk, i, hi, v => by
      dsimp only [pset, pget]
      rw [pow2Small_eq d, PTree.withVal_eq, PTree.withVal_eq]
      rw [pow_succ'] at hk hi
      have hb_eq : ∀ n, Nat.ble (2 ^ d) n = decide (2 ^ d ≤ n) := fun n ↦
        Bool.eq_iff_iff.mpr ((nat_ble_iff _ _).trans (iff_of_eq decide_eq_true_eq.symm))
      rw [hb_eq k, hb_eq i]
      by_cases hkle : 2 ^ d ≤ k <;> by_cases hile : 2 ^ d ≤ i <;>
        simp only [hkle, hile, decide_true, decide_false, Nat.sub_eq]
      · rw [pget_pset dflt d r hr (k - 2 ^ d) (by omega) (i - 2 ^ d) (by omega) v]
        simp [show (i - 2 ^ d = k - 2 ^ d) ↔ (i = k) by omega]
      · exact (iteNeg (by omega)).symm
      · exact (iteNeg (by omega)).symm
      · exact pget_pset dflt d l hl k (by omega) i (by omega) v
/-- Helper `initColsFast` for compact `165`-wire Slot-3 state preparation. -/
def initColsFast (nRows : ℕ) : ℕ → PTree ℕ → PTree ℕ
  | 0, t => t
  | i + 1, t => PTree.withVal (psetNat 8 t i (colMaskFast nRows i)) (initColsFast nRows i)
theorem initColsFast_spec (nRows : ℕ) :
    ∀ (m : ℕ), m ≤ 256 → ∀ (t : PTree ℕ), PTree.hasDepth 8 t →
      PTree.hasDepth 8 (initColsFast nRows m t) ∧
        ∀ w < 256, pget 0 8 (initColsFast nRows m t) w =
          if w < m then colMaskFast nRows w else pget 0 8 t w
  | 0, _, t, ht => ⟨ht, fun _ _ ↦ by simp [initColsFast]⟩
  | i + 1, hm, t, ht => by
      dsimp only [initColsFast]; rw [psetNat_eq, PTree.withVal_eq]
      have h256 : (2 ^ 8 : ℕ) = 256 := by decide
      have ht' : PTree.hasDepth 8 (pset 8 t i (colMaskFast nRows i)) :=
        pset_hasDepth 8 t ht i (by rw [h256]; omega) _
      obtain ⟨hP, hG⟩ := initColsFast_spec nRows i (by omega) _ ht'
      refine ⟨hP, fun w hw ↦ ?_⟩
      rw [hG w hw]
      by_cases hwi : w < i
      · have hwi1 : w < i + 1 := by omega
        simp [hwi, hwi1]
      · simp only [hwi, ↓reduceIte]
        rw [pget_pset 0 8 t ht i (by rw [h256]; omega) w (by rw [h256]; exact hw)]
        by_cases heq : w = i
        · subst heq; simp
        · have hnot : ¬ (w < i + 1) := by omega
          simp [heq, hnot]
/-- Helper `evalSIMD` for compact `165`-wire Slot-3 state preparation. -/
def evalSIMD (allMask : ℕ) : ℕ → List MicroStep → PTree ℕ → PTree ℕ
  | _, [], t => t
  | top, .nW a :: rest, t =>
      PTree.withVal (psetNat 8 t a (Nat.xor allMask (pget 0 8 t a))) (evalSIMD allMask top rest)
  | top, .cW a b :: rest, t =>
      PTree.withVal (psetNat 8 t b (Nat.xor (pget 0 8 t b) (pget 0 8 t a))) (evalSIMD allMask top
        rest)
  | top, .aW a b :: rest, t =>
      PTree.withVal (psetNat 8 t top (Nat.land (pget 0 8 t a) (pget 0 8 t b)))
        (evalSIMD allMask (top + 1) rest)
private theorem evalSIMD_step_agree {r idx : ℕ} {t : PTree ℕ} {st : List Bool}
    (hPt : PTree.hasDepth 8 t) (hlen : st.length ≤ 256) (hidx : idx < st.length)
    (hagree : ∀ i < st.length, (pget 0 8 t i).testBit r = getBoolAt st i)
    (v : ℕ) (bv : Bool) (hv : v.testBit r = bv) :
    ∀ j < (setBoolAt st idx bv).length,
      (pget 0 8 (pset 8 t idx v) j).testBit r = getBoolAt (setBoolAt st idx bv) j := by
  have h256 : (2 ^ 8 : ℕ) = 256 := by decide
  intro j hj
  rw [length_setBoolAt] at hj
  rw [pget_pset 0 8 t hPt idx (by rw [h256]; omega) j (by rw [h256]; omega),
    getBoolAt_setBoolAt st idx j hidx]
  by_cases hji : j = idx
  · subst hji; simp [hv]
  · simp [hji, hagree j hj]

theorem evalSIMD_agree (nRows r : ℕ) (hr : r < nRows) (ops : List MicroStep) : ∀ (top : ℕ)
    (t : PTree ℕ) (st : List Bool), PTree.hasDepth 8 t → microValid top ops = true → top +
    microAllocs ops = st.length → st.length ≤ 256 →
    (∀ i < st.length, (pget 0 8 t i).testBit r = getBoolAt st i) → ∀ i < st.length, (pget 0 8
    (evalSIMD (Nat.sub (Nat.pow 2 nRows) 1) top ops t) i).testBit r = getBoolAt
    (evalMicroList top ops st) i := by
  have h256 : (2 ^ 8 : ℕ) = 256 := by decide
  induction ops with
  | nil => intro _ _ _ _ _ _ _ hagree i hi; exact hagree i hi
  | cons op rest ih =>
      intro top t st hPt hv halloc hlen hagree i hi
      cases op with
      | nW a =>
          obtain ⟨ha, hvR⟩ := microValid_nW hv
          dsimp only [microAllocs] at halloc
          dsimp only [evalSIMD, evalMicroList]; rw [psetNat_eq, PTree.withVal_eq]
          refine ih top _ _ (pset_hasDepth 8 t hPt a (by rw [h256]; omega) _) hvR
            (by rw [length_setBoolAt]; exact halloc) (by rw [length_setBoolAt]; exact hlen)
            (evalSIMD_step_agree hPt hlen (by omega) hagree _ _ ?_) i
              (by rw [length_setBoolAt]; exact hi)
          change ((Nat.sub (Nat.pow 2 nRows) 1) ^^^ pget 0 8 t a).testBit r =
            Bool.not (getBoolAt st a)
          rw [Nat.testBit_xor, testBit_allMask, decide_eq_true hr, hagree a (by omega)]
          cases getBoolAt st a <;> rfl
      | cW a b =>
          obtain ⟨ha, hb, _, hvR⟩ := microValid_cW hv
          dsimp only [microAllocs] at halloc
          dsimp only [evalSIMD, evalMicroList]; rw [psetNat_eq, PTree.withVal_eq]
          refine ih top _ _ (pset_hasDepth 8 t hPt b (by rw [h256]; omega) _) hvR
            (by rw [length_setBoolAt]; exact halloc) (by rw [length_setBoolAt]; exact hlen)
            (evalSIMD_step_agree hPt hlen (by omega) hagree _ _ ?_) i
              (by rw [length_setBoolAt]; exact hi)
          change (pget 0 8 t b ^^^ pget 0 8 t a).testBit r = xor (getBoolAt st b) (getBoolAt st a)
          rw [Nat.testBit_xor, hagree b (by omega), hagree a (by omega)]
      | aW a b =>
          obtain ⟨ha, hb, _, hvR⟩ := microValid_aW hv
          dsimp only [microAllocs] at halloc
          dsimp only [evalSIMD, evalMicroList]; rw [psetNat_eq, PTree.withVal_eq]
          refine ih (top + 1) _ _ (pset_hasDepth 8 t hPt top (by rw [h256]; omega) _) hvR
            (by rw [length_setBoolAt]; omega) (by rw [length_setBoolAt]; exact hlen)
            (evalSIMD_step_agree hPt hlen (by omega) hagree _ _ ?_) i
              (by rw [length_setBoolAt]; exact hi)
          change (pget 0 8 t a &&& pget 0 8 t b).testBit r = (getBoolAt st a && getBoolAt st b)
          rw [Nat.testBit_and, hagree a (by omega), hagree b (by omega)]
/-- Helper `simdRun` for compact `165`-wire Slot-3 state preparation. -/
def simdRun (nRows nIn : ℕ) (ops : List MicroStep) : PTree ℕ :=
  evalSIMD (allMaskFast nRows 1) nIn ops (initColsFast nRows nIn (pconst 0 8))
theorem simdRun_testBit_eq (nRows nIn len r s : ℕ) (ops : List MicroStep) (hlen : len ≤ 256)
    (hr : r < nRows) (hs : s < len) (hv : microValid nIn ops = true)
    (halloc : nIn + microAllocs ops = len) : (pget 0 8 (simdRun nRows nIn ops) s).testBit r =
    getBoolAt (evalMicroList nIn ops (initBoolList nIn len r)) s := by
  dsimp only [simdRun]
  have hmask : allMaskFast nRows 1 = Nat.sub (Nat.pow 2 nRows) 1 := by
    rw [allMaskFast_eq, one_mul]; rfl
  rw [hmask]
  have h256 : (2 ^ 8 : ℕ) = 256 := by decide
  obtain ⟨hP0, hG0⟩ := initColsFast_spec nRows nIn (by omega) (pconst 0 8) (pconst_hasDepth 0 8)
  have hlen_st : (initBoolList nIn len r).length = len := length_mkBoolList nIn r 0 len
  refine evalSIMD_agree nRows r hr ops nIn _ (initBoolList nIn len r)
    hP0 hv (halloc.trans hlen_st.symm) (by rw [hlen_st]; exact hlen)
    (fun i hi ↦ ?_) s (by rw [hlen_st]; exact hs)
  rw [hlen_st] at hi
  rw [hG0 i (by omega)]
  dsimp only [initBoolList]
  rw [getBoolAt_mkBoolList nIn r 0 len i hi]
  simp only [zero_add]
  by_cases hin : i < nIn
  · simp only [hin, ↓reduceIte]; rw [testBit_colMaskFast, decide_eq_true hr]; simp
  · simp only [hin, ↓reduceIte]; rw [pget_pconst 0 8 i (by rw [h256]; omega)]; simp
/-- Helper `getNatAt` for compact `165`-wire Slot-3 state preparation. -/
def getNatAt : List ℕ → ℕ → ℕ
  | [], _ => 0
  | x :: _, 0 => x
  | _ :: xs, k + 1 => getNatAt xs k
/-- Helper `kcTable49168List` for compact `165`-wire Slot-3 state preparation. -/
def kcTable49168List : List ℕ := [
  82, 292, 319, 532, 286, 259, 259, 102, 360, 127, 12, 318, 771, 340, 771, 575,
  44, 552, 566, 774, 518, 114, 1631, 3768, 5659, 7396, 9006, 10494, 11877, 13160, 14360, 15483,
  16536, 17525, 18456, 19333, 20162, 20946, 21688, 22392, 23063, 23699, 24306, 24883, 25436, 25963,
    26468, 26951,
  27414, 27856, 28284, 28693, 29088, 29466, 29831, 30182, 30520, 30848, 31164, 31469, 31764, 32050,
    32326, 32592,
  32851, 33103, 33346, 33583, 33811, 34034, 34250, 34461, 34665, 34864, 35057, 35245, 35428, 35607,
    35780, 35950,
  36115, 36275, 36433, 36587, 36737, 36883, 37026, 37165, 37302, 37435, 37565, 37693, 37818, 37939,
    38059, 38176,
  38291, 38403, 38512, 38620, 38726, 38829, 38930, 39030, 39127, 39223, 39317, 39408, 39499, 39588,
    39675, 39760,
  39844, 39927, 40008, 40088, 40166, 40243, 40318, 40392, 40466, 40538, 40608, 40678, 40747, 40814,
    40880, 40946,
  41010, 41072, 41135, 41197, 41256, 41316, 41376, 41433, 41490, 41546, 41600, 41655, 41709, 41762,
    41814, 41865,
  41916, 41966, 42016, 42065, 42112, 42160, 42206, 42252, 42298, 42343, 42387, 42431, 42474, 42517,
    42559, 42600,
  42640, 42682, 42722, 42760, 42800, 42839, 42877, 42915, 42952, 42989, 43024, 43061, 43096, 43132,
    43166, 43200,
  43235, 43268, 43301, 43334, 43366, 43398, 43430, 43462, 43493, 43523, 43554, 43584, 43613, 43643,
    43672, 43701,
  43728, 43757, 43785, 43813, 43840, 43867, 43894, 43920, 43947, 43973, 43998, 44024, 44049, 44074,
    44099, 44123,
  44147, 44171, 44195, 44219, 44242, 44264, 44288, 44311, 44333, 44355, 44378, 44400, 44421, 44443,
    44465, 44485,
  44506, 44527, 44547, 44568, 44588, 44608, 44627, 44647, 44667, 44686, 44704, 44723, 44743, 44762,
    44780, 44799,
  44817, 44835, 44853, 44870, 44888, 44904, 44923, 44939, 44956, 44974, 44991, 45007, 45024, 45040,
    45056, 45336
]
/-- Right-fold CNOT fan-in onto target slot `t` for `MicroStep` lists. -/
def cnotTo (t : ℕ) : List ℕ → List MicroStep → List MicroStep
  | [], k => k
  | u :: us, k => .cW u t :: cnotTo t us k

/-- Reverse-order CNOT uncompute onto target slot `t` for `MicroStep` lists. -/
def cnotRevTo (t : ℕ) : List ℕ → List MicroStep → List MicroStep
  | [], k => k
  | u :: us, k => cnotRevTo t us (.cW u t :: k)

/-- Conjugated `TempAnd` (`aW a b`) wrapped in CNOT basis fan-in/uncompute on `b` and `a`. -/
def conjAndStep (a b : ℕ) (xs ys : List ℕ) (k : List MicroStep) : List MicroStep :=
  cnotTo b xs (cnotTo a ys (.aW a b :: cnotRevTo a ys (cnotRevTo b xs k)))

/-- Palindromic `MicroStep` wrapper `pre ++ mid ++ pre.reverse ++ post`. -/
def palWrap : List MicroStep → List MicroStep → List MicroStep → List MicroStep
  | [], mid, post => mid ++ post
  | op :: ops, mid, post => op :: palWrap ops mid (op :: post)

/-- Prepend literal `MicroStep` slice `xs` onto continuation `k`. -/
def rawSteps : List MicroStep → List MicroStep → List MicroStep
  | [], k => k
  | x :: xs, k => x :: rawSteps xs k

/-- Helper `s1Kc68Ops` for compact `165`-wire Slot-3 state preparation. -/
def s1Kc68Ops : List MicroStep :=
  rawSteps [.aW 5 6, .aW 5 7, .aW 6 7, .aW 8 7, .aW 1 0, .aW 2 0, .aW 2 1, .aW 14 0,
    .aW 3 0, .aW 3 1, .aW 17 0, .aW 3 2, .aW 19 0, .aW 19 1, .aW 21 0, .aW 4 0, .aW 4 1,
    .aW 24 0, .aW 4 2, .aW 26 0, .aW 26 1, .aW 28 0, .aW 4 3, .aW 30 0, .aW 30 1, .aW 32 0,
    .aW 30 2, .aW 34 0, .aW 34 1, .aW 36 0] <|
  conjAndStep 18 5 [8, 9, 11, 32, 34, 36] [19, 22, 4, 32, 33, 36, 37, 6, 7, 10] <|
  conjAndStep 13 5 [8, 9, 11, 27, 28, 29, 32, 34, 36]
    [14, 15, 3, 18, 19, 20, 21, 25, 26, 27, 28, 30, 32, 34, 36, 6, 8, 10, 11] <|
  conjAndStep 30 8 [7, 11, 36] [32, 34, 35, 37, 11] <|
  conjAndStep 2 5 [9, 11, 1, 12, 14, 3, 16, 19, 22, 23, 24, 28, 34, 36]
    [15, 16, 18, 19, 20, 22, 4, 24, 28, 29, 30, 31, 32, 33, 6, 10, 11] <|
  conjAndStep 0 8 [11, 12, 15, 3, 18, 19, 20, 4, 23, 29, 32]
    [12, 13, 14, 15, 3, 16, 17, 18, 19, 20, 22, 23, 24, 25, 26, 27, 29, 30, 32, 34, 7, 11] <|
  conjAndStep 3 9 [10, 17, 21, 31, 33, 34, 35, 37]
    [17, 19, 21, 24, 26, 28, 31, 32, 33, 34, 10] <|
  conjAndStep 1 5 [6, 7, 9, 14, 16, 17, 18, 20, 24, 25, 29, 33, 34, 35, 36, 37]
    [14, 3, 17, 20, 22, 24, 29, 30, 32, 37, 6, 8, 10, 11] <|
  conjAndStep 12 8 [9, 0, 13, 15, 17, 21, 4, 23, 25, 27, 34, 36, 37]
    [2, 3, 19, 22, 4, 26, 27, 32, 34, 35, 37, 7] <|
  conjAndStep 2 9 [11, 4, 28, 30, 36, 37]
    [15, 18, 19, 20, 21, 22, 4, 23, 24, 28, 29, 30, 32, 33, 34, 35, 37, 11] <|
  conjAndStep 0 5 [6, 7, 11, 14, 16, 18, 19, 23, 24, 26, 27, 29, 31, 32, 35, 36, 37]
    [1, 12, 2, 15, 3, 16, 20, 21, 23, 25, 27, 28, 30, 31, 33, 35, 36, 37, 6, 10] <|
  conjAndStep 1 8 [7, 10, 12, 13, 15, 3, 17, 18, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 32, 35]
    [13, 17, 20, 21, 4, 23, 26, 28, 29, 32, 35, 36, 37, 7, 9, 10, 11] <|
  conjAndStep 2 9 [10, 11, 15, 16, 17, 18, 19, 20, 22, 4, 27, 28, 30, 35, 36]
    [3, 16, 20, 4, 25, 27, 30, 32, 35, 10] <|
  conjAndStep 1 5 [6, 7, 10, 11, 0, 14, 15, 3, 16, 17, 22, 24, 25, 26, 30, 31, 36]
    [12, 3, 17, 19, 20, 21, 4, 25, 30, 32, 34, 36, 6, 7, 9, 11] <|
  conjAndStep 12 8 [7, 9, 11, 13, 14, 16, 22, 25, 26, 29, 30, 31, 32, 35, 36]
    [14, 15, 16, 19, 22, 23, 25, 27, 28, 36, 7, 10, 11] <|
  conjAndStep 2 9 [14, 15, 3, 18, 20, 21, 4, 24, 28, 29, 34, 35, 37]
    [14, 3, 17, 18, 20, 21, 23, 26, 30, 31, 32, 33, 34, 10, 11] <|
  conjAndStep 1 5 [6, 8, 10, 2, 14, 17, 19, 22, 4, 26, 28, 29, 30, 31, 33, 34, 36]
    [2, 14, 15, 19, 21, 23, 26, 28, 29, 30, 31, 32, 33, 36, 6, 7, 9, 11] <|
  conjAndStep 0 8 [7, 10, 11, 12, 13, 17, 20, 22, 23, 26, 33, 34, 35, 36, 37]
    [13, 14, 15, 3, 16, 18, 20, 4, 23, 24, 27, 32, 33, 34, 35, 37, 7, 9, 10] <|
  conjAndStep 13 9 [11, 15, 16, 17, 20, 22, 24, 26, 29, 31, 34, 37]
    [15, 3, 16, 17, 18, 20, 4, 26, 28, 29, 31, 32, 33, 35, 37, 10] <|
  conjAndStep 12 5 [9, 0, 16, 17, 18, 19, 21, 22, 4, 24, 25, 28, 31, 34, 35, 37]
    [2, 16, 17, 19, 20, 21, 22, 4, 24, 28, 30, 31, 33, 35, 6, 8, 9, 11] <|
  conjAndStep 1 8 [7, 9, 13, 14, 15, 3, 17, 18, 20, 22, 24, 32, 35, 36, 37]
    [2, 3, 16, 17, 18, 19, 20, 21, 22, 4, 23, 24, 25, 27, 29, 30, 31, 37, 7, 9] <|
  conjAndStep 2 9 [10, 11, 14, 3, 16, 22, 23, 26, 29, 31, 33, 35]
    [14, 17, 21, 22, 27, 29, 31, 32, 34, 35, 37, 10, 11] <|
  conjAndStep 1 5 [6, 8, 15, 3, 16, 17, 19, 21, 4, 23, 25, 26, 27, 28, 29, 30, 31, 35, 36, 37]
    [12, 2, 13, 15, 3, 17, 18, 19, 20, 24, 25, 28, 29, 30, 31, 32, 35, 6, 8, 11] <|
  conjAndStep 0 8 [7, 10, 11, 12, 2, 13, 3, 16, 21, 4, 23, 27, 29, 30, 31, 32, 33, 34, 35, 36]
    [12, 2, 13, 14, 17, 18, 24, 27, 28, 29, 31, 32, 33, 36, 37, 9] <|
  conjAndStep 14 10 [3, 16, 17, 4, 23, 24, 25, 26, 28, 30, 35, 36]
    [16, 17, 18, 19, 20, 22, 28, 31, 33, 37, 11] <|
  conjAndStep 0 5 [6, 7, 9, 10, 2, 14, 3, 16, 17, 19, 22, 25, 29, 32, 35]
    [1, 12, 14, 15, 3, 17, 18, 20, 21, 22, 24, 26, 27, 28, 30, 31, 32, 35, 36, 6, 8, 9] <|
  conjAndStep 1 7 [10, 13, 15, 3, 20, 21, 22, 4, 23, 24, 25, 26, 29, 31, 32, 33, 34, 37]
    [13, 15, 16, 17, 18, 19, 21, 22, 23, 24, 25, 26, 27, 31, 34, 35, 9, 10, 11] <|
  conjAndStep 3 10 [11, 15, 16, 17, 18, 20, 21, 24, 27, 29, 30, 31, 33, 37]
    [17, 18, 21, 23, 27, 28, 29, 30, 33, 34, 36, 37, 11] <|
  conjAndStep 1 5 [7, 9, 0, 1, 12, 13, 15, 3, 19, 20, 22, 4, 26, 30, 31, 32, 33, 34]
    [2, 14, 22, 24, 26, 28, 29, 30, 33, 34, 36, 37, 6, 7, 10] <|
  conjAndStep 17 5 [6, 10, 11, 0, 1, 12, 13, 15, 3, 16, 18, 19, 4, 26, 29, 31, 34]
    [19, 21, 4, 32, 34, 36, 6, 7, 10] <|
  conjAndStep 1 8 [7, 11, 14, 3, 21, 4, 28, 30, 36]
    [2, 3, 16, 18, 20, 21, 4, 24, 26, 29, 31, 34, 35, 7] <|
  conjAndStep 0 5 [6, 8, 7, 9, 10, 11, 1, 14, 3, 19, 24, 28, 29, 33, 35, 37]
    [12, 2, 13, 14, 15, 3, 19, 20, 4, 24, 30, 34, 35, 37, 6, 8, 10, 11] <|
  conjAndStep 24 8 [7, 9, 10, 19, 4, 34] [26, 28, 30, 32, 34, 36, 10, 11] <|
  conjAndStep 2 8 [5, 12, 13, 14, 16, 18, 22, 27, 30, 31, 36, 37]
    [14, 15, 3, 18, 20, 21, 22, 4, 24, 26, 27, 28, 29, 30, 31, 32, 5, 7] <|
  conjAndStep 0 5 [9, 13, 14, 15, 17, 20, 21, 23, 26, 27, 28, 30, 31, 32, 34, 36, 37]
    [1, 12, 2, 14, 16, 20, 21, 22, 25, 27, 29, 30, 31, 34, 6, 7, 9, 10] <|
  conjAndStep 1 7 [9, 11, 12, 14, 15, 3, 17, 20, 21, 22, 4, 23, 26, 27, 28, 30, 33]
    [12, 15, 16, 17, 18, 19, 21, 22, 4, 23, 26, 30, 31, 32, 34, 35, 36, 37, 9] <|
  conjAndStep 2 10 [14, 15, 17, 20, 21, 4, 23, 24, 25, 26, 29, 30, 32, 33, 34]
    [14, 15, 17, 19, 20, 21, 22, 23, 25, 27, 29, 30, 31, 33, 35, 11] <|
  conjAndStep 0 5 [8, 9, 10, 11, 2, 13, 20, 21, 4, 23, 26, 27, 29, 32, 33, 34, 37]
    [1, 2, 13, 16, 18, 4, 23, 26, 28, 29, 31, 35, 8, 9, 10] <|
  conjAndStep 1 9 [10, 11, 13, 23, 25, 30, 32, 33, 35, 36, 37]
    [12, 13, 15, 3, 17, 18, 19, 20, 21, 22, 4, 25, 26, 27, 28, 29, 31, 32, 34, 10] <|
  cnotTo 75 [70, 74, 5, 6, 8, 9, 10, 11, 1, 12, 2, 14, 15, 17, 18, 19, 4, 25, 26, 27, 28,
    29, 31, 33, 34, 35, 36] <|
  cnotTo 64 [62, 63, 5, 6, 10, 1, 12, 2, 13, 15, 16, 17, 19, 20, 21, 23, 25, 26, 27, 31, 34,
    36, 37] <|
  rawSteps [.nW 64] <|
  cnotTo 61 [59, 60, 6, 8, 9, 11, 0, 1, 12, 13, 14, 3, 16, 22, 4, 27, 31, 32, 33, 37] <|
  cnotTo 58 [56, 57, 7, 10, 0, 12, 2, 14, 15, 16, 19, 21, 22, 24, 26, 28, 30, 33, 35, 37] <|
  rawSteps [.nW 58] <|
  cnotTo 55 [53, 54, 5, 6, 7, 9, 10, 0, 2, 15, 3, 18, 19, 22, 4, 23, 24, 27, 28, 29, 32, 34,
    35] <|
  rawSteps [.nW 55] <|
  cnotTo 52 [50, 51, 6, 8, 7, 9, 0, 1, 13, 14, 15, 3, 19, 20, 4, 23, 24, 32] <|
  cnotTo 49 [47, 48, 5, 6, 9, 12, 13, 3, 17, 18, 20, 23, 25, 26, 27, 28, 30, 33, 34, 37] <|
  rawSteps [.nW 49] <|
  cnotTo 73 [70, 71, 72, 9, 10, 11, 13, 19, 20, 22, 4, 24, 27, 28, 30, 34] <|
  cnotTo 46 [44, 45, 6, 8, 7, 10, 11, 0, 1, 12, 2, 13, 14, 3, 19, 22, 25, 28, 31, 33, 34, 35] <|
  cnotTo 43 [41, 42, 9, 12, 15, 3, 17, 18, 20, 21, 22, 25, 29, 30, 32, 33, 36] <|
  cnotTo 69 [65, 68, 6, 8, 7, 9, 11, 1, 3, 16, 18, 19, 22, 26, 30, 31, 32, 33, 34, 36] <|
  cnotTo 67 [65, 66, 6, 8, 9, 1, 3, 16, 18, 19, 20, 21, 22, 23, 25, 26, 27, 29, 30, 32, 34] <|
  cnotTo 40 [39, 8, 27, 28, 29, 30, 35, 37] <| cnotTo 38 [7, 32, 34, 36] <|
  rawSteps [.cW 40 67, .cW 67 69, .cW 40 43, .cW 69 46, .cW 38 46] <|
  cnotTo 49 [46, 43, 67] <| rawSteps [.cW 73 55] <| cnotTo 58 [52, 49, 46] <|
  rawSteps [.cW 61 64] <| cnotTo 11 [5, 8, 9] <| rawSteps [.cW 6 10, .cW 7 10] <|
  []
/-- Helper `s1Kc68OutSlots` for compact `165`-wire Slot-3 state preparation. -/
def s1Kc68OutSlots : List ℕ := [
  75, 64, 61, 58, 55, 52, 49, 73, 46, 43, 69, 67, 40, 38, 11, 10
]
/-- Helper `s2Unpack64Ops` for compact `165`-wire Slot-3 state preparation. -/
def s2Unpack64Ops : List MicroStep :=
  palWrap [.nW 21, .nW 20] [.aW 21 20] <| palWrap [.nW 19] [.aW 22 19] <|
  palWrap [.nW 18] [.aW 23 18] <| palWrap [.nW 17] [.aW 24 17] <|
  palWrap [.nW 16] [.aW 25 16] <| palWrap [.nW 15] [.aW 26 15] <|
  palWrap [.cW 21 22, .cW 23 22, .cW 24 22, .cW 25 22, .cW 26 22, .nW 22, .cW 1 0] [.aW 22 0] <|
  rawSteps [.cW 1 28] <|
  palWrap [.cW 21 22, .cW 23 22, .cW 24 22, .cW 25 22, .cW 26 22, .nW 22, .cW 2 1] [.aW 22 1] <|
  rawSteps [.cW 2 29] <|
  palWrap [.cW 21 22, .cW 23 22, .cW 24 22, .cW 25 22, .cW 26 22, .nW 22, .cW 3 2] [.aW 22 2] <|
  rawSteps [.cW 3 30] <|
  palWrap [.cW 21 22, .cW 23 22, .cW 24 22, .cW 25 22, .cW 26 22, .nW 22, .cW 4 3] [.aW 22 3] <|
  rawSteps [.cW 4 31] <|
  palWrap [.cW 21 22, .cW 23 22, .cW 24 22, .cW 25 22, .cW 26 22, .nW 22, .cW 5 4] [.aW 22 4] <|
  rawSteps [.cW 5 32] <|
  palWrap [.cW 21 22, .cW 23 22, .cW 24 22, .cW 25 22, .cW 26 22, .nW 22, .cW 6 5] [.aW 22 5] <|
  rawSteps [.cW 6 33, .aW 21 0] <| palWrap [.nW 22] [.aW 22 28] <|
  palWrap [.cW 24 22, .cW 26 22, .cW 29 0] [.aW 22 0] <| rawSteps [.cW 29 36] <|
  palWrap [.nW 23] [.aW 23 36] <| palWrap [.cW 24 22, .cW 26 22, .cW 30 28] [.aW 22 28] <|
  rawSteps [.cW 30 38] <| palWrap [.nW 24] [.aW 24 38] <|
  palWrap [.cW 24 22, .cW 26 22, .cW 31 29] [.aW 22 29] <| rawSteps [.cW 31 40] <|
  palWrap [.nW 24] [.aW 24 40] <| conjAndStep 24 0 [] [25] <| rawSteps [.cW 41 42] <|
  palWrap [.cW 24 22, .cW 26 22, .cW 32 30] [.aW 22 30] <| rawSteps [.cW 32 43] <|
  palWrap [.nW 24] [.aW 24 43] <| conjAndStep 24 28 [] [26] <| rawSteps [.cW 44 45] <|
  palWrap [.cW 24 22, .cW 26 22, .cW 33 31] [.aW 22 31] <| rawSteps [.cW 33 46] <|
  conjAndStep 24 36 [46] [] <| rawSteps [.cW 46 47, .aW 21 7] <|
  palWrap [.cW 21 22, .cW 23 22, .cW 24 22, .cW 25 22, .cW 26 22, .nW 22, .cW 8 6] [.aW 22 6] <|
  rawSteps [.cW 8 49] <| palWrap [.nW 22] [.aW 22 49] <|
  palWrap [.cW 21 22, .cW 23 22, .cW 24 22, .cW 25 22, .cW 26 22, .nW 22, .cW 9 7] [.aW 22 7] <|
  rawSteps [.cW 9 51] <| palWrap [.cW 24 22, .cW 26 22, .cW 51 5] [.aW 22 5] <|
  rawSteps [.cW 51 52] <| palWrap [.nW 23] [.aW 23 52] <|
  palWrap [.cW 21 22, .cW 23 22, .cW 24 22, .cW 25 22, .cW 26 22, .nW 22,
    .cW 10 8] [.aW 22 8] <|
  rawSteps [.cW 10 54] <|
  palWrap [.cW 24 22, .cW 26 22, .cW 32 5, .cW 33 5, .cW 54 5] [.aW 22 5] <|
  rawSteps [.cW 54 55] <| palWrap [.nW 24] [.aW 24 55] <|
  palWrap [.cW 21 22, .cW 23 22, .cW 24 22, .cW 25 22, .cW 26 22, .nW 22,
    .cW 13 11] [.aW 22 11] <|
  rawSteps [.cW 13 57] <| palWrap [.cW 24 22, .cW 26 22, .cW 57 51] [.aW 22 51] <|
  rawSteps [.cW 57 58, .cW 24 22, .cW 26 22] <| cnotTo 1 [4, 31, 32] <| rawSteps [.aW 22 1] <|
  cnotTo 1 [4, 31, 32] <| rawSteps [.cW 26 22, .cW 24 22] <| cnotTo 59 [4, 31, 32] <|
  conjAndStep 24 59 [58] [] <| rawSteps [.cW 58 60, .aW 21 11] <|
  palWrap [.cW 21 23, .nW 23, .cW 9 51, .cW 7 51] [.aW 23 51] <|
  palWrap [.cW 25 23, .cW 4 3, .cW 5 3, .cW 31 3, .cW 32 3] [.aW 23 3] <|
  rawSteps [.cW 61 63, .cW 62 63, .aW 21 12] <|
  palWrap [.cW 21 23, .nW 23, .cW 10 54, .cW 8 54] [.aW 23 54] <|
  palWrap [.cW 25 23, .cW 5 4, .cW 6 4, .cW 32 4, .cW 33 4] [.aW 23 4] <|
  conjAndStep 25 2 [] [26] <| cnotTo 67 [64, 65, 66] <| rawSteps [.aW 21 14] <|
  palWrap [.cW 21 22, .cW 23 22, .cW 24 22, .cW 25 22, .cW 26 22, .nW 22,
    .cW 15 12] [.aW 22 12] <|
  rawSteps [.cW 15 69] <| palWrap [.nW 22] [.aW 22 69] <|
  palWrap [.cW 21 22, .nW 22, .cW 19 16] [.aW 22 16] <| cnotTo 71 [19, 22, 23] <|
  palWrap [.cW 21 22, .cW 23 22, .cW 24 22, .cW 25 22, .cW 26 22, .nW 22,
    .cW 13 10] [.aW 22 10] <|
  rawSteps [.cW 13 72] <|
  palWrap [.cW 21 22, .cW 23 22, .cW 24 22, .cW 25 22, .cW 26 22, .nW 22, .cW 7 4] [.aW 22 4] <|
  rawSteps [.cW 7 73] <| conjAndStep 24 73 [72] [] <| rawSteps [.cW 72 74] <|
  conjAndStep 22 74 [] [26] <| rawSteps [.cW 71 75, .aW 21 16] <|
  palWrap [.cW 21 23, .nW 23, .cW 13 72, .cW 10 72] [.aW 23 72] <| rawSteps [.cW 76 77] <|
  palWrap [.cW 21 22, .cW 23 22, .cW 24 22, .cW 25 22, .cW 26 22, .nW 22,
    .cW 17 14] [.aW 22 14] <|
  rawSteps [.cW 17 78] <|
  palWrap [.cW 24 22, .cW 26 22, .cW 11 10, .cW 54 10, .cW 57 10, .cW 72 10,
    .cW 78 10] [.aW 22 10] <|
  rawSteps [.cW 78 79] <| palWrap [.nW 24] [.aW 24 79] <|
  palWrap [.cW 21 23, .nW 23, .cW 18 69, .cW 15 69, .cW 12 69] [.aW 23 69] <|
  cnotTo 81 [18, 23, 24] <|
  palWrap [.cW 25 23, .cW 7 5, .cW 9 5, .cW 32 5, .cW 33 5, .cW 51 5, .cW 73 5] [.aW 23 5] <|
  rawSteps [.cW 81 82] <| palWrap [.cW 21 23, .nW 23, .cW 17 78, .cW 14 78] [.aW 23 78] <|
  palWrap [.cW 25 23, .cW 10 8, .cW 54 8, .cW 57 8, .cW 72 8] [.aW 23 8] <|
  conjAndStep 25 2 [3, 4, 5, 30, 31, 32] [] <| rawSteps [.cW 20 85, .nW 85] <|
  cnotTo 85 [21, 22, 83, 84] <|
  []
/-- Helper `s2MtSlotsFlat` for compact `165`-wire Slot-3 state preparation. -/
def s2MtSlotsFlat : List ℕ := [
  34, 35, 37, 39, 42, 45, 47, 48, 50, 53, 56, 63, 67, 60, 68, 70, 77, 80, 82, 75, 85
]
/-- Helper `s2AxisZbad7Ops` for compact `165`-wire Slot-3 state preparation. -/
def s2AxisZbad7Ops : List MicroStep := [
  .nW 0, .nW 1, .aW 0 1, .nW 1, .nW 0, .nW 2, .aW 8 2, .nW 2, .nW 3, .aW 9 3,
  .nW 3, .nW 4, .aW 10 4, .nW 4, .nW 5, .aW 11 5, .nW 5, .nW 6, .aW 12 6, .nW 6,
  .aW 13 7
]
/-- Helper `s2ValidComb6Ops` for compact `165`-wire Slot-3 state preparation. -/
def s2ValidComb6Ops : List MicroStep := [
  .nW 1, .nW 2, .nW 3, .aW 1 2, .aW 7 3, .nW 3, .nW 2, .nW 1, .nW 0, .nW 8,
  .nW 4, .nW 5, .nW 6, .aW 0 8, .aW 4 5, .aW 10 6, .aW 9 11, .nW 6, .nW 5, .nW 4,
  .nW 0
]
/- ## Generic `SsaProg` Clean-Copy Bridge (`0-T` Scratch Uncomputation) -/

/-- `RawSsa` predicate asserting no instruction touches wires in `[kLo, cur₀)`. -/
def RawSsaAvoidsMid {M : ℕ} (kLo cur₀ : ℕ) : RawSsa M → Prop
  | .done => True
  | .x q rest => ¬ (kLo ≤ q.val ∧ q.val < cur₀) ∧ RawSsaAvoidsMid kLo cur₀ rest
  | .cnot c t _ rest =>
      ¬ (kLo ≤ c.val ∧ c.val < cur₀) ∧ ¬ (kLo ≤ t.val ∧ t.val < cur₀) ∧
        RawSsaAvoidsMid kLo cur₀ rest
  | .skipZero rest => RawSsaAvoidsMid kLo cur₀ rest
  | .andClean anc c₁ c₂ _ _ _ rest =>
      ¬ (kLo ≤ anc.val ∧ anc.val < cur₀) ∧ ¬ (kLo ≤ c₁.val ∧ c₁.val < cur₀) ∧
        ¬ (kLo ≤ c₂.val ∧ c₂.val < cur₀) ∧ RawSsaAvoidsMid kLo cur₀ rest

theorem rawSsa_eval_mid {M : ℕ} (kLo cur₀ : ℕ) :
    ∀ (r : RawSsa M), RawSsaAvoidsMid kLo cur₀ r →
      ∀ (β : BitAssignment M) (w : Wire M), kLo ≤ w.val ∧ w.val < cur₀ → r.eval β w = β w
  | .done, _, _, _, _ => rfl
  | .x q rest, ⟨hq, hr⟩, β, w, hw => by
      dsimp only [RawSsa.eval]
      rw [rawSsa_eval_mid kLo cur₀ rest hr _ w hw,
        Function.update_of_ne (fun heq : w = q ↦ hq (heq ▸ hw))]
  | .cnot _ t _ rest, ⟨_, ht, hr⟩, β, w, hw => by
      dsimp only [RawSsa.eval]
      rw [rawSsa_eval_mid kLo cur₀ rest hr _ w hw,
        Function.update_of_ne (fun heq : w = t ↦ ht (heq ▸ hw))]
  | .skipZero rest, hr, β, w, hw => rawSsa_eval_mid kLo cur₀ rest hr β w hw
  | .andClean anc _ _ _ _ _ rest, ⟨ha, _, _, hr⟩, β, w, hw => by
      dsimp only [RawSsa.eval]
      rw [rawSsa_eval_mid kLo cur₀ rest hr _ w hw,
        Function.update_of_ne (fun heq : w = anc ↦ ha (heq ▸ hw))]

theorem microSlotWire_not_mid {M nIn : ℕ} (inW : Fin nIn → Wire M) (kLo cur₀ : ℕ)
    (hInLo : ∀ i, (inW i).val < kLo) (s : ℕ) (hb : nIn ≤ s → cur₀ + (s - nIn) < M) :
    ¬ (kLo ≤ (microSlotWire inW cur₀ s hb).val ∧ (microSlotWire inW cur₀ s hb).val < cur₀) := by
  by_cases hs : s < nIn
  · rw [microSlotWire_lt_in inW cur₀ s hs hb]
    have hlt := hInLo ⟨s, hs⟩
    omega
  · rw [microSlotWire_ge_in inW cur₀ s (by omega) hb]
    dsimp
    omega

theorem ssaMicroRun_avoidsMid {M nIn : ℕ} (inW : Fin nIn → Wire M)
    (hinj : Function.Injective inW) (kLo cur₀ : ℕ)
    (hin_lt : ∀ i, (inW i).val < cur₀) (hInLo : ∀ i, (inW i).val < kLo) :
    ∀ (ops : List MicroStep) (top cur : ℕ)
      (hrel : nIn + cur = cur₀ + top ∧ nIn ≤ top)
      (hv : microValid top ops = true) (hM : microEnd cur ops ≤ M),
      RawSsaAvoidsMid kLo cur₀ (ssaMicroRun inW hinj cur₀ hin_lt top cur hrel ops hv hM).raw
  | [], _, _, _, _, _ => trivial
  | op :: rest, top, cur, hrel, hv, hM => by
      cases op with
      | nW a =>
          obtain ⟨_, hvR⟩ := microValid_nW hv
          have ih := ssaMicroRun_avoidsMid inW hinj kLo cur₀ hin_lt hInLo rest top cur hrel hvR hM
          exact ⟨microSlotWire_not_mid inW kLo cur₀ hInLo a _, ih⟩
      | cW a b =>
          obtain ⟨_, _, _, hvR⟩ := microValid_cW hv
          have ih := ssaMicroRun_avoidsMid inW hinj kLo cur₀ hin_lt hInLo rest top cur hrel hvR hM
          exact ⟨microSlotWire_not_mid inW kLo cur₀ hInLo a _,
            microSlotWire_not_mid inW kLo cur₀ hInLo b _, ih⟩
      | aW a b =>
          obtain ⟨_, _, _, hvR⟩ := microValid_aW hv
          have hrel' : nIn + (cur + 1) = cur₀ + (top + 1) ∧ nIn ≤ top + 1 :=
            ⟨by obtain ⟨_, _⟩ := hrel; omega, by obtain ⟨_, _⟩ := hrel; omega⟩
          have ih := ssaMicroRun_avoidsMid inW hinj kLo cur₀ hin_lt hInLo rest (top + 1) (cur + 1)
            hrel' hvR hM
          refine ⟨by obtain ⟨_, _⟩ := hrel; dsimp; omega,
            microSlotWire_not_mid inW kLo cur₀ hInLo a _,
            microSlotWire_not_mid inW kLo cur₀ hInLo b _, ih⟩

theorem ssaCastEnd_raw {M cur e1 e2 : ℕ} (h : e1 = e2) (p : SsaProg M cur e1) :
    (ssaCastEnd h p).raw = p.raw := by
  cases h; rfl

theorem ssaMicro_avoidsMid {M nIn : ℕ} (inW : Fin nIn → Wire M)
    (hinj : Function.Injective inW) (kLo cur₀ endCur nAlloc : ℕ)
    (hin_lt : ∀ i, (inW i).val < cur₀) (hInLo : ∀ i, (inW i).val < kLo) (ops : List MicroStep)
    (hmeta : microValid nIn ops = true ∧ microAllocs ops = nAlloc ∧ cur₀ + nAlloc = endCur)
    (hM : endCur ≤ M) : RawSsaAvoidsMid kLo cur₀
    (ssaMicro inW hinj cur₀ endCur nAlloc hin_lt ops hmeta hM).raw := by
  unfold ssaMicro
  dsimp only
  rw [ssaCastEnd_raw]
  exact ssaMicroRun_avoidsMid inW hinj kLo cur₀ hin_lt hInLo ops nIn cur₀
    ⟨Nat.add_comm nIn cur₀, le_rfl⟩ hmeta.1 _

/-- Converts `RawSsa M` directly to `TempCtx M`. -/
def rawSsaToSharedCtx {M : ℕ} : RawSsa M → TempCtx M
  | .done => .hole
  | .x q rest => .seqPre (.x q) (.seqPost (rawSsaToSharedCtx rest) (.x q))
  | .cnot c t hct rest =>
    .seqPre (.cnot c t hct) (.seqPost (rawSsaToSharedCtx rest) (.cnot c t hct))
  | .skipZero rest => rawSsaToSharedCtx rest
  | .andClean anc c₁ c₂ h₁₂ hc1a hc2a rest =>
      .tempAnd c₁ c₂ anc h₁₂ hc1a hc2a (rawSsaToSharedCtx rest)

private theorem update_add_invol {M : ℕ} (β : BitAssignment M) (q : Wire M) (x : ZMod 2) :
    Function.update (Function.update β q (β q + x)) q
      (Function.update β q (β q + x) q + x) = β := by
  funext w
  by_cases hw : w = q
  · subst hw; simp only [Function.update_self]; exact zmod2_add_cancel_right _ _
  · simp [Function.update_of_ne hw]

private theorem cleanRem_update_lt {M cur : ℕ} {β : BitAssignment M} {q : Wire M} (v : ZMod 2)
    (hq : q.val < cur) (hcur : cur ≤ M) (hβ : cleanRem M (M - cur) β) :
    cleanRem M (M - cur) (Function.update β q v) := fun w hw ↦ by
  rw [Function.update_of_ne (wire_ne_of_gt (by omega))]; exact hβ w hw

theorem rawSsaToSharedCtx_valid_and_bits {M : ℕ} :
    ∀ (p : RawSsa M) {cur endCur : ℕ},
      RawSsa.Wf cur endCur p →
      endCur ≤ M →
      (∀ β : BitAssignment M, cleanRem M (M - cur) β →
        ((rawSsaToSharedCtx p).plug .nil).evalBits β = β) ∧
      ValidCleanRem M (M - cur) ((rawSsaToSharedCtx p).plug .nil)
  | .done, _, _, _, _ => ⟨fun _ _ ↦ rfl, trivial⟩
  | .x q rest, cur, _, ⟨hq, hwf⟩, hEnd => by
      have hcurM : cur ≤ M := le_trans (RawSsa.le_end hwf) hEnd
      obtain ⟨ihBits, ihVal⟩ := rawSsaToSharedCtx_valid_and_bits rest hwf hEnd
      have hPres : ∀ β,
        cleanRem M (M - cur) β → cleanRem M (M - cur) (Function.update β q (β q + 1)) :=
        fun _ ↦ cleanRem_update_lt _ hq hcurM
      refine ⟨fun β hβ ↦ ?_, M - cur, Nat.sub_le M cur, trivial,
        ⟨M - cur, Nat.sub_le M cur, ihVal, trivial, fun β₁ hβ₁ ↦ (ihBits β₁ hβ₁).symm ▸ hβ₁⟩, hPres⟩
      dsimp only [rawSsaToSharedCtx, TempCtx.plug, TempPhaseProg.evalBits, CliffProg.eval]
      rw [ihBits _ (hPres β hβ)]; exact update_add_invol β q 1
  | .cnot c t hct rest, cur, _, ⟨_, ht, hwf⟩, hEnd => by
      have hcurM : cur ≤ M := le_trans (RawSsa.le_end hwf) hEnd
      obtain ⟨ihBits, ihVal⟩ := rawSsaToSharedCtx_valid_and_bits rest hwf hEnd
      have hPres : ∀ β,
        cleanRem M (M - cur) β → cleanRem M (M - cur) (Function.update β t (β t + β c)) :=
        fun _ ↦ cleanRem_update_lt _ ht hcurM
      refine ⟨fun β hβ ↦ ?_, M - cur, Nat.sub_le M cur, trivial,
        ⟨M - cur, Nat.sub_le M cur, ihVal, trivial, fun β₁ hβ₁ ↦ (ihBits β₁ hβ₁).symm ▸ hβ₁⟩, hPres⟩
      dsimp only [rawSsaToSharedCtx, TempCtx.plug, TempPhaseProg.evalBits, CliffProg.eval]
      rw [ihBits _ (hPres β hβ), Function.update_of_ne hct _ _]
      simpa only [Function.update_self] using update_add_invol β t (β c)
  | .skipZero rest, cur, _, ⟨_, hwf⟩, hEnd => by
      obtain ⟨ihBits, ihVal⟩ := rawSsaToSharedCtx_valid_and_bits rest hwf hEnd
      exact ⟨fun β hβ ↦ ihBits β (fun w hw ↦ hβ w (by omega)),
        validCleanRem_mono (by omega) ihVal⟩
  | .andClean anc c₁ c₂ h₁₂ hc1a hc2a rest, cur, _, ⟨hanc_val, _, _, hwf⟩, hEnd => by
      have hcur_lt : cur < M :=
        lt_of_lt_of_le (Nat.lt_succ_self cur) (le_trans (RawSsa.le_end hwf) hEnd)
      obtain ⟨ihBits, ihVal⟩ := rawSsaToSharedCtx_valid_and_bits rest hwf hEnd
      have hPres : ∀ β : BitAssignment M, cleanRem M (M - cur) β →
          cleanRem M (M - (cur + 1)) (Function.update β anc (β anc + β c₁ * β c₂)) :=
            fun β hβ w hw ↦ by
        rw [Function.update_of_ne (wire_ne_of_gt (by omega))]; exact hβ w (by omega)
      refine ⟨fun β hβ ↦ ?_, by omega, by simpa only [hanc_val] using ihVal, fun β₁ hβ₁ ↦ ?_⟩
      · dsimp only [rawSsaToSharedCtx, TempCtx.plug, TempPhaseProg.evalBits]
        rw [ihBits _ (hPres β hβ), Function.update_of_ne hc1a _ _, Function.update_of_ne hc2a _ _]
        simpa only [Function.update_self] using update_add_invol β anc (β c₁ * β c₂)
      · rw [ihBits β₁ (by simpa only [hanc_val] using hβ₁)]; exact ⟨rfl, rfl, rfl⟩

theorem rawSsaToSharedCtx_fwdBits {M : ℕ} :
    ∀ (r : RawSsa M) (β : BitAssignment M),
      (rawSsaToSharedCtx r).fwdBits β = r.eval β
  | .done, _ => rfl
  | .x _ rest, β => by
      simp [rawSsaToSharedCtx, TempCtx.fwdBits, CliffProg.eval, RawSsa.eval,
        rawSsaToSharedCtx_fwdBits rest]
  | .cnot _ _ _ rest, β => by
      simp [rawSsaToSharedCtx, TempCtx.fwdBits, CliffProg.eval, RawSsa.eval,
        rawSsaToSharedCtx_fwdBits rest]
  | .skipZero rest, β => rawSsaToSharedCtx_fwdBits rest β
  | .andClean _ _ _ _ _ _ rest, β => by
      simp[rawSsaToSharedCtx, TempCtx.fwdBits, RawSsa.eval, rawSsaToSharedCtx_fwdBits rest]

theorem rawSsa_toTempCtx_disjoint {M : ℕ} (kLo cur₀ : ℕ) :
    ∀ (r : RawSsa M), RawSsaAvoidsMid kLo cur₀ r →
      (rawSsaToSharedCtx r).DisjointFrom (fun w : Wire M ↦ kLo ≤ w.val ∧ w.val < cur₀)
  | .done, _ => trivial
  | .x _ rest, ⟨hq, hr⟩ => ⟨hq, rawSsa_toTempCtx_disjoint kLo cur₀ rest hr, hq⟩
  | .cnot _ _ _ rest, ⟨hc, ht, hr⟩ =>
      ⟨⟨hc, ht⟩, rawSsa_toTempCtx_disjoint kLo cur₀ rest hr, ⟨hc, ht⟩⟩
  | .skipZero rest, hr => rawSsa_toTempCtx_disjoint kLo cur₀ rest hr
  | .andClean _ _ _ _ _ _ rest, ⟨ha, h1, h2, hr⟩ =>
      ⟨h1, h2, ha, rawSsa_toTempCtx_disjoint kLo cur₀ rest hr⟩

theorem rawSsa_toTempCtx_supportsM {M : ℕ} :
    ∀ (r : RawSsa M), (rawSsaToSharedCtx r).SupportsBelowCtx M
  | .done => trivial
  | .x q rest => ⟨q.isLt, rawSsa_toTempCtx_supportsM rest, q.isLt⟩
  | .cnot c t _ rest => ⟨⟨c.isLt, t.isLt⟩, rawSsa_toTempCtx_supportsM rest, ⟨c.isLt, t.isLt⟩⟩
  | .skipZero rest => rawSsa_toTempCtx_supportsM rest
  | .andClean anc _ _ _ _ _ rest => ⟨anc.isLt, rawSsa_toTempCtx_supportsM rest⟩

theorem rawSsa_plug_z_eq_nil {M : ℕ} (q₀ : Wire M) :
    ∀ (K : TempCtx M),
      (∀ β : BitAssignment M, (K.plug (.z q₀)).evalBits β = (K.plug .nil).evalBits β) ∧
      (∀ rem : ℕ, ValidCleanRem M rem (K.plug .nil) → ValidCleanRem M rem (K.plug (.z q₀)))
  | .hole => ⟨fun _ ↦ rfl, fun _ _ ↦ trivial⟩
  | .seqPre c K => by
      obtain ⟨hB, hV⟩ := rawSsa_plug_z_eq_nil q₀ K
      refine ⟨fun β ↦ hB (c.eval β), fun rem ⟨remMid, hmid, _, hv, hpres⟩ ↦
        ⟨remMid, hmid, trivial, hV remMid hv, hpres⟩⟩
  | .seqPost K c => by
      obtain ⟨hB, hV⟩ := rawSsa_plug_z_eq_nil q₀ K
      refine ⟨fun β ↦ by dsimp [TempCtx.plug, TempPhaseProg.evalBits]; rw [hB β],
        fun rem ⟨remMid, hmid, hv, _, hpres⟩ ↦ ⟨remMid, hmid, hV rem hv, trivial, ?_⟩⟩
      intro β hβ
      rw [hB β]
      exact hpres β hβ
  | .tempAnd c₁ c₂ anc h₁₂ h₁a h₂a K => by
      obtain ⟨hB, hV⟩ := rawSsa_plug_z_eq_nil q₀ K
      refine ⟨fun β ↦ ?_, fun rem ⟨hanc, hv, hpres⟩ ↦ ⟨hanc, hV _ hv, fun β₁ hβ₁ ↦ ?_⟩⟩
      · dsimp only [TempCtx.plug, TempPhaseProg.evalBits]
        rw [hB]
      · rw [hB β₁]
        exact hpres β₁ hβ₁

/-- Pure-Clifford CNOT fanout copying `src ⟨i, _⟩` onto `⟨kLo + i, _⟩` for `i < j`. -/
def copySlotCliff {M : ℕ} (kLo kLen : ℕ) (hk : kLo + kLen ≤ M)
    (src : Fin kLen → Wire M) (hSrcGe : ∀ i : Fin kLen, kLo + kLen ≤ (src i).val) :
    ∀ (j : ℕ), j ≤ kLen → CliffProg M
  | 0, _ => .nil
  | j + 1, hj =>
      let idx : Fin kLen := ⟨j, hj⟩
      let dst : Wire M := ⟨kLo + j, by omega⟩
      have hne : src idx ≠ dst := wire_ne_of_gt (by have := hSrcGe idx; dsimp [dst]; omega)
      .seq (copySlotCliff kLo kLen hk src hSrcGe j (Nat.le_of_succ_le hj)) (.cnot (src idx) dst hne)

theorem copySlotCliff_eval {M : ℕ} (kLo kLen : ℕ) (hk : kLo + kLen ≤ M)
    (src : Fin kLen → Wire M) (hSrcGe : ∀ i : Fin kLen, kLo + kLen ≤ (src i).val) :
    ∀ (j : ℕ) (hj : j ≤ kLen) (γ : BitAssignment M) (w : Wire M),
      (copySlotCliff kLo kLen hk src hSrcGe j hj).eval γ w =
        if h : kLo ≤ w.val ∧ w.val < kLo + j then
          γ w + γ (src ⟨w.val - kLo, by omega⟩)
        else γ w
  | 0, _, γ, w => by
      have hnot : ¬ (kLo ≤ w.val ∧ w.val < kLo + 0) := by omega
      rw [diteNeg hnot]
      rfl
  | j + 1, hj, γ, w => by
      have ih := copySlotCliff_eval kLo kLen hk src hSrcGe j (Nat.le_of_succ_le hj) γ
      let idx : Fin kLen := ⟨j, hj⟩
      let dst : Wire M := ⟨kLo + j, by omega⟩
      have hsrc_out : ¬ (kLo ≤ (src idx).val ∧ (src idx).val < kLo + j) := by
        have := hSrcGe idx; omega
      have hsrc_eq : (copySlotCliff kLo kLen hk src hSrcGe j (Nat.le_of_succ_le hj)).eval γ (src
        idx) =
          γ (src idx) := by
        rw [ih (src idx), diteNeg hsrc_out]
      dsimp only [copySlotCliff, CliffProg.eval]
      by_cases hwd : w = dst
      · subst hwd
        rw [Function.update_self, hsrc_eq, ih dst]
        have hnot_j : ¬ (kLo ≤ dst.val ∧ dst.val < kLo + j) := by dsimp [dst]; omega
        have hin_j1 : kLo ≤ dst.val ∧ dst.val < kLo + (j + 1) := by dsimp [dst]; omega
        rw [diteNeg hnot_j, ditePos hin_j1]
        have hidx : (⟨dst.val - kLo, by omega⟩ : Fin kLen) = idx :=
          Fin.ext (by dsimp [dst, idx]; omega)
        rw [hidx]
      · rw [Function.update_of_ne hwd, ih w]
        have hw_ne_val : w.val ≠ kLo + j := fun hv ↦ hwd (Fin.ext hv)
        by_cases hin : kLo ≤ w.val ∧ w.val < kLo + j
        · have hin' : kLo ≤ w.val ∧ w.val < kLo + (j + 1) := ⟨hin.1, by omega⟩
          rw [ditePos hin, ditePos hin']
        · have hin' : ¬ (kLo ≤ w.val ∧ w.val < kLo + (j + 1)) := by omega
          rw [diteNeg hin, diteNeg hin']

/-- Generic right-register XOR bit-assignment map `(α_left, α_right ⊕ tbl(α_left))` on `k₁ + k₂`
  wires. -/
def xorRightMapGen {k₁ k₂ : ℕ} (tbl : BitAssignment k₁ → BitAssignment k₂)
    (α : BitAssignment (k₁ + k₂)) : BitAssignment (k₁ + k₂) :=
  fun w ↦
    if h : w.val < k₁ then
      α w
    else
      α w + tbl (fun i ↦ α (Fin.castAdd k₂ i)) ⟨w.val - k₁, by omega⟩

theorem xorRightMapGen_invol {k₁ k₂ : ℕ} (tbl : BitAssignment k₁ → BitAssignment k₂)
    (α : BitAssignment (k₁ + k₂)) : xorRightMapGen tbl (xorRightMapGen tbl α) = α := by
  funext w
  dsimp only [xorRightMapGen]
  by_cases hw : w.val < k₁
  · simp [hw]
  · rw [diteNeg hw, diteNeg hw]
    have hleft : (fun i : Fin k₁ ↦
        (if h : (Fin.castAdd k₂ i).val < k₁ then α (Fin.castAdd k₂ i) else
          α (Fin.castAdd k₂ i) + tbl (fun i' ↦ α (Fin.castAdd k₂ i'))
            ⟨(Fin.castAdd k₂ i).val - k₁, by omega⟩)) =
        fun i : Fin k₁ ↦ α (Fin.castAdd k₂ i) := by
      funext i
      exact ditePos i.isLt
    rw [hleft]
    exact zmod2_add_cancel_right _ _

/-- Generic `Equiv.Perm (Fin (2 ^ (k₁ + k₂)))` induced by `xorRightMapGen tbl`. -/
def xorRightPermGen {k₁ k₂ : ℕ} (tbl : BitAssignment k₁ → BitAssignment k₂) :
    Equiv.Perm (Fin (2 ^ (k₁ + k₂))) :=
  let f : Fin (2 ^ (k₁ + k₂)) → Fin (2 ^ (k₁ + k₂)) :=
    fun z ↦ (basisBitsEquiv (k₁ + k₂)).symm (xorRightMapGen tbl (basisBits (k₁ + k₂) z))
  have hbb : ∀ y : Fin (2 ^ (k₁ + k₂)), basisBits (k₁ + k₂) y = basisBitsEquiv (k₁ + k₂) y :=
    fun _ ↦ rfl
  have hf : Function.LeftInverse f f := fun z ↦ by
    dsimp only [f]
    rw[hbb ((basisBitsEquiv (k₁ + k₂)).symm _), (basisBitsEquiv (k₁ + k₂)).apply_symm_apply,
        xorRightMapGen_invol, hbb z, (basisBitsEquiv (k₁ + k₂)).symm_apply_apply]
  { toFun := f, invFun := f, left_inv := hf, right_inv := hf }

/-- Sign-free permutation unitary on `k₁ + k₂` wires XORing `tbl` onto the right `k₂` wires. -/
noncomputable def uXorRightPerm {k₁ k₂ : ℕ} (tbl : BitAssignment k₁ → BitAssignment k₂) :
    Unitary (2 ^ (k₁ + k₂)) := permSignUnitary (xorRightPermGen tbl) (fun _ ↦ false)

theorem uXorRightPerm_mulVec_ket {k₁ k₂ : ℕ} (tbl : BitAssignment k₁ → BitAssignment k₂)
    (α : BitAssignment (k₁ + k₂)) : (uXorRightPerm tbl).1.mulVec (ket α) =
    ((-1 : ℂ) ^ (0 : ZMod 2).val) • ket (xorRightMapGen tbl α) := by
  let k := k₁ + k₂
  let z := (basisBitsEquiv k).symm α
  have hket_z : (Pi.single z (1 : ℂ) : Fin (2 ^ k) → ℂ) = ket α := by
    dsimp only [z, k]; funext x; simp [ket, basisState]
  let rId : QRegister k k := QRegister.block 0 k (Nat.zero_add k).le
  have hrw : ∀ w : Fin k, rId w = w :=
    fun w ↦ Fin.ext (by simp [rId, QRegister.block, Fin.natAddEmb])
  have hex : ∀ x : Fin (2 ^ k), rId.extractIndex x = x := fun x ↦ by
    apply (basisBitsEquiv k).injective
    funext w
    exact (QRegister.basisBits_extractIndex rId x w).trans (congrArg (basisBits k x) (hrw w))
  let M_u : Matrix (Fin (2 ^ k)) (Fin (2 ^ k)) ℂ := (uXorRightPerm tbl).1
  have hid_emb : rId.embedUnitary (uXorRightPerm tbl) = uXorRightPerm tbl := by
    apply Subtype.ext
    change rId.embedMatrix M_u = M_u
    ext i j
    rw [QRegister.embedMatrix_apply]
    have hunit : (rId.basisSplitEquiv i).2 = (rId.basisSplitEquiv j).2 :=
      (rId.basisSplit_environment_eq_iff i j).mpr fun q hq ↦ absurd ⟨q, hrw q⟩ hq
    rw [ite_eq_left hunit, mul_one, hex i, hex j]
  have hrep : ∀ y : Fin (2 ^ k), rId.replaceIndex z y = y := fun y ↦ by
    apply (basisBitsEquiv k).injective
    funext w
    have h := QRegister.basisBits_replaceIndex_apply rId z y w
    rwa [hrw w] at h
  rw [← hket_z, ← hid_emb, uXorRightPerm, embedUnitary_permSignUnitary_mulVec_single]
  simp only [hex, hrep, Bool.false_eq_true, ↓reduceIte, one_smul, ZMod.val_zero, _root_.pow_zero]
  have hbb : ∀ y : Fin (2 ^ k), basisBits k y = basisBitsEquiv k y := fun _ ↦ rfl
  have hz_bb : basisBits k z = α := (hbb z).trans ((basisBitsEquiv k).apply_symm_apply α)
  have hz_bits : basisBits k (xorRightPermGen tbl z) = xorRightMapGen tbl α :=
    (hbb _).trans (((basisBitsEquiv k).apply_symm_apply _).trans (congrArg (xorRightMapGen tbl)
      hz_bb))
  have hz_eq : xorRightPermGen tbl z = (basisBitsEquiv k).symm (xorRightMapGen tbl α) := by
    rw [← hz_bits, hbb]; exact ((basisBitsEquiv k).symm_apply_apply _).symm
  rw [hz_eq]
  dsimp only [k]; funext x; simp [ket, basisState]

theorem ssaPlugCopy_spec {k₁ k₂ mScr : ℕ} (hkPos : 0 < k₁ + k₂ + mScr)
    (p : SsaProg (k₁ + k₂ + mScr) (k₁ + k₂) (k₁ + k₂ + mScr))
    (hAvoid : RawSsaAvoidsMid k₁ (k₁ + k₂) p.raw)
    (src : Fin k₂ → Wire (k₁ + k₂ + mScr))
    (hSrcGe : ∀ j : Fin k₂, k₁ + k₂ ≤ (src j).val)
    (tbl : BitAssignment k₁ → BitAssignment k₂)
    (hEvalSrc : ∀ (α : BitAssignment (k₁ + k₂)) (j : Fin k₂),
      p.eval (padZeroBits α) (src j) = tbl (fun i ↦ α (Fin.castAdd k₂ i)) j) :
    let M := k₁ + k₂ + mScr
    let hk : k₁ + k₂ ≤ M := Nat.le_add_right (k₁ + k₂) mScr
    let prog : TempPhaseProg M :=
      (rawSsaToSharedCtx p.raw).plug (.cliff (copySlotCliff k₁ k₂ hk src hSrcGe k₂ le_rfl))
    prog.countTempAnd = p.countAnd ∧
    ValidCleanRem M mScr prog ∧
    (∀ α : BitAssignment (k₁ + k₂),
      prog.evalBits (padZeroBits α) = padZeroBits (xorRightMapGen tbl α)) ∧
    (∀ α : BitAssignment (k₁ + k₂), prog.evalSign (padZeroBits α) = 0) := by
  intro M hk prog
  let q₀ : Wire M := ⟨0, hkPos⟩
  let mutW : Wire M → Prop := fun w ↦ k₁ ≤ w.val ∧ w.val < k₁ + k₂
  let cCopy := copySlotCliff k₁ k₂ hk src hSrcGe k₂ le_rfl
  let K : TempCtx M := rawSsaToSharedCtx p.raw
  have hProgEq : prog = K.plug (.cliff cCopy) := rfl
  have hDisj : K.DisjointFrom mutW := rawSsa_toTempCtx_disjoint k₁ (k₁ + k₂) p.raw hAvoid
  have hSupp : K.SupportsBelowCtx M := rawSsa_toTempCtx_supportsM p.raw
  have hBodyNonMut : ∀ (γ : BitAssignment M) (w : Wire M),
      ¬ mutW w → (TempPhaseProg.cliff cCopy).evalBits γ w = γ w := by
    intro γ w hw
    dsimp only [TempPhaseProg.evalBits]
    rw [copySlotCliff_eval k₁ k₂ hk src hSrcGe k₂ le_rfl γ w, diteNeg hw]
  obtain ⟨hNilBits, hNilVal⟩ := rawSsaToSharedCtx_valid_and_bits p.raw p.wf (le_refl M)
  obtain ⟨hZBits, hZVal⟩ := rawSsa_plug_z_eq_nil q₀ K
  have hSub : M - (k₁ + k₂) = mScr := by dsimp [M]; omega
  rw [hSub] at hNilBits hNilVal
  have hVal : ValidCleanRem M mScr prog :=
    TempCtx.plug_validCleanRem hDisj hSupp (by simp [ValidCleanRem]) hBodyNonMut q₀
      (by omega : M - M ≤ mScr) (hZVal mScr hNilVal)
  have hCnt : prog.countTempAnd = p.countAnd := by
    rw [hProgEq, TempCtx.plug_countTempAnd]
    change K.countTempAnd + 0 = p.countAnd
    rw [Nat.add_zero]
    have hK_cnt : ∀ r : RawSsa M, (rawSsaToSharedCtx r).countTempAnd = r.countAnd := by
      intro r; induction r with
      | done => rfl
      | x _ rest ih => simpa [rawSsaToSharedCtx, TempCtx.countTempAnd, RawSsa.countAnd] using ih
      | cnot _ _ _ rest ih =>
        simpa [rawSsaToSharedCtx, TempCtx.countTempAnd, RawSsa.countAnd] using ih
      | skipZero rest ih => exact ih
      | andClean _ _ _ _ _ _ rest ih =>
          simp only [rawSsaToSharedCtx, TempCtx.countTempAnd, RawSsa.countAnd, ih]
    exact hK_cnt p.raw
  refine ⟨hCnt, hVal, fun α ↦ ?_, fun α ↦ ?_⟩
  · have hcl : cleanRem M mScr (padZeroBits α) := fun w hw ↦
      padZeroBits_ge α w (by dsimp [M] at hw; omega)
    obtain ⟨hMut, hNon⟩ := TempCtx.plug_evalBits_split hDisj hBodyNonMut q₀ (padZeroBits α)
    funext w
    by_cases hm : mutW w
    · rw [hMut w hm]
      dsimp only [TempPhaseProg.evalBits]
      rw [rawSsaToSharedCtx_fwdBits p.raw, copySlotCliff_eval k₁ k₂ hk src hSrcGe k₂ le_rfl _ w,
        ditePos hm]
      have hw_lt : w.val < k₁ + k₂ := hm.2
      have hnot_lo : ¬ w.val < k₁ := by omega
      rw [padZeroBits_lt (xorRightMapGen tbl α) w hw_lt]
      dsimp only [xorRightMapGen]
      rw [diteNeg hnot_lo]
      have hp_mid : p.eval (padZeroBits α) w = α ⟨w.val, hw_lt⟩ := (rawSsa_eval_mid k₁ (k₁ +
          k₂) p.raw hAvoid (padZeroBits α) w hm).trans (padZeroBits_lt α w hw_lt)
      change p.eval (padZeroBits α) w + p.eval (padZeroBits α) (src ⟨w.val - k₁, _⟩) = _
      rw [hp_mid, hEvalSrc α ⟨w.val - k₁, by omega⟩]
    · rw [hNon w hm, hZBits (padZeroBits α), hNilBits (padZeroBits α) hcl]
      by_cases hw_lt : w.val < k₁ + k₂
      · have hw_lo : w.val < k₁ := by dsimp [mutW] at hm; omega
        rw [padZeroBits_lt α w hw_lt, padZeroBits_lt (xorRightMapGen tbl α) w hw_lt]
        dsimp only [xorRightMapGen]
        rw [ditePos hw_lo]
      · rw [padZeroBits_ge α w (by omega), padZeroBits_ge (xorRightMapGen tbl α) w (by omega)]
  · rw [hProgEq, TempCtx.plug_evalSign]
    rfl
/- ## Stage 1: `68`-`TempAnd` Threshold Lookup `progStage1Kc49` on `49 + 68 = 117` Wires -/

theorem s1Kc68_meta :
    microValid 8 s1Kc68Ops = true ∧ microAllocs s1Kc68Ops = 68 ∧ 49 + 68 = 117 := by
  decide +kernel

def checkStage1Cert : Bool := PTree.withVal (simdRun 256 8 s1Kc68Ops) fun t ↦ allBelow 8
    (fun i ↦ Nat.beq (pget 0 8 t i) (colMaskFast 256 i)) && allBelow 16 (fun j ↦ Nat.beq (pget
    0 8 t (getNatAt s1Kc68OutSlots j)) (packPredLoop (fun c ↦ fastBitSmall (getNatAt
    kcTable49168List c) j) 256 0 1 0))

theorem checkStage1Cert_true : checkStage1Cert = true := by decide +kernel

def tblBits16 (α33 : BitAssignment 33) : BitAssignment 16 :=
  fun j ↦ b2z ((getNatAt kcTable49168List (bitsVal (fun i : Fin 8 ↦
    α33 ⟨25 + i.val, by omega⟩))).testBit j.val)

/-- Helper `listXor` for compact `165`-wire Slot-3 state preparation. -/
def listXor : List ℕ → List ℕ → List ℕ
  | a :: as, b :: bs => Nat.xor a b :: listXor as bs
  | _, _ => []
/-- Helper `listScale` for compact `165`-wire Slot-3 state preparation. -/
def listScale : ℕ → List ℕ → List ℕ
  | m, b :: bs => Nat.land m b :: listScale m bs
  | _, [] => []
/-- Helper `listAllZero` for compact `165`-wire Slot-3 state preparation. -/
def listAllZero : List ℕ → Bool
  | [] => true
  | x :: xs => Bool.casesOn (Nat.beq x 0) false (listAllZero xs)
/-- Helper `listEqNat` for compact `165`-wire Slot-3 state preparation. -/
def listEqNat : List ℕ → List ℕ → Bool
  | [], [] => true
  | a :: as, b :: bs => Bool.casesOn (Nat.beq a b) false (listEqNat as bs)
  | _, _ => false
theorem listEqNat_iff : ∀ (xs ys : List ℕ), listEqNat xs ys = true ↔ xs = ys
  | [], [] => by simp [listEqNat]
  | [], _ :: _ => by simp [listEqNat]
  | _ :: _, [] => by simp [listEqNat]
  | a :: as, b :: bs => by
      dsimp only [listEqNat]
      by_cases hab : Nat.beq a b = true
      · rw [hab]; dsimp only
        rw [listEqNat_iff as bs]
        have haeq := (nat_beq_iff a b).mp hab
        subst haeq; simp
      · have hbf : Nat.beq a b = false := Bool.eq_false_iff.mpr hab
        rw [hbf]; simp only [Bool.false_eq_true, false_iff, List.cons.injEq, not_and]
        intro haeq _; exact hab ((nat_beq_iff a b).mpr haeq)
/-- Helper `evalLin15` for compact `165`-wire Slot-3 state preparation. -/
def evalLin15 (t7 u : ℕ) : ℕ → List ℕ → Bool
  | _, [] => false
  | i, c :: cs => xor (u.testBit i && c.testBit t7) (evalLin15 t7 u (i + 1) cs)
/-- Helper `evalAff16` for compact `165`-wire Slot-3 state preparation. -/
def evalAff16 (u : ℕ) : List ℕ → Bool
  | [] => false
  | c0 :: cs => xor (c0.testBit (u / 32768)) (evalLin15 (u / 32768) u 0 cs)
theorem length_listXor : ∀ (xs ys : List ℕ),
    xs.length = ys.length → (listXor xs ys).length = xs.length
  | [], [], _ => rfl
  | _ :: as, _ :: bs, h => by simp [listXor, length_listXor as bs (by simpa using h)]
theorem length_listScale (m : ℕ) : ∀ (xs : List ℕ), (listScale m xs).length = xs.length
  | [] => rfl
  | _ :: bs => by simp [listScale, length_listScale m bs]
theorem evalLin15_zero (t7 u : ℕ) : ∀ (i : ℕ) (cs : List ℕ),
    listAllZero cs = true → evalLin15 t7 u i cs = false
  | _, [], _ => rfl
  | i, c :: cs, hz => by
      dsimp only [listAllZero] at hz
      by_cases hc0 : Nat.beq c 0 = true
      · rw [hc0] at hz; dsimp only at hz
        have hce := (nat_beq_iff c 0).mp hc0
        subst hce
        simp [evalLin15, evalLin15_zero t7 u (i + 1) cs hz]
      · rw [Bool.eq_false_iff.mpr hc0] at hz; cases hz
theorem bool_xor_four (a b c d : Bool) : xor (xor a b) (xor c d) = xor (xor a c) (xor b d) := by
  cases a <;> cases b <;> cases c <;> cases d <;> rfl
theorem evalLin15_xor (t7 u : ℕ) : ∀ (i : ℕ) (xs ys : List ℕ),
    xs.length = ys.length →
    evalLin15 t7 u i (listXor xs ys) = xor (evalLin15 t7 u i xs) (evalLin15 t7 u i ys)
  | _, [], [], _ => rfl
  | i, a :: as, b :: bs, hlen => by
      dsimp only [listXor, evalLin15]
      rw [evalLin15_xor t7 u (i + 1) as bs (by simpa using hlen)]
      change xor (u.testBit i && (a ^^^ b).testBit t7) _ = _
      rw [Nat.testBit_xor]
      have hd : (u.testBit i && xor (a.testBit t7) (b.testBit t7)) =
          xor (u.testBit i && a.testBit t7) (u.testBit i && b.testBit t7) := by
        cases u.testBit i <;> cases a.testBit t7 <;> cases b.testBit t7 <;> rfl
      rw [hd]
      exact bool_xor_four _ _ _ _
theorem evalLin15_scale (t7 u m : ℕ) : ∀ (i : ℕ) (cs : List ℕ),
    evalLin15 t7 u i (listScale m cs) = (m.testBit t7 && evalLin15 t7 u i cs)
  | _, [] => by simp [listScale, evalLin15]
  | i, c :: cs => by
      dsimp only [listScale, evalLin15]
      rw [evalLin15_scale t7 u m (i + 1) cs]
      change xor (u.testBit i && (m &&& c).testBit t7) _ = _
      rw [Nat.testBit_and]
      cases m.testBit t7 <;> cases u.testBit i <;> cases c.testBit t7 <;>
        cases evalLin15 t7 u (i + 1) cs <;> rfl
/-- Helper `affZero16` for compact `165`-wire Slot-3 state preparation. -/
def affZero16 : List ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- Helper `affNot` for compact `165`-wire Slot-3 state preparation. -/
def affNot (all128 : ℕ) : List ℕ → List ℕ
  | [] => []
  | c0 :: cs => Nat.xor all128 c0 :: cs
/-- Helper `affAndOpt` for compact `165`-wire Slot-3 state preparation. -/
def affAndOpt : List ℕ → List ℕ → Option (List ℕ)
  | a0 :: as, b0 :: bs =>
      if listAllZero as then some (listScale a0 (b0 :: bs))
      else if listAllZero bs then some (listScale b0 (a0 :: as))
      else none
  | _, _ => none
theorem affNot_eval (u : ℕ) (hu : u / 32768 < 128) (a : List ℕ) (ha : a.length = 16) :
    (affNot (allMaskFast 128 1) a).length = 16 ∧
      evalAff16 u (affNot (allMaskFast 128 1) a) = Bool.not (evalAff16 u a) := by
  rcases a with _ | ⟨c0, cs⟩
  · cases ha
  · refine ⟨ha, ?_⟩
    dsimp only [affNot, evalAff16]
    change xor ((allMaskFast 128 1 ^^^ c0).testBit (u / 32768)) _ = _
    rw [Nat.testBit_xor, testBit_allMaskFast hu]
    cases c0.testBit (u / 32768) <;> cases evalLin15 (u / 32768) u 0 cs <;> rfl
theorem affXor_eval (u : ℕ) (a b : List ℕ) (ha : a.length = 16) (hb : b.length = 16) :
    (listXor b a).length = 16 ∧
      evalAff16 u (listXor b a) = xor (evalAff16 u b) (evalAff16 u a) := by
  rcases a with _ | ⟨a0, as⟩; · cases ha
  rcases b with _ | ⟨b0, bs⟩; · cases hb
  refine ⟨length_listXor _ _ (hb.trans ha.symm) |>.trans hb, ?_⟩
  dsimp only [listXor, evalAff16]
  rw [evalLin15_xor (u / 32768) u 0 bs as (by simp at ha hb; omega)]
  change xor ((b0 ^^^ a0).testBit (u / 32768)) _ = _
  rw [Nat.testBit_xor]
  exact bool_xor_four _ _ _ _
private theorem affScaleZero_eval (u x0 y0 : ℕ) (xs ys : List ℕ) (hz : listAllZero xs = true) :
    evalAff16 u (listScale x0 (y0 :: ys)) = (evalAff16 u (x0 :: xs) && evalAff16 u (y0 :: ys)) := by
  dsimp only [listScale, evalAff16]
  rw [evalLin15_zero (u / 32768) u 0 xs hz, evalLin15_scale]
  change xor ((x0 &&& y0).testBit (u / 32768)) _ = _
  rw [Nat.testBit_and]
  cases x0.testBit (u / 32768) <;> cases y0.testBit (u / 32768) <;>
    cases evalLin15 (u / 32768) u 0 ys <;> rfl

theorem affAndOpt_eval (u : ℕ) {a b res : List ℕ}
    (ha : a.length = 16) (hb : b.length = 16) (hopt : affAndOpt a b = some res) :
    res.length = 16 ∧ evalAff16 u res = (evalAff16 u a && evalAff16 u b) := by
  rcases a with _ | ⟨a0, as⟩; · cases ha
  rcases b with _ | ⟨b0, bs⟩; · cases hb
  dsimp only [affAndOpt] at hopt
  by_cases hza : listAllZero as = true
  · rw [hza] at hopt; simp only [↓reduceIte, Option.some.injEq] at hopt; subst hopt
    exact ⟨(length_listScale a0 (b0 :: bs)).trans hb, affScaleZero_eval u a0 b0 as bs hza⟩
  · rw [Bool.eq_false_iff.mpr hza] at hopt; simp only [Bool.false_eq_true, ↓reduceIte] at hopt
    by_cases hzb : listAllZero bs = true
    · rw [hzb] at hopt; simp only [↓reduceIte, Option.some.injEq] at hopt; subst hopt
      exact ⟨(length_listScale b0 (a0 :: as)).trans ha,
        (affScaleZero_eval u b0 a0 bs as hzb).trans (Bool.and_comm _ _)⟩
    · rw [Bool.eq_false_iff.mpr hzb] at hopt; cases hopt
/-- Helper `mkListFrom` for compact `165`-wire Slot-3 state preparation. -/
def mkListFrom (f : ℕ → ℕ) : ℕ → ℕ → List ℕ
  | _, 0 => []
  | off, rem + 1 => f off :: mkListFrom f (off + 1) rem
theorem length_mkListFrom (f : ℕ → ℕ) : ∀ off rem : ℕ, (mkListFrom f off rem).length = rem
  | _, 0 => rfl
  | off, rem + 1 => by simp [mkListFrom, length_mkListFrom f (off + 1) rem]
theorem evalLin15_mkListFrom_false (f : ℕ → ℕ) (t7 u : ℕ) :
    ∀ (off rem : ℕ), (∀ j, off ≤ j → j < off + rem → (f j).testBit t7 = false) →
      evalLin15 t7 u off (mkListFrom f off rem) = false
  | _, 0, _ => rfl
  | off, rem + 1, h => by
      dsimp only [mkListFrom, evalLin15]
      rw [h off le_rfl (by omega), Bool.and_false,
        evalLin15_mkListFrom_false f t7 u (off + 1) rem (fun j h1 h2 ↦ h j (by omega) (by omega))]
      rfl
theorem evalLin15_mkListFrom_single (f : ℕ → ℕ) (t7 u k : ℕ) :
    ∀ (off rem : ℕ), off ≤ k → k < off + rem →
      (∀ j, off ≤ j → j < off + rem → (f j).testBit t7 = decide (j = k)) →
      evalLin15 t7 u off (mkListFrom f off rem) = u.testBit k
  | _, 0, hlo, hhi, _ => by omega
  | off, rem + 1, hlo, hhi, h => by
      dsimp only [mkListFrom, evalLin15]
      by_cases hok : off = k
      · subst hok
        rw [h off le_rfl (by omega), decide_eq_true rfl, Bool.and_true,
          evalLin15_mkListFrom_false f t7 u (off + 1) rem (fun j h1 h2 ↦ by
            rw [h j (by omega) (by omega)]; exact decide_eq_false (by omega))]
        cases u.testBit off <;> rfl
      · rw [h off le_rfl (by omega), decide_eq_false hok, Bool.and_false,
          evalLin15_mkListFrom_single f t7 u k (off + 1) rem (by omega) (by omega)
            (fun j h1 h2 ↦ h j (by omega) (by omega))]
        cases u.testBit k <;> rfl
/-- Helper `initAff22` for compact `165`-wire Slot-3 state preparation. -/
def initAff22 (i : ℕ) : List ℕ := if Nat.ble 15 i then colMaskFast 128 (i - 15) :: mkListFrom
    (fun _ ↦ 0) 0 15 else 0 :: mkListFrom
    (fun j ↦ Bool.casesOn (Nat.beq j i) 0 (allMaskFast 128 1)) 0 15
theorem initAff22_spec {u : ℕ} (hu : u / 32768 < 128) {i : ℕ} (hi : i < 22) :
    (initAff22 i).length = 16 ∧ evalAff16 u (initAff22 i) = u.testBit i := by
  dsimp only [initAff22]
  by_cases h15 : 15 ≤ i
  · rw [(nat_ble_iff 15 i).mpr h15]; simp only [↓reduceIte]
    refine ⟨by simp [length_mkListFrom], ?_⟩
    dsimp only [evalAff16]
    rw [evalLin15_mkListFrom_false _ (u / 32768) u 0 15 (fun _ _ _ ↦ by simp),
      testBit_colMaskFast, decide_eq_true hu, Bool.true_and]
    have hdiv := testBit_div_two_powAux u 15 (i - 15)
    change (u / 32768).testBit (i - 15) = u.testBit (15 + (i - 15)) at hdiv
    rw [hdiv, show 15 + (i - 15) = i by omega]
    cases u.testBit i <;> rfl
  · have hbf : Nat.ble 15 i = false :=
      Bool.eq_false_iff.mpr (fun ht ↦ h15 ((nat_ble_iff 15 i).mp ht))
    rw [hbf]; simp only [Bool.false_eq_true, ↓reduceIte]
    refine ⟨by simp [length_mkListFrom], ?_⟩
    dsimp only [evalAff16]
    rw [Nat.zero_testBit,
      evalLin15_mkListFrom_single _ (u / 32768) u i 0 15 (Nat.zero_le i) (by omega)
        (fun j _ _ ↦ by
          by_cases hji : j = i
          · subst hji; rw [(nat_beq_iff j j).mpr rfl]; dsimp only
            rw [testBit_allMaskFast hu, decide_eq_true rfl]
          · have hjb : Nat.beq j i = false :=
              Bool.eq_false_iff.mpr (fun ht ↦ hji ((nat_beq_iff j i).mp ht))
            rw [hjb]; dsimp only; rw [Nat.zero_testBit, decide_eq_false hji])]
    cases u.testBit i <;> rfl
/-- Helper `initAffTree` for compact `165`-wire Slot-3 state preparation. -/
def initAffTree : ℕ → PTree (List ℕ) → PTree (List ℕ)
  | 0, t => t
  | i + 1, t => PTree.withVal (pset 8 t i (initAff22 i)) (initAffTree i)
theorem initAffTree_spec :
    ∀ (m : ℕ), m ≤ 22 → ∀ (t : PTree (List ℕ)), PTree.hasDepth 8 t →
      PTree.hasDepth 8 (initAffTree m t) ∧
        ∀ s < 256, pget affZero16 8 (initAffTree m t) s =
          if s < m then initAff22 s else pget affZero16 8 t s
  | 0, _, t, ht => ⟨ht, fun _ _ ↦ by simp [initAffTree]⟩
  | i + 1, hm, t, ht => by
      dsimp only [initAffTree]; rw [PTree.withVal_eq]
      have h256 : (2 ^ 8 : ℕ) = 256 := by decide
      have ht' := pset_hasDepth 8 t ht i (by rw [h256]; omega) (initAff22 i)
      obtain ⟨hD, hG⟩ := initAffTree_spec i (by omega) _ ht'
      refine ⟨hD, fun s hs ↦ ?_⟩
      rw [hG s hs]
      by_cases hsi : s < i
      · simp [hsi, show s < i + 1 by omega]
      · simp only [hsi, ↓reduceIte]
        rw [pget_pset affZero16 8 t ht i (by rw [h256]; omega) s (by rw [h256]; exact hs)]
        by_cases heq : s = i
        · subst heq; simp
        · simp [heq, show ¬ (s < i + 1) by omega]
/-- Helper `forceListNat` for compact `165`-wire Slot-3 state preparation. -/
def forceListNat : List ℕ → (List ℕ → Option (PTree (List ℕ))) → Option (PTree (List ℕ))
  | [], k => k []
  | x :: xs, k => forceNat x (fun x' ↦ forceListNat xs (fun xs' ↦ k (x' :: xs')))
theorem forceListNat_eq : ∀ (xs : List ℕ) (k : List ℕ → Option (PTree (List ℕ))),
    forceListNat xs k = k xs
  | [], _ => rfl
  | x :: xs, k => by
      dsimp only [forceListNat]
      rw [forceNat_eq, forceListNat_eq xs]
/-- Helper `evalAffSteps` for compact `165`-wire Slot-3 state preparation. -/
def evalAffSteps (all128 : ℕ) : ℕ → List MicroStep → PTree (List ℕ) → Option (PTree (List ℕ))
  | _, [], t => some t
  | top, .nW a :: rest, t =>
      forceListNat (affNot all128 (pget affZero16 8 t a)) fun v ↦
        PTree.withVal (pset 8 t a v) (evalAffSteps all128 top rest)
  | top, .cW a b :: rest, t =>
      forceListNat (listXor (pget affZero16 8 t b) (pget affZero16 8 t a)) fun v ↦
        PTree.withVal (pset 8 t b v) (evalAffSteps all128 top rest)
  | top, .aW a b :: rest, t =>
      match affAndOpt (pget affZero16 8 t a) (pget affZero16 8 t b) with
      | none => none
      | some res =>
          forceListNat res fun v ↦
            PTree.withVal (pset 8 t top v) (evalAffSteps all128 (top + 1) rest)
private theorem evalAffSteps_step_agree {u top' idx : ℕ} {t : PTree (List ℕ)} {st : List Bool}
    (hDt : PTree.hasDepth 8 t) (htop_st : top' ≤ st.length) (hst256 : st.length ≤ 256)
    (hidx : idx < top')
    (hagree : ∀ i < top', i ≠ idx →
      (pget affZero16 8 t i).length = 16 ∧ evalAff16 u (pget affZero16 8 t i) = getBoolAt st i)
    (res : List ℕ) (bv : Bool) (hres : res.length = 16 ∧ evalAff16 u res = bv) :
    ∀ j < top', (pget affZero16 8 (pset 8 t idx res) j).length = 16 ∧
      evalAff16 u (pget affZero16 8 (pset 8 t idx res) j) = getBoolAt (setBoolAt st idx bv) j := by
  have h256 : (2 ^ 8 : ℕ) = 256 := by decide
  intro j hj
  rw [pget_pset affZero16 8 t hDt idx (by rw [h256]; omega) j (by rw [h256]; omega),
    getBoolAt_setBoolAt st idx j (by omega)]
  by_cases hji : j = idx
  · subst hji; simp [hres]
  · simp [hji, hagree j hj hji]

theorem evalAffSteps_agree {u : ℕ} (hu : u / 32768 < 128) (ops : List MicroStep) : ∀ (top : ℕ)
    (t tOut : PTree (List ℕ)) (st : List Bool), PTree.hasDepth 8 t → microValid top ops = true
    → top + microAllocs ops = st.length → st.length ≤ 256 → (∀ i < top, (pget affZero16 8 t
    i).length = 16 ∧ evalAff16 u (pget affZero16 8 t i) = getBoolAt st i) → evalAffSteps
    (allMaskFast 128 1) top ops t = some tOut → ∀ i < st.length, evalAff16 u
    (pget affZero16 8 tOut i) = getBoolAt (evalMicroList top ops st) i := by
  have h256 : (2 ^ 8 : ℕ) = 256 := by decide
  induction ops with
  | nil =>
      intro top t tOut st _ _ halloc _ hagree hopt i hi
      dsimp only [evalAffSteps] at hopt; injection hopt with hEq; subst hEq
      dsimp only [microAllocs, Nat.add_zero] at halloc
      exact (hagree i (by omega)).2
  | cons op rest ih =>
      intro top t tOut st hDt hv halloc hlen hagree hopt i hi
      cases op with
      | nW a =>
          obtain ⟨ha, hvR⟩ := microValid_nW hv
          dsimp only [microAllocs] at halloc
          dsimp only [evalAffSteps, evalMicroList] at hopt ⊢
          rw [forceListNat_eq, PTree.withVal_eq] at hopt
          obtain ⟨hlN, heN⟩ := affNot_eval u hu _ (hagree a ha).1
          refine ih top _ tOut _ (pset_hasDepth 8 t hDt a (by rw [h256]; omega) _) hvR
            (by rw [length_setBoolAt]; exact halloc) (by rw [length_setBoolAt]; exact hlen)
            (evalAffSteps_step_agree hDt (by omega) hlen ha (fun j hj _ ↦ hagree j hj) _ _
              ⟨hlN, heN.trans (congrArg Bool.not (hagree a ha).2)⟩)
            hopt i (by rw [length_setBoolAt]; exact hi)
      | cW a b =>
          obtain ⟨ha, hb, _, hvR⟩ := microValid_cW hv
          dsimp only [microAllocs] at halloc
          dsimp only [evalAffSteps, evalMicroList] at hopt ⊢
          rw [forceListNat_eq, PTree.withVal_eq] at hopt
          obtain ⟨hlX, heX⟩ := affXor_eval u _ _ (hagree a ha).1 (hagree b hb).1
          refine ih top _ tOut _ (pset_hasDepth 8 t hDt b (by rw [h256]; omega) _) hvR
            (by rw [length_setBoolAt]; exact halloc) (by rw [length_setBoolAt]; exact hlen)
            (evalAffSteps_step_agree hDt (by omega) hlen hb (fun j hj _ ↦ hagree j hj) _ _
              ⟨hlX, heX.trans (by rw [(hagree b hb).2, (hagree a ha).2])⟩)
            hopt i (by rw [length_setBoolAt]; exact hi)
      | aW a b =>
          obtain ⟨ha, hb, _, hvR⟩ := microValid_aW hv
          dsimp only [microAllocs] at halloc
          dsimp only [evalAffSteps, evalMicroList] at hopt ⊢
          cases hAnd : affAndOpt (pget affZero16 8 t a) (pget affZero16 8 t b) with
          | none => rw [hAnd] at hopt; cases hopt
          | some res =>
              rw [hAnd] at hopt; dsimp only at hopt
              rw [forceListNat_eq, PTree.withVal_eq] at hopt
              obtain ⟨hlR, heR⟩ := affAndOpt_eval u (hagree a ha).1 (hagree b hb).1 hAnd
              refine ih (top + 1) _ tOut _ (pset_hasDepth 8 t hDt top (by rw [h256]; omega) _) hvR
                (by rw [length_setBoolAt]; omega) (by rw [length_setBoolAt]; exact hlen)
                (evalAffSteps_step_agree hDt (by omega) hlen (Nat.lt_succ_self top)
                  (fun j hj hne ↦ hagree j (by omega)) _ _
                  ⟨hlR, heR.trans (by rw [(hagree a ha).2, (hagree b hb).2])⟩)
                hopt i (by rw [length_setBoolAt]; exact hi)
attribute [local irreducible] evalMicroList
/-- Helper `fastTop7Mu` for compact `165`-wire Slot-3 state preparation. -/
def fastTop7Mu (t : ℕ) : ℕ := Bool.casesOn (Nat.ble 64 t) (Bool.casesOn (Nat.ble 32 t)
    (Bool.casesOn (Nat.ble 16 t) (Bool.casesOn (Nat.ble 8 t) (Bool.casesOn (Nat.ble 4 t)
    (Bool.casesOn (Nat.ble 2 t) 0 1) 2) 3) 4) 5) 6
theorem fastTop7Mu_eq {t : ℕ} (ht : t < 128) : fastTop7Mu t = top7Mu t := by
  have hall : allBelow 128 (fun x ↦ Nat.beq (fastTop7Mu x) (top7Mu x)) = true := by decide
  exact (nat_beq_iff _ _).mp ((allBelow_iff 128 _).mp hall t ht)
/-- Helper `targetZ7Aff` for compact `165`-wire Slot-3 state preparation. -/
def targetZ7Aff : List ℕ := 1 :: mkListFrom (fun _ ↦ 0) 0 15
/-- Helper `targetMtAff` for compact `165`-wire Slot-3 state preparation. -/
def targetMtAff (w b : ℕ) : List ℕ :=
  let c0 := packPredLoop (fun t ↦
    let mu := fastTop7Mu t
    Bool.casesOn (Nat.ble (6 - b) mu) false
      (let k := w * (mu + 1) + (b - (6 - mu))
       Bool.casesOn (Nat.ble 15 k) false (fastBitSmall t (k - 15)))) 128 0 1 0
  c0 :: mkListFrom (fun j ↦
    packPredLoop (fun t ↦
      let mu := fastTop7Mu t
      Bool.casesOn (Nat.ble (6 - b) mu) false
        (Nat.beq (w * (mu + 1) + (b - (6 - mu))) j)) 128 0 1 0) 0 15
theorem targetZ7Aff_eval (u22 : Fin 4194304) :
    evalAff16 u22.val targetZ7Aff = decide (u22.val / 32768 = 0) := by
  dsimp only [targetZ7Aff, evalAff16]
  rw [evalLin15_mkListFrom_false _ _ _ 0 15 (fun _ _ _ ↦ by simp)]
  have h1 : (1 : ℕ).testBit (u22.val / 32768) = decide (u22.val / 32768 = 0) := by
    simpa using testBit_two_pow 0 (u22.val / 32768)
  rw [h1]; cases decide (u22.val / 32768 = 0) <;> rfl
theorem targetMtAff_eval (u22 : Fin 4194304) (w : Fin 3) (b : Fin 7) :
    evalAff16 u22.val (targetMtAff w.val b.val) = (shiftedMag3 u22 w).testBit b.val := by
  set t7 := u22.val / 32768
  have ht7 : t7 < 128 := by have := u22.isLt; omega
  have hmu : fastTop7Mu t7 = shellMu3 u22 := (fastTop7Mu_eq ht7).trans (top7Mu_eq_shellMu3 u22)
  dsimp only [targetMtAff, evalAff16]
  rw [shiftedMag3_testBit u22 w b]
  have hc0 : (packPredLoop (fun t ↦
      let mu := fastTop7Mu t
      Bool.casesOn (Nat.ble (6 - b.val) mu) false
        (let k := w.val * (mu + 1) + (b.val - (6 - mu))
         Bool.casesOn (Nat.ble 15 k) false (fastBitSmall t (k - 15)))) 128 0 1 0).testBit t7 =
      (Bool.casesOn (Nat.ble (6 - b.val) (shellMu3 u22)) false
        (let k := w.val * (shellMu3 u22 + 1) + (b.val - (6 - shellMu3 u22))
         Bool.casesOn (Nat.ble 15 k) false (t7.testBit (k - 15)))) := by
    rw [testBit_packPredLoop_zero _ 128 t7 ht7]
    simp only [hmu, fastBitSmall_eq_testBit]
  rw [hc0]
  by_cases hle : 6 - b.val ≤ shellMu3 u22
  · rw [(nat_ble_iff (6 - b.val) (shellMu3 u22)).mpr hle, itePos hle]; dsimp only
    set k := w.val * (shellMu3 u22 + 1) + (b.val - (6 - shellMu3 u22))
    by_cases hk15 : 15 ≤ k
    · rw [(nat_ble_iff 15 k).mpr hk15]; dsimp only
      rw [evalLin15_mkListFrom_false _ t7 u22.val 0 15 (fun j _ _ ↦ by
        rw [testBit_packPredLoop_zero _ 128 t7 ht7]
        simp only [hmu]
        rw [(nat_ble_iff (6 - b.val) (shellMu3 u22)).mpr hle]; dsimp only
        exact Bool.eq_false_iff.mpr (fun ht ↦ by have := (nat_beq_iff k j).mp ht; omega))]
      have hdiv := testBit_div_two_powAux u22.val 15 (k - 15)
      change t7.testBit (k - 15) = u22.val.testBit (15 + (k - 15)) at hdiv
      rw [hdiv, show 15 + (k - 15) = k by omega]
      cases u22.val.testBit k <;> rfl
    · have hkbf : Nat.ble 15 k = false :=
        Bool.eq_false_iff.mpr (fun ht ↦ hk15 ((nat_ble_iff 15 k).mp ht))
      rw [hkbf]; dsimp only
      rw [evalLin15_mkListFrom_single _ t7 u22.val k 0 15 (Nat.zero_le k) (by omega)
        (fun j _ _ ↦ by
          rw [testBit_packPredLoop_zero _ 128 t7 ht7]
          simp only [hmu]
          rw [(nat_ble_iff (6 - b.val) (shellMu3 u22)).mpr hle]; dsimp only
          by_cases hjk : j = k
          · rw [hjk, (nat_beq_iff k k).mpr rfl, decide_eq_true rfl]
          · rw [Bool.eq_false_iff.mpr (fun ht ↦ hjk ((nat_beq_iff k j).mp ht).symm),
              decide_eq_false hjk])]
      cases u22.val.testBit k <;> rfl
  · have hbf : Nat.ble (6 - b.val) (shellMu3 u22) = false :=
      Bool.eq_false_iff.mpr (fun ht ↦ hle ((nat_ble_iff _ _).mp ht))
    rw [hbf, iteNeg hle]; dsimp only
    rw [evalLin15_mkListFrom_false _ t7 u22.val 0 15 (fun j _ _ ↦ by
      rw [testBit_packPredLoop_zero _ 128 t7 ht7]
      simp only [hmu]
      rw [hbf])]
    rfl
/- ## Stage 2: `64`-`TempAnd` Shell Unpacker `progStage2Unpack71` on `71 + 64 = 135` Wires -/

/-- `22`-bit `u22` input wire map inside `71 + 64 = 135` wires. -/
def inU22 : Fin 22 → Wire (71 + 64) := fun i ↦ ⟨i.val, by omega⟩

theorem inU22_inj : Function.Injective inU22 := fun i j h ↦
  Fin.ext (by simpa [inU22] using congrArg Fin.val h)

theorem inU22_lt71 : ∀ i, (inU22 i).val < 71 := fun i ↦ by dsimp [inU22]; omega

theorem inU22_lt49 : ∀ i, (inU22 i).val < 49 := fun i ↦ by dsimp [inU22]; omega

theorem s2Unpack64_meta :
    microValid 22 s2Unpack64Ops = true ∧ microAllocs s2Unpack64Ops = 64 ∧ 71 + 64 = 135 := by
  decide +kernel

/-- Stage-2 `64`-AND SSA program on `71 + 64 = 135` wires. -/
def ssaStage2Unpack64 : SsaProg (71 + 64) 71 (71 + 64) :=
  ssaMicro inU22 inU22_inj 71 135 64 inU22_lt71 s2Unpack64Ops s2Unpack64_meta (le_refl 135)

theorem ssaStage2Unpack64_countAnd : ssaStage2Unpack64.countAnd = 64 :=
  (ssaMicro_spec inU22 inU22_inj 71 135 64 inU22_lt71 s2Unpack64Ops s2Unpack64_meta (le_refl 135)).1

theorem ssaStage2Unpack64_avoidsMid : RawSsaAvoidsMid 49 (49 + 22) ssaStage2Unpack64.raw :=
  ssaMicro_avoidsMid inU22 inU22_inj 49 71 135 64 inU22_lt71 inU22_lt49
    s2Unpack64Ops s2Unpack64_meta (le_refl 135)

/-- Stage-2 affine-tree equivalence certificate. -/
def stage2CheckTree (t : PTree (List ℕ)) : Bool := allBelow 22
    (fun i ↦ listEqNat (pget affZero16 8 t i) (initAff22 i)) && listEqNat
    (pget affZero16 8 t 27) targetZ7Aff && allBelow 3 (fun w ↦ allBelow 7 (fun b ↦ listEqNat
    (pget affZero16 8 t (getNatAt s2MtSlotsFlat (7 * w + b))) (targetMtAff w b)))

theorem checkStage2Cert_true :
    checkOpt
      (evalAffSteps (allMaskFast 128 1) 22 s2Unpack64Ops (initAffTree 22 (pconst affZero16 8)))
      stage2CheckTree = true := by decide +kernel

/-- Scratch wire `76 = 71 + (27 - 22)` holding `z7` inside Stage 2 (`71 + 64 = 135`). -/
def z7Scratch : Wire (71 + 64) := ⟨76, by decide⟩

/-- Scratch wires holding the `3 × 7` bits of `shiftedMag3 u22` inside Stage 2 (`71 + 64 = 135`). -/
def mtScratch (w : Fin 3) (b : Fin 7) : Wire (71 + 64) :=
  ⟨71 + (getNatAt s2MtSlotsFlat (7 * w.val + b.val) - 22), by revert w b; decide⟩

theorem ssaStage2Unpack64_spec (β : BitAssignment (71 + 64))
    (hcl : ∀ w : Wire (71 + 64), 71 ≤ w.val → β w = 0) :
    let u22 : Fin 4194304 := ⟨bitsVal (fun i ↦ β (inU22 i)), bitsVal_lt_two_pow _⟩
    let δ := ssaStage2Unpack64.eval β
    ssaStage2Unpack64.countAnd = 64 ∧
    (∀ w : Wire (71 + 64), 135 ≤ w.val → δ w = 0) ∧
    (∀ w : Wire (71 + 64), w.val < 71 → δ w = β w) ∧
    δ z7Scratch = b2z (decide (u22.val / 32768 = 0)) ∧
    (∀ (w : Fin 3) (b : Fin 7), δ (mtScratch w b) = b2z ((shiftedMag3 u22 w).testBit b.val)) := by
  dsimp only
  let u := bitsVal (fun i ↦ β (inU22 i))
  let u22 : Fin 4194304 := ⟨u, bitsVal_lt_two_pow _⟩
  have hu_t7 : u / 32768 < 128 := by have := u22.isLt; dsimp only [u22] at this; omega
  obtain ⟨hCnt, hEv⟩ := ssaMicro_spec inU22 inU22_inj 71 135 64 inU22_lt71
    s2Unpack64Ops s2Unpack64_meta (le_refl 135)
  obtain ⟨hcO, hpO, hsO⟩ := hEv β hcl
  obtain ⟨tOut, hRun, hcert⟩ := checkOpt_sound checkStage2Cert_true
  dsimp only [stage2CheckTree] at hcert
  obtain ⟨h12, hMt⟩ := Bool.and_eq_true_iff.mp hcert
  obtain ⟨hIn, hZ7⟩ := Bool.and_eq_true_iff.mp h12
  obtain ⟨hD0, hG0⟩ := initAffTree_spec 22 (by decide) (pconst affZero16 8)
    (pconst_hasDepth affZero16 8)
  have hlen_st : (initBoolList 22 (22 + 64) u).length = 86 := length_mkBoolList 22 u 0 (22 + 64)
  have hAgree := evalAffSteps_agree hu_t7 s2Unpack64Ops 22
    (initAffTree 22 (pconst affZero16 8)) tOut (initBoolList 22 (22 + 64) u) hD0
    s2Unpack64_meta.1 (by rw [s2Unpack64_meta.2.1, hlen_st]) (by rw [hlen_st]; decide)
    (fun i hi ↦ by
      rw [hG0 i (by omega), itePos hi]
      obtain ⟨hl, he⟩ := initAff22_spec hu_t7 hi
      refine ⟨hl, he.trans ?_⟩
      dsimp only [initBoolList]
      rw [getBoolAt_mkBoolList 22 u 0 (22 + 64) i (by omega), Nat.zero_add,
        decide_eq_true hi, Bool.true_and]) hRun
  have hrest : ∀ i < 22,
      getBoolAt (evalMicroList 22 s2Unpack64Ops (initBoolList 22 (22 + 64) u)) i = u.testBit i := by
    intro i hi
    have hi_eq := (listEqNat_iff _ _).mp ((allBelow_iff 22 _).mp hIn i hi)
    rw [← hAgree i (by rw [hlen_st]; omega), hi_eq, (initAff22_spec hu_t7 hi).2]
  refine ⟨hCnt, hcO, hpO hrest, ?_, fun w b ↦ ?_⟩
  · have hz_eq := (listEqNat_iff _ _).mp hZ7
    have hw27 : z7Scratch = ⟨71 + (27 - 22), by decide⟩ := rfl
    dsimp only [ssaStage2Unpack64]
    rw [hw27, hsO 27 (by decide) (by decide), ← hAgree 27 (by rw [hlen_st]; decide),
      hz_eq, targetZ7Aff_eval u22]
  · have hs_bnd : 22 ≤ getNatAt s2MtSlotsFlat (7 * w.val + b.val) ∧
        getNatAt s2MtSlotsFlat (7 * w.val + b.val) < 86 := by
      revert w b; decide
    have hm_eq := (listEqNat_iff _ _).mp
      ((allBelow_iff 7 _).mp ((allBelow_iff 3 _).mp hMt w.val w.isLt) b.val b.isLt)
    dsimp only [ssaStage2Unpack64, mtScratch]
    rw [hsO _ hs_bnd.1 hs_bnd.2,
      ← hAgree _ (by rw [hlen_st]; exact hs_bnd.2), hm_eq, targetMtAff_eval u22 w b]

/-- Source scratch wires (`z7Scratch` followed by `3 × 7` `mtScratch`) copied into `[49..71)`. -/
def unpackSrc22 (j : Fin 22) : Wire (49 + 22 + 64) :=
  if h0 : j.val = 0 then z7Scratch
  else mtScratch ⟨(j.val - 1) / 7, by omega⟩ ⟨(j.val - 1) % 7, by omega⟩

theorem unpackSrc22_ge71 (j : Fin 22) : 49 + 22 ≤ (unpackSrc22 j).val := by
  revert j; decide

/-- `22`-bit unpacked `(z7, shiftedMag3 u22)` bit-assignment from `α49 : BitAssignment 49`. -/
def tblBitsUnpack22 (α49 : BitAssignment 49) : BitAssignment 22 :=
  let u22 : Fin 4194304 := ⟨bitsVal (fun i : Fin 22 ↦ α49 ⟨i.val, by omega⟩), bitsVal_lt_two_pow _⟩
  fun j ↦
    if h0 : j.val = 0 then
      b2z (decide (u22.val / 32768 = 0))
    else
      b2z ((shiftedMag3 u22 ⟨(j.val - 1) / 7, by omega⟩).testBit ((j.val - 1) % 7))

/-- Clean-tail `64`-`TempAnd` Stage-2 program XORing `tblBitsUnpack22` onto `[49..71)` and
  uncomputing `[71..135)` at `0 T`. -/
def progStage2Unpack71 : TempPhaseProg (49 + 22 + 64) :=
  (rawSsaToSharedCtx ssaStage2Unpack64.raw).plug
    (.cliff (copySlotCliff 49 22 (by decide) unpackSrc22 unpackSrc22_ge71 22 le_rfl))

theorem progStage2Unpack71_spec : progStage2Unpack71.countTempAnd = 64 ∧ ValidCleanRem
    (49 + 22 + 64) 64 progStage2Unpack71 ∧ (∀ α71 : BitAssignment (49 + 22),
    progStage2Unpack71.evalBits (padZeroBits α71) = padZeroBits (xorRightMapGen
    tblBitsUnpack22 α71)) ∧ (∀ α71 : BitAssignment (49 + 22), progStage2Unpack71.evalSign
    (padZeroBits α71) = 0) := by
  have hSpec := ssaPlugCopy_spec (k₁ := 49) (k₂ := 22) (mScr := 64) (by decide)
    ssaStage2Unpack64 ssaStage2Unpack64_avoidsMid unpackSrc22 unpackSrc22_ge71 tblBitsUnpack22
    (fun α71 j ↦ by
      have hcl : ∀ w : Wire (71 + 64), 71 ≤ w.val → padZeroBits α71 w = 0 :=
        fun w hw ↦ padZeroBits_ge α71 w hw
      obtain ⟨_, _, _, hz7, hmt⟩ := ssaStage2Unpack64_spec (padZeroBits α71) hcl
      have hu_eq : (fun i : Fin 22 ↦ padZeroBits α71 (inU22 i)) =
          (fun i : Fin 22 ↦ α71 (Fin.castAdd 22 ⟨i.val, by omega⟩)) := by
        funext i
        dsimp only [inU22]
        exact padZeroBits_lt α71 ⟨i.val, by omega⟩ (by dsimp; omega)
      dsimp only [unpackSrc22, tblBitsUnpack22]
      by_cases h0 : j.val = 0
      · rw [ditePos h0, ditePos h0]
        exact hz7.trans (by rw [hu_eq])
      · rw [diteNeg h0, diteNeg h0]
        exact (hmt ⟨(j.val - 1) / 7, by omega⟩ ⟨(j.val - 1) % 7, by omega⟩).trans (by rw [hu_eq]))
  simpa only [progStage2Unpack71, ssaStage2Unpack64_countAnd] using hSpec

attribute [local irreducible] ssaStage2Unpack64 progStage2Unpack71
/- ## Stage 3 + Stage 4: `127`-`TempAnd` Validity & CSA Kick (`ssaKick198` on `71 + 127 = 198`
Wires) -/

/-- Wire `[33..49)` holding bit `j` of `kc` inside `198` wires. -/
def kcWire (j : Fin 16) : Wire 198 := ⟨33 + j.val, by omega⟩

/-- Wire `49` holding `z7` inside `198` wires. -/
def z7Wire : Wire 198 := ⟨49, by decide⟩

/-- Wire `50 + 7*w + b` (`[50..71)`) holding bit `b` of `shiftedMag3 u22 w` inside `198` wires. -/
def mtWire (w : Fin 3) (b : Fin 7) : Wire 198 := ⟨50 + 7 * w.val + b.val, by omega⟩
/-- Helper `zPref` for compact `165`-wire Slot-3 state preparation. -/
def zPref (m : ℕ) : ℕ → Bool
  | 0 => (Bool.not (fastBitSmall m 0)) && (Bool.not (fastBitSmall m 1))
  | k + 1 => zPref m k && (Bool.not (fastBitSmall m (k + 2)))
theorem zPref_five_eq_zero {m : ℕ} (hm : m < 128) : zPref m 5 = decide (m = 0) := by
  have hall : allBelow 128 (fun x ↦ (zPref x 5 == Nat.beq x 0)) = true := by decide
  have hx := (bool_beq_iff _ _).mp ((allBelow_iff 128 _).mp hall m hm)
  rw [hx]
  by_cases h0 : m = 0
  · subst h0; rfl
  · rw [Bool.eq_false_iff.mpr (fun ht ↦ h0 ((nat_beq_iff m 0).mp ht)), decide_eq_false h0]
theorem s2AxisZbad7_meta (w : Fin 3) : microValid 8 s2AxisZbad7Ops = true ∧ microAllocs
    s2AxisZbad7Ops = 7 ∧ (71 + 7 * w.val) + 7 = 71 + 7 * (w.val + 1) := by
  revert w; decide
/-- Helper `checkZbad7Cert` for compact `165`-wire Slot-3 state preparation. -/
def checkZbad7Cert : Bool := PTree.withVal (simdRun 256 8 s2AxisZbad7Ops) fun t ↦ allBelow 8
    (fun i ↦ Nat.beq (pget 0 8 t i) (colMaskFast 256 i)) && allBelow 6 (fun k ↦ Nat.beq (pget
    0 8 t (8 + k)) (packPredLoop (fun r ↦ zPref (Nat.land r 127) k) 256 0 1 0)) && Nat.beq
    (pget 0 8 t 14) (packPredLoop (fun r ↦ zPref (Nat.land r 127) 5 && fastBitSmall r 7) 256 0
    1 0)
theorem checkZbad7Cert_true : checkZbad7Cert = true := by decide +kernel
/-- Helper `inZbad8` for compact `165`-wire Slot-3 state preparation. -/
def inZbad8 (w : Fin 3) : Fin 8 → Wire 198 := fun i ↦
  if h : i.val < 7 then mtWire w ⟨i.val, h⟩ else ⟨22 + w.val, by omega⟩
theorem inZbad8_inj (w : Fin 3) : Function.Injective (inZbad8 w) := by
  intro i j; revert w i j; decide
theorem inZbad8_lt (w : Fin 3) : ∀ i, (inZbad8 w i).val < 71 + 7 * w.val := by
  revert w; decide
/-- Helper `ssaAxisZbad7` for compact `165`-wire Slot-3 state preparation. -/
def ssaAxisZbad7 (w : Fin 3) : SsaProg 198 (71 + 7 * w.val) (71 + 7 * (w.val + 1)) :=
  ssaMicro (inZbad8 w) (inZbad8_inj w) (71 + 7 * w.val) (71 + 7 * (w.val + 1)) 7
    (inZbad8_lt w) s2AxisZbad7Ops (s2AxisZbad7_meta w) (by revert w; decide)
/-- Helper `zWire` for compact `165`-wire Slot-3 state preparation. -/
def zWire (w : Fin 3) (k : Fin 6) : Wire 198 :=
  ⟨71 + 7 * w.val + k.val, by omega⟩
/-- Helper `badWire` for compact `165`-wire Slot-3 state preparation. -/
def badWire (w : Fin 3) : Wire 198 :=
  ⟨71 + 7 * w.val + 6, by omega⟩
theorem ssaAxisZbad7_spec (w : Fin 3) (m7 : ℕ) (hm7 : m7 < 128) (sBit : Bool)
    (β : BitAssignment 198)
    (hcl : ∀ q : Wire 198, 71 + 7 * w.val ≤ q.val → β q = 0)
    (hmt : ∀ b : Fin 7, β (mtWire w b) = b2z (m7.testBit b.val))
    (hs : β ⟨22 + w.val, by omega⟩ = b2z sBit) :
    let δ := (ssaAxisZbad7 w).eval β
    (ssaAxisZbad7 w).countAnd = 7 ∧
    (∀ q : Wire 198, 71 + 7 * (w.val + 1) ≤ q.val → δ q = 0) ∧
    (∀ q : Wire 198, q.val < 71 + 7 * w.val → δ q = β q) ∧
    (∀ k : Fin 6, δ (zWire w k) = b2z (zPref m7 k.val)) ∧
    δ (badWire w) = b2z (decide (m7 = 0) && sBit) := by
  dsimp only
  let r := bitsVal (fun i ↦ β (inZbad8 w i))
  obtain ⟨hCnt, hEv⟩ := ssaMicro_spec (inZbad8 w) (inZbad8_inj w)
    (71 + 7 * w.val) (71 + 7 * (w.val + 1)) 7 (inZbad8_lt w)
    s2AxisZbad7Ops (s2AxisZbad7_meta w) (by have := w.isLt; omega)
  obtain ⟨hcO, hpO, hsO⟩ := hEv β hcl
  have hr_lt : r < 256 := bitsVal_lt_two_pow _
  have htb_lo : ∀ j < 7, (m7 + (if sBit then 128 else 0)).testBit j = m7.testBit j := fun j hj ↦ by
    cases sBit
    · simp
    · simp only [↓reduceIte]
      have hmod := testBit_mod_two_powAux 7 (m7 + 128) j
      rw [decide_eq_true hj, Bool.true_and, show (m7 + 128) % 2 ^ 7 = m7 by omega] at hmod
      exact hmod.symm
  have htb_7 : (m7 + (if sBit then 128 else 0)).testBit 7 = sBit := by
    have hdiv := testBit_div_two_powAux (m7 + (if sBit then 128 else 0)) 7 0
    change ((m7 + (if sBit then 128 else 0)) / 128).testBit 0 = _ at hdiv
    rw [← hdiv]
    cases sBit <;> simp only [Bool.false_eq_true, ↓reduceIte]
    · rw [show (m7 + 0) / 128 = 0 by omega]; rfl
    · rw [show (m7 + 128) / 128 = 1 by omega]; rfl
  have hr_eq : r = m7 + (if sBit then 128 else 0) := by
    refine bitsVal_eq_of_testBit _ _ (by cases sBit <;> (dsimp; omega)) fun i ↦ ?_
    by_cases hi7 : i.val < 7
    · rw [show inZbad8 w i = mtWire w ⟨i.val, hi7⟩ from ditePos hi7,
        hmt ⟨i.val, hi7⟩, htb_lo i.val hi7]
      cases m7.testBit i.val <;> rfl
    · rw [show inZbad8 w i = ⟨22 + w.val, by omega⟩ from diteNeg hi7,
        hs, show i.val = 7 by omega, htb_7]
      cases sBit <;> rfl
  have hr_land : Nat.land r 127 = m7 := by
    apply Nat.eq_of_testBit_eq; intro j
    change (r &&& 127).testBit j = m7.testBit j
    rw [Nat.testBit_and, show (127 : ℕ) = Nat.sub (Nat.pow 2 7) 1 from rfl, testBit_allMask 7 j]
    by_cases hj7 : j < 7
    · rw [decide_eq_true hj7, Bool.and_true, hr_eq]; exact htb_lo j hj7
    · rw [decide_eq_false hj7, Bool.and_false]
      exact (Nat.testBit_lt_two_pow
        (lt_of_lt_of_le hm7 (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 7 ≤ j)))).symm
  have hr_b7 : r.testBit 7 = sBit := hr_eq ▸ htb_7
  have hcert := checkZbad7Cert_true
  dsimp only [checkZbad7Cert] at hcert
  rw [PTree.withVal_eq] at hcert
  obtain ⟨h12, hBad⟩ := Bool.and_eq_true_iff.mp hcert
  obtain ⟨hIn, hZ⟩ := Bool.and_eq_true_iff.mp h12
  have hrest : ∀ i < 8,
      getBoolAt (evalMicroList 8 s2AxisZbad7Ops (initBoolList 8 15 r)) i = r.testBit i := by
    intro i hi
    have hi_eq := (nat_beq_iff _ _).mp ((allBelow_iff 8 _).mp hIn i hi)
    rw [← simdRun_testBit_eq 256 8 15 r i s2AxisZbad7Ops (by decide) hr_lt (by omega)
      (s2AxisZbad7_meta w).1 (by rw [(s2AxisZbad7_meta w).2.1]),
      hi_eq, testBit_colMaskFast, decide_eq_true hr_lt]; simp
  refine ⟨hCnt, hcO, hpO hrest, fun k ↦ ?_, ?_⟩
  · have hzk : zWire w k = ⟨(71 + 7 * w.val) + ((8 + k.val) - 8), by omega⟩ :=
      Fin.ext (by dsimp [zWire]; omega)
    dsimp only [ssaAxisZbad7]
    rw [hzk, hsO (8 + k.val) (by omega) (by omega),
      ← simdRun_testBit_eq 256 8 15 r (8 + k.val) s2AxisZbad7Ops (by decide) hr_lt (by omega)
        (s2AxisZbad7_meta w).1 (by rw [(s2AxisZbad7_meta w).2.1])]
    have hk_eq := (nat_beq_iff _ _).mp ((allBelow_iff 6 _).mp hZ k.val k.isLt)
    rw [hk_eq, testBit_packPredLoop_zero _ 256 r hr_lt, hr_land]
  · have hbw : badWire w = ⟨(71 + 7 * w.val) + (14 - 8), by omega⟩ := rfl
    dsimp only [ssaAxisZbad7]
    rw [hbw, hsO 14 (by decide) (by decide),
      ← simdRun_testBit_eq 256 8 15 r 14 s2AxisZbad7Ops (by decide) hr_lt (by decide)
        (s2AxisZbad7_meta w).1 (by rw [(s2AxisZbad7_meta w).2.1]),
      (nat_beq_iff _ _).mp hBad, testBit_packPredLoop_zero _ 256 r hr_lt,
      hr_land, fastBitSmall_eq_testBit, hr_b7, zPref_five_eq_zero hm7]
/-- Helper `inVComb7List` for compact `165`-wire Slot-3 state preparation. -/
def inVComb7List : List ℕ :=
  [49, (mtWire 0 6).val, (mtWire 1 6).val, (mtWire 2 6).val, 77, 84, 91]
/-- Helper `inVComb7` for compact `165`-wire Slot-3 state preparation. -/
def inVComb7 : Fin 7 → Wire 198 := fun i ↦
  ⟨getNatAt inVComb7List i.val, by revert i; decide⟩
theorem inVComb7_inj : Function.Injective inVComb7 := by
  intro i j; revert i j; decide
theorem inVComb7_lt : ∀ i, (inVComb7 i).val < 92 := by
  decide
theorem s2ValidComb6_meta :
    microValid 7 s2ValidComb6Ops = true ∧ microAllocs s2ValidComb6Ops = 6 ∧ 92 + 6 = 98 := by
  decide
/-- Helper `ssaValidComb6` for compact `165`-wire Slot-3 state preparation. -/
def ssaValidComb6 : SsaProg 198 92 98 :=
  ssaMicro inVComb7 inVComb7_inj 92 98 6 inVComb7_lt s2ValidComb6Ops s2ValidComb6_meta (by decide)
/-- Helper `checkVComb6Cert` for compact `165`-wire Slot-3 state preparation. -/
def checkVComb6Cert : Bool :=
  PTree.withVal (simdRun 128 7 s2ValidComb6Ops) fun t ↦
    allBelow 7 (fun i ↦ Nat.beq (pget 0 8 t i) (colMaskFast 128 i)) &&
    Nat.beq (pget 0 8 t 12)
      (packPredLoop (fun r ↦
        (Bool.not (fastBitSmall r 0)) &&
        (fastBitSmall r 1 || fastBitSmall r 2 || fastBitSmall r 3) &&
        (Bool.not (fastBitSmall r 4)) && (Bool.not (fastBitSmall r 5)) &&
          (Bool.not (fastBitSmall r 6))) 128 0 1 0)
theorem checkVComb6Cert_true : checkVComb6Cert = true := by decide +kernel
/-- Helper `ssaStage3Valid27` for compact `165`-wire Slot-3 state preparation. -/
def ssaStage3Valid27 : SsaProg 198 71 98 :=
  (ssaAxisZbad7 0).append ((ssaAxisZbad7 1).append ((ssaAxisZbad7 2).append ssaValidComb6))
theorem ssaStage3Valid27_countAnd : ssaStage3Valid27.countAnd = 27 := by
  have hc : ∀ w : Fin 3, (ssaAxisZbad7 w).countAnd = 7 := fun w ↦
    (ssaMicro_spec (inZbad8 w) (inZbad8_inj w) _ _ 7 (inZbad8_lt w)
      s2AxisZbad7Ops (s2AxisZbad7_meta w) (by revert w; decide)).1
  have hcV : ssaValidComb6.countAnd = 6 := (ssaMicro_spec inVComb7 inVComb7_inj 92 98 6
      inVComb7_lt s2ValidComb6Ops s2ValidComb6_meta (by decide)).1
  dsimp only [ssaStage3Valid27]
  rw [SsaProg.append_countAnd, SsaProg.append_countAnd, SsaProg.append_countAnd,
    hc 0, hc 1, hc 2, hcV]
/-- Helper `validWire` for compact `165`-wire Slot-3 state preparation. -/
def validWire : Wire 198 := ⟨97, by decide⟩
theorem signBit3_eq_testBit :
    ∀ (s3 : Fin 8) (w : Fin 3), s3.val.testBit w.val = decide (signBit3 s3 w = 1) := by
  decide
theorem ssaStage3Valid27_spec (u22 : Fin 4194304) (s3 : Fin 8) (β : BitAssignment 198)
    (hcl : ∀ q : Wire 198, 71 ≤ q.val → β q = 0)
    (hz7 : β z7Wire = b2z (decide (u22.val / 32768 = 0)))
    (hmt : ∀ (w : Fin 3) (b : Fin 7), β (mtWire w b) = b2z ((shiftedMag3 u22 w).testBit b.val))
    (hs3 : ∀ w : Fin 3, β ⟨22 + w.val, by omega⟩ = b2z (s3.val.testBit w.val)) :
    let δ := ssaStage3Valid27.eval β
    ssaStage3Valid27.countAnd = 27 ∧
    (∀ q : Wire 198, 98 ≤ q.val → δ q = 0) ∧
    (∀ q : Wire 198, q.val < 71 → δ q = β q) ∧
    (∀ (w : Fin 3) (k : Fin 6), δ (zWire w k) = b2z (zPref (shiftedMag3 u22 w) k.val)) ∧
    δ validWire = b2z (validShellNu3 u22 s3) := by
  dsimp only
  obtain ⟨hc0, hcl0, hp0, hz0, hb0⟩ := ssaAxisZbad7_spec 0 (shiftedMag3 u22 0)
    (shiftedMag3_lt_128 u22 0) (s3.val.testBit 0) β hcl (hmt 0) (hs3 0)
  let β₁ := (ssaAxisZbad7 0).eval β
  obtain ⟨hc1, hcl1, hp1, hz1, hb1⟩ := ssaAxisZbad7_spec 1 (shiftedMag3 u22 1)
    (shiftedMag3_lt_128 u22 1) (s3.val.testBit 1) β₁ hcl0
    (fun b ↦ (hp0 (mtWire 1 b) (by revert b; decide)).trans (hmt 1 b))
    ((hp0 ⟨23, by decide⟩ (by decide)).trans (hs3 1))
  let β₂ := (ssaAxisZbad7 1).eval β₁
  obtain ⟨hc2, hcl2, hp2, hz2, hb2⟩ := ssaAxisZbad7_spec 2 (shiftedMag3 u22 2)
    (shiftedMag3_lt_128 u22 2) (s3.val.testBit 2) β₂ hcl1
    (fun b ↦ (hp1 (mtWire 2 b) (by revert b; decide)).trans
      ((hp0 (mtWire 2 b) (by revert b; decide)).trans (hmt 2 b)))
    ((hp1 ⟨24, by decide⟩ (by decide)).trans ((hp0 ⟨24, by decide⟩ (by decide)).trans (hs3 2)))
  let β₃ := (ssaAxisZbad7 2).eval β₂
  let r := bitsVal (fun i ↦ β₃ (inVComb7 i))
  obtain ⟨hcV, hEvV⟩ := ssaMicro_spec inVComb7 inVComb7_inj 92 98 6 inVComb7_lt
    s2ValidComb6Ops s2ValidComb6_meta (by decide)
  obtain ⟨hclV, hpV, hsV⟩ := hEvV β₃ hcl2
  have hr_lt : r < 128 := bitsVal_lt_two_pow _
  have hcert := checkVComb6Cert_true
  dsimp only [checkVComb6Cert] at hcert
  rw [PTree.withVal_eq] at hcert
  obtain ⟨hInV, hOutV⟩ := Bool.and_eq_true_iff.mp hcert
  have hrestV : ∀ i < 7,
      getBoolAt (evalMicroList 7 s2ValidComb6Ops (initBoolList 7 13 r)) i = r.testBit i := by
    intro i hi
    have hi_eq := (nat_beq_iff _ _).mp ((allBelow_iff 7 _).mp hInV i hi)
    rw [← simdRun_testBit_eq 128 7 13 r i s2ValidComb6Ops (by decide) hr_lt (by omega)
      s2ValidComb6_meta.1 (by rw [s2ValidComb6_meta.2.1]),
      hi_eq, testBit_colMaskFast, decide_eq_true hr_lt]; simp
  have hp_all : ∀ q : Wire 198, q.val < 92 → ssaValidComb6.eval β₃ q = β₃ q := hpV hrestV
  have h30 : ∀ q : Wire 198, q.val < 71 → β₃ q = β q := fun q hq ↦
    (hp2 q (by omega)).trans ((hp1 q (by omega)).trans (hp0 q hq))
  dsimp only [ssaStage3Valid27]
  simp only [SsaProg.append_eval]
  refine ⟨ssaStage3Valid27_countAnd, hclV, fun q hq ↦ (hp_all q (by omega)).trans (h30 q hq),
    fun w k ↦ ?_, ?_⟩
  · rw [hp_all (zWire w k) (by dsimp [zWire]; omega)]
    fin_cases w
    · exact (hp2 (zWire 0 k) (by dsimp [zWire]; omega)).trans
        ((hp1 (zWire 0 k) (by dsimp [zWire]; omega)).trans (hz0 k))
    · exact (hp2 (zWire 1 k) (by dsimp [zWire]; omega)).trans (hz1 k)
    · exact hz2 k
  · dsimp only [ssaValidComb6]
    rw [show validWire = ⟨92 + (12 - 7), by decide⟩ from rfl, hsV 12 (by decide) (by decide),
      ← simdRun_testBit_eq 128 7 13 r 12 s2ValidComb6Ops (by decide) hr_lt (by decide)
        s2ValidComb6_meta.1 (by rw [s2ValidComb6_meta.2.1]),
      (nat_beq_iff _ _).mp hOutV, testBit_packPredLoop_zero _ 128 r hr_lt]
    simp only [fastBitSmall_eq_testBit]
    have htb_in : ∀ (i : Fin 7) (b : Bool), β₃ (inVComb7 i) = b2z b → r.testBit i.val = b := by
      intro i b hb; rw [bitsVal_testBit_eq (fun j ↦ β₃ (inVComb7 j)) i, hb]; cases b <;> decide
    have hr0 : r.testBit 0 = decide (u22.val / 32768 = 0) :=
      htb_in 0 _ ((h30 z7Wire (by decide)).trans hz7)
    have hr1 : r.testBit 1 = (shiftedMag3 u22 0).testBit 6 :=
      htb_in 1 _ ((h30 (mtWire 0 6) (by decide)).trans (hmt 0 6))
    have hr2 : r.testBit 2 = (shiftedMag3 u22 1).testBit 6 :=
      htb_in 2 _ ((h30 (mtWire 1 6) (by decide)).trans (hmt 1 6))
    have hr3 : r.testBit 3 = (shiftedMag3 u22 2).testBit 6 :=
      htb_in 3 _ ((h30 (mtWire 2 6) (by decide)).trans (hmt 2 6))
    have hr4 : r.testBit 4 = (decide (shiftedMag3 u22 0 = 0) && decide (signBit3 s3 0 = 1)) := by
      rw [← signBit3_eq_testBit s3 0]
      exact htb_in 4 _ ((hp2 (badWire 0) (by decide)).trans ((hp1 (badWire 0) (by decide)).trans
        hb0))
    have hr5 : r.testBit 5 = (decide (shiftedMag3 u22 1 = 0) && decide (signBit3 s3 1 = 1)) := by
      rw [← signBit3_eq_testBit s3 1]; exact htb_in 5 _ ((hp2 (badWire 1) (by decide)).trans hb1)
    have hr6 : r.testBit 6 = (decide (shiftedMag3 u22 2 = 0) && decide (signBit3 s3 2 = 1)) := by
      rw [← signBit3_eq_testBit s3 2]; exact htb_in 6 _ hb2
    have hnot0 : Bool.not (decide (u22.val / 32768 = 0)) = decide (0 < u22.val / 32768) := by
      by_cases h0 : u22.val / 32768 = 0 <;> simp [h0, Nat.pos_of_ne_zero]
    rw [hr0, hnot0, hr1, hr2, hr3, hr4, hr5, hr6, validShellNu3_eq_shifted u22 s3]
attribute [local irreducible] ssaStage3Valid27
/-- Helper `ZpCsaOp` for compact `165`-wire Slot-3 state preparation. -/
inductive ZpCsaOp where
  | xW : ℕ → ZpCsaOp
  | cnotW : ℕ → ℕ → ZpCsaOp
  | pushWt : ℕ → ℕ → ZpCsaOp
  | fa : ℕ → ℕ → ℕ → ℕ → ZpCsaOp
  | ha : ℕ → ℕ → ℕ → ZpCsaOp
/-- Helper `csa100Ops` for compact `165`-wire Slot-3 state preparation. -/
def csa100Ops : List ZpCsaOp := [
  .cnotW 0 7, .cnotW 1 7, .cnotW 2 7, .pushWt 7 2, .cnotW 13 20, .cnotW 14 20, .cnotW 15 20,
    .pushWt 20 2,
  .cnotW 26 33, .cnotW 27 33, .cnotW 28 33, .pushWt 33 2, .xW 8, .cnotW 3 8, .pushWt 8 3, .xW 9,
  .cnotW 4 9, .pushWt 9 4, .pushWt 10 5, .xW 21, .cnotW 16 21, .pushWt 21 3, .xW 22, .cnotW 17 22,
  .pushWt 22 4, .xW 23, .cnotW 18 23, .pushWt 23 5, .xW 24, .cnotW 19 24, .pushWt 24 6,
    .pushWt 25 7,
  .xW 34, .cnotW 29 34, .pushWt 34 3, .xW 35, .cnotW 30 35, .pushWt 35 4, .xW 36, .cnotW 31 36,
  .pushWt 36 5, .xW 37, .cnotW 32 37, .pushWt 37 6, .xW 2, .cnotW 1 2, .pushWt 2 2, .xW 15,
  .cnotW 14 15, .pushWt 15 2, .xW 28, .cnotW 27 28, .pushWt 28 2, .xW 5, .pushWt 5 5, .xW 6,
  .pushWt 6 6, .fa 2 2 41 15, .fa 2 28 7 20, .fa 5 5 44 10, .fa 6 6 45 24, .xW 6, .xW 5,
    .cnotW 27 28,
  .xW 28, .cnotW 14 15, .xW 15, .cnotW 1 2, .xW 2, .pushWt 0 0, .pushWt 0 7, .pushWt 1 8,
  .pushWt 2 9, .pushWt 3 10, .pushWt 4 11, .pushWt 5 12, .pushWt 6 13, .pushWt 13 0, .pushWt 13 7,
    .pushWt 14 8,
  .pushWt 15 9, .pushWt 16 10, .pushWt 17 11, .pushWt 18 12, .pushWt 19 13, .pushWt 26 0,
    .pushWt 26 7, .pushWt 27 8,
  .pushWt 28 9, .pushWt 29 10, .pushWt 30 11, .pushWt 31 12, .pushWt 32 13, .fa 0 0 39 13,
    .fa 7 0 46 13, .fa 7 26 25 58,
  .fa 8 1 47 14, .fa 8 27 60 61, .fa 9 2 48 15, .fa 9 28 62 63, .fa 10 3 49 16, .fa 10 29 64 65,
    .fa 11 4 50 17, .fa 11 30 66 67,
  .fa 12 5 51 18, .fa 12 31 68 69, .fa 13 6 52 19, .fa 13 32 70 71, .ha 0 26 39, .xW 6, .cnotW 6 0,
    .cnotW 6 1,
  .cnotW 6 2, .cnotW 6 3, .cnotW 6 4, .cnotW 6 5, .xW 6, .pushWt 0 6, .pushWt 1 7, .pushWt 2 8,
  .pushWt 3 9, .pushWt 4 10, .pushWt 5 11, .xW 19, .cnotW 19 13, .cnotW 19 14, .cnotW 19 15,
    .cnotW 19 16,
  .cnotW 19 17, .cnotW 19 18, .xW 19, .pushWt 13 6, .pushWt 14 7, .pushWt 15 8, .pushWt 16 9,
    .pushWt 17 10,
  .pushWt 18 11, .xW 32, .cnotW 32 26, .cnotW 32 27, .cnotW 32 28, .cnotW 32 29, .cnotW 32 30,
    .cnotW 32 31,
  .xW 32, .pushWt 26 6, .pushWt 27 7, .pushWt 28 8, .pushWt 29 9, .pushWt 30 10, .pushWt 31 11,
    .fa 6 0 37 13,
  .fa 6 26 57 45, .fa 7 1 46 14, .fa 7 27 25 75, .fa 8 2 47 15, .fa 8 28 60 77, .fa 9 3 48 16,
    .fa 9 29 62 79, .fa 10 4 49 17,
  .fa 10 30 64 81, .fa 11 5 50 18, .fa 11 31 66 83, .xW 5, .cnotW 5 0, .cnotW 5 1, .cnotW 5 2,
    .cnotW 5 3,
  .cnotW 5 4, .xW 5, .pushWt 0 5, .pushWt 1 6, .pushWt 2 7, .pushWt 3 8, .pushWt 4 9, .xW 18,
  .cnotW 18 13, .cnotW 18 14, .cnotW 18 15, .cnotW 18 16, .cnotW 18 17, .xW 18, .pushWt 13 5,
    .pushWt 14 6,
  .pushWt 15 7, .pushWt 16 8, .pushWt 17 9, .xW 31, .cnotW 31 26, .cnotW 31 27, .cnotW 31 28,
    .cnotW 31 29,
  .cnotW 31 30, .xW 31, .pushWt 26 5, .pushWt 27 6, .pushWt 28 7, .pushWt 29 8, .pushWt 30 9,
    .fa 5 0 23 13,
  .fa 5 26 36 44, .fa 6 1 37 14, .fa 6 27 57 87, .fa 7 2 76 15, .fa 7 28 46 25, .fa 8 3 78 16,
    .fa 8 29 47 60, .fa 9 4 80 17,
  .fa 9 30 48 62, .xW 4, .cnotW 4 0, .cnotW 4 1, .cnotW 4 2, .cnotW 4 3, .xW 4, .pushWt 0 4,
  .pushWt 1 5, .pushWt 2 6, .pushWt 3 7, .xW 17, .cnotW 17 13, .cnotW 17 14, .cnotW 17 15,
    .cnotW 17 16,
  .xW 17, .pushWt 13 4, .pushWt 14 5, .pushWt 15 6, .pushWt 16 7, .xW 30, .cnotW 30 26,
    .cnotW 30 27,
  .cnotW 30 28, .cnotW 30 29, .xW 30, .cnotW 38 29, .pushWt 26 4, .pushWt 27 5, .pushWt 28 6,
    .pushWt 29 7,
  .fa 4 0 43 13, .fa 4 26 9 22, .fa 5 1 23 14, .fa 5 27 36 97, .fa 6 2 88 15, .fa 6 28 37 57,
    .fa 7 3 89 16, .fa 7 29 90 76,
  .cnotW 38 29, .pushWt 38 8, .xW 3, .cnotW 3 0, .cnotW 3 1, .cnotW 3 2, .xW 3, .pushWt 0 3,
  .pushWt 1 4, .pushWt 2 5, .xW 16, .cnotW 16 13, .cnotW 16 14, .cnotW 16 15, .xW 16, .pushWt 13 3,
  .pushWt 14 4, .pushWt 15 5, .xW 29, .cnotW 29 26, .cnotW 29 27, .cnotW 29 28, .xW 29,
    .pushWt 26 3,
  .pushWt 27 4, .pushWt 28 5, .fa 3 0 42 13, .fa 3 26 8 21, .fa 4 1 35 14, .fa 4 27 43 9,
    .fa 5 2 98 15, .fa 5 28 23 36,
  .fa 1 59 40 74, .fa 2 41 33 7, .ha 2 33 111, .fa 3 55 34 56, .fa 3 8 42 112, .fa 3 34 113 42,
    .fa 4 106 105 35, .fa 4 114 43 115,
  .fa 4 105 116 43, .fa 5 108 107 98, .fa 5 117 23 118, .fa 5 107 119 23, .fa 6 100 99 88,
    .fa 6 109 37 110, .fa 6 121 120 122, .fa 6 37 99 120,
  .fa 7 101 46 102, .fa 7 90 89 123, .fa 7 125 124 126, .fa 7 89 46 124, .fa 8 92 91 78,
    .fa 8 103 47 104, .fa 8 127 38 128, .fa 8 130 129 91,
  .fa 8 38 47 129, .fa 9 94 93 80, .fa 9 131 48 132, .fa 9 134 133 135, .fa 9 48 93 133,
    .fa 10 49 82 64, .fa 10 96 95 136, .fa 10 138 137 139,
  .fa 10 95 82 137, .fa 11 50 84 66, .fa 11 141 140 142, .fa 11 84 143 140, .fa 12 68 51 85,
    .fa 12 144 86 145, .fa 12 51 146 86, .fa 13 70 52 147,
  .fa 13 149 148 52, .fa 14 72 53 73, .fa 14 151 150 53, .fa 15 152 54 153
]
/-- End scratch-cursor index after executing `ZpCsaOp` list. -/
@[reducible] def csaEnd : ℕ → List ZpCsaOp → ℕ
  | c, [] => c
  | c, .xW _ :: rest => csaEnd c rest
  | c, .cnotW _ _ :: rest => csaEnd c rest
  | c, .pushWt _ _ :: rest => csaEnd c rest
  | c, .fa _ _ _ _ :: rest => csaEnd (c + 1) rest
  | c, .ha _ _ _ :: rest => csaEnd (c + 1) rest
/-- Helper `csaAllocs` for compact `165`-wire Slot-3 state preparation. -/
def csaAllocs : List ZpCsaOp → ℕ
  | [] => 0
  | .xW _ :: rest => csaAllocs rest
  | .cnotW _ _ :: rest => csaAllocs rest
  | .pushWt _ _ :: rest => csaAllocs rest
  | .fa _ _ _ _ :: rest => 1 + csaAllocs rest
  | .ha _ _ _ :: rest => 1 + csaAllocs rest
theorem csaEnd_eq_add : ∀ (ops : List ZpCsaOp) (c : ℕ),
    csaEnd c ops = c + csaAllocs ops
  | [], c => by simp [csaEnd, csaAllocs]
  | .xW _ :: rest, c => csaEnd_eq_add rest c
  | .cnotW _ _ :: rest, c => csaEnd_eq_add rest c
  | .pushWt _ _ :: rest, c => csaEnd_eq_add rest c
  | .fa _ _ _ _ :: rest, c => by
      dsimp only [csaEnd, csaAllocs]
      rw [csaEnd_eq_add rest (c + 1)]; omega
  | .ha _ _ _ :: rest, c => by
      dsimp only [csaEnd, csaAllocs]
      rw [csaEnd_eq_add rest (c + 1)]; omega
/-- Helper `csaValid` for compact `165`-wire Slot-3 state preparation. -/
def csaValid : ℕ → List ZpCsaOp → Bool
  | _, [] => true
  | top, .xW s :: rest => decide (s < 39) && csaValid top rest
  | top, .cnotW sc st :: rest =>
      decide (sc < 39) && decide (st < 39) && decide (sc ≠ st) && csaValid top rest
  | top, .pushWt s col :: rest =>
      decide (s < 39) && decide (col < 16) && csaValid top rest
  | top, .fa col a b cin :: rest =>
      decide (col < 16) && decide (a < top) && decide (b < top) && decide (cin < top) &&
      decide (a ≠ b) && decide (a ≠ cin) && decide (b ≠ cin) && csaValid (top + 1) rest
  | top, .ha col a c :: rest =>
      decide (col < 16) && decide (a < top) && decide (c < top) && decide (a ≠ c) &&
      csaValid (top + 1) rest
theorem csaValid_xW {top s : ℕ} {rest : List ZpCsaOp}
    (hv : csaValid top (.xW s :: rest) = true) : s < 39 ∧ csaValid top rest = true := by
  simpa [csaValid, Bool.and_eq_true, decide_eq_true_eq] using hv
theorem csaValid_cnotW {top sc st : ℕ} {rest : List ZpCsaOp}
    (hv : csaValid top (.cnotW sc st :: rest) = true) :
    sc < 39 ∧ st < 39 ∧ sc ≠ st ∧ csaValid top rest = true := by
  simpa [csaValid, Bool.and_eq_true, decide_eq_true_eq, and_assoc] using hv
theorem csaValid_pushWt {top s col : ℕ} {rest : List ZpCsaOp}
    (hv : csaValid top (.pushWt s col :: rest) = true) :
    s < 39 ∧ col < 16 ∧ csaValid top rest = true := by
  simpa [csaValid, Bool.and_eq_true, decide_eq_true_eq, and_assoc] using hv
theorem csaValid_fa {top col a b cin : ℕ} {rest : List ZpCsaOp}
    (hv : csaValid top (.fa col a b cin :: rest) = true) : col < 16 ∧ a < top ∧ b < top ∧ cin
    < top ∧ a ≠ b ∧ a ≠ cin ∧ b ≠ cin ∧ csaValid (top + 1) rest = true := by
  simpa [csaValid, Bool.and_eq_true, decide_eq_true_eq, and_assoc] using hv
theorem csaValid_ha {top col a c : ℕ} {rest : List ZpCsaOp}
    (hv : csaValid top (.ha col a c :: rest) = true) :
    col < 16 ∧ a < top ∧ c < top ∧ a ≠ c ∧ csaValid (top + 1) rest = true := by
  simpa [csaValid, Bool.and_eq_true, decide_eq_true_eq, and_assoc] using hv
/-- Helper `inCsa55List` for compact `165`-wire Slot-3 state preparation. -/
def inCsa55List : List ℕ := [(mtWire 0 0).val, (mtWire 0 1).val, (mtWire 0 2).val, (mtWire 0
    3).val, (mtWire 0 4).val, (mtWire 0 5).val, (mtWire 0 6).val, (zWire 0 0).val, (zWire 0
    1).val, (zWire 0 2).val, (zWire 0 3).val, (zWire 0 4).val, (zWire 0 5).val, (mtWire 1
    0).val, (mtWire 1 1).val, (mtWire 1 2).val, (mtWire 1 3).val, (mtWire 1 4).val, (mtWire 1
    5).val, (mtWire 1 6).val, (zWire 1 0).val, (zWire 1 1).val, (zWire 1 2).val, (zWire 1
    3).val, (zWire 1 4).val, (zWire 1 5).val, (mtWire 2 0).val, (mtWire 2 1).val, (mtWire 2
    2).val, (mtWire 2 3).val, (mtWire 2 4).val, (mtWire 2 5).val, (mtWire 2 6).val, (zWire 2
    0).val, (zWire 2 1).val, (zWire 2 2).val, (zWire 2 3).val, (zWire 2 4).val, (zWire 2
    5).val, (kcWire 0).val, (kcWire 1).val, (kcWire 2).val, (kcWire 3).val, (kcWire 4).val,
    (kcWire 5).val, (kcWire 6).val, (kcWire 7).val, (kcWire 8).val, (kcWire 9).val, (kcWire
    10).val, (kcWire 11).val, (kcWire 12).val, (kcWire 13).val, (kcWire 14).val, (kcWire
    15).val]
/-- Helper `inCsa55` for compact `165`-wire Slot-3 state preparation. -/
def inCsa55 : Fin 55 → Wire 198 := fun i ↦
  ⟨getNatAt inCsa55List i.val, by revert i; decide⟩
theorem inCsa55_inj : Function.Injective inCsa55 := by
  intro i j; revert i j; decide
theorem inCsa55_lt97 : ∀ i : Fin 55, (inCsa55 i).val < 97 := by
  decide
theorem inCsa55_lt : ∀ i : Fin 55, (inCsa55 i).val < 98 :=
  fun i ↦ Nat.lt_trans (inCsa55_lt97 i) (by decide)
theorem inPlaceFA_val (x y c : ZMod 2) :
    (x + y + c).val + 2 * ((x + c) * (y + c) + c).val = x.val + y.val + c.val := by
  rcases bit_cases x with rfl | rfl <;>
    rcases bit_cases y with rfl | rfl <;>
    rcases bit_cases c with rfl | rfl <;> decide
theorem inPlaceHA_val (x y : ZMod 2) : (x + y).val + 2 * (x * y).val = x.val + y.val := by
  rcases bit_cases x with rfl | rfl <;>
    rcases bit_cases y with rfl | rfl <;> decide
/-- Helper `ssaFaStep` for compact `165`-wire Slot-3 state preparation. -/
def ssaFaStep {cur endCur : ℕ} (hcur : cur < 198) (wA wB wCin : Wire 198) (hab : wA ≠ wB)
    (hac : wA ≠ wCin) (hbc : wB ≠ wCin) (ha : wA.val < cur) (hb : wB.val < cur)
    (hc : wCin.val < cur) (rest : SsaProg 198 (cur + 1) endCur) : SsaProg 198 cur endCur :=
  have hc_lt : wCin.val < cur + 1 := by omega
  have ha_lt : wA.val < cur + 1 := by omega
  have hb_lt : wB.val < cur + 1 := by omega
  have hc_ne_out : wCin ≠ ⟨cur, hcur⟩ := wire_ne_of_lt hc
  .cnot wCin wA hac.symm hc ha
    (.cnot wCin wB hbc.symm hc hb
      (.andClean hcur wA wB hab ha hb
        (.cnot wCin wA hac.symm hc_lt ha_lt
          (.cnot wA wB hab ha_lt hb_lt
            (.cnot wCin ⟨cur, hcur⟩ hc_ne_out hc_lt (by dsimp; omega) rest)))))
theorem ssaFaStep_countAnd {cur endCur : ℕ} (hcur : cur < 198) (wA wB wCin : Wire 198)
    (hab : wA ≠ wB) (hac : wA ≠ wCin) (hbc : wB ≠ wCin) (ha : wA.val < cur)
    (hb : wB.val < cur) (hc : wCin.val < cur) (rest : SsaProg 198 (cur + 1) endCur) :
    (ssaFaStep hcur wA wB wCin hab hac hbc ha hb hc rest).countAnd = 1 + rest.countAnd := by
  dsimp only [ssaFaStep]
  simp only [SsaProg.countAnd_cnot, SsaProg.countAnd_andClean]
theorem ssaFaStep_eval {cur endCur : ℕ} (hcur : cur < 198) (wA wB wCin : Wire 198)
    (hab : wA ≠ wB) (hac : wA ≠ wCin) (hbc : wB ≠ wCin) (ha : wA.val < cur)
    (hb : wB.val < cur) (hc : wCin.val < cur) (rest : SsaProg 198 (cur + 1) endCur)
    (β : BitAssignment 198) (h0 : β ⟨cur, hcur⟩ = 0) : ∃ β' : BitAssignment 198,
    (ssaFaStep hcur wA wB wCin hab hac hbc ha hb hc rest).eval β = rest.eval β' ∧ β' wB = β wA
    + β wB + β wCin ∧ β' ⟨cur, hcur⟩ = (β wA + β wCin) * (β wB + β wCin) + β wCin ∧
    (∀ q : Wire 198, q ≠ wB → q ≠ ⟨cur, hcur⟩ → β' q = β q) := by
  have ha_out : wA ≠ ⟨cur, hcur⟩ := wire_ne_of_lt ha
  have hb_out : wB ≠ ⟨cur, hcur⟩ := wire_ne_of_lt hb
  have hc_out : wCin ≠ ⟨cur, hcur⟩ := wire_ne_of_lt hc
  dsimp only [ssaFaStep]
  simp only [SsaProg.eval_cnot, SsaProg.eval_andClean]
  refine ⟨_, rfl, ?_, ?_, fun q hqb hqo ↦ ?_⟩
  · simp only [Function.update_apply, hab, hab.symm, hac.symm, hbc.symm,
      ha_out, ha_out.symm, hb_out, hb_out.symm, hc_out, ↓reduceIte]
    rcases bit_cases (β wA) with hA | hA <;>
      rcases bit_cases (β wB) with hB | hB <;>
      rcases bit_cases (β wCin) with hC | hC <;> rw [hA, hB, hC] <;> decide
  · simp only [Function.update_apply, hab, hab.symm, hac.symm, hbc.symm,
      ha_out, ha_out.symm, hb_out, hb_out.symm, hc_out, h0, ↓reduceIte]
    rcases bit_cases (β wA) with hA | hA <;>
      rcases bit_cases (β wB) with hB | hB <;>
      rcases bit_cases (β wCin) with hC | hC <;> rw [hA, hB, hC] <;> decide
  · by_cases hqa : q = wA
    · subst hqa
      simp only [Function.update_apply, hab, hab.symm, hac.symm, hbc.symm,
        ha_out, ha_out.symm, hb_out, hb_out.symm, hc_out, ↓reduceIte]
      rcases bit_cases (β q) with hA | hA <;>
        rcases bit_cases (β wCin) with hC | hC <;> rw [hA, hC] <;> decide
    · simp only [Function.update_apply, hqa, hqb, hqo, ↓reduceIte]
/-- Helper `ssaHaStep` for compact `165`-wire Slot-3 state preparation. -/
def ssaHaStep {cur endCur : ℕ} (hcur : cur < 198) (wA wC : Wire 198) (hac : wA ≠ wC)
    (ha : wA.val < cur) (hc : wC.val < cur) (rest : SsaProg 198 (cur + 1) endCur) : SsaProg
    198 cur endCur :=
  have ha_lt : wA.val < cur + 1 := by omega
  have hc_lt : wC.val < cur + 1 := by omega
  .andClean hcur wA wC hac ha hc (.cnot wA wC hac ha_lt hc_lt rest)
theorem ssaHaStep_countAnd {cur endCur : ℕ} (hcur : cur < 198) (wA wC : Wire 198)
    (hac : wA ≠ wC) (ha : wA.val < cur) (hc : wC.val < cur)
    (rest : SsaProg 198 (cur + 1) endCur) : (ssaHaStep hcur wA wC hac ha hc rest).countAnd = 1
    + rest.countAnd := by
  dsimp only [ssaHaStep]
  simp only [SsaProg.countAnd_andClean, SsaProg.countAnd_cnot]
theorem ssaHaStep_eval {cur endCur : ℕ} (hcur : cur < 198) (wA wC : Wire 198) (hac : wA ≠ wC)
    (ha : wA.val < cur) (hc : wC.val < cur) (rest : SsaProg 198 (cur + 1) endCur)
    (β : BitAssignment 198) (h0 : β ⟨cur, hcur⟩ = 0) : ∃ β' : BitAssignment 198,
    (ssaHaStep hcur wA wC hac ha hc rest).eval β = rest.eval β' ∧ β' wC = β wA + β wC ∧ β'
    ⟨cur, hcur⟩ = β wA * β wC ∧ (∀ q : Wire 198, q ≠ wC → q ≠ ⟨cur, hcur⟩ → β' q = β q) := by
  have ha_out : wA ≠ ⟨cur, hcur⟩ := wire_ne_of_lt ha
  have hc_out : wC ≠ ⟨cur, hcur⟩ := wire_ne_of_lt hc
  dsimp only [ssaHaStep]
  simp only [SsaProg.eval_andClean, SsaProg.eval_cnot]
  refine ⟨_, rfl, ?_, ?_, fun q hqc hqo ↦ ?_⟩
  · simp only [Function.update_apply, ha_out, hc_out, ↓reduceIte]
    ring
  · simp only [Function.update_apply, ha_out, hc_out, hc_out.symm, h0, ↓reduceIte]
    ring
  · simp only [Function.update_apply, hqc, hqo, ↓reduceIte]
/-- Helper `ssaCsaRun` for compact `165`-wire Slot-3 state preparation. -/
def ssaCsaRun :
    (top cur : ℕ) → (hrel : 55 + cur = 98 + top ∧ 55 ≤ top) → (ops : List ZpCsaOp) →
    (hv : csaValid top ops = true) →
    (hM : csaEnd cur ops ≤ 198) →
    SsaProg 198 cur (csaEnd cur ops)
  | _, cur, _, [], _, _ => .done cur
  | top, cur, hrel, .xW s :: rest, hv, hM =>
      have hs39 := (csaValid_xW hv).1
      have hs : s < top := by obtain ⟨_, _⟩ := hrel; omega
      have hM' : csaEnd cur rest ≤ 198 := hM
      have hce : cur ≤ 198 := by have := csaEnd_eq_add rest cur; omega
      let wS := microSlotWire inCsa55 98 s (microSlotBound hrel hs hce)
      .x wS (microSlotWire_val_lt inCsa55 98 inCsa55_lt hrel hs _)
        (ssaCsaRun top cur hrel rest (csaValid_xW hv).2 hM)
  | top, cur, hrel, .cnotW sc st :: rest, hv, hM =>
      have h := csaValid_cnotW hv
      have hsc : sc < top := by obtain ⟨_, _⟩ := hrel; omega
      have hst : st < top := by obtain ⟨_, _⟩ := hrel; omega
      have hM' : csaEnd cur rest ≤ 198 := hM
      have hce : cur ≤ 198 := by have := csaEnd_eq_add rest cur; omega
      let wC := microSlotWire inCsa55 98 sc (microSlotBound hrel hsc hce)
      let wT := microSlotWire inCsa55 98 st (microSlotBound hrel hst hce)
      .cnot wC wT (microSlotWire_ne inCsa55 inCsa55_inj 98 inCsa55_lt h.2.2.1 _ _)
        (microSlotWire_val_lt inCsa55 98 inCsa55_lt hrel hsc _)
        (microSlotWire_val_lt inCsa55 98 inCsa55_lt hrel hst _)
        (ssaCsaRun top cur hrel rest h.2.2.2 hM)
  | top, cur, hrel, .pushWt _ _ :: rest, hv, hM =>
      ssaCsaRun top cur hrel rest (csaValid_pushWt hv).2.2 hM
  | top, cur, hrel, .fa _ a b cin :: rest, hv, hM =>
      have h := csaValid_fa hv
      have hM' : csaEnd (cur + 1) rest ≤ 198 := hM
      have hcur : cur < 198 := by
        have := csaEnd_eq_add rest (cur + 1); omega
      have hce : cur ≤ 198 := Nat.le_of_lt hcur
      let wA := microSlotWire inCsa55 98 a (microSlotBound hrel h.2.1 hce)
      let wB := microSlotWire inCsa55 98 b (microSlotBound hrel h.2.2.1 hce)
      let wCin := microSlotWire inCsa55 98 cin (microSlotBound hrel h.2.2.2.1 hce)
      ssaFaStep hcur wA wB wCin
        (microSlotWire_ne inCsa55 inCsa55_inj 98 inCsa55_lt h.2.2.2.2.1 _ _)
        (microSlotWire_ne inCsa55 inCsa55_inj 98 inCsa55_lt h.2.2.2.2.2.1 _ _)
        (microSlotWire_ne inCsa55 inCsa55_inj 98 inCsa55_lt h.2.2.2.2.2.2.1 _ _)
        (microSlotWire_val_lt inCsa55 98 inCsa55_lt hrel h.2.1 _)
        (microSlotWire_val_lt inCsa55 98 inCsa55_lt hrel h.2.2.1 _)
        (microSlotWire_val_lt inCsa55 98 inCsa55_lt hrel h.2.2.2.1 _)
        (ssaCsaRun (top + 1) (cur + 1)
          ⟨by obtain ⟨_, _⟩ := hrel; omega, by obtain ⟨_, _⟩ := hrel; omega⟩
          rest h.2.2.2.2.2.2.2 hM)
  | top, cur, hrel, .ha _ a c :: rest, hv, hM =>
      have h := csaValid_ha hv
      have hM' : csaEnd (cur + 1) rest ≤ 198 := hM
      have hcur : cur < 198 := by
        have := csaEnd_eq_add rest (cur + 1); omega
      have hce : cur ≤ 198 := Nat.le_of_lt hcur
      let wA := microSlotWire inCsa55 98 a (microSlotBound hrel h.2.1 hce)
      let wC := microSlotWire inCsa55 98 c (microSlotBound hrel h.2.2.1 hce)
      ssaHaStep hcur wA wC
        (microSlotWire_ne inCsa55 inCsa55_inj 98 inCsa55_lt h.2.2.2.1 _ _)
        (microSlotWire_val_lt inCsa55 98 inCsa55_lt hrel h.2.1 _)
        (microSlotWire_val_lt inCsa55 98 inCsa55_lt hrel h.2.2.1 _)
        (ssaCsaRun (top + 1) (cur + 1)
          ⟨by obtain ⟨_, _⟩ := hrel; omega, by obtain ⟨_, _⟩ := hrel; omega⟩ rest h.2.2.2.2 hM)
/-- Helper `CsaSymState` for compact `165`-wire Slot-3 state preparation. -/
structure CsaSymState where
  wt : PTree ℕ
  alive : PTree Bool
  aff : PTree ℕ
  ax0 : List (ℕ × ℕ)
  ax1 : List (ℕ × ℕ)
  ax2 : List (ℕ × ℕ)
/-- Helper `basisBit14` for compact `165`-wire Slot-3 state preparation. -/
def basisBit14 (m i : ℕ) : Bool := if i < 7 then fastBitSmall m i else if i < 13 then zPref m
    (i - 7) else Nat.beq i 13
/-- Helper `evalAff14Loop` for compact `165`-wire Slot-3 state preparation. -/
def evalAff14Loop (m word14 : ℕ) : ℕ → Bool
  | 0 => false
  | i + 1 => xor (evalAff14Loop m word14 i) (fastBitSmall word14 i && basisBit14 m i)
/-- Helper `evalAff14` for compact `165`-wire Slot-3 state preparation. -/
def evalAff14 (m word14 : ℕ) : Bool := evalAff14Loop m word14 14
theorem evalAff14Loop_xor (m w1 w2 : ℕ) :
    ∀ k : ℕ, evalAff14Loop m (Nat.xor w1 w2) k = xor (evalAff14Loop m w1 k) (evalAff14Loop m w2 k)
  | 0 => rfl
  | i + 1 => by
      dsimp only [evalAff14Loop]
      rw [evalAff14Loop_xor m w1 w2 i, fastBitSmall_eq_testBit, fastBitSmall_eq_testBit,
        fastBitSmall_eq_testBit]
      change xor _ (((w1 ^^^ w2).testBit i) && basisBit14 m i) = _
      rw [Nat.testBit_xor]
      have hd : (xor (w1.testBit i) (w2.testBit i) && basisBit14 m i) =
          xor (w1.testBit i && basisBit14 m i) (w2.testBit i && basisBit14 m i) := by
        cases w1.testBit i <;> cases w2.testBit i <;> cases basisBit14 m i <;> rfl
      rw [hd]
      exact bool_xor_four _ _ _ _
theorem evalAff14_xor (m w1 w2 : ℕ) : evalAff14 m (Nat.xor w1 w2) = xor (evalAff14 m w1)
    (evalAff14 m w2) := evalAff14Loop_xor m w1 w2 14
theorem evalAff14_8192 (m : ℕ) : evalAff14 m 8192 = true := by
  have hb : ∀ i < 13, fastBitSmall 8192 i = false := by decide
  have hb13 : fastBitSmall 8192 13 = true := by decide
  have hloop : ∀ k ≤ 13, evalAff14Loop m 8192 k = false := by
    intro k hk
    induction k with
    | zero => rfl
    | succ i ih =>
        dsimp only [evalAff14Loop]
        rw [ih (by omega), hb i (by omega)]
        rfl
  rw [evalAff14, show (14 : ℕ) = 13 + 1 from rfl, evalAff14Loop.eq_2, hloop 13 le_rfl, hb13]
  rfl
theorem evalAff14Loop_pow_gt (m j : ℕ) :
    ∀ k : ℕ, k ≤ j → evalAff14Loop m (2 ^ j) k = false
  | 0, _ => rfl
  | i + 1, hi => by
      dsimp only [evalAff14Loop]
      rw [evalAff14Loop_pow_gt m j i (by omega), fastBitSmall_eq_testBit, testBit_two_pow,
        decide_eq_false (by omega)]; rfl
theorem evalAff14Loop_pow_le (m j : ℕ) :
    ∀ k : ℕ, j < k → evalAff14Loop m (2 ^ j) k = basisBit14 m j
  | 0, hk => absurd hk (Nat.not_lt_zero _)
  | i + 1, hk => by
      dsimp only [evalAff14Loop]
      by_cases hij : i = j
      · subst hij
        rw [evalAff14Loop_pow_gt m i i le_rfl, fastBitSmall_eq_testBit, testBit_two_pow,
          decide_eq_true rfl]; simp
      · rw [evalAff14Loop_pow_le m j i (by omega), fastBitSmall_eq_testBit, testBit_two_pow,
          decide_eq_false hij]; simp
theorem evalAff14_pow_b (m : ℕ) (b : Fin 7) : evalAff14 m (2 ^ b.val) = m.testBit b.val := by
  unfold evalAff14
  rw [evalAff14Loop_pow_le m b.val 14 (by omega)]
  unfold basisBit14
  rw [itePos b.isLt, fastBitSmall_eq_testBit]
theorem evalAff14_pow_z (m : ℕ) (k : Fin 6) :
    evalAff14 m (2 ^ (7 + k.val)) = zPref m k.val := by
  unfold evalAff14
  rw [evalAff14Loop_pow_le m (7 + k.val) 14 (by omega)]
  unfold basisBit14
  rw [iteNeg (by omega), itePos (by omega)]
  congr 1; omega
/-- Helper `evalAxisTerms` for compact `165`-wire Slot-3 state preparation. -/
def evalAxisTerms (m : ℕ) : List (ℕ × ℕ) → ℕ
  | [] => 0
  | (w, word14) :: rest =>
      Bool.casesOn (evalAff14 m word14) 0 w + evalAxisTerms m rest
/-- Helper `pushAxisTerm` for compact `165`-wire Slot-3 state preparation. -/
def pushAxisTerm (ax : ℕ) (term : ℕ × ℕ) (st : CsaSymState) : CsaSymState :=
  if Nat.beq ax 0 then { st with ax0 := term :: st.ax0 }
  else if Nat.beq ax 1 then { st with ax1 := term :: st.ax1 }
  else { st with ax2 := term :: st.ax2 }
/-- Helper `runCsaSym` for compact `165`-wire Slot-3 state preparation. -/
def runCsaSym : ℕ → List ZpCsaOp → CsaSymState → Option CsaSymState
  | _, [], st => some st
  | top, .xW s :: rest, st =>
      if s < 39 && pget false 8 st.alive s && Nat.beq (pget 0 8 st.wt s) 0 then
        PTree.withVal (psetNat 8 st.aff s (Nat.xor (pget 0 8 st.aff s) 8192)) fun aff' ↦
          runCsaSym top rest { st with aff := aff' }
      else none
  | top, .cnotW sc stt :: rest, st =>
      if sc < 39 && stt < 39 && decide (sc ≠ stt) && Nat.beq (sc / 13) (stt / 13) &&
          pget false 8 st.alive sc && pget false 8 st.alive stt &&
          Nat.beq (pget 0 8 st.wt stt) 0 then
        PTree.withVal (psetNat 8 st.aff stt (Nat.xor (pget 0 8 st.aff stt) (pget 0 8 st.aff sc)))
          fun aff' ↦
          runCsaSym top rest { st with aff := aff' }
      else none
  | top, .pushWt s col :: rest, st =>
      if s < 39 && col < 16 && pget false 8 st.alive s then
        let w := pow2Small col
        forceNat (pget 0 8 st.aff s) fun affS ↦
          PTree.withVal (psetNat 8 st.wt s (Nat.add (pget 0 8 st.wt s) w)) fun wt' ↦
            runCsaSym top rest (pushAxisTerm (s / 13) (w, affS) { st with wt := wt' })
      else none
  | top, .fa col a b cin :: rest, st =>
      if top < 155 && col < 16 && a < top && b < top && cin < top &&
          decide (a ≠ b) && decide (a ≠ cin) && decide (b ≠ cin) then
        let w := pow2Small col
        let wa := pget 0 8 st.wt a
        let wb := pget 0 8 st.wt b
        let wc := pget 0 8 st.wt cin
        if Nat.ble w wa && Nat.ble w wc && Nat.beq wb w then
          PTree.withVal (psetNat 8 st.wt a (Nat.sub wa w)) fun wt1 ↦
          PTree.withVal (psetNat 8 wt1 cin (Nat.sub wc w)) fun wt2 ↦
          PTree.withVal (psetNat 8 wt2 top (Nat.add w w)) fun wt3 ↦
          PTree.withVal (pset 8 st.alive b false) fun al1 ↦
            runCsaSym (top + 1) rest { st with wt := wt3, alive := al1 }
        else none
      else none
  | top, .ha col a c :: rest, st =>
      if top < 155 && col < 16 && a < top && c < top && decide (a ≠ c) then
        let w := pow2Small col
        let wa := pget 0 8 st.wt a
        let wc := pget 0 8 st.wt c
        if Nat.ble w wa && Nat.beq wc w then
          PTree.withVal (psetNat 8 st.wt a (Nat.sub wa w)) fun wt1 ↦
          PTree.withVal (psetNat 8 wt1 top (Nat.add w w)) fun wt2 ↦
          PTree.withVal (pset 8 st.alive c false) fun al1 ↦
            runCsaSym (top + 1) rest { st with wt := wt2, alive := al1 }
        else none
      else none
/-- Helper `initKcWtLoop` for compact `165`-wire Slot-3 state preparation. -/
def initKcWtLoop : ℕ → PTree ℕ → PTree ℕ
  | 0, t => t
  | j + 1, t => PTree.withVal (pset 8 t (39 + j) (pow2Small j)) (initKcWtLoop j)
/-- Helper `initAliveLoop` for compact `165`-wire Slot-3 state preparation. -/
def initAliveLoop : ℕ → PTree Bool → PTree Bool
  | 0, t => t
  | s + 1, t => PTree.withVal (pset 8 t s true) (initAliveLoop s)
/-- Helper `initAff14Loop` for compact `165`-wire Slot-3 state preparation. -/
def initAff14Loop : ℕ → PTree ℕ → PTree ℕ
  | 0, t => t
  | s + 1, t => PTree.withVal (pset 8 t s (pow2Small (s % 13))) (initAff14Loop s)
/-- Helper `initCsaSymState` for compact `165`-wire Slot-3 state preparation. -/
def initCsaSymState : CsaSymState :=
  { wt := initKcWtLoop 16 (pconst 0 8)
    alive := initAliveLoop 39 (pconst false 8)
    aff := initAff14Loop 39 (pconst 0 8)
    ax0 := []
    ax1 := []
    ax2 := [] }
/-- Helper `sumWeights` for compact `165`-wire Slot-3 state preparation. -/
def sumWeights (wt : PTree ℕ) : ℕ → ℕ
  | 0 => 0
  | s + 1 => sumWeights wt s + pget 0 8 wt s
/-- Helper `sumFun` for compact `165`-wire Slot-3 state preparation. -/
def sumFun (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => sumFun f n + f n
theorem sumFun_congr {f g : ℕ → ℕ} :
    ∀ (n : ℕ), (∀ i < n, f i = g i) → sumFun f n = sumFun g n
  | 0, _ => rfl
  | n + 1, h => by
      dsimp only [sumFun]
      rw [sumFun_congr n (fun i hi ↦ h i (by omega)), h n (by omega)]
theorem sumFun_point_swap (f g : ℕ → ℕ) :
    ∀ (n k : ℕ), k < n → (∀ i < n, i ≠ k → g i = f i) →
      sumFun g n + f k = sumFun f n + g k
  | 0, _, hk, _ => absurd hk (Nat.not_lt_zero _)
  | n + 1, k, hk, h => by
      dsimp only [sumFun]
      by_cases hkn : k = n
      · subst k
        rw [sumFun_congr n (fun i hi ↦ h i (by omega) (by omega))]
        omega
      · have ih := sumFun_point_swap f g n k (by omega) (fun i hi hne ↦ h i (by omega) hne)
        have hn := h n (by omega) (Ne.symm hkn)
        omega
/-- Helper `slotContrib` for compact `165`-wire Slot-3 state preparation. -/
def slotContrib (wt : PTree ℕ) (β : BitAssignment 198) (s : ℕ) : ℕ :=
  if hs : s < 155 then
    pget 0 8 wt s * (β (microSlotWire inCsa55 98 s (fun _ ↦ by omega))).val
  else 0
theorem sumFun_slotContrib_le_sumWeights (wt : PTree ℕ) (β : BitAssignment 198) :
    ∀ n : ℕ, n ≤ 155 → sumFun (slotContrib wt β) n ≤ sumWeights wt n
  | 0, _ => le_rfl
  | s + 1, hs => by
      dsimp only [sumFun, sumWeights]
      have ih := sumFun_slotContrib_le_sumWeights wt β s (by omega)
      dsimp only [slotContrib]
      rw [ditePos (by omega : s < 155)]
      set b := β (microSlotWire inCsa55 98 s (fun _ ↦ by omega))
      have hb_le : b.val ≤ 1 := by have := b.val_lt; omega
      have hmul : pget 0 8 wt s * b.val ≤ pget 0 8 wt s * 1 := Nat.mul_le_mul_left _ hb_le
      omega
/-- Helper `mAxOf` for compact `165`-wire Slot-3 state preparation. -/
def mAxOf (m0 m1 m2 ax : ℕ) : ℕ := if ax = 0 then m0 else if ax = 1 then m1 else m2
/-- Helper `CsaInv` for compact `165`-wire Slot-3 state preparation. -/
def CsaInv (m0 m1 m2 kc top cur : ℕ) (β : BitAssignment 198) (st : CsaSymState) : Prop :=
  PTree.hasDepth 8 st.wt ∧
  PTree.hasDepth 8 st.alive ∧
  PTree.hasDepth 8 st.aff ∧
  (∀ q : Wire 198, cur ≤ q.val → β q = 0) ∧
  (∀ s, top ≤ s → s < 256 → pget 0 8 st.wt s = 0) ∧
  (∀ s, 39 ≤ s → s < 256 → pget false 8 st.alive s = false) ∧
  (∀ s (hs : s < 39), pget false 8 st.alive s = true →
    β (microSlotWire inCsa55 98 s (fun _ ↦ by omega)) =
      b2z (evalAff14 (mAxOf m0 m1 m2 (s / 13)) (pget 0 8 st.aff s))) ∧
  sumFun (slotContrib st.wt β) top =
    kc + evalAxisTerms m0 st.ax0 + evalAxisTerms m1 st.ax1 + evalAxisTerms m2 st.ax2
theorem initKcWtLoop_spec :
    ∀ (k : ℕ), k ≤ 16 → ∀ (t : PTree ℕ), PTree.hasDepth 8 t →
      PTree.hasDepth 8 (initKcWtLoop k t) ∧
        ∀ s < 256, pget 0 8 (initKcWtLoop k t) s =
          if 39 ≤ s ∧ s < 39 + k then 2 ^ (s - 39) else pget 0 8 t s
  | 0, _, t, ht => ⟨ht, fun s _ ↦ by rw [iteNeg (by omega)]; rfl⟩
  | j + 1, hj, t, ht => by
      dsimp only [initKcWtLoop]; rw [PTree.withVal_eq]
      have h256 : (2 ^ 8 : ℕ) = 256 := by decide
      have ht' : PTree.hasDepth 8 (pset 8 t (39 + j) (pow2Small j)) :=
        pset_hasDepth 8 t ht (39 + j) (by rw [h256]; omega) _
      obtain ⟨hD, hG⟩ := initKcWtLoop_spec j (by omega) _ ht'
      refine ⟨hD, fun s hs ↦ ?_⟩
      rw [hG s hs]
      by_cases hsj : 39 ≤ s ∧ s < 39 + j
      · rw [itePos hsj, itePos (by omega : 39 ≤ s ∧ s < 39 + (j + 1))]
      · rw [iteNeg hsj,
        pget_pset 0 8 t ht (39 + j) (by rw [h256]; omega) s (by rw [h256]; exact hs)]
        by_cases heq : s = 39 + j
        · subst heq
          rw [itePos rfl, itePos (by omega : 39 ≤ 39 + j ∧ 39 + j < 39 + (j + 1)), pow2Small_eq]
          congr 1; omega
        · rw [iteNeg heq, iteNeg (by omega : ¬ (39 ≤ s ∧ s < 39 + (j + 1)))]
theorem initAliveLoop_spec :
    ∀ (k : ℕ), k ≤ 39 → ∀ (t : PTree Bool), PTree.hasDepth 8 t →
      PTree.hasDepth 8 (initAliveLoop k t) ∧
        ∀ s < 256, pget false 8 (initAliveLoop k t) s =
          if s < k then true else pget false 8 t s
  | 0, _, t, ht => ⟨ht, fun s _ ↦ by simp [initAliveLoop]⟩
  | j + 1, hj, t, ht => by
      dsimp only [initAliveLoop]; rw [PTree.withVal_eq]
      have h256 : (2 ^ 8 : ℕ) = 256 := by decide
      have ht' : PTree.hasDepth 8 (pset 8 t j true) :=
        pset_hasDepth 8 t ht j (by rw [h256]; omega) _
      obtain ⟨hD, hG⟩ := initAliveLoop_spec j (by omega) _ ht'
      refine ⟨hD, fun s hs ↦ ?_⟩
      rw [hG s hs]
      by_cases hsj : s < j
      · simp [hsj, show s < j + 1 by omega]
      · simp only [hsj, ↓reduceIte]
        rw [pget_pset false 8 t ht j (by rw [h256]; omega) s (by rw [h256]; exact hs)]
        by_cases heq : s = j
        · subst heq; simp
        · simp [heq, show ¬ (s < j + 1) by omega]
theorem initAff14Loop_spec :
    ∀ (k : ℕ), k ≤ 39 → ∀ (t : PTree ℕ), PTree.hasDepth 8 t →
      PTree.hasDepth 8 (initAff14Loop k t) ∧
        ∀ s < 256, pget 0 8 (initAff14Loop k t) s =
          if s < k then 2 ^ (s % 13) else pget 0 8 t s
  | 0, _, t, ht => ⟨ht, fun s _ ↦ by simp [initAff14Loop]⟩
  | j + 1, hj, t, ht => by
      dsimp only [initAff14Loop]; rw [PTree.withVal_eq]
      have h256 : (2 ^ 8 : ℕ) = 256 := by decide
      have ht' : PTree.hasDepth 8 (pset 8 t j (pow2Small (j % 13))) :=
        pset_hasDepth 8 t ht j (by rw [h256]; omega) _
      obtain ⟨hD, hG⟩ := initAff14Loop_spec j (by omega) _ ht'
      refine ⟨hD, fun s hs ↦ ?_⟩
      rw [hG s hs]
      by_cases hsj : s < j
      · simp [hsj, show s < j + 1 by omega]
      · simp only [hsj, ↓reduceIte]
        rw [pget_pset 0 8 t ht j (by rw [h256]; omega) s (by rw [h256]; exact hs)]
        by_cases heq : s = j
        · subst heq; simp [pow2Small_eq]
        · simp [heq, show ¬ (s < j + 1) by omega]
theorem inCsa55_mt (w : Fin 3) (b : Fin 7) :
    inCsa55 ⟨13 * w.val + b.val, by omega⟩ = mtWire w b := by
  revert w b; decide
theorem inCsa55_z (w : Fin 3) (k : Fin 6) :
    inCsa55 ⟨13 * w.val + 7 + k.val, by omega⟩ = zWire w k := by
  revert w k; decide
theorem inCsa55_kc (j : Fin 16) :
    inCsa55 ⟨39 + j.val, by omega⟩ = kcWire j := by
  revert j; decide
theorem initCsaSymState_inv (m0 m1 m2 kc : ℕ) (hkc_lt : kc < 65536) (β : BitAssignment 198)
    (hcl : ∀ q : Wire 198, 98 ≤ q.val → β q = 0) (hmt : ∀ (w : Fin 3) (b : Fin 7), β (mtWire w
    b) = b2z ((mAxOf m0 m1 m2 w.val).testBit b.val)) (hz : ∀ (w : Fin 3) (k : Fin 6), β (zWire
    w k) = b2z (zPref (mAxOf m0 m1 m2 w.val) k.val))
    (hkc : ∀ j : Fin 16, β (kcWire j) = b2z (kc.testBit j.val)) : CsaInv m0 m1 m2 kc 55 98 β
    initCsaSymState := by
  have h256 : (2 ^ 8 : ℕ) = 256 := by decide
  obtain ⟨hDw, hGw⟩ := initKcWtLoop_spec 16 le_rfl (pconst 0 8) (pconst_hasDepth 0 8)
  obtain ⟨hDal, hGal⟩ := initAliveLoop_spec 39 le_rfl (pconst false 8) (pconst_hasDepth false 8)
  obtain ⟨hPort, hGaf⟩ := initAff14Loop_spec 39 le_rfl (pconst 0 8) (pconst_hasDepth 0 8)
  refine ⟨hDw, hDal, hPort, hcl, fun s hlo hhi ↦ ?_, fun s hlo hhi ↦ ?_, fun s hs _ ↦ ?_, ?_⟩
  · dsimp [initCsaSymState]
    rw [hGw s hhi, iteNeg (by omega), pget_pconst 0 8 s (by rw [h256]; exact hhi)]
  · dsimp [initCsaSymState]
    rw [hGal s hhi, iteNeg (by omega), pget_pconst false 8 s (by rw [h256]; exact hhi)]
  · dsimp [initCsaSymState]
    rw [hGaf s (by omega), itePos hs, microSlotWire_lt_in inCsa55 98 s (by omega)]
    let w : Fin 3 := ⟨s / 13, by omega⟩
    let r := s % 13
    have hsr : 13 * w.val + r = s := Nat.div_add_mod s 13
    by_cases hr7 : r < 7
    · have hin : (⟨s, by omega⟩ : Fin 55) = ⟨13 * w.val + (⟨r, hr7⟩ : Fin 7).val, by omega⟩ :=
        Fin.ext hsr.symm
      rw [hin, inCsa55_mt w ⟨r, hr7⟩, hmt w ⟨r, hr7⟩]
      exact congrArg b2z (evalAff14_pow_b (mAxOf m0 m1 m2 (s / 13)) ⟨r, hr7⟩).symm
    · let k : Fin 6 := ⟨r - 7, by omega⟩
      have hsr' : 13 * w.val + 7 + k.val = s := by dsimp [k]; omega
      have hin : (⟨s, by omega⟩ : Fin 55) = ⟨13 * w.val + 7 + k.val, by omega⟩ := Fin.ext hsr'.symm
      rw [hin, inCsa55_z w k, hz w k]
      have hr_eq : r = 7 + k.val := by dsimp [k]; omega
      rw [show s % 13 = r from rfl, hr_eq]
      exact congrArg b2z (evalAff14_pow_z (mAxOf m0 m1 m2 (s / 13)) k).symm
  · dsimp only [initCsaSymState, evalAxisTerms]
    simp only [Nat.add_zero]
    have hlow39 : ∀ n ≤ 39, sumFun (slotContrib (initKcWtLoop 16 (pconst 0 8)) β) n = 0 := by
      intro n hn
      induction n with
      | zero => rfl
      | succ s ih =>
          dsimp only [sumFun, slotContrib]
          rw [ih (by omega), ditePos (by omega : s < 155),
            hGw s (by omega), iteNeg (by omega), pget_pconst 0 8 s (by rw [h256]; omega),
            zero_mul, zero_add]
    have hkc_sum : ∀ n : ℕ, (hn : n ≤ 16) →
        sumFun (slotContrib (initKcWtLoop 16 (pconst 0 8)) β) (39 + n) =
          ∑ j : Fin n, (β (kcWire ⟨j.val, Nat.lt_of_lt_of_le j.isLt hn⟩)).val * 2 ^ j.val := by
      intro n hn
      induction n with
      | zero => simpa using hlow39 39 le_rfl
      | succ m ih =>
          rw [show 39 + (m + 1) = (39 + m) + 1 by omega]
          dsimp only [sumFun]
          rw [ih (by omega), Fin.sum_univ_castSucc]
          congr 1
          dsimp only [slotContrib]
          rw [ditePos (by omega : 39 + m < 155), hGw (39 + m) (by omega),
            itePos (by omega : 39 ≤ 39 + m ∧ 39 + m < 39 + 16),
            show 39 + m - 39 = m by omega,
            microSlotWire_lt_in inCsa55 98 (39 + m) (by omega)]
          have hin : (⟨39 + m, by omega⟩ : Fin 55) = ⟨39 + (⟨m, hn⟩ : Fin 16).val, by omega⟩ := rfl
          rw [hin, inCsa55_kc ⟨m, hn⟩]
          dsimp [Fin.last]
          ring
    have hsum16 := hkc_sum 16 le_rfl
    have hbv : bitsVal (fun j : Fin 16 ↦ β (kcWire j)) = kc := by
      refine bitsVal_eq_of_testBit _ kc (by omega) fun j ↦ ?_
      rw [hkc j]; cases kc.testBit j.val <;> rfl
    simpa [bitsVal] using hsum16.trans hbv
private theorem csaInv_aff_update {m0 m1 m2 kc top cur : ℕ}
    (hrel : 55 + cur = 98 + top ∧ 55 ≤ top) (hce : cur ≤ 198) (_htop155 : top ≤ 155)
    {β : BitAssignment 198} {st : CsaSymState} (hInv : CsaInv m0 m1 m2 kc top cur β st)
    (tgt : ℕ) (htgt : tgt < top) (hwt0 : pget 0 8 st.wt tgt = 0)
    (vBit : ZMod 2) (vAff : ℕ) (hv : vBit = b2z (evalAff14 (mAxOf m0 m1 m2 (tgt / 13)) vAff)) :
    CsaInv m0 m1 m2 kc top cur
      (Function.update β (microSlotWire inCsa55 98 tgt (microSlotBound hrel htgt hce)) vBit)
      { st with aff := pset 8 st.aff tgt vAff } := by
  have h256 : (2 ^ 8 : ℕ) = 256 := by decide
  obtain ⟨hDw, hDal, hPort, hcl, hwtHi, halHi, hAff, hSum⟩ := hInv
  let wT := microSlotWire inCsa55 98 tgt (microSlotBound hrel htgt hce)
  have hwT_lt : wT.val < cur := microSlotWire_val_lt inCsa55 98 inCsa55_lt hrel htgt _
  refine ⟨hDw, hDal, pset_hasDepth 8 st.aff hPort tgt (by rw [h256]; omega) _,
    fun q hq ↦ ?_, hwtHi, halHi, fun u hu halU ↦ ?_, ?_⟩
  · rw [Function.update_of_ne (wire_ne_of_gt (by omega))]; exact hcl q hq
  · rw [pget_pset 0 8 st.aff hPort tgt (by rw [h256]; omega) u (by rw [h256]; omega)]
    by_cases hut : u = tgt
    · subst hut; simp only [↓reduceIte]
      have hwEq : microSlotWire inCsa55 98 u (fun _ ↦ by omega) = wT := rfl
      rw [hwEq, Function.update_self]; exact hv
    · simp only [hut, ↓reduceIte]
      rw [Function.update_of_ne (microSlotWire_ne inCsa55 inCsa55_inj 98 inCsa55_lt hut _ _)]
      exact hAff u hu halU
  · dsimp only; rw [← hSum]
    refine sumFun_congr top fun u hu ↦ ?_
    dsimp only [slotContrib]
    rw [ditePos (by omega : u < 155), ditePos (by omega : u < 155)]
    by_cases hut : u = tgt
    · subst hut; rw [hwt0, zero_mul, zero_mul]
    · rw [Function.update_of_ne (microSlotWire_ne inCsa55 inCsa55_inj 98 inCsa55_lt hut _ _)]

private theorem csa_wire_ne_of_notin {q : Wire 198} (hq : q.val < 98)
    (hnotin : ∀ i : Fin 55, q ≠ inCsa55 i) (s : ℕ) (hb : 55 ≤ s → 98 + (s - 55) < 198) :
    q ≠ microSlotWire inCsa55 98 s hb := by
  by_cases hs55 : s < 55
  · rw [microSlotWire_lt_in inCsa55 98 s hs55 hb]; exact hnotin ⟨s, hs55⟩
  · rw [microSlotWire_ge_in inCsa55 98 s (by omega) hb]; exact wire_ne_of_lt (by dsimp; omega)

private theorem sumFun_slotContrib_sub {top x v0 w : ℕ} {wt : PTree ℕ} (β : BitAssignment 198)
    (hDw : PTree.hasDepth 8 wt) (hx : x < top) (htop155 : top ≤ 155)
    (hv0 : pget 0 8 wt x = v0) (hw : w ≤ v0) :
    sumFun (slotContrib wt β) top =
      sumFun (slotContrib (pset 8 wt x (v0 - w)) β) top +
      w * (β (microSlotWire inCsa55 98 x (fun _ ↦ by omega))).val := by
  have h256 : (2 ^ 8 : ℕ) = 256 := by decide
  let wX := microSlotWire inCsa55 98 x (fun _ ↦ by omega)
  have hswap := sumFun_point_swap (slotContrib wt β) (slotContrib (pset 8 wt x (v0 - w)) β)
    top x hx fun u _ hne ↦ by
      dsimp [slotContrib]
      rw [pget_pset 0 8 wt hDw x (by rw [h256]; omega) u (by rw [h256]; omega), iteNeg hne]
  have hold : slotContrib wt β x = v0 * (β wX).val := by
    dsimp [slotContrib, wX]; rw [ditePos (by omega : x < 155), hv0]
  have hnew : slotContrib (pset 8 wt x (v0 - w)) β x = (v0 - w) * (β wX).val := by
    dsimp [slotContrib, wX]
    rw [ditePos (by omega : x < 155),
      pget_pset 0 8 wt hDw x (by rw [h256]; omega) x (by rw [h256]; omega), itePos rfl]
  have hsplit : (v0 - w) * (β wX).val + w * (β wX).val = v0 * (β wX).val := by
    rw [← Nat.add_mul, Nat.sub_add_cancel hw]
  rw [hold, hnew] at hswap
  dsimp only [wX] at hswap hsplit ⊢
  omega

private theorem sumFun_slotContrib_carry {top cur mid w : ℕ}
    (hrel : 55 + cur = 98 + top ∧ 55 ≤ top) (hcur : cur < 198) (htop155 : top < 155)
    {wt : PTree ℕ} {β β' : BitAssignment 198} (hDw : PTree.hasDepth 8 wt)
    (hmid : mid < top) (hw_mid : pget 0 8 wt mid = w)
    (hOth : ∀ q : Wire 198,
      q ≠ microSlotWire inCsa55 98 mid (microSlotBound hrel hmid (Nat.le_of_lt hcur)) →
      q ≠ ⟨cur, hcur⟩ → β' q = β q) :
    sumFun (slotContrib (pset 8 wt top (w + w)) β') (top + 1) +
      w * (β (microSlotWire inCsa55 98 mid (microSlotBound hrel hmid (Nat.le_of_lt hcur)))).val =
    sumFun (slotContrib wt β) top +
      w * (β' (microSlotWire inCsa55 98 mid (microSlotBound hrel hmid (Nat.le_of_lt hcur)))).val +
      (w + w) * (β' ⟨cur, hcur⟩).val := by
  have h256 : (2 ^ 8 : ℕ) = 256 := by decide
  let wM := microSlotWire inCsa55 98 mid (microSlotBound hrel hmid (Nat.le_of_lt hcur))
  let cout : Wire 198 := ⟨cur, hcur⟩
  dsimp only [sumFun]
  have htop_c : slotContrib (pset 8 wt top (w + w)) β' top = (w + w) * (β' cout).val := by
    dsimp [slotContrib]
    rw [ditePos htop155,
      pget_pset 0 8 wt hDw top (by rw [h256]; omega) top (by rw [h256]; omega),
      itePos rfl, microSlotWire_ge_in inCsa55 98 top hrel.2,
      show (⟨98 + (top - 55), by omega⟩ : Wire 198) = cout from Fin.ext (by dsimp [cout]; omega)]
  have hcongr : sumFun (slotContrib (pset 8 wt top (w + w)) β') top =
      sumFun (slotContrib wt β') top :=
    sumFun_congr top fun u hu ↦ by
      dsimp [slotContrib]
      rw [pget_pset 0 8 wt hDw top (by rw [h256]; omega) u (by rw [h256]; omega),
        iteNeg (by omega)]
  have hswap := sumFun_point_swap (slotContrib wt β) (slotContrib wt β')
    top mid hmid fun u hu hne ↦ by
      dsimp [slotContrib]
      rw [ditePos (by omega : u < 155), ditePos (by omega : u < 155),
        hOth _ (microSlotWire_ne inCsa55 inCsa55_inj 98 inCsa55_lt hne _ _)
          (wire_ne_of_lt (microSlotWire_val_lt inCsa55 98 inCsa55_lt hrel hu _))]
  have hm_old : slotContrib wt β mid = w * (β wM).val := by
    dsimp [slotContrib]; rw [ditePos (by omega : mid < 155), hw_mid]
  have hm_new : slotContrib wt β' mid = w * (β' wM).val := by
    dsimp [slotContrib]; rw [ditePos (by omega : mid < 155), hw_mid]
  rw [hm_old, hm_new] at hswap
  rw [hcongr, htop_c]
  dsimp only [wM, cout] at hswap ⊢
  omega

private theorem csa_kill_alive_props {m0 m1 m2 top cur mid : ℕ}
    (hrel : 55 + cur = 98 + top ∧ 55 ≤ top) (hcur : cur < 198)
    {st : CsaSymState} {β β' : BitAssignment 198}
    (hDal : PTree.hasDepth 8 st.alive) (hcl : ∀ q : Wire 198, cur ≤ q.val → β q = 0)
    (halHi : ∀ u, 39 ≤ u → u < 256 → pget false 8 st.alive u = false)
    (hAff : ∀ u (hu : u < 39), pget false 8 st.alive u = true →
      β (microSlotWire inCsa55 98 u (fun _ ↦ by omega)) =
        b2z (evalAff14 (mAxOf m0 m1 m2 (u / 13)) (pget 0 8 st.aff u)))
    (hmid : mid < top) (_htop155 : top < 155)
    (hOth : ∀ q : Wire 198,
      q ≠ microSlotWire inCsa55 98 mid (microSlotBound hrel hmid (Nat.le_of_lt hcur)) →
      q ≠ ⟨cur, hcur⟩ → β' q = β q) :
    PTree.hasDepth 8 (pset 8 st.alive mid false) ∧
    (∀ q : Wire 198, cur + 1 ≤ q.val → β' q = 0) ∧
    (∀ u, 39 ≤ u → u < 256 → pget false 8 (pset 8 st.alive mid false) u = false) ∧
    (∀ u (hu : u < 39), pget false 8 (pset 8 st.alive mid false) u = true →
      β' (microSlotWire inCsa55 98 u (fun _ ↦ by omega)) =
        b2z (evalAff14 (mAxOf m0 m1 m2 (u / 13)) (pget 0 8 st.aff u))) := by
  have h256 : (2 ^ 8 : ℕ) = 256 := by decide
  refine ⟨pset_hasDepth 8 st.alive hDal mid (by rw [h256]; omega) _,
    fun q hq ↦ ?_, fun u hlo hhi ↦ ?_, fun u hu halU ↦ ?_⟩
  · rw [hOth q (wire_ne_of_gt (lt_of_lt_of_le
      (microSlotWire_val_lt inCsa55 98 inCsa55_lt hrel hmid _) (by omega)))
      (wire_ne_of_gt (by dsimp; omega))]
    exact hcl q (by omega)
  · rw [pget_pset false 8 st.alive hDal mid (by rw [h256]; omega) u (by rw [h256]; exact hhi)]
    by_cases hum : u = mid
    · simp [hum]
    · rw [iteNeg hum]; exact halHi u hlo hhi
  · rw [pget_pset false 8 st.alive hDal mid (by rw [h256]; omega) u (by rw [h256]; omega)] at halU
    by_cases hum : u = mid
    · rw [itePos hum] at halU; cases halU
    · rw [iteNeg hum] at halU
      rw [hOth _ (microSlotWire_ne inCsa55 inCsa55_inj 98 inCsa55_lt hum _ _)
        (wire_ne_of_lt (microSlotWire_val_lt inCsa55 98 inCsa55_lt hrel (by omega : u < top) _))]
      exact hAff u hu halU

theorem ssaCsaRun_spec (m0 m1 m2 kc : ℕ) : ∀ (ops : List ZpCsaOp) (top cur : ℕ)
    (hrel : 55 + cur = 98 + top ∧ 55 ≤ top) (_htop55 : 55 ≤ top)
    (hv : csaValid top ops = true) (hM : csaEnd cur ops ≤ 198),
    (ssaCsaRun top cur hrel ops hv hM).countAnd = csaAllocs ops ∧ ∀ (β : BitAssignment 198)
    (st stOut : CsaSymState), CsaInv m0 m1 m2 kc top cur β st → runCsaSym top ops st = some
    stOut → CsaInv m0 m1 m2 kc (top + csaAllocs ops) (csaEnd cur ops)
    ((ssaCsaRun top cur hrel ops hv hM).eval β) stOut ∧ (∀ q : Wire 198, q.val < 98 → (∀ i :
    Fin 55, q ≠ inCsa55 i) → (ssaCsaRun top cur hrel ops hv hM).eval β q = β q) := by
  have h256 : (2 ^ 8 : ℕ) = 256 := by decide
  intro ops
  induction ops with
  | nil =>
      intro top cur hrel _ _ _
      dsimp only [ssaCsaRun, csaAllocs, csaEnd]
      simp only [SsaProg.countAnd_done, SsaProg.eval_done]
      refine ⟨trivial, fun β st stOut hInv hRun ↦ ?_⟩
      dsimp only [runCsaSym] at hRun; injection hRun with hEq; subst hEq
      exact ⟨by simpa only [Nat.add_zero] using hInv, fun _ _ _ ↦ trivial⟩
  | cons op rest ih =>
      intro top cur hrel htop55 hv hM
      cases op with
      | xW s =>
          obtain ⟨hs39, hvR⟩ := csaValid_xW hv
          have hce : cur ≤ 198 := by dsimp [csaEnd] at hM; have := csaEnd_eq_add rest cur; omega
          have hex_le : top ≤ 155 := by have := csaEnd_eq_add rest cur; dsimp [csaEnd] at hM; omega
          obtain ⟨ihCnt, ihEv⟩ := ih top cur hrel htop55 hvR hM
          refine ⟨by dsimp only [ssaCsaRun, csaAllocs]; rw [SsaProg.countAnd_x, ihCnt],
            fun β st stOut hInv hRun ↦ ?_⟩
          dsimp only [runCsaSym] at hRun; split_ifs at hRun with hG
          rw [psetNat_eq, PTree.withVal_eq] at hRun
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hG
          have hInv' := csaInv_aff_update hrel hce hex_le hInv s (by omega)
            ((nat_beq_iff _ _).mp hG.2) _ (Nat.xor (pget 0 8 st.aff s) 8192) (by
              have hAff := hInv.2.2.2.2.2.2.1 s hs39 hG.1.2
              change β (microSlotWire inCsa55 98 s (fun _ ↦ by omega)) + 1 = _
              rw [hAff, evalAff14_xor, evalAff14_8192, ← b2z_not]
              cases evalAff14 (mAxOf m0 m1 m2 (s / 13)) (pget 0 8 st.aff s) <;> decide)
          obtain ⟨hOutInv, hOutPres⟩ := ihEv _ _ stOut hInv' hRun
          dsimp only [ssaCsaRun, csaAllocs, csaEnd]; simp only [SsaProg.eval_x]
          exact ⟨hOutInv, fun q hq hni ↦
            (hOutPres q hq hni).trans (Function.update_of_ne (csa_wire_ne_of_notin hq hni s _) _ _)⟩
      | cnotW sc stt =>
          obtain ⟨hsc39, hst39, _, hvR⟩ := csaValid_cnotW hv
          have hce : cur ≤ 198 := by dsimp [csaEnd] at hM; have := csaEnd_eq_add rest cur; omega
          have hex_le : top ≤ 155 := by have := csaEnd_eq_add rest cur; dsimp [csaEnd] at hM; omega
          obtain ⟨ihCnt, ihEv⟩ := ih top cur hrel htop55 hvR hM
          refine ⟨by dsimp only [ssaCsaRun, csaAllocs]; rw [SsaProg.countAnd_cnot, ihCnt],
            fun β st stOut hInv hRun ↦ ?_⟩
          dsimp only [runCsaSym] at hRun; split_ifs at hRun with hG
          rw [psetNat_eq, PTree.withVal_eq] at hRun
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hG
          obtain ⟨⟨⟨⟨⟨⟨_, _⟩, _⟩, hdiv_b⟩, halC⟩, halT⟩, hwt0_b⟩ := hG
          have hInv' := csaInv_aff_update hrel hce hex_le hInv stt (by omega)
            ((nat_beq_iff _ _).mp hwt0_b) _ (Nat.xor (pget 0 8 st.aff stt) (pget 0 8 st.aff sc)) (by
              have hAff := hInv.2.2.2.2.2.2.1
              change β (microSlotWire inCsa55 98 stt (fun _ ↦ by omega)) +
                β (microSlotWire inCsa55 98 sc (fun _ ↦ by omega)) = _
              rw [hAff stt hst39 halT, hAff sc hsc39 halC, (nat_beq_iff _ _).mp hdiv_b,
                evalAff14_xor, b2z_xor])
          obtain ⟨hOutInv, hOutPres⟩ := ihEv _ _ stOut hInv' hRun
          dsimp only [ssaCsaRun, csaAllocs, csaEnd]; simp only [SsaProg.eval_cnot]
          exact ⟨hOutInv, fun q hq hni ↦
            (hOutPres q hq hni).trans (Function.update_of_ne (csa_wire_ne_of_notin hq hni stt _) _
              _)⟩
      | pushWt s col =>
          obtain ⟨hs39, hcol16, hvR⟩ := csaValid_pushWt hv
          obtain ⟨ihCnt, ihEv⟩ := ih top cur hrel htop55 hvR hM
          refine ⟨by dsimp only [ssaCsaRun, csaAllocs]; exact ihCnt,
            fun β st stOut hInv hRun ↦ ?_⟩
          dsimp only [runCsaSym] at hRun
          split_ifs at hRun with hG
          rw [forceNat_eq, psetNat_eq, PTree.withVal_eq] at hRun
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hG
          obtain ⟨_, halS⟩ := hG
          obtain ⟨hDw, hDal, hPort, hcl, hwtHi, halHi, hAff, hSum⟩ := hInv
          set w := pow2Small col
          let wt' := pset 8 st.wt s (pget 0 8 st.wt s + w)
          let st' := pushAxisTerm (s / 13) (w, pget 0 8 st.aff s) { st with wt := wt' }
          have hst'_wt : st'.wt = wt' := by dsimp [st', pushAxisTerm]; split_ifs <;> rfl
          have hst'_al : st'.alive = st.alive := by dsimp [st', pushAxisTerm]; split_ifs <;> rfl
          have hst'_af : st'.aff = st.aff := by dsimp [st', pushAxisTerm]; split_ifs <;> rfl
          have hex_le : top ≤ 155 := by
            have := csaEnd_eq_add rest cur; dsimp [csaEnd] at hM; omega
          have hInv' : CsaInv m0 m1 m2 kc top cur β st' := by
            refine ⟨hst'_wt ▸ pset_hasDepth 8 st.wt hDw s (by rw [h256]; omega) _,
              hst'_al ▸ hDal, hst'_af ▸ hPort, hcl,
              fun u hlo hhi ↦ ?_, hst'_al ▸ halHi, hst'_al ▸ hst'_af ▸ hAff, ?_⟩
            · rw [hst'_wt,
              pget_pset 0 8 st.wt hDw s (by rw [h256]; omega) u (by rw [h256]; exact hhi),
                iteNeg (by omega)]
              exact hwtHi u hlo hhi
            · rw [hst'_wt]
              have hswap := sumFun_point_swap (slotContrib st.wt β) (slotContrib wt' β)
                top s (by omega) fun u hu hne ↦ by
                  dsimp only [slotContrib, wt']
                  rw [pget_pset 0 8 st.wt hDw s (by rw [h256]; omega) u (by rw [h256]; omega),
                    iteNeg hne]
              have hs_old : slotContrib st.wt β s =
                  pget 0 8 st.wt s * (β (microSlotWire inCsa55 98 s (fun _ ↦ by omega))).val := by
                dsimp [slotContrib]; rw [ditePos (by omega : s < 155)]
              have hs_new : slotContrib wt' β s =
                  (pget 0 8 st.wt s + w) * (β (microSlotWire inCsa55 98 s (fun _ ↦
                    by omega))).val := by
                dsimp [slotContrib, wt']
                rw [ditePos (by omega : s < 155),
                  pget_pset 0 8 st.wt hDw s (by rw [h256]; omega) s (by rw [h256]; omega),
                  itePos rfl]
              rw [hs_old, hs_new, Nat.add_mul] at hswap
              have hadd_s : sumFun (slotContrib wt' β) top =
                  sumFun (slotContrib st.wt β) top +
                    w * (β (microSlotWire inCsa55 98 s (fun _ ↦ by omega))).val := by omega
              have hval_s : w * (β (microSlotWire inCsa55 98 s (fun _ ↦ by omega))).val =
                  Bool.casesOn (evalAff14 (mAxOf m0 m1 m2 (s / 13)) (pget 0 8 st.aff s)) 0 w := by
                rw [hAff s hs39 halS, b2z_val]
                cases evalAff14 (mAxOf m0 m1 m2 (s / 13)) (pget 0 8 st.aff s) <;> simp
              rw [hadd_s, hSum, hval_s]
              have hax_bnd : s / 13 = 0 ∨ s / 13 = 1 ∨ s / 13 = 2 := by omega
              rcases hax_bnd with h0 | h1 | h2
              · dsimp [st', pushAxisTerm, mAxOf]; rw [h0]; dsimp [evalAxisTerms]; omega
              · dsimp [st', pushAxisTerm, mAxOf]; rw [h1]; dsimp [evalAxisTerms]; omega
              · dsimp [st', pushAxisTerm, mAxOf]; rw [h2]; dsimp [evalAxisTerms]; omega
          dsimp only [ssaCsaRun, csaAllocs, csaEnd]
          exact ihEv β st' stOut hInv' hRun
      | fa col a b cin =>
          obtain ⟨_, ha_lt, hb_lt, hc_lt, hab_ne, hac_ne, hbc_ne, hvR⟩ := csaValid_fa hv
          have hcur : cur < 198 := by
            dsimp [csaEnd] at hM; have := csaEnd_eq_add rest (cur + 1); omega
          have hce : cur ≤ 198 := Nat.le_of_lt hcur
          have hrel' : 55 + (cur + 1) = 98 + (top + 1) ∧ 55 ≤ top + 1 :=
            ⟨by obtain ⟨_, _⟩ := hrel; omega, by omega⟩
          obtain ⟨ihCnt, ihEv⟩ := ih (top + 1) (cur + 1) hrel' (by omega) hvR hM
          refine ⟨by dsimp only [ssaCsaRun, csaAllocs]; rw [ssaFaStep_countAnd, ihCnt],
            fun β st stOut hInv hRun ↦ ?_⟩
          dsimp only [runCsaSym] at hRun
          split_ifs at hRun with hG1 hG2
          simp only [psetNat_eq, PTree.withVal_eq] at hRun
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hG1 hG2
          have htop155 : top < 155 := hG1.1.1.1.1.1.1.1
          set w := pow2Small col
          have hw_wa : w ≤ pget 0 8 st.wt a := (nat_ble_iff _ _).mp hG2.1.1
          have hw_wc : w ≤ pget 0 8 st.wt cin := (nat_ble_iff _ _).mp hG2.1.2
          have hwb_eq : pget 0 8 st.wt b = w := (nat_beq_iff _ _).mp hG2.2
          obtain ⟨hDw, hDal, hPort, hcl, hwtHi, halHi, hAff, hSum⟩ := hInv
          let wA := microSlotWire inCsa55 98 a (microSlotBound hrel ha_lt hce)
          let wB := microSlotWire inCsa55 98 b (microSlotBound hrel hb_lt hce)
          let wCin := microSlotWire inCsa55 98 cin (microSlotBound hrel hc_lt hce)
          let cout : Wire 198 := ⟨cur, hcur⟩
          obtain ⟨β', hEvalEq, hβ'B, hβ'Out, hβ'Oth⟩ := ssaFaStep_eval hcur wA wB wCin
            (microSlotWire_ne inCsa55 inCsa55_inj 98 inCsa55_lt hab_ne _ _)
            (microSlotWire_ne inCsa55 inCsa55_inj 98 inCsa55_lt hac_ne _ _)
            (microSlotWire_ne inCsa55 inCsa55_inj 98 inCsa55_lt hbc_ne _ _)
            (microSlotWire_val_lt inCsa55 98 inCsa55_lt hrel ha_lt _)
            (microSlotWire_val_lt inCsa55 98 inCsa55_lt hrel hb_lt _)
            (microSlotWire_val_lt inCsa55 98 inCsa55_lt hrel hc_lt _)
            (ssaCsaRun (top + 1) (cur + 1) hrel' rest hvR hM) β (hcl cout le_rfl)
          let wt1 := pset 8 st.wt a (pget 0 8 st.wt a - w)
          let wt2 := pset 8 wt1 cin (pget 0 8 st.wt cin - w)
          let wt3 := pset 8 wt2 top (w + w)
          have hDw1 : PTree.hasDepth 8 wt1 := pset_hasDepth 8 st.wt hDw a (by rw [h256]; omega) _
          have hDw2 : PTree.hasDepth 8 wt2 := pset_hasDepth 8 wt1 hDw1 cin (by rw [h256]; omega) _
          have hDw3 : PTree.hasDepth 8 wt3 := pset_hasDepth 8 wt2 hDw2 top (by rw [h256]; omega) _
          obtain ⟨hDal1, hcl1, halHi1, hAff1⟩ :=
            csa_kill_alive_props hrel hcur hDal hcl halHi hAff hb_lt htop155 hβ'Oth
          have hInv' : CsaInv m0 m1 m2 kc (top + 1) (cur + 1) β'
              { st with wt := wt3, alive := pset 8 st.alive b false } := by
            refine ⟨hDw3, hDal1, hPort, hcl1, fun u hlo hhi ↦ ?_, halHi1, hAff1, ?_⟩
            · dsimp only [wt3, wt2, wt1]
              rw [pget_pset 0 8 wt2 hDw2 top (by rw [h256]; omega) u (by rw [h256]; exact hhi),
                iteNeg (by omega),
                pget_pset 0 8 wt1 hDw1 cin (by rw [h256]; omega) u (by rw [h256]; exact hhi),
                iteNeg (by omega),
                pget_pset 0 8 st.wt hDw a (by rw [h256]; omega) u (by rw [h256]; exact hhi),
                iteNeg (by omega)]
              exact hwtHi u (by omega) hhi
            · have hwt1_cin : pget 0 8 wt1 cin = pget 0 8 st.wt cin := by
                dsimp [wt1]
                rw [pget_pset 0 8 st.wt hDw a (by rw [h256]; omega) cin (by rw [h256]; omega),
                  iteNeg hac_ne.symm]
              have hwt2_b : pget 0 8 wt2 b = w := by
                dsimp [wt2, wt1]
                rw [pget_pset 0 8 wt1 hDw1 cin (by rw [h256]; omega) b (by rw [h256]; omega),
                  iteNeg hbc_ne,
                  pget_pset 0 8 st.wt hDw a (by rw [h256]; omega) b (by rw [h256]; omega),
                  iteNeg hab_ne.symm, hwb_eq]
              have hcarry := sumFun_slotContrib_carry hrel hcur htop155 hDw2 hb_lt hwt2_b hβ'Oth
              have hsubC :=
                sumFun_slotContrib_sub β hDw1 hc_lt (Nat.le_of_lt htop155) hwt1_cin hw_wc
              have hsubA := sumFun_slotContrib_sub β hDw ha_lt (Nat.le_of_lt htop155) rfl hw_wa
              change sumFun (slotContrib wt3 β') (top + 1) + w * (β wB).val =
                sumFun (slotContrib wt2 β) top + w * (β' wB).val + (w + w) * (β' cout).val at hcarry
              change sumFun (slotContrib wt1 β) top =
                sumFun (slotContrib wt2 β) top + w * (β wCin).val at hsubC
              change sumFun (slotContrib st.wt β) top =
                sumFun (slotContrib wt1 β) top + w * (β wA).val at hsubA
              have hfa_w : w * (β' wB).val + (w + w) * (β' cout).val =
                  w * (β wA).val + w * (β wB).val + w * (β wCin).val := by
                have hfa0 := congrArg (w * ·) (inPlaceFA_val (β wA) (β wB) (β wCin))
                rw [← hβ'B, ← hβ'Out] at hfa0; linarith
              dsimp only; omega
          obtain ⟨hOutInv, hOutPres⟩ := ihEv β' _ stOut hInv' hRun
          dsimp only [ssaCsaRun, csaAllocs, csaEnd]
          rw [hEvalEq, show top + (1 + csaAllocs rest) = (top + 1) + csaAllocs rest by omega]
          exact ⟨hOutInv, fun q hq hni ↦ (hOutPres q hq hni).trans
            (hβ'Oth q (csa_wire_ne_of_notin hq hni b _) (wire_ne_of_lt (by dsimp [cout]; omega)))⟩
      | ha col a c =>
          obtain ⟨_, ha_lt, hc_lt, hac_ne, hvR⟩ := csaValid_ha hv
          have hcur : cur < 198 := by
            dsimp [csaEnd] at hM; have := csaEnd_eq_add rest (cur + 1); omega
          have hce : cur ≤ 198 := Nat.le_of_lt hcur
          have hrel' : 55 + (cur + 1) = 98 + (top + 1) ∧ 55 ≤ top + 1 :=
            ⟨by obtain ⟨_, _⟩ := hrel; omega, by omega⟩
          obtain ⟨ihCnt, ihEv⟩ := ih (top + 1) (cur + 1) hrel' (by omega) hvR hM
          refine ⟨by dsimp only [ssaCsaRun, csaAllocs]; rw [ssaHaStep_countAnd, ihCnt],
            fun β st stOut hInv hRun ↦ ?_⟩
          dsimp only [runCsaSym] at hRun
          split_ifs at hRun with hG1 hG2
          simp only [psetNat_eq, PTree.withVal_eq] at hRun
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hG1 hG2
          have htop155 : top < 155 := hG1.1.1.1.1
          set w := pow2Small col
          have hw_wa : w ≤ pget 0 8 st.wt a := (nat_ble_iff _ _).mp hG2.1
          have hwc_eq : pget 0 8 st.wt c = w := (nat_beq_iff _ _).mp hG2.2
          obtain ⟨hDw, hDal, hPort, hcl, hwtHi, halHi, hAff, hSum⟩ := hInv
          let wA := microSlotWire inCsa55 98 a (microSlotBound hrel ha_lt hce)
          let wC := microSlotWire inCsa55 98 c (microSlotBound hrel hc_lt hce)
          let cout : Wire 198 := ⟨cur, hcur⟩
          obtain ⟨β', hEvalEq, hβ'C, hβ'Out, hβ'Oth⟩ := ssaHaStep_eval hcur wA wC
            (microSlotWire_ne inCsa55 inCsa55_inj 98 inCsa55_lt hac_ne _ _)
            (microSlotWire_val_lt inCsa55 98 inCsa55_lt hrel ha_lt _)
            (microSlotWire_val_lt inCsa55 98 inCsa55_lt hrel hc_lt _)
            (ssaCsaRun (top + 1) (cur + 1) hrel' rest hvR hM) β (hcl cout le_rfl)
          let wt1 := pset 8 st.wt a (pget 0 8 st.wt a - w)
          let wt2 := pset 8 wt1 top (w + w)
          have hDw1 : PTree.hasDepth 8 wt1 := pset_hasDepth 8 st.wt hDw a (by rw [h256]; omega) _
          have hDw2 : PTree.hasDepth 8 wt2 := pset_hasDepth 8 wt1 hDw1 top (by rw [h256]; omega) _
          obtain ⟨hDal1, hcl1, halHi1, hAff1⟩ :=
            csa_kill_alive_props hrel hcur hDal hcl halHi hAff hc_lt htop155 hβ'Oth
          have hInv' : CsaInv m0 m1 m2 kc (top + 1) (cur + 1) β'
              { st with wt := wt2, alive := pset 8 st.alive c false } := by
            refine ⟨hDw2, hDal1, hPort, hcl1, fun u hlo hhi ↦ ?_, halHi1, hAff1, ?_⟩
            · dsimp only [wt2, wt1]
              rw [pget_pset 0 8 wt1 hDw1 top (by rw [h256]; omega) u (by rw [h256]; exact hhi),
                iteNeg (by omega),
                pget_pset 0 8 st.wt hDw a (by rw [h256]; omega) u (by rw [h256]; exact hhi),
                iteNeg (by omega)]
              exact hwtHi u (by omega) hhi
            · have hwt1_c : pget 0 8 wt1 c = w := by
                dsimp [wt1]
                rw [pget_pset 0 8 st.wt hDw a (by rw [h256]; omega) c (by rw [h256]; omega),
                  iteNeg hac_ne.symm, hwc_eq]
              have hcarry := sumFun_slotContrib_carry hrel hcur htop155 hDw1 hc_lt hwt1_c hβ'Oth
              have hsubA := sumFun_slotContrib_sub β hDw ha_lt (Nat.le_of_lt htop155) rfl hw_wa
              change sumFun (slotContrib wt2 β') (top + 1) + w * (β wC).val =
                sumFun (slotContrib wt1 β) top + w * (β' wC).val + (w + w) * (β' cout).val at hcarry
              change sumFun (slotContrib st.wt β) top =
                sumFun (slotContrib wt1 β) top + w * (β wA).val at hsubA
              have hha_w : w * (β' wC).val + (w + w) * (β' cout).val =
                  w * (β wA).val + w * (β wC).val := by
                have hha0 := congrArg (w * ·) (inPlaceHA_val (β wA) (β wC))
                rw [← hβ'C, ← hβ'Out] at hha0; linarith
              dsimp only; omega
          obtain ⟨hOutInv, hOutPres⟩ := ihEv β' _ stOut hInv' hRun
          dsimp only [ssaCsaRun, csaAllocs, csaEnd]
          rw [hEvalEq, show top + (1 + csaAllocs rest) = (top + 1) + csaAllocs rest by omega]
          exact ⟨hOutInv, fun q hq hni ↦ (hOutPres q hq hni).trans
            (hβ'Oth q (csa_wire_ne_of_notin hq hni c _) (wire_ne_of_lt (by dsimp [cout]; omega)))⟩
attribute [local irreducible] ssaCsaRun
theorem csa100_meta :
    csaValid 55 csa100Ops = true ∧ csaAllocs csa100Ops = 100 ∧ 98 + 100 = 198 := by
  decide +kernel
/-- Helper `ssaStage4Csa100` for compact `165`-wire Slot-3 state preparation. -/
def ssaStage4Csa100 : SsaProg 198 98 198 :=
  have hEq : csaEnd 98 csa100Ops = 198 := by
    rw [csaEnd_eq_add, csa100_meta.2.1, csa100_meta.2.2]
  ssaCastEnd hEq (ssaCsaRun 55 98 ⟨rfl, le_rfl⟩ csa100Ops csa100_meta.1 (by rw [hEq]))
theorem ssaStage4Csa100_countAnd : ssaStage4Csa100.countAnd = 100 := by
  have hEq : csaEnd 98 csa100Ops = 198 := by
    rw [csaEnd_eq_add, csa100_meta.2.1, csa100_meta.2.2]
  dsimp only [ssaStage4Csa100]
  rw [ssaCastEnd_countAnd, (ssaCsaRun_spec 0 0 0 0 csa100Ops 55 98 ⟨rfl,
    le_rfl⟩ le_rfl csa100_meta.1 (by rw [hEq])).1,
    csa100_meta.2.1]
/-- Helper `stage4CheckEnd` for compact `165`-wire Slot-3 state preparation. -/
def stage4CheckEnd (stEnd : CsaSymState) : Bool := Nat.beq (pget 0 8 stEnd.wt 154) 65536 &&
    Nat.beq (sumWeights stEnd.wt 154) 65535 && allBelow 128 (fun m ↦ Nat.beq (evalAxisTerms m
    stEnd.ax0) (m * m + 5456) && Nat.beq (evalAxisTerms m stEnd.ax1) (m * m + 5456) && Nat.beq
    (evalAxisTerms m stEnd.ax2) (m * m + 5456))
theorem checkStage4Cert_true :
    checkOpt (runCsaSym 55 csa100Ops initCsaSymState) stage4CheckEnd = true := by
  decide +kernel
/-- Helper `carry16Wire` for compact `165`-wire Slot-3 state preparation. -/
def carry16Wire : Wire 198 := ⟨197, by decide⟩
theorem ssaStage4Csa100_spec (u22 : Fin 4194304) (kc : ℕ) (hkc_lt : kc < 65536)
    (β : BitAssignment 198)
    (hcl : ∀ q : Wire 198, 98 ≤ q.val → β q = 0)
    (hmt : ∀ (w : Fin 3) (b : Fin 7), β (mtWire w b) = b2z ((shiftedMag3 u22 w).testBit b.val))
    (hz : ∀ (w : Fin 3) (k : Fin 6), β (zWire w k) = b2z (zPref (shiftedMag3 u22 w) k.val))
    (hkc : ∀ j : Fin 16, β (kcWire j) = b2z (kc.testBit j.val)) :
    let δ := ssaStage4Csa100.eval β
    ssaStage4Csa100.countAnd = 100 ∧
    δ validWire = β validWire ∧
    δ carry16Wire + 1 = b2z (decide (kc + 16368 + sTilde3 u22 < 65536)) := by
  let m0 := shiftedMag3 u22 0
  let m1 := shiftedMag3 u22 1
  let m2 := shiftedMag3 u22 2
  have hm0 : m0 < 128 := shiftedMag3_lt_128 u22 0
  have hm1 : m1 < 128 := shiftedMag3_lt_128 u22 1
  have hm2 : m2 < 128 := shiftedMag3_lt_128 u22 2
  have hmAx : ∀ w : Fin 3, mAxOf m0 m1 m2 w.val = shiftedMag3 u22 w := fun w ↦ by
    fin_cases w <;> rfl
  have hInit := initCsaSymState_inv m0 m1 m2 kc hkc_lt β hcl
    (fun w b ↦ by rw [hmAx w]; exact hmt w b)
    (fun w k ↦ by rw [hmAx w]; exact hz w k) hkc
  have hEq : csaEnd 98 csa100Ops = 198 := by
    rw [csaEnd_eq_add, csa100_meta.2.1, csa100_meta.2.2]
  obtain ⟨hCnt, hRunSpec⟩ := ssaCsaRun_spec m0 m1 m2 kc csa100Ops 55 98 ⟨rfl, le_rfl⟩ le_rfl
    csa100_meta.1 (by rw [hEq])
  obtain ⟨stEnd, hSym, hcert⟩ := checkOpt_sound checkStage4Cert_true
  dsimp only [stage4CheckEnd] at hcert
  obtain ⟨h12_cert, hPoly⟩ := Bool.and_eq_true_iff.mp hcert
  obtain ⟨hw154_b, hsum154_b⟩ := Bool.and_eq_true_iff.mp h12_cert
  have hw154 : pget 0 8 stEnd.wt 154 = 65536 := (nat_beq_iff _ _).mp hw154_b
  have hsum154 : sumWeights stEnd.wt 154 = 65535 := (nat_beq_iff _ _).mp hsum154_b
  have hAx0 : evalAxisTerms m0 stEnd.ax0 = m0 * m0 + 5456 :=
    (nat_beq_iff _ _).mp (Bool.and_eq_true_iff.mp
      (Bool.and_eq_true_iff.mp ((allBelow_iff 128 _).mp hPoly m0 hm0)).1).1
  have hAx1 : evalAxisTerms m1 stEnd.ax1 = m1 * m1 + 5456 :=
    (nat_beq_iff _ _).mp (Bool.and_eq_true_iff.mp
      (Bool.and_eq_true_iff.mp ((allBelow_iff 128 _).mp hPoly m1 hm1)).1).2
  have hAx2 : evalAxisTerms m2 stEnd.ax2 = m2 * m2 + 5456 :=
    (nat_beq_iff _ _).mp (Bool.and_eq_true_iff.mp ((allBelow_iff 128 _).mp hPoly m2 hm2)).2
  obtain ⟨hInvEnd, hPres⟩ := hRunSpec β initCsaSymState stEnd hInit hSym
  dsimp only
  refine ⟨ssaStage4Csa100_countAnd, ?_, ?_⟩
  · dsimp only [ssaStage4Csa100]
    rw [ssaCastEnd_eval]
    exact hPres validWire (by decide) (fun i h ↦ by
      have hlt97 := inCsa55_lt97 i
      rw [← h] at hlt97; exact absurd hlt97 (by decide))
  · dsimp only [ssaStage4Csa100]
    rw [ssaCastEnd_eval]
    let δ := (ssaCsaRun 55 98 ⟨rfl, le_rfl⟩ csa100Ops csa100_meta.1 (by rw [hEq])).eval β
    have hsT : sTilde3 u22 = m0 * m0 + m1 * m1 + m2 * m2 := by
      unfold sTilde3; dsimp [m0, m1, m2]; ring
    have hSumEnd : sumFun (slotContrib stEnd.wt δ) 154 + 65536 * (δ carry16Wire).val =
        kc + 16368 + sTilde3 u22 := by
      have hc154 : slotContrib stEnd.wt δ 154 = 65536 * (δ carry16Wire).val := by
        rw [slotContrib, ditePos (by decide), hw154,
          microSlotWire_ge_in inCsa55 98 154 (by decide)]
        rfl
      have h155 : sumFun (slotContrib stEnd.wt δ) 155 = kc + 16368 + sTilde3 u22 := by
        rw [congrArg (sumFun (slotContrib stEnd.wt δ))
            (by rw [csa100_meta.2.1] : 155 = 55 + csaAllocs csa100Ops),
          hInvEnd.2.2.2.2.2.2.2, hAx0, hAx1, hAx2, hsT]; omega
      dsimp only [sumFun] at h155; rw [hc154] at h155; exact h155
    have hle154 := (sumFun_slotContrib_le_sumWeights stEnd.wt δ 154 (by decide)).trans_eq hsum154
    change δ carry16Wire + 1 = _
    rcases bit_cases (δ carry16Wire) with h0 | h1
    · rw [h0, show (0 : ZMod 2).val = 0 from rfl] at hSumEnd
      rw [h0, decide_eq_true (by omega : kc + 16368 + sTilde3 u22 < 65536)]; rfl
    · rw [h1, show (1 : ZMod 2).val = 1 from rfl] at hSumEnd
      rw [h1, decide_eq_false (by omega : ¬ (kc + 16368 + sTilde3 u22 < 65536))]; decide
attribute [local irreducible] ssaStage4Csa100
/-- Helper `fastMin` for compact `165`-wire Slot-3 state preparation. -/
def fastMin (x y : ℕ) : ℕ := Bool.casesOn (Nat.ble x y) y x
/-- Helper `fastMax` for compact `165`-wire Slot-3 state preparation. -/
def fastMax (x y : ℕ) : ℕ := Bool.casesOn (Nat.ble x y) x y
theorem fastMin_eq (x y : ℕ) : fastMin x y = min x y := by
  dsimp only [fastMin]
  by_cases h : x ≤ y
  · rw [(nat_ble_iff x y).mpr h, Nat.min_eq_left h]
  · rw [Bool.eq_false_iff.mpr (fun ht ↦ h ((nat_ble_iff x y).mp ht)), Nat.min_eq_right (by omega)]
theorem fastMax_eq (x y : ℕ) : fastMax x y = max x y := by
  dsimp only [fastMax]
  by_cases h : x ≤ y
  · rw [(nat_ble_iff x y).mpr h, Nat.max_eq_right h]
  · rw [Bool.eq_false_iff.mpr (fun ht ↦ h ((nat_ble_iff x y).mp ht)), Nat.max_eq_left (by omega)]
/-- Helper `isqrtStep` for compact `165`-wire Slot-3 state preparation. -/
def isqrtStep (x bit r : ℕ) : ℕ := forceNat (r + bit) fun c ↦ Bool.casesOn (Nat.ble (c * c) x)
    r c
/-- Helper `isqrt128` for compact `165`-wire Slot-3 state preparation. -/
def isqrt128 (x : ℕ) : ℕ := forceNat (Bool.casesOn (Nat.ble 4096 x) 0 64) fun r6 ↦ forceNat
    (isqrtStep x 32 r6) fun r5 ↦ forceNat (isqrtStep x 16 r5) fun r4 ↦ forceNat
    (isqrtStep x 8 r4) fun r3 ↦ forceNat (isqrtStep x 4 r3) fun r2 ↦ forceNat
    (isqrtStep x 2 r2) fun r1 ↦ isqrtStep x 1 r1
/-- Helper `isSq128` for compact `165`-wire Slot-3 state preparation. -/
def isSq128 (x : ℕ) : Bool := forceNat x fun x0 ↦ forceNat (isqrt128 x0) fun r ↦ Nat.beq
    (r * r) x0
theorem isSq128_hit {b : ℕ} (hb : b < 128) : isSq128 (b * b) = true := by
  have hall : allBelow 128 (fun k ↦ isSq128 (k * k)) = true := by decide +kernel
  exact (allBelow_iff 128 _).mp hall b hb
theorem sq_add_sq_mod4_ne_3 (a b : ℕ) : Nat.beq ((a * a + b * b) % 4) 3 = false := by
  have hall : allBelow 4 (fun x ↦ allBelow 4 (fun y ↦
    Bool.not (Nat.beq ((x * x + y * y) % 4) 3))) = true := by
    decide +kernel
  have h1 := (allBelow_iff 4 _).mp hall (a % 4) (Nat.mod_lt a (by decide))
  have h2 := (allBelow_iff 4 _).mp h1 (b % 4) (Nat.mod_lt b (by decide))
  have hmod : (a * a + b * b) % 4 = ((a % 4) * (a % 4) + (b % 4) * (b % 4)) % 4 := by
    rw [Nat.add_mod, Nat.mul_mod a a, Nat.mul_mod b b, ← Nat.add_mod]
  rw [hmod]
  exact Bool.eq_false_iff.mpr (fun ht ↦ by rw [ht] at h2; cases h2)
theorem sq3_mod8_ne_7 (a b d : ℕ) : Nat.beq ((a * a + b * b + d * d) % 8) 7 = false := by
  have hall : allBelow 8 (fun x ↦ allBelow 8 (fun y ↦ allBelow 8 (fun z ↦
      Bool.not (Nat.beq ((x * x + y * y + z * z) % 8) 7)))) = true := by decide +kernel
  have h1 := (allBelow_iff 8 _).mp hall (a % 8) (Nat.mod_lt a (by decide))
  have h2 := (allBelow_iff 8 _).mp h1 (b % 8) (Nat.mod_lt b (by decide))
  have h3 := (allBelow_iff 8 _).mp h2 (d % 8) (Nat.mod_lt d (by decide))
  have hmod : (a * a + b * b + d * d) % 8 =
      ((a % 8) * (a % 8) + (b % 8) * (b % 8) + (d % 8) * (d % 8)) % 8 := by
    rw [Nat.add_mod, Nat.add_mod (a * a) (b * b), Nat.mul_mod a a, Nat.mul_mod b b, Nat.mul_mod d d]
    omega
  rw [hmod]
  exact Bool.eq_false_iff.mpr (fun ht ↦ by rw [ht] at h3; cases h3)
/-- Helper `noTwoSq128` for compact `165`-wire Slot-3 state preparation. -/
def noTwoSq128 (rem : ℕ) : Bool := forceNat rem fun rem0 ↦ Bool.casesOn (Nat.beq (rem0 % 4) 3)
    (allBelow 128 fun a ↦ forceNat (a * a) fun a2 ↦ Bool.casesOn (Nat.ble rem0 (a2 + a2) &&
    Nat.ble a2 rem0) true (Bool.not (isSq128 (rem0 - a2)))) true
theorem noTwoSq128_hit_le {a b : ℕ} (ha : a < 128) (hb : b < 128) (hba : b ≤ a) :
    noTwoSq128 (a * a + b * b) = false := by
  dsimp only [noTwoSq128]
  rw [forceNat_eq, sq_add_sq_mod4_ne_3 a b]
  dsimp only
  apply Bool.eq_false_iff.mpr
  intro hall
  have ha_chk := (allBelow_iff 128 _).mp hall a ha
  rw [forceNat_eq] at ha_chk
  have h1 : Nat.ble (a * a + b * b) (a * a + a * a) = true := (nat_ble_iff _ _).mpr (by nlinarith)
  have h2 : Nat.ble (a * a) (a * a + b * b) = true := (nat_ble_iff _ _).mpr (by omega)
  change Bool.casesOn (Nat.ble (a * a + b * b) (a * a + a * a) && Nat.ble (a * a) (a * a + b * b))
    true (Bool.not (isSq128 ((a * a + b * b) - a * a))) = true at ha_chk
  rw [h1, h2] at ha_chk
  dsimp only [Bool.and_self] at ha_chk
  rw [show (a * a + b * b) - a * a = b * b by omega, isSq128_hit hb] at ha_chk
  cases ha_chk
theorem noTwoSq128_hit {a b : ℕ} (ha : a < 128) (hb : b < 128) :
    noTwoSq128 (a * a + b * b) = false := by
  by_cases hba : b ≤ a
  · exact noTwoSq128_hit_le ha hb hba
  · rw [Nat.add_comm]
    exact noTwoSq128_hit_le hb ha (by omega)
/-- Helper `thr16Fast` for compact `165`-wire Slot-3 state preparation. -/
def thr16Fast (c : ℕ) : ℕ :=
  Bool.casesOn (Nat.beq c 0) (fastMin 65535 (1044190 / c + 1)) 65535
theorem thr16Fast_eq (c : Fin 256) : thr16Fast c.val = thr16 c := by
  revert c; decide
/-- Helper `checkShellThrCert` for compact `165`-wire Slot-3 state preparation. -/
def checkShellThrCert : Bool := allBelow 256 fun c ↦ forceNat (getNatAt kcTable49168List c)
    fun kc ↦ Nat.ble kc 49168 && forceNat (49168 - kc) fun tEff ↦ forceNat (thr16Fast c)
    fun tId ↦ forceNat (fastMax 4096 (fastMin tEff tId)) fun lo ↦ forceNat
    (fastMin 48388 (fastMax tEff tId)) fun hi ↦ allBelowFrom (fun s ↦ Bool.casesOn (Nat.beq (s
    % 8) 7) (allBelowFrom (fun d ↦ forceNat (d * d) fun d2 ↦ Bool.casesOn (Nat.ble d2 s &&
    Nat.ble (s - d2) 32258) true (noTwoSq128 (s - d2))) 64 64) true) lo (hi - lo)
theorem checkShellThrCert_true : checkShellThrCert = true := by decide +kernel
theorem testBit_six_iff_ge_64 {m : ℕ} (hm : m < 128) : m.testBit 6 = true ↔ 64 ≤ m := by
  have hall : allBelow 128 (fun x ↦ (x.testBit 6 == Nat.ble 64 x)) = true := by decide
  have hx := (bool_beq_iff _ _).mp ((allBelow_iff 128 _).mp hall m hm)
  rw [hx]; exact nat_ble_iff 64 m
theorem shell_thr_equiv (u22 : Fin 4194304) (s3 : Fin 8) (c8 : Fin 256)
    (hval : validShellNu3 u22 s3 = true) :
    decide (getNatAt kcTable49168List c8.val + 16368 + sTilde3 u22 < 65536) =
      decide (sTilde3 u22 < thr16 c8) := by
  have hc_chk := (allBelow_iff 256 _).mp checkShellThrCert_true c8.val c8.isLt
  rw [forceNat_eq] at hc_chk
  obtain ⟨hkc_le_b, hGapC⟩ := Bool.and_eq_true_iff.mp hc_chk
  rw [forceNat_eq, forceNat_eq, forceNat_eq, forceNat_eq] at hGapC
  let kc := getNatAt kcTable49168List c8.val
  have hkc_le : kc ≤ 49168 := (nat_ble_iff _ _).mp hkc_le_b
  have hv := hval
  rw [validShellNu3_eq_shifted u22 s3] at hv
  simp only [Bool.and_eq_true, Bool.or_eq_true] at hv
  have h6 := hv.1.1.1.2
  have hex3 : ∃ a b d : ℕ, a < 128 ∧ b < 128 ∧ 64 ≤ d ∧ d < 128 ∧
      sTilde3 u22 = a * a + b * b + d * d := by
    have hmk : ∀ (i j k : Fin 3), (shiftedMag3 u22 k).testBit 6 = true →
        sTilde3 u22 = shiftedMag3 u22 i * shiftedMag3 u22 i +
          shiftedMag3 u22 j * shiftedMag3 u22 j + shiftedMag3 u22 k * shiftedMag3 u22 k →
        ∃ a b d, a < 128 ∧ b < 128 ∧ 64 ≤ d ∧ d < 128 ∧ sTilde3 u22 = a * a + b * b + d * d :=
      fun i j k hk hs ↦ ⟨_, _, _, shiftedMag3_lt_128 u22 i, shiftedMag3_lt_128 u22 j,
        (testBit_six_iff_ge_64 (shiftedMag3_lt_128 u22 k)).mp hk, shiftedMag3_lt_128 u22 k, hs⟩
    rcases h6 with (h0 | h1) | h2
    · exact hmk 1 2 0 h0 (by unfold sTilde3; ring)
    · exact hmk 0 2 1 h1 (by unfold sTilde3; ring)
    · exact hmk 0 1 2 h2 (by unfold sTilde3; ring)
  obtain ⟨a, b, d, ha, hb, hd64, hd128, hsEq⟩ := hex3
  let s := sTilde3 u22
  have hsEq' : s = a * a + b * b + d * d := hsEq
  have hs_lo : 4096 ≤ s := by rw [hsEq']; nlinarith
  have hs_hi : s < 48388 := Nat.lt_succ_of_le (sTilde3_le_48387 u22)
  let tEff := 49168 - kc
  let tId := thr16 c8
  rw [thr16Fast_eq c8] at hGapC
  simp only [fastMin_eq, fastMax_eq] at hGapC
  have hnot_gap : ¬ (min tEff tId ≤ s ∧ s < max tEff tId) := by
    rintro ⟨hmin, hmax⟩
    let lo := max 4096 (min tEff tId)
    let hi := min 48388 (max tEff tId)
    have hlo_s : lo ≤ s := max_le hs_lo hmin
    have hs_hi' : s < hi := lt_min hs_hi hmax
    have hs_chk := (allBelowFrom_iff _ lo (hi - lo)).mp hGapC (s - lo) (by omega)
    rw [show lo + (s - lo) = s by omega] at hs_chk
    have hs_mod8 : Nat.beq (s % 8) 7 = false := by
      rw [hsEq']; exact sq3_mod8_ne_7 a b d
    change Bool.casesOn (Nat.beq (s % 8) 7) _ true = true at hs_chk
    rw [hs_mod8] at hs_chk; dsimp only at hs_chk
    have hd_chk := (allBelowFrom_iff _ 64 64).mp hs_chk (d - 64) (by omega)
    rw [show 64 + (d - 64) = d by omega, forceNat_eq] at hd_chk
    have hrem_eq : s - d * d = a * a + b * b := by omega
    have hd2_le : Nat.ble (d * d) s = true := (nat_ble_iff _ _).mpr (by omega)
    have hrem_le : Nat.ble (s - d * d) 32258 = true :=
      (nat_ble_iff _ _).mpr (by rw [hrem_eq]; nlinarith)
    change Bool.casesOn (Nat.ble (d * d) s && Nat.ble (s - d * d) 32258)
      true (noTwoSq128 (s - d * d)) = true at hd_chk
    rw [hd2_le, hrem_le] at hd_chk
    dsimp only [Bool.and_self] at hd_chk
    rw [hrem_eq, noTwoSq128_hit ha hb] at hd_chk
    cases hd_chk
  apply decide_iff_both
  dsimp only [kc, s, tEff, tId] at hkc_le hnot_gap ⊢
  omega
theorem kc_lt_65536 (c8 : Fin 256) : getNatAt kcTable49168List c8.val < 65536 := by
  revert c8; decide
theorem predCoarseGood33_eq_b2z (α : BitAssignment 33) : predCoarseGood33 α = b2z
    (coarseGood3Computable ((QRegister.block 0 22 s3Bound_0_22).extractIndex ((basisBitsEquiv
    33).symm α)) ((QRegister.block 22 3 s3Bound_22_3).extractIndex ((basisBitsEquiv 33).symm
    α)) ((QRegister.block 25 8 s3Bound_25_8).extractIndex ((basisBitsEquiv 33).symm α))) := by
  change (if coarseGood3Computable ((QRegister.block 0 22 s3Bound_0_22).extractIndex
    ((basisBitsEquiv 33).symm α)) ((QRegister.block 22 3 s3Bound_22_3).extractIndex
    ((basisBitsEquiv 33).symm α)) ((QRegister.block 25 8 s3Bound_25_8).extractIndex
    ((basisBitsEquiv 33).symm α)) = true then (1 : ZMod 2) else 0) = _
  set cg := coarseGood3Computable
    ((QRegister.block 0 22 s3Bound_0_22).extractIndex ((basisBitsEquiv 33).symm α))
    ((QRegister.block 22 3 s3Bound_22_3).extractIndex ((basisBitsEquiv 33).symm α))
    ((QRegister.block 25 8 s3Bound_25_8).extractIndex ((basisBitsEquiv 33).symm α))
  by_cases h : cg = true
  · rw [itePos h, h]; rfl
  · rw [iteNeg h, Bool.eq_false_iff.mpr h]; rfl
/- ## Clean-Workspace Staged Closure (`dCoarseGood33_165`, `dOaa33_165`, `dPrep3_216_179`) -/

/-- `127`-AND Stage-3+4 phase-kick SSA program on `71 + 127 = 198` wires. -/
def ssaKick198 : SsaProg (71 + 127) 71 (71 + 127) := ssaStage3Valid27.append
    (ssaStage4Csa100.append (SsaProg.x carry16Wire (by decide) (SsaProg.done 198)))

theorem ssaKick198_countAnd : ssaKick198.countAnd = 127 := by
  dsimp only [ssaKick198]
  rw [SsaProg.append_countAnd, SsaProg.append_countAnd,
    ssaStage3Valid27_countAnd, ssaStage4Csa100_countAnd]
  rfl

theorem ssaKick198_eval_eq (β₀ : BitAssignment (71 + 127)) : ssaKick198.eval β₀ =
    Function.update (ssaStage4Csa100.eval (ssaStage3Valid27.eval β₀)) carry16Wire
    (ssaStage4Csa100.eval (ssaStage3Valid27.eval β₀) carry16Wire + 1) := by
  dsimp only [ssaKick198]
  simp only [SsaProg.append_eval, SsaProg.eval_x, SsaProg.eval_done]

attribute [local irreducible] kcTable49168List

/-- `71`-bit active phase predicate realized by `ssaKick198` + `CZ(validWire, carry16Wire)`. -/
def predKick71 (α71 : BitAssignment 71) : ZMod 2 :=
  let β₀ : BitAssignment (71 + 127) := padZeroBits α71
  ssaKick198.eval β₀ validWire * ssaKick198.eval β₀ carry16Wire

theorem ssaKick198_pred (α71 : BitAssignment 71) :
    let β₀ : BitAssignment (71 + 127) := padZeroBits α71
    ssaKick198.eval β₀ validWire * ssaKick198.eval β₀ carry16Wire = predKick71 α71 :=
  rfl

/-- `508 T` dynamic circuit realizing `phaseDiagUnitary predKick71` on `71` active + `127` clean
  scratch wires. -/
noncomputable def dKick71 {Var : Type} {n : ℕ} (v : Var)
    (rAct71 : QRegister 71 n) (rScr127 : QRegister 127 n)
    (hDisj : rAct71.DisjointWires rScr127) : DynamicCircuit Var n :=
  compileSsaCzDyn v rAct71 rScr127 hDisj (le_refl 127) ssaKick198 validWire carry16Wire (by decide)

theorem dKick71_count_toff {Var : Type} {n : ℕ} (v : Var) (rAct71 : QRegister 71 n)
    (rScr127 : QRegister 127 n) (hDisj : rAct71.DisjointWires rScr127) :
    (dKick71 v rAct71 rScr127 hDisj).count PrimitiveGate.TOFF = 0 :=
    compileSsaCzDyn_count_toff v rAct71 rScr127 hDisj (le_refl 127) ssaKick198 validWire
    carry16Wire (by decide)

theorem dKick71_count_t {Var : Type} {n : ℕ} (v : Var) (rAct71 : QRegister 71 n)
    (rScr127 : QRegister 127 n) (hDisj : rAct71.DisjointWires rScr127) :
    (dKick71 v rAct71 rScr127 hDisj).count PrimitiveGate.T = 508 := by
  unfold dKick71
  rw [compileSsaCzDyn_count_t, ssaKick198_countAnd]

def phaseStage234_49 (α49 : BitAssignment 49) : ZMod 2 :=
  predKick71 (xorRightMapGen tblBitsUnpack22 (padZeroBits α49))

private theorem xorRightMapGen_padZeroBits_lo {k₁ k₂ : ℕ}
    (tbl : BitAssignment k₁ → BitAssignment k₂) (α : BitAssignment k₁) (i : ℕ) (hi : i < k₁) :
    xorRightMapGen tbl (padZeroBits α) ⟨i, by omega⟩ = α ⟨i, hi⟩ := by
  dsimp only [xorRightMapGen]
  rw [ditePos hi, padZeroBits_lt α ⟨i, by omega⟩ hi]

private theorem xorRightMapGen_padZeroBits_hi {k₁ k₂ : ℕ}
    (tbl : BitAssignment k₁ → BitAssignment k₂) (α : BitAssignment k₁) (j : Fin k₂) :
    xorRightMapGen tbl (padZeroBits α) ⟨k₁ + j.val, by omega⟩ = tbl α j := by
  dsimp only [xorRightMapGen]
  rw [diteNeg (show ¬ (k₁ + j.val < k₁) by omega),
    padZeroBits_ge α ⟨k₁ + j.val, by omega⟩ (by dsimp; omega), zero_add]
  have hleft : (fun i : Fin k₁ ↦ padZeroBits α (Fin.castAdd k₂ i)) = α := funext fun i ↦
    (padZeroBits_lt α (Fin.castAdd k₂ i) i.isLt).trans (congrArg α (Fin.ext rfl))
  rw [hleft, show (⟨k₁ + j.val - k₁, by omega⟩ : Fin k₂) = j from Fin.ext (by dsimp; omega)]

theorem phaseStage234_49_on_stage1 (α33 : BitAssignment 33) :
    phaseStage234_49 (xorRightMapGen tblBits16 (padZeroBits α33)) = predCoarseGood33 α33 := by
  let idx : Fin (2 ^ 33) := (basisBitsEquiv 33).symm α33
  have hα_bb : basisBits 33 idx = α33 := (basisBitsEquiv 33).apply_symm_apply α33
  let u22 : Fin 4194304 := (QRegister.block 0 22 s3Bound_0_22).extractIndex idx
  let s3 : Fin 8 := (QRegister.block 22 3 s3Bound_22_3).extractIndex idx
  let c8 : Fin 256 := (QRegister.block 25 8 s3Bound_25_8).extractIndex idx
  let α49 : BitAssignment (33 + 16) := xorRightMapGen tblBits16 (padZeroBits α33)
  let α71 : BitAssignment 71 := xorRightMapGen tblBitsUnpack22 (padZeroBits α49)
  let β₀ : BitAssignment (71 + 127) := padZeroBits α71
  have hα49_lo : ∀ (i : ℕ) (hi : i < 33), α49 ⟨i, by omega⟩ = α33 ⟨i, hi⟩ :=
    xorRightMapGen_padZeroBits_lo tblBits16 α33
  have hα49_kc : ∀ j : Fin 16, α49 ⟨33 + j.val, by omega⟩ = tblBits16 α33 j :=
    xorRightMapGen_padZeroBits_hi tblBits16 α33
  have hα71_lo : ∀ (i : ℕ) (hi : i < 49), α71 ⟨i, by omega⟩ = α49 ⟨i, hi⟩ :=
    xorRightMapGen_padZeroBits_lo tblBitsUnpack22 α49
  have hα71_up : ∀ j : Fin 22, α71 ⟨49 + j.val, by omega⟩ = tblBitsUnpack22 α49 j :=
    xorRightMapGen_padZeroBits_hi tblBitsUnpack22 α49
  have hblk_val : ∀ {off len : ℕ} (hB : off + len ≤ 33) (f : Fin len → ZMod 2),
      (∀ i : Fin len, f i = α33 ⟨off + i.val, by omega⟩) →
      bitsVal f = ((QRegister.block off len hB).extractIndex idx).val := fun {off len} hB f hf ↦ by
    refine bitsVal_eq_of_testBit _ _ ((QRegister.block off len hB).extractIndex idx).isLt fun i ↦ ?_
    rw [hf i, ← basisBits_eq_testBit]
    exact (congrArg α33 (Fin.ext rfl)).symm.trans
      (hα_bb ▸ (QRegister.basisBits_extractIndex (QRegister.block off len hB) idx i).symm)
  have hu22_val : ∀ (f : Fin 22 → ZMod 2),
      (∀ i : Fin 22, f i = α33 ⟨i.val, Nat.lt_trans i.isLt (by decide)⟩) →
      bitsVal f = u22.val := fun f hf ↦ hblk_val s3Bound_0_22 f fun i ↦
        (hf i).trans (congrArg α33 (Fin.ext (Nat.zero_add i.val).symm))
  have hu22_fin : ∀ (f : Fin 22 → ZMod 2) (hlt : bitsVal f < 4194304),
      (∀ i : Fin 22, f i = α33 ⟨i.val, Nat.lt_trans i.isLt (by decide)⟩) →
      (⟨bitsVal f, hlt⟩ : Fin 4194304) = u22 := fun f _ hf ↦ Fin.ext (hu22_val f hf)
  have hc8_val : ∀ (f : Fin 8 → ZMod 2),
      (∀ i : Fin 8, f i = α33 ⟨25 + i.val, by omega⟩) →
      bitsVal f = c8.val := hblk_val s3Bound_25_8
  have hcl₀ : ∀ q : Wire 198, 71 ≤ q.val → β₀ q = 0 := fun q hq ↦ @padZeroBits_ge 71 127 α71 q hq
  have hz7_₀ : β₀ z7Wire = b2z (decide (u22.val / 32768 = 0)) := by
    dsimp only [β₀, z7Wire]
    rw [@padZeroBits_lt 71 127 α71 ⟨49, by decide⟩ (by decide)]
    refine (hα71_up 0).trans ?_
    dsimp only [tblBitsUnpack22]
    rw [ditePos (Fin.val_zero 22)]
    refine congrArg (fun n ↦ b2z (decide (n / 32768 = 0))) (hu22_val _ fun i ↦ ?_)
    exact (congrArg α49 (Fin.ext rfl)).trans (hα49_lo i.val (Nat.lt_trans i.isLt (by decide)))
  have hmt_₀ : ∀ (w : Fin 3) (b : Fin 7),
      β₀ (mtWire w b) = b2z ((shiftedMag3 u22 w).testBit b.val) := fun w b ↦ by
    dsimp only [β₀, mtWire]
    rw [@padZeroBits_lt 71 127 α71 ⟨50 + 7 * w.val + b.val, by omega⟩ (by dsimp; omega)]
    let j : Fin 22 := ⟨1 + 7 * w.val + b.val, by omega⟩
    have hj_w : (⟨49 + j.val, by omega⟩ : Fin 71) = ⟨50 + 7 * w.val + b.val, by omega⟩ :=
      Fin.ext (by dsimp [j]; omega)
    rw [← hj_w, hα71_up j]
    dsimp only [tblBitsUnpack22]
    have hnot0 : j.val ≠ 0 := by dsimp [j]; omega
    rw [diteNeg hnot0]
    have hw_div : (⟨(j.val - 1) / 7, by omega⟩ : Fin 3) = w := Fin.ext (by dsimp [j]; omega)
    have hb_mod : (j.val - 1) % 7 = b.val := by dsimp [j]; omega
    rw [hw_div, hb_mod]
    refine congrArg (fun u ↦ b2z ((shiftedMag3 u w).testBit b.val)) (hu22_fin _ _ fun i ↦ ?_)
    exact (congrArg α49 (Fin.ext rfl)).trans (hα49_lo i.val (Nat.lt_trans i.isLt (by decide)))
  have hs3_₀ : ∀ w : Fin 3, β₀ ⟨22 + w.val, by omega⟩ = b2z (s3.val.testBit w.val) := fun w ↦ by
    dsimp only [β₀]
    rw [@padZeroBits_lt 71 127 α71 ⟨22 + w.val, by omega⟩ (by dsimp; omega),
      hα71_lo (22 + w.val) (by omega), hα49_lo (22 + w.val) (by omega)]
    have hb := QRegister.basisBits_extractIndex (QRegister.block 22 3 s3Bound_22_3) idx w
    rw [hα_bb] at hb
    have hb' : basisBits 3 s3 w = α33 ⟨22 + w.val, by omega⟩ :=
      hb.trans (congrArg α33 (Fin.ext rfl))
    rw [← hb', basisBits_eq_testBit]
    cases s3.val.testBit w.val <;> rfl
  obtain ⟨_, hcl₃, hp₃, hz₃, hval₃⟩ := ssaStage3Valid27_spec u22 s3 β₀ hcl₀ hz7_₀ hmt_₀ hs3_₀
  let β₃ := ssaStage3Valid27.eval β₀
  have hmt₃ : ∀ (w : Fin 3) (b : Fin 7),
      β₃ (mtWire w b) = b2z ((shiftedMag3 u22 w).testBit b.val) :=
    fun w b ↦ (hp₃ _ (by revert w b; decide)).trans (hmt_₀ w b)
  have hkc₃ : ∀ j : Fin 16,
      β₃ (kcWire j) = b2z ((getNatAt kcTable49168List c8.val).testBit j.val) := fun j ↦ by
    refine (hp₃ _ (by revert j; decide)).trans ?_
    dsimp only [β₀, kcWire]
    rw [@padZeroBits_lt 71 127 α71 ⟨33 + j.val, by omega⟩ (by dsimp; omega),
      hα71_lo (33 + j.val) (by omega), hα49_kc j]
    dsimp only [tblBits16]
    refine congrArg (fun n ↦ b2z ((getNatAt kcTable49168List n).testBit j.val)) (hc8_val _ fun _ ↦
      ?_)
    exact congrArg α33 (Fin.ext rfl)
  obtain ⟨_, hval₄, hcar₄⟩ := ssaStage4Csa100_spec u22 (getNatAt kcTable49168List c8.val)
    (kc_lt_65536 c8) β₃ hcl₃ hmt₃ hz₃ hkc₃
  let β₄ := ssaStage4Csa100.eval β₃
  have hev : ssaKick198.eval β₀ = Function.update β₄ carry16Wire (β₄ carry16Wire + 1) :=
    ssaKick198_eval_eq β₀
  change ssaKick198.eval β₀ validWire * ssaKick198.eval β₀ carry16Wire = _
  rw [hev, Function.update_of_ne (by decide : validWire ≠ carry16Wire), Function.update_self]
  dsimp only [β₄]
  rw [hval₄, hcar₄]
  dsimp only [β₃]
  rw [hval₃, ← b2z_and]
  have hcg : (validShellNu3 u22 s3 && decide (getNatAt kcTable49168List c8.val + 16368 +
      sTilde3 u22 < 65536)) = coarseGood3Computable u22 s3 c8 := by
    rw [coarseGood3Computable_eq_sTilde u22 s3 c8]
    by_cases hv : validShellNu3 u22 s3 = true
    · rw [hv, Bool.true_and, Bool.true_and, shell_thr_equiv u22 s3 c8 hv]
    · rw [Bool.eq_false_iff.mpr hv, Bool.false_and, Bool.false_and]
  rw [hcg, predCoarseGood33_eq_b2z α33]

theorem phaseDiagUnitary_mulVec_ket {k : ℕ} (pred : BitAssignment k →
    ZMod 2) (α : BitAssignment k) :
    (phaseDiagUnitary pred).1.mulVec (ket α) = ((-1 : ℂ) ^ (pred α).val) • ket α := by
  let z := (basisBitsEquiv k).symm α
  have hk : ket α = Pi.single z 1 := by funext x; simp [z, ket, basisState]
  have hb : basisBits k z = α := (basisBitsEquiv k).apply_symm_apply α
  rw [hk, phaseDiagUnitary, Matrix.mulVec_single_one]
  funext x
  by_cases hx : x = z
  · subst hx; simp [Matrix.diagonal, hb]
  · simp [Matrix.diagonal, hx]

theorem unpack_kick_unpack_unitary : uXorRightPerm tblBitsUnpack22 *
    (phaseDiagUnitary predKick71 * uXorRightPerm tblBitsUnpack22) = phaseDiagUnitary
    (fun α71 ↦ predKick71 (xorRightMapGen tblBitsUnpack22 α71)) := by
  apply Subtype.ext
  apply MeasureBranchHadamardSem.matrix_ext_ket
  intro α71
  rw [Submonoid.coe_mul, Submonoid.coe_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    uXorRightPerm_mulVec_ket, ZMod.val_zero, _root_.pow_zero, one_smul,
    phaseDiagUnitary_mulVec_ket, Matrix.mulVec_smul, uXorRightPerm_mulVec_ket,
    ZMod.val_zero, _root_.pow_zero, one_smul, xorRightMapGen_invol,
    phaseDiagUnitary_mulVec_ket]

attribute [local irreducible] ssaKick198 dKick71

set_option maxRecDepth 512

/-- Catalyst-free `3`-qutrit pure circuit embedded directly on `rCore : QRegister (momCoreWires
  mPayload) n` (`117 T`, `0 TOFF`). -/
def cQutrit3CoreGen {mPayload : ℕ} (hmPay : 80 ≤ mPayload) {n : ℕ}
    (rCore : QRegister (momCoreWires mPayload) n) : Circuit n :=
  cPrepQutrit2.onRegister (rCore.compose (s3QutritPairCore hmPay 0)) ;;ᶜ
    cPrepQutrit2.onRegister (rCore.compose (s3QutritPairCore hmPay 1)) ;;ᶜ
    cPrepQutrit2.onRegister (rCore.compose (s3QutritPairCore hmPay 2))

theorem cQutrit3CoreGen_count_toff {mPayload : ℕ} (hmPay : 80 ≤ mPayload) {n : ℕ}
    (rCore : QRegister (momCoreWires mPayload) n) :
    (cQutrit3CoreGen hmPay rCore).count PrimitiveGate.TOFF = 0 := by
  simp [cQutrit3CoreGen, cPrepQutrit2_count_toff]

theorem cQutrit3CoreGen_inv_count_toff {mPayload : ℕ} (hmPay : 80 ≤ mPayload) {n : ℕ}
    (rCore : QRegister (momCoreWires mPayload) n) :
    (cQutrit3CoreGen hmPay rCore).inverse.count PrimitiveGate.TOFF = 0 := by
  simp [cQutrit3CoreGen, cPrepQutrit2_count_toff]

theorem cQutrit3CoreGen_count_t {mPayload : ℕ} (hmPay : 80 ≤ mPayload) {n : ℕ}
    (rCore : QRegister (momCoreWires mPayload) n) :
    (cQutrit3CoreGen hmPay rCore).count PrimitiveGate.T = 117 := by
  simp [cQutrit3CoreGen, cPrepQutrit2_count_t]

theorem cQutrit3CoreGen_inv_count_t {mPayload : ℕ} (hmPay : 80 ≤ mPayload) {n : ℕ}
    (rCore : QRegister (momCoreWires mPayload) n) :
    (cQutrit3CoreGen hmPay rCore).inverse.count PrimitiveGate.T = 117 := by
  simp [cQutrit3CoreGen, cPrepQutrit2_count_t]

theorem cQutrit3CoreGen_eval {mPayload : ℕ} (hmPay : 80 ≤ mPayload) {n : ℕ}
    (rCore : QRegister (momCoreWires mPayload) n) :
    (cQutrit3CoreGen hmPay rCore).eval = rCore.embedUnitary (uQutrit3 hmPay) := by
  dsimp only [cQutrit3CoreGen, uQutrit3]
  rw [Circuit.eval_seq, Circuit.eval_seq,
    Circuit.eval_onRegister, Circuit.eval_onRegister, Circuit.eval_onRegister]
  have hsel : ∀ j : Fin 3,
      (rCore.compose (s3QutritPairCore hmPay j)).embedUnitary cPrepQutrit2.eval =
        rCore.embedUnitary ((s3QutritPairCore hmPay j).embedUnitary cPrepQutrit2.eval) :=
    fun j ↦ QRegister.embedUnitary_compose rCore (s3QutritPairCore hmPay j) cPrepQutrit2.eval
  rw [hsel 0, hsel 1, hsel 2]
  simp only [s3EmbedUnitary_mul, mul_assoc]

end ConfigLeaf3Prep179Spec

end Leaf3Prep179Spec
end
end Leaf3Prep179Spec

end QuantumComputation.Specs.StoppingPowerSolution
