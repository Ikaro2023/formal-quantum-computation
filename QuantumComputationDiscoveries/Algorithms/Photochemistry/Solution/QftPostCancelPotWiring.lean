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
public import QuantumComputationDiscoveries.Algorithms.Photochemistry.Solution.PotentialSelectSpecB
public import QuantumComputationDiscoveries.Algorithms.Photochemistry.Solution.FermatXagParityEngine

open QuantumComputation.Specs.PhotochemistrySolution.SpecDefs
open QuantumComputation.Specs.PhotochemistrySolution.QhlAux
open QuantumComputation.Specs.PhotochemistrySolution.PgBase
open QuantumComputation.Specs.PhotochemistrySolution.SelectBase
@[expose] public section
set_option allowUnsafeReducibility true
set_option autoImplicit false

noncomputable section ScopedLocalHelpers
open scoped Matrix BigOperators
noncomputable section
set_option exponentiation.threshold 256
open scoped Circuit.Notation
open Operator QProg DynamicCircuit Matrix Circuit Qubit PrimitiveGate QuantumComputation.Specs
  QuantumComputation.Specs.PhotochemistrySolution
  QuantumComputation.Specs.PhotochemistrySolution.SelectSymDynInstance
  QuantumComputation.Specs.PhotochemistrySolution.SelectRefl
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
  _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt
open QuantumComputation.Specs.PhotochemistrySolution.SelectDataBuilder
  QuantumComputation.Specs.PhotochemistrySolution.SelectFastQft8Gidney
  QuantumComputation.Specs.PhotochemistrySolution.SelectFastFlags
  QuantumComputation.Specs.PhotochemistrySolution.SelectCompactAnc
  QuantumComputation.Specs.PhotochemistrySolution.SelectQft8GidneyStg3
open QuantumComputation.Specs.PhotochemistrySolution.SelectQft8CatLocal
  QuantumComputation.Specs.PhotochemistrySolution.FastQft8
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB hiding bitSign ket ket_CNOT
  ket_TOFF ket_X matrix_ext_ket writeReg writeReg_apply_of_not_mem
namespace QuantumComputation.Specs.PhotochemistrySolution.Qft8PostCancelT5
open QFT PhotochemistrySolution.SelectOracles PhotochemistrySolution.UnembedO3Bridge
/-! ## Part 1: General `AndBracketProg.inv`, `.primT`, and `.primToff` -/

theorem circuit_count_inv_local {n k : ℕ} (g₀ : PrimitiveGate k)
    (hg : ∀ {m : ℕ} (g : PrimitiveGate m) (w : QRegister m n),
      (Circuit.gate g w).inverse.count g₀ = (Circuit.gate g w).count g₀)
    (c : Circuit n) : c.inverse.count g₀ = c.count g₀ := by
  induction c with
  | identity => rfl
  | gate g w => exact hg g w
  | seq _ _ ih₁ ih₂ => simp only [Circuit.inverse, Circuit.count_seq, ih₁, ih₂, Nat.add_comm]
def abpInv {n : ℕ} : AndBracketProg n → AndBracketProg n
  | .id => .id
  | .prim c => .prim c.inverse
  | .seq p₁ p₂ => .seq (abpInv p₂) (abpInv p₁)
  | .tempAnd c₁ c₂ anc h₁₂ h₁a h₂a body => .tempAnd c₁ c₂ anc h₁₂ h₁a h₂a (abpInv body)
def abpPrimT {n : ℕ} : AndBracketProg n → ℕ
  | .id => 0
  | .prim c => c.count .T
  | .seq p₁ p₂ => abpPrimT p₁ + abpPrimT p₂
  | .tempAnd _ _ _ _ _ _ body => abpPrimT body
def abpPrimToff {n : ℕ} : AndBracketProg n → ℕ
  | .id => 0
  | .prim c => c.count .TOFF
  | .seq p₁ p₂ => abpPrimToff p₁ + abpPrimToff p₂
  | .tempAnd _ _ _ _ _ _ body => abpPrimToff body
@[simp] theorem numTempAnd_abpInv {n : ℕ} (p : AndBracketProg n) :
    (abpInv p).numTempAnd = p.numTempAnd := by
  induction p <;> simp only [abpInv, AndBracketProg.numTempAnd, *, Nat.add_comm]
@[simp] theorem abpPrimT_abpInv {n : ℕ} (p : AndBracketProg n) :
    abpPrimT (abpInv p) = abpPrimT p := by
  have hc (c : Circuit n) := circuit_count_inv_local .T (fun g _ ↦ by cases g <;> rfl) c
  induction p <;> simp only [abpInv, abpPrimT, *, Nat.add_comm]
@[simp] theorem abpPrimToff_abpInv {n : ℕ} (p : AndBracketProg n) :
    abpPrimToff (abpInv p) = abpPrimToff p := by
  have hc (c : Circuit n) := circuit_count_inv_local .TOFF (fun g _ ↦ by cases g <;> rfl) c
  induction p <;> simp only [abpInv, abpPrimToff, *, Nat.add_comm]
@[simp] theorem abpPrimT_onRegister {M n : ℕ} (r : QRegister M n) (p : AndBracketProg M) :
    abpPrimT (p.onRegister r) = abpPrimT p := by
  induction p <;> simp only [AndBracketProg.onRegister, abpPrimT, Circuit.count_onRegister, *]
@[simp] theorem abpPrimToff_onRegister {M n : ℕ} (r : QRegister M n) (p : AndBracketProg M) :
    abpPrimToff (p.onRegister r) = abpPrimToff p := by
  induction p <;> simp only [AndBracketProg.onRegister, abpPrimToff, Circuit.count_onRegister, *]
theorem count_toDyn_t_gen {Var : Type} {n : ℕ} (v : Var) (p : AndBracketProg n) :
    (p.toDyn v).count .T = 4 * p.numTempAnd + abpPrimT p := by
  induction p with
  | id => rfl
  | prim _ => simp [AndBracketProg.toDyn, AndBracketProg.numTempAnd, abpPrimT]
  | seq p₁ p₂ ih₁ ih₂ =>
      change (p₁.toDyn v).count .T + (p₂.toDyn v).count .T = 4 * (p₁.numTempAnd + p₂.numTempAnd) +
          (abpPrimT p₁ + abpPrimT p₂)
      rw [ih₁, ih₂]
      omega
  | tempAnd c₁ c₂ anc h₁₂ h₁a h₂a body ih =>
      change (andComputeCircuit c₁ c₂ anc h₁₂ h₁a h₂a).count .T + ((body.toDyn v).count .T +
        (andUncomputeDyn v c₁ c₂ anc h₁₂ h₁a h₂a).count .T) = 4 * (1 + body.numTempAnd) +
            abpPrimT body
      rw [count_andComputeCircuit_t, ih, count_andUncomputeDyn_t]
      omega
theorem count_toDyn_toff_gen {Var : Type} {n : ℕ} (v : Var) (p : AndBracketProg n) :
    (p.toDyn v).count .TOFF = abpPrimToff p := by
  induction p with
  | id | prim _ => rfl
  | seq p₁ p₂ ih₁ ih₂ =>
      change (p₁.toDyn v).count .TOFF + (p₂.toDyn v).count .TOFF = abpPrimToff p₁ +
          abpPrimToff p₂
      rw [ih₁, ih₂]
  | tempAnd c₁ c₂ anc h₁₂ h₁a h₂a body ih =>
      change (andComputeCircuit c₁ c₂ anc h₁₂ h₁a h₂a).count .TOFF +
        ((body.toDyn v).count .TOFF + (andUncomputeDyn v c₁ c₂ anc h₁₂ h₁a h₂a).count .TOFF) =
            abpPrimToff body
      rw [count_andComputeCircuit_toff, ih, count_andUncomputeDyn_toff]
      omega
theorem eval_abpInv_eq_inv {M : ℕ} (p : AndBracketProg M) :
    (abpInv p).toCircuit.eval = (p.toCircuit.eval)⁻¹ := by
  refine (inv_eq_of_mul_eq_one_right ?_).symm
  induction p with
  | id => simp [abpInv, AndBracketProg.toCircuit]
  | prim _ => simp only [abpInv, AndBracketProg.toCircuit, Circuit.eval_inverse, mul_inv_cancel]
  | seq p₁ p₂ ih₁ ih₂ =>
      simp only [abpInv, AndBracketProg.toCircuit, Circuit.eval_seq, mul_assoc]
      rw [← mul_assoc p₁.toCircuit.eval, ih₁, one_mul, ih₂]
  | tempAnd c₁ c₂ anc h₁₂ h₁a h₂a body ih =>
      simp only [abpInv, AndBracketProg.toCircuit, Circuit.eval_seq, mul_assoc]
      rw [← mul_assoc _ _ ((abpInv body).toCircuit.eval * _), eval_TOFF_mul_self, one_mul,
        ← mul_assoc body.toCircuit.eval, ih, one_mul, eval_TOFF_mul_self]
theorem abpPrimT_toBracket_zero {M : ℕ} (p : ClassicalBracketProg M) :
    abpPrimT p.toBracket = 0 ∧ abpPrimToff p.toBracket = 0 := by
  induction p <;> simp_all [ClassicalBracketProg.toBracket, abpPrimT, abpPrimToff]
@[simp] theorem abpPrimT_reverse {M : ℕ} (p : AndBracketProg M) :
    abpPrimT p.reverse = abpPrimT p := by
  induction p <;> simp [AndBracketProg.reverse, abpPrimT, *, Nat.add_comm]
@[simp] theorem abpPrimToff_reverse {M : ℕ} (p : AndBracketProg M) :
    abpPrimToff p.reverse = abpPrimToff p := by
  induction p <;> simp [AndBracketProg.reverse, abpPrimToff, *, Nat.add_comm]
theorem andBracketWires_abpInv {M : ℕ} {P : Wire M → Prop} (p : AndBracketProg M)
    (hp : AndBracketWires P p) : AndBracketWires P (abpInv p) := by
  induction p with
  | id => trivial
  | prim _ => exact circWires_inverse hp
  | seq _ _ ih₁ ih₂ => exact ⟨ih₂ hp.2, ih₁ hp.1⟩
  | tempAnd _ _ _ _ _ _ _ ih => exact ⟨hp.1, hp.2.1, hp.2.2.1, ih hp.2.2.2⟩
/-! ## Part 2: `gidneyTAddPhase` -/

def gidneyTAddPhase {M : ℕ} :
    ∀ (m : ℕ) (rA rB rCarry : QRegister m M) (cIn : Wire M),
      rA.DisjointWires rB → rA.DisjointWires rCarry → rB.DisjointWires rCarry →
      cIn ∉ Set.range rA.wires → cIn ∉ Set.range rB.wires → cIn ∉ Set.range rCarry.wires →
      AndBracketProg M
  | 0, _, _, _, cIn, _, _, _, _, _, _ => .prim (Circuit.T cIn)
  | m + 1, rA, rB, rCarry, cIn, hAB, hAC, hBC, hcA, hcB, hcC =>
      let hcA0 : cIn ≠ rA 0 := fun e ↦ hcA ⟨0, e.symm⟩
      let hcB0 : cIn ≠ rB 0 := fun e ↦ hcB ⟨0, e.symm⟩
      let hcC0 : cIn ≠ rCarry 0 := fun e ↦ hcC ⟨0, e.symm⟩
      let hAB0 : rA 0 ≠ rB 0 := hAB.ne 0 0; let hAC0 : rA 0 ≠ rCarry 0 := hAC.ne 0 0;
      let hBC0 : rB 0 ≠ rCarry 0 := hBC.ne 0 0
      let hAB' :
          (PhotochemistrySolution.regTail rA).DisjointWires (PhotochemistrySolution.regTail rB) :=
          QRegister.disjoint_iff.mpr fun i j e ↦ hAB.ne i.succ j.succ e
      let hAC' :
          (PhotochemistrySolution.regTail rA).DisjointWires (PhotochemistrySolution.regTail rCarry)
          := QRegister.disjoint_iff.mpr fun i j e ↦ hAC.ne i.succ j.succ e
      let hBC' :
          (PhotochemistrySolution.regTail rB).DisjointWires (PhotochemistrySolution.regTail rCarry)
          := QRegister.disjoint_iff.mpr fun i j e ↦ hBC.ne i.succ j.succ e
      let hcA' : rCarry 0 ∉ Set.range (PhotochemistrySolution.regTail rA).wires := fun ⟨i, e⟩ ↦
          hAC.ne i.succ 0 e
      let hcB' : rCarry 0 ∉ Set.range (PhotochemistrySolution.regTail rB).wires := fun ⟨i, e⟩ ↦
          hBC.ne i.succ 0 e
      let hcC' : rCarry 0 ∉ Set.range (PhotochemistrySolution.regTail rCarry).wires := fun ⟨i, e⟩ ↦
          Fin.succ_ne_zero i (rCarry.wires.injective e)
      .seq (.prim (.CNOT cIn (rA 0) hcA0))
        (.seq (.prim (.CNOT cIn (rB 0) hcB0))
          (.seq (.tempAnd (rA 0) (rB 0) (rCarry 0) hAB0 hAC0 hBC0
            (.seq (.prim (.CNOT cIn (rCarry 0) hcC0))
              (.seq (gidneyTAddPhase m (PhotochemistrySolution.regTail rA)
                  (PhotochemistrySolution.regTail rB)
                      (PhotochemistrySolution.regTail rCarry)
                          (rCarry 0) hAB' hAC' hBC' hcA' hcB' hcC')
                    (.prim (.CNOT cIn (rCarry 0) hcC0)))))
            (.seq (.prim (.CNOT (rA 0) (rB 0) hAB0))
              (.seq (.prim (.CNOT cIn (rA 0) hcA0))
                    (.prim (.CNOT cIn (rB 0) hcB0))))))
theorem gidneyTailDisj {M m : ℕ} {rA rB rCarry : QRegister (m + 1) M}
    (hAB : rA.DisjointWires rB) (hAC : rA.DisjointWires rCarry) (hBC : rB.DisjointWires rCarry) :
    (PhotochemistrySolution.regTail rA).DisjointWires (PhotochemistrySolution.regTail rB) ∧
    (PhotochemistrySolution.regTail rA).DisjointWires (PhotochemistrySolution.regTail rCarry) ∧
    (PhotochemistrySolution.regTail rB).DisjointWires (PhotochemistrySolution.regTail rCarry) ∧
    rCarry 0 ∉ Set.range (PhotochemistrySolution.regTail rA).wires ∧
    rCarry 0 ∉ Set.range (PhotochemistrySolution.regTail rB).wires ∧
    rCarry 0 ∉ Set.range (PhotochemistrySolution.regTail rCarry).wires :=
  ⟨QRegister.disjoint_iff.mpr fun i j e ↦ hAB.ne i.succ j.succ e,
   QRegister.disjoint_iff.mpr fun i j e ↦ hAC.ne i.succ j.succ e,
   QRegister.disjoint_iff.mpr fun i j e ↦ hBC.ne i.succ j.succ e,
   fun ⟨i, e⟩ ↦ hAC.ne i.succ 0 e, fun ⟨i, e⟩ ↦ hBC.ne i.succ 0 e,
   fun ⟨i, e⟩ ↦ Fin.succ_ne_zero i (rCarry.wires.injective e)⟩
theorem gidneyTAddPhase_counts {M : ℕ} :
    ∀ (m : ℕ) (rA rB rCarry : QRegister m M) (cIn : Wire M)
      (hAB : rA.DisjointWires rB) (hAC : rA.DisjointWires rCarry) (hBC : rB.DisjointWires rCarry)
      (hcA : cIn ∉ Set.range rA.wires) (hcB : cIn ∉ Set.range rB.wires)
      (hcC : cIn ∉ Set.range rCarry.wires),
      (gidneyTAddPhase m rA rB rCarry cIn hAB hAC hBC hcA hcB hcC).numTempAnd = m ∧
      abpPrimT (gidneyTAddPhase m rA rB rCarry cIn hAB hAC hBC hcA hcB hcC) = 1 ∧
      abpPrimToff (gidneyTAddPhase m rA rB rCarry cIn hAB hAC hBC hcA hcB hcC) = 0
  | 0, _, _, _, _, _, _, _, _, _, _ => ⟨rfl, rfl, rfl⟩
  | m + 1, rA, rB, rCarry, cIn, hAB, hAC, hBC, hcA, hcB, hcC => by
      let d := gidneyTailDisj hAB hAC hBC
      obtain ⟨ihA, ihT, ihF⟩ :=
          gidneyTAddPhase_counts m _ _ _ (rCarry 0) d.1 d.2.1 d.2.2.1 d.2.2.2.1 d.2.2.2.2.1
          d.2.2.2.2.2
      exact ⟨by
        simp [gidneyTAddPhase, AndBracketProg.numTempAnd, ihA]
        omega,
        by simp [gidneyTAddPhase, abpPrimT, ihT], by simp [gidneyTAddPhase, abpPrimToff, ihF]⟩
theorem andBracketWires_gidneyTAddPhase {M : ℕ} {P : Wire M → Prop} :
    ∀ (m : ℕ) (rA rB rCarry : QRegister m M) (cIn : Wire M)
      (hAB : rA.DisjointWires rB) (hAC : rA.DisjointWires rCarry) (hBC : rB.DisjointWires rCarry)
      (hcA : cIn ∉ Set.range rA.wires) (hcB : cIn ∉ Set.range rB.wires)
      (hcC : cIn ∉ Set.range rCarry.wires),
      (∀ i : Fin m, P (rA i)) → (∀ i : Fin m, P (rB i)) →
      (∀ i : Fin m, P (rCarry i)) → P cIn →
      AndBracketWires P (gidneyTAddPhase m rA rB rCarry cIn hAB hAC hBC hcA hcB hcC)
  | 0, _, _, _, _, _, _, _, _, _, _, _, _, _, hc => fun ⟨0, _⟩ ↦ hc
  | m + 1, _, _, rCarry, _, hAB, hAC, hBC, _, _, _, hA, hB, hC, hc =>
      let d := gidneyTailDisj hAB hAC hBC
      have hp2 {a b : Wire M} {h : a ≠ b} (ha : P a) (hb : P b) : CircWires P (.CNOT a b h) :=
        fun | ⟨0, _⟩ => ha | ⟨1, _⟩ => hb
      have ih :=
          andBracketWires_gidneyTAddPhase m _ _ _ (rCarry 0) d.1 d.2.1 d.2.2.1 d.2.2.2.1 d.2.2.2.2.1
          d.2.2.2.2.2
        (fun i ↦ hA i.succ) (fun i ↦ hB i.succ) (fun i ↦ hC i.succ) (hC 0)
      ⟨hp2 hc (hA 0), hp2 hc (hB 0), ⟨hA 0, hB 0, hC 0, ⟨hp2 hc (hC 0), ih, hp2 hc (hC 0)⟩⟩,
        hp2 (hA 0) (hB 0), hp2 hc (hA 0), hp2 hc (hB 0)⟩
def conjTAddProg {M : ℕ} (prep : ClassicalBracketProg M) (m : ℕ) (rA rB rCarry : QRegister m M)
    (cIn : Wire M) (hAB : rA.DisjointWires rB) (hAC : rA.DisjointWires rCarry)
    (hBC : rB.DisjointWires rCarry) (hcA : cIn ∉ Set.range rA.wires)
    (hcB : cIn ∉ Set.range rB.wires) (hcC : cIn ∉ Set.range rCarry.wires) : AndBracketProg M :=
  .seq prep.toBracket
    (.seq (gidneyTAddPhase m rA rB rCarry cIn hAB hAC hBC hcA hcB hcC)
      prep.toBracket.reverse)
/-! ## Part 3: `98-T` 5-Catalyst-Bit Post-Cancel `QFT8` Circuit -/

def layerJ1DirectCirc {M : ℕ} (rP : QRegister 8 M) : Circuit M :=
  Circuit.T (rP 1) ;;ᶜ
  Circuit.CNOT (rP 0) (rP 1) (rP.wires.injective.ne (fin8_ne rfl)) ;;ᶜ
  (Circuit.T (rP 1)).inverse ;;ᶜ
  Circuit.CNOT (rP 0) (rP 1) (rP.wires.injective.ne (fin8_ne rfl))
def layerJTopTSCirc {M : ℕ} (pPrev pJ : Wire M) (hne : pPrev ≠ pJ) : Circuit M :=
  Circuit.CNOT pPrev pJ hne ;;ᶜ
  (Circuit.T pJ).inverse ;;ᶜ
  Circuit.CNOT pPrev pJ hne ;;ᶜ
  Circuit.S pJ
theorem prepJT5_step_bounds {m : ℕ} (hm : m + 1 ≤ 5) : m ≤ 5 ∧ m < 7 ∧ m < 8 := by omega
def prepJT5Prefix {M : ℕ} (rP : QRegister 8 M) (rDelta : QRegister 7 M)
    (hPDelta : rP.DisjointWires rDelta) (j : Fin 8) :
    ∀ (m : ℕ), m ≤ 5 → ClassicalBracketProg M
  | 0, _ => .id
  | m + 1, hm =>
      let hb := prepJT5_step_bounds hm
      .seq (prepJT5Prefix rP rDelta hPDelta j m hb.1)
        (.seq (.x (rDelta ⟨m, hb.2.1⟩))
          (.seq (.cnot (rP ⟨m, hb.2.2⟩) (rDelta ⟨m, hb.2.1⟩) (hPDelta.ne _ _))
            (.cnot (rP j) (rDelta ⟨m, hb.2.1⟩) (hPDelta.ne _ _))))
def prepJT5 {M : ℕ} (rP : QRegister 8 M) (rDelta : QRegister 7 M)
    (hPDelta : rP.DisjointWires rDelta) (j : Fin 8) (m : ℕ) (hm : m ≤ 5) : ClassicalBracketProg M :=
    .seq (prepJT5Prefix rP rDelta hPDelta j m hm) (.x (rP j))
theorem layerJT5_bounds {j : Fin 8} (hj2 : 2 ≤ j.val) (hj7 : j.val < 7) :
    0 + (j.val - 1) ≤ 7 ∧ (6 - j.val) + (j.val - 1) ≤ 8 ∧
    0 + (j.val - 1) ≤ 6 ∧ j.val - 1 ≤ 5 ∧ j.val - 1 < 8 := by omega
theorem layerJT5_disj {M : ℕ} {rCat rP : QRegister 8 M} {rDelta : QRegister 7 M}
    {rCarry : QRegister 6 M}
    (hPCat : rP.DisjointWires rCat) (hPDelta : rP.DisjointWires rDelta)
    (hDCat : rDelta.DisjointWires rCat) (hDCarry : rDelta.DisjointWires rCarry)
    (hCatCarry : rCat.DisjointWires rCarry) (hPCarry : rP.DisjointWires rCarry)
    (j : Fin 8) (hj2 : 2 ≤ j.val) (hj7 : j.val < 7) :
    let hb := layerJT5_bounds hj2 hj7; let m := j.val - 1; let rA := rDelta.slice 0 m hb.1;
    let rB := rCat.slice (6 - j.val) m hb.2.1; let rC := rCarry.slice 0 m hb.2.2.1
    rA.DisjointWires rB ∧ rA.DisjointWires rC ∧ rB.DisjointWires rC ∧
    rP j ∉ Set.range rA.wires ∧ rP j ∉ Set.range rB.wires ∧ rP j ∉ Set.range rC.wires :=
  ⟨QRegister.disjoint_iff.mpr fun a b e ↦ hDCat.ne ⟨0 + a.val, by omega⟩
      ⟨(6 - j.val) + b.val, by omega⟩ e,
   QRegister.disjoint_iff.mpr fun a b e ↦ hDCarry.ne ⟨0 + a.val, by omega⟩ ⟨0 + b.val, by omega⟩ e,
   QRegister.disjoint_iff.mpr fun a b e ↦ hCatCarry.ne ⟨(6 - j.val) + a.val, by omega⟩
      ⟨0 + b.val, by omega⟩ e,
   fun ⟨a, e⟩ ↦ hPDelta.ne j ⟨0 + a.val, by omega⟩ e.symm,
   fun ⟨a, e⟩ ↦ hPCat.ne j ⟨(6 - j.val) + a.val, by omega⟩ e.symm,
   fun ⟨a, e⟩ ↦ hPCarry.ne j ⟨0 + a.val, by omega⟩ e.symm⟩
def layerJT5Inner {M : ℕ} (rCat rP : QRegister 8 M) (rDelta : QRegister 7 M)
    (rCarry : QRegister 6 M) (hPCat : rP.DisjointWires rCat) (hPDelta : rP.DisjointWires rDelta)
    (hDCat : rDelta.DisjointWires rCat) (hDCarry : rDelta.DisjointWires rCarry)
    (hCatCarry : rCat.DisjointWires rCarry) (hPCarry : rP.DisjointWires rCarry) (j : Fin 8)
    (hj2 : 2 ≤ j.val) (hj7 : j.val < 7) : AndBracketProg M :=
  let hb := layerJT5_bounds hj2 hj7;
  let hd := layerJT5_disj hPCat hPDelta hDCat hDCarry hCatCarry hPCarry j hj2 hj7;
  let jPrev : Fin 8 := ⟨j.val - 1, hb.2.2.2.2⟩
  have hnePrev : rP jPrev ≠ rP j := rP.wires.injective.ne (fun e ↦ by
    have hv := congrArg Fin.val e; change j.val - 1 = j.val at hv; omega)
  .seq
    (conjTAddProg (prepJT5 rP rDelta hPDelta j (j.val - 1) hb.2.2.2.1) (j.val - 1)
      (rDelta.slice 0 (j.val - 1) hb.1) (rCat.slice (6 - j.val) (j.val - 1) hb.2.1)
      (rCarry.slice 0 (j.val - 1) hb.2.2.1) (rP j)
      hd.1 hd.2.1 hd.2.2.1 hd.2.2.2.1 hd.2.2.2.2.1 hd.2.2.2.2.2)
    (.prim (layerJTopTSCirc (rP jPrev) (rP j) hnePrev))
def layerJT5Bracket {M : ℕ} (rCat rP : QRegister 8 M) (rDelta : QRegister 7 M)
    (rCarry : QRegister 6 M) (hPCat : rP.DisjointWires rCat) (hPDelta : rP.DisjointWires rDelta)
    (hDCat : rDelta.DisjointWires rCat) (hDCarry : rDelta.DisjointWires rCarry)
    (hCatCarry : rCat.DisjointWires rCarry) (hPCarry : rP.DisjointWires rCarry) (j : Fin 8)
    (hj2 : 2 ≤ j.val) (hj7 : j.val < 7) : AndBracketProg M :=
  let hb := layerJT5_bounds hj2 hj7;
  let hd := layerJT5_disj hPCat hPDelta hDCat hDCarry hCatCarry hPCarry j hj2 hj7;
  let jPrev : Fin 8 := ⟨j.val - 1, hb.2.2.2.2⟩
  have hnePrev : rP jPrev ≠ rP j := rP.wires.injective.ne (fun e ↦ by
    have hv := congrArg Fin.val e; change j.val - 1 = j.val at hv; omega)
  .seq
    (conjTAddProg (prepJT5 rP rDelta hPDelta j (j.val - 1) hb.2.2.2.1) (j.val - 1)
      (rDelta.slice 0 (j.val - 1) hb.1) (rCat.slice (6 - j.val) (j.val - 1) hb.2.1)
      (rCarry.slice 0 (j.val - 1) hb.2.2.1) (rP j)
      hd.1 hd.2.1 hd.2.2.1 hd.2.2.2.1 hd.2.2.2.2.1 hd.2.2.2.2.2)
    (.seq (.prim (layerJTopTSCirc (rP jPrev) (rP j) hnePrev))
          (.prim (.H (rP j))))
theorem slice05_le7 : 0 + 5 ≤ 7 := by omega
theorem slice05_le8 : 0 + 5 ≤ 8 := by omega
theorem slice05_le6 : 0 + 5 ≤ 6 := by omega
theorem layerJ7T5_disj {M : ℕ} {rCat : QRegister 8 M} {rDelta : QRegister 7 M}
    {rCarry : QRegister 6 M} (hDCat : rDelta.DisjointWires rCat)
    (hDCarry : rDelta.DisjointWires rCarry) (hCatCarry : rCat.DisjointWires rCarry) :
    (rDelta.slice 0 5 slice05_le7).DisjointWires (rCat.slice 0 5 slice05_le8) ∧
    (rDelta.slice 0 5 slice05_le7).DisjointWires (rCarry.slice 0 5 slice05_le6) ∧
    (rCat.slice 0 5 slice05_le8).DisjointWires (rCarry.slice 0 5 slice05_le6) ∧
    rDelta 5 ∉ Set.range (rDelta.slice 0 5 slice05_le7).wires ∧
    rDelta 5 ∉ Set.range (rCat.slice 0 5 slice05_le8).wires ∧
    rDelta 5 ∉ Set.range (rCarry.slice 0 5 slice05_le6).wires :=
  ⟨QRegister.disjoint_iff.mpr fun a b e ↦ hDCat.ne ⟨0 + a.val, by omega⟩ ⟨0 + b.val, by omega⟩ e,
   QRegister.disjoint_iff.mpr fun a b e ↦ hDCarry.ne ⟨0 + a.val, by omega⟩ ⟨0 + b.val, by omega⟩ e,
   QRegister.disjoint_iff.mpr fun a b e ↦
       hCatCarry.ne ⟨0 + a.val, by omega⟩ ⟨0 + b.val, by omega⟩ e,
   fun ⟨a, e⟩ ↦ by
     have hv := congrArg Fin.val (rDelta.wires.injective e)
     change 0 + a.val = 5 at hv; omega,
   fun ⟨a, e⟩ ↦ hDCat.ne 5 ⟨0 + a.val, by omega⟩ e.symm,
   fun ⟨a, e⟩ ↦ hDCarry.ne 5 ⟨0 + a.val, by omega⟩ e.symm⟩
def prepJ7T5 {M : ℕ} (rP : QRegister 8 M) (rDelta : QRegister 7 M)
    (hPDelta : rP.DisjointWires rDelta) : ClassicalBracketProg M :=
    .seq (.seq (.x (rDelta 0)) (.seq (.cnot (rP 1) (rDelta 0) (hPDelta.ne 1 0))
    (.cnot (rP 7) (rDelta 0) (hPDelta.ne 7 0))))
    (.seq (.seq (.x (rDelta 1)) (.seq (.cnot (rP 2) (rDelta 1) (hPDelta.ne 2 1))
    (.cnot (rP 7) (rDelta 1) (hPDelta.ne 7 1))))
    (.seq (.seq (.x (rDelta 2)) (.seq (.cnot (rP 3) (rDelta 2) (hPDelta.ne 3 2))
    (.cnot (rP 7) (rDelta 2) (hPDelta.ne 7 2))))
    (.seq (.seq (.x (rDelta 3)) (.seq (.cnot (rP 4) (rDelta 3) (hPDelta.ne 4 3))
    (.cnot (rP 7) (rDelta 3) (hPDelta.ne 7 3))))
    (.seq (.seq (.x (rDelta 4)) (.seq (.cnot (rP 5) (rDelta 4) (hPDelta.ne 5 4))
    (.cnot (rP 7) (rDelta 4) (hPDelta.ne 7 4)))) (.seq (.x (rDelta 5)) (.cnot (rP 7) (rDelta 5)
    (hPDelta.ne 7 5)))))))
def layerJ7T5Inner {M : ℕ} (rCat rP : QRegister 8 M) (rDelta : QRegister 7 M)
    (rCarry : QRegister 6 M) (hPDelta : rP.DisjointWires rDelta) (hDCat : rDelta.DisjointWires rCat)
    (hDCarry : rDelta.DisjointWires rCarry) (hCatCarry : rCat.DisjointWires rCarry) :
    AndBracketProg M :=
  let h := layerJ7T5_disj hDCat hDCarry hCatCarry
  .seq
    (.tempAnd (rP 7) (rP 0) (rDelta 5)
      (rP.wires.injective.ne (fin8_ne rfl)) (hPDelta.ne 7 5) (hPDelta.ne 0 5)
      (conjTAddProg (prepJ7T5 rP rDelta hPDelta) 5
        (rDelta.slice 0 5 slice05_le7) (rCat.slice 0 5 slice05_le8)
        (rCarry.slice 0 5 slice05_le6) (rDelta 5)
        h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2))
    (.prim (layerJTopTSCirc (rP 6) (rP 7) (rP.wires.injective.ne (fin8_ne rfl))))
def layerJ7T5Bracket {M : ℕ} (rCat rP : QRegister 8 M) (rDelta : QRegister 7 M)
    (rCarry : QRegister 6 M) (hPDelta : rP.DisjointWires rDelta) (hDCat : rDelta.DisjointWires rCat)
    (hDCarry : rDelta.DisjointWires rCarry) (hCatCarry : rCat.DisjointWires rCarry) :
    AndBracketProg M :=
  let h := layerJ7T5_disj hDCat hDCarry hCatCarry
  .seq
    (.tempAnd (rP 7) (rP 0) (rDelta 5)
      (rP.wires.injective.ne (fin8_ne rfl)) (hPDelta.ne 7 5) (hPDelta.ne 0 5)
      (conjTAddProg (prepJ7T5 rP rDelta hPDelta) 5
        (rDelta.slice 0 5 slice05_le7) (rCat.slice 0 5 slice05_le8)
        (rCarry.slice 0 5 slice05_le6) (rDelta 5)
        h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2))
    (.seq (.prim (layerJTopTSCirc (rP 6) (rP 7) (rP.wires.injective.ne (fin8_ne rfl))))
          (.prim (.H (rP 7))))
def postCancelT5MidRange {M : ℕ} (rCat rP : QRegister 8 M) (rDelta : QRegister 7 M)
    (rCarry : QRegister 6 M) (hPCat : rP.DisjointWires rCat) (hPDelta : rP.DisjointWires rDelta)
    (hDCat : rDelta.DisjointWires rCat) (hDCarry : rDelta.DisjointWires rCarry)
    (hCatCarry : rCat.DisjointWires rCarry) (hPCarry : rP.DisjointWires rCarry) (j : ℕ)
    (h2 : 2 ≤ j) : AndBracketProg M :=
    if hj7 : j <
    7 then .seq (layerJT5Bracket rCat rP rDelta rCarry hPCat hPDelta hDCat hDCarry hCatCarry hPCarry
    ⟨j, Nat.lt_trans hj7 (Nat.lt_succ_self 7)⟩ h2 hj7)
    (postCancelT5MidRange rCat rP rDelta rCarry hPCat hPDelta hDCat hDCarry hCatCarry hPCarry (j +
    1) (Nat.le_succ_of_le h2)) else .id
termination_by 7 - j
def polyPostCancelT5Qft8Bracket98 {M : ℕ} (rCat rP : QRegister 8 M) (rDelta : QRegister 7 M)
    (rCarry : QRegister 6 M) (hPCat : rP.DisjointWires rCat) (hPDelta : rP.DisjointWires rDelta)
    (hDCat : rDelta.DisjointWires rCat) (hDCarry : rDelta.DisjointWires rCarry)
    (hCatCarry : rCat.DisjointWires rCarry) (hPCarry : rP.DisjointWires rCarry) :
    AndBracketProg M :=
  .seq (.prim (polySwapAll8Circ rP ;;ᶜ Circuit.H (rP 0) ;;ᶜ layerJ1DirectCirc rP ;;ᶜ Circuit.H
      (rP 1)))
    (.seq
      (postCancelT5MidRange rCat rP rDelta rCarry hPCat hPDelta hDCat hDCarry hCatCarry hPCarry
        2 (Nat.le_refl 2))
      (layerJ7T5Bracket rCat rP rDelta rCarry hPDelta hDCat hDCarry hCatCarry))
abbrev qft8PostCancel98Bracket (scrW off : ℕ) (hoff : 1 ≤ off ∧ off + 21 ≤ scrW)
    (rP : QRegister 8 (totDimCompactGen scrW)) (hP : Qft8Stg3ValidP scrW off rP) :
    AndBracketProg (totDimCompactGen scrW) :=
    polyPostCancelT5Qft8Bracket98 (locCat8SharedCompactGen scrW) rP (qft8Stg3Delta7 scrW off hoff)
    (qft8Stg3Carry6 scrW off hoff) (qft8Stg3_rP_disj_cat8 hP) (qft8Stg3_rP_disj_delta7 hoff hP)
    (qft8Stg3_delta7_disj_cat8 hoff) (qft8Stg3_delta7_disj_carry6 hoff)
    (qft8Stg3_cat8_disj_carry6 hoff) (qft8Stg3_rP_disj_carry6 hoff hP)
def pQft8PostCancel98Fwd {Var : Type} {n : ℕ} (v : Var) (scrW off : ℕ)
    (hoff : 1 ≤ off ∧ off + 21 ≤ scrW) (rTot : QRegister (totDimCompactGen scrW) n)
    (rP : QRegister 8 (totDimCompactGen scrW)) (hP : Qft8Stg3ValidP scrW off rP) :
    DynamicCircuit Var n := ((qft8PostCancel98Bracket scrW off hoff rP hP).onRegister rTot).toDyn v
def pQft8PostCancel98Rev {Var : Type} {n : ℕ} (v : Var) (scrW off : ℕ)
    (hoff : 1 ≤ off ∧ off + 21 ≤ scrW) (rTot : QRegister (totDimCompactGen scrW) n)
    (rP : QRegister 8 (totDimCompactGen scrW)) (hP : Qft8Stg3ValidP scrW off rP) :
    DynamicCircuit Var n :=
  ((abpInv (qft8PostCancel98Bracket scrW off hoff rP hP)).onRegister rTot).toDyn v
/-! ## Part 5: Exact Gate Counts & Tight Wire Footprint Proofs -/

theorem prepJT5Prefix_zero_and_disj {M : ℕ} {P : Wire M → Prop}
    (rP : QRegister 8 M) (rDelta : QRegister 7 M) (hPDelta : rP.DisjointWires rDelta)
    (j : Fin 8) (hP : ∀ i : Fin 8, P (rP i))
    (hD : ∀ i : Fin 5, P (rDelta ⟨i.val, by omega⟩)) :
    ∀ (m : ℕ) (hm : m ≤ 5),
      (prepJT5Prefix rP rDelta hPDelta j m hm).numTempAnd = 0 ∧
      CBPDisj P (prepJT5Prefix rP rDelta hPDelta j m hm)
  | 0, _ => ⟨rfl, trivial⟩
  | m + 1, hm =>
      let ⟨ih0, ihd⟩ := prepJT5Prefix_zero_and_disj rP rDelta hPDelta j hP hD m (by omega)
      have hd_m : P (rDelta ⟨m, (prepJT5_step_bounds hm).2.1⟩) := hD ⟨m, by omega⟩
      ⟨by simp [prepJT5Prefix, ClassicalBracketProg.numTempAnd, ih0],
        ⟨ihd, hd_m, ⟨hP _, hd_m⟩, ⟨hP _, hd_m⟩⟩⟩
theorem prepJT5_zero_and_disj {M : ℕ} {P : Wire M → Prop}
    (rP : QRegister 8 M) (rDelta : QRegister 7 M) (hPDelta : rP.DisjointWires rDelta)
    (j : Fin 8) (m : ℕ) (hm : m ≤ 5)
    (hP : ∀ i : Fin 8, P (rP i))
    (hD : ∀ i : Fin 5, P (rDelta ⟨i.val, by omega⟩)) :
    (prepJT5 rP rDelta hPDelta j m hm).numTempAnd = 0 ∧
    CBPDisj P (prepJT5 rP rDelta hPDelta j m hm) := by
  obtain ⟨h0, hd⟩ := prepJT5Prefix_zero_and_disj rP rDelta hPDelta j hP hD m hm
  exact ⟨by simp [prepJT5, ClassicalBracketProg.numTempAnd, h0], ⟨hd, hP _⟩⟩
theorem prepJ7T5_zero_and_disj {M : ℕ} {P : Wire M → Prop}
    (rP : QRegister 8 M) (rDelta : QRegister 7 M) (hPDelta : rP.DisjointWires rDelta)
    (hP : ∀ i : Fin 8, P (rP i))
    (hD : ∀ i : Fin 6, P (rDelta ⟨i.val, by omega⟩)) :
    (prepJ7T5 rP rDelta hPDelta).numTempAnd = 0 ∧
    CBPDisj P (prepJ7T5 rP rDelta hPDelta) :=
  ⟨rfl, ⟨⟨hD 0, ⟨hP 1, hD 0⟩, hP 7, hD 0⟩,
    ⟨hD 1, ⟨hP 2, hD 1⟩, hP 7, hD 1⟩,
    ⟨hD 2, ⟨hP 3, hD 2⟩, hP 7, hD 2⟩,
    ⟨hD 3, ⟨hP 4, hD 3⟩, hP 7, hD 3⟩,
    ⟨hD 4, ⟨hP 5, hD 4⟩, hP 7, hD 4⟩,
    hD 5, hP 7, hD 5⟩⟩
theorem layerJ7T5Bracket_counts {M : ℕ} (rCat rP : QRegister 8 M) (rDelta : QRegister 7 M)
    (rCarry : QRegister 6 M) (hPDelta : rP.DisjointWires rDelta) (hDCat : rDelta.DisjointWires rCat)
    (hDCarry : rDelta.DisjointWires rCarry) (hCatCarry : rCat.DisjointWires rCarry) :
    (layerJ7T5Bracket rCat rP rDelta rCarry hPDelta hDCat hDCarry hCatCarry).numTempAnd = 6 ∧
    abpPrimT (layerJ7T5Bracket rCat rP rDelta rCarry hPDelta hDCat hDCarry hCatCarry) = 2 ∧
    abpPrimToff (layerJ7T5Bracket rCat rP rDelta rCarry hPDelta hDCat hDCarry hCatCarry) = 0 := by
  let h := layerJ7T5_disj hDCat hDCarry hCatCarry
  obtain ⟨hA, hT, hF⟩ := gidneyTAddPhase_counts 5 (rDelta.slice 0 5 slice05_le7)
    (rCat.slice 0 5 slice05_le8) (rCarry.slice 0 5 slice05_le6)
        (rDelta 5) h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2
  obtain ⟨hpT, hpF⟩ := abpPrimT_toBracket_zero (prepJ7T5 rP rDelta hPDelta)
  exact
      ⟨by simp [layerJ7T5Bracket, conjTAddProg, AndBracketProg.numTempAnd,
            AndBracketProg.numTempAnd_reverse, hA,
      show (prepJ7T5 rP rDelta hPDelta).toBracket.numTempAnd = 0 from rfl],
    by simp [layerJ7T5Bracket, conjTAddProg, abpPrimT, hpT, hT,
      show (layerJTopTSCirc (rP 6) (rP 7) (rP.wires.injective.ne (fin8_ne rfl))).count .T =
          1 from rfl],
    by simp [layerJ7T5Bracket, conjTAddProg, abpPrimToff, hpF, hF,
      show (layerJTopTSCirc (rP 6) (rP 7) (rP.wires.injective.ne (fin8_ne rfl))).count .TOFF =
          0 from rfl]⟩
theorem postCancelT5MidRange_step_counts {M : ℕ}
    (rCat rP : QRegister 8 M) (rDelta : QRegister 7 M) (rCarry : QRegister 6 M)
    (hPCat : rP.DisjointWires rCat) (hPDelta : rP.DisjointWires rDelta)
    (hDCat : rDelta.DisjointWires rCat) (hDCarry : rDelta.DisjointWires rCarry)
    (hCatCarry : rCat.DisjointWires rCarry) (hPCarry : rP.DisjointWires rCarry)
    (j : ℕ) (h2 : 2 ≤ j) (hj7 : j < 7) :
    let cur :=
        postCancelT5MidRange rCat rP rDelta rCarry hPCat hPDelta hDCat hDCarry hCatCarry hPCarry j
        h2
    let nxt :=
        postCancelT5MidRange rCat rP rDelta rCarry hPCat hPDelta hDCat hDCarry hCatCarry hPCarry
        (j + 1) (Nat.le_succ_of_le h2)
    cur.numTempAnd = (j - 1) + nxt.numTempAnd ∧ abpPrimT cur = 2 + abpPrimT nxt ∧ abpPrimToff cur =
        abpPrimToff nxt := by
  let jf : Fin 8 := ⟨j, Nat.lt_trans hj7 (Nat.lt_succ_self 7)⟩
  let hb := layerJT5_bounds (j := jf) h2 hj7
  let hd := layerJT5_disj hPCat hPDelta hDCat hDCarry hCatCarry hPCarry jf h2 hj7
  obtain ⟨hA, hT, hF⟩ := gidneyTAddPhase_counts (jf.val - 1) (rDelta.slice 0 (jf.val - 1) hb.1)
    (rCat.slice (6 - jf.val) (jf.val - 1) hb.2.1) (rCarry.slice 0 (jf.val - 1) hb.2.2.1) (rP jf)
    hd.1 hd.2.1 hd.2.2.1 hd.2.2.2.1 hd.2.2.2.2.1 hd.2.2.2.2.2
  have hp0 : (prepJT5 rP rDelta hPDelta jf (jf.val - 1) hb.2.2.2.1).toBracket.numTempAnd = 0 :=
    (ClassicalBracketProg.toBracket_numTempAnd _).trans ((prepJT5_zero_and_disj (P := fun _ ↦
        True) rP rDelta hPDelta
      jf (jf.val - 1) hb.2.2.2.1 (fun _ ↦ trivial) (fun _ ↦ trivial)).1)
  obtain ⟨hpT, hpF⟩ :=
      abpPrimT_toBracket_zero (prepJT5 rP rDelta hPDelta jf (jf.val - 1) hb.2.2.2.1)
  intro cur nxt
  have hcur : cur =
      .seq (layerJT5Bracket rCat rP rDelta rCarry hPCat hPDelta hDCat hDCarry hCatCarry hPCarry jf
      h2 hj7) nxt := by
    dsimp only [cur, nxt]
    conv_lhs => unfold postCancelT5MidRange
    exact dite_eq_left hj7
  have hts (u w : Wire M) (h : u ≠ w) : (layerJTopTSCirc u w h).count .T = 1 ∧
      (layerJTopTSCirc u w h).count .TOFF = 0 := ⟨rfl, rfl⟩
  rw [hcur]
  refine ⟨?_,
      by simp only [abpPrimT, layerJT5Bracket, conjTAddProg, abpPrimT_reverse, hpT, hT,
           (hts _ _ _).1,
      show (Circuit.H (rP jf)).count .T = 0 from rfl],
    by
      simp only [abpPrimToff, layerJT5Bracket, conjTAddProg, abpPrimToff_reverse, hpF, hF,
         (hts _ _ _).2,
      show (Circuit.H (rP jf)).count .TOFF = 0 from rfl]
      omega⟩
  simp only [AndBracketProg.numTempAnd, layerJT5Bracket, conjTAddProg,
      AndBracketProg.numTempAnd_reverse, hp0, hA]
  change 0 + ((j - 1) + 0) + (0 + 0) + _ = _
  omega
theorem polyPostCancelT5Qft8Bracket98_counts {M : ℕ}
    (rCat rP : QRegister 8 M) (rDelta : QRegister 7 M) (rCarry : QRegister 6 M)
    (hPCat : rP.DisjointWires rCat) (hPDelta : rP.DisjointWires rDelta)
    (hDCat : rDelta.DisjointWires rCat) (hDCarry : rDelta.DisjointWires rCarry)
    (hCatCarry : rCat.DisjointWires rCarry) (hPCarry : rP.DisjointWires rCarry) :
    let br :=
        polyPostCancelT5Qft8Bracket98 rCat rP rDelta rCarry hPCat hPDelta hDCat hDCarry hCatCarry
        hPCarry
    br.numTempAnd = 21 ∧ abpPrimT br = 14 ∧ abpPrimToff br = 0 := by
  have h7 :
      postCancelT5MidRange rCat rP rDelta rCarry hPCat hPDelta hDCat hDCarry hCatCarry hPCarry 7
      (by omega) = .id := by
    unfold postCancelT5MidRange
    exact dite_eq_right (by omega)
  let stp (j : ℕ) (h2 : 2 ≤ j) (hj7 : j < 7) :=
    postCancelT5MidRange_step_counts rCat rP rDelta rCarry hPCat hPDelta hDCat hDCarry hCatCarry
        hPCarry j h2 hj7
  obtain ⟨⟨a2, t2, f2⟩, ⟨a3, t3, f3⟩, ⟨a4, t4, f4⟩, ⟨a5, t5, f5⟩, ⟨a6, t6, f6⟩⟩ : _ ∧ _ ∧ _ ∧ _ ∧
      _ :=
    ⟨stp 2 (by omega) (by omega), stp 3 (by omega) (by omega), stp 4 (by omega) (by omega),
      stp 5 (by omega) (by omega), stp 6 (by omega) (by omega)⟩
  obtain ⟨l7A, l7T, l7F⟩ :=
      layerJ7T5Bracket_counts rCat rP rDelta rCarry hPDelta hDCat hDCarry hCatCarry
  have hpreT :
      (polySwapAll8Circ rP ;;ᶜ Circuit.H (rP 0) ;;ᶜ layerJ1DirectCirc rP ;;ᶜ Circuit.H (rP 1)).count
      .T = 2 := rfl
  have hpreF :
      (polySwapAll8Circ rP ;;ᶜ Circuit.H (rP 0) ;;ᶜ layerJ1DirectCirc rP ;;ᶜ Circuit.H (rP 1)).count
      .TOFF = 0 := rfl
  exact
      ⟨by simp only [polyPostCancelT5Qft8Bracket98, AndBracketProg.numTempAnd, h7, l7A, a2, a3, a4,
            a5, a6],
    by simp only [polyPostCancelT5Qft8Bracket98, abpPrimT, hpreT, h7, l7T, t2, t3, t4, t5, t6],
    by simp only [polyPostCancelT5Qft8Bracket98, abpPrimToff, hpreF, h7, l7F, f2, f3, f4, f5, f6]⟩
theorem andBracketWires_polyPostCancelT5Qft8Bracket98 {M : ℕ} {P : Wire M → Prop}
    (rCat rP : QRegister 8 M) (rDelta : QRegister 7 M) (rCarry : QRegister 6 M)
    (hPCat : rP.DisjointWires rCat) (hPDelta : rP.DisjointWires rDelta)
    (hDCat : rDelta.DisjointWires rCat) (hDCarry : rDelta.DisjointWires rCarry)
    (hCatCarry : rCat.DisjointWires rCarry) (hPCarry : rP.DisjointWires rCarry)
    (hCat5 : ∀ i : Fin 5, P (rCat ⟨i.val, by omega⟩))
    (hP : ∀ i : Fin 8, P (rP i))
    (hD6 : ∀ i : Fin 6, P (rDelta ⟨i.val, by omega⟩))
    (hC5 : ∀ i : Fin 5, P (rCarry ⟨i.val, by omega⟩)) :
    AndBracketWires P (polyPostCancelT5Qft8Bracket98 rCat rP rDelta rCarry
      hPCat hPDelta hDCat hDCarry hCatCarry hPCarry) := by
  have hp1 {g : PrimitiveGate 1} {u : Wire M}
      (hu : P u) : CircWires P (.gate g (QRegister.singleton u)) := fun ⟨0, _⟩ ↦ hu
  have hp2 {a b : Wire M} {h : a ≠ b} (ha : P a) (hb : P b) : CircWires P (.CNOT a b h) :=
      fun | ⟨0, _⟩ => ha | ⟨1, _⟩ => hb
  have hsw2 (a b : Fin 8) (h : rP a ≠ rP b) : CircWires P (polySwapWire2Circ (rP a) (rP b) h) :=
    ⟨hp2 (hP a) (hP b), hp2 (hP b) (hP a), hp2 (hP a) (hP b)⟩
  have hts {u w : Wire M} {hne : u ≠ w} (hu : P u)
      (hw : P w) : CircWires P (layerJTopTSCirc u w hne) :=
    ⟨hp2 hu hw, circWires_inverse (hp1 hw), hp2 hu hw, hp1 hw⟩
  have hw_conj {prep : ClassicalBracketProg M} {m : ℕ} {rA rB rCr : QRegister m M} {cIn : Wire M}
      {hAB hAC hBC hcA hcB hcC} (hp : CBPDisj P prep) (hA : ∀ i, P (rA i)) (hB : ∀ i, P (rB i))
      (hCr : ∀ i, P (rCr i)) (hc : P cIn) :
      AndBracketWires P (conjTAddProg prep m rA rB rCr cIn hAB hAC hBC hcA hcB hcC) :=
    ⟨cbpDisj_andBracketWires _ hp,
        andBracketWires_gidneyTAddPhase _ _ _ _ _ _ _ _ _ _ _ hA hB hCr hc,
      andBracketWires_reverse _ (cbpDisj_andBracketWires _ hp)⟩
  have hmid (rem : ℕ) : ∀ (j : ℕ) (h2 : 2 ≤ j), 7 - j = rem →
      AndBracketWires P (postCancelT5MidRange rCat rP rDelta rCarry hPCat hPDelta hDCat hDCarry
          hCatCarry hPCarry j h2) := by
    induction rem with
    | zero =>
        intro j _ _
        unfold postCancelT5MidRange
        split_ifs <;> first | omega | trivial
    | succ r ih =>
        intro j h2 hrem
        unfold postCancelT5MidRange
        split_ifs with hj7
        · let jf : Fin 8 := ⟨j, by omega⟩
          exact ⟨⟨hw_conj (prepJT5_zero_and_disj rP rDelta hPDelta jf (j - 1)
              (by omega) hP (fun i ↦ hD6 ⟨i.val, by omega⟩)).2
            (fun i ↦ by
              have : i.val < j - 1 := i.isLt
              exact hD6 ⟨0 + i.val, by omega⟩)
            (fun i ↦ by
              have : i.val < j - 1 := i.isLt
              exact hCat5 ⟨(6 - j) + i.val, by omega⟩)
            (fun i ↦ by
              have : i.val < j - 1 := i.isLt
              exact hC5 ⟨0 + i.val, by omega⟩) (hP jf),
            hts (hP _) (hP _), hp1 (hP jf)⟩, ih (j + 1) (by omega) (by omega)⟩
        · trivial
  exact ⟨⟨⟨hsw2 0 7 _, hsw2 1 6 _, hsw2 2 5 _, hsw2 3 4 _⟩, hp1 (hP 0),
      ⟨hp1 (hP 1), hp2 (hP 0) (hP 1), circWires_inverse (hp1 (hP 1)), hp2 (hP 0) (hP 1)⟩,
          hp1 (hP 1)⟩,
    hmid 5 2 (by omega) rfl,
        ⟨⟨hP 7, hP 0, hD6 5, hw_conj (prepJ7T5_zero_and_disj rP rDelta hPDelta hP hD6).2
      (fun i ↦ hD6 ⟨0 + i.val, by omega⟩) (fun i ↦ hCat5 ⟨0 + i.val, by omega⟩)
      (fun i ↦ hC5 ⟨0 + i.val, by omega⟩) (hD6 5)⟩, hts (hP 6) (hP 7), hp1 (hP 7)⟩⟩
/-!
## Part 6a: `phase8Exp` , `EvalPhase8Perm` , `gidneyTAddPhase_eval_and_comm` , & `TAddCatShiftSpec`
-/

noncomputable def phase8Exp (k : ZMod 8) : ℂ :=
    Complex.exp (2 * Real.pi * Complex.I * (((32 * k.val : ℕ) : ℝ) / (2 ^ 8 : ℝ)))
@[simp] theorem phase8Exp_zero : phase8Exp 0 = 1 := by simp [phase8Exp]
theorem phase8Exp_ne_zero (k : ZMod 8) : phase8Exp k ≠ 0 := Complex.exp_ne_zero _
theorem phase8Exp_add (a b : ZMod 8) : phase8Exp (a + b) = phase8Exp a * phase8Exp b := by
  unfold phase8Exp
  rw [← Complex.exp_add, show 2 * (Real.pi : ℂ) * Complex.I * (((32 * a.val : ℕ) : ℝ) /
      (2 ^ 8 : ℝ)) +
      2 * (Real.pi : ℂ) * Complex.I * (((32 * b.val : ℕ) : ℝ) / (2 ^ 8 : ℝ)) =
      2 * (Real.pi : ℂ) * Complex.I * ((((32 * a.val + 32 * b.val : ℕ) : ℝ)) /
          (2 ^ 8 : ℝ)) by
            push_cast
            ring,
    ← PhotochemistrySolution.exp_two_pi_I_mod_div_two_pow 8 (32 * (a + b).val),
    ← PhotochemistrySolution.exp_two_pi_I_mod_div_two_pow 8 (32 * a.val + 32 * b.val),
    show (32 * (a + b).val) % 2 ^ 8 = (32 * a.val + 32 *
        b.val) % 2 ^ 8 by fin_cases a <;> fin_cases b <;> decide]
theorem phase8Exp_neg_mul_self (k : ZMod 8) : phase8Exp (-k) * phase8Exp k = 1 := by
  rw [← phase8Exp_add, neg_add_cancel, phase8Exp_zero]
theorem sqrt2_mul_self : (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ) = 2 := by
  exact_mod_cast Real.mul_self_sqrt (by norm_num)
theorem phase8Exp_one : phase8Exp 1 = (1 + Complex.I) / (Real.sqrt 2 : ℂ) := by
  unfold phase8Exp
  rw [show (1 : ZMod 8).val = 1 from rfl, show 2 * (Real.pi : ℂ) * Complex.I * (((32 * 1 : ℕ) : ℝ) /
      (2 ^ 8 : ℝ)) =
      ((Real.pi / 4 : ℝ) : ℂ) * Complex.I by
        push_cast
        ring,
    Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_pi_div_four,
        Real.sin_pi_div_four]
  have hsne : (Real.sqrt 2 : ℂ) ≠ 0 := fun h ↦
      by
        have h2 := sqrt2_mul_self
        rw [h, zero_mul] at h2
        norm_num at h2
  push_cast
  exact mul_right_cancel₀ hsne (by
    rw [show ((Real.sqrt 2 : ℂ) / 2 + (Real.sqrt 2 : ℂ) / 2 * Complex.I) * (Real.sqrt 2 : ℂ) =
      ((Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ)) / 2 * (1 + Complex.I) by ring, sqrt2_mul_self,
          div_mul_cancel₀ _ hsne]
    ring)
theorem phase8Exp_two : phase8Exp 2 = Complex.I := by
  rw [show (2 : ZMod 8) = 1 + 1 from rfl, phase8Exp_add, phase8Exp_one,
      show ((1 + Complex.I) / (Real.sqrt 2 : ℂ)) * ((1 + Complex.I) / (Real.sqrt 2 : ℂ)) =
        (1 + 2 * Complex.I + Complex.I * Complex.I) / ((Real.sqrt 2 : ℂ) *
            (Real.sqrt 2 : ℂ)) by ring,
      Complex.I_mul_I, sqrt2_mul_self]
  ring
theorem phase8Exp_four : phase8Exp 4 = -1 := by
  rw [show (4 : ZMod 8) = 2 + 2 from rfl, phase8Exp_add, phase8Exp_two, Complex.I_mul_I]
theorem singleton_embedMatrix_mulVec_ket8 {n : ℕ} (q : Wire n) (A : Matrix (Fin 2) (Fin 2) ℂ)
    (β : BitAssignment n) : ((QRegister.singleton q).embedMatrix A).mulVec (KinB.ket β) =
    A 0 (if β q = 0 then 0 else 1) • KinB.ket (Function.update β q 0) +
    A 1 (if β q = 0 then 0 else 1) • KinB.ket (Function.update β q 1) := by
  have hloc : KinB.localIdx (QRegister.singleton q) β = if β q = 0 then 0 else 1 :=
    (show ∀ b : ZMod 2, ((basisBitsEquiv 1).symm (fun _ ↦ b) : Fin 2) = if b =
        0 then 0 else 1 by decide) (β q)
  have hw (l : Fin 2) (b : ZMod 2) (hb : basisBits 1 l = fun _ ↦ b) :
      KinB.writeReg β (QRegister.singleton q) (basisBits 1 l) = Function.update β q b := by
    rw [KinB.writeReg_eq_update _ _ _ 0 (fun i hi ↦ absurd (Subsingleton.elim i 0) hi), hb]
    rfl
  rw [PhotochemistrySolution.KinB.embedMatrix_mulVec_ket, hloc]
  change ∑ l : Fin 2, _ = _
  rw [Fin.sum_univ_two, hw 0 0 (by decide), hw 1 1 (by decide)]
def EvalPhase8Perm {M : ℕ} (p : AndBracketProg M) (ph : BitAssignment M → ZMod 8)
    (f : BitAssignment M → BitAssignment M) : Prop :=
    ∀ β : BitAssignment M, p.toCircuit.eval.1.mulVec (KinB.ket β) =
    phase8Exp (ph β) • KinB.ket (f β)
theorem EvalPhase8Perm.seq {M : ℕ} {p₁ p₂ : AndBracketProg M} {ph₁ ph₂ : BitAssignment M → ZMod 8}
    {f₁ f₂ : BitAssignment M → BitAssignment M} (h₁ : EvalPhase8Perm p₁ ph₁ f₁)
    (h₂ : EvalPhase8Perm p₂ ph₂ f₂) : EvalPhase8Perm (.seq p₁ p₂) (fun β ↦ ph₁ β + ph₂ (f₁ β))
    (fun β ↦ f₂ (f₁ β)) := fun β ↦ by
  simp only [AndBracketProg.toCircuit, Circuit.eval_seq, Submonoid.coe_mul, ← Matrix.mulVec_mulVec]
  rw [h₁ β, Matrix.mulVec_smul, h₂ (f₁ β), smul_smul, ← phase8Exp_add]
theorem EvalPhase8Perm.cnot {M : ℕ} (c t : Wire M)
    (h : c ≠ t) : EvalPhase8Perm (.prim (Circuit.CNOT c t h)) (fun _ ↦ 0)
    (fun β ↦ Function.update β t (β t + β c)) := fun β ↦ by
  rw [phase8Exp_zero, one_smul]
  exact PhotochemistrySolution.KinB.ket_CNOT c t h β
theorem ket_diag1_eval8 {M : ℕ} (g : PrimitiveGate 1) (q : Wire M) (k : ZMod 8)
    (hg : g.eval = !![1, 0; 0, phase8Exp k]) (β : BitAssignment M) :
    (Circuit.single g q).eval.1.mulVec (PhotochemistrySolution.KinB.ket β) =
      phase8Exp (k * ((β q).val : ZMod 8)) • PhotochemistrySolution.KinB.ket β := by
  rw [Circuit.eval_single, QRegister.embedUnitary_val, hg, singleton_embedMatrix_mulVec_ket8]
  have e := Function.update_eq_self q β
  rcases bit_cases (β q) with hb | hb <;> rw [hb] at e ⊢
  · simp [e]
  · rw [ZMod.val_one, Nat.cast_one, mul_one]
    simp [e]
theorem ket_T_eval8 {M : ℕ} (q : Wire M) (β : BitAssignment M) :
    (Circuit.T q).eval.1.mulVec (KinB.ket β) = phase8Exp ((β q).val : ZMod 8) • KinB.ket β := by
  simpa only [one_mul] using ket_diag1_eval8 .T q 1
      (by simp [PrimitiveGate.eval, Qubit.T, phase8Exp_one]) β
theorem ket_S_eval8 {M : ℕ} (q : Wire M) (β : BitAssignment M) :
    (Circuit.S q).eval.1.mulVec (KinB.ket β) = phase8Exp (2 * ((β q).val : ZMod 8)) • KinB.ket β :=
  ket_diag1_eval8 .S q 2 (by simp [PrimitiveGate.eval, Qubit.S, phase8Exp_two]) β
theorem ket_Z_eval8 {M : ℕ} (q : Wire M) (β : BitAssignment M) :
    (Circuit.Z q).eval.1.mulVec (KinB.ket β) = phase8Exp (4 * ((β q).val : ZMod 8)) • KinB.ket β :=
  ket_diag1_eval8 .Z q 4 (by simp [PrimitiveGate.eval, Qubit.Z, phase8Exp_four]) β
theorem ket_TInv_eval8 {M : ℕ} (q : Wire M) (β : BitAssignment M) :
    (Circuit.T q).inverse.eval.1.mulVec (KinB.ket β) =
    phase8Exp (7 * ((β q).val : ZMod 8)) • KinB.ket β := by
  change (Circuit.seq (Circuit.T q) (Circuit.seq (Circuit.S q)
      (Circuit.seq (Circuit.Z q) Circuit.identity))).eval.1.mulVec
    (PhotochemistrySolution.KinB.ket β) = _
  simp only [Circuit.eval_seq, Circuit.eval_identity, one_mul, Submonoid.coe_mul,
      ← Matrix.mulVec_mulVec, ket_T_eval8,
    ket_S_eval8, ket_Z_eval8, Matrix.mulVec_smul, smul_smul, ← phase8Exp_add]
  exact congrArg (· • PhotochemistrySolution.KinB.ket β) (congrArg phase8Exp (by ring))
theorem EvalPhase8Perm.tGate {M : ℕ} (q : Wire M) : EvalPhase8Perm (.prim (Circuit.T q))
    (fun β ↦ ((β q).val : ZMod 8)) (fun β ↦ β) := ket_T_eval8 q
theorem EvalPhase8Perm.tempAnd {M : ℕ}
    (c₁ c₂ anc : Wire M) (h₁₂ : c₁ ≠ c₂) (h₁a : c₁ ≠ anc) (h₂a : c₂ ≠ anc)
    (body : AndBracketProg M) (ph : BitAssignment M → ZMod 8)
    (f : BitAssignment M → BitAssignment M) (hb : EvalPhase8Perm body ph f) :
    let toff := fun γ : BitAssignment M ↦ Function.update γ anc (γ anc + γ c₁ * γ c₂)
    EvalPhase8Perm (.tempAnd c₁ c₂ anc h₁₂ h₁a h₂a body)
      (fun β ↦ ph (toff β)) (fun β ↦ toff (f (toff β))) := fun β ↦ by
  simp only [AndBracketProg.toCircuit, Circuit.eval_seq, Submonoid.coe_mul, ← Matrix.mulVec_mulVec]
  rw [KinB.ket_TOFF, hb _, Matrix.mulVec_smul, KinB.ket_TOFF]
theorem EvalPhase8Perm.comm_cleanProj_of_fix {M : ℕ} {p : AndBracketProg M}
    {ph : BitAssignment M → ZMod 8} {f : BitAssignment M → BitAssignment M}
    (hp : EvalPhase8Perm p ph f) (S : Finset (Wire M)) (hfix : ∀ (β : BitAssignment M)
    (w : Wire M), w ∈ S → f β w = β w) : p.toCircuit.eval.1 * cleanProj S = cleanProj S *
    p.toCircuit.eval.1 := by
  refine PhotochemistrySolution.KinB.matrix_ext_ket fun β ↦ ?_
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, cleanProj_mulVec_ket]
  by_cases hS : ∀ w ∈ S, β w = 0
  · rw [ite_eq_left hS, hp β, Matrix.mulVec_smul, cleanProj_mulVec_ket, ite_eq_left fun w hw ↦
        (hfix β w hw).trans (hS w hw)]
  · rw [ite_eq_right hS, Matrix.mulVec_zero, hp β, Matrix.mulVec_smul, cleanProj_mulVec_ket,
      ite_eq_right fun h ↦ hS fun w hw ↦ (hfix β w hw).symm.trans (h w hw), smul_zero]
theorem EvalPhase8Perm.comm_andInvProj_of_fix {M : ℕ} {p : AndBracketProg M}
    {ph : BitAssignment M → ZMod 8} {f : BitAssignment M → BitAssignment M}
    (hp : EvalPhase8Perm p ph f) (c₁ c₂ anc : Wire M) (hfix : ∀ β : BitAssignment M, f β c₁ = β c₁ ∧
    f β c₂ = β c₂ ∧ f β anc = β anc) : p.toCircuit.eval.1 * andInvProj c₁ c₂ anc =
    andInvProj c₁ c₂ anc * p.toCircuit.eval.1 := by
  refine PhotochemistrySolution.KinB.matrix_ext_ket fun β ↦ ?_
  obtain ⟨h1, h2, ha⟩ := hfix β
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, andInvProj_mulVec_ket]
  by_cases hinv : β anc = β c₁ * β c₂
  · rw [ite_eq_left hinv, hp β, Matrix.mulVec_smul, andInvProj_mulVec_ket,
        ite_eq_left (by rw [ha, h1, h2, hinv])]
  · rw [ite_eq_right hinv, Matrix.mulVec_zero, hp β, Matrix.mulVec_smul, andInvProj_mulVec_ket,
      ite_eq_right (by
        rw [ha, h1, h2]
        exact hinv), smul_zero]
theorem EvalPhase8Perm.localOnQft16_both {M : ℕ} (rP rCat : QRegister 8 M) {p : AndBracketProg M}
    {ph : BitAssignment M → ZMod 8} {f : BitAssignment M → BitAssignment M}
    (hep : EvalPhase8Perm p ph f) (hpr : ∀ (β : BitAssignment M)
    (u : Wire M), u ∉ Set.range rP.wires → u ∉ Set.range rCat.wires → f β u = β u) :
    LocalOnQft16 rP rCat p.toCircuit.eval.1 ∧ LocalOnQft16 rP rCat (p.toCircuit.eval⁻¹).1 := by
  refine ⟨fun α G hG ↦
      by rw [hep α, Matrix.mulVec_smul, eq_set16_of_pres_outside rP rCat α (f α)
           (hpr α), hG, smul_zero],
    fun α G hG ↦ ?_⟩
  have hinv_ket (β : BitAssignment M) : (p.toCircuit.eval⁻¹).1.mulVec (KinB.ket (f β)) =
      phase8Exp (-ph β) • PhotochemistrySolution.KinB.ket β := by
    have h1 : ((p.toCircuit.eval⁻¹).1 * p.toCircuit.eval.1).mulVec (KinB.ket β) =
        PhotochemistrySolution.KinB.ket β := by
      rw [show (p.toCircuit.eval⁻¹).1 * p.toCircuit.eval.1 = 1 from
        congrArg Subtype.val (inv_mul_cancel p.toCircuit.eval), Matrix.one_mulVec]
    rw [← Matrix.mulVec_mulVec, hep β, Matrix.mulVec_smul] at h1
    rw [← one_smul ℂ ((p.toCircuit.eval⁻¹).1.mulVec _), ← phase8Exp_neg_mul_self (ph β), mul_smul,
        h1]
  obtain ⟨β, rfl⟩ := ((Finite.injective_iff_bijective (f := f)).mp fun β₁ β₂ hfeq ↦ by
    have h := congrFun ((hinv_ket β₁).symm.trans (hfeq ▸ hinv_ket β₂)) ((basisBitsEquiv M).symm β₂)
    by_contra hne
    simp only [Pi.smul_apply, smul_eq_mul, KinB.ket, basisState] at h
    rw [Pi.single_eq_of_ne (fun e ↦ hne ((basisBitsEquiv M).symm.injective e.symm)),
        Pi.single_eq_same, mul_zero, mul_one] at h
    exact phase8Exp_ne_zero (-ph β₂) h.symm).surjective α
  rw [hinv_ket β, Matrix.mulVec_smul, eq_set16_of_pres_outside rP rCat (f β) β (fun u hp hc ↦
      (hpr β u hp hc).symm), hG, smul_zero]
/-! ### `CommCleanBracket.abpInv` & `CleanStepPair13AbpInv` (`0` `IsSelfInvPrim` Needed!) -/

theorem CommCleanBracket.of_abpInv {M : ℕ} {S : Finset (Wire M)} {p : AndBracketProg M}
    (hp : CommCleanBracket S p) : CommCleanBracket S (abpInv p) := by
  induction p generalizing S with
  | id => trivial
  | prim c =>
      change c.inverse.eval.1 * cleanProj S = cleanProj S * c.inverse.eval.1
      rw [Circuit.eval_inverse]
      exact unitary_inv_comm c.eval (cleanProj S) hp
  | seq _ _ ih₁ ih₂ => exact ⟨ih₂ hp.2, ih₁ hp.1⟩
  | tempAnd c₁ c₂ anc h₁₂ h₁a h₂a body ih =>
      rcases hp with ⟨hanc, hbody, hand, hcomm⟩
      exact ⟨hanc, ih hbody, eval_abpInv_eq_inv body ▸ unitary_inv_comm body.toCircuit.eval _ hand,
        show (abpInv (.tempAnd c₁ c₂ anc h₁₂ h₁a h₂a body)).toCircuit.eval.1 * cleanProj S =
          cleanProj S * (abpInv (.tempAnd c₁ c₂ anc h₁₂ h₁a h₂a body)).toCircuit.eval.1 from
            eval_abpInv_eq_inv (.tempAnd c₁ c₂ anc h₁₂ h₁a h₂a body) ▸ unitary_inv_comm _ _ hcomm⟩
def CleanStepPair13AbpInv {Var : Type} [Fintype Var] [DecidableEq Var] {M n : ℕ} [NeZero (2 ^ n)]
    (v : Var) (rTot : QRegister M n) (rClean13 : QRegister 13 M) (p : AndBracketProg M) : Prop :=
    p.toCircuit.eval.1 * cleanProj (Finset.univ.image rClean13.wires) =
    cleanProj (Finset.univ.image rClean13.wires) * p.toCircuit.eval.1 ∧
    CleanWorkStep (rTot.compose rClean13) (rTot.embedUnitary p.toCircuit.eval)
    ((p.onRegister rTot).toDyn v) ∧ CleanWorkStep (rTot.compose rClean13)
    ((rTot.embedUnitary p.toCircuit.eval)⁻¹) (((abpInv p).onRegister rTot).toDyn v)
theorem CleanStepPair13AbpInv.id {Var : Type} [Fintype Var] [DecidableEq Var] {M n : ℕ}
    [NeZero (2 ^ n)] (v : Var) (rTot : QRegister M n) (rClean13 : QRegister 13 M) :
    CleanStepPair13AbpInv v rTot rClean13 .id :=
  have hs := cleanWorkStep_onRegister_of_commClean v rTot rClean13 .id trivial
  ⟨by simp [AndBracketProg.toCircuit], hs,
    (show (rTot.embedUnitary AndBracketProg.id.toCircuit.eval)⁻¹ =
        rTot.embedUnitary AndBracketProg.id.toCircuit.eval by
      change (rTot.embedUnitary (1 : Unitary (2 ^ M)))⁻¹ = rTot.embedUnitary 1
      rw [rTot.embedUnitary_one, inv_one]).symm ▸ hs⟩
theorem CleanStepPair13AbpInv.seq {Var : Type} [Fintype Var] [DecidableEq Var] {M n : ℕ}
    [NeZero (2 ^ n)] {v : Var} {rTot : QRegister M n} {rClean13 : QRegister 13 M}
    {p₁ p₂ : AndBracketProg M} (h₁ : CleanStepPair13AbpInv v rTot rClean13 p₁)
    (h₂ : CleanStepPair13AbpInv v rTot rClean13 p₂) :
    CleanStepPair13AbpInv v rTot rClean13 (.seq p₁ p₂) := by
  rcases h₁, h₂ with ⟨⟨hc₁, hf₁, hr₁⟩, ⟨hc₂, hf₂, hr₂⟩⟩
  exact ⟨by
    simp only [AndBracketProg.toCircuit, Circuit.eval_seq, Submonoid.coe_mul]
    rw [Matrix.mul_assoc, hc₁, ← Matrix.mul_assoc, hc₂, Matrix.mul_assoc],
    (rTot.embedUnitary_mul p₂.toCircuit.eval p₁.toCircuit.eval).symm ▸ CleanWorkStep.seq hf₁ hf₂,
    (show (rTot.embedUnitary (AndBracketProg.seq p₁ p₂).toCircuit.eval)⁻¹ =
      (rTot.embedUnitary p₁.toCircuit.eval)⁻¹ * (rTot.embedUnitary p₂.toCircuit.eval)⁻¹ by
        simp only [AndBracketProg.toCircuit, Circuit.eval_seq, rTot.embedUnitary_mul,
            _root_.mul_inv_rev]).symm ▸ CleanWorkStep.seq hr₂ hr₁⟩
theorem CleanStepPair13AbpInv.of_subreg {Var : Type} [Fintype Var] [DecidableEq Var] {M n w : ℕ}
    [NeZero (2 ^ n)] (v : Var) (rTot : QRegister M n) (rClean13 : QRegister 13 M)
    (rSub : QRegister w M) (hSub : ∀ i : Fin w, ∃ j : Fin 13, rSub i = rClean13 j)
    (p : AndBracketProg M) (hCommSub : CommCleanBracket (Finset.univ.image rSub.wires) p)
    (hComm13 : p.toCircuit.eval.1 * cleanProj (Finset.univ.image rClean13.wires) =
    cleanProj (Finset.univ.image rClean13.wires) * p.toCircuit.eval.1) :
    CleanStepPair13AbpInv v rTot rClean13 p := by
  have himg : (Finset.univ.image rClean13.wires).image rTot.wires =
      Finset.univ.image (rTot.compose rClean13).wires := by
    ext x
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨fun ⟨_, ⟨i, hi⟩, hx⟩ ↦ ⟨i, by
      rw [← hx, ← hi]
      rfl⟩, fun ⟨i, hi⟩ ↦
        ⟨rClean13 i, ⟨i, rfl⟩, hi⟩⟩
  have hCf : (rTot.embedUnitary p.toCircuit.eval).1 *
      (rTot.compose rClean13).basisOutcomeProjector 0 =
      (rTot.compose rClean13).basisOutcomeProjector 0 * (rTot.embedUnitary p.toCircuit.eval).1 := by
    rw [QRegister.embedUnitary_val,
        ← cleanProj_range_eq_basisOutcomeProjector_zero (rTot.compose rClean13), ← himg,
      cleanProj_image_eq_embedMatrix, ← rTot.embedMatrix_mul, ← rTot.embedMatrix_mul, hComm13]
  have hSubTot (i : Fin w) := (hSub i).imp fun _ hj ↦ congrArg rTot.wires hj
  exact ⟨hComm13,
      CleanWorkStep.of_subreg _ _ hSubTot _ _ hCf (cleanWorkStep_onRegister_of_commClean v rTot rSub
      p hCommSub),
    CleanWorkStep.of_subreg _ _ hSubTot _ _ (unitary_inv_comm (rTot.embedUnitary p.toCircuit.eval) _
        hCf)
      ((by rw [eval_abpInv_eq_inv, rTot.embedUnitary_inv] :
        rTot.embedUnitary (abpInv p).toCircuit.eval = (rTot.embedUnitary p.toCircuit.eval)⁻¹) ▸
        cleanWorkStep_onRegister_of_commClean v rTot rSub (abpInv p)
            (CommCleanBracket.of_abpInv hCommSub))⟩
theorem CleanStepPair13AbpInv.of_prim_rP {Var : Type} [Fintype Var] [DecidableEq Var] {M n : ℕ}
    [NeZero (2 ^ n)] (v : Var) (rTot : QRegister M n) (rClean13 : QRegister 13 M)
    (rP : QRegister 8 M) (hPClean : rP.DisjointWires rClean13) (c : Circuit M)
    (A : Operator (2 ^ 8)) (hc : c.eval.1 = rP.embedMatrix A) :
    CleanStepPair13AbpInv v rTot rClean13 (.prim c) :=
  have hcomm : c.eval.1 * cleanProj (Finset.univ.image rClean13.wires) =
      cleanProj (Finset.univ.image rClean13.wires) * c.eval.1 := by
    rw [hc, cleanProj_range_eq_basisOutcomeProjector_zero]
    exact rP.embedMatrix_comm_of_disjoint rClean13 hPClean A _
  CleanStepPair13AbpInv.of_subreg v rTot rClean13 rClean13 (fun i ↦ ⟨i, rfl⟩) (.prim c) hcomm hcomm
/-! ### `gidneyTAddPhase_eval_and_comm` & `conjTAddProg_spec` -/
theorem gidneyTAddPhase_eval_and_comm {M : ℕ} :
    ∀ (m : ℕ) (rA rB rCarry : QRegister m M) (cIn : Wire M)
      (hAB : rA.DisjointWires rB) (hAC : rA.DisjointWires rCarry) (hBC : rB.DisjointWires rCarry)
      (hcA : cIn ∉ Set.range rA.wires) (hcB : cIn ∉ Set.range rB.wires)
      (hcC : cIn ∉ Set.range rCarry.wires),
      ∃ (ph : BitAssignment M → ZMod 8) (f : BitAssignment M → BitAssignment M),
        EvalPhase8Perm (gidneyTAddPhase m rA rB rCarry cIn hAB hAC hBC hcA hcB hcC) ph f ∧
        (∀ (β : BitAssignment M) (u : Wire M), u ∉ Set.range rB.wires → f β u = β u) ∧
        (∀ β : BitAssignment M, (∀ i : Fin m, β (rCarry i) = 0) →
          ph β = (((PhotochemistrySolution.regVal m rB β + PhotochemistrySolution.regVal m rA β +
                    (β cIn).val) / 2 ^ m : ℕ) : ZMod 8) ∧
          PhotochemistrySolution.regVal m rB (f β) =
            (PhotochemistrySolution.regVal m rB β + PhotochemistrySolution.regVal m rA β +
              (β cIn).val) % 2 ^ m) ∧
        (∀ S : Finset (Wire M),
          (∀ i : Fin m, rA i ∉ S) → (∀ i : Fin m, rB i ∉ S) →
          (cIn ∉ S) → (∀ i : Fin m, rCarry i ∈ S) →
          CommCleanBracket S (gidneyTAddPhase m rA rB rCarry cIn hAB hAC hBC hcA hcB hcC))
  | 0, _rA, _rB, _rCarry, cIn, _hAB, _hAC, _hBC, _hcA, _hcB, _hcC =>
      ⟨fun β ↦ ((β cIn).val : ZMod 8), fun β ↦ β, EvalPhase8Perm.tGate cIn, fun _ _ _ ↦ rfl,
        fun β _ ↦
            ⟨by
              change ((β cIn).val : ZMod 8) = (((0 + 0 + (β cIn).val) / 1 : ℕ) : ZMod 8)
              simp,
          by
            change 0 = (0 + 0 + (β cIn).val) % 1
            omega⟩,
        fun S _ _ _ _ ↦
            EvalPhase8Perm.comm_cleanProj_of_fix (EvalPhase8Perm.tGate cIn) S (fun _ _ _ ↦ rfl)⟩
  | m + 1, rA, rB, rCarry, cIn, hAB, hAC, hBC, hcA, hcB, hcC => by
      let hab := hAB.ne 0 0
      let hac := hAC.ne 0 0
      let hbc := hBC.ne 0 0
      have hca : cIn ≠ rA 0 := fun e ↦ hcA ⟨0, e.symm⟩
      have hcb : cIn ≠ rB 0 := fun e ↦ hcB ⟨0, e.symm⟩
      have hcc : cIn ≠ rCarry 0 := fun e ↦ hcC ⟨0, e.symm⟩
      let dT := gidneyTailDisj hAB hAC hBC
      obtain ⟨ph_ih, f_ih, hev_ih, hout_ih, hval_ih, hcomm_ih⟩ :=
        gidneyTAddPhase_eval_and_comm m _ _ _ (rCarry 0) dT.1 dT.2.1 dT.2.2.1 dT.2.2.2.1
            dT.2.2.2.2.1 dT.2.2.2.2.2
      let stepPre (β : BitAssignment M) :=
          Function.update (Function.update β (rA 0) (β (rA 0) + β cIn)) (rB 0) (β (rB 0) + β cIn)
      let cNext (γ : BitAssignment M) := Function.update γ (rCarry 0) (γ (rCarry 0) + γ cIn)
      let bodyPh (γ : BitAssignment M) : ZMod 8 := ph_ih (cNext γ)
      let bodyF (γ : BitAssignment M) := cNext (f_ih (cNext γ))
      have hbody_ev : EvalPhase8Perm (.seq (.prim (.CNOT cIn (rCarry 0) hcc))
          (.seq (gidneyTAddPhase m _ _ _ (rCarry 0) dT.1 dT.2.1 dT.2.2.1 dT.2.2.2.1 dT.2.2.2.2.1
              dT.2.2.2.2.2)
            (.prim (.CNOT cIn (rCarry 0) hcc)))) bodyPh bodyF := fun γ ↦
        ((EvalPhase8Perm.seq (EvalPhase8Perm.cnot cIn (rCarry 0) hcc)
          (EvalPhase8Perm.seq hev_ih (EvalPhase8Perm.cnot cIn (rCarry 0) hcc))) γ).trans
          (congrArg₂ (· • ·) (congrArg phase8Exp (by
            simp only [zero_add, add_zero]
            rfl)) rfl)
      have hbody_out (γ : BitAssignment M) (u : Wire M)
          (hu : u ∉ Set.range (PhotochemistrySolution.regTail rB).wires) : bodyF γ u = γ u := by
        dsimp only [bodyF, cNext]
        rcases eq_or_ne u (rCarry 0) with rfl | huc
        · rw [Function.update_self, hout_ih _ (rCarry 0) (fun ⟨j, hj⟩ ↦ hBC.ne j.succ 0 hj),
            hout_ih _ cIn (fun ⟨j, hj⟩ ↦ hcB ⟨j.succ, hj⟩), Function.update_self,
                Function.update_of_ne hcc,
            add_assoc, CharTwo.add_self_eq_zero, add_zero]
        · rw [Function.update_of_ne huc, hout_ih _ u hu, Function.update_of_ne huc]
      let toff0 (γ : BitAssignment M) :=
          Function.update γ (rCarry 0) (γ (rCarry 0) + γ (rA 0) * γ (rB 0))
      let stepPost (δ : BitAssignment M) :=
          Function.update (Function.update (Function.update δ (rB 0) (δ (rB 0) + δ (rA 0)))
        (rA 0) (δ (rA 0) + δ cIn)) (rB 0) ((δ (rB 0) + δ (rA 0)) + δ cIn)
      let phTot (β : BitAssignment M) : ZMod 8 := bodyPh (toff0 (stepPre β))
      let fTot (β : BitAssignment M) := stepPost (toff0 (bodyF (toff0 (stepPre β))))
      have htoff_out (γ : BitAssignment M) (w : Wire M)
          (hw : w ∉ Set.range (PhotochemistrySolution.regTail rB).wires) :
          toff0 (bodyF (toff0 γ)) w = γ w := by
        dsimp only [toff0]
        rcases eq_or_ne w (rCarry 0) with rfl | hwc
        · rw [Function.update_self, hbody_out _ (rCarry 0) hw, hbody_out _ (rA 0)
              (fun ⟨j, hj⟩ ↦ hAB.ne 0 j.succ hj.symm),
            hbody_out _ (rB 0) (fun ⟨j, hj⟩ ↦ Fin.succ_ne_zero j (rB.wires.injective hj)),
                Function.update_self,
            Function.update_of_ne hac, Function.update_of_ne hbc, add_assoc,
                CharTwo.add_self_eq_zero, add_zero]
        · rw [Function.update_of_ne hwc, hbody_out _ w hw, Function.update_of_ne hwc]
      have htot_ev : EvalPhase8Perm
          (gidneyTAddPhase (m + 1) rA rB rCarry cIn hAB hAC hBC hcA hcB hcC) phTot fTot := fun β ↦
              by
        have hev := EvalPhase8Perm.seq (EvalPhase8Perm.cnot cIn (rA 0) hca)
          (EvalPhase8Perm.seq (EvalPhase8Perm.cnot cIn (rB 0) hcb)
            (EvalPhase8Perm.seq (EvalPhase8Perm.tempAnd (rA 0) (rB 0)
                (rCarry 0) hab hac hbc _ _ _ hbody_ev)
              (EvalPhase8Perm.seq (EvalPhase8Perm.cnot (rA 0) (rB 0) hab)
                (EvalPhase8Perm.seq (EvalPhase8Perm.cnot cIn (rA 0) hca)
                    (EvalPhase8Perm.cnot cIn (rB 0) hcb)))))
        dsimp only [gidneyTAddPhase]
        rw [hev β]
        have hpre_eq : Function.update (Function.update β (rA 0) (β (rA 0) + β cIn)) (rB 0)
            (Function.update β (rA 0) (β (rA 0) + β cIn) (rB 0) +
              Function.update β (rA 0) (β (rA 0) + β cIn) cIn) = stepPre β := by
          rw [Function.update_of_ne hab.symm, Function.update_of_ne hca]
        refine congrArg₂ (· • ·)
            (congrArg phase8Exp (by
              simp only [zero_add, add_zero, hpre_eq]
              rfl))
            (congrArg _ ?_)
        dsimp only [fTot, stepPost]
        rw [hpre_eq]
        conv_lhs => rw [Function.update_of_ne hab, Function.update_of_ne hcb,
          Function.update_of_ne hab.symm, Function.update_self, Function.update_of_ne hca,
              Function.update_of_ne hcb]
      have htot_out (β : BitAssignment M) (u : Wire M) (hu : u ∉ Set.range rB.wires) : fTot β u =
          β u := by
        have hub0 : u ≠ rB 0 := fun e ↦ hu ⟨0, e.symm⟩
        dsimp only [fTot, stepPost]
        rw [Function.update_of_ne hub0]
        rcases eq_or_ne u (rA 0) with rfl | hua0
        · rw [Function.update_self, htoff_out _ (rA 0) (fun ⟨j, hj⟩ ↦ hAB.ne 0 j.succ hj.symm),
            htoff_out _ cIn (fun ⟨j, hj⟩ ↦ hcB ⟨j.succ, hj⟩)]
          simp only [stepPre, Function.update_of_ne hab, Function.update_self,
              Function.update_of_ne hcb,
            Function.update_of_ne hca, add_assoc, CharTwo.add_self_eq_zero, add_zero]
        · rw [Function.update_of_ne hua0, Function.update_of_ne hub0, htoff_out _ u fun ⟨j, hj⟩ ↦
              hu ⟨j.succ, hj⟩]
          simp only [stepPre, Function.update_of_ne hub0, Function.update_of_ne hua0]
      refine ⟨phTot, fTot, htot_ev, htot_out, fun β hc0 ↦ ?_, fun S hSA hSB _ hSC ↦ ?_⟩
      · let η := cNext (toff0 (stepPre β))
        have hη_ne {w : Wire M} (h1 : w ≠ rCarry 0) (h2 : w ≠ rB 0) (h3 : w ≠ rA 0) : η w =
            β w := by
          simp only [η, cNext, toff0, stepPre, Function.update_of_ne h1, Function.update_of_ne h2,
              Function.update_of_ne h3]
        have hη_c0 : η (rCarry 0) = β cIn + (β (rA 0) + β cIn) * (β (rB 0) + β cIn) := by
          simp only [η, cNext, toff0, stepPre, Function.update_self, Function.update_of_ne hcc,
              Function.update_of_ne hab,
            Function.update_of_ne hca, Function.update_of_ne hcb, Function.update_of_ne hac.symm,
            Function.update_of_ne hbc.symm, hc0 0, zero_add]
          ring
        have hη_tail_A :=
            SelectFastRouterEval.regVal_congr (PhotochemistrySolution.regTail rA) η β fun i ↦
          hη_ne (hAC.ne i.succ 0) (hAB.ne i.succ 0) (rA.wires.injective.ne (Fin.succ_ne_zero i))
        have hη_tail_B :=
            SelectFastRouterEval.regVal_congr (PhotochemistrySolution.regTail rB) η β fun i ↦
          hη_ne (hBC.ne i.succ 0) (rB.wires.injective.ne (Fin.succ_ne_zero i))
              (hAB.ne 0 i.succ).symm
        obtain ⟨hph_ih, hsum_ih⟩ := hval_ih η fun i ↦
          (hη_ne (rCarry.wires.injective.ne (Fin.succ_ne_zero i))
              (hBC.ne 0 i.succ).symm (hAC.ne 0 i.succ).symm).trans (hc0 i.succ)
        obtain ⟨hcout_bit, hb0_bit, _⟩ := gidney_full_bit_step (β (rA 0)) (β (rB 0)) (β cIn)
        let s0 := (β (rA 0)).val + (β (rB 0)).val + (β cIn).val
        have hcarry0_val : (η (rCarry 0)).val = s0 / 2 := by
          rw [hη_c0, hcout_bit]
          have :=
              ZMod.val_lt (β (rA 0))
          have := ZMod.val_lt (β (rB 0))
          have := ZMod.val_lt (β cIn)
          exact ZMod.val_cast_of_lt (by omega)
        let X_top := PhotochemistrySolution.regVal m (PhotochemistrySolution.regTail rB) β +
          PhotochemistrySolution.regVal m (PhotochemistrySolution.regTail rA) β + (η (rCarry 0)).val
        have htot_int : PhotochemistrySolution.regVal (m + 1) rB β +
            PhotochemistrySolution.regVal (m + 1) rA β + (β cIn).val =
            s0 % 2 + 2 * X_top := by
          change ((β (rB 0)).val + 2 *
              PhotochemistrySolution.regVal m (PhotochemistrySolution.regTail rB) β) +
            ((β (rA 0)).val + 2 *
                PhotochemistrySolution.regVal m (PhotochemistrySolution.regTail rA) β) +
                (β cIn).val = _
          dsimp only [X_top, s0]
          rw [hcarry0_val]
          omega
        refine ⟨hph_ih.trans <| by
            rw [hη_tail_A, hη_tail_B, htot_int, pow_succ' 2 m, ← Nat.div_div_eq_div_mul]
            exact congrArg Nat.cast (congrArg (· / 2 ^ m) (by omega)), ?_⟩
        have hb0_out : (fTot β (rB 0)).val = s0 % 2 := by
          dsimp only [fTot, stepPost]
          rw [Function.update_self,
            htoff_out _ (rB 0) (fun ⟨j, hj⟩ ↦ Fin.succ_ne_zero j (rB.wires.injective hj)),
            htoff_out _ (rA 0) (fun ⟨j, hj⟩ ↦ hAB.ne 0 j.succ hj.symm),
                htoff_out _ cIn (fun ⟨j, hj⟩ ↦ hcB ⟨j.succ, hj⟩)]
          simp only [stepPre, s0, Function.update_self, Function.update_of_ne hab,
            Function.update_of_ne hcb, Function.update_of_ne hca, hb0_bit]
        have htail_out : PhotochemistrySolution.regVal m (PhotochemistrySolution.regTail rB)
            (fTot β) = X_top % 2 ^ m :=
          (SelectFastRouterEval.regVal_congr (PhotochemistrySolution.regTail rB) (fTot β)
              (f_ih η) fun i ↦ by
            change fTot β (rB i.succ) = f_ih η (rB i.succ)
            simp only [fTot, stepPost, toff0, bodyF, cNext, η,
                Function.update_of_ne (rB.wires.injective.ne (Fin.succ_ne_zero i)),
              Function.update_of_ne (hAB.ne 0 i.succ).symm,
                  Function.update_of_ne (hBC.ne i.succ 0)]).trans
            (by rw [hsum_ih, hη_tail_A, hη_tail_B])
        change (fTot β (rB 0)).val + 2 *
            PhotochemistrySolution.regVal m (PhotochemistrySolution.regTail rB) (fTot β) =
          (PhotochemistrySolution.regVal (m + 1) rB β + PhotochemistrySolution.regVal (m + 1) rA β +
              (β cIn).val) % 2 ^ (m + 1)
        rw [hb0_out, htail_out, htot_int, pow_succ' 2 m]
        have hlt : s0 % 2 + 2 * (X_top % 2 ^ m) < 2 * 2 ^ m := by
          have :=
              Nat.mod_lt s0 (by decide : 0 < 2)
          have := Nat.mod_lt X_top (pow_pos (by decide : 0 < 2) m)
          omega
        conv_rhs => rw [(Nat.div_add_mod X_top (2 ^ m)).symm]
        rw [show s0 % 2 + 2 * (2 ^ m * (X_top / 2 ^ m) + X_top % 2 ^ m) =
              (s0 % 2 + 2 * (X_top % 2 ^ m)) + (X_top / 2 ^ m) * (2 * 2 ^ m) by ring,
            Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hlt]
      · have htemp_ev : EvalPhase8Perm (.tempAnd (rA 0) (rB 0) (rCarry 0) hab hac hbc _)
            (fun γ ↦ bodyPh (toff0 γ)) (fun γ ↦ toff0 (bodyF (toff0 γ))) :=
          EvalPhase8Perm.tempAnd _ _ _ _ _ _ _ _ _ hbody_ev
        refine ⟨hcnot_comm_clean S _ _ _ (hSA 0), hcnot_comm_clean S _ _ _ (hSB 0),
          ⟨hSC 0,
            ⟨hcnot_comm_clean (S.erase (rCarry 0)) _ _ _ (Finset.notMem_erase _ _),
              hcomm_ih (S.erase (rCarry 0)) (fun i h ↦ hSA i.succ (Finset.mem_of_mem_erase h))
                (fun i h ↦ hSB i.succ (Finset.mem_of_mem_erase h)) (Finset.notMem_erase _ _)
                (fun i ↦ Finset.mem_erase.mpr ⟨rCarry.wires.injective.ne (Fin.succ_ne_zero i),
                    hSC i.succ⟩),
              hcnot_comm_clean (S.erase (rCarry 0)) _ _ _ (Finset.notMem_erase _ _)⟩,
            EvalPhase8Perm.comm_andInvProj_of_fix hbody_ev (rA 0) (rB 0) (rCarry 0) fun γ ↦
              ⟨hbody_out γ (rA 0) (fun ⟨j, hj⟩ ↦ hAB.ne 0 j.succ hj.symm),
                hbody_out γ (rB 0) (fun ⟨j, hj⟩ ↦ Fin.succ_ne_zero j (rB.wires.injective hj)),
                hbody_out γ (rCarry 0) (fun ⟨j, hj⟩ ↦ hBC.ne j.succ 0 hj)⟩,
            EvalPhase8Perm.comm_cleanProj_of_fix htemp_ev S fun γ w hw ↦
              htoff_out γ w fun ⟨j, hj⟩ ↦ hSB j.succ (hj.symm ▸ hw)⟩,
          hcnot_comm_clean S _ _ _ (hSB 0), hcnot_comm_clean S _ _ _ (hSA 0),
              hcnot_comm_clean S _ _ _ (hSB 0)⟩
theorem conjTAddProg_spec {M : ℕ} (prep : ClassicalBracketProg M)
    (h0 : prep.numTempAnd = 0)
    (m : ℕ) (rA rB rCarry : QRegister m M) (cIn : Wire M)
    (hAB : rA.DisjointWires rB) (hAC : rA.DisjointWires rCarry) (hBC : rB.DisjointWires rCarry)
    (hcA : cIn ∉ Set.range rA.wires) (hcB : cIn ∉ Set.range rB.wires)
    (hcC : cIn ∉ Set.range rCarry.wires)
    (hPB : CBPDisj (fun u ↦ u ∉ Set.range rB.wires) prep)
    (hPC : CBPDisj (fun u ↦ u ∉ Set.range rCarry.wires) prep) :
    let prog := conjTAddProg prep m rA rB rCarry cIn hAB hAC hBC hcA hcB hcC
    (∀ S : Finset (Wire M), CBPDisj (fun u ↦ u ∉ S) prep →
      (∀ i : Fin m, rA i ∉ S) → (∀ i : Fin m, rB i ∉ S) →
      cIn ∉ S → (∀ i : Fin m, rCarry i ∈ S) → CommCleanBracket S prog) ∧
    ∃ (ph : BitAssignment M → ZMod 8) (g : BitAssignment M → BitAssignment M),
      EvalPhase8Perm prog ph g ∧
      (∀ (β : BitAssignment M) (u : Wire M), u ∉ Set.range rB.wires → g β u = β u) ∧
      (∀ β : BitAssignment M, (∀ i : Fin m, β (rCarry i) = 0) →
        ph β = (((PhotochemistrySolution.regVal m rB β +
            PhotochemistrySolution.regVal m rA (prep.evalBits β) +
            (prep.evalBits β cIn).val) / 2 ^ m : ℕ) : ZMod 8) ∧
        PhotochemistrySolution.regVal m rB (g β) =
          (PhotochemistrySolution.regVal m rB β +
            PhotochemistrySolution.regVal m rA (prep.evalBits β) +
            (prep.evalBits β cIn).val) % 2 ^ m) := by
  intro prog
  have hp_si := prep.toBracket_isSelfInvPrim
  obtain ⟨ph0, f0, hev0, hout0, hval0, hcomm0⟩ :=
      gidneyTAddPhase_eval_and_comm m rA rB rCarry cIn hAB hAC hBC hcA hcB hcC
  let g (β : BitAssignment M) := DynCircExt.writeReg β rB fun j ↦ f0 (prep.evalBits β) (rB j)
  have hg_out (β : BitAssignment M) (u : Wire M) (hu : u ∉ Set.range rB.wires) : g β u = β u :=
    DynCircExt.writeReg_apply_of_not_mem β rB _ u hu
  have hprep_g (β : BitAssignment M) : prep.evalBits (g β) = f0 (prep.evalBits β) := funext fun u ↦
      by
    obtain ⟨hcong, hfix⟩ := cbpDisj_evalBits prep hPB (hg_out β)
    by_cases hu : u ∈ Set.range rB.wires
    · obtain ⟨j, rfl⟩ := hu
      exact (hfix (rB j) fun h ↦
          h ⟨j, rfl⟩).trans (DynCircExt.writeReg_apply_reg β rB _ j)
    · exact (hcong u hu).trans (hout0 (prep.evalBits β) u hu).symm
  have hrev_ket (γ : BitAssignment M) :
      prep.toBracket.reverse.toCircuit.eval.1.mulVec (KinB.ket (prep.evalBits γ)) =
        PhotochemistrySolution.KinB.ket γ := by
    simpa only [Submonoid.coe_mul, ← Matrix.mulVec_mulVec, Matrix.one_mulVec,
        prep.toBracket_ket γ] using
      congrArg (fun A : Operator (2 ^ M) ↦ A.mulVec (PhotochemistrySolution.KinB.ket γ))
        (show (prep.toBracket.reverse.toCircuit.eval * prep.toBracket.toCircuit.eval).1 = 1 by
          rw [AndBracketProg.eval_reverse_eq_inv hp_si, inv_mul_cancel]
          rfl)
  refine ⟨fun S hpS hSA hSB hcS hSC ↦ ⟨cbpDisj_commClean S prep h0 hpS, hcomm0 S hSA hSB hcS hSC,
      CommCleanBracket.reverse hp_si (cbpDisj_commClean S prep h0 hpS)⟩,
    fun β ↦ ph0 (prep.evalBits β), g, fun β ↦ by
      dsimp only [prog, conjTAddProg]
      simp only [AndBracketProg.toCircuit, Circuit.eval_seq,
          Submonoid.coe_mul,
        ← Matrix.mulVec_mulVec, prep.toBracket_ket β, hev0 (prep.evalBits β), ← hprep_g β,
            Matrix.mulVec_smul, hrev_ket (g β)],
    hg_out, fun β hc0 ↦ ?_⟩
  obtain ⟨hp_v, hs_v⟩ := hval0 (prep.evalBits β) fun i ↦
    ((cbpDisj_evalBits prep hPC fun _ _ ↦ rfl).2 (rCarry i) fun h ↦ h ⟨i, rfl⟩).trans (hc0 i)
  rw [PhotochemistrySolution.SelectFastRouterEval.regVal_congr rB _ β fun j ↦
    (cbpDisj_evalBits prep hPB fun _ _ ↦ rfl).2 (rB j) fun h ↦ h ⟨j, rfl⟩] at hp_v hs_v
  exact ⟨hp_v, (PhotochemistrySolution.SelectFastRouterEval.regVal_congr rB _ _ fun j ↦
    DynCircExt.writeReg_apply_reg β rB _ j).trans hs_v⟩
/-! ### `layerJ1DirectCirc`, `layerJTopTSCirc`, & `TAddCatShiftSpec` -/

theorem update_self_add_cancel_qft8 {M : ℕ} (β : BitAssignment M) {a b : Wire M} (hne : a ≠ b) :
    Function.update (Function.update β b (β b + β a)) b
      (Function.update β b (β b + β a) b + Function.update β b (β b + β a) a) = β := by
  ext u
  by_cases hu : u = b
  · subst hu
    simp only [Function.update_self, Function.update_of_ne hne, add_assoc,
        CharTwo.add_self_eq_zero, add_zero]
  · simp only [Function.update_of_ne hu]
theorem layerJ1DirectCirc_eval {M : ℕ} (rP : QRegister 8 M) :
    EvalPhase8Perm (.prim (layerJ1DirectCirc rP))
      (fun β ↦ ((β (rP 1)).val + 7 * (β (rP 0) + β (rP 1)).val : ℕ))
      (fun β ↦ β) := fun β ↦ by
  dsimp only [AndBracketProg.toCircuit, layerJ1DirectCirc]
  simp only [Circuit.eval_seq, Submonoid.coe_mul, ← Matrix.mulVec_mulVec, ket_T_eval8,
    KinB.ket_CNOT, ket_TInv_eval8, Matrix.mulVec_smul, smul_smul, ← phase8Exp_add]
  rw [update_self_add_cancel_qft8 β (rP.wires.injective.ne (fin8_ne rfl)), Function.update_self,
      add_comm (β (rP 1)) (β (rP 0))]
  exact congrArg (· • KinB.ket β) (congrArg phase8Exp (by
    push_cast
    ring))
theorem layerJTopTSCirc_eval {M : ℕ} (pPrev pJ : Wire M) (hne : pPrev ≠ pJ) :
    EvalPhase8Perm (.prim (layerJTopTSCirc pPrev pJ hne))
      (fun β ↦ (7 * (β pPrev + β pJ).val + 2 * (β pJ).val : ℕ))
      (fun β ↦ β) := fun β ↦ by
  dsimp only [AndBracketProg.toCircuit, layerJTopTSCirc]
  simp only [Circuit.eval_seq, Submonoid.coe_mul, ← Matrix.mulVec_mulVec, KinB.ket_CNOT,
    ket_TInv_eval8, ket_S_eval8, Matrix.mulVec_smul, smul_smul, ← phase8Exp_add]
  rw [update_self_add_cancel_qft8 β hne, Function.update_self, add_comm (β pJ) (β pPrev)]
  exact congrArg (· • KinB.ket β) (congrArg phase8Exp (by
    push_cast
    ring))
def TAddCatShiftOn {M : ℕ} (rCat : QRegister 8 M) (cleanP : BitAssignment M → Prop)
    (Δ : BitAssignment M → ℕ) (p : AndBracketProg M) : Prop :=
  ∃ (ph8 : BitAssignment M → ZMod 8) (f : BitAssignment M → BitAssignment M),
    EvalPhase8Perm p ph8 f ∧
    (∀ (β : BitAssignment M) (u : Wire M),
      (∀ j : Fin 5, u ≠ rCat ⟨j.val, by omega⟩) → f β u = β u) ∧
    (∀ β : BitAssignment M, cleanP β →
      PhotochemistrySolution.regVal 5 (rCat.slice 0 5 slice05_le8) (f β) =
        (PhotochemistrySolution.regVal 5 (rCat.slice 0 5 slice05_le8) β + Δ β) % 32 ∧
      ph8 β =
        (((PhotochemistrySolution.regVal 5 (rCat.slice 0 5 slice05_le8) β + Δ β) /
            32 : ℕ) : ZMod 8))
abbrev TAddCatShiftSpec {M : ℕ} (rCat : QRegister 8 M) (rClean13 : QRegister 13 M)
    (Δ : BitAssignment M → ℕ) (p : AndBracketProg M) : Prop :=
    TAddCatShiftOn rCat (fun β ↦ ∀ j : Fin 13, β (rClean13 j) = 0) Δ p
theorem TAddCatShiftOn.comm_cleanProj {M : ℕ} {rCat : QRegister 8 M}
    {cleanP : BitAssignment M → Prop} {Δ : BitAssignment M → ℕ} {p : AndBracketProg M}
    (h : TAddCatShiftOn rCat cleanP Δ p) (S : Finset (Wire M))
    (hDisj : ∀ w ∈ S, ∀ j : Fin 5, w ≠ rCat ⟨j.val, by omega⟩) :
    p.toCircuit.eval.1 * cleanProj S = cleanProj S * p.toCircuit.eval.1 := by
  obtain ⟨ph8, f, hev, hout, _⟩ := h
  exact EvalPhase8Perm.comm_cleanProj_of_fix hev S fun β w hw ↦ hout β w (hDisj w hw)
theorem TAddCatShiftOn.localOnQft16_both {M : ℕ} {rCat : QRegister 8 M}
    {cleanP : BitAssignment M → Prop} {Δ : BitAssignment M → ℕ} {p : AndBracketProg M}
    (rP : QRegister 8 M) (h : TAddCatShiftOn rCat cleanP Δ p) :
    LocalOnQft16 rP rCat p.toCircuit.eval.1 ∧ LocalOnQft16 rP rCat (p.toCircuit.eval⁻¹).1 := by
  obtain ⟨ph8, f, hev, hout, _⟩ := h
  exact EvalPhase8Perm.localOnQft16_both rP rCat hev fun β u _ hc ↦
    hout β u fun j e ↦ hc ⟨⟨j.val, by omega⟩, e.symm⟩
theorem TAddCatShiftOn.weaken {M : ℕ} {rCat : QRegister 8 M} {P₁ P₂ : BitAssignment M → Prop}
    {Δ : BitAssignment M → ℕ} {p : AndBracketProg M} (h : TAddCatShiftOn rCat P₁ Δ p)
    (himp : ∀ β, P₂ β → P₁ β) : TAddCatShiftOn rCat P₂ Δ p := by
  obtain ⟨ph8, f, hev, hout, hv⟩ := h
  exact ⟨ph8, f, hev, hout, fun β h₂ ↦ hv β (himp β h₂)⟩
theorem TAddCatShiftSpec.of_diag8 {M : ℕ} (rCat : QRegister 8 M) (rClean13 : QRegister 13 M)
    (k : BitAssignment M → ℕ) (p : AndBracketProg M)
    (hep : EvalPhase8Perm p (fun β ↦ (k β : ZMod 8)) (fun β ↦ β)) :
    TAddCatShiftSpec rCat rClean13 (fun β ↦ 32 * k β) p := by
  refine ⟨fun β ↦ (k β : ZMod 8), fun β ↦ β, hep, fun _ _ _ ↦ rfl, fun β _ ↦ ?_⟩
  dsimp only
  have hlt : PhotochemistrySolution.regVal 5 (rCat.slice 0 5 slice05_le8) β < 32 :=
      regVal_lt_two_pow_local 5 _ β
  exact ⟨by omega, congrArg Nat.cast (by omega)⟩
theorem TAddCatShiftSpec.seq {M : ℕ} {rCat : QRegister 8 M} {rClean13 : QRegister 13 M}
    (hCatClean : rCat.DisjointWires rClean13)
    {Δ₁ Δ₂ : BitAssignment M → ℕ} {p₁ p₂ : AndBracketProg M}
    (h₁ : TAddCatShiftSpec rCat rClean13 Δ₁ p₁)
    (h₂ : TAddCatShiftSpec rCat rClean13 Δ₂ p₂)
    (hInv₂ : ∀ γ₁ γ₂ : BitAssignment M,
      (∀ u, (∀ j : Fin 5, u ≠ rCat ⟨j.val, by omega⟩) → γ₁ u = γ₂ u) → Δ₂ γ₁ = Δ₂ γ₂) :
    TAddCatShiftSpec rCat rClean13 (fun β ↦ Δ₁ β + Δ₂ β) (.seq p₁ p₂) := by
  rcases h₁, h₂ with ⟨⟨ph₁, f₁, hev₁, hout₁, hv₁⟩, ⟨ph₂, f₂, hev₂, hout₂, hv₂⟩⟩
  refine ⟨fun β ↦ ph₁ β + ph₂ (f₁ β), fun β ↦ f₂ (f₁ β), EvalPhase8Perm.seq hev₁ hev₂,
    fun β u hu ↦ (hout₂ (f₁ β) u hu).trans (hout₁ β u hu), fun β h0 ↦ ?_⟩
  dsimp only
  obtain ⟨hs₁, hp₁⟩ := hv₁ β h0
  obtain ⟨hs₂, hp₂⟩ := hv₂ (f₁ β) fun j ↦
    (hout₁ β (rClean13 j) fun c e ↦ hCatClean.ne ⟨c.val, by omega⟩ j e.symm).trans (h0 j)
  rw [hInv₂ (f₁ β) β (hout₁ β), hs₁] at hs₂ hp₂
  refine ⟨hs₂.trans (by omega), ?_⟩
  rw [hp₁, hp₂, ← Nat.cast_add]
  exact congrArg Nat.cast (by omega)
theorem mod_div_shift_32 (s m : ℕ) (hs : s + m = 5) (lo S : ℕ) (hlo : lo < 2 ^ s) : lo + 2 ^ s *
    (S % 2 ^ m) = (lo + 2 ^ s * S) % 32 ∧ S / 2 ^ m = (lo + 2 ^ s * S) / 32 := by
  have hpow : 2 ^ s * 2 ^ m = 32 := by
    rw [← pow_add, hs]
    rfl
  have hlt : lo + 2 ^ s * (S % 2 ^ m) < 32 := by
    have hm :=
        Nat.mul_le_mul_left (2 ^ s)
        (Nat.succ_le_of_lt (Nat.mod_lt S (pow_pos (by decide : 0 < 2) m)))
    rw [Nat.mul_succ, hpow] at hm
    omega
  have hexp : lo + 2 ^ s * S = (lo + 2 ^ s * (S % 2 ^ m)) + (S / 2 ^ m) * 32 := by
    conv_lhs => rw [(Nat.div_add_mod S (2 ^ m)).symm]
    rw [show lo + 2 ^ s * (2 ^ m * (S / 2 ^ m) + S % 2 ^ m) =
      (lo + 2 ^ s * (S % 2 ^ m)) + (S / 2 ^ m) * (2 ^ s * 2 ^ m) by ring, hpow]
  exact ⟨by rw [hexp, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hlt],
    by rw [hexp, Nat.add_mul_div_right _ _ (by decide : 0 < 32), Nat.div_eq_zero_iff.mpr (.inr hlt),
         zero_add]⟩
theorem TAddCatShiftOn.conjTAdd {M : ℕ} (rCat : QRegister 8 M) (s m : ℕ) (hs : s + m = 5)
    (hs8 : s + m ≤ 8) (prep : ClassicalBracketProg M) (h0 : prep.numTempAnd = 0)
    (rA rCarry : QRegister m M) (cIn : Wire M) (hAB : rA.DisjointWires (rCat.slice s m hs8))
    (hAC : rA.DisjointWires rCarry) (hBC : (rCat.slice s m hs8).DisjointWires rCarry)
    (hcA : cIn ∉ Set.range rA.wires) (hcB : cIn ∉ Set.range (rCat.slice s m hs8).wires)
    (hcC : cIn ∉ Set.range rCarry.wires)
    (hPB : CBPDisj (fun u ↦ u ∉ Set.range (rCat.slice s m hs8).wires) prep)
    (hPC : CBPDisj (fun u ↦ u ∉ Set.range rCarry.wires) prep) : TAddCatShiftOn rCat (fun β ↦
    ∀ i : Fin m, β (rCarry i) = 0)
    (fun β ↦ 2 ^ s * (PhotochemistrySolution.regVal m rA (prep.evalBits β) +
    (prep.evalBits β cIn).val))
    (conjTAddProg prep m rA (rCat.slice s m hs8) rCarry cIn hAB hAC hBC hcA hcB hcC) := by
  let rB : QRegister m M := rCat.slice s m hs8
  obtain ⟨_, ph, g, hev, hg_out, hval⟩ :=
      conjTAddProg_spec prep h0 m rA rB rCarry cIn hAB hAC hBC hcA hcB hcC hPB hPC
  have hsplit (γ : BitAssignment M) :
      PhotochemistrySolution.regVal 5 (rCat.slice 0 5 slice05_le8) γ =
      PhotochemistrySolution.regVal s (rCat.slice 0 s (by omega)) γ + 2 ^ s *
          PhotochemistrySolution.regVal m rB γ := by
    rw [regVal_eq_of_wires_eq_qft8 hs.symm (rCat.slice 0 5 slice05_le8) (rCat.slice 0 (s + m)
        (by omega)) γ
          (fun _ _ _ ↦ congrArg rCat.wires (Fin.ext (by
            dsimp [QRegister.slice]
            omega))),
        regVal_slice_split_local s m (rCat.slice 0 (s + m) (by omega)) γ,
        regVal_eq_of_wires_eq_qft8 rfl _ (rCat.slice 0 s (by omega)) γ
          (fun _ _ _ ↦ congrArg rCat.wires (Fin.ext (by
            dsimp [QRegister.slice]
            omega))),
        regVal_eq_of_wires_eq_qft8 rfl _ rB γ
          (fun _ _ _ ↦ congrArg rCat.wires (Fin.ext (by
            dsimp [rB, QRegister.slice]
            omega)))]
  refine ⟨ph, g, hev, fun β u hu ↦ hg_out β u fun ⟨j, hj⟩ ↦ hu ⟨s + j.val, by omega⟩ hj.symm,
      fun β hc0 ↦ ?_⟩
  dsimp only
  obtain ⟨hp_v, hs_v⟩ := hval β hc0
  obtain ⟨hm1, hm2⟩ :=
      mod_div_shift_32 s m hs (PhotochemistrySolution.regVal s (rCat.slice 0 s (by omega)) β)
    (PhotochemistrySolution.regVal m rB β + PhotochemistrySolution.regVal m rA (prep.evalBits β) +
        (prep.evalBits β cIn).val)
    (regVal_lt_two_pow_local s _ β)
  have hs_eq : PhotochemistrySolution.regVal s (rCat.slice 0 s (by omega)) β +
      2 ^ s * (PhotochemistrySolution.regVal m rB β +
          PhotochemistrySolution.regVal m rA (prep.evalBits β) + (prep.evalBits β cIn).val) =
      PhotochemistrySolution.regVal 5 (rCat.slice 0 5 slice05_le8) β +
        2 ^ s * (PhotochemistrySolution.regVal m rA (prep.evalBits β) + (prep.evalBits β cIn).val)
            := by
              rw [hsplit β]
              ring
  exact
      ⟨by rw [hsplit (g β), SelectFastRouterEval.regVal_congr _ (g β) β fun j ↦
            hg_out β _ fun ⟨idx, hm⟩ ↦ by
      have hv : s + idx.val = 0 + j.val :=
          congrArg Fin.val (rCat.wires.injective hm)
      have := j.isLt
      omega,
      hs_v, hm1, hs_eq], by rw [hp_v, hm2, hs_eq]⟩
theorem TAddCatShiftOn.tempAnd_comm {M : ℕ} {rCat : QRegister 8 M}
    {cleanP : BitAssignment M → Prop} {Δ : BitAssignment M → ℕ} {body : AndBracketProg M}
    (c₁ c₂ anc : Wire M) (h₁₂ : c₁ ≠ c₂) (h₁a : c₁ ≠ anc) (h₂a : c₂ ≠ anc)
    (hc₁ : ∀ j : Fin 5, c₁ ≠ rCat ⟨j.val, by omega⟩)
    (hc₂ : ∀ j : Fin 5, c₂ ≠ rCat ⟨j.val, by omega⟩)
    (hanc : ∀ j : Fin 5, anc ≠ rCat ⟨j.val, by omega⟩)
    (hBody : TAddCatShiftOn rCat cleanP Δ body) :
    let toff := fun γ : BitAssignment M ↦ Function.update γ anc (γ anc + γ c₁ * γ c₂)
    body.toCircuit.eval.1 * andInvProj c₁ c₂ anc = andInvProj c₁ c₂ anc * body.toCircuit.eval.1 ∧
    TAddCatShiftOn rCat (fun β ↦ cleanP (toff β)) (fun β ↦ Δ (toff β))
        (.tempAnd c₁ c₂ anc h₁₂ h₁a h₂a body) := by
  intro toff
  obtain ⟨ph, f, hev, hout, hv⟩ := hBody
  have hB (γ : BitAssignment M) : PhotochemistrySolution.regVal 5 (rCat.slice 0 5 slice05_le8)
      (toff γ) =
      PhotochemistrySolution.regVal 5 (rCat.slice 0 5 slice05_le8) γ :=
    PhotochemistrySolution.SelectFastRouterEval.regVal_congr _ _ _ fun j ↦ by
      rw [show (rCat.slice 0 5 slice05_le8) j = rCat ⟨j.val, by omega⟩ from
        congrArg rCat.wires (Fin.ext (by
          dsimp [QRegister.slice]
          omega))]
      exact Function.update_of_ne (fun e ↦ hanc j e.symm) _ _
  refine ⟨EvalPhase8Perm.comm_andInvProj_of_fix hev c₁ c₂ anc fun β ↦ ⟨hout β c₁ hc₁, hout β c₂ hc₂,
      hout β anc hanc⟩,
    fun β ↦ ph (toff β), fun β ↦
        toff (f (toff β)), EvalPhase8Perm.tempAnd c₁ c₂ anc h₁₂ h₁a h₂a body ph f hev,
    fun β u hu ↦ by
      dsimp only [toff]
      rcases eq_or_ne u anc with rfl | hua
      · rw [Function.update_self, hout _ _ hanc, hout _ c₁ hc₁, hout _ c₂ hc₂, Function.update_self,
          Function.update_of_ne h₁a, Function.update_of_ne h₂a, add_assoc, CharTwo.add_self_eq_zero,
              add_zero]
      · rw [Function.update_of_ne hua, hout _ u hu, Function.update_of_ne hua], fun β hc ↦ ?_⟩
  obtain ⟨hs, hp⟩ :=
      hv (toff β) hc
  dsimp only
  rw [hB (f (toff β)), hs, hB β, hp, hB β]
  exact ⟨rfl, rfl⟩
set_option exponentiation.threshold 8192
open PhotochemistrySolution.SelectQft8CatKick
/-! ### 1. `exp256` & `StepPD` Bit-Level Evaluation of `prepJT5` and `prepJ7T5` -/

noncomputable def exp256 (k : ℕ) : ℂ :=
    Complex.exp (2 * Real.pi * Complex.I * ((k : ℝ) / (2 ^ 8 : ℝ)))
theorem exp256_zero : exp256 0 = 1 := by simp [exp256]
theorem exp256_add (a b : ℕ) : exp256 (a + b) = exp256 a * exp256 b := by
  unfold exp256
  rw [← Complex.exp_add]
  exact congrArg Complex.exp (by
    push_cast
    ring)
theorem exp256_mod (a : ℕ) : exp256 (a % 256) = exp256 a :=
    PhotochemistrySolution.exp_two_pi_I_mod_div_two_pow 8 a
theorem exp256_congr {a b : ℕ} (h : a % 256 = b % 256) : exp256 a = exp256 b := by
  rw [← exp256_mod a, ← exp256_mod b, h]
theorem star_exp256_mul_self (a : ℕ) : star (exp256 a) * exp256 a = 1 := by
  unfold exp256
  rw [Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add]
  rw [show (starRingEnd ℂ) (2 * ↑Real.pi * Complex.I * ((a : ℝ) / (2 ^ 8 : ℝ))) +
      2 * ↑Real.pi * Complex.I * ((a : ℝ) / (2 ^ 8 : ℝ)) = 0 by
    simp only [map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I, map_div₀]
    ring,
        Complex.exp_zero]
theorem phase8Exp_natCast_eq_exp256 (k : ℕ) : phase8Exp (k : ZMod 8) = exp256 (32 * k) := by
  let q := k % 8
  have hcast : (k : ZMod 8) = (q : ZMod 8) := by
    conv_lhs => rw [← Nat.div_add_mod k 8]
    rw [Nat.cast_add, Nat.cast_mul, show ((8 : ℕ) : ZMod 8) = 0 from rfl, zero_mul, zero_add]
  rw [hcast, phase8Exp, ZMod.val_natCast_of_lt (Nat.mod_lt _ (by decide)),
    exp256_congr (show (32 * k) % 256 = (32 * q) % 256 by
      dsimp only [q]
      omega), exp256]
def fin8Bits (k : Fin (2 ^ 8)) : Fin 8 → Bool := fun i ↦ decide (basisBits 8 k i = 1)
theorem cond_fin8Bits (k : Fin (2 ^ 8)) (i : Fin 8) : cond (fin8Bits k i) 1 0 =
    (basisBits 8 k i).val :=
  (show ∀ b : ZMod 2, cond (decide (b = 1)) 1 0 = b.val by decide) _
theorem cond_pBits {M : ℕ} (rP : QRegister 8 M) (β : BitAssignment M)
    (i : Fin 8) : cond (pBits rP β i) 1 0 = (β (rP i)).val :=
  (show ∀ b : ZMod 2, cond (decide (b = 1)) 1 0 = b.val by decide) _
theorem pBits_eq_fin8Bits_readRegIdx {M : ℕ} (rP : QRegister 8 M) (β : BitAssignment M) :
    pBits rP β = fin8Bits (readRegIdx rP β) :=
  funext fun i ↦ by
    dsimp only [pBits, fin8Bits]
    rw [basisBits_readRegIdx rP β i]
theorem val_xor_bits (a b : ZMod 2) (pa pb : Bool) (ha : a.val = cond pa 1 0)
    (hb : b.val = cond pb 1 0) : (a + b).val = cond (xor pa pb) 1 0 :=
    FastQft8.val_add_bit a b pa pb ha hb
def dkJT5Bool (p : Fin 8 → Bool) (j : Fin 8) (m : ℕ) : Fin 7 → Bool := fun k ↦
    if k.val < m then xor (xor true (p (Fin.ofNat 8 k.val))) (p j) else false
theorem stepPD_prepJT5Prefix {M : ℕ} (rP : QRegister 8 M) (rDelta : QRegister 7 M)
    (hPDelta : rP.DisjointWires rDelta) (j : Fin 8) (p : Fin 8 → Bool) :
    ∀ (m : ℕ) (hm : m ≤ 5),
      StepPD rP rDelta (prepJT5Prefix rP rDelta hPDelta j m hm)
        p (fun _ ↦ false) p (dkJT5Bool p j m)
  | 0, _ => fun _ h ↦ h
  | m + 1, hm => by
      let hb := prepJT5_step_bounds hm
      have hd_eq : updD (dkJT5Bool p j m) ⟨m, hb.2.1⟩
          (xor (xor (!(dkJT5Bool p j m ⟨m, hb.2.1⟩)) (p ⟨m, hb.2.2⟩)) (p j)) = dkJT5Bool p j (m + 1)
              := funext fun k ↦ by
        rcases eq_or_ne k ⟨m, hb.2.1⟩ with rfl | hk
        · simp only [updD, ↓reduceIte, dkJT5Bool, Nat.lt_irrefl m, Nat.lt_succ_self m,
            show (⟨m, hb.2.2⟩ : Fin 8) =
                Fin.ofNat 8 m from Fin.ext (by
                  change m = m % 8
                  omega)]
          rfl
        · simp only [updD, hk, ↓reduceIte, dkJT5Bool,
            show (k.val < m + 1) ↔ (k.val < m) by have : k.val ≠ m := Fin.val_ne_of_ne hk; omega]
      exact (stepPD_prepJT5Prefix rP rDelta hPDelta j p m hb.1).seq
        (hd_eq ▸ StepPD.tripleXCC hPDelta p (dkJT5Bool p j m) ⟨m, hb.2.1⟩ ⟨m, hb.2.2⟩ j)
theorem prepJT5_shift_eq_bool {M : ℕ} (rP : QRegister 8 M) (rDelta : QRegister 7 M)
    (hPDelta : rP.DisjointWires rDelta) (j : Fin 8) (hj2 : 2 ≤ j.val) (hj7 : j.val < 7)
    (β : BitAssignment M) (hD0 : ∀ k : Fin 7, β (rDelta k) = 0) :
    let hb := layerJT5_bounds hj2 hj7;
    let prep := prepJT5 rP rDelta hPDelta j (j.val - 1) hb.2.2.2.1;
    let jPrev : Fin 8 := ⟨j.val - 1, hb.2.2.2.2⟩
    2 ^ (6 - j.val) *
        (PhotochemistrySolution.regVal (j.val - 1) (rDelta.slice 0 (j.val - 1) hb.1)
            (prep.evalBits β) +
          (prep.evalBits β (rP j)).val) +
      32 * (7 * (β (rP jPrev) + β (rP j)).val + 2 * (β (rP j)).val) =
      deltaLayerBool j (pBits rP β) := by
  intro hb prep jPrev
  let p := pBits rP β
  have hstep : MatchesPD rP rDelta (prep.evalBits β) (updP p j (!p j)) (dkJT5Bool p j (j.val - 1))
      :=
    (stepPD_prepJT5Prefix rP rDelta hPDelta j p (j.val - 1) hb.2.2.2.1).seq
      (StepPD.xP hPDelta p (dkJT5Bool p j (j.val - 1)) j) β (matchesPD_init rP rDelta β hD0)
  dsimp only [deltaLayerBool]
  simp only [show ¬ j.val = 0 by omega, show ¬ j.val = 1 by omega,
      hj7, ↓reduceIte]
  rw [regVal_eq_bool (j.val - 1) _ (prep.evalBits β)
      (fun i ↦ xor (xor true (p (Fin.ofNat 8 i.val))) (p j)) (fun i ↦ by
        rw [show (rDelta.slice 0 (j.val - 1) hb.1) i = rDelta ⟨i.val, by omega⟩ from
          congrArg rDelta.wires (Fin.ext (by
            dsimp [QRegister.slice]
            omega)), hstep.2 ⟨i.val,
              by omega⟩]
        simp only [dkJT5Bool, i.isLt, ↓reduceIte]),
    show (prep.evalBits β (rP j)).val = cond (!p j) 1 0 by
      rw [hstep.1 j]
      simp [updP],
    val_xor_bits _ _ _ _ ((congrArg (fun idx ↦ (β (rP idx)).val)
      (Fin.ext (by
        change j.val - 1 = (j.val - 1) % 8
        omega))).trans
        (cond_pBits rP β (Fin.ofNat 8 (j.val - 1))).symm)
      (cond_pBits rP β j).symm, (cond_pBits rP β j).symm]
theorem matchesPD_toff5Step {M : ℕ} {rP : QRegister 8 M} {rDelta : QRegister 7 M}
    (hPDelta : rP.DisjointWires rDelta) {γ : BitAssignment M} {p : Fin 8 → Bool} {d : Fin 7 → Bool}
    (h : MatchesPD rP rDelta γ p d) : MatchesPD rP rDelta (Function.update γ (rDelta 5)
    (γ (rDelta 5) + γ (rP 7) * γ (rP 0))) p (updD d 5 (xor (d 5) (p 7 && p 0))) := by
  refine ⟨fun m ↦ by
    rw [Function.update_of_ne (hPDelta.ne m 5)]
    exact h.1 m, fun j ↦ ?_⟩
  rcases eq_or_ne j 5 with rfl | hj5
  · simp only [Function.update_self, updD, ↓reduceIte]
    exact val_toff_bit _ _ _ _ _ _ (h.2 5)
        (h.1 7) (h.1 0)
  · rw [Function.update_of_ne (rDelta.wires.injective.ne hj5)]
    simp only [updD, hj5,
        ↓reduceIte]
    exact h.2 j
theorem prepJ7T5_shift_eq_bool {M : ℕ} (rP : QRegister 8 M) (rDelta : QRegister 7 M)
    (hPDelta : rP.DisjointWires rDelta)
    (β : BitAssignment M) (hD0 : ∀ k : Fin 7, β (rDelta k) = 0) :
    let γ0 := Function.update β (rDelta 5) (β (rDelta 5) + β (rP 7) * β (rP 0));
    let prep := prepJ7T5 rP rDelta hPDelta
    2 ^ 0 *
        (PhotochemistrySolution.regVal 5 (rDelta.slice 0 5 slice05_le7) (prep.evalBits γ0) +
          (prep.evalBits γ0 (rDelta 5)).val) +
      32 * (7 * (β (rP 6) + β (rP 7)).val + 2 * (β (rP 7)).val) =
      deltaLayerBool 7 (pBits rP β) := by
  intro γ0 prep
  let p := pBits rP β
  have ht5 : MatchesPD rP rDelta γ0 p (vec7 false false false false false (p 7 && p 0) false) := by
    have h := matchesPD_toff5Step (p := p) hPDelta (matchesPD_init rP rDelta β hD0)
    rw [fun_false_eq_vec7, updD_vec7_5] at h
    simpa only [Bool.false_xor] using h
  have hs := ((StepPD.tripleXCC hPDelta p _ 0 1 7).seq ((StepPD.tripleXCC hPDelta p _ 1 2 7).seq
    ((StepPD.tripleXCC hPDelta p _ 2 3 7).seq ((StepPD.tripleXCC hPDelta p _ 3 4 7).seq
      ((StepPD.tripleXCC hPDelta p _ 4 5 7).seq (StepPD.pairXC hPDelta p _ 5 7)))))) γ0 ht5
  simp only [updD_vec7_0, updD_vec7_1, updD_vec7_2, updD_vec7_3, updD_vec7_4, updD_vec7_5] at hs
  change MatchesPD rP rDelta (prep.evalBits γ0) p _ at hs
  dsimp only [deltaLayerBool]
  simp only [show ¬ (7 : Fin 8).val = 0 by decide,
      show ¬ (7 : Fin 8).val = 1 by decide,
    show ¬ (7 : Fin 8).val < 7 by decide, ↓reduceIte, pow_zero, one_mul]
  rw [regVal_eq_bool 5 (rDelta.slice 0 5 slice05_le7) (prep.evalBits γ0)
      (fun i ↦ xor (xor true (p (Fin.ofNat 8 (i.val + 1)))) (p 7))
          (fun i ↦ by fin_cases i <;> exact hs.2 _),
    hs.2 5, val_xor_bits _ _ _ _ (cond_pBits rP β 6).symm (cond_pBits rP β 7).symm,
        (cond_pBits rP β 7).symm]
  rfl
/-! ### 2. `TAddCatShiftSpec`, `LocalOnQft16`, and `CleanStepPair13AbpInv` for All Blocks -/

def shiftJT5 {M : ℕ} (rP : QRegister 8 M) (rDelta : QRegister 7 M)
    (hPDelta : rP.DisjointWires rDelta) (j : Fin 8) (hj2 : 2 ≤ j.val) (hj7 : j.val < 7)
    (β : BitAssignment M) : ℕ :=
  let hb := layerJT5_bounds hj2 hj7; let prep := prepJT5 rP rDelta hPDelta j (j.val - 1) hb.2.2.2.1;
  let jPrev : Fin 8 := ⟨j.val - 1, hb.2.2.2.2⟩
  2 ^ (6 - j.val) *
      (PhotochemistrySolution.regVal (j.val - 1) (rDelta.slice 0 (j.val - 1) hb.1)
          (prep.evalBits β) +
        (prep.evalBits β (rP j)).val) +
    32 * (7 * (β (rP jPrev) + β (rP j)).val + 2 * (β (rP j)).val)
def shiftJ7T5 {M : ℕ} (rP : QRegister 8 M) (rDelta : QRegister 7 M)
    (hPDelta : rP.DisjointWires rDelta) (β : BitAssignment M) : ℕ :=
  let γ0 := Function.update β (rDelta 5) (β (rDelta 5) + β (rP 7) * β (rP 0));
  let prep := prepJ7T5 rP rDelta hPDelta
  2 ^ 0 *
      (PhotochemistrySolution.regVal 5 (rDelta.slice 0 5 slice05_le7) (prep.evalBits γ0) +
        (prep.evalBits γ0 (rDelta 5)).val) +
    32 * (7 * (β (rP 6) + β (rP 7)).val + 2 * (β (rP 7)).val)
theorem embedMatrix_diagonal_mulVec_ket8 {M : ℕ} (rP : QRegister 8 M)
    (d : Fin (2 ^ 8) → ℂ) (β : BitAssignment M) :
    (rP.embedMatrix (Matrix.diagonal d)).mulVec (PhotochemistrySolution.KinB.ket β) =
      d (readRegIdx rP β) • PhotochemistrySolution.KinB.ket β := by
  rw [embedMatrix_mulVec_ket_sym rP (Matrix.diagonal d) β, Finset.sum_eq_single (readRegIdx rP β)]
  · rw [Matrix.diagonal_apply_eq, writeReg_extractIndex_self_sym rP β]
  · exact fun z _ hz ↦ by rw [Matrix.diagonal_apply_ne _ hz, zero_smul]
  · exact fun h ↦ absurd (Finset.mem_univ _) h
theorem layerJ1DirectCirc_eq_embedMatrix {M : ℕ} (rP : QRegister 8 M) :
    (layerJ1DirectCirc rP).eval.1 =
      rP.embedMatrix (Matrix.diagonal (fun u ↦ exp256 (deltaLayerBool 1 (fin8Bits u)))) := by
  refine PhotochemistrySolution.KinB.matrix_ext_ket fun β ↦ ?_
  have hlhs := layerJ1DirectCirc_eval rP β
  dsimp only [AndBracketProg.toCircuit] at hlhs
  rw [hlhs, phase8Exp_natCast_eq_exp256, embedMatrix_diagonal_mulVec_ket8]
  refine congrArg (· • PhotochemistrySolution.KinB.ket β) (congrArg exp256 ?_)
  dsimp only [deltaLayerBool]
  simp only [Fin.val_one, Nat.one_ne_zero, ↓reduceIte, ← pBits_eq_fin8Bits_readRegIdx rP β]
  rw [← (cond_pBits rP β 1).symm,
    ← val_xor_bits _ _ _ _ (cond_pBits rP β 0).symm (cond_pBits rP β 1).symm]
theorem preJ01Circ_eq_embedMatrix {M : ℕ} (rP : QRegister 8 M) :
    (polySwapAll8Circ rP ;;ᶜ Circuit.H (rP 0) ;;ᶜ layerJ1DirectCirc rP ;;ᶜ
        Circuit.H (rP 1)).eval.1 =
      rP.embedMatrix ((hadamardAt 8 1).1 *
        (Matrix.diagonal (fun u ↦ exp256 (deltaLayerBool 1 (fin8Bits u))) *
          ((hadamardAt 8 0).1 * (QFT.swapAllUnitary 8).1))) := by
  simp only [Circuit.eval_seq, Submonoid.coe_mul, eval_polySwapAll8Circ_eq_swapAllUnitary_noSym rP,
      eval_H_eq_embedMatrix8_noSym rP, layerJ1DirectCirc_eq_embedMatrix rP, ← rP.embedMatrix_mul,
      Matrix.mul_assoc]
/-- `6`-wire clean subregister `[rDelta 5, rCarry 0, ..., rCarry 4]` of `rClean13` for `j = 7`. -/
def rSub6J7 {M : ℕ} (rDelta : QRegister 7 M) (rCarry : QRegister 6 M)
    (hDCarry : rDelta.DisjointWires rCarry) : QRegister 6 M where
  wires :=
    { toFun := fun i ↦ if i.val = 0 then rDelta 5 else rCarry ⟨i.val - 1, by omega⟩
      inj' := fun a b e ↦ by
        dsimp only at e
        split_ifs at e with ha hb hb
        · exact Fin.ext (ha.trans hb.symm)
        · exfalso; exact hDCarry.ne 5 _ e
        · exfalso; exact hDCarry.ne 5 _ e.symm
        · have hv := congrArg Fin.val (rCarry.wires.injective e); change a.val - 1 = b.val - 1 at hv
          exact Fin.ext (by omega) }
end QuantumComputation.Specs.PhotochemistrySolution.Qft8PostCancelT5
end

section
set_option exponentiation.threshold 8192
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Stage4Kin14Scb (abpKin14Usel wOutKin226)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB (ComputeProg)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.XMeasUnld (xorWireUnitary_mulVec_ket
    permUnitary permUnitary_mulVec_ket)

noncomputable section
set_option maxRecDepth 4096
namespace QuantumComputation.Specs.PhotochemistrySolution.Qft8PostCancelT5
open Operator QProg DynamicCircuit Matrix Circuit Qubit PrimitiveGate QFT QuantumComputation.Specs
  PhotochemistrySolution PhotochemistrySolution.SelectSymDynInstance
  PhotochemistrySolution.SelectRefl PhotochemistrySolution.SelectDataBuilder
  PhotochemistrySolution.SelectFastQft8Gidney PhotochemistrySolution.SelectFastFlags
  PhotochemistrySolution.SelectCompactAnc
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
  _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt
open PhotochemistrySolution.SelectQft8GidneyStg3 PhotochemistrySolution.SelectQft8CatLocal
open PhotochemistrySolution.SelectQft8CatKick PhotochemistrySolution.FastQft8
  PhotochemistrySolution.SelectQft8KinMid
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB hiding writeReg
  writeReg_apply_of_not_mem ket ket_X ket_CNOT ket_TOFF matrix_ext_ket bitSign
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SelectCsa64ProvSpec
  (compose_basisOutcomeProjector_zero)
open scoped Circuit.Notation
theorem postCancelBlocks_catShift_and_step {Var : Type} [Fintype Var] [DecidableEq Var]
    {M n : ℕ} [NeZero (2 ^ n)] (v : Var)
    (rTot : QRegister M n)
    (rCat rP : QRegister 8 M) (rDelta : QRegister 7 M) (rCarry : QRegister 6 M)
    (rClean13 : QRegister 13 M)
    (hPCat : rP.DisjointWires rCat) (hPDelta : rP.DisjointWires rDelta)
    (hDCat : rDelta.DisjointWires rCat) (hDCarry : rDelta.DisjointWires rCarry)
    (hCatCarry : rCat.DisjointWires rCarry) (hPCarry : rP.DisjointWires rCarry)
    (hSubD : ∀ i : Fin 7, rClean13 ⟨i.val, by omega⟩ = rDelta i)
    (hSubC : ∀ i : Fin 6, rClean13 ⟨7 + i.val, by omega⟩ = rCarry i) :
    (∀ (j : Fin 8) (hj2 : 2 ≤ j.val) (hj7 : j.val < 7),
      TAddCatShiftSpec rCat rClean13 (shiftJT5 rP rDelta hPDelta j hj2 hj7)
        (layerJT5Inner rCat rP rDelta rCarry hPCat hPDelta hDCat hDCarry hCatCarry hPCarry
          j hj2 hj7)) ∧
    TAddCatShiftSpec rCat rClean13 (shiftJ7T5 rP rDelta hPDelta)
      (layerJ7T5Inner rCat rP rDelta rCarry hPDelta hDCat hDCarry hCatCarry) ∧
    CleanStepPair13AbpInv v rTot rClean13
      (polyPostCancelT5Qft8Bracket98 rCat rP rDelta rCarry hPCat hPDelta hDCat hDCarry
        hCatCarry hPCarry) ∧
    (LocalOnQft16 rP rCat
      (polyPostCancelT5Qft8Bracket98 rCat rP rDelta rCarry hPCat hPDelta hDCat hDCarry
        hCatCarry hPCarry).toCircuit.eval.1 ∧
     LocalOnQft16 rP rCat
      ((polyPostCancelT5Qft8Bracket98 rCat rP rDelta rCarry hPCat hPDelta hDCat hDCarry
        hCatCarry hPCarry).toCircuit.eval⁻¹).1) := by
  have hCatClean := disjoint_rCat_clean13 rCat rDelta rCarry rClean13 hDCat hCatCarry hSubD hSubC
  have hPClean := disjoint_rP_clean13 rP rDelta rCarry rClean13 hPDelta hPCarry hSubD hSubC
  let S6 := Finset.univ.image rCarry.wires
  let S13 := Finset.univ.image rClean13.wires
  have hDisjS13 (w) (hw : w ∈ S13) (j : Fin 5) (e : w = rCat ⟨j.val, by omega⟩) : False :=
    (Finset.mem_image.mp hw).elim fun m hm ↦
        hCatClean.ne ⟨j.val, by omega⟩ m (e.symm.trans hm.2.symm)
  have hNotRk {w : ℕ} {r : QRegister w M} (hd : r.DisjointWires rCarry) (i : Fin w) : r i ∉ S6 :=
    fun h ↦ (Finset.mem_image.mp h).elim fun m hm ↦ hd.ne i m hm.2.symm
  have hCat_not_S6 {s w : ℕ} {hs : s + w ≤ 8} (i : Fin w) : (rCat.slice s w hs) i ∉ S6 :=
    fun h ↦ (Finset.mem_image.mp h).elim fun m hm ↦ hCatCarry.ne _ m hm.2.symm
  have hts_step (a b : Fin 8) (hne : rP a ≠ rP b) :
      CleanStepPair13AbpInv v rTot rClean13 (.prim (layerJTopTSCirc (rP a) (rP b) hne)) :=
    have hc := EvalPhase8Perm.comm_cleanProj_of_fix
      (layerJTopTSCirc_eval (rP a) (rP b) hne) S13 fun _ _ _ ↦ rfl
    CleanStepPair13AbpInv.of_subreg v rTot rClean13 rClean13 (fun i ↦ ⟨i, rfl⟩) _ hc hc
  have hts_inv_cat5 (a b : Fin 8) (γ₁ γ₂ : BitAssignment M)
      (h : ∀ u, (∀ c : Fin 5, u ≠ rCat ⟨c.val, by omega⟩) → γ₁ u = γ₂ u) :
      32 * (7 * (γ₁ (rP a) + γ₁ (rP b)).val + 2 * (γ₁ (rP b)).val) =
        32 * (7 * (γ₂ (rP a) + γ₂ (rP b)).val + 2 * (γ₂ (rP b)).val) := by
    rw [h (rP a) fun c e ↦ hPCat.ne a ⟨c.val, by omega⟩ e,
      h (rP b) fun c e ↦ hPCat.ne b ⟨c.val, by omega⟩ e]
  let stepLoc (p : AndBracketProg M) : Prop :=
    CleanStepPair13AbpInv v rTot rClean13 p ∧
      LocalOnQft16 rP rCat p.toCircuit.eval.1 ∧ LocalOnQft16 rP rCat (p.toCircuit.eval⁻¹).1
  have stepLoc_seq {p₁ p₂ : AndBracketProg M} (h₁ : stepLoc p₁) (h₂ : stepLoc p₂) :
      stepLoc (.seq p₁ p₂) := by
    refine ⟨CleanStepPair13AbpInv.seq h₁.1 h₂.1, ?_, ?_⟩
    · simp only [AndBracketProg.toCircuit, Circuit.eval_seq, Submonoid.coe_mul]
      exact LocalOnQft16.mul rP rCat h₂.2.1 h₁.2.1
    · simp only [AndBracketProg.toCircuit, Circuit.eval_seq, _root_.mul_inv_rev, Submonoid.coe_mul]
      exact LocalOnQft16.mul rP rCat h₁.2.2 h₂.2.2
  have hLoc_embed_rP {c : Circuit M} {A : Operator (2 ^ 8)} (hc : c.eval.1 = rP.embedMatrix A) :
      stepLoc (.prim c) :=
    ⟨CleanStepPair13AbpInv.of_prim_rP v rTot rClean13 rP hPClean c A hc,
      hc.symm ▸ LocalOnQft16.of_embed_rP rP rCat _, by
        change LocalOnQft16 rP rCat c.eval.1ᴴ
        rw [hc, ← rP.embedMatrix_conjTranspose]
        exact LocalOnQft16.of_embed_rP rP rCat _⟩
  have hBr_loc {inner : AndBracketProg M} {Δ : BitAssignment M → ℕ}
      (a j : Fin 8) (hne : rP a ≠ rP j)
      (hspec : TAddCatShiftSpec rCat rClean13 Δ
        (.seq inner (.prim (layerJTopTSCirc (rP a) (rP j) hne))))
      (hstep : CleanStepPair13AbpInv v rTot rClean13 inner) :
      stepLoc (.seq inner (.seq (.prim (layerJTopTSCirc (rP a) (rP j) hne)) (.prim (.H (rP j)))))
          := by
    obtain ⟨hH_s, hH_f, hH_i⟩ := hLoc_embed_rP (eval_H_eq_embedMatrix8_noSym rP j)
    have hev : (AndBracketProg.seq inner
        (.seq (.prim (layerJTopTSCirc (rP a) (rP j) hne)) (.prim (.H (rP j))))).toCircuit.eval =
        (Circuit.H (rP j)).eval *
        (AndBracketProg.seq inner (.prim (layerJTopTSCirc (rP a) (rP j) hne))).toCircuit.eval := by
      simp only [AndBracketProg.toCircuit, Circuit.eval_seq, mul_assoc]
    refine ⟨.seq hstep (.seq (hts_step a j hne) hH_s), ?_, ?_⟩
    · rw [hev, Submonoid.coe_mul]
      exact LocalOnQft16.mul rP rCat hH_f (hspec.localOnQft16_both rP).1
    · rw [hev, _root_.mul_inv_rev, Submonoid.coe_mul]
      exact LocalOnQft16.mul rP rCat (hspec.localOnQft16_both rP).2 hH_i
  let rSubJ7 := rSub6J7 rDelta rCarry hDCarry
  let SJ7 := Finset.univ.image rSubJ7.wires
  have hrSub (i : Fin 6) :
      rSubJ7 i = if i.val = 0 then rDelta 5 else rCarry ⟨i.val - 1, by omega⟩ := rfl
  have hSubJ7 (i : Fin 6) : ∃ j : Fin 13, rSubJ7 i = rClean13 j :=
    if hi0 : i.val = 0 then ⟨⟨5, by omega⟩, ((hrSub i).trans (ite_eq_left hi0)).trans (hSubD
        5).symm⟩
    else ⟨⟨7 + (i.val - 1), by omega⟩,
      ((hrSub i).trans (ite_eq_right hi0)).trans (hSubC ⟨i.val - 1, by omega⟩).symm⟩
  have hDisjSJ7 (w) (hw : w ∈ SJ7) (j : Fin 5) (e : w = rCat ⟨j.val, by omega⟩) : False :=
    (Finset.mem_image.mp hw).elim fun m hm ↦ (hSubJ7 m).elim fun k hk ↦
      hCatClean.ne ⟨j.val, by omega⟩ k (e.symm.trans (hm.2.symm.trans hk))
  let SJ7e := SJ7.erase (rDelta 5)
  have hSJ7e_sub (u) (hu : u ∈ SJ7e) : u ∈ S6 := by
    obtain ⟨hne, m, _, rfl⟩ := (Finset.mem_erase.mp hu).imp_right Finset.mem_image.mp
    exact if hm0 : m.val = 0 then absurd ((hrSub m).trans (ite_eq_left hm0)) hne
      else Finset.mem_image.mpr ⟨_, Finset.mem_univ _, ((hrSub m).trans (ite_eq_right hm0)).symm⟩
  have hC5_in_SJ7e (i : Fin 5) : (rCarry.slice 0 5 slice05_le6) i ∈ SJ7e := by
    rw [show (rCarry.slice 0 5 slice05_le6) i = rCarry ⟨i.val, by omega⟩ from
      congrArg rCarry.wires (Fin.ext (Nat.zero_add i.val))]
    refine Finset.mem_erase.mpr ⟨(hDCarry.ne 5 _).symm,
      Finset.mem_image.mpr ⟨⟨i.val + 1, by omega⟩, Finset.mem_univ _, ?_⟩⟩
    change (if i.val + 1 = 0 then rDelta 5 else rCarry ⟨i.val + 1 - 1, _⟩) =
      rCarry ⟨i.val, by omega⟩
    simp
  let h7d := layerJ7T5_disj hDCat hDCarry hCatCarry
  let p7 := prepJ7T5 rP rDelta hPDelta
  have hp7d (P : Wire M → Prop) (hP : ∀ i, P (rP i))
      (hD : ∀ i : Fin 6, P (rDelta ⟨i.val, by omega⟩)) :=
    prepJ7T5_zero_and_disj (P := P) rP rDelta hPDelta hP hD
  obtain ⟨hz7, hd7_B⟩ := hp7d (· ∉ Set.range (rCat.slice 0 5 slice05_le8).wires)
    (fun i ⟨_, e⟩ ↦ hPCat.ne i _ e.symm) fun _ ⟨_, e⟩ ↦ hDCat.ne _ _ e.symm
  have hd7_C := (hp7d (· ∉ Set.range (rCarry.slice 0 5 slice05_le6).wires)
    (fun i ⟨_, e⟩ ↦ hPCarry.ne i _ e.symm) fun _ ⟨_, e⟩ ↦ hDCarry.ne _ _ e.symm).2
  obtain ⟨hl7_and, hl7_temp_on⟩ := TAddCatShiftOn.tempAnd_comm (rP 7) (rP 0) (rDelta 5)
    (rP.wires.injective.ne (fin8_ne rfl)) (hPDelta.ne 7 5) (hPDelta.ne 0 5)
    (fun j e ↦ hPCat.ne 7 ⟨j.val, by omega⟩ e) (fun j e ↦ hPCat.ne 0 ⟨j.val, by omega⟩ e)
    (fun j e ↦ hDCat.ne 5 ⟨j.val, by omega⟩ e)
    (TAddCatShiftOn.conjTAdd rCat 0 5 rfl slice05_le8 p7 hz7
      (rDelta.slice 0 5 slice05_le7) (rCarry.slice 0 5 slice05_le6) (rDelta 5)
      h7d.1 h7d.2.1 h7d.2.2.1 h7d.2.2.2.1 h7d.2.2.2.2.1 h7d.2.2.2.2.2 hd7_B hd7_C)
  let l7t : AndBracketProg M := .tempAnd (rP 7) (rP 0) (rDelta 5)
    (rP.wires.injective.ne (fin8_ne rfl)) (hPDelta.ne 7 5) (hPDelta.ne 0 5)
    (conjTAddProg p7 5 (rDelta.slice 0 5 slice05_le7) (rCat.slice 0 5 slice05_le8)
      (rCarry.slice 0 5 slice05_le6) (rDelta 5)
      h7d.1 h7d.2.1 h7d.2.2.1 h7d.2.2.2.1 h7d.2.2.2.2.1 h7d.2.2.2.2.2)
  have hl7_temp_spec : TAddCatShiftSpec rCat rClean13 _ l7t :=
    hl7_temp_on.weaken fun β h0 i ↦ by
      dsimp only
      rw [show (rCarry.slice 0 5 slice05_le6) i = rCarry ⟨0 + i.val, by omega⟩ from rfl,
        Function.update_of_ne (hDCarry.ne 5 _).symm, ← hSubC ⟨0 + i.val, by omega⟩]
      exact h0 _
  have hl7_in_spec : TAddCatShiftSpec rCat rClean13 (shiftJ7T5 rP rDelta hPDelta)
      (layerJ7T5Inner rCat rP rDelta rCarry hPDelta hDCat hDCarry hCatCarry) :=
    TAddCatShiftSpec.seq hCatClean hl7_temp_spec
      (TAddCatShiftSpec.of_diag8 rCat rClean13 _ _
        (layerJTopTSCirc_eval (rP 6) (rP 7) (rP.wires.injective.ne (fin8_ne rfl))))
      (hts_inv_cat5 6 7)
  obtain ⟨hc7, _⟩ := conjTAddProg_spec p7 hz7 5 (rDelta.slice 0 5 slice05_le7)
    (rCat.slice 0 5 slice05_le8) (rCarry.slice 0 5 slice05_le6) (rDelta 5)
    h7d.1 h7d.2.1 h7d.2.2.1 h7d.2.2.2.1 h7d.2.2.2.2.1 h7d.2.2.2.2.2 hd7_B hd7_C
  have hl7_temp_step := CleanStepPair13AbpInv.of_subreg v rTot rClean13 rSubJ7 hSubJ7 l7t
    ⟨Finset.mem_image.mpr ⟨⟨0, by omega⟩, Finset.mem_univ _, rfl⟩,
     hc7 SJ7e (hp7d (· ∉ SJ7e) (fun i h ↦ hNotRk hPCarry i (hSJ7e_sub _ h))
       fun _ h ↦ hNotRk hDCarry _ (hSJ7e_sub _ h)).2
       (fun _ h ↦ hNotRk hDCarry _ (hSJ7e_sub _ h)) (fun i h ↦ hCat_not_S6 i (hSJ7e_sub _ h))
       (fun h ↦ hNotRk hDCarry 5 (hSJ7e_sub _ h)) hC5_in_SJ7e,
     hl7_and, hl7_temp_on.comm_cleanProj SJ7 hDisjSJ7⟩
    (hl7_temp_spec.comm_cleanProj S13 hDisjS13)
  have hl7_br := hBr_loc 6 7 (rP.wires.injective.ne (fin8_ne rfl)) hl7_in_spec hl7_temp_step
  have hpre := hLoc_embed_rP (preJ01Circ_eq_embedMatrix rP)
  have hMid_all (j : Fin 8) (hj2 : 2 ≤ j.val) (hj7 : j.val < 7) :
      TAddCatShiftSpec rCat rClean13 (shiftJT5 rP rDelta hPDelta j hj2 hj7)
        (layerJT5Inner rCat rP rDelta rCarry hPCat hPDelta hDCat hDCarry hCatCarry hPCarry j hj2
            hj7) ∧
      stepLoc (layerJT5Bracket rCat rP rDelta rCarry hPCat hPDelta hDCat hDCarry
        hCatCarry hPCarry j hj2 hj7) := by
    let hb := layerJT5_bounds hj2 hj7
    let hd := layerJT5_disj hPCat hPDelta hDCat hDCarry hCatCarry hPCarry j hj2 hj7
    let pJ := prepJT5 rP rDelta hPDelta j (j.val - 1) hb.2.2.2.1
    let jPrev : Fin 8 := ⟨j.val - 1, hb.2.2.2.2⟩
    have hnePrev : rP jPrev ≠ rP j :=
      rP.wires.injective.ne fun e ↦ by have hv := congrArg Fin.val e; dsimp [jPrev] at hv; omega
    have hpJd (P : Wire M → Prop) (hP : ∀ i, P (rP i))
        (hD : ∀ i : Fin 5, P (rDelta ⟨i.val, by omega⟩)) :=
      prepJT5_zero_and_disj (P := P) rP rDelta hPDelta j (j.val - 1) hb.2.2.2.1 hP hD
    obtain ⟨hzJ, hdJ_B⟩ := hpJd (· ∉ Set.range (rCat.slice (6 - j.val) (j.val - 1) hb.2.1).wires)
      (fun i ⟨_, e⟩ ↦ hPCat.ne i _ e.symm) fun _ ⟨_, e⟩ ↦ hDCat.ne _ _ e.symm
    have hdJ_C := (hpJd (· ∉ Set.range (rCarry.slice 0 (j.val - 1) hb.2.2.1).wires)
      (fun i ⟨_, e⟩ ↦ hPCarry.ne i _ e.symm) fun _ ⟨_, e⟩ ↦ hDCarry.ne _ _ e.symm).2
    have hconj_spec : TAddCatShiftSpec rCat rClean13 _
        (conjTAddProg pJ (j.val - 1) (rDelta.slice 0 (j.val - 1) hb.1)
          (rCat.slice (6 - j.val) (j.val - 1) hb.2.1) (rCarry.slice 0 (j.val - 1) hb.2.2.1)
          (rP j) hd.1 hd.2.1 hd.2.2.1 hd.2.2.2.1 hd.2.2.2.2.1 hd.2.2.2.2.2) :=
      (TAddCatShiftOn.conjTAdd rCat (6 - j.val) (j.val - 1) (by omega) hb.2.1 pJ hzJ
        (rDelta.slice 0 (j.val - 1) hb.1) (rCarry.slice 0 (j.val - 1) hb.2.2.1) (rP j)
        hd.1 hd.2.1 hd.2.2.1 hd.2.2.2.1 hd.2.2.2.2.1 hd.2.2.2.2.2 hdJ_B hdJ_C).weaken
        fun _ h0 i ↦ (hSubC ⟨0 + i.val, by omega⟩) ▸ h0 _
    have hin_spec : TAddCatShiftSpec rCat rClean13 (shiftJT5 rP rDelta hPDelta j hj2 hj7)
        (layerJT5Inner rCat rP rDelta rCarry hPCat hPDelta hDCat hDCarry hCatCarry hPCarry j hj2
            hj7) :=
      TAddCatShiftSpec.seq hCatClean hconj_spec
        (TAddCatShiftSpec.of_diag8 rCat rClean13 _ _ (layerJTopTSCirc_eval (rP jPrev)
            (rP j) hnePrev))
        (hts_inv_cat5 jPrev j)
    obtain ⟨hc_J, _⟩ := conjTAddProg_spec pJ hzJ (j.val - 1) (rDelta.slice 0 (j.val - 1) hb.1)
      (rCat.slice (6 - j.val) (j.val - 1) hb.2.1) (rCarry.slice 0 (j.val - 1) hb.2.2.1) (rP j)
      hd.1 hd.2.1 hd.2.2.1 hd.2.2.2.1 hd.2.2.2.2.1 hd.2.2.2.2.2 hdJ_B hdJ_C
    have hconj_step := CleanStepPair13AbpInv.of_subreg v rTot rClean13 rCarry
      (fun i ↦ ⟨⟨7 + i.val, by omega⟩, (hSubC i).symm⟩) _
      (hc_J S6 (hpJd (· ∉ S6) (hNotRk hPCarry) fun _ ↦ hNotRk hDCarry _).2
        (fun _ ↦ hNotRk hDCarry _) hCat_not_S6 (hNotRk hPCarry j)
        fun _ ↦ Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩)
      (hconj_spec.comm_cleanProj S13 hDisjS13)
    exact ⟨hin_spec, hBr_loc jPrev j hnePrev hin_spec hconj_step⟩
  have hMidRange (rem : ℕ) : ∀ (j : ℕ) (h2 : 2 ≤ j), 7 - j = rem →
      stepLoc (postCancelT5MidRange rCat rP rDelta rCarry hPCat hPDelta hDCat hDCarry
        hCatCarry hPCarry j h2) := by
    induction rem with
    | zero =>
        intro j h2 _
        have hj7 : ¬ j < 7 := by omega
        unfold postCancelT5MidRange
        rw [dite_eq_right hj7]
        refine ⟨.id v rTot rClean13, .id rP rCat, ?_⟩
        change LocalOnQft16 rP rCat ((1 : Unitary (2 ^ M))⁻¹).1
        rw [inv_one]
        exact LocalOnQft16.id rP rCat
    | succ _ ih =>
        intro j h2 _
        have hj7 : j < 7 := by omega
        unfold postCancelT5MidRange
        rw [dite_eq_left hj7]
        exact stepLoc_seq (hMid_all ⟨j, Nat.lt_trans hj7 (Nat.lt_succ_self 7)⟩ h2 hj7).2
          (ih (j + 1) (Nat.le_succ_of_le h2) (by omega))
  exact ⟨fun j hj2 hj7 ↦ (hMid_all j hj2 hj7).1, hl7_in_spec,
    stepLoc_seq hpre (stepLoc_seq (hMidRange 5 2 (Nat.le_refl 2) rfl) hl7_br)⟩
/-! ### 3. Universal `TAddCatShiftSpec` Kickback Lemma `TAddCatShiftSpec.mul_cat_clean13` -/

theorem tAddCatPerm_lt (Δ : ℕ) (y : Fin (2 ^ 8)) : (y.val % 32 + Δ) % 32 + 32 * (y.val / 32) <
    2 ^ 8 := by have := y.isLt; omega
def tAddCatPerm (Δ : ℕ) (y : Fin (2 ^ 8)) : Fin (2 ^ 8) :=
    ⟨(y.val % 32 + Δ) % 32 + 32 * (y.val / 32), tAddCatPerm_lt Δ y⟩
theorem tAddCatPerm_bijective (Δ : ℕ) : Function.Bijective (tAddCatPerm Δ) :=
  (Finite.injective_iff_bijective (f := tAddCatPerm Δ)).mp fun y₁ y₂ h ↦ by
    have hv := congrArg Fin.val h; dsimp only [tAddCatPerm] at hv
    have h1 := y₁.isLt; have h2 := y₂.isLt
    have hΔ := (Nat.div_add_mod Δ 32).symm
    exact Fin.ext (by omega)
theorem tAddShift_phaseGradient8 (y : Fin (2 ^ 8))
    (Δ : ℕ) : phase8Exp (((y.val % 32 + Δ) / 32 : ℕ) : ZMod 8) * PgBase.phaseGradientState 8 y =
    exp256 Δ * PgBase.phaseGradientState 8 (tAddCatPerm Δ y) := by
  let z := tAddCatPerm Δ y; let af : Fin (2 ^ 8) := z - y;
  have hy_eq : z - af = y := sub_sub_cancel z y;
  have hshift := PhotochemistrySolution.phaseGradientState_sub_shift_main 8 af z
  have hexp_af : Complex.exp (2 * Real.pi * Complex.I * ((af.val : ℝ) / (2 ^ 8 : ℝ))) =
      exp256 af.val := by unfold exp256; push_cast; rfl
  rw [hy_eq, hexp_af] at hshift; rw [phase8Exp_natCast_eq_exp256, hshift, ← mul_assoc, ← exp256_add]
  refine congrArg (· * PgBase.phaseGradientState 8 z) (exp256_congr ?_)
  have haf : af.val = (2 ^ 8 - y.val + z.val) % 2 ^ 8 := by dsimp only [af]; rw [Fin.sub_def]
  have hy := y.isLt; have hΔ := (Nat.div_add_mod Δ 256).symm
  rw [haf]; dsimp only [z, tAddCatPerm]; omega
theorem TAddCatShiftSpec.mul_cat_clean13 {M : ℕ} {rCat rP : QRegister 8 M}
    {rClean13 : QRegister 13 M} (hPCat : rP.DisjointWires rCat)
    (hCatClean : rCat.DisjointWires rClean13) {Δ : BitAssignment M → ℕ} {B : (Fin 8 → Bool) → ℕ}
    {prog : AndBracketProg M} (hSpec : TAddCatShiftSpec rCat rClean13 Δ prog)
    (hB : ∀ γ : BitAssignment M, (∀ j : Fin 13, γ (rClean13 j) = 0) → Δ γ = B (pBits rP γ)) :
    prog.toCircuit.eval.1 * (rCat.embedMatrix catState8Mat * rClean13.basisOutcomeProjector 0) =
    rP.embedMatrix (Matrix.diagonal (fun u ↦ exp256 (B (fin8Bits u)))) *
    (rCat.embedMatrix catState8Mat * rClean13.basisOutcomeProjector 0) := by
  refine mul_cat_clean13_eq_of_mulVec_noSym rCat rClean13 hCatClean _ _ fun env hc ↦ ?_
  obtain ⟨ph, f, hep, hout, hval⟩ := hSpec
  let β : Fin (2 ^ 8) → BitAssignment M := fun y ↦ basisBits M (rCat.basisSplitEquiv.symm (y, env))
  let δ0 := B (pBits rP (β 0))
  have hout_cat : ∀ (y : Fin (2 ^ 8)) (w : Wire M), w ∉ Set.range rCat.wires → β y w = β 0 w :=
      fun y w hw ↦
      congrFun ((congrArg Prod.snd (rCat.basisSplitEquiv.apply_symm_apply (y,
      env))).trans (congrArg Prod.snd (rCat.basisSplitEquiv.apply_symm_apply (0, env))).symm)
      ⟨w, hw⟩
  have hp_y : ∀ y : Fin (2 ^ 8), pBits rP (β y) = pBits rP (β 0) := fun y ↦
    funext fun i ↦ congrArg (fun x ↦ decide (x = 1))
      (hout_cat y (rP i) fun ⟨c, hce⟩ ↦ hPCat.ne i c hce.symm)
  have hcat_split : ∀ γ : BitAssignment M,
      PhotochemistrySolution.regVal 8 rCat γ =
        PhotochemistrySolution.regVal 5 (rCat.slice 0 5 slice05_le8) γ +
          32 * PhotochemistrySolution.regVal 3 (rCat.slice 5 3 (by omega)) γ :=
    fun γ ↦ regVal_slice_split_local 5 3 rCat γ
  have hlhs : prog.toCircuit.eval.1.mulVec (rCat.tensorState (PgBase.phaseGradientState 8)
      (Pi.single env 1)) = exp256 δ0 • rCat.tensorState (PgBase.phaseGradientState 8)
      (Pi.single env 1) := by
    rw [PhotochemistrySolution.tensorState_single_eq_sum rCat (PgBase.phaseGradientState 8) env,
        Matrix.mulVec_sum, Finset.smul_sum]; change (∑ y : Fin (2 ^ 8),
        prog.toCircuit.eval.1.mulVec (PgBase.phaseGradientState 8 y • ketState (β y))) = ∑ y :
        Fin (2 ^ 8), exp256 δ0 • (PgBase.phaseGradientState 8 y • ketState (β y))
    have hstep : ∀ y : Fin (2 ^ 8),
        prog.toCircuit.eval.1.mulVec (ketState (β y)) =
          phase8Exp (((y.val % 32 + δ0) / 32 : ℕ) : ZMod 8) •
            ketState (β (tAddCatPerm δ0 y)) := fun y ↦ by
      have hc_y : ∀ i : Fin 13, β y (rClean13 i) = 0 := fun i ↦
          (hout_cat y (rClean13 i) fun ⟨b, hb⟩ ↦ hCatClean.ne b i hb).trans (hc i)
      obtain ⟨hlo_f, hph_f⟩ := hval (β y) hc_y;
      have hΔ_y : Δ (β y) = δ0 := (hB (β y) hc_y).trans (congrArg B (hp_y y))
      have hry : PhotochemistrySolution.regVal 8 rCat (β y) = y.val := by
        rw [PhotochemistrySolution.regVal_basisBits rCat];
        exact congrArg Fin.val (congrArg Prod.fst (rCat.basisSplitEquiv.apply_symm_apply (y, env)))
      have hlo_y : PhotochemistrySolution.regVal 5 (rCat.slice 0 5 slice05_le8) (β y) = y.val % 32 ∧
          PhotochemistrySolution.regVal 3 (rCat.slice 5 3 (by omega)) (β y) = y.val / 32 := by
        have hs := hcat_split (β y);
        have hlt := regVal_lt_two_pow_local 5 (rCat.slice 0 5 slice05_le8) (β y); omega
      have hf_hi : PhotochemistrySolution.regVal 3 (rCat.slice 5 3 (by omega)) (f (β y)) =
          PhotochemistrySolution.regVal 3 (rCat.slice 5 3 (by omega)) (β y) :=
        PhotochemistrySolution.SelectFastRouterEval.regVal_congr _ _ _ fun k ↦
          hout (β y) _ fun j e ↦ by
            have hv := congrArg Fin.val (rCat.wires.injective e)
            dsimp [QRegister.slice] at hv
            omega
      have hval_f : PhotochemistrySolution.regVal 8 rCat (f (β y)) = (tAddCatPerm δ0 y).val := by
        rw [hcat_split (f (β y)), hlo_f, hlo_y.1, hΔ_y, hf_hi, hlo_y.2]; rfl
      have hpres_f : ∀ w ∉ Set.range rCat.wires, f (β y) w = β y w :=
        fun w hw ↦ hout (β y) w fun j e ↦ hw ⟨⟨j.val, by omega⟩, e.symm⟩
      change prog.toCircuit.eval.1.mulVec (KinB.ket (β y)) = _;
      rw [hep (β y), hph_f, hlo_y.1, hΔ_y,
          PhotochemistrySolution.eq_basisBits_basisSplitEquiv_symm rCat y (tAddCatPerm δ0 y) env
          (f (β y)) hpres_f hval_f]
    simp_rw [Matrix.mulVec_smul, hstep, smul_comm (PgBase.phaseGradientState 8 _), ← mul_smul,
        tAddShift_phaseGradient8, mul_smul]
    exact Equiv.sum_comp (Equiv.ofBijective (tAddCatPerm δ0) (tAddCatPerm_bijective δ0)) fun z ↦
        exp256 δ0 • PgBase.phaseGradientState 8 z • ketState (β z)
  have hrhs :
      (rP.embedMatrix (Matrix.diagonal (fun u ↦
      exp256 (B (fin8Bits u))))).mulVec (rCat.tensorState (PgBase.phaseGradientState 8)
      (Pi.single env 1)) = exp256 δ0 • rCat.tensorState (PgBase.phaseGradientState 8)
      (Pi.single env 1) := by
    let d : Fin (2 ^ 8) → ℂ := fun u ↦ exp256 (B (fin8Bits u))
    rw [PhotochemistrySolution.tensorState_single_eq_sum rCat (PgBase.phaseGradientState 8) env,
        Matrix.mulVec_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun y _ ↦ ?_
    change (rP.embedMatrix (Matrix.diagonal d)).mulVec (PgBase.phaseGradientState 8 y • ketState
        (β y)) = exp256 δ0 • (PgBase.phaseGradientState 8 y • ketState (β y))
    have hk_diag : (rP.embedMatrix (Matrix.diagonal d)).mulVec (ketState (β y)) =
        d (readRegIdx rP (β y)) • ketState (β y) := embedMatrix_diagonal_mulVec_ket8 rP d (β y)
    have hd_eq : d (readRegIdx rP (β y)) = exp256 δ0 := by
      dsimp only [d, δ0]; rw [← pBits_eq_fin8Bits_readRegIdx rP (β y), hp_y y]
    rw [Matrix.mulVec_smul, hk_diag, hd_eq, smul_comm]
  rw [hlhs, hrhs]
/-! ### 4. Single-Survivor `8`-Layer Matrix Collapse & `M98 = (dPost8U * qftGridUnitary).1` -/

def xPref (m : ℕ) (x' : Fin (2 ^ 8)) : ℕ :=
    ∑ a ∈ Finset.range m, if ha : a < 8 then (basisBits 8 x' ⟨a, ha⟩).val * 2 ^ (7 - a) else 0
def eClosed (m : ℕ) (x' r : Fin (2 ^ 8)) : ℕ :=
    eZeroBool m (fin8Bits r) + rLoBool m (fin8Bits r) * xPref m x'
def ePost8 (r : Fin (2 ^ 8)) : ℕ := eZeroBool 8 (fin8Bits r)
theorem dvd_256_two_pow_mul_xPref (j : Fin 8) (x' : Fin (2 ^ 8)) : 256 ∣ 2 ^ j.val *
    xPref j.val x' := by
  rw [xPref, Finset.mul_sum]
  refine Finset.dvd_sum fun a ha ↦ ?_
  have ha8 : a < 8 := Nat.lt_trans (Finset.mem_range.mp ha) j.isLt
  simp only [ha8, ↓reduceDIte]
  refine ⟨(basisBits 8 x' ⟨a, ha8⟩).val * 2 ^ (j.val - 1 - a), ?_⟩
  rw [mul_left_comm (2 ^ j.val), (show ∀ b : Fin 8, ∀ c < b.val,
    2 ^ b.val * 2 ^ (7 - c) = 256 * 2 ^ (b.val - 1 - c) by decide) j a (Finset.mem_range.mp ha)]
  ring
theorem eClosed_step_mod256 (j : Fin 8) (x' r : Fin (2 ^ 8)) :
    let yj := (basisBitsEquiv 8).symm (Function.update (basisBits 8 r) j (basisBits 8 x' j))
    (eClosed j.val x' yj + deltaLayerBool j (fin8Bits yj) +
        128 * (basisBits 8 r j).val * (basisBits 8 x' j).val) % 256 =
      eClosed (j.val + 1) x' r % 256 := by
  intro yj
  have hyj_bits : basisBits 8 yj = Function.update (basisBits 8 r) j (basisBits 8 x' j) :=
    (basisBitsEquiv 8).apply_symm_apply _
  have hfin_yj : fin8Bits yj = updP (fin8Bits r) j (fin8Bits x' j) := funext fun i ↦ by
    by_cases hij : i = j <;> simp [hij, fin8Bits, updP, hyj_bits]
  have hstep := eZeroBool_step j (fin8Bits yj)
  obtain ⟨heZ, hrLo_u, hrLo_s⟩ := eZeroBool_upd_and_rLo j (fin8Bits x' j) (fin8Bits r)
  obtain ⟨q, hq⟩ := dvd_256_two_pow_mul_xPref j x'
  unfold eClosed
  rw [← hfin_yj] at heZ hrLo_u
  rw [cond_fin8Bits, hyj_bits, Function.update_self, heZ, hrLo_u] at hstep
  rw [hrLo_u, show xPref (j.val + 1) x' =
        xPref j.val x' + (basisBits 8 x' j).val * 2 ^ (7 - j.val) by
      simp only [xPref, Finset.sum_range_succ, j.isLt, ↓reduceDIte],
    hrLo_s, cond_fin8Bits, show eZeroBool (j.val + 1) (fin8Bits r) +
        (rLoBool j.val (fin8Bits r) + (basisBits 8 r j).val * 2 ^ j.val) *
          (xPref j.val x' + (basisBits 8 x' j).val * 2 ^ (7 - j.val)) =
      ((eZeroBool (j.val + 1) (fin8Bits r) +
          rLoBool j.val (fin8Bits r) * (basisBits 8 x' j).val * 2 ^ (7 - j.val)) +
        (rLoBool j.val (fin8Bits r) * xPref j.val x' +
          (2 ^ j.val * 2 ^ (7 - j.val)) * (basisBits 8 r j).val * (basisBits 8 x' j).val)) +
      (basisBits 8 r j).val * (2 ^ j.val * xPref j.val x') by ring,
    hq, (show ∀ b : Fin 8, 2 ^ b.val * 2 ^ (7 - b.val) = 128 by decide) j,
    ← mul_assoc (basisBits 8 r j).val 256 q,
    mul_comm (basisBits 8 r j).val 256, mul_assoc 256, Nat.add_mul_mod_self_left]
  omega
theorem regValBool_eq_sum_pow :
    ∀ (w : ℕ) (b : Fin w → Bool),
      regValBool w b = ∑ i : Fin w, cond (b i) 1 0 * 2 ^ i.val
  | 0, _ => rfl
  | w + 1, b => by
      dsimp only [regValBool]
      rw [regValBool_eq_sum_pow w (fun i ↦ b i.succ), Fin.sum_univ_succ, Fin.val_zero, pow_zero,
          mul_one, Finset.mul_sum]
      refine congrArg (cond (b 0) 1 0 + ·) (Finset.sum_congr rfl fun i _ ↦ ?_)
      rw [Fin.val_succ, pow_succ']; ring
theorem eClosed_eight_bitRev (x r : Fin (2 ^ 8)) : eClosed 8 (bitRevEquiv 8 x) r = ePost8 r +
    r.val * x.val := by
  unfold eClosed ePost8 rLoBool
  have hr : regValBool 8 (fun k ↦ fin8Bits r (Fin.ofNat 8 k.val)) = r.val := by
    rw [regValBool_eq_sum_pow 8, ← SelectLcu70Rot32.sum_basisBits_mul_two_pow_32_rot32only 8 r]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    have hk : Fin.ofNat 8 k.val = k := Fin.ext (Nat.mod_eq_of_lt k.isLt); rw [hk, cond_fin8Bits r k]
  have hx : xPref 8 (bitRevEquiv 8 x) = x.val := by
    rw [xPref, ← Fin.sum_univ_eq_sum_range _ 8]
    refine (Finset.sum_congr rfl fun a _ ↦ ?_).trans ((Fintype.sum_equiv Fin.revPerm _
        (fun t : Fin 8 ↦ (basisBits 8 x t).val * 2 ^ t.val) fun _ ↦ rfl).trans ?_)
    · simp only [a.isLt, ↓reduceDIte, Fin.eta, basisBits_bitRevEquiv_coe]
      exact congrArg ((basisBits 8 x a.rev).val * 2 ^ ·)
        ((show ∀ b : Fin 8, 7 - b.val = b.rev.val by decide) a)
    · exact SelectLcu70Rot32.sum_basisBits_mul_two_pow_32_rot32only
        8 x
  rw [hr, hx]
/-- State invariant after `m` layers (`0 ≤ m ≤ 8`) starting from `basisState x'`. -/
def LayerVecInv (m : ℕ) (x' : Fin (2 ^ 8)) (v : Fin (2 ^ 8) → ℂ) : Prop :=
    ∀ r : Fin (2 ^ 8), if ∀ k : Fin 8, m ≤ k.val → basisBits 8 r k = basisBits 8 x' k then v r =
    (1 / Real.sqrt 2 : ℂ) ^ m * exp256 (eClosed m x' r) else v r = 0
theorem layerVecInv_zero (x' : Fin (2 ^ 8)) :
    LayerVecInv 0 x' (basisState x') := fun r ↦ by
  by_cases hall : ∀ k : Fin 8, 0 ≤ k.val → basisBits 8 r k = basisBits 8 x' k
  · rw [ite_eq_left hall]
    have hrx : r = x' := (basisBitsEquiv 8).injective (funext fun k ↦ hall k (Nat.zero_le _))
    subst hrx;
    have he0 : eClosed 0 r r = 0 :=
        rfl; rw [he0, pow_zero, exp256_zero, mul_one, basisState, Pi.single_eq_same]
  · rw [ite_eq_right hall]
    have hne : r ≠ x' := fun e ↦ hall (e ▸ fun _ _ ↦ rfl)
    rw [basisState, Pi.single_eq_of_ne hne]
theorem hadamardPhase_eq_exp256 (a b : ZMod 2) : (1 / Real.sqrt 2 : ℂ) * hadamardPhase (a * b) =
    (1 / Real.sqrt 2 : ℂ) * exp256 (128 * a.val * b.val) := by
  rw [KineticStep.hadamardPhase_eq_plusPhase]; unfold KineticStep.plusPhase exp256
  congr 1; congr 1; push_cast; ring
theorem hadamardAt8_mul_diag_step (j : Fin 8) (x' : Fin (2 ^ 8)) (v : Fin (2 ^ 8) → ℂ)
    (hv : LayerVecInv j.val x' v) : LayerVecInv (j.val +
    1) x' ((hadamardAt 8 j).1.mulVec ((Matrix.diagonal (fun u ↦
    exp256 (deltaLayerBool j (fin8Bits u)))).mulVec v)) := by
  rw [show (Matrix.diagonal fun u ↦ exp256 (deltaLayerBool j (fin8Bits u))).mulVec v =
      fun y ↦ exp256 (deltaLayerBool j (fin8Bits y)) * v y from
    funext fun _ ↦ Matrix.mulVec_diagonal _ _ _]
  intro r
  simp only [Matrix.mulVec, dotProduct, hadamardAt_apply_phase]
  have hterm0 (y : Fin (2 ^ 8)) (hny : (∀ m ≠ j, basisBits 8 r m = basisBits 8 y m) →
      ¬ ∀ k : Fin 8, j.val ≤ k.val → basisBits 8 y k = basisBits 8 x' k) :
      (if ∀ m ≠ j, basisBits 8 r m = basisBits 8 y m then
        (1 / Real.sqrt 2 : ℂ) * hadamardPhase (basisBits 8 r j * basisBits 8 y j) else 0) *
        (exp256 (deltaLayerBool j (fin8Bits y)) * v y) = 0 := by
    by_cases hall : ∀ m ≠ j, basisBits 8 r m = basisBits 8 y m
    · have hvy := hv y
      rw [ite_eq_right (hny hall)] at hvy
      simp [hvy]
    · simp [ite_eq_right hall]
  by_cases hhi : ∀ k : Fin 8, j.val + 1 ≤ k.val → basisBits 8 r k = basisBits 8 x' k
  · rw [ite_eq_left hhi]
    let yj := (basisBitsEquiv 8).symm (Function.update (basisBits 8 r) j (basisBits 8 x' j))
    have hyj : basisBits 8 yj = Function.update (basisBits 8 r) j (basisBits 8 x' j) :=
      (basisBitsEquiv 8).apply_symm_apply _
    rw [Fintype.sum_eq_single yj fun y hy ↦ hterm0 y fun hall hky ↦ hy <|
      (basisBitsEquiv 8).injective <| funext fun m ↦ by
        by_cases hmj : m = j
        · simp [hmj, hyj, hky _ (Nat.le_refl _)]
        · simp [hyj, hmj, (hall m hmj).symm]]
    have hinv_yj (k : Fin 8) (hk : j.val ≤ k.val) : basisBits 8 yj k = basisBits 8 x' k := by
      rcases eq_or_ne k j with rfl | hkj
      · simp [hyj]
      · simp [hyj, hkj, hhi k (by have : k.val ≠ j.val := fun e ↦ hkj (Fin.ext e); omega)]
    have hvyj := hv yj
    rw [ite_eq_left hinv_yj] at hvyj
    rw [ite_eq_left (fun m hm ↦ by simp [hyj, hm] : ∀ m ≠ j, _),
      show basisBits 8 yj j = basisBits 8 x' j by simp [hyj], hadamardPhase_eq_exp256, hvyj]
    have hexp : exp256 (128 * (basisBits 8 r j).val * (basisBits 8 x' j).val) *
        (exp256 (deltaLayerBool j (fin8Bits yj)) * exp256 (eClosed j.val x' yj)) =
        exp256 (eClosed (j.val + 1) x' r) := by
      rw [← exp256_add, ← exp256_add]
      refine exp256_congr ?_
      rw [show 128 * (basisBits 8 r j).val * (basisBits 8 x' j).val +
          (deltaLayerBool j (fin8Bits yj) + eClosed j.val x' yj) =
          eClosed j.val x' yj + deltaLayerBool j (fin8Bits yj) +
          128 * (basisBits 8 r j).val * (basisBits 8 x' j).val by ring]
      exact eClosed_step_mod256 j x' r
    rw [pow_succ (1 / Real.sqrt 2 : ℂ) j.val, ← hexp]
    ring
  · rw [ite_eq_right hhi]
    exact Finset.sum_eq_zero fun y _ ↦ hterm0 y fun hall hky ↦ hhi fun k hk1 ↦
      (hall k fun e ↦ by subst e; omega).trans (hky k (by omega))
/-- Layer unitary `(hadamardAt 8 j).1 * diag(exp256 (δ_j))` on `2 ^ 8`. -/
noncomputable def postCancelLayerMat (j : Fin 8) : Operator (2 ^ 8) :=
  (hadamardAt 8 j).1 * Matrix.diagonal (fun u ↦ exp256 (deltaLayerBool j (fin8Bits u)))
/-- Product of middle layers `2 .. 6` on `2 ^ 8`. -/
noncomputable def postCancelMidMat : Operator (2 ^ 8) :=
  postCancelLayerMat 6 *
    (postCancelLayerMat 5 *
      (postCancelLayerMat 4 *
        (postCancelLayerMat 3 * postCancelLayerMat 2)))
/-- Post-cancellation diagonal unitary `dPost8U = diag(exp(2πi ePost8(r) / 256))`. -/
noncomputable def dPost8U : Unitary (2 ^ 8) :=
  ⟨Matrix.diagonal (fun r ↦ exp256 (ePost8 r)), by
    rw [Unitary.mem_iff, Matrix.star_eq_conjTranspose]
    have h1 : (Matrix.diagonal (fun r : Fin (2 ^ 8) ↦ exp256 (ePost8 r)))ᴴ *
        Matrix.diagonal (fun r : Fin (2 ^ 8) ↦ exp256 (ePost8 r)) = 1 := by
      rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]; ext i j
      by_cases hij : i = j
      · subst hij; simp only [Matrix.diagonal_apply_eq, Pi.star_apply, Matrix.one_apply_eq]
        exact star_exp256_mul_self (ePost8 i)
      · simp [Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij]
    exact ⟨h1, mul_eq_one_comm.mp h1⟩⟩
theorem postCancelAll8Mat_eq_dPost8U_mul_qftGrid : (postCancelLayerMat 7 * (postCancelMidMat *
    (postCancelLayerMat 1 * (postCancelLayerMat 0 * (QFT.swapAllUnitary 8).1)))) =
    (dPost8U * qftGridUnitary).1 := by
  let M98 : Operator (2 ^ 8) :=
      postCancelLayerMat 7 * (postCancelMidMat * (postCancelLayerMat 1 * (postCancelLayerMat 0 *
      (QFT.swapAllUnitary 8).1))); change M98 = (dPost8U * qftGridUnitary).1; ext r x
  have hcol : ∀ A : Matrix (Fin (2 ^ 8)) (Fin (2 ^ 8)) ℂ, A r x = (A.mulVec (basisState x)) r :=
    fun A ↦ by rw [basisState, Matrix.mulVec_single_one, Matrix.col_apply]
  rw [hcol M98, hcol (dPost8U * qftGridUnitary).1]; let x' := bitRevEquiv 8 x;
  have hsw : (QFT.swapAllUnitary 8).1.mulVec (basisState x) = basisState x' :=
      KineticStep.swapAllUnitary_mulVec_basisState 8 x
  have hstep : ∀ (j : Fin 8) {v : Fin (2 ^ 8) → ℂ},
      LayerVecInv j.val x' v → LayerVecInv (j.val + 1) x' ((postCancelLayerMat j).mulVec v) :=
    fun j {v} hv ↦ by
      unfold postCancelLayerMat; rw [← Matrix.mulVec_mulVec];
      exact hadamardAt8_mul_diag_step j x' v hv
  have hv0 := layerVecInv_zero x'; have hv1 := hstep 0 hv0; have hv2 := hstep 1 hv1;
  have hv3 := hstep 2 hv2; have hv4 := hstep 3 hv3; have hv5 := hstep 4 hv4;
  have hv6 := hstep 5 hv5; have hv7 := hstep 6 hv6; have hv8 := hstep 7 hv7
  have hm98_vec : M98.mulVec (basisState x) =
      (postCancelLayerMat 7).mulVec ((postCancelLayerMat 6).mulVec ((postCancelLayerMat 5).mulVec
      ((postCancelLayerMat 4).mulVec ((postCancelLayerMat 3).mulVec ((postCancelLayerMat 2).mulVec
      ((postCancelLayerMat 1).mulVec ((postCancelLayerMat 0).mulVec (basisState x'))))))))
      := by dsimp only [M98, postCancelMidMat]; simp only [← Matrix.mulVec_mulVec, hsw]
  have hr8 : ∀ k : Fin 8, 8 ≤ k.val → basisBits 8 r k = basisBits 8 x' k := fun k hk ↦
      absurd k.isLt (Nat.not_lt_of_ge hk)
  have hlhs_r := hv8 r;
  have h78 : (7 : Fin 8).val + 1 = 8 :=
      rfl; rw [h78] at hlhs_r; rw [ite_eq_left hr8] at hlhs_r; rw [hm98_vec, hlhs_r,
      eClosed_eight_bitRev x r, exp256_add]
  have hrhs_r : ((dPost8U * qftGridUnitary).1.mulVec (basisState x)) r = exp256 (ePost8 r) *
      QFT.qftMatrix 8 r x := by
    rw [← hcol (dPost8U * qftGridUnitary).1]
    change (Matrix.diagonal (fun u ↦ exp256 (ePost8 u)) * QFT.qftMatrix 8) r x = _
    rw [Matrix.diagonal_mul]
  rw [hrhs_r]; unfold QFT.qftMatrix
  have hsqrt : (1 / Real.sqrt 2 : ℂ) ^ 8 = (1 / (Real.sqrt (2 ^ 8 : ℝ) : ℂ)) := by
    have h : (1 / Real.sqrt 2 : ℝ) ^ 8 = 1 / Real.sqrt ((2 : ℝ) ^ 8) := by
      rw [_root_.one_div_pow, KineticStep.sqrt_two_pow]
    exact mod_cast h
  have hexp_rx : exp256 (r.val * x.val) = Complex.exp (2 * ↑Real.pi * Complex.I *
      ((((x.val : ℝ) * (r.val : ℝ) : ℝ) : ℂ) / ((2 ^ 8 : ℝ) : ℂ))) := by
    unfold exp256
    congr 1; push_cast; ring
  rw [hsqrt, hexp_rx]; ring
/-! ### 5. `spliceUnitary`, `qft8PostCancel98CatU`, `CleanWorkStep`s, and `dPost8U` Cancellation -/

theorem polyPostCancelT5Qft8Bracket98_comm_proj13 {M : ℕ}
    (rCat rP : QRegister 8 M) (rDelta : QRegister 7 M) (rCarry : QRegister 6 M)
    (rClean13 : QRegister 13 M)
    (hPCat : rP.DisjointWires rCat) (hPDelta : rP.DisjointWires rDelta)
    (hDCat : rDelta.DisjointWires rCat) (hDCarry : rDelta.DisjointWires rCarry)
    (hCatCarry : rCat.DisjointWires rCarry) (hPCarry : rP.DisjointWires rCarry)
    (hSubD : ∀ i : Fin 7, rClean13 ⟨i.val, by omega⟩ = rDelta i)
    (hSubC : ∀ i : Fin 6, rClean13 ⟨7 + i.val, by omega⟩ = rCarry i) :
    (polyPostCancelT5Qft8Bracket98 rCat rP rDelta rCarry hPCat hPDelta hDCat hDCarry
      hCatCarry hPCarry).toCircuit.eval.1 * rClean13.basisOutcomeProjector 0 =
    rClean13.basisOutcomeProjector 0 *
      (polyPostCancelT5Qft8Bracket98 rCat rP rDelta rCarry hPCat hPDelta hDCat hDCarry
        hCatCarry hPCarry).toCircuit.eval.1 := by
  have : NeZero (2 ^ M) :=
      ⟨pow_ne_zero M two_ne_zero⟩; rw [← cleanProj_range_eq_basisOutcomeProjector_zero rClean13];
      exact (postCancelBlocks_catShift_and_step Unit.unit ⟨Function.Embedding.refl (Fin M)⟩ rCat rP
      rDelta rCarry rClean13 hPCat hPDelta hDCat hDCarry hCatCarry hPCarry hSubD hSubC).2.2.1.1
theorem embedUnitary_dPost8_qftGrid_comm_proj13 {M : ℕ}
    (rP : QRegister 8 M) (rDelta : QRegister 7 M) (rCarry : QRegister 6 M)
    (rClean13 : QRegister 13 M)
    (hPDelta : rP.DisjointWires rDelta) (hPCarry : rP.DisjointWires rCarry)
    (hSubD : ∀ i : Fin 7, rClean13 ⟨i.val, by omega⟩ = rDelta i)
    (hSubC : ∀ i : Fin 6, rClean13 ⟨7 + i.val, by omega⟩ = rCarry i) :
    (rP.embedUnitary (dPost8U * qftGridUnitary)).1 * rClean13.basisOutcomeProjector 0 =
      rClean13.basisOutcomeProjector 0 * (rP.embedUnitary (dPost8U * qftGridUnitary)).1 :=
  rP.embedMatrix_comm_of_disjoint rClean13
    (disjoint_rP_clean13 rP rDelta rCarry rClean13 hPDelta hPCarry hSubD hSubC) _ _
noncomputable def polyPostCancelCleanUnitary {M : ℕ}
    (rCat rP : QRegister 8 M) (rDelta : QRegister 7 M) (rCarry : QRegister 6 M)
    (rClean13 : QRegister 13 M)
    (hPCat : rP.DisjointWires rCat) (hPDelta : rP.DisjointWires rDelta)
    (hDCat : rDelta.DisjointWires rCat) (hDCarry : rDelta.DisjointWires rCarry)
    (hCatCarry : rCat.DisjointWires rCarry) (hPCarry : rP.DisjointWires rCarry)
    (hSubD : ∀ i : Fin 7, rClean13 ⟨i.val, by omega⟩ = rDelta i)
    (hSubC : ∀ i : Fin 6, rClean13 ⟨7 + i.val, by omega⟩ = rCarry i) :
    Unitary (2 ^ M) :=
  spliceUnitary
    (polyPostCancelT5Qft8Bracket98 rCat rP rDelta rCarry hPCat hPDelta hDCat hDCarry
      hCatCarry hPCarry).toCircuit.eval
    (rP.embedUnitary (dPost8U * qftGridUnitary))
    (rClean13.basisOutcomeProjector 0)
    (rClean13.basisOutcomeProjector_conjTranspose 0)
    (basisOutcomeProjector_zero_idem rClean13)
    (polyPostCancelT5Qft8Bracket98_comm_proj13 rCat rP rDelta rCarry rClean13
      hPCat hPDelta hDCat hDCarry hCatCarry hPCarry hSubD hSubC)
    (embedUnitary_dPost8_qftGrid_comm_proj13 rP rDelta rCarry rClean13
      hPDelta hPCarry hSubD hSubC)
theorem polyPostCancelCleanUnitary_props {M : ℕ}
    (rCat rP : QRegister 8 M) (rDelta : QRegister 7 M) (rCarry : QRegister 6 M)
    (rClean13 : QRegister 13 M)
    (hPCat : rP.DisjointWires rCat) (hPDelta : rP.DisjointWires rDelta)
    (hDCat : rDelta.DisjointWires rCat) (hDCarry : rDelta.DisjointWires rCarry)
    (hCatCarry : rCat.DisjointWires rCarry) (hPCarry : rP.DisjointWires rCarry)
    (hSubD : ∀ i : Fin 7, rClean13 ⟨i.val, by omega⟩ = rDelta i)
    (hSubC : ∀ i : Fin 6, rClean13 ⟨7 + i.val, by omega⟩ = rCarry i) :
    let Q :=
        polyPostCancelCleanUnitary rCat rP rDelta rCarry rClean13 hPCat hPDelta hDCat hDCarry
        hCatCarry hPCarry hSubD hSubC; let Q98 :=
                                         (polyPostCancelT5Qft8Bracket98 rCat rP rDelta rCarry hPCat
                                         hPDelta hDCat hDCarry hCatCarry hPCarry).toCircuit.eval;
                                         let W :=
                                         rP.embedUnitary (dPost8U *
                                         qftGridUnitary); let P13 :=
                                                            rClean13.basisOutcomeProjector 0;
                                                            let Pcat :=
                                                            rCat.embedMatrix catState8Mat
    (Q.1 * P13 = Q98.1 * P13) ∧
    (Q.1 * Pcat = Pcat * W.1 ∧ (Q⁻¹).1 * Pcat = (W⁻¹).1 * Pcat) ∧
    (LocalOnQft16 rP rCat Q.1 ∧ LocalOnQft16 rP rCat (Q⁻¹).1) := by
  intro Q Q98 W P13 Pcat
  have : NeZero (2 ^ M) := ⟨pow_ne_zero M two_ne_zero⟩
  have hCatClean := disjoint_rCat_clean13 rCat rDelta rCarry rClean13 hDCat hCatCarry hSubD hSubC
  have hPClean := disjoint_rP_clean13 rP rDelta rCarry rClean13 hPDelta hPCarry hSubD hSubC
  obtain ⟨hmid_spec, hl7_spec, _, hg_f, hg_i⟩ :=
    postCancelBlocks_catShift_and_step Unit.unit ⟨Function.Embedding.refl (Fin M)⟩
      rCat rP rDelta rCarry rClean13 hPCat hPDelta hDCat hDCarry hCatCarry hPCarry hSubD hSubC
  let Pi := Pcat * P13
  have hD0 {γ : BitAssignment M} (h0 : ∀ j : Fin 13, γ (rClean13 j) = 0) (j : Fin 7) :
      γ (rDelta j) = 0 := (hSubD j).symm ▸ h0 _
  have hcomm_rP (A : Operator (2 ^ 8)) : rP.embedMatrix A * Pi = Pi * rP.embedMatrix A := by
    have hc13 : rP.embedMatrix A * P13 = P13 * rP.embedMatrix A :=
      rP.embedMatrix_comm_of_disjoint rClean13 hPClean A _
    dsimp only [Pi, Pcat]
    rw [← Matrix.mul_assoc, rP.embedMatrix_comm_of_disjoint rCat hPCat A _,
      Matrix.mul_assoc, hc13, ← Matrix.mul_assoc]
  have hseq_pi {U V : Operator (2 ^ M)} {MU MV : Operator (2 ^ 8)}
      (hU : U * Pi = rP.embedMatrix MU * Pi) (hV : V * Pi = rP.embedMatrix MV * Pi) :
      (V * U) * Pi = rP.embedMatrix (MV * MU) * Pi := by
    rw [Matrix.mul_assoc, hU, hcomm_rP MU, ← Matrix.mul_assoc, hV, Matrix.mul_assoc,
      ← hcomm_rP MU, ← Matrix.mul_assoc, ← rP.embedMatrix_mul]
  -- Prefix (layers 0 & 1)
  have hpre_pi : (polySwapAll8Circ rP ;;ᶜ Circuit.H (rP 0) ;;ᶜ layerJ1DirectCirc rP ;;ᶜ
      Circuit.H (rP 1)).eval.1 * Pi =
      rP.embedMatrix (postCancelLayerMat 1 *
        (postCancelLayerMat 0 * (QFT.swapAllUnitary 8).1)) * Pi := by
    have hd0 : (Matrix.diagonal fun u ↦ exp256 (deltaLayerBool 0 (fin8Bits u))) = 1 := by
      ext i j
      by_cases hij : i = j <;> simp [hij, deltaLayerBool, exp256_zero, Matrix.one_apply]
    rw [preJ01Circ_eq_embedMatrix rP]
    unfold postCancelLayerMat
    rw [hd0, mul_one]
    simp only [Matrix.mul_assoc]
  -- Layer j bracket on Pi (2 ≤ j < 7)
  have hlay_pi {c : AndBracketProg M} {Δ : BitAssignment M → ℕ} (a j : Fin 8) (hne : rP a ≠ rP j)
      (hspec : TAddCatShiftSpec rCat rClean13 Δ (.seq c (.prim (layerJTopTSCirc (rP a)
          (rP j) hne))))
      (hB : ∀ γ : BitAssignment M,
        (∀ k : Fin 13, γ (rClean13 k) = 0) → Δ γ = deltaLayerBool j (pBits rP γ)) :
      (AndBracketProg.seq c
        (.seq (.prim (layerJTopTSCirc (rP a) (rP j) hne)) (.prim (.H (rP j))))).toCircuit.eval.1 *
        Pi = rP.embedMatrix (postCancelLayerMat j) * Pi := by
    have hev : (AndBracketProg.seq c
        (.seq (.prim (layerJTopTSCirc (rP a) (rP j) hne)) (.prim (.H (rP j))))).toCircuit.eval.1 =
        rP.embedMatrix (hadamardAt 8 j).1 *
          (AndBracketProg.seq c (.prim (layerJTopTSCirc (rP a) (rP j) hne))).toCircuit.eval.1 := by
      simp only [AndBracketProg.toCircuit, Circuit.eval_seq, Submonoid.coe_mul,
        eval_H_eq_embedMatrix8_noSym rP j, Matrix.mul_assoc]
    rw [hev, Matrix.mul_assoc, TAddCatShiftSpec.mul_cat_clean13 hPCat hCatClean hspec hB,
      ← Matrix.mul_assoc, ← rP.embedMatrix_mul]
    rfl
  have hlay_mid (j : Fin 8) (hj2 : 2 ≤ j.val) (hj7 : j.val < 7) :
      (layerJT5Bracket rCat rP rDelta rCarry hPCat hPDelta hDCat hDCarry hCatCarry hPCarry
        j hj2 hj7).toCircuit.eval.1 * Pi = rP.embedMatrix (postCancelLayerMat j) * Pi :=
    hlay_pi ⟨j.val - 1, (layerJT5_bounds hj2 hj7).2.2.2.2⟩ j _ (hmid_spec j hj2 hj7)
      fun γ h0 ↦ prepJT5_shift_eq_bool rP rDelta hPDelta j hj2 hj7 γ (hD0 h0)
  -- Direct 5-step unroll of postCancelT5MidRange 2 (layers 2, 3, 4, 5, 6)
  have hmid_step_unfold (j : ℕ) (h2 : 2 ≤ j) (hj7 : j < 7) :
      (postCancelT5MidRange rCat rP rDelta rCarry hPCat hPDelta hDCat hDCarry hCatCarry hPCarry
        j h2).toCircuit.eval.1 =
      (postCancelT5MidRange rCat rP rDelta rCarry hPCat hPDelta hDCat hDCarry hCatCarry hPCarry
        (j + 1) (Nat.le_succ_of_le h2)).toCircuit.eval.1 *
        (layerJT5Bracket rCat rP rDelta rCarry hPCat hPDelta hDCat hDCarry hCatCarry hPCarry
          ⟨j, Nat.lt_trans hj7 (Nat.lt_succ_self 7)⟩ h2 hj7).toCircuit.eval.1 := by
    conv_lhs => unfold postCancelT5MidRange
    rw [dite_eq_left hj7]
    rfl
  have hmid_pi : (postCancelT5MidRange rCat rP rDelta rCarry hPCat hPDelta hDCat hDCarry
      hCatCarry hPCarry 2 (Nat.le_refl 2)).toCircuit.eval.1 * Pi =
      rP.embedMatrix postCancelMidMat * Pi := by
    have h7 : (postCancelT5MidRange rCat rP rDelta rCarry hPCat hPDelta hDCat hDCarry
        hCatCarry hPCarry 7 (by omega)).toCircuit.eval.1 = 1 := by
      unfold postCancelT5MidRange
      rw [dite_eq_right (Nat.lt_irrefl 7)]
      rfl
    rw [hmid_step_unfold 2 _ (by decide), hmid_step_unfold 3 _ (by decide),
      hmid_step_unfold 4 _ (by decide), hmid_step_unfold 5 _ (by decide),
      hmid_step_unfold 6 _ (by decide), h7, one_mul]
    have p26 := hseq_pi (hseq_pi (hseq_pi (hseq_pi (hlay_mid 2 (by decide) (by decide))
        (hlay_mid 3 (by decide) (by decide))) (hlay_mid 4 (by decide) (by decide)))
        (hlay_mid 5 (by decide) (by decide))) (hlay_mid 6 (by decide) (by decide))
    simp only [Matrix.mul_assoc] at p26 ⊢
    exact p26
  -- Layer j = 7 bracket on Pi
  have hl7_pi : (layerJ7T5Bracket rCat rP rDelta rCarry hPDelta hDCat hDCarry
      hCatCarry).toCircuit.eval.1 * Pi = rP.embedMatrix (postCancelLayerMat 7) * Pi :=
    hlay_pi 6 7 _ hl7_spec fun γ h0 ↦ prepJ7T5_shift_eq_bool rP rDelta hPDelta γ (hD0 h0)
  -- Combine all 8 layers
  have hmul_cat : Q98.1 * Pi = W.1 * Pi := by
    have hev_all : Q98.1 =
        (layerJ7T5Bracket rCat rP rDelta rCarry hPDelta hDCat hDCarry hCatCarry).toCircuit.eval.1 *
          ((postCancelT5MidRange rCat rP rDelta rCarry hPCat hPDelta hDCat hDCarry hCatCarry
            hPCarry 2 (Nat.le_refl 2)).toCircuit.eval.1 *
          (polySwapAll8Circ rP ;;ᶜ Circuit.H (rP 0) ;;ᶜ layerJ1DirectCirc rP ;;ᶜ
            Circuit.H (rP 1)).eval.1) := by
      simp only [Q98, polyPostCancelT5Qft8Bracket98, AndBracketProg.toCircuit, Circuit.eval_seq,
        Submonoid.coe_mul, Matrix.mul_assoc]
    rw [hev_all, hseq_pi (hseq_pi hpre_pi hmid_pi) hl7_pi,
      postCancelAll8Mat_eq_dPost8U_mul_qftGrid]
    rfl
  have hcat_fwd : Q.1 * Pcat = Pcat * W.1 :=
    (spliceUnitary_mul_comm_proj Q98 W P13 Pcat _ _ _ _
      (rClean13.embedMatrix_comm_of_disjoint rCat hCatClean.symm _ _)
      (by rw [Matrix.mul_assoc, Matrix.mul_assoc]; exact hmul_cat)).trans
      (rP.embedMatrix_comm_of_disjoint rCat hPCat _ _)
  have hcat_inv : (Q⁻¹).1 * Pcat = (W⁻¹).1 * Pcat := by
    calc (Q⁻¹).1 * Pcat = (Q⁻¹).1 * ((Pcat * W.1) * (W⁻¹).1) := by
          rw [Matrix.mul_assoc Pcat, show W.1 * (W⁻¹).1 = 1 from
            congrArg Subtype.val (mul_inv_cancel W), mul_one]
      _ = ((Q⁻¹).1 * Q.1) * (Pcat * (W⁻¹).1) := by simp only [← hcat_fwd, Matrix.mul_assoc]
      _ = (W⁻¹).1 * Pcat := by
          rw [show (Q⁻¹).1 * Q.1 = 1 from congrArg Subtype.val (inv_mul_cancel Q), one_mul,
            ← unitary_inv_comm W Pcat (rP.embedMatrix_comm_of_disjoint rCat hPCat _ _)]
  have hQ_inv_eq : (Q⁻¹).1 = (Q98⁻¹).1 * P13 + (W⁻¹).1 * (1 - P13) := by
    have hP_herm : P13ᴴ = P13 := rClean13.basisOutcomeProjector_conjTranspose 0
    change (Q98.1 * P13 + W.1 * (1 - P13))ᴴ = _
    rw [Matrix.conjTranspose_add, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      hP_herm, conjTranspose_sub, conjTranspose_one, hP_herm]
    change P13 * (Q98⁻¹).1 + (1 - P13) * (W⁻¹).1 = _
    rw [← unitary_inv_comm Q98 P13 (polyPostCancelT5Qft8Bracket98_comm_proj13 rCat rP rDelta rCarry
        rClean13 hPCat hPDelta hDCat hDCarry hCatCarry hPCarry hSubD hSubC),
      ← unitary_inv_comm W (1 - P13) (by
        rw [mul_sub, mul_one, sub_mul, one_mul, embedUnitary_dPost8_qftGrid_comm_proj13 rP rDelta
          rCarry rClean13 hPDelta hPCarry hSubD hSubC])]
  have hw_i : LocalOnQft16 rP rCat (W⁻¹).1 := by
    change LocalOnQft16 rP rCat W.1ᴴ
    exact (QRegister.embedUnitary_val rP _ ▸ rP.embedMatrix_conjTranspose _) ▸
      LocalOnQft16.of_embed_rP rP rCat _
  exact ⟨spliceUnitary_mul_proj Q98 W P13 _ _ _ _, ⟨hcat_fwd, hcat_inv⟩,
    ⟨localOnQft16_add_proj_noSym rP rCat rClean13 hg_f (LocalOnQft16.of_embed_rP rP rCat _),
      hQ_inv_eq ▸ localOnQft16_add_proj_noSym rP rCat rClean13 hg_i hw_i⟩⟩
attribute [local irreducible] SpecDefs.systemQubits_frozen
    SelectCompactAnc.ancWOfScr
noncomputable abbrev qft8PostCancel98IdealU (scrW : ℕ) (rP : QRegister 8 (totDimCompactGen scrW)) :
    Unitary (2 ^ totDimCompactGen scrW) := rP.embedUnitary (dPost8U * qftGridUnitary)
noncomputable def qft8PostCancel98CatU {Var : Type} (_v : Var) (scrW off : ℕ)
    (hoff : 1 ≤ off ∧ off + 21 ≤ scrW) (rP : QRegister 8 (totDimCompactGen scrW))
    (hP : Qft8Stg3ValidP scrW off rP) : Unitary (2 ^ totDimCompactGen scrW) :=
    polyPostCancelCleanUnitary (locCat8SharedCompactGen scrW) rP (qft8Stg3Delta7 scrW off hoff)
    (qft8Stg3Carry6 scrW off hoff) (qft8Stg3Clean13 scrW off hoff) (qft8Stg3_rP_disj_cat8 hP)
    (qft8Stg3_rP_disj_delta7 hoff hP) (qft8Stg3_delta7_disj_cat8 hoff)
    (qft8Stg3_delta7_disj_carry6 hoff) (qft8Stg3_cat8_disj_carry6 hoff)
    (qft8Stg3_rP_disj_carry6 hoff hP) (qft8Stg3_clean13_sub_delta7 hoff)
    (qft8Stg3_clean13_sub_carry6 hoff)
theorem qft8PostCancel98CatU_props {Var : Type} (v : Var) (scrW off : ℕ)
    (hoff : 1 ≤ off ∧ off + 21 ≤ scrW) (rP : QRegister 8 (totDimCompactGen scrW))
    (hP : Qft8Stg3ValidP scrW off rP) : (qft8PostCancel98CatU v scrW off hoff rP hP).1 *
    (qft8Stg3Clean13 scrW off hoff).basisOutcomeProjector 0 =
    (qft8PostCancel98Bracket scrW off hoff rP hP).toCircuit.eval.1 *
    (qft8Stg3Clean13 scrW off hoff).basisOutcomeProjector 0 ∧
    (qft8PostCancel98CatU v scrW off hoff rP hP).1 * cat8SharedProjCompactGen scrW =
    cat8SharedProjCompactGen scrW * (qft8PostCancel98IdealU scrW rP).1 ∧
    ((qft8PostCancel98CatU v scrW off hoff rP hP)⁻¹).1 * cat8SharedProjCompactGen scrW =
    ((qft8PostCancel98IdealU scrW rP)⁻¹).1 *
    cat8SharedProjCompactGen scrW := by have props :=
                                          polyPostCancelCleanUnitary_props (locCat8SharedCompactGen
                                          scrW) rP (qft8Stg3Delta7 scrW off hoff)
                                          (qft8Stg3Carry6 scrW off hoff)
                                          (qft8Stg3Clean13 scrW off hoff) (qft8Stg3_rP_disj_cat8 hP)
                                          (qft8Stg3_rP_disj_delta7 hoff hP)
                                          (qft8Stg3_delta7_disj_cat8 hoff)
                                          (qft8Stg3_delta7_disj_carry6 hoff)
                                          (qft8Stg3_cat8_disj_carry6 hoff)
                                          (qft8Stg3_rP_disj_carry6 hoff hP)
                                          (qft8Stg3_clean13_sub_delta7 hoff)
                                          (qft8Stg3_clean13_sub_carry6 hoff); exact ⟨props.1,
                                          props.2.1.1, props.2.1.2⟩
theorem qft8PostCancel98CatU_localOnQft16 {Var : Type} (v : Var) (scrW off : ℕ)
    (hoff : 1 ≤ off ∧ off + 21 ≤ scrW) (rP : QRegister 8 (totDimCompactGen scrW))
    (hP : Qft8Stg3ValidP scrW off rP) : LocalOnQft16 rP (locCat8SharedCompactGen scrW)
    (qft8PostCancel98CatU v scrW off hoff rP hP).1 ∧ LocalOnQft16 rP (locCat8SharedCompactGen scrW)
    ((qft8PostCancel98CatU v scrW off hoff rP hP)⁻¹).1 :=
    (polyPostCancelCleanUnitary_props (locCat8SharedCompactGen scrW) rP (qft8Stg3Delta7 scrW off
    hoff) (qft8Stg3Carry6 scrW off hoff) (qft8Stg3Clean13 scrW off hoff) (qft8Stg3_rP_disj_cat8 hP)
    (qft8Stg3_rP_disj_delta7 hoff hP) (qft8Stg3_delta7_disj_cat8 hoff)
    (qft8Stg3_delta7_disj_carry6 hoff) (qft8Stg3_cat8_disj_carry6 hoff)
    (qft8Stg3_rP_disj_carry6 hoff hP) (qft8Stg3_clean13_sub_delta7 hoff)
    (qft8Stg3_clean13_sub_carry6 hoff)).2.2
theorem qft8PostCancel98CatU_comm_projOneQ {Var : Type} (v : Var) (scrW off : ℕ)
    (hoff : 1 ≤ off ∧ off + 21 ≤ scrW) (rP : QRegister 8 (totDimCompactGen scrW))
    (hP : Qft8Stg3ValidP scrW off rP) : (qft8PostCancel98CatU v scrW off hoff rP hP).1 *
    projOneQCompactGen scrW = projOneQCompactGen scrW *
    (qft8PostCancel98CatU v scrW off hoff rP hP).1 := by
  have hqP : (QRegister.singleton (locQCompactGen scrW)).DisjointWires rP :=
    QRegister.disjoint_iff.mpr fun i k h ↦ by
      fin_cases i
      obtain ⟨p, hp, _, _⟩ := hP k;
      have hv :=
          congrArg Fin.val ((locAncCompactGen scrW).wires.injective (h.trans hp)); change 34 +
          scrW + 70 = p.val at hv; omega
  have hqCat : (QRegister.singleton (locQCompactGen scrW)).DisjointWires
      (locCat8SharedCompactGen scrW) :=
    QRegister.disjoint_iff.mpr fun i c h ↦ by
      fin_cases i
      have hv :=
          congrArg Fin.val ((locAncCompactGen scrW).wires.injective h); change 34 + scrW + 70 = 0 +
          (26 + c.val) at hv; omega
  exact localOnQft16_comm_basisOutcomeProjector
    (qft8PostCancel98CatU_localOnQft16 v scrW off hoff rP hP).1
    (QRegister.singleton (locQCompactGen scrW)) hqP hqCat 1
attribute [local irreducible] qft8PostCancel98CatU polyPostCancelT5Qft8Bracket98
theorem qft8PostCancel98Bracket_cleanStep_catU_of_subreg
    {Var : Type} [Fintype Var] [DecidableEq Var]
    {n wW : ℕ} [NeZero (2 ^ n)] (v : Var) (scrW off : ℕ) (hoff : 1 ≤ off ∧ off + 21 ≤ scrW)
    (rP : QRegister 8 (totDimCompactGen scrW)) (hP : Qft8Stg3ValidP scrW off rP)
    (rWork : QRegister wW (totDimCompactGen scrW))
    (hSub : ∀ i : Fin 13, ∃ j, (qft8Stg3Clean13 scrW off hoff).wires i = rWork.wires j)
    (hWP : rWork.DisjointWires rP)
    (hWCat : rWork.DisjointWires (locCat8SharedCompactGen scrW))
    (rTot : QRegister (totDimCompactGen scrW) n) :
    let Q := qft8PostCancel98CatU v scrW off hoff rP hP
    CleanWorkStep (rTot.compose rWork) (rTot.embedUnitary Q)
      (pQft8PostCancel98Fwd v scrW off hoff rTot rP hP) ∧
    CleanWorkStep (rTot.compose rWork) (rTot.embedUnitary Q)⁻¹
      (pQft8PostCancel98Rev v scrW off hoff rTot rP hP) := by
  let br := qft8PostCancel98Bracket scrW off hoff rP hP
  let Q := qft8PostCancel98CatU v scrW off hoff rP hP
  let rC := qft8Stg3Clean13 scrW off hoff
  let P0 := rC.basisOutcomeProjector 0
  obtain ⟨hLoc_f, hLoc_i⟩ := qft8PostCancel98CatU_localOnQft16 v scrW off hoff rP hP
  obtain ⟨hStep0, hStep_f, hStep_i⟩ := (postCancelBlocks_catShift_and_step v rTot
    (locCat8SharedCompactGen scrW) rP (qft8Stg3Delta7 scrW off hoff)
    (qft8Stg3Carry6 scrW off hoff) rC (qft8Stg3_rP_disj_cat8 hP)
    (qft8Stg3_rP_disj_delta7 hoff hP) (qft8Stg3_delta7_disj_cat8 hoff)
    (qft8Stg3_delta7_disj_carry6 hoff) (qft8Stg3_cat8_disj_carry6 hoff)
    (qft8Stg3_rP_disj_carry6 hoff hP) (qft8Stg3_clean13_sub_delta7 hoff)
    (qft8Stg3_clean13_sub_carry6 hoff)).2.2.1
  have hbr_comm : br.toCircuit.eval.1 * P0 = P0 * br.toCircuit.eval.1 := by
    dsimp only [P0]
    rwa [← cleanProj_range_eq_basisOutcomeProjector_zero rC]
  have hSubDisj {w : ℕ} {r : QRegister w (totDimCompactGen scrW)} (hd : rWork.DisjointWires r) :
      rC.DisjointWires r :=
    QRegister.disjoint_iff.mpr fun i k h ↦ let ⟨j, hj⟩ := hSub i; hd.ne j k (hj.symm.trans h)
  have heq_f : Q.1 * P0 = br.toCircuit.eval.1 * P0 :=
    (qft8PostCancel98CatU_props v scrW off hoff rP hP).1
  have heq_i : (Q⁻¹).1 * P0 = (br.toCircuit.eval⁻¹).1 * P0 := by
    calc (Q⁻¹).1 * P0
        = (Q⁻¹).1 * (P0 * (br.toCircuit.eval.1 * (br.toCircuit.eval⁻¹).1)) := by
            rw [show br.toCircuit.eval.1 * (br.toCircuit.eval⁻¹).1 = 1 from
              congrArg Subtype.val (mul_inv_cancel br.toCircuit.eval), mul_one]
      _ = ((Q⁻¹).1 * Q.1) * (P0 * (br.toCircuit.eval⁻¹).1) := by
            rw [← Matrix.mul_assoc P0, ← hbr_comm, ← heq_f]
            simp only [Matrix.mul_assoc]
      _ = (br.toCircuit.eval⁻¹).1 * P0 := by
            rw [show (Q⁻¹).1 * Q.1 = 1 from congrArg Subtype.val (inv_mul_cancel Q),
              one_mul, ← SelectFastQft8Gidney.unitary_inv_comm br.toCircuit.eval P0 hbr_comm]
  have hSubTot (i : Fin 13) : ∃ j, (rTot.compose rC) i = (rTot.compose rWork) j :=
    let ⟨j, hj⟩ := hSub i; ⟨j, congrArg rTot.wires hj⟩
  have liftStep (U B : Unitary (2 ^ totDimCompactGen scrW)) (prog : DynamicCircuit Var n)
      (hLoc : LocalOnQft16 rP (locCat8SharedCompactGen scrW) U.1)
      (heq : U.1 * P0 = B.1 * P0)
      (hst : CleanWorkStep (rTot.compose rC) (rTot.embedUnitary B) prog) :
      CleanWorkStep (rTot.compose rWork) (rTot.embedUnitary U) prog := by
    have lc {w : ℕ} (R : QRegister w (totDimCompactGen scrW))
        (hRP : R.DisjointWires rP) (hRC : R.DisjointWires (locCat8SharedCompactGen scrW)) :
        (rTot.embedUnitary U).1 * (rTot.compose R).basisOutcomeProjector 0 =
          (rTot.compose R).basisOutcomeProjector 0 * (rTot.embedUnitary U).1 := by
      rw [QRegister.embedUnitary_val, compose_basisOutcomeProjector_zero,
        ← rTot.embedMatrix_mul, ← rTot.embedMatrix_mul,
        localOnQft16_comm_basisOutcomeProjector hLoc R hRP hRC 0]
    have leq : (rTot.embedUnitary U).1 * (rTot.compose rC).basisOutcomeProjector 0 =
        (rTot.embedUnitary B).1 * (rTot.compose rC).basisOutcomeProjector 0 := by
      rw [QRegister.embedUnitary_val, QRegister.embedUnitary_val,
          compose_basisOutcomeProjector_zero,
        ← rTot.embedMatrix_mul, ← rTot.embedMatrix_mul, heq]
    exact CleanWorkStep.of_subreg _ _ hSubTot _ _ (lc rWork hWP hWCat)
      (CleanWorkStep.congr_on_proj (rTot.compose rC) (rTot.embedUnitary B) (rTot.embedUnitary U)
        prog (lc rC (hSubDisj hWP) (hSubDisj hWCat)) leq hst)
  rw [← QRegister.embedUnitary_inv] at hStep_i
  refine ⟨liftStep Q br.toCircuit.eval _ hLoc_f heq_f hStep_f, ?_⟩
  rw [← QRegister.embedUnitary_inv]
  exact liftStep Q⁻¹ br.toCircuit.eval⁻¹ _ hLoc_i heq_i hStep_i
/-- Any computational-basis diagonal operator `D` commutes with `rP.embedUnitary dPost8U`. -/
theorem diag_ket_comm_embed_dPost8U {M : ℕ} (rP : QRegister 8 M) (D : Operator (2 ^ M))
    (f : BitAssignment M → ℂ) (hD : ∀ β : BitAssignment M, D.mulVec (KinB.ket β) =
    f β • KinB.ket β) : D * (rP.embedUnitary dPost8U).1 = (rP.embedUnitary dPost8U).1 * D := by
  let d : Fin (2 ^ 8) → ℂ := fun r ↦ exp256 (ePost8 r)
  have hDp : ∀ β : BitAssignment M, (rP.embedUnitary dPost8U).1.mulVec (KinB.ket β) =
      d (readRegIdx rP β) • KinB.ket β := embedMatrix_diagonal_mulVec_ket8 rP d
  refine PhotochemistrySolution.KinB.matrix_ext_ket fun β ↦ ?_
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hDp β, Matrix.mulVec_smul, hD β,
      Matrix.mulVec_smul, hDp β, smul_comm]
/--
Drop-in conjugation theorem reducing `qft8PostCancel98CatU` conjugation of any `dPost8U`-commuting
kinetic core directly to `qft8Stg3IdealU = rP.embedUnitary qftGridUnitary`!
-/
theorem qft8PostCancel98CatU_conj_mul_cat8SharedProj {Var : Type} (v : Var) (scrW off : ℕ)
    (hoff : 1 ≤ off ∧ off + 21 ≤ scrW) (rP : QRegister 8 (totDimCompactGen scrW))
    (hP : Qft8Stg3ValidP scrW off rP) (U_kin : Unitary (2 ^ totDimCompactGen scrW))
    (hU_cat : U_kin.1 * cat8SharedProjCompactGen scrW = cat8SharedProjCompactGen scrW * U_kin.1)
    (hU_dpost : U_kin.1 * (rP.embedUnitary dPost8U).1 = (rP.embedUnitary dPost8U).1 * U_kin.1) :
    (((qft8PostCancel98CatU v scrW off hoff rP hP)⁻¹ * U_kin *
    (qft8PostCancel98CatU v scrW off hoff rP hP)).1) * cat8SharedProjCompactGen scrW =
    (((qft8Stg3IdealU scrW rP)⁻¹ * U_kin * (qft8Stg3IdealU scrW rP)).1) *
    cat8SharedProjCompactGen scrW := by
  obtain ⟨_, hcat_f, hcat_i⟩ := qft8PostCancel98CatU_props v scrW off hoff rP hP;
  let W := qft8PostCancel98IdealU scrW rP; let D := rP.embedUnitary dPost8U;
  let Qid := qft8Stg3IdealU scrW rP;
  have hW_cat : W.1 * cat8SharedProjCompactGen scrW = cat8SharedProjCompactGen scrW * W.1 :=
      rP.embedMatrix_comm_of_disjoint (locCat8SharedCompactGen scrW) (qft8Stg3_rP_disj_cat8 hP) _ _
  have hconj_W : (((qft8PostCancel98CatU v scrW off hoff rP hP)⁻¹ * U_kin *
      (qft8PostCancel98CatU v scrW off hoff rP hP)).1) * cat8SharedProjCompactGen scrW =
      ((W⁻¹ * U_kin * W).1) *
      cat8SharedProjCompactGen scrW
      := by simp only [Submonoid.coe_mul, Matrix.mul_assoc]; rw [hcat_f, ← Matrix.mul_assoc U_kin.1,
              hU_cat, Matrix.mul_assoc,
              ← Matrix.mul_assoc ((qft8PostCancel98CatU v scrW off hoff rP hP)⁻¹).1, hcat_i,
              Matrix.mul_assoc, ← Matrix.mul_assoc (cat8SharedProjCompactGen scrW), ← hU_cat,
              Matrix.mul_assoc, ← hW_cat]
  have hW_eq : W = D * Qid := rP.embedUnitary_mul dPost8U qftGridUnitary
  have hWinv_eq : W⁻¹ = Qid⁻¹ * D⁻¹ := by rw [hW_eq, _root_.mul_inv_rev]
  have hDD : (D⁻¹).1 * D.1 = 1 := congrArg Subtype.val (inv_mul_cancel D)
  have hconj_cancel : (W⁻¹ * U_kin * W).1 = (Qid⁻¹ * U_kin * Qid).1 := by
    rw [hWinv_eq, hW_eq]; simp only [Submonoid.coe_mul, Matrix.mul_assoc];
    rw [← Matrix.mul_assoc U_kin.1 D.1 Qid.1, hU_dpost, Matrix.mul_assoc D.1 U_kin.1 Qid.1,
        ← Matrix.mul_assoc (D⁻¹).1 D.1 (U_kin.1 * Qid.1), hDD, one_mul]
  rw [hconj_W, hconj_cancel]
end QuantumComputation.Specs.PhotochemistrySolution.Qft8PostCancelT5
end

noncomputable section
open QuantumComputation.Specs.PhotochemistrySolution.KinNormSlice
  QuantumComputation.Specs.PhotochemistrySolution.SelectCompactAnc
open Operator QProg Matrix Circuit Qubit QuantumComputation.Specs
  QuantumComputation.Specs.PhotochemistrySolution
  QuantumComputation.Specs.PhotochemistrySolution.SelectOracles
  QuantumComputation.Specs.PhotochemistrySolution.RouterSelectWiringA
  QuantumComputation.Specs.PhotochemistrySolution.ZeroNEremSpec
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
namespace QuantumComputation.Specs.PhotochemistrySolution.PotSelectWiring
open scoped Circuit.Notation
open PrimitiveGate
open PhotochemistrySolution.RouterSelectWiringB PhotochemistrySolution.SplitRouter47_187
open _root_.DynamicCircuit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt hiding ket matrix_ext_ket
theorem potBWire_out_lt {N : ℕ} {j : Fin N} (h1 : j.val < 9) : 32 + (j.val - 1) < 40 := by omega
theorem potBWire_nucLo_lt {N : ℕ} {j : Fin N} (h2 : j.val < 33) : j.val - 9 < 24 := by omega
theorem potBWire_elecLo_lt {N : ℕ} {j : Fin N} (h3 : j.val < 57) : j.val - 33 < 24 := by omega
theorem potBWire_elecHi_lt {N : ℕ} {j : Fin N} (h4 : j.val < 81) : j.val - 57 < 24 := by omega
theorem potBWire_inner_lt {N : ℕ} {j : Fin N} (h5 : j.val < 122) : j.val - 81 < 41 := by omega
theorem potBWire_nucHi_lt {N : ℕ} {j : Fin N} (h6 : j.val < 146) : j.val - 122 < 24 := by omega
theorem potBWire_clean_lt {Wp : ℕ} (hWp : Wp ≤ 714) (j : Fin (122 + Wp)) :
    j.val - 146 < 690 := by omega
/--
3-port Stage-4 wire map (`QRegister (122 + Wp) dLayout`, `Wp <= 193 + wIn` across `0 <= wIn`):
- `0`: `wLocQLayout` (`7297`),
- `1..8`: `rOut40Layout 32..39` (`5747..5754`: `isScreen, isPot, isKin, isNN, sp1[2], sp2[2]`),
- `9..32`: `rBufLo rNucLayout` (`5755..5778`, `NucPortA`),
- `33..56`: `rBufLo rElecLayout` (`5851..5874`, `ElecPortA`),
- `57..80`: `rBufHi rElecLayout` (`5875..5898`, unified `PortB = if isNN then nB else eB`),
- `81..121`: `rInner41Layout` (`7256..7296`, `41` uniform inner coin bits),
- `122..145`: `rBufHi rNucLayout` (`5779..5802`, `24` freed `NucPortB` clean wires),
- `146..121+Wp`: `rClean690Layout 0..Wp-25` (`[5680..5712]` and `[5947..6082+wIn]`).
-/
def potZeroNEremPortBWireFn (Wp : ℕ) (hWp : Wp ≤ 714) (j : Fin (122 + Wp)) : Wire dLayout :=
    if _ : j.val = 0 then wLocQLayout else if h1 : j.val < 9 then rOut40Layout ⟨32 + (j.val - 1),
    potBWire_out_lt h1⟩ else if h2 : j.val < 33 then rBufLo rNucLayout ⟨j.val - 9,
    potBWire_nucLo_lt h2⟩ else if h3 : j.val < 57 then rBufLo rElecLayout ⟨j.val - 33,
    potBWire_elecLo_lt h3⟩ else if h4 : j.val < 81 then rBufHi rElecLayout ⟨j.val - 57,
    potBWire_elecHi_lt h4⟩ else if h5 : j.val < 122 then rInner41Layout ⟨j.val - 81,
    potBWire_inner_lt h5⟩ else if h6 : j.val < 146 then rBufHi rNucLayout ⟨j.val - 122,
    potBWire_nucHi_lt h6⟩ else rClean690Layout ⟨j.val - 146, potBWire_clean_lt hWp j⟩
theorem potZeroNEremPortBWireFn_eq_old {Wp : ℕ} (hWp : Wp ≤ 714) (j : Fin (122 + Wp)) :
    potZeroNEremPortBWireFn Wp hWp j =
      if _ : j.val < 33 then potZeroNEremWireFn 0 (by omega) ⟨j.val, by omega⟩
      else if _ : j.val < 122 then potZeroNEremWireFn 0 (by omega) ⟨j.val + 24, by omega⟩
      else if _ : j.val < 146 then
        potZeroNEremWireFn 0 (by omega) ⟨33 + (j.val - 122), by omega⟩
      else rClean690Layout ⟨j.val - 146, potBWire_clean_lt hWp j⟩ := by
  let eqF {K} (f : Fin K → Wire dLayout) {a b : Fin K} (h : a.1 = b.1 := by
    dsimp only <;> omega) := congrArg f (Fin.ext h)
  by_cases h2 : j.val < 33
  · by_cases h0 : j.val = 0 <;> by_cases h1 : j.val < 9 <;>
      simp only [potZeroNEremPortBWireFn, potZeroNEremWireFn, h0, h1, h2, show (0 : ℕ) <
          33 by decide, ↓reduceDIte]
  · obtain ⟨h0, h1⟩ : ¬ j.val = 0 ∧ ¬ j.val < 9 := by omega
    by_cases h5 : j.val < 122
    · obtain ⟨g0, g1, g2, g3, g6⟩ : ¬ j.val + 24 = 0 ∧ ¬ j.val + 24 < 9 ∧ ¬ j.val + 24 < 33 ∧
          ¬ j.val + 24 < 57 ∧ j.val + 24 < 146 := by omega
      by_cases h3 : j.val < 57 <;> by_cases h4 : j.val < 81 <;>
        simp only [potZeroNEremPortBWireFn, potZeroNEremWireFn, h0, h1, h2, h3, h4, h5, g0, g1, g2,
            g3, g6,
          show (j.val + 24 < 81) ↔ (j.val < 57) by omega, show (j.val + 24 < 105) ↔
              (j.val < 81) by omega, ↓reduceDIte] <;>
        first | omega | exact eqF (rBufLo rElecLayout) | exact eqF (rBufHi rElecLayout)
              | exact eqF rInner41Layout
    · obtain ⟨h3, h4⟩ : ¬ j.val < 57 ∧ ¬ j.val < 81 := by omega
      by_cases h6 : j.val < 146
      · obtain ⟨k0, k1, k2, k3⟩ : ¬ 33 + (j.val - 122) = 0 ∧ ¬ 33 + (j.val - 122) < 9 ∧
            ¬ 33 + (j.val - 122) < 33 ∧ 33 + (j.val - 122) < 57 := by omega
        simp only [potZeroNEremPortBWireFn, potZeroNEremWireFn, h0, h1, h2, h3, h4, h5, h6, k0, k1,
            k2, k3, ↓reduceDIte]
        exact eqF (rBufHi rNucLayout)
      · simp only [potZeroNEremPortBWireFn, h0, h1, h2, h3, h4, h5, h6, ↓reduceDIte]

theorem val_potZeroNEremPortBWireFn {Wp : ℕ} (hWp : Wp ≤ 714) (j : Fin (122 + Wp)) :
    (potZeroNEremPortBWireFn Wp hWp j).val = if j.val = 0 then 7297 else if j.val < 33 then 5746 +
    j.val else if j.val < 81 then 5851 + (j.val - 33) else if j.val < 122 then 7256 +
    (j.val - 81) else if j.val < 146 then 5779 + (j.val - 122) else if j.val < 179 then 5680 +
    (j.val - 146) else 5947 + (j.val - 179) := by
  have hjLt : j.val < 122 + Wp := j.isLt
  rw [potZeroNEremPortBWireFn_eq_old]
  by_cases h33 : j.val < 33
  · have hv := val_potZeroNEremWireFn (Wp := 0) (by omega) ⟨j.val, by omega⟩
    simp only [h33, ↓reduceDIte] at hv ⊢
    rw [hv]
    split_ifs at * <;> omega
  · by_cases h122 : j.val < 122
    · have hv := val_potZeroNEremWireFn (Wp := 0) (by omega) ⟨j.val + 24, by omega⟩
      simp only [h33, h122, ↓reduceDIte] at hv ⊢
      rw [hv]
      split_ifs at * <;> omega
    · by_cases h146 : j.val < 146
      · have hv := val_potZeroNEremWireFn (Wp := 0) (by omega) ⟨33 + (j.val - 122), by omega⟩
        simp only [h33, h122, h146, ↓reduceDIte] at hv ⊢
        rw [hv]
        split_ifs at * <;> omega
      · have hv := val_rClean690Layout ⟨j.val - 146, potBWire_clean_lt hWp j⟩
        simp only [h33, h122, h146, ↓reduceDIte] at hv ⊢
        rw [hv]
        split_ifs at * <;> omega
/-- Linear left inverse of `(potZeroNEremPortBWireFn Wp hWp ·).val`. -/
def invPotZeroNEremPortB (w : ℕ) : ℕ :=
    if w = 7297 then 0 else if w < 5715 then 146 + (w - 5680) else if w < 5779 then w -
    5746 else if w < 5810 then 122 + (w - 5779) else if w < 5910 then 33 + (w - 5851) else if w <
    7000 then 179 + (w - 5947) else 81 + (w - 7256)
theorem invPotZeroNEremPortB_val {Wp : ℕ} (hWp : Wp ≤ 714) (j : Fin (122 + Wp)) :
    invPotZeroNEremPortB (potZeroNEremPortBWireFn Wp hWp j).val = j.val := by
  have hw := val_potZeroNEremPortBWireFn hWp j
  split_ifs at hw <;> (
    rw [hw]
    dsimp only [invPotZeroNEremPortB]
    split_ifs <;> omega)
theorem rPotZeroNEremPortB_inj {Wp : ℕ}
    (hWp : Wp ≤ 714) : Function.Injective (potZeroNEremPortBWireFn Wp hWp) :=
  fun a b h ↦
      Fin.ext (by rw [← invPotZeroNEremPortB_val hWp a, ← invPotZeroNEremPortB_val hWp b, h])
/-- Complete `(122 + Wp)`-wire 3-port potential register on `dLayout` (`Wp <= 193 + wIn`). -/
def rPotZeroNEremPortB (Wp : ℕ) (hWp : Wp ≤ 714) : QRegister (122 + Wp) dLayout :=
    ⟨⟨potZeroNEremPortBWireFn Wp hWp, rPotZeroNEremPortB_inj hWp⟩⟩
theorem potBIdx0_lt {W : ℕ} : 0 < 122 + W := by omega
theorem potBIdx1_lt {W : ℕ} : 1 < 122 + W := by omega
theorem potBIdx2_lt {W : ℕ} : 2 < 122 + W := by omega
theorem potBIdx4_lt {W : ℕ} : 4 < 122 + W := by omega
theorem potBIdx5_lt {W : ℕ} : 5 < 122 + W := by omega
theorem potBIdx6_lt {W : ℕ} : 6 < 122 + W := by omega
theorem potBIdx7_lt {W : ℕ} : 7 < 122 + W := by omega
theorem potBIdx8_lt {W : ℕ} : 8 < 122 + W := by omega
theorem potBBlkNucA_le {W : ℕ} : 9 + 24 ≤ 122 + W := by omega
theorem potBBlkElecA_le {W : ℕ} : 33 + 24 ≤ 122 + W := by omega
theorem potBBlkPortB_le {W : ℕ} : 57 + 24 ≤ 122 + W := by omega
theorem potBBlkCoin41_le {W : ℕ} : 81 + 41 ≤ 122 + W := by omega
theorem potBBlkWork_le {W : ℕ} : 122 + W ≤ 122 + W := le_rfl
/-- `wPotBLocQ` helper in `PotentialSelectSpecA`. -/
abbrev wPotBLocQ {W n : ℕ} (r : QRegister (122 + W) n) : Wire n := r ⟨0, potBIdx0_lt⟩
abbrev wPotBIsScreen {W n : ℕ} (r : QRegister (122 + W) n) : Wire n := r ⟨1, potBIdx1_lt⟩
/-- `wPotBIsPot` helper in `PotentialSelectSpecA`. -/
abbrev wPotBIsPot {W n : ℕ} (r : QRegister (122 + W) n) : Wire n := r ⟨2, potBIdx2_lt⟩
/-- `wPotBIsNN` helper in `PotentialSelectSpecA`. -/
abbrev wPotBIsNN {W n : ℕ} (r : QRegister (122 + W) n) : Wire n := r ⟨4, potBIdx4_lt⟩
abbrev wPotBSp1B0 {W n : ℕ} (r : QRegister (122 + W) n) : Wire n := r ⟨5, potBIdx5_lt⟩
/-- `wPotBSp1B1` helper in `PotentialSelectSpecA`. -/
abbrev wPotBSp1B1 {W n : ℕ} (r : QRegister (122 + W) n) : Wire n := r ⟨6, potBIdx6_lt⟩
abbrev wPotBSp2B0 {W n : ℕ} (r : QRegister (122 + W) n) : Wire n := r ⟨7, potBIdx7_lt⟩
/-- `wPotBSp2B1` helper in `PotentialSelectSpecA`. -/
abbrev wPotBSp2B1 {W n : ℕ} (r : QRegister (122 + W) n) : Wire n := r ⟨8, potBIdx8_lt⟩
abbrev rPotBNucA {W n : ℕ} (r : QRegister (122 + W) n) : QRegister 24 n :=
  r.compose (QRegister.block 9 24 potBBlkNucA_le)
/-- `rPotBElecA` helper in `PotentialSelectSpecA`. -/
abbrev rPotBElecA {W n : ℕ} (r : QRegister (122 + W) n) : QRegister 24 n :=
  r.compose (QRegister.block 33 24 potBBlkElecA_le)
/-- `rPotBPortB` helper in `PotentialSelectSpecA`. -/
abbrev rPotBPortB {W n : ℕ} (r : QRegister (122 + W) n) : QRegister 24 n :=
  r.compose (QRegister.block 57 24 potBBlkPortB_le)
/-- `rPotBCoin41` helper in `PotentialSelectSpecA`. -/
abbrev rPotBCoin41 {W n : ℕ} (r : QRegister (122 + W) n) : QRegister 41 n :=
  r.compose (QRegister.block 81 41 potBBlkCoin41_le)
/-- `rPotBWork` helper in `PotentialSelectSpecA`. -/
abbrev rPotBWork {W n : ℕ} (r : QRegister (122 + W) n) : QRegister W n :=
  r.compose (QRegister.block 122 W potBBlkWork_le)
/-- `PotBPhaseBitFn` helper in `PotentialSelectSpecA`. -/
abbrev PotBPhaseBitFn : Type :=
  Bool → Bool → Fin 4 → Fin 4 →
    (Fin 3 → Fin 256) → (Fin 3 → Fin 256) →
    (Fin 3 → Fin 256) → (Fin 3 → Fin 256) → BitAssignment 41 → ZMod 2
/-- Phase bit of a 3-port `Stage4ZeroNEremPotOraclePortB` read from `r : QRegister (122 + W) n`.
-/
abbrev potOraclePortBBitEval {W n : ℕ} (phaseBit : PotBPhaseBitFn) (r : QRegister (122 + W) n)
    (δ : BitAssignment n) : ZMod 2 :=
    phaseBit (δ (wPotBIsScreen r) == 1) (δ (wPotBIsNN r) == 1) (speciesOfBits2 (δ (wPotBSp1B0 r))
    (δ (wPotBSp1B1 r))) (speciesOfBits2 (δ (wPotBSp2B0 r)) (δ (wPotBSp2B1 r)))
    (coordOfReg24 (rPotBNucA r) δ)
    (if δ (wPotBIsNN r) == 1 then coordOfReg24 (rPotBPortB r) δ else 0)
    (coordOfReg24 (rPotBElecA r) δ)
    (if δ (wPotBIsNN r) == 1 then 0 else coordOfReg24 (rPotBPortB r) δ)
    (fun k ↦ δ (rPotBCoin41 r k))
end QuantumComputation.Specs.PhotochemistrySolution.PotSelectWiring

section
open QuantumComputation.Specs.PhotochemistrySolution.KetSupport
  QuantumComputation.Specs.PhotochemistrySolution.RouterSelectWiringB
open _root_.DynamicCircuit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt hiding bit_cases
  eval_seq_mulVec ket ket_CNOT ket_TOFF ket_X ket_projector_one ket_projector_zero matrix_ext_ket
  qAssign_obs_map_val
open _root_.QuantumComputation.Specs.PhotochemistrySolution.QubitizationWalkSem (sqrtHalf)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB (ket)
attribute [local irreducible]
    QuantumComputation.Specs.PhotochemistrySolution.SelectCompactAnc.ancWOfScr
namespace QuantumComputation.Specs.PhotochemistrySolution.PotSelectWiring
open PhotochemistrySolution.SelectApprox
open _root_.QuantumComputation.Specs.PhotochemistrySolution.QubitizationWalkSem
  (sqrtHalf_mul_sqrtHalf)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB (matrix_ext_ket)
attribute [local irreducible] SpecDefs.systemQubits_frozen
  PgBase.phaseGradientState abpKin14Usel
/-- Per-outer-coin potential expectation on computational basis index `x`. -/
def potTermZeroNErem (decodeCoin : Fin (2 ^ 41) → ZeroNEremSector) (potExpect : PotExpectFn)
    (c : Fin (2 ^ 41)) (x : Fin (2 ^ systemQubits_frozen)) : ℝ :=
  match decodeCoin c with
  | .idle => 0
  | .kin _ _ => 0
  | .ee n1 e1 e2 =>
      potExpect true false (nucSpecies n1) 0
        (sysCoord x (nucParticle n1)) 0
        (sysCoord x (elecParticle e1)) (sysCoord x (elecParticle e2))
  | .nn n1 n2 e1 =>
      potExpect true true (nucSpecies n1) (nucSpecies n2)
        (sysCoord x (nucParticle n1)) (sysCoord x (nucParticle n2))
        (sysCoord x (elecParticle e1)) 0
  | .en n1 e1 =>
      potExpect false false (nucSpecies n1) 0
        (sysCoord x (nucParticle n1)) 0 (sysCoord x (elecParticle e1)) 0
/-- System-register operator summed over the 41 inner coin bits at fixed outer coin `c`. -/
noncomputable def bOuterZeroNErem (decodeCoin : Fin (2 ^ 41) → ZeroNEremSector)
    (potExpect : PotExpectFn) (c : Fin (2 ^ 41)) : OpSys :=
  match decodeCoin c with
  | .idle => (2 ^ 41 : ℂ) • (1 : OpSys)
  | .kin i ax => (2 ^ 41 : ℂ) • kinNormOp i ax
  | _ => (2 ^ 41 : ℂ) • diagReal (potTermZeroNErem decodeCoin potExpect c)
theorem block_encoding_of_ket {N L S R : ℕ} [NeZero (2 ^ N)] (rL : QRegister L N)
    (rS : QRegister S N) (rScr : QRegister R N) (A : Operator (2 ^ S))
    (H W U : Operator.Unitary (2 ^ N)) (g : BitAssignment N → Fin (2 ^ 41) → BitAssignment 41 →
    BitAssignment N) (bOp : Fin (2 ^ 41) → Operator (2 ^ S))
    (hAvg : (2 ^ 82 : ℂ)⁻¹ • (∑ c : Fin (2 ^ 41), bOp c) = A)
    (hHad : ∀ (β : BitAssignment N), (∀ u, β (rL u) = 0) → H.1.mulVec (ket β) =
    (sqrtHalf ^ 82) • ∑ c : Fin (2 ^ 41), ∑ z : BitAssignment 41, ket (g β c z))
    (hSec : ∀ (β : BitAssignment N), (∀ u, β (rL u) = 0) → (∀ m, β (rScr m) = 0) →
    ∀ c : Fin (2 ^ 41), (∑ z : BitAssignment 41, (rL.basisOutcomeProjector 0 *
    (H⁻¹).1).mulVec (((W⁻¹ * U * W).1).mulVec (ket (g β c z)))) =
    (sqrtHalf ^ 82) • (rS.embedMatrix (bOp c)).mulVec (ket β)) : rL.basisOutcomeProjector 0 *
    ((W * H)⁻¹ * U * (W * H)).1 * rL.basisOutcomeProjector 0 * rScr.basisOutcomeProjector 0 =
    rS.embedMatrix A * rL.basisOutcomeProjector 0 * rScr.basisOutcomeProjector 0 := by
  refine matrix_ext_ket fun β ↦ ?_
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec (ket β),
    ← Matrix.mulVec_mulVec _ (rS.embedMatrix A), SelectRefl.ket_basisOutcomeProjector_zero]
  by_cases hScr : ∀ m, β (rScr m) = 0 <;> simp only [hScr, implies_true, ↓reduceIte,
      Matrix.mulVec_zero]
  rw [PhotochemistrySolution.SelectRefl.ket_basisOutcomeProjector_zero]
  by_cases hr0 : ∀ u, β (rL u) = 0 <;> simp only [hr0, implies_true, ↓reduceIte, Matrix.mulVec_zero]
  rw [show rL.basisOutcomeProjector 0 * ((W * H)⁻¹ * U * (W * H)).1 =
      (rL.basisOutcomeProjector 0 * (H⁻¹).1) * (W⁻¹ * U * W).1 * H.1 by
      rw [_root_.mul_inv_rev]
      simp only [Submonoid.coe_mul, Matrix.mul_assoc],
    ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hHad β hr0, Matrix.mulVec_smul,
    Matrix.mulVec_smul, Matrix.mulVec_sum, Matrix.mulVec_sum]
  simp_rw [Matrix.mulVec_sum, hSec β hr0 hScr, ← Finset.smul_sum, smul_smul, ← Matrix.sum_mulVec,
      ← rS.embedMatrix_sum]
  rw [show sqrtHalf ^ 82 * sqrtHalf ^ 82 =
      (2 ^ 82 : ℂ)⁻¹ by rw [← mul_pow, sqrtHalf_mul_sqrtHalf, one_div, inv_pow],
    ← Matrix.smul_mulVec, ← rS.embedMatrix_smul, hAvg]

end QuantumComputation.Specs.PhotochemistrySolution.PotSelectWiring

namespace QuantumComputation.Specs.PhotochemistrySolution.GenWeightsSelect
open PhotochemistrySolution.SplitRouter47_187 PhotochemistrySolution.Stage12Compact
  PhotochemistrySolution.TelescopeSlice PhotochemistrySolution.PotSelectWiring
  PhotochemistrySolution.SelectApprox
attribute [local irreducible] systemQubits_frozen PgBase.phaseGradientState abpKin14Usel
/--
Arbitrary-weight 41-bit coin multiplicity contract on `ZeroNEremSector` (also enforcing
`e1 < e2` on `.ee` and `n1 < n2` on `.nn`).
-/
def ValidGenZeroNEremCoin (wEE : Fin 4 → ℕ) (wNN : Fin 4 → Fin 4 → ℕ) (wEN : Fin 4 → ℕ)
    (wKin : Particle_frozen → ℕ) (wIdle : ℕ) (decodeCoin : Fin (2 ^ 41) → ZeroNEremSector) : Prop :=
  ∀ s : ZeroNEremSector,
    ((Finset.univ : Finset (Fin (2 ^ 41))).filter (fun c ↦ decodeCoin c = s)).card =
      match s with
      | .idle => wIdle
      | .ee n1 e1 e2 => if e1 < e2 then wEE (nucSpecies n1) else 0
      | .nn n1 n2 _ => if n1 < n2 then wNN (nucSpecies n1) (nucSpecies n2) else 0
      | .en n1 _ => wEN (nucSpecies n1)
      | .kin i _ => wKin i
theorem ValidGenZeroNEremCoin.ee_lt {wEE : Fin 4 → ℕ} {wNN : Fin 4 → Fin 4 → ℕ} {wEN : Fin 4 → ℕ}
    {wKin : Particle_frozen → ℕ} {wIdle : ℕ} {decodeCoin : Fin (2 ^ 41) → ZeroNEremSector}
    (hCoin : ValidGenZeroNEremCoin wEE wNN wEN wKin wIdle decodeCoin) {c : Fin (2 ^ 41)}
    {n1 : Fin 47} {e1 e2 : Fin 187} (hc : decodeCoin c = .ee n1 e1 e2) : e1 < e2 := by
  exact Decidable.byContradiction fun h ↦ (Finset.card_pos.mpr
    ⟨c, Finset.mem_filter.mpr ⟨Finset.mem_univ c,
        hc⟩⟩).ne' ((hCoin (.ee n1 e1 e2)).trans (ite_eq_right h))
theorem ValidGenZeroNEremCoin.nn_lt {wEE : Fin 4 → ℕ} {wNN : Fin 4 → Fin 4 → ℕ} {wEN : Fin 4 → ℕ}
    {wKin : Particle_frozen → ℕ} {wIdle : ℕ} {decodeCoin : Fin (2 ^ 41) → ZeroNEremSector}
    (hCoin : ValidGenZeroNEremCoin wEE wNN wEN wKin wIdle decodeCoin) {c : Fin (2 ^ 41)}
    {n1 n2 : Fin 47} {e1 : Fin 187} (hc : decodeCoin c = .nn n1 n2 e1) : n1 < n2 := by
  exact Decidable.byContradiction fun h ↦ (Finset.card_pos.mpr
    ⟨c, Finset.mem_filter.mpr ⟨Finset.mem_univ c,
        hc⟩⟩).ne' ((hCoin (.nn n1 n2 e1)).trans (ite_eq_right h))
end QuantumComputation.Specs.PhotochemistrySolution.GenWeightsSelect

end
end

noncomputable section
open QuantumComputation.Specs.PhotochemistrySolution.FineLegendre
  QuantumComputation.Specs.PhotochemistrySolution.InPlaceModAdd
  QuantumComputation.Specs.PhotochemistrySolution.SelectCsa64ProvSpec
open QuantumComputation.Specs.PhotochemistrySolution.XMeasChunkQromUnld
  QuantumComputation.Specs.PhotochemistrySolution.SelectOracles
  QuantumComputation.Specs.PhotochemistrySolution.XMeasLinearCleanStep
open QuantumComputation.Specs.PhotochemistrySolution.PotSelectWiring
  QuantumComputation.Specs.PhotochemistrySolution.UnembedO3Bridge Operator QProg Matrix
  QuantumComputation.Specs.PhotochemistrySolution
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynQromUncompA (projBit
    remeasureIf)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Word73PotPool (openBoxDist3DSq)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SubregMBUCore (onRegCP wrapDynOnReg
    counts_wrapDynOnReg uStageOfCP validProg_onRegCP)
namespace QuantumComputation.Specs.PhotochemistrySolution.PotOracleGen
open Circuit Qubit PhotochemistrySolution.SelectStructuredCB PhotochemistrySolution.ZeroNEremSpec
  PhotochemistrySolution.ZeroNEremCsa36Kick
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
open PhotochemistrySolution.Csa36KickStep
open _root_.DynamicCircuit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt hiding bit_cases ket ket_CNOT
  ket_TOFF ket_X ket_projector_one ket_projector_zero localIdx matrix_ext_ket qAssign_obs_map_val
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt (writeReg writeReg_apply_reg
  writeReg_apply_of_not_mem)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB (ket matrix_ext_ket)
attribute [local semireducible] SubregMBUCore.onRegCP SubregMBUCore.wrapDynOnReg
    SubregMBUCore.uStageOfCP DynQromUncompA.fwdCirc
theorem itePos {α : Sort*} {c : Prop} [Decidable c] (h : c) {a b : α} : (if c then a else b) = a :=
    ite_eq_left h
theorem iteNeg {α : Sort*} {c : Prop} [Decidable c] (h : ¬c) {a b : α} : (if c then a else b) = b :=
    ite_eq_right h
theorem ditePos {α : Sort*} {c : Prop} [Decidable c] (h : c) {a : c → α} {b : ¬c → α} :
    (if hc : c then a hc else b hc) = a h := dite_eq_left h
theorem diteNeg {α : Sort*} {c : Prop} [Decidable c] (h : ¬c) {a : c → α} {b : ¬c → α} :
    (if hc : c then a hc else b hc) = b h := dite_eq_right h

/-- Pointwise inequality from register disjointness. -/
theorem disj_ne {a b n : ℕ} {rA : QRegister a n} {rB : QRegister b n} (hd : rA.DisjointWires rB)
    (i : Fin a) (j : Fin b)
    : rA i ≠ rB j := fun e ↦ Set.disjoint_left.mp hd ⟨i, rfl⟩ ⟨j, e.symm⟩
/-- Pointwise wire inequality promotes to register disjointness. -/
theorem disj_of_ne {a b n : ℕ} {rA : QRegister a n} {rB : QRegister b n} (h : ∀ (i : Fin a)
    (j : Fin b), rA i ≠ rB j) :
    rA.DisjointWires rB := Set.disjoint_left.mpr fun _ ⟨i, hi⟩ ⟨j, hj⟩ ↦ h i j (hi.trans hj.symm)

theorem cpw_onRegCP_clean {w n : ℕ} (r : QRegister w n) {S : Wire n → Prop} (hr : ∀ u, S (r u)) :
    ∀ cp
    : ComputeProg w, ComputeProgWires S (onRegCP r cp)
  | .id => trivial
  | .x _ => hr _
  | .cnot _ _ _ => ⟨hr _, hr _⟩
  | .andGate _ _ _ _ _ _ => ⟨hr _, hr _, hr _⟩
  | .seq p₁ p₂ => ⟨cpw_onRegCP_clean r hr p₁, cpw_onRegCP_clean r hr p₂⟩

theorem stepCB_writeReg_comm {w k n : ℕ} (r : QRegister w n) (rT : QRegister k n)
    (hd : r.DisjointWires rT)
    (f : BitAssignment w → BitAssignment w) (g : Fin k → ZMod 2) (β : BitAssignment n) :
    stepCB r f (writeReg β rT g) = writeReg (stepCB r f β) rT g := by
  dsimp only [stepCB]
  rw [show (fun u ↦ writeReg β rT g (r u)) = fun u ↦ β (r u) from funext fun u ↦
    writeReg_apply_of_not_mem _ _ _ _ fun ⟨j, hj⟩ ↦ disj_ne hd u j hj.symm]
  ext x
  by_cases hxR : ∃ u, r u = x
  · obtain ⟨u, rfl⟩ := hxR
    rw [writeReg_apply_reg, writeReg_apply_of_not_mem _ _ _ _ fun ⟨j, hj⟩ ↦ disj_ne hd u j hj.symm,
        writeReg_apply_reg]
  · by_cases hxT : ∃ j, rT j = x
    · obtain ⟨j, rfl⟩ := hxT
      rw [writeReg_apply_of_not_mem _ _ _ _ hxR, writeReg_apply_reg, writeReg_apply_reg]
    · simp only [writeReg_apply_of_not_mem _ _ _ _ hxR, writeReg_apply_of_not_mem _ _ _ _ hxT]

theorem subspaceStep_wrapOnReg_vprog2 {Var : Type} [Fintype Var] [DecidableEq Var] {W w n : ℕ}
    [NeZero (2 ^ n)]
    (v : Var) (rWork : QRegister W n) (r : QRegister w n) (sLoc : Finset (Wire w))
        (cp : ComputeProg w)
    (nAnd : ℕ) (hVpLoc : cp.ValidProg ∅ sLoc) (hAnd : cp.numAnd = nAnd)
        (stPre stPost : BitAssignment n →
      BitAssignment n) (phPre phPost : BitAssignment n → ZMod 2) (pMid : DynamicCircuit Var n)
    (hClnPre : ∀ u : Wire w, u ∈ sLoc → ∀ δ, (∀ k : Fin W, δ (rWork k) = 0) → stPre δ (r u) = 0)
      (hClnPost : ∀ u : Wire w, u ∈ sLoc → ∀ δ, (∀ k : Fin W, δ (rWork k) = 0) → stPost δ (r u) = 0)
    (hMid : SubspaceStep (mkKetOpW rWork (fun δ ↦ stepCB r cp.fwdBits (stPre δ)) phPre)
        (mkKetOpW rWork
      (fun δ ↦ stepCB r cp.fwdBits (stPost δ)) phPost) pMid) :
    SubspaceStep (mkKetOpW rWork stPre phPre) (mkKetOpW rWork stPost phPost)
        (wrapDynOnReg v r cp pMid) ∧
      (wrapDynOnReg v r cp pMid).count .T = 4 * nAnd + pMid.count .T ∧
    (wrapDynOnReg v r cp pMid).count .TOFF = pMid.count .TOFF ∧ (∀ S : Wire n → Prop,
        (∀ u, S (r u)) → DynWires S pMid →
      DynWires S (wrapDynOnReg v r cp pMid)) := by
  have hCleanOp {stX} (hClnX : ∀ u ∈ sLoc, ∀ δ, (∀ k, δ (rWork k) = 0) → stX δ (r u) = 0) (ph) :
      KinB.cleanProj (sLoc.image r.wires) * mkKetOpW rWork stX ph = mkKetOpW rWork stX ph :=
    matrix_ext_ket fun δ ↦ by
      rw [← Matrix.mulVec_mulVec, mkKetOpW_mulVec_ket]
      split_ifs with hz
      · rw [Matrix.mulVec_smul, KinB.cleanProj_mulVec_ket, ite_eq_left fun _ hy ↦
          (Finset.mem_image.mp hy).choose_spec.2 ▸ hClnX _ (Finset.mem_image.mp hy).choose_spec.1 δ
              hz]
      · rw [Matrix.mulVec_zero]
  obtain ⟨ht, hf⟩ := counts_wrapDynOnReg v r cp pMid
  refine ⟨PhotochemistrySolution.DynQromUncompA.subspaceStep_wrapDyn v (onRegCP r cp)
      (sLoc.image r.wires) pMid _ _ (validProg_onRegCP r hVpLoc) (hCleanOp hClnPre phPre)
      (hCleanOp hClnPost phPost) ?_, ht.trans (hAnd ▸ rfl), hf,
    fun S hr hd ↦ dynWires_wrapDyn v (onRegCP r cp) pMid (cpw_onRegCP_clean r hr cp) hd⟩
  rwa [show (DynQromUncompA.fwdCirc (onRegCP r cp)).eval.1 = (uStageOfCP r cp).1 by
      rw [PhotochemistrySolution.SubregMBUCore.fwdCirc_onRegCP_eq, Circuit.eval_onRegister]
      rfl, uStageOfCP_mul_mkKetOpW, uStageOfCP_mul_mkKetOpW]

theorem potGen_y36_lt (K : ℕ) (b : Fin 36) : 18 + b.val < 54 + K := by omega
theorem potGen_mid_lt {M K : ℕ} (hMK : M ≤ K) (j : Fin M) : 54 + j.val < 54 + K :=
    Nat.add_lt_add_left (Nat.lt_of_lt_of_le j.isLt hMK) 54
theorem potGen_k_lt (K : ℕ) (u : Fin K) : 54 + u.val < 54 + K := by omega
theorem potGen_d2_lt (K : ℕ) (b : Fin 18) : b.val < 54 + K := by omega
theorem writeReg_zero_prefix_pairStep {B n : ℕ} (rB : QRegister B n) (β : BitAssignment n)
    (f g : Fin B → ZMod 2) (hg : ∀ b, g b = β (rB b)) :
    writeReg β rB (fun b ↦ if b.val < 0 then f b else g b) = β := funext fun w ↦ by
  by_cases hw : ∃ b : Fin B, rB b = w
  · obtain ⟨b, rfl⟩ := hw
    rw [writeReg_apply_reg, ite_eq_right (Nat.not_lt_zero _), hg b]
  · exact writeReg_apply_of_not_mem _ _ _ _ hw
theorem writeReg_upd_prefix_pairStep {B n : ℕ} (rB : QRegister B n) (β : BitAssignment n)
    (f g : Fin B → ZMod 2) {j : ℕ} (hj : j < B) :
    Function.update (writeReg β rB fun b ↦ if b.val < j then f b else g b) (rB ⟨j, hj⟩)
        (f ⟨j, hj⟩) =
      writeReg β rB fun b ↦ if b.val < j + 1 then f b else g b := funext fun w ↦ by
  by_cases hw : ∃ b : Fin B, rB b = w
  · obtain ⟨b, rfl⟩ := hw
    rcases eq_or_ne b ⟨j, hj⟩ with rfl | hbj
    · rw [Function.update_self, writeReg_apply_reg, ite_eq_left (Nat.lt_succ_self _)]
    · rw [Function.update_of_ne (rB.wires.injective.ne hbj), writeReg_apply_reg, writeReg_apply_reg]
      exact if_congr ⟨Nat.lt_succ_of_lt,
        fun h ↦ lt_of_le_of_ne (Nat.lt_succ_iff.mp h) fun e ↦ hbj (Fin.ext e)⟩ rfl rfl
  · rw [Function.update_of_ne (fun e ↦ hw ⟨⟨j, hj⟩, e.symm⟩),
        writeReg_apply_of_not_mem _ _ _ _ hw, writeReg_apply_of_not_mem _ _ _ _ hw]
/-- Exact 3D open-box squared grid distance. -/
abbrev openCoordDistSq (a b : Fin 3 → Fin 256) : ℕ :=
    openBoxDist1D (a 0) (b 0) ^ 2 + openBoxDist1D (a 1) (b 1) ^ 2 + openBoxDist1D (a 2) (b 2) ^ 2
end QuantumComputation.Specs.PhotochemistrySolution.PotOracleGen

namespace QuantumComputation.Specs.PhotochemistrySolution.ScreenFermatCore
open DynamicCircuit Real QuantumComputation.Specs PhotochemistrySolution.QubitizationWalkSem
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt
open PhotochemistrySolution.SelectApprox PhotochemistrySolution.SelectCompactAnc
  PhotochemistrySolution.ClusterPotSlice PhotochemistrySolution.ZeroNEremSpec
open PhotochemistrySolution.BlockApprox PhotochemistrySolution.GenWeightsSelect
  PhotochemistrySolution.TelescopeSlice
open _root_.QuantumComputation.Specs.PhotochemistrySolution.PotOracleGen (openCoordDistSq)
theorem sum_bits_testBit_ind : ∀ (d t : ℕ), t ≤ 2 ^ d → (∑ hi : (Fin d → ZMod 2),
    if (t + ∑ k : Fin d,
  (hi k).val * 2 ^ k.val).testBit d then (-1 : ℝ) else 1) = (2 ^ d : ℝ) - 2 * (t : ℝ)
  | 0, tn, ht => by
    simp only [Finset.univ_unique, Finset.sum_singleton, Finset.univ_eq_empty, Finset.sum_empty,
        add_zero, pow_zero]
    rcases (by omega : tn = 0 ∨ tn = 1) with rfl | rfl <;> norm_num
  | d + 1, tn, ht => by
    rw [← (Fin.consEquiv fun _ : Fin (d + 1) ↦ ZMod 2).sum_comp, Fintype.sum_prod_type]
    simp_rw [show ∀ (b : ZMod 2) (tl : Fin d → ZMod 2),
        (tn + ∑ k : Fin (d + 1), (Fin.consEquiv (fun _ : Fin (d + 1) ↦ ZMod 2) (b, tl) k).val *
            2 ^ k.val).testBit (d + 1) =
        ((tn + b.val) / 2 + ∑ k : Fin d, (tl k).val * 2 ^ k.val).testBit d from fun b tl ↦ by
      rw [Fin.sum_univ_succ]
      change (tn + (b.val * 2 ^ 0 + ∑ k : Fin d, (tl k).val * 2 ^ (k.val + 1))).testBit (d + 1) = _
      simp only [pow_zero, mul_one, pow_succ', ← mul_assoc]
      simp_rw [show ∀ k : Fin d, (tl k).val * 2 * 2 ^ k.val = 2 *
          ((tl k).val * 2 ^ k.val) from fun _ ↦ by ring,
        ← Finset.mul_sum, ← add_assoc, Nat.testBit_succ]
      exact congrArg (Nat.testBit · d) (by omega)]
    erw [Fin.sum_univ_two, ZMod.val_zero, ZMod.val_one]
    rw [sum_bits_testBit_ind d _ (by omega), sum_bits_testBit_ind d _ (by omega), pow_succ']
    linarith [show (((tn + 0) / 2 : ℕ) : ℝ) + ((tn + 1) / 2 : ℕ) = tn by
      exact_mod_cast (by omega : (tn + 0) / 2 + (tn + 1) / 2 = tn)]

theorem openCoordDistSq_sys (x : Fin (2 ^ systemQubits_frozen)) (p q : Particle_frozen) :
    openCoordDistSq (sysCoord x p)
    (sysCoord x q) = pairOpenDistSq x p q := by
  unfold openCoordDistSq sysCoord pairOpenDistSq
  rw [Fin.sum_univ_three]
theorem openBoxDist3DSq_sys (x : Fin (2 ^ systemQubits_frozen)) (p q : Particle_frozen) :
    openBoxDist3DSq (sysCoord x p)
    (sysCoord x q) = pairOpenDistSq x p q := by
  unfold openBoxDist3DSq sysCoord pairOpenDistSq
  rw [Fin.sum_univ_three]
theorem nucParticle_eq_nucP (n1 : Fin 47) : nucParticle n1 = nucP n1 := rfl
theorem elecParticle_eq_elecP (e1 : Fin 187) : elecParticle e1 = elecP e1 := rfl
end QuantumComputation.Specs.PhotochemistrySolution.ScreenFermatCore

namespace QuantumComputation.Specs.PhotochemistrySolution.ZHi30
open DynamicCircuit Real QuantumComputation.Specs PhotochemistrySolution.ClusterPotSlice
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt
open PhotochemistrySolution.ZeroNEremSpec PhotochemistrySolution.TelescopeSlice
  PhotochemistrySolution.EvenOctB70
open PhotochemistrySolution.ScreenFermatCore PhotochemistrySolution.PopBernstein
open _root_.QuantumComputation.Specs.PhotochemistrySolution.PotOracleGen (openCoordDistSq)
attribute [local irreducible] systemQubits_frozen
def fnEE30 (y : ℕ) : ℕ := y >>> 6
def fnNN30 (y : ℕ) : ℕ := y >>> 5
def fnEN9_30 (y : ℕ) : ℕ := (y >>> 6) + (y >>> 3)
def fnEN10_30 (y : ℕ) : ℕ := (y >>> 5) + (y >>> 3)
def fnEN30 (sp : Fin 4) (y : ℕ) : ℕ := (if sp == 1 then y >>> 5 else y >>> 6) + (y >>> 3)
/-- GMP `O(1)`-depth `|v| ≤ 2^29` cap check (`536,870,912`). -/
def chkCap29Fast (v : ℤ) : Bool := zLeB (-536870912) v && zLeB v 536870912
theorem chkCap29Fast_abs {v : ℤ} (h : chkCap29Fast v = true) : |v| ≤ 536870912 := by
  unfold chkCap29Fast at h
  simpa only [Bool.and_eq_true, zLeB_eq_true, ← abs_le] using h
theorem shr_mono_nat {a b : ℕ} (h : a ≤ b) (s : ℕ) : a >>> s ≤ b >>> s := by
  simpa only [Nat.shiftRight_eq_div_pow] using Nat.div_le_div_right h
theorem fnEN30_mono {a b : ℕ} (h : a ≤ b) (sp : Fin 4) : fnEN30 sp a ≤ fnEN30 sp b := by
  have : a >>> 3 ≤ b >>> 3 ∧ a >>> 5 ≤ b >>> 5 ∧ a >>> 6 ≤ b >>> 6 :=
      ⟨shr_mono_nat h 3, shr_mono_nat h 5, shr_mono_nat h 6⟩
  unfold fnEN30
  split_ifs <;> omega
theorem cap29_of_mono {z zlo zhi off : ℤ} (hlo : zlo ≤ z) (hhi : z ≤ zhi)
    (h1 : chkCap29Fast (zlo - off) = true)
    (h2 : chkCap29Fast (zhi - off) = true) :
    |z - off| ≤ 536870912 := by
  exact abs_le.mpr ⟨(abs_le.mp (chkCap29Fast_abs h1)).1.trans (Int.sub_le_sub_right hlo off),
    (Int.sub_le_sub_right hhi off).trans (abs_le.mp (chkCap29Fast_abs h2)).2⟩
end QuantumComputation.Specs.PhotochemistrySolution.ZHi30

namespace QuantumComputation.Specs.PhotochemistrySolution.PotOraclePortB
open Circuit Qubit PrimitiveGate QuantumComputation.Specs PhotochemistrySolution.SubspaceMbu
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
open PhotochemistrySolution.ZeroNEremSpec PhotochemistrySolution.QubitizationWalkSem
  PhotochemistrySolution.SplitBellVecCleanStep
open _root_.DynamicCircuit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt hiding bit_cases
  eval_seq_mulVec ket ket_CNOT ket_TOFF ket_X ket_projector_one ket_projector_zero localIdx
  matrix_ext_ket qAssign_obs_map_val
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt (writeReg writeReg_apply_reg
  writeReg_apply_of_not_mem)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.PotOracleGen
  (subspaceStep_wrapOnReg_vprog2 writeReg_zero_prefix_pairStep writeReg_upd_prefix_pairStep)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB (ket matrix_ext_ket)
attribute [local semireducible] remeasureIf projBit chunkXorOp
theorem subspaceStep_seq_portB {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    {R₀ R₁ R₂ : Operator (2 ^ n)}
    {p₁ p₂ : DynamicCircuit Var n} (s₁ : SubspaceStep R₀ R₁ p₁) (s₂ : SubspaceStep R₁ R₂ p₂) :
    SubspaceStep R₀ R₂ (.seq p₁ p₂) := fun ψ ↦ by
  obtain ⟨N₂, h₂, e₂⟩ := s₂ ψ
  obtain ⟨N₁, h₁, e₁⟩ := s₁ N₂
  refine ⟨N₁, ?_, e₂.trans e₁⟩
  dsimp only [DynamicCircuit.compile, wp, qSeq]
  rw [h₂, h₁]

theorem subspaceStep_cnot_mkKetOpW {Var : Type} [Fintype Var] [DecidableEq Var] {W n : ℕ}
    [NeZero (2 ^ n)]
    (rWork : QRegister W n) (c t : Wire n) (hct : c ≠ t)
    (st : BitAssignment n → BitAssignment n) (ph : BitAssignment n → ZMod 2) :
        SubspaceStep (mkKetOpW rWork st ph)
      (mkKetOpW rWork (fun δ ↦ Function.update (st δ) t (st δ t + st δ c)) ph)
      (.circuit (Var := Var) (.CNOT c t hct)) :=
  subspaceStep_congr_out (subspaceStep_of_circuit (Var := Var) (mkKetOpW rWork st ph)
      (.CNOT c t hct))
    (matrix_ext_ket fun δ ↦ by
      rw [← Matrix.mulVec_mulVec, mkKetOpW_mulVec_ket, mkKetOpW_mulVec_ket]
      split_ifs with hz
      · rw [Matrix.mulVec_smul, PhotochemistrySolution.KinB.ket_CNOT]
      · rw [Matrix.mulVec_zero])

theorem blk24_not_mem {m n : ℕ} (r : QRegister m n) (b : ℕ) (hb : b + 24 ≤ m) (c : ℕ) (hc : c < m)
    (hd : c < b ∨ b + 24 ≤ c) : ¬∃ j : Fin 24, (r.compose (QRegister.block b 24 hb)) j = r ⟨c, hc⟩
    :=
  fun ⟨j, hj⟩ ↦ by
    have hv : b + j.val = c := congrArg Fin.val (r.wires.injective hj)
    omega

theorem blk24_disj {m n : ℕ} (r : QRegister m n) (a b : ℕ) (ha : a + 24 ≤ m) (hb : b + 24 ≤ m)
    (hd : a + 24 ≤ b ∨ b +
  24 ≤ a) (j : Fin 24) :
    ¬∃ q : Fin 24, (r.compose (QRegister.block b 24 hb)) q =
        (r.compose (QRegister.block a 24 ha)) j :=
  fun ⟨q, hq⟩ ↦
      blk24_not_mem r b hb (a + j.val) (by omega) (by omega)
      ⟨q, hq.trans (congrArg r.wires (Fin.ext rfl))⟩

theorem subspaceStep_mul_right {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    {A B : Operator (2 ^ n)}
    {d : DynamicCircuit Var n} (X : Operator (2 ^ n))
    (h : SubspaceStep A B d) : SubspaceStep (A * X) (B * X) d :=
  fun M ↦ let ⟨N, hwp, hm⟩ := h M
    ⟨N, hwp,
        by simpa only [Matrix.conjTranspose_mul, Matrix.mul_assoc] using congrArg (fun Z ↦ Xᴴ *
             (Z * X)) hm⟩

theorem circWires_czPairsCircuit {n : ℕ} {S : Wire n → Prop} : ∀ (pairs : List (WirePair n)),
    (∀ p ∈ pairs, S p.1 ∧
  S p.2.1) → CircWires S (czPairsCircuit pairs)
  | [], _ => trivial
  | p :: ps, hS =>
      let ⟨hp1, hp2⟩ := hS p List.mem_cons_self
      ⟨⟨fun _ ↦ hp2, fun i ↦ match i with | ⟨0, _⟩ => hp1 | ⟨1, _⟩ => hp2, fun _ ↦ hp2⟩,
        circWires_czPairsCircuit ps fun q hq ↦ hS q (List.mem_cons_of_mem p hq)⟩

theorem dynWires_xUnloadChunkCzPairsSeqDyn {Var : Type} {n : ℕ} {S : Wire n → Prop} (v : Var)
    (rOut : ℕ → Wire n)
    (ofs : ℕ) (pairsFn : ℕ → List (WirePair n)) (rest : DynamicCircuit Var n)
        (hRest : DynWires S rest) :
    ∀ k : ℕ, (∀ i < k, S (rOut (ofs + i))) → (∀ i < k, ∀ p ∈ pairsFn i, S p.1 ∧ S p.2.1) →
        DynWires S
      (xUnloadChunkCzPairsSeqDyn v rOut ofs pairsFn rest k)
  | 0, _, _ => hRest
  | j + 1, hOut, hP =>
      ⟨fun _ ↦ hOut j (Nat.lt_succ_self j), ⟨fun _ ↦ hOut j (Nat.lt_succ_self j),
          ⟨⟨fun _ ↦ hOut j (Nat.lt_succ_self j),
        circWires_czPairsCircuit (pairsFn j) (hP j (Nat.lt_succ_self j))⟩, trivial⟩⟩,
       dynWires_xUnloadChunkCzPairsSeqDyn v rOut ofs pairsFn rest hRest j
         (fun i hi ↦ hOut i (Nat.lt_succ_of_lt hi)) (fun i hi ↦ hP i (Nat.lt_succ_of_lt hi))⟩

theorem packUnpack_b {W j : ℕ} (h24 : 24 ≤ W) (hj : j < 24) : 4 < 122 + W ∧ 57 + j < 122 + W ∧ 122 +
    j < 122 + W ∧
    0 < 122 + W ∧
    122 + j ≠ 57 + j ∧ 4 ≠ 57 + j ∧ 57 + j ≠ 122 + j ∧ 4 ≠ 122 + j := by omega
theorem potWrapSub_le {Wp W : ℕ} (hW : Wp ≤ W) : 0 + (122 + Wp) ≤ 122 + W := by omega

/-- `0-T` CNOT ladder `CNOT(r[122+b], r[57+b])` across `b < k ≤ 24`. -/
def cPackCnotAux {n W : ℕ} (r : QRegister (122 + W) n) (h24 : 24 ≤ W) : ∀ k : ℕ, k ≤ 24 → Circuit n
  | 0, _ => .identity
  | j + 1, hj =>
      let hb := packUnpack_b h24 hj
      .seq (cPackCnotAux r h24 j (Nat.le_of_succ_le hj))
        (Circuit.CNOT (r ⟨122 + j, hb.2.2.1⟩) (r ⟨57 + j, hb.2.1⟩)
            (r.wires.injective.ne (fun e ↦ hb.2.2.2.2.1 (congrArg Fin.val e))))

theorem cPackCnotAux_spec {n W : ℕ} [NeZero (2 ^ n)] (r : QRegister (122 + W) n)
    (h24 : 24 ≤ W) : ∀ (k : ℕ) (hk : k ≤
  24), (∀ β : BitAssignment n, (cPackCnotAux r h24 k hk).eval.1.mulVec (ket β) =
        ket (writeReg β (r.compose (QRegister.block 57 24 (by omega)))
          (fun b ↦ if b.val < k then β (r ⟨57 + b.val, by omega⟩) + β (r ⟨122 + b.val, by omega⟩)
                   else β (r ⟨57 + b.val, by omega⟩)))) ∧
      (cPackCnotAux r h24 k hk).count .T = 0 ∧ (cPackCnotAux r h24 k hk).count .TOFF = 0 ∧
          (∀ S : Wire n → Prop, (∀ u, S
        (r u)) → CircWires S (cPackCnotAux r h24 k hk))
  | 0, _ => ⟨fun β ↦ by
      dsimp only [cPackCnotAux]
      rw [Circuit.eval_identity, Submonoid.coe_one, Matrix.one_mulVec]
      exact congrArg ket (Eq.symm (writeReg_zero_prefix_pairStep _ β _ _ fun _ ↦
        congrArg β (congrArg r.wires (Fin.ext rfl)))), rfl, rfl, fun _ _ ↦ trivial⟩
  | j + 1, hj => by
      obtain ⟨hKet, hT, hF, hW⟩ := cPackCnotAux_spec r h24 j (Nat.le_of_succ_le hj)
      refine ⟨fun β ↦ ?_, by simp [cPackCnotAux, hT], by simp [cPackCnotAux, hF],
        fun S hr ↦ ⟨hW S hr, fun | ⟨0, _⟩ => hr _ | ⟨1, _⟩ => hr _⟩⟩
      let rE := r.compose (QRegister.block 57 24 (by omega))
      dsimp only [cPackCnotAux]
      rw [DynCircExt.eval_seq_mulVec, hKet β]
      change (Circuit.CNOT _ _ _).eval.1.mulVec (DynCircExt.ket _) = _
      rw [DynCircExt.ket_CNOT]
      rw [show writeReg β rE _ (r ⟨122 + j, by omega⟩) = β (r ⟨122 + j, by omega⟩) from
          writeReg_apply_of_not_mem _ _ _ _ (blk24_not_mem r 57 _ (122 + j) (by omega) (by omega)),
        show r ⟨57 + j, by omega⟩ = rE ⟨j, hj⟩ from congrArg r.wires (Fin.ext rfl),
        writeReg_apply_reg, ite_eq_right (Nat.lt_irrefl _)]
      exact congrArg ket (writeReg_upd_prefix_pairStep rE β _ _ hj)

theorem oneHot_pack_unpack_bits : ∀ (nn e n : ZMod 2), ((nn = 0 → n = 0) ∧ (nn = 1 → e = 0)) →
      let p := e + n
      n = nn * p ∧ p + nn * p = e := by decide

attribute [local irreducible] systemQubits_frozen SelectCompactAnc.ancWOfScr

theorem chunkXorOp_mkKetOpW_eq {n W m : ℕ} [NeZero (2 ^ n)] (rW : QRegister m n)
    (r : QRegister (122 + W) n) (h24 : 24 ≤
  W) (stP : BitAssignment n → BitAssignment n)
    (hZero : ∀ δ (b : Fin 24), stP δ (r ⟨122 + b.val, by omega⟩) = 0) :
    let rOut : ℕ → Wire n := fun i ↦ if hi : i < 24 then r ⟨122 + i, by omega⟩ else r ⟨0, by omega⟩
    let pairsFn : ℕ → List (WirePair n) := fun i ↦ if hi : i < 24 then
      ⟨r ⟨4, by omega⟩, ⟨r ⟨57 + i, by omega⟩,
        r.wires.injective.ne (fun e ↦ (by omega : 4 ≠ 57 + i) (congrArg Fin.val e))⟩⟩ :: []
      else []
    let bitFn : ℕ → BitAssignment n → ZMod 2 := fun i β ↦ czPairsParity (pairsFn i) β
    have hf : ∀ i β a, bitFn i (Function.update β (rOut (0 + i)) a) = bitFn i β := fun i β a ↦ by
      dsimp only [bitFn, pairsFn, rOut]
      rw [Nat.zero_add]
      split_ifs with hi
      · exact czPairsParity_indep _ _ (fun p hp ↦ by
          rw [List.mem_singleton.mp hp]
          exact ⟨r.wires.injective.ne (fun e ↦ (by omega : 4 ≠ 122 + i) (congrArg Fin.val e)),
              r.wires.injective.ne
            (fun e ↦ (by omega : 57 + i ≠ 122 + i) (congrArg Fin.val e))⟩) β a
      · rfl
    ∀ (k : ℕ) (_hk : k ≤ 24),
      chunkXorOp rOut 0 bitFn hf k * mkKetOpW rW stP (fun _ ↦ 0) =
        mkKetOpW rW (fun δ ↦ writeReg (stP δ) (r.compose (QRegister.block 122 24 (by omega)))
          (fun b ↦ if b.val < k then stP δ (r ⟨4, by omega⟩) * stP δ (r ⟨57 + b.val, by omega⟩)
                   else 0)) (fun _ ↦ 0) := by
  intro rOut pairsFn bitFn hf k hk
  induction k with
  | zero =>
      simpa only [chunkXorOp, Matrix.one_mul] using mkKetOpW_congr rW (fun δ _ ↦
        (writeReg_zero_prefix_pairStep _ (stP δ) _ _ fun b ↦
          ((congrArg (stP δ) (congrArg r.wires (Fin.ext rfl))).trans (hZero δ b)).symm).symm)
              (fun _ _ ↦ rfl)
  | succ j ih =>
      dsimp only [chunkXorOp]
      rw [Matrix.mul_assoc, ih (Nat.le_of_succ_le hk)]
      refine matrix_ext_ket fun δ ↦ by
        rw [← Matrix.mulVec_mulVec, mkKetOpW_mulVec_ket, mkKetOpW_mulVec_ket]
        split_ifs with hz
        · let rN := r.compose (QRegister.block 122 24 (by omega))
          rw [bitSign_zero, one_smul, one_smul, xorWireUnitary_mulVec_ket,
            show bitFn j (writeReg (stP δ) rN _) = stP δ (r ⟨4, by omega⟩) *
                stP δ (r ⟨57 + j, by omega⟩) by
              dsimp only [bitFn, pairsFn]
              rw [dite_eq_left (show j < 24 from hk)]
              dsimp only [czPairsParity]
              rw [add_zero, writeReg_apply_of_not_mem _ _ _ _ (blk24_not_mem r 122 _ 4 (by omega)
                  (by omega)),
                writeReg_apply_of_not_mem _ _ _ _ (blk24_not_mem r 122 _ (57 + j) (by omega)
                    (by omega))],
            show rOut (0 + j) = rN ⟨j, hk⟩ by
              dsimp only [rOut]
              rw [Nat.zero_add, dite_eq_left (show j < 24 from hk)]
              exact congrArg r.wires (Fin.ext rfl),
            writeReg_apply_reg, ite_eq_right (Nat.lt_irrefl _), zero_add]
          exact congrArg ket (writeReg_upd_prefix_pairStep rN (stP δ) _ _ hk)
        · exact Matrix.mulVec_zero _

theorem packPortBSt_b {W : ℕ} (h24 : 24 ≤ W) : 57 + 24 ≤ 122 + W ∧ 122 + 24 ≤ 122 + W := by omega
/-- Packed state storing `st0[57+b] + st0[122+b]` on `[57..80]` and `0` on `[122..145]`. -/
def packPortBSt {n W : ℕ} (r : QRegister (122 + W) n) (h24 : 24 ≤ W)
    (st0 : BitAssignment n → BitAssignment n) (δ : BitAssignment n) : BitAssignment n :=
  writeReg (writeReg (st0 δ) (r.compose (QRegister.block 57 24 (packPortBSt_b h24).1))
      (fun b ↦ st0 δ (r ⟨57 + b.val, (packUnpack_b h24 b.isLt).2.1⟩) +
      st0 δ (r ⟨122 + b.val, (packUnpack_b h24 b.isLt).2.2.1⟩)))
    (r.compose (QRegister.block 122 24 (packPortBSt_b h24).2)) (fun _ ↦ 0)

theorem packPortBSt_props {n W : ℕ} (r : QRegister (122 + W) n) (h24 : 24 ≤ W)
    (st0 : BitAssignment n →
  BitAssignment n) :
    (∀ δ (b : Fin 24), packPortBSt r h24 st0 δ (r ⟨122 + b.val, by omega⟩) = 0) ∧
    (∀ δ, packPortBSt r h24 st0 δ (r ⟨4, by omega⟩) = st0 δ (r ⟨4, by omega⟩)) ∧
    (∀ δ (b : Fin 24), packPortBSt r h24 st0 δ (r ⟨57 + b.val, by omega⟩) =
      st0 δ (r ⟨57 + b.val, by omega⟩) + st0 δ (r ⟨122 + b.val, by omega⟩)) := by
  exact ⟨fun δ b ↦ (congrArg _ (congrArg r.wires (Fin.ext rfl))).trans
      (writeReg_apply_reg _ (r.compose (QRegister.block 122 24 _)) _ b),
    fun δ ↦
        (writeReg_apply_of_not_mem _ _ _ _ (blk24_not_mem r 122 _ 4 (by omega) (by omega))).trans
      (writeReg_apply_of_not_mem _ _ _ _ (blk24_not_mem r 57 _ 4 (by omega) (by omega))),
    fun δ b ↦
        (writeReg_apply_of_not_mem _ _ _ _ (blk24_not_mem r 122 _ (57 + b.val) (by omega)
        (by omega))).trans
      ((congrArg _ (congrArg r.wires (Fin.ext rfl))).trans (writeReg_apply_reg _ (r.compose
          (QRegister.block 57 24 _)) _ b))⟩
end QuantumComputation.Specs.PhotochemistrySolution.PotOraclePortB

namespace QuantumComputation.Specs.PhotochemistrySolution.PotPortBMux
open Circuit Qubit PhotochemistrySolution.SelectStructuredCB
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt (writeReg writeReg_apply_reg
  writeReg_apply_of_not_mem)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.PotOracleGen (disj_ne openCoordDistSq
    subspaceStep_wrapOnReg_vprog2)
theorem sbScr_lt6 {kScr : ℕ} (h6 : 6 ≤ kScr) (j : Fin 6) : j.val < kScr :=
    Nat.lt_of_lt_of_le j.isLt h6
theorem sb48_a_le (kScr : ℕ) : 0 + 24 ≤ 48 + kScr := by omega
theorem sb48_b_le (kScr : ℕ) : 24 + 24 ≤ 48 + kScr := by omega
theorem sb48_in_lt (kScr : ℕ) (u : Fin 48) : u.val < 48 + kScr := by omega
theorem sb48_out_lt {kScr : ℕ} (h6 : 6 ≤ kScr) (j : Fin 6) : 48 + j.val < 48 + kScr := by omega
theorem sb48_sub24 {m : ℕ} (h1 : ¬ m < 24) (h2 : m < 48) : m - 24 < 24 := by omega
theorem sb48_sub48 {kScr m : ℕ} (h1 : ¬ m < 48) (h2 : m < 48 + kScr) : m - 48 < kScr := by omega

/-- `48 + kScr`-wire register map `rA ++ rB ++ rScr` for `ShortBin7Pkg.ofComputeProg`. -/
def fReg48Plus {kScr n : ℕ} (rA rB : QRegister 24 n) (rScr : QRegister kScr n)
    (u : Wire (48 + kScr)) : Wire n :=
  if h1 : u.val < 24 then rA ⟨u.val, h1⟩
  else if h2 : u.val < 48 then rB ⟨u.val - 24, sb48_sub24 h1 h2⟩
  else rScr ⟨u.val - 48, sb48_sub48 h2 u.isLt⟩

theorem fReg48Plus_injective {kScr n : ℕ} (rA rB : QRegister 24 n) (rScr : QRegister kScr n)
    (hAB : rA.DisjointWires rB)
    (hAS : rA.DisjointWires rScr) (hBS : rB.DisjointWires rScr) :
    Function.Injective (fReg48Plus rA rB rScr) := fun u v heq ↦ by
  dsimp [fReg48Plus] at heq
  split_ifs at heq <;> try first
    | exact absurd heq (disj_ne hAB _ _) | exact absurd heq.symm (disj_ne hAB _ _)
    | exact absurd heq (disj_ne hAS _ _) | exact absurd heq.symm (disj_ne hAS _ _)
    | exact absurd heq (disj_ne hBS _ _) | exact absurd heq.symm (disj_ne hBS _ _)
  · exact Fin.ext (Fin.mk.inj (rA.wires.injective heq))
  · have : u.val - 24 = v.val - 24 := congrArg Fin.val (rB.wires.injective heq)
    exact Fin.ext (by omega)
  · have : u.val - 48 = v.val - 48 := congrArg Fin.val (rScr.wires.injective heq)
    exact Fin.ext (by omega)

theorem fReg48Plus_coords {kScr n : ℕ} (rA rB : QRegister 24 n) (rScr : QRegister kScr n)
    (hinj : Function.Injective
  (fReg48Plus rA rB rScr)) (s : BitAssignment n) :
    let r48k : QRegister (48 + kScr) n := ⟨⟨fReg48Plus rA rB rScr, hinj⟩⟩
    coordOfReg24 (QRegister.block 0 24 (sb48_a_le kScr)) (fun q ↦ s (r48k q)) = coordOfReg24 rA s ∧
    coordOfReg24 (QRegister.block 24 24 (sb48_b_le kScr)) (fun q ↦ s (r48k q)) =
        coordOfReg24 rB s := by
  refine ⟨funext fun ax ↦ congrArg _ (funext fun k ↦ congrArg s ?_),
    funext fun ax ↦ congrArg _ (funext fun k ↦ congrArg s ?_)⟩
  · exact (dite_eq_left (by omega : 0 + (8 * ax.val + k.val) < 24)).trans (congrArg rA.wires
        (Fin.ext (Nat.zero_add _)))
  · exact (dite_eq_right (by omega : ¬ 24 + (8 * ax.val + k.val) < 24)).trans
      ((dite_eq_left (by omega : 24 + (8 * ax.val + k.val) < 48)).trans
        (congrArg rB.wires (Fin.ext (Nat.add_sub_cancel_left 24 _))))

theorem cDitePos {P : Prop} (inst : Decidable P) {α : Sort*} (h : P) {a : P → α}
    {b : ¬ P → α} : @dite α P inst a b =
    a h := @dite_eq_left P inst h α a b

/--
Universal two-state (`st -> stPost`) `wrapDynOnReg` lemma on a trailing scratch/output block
`B .. B + L - 1` (`B + L = K`) with `0` reverse `T` gates (`0` `.TOFF`).
-/
theorem subspaceStep_wrapOnReg_block2 {Var : Type} [Fintype Var] [DecidableEq Var] {W B L K n : ℕ}
    [NeZero (2 ^ n)]
    (hBL : B + L ≤ K) (hBK : B + L = K) (hIdx : ∀ j : Fin L, B + j.val < K) (v : Var)
    (rWork : QRegister W n) (r : QRegister K n) (sMask : ℕ) (cp : ComputeProg K) (nAnd tCost : ℕ)
      (hValid : StructuredCB.validProgMask 0 sMask cp = true) (hAnd : cp.numAnd = nAnd)
          (htCost : 4 * nAnd = tCost)
    (st stPost : BitAssignment n → BitAssignment n) (phPre phPost : BitAssignment n → ZMod 2)
      (mid : DynamicCircuit Var n) (hMaskCln : ∀ u : Wire K, sMask.testBit u.val = true →
          ∀ δ : BitAssignment n,
      (∀ q : Fin W, δ (rWork q) = 0) → st δ (r u) = 0) (hSame : ∀ (δ : BitAssignment n)
          (u : Fin K), (∀ q : Fin W, δ
        (rWork q) = 0) → stPost δ (r u) = st δ (r u))
    (hKeepLt : ∀ (δ : BitAssignment n), (∀ q : Fin W, δ (rWork q) = 0) → ∀ u : Wire K, u.val < B →
        cp.fwdBits
      (fun q ↦ st δ (r q)) u = st δ (r u)) (hMid : ∀ stMid : BitAssignment n → BitAssignment n,
      (∀ (δ : BitAssignment n) (w : Wire n), (∀ j : Fin L, w ≠ r ⟨B + j.val, hIdx j⟩) → stMid δ w =
          st δ w) → (∀
        (δ : BitAssignment n) (u : Wire K), (∀ q : Fin W, δ (rWork q) = 0) →
        stMid δ (r u) = cp.fwdBits (fun q ↦ st δ (r q)) u) →
            SubspaceStep (mkKetOpW rWork stMid phPre) (mkKetOpW rWork
          (fun δ ↦ writeReg (stPost δ) (r.compose (QRegister.block B L hBL))
          (fun j ↦ stMid δ (r ⟨B + j.val, hIdx j⟩))) phPost) mid) :
              SubspaceStep (mkKetOpW rWork st phPre)
            (mkKetOpW rWork stPost phPost) (wrapDynOnReg v r cp mid) ∧
              (wrapDynOnReg v r cp mid).count .T = tCost + mid.count .T ∧
    (wrapDynOnReg v r cp mid).count .TOFF = mid.count .TOFF ∧ (∀ S : Wire n → Prop, (∀ u, S (r u)) →
        DynWires S mid →
      DynWires S (wrapDynOnReg v r cp mid)) := by
  let stMid : BitAssignment n → BitAssignment n :=
    fun δ ↦
        @ite _ (∀ q : Fin W, δ (rWork q) =
        0) Fintype.decidableForallFintype (stepCB r cp.fwdBits (st δ)) (st δ)
  have hMidKeep (δ : BitAssignment n) (w : Wire n) (hw : ∀ j : Fin L, w ≠ r ⟨B + j.val, hIdx j⟩) :
      stMid δ w = st δ w := by
    dsimp only [stMid]
    by_cases hz : ∀ q : Fin W, δ (rWork q) = 0
    · rw [@ite_eq_left _ Fintype.decidableForallFintype hz _ _ _]
      by_cases hex : ∃ u : Fin K, r u = w
      · obtain ⟨u, rfl⟩ := hex
        rw [stepCB, writeReg_apply_reg]
        exact if hlt : u.val < B then hKeepLt δ hz u hlt
          else absurd (congrArg r.wires (Fin.ext (Nat.add_sub_of_le (Nat.le_of_not_lt hlt)).symm))
              (hw ⟨u.val - B, by omega⟩)
      · exact writeReg_apply_of_not_mem _ _ _ _ hex
    · exact congrFun (@ite_eq_right _ Fintype.decidableForallFintype hz _ _ _) w
  have hMidVal (δ : BitAssignment n) (u : Wire K) (hz : ∀ q : Fin W, δ (rWork q) = 0) :
      stMid δ (r u) = cp.fwdBits (fun q ↦ st δ (r q)) u := by
    dsimp only [stMid, stepCB]
    rw [@ite_eq_left _ Fintype.decidableForallFintype hz _ _ _, writeReg_apply_reg]
  have hPreEq : mkKetOpW rWork (fun δ ↦ stepCB r cp.fwdBits (st δ)) phPre =
      mkKetOpW rWork stMid phPre :=
    mkKetOpW_congr rWork (fun _ hz ↦ (@ite_eq_left _ Fintype.decidableForallFintype hz _ _ _).symm)
        (fun _ _ ↦ rfl)
  have hPostEq : mkKetOpW rWork (fun δ ↦ stepCB r cp.fwdBits (stPost δ)) phPost =
      mkKetOpW rWork (fun δ ↦ writeReg (stPost δ) (r.compose (QRegister.block B L hBL))
        (fun j ↦ stMid δ (r ⟨B + j.val, hIdx j⟩))) phPost :=
    mkKetOpW_congr rWork (fun δ hz ↦ funext fun w ↦ by
      let rBlk := r.compose (QRegister.block B L hBL)
      dsimp only [stepCB]
      rw [show (fun q : Fin K ↦ stPost δ (r q)) = fun q : Fin K ↦ st δ (r q) from funext fun q ↦
          hSame δ q hz]
      by_cases hex : ∃ u : Fin K, r u = w
      · obtain ⟨u, rfl⟩ := hex
        rw [writeReg_apply_reg]
        by_cases hlt : u.val < B
        · rw [hKeepLt δ hz u hlt, writeReg_apply_of_not_mem _ rBlk _ _ (fun ⟨j, hj⟩ ↦ by
            have : B + j.val = u.val := congrArg Fin.val (r.wires.injective hj)
            omega), hSame δ u hz]
        · let j : Fin L := ⟨u.val - B, by omega⟩
          rw [show r u =
              rBlk j from congrArg r.wires (Fin.ext (Nat.add_sub_of_le (Nat.le_of_not_lt
              hlt)).symm),
            writeReg_apply_reg, show (⟨B + j.val, hIdx j⟩ : Wire K) = u from
              Fin.ext (Nat.add_sub_of_le (Nat.le_of_not_lt hlt)), hMidVal δ u hz]
      · rw [writeReg_apply_of_not_mem _ _ _ _ hex,
          writeReg_apply_of_not_mem _ _ _ _ fun ⟨j, hj⟩ ↦
              hex ⟨QRegister.block B L hBL j, hj⟩]) (fun _ _ ↦ rfl)
  obtain ⟨h1, h2, h3, h4⟩ := subspaceStep_wrapOnReg_vprog2 v rWork r (maskFinset K sMask) cp nAnd
    (maskFinset_zero K ▸ StructuredCB.validProg_of_validProgMask hValid) hAnd st stPost phPre phPost
        mid
    (fun u hu δ hz ↦ hMaskCln u (mem_maskFinset.mp hu) δ hz)
    (fun u hu δ hz ↦ (hSame δ u hz).trans (hMaskCln u (mem_maskFinset.mp hu) δ hz))
    (hPreEq ▸ hPostEq ▸ hMid stMid hMidKeep hMidVal)
  exact ⟨h1, h2.trans (htCost ▸ rfl), h3, h4⟩

/-- Constructive MBU wrapper around `cp : ComputeProg (48 + kScr)` on `rA ++ rB ++ rScr`. -/
def wrapShortBin7OfCP {kScr : ℕ} (cp : ComputeProg (48 + kScr)) {Var : Type} {n : ℕ} (v : Var)
    (rA rB : QRegister 24 n) (rScr : QRegister kScr n) (mid : DynamicCircuit Var n) :
    DynamicCircuit Var n :=
  @dite _ (Function.Injective (fReg48Plus rA rB rScr))
      (Fintype.decidableInjectiveFintype (fReg48Plus rA rB rScr))
    (fun hinj ↦ wrapDynOnReg v ⟨⟨fReg48Plus rA rB rScr, hinj⟩⟩ cp mid) (fun _ ↦ mid)
end QuantumComputation.Specs.PhotochemistrySolution.PotPortBMux

namespace QuantumComputation.Specs.PhotochemistrySolution.Dist18QuadUnld
open Circuit Qubit QuantumComputation.Specs PhotochemistrySolution.SelectStructuredCB
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
open PhotochemistrySolution.SelectFastFlags PhotochemistrySolution.Stage4Cluster22Xnor
  PhotochemistrySolution.ZeroNEremSpec
open _root_.DynamicCircuit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt hiding bit_cases ket ket_CNOT
  ket_TOFF ket_X ket_projector_one ket_projector_zero localIdx matrix_ext_ket qAssign_obs_map_val
  writeReg writeReg_apply_of_not_mem writeReg_apply_reg
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB hiding bitSign ket ket_CNOT
  ket_TOFF ket_X localIdx matrix_ext_ket writeReg writeReg_apply_of_not_mem writeReg_apply_reg
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt (writeReg writeReg_apply_reg
  writeReg_apply_of_not_mem matrix_ext_ket)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.PotOracleGen (openCoordDistSq disj_ne
    disj_of_ne stepCB_writeReg_comm subspaceStep_wrapOnReg_vprog2 writeReg_zero_prefix_pairStep
    writeReg_upd_prefix_pairStep)
attribute [local semireducible] remeasureIf projBit chunkXorOp
/-- Axis-0 token list with `(2, [], true)` folded into `(2, [26], false)` (`poolSum` invariant). -/
def axTokens0_ha : List DToken :=
  [(0, [24], true), (2, [58], false), (8, [57], true), (2, [26], true), (3, [26], false)] ++
  ((List.range 5).map fun k => (k + 3, [24 + (k + 3)], false)) ++
  ((List.range 8).map fun k => (k + 8, [24 + k, 57], false)) ++
  (((List.range 8).flatMap fun i => ((List.range 8).map fun j => (i, j))).filterMap fun ij =>
      if ij.1 < ij.2 /\ ¬ (ij.1 = 0 /\ ij.2 = 1) then some (ij.1 + ij.2, [24 + ij.1, 24 + ij.2],
      true) else none)
/-- `135`-token initial Dadda pool with `(2, [], true)` folded into `axTokens0_ha`. -/
def initTokens128 : List DToken :=
    axTokens0_ha ++ axTokens 1 ++ axTokens 2 ++ [(16, [], true), (17, [], true)]

theorem axTokens0_split_eq : axTokens 0 = [(0, [24], true), (2, [58], false), (8, [57], true),
    (2, [26],
  false)] ++ axTokens0_ha.drop 5 ∧
    axTokens0_ha = [(0, [24], true), (2, [58], false), (8, [57], true), (2, [26], true),
        (3, [26], false)] ++
      axTokens0_ha.drop 5 := by decide +kernel

theorem poolSum_axTokens0_ha (γ0 : BitAssignment 304) : poolSum axTokens0_ha γ0 =
    poolSum (axTokens 0) γ0 + 4 := by
  obtain ⟨h0, hha⟩ := axTokens0_split_eq
  rw [hha, h0, poolSum_append, poolSum_append]
  have := (by decide : ∀ x : ZMod 2, ((1 + (x + 0) : ZMod 2)).val * 2 ^ 2 +
    ((0 + (x + 0) : ZMod 2)).val * 2 ^ 3 = ((0 + (x + 0) : ZMod 2)).val * 2 ^ 2 + 4) (γ0 (w304 26))
  simp only [poolSum, List.foldr, tokBit, Bool.false_eq_true, ↓reduceIte]
  omega

theorem poolSum_initTokens128_eq (γ0 : BitAssignment 304) : poolSum initTokens128 γ0 =
    poolSum initTokens γ0 := by
  have h2 : poolSum [(2, [], true), (16, [], true), (17, [], true)] γ0 =
      4 + poolSum [(16, [], true), (17, [], true)] γ0 := by
    simp only [poolSum, List.foldr, tokBit, ↓reduceIte, add_zero, show ((1 : ZMod 2)).val =
        1 from rfl]
    omega
  simp only [initTokens128, initTokens, poolSum_append, poolSum_axTokens0_ha, h2]
  omega

theorem inNatList_append_quad (a : ℕ) (xs ys : List ℕ) :
    inNatList a (xs ++ ys) = (inNatList a xs || inNatList a ys) := by
  induction xs with
  | nil => simp [inNatList]
  | cons _ _ ih => simp [List.cons_append, inNatList, ih, Bool.or_assoc]

theorem testBit_eq_decide_div_mod : ∀ (x k : ℕ), x.testBit k = decide ((x / 2 ^ k) % 2 = 1)
  | x, 0 => by rw [Nat.testBit_zero, Nat.pow_zero, Nat.div_one]
  | x, k + 1 => by
      rw [Nat.testBit_succ, testBit_eq_decide_div_mod (x / 2) k, Nat.div_div_eq_div_mul,
          Nat.pow_succ, Nat.mul_comm 2 (2 ^ k)]

theorem horner_init (N s0 r2 : ℕ) (hN : N = s0 + 4 * r2) (hs0 : s0 < 4) :
    (N / 1) % 2 = s0 % 2 ∧ (N / 2) % 2 = (s0 / 2) % 2 ∧ N / 4 = r2 :=
        hN ▸ ⟨by omega, by omega, by omega⟩

def outWireOfRegQuad {B n : ℕ} (hB : 0 < B) (rOut : QRegister B n) (j : ℕ) : Wire n :=
    rOut ⟨j % B, Nat.mod_lt j hB⟩

theorem circWires_czPairs_quad {n : ℕ} {S : Wire n → Prop} : ∀ (pairs : List (WirePair n)),
    (∀ p ∈ pairs, S p.1 ∧
  S p.2.1) → CircWires S (czPairsCircuit pairs) := PotOraclePortB.circWires_czPairsCircuit

theorem dynWires_xUnloadChunk_quad {Var : Type} {n : ℕ} {S : Wire n → Prop} (v : Var)
    (rOut : ℕ → Wire n) (ofs : ℕ)
    (pairsFn : ℕ → List (WirePair n)) (hOut : ∀ i, S (rOut i))
        (hPairs : ∀ j p, p ∈ pairsFn j → S p.1 ∧ S p.2.1) :
    ∀ k : ℕ, DynWires S (xUnloadChunkCzPairsSeqDyn v rOut ofs pairsFn (.circuit .identity) k)
  | k =>
      PotOraclePortB.dynWires_xUnloadChunkCzPairsSeqDyn v rOut ofs pairsFn (.circuit .identity)
        trivial k (fun i _ ↦ hOut (ofs + i)) (fun i _ p hp ↦ hPairs i p hp)

def updPrefixQuad {B n : ℕ} (hB : 0 < B) (rOut : QRegister B n) (β : BitAssignment n)
    (g : ℕ → ZMod 2) : ℕ → BitAssignment n
  | 0 => β
  | k + 1 => Function.update (updPrefixQuad hB rOut β g k) (outWireOfRegQuad hB rOut k) (g k)

theorem updPrefixQuad_eq_writeReg {B n : ℕ} (hB : 0 < B) (rOut : QRegister B n)
    (β : BitAssignment n) (g : ℕ → ZMod 2) : updPrefixQuad hB rOut β g B = writeReg β rOut (fun j ↦
        g j.val) := by
  have hP : ∀ k ≤ B, updPrefixQuad hB rOut β g k =
      writeReg β rOut fun j ↦ if j.val < k then g j.val else β (rOut j) :=
    Nat.rec (fun _ ↦ Eq.symm (writeReg_zero_prefix_pairStep rOut β _ _ fun _ ↦ rfl)) fun m ih hm ↦
        by
      rw [updPrefixQuad, ih (Nat.le_of_succ_le hm),
          show outWireOfRegQuad hB rOut m =
              rOut ⟨m, hm⟩ from congrArg rOut.wires (Fin.ext (Nat.mod_eq_of_lt hm))]
      exact writeReg_upd_prefix_pairStep rOut β (fun j ↦ g j.val) (fun j ↦ β (rOut j)) hm
  exact (hP B le_rfl).trans (congrArg (writeReg β rOut) (funext fun j ↦ ite_eq_left j.isLt))

theorem projBit_zero_mkKetOpW_quad {W n : ℕ} [NeZero (2 ^ n)] (rWork : QRegister W n) (q : Wire n)
    (st : BitAssignment n → BitAssignment n) (ph : BitAssignment n → ZMod 2)
    (hq0 : ∀ δ, (∀ k : Fin W, δ (rWork k) = 0) → st δ q =
      0) : projBit q 0 * mkKetOpW rWork st ph = mkKetOpW rWork st ph :=
          projBit_mul_mkKetOpW rWork st ph q hq0

def quadCoreGen {Var : Type} {M B n : ℕ} (hB : 0 < B) (cp : ComputeProg M)
    (pairsFn : ℕ → List (WirePair n)) (v : Var) (rIn : QRegister M n) (rTgt : QRegister B n) :
    DynamicCircuit Var n :=
  wrapDynOnReg v rIn cp (xUnloadChunkCzPairsSeqDyn v (outWireOfRegQuad hB rTgt) 0 pairsFn
      (.circuit .identity) B)

theorem hB18_quad : (0 : ℕ) < 18 := by decide

theorem stepCB_apply_outside {w n : ℕ} (r : QRegister w n) (f : BitAssignment w → BitAssignment w)
    (β : BitAssignment n)
    (q : Wire n) (hne : ∀ u : Fin w, r u ≠ q) : stepCB r f β q = β q :=
  writeReg_apply_of_not_mem _ _ _ _ fun ⟨u, hu⟩ ↦ hne u hu
end QuantumComputation.Specs.PhotochemistrySolution.Dist18QuadUnld

namespace QuantumComputation.Specs.PhotochemistrySolution.ReflStage4
open Circuit Qubit PrimitiveGate PhotochemistrySolution.Poly28Sub254
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt (writeReg writeReg_apply_reg
  writeReg_apply_of_not_mem)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.PotOracleGen (disj_ne)
theorem finBitsVal_ite_testBit (m v : ℕ) : finBitsVal (fun i : Fin m ↦
    if v.testBit i.val then (1 : ZMod 2) else 0) = v % 2 ^ m := by
  rw [finBitsVal_eq_natOfZModBits]
  simp only [natOfZModBits, legNatOfZModBits_eq_sum]
  refine (Finset.sum_congr rfl fun j _ ↦ ?_).trans (sum_two_pow_testBit m v)
  cases v.testBit j.val <;> simp

/-- Deterministic post-state of `pOWAdd17Kick16` / `pOWLeg1Pass16` / `pOWLeg2Pass16` on `rZ16`. -/
def stOWZ16 {n : ℕ} (rZ16 : QRegister 16 n) (vFn : BitAssignment n → ℕ)
    (st : BitAssignment n → BitAssignment n) : BitAssignment n → BitAssignment n :=
  fun δ ↦ writeReg (st δ) rZ16 fun i ↦
    if ((finBitsVal (fun j : Fin 16 ↦ st δ (rZ16 j)) +
        vFn δ % 2 ^ 16) % 2 ^ 16).testBit i.val then 1 else 0
/-- Phase kick `+ (((zHi + v % 2^16) / 2^16 + v / 2^16 : ℕ) : ZMod 2)` of a `17`-bit OW leg pass. -/
def phOWZ16 {n : ℕ} (rZ16 : QRegister 16 n) (vFn : BitAssignment n → ℕ)
    (st : BitAssignment n → BitAssignment n) (ph : BitAssignment n → ZMod 2) : BitAssignment n →
    ZMod 2 :=
  fun δ ↦
      ph δ + ((((finBitsVal (fun j : Fin 16 ↦ st δ (rZ16 j)) + vFn δ % 2 ^ 16) / 2 ^ 16 + vFn δ /
      2 ^ 16 : ℕ) : ZMod 2))
theorem stOWZ16_outside {n : ℕ} (rZ16 : QRegister 16 n) (vFn : BitAssignment n → ℕ)
    (st : BitAssignment n →
  BitAssignment n) (δ : BitAssignment n) {w : Wire n}
    (hw : ∀ i : Fin 16, w ≠ rZ16 i) : stOWZ16 rZ16 vFn st δ w = st δ w :=
        writeReg_apply_of_not_mem _ _ _ _ fun ⟨i,
      hi⟩ ↦ hw i hi.symm
theorem stOWZ16_val {n : ℕ} (rZ16 : QRegister 16 n) (vFn : BitAssignment n → ℕ)
    (st : BitAssignment n → BitAssignment n)
    (δ : BitAssignment n) : finBitsVal (fun i : Fin 16 ↦ stOWZ16 rZ16 vFn st δ (rZ16 i)) =
      (finBitsVal (fun j : Fin 16 ↦ st δ (rZ16 j)) + vFn δ % 2 ^ 16) % 2 ^ 16 := by
  simp only [stOWZ16, writeReg_apply_reg, finBitsVal_ite_testBit, Nat.mod_mod]
end QuantumComputation.Specs.PhotochemistrySolution.ReflStage4

namespace QuantumComputation.Specs.PhotochemistrySolution.OuterW11Bridge
open Circuit Qubit PrimitiveGate QuantumComputation.Specs PhotochemistrySolution.KetSupport
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
open PhotochemistrySolution.RouterSelectWiringA PhotochemistrySolution.RouterSelectWiringB
  PhotochemistrySolution.ProviderCore PhotochemistrySolution.Stage12Compact
open PhotochemistrySolution.ZeroNEremSpec PhotochemistrySolution.Coin70Lift
  PhotochemistrySolution.TopSelectBridge PhotochemistrySolution.SelectCompactAnc
open _root_.DynamicCircuit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt hiding bit_cases
  eval_seq_mulVec ket ket_CNOT ket_TOFF ket_X ket_projector_one ket_projector_zero localIdx
  matrix_ext_ket qAssign_obs_map_val
open _root_.QuantumComputation.Specs.PhotochemistrySolution.PotOracleGen (disj_of_ne)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SplitRouter47_187 (uRouterSwapConj)
attribute [local reducible] totDimCompactGen
attribute [local irreducible] systemQubits_frozen SelectCompactAnc.ancWOfScr uRouterSwapConj
    PgBase.phaseGradientState
theorem rCoinExt_comm_off4 {kExt k : ℕ} (hk : kExt ≤ 72) {r : QRegister k dLayout}
    (hoff4 : OffIndexAndScratchPoly systemQubits_frozen scrWLayout (lcuSubLGen hpLayout)
        (scrSubLGen hpLayout) r)
    (M₁ : Operator (2 ^ kExt)) (M₂ : Operator (2 ^ k)) : Commute ((rCoinExt kExt hk).embedMatrix M₁)
      (r.embedMatrix M₂) :=
  (rCoinExt kExt hk).embedMatrix_comm_of_disjoint r (disj_of_ne fun i j e ↦ by
    have := hoffIndex_bounds_layout hoff4 j
    have := (val_rCoinExt hk i).symm.trans (congrArg Fin.val e)
    omega) M₁ M₂
end QuantumComputation.Specs.PhotochemistrySolution.OuterW11Bridge
end

noncomputable section
open QuantumComputation.Specs.PhotochemistrySolution.XMeasLinearCleanStep Operator QProg Matrix
  Circuit Qubit HermitianMat QuantumComputation.Specs
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
open QuantumComputation.Specs.PhotochemistrySolution
  QuantumComputation.Specs.PhotochemistrySolution.SplitRouter47_187
open _root_.DynamicCircuit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt hiding bit_cases
  eval_seq_mulVec ket ket_CNOT ket_TOFF ket_X ket_projector_one ket_projector_zero matrix_ext_ket
  qAssign_obs_map_val
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SplitRouterSeqBell26k hiding ket
  matrix_ext_ket
open scoped ComplexOrder MatrixOrder Circuit.Notation
namespace QuantumComputation.Specs.PhotochemistrySolution.Stage2Xor84
open PrimitiveGate PhotochemistrySolution.UnembedO3Bridge PhotochemistrySolution.SelectOracles
  PhotochemistrySolution.RouterSelectWiringA PhotochemistrySolution.ProviderCore
open PhotochemistrySolution.RouterSelectWiringB PhotochemistrySolution.Stage12Compact
  PhotochemistrySolution.ZeroNEremSpec PhotochemistrySolution.PotSelectWiring
attribute [local irreducible] systemQubits_frozen SelectCompactAnc.ancWOfScr
    PgBase.phaseGradientState
/--
Bijection on `[0..453]` packing `4 + 57 + 203 = 264` non-`rCtrlHi` scratch wires into
`[0..263]`, `rCtrlHi[0..186]` linearly into `[264..450]`, and the three ghost indices
`{4, 5, 396}` (`j in {4606, 4607, 4998}`) into `{451, 452, 453}`.
-/
def privRank454 (k : ℕ) : ℕ :=
    if k < 4 then k else if k < 6 then 451 + (k - 4) else if k < 209 then 61 + (k - 6) else if k <
    396 then 264 + (k - 209) else if k = 396 then 453 else 4 + (k - 397)
theorem privRank454_lt {k : ℕ} (hk : k < 454) : privRank454 k < 454 := by
  unfold privRank454; split_ifs <;> omega
theorem privRank454_inj {a b : ℕ} (ha : a < 454) (hb : b < 454)
    (h : privRank454 a = privRank454 b) : a =
    b := by unfold privRank454 at h; split_ifs at h <;> omega
theorem scrIdx_lo_lt {rk : ℕ} (h : rk < 33) : 30 + rk < scrLLayout := by dsimp [scrLLayout]; omega
theorem scrIdx_hi_lt {rk : ℕ} (h : rk < 454) : 297 + (rk - 33) < scrLLayout := by
  dsimp [scrLLayout]; omega
theorem sub4602_lt454 (j : Fin (routerWidth 187 8)) : j.val - 4602 < 454 := by
  have _ : j.val < 5056 := hEW5056 ▸ j.isLt; omega
/--
Wire map for `rElecXor179` placing `privRank454 (j - 4602)` into `[5680..5712] u [5947..6367]`
so `UsedXorTight K rElecXor179` is active on `ActiveLayoutFusedOf wIn` for every `95 + K <= wIn`
(`K = 84 -> wIn >= 179`, `Q = 6,311`, `0` extra `T` gates).
-/
def elecXor179WireFn (j : Fin (routerWidth 187 8)) : Wire dLayout :=
  if _ : j.val < 4602 then elecRouterWireFn j
  else
    let rk := privRank454 (j.val - 4602)
    if h2 : rk < 33 then rScrLayout ⟨30 + rk, scrIdx_lo_lt h2⟩
    else rScrLayout ⟨297 + (rk - 33), scrIdx_hi_lt (privRank454_lt (sub4602_lt454 j))⟩
theorem val_elecXor179WireFn (j : Fin (routerWidth 187 8)) : (elecXor179WireFn j).val = if j.val <
    18 then 5729 + j.val else if j.val < 114 then 5851 + (j.val - 18) else if j.val <
    4602 then 1128 + (j.val - 114)
    else if privRank454 (j.val - 4602) < 33 then 5680 + privRank454 (j.val - 4602) else 5947 +
        (privRank454 (j.val - 4602) - 33) := by
  have ⟨_, _⟩ := And.intro (j.isLt.trans_eq hEW5056) (privRank454_lt (sub4602_lt454 j))
  dsimp only [elecXor179WireFn]
  by_cases h1 : j.val < 4602
  · rw [dite_eq_left h1, val_elecRouterWireFn]
    split_ifs <;> omega
  · rw [dite_eq_right h1]
    split_ifs <;> rw [val_rScrLayout] <;> dsimp <;> omega

theorem elecXor179WireFn_injective : Function.Injective elecXor179WireFn := fun a b h ↦ by
  have ⟨_, _, _, _⟩ := And.intro (a.isLt.trans_eq hEW5056) (And.intro (b.isLt.trans_eq hEW5056)
    (And.intro (privRank454_lt (sub4602_lt454 a)) (privRank454_lt (sub4602_lt454 b))))
  have hv :=
      (val_elecXor179WireFn a).symm.trans ((congrArg Fin.val h).trans (val_elecXor179WireFn b))
  refine Fin.ext (if hab : a.val < 4602 ∨ b.val < 4602 then by split_ifs at hv <;> omega else ?_)
  have := privRank454_inj (sub4602_lt454 a) (sub4602_lt454 b) (by split_ifs at hv <;> omega)
  omega
/--
Tight `95 + K`-active electron `RouterReg 187 8 dLayout` (`wIn = 179`, `Q = 6,311` at `K = 84`,
`0` extra `T` gates, `100%` identical public/Bell/system wires to `rElecLayout`).
-/
def rElecXor179 : RouterReg 187 8 dLayout := ⟨⟨elecXor179WireFn, elecXor179WireFn_injective⟩⟩
theorem rElecXor179_eq_of_lt4602 {j : Fin (routerWidth 187 8)} (hj : j.val < 4602)
    : rElecXor179 j = rElecLayout j :=
  (dite_eq_left hj : elecXor179WireFn j = _)

theorem rElecXor179_roles_eq : rHas1 rElecXor179 = rHas1 rElecLayout ∧ rRawHas2 rElecXor179 =
    rRawHas2 rElecLayout ∧
    rIdx1 rElecXor179 = rIdx1 rElecLayout ∧ rIdx2 rElecXor179 = rIdx2 rElecLayout ∧
        rBufLo rElecXor179 = rBufLo rElecLayout ∧
    rBufHi rElecXor179 = rBufHi rElecLayout ∧ rHA rElecXor179 = rHA rElecLayout ∧ rHB rElecXor179 =
        rHB rElecLayout ∧ rSys rElecXor179 = rSys rElecLayout :=
  ⟨rElecXor179_eq_of_lt4602 (by dsimp; omega),
      rElecXor179_eq_of_lt4602 (by change 1 % routerWidth 187 8 < 4602; rw [hEW5056]; omega),
   funext fun _ ↦ rElecXor179_eq_of_lt4602 (by dsimp; omega), funext fun _ ↦
       rElecXor179_eq_of_lt4602 (by dsimp; omega),
   funext fun _ ↦ rElecXor179_eq_of_lt4602 (by dsimp; omega), funext fun _ ↦
       rElecXor179_eq_of_lt4602 (by dsimp; omega),
   funext fun _ ↦ rElecXor179_eq_of_lt4602 (by dsimp; omega), funext fun _ ↦
       rElecXor179_eq_of_lt4602 (by dsimp; omega),
   funext fun _ ↦ funext fun _ ↦ rElecXor179_eq_of_lt4602 (by dsimp; omega)⟩
end QuantumComputation.Specs.PhotochemistrySolution.Stage2Xor84

namespace QuantumComputation.Specs.PhotochemistrySolution.Stage2QromMux
theorem stream_quot_lt {M dLo Q : ℕ} (hM : M ≤ 2 ^ dLo * Q) (p : Fin M) : p.val / 2 ^ dLo < Q :=
    Nat.div_lt_of_lt_mul (Nat.lt_of_lt_of_le p.isLt hM)
theorem stream_mod_lt {M : ℕ} (dLo : ℕ) (p : Fin M) : p.val % 2 ^ dLo < 2 ^ dLo :=
    Nat.mod_lt p.val (Nat.two_pow_pos dLo)
end QuantumComputation.Specs.PhotochemistrySolution.Stage2QromMux

namespace QuantumComputation.Specs.PhotochemistrySolution.Stage2PotUnld
open PhotochemistrySolution.UnembedO3Bridge PhotochemistrySolution.SelectOracles
  PhotochemistrySolution.RouterSelectWiringA PhotochemistrySolution.ProviderCore
open PhotochemistrySolution.RouterSelectWiringB PhotochemistrySolution.Stage12Compact
  PhotochemistrySolution.ZeroNEremSpec PhotochemistrySolution.PotSelectWiring
open PhotochemistrySolution.Stage2Xor84
attribute [local irreducible] systemQubits_frozen SelectCompactAnc.ancWOfScr
    PgBase.phaseGradientState
theorem sub1238_lt156 (i : Fin (routerWidth 47 6)) : i.val - 1238 < 156 := by
  have _ : i.val < 1394 := hNW1394 ▸ i.isLt; omega
/--
Zero-`wIn` nuclear sub-router placing `[1238..1393]` inside `[5680..5699] u [5947..6082]` so
every wire of `rNucXor0` lies in `ActiveLayoutFusedOf wIn` for ALL `wIn : ℕ` (`0 <= wIn`).
-/
def nucXor0WireFn (i : Fin (routerWidth 47 6)) : Wire dLayout :=
  if _ : i.val < 1238 then nucRouterWireFn i
  else
    let k := i.val - 1238
    if _ : k < 20 then rScrLayout ⟨30 + k, by dsimp [scrLLayout]; omega⟩
    else rScrLayout ⟨297 + (k - 20), by have := sub1238_lt156 i; dsimp [scrLLayout]; omega⟩
theorem val_nucXor0WireFn (i : Fin (routerWidth 47 6)) : (nucXor0WireFn i).val = if i.val <
    14 then 5715 + i.val else if i.val < 110 then 5755 + (i.val - 14) else if i.val <
    1238 then i.val - 110 else if i.val - 1238 < 20 then 5680 + (i.val - 1238) else 5947 +
    (i.val - 1258) := by
  have := i.isLt.trans_eq hNW1394
  dsimp only [nucXor0WireFn]
  by_cases h1 : i.val < 1238
  · rw [dite_eq_left h1, val_nucRouterWireFn]
    split_ifs <;> omega
  · rw [dite_eq_right h1]
    split_ifs <;> rw [val_rScrLayout] <;> dsimp <;> omega
/-- Nuclear `RouterReg 47 6 dLayout` active for ALL `wIn : ℕ` (`wIn >= 0`). -/
def rNucXor0 : RouterReg 47 6 dLayout :=
  ⟨⟨nucXor0WireFn, fun a b h ↦ by
    have _ : a.val < 1394 := hNW1394 ▸ a.isLt; have _ : b.val < 1394 := hNW1394 ▸ b.isLt;
    have hv := congrArg Fin.val h; rw [val_nucXor0WireFn, val_nucXor0WireFn] at hv
    split_ifs at hv <;> (apply Fin.ext; omega)⟩⟩
end QuantumComputation.Specs.PhotochemistrySolution.Stage2PotUnld

namespace QuantumComputation.Specs.PhotochemistrySolution.Stage2ElecFirst
open PhotochemistrySolution.UnembedO3Bridge PhotochemistrySolution.SelectOracles
  PhotochemistrySolution.RouterSelectWiringA PhotochemistrySolution.ProviderCore
open PhotochemistrySolution.RouterSelectWiringB PhotochemistrySolution.Stage12Compact
  PhotochemistrySolution.ZeroNEremSpec PhotochemistrySolution.PotSelectWiring
open PhotochemistrySolution.Stage2Xor84 PhotochemistrySolution.Stage2PotUnld
attribute [local irreducible] systemQubits_frozen SelectCompactAnc.ancWOfScr
theorem routerSwapBits_congr_pub {M D : ℕ} (r : RouterReg M D dLayout)
    {δ₁ δ₂ : BitAssignment dLayout} (hPub : ∀ i : Fin (routerWidth M D), i.val < basePub M D →
    δ₁ (r i) = δ₂ (r i)) {w : Wire dLayout} (hw : δ₁ w = δ₂ w) :
    routerSwapBits r δ₁ w = routerSwapBits r δ₂ w := by
  have hId1 : idxValD (rIdx1 r) δ₁ = idxValD (rIdx1 r) δ₂ :=
    idxValD_congr fun d ↦ hPub _ ((fun _ ↦ by
      dsimp [basePub]
      omega) d.isLt)
  have hId2 : idxValD (rIdx2 r) δ₁ = idxValD (rIdx2 r) δ₂ :=
    idxValD_congr fun d ↦ hPub _ ((fun _ ↦ by
      dsimp [basePub]
      omega) d.isLt)
  have hEff : routerHas2Eff r δ₁ = routerHas2Eff r δ₂ := by
    simp only [routerHas2Eff, (hPub _ (by
      dsimp [basePub]
      omega) : δ₁ (rRawHas2 r) = _), hId1,
        hId2]
  have hMin : routerIdxMinVal r δ₁ = routerIdxMinVal r δ₂ := by
    simp only [routerIdxMinVal, hEff, hId1, hId2]
  have hMax : routerIdxMaxVal r δ₁ = routerIdxMaxVal r δ₂ := by
    simp only [routerIdxMaxVal, hEff, hId1, hId2]
  have swStep (off : ℕ) (ltOff : ∀ b : Fin 24, off + b.val < routerWidth M D)
      (hOff : off + 24 ≤ 98 + 2 * D)
      (p : Fin M) {ξ₁ ξ₂} (hξ : ∀ i, i.val < basePub M D → ξ₁ (r i) = ξ₂ (r i)) {q}
          (eqQ : ξ₁ q = ξ₂ q) :
      swapVecBits 24 (fun b ↦ r ⟨off + b.val, ltOff b⟩) (fun b ↦ rSys r p b) ξ₁ q =
        swapVecBits 24 (fun b ↦ r ⟨off + b.val, ltOff b⟩) (fun b ↦ rSys r p b) ξ₂ q := by
    have sp := swapVecBits_spec 24 (fun b ↦ r ⟨off + b.val, ltOff b⟩) (rSys r p)
      (fun _ _ e ↦ Fin.ext (Decidable.byContradiction fun _ ↦ rr_ne r (by
        dsimp
        omega) e))
      (fun _ _ e ↦ Fin.ext (Decidable.byContradiction fun _ ↦ rr_ne r (by
        dsimp
        omega) e))
      (fun j _ ↦ rr_ne r (ne_of_lt (Nat.lt_of_lt_of_le (Nat.add_lt_add_left j.isLt off)
          (by
            dsimp
            omega))))
    rcases Classical.em (∃ b, q = r ⟨off + b.val, ltOff b⟩) with ⟨b, rfl⟩ | hqU
    · exact ((sp ξ₁).1 b).trans ((hξ _ (by
      dsimp [basePub]
      nlinarith [p.isLt, b.isLt])).trans
          ((sp ξ₂).1 b).symm)
    · rcases Classical.em (∃ b, q = rSys r p b) with ⟨b, rfl⟩ | hqT
      · exact ((sp ξ₁).2.1 b).trans ((hξ _ (Nat.lt_of_lt_of_le (Nat.add_lt_add_left b.isLt off)
          (by
            dsimp [basePub]
            omega))).trans ((sp ξ₂).2.1 b).symm)
      · exact ((sp ξ₁).2.2 q (fun b e ↦ hqU ⟨b, e⟩) (fun b e ↦ hqT ⟨b, e⟩)).trans
          (eqQ.trans ((sp ξ₂).2.2 q (fun b e ↦ hqU ⟨b, e⟩) (fun b e ↦ hqT ⟨b, e⟩)).symm)
  have hLo {q} (eqQ : δ₁ q = δ₂ q) : routerLoBits r δ₁ q = routerLoBits r δ₂ q := by
    simp only [routerLoBits, ← (hPub _ (by
      dsimp [basePub]
      omega) : δ₁ (rHas1 r) = _), ← hMin]
    split_ifs with hc
    · exact swStep (2 + 2 * D) (rw_ltBufLo M D) (by omega) ⟨_, hc.2⟩ hPub eqQ
    · exact eqQ
  simp only [routerSwapBits, ← hEff, ← hMax]
  split_ifs with hc
  · exact swStep (26 + 2 * D) (rw_ltBufHi M D) (by omega) ⟨_, hc.2⟩ (fun _ hi ↦ hLo (hPub _ hi))
        (hLo hw)
  · exact hLo hw
end QuantumComputation.Specs.PhotochemistrySolution.Stage2ElecFirst

namespace QuantumComputation.Specs.PhotochemistrySolution.SortedRouterSpec
/--
Zero-gated strictly sorted single-buffer Stage-5 Dual-Bell unloader (`8 * M - 8 * D - 12` `T`,
`0 .TOFF`, `UsedXorTight 0 r`: `316 T` on `(47, 6)` and `1,420 T` on `(187, 8)`).
-/
theorem sortedUnload_lt_of_sub {D d : ℕ} (hdlt : d < D - 1) : d < D := by omega
end QuantumComputation.Specs.PhotochemistrySolution.SortedRouterSpec

namespace QuantumComputation.Specs.PhotochemistrySolution.Stage2ElecFirstZero
/-- Disjoint interval swap involution swapping `[a, a + w)` with `[b, b + w)`. -/
def swapPair (a b w i : ℕ) : ℕ :=
    if a ≤ i ∧ i < a + w then b + (i - a) else if b ≤ i ∧ i < b + w then a + (i - b) else i
theorem swapPair_lt {a b w N i : ℕ} (ha : a + w ≤ N) (hb : b + w ≤ N)
    (hi : i < N) : swapPair a b w i < N := by unfold swapPair; split_ifs <;> omega
theorem swapPair_invol {a b w : ℕ} (hDisj : a + w ≤ b ∨ b + w ≤ a)
    (i : ℕ) : swapPair a b w (swapPair a b w i) = i := by unfold swapPair; split_ifs <;> omega
theorem swapPair_fixed {a b w i : ℕ} (ha : i < a ∨ a + w ≤ i) (hb : i < b ∨ b + w ≤ i) :
    swapPair a b w i = i := by unfold swapPair; split_ifs <;> omega
theorem swapPair_comm {a₁ b₁ w₁ a₂ b₂ w₂ : ℕ} (h1 : a₁ + w₁ ≤ a₂ ∨ a₂ + w₂ ≤ a₁)
    (h2 : a₁ + w₁ ≤ b₂ ∨ b₂ + w₂ ≤ a₁) (h3 : b₁ + w₁ ≤ a₂ ∨ a₂ + w₂ ≤ b₁)
    (h4 : b₁ + w₁ ≤ b₂ ∨ b₂ + w₂ ≤ b₁) (x : ℕ) : swapPair a₁ b₁ w₁ (swapPair a₂ b₂ w₂ x) =
    swapPair a₂ b₂ w₂ (swapPair a₁ b₁ w₁ x) := by unfold swapPair; split_ifs <;> omega
end QuantumComputation.Specs.PhotochemistrySolution.Stage2ElecFirstZero

section
open QuantumComputation.Specs.PhotochemistrySolution.XMeasUnld
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB hiding bitSign eval_seq_mulVec ket
  ket_CNOT ket_TOFF ket_X matrix_ext_ket writeReg writeReg_apply_of_not_mem
namespace QuantumComputation.Specs.PhotochemistrySolution.Stage2ZeroGated
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SortedRouterSpec
  (ValidZeroGatedSortedRouterInput routerCtrlLo_of_zeroGatedSorted routerCtrlHi_of_zeroGatedSorted)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Stage2ElecFirstZero (swapPair
    swapPair_lt swapPair_invol swapPair_fixed)
attribute [local semireducible] ComputeProg.fwdBits DynQromUncompA.remeasureIf
    DynQromUncompA.wrapDyn SplitRouterSeqBell26k.tempAndFanoutDyn
  PhotochemistrySolution.KinB.andComputeCircuit PhotochemistrySolution.KinB.andUncomputeDyn
/--
Re-indexed `RouterReg M D n` induced by a bounded involution `f` on
`[0 .. routerWidth M D)`.
-/
def routerOfInvol {M D n : ℕ} (r : RouterReg M D n) (f : ℕ → ℕ)
    (hfLt : ∀ i < routerWidth M D, f i < routerWidth M D)
    (hfInv : ∀ i < routerWidth M D, f (f i) = i) : RouterReg M D n where
  wires :=
    ⟨fun i ↦ r ⟨f i.val, hfLt i.val i.isLt⟩, fun i j hij ↦ by
      have heq : f i.val = f j.val := congrArg Fin.val (r.wires.injective hij)
      exact Fin.ext (by rw [← hfInv i.val i.isLt, ← hfInv j.val j.isLt, heq])⟩
/-- Equivalence of two `RouterReg M D n` views sharing all public wires and `sPrivCleanSet`. -/
def SamePubPriv {M D n : ℕ} (r' r : RouterReg M D n) : Prop :=
    (∀ i : Fin (routerWidth M D), i.val < basePub M D → r' i = r i) ∧ sPrivCleanSet r' =
    sPrivCleanSet r
theorem samePubPriv_routerOfInvol {M D n : ℕ} (r : RouterReg M D n) (f : ℕ → ℕ)
    (hfLt : ∀ i < routerWidth M D, f i < routerWidth M D) (hfInv : ∀ i < routerWidth M D, f (f i) =
    i) (hfPub : ∀ i < basePub M D, f i = i) : SamePubPriv (routerOfInvol r f hfLt hfInv) r := by
  refine ⟨fun i hi ↦ congrArg r.wires (Fin.ext (hfPub i.val hi)), Finset.ext fun w ↦ ?_⟩
  have hGe (i) (hi : i < routerWidth M D) (hge : basePub M D ≤ i) : basePub M D ≤ f i :=
    Decidable.byContradiction fun hlt ↦ by
      have := (hfInv i hi).symm.trans (hfPub (f i) (Nat.lt_of_not_ge hlt))
      omega
  simp only [sPrivCleanSet, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun ⟨i, hge, hw⟩ ↦ ⟨⟨f i.val, hfLt i.val i.isLt⟩, hGe i.val i.isLt hge, hw⟩,
    fun ⟨j, hge, hw⟩ ↦ ⟨⟨f j.val, hfLt j.val j.isLt⟩, hGe j.val j.isLt hge,
      (congrArg r.wires (Fin.ext (hfInv j.val j.isLt))).trans hw⟩⟩
theorem samePubPriv_pub_eq {M D n : ℕ} {r' r : RouterReg M D n} (hEq : SamePubPriv r' r) :
    rHas1 r' = rHas1 r ∧ rRawHas2 r' = rRawHas2 r ∧ rIdx1 r' = rIdx1 r ∧ rIdx2 r' = rIdx2 r ∧
    rBufLo r' = rBufLo r ∧ rBufHi r' = rBufHi r ∧ rHA r' = rHA r ∧ rHB r' = rHB r ∧ rSys r' =
        rSys r :=
  ⟨hEq.1 _ (by unfold basePub; dsimp; omega), hEq.1 _ (by unfold basePub; dsimp; omega),
      funext fun d ↦ hEq.1 _ (by have := d.isLt; unfold basePub; dsimp; omega),
   funext fun d ↦ hEq.1 _ (by have := d.isLt; unfold basePub; dsimp; omega),
   funext fun b ↦ hEq.1 _ (by have := b.isLt; unfold basePub; dsimp; omega),
   funext fun b ↦ hEq.1 _ (by have := b.isLt; unfold basePub; dsimp; omega),
   funext fun b ↦ hEq.1 _ (by have := b.isLt; unfold basePub; dsimp; omega),
   funext fun b ↦ hEq.1 _ (by have := b.isLt; unfold basePub; dsimp; omega),
   funext fun p ↦ funext fun b ↦
       hEq.1 _ (by have := p.isLt; have := b.isLt; unfold basePub; dsimp; omega)⟩
theorem validRouterInput_iff_of_samePubPriv {M D n : ℕ} {r' r : RouterReg M D n}
    (hEq : SamePubPriv r' r) (β : BitAssignment n) : ValidRouterInput r' β ↔
    ValidRouterInput r β := by obtain ⟨e1, e2, ei1, ei2, ebl, ebh, eha, ehb, _⟩ :=
                                 samePubPriv_pub_eq hEq; unfold ValidRouterInput; rw [e1, e2, ei1,
                                 ei2, ebl, ebh, eha, ehb, hEq.2]
theorem validZeroGated_iff_of_samePubPriv {M D n : ℕ} {r' r : RouterReg M D n}
    (hEq : SamePubPriv r' r) (β : BitAssignment n) : ValidZeroGatedSortedRouterInput r' β ↔
    ValidZeroGatedSortedRouterInput r β := by obtain ⟨e1, e2, ei1, ei2, _, _, _, _, _⟩ :=
                                                samePubPriv_pub_eq hEq; unfold
                                                ValidZeroGatedSortedRouterInput;
                                                rw [validRouterInput_iff_of_samePubPriv hEq β, e1,
                                                  e2,
                                                ei1, ei2]
def swapHas2Alias (M D i : ℕ) : ℕ := swapPair 1 (basePub M D + 1) 1 i
theorem swapHas2Alias_lt {M D i : ℕ} (hi : i < routerWidth M D) : swapHas2Alias M D i <
    routerWidth M D := by
  unfold swapHas2Alias
  exact swapPair_lt (by unfold routerWidth; omega) (by unfold routerWidth basePub; omega) hi
theorem swapHas2Alias_invol {M D i : ℕ} : swapHas2Alias M D (swapHas2Alias M D i) = i :=
    swapPair_invol (Or.inl (by unfold basePub; omega)) i
/-- `RouterReg` view aliasing `rHas2Eff` directly to `rRawHas2 r`, leaving `bp + 1` untouched. -/
def rHas2Alias {M D n : ℕ} (r : RouterReg M D n) : RouterReg M D n :=
    routerOfInvol r (swapHas2Alias M D) (fun _ hi ↦ swapHas2Alias_lt hi)
    (fun _ _ ↦ swapHas2Alias_invol)
theorem planeOfRouter_rHas2Alias_apply_of_ne1 {M D n : ℕ} (r : RouterReg M D n) (b : Fin 24)
    (i : Fin (planeWidth M D)) (hi : i.val ≠ 1) : planeOfRouter (rHas2Alias r) b i =
    planeOfRouter r b i := by
  have _ : _ ∧ _ := ⟨b.isLt, i.isLt⟩
  have _ : planeIdxVal M D b i.val ≠ 1 ∧ planeIdxVal M D b i.val ≠ basePub M D + 1 := by
    dsimp only [planeWidth, planeIdxVal, planeIdxFixed, planeIdxD, planeIdxM, basePub] at *
    split_ifs <;> omega
  exact congrArg r.wires (Fin.ext (show swapPair 1 (basePub M D + 1) 1 (planeIdxVal M D b i.val) =
      _ from
    swapPair_fixed (by omega) (by omega)))

theorem planeOfRouter_rHas2Alias_roles {M D n : ℕ} (r : RouterReg M D n)
    (b : Fin 24) : pHas1 (planeOfRouter (rHas2Alias r) b) = rHas1 r ∧
    pHas2Eff (planeOfRouter (rHas2Alias r) b) = rRawHas2 r ∧
    pOnly1 (planeOfRouter (rHas2Alias r) b) = rOnly1 r ∧ pBufLo (planeOfRouter (rHas2Alias r) b) =
        pBufLo (planeOfRouter r b) ∧
    pBufHi (planeOfRouter (rHas2Alias r) b) = pBufHi (planeOfRouter r b) ∧
        pHA (planeOfRouter (rHas2Alias r) b) = pHA (planeOfRouter r b) ∧
    pHB (planeOfRouter (rHas2Alias r) b) = pHB (planeOfRouter r b) ∧
        pAnc (planeOfRouter (rHas2Alias r) b) = rAnc r ∧ pUMsb (planeOfRouter (rHas2Alias r) b) =
        rUMsb r ∧ pNotMin (planeOfRouter (rHas2Alias r) b) = rNotMin r ∧
    pNotMax (planeOfRouter (rHas2Alias r) b) = rNotMax r ∧ pAMsb (planeOfRouter (rHas2Alias r) b) =
        rAMsb r ∧ pCReg (planeOfRouter (rHas2Alias r) b) = rCReg r ∧
        pCtrlLo (planeOfRouter (rHas2Alias r) b) = rCtrlLo r ∧
    pCtrlHi (planeOfRouter (rHas2Alias r) b) = rCtrlHi r ∧ pSys (planeOfRouter (rHas2Alias r) b) =
        pSys (planeOfRouter r b) := by
  have fx (i) (h : i.val ≠ 1 := by dsimp <;> omega) := planeOfRouter_rHas2Alias_apply_of_ne1 r b i h
  have rEq {i j : Fin (routerWidth M D)} (h : i.val = j.val) : r i = r j :=
      congrArg r.wires (Fin.ext h)
  exact ⟨(fx _).trans (rEq rfl), congrArg r.wires (Fin.ext (by
      change swapHas2Alias M D (planeIdxVal M D b 1) = 1
      dsimp only [planeIdxVal, planeIdxFixed, swapHas2Alias, swapPair]
      split_ifs <;> omega)),
    (fx _).trans (rEq (by simp [planeIdxVal, planeIdxFixed])), fx _, fx _, fx _, fx _,
    (fx _).trans (rEq (by simp [planeIdxVal, planeIdxFixed])),
    funext fun d ↦ (fx _).trans (planeOfRouter_uMsb r b d), funext fun d ↦
        (fx _).trans (planeOfRouter_notMin r b d),
    funext fun d ↦ (fx _).trans (planeOfRouter_notMax r b d), funext fun d ↦
        (fx _).trans (planeOfRouter_aMsb r b d),
    funext fun d ↦
        (fx _).trans (planeOfRouter_cReg r b d), (funext fun _ ↦
        fx _).trans (planeOfRouter_ctrlLo r b),
    (funext fun _ ↦ fx _).trans (planeOfRouter_ctrlHi r b), funext fun _ ↦ fx _⟩
/-- Computable `Bool`-equality public low-port indicator `p.val = idx1 ? has1 : 0`. -/
def pubCtrlLo {M D n : ℕ} (r : RouterReg M D n) (α : BitAssignment n) (p : Fin M) : ZMod 2 :=
  cond (Nat.beq p.val (idxValD (rIdx1 r) α)) (α (rHas1 r)) 0
/-- Computable `Bool`-equality public high-port indicator `p.val = idx2 ? rawHas2 : 0`. -/
def pubCtrlHi {M D n : ℕ} (r : RouterReg M D n) (α : BitAssignment n) (p : Fin M) : ZMod 2 :=
    cond (Nat.beq p.val (idxValD (rIdx2 r) α)) (α (rRawHas2 r)) 0
theorem pubCtrl_congr {M D n : ℕ} (r : RouterReg M D n) {α₁ α₂ : BitAssignment n}
    (hEq : ∀ w, PubCtrlSet r w → α₁ w = α₂ w) : pubCtrlLo r α₁ = pubCtrlLo r α₂ ∧ pubCtrlHi r α₁ =
    pubCtrlHi r α₂ := by
  obtain ⟨r1, r2, i1, i2⟩ := pubCtrlSet_roles r
  exact ⟨funext fun p ↦ by simp only [pubCtrlLo, idxValD_congr fun d ↦ hEq _ (i1 d), hEq _ r1],
    funext fun p ↦ by simp only [pubCtrlHi, idxValD_congr fun d ↦ hEq _ (i2 d), hEq _ r2]⟩
theorem pubCtrl_eq_routerCtrl {M D n : ℕ} {r : RouterReg M D n} {β : BitAssignment n}
    (hβ : ValidZeroGatedSortedRouterInput r β) : pubCtrlLo r β = routerCtrlLo r β ∧ pubCtrlHi r β =
    routerCtrlHi r β :=
  ⟨funext fun p ↦ by rw [pubCtrlLo, cond_nat_beq,
    congrFun (routerCtrlLo_of_zeroGatedSorted hβ) p],
   funext fun p ↦ by rw [pubCtrlHi, cond_nat_beq,
    congrFun (routerCtrlHi_of_zeroGatedSorted hβ) p]⟩
theorem rCtrlLo_inj_ne {M D n : ℕ} (r : RouterReg M D n) : ∀ p q : Fin M, p ≠ q → rCtrlLo r p ≠
    rCtrlLo r q :=
  fun _ _ hpq e ↦ hpq (Fin.ext (by
    have hv := congrArg Fin.val (r.wires.injective e); dsimp at hv; omega))
theorem rCtrlHi_inj_ne {M D n : ℕ} (r : RouterReg M D n) : ∀ p q : Fin M, p ≠ q → rCtrlHi r p ≠
    rCtrlHi r q :=
  fun _ _ hpq e ↦ hpq (Fin.ext (by
    have hv := congrArg Fin.val (r.wires.injective e); dsimp at hv; omega))
/-- Unitary XORing `pubCtrlLo r α p + pubCtrlHi r α p` into `rCtrlLo r p`. -/
def uXorTargetLo {M D n : ℕ} (r : RouterReg M D n) : Unitary (2 ^ n) :=
  uVecToggle (rCtrlLo r) (rCtrlLo_inj_ne r)
    (fun α p ↦ pubCtrlLo r α p + pubCtrlHi r α p)
    (fun _ _ hEq ↦ by
      have hp := pubCtrl_congr r fun w ⟨u, hu, hw⟩ ↦ hw ▸
        hEq (r u) fun p ↦ rr_ne r (by have := p.isLt; unfold basePub; dsimp; omega)
      funext p; rw [congrFun hp.1 p, congrFun hp.2 p])
/-- Unitary toggling `rCtrlHi r p` by `pubCtrlHi r α p + targetHi α p`. -/
def uHiBridge {M D n : ℕ} (r : RouterReg M D n) (targetHi : BitAssignment n → Fin M → ZMod 2)
    (hDep : ∀ α₁ α₂, (∀ w, PubCtrlSet r w → α₁ w = α₂ w) → targetHi α₁ = targetHi α₂) :
    Unitary (2 ^ n) :=
  uVecToggle (rCtrlHi r) (rCtrlHi_inj_ne r)
    (fun α p ↦ pubCtrlHi r α p + targetHi α p)
    (fun _ _ hEq ↦ by
      have hc : ∀ w, PubCtrlSet r w → _ = _ := fun w ⟨u, hu, hw⟩ ↦ hw ▸
        hEq (r u) fun p ↦ rr_ne r (by have := p.isLt; unfold basePub; dsimp; omega)
      funext p; rw [congrFun (pubCtrl_congr r hc).2 p, congrFun (hDep _ _ hc) p])
/-- Wires disjoint from both `rCtrlHi r` and `PubCtrlSet r`. -/
def SNotHiBridge {M D n : ℕ} (r : RouterReg M D n) (w : Wire n) : Prop :=
    (∀ p : Fin M, w ≠ rCtrlHi r p) ∧ ¬ PubCtrlSet r w
open PrimitiveGate hiding s
theorem actsIndepOf_uHiBridge {M D n : ℕ} (r : RouterReg M D n)
    (targetHi : BitAssignment n → Fin M → ZMod 2)
    (hDep : ∀ α₁ α₂, (∀ w, PubCtrlSet r w → α₁ w = α₂ w) → targetHi α₁ = targetHi α₂) :
    ActsIndepOf (SNotHiBridge r) (uHiBridge r targetHi hDep) :=
  actsIndepOf_uVecToggle _ _ _ _ (fun _ hw ↦ hw.1) fun q hq α val ↦ by
    have hc : ∀ w, PubCtrlSet r w → Function.update α q val w = α w := fun w hw ↦
        Function.update_of_ne (fun (e : w = q) ↦ hq.2 (e ▸ hw)) _ _
    exact funext fun p ↦
        congrArg₂ (· + ·) (congrFun (pubCtrl_congr r hc).2 p) (congrFun (hDep _ _ hc) p)

theorem actsIndepOf_allPlaneMod_uXorTargetLo {M D n : ℕ} (r : RouterReg M D n) :
    ActsIndepOf (AllPlaneMod r) (uXorTargetLo r) :=
  actsIndepOf_uVecToggle _ _ _ _ (fun u hw p (e : u = rCtrlLo r p) ↦
      not_allPlaneMod_of_idx r (Or.inr (by dsimp; omega)) (e ▸ hw)) fun q hq α val ↦ by
    have hc : ∀ w, PubCtrlSet r w → Function.update α q val w = α w := fun w hw ↦
        Function.update_of_ne (fun (e : w = q) ↦ not_allPlaneMod_of_pubCtrlSet hw (e ▸ hq)) _ _
    exact funext fun p ↦
        congrArg₂ (· + ·) (congrFun (pubCtrl_congr r hc).1 p) (congrFun (pubCtrl_congr r hc).2 p)

theorem fwdBits_pUMsbDownLoop_other {M D n : ℕ} (usePhantom : Bool) (r : RouterReg M D n) :
    ∀ (k : ℕ) (hk : k < D) (η : BitAssignment n), (∀ d : Fin D, d.val < k → η (rUMsb r d) = 0) →
      ∀ w : Wire n, (∀ d : Fin D, w ≠ rUMsb r d) → (pUMsbDownLoop usePhantom r k hk).fwdBits η w =
          η w
  | 0, _, _, _, _, _ => rfl
  | k + 1, hk, η, h0, w, hw => by
      obtain ⟨_, _, sOth⟩ := fwdBits_pUMsbStep usePhantom r k hk η (h0 _ (Nat.lt_succ_self k))
      dsimp only [pUMsbDownLoop]
      rw [fwdBits_seq]
      exact (fwdBits_pUMsbDownLoop_other usePhantom r k (Nat.lt_of_succ_lt hk) _
        (fun d hd ↦ (sOth _ (rUMsb_ne_of_ne r fun e ↦
            by have := congrArg Fin.val e; dsimp at this; omega)
          (rUMsb_ne_of_ne r fun e ↦
              by have :=
                   congrArg Fin.val e; dsimp at this; omega)).trans (h0 d (Nat.lt_succ_of_lt hd))) w
                   hw).trans (sOth w (hw _) (hw _))
end QuantumComputation.Specs.PhotochemistrySolution.Stage2ZeroGated

namespace QuantumComputation.Specs.PhotochemistrySolution.Stage2ChDiffMux960
open PhotochemistrySolution.SplitRouterFredkinMux PhotochemistrySolution.SplitRouterMuxD1
  PhotochemistrySolution.Stage2QromMux PhotochemistrySolution.SelectOracles
open PhotochemistrySolution.ProviderCore
open _root_.QuantumComputation.Specs.PhotochemistrySolution.QubitizationWalkSem hiding bitSign
  bitSign_add bitSign_mul_self sqrtHalf sqrtHalf_mul_sqrtHalf star_sqrtHalf
attribute [local semireducible] SplitRouterSeqBell26k.tempAndFanoutDyn KinB.andComputeCircuit
    KinB.andUncomputeDyn XMeasLinearCleanStep.xUnloadCzPairsSeqDyn
theorem uMsbHi_le_oneHot_of_validPlaneCtrlMuxD1 {M D n : ℕ} (r : PlaneReg M D n)
    {β : BitAssignment n} (hC : ValidPlaneCtrlMuxD1 r β) :
    (∀ d : Fin D, 1 ≤ d.val → β (pUMsb r d) = 0) ∨ (∃ dS : Fin D, 1 ≤ dS.val ∧ ∀ d : Fin D, 1 ≤
        d.val → β (pUMsb r d) = if d = dS then 1 else 0) := by
  rcases PhotochemistrySolution.XMeasUnld.bit_cases (β (pHas1 r)) with h1_0 | h1_1
  · exact Or.inl (hC.2.1 h1_0).2.2
  · obtain ⟨_, _, _, _, hM1, hM2⟩ := hC.2.2.2 h1_1
    obtain ⟨dS, hu⟩ : ∃ dS : Fin D, ∀ d : Fin D, 1 ≤ d.val → β (pUMsb r d) = if d =
        dS then 1 else 0 :=
      (PhotochemistrySolution.XMeasUnld.bit_cases (β (pHas2Eff r))).elim
        (fun h0 ↦ (hM1 h0).imp fun _ h ↦ h.2) fun h1 ↦ let ⟨_, _, _, _, _, dS, _, _, hu⟩ := hM2 h1
          ⟨dS, hu⟩
    exact if hd0 : dS.val = 0 then Or.inl fun d hd1 ↦ (hu d hd1).trans
      (ite_eq_right (Fin.ne_of_val_ne (by omega))) else Or.inr ⟨dS, by omega, hu⟩
end QuantumComputation.Specs.PhotochemistrySolution.Stage2ChDiffMux960

namespace QuantumComputation.Specs.PhotochemistrySolution.Stage2ChDiffNoNF
open PhotochemistrySolution.SplitRouterFredkinMux PhotochemistrySolution.SplitRouterMuxD1
  PhotochemistrySolution.Stage2QromMux PhotochemistrySolution.SelectOracles
open PhotochemistrySolution.RouterSelectWiringA PhotochemistrySolution.ProviderCore
  PhotochemistrySolution.Stage2ChDiffMux960 PhotochemistrySolution.Stage2ElecFirstZero
open _root_.QuantumComputation.Specs.PhotochemistrySolution.QubitizationWalkSem hiding bitSign
  bitSign_add bitSign_mul_self sqrtHalf sqrtHalf_mul_sqrtHalf star_sqrtHalf
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Stage2ZeroGated (routerOfInvol
    SNotHiBridge)
attribute [local semireducible] SplitRouterSeqBell26k.tempAndFanoutDyn KinB.andComputeCircuit
    KinB.andUncomputeDyn XMeasLinearCleanStep.xUnloadCzPairsSeqDyn
/--
Computable prefix loop toggling `pNotMin r d` by `β (pHas1 r)` and `pNotMax r d` by
`β (pHas2Eff r)` for `d < k`.
-/
def toggleNotFlagsLoop {M D n : ℕ} (r : PlaneReg M D n) (β : BitAssignment n) :
    ∀ k : ℕ, k ≤ D → BitAssignment n
  | 0, _ => β
  | k + 1, hk =>
      let prev := toggleNotFlagsLoop r β k (Nat.le_of_succ_le hk); let d : Fin D := ⟨k, hk⟩
      Function.update
        (Function.update prev (pNotMin r d) (prev (pNotMin r d) + β (pHas1 r)))
        (pNotMax r d) (prev (pNotMax r d) + β (pHas2Eff r))
/-- Computable `BitAssignment` involution mapping un-negated `(idx1, idx2)` flags on
`(pNotMin, pNotMax)` to standard `(¬pMin, ¬pMax)` flags (`pNotMin ⊕ pHas1`, `pNotMax ⊕ pHas2Eff`).
-/
def toggleNotFlags {M D n : ℕ} (r : PlaneReg M D n) (β : BitAssignment n) : BitAssignment n :=
  toggleNotFlagsLoop r β D le_rfl
/--
Classical plane control invariant when `(pNotMin, pNotMax)` hold raw zero-gated `(idx1, idx2)`
instead of `(idx1 ⊕ has1, idx2 ⊕ has2Eff)`.
-/
def ValidPlaneCtrlMuxD1NoNF {M D n : ℕ} (r : PlaneReg M D n) (β : BitAssignment n) : Prop :=
    ValidPlaneCtrlMuxD1 r (toggleNotFlags r β)
theorem toggleNotFlagsLoop_other {M D n : ℕ} (r : PlaneReg M D n) (β : BitAssignment n) {w : Wire n}
    (hMin : ∀ d : Fin D, w ≠ pNotMin r d) (hMax : ∀ d : Fin D, w ≠ pNotMax r d) :
    ∀ (k : ℕ) (hk : k ≤ D), toggleNotFlagsLoop r β k hk w = β w
  | 0, _ => rfl
  | k + 1, hk => by
      dsimp only [toggleNotFlagsLoop]
      rw [Function.update_of_ne (hMax ⟨k, hk⟩), Function.update_of_ne (hMin ⟨k, hk⟩)]
      exact toggleNotFlagsLoop_other r β hMin hMax k (Nat.le_of_succ_le hk)

theorem toggleNotFlagsLoop_both_pairStep {M D n : ℕ} (r : PlaneReg M D n)
    (β : BitAssignment n) (d : Fin D) :
    ∀ (k : ℕ) (hk : k ≤ D),
      toggleNotFlagsLoop r β k hk (pNotMin r d) =
        (if d.val < k then β (pNotMin r d) + β (pHas1 r) else β (pNotMin r d)) ∧
      toggleNotFlagsLoop r β k hk (pNotMax r d) =
        (if d.val < k then β (pNotMax r d) + β (pHas2Eff r) else β (pNotMax r d))
  | 0, _ => ⟨(ite_eq_right (Nat.not_lt_zero _)).symm, (ite_eq_right (Nat.not_lt_zero _)).symm⟩
  | k + 1, hk => by
      obtain ⟨ihMin, ihMax⟩ := toggleNotFlagsLoop_both_pairStep r β d k (Nat.le_of_succ_le hk)
      dsimp only [toggleNotFlagsLoop]
      rw [Function.update_of_ne (pr_ne r (by
        dsimp
        omega) : pNotMin r d ≠ pNotMax r ⟨k, hk⟩)]
      rcases eq_or_ne d ⟨k, hk⟩ with rfl | hdk
      · dsimp only at ihMin ihMax ⊢
        simp only [Function.update_self, ihMin, ihMax, lt_irrefl, Nat.lt_succ_self, ↓reduceIte,
            and_self]
      · have _ : d.val ≠ k := Fin.val_ne_of_ne hdk
        rw [Function.update_of_ne (pr_ne r (by
          dsimp
          omega)), ihMin,
          Function.update_of_ne (pr_ne r (by
            dsimp
            omega)),
          Function.update_of_ne (pr_ne r (by
            dsimp
            omega) : pNotMax r d ≠ pNotMin r ⟨k, hk⟩),
              ihMax]
        exact ⟨if_congr ⟨Nat.lt_succ_of_lt, by omega⟩ rfl rfl, if_congr ⟨Nat.lt_succ_of_lt,
            by omega⟩ rfl rfl⟩

theorem toggleNotFlagsLoop_notMin {M D n : ℕ} (r : PlaneReg M D n) (β : BitAssignment n)
    (d : Fin D) (k : ℕ) (hk : k ≤ D) : toggleNotFlagsLoop r β k hk (pNotMin r d) =
      if d.val < k then β (pNotMin r d) + β (pHas1 r) else β (pNotMin r d) :=
  (toggleNotFlagsLoop_both_pairStep r β d k hk).1

theorem toggleNotFlagsLoop_notMax {M D n : ℕ} (r : PlaneReg M D n) (β : BitAssignment n)
    (d : Fin D) (k : ℕ) (hk : k ≤ D) : toggleNotFlagsLoop r β k hk (pNotMax r d) =
      if d.val < k then β (pNotMax r d) + β (pHas2Eff r) else β (pNotMax r d) :=
  (toggleNotFlagsLoop_both_pairStep r β d k hk).2

theorem toggleNotFlags_other {M D n : ℕ} (r : PlaneReg M D n) (β : BitAssignment n) {w : Wire n}
    (hMin : ∀ d : Fin D, w ≠ pNotMin r d) (hMax : ∀ d : Fin D, w ≠ pNotMax r d) :
    toggleNotFlags r β w = β w := toggleNotFlagsLoop_other r β hMin hMax D le_rfl

theorem toggleNotFlags_notMin {M D n : ℕ} (r : PlaneReg M D n) (β : BitAssignment n)
    (d : Fin D) : toggleNotFlags r β (pNotMin r d) = β (pNotMin r d) + β (pHas1 r) := by
  exact (toggleNotFlagsLoop_notMin r β d D le_rfl).trans (ite_eq_left d.isLt)
theorem toggleNotFlags_notMax {M D n : ℕ} (r : PlaneReg M D n) (β : BitAssignment n)
    (d : Fin D) : toggleNotFlags r β (pNotMax r d) = β (pNotMax r d) + β (pHas2Eff r) := by
  exact (toggleNotFlagsLoop_notMax r β d D le_rfl).trans (ite_eq_left d.isLt)
theorem z2_add_self_cancel (x y : ZMod 2) : (x + y) + y = x := by
  rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
theorem uMsbHi_le_oneHot_of_validPlaneCtrlMuxD1NoNF {M D n : ℕ} (r : PlaneReg M D n)
    {β : BitAssignment n} (hC : ValidPlaneCtrlMuxD1NoNF r β) :
    (∀ d : Fin D, 1 ≤ d.val → β (pUMsb r d) = 0) ∨ (∃ dS : Fin D, 1 ≤ dS.val ∧ ∀ d : Fin D, 1 ≤
        d.val → β (pUMsb r d) = if d = dS then 1 else 0) := by
  have hu : ∀ d : Fin D, toggleNotFlags r β (pUMsb r d) = β (pUMsb r d) := fun _ ↦
      toggleNotFlags_other r β (fun _ ↦ pr_ne r (by dsimp; omega))
      (fun _ ↦ pr_ne r (by dsimp; omega))
  exact (uMsbHi_le_oneHot_of_validPlaneCtrlMuxD1 r hC).imp (fun h0 d hd1 ↦
      (hu d).symm.trans (h0 d hd1)) fun ⟨dS, hdS1, h1⟩ ↦
      ⟨dS, hdS1, fun d hd1 ↦ (hu d).symm.trans (h1 d hd1)⟩
/- ## Part 1: Multi-Plane `SubspaceStep` for `pDualBellPlanesMuxD1CHDiffNoNFMD` -/
def swapIdx12Alias (M D i : ℕ) : ℕ :=
    swapPair 2 (basePub M D + 6) (2 * D) (swapPair 1 (basePub M D + 1) 1 i)
theorem swapIdx12Alias_lt {M D i : ℕ} (hi : i < routerWidth M D) : swapIdx12Alias M D i <
    routerWidth M D :=
  swapPair_lt (by unfold routerWidth; omega) (by unfold routerWidth basePub; omega)
    (swapPair_lt (by unfold routerWidth; omega) (by unfold routerWidth basePub; omega) hi)

theorem swapIdx12Alias_invol {M D i : ℕ} : swapIdx12Alias M D (swapIdx12Alias M D i) = i := by
  unfold swapIdx12Alias
  rw [← swapPair_comm (by omega) (by unfold basePub; omega) (by unfold basePub; omega)
      (by unfold basePub; omega), swapPair_invol (Or.inl (by unfold basePub; omega)),
      swapPair_invol (Or.inl (by unfold basePub; omega))]
/--
`RouterReg` view aliasing `rHas2Eff` to `rRawHas2 r` and `(rNotMin, rNotMax)` directly to
`(rIdx1 r, rIdx2 r)`, leaving `[basePub + 1]` and `[basePub + 6 .. basePub + 6 + 2 * D)` untouched.
-/
def rIdx12Alias {M D n : ℕ} (r : RouterReg M D n) : RouterReg M D n :=
    routerOfInvol r (swapIdx12Alias M D) (fun _ hi ↦ swapIdx12Alias_lt hi)
    (fun _ _ ↦ swapIdx12Alias_invol)
theorem planeOfRouter_rIdx12Alias_apply_of_ne {M D n : ℕ} (r : RouterReg M D n) (b : Fin 24)
    (i : Fin (planeWidth M D))
    (hi1 : i.val ≠ 1) (hiNF : ¬ (8 + D ≤ i.val ∧ i.val < 8 + 3 * D)) :
        planeOfRouter (rIdx12Alias r) b i = planeOfRouter r b i := by
  have _ : _ ∧ _ := ⟨b.isLt, i.isLt⟩
  have hp : (planeIdxVal M D b i.val < 2 ∧ planeIdxVal M D b i.val ≠ 1 ∨ 2 + 2 * D ≤
      planeIdxVal M D b i.val) ∧
      (planeIdxVal M D b i.val < basePub M D + 6 ∧ planeIdxVal M D b i.val ≠ basePub M D + 1 ∨
        basePub M D + 6 + 2 * D ≤ planeIdxVal M D b i.val) := by
    dsimp only [planeWidth, planeIdxVal, planeIdxFixed, planeIdxD, planeIdxM, basePub] at *
    split_ifs <;> omega
  exact congrArg r.wires (Fin.ext (show swapPair 2 _ _ (swapPair 1 _ _ (planeIdxVal M D b i.val)) =
      planeIdxVal M D b i.val from (congrArg (swapPair 2 (basePub M D + 6) (2 * D))
    (swapPair_fixed (a := 1) (by omega) (by omega))).trans (swapPair_fixed (by omega) (by omega))))
set_option maxHeartbeats 800000 in
-- Simultaneous 14-field router-plane role equality reduction exceeds 200k heartbeats.
theorem planeOfRouter_rIdx12Alias_roles {M D n : ℕ} (r : RouterReg M D n)
    (b : Fin 24) : pHas1 (planeOfRouter (rIdx12Alias r) b) = rHas1 r ∧
    pHas2Eff (planeOfRouter (rIdx12Alias r) b) = rRawHas2 r ∧
    pOnly1 (planeOfRouter (rIdx12Alias r) b) = rOnly1 r ∧ pBufLo (planeOfRouter (rIdx12Alias r) b) =
        pBufLo (planeOfRouter r b) ∧
    pBufHi (planeOfRouter (rIdx12Alias r) b) = pBufHi (planeOfRouter r b) ∧
        pHA (planeOfRouter (rIdx12Alias r) b) = pHA (planeOfRouter r b) ∧
    pHB (planeOfRouter (rIdx12Alias r) b) = pHB (planeOfRouter r b) ∧
        pAnc (planeOfRouter (rIdx12Alias r) b) = rAnc r ∧ pUMsb (planeOfRouter (rIdx12Alias r) b) =
        rUMsb r ∧ pNotMin (planeOfRouter (rIdx12Alias r) b) = rIdx1 r ∧
    pNotMax (planeOfRouter (rIdx12Alias r) b) = rIdx2 r ∧ pAMsb (planeOfRouter (rIdx12Alias r) b) =
        rAMsb r ∧ pCReg (planeOfRouter (rIdx12Alias r) b) = rCReg r ∧
        pCtrlLo (planeOfRouter (rIdx12Alias r) b) = rCtrlLo r ∧
    pCtrlHi (planeOfRouter (rIdx12Alias r) b) = rCtrlHi r ∧ pSys (planeOfRouter (rIdx12Alias r) b) =
        pSys (planeOfRouter r b) := by
  have fx (i) (h1 : i.val ≠ 1 := by dsimp <;> omega)
      (h2 : ¬ (8 + D ≤ i.val ∧ i.val < 8 + 3 * D) := by dsimp <;> omega) :=
    planeOfRouter_rIdx12Alias_apply_of_ne r b i h1 h2
  have rEq {i j : Fin (routerWidth M D)} (h : i.val = j.val) : r i = r j :=
      congrArg r.wires (Fin.ext h)
  have swD (off : ℕ) (d : Fin D) (ho : off = 0 ∨ off = D) :
      swapIdx12Alias M D (planeIdxVal M D b (8 + D + off + d.val)) = 2 + off + d.val := by
    have := d.isLt
    rw [show planeIdxVal M D b (8 + D + off + d.val) = basePub M D + 6 + off + d.val by
      dsimp only [planeIdxVal, planeIdxD, basePub]
      split_ifs <;> omega,
      swapIdx12Alias, swapPair_fixed (a := 1) (Or.inr (by omega)) (Or.inr (by omega))]
    dsimp only [swapPair, basePub]
    split_ifs <;> omega
  exact ⟨(fx _).trans (rEq rfl), congrArg r.wires (Fin.ext (by
      change swapIdx12Alias M D (planeIdxVal M D b 1) = 1
      dsimp only [planeIdxVal, planeIdxFixed, swapPair, swapIdx12Alias, basePub]
      split_ifs <;>
          omega)),
    (fx _).trans (rEq (by simp [planeIdxVal, planeIdxFixed])), fx _, fx _, fx _, fx _,
    (fx _).trans (rEq (by simp [planeIdxVal, planeIdxFixed])),
    funext fun d ↦
        (fx _ (h2 := (fun _ ↦ by
          dsimp
          omega) d.isLt)).trans (planeOfRouter_uMsb r b d),
    funext fun d ↦ congrArg r.wires (Fin.ext (by simpa only [add_zero] using swD 0 d (.inl rfl))),
    funext fun d ↦ congrArg r.wires (Fin.ext (by
      simpa only [show 8 + D + D + d.val = 8 + 2 * D + d.val by omega] using swD D d (.inr rfl))),
    funext fun d ↦ (fx _).trans (planeOfRouter_aMsb r b d), funext fun d ↦
        (fx _).trans (planeOfRouter_cReg r b d),
    (funext fun _ ↦ fx _).trans (planeOfRouter_ctrlLo r b),
    (funext fun _ ↦ fx _).trans (planeOfRouter_ctrlHi r b), funext fun _ ↦ fx _⟩
end QuantumComputation.Specs.PhotochemistrySolution.Stage2ChDiffNoNF
end
end

noncomputable section
namespace QuantumComputation.Specs.PhotochemistrySolution.Stage1AsymRevEngine
open PhotochemistrySolution.ZeroNEremSpec
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CoinWrap (oddBits xagEnv)
/- ## Section 1: Pre-CNOT Transform & Pure-Zero Invariant on `ZeroNEremSector` -/
/-- Exact 19-CNOT pre-reduction bit transform on 40-bit Stage-1 output mask `m`. -/
def preCnotBit40 (m : ℕ) (j : ℕ) : Bool :=
    if j == 35 then xor (m.testBit 35) (m.testBit 1) else if j == 32 then xor (m.testBit 32)
    (xor (m.testBit 15) (m.testBit 1)) else if j == 34 then xor (m.testBit 34) (xor (m.testBit 0)
    (m.testBit 14)) else if Nat.ble 16 j && Nat.ble (j + 1) 24 then xor (m.testBit j)
    (m.testBit (j + 8)) else if Nat.ble 2 j && Nat.ble (j + 1) 8 then xor (m.testBit j)
    (m.testBit (j + 6)) else m.testBit j
theorem testBit_ite_one_zero (b : Bool) (d : ℕ) : (if b then 1 else 0).testBit d = if d =
    0 then b else false := by
  cases b <;> cases d <;> simp [Nat.testBit_succ]

theorem testBit_flag_shift (b : Bool) (s k : ℕ) : ((if b then 1 else 0) <<< s).testBit k = if k =
    s then b else false := by
  by_cases hge : k ≥ s
  · simp [Nat.testBit_shiftLeft, hge, testBit_ite_one_zero, show (k - s = 0) ↔ k = s by omega]
  · simp [Nat.testBit_shiftLeft, hge, show k ≠ s by omega]

theorem testBit_mask_shift_out (x mask w s k : ℕ) (hm : mask < 2 ^ w) (hk : k < s ∨ s + w ≤ k) :
    ((x &&& mask) <<< s).testBit k = false := by
  exact hk.elim (fun h ↦ by simp [Nat.testBit_shiftLeft, Nat.not_le_of_gt h]) fun h ↦ by
    simp [Nat.testBit_shiftLeft, show k ≥ s by omega, Nat.testBit_and,
      Nat.testBit_lt_two_pow (hm.trans_le (Nat.pow_le_pow_right (by decide) (by omega)) : mask <
          2 ^ (k - s))]

theorem testBit_packOut40_outside_fields
    (hasN1 hasN2 : Bool) (n1 n2 : ℕ) (hasE1 hasE2 : Bool) (e1 e2 : ℕ)
    (isScreen isPot isKin isNN : Bool) (sp1 aux2 k : ℕ)
    (hk1 : k < 2 ∨ 8 ≤ k) (hk2 : k < 8 ∨ 14 ≤ k)
    (hk3 : k < 16 ∨ 24 ≤ k) (hk4 : k < 24 ∨ 32 ≤ k)
    (hk5 : k < 36) :
    (packOut40ZeroNErem hasN1 hasN2 n1 n2 hasE1 hasE2 e1 e2
      isScreen isPot isKin isNN sp1 aux2).testBit k =
    ((if k = 0 then hasN1 else false) ||
     (if k = 1 then hasN2 else false) ||
     (if k = 14 then hasE1 else false) ||
     (if k = 15 then hasE2 else false) ||
     (if k = 32 then isScreen else false) ||
     (if k = 33 then isPot else false) ||
     (if k = 34 then isKin else false) ||
     (if k = 35 then isNN else false)) := by
  have ms (x mask w s : ℕ) (hk : k < s ∨ s + w ≤ k) (hm : mask < 2 ^ w := by
    decide) := testBit_mask_shift_out x mask w s k hm hk
  simp only [packOut40ZeroNErem, Nat.testBit_or, ms n1 63 6 2 hk1, ms n2 63 6 8 hk2,
      ms e1 255 8 16 hk3, ms e2 255 8 24 hk4,
    ms sp1 3 2 36 (Or.inl hk5), ms aux2 3 2 38 (Or.inl (by omega)), testBit_ite_one_zero,
        testBit_flag_shift, Bool.or_false]
theorem testBit_packOut40_flags
    (b0 b1 : Bool) (n1 n2 : ℕ) (b14 b15 : Bool) (e1 e2 : ℕ)
    (b32 b33 b34 b35 : Bool) (sp1 aux2 : ℕ) :
    let m := packOut40ZeroNErem b0 b1 n1 n2 b14 b15 e1 e2 b32 b33 b34 b35 sp1 aux2
    m.testBit 0 = b0 ∧ m.testBit 1 = b1 ∧ m.testBit 14 = b14 ∧ m.testBit 15 = b15 ∧ m.testBit 32 =
        b32 ∧ m.testBit 34 = b34 ∧ m.testBit 35 = b35 := by
  have f (k : ℕ) (h1 : k < 2 ∨ 8 ≤ k := by
    omega) (h2 : k < 8 ∨ 14 ≤ k := by
      omega) (h3 : k < 16 ∨ 24 ≤ k := by
        omega) (h4 : k < 24 ∨ 32 ≤ k := by omega) (h5 : k < 36 := by omega) :=
    testBit_packOut40_outside_fields b0 b1 n1 n2 b14 b15 e1 e2 b32 b33 b34 b35 sp1 aux2 k h1 h2 h3
        h4 h5
  simp [f 0, f 1, f 14, f 15, f 32, f 34, f 35]
/-- After `pre_cnots`, output bits `35, 32, 34` vanish identically on every `ZeroNEremSector`. -/
theorem preCnotBit40_zeroNErem_pureZero (s : ZeroNEremSector) :
    preCnotBit40 (zeroNEremOutMask s) 35 = false ∧
      preCnotBit40 (zeroNEremOutMask s) 32 = false ∧
      preCnotBit40 (zeroNEremOutMask s) 34 = false := by
  have go {b0 b1 : Bool} {n1 n2 : ℕ} {b14 b15 : Bool} {e1 e2 : ℕ} {b32 b33 b34 b35 : Bool}
      {sp1 aux2 m : ℕ}
      (hm : m = packOut40ZeroNErem b0 b1 n1 n2 b14 b15 e1 e2 b32 b33 b34 b35 sp1 aux2)
      (h : (xor b35 b1 = false) ∧ (xor b32 (xor b15 b1) = false) ∧ (xor b34 (xor b0 b14) = false)) :
      preCnotBit40 m 35 = false ∧ preCnotBit40 m 32 = false ∧ preCnotBit40 m 34 = false := by
    obtain ⟨h0, h1, h14, h15, h32, h34, h35⟩ :=
        testBit_packOut40_flags b0 b1 n1 n2 b14 b15 e1 e2 b32 b33 b34 b35 sp1 aux2
    simpa [hm, preCnotBit40, h0, h1, h14, h15, h32, h34, h35] using h
  cases s <;> dsimp only [zeroNEremOutMask] <;> try split_ifs
  all_goals first | decide | exact go rfl (by decide)

/- ## Section 2: First-pass (`mid32OutIdx`) & Second-pass (`tail5OutIdx`) Output Partition -/
/-- Second-pass tail output indices `[15, 1, 33, 14, 0]` on `rOut40Layout`. -/
def tail5OutIdx (s : Fin 5) : ℕ :=
  if s.val == 0 then 15
  else if s.val == 1 then 1
  else if s.val == 2 then 33
  else if s.val == 3 then 14
  else 0
/-- First-pass middle output indices `[24..31, 16..23, 8..13, 2..7, 36..39]` on `rOut40Layout`. -/
def mid32OutIdx (i : Fin 32) : ℕ :=
    if Nat.ble (i.val + 1) 8 then 24 + i.val else if Nat.ble (i.val + 1) 16 then 8 +
    i.val else if Nat.ble (i.val + 1) 22 then i.val - 8 else if Nat.ble (i.val + 1) 28 then i.val -
    20 else 8 + i.val
theorem tail5OutIdx_lt40 (s : Fin 5) : tail5OutIdx s < 40 := by fin_cases s <;> decide
theorem mid32OutIdx_lt40 (i : Fin 32) : mid32OutIdx i < 40 := by fin_cases i <;> decide
theorem tail5OutIdx_injective : Function.Injective tail5OutIdx := by decide
theorem mid32OutIdx_injective : Function.Injective mid32OutIdx := by decide
theorem mid32_ne_tail5 (i : Fin 32) (s : Fin 5) : mid32OutIdx i ≠ tail5OutIdx s := by
  decide +revert
theorem out40_partition (j : Fin 40) :
    j.val = 35 ∨ j.val = 32 ∨ j.val = 34 ∨
      (∃ i : Fin 32, mid32OutIdx i = j.val) ∨ (∃ s : Fin 5, tail5OutIdx s = j.val) := by
  decide +revert
/- ## Section 3: Predictor Bit Functions & Factored Bilinear Compiler -/
/--
First-pass `(49 + M)`-wire predictor bit (`0 = 1`, `1..41 = coin`, `42..41+M = work`,
`42+M..46+M = tail5`, `47+M..48+M = tmp0, tmp1`).
-/
def midPredBit (M : ℕ) (coreGates : Fin M → ℕ × ℕ) (coreMask0 coreMask1 : ℕ) (c : Fin (2 ^ 41))
    (m40 : ℕ) (u : ℕ) : Bool :=
  let env := xagEnv c.val M coreGates M le_rfl
  if Nat.ble (u + 1) (42 + M) then env.testBit u
  else if u == 42 + M then preCnotBit40 m40 15
  else if u == 43 + M then preCnotBit40 m40 1
  else if u == 44 + M then preCnotBit40 m40 33
  else if u == 45 + M then preCnotBit40 m40 14
  else if u == 46 + M then preCnotBit40 m40 0
  else if u == 47 + M then preCnotBit40 m40 15 && oddBits (env &&& coreMask0) (42 + M)
  else if u == 48 + M then preCnotBit40 m40 1 && oddBits (env &&& coreMask1) (42 + M)
  else false
/--
Second-pass `(47 + M)`-wire predictor bit (`0 = 1`, `1..41 = coin`, `42..41+M = work`,
`42+M..46+M = tail5`).
-/
def tailPredBit (M : ℕ) (coreGates : Fin M → ℕ × ℕ) (c : Fin (2 ^ 41)) (m40 : ℕ) (u : ℕ) : Bool :=
  let env := xagEnv c.val M coreGates M le_rfl
  if Nat.ble (u + 1) (42 + M) then env.testBit u
  else if u == 42 + M then preCnotBit40 m40 15
  else if u == 43 + M then preCnotBit40 m40 1
  else if u == 44 + M then preCnotBit40 m40 33
  else if u == 45 + M then preCnotBit40 m40 14
  else if u == 46 + M then preCnotBit40 m40 0
  else false
theorem tailPredBit_zero (M : ℕ) (coreGates : Fin M → ℕ × ℕ) (c : Fin (2 ^ 41))
    (m40 : ℕ) : tailPredBit M coreGates c m40 0 = true := by
  simpa only [tailPredBit, Nat.ble_eq_true_of_le (by omega : 1 ≤ 42 + M), ↓reduceIte] using
    (CoinWrap.xagEnv_invariant c M coreGates M le_rfl).1
theorem midPredBit_zero (M : ℕ) (coreGates : Fin M → ℕ × ℕ) (coreMask0 coreMask1 : ℕ)
    (c : Fin (2 ^ 41)) (m40 : ℕ) :
    midPredBit M coreGates coreMask0 coreMask1 c m40 0 = true := by
  simpa only [midPredBit, tailPredBit, Nat.ble_eq_true_of_le (by omega : 1 ≤ 42 + M),
      ↓reduceIte] using
    tailPredBit_zero M coreGates c m40
/-- Pure `Bool` quadratic `CZ`-pair parity `⊕_{(a, b) ∈ pairs} (bitOf a && bitOf b)`. -/
def pairsParityBool (bitOf : ℕ → Bool) : List (ℕ × ℕ) → Bool
  | [] => false
  | p :: ps => xor (bitOf p.1 && bitOf p.2) (pairsParityBool bitOf ps)
/-- Check `a < b < bound` on every `(a, b) ∈ pairs`. -/
def checkPairsBound (bound : ℕ) : List (ℕ × ℕ) → Bool
  | [] => true
  | p :: ps => Nat.ble (p.1 + 1) p.2 && Nat.ble (p.2 + 1) bound && checkPairsBound bound ps
/-- Pure `Bool` linear parity `⊕_{u ∈ us} bitOf u`. -/
def listXorBool (bitOf : ℕ → Bool) : List ℕ → Bool
  | [] => false
  | u :: us => xor (bitOf u) (listXorBool bitOf us)
/--
Factored bilinear parity `⊕_{(lhs, rhs) ∈ terms} ((⊕_{a ∈ lhs} bitOf a) && (⊕_{b ∈ rhs} bitOf b))` .
-/
def evalBilinearBool (bitOf : ℕ → Bool) : List (List ℕ × List ℕ) → Bool
  | [] => false
  | t :: ts => xor (listXorBool bitOf t.1 && listXorBool bitOf t.2) (evalBilinearBool bitOf ts)
def checkListLt (bound : ℕ) : List ℕ → Bool
  | [] => true
  | u :: us => Nat.ble (u + 1) bound && checkListLt bound us
def checkNoZeroZero : List ℕ → List ℕ → Bool
  | [], _ => true
  | a :: as, bs =>
      (if a == 0 then bs.all (fun b ↦ Bool.not (b == 0)) else true) && checkNoZeroZero as bs
/--
Well-formedness check for factored bilinear terms (`a < bound`, `b < bound` , `(a, b) ≠ (0, 0)` ).
-/
def checkBilinearTerms (bound : ℕ) : List (List ℕ × List ℕ) → Bool
  | [] => true
  | t :: ts =>
      checkListLt bound t.1 && checkListLt bound t.2 &&
      checkNoZeroZero t.1 t.2 && checkBilinearTerms bound ts
def togglePair (p : ℕ × ℕ) : List (ℕ × ℕ) → List (ℕ × ℕ)
  | [] => [p]
  | q :: qs => if p.1 == q.1 && p.2 == q.2 then qs else q :: togglePair p qs
def addProdPair (a b : ℕ) (acc : List (ℕ × ℕ)) : List (ℕ × ℕ) :=
    if a == b then if a == 0 then acc else togglePair (0, a) acc else if Nat.ble (a +
    1) b then togglePair (a, b) acc else togglePair (b, a) acc
def addRowPairs (a : ℕ) : List ℕ → List (ℕ × ℕ) → List (ℕ × ℕ)
  | [], acc => acc
  | b :: bs, acc => addRowPairs a bs (addProdPair a b acc)
def addBlockPairs : List ℕ → List ℕ → List (ℕ × ℕ) → List (ℕ × ℕ)
  | [], _, acc => acc
  | a :: as, bs, acc => addBlockPairs as bs (addRowPairs a bs acc)
/-- Compile factored bilinear terms into cancelled strict-upper-triangular `(a < b)` pairs. -/
def compileBilinearPairs : List (List ℕ × List ℕ) → List (ℕ × ℕ)
  | [] => []
  | t :: ts => addBlockPairs t.1 t.2 (compileBilinearPairs ts)
theorem togglePair_spec {bound : ℕ} (bitOf : ℕ → Bool) {p : ℕ × ℕ}
    (hp : (Nat.ble (p.1 + 1) p.2 && Nat.ble (p.2 + 1) bound) = true) :
    ∀ ps : List (ℕ × ℕ), checkPairsBound bound ps = true →
      checkPairsBound bound (togglePair p ps) = true ∧
      pairsParityBool bitOf (togglePair p ps) =
        xor (bitOf p.1 && bitOf p.2) (pairsParityBool bitOf ps)
  | [], _ =>
        ⟨by simpa [togglePair, checkPairsBound] using hp, by simp [togglePair, pairsParityBool]⟩
  | q :: qs, hps => by
      obtain ⟨hq, hqs⟩ := Bool.and_eq_true_iff.mp hps
      obtain ⟨ihB, ihP⟩ := togglePair_spec bitOf hp qs hqs
      by_cases heq : (p.1 == q.1 && p.2 == q.2) = true
      · have hqp : p.1 = q.1 ∧ p.2 = q.2 := by simpa [Bool.and_eq_true, beq_iff_eq] using heq
        simp only [togglePair, pairsParityBool, ← hqp.1, ← hqp.2]
        cases bitOf p.1 && bitOf p.2 <;> simp [hqs]
      · simp only [togglePair, Bool.eq_false_iff.mpr heq, Bool.false_eq_true, ↓reduceIte,
          checkPairsBound, hq, ihB, Bool.and_self, pairsParityBool, ihP, true_and]
        cases bitOf q.1 && bitOf q.2 <;> cases bitOf p.1 && bitOf p.2 <;> simp

theorem addProdPair_spec {bound a b : ℕ} (bitOf : ℕ → Bool) (h0 : bitOf 0 = true)
    (ha : Nat.ble (a + 1) bound = true) (hb : Nat.ble (b + 1) bound = true)
    (hzz : ¬(a = 0 ∧ b = 0)) (acc : List (ℕ × ℕ)) (hacc : checkPairsBound bound acc = true) :
    checkPairsBound bound (addProdPair a b acc) = true ∧
        pairsParityBool bitOf (addProdPair a b acc) = xor (bitOf a && bitOf b)
        (pairsParityBool bitOf acc) := by
  have ⟨_, _⟩ := And.intro (Nat.le_of_ble_eq_true ha) (Nat.le_of_ble_eq_true hb)
  have tog (x y : ℕ) (hy : Nat.ble (y + 1) bound = true) (hxy : x < y := by omega) :=
    togglePair_spec bitOf (p := (x, y)) (Bool.and_eq_true_iff.mpr ⟨Nat.ble_eq_true_of_le hxy,
        hy⟩) acc hacc
  dsimp only [addProdPair]
  by_cases hab : a = b
  · subst hab
    simp only [beq_self_eq_true, ↓reduceIte, beq_false_of_ne fun e ↦ hzz ⟨e, e⟩,
      Bool.false_eq_true, (tog 0 a ha).1, (tog 0 a ha).2, h0, true_and]
    cases bitOf a <;> simp
  · by_cases hlt : a < b
    · simpa only [beq_false_of_ne hab, Bool.false_eq_true, Nat.ble_eq_true_of_le hlt,
          ↓reduceIte] using tog a b hb
    · simp [beq_false_of_ne hab, Bool.eq_false_iff.mpr fun h ↦ hlt (Nat.le_of_ble_eq_true h),
        (tog b a ha).1, (tog b a ha).2, Bool.and_comm]

theorem addRowPairs_spec {bound a : ℕ} (bitOf : ℕ → Bool) (h0 : bitOf 0 = true)
    (ha : Nat.ble (a + 1) bound = true) :
    ∀ (bs : List ℕ) (acc : List (ℕ × ℕ)),
      checkListLt bound bs = true →
      (if a == 0 then bs.all (fun b ↦ Bool.not (b == 0)) else true) = true →
      checkPairsBound bound acc = true →
      checkPairsBound bound (addRowPairs a bs acc) = true ∧
      pairsParityBool bitOf (addRowPairs a bs acc) =
        xor (bitOf a && listXorBool bitOf bs) (pairsParityBool bitOf acc)
  | [], acc, _, _, hacc => ⟨hacc, by simp [addRowPairs, listXorBool]⟩
  | b :: bs, acc, hbs, hno0, hacc => by
      obtain ⟨hb1, hbs2⟩ := Bool.and_eq_true_iff.mp hbs
      obtain ⟨ha1, hp1⟩ :=
          addProdPair_spec bitOf h0 ha hb1 (fun ⟨ea, eb⟩ ↦ by simp [ea, eb] at hno0) acc hacc
      obtain ⟨ha2, hp2⟩ :=
          addRowPairs_spec bitOf h0 ha bs _ hbs2 (by split_ifs at hno0 ⊢ <;> simp_all) ha1
      exact ⟨ha2, (hp2.trans (congrArg (xor _) hp1)).trans
        ((by decide : ∀ x y z w : Bool, xor (x && z)
            (xor (x && y) w) = xor (x && xor y z) w) _ _ _ _)⟩

theorem addBlockPairs_spec {bound : ℕ} (bitOf : ℕ → Bool) (h0 : bitOf 0 = true) :
    ∀ (as bs : List ℕ) (acc : List (ℕ × ℕ)),
      checkListLt bound as = true →
      checkListLt bound bs = true →
      checkNoZeroZero as bs = true →
      checkPairsBound bound acc = true →
      checkPairsBound bound (addBlockPairs as bs acc) = true ∧
      pairsParityBool bitOf (addBlockPairs as bs acc) =
        xor (listXorBool bitOf as && listXorBool bitOf bs) (pairsParityBool bitOf acc)
  | [], _, acc, _, _, _, hacc => ⟨hacc, by simp [addBlockPairs, listXorBool]⟩
  | a :: as, bs, acc, has, hbs, hzz, hacc => by
      obtain ⟨ha1, has2⟩ := Bool.and_eq_true_iff.mp has
      obtain ⟨hz1, hzz2⟩ := Bool.and_eq_true_iff.mp hzz
      obtain ⟨haR, hpR⟩ := addRowPairs_spec bitOf h0 ha1 bs acc hbs hz1 hacc
      obtain ⟨haB, hpB⟩ := addBlockPairs_spec bitOf h0 as bs _ has2 hbs hzz2 haR
      exact ⟨haB, (hpB.trans (congrArg (xor _) hpR)).trans
        ((by decide : ∀ x y z w : Bool, xor (z && y)
            (xor (x && y) w) = xor (xor x z && y) w) _ _ _ _)⟩

theorem compileBilinearPairs_spec {bound : ℕ} (bitOf : ℕ → Bool) (h0 : bitOf 0 = true) :
    ∀ terms : List (List ℕ × List ℕ),
      checkBilinearTerms bound terms = true →
      checkPairsBound bound (compileBilinearPairs terms) = true ∧
      pairsParityBool bitOf (compileBilinearPairs terms) = evalBilinearBool bitOf terms
  | [], _ => ⟨rfl, rfl⟩
  | t :: ts, hok => by
      rcases (by simpa only [checkBilinearTerms, Bool.and_eq_true] using hok) with ⟨⟨⟨hl, hr⟩, hzz⟩,
          hrest⟩
      obtain ⟨hbR, hpR⟩ := compileBilinearPairs_spec bitOf h0 ts hrest
      obtain ⟨hbA, hpA⟩ := addBlockPairs_spec bitOf h0 t.1 t.2 _ hl hr hzz hbR
      exact ⟨hbA, hpA.trans (hpR ▸ rfl)⟩
end QuantumComputation.Specs.PhotochemistrySolution.Stage1AsymRevEngine
end

section

open QuantumComputation.Specs.PhotochemistrySolution.Stage4KinFull
  QuantumComputation.Specs.PhotochemistrySolution.TargetBScr
noncomputable section
open Operator QProg Matrix Circuit Qubit QuantumComputation.Specs
  QuantumComputation.Specs.PhotochemistrySolution
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
open QuantumComputation.Specs.PhotochemistrySolution.SelectOracles
  QuantumComputation.Specs.PhotochemistrySolution.RouterSelectWiringA
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB (ket)
attribute [local irreducible]
    QuantumComputation.Specs.PhotochemistrySolution.SelectCompactAnc.ancWOfScr
namespace QuantumComputation.Specs.PhotochemistrySolution.PotSelectWiring
open PhotochemistrySolution.KetSupport PhotochemistrySolution.SplitRouter47_187
  PhotochemistrySolution.RouterSelectWiringB PhotochemistrySolution.Stage12Compact
open PhotochemistrySolution.ZeroNEremSpec PhotochemistrySolution.SelectApprox
open _root_.DynamicCircuit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt hiding bit_cases
  eval_seq_mulVec ket ket_CNOT ket_TOFF ket_X ket_projector_one ket_projector_zero matrix_ext_ket
  qAssign_obs_map_val
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SelectCompactAnc (ancWOfScr)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SelectDataBuilder
  (embedMatrix_mulVec_ket_sym)
attribute [local irreducible] systemQubits_frozen PgBase.phaseGradientState abpKin14Usel
theorem mulVec_chain3 {N : ℕ} (A B C : Matrix (Fin N) (Fin N) ℂ) (v₁ v₂ v₃ : Fin N → ℂ) (c : ℂ)
    (hC : C.mulVec v₁ = v₂) (hB : B.mulVec v₂ = c • v₃) : (A * B * C).mulVec v₁ =
    c • A.mulVec v₃
    := by rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hC, hB, Matrix.mulVec_smul]
theorem embed_diagReal_mulVec_ket {s d : ℕ} [NeZero (2 ^ s)] [NeZero (2 ^ d)] (r : QRegister s d)
    (g : Fin (2 ^ s) → ℝ) (β : BitAssignment d) : (r.embedMatrix (diagReal g)).mulVec (ket β) =
    (g (KinB.localIdx r β) : ℂ) • ket β := by
  let x := PhotochemistrySolution.KinB.localIdx r β
  have hidx : PhotochemistrySolution.SelectDataBuilder.readRegIdx r β = x :=
    congrArg (basisBitsEquiv s).symm (funext fun j ↦
        congrFun ((basisBitsEquiv d).apply_symm_apply β) (r.wires j))
  have hwrt : DynCircExt.writeReg β r (basisBits s x) = β := funext fun w ↦ by
    by_cases hw : ∃ j : Fin s, w = r j
    · obtain ⟨j, rfl⟩ := hw
      exact (DynCircExt.writeReg_apply_reg β r _ j).trans
          (congrFun ((basisBitsEquiv s).apply_symm_apply (fun k ↦ β (r k))) j)
    · exact DynCircExt.writeReg_apply_of_not_mem β r _ w fun ⟨j, hj⟩ ↦ hw ⟨j, hj.symm⟩
  rw [embedMatrix_mulVec_ket_sym r (diagReal g) β, hidx,
    Finset.sum_eq_single x (fun y _ hne ↦
    by simp [diagReal, Matrix.diagonal_apply_ne _ hne]) (fun hx ↦ absurd (Finset.mem_univ x) hx),
    hwrt]
  simp [diagReal, x]
theorem h41_add_lt82 (k : Fin 41) : 41 + k.val < mLayout + 2 := by dsimp [mLayout]; omega
theorem rInner41_eq_lcu (k : Fin 41) : rInner41Layout k = rLcu82Layout ⟨41 + k.val,
    h41_add_lt82 k⟩ :=
  Fin.ext (by rw [val_rInner41Layout, val_rLcu82Layout]; dsimp; omega)
theorem writeReg_rInner41_lt7256 (α : BitAssignment dLayout) (z : BitAssignment 41)
    {u : Wire dLayout} (hu : u.val < 7256) : DynCircExt.writeReg α rInner41Layout z u = α u :=
  DynCircExt.writeReg_apply_of_not_mem _ _ _ u fun ⟨k, hk⟩ ↦ by
    rw [← hk, val_rInner41Layout] at hu; omega
theorem swapVecBits_writeReg_z :
    ∀ (k : ℕ) (a b : Fin k → Wire dLayout),
      (∀ i, (a i).val < 7256) → (∀ i, (b i).val < 7256) →
      ∀ (α : BitAssignment dLayout) (z : BitAssignment 41),
      swapVecBits k a b (DynCircExt.writeReg α rInner41Layout z) =
        DynCircExt.writeReg (swapVecBits k a b α) rInner41Layout z
  | 0, _, _, _, _, _, _ => rfl
  | k + 1, a, b, ha, hb, α, z => by
      dsimp only [swapVecBits]
      rw [swapVecBits_writeReg_z k _ _ (fun i ↦ ha i.castSucc) (fun i ↦ hb i.castSucc) α z]
      let β := swapVecBits k (fun i ↦ a i.castSucc) (fun i ↦ b i.castSucc) α
      funext w
      dsimp only [swapPairBits]
      have hwL {γ} {u : Wire dLayout} (hu : u.val < 7256) := writeReg_rInner41_lt7256 γ z hu
      rcases eq_or_ne w (a (Fin.last k)) with rfl | hwa
      · rw [Function.update_self, hwL (hb _), hwL (ha _), Function.update_self]
      · rcases eq_or_ne w (b (Fin.last k)) with rfl | hwb
        · rw [Function.update_of_ne hwa, Function.update_self, hwL (ha _), hwL (hb _),
              Function.update_of_ne hwa,
            Function.update_self]
        · rw [Function.update_of_ne hwa, Function.update_of_ne hwb]
          by_cases hw : w ∈ Set.range rInner41Layout.wires
          · obtain ⟨i, rfl⟩ := hw
            rw [DynCircExt.writeReg_apply_reg, DynCircExt.writeReg_apply_reg]
          · rw [DynCircExt.writeReg_apply_of_not_mem _ _ _ _ hw,
              DynCircExt.writeReg_apply_of_not_mem _ _ _ _ hw, Function.update_of_ne hwa,
                  Function.update_of_ne hwb]
theorem routerSwapBits_writeReg_z {M D : ℕ} (r : RouterReg M D dLayout)
    (hr : ∀ j : Fin (routerWidth M D), (r j).val < 7256) (α : BitAssignment dLayout)
        (z : BitAssignment 41) :
    routerSwapBits r (DynCircExt.writeReg α rInner41Layout z) =
      DynCircExt.writeReg (routerSwapBits r α) rInner41Layout z := by
  let αz := DynCircExt.writeReg α rInner41Layout z
  have heq_hdr (j : Fin (routerWidth M D)) : αz (r j) = α (r j) :=
      writeReg_rInner41_lt7256 α z (hr j)
  have hIdx (f : Fin D → Fin (routerWidth M D)) : idxValD (fun d ↦ r (f d)) αz = idxValD (fun d ↦
      r (f d)) α :=
    Nat.eq_of_testBit_eq fun d ↦
        by
          rw [testBit_idxValD, testBit_idxValD]
          split_ifs <;> simp only [heq_hdr]
  have hEff : routerHas2Eff r αz = routerHas2Eff r α := by
    rw [routerHas2Eff, routerHas2Eff, hIdx _, hIdx _, heq_hdr _]
  have hMin : routerIdxMinVal r αz = routerIdxMinVal r α := by
    rw [routerIdxMinVal, routerIdxMinVal, hEff, hIdx _, hIdx _]
  have hMax : routerIdxMaxVal r αz = routerIdxMaxVal r α := by
    rw [routerIdxMaxVal, routerIdxMaxVal, hEff, hIdx _, hIdx _]
  have step (buf : Fin 24 → Wire dLayout) (hb : ∀ b, (buf b).val < 7256)
      (fl : BitAssignment dLayout → ZMod 2)
      (ix : BitAssignment dLayout → ℕ) (δ : BitAssignment dLayout) (hfl : fl αz = fl α)
          (hix : ix αz = ix α) :
      (if h : fl αz = 1 ∧ ix αz < M then swapVecBits 24 buf (fun b ↦ rSys r ⟨ix αz, h.2⟩ b)
        (DynCircExt.writeReg δ rInner41Layout z) else DynCircExt.writeReg δ rInner41Layout
            z) =
      DynCircExt.writeReg (if h : fl α = 1 ∧ ix α < M then
        swapVecBits 24 buf (fun b ↦ rSys r ⟨ix α, h.2⟩ b) δ else δ) rInner41Layout z := by
    by_cases hc : fl α = 1 ∧ ix α < M
    · have hcz : fl αz = 1 ∧ ix αz < M := by rwa [hfl, hix]
      rw [dite_eq_left hcz, dite_eq_left hc, show (⟨_, hcz.2⟩ : Fin M) = ⟨_, hc.2⟩ from Fin.ext hix]
      exact swapVecBits_writeReg_z 24 _ _ hb (fun _ ↦ hr _) δ z
    · rw [dite_eq_right (by rwa [hfl, hix]), dite_eq_right hc]
  unfold routerSwapBits
  rw [show routerLoBits r αz = DynCircExt.writeReg (routerLoBits r α) rInner41Layout z from
    step (rBufLo r) (fun _ ↦ hr _) (fun γ ↦ γ (rHas1 r)) (routerIdxMinVal r) α (heq_hdr _) hMin]
  exact step (rBufHi r) (fun _ ↦ hr _) (routerHas2Eff r) (routerIdxMaxVal r) _ hEff hMax
end QuantumComputation.Specs.PhotochemistrySolution.PotSelectWiring

namespace QuantumComputation.Specs.PhotochemistrySolution.RouterSelectWiringB
open PhotochemistrySolution.Kinetic664 PrimitiveGate PhotochemistrySolution.SelectCompactAnc
  PhotochemistrySolution.SelectFastFlags
open PhotochemistrySolution.SelectStructuredCB PhotochemistrySolution.Stage4Kin14Scb
  PhotochemistrySolution.ProviderCore
open _root_.DynamicCircuit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt hiding ket ket_projector_zero
  matrix_ext_ket qAssign_obs_map_val
attribute [local reducible] totDimCompactGen
attribute [local irreducible] SpecDefs.systemQubits_frozen
  bSpeciesSwap50 PhotochemistrySolution.Stage4KinFull.bAxisMux27 abpKin14Usel
theorem rClean690Layout_proj_split_sqf : rClean690Layout.basisOutcomeProjector 0 =
    (rKin4.basisOutcomeProjector 0 * rPre165Align.basisOutcomeProjector 0) *
    rWorkInnerLayout.basisOutcomeProjector 0 := by
  have : NeZero (2 ^ dLayout) := ⟨pow_ne_zero dLayout two_ne_zero⟩
  refine KinB.matrix_ext_ket fun δ ↦ ?_
  rw [SelectRefl.ket_basisOutcomeProjector_zero, ← Matrix.mulVec_mulVec,
      SelectRefl.ket_basisOutcomeProjector_zero]
  have k4 (j : Fin 4) (u : Wire dLayout) (c : ℕ) (hc : c < 690 := by
    omega) (hu : (rKin4 j).val = u.val := by rfl)
      (hv : u.val = (rClean690Layout ⟨c, hc⟩).val := by
        rw [val_rAlignLayout, val_rClean690Layout] <;> decide) :
      rKin4 j = rClean690Layout ⟨c, hc⟩ := Fin.ext (hu.trans hv)
  have hk4_map : _ ∧ _ ∧ _ ∧ _ :=
      ⟨k4 0 wKinAxis0 142, k4 1 wKinAxis1 143, k4 2 wIsFineCopy 168, k4 3 wIsElecKin 144⟩
  have hEqv : (∀ m, δ (rClean690Layout m) = 0) ↔
      ((∀ j, δ (rKin4 j) = 0) ∧ (∀ i, δ (rPre165Align i) = 0)) ∧
          (∀ k, δ (rWorkInnerLayout k) = 0) := by
    refine ⟨fun h ↦ ⟨⟨?_, fun i ↦ ?_⟩, fun k ↦ ?_⟩, fun ⟨⟨hk4, hp⟩, hw⟩ m ↦ ?_⟩
    · exact fun
        | ⟨0, _⟩ =>
              (congrArg δ hk4_map.1).trans (h ⟨142,
              by omega⟩) | ⟨1, _⟩ => (congrArg δ hk4_map.2.1).trans (h ⟨143, by omega⟩)
        | ⟨2, _⟩ => (congrArg δ hk4_map.2.2.1).trans (h ⟨168, by omega⟩)
        | ⟨3, _⟩ => (congrArg δ hk4_map.2.2.2).trans (h ⟨144, by omega⟩)
    · rw [rPre165_apply]; dsimp only [pre165Fn]; split_ifs <;> exact h _
    · exact (congrArg δ (Fin.ext (by
        rw [val_rWorkInnerLayout, val_rClean690Layout]
        dsimp only
        split_ifs <;> omega) :
        rWorkInnerLayout k = rClean690Layout ⟨169 + k.val, by omega⟩)).trans (h _)
    · have hm_lt := m.isLt
      rcases (by omega : m.val < 142 ∨ m.val = 142 ∨ m.val = 143 ∨ m.val = 144 ∨
          (145 ≤ m.val ∧ m.val < 168) ∨ m.val = 168 ∨ 169 ≤ m.val) with hm | hm | hm | hm | ⟨_,
              _⟩ | hm | hm
      · exact (congrArg δ (by
          rw [rPre165_apply]
          dsimp only [pre165Fn]
          split_ifs <;> rfl :
              rClean690Layout
            m = rPre165Align ⟨m.val, by omega⟩)).trans (hp _)
      · exact (Fin.ext hm : m = ⟨142, by omega⟩) ▸ hk4_map.1 ▸ hk4 0
      · exact (Fin.ext hm : m = ⟨143, by omega⟩) ▸ hk4_map.2.1 ▸ hk4 1
      · exact (Fin.ext hm : m = ⟨144, by omega⟩) ▸ hk4_map.2.2.2 ▸ hk4 3
      · rw [show rClean690Layout m = rPre165Align ⟨m.val - 3, by omega⟩ from by
          rw [rPre165_apply]
          dsimp only [pre165Fn]
          rw [difNegSqf (by omega), difNegSqf (by omega)]
          exact congrArg rClean690Layout (Fin.ext (by
            simp only
            omega))]
        exact hp _
      · exact (Fin.ext hm : m = ⟨168, by omega⟩) ▸ hk4_map.2.2.1 ▸ hk4 2
      · exact (congrArg δ (Fin.ext
          (by
            rw [val_rClean690Layout, val_rWorkInnerLayout]
            dsimp only
            split_ifs <;>
                omega) : rClean690Layout
          m = rWorkInnerLayout ⟨m.val - 169, by omega⟩)).trans (hw _)
  by_cases hw : ∀ k : Fin 521, δ (rWorkInnerLayout k) = 0
  · rw [ifPosSqf hw, ← Matrix.mulVec_mulVec, SelectRefl.ket_basisOutcomeProjector_zero]
    by_cases hp : ∀ i : Fin 165, δ (rPre165Align i) = 0
    · rw [ifPosSqf hp, SelectRefl.ket_basisOutcomeProjector_zero]
      by_cases hk : ∀ j : Fin 4, δ (rKin4 j) = 0
      · rw [ifPosSqf hk, ifPosSqf (hEqv.mpr ⟨⟨hk, hp⟩, hw⟩)]
      · rw [ifNegSqf hk, ifNegSqf (fun ha ↦ hk (hEqv.mp ha).1.1)]
    · rw [ifNegSqf hp, ifNegSqf (fun ha ↦ hp (hEqv.mp ha).1.2), Matrix.mulVec_zero]
  · rw [ifNegSqf hw, ifNegSqf (fun ha ↦ hw (hEqv.mp ha).2), Matrix.mulVec_zero]
theorem writeReg_rInner41_kin226_keep_sqf (β : BitAssignment dLayout) (z : BitAssignment 41)
    (j : Fin 226) (hj : j.val < 8 ∨ 22 ≤ j.val) : writeReg β rInner41Layout z (rKin226Layout j) =
    β (rKin226Layout j) :=
  writeReg_apply_of_not_mem β rInner41Layout z _ fun ⟨m, hm⟩ ↦ by
    have hv : (rInner41Layout m).val = (kin226WireFn j).val := congrArg Fin.val hm
    rw [val_rInner41Layout, val_kin226WireFn] at hv; split_ifs at hv <;> omega
theorem rKin226_eq_rWorkInner_sqf (w : Wire 226) (hw : 25 ≤ w.val) :
    rKin226Layout w = rWorkInnerLayout ⟨22 + (w.val - 24), by have := w.isLt; omega⟩ := by
  have hwlt : 22 + (w.val - 24) < 521 := by have := w.isLt; omega
  apply Fin.ext; change (kin226WireFn w).val = (rWorkInnerLayout ⟨22 + (w.val - 24), hwlt⟩).val
  rw [val_kin226WireFn, val_rWorkInnerLayout]; dsimp; split_ifs <;> omega
theorem kOfBits8_congr_lt8_sqf (g₁ g₂ : BitAssignment 226) (h : ∀ j : Wire 226, j.val < 8 → g₁ j =
    g₂ j) : kOfBits8 g₁ = kOfBits8 g₂ := by
  have hpre : ∀ n ≤ 8, prefixSum (fun j ↦ g₁ (wKin j)) n = prefixSum (fun j ↦ g₂ (wKin j)) n := by
    intro n
    induction n with
    | zero => exact fun _ ↦ rfl
    | succ n ih =>
        refine fun hn ↦ ?_
        dsimp only [prefixSum]
        rw [ih (Nat.le_of_succ_le hn), h (wKin n) (by
          dsimp [wKin, finMod]
          omega)]
  dsimp only [kOfBits8]
  rw [hpre 8 le_rfl]
end QuantumComputation.Specs.PhotochemistrySolution.RouterSelectWiringB
end

section
namespace QuantumComputation.Specs.PhotochemistrySolution.Kinetic664
open Operator QProg DynamicCircuit Matrix Circuit Qubit QuantumComputation.Specs
  PhotochemistrySolution PhotochemistrySolution.SelectFastQft8Gidney
  PhotochemistrySolution.SelectFastFlags PhotochemistrySolution.SelectStructuredCB
  PhotochemistrySolution.Stage4Kin14Scb PhotochemistrySolution.UnembedO3Bridge
  PhotochemistrySolution.KineticFast
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
  _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB hiding writeReg
  writeReg_apply_of_not_mem ket ket_X ket_CNOT ket_TOFF matrix_ext_ket bitSign
open _root_.QuantumComputation.Specs.PhotochemistrySolution.QubitizationWalkSem (czCircuit
    czCircuit_mulVec_ket bitSign)
attribute [local semireducible] StructuredCB.validProgMask StructuredCB.finalCleanMask
theorem isPhaseDiag_and_valid_abpKin2m1 :
    IsPhaseDiag abpKin15SqFree2m1Usel.toCircuit.eval.1 kin2m1OutBit ∧
        ValidCleanBracket (maskFinset 226 sMask15SqFree2m1) abpKin15SqFree2m1Usel ∧
      IsPhaseDiag abpKin15SqFree2m1Csel.toCircuit.eval.1 (fun β ↦ β wLocQ226 * kin2m1OutBit β) ∧
        ValidCleanBracket (maskFinset 226 sMask15SqFree2m1) abpKin15SqFree2m1Csel ∧
      IsPhaseDiag abpKin14SqFree2m1Usel.toCircuit.eval.1 (fun β ↦ β wIsKin226 * kin2m1RawBit β) ∧
        ValidCleanBracket (maskFinset 226 sMask14SqFree2m1) abpKin14SqFree2m1Usel := by
  have av {w : Wire 226} {p : ComputeProg 226} (h : avoids226 (2 ^ w.val) p = true)
      (β : BitAssignment 226) :
      p.fwdBits β w = β w := (fwdBits_avoids (2 ^ w.val) p h).2 β w Nat.testBit_two_pow_self
  have wv {p : ComputeProg 226} {s : ℕ} (hp : StructuredCB.validProgMask 0 s p = true)
      (g : Circuit 226)
      (f : BitAssignment 226 → ZMod 2)
          (hg : IsPhaseDiag (AndBracketProg.prim g).toCircuit.eval.1 f) :
      IsPhaseDiag (p.wrap (.prim g)).toCircuit.eval.1 (fun β ↦ f (p.fwdBits β)) ∧
        ValidCleanBracket (maskFinset 226 s) (p.wrap (.prim g)) :=
    ⟨@IsPhaseDiag.wrap_computeProg 226 p (.prim g) f hg,
        @validCleanBracket_wrap_phase 226 p (maskFinset 226 s) (.prim g) f
      (maskFinset_zero 226 ▸ StructuredCB.validProg_of_validProgMask hp)
          (hg.preserves_cleanProj _) hg⟩
  obtain ⟨du, vu⟩ :=
      wv pKin2m1_props.2.2.2.1 (zGateCirc wOutKin226) (fun β ↦ β wOutKin226)
      (ket_zGateCirc wOutKin226)
  obtain ⟨dc, vc⟩ := wv pKin2m1_props.2.2.2.1 (czCircuit wLocQ226 wOutKin226 hq226_ne_out)
    (fun β ↦ β wLocQ226 * β wOutKin226) (czCircuit_mulVec_ket wLocQ226 wOutKin226 hq226_ne_out)
  obtain ⟨d14, v14⟩ := wv pKin2m1_props.2.2.1 (czCircuit wIsKin226 (wKin 68) hwIsKin226_ne_68)
    (fun β ↦ β wIsKin226 * β (wKin 68)) (czCircuit_mulVec_ket wIsKin226 (wKin 68) hwIsKin226_ne_68)
  exact ⟨du, vu,
    fun β ↦
        (dc β).trans (congrArg (fun x ↦ bitSign (x * kin2m1OutBit β) • DynCircExt.ket β)
        (av pKin2m1_props.2.2.2.2.1 β)), vc,
    fun β ↦
        (d14 β).trans (congrArg (fun x ↦ bitSign (x * kin2m1RawBit β) • DynCircExt.ket β)
        (av pKin2m1_props.2.2.2.2.2 β)), v14⟩
end QuantumComputation.Specs.PhotochemistrySolution.Kinetic664
end

section
namespace QuantumComputation.Specs.PhotochemistrySolution.RouterSelectWiringB
open Operator QProg Matrix Circuit Qubit PrimitiveGate DynamicCircuit QuantumComputation.Specs
  PhotochemistrySolution
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
  _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt
open PhotochemistrySolution.Stage4Kin14Scb PhotochemistrySolution.SelectOracles
  PhotochemistrySolution.RouterSelectWiringA PhotochemistrySolution.Kinetic664
open _root_.QuantumComputation.Specs.PhotochemistrySolution.QubitizationWalkSem (bitSign
    bitSign_zero bitSign_one)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SelectStructuredCB (finMod)
def extBits2m1 {k : ℕ} (x : BitAssignment k) (i : ℕ) : ZMod 2 := if hi : i < k then x ⟨i, hi⟩ else 0
def splitBitsTop2m1 (k : ℕ) : (BitAssignment k × ZMod 2) ≃ BitAssignment (k + 1) where
  toFun p j := if hj : j.val < k then p.1 ⟨j.val, hj⟩ else p.2
  invFun y := (fun i ↦ y ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩, y ⟨k, Nat.lt_succ_self k⟩)
  left_inv p := by
    rcases p with ⟨x, b⟩
    ext i
    · dsimp only; exact dite_eq_left i.isLt
    · dsimp only; exact dite_eq_right (Nat.lt_irrefl k)
  right_inv y := by
    funext j; dsimp only
    by_cases hj : j.val < k
    · exact dite_eq_left hj
    · rw [dite_eq_right hj]
      have hjk : k = j.val := by have := j.isLt; omega
      exact congrArg y (Fin.ext hjk)
theorem sum_fin_pow_succ_split_2m1 (k : ℕ) (g : ℕ → ℂ) : (∑ q : Fin (2 ^ (k + 1)), g q.val) =
    (∑ m : Fin (2 ^ k), g m.val) + (∑ m : Fin (2 ^ k), g (m.val + 2 ^ k)) := by
  rw [← Equiv.sum_comp (finCongr (show 2 ^ k + 2 ^ k =
      2 ^ (k + 1) by rw [Nat.pow_succ, Nat.mul_two])), Fin.sum_univ_add]
  exact congrArg₂ _ (Finset.sum_congr rfl fun _ _ ↦ rfl)
      (Finset.sum_congr rfl fun m _ ↦ congrArg g (Nat.add_comm _ _))
theorem sum_zmod2_two_2m1 (g : ZMod 2 → ℂ) : (∑ b : ZMod 2, g b) = g 0 + g 1 := Fin.sum_univ_two g
theorem sum_coin2m1Val_c0_c1 :
    ∀ (k : ℕ) (f : ℕ → ℂ),
      ((∑ u : BitAssignment k, ∑ v : BitAssignment k,
          f (coin2m1Val k 0 (extBits2m1 u) (extBits2m1 v))) =
        ∑ m : Fin (2 ^ k), ((2 * m.val + 1 : ℕ) : ℂ) * f m.val) ∧
      ((∑ u : BitAssignment k, ∑ v : BitAssignment k,
          f (coin2m1Val k 1 (extBits2m1 u) (extBits2m1 v))) =
        ∑ m : Fin (2 ^ k), ((2 * (2 ^ k - 1 - m.val) + 1 : ℕ) : ℂ) * f m.val)
  | 0, f => by
      have : Unique (BitAssignment 0) :=
          Fintype.card_eq_one_iff_nonempty_unique.mp (by simp [BitAssignment]) |>.some
      simp [Finset.univ_unique, coin2m1Val]
  | k + 1, f => by
      have ih := sum_coin2m1Val_c0_c1 k f
      have ihShift := sum_coin2m1Val_c0_c1 k (fun n ↦ f (n + 2 ^ k))
      have h_lt (w : BitAssignment k) (bw : ZMod 2) : ∀ i < k, extBits2m1 (splitBitsTop2m1 k (w,
          bw)) i = extBits2m1 w i :=
        fun i hi ↦
            by simp only [extBits2m1, splitBitsTop2m1, Equiv.coe_fn_mk, Nat.lt_succ_of_lt hi, hi,
                 ↓reduceDIte]
      have hEval (c : ZMod 2) (u v : BitAssignment k) (bu bv : ZMod 2) :
          coin2m1Val (k + 1) c (extBits2m1 (splitBitsTop2m1 k (u, bu)))
              (extBits2m1 (splitBitsTop2m1 k (v, bv))) =
            let s := c + bu * bv
            coin2m1Val k s (extBits2m1 u) (extBits2m1 v) + (if bu + bv + s = 1 then 2 ^ k else 0)
                := by
        dsimp only [coin2m1Val]
        have htop (w : BitAssignment k) (bw : ZMod 2) : extBits2m1 (splitBitsTop2m1 k (w, bw)) k =
            bw := by simp [extBits2m1, splitBitsTop2m1]
        rw [htop, htop, coin2m1Val_congr k _ (h_lt u bu) (h_lt v bv)]
      let S (c : ZMod 2) (sh : ℕ) :=
          ∑ u : BitAssignment k, ∑ v : BitAssignment k, f (coin2m1Val k c (extBits2m1 u)
          (extBits2m1 v) + sh)
      have hUnf (c : ZMod 2) : (∑ u : BitAssignment (k + 1), ∑ v : BitAssignment (k + 1),
          f (coin2m1Val (k + 1) c (extBits2m1 u) (extBits2m1 v))) =
          ∑ bu : ZMod 2, ∑ bv : ZMod 2, S (c + bu * bv)
              (if bu + bv + (c + bu * bv) = 1 then 2 ^ k else 0) := by
        rw [← Equiv.sum_comp (splitBitsTop2m1 k)]
        simp_rw [← Equiv.sum_comp (splitBitsTop2m1 k), Fintype.sum_prod_type]
        rw [Finset.sum_comm (s := Finset.univ (α := BitAssignment k))]
        simp_rw [Finset.sum_comm (s := Finset.univ (α := BitAssignment k))
            (t := Finset.univ (α := ZMod 2)), hEval c]
        rfl
      constructor
      · rw [hUnf 0]
        simp_rw [sum_zmod2_two_2m1]
        change (S 0 0 + S 0 (2 ^ k)) + (S 0 (2 ^ k) + S 1 (2 ^ k)) = _
        dsimp only [S]
        simp only [Nat.add_zero]
        rw [ih.1, ihShift.1, ihShift.2,
          sum_fin_pow_succ_split_2m1 k (fun n ↦ ((2 * n + 1 : ℕ) : ℂ) * f n), add_assoc,
          ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
        refine congrArg (_ + ·) (Finset.sum_congr rfl fun m _ ↦ ?_)
        have hm := m.isLt
        rw [← add_mul, ← add_mul]
        exact congrArg (· * _)
            (by exact_mod_cast (show (2 * m.val + 1) + ((2 * m.val + 1) + (2 * (2 ^ k - 1 - m.val) +
                  1)) = 2 * (m.val + 2 ^ k) + 1 by omega))
      · rw [hUnf 1]
        simp_rw [sum_zmod2_two_2m1]
        change (S 1 (2 ^ k) + S 1 0) + (S 1 0 + S 0 0) = _
        dsimp only [S]
        simp only [Nat.add_zero]
        rw [ihShift.2, ih.2, ih.1, sum_fin_pow_succ_split_2m1 k (fun n ↦
            ((2 * (2 ^ (k + 1) - 1 - n) + 1 : ℕ) : ℂ) * f n), add_assoc, add_comm]
        refine congrArg₂ (· + ·) (by
            rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl fun m _ ↦ ?_
            have hm := m.isLt
            rw [← add_mul, ← add_mul]
            exact congrArg (· * _) (by
              exact_mod_cast (show (2 * (2 ^ k - 1 - m.val) + 1) + ((2 * (2 ^ k - 1 - m.val) +
                1) + (2 * m.val + 1)) = 2 * (2 ^ (k + 1) - 1 - m.val) +
                1 by
                  simp only [Nat.pow_succ]
                  omega)))
          (Finset.sum_congr rfl fun m _ ↦ by
            have hm := m.isLt
            rw [show 2 ^ k - 1 - m.val = 2 ^ (k + 1) - 1 -
                (m.val + 2 ^ k) by
                  simp only [Nat.pow_succ]
                  omega])
theorem sum_fin128_2m1_lt_eq :
    ∀ a : ℕ, a ≤ 128 →
      (∑ q : Fin 128, (if q.val < a then ((2 * q.val + 1 : ℕ) : ℂ) else 0)) =
        (a : ℂ) * (a : ℂ)
  | 0, _ => by simp
  | a + 1, ha => by
      have hpt : ∀ q : Fin 128, (if q.val < a + 1 then ((2 * q.val + 1 : ℕ) : ℂ) else 0) =
          (if q.val < a then ((2 * q.val + 1 : ℕ) : ℂ) else 0) +
              (if q = ⟨a, ha⟩ then ((2 * a + 1 : ℕ) : ℂ) else 0) := fun q ↦ by
        by_cases hlt : q.val < a
        · simp [hlt, Nat.lt_succ_of_lt hlt, show q ≠ ⟨a, ha⟩ from fun e ↦
              Nat.ne_of_lt hlt (congrArg Fin.val e)]
        · by_cases heq : q.val = a
          · simp [show q = ⟨a, ha⟩ from Fin.ext heq]
          · simp [hlt, show ¬q.val < a + 1 by omega, show q ≠ ⟨a, ha⟩ from fun e ↦
                heq (congrArg Fin.val e)]
      simp_rw [hpt, Finset.sum_add_distrib, sum_fin128_2m1_lt_eq a (Nat.le_of_succ_le ha),
          Finset.sum_ite_eq', Finset.mem_univ, ite_true]
      push_cast
      ring
theorem sum_fin128_2m1_all : (∑ q : Fin 128, ((2 * q.val + 1 : ℕ) : ℂ)) = (16384 : ℂ) := by
  simpa only [Fin.is_lt, ↓reduceIte,
      Nat.cast_ofNat] using (sum_fin128_2m1_lt_eq 128 le_rfl).trans (by norm_num)
theorem bitSign_ite_le_2m1 (a m : ℕ) : bitSign (if a ≤ m then (1 : ZMod 2) else 0) = (-1 : ℂ) +
    (2 : ℂ) * (if m < a then (1 : ℂ) else 0) := by
  by_cases h : a ≤ m
  · have hlt : ¬(m < a) := by omega
    simp only [h, hlt, ↓reduceIte, bitSign_one]; ring
  · have hlt : m < a := by omega
    simp only [h, hlt, ↓reduceIte, bitSign_zero]; norm_num
theorem sum_z41_kin2m1_pure (k : Fin 256) :
    (∑ z : BitAssignment 41,
      bitSign (if (twosComplement_frozen k).natAbs ≤
        coin2m1Val 7 0
          (fun i ↦ if hi : i < 7 then z ⟨i, by omega⟩ else 0)
          (fun i ↦ if hi : i < 7 then z ⟨7 + i, by omega⟩ else 0)
        then (1 : ZMod 2) else 0)) =
      (2 ^ 41 : ℂ) * ((((twosComplement_frozen k : ℝ) ^ 2 - 8192) / 8192 : ℝ) : ℂ) := by
  let A : ℕ := (twosComplement_frozen k).natAbs
  have hAle : A ≤ 128 := by
    have hlo := Int.le_bmod (x := (k.val : ℤ)) (by omega : 0 < 256)
    have hhi := Int.bmod_lt (x := (k.val : ℤ)) (by omega : 0 < 256)
    have hx : -128 ≤ twosComplement_frozen k ∧ twosComplement_frozen k ≤ 128 := by
      unfold twosComplement_frozen gridBits_frozen;
      change -128 ≤ (k.val : ℤ).bmod 256 ∧ (k.val : ℤ).bmod 256 ≤ 128; omega
    dsimp only [A]; omega
  rw [sum_split_bits 14 27 (fun u ↦ bitSign (if A ≤ coin2m1Val 7 0 (fun i ↦
    if hi : i < 7 then u ⟨i, by omega⟩ else 0) (fun i ↦ if hi : i < 7 then u ⟨7 + i,
    by omega⟩ else 0) then (1 : ZMod 2) else 0))]
  rw [← Equiv.sum_comp (Fin.appendEquiv (α := ZMod 2) 7 7), Fintype.sum_prod_type]
  simp_rw [show ∀ u₁ u₂ : BitAssignment 7,
      coin2m1Val 7 0 (fun i ↦ if hi : i < 7 then (Fin.appendEquiv 7 7 (u₁, u₂))
          ⟨i, by omega⟩ else 0)
        (fun i ↦ if hi : i < 7 then (Fin.appendEquiv 7 7 (u₁, u₂)) ⟨7 + i, by omega⟩ else 0) =
      coin2m1Val 7 0 (extBits2m1 u₁) (extBits2m1 u₂) from fun u₁ u₂ ↦
    coin2m1Val_congr 7 0
      (fun i hi ↦ by simp only [extBits2m1, Fin.appendEquiv_apply, hi, ↓reduceDIte,
        show (⟨i, by omega⟩ : Fin (7 + 7)) = Fin.castAdd 7 ⟨i, hi⟩ from Fin.ext rfl,
            Fin.append_left])
      (fun i hi ↦ by simp only [extBits2m1, Fin.appendEquiv_apply, hi, ↓reduceDIte,
        show (⟨7 + i, by omega⟩ : Fin (7 + 7)) = Fin.natAdd 7 ⟨i, hi⟩ from Fin.ext rfl,
            Fin.append_right])]
  rw [(sum_coin2m1Val_c0_c1 7 (fun m ↦ bitSign (if A ≤ m then 1 else 0))).1]
  change (2 ^ 27 : ℂ) * (∑ m : Fin 128, _) = _
  simp_rw [show ∀ m : Fin 128, ((2 * m.val + 1 : ℕ) : ℂ) * bitSign (if A ≤ m.val then 1 else 0) =
      -(((2 * m.val + 1 : ℕ) : ℂ)) + (2 : ℂ) *
          (if m.val < A then ((2 * m.val + 1 : ℕ) : ℂ) else 0) from fun m ↦ by
    rw [bitSign_ite_le_2m1]
    by_cases hlt : m.val < A <;> simp [hlt]
    ring]
  have hR := congrArg (Int.cast (R := ℝ)) (Int.natCast_natAbs (twosComplement_frozen k))
  rw [Int.cast_natCast, Int.cast_abs] at hR
  rw [Finset.sum_add_distrib, Finset.sum_neg_distrib, sum_fin128_2m1_all, ← Finset.mul_sum,
    sum_fin128_2m1_lt_eq A hAle, show ((A : ℂ) * (A : ℂ)) =
        (((twosComplement_frozen k : ℝ) ^ 2 : ℝ) : ℂ) from by
      rw [← sq_abs (twosComplement_frozen k : ℝ), ← hR]
      push_cast
      ring]
  push_cast
  ring
theorem sum_z41_kin2m1OutBit_eq (β : BitAssignment dLayout) (hk1 : β wIsKin = 1)
    (hscr : ∀ m : Fin 521, 22 ≤ m.val → β (rWorkInnerLayout m) = 0) :
    (∑ z : BitAssignment 41, bitSign (kin2m1OutBit (fun j ↦
        writeReg β rInner41Layout z (rKin226Layout j)))) =
      (2 ^ 41 : ℂ) * ((((twosComplement_frozen (kOfBits8 (fun j ↦ β (rKin226Layout j))) : ℝ) ^ 2 -
          8192) / 8192 : ℝ) : ℂ) := by
  let k := kOfBits8 (fun j ↦ β (rKin226Layout j))
  rw [← sum_z41_kin2m1_pure k]
  refine Finset.sum_congr rfl fun z _ ↦ congrArg bitSign ?_
  let γ : BitAssignment 226 := fun j ↦ writeReg β rInner41Layout z (rKin226Layout j)
  have hscr25 (w : Wire 226) (hw : 25 ≤ w.val) : γ w = 0 := by
    change writeReg β rInner41Layout z (rKin226Layout w) = 0
    rw [writeReg_rInner41_kin226_keep_sqf β z w (Or.inr (by omega)), rKin226_eq_rWorkInner_sqf w hw]
    exact hscr _ (Nat.le_add_right 22 _)
  have hw_z (off i : ℕ) (hb : off + i < 14) : γ (wKin (8 + (off + i))) = z ⟨off + i, by omega⟩ := by
    refine (congrArg (writeReg β rInner41Layout z) ?_).trans (writeReg_apply_reg _ _ _ _)
    rw [show wKin (8 + (off + i)) = ⟨8 + (off + i),
        by omega⟩ from Fin.ext (Nat.mod_eq_of_lt (by omega))]
    exact Fin.ext (by
      change (kin226WireFn ⟨8 + (off + i), _⟩).val = _
      rw [val_kin226WireFn, val_rInner41Layout]
      dsimp
      split_ifs <;> omega)
  rw [kin2m1OutBit_eq_fn γ,
    show γ wOutKin226 =
        0 from (writeReg_rInner41_kin226_keep_sqf β z _ (Or.inr (by decide))).trans (hscr ⟨22,
        by omega⟩ le_rfl),
    show γ wIsKin226 =
        1 from (writeReg_rInner41_kin226_keep_sqf β z _ (Or.inr (by decide))).trans hk1,
    zero_add, one_mul, kin2m1RawBit_eq γ hscr25,
    kOfBits8_congr_lt8_sqf _ _ (fun j hj ↦ writeReg_rInner41_kin226_keep_sqf β z j (Or.inl hj))]
  refine congrArg (fun v ↦ if (twosComplement_frozen k).natAbs ≤ v then (1 : ZMod 2) else 0)
      (coin2m1Val_congr 7 0 ?_ ?_)
  · exact fun i hi ↦ (congrArg (γ ∘ wKin) (show 8 + i = 8 + (0 + i) by omega)).trans
      ((hw_z 0 i (by omega)).trans (by simp only [hi, ↓reduceDIte, Nat.zero_add]))
  · exact fun i hi ↦ (congrArg (γ ∘ wKin) (show 15 + i = 8 + (7 + i) by omega)).trans
      ((hw_z 7 i (by omega)).trans (by simp only [hi, ↓reduceDIte]))
theorem sum_z41_qft8_kin2m1OutBit_matrix (β : BitAssignment dLayout) (hk1 : β wIsKin = 1)
    (hscr : ∀ m : Fin 521, 22 ≤ m.val → β (rWorkInnerLayout m) = 0) :
    (∑ z : BitAssignment 41, (QFT.qftMatrix 8)ᴴ * Matrix.diagonal (fun k : Fin 256 ↦
      bitSign (kin2m1OutBit (fun j ↦
      writeReg (writeReg β rPKinLayout (basisBits 8 k)) rInner41Layout z (rKin226Layout
      j)))) * QFT.qftMatrix 8) =
      (2 ^ 41 : ℂ) • kinAxisShiftedOp := by
  have hdiag : (∑ z : BitAssignment 41,
    Matrix.diagonal (fun k : Fin 256 ↦ bitSign (kin2m1OutBit (fun j ↦
    writeReg (writeReg β rPKinLayout (basisBits 8 k)) rInner41Layout z (rKin226Layout j))))) =
      (2 ^ 41 : ℂ) • Matrix.diagonal (fun k : Fin 256 ↦
          ((((twosComplement_frozen k : ℝ) ^ 2 - 8192) / 8192 : ℝ) : ℂ)) := by
    ext k₁ k₂
    rcases eq_or_ne k₁ k₂ with rfl | hk
    · simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.diagonal_apply_eq, smul_eq_mul]
      let βk := writeReg β rPKinLayout (basisBits 8 k₁)
      have notPK {u : Wire dLayout} (hu : u.val < 5755 ∨ 5763 ≤ u.val) : βk u = β u :=
        writeReg_apply_of_not_mem β rPKinLayout (basisBits 8 k₁) u fun ⟨b, hb⟩ ↦ by
          have _ := b.isLt
          have hv := (val_rPKinLayout b).symm.trans (congrArg Fin.val hb)
          omega
      have hk_isk : βk wIsKin = 1 :=
          (notPK (Or.inl (by
            dsimp [wIsKin]
            rw [val_rOut40Layout]
            omega))).trans hk1
      have hk_scr (m : Fin 521) (hm : 22 ≤ m.val) : βk (rWorkInnerLayout m) = 0 :=
        (notPK (Or.inr (by
          rw [val_rWorkInnerLayout]
          omega))).trans (hscr m hm)
      have hk_bits : kOfBits8 (fun j ↦ βk (rKin226Layout j)) = k₁ :=
          kOfBits8_of_basisBits8 k₁ _ fun b ↦ by
        have hb := b.isLt
        have hw : rKin226Layout (wKin b.val) = rPKinLayout b := by
          rw [show wKin b.val = ⟨b.val, by omega⟩ from Fin.ext (Nat.mod_eq_of_lt (by omega))]
          exact Fin.ext (by
            change (kin226WireFn ⟨b.val, _⟩).val = _
            rw [val_kin226WireFn, val_rPKinLayout]
            dsimp
            split_ifs
            omega)
        exact (congrArg βk hw).trans (writeReg_apply_reg _ _ _ _)
      exact (sum_z41_kin2m1OutBit_eq βk hk_isk hk_scr).trans (by rw [hk_bits])
    · simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.diagonal_apply_ne _ hk,
          Finset.sum_const_zero, smul_zero]
  rw [← Finset.sum_mul, ← Finset.mul_sum, hdiag, kinAxisShiftedOp, Matrix.mul_smul, Matrix.smul_mul]
open PhotochemistrySolution.SelectFastFlags PhotochemistrySolution.SelectQft8GidneyStg3
  PhotochemistrySolution.ProviderCore
open PhotochemistrySolution.FastQft8 PhotochemistrySolution.SelectKin526OneWrap
theorem hAv23_15SqFree2m1 : cpAvoid23_sqf pKinPre15SqFree2m1CP = true := by decide +kernel
attribute [local irreducible] systemQubits_frozen SelectCompactAnc.ancWOfScr
    PgBase.phaseGradientState XMeasChunkQromUnldA.phaseFlipUnitary
  Stage4Kin14Scb.abpKin14Usel Stage4Kin14Scb.abpKin14Csel Kinetic664.abpKin14SqFree2m1Usel
      Kinetic664.abpKin15SqFree2m1Usel
  Kinetic664.abpKin15SqFree2m1Csel Stage4KinFull.bAxisMux27 bSpeciesSwap50
/-- Uncontrolled local middle unitary for exact 2-coin square-free kinetic (`16` ANDs = `64 T`). -/
noncomputable def uKinMid2m1UselLayout : Unitary (2 ^ dLayout) :=
  rKin226Layout.embedUnitary abpKin15SqFree2m1Usel.toCircuit.eval
/-- Controlled local middle unitary for exact 2-coin square-free kinetic (`16` ANDs = `64 T`). -/
noncomputable def uKinMid2m1CselLayout : Unitary (2 ^ dLayout) :=
  rKin226Layout.embedUnitary abpKin15SqFree2m1Csel.toCircuit.eval
/-- Core ideal-QFT kinetic unitary (`Usel`) for exact 2-coin square-free kinetic. -/
noncomputable def uKinCoreIdeal2m1UselLayout : Unitary (2 ^ dLayout) :=
  uMux27Layout⁻¹ *
    ((qft8Stg3IdealU scrWLayout rPKinLayout)⁻¹ *
      uKinMid2m1UselLayout *
      qft8Stg3IdealU scrWLayout rPKinLayout) *
    uMux27Layout
/-- Species-swapped ideal-QFT kinetic unitary (`Usel`) for exact 2-coin square-free kinetic. -/
noncomputable def uKinIdeal2m1UselLayout : Unitary (2 ^ dLayout) :=
    uSpeciesSwap50Layout⁻¹ * uKinCoreIdeal2m1UselLayout * uSpeciesSwap50Layout
noncomputable def uAlignedKinIdeal2m1Layout : Unitary (2 ^ dLayout) :=
    uKinAlign0Layout⁻¹ * uKinIdeal2m1UselLayout * uKinAlign0Layout
theorem uKinMid2m1_isPhaseDiag_layout (δ : BitAssignment dLayout) :
    uKinMid2m1UselLayout.1.mulVec (KinB.ket δ) =
    QubitizationWalkSem.bitSign (kin2m1OutBit (fun j ↦
    δ (rKin226Layout j))) • KinB.ket δ :=
  embedUnitary_mulVec_ket_of_isPhaseDiag rKin226Layout abpKin15SqFree2m1Usel.toCircuit.eval
      isPhaseDiag_and_valid_abpKin2m1.1 δ
end QuantumComputation.Specs.PhotochemistrySolution.RouterSelectWiringB
end
end

section

open QuantumComputation.Specs.PhotochemistrySolution.Stage4Cluster22Xnor
  QuantumComputation.Specs.PhotochemistrySolution.SelectCsa64ProvSpec
open _root_.QuantumComputation.Specs.PhotochemistrySolution.FineLegendre (mkKetOpW)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.PotOracleGen (openCoordDistSq)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.ZeroNEremSpec (fin8Bin)

noncomputable section
namespace QuantumComputation.Specs.PhotochemistrySolution.Coin70Lift

open Operator QProg Matrix Circuit Qubit PrimitiveGate QuantumComputation.Specs
  PhotochemistrySolution
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
open PhotochemistrySolution.PotSelectWiring PhotochemistrySolution.SelectOracles
  PhotochemistrySolution.FineLegendre PhotochemistrySolution.PotOracleGen
theorem natOfBoolBits_testBit_self : ∀ (k v : ℕ), v < 2 ^ k →
    PhotochemistrySolution.Stage4FineFast.natOfBoolBits k (fun b ↦ v.testBit b.val) = v
  | 0, _, hv => (Nat.lt_one_iff.mp hv).symm
  | k + 1, v, hv => by
      simp only [PhotochemistrySolution.Stage4FineFast.natOfBoolBits]
      rw [show (fun i : Fin k ↦ v.testBit i.val) = fun i ↦ (v % 2 ^ k).testBit i.val from
        funext fun i ↦ by simp [Nat.testBit_mod_two_pow, i.isLt],
        natOfBoolBits_testBit_self k (v % 2 ^ k) (Nat.mod_lt v (Nat.two_pow_pos k))]
      simp only [Nat.testBit_eq_decide_div_mod_eq]
      have hd := Nat.mod_add_div v (2 ^ k)
      match hq : v / 2 ^ k, Nat.div_lt_of_lt_mul (Nat.pow_succ 2 k ▸ hv) with
      | 0, _ | 1, _ => simpa [hq] using hd

theorem natOfZModBits_ite_testBit_local (k v : ℕ) (hv : v < 2 ^ k) :
    natOfZModBits k (fun b ↦ if v.testBit b.val then 1 else 0) = v := by
  simpa [natOfZModBits, show (fun i : Fin k ↦
      ((if v.testBit i.val then (1 : ZMod 2) else 0) == 1)) =
    fun i ↦ v.testBit i.val from funext fun i ↦ by cases v.testBit i.val <;> rfl] using
    natOfBoolBits_testBit_self k v hv

theorem add_two_pow_testBit_lt {lo k j : ℕ} (_ : lo < 2 ^ k) (hj : j < k) :
    (lo + 2 ^ k).testBit j = lo.testBit j := by
  simpa only [Nat.testBit_mod_two_pow, decide_eq_true hj, Bool.true_and]
    using congrArg (·.testBit j) (Nat.add_mod_right lo (2 ^ k))
theorem natOfBoolBits_lt_pow : ∀ (k : ℕ) (g : Fin k → Bool),
    PhotochemistrySolution.Stage4FineFast.natOfBoolBits k g < 2 ^ k
  | 0, _ => Nat.zero_lt_one
  | k + 1, g => by
      have _ := natOfBoolBits_lt_pow k fun i ↦ g ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩
      unfold PhotochemistrySolution.Stage4FineFast.natOfBoolBits
      split_ifs <;> simp only [Nat.pow_succ] <;> omega

theorem natOfZModBits_11_lt (f : Fin 11 → ZMod 2) : natOfZModBits 11 f < 2048 :=
  natOfBoolBits_lt_pow 11 _
attribute [local irreducible] natOfZModBits
theorem natOfBoolBits_testBit : ∀ (k : ℕ) (g : Fin k → Bool) (b : Fin k),
    (PhotochemistrySolution.Stage4FineFast.natOfBoolBits k g).testBit b.val = g b
  | 0, _, b => Fin.elim0 b
  | k + 1, g, b => by
      simp only [PhotochemistrySolution.Stage4FineFast.natOfBoolBits]
      have hlo := natOfBoolBits_lt_pow k fun i ↦ g ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩
      if hb : b.val < k then
        have ih := natOfBoolBits_testBit k (fun i ↦ g ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩) ⟨b.val, hb⟩
        split_ifs <;> first | exact (add_two_pow_testBit_lt hlo hb).trans ih | simpa using ih
      else
        obtain rfl : b = ⟨k, Nat.lt_succ_self k⟩ :=
          Fin.ext (Nat.le_antisymm (Nat.le_of_lt_succ b.isLt) (Nat.not_lt.mp hb))
        dsimp only
        cases g ⟨k, Nat.lt_succ_self k⟩ <;>
          simp [Nat.testBit_eq_decide_div_mod_eq, Nat.div_eq_of_lt hlo, Nat.two_pow_pos k]
end QuantumComputation.Specs.PhotochemistrySolution.Coin70Lift

namespace QuantumComputation.Specs.PhotochemistrySolution.ReflStage4

open Qubit PhotochemistrySolution PhotochemistrySolution.PotOracleGen
  PhotochemistrySolution.PotSelectWiring
/- ## Section 1: Index Bounds & Compose Disjointness -/
theorem owCompose_disj {A B M n : ℕ} {f : QRegister A M} {g : QRegister B M} (r : QRegister M n)
    (hne : ∀ (i : Fin A) (j : Fin B), (f i).val ≠ (g j).val) :
    (r.compose f).DisjointWires (r.compose g) :=
  disj_of_ne fun i j e ↦ hne i j (congrArg Fin.val (r.wires.injective e))
/- ## Section 2: Gate Wires & Header Subregisters (`h2 : 2 ≤ kPool`) -/
end QuantumComputation.Specs.PhotochemistrySolution.ReflStage4

namespace QuantumComputation.Specs.PhotochemistrySolution.EvenOctB70

open PhotochemistrySolution.ZeroNEremCsa36Kick PhotochemistrySolution.BandEnc12Sync
/-- Bitwise OR across all columns in `cs` (`syncNat`-normalized). -/
def orCols : List ℕ → ℕ
  | [] => 0
  | c :: cs => syncNat (c ||| orCols cs)
theorem testBit_orCols :
    ∀ (cs : List ℕ) (q : ℕ),
      (orCols cs).testBit q = decide (0 < vecVal cs q)
  | [], _ => by simp [orCols, vecVal]
  | c :: cs, q => by
      rcases Bool.eq_false_or_eq_true (c.testBit q) with h | h <;>
        simp [orCols, syncNat_eq, testBit_orCols cs q, vecVal, h]
theorem testBit_orCols_drop (s : ℕ) (cs : List ℕ) (q : ℕ) : (orCols (cs.drop s)).testBit q =
    decide (2 ^ s ≤ vecVal cs q) := by
  rw [testBit_orCols, vecVal_drop, Nat.shiftRight_eq_div_pow]
  exact (em (2 ^ s ≤ vecVal cs q)).elim (fun h ↦ by simp [h, Nat.div_pos h (Nat.two_pow_pos s)])
    (fun h ↦ by simp [h, Nat.div_eq_zero_iff.mpr (.inr (Nat.lt_of_not_ge h))])
theorem vecVal_append :
    ∀ (as bs : List ℕ) (q : ℕ),
      vecVal (as ++ bs) q = vecVal as q + 2 ^ as.length * vecVal bs q
  | [], bs, q => by simp [vecVal]
  | a :: as, bs, q => by
      simp only [List.cons_append, vecVal, vecVal_append as bs q, List.length_cons, Nat.pow_succ]
      cases a.testBit q <;> ring
/-- `22`-column expected bitslice `[idx8 (8)] ++ [t10 (10)] ++ [k4 (4)]` for octave `k`. -/
def oct22Cols (mx : ℕ) (uc : List ℕ) (k : ℕ) : List ℕ :=
  let hi := uc.getD 17 0; let idxLo := (uc.drop 9).take 7 ++ [0];
  let idxHi := (uc.drop 10).take 7 ++ [mx]; let idx8 := vecMux hi idxHi idxLo;
  let tLo := 0 :: uc.take 9; let tHi := uc.take 10; let t10 := vecMux hi tHi tLo
  idx8 ++ t10 ++ vecConst mx 4 k
theorem oct22Cols_length (mx : ℕ) (uc : List ℕ) (k : ℕ) (huc : uc.length = 18) :
    (oct22Cols mx uc k).length = 22 := by
  dsimp only [oct22Cols]
  rw [List.length_append, List.length_append, vecMux_length _ _ _ (by simp [huc]),
    vecMux_length _ _ _ (by simp [huc]), vecConst_length]
  simp [huc]
theorem oct22Cols_spec (mx : ℕ) (uc : List ℕ) (k d2 : ℕ)
    (hmx : mx.testBit d2 = true) (huc : uc.length = 18)
    (hk : k ≤ 8) (hu0 : 65536 ≤ vecVal uc d2) (hu1 : vecVal uc d2 < 262144) :
    let u := vecVal uc d2
    vecVal (oct22Cols mx uc k) d2 = (if u < 131072 then (u - 65536) / 512 else 128 + (u - 131072) /
        1024) +
      256 * (if u < 131072 then (u % 512) * 2 else u % 1024) + 262144 * k := by
  dsimp only [oct22Cols]
  rw [List.append_assoc, vecVal_append, vecMux_length _ _ _ (by simp [huc]), vecVal_append,
    vecMux_length _ _ _ (by simp [huc]), vecVal_mux _ _ _ d2 (by simp [huc]),
    vecVal_mux _ _ _ d2 (by simp [huc]),
    show (uc.getD 17 0).testBit d2 = decide (131072 ≤ vecVal uc d2) by
      rw [← vecVal_testBit, Nat.testBit_eq_decide_div_mod_eq]
      norm_num only
      exact decide_eq_decide.mpr (by omega),
    vecVal_const hmx 4 k]
  simp only [vecVal_append, vecVal_take, vecVal_drop, List.length_append, List.length_take,
      List.length_drop,
    List.length_singleton, huc, vecVal, hmx, Nat.zero_testBit, Bool.false_eq_true, ↓reduceIte,
        mul_zero,
    add_zero, zero_add, mul_one, Nat.shiftLeft_eq, one_mul, Nat.and_two_pow_sub_one_eq_mod,
    Nat.shiftRight_eq_div_pow, decide_eq_true_eq]
  split_ifs <;> norm_num <;> omega

/-- Shift `mCols` into octave `k` (`18` columns): `m <<< (16 - 2 * k)`. -/
def uColsOf (mCols : List ℕ) (k : ℕ) : List ℕ :=
    List.replicate (16 - 2 * k) 0 ++ mCols.take (2 * k + 2)
theorem uColsOf_length (mCols : List ℕ) (k : ℕ) (hm : mCols.length = 18)
    (hk : k ≤ 8) : (uColsOf mCols k).length = 18 := by
  unfold uColsOf
  simp [hm]
  omega
theorem uColsOf_val (mCols : List ℕ) (k d2 : ℕ) (_hk : k ≤ 8)
    (hlt : vecVal mCols d2 < 2 ^ (2 * k + 2)) : vecVal (uColsOf mCols k) d2 = (vecVal mCols d2) <<<
    (16 - 2 * k) := by
  rw [uColsOf, vecVal_shl, vecVal_take,
    show 1 <<< (2 * k + 2) = 2 ^ (2 * k + 2) by simp [Nat.shiftLeft_eq],
    Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt hlt]
/-- Recursive octave cascade `k = 0 .. nOct` avoiding exponential `vecMux` unfolding. -/
def expEvenOctLoop (mx : ℕ) (mCols : List ℕ) : ℕ → List ℕ
  | 0 => oct22Cols mx (uColsOf mCols 0) 0
  | k + 1 =>
      vecMux (orCols (mCols.drop (2 * (k + 1))))
        (oct22Cols mx (uColsOf mCols (k + 1)) (k + 1))
        (expEvenOctLoop mx mCols k)
/-- Exact `22`-column expected bitslice `[idx8 ++ t10 ++ k4]` across all `d2 < 262144`. -/
def expEvenOctCols (nn mx : ℕ) (cs18 : List ℕ) : List ℕ :=
  let mCols :=
      if Nat.beq nn 1 then vecMux (orCols (cs18.drop 3)) cs18 (vecConst mx 18 8) else vecMux
      (orCols cs18) cs18 (vecConst mx 18 1)
  expEvenOctLoop mx mCols 8
theorem expEvenOctLoop_length (mx : ℕ) (mCols : List ℕ) (hm : mCols.length = 18) :
    ∀ k ≤ 8, (expEvenOctLoop mx mCols k).length = 22
  | 0, _ => oct22Cols_length mx _ 0 (uColsOf_length mCols 0 hm (by omega))
  | k + 1, hk => by
      have hi := oct22Cols_length mx _ (k + 1) (uColsOf_length mCols (k + 1) hm hk)
      exact (vecMux_length _ _ _ (hi.trans (expEvenOctLoop_length mx mCols hm k
          (by omega)).symm)).trans hi
theorem evenOctKRef_of_band {m k : ℕ} (hk : k ≤ 7) (hlo : 2 ^ (2 * (k + 1)) ≤ m)
    (hhi : m < 2 ^ (2 * (k + 1) + 2)) : evenOctKRef m = k + 1 ∧ 65536 ≤ m <<< (16 - 2 * (k + 1)) ∧
    m <<< (16 - 2 * (k + 1)) < 262144 := by
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    (
      norm_num at hlo hhi
      unfold evenOctKRef
      simp only [Nat.shiftLeft_eq]
      split_ifs <;>
        omega)
theorem expEvenOctLoop_val (mx : ℕ) (mCols : List ℕ) (d2 : ℕ)
    (hmx : mx.testBit d2 = true) (hm : mCols.length = 18)
    (h1 : 1 ≤ vecVal mCols d2) :
    ∀ k ≤ 8, vecVal mCols d2 < 2 ^ (2 * k + 2) →
      vecVal (expEvenOctLoop mx mCols k) d2 =
        let m := vecVal mCols d2; let u := m <<< (16 - 2 * evenOctKRef m)
        (if u < 131072 then (u - 65536) / 512 else 128 + (u - 131072) / 1024) +
        256 * (if u < 131072 then (u % 512) * 2 else u % 1024) + 262144 * evenOctKRef m
  | 0, _, htop => by
      have huEq := uColsOf_val mCols 0 d2 (by omega) htop
      dsimp only [expEvenOctLoop]
      rw [oct22Cols_spec mx _ 0 d2 hmx (uColsOf_length mCols 0 hm (by omega)) (by omega)
        (by
          simp only [huEq, Nat.shiftLeft_eq]
          omega)
            (by
              simp only [huEq, Nat.shiftLeft_eq]
              omega),
        huEq, show evenOctKRef (vecVal mCols d2) = 0 by
          unfold evenOctKRef
          exact PhotochemistrySolution.PotOracleGen.itePos (by omega)]
  | k + 1, hk, htop => by
      have hi := oct22Cols_length mx _ (k + 1) (uColsOf_length mCols (k + 1) hm hk)
      dsimp only [expEvenOctLoop]
      rw [vecVal_mux _ _ _ d2 (hi.trans (expEvenOctLoop_length mx mCols hm k (by omega)).symm),
        testBit_orCols_drop (2 * (k + 1)) mCols d2]
      by_cases hge : 2 ^ (2 * (k + 1)) ≤ vecVal mCols d2
      · obtain ⟨hkEq, hb1, hb2⟩ := evenOctKRef_of_band (by omega) hge htop
        have huEq := uColsOf_val mCols (k + 1) d2 hk htop
        rw [ite_eq_left (decide_eq_true hge), oct22Cols_spec mx _ (k + 1) d2 hmx
          (uColsOf_length mCols (k + 1) hm hk) hk (huEq ▸ hb1) (huEq ▸ hb2), huEq, hkEq]
      · simp only [hge, decide_false, Bool.false_eq_true, ↓reduceIte]
        exact expEvenOctLoop_val mx mCols d2 hmx hm h1 k (by omega)
          (by simpa [show 2 * (k + 1) = 2 * k + 2 by omega] using Nat.lt_of_not_ge hge)

theorem expEvenOctCols_val (nn : ℕ) (_hnn : nn < 2) {d2 : ℕ} (hd2 : d2 < 2 ^ 18) :
    let r := coordState 18; let exp := expEvenOctCols nn r.2.1 r.2.2;
    let p := evenOctIdxT10K (Nat.beq nn 1) d2
    exp.length = 22 ∧ vecVal exp d2 = p.1 + 256 * p.2.1 + 262144 * p.2.2 := by
  obtain ⟨_, hM, hlen, _, _⟩ := coordState_spec 18
  set mx := (coordState 18).2.1
  set cs18 := (coordState 18).2.2
  have hmx : mx.testBit d2 = true := by
    rw [hM, Nat.testBit_two_pow_sub_one]
    exact decide_eq_true (hd2.trans_le (by norm_num))
  dsimp only [expEvenOctCols]
  set mCols := if Nat.beq nn 1 then vecMux (orCols (cs18.drop 3)) cs18 (vecConst mx 18 8)
    else vecMux (orCols cs18) cs18 (vecConst mx 18 1)
  have hmLen : mCols.length = 18 := by
    dsimp only [mCols]
    split_ifs <;>
      exact (vecMux_length _ _ _ (hlen.trans (vecConst_length mx 18 _).symm)).trans hlen
  have hmVal : vecVal mCols d2 = max d2 (if Nat.beq nn 1 then 8 else 1) := by
    dsimp only [mCols]
    cases Nat.beq nn 1
    · rw [ite_eq_right Bool.false_ne_true,
          vecVal_mux _ _ _ d2 (hlen.trans (vecConst_length mx 18 1).symm),
        testBit_orCols, vecVal_coord 18 d2 hd2, vecVal_const hmx 18 1]
      by_cases hd0 : 0 < d2 <;> simp [hd0] <;> omega
    · rw [ite_eq_left rfl, vecVal_mux _ _ _ d2 (hlen.trans (vecConst_length mx 18 8).symm),
        testBit_orCols_drop 3 cs18 d2, vecVal_coord 18 d2 hd2, vecVal_const hmx 18 8]
      norm_num
      by_cases hd8 : 8 ≤ d2 <;> simp [hd8]
      omega
  have hmBnd : 1 ≤ vecVal mCols d2 ∧ vecVal mCols d2 < 2 ^ 18 := by
    rw [hmVal]
    split_ifs <;> omega
  exact ⟨expEvenOctLoop_length mx mCols hmLen 8 (by omega),
    (expEvenOctLoop_val mx mCols d2 hmx hmLen hmBnd.1 8 (by omega) hmBnd.2).trans
      (by simp only [hmVal, evenOctIdxT10K])⟩

theorem expEvenOctCols_testBit (nn : ℕ) (hnn : nn < 2) {d2 : ℕ} (hd2 : d2 < 2 ^ 18)
    (j : ℕ) (hj : j < 22) :
    let r := coordState 18; let exp := expEvenOctCols nn r.2.1 r.2.2;
    let p := evenOctIdxT10K (Nat.beq nn 1) d2
    (exp.getD j 0).testBit d2 =
      if j < 8 then p.1.testBit j else if j < 18 then p.2.1.testBit (j - 8) else p.2.2.testBit (j -
          18) := by
  dsimp only
  obtain ⟨_, hv⟩ := expEvenOctCols_val nn hnn hd2
  obtain ⟨hb0, hb1, _⟩ := evenOctIdxT10K_bounds (Nat.beq nn 1) (by omega : d2 < 262144)
  set p := evenOctIdxT10K (Nat.beq nn 1) d2
  have hMod (w : ℕ) {x y b : ℕ} (hb : b < w) (he : x % 2 ^ w = y % 2 ^ w) : x.testBit b =
      y.testBit b := by
    simpa [Nat.testBit_mod_two_pow, hb] using congrArg (·.testBit b) he
  rw [← vecVal_testBit, hv]
  split_ifs with hj8 hj18
  · exact hMod 8 hj8 (by omega)
  · rw [show j = 8 + (j - 8) by omega, ← Nat.testBit_shiftRight, Nat.shiftRight_eq_div_pow,
        add_tsub_cancel_left]
    exact hMod 10 (by omega) (by omega)
  · rw [show j = 18 + (j - 18) by omega, ← Nat.testBit_shiftRight, Nat.shiftRight_eq_div_pow]
    simpa [add_tsub_cancel_left] using
      congrArg (·.testBit (j - 18)) (show (p.1 + 256 * p.2.1 + 262144 * p.2.2) / 2 ^ 18 =
          p.2.2 by omega)
end QuantumComputation.Specs.PhotochemistrySolution.EvenOctB70

namespace QuantumComputation.Specs.PhotochemistrySolution.ShortBin7
theorem byteOfBits_testBit : ∀ (f : Fin 8 → ZMod 2) (k : Fin 8), (byteOfBits f).val.testBit k.val =
    (f k == 1) := by decide +kernel
theorem zmod2_eq_of_beq_one : ∀ x y : ZMod 2, (x == 1) = (y == 1) → x = y := by decide
end QuantumComputation.Specs.PhotochemistrySolution.ShortBin7
namespace QuantumComputation.Specs.PhotochemistrySolution.ShortBin7Pre6ZHi30
set_option maxRecDepth 4096
open Operator QProg Matrix Circuit Qubit PhotochemistrySolution
  PhotochemistrySolution.SelectStructuredCB PhotochemistrySolution.ZeroNEremAxisSq18
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
open PhotochemistrySolution.ShortBin7 PhotochemistrySolution.SelectOracles
  PhotochemistrySolution.Csa36KickStep PhotochemistrySolution.PotPortBMux
open PhotochemistrySolution.ShortBin7XagOpt
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt (writeReg)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.PotSelectWiring (coordOfReg24)
def packCoords48 (cA cB : Fin 3 → Fin 256) : ℕ := packBits 48 fun u ↦
    if u < 8 then (cA 0).val.testBit u else if u < 16 then (cA 1).val.testBit (u - 8) else if u <
    24 then (cA 2).val.testBit (u - 16) else if u < 32 then (cB 0).val.testBit (u - 24) else if u <
    40 then (cB 1).val.testBit (u - 32) else (cB 2).val.testBit (u - 40)
theorem packCoords48_testBit (cA cB : Fin 3 → Fin 256) (u : Fin 108) :
    (packCoords48 cA cB).testBit u.val =
      if u.val < 8 then (cA 0).val.testBit u.val
      else if u.val < 16 then (cA 1).val.testBit (u.val - 8)
      else if u.val < 24 then (cA 2).val.testBit (u.val - 16)
      else if u.val < 32 then (cB 0).val.testBit (u.val - 24)
      else if u.val < 40 then (cB 1).val.testBit (u.val - 32)
      else if u.val < 48 then (cB 2).val.testBit (u.val - 40) else false := by
  by_cases h48 : u.val < 48 <;>
    simp only [packCoords48, packBits_testBit, h48, decide_true, decide_false, Bool.true_and,
        Bool.false_and, ↓reduceIte]
  split_ifs <;> first | rfl | omega

/-- Pre-priority `6`-bit radial code computed from `(cA, cB)` via `treeCombPre14`. -/
def pre6OfCoords (cA cB : Fin 3 → Fin 256) : Fin 64 :=
  let q := (sq5ParOfUV (cA 0).val (cB 0).val) |||
    ((sq5ParOfUV (cA 1).val (cB 1).val) <<< 5) |||
    ((sq5ParOfUV (cA 2).val (cB 2).val) <<< 10)
  let st := evalPrimTree 29 q treeCombPre14
  ⟨packBits 6 fun k ↦ st.testBit (15 + k),
   lt_of_lt_of_eq (packBits_lt 6 _) (by decide)⟩
theorem pre6OfCoords_valid (cA cB : Fin 3 → Fin 256) :
    validPre6Mask64.testBit (pre6OfCoords cA cB).val = true :=
  (evalPrimTree_combPre14_bits (sq5ParOfUV (cA 0).val (cB 0).val) (sq5ParOfUV (cA 1).val (cB 1).val)
      (sq5ParOfUV (cA 2).val (cB 2).val)
    (sq5ParOfUV_lt32 (cA 0) (cB 0)) (sq5ParOfUV_lt32 (cA 1) (cB 1)) (sq5ParOfUV_lt32 (cA 2) (cB 2))
    (validSq5Mask32_of_uv (cA 0) (cB 0)) (validSq5Mask32_of_uv (cA 1) (cB 1))
        (validSq5Mask32_of_uv (cA 2) (cB 2))).2.1
theorem oneHot6OfPre6_pre6OfCoords (cA cB : Fin 3 → Fin 256) :
    oneHot6OfPre6 (pre6OfCoords cA cB).val = binOneHot6 (fin8Bin (openCoordDistSq cA cB)).val := by
  have hOh := (evalPrimTree_combPre14_bits _ _ _
    (sq5ParOfUV_lt32 (cA 0) (cB 0)) (sq5ParOfUV_lt32 (cA 1) (cB 1)) (sq5ParOfUV_lt32 (cA 2) (cB 2))
    (validSq5Mask32_of_uv (cA 0) (cB 0)) (validSq5Mask32_of_uv (cA 1) (cB 1))
        (validSq5Mask32_of_uv (cA 2) (cB 2))).2.2
  refine Nat.eq_of_testBit_eq fun j ↦ if hj : j < 6 then (hOh ⟨j, hj⟩).trans (congrArg (·.testBit j)
      ((fin8OneHotNat_sq5Par_eq (cA 0) (cA 1) (cA 2) (cB 0) (cB 1)
          (cB 2)).trans (binOneHot6_fin8Bin _).symm))
  else by
    have hp : 64 ≤ 2 ^ j :=
        (by norm_num : 64 ≤ 2 ^ 6).trans (Nat.pow_le_pow_right (by omega) (by omega))
    rw [Nat.testBit_lt_two_pow ((oneHot6OfPre6_lt _).trans_le hp),
      Nat.testBit_lt_two_pow (((by decide : ∀ b : Fin 8, binOneHot6 b.val < 64) _).trans_le hp)]

/-- Pre-priority `6`-bit radial code MBU package (`wrapDom` domain wrapper). -/
structure ShortBin7Pre6Pkg (kScr tSB : ℕ) where
  h6 : 6 ≤ kScr
  wrapDom : {Var : Type} → {n : ℕ} → Var →
    QRegister 24 n → QRegister 24 n → QRegister kScr n →
    DynamicCircuit Var n → DynamicCircuit Var n
  step_and_counts : ∀ {Var : Type} [Fintype Var] [DecidableEq Var] {W n : ℕ} [NeZero (2 ^ n)]
    (v : Var) (rWork : QRegister W n)
    (rA rB : QRegister 24 n) (rScr : QRegister kScr n),
    rA.DisjointWires rB → rA.DisjointWires rScr → rB.DisjointWires rScr →
    ∀ (st stPost : BitAssignment n → BitAssignment n)
      (phPre phPost : BitAssignment n → ZMod 2)
      (mid : DynamicCircuit Var n),
    (∀ (δ : BitAssignment n) (u : Fin kScr),
      (∀ k : Fin W, δ (rWork k) = 0) → st δ (rScr u) = 0) →
    (∀ (δ : BitAssignment n), (∀ k : Fin W, δ (rWork k) = 0) →
      (∀ i : Fin 24, stPost δ (rA i) = st δ (rA i)) ∧
      (∀ i : Fin 24, stPost δ (rB i) = st δ (rB i)) ∧
      (∀ u : Fin kScr, stPost δ (rScr u) = 0)) →
    (∀ stMid : BitAssignment n → BitAssignment n,
      (∀ (δ : BitAssignment n) (w : Wire n),
        (∀ u : Fin kScr, w ≠ rScr u) → stMid δ w = st δ w) →
      (∀ (δ : BitAssignment n), (∀ k : Fin W, δ (rWork k) = 0) → ∀ j : Fin 6,
        stMid δ (rScr ⟨j.val, sbScr_lt6 h6 j⟩) =
          if (pre6OfCoords (coordOfReg24 rA (st δ)) (coordOfReg24 rB (st δ))).val.testBit j.val
          then 1 else 0) →
      SubspaceStep (mkKetOpW rWork stMid phPre)
        (mkKetOpW rWork (fun δ ↦ writeReg (stPost δ) rScr (fun u ↦ stMid δ (rScr u))) phPost)
        mid) →
    SubspaceStep (mkKetOpW rWork st phPre) (mkKetOpW rWork stPost phPost)
      (wrapDom v rA rB rScr mid) ∧
    (wrapDom v rA rB rScr mid).count .T = tSB + mid.count .T ∧
    (wrapDom v rA rB rScr mid).count .TOFF = mid.count .TOFF ∧
    (∀ S : Wire n → Prop,
      (∀ i, S (rA i)) → (∀ i, S (rB i)) → (∀ u, S (rScr u)) → DynWires S mid →
      DynWires S (wrapDom v rA rB rScr mid))
def ShortBin7Pre6Pkg.ofComputeProg {kScr nAnd tSB : ℕ} (h6 : 6 ≤ kScr)
    (sMask : ℕ) (cp : ComputeProg (48 + kScr))
    (hValid : StructuredCB.validProgMask 0 sMask cp = true)
    (hAnd : cp.numAnd = nAnd) (htSB : 4 * nAnd = tSB)
    (hMaskGe : ∀ u : Wire (48 + kScr), sMask.testBit u.val = true → 48 ≤ u.val)
    (hSpec : ∀ β : BitAssignment (48 + kScr),
      (∀ u : Wire (48 + kScr), 48 ≤ u.val → β u = 0) →
      (∀ u : Fin 48, cp.fwdBits β ⟨u.val, sb48_in_lt kScr u⟩ = β ⟨u.val, sb48_in_lt kScr u⟩) ∧
      (∀ j : Fin 6, cp.fwdBits β ⟨48 + j.val, sb48_out_lt h6 j⟩ =
        if (pre6OfCoords
          (coordOfReg24 (QRegister.block 0 24 (sb48_a_le kScr)) β)
          (coordOfReg24 (QRegister.block 24 24 (sb48_b_le kScr)) β)).val.testBit j.val
        then 1 else 0)) :
    ShortBin7Pre6Pkg kScr tSB where
  h6 := h6
  wrapDom := fun v rA rB rScr mid ↦ wrapShortBin7OfCP cp v rA rB rScr mid
  step_and_counts := by
    intro Var _ _ W n _ v rWork rA rB rScr hAB hAS hBS st stPost phPre phPost mid
      hZero hPost hMid
    have hinj :=
        fReg48Plus_injective rA rB rScr hAB hAS hBS; simp only [wrapShortBin7OfCP,
        cDitePos (Fintype.decidableInjectiveFintype (fReg48Plus rA rB rScr)) hinj]
    set r48k : QRegister (48 + kScr) n := ⟨⟨fReg48Plus rA rB rScr, hinj⟩⟩
    have hScrIdx : ∀ u : Fin kScr, 48 + u.val < 48 + kScr := fun u ↦ Nat.add_lt_add_left u.isLt 48
    have hScrW : ∀ u : Fin kScr, r48k ⟨48 + u.val, hScrIdx u⟩ = rScr u := fun u ↦ by
      change fReg48Plus rA rB rScr ⟨48 + u.val, _⟩ = rScr u
      dsimp [fReg48Plus]; split_ifs
      · omega
      · omega
      · exact congrArg rScr.wires (Fin.ext (by dsimp; omega))
    have hBlkEq : r48k.compose (QRegister.block 48 kScr le_rfl) = rScr :=
      congrArg QRegister.mk (Function.Embedding.ext fun u ↦ hScrW u)
    have hCln48 : ∀ (δ : BitAssignment n), (∀ q : Fin W, δ (rWork q) = 0) →
        ∀ q : Wire (48 + kScr), 48 ≤ q.val → st δ (r48k q) = 0 := fun δ hz q hq ↦ by
      have heq : r48k q = rScr ⟨q.val - 48, sb48_sub48 (Nat.not_lt.mpr hq) q.isLt⟩ := by
        change fReg48Plus rA rB rScr q = _
        dsimp [fReg48Plus]; split_ifs <;> first | omega | rfl
      rw [heq]; exact hZero δ _ hz
    have hRes := subspaceStep_wrapOnReg_block2 le_rfl rfl hScrIdx v rWork r48k
      sMask cp nAnd tSB hValid hAnd htSB st stPost phPre phPost mid
      (fun u hu δ hz ↦ hCln48 δ hz u (hMaskGe u hu))
      (fun δ u hz ↦ by
        change stPost δ (fReg48Plus rA rB rScr u) = st δ (fReg48Plus rA rB rScr u)
        dsimp [fReg48Plus]; split_ifs
        · exact (hPost δ hz).1 _
        · exact (hPost δ hz).2.1 _
        · exact ((hPost δ hz).2.2 _).trans (hZero δ _ hz).symm)
      (fun δ hz u hlt ↦ (hSpec (fun q ↦ st δ (r48k q)) (hCln48 δ hz)).1 ⟨u.val, hlt⟩)
      (fun stMid hKeep hVal ↦ by
        have hPostCongr : (fun δ ↦ writeReg (stPost δ)
            (r48k.compose (QRegister.block 48 kScr le_rfl))
            (fun u ↦ stMid δ (r48k ⟨48 + u.val, hScrIdx u⟩))) =
            (fun δ ↦ writeReg (stPost δ) rScr (fun u ↦ stMid δ (rScr u))) := by
          funext δ; rw [hBlkEq]
          exact congrArg (writeReg (stPost δ) rScr) (funext fun u ↦ by rw [hScrW u])
        rw [hPostCongr]
        refine hMid stMid (fun δ w hw ↦ hKeep δ w (fun u hu ↦ hw u (hu.trans (hScrW u))))
            (fun δ hz j ↦ ?_)
        have hjW : rScr ⟨j.val, sbScr_lt6 h6 j⟩ = r48k ⟨48 + j.val, sb48_out_lt h6 j⟩ :=
            (hScrW ⟨j.val, sbScr_lt6 h6 j⟩).symm; rw [hjW, hVal δ ⟨48 + j.val, sb48_out_lt h6 j⟩ hz]
        have hOut := (hSpec (fun q ↦ st δ (r48k q)) (hCln48 δ hz)).2 j
        obtain ⟨hRA, hRB⟩ := fReg48Plus_coords rA rB rScr hinj (st δ); rw [hRA, hRB] at hOut
        exact hOut)
    exact ⟨hRes.1, hRes.2.1, hRes.2.2.1, fun S hSA hSB hSS hd ↦
      hRes.2.2.2 S (fun u ↦ by
        change S (fReg48Plus rA rB rScr u)
        dsimp [fReg48Plus]; split_ifs <;> [exact hSA _; exact hSB _; exact hSS _]) hd⟩
end QuantumComputation.Specs.PhotochemistrySolution.ShortBin7Pre6ZHi30
namespace QuantumComputation.Specs.PhotochemistrySolution.Sh14P5Mux17
open Qubit PhotochemistrySolution
open _root_.QuantumComputation.Specs.PhotochemistrySolution.ShortBin7Pre6ZHi30 (validPre6Mask64
    oneHot6OfPre6 oneHot6OfPre6_lt pre6OfCoords pre6OfCoords_valid oneHot6OfPre6_pre6OfCoords)
-- Part A: Physical `ShortBin7Pre6ZHi30` & `pre6OfCoords` bridges
theorem pre6OneHot6S14_eq_oneHot6OfPre6 (p6 : Fin 64) : pre6OneHot6S14 p6.val =
    oneHot6OfPre6 p6.val := by
  revert p6
  decide +kernel
theorem pre5OfPre6_pre6OfCoords (cA cB : Fin 3 → Fin 256) : pre5OfPre6 (pre6OfCoords cA cB) =
    pre5OfFin8 (fin8Bin (openCoordDistSq cA cB))
    := by apply pre5OfPre6_eq_pre5OfFin8_of_oneHot6; rw [pre6OneHot6S14_eq_oneHot6OfPre6,
            oneHot6OfPre6_pre6OfCoords]
theorem owmbu_two_leg_kick_collapse (z30 v1 v2 w : ℕ) :
    let q1 := (z30 / 2 ^ 14 + v1 % 2 ^ 16) / 2 ^ 16 + v1 / 2 ^ 16;
    let zHi1 := (z30 / 2 ^ 14 + v1 % 2 ^ 16) % 2 ^ 16;
    let q2 := (zHi1 + v2 % 2 ^ 16) / 2 ^ 16 + v2 / 2 ^ 16;
    let zHi2 := (zHi1 + v2 % 2 ^ 16) % 2 ^ 16; let zMid30 := z30 % 2 ^ 14 + 2 ^ 14 * zHi2;
    let tMod31 := (v1 * 2 ^ 14 + v2 * 2 ^ 14 + w) % 2 ^ 31
    zHi2 = (z30 / 2 ^ 14 + v1 + v2) % 2 ^ 16 ∧ (zMid30 + w) + 2 ^ 30 * (q1 + q2) = z30 +
        (v1 * 2 ^ 14 + v2 * 2 ^ 14 + w) ∧
    (q1 + q2 + (zMid30 + w) / 2 ^ 30) % 2 = ((tMod31 + z30) / 2 ^ 30) % 2 ∧
    Bool.xor (Bool.xor (q1 % 2 == 1) (q2 % 2 == 1)) ((zMid30 + w).testBit 30) =
        (tMod31 + z30).testBit 30 := by
  dsimp only
  set zHi1 := (z30 / 2 ^ 14 + v1 % 2 ^ 16) % 2 ^ 16
  set q1 := (z30 / 2 ^ 14 + v1 % 2 ^ 16) / 2 ^ 16 + v1 / 2 ^ 16
  set q2 := (zHi1 + v2 % 2 ^ 16) / 2 ^ 16 + v2 / 2 ^ 16
  set zMid := z30 % 2 ^ 14 + 2 ^ 14 * ((zHi1 + v2 % 2 ^ 16) % 2 ^ 16)
  set S := v1 * 2 ^ 14 + v2 * 2 ^ 14 + w
  have _ : _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ :=
    ⟨Nat.div_add_mod v1 (2 ^ 16), Nat.div_add_mod v2 (2 ^ 16), Nat.div_add_mod z30 (2 ^ 14),
      Nat.div_add_mod (z30 / 2 ^ 14 + v1 % 2 ^ 16) (2 ^ 16), Nat.div_add_mod (zHi1 + v2 % 2 ^ 16)
          (2 ^ 16),
      Nat.div_add_mod S (2 ^ 31), Nat.div_add_mod (zMid + w) (2 ^ 30), Nat.div_add_mod (S % 2 ^ 31 +
          z30) (2 ^ 30)⟩
  have hPar : (q1 + q2 + (zMid + w) / 2 ^ 30) % 2 = ((S % 2 ^ 31 + z30) / 2 ^ 30) % 2 := by omega
  refine ⟨by omega, by omega, hPar, ?_⟩
  have hp : (q1 % 2 + q2 % 2 + (zMid + w) / 2 ^ 30 % 2) % 2 = (S % 2 ^ 31 + z30) / 2 ^ 30 % 2 := by
    omega
  have hxor (a b c d : ℕ) (ha : a = 0 ∨ a = 1) (hb : b = 0 ∨ b = 1) (hc : c = 0 ∨ c = 1)
      (hd : d = 0 ∨ d = 1) (h : (a + b + c) % 2 = d) :
      Bool.xor (Bool.xor (a == 1) (b == 1)) (decide (c = 1)) = decide (d = 1) := by
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
      rcases hc with rfl | rfl <;> rcases hd with rfl | rfl <;> first | omega | rfl
  rw [Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq]
  exact hxor _ _ _ _ (Nat.mod_two_eq_zero_or_one _) (Nat.mod_two_eq_zero_or_one _)
    (Nat.mod_two_eq_zero_or_one _) (Nat.mod_two_eq_zero_or_one _) hp

end QuantumComputation.Specs.PhotochemistrySolution.Sh14P5Mux17
namespace QuantumComputation.Specs.PhotochemistrySolution.ReflStage4
theorem ow0_lt5 : 0 < 5 := by omega
theorem ow1_lt5 : 1 < 5 := by omega
theorem ow2_lt5 : 2 < 5 := by omega
theorem ow3_lt5 : 3 < 5 := by omega
theorem ow4_lt5 : 4 < 5 := by omega
end QuantumComputation.Specs.PhotochemistrySolution.ReflStage4

namespace QuantumComputation.Specs.PhotochemistrySolution.Stage2ElecFirst

open Operator QProg Matrix Circuit Qubit PrimitiveGate QuantumComputation.Specs
  PhotochemistrySolution
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
open PhotochemistrySolution.SelectOracles PhotochemistrySolution.PotSelectWiring
  PhotochemistrySolution.SplitRouter47_187 PhotochemistrySolution.UnembedO3Bridge
open PhotochemistrySolution.RouterSelectWiringA PhotochemistrySolution.ProviderCore
  PhotochemistrySolution.RouterSelectWiringB PhotochemistrySolution.Stage12Compact
open PhotochemistrySolution.ZeroNEremSpec PhotochemistrySolution.Stage2Xor84
  PhotochemistrySolution.Stage2PotUnld
open _root_.DynamicCircuit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt hiding ket matrix_ext_ket
  qAssign_obs_map_val ket_projector_zero ket_projector_one ket_X ket_CNOT ket_TOFF eval_seq_mulVec
  bit_cases
attribute [local irreducible] systemQubits_frozen SelectCompactAnc.ancWOfScr
/-- Pointwise commutation of `routerSwapBits rNucLayout` and `routerSwapBits rElecLayout`. -/
theorem routerSwap_nuc_elec_comm {δ : BitAssignment dLayout} (hVN : ValidRouterInput rNucLayout δ)
    (hVE : ValidRouterInput rElecLayout δ) :
    routerSwapBits rNucLayout (routerSwapBits rElecLayout δ) =
      routerSwapBits rElecLayout (routerSwapBits rNucLayout δ) := by
  have ⟨_, _⟩ := And.intro hEW5056 hNW1394
  have out_of {M D : ℕ} (r : RouterReg M D dLayout) {φ : BitAssignment dLayout}
      (hV : ValidRouterInput r φ)
      {w : Wire dLayout} (hNe : ∀ (k : ℕ) (hk : k < routerWidth M D),
        ((2 + 2 * D ≤ k ∧ k < 50 + 2 * D) ∨ (98 + 2 * D ≤ k ∧ k < 98 + 2 * D + 24 * M)) → w ≠
            r ⟨k, hk⟩) :
      routerSwapBits r φ w = φ w :=
    routerSwapBits_outside_mod r hV (fun b ↦ hNe (2 + 2 * D + b.val)
        (by
          unfold routerWidth
          omega) (by omega))
      (fun b ↦ hNe (26 + 2 * D + b.val) (by
        unfold routerWidth
        omega) (by omega))
      (fun p b ↦ hNe (98 + 2 * D + 24 * p.val + b.val) (by
        unfold routerWidth
        omega) (by omega))
  have outE {φ} (hV : ValidRouterInput rElecLayout φ) {w : Wire dLayout}
      (hw : ¬ ((1128 ≤ w.val ∧ w.val ≤ 5615) ∨ (5851 ≤ w.val ∧ w.val ≤ 5898))) :
      routerSwapBits rElecLayout φ w = φ w :=
    out_of rElecLayout hV fun k hk h ↦ fun e ↦
        hw (val_elecRouterWireFn ⟨k, hk⟩ |> fun hv : (rElecLayout _).val = _ ↦ by
      rw [← e] at hv
      dsimp at hv h
      split_ifs at hv <;> omega)
  have outN {φ} (hV : ValidRouterInput rNucLayout φ) {w : Wire dLayout}
      (hw : ¬ (w.val < 1128 ∨ (5755 ≤ w.val ∧ w.val ≤ 5802))) :
      routerSwapBits rNucLayout φ w = φ w :=
    out_of rNucLayout hV fun k hk h ↦ fun e ↦
        hw (val_nucRouterWireFn ⟨k, hk⟩ |> fun hv : (rNucLayout _).val = _ ↦ by
      rw [← e] at hv
      dsimp at hv h
      split_ifs at hv <;> omega)
  have allN (i : Fin (routerWidth 47 6)) : routerSwapBits rElecLayout δ (rNucLayout i) =
      δ (rNucLayout i) :=
    outE hVE (val_rNuc_bounds i |> fun _ ↦ by omega)
  have allE (j : Fin (routerWidth 187 8)) : routerSwapBits rNucLayout δ (rElecLayout j) =
      δ (rElecLayout j) :=
    outN hVN (val_rElec_bounds j |> fun _ ↦ by omega)
  have valid_of_eq {M D : ℕ} (r : RouterReg M D dLayout) {φ : BitAssignment dLayout}
      (hV : ValidRouterInput r δ) (hEq : ∀ k : Fin (routerWidth M D), φ (r k) = δ (r k)) :
          ValidRouterInput r φ :=
    have eqI (rI : Fin D → Wire dLayout) (h : ∀ x : Fin D, φ (rI x) = δ (rI x)) : idxValD rI φ =
        idxValD rI δ :=
      Nat.eq_of_testBit_eq fun d ↦
          by
            rw [testBit_idxValD, testBit_idxValD]
            split_ifs <;> simp [h]
    ⟨fun h2 ↦ (hEq _).trans (hV.1 ((hEq _).symm.trans h2)),
      by simpa only [rHas1, hEq, eqI (rIdx1 r) fun x ↦ hEq ⟨2 + x.val, rw_ltIdx1 x⟩] using hV.2.1,
      fun h2 ↦
          (eqI (rIdx2 r) fun x ↦ hEq ⟨2 + D + x.val,
          rw_ltIdx2 x⟩).trans_lt (hV.2.2.1 ((hEq _).symm.trans h2)),
      fun b ↦ by simpa only [rBufLo, rBufHi, rHA, rHB, hEq] using hV.2.2.2.1 b,
      fun u hu ↦ let ⟨j, hj, hju⟩ := Finset.mem_image.mp hu
        hju ▸ (hEq j).trans (hV.2.2.2.2 (r j) (Finset.mem_image.mpr ⟨j, hj, rfl⟩))⟩
  exact funext fun w ↦ if hwN : w.val < 1128 ∨ (5755 ≤ w.val ∧ w.val ≤ 5802) then
    (routerSwapBits_congr_pub rNucLayout (fun i _ ↦ allN i) (outE hVE (by omega))).trans
      (outE (valid_of_eq rElecLayout hVE allE) (by omega)).symm
  else (outN (valid_of_eq rNucLayout hVN allN) hwN).trans
    (routerSwapBits_congr_pub rElecLayout (fun j _ ↦ allE j) (outN hVN hwN)).symm

end QuantumComputation.Specs.PhotochemistrySolution.Stage2ElecFirst

section
open Operator QProg Matrix Circuit Qubit PrimitiveGate QuantumComputation.Specs
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
open QuantumComputation.Specs.PhotochemistrySolution
  QuantumComputation.Specs.PhotochemistrySolution.SelectOracles
  QuantumComputation.Specs.PhotochemistrySolution.PotSelectWiring
  QuantumComputation.Specs.PhotochemistrySolution.XMeasChunkQromUnldA
open _root_.QuantumComputation.Specs.PhotochemistrySolution.QubitizationWalkSem (bitSign)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB (ket matrix_ext_ket)
namespace QuantumComputation.Specs.PhotochemistrySolution.Coin70Lift
open PhotochemistrySolution.XMeasChunkQromUnld PhotochemistrySolution.DynQromUncompA
  PhotochemistrySolution.Sub5885
local instance (priority := 100000) {k : ℕ} : NeZero (2 ^ k) := ⟨pow_ne_zero k two_ne_zero⟩
attribute [local irreducible] systemQubits_frozen SelectCompactAnc.ancWOfScr
theorem dite_pos_c70 {α : Sort*} {P : Prop} (inst : Decidable P) (hp : P) {a : P → α} {b : ¬ P →
  α} : @dite α P inst a b = a hp := by
  cases inst with | isTrue _ => rfl | isFalse hn => exact absurd hp hn
/-- Lift a `[Fintype Var] [DecidableEq Var]` circuit builder to arbitrary `Var`. -/
noncomputable def liftFinDyn_c70 {Var : Type} {n : ℕ} (f : [Fintype Var] → [DecidableEq Var] →
    DynamicCircuit Var n) : DynamicCircuit Var n :=
    @dite _ (Finite Var) (Classical.dec (Finite Var)) (fun hf ↦ @f (@Fintype.ofFinite Var hf)
    (Classical.decEq Var)) (fun _ ↦ .identity)
theorem liftFinDyn_eq_c70 {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    (f : [Fintype Var] → [DecidableEq Var] → DynamicCircuit Var n) : liftFinDyn_c70 f = f := by
  exact (dite_pos_c70 (Classical.dec (Finite Var)) inferInstance).trans <| by
    rw [Subsingleton.elim (@Fintype.ofFinite Var inferInstance) ‹_›,
      show Classical.decEq Var = ‹_› from funext fun _ ↦ funext fun _ ↦ Subsingleton.elim _ _]
end QuantumComputation.Specs.PhotochemistrySolution.Coin70Lift

namespace QuantumComputation.Specs.PhotochemistrySolution.ReflStage4
open _root_.DynamicCircuit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt hiding ket matrix_ext_ket
local instance (priority := 100000) {k : ℕ} : NeZero (2 ^ k) := ⟨pow_ne_zero k two_ne_zero⟩
/-- Inner-coin permutation `(isScreen, isNN, sp1, sp2, nA, nB, eA, eB, z) → z'`. -/
abbrev PotBCoinSwapFn : Type :=
  Bool → Bool → Fin 4 → Fin 4 →
    (Fin 3 → Fin 256) → (Fin 3 → Fin 256) →
    (Fin 3 → Fin 256) → (Fin 3 → Fin 256) → BitAssignment 41 → BitAssignment 41
/--
Routed Stage-4 flag validity: `isPot = 0 → isScreen = 0 ∧ isNN = 0` and
`isScreen = 0 → isNN = 0` (matching `Sh14P5Mux17` guard).
-/
def ValidPotBFlags {W n : ℕ} (r : QRegister (122 + W) n) (β : BitAssignment n) : Prop :=
  (β (wPotBIsPot r) = 0 → β (wPotBIsScreen r) = 0 ∧ β (wPotBIsNN r) = 0) ∧
    (β (wPotBIsScreen r) = 0 → β (wPotBIsNN r) = 0)
/-- 3-port inner-coin permutation read from `r : QRegister (122 + W) n`. -/
abbrev potOraclePortBCoinEval {W n : ℕ} (coinSwap : PotBCoinSwapFn) (r : QRegister (122 + W) n)
    (δ : BitAssignment n) : BitAssignment 41 :=
  coinSwap (δ (wPotBIsScreen r) == 1) (δ (wPotBIsNN r) == 1)
    (speciesOfBits2 (δ (wPotBSp1B0 r)) (δ (wPotBSp1B1 r)))
    (speciesOfBits2 (δ (wPotBSp2B0 r)) (δ (wPotBSp2B1 r)))
    (coordOfReg24 (rPotBNucA r) δ)
    (if δ (wPotBIsNN r) == 1 then coordOfReg24 (rPotBPortB r) δ else 0)
    (coordOfReg24 (rPotBElecA r) δ)
    (if δ (wPotBIsNN r) == 1 then 0 else coordOfReg24 (rPotBPortB r) δ)
    (fun k ↦ δ (rPotBCoin41 r k))
/-- 4-port inner-coin permutation read from `r : QRegister (146 + W) n`. -/
abbrev potOracleCoinEval {W n : ℕ} (coinSwap : PotBCoinSwapFn) (r : QRegister (146 + W) n)
    (δ : BitAssignment n) : BitAssignment 41 :=
  coinSwap (δ (wPotIsScreen r) == 1) (δ (wPotIsNN r) == 1)
    (speciesOfBits2 (δ (wPotSp1B0 r)) (δ (wPotSp1B1 r)))
    (speciesOfBits2 (δ (wPotSp2B0 r)) (δ (wPotSp2B1 r)))
    (coordOfReg24 (rPotNucA r) δ) (coordOfReg24 (rPotNucB r) δ)
    (coordOfReg24 (rPotElecA r) δ) (coordOfReg24 (rPotElecB r) δ)
    (fun k ↦ δ (rPotCoin41 r k))
/-- Active gate boolean (`locQ && isPot` on `Csel`, `isPot` on `Usel`). -/
def potBGateActive {W n : ℕ} (isCsel : Bool) (r : QRegister (122 + W) n) (δ : BitAssignment n) :
    Bool :=
    if isCsel then (δ (wPotBLocQ r) == 1) && (δ (wPotBIsPot r) == 1) else (δ (wPotBIsPot r) == 1)
def potReflPortBSt {kExt W n : ℕ} (coinSwapK : BitAssignment kExt → PotBCoinSwapFn) (isCsel : Bool)
    (r : QRegister (122 + W) n) (rCoin : QRegister kExt n) (st : BitAssignment n → BitAssignment n)
    (δ : BitAssignment n) : BitAssignment n :=
  if potBGateActive isCsel r (st δ) then
    writeReg (st δ) (rPotBCoin41 r)
      (potOraclePortBCoinEval (coinSwapK (fun j ↦ st δ (rCoin j))) r (st δ))
  else st δ
/-- Post-phase of a reflected 3-port potential oracle starting from zero phase. -/
def potReflPortBPh0 {kExt W n : ℕ} (phaseBitK : BitAssignment kExt → PotBPhaseBitFn) (isCsel : Bool)
    (r : QRegister (122 + W) n) (rCoin : QRegister kExt n) (st : BitAssignment n → BitAssignment n)
    (δ : BitAssignment n) : ZMod 2 :=
  (if isCsel then st δ (wPotBLocQ r) * st δ (wPotBIsPot r) else st δ (wPotBIsPot r)) *
    potOraclePortBBitEval (phaseBitK (fun j ↦ st δ (rCoin j))) r (st δ)
/-- Per-`γ` reflected Stage-4 potential slice specification on `dLayout`. -/
structure ReflPotSliceSpec (potExpect : PotExpectFn) where
  phaseBit : PotBPhaseBitFn
  coinSwap : PotBCoinSwapFn
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
  avg_coin41 : ∀ (isScreen isNN : Bool) (sp1 sp2 : Fin 4) (nA nB eA eB : Fin 3 → Fin 256),
    (2 ^ 41 : ℂ)⁻¹ *
      (∑ z : BitAssignment 41, bitSign (phaseBit isScreen isNN sp1 sp2 nA nB eA eB z)) =
      (potExpect isScreen isNN sp1 sp2 nA nB eA eB : ℂ)
/--
Reflected 3-port `PortB` Stage-4 potential oracle with asymmetric `(tPotU, tPotC)` `T`-counts
and involutive inner-coin reflection `coinSwapK` (`U_{g=0} = I`).
-/
structure Stage4ReflCoinKPotOraclePortB (kExt Wp tPotU tPotC : ℕ)
    (potExpectK : BitAssignment kExt → PotExpectFn) where
  phaseBitK : BitAssignment kExt → PotBPhaseBitFn
  coinSwapK : BitAssignment kExt → PotBCoinSwapFn
  pCsel : ∀ {Var : Type} {n : ℕ},
    Var → QRegister (122 + Wp) n → QRegister kExt n → DynamicCircuit Var n
  pUsel : ∀ {Var : Type} {n : ℕ},
    Var → QRegister (122 + Wp) n → QRegister kExt n → DynamicCircuit Var n
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
    (r : QRegister (122 + Wp) n) (rCoin : QRegister kExt n)
    (_ : r.DisjointWires rCoin) (isCsel : Bool)
    (st : BitAssignment n → BitAssignment n),
    (∀ δ, (∀ q : Fin m, δ (rW q) = 0) → ValidPotBFlags r (st δ)) →
    (∀ δ (u : Fin Wp), (∀ q : Fin m, δ (rW q) = 0) → st δ (rPotBWork r u) = 0) →
    let p := if isCsel then pCsel v r rCoin else pUsel v r rCoin
    SubspaceStep (mkKetOpW rW st (fun _ ↦ 0))
      (mkKetOpW rW (potReflPortBSt coinSwapK isCsel r rCoin st)
        (potReflPortBPh0 phaseBitK isCsel r rCoin st)) p ∧
    p.count .T = (if isCsel then tPotC else tPotU) ∧
    p.count .TOFF = 0
  dynWires : ∀ {Var : Type} {n : ℕ} (S : Wire n → Prop) (v : Var)
    (r : QRegister (122 + Wp) n) (rCoin : QRegister kExt n),
    (∀ i : Fin (122 + Wp), S (r i)) → (∀ j : Fin kExt, S (rCoin j)) →
    DynWires S (pCsel v r rCoin) ∧ DynWires S (pUsel v r rCoin)
  avg_coin41 : ∀ (γ : BitAssignment kExt) (isScreen isNN : Bool) (sp1 sp2 : Fin 4)
    (nA nB eA eB : Fin 3 → Fin 256),
    (2 ^ 41 : ℂ)⁻¹ *
      (∑ zc : BitAssignment 41,
        bitSign (phaseBitK γ isScreen isNN sp1 sp2 nA nB eA eB zc)) =
      (potExpectK γ isScreen isNN sp1 sp2 nA nB eA eB : ℂ)
/-- Extract the per-`γ` `ReflPotSliceSpec` from a `Stage4ReflCoinKPotOraclePortB`. -/
def Stage4ReflCoinKPotOraclePortB.slice {kExt Wp tPotU tPotC : ℕ}
    {potExpectK : BitAssignment kExt → PotExpectFn}
    (o : Stage4ReflCoinKPotOraclePortB kExt Wp tPotU tPotC potExpectK)
    (γ : BitAssignment kExt) : ReflPotSliceSpec (potExpectK γ) where
  phaseBit := o.phaseBitK γ
  coinSwap := o.coinSwapK γ
  coinSwap_invol := o.coinSwap_invol γ
  phaseBit_coinSwap := o.phaseBit_coinSwap γ
  phaseBit_port := o.phaseBit_port γ
  coinSwap_port := o.coinSwap_port γ
  avg_coin41 := o.avg_coin41 γ
end QuantumComputation.Specs.PhotochemistrySolution.ReflStage4
end
end

noncomputable section
open QuantumComputation.Specs.PhotochemistrySolution.SortedRouterSpec
  QuantumComputation.Specs.PhotochemistrySolution.SplitBellVecCleanStep Operator QProg Matrix
  Circuit Qubit QuantumComputation.Specs.PhotochemistrySolution
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
namespace QuantumComputation.Specs.PhotochemistrySolution.EvenOctB70
open _root_.DynamicCircuit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt hiding bit_cases ket ket_CNOT
  ket_TOFF ket_X ket_projector_one ket_projector_zero localIdx matrix_ext_ket qAssign_obs_map_val
open PhotochemistrySolution.FineLegendre PhotochemistrySolution.PotOracleGen
  PhotochemistrySolution.UnembedO3Bridge
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt (writeReg writeReg_apply_reg
  writeReg_apply_of_not_mem)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB (ket matrix_ext_ket)
/-- `0 T` pointwise CNOT vector `rSrc[b] -> rDst[b]` across `b = 0 .. k - 1`. -/
def cnotVecAux {B n : ℕ} (rSrc rDst : QRegister B n) (hDisj : rSrc.DisjointWires rDst) :
    ∀ k : ℕ, k ≤ B → Circuit n
  | 0, _ => .identity
  | k + 1, hk =>
      .seq (cnotVecAux rSrc rDst hDisj k (Nat.le_of_succ_le hk))
        (Circuit.CNOT (rSrc ⟨k, hk⟩) (rDst ⟨k, hk⟩) (disj_ne hDisj ⟨k, hk⟩ ⟨k, hk⟩))
theorem cnotVecAux_counts {B n : ℕ} (rSrc rDst : QRegister B n)
    (hDisj : rSrc.DisjointWires rDst) :
    ∀ (k : ℕ) (hk : k ≤ B),
      (cnotVecAux rSrc rDst hDisj k hk).count .T = 0 ∧
      (cnotVecAux rSrc rDst hDisj k hk).count .TOFF = 0
  | 0, _ => ⟨rfl, rfl⟩
  | k + 1, hk =>
      let ⟨ht, hf⟩ := cnotVecAux_counts rSrc rDst hDisj k (Nat.le_of_succ_le hk)
      ⟨by simpa [cnotVecAux, Circuit.count_seq, Circuit.CNOT] using ht,
       by simpa [cnotVecAux, Circuit.count_seq, Circuit.CNOT] using hf⟩
theorem cnotVecAux_wires {B n : ℕ} {S : Wire n → Prop}
    (rSrc rDst : QRegister B n) (hDisj : rSrc.DisjointWires rDst)
    (hS : ∀ b, S (rSrc b)) (hD : ∀ b, S (rDst b)) :
    ∀ (k : ℕ) (hk : k ≤ B), CircWires S (cnotVecAux rSrc rDst hDisj k hk)
  | 0, _ => trivial
  | k + 1, hk =>
      ⟨cnotVecAux_wires rSrc rDst hDisj hS hD k (Nat.le_of_succ_le hk),
       fun | ⟨0, _⟩ => hS ⟨k, hk⟩ | ⟨1, _⟩ => hD ⟨k, hk⟩⟩
theorem cnotVecAux_ket {B n : ℕ} (rSrc rDst : QRegister B n)
    (hDisj : rSrc.DisjointWires rDst) (β : BitAssignment n) :
    ∀ (k : ℕ) (hk : k ≤ B),
      (cnotVecAux rSrc rDst hDisj k hk).eval.1.mulVec (ket β) =
        ket (writeReg β rDst (fun b ↦ if b.val < k then β (rDst b) + β (rSrc b) else β (rDst b)))
  | 0, _ => by
      simpa [cnotVecAux, Circuit.eval_identity, show writeReg β rDst (fun b ↦ β (rDst b)) = β from
        funext fun w ↦
            (em (∃ b, rDst b = w)).elim (fun ⟨b, hb⟩ ↦ hb ▸ writeReg_apply_reg β rDst _ b)
          (writeReg_apply_of_not_mem β rDst _ w)] using Matrix.one_mulVec (ket β)
  | k + 1, hk => by
      dsimp only [cnotVecAux]
      rw [DynCircExt.eval_seq_mulVec, cnotVecAux_ket rSrc rDst hDisj β k (Nat.le_of_succ_le hk),
        DynCircExt.ket_CNOT]
      refine congrArg ket (funext fun w ↦ ?_)
      rcases eq_or_ne w (rDst ⟨k, hk⟩) with rfl | hw
      · simp [writeReg_apply_reg, add_comm,
          writeReg_apply_of_not_mem β rDst _ (rSrc ⟨k, hk⟩) fun ⟨b, hb⟩ ↦
              disj_ne hDisj ⟨k, hk⟩ b hb.symm]
      · rw [Function.update_of_ne hw]
        exact (em (∃ b, rDst b = w)).elim (fun ⟨b, hb⟩ ↦ by
          subst hb
          have _ : b.val ≠ k := fun e ↦ hw (congrArg rDst.wires (Fin.ext e))
          simp only [writeReg_apply_reg]
          split_ifs <;> first | rfl | omega) fun hm ↦
          (writeReg_apply_of_not_mem _ rDst _ w hm).trans (writeReg_apply_of_not_mem _ rDst _ w
              hm).symm

theorem subspaceStep_cnotVec {Var : Type} [Fintype Var] [DecidableEq Var]
    {B W n : ℕ} [NeZero (2 ^ n)]
    (rWork : QRegister W n) (rSrc rDst : QRegister B n) (hDisj : rSrc.DisjointWires rDst)
    (st : BitAssignment n → BitAssignment n) (ph : BitAssignment n → ZMod 2) :
    SubspaceStep (Var := Var) (mkKetOpW rWork st ph)
      (mkKetOpW rWork (fun δ ↦ writeReg (st δ) rDst (fun b ↦ st δ (rDst b) + st δ (rSrc b))) ph)
      (.circuit (cnotVecAux rSrc rDst hDisj B le_rfl)) := by
  exact (show (cnotVecAux rSrc rDst hDisj B le_rfl).eval.1 * mkKetOpW rWork st ph =
      mkKetOpW rWork (fun δ ↦ writeReg (st δ) rDst (fun b ↦ st δ (rDst b) + st δ (rSrc b))) ph from
    matrix_ext_ket fun δ ↦ by
      rw [← Matrix.mulVec_mulVec, mkKetOpW_mulVec_ket, mkKetOpW_mulVec_ket]
      split_ifs with hz
      · rw [Matrix.mulVec_smul, cnotVecAux_ket]
        simp
      · rw [Matrix.mulVec_zero]) ▸
    subspaceStep_of_circuit (Var := Var) (mkKetOpW rWork st ph)
        (cnotVecAux rSrc rDst hDisj B le_rfl)

end QuantumComputation.Specs.PhotochemistrySolution.EvenOctB70

section
open HermitianMat QuantumComputation.Specs.PhotochemistrySolution.SplitRouter47_187
open _root_.DynamicCircuit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt hiding bit_cases
  eval_seq_mulVec ket ket_CNOT ket_TOFF ket_X ket_projector_one ket_projector_zero matrix_ext_ket
  qAssign_obs_map_val
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB hiding bitSign eval_seq_mulVec ket
  ket_CNOT ket_TOFF ket_X matrix_ext_ket writeReg writeReg_apply_of_not_mem
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SplitRouterSeqBell26k hiding ket
  matrix_ext_ket
namespace QuantumComputation.Specs.PhotochemistrySolution.Stage2ZeroGated
attribute [local semireducible] ComputeProg.fwdBits
/--
Exact 4-conjunct classical control invariant shape for `SplitRouterMuxD1` across Mode 0,
Mode 1 (phantom `2 ^ D - 1`), and Mode 2 (`pOnly1` and `pUMsb 0` unconstrained).
-/
abbrev ValidPlaneCtrlD1Shape {M D n : ℕ} (r : PlaneReg M D n) (β : BitAssignment n) : Prop :=
    (β (pHas2Eff r) = 1 → β (pHas1 r) = 1) ∧ (β (pHas1 r) = 0 → (∀ p : Fin M, β (pCtrlLo r p) = 0) ∧
    (∀ d : Fin D, β (pNotMin r d) = 0) ∧ (∀ d : Fin D, 1 ≤ d.val → β (pUMsb r d) = 0)) ∧
    (β (pHas2Eff r) = 0 → (∀ p : Fin M, β (pCtrlHi r p) = 0) ∧ (∀ d : Fin D, β (pNotMax r d) = 0)) ∧
    (β (pHas1 r) = 1 → ∃ pMin : Fin M, β (pCtrlLo r pMin) = 1 ∧ (∀ p : Fin M, p ≠ pMin →
    β (pCtrlLo r p) = 0) ∧ (∀ d : Fin D, β (pNotMin r d) =
    if pMin.val.testBit d.val then 0 else 1) ∧ (β (pHas2Eff r) = 0 → ∃ dStar : Fin D,
    pMin.val.testBit dStar.val = false ∧ (∀ d : Fin D, 1 ≤ d.val → β (pUMsb r d) = if d =
    dStar then 1 else 0)) ∧ (β (pHas2Eff r) = 1 → ∃ pMax : Fin M, pMin.val < pMax.val ∧
    β (pCtrlHi r pMax) = 1 ∧ (∀ p : Fin M, p ≠ pMax → β (pCtrlHi r p) = 0) ∧
    (∀ d : Fin D, β (pNotMax r d) = if pMax.val.testBit d.val then 0 else 1) ∧ ∃ dStar : Fin D,
    pMin.val.testBit dStar.val = false ∧ pMax.val.testBit dStar.val = true ∧ (∀ d : Fin D, 1 ≤
    d.val → β (pUMsb r d) = if d = dStar then 1 else 0)))
theorem validPlaneD1_of_pHdrD1ZG {M D n : ℕ} (hMD : M < 2 ^ D) (hD2 : 2 ≤ D) (r : RouterReg M D n)
    {β γ η : BitAssignment n} (hβ : ValidZeroGatedSortedRouterInput r β)
    (hAg : AgreesBeforeHdr r β γ) (hLo : ∀ p : Fin M, η (rCtrlLo r p) = routerCtrlLo r β p)
    (hHi : ∀ p : Fin M, η (rCtrlHi r p) = routerCtrlHi r β p)
    (hOth : ∀ w : Wire n, (∀ p, w ≠ rCtrlLo r p) → (∀ p, w ≠ rCtrlHi r p) → η w =
    (pHdrD1ZG hD2 r).fwdBits γ w)
    (b : Fin 24) : ValidPlaneCtrlD1Shape (planeOfRouter (rHas2Alias r) b) η ∧
    ValidPlaneClean (planeOfRouter (rHas2Alias r) b) η := by
  let δ := (pHdrD1ZG hD2 r).fwdBits γ
  let pr := planeOfRouter (rHas2Alias r) b
  obtain ⟨rH1, rH2, _, rBL, rBH, rHAe, rHBe, rAn, rUM, rNM1, rNM2, rAM, rCR, rCL, rCH, _⟩ :=
    planeOfRouter_rHas2Alias_roles r b
  have hSupp := progSupportedIn_pHdrD1ZG hD2 r (P := fun w ↦ ∃ u : Fin (routerWidth M D),
    (u.val < 2 + 2 * D ∨ (basePub M D + 6 ≤ u.val ∧ u.val < basePub M D + 6 + 2 * D) ∨
      (basePub M D + 7 + 2 * D + 2 * M ≤ u.val ∧ u.val < basePub M D + 7 + 3 * D + 2 * M)) ∧ w =
          r u)
    (fun {u} hu ↦ ⟨u, hu, rfl⟩)
  have hOthIdx {u : Fin (routerWidth M D)}
      (hu : u.val < basePub M D + 6 + 2 * D ∨ basePub M D + 6 + 2 * D + 2 * M ≤ u.val) : η (r u) =
          δ (r u) :=
    hOth (r u) (fun p ↦ rr_ne r (by
      cases p
      dsimp [basePub] at hu ⊢
      omega))
      (fun p ↦ rr_ne r (by
        cases p
        dsimp [basePub] at hu ⊢
        omega))
  have hCln {w : Wire n} {u : Fin (routerWidth M D)} (hw : w = r u)
      (hu : (2 + 2 * D ≤ u.val ∧ u.val < basePub M D) ∨ basePub M D + 7 + 3 * D + 2 * M ≤ u.val)
      (h0 : γ (r u) = 0) : η w = 0 :=
    (congrArg η hw).trans <| ((hOthIdx (by omega)).trans (fwdBits_eq_of_not_supp _ hSupp γ fun ⟨_,
        hu', eqw⟩ ↦
        r.wires.injective eqw |> congrArg Fin.val |> fun _ ↦
            by
              unfold basePub at hu hu'
              omega)).trans h0
  obtain ⟨dH1, dH2, dNM1, dNM2, dU0, dU1, dU2⟩ := fwdBits_pHdrD1ZG_spec hMD hD2 r hβ hAg
  have ηH1 : η (rHas1 r) = β (rHas1 r) :=
      (hOthIdx (Or.inl (by
        dsimp [basePub]
        omega))).trans dH1
  have ηH2 : η (rRawHas2 r) = β (rRawHas2 r) :=
      (hOthIdx (Or.inl (by
        dsimp [basePub]
        omega))).trans dH2
  have ηNM1 (d : Fin D) : η (rNotMin r d) = β (rHas1 r) + β (rIdx1 r d) :=
    (hOthIdx (Or.inl (by
      cases d
      dsimp
      omega))).trans (dNM1 d)
  have ηNM2 (d : Fin D) : η (rNotMax r d) = β (rRawHas2 r) + β (rIdx2 r d) :=
    (hOthIdx (Or.inl (by
      cases d
      dsimp
      omega))).trans (dNM2 d)
  have ηUM (d : Fin D) : η (rUMsb r d) = δ (rUMsb r d) :=
      hOthIdx (Or.inr (by
        cases d
        dsimp
        omega))
  have cLo := routerCtrlLo_of_zeroGatedSorted hβ
  have cHi := routerCtrlHi_of_zeroGatedSorted hβ
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ⟨hCln (rBL.trans (planeOfRouter_bufLo _ b))
       (Or.inl ⟨by
         dsimp
         omega, by
         cases b
         dsimp [basePub]
         omega⟩) (hAg.2.2.2.2.1 b).1,
     hCln (rBH.trans (planeOfRouter_bufHi _ b))
       (Or.inl ⟨by
         dsimp
         omega, by
         cases b
         dsimp [basePub]
         omega⟩)
           (hAg.2.2.2.2.1 b).2.1,
     hCln (rHAe.trans (planeOfRouter_hA _ b))
       (Or.inl ⟨by
         dsimp
         omega, by
         cases b
         dsimp [basePub]
         omega⟩)
           (hAg.2.2.2.2.1 b).2.2.1,
     hCln (rHBe.trans (planeOfRouter_hB _ b))
       (Or.inl ⟨by
         dsimp
         omega, by
         cases b
         dsimp [basePub]
         omega⟩)
           (hAg.2.2.2.2.1 b).2.2.2,
     fun d ↦ hCln (congrFun rAM d) (Or.inr (by
       dsimp
       omega)) (hAg.2.2.2.2.2.2 d).2.2.2.1,
     fun d ↦ hCln (congrFun rCR d) (Or.inr (by
       dsimp
       omega)) (hAg.2.2.2.2.2.2 d).2.2.2.2,
     hCln rAn (Or.inr (by
       dsimp
       omega)) hAg.2.2.2.2.2.1⟩⟩
  · rw [rH2, rH1, ηH2, ηH1]
    exact hβ.1.1
  · rw [rH1, ηH1]
    exact fun hz1 ↦ ⟨fun p ↦ by rw [congrFun rCL p, hLo p, congrFun cLo p, hz1, ite_self],
      fun d ↦ by rw [congrFun rNM1 d, ηNM1 d, hz1, hβ.2.1 hz1 d, add_zero],
      fun d _ ↦ (congrArg η (congrFun rUM d)).trans ((ηUM d).trans (dU0 hz1 d))⟩
  · rw [rH2, ηH2]
    exact fun hz2 ↦ ⟨fun p ↦ by rw [congrFun rCH p, hHi p, congrFun cHi p, hz2, ite_self],
      fun d ↦ by rw [congrFun rNM2 d, ηNM2 d, hz2, hβ.2.2.1 hz2 d, add_zero]⟩
  · rw [rH1, rH2, ηH1, ηH2]
    intro ho1
    let pMin : Fin M := ⟨idxValD (rIdx1 r) β, hβ.1.2.1 ho1⟩
    refine ⟨pMin, by rw [congrFun rCL pMin, hLo pMin, congrFun cLo pMin, ite_eq_left rfl, ho1],
      fun p hp ↦ by rw [congrFun rCL p, hLo p, congrFun cLo p, ite_eq_right (hp ∘ Fin.ext)],
      fun d ↦ (congrArg η (congrFun rNM1 d)).trans ((ηNM1 d).trans
        ((congrArg (· + β (rIdx1 r d)) ho1).trans (not_flag_of_one (rIdx1 r) β d))),
      fun hz2 ↦ match dU1 ho1 hz2 with
      | ⟨dStar, hb1, hU⟩ =>
            ⟨dStar, hb1, fun d _ ↦ (congrArg η (congrFun rUM d)).trans ((ηUM d).trans (hU d))⟩,
      fun ho2 ↦ match dU2 ho1 ho2 with
      | ⟨dStar, hb1, hb2, hU⟩ =>
        ⟨⟨idxValD (rIdx2 r) β, hβ.1.2.2.1 ho2⟩, hβ.2.2.2 ho2,
          by rw [congrFun rCH _, hHi _, congrFun cHi _, ite_eq_left rfl, ho2],
          fun p hp ↦ by rw [congrFun rCH p, hHi p, congrFun cHi p, ite_eq_right (hp ∘ Fin.ext)],
          fun d ↦ (congrArg η (congrFun rNM2 d)).trans ((ηNM2 d).trans
            ((congrArg (· + β (rIdx2 r d)) ho2).trans (not_flag_of_one (rIdx2 r) β d))),
          dStar, hb1, hb2, fun d _ ↦ (congrArg η (congrFun rUM d)).trans ((ηUM d).trans (hU d))⟩⟩

open scoped ComplexOrder MatrixOrder
open PhotochemistrySolution.XMeasUnld PhotochemistrySolution.SplitRouterFredkinMux
  PhotochemistrySolution.SplitRouterMuxD1
open PrimitiveGate hiding s
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynQromUncompA (wrapDyn)
attribute [local semireducible] DynQromUncompA.remeasureIf DynQromUncompA.wrapDyn
    DynQromUncompA.fwdCirc
theorem pub_pHdrD1ZG {M D n : ℕ} (hD2 : 2 ≤ D) (r : RouterReg M D n) {β γ : BitAssignment n}
    (hAg : AgreesBeforeHdr r β γ) : ∀ w, PubCtrlSet r w → (pHdrD1ZG hD2 r).fwdBits γ w = β w := by
  obtain ⟨_, _, nfOth⟩ := fwdBits_pNotFlagsZG r γ
    (fun d ↦ (hAg.2.2.2.2.2.2 d).1) (fun d ↦ (hAg.2.2.2.2.2.2 d).2.1) D le_rfl
  rintro _ ⟨u, huPub, rfl⟩
  have nU (d : Fin D) : r u ≠ rUMsb r d := rr_ne r (by
    unfold basePub
    dsimp
    omega)
  dsimp only [pHdrD1ZG]
  rw [fwdBits_seq, fwdBits_seq, fwdBits_pUMsbDownLoop_other true r (D - 2) (hdr_lt2 hD2) _
    (fun d hlt ↦ by
      have neHi {k : Fin D} (hk : D - 2 ≤ k.val := by dsimp <;> omega) : rUMsb r d ≠ rUMsb r k :=
        rUMsb_ne_of_ne r fun e ↦ absurd (congrArg Fin.val e) (by omega)
      dsimp only [ComputeProg.fwdBits]
      repeat rw [Function.update_of_ne neHi]
      exact (nfOth _ (fun _ ↦ rr_ne r (d.isLt |> fun _ ↦ by
        dsimp
        omega))
        (fun _ ↦ rr_ne r (d.isLt |> fun _ ↦ by
          dsimp
          omega))).trans (hAg.2.2.2.2.2.2 d).2.2.1)
    (r u) nU]
  dsimp only [ComputeProg.fwdBits]
  repeat rw [Function.update_of_ne (nU _)]
  rw [nfOth _ (fun _ ↦ rr_ne r (by
    unfold basePub
    dsimp
    omega))
    (fun _ ↦ rr_ne r (by
      unfold basePub
      dsimp
      omega))]
  by_cases h0 : u.val = 0
  · exact (Fin.ext h0 : u = ⟨0, by
    unfold routerWidth
    omega⟩) ▸ hAg.1
  · by_cases h1 : u.val = 1
    · exact (Fin.ext h1 : u = ⟨1, by
      unfold routerWidth
      omega⟩) ▸ hAg.2.1
    · by_cases hI1 : u.val < 2 + D
      · exact (show r u = rIdx1 r ⟨u.val - 2, by omega⟩ from
          congrArg r.wires (Fin.ext (by
            dsimp
            omega))) ▸ hAg.2.2.1 _
      · exact (show r u = rIdx2 r ⟨u.val - (2 + D), by omega⟩ from
          congrArg r.wires (Fin.ext (by
            dsimp
            omega))) ▸ hAg.2.2.2.1 _

theorem valid_plane_zgModeMuxD1 {M D n : ℕ} (hMD : M < 2 ^ D) (hD2 : 2 ≤ D) (r : RouterReg M D n)
    {β γ η : BitAssignment n} (hβ : ValidZeroGatedSortedRouterInput r β)
    (hAg : AgreesBeforeHdr r β γ) (_hHdrCln : ∀ u : Fin (routerWidth M D), basePub M D + 4 ≤ u.val →
    u.val < basePub M D + 4 → γ (r u) = 0) (hLo : ∀ p : Fin M, η (rCtrlLo r p) = routerCtrlLo r β p)
    (hHi : ∀ p : Fin M, η (rCtrlHi r p) = routerCtrlHi r β p)
    (hOth : ∀ w : Wire n, (∀ p, w ≠ rCtrlLo r p) → (∀ p, w ≠ rCtrlHi r p) → η w =
    (pHdrD1ZG hD2 r).fwdBits γ w)
    (b : Fin 24) : ValidPlaneCtrlMuxD1 (planeOfRouter (rHas2Alias r) b) η ∧
    ValidPlaneCleanMuxD1 (planeOfRouter (rHas2Alias r) b) η
    := by obtain ⟨hC, hZ⟩ :=
            validPlaneD1_of_pHdrD1ZG hMD hD2 r hβ hAg hLo hHi hOth b; exact ⟨hC,
            validPlaneCleanMuxD1_of_clean _ hZ⟩
end QuantumComputation.Specs.PhotochemistrySolution.Stage2ZeroGated
end
end

noncomputable section
namespace QuantumComputation.Specs.PhotochemistrySolution.PopBernstein
open Operator QProg Matrix Circuit Qubit PhotochemistrySolution
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
def rTop22Hi {K n : ℕ} (hK : 90 ≤ K) (r : QRegister (54 + K) n) : QRegister 22 n :=
  ⟨⟨fun j ↦ r ⟨54 + (K - 22 + j.val), by omega⟩, fun _ _ e ↦ Fin.ext (by
    have hv := congrArg Fin.val (r.wires.injective e); dsimp at hv; omega)⟩⟩
end QuantumComputation.Specs.PhotochemistrySolution.PopBernstein
end

noncomputable section
open scoped ComplexOrder MatrixOrder
open Operator QProg Matrix Circuit Qubit PrimitiveGate HermitianMat
  QuantumComputation.Specs.PhotochemistrySolution
  QuantumComputation.Specs.PhotochemistrySolution.XMeasUnld
  QuantumComputation.Specs.PhotochemistrySolution.SplitRouter47_187
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
open _root_.DynamicCircuit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt hiding bit_cases
  eval_seq_mulVec ket ket_CNOT ket_TOFF ket_X ket_projector_one ket_projector_zero matrix_ext_ket
  qAssign_obs_map_val
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB hiding bitSign eval_seq_mulVec ket
  ket_CNOT ket_TOFF ket_X matrix_ext_ket writeReg writeReg_apply_of_not_mem
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SplitRouterSeqBell26k hiding ket
  matrix_ext_ket
namespace QuantumComputation.Specs.PhotochemistrySolution.Stage2QromMux
attribute [local semireducible]
  ComputeProg.ValidProg ComputeProg.finalClean ComputeProg.fwdBits
theorem ite_congr_prop {α : Type*} {P Q : Prop} [Decidable P] [Decidable Q] (h : P ↔ Q)
    (a b : α) : (if P then a else b) = if Q then a else b :=
  if_congr h rfl rfl
theorem xorWireUnitary_ket_local {n : ℕ} (q : Wire n) (f : BitAssignment n → ZMod 2)
    (hf : ∀ β a, f (Function.update β q a) = f β) (β : BitAssignment n) :
    (xorWireUnitary q f hf).1.mulVec (ket β) = ket (Function.update β q (β q + f β)) :=
    xorWireUnitary_mulVec_ket q f hf β

theorem rCtrlLo_inj {M D n : ℕ} (r : RouterReg M D n) {p₁ p₂ : Fin M}
    (h : rCtrlLo r p₁ = rCtrlLo r p₂) : p₁ = p₂ :=
  Fin.ext (by have hv := congrArg Fin.val (r.wires.injective h); dsimp at hv; omega)
def ctrlLoPrefixBits {M D n : ℕ} (r : RouterReg M D n) (delta : Fin M → ZMod 2) (P : Fin M → Prop)
    [DecidablePred P] (γ : BitAssignment n) (w : Wire n) : ZMod 2 :=
    if h : ∃ p : Fin M, P p ∧ w = rCtrlLo r p then γ w + delta (Classical.choose h) else γ w
theorem ctrlLoPrefixBits_of_not_ctrlLo {M D n : ℕ} (r : RouterReg M D n) (delta : Fin M → ZMod 2)
    (P : Fin M → Prop) [DecidablePred P] (γ : BitAssignment n) {u : Wire n}
    (hu : ∀ p : Fin M, u ≠ rCtrlLo r p) : ctrlLoPrefixBits r delta P γ u = γ u :=
  dite_eq_right fun ⟨p, _, e⟩ ↦ hu p e
theorem ctrlLoPrefixBits_ctrlLo {M D n : ℕ} (r : RouterReg M D n) (delta : Fin M → ZMod 2)
    (P : Fin M → Prop) [DecidablePred P] (γ : BitAssignment n)
    (p₀ : Fin M) : ctrlLoPrefixBits r delta P γ (rCtrlLo r p₀) = if P p₀ then γ (rCtrlLo r p₀) +
    delta p₀ else γ (rCtrlLo r p₀) := by
  unfold ctrlLoPrefixBits
  exact if hp : P p₀ then
    let he : ∃ p, P p ∧ rCtrlLo r p₀ = rCtrlLo r p := ⟨p₀, hp, rfl⟩
    (dite_eq_left he).trans
      ((congrArg (γ _ + delta ·) (rCtrlLo_inj r he.choose_spec.2.symm)).trans (ite_eq_left hp).symm)
  else (dite_eq_right fun ⟨_, hp', e⟩ ↦ hp (rCtrlLo_inj r e ▸ hp')).trans (ite_eq_right hp).symm

end QuantumComputation.Specs.PhotochemistrySolution.Stage2QromMux
end

section
open QuantumComputation.Specs.PhotochemistrySolution.CoinWrap
  QuantumComputation.Specs.PhotochemistrySolution.Cartesian254

noncomputable section
namespace QuantumComputation.Specs.PhotochemistrySolution.PopBernstein
open Operator QProg Matrix Circuit Qubit PhotochemistrySolution
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
attribute [local semireducible] PhotochemistrySolution.SubregMBUCore.wrapDynOnReg
def rY36Of {K n : ℕ} (r : QRegister (54 + K) n) : QRegister 36 n :=
  ⟨⟨fun b ↦ r ⟨18 + b.val, PotOracleGen.potGen_y36_lt K b⟩, fun _ _ e ↦ Fin.ext (by
    have hv := congrArg Fin.val (r.wires.injective e)
    dsimp at hv
    omega)⟩⟩
def rPoolOf {M K n : ℕ} (hMK : M ≤ K) (r : QRegister (54 + K) n) : QRegister M n :=
  ⟨⟨fun u ↦ r ⟨54 + u.val, by omega⟩, fun _ _ e ↦ Fin.ext (by
    have hv := congrArg Fin.val (r.wires.injective e)
    dsimp at hv
    omega)⟩⟩
theorem d2_lt_262144 {x : ℕ} (hx : x ≤ 195075) : x < 262144 := by omega
end QuantumComputation.Specs.PhotochemistrySolution.PopBernstein

namespace QuantumComputation.Specs.PhotochemistrySolution.XagParityEngine
set_option maxRecDepth 4096
open PrimitiveGate PhotochemistrySolution.FermatInverse
theorem xagEnv_prefix_eq (c : ℕ) {N₁ N₂ : ℕ} {g₁ g₂ : ℕ → ℕ × ℕ} :
    ∀ k (hk₁ : k ≤ N₁) (hk₂ : k ≤ N₂), (∀ j < k, g₁ j = g₂ j) →
      xagEnv c N₁ (fun i ↦ g₁ i.val) k hk₁ = xagEnv c N₂ (fun i ↦ g₂ i.val) k hk₂
  | 0, _, _, _ => rfl
  | k + 1, hk₁, hk₂, hEq => by simp only [xagEnv, xagEnv_prefix_eq c k (Nat.le_of_succ_le hk₁)
      (Nat.le_of_succ_le hk₂) fun j hj ↦ hEq j (Nat.lt_succ_of_lt hj), hEq k (Nat.lt_succ_self k)]
theorem wBit_trim_prefix {c N K : ℕ} (hK : K ≤ N) (hN : N ≤ 334) (g : ℕ → ℕ × ℕ) {msk : ℕ}
    (hM : msk < 2 ^ (42 + K)) :
    wBit (xagEnv c N (fun i ↦ g i.val) N le_rfl) msk =
      oddBits (xagEnv c N (fun i ↦ g i.val) K hK &&& msk) (42 + K) := by
  conv_lhs => rw [wBit, show (376 : ℕ) = (42 + K) + (334 - K) by omega,
    oddBits_trim_above (m := 42 + K) fun i hi ↦ by rw [Nat.testBit_and,
      Nat.testBit_lt_two_pow (hM.trans_le (Nat.pow_le_pow_right (by omega) hi)), Bool.and_false]]
  refine oddBits_congr_lt (42 + K) fun i hi ↦ ?_
  have hm := xagEnv_mono_below (c := c) (N := N) (gates := fun j ↦ g j.val)
    (k := K) (b := i) hi (N - K) (by omega)
  rw [xagEnv_congr_step (show K + (N - K) = N by omega) _ le_rfl] at hm
  rw [Nat.testBit_and, Nat.testBit_and, hm]
theorem wBit_eq_of_prefix {c N₁ N₂ K : ℕ} (hK₁ : K ≤ N₁) (hN₁ : N₁ ≤ 334) (hK₂ : K ≤ N₂)
    (hN₂ : N₂ ≤ 334) {g₁ g₂ : ℕ → ℕ × ℕ}
    (hPref : allTree 10 0 K (fun j ↦ beqPair (g₁ j) (g₂ j)) = true) {msk : ℕ}
    (hMsk : Nat.blt msk (1 <<< (42 + K)) = true) :
    wBit (xagEnv c N₁ (fun i ↦ g₁ i.val) N₁ le_rfl) msk =
      wBit (xagEnv c N₂ (fun i ↦ g₂ i.val) N₂ le_rfl) msk := by
  have hM : msk < 2 ^ (42 + K) := by rwa [Nat.shiftLeft_eq, one_mul, Nat.blt_eq] at hMsk
  rw [wBit_trim_prefix hK₁ hN₁ g₁ hM, wBit_trim_prefix hK₂ hN₂ g₂ hM,
      xagEnv_prefix_eq c K hK₁ hK₂ fun j hj ↦ beqPair_imp (allTree_zero hPref hj)]
theorem wPack_eq_of_prefix (c : ℕ) {N₁ N₂ K : ℕ} (hK₁ : K ≤ N₁) (hN₁ : N₁ ≤ 334)
    (hK₂ : K ≤ N₂) (hN₂ : N₂ ≤ 334) {g₁ g₂ : ℕ → ℕ × ℕ}
    (hPref : allTree 10 0 K (fun j ↦ beqPair (g₁ j) (g₂ j)) = true) :
    ∀ {ms : List ℕ}, (ms.all fun m ↦ Nat.blt m (1 <<< (42 + K))) = true →
      wPack (xagEnv c N₁ (fun i ↦ g₁ i.val) N₁ le_rfl) ms =
        wPack (xagEnv c N₂ (fun i ↦ g₂ i.val) N₂ le_rfl) ms
  | [], _ => rfl
  | _ :: _, hAll => by
      rcases Bool.and_eq_true_iff.mp hAll with ⟨hMa, hMs⟩
      simp only [wPack, wBit_eq_of_prefix hK₁ hN₁ hK₂ hN₂ hPref hMa,
        wPack_eq_of_prefix c hK₁ hN₁ hK₂ hN₂ hPref hMs]
end QuantumComputation.Specs.PhotochemistrySolution.XagParityEngine
end

noncomputable section
set_option maxRecDepth 16384
namespace QuantumComputation.Specs.PhotochemistrySolution.Tier1K3708
open PhotochemistrySolution.ZeroNEremSpec PhotochemistrySolution.Stage1AsymRevEngine
open _root_.QuantumComputation.Specs.PhotochemistrySolution.FermatInverse (allTree allTree_zero
    coinW outW phiU1 decodeUltraNuc192 wBit wPack testBit_wPack bitAt bitAt_eq_testBit packBools
    oddBits_and_xor nat_add_eq nat_xor_eq nat_shr_eq b2BEq b2_bEq_iff)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.FermatInverse (b2_testBit_mod_pow
    b2PackSlice b2_packBools_append b2_packBools_slice)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.XagParityEngine (wBit_coin_gen
    wBit_eq_of_prefix wPack_eq_of_prefix)
/-- Forward `232`-AND XAG environment on `c : Fin (2 ^ 41)`. -/
def envTier1K3708 (c : Fin (2 ^ 41)) : ℕ :=
  xagEnv c.val nGatesTier1K3708 gatesTier1K3708 nGatesTier1K3708 le_rfl
/-- Monomorphic `List ℕ` equality check. -/
def listBeqNatT1 : List ℕ → List ℕ → Bool
  | [], [] => true
  | x :: xs, y :: ys => Bool.and (Nat.beq x y) (listBeqNatT1 xs ys)
  | _, _ => false
theorem listBeqNatT1_imp : ∀ {xs ys : List ℕ}, listBeqNatT1 xs ys = true → xs = ys
  | [], [], _ => rfl
  | _ :: _, [], h | [], _ :: _, h => Bool.noConfusion h
  | _ :: _, _ :: _, h =>
        congrArg₂ List.cons (Nat.beq_eq.mp (Bool.and_eq_true_iff.mp h).1)
        (listBeqNatT1_imp (Bool.and_eq_true_iff.mp h).2)
/-- Computable species code `0=H, 1=C, 2=N, 3=O` on `na < 47`. -/
def nucSpNatT1 (na : ℕ) : ℕ :=
    cond (Nat.blt na 23) 1 (cond (Nat.blt na 43) 0 (cond (Nat.blt na 46) 2 3))
theorem nucSpNatT1_eq_nucSpecies : ∀ n : Fin 47, nucSpNatT1 n.val =
    (PhotochemistrySolution.ZeroNEremSpec.nucSpecies n).val := by decide
/-- Unconditional row care predicate. -/
def careAllTier1 (_ : ℕ) : Bool := true
/-- Symbolic input wire masks for block `00` (`B0_x_hi8`). -/
def tier1In00 : List ℕ :=
  [coinW 33, coinW 34, coinW 35, coinW 36, coinW 37, coinW 38, coinW 39, coinW 40]
/-- Global output parity masks for block `00` (`B0_x_hi8`). -/
def tier1Out00 : List ℕ := [0x1800000000000]
/-- Exact semantic spec of `F00` (`B0_x_hi8`). -/
def specTier1_00 (r : ℕ) : ℕ := cond (Nat.beq r 255) 1 0
/-- Symbolic input wire masks for block `01` (`B1_x_sq_inv`). -/
def tier1In01 : List ℕ :=
  [coinW 25, coinW 26, coinW 27, coinW 28, coinW 29, coinW 30, coinW 31, coinW 32,
   outW tier1Out00 0]
/-- Global output parity masks for block `01` (`B1_x_sq_inv`). -/
def tier1Out01 : List ℕ := [
  0x1cd800124000001, 0x1d800000000000, 0x3d800000000000, 0x5800000000000,
  0x1b1800170000000, 0x1058000a0000000, 0x9800000000000, 0x1f800000000000
]
/-- Exact semantic spec of `F01` (`B1_x_sq_inv`). -/
def specTier1_01 (r : ℕ) : ℕ := cond (Nat.beq (r / 256) 0) 0 (r % 256)
/-- Folded `8`-bit `a8` wire mask `coinW (33 + i) ^^^ outW tier1Out01 i`. -/
def a8T1W (i : ℕ) : ℕ := Nat.xor (coinW (33 + i)) (outW tier1Out01 i)
/-- Folded `8`-bit `b8` wire mask `coinW (25 + i) ^^^ outW tier1Out01 i`. -/
def b8T1W (i : ℕ) : ℕ := Nat.xor (coinW (25 + i)) (outW tier1Out01 i)
/-- Symbolic input wire masks for block `02` (`B2_x_255`). -/
def tier1In02 : List ℕ :=
  [a8T1W 0, a8T1W 1, a8T1W 2, a8T1W 3, a8T1W 4, a8T1W 5, a8T1W 6, a8T1W 7]
/-- Global output parity masks for block `02` (`B2_x_255`). -/
def tier1Out02 : List ℕ := [
  0x19cd800524000001, 0x281d800800000000, 0x483d801000000000, 0x8805802000000000,
  0x800000000000000, 0x7801f820000000001, 0xa801f820000000000, 0x221058080a0000000,
  0xa91ae024170000000, 0x170bd81c1d0000000, Nat.shiftLeft 1 66
]
/-- Exact semantic spec of `F02` (`B2_x_255`). -/
def specTier1_02 (r : ℕ) : ℕ :=
  let p := b2Spec r
  p.1 + 32 * p.2.1 + 128 * p.2.2.1 + cond p.2.2.2 1024 0
/-- Exact semantic spec of `F03` (`B6_y_1023_coset` directly on `hi10`). -/
def specTier1_03 (r : ℕ) : ℕ :=
  let p := b6Spec r
  p.1 + 16 * p.2.1 + 64 * p.2.2.1 + cond p.2.2.2 2048 0
/-- Kernel-primitive `r11 + 16 * h2` evaluator on `rv <= 32` (`0` tuple zeta blowup). -/
def b6RemFastT1 (rv : ℕ) : ℕ :=
  match Nat.beq rv 32 with
  | true => 41
  | false =>
      let r4 := Nat.shiftRight rv 4; let r30 := Nat.land rv 15
      match Nat.blt r30 11 with
      | true => Nat.add r30 (Nat.shiftLeft r4 4)
      | false =>
          match Nat.beq r30 11 with
          | true => Nat.add (Nat.sub 10 (Nat.shiftLeft r4 1)) 32
          | false => Nat.add (Nat.xor (Nat.sub r30 8) (Nat.shiftLeft r4 2)) 32
/-- Kernel-primitive `F03` spec (`0` typeclass synthesis, `0` tuple zeta blowup). -/
def fastSpecTier1_03 (r : ℕ) : ℕ :=
  let lo5 := Nat.land r 31; let hi5 := Nat.land (Nat.shiftRight r 5) 31
  match Nat.beq hi5 31 with
  | true => Nat.add 41 (Nat.add (Nat.shiftLeft lo5 6) (cond (Nat.beq lo5 31) 2048 0))
  | false => Nat.add (b6RemFastT1 lo5) (Nat.shiftLeft hi5 6)
theorem fastSpecTier1_03_eq (r : ℕ) : fastSpecTier1_03 r = specTier1_03 r := by
  dsimp only [fastSpecTier1_03, specTier1_03, b6Spec]
  rw [show Nat.land r 31 = r % 32 from Nat.and_two_pow_sub_one_eq_mod r 5,
    show Nat.land (Nat.shiftRight r 5) 31 = (r / 32) % 32 by
      rw [nat_shr_eq, Nat.shiftRight_eq_div_pow]
      exact Nat.and_two_pow_sub_one_eq_mod (r / 32) 5]
  simp only [show ∀ x, (x == 31) = Nat.beq x 31 from fun _ ↦
      Bool.eq_iff_iff.mpr (by simp [Nat.beq_eq]),
    nat_add_eq, show ∀ x, Nat.shiftLeft x 6 = 64 * x from fun x ↦
        (Nat.shiftLeft_eq x 6).trans (Nat.mul_comm x 64)]
  cases h31 : Nat.beq ((r / 32) % 32) 31 <;> dsimp only [cond]
  · simpa [h31] using congrArg (· + 64 * (r / 32 % 32))
        (Nat.beq_eq.mp (allTree_zero (by decide +kernel :
      allTree 7 0 33 (fun rv ↦ Nat.beq (b6RemFastT1 rv) ((b6Rem33 rv).1 + 16 * (b6Rem33 rv).2)) =
        true) (Nat.lt_succ_of_lt (Nat.mod_lt r (by omega)))))
  · rw [show (b6Rem33 32).1 + 16 * (b6Rem33 32).2 = 41 from rfl]
    ring
/-- Row care `r11 < 11 ∧ r17 < 17` for `F04` (`B9_phi_u1`). -/
def careTier1_04 (r : ℕ) : Bool :=
  Bool.and (Nat.blt (r % 16) 11) (Nat.blt (r / 16) 17)
/-- Exact semantic spec of `F04` (`B9_phi_u1`). -/
def specTier1_04 (r : ℕ) : ℕ := phiU1 (r % 16) (r / 16)
/-- Row care `h1 < 3` for `F05` (`B10_z1_nuc14_care`). -/
def careTier1_05 (r : ℕ) : Bool := Nat.blt (r % 4) 3
/-- Exact semantic spec of `F05` (`B10_z1_nuc14_care`). -/
def specTier1_05 (r : ℕ) : ℕ :=
  let d := decodeUltraNuc192 (64 * (r % 4) + (r / 4) % 64)
  cond d.1 (1 + 2 * nucSpNatT1 d.2.val + 8 * d.2.val) 0
/-- Row care `h2 < 3` for `F06` (`B11_z2_nuc13`). -/
def careTier1_06 (r : ℕ) : Bool := Nat.blt (r % 4) 3
/-- Output bitmask (`511 + 512 * 255` when `z2` valid, `1 + 512 * 255` when invalid) for `F06`. -/
def maskTier1_06 (r : ℕ) : ℕ :=
  let d := decodeUltraNuc192 (64 * (r % 4) + (r / 4) % 64)
  (cond d.1 511 1) + 512 * 255
/-- Exact semantic spec of `F06` (`B11_z2_nuc13`). -/
def specTier1_06 (r : ℕ) : ℕ :=
  let d := decodeUltraNuc192 (64 * (r % 4) + (r / 4) % 64)
  (cond d.1 (1 + 2 * nucSpNatT1 d.2.val + 8 * d.2.val) 0) + 512 * b11Z2OfHX (r % 4) ((r / 4) % 64)
/-- Output bitmask (`2` when `a = b`, `3` when `a =/= b`) for `F07` (`B12a_na_lo_opt`). -/
def maskTier1_07 (r : ℕ) : ℕ := cond (Nat.beq (r % 8) ((r / 8) % 8)) 2 3
/-- Exact semantic spec of `F07` (`B12a_na_lo_opt`). -/
def specTier1_07 (r : ℕ) : ℕ :=
    cond (Nat.beq (r % 8) ((r / 8) % 8)) 2 (cond (Nat.blt (r % 8) ((r / 8) % 8)) 1 0)
/-- Exact semantic spec of `F08` (`B12b_na_hi_opt`). -/
def specTier1_08 (r : ℕ) : ℕ :=
  let a := r % 8; let b := (r / 8) % 8;
  let ltOut := Bool.or (Nat.blt a b) (Bool.and (Nat.beq a b) (bitAt r 6));
  let eqOut := Bool.and (Nat.beq a b) (bitAt r 7)
  cond ltOut 1 0 + cond eqOut 2 0
/-- Output bitmask (`2` when `a = b`, `3` when `a =/= b`) for `F09` (`B13a_ez_lo_opt`). -/
def maskTier1_09 (r : ℕ) : ℕ := cond (Nat.beq (r % 16) ((r / 16) % 16)) 2 3
/-- Exact semantic spec of `F09` (`B13a_ez_lo_opt`). -/
def specTier1_09 (r : ℕ) : ℕ :=
    cond (Nat.beq (r % 16) ((r / 16) % 16)) 2 (cond (Nat.blt (r % 16) ((r / 16) % 16)) 1 0)
/-- Row care `a < 12 ∧ b < 12` (`u1, z2 < 192`) for `F10` (`B13b_ez_hi_opt`). -/
def careTier1_10 (r : ℕ) : Bool :=
  Bool.and (Nat.blt (r % 16) 12) (Nat.blt ((r / 16) % 16) 12)
/-- Exact semantic spec of `F10` (`B13b_ez_hi_opt`). -/
def specTier1_10 (r : ℕ) : ℕ :=
  let a := r % 16; let b := (r / 16) % 16;
  let ltOut := Bool.or (Nat.blt a b) (Bool.and (Nat.beq a b) (bitAt r 8));
  let eqOut := Bool.and (Nat.beq a b) (bitAt r 9)
  cond ltOut 1 0 + cond eqOut 2 0

/-- Single ripple-borrow bitplane step for unsigned comparator blocks `F16..F19`. -/
def cmpStepPlaneT1 (ones c a b : ℕ) : ℕ :=
  orPlaneT1 (andPlaneT1 (notPlaneT1 ones a) b)
    (andPlaneT1 (notPlaneT1 ones (Nat.xor a b)) c)
/-- Ripple `n` comparator bitplanes starting at bit `i` (`a` at `i..`, `b` at `k + i..`). -/
def cmpLoopPlaneT1 (ones k : ℕ) (vt : ℕ → ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, _, c => c
  | n + 1, i, c =>
      cmpLoopPlaneT1 ones k vt n (Nat.succ i) (cmpStepPlaneT1 ones c (vt i) (vt (k + i)))
/-- Word-parallel bitplane pair `(ones, [out])` for `k`-bit comparator (`F16..F19`). -/
def planesCmpKT1 (k ones : ℕ) (vt : ℕ → ℕ) : ℕ × List ℕ :=
  (ones, [cmpLoopPlaneT1 ones k vt k 0 (vt (2 * k))])
/-- Boolean step matching `cmpStepPlaneT1`. -/
def cmpStepBoolT1 (c a b : Bool) : Bool :=
    Bool.or (Bool.and (Bool.not a) b) (Bool.and (Bool.not (xor a b)) c)
theorem cmpStepBoolT1_eq (a b : ℕ) (c : Bool) :
    Bool.or (Nat.blt (a / 2) (b / 2))
      (Bool.and (Nat.beq (a / 2) (b / 2)) (cmpStepBoolT1 c (bitAt a 0) (bitAt b 0))) =
      Bool.or (Nat.blt a b) (Bool.and (Nat.beq a b) c) := by
  rw [cmpStepBoolT1, bitAt_eq_testBit, bitAt_eq_testBit, Nat.testBit_zero, Nat.testBit_zero]
  refine Bool.eq_iff_iff.mpr ?_
  cases ha : decide (a % 2 = 1) <;> cases hb : decide (b % 2 = 1) <;> cases c <;>
    simp [Nat.blt_eq, Nat.beq_eq] at ha hb ⊢ <;> omega
theorem bitAt_cmpLoopPlaneT1 {ones k r : ℕ} {vt : ℕ → ℕ}
    (h1 : bitAt ones r = true) :
    ∀ n i c a b, a < 2 ^ n → b < 2 ^ n → (∀ j < n, bitAt (vt (i + j)) r = bitAt a j) →
      (∀ j < n, bitAt (vt (k + i + j)) r = bitAt b j) →
      bitAt (cmpLoopPlaneT1 ones k vt n i c) r =
        Bool.or (Nat.blt a b) (Bool.and (Nat.beq a b) (bitAt c r))
  | 0, _, c, a, b, ha, hb, _, _ => by
      simp only [show a = 0 by omega, show b = 0 by omega, cmpLoopPlaneT1]
      cases bitAt c r <;> rfl
  | n + 1, i, c, a, b, ha, hb, hA, hB => by
      have hPow : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [Nat.pow_succ, Nat.mul_comm]
      have hSh {o x} (hX : ∀ j < n + 1, bitAt (vt (o + j)) r = bitAt x j) (j) (hj : j < n) :
          bitAt (vt (o + 1 + j)) r = bitAt (x / 2) j := by
        rw [show o + 1 + j = o + (j + 1) by omega, hX (j + 1) (by omega),
            bitAt_eq_testBit, bitAt_eq_testBit, ← Nat.pow_one 2, Nat.testBit_div_two_pow]
      dsimp only [cmpLoopPlaneT1, cmpStepPlaneT1]
      rw [bitAt_cmpLoopPlaneT1 h1 n (i + 1) _ (a / 2) (b / 2) (by omega) (by omega) (hSh hA)
          (hSh hB), bitAt_orPlaneT1, bitAt_andPlaneT1, bitAt_andPlaneT1, bitAt_notPlaneT1 h1,
        bitAt_notPlaneT1 h1, bitAt_eq_testBit (Nat.xor _ _), nat_xor_eq, Nat.testBit_xor,
        ← bitAt_eq_testBit, ← bitAt_eq_testBit, show vt i = vt (i + 0) from rfl, hA 0 (by omega),
        show vt (k + i) = vt (k + i + 0) from rfl, hB 0 (by omega), ← cmpStepBoolT1,
        cmpStepBoolT1_eq]
theorem planesCmpKT1_spec {k r ones : ℕ} {vt : ℕ → ℕ}
    (_hr : r < 2 ^ (2 * k + 1)) (h1 : bitAt ones r = true)
    (hVt : ∀ i < 2 * k + 1, bitAt (vt i) r = bitAt r i)
    (_hCare : careAllTier1 r = true) :
    bitAt (planesCmpKT1 k ones vt).1 r = true ∧
      packRowAtT1 r (planesCmpKT1 k ones vt).2 =
        let a := r % 2 ^ k
      let b := (r / 2 ^ k) % 2 ^ k
      cond (Bool.or (Nat.blt a b) (Bool.and (Nat.beq a b) (bitAt r (2 * k)))) 1 0 := by
  refine ⟨h1, by
    rw [planesCmpKT1, packRowAtT1_cons, show packRowAtT1 r [] = 0 from rfl, Nat.mul_zero,
      Nat.add_zero, bitAt_cmpLoopPlaneT1 h1 k 0 (vt (2 * k)) (r % 2 ^ k) ((r / 2 ^ k) % 2 ^ k)
        (Nat.mod_lt _ (Nat.two_pow_pos k)) (Nat.mod_lt _ (Nat.two_pow_pos k))
        (fun j hj ↦ (hVt (0 + j) (by omega)).trans (by simpa using bitAt_div_modT1 r 0 k j hj))
        (fun j hj ↦ by rw [Nat.add_zero, hVt (k + j) (by omega), bitAt_div_modT1 r k k j hj]),
      hVt (2 * k) (by omega)]⟩
/--
`23` -bit comparator LHS mask list `v23T1W` (`b8[0..5] ++ lo10[0..5] ++ c5 ++ lo10[6..9] ++
b8[6..7]`).
-/
def v23T1W : List ℕ :=
  [b8T1W 0, b8T1W 1, b8T1W 2, b8T1W 3, b8T1W 4, b8T1W 5,
   coinW 5, coinW 6, coinW 7, coinW 8, coinW 9, coinW 10,
   coinW 0, coinW 1, coinW 2, coinW 3, coinW 4,
   coinW 11, coinW 12, coinW 13, coinW 14,
   b8T1W 6, b8T1W 7]
/-- Conditionally XOR `sig` into `acc` when bit `i` of `val` is `1`. -/
def xorMaskedConstT1 (sig val i acc : ℕ) : ℕ := cond (bitAt val i) (Nat.xor acc sig) acc
def specTier1_17 (r : ℕ) : ℕ :=
  let a := r % 32; let b := (r / 32) % 32
  cond (Bool.or (Nat.blt a b) (Bool.and (Nat.beq a b) (bitAt r 10))) 1 0

def careTier1_20 (r : ℕ) : Bool :=
  let s :=
      cond (bitAt r 0) 1 0 + cond (bitAt r 1) 1 0 + cond (bitAt r 2) 1 0 + cond (bitAt r 3) 1 0 +
      cond (bitAt r 4) 1 0 + cond (bitAt r 5) 1 0
  Nat.ble s 1
/-- Exact semantic spec of `F20` (`B17ab_do_pot`). -/
def specTier1_20 (r : ℕ) : ℕ :=
  let lt23 := bitAt r 6; let z1Ok := bitAt r 7; let z2Ok := bitAt r 8;
  let doEe :=
      Bool.and (Bool.and (Bool.and z1Ok z2Ok) (Bool.not (bitAt r 9))) (Bool.or (bitAt r 0)
      (Bool.and (bitAt r 1) lt23)); let doNn :=
                                      Bool.and (Bool.and (Bool.and z1Ok z2Ok)
                                      (Bool.not (bitAt r 10))) (Bool.or (bitAt r 2)
                                      (Bool.and (bitAt r 3) lt23));
                                      let doEn :=
                                      Bool.and z1Ok (Bool.or (bitAt r 4)
                                      (Bool.and (bitAt r 5) lt23))
  cond doEe 1 0 + cond doNn 2 0 + cond doEn 4 0
theorem planesPot20T1_spec {r ones : ℕ} {vt : ℕ → ℕ} (_hr : r < 2 ^ 11) (h1 : bitAt ones r = true)
    (hVt : ∀ i < 11, bitAt (vt i) r = bitAt r i) (hCare : careTier1_20 r = true) :
    bitAt (planesPot20T1 ones vt).1 r = true ∧
      packRowAtT1 r (planesPot20T1 ones vt).2 = specTier1_20 r := by
  refine ⟨?_, ?_⟩ <;> simp only [planesPot20T1, specTier1_20, packRowAtT1,
    bitAt_notPlaneT1 h1, bitAt_orPlaneT1, bitAt_andPlaneT1, hVt 0 (by omega),
    hVt 1 (by omega), hVt 2 (by omega), hVt 3 (by omega), hVt 4 (by omega), hVt 5 (by omega),
    hVt 6 (by omega), hVt 7 (by omega), hVt 8 (by omega), hVt 9 (by omega), hVt 10 (by omega)]
  · dsimp only [careTier1_20] at hCare
    revert hCare
    cases bitAt r 0 <;> cases bitAt r 1 <;> cases bitAt r 2 <;>
      cases bitAt r 3 <;> cases bitAt r 4 <;> cases bitAt r 5 <;> decide
  · generalize Bool.and (Bool.and _ (Bool.not (bitAt r 9))) _ = b0
    generalize Bool.and (Bool.and _ (Bool.not (bitAt r 10))) _ = b1
    generalize Bool.and (bitAt r 7) (Bool.or (bitAt r 4) _) = b2
    cases b0 <;> cases b1 <;> cases b2 <;> rfl
def careTier1_22 (r : ℕ) : Bool := Bool.or (Bool.not (bitAt r 1)) (bitAt r 0)
/-- Exact semantic spec of `F22` (`B18a_e_lo`). -/
def specTier1_22 (r : ℕ) : ℕ :=
  let hasE1 := bitAt r 0; let doEe := bitAt r 1; let sw := Bool.and doEe (Bool.not (bitAt r 2));
  let u := (r / 8) % 16; let z := (r / 128) % 16; let e1 := cond sw z (cond hasE1 u 0);
  let e2 := cond doEe (cond sw u z) 0
  cond sw 1 0 + 2 * e1 + 32 * e2
def careTier1_23 (r : ℕ) : Bool :=
  Bool.and (Bool.or (Bool.not (bitAt r 1)) (bitAt r 0))
           (Bool.or (Bool.not (bitAt r 2)) (bitAt r 1))
/-- Exact semantic spec of `F23` (`B18b_e_hi`). -/
def specTier1_23 (r : ℕ) : ℕ :=
  let hasE1 := bitAt r 0; let doEe := bitAt r 1; let sw := bitAt r 2; let u := (r / 8) % 16;
  let z := (r / 128) % 16; let e1 := cond sw z (cond hasE1 u 0); let e2 := cond doEe (cond sw u z) 0
  e1 + 16 * e2
def careTier1_24 (r : ℕ) : Bool := Bool.or (Bool.not (bitAt r 1)) (bitAt r 0)
/-- Exact semantic spec of `F24` (`B19a_n_lo`). -/
def specTier1_24 (r : ℕ) : ℕ :=
  let isPot := bitAt r 0; let doNn := bitAt r 1; let sw := Bool.and doNn (Bool.not (bitAt r 2));
  let a := (r / 8) % 4; let b := (r / 32) % 4; let s1 := (r / 128) % 4; let s2 := (r / 512) % 4;
  let n1 := cond sw b (cond isPot a 0); let n2 := cond doNn (cond sw a b) 0;
  let sp1 := cond sw s2 (cond isPot s1 0); let sp2 := cond doNn (cond sw s1 s2) 0
  cond sw 1 0 + 2 * n1 + 8 * n2 + 32 * sp1 + 128 * sp2
def specTier1_26 (r : ℕ) : ℕ := cond (bitAt r 0) (r / 2) 0

theorem t1Ev_and4 {a b c d : Bool} (h : Bool.and a (Bool.and b (Bool.and c d)) = true) :
    a = true ∧ b = true ∧ c = true ∧ d = true := by simpa only [Bool.and_eq_true_iff] using h
theorem t1Ev_bitAt_div (r k : ℕ) : bitAt r k = (r / 2 ^ k).testBit 0 := by
  rw [Nat.testBit_div_two_pow, Nat.zero_add, bitAt_eq_testBit]
theorem t1Ev_bitAt_zero (b : Bool) (rest : ℕ) : bitAt (cond b 1 0 + 2 * rest) 0 = b := by
  rw [bitAt_eq_testBit, Nat.testBit_zero]
  cases b <;> simp [cond, Nat.add_mul_mod_self_left]
theorem t1Ev_wBit_xor (e a b : ℕ) : wBit e (Nat.xor a b) = xor (wBit e a) (wBit e b) :=
  nat_xor_eq a b ▸ oddBits_and_xor e a b 376
theorem t1Ev_wBit_coinW (c : Fin (2 ^ 41)) {i : ℕ} (hi : i < 41) : wBit (envTier1K3708 c)
    (coinW i) = c.val.testBit i :=
  wBit_coin_gen (N := nGatesTier1K3708) (Nat.ble_eq.mp rfl) c hi
theorem t1Ev_wBit_outW (e : ℕ) (ms : List ℕ) (q : ℕ) : wBit e (outW ms q) =
    (wPack e ms).testBit q := (testBit_wPack e ms q).symm
theorem t1Ev_wPack_eq_packBools (e : ℕ) : ∀ ms : List ℕ, wPack e ms = packBools (ms.map (wBit e))
  | [] => rfl
  | m :: ms => congrArg (cond (wBit e m) 1 0 + 2 * ·) (t1Ev_wPack_eq_packBools e ms)
theorem t1Ev_wPack_singleton (e m : ℕ) : wPack e [m] = cond (wBit e m) 1 0 := by
  cases h : wBit e m <;> simp [wPack, h]
theorem t1Ev_wPack_append (e : ℕ) (xs ys : List ℕ) : wPack e (xs ++ ys) = wPack e xs +
    2 ^ xs.length * wPack e ys := by
  rw [t1Ev_wPack_eq_packBools, List.map_append, b2_packBools_append, List.length_map,
      ← t1Ev_wPack_eq_packBools, ← t1Ev_wPack_eq_packBools]
theorem t1Ev_wBit_of_masked {e : ℕ} {ms : List ℕ} {msk sp q : ℕ}
    (hM : (wPack e ms) &&& msk = sp &&& msk) (hq : msk.testBit q = true) :
    wBit e (outW ms q) = sp.testBit q := by
  have h := congrArg (·.testBit q) hM
  rwa [Nat.testBit_and, Nat.testBit_and, hq, Bool.and_true, Bool.and_true, ← t1Ev_wBit_outW] at h
theorem t1Ev_subword_bit (x sh k i : ℕ) (hi : i < k) : ((x / 2 ^ sh) % 2 ^ k).testBit i =
    x.testBit (sh + i) := by
  rw [b2_testBit_mod_pow _ k i hi, Nat.testBit_div_two_pow, Nat.add_comm i sh]
theorem t1Ev_cmp2_hi {B a b : ℕ} (hB : 0 < B) {ltLo : Bool}
    (hLo : a % B ≠ b % B → ltLo = Nat.blt (a % B) (b % B)) :
    Bool.and (Nat.beq (a / B) (b / B)) (Nat.beq (a % B) (b % B)) = Nat.beq a b ∧
      (a ≠ b → Bool.or (Nat.blt (a / B) (b / B)) (Bool.and (Nat.beq (a / B) (b / B)) ltLo) =
        Nat.blt a b) := by
  have ha := (Nat.div_add_mod a B).symm
  have hb := (Nat.div_add_mod b B).symm
  have ⟨hmA, hmB⟩ := And.intro (Nat.mod_lt a hB) (Nat.mod_lt b hB)
  refine ⟨Bool.eq_iff_iff.mpr ⟨fun h ↦ ?_, fun e ↦ by simp [Nat.beq_eq.mp e]⟩,
    fun hNe ↦ Bool.eq_iff_iff.mpr ?_⟩
  · simp only [Bool.and_eq_true, Nat.beq_eq] at h ⊢
    rw [ha, hb, h.1, h.2]
  · by_cases hEq : a / B = b / B
    · simp only [hLo fun hm ↦ hNe (by rw [ha, hb, hEq, hm]), Bool.or_eq_true, Bool.and_eq_true,
        Nat.blt_eq, Nat.beq_eq, hEq, lt_self_iff_false, true_and, false_or]
      conv_rhs => rw [ha, hb, hEq]
      omega
    · simp only [Bool.or_eq_true, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq, hEq, false_and,
        or_false]
      rcases Nat.lt_or_gt_of_ne hEq with h | h
      · have _ := Nat.mul_succ B _ ▸ Nat.mul_le_mul_left B h
        omega
      · have _ := Nat.mul_succ B _ ▸ Nat.mul_le_mul_left B h
        omega
/-- Contiguous output slice `[outW ms sh, ..., outW ms (sh + k - 1)]`. -/
def t1EvOutSlice (ms : List ℕ) (sh : ℕ) : ℕ → List ℕ
  | 0 => []
  | k + 1 => outW ms sh :: t1EvOutSlice ms (sh + 1) k
theorem t1Ev_len_outSlice (ms : List ℕ) : ∀ sh k, (t1EvOutSlice ms sh k).length = k
  | _, 0 => rfl
  | sh, k + 1 => congrArg (· + 1) (t1Ev_len_outSlice ms (sh + 1) k)
theorem t1Ev_wPack_outSlice (e : ℕ) (ms : List ℕ) (sh k : ℕ) :
    wPack e (t1EvOutSlice ms sh k) = (wPack e ms / 2 ^ sh) % 2 ^ k := by
  have hM : ∀ m s, (t1EvOutSlice ms s m).map (wBit e) = b2PackSlice (wPack e ms) s m :=
    Nat.rec (fun _ ↦ rfl) fun m ih s ↦ by
      simp only [t1EvOutSlice, b2PackSlice, List.map_cons, t1Ev_wBit_outW, ih (s + 1)]
  rw [t1Ev_wPack_eq_packBools, hM k sh, b2_packBools_slice]
/-- Contiguous indexed wire slice `[f sh, ..., f (sh + k - 1)]`. -/
def t1EvWireSlice (f : ℕ → ℕ) (sh : ℕ) : ℕ → List ℕ
  | 0 => []
  | k + 1 => f sh :: t1EvWireSlice f (sh + 1) k
theorem t1Ev_len_wireSlice (f : ℕ → ℕ) : ∀ sh k, (t1EvWireSlice f sh k).length = k
  | _, 0 => rfl
  | sh, k + 1 => congrArg (· + 1) (t1Ev_len_wireSlice f (sh + 1) k)
theorem t1Ev_wPack_wireSlice (e : ℕ) (f : ℕ → ℕ) (v sh k : ℕ)
    (hB : ∀ i < k, wBit e (f (sh + i)) = v.testBit (sh + i)) :
    wPack e (t1EvWireSlice f sh k) = (v / 2 ^ sh) % 2 ^ k := by
  have hM : ∀ m s, (∀ i < m, wBit e (f (s + i)) = v.testBit (s + i)) →
      (t1EvWireSlice f s m).map (wBit e) = b2PackSlice v s m :=
    Nat.rec (fun _ _ ↦ rfl) fun m ih s h ↦ by
      simp only [t1EvWireSlice, b2PackSlice, List.map_cons, Nat.add_zero s ▸ h 0 (by omega),
        ih (s + 1) fun i hi ↦ (show s + 1 + i = s + (i + 1) by omega) ▸ h (i + 1) (by omega)]
  rw [t1Ev_wPack_eq_packBools, hM k sh hB, b2_packBools_slice]
/-- Coin bits `0..4` (`c5 < 32`). -/
def t1EvC5 (c : Fin (2 ^ 41)) : ℕ := c.val % 32
/-- Coin bits `5..24` (`y20 < 1048576`). -/
def t1EvY20 (c : Fin (2 ^ 41)) : ℕ := (c.val / 32) % 1048576
/-- Coin bits `5..14` (`lo10 < 1024`). -/
def t1EvLo10 (c : Fin (2 ^ 41)) : ℕ := t1EvY20 c % 1024
/-- Coin bits `15..24` (`hi10 < 1024`). -/
def t1EvHi10 (c : Fin (2 ^ 41)) : ℕ := t1EvY20 c / 1024
/-- Coin bits `25..40` (`x16 < 65536`). -/
def t1EvX16 (c : Fin (2 ^ 41)) : ℕ := c.val / 33554432
/-- Coin bits `25..32` (`lo8 < 256`). -/
def t1EvLo8 (c : Fin (2 ^ 41)) : ℕ := t1EvX16 c % 256
/-- Coin bits `33..40` (`hi8 < 256`). -/
def t1EvHi8 (c : Fin (2 ^ 41)) : ℕ := t1EvX16 c / 256
/-- Folded `8`-bit `a8 < 256`. -/
def t1EvA8 (c : Fin (2 ^ 41)) : ℕ :=
  cond (Nat.beq (t1EvHi8 c) 255) (255 - t1EvLo8 c) (t1EvHi8 c)
/-- Folded `8`-bit `b8 < 256`. -/
def t1EvB8 (c : Fin (2 ^ 41)) : ℕ :=
  cond (Nat.beq (t1EvHi8 c) 255) 0 (t1EvLo8 c)
/-- `b2Spec (t1EvA8 c)`. -/
def t1EvPx (c : Fin (2 ^ 41)) : ℕ × ℕ × ℕ × Bool := b2Spec (t1EvA8 c)
/-- `d1 = decodeUltraNuc192 (64 * h1 + b8 % 64)`. -/
def t1EvD1 (c : Fin (2 ^ 41)) : Bool × Fin 47 :=
  decodeUltraNuc192 (64 * (t1EvPx c).2.1 + t1EvB8 c % 64)
/-- `11`-bit `w11` subword `< 2048`. -/
def t1EvW11 (c : Fin (2 ^ 41)) : ℕ :=
  t1EvC5 c + 32 * (t1EvLo10 c / 64) + 512 * (t1EvB8 c / 64)
/-- `23`-bit comparator LHS `v23 < 8388608`. -/
def t1EvV23 (c : Fin (2 ^ 41)) : ℕ :=
  cart254V23 (t1EvB8 c % 64) (t1EvLo10 c % 64) (t1EvW11 c)
/-- `15`-bit `.kinNuc` subword `u15 < 32768`. -/
def t1EvU15 (c : Fin (2 ^ 41)) : ℕ := (t1EvLo10 c % 64) + 64 * t1EvC5 c + 2048 * (t1EvLo10 c / 64)
theorem t1Ev_coin_bounds (c : Fin (2 ^ 41)) :
    t1EvC5 c < 32 ∧ t1EvLo10 c < 1024 ∧ t1EvHi10 c < 1024 ∧ t1EvLo8 c < 256 ∧
      t1EvHi8 c < 256 ∧ t1EvA8 c < 256 ∧ t1EvB8 c < 256 ∧ t1EvW11 c < 2048 ∧
      t1EvV23 c < 8388608 ∧ t1EvU15 c < 32768 := by
  have hc := c.isLt
  obtain ⟨hA, hB⟩ : t1EvA8 c < 256 ∧ t1EvB8 c < 256 := by
    dsimp only [t1EvA8, t1EvB8, t1EvLo8, t1EvHi8, t1EvX16]
    cases Nat.beq ((c.val / 33554432) / 256) 255 <;> dsimp only [cond] <;> omega
  dsimp only [t1EvC5, t1EvY20, t1EvLo10, t1EvHi10, t1EvX16, t1EvLo8, t1EvHi8, t1EvW11,
    t1EvV23, cart254V23, t1EvU15]
  exact ⟨by omega, by omega, by omega, by omega, by omega, hA, hB, by omega, by omega, by omega⟩
theorem t1Ev_v23_kinNuc (c : Fin (2 ^ 41)) (h255 : Nat.beq (t1EvHi8 c) 255 = true) :
    t1EvV23 c = 64 * t1EvU15 c := by
  simp only [t1EvV23, cart254V23, t1EvW11, t1EvU15, t1EvB8, h255, Bool.cond_true]
  omega
theorem t1Ev_coin_hi10_bit (c : Fin (2 ^ 41)) {i : ℕ} (hi : i < 10) :
    wBit (envTier1K3708 c) (coinW (15 + i)) = (t1EvHi10 c).testBit i := by
  rw [t1Ev_wBit_coinW c (by omega), ← t1Ev_subword_bit c.val 15 10 i hi]
  dsimp only [t1EvHi10, t1EvY20]
  exact congrArg (Nat.testBit · i) (by omega)
theorem t1Ev_hi8_mod (c : Fin (2 ^ 41)) : (c.val / 2 ^ 33) % 2 ^ 8 = t1EvHi8 c :=
  (congrArg (· % 2 ^ 8) (Nat.div_div_eq_div_mul c.val (2 ^ 25) (2 ^ 8)).symm).trans
    (Nat.mod_eq_of_lt ((t1Ev_coin_bounds c).2.2.2.2.1 : _ < 2 ^ 8))
theorem t1Ev_chk (k0 m : ℕ) (ins : List ℕ) (lg : List (ℕ × ℕ)) (lo go : List ℕ) (sp : ℕ → ℕ)
    (h : checkBlockFullFastT1 nGatesTier1K3708 gatesTier1K3708At k0 m ins lg lo go
      careAllTier1 sp = true) (c : Fin (2 ^ 41)) :
    wPack (envTier1K3708 c) go = sp (wPack (envTier1K3708 c) ins) :=
  wPack_of_checkBlockFullFastT1 gatesTier1K3708_wf h c rfl
theorem t1Ev_wBit_out00 (c : Fin (2 ^ 41)) :
    wBit (envTier1K3708 c) (outW tier1Out00 0) = Nat.beq (t1EvHi8 c) 255 := by
  rw [t1Ev_wBit_outW, t1Ev_chk 0 8 tier1In00 [(11, 161), (81, 256), (2, 0x400), (4, 512),
        (67, 0x800), (0x1000, 0x2201), (0x4000, 0x4a83)] [0xc000] tier1Out00 specTier1_00
        (by decide +kernel) c, show tier1In00 = t1EvWireSlice coinW 33 8 from rfl,
      t1Ev_wPack_wireSlice _ coinW c.val 33 8 fun i _ ↦ t1Ev_wBit_coinW c (by omega),
      t1Ev_hi8_mod c, specTier1_00]
  cases Nat.beq (t1EvHi8 c) 255 <;> rfl
theorem t1Ev_wPack_out01 (c : Fin (2 ^ 41)) :
    wPack (envTier1K3708 c) tier1Out01 = cond (Nat.beq (t1EvHi8 c) 255) (t1EvLo8 c) 0 := by
  have hLo := (t1Ev_coin_bounds c).2.2.2.1
  rw [t1Ev_chk 7 9 tier1In01 [(260, 512), (512, 528), (129, 640), (512, 0xd80), (512, 0x508),
        (513, 0x542b), (513, 0x1ae8), (513, 0x4050)] [0x39a93, 0x3a00, 0x7a00, 0xa00, 0x362b8,
        0x20a50, 0x1200, 0x3e00] tier1Out01 specTier1_01 (by decide +kernel) c,
      show tier1In01 = t1EvWireSlice coinW 25 8 ++ [outW tier1Out00 0] from rfl,
      t1Ev_wPack_append, t1Ev_len_wireSlice, t1Ev_wPack_wireSlice _ coinW c.val 25 8
        fun i _ ↦ t1Ev_wBit_coinW c (by omega),
      show (c.val / 2 ^ 25) % 2 ^ 8 = t1EvLo8 c from rfl,
      show (2 : ℕ) ^ 8 = 256 from rfl, t1Ev_wPack_singleton, t1Ev_wBit_out00 c, specTier1_01]
  cases Nat.beq (t1EvHi8 c) 255 <;> simp [cond, Nat.div_eq_of_lt hLo, Nat.mod_eq_of_lt hLo]
theorem t1Ev_wBit_a8T1W (c : Fin (2 ^ 41)) {i : ℕ} (hi : i < 8) :
    wBit (envTier1K3708 c) (a8T1W i) = (t1EvA8 c).testBit i := by
  dsimp only [a8T1W, t1EvA8]
  rw [t1Ev_wBit_xor, t1Ev_wBit_coinW c (by omega), ← t1Ev_subword_bit c.val 33 8 i hi,
    t1Ev_hi8_mod c, t1Ev_wBit_outW, t1Ev_wPack_out01 c]
  cases h : Nat.beq (t1EvHi8 c) 255 <;> dsimp only [cond]
  · rw [Nat.zero_testBit, Bool.xor_false]
  · rcases Bool.and_eq_true_iff.mp (allTree_zero (allTree_zero (by decide +kernel :
      allTree 9 0 256 (fun v ↦ allTree 4 0 8 fun j ↦ Bool.and
        (b2BEq ((255 - v).testBit j) (Bool.not (v.testBit j))) ((255 : ℕ).testBit j)) = true)
      (t1Ev_coin_bounds c).2.2.2.1) hi) with ⟨h1, h2⟩
    rw [Nat.eq_of_beq_eq_true h, h2, (b2_bEq_iff _ _).mp h1]
    cases (t1EvLo8 c).testBit i <;> rfl
theorem t1Ev_wBit_b8T1W (c : Fin (2 ^ 41)) {i : ℕ} (hi : i < 8) :
    wBit (envTier1K3708 c) (b8T1W i) = (t1EvB8 c).testBit i := by
  dsimp only [b8T1W, t1EvB8]
  rw [t1Ev_wBit_xor, t1Ev_wBit_coinW c (by omega), ← t1Ev_subword_bit c.val 25 8 i hi,
      show (c.val / 2 ^ 25) % 2 ^ 8 = t1EvLo8 c from rfl, t1Ev_wBit_outW, t1Ev_wPack_out01 c]
  cases Nat.beq (t1EvHi8 c) 255 <;> simp [cond]
theorem e1Sp5 {a b c d e f : Bool}
    (h : Bool.and a (Bool.and b (Bool.and c (Bool.and d (Bool.and e f)))) = true) :
    (a = true ∧ b = true ∧ c = true ∧ d = true ∧ e = true) ∧ f = true := by
  simpa only [Bool.and_eq_true_iff, and_assoc] using h
theorem t1Ev_cert_b2 : allTree 9 0 256 (fun a8 ↦
    let p := b2Spec a8
    let s := specTier1_02 a8
    Bool.and (Nat.blt p.1 17) (Bool.and (Nat.blt p.2.1 3) (Bool.and (Nat.blt p.2.2.1 8)
      (Bool.and (b2BEq p.2.2.2 (Nat.beq a8 255)) (Bool.and (Bool.or p.2.2.2 (Nat.ble p.2.2.1 4))
        (Bool.and (Nat.beq (s % 32) p.1) (Bool.and (Nat.beq ((s / 32) % 4) p.2.1)
          (Bool.and (Nat.beq ((s / 128) % 8) p.2.2.1) (b2BEq (s.testBit 10) p.2.2.2))))))))) =
    true := by decide +kernel
theorem t1Ev_b2_props (c : Fin (2 ^ 41)) : (t1EvPx c).1 < 17 ∧ (t1EvPx c).2.1 < 3 ∧
    (t1EvPx c).2.2.1 < 8 ∧ (t1EvPx c).2.2.2 = Nat.beq (t1EvA8 c) 255 ∧
    ((t1EvPx c).2.2.2 = false → (t1EvPx c).2.2.1 ≤ 4) := by
  rcases (e1Sp5 (allTree_zero t1Ev_cert_b2 (t1Ev_coin_bounds c).2.2.2.2.2.1)).1 with
    ⟨h1, h2, h3, h4, h5⟩
  dsimp only [t1EvPx]
  exact ⟨Nat.blt_eq.mp h1, Nat.blt_eq.mp h2, Nat.blt_eq.mp h3, (b2_bEq_iff _ _).mp h4,
    fun hf ↦ Nat.ble_eq.mp (by rwa [hf, Bool.false_or] at h5)⟩
theorem t1Ev_out02_slices (c : Fin (2 ^ 41)) :
    wPack (envTier1K3708 c) (t1EvOutSlice tier1Out02 0 5) = (t1EvPx c).1 ∧
      wPack (envTier1K3708 c) (t1EvOutSlice tier1Out02 5 2) = (t1EvPx c).2.1 ∧
      wPack (envTier1K3708 c) (t1EvOutSlice tier1Out02 7 3) = (t1EvPx c).2.2.1 ∧
      wBit (envTier1K3708 c) (outW tier1Out02 10) = (t1EvPx c).2.2.2 := by
  have ha8 : t1EvA8 c < 2 ^ 8 := (t1Ev_coin_bounds c).2.2.2.2.2.1
  have hP2 := (t1Ev_chk 15 8 tier1In02 [(256, 32), (64, 161), (512, 0x400), (3, 0x802),
    (36, 0x800), (264, 0x800), (17, 0x800), (0x70e0, 0x8101), (0x51a0, 0x170e0),
    (0x3800, 0x20701), (0x18100, 0x760c0)] [0x1802, 0x2804, 0x4808, 0x8810, 0x800, 0x78101,
    0xa8100, 0x22040, 0xa9120, 0x170e0, 0x40000] tier1Out02 specTier1_02
    (by decide +kernel) c).trans (congrArg specTier1_02 (by
      rw [show tier1In02 = t1EvWireSlice a8T1W 0 8 from rfl, t1Ev_wPack_wireSlice _ a8T1W
        (t1EvA8 c) 0 8 fun i hi ↦ (Nat.zero_add i).symm ▸ t1Ev_wBit_a8T1W c hi, pow_zero,
        Nat.div_one, Nat.mod_eq_of_lt ha8]))
  rcases t1Ev_and4 (e1Sp5 (allTree_zero t1Ev_cert_b2 ha8)).2 with ⟨s1, s2, s3, s4⟩
  simp only [t1Ev_wPack_outSlice, t1Ev_wBit_outW, hP2, t1EvPx, pow_zero, Nat.div_one]
  exact ⟨Nat.beq_eq.mp s1, Nat.beq_eq.mp s2, Nat.beq_eq.mp s3, (b2_bEq_iff _ _).mp s4⟩
theorem t1Ev_cert_phi_z2 :
    Bool.and
      (allTree 5 0 11 (fun r11 ↦ allTree 6 0 17 (fun r17 ↦ Nat.blt (phiU1 r11 r17) 187)))
      (allTree 3 0 3 (fun h2 ↦ allTree 7 0 64 (fun x ↦
        Bool.and (Nat.blt (b11Z2OfHX h2 x) 256)
          (Bool.or (Bool.not (decodeUltraNuc192 (64 * h2 + x)).1)
            (Nat.blt (b11Z2OfHX h2 x) 187))))) = true := by decide +kernel
theorem t1Ev_two_bits {x : ℕ} {a b : Bool} (h : x = cond a 1 0 + cond b 2 0) :
    x.testBit 0 = a ∧ x.testBit 1 = b := h ▸ by cases a <;> cases b <;> exact ⟨rfl, rfl⟩
theorem t1Ev_testBit0_pair (u v : Bool) : (cond u 1 0 + 2 * cond v 1 0).testBit 0 = u := by
  cases u <;> cases v <;> rfl
theorem t1Ev_testBit0_single (u : Bool) : (cond u 1 0).testBit 0 = u := by cases u <;> rfl
theorem t1Ev_cond_lt2 (u : Bool) : cond u 1 0 < 2 := by cases u <;> decide
/-- `knOk` (`isX and hi10 < 768`) flag of `F11`. -/
def t1EvKnOk (c : Fin (2 ^ 41)) : Bool := Bool.and (t1EvPx c).2.2.2 (Nat.blt (t1EvHi10 c) 768)
theorem t1Ev_wPack_v23T1W (c : Fin (2 ^ 41)) : wPack (envTier1K3708 c) v23T1W = t1EvV23 c := by
  have hb8 := (t1Ev_coin_bounds c).2.2.2.2.2.2.1
  rw [show v23T1W = t1EvWireSlice b8T1W 0 6 ++ (t1EvWireSlice coinW 5 6 ++
        (t1EvWireSlice coinW 0 5 ++ (t1EvWireSlice coinW 11 4 ++ t1EvWireSlice b8T1W 6 2)))
        from rfl, t1Ev_wPack_append, t1Ev_wPack_append, t1Ev_wPack_append, t1Ev_wPack_append,
      t1Ev_len_wireSlice, t1Ev_len_wireSlice, t1Ev_len_wireSlice, t1Ev_len_wireSlice,
      t1Ev_wPack_wireSlice _ b8T1W (t1EvB8 c) 0 6
        fun i _ ↦ (Nat.zero_add i).symm ▸ t1Ev_wBit_b8T1W c (by omega),
      t1Ev_wPack_wireSlice _ coinW c.val 5 6 fun i _ ↦ t1Ev_wBit_coinW c (by omega),
      t1Ev_wPack_wireSlice _ coinW c.val 0 5
        fun i _ ↦ (Nat.zero_add i).symm ▸ t1Ev_wBit_coinW c (by omega),
      t1Ev_wPack_wireSlice _ coinW c.val 11 4 fun i _ ↦ t1Ev_wBit_coinW c (by omega),
      t1Ev_wPack_wireSlice _ b8T1W (t1EvB8 c) 6 2 fun i _ ↦ t1Ev_wBit_b8T1W c (by omega)]
  dsimp only [t1EvV23, cart254V23, t1EvW11, t1EvC5, t1EvLo10, t1EvY20]
  omega
/- ## Section 1: Parity-Mask Wire-List & `m40` Congruence Helpers -/

/-- Set bit positions `< k` of parity mask `msk` (MSB-first, matching `oddBits`). -/
def bitsOfMaskT1 (msk : ℕ) : ℕ → List ℕ
  | 0 => []
  | k + 1 => cond (msk.testBit k) (k :: bitsOfMaskT1 msk k) (bitsOfMaskT1 msk k)
theorem listXorBool_bitsOfMaskT1 {bitOf : ℕ → Bool} (e msk : ℕ) :
    ∀ k, (∀ u < k, bitOf u = e.testBit u) →
      listXorBool bitOf (bitsOfMaskT1 msk k) = oddBits (e &&& msk) k
  | 0, _ => rfl
  | k + 1, hBit => by
      rw [bitsOfMaskT1, oddBits, Nat.testBit_and]
      cases msk.testBit k <;> simp [cond, listXorBool, hBit k (Nat.lt_succ_self k),
        listXorBool_bitsOfMaskT1 e msk k fun u hu ↦ hBit u (Nat.lt_succ_of_lt hu), Bool.xor_comm]
theorem listXorBool_midPredBit_bitsOfMaskT1 (M : ℕ) (coreGates : Fin M → ℕ × ℕ) (m0 m1 : ℕ)
    (c : Fin (2 ^ 41)) (m40 msk : ℕ) :
    listXorBool (midPredBit M coreGates m0 m1 c m40) (bitsOfMaskT1 msk (42 + M)) =
      oddBits (xagEnv c.val M coreGates M le_rfl &&& msk) (42 + M) :=
  listXorBool_bitsOfMaskT1 _ msk (42 + M) fun _ hu ↦ by simp [midPredBit, Nat.ble_eq_true_of_le hu]
theorem listXorBool_tailPredBit_bitsOfMaskT1 (M : ℕ) (coreGates : Fin M → ℕ × ℕ) (c : Fin (2 ^ 41))
    (m40 msk : ℕ) :
    listXorBool (tailPredBit M coreGates c m40) (bitsOfMaskT1 msk (42 + M)) =
      oddBits (xagEnv c.val M coreGates M le_rfl &&& msk) (42 + M) :=
  listXorBool_bitsOfMaskT1 _ msk (42 + M) fun _ hu ↦ by simp [tailPredBit, Nat.ble_eq_true_of_le hu]
theorem preCnotBit40_congrT1 {m₁ m₂ : ℕ} (hm : ∀ k : Fin 40, m₁.testBit k.val = m₂.testBit k.val)
    {j : ℕ} (hj : j < 40) : preCnotBit40 m₁ j = preCnotBit40 m₂ j := by
  have hb (k : ℕ) (hk : k < 40) : m₁.testBit k = m₂.testBit k := hm ⟨k, hk⟩
  dsimp only [preCnotBit40]
  rw [hb 35 (by omega), hb 1 (by omega), hb 32 (by omega), hb 15 (by omega),
      hb 34 (by omega), hb 0 (by omega), hb 14 (by omega), hb j hj]
  split_ifs with _ _ _ h16 h2 <;> try rfl
  · have := Nat.le_of_ble_eq_true (Bool.and_eq_true_iff.mp h16).2
    rw [hb (j + 8) (by omega)]
  · have := Nat.le_of_ble_eq_true (Bool.and_eq_true_iff.mp h2).2
    rw [hb (j + 6) (by omega)]
theorem midPredBit_congr_m40T1 (M : ℕ) (coreGates : Fin M → ℕ × ℕ) (m0 m1 : ℕ) (c : Fin (2 ^ 41))
    {m₁ m₂ : ℕ} (hm : ∀ k : Fin 40, m₁.testBit k.val = m₂.testBit k.val) :
    midPredBit M coreGates m0 m1 c m₁ = midPredBit M coreGates m0 m1 c m₂ :=
  have p (j) (hj : j < 40) := preCnotBit40_congrT1 hm hj
  funext fun _ ↦ by simp only [midPredBit, p 15 (by omega), p 1 (by omega), p 33 (by omega),
    p 14 (by omega), p 0 (by omega)]
theorem tailPredBit_congr_m40T1 (M : ℕ) (coreGates : Fin M → ℕ × ℕ) (c : Fin (2 ^ 41))
    {m₁ m₂ : ℕ} (hm : ∀ k : Fin 40, m₁.testBit k.val = m₂.testBit k.val) :
    tailPredBit M coreGates c m₁ = tailPredBit M coreGates c m₂ :=
  have p (j) (hj : j < 40) := preCnotBit40_congrT1 hm hj
  funext fun _ ↦ by simp only [tailPredBit, p 15 (by omega), p 1 (by omega), p 33 (by omega),
    p 14 (by omega), p 0 (by omega)]
/-
## Section 2: `Tier1` (`M = 166`) Reverse Bilinear Tables, Bound Certificates & `wPack` Helpers
-/
end QuantumComputation.Specs.PhotochemistrySolution.Tier1K3708
end
end

noncomputable section
open QuantumComputation.Specs.PhotochemistrySolution.TopSelectBridge
  QuantumComputation.Specs.PhotochemistrySolution.SelectKin526OneWrap
  QuantumComputation.Specs.PhotochemistrySolution.TargetBScr
open Operator QProg Matrix Circuit Qubit PrimitiveGate
  QuantumComputation.Specs.PhotochemistrySolution
  QuantumComputation.Specs.PhotochemistrySolution.RouterSelectWiringA
  QuantumComputation.Specs.PhotochemistrySolution.ProviderCore
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
namespace QuantumComputation.Specs.PhotochemistrySolution.PotSelectWiring
open QuantumComputation.Specs PhotochemistrySolution.KetSupport
  PhotochemistrySolution.SelectCompactAnc PhotochemistrySolution.SplitRouter47_187
open PhotochemistrySolution.SelectOracles PhotochemistrySolution.RouterSelectWiringB
  PhotochemistrySolution.Stage12Compact PhotochemistrySolution.ZeroNEremSpec
open PhotochemistrySolution.SelectDataBuilder
open _root_.DynamicCircuit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt hiding bit_cases
  eval_seq_mulVec ket ket_CNOT ket_TOFF ket_X ket_projector_one ket_projector_zero matrix_ext_ket
  qAssign_obs_map_val
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SplitRouterSeqBell26k (SupportedOn)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB (ket matrix_ext_ket)
theorem privIdx_lt (j : Fin 454) : 4602 + j.val < routerWidth 187 8 := by rw [hEW5056]; omega
attribute [local irreducible] systemQubits_frozen SelectCompactAnc.ancWOfScr
theorem supportedOn_of_inKetPred {n : ℕ} {Pred : BitAssignment n → Prop}
    {R : Operator (2 ^ n)}
    (hIn : ∀ γ : BitAssignment n, inKetPred Pred (R.mulVec (ket γ))) :
    SupportedOn Pred R :=
  fun A B hAB ↦ by
    have : NeZero (2 ^ n) := ⟨pow_ne_zero n two_ne_zero⟩
    refine matrix_ext_ket fun γ ↦ ?_
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, vec_eq_sum_ket (R.mulVec (ket γ)),
      Matrix.mulVec_sum, Matrix.mulVec_sum]
    exact Finset.sum_congr rfl fun β _ ↦ if hc : (R.mulVec (ket γ)) ((basisBitsEquiv n).symm β) = 0
      then by simp [hc] else by simp only [Matrix.mulVec_smul, hAB β (hIn γ β hc)]
theorem embedMatrix_ket_eq_writeReg {m n : ℕ} (rTot : QRegister m n) (M : Operator (2 ^ m))
    (β : BitAssignment n) {δ : BitAssignment m} (hM : M.mulVec (ket (fun i ↦ β (rTot i))) = ket δ) :
    (rTot.embedMatrix M).mulVec (ket β) = ket (DynCircExt.writeReg β rTot δ) := by
  have hr : readRegIdx rTot β = (basisBitsEquiv m).symm (fun i ↦ β (rTot i)) :=
    (basisBitsEquiv m).injective ((funext fun i ↦
      ((QRegExt.basisBits_extractIdx rTot) ((basisBitsEquiv n).symm β) i).trans
        (congrFun ((basisBitsEquiv n).apply_symm_apply β) (rTot i))).trans
          ((basisBitsEquiv m).apply_symm_apply _).symm)
  let y := (basisBitsEquiv m).symm δ
  have hE (z' : Fin (2 ^ m)) : M z' ((basisBitsEquiv m).symm (fun i ↦ β (rTot i))) = Pi.single (M :=
      fun _ ↦ ℂ) y 1 z' :=
    congrFun ((Matrix.mulVec_single_one M _).symm.trans (((congrArg M.mulVec (ket_eq_single_symm
        _)).symm).trans
      (hM.trans (ket_eq_single_symm δ)))) z'
  change (rTot.embedMatrix M).mulVec (DynCircExt.ket β) = DynCircExt.ket _
  rw [embedMatrix_mulVec_ket_sym rTot M β, hr, Finset.sum_eq_single y
    (fun z' _ hz ↦ by rw [hE z', Pi.single_eq_of_ne hz, zero_smul])
        (fun hy ↦ (hy (Finset.mem_univ y)).elim),
    hE y, Pi.single_eq_same, one_smul]
  exact congrArg ket (congrArg (DynCircExt.writeReg β rTot)
      ((basisBitsEquiv m).apply_symm_apply δ))
theorem validRouter_compose_writeReg {M D m n : ℕ} (rTot : QRegister m n) (r : RouterReg M D m)
    (η : BitAssignment n) (δ : BitAssignment m) (hV : ValidRouterInput r δ) :
    ValidRouterInput (rTot.compose r) (DynCircExt.writeReg η rTot δ) := by
  have hAt (i) : DynCircExt.writeReg η rTot δ ((rTot.compose r) i) = δ (r i) :=
    DynCircExt.writeReg_apply_reg η rTot δ (r i)
  have hId (f : Fin D → Fin (routerWidth M D)) :
      idxValD (fun d ↦ (rTot.compose r) (f d)) (DynCircExt.writeReg η rTot δ) = idxValD (fun d ↦
          r (f d)) δ :=
    Nat.eq_of_testBit_eq fun d ↦
        by
          rw [testBit_idxValD, testBit_idxValD]
          split_ifs <;> simp only [hAt]
  refine ⟨fun hr ↦ (hAt _).trans (hV.1 ((hAt _).symm.trans hr)),
    fun hh ↦ (hId _).symm ▸ hV.2.1 ((hAt _).symm.trans hh),
    fun hr ↦ (hId _).symm ▸ hV.2.2.1 ((hAt _).symm.trans hr),
    fun b ↦ ⟨(hAt _).trans (hV.2.2.2.1 b).1, (hAt _).trans (hV.2.2.2.1 b).2.1,
      (hAt _).trans (hV.2.2.2.1 b).2.2.1, (hAt _).trans (hV.2.2.2.1 b).2.2.2⟩, fun w hw ↦ ?_⟩
  rcases Finset.mem_image.mp hw with ⟨i, hi, rfl⟩
  exact (hAt i).trans (hV.2.2.2.2 (r i) (Finset.mem_image.mpr ⟨i, hi, rfl⟩))
theorem swapVecBits_compose_writeReg {m n : ℕ} (rTot : QRegister m n) (u v : Fin 24 → Wire m)
    (injU : Function.Injective u) (injV : Function.Injective v) (disjUV : ∀ j k, u j ≠ v k)
    (η : BitAssignment n) (δ : BitAssignment m) : swapVecBits 24 (fun b ↦ rTot (u b))
    (fun b ↦ rTot (v b)) (DynCircExt.writeReg η rTot δ) =
    DynCircExt.writeReg η rTot (swapVecBits 24 u v δ) := by
  have spAmb := swapVecBits_spec 24 (fun b ↦ rTot (u b)) (fun b ↦ rTot (v b))
    (fun _ _ e ↦ injU (rTot.wires.injective e)) (fun _ _ e ↦ injV (rTot.wires.injective e))
    (fun j k e ↦ disjUV j k (rTot.wires.injective e)) (DynCircExt.writeReg η rTot δ)
  have spLoc := swapVecBits_spec 24 u v injU injV disjUV δ; funext w
  by_cases hwR : w ∈ Set.range rTot.wires
  · rcases hwR with ⟨q, rfl⟩
    rw [DynCircExt.writeReg_apply_reg]
    by_cases hqU : ∃ b, q = u b
    · obtain ⟨b, rfl⟩ :=
          hqU; exact (spAmb.1 b).trans ((DynCircExt.writeReg_apply_reg η rTot δ (v b)).trans
          (spLoc.1 b).symm)
    · by_cases hqV : ∃ b, q = v b
      · obtain ⟨b, rfl⟩ :=
            hqV; exact (spAmb.2.1 b).trans ((DynCircExt.writeReg_apply_reg η rTot δ (u b)).trans
            (spLoc.2.1 b).symm)
      · exact (spAmb.2.2 (rTot q) (fun b e ↦ hqU ⟨b, rTot.wires.injective e⟩)
            (fun b e ↦ hqV ⟨b, rTot.wires.injective e⟩)).trans
          ((DynCircExt.writeReg_apply_reg η rTot δ q).trans (spLoc.2.2 q (fun b e ↦ hqU ⟨b, e⟩)
              (fun b e ↦ hqV ⟨b, e⟩)).symm)
  · rw [DynCircExt.writeReg_apply_of_not_mem _ _ _ _ hwR]
    exact (spAmb.2.2 w (fun b e ↦ hwR ⟨u b, e.symm⟩)
        (fun b e ↦
        hwR ⟨v b, e.symm⟩)).trans (DynCircExt.writeReg_apply_of_not_mem η rTot δ w hwR)
theorem routerSwapBits_compose_writeReg {M D m n : ℕ} (rTot : QRegister m n) (r : RouterReg M D m)
    (η : BitAssignment n) (δ : BitAssignment m) :
    routerSwapBits (rTot.compose r) (DynCircExt.writeReg η rTot δ) =
        DynCircExt.writeReg η rTot (routerSwapBits r δ) := by
  let wR := DynCircExt.writeReg η rTot
  have hAt (i : Fin (routerWidth M D)) : wR δ ((rTot.compose r) i) = δ (r i) :=
    DynCircExt.writeReg_apply_reg η rTot δ (r i)
  have rVal {i j : Fin (routerWidth M D)} (e : r i = r j) : i.val = j.val :=
      congrArg Fin.val (r.wires.injective e)
  have hId (f : Fin D → Fin (routerWidth M D)) : idxValD (fun d ↦ (rTot.compose r) (f d))
      (wR δ) = idxValD (fun d ↦ r (f d)) δ :=
    Nat.eq_of_testBit_eq fun d ↦
        by
          rw [testBit_idxValD, testBit_idxValD]
          split_ifs <;> simp only [hAt]
  have hEff : routerHas2Eff (rTot.compose r) (wR δ) = routerHas2Eff r δ := by
    rw [routerHas2Eff, routerHas2Eff, hAt _, hId _, hId _]
  have step (buf : Fin 24 → Wire m) (injB : Function.Injective buf)
      (disjBS : ∀ p j k, buf j ≠ rSys r p k)
      (fl1 fl2 : ZMod 2) (ix1 ix2 : ℕ) (δ0 : BitAssignment m) (hfl : fl1 = fl2) (hix : ix1 = ix2) :
      (if h : fl1 = 1 ∧ ix1 < M then swapVecBits 24 (fun b ↦ rTot (buf b))
          (fun b ↦ rTot (rSys r ⟨ix1, h.2⟩ b)) (wR δ0) else wR δ0) =
      wR (if h : fl2 = 1 ∧ ix2 < M then swapVecBits 24 buf (fun b ↦
          rSys r ⟨ix2, h.2⟩ b) δ0 else δ0) := by
    subst hfl hix
    split_ifs with hc
    · exact swapVecBits_compose_writeReg rTot buf _ injB
        (fun _ _ e ↦ Fin.ext (by
          have hv := rVal e
          dsimp at hv
          omega)) (disjBS _) η δ0
    · rfl
  unfold routerSwapBits
  rw [show routerLoBits (rTot.compose r) (wR δ) = wR (routerLoBits r δ) from
    step (rBufLo r) (fun _ _ e ↦ Fin.ext (by
      have hv := rVal e
      dsimp at hv
      omega))
      (fun _ j _ e ↦
          by
            have _ := j.isLt
            have hv := rVal e
            dsimp at hv
            omega) _ _ _ _ δ (hAt _)
      (by rw [routerIdxMinVal, routerIdxMinVal, hEff, hId _, hId _])]
  exact step (rBufHi r) (fun _ _ e ↦ Fin.ext (by
    have hv := rVal e
    dsimp at hv
    omega))
    (fun _ j _ e ↦
        by
          have _ := j.isLt
          have hv :=
                                  rVal e
          dsimp at hv
          omega) _ _ _ _ (routerLoBits r δ) hEff
    (by rw [routerIdxMaxVal, routerIdxMaxVal, hEff, hId _, hId _])
theorem validRouter_rElec {decodeCoin : Fin (2 ^ 41) → ZeroNEremSector}
    (rElec : RouterReg 187 8 dLayout) (hRoles : rHas1 rElec = rHas1 rElecLayout ∧ rRawHas2 rElec =
    rRawHas2 rElecLayout ∧ rIdx1 rElec = rIdx1 rElecLayout ∧ rIdx2 rElec = rIdx2 rElecLayout ∧
    rBufLo rElec = rBufLo rElecLayout ∧ rBufHi rElec = rBufHi rElecLayout ∧ rHA rElec =
    rHA rElecLayout ∧ rHB rElec = rHB rElecLayout ∧ rSys rElec = rSys rElecLayout)
    (hPrivScr : ∀ j : Fin 454, ∃ m : Fin scrLLayout, rElec ⟨4602 + j.val, privIdx_lt j⟩ =
    rScrLayout m ∧ (m.val < 65 ∨ 153 ≤ m.val)) {α : BitAssignment dLayout} (hScr : CleanScr α)
    (c : Fin (2 ^ 41)) (z : BitAssignment 41) :
    ValidRouterInput rElec (routedStage2 decodeCoin α c z) := by
  obtain ⟨h1, h2, hi1, hi2, hBL, hBH, hA, hB, _⟩ := hRoles
  obtain ⟨hVN, _, hVE, _, _, _⟩ := validRouter_stage1 (decodeCoin := decodeCoin) hScr c z
  refine ⟨h1.symm ▸ h2.symm ▸ hVE.1, h1.symm ▸ hi1.symm ▸ hVE.2.1, h2.symm ▸ hi2.symm ▸ hVE.2.2.1,
    fun b ↦ hBL.symm ▸ hBH.symm ▸ hA.symm ▸ hB.symm ▸ hVE.2.2.2.1 b, fun w hw ↦ ?_⟩
  rcases Finset.mem_image.mp hw with ⟨i, hi, rfl⟩
  have ⟨_, _⟩ : 4602 ≤ i.val ∧ i.val < 5056 :=
    ⟨(show basePub 187 8 = 4602 from rfl) ▸ (Finset.mem_filter.mp hi).2, i.isLt.trans_eq hEW5056⟩
  obtain ⟨m, hm, hmBnd⟩ := hPrivScr ⟨i.val - 4602, by omega⟩
  rw [show i = ⟨4602 + (i.val - 4602), privIdx_lt ⟨i.val - 4602,
      by omega⟩⟩ from Fin.ext (by
        dsimp
        omega), hm]
  have ⟨hmVal, _⟩ : (rScrLayout m).val = 5650 + m.val ∧ m.val < 1565 := ⟨val_rScrLayout m, m.isLt⟩
  have hNeNuc (idx : Fin (routerWidth 47 6))
      (_ : (14 ≤ idx.val ∧ idx.val < 62) ∨ (110 ≤ idx.val ∧ idx.val < 1238))
          (e : rNucLayout idx = rScrLayout m) : False := by
    have hv := hmVal.symm.trans ((congrArg Fin.val e).symm.trans (val_nucRouterWireFn idx))
    split_ifs at hv <;> omega
  rw [routedStage2, routerSwapBits_outside_mod rNucLayout hVN
    (fun b e ↦ hNeNuc ⟨14 + b.val, by
      rw [hNW1394]
      omega⟩ (by
      dsimp
      omega) e.symm)
    (fun b e ↦ hNeNuc ⟨38 + b.val, by
      rw [hNW1394]
      omega⟩ (by
      dsimp
      omega) e.symm)
    (fun p b e ↦ hNeNuc ⟨110 + 24 * p.val + b.val, by
      rw [hNW1394]
      omega⟩
        (by
          dsimp
          omega) e.symm)]
  unfold routedStage1 routedStage0
  rw [DynCircExt.writeReg_apply_of_not_mem _ rOut40Layout _ _ fun ⟨k, hk⟩ ↦
      ((fun (_ : _ ∧ _) ↦ by omega)
          ⟨k.isLt, (val_rOut40Layout k).symm.trans ((congrArg Fin.val hk).trans hmVal)⟩),
    DynCircExt.writeReg_apply_of_not_mem _ rLcu82Layout _ _ fun ⟨l, hl⟩ ↦
      ((fun _ ↦ by omega) ((val_rLcu82Layout l).symm.trans ((congrArg Fin.val hl).trans hmVal)))]
  exact hScr m
end QuantumComputation.Specs.PhotochemistrySolution.PotSelectWiring

namespace QuantumComputation.Specs.PhotochemistrySolution.Coin70Lift
open QuantumComputation.Specs PhotochemistrySolution.RouterSelectWiringB
  PhotochemistrySolution.Stage12Compact PhotochemistrySolution.ZeroNEremSpec
  PhotochemistrySolution.PotSelectWiring
open _root_.DynamicCircuit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt hiding bit_cases
  eval_seq_mulVec ket ket_CNOT ket_TOFF ket_X ket_projector_one ket_projector_zero localIdx
  matrix_ext_ket qAssign_obs_map_val
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SelectCompactAnc (ancWOfScr)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB (ket matrix_ext_ket)
abbrev rScrExt (kExt : ℕ) (hk : kExt ≤ 72) : QRegister (scrLExt kExt) dLayout :=
    rScrLGen (hpExt kExt hk)
abbrev rLcuExt (kExt : ℕ) (hk : kExt ≤ 72) : QRegister (mExt kExt + 2) dLayout :=
    rLcuLGen (hpExt kExt hk)
abbrev pScrExt (kExt : ℕ) (hk : kExt ≤ 72) : Operator (2 ^ dLayout) :=
    (rScrExt kExt hk).basisOutcomeProjector 0
theorem val_rScrExt {kExt : ℕ} (hk : kExt ≤ 72) (i : Fin (scrLExt kExt)) : (rScrExt kExt hk i).val =
    5650 + i.val := by change 5616 + (34 + i.val) = 5650 + i.val; omega
theorem val_rLcuExt {kExt : ℕ} (hk : kExt ≤ 72) (i : Fin (mExt kExt + 2)) :
    (rLcuExt kExt hk i).val = (7215 - kExt) + i.val := by
  have hi := i.isLt
  change 5616 + ((34 + (1565 - kExt)) + i.val) = (7215 - kExt) + i.val; omega
attribute [local irreducible] systemQubits_frozen SelectCompactAnc.ancWOfScr
theorem pScrExt_herm (kExt : ℕ) (hk : kExt ≤ 72) : (pScrExt kExt hk)ᴴ = pScrExt kExt hk :=
    QRegister.basisOutcomeProjector_conjTranspose (rScrExt kExt hk) 0
theorem pScrExt_idem (kExt : ℕ) (hk : kExt ≤ 72) : pScrExt kExt hk * pScrExt kExt hk =
    pScrExt kExt hk := QRegister.basisOutcomeProjector_mul_self (rScrExt kExt hk) 0
local instance (priority := 100000) {k : ℕ} : NeZero (2 ^ k) := ⟨pow_ne_zero k two_ne_zero⟩
theorem zmod2_add_cancel_c70 (a b : ZMod 2) : a + b + b = a := by
  fin_cases a <;> fin_cases b <;> rfl
theorem zmod2_add_eq_zero_iff_c70 (a b : ZMod 2) : a + b = 0 ↔ a = b :=
  ⟨fun he ↦ by rw [← zmod2_add_cancel_c70 a b, he, zero_add],
   fun he ↦ by subst he; have h0 := zmod2_add_cancel_c70 0 a; rwa [zero_add] at h0⟩
/-- Involutive bijection wrapped as a `Unitary (2 ^ n)`. -/
def involUnitary_c70 {n : ℕ} (f : BitAssignment n → BitAssignment n) (hf : Function.Involutive f) :
    Unitary (2 ^ n) := permUnitary ⟨f, f, hf, hf⟩
theorem involUnitary_mulVec_ket_c70 {n : ℕ} (f : BitAssignment n → BitAssignment n)
    (hf : Function.Involutive f) (β : BitAssignment n) : (involUnitary_c70 f hf).1.mulVec (ket β) =
    ket (f β) :=
  permUnitary_mulVec_ket ⟨f, f, hf, hf⟩ β
/-- Bitwise XOR toggle on register `rC` by fixed bit-assignment `γ`. -/
def togBits_c70 {m n : ℕ} (rC : QRegister m n) (γ : BitAssignment m) (δ : BitAssignment n) :
    BitAssignment n := DynCircExt.writeReg δ rC (fun j ↦ δ (rC j) + γ j)
theorem togBits_invol_c70 {m n : ℕ} (rC : QRegister m n) (γ : BitAssignment m) :
    Function.Involutive (togBits_c70 rC γ) :=
  fun δ ↦ funext fun w ↦ by
    by_cases hw : w ∈ Set.range rC.wires
    · rcases hw with ⟨j, rfl⟩
      rw [togBits_c70, DynCircExt.writeReg_apply_reg, togBits_c70,
          DynCircExt.writeReg_apply_reg]
      exact zmod2_add_cancel_c70 (δ (rC j)) (γ j)
    · rw [togBits_c70, DynCircExt.writeReg_apply_of_not_mem _ _ _ _ hw, togBits_c70,
        DynCircExt.writeReg_apply_of_not_mem _ _ _ _ hw]
/-- Involutive permutation unitary toggling register `rC` by `γ`. -/
def uTogGen_c70 {m n : ℕ} (rC : QRegister m n) (γ : BitAssignment m) : Unitary (2 ^ n) :=
    involUnitary_c70 (togBits_c70 rC γ) (togBits_invol_c70 rC γ)
theorem uTogGen_mulVec_ket_c70 {m n : ℕ} (rC : QRegister m n) (γ : BitAssignment m)
    (β : BitAssignment n) : (uTogGen_c70 rC γ).1.mulVec (ket β) = ket (togBits_c70 rC γ β) :=
  involUnitary_mulVec_ket_c70 _ _ β
/-- Local `2 ^ m` toggle unitary for bit-assignment `γ`. -/
def uTogLocal_c70 {m : ℕ} (γ : BitAssignment m) : Unitary (2 ^ m) :=
    uTogGen_c70 (QRegister.block 0 m (Nat.zero_add m).le) γ
theorem embedUnitary_uTogLocal_c70 {m n : ℕ} (rC : QRegister m n) (γ : BitAssignment m) :
    rC.embedUnitary (uTogLocal_c70 γ) = uTogGen_c70 rC γ := by
  refine Subtype.ext (matrix_ext_ket fun β ↦ ?_)
  unfold uTogLocal_c70;
  rw [QRegister.embedUnitary_val,
      embedMatrix_ket_eq_writeReg rC _ β (uTogGen_mulVec_ket_c70 _ _ _), uTogGen_mulVec_ket_c70]
  refine congrArg ket (funext fun w ↦ ?_)
  by_cases hw : w ∈ Set.range rC.wires
  · rcases hw with ⟨j, rfl⟩
    have hj : (QRegister.block 0 m (Nat.zero_add m).le : QRegister m m) j = j :=
        Fin.ext (Nat.zero_add j.val)
    rw [DynCircExt.writeReg_apply_reg]; unfold togBits_c70;
    rw [DynCircExt.writeReg_apply_reg]
    conv_lhs => rw [← hj]
    rw [DynCircExt.writeReg_apply_reg, hj]
  · rw [DynCircExt.writeReg_apply_of_not_mem _ _ _ _ hw, togBits_c70,
        DynCircExt.writeReg_apply_of_not_mem _ _ _ _ hw]
theorem uTogGen_mul_self_c70 {m n : ℕ} (rC : QRegister m n) (γ : BitAssignment m) :
    (uTogGen_c70 rC γ).1 * (uTogGen_c70 rC γ).1 = 1 :=
  matrix_ext_ket fun β ↦ by
    rw [← Matrix.mulVec_mulVec, uTogGen_mulVec_ket_c70, uTogGen_mulVec_ket_c70,
      togBits_invol_c70 rC γ β, Matrix.one_mulVec]
theorem uTogGen_herm_c70 {m n : ℕ} (rC : QRegister m n) (γ : BitAssignment m) :
    (uTogGen_c70 rC γ).1ᴴ = (uTogGen_c70 rC γ).1 := by
  change (uTogGen_c70 rC γ)⁻¹.1 = (uTogGen_c70 rC γ).1
  rw [← Matrix.mul_one (uTogGen_c70 rC γ)⁻¹.1, ← uTogGen_mul_self_c70 rC γ,
    ← Matrix.mul_assoc, ← Submonoid.coe_mul, inv_mul_cancel, OneMemClass.coe_one, Matrix.one_mul]
/-- Orthogonal projector onto computational basis states with `rC = γ`. -/
def projBits_c70 {m n : ℕ} [NeZero (2 ^ n)] (rC : QRegister m n) (γ : BitAssignment m) :
    Operator (2 ^ n) := (uTogGen_c70 rC γ).1 * rC.basisOutcomeProjector 0 * (uTogGen_c70 rC γ).1
theorem projBits_mulVec_ket_c70 {m n : ℕ} [NeZero (2 ^ n)] (rC : QRegister m n)
    (γ : BitAssignment m) (β : BitAssignment n) : (projBits_c70 rC γ).mulVec (ket β) =
    if (∀ j : Fin m, β (rC j) = γ j) then ket β else 0 := by
  unfold projBits_c70;
  rw [Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, uTogGen_mulVec_ket_c70,
      SelectRefl.ket_basisOutcomeProjector_zero]
  have hiff : (∀ j : Fin m, togBits_c70 rC γ β (rC j) = 0) ↔ ∀ j : Fin m, β (rC j) = γ j :=
    ⟨fun hz j ↦
        (zmod2_add_eq_zero_iff_c70 _ _).mp ((DynCircExt.writeReg_apply_reg β rC _ j).symm.trans
        (hz j)),
     fun he j ↦
         (DynCircExt.writeReg_apply_reg β rC _ j).trans ((zmod2_add_eq_zero_iff_c70 _ _).mpr
         (he j))⟩
  by_cases hc : ∀ j : Fin m, β (rC j) = γ j
  · rw [ite_eq_left (hiff.mpr hc), ite_eq_left hc, uTogGen_mulVec_ket_c70, togBits_invol_c70]
  · rw [ite_eq_right (mt hiff.mp hc), ite_eq_right hc, Matrix.mulVec_zero]
theorem projBits_herm_c70 {m n : ℕ} [NeZero (2 ^ n)] (rC : QRegister m n) (γ : BitAssignment m) :
    (projBits_c70 rC γ)ᴴ =
    projBits_c70 rC γ
    := by unfold projBits_c70; rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
            uTogGen_herm_c70, QRegister.basisOutcomeProjector_conjTranspose, Matrix.mul_assoc]
theorem projBits_mul_c70 {m n : ℕ} [NeZero (2 ^ n)] (rC : QRegister m n) (γ δ : BitAssignment m) :
    projBits_c70 rC γ * projBits_c70 rC δ = if γ = δ then projBits_c70 rC γ else 0 :=
  matrix_ext_ket fun β ↦ by
    rw [← Matrix.mulVec_mulVec, projBits_mulVec_ket_c70]
    by_cases hδ : ∀ j : Fin m, β (rC j) = δ j <;> rcases eq_or_ne γ δ with rfl | hγδ
    · rw [ite_eq_left rfl, ite_eq_left hδ]
    · rw [ite_eq_right hγδ, Matrix.zero_mulVec, ite_eq_left hδ, projBits_mulVec_ket_c70,
        ite_eq_right fun hγ ↦ hγδ (funext fun j ↦ (hγ j).symm.trans (hδ j))]
    · rw [ite_eq_left rfl, ite_eq_right hδ, Matrix.mulVec_zero, projBits_mulVec_ket_c70,
          ite_eq_right hδ]
    · rw [ite_eq_right hγδ, Matrix.zero_mulVec, ite_eq_right hδ, Matrix.mulVec_zero]
theorem sum_projBits_c70 {m n : ℕ} [NeZero (2 ^ n)] (rC : QRegister m n) : (∑ γ : BitAssignment m,
    projBits_c70 rC γ) = 1 :=
  matrix_ext_ket fun β ↦ by
    rw [Matrix.sum_mulVec, Matrix.one_mulVec, Finset.sum_eq_single (fun j ↦ β (rC j))
      (fun γ _ hne ↦
          by rw [projBits_mulVec_ket_c70, ite_eq_right (fun hγ ↦ hne (funext fun j ↦ (hγ j).symm))])
      (fun hmem ↦ absurd (Finset.mem_univ _) hmem), projBits_mulVec_ket_c70, ite_eq_left (fun _ ↦
          rfl)]
theorem embedMatrix_projBits_c70 {m d n : ℕ} [NeZero (2 ^ d)] [NeZero (2 ^ n)]
    (rTot : QRegister d n) (rC : QRegister m d) (γ : BitAssignment m) :
    rTot.embedMatrix (projBits_c70 rC γ) = projBits_c70 (rTot.compose rC) γ :=
  embedMatrix_eq_of_ketMap rTot (projBits_c70 rC γ) (projBits_c70 (rTot.compose rC) γ) (fun α ↦
    if ∀ j : Fin m, α (rC j) = γ j then 1 else 0) id
    (fun α ↦ by
      rw [projBits_mulVec_ket_c70]
      split_ifs <;> simp)
    (fun δ ↦ by
      dsimp only [id]
      rw [projBits_mulVec_ket_c70, writeReg_self]
      change (if ∀ j : Fin m, δ (rTot (rC j)) = γ j then _ else _) = _
      split_ifs <;> simp)
theorem pScrExt_mul_projBits_c70 {kExt n : ℕ} [NeZero (2 ^ n)] (hk : kExt ≤ 72)
    (rTot : QRegister dLayout n) (γ : BitAssignment kExt) :
    let P_ext := (rTot.compose (rScrExt kExt hk)).basisOutcomeProjector 0;
    let R₀ := (rTot.compose rScrLayout).basisOutcomeProjector 0;
    let U_γ := uTogGen_c70 (rTot.compose (rCoinExt kExt hk)) γ
    P_ext * projBits_c70 (rTot.compose (rCoinExt kExt hk)) γ = U_γ.1 * R₀ * U_γ.1 := by
  intro P_ext R₀ U_γ
  let rC := rTot.compose (rCoinExt kExt hk)
  refine matrix_ext_ket fun β ↦ ?_
  rw [← Matrix.mulVec_mulVec, Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      projBits_mulVec_ket_c70, uTogGen_mulVec_ket_c70, SelectRefl.ket_basisOutcomeProjector_zero]
  have eqS (m : Fin scrLLayout) (hlt : m.val < 1565 - kExt) :
      togBits_c70 rC γ β ((rTot.compose rScrLayout) m) = β ((rTot.compose (rScrExt kExt hk))
          ⟨m.val, hlt⟩) := by
    rw [togBits_c70, DynCircExt.writeReg_apply_of_not_mem _ _ _ _ fun ⟨j, hj⟩ ↦ by
      have hv := congrArg Fin.val (rTot.wires.injective hj)
      rw [val_rCoinExt, val_rScrLayout] at hv
      omega]
    exact congrArg β (congrArg rTot.wires (Fin.ext (by rw [val_rScrLayout, val_rScrExt])))
  have eqC (j : Fin kExt) :
      togBits_c70 rC γ β ((rTot.compose rScrLayout)
          ⟨(1565 - kExt) + j.val, by
            dsimp [scrLLayout]
            omega⟩) = β (rC j) + γ j := by
    rw [show (rTot.compose rScrLayout) ⟨(1565 - kExt) + j.val, _⟩ = rC j from
      congrArg rTot.wires (Fin.ext (by
        rw [val_rScrLayout, val_rCoinExt]
        dsimp
        omega)),
          togBits_c70,
      DynCircExt.writeReg_apply_reg]
  by_cases hC : ∀ j : Fin kExt, β (rC j) = γ j
  · rw [ite_eq_left hC, PhotochemistrySolution.SelectRefl.ket_basisOutcomeProjector_zero]
    by_cases hS : ∀ i : Fin (scrLExt kExt), β ((rTot.compose (rScrExt kExt hk)) i) = 0
    · rw [ite_eq_left hS, ite_eq_left fun m ↦ if hlt : m.val < 1565 -
          kExt then (eqS m hlt).trans (hS _) else by
          have hm := m.isLt
          let j : Fin kExt := ⟨m.val - (1565 - kExt), by
            dsimp [scrLLayout] at hm
            omega⟩
          exact (congrArg _ (congrArg (rTot.compose rScrLayout)
            (Fin.ext (by
              dsimp [j]
              omega) : m = ⟨(1565 - kExt) + j.val,
                by
                  dsimp [scrLLayout]
                  omega⟩))).trans
            ((eqC j).trans ((zmod2_add_eq_zero_iff_c70 _ _).mpr (hC j))),
        uTogGen_mulVec_ket_c70, togBits_invol_c70]
    · rw [ite_eq_right hS, ite_eq_right fun hAll ↦ hS fun i ↦
        (eqS ⟨i.val,
            ((fun hi ↦
            by
              dsimp [scrLExt] at hi
              dsimp [scrLLayout]
              omega) i.isLt)⟩ i.isLt).symm.trans (hAll _),
        Matrix.mulVec_zero]
  · rw [ite_eq_right hC, Matrix.mulVec_zero, ite_eq_right fun hAll ↦ hC fun j ↦
      (zmod2_add_eq_zero_iff_c70 _ _).mp ((eqC j).symm.trans (hAll _)), Matrix.mulVec_zero]
theorem pScrExt_eq_sum_tog_c70 {kExt n : ℕ} [NeZero (2 ^ n)] (hk : kExt ≤ 72)
    (rTot : QRegister dLayout n) : (rTot.compose (rScrExt kExt hk)).basisOutcomeProjector 0 = ∑ γ :
    BitAssignment kExt, (uTogGen_c70 (rTot.compose (rCoinExt kExt hk)) γ).1 *
    (rTot.compose rScrLayout).basisOutcomeProjector 0 *
    (uTogGen_c70 (rTot.compose (rCoinExt kExt hk)) γ).1 := by
  set P_ext := (rTot.compose (rScrExt kExt hk)).basisOutcomeProjector 0
  rw [show P_ext = P_ext * ∑ γ : BitAssignment kExt,
    projBits_c70 (rTot.compose (rCoinExt kExt hk)) γ by rw [sum_projBits_c70, Matrix.mul_one],
    Matrix.mul_sum]
  exact Finset.sum_congr rfl fun γ _ ↦ pScrExt_mul_projBits_c70 hk rTot γ
end QuantumComputation.Specs.PhotochemistrySolution.Coin70Lift

namespace QuantumComputation.Specs.PhotochemistrySolution.RouterSelectWiringB
open DynamicCircuit QuantumComputation.Specs PhotochemistrySolution.SubspaceMbu
  PhotochemistrySolution.SelectCompactAnc PhotochemistrySolution.SelectFastFlags
  PhotochemistrySolution.SelectFastQft8Gidney
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt
open PhotochemistrySolution.SelectQft8GidneyStg3 PhotochemistrySolution.UnembedO3Bridge
  PhotochemistrySolution.SelectOracles PhotochemistrySolution.Kinetic664
open PhotochemistrySolution.Stage4KinFull PhotochemistrySolution.QubitizationWalkSem
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB hiding bitSign ket ket_CNOT
  ket_TOFF ket_X matrix_ext_ket writeReg writeReg_apply_of_not_mem
attribute [local irreducible] SpecDefs.systemQubits_frozen
    SelectCompactAnc.ancWOfScr PgBase.phaseGradientState
  XMeasChunkQromUnldA.phaseFlipUnitary Stage4Kin14Scb.abpKin14Usel Stage4Kin14Scb.abpKin14Csel
  Kinetic664.abpKin14SqFree2m1Usel Kinetic664.abpKin15SqFree2m1Usel Kinetic664.abpKin15SqFree2m1Csel
      Stage4KinFull.bAxisMux27
  bSpeciesSwap50
theorem uKinIdeal2m1UselLayout_comm_off {k : ℕ} (r : QRegister k dLayout)
    (hoff : OffIndexAndScratchPoly systemQubits_frozen scrWLayout (lcuSubLGen hpLayout)
      (scrSubLGen hpLayout) r)
    (M : Operator (2 ^ k)) : Commute uKinIdeal2m1UselLayout.1 (r.embedMatrix M) := by
  have : NeZero (2 ^ dLayout) := ⟨pow_ne_zero dLayout two_ne_zero⟩
  let Qid : Unitary (2 ^ dLayout) := qft8Stg3IdealU scrWLayout rPKinLayout
  have cSp : Commute uSpeciesSwap50Layout.1 _ :=
      embedUnitary_comm_of_disjoint rSpeciesSwap50Layout _ r (uSp50_disj_off hoff) M
  have cMux : Commute uMux27Layout.1 _ :=
      embedUnitary_comm_of_disjoint rMux27Layout _ r (uMux27_disj_off hoff) M
  have cQid : Commute Qid.1 (r.embedMatrix M) := embedUnitary_comm_of_disjoint rPKinLayout _ r
    (QRegister.disjoint_iff.mpr fun j i e ↦ by
      have _ := hoffIndex_bounds_layout hoff i
      have _ := (val_rPKinLayout j).symm.trans (congrArg Fin.val e)
      omega) M
  have cMid := comm_embedMatrix_of_isPhaseDiag uKinMid2m1_isPhaseDiag_layout r M fun β γ ↦
    fwdBits_congr_avoid23_sqf hAv23_15SqFree2m1 _ _
      (fun j _ ↦ DynCircExt.writeReg_apply_of_not_mem β r γ _ fun ⟨i, hi⟩ ↦ by
        have _ := hoffIndex_bounds_layout hoff i
        have hv : (r i).val = (kin226WireFn j).val :=
            congrArg Fin.val (hi.trans (rKin226_eq_fn_w0 j))
        rw [val_kin226WireFn] at hv
        split_ifs at hv <;> omega) wOutKin226 (by decide +kernel)
  unfold uKinIdeal2m1UselLayout uKinCoreIdeal2m1UselLayout
  simp only [Submonoid.coe_mul]
  exact Commute.mul_left (Commute.mul_left (unitary_inv_comm uSpeciesSwap50Layout _ cSp)
    (Commute.mul_left (Commute.mul_left (unitary_inv_comm uMux27Layout _ cMux)
      (Commute.mul_left (Commute.mul_left (unitary_inv_comm Qid _ cQid) cMid) cQid)) cMux)) cSp
end QuantumComputation.Specs.PhotochemistrySolution.RouterSelectWiringB

namespace QuantumComputation.Specs.PhotochemistrySolution.Kinetic664Stage4
open PhotochemistrySolution.RouterSelectWiringB PhotochemistrySolution.Kinetic664
  PhotochemistrySolution.SubspaceMbu PhotochemistrySolution.SelectCompactAnc
  PhotochemistrySolution.SelectQft8GidneyStg3 PhotochemistrySolution.PotSelectWiring
  PhotochemistrySolution.KetSupport
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SelectFastQft8Gidney hiding
  unitary_inv_comm
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB (ket matrix_ext_ket)
attribute [local reducible] totDimCompactGen
attribute [local irreducible] SpecDefs.systemQubits_frozen
    SelectCompactAnc.ancWOfScr bSpeciesSwap50 Stage4KinFull.bAxisMux27 abpKin14Usel
    abpKin15SqFree2m1Usel abpKin15SqFree2m1Csel
theorem uKinMid2m1Usel_sq_one : uKinMid2m1UselLayout * uKinMid2m1UselLayout = 1 := by
  have : NeZero (2 ^ dLayout) := ⟨pow_ne_zero dLayout two_ne_zero⟩
  exact Subtype.ext (matrix_ext_ket fun δ ↦ by
    rw [Submonoid.coe_mul, Submonoid.coe_one, Matrix.one_mulVec, ← Matrix.mulVec_mulVec,
      uKinMid2m1_isPhaseDiag_layout δ, Matrix.mulVec_smul, uKinMid2m1_isPhaseDiag_layout δ,
      smul_smul, bitSign_sq_eq_one, one_smul])
theorem uKinIdeal2m1Usel_sq_one : uKinIdeal2m1UselLayout * uKinIdeal2m1UselLayout = 1 :=
    inv_conj_sq_one uSpeciesSwap50Layout uKinCoreIdeal2m1UselLayout (inv_conj_sq_one
    uMux27Layout _ (inv_conj_sq_one (qft8Stg3IdealU scrWLayout rPKinLayout) uKinMid2m1UselLayout
    uKinMid2m1Usel_sq_one))
theorem uKinIdeal2m1_comm_proj0 (u : Wire dLayout)
    (hu : u.val < 5755 ∨ (6083 ≤ u.val ∧ u.val ≠ 6104)) :
    uKinIdeal2m1UselLayout.1 * pBit0 u = pBit0 u * uKinIdeal2m1UselLayout.1 := by
  have : NeZero (2 ^ dLayout) := ⟨pow_ne_zero dLayout two_ne_zero⟩
  let P := pBit0 u
  have cConj {m : ℕ} (r : QRegister m dLayout) (U : Unitary (2 ^ m)) {A : Operator (2 ^ dLayout)}
      (h : ∀ j, (r j).val ≠ u.val) (hA : A * P = P * A) :
      (r.embedUnitary U)⁻¹.1 * A * (r.embedUnitary U).1 * P = P * ((r.embedUnitary U)⁻¹.1 * A *
          (r.embedUnitary U).1) := by
    have cU := embedUnitary_comm_of_disjoint r U (QRegister.singleton u)
      (QRegister.disjoint_iff.mpr fun j i e ↦ by
        fin_cases i
        exact h j (congrArg Fin.val e))
          (compProj 0)
    exact conj_comm_selA (r.embedUnitary U)⁻¹.1 A (r.embedUnitary U).1 P (unitary_inv_comm
        (r.embedUnitary U) P cU) hA cU
  exact cConj rSpeciesSwap50Layout _
    (fun j hv ↦
        by
          have _ :=
             j.isLt
          rw [rSp50_eq_fn_w0, val_speciesSwap50WireFn] at hv
          split_ifs at hv <;>
             omega)
    (cConj rMux27Layout _
      (fun j hv ↦
          by
            have _ :=
               j.isLt
            rw [rMux27_eq_fn_w0, val_mux27WireFn] at hv
            split_ifs at hv <;> omega)
      (cConj rPKinLayout _ (fun j hv ↦ by
        have _ := j.isLt
        rw [val_rPKinLayout] at hv
        omega)
        (IsPhaseDiag.comm_basisOutcomeProjector_zero uKinMid2m1_isPhaseDiag_layout
            (QRegister.singleton u))))
theorem uKinIdeal2m1_comm_pBit0_wIsFine : uKinIdeal2m1UselLayout.1 * pBit0 wIsFine =
    pBit0 wIsFine * uKinIdeal2m1UselLayout.1 :=
  uKinIdeal2m1_comm_proj0 wIsFine
    (Or.inl (by dsimp [wIsFine]; rw [val_rOut40Layout]; dsimp; omega))
end QuantumComputation.Specs.PhotochemistrySolution.Kinetic664Stage4
end

noncomputable section
open Operator QProg Matrix Circuit Qubit PrimitiveGate
  QuantumComputation.Specs.PhotochemistrySolution.KetSupport
  QuantumComputation.Specs.PhotochemistrySolution
  QuantumComputation.Specs.PhotochemistrySolution.SelectCompactAnc
  QuantumComputation.Specs.PhotochemistrySolution.RouterSelectWiringA
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
open QuantumComputation.Specs.PhotochemistrySolution.RouterSelectWiringB
  QuantumComputation.Specs.PhotochemistrySolution.ProviderCore
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB (ket)
attribute [local irreducible]
    QuantumComputation.Specs.PhotochemistrySolution.SelectCompactAnc.ancWOfScr
namespace QuantumComputation.Specs.PhotochemistrySolution.PotSelectWiring
open QuantumComputation.Specs PhotochemistrySolution.SplitRouter47_187
  PhotochemistrySolution.SelectOracles PhotochemistrySolution.Stage12Compact
open PhotochemistrySolution.ZeroNEremSpec PhotochemistrySolution.SelectSandwich
  PhotochemistrySolution.XMeasChunkQromUnldA
open _root_.DynamicCircuit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt hiding bit_cases
  eval_seq_mulVec ket ket_CNOT ket_TOFF ket_X ket_projector_one ket_projector_zero matrix_ext_ket
  qAssign_obs_map_val
attribute [local irreducible] systemQubits_frozen PgBase.phaseGradientState phaseFlipUnitary
theorem wNoHad_mulVec_ket {wIn : ℕ} {decodeCoin : Fin (2 ^ 41) → ZeroNEremSector}
    (o1 : Stage1ZeroNEremLayout wIn decodeCoin) {β : BitAssignment dLayout} (hScr : CleanScr β)
    (c : Fin (2 ^ 41)) (z : BitAssignment 41) :
    (wNoHad o1.uLocal).1.mulVec (ket (routedStage0 β c z)) = ket (routedKet decodeCoin β c z)
    := by
  have : NeZero (2 ^ dLayout) := ⟨pow_ne_zero dLayout two_ne_zero⟩
  let δ₀ := routedStage0 β c z
  have hc (k : Fin 41) : δ₀ (rOuter41Layout k) = if c.val.testBit k.val then 1 else 0 :=
    (congrArg δ₀ (Fin.ext (by rw [val_rOuter41Layout, val_rLcu82Layout]))).trans
      ((DynCircExt.writeReg_apply_reg β rLcu82Layout _ ⟨k.val, fin41_lt_mLayout k⟩).trans
        (pack82_apply_lt c z k))
  have hout (j : Fin 40) : δ₀ (rOut40Layout j) = 0 :=
    (DynCircExt.writeReg_apply_of_not_mem β rLcu82Layout _ _ fun ⟨_, e⟩ ↦
      absurd (congrArg Fin.val e) (by
        rw [val_rLcu82Layout, val_rOut40Layout]
        omega)).trans
      ((show rOut40Layout j = rScrLayout ⟨65 + j.val,
          by
            dsimp [scrLLayout]
            omega⟩ from rfl) ▸ hScr _)
  have h1493 (k : Fin 1493) : δ₀ (rScrCompact1493 k) = 0 :=
      (rScrCompact1493_sub_scr k).elim fun m hm ↦
      (DynCircExt.writeReg_apply_of_not_mem β rLcu82Layout _ _ fun ⟨_, e⟩ ↦
          absurd (congrArg Fin.val e)
          (by
            rw [val_rLcu82Layout, hm, val_rScrLayout]
            dsimp [scrLLayout]
            omega)).trans
              (hm ▸ hScr m)
  obtain ⟨hVN, _, hVE, _⟩ := validRouter_stage1 (decodeCoin := decodeCoin) hScr c z
  unfold wNoHad
  rw [Submonoid.coe_mul, Submonoid.coe_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    o1.ket_of_clean c δ₀ hc hout h1493]
  change (uRouterSwapConj rElecLayout).1.mulVec
    ((uRouterSwapConj rNucLayout).1.mulVec (ket (routedStage1 decodeCoin β c z))) = _
  rw [uRouterSwapConj_ket_eq rNucLayout hVN]
  exact uRouterSwapConj_ket_eq rElecLayout hVE

theorem wNoHad_inv_mulVec_ket {wIn : ℕ} {decodeCoin : Fin (2 ^ 41) → ZeroNEremSector}
    (o1 : Stage1ZeroNEremLayout wIn decodeCoin) {β : BitAssignment dLayout} (hScr : CleanScr β)
    (c : Fin (2 ^ 41)) (z : BitAssignment 41) :
    ((wNoHad o1.uLocal)⁻¹).1.mulVec (ket (routedKet decodeCoin β c z)) =
    ket (routedStage0 β c z) :=
    inv_mulVec_of_fwd (wNoHad o1.uLocal) (wNoHad_mulVec_ket o1 hScr c z)
theorem comm_pScr_uHad82 : Commute uHad82Layout.1 pScr := by
  have : NeZero (2 ^ dLayout) := ⟨pow_ne_zero _ two_ne_zero⟩
  refine hadamardRegSym_comm_disjoint (Var :=
      Unit) wHasN1 82 rLcu82Layout hDisjHad82_layout rScrLayout
    (QRegister.disjoint_iff.mpr fun i j e ↦ ?_) (compProj 0)
  obtain ⟨hj, hv⟩ : j.val < 1565 ∧ (rLcu82Layout ⟨i.1, i.2⟩).val = (rScrLayout j).val :=
      ⟨j.2, congrArg Fin.val e⟩
  rw [val_rLcu82Layout, val_rScrLayout] at hv
  dsimp only at hv
  omega

theorem routedStage0_self (β : BitAssignment dLayout) : routedStage0 β (outerCoinOf82 (fun i ↦
    β (rLcu82Layout i))) (innerBitsOf82 (fun i ↦ β (rLcu82Layout i))) = β := by
  unfold routedStage0
  rw [pack82_left_inv]
  exact writeReg_self rLcu82Layout β
theorem routedKet_workInner {decodeCoin : Fin (2 ^ 41) → ZeroNEremSector}
    {β : BitAssignment dLayout}
    (hScr : CleanScr β) (c : Fin (2 ^ 41)) (z : BitAssignment 41) (k : Fin 521) :
    routedKet decodeCoin β c z (rWorkInnerLayout k) = 0 :=
  ((validRouter_stage1 (decodeCoin := decodeCoin) hScr c z).2.2.2.1 (rWorkInnerLayout k)
    (by
      rw [val_rWorkInnerLayout]
      omega)).trans
    (stage1_scr_zero hScr c z (by
      rw [val_rWorkInnerLayout]
      omega))
theorem routedKet_out40 {decodeCoin : Fin (2 ^ 41) → ZeroNEremSector} {β : BitAssignment dLayout}
    (hScr : CleanScr β) (c : Fin (2 ^ 41)) (z : BitAssignment 41) (j : Fin 40) :
    routedKet decodeCoin β c z (rOut40Layout j) = outMaskBits40 (decodeCoin c) j :=
  ((validRouter_stage1 (decodeCoin := decodeCoin) hScr c z).2.2.2.1 (rOut40Layout j)
    (by
      rw [val_rOut40Layout]
      omega)).trans (DynCircExt.writeReg_apply_reg _ rOut40Layout _
        j)
theorem routedKet_sector_flags {decodeCoin : Fin (2 ^ 41) → ZeroNEremSector}
    {β : BitAssignment dLayout} (hScr : CleanScr β)
    (c : Fin (2 ^ 41)) (z : BitAssignment 41) :
    let γ := routedKet decodeCoin β c z
    (γ wIsFine = 0 ∧ γ wIsKin = 0) ∨ (γ wIsFine = 1 ∧ γ wIsKin = 0) ∨ (γ wIsFine = 0 ∧ γ wIsKin = 1)
        := by
  let γ := routedKet decodeCoin β c z
  have chk (hN1 hN2 : Bool) (n1 n2 : ℕ) (hE1 hE2 : Bool) (e1 e2 : ℕ)
      (isScreen isPot isKin isNN : Bool)
      (sp1 aux2 : ℕ) (heq : zeroNEremOutMask (decodeCoin c) =
        packOut40ZeroNErem hN1 hN2 n1 n2 hE1 hE2 e1 e2 isScreen isPot isKin isNN sp1 aux2)
      (hB : n1 < 64 ∧ n2 < 64 ∧ e1 < 256 ∧ e2 < 256 := by omega)
      (hPK : ¬(isPot = true ∧ isKin = true) := by decide) :
      (γ wIsFine = 0 ∧ γ wIsKin = 0) ∨ (γ wIsFine = 1 ∧ γ wIsKin = 0) ∨ (γ wIsFine = 0 ∧ γ wIsKin =
          1) := by
    have F :=
        packOut40ZeroNErem_fields hN1 hN2 n1 n2 hE1 hE2 e1 e2 isScreen isPot isKin isNN sp1 aux2
      hB.1 hB.2.1 hB.2.2.1 hB.2.2.2 γ fun j ↦ (routedKet_out40 hScr c z j).trans
        (by
          dsimp [outMaskBits40]
          rw [heq])
    rw [F.2.2.2.2.2.2.2.2.2.1, F.2.2.2.2.2.2.2.2.2.2.1]
    cases isPot <;> cases isKin <;> simp at hPK ⊢
  match hs : decodeCoin c with
  | .idle =>
      exact chk false false 0 0 false false 0 0 false false false false 0 0
        (congrArg zeroNEremOutMask hs)
  | .ee n1 e1 e2 =>
      exact chk true false n1.val 0 true true e1.val e2.val true true false false (nucSpecies
          n1).val 0
        (congrArg zeroNEremOutMask hs)
  | .nn n1 n2 e1 =>
      exact chk true true n1.val n2.val true false e1.val 0 true true false true (nucSpecies n1).val
        (nucSpecies n2).val (congrArg zeroNEremOutMask hs)
  | .en n1 e1 =>
      exact chk true false n1.val 0 true false e1.val 0 false true false false (nucSpecies n1).val 0
        (congrArg zeroNEremOutMask hs)
  | .kin i ax =>
      have _ := i.isLt
      exact (em (i.val < 47)).elim (fun hi ↦
          chk true false i.val 0 false false 0 0 false false true false 0 ax.val
          (by simp [hs, zeroNEremOutMask, hi]))
        (fun hi ↦ chk false false 0 0 true false (i.val - 47) 0 false false true false 0 ax.val
          (by simp [hs, zeroNEremOutMask, hi]))

end QuantumComputation.Specs.PhotochemistrySolution.PotSelectWiring

namespace QuantumComputation.Specs.PhotochemistrySolution.Kinetic664Stage4
open PhotochemistrySolution.Kinetic664 PhotochemistrySolution.SubspaceMbu
  PhotochemistrySolution.SelectQft8GidneyStg3 PhotochemistrySolution.PotSelectWiring
open PhotochemistrySolution.DynQromUncompA PhotochemistrySolution.Stage4Kin14Scb
  PhotochemistrySolution.QubitizationWalkSem PhotochemistrySolution.SelectKin526OneWrap
  PhotochemistrySolution.SelectStructuredCB
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SelectFastQft8Gidney hiding
  unitary_inv_comm
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB (matrix_ext_ket)
attribute [local reducible] totDimCompactGen
attribute [local irreducible] SpecDefs.systemQubits_frozen
    bSpeciesSwap50 Stage4KinFull.bAxisMux27 abpKin14Usel abpKin15SqFree2m1Usel abpKin15SqFree2m1Csel
theorem uKinIdeal2m1Usel_fix_pK0 :
    uKinIdeal2m1UselLayout.1 *
      (pBit0 wIsKin * pBit0 (rWorkInnerLayout ⟨22, fin22_lt_521⟩)) =
    pBit0 wIsKin * pBit0 (rWorkInnerLayout ⟨22, fin22_lt_521⟩) := by
  let w22 := rWorkInnerLayout ⟨22, fin22_lt_521⟩
  let P := pBit0 wIsKin * pBit0 w22
  let Qid := qft8Stg3IdealU scrWLayout rPKinLayout
  have hMidP : uKinMid2m1UselLayout.1 * P = P := matrix_ext_ket fun δ ↦ by
    dsimp only [P, pBit0]
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, SelectRefl.ket_basisOutcomeProjector_zero]
    by_cases h22 : ∀ i : Fin 1, δ ((QRegister.singleton w22) i) = 0
    · rw [ifPosSqf h22, PhotochemistrySolution.SelectRefl.ket_basisOutcomeProjector_zero]
      by_cases hK : ∀ i : Fin 1, δ ((QRegister.singleton wIsKin) i) = 0
      · rw [ifPosSqf hK, uKinMid2m1_isPhaseDiag_layout δ, kin2m1OutBit_eq_fn,
          show δ (rKin226Layout wOutKin226) = 0 from (Fin.ext (by
            change (kin226WireFn wOutKin226).val = w22.val
            rw [val_kin226WireFn, val_rWorkInnerLayout]
            dsimp [wOutKin226, finMod]) : rKin226Layout wOutKin226 = w22) ▸ h22 0,
          show δ (rKin226Layout wIsKin226) = 0 from (Fin.ext (by
            change (kin226WireFn wIsKin226).val = wIsKin.val
            rw [val_kin226WireFn]
            dsimp only [wIsKin]
            rw [val_rOut40Layout]
            dsimp [wIsKin226, finMod]) : rKin226Layout wIsKin226 = wIsKin) ▸ hK 0,
          zero_mul, add_zero, bitSign_zero, one_smul]
      · rw [ifNegSqf hK, Matrix.mulVec_zero]
    · rw [ifNegSqf h22, Matrix.mulVec_zero, Matrix.mulVec_zero]
  have cDisj {k} (rk : QRegister k dLayout) (U : Operator.Unitary (2 ^ k))
      (hr : ∀ j : Fin k, (rk j).val ≠ 5749 ∧ (rk j).val ≠ 6105) :
      (rk.embedUnitary U).1 * P = P * (rk.embedUnitary U).1 :=
    comm_mul _ _ _
      (embedUnitary_comm_of_disjoint rk _ _ (QRegister.disjoint_iff.mpr fun j i e ↦ by
        fin_cases i
        exact absurd (congrArg Fin.val e : (rk j).val = wIsKin.val)
            (hr j |> fun _ ↦ by
          dsimp [wIsKin]
          rw [val_rOut40Layout]
          dsimp
          omega)) _)
      (embedUnitary_comm_of_disjoint rk _ _ (QRegister.disjoint_iff.mpr fun j i e ↦ by
        fin_cases i
        exact absurd (congrArg Fin.val e : (rk j).val = w22.val) (hr j |> fun _ ↦ by
          dsimp only [w22]
          rw [val_rWorkInnerLayout]
          dsimp
          omega)) _)
  exact conj_fix_proj (uSpeciesSwap50Layout⁻¹).1 uSpeciesSwap50Layout.1
      uKinCoreIdeal2m1UselLayout.1 P
    (congrArg Subtype.val (inv_mul_cancel uSpeciesSwap50Layout))
    (cDisj rSpeciesSwap50Layout _ fun ⟨j, hj⟩ ↦ by
      rw [rSp50_eq_fn_w0, val_speciesSwap50WireFn]
      split_ifs <;> omega)
    (conj_fix_proj (uMux27Layout⁻¹).1 uMux27Layout.1 (Qid⁻¹ * uKinMid2m1UselLayout * Qid).1 P
      (congrArg Subtype.val (inv_mul_cancel uMux27Layout))
      (cDisj rMux27Layout _ fun ⟨j, hj⟩ ↦
          by
            rw [rMux27_eq_fn_w0, val_mux27WireFn]
            split_ifs <;> omega)
      (conj_fix_proj (Qid⁻¹).1 Qid.1 uKinMid2m1UselLayout.1 P (congrArg Subtype.val
          (inv_mul_cancel Qid))
        (cDisj rPKinLayout _ fun ⟨j, hj⟩ ↦ by
          rw [val_rPKinLayout]
          omega) hMidP))

theorem uAlignedKinIdeal2m1_fix (γ : BitAssignment dLayout) (hk0 : γ wIsKin = 0)
    (hw22 : γ (rWorkInnerLayout ⟨22, fin22_lt_521⟩) = 0) :
    uAlignedKinIdeal2m1Layout.1.mulVec (ket γ) = ket γ := by
  let ηk := pKinAlign0.fwdBits γ
  let w22 := rWorkInnerLayout ⟨22, fin22_lt_521⟩
  have hFk : uKinAlign0Layout.1.mulVec (ket γ) = ket ηk := fwdCirc_mulVec_ket pKinAlign0 γ
  unfold uAlignedKinIdeal2m1Layout
  rw [Submonoid.coe_mul, Submonoid.coe_mul, uKinAlign0Layout_inv_eq, ← Matrix.mulVec_mulVec,
      ← Matrix.mulVec_mulVec, hFk,
    show uKinIdeal2m1UselLayout.1.mulVec (ket ηk) = ket ηk by
      rw [← show (pBit0 wIsKin * pBit0 w22).mulVec (ket ηk) = ket ηk by
        rw [← Matrix.mulVec_mulVec, pBit0_ket ((fwdBits_not_target targetsIn_pKinAlign0 γ
            (by
              rw [val_rWorkInnerLayout]
              dsimp only
              omega)).trans hw22),
          pBit0_ket ((fwdBits_not_target targetsIn_pKinAlign0 γ
            (by
              dsimp only [wIsKin]
              rw [val_rOut40Layout]
              dsimp only
              omega)).trans
                hk0)],
        Matrix.mulVec_mulVec, uKinIdeal2m1Usel_fix_pK0],
    ← hFk, Matrix.mulVec_mulVec, ← Submonoid.coe_mul, uKinAlign0Layout_sq_one, Submonoid.coe_one,
        Matrix.one_mulVec]

end QuantumComputation.Specs.PhotochemistrySolution.Kinetic664Stage4
end
end
end

end ScopedLocalHelpers
end
