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

public import QuantumComputationSpecs.Algorithms.P450DFTHCData
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.DihedralWalkQPE46687
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.TailShiftWindow46847
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.TailShiftThreeGearA

@[expose] public section

/-!
# Tail-Shifted Three-Gear Sub-Clock Shift Primitives

Provides parametric Toffoli-free sub-clock shift circuits (`ctrlAddMod4LocalDyn`,
`ctrlAddMod8Odd17LocalDyn`, `ctrlAddMod8Odd35LocalDyn`, `tailShiftClockPermDyn`),
`TailShiftMode` (`.mod4Add1`, `.mod4Add3`, `.mod8Add1`, `.mod8Add3`), and `TailShiftParams`.
-/

namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.TailShiftThreeGear
open QuantumComputation.Specs QuantumComputation.Specs.P450

open Operator QProg Matrix HermitianMat Circuit Real QuantumComputation.Specs
open QuantumComputation.Specs.P450 BlockEncodingCore
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.WalkQPEBridge hiding
  rActLoc rActLoc_disjoint_rScrLoc rCatInAct rCatLoc rQPEInAct rQPEInAct_disjoint_rWalkCatInAct
  rQPEInAnc rQPELoc rQPELoc_disjoint_rScrLoc rQPELoc_disjoint_rWalkCatLoc rScrLoc rScrUbLoc
  rWalkCatInAct rWalkCatLoc rWalkCatLoc_disjoint_rScrLoc
open WalkQPEBridgeXMeas hiding image_rFullZeroLoc rFullZeroLoc
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.WalkQPEFlexBridge hiding
  cleanRealizesSet_of_rScrUbLoc cleanRealizes_rScrLoc_of_sub
open TopIntegrationBridge Cat11CompactPhase2Bridge
open DihedralWalkQPE BlockEncodingCircuit
open DihedralWalkQPE.BlockReflection (affineFoldVal)
open DihedralWalkQPE.MultiGearQPE (combARem)
open TwoGearBox hiding m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.TwoGearQPEPhase5
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.Comparators hiding CleanRealizes
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.Comparators.ComparatorProofs
open scoped Matrix BigOperators Matrix.Norms.L2Operator

/-! ## Section 3: Parametric `TOFF = 0` Sub-Clock Shift (`tailShiftClockPermDyn`) -/

/-- Local `4`-wire controlled `+1` (`addThree = false`) or `+3` (`addThree = true`) modulo `4`
adder (`4 T`, `0 TOFF`, wire `0` = flag, wires `1..2` = target, wire `3` = clean ancilla). -/
def ctrlAddMod4LocalDyn {Var : Type} (v : Var) (addThree : Bool) : DynamicCircuit Var 4 :=
  if addThree then
    .seq (.circuit (Circuit.CNOT 0 1 (by decide)))
      (DynamicCircuit.jonesToffoli v 0 1 2 3 (by decide) (by decide) (by decide) (by decide))
  else
    .seq (DynamicCircuit.jonesToffoli v 0 1 2 3 (by decide) (by decide) (by decide) (by decide))
      (.circuit (Circuit.CNOT 0 1 (by decide)))
@[simp] theorem ctrlAddMod4LocalDyn_count_toff {Var : Type} (v : Var) (addThree : Bool) :
    (ctrlAddMod4LocalDyn v addThree).count .TOFF = 0 := by
  cases addThree <;> simp [ctrlAddMod4LocalDyn, DynamicCircuit.jonesToffoli, Circuit.CNOT]
@[simp] theorem ctrlAddMod4LocalDyn_count_t {Var : Type} (v : Var) (addThree : Bool) :
    (ctrlAddMod4LocalDyn v addThree).count .T = 4 := by
  cases addThree <;> simp [ctrlAddMod4LocalDyn, DynamicCircuit.jonesToffoli, Circuit.CNOT]

/-- `CleanRealizes` for `ctrlAddMod4LocalDyn` on `(block 0 3, block 3 1)`. -/
theorem cleanRealizes_ctrlAddMod4LocalDyn {Var : Type} [Fintype Var] [DecidableEq Var]
    (v : Var) (addThree : Bool) :
    Comparators.CleanRealizes v (QRegister.block 0 3 (by decide))
      (QRegister.block 3 1 (by decide))
      (muxBitLocalUnitary 1 (permutationUnitary
        (if addThree then addConstModPerm 2 3 1 (by decide)
         else addConstModPerm 2 1 3 (by decide))))
      (ctrlAddMod4LocalDyn v addThree) := by
  let rAct : QRegister 3 4 := QRegister.block 0 3 (by decide)
  let rScr : QRegister 1 4 := QRegister.block 3 1 (by decide)
  have himg : rScr.image = ({3} : Finset (Wire 4)) := by decide
  apply CleanRealizesWires.toCleanRealizes
  rw [himg]
  have hJT := CleanRealizesWires.jonesToffoli (Var := Var) (v := v) (S := ({3} : Finset (Wire 4)))
    0 1 2 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
  have hCX := CleanRealizesWires.circuit v ({3} : Finset (Wire 4))
    (Circuit.CNOT 0 1 (by decide)) (by decide) (by decide)
  have himgDisj : Disjoint rAct.image ({3} : Finset (Wire 4)) := by decide
  have hr : (QRegister.block 0 3 (by decide) : QRegister 3 4) =
      (QRegister.singleton 0).concat (QRegister.block 1 2 (by decide)) (by decide) := by
    ext i
    fin_cases i <;> rfl
  have hstep : CleanRealizesWires v ({3} : Finset (Wire 4))
      (if addThree then
        (Circuit.TOFF 0 1 2 (by decide) (by decide) (by decide)).eval *
          (Circuit.CNOT 0 1 (by decide)).eval
       else
        (Circuit.CNOT 0 1 (by decide)).eval *
          (Circuit.TOFF 0 1 2 (by decide) (by decide) (by decide)).eval)
      (ctrlAddMod4LocalDyn v addThree) := by
    cases addThree
    · exact hJT.seq hCX
    · exact hCX.seq hJT
  refine hstep.congr_unitary ?_
    (embedMatrix_comm_zeroProjOn_of_disjoint rAct _ himgDisj _)
  apply congrArg (· * zeroProjOn ({3} : Finset (Wire 4)))
  refine matrix_ext_ket fun β ↦ ?_
  have hβ : β = ![β 0, β 1, β 2, β 3] := funext fun i ↦ by fin_cases i <;> rfl
  rw [hβ]
  cases addThree <;> rcases bit_cases (β 0) with b0 | b0 <;>
    rcases bit_cases (β 1) with b1 | b1 <;> rcases bit_cases (β 2) with b2 | b2 <;>
    rcases bit_cases (β 3) with b3 | b3 <;> rw [b0, b1, b2, b3] <;>
    simp only [↓reduceIte, Bool.false_eq_true, Submonoid.coe_mul, ← Matrix.mulVec_mulVec,
      ket_TOFF, ket_CNOT]
  all_goals
    rw [hr, embedUnitary_muxPredLocalUnitary, muxPredUnitary_mulVec_ket]
    simp only [localIdx_val_one]
    try simp only [Submonoid.coe_one, QRegister.embedUnitary_one, Matrix.one_mulVec]
    try simp only [embedUnitary_permutationUnitary_mulVec_ket]
    congr 1
    ext i
    simp only [Function.update_apply, writeReg_block_apply, basisBits_eq_div_mod]
    fin_cases i <;> decide

/-- Local `6`-wire controlled `+1` (`addSeven = false`) or `+7` (`addSeven = true`) modulo `8`
adder (`8 T`, `0 TOFF`, wire `0` = flag, wires `1..3` = target, wires `4..5` = clean ancillas). -/
def ctrlAddMod8Odd17LocalDyn {Var : Type} (v : Var) (addSeven : Bool) : DynamicCircuit Var 6 :=
  if addSeven then
    .seq (.circuit (Circuit.CNOT 0 1 (by decide)))
      (andSandwich v 0 1 4 (by decide) (by decide) (by decide)
        (.seq (.circuit (Circuit.CNOT 4 2 (by decide)))
          (DynamicCircuit.jonesToffoli v 4 2 3 5
            (by decide) (by decide) (by decide) (by decide))))
  else
    .seq (andSandwich v 0 1 4 (by decide) (by decide) (by decide)
        (.seq
          (DynamicCircuit.jonesToffoli v 4 2 3 5
            (by decide) (by decide) (by decide) (by decide))
          (.circuit (Circuit.CNOT 4 2 (by decide)))))
      (.circuit (Circuit.CNOT 0 1 (by decide)))
@[simp] theorem ctrlAddMod8Odd17LocalDyn_count_toff {Var : Type} (v : Var) (addSeven : Bool) :
    (ctrlAddMod8Odd17LocalDyn v addSeven).count .TOFF = 0 := by
  cases addSeven <;> simp [ctrlAddMod8Odd17LocalDyn, DynamicCircuit.jonesToffoli, Circuit.CNOT]
@[simp] theorem ctrlAddMod8Odd17LocalDyn_count_t {Var : Type} (v : Var) (addSeven : Bool) :
    (ctrlAddMod8Odd17LocalDyn v addSeven).count .T = 8 := by
  cases addSeven <;> simp [ctrlAddMod8Odd17LocalDyn, DynamicCircuit.jonesToffoli, Circuit.CNOT]

/-- Local `6`-wire controlled `+3` (`addFive = false`) or `+5` (`addFive = true`) modulo `8`
adder (`8 T`, `0 TOFF`, wire `0` = flag, wires `1..3` = target, wires `4..5` = clean ancillas),
obtained from `ctrlAddMod8Odd17LocalDyn` via MSB `+4` (`CNOT 0 3`). -/
def ctrlAddMod8Odd35LocalDyn {Var : Type} (v : Var) (addFive : Bool) : DynamicCircuit Var 6 :=
  if addFive then
    .seq (.circuit (Circuit.CNOT 0 3 (by decide))) (ctrlAddMod8Odd17LocalDyn v false)
  else
    .seq (ctrlAddMod8Odd17LocalDyn v true) (.circuit (Circuit.CNOT 0 3 (by decide)))
@[simp] theorem ctrlAddMod8Odd35LocalDyn_count_toff {Var : Type} (v : Var) (addFive : Bool) :
    (ctrlAddMod8Odd35LocalDyn v addFive).count .TOFF = 0 := by
  cases addFive <;> simp [ctrlAddMod8Odd35LocalDyn, Circuit.CNOT]
@[simp] theorem ctrlAddMod8Odd35LocalDyn_count_t {Var : Type} (v : Var) (addFive : Bool) :
    (ctrlAddMod8Odd35LocalDyn v addFive).count .T = 8 := by
  cases addFive <;> simp [ctrlAddMod8Odd35LocalDyn, Circuit.CNOT]
theorem cnot0_sq6 (tgt : Wire 6) (h0t : (0 : Wire 6) ≠ tgt) :
    (Circuit.CNOT 0 tgt h0t).eval * (Circuit.CNOT 0 tgt h0t).eval = 1 := by
  refine Subtype.ext (matrix_ext_ket fun β ↦ ?_)
  rw [Submonoid.coe_mul, ← Matrix.mulVec_mulVec, ket_CNOT, ket_CNOT, Submonoid.coe_one,
    Matrix.one_mulVec]
  congr 1
  ext i
  by_cases hi : i = tgt <;>
    simp [hi, h0t, add_assoc, CharTwo.add_self_eq_zero]
theorem cnot0_emb6 (t : Wire 4) (h4 : 0 ≠ t) (w : Wire 6) (h6 : 0 ≠ w)
    (hw : w = (QRegister.block 0 4 (by decide)) t) :
    (Circuit.CNOT 0 w h6).eval =
      (QRegister.block 0 4 (by decide)).embedUnitary (Circuit.CNOT 0 t h4).eval := by
  rw [← Circuit.eval_onRegister]
  dsimp only [Circuit.CNOT, Circuit.onRegister]
  congr 2
  ext i
  fin_cases i
  · rfl
  · exact congrArg Fin.val hw
theorem ketCnot01 (x0 x1 x2 x3 x4 x5 : ZMod 2) :
    (Circuit.CNOT (0 : Wire 6) 1 (by decide)).eval.1 *ᵥ ket ![x0, x1, x2, x3, x4, x5] =
      ket ![x0, x1 + x0, x2, x3, x4, x5] :=
  (ket_CNOT ..).trans (congrArg ket (funext fun i ↦ by fin_cases i <;> rfl))
theorem ketCnot42 (x0 x1 x2 x3 x4 x5 : ZMod 2) :
    (Circuit.CNOT (4 : Wire 6) 2 (by decide)).eval.1 *ᵥ ket ![x0, x1, x2, x3, x4, x5] =
      ket ![x0, x1, x2 + x4, x3, x4, x5] :=
  (ket_CNOT ..).trans (congrArg ket (funext fun i ↦ by fin_cases i <;> rfl))
theorem ketToff423 (x0 x1 x2 x3 x4 x5 : ZMod 2) :
    (Circuit.TOFF (4 : Wire 6) 2 3 (by decide) (by decide) (by decide)).eval.1 *ᵥ
        ket ![x0, x1, x2, x3, x4, x5] = ket ![x0, x1, x2, x3 + x4 * x2, x4, x5] :=
  (ket_TOFF ..).trans (congrArg ket (funext fun i ↦ by fin_cases i <;> rfl))
theorem ketToff014 (x0 x1 x2 x3 x4 x5 : ZMod 2) :
    (Circuit.TOFF (0 : Wire 6) 1 4 (by decide) (by decide) (by decide)).eval.1 *ᵥ
        ket ![x0, x1, x2, x3, x4, x5] = ket ![x0, x1, x2, x3, x4 + x0 * x1, x5] :=
  (ket_TOFF ..).trans (congrArg ket (funext fun i ↦ by fin_cases i <;> rfl))

/-- Shared `CleanRealizesWires` wrapper for a `6`-wire `andSandwich v 0 1 4` body realizing an
active `4`-wire unitary `V_loc` on `QRegister.block 0 4`. -/
theorem cleanRealizesWires_andSandwich014 {Var : Type} [Fintype Var] [DecidableEq Var]
    (v : Var) (V_loc : Unitary (2 ^ 4))
    {U_mid : Unitary (2 ^ 6)} {mid : DynamicCircuit Var 6}
    (hmid : CleanRealizesWires v ({5} : Finset (Wire 6)) U_mid mid)
    (hket : ∀ x0 x1 x2 x3 x5 : ZMod 2,
      (Circuit.TOFF (0 : Wire 6) 1 4 (by decide) (by decide) (by decide)).eval.1 *ᵥ
        (U_mid.1 *ᵥ
          ((Circuit.TOFF (0 : Wire 6) 1 4 (by decide) (by decide) (by decide)).eval.1 *ᵥ
            ket ![x0, x1, x2, x3, 0, x5])) =
      ((QRegister.block 0 4 (by decide)).embedUnitary V_loc).1 *ᵥ
        ket ![x0, x1, x2, x3, 0, x5]) :
    CleanRealizesWires v (insert 4 ({5} : Finset (Wire 6)))
      ((QRegister.block 0 4 (by decide)).embedUnitary V_loc)
      (andSandwich v 0 1 4 (by decide) (by decide) (by decide) mid) := by
  let rAct : QRegister 4 6 := QRegister.block 0 4 (by decide)
  let S5 : Finset (Wire 6) := {5}
  have hDisj4 : rAct.DisjointWires (QRegister.singleton 4) := by decide
  have himgDisj5 : Disjoint rAct.image S5 := by decide
  exact CleanRealizesWires.andSandwich (Var := Var) (v := v) (S := S5)
    0 1 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    hmid (W := rAct.embedUnitary V_loc)
    (by
      intro P₀ T_anc
      dsimp only [P₀, T_anc]
      rw [singleton_basisOutcomeProjector_zero_eq]
      apply matrix_ext_ket
      intro β
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, zeroProjOn_mulVec_ket]
      simp only [Finset.mem_singleton, forall_eq]
      by_cases hb4 : β 4 = 0
      · rw [ite_eq_left hb4]
        have hβ : β = ![β 0, β 1, β 2, β 3, 0, β 5] := by
          ext i
          fin_cases i <;> simp [hb4]
        rw [hβ]
        simp only [Submonoid.coe_mul, ← Matrix.mulVec_mulVec]
        exact hket (β 0) (β 1) (β 2) (β 3) (β 5)
      · rw [ite_eq_right hb4, Matrix.mulVec_zero, Matrix.mulVec_zero])
    (QRegister.embedMatrix_comm_basisOutcomeProjector_of_disjoint rAct _ hDisj4 V_loc.1 0)
    (embedMatrix_comm_zeroProjOn_of_disjoint rAct S5 himgDisj5 V_loc.1)
theorem block04_eq_concat :
    (QRegister.block 0 4 (by decide) : QRegister 4 6) =
      (QRegister.singleton 0).concat (QRegister.block 1 3 (by decide)) (by decide) := by
  ext i
  fin_cases i <;> rfl
theorem whole4_eq_concat :
    (QRegister.whole 4 : QRegister 4 4) =
      (QRegister.singleton 0).concat (QRegister.block 1 3 (by decide)) (by decide) := by
  ext i
  fin_cases i <;> rfl
theorem cleanRealizes_ctrlAddMod8Odd1LocalDyn {Var : Type} [Fintype Var] [DecidableEq Var]
    (v : Var) :
    Comparators.CleanRealizes v (QRegister.block 0 4 (by decide))
      (QRegister.block 4 2 (by decide))
      (muxBitLocalUnitary 1 (permutationUnitary (addConstModPerm 3 1 7 (by decide))))
      (ctrlAddMod8Odd17LocalDyn v false) := by
  let rAct : QRegister 4 6 := QRegister.block 0 4 (by decide)
  let S5 : Finset (Wire 6) := {5}
  let S45 : Finset (Wire 6) := insert (4 : Wire 6) S5
  have himg : (QRegister.block 4 2 (by decide) : QRegister 2 6).image = S45 := by decide
  apply CleanRealizesWires.toCleanRealizes
  rw [himg]
  have hJT := CleanRealizesWires.jonesToffoli (Var := Var) (v := v) (S := S5) 4 2 3 5
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
  have hCX42 := CleanRealizesWires.circuit v S5
    (Circuit.CNOT 4 2 (by decide)) (by decide) (by decide)
  have hCX01 := CleanRealizesWires.circuit v S45
    (Circuit.CNOT 0 1 (by decide)) (by simp [Circuit.CNOT]) (by decide)
  have himgDisj : Disjoint rAct.image S45 := by decide
  let U1 : Unitary (2 ^ 4) :=
    muxBitLocalUnitary 1 (permutationUnitary (addConstModPerm 3 1 7 (by decide)))
  let V_loc : Unitary (2 ^ 4) := (Circuit.CNOT 0 1 (by decide)).eval * U1
  have hU_eq : rAct.embedUnitary V_loc =
      (Circuit.CNOT (0 : Wire 6) 1 (by decide)).eval * rAct.embedUnitary U1 := by
    dsimp only [V_loc, rAct]
    rw [QRegister.embedUnitary_mul, ← cnot0_emb6 1 (by decide) 1 (by decide) rfl]
  have hbit0 (x0 x1 x2 x3 x4 x5 : ZMod 2) :
      bitNat (![x0, x1, x2, x3, x4, x5] ((QRegister.singleton 0) 0)) =
        if x0 = 1 then 1 else 0 := rfl
  have hSand := cleanRealizesWires_andSandwich014 v V_loc (hJT.seq hCX42) (by
    intro x0 x1 x2 x3 x5
    rw [hU_eq]
    rcases bit_cases x0 with b0 | b0 <;> rcases bit_cases x1 with b1 | b1 <;>
      rcases bit_cases x2 with b2 | b2 <;> rcases bit_cases x3 with b3 | b3 <;>
      rcases bit_cases x5 with b5 | b5 <;> rw [b0, b1, b2, b3, b5] <;>
      simp only [Submonoid.coe_mul, ← Matrix.mulVec_mulVec,
        ketCnot42, ketToff423, ketToff014]
    all_goals
      dsimp only [U1, rAct]
      rw [block04_eq_concat, embedUnitary_muxPredLocalUnitary, muxPredUnitary_mulVec_ket]
      simp only [localIdx_val_one, hbit0]
      try simp only [zero_ne_one, ↓reduceIte]
      try simp only [decide_true]
      try simp only [decide_false]
      try simp only [Bool.false_eq_true]
      simp only [↓reduceIte]
      try simp only [Submonoid.coe_one, QRegister.embedUnitary_one, Matrix.one_mulVec]
      try simp only [embedUnitary_permutationUnitary_mulVec_ket]
      simp only [ket_CNOT]
      apply congrArg ket
      ext i
      simp only [Function.update_apply, writeReg_block_apply, basisBits_eq_div_mod]
      fin_cases i <;> decide)
  dsimp only [ctrlAddMod8Odd17LocalDyn]
  refine (hSand.seq hCX01).congr_unitary ?_
    (embedMatrix_comm_zeroProjOn_of_disjoint rAct S45 himgDisj _)
  apply congrArg (· * zeroProjOn S45)
  refine congrArg Subtype.val ?_
  rw [hU_eq, ← mul_assoc, cnot0_sq6 1 (by decide), one_mul]
theorem cleanRealizes_ctrlAddMod8Odd7LocalDyn {Var : Type} [Fintype Var] [DecidableEq Var]
    (v : Var) :
    Comparators.CleanRealizes v (QRegister.block 0 4 (by decide))
      (QRegister.block 4 2 (by decide))
      (muxBitLocalUnitary 1 (permutationUnitary (addConstModPerm 3 7 1 (by decide))))
      (ctrlAddMod8Odd17LocalDyn v true) := by
  let rAct : QRegister 4 6 := QRegister.block 0 4 (by decide)
  let S5 : Finset (Wire 6) := {5}
  let S45 : Finset (Wire 6) := insert (4 : Wire 6) S5
  have himg : (QRegister.block 4 2 (by decide) : QRegister 2 6).image = S45 := by decide
  apply CleanRealizesWires.toCleanRealizes
  rw [himg]
  have hJT := CleanRealizesWires.jonesToffoli (Var := Var) (v := v) (S := S5) 4 2 3 5
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
  have hCX42 := CleanRealizesWires.circuit v S5
    (Circuit.CNOT 4 2 (by decide)) (by decide) (by decide)
  have hCX01 := CleanRealizesWires.circuit v S45
    (Circuit.CNOT 0 1 (by decide)) (by simp [Circuit.CNOT]) (by decide)
  have himgDisj : Disjoint rAct.image S45 := by decide
  let U7 : Unitary (2 ^ 4) :=
    muxBitLocalUnitary 1 (permutationUnitary (addConstModPerm 3 7 1 (by decide)))
  let V_loc : Unitary (2 ^ 4) := U7 * (Circuit.CNOT 0 1 (by decide)).eval
  have hU_eq : rAct.embedUnitary V_loc =
      rAct.embedUnitary U7 * (Circuit.CNOT (0 : Wire 6) 1 (by decide)).eval := by
    dsimp only [V_loc, rAct]
    rw [QRegister.embedUnitary_mul, ← cnot0_emb6 1 (by decide) 1 (by decide) rfl]
  have hbit0 (x0 x1 x2 x3 x4 x5 : ZMod 2) :
      bitNat (![x0, x1, x2, x3, x4, x5] ((QRegister.singleton 0) 0)) =
        if x0 = 1 then 1 else 0 := rfl
  have hSand := cleanRealizesWires_andSandwich014 v V_loc (hCX42.seq hJT) (by
    intro x0 x1 x2 x3 x5
    rw [hU_eq]
    rcases bit_cases x0 with b0 | b0 <;> rcases bit_cases x1 with b1 | b1 <;>
      rcases bit_cases x2 with b2 | b2 <;> rcases bit_cases x3 with b3 | b3 <;>
      rcases bit_cases x5 with b5 | b5 <;> rw [b0, b1, b2, b3, b5] <;>
      simp only [Submonoid.coe_mul, ← Matrix.mulVec_mulVec,
        ketCnot01, ketCnot42, ketToff423, ketToff014]
    all_goals
      dsimp only [U7, rAct]
      rw [block04_eq_concat, embedUnitary_muxPredLocalUnitary, muxPredUnitary_mulVec_ket]
      simp only [localIdx_val_one, hbit0]
      try simp only [zero_ne_one, ↓reduceIte]
      try simp only [decide_true]
      try simp only [decide_false]
      try simp only [Bool.false_eq_true]
      simp only [↓reduceIte]
      try simp only [Submonoid.coe_one, QRegister.embedUnitary_one, Matrix.one_mulVec]
      try simp only [embedUnitary_permutationUnitary_mulVec_ket]
      apply congrArg ket
      ext i
      try simp only [writeReg_block_apply, basisBits_eq_div_mod]
      fin_cases i <;> decide)
  dsimp only [ctrlAddMod8Odd17LocalDyn]
  refine (hCX01.seq hSand).congr_unitary ?_
    (embedMatrix_comm_zeroProjOn_of_disjoint rAct S45 himgDisj _)
  apply congrArg (· * zeroProjOn S45)
  refine congrArg Subtype.val ?_
  rw [hU_eq, mul_assoc, cnot0_sq6 1 (by decide), mul_one]

theorem muxAddMod8_cnot03_pre :
    muxBitLocalUnitary 1 (permutationUnitary (addConstModPerm 3 1 7 (by decide))) *
      (Circuit.CNOT (0 : Wire 4) 3 (by decide)).eval =
    muxBitLocalUnitary 1 (permutationUnitary (addConstModPerm 3 5 3 (by decide))) := by
  have hbit0 (x0 x1 x2 x3 : ZMod 2) :
      bitNat (![x0, x1, x2, x3] ((QRegister.singleton 0) 0)) =
        if x0 = 1 then 1 else 0 := rfl
  have hcnot03 (x0 x1 x2 x3 : ZMod 2) :
      (Circuit.CNOT (0 : Wire 4) 3 (by decide)).eval.1 *ᵥ ket ![x0, x1, x2, x3] =
        ket ![x0, x1, x2, x3 + x0] :=
    (ket_CNOT ..).trans (congrArg ket (funext fun i ↦ by fin_cases i <;> rfl))
  rw [← QRegister.whole_embedUnitary
      (muxBitLocalUnitary 1 (permutationUnitary (addConstModPerm 3 1 7 (by decide)))),
    ← QRegister.whole_embedUnitary
      (muxBitLocalUnitary 1 (permutationUnitary (addConstModPerm 3 5 3 (by decide))))]
  refine Subtype.ext (matrix_ext_ket fun β ↦ ?_)
  have hβ : β = ![β 0, β 1, β 2, β 3] := funext fun i ↦ by fin_cases i <;> rfl
  rw [hβ]
  rcases bit_cases (β 0) with b0 | b0 <;> rcases bit_cases (β 1) with b1 | b1 <;>
    rcases bit_cases (β 2) with b2 | b2 <;> rcases bit_cases (β 3) with b3 | b3 <;>
    rw [b0, b1, b2, b3]
  all_goals
    rw [Submonoid.coe_mul, ← Matrix.mulVec_mulVec, hcnot03, whole4_eq_concat,
      embedUnitary_muxPredLocalUnitary, muxPredUnitary_mulVec_ket,
      embedUnitary_muxPredLocalUnitary, muxPredUnitary_mulVec_ket]
    simp only [localIdx_val_one, hbit0]
    try simp only [zero_ne_one, ↓reduceIte]
    try simp only [decide_true]
    try simp only [decide_false]
    try simp only [Bool.false_eq_true]
    simp only [↓reduceIte]
    try simp only [Submonoid.coe_one, QRegister.embedUnitary_one, Matrix.one_mulVec]
    try simp only [embedUnitary_permutationUnitary_mulVec_ket]
    apply congrArg ket
    ext i
    try simp only [writeReg_block_apply, basisBits_eq_div_mod]
    fin_cases i <;> decide
theorem muxAddMod8_cnot03_post :
    (Circuit.CNOT (0 : Wire 4) 3 (by decide)).eval *
      muxBitLocalUnitary 1 (permutationUnitary (addConstModPerm 3 7 1 (by decide))) =
    muxBitLocalUnitary 1 (permutationUnitary (addConstModPerm 3 3 5 (by decide))) := by
  have hbit0 (x0 x1 x2 x3 : ZMod 2) :
      bitNat (![x0, x1, x2, x3] ((QRegister.singleton 0) 0)) =
        if x0 = 1 then 1 else 0 := rfl
  rw [← QRegister.whole_embedUnitary
      (muxBitLocalUnitary 1 (permutationUnitary (addConstModPerm 3 7 1 (by decide)))),
    ← QRegister.whole_embedUnitary
      (muxBitLocalUnitary 1 (permutationUnitary (addConstModPerm 3 3 5 (by decide))))]
  refine Subtype.ext (matrix_ext_ket fun β ↦ ?_)
  have hβ : β = ![β 0, β 1, β 2, β 3] := funext fun i ↦ by fin_cases i <;> rfl
  rw [hβ]
  rcases bit_cases (β 0) with b0 | b0 <;> rcases bit_cases (β 1) with b1 | b1 <;>
    rcases bit_cases (β 2) with b2 | b2 <;> rcases bit_cases (β 3) with b3 | b3 <;>
    rw [b0, b1, b2, b3]
  all_goals
    rw [Submonoid.coe_mul, ← Matrix.mulVec_mulVec, whole4_eq_concat,
      embedUnitary_muxPredLocalUnitary, muxPredUnitary_mulVec_ket,
      embedUnitary_muxPredLocalUnitary, muxPredUnitary_mulVec_ket]
    simp only [localIdx_val_one, hbit0]
    try simp only [zero_ne_one, ↓reduceIte]
    try simp only [decide_true]
    try simp only [decide_false]
    try simp only [Bool.false_eq_true]
    simp only [↓reduceIte]
    try simp only [Submonoid.coe_one, QRegister.embedUnitary_one, Matrix.one_mulVec]
    try simp only [embedUnitary_permutationUnitary_mulVec_ket]
    simp only [ket_CNOT]
    apply congrArg ket
    ext i
    simp only [Function.update_apply, writeReg_block_apply, basisBits_eq_div_mod]
    fin_cases i <;> decide
theorem cleanRealizes_cnot03_6 {Var : Type} [Fintype Var] [DecidableEq Var] (v : Var) :
    Comparators.CleanRealizes v (QRegister.block 0 4 (by decide))
      (QRegister.block 4 2 (by decide))
      (Circuit.CNOT (0 : Wire 4) 3 (by decide)).eval
      (.circuit (Circuit.CNOT (0 : Wire 6) 3 (by decide))) := by
  have : NeZero (2 ^ 6) := ⟨by decide⟩
  have hc : (Circuit.CNOT (0 : Wire 4) 3 (by decide)).onRegister
      (QRegister.block 0 4 (by decide)) = Circuit.CNOT (0 : Wire 6) 3 (by decide) := by
    dsimp only [Circuit.CNOT, Circuit.onRegister]
    congr 2
    ext i
    fin_cases i <;> rfl
  rw [← hc]
  exact CleanDyn.CleanRealizes.circuit v
    (QRegister.block 0 4 (by decide)) (QRegister.block 4 2 (by decide)) (by decide)
    (Circuit.CNOT (0 : Wire 4) 3 (by decide)) rfl
theorem cleanRealizes_ctrlAddMod8Odd3LocalDyn {Var : Type} [Fintype Var] [DecidableEq Var]
    (v : Var) :
    Comparators.CleanRealizes v (QRegister.block 0 4 (by decide))
      (QRegister.block 4 2 (by decide))
      (muxBitLocalUnitary 1 (permutationUnitary (addConstModPerm 3 3 5 (by decide))))
      (ctrlAddMod8Odd35LocalDyn v false) := by
  have : NeZero (2 ^ 6) := ⟨by decide⟩
  exact CleanDyn.CleanRealizes.congr_unitary
    (CleanDyn.CleanRealizes.seq (cleanRealizes_ctrlAddMod8Odd7LocalDyn v)
      (cleanRealizes_cnot03_6 v))
    muxAddMod8_cnot03_post
theorem cleanRealizes_ctrlAddMod8Odd5LocalDyn {Var : Type} [Fintype Var] [DecidableEq Var]
    (v : Var) :
    Comparators.CleanRealizes v (QRegister.block 0 4 (by decide))
      (QRegister.block 4 2 (by decide))
      (muxBitLocalUnitary 1 (permutationUnitary (addConstModPerm 3 5 3 (by decide))))
      (ctrlAddMod8Odd35LocalDyn v true) := by
  have : NeZero (2 ^ 6) := ⟨by decide⟩
  exact CleanDyn.CleanRealizes.congr_unitary
    (CleanDyn.CleanRealizes.seq (cleanRealizes_cnot03_6 v)
      (cleanRealizes_ctrlAddMod8Odd1LocalDyn v))
    muxAddMod8_cnot03_pre

/-- Sub-clock conditional shift mode for Tail-Shifted Three-Gear QPE. -/
inductive TailShiftMode : Type where
  | mod4Add1
  | mod4Add3
  | mod8Add1
  | mod8Add3
  | mod8Add5
  deriving DecidableEq

/-- Width of the shifted sub-clock slice (`2` for `mod4*`, `3` for `mod8*`). -/
def TailShiftMode.wShift : TailShiftMode → ℕ
  | .mod4Add1 | .mod4Add3 => 2
  | .mod8Add1 | .mod8Add3 | .mod8Add5 => 3

/-- Forward shift constant (`1` or `3`). -/
def TailShiftMode.cFwd : TailShiftMode → ℕ
  | .mod4Add1 | .mod8Add1 => 1
  | .mod4Add3 | .mod8Add3 => 3
  | .mod8Add5 => 5

/-- Backward inverse shift constant (`3`, `1`, `7`, or `5`). -/
def TailShiftMode.cBwd : TailShiftMode → ℕ
  | .mod4Add1 => 3
  | .mod4Add3 => 1
  | .mod8Add1 => 7
  | .mod8Add3 => 5
  | .mod8Add5 => 3

/-- Clean body ancillas needed inside `withEqConstFlagDyn` (`1` for `mod4*`, `2` for `mod8*`). -/
def TailShiftMode.sBody : TailShiftMode → ℕ
  | .mod4Add1 | .mod4Add3 => 1
  | .mod8Add1 | .mod8Add3 | .mod8Add5 => 2

/-- `T`-gate count of the inner controlled modular adder (`4` for `mod4*`, `8` for `mod8*`). -/
def TailShiftMode.tBody : TailShiftMode → ℕ
  | .mod4Add1 | .mod4Add3 => 4
  | .mod8Add1 | .mod8Add3 | .mod8Add5 => 8
theorem TailShiftMode.cFwd_add_cBwd_mod (mode : TailShiftMode) :
    (mode.cFwd + mode.cBwd) % 2 ^ mode.wShift = 0 := by
  cases mode <;> decide
theorem TailShiftMode.cBwd_add_cFwd_mod (mode : TailShiftMode) :
    (mode.cBwd + mode.cFwd) % 2 ^ mode.wShift = 0 := by
  cases mode <;> decide

/-- Bundled arithmetic and gate-count parameters for Tail-Shifted Three-Gear QPE. -/
structure TailShiftParams (M m2 m1 nStd kTail tShift : ℕ) where
  mode : TailShiftMode
  mShift : ℕ
  hm1_le : m1 ≤ mShift
  hmShift_eq : mShift + mode.wShift = m2
  hm2_le14 : m2 ≤ 14
  hnStd_lo : 2 ^ (16 - m2 - 1) ≤ nStd
  hnStd_hi : nStd + 1 < 2 ^ (16 - m2)
  hFoldTop : affineFoldVal (16 - m2 - 1) (nStd + 1 - 2 ^ (16 - m2 - 1)) (nStd + 1) =
    2 ^ (16 - m2) - 1
  hFoldStd : ∀ q : Fin (2 ^ (16 - m2)), q.val ≤ nStd →
    affineFoldVal (16 - m2 - 1) (nStd + 1 - 2 ^ (16 - m2 - 1)) q.val < 2 ^ (16 - m2) - 1
  hM_eq : M + 1 = (nStd + 1) * 2 ^ m2 + kTail
  hkTail_pos : 1 ≤ kTail
  hkTail_lt : kTail < 2 ^ m2
  hqShift_eq : (mode.cFwd * 2 ^ (mShift - m1)) * 2 ^ m1 = 2 ^ m2 - kTail
  htShift : 2 * (eqConstTCount (16 - m2) (nStd + 1) + mode.tBody) ≤ tShift

/-- Conditional sub-clock shift value helper on `16 - m1` bits. -/
def tailShiftClockMapVal (bM _bC nStd q : ℕ) (x : ℕ) : ℕ :=
  let xc := x / 2 ^ bM
  let xm := x % 2 ^ bM
  (if xc = nStd + 1 then (xm + q) % 2 ^ bM else xm) + xc * 2 ^ bM
theorem tailShiftClockMapVal_lt {bM bC nStd q x : ℕ} (hx : x < 2 ^ (bM + bC)) :
    tailShiftClockMapVal bM bC nStd q x < 2 ^ (bM + bC) := by
  have hxc : x / 2 ^ bM < 2 ^ bC := Nat.div_lt_of_lt_mul (by rwa [← pow_add])
  have hxm : (if x / 2 ^ bM = nStd + 1 then (x % 2 ^ bM + q) % 2 ^ bM else x % 2 ^ bM) <
      2 ^ bM := by split_ifs <;> exact Nat.mod_lt _ (Nat.two_pow_pos bM)
  dsimp only [tailShiftClockMapVal]
  calc _ < 2 ^ bM + (x / 2 ^ bM) * 2 ^ bM := Nat.add_lt_add_right hxm _
    _ = (x / 2 ^ bM + 1) * 2 ^ bM := by ring
    _ ≤ 2 ^ bC * 2 ^ bM := Nat.mul_le_mul_right _ hxc
    _ = 2 ^ (bM + bC) := by rw [← pow_add, add_comm]
theorem tailShiftClockMapVal_cancel {bM bC nStd q₁ q₂ : ℕ}
    (hinv : (q₁ + q₂) % 2 ^ bM = 0) (x : ℕ) :
    tailShiftClockMapVal bM bC nStd q₂ (tailShiftClockMapVal bM bC nStd q₁ x) = x := by
  have hp := Nat.two_pow_pos bM
  let xm₁ := if x / 2 ^ bM = nStd + 1 then (x % 2 ^ bM + q₁) % 2 ^ bM else x % 2 ^ bM
  have hlt : xm₁ < 2 ^ bM := by
    dsimp [xm₁]
    split_ifs <;> exact Nat.mod_lt _ hp
  dsimp only [tailShiftClockMapVal]
  change (if (xm₁ + x / 2 ^ bM * 2 ^ bM) / 2 ^ bM = nStd + 1 then _ else _) + _ = x
  rw [Nat.add_mul_div_right _ _ hp, Nat.div_eq_of_lt hlt, zero_add,
    Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hlt]
  by_cases hc : x / 2 ^ bM = nStd + 1
  · dsimp only [xm₁]
    simp only [hc, ↓reduceIte]
    have hmod : ((x % 2 ^ bM + q₁) % 2 ^ bM + q₂) % 2 ^ bM = x % 2 ^ bM := by
      calc ((x % 2 ^ bM + q₁) % 2 ^ bM + q₂) % 2 ^ bM
          = (x % 2 ^ bM + (q₁ + q₂)) % 2 ^ bM := by rw [Nat.mod_add_mod, add_assoc]
        _ = x % 2 ^ bM := by simp only [Nat.add_mod, hinv, add_zero, Nat.mod_mod]
    rw [hmod, ← hc, mul_comm _ (2 ^ bM), Nat.mod_add_div]
  · dsimp only [xm₁]
    simp only [hc, ↓reduceIte, mul_comm _ (2 ^ bM), Nat.mod_add_div]
theorem TailShiftParams.hm1_lt_m2 {M m2 m1 nStd kTail tShift : ℕ}
    (ts : TailShiftParams M m2 m1 nStd kTail tShift) : m1 < m2 := by
  have h1 := ts.hm1_le
  have h2 := ts.hmShift_eq
  cases h : ts.mode <;> simp only [h, TailShiftMode.wShift] at h2 <;> omega
theorem TailShiftParams.hm1_le14 {M m2 m1 nStd kTail tShift : ℕ}
    (ts : TailShiftParams M m2 m1 nStd kTail tShift) : m1 ≤ 14 :=
  Nat.le_of_lt (Nat.lt_of_lt_of_le ts.hm1_lt_m2 ts.hm2_le14)
theorem TailShiftParams.hm1_le16 {M m2 m1 nStd kTail tShift : ℕ}
    (ts : TailShiftParams M m2 m1 nStd kTail tShift) : m1 ≤ 16 :=
  le_trans ts.hm1_le14 (by decide)
theorem TailShiftParams.hbC_ge2 {M m2 m1 nStd kTail tShift : ℕ}
    (ts : TailShiftParams M m2 m1 nStd kTail tShift) : 2 ≤ 16 - m2 := by
  have h := ts.hm2_le14
  omega

theorem TailShiftParams.hbC_ge1 {M m2 m1 nStd kTail tShift : ℕ}
    (ts : TailShiftParams M m2 m1 nStd kTail tShift) : 1 ≤ 16 - m2 :=
  le_trans (by decide) ts.hbC_ge2

theorem TailShiftParams.hSubM_eq {M m2 m1 nStd kTail tShift : ℕ}
    (ts : TailShiftParams M m2 m1 nStd kTail tShift) :
    (m2 - m1) + (16 - m2) = 16 - m1 := by
  have h1 := ts.hm1_lt_m2
  have h2 := ts.hm2_le14
  omega

theorem TailShiftParams.hSubM_le {M m2 m1 nStd kTail tShift : ℕ}
    (ts : TailShiftParams M m2 m1 nStd kTail tShift) :
    (m2 - m1) + (16 - m2) ≤ 16 - m1 :=
  ts.hSubM_eq.le

theorem TailShiftParams.hBlock0SubM_le {M m2 m1 nStd kTail tShift : ℕ}
    (ts : TailShiftParams M m2 m1 nStd kTail tShift) : 0 + (m2 - m1) ≤ 16 - m1 := by
  have h := ts.hSubM_le
  omega

theorem TailShiftParams.hShift_eq {M m2 m1 nStd kTail tShift : ℕ}
    (ts : TailShiftParams M m2 m1 nStd kTail tShift) :
    (ts.mShift - m1) + ts.mode.wShift = m2 - m1 := by
  have h1 := ts.hm1_le
  have h2 := ts.hmShift_eq
  omega

theorem TailShiftParams.hShift_le {M m2 m1 nStd kTail tShift : ℕ}
    (ts : TailShiftParams M m2 m1 nStd kTail tShift) :
    (ts.mShift - m1) + ts.mode.wShift ≤ 16 - m1 :=
  le_trans ts.hShift_eq.le (Nat.le_trans (Nat.le_add_right _ (16 - m2)) ts.hSubM_le)

theorem tailShiftClockPerm_inv_mod {M m2 m1 nStd kTail tShift : ℕ}
    (ts : TailShiftParams M m2 m1 nStd kTail tShift) :
    (ts.mode.cFwd * 2 ^ (ts.mShift - m1) + ts.mode.cBwd * 2 ^ (ts.mShift - m1)) %
      2 ^ (m2 - m1) = 0 := by
  have hsum : ts.mode.cFwd * 2 ^ (ts.mShift - m1) + ts.mode.cBwd * 2 ^ (ts.mShift - m1) =
      (ts.mode.cFwd + ts.mode.cBwd) * 2 ^ (ts.mShift - m1) := by ring
  have hpow : 2 ^ (m2 - m1) = 2 ^ ts.mode.wShift * 2 ^ (ts.mShift - m1) := by
    rw [← ts.hShift_eq, add_comm, pow_add]
  obtain ⟨k, hk⟩ := Nat.dvd_of_mod_eq_zero ts.mode.cFwd_add_cBwd_mod
  rw [hsum, hk, hpow,
    show 2 ^ ts.mode.wShift * k * 2 ^ (ts.mShift - m1) =
      (2 ^ ts.mode.wShift * 2 ^ (ts.mShift - m1)) * k by ring,
    Nat.mul_mod_right]

/-- Full `(16 - m1)`-bit QPE clock permutation on `m1 .. 15` shifting `m1 .. m2 - 1` by
`qShift = mode.cFwd * 2 ^ (mShift - m1)` modulo `2 ^ (m2 - m1)` iff `m2 .. 15` equals `nStd + 1`. -/
def tailShiftClockPerm {M m2 m1 nStd kTail tShift : ℕ}
    (ts : TailShiftParams M m2 m1 nStd kTail tShift) :
    Equiv.Perm (Fin (2 ^ (16 - m1))) where
  toFun x := ⟨tailShiftClockMapVal (m2 - m1) (16 - m2) nStd
      (ts.mode.cFwd * 2 ^ (ts.mShift - m1)) x.val,
    lt_of_lt_of_eq
      (tailShiftClockMapVal_lt (lt_of_lt_of_eq x.isLt (congrArg (2 ^ ·) ts.hSubM_eq.symm)))
      (congrArg (2 ^ ·) ts.hSubM_eq)⟩
  invFun y := ⟨tailShiftClockMapVal (m2 - m1) (16 - m2) nStd
      (ts.mode.cBwd * 2 ^ (ts.mShift - m1)) y.val,
    lt_of_lt_of_eq
      (tailShiftClockMapVal_lt (lt_of_lt_of_eq y.isLt (congrArg (2 ^ ·) ts.hSubM_eq.symm)))
      (congrArg (2 ^ ·) ts.hSubM_eq)⟩
  left_inv x := Fin.ext
    (tailShiftClockMapVal_cancel (bC := 16 - m2) (tailShiftClockPerm_inv_mod ts) x.val)
  right_inv y := Fin.ext (tailShiftClockMapVal_cancel (bC := 16 - m2)
    (by
      rw [add_comm]
      exact tailShiftClockPerm_inv_mod ts) y.val)

theorem TailShiftParams.scr_need_le {M m2 m1 nStd kTail tShift : ℕ}
    (ts : TailShiftParams M m2 m1 nStd kTail tShift) (aRem mRem sRem : ℕ) :
    1 + (16 - m2 - 2) + ts.mode.sBody ≤ scrAncillas 16 0 aRem mRem sRem := by
  have hc := scr_ge_chunked 16 0 aRem mRem sRem
  dsimp [chunkedCtrlScrNeed] at hc
  have h1 := ts.hmShift_eq
  have h2 := ts.hm2_le14
  cases h : ts.mode <;> simp only [h, TailShiftMode.wShift, TailShiftMode.sBody] at h1 ⊢ <;> omega

/-- Inner `(1 + wShift + sBody)`-wire controlled sub-clock shift circuit for `ts.mode`. -/
def tailShiftBodyLocalDyn {Var : Type} (mode : TailShiftMode) (v : Var) (invert : Bool) :
    DynamicCircuit Var (1 + mode.wShift + mode.sBody) :=
  match mode with
  | .mod4Add1 => ctrlAddMod4LocalDyn v invert
  | .mod4Add3 => ctrlAddMod4LocalDyn v (!invert)
  | .mod8Add1 => ctrlAddMod8Odd17LocalDyn v invert
  | .mod8Add3 => ctrlAddMod8Odd35LocalDyn v invert
  | .mod8Add5 => ctrlAddMod8Odd35LocalDyn v (!invert)

@[simp] theorem tailShiftBodyLocalDyn_count_toff {Var : Type} (mode : TailShiftMode) (v : Var)
    (invert : Bool) : (tailShiftBodyLocalDyn mode v invert).count .TOFF = 0 := by
  cases mode <;> dsimp only [tailShiftBodyLocalDyn, TailShiftMode.wShift, TailShiftMode.sBody]
  · exact ctrlAddMod4LocalDyn_count_toff v invert
  · exact ctrlAddMod4LocalDyn_count_toff v (!invert)
  · exact ctrlAddMod8Odd17LocalDyn_count_toff v invert
  · exact ctrlAddMod8Odd35LocalDyn_count_toff v invert
  · exact ctrlAddMod8Odd35LocalDyn_count_toff v (!invert)

@[simp] theorem tailShiftBodyLocalDyn_count_t {Var : Type} (mode : TailShiftMode) (v : Var)
    (invert : Bool) : (tailShiftBodyLocalDyn mode v invert).count .T = mode.tBody := by
  cases mode <;> dsimp only [tailShiftBodyLocalDyn, TailShiftMode.wShift, TailShiftMode.sBody,
    TailShiftMode.tBody]
  · exact ctrlAddMod4LocalDyn_count_t v invert
  · exact ctrlAddMod4LocalDyn_count_t v (!invert)
  · exact ctrlAddMod8Odd17LocalDyn_count_t v invert
  · exact ctrlAddMod8Odd35LocalDyn_count_t v invert
  · exact ctrlAddMod8Odd35LocalDyn_count_t v (!invert)

theorem cleanRealizes_tailShiftBodyLocalDyn {Var : Type} [Fintype Var] [DecidableEq Var]
    (mode : TailShiftMode) (v : Var) (invert : Bool) :
    Comparators.CleanRealizes v
      (QRegister.block 0 (1 + mode.wShift) (by cases mode <;> decide))
      (QRegister.block (1 + mode.wShift) mode.sBody (by cases mode <;> decide))
      (muxBitLocalUnitary 1 (permutationUnitary
        (if invert then addConstModPerm mode.wShift mode.cBwd mode.cFwd mode.cBwd_add_cFwd_mod
         else addConstModPerm mode.wShift mode.cFwd mode.cBwd mode.cFwd_add_cBwd_mod)))
      (tailShiftBodyLocalDyn mode v invert) := by
  cases mode <;> cases invert <;>
    dsimp only [tailShiftBodyLocalDyn, TailShiftMode.wShift, TailShiftMode.sBody,
      TailShiftMode.cFwd, TailShiftMode.cBwd]
  · exact cleanRealizes_ctrlAddMod4LocalDyn v false
  · exact cleanRealizes_ctrlAddMod4LocalDyn v true
  · exact cleanRealizes_ctrlAddMod4LocalDyn v true
  · exact cleanRealizes_ctrlAddMod4LocalDyn v false
  · exact cleanRealizes_ctrlAddMod8Odd1LocalDyn v
  · exact cleanRealizes_ctrlAddMod8Odd7LocalDyn v
  · exact cleanRealizes_ctrlAddMod8Odd3LocalDyn v
  · exact cleanRealizes_ctrlAddMod8Odd5LocalDyn v
  · exact cleanRealizes_ctrlAddMod8Odd5LocalDyn v
  · exact cleanRealizes_ctrlAddMod8Odd3LocalDyn v

/-- Parametric `TOFF = 0` conditional QPE sub-clock shift on `combQubitsB wOuter wInner2 ko km sRem`
(`invert = false` realizes `tailShiftClockPerm ts`; `invert = true` realizes `.symm`). -/
def tailShiftClockPermDyn {Var : Type} (wOuter wInner2 ko km sRem : ℕ)
    {M m2 m1 nStd kTail tShift : ℕ} (ts : TailShiftParams M m2 m1 nStd kTail tShift)
    (v : Var) (invert : Bool) : DynamicCircuit Var (combQubitsB wOuter wInner2 ko km sRem) :=
  let mOut := mOutUB wOuter
  let mMid := mMidUB wInner2
  let aRem := combARem wOuter wInner2 ko km
  let mRem := midRemWidth wInner2 km
  let rHi1 := (rActLoc 16 11 mOut mMid 0 aRem mRem sRem).compose
    ((rQPEInAct 16 11 mOut mMid).compose (rHiInQPE16 m1 ts.hm1_le16))
  let rTopC := rHi1.compose (QRegister.block (m2 - m1) (16 - m2) ts.hSubM_le)
  let rShift := rHi1.compose (QRegister.block (ts.mShift - m1) ts.mode.wShift ts.hShift_le)
  let rScr := rScrLoc 16 11 mOut mMid 0 aRem mRem sRem
  let hscr := ts.scr_need_le aRem mRem sRem
  let wFlag := rScr ⟨0, by omega⟩
  let rCarry := rScr.compose (QRegister.block 1 (16 - m2 - 2) (by omega))
  let rBodyScr := rScr.compose (QRegister.block (1 + (16 - m2 - 2)) ts.mode.sBody hscr)
  have hHiEq : rHi1 =
      (rQPELoc 16 11 mOut mMid 0 aRem mRem sRem).compose (rHiInQPE16 m1 ts.hm1_le16) := by
    ext i
    rfl
  have hHiScr : rHi1.DisjointWires rScr := hHiEq ▸ QubitisedWalk.disjointWires_compose_left
    (rQPELoc_disjoint_rScrLoc 16 11 mOut mMid 0 aRem mRem sRem)
  have hFT : (QRegister.singleton wFlag).DisjointWires rShift := by
    rw [QRegister.disjoint_iff]
    intro a j
    fin_cases a
    exact ((QubitisedWalk.disjointWires_compose_left hHiScr).ne j ⟨0, by omega⟩).symm
  have hFBS : ((QRegister.singleton wFlag).concat rShift hFT).DisjointWires rBodyScr := by
    rw [QRegister.disjoint_iff]
    intro p j
    rcases finSumFinEquiv.surjective p with ⟨a | i, rfl⟩
    · fin_cases a
      simp only [finSumFinEquiv_apply_left, QRegister.concat_apply_left,
        QRegister.singleton_apply, wFlag, rBodyScr, QRegister.compose_apply]
      intro h
      have hv := congrArg Fin.val (rScr.wires.injective h)
      simp only [QRegister.block_apply_val] at hv
      omega
    · simp only [finSumFinEquiv_apply_right, QRegister.concat_apply_right]
      exact (QubitisedWalk.disjointWires_compose_left
        (QubitisedWalk.disjointWires_compose_right hHiScr)).ne i j
  let rBodyLoc := ((QRegister.singleton wFlag).concat rShift hFT).concat rBodyScr hFBS
  withEqConstFlagDyn v rTopC (nStd + 1) rCarry wFlag ts.hbC_ge1
    (QubitisedWalk.disjointWires_compose_left (QubitisedWalk.disjointWires_compose_right hHiScr))
    (fun i ↦ (QubitisedWalk.disjointWires_compose_left hHiScr).ne i ⟨0, by omega⟩)
    (fun j h ↦ by
      have hv := congrArg Fin.val (rScr.wires.injective h)
      simp only [QRegister.block_apply_val] at hv
      omega)
    ((tailShiftBodyLocalDyn ts.mode v invert).onRegister rBodyLoc)

@[simp] theorem tailShiftClockPermDyn_count_toff {Var : Type} (wOuter wInner2 ko km sRem : ℕ)
    {M m2 m1 nStd kTail tShift : ℕ} (ts : TailShiftParams M m2 m1 nStd kTail tShift)
    (v : Var) (invert : Bool) :
    (tailShiftClockPermDyn wOuter wInner2 ko km sRem ts v invert).count .TOFF = 0 := by
  simp [tailShiftClockPermDyn, count_withEqConstFlagDyn_toff]

theorem tailShiftClockPermDyn_pair_count_t_le {Var : Type} (wOuter wInner2 ko km sRem : ℕ)
    {M m2 m1 nStd kTail tShift : ℕ} (ts : TailShiftParams M m2 m1 nStd kTail tShift) (v : Var) :
    (tailShiftClockPermDyn wOuter wInner2 ko km sRem ts v false).count .T +
      (tailShiftClockPermDyn wOuter wInner2 ko km sRem ts v true).count .T ≤ tShift := by
  have ht := ts.htShift
  simp only [tailShiftClockPermDyn, count_withEqConstFlagDyn_t, DynamicCircuit.count_onRegister,
    tailShiftBodyLocalDyn_count_t]
  omega

theorem embed_subClockMux_eq_tailShiftClockPerm {M m2 m1 nStd kTail tShift : ℕ}
    (ts : TailShiftParams M m2 m1 nStd kTail tShift) (invert : Bool) :
    let rTop : QRegister (16 - m2) (16 - m1) := QRegister.block (m2 - m1) (16 - m2) ts.hSubM_le
    let rSh : QRegister ts.mode.wShift (16 - m1) :=
      QRegister.block (ts.mShift - m1) ts.mode.wShift ts.hShift_le
    have hDisj : rTop.DisjointWires rSh := QRegister.disjoint_iff.mpr fun i j hij ↦ by
      have hv := congrArg Fin.val hij
      have _hj := j.isLt
      have hsh := ts.hShift_eq
      simp only [rTop, rSh, QRegister.block_apply_val] at hv
      omega
    let σ_sh : Equiv.Perm (Fin (2 ^ ts.mode.wShift)) :=
      if invert then addConstModPerm ts.mode.wShift ts.mode.cBwd ts.mode.cFwd
        ts.mode.cBwd_add_cFwd_mod
      else addConstModPerm ts.mode.wShift ts.mode.cFwd ts.mode.cBwd ts.mode.cFwd_add_cBwd_mod
    (rTop.concat rSh hDisj).embedUnitary
        (muxPredLocalUnitary (fun a : Fin (2 ^ (16 - m2)) ↦ decide (a.val = nStd + 1)) 1
          (permutationUnitary σ_sh)) =
      permutationUnitary
        (if invert then (tailShiftClockPerm ts).symm else tailShiftClockPerm ts) := by
  intro rTop rSh hDisj σ_sh
  have hm12 := ts.hm1_lt_m2
  have hm2_14 := ts.hm2_le14
  let N := 16 - m1
  let s := ts.mShift - m1
  let w := ts.mode.wShift
  let bM := m2 - m1
  let c := if invert then ts.mode.cBwd else ts.mode.cFwd
  let τ := if invert then (tailShiftClockPerm ts).symm else tailShiftClockPerm ts
  have hsw : s + w = bM := ts.hShift_eq
  have hbMN : bM + (16 - m2) = N := ts.hSubM_eq
  have hWhole : (QRegister.whole N).embedUnitary (permutationUnitary τ) = permutationUnitary τ :=
    QRegister.whole_embedUnitary _
  rw [← hWhole]
  refine Subtype.ext (matrix_ext_ket fun β ↦ ?_)
  rw [QRegister.embedUnitary_val, QRegister.embedUnitary_val, ← QRegister.embedUnitary_val,
    ← QRegister.embedUnitary_val, embedUnitary_muxPredLocalUnitary, muxPredUnitary_mulVec_ket,
    embedUnitary_permutationUnitary_mulVec_ket]
  let idx := (basisBits N).symm β
  have hlocW : localIdx (QRegister.whole N) β = idx := rfl
  have hTopVal : (localIdx rTop β).val = idx.val / 2 ^ bM := by
    apply Nat.eq_of_testBit_eq
    intro k
    by_cases hk : k < 16 - m2
    · rw [Nat.testBit_div_two_pow]
      have hb1 := testBit_eq_decide_basisBits (localIdx rTop β) ⟨k, hk⟩
      have hb2 := testBit_eq_decide_basisBits idx ⟨k + bM, by omega⟩
      rw [basisBits_basisBitsEquiv_symm] at hb1 hb2
      have hfin : rTop ⟨k, hk⟩ = ⟨k + bM, by omega⟩ := Fin.ext (by
        simp only [rTop, QRegister.block_apply_val]
        omega)
      exact hb1.trans ((congrArg (fun p ↦ decide (β p = 1)) hfin).trans hb2.symm)
    · have hid_lt : idx.val / 2 ^ bM < 2 ^ (16 - m2) := Nat.div_lt_of_lt_mul (by
        rw [← pow_add, hbMN]
        exact idx.isLt)
      rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le (localIdx rTop β).isLt
          (Nat.pow_le_pow_right Nat.two_pos (by omega))),
        Nat.testBit_lt_two_pow (lt_of_lt_of_le hid_lt
          (Nat.pow_le_pow_right Nat.two_pos (by omega)))]
  have hVal2 : (localIdx rSh β).val = (idx.val % 2 ^ bM) / 2 ^ s := by
    apply Nat.eq_of_testBit_eq
    intro k
    by_cases hk : k < w
    · rw [Nat.testBit_div_two_pow, Nat.testBit_mod_two_pow,
        decide_eq_true (show k + s < bM by omega), Bool.true_and]
      have hb1 := testBit_eq_decide_basisBits (localIdx rSh β) ⟨k, hk⟩
      have hb2 := testBit_eq_decide_basisBits idx ⟨k + s, by omega⟩
      rw [basisBits_basisBitsEquiv_symm] at hb1 hb2
      have hfin : rSh ⟨k, hk⟩ = ⟨k + s, by omega⟩ := Fin.ext (by
        simp only [rSh, QRegister.block_apply_val]
        omega)
      exact hb1.trans ((congrArg (fun p ↦ decide (β p = 1)) hfin).trans hb2.symm)
    · have hsh_lt : (idx.val % 2 ^ bM) / 2 ^ s < 2 ^ w := Nat.div_lt_of_lt_mul (by
        rw [← pow_add, hsw]
        exact Nat.mod_lt _ (Nat.two_pow_pos bM))
      rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le (localIdx rSh β).isLt
          (Nat.pow_le_pow_right Nat.two_pos (by omega))),
        Nat.testBit_lt_two_pow (lt_of_lt_of_le hsh_lt
          (Nat.pow_le_pow_right Nat.two_pos (by omega)))]
  have hτVal : (τ idx).val = tailShiftClockMapVal bM (16 - m2) nStd (c * 2 ^ s) idx.val := by
    cases invert <;> rfl
  have hσVal : (σ_sh (localIdx rSh β)).val = ((localIdx rSh β).val + c) % 2 ^ w := by
    cases invert <;> rfl
  by_cases hc_eq : idx.val / 2 ^ bM = nStd + 1
  · have hpred : decide ((localIdx rTop β).val = nStd + 1) = true :=
      decide_eq_true (hTopVal.trans hc_eq)
    rw [ite_eq_left hpred, embedUnitary_permutationUnitary_mulVec_ket]
    congr 1
    ext q
    have hmod_decomp : (idx.val % 2 ^ bM + c * 2 ^ s) % 2 ^ bM =
        (idx.val % 2 ^ bM) % 2 ^ s + (((idx.val % 2 ^ bM) / 2 ^ s + c) % 2 ^ w) * 2 ^ s := by
      let lo := (idx.val % 2 ^ bM) % 2 ^ s
      let mid := (idx.val % 2 ^ bM) / 2 ^ s
      have hxm : idx.val % 2 ^ bM = lo + mid * 2 ^ s := by
        dsimp [lo, mid]
        have hmd := Nat.mod_add_div (idx.val % 2 ^ bM) (2 ^ s)
        linarith
      have hlo : lo < 2 ^ s := Nat.mod_lt _ (Nat.two_pow_pos s)
      have hmid' : (mid + c) % 2 ^ w < 2 ^ w := Nat.mod_lt _ (Nat.two_pow_pos w)
      have hpow : 2 ^ bM = 2 ^ w * 2 ^ s := by rw [← hsw, add_comm, pow_add]
      have hsum_eq : idx.val % 2 ^ bM + c * 2 ^ s =
          (lo + ((mid + c) % 2 ^ w) * 2 ^ s) + (2 ^ bM) * ((mid + c) / 2 ^ w) := by
        have hdm := Nat.div_add_mod (mid + c) (2 ^ w)
        rw [hxm, hpow]
        nlinarith
      have hlt_bM : lo + ((mid + c) % 2 ^ w) * 2 ^ s < 2 ^ bM := by
        rw [hpow]
        nlinarith
      rw [hsum_eq, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt_bM]
    have hτ_eq : (τ idx).val =
        ((idx.val % 2 ^ bM) % 2 ^ s + (((idx.val % 2 ^ bM) / 2 ^ s + c) % 2 ^ w) * 2 ^ s) +
          (idx.val / 2 ^ bM) * 2 ^ bM := by
      rw [hτVal]
      dsimp only [tailShiftClockMapVal]
      rw [ite_eq_left hc_eq, hmod_decomp]
    rw [hlocW, writeReg_whole2]
    apply zmod2_eq_of_decide_eq
    rw [← testBit_eq_decide_basisBits (τ idx) q]
    have h2s : 2 ^ bM = 2 ^ s * 2 ^ w := by rw [← hsw, pow_add]
    by_cases hq_lo : q.val < s
    · have hnot : q ∉ Set.range rSh.wires := fun hm ↦ by
        obtain ⟨j, rfl⟩ := hm
        simp only [rSh, QRegister.block_apply_val] at hq_lo
        omega
      rw [Comparators.writeReg_apply_of_not_mem _ _ _ q hnot]
      have h1 := testBit_eq_decide_basisBits idx q
      rw [basisBits_basisBitsEquiv_symm] at h1
      rw [← h1, hτ_eq]
      have hdiv0 : q.val < bM := by omega
      have hmul : (((idx.val % 2 ^ bM) / 2 ^ s + c) % 2 ^ w) * 2 ^ s +
          (idx.val / 2 ^ bM) * 2 ^ bM =
          ((((idx.val % 2 ^ bM) / 2 ^ s + c) % 2 ^ w) +
            (idx.val / 2 ^ bM) * 2 ^ w) * 2 ^ s := by
        rw [h2s]
        ring
      rw [add_assoc, hmul, add_mul_testBit_of_lt (Nat.mod_lt _ (Nat.two_pow_pos s)) hq_lo]
      simp [Nat.testBit_mod_two_pow, hq_lo, hdiv0]
    · by_cases hq_mid : q.val < bM
      · let j : Fin w := ⟨q.val - s, by omega⟩
        have hqj : rSh j = q := Fin.ext (by
          simp only [rSh, j, QRegister.block_apply_val]
          omega)
        rw [← hqj, writeReg_apply_reg, ← testBit_eq_decide_basisBits (σ_sh (localIdx rSh β)) j,
          hσVal, hVal2, hqj, hτ_eq]
        have hlo : (idx.val % 2 ^ bM) % 2 ^ s < 2 ^ s := Nat.mod_lt _ (Nat.two_pow_pos s)
        have hmul : (idx.val % 2 ^ bM) % 2 ^ s +
            (((idx.val % 2 ^ bM) / 2 ^ s + c) % 2 ^ w) * 2 ^ s +
            (idx.val / 2 ^ bM) * 2 ^ bM =
            (idx.val % 2 ^ bM) % 2 ^ s +
              ((((idx.val % 2 ^ bM) / 2 ^ s + c) % 2 ^ w) +
                (idx.val / 2 ^ bM) * 2 ^ w) * 2 ^ s := by
          rw [h2s]
          ring
        rw [hmul, add_mul_testBit_of_ge hlo (by omega),
          add_mul_testBit_of_lt (Nat.mod_lt _ (Nat.two_pow_pos w)) (by omega)]
      · have hnot : q ∉ Set.range rSh.wires := fun hm ↦ by
          obtain ⟨j, rfl⟩ := hm
          have _hj := j.isLt
          simp only [rSh, QRegister.block_apply_val] at hq_mid
          omega
        rw [Comparators.writeReg_apply_of_not_mem _ _ _ q hnot]
        have h1 := testBit_eq_decide_basisBits idx q
        rw [basisBits_basisBitsEquiv_symm] at h1
        rw [← h1, hτ_eq]
        have hlt_bM : (idx.val % 2 ^ bM) % 2 ^ s +
            (((idx.val % 2 ^ bM) / 2 ^ s + c) % 2 ^ w) * 2 ^ s < 2 ^ bM := by
          rw [← hmod_decomp]
          exact Nat.mod_lt _ (Nat.two_pow_pos bM)
        rw [add_mul_testBit_of_ge hlt_bM (by omega)]
        have hidx_eq : idx.val = idx.val % 2 ^ bM + (idx.val / 2 ^ bM) * 2 ^ bM := by
          have hmd := Nat.mod_add_div idx.val (2 ^ bM)
          linarith
        conv_lhs => rw [hidx_eq]
        rw [add_mul_testBit_of_ge (Nat.mod_lt _ (Nat.two_pow_pos bM)) (by omega)]
  · have hpred : decide ((localIdx rTop β).val = nStd + 1) = false :=
      decide_eq_false (fun h ↦ hc_eq (hTopVal.symm.trans h))
    have hτ_id : τ idx = idx := Fin.ext (by
      rw [hτVal]
      dsimp only [tailShiftClockMapVal]
      rw [ite_eq_right hc_eq, mul_comm _ (2 ^ bM), Nat.mod_add_div])
    simp only [hpred, Bool.false_eq_true, ↓reduceIte, QRegister.embedUnitary_one,
      Submonoid.coe_one, Matrix.one_mulVec]
    rw [embedUnitary_permutationUnitary_mulVec_ket, hlocW, hτ_id, writeReg_whole2,
      basisBits_basisBitsEquiv_symm]

end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.TailShiftThreeGear
end
