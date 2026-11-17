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
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.BellSuperLegSplice
/-! # Zero-Top-Ancilla `d = 11` Streamed Phase-Kick & Affine `Lac = 2` Plane Engine
Refs: Jones (`10.1103/PhysRevA.87.022328`), Gidney (`10.22331/q-2018-06-18-74`),
Berry (`10.22331/q-2019-12-02-208`), Lee (`10.1103/PRXQuantum.2.030305`). -/
@[expose] public section
namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.PhaseBD11CompactCore
open QuantumComputation.Specs QuantumComputation.Specs.P450
open Operator QProg Matrix HermitianMat Real CoherentAlias Solution.CleanDyn AliasPrep
open QuantumComputation.Specs Solution QuantumComputation.Specs.P450 TwoGearBox
open Solution.CircuitModular GivensOps BlockEncodingCore
open BlockEncodingCircuit SelectSwapQROM GivensCascade
open SelectRouter10 TopIntegrationBridge
open Lac2Fused184Select Lac2Fused184SelectWrap Router10Lac2Select
open Phase2MidSandwich MidReflCtxRetain OneHotSimulates
open PolymorphicFused184Select Lac2ZeroPar183Select CompactFoldedSelect
open ReordOuter13Bridge StepEncK StepDecK
open CompactStepFast175Core CompactOuter9Bound50Core CompactOuter9Bound50Select
open Balanced160Select Pi145SOSPermBridge LowBitPi145Select BellPhaseASelect
open BellSingletCSwap58 Cat11CompactPhase2Bridge PhaseB154Pi145Select
open BellRouter57 BellRouter57Pure NoNegSelect57Pure CompactCore145Bundle
open BellPersistNoNeg BellSelectNoNegPair Select57Slices BellPersistCore
open BellAsymCore BellSuperLegSplice
open scoped Matrix BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
theorem update_update_self_eq2 {n : ℕ} (β : BitAssignment n) (w : Wire n) (v : ZMod 2) :
    Function.update (Function.update β w v) w (β w) = β := by
  rw [Function.update_idem, Function.update_eq_self]
theorem update_of_mem_not_mem {n : ℕ} {S : Finset (Wire n)} {w x : Wire n} (hw : w ∈ S) (hx : x ∉
  S) (β : BitAssignment n) (v : ZMod 2) : Function.update β x v w = β w := Function.update_of_ne
  (fun h : w = x ↦ hx (h ▸ hw)) v β
theorem update_ne_of_eq {n : ℕ} {w₁ w₂ x : Wire n} (heq : w₁ = w₂) (hne : w₂ ≠ x) (β :
  BitAssignment n) (v : ZMod 2) : Function.update β x v w₁ = β w₁ := heq ▸ Function.update_of_ne hne
  v β
theorem update_anc_ne {n : ℕ} {w x₁ x₂ : Wire n} (heq : x₁ = x₂) (hne : w ≠ x₂) (β : BitAssignment
    n) (v : ZMod 2) : Function.update β x₁ v w = β w := by rw [heq]
                                                           exact Function.update_of_ne hne v β
theorem fin_pred_ne {m j : ℕ} (h0 : 0 < j) (hj : j < m) : (⟨j - 1, by omega⟩ : Fin m) ≠ ⟨j, hj⟩ :=
    by
  intro h
  have hv := congrArg Fin.val h
  dsimp at hv
  omega
theorem evolve_T_ket2 {n : ℕ} (q : Wire n) (β : BitAssignment n) : (Circuit.T q).eval.1.mulVec
    (UnsignedGivens.ket β) = (if β q = 0 then (1 : ℂ) else UnsignedGivens.omega8) •
        UnsignedGivens.ket β := by
  rw [UnsignedGivens.evolve_T_ket]
  congr 1
  rcases UnsignedGivens.zmod2_eq_zero_or_one (β q) with hb | hb <;> simp [hb]
theorem evolve_T_inverse_ket {n : ℕ} (q : Wire n) (β : BitAssignment n) : (Circuit.T
    q).inverse.eval.1.mulVec (UnsignedGivens.ket β) = (if β q = 0 then (1 : ℂ) else -Complex.I *
    UnsignedGivens.omega8) • UnsignedGivens.ket β := by
  change (Circuit.seq (Circuit.T q) (Circuit.seq (Circuit.S q) (Circuit.seq (Circuit.Z q)
    .identity))).eval.1.mulVec (UnsignedGivens.ket β) = _
  simp only [UnsignedGivens.eval_seq_mulVec, UnsignedGivens.eval_identity_mulVec,
    UnsignedGivens.evolve_T_ket,
    UnsignedGivens.evolve_S_ket, UnsignedGivens.evolve_Z_ket, Matrix.mulVec_smul, smul_smul]
  congr 1
  rcases UnsignedGivens.zmod2_eq_zero_or_one (β q) with hb | hb
  · simp [hb]
  · simp [hb]
    ring
/-- 8-gate diagonal/CNOT core of the `4-T` relative-phase Toffoli (`4 T`, `0 TOFF`). -/
def rccxMid8 {n : ℕ} (c₁ c₂ t : Wire n) (h₁t : c₁ ≠ t) (h₂t : c₂ ≠ t) : Circuit n := Circuit.seq
  (Circuit.T t) (Circuit.seq (Circuit.CNOT c₂ t h₂t) (Circuit.seq (Circuit.T t).inverse
  (Circuit.seq (Circuit.CNOT c₁ t h₁t) (Circuit.seq (Circuit.T t) (Circuit.seq (Circuit.CNOT c₂ t
  h₂t) (Circuit.seq (Circuit.T t).inverse (Circuit.CNOT c₁ t h₁t)))))))
/-- `4-T`, `0-TOFF` relative-phase Toffoli (`rccxCircuit`) with phase `-i` on `c₁ · c₂ = 1`. -/
def rccxCircuit {n : ℕ} (c₁ c₂ t : Wire n) (h₁t : c₁ ≠ t) (h₂t : c₂ ≠ t) : Circuit n :=
  Circuit.seq (Circuit.H t) (Circuit.seq (rccxMid8 c₁ c₂ t h₁t h₂t) (Circuit.H t))
@[simp] theorem countRccxMid8_t {n : ℕ} (c₁ c₂ t : Wire n) (h₁t : c₁ ≠ t) (h₂t : c₂ ≠ t) :
    (rccxMid8 c₁ c₂ t h₁t h₂t).count .T = 4 := by
  simp [rccxMid8, Circuit.inverse, Circuit.inverseGate, Circuit.sequence]
@[simp] theorem countRccxMid8_toff {n : ℕ} (c₁ c₂ t : Wire n) (h₁t : c₁ ≠ t) (h₂t : c₂ ≠ t) :
    (rccxMid8 c₁ c₂ t h₁t h₂t).count .TOFF = 0 := by
  simp [rccxMid8, Circuit.inverse, Circuit.inverseGate, Circuit.sequence]
@[simp] theorem countRccxCircuit_t {n : ℕ} (c₁ c₂ t : Wire n) (h₁t : c₁ ≠ t) (h₂t : c₂ ≠ t) :
    (rccxCircuit c₁ c₂ t h₁t h₂t).count .T = 4 := by simp [rccxCircuit]
@[simp] theorem countRccxCircuit_toff {n : ℕ} (c₁ c₂ t : Wire n) (h₁t : c₁ ≠ t) (h₂t : c₂ ≠ t) :
    (rccxCircuit c₁ c₂ t h₁t h₂t).count .TOFF = 0 := by simp [rccxCircuit]
@[simp] theorem countRccxCircuit_inverse_t {n : ℕ} (c₁ c₂ t : Wire n) (h₁t : c₁ ≠ t) (h₂t : c₂ ≠
    t) : (rccxCircuit c₁ c₂ t h₁t h₂t).inverse.count .T = 4 := by
  simp [rccxCircuit, rccxMid8, Circuit.inverse, Circuit.inverseGate, Circuit.sequence]
@[simp] theorem countRccxCircuit_inverse_toff {n : ℕ} (c₁ c₂ t : Wire n) (h₁t : c₁ ≠ t) (h₂t : c₂
    ≠ t) : (rccxCircuit c₁ c₂ t h₁t h₂t).inverse.count .TOFF = 0 := by
  simp [rccxCircuit, rccxMid8, Circuit.inverse, Circuit.inverseGate, Circuit.sequence]
theorem rccxPhase4T_eq (b₁ b₂ a : ZMod 2) : (if a = 0 then (1 : ℂ) else UnsignedGivens.omega8) *
    (if a + b₂
    = 0 then (1 : ℂ) else -Complex.I * UnsignedGivens.omega8) * (if a + b₂ + b₁ = 0 then (1 :
      ℂ) else
    UnsignedGivens.omega8) * (if a + b₁ = 0 then (1 : ℂ) else -Complex.I * UnsignedGivens.omega8) =
      if b₁ * b₂ = 0
    then 1 else if a = 0 then -Complex.I else Complex.I := by
  have ho2 : UnsignedGivens.omega8 * UnsignedGivens.omega8 = Complex.I := by
    simpa [sq] using UnsignedGivens.omega8_sq
  have hI2 : Complex.I * Complex.I = -1 := Complex.I_mul_I
  have h10 : (1 : ZMod 2) ≠ 0 := by decide
  have h11 : (1 : ZMod 2) + 1 = 0 := by decide
  rcases UnsignedGivens.zmod2_eq_zero_or_one b₁ with rfl | rfl <;>
    rcases UnsignedGivens.zmod2_eq_zero_or_one b₂ with rfl | rfl <;>
    rcases UnsignedGivens.zmod2_eq_zero_or_one a with rfl | rfl <;>
    simp only [add_zero, zero_add, mul_zero, mul_one, one_mul, h11, h10, ↓reduceIte, neg_mul,
      mul_neg, neg_neg, mul_assoc, mul_left_comm UnsignedGivens.omega8 Complex.I, ho2, hI2]
theorem evolveRccxMid8_ket {n : ℕ} (c₁ c₂ t : Wire n) (h₁t : c₁ ≠ t) (h₂t : c₂ ≠ t) (β :
    BitAssignment n) : (rccxMid8 c₁ c₂ t h₁t h₂t).eval.1.mulVec (UnsignedGivens.ket β) = (if β c₁ *
      β c₂ =
    0 then (1 : ℂ) else if β t = 0 then -Complex.I else Complex.I) • UnsignedGivens.ket β := by
  have hadd1 (x y : ZMod 2) : x + y + y = x := UnsignedGivens.zmod2_add_cancel_right x y
  have hadd2 (x y z : ZMod 2) : x + y + z + y = x + z := by
    rw [show x + y + z + y = (x + z) + y + y by ring, UnsignedGivens.zmod2_add_cancel_right]
  dsimp only [rccxMid8]
  simp only [UnsignedGivens.eval_seq_mulVec, evolve_T_ket2, evolve_T_inverse_ket,
    UnsignedGivens.evolve_CNOT_ket,
    Matrix.mulVec_smul, Function.update_self, Function.update_of_ne h₁t, Function.update_of_ne h₂t,
    Function.update_idem, hadd2, hadd1, Function.update_eq_self, smul_smul]
  congr 1
  rw [← rccxPhase4T_eq (β c₁) (β c₂) (β t)]
  ring
theorem evolveRccxCircuit_ket {n : ℕ} (c₁ c₂ t : Wire n) (h₁t : c₁ ≠ t) (h₂t : c₂ ≠ t) (β :
    BitAssignment n) : (rccxCircuit c₁ c₂ t h₁t h₂t).eval.1.mulVec (UnsignedGivens.ket β) =
      (if β c₁ * β c₂
    = 0 then (1 : ℂ) else -Complex.I) • UnsignedGivens.ket (Function.update β t (β t + β c₁ *
      β c₂)) :=
    by
  have hs2 := UnsignedGivens.sqrtHalfC_sq
  have h10 : (1 : ZMod 2) ≠ 0 := by decide
  have h11 : (1 : ZMod 2) + 1 = 0 := by decide
  rw [rccxCircuit, UnsignedGivens.eval_seq_mulVec, UnsignedGivens.eval_seq_mulVec,
    UnsignedGivens.evolve_H_ket]
  simp only [Matrix.mulVec_smul, Matrix.mulVec_add, evolveRccxMid8_ket, Function.update_self,
    Function.update_of_ne h₁t, Function.update_of_ne h₂t, h10, ↓reduceIte,
      UnsignedGivens.evolve_H_ket,
    Function.update_idem, smul_add, smul_smul]
  rcases UnsignedGivens.zmod2_eq_zero_or_one (β c₁ * β c₂) with hp | hp <;>
    rcases UnsignedGivens.zmod2_eq_zero_or_one (β t) with ht | ht <;>
    (simp only [hp, ht, add_zero, zero_add, h11, h10, ↓reduceIte]
     ext idx
     simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, ZMod.val_zero, ZMod.val_one]
     ring_nf
     simp only [hs2]
     ring)
/-- Zero-ancilla `9-T`, `0-TOFF` relative-phase Toffoli phase kick (`rccxPhaseTKick`): applies
diagonal phase `ω₈^{(β c₁ · β c₂ + β w_p).val}` on `{c₁, c₂, w_p}` with `0` extra wires. -/
def rccxPhaseTKick {n : ℕ} (c₁ c₂ w_p : Wire n) (h₁p : c₁ ≠ w_p) (h₂p : c₂ ≠ w_p) : Circuit n :=
  Circuit.seq (rccxCircuit c₁ c₂ w_p h₁p h₂p) (Circuit.seq (Circuit.T w_p) (rccxCircuit c₁ c₂
  w_p h₁p h₂p).inverse)
@[simp] theorem countRccxPhaseTKick_t {n : ℕ} (c₁ c₂ w_p : Wire n) (h₁p : c₁ ≠ w_p) (h₂p : c₂ ≠
    w_p) : (rccxPhaseTKick c₁ c₂ w_p h₁p h₂p).count .T = 9 := by simp [rccxPhaseTKick]
@[simp] theorem countRccxPhaseTKick_toff {n : ℕ} (c₁ c₂ w_p : Wire n) (h₁p : c₁ ≠ w_p) (h₂p : c₂
    ≠ w_p) : (rccxPhaseTKick c₁ c₂ w_p h₁p h₂p).count .TOFF = 0 := by simp [rccxPhaseTKick]
theorem evolveRccxPhaseTKick_ket {n : ℕ} (c₁ c₂ w_p : Wire n) (h₁p : c₁ ≠ w_p) (h₂p : c₂ ≠ w_p)
    (β : BitAssignment n) :
      (rccxPhaseTKick c₁ c₂ w_p h₁p h₂p).eval.1.mulVec (UnsignedGivens.ket β) =
    (UnsignedGivens.omega8 ^ (β c₁ * β c₂ + β w_p).val) • UnsignedGivens.ket β := by
  let U := rccxCircuit c₁ c₂ w_p h₁p h₂p
  have hU := evolveRccxCircuit_ket c₁ c₂ w_p h₁p h₂p β
  have hT_mid : (Circuit.T w_p).eval.1.mulVec (U.eval.1.mulVec (UnsignedGivens.ket β)) =
    (UnsignedGivens.omega8 ^ (β
      c₁ * β c₂ + β w_p).val) • (U.eval.1.mulVec (UnsignedGivens.ket β)) := by
    rw [hU, Matrix.mulVec_smul, UnsignedGivens.evolve_T_ket, Function.update_self,
      add_comm (β w_p) (β c₁ * β
      c₂), smul_smul, mul_comm, ← smul_smul]
  have hinv_mul : U.inverse.eval.1 * U.eval.1 = 1 :=
    congrArg Subtype.val (show U.inverse.eval * U.eval = 1 by
      rw [Circuit.eval_inverse, inv_mul_cancel])
  dsimp only [rccxPhaseTKick]
  rw [UnsignedGivens.eval_seq_mulVec, UnsignedGivens.eval_seq_mulVec]
  change U.inverse.eval.1.mulVec ((Circuit.T w_p).eval.1.mulVec (U.eval.1.mulVec
    (UnsignedGivens.ket β))) =
      _
  rw [hT_mid, Matrix.mulVec_smul, Matrix.mulVec_mulVec, hinv_mul, Matrix.one_mulVec]
/-- Pairwise disjointness witness for the `(a0, rC)` streamed Gidney phase-kick engine. -/
structure TopZeroGidneyDisjoint {n B : ℕ} (rCat : QRegister B n) (a0 : Wire n)
    (rC : QRegister (B - 1) n) (w_p : Wire n) : Prop where
  ne_cat_a0 : ∀ i, rCat i ≠ a0
  disj_cat_C : rCat.DisjointWires rC
  ne_a0_C : ∀ j, a0 ≠ rC j
  ne_cat_wp : ∀ i, rCat i ≠ w_p
  ne_a0_wp : a0 ≠ w_p
  ne_C_wp : ∀ j, rC j ≠ w_p
namespace TopZeroGidneyDisjoint
theorem ne_cat_C {n B : ℕ} {rCat : QRegister B n} {a0 : Wire n} {rC : QRegister (B - 1) n} {w_p :
  Wire n} (h : TopZeroGidneyDisjoint rCat a0 rC w_p) (i : Fin B) (j : Fin (B - 1)) : rCat i ≠ rC j
  := QRegister.disjoint_iff.mp h.disj_cat_C i j
theorem disj_a0_C {n B : ℕ} {rCat : QRegister B n} {a0 : Wire n} {rC : QRegister (B - 1) n} {w_p :
    Wire n} (h : TopZeroGidneyDisjoint rCat a0 rC w_p) : (QRegister.singleton a0).DisjointWires rC
    :=
  QRegister.disjoint_iff.mpr fun i j ↦ by fin_cases i
                                          exact h.ne_a0_C j
end TopZeroGidneyDisjoint
/-- Bundle of `(B + 2)` clean bit-loader steps all targeting the single streamed wire `a0`. -/
structure TopZeroPhaseKickBitSteps {n B : ℕ} (rCat : QRegister B n) (a0 : Wire n)
    (rC : QRegister (B - 1) n) (w_p : Wire n) (S_ctrl : Finset (Wire n)) where
  stepTop : UnsignedGivens.PhasedStep n
  stepMid : UnsignedGivens.PhasedStep n
  stepLo : Fin B → UnsignedGivens.PhasedStep n
  bitTop : BitAssignment n → ZMod 2
  bitMid : BitAssignment n → ZMod 2
  bitLo : BitAssignment n → Fin B → ZMod 2
  ancTop : stepTop.anc = a0
  ancMid : stepMid.anc = a0
  ancLo : ∀ j : Fin B, (stepLo j).anc = a0
  cleanTop : UnsignedGivens.IsCleanBitStep stepTop bitTop S_ctrl
  cleanMid : UnsignedGivens.IsCleanBitStep stepMid bitMid S_ctrl
  cleanLo : ∀ j : Fin B, UnsignedGivens.IsCleanBitStep (stepLo j) (fun β ↦ bitLo β j) S_ctrl
  disj_ctrl_wp : w_p ∉ S_ctrl
  disj_ctrl_cat : Disjoint S_ctrl rCat.image
  not_mem_ctrl_a0 : a0 ∉ S_ctrl
  disj_ctrl_C : Disjoint S_ctrl rC.image
variable {Var : Type} {n B : ℕ}
/-- Zero-ancilla `9-T`, `0-TOFF` top-bit carry kick and sum circuit on `(x, a0, c, w_p)`: kicks `ω₈
^ (((β x + β c) * (β a0 + β c) + β c) + β w_p).val` via `rccxPhaseTKick` and updates `x` in place
to `β x + β c + β a0` while restoring `a0`, `c`, and `w_p`. -/
def topCarrySumBody (x a0 c w_p : Wire n) (hxa : x ≠ a0) (hcx : c ≠ x) (hca : c ≠ a0) (hcp : c ≠
  w_p) (hxp : x ≠ w_p) (hap : a0 ≠ w_p) : Circuit n := Circuit.seq (Circuit.seq (Circuit.CNOT c x
  hcx) (Circuit.seq (Circuit.CNOT c a0 hca) (Circuit.CNOT c w_p hcp))) (Circuit.seq
  (rccxPhaseTKick x a0 w_p hxp hap) (Circuit.seq (Circuit.CNOT c w_p hcp) (Circuit.seq
  (Circuit.CNOT c a0 hca) (Circuit.CNOT a0 x hxa.symm))))
@[simp] theorem count_topCarrySumBody_toff (x a0 c w_p : Wire n) (hxa : x ≠ a0) (hcx : c ≠ x) (hca :
    c ≠ a0) (hcp : c ≠ w_p) (hxp : x ≠ w_p) (hap : a0 ≠ w_p) : (topCarrySumBody x a0 c w_p hxa hcx
    hca hcp hxp hap).count .TOFF = 0 := by simp [topCarrySumBody]
@[simp] theorem count_topCarrySumBody_t (x a0 c w_p : Wire n) (hxa : x ≠ a0) (hcx : c ≠ x) (hca : c
    ≠ a0) (hcp : c ≠ w_p) (hxp : x ≠ w_p) (hap : a0 ≠ w_p) : (topCarrySumBody x a0 c w_p hxa hcx hca
    hcp hxp hap).count .T = 9 := by simp [topCarrySumBody]
theorem evolve_topCarrySumBody_ket (x a0 c w_p : Wire n) (hxa : x ≠ a0) (hcx : c ≠ x) (hca : c ≠ a0)
    (hcp : c ≠ w_p) (hxp : x ≠ w_p) (hap : a0 ≠ w_p) (β : BitAssignment n) : (topCarrySumBody x a0 c
    w_p hxa hcx hca hcp hxp hap).eval.1.mulVec (UnsignedGivens.ket β) =
      (UnsignedGivens.omega8 ^ (((β x + β c) * (β a0
    + β c) + β c) + β w_p).val) • UnsignedGivens.ket (Function.update β x (β x + β c + β a0)) := by
  dsimp only [topCarrySumBody]
  simp only [UnsignedGivens.eval_seq_mulVec, UnsignedGivens.evolve_CNOT_ket]
  rw [Function.update_of_ne hxa.symm, Function.update_of_ne hcx, Function.update_of_ne hap.symm,
    Function.update_of_ne hxp.symm, Function.update_of_ne hca, Function.update_of_ne hcx]
  set β₁ := Function.update (Function.update (Function.update β x (β x + β c)) a0 (β a0 + β c)) w_p
    (β w_p + β c)
  have h1x : β₁ x = β x + β c := by simp [β₁, Function.update_of_ne hxp, Function.update_of_ne hxa]
  have h1a : β₁ a0 = β a0 + β c := by simp [β₁, Function.update_of_ne hap]
  have h1p : β₁ w_p = β w_p + β c := by simp [β₁]
  have h1c : β₁ c = β c := by
    simp [β₁, Function.update_of_ne hcp, Function.update_of_ne hca, Function.update_of_ne hcx]
  rw [evolveRccxPhaseTKick_ket x a0 w_p hxp hap β₁]
  simp only [Matrix.mulVec_smul, UnsignedGivens.evolve_CNOT_ket]
  have hph : β₁ x * β₁ a0 + β₁ w_p = ((β x + β c) * (β a0 + β c) + β c) + β w_p := by
    rw [h1x, h1a, h1p]
    ring
  rw [hph]
  congr 1
  rw [h1p, h1c, UnsignedGivens.zmod2_add_cancel_right]
  set γ₁ := Function.update β₁ w_p (β w_p)
  have hγ1a : γ₁ a0 = β a0 + β c := by simp [γ₁, Function.update_of_ne hap, h1a]
  have hγ1c : γ₁ c = β c := by simp [γ₁, Function.update_of_ne hcp, h1c]
  rw [hγ1a, hγ1c, UnsignedGivens.zmod2_add_cancel_right]
  set γ₂ := Function.update γ₁ a0 (β a0)
  have hγ2x : γ₂ x = β x + β c := by
    simp [γ₂, γ₁, Function.update_of_ne hxa, Function.update_of_ne hxp, h1x]
  have hγ2a : γ₂ a0 = β a0 := by simp [γ₂]
  rw [hγ2x, hγ2a]
  apply congrArg UnsignedGivens.ket
  funext w
  rcases eq_or_ne w x with rfl | hwx
  · simp
  · rcases eq_or_ne w a0 with rfl | hwa
    · simp [γ₂, hwx]
    · rcases eq_or_ne w w_p with rfl | hwp
      · simp [γ₂, γ₁, hwx, hwa]
      · simp [γ₂, γ₁, β₁, hwx, hwa, hwp]
/-- Forward carry-compute body at streamed bit `j < B - 1` using `a0` and `rC[j]` (`4 T`). -/
def topZeroFwdDyn (hB : 2 ≤ B) (rCat : QRegister B n) (a0 : Wire n) (rC : QRegister (B - 1) n) (w_p
    : Wire n) (hd : TopZeroGidneyDisjoint rCat a0 rC w_p) (j : ℕ) (hjb : j < B - 1) : DynamicCircuit
    Var n :=
  let jfCat : Fin B := ⟨j, by omega⟩
  let jfC : Fin (B - 1) := ⟨j, hjb⟩
  if h0 : 0 < j then
    let jprev : Fin (B - 1) := ⟨j - 1, by omega⟩
    have hpne : jprev ≠ jfC := fin_pred_ne h0 hjb
    .seq (.circuit (Circuit.seq (Circuit.CNOT (rC jprev) (rCat jfCat) (hd.ne_cat_C jfCat
      jprev).symm) (Circuit.CNOT (rC jprev) a0 (hd.ne_a0_C jprev).symm))) (.seq
      (DynamicCircuit.andCompute (rCat jfCat) a0 (rC jfC) (hd.ne_cat_C jfCat jfC) (hd.ne_a0_C jfC))
      (.circuit (Circuit.seq (Circuit.CNOT (rC jprev) (rC jfC)
        (UnsignedGivens.GidneyKickDisjoint.ne_C_C rC
      hpne)) (Circuit.seq (Circuit.CNOT (rC jprev) a0 (hd.ne_a0_C jprev).symm) (Circuit.CNOT (rC
      jprev) (rCat jfCat) (hd.ne_cat_C jfCat jprev).symm)))))
  else DynamicCircuit.andCompute (rCat jfCat) a0 (rC jfC) (hd.ne_cat_C jfCat jfC) (hd.ne_a0_C jfC)
/-- Reference pure `Circuit n` for `topZeroFwdDyn`. -/
def topZeroFwdRef (hB : 2 ≤ B) (rCat : QRegister B n) (a0 : Wire n) (rC : QRegister (B - 1) n) (w_p
    : Wire n) (hd : TopZeroGidneyDisjoint rCat a0 rC w_p) (j : ℕ) (hjb : j < B - 1) : Circuit n :=
  let jfCat : Fin B := ⟨j, by omega⟩
  let jfC : Fin (B - 1) := ⟨j, hjb⟩
  if h0 : 0 < j then
    let jprev : Fin (B - 1) := ⟨j - 1, by omega⟩
    have hpne : jprev ≠ jfC := fin_pred_ne h0 hjb
    Circuit.seq (gFwd4 (rCat jfCat) a0 (rC jfC) (rC jprev) (hd.ne_cat_a0 jfCat) (hd.ne_cat_C jfCat
        jfC) (hd.ne_a0_C jfC) (hd.ne_cat_C jfCat jprev) (hd.ne_a0_C jprev)
        (UnsignedGivens.GidneyKickDisjoint.ne_C_C rC hpne).symm) (Circuit.seq (Circuit.CNOT
          (rC jprev) a0
        (hd.ne_a0_C jprev).symm) (Circuit.CNOT (rC jprev) (rCat jfCat) (hd.ne_cat_C jfCat
        jprev).symm))
  else Circuit.TOFF (rCat jfCat) a0 (rC jfC) (hd.ne_cat_a0 jfCat) (hd.ne_cat_C jfCat jfC)
    (hd.ne_a0_C jfC)
/-- Backward carry-uncompute and sum body at streamed bit `j < B - 1` (`0 T`, `0 TOFF`). -/
def topZeroBwdDyn (v : Var) (hB : 2 ≤ B) (rCat : QRegister B n) (a0 : Wire n) (rC : QRegister (B -
    1) n) (w_p : Wire n) (hd : TopZeroGidneyDisjoint rCat a0 rC w_p) (j : ℕ) (hjb : j < B - 1) :
    DynamicCircuit Var n :=
  let jfCat : Fin B := ⟨j, by omega⟩
  let jfC : Fin (B - 1) := ⟨j, hjb⟩
  if h0 : 0 < j then
    let jprev : Fin (B - 1) := ⟨j - 1, by omega⟩
    have hpne : jprev ≠ jfC := fin_pred_ne h0 hjb
    .seq (.circuit (Circuit.seq (Circuit.seq (Circuit.CNOT (rC jprev) (rCat jfCat) (hd.ne_cat_C
        jfCat jprev).symm) (Circuit.CNOT (rC jprev) a0 (hd.ne_a0_C jprev).symm)) (Circuit.CNOT (rC
        jprev) (rC jfC) (UnsignedGivens.GidneyKickDisjoint.ne_C_C rC hpne)))) (.seq
        (DynamicCircuit.andUncompute v (rCat jfCat) a0 (rC jfC) (hd.ne_cat_a0 jfCat)) (.circuit
        (Circuit.seq (Circuit.CNOT (rC jprev) a0 (hd.ne_a0_C jprev).symm) (Circuit.CNOT a0 (rCat
        jfCat) (hd.ne_cat_a0 jfCat).symm))))
  else .seq (DynamicCircuit.andUncompute v (rCat jfCat) a0 (rC jfC) (hd.ne_cat_a0 jfCat)) (.circuit
    (Circuit.CNOT a0 (rCat jfCat) (hd.ne_cat_a0 jfCat).symm))
/-- Reference pure `Circuit n` for `topZeroBwdDyn`. -/
def topZeroBwdRef (hB : 2 ≤ B) (rCat : QRegister B n) (a0 : Wire n) (rC : QRegister (B - 1) n) (w_p
    : Wire n) (hd : TopZeroGidneyDisjoint rCat a0 rC w_p) (j : ℕ) (hjb : j < B - 1) : Circuit n :=
  let jfCat : Fin B := ⟨j, by omega⟩
  let jfC : Fin (B - 1) := ⟨j, hjb⟩
  if h0 : 0 < j then
    let jprev : Fin (B - 1) := ⟨j - 1, by omega⟩
    have hpne : jprev ≠ jfC := fin_pred_ne h0 hjb
    Circuit.seq (Circuit.seq (Circuit.CNOT (rC jprev) (rCat jfCat) (hd.ne_cat_C jfCat jprev).symm)
      (Circuit.CNOT (rC jprev) a0 (hd.ne_a0_C jprev).symm)) (gBwd4 (rCat jfCat) a0 (rC jfC) (rC
      jprev) (hd.ne_cat_a0 jfCat) (hd.ne_cat_C jfCat jfC) (hd.ne_a0_C jfC) (hd.ne_a0_C jprev)
      (UnsignedGivens.GidneyKickDisjoint.ne_C_C rC hpne).symm)
  else gBwd3 (rCat jfCat) a0 (rC jfC) (hd.ne_cat_a0 jfCat) (hd.ne_cat_C jfCat jfC) (hd.ne_a0_C jfC)
/-- Streamed low prefix of `k ≤ B - 1` bits wrapping `topCarrySumBody` (`12 * k + 13` `T`). -/
def topZeroPrefixDyn (v : Var) (hB : 2 ≤ B) (rCat : QRegister B n) (a0 : Wire n) (rC : QRegister (B
    - 1) n) (w_p : Wire n) (hd : TopZeroGidneyDisjoint rCat a0 rC w_p) {S_ctrl : Finset (Wire n)}
    (bs : TopZeroPhaseKickBitSteps rCat a0 rC w_p S_ctrl) : (k : ℕ) → k ≤ B - 1 → DynamicCircuit
    Var n
  | 0, _ =>
      let jb : Fin B := ⟨B - 1, by omega⟩
      let jc : Fin (B - 1) := ⟨B - 2, by omega⟩
      (bs.stepLo jb).wrapDynamic v (.circuit (topCarrySumBody (rCat jb) a0 (rC jc) w_p
        (hd.ne_cat_a0 jb) (hd.ne_cat_C jb jc).symm (hd.ne_a0_C jc).symm (hd.ne_C_wp jc)
        (hd.ne_cat_wp jb) hd.ne_a0_wp))
  | k + 1, _ =>
      let j := (B - 1) - (k + 1)
      let jf : Fin B := ⟨j, by omega⟩
      .seq ((bs.stepLo jf).wrapDynamic v (topZeroFwdDyn hB rCat a0 rC w_p hd j (by omega))) (.seq
        (topZeroPrefixDyn v hB rCat a0 rC w_p hd bs k (by omega)) ((bs.stepLo jf).wrapDynamic v
        (topZeroBwdDyn v hB rCat a0 rC w_p hd j (by omega))))
/-- Reference pure `Circuit n` for `topZeroPrefixDyn`. -/
def topZeroPrefixRef (hB : 2 ≤ B) (rCat : QRegister B n) (a0 : Wire n) (rC : QRegister (B - 1) n)
    (w_p : Wire n) (hd : TopZeroGidneyDisjoint rCat a0 rC w_p) {S_ctrl : Finset (Wire n)} (bs :
    TopZeroPhaseKickBitSteps rCat a0 rC w_p S_ctrl) : (k : ℕ) → k ≤ B - 1 → Circuit n
  | 0, _ =>
      let jb : Fin B := ⟨B - 1, by omega⟩
      let jc : Fin (B - 1) := ⟨B - 2, by omega⟩
      (bs.stepLo jb).wrapCircuit (topCarrySumBody (rCat jb) a0 (rC jc) w_p (hd.ne_cat_a0 jb)
        (hd.ne_cat_C jb jc).symm (hd.ne_a0_C jc).symm (hd.ne_C_wp jc) (hd.ne_cat_wp jb)
        hd.ne_a0_wp)
  | k + 1, _ =>
      let j := (B - 1) - (k + 1)
      let jf : Fin B := ⟨j, by omega⟩
      Circuit.seq ((bs.stepLo jf).wrapCircuit (topZeroFwdRef hB rCat a0 rC w_p hd j (by omega)))
          (Circuit.seq (topZeroPrefixRef hB rCat a0 rC w_p hd bs k (by omega)) ((bs.stepLo
          jf).wrapCircuit (topZeroBwdRef hB rCat a0 rC w_p hd j (by omega))))
/-- Zero-top-ancilla `(B + 2)`-bit unsigned phase-kick engine (`12 * B + 10` `T`, `0 TOFF`). -/
def topZeroRawUnsignedPhaseKickDyn (v : Var) (hB : 2 ≤ B) (rCat : QRegister B n) (a0 : Wire n) (rC :
    QRegister (B - 1) n) (w_p : Wire n) (hd : TopZeroGidneyDisjoint rCat a0 rC w_p) {S_ctrl : Finset
    (Wire n)} (bs : TopZeroPhaseKickBitSteps rCat a0 rC w_p S_ctrl) : DynamicCircuit Var n :=
  let kickTop :=
    bs.stepTop.wrapDynamic v (.circuit (Circuit.seq (Circuit.S a0) (UnsignedGivens.czCircuit w_p
    a0 hd.ne_a0_wp.symm)))
  let kickMid :=
    DynamicCircuit.seq (bs.stepMid.wrapDynamic v (.circuit (UnsignedGivens.parityTCircuit a0 w_p
    hd.ne_a0_wp))) (.circuit (UnsignedGivens.sdagCircuit w_p))
  let fan := UnsignedGivens.cnotFanoutReg B w_p rCat (fun j ↦ (hd.ne_cat_wp j).symm)
  let kickLo := DynamicCircuit.seq (.circuit fan) (DynamicCircuit.seq (topZeroPrefixDyn v hB rCat a0
    rC w_p hd bs (B - 1) le_rfl) (.circuit fan))
  DynamicCircuit.seq kickTop (DynamicCircuit.seq kickMid kickLo)
/-- Reference pure `Circuit n` for `topZeroRawUnsignedPhaseKickDyn`. -/
def topZeroRawUnsignedPhaseKickRef (hB : 2 ≤ B) (rCat : QRegister B n) (a0 : Wire n) (rC : QRegister
    (B - 1) n) (w_p : Wire n) (hd : TopZeroGidneyDisjoint rCat a0 rC w_p) {S_ctrl : Finset (Wire n)}
    (bs : TopZeroPhaseKickBitSteps rCat a0 rC w_p S_ctrl) : Circuit n :=
  let kickTop := bs.stepTop.wrapCircuit (Circuit.seq (Circuit.S a0) (UnsignedGivens.czCircuit w_p a0
    hd.ne_a0_wp.symm))
  let kickMid :=
    Circuit.seq (bs.stepMid.wrapCircuit (UnsignedGivens.parityTCircuit a0 w_p hd.ne_a0_wp))
    (UnsignedGivens.sdagCircuit w_p)
  let fan := UnsignedGivens.cnotFanoutReg B w_p rCat (fun j ↦ (hd.ne_cat_wp j).symm)
  let kickLo := Circuit.seq fan (Circuit.seq (topZeroPrefixRef hB rCat a0 rC w_p hd bs (B - 1)
    le_rfl) fan)
  Circuit.seq kickTop (Circuit.seq kickMid kickLo)
theorem count_topZeroFwdBwdDyn (v : Var) (hB : 2 ≤ B) (rCat : QRegister B n) (a0 : Wire n) (rC :
    QRegister (B - 1) n) (w_p : Wire n) (hd : TopZeroGidneyDisjoint rCat a0 rC w_p) (j : ℕ) (hjb :
    j < B - 1) : (topZeroFwdDyn (Var := Var) hB rCat a0 rC w_p hd j hjb).count .TOFF = 0 ∧
    (topZeroFwdDyn (Var := Var) hB rCat a0 rC w_p hd j hjb).count .T = 4 ∧ (topZeroBwdDyn v hB rCat
      a0 rC w_p hd j hjb).count .TOFF = 0 ∧ (topZeroBwdDyn v hB rCat a0 rC w_p hd j hjb).count .T =
      0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · by_cases h0 : 0 < j <;> simp [topZeroFwdDyn, h0, DynamicCircuit.count_andCompute_toff]
  · by_cases h0 : 0 < j <;> simp [topZeroFwdDyn, h0, DynamicCircuit.count_andCompute_t]
  · by_cases h0 : 0 < j <;> simp [topZeroBwdDyn, h0, DynamicCircuit.count_andUncompute_toff]
  · by_cases h0 : 0 < j <;> simp [topZeroBwdDyn, h0, DynamicCircuit.count_andUncompute_t]
theorem count_topZeroPrefixDyn (v : Var) (hB : 2 ≤ B) (rCat : QRegister B n) (a0 : Wire n) (rC :
    QRegister (B - 1) n) (w_p : Wire n) (hd : TopZeroGidneyDisjoint rCat a0 rC w_p) {S_ctrl : Finset
    (Wire n)} (bs : TopZeroPhaseKickBitSteps rCat a0 rC w_p S_ctrl) (k : ℕ) (hk : k ≤ B - 1) :
    (topZeroPrefixDyn v hB rCat a0 rC w_p hd bs k hk).count .TOFF = 0 ∧ (topZeroPrefixDyn v hB rCat
    a0 rC w_p hd bs k hk).count .T = 12 * k + 13 := by
  induction k with
  | zero =>
      refine ⟨?_, ?_⟩
      · dsimp only [topZeroPrefixDyn]
        rw [UnsignedGivens.PhasedStep.count_wrapDynamic_toff _ _ _ (bs.cleanLo _).clifford]
        simp [DynamicCircuit.count]
      · dsimp only [topZeroPrefixDyn]
        rw [UnsignedGivens.PhasedStep.count_wrapDynamic_t _ _ _ (bs.cleanLo _).clifford]
        simp [DynamicCircuit.count]
  | succ k ih =>
      obtain ⟨h0, h1⟩ := ih (by omega)
      obtain ⟨hf0, hf1, hb0, hb1⟩ := count_topZeroFwdBwdDyn v hB rCat a0 rC w_p hd ((B - 1) - (k +
        1)) (by omega)
      refine ⟨?_, ?_⟩
      · dsimp only [topZeroPrefixDyn, DynamicCircuit.count]
        rw [UnsignedGivens.PhasedStep.count_wrapDynamic_toff _ _ _ (bs.cleanLo _).clifford,
          UnsignedGivens.PhasedStep.count_wrapDynamic_toff _ _ _ (bs.cleanLo _).clifford, hf0, hb0,
            h0]
      · dsimp only [topZeroPrefixDyn, DynamicCircuit.count]
        rw [UnsignedGivens.PhasedStep.count_wrapDynamic_t _ _ _ (bs.cleanLo _).clifford,
          UnsignedGivens.PhasedStep.count_wrapDynamic_t _ _ _ (bs.cleanLo _).clifford, hf1, hb1, h1]
        omega
@[simp] theorem count_topZeroRawUnsignedPhaseKickDyn_toff (v : Var) (hB : 2 ≤ B) (rCat : QRegister B
    n) (a0 : Wire n) (rC : QRegister (B - 1) n) (w_p : Wire n) (hd : TopZeroGidneyDisjoint rCat a0
    rC w_p) {S_ctrl : Finset (Wire n)} (bs : TopZeroPhaseKickBitSteps rCat a0 rC w_p S_ctrl) :
    (topZeroRawUnsignedPhaseKickDyn v hB rCat a0 rC w_p hd bs).count .TOFF = 0 := by
  dsimp only [topZeroRawUnsignedPhaseKickDyn, DynamicCircuit.count]
  rw [UnsignedGivens.PhasedStep.count_wrapDynamic_toff _ _ _ bs.cleanTop.clifford,
    UnsignedGivens.PhasedStep.count_wrapDynamic_toff _ _ _ bs.cleanMid.clifford,
      (count_topZeroPrefixDyn v hB
    rCat a0 rC w_p hd bs (B - 1) le_rfl).1]
  simp [DynamicCircuit.count]
@[simp] theorem count_topZeroRawUnsignedPhaseKickDyn_t (v : Var) (hB : 2 ≤ B) (rCat : QRegister B n)
    (a0 : Wire n) (rC : QRegister (B - 1) n) (w_p : Wire n) (hd : TopZeroGidneyDisjoint rCat a0 rC
    w_p) {S_ctrl : Finset (Wire n)} (bs : TopZeroPhaseKickBitSteps rCat a0 rC w_p S_ctrl) :
    (topZeroRawUnsignedPhaseKickDyn v hB rCat a0 rC w_p hd bs).count .T = 8 * B + 10 + 4 * B := by
  dsimp only [topZeroRawUnsignedPhaseKickDyn, DynamicCircuit.count]
  rw [UnsignedGivens.PhasedStep.count_wrapDynamic_t _ _ _ bs.cleanTop.clifford,
    UnsignedGivens.PhasedStep.count_wrapDynamic_t _ _ _ bs.cleanMid.clifford,
      (count_topZeroPrefixDyn v hB
    rCat a0 rC w_p hd bs (B - 1) le_rfl).2]
  have htop :
    (Circuit.seq (Circuit.S a0) (UnsignedGivens.czCircuit w_p a0 hd.ne_a0_wp.symm)).count .T = 0 :=
      by
    simp
  have hmid : (UnsignedGivens.parityTCircuit a0 w_p hd.ne_a0_wp).count .T = 1 :=
    UnsignedGivens.count_parityTCircuit_t
    _ _ _
  have hsd : (UnsignedGivens.sdagCircuit w_p).count .T = 0 := UnsignedGivens.count_sdagCircuit_t _
  have hfan : (UnsignedGivens.cnotFanoutReg B w_p rCat (fun j ↦
    (hd.ne_cat_wp j).symm)).count .T = 0 :=
    UnsignedGivens.count_cnotFanoutReg_t _ _ _ _
  dsimp only [DynamicCircuit.count]
  rw [htop, hmid, hsd, hfan]
  omega
theorem topZeroFwdBwdRef_perm (hB : 2 ≤ B) (rCat : QRegister B n) (a0 : Wire n) (rC : QRegister (B
    - 1) n) (w_p : Wire n) (hd : TopZeroGidneyDisjoint rCat a0 rC w_p) (j : ℕ) (hjb : j < B - 1) :
    let jfCat : Fin B := ⟨j, by omega⟩
    let jfC : Fin (B - 1) := ⟨j, hjb⟩
    let cp (β : BitAssignment n) : ZMod 2 := if h0 : 0 < j then β (rC ⟨j - 1, by omega⟩) else 0
    let δ (β : BitAssignment n) : ZMod 2 := (β (rCat jfCat) + cp β) * (β a0 + cp β) + cp β
    UnsignedGivens.PhasedPerm (topZeroFwdRef hB rCat a0 rC w_p hd j hjb) (fun _ ↦ 1) (fun β ↦
      Function.update β (rC jfC) (β (rC jfC) + δ β)) ∧
    UnsignedGivens.PhasedPerm (topZeroBwdRef hB rCat a0 rC w_p hd j hjb) (fun _ ↦ 1) (fun β ↦
      Function.update (Function.update β (rC jfC) (β (rC jfC) + δ β)) (rCat jfCat) (β (rCat jfCat)
      + cp β + β a0)) := by
  intro jfCat jfC cp δ
  refine ⟨fun β ↦ ?_, fun β ↦ ?_⟩
  · rw [one_smul]
    dsimp only [topZeroFwdRef, cp, δ, jfCat, jfC]
    by_cases h0 : 0 < j
    · simp only [h0, ↓reduceDIte]
      exact evolve_gidneyFwd4_ket _ _ _ _ _ _ _ _ _ _ β
    · simp only [h0, ↓reduceDIte, add_zero, UnsignedGivens.evolve_TOFF_ket]
  · rw [one_smul]
    dsimp only [topZeroBwdRef, cp, δ, jfCat, jfC]
    by_cases h0 : 0 < j
    · simp only [h0, ↓reduceDIte]
      exact evolve_gidneyBwd4_ket _ _ _ _ _ _ _ (hd.ne_cat_C _ _) _ _ β _
        (UnsignedGivens.zmod2_add_cancel_right _ _).symm
    · simp only [h0, ↓reduceDIte, add_zero]
      rw [evolve_gBwd3_ket _ _ _ _ _ _ β _ _ _ rfl rfl
        (UnsignedGivens.zmod2_add_cancel_right _ _).symm]
      apply congrArg UnsignedGivens.ket
      funext w
      rcases eq_or_ne w (rCat ⟨j, by omega⟩) with rfl | hwy
      · simp
      · rcases eq_or_ne w a0 with rfl | hwa
        · simp [hwy, Function.update_of_ne (hd.ne_a0_C _)]
        · simp [hwy, hwa]
theorem topZeroPrefixRef_spec (hB : 2 ≤ B) (rCat : QRegister B n) (a0 : Wire n) (rC : QRegister (B -
    1) n) (w_p : Wire n) (hd : TopZeroGidneyDisjoint rCat a0 rC w_p) {S_ctrl : Finset (Wire n)} (bs
    : TopZeroPhaseKickBitSteps rCat a0 rC w_p S_ctrl) (k : ℕ) (hk : k ≤ B - 1) : ∃ (φ :
    BitAssignment n → ℂ) (f : BitAssignment n → BitAssignment n),
      UnsignedGivens.PhasedPerm (topZeroPrefixRef
    hB rCat a0 rC w_p hd bs k hk) φ f ∧ (∀ β (w : Wire n), (∀ m : Fin B, (B - 1) - k ≤ m.val → w ≠
    rCat m) → f β w = β w) ∧ (∀ β (yc a : ℕ), yc < 2 ^ B → a < 2 ^ B → (∀ m : Fin B, (B - 1) - k ≤
    m.val → β (rCat m) = ((yc / 2 ^ m.val % 2 : ℕ) : ZMod 2)) → β a0 = 0 → (∀ m : Fin B, (B - 1) - k
    ≤ m.val → bs.bitLo β m = ((a / 2 ^ m.val % 2 : ℕ) : ZMod 2)) → (∀ m : Fin (B - 1), (B - 1) - k ≤
    m.val → β (rC m) = 0) → (∀ _h0 : 0 < (B - 1) - k, β (rC ⟨(B - 1) - k - 1, by omega⟩) =
    ((UnsignedGivens.carryAt yc a ((B - 1) - k) : ℕ) : ZMod 2)) → φ β =
      UnsignedGivens.omega8 ^ ((((yc + a) / 2 ^ B :
    ℕ) : ZMod 2) + β w_p).val ∧ ∀ m : Fin B, (B - 1) - k ≤ m.val → f β (rCat m) = (((yc + a) / 2 ^
    m.val % 2 : ℕ) : ZMod 2)) := by
  induction k with
  | zero =>
      let jb : Fin B := ⟨B - 1, by omega⟩
      let jc : Fin (B - 1) := ⟨B - 2, by omega⟩
      let s := bs.stepLo jb
      have hs_anc : s.anc = a0 := bs.ancLo jb
      have hcat_nc : rCat jb ∉ S_ctrl := fun hm ↦ Finset.disjoint_left.mp bs.disj_ctrl_cat hm
        (QRegister.mem_image rCat _ |>.mpr ⟨jb, rfl⟩)
      let cBody := topCarrySumBody (rCat jb) a0 (rC jc) w_p (hd.ne_cat_a0 jb) (hd.ne_cat_C jb
        jc).symm (hd.ne_a0_C jc).symm (hd.ne_C_wp jc) (hd.ne_cat_wp jb) hd.ne_a0_wp
      let φ_body (γ : BitAssignment n) : ℂ :=
        UnsignedGivens.omega8 ^ (((γ (rCat jb) + γ (rC jc)) * (γ a0 + γ
        (rC jc)) + γ (rC jc)) + γ w_p).val
      let f_body (γ : BitAssignment n) : BitAssignment n := Function.update γ (rCat jb) (γ (rCat jb)
        + γ (rC jc) + γ a0)
      have hperm_body : UnsignedGivens.PhasedPerm cBody φ_body f_body := fun γ ↦
        evolve_topCarrySumBody_ket
        _ _ _ _ _ _ _ _ _ _ γ
      let f_out (β : BitAssignment n) : BitAssignment n := Function.update β (rCat jb) (β (rCat jb)
        + β (rC jc) + (β a0 + bs.bitLo β jb))
      have hperm_out : UnsignedGivens.PhasedPerm (s.wrapCircuit cBody) (fun β ↦
        φ_body (Function.update β
        s.anc (β s.anc + bs.bitLo β jb))) f_out := cleanWrap_perm_of_eq (bs.cleanLo jb) hperm_body
        (fun γ ↦ update_ne_of_eq hs_anc (hd.ne_cat_a0 jb).symm γ _) (fun _ _ hw ↦
        update_of_mem_not_mem hw hcat_nc _ _)
          (fun β ↦ by
            dsimp only [f_body, f_out]
            rw [hs_anc, Function.update_of_ne (hd.ne_cat_a0 jb), Function.update_of_ne (hd.ne_a0_C
              jc).symm, Function.update_self]
            funext w
            rcases eq_or_ne w a0 with rfl | hwa
            · simp [Function.update_of_ne (hd.ne_cat_a0 jb).symm]
            · rcases eq_or_ne w (rCat jb) with rfl | hwx
              · simp [hwa]
              · simp [hwa, hwx])
      have hjb_ge : (B - 1) - 0 ≤ jb.val := by dsimp [jb]
                                               omega
      refine ⟨_, f_out, hperm_out, ?_, ?_⟩
      · intro β w hw
        exact Function.update_of_ne (hw jb hjb_ge) _ _
      · intro β yc a hyc ha hcat ha0 hbit _ hprev
        have hc_prev : β (rC jc) = ((UnsignedGivens.carryAt yc a (B - 1) : ℕ) : ZMod 2) := by
          have hp0 := hprev (by omega : 0 < (B - 1) - 0)
          have hjc_eq : (⟨(B - 1) - 0 - 1, by omega⟩ : Fin (B - 1)) = jc := by ext
                                                                               dsimp [jc]
                                                                               omega
          rwa [hjc_eq, Nat.sub_zero] at hp0
        have hcat_jb : β (rCat jb) = ((yc / 2 ^ (B - 1) % 2 : ℕ) : ZMod 2) := hcat jb hjb_ge
        have hbit_jb : bs.bitLo β jb = ((a / 2 ^ (B - 1) % 2 : ℕ) : ZMod 2) := hbit jb hjb_ge
        have hmaj : (β (rCat jb) + β (rC jc)) * (bs.bitLo β jb + β (rC jc)) + β (rC jc) = (((yc + a)
            / 2 ^ B : ℕ) : ZMod 2) := by
          rw [hcat_jb, hbit_jb, hc_prev, add_comm _ ((UnsignedGivens.carryAt yc a (B - 1) : ℕ) :
            ZMod 2),
            ← UnsignedGivens.carryAt_of_lt hyc ha, show B = (B - 1) + 1 by
              omega, UnsignedGivens.carryAt_succ]
          exact UnsignedGivens.gidney_maj_zmod2 (UnsignedGivens.carryAt_lt_two yc a (B -
            1)) (Nat.mod_lt _ (by omega))
            (Nat.mod_lt _ (by omega))
        refine ⟨?_, fun m hm ↦ ?_⟩
        · dsimp only [φ_body]
          rw [hs_anc, ha0, zero_add, Function.update_of_ne (hd.ne_cat_a0 jb), Function.update_of_ne
            (hd.ne_a0_C jc).symm, Function.update_self, Function.update_of_ne hd.ne_a0_wp.symm,
            hmaj]
        · have hm_eq : m = jb := Fin.ext (by
            have := m.isLt
            dsimp [jb]
            omega)
          rw [hm_eq]
          dsimp only [f_out]
          rw [Function.update_self, hcat_jb, hc_prev, ha0, zero_add, hbit_jb]
          simpa only [jb,
            UnsignedGivens.add_div_pow_mod_two] using UnsignedGivens.gidney_sum_zmod2
            (UnsignedGivens.carryAt yc
            a (B - 1)) (yc / 2 ^ (B - 1) % 2) (a / 2 ^ (B - 1) % 2)
  | succ k ih =>
      obtain ⟨φ_in, f_in, hperm_in, hfix_in, hval_in⟩ := ih (by omega)
      let j := (B - 1) - (k + 1)
      have hjb : j < B - 1 := by omega
      let jfCat : Fin B := ⟨j, by omega⟩
      let jfC : Fin (B - 1) := ⟨j, hjb⟩
      let s := bs.stepLo jfCat
      have hs_anc : s.anc = a0 := bs.ancLo jfCat
      have hC_nc : rC jfC ∉ S_ctrl := fun hm ↦ Finset.disjoint_left.mp bs.disj_ctrl_C hm
        (QRegister.mem_image rC _ |>.mpr ⟨jfC, rfl⟩)
      have hcat_nc : rCat jfCat ∉ S_ctrl := fun hm ↦ Finset.disjoint_left.mp bs.disj_ctrl_cat hm
        (QRegister.mem_image rCat _ |>.mpr ⟨jfCat, rfl⟩)
      let cp (γ : BitAssignment n) : ZMod 2 := if h0 : 0 < j then γ (rC ⟨j - 1, by omega⟩) else 0
      let a_eff (γ : BitAssignment n) : ZMod 2 := γ a0 + bs.bitLo γ jfCat
      let δc (γ : BitAssignment n) : ZMod 2 := (γ (rCat jfCat) + cp γ) * (a_eff γ + cp γ) + cp γ
      let β₁ (β : BitAssignment n) := Function.update β (rC jfC) (β (rC jfC) + δc β)
      let f_bwd (γ : BitAssignment n) := Function.update (Function.update γ (rC jfC) (γ (rC jfC) +
        ((γ (rCat jfCat) + cp γ) * (γ a0 + cp γ) + cp γ))) (rCat jfCat) (γ (rCat jfCat) + cp γ + γ
        a0)
      have hjf_ge : (B - 1) - (k + 1) ≤ jfCat.val := le_rfl
      have hjfC_ge : (B - 1) - (k + 1) ≤ jfC.val := le_rfl
      have hpermFB := topZeroFwdBwdRef_perm hB rCat a0 rC w_p hd j hjb
      have hperm_wrapF :
        UnsignedGivens.PhasedPerm (s.wrapCircuit (topZeroFwdRef hB rCat a0 rC w_p hd j
        hjb)) (fun _ ↦ 1) β₁ := cleanWrap_perm_of_eq (bs.cleanLo jfCat) hpermFB.1 (fun β ↦
        update_ne_of_eq hs_anc (hd.ne_a0_C jfC) β _) (fun _ _ hw ↦ update_of_mem_not_mem hw
        hC_nc _ _)
          (fun β ↦ by
            dsimp only
            rw [hs_anc]
            let γ := Function.update β a0 (β a0 + bs.bitLo β jfCat)
            have hγ_a0 : γ a0 = β a0 + bs.bitLo β jfCat := Function.update_self _ _ _
            have hγ_C : γ (rC jfC) = β (rC jfC) := Function.update_of_ne (hd.ne_a0_C jfC).symm _ _
            have hγ_cat : γ (rCat jfCat) = β (rCat jfCat) := Function.update_of_ne (hd.ne_cat_a0
              jfCat) _ _
            have hγ_cp : (if h0 : 0 < j then γ (rC ⟨j - 1, by omega⟩) else 0) = cp β := by
              by_cases h0 : 0 < j
              · simp [cp, γ, h0, Function.update_of_ne (hd.ne_a0_C _).symm]
              · simp [cp, h0]
            change Function.update (Function.update γ (rC jfC) (γ (rC jfC) + ((γ (rCat jfCat) +
                  if h0 : 0 < j then γ (rC ⟨j - 1, by omega⟩) else 0) *
                  (γ a0 + if h0 : 0 < j then γ (rC ⟨j - 1, by omega⟩) else 0) +
                  if h0 : 0 < j then γ (rC ⟨j - 1, by omega⟩) else 0)))
                a0 (β a0) = β₁ β
            rw [hγ_C, hγ_cat, hγ_a0, hγ_cp]
            funext w
            rcases eq_or_ne w (rC jfC) with rfl | hwc
            · simp [β₁, δc, a_eff, (hd.ne_a0_C jfC).symm]
            · rcases eq_or_ne w a0 with rfl | hwa
              · simp [β₁, hwc]
              · simp [γ, β₁, hwc, hwa])
      let f_wrapB (γ : BitAssignment n) := Function.update (f_bwd (Function.update γ s.anc (γ s.anc
        + bs.bitLo γ jfCat))) s.anc (γ s.anc)
      have hperm_wrapB :
        UnsignedGivens.PhasedPerm (s.wrapCircuit (topZeroBwdRef hB rCat a0 rC w_p hd j
        hjb)) (fun _ ↦ 1) f_wrapB := cleanWrap_perm_of_eq (bs.cleanLo jfCat) hpermFB.2
          (fun β ↦ by
            dsimp only [f_bwd]
            rw [hs_anc, Function.update_of_ne (hd.ne_cat_a0 jfCat).symm, Function.update_of_ne
              (hd.ne_a0_C jfC)])
          (fun _ _ hw ↦ (update_of_mem_not_mem hw hcat_nc _ _).trans (update_of_mem_not_mem hw
              hC_nc _ _))
          (fun _ ↦ rfl)
      let f_out (β : BitAssignment n) := Function.update (Function.update (f_in (β₁ β)) (rC jfC) (β
        (rC jfC))) (rCat jfCat) (β (rCat jfCat) + cp β + a_eff β)
      have hfB_eq (β : BitAssignment n) : f_wrapB (f_in (β₁ β)) = f_out β := by
        have hγ_cat : f_in (β₁ β) (rCat jfCat) = β (rCat jfCat) := by
          rw [hfix_in (β₁ β) (rCat jfCat) fun m hm h ↦ by
            have := congrArg Fin.val (rCat.wires.injective h)
            dsimp [jfCat] at this
            omega]
          exact Function.update_of_ne (hd.ne_cat_C jfCat jfC) _ _
        have hγ_a0 : f_in (β₁ β) a0 = β a0 := by
          rw [hfix_in (β₁ β) a0 fun m _ ↦ (hd.ne_cat_a0 m).symm]
          exact Function.update_of_ne (hd.ne_a0_C jfC) _ _
        have hγ_C : f_in (β₁ β) (rC jfC) = β (rC jfC) + δc β := by
          rw [hfix_in (β₁ β) (rC jfC) fun m _ ↦ (hd.ne_cat_C m jfC).symm]
          exact Function.update_self _ _ _
        have hγ_bit : bs.bitLo (f_in (β₁ β)) jfCat = bs.bitLo β jfCat :=
          (bs.cleanLo jfCat).bitVal_congr (f_in (β₁ β)) β fun w hw ↦ by
            rw [hfix_in (β₁ β) w fun m _ hm ↦ Finset.disjoint_left.mp bs.disj_ctrl_cat hw
              (QRegister.mem_image rCat _ |>.mpr ⟨m, hm.symm⟩)]
            have hC_ne : w ≠ rC jfC := fun h ↦ by rw [h] at hw
                                                  exact hC_nc hw
            exact Function.update_of_ne hC_ne _ _
        have hcp_γ : cp (Function.update (f_in (β₁ β)) a0 (f_in (β₁ β) a0 + bs.bitLo (f_in (β₁ β))
            jfCat)) = cp β := by
          by_cases h0 : 0 < j
          · simp only [cp, h0, ↓reduceDIte, Function.update_of_ne (hd.ne_a0_C _).symm]
            rw [hfix_in (β₁ β) (rC ⟨j - 1, by omega⟩) fun m _ ↦ (hd.ne_cat_C m _).symm]
            exact Function.update_of_ne (UnsignedGivens.GidneyKickDisjoint.ne_C_C rC (by
                intro h
                have := congrArg Fin.val h
                dsimp [jfC] at this
                omega)) _ _
          · simp [cp, h0]
        dsimp only [f_wrapB, f_bwd]
        rw [hs_anc, Function.update_self, Function.update_of_ne (hd.ne_a0_C jfC).symm,
          Function.update_of_ne (hd.ne_cat_a0 jfCat), hcp_γ, hγ_cat, hγ_a0, hγ_bit, hγ_C]
        change Function.update (Function.update (Function.update (Function.update (f_in (β₁ β)) a0
            (a_eff β)) (rC jfC) (β (rC jfC) + δc β + δc β)) (rCat jfCat) (β (rCat jfCat) + cp β +
            a_eff β)) a0 (β a0) = f_out β
        rw [UnsignedGivens.zmod2_add_cancel_right]
        funext w
        rcases eq_or_ne w a0 with rfl | hwa
        · dsimp only [f_out]
          rw [Function.update_self, Function.update_of_ne (hd.ne_cat_a0 jfCat).symm,
            Function.update_of_ne (hd.ne_a0_C jfC)]
          exact hγ_a0.symm
        · rcases eq_or_ne w (rCat jfCat) with rfl | hwy
          · dsimp only [f_out]
            simp [hwa]
          · rcases eq_or_ne w (rC jfC) with rfl | hwc
            · dsimp only [f_out]
              simp [hwa, hwy]
            · dsimp only [f_out]
              simp [hwa, hwy, hwc]
      refine ⟨fun β ↦ φ_in (β₁ β), f_out, ?_, ?_, ?_⟩
      · intro β
        dsimp only [topZeroPrefixRef]
        simp only [UnsignedGivens.eval_seq_mulVec]
        rw [hperm_wrapF β, one_smul, hperm_in (β₁ β), Matrix.mulVec_smul, hperm_wrapB (f_in (β₁ β)),
          one_smul, hfB_eq β]
      · intro β w hw
        dsimp only [f_out]
        have hne_cat : w ≠ rCat jfCat := hw jfCat hjf_ge
        rw [Function.update_of_ne hne_cat]
        by_cases hwc : w = rC jfC
        · subst hwc
          simp
        · rw [Function.update_of_ne hwc, hfix_in _ w fun m hm ↦ hw m (by omega)]
          simp [β₁, hwc]
      · intro β yc a hyc ha hcat ha0 hbit hC hprev
        have hcp_val : cp β = ((UnsignedGivens.carryAt yc a j : ℕ) : ZMod 2) := by
          by_cases h0 : 0 < j
          · simpa only [cp, h0, ↓reduceDIte] using hprev h0
          · have hj0 : j = 0 := by omega
            simp [cp, hj0]
        have ha_eff : a_eff β = ((a / 2 ^ j % 2 : ℕ) : ZMod 2) := by
          dsimp only [a_eff]
          rw [ha0, zero_add, hbit jfCat hjf_ge]
        have hcat_jf : β (rCat jfCat) = ((yc / 2 ^ j % 2 : ℕ) : ZMod 2) := hcat jfCat hjf_ge
        have hC_jf : β (rC jfC) = 0 := hC jfC hjfC_ge
        have hcarry_next : β₁ β (rC jfC) = ((UnsignedGivens.carryAt yc a (j + 1) : ℕ) :
            ZMod 2) := by
          dsimp only [β₁, δc]
          rw [Function.update_self, hC_jf, zero_add, hcat_jf, ha_eff, hcp_val, add_comm _
            ((UnsignedGivens.carryAt yc a j : ℕ) : ZMod 2), UnsignedGivens.carryAt_succ]
          exact UnsignedGivens.gidney_maj_zmod2 (UnsignedGivens.carryAt_lt_two yc a j) (Nat.mod_lt _
            (by omega))
            (Nat.mod_lt _ (by omega))
        have hin := hval_in (β₁ β) yc a hyc ha
          (fun m hm ↦ by
            dsimp only [β₁]
            rw [Function.update_of_ne (hd.ne_cat_C m jfC)]
            exact hcat m (by omega))
          (by
            dsimp only [β₁]
            rw [Function.update_of_ne (hd.ne_a0_C jfC), ha0])
          (fun m hm ↦ by
            rw [(bs.cleanLo m).bitVal_congr (β₁ β) β fun w hw ↦ by
              have hC_ne : w ≠ rC jfC := fun h ↦ by rw [h] at hw
                                                    exact hC_nc hw
              exact Function.update_of_ne hC_ne _ _]
            exact hbit m (by omega))
          (fun m hm ↦ by
            have hne : rC m ≠ rC jfC := fun h ↦ by have := congrArg Fin.val (rC.wires.injective h)
                                                   dsimp [jfC] at this
                                                   omega
            dsimp only [β₁]
            rw [Function.update_of_ne hne]
            exact hC m (by omega))
          (fun _ ↦ by
            have hidx : (⟨(B - 1) - k - 1, by omega⟩ : Fin (B - 1)) = jfC := by ext
                                                                                dsimp [jfC]
                                                                                omega
            have hdk : (B - 1) - k = j + 1 := by omega
            rw [hidx, hdk]
            exact hcarry_next)
        have hwp₁ : β₁ β w_p = β w_p := Function.update_of_ne (hd.ne_C_wp jfC).symm _ _
        refine ⟨?_, fun m hm ↦ ?_⟩
        · dsimp only
          rw [hin.1, hwp₁]
        · by_cases hmj : m.val = j
          · have hm_eq : m = jfCat := Fin.ext hmj
            rw [hm_eq]
            dsimp only [f_out]
            rw [Function.update_self, hcp_val, hcat_jf, ha_eff]
            simpa only [jfCat,
              UnsignedGivens.add_div_pow_mod_two] using UnsignedGivens.gidney_sum_zmod2
              (UnsignedGivens.carryAt yc a j) (yc / 2 ^ j % 2) (a / 2 ^ j % 2)
          · have hcat_ne : rCat m ≠ rCat jfCat := fun h ↦ hmj (congrArg Fin.val
              (rCat.wires.injective h))
            dsimp only [f_out]
            rw [Function.update_of_ne hcat_ne, Function.update_of_ne (hd.ne_cat_C m jfC)]
            exact hin.2 m (by omega)
theorem SubspaceStepU_topZeroFwdDyn [Fintype Var] [DecidableEq Var] (hB : 2 ≤ B) (rCat : QRegister B
    n) (a0 : Wire n) (rC : QRegister (B - 1) n) (w_p : Wire n) (hd : TopZeroGidneyDisjoint rCat a0
    rC w_p) (j : ℕ) (hjb : j < B - 1) {R₀ : Operator (2 ^ n)} (hC0 : ZeroOnWire (rC ⟨j, hjb⟩) R₀) :
    SubspaceStepU R₀ ((topZeroFwdRef hB rCat a0 rC w_p hd j hjb).eval.1 * R₀) (topZeroFwdDyn (Var :=
    Var) hB rCat a0 rC w_p hd j hjb) := by
  let jfCat : Fin B := ⟨j, by omega⟩
  let jfC : Fin (B - 1) := ⟨j, hjb⟩
  dsimp only [topZeroFwdDyn, topZeroFwdRef]
  by_cases h0 : 0 < j
  · simp only [h0, ↓reduceDIte]
    let jprev : Fin (B - 1) := ⟨j - 1, by omega⟩
    have hpne : jprev ≠ jfC := fin_pred_ne h0 hjb
    let cPre := Circuit.seq (Circuit.CNOT (rC jprev) (rCat jfCat) (hd.ne_cat_C jfCat jprev).symm)
      (Circuit.CNOT (rC jprev) a0 (hd.ne_a0_C jprev).symm)
    let cPost :=
      Circuit.seq (Circuit.CNOT (rC jprev) (rC jfC) (UnsignedGivens.GidneyKickDisjoint.ne_C_C rC
      hpne)) (Circuit.seq (Circuit.CNOT (rC jprev) a0 (hd.ne_a0_C jprev).symm) (Circuit.CNOT (rC
      jprev) (rCat jfCat) (hd.ne_cat_C jfCat jprev).symm))
    have hnot : rC jfC ∉ cPre.support := by
      simp only [cPre, Circuit.support_seq, Circuit.support_cnot, Finset.mem_union,
        Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨⟨(UnsignedGivens.GidneyKickDisjoint.ne_C_C rC hpne).symm,
        (hd.ne_cat_C jfCat jfC).symm⟩,
        ⟨(UnsignedGivens.GidneyKickDisjoint.ne_C_C rC hpne).symm, (hd.ne_a0_C jfC).symm⟩⟩
    have hs1 := SubspaceStepU.of_circuit (Var := Var) (R₀ := R₀) cPre rfl
    have hs2 := SubspaceStepU.of_andCompute (Var := Var) (rCat jfCat) a0 (rC jfC) (hd.ne_cat_a0
      jfCat) (hd.ne_cat_C jfCat jfC) (hd.ne_a0_C jfC) (zeroOnWire_mul_of_not_mem_support (rC jfC)
      cPre hnot hC0)
    refine (hs1.seq (hs2.seq (SubspaceStepU.of_circuit (Var := Var) cPost rfl))).congr rfl ?_
    dsimp only [gFwd4, cPre, cPost, jfCat, jfC, jprev]
    simp only [Circuit.eval_seq, Submonoid.coe_mul, Matrix.mul_assoc]
  · simp only [h0, ↓reduceDIte]
    exact SubspaceStepU.of_andCompute (Var := Var) (rCat jfCat) a0 (rC jfC) (hd.ne_cat_a0 jfCat)
      (hd.ne_cat_C jfCat jfC) (hd.ne_a0_C jfC) hC0
theorem SubspaceStepU_topZeroBwdDyn [Fintype Var] [DecidableEq Var] (v : Var) (hB : 2 ≤ B) (rCat :
    QRegister B n) (a0 : Wire n) (rC : QRegister (B - 1) n) (w_p : Wire n) (hd :
    TopZeroGidneyDisjoint rCat a0 rC w_p) (j : ℕ) (hjb : j < B - 1) {R₀ : Operator (2 ^ n)} (hC1 :
    ZeroOnWire (rC ⟨j, hjb⟩) ((topZeroBwdRef hB rCat a0 rC w_p hd j hjb).eval.1 * R₀)) :
    SubspaceStepU R₀ ((topZeroBwdRef hB rCat a0 rC w_p hd j hjb).eval.1 * R₀) (topZeroBwdDyn v hB
    rCat a0 rC w_p hd j hjb) := by
  let jfCat : Fin B := ⟨j, by omega⟩
  let jfC : Fin (B - 1) := ⟨j, hjb⟩
  dsimp only [topZeroBwdDyn, topZeroBwdRef] at hC1 ⊢
  by_cases h0 : 0 < j
  · simp only [h0, ↓reduceDIte] at hC1 ⊢
    let jprev : Fin (B - 1) := ⟨j - 1, by omega⟩
    have hpne : jprev ≠ jfC := fin_pred_ne h0 hjb
    let cPre := Circuit.seq (Circuit.seq (Circuit.CNOT (rC jprev) (rCat jfCat) (hd.ne_cat_C jfCat
      jprev).symm) (Circuit.CNOT (rC jprev) a0 (hd.ne_a0_C jprev).symm)) (Circuit.CNOT (rC jprev)
      (rC jfC) (UnsignedGivens.GidneyKickDisjoint.ne_C_C rC hpne))
    let T_anc := Circuit.TOFF (rCat jfCat) a0 (rC jfC) (hd.ne_cat_a0 jfCat) (hd.ne_cat_C jfCat jfC)
      (hd.ne_a0_C jfC)
    let cPost := Circuit.seq (Circuit.CNOT (rC jprev) a0 (hd.ne_a0_C jprev).symm) (Circuit.CNOT a0
      (rCat jfCat) (hd.ne_cat_a0 jfCat).symm)
    have hnot : rC jfC ∉ cPost.support := by
      simp only [cPost, Circuit.support_seq, Circuit.support_cnot, Finset.mem_union,
        Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨⟨(UnsignedGivens.GidneyKickDisjoint.ne_C_C rC hpne).symm, (hd.ne_a0_C jfC).symm⟩,
        ⟨(hd.ne_a0_C
        jfC).symm, (hd.ne_cat_C jfCat jfC).symm⟩⟩
    have href_eq : (Circuit.seq (Circuit.seq (Circuit.CNOT (rC jprev) (rCat jfCat) (hd.ne_cat_C
        jfCat jprev).symm) (Circuit.CNOT (rC jprev) a0 (hd.ne_a0_C jprev).symm)) (gBwd4 (rCat jfCat)
        a0 (rC jfC) (rC jprev) (hd.ne_cat_a0 jfCat) (hd.ne_cat_C jfCat jfC) (hd.ne_a0_C jfC)
        (hd.ne_a0_C jprev) (UnsignedGivens.GidneyKickDisjoint.ne_C_C rC hpne).symm)).eval.1 * R₀ =
        cPost.eval.1 * (T_anc.eval.1 * (cPre.eval.1 * R₀)) := by
      dsimp only [gBwd4, cPre, T_anc, cPost, jfCat, jfC, jprev]
      simp only [Circuit.eval_seq, Submonoid.coe_mul, Matrix.mul_assoc]
    have hClean := proj_zero_of_post_eq (rC jfC) cPost hnot (by rwa [← href_eq])
    have hs1 := SubspaceStepU.of_circuit (Var := Var) (R₀ := R₀) cPre rfl
    have hs2 := SubspaceStepU_of_andUncompute_fwd (R₀ := cPre.eval.1 * R₀) v (rCat jfCat) a0 (rC
      jfC) (hd.ne_cat_a0 jfCat) (hd.ne_cat_C jfCat jfC) (hd.ne_a0_C jfC) hClean
    exact (hs1.seq (hs2.seq (SubspaceStepU.of_circuit (Var := Var) cPost rfl))).congr rfl
      href_eq.symm
  · simp only [h0, ↓reduceDIte] at hC1 ⊢
    let T_anc := Circuit.TOFF (rCat jfCat) a0 (rC jfC) (hd.ne_cat_a0 jfCat) (hd.ne_cat_C jfCat jfC)
      (hd.ne_a0_C jfC)
    let cPost := Circuit.CNOT a0 (rCat jfCat) (hd.ne_cat_a0 jfCat).symm
    have hnot : rC jfC ∉ cPost.support := by
      simp only [cPost, Circuit.support_cnot, Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨(hd.ne_a0_C jfC).symm, (hd.ne_cat_C jfCat jfC).symm⟩
    have href_eq : (gBwd3 (rCat jfCat) a0 (rC jfC) (hd.ne_cat_a0 jfCat) (hd.ne_cat_C jfCat jfC)
        (hd.ne_a0_C jfC)).eval.1 * R₀ = cPost.eval.1 * (T_anc.eval.1 * R₀) := by
      dsimp only [gBwd3, T_anc, cPost, jfCat, jfC]
      simp only [Circuit.eval_seq, Submonoid.coe_mul, Matrix.mul_assoc]
    have hClean := proj_zero_of_post_eq (rC jfC) cPost hnot (by rwa [← href_eq])
    have hs1 := SubspaceStepU_of_andUncompute_fwd (R₀ := R₀) v (rCat jfCat) a0 (rC jfC)
      (hd.ne_cat_a0 jfCat) (hd.ne_cat_C jfCat jfC) (hd.ne_a0_C jfC) hClean
    exact (hs1.seq (SubspaceStepU.of_circuit (Var := Var) cPost rfl)).congr rfl href_eq.symm
theorem SubspaceStepU_topZeroPrefixDyn [Fintype Var] [DecidableEq Var] (v : Var) (hB : 2 ≤ B) (rCat
    : QRegister B n) (a0 : Wire n) (rC : QRegister (B - 1) n) (w_p : Wire n) (hd :
    TopZeroGidneyDisjoint rCat a0 rC w_p) {S_ctrl : Finset (Wire n)} (bs : TopZeroPhaseKickBitSteps
    rCat a0 rC w_p S_ctrl) (k : ℕ) (hk : k ≤ B - 1) {R₀ : Operator (2 ^ n)} (ha0 : ZeroOnWire a0 R₀)
    (hC0 : ∀ m : Fin (B - 1), (B - 1) - k ≤ m.val → ZeroOnWire (rC m) R₀) : SubspaceStepU R₀
    ((topZeroPrefixRef hB rCat a0 rC w_p hd bs k hk).eval.1 * R₀) (topZeroPrefixDyn v hB rCat a0 rC
    w_p hd bs k hk) := by
  induction k generalizing R₀ with
  | zero =>
      let jb : Fin B := ⟨B - 1, by omega⟩
      let jc : Fin (B - 1) := ⟨B - 2, by omega⟩
      let s := bs.stepLo jb
      have hs_anc : s.anc = a0 := bs.ancLo jb
      have hcat_nc : rCat jb ∉ S_ctrl := fun hm ↦ Finset.disjoint_left.mp bs.disj_ctrl_cat hm
        (QRegister.mem_image rCat _ |>.mpr ⟨jb, rfl⟩)
      let cBody := topCarrySumBody (rCat jb) a0 (rC jc) w_p (hd.ne_cat_a0 jb) (hd.ne_cat_C jb
        jc).symm (hd.ne_a0_C jc).symm (hd.ne_C_wp jc) (hd.ne_cat_wp jb) hd.ne_a0_wp
      have hperm_body : UnsignedGivens.PhasedPerm cBody (fun γ ↦
        UnsignedGivens.omega8 ^ (((γ (rCat jb) + γ (rC jc))
        * (γ a0 + γ (rC jc)) + γ (rC jc)) + γ w_p).val) (fun γ ↦ Function.update γ (rCat jb) (γ
        (rCat jb) + γ (rC jc) + γ a0)) := fun γ ↦ evolve_topCarrySumBody_ket _ _ _ _ _ _ _ _ _ _ γ
      exact SubspaceStepU_cleanBitStep_wrap (R₀ := R₀) v (bs.cleanLo jb) hperm_body (fun γ ↦
        update_ne_of_eq hs_anc (hd.ne_cat_a0 jb).symm γ _) (fun _ _ hw ↦ update_of_mem_not_mem
        hw hcat_nc _ _) (hs_anc.symm ▸ ha0) (.circuit cBody) (SubspaceStepU.of_circuit cBody rfl)
  | succ k ih =>
      let j := (B - 1) - (k + 1)
      have hjb : j < B - 1 := by omega
      let jfCat : Fin B := ⟨j, by omega⟩
      let jfC : Fin (B - 1) := ⟨j, hjb⟩
      let s := bs.stepLo jfCat
      have hs_anc : s.anc = a0 := bs.ancLo jfCat
      have hjfC_ge : (B - 1) - (k + 1) ≤ jfC.val := le_rfl
      have hC_nc : rC jfC ∉ S_ctrl := fun hm ↦ Finset.disjoint_left.mp bs.disj_ctrl_C hm
        (QRegister.mem_image rC _ |>.mpr ⟨jfC, rfl⟩)
      have hcat_nc : rCat jfCat ∉ S_ctrl := fun hm ↦ Finset.disjoint_left.mp bs.disj_ctrl_cat hm
        (QRegister.mem_image rCat _ |>.mpr ⟨jfCat, rfl⟩)
      have hpermFB := topZeroFwdBwdRef_perm hB rCat a0 rC w_p hd j hjb
      let c_pm := Circuit.seq s.pre (Circuit.seq (Circuit.TOFF s.c₁ s.c₂ s.anc s.h₁₂ s.h₁a s.h₂a)
        s.midPre)
      have hfixF_anc (β : BitAssignment n) : Function.update β (rC jfC) (β (rC jfC) + ((β (rCat
          jfCat) + if h0 : 0 < j then β (rC ⟨j - 1, by omega⟩) else 0) * (β a0 + if h0 : 0 < j then
          β (rC ⟨j - 1, by omega⟩) else 0) + if h0 : 0 < j then β (rC ⟨j - 1, by omega⟩) else 0))
          s.anc = β s.anc := by rw [hs_anc]
                                exact Function.update_of_ne (hd.ne_a0_C jfC) _ _
      have hfixF_ctrl (β : BitAssignment n) (w : Wire n) (hw : w ∈ S_ctrl) : Function.update β (rC
          jfC) (β (rC jfC) + ((β (rCat jfCat) + if h0 : 0 < j then β (rC ⟨j - 1, by omega⟩) else 0)
          * (β a0 + if h0 : 0 < j then β (rC ⟨j - 1, by omega⟩) else 0) + if h0 : 0 < j then β (rC
          ⟨j - 1, by omega⟩) else 0)) w = β w := by
        have hC_ne : w ≠ rC jfC := fun h ↦ by rw [h] at hw
                                              exact hC_nc hw
        exact Function.update_of_ne hC_ne _ _
      have hsF : SubspaceStepU R₀ ((s.wrapCircuit (topZeroFwdRef hB rCat a0 rC w_p hd j hjb)).eval.1
          * R₀) (s.wrapDynamic v (topZeroFwdDyn hB rCat a0 rC w_p hd j hjb)) := by
        refine SubspaceStepU_cleanBitStep_wrap v (bs.cleanLo jfCat) hpermFB.1 hfixF_anc hfixF_ctrl
          (hs_anc.symm ▸ ha0) _ ?_
        dsimp only
        have hc_pm : s.midPre.eval.1 * ((Circuit.TOFF s.c₁ s.c₂ s.anc s.h₁₂ s.h₁a s.h₂a).eval.1 *
            (s.pre.eval.1 * R₀)) = c_pm.eval.1 * R₀ := by
          dsimp only [c_pm]
          simp only [Circuit.eval_seq, Submonoid.coe_mul, Matrix.mul_assoc]
        rw [hc_pm]
        exact SubspaceStepU_topZeroFwdDyn hB rCat a0 rC w_p hd j hjb
          (zeroOnWire_mul_of_phasedPerm_fix (rC jfC) c_pm (bs.cleanLo jfCat).pre_mid_perm (fun β ↦
          update_anc_ne hs_anc (hd.ne_a0_C jfC).symm β _) (hC0 jfC hjfC_ge))
      have hwrapF_perm :=
        (UnsignedGivens.cleanBitStep_wrap_spec (bs.cleanLo jfCat) hpermFB.1 hfixF_anc
        hfixF_ctrl).1
      let cF := s.wrapCircuit (topZeroFwdRef hB rCat a0 rC w_p hd j hjb)
      let R₁ := cF.eval.1 * R₀
      have ha0_R1 : ZeroOnWire a0 R₁ := zeroOnWire_mul_of_phasedPerm_fix a0 cF hwrapF_perm
          (fun β ↦ by rw [hs_anc, Function.update_self])
          ha0
      have hC0_R1 : ∀ m : Fin (B - 1), (B - 1) - k ≤ m.val → ZeroOnWire (rC m) R₁ :=
        fun m hm ↦ by
          refine zeroOnWire_mul_of_phasedPerm_fix (rC m) cF hwrapF_perm (fun β ↦ ?_) (hC0 m
            (by omega))
          have hne_anc : rC m ≠ s.anc := by rw [hs_anc]
                                            exact (hd.ne_a0_C m).symm
          have hne_C : rC m ≠ rC jfC := fun h ↦ by
            have hv := congrArg Fin.val (rC.wires.injective h)
            dsimp [jfC] at hv
            omega
          rw [Function.update_of_ne hne_anc, Function.update_of_ne hne_C, Function.update_of_ne
            hne_anc]
      have hsMid := ih (by omega) ha0_R1 hC0_R1
      let cMid := topZeroPrefixRef hB rCat a0 rC w_p hd bs k (by omega)
      let R₂ := cMid.eval.1 * R₁
      obtain ⟨_, _, hperm_mid, hfix_mid, _⟩ := topZeroPrefixRef_spec hB rCat a0 rC w_p hd bs k
        (by omega)
      have ha0_R2 : ZeroOnWire a0 R₂ := zeroOnWire_mul_of_phasedPerm_fix a0 cMid hperm_mid (fun β ↦
        hfix_mid β a0 fun m _ ↦ (hd.ne_cat_a0 m).symm) ha0_R1
      have hsB : SubspaceStepU R₂ ((s.wrapCircuit (topZeroBwdRef hB rCat a0 rC w_p hd j hjb)).eval.1
          * R₂) (s.wrapDynamic v (topZeroBwdDyn v hB rCat a0 rC w_p hd j hjb)) := by
        refine SubspaceStepU_cleanBitStep_wrap v (bs.cleanLo jfCat) hpermFB.2
          (fun β ↦ by
            rw [hs_anc, Function.update_of_ne (hd.ne_cat_a0 jfCat).symm, Function.update_of_ne
              (hd.ne_a0_C jfC)])
          (fun _ _ hw ↦ (update_of_mem_not_mem hw hcat_nc _ _).trans (update_of_mem_not_mem hw
              hC_nc _ _))
          (hs_anc.symm ▸ ha0_R2)
          _ ?_
        dsimp only
        apply SubspaceStepU_topZeroBwdDyn
        let R_in2 := s.midPre.eval.1 * ((Circuit.TOFF s.c₁ s.c₂ s.anc s.h₁₂ s.h₁a s.h₂a).eval.1 *
          (s.pre.eval.1 * R₂))
        let c_mp := Circuit.seq s.midPost (Circuit.seq (Circuit.TOFF s.c₁ s.c₂ s.anc s.h₁₂ s.h₁a
          s.h₂a) s.post)
        have hmp_perm : UnsignedGivens.PhasedPerm c_mp (fun _ ↦ 1)
            (fun β ↦ Function.update β s.anc (β s.anc + bs.bitLo β jfCat)) := fun β ↦ by
          rw [one_smul]
          exact (bs.cleanLo jfCat).mid_post_inv β
        apply zeroOnWire_of_mul_phasedPerm_fix (rC jfC) c_mp hmp_perm (fun β ↦ update_anc_ne
          hs_anc (hd.ne_a0_C jfC).symm β _)
        obtain ⟨_, _, hperm_all, hfix_all, _⟩ := topZeroPrefixRef_spec hB rCat a0 rC w_p hd bs (k +
          1) hk
        have hall_C := zeroOnWire_mul_of_phasedPerm_fix (rC jfC) _ hperm_all (fun β ↦ hfix_all β
          (rC jfC) fun m _ ↦ (hd.ne_cat_C m jfC).symm) (hC0 jfC hjfC_ge)
        have hceq : c_mp.eval.1 * ((topZeroBwdRef hB rCat a0 rC w_p hd j hjb).eval.1 * R_in2) =
            (topZeroPrefixRef hB rCat a0 rC w_p hd bs (k + 1) hk).eval.1 * R₀ := by
          dsimp only [topZeroPrefixRef, UnsignedGivens.PhasedStep.wrapCircuit, c_mp, R_in2, R₂, R₁,
            cMid, cF,
            s, j, jfCat]
          simp only [Circuit.eval_seq, Submonoid.coe_mul, Matrix.mul_assoc]
        rwa [hceq]
      refine (hsF.seq (hsMid.seq hsB)).congr rfl ?_
      dsimp only [topZeroPrefixRef, R₂, R₁, cMid, cF, s, j, jfCat]
      simp only [Circuit.eval_seq, Submonoid.coe_mul, Matrix.mul_assoc]
theorem topZeroRawUnsignedPhaseKickRef_phasedPerm (hB : 2 ≤ B) (rCat : QRegister B n) (a0 : Wire n)
    (rC : QRegister (B - 1) n) (w_p : Wire n) (hd : TopZeroGidneyDisjoint rCat a0 rC w_p) {S_ctrl :
    Finset (Wire n)} (bs : TopZeroPhaseKickBitSteps rCat a0 rC w_p S_ctrl) : ∃ (φ : BitAssignment n
    → ℂ) (f : BitAssignment n → BitAssignment n),
      UnsignedGivens.PhasedPerm (topZeroRawUnsignedPhaseKickRef
    hB rCat a0 rC w_p hd bs) φ f ∧ ∀ β (w : Wire n), w ∉ rCat.image → f β w = β w := by
  let cTopIn := Circuit.seq (Circuit.S a0) (UnsignedGivens.czCircuit w_p a0 hd.ne_a0_wp.symm)
  have hp_top_in : UnsignedGivens.PhasedPerm cTopIn
      (fun γ ↦ Complex.I ^ (γ a0).val * (-1 : ℂ) ^ (γ w_p * γ a0).val) id := fun γ ↦ by
    dsimp only [UnsignedGivens.PhasedPerm, cTopIn, id_eq]
    rw [UnsignedGivens.eval_seq_mulVec, UnsignedGivens.evolve_S_ket, Matrix.mulVec_smul,
      UnsignedGivens.evolve_czCircuit_ket,
      smul_smul]
  have hp₁ := cleanWrap_perm_of_eq bs.cleanTop hp_top_in (fun _ ↦ rfl) (fun _ _ _ ↦ rfl) (fun β ↦
    update_update_self_eq2 β _ _)
  let cMidIn := UnsignedGivens.parityTCircuit a0 w_p hd.ne_a0_wp
  have hp_mid_in : UnsignedGivens.PhasedPerm cMidIn (fun γ ↦
    UnsignedGivens.omega8 ^ (γ a0 + γ w_p).val) id := fun γ
    ↦ UnsignedGivens.evolve_parityTCircuit_ket _ _ _ γ
  have hp_mid1 := cleanWrap_perm_of_eq bs.cleanMid hp_mid_in (fun _ ↦ rfl) (fun _ _ _ ↦ rfl) (fun β
    ↦ update_update_self_eq2 β _ _)
  have hp₂ := hp_mid1.seq (fun γ ↦ UnsignedGivens.evolve_sdagCircuit_ket w_p γ)
  let fan := UnsignedGivens.cnotFanoutReg B w_p rCat (fun j ↦ (hd.ne_cat_wp j).symm)
  let f_fan (β : BitAssignment n) (w : Wire n) : ZMod 2 := if w ∈ Set.range rCat.wires then β w + β
    w_p else β w
  have hperm_fan : UnsignedGivens.PhasedPerm fan (fun _ ↦ 1) f_fan := fun β ↦ by
    rw [one_smul]
    exact UnsignedGivens.evolve_cnotFanoutReg_ket B w_p rCat _ β
  have hfix_fan : ∀ β (w : Wire n), w ∉ rCat.image → f_fan β w = β w := fun β w hw ↦
    ite_eq_right_of_eq_false _ _ (eq_false fun ⟨j, hj⟩ ↦ hw (QRegister.mem_image rCat w |>.mpr ⟨j,
    hj⟩))
  obtain ⟨_, _, hp_lo, hfix_lo, _⟩ := topZeroPrefixRef_spec hB rCat a0 rC w_p hd bs (B - 1) le_rfl
  refine ⟨_, _, hp₁.seq (hp₂.seq (hperm_fan.seq (hp_lo.seq hperm_fan))), fun β w hw ↦ ?_⟩
  dsimp only [Function.comp_apply, id_eq]
  rw [hfix_fan _ w hw, hfix_lo _ w fun m _ hm ↦ hw (QRegister.mem_image rCat w |>.mpr ⟨m, hm.symm⟩),
    hfix_fan _ w hw]
theorem realizesCleanRef_topZeroRawUnsignedPhaseKickDyn [Fintype Var] [DecidableEq Var] [NeZero (2 ^
    n)] (v : Var) (hB : 2 ≤ B) (rCat : QRegister B n) (a0 : Wire n) (rC : QRegister (B - 1) n) (w_p
    : Wire n) (hd : TopZeroGidneyDisjoint rCat a0 rC w_p) {S_ctrl : Finset (Wire n)} (bs :
    TopZeroPhaseKickBitSteps rCat a0 rC w_p S_ctrl) :
      UnsignedGivens.RealizesCleanRef ((QRegister.singleton
    a0).concat rC hd.disj_a0_C) (topZeroRawUnsignedPhaseKickRef hB rCat a0 rC w_p hd bs)
    (topZeroRawUnsignedPhaseKickDyn v hB rCat a0 rC w_p hd bs) := by
  let rWork := (QRegister.singleton a0).concat rC hd.disj_a0_C
  let P₀ := rWork.basisOutcomeProjector 0
  obtain ⟨_, _, hp_all, hfix_all⟩ := topZeroRawUnsignedPhaseKickRef_phasedPerm hB rCat a0 rC w_p hd
    bs
  have hclean : (topZeroRawUnsignedPhaseKickRef hB rCat a0 rC w_p hd bs).eval.1 * P₀ = P₀ *
      (topZeroRawUnsignedPhaseKickRef hB rCat a0 rC w_p hd bs).eval.1 * P₀ := by
    refine UnsignedGivens.cleanProjector_of_phasedPerm_fix rWork _ hp_all fun β idx hidx ↦ ?_
    have hnotin : rWork idx ∉ rCat.image := by
      rw [QRegister.mem_image]
      rintro ⟨m, hm⟩
      obtain ⟨i | j, rfl⟩ := finSumFinEquiv.surjective idx
      · fin_cases i
        exact hd.ne_cat_a0 m (by simpa [rWork] using hm)
      · exact hd.ne_cat_C m j (by simpa [rWork] using hm)
    rw [hfix_all β (rWork idx) hnotin, hidx]
  refine realizesCleanRef_of_subspaceStepU rWork _ _ hclean ?_
  have hp_id : UnsignedGivens.PhasedPerm (.identity : Circuit n) (fun _ ↦ 1) id := fun β ↦ by
    rw [one_smul]
    exact UnsignedGivens.eval_identity_mulVec (UnsignedGivens.ket β)
  have hWorkZero (idx : Fin (1 + (B - 1))) : ZeroOnWire (rWork idx) P₀ := by
    simpa only [ZeroOnWire, Circuit.eval_identity, Submonoid.coe_one, Matrix.one_mul] using
      singleton_proj_zero_mul_eval_mul_work_eq (rWork idx) rWork .identity hp_id (fun _ h ↦ h idx)
  have ha0_P0 : ZeroOnWire a0 P₀ := by
    simpa only [rWork, QRegister.concat_apply_left, QRegister.singleton_apply] using hWorkZero
      (Fin.castAdd (B - 1) 0)
  have hC0_P0 (m : Fin (B - 1)) : ZeroOnWire (rC m) P₀ := by
    simpa only [rWork, QRegister.concat_apply_right] using hWorkZero (Fin.natAdd 1 m)
  let cTopIn := Circuit.seq (Circuit.S a0) (UnsignedGivens.czCircuit w_p a0 hd.ne_a0_wp.symm)
  have hp_top_in : UnsignedGivens.PhasedPerm cTopIn
      (fun γ ↦ Complex.I ^ (γ a0).val * (-1 : ℂ) ^ (γ w_p * γ a0).val) id := fun γ ↦ by
    dsimp only [UnsignedGivens.PhasedPerm, cTopIn, id_eq]
    rw [UnsignedGivens.eval_seq_mulVec, UnsignedGivens.evolve_S_ket, Matrix.mulVec_smul,
      UnsignedGivens.evolve_czCircuit_ket,
      smul_smul]
  have hsTop := SubspaceStepU_cleanBitStep_wrap (R₀ := P₀) v bs.cleanTop hp_top_in (fun _ ↦ rfl)
    (fun _ _ _ ↦ rfl) (by
      rw [bs.ancTop]
      exact ha0_P0)
    (.circuit cTopIn) (SubspaceStepU.of_circuit cTopIn rfl)
  have hp₁ := cleanWrap_perm_of_eq bs.cleanTop hp_top_in (fun _ ↦ rfl) (fun _ _ _ ↦ rfl) (fun β ↦
    update_update_self_eq2 β _ _)
  let R₁ := (bs.stepTop.wrapCircuit cTopIn).eval.1 * P₀
  have ha0_R1 : ZeroOnWire a0 R₁ := zeroOnWire_mul_of_phasedPerm_fix _ _ hp₁ (fun _ ↦ rfl) ha0_P0
  have hC0_R1 (m : Fin (B - 1)) := zeroOnWire_mul_of_phasedPerm_fix _ _ hp₁ (fun _ ↦ rfl) (hC0_P0
    m)
  let cMidIn := UnsignedGivens.parityTCircuit a0 w_p hd.ne_a0_wp
  have hp_mid_in : UnsignedGivens.PhasedPerm cMidIn (fun γ ↦
    UnsignedGivens.omega8 ^ (γ a0 + γ w_p).val) id := fun γ
    ↦ UnsignedGivens.evolve_parityTCircuit_ket _ _ _ γ
  have hsMid1 := SubspaceStepU_cleanBitStep_wrap (R₀ := R₁) v bs.cleanMid hp_mid_in (fun _ ↦ rfl)
    (fun _ _ _ ↦ rfl) (by
      rw [bs.ancMid]
      exact ha0_R1)
    (.circuit cMidIn) (SubspaceStepU.of_circuit cMidIn rfl)
  let cMidFull := Circuit.seq (bs.stepMid.wrapCircuit cMidIn) (UnsignedGivens.sdagCircuit w_p)
  let R₂ := cMidFull.eval.1 * R₁
  have hsMid : SubspaceStepU R₁ R₂ (.seq (bs.stepMid.wrapDynamic v (.circuit cMidIn)) (.circuit
    (UnsignedGivens.sdagCircuit w_p))) :=
      (hsMid1.seq (SubspaceStepU.of_circuit (UnsignedGivens.sdagCircuit w_p)
    rfl)).congr rfl (by
        dsimp only [R₂, cMidFull]
        simp only [Circuit.eval_seq, Submonoid.coe_mul, mul_assoc])
  have hp_midF := (cleanWrap_perm_of_eq bs.cleanMid hp_mid_in (fun _ ↦ rfl) (fun _ _ _ ↦ rfl) (fun
    β ↦ update_update_self_eq2 β _ _)).seq (fun γ ↦ UnsignedGivens.evolve_sdagCircuit_ket w_p γ)
  let fan := UnsignedGivens.cnotFanoutReg B w_p rCat (fun j ↦ (hd.ne_cat_wp j).symm)
  have hp_fan : UnsignedGivens.PhasedPerm fan (fun _ ↦ 1)
      (fun β w ↦ if w ∈ Set.range rCat.wires then β w + β w_p else β w) := fun β ↦ by
    rw [one_smul]
    exact UnsignedGivens.evolve_cnotFanoutReg_ket B w_p rCat _ β
  let R₃ := fan.eval.1 * R₂
  have ha0_Main : ZeroOnWire a0 R₃ := zeroOnWire_mul_of_phasedPerm_fix _ fan hp_fan (fun _ ↦
    ite_eq_right_of_eq_false _ _ (eq_false fun ⟨m, hm⟩ ↦ hd.ne_cat_a0 m hm))
    (zeroOnWire_mul_of_phasedPerm_fix _ cMidFull hp_midF (fun _ ↦ rfl) ha0_R1)
  have hC0_Main (m : Fin (B - 1)) (_ : (B - 1) - (B - 1) ≤ m.val) : ZeroOnWire (rC m) R₃ :=
    zeroOnWire_mul_of_phasedPerm_fix _ fan hp_fan (fun _ ↦ ite_eq_right_of_eq_false _ _ (eq_false
    fun ⟨k, hk⟩ ↦ hd.ne_cat_C k m hk)) (zeroOnWire_mul_of_phasedPerm_fix _ cMidFull hp_midF (fun _ ↦
    rfl) (hC0_R1 m))
  have hsPref := SubspaceStepU_topZeroPrefixDyn v hB rCat a0 rC w_p hd bs (B - 1) le_rfl ha0_Main
    hC0_Main
  refine (hsTop.seq (hsMid.seq ((SubspaceStepU.of_circuit fan rfl).seq (hsPref.seq
    (SubspaceStepU.of_circuit fan rfl))))).congr rfl ?_
  dsimp only [topZeroRawUnsignedPhaseKickRef, R₃, R₂, R₁, P₀, rWork, cMidFull, fan, cMidIn, cTopIn]
  simp only [Circuit.eval_seq, Submonoid.coe_mul, Matrix.mul_assoc]
theorem topZeroRawUnsignedPhaseKickRef_ket_of_zero (hB : 2 ≤ B) (rCat : QRegister B n) (a0 : Wire
    n) (rC : QRegister (B - 1) n) (w_p : Wire n) (hd : TopZeroGidneyDisjoint rCat a0 rC w_p)
    {S_ctrl : Finset (Wire n)} (bs : TopZeroPhaseKickBitSteps rCat a0 rC w_p S_ctrl) (β :
    BitAssignment n) (ha0 : β a0 = 0) (hC0 : ∀ j : Fin (B - 1), β (rC j) = 0) :
    let a_lo := UnsignedGivens.bitSeqVal (bs.bitLo β)
    let b_mid := (bs.bitMid β).val
    let b_top := (bs.bitTop β).val
    let y := UnsignedGivens.localIdx rCat β
    let y_out := UnsignedGivens.signedAddModPerm B a_lo (UnsignedGivens.bitSeqVal_lt _) (β w_p) y
    (topZeroRawUnsignedPhaseKickRef hB rCat a0 rC w_p hd bs).eval.1.mulVec (UnsignedGivens.ket β) =
      UnsignedGivens.rawPhaseStepVal B a_lo b_mid b_top (β w_p) y •
        UnsignedGivens.ket (UnsignedGivens.writeReg β rCat
      (basisBits B y_out)) := by
  intro a_lo b_mid b_top y y_out
  let cTopIn := Circuit.seq (Circuit.S a0) (UnsignedGivens.czCircuit w_p a0 hd.ne_a0_wp.symm)
  have hp_top_in : UnsignedGivens.PhasedPerm cTopIn
      (fun γ ↦ Complex.I ^ (γ a0).val * (-1 : ℂ) ^ (γ w_p * γ a0).val) id := fun γ ↦ by
    dsimp only [UnsignedGivens.PhasedPerm, cTopIn, id_eq]
    rw [UnsignedGivens.eval_seq_mulVec, UnsignedGivens.evolve_S_ket, Matrix.mulVec_smul,
      UnsignedGivens.evolve_czCircuit_ket,
      smul_smul]
  have hwrap_top := UnsignedGivens.cleanBitStep_wrap_spec bs.cleanTop hp_top_in (fun _ ↦
    rfl) (fun _ _ _ ↦
    rfl)
  have htop_ket : (bs.stepTop.wrapCircuit cTopIn).eval.1.mulVec (UnsignedGivens.ket β) =
    (Complex.I ^ b_top *
      (-1 : ℂ) ^ ((β w_p).val * b_top)) • UnsignedGivens.ket β := by
    rw [hwrap_top.1 β]
    dsimp only [id]
    rw [update_update_self_eq2]
    congr 1
    rw [bs.ancTop, ha0, zero_add, Function.update_self, Function.update_of_ne hd.ne_a0_wp.symm]
    rcases UnsignedGivens.zmod2_eq_zero_or_one (β w_p) with hw | hw <;>
      rcases UnsignedGivens.zmod2_eq_zero_or_one (bs.bitTop β) with ht | ht <;> simp [b_top, hw, ht]
  let cMidIn := UnsignedGivens.parityTCircuit a0 w_p hd.ne_a0_wp
  have hp_mid_in : UnsignedGivens.PhasedPerm cMidIn (fun γ ↦
    UnsignedGivens.omega8 ^ (γ a0 + γ w_p).val) id := fun γ
    ↦ UnsignedGivens.evolve_parityTCircuit_ket _ _ _ γ
  have hwrap_mid := UnsignedGivens.cleanBitStep_wrap_spec bs.cleanMid hp_mid_in (fun _ ↦
    rfl) (fun _ _ _ ↦
    rfl)
  have hmid1_ket : (bs.stepMid.wrapCircuit cMidIn).eval.1.mulVec (UnsignedGivens.ket β) =
    (UnsignedGivens.omega8 ^
      ((((b_mid : ℕ) : ZMod 2) + β w_p).val)) • UnsignedGivens.ket β := by
    rw [hwrap_mid.1 β]
    dsimp only [id]
    rw [update_update_self_eq2]
    congr 1
    rw [bs.ancMid, ha0, zero_add, Function.update_self, Function.update_of_ne hd.ne_a0_wp.symm,
      UnsignedGivens.zmod2_eq_natCast_mod_two (bs.bitMid β)]
  let fan := UnsignedGivens.cnotFanoutReg B w_p rCat (fun j ↦ (hd.ne_cat_wp j).symm)
  let β_fan : BitAssignment n := fun w ↦ if w ∈ Set.range rCat.wires then β w + β w_p else β w
  let yc := if β w_p = 0 then y.val else 2 ^ B - 1 - y.val
  have hyc_val : UnsignedGivens.regVal rCat β_fan = yc := by
    simpa [β_fan, yc, y,
      UnsignedGivens.regVal] using UnsignedGivens.regVal_after_fanout rCat β (β w_p)
  obtain ⟨_, f_lo, hperm_lo, hfix_lo, hval_lo⟩ := topZeroPrefixRef_spec hB rCat a0 rC w_p hd bs (B -
    1) le_rfl
  have hcat_fan (k : Fin B) : β_fan (rCat k) = ((yc / 2 ^ k.val % 2 : ℕ) : ZMod 2) := by
    rw [← hyc_val]
    exact UnsignedGivens.reg_bit_eq_natCast_regVal rCat β_fan k
  have ha_fan : β_fan a0 = 0 := by simp only [β_fan, show a0 ∉ Set.range rCat.wires from fun ⟨j, hj⟩
                                     ↦ hd.ne_cat_a0 j hj, ↓reduceIte, ha0]
  have hlo_fan (k : Fin B) (_ : (B - 1) - (B - 1) ≤ k.val) : bs.bitLo β_fan k = ((a_lo / 2 ^ k.val %
      2 : ℕ) : ZMod 2) := by
    have hbv : bs.bitLo β_fan k = bs.bitLo β k :=
      (bs.cleanLo k).bitVal_congr β_fan β fun w hw ↦ by
        have hnot : w ∉ Set.range rCat.wires := fun ⟨j, hj⟩ ↦ Finset.disjoint_left.mp
          bs.disj_ctrl_cat hw (QRegister.mem_image rCat _ |>.mpr ⟨j, hj⟩)
        simp only [β_fan, hnot, ↓reduceIte]
    rw [hbv]
    exact (UnsignedGivens.bitSeqVal_div_pow_mod_two (bs.bitLo β) k).symm
  have hC_fan (k : Fin (B - 1)) : β_fan (rC k) = 0 := by
    simp only [β_fan, show rC k ∉ Set.range rCat.wires from fun ⟨j, hj⟩ ↦ hd.ne_cat_C j k hj,
      ↓reduceIte, hC0 k]
  have hv_lo :=
    hval_lo β_fan yc a_lo (hyc_val ▸ UnsignedGivens.regVal_lt rCat β_fan)
    (UnsignedGivens.bitSeqVal_lt _)
    (fun k _ ↦ hcat_fan k) ha_fan hlo_fan (fun k _ ↦ hC_fan k) (fun h0 ↦ absurd h0 (by omega))
  have hwp_fan : β_fan w_p = β w_p := by simp only [β_fan, show w_p ∉ Set.range rCat.wires from fun
                                           ⟨j, hj⟩ ↦ hd.ne_cat_wp j hj, ↓reduceIte]
  have hfan2 : fan.eval.1.mulVec (UnsignedGivens.ket (f_lo β_fan)) =
    UnsignedGivens.ket (UnsignedGivens.writeReg β rCat
      (basisBits B y_out)) := by
    rw [UnsignedGivens.evolve_cnotFanoutReg_ket]
    apply congrArg UnsignedGivens.ket
    funext w
    rw [hfix_lo β_fan w_p fun j _ hj ↦ hd.ne_cat_wp j hj.symm, hwp_fan]
    by_cases hw : w ∈ Set.range rCat.wires
    · obtain ⟨k, rfl⟩ := hw
      have hdvd : 2 ^ (k.val + 1) ∣ 2 ^ B := Nat.pow_dvd_pow 2 k.isLt
      have hdm (m : ℕ) : m / 2 ^ k.val % 2 = (m % 2 ^ (k.val + 1)) / 2 ^ k.val := by
        rw [pow_succ, Nat.mod_mul_right_div_self]
      simp only [show rCat k ∈ Set.range rCat.wires from ⟨k, rfl⟩, ↓reduceIte,
        UnsignedGivens.writeReg_apply_reg, hv_lo.2 k (by omega)]
      rcases UnsignedGivens.zmod2_eq_zero_or_one (β w_p) with hwp0 | hwp1
      · simp only [hwp0, add_zero]
        have hyo : y_out.val = (y.val + a_lo) % 2 ^ B := by
          simp [y_out, UnsignedGivens.signedAddModPerm, hwp0]
        rw [basisBits_eq_div_mod, hyo]
        simp only [yc, hwp0, ↓reduceIte]
        congr 1
        rw [hdm ((y.val + a_lo) % 2 ^ B), Nat.mod_mod_of_dvd _ hdvd, ← hdm]
      · simp only [hwp1]
        have h10 : (1 : ZMod 2) ≠ 0 := by decide
        have hyo : y_out.val = 2 ^ B - 1 - ((2 ^ B - 1 - y.val + a_lo) % 2 ^ B) := by
          simp [y_out, UnsignedGivens.signedAddModPerm, hwp1, h10]
        rw [basisBits_eq_div_mod, hyo]
        set ysum := (yc + a_lo) % 2 ^ B
        have hmod_bit : (yc + a_lo) / 2 ^ k.val % 2 = ysum / 2 ^ k.val % 2 := by
          rw [hdm (yc + a_lo), hdm ysum, Nat.mod_mod_of_dvd _ hdvd]
        rw [hmod_bit]
        have hoc :=
          UnsignedGivens.onesComp_div_pow_mod_two k.isLt (Nat.mod_lt (yc + a_lo) (Nat.two_pow_pos
          B))
        have h_xor : (((ysum / 2 ^ k.val % 2 : ℕ) : ZMod 2) + 1) = ((1 - ysum / 2 ^ k.val % 2 : ℕ) :
            ZMod 2) := by
          rcases Nat.mod_two_eq_zero_or_one (ysum / 2 ^ k.val) with h | h
          · simp [h]
          · simp [h]
        rw [h_xor]
        have hyc_def : yc = 2 ^ B - 1 - y.val := by dsimp [yc]
                                                    simp [hwp1, h10]
        dsimp [ysum] at hoc ⊢
        rw [hyc_def] at hoc
        rw [hoc, hyc_def]
    · simp only [hw, ↓reduceIte, UnsignedGivens.writeReg_apply_of_not_mem _ _ _ _ hw]
      rw [hfix_lo β_fan w fun j _ hj ↦ hw ⟨j, hj.symm⟩]
      simp only [β_fan, hw, ↓reduceIte]
  dsimp only [topZeroRawUnsignedPhaseKickRef]
  simp only [UnsignedGivens.eval_seq_mulVec]
  rw [htop_ket]
  simp only [Matrix.mulVec_smul]
  rw [hmid1_ket]
  simp only [Matrix.mulVec_smul]
  rw [UnsignedGivens.evolve_sdagCircuit_ket]
  simp only [Matrix.mulVec_smul]
  rw [UnsignedGivens.evolve_cnotFanoutReg_ket B w_p rCat _ β, hperm_lo β_fan]
  simp only [Matrix.mulVec_smul]
  rw [hfan2, hv_lo.1, hwp_fan]
  simp only [smul_smul]
  congr 1
  dsimp [UnsignedGivens.rawPhaseStepVal, yc]
  ring
attribute [irreducible] topZeroRawUnsignedPhaseKickDyn topZeroRawUnsignedPhaseKickRef
open Solution.CompactStepFast176Select.UnsignedGivens (affineBilinearBitStep
  extendHot0 isCleanBitStep_affineBilinearFormula affinePlaneEffK affineApexEffK
  affineUnsignedBilinearLac2CascadeCtrlUnitary clearHot0Circuit evolve_clearHot0Circuit_ket
  clearHot0Circuit_eval_mul_self clearHot0_zero_of_isOneHot)
open Solution.CompactStepFast176Select.OneHotMux
  (clearHot0Circuit_conj_muxCtrlUnitary_eq)
/-- `TopZeroPhaseKickBitSteps` reading `(idxTop, idxMid, 0 .. B - 1)` from `row` onto `a0`. -/
def topZeroAffineTableBitSteps {n B G' : ℕ} (idxTop idxMid : ℕ) (row : Fin (G' + 1) → Bool → ℕ) (u
    w_v : Wire n) (rHot' : QRegister G' n) (rCat : QRegister B n) (a0 : Wire n) (rC : QRegister (B -
    1) n) (w_p : Wire n) (huv : u ≠ w_v) (hh_u : ∀ g, rHot' g ≠ u) (hh_v : ∀ g, rHot' g ≠ w_v)
    (hu_wp : u ≠ w_p) (hv_wp : w_v ≠ w_p) (hh_wp : ∀ g, rHot' g ≠ w_p) (hu_cat : ∀ i, u ≠ rCat i)
    (hv_cat : ∀ i, w_v ≠ rCat i) (hh_cat : ∀ g i, rHot' g ≠ rCat i) (hu_a0 : u ≠ a0) (hv_a0 : w_v ≠
    a0) (hh_a0 : ∀ g, rHot' g ≠ a0) (hu_C : ∀ i, u ≠ rC i) (hv_C : ∀ i, w_v ≠ rC i) (hh_C : ∀ g i,
    rHot' g ≠ rC i) : TopZeroPhaseKickBitSteps rCat a0 rC w_p (insert u (insert w_v rHot'.image))
    where
  stepTop := affineBilinearBitStep G' u w_v rHot' (UnsignedGivens.rowBitMask row false idxTop)
    (UnsignedGivens.rowBitMask row true idxTop) a0 huv hu_a0 hv_a0 hh_u hh_v hh_a0
  stepMid := affineBilinearBitStep G' u w_v rHot' (UnsignedGivens.rowBitMask row false idxMid)
    (UnsignedGivens.rowBitMask row true idxMid) a0 huv hu_a0 hv_a0 hh_u hh_v hh_a0
  stepLo := fun j ↦ affineBilinearBitStep G' u w_v rHot' (UnsignedGivens.rowBitMask row false j.val)
    (UnsignedGivens.rowBitMask row true j.val) a0 huv hu_a0 hv_a0 hh_u hh_v hh_a0
  bitTop := fun β ↦ UnsignedGivens.bilinearBitFormula (β u) (β w_v)
    (extendHot0 (fun g ↦ β (rHot' g))) (UnsignedGivens.rowBitMask row false idxTop)
    (UnsignedGivens.rowBitMask row true idxTop)
  bitMid := fun β ↦ UnsignedGivens.bilinearBitFormula (β u) (β w_v)
    (extendHot0 (fun g ↦ β (rHot' g))) (UnsignedGivens.rowBitMask row false idxMid)
    (UnsignedGivens.rowBitMask row true idxMid)
  bitLo := fun β j ↦ UnsignedGivens.bilinearBitFormula (β u) (β w_v)
    (extendHot0 (fun g ↦ β (rHot' g))) (UnsignedGivens.rowBitMask row false j.val)
    (UnsignedGivens.rowBitMask row true j.val)
  ancTop := rfl
  ancMid := rfl
  ancLo := fun _ ↦ rfl
  cleanTop := isCleanBitStep_affineBilinearFormula _ _ _ _ _ _ _ _ _ _ _ _ _
  cleanMid := isCleanBitStep_affineBilinearFormula _ _ _ _ _ _ _ _ _ _ _ _ _
  cleanLo := fun _ ↦ isCleanBitStep_affineBilinearFormula _ _ _ _ _ _ _ _ _ _ _ _ _
  disj_ctrl_wp := by simp only [Finset.mem_insert, QRegister.mem_image, not_or, not_exists]
                     exact ⟨hu_wp.symm, hv_wp.symm, fun g hg ↦ hh_wp g hg⟩
  disj_ctrl_cat := by
    rw [Finset.disjoint_insert_left, Finset.disjoint_insert_left, QRegister.mem_image,
      QRegister.mem_image]
    refine ⟨fun ⟨i, hi⟩ ↦ hu_cat i hi.symm, fun ⟨i, hi⟩ ↦ hv_cat i hi.symm, Finset.disjoint_left.mpr
      fun q hq hc ↦ ?_⟩
    obtain ⟨g, rfl⟩ := QRegister.mem_image rHot' q |>.mp hq
    obtain ⟨i, hi⟩ := QRegister.mem_image rCat _ |>.mp hc
    exact hh_cat g i hi.symm
  not_mem_ctrl_a0 := by simp only [Finset.mem_insert, QRegister.mem_image, not_or, not_exists]
                        exact ⟨hu_a0.symm, hv_a0.symm, fun g hg ↦ hh_a0 g hg⟩
  disj_ctrl_C := by
    rw [Finset.disjoint_insert_left, Finset.disjoint_insert_left, QRegister.mem_image,
      QRegister.mem_image]
    refine ⟨fun ⟨i, hi⟩ ↦ hu_C i hi.symm, fun ⟨i, hi⟩ ↦ hv_C i hi.symm, Finset.disjoint_left.mpr fun
      q hq hc ↦ ?_⟩
    obtain ⟨g, rfl⟩ := QRegister.mem_image rHot' q |>.mp hq
    obtain ⟨i, hi⟩ := QRegister.mem_image rC _ |>.mp hc
    exact hh_C g i hi.symm
/-- Bundled wire-disjointness hypotheses for `topZeroAffineLac2KickDyn`. -/
structure TopZeroAffineKickDisjoint {n B G' : ℕ} (w_ctrl sub w_v : Wire n)
    (rHot' : QRegister G' n) (rCat : QRegister B n) (a0 : Wire n)
    (rC : QRegister (B - 1) n) (w_p : Wire n) : Prop where
  hcs : w_ctrl ≠ sub
  hcv : w_ctrl ≠ w_v
  hsv : sub ≠ w_v
  hh_ctrl : ∀ g, rHot' g ≠ w_ctrl
  hh_v : ∀ g, rHot' g ≠ w_v
  hctrl_wp : w_ctrl ≠ w_p
  hv_wp : w_v ≠ w_p
  hh_wp : ∀ g, rHot' g ≠ w_p
  hctrl_cat : ∀ i, w_ctrl ≠ rCat i
  hv_cat : ∀ i, w_v ≠ rCat i
  hh_cat : ∀ g i, rHot' g ≠ rCat i
  hsub_cat : ∀ i, sub ≠ rCat i
  hctrl_a0 : w_ctrl ≠ a0
  hv_a0 : w_v ≠ a0
  hh_a0 : ∀ g, rHot' g ≠ a0
  hsub_a0 : sub ≠ a0
  hctrl_C : ∀ i, w_ctrl ≠ rC i
  hv_C : ∀ i, w_v ≠ rC i
  hh_C : ∀ g i, rHot' g ≠ rC i
  hsub_C : ∀ i, sub ≠ rC i
/-- Zero-top-ancilla `(B + 2)`-bit `Lac = 2` affine phase-kick circuit (`12 * B + 14` `T`). -/
def topZeroAffineLac2KickDyn {Var : Type} {n B G' : ℕ} (v : Var) (hB : 2 ≤ B) (idxTop idxMid : ℕ)
    (row : Fin (G' + 1) → Bool → ℕ) (w_ctrl sub w_v : Wire n) (rHot' : QRegister G' n) (rCat :
    QRegister B n) (a0 : Wire n) (rC : QRegister (B - 1) n) (w_p : Wire n) (hd :
    TopZeroGidneyDisjoint rCat a0 rC w_p) (hdk : TopZeroAffineKickDisjoint w_ctrl sub w_v rHot' rCat
    a0 rC w_p) : DynamicCircuit Var n :=
  let bs := topZeroAffineTableBitSteps idxTop idxMid row w_ctrl w_v rHot' rCat a0 rC w_p hdk.hcv
    hdk.hh_ctrl hdk.hh_v hdk.hctrl_wp hdk.hv_wp hdk.hh_wp hdk.hctrl_cat hdk.hv_cat hdk.hh_cat
    hdk.hctrl_a0 hdk.hv_a0 hdk.hh_a0 hdk.hctrl_C hdk.hv_C hdk.hh_C
  (UnsignedGivens.inPlaceUVStep w_ctrl sub w_v hdk.hcs hdk.hcv hdk.hsv).wrapDynamic v
    (topZeroRawUnsignedPhaseKickDyn v hB rCat a0 rC w_p hd bs)
/-- Reference Toffoli circuit matched by `topZeroAffineLac2KickDyn`. -/
def topZeroAffineLac2KickRef {n B G' : ℕ} (hB : 2 ≤ B) (idxTop idxMid : ℕ) (row : Fin (G' + 1) →
    Bool → ℕ) (w_ctrl sub w_v : Wire n) (rHot' : QRegister G' n) (rCat : QRegister B n) (a0 : Wire
    n) (rC : QRegister (B - 1) n) (w_p : Wire n) (hd : TopZeroGidneyDisjoint rCat a0 rC w_p) (hdk :
    TopZeroAffineKickDisjoint w_ctrl sub w_v rHot' rCat a0 rC w_p) : Circuit n :=
  let bs := topZeroAffineTableBitSteps idxTop idxMid row w_ctrl w_v rHot' rCat a0 rC w_p hdk.hcv
    hdk.hh_ctrl hdk.hh_v hdk.hctrl_wp hdk.hv_wp hdk.hh_wp hdk.hctrl_cat hdk.hv_cat hdk.hh_cat
    hdk.hctrl_a0 hdk.hv_a0 hdk.hh_a0 hdk.hctrl_C hdk.hv_C hdk.hh_C
  (UnsignedGivens.inPlaceUVStep w_ctrl sub w_v hdk.hcs hdk.hcv hdk.hsv).wrapCircuit
    (topZeroRawUnsignedPhaseKickRef hB rCat a0 rC w_p hd bs)
@[simp] theorem count_topZeroAffineLac2KickDyn_toff {Var : Type} {n B G' : ℕ} (v : Var) (hB : 2 ≤ B)
    (idxTop idxMid : ℕ) (row : Fin (G' + 1) → Bool → ℕ) (w_ctrl sub w_v : Wire n) (rHot' : QRegister
    G' n) (rCat : QRegister B n) (a0 : Wire n) (rC : QRegister (B - 1) n) (w_p : Wire n) (hd :
    TopZeroGidneyDisjoint rCat a0 rC w_p) (hdk : TopZeroAffineKickDisjoint w_ctrl sub w_v rHot' rCat
    a0 rC w_p) : (topZeroAffineLac2KickDyn v hB idxTop idxMid row w_ctrl sub w_v rHot' rCat a0 rC
    w_p hd hdk).count .TOFF = 0 := by
  unfold topZeroAffineLac2KickDyn
  rw [UnsignedGivens.PhasedStep.count_wrapDynamic_toff _ _ _
    (UnsignedGivens.isCliffordWrapper_inPlaceUVStep _ _ _ _ _
    _)]
  exact count_topZeroRawUnsignedPhaseKickDyn_toff _ _ _ _ _ _ _ _
@[simp] theorem count_topZeroAffineLac2KickDyn_t {Var : Type} {n B G' : ℕ} (v : Var) (hB : 2 ≤ B)
    (idxTop idxMid : ℕ) (row : Fin (G' + 1) → Bool → ℕ) (w_ctrl sub w_v : Wire n) (rHot' : QRegister
    G' n) (rCat : QRegister B n) (a0 : Wire n) (rC : QRegister (B - 1) n) (w_p : Wire n) (hd :
    TopZeroGidneyDisjoint rCat a0 rC w_p) (hdk : TopZeroAffineKickDisjoint w_ctrl sub w_v rHot' rCat
    a0 rC w_p) : (topZeroAffineLac2KickDyn v hB idxTop idxMid row w_ctrl sub w_v rHot' rCat a0 rC
    w_p hd hdk).count .T = 8 * B + 14 + 4 * B := by
  unfold topZeroAffineLac2KickDyn
  rw [UnsignedGivens.PhasedStep.count_wrapDynamic_t _ _ _
    (UnsignedGivens.isCliffordWrapper_inPlaceUVStep _ _ _ _ _
    _), count_topZeroRawUnsignedPhaseKickDyn_t]
  omega
theorem topZeroAffineLac2KickRef_phasedPerm {n B G' : ℕ} (hB : 2 ≤ B) (idxTop idxMid : ℕ) (row : Fin
    (G' + 1) → Bool → ℕ) (w_ctrl sub w_v : Wire n) (rHot' : QRegister G' n) (rCat : QRegister B n)
    (a0 : Wire n) (rC : QRegister (B - 1) n) (w_p : Wire n) (hd : TopZeroGidneyDisjoint rCat a0 rC
    w_p) (hdk : TopZeroAffineKickDisjoint w_ctrl sub w_v rHot' rCat a0 rC w_p) : ∃ (φ :
    BitAssignment n → ℂ) (f : BitAssignment n → BitAssignment n), UnsignedGivens.PhasedPerm
    (topZeroAffineLac2KickRef hB idxTop idxMid row w_ctrl sub w_v rHot' rCat a0 rC w_p hd hdk) φ f ∧
    ∀ β (w : Wire n), w ∉ rCat.image → f β w = β w := by
  let bs := topZeroAffineTableBitSteps idxTop idxMid row w_ctrl w_v rHot' rCat a0 rC w_p hdk.hcv
    hdk.hh_ctrl hdk.hh_v hdk.hctrl_wp hdk.hv_wp hdk.hh_wp hdk.hctrl_cat hdk.hv_cat hdk.hh_cat
    hdk.hctrl_a0 hdk.hv_a0 hdk.hh_a0 hdk.hctrl_C hdk.hv_C hdk.hh_C
  obtain ⟨_, _, hp_in, hfix_in⟩ := topZeroRawUnsignedPhaseKickRef_phasedPerm hB rCat a0 rC w_p hd bs
  have hc_not : w_ctrl ∉ rCat.image := fun h ↦ by
    obtain ⟨i, hi⟩ := QRegister.mem_image rCat _ |>.mp h
    exact hdk.hctrl_cat i hi.symm
  have hs_not : sub ∉ rCat.image := fun h ↦ by obtain ⟨i, hi⟩ := QRegister.mem_image rCat _ |>.mp h
                                               exact hdk.hsub_cat i hi.symm
  have hv_not : w_v ∉ rCat.image := fun h ↦ by obtain ⟨i, hi⟩ := QRegister.mem_image rCat _ |>.mp h
                                               exact hdk.hv_cat i hi.symm
  have hwrap :=
    UnsignedGivens.inPlaceUVStep_wrap_spec w_ctrl sub w_v hdk.hcs hdk.hcv hdk.hsv hp_in (fun β ↦
    hfix_in β w_ctrl hc_not) (fun β ↦ hfix_in β sub hs_not) (fun β ↦ hfix_in β w_v hv_not)
  refine ⟨_, _, hwrap.1, fun β w hw ↦ ?_⟩
  by_cases hwc : w = w_ctrl
  · subst w
    exact hwrap.2.1 β
  · by_cases hwv : w = w_v
    · subst w
      dsimp only
      rw [hfix_in _ w_ctrl hc_not, hfix_in _ w_v hv_not, hfix_in _ sub hs_not]
      simp only [Function.update_self, Function.update_of_ne hdk.hcv.symm, Function.update_of_ne
        hdk.hcs.symm, Function.update_of_ne hdk.hsv, UnsignedGivens.zmod2_add_cancel_right]
    · dsimp only
      rw [Function.update_of_ne hwv, Function.update_of_ne hwc, hfix_in _ w hw]
      simp only [Function.update_of_ne hwc, Function.update_of_ne hwv]
theorem realizesCleanRef_topZeroAffineLac2KickDyn_widen {Var : Type} [Fintype Var] [DecidableEq Var]
    {n B G' m : ℕ} [NeZero (2 ^ n)] (v : Var) (hB : 2 ≤ B) (idxTop idxMid : ℕ) (row : Fin (G' + 1) →
    Bool → ℕ) (w_ctrl sub w_v : Wire n) (rHot' : QRegister G' n) (rCat : QRegister B n) (a0 : Wire
    n) (rC : QRegister (B - 1) n) (w_p : Wire n) (hd : TopZeroGidneyDisjoint rCat a0 rC w_p) (hdk :
    TopZeroAffineKickDisjoint w_ctrl sub w_v rHot' rCat a0 rC w_p) (rWork : QRegister m n) (hv_mem :
    w_v ∈ rWork.image) (ha0_mem : a0 ∈ rWork.image) (hC_sub : rC.image ⊆ rWork.image) (hcat_work : ∀
    (i : Fin B) (j : Fin m), rCat i ≠ rWork j) : UnsignedGivens.RealizesCleanRef rWork
    (topZeroAffineLac2KickRef hB idxTop idxMid row w_ctrl sub w_v rHot' rCat a0 rC w_p hd hdk)
    (topZeroAffineLac2KickDyn v hB idxTop idxMid row w_ctrl sub w_v rHot' rCat a0 rC w_p hd hdk) :=
    by
  let bs := topZeroAffineTableBitSteps idxTop idxMid row w_ctrl w_v rHot' rCat a0 rC w_p hdk.hcv
    hdk.hh_ctrl hdk.hh_v hdk.hctrl_wp hdk.hv_wp hdk.hh_wp hdk.hctrl_cat hdk.hv_cat hdk.hh_cat
    hdk.hctrl_a0 hdk.hv_a0 hdk.hh_a0 hdk.hctrl_C hdk.hv_C hdk.hh_C
  let sUV := UnsignedGivens.inPlaceUVStep w_ctrl sub w_v hdk.hcs hdk.hcv hdk.hsv
  let rRest := (QRegister.singleton a0).concat rC hd.disj_a0_C
  obtain ⟨_, _, hp_in, hfix_in⟩ := topZeroRawUnsignedPhaseKickRef_phasedPerm hB rCat a0 rC w_p hd bs
  have hwrap_uv :=
    UnsignedGivens.inPlaceUVStep_wrap_spec w_ctrl sub w_v hdk.hcs hdk.hcv hdk.hsv hp_in
    (fun β ↦ hfix_in β w_ctrl fun h ↦ by
      obtain ⟨i, hi⟩ := QRegister.mem_image rCat _ |>.mp h
      exact hdk.hctrl_cat i hi.symm)
    (fun β ↦ hfix_in β sub fun h ↦ by
      obtain ⟨i, hi⟩ := QRegister.mem_image rCat _ |>.mp h
      exact hdk.hsub_cat i hi.symm)
    (fun β ↦ hfix_in β w_v fun h ↦ by
      obtain ⟨i, hi⟩ := QRegister.mem_image rCat _ |>.mp h
      exact hdk.hv_cat i hi.symm)
  obtain ⟨_, _, hp_all, hfix_all⟩ := topZeroAffineLac2KickRef_phasedPerm hB idxTop idxMid row w_ctrl
    sub w_v rHot' rCat a0 rC w_p hd hdk
  have hv_nr : w_v ∉ rRest.image := by
    rw [UnsignedGivens.image_concat_eq, QRegister.image_singleton, Finset.mem_union,
      Finset.mem_singleton,
      QRegister.mem_image]
    rintro (rfl | ⟨i, hi⟩)
    · exact hdk.hv_a0 rfl
    · exact hdk.hv_C i hi.symm
  have hc_nr : sUV.c₁ ∉ rRest.image := by
    change w_ctrl ∉ rRest.image
    rw [UnsignedGivens.image_concat_eq, QRegister.image_singleton, Finset.mem_union,
      Finset.mem_singleton,
      QRegister.mem_image]
    rintro (rfl | ⟨i, hi⟩)
    · exact hdk.hctrl_a0 rfl
    · exact hdk.hctrl_C i hi.symm
  have hs_nr : sUV.c₂ ∉ rRest.image := by
    change sub ∉ rRest.image
    rw [UnsignedGivens.image_concat_eq, QRegister.image_singleton, Finset.mem_union,
      Finset.mem_singleton,
      QRegister.mem_image]
    rintro (rfl | ⟨i, hi⟩)
    · exact hdk.hsub_a0 rfl
    · exact hdk.hsub_C i hi.symm
  have hd_anc : (QRegister.singleton sUV.anc).DisjointWires rRest := by
    rw [UnsignedGivens.disjointWires_iff_disjoint_image, QRegister.image_singleton,
      Finset.disjoint_singleton_left]
    exact hv_nr
  have hmid_rest : Disjoint sUV.midPre.support rRest.image :=
    Finset.disjoint_left.mpr fun q hq ↦ by
      simp only [sUV, UnsignedGivens.inPlaceUVStep, Circuit.support_cnot, Finset.mem_insert,
        Finset.mem_singleton] at hq
      rcases hq with rfl | rfl
      · exact hv_nr
      · exact hc_nr
  let rTotal := (QRegister.singleton sUV.anc).concat rRest hd_anc
  have hsub_tot : rTotal.image ⊆ rWork.image := by
    rw [UnsignedGivens.image_concat_eq, QRegister.image_singleton, UnsignedGivens.image_concat_eq,
      QRegister.image_singleton, Finset.union_subset_iff, Finset.singleton_subset_iff,
      Finset.union_subset_iff, Finset.singleton_subset_iff]
    exact ⟨hv_mem, ha0_mem, hC_sub⟩
  have hcl_tot := UnsignedGivens.cleanProjector_of_phasedPerm_fix rTotal _ hp_all fun β idx hidx ↦
      by
    obtain ⟨j, hj⟩ := QRegister.mem_image rWork _ |>.mp (hsub_tot (QRegister.mem_image rTotal _
      |>.mpr ⟨idx, rfl⟩))
    have hnot_cat : rTotal idx ∉ rCat.image := by rw [← hj, QRegister.mem_image]
                                                  rintro ⟨i, hi⟩
                                                  exact hcat_work i j hi
    rw [hfix_all β (rTotal idx) hnot_cat, hidx]
  have hcl_wrk := UnsignedGivens.cleanProjector_of_phasedPerm_fix rWork _ hp_all fun β j hj ↦ by
    have hnot_cat : rWork j ∉ rCat.image := by rw [QRegister.mem_image]
                                               rintro ⟨i, hi⟩
                                               exact hcat_work i j hi
    rw [hfix_all β (rWork j) hnot_cat, hj]
  exact (UnsignedGivens.RealizesCleanRef.wrapDynamic v sUV _ _ rRest hd_anc (by simp [sUV,
    UnsignedGivens.inPlaceUVStep]) (by simp [sUV,
      UnsignedGivens.inPlaceUVStep]) hc_nr hs_nr hmid_rest
    hwrap_uv.2.2.2.2.2 (realizesCleanRef_topZeroRawUnsignedPhaseKickDyn v hB rCat a0 rC w_p hd bs)
    hcl_tot).widenImage hsub_tot hcl_wrk
open Solution.TwoGearQPEPhase5 Solution.CompactTuned162StepWalk
open Solution.CompactZeroCmp20OuterParam Solution.DihedralWalkQPE
instance instNeZeroTwoPowD11 (k : ℕ) : NeZero (2 ^ k) := ⟨(Nat.two_pow_pos k).ne'⟩
end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.PhaseBD11CompactCore
end
