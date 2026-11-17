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

@[expose] public section

/-!
# Tail-Shifted Three-Gear Dihedral Engine — Part A

Foundational circuits and clean-ancilla realization theorems for Tail-Shifted Three-Gear QPE:
1. Non-involutive QPE clock-permutation conjugation for `QubitisedWalk.qpeMuxUnitary`.
2. Tail-fused coarse dihedral walk `tailFusedDihedralRefl2Dyn` on `bGear` clock bits (`2 ≤ bGear`,
   `2 ^ (bGear - 1) ≤ nStd < 2 ^ bGear - 1`), fusing `nStd` coarse `2 ^ m2`-step chunks with a
   single `kTail`-step tail super-reflection at zero extra coarse steps via `4` all-ones sign
   reflections (`16 * ((bGear - 1) + (aRem - 1))` `T` gates, `0` `.TOFF`).
3. Parametric `TOFF = 0` conditional QPE sub-clock shift (`mod 4` in `4 T` and `mod 8` `+3/+5` in
   `8 T`) wrapped in `Comparators.withEqConstFlagDyn` (`tailShiftClockPermDyn`), covering
   `(46719, m2 = 10)`, `(46719, m2 = 9)`, and `(46847, m2 = 10)` without instantiating heavy
   window trees.
-/

namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.TailShiftThreeGear
open QuantumComputation.Specs QuantumComputation.Specs.P450

open Operator QProg Matrix HermitianMat Circuit Real
open QuantumComputation.Specs QuantumComputation.Specs.P450
open BlockEncodingCore BlockEncodingCircuit
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.WalkQPEBridge hiding
  rActLoc rActLoc_disjoint_rScrLoc rCatInAct rCatLoc rQPEInAct rQPEInAct_disjoint_rWalkCatInAct
  rQPEInAnc rQPELoc rQPELoc_disjoint_rScrLoc rQPELoc_disjoint_rWalkCatLoc rScrLoc rScrUbLoc
  rWalkCatInAct rWalkCatLoc rWalkCatLoc_disjoint_rScrLoc
open WalkQPEBridgeXMeas hiding image_rFullZeroLoc rFullZeroLoc
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.WalkQPEFlexBridge hiding
  cleanRealizesSet_of_rScrUbLoc cleanRealizes_rScrLoc_of_sub
open TopIntegrationBridge Cat11CompactPhase2Bridge
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.DihedralWalkQPE
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.DihedralWalkQPE.BlockReflection
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.DihedralWalkQPE.ApproxIqft16
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.DihedralWalkQPE.SineWindowFlexM
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.DihedralWalkQPE.MultiGearQPE (
  outRemWidth outZeroPrefixReg combARem combAncillas combQubits combWalkCatReg
  combWalkReflRegs combWalkReflCovers comb_hbScr16 CleanWalkRefl2 WalkRefl2ErrLe
  P450RefVarBound ReordSosHyp RealizesP450GroundQPE tensorWalkCat_smul_right
  approxPhaseGrad11Ray exactPhaseGrad11RayUnitary norm_phaseGrad11RayScalar
  exactPhaseGrad11RayUnitary_mulVec_zero approxPhaseGrad11Ray_count_toff
  approxPhaseGrad11Ray_count_t norm_approxPhaseGrad11Ray_sub_le)
open TwoGearBox hiding m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11
open TailShiftBox TwoGearQPEPhase5
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.TwoGearBondDefer
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.TailShiftWindow46847
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.Comparators hiding CleanRealizes
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.Comparators.ComparatorProofs
open scoped Matrix BigOperators Matrix.Norms.L2Operator

/-! ## Section 1: Non-Involutive Clock-Permutation Conjugation & Mux Lifting -/

/-- Equality congruence for `XMeasCircuit.CleanRealizes` in the target unitary. -/
theorem cleanRealizes_of_eq {Var : Type} [Fintype Var] [DecidableEq Var]
    {N k s : ℕ} {v : Var} {rAct : QRegister k N} {rScr : QRegister s N}
    {U₁ U₂ : Unitary (2 ^ k)} {P : DynamicCircuit Var N}
    (h : XMeasCircuit.CleanRealizes v rAct rScr U₁ P) (hU : U₁ = U₂) :
    XMeasCircuit.CleanRealizes v rAct rScr U₂ P :=
  hU ▸ h

/-- Action of `r.basisOutcomeProjector x` on computational basis ket `ket β`. -/
theorem basisOutcomeProjector_mulVec_ket2 {N m : ℕ} (r : QRegister m N)
    (x : Fin (2 ^ m)) (β : BitAssignment N) :
    (r.basisOutcomeProjector x).mulVec (ket β) = if localIdx r β = x then ket β else 0 := by
  funext g
  rw [QRegister.basisOutcomeProjector_mulVec]
  by_cases hg : g = (basisBits N).symm β
  · subst hg
    have hex : r.extractIndex ((basisBits N).symm β) = localIdx r β := by
      apply (basisBits m).injective
      funext i
      rw [QRegister.basisBits_extractIndex, basisBits_basisBitsEquiv_symm]
      exact (congrFun (basisBits_basisBitsEquiv_symm (fun j ↦ β (r j))) i).symm
    rw [hex]
    by_cases hx : localIdx r β = x <;> simp [hx]
  · have hk0 : ket β g = 0 := Pi.single_eq_of_ne hg _
    split_ifs <;> simp [hk0]

theorem writeReg_self2 {N m : ℕ} (β : BitAssignment N) (r : QRegister m N) :
    writeReg β r (basisBits m (localIdx r β)) = β := by
  funext w
  by_cases hw : w ∈ Set.range r.wires
  · obtain ⟨i, rfl⟩ := hw
    rw [writeReg_apply_reg, basisBits_basisBitsEquiv_symm]
  · exact Comparators.writeReg_apply_of_not_mem β r _ w hw

theorem writeReg_idem2 {N m : ℕ} (β : BitAssignment N) (r : QRegister m N)
    (γ₁ γ₂ : BitAssignment m) :
    writeReg (writeReg β r γ₁) r γ₂ = writeReg β r γ₂ := by
  funext w
  by_cases hw : w ∈ Set.range r.wires
  · obtain ⟨i, rfl⟩ := hw
    rw [writeReg_apply_reg, writeReg_apply_reg]
  · simp only [Comparators.writeReg_apply_of_not_mem _ _ _ _ hw]

theorem writeReg_whole2 {N : ℕ} (β γ : BitAssignment N) :
    writeReg β (QRegister.whole N) γ = γ :=
  funext fun w ↦ writeReg_apply_reg β (QRegister.whole N) γ w

theorem writeReg_block_apply {N s w : ℕ} (h : s + w ≤ N)
    (β : BitAssignment N) (γ : BitAssignment w) (i : Wire N) :
    writeReg β (QRegister.block s w h) γ i =
      if hs : s ≤ i.val ∧ i.val < s + w then γ ⟨i.val - s, by omega⟩ else β i := by
  by_cases hs : s ≤ i.val ∧ i.val < s + w
  · rw [dite_eq_left hs]
    have hi : QRegister.block s w h ⟨i.val - s, by omega⟩ = i :=
      Fin.ext (by
        simp only [QRegister.block_apply_val]
        omega)
    conv_lhs => rw [← hi]
    exact writeReg_apply_reg β (QRegister.block s w h) γ ⟨i.val - s, by omega⟩
  · rw [dite_eq_right hs]
    refine Comparators.writeReg_apply_of_not_mem β (QRegister.block s w h) γ i fun hm ↦ hs ?_
    obtain ⟨j, rfl⟩ := hm
    have := j.isLt
    simp only [QRegister.block_apply_val]
    omega

/-- Modular addition permutation `x ↦ (x + c) % 2 ^ w` on `Fin (2 ^ w)`. -/
def addConstModPerm (w c cInv : ℕ) (hinv : (c + cInv) % 2 ^ w = 0) :
    Equiv.Perm (Fin (2 ^ w)) where
  toFun x := ⟨(x.val + c) % 2 ^ w, Nat.mod_lt _ (Nat.two_pow_pos w)⟩
  invFun y := ⟨(y.val + cInv) % 2 ^ w, Nat.mod_lt _ (Nat.two_pow_pos w)⟩
  left_inv x := Fin.ext (by
    calc ((x.val + c) % 2 ^ w + cInv) % 2 ^ w
        = (x.val + (c + cInv)) % 2 ^ w := by rw [Nat.mod_add_mod, add_assoc]
      _ = x.val := by rw [Nat.add_mod, hinv, add_zero, Nat.mod_mod, Nat.mod_eq_of_lt x.isLt])
  right_inv y := Fin.ext (by
    have hinv' : (cInv + c) % 2 ^ w = 0 := by
      rw [add_comm]
      exact hinv
    calc ((y.val + cInv) % 2 ^ w + c) % 2 ^ w
        = (y.val + (cInv + c)) % 2 ^ w := by rw [Nat.mod_add_mod, add_assoc]
      _ = y.val := by rw [Nat.add_mod, hinv', add_zero, Nat.mod_mod, Nat.mod_eq_of_lt y.isLt])

@[simp]
theorem addConstModPerm_val (w c cInv : ℕ) (hinv : (c + cInv) % 2 ^ w = 0)
    (x : Fin (2 ^ w)) : (addConstModPerm w c cInv hinv x).val = (x.val + c) % 2 ^ w := rfl

theorem localIdx_val_one {N : ℕ} (r : QRegister 1 N) (β : BitAssignment N) :
    (localIdx r β).val = bitNat (β (r 0)) := by
  have hlt : regVal r β < 2 := by simpa using regVal_lt r β
  have h0 := regVal_div_pow_mod_two r β (show 0 < 1 by decide)
  rw [_root_.pow_zero, Nat.div_one, Nat.mod_eq_of_lt hlt] at h0
  exact h0

theorem testBit_eq_decide_basisBits {q : ℕ} (j : Fin (2 ^ q)) (i : Fin q) :
    j.val.testBit i.val = decide (basisBits q j i = 1) := by
  rw [basisBits_eq_testBit]
  cases j.val.testBit i.val <;> decide

theorem zmod2_eq_of_decide_eq {a b : ZMod 2}
    (h : decide (a = 1) = decide (b = 1)) : a = b := by
  rcases bit_cases a with rfl | rfl <;> rcases bit_cases b with rfl | rfl <;> revert h <;> decide

theorem add_mul_testBit_of_lt {a b s k : ℕ} (_ha : a < 2 ^ s) (hk : k < s) :
    (a + b * 2 ^ s).testBit k = a.testBit k := by
  have h1 : ((a + b * 2 ^ s) % 2 ^ s).testBit k = (a % 2 ^ s).testBit k := by
    rw [Nat.add_mul_mod_self_right]
  simpa only [Nat.testBit_mod_two_pow, decide_eq_true hk, Bool.true_and] using h1

theorem add_mul_testBit_of_ge {a b s k : ℕ} (ha : a < 2 ^ s) (hk : s ≤ k) :
    (a + b * 2 ^ s).testBit k = b.testBit (k - s) := by
  have hk_eq : k = (k - s) + s := by omega
  rw [hk_eq, ← Nat.testBit_div_two_pow, Nat.add_mul_div_right _ _ (Nat.two_pow_pos s),
    Nat.div_eq_of_lt ha, zero_add, Nat.add_sub_cancel]

/-- Conjugating `QubitisedWalk.qpeMuxUnitary F` by an arbitrary clock permutation `σ`
(`P_{σ⁻¹} * M * P_σ`)
reindexes the multiplexer fiber to `fun x ↦ F (σ x)`. -/
theorem qpeMuxUnitary_conj_perm_gen {b k : ℕ} (σ : Equiv.Perm (Fin (2 ^ b)))
    (F : Fin (2 ^ b) → Unitary (2 ^ k)) :
    (QubitisedWalk.qpeInCombined b k).embedUnitary (permutationUnitary σ.symm) *
        QubitisedWalk.qpeMuxUnitary F *
        (QubitisedWalk.qpeInCombined b k).embedUnitary (permutationUnitary σ) =
      QubitisedWalk.qpeMuxUnitary (fun x ↦ F (σ x)) := by
  let rQ := QubitisedWalk.qpeInCombined b k
  let rW := QubitisedWalk.walkInCombined b k
  let Pσ := (rQ.embedUnitary (permutationUnitary σ)).1
  let Pσi := (rQ.embedUnitary (permutationUnitary σ.symm)).1
  have hdisj : rQ.DisjointWires rW := QubitisedWalk.qpeInCombined_disjoint_walkInCombined b k
  have hloc_any (τ : Equiv.Perm (Fin (2 ^ b))) (β : BitAssignment (b + k)) :
      localIdx rQ (writeReg β rQ (basisBits b (τ (localIdx rQ β)))) = τ (localIdx rQ β) := by
    apply (basisBits b).injective
    funext i
    rw [basisBits_basisBitsEquiv_symm, writeReg_apply_reg]
  have hproj (m : Fin (2 ^ b)) :
      Pσi * rQ.basisOutcomeProjector m * Pσ = rQ.basisOutcomeProjector (σ.symm m) := by
    refine matrix_ext_ket fun β ↦ ?_
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    dsimp only [Pσ, Pσi]
    rw [embedUnitary_permutationUnitary_mulVec_ket, basisOutcomeProjector_mulVec_ket2,
      basisOutcomeProjector_mulVec_ket2, hloc_any]
    have hiff : σ (localIdx rQ β) = m ↔ localIdx rQ β = σ.symm m :=
      (σ.eq_symm_apply).symm
    by_cases hm : localIdx rQ β = σ.symm m
    · rw [ite_eq_left (hiff.mpr hm), ite_eq_left hm, embedUnitary_permutationUnitary_mulVec_ket,
        hloc_any, writeReg_idem2, σ.symm_apply_apply, writeReg_self2]
    · rw [ite_eq_right (mt hiff.mp hm), ite_eq_right hm, Matrix.mulVec_zero]
  apply Subtype.ext
  change Pσi * (QubitisedWalk.qpeMuxUnitary F).1 * Pσ =
    (QubitisedWalk.qpeMuxUnitary (fun x ↦ F (σ x))).1
  rw [QubitisedWalk.qpeMuxUnitary_val, QubitisedWalk.qpeMuxUnitary_val]
  dsimp only [QubitisedWalk.qpeMuxMatrix]
  rw [Finset.mul_sum, Finset.sum_mul]
  let g : Fin (2 ^ b) → Operator (2 ^ (b + k)) := fun x ↦
    rQ.basisOutcomeProjector x * rW.embedMatrix (F (σ x)).1
  have hterm (m : Fin (2 ^ b)) :
      Pσi * (rQ.basisOutcomeProjector m * rW.embedMatrix (F m).1) * Pσ = g (σ.symm m) := by
    have hcomm : rW.embedMatrix (F m).1 * Pσ = Pσ * rW.embedMatrix (F m).1 :=
      (rQ.embedMatrix_comm_of_disjoint rW hdisj (permutationUnitary σ).1 (F m).1).symm
    calc Pσi * (rQ.basisOutcomeProjector m * rW.embedMatrix (F m).1) * Pσ
        = Pσi * rQ.basisOutcomeProjector m * (rW.embedMatrix (F m).1 * Pσ) := by
          simp only [Matrix.mul_assoc]
      _ = (Pσi * rQ.basisOutcomeProjector m * Pσ) * rW.embedMatrix (F m).1 := by
          simp only [hcomm, Matrix.mul_assoc]
      _ = rQ.basisOutcomeProjector (σ.symm m) * rW.embedMatrix (F m).1 := by rw [hproj m]
      _ = g (σ.symm m) := by simp only [g, σ.apply_symm_apply]
  exact (Finset.sum_congr rfl fun m _ ↦ hterm m).trans (Equiv.sum_comp σ.symm g)

/-- Lifts a walk-only `CleanRealizes` onto `rClock.concat rWalk` as a constant `qpeMuxUnitary`. -/
theorem cleanRealizes_walkOnCombined2 {Var : Type} [Fintype Var] [DecidableEq Var]
    {N b k s : ℕ} {v : Var} {rClock : QRegister b N} {rWalk : QRegister k N}
    (hCW : rClock.DisjointWires rWalk) {rFull : QRegister s N}
    {U : Unitary (2 ^ k)} {P : DynamicCircuit Var N}
    (hP : XMeasCircuit.CleanRealizes v rWalk rFull U P) :
    XMeasCircuit.CleanRealizes v (rClock.concat rWalk hCW) rFull
      (QubitisedWalk.qpeMuxUnitary (fun _ : Fin (2 ^ b) ↦ U)) P := by
  refine cleanRealizes_of_eq (XMeasCircuit.CleanRealizes.liftActiveOfEq
    (QubitisedWalk.concat_compose_walkInCombined rClock rWalk hCW).symm hP) ?_
  apply Subtype.ext
  rw [QRegister.embedUnitary_val, QubitisedWalk.qpeMuxUnitary_val]
  dsimp only [QubitisedWalk.qpeMuxMatrix]
  rw [← Finset.sum_mul, (QubitisedWalk.qpeInCombined b k).sum_basisOutcomeProjector, Matrix.one_mul]

/-- Lifts a `qpeMuxUnitary` on a clock sub-slice `rSlice : QRegister b B` to the full `B`-bit clock
combined with `k` walk wires. -/
theorem embed_slice_qpeMuxUnitary {b B k : ℕ} (rSlice : QRegister b B)
    (F : Fin (2 ^ b) → Unitary (2 ^ k)) :
    let rQ := QubitisedWalk.qpeInCombined B k
    let rW := QubitisedWalk.walkInCombined B k
    let hDisj : (rQ.compose rSlice).DisjointWires rW :=
      QubitisedWalk.disjointWires_compose_left
        (QubitisedWalk.qpeInCombined_disjoint_walkInCombined B k)
    ((rQ.compose rSlice).concat rW hDisj).embedUnitary (QubitisedWalk.qpeMuxUnitary F) =
      QubitisedWalk.qpeMuxUnitary (fun x : Fin (2 ^ B) ↦ F (rSlice.extractIndex x)) := by
  intro rQ rW hDisj
  have hdQW := QubitisedWalk.qpeInCombined_disjoint_walkInCombined B k
  apply Subtype.ext
  apply matrix_ext_ket
  intro β
  rw [QRegister.embedUnitary_val, QubitisedWalk.qpeMuxUnitary_val, QubitisedWalk.qpeMuxUnitary_val,
    QubitisedWalk.embedMatrix_qpeMuxMatrix]
  dsimp only [QubitisedWalk.qpeMuxMatrix]
  rw [Matrix.sum_mulVec, Matrix.sum_mulVec]
  have hloc_eq : rSlice.extractIndex (localIdx rQ β) = localIdx (rQ.compose rSlice) β := by
    apply (basisBits b).injective
    funext i
    rw [QRegister.basisBits_extractIndex, basisBits_basisBitsEquiv_symm,
      basisBits_basisBitsEquiv_symm, QRegister.compose_apply]
  rw [Finset.sum_eq_single (localIdx (rQ.compose rSlice) β), Finset.sum_eq_single (localIdx rQ β)]
  · rw [← QRegister.embedMatrix_comm_basisOutcomeProjector_of_disjoint rW (rQ.compose rSlice)
        hDisj.symm (F (localIdx (rQ.compose rSlice) β)).1 (localIdx (rQ.compose rSlice) β),
      ← QRegister.embedMatrix_comm_basisOutcomeProjector_of_disjoint rW rQ
        hdQW.symm (F (rSlice.extractIndex (localIdx rQ β))).1 (localIdx rQ β),
      ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, basisOutcomeProjector_mulVec_ket2,
      basisOutcomeProjector_mulVec_ket2, ite_eq_left rfl, ite_eq_left rfl, hloc_eq]
  · intro x _ hx
    rw [← QRegister.embedMatrix_comm_basisOutcomeProjector_of_disjoint rW rQ hdQW.symm _ x,
      ← Matrix.mulVec_mulVec, basisOutcomeProjector_mulVec_ket2, ite_eq_right (Ne.symm hx),
      Matrix.mulVec_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h
  · intro y _ hy
    rw [← QRegister.embedMatrix_comm_basisOutcomeProjector_of_disjoint rW (rQ.compose rSlice)
        hDisj.symm _ y, ← Matrix.mulVec_mulVec, basisOutcomeProjector_mulVec_ket2,
      ite_eq_right (Ne.symm hy), Matrix.mulVec_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-! ## Section 2: All-Ones Pattern Reflection & Tail-Fused Coarse Dihedral Walk -/

/-- Absorbs additional clean wires into `XMeasCircuit.CleanRealizes` when `W` commutes with
`rScr₂`. -/
theorem absorbCleanActive_of_comm2 {Var : Type} [Fintype Var] [DecidableEq Var]
    {N k s₁ s₂ : ℕ} {v : Var} {rAct : QRegister k N}
    {rScr₁ : QRegister s₁ N} {rScr₂ : QRegister s₂ N}
    {U : Unitary (2 ^ k)} {W : Unitary (2 ^ k)} {P : DynamicCircuit Var N}
    (h : XMeasCircuit.CleanRealizes v rAct rScr₁ U P)
    (hsub : rScr₁.image ⊆ rScr₂.image)
    (hUW : (rAct.embedUnitary U).1 * rScr₂.basisOutcomeProjector 0 =
      (rAct.embedUnitary W).1 * rScr₂.basisOutcomeProjector 0)
    (hWcomm : (rAct.embedUnitary W).1 * rScr₂.basisOutcomeProjector 0 =
      rScr₂.basisOutcomeProjector 0 * (rAct.embedUnitary W).1) :
    XMeasCircuit.CleanRealizes v rAct rScr₂ W P := by
  refine XMeasCircuit.CleanRealizes.absorbCleanActive h hsub hUW ?_
  rw [hWcomm, ← Matrix.mul_assoc, QRegister.basisOutcomeProjector_mul_self]

theorem embedMatrix_reflIn {k m n : ℕ} (r : QRegister m n) (inAll : QRegister k m) :
    r.embedMatrix (QubitisedWalk.reflInUnitary inAll).1 =
      (2 : ℂ) • (r.compose inAll).basisOutcomeProjector 0 - 1 := by
  change r.embedMatrix ((2 : ℂ) • inAll.basisOutcomeProjector 0 - 1) = _
  rw [QubitisedWalk.embedMatrix_sub_local, QRegister.embedMatrix_smul, QRegister.embedMatrix_one,
    CleanDyn.compose_basisOutcomeProjector]

theorem localIdx_eq_zero_iff {N m : ℕ} (r : QRegister m N) (β : BitAssignment N) :
    localIdx r β = 0 ↔ ∀ i : Fin m, β (r i) = 0 := by
  constructor
  · intro h i
    have hb := congrFun (basisBits_basisBitsEquiv_symm (fun j ↦ β (r j))) i
    rw [← hb]
    change basisBits m (localIdx r β) i = 0
    rw [h]
    exact _root_.basisBits_zero_at m i
  · intro hall
    apply (basisBits m).injective
    ext i
    rw [basisBits_basisBitsEquiv_symm, hall i, _root_.basisBits_zero_at]

/-- Right-multiplication of embedded `reflInUnitary` on `rFullZeroLoc`. -/
theorem embed_reflInUnitary_mul_rFullZero {bQPE bCat mOut mMid mLow aRem mRem sUb kZero : ℕ}
    {refl : WalkReflRegs bCat mOut mMid aRem mRem}
    {rAncZero : QRegister kZero (mOut + mMid)}
    (hCov : WalkReflCovers bQPE bCat mOut mMid mLow sUb refl rAncZero) :
    let rWC := rWalkCatLoc bQPE bCat mOut mMid mLow aRem mRem sUb
    let rFull := rFullZeroLoc bQPE bCat mOut mMid mLow aRem mRem sUb rAncZero
    rWC.embedMatrix (QubitisedWalk.reflInUnitary refl.inAll).1 * rFull.basisOutcomeProjector 0 =
      rWC.embedMatrix (QubitisedWalk.reflInUnitary (inAllWalkCat bCat mOut mMid)).1 *
        rFull.basisOutcomeProjector 0 := by
  intro rWC rFull
  rw [embedMatrix_reflIn, embedMatrix_reflIn, Matrix.sub_mul, Matrix.sub_mul,
    Matrix.smul_mul, Matrix.smul_mul]
  congr 2
  refine matrix_ext_ket fun β ↦ ?_
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, basisOutcomeProjector_mulVec_ket2]
  by_cases hz : localIdx rFull β = 0
  · rw [ite_eq_left hz, basisOutcomeProjector_mulVec_ket2, basisOutcomeProjector_mulVec_ket2]
    have hz_all := (localIdx_eq_zero_iff rFull β).mp hz
    have hzero (w : _) (hw : w ∈ rFull.image) : β w = 0 := by
      obtain ⟨idx, rfl⟩ := (QRegister.mem_image _ _).mp hw
      exact hz_all idx
    have hiff : localIdx (rWC.compose refl.inAll) β = 0 ↔
        localIdx (rWC.compose (inAllWalkCat bCat mOut mMid)) β = 0 := by
      rw [localIdx_eq_zero_iff, localIdx_eq_zero_iff]
      refine ⟨fun hall j ↦ ?_, fun hall i ↦ ?_⟩
      · have hmem : (rWC.compose (inAllWalkCat bCat mOut mMid)) j ∈
            (rWC.compose refl.inAll).image ∪ rFull.image :=
          hCov.2 ▸ Finset.mem_union_left _ ((QRegister.mem_image _ _).mpr ⟨j, rfl⟩)
        rcases Finset.mem_union.mp hmem with h1 | h2
        · obtain ⟨i, hi⟩ := (QRegister.mem_image _ _).mp h1
          exact hi ▸ hall i
        · exact hzero _ h2
      · have hmem : (rWC.compose refl.inAll) i ∈
            (rWC.compose (inAllWalkCat bCat mOut mMid)).image ∪ rFull.image :=
          hCov.2.symm ▸ Finset.mem_union_left _ ((QRegister.mem_image _ _).mpr ⟨i, rfl⟩)
        rcases Finset.mem_union.mp hmem with h1 | h2
        · obtain ⟨j, hj⟩ := (QRegister.mem_image _ _).mp h1
          exact hj ▸ hall j
        · exact hzero _ h2
    by_cases h1 : localIdx (rWC.compose refl.inAll) β = 0
    · rw [ite_eq_left h1, ite_eq_left (hiff.mp h1)]
    · rw [ite_eq_right h1, ite_eq_right (mt hiff.mpr h1)]
  · rw [ite_eq_right hz, Matrix.mulVec_zero, Matrix.mulVec_zero]

/-- Commutativity of embedded `qpeMuxUnitary` of `reflInUnitary` with `rFullZeroLoc` projector. -/
theorem embed_qpeMux_reflIn_comm_rFullZero
    {bQPE bCat mOut mMid mLow aRem mRem sUb kZero : ℕ}
    (rAncZero : QRegister kZero (mOut + mMid)) (pred : Fin (2 ^ bQPE) → Bool) :
    let rClock := rQPELoc bQPE bCat mOut mMid mLow aRem mRem sUb
    let rWC := rWalkCatLoc bQPE bCat mOut mMid mLow aRem mRem sUb
    let rComb := rClock.concat rWC
      (rQPELoc_disjoint_rWalkCatLoc bQPE bCat mOut mMid mLow aRem mRem sUb)
    let rFull := rFullZeroLoc bQPE bCat mOut mMid mLow aRem mRem sUb rAncZero
    let R₀ := QubitisedWalk.reflInUnitary (inAllWalkCat bCat mOut mMid)
    (rComb.embedUnitary (QubitisedWalk.qpeMuxUnitary (fun y ↦ if pred y then R₀ else 1))).1 *
        rFull.basisOutcomeProjector 0 =
      rFull.basisOutcomeProjector 0 *
        (rComb.embedUnitary
          (QubitisedWalk.qpeMuxUnitary (fun y ↦ if pred y then R₀ else 1))).1 := by
  intro rClock rWC rComb rFull R₀
  rw [QRegister.embedUnitary_val, QubitisedWalk.qpeMuxUnitary_val,
    QubitisedWalk.embedMatrix_qpeMuxMatrix,
    Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ ↦ ?_
  have hPcomm := QRegister.basisOutcomeProjector_comm rClock m rFull 0
  have hWcomm : rWC.embedMatrix (if pred m then R₀ else 1).1 * rFull.basisOutcomeProjector 0 =
      rFull.basisOutcomeProjector 0 * rWC.embedMatrix (if pred m then R₀ else 1).1 := by
    cases pred m
    · simp only [Bool.false_eq_true, ↓reduceIte, Submonoid.coe_one, QRegister.embedMatrix_one,
        Matrix.one_mul, Matrix.mul_one]
    · simp only [↓reduceIte, R₀, embedMatrix_reflIn, Matrix.sub_mul, Matrix.mul_sub,
        Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul,
        QRegister.basisOutcomeProjector_comm (rWC.compose (inAllWalkCat bCat mOut mMid)) 0 rFull 0]
  rw [Matrix.mul_assoc, hWcomm, ← Matrix.mul_assoc, hPcomm, Matrix.mul_assoc]

/-- Replaces `refl.inAll` with `inAllWalkCat` inside a `qpeMuxUnitary` on `rFullZeroLoc`. -/
theorem embed_qpeMux_reflIn_mul_rFullZero
    {bQPE bCat mOut mMid mLow aRem mRem sUb kZero : ℕ}
    {refl : WalkReflRegs bCat mOut mMid aRem mRem}
    {rAncZero : QRegister kZero (mOut + mMid)}
    (hCov : WalkReflCovers bQPE bCat mOut mMid mLow sUb refl rAncZero)
    (pred : Fin (2 ^ bQPE) → Bool) :
    let rClock := rQPELoc bQPE bCat mOut mMid mLow aRem mRem sUb
    let rWC := rWalkCatLoc bQPE bCat mOut mMid mLow aRem mRem sUb
    let rComb := rClock.concat rWC
      (rQPELoc_disjoint_rWalkCatLoc bQPE bCat mOut mMid mLow aRem mRem sUb)
    let rFull := rFullZeroLoc bQPE bCat mOut mMid mLow aRem mRem sUb rAncZero
    let R_sub := QubitisedWalk.reflInUnitary refl.inAll
    let R₀ := QubitisedWalk.reflInUnitary (inAllWalkCat bCat mOut mMid)
    (rComb.embedUnitary (QubitisedWalk.qpeMuxUnitary (fun y ↦ if pred y then R_sub else 1))).1 *
        rFull.basisOutcomeProjector 0 =
      (rComb.embedUnitary (QubitisedWalk.qpeMuxUnitary (fun y ↦ if pred y then R₀ else 1))).1 *
        rFull.basisOutcomeProjector 0 := by
  intro rClock rWC rComb rFull R_sub R₀
  rw [QRegister.embedUnitary_val, QRegister.embedUnitary_val, QubitisedWalk.qpeMuxUnitary_val,
    QubitisedWalk.qpeMuxUnitary_val, QubitisedWalk.embedMatrix_qpeMuxMatrix,
    QubitisedWalk.embedMatrix_qpeMuxMatrix, Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m _ ↦ ?_
  rw [Matrix.mul_assoc, Matrix.mul_assoc]
  congr 1
  cases pred m
  · simp only [Bool.false_eq_true, ↓reduceIte, Submonoid.coe_one, QRegister.embedMatrix_one]
  · simp only [↓reduceIte]
    exact embed_reflInUnitary_mul_rFullZero hCov

/-- Folded-basis fiber of `tailFusedWalkBodyDyn` on `y : Fin (2 ^ bGear)`. -/
noncomputable def tailFusedBodyFiber {bGear d : ℕ} (nStd : ℕ)
    (uSuperStd uSuperTail R₀ : Unitary d) (y : Fin (2 ^ bGear)) : Unitary d :=
  if y.val = 2 ^ bGear - 1 then
    R₀ * uSuperTail * R₀ *
      (uSuperStd * (R₀ * uSuperStd) ^ (chunkSize2 (bGear - 1) nStd (bGear - 1) - 1) * R₀ *
        chunksFiber (bGear - 1) nStd (R₀ * uSuperStd) R₀ (bGear - 1) y * R₀)
  else
    uSuperTail * R₀ * chunksFiber (bGear - 1) nStd (R₀ * uSuperStd) R₀ bGear y

/-- Unfolded-clock fiber of `tailFusedDihedralRefl2Dyn` on `x : Fin (2 ^ bGear)`. -/
noncomputable def tailFusedScheduleFiber {bGear d : ℕ} (nStd : ℕ)
    (uSuperStd uSuperTail R₀ : Unitary d) (x : Fin (2 ^ bGear)) : Unitary d :=
  tailFusedBodyFiber nStd uSuperStd uSuperTail R₀ (qpeAffinePerm bGear bGear nStd x)

/-- On the all-ones clock state `y.val = 2 ^ bGear - 1`, `chunksFiber` over the lower
`bGear - 1` binary chunks equals `R₀ * W ^ (2 ^ (bGear - 1) - 1) * R₀`. -/
theorem chunksFiber_allOnes_lower {bGear d : ℕ} (hbGear2 : 2 ≤ bGear) (nStd : ℕ)
    (W R₀ : Unitary d) (hR₀ : R₀ * R₀ = 1)
    (y : Fin (2 ^ bGear)) (hy : y.val = 2 ^ bGear - 1) :
    chunksFiber (bGear - 1) nStd W R₀ (bGear - 1) y =
      R₀ * W ^ (2 ^ (bGear - 1) - 1) * R₀ := by
  have hall_bits (k : ℕ) (hk : k < bGear) : y.val.testBit k = true := by
    simpa [hy, Nat.testBit_two_pow_sub_one] using hk
  have hrec : ∀ m : ℕ, m ≤ bGear - 1 → 1 ≤ m →
      chunksFiber (bGear - 1) nStd W R₀ m y = R₀ * W ^ (2 ^ m - 1) * R₀ := by
    intro m hm hpos
    induction m with
    | zero => omega
    | succ k' ih =>
      have hk_lt : k' < bGear - 1 := by omega
      have hpred : chunkPred (bGear - 1) k' y = true := by
        simpa only [chunkPred, ite_eq_left hk_lt] using hall_bits k' (by omega)
      have hsize : chunkSize2 (bGear - 1) nStd k' = 2 ^ k' :=
        ite_eq_left hk_lt
      by_cases hk0 : k' = 0
      · subst hk0
        simp only [chunksFiber, mul_one, chunkFiberStep, hpred, ↓reduceIte, hsize,
          zero_add, _root_.pow_zero, pow_one, Nat.reduceSub]
      · have ihk := ih (by omega) (by omega)
        simp only [chunksFiber, chunkFiberStep, hpred, ↓reduceIte, hsize, ihk]
        have hpow_sum : 2 ^ k' + (2 ^ k' - 1) = 2 ^ (k' + 1) - 1 := by
          have := Nat.two_pow_pos k'
          rw [pow_succ]
          omega
        calc (R₀ * W ^ (2 ^ k') * R₀) * (R₀ * W ^ (2 ^ k' - 1) * R₀)
            = R₀ * W ^ (2 ^ k') * (R₀ * R₀) * W ^ (2 ^ k' - 1) * R₀ := by
              simp only [mul_assoc]
          _ = R₀ * (W ^ (2 ^ k') * W ^ (2 ^ k' - 1)) * R₀ := by
              simp only [hR₀, mul_one, mul_assoc]
          _ = R₀ * W ^ (2 ^ (k' + 1) - 1) * R₀ := by rw [← pow_add, hpow_sum]
  exact hrec (bGear - 1) le_rfl (by omega)

/-- Simplifies the `y.val = 2 ^ bGear - 1` branch of `tailFusedBodyFiber` to
`R₀ * uSuperTail * (R₀ * uSuperStd) ^ nStd`. -/
theorem tailFusedBodyFiber_allOnes_eq {bGear d : ℕ} (hbGear2 : 2 ≤ bGear)
    {nStd : ℕ} (hMlo : 2 ^ (bGear - 1) ≤ nStd)
    (uSuperStd uSuperTail R₀ : Unitary d) (hR₀ : R₀ * R₀ = 1)
    (y : Fin (2 ^ bGear)) (hy : y.val = 2 ^ bGear - 1) :
    tailFusedBodyFiber nStd uSuperStd uSuperTail R₀ y =
      R₀ * uSuperTail * (R₀ * uSuperStd) ^ nStd := by
  unfold tailFusedBodyFiber
  rw [ite_eq_left hy, chunksFiber_allOnes_lower hbGear2 nStd (R₀ * uSuperStd) R₀ hR₀ y hy]
  let W := R₀ * uSuperStd
  have hsize_top : chunkSize2 (bGear - 1) nStd (bGear - 1) = nStd + 1 - 2 ^ (bGear - 1) :=
    ite_eq_right (Nat.lt_irrefl _)
  rw [hsize_top]
  have hexp : nStd + 1 - 2 ^ (bGear - 1) - 1 + 1 + (2 ^ (bGear - 1) - 1) = nStd := by
    have := Nat.two_pow_pos (bGear - 1)
    omega
  calc R₀ * uSuperTail * R₀ *
          (uSuperStd * W ^ (nStd + 1 - 2 ^ (bGear - 1) - 1) * R₀ *
            (R₀ * W ^ (2 ^ (bGear - 1) - 1) * R₀) * R₀)
      = R₀ * uSuperTail * ((R₀ * uSuperStd) * W ^ (nStd + 1 - 2 ^ (bGear - 1) - 1) *
          (R₀ * R₀) * W ^ (2 ^ (bGear - 1) - 1) * (R₀ * R₀)) := by
        simp only [mul_assoc]
    _ = R₀ * uSuperTail *
          (W * W ^ (nStd + 1 - 2 ^ (bGear - 1) - 1) * W ^ (2 ^ (bGear - 1) - 1)) := by
        rw [hR₀, mul_one, mul_one]
    _ = R₀ * uSuperTail * W ^ nStd := by
        rw [← pow_succ', ← pow_add, hexp]

end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.TailShiftThreeGear
end
