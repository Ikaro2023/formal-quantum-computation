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

public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.Slot2ApexGidney46

@[expose] public section
set_option allowUnsafeReducibility true

namespace QuantumComputation.Specs.StoppingPowerSolution
open SpecsAux

section ModInterWalkRSum42Hoist
@[expose] public section
namespace InterWalkRSum42Hoist
section ConfigInterWalkRSum42Hoist
set_option backward.isDefEq.respectTransparency true
set_option exponentiation.threshold 256
local instance (priority := 1000000) instNeZeroTwoPowRSum42HoistSem (k : ℕ) : NeZero (2 ^ k) :=
  ⟨Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos k)⟩
open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt Real
open scoped Matrix BigOperators Matrix.Norms.L2Operator
open DyadicQft64 hiding dyadicTurn phaseGradKet
open DyadicQft64.PhasePerm SpecsAux.SpecMirror
open StepBBlock0 (bitsVal_eq_of_testBit)
open FullSysCatSegmentBridge
  (fullSysCoreWires fullSysBEWires beCoreBlock)
open NuclearTwistAndXor654Concrete (rElecSlotAxis)
open NuclearTwistRealizes
  (uXor32Core uXor32Core_inv xor32BitFn xor32CorePerm
  slot2AxisSum)
open ProjZ512QftAndTwist288 (rCoreBlock48)
open SingleCatClosure
  (kActSingleCatClosure qSigInSingleCat cSlackParkSingleCat cSlackUnparkSingleCat
    compose_concat_eq_singleCat slackParkStepsSingleCat optXSingleCat)
open OraAndPrepBundle (castNatUnitary)
open FullSysMomSlots0135Concrete (momCoreWires)
open SpecsAux.BridgeFermionicComm (permutationUnitary_apply)
open PhaseGradSignalRot
  (RevStep runRevList compileRevList compileRevList_mulVec_ket)
open PosMomSelectDynamic (unitaryConj unitaryConj_val)
open FullSysFullPrepareAndTopConcrete (coreAncSym)
open MeasureBranchHadamardSem (matrix_ext_ket)
theorem uStream42Init_def : uStream42Init = uXor32Full *
    (uStreamFull 2 * (uStreamFull 1 * (uStreamFull 0 * uXor32Full))) := rfl
attribute [local irreducible] uHybridStream220 uStream42Init
def PreservesFeature {d : ℕ} {α : Type*} (f : Fin d → α) (M : Operator d) : Prop :=
  ∀ i j : Fin d, M i j ≠ 0 → f i = f j
theorem PreservesFeature.one {d : ℕ} {α : Type*} (f : Fin d → α) :
    PreservesFeature f (1 : Operator d) := fun i j hne ↦
  congrArg f (Classical.byContradiction fun hij ↦ hne (by simp [hij]))
theorem PreservesFeature.diagonal {d : ℕ} {α : Type*} (f : Fin d → α) (g : Fin d → ℂ) :
    PreservesFeature f (Matrix.diagonal g) := fun i j hne ↦
  congrArg f (Classical.byContradiction fun hij ↦ hne (by simp [hij]))
theorem PreservesFeature.smul {d : ℕ} {α : Type*} {f : Fin d → α} {M : Operator d}
    (z : ℂ) (hM : PreservesFeature f M) : PreservesFeature f (z • M) := fun i j hne ↦
  hM i j (right_ne_zero_of_mul (by simpa [Matrix.smul_apply] using hne))
theorem PreservesFeature.neg {d : ℕ} {α : Type*} {f : Fin d → α} {M : Operator d}
    (hM : PreservesFeature f M) : PreservesFeature f (-M) := fun i j hne ↦
  hM i j (neg_ne_zero.mp (by simpa [Matrix.neg_apply] using hne))
theorem PreservesFeature.add {d : ℕ} {α : Type*} {f : Fin d → α} {A B : Operator d}
    (hA : PreservesFeature f A) (hB : PreservesFeature f B) : PreservesFeature f (A + B) :=
  fun i j hne ↦ if ha : A i j = 0 then hB i j (by simpa [Matrix.add_apply, ha] using hne)
    else hA i j ha
theorem PreservesFeature.sub {d : ℕ} {α : Type*} {f : Fin d → α} {A B : Operator d}
    (hA : PreservesFeature f A) (hB : PreservesFeature f B) : PreservesFeature f (A - B) := by
  simpa [sub_eq_add_neg] using hA.add hB.neg
theorem PreservesFeature.mul {d : ℕ} {α : Type*} {f : Fin d → α} {A B : Operator d}
    (hA : PreservesFeature f A) (hB : PreservesFeature f B) : PreservesFeature f (A * B) := by
  intro i j hne
  obtain ⟨k, _, hk⟩ := Finset.exists_ne_zero_of_sum_ne_zero (by rwa [Matrix.mul_apply] at hne)
  exact (hA i k (left_ne_zero_of_mul hk)).trans (hB k j (right_ne_zero_of_mul hk))
theorem PreservesFeature.conjTranspose {d : ℕ} {α : Type*} {f : Fin d → α} {M : Operator d}
    (hM : PreservesFeature f M) : PreservesFeature f Mᴴ := fun i j hne ↦
  (hM j i (star_ne_zero.mp hne)).symm
theorem PreservesFeature.unitary_inv {d : ℕ} {α : Type*} {f : Fin d → α} {U : Unitary d}
    (hU : PreservesFeature f U.1) : PreservesFeature f (U⁻¹).1 := hU.conjTranspose
theorem PreservesFeature.unitaryConj {d : ℕ} {α : Type*} {f : Fin d → α} {U V : Unitary d}
    (hU : PreservesFeature f U.1) (hV : PreservesFeature f V.1) :
    PreservesFeature f (unitaryConj U V).1 := by
  simpa [unitaryConj_val] using (hU.conjTranspose.mul hV).mul hU
theorem PreservesFeature.of_map {d : ℕ} {α β : Type*} {f : Fin d → α} (g : α → β)
    {M : Operator d} (hM : PreservesFeature f M) : PreservesFeature (fun x ↦ g (f x)) M := fun
    i j hne ↦ congrArg g (hM i j hne)
theorem PreservesFeature.id_imp {d : ℕ} {α : Type*} (f : Fin d → α) {M : Operator d}
    (hM : PreservesFeature id M) : PreservesFeature f M := fun i j hne ↦ congrArg f (hM i j hne)
theorem PreservesFeature.basisOutcomeProjector {k n : ℕ} (r : QRegister k n) (o : Fin (2 ^ k)) :
    PreservesFeature id (r.basisOutcomeProjector o) :=
  r.basisOutcomeProjector_eq_diagonal o ▸ PreservesFeature.diagonal id _
theorem PreservesFeature.embedMatrix_id {k n : ℕ} (r : QRegister k n) {A : Operator (2 ^ k)}
    (hA : PreservesFeature id A) : PreservesFeature id (r.embedMatrix A) := by
  intro x y hne
  by_cases hAgree : (r.basisSplitEquiv x).2 = (r.basisSplitEquiv y).2
  · rw [QRegister.embedMatrix_apply, ite_eq_left hAgree, mul_one] at hne
    change A (r.extractIndex x) (r.extractIndex y) ≠ 0 at hne
    have hExt : r.extractIndex x = r.extractIndex y := hA _ _ hne
    have hOut : r.AgreeOutside x y := (r.basisSplit_environment_eq_iff x y).mp hAgree
    apply (basisBitsEquiv n).injective
    funext w
    by_cases hw : w ∈ Set.range r.wires
    · rcases hw with ⟨idx, rfl⟩
      have hx := r.basisBits_extractIndex x idx
      have hy := r.basisBits_extractIndex y idx
      change basisBits n x (r idx) = basisBits n y (r idx)
      rw [← hx, ← hy, hExt]
    · exact hOut w hw
  · rw [QRegister.embedMatrix_apply, ite_eq_right hAgree, mul_zero] at hne
    exact False.elim (hne rfl)
theorem preservesFeature_embedMatrix_of_extract {k n : ℕ} {α : Type*} (r : QRegister k n)
    (g : Fin (2 ^ k) → α) {A : Operator (2 ^ k)} (hA : PreservesFeature g A) :
    PreservesFeature (fun x : Fin (2 ^ n) ↦ g (r.extractIndex x)) (r.embedMatrix A) := by
  intro x y hne
  by_cases hAgree : (r.basisSplitEquiv x).2 = (r.basisSplitEquiv y).2
  · rw [QRegister.embedMatrix_apply, ite_eq_left hAgree, mul_one] at hne
    change A (r.extractIndex x) (r.extractIndex y) ≠ 0 at hne
    exact hA _ _ hne
  · rw [QRegister.embedMatrix_apply, ite_eq_right hAgree, mul_zero] at hne
    exact False.elim (hne rfl)
theorem preservesFeature_permutationUnitary {d : ℕ} {α : Type*} (f : Fin d → α)
    (σ : Equiv.Perm (Fin d)) (hσ : ∀ j : Fin d, f (σ j) = f j) :
    PreservesFeature f (Operator.permutationUnitary σ).1 := fun i j hne ↦
  (congrArg f (Classical.byContradiction fun hij ↦
    hne (by simp [permutationUnitary_apply, hij]))).trans (hσ j)
theorem preservesFeature_of_mulVec_basisKet {n : ℕ} {α : Type*} (f : Fin (2 ^ n) → α)
    (M : Operator (2 ^ n)) (g : BitAssignment n → BitAssignment n) (hket : ∀ β : BitAssignment
    n, M.mulVec (basisKet β) = basisKet (g β)) (hf : ∀ j : Fin (2 ^ n), f ((basisBitsEquiv
    n).symm (g (basisBits n j))) = f j) : PreservesFeature f M := by
  intro i j hne
  have hentry : M i j = (M.mulVec (Pi.single j 1)) i := by
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  rw [pi_single_eq_basisKet, hket (basisBits n j)] at hentry
  dsimp only [basisKet, basisState] at hentry
  rw [hentry, Pi.single_apply] at hne
  by_cases hij : i = (basisBitsEquiv n).symm (g (basisBits n j))
  · rw [hij, hf j]
  · simp [hij] at hne
def low3924Bits {n : ℕ} (hn : 3924 ≤ n) (x : Fin (2 ^ n)) : Fin 3924 → ZMod 2 :=
  fun q ↦ basisBits n x ⟨q.val, lt_of_lt_of_le q.isLt hn⟩
def FixesLow3924 {n : ℕ} (hn : 3924 ≤ n) (M : Operator (2 ^ n)) : Prop :=
  PreservesFeature (low3924Bits hn) M
def IsHigh3924Reg {k n : ℕ} (r : QRegister k n) : Prop := ∀ i : Fin k, 3924 ≤ (r i).val
def IsLow3924Prefix {k n : ℕ} (hk : 3924 ≤ k) (hn : 3924 ≤ n) (r : QRegister k n) : Prop := ∀
    q : Fin 3924, r ⟨q.val, lt_of_lt_of_le q.isLt hk⟩ = ⟨q.val, lt_of_lt_of_le q.isLt hn⟩
theorem isLow3924Prefix_block0 {k n : ℕ} (hk : 3924 ≤ k) (hn : 3924 ≤ n) (hle : 0 + k ≤ n) :
    IsLow3924Prefix hk hn (QRegister.block 0 k hle) := fun _ ↦ Fin.ext (by simp)
theorem isLow3924Prefix_compose {k m n : ℕ} (hk : 3924 ≤ k) (hm : 3924 ≤ m) (hn : 3924 ≤ n)
    {r₁ : QRegister m n} {r₂ : QRegister k m} (h₁ : IsLow3924Prefix hm hn r₁)
    (h₂ : IsLow3924Prefix hk hm r₂) : IsLow3924Prefix hk hn (r₁.compose r₂) :=
  fun q ↦ (congrArg r₁ (h₂ q)).trans (h₁ q)
theorem isLow3924Prefix_concat_left {k₁ k₂ n : ℕ} (hk₁ : 3924 ≤ k₁) (hn : 3924 ≤ n)
    {r₁ : QRegister k₁ n} (r₂ : QRegister k₂ n) (hD : r₁.DisjointWires r₂)
    (h₁ : IsLow3924Prefix hk₁ hn r₁) : IsLow3924Prefix (le_trans hk₁ (Nat.le_add_right k₁ k₂))
    hn (r₁.concat r₂ hD) := by
  intro q
  have hcast : (⟨q.val, lt_of_lt_of_le q.isLt (le_trans hk₁ (Nat.le_add_right k₁ k₂))⟩ :
      Fin (k₁ + k₂)) = Fin.castAdd k₂ ⟨q.val, lt_of_lt_of_le q.isLt hk₁⟩ := rfl
  rw [hcast, QRegister.concat_apply_left]
  exact h₁ q
theorem isHigh3924Reg_concat {k₁ k₂ n : ℕ} {r₁ : QRegister k₁ n} {r₂ : QRegister k₂ n}
    (hD : r₁.DisjointWires r₂) (h₁ : IsHigh3924Reg r₁) (h₂ : IsHigh3924Reg r₂) : IsHigh3924Reg
    (r₁.concat r₂ hD) := by
  intro i
  refine Fin.addCases (fun a ↦ ?_) (fun b ↦ ?_) i
  · rw [QRegister.concat_apply_left]; exact h₁ a
  · rw [QRegister.concat_apply_right]; exact h₂ b
theorem low3924Bits_extractIndex_of_prefix {k n : ℕ} {hk : 3924 ≤ k} {hn : 3924 ≤ n}
    {r : QRegister k n} (hr : IsLow3924Prefix hk hn r) (x : Fin (2 ^ n)) : low3924Bits hk
    (r.extractIndex x) = low3924Bits hn x := by
  funext q
  dsimp only [low3924Bits]
  rw [r.basisBits_extractIndex x ⟨q.val, lt_of_lt_of_le q.isLt hk⟩]
  exact congrArg (basisBits n x) (hr q)
theorem fixesLow3924_embedMatrix_prefix {k n : ℕ} {hk : 3924 ≤ k} {hn : 3924 ≤ n}
    {r : QRegister k n} (hr : IsLow3924Prefix hk hn r) {A : Operator (2 ^ k)}
    (hA : FixesLow3924 hk A) : FixesLow3924 hn (r.embedMatrix A) := by
  intro x y hne
  have h0 := preservesFeature_embedMatrix_of_extract r (low3924Bits hk) hA x y hne
  dsimp only at h0
  rwa [low3924Bits_extractIndex_of_prefix hr x, low3924Bits_extractIndex_of_prefix hr y] at h0
theorem fixesLow3924_embedMatrix_high {k n : ℕ} (hn : 3924 ≤ n) {r : QRegister k n}
    (hr : IsHigh3924Reg r) (A : Operator (2 ^ k)) : FixesLow3924 hn (r.embedMatrix A) := by
  intro x y hne
  by_cases hAgree : (r.basisSplitEquiv x).2 = (r.basisSplitEquiv y).2
  · have hOut : r.AgreeOutside x y := (r.basisSplit_environment_eq_iff x y).mp hAgree
    funext q
    dsimp only [low3924Bits]
    refine hOut ⟨q.val, lt_of_lt_of_le q.isLt hn⟩ ?_
    rintro ⟨idx, hidx⟩
    have hv := congrArg Fin.val hidx
    have hge := hr idx
    have hlt := q.isLt
    dsimp only at hv
    omega
  · rw [QRegister.embedMatrix_apply, ite_eq_right hAgree, mul_zero] at hne
    exact False.elim (hne rfl)
theorem fixesLow3924_castNatUnitary {a b : ℕ} (h : a = b) (ha : 3924 ≤ a) (hb : 3924 ≤ b)
    {U : Unitary (2 ^ a)} (hU : FixesLow3924 ha U.1) : FixesLow3924 hb (castNatUnitary h U).1 := by
  subst h
  exact hU
noncomputable def rawStreamOfLow (b : Fin 3924 → ZMod 2) (w : Fin 3) : ℕ := ∑ e : Fin numElectrons,
    bitsVal (fun t : Fin 6 ↦ b ⟨18 * e.val + 6 * w.val + t.val, by
      have he : e.val < 218 := e.isLt
      have hw := w.isLt; have ht := t.isLt
      omega⟩)
noncomputable def hoistStreamOfLow (b : Fin 3924 → ZMod 2) (w : Fin 3) : ℕ :=
  rawStreamOfLow (fun q ↦ if q.val % 6 = 5 then b q + 1 else b q) w
noncomputable def rawStreamVec {n : ℕ} (hn : 3924 ≤ n) (x : Fin (2 ^ n)) : Fin 3 → ℕ :=
  rawStreamOfLow (low3924Bits hn x)
noncomputable def hoistStreamVec {n : ℕ} (hn : 3924 ≤ n) (x : Fin (2 ^ n)) : Fin 3 → ℕ :=
  hoistStreamOfLow (low3924Bits hn x)
def PreservesRawStream42 {n : ℕ} (hn : 3924 ≤ n) (M : Operator (2 ^ n)) : Prop :=
  PreservesFeature (rawStreamVec hn) M
def PreservesHoistStream42 {n : ℕ} (hn : 3924 ≤ n) (M : Operator (2 ^ n)) : Prop :=
  PreservesFeature (hoistStreamVec hn) M
theorem FixesLow3924.preservesRawStream42 {n : ℕ} {hn : 3924 ≤ n} {M : Operator (2 ^ n)}
    (hM : FixesLow3924 hn M) : PreservesRawStream42 hn M := hM.of_map rawStreamOfLow
theorem FixesLow3924.preservesHoistStream42 {n : ℕ} {hn : 3924 ≤ n} {M : Operator (2 ^ n)}
    (hM : FixesLow3924 hn M) : PreservesHoistStream42 hn M := hM.of_map hoistStreamOfLow
theorem rawStreamOfLow_eq_slot2AxisSum {mPayload : ℕ}
    (γ : BitAssignment (fullSysCoreWires mPayload)) (w : Fin 3) :
    rawStreamOfLow (fun q : Fin 3924 ↦ γ ⟨q.val, by
      have := q.isLt
      dsimp [fullSysCoreWires, SpecsAux.SpecMirror.systemQubits,
        SpecsAux.SpecMirror.numElectrons, SpecsAux.SpecMirror.electronBits,
          SpecsAux.SpecMirror.projectileBits]
      omega⟩) w = slot2AxisSum w γ := by
  unfold rawStreamOfLow slot2AxisSum regVal
  refine Finset.sum_congr rfl fun e _ ↦ congrArg bitsVal (funext fun t ↦ congrArg γ ?_)
  ext
  simp [rElecSlotAxis, QRegExt.idReg, Nat.add_assoc]
theorem h3924_core : 3924 ≤ fullSysCoreWires 80 := by decide
theorem h3924_momCore : 3924 ≤ momCoreWires 80 := by decide
theorem h3924_momCat : 3924 ≤ momCoreWires 80 + 48 := by decide
theorem h3924_cat : 3924 ≤ fullSysCoreWires 80 + 48 := by decide
theorem h3924_be : 3924 ≤ fullSysBEWires 80 := by decide
theorem h3924_actOrig : 3924 ≤ kActOrig := by decide
theorem isLow3924Prefix_rBEOrig : IsLow3924Prefix h3924_be h3924_actOrig rBEOrig :=
  isLow3924Prefix_block0 h3924_be h3924_actOrig _
theorem isLow3924Prefix_beCoreBlock80 : IsLow3924Prefix h3924_core h3924_be (beCoreBlock 80)
    := isLow3924Prefix_block0 h3924_core h3924_be _
theorem isLow3924Prefix_rCoreOrig : IsLow3924Prefix h3924_core h3924_actOrig rCoreOrig :=
  isLow3924Prefix_compose h3924_core h3924_be h3924_actOrig
    isLow3924Prefix_rBEOrig isLow3924Prefix_beCoreBlock80
theorem isLow3924Prefix_rCTOrig : IsLow3924Prefix h3924_cat h3924_actOrig rCTOrig :=
  isLow3924Prefix_concat_left h3924_core h3924_actOrig rPG48Orig hCoreOrig_disj_PG48Orig
    isLow3924Prefix_rCoreOrig
theorem slot2AxisSum_swapElec0Bits {mPayload : ℕ} (e₀ : Fin numElectrons)
    (γ : BitAssignment (fullSysCoreWires mPayload)) (w : Fin 3) :
    slot2AxisSum w (CoinDispatchedBarrel288.swapElec0Bits e₀ γ) = slot2AxisSum w γ := by
  by_cases he0 : e₀ = ⟨0, by decide⟩
  · subst he0
    have h0 : CoinDispatchedBarrel288.swapElec0Bits (⟨0, by decide⟩ : Fin numElectrons) γ = γ := by
      funext k; simp [CoinDispatchedBarrel288.swapElec0Bits]
    rw [h0]
  · have he0_val : e₀.val ≠ 0 := fun h ↦ he0 (Fin.ext h)
    unfold slot2AxisSum
    have hterm : ∀ e : Fin numElectrons, regVal (rElecSlotAxis (QRegExt.idReg _) e w)
          (CoinDispatchedBarrel288.swapElec0Bits e₀ γ) = regVal (rElecSlotAxis (QRegExt.idReg _)
          (Equiv.swap (⟨0, by decide⟩ : Fin numElectrons) e₀ e) w) γ := by
      intro e
      unfold regVal
      refine congrArg bitsVal (funext fun t ↦ ?_)
      have ht := t.isLt; have hw := w.isLt; have he := e.isLt; have he₀ := e₀.isLt
      dsimp only [SpecsAux.SpecMirror.numElectrons] at he he₀
      by_cases h1 : e = ⟨0, by decide⟩
      · subst h1
        rw [Equiv.swap_apply_left]
        simp only [rElecSlotAxis, QRegister.slice_apply, QRegExt.idReg_apply]
        dsimp only [CoinDispatchedBarrel288.swapElec0Bits]
        rw [ite_eq_right he0_val, dite_eq_left (by dsimp; omega)]
        refine congrArg γ (Fin.ext ?_); dsimp; omega
      · by_cases h2 : e = e₀
        · subst h2
          rw [Equiv.swap_apply_right]
          simp only [rElecSlotAxis, QRegister.slice_apply, QRegExt.idReg_apply]
          dsimp only [CoinDispatchedBarrel288.swapElec0Bits]
          rw [ite_eq_right he0_val, dite_eq_right (by dsimp; omega),
            dite_eq_left ⟨by dsimp; omega, by dsimp; omega⟩]
          refine congrArg γ (Fin.ext ?_); dsimp; omega
        · have hne0 : e.val ≠ 0 := fun hv ↦ h1 (Fin.ext hv)
          have hnee : e.val ≠ e₀.val := fun hv ↦ h2 (Fin.ext hv)
          rw [Equiv.swap_apply_of_ne_of_ne h1 h2]
          simp only [rElecSlotAxis, QRegister.slice_apply, QRegExt.idReg_apply]
          dsimp only [CoinDispatchedBarrel288.swapElec0Bits]
          rw [ite_eq_right he0_val, dite_eq_right (by dsimp; omega),
            dite_eq_right (by dsimp; omega)]
    simp_rw [hterm]
    exact Equiv.sum_comp (Equiv.swap (⟨0, by decide⟩ : Fin numElectrons) e₀)
      (fun e ↦ regVal (rElecSlotAxis (QRegExt.idReg _) e w) γ)
theorem fixesLow3924_embed_dyadicDiag {k n B : ℕ} (hn : 3924 ≤ n) (r : QRegister k n)
    (e : BitAssignment k → ℤ) :
    FixesLow3924 hn (r.embedUnitary (DyadicQft64.dyadicDiagUnitary k B e)).1 :=
  PreservesFeature.id_imp _
    (PreservesFeature.embedMatrix_id r (PreservesFeature.diagonal id _))
theorem fixesLow3924_uApexShift45 {kSys W : ℕ} (hk : 3924 ≤ kSys) (hW : W ≤ 45)
    (δ : BitAssignment kSys → ℤ) : FixesLow3924 (le_trans hk (Nat.le_add_right kSys 48))
    (JunctionApexCSA288.uApexShift45 kSys W hW δ).1 := by
  unfold JunctionApexCSA288.uApexShift45
    JunctionApexCSA288.uApexShiftA
  simp only [Submonoid.coe_mul]
  refine PreservesFeature.mul ?_ (PreservesFeature.diagonal _ _)
  refine preservesFeature_permutationUnitary _
    (JunctionApexCSA288.apexWinPermA kSys 45 W hW δ) (fun j ↦ ?_)
  funext q
  dsimp only [low3924Bits]
  have hcast : (⟨q.val, lt_of_lt_of_le q.isLt (le_trans hk (Nat.le_add_right kSys 48))⟩ :
      Fin (kSys + 48)) = Fin.castAdd 48 ⟨q.val, lt_of_lt_of_le q.isLt hk⟩ := rfl
  rw [hcast]
  have hfst : (splitSysCatEquiv kSys 48
      (JunctionApexCSA288.apexWinPermA kSys 45 W hW δ j)).1 =
      (splitSysCatEquiv kSys 48 j).1 := by
    simp [JunctionApexCSA288.apexWinPermA,
      JunctionApexCSA288.apexWinMidPermA]
  exact congrFun hfst ⟨q.val, lt_of_lt_of_le q.isLt hk⟩
set_option exponentiation.threshold 8192 in
theorem fixesLow3924_coreAncSym80_embed (U : Unitary (2 ^ (80 + 6))) :
    FixesLow3924 h3924_core ((coreAncSym 80).embedUnitary U).1 := by
  rw [QRegister.embedUnitary_val]
  refine fixesLow3924_embedMatrix_high h3924_core (fun idx ↦ ?_) U.1
  have := idx.isLt
  dsimp [coreAncSym, qreg_block_apply, SpecsAux.SpecMirror.systemQubits,
    SpecsAux.SpecMirror.numElectrons, SpecsAux.SpecMirror.electronBits,
      SpecsAux.SpecMirror.projectileBits]
  omega
theorem qSig80_ge_3924 : 3924 ≤ (qSigInSingleCat 80 48 40).val := by decide
set_option exponentiation.threshold 8192 in
theorem fixesLow3924_single_qSig (g : PrimitiveGate 1) :
    FixesLow3924 h3924_actOrig (Circuit.single g (qSigInSingleCat 80 48 40)).eval.1 := by
  rw [Circuit.eval_single, QRegister.embedUnitary_val]
  refine fixesLow3924_embedMatrix_high h3924_actOrig (fun i ↦ ?_) _
  fin_cases i
  exact qSig80_ge_3924
def revStepHigh3924Bool {n : ℕ} : RevStep n → Bool
  | .x w => decide (3924 ≤ w.val)
  | .cnot c t => decide (3924 ≤ c.val ∧ 3924 ≤ t.val)
  | .toff a b t => decide (3924 ≤ a.val ∧ 3924 ≤ b.val ∧ 3924 ≤ t.val)
abbrev RevStepHigh3924 {n : ℕ} (s : RevStep n) : Prop := revStepHigh3924Bool s = true
theorem revStep_run_eq_low {n : ℕ} {s : RevStep n} (hs : RevStepHigh3924 s)
    (β : BitAssignment n) {w : Wire n} (hw : w.val < 3924) : s.run β w = β w := by
  cases s with
  | x q =>
      have hq : 3924 ≤ q.val := of_decide_eq_true hs
      have hne : w ≠ q := fun h ↦ by subst h; exact Nat.not_le_of_lt hw hq
      simp [RevStep.run, Function.update_of_ne hne]
  | cnot c t =>
      have hct : 3924 ≤ c.val ∧ 3924 ≤ t.val := of_decide_eq_true hs
      have hne : w ≠ t := fun h ↦ by subst h; exact Nat.not_le_of_lt hw hct.2
      dsimp [RevStep.run]
      split_ifs <;> simp [Function.update_of_ne hne]
  | toff a b t =>
      have habt : 3924 ≤ a.val ∧ 3924 ≤ b.val ∧ 3924 ≤ t.val := of_decide_eq_true hs
      have hne : w ≠ t := fun h ↦ by subst h; exact Nat.not_le_of_lt hw habt.2.2
      dsimp [RevStep.run]
      split_ifs <;> simp [Function.update_of_ne hne]
theorem runRevList_eq_low {n : ℕ} : ∀ (ss : List (RevStep n)), (∀ s ∈ ss, RevStepHigh3924 s) →
      ∀ (β : BitAssignment n) {w : Wire n}, w.val < 3924 → runRevList ss β w = β w
  | [], _, _, _, _ => rfl
  | s :: ss, hss, β, _, hw =>
      (runRevList_eq_low ss (fun s' hs' ↦ hss s' (List.mem_cons_of_mem s hs')) (s.run β) hw).trans
        (revStep_run_eq_low (hss s List.mem_cons_self) β hw)
theorem fixesLow3924_compileRevList {n : ℕ} (hn : 3924 ≤ n) (ss : List (RevStep n))
    (hss : ∀ s ∈ ss, RevStepHigh3924 s) : FixesLow3924 hn (compileRevList ss).eval.1 :=
  preservesFeature_of_mulVec_basisKet (low3924Bits hn) _ (runRevList ss)
    (compileRevList_mulVec_ket ss) fun j ↦ funext fun q ↦ by
      dsimp only [low3924Bits]
      rw [basisBits_basisBitsEquiv_symm_eq]
      exact runRevList_eq_low ss hss (basisBits n j) q.isLt
theorem slackParkSteps80_high :
    ∀ s ∈ slackParkStepsSingleCat 80 48 40, RevStepHigh3924 s := by decide
set_option exponentiation.threshold 8192 in
theorem fixesLow3924_cSlackParkSingleCat :
    FixesLow3924 h3924_actOrig (cSlackParkSingleCat 80 48 40).eval.1 :=
  fixesLow3924_compileRevList h3924_actOrig _ slackParkSteps80_high
set_option exponentiation.threshold 8192 in
theorem fixesLow3924_cSlackUnparkSingleCat :
    FixesLow3924 h3924_actOrig (cSlackUnparkSingleCat 80 48 40).eval.1 :=
  fixesLow3924_compileRevList h3924_actOrig _ fun s hs ↦
    slackParkSteps80_high s (List.mem_reverse.mp hs)
set_option exponentiation.threshold 8192 in
theorem fixesLow3924_optXSingleCat (b : Bool) :
    FixesLow3924 h3924_actOrig (optXSingleCat 80 48 40 b).1 := by
  cases b
  · exact PreservesFeature.one _
  · exact fixesLow3924_single_qSig PrimitiveGate.X
noncomputable def streamTarget42 (S : Fin 3 → ℕ) : Fin (2 ^ 42) :=
  (basisBitsEquiv 42).symm fun j : Fin 42 ↦
    if (S ⟨j.val / 14, by omega⟩).testBit (j.val % 14) then 1 else 0
theorem basisBits_streamTarget42 (S : Fin 3 → ℕ) (w : Fin 3) (i : Fin 14) : basisBits 42
    (streamTarget42 S) (rSum14In42 w i) = if (S w).testBit i.val then 1 else 0 := by
  dsimp only [streamTarget42, rSum14In42]
  rw [basisBits_basisBitsEquiv_symm_eq]
  rw [qreg_block_apply]
  dsimp only
  have hdiv : (14 * w.val + i.val) / 14 = w.val := by omega
  have hmod : (14 * w.val + i.val) % 14 = i.val := by omega
  have hw : (⟨(14 * w.val + i.val) / 14, by omega⟩ : Fin 3) = w := Fin.ext hdiv
  rw [hw, hmod]
noncomputable def streamProjOpGen {kAct kSum N : ℕ} (rAct : QRegister kAct N)
    (rSum : QRegister kSum N) (T : Fin (2 ^ kAct) → Fin (2 ^ kSum)) : Operator (2 ^ N) :=
    Matrix.of fun x y ↦ if rAct.extractIndex x = rAct.extractIndex y ∧ rSum.extractIndex y = 0
    ∧ rSum.extractIndex x = T (rAct.extractIndex y) then 1 else 0
noncomputable abbrev streamProjOp (F : Fin (2 ^ kActOrig) → (Fin 3 → ℕ)) : Operator
    (2 ^ kFull80) := streamProjOpGen rAct0 rSum0 (fun a ↦ streamTarget42 (F a))
theorem act0_sum0_join_unique {x₁ x₂ : Fin (2 ^ kFull80)}
    (hA : rAct0.extractIndex x₁ = rAct0.extractIndex x₂)
    (hS : rSum0.extractIndex x₁ = rSum0.extractIndex x₂) : x₁ = x₂ := by
  apply (basisBitsEquiv kFull80).injective
  funext g
  change basisBits kFull80 x₁ g = basisBits kFull80 x₂ g
  by_cases hg : g.val < kActOrig
  · have h1 := rAct0.basisBits_extractIndex x₁ ⟨g.val, hg⟩
    have h2 := rAct0.basisBits_extractIndex x₂ ⟨g.val, hg⟩
    have hrg : rAct0 ⟨g.val, hg⟩ = g := Fin.ext (by simp [rAct0])
    rw [hrg] at h1 h2
    exact h1.symm.trans ((congrArg (fun z ↦ basisBits kActOrig z ⟨g.val, hg⟩) hA).trans h2)
  · have hlt42 : g.val - kActOrig < 42 := by
      have := g.isLt
      dsimp [kFull80, mActHoist, kActOrig, mActOrig, kActSingleCatClosure] at this ⊢
      omega
    have h1 := rSum0.basisBits_extractIndex x₁ ⟨g.val - kActOrig, hlt42⟩
    have h2 := rSum0.basisBits_extractIndex x₂ ⟨g.val - kActOrig, hlt42⟩
    have hrg : rSum0 ⟨g.val - kActOrig, hlt42⟩ = g := Fin.ext (by simp [rSum0]; omega)
    rw [hrg] at h1 h2
    exact h1.symm.trans ((congrArg (fun z ↦ basisBits 42 z ⟨g.val - kActOrig, hlt42⟩) hS).trans h2)
noncomputable def joinActSum (a : Fin (2 ^ kActOrig)) (s : Fin (2 ^ 42)) : Fin (2 ^ kFull80) :=
  (basisBitsEquiv kFull80).symm fun g ↦ if hg : g.val < kActOrig then
      basisBits kActOrig a ⟨g.val, hg⟩
    else
      basisBits 42 s ⟨g.val - kActOrig, by
        have := g.isLt
        dsimp [kFull80, mActHoist, kActOrig, mActOrig, kActSingleCatClosure] at this ⊢
        omega⟩
theorem extractIndex_rAct0_joinActSum (a : Fin (2 ^ kActOrig)) (s : Fin (2 ^ 42)) :
    rAct0.extractIndex (joinActSum a s) = a := by
  apply (basisBitsEquiv kActOrig).injective
  funext i
  change basisBits kActOrig (rAct0.extractIndex (joinActSum a s)) i = basisBits kActOrig a i
  rw [rAct0.basisBits_extractIndex]
  dsimp only [joinActSum]
  rw [basisBits_basisBitsEquiv_symm_eq]
  have hi : (rAct0 i).val < kActOrig := by
    simp [rAct0]
  rw [dite_eq_left hi]
  refine congrArg (basisBits kActOrig a) (Fin.ext ?_)
  simp [rAct0]
theorem extractIndex_rSum0_joinActSum (a : Fin (2 ^ kActOrig)) (s : Fin (2 ^ 42)) :
    rSum0.extractIndex (joinActSum a s) = s := by
  apply (basisBitsEquiv 42).injective
  funext i
  change basisBits 42 (rSum0.extractIndex (joinActSum a s)) i = basisBits 42 s i
  rw [rSum0.basisBits_extractIndex]
  dsimp only [joinActSum]
  rw [basisBits_basisBitsEquiv_symm_eq]
  have hi : ¬ (rSum0 i).val < kActOrig := by
    rw [rSum0, qreg_block_apply]; dsimp; omega
  rw [dite_eq_right hi]
  refine congrArg (basisBits 42 s) (Fin.ext ?_)
  dsimp [rSum0, qreg_block_apply]; omega
theorem basisSplit_rAct0_eq_iff (x y : Fin (2 ^ kFull80)) : (rAct0.basisSplitEquiv x).2 =
    (rAct0.basisSplitEquiv y).2 ↔ rSum0.extractIndex x = rSum0.extractIndex y := by
  rw [rAct0.basisSplit_environment_eq_iff]
  constructor
  · intro hOut
    apply (basisBitsEquiv 42).injective
    funext i
    change basisBits 42 (rSum0.extractIndex x) i = basisBits 42 (rSum0.extractIndex y) i
    rw [rSum0.basisBits_extractIndex, rSum0.basisBits_extractIndex]
    refine hOut (rSum0 i) ?_
    rintro ⟨idx, hidx⟩
    exact hAct0_disj_Sum0.ne idx i hidx
  · intro hS w hw
    have hge : ¬ w.val < kActOrig := fun hlt ↦ hw ⟨⟨w.val, hlt⟩, Fin.ext (by simp [rAct0])⟩
    have hlt42 : w.val - kActOrig < 42 := by
      have := w.isLt
      dsimp [kFull80, mActHoist, kActOrig, mActOrig, kActSingleCatClosure] at this ⊢
      omega
    have hwEq : rSum0 ⟨w.val - kActOrig, hlt42⟩ = w := Fin.ext (by simp [rSum0]; omega)
    have h1 := rSum0.basisBits_extractIndex x ⟨w.val - kActOrig, hlt42⟩
    have h2 := rSum0.basisBits_extractIndex y ⟨w.val - kActOrig, hlt42⟩
    rw [hwEq] at h1 h2
    exact h1.symm.trans ((congrArg (fun z ↦ basisBits 42 z ⟨w.val - kActOrig, hlt42⟩) hS).trans h2)
theorem embedAct_comm_streamOpGen {kAct kSum N : ℕ} (rAct : QRegister kAct N)
    (rSum : QRegister kSum N) (join : Fin (2 ^ kAct) → Fin (2 ^ kSum) → Fin (2 ^ N)) (hUnique
    : ∀ {x₁ x₂ : Fin (2 ^ N)}, rAct.extractIndex x₁ = rAct.extractIndex x₂ → rSum.extractIndex
    x₁ = rSum.extractIndex x₂ → x₁ = x₂) (hJoinAct : ∀ a s, rAct.extractIndex (join a s) = a)
    (hJoinSum : ∀ a s, rSum.extractIndex (join a s) = s) (hSplit : ∀ x y : Fin (2 ^ N),
    (rAct.basisSplitEquiv x).2 = (rAct.basisSplitEquiv y).2 ↔ rSum.extractIndex x =
    rSum.extractIndex y) {α : Type*} {F : Fin (2 ^ kAct) → α} (target : α → Fin (2 ^ kSum))
    {A : Operator (2 ^ kAct)} (hA : PreservesFeature F A) : rAct.embedMatrix A *
    streamProjOpGen rAct rSum (fun a ↦ target (F a)) = streamProjOpGen rAct rSum
    (fun a ↦ target (F a)) * rAct.embedMatrix A := by
  let P := streamProjOpGen rAct rSum (fun a ↦ target (F a))
  change rAct.embedMatrix A * P = P * rAct.embedMatrix A
  ext x y
  rw [Matrix.mul_apply, Matrix.mul_apply]
  by_cases hSy : rSum.extractIndex y = 0
  · let zL := join (rAct.extractIndex y) (rSum.extractIndex x)
    let zR := join (rAct.extractIndex x) 0
    have hL : ∑ z : Fin (2 ^ N), rAct.embedMatrix A x z * P z y =
        if rSum.extractIndex x = target (F (rAct.extractIndex y)) then
          A (rAct.extractIndex x) (rAct.extractIndex y) else 0 := by
      rw [Finset.sum_eq_single zL]
      · have hEnv : (rAct.basisSplitEquiv x).2 = (rAct.basisSplitEquiv zL).2 :=
          (hSplit x zL).mpr (hJoinSum _ _).symm
        rw [QRegister.embedMatrix_apply, ite_eq_left hEnv, mul_one]
        dsimp only [P, streamProjOpGen, Matrix.of_apply]
        rw [hJoinAct, hJoinSum]
        simp [hSy]
      · intro z _ hzne
        dsimp only [P, streamProjOpGen, Matrix.of_apply]
        by_cases hzy : rAct.extractIndex z = rAct.extractIndex y ∧ rSum.extractIndex y = 0 ∧
            rSum.extractIndex z = target (F (rAct.extractIndex y))
        · by_cases hEnv : (rAct.basisSplitEquiv x).2 = (rAct.basisSplitEquiv z).2
          · have hSx := (hSplit x z).mp hEnv
            exfalso
            refine hzne (hUnique ?_ ?_)
            · rw [hzy.1, hJoinAct]
            · rw [← hSx, hJoinSum]
          · simp only [QRegister.embedMatrix_apply, ite_eq_right hEnv, mul_zero, zero_mul]
        · rw [ite_eq_right hzy, mul_zero]
      · simp
    have hR : ∑ z : Fin (2 ^ N), P x z * rAct.embedMatrix A z y =
        if rSum.extractIndex x = target (F (rAct.extractIndex x)) then
          A (rAct.extractIndex x) (rAct.extractIndex y) else 0 := by
      rw [Finset.sum_eq_single zR]
      · have hEnv : (rAct.basisSplitEquiv zR).2 = (rAct.basisSplitEquiv y).2 :=
          (hSplit zR y).mpr ((hJoinSum _ _).trans hSy.symm)
        rw [QRegister.embedMatrix_apply, ite_eq_left hEnv, mul_one]
        dsimp only [P, streamProjOpGen, Matrix.of_apply]
        rw [hJoinAct, hJoinSum]
        simp
      · intro z _ hzne
        by_cases hEnv : (rAct.basisSplitEquiv z).2 = (rAct.basisSplitEquiv y).2
        · have hSz : rSum.extractIndex z = 0 := ((hSplit z y).mp hEnv).trans hSy
          dsimp only [P, streamProjOpGen, Matrix.of_apply]
          by_cases hAz : rAct.extractIndex x = rAct.extractIndex z
          · exfalso
            refine hzne (hUnique ?_ ?_)
            · rw [← hAz, hJoinAct]
            · rw [hSz, hJoinSum]
          · simp [hAz]
        · simp only [QRegister.embedMatrix_apply, ite_eq_right hEnv, mul_zero]
      · simp
    rw [hL, hR]
    by_cases hAxy : A (rAct.extractIndex x) (rAct.extractIndex y) = 0
    · simp [hAxy]
    · rw [hA _ _ hAxy]
  · have hL0 : ∀ z : Fin (2 ^ N), P z y = 0 := fun z ↦ by
      simp [P, streamProjOpGen, Matrix.of_apply, hSy]
    have hR0 : ∀ z : Fin (2 ^ N), rAct.embedMatrix A z y = 0 ∨ P x z = 0 := fun z ↦ by
      by_cases hEnv : (rAct.basisSplitEquiv z).2 = (rAct.basisSplitEquiv y).2
      · right
        have hSz : rSum.extractIndex z ≠ 0 := by
          rw [(hSplit z y).mp hEnv]; exact hSy
        simp [P, streamProjOpGen, Matrix.of_apply, hSz]
      · left; simp [QRegister.embedMatrix_apply, hEnv]
    have hLSum : ∑ z : Fin (2 ^ N), rAct.embedMatrix A x z * P z y = 0 :=
      Finset.sum_eq_zero fun z _ ↦ by rw [hL0 z, mul_zero]
    have hRSum : ∑ z : Fin (2 ^ N), P x z * rAct.embedMatrix A z y = 0 :=
      Finset.sum_eq_zero fun z _ ↦ by
        rcases hR0 z with hz | hz
        · rw [hz, mul_zero]
        · rw [hz, zero_mul]
    exact hLSum.trans hRSum.symm
theorem embedAct0_comm_streamOp {F : Fin (2 ^ kActOrig) → (Fin 3 → ℕ)}
    {A : Operator (2 ^ kActOrig)} (hA : PreservesFeature F A) : rAct0.embedMatrix A *
    streamProjOp F = streamProjOp F * rAct0.embedMatrix A := embedAct_comm_streamOpGen rAct0
    rSum0 joinActSum (fun hA0 hS0 ↦ act0_sum0_join_unique hA0 hS0)
    extractIndex_rAct0_joinActSum extractIndex_rSum0_joinActSum basisSplit_rAct0_eq_iff
    streamTarget42 hA
noncomputable def E_rawStream42 : Operator (2 ^ kFull80) :=
  (uStreamFull 2 * (uStreamFull 1 * uStreamFull 0)).1 * pSum42Zero
noncomputable def E_stream42 : Operator (2 ^ kFull80) := uStream42Init.1 * pSum42Zero
theorem projZeroGen_mulVec_basisKet {k N : ℕ} (r : QRegister k N) (β : BitAssignment N) :
    (r.basisOutcomeProjector 0).mulVec (basisKet β) =
      if r.extractIndex ((basisBitsEquiv N).symm β) = 0 then basisKet β else 0 := by
  rw [r.basisOutcomeProjector_eq_diagonal]
  ext x
  dsimp only [basisKet, basisState]
  rw [Matrix.mulVec_diagonal]
  by_cases h0 : r.extractIndex ((basisBitsEquiv N).symm β) = 0
  · rw [ite_eq_left h0]
    by_cases hx : x = (basisBitsEquiv N).symm β
    · subst hx; simp [h0]
    · simp [hx]
  · rw [ite_eq_right h0]
    by_cases hx : x = (basisBitsEquiv N).symm β
    · subst hx; simp [h0]
    · simp [hx]
theorem pSum42Zero_mulVec_basisKet (β : BitAssignment kFull80) : pSum42Zero.mulVec
    (basisKet β) = if rSum0.extractIndex ((basisBitsEquiv kFull80).symm β) = 0 then basisKet β
    else 0 := projZeroGen_mulVec_basisKet rSum0 β
theorem rSum0_extractIndex_eq_zero_iff (β : BitAssignment kFull80) : rSum0.extractIndex
    ((basisBitsEquiv kFull80).symm β) = 0 ↔ ∀ j : Fin 42, β (rSum0 j) = 0 :=
  ((QRegExt.extractIndex_eq_zero_iff rSum0) _).trans
    (by simp only [basisBits_basisBitsEquiv_symm_eq])
theorem streamProjOpGen_mulVec_basisKet {kAct kSum N : ℕ} (rAct : QRegister kAct N)
    (rSum : QRegister kSum N) (join : Fin (2 ^ kAct) → Fin (2 ^ kSum) → Fin (2 ^ N)) (hUnique
    : ∀ {x₁ x₂ : Fin (2 ^ N)}, rAct.extractIndex x₁ = rAct.extractIndex x₂ → rSum.extractIndex
    x₁ = rSum.extractIndex x₂ → x₁ = x₂) (hJoinAct : ∀ a s, rAct.extractIndex (join a s) = a)
    (hJoinSum : ∀ a s, rSum.extractIndex (join a s) = s) (T : Fin (2 ^ kAct) → Fin (2 ^ kSum))
    (β : BitAssignment N) : (streamProjOpGen rAct rSum T).mulVec (basisKet β) = if
    rSum.extractIndex ((basisBitsEquiv N).symm β) = 0 then basisKet (basisBits N (join
    (rAct.extractIndex ((basisBitsEquiv N).symm β)) (T (rAct.extractIndex ((basisBitsEquiv
    N).symm β))))) else 0 := by
  let y := (basisBitsEquiv N).symm β
  ext x
  have hmv : ((streamProjOpGen rAct rSum T).mulVec (basisKet β)) x =
      streamProjOpGen rAct rSum T x y := by
    change ((streamProjOpGen rAct rSum T).mulVec (Pi.single y 1)) x = _
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  rw [hmv]
  dsimp only [streamProjOpGen, Matrix.of_apply]
  by_cases h0 : rSum.extractIndex y = 0
  · rw [ite_eq_left h0]
    let tgt := join (rAct.extractIndex y) (T (rAct.extractIndex y))
    have hiff : (rAct.extractIndex x = rAct.extractIndex y ∧ rSum.extractIndex y = 0 ∧
        rSum.extractIndex x = T (rAct.extractIndex y)) ↔ x = tgt := by
      constructor
      · rintro ⟨hA, _, hS⟩
        refine hUnique ?_ ?_
        · rw [hA, hJoinAct]
        · rw [hS, hJoinSum]
      · rintro rfl
        exact ⟨hJoinAct _ _, h0, hJoinSum _ _⟩
    rw [if_congr hiff rfl rfl]
    dsimp only [basisKet, basisState]
    rw [basisBitsEquiv_symm_basisBits_eq, Pi.single_apply]
  · rw [ite_eq_right h0]
    simp [h0]
theorem streamProjOp_mulVec_basisKet (F : Fin (2 ^ kActOrig) → (Fin 3 → ℕ))
    (β : BitAssignment kFull80) : (streamProjOp F).mulVec (basisKet β) = if rSum0.extractIndex
    ((basisBitsEquiv kFull80).symm β) = 0 then basisKet (basisBits kFull80 (joinActSum
    (rAct0.extractIndex ((basisBitsEquiv kFull80).symm β)) (streamTarget42 (F
    (rAct0.extractIndex ((basisBitsEquiv kFull80).symm β)))))) else 0 :=
    streamProjOpGen_mulVec_basisKet rAct0 rSum0 joinActSum
    (fun hA0 hS0 ↦ act0_sum0_join_unique hA0 hS0) extractIndex_rAct0_joinActSum
    extractIndex_rSum0_joinActSum (fun a ↦ streamTarget42 (F a)) β
theorem E_rawStream42_eq_streamProjOp :
    E_rawStream42 = streamProjOp (rawStreamVec h3924_actOrig) := by
  apply matrix_ext_ket; intro β
  change ((uStreamFull 2 * (uStreamFull 1 * uStreamFull 0)).1 * pSum42Zero).mulVec (basisKet β) =
    (streamProjOp (rawStreamVec h3924_actOrig)).mulVec (basisKet β)
  rw [← Matrix.mulVec_mulVec, pSum42Zero_mulVec_basisKet, streamProjOp_mulVec_basisKet]
  by_cases h0 : rSum0.extractIndex ((basisBitsEquiv kFull80).symm β) = 0
  · rw [ite_eq_left h0, ite_eq_left h0]
    have hzAll : ∀ j : Fin 42, β (rSum0 j) = 0 := (rSum0_extractIndex_eq_zero_iff β).mp h0
    have hDisjS {a b : Fin 3} (hne : a ≠ b) (i : Fin 14) :
        rSum14Full b i ∉ (rSum14Full a).image := fun hm ↦ by
      rcases (QRegister.mem_image _ _).mp hm with ⟨k, hk⟩
      exact (hSum14In42_disj hne).ne k i (rSum0.wires.injective hk)
    have hDisjC (a : Fin 3) (q : Fin (fullSysCoreWires 80)) :
        rCoreFull q ∉ (rSum14Full a).image := fun hm ↦ by
      rcases (QRegister.mem_image _ _).mp hm with ⟨k, hk⟩
      exact (hCoreFull_disj_Sum14 a).ne q k hk.symm
    obtain ⟨β₁, hk₁, hout₁, hsum₁⟩ := uHybridStream220_compute_ket 0 rCoreFull (rSum14Full 0)
      (hCoreFull_disj_Sum14 0) β fun i ↦ hzAll (rSum14In42 0 i)
    have hz1 : ∀ i : Fin 14, β₁ (rSum14Full 1 i) = 0 := fun i ↦ by
      rw [hout₁ _ (hDisjS (by decide) i)]; exact hzAll (rSum14In42 1 i)
    obtain ⟨β₂, hk₂, hout₂, hsum₂⟩ :=
      uHybridStream220_compute_ket 1 rCoreFull (rSum14Full 1) (hCoreFull_disj_Sum14 1) β₁ hz1
    have hCore₁ : (fun q ↦ β₁ (rCoreFull q)) = (fun q ↦ β (rCoreFull q)) :=
      funext fun q ↦ hout₁ _ (hDisjC 0 q)
    have hz2 : ∀ i : Fin 14, β₂ (rSum14Full 2 i) = 0 := fun i ↦ by
      rw [hout₂ _ (hDisjS (by decide) i), hout₁ _ (hDisjS (by decide) i)]
      exact hzAll (rSum14In42 2 i)
    obtain ⟨β₃, hk₃, hout₃, hsum₃⟩ :=
      uHybridStream220_compute_ket 2 rCoreFull (rSum14Full 2) (hCoreFull_disj_Sum14 2) β₂ hz2
    have hCore₂ : (fun q ↦ β₂ (rCoreFull q)) = (fun q ↦ β (rCoreFull q)) :=
      funext fun q ↦ (hout₂ _ (hDisjC 1 q)).trans (congrFun hCore₁ q)
    change (uStreamFull 0).1.mulVec (basisKet β) = basisKet β₁ at hk₁
    change (uStreamFull 1).1.mulVec (basisKet β₁) = basisKet β₂ at hk₂
    change (uStreamFull 2).1.mulVec (basisKet β₂) = basisKet β₃ at hk₃
    simp only [Submonoid.coe_mul, ← Matrix.mulVec_mulVec]
    change (uStreamFull 2).1.mulVec
      ((uStreamFull 1).1.mulVec ((uStreamFull 0).1.mulVec (basisKet β))) = _
    rw [hk₁, hk₂, hk₃]
    refine congrArg basisKet ?_
    let y := (basisBitsEquiv kFull80).symm β
    have hRawEq (w : Fin 3) : slot2AxisSum w (fun q ↦ β (rCoreFull q)) =
        rawStreamVec h3924_actOrig (rAct0.extractIndex y) w := by
      rw [← rawStreamOfLow_eq_slot2AxisSum (fun q ↦ β (rCoreFull q)) w]
      dsimp only [rawStreamVec]
      refine congrFun (congrArg rawStreamOfLow (funext fun q ↦ ?_)) w
      dsimp only [low3924Bits]
      rw [rAct0.basisBits_extractIndex y ⟨q.val, lt_of_lt_of_le q.isLt h3924_actOrig⟩,
        basisBits_basisBitsEquiv_symm_eq]
      refine congrArg β ?_
      have hpre := isLow3924Prefix_rCoreOrig q
      change rCoreFull ⟨q.val, _⟩ = rAct0 ⟨q.val, _⟩
      exact congrArg rAct0 hpre
    funext g
    by_cases hg : g.val < kActOrig
    · have hgAct : g = rAct0 ⟨g.val, hg⟩ := Fin.ext (by simp [rAct0])
      have hnot : ∀ w : Fin 3, g ∉ (rSum14Full w).image := fun w hm ↦ by
        rcases (QRegister.mem_image _ _).mp hm with ⟨k, hk⟩
        exact (hAct0_disj_Sum14 w).ne ⟨g.val, hg⟩ k (hgAct.symm.trans hk.symm)
      rw [hout₃ g (hnot 2), hout₂ g (hnot 1), hout₁ g (hnot 0)]
      dsimp only [joinActSum]
      rw [basisBits_basisBitsEquiv_symm_eq, dite_eq_left hg, rAct0.basisBits_extractIndex,
        basisBits_basisBitsEquiv_symm_eq, ← hgAct]
    · have hlt42 : g.val - kActOrig < 42 := by
        have := g.isLt
        dsimp [kFull80, mActHoist, kActOrig, mActOrig, kActSingleCatClosure] at this ⊢
        omega
      let j42 : Fin 42 := ⟨g.val - kActOrig, hlt42⟩
      let w : Fin 3 := ⟨j42.val / 14, by omega⟩
      let i14 : Fin 14 := ⟨j42.val % 14, by omega⟩
      have hjEq : rSum14In42 w i14 = j42 := Fin.ext (by simp [rSum14In42, w, i14]; omega)
      have hgSum : rSum14Full w i14 = g := by
        change rSum0 (rSum14In42 w i14) = g
        rw [hjEq]; exact Fin.ext (by simp [rSum0, j42]; omega)
      dsimp only [joinActSum]
      rw [basisBits_basisBitsEquiv_symm_eq, dite_eq_right hg]
      change β₃ g =
        basisBits 42 (streamTarget42 (rawStreamVec h3924_actOrig (rAct0.extractIndex y))) j42
      rw [← hjEq, basisBits_streamTarget42, ← hgSum, ← hRawEq w]
      have hw3 : ∀ x : Fin 3, x = 0 ∨ x = 1 ∨ x = 2 := by decide
      rcases hw3 w with hw | hw | hw <;> rw [hw]
      · rw [hout₃ _ (hDisjS (by decide) i14), hout₂ _ (hDisjS (by decide) i14), hsum₁ i14]
      · rw [hout₃ _ (hDisjS (by decide) i14), hsum₂ i14, hCore₁]
      · rw [hsum₃ i14, hCore₂]
  · rw [ite_eq_right h0, ite_eq_right h0, Matrix.mulVec_zero]
theorem embedPermGen_mulVec_basisKet {k N : ℕ} (r : QRegister k N)
    (σ : Equiv.Perm (Fin (2 ^ k))) (β fβ : BitAssignment N)
    (hout : ∀ w : Wire N, w ∉ r.image → fβ w = β w) (hExt : r.extractIndex ((basisBitsEquiv
    N).symm fβ) = σ (r.extractIndex ((basisBitsEquiv N).symm β))) :
    (r.embedUnitary (Operator.permutationUnitary σ)).1.mulVec (basisKet β) = basisKet fβ := by
  ext x
  let y := (basisBitsEquiv N).symm β
  let xTgt := (basisBitsEquiv N).symm fβ
  have hmv : ((r.embedUnitary (Operator.permutationUnitary σ)).1.mulVec (basisKet β)) x =
      (r.embedUnitary (Operator.permutationUnitary σ)).1 x y := by
    change ((r.embedUnitary (Operator.permutationUnitary σ)).1.mulVec (Pi.single y 1)) x = _
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  rw [hmv]
  change r.embedMatrix (Operator.permutationUnitary σ).1 x y =
    (Pi.single xTgt (1 : ℂ) : Fin (2 ^ N) → ℂ) x
  have hEnvTgt : (r.basisSplitEquiv xTgt).2 = (r.basisSplitEquiv y).2 := by
    rw [r.basisSplit_environment_eq_iff]
    intro w hw
    dsimp only [xTgt, y]
    rw [basisBits_basisBitsEquiv_symm_eq, basisBits_basisBitsEquiv_symm_eq]
    exact hout w (fun hm ↦ by
      rcases (QRegister.mem_image _ _).mp hm with ⟨idx, rfl⟩
      exact hw ⟨idx, rfl⟩)
  by_cases hx : x = xTgt
  · subst hx
    rw [QRegister.embedMatrix_apply, ite_eq_left hEnvTgt, mul_one,
      permutationUnitary_apply, ite_eq_left hExt, Pi.single_eq_same]
  · rw [Pi.single_eq_of_ne hx]
    by_cases hEnv : (r.basisSplitEquiv x).2 = (r.basisSplitEquiv y).2
    · rw [QRegister.embedMatrix_apply, ite_eq_left hEnv, mul_one, permutationUnitary_apply]
      have hneExt : r.extractIndex x ≠ σ (r.extractIndex y) := by
        intro heq
        refine hx ?_
        apply (basisBitsEquiv N).injective
        funext w
        change basisBits N x w = basisBits N xTgt w
        by_cases hw : w ∈ Set.range r.wires
        · rcases hw with ⟨q, rfl⟩
          have h1 := r.basisBits_extractIndex x q
          have h2 := r.basisBits_extractIndex xTgt q
          rw [← h1, ← h2, heq, ← hExt]
        · have ho1 := (r.basisSplit_environment_eq_iff x y).mp hEnv w hw
          have ho2 := (r.basisSplit_environment_eq_iff xTgt y).mp hEnvTgt w hw
          exact ho1.trans ho2.symm
      rw [ite_eq_right hneExt]
    · rw [QRegister.embedMatrix_apply, ite_eq_right hEnv, mul_zero]
set_option exponentiation.threshold 8192 in
theorem uXor32Full_mulVec_basisKet (β : BitAssignment kFull80) : uXor32Full.1.mulVec (basisKet β) =
      basisKet (fun g ↦ if g.val < 3924 ∧ g.val % 6 = 5 then β g + 1 else β g) := by
  let f (γ : BitAssignment kFull80) : BitAssignment kFull80 :=
    fun g ↦ if g.val < 3924 ∧ g.val % 6 = 5 then γ g + 1 else γ g
  have hout : ∀ w : Wire kFull80, w ∉ rCoreFull.image → f β w = β w := by
    intro w hw
    dsimp only [f]
    by_cases hlt : w.val < 3924
    · exfalso
      refine hw ((QRegister.mem_image rCoreFull w).mpr ⟨⟨w.val, lt_of_lt_of_le hlt h3924_core⟩, ?_⟩)
      have hp := isLow3924Prefix_rCoreOrig ⟨w.val, hlt⟩
      exact (congrArg rAct0 hp).trans (Fin.ext (by simp [rAct0]))
    · simp [hlt]
  have hin (q : Fin (fullSysCoreWires 80)) :
      f β (rCoreFull q) = xor32BitFn 80 (fun i ↦ β (rCoreFull i)) q := by
    change (if (rCoreFull q).val < 3924 ∧ (rCoreFull q).val % 6 = 5 then β (rCoreFull q) + 1
        else β (rCoreFull q)) =
      (if q.val < 3924 ∧ q.val % 6 = 5 then β (rCoreFull q) + 1 else β (rCoreFull q))
    by_cases hq : q.val < 3924
    · have hp := isLow3924Prefix_rCoreOrig ⟨q.val, hq⟩
      have hv : (rCoreFull q).val = q.val :=
        (congrArg (fun x ↦ (rAct0 x).val) hp).trans (by simp [rAct0])
      rw [hv]
    · have hv : ¬ (rCoreFull q).val < 3924 := fun hlt ↦ by
        have hp := isLow3924Prefix_rCoreOrig ⟨(rCoreFull q).val, hlt⟩
        have ha : rCoreFull ⟨(rCoreFull q).val, lt_of_lt_of_le hlt h3924_core⟩ = rCoreFull q :=
          Fin.ext ((congrArg (fun x ↦ (rAct0 x).val) hp).trans (by simp [rAct0]))
        exact hq (rCoreFull.wires.injective ha ▸ hlt)
      simp only [hv, hq, false_and, ↓reduceIte]
  let y := (basisBitsEquiv kFull80).symm β
  let xTgt := (basisBitsEquiv kFull80).symm (f β)
  have hExtTgt : rCoreFull.extractIndex xTgt = xor32CorePerm 80 (rCoreFull.extractIndex y) := by
    apply (basisBitsEquiv (fullSysCoreWires 80)).injective
    funext q
    change basisBits (fullSysCoreWires 80) (rCoreFull.extractIndex xTgt) q =
      basisBits (fullSysCoreWires 80) (xor32CorePerm 80 (rCoreFull.extractIndex y)) q
    rw [rCoreFull.basisBits_extractIndex]
    dsimp only [xTgt]
    rw [basisBits_basisBitsEquiv_symm_eq, hin q]
    have hPoly {mP : ℕ} (c : Fin (2 ^ fullSysCoreWires mP)) :
        basisBits _ (xor32CorePerm mP c) = xor32BitFn mP (basisBits _ c) :=
      (basisBitsEquiv _).apply_symm_apply _
    rw [hPoly (rCoreFull.extractIndex y)]
    refine congrFun (congrArg (xor32BitFn 80) (funext fun i ↦ ?_)) q
    rw [rCoreFull.basisBits_extractIndex]
    dsimp only [y]; rw [basisBits_basisBitsEquiv_symm_eq]
  exact embedPermGen_mulVec_basisKet rCoreFull (xor32CorePerm 80) β (f β) hout hExtTgt
set_option exponentiation.threshold 8192 in
theorem uXor32Full_mul_self : uXor32Full * uXor32Full = 1 := by
  unfold uXor32Full
  rw [← rCoreFull.embedUnitary_mul]
  have h1 : uXor32Core 80 * uXor32Core 80 = 1 := by
    nth_rw 1 [← uXor32Core_inv 80]
    exact inv_mul_cancel _
  rw [h1, rCoreFull.embedUnitary_one]
theorem uXor32Full_comm_pSum42Zero : uXor32Full.1 * pSum42Zero = pSum42Zero * uXor32Full.1 := by
  unfold uXor32Full pSum42Zero
  rw [QRegister.embedUnitary_val]
  exact (QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint rCoreFull) rSum0
    (hAct0_disj_Sum0.compose_left rCoreOrig) _ 0
theorem E_stream42_eq_conj_E_rawStream42 :
    E_stream42 = uXor32Full.1 * E_rawStream42 * uXor32Full.1 := by
  unfold E_stream42 E_rawStream42
  rw [uStream42Init_def]
  simp only [Submonoid.coe_mul, Matrix.mul_assoc]
  rw [← uXor32Full_comm_pSum42Zero]
theorem uXor32Full_mul_E_stream42 : uXor32Full.1 * E_stream42 = E_rawStream42 * uXor32Full.1 := by
  rw [E_stream42_eq_conj_E_rawStream42, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    ← Submonoid.coe_mul, uXor32Full_mul_self, OneMemClass.coe_one, Matrix.one_mul]
theorem E_stream42_eq_streamProjOp : E_stream42 = streamProjOp (hoistStreamVec h3924_actOrig) := by
  apply matrix_ext_ket; intro β
  change E_stream42.mulVec (basisKet β) =
    (streamProjOp (hoistStreamVec h3924_actOrig)).mulVec (basisKet β)
  rw [E_stream42_eq_conj_E_rawStream42, E_rawStream42_eq_streamProjOp]
  simp only [← Matrix.mulVec_mulVec]
  rw [uXor32Full_mulVec_basisKet, streamProjOp_mulVec_basisKet, streamProjOp_mulVec_basisKet]
  let β' : BitAssignment kFull80 := fun g ↦ if g.val < 3924 ∧ g.val % 6 = 5 then β g + 1 else β g
  have hSumEq : rSum0.extractIndex ((basisBitsEquiv kFull80).symm β') =
      rSum0.extractIndex ((basisBitsEquiv kFull80).symm β) := by
    apply (basisBitsEquiv 42).injective; funext j
    change basisBits 42 (rSum0.extractIndex ((basisBitsEquiv kFull80).symm β')) j =
      basisBits 42 (rSum0.extractIndex ((basisBitsEquiv kFull80).symm β)) j
    rw [rSum0.basisBits_extractIndex, rSum0.basisBits_extractIndex,
      basisBits_basisBitsEquiv_symm_eq, basisBits_basisBitsEquiv_symm_eq]
    dsimp only [β']
    have hnot : ¬ (rSum0 j).val < 3924 := by
      rw [rSum0, qreg_block_apply]; dsimp [kActOrig, mActOrig, kActSingleCatClosure,
        SpecsAux.SpecMirror.systemQubits, SpecsAux.SpecMirror.numElectrons,
        SpecsAux.SpecMirror.electronBits, SpecsAux.SpecMirror.projectileBits]; omega
    simp [hnot]
  rw [hSumEq]
  by_cases h0 : rSum0.extractIndex ((basisBitsEquiv kFull80).symm β) = 0
  · rw [ite_eq_left h0, ite_eq_left h0, uXor32Full_mulVec_basisKet]
    refine congrArg basisKet ?_
    let y := (basisBitsEquiv kFull80).symm β
    let y' := (basisBitsEquiv kFull80).symm β'
    have hFeat : rawStreamVec h3924_actOrig (rAct0.extractIndex y') =
        hoistStreamVec h3924_actOrig (rAct0.extractIndex y) := by
      funext w
      dsimp only [rawStreamVec, hoistStreamVec, hoistStreamOfLow]
      refine congrFun (congrArg rawStreamOfLow (funext fun q ↦ ?_)) w
      dsimp only [low3924Bits]
      rw [rAct0.basisBits_extractIndex, rAct0.basisBits_extractIndex]
      dsimp only [y, y', β']
      rw [basisBits_basisBitsEquiv_symm_eq, basisBits_basisBitsEquiv_symm_eq]
      have hqVal : (rAct0 ⟨q.val, lt_of_lt_of_le q.isLt h3924_actOrig⟩).val = q.val := by
        simp [rAct0]
      simp [hqVal, q.isLt]
    rw [hFeat]
    funext g
    by_cases hg : g.val < kActOrig
    · dsimp only [joinActSum, y, y', β']
      simp only [basisBits_basisBitsEquiv_symm_eq, dite_eq_left hg, rAct0.basisBits_extractIndex]
      have hgVal : (rAct0 ⟨g.val, hg⟩).val = g.val := by simp [rAct0]
      simp only [hgVal]
      by_cases h39 : g.val < 3924 ∧ g.val % 6 = 5
      · simp [h39]
      · simp [h39]
    · have hnot39 : ¬ g.val < 3924 := by
        have : 3924 ≤ kActOrig := h3924_actOrig
        omega
      simp only [hnot39, false_and, ↓reduceIte]
      dsimp only [joinActSum]
      rw [basisBits_basisBitsEquiv_symm_eq, basisBits_basisBitsEquiv_symm_eq,
        dite_eq_right hg, dite_eq_right hg]
  · rw [ite_eq_right h0, ite_eq_right h0, Matrix.mulVec_zero]
def rPG45Full : QRegister 45 kFull80 := rPG48Full.slice 0 45 (by decide)
theorem hCoreFull_disj_PG45Full : rCoreFull.DisjointWires rPG45Full :=
  hCoreFull_disj_PG48Full.compose_right _
theorem hPSum45Full (w : Fin 3) : rPG45Full.DisjointWires (rSum14Full w) :=
  (hPSumFull w).compose_left _
theorem embedAct0_comm_pSum42Zero (A : Operator (2 ^ kActOrig)) :
    rAct0.embedMatrix A * pSum42Zero = pSum42Zero * rAct0.embedMatrix A :=
  (QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint rAct0) rSum0 hAct0_disj_Sum0 A 0
theorem embedSubAct0_comm_pSum42Zero {k : ℕ} (sub : QRegister k kActOrig) (U : Unitary (2 ^ k)) :
    ((rAct0.compose sub).embedUnitary U).1 * pSum42Zero =
      pSum42Zero * ((rAct0.compose sub).embedUnitary U).1 := by
  rw [QRegister.embedUnitary_val]
  exact (QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint (rAct0.compose sub)) rSum0
    (hAct0_disj_Sum0.compose_left sub) U.1 0
theorem rCTFull_eq_compose : rCTFull = rAct0.compose rCTOrig :=
  compose_concat_eq_singleCat rAct0 rCoreOrig rPG48Orig hCoreOrig_disj_PG48Orig
theorem rCTFull_embedUnitary_eq (U : Unitary (2 ^ (fullSysCoreWires 80 + 48))) :
    rCTFull.embedUnitary U = rAct0.embedUnitary (rCTOrig.embedUnitary U) := by
  rw [rCTFull_eq_compose, QRegister.embedUnitary_compose]
theorem rCTFull_comm_pSum42Zero (U : Unitary (2 ^ (fullSysCoreWires 80 + 48))) :
    (rCTFull.embedUnitary U).1 * pSum42Zero = pSum42Zero * (rCTFull.embedUnitary U).1 := by
  rw [rCTFull_eq_compose]
  exact embedSubAct0_comm_pSum42Zero rCTOrig U
theorem rCTFull_compose_rCoreBlock48 : rCTFull.compose (rCoreBlock48 80) = rCoreFull :=
    concat_compose_block_left rCoreFull rPG48Full hCoreFull_disj_PG48Full _
theorem embedAct0_comm_E_stream42 {U : Unitary (2 ^ kActOrig)}
    (hU : PreservesHoistStream42 h3924_actOrig U.1) :
    (rAct0.embedUnitary U).1 * E_stream42 = E_stream42 * (rAct0.embedUnitary U).1 := by
  rw [E_stream42_eq_streamProjOp, QRegister.embedUnitary_val]
  exact embedAct0_comm_streamOp hU
theorem embedAct0_comm_E_rawStream42 {U : Unitary (2 ^ kActOrig)}
    (hU : PreservesRawStream42 h3924_actOrig U.1) :
    (rAct0.embedUnitary U).1 * E_rawStream42 = E_rawStream42 * (rAct0.embedUnitary U).1 := by
  rw [E_rawStream42_eq_streamProjOp, QRegister.embedUnitary_val]
  exact embedAct0_comm_streamOp hU
noncomputable def applyPG45Add (Δ : BitAssignment (fullSysCoreWires 80) → ℕ)
    (δ : BitAssignment kFull80) : BitAssignment kFull80 := fun g ↦ if hg : g ∈ rPG45Full.image then
    let k45 := Classical.choose ((QRegister.mem_image rPG45Full g).mp hg)
    if ((regVal rPG45Full δ + Δ (fun q ↦ δ (rCoreFull q))) % 2 ^ 45).testBit k45.val
    then 1 else 0
  else δ g
theorem applyPG45Add_out (Δ : BitAssignment (fullSysCoreWires 80) → ℕ)
    (δ : BitAssignment kFull80) (g : Wire kFull80)
    (hg : g ∉ (rPG48Full.slice 0 45 (by decide)).image) : applyPG45Add Δ δ g = δ g := dite_eq_right
    hg
theorem applyPG45Add_regVal (Δ : BitAssignment (fullSysCoreWires 80) → ℕ)
    (δ : BitAssignment kFull80) : regVal (rPG48Full.slice 0 45 (by decide)) (applyPG45Add Δ δ) =
      (regVal (rPG48Full.slice 0 45 (by decide)) δ + Δ (fun q ↦ δ (rCoreFull q))) % 2 ^ 45 := by
  change bitsVal (fun i ↦ applyPG45Add Δ δ (rPG45Full i)) = _
  refine StepBBlock0.bitsVal_eq_of_testBit _ _
    (Nat.mod_lt _ (Nat.two_pow_pos 45)) (fun i ↦ ?_)
  have hmem : rPG45Full i ∈ rPG45Full.image := (QRegister.mem_image rPG45Full _).mpr ⟨i, rfl⟩
  dsimp only [applyPG45Add]
  rw [dite_eq_left hmem]
  have hch : Classical.choose ((QRegister.mem_image rPG45Full (rPG45Full i)).mp hmem) = i :=
    rPG45Full.wires.injective
      (Classical.choose_spec ((QRegister.mem_image rPG45Full (rPG45Full i)).mp hmem))
  rw [hch]; rfl
def zeroSum14 (w : Fin 3) (δ : BitAssignment kFull80) : BitAssignment kFull80 :=
  fun g ↦ if g ∈ (rSum14Full w).image then 0 else δ g
theorem core_applyPG45Add (Δ : BitAssignment (fullSysCoreWires 80) → ℕ)
    (δ : BitAssignment kFull80) :
    (fun q ↦ applyPG45Add Δ δ (rCoreFull q)) = (fun q ↦ δ (rCoreFull q)) :=
  funext fun q ↦ applyPG45Add_out Δ δ _ (fun hm ↦ by
    rcases (QRegister.mem_image _ _).mp hm with ⟨k, hk⟩
    exact hCoreFull_disj_PG45Full.ne q k hk.symm)
theorem sum14_applyPG45Add (w : Fin 3) (Δ : BitAssignment (fullSysCoreWires 80) → ℕ)
    (δ : BitAssignment kFull80) (i : Fin 14) :
    applyPG45Add Δ δ (rSum14Full w i) = δ (rSum14Full w i) := applyPG45Add_out Δ δ _ (fun hm ↦ by
    rcases (QRegister.mem_image _ _).mp hm with ⟨k, hk⟩
    exact (hPSum45Full w).ne k i hk)
theorem core_zeroSum14 (w : Fin 3) (δ : BitAssignment kFull80) :
    (fun q ↦ zeroSum14 w δ (rCoreFull q)) = (fun q ↦ δ (rCoreFull q)) :=
  funext fun q ↦ ite_eq_right (fun hm ↦ by
    rcases (QRegister.mem_image _ _).mp hm with ⟨k, hk⟩
    exact (hCoreFull_disj_Sum14 w).ne q k hk.symm)
theorem sum14_zeroSum14_ne {w w' : Fin 3} (hne : w ≠ w') (δ : BitAssignment kFull80)
    (i : Fin 14) : zeroSum14 w' δ (rSum14Full w i) = δ (rSum14Full w i) :=
  ite_eq_right (fun hm ↦ by
    rcases (QRegister.mem_image _ _).mp hm with ⟨k, hk⟩
    exact (hSum14In42_disj hne).ne i k (rSum0.wires.injective hk.symm))
theorem regVal_rPG45Full_zeroSum14 (w : Fin 3) (δ : BitAssignment kFull80) :
    regVal (rPG48Full.slice 0 45 (by decide)) (zeroSum14 w δ) =
      regVal (rPG48Full.slice 0 45 (by decide)) δ := by
  change bitsVal (fun i ↦ zeroSum14 w δ (rPG45Full i)) = bitsVal (fun i ↦ δ (rPG45Full i))
  refine congrArg bitsVal (funext fun i ↦ ?_)
  exact ite_eq_right (fun hm ↦ by
    rcases (QRegister.mem_image _ _).mp hm with ⟨k, hk⟩
    exact (hPSum45Full w).ne i k hk.symm)
theorem zeroSum14_applyPG45Add (w : Fin 3) (Δ : BitAssignment (fullSysCoreWires 80) → ℕ)
    (δ : BitAssignment kFull80) :
    zeroSum14 w (applyPG45Add Δ δ) = applyPG45Add Δ (zeroSum14 w δ) := by
  have hCore := core_zeroSum14 w δ
  have hPG : regVal rPG45Full (zeroSum14 w δ) = regVal rPG45Full δ :=
    regVal_rPG45Full_zeroSum14 w δ
  funext g
  by_cases hgS : g ∈ (rSum14Full w).image
  · have hgP : g ∉ rPG45Full.image := fun hmP ↦ by
      rcases (QRegister.mem_image _ _).mp hgS with ⟨i, rfl⟩
      rcases (QRegister.mem_image _ _).mp hmP with ⟨k, hk⟩
      exact (hPSum45Full w).ne k i hk
    dsimp only [zeroSum14, applyPG45Add]
    rw [ite_eq_left hgS, dite_eq_right hgP, ite_eq_left hgS]
  · dsimp only [zeroSum14]
    rw [ite_eq_right hgS]
    dsimp only [applyPG45Add]
    by_cases hgP : g ∈ rPG45Full.image
    · rw [dite_eq_left hgP, dite_eq_left hgP, hPG, hCore]
    · rw [dite_eq_right hgP, dite_eq_right hgP]; dsimp only [zeroSum14]; rw [ite_eq_right hgS]
theorem proj_absorb_comm_lemma {D : ℕ} (W1 W0 Psym Panc Psum : Operator D)
    (hEq : W1 * Psum = W0 * Psum) (hAbs : Psum * Panc = Panc)
    (hComm : Psym * Psum = Psum * Psym) : W1 * (Psym * Panc) = W0 * (Psym * Panc) := by
  have hL (W : Operator D) : W * (Psym * Panc) = (W * Psum) * (Psym * Panc) := by
    nth_rw 1 [← hAbs]
    simp only [← Matrix.mul_assoc, hComm]
  rw [hL W1, hEq, ← hL W0]
theorem embedAct0_fixesLow3924_comm_E_stream42 {U : Unitary (2 ^ kActOrig)}
    (hU : FixesLow3924 h3924_actOrig U.1) :
    (rAct0.embedUnitary U).1 * E_stream42 = E_stream42 * (rAct0.embedUnitary U).1 :=
  embedAct0_comm_E_stream42 hU.preservesHoistStream42
end ConfigInterWalkRSum42Hoist
end InterWalkRSum42Hoist
end
end ModInterWalkRSum42Hoist
section ModGidneySignalRotPart1
@[expose] public section
namespace GidneySignalRotPart1
open Operator Matrix Circuit _root_.DynamicCircuit DynCircuitExt QProg HermitianMat
open scoped Matrix ComplexOrder MatrixOrder Circuit.Notation Matrix.Norms.L2Operator BigOperators
open SpecsAux.SpecMirror
open SpecsAux.FullScaleBESector hiding phaseGradientState
open SpecsAux.PhaseGradCatalystCore
open PhaseGradSignalRot hiding IntertwinesCat
open TFreeLaurentGQSP CatalyzedLaurentGQSP
open BidirectionalCatalyzedGQSP
open BidirectionalCatalyzedGQSPBridge
open TwosCompAndWire0Cancel
open FullSysCatSegmentBridge
open SingleCatSpine
open SingleCatClosure
def gidneyRotToffEquiv (c : ℕ) : ℕ := 2 * (activeMsbWidth42 c - 2)
theorem trailingZeros42Aux_eq_fuel_iff :
    ∀ (fuel c : ℕ), c < 2 ^ fuel → (trailingZeros42Aux fuel c = fuel ↔ c = 0)
  | 0, c, hlt => by
      simp [trailingZeros42Aux]
      omega
  | fuel + 1, c, hlt => by
      unfold trailingZeros42Aux
      by_cases hc : c = 0
      · simp [hc]
      · simp only [hc, ↓reduceIte, iff_false]
        split_ifs with hmod
        · intro heq
          have hlt2 : c / 2 < 2 ^ fuel :=
            (Nat.div_lt_iff_lt_mul (by decide : 0 < 2)).mpr (by rwa [Nat.pow_succ] at hlt)
          have h0 := (trailingZeros42Aux_eq_fuel_iff fuel (c / 2) hlt2).mp (by omega)
          omega
        · exact not_false
theorem activeMsbWidth42_eq_zero_iff {c : ℕ} (hlt : c < 2 ^ 42) :
    activeMsbWidth42 c = 0 ↔ c = 0 := by
  unfold activeMsbWidth42 trailingZeros42
  have hle := trailingZeros42Aux_le 42 c
  have hiff := trailingZeros42Aux_eq_fuel_iff 42 c hlt
  omega
theorem odd_div_two_pow_trailingZeros42Aux :
    ∀ (fuel c : ℕ), c ≠ 0 → c < 2 ^ fuel → (c / 2 ^ trailingZeros42Aux fuel c) % 2 = 1
  | 0, c, hc, hlt => by simp at hlt; omega
  | fuel + 1, c, hc, hlt => by
      unfold trailingZeros42Aux
      simp only [hc, ↓reduceIte]
      split_ifs with hmod
      · have hc2_ne : c / 2 ≠ 0 := by omega
        have hc2_lt : c / 2 < 2 ^ fuel :=
          (Nat.div_lt_iff_lt_mul (by decide : 0 < 2)).mpr (by rwa [Nat.pow_succ] at hlt)
        have heq : c = 2 * (c / 2) := by omega
        have hdiv : c / 2 ^ (1 + trailingZeros42Aux fuel (c / 2)) =
            (c / 2) / 2 ^ trailingZeros42Aux fuel (c / 2) := by
          nth_rw 1 [heq]
          rw [Nat.pow_add, pow_one]
          exact Nat.mul_div_mul_left (c / 2) _ (by decide : 0 < 2)
        rw [hdiv]
        exact odd_div_two_pow_trailingZeros42Aux fuel (c / 2) hc2_ne hc2_lt
      · simp
        omega
theorem odd_div_two_pow_trailingZeros42 {c : ℕ} (hc : c ≠ 0) (hlt : c < 2 ^ 42) :
    (c / 2 ^ trailingZeros42 c) % 2 = 1 := odd_div_two_pow_trailingZeros42Aux 42 c hc hlt
section GidneyConstAux
variable {Var : Type} {n : ℕ}
def bitZ (b : Bool) : ZMod 2 := if b then 1 else 0
def optXWire (b : Bool) (w : Wire n) : Circuit n := if b then Circuit.X w else Circuit.identity
@[simp] theorem count_optXWire_toff (b : Bool) (w : Wire n) : (optXWire b w).count .TOFF = 0 := by
  cases b <;> rfl
@[simp] theorem count_optXWire_t (b : Bool) (w : Wire n) : (optXWire b w).count .T = 0 := by
  cases b <;> rfl
theorem support_optXWire_subset (b : Bool) (w : Wire n) : (optXWire b w).support ⊆ {w} := by
  cases b
  · simp [optXWire]
  · intro q hq
    simp only [optXWire, ↓reduceIte, Circuit.X, Circuit.single, Circuit.support_gate] at hq
    rcases (QRegister.mem_image _ q).mp hq with ⟨i, rfl⟩
    fin_cases i
    simp [QRegister.singleton]
theorem classicalPerm_optXWire (b : Bool) (w : Wire n) :
    ClassicalPerm (optXWire b w) (fun β ↦ Function.update β w (β w + bitZ b)) := by
  cases b
  · have hid : (fun β : BitAssignment n ↦ Function.update β w (β w + bitZ false)) = id := by
      funext β u
      by_cases hu : u = w
      · subst hu; simp [bitZ]
      · simp [Function.update_of_ne hu]
    dsimp only [optXWire]
    rw [hid]
    exact ClassicalPerm.identity
  · intro β
    simpa [optXWire, bitZ] using evolve_X_basisKet w β
def gidneyConstStep (b : Bool) (c_in t₀ c₀ : Wire n)
    (hcin_t : c_in ≠ t₀) (hcin_c : c_in ≠ c₀) (htc : t₀ ≠ c₀) : TempAndStep n where
  pre := optXWire b c_in ;;ᶜ optXWire b t₀
  c₁ := c_in
  c₂ := t₀
  anc := c₀
  h₁₂ := hcin_t
  h₁a := hcin_c
  h₂a := htc
  midPre := optXWire b c_in ;;ᶜ optXWire b c₀
  midPost := optXWire b c₀ ;;ᶜ optXWire b c_in
  post := optXWire b c_in ;;ᶜ Circuit.CNOT c_in t₀ hcin_t
theorem gidneyConstStep_isClifford (b : Bool) (c_in t₀ c₀ : Wire n)
    (hcin_t : c_in ≠ t₀) (hcin_c : c_in ≠ c₀) (htc : t₀ ≠ c₀) :
    (gidneyConstStep b c_in t₀ c₀ hcin_t hcin_c htc).IsCliffordWrapper := by
  simp [gidneyConstStep, TempAndStep.IsCliffordWrapper]
theorem zmod2_const_adder_val (b : Bool) (t cin : ZMod 2) : (t + bitZ b + cin).val + 2 *
    ((cin + bitZ b) * (t + bitZ b) + bitZ b).val = t.val + (bitZ b).val + cin.val := by
  revert b t cin; decide
def gidneyConstAuxCircuit : (k : ℕ) → (bits : Fin (k + 1) → Bool) → (rT : QRegister (k + 1) n) →
    (rC : QRegister k n) → (c_in : Wire n) → (hdisj_TC : rT.DisjointWires rC) →
    (hcin_T : c_in ∉ rT.image) → (hcin_C : c_in ∉ rC.image) → Circuit n
  | 0, bits, rT, _, c_in, _, hcin_T, _ =>
      have hcin_t0 : c_in ≠ rT 0 := QRegister.ne_apply_of_not_mem_image rT c_in hcin_T 0
      Circuit.CNOT c_in (rT 0) hcin_t0 ;;ᶜ optXWire (bits 0) (rT 0)
  | k + 1, bits, rT, rC, c_in, hdisj_TC, hcin_T, hcin_C =>
      let rT_rest := rT.slice 1 (k + 1) (by omega)
      let rC_rest := rC.slice 1 k (by omega)
      have htc : rT 0 ≠ rC 0 := hdisj_TC.ne 0 0
      have hcin_t : c_in ≠ rT 0 := QRegister.ne_apply_of_not_mem_image rT _ hcin_T 0
      have hcin_c : c_in ≠ rC 0 := QRegister.ne_apply_of_not_mem_image rC _ hcin_C 0
      have hdisj_TC_rest : rT_rest.DisjointWires rC_rest :=
        (hdisj_TC.compose_left _).compose_right _
      have hc0_T_rest : rC 0 ∉ rT_rest.image :=
        fun hj ↦ hdisj_TC.apply_not_mem_left 0 (QRegister.image_compose_subset rT _ hj)
      have hc0_C_rest : rC 0 ∉ rC_rest.image := QRegExt.head_not_mem_tail_image rC
      (gidneyConstStep (bits 0) c_in (rT 0) (rC 0) hcin_t hcin_c htc).wrapCircuit
        (gidneyConstAuxCircuit k (fun j ↦ bits j.succ) rT_rest rC_rest (rC 0)
          hdisj_TC_rest hc0_T_rest hc0_C_rest)
def gidneyConstAuxDyn (v : Var) :
    (k : ℕ) → (bits : Fin (k + 1) → Bool) → (rT : QRegister (k + 1) n) →
    (rC : QRegister k n) → (c_in : Wire n) → (hdisj_TC : rT.DisjointWires rC) →
    (hcin_T : c_in ∉ rT.image) → (hcin_C : c_in ∉ rC.image) → DynamicCircuit Var n
  | 0, bits, rT, _, c_in, _, hcin_T, _ =>
      have hcin_t0 : c_in ≠ rT 0 := QRegister.ne_apply_of_not_mem_image rT c_in hcin_T 0
      .circuit (Circuit.CNOT c_in (rT 0) hcin_t0 ;;ᶜ optXWire (bits 0) (rT 0))
  | k + 1, bits, rT, rC, c_in, hdisj_TC, hcin_T, hcin_C =>
      let rT_rest := rT.slice 1 (k + 1) (by omega)
      let rC_rest := rC.slice 1 k (by omega)
      have htc : rT 0 ≠ rC 0 := hdisj_TC.ne 0 0
      have hcin_t : c_in ≠ rT 0 := QRegister.ne_apply_of_not_mem_image rT _ hcin_T 0
      have hcin_c : c_in ≠ rC 0 := QRegister.ne_apply_of_not_mem_image rC _ hcin_C 0
      have hdisj_TC_rest : rT_rest.DisjointWires rC_rest :=
        (hdisj_TC.compose_left _).compose_right _
      have hc0_T_rest : rC 0 ∉ rT_rest.image :=
        fun hj ↦ hdisj_TC.apply_not_mem_left 0 (QRegister.image_compose_subset rT _ hj)
      have hc0_C_rest : rC 0 ∉ rC_rest.image := QRegExt.head_not_mem_tail_image rC
      (gidneyConstStep (bits 0) c_in (rT 0) (rC 0) hcin_t hcin_c htc).wrapDynamic v
        (gidneyConstAuxDyn v k (fun j ↦ bits j.succ) rT_rest rC_rest (rC 0)
          hdisj_TC_rest hc0_T_rest hc0_C_rest)
@[simp] theorem count_gidneyConstAuxDyn_toff (v : Var) (k : ℕ)
    (bits : Fin (k + 1) → Bool) (rT : QRegister (k + 1) n) (rC : QRegister k n) (c_in : Wire n)
    (hdisj_TC : rT.DisjointWires rC) (hcin_T : c_in ∉ rT.image) (hcin_C : c_in ∉ rC.image) :
    (gidneyConstAuxDyn v k bits rT rC c_in hdisj_TC hcin_T hcin_C).count .TOFF = 0 := by
  induction k generalizing c_in with
  | zero => simp [gidneyConstAuxDyn]
  | succ k ih =>
      rw [gidneyConstAuxDyn,
        TempAndStep.count_wrapDynamic_toff _ _ _ (gidneyConstStep_isClifford ..)]
      exact ih ..
@[simp] theorem count_gidneyConstAuxDyn_t (v : Var) (k : ℕ)
    (bits : Fin (k + 1) → Bool) (rT : QRegister (k + 1) n) (rC : QRegister k n) (c_in : Wire n)
    (hdisj_TC : rT.DisjointWires rC) (hcin_T : c_in ∉ rT.image) (hcin_C : c_in ∉ rC.image) :
    (gidneyConstAuxDyn v k bits rT rC c_in hdisj_TC hcin_T hcin_C).count .T = 4 * k := by
  induction k generalizing c_in with
  | zero => simp [gidneyConstAuxDyn]
  | succ k ih =>
      rw [gidneyConstAuxDyn,
        TempAndStep.count_wrapDynamic_t _ _ _ (gidneyConstStep_isClifford ..), ih]
      omega
theorem storeConst_gidneyConstAuxDyn [Fintype Var] [DecidableEq Var] [NeZero (2 ^ n)] (v : Var) :
    ∀ (k : ℕ) (bits : Fin (k + 1) → Bool)
      (rT : QRegister (k + 1) n) (rC : QRegister k n) (c_in : Wire n)
      (hdisj_TC : rT.DisjointWires rC) (hcin_T : c_in ∉ rT.image) (hcin_C : c_in ∉ rC.image),
      StoreConst (gidneyConstAuxDyn v k bits rT rC c_in hdisj_TC hcin_T hcin_C)
  | 0, _, _, _, _, _, _, _ => StoreConst.circuit _
  | k + 1, _, _, _, _, _, _, _ =>
      StoreConst.wrapDynamic v _ (storeConst_gidneyConstAuxDyn v k _ _ _ _ _ _ _)
theorem gidneyConstAux_correct [Fintype Var] [DecidableEq Var] [NeZero (2 ^ n)] (v : Var)
    (k : ℕ) (bits : Fin (k + 1) → Bool) (rT : QRegister (k + 1) n) (rC : QRegister k n)
    (c_in : Wire n) (hdisj_TC : rT.DisjointWires rC) (hcin_T : c_in ∉ rT.image)
    (hcin_C : c_in ∉ rC.image) : ∃ f : BitAssignment n → BitAssignment n, ClassicalPerm
    (gidneyConstAuxCircuit k bits rT rC c_in hdisj_TC hcin_T hcin_C) f ∧
    (∀ β w, w ∉ rT.image → f β w = β w) ∧ (∀ β, (∀ i : Fin k, β (rC i) = 0) → regVal rT (f β)
    = (regVal rT β + bitsVal (fun j ↦ bitZ (bits j)) + (β c_in).val) % 2 ^ (k + 1)) ∧ (∀ Θ :
    CQAssertionCompat Var (2 ^ n), (∀ σ val, Θ (Function.update σ v val) = Θ σ) →
    CQAssertion.restrictToZeroAncilla (wp (gidneyConstAuxDyn v k bits rT rC c_in hdisj_TC hcin_T
    hcin_C).compile Θ) rC = CQAssertion.restrictToZeroAncilla (wpQAssignCompat
    (gidneyConstAuxCircuit k bits rT rC c_in hdisj_TC hcin_T hcin_C).eval Θ) rC) := by
  induction k generalizing c_in with
  | zero =>
      have hcin_t0 : c_in ≠ rT 0 := QRegister.ne_apply_of_not_mem_image rT c_in hcin_T 0
      let f : BitAssignment n → BitAssignment n :=
        fun β ↦ Function.update β (rT 0) (β (rT 0) + β c_in + bitZ (bits 0))
      refine ⟨f, ?_, ?_, ?_, ?_⟩
      · have hseq := (ClassicalPerm.CNOT c_in (rT 0) hcin_t0).seq
          (classicalPerm_optXWire (bits 0) (rT 0))
        intro β
        dsimp only [gidneyConstAuxCircuit]
        rw [hseq β]
        congr 1; funext w
        by_cases hwt : w = rT 0
        · subst hwt; simp [f]
        · simp [f, Function.update_of_ne hwt]
      · intro β w hw
        have hwt : w ≠ rT 0 := QRegister.ne_apply_of_not_mem_image rT w hw 0
        exact Function.update_of_ne hwt _ _
      · intro β _
        rw [regVal_head_tail, regVal_head_tail]
        have h0_slice : ∀ γ, regVal (rT.slice 1 0 (by omega)) γ = 0 := by
          intro γ; simp [regVal, bitsVal]
        rw [h0_slice, h0_slice]
        dsimp only [f, bitsVal]
        rw [Fin.sum_univ_one]
        simp only [Function.update_self, Fin.val_zero, _root_.pow_zero, mul_zero, add_zero]
        have hmod : ∀ a b c : ZMod 2, (a + c + b).val = (a.val + b.val * 1 + c.val) % 2 := by
          decide
        exact hmod (β (rT 0)) (bitZ (bits 0)) (β c_in)
      · intro Θ _
        rw [gidneyConstAuxDyn, gidneyConstAuxCircuit, DynamicCircuit.compile_circuit,
          DynCircuitExt.wp_circuit_compile_compat]
  | succ k ih =>
      let b0 := bits 0
      let rT_rest := rT.slice 1 (k + 1) (by omega)
      let rC_rest := rC.slice 1 k (by omega)
      have htc : rT 0 ≠ rC 0 := hdisj_TC.ne 0 0
      have hcin_t : c_in ≠ rT 0 := QRegister.ne_apply_of_not_mem_image rT _ hcin_T 0
      have hcin_c : c_in ≠ rC 0 := QRegister.ne_apply_of_not_mem_image rC _ hcin_C 0
      have hdisj_TC_rest : rT_rest.DisjointWires rC_rest :=
        (hdisj_TC.compose_left _).compose_right _
      have hc0_T_rest : rC 0 ∉ rT_rest.image :=
        fun hj ↦ hdisj_TC.apply_not_mem_left 0 (QRegister.image_compose_subset rT _ hj)
      have hc0_C_rest : rC 0 ∉ rC_rest.image := QRegExt.head_not_mem_tail_image rC
      have ht0_T_rest : rT 0 ∉ rT_rest.image := QRegExt.head_not_mem_tail_image rT
      have hcin_T_rest : c_in ∉ rT_rest.image :=
        fun hj ↦ hcin_T (QRegister.image_compose_subset rT _ hj)
      obtain ⟨f_rest, hperm_rest, hout_rest, hval_rest, hwp_rest⟩ := ih (fun j ↦ bits j.succ)
          rT_rest rC_rest (rC 0) hdisj_TC_rest hc0_T_rest hc0_C_rest
      let s_step := gidneyConstStep b0 c_in (rT 0) (rC 0) hcin_t hcin_c htc
      let c_inner := gidneyConstAuxCircuit k (fun j ↦ bits j.succ) rT_rest rC_rest (rC 0)
        hdisj_TC_rest hc0_T_rest hc0_C_rest
      let d_inner := gidneyConstAuxDyn v k (fun j ↦ bits j.succ) rT_rest rC_rest (rC 0)
        hdisj_TC_rest hc0_T_rest hc0_C_rest
      let f_pre := fun β : BitAssignment n ↦ Function.update
          (Function.update β c_in (β c_in + bitZ b0)) (rT 0) (β (rT 0) + bitZ b0)
      let f_midPre := fun β : BitAssignment n ↦ Function.update
          (Function.update β c_in (β c_in + bitZ b0)) (rC 0) (β (rC 0) + bitZ b0)
      let f_midPost := fun β : BitAssignment n ↦ Function.update
          (Function.update β (rC 0) (β (rC 0) + bitZ b0)) c_in (β c_in + bitZ b0)
      let f_post := fun β : BitAssignment n ↦ let β' := Function.update β c_in (β c_in + bitZ b0)
        Function.update β' (rT 0) (β' (rT 0) + β' c_in)
      have hOpt2 {u w0 : Wire n} (hne : u ≠ w0) : ClassicalPerm (optXWire b0 u ;;ᶜ optXWire b0 w0)
          (fun β ↦ Function.update (Function.update β u (β u + bitZ b0)) w0 (β w0 + bitZ b0)) := by
        intro β
        rw [((classicalPerm_optXWire b0 u).seq (classicalPerm_optXWire b0 w0)) β]
        refine congrArg ket (funext fun w ↦ ?_)
        by_cases hw : w = w0
        · subst hw
          simp [Function.update_of_ne hne.symm]
        · simp [Function.update_of_ne hw]
      have hpre_perm : ClassicalPerm s_step.pre f_pre := hOpt2 hcin_t
      have hmidPre_perm : ClassicalPerm s_step.midPre f_midPre := hOpt2 hcin_c
      have hmidPost_perm : ClassicalPerm s_step.midPost f_midPost := hOpt2 hcin_c.symm
      have hpost_perm : ClassicalPerm s_step.post f_post :=
        (classicalPerm_optXWire b0 c_in).seq (ClassicalPerm.CNOT c_in (rT 0) hcin_t)
      let f_body := f_midPost ∘ f_rest ∘ f_midPre
      have hbody_perm : ClassicalPerm (s_step.midPre ;;ᶜ c_inner ;;ᶜ s_step.midPost) f_body :=
        hmidPre_perm.seq (hperm_rest.seq hmidPost_perm)
      have hbody_cin : ∀ β, f_body β c_in = β c_in := by
        intro β
        dsimp only [f_body, f_midPost, f_midPre, Function.comp_apply]
        simp only [Function.update_self, Function.update_of_ne hcin_c,
          hout_rest _ c_in hcin_T_rest, LocalClassicalPerm.zmod2_add_cancel_right]
      have hbody_t0 : ∀ β, f_body β (rT 0) = β (rT 0) := by
        intro β
        dsimp only [f_body, f_midPost, f_midPre, Function.comp_apply]
        simp only [Function.update_of_ne hcin_t.symm, Function.update_of_ne htc,
          hout_rest _ (rT 0) ht0_T_rest]
      have hbody_c0 : ∀ β, f_body β (rC 0) = β (rC 0) := by
        intro β
        dsimp only [f_body, f_midPost, f_midPre, Function.comp_apply]
        simp only [Function.update_of_ne hcin_c.symm, Function.update_self,
          hout_rest _ (rC 0) hc0_T_rest, LocalClassicalPerm.zmod2_add_cancel_right]
      have hc_body := toffoli_conj_preserves_zero_ancilla_of_classicalPerm
        c_in (rT 0) (rC 0) hcin_t hcin_c htc (s_step.midPre ;;ᶜ c_inner ;;ᶜ s_step.midPost)
        f_body hbody_perm hbody_cin hbody_t0 hbody_c0
      let f_toff := fun β : BitAssignment n ↦
        Function.update β (rC 0) (β (rC 0) + β c_in * β (rT 0))
      let f_total := f_post ∘ f_toff ∘ f_body ∘ f_toff ∘ f_pre
      have htotal_perm : ClassicalPerm
          (gidneyConstAuxCircuit (k + 1) bits rT rC c_in hdisj_TC hcin_T hcin_C) f_total := by
        have htoff_p := ClassicalPerm.TOFF c_in (rT 0) (rC 0) hcin_t hcin_c htc
        have hseq := hpre_perm.seq (htoff_p.seq (hbody_perm.seq (htoff_p.seq hpost_perm)))
        intro β
        rw [gidneyConstAuxCircuit, show s_step.wrapCircuit c_inner =
            s_step.pre ;;ᶜ (Circuit.TOFF c_in (rT 0) (rC 0) hcin_t hcin_c htc ;;ᶜ
              ((s_step.midPre ;;ᶜ c_inner ;;ᶜ s_step.midPost) ;;ᶜ
                (Circuit.TOFF c_in (rT 0) (rC 0) hcin_t hcin_c htc ;;ᶜ s_step.post))) by
          simp [s_step, gidneyConstStep, TempAndStep.wrapCircuit]]
        exact hseq β
      refine ⟨f_total, htotal_perm, ?_, ?_, ?_⟩
      · intro β w hw
        have hwt0 : w ≠ rT 0 := QRegister.ne_apply_of_not_mem_image rT w hw 0
        have hw_rest : w ∉ rT_rest.image := fun hj ↦ hw (QRegister.image_compose_subset rT _ hj)
        let β₂ := f_toff (f_pre β)
        change f_post (f_toff (f_body β₂)) w = β w
        by_cases hwcin : w = c_in
        · subst hwcin
          dsimp only [f_post, f_toff]
          simp only [Function.update_of_ne hcin_t, Function.update_self,
            Function.update_of_ne hcin_c, hbody_cin β₂]
          dsimp only [β₂, f_toff, f_pre]
          simp only [Function.update_of_ne hcin_c, Function.update_of_ne hcin_t,
            Function.update_self, LocalClassicalPerm.zmod2_add_cancel_right]
        · by_cases hwc : w = rC 0
          · subst hwc
            dsimp only [f_post, f_toff]
            simp only [Function.update_of_ne htc.symm, Function.update_of_ne hcin_c.symm,
              Function.update_self, hbody_c0 β₂, hbody_cin β₂, hbody_t0 β₂]
            dsimp only [β₂, f_toff]
            simp only [Function.update_self, Function.update_of_ne hcin_c,
              Function.update_of_ne htc, LocalClassicalPerm.zmod2_add_cancel_right]
            dsimp only [f_pre]
            simp only [Function.update_of_ne htc.symm, Function.update_of_ne hcin_c.symm]
          · dsimp only [f_post, f_toff]
            simp only [Function.update_of_ne hwt0, Function.update_of_ne hwcin,
              Function.update_of_ne hwc]
            dsimp only [f_body, f_midPost, f_midPre, Function.comp_apply]
            simp only [Function.update_of_ne hwcin, Function.update_of_ne hwc,
              hout_rest _ w hw_rest]
            dsimp only [β₂, f_toff, f_pre]
            simp [Function.update_of_ne hwc, Function.update_of_ne hwt0,
              Function.update_of_ne hwcin]
      · intro β hβ_C
        have hβ_c0 : β (rC 0) = 0 := hβ_C 0
        let β_mid := f_midPre (f_toff (f_pre β))
        have hβ_mid_c0 : β_mid (rC 0) = (β c_in + bitZ b0) * (β (rT 0) + bitZ b0) + bitZ b0 := by
          dsimp only [β_mid, f_midPre, f_toff, f_pre]
          simp [Function.update_of_ne hcin_c.symm, Function.update_of_ne htc.symm,
            Function.update_of_ne hcin_c, Function.update_of_ne hcin_t, hβ_c0]
        have hT_ne (i : Fin (k + 1)) :
            rT_rest i ≠ c_in ∧ rT_rest i ≠ rT 0 ∧ rT_rest i ≠ rC 0 := by
          have hi_mem : rT_rest i ∈ rT_rest.image := (QRegister.mem_image rT_rest _).mpr ⟨i, rfl⟩
          exact ⟨fun h ↦ hcin_T_rest (h ▸ hi_mem), fun h ↦ ht0_T_rest (h ▸ hi_mem),
            fun h ↦ hc0_T_rest (h ▸ hi_mem)⟩
        have hβ_mid_T_rest (i : Fin (k + 1)) : β_mid (rT_rest i) = β (rT_rest i) := by
          rcases hT_ne i with ⟨hi_cin, hi_t0, hi_c0⟩
          dsimp only [β_mid, f_midPre, f_toff, f_pre]
          simp [Function.update_of_ne hi_c0, Function.update_of_ne hi_cin,
            Function.update_of_ne hi_t0]
        have hβ_mid_C_rest (i : Fin k) : β_mid (rC_rest i) = 0 := by
          have hi_mem : rC_rest i ∈ rC_rest.image := (QRegister.mem_image rC_rest _).mpr ⟨i, rfl⟩
          have hi_cin : rC_rest i ≠ c_in :=
            fun h ↦ hcin_C (QRegister.image_compose_subset rC _ (h ▸ hi_mem))
          have hi_t0 : rC_rest i ≠ rT 0 := fun h ↦ hdisj_TC.apply_not_mem_right 0
              (QRegister.image_compose_subset rC _ (h ▸ hi_mem))
          have hi_c0 : rC_rest i ≠ rC 0 := fun h ↦ hc0_C_rest (h ▸ hi_mem)
          dsimp only [β_mid, f_midPre, f_toff, f_pre]
          simp only [Function.update_of_ne hi_c0, Function.update_of_ne hi_cin,
            Function.update_of_ne hi_t0]
          exact hβ_C ⟨1 + i.val, by omega⟩
        have htotal_t0 : f_total β (rT 0) = β (rT 0) + bitZ b0 + β c_in := by
          let β₂ := f_toff (f_pre β)
          change f_post (f_toff (f_body β₂)) (rT 0) = _
          dsimp only [f_post, f_toff]
          simp only [Function.update_self, Function.update_of_ne hcin_t.symm,
            Function.update_of_ne htc, Function.update_of_ne hcin_c, hbody_t0 β₂, hbody_cin β₂]
          dsimp only [β₂, f_toff, f_pre]
          simp only [Function.update_of_ne htc, Function.update_of_ne hcin_c,
            Function.update_of_ne hcin_t, Function.update_self,
            LocalClassicalPerm.zmod2_add_cancel_right]
        have htotal_T_rest (i : Fin (k + 1)) :
            f_total β (rT_rest i) = f_rest β_mid (rT_rest i) := by
          rcases hT_ne i with ⟨hi_cin, hi_t0, hi_c0⟩
          dsimp only [f_total, f_post, f_toff, f_body, f_midPost, Function.comp_apply, β_mid]
          simp [Function.update_of_ne hi_t0, Function.update_of_ne hi_cin,
            Function.update_of_ne hi_c0]
        rw [regVal_head_tail rT (f_total β), regVal_congr rT_rest htotal_T_rest,
          hval_rest β_mid hβ_mid_C_rest, regVal_congr rT_rest hβ_mid_T_rest, htotal_t0, hβ_mid_c0]
        have hbits_split : bitsVal (fun j : Fin (k + 2) ↦ bitZ (bits j)) =
            (bitZ b0).val + 2 * bitsVal (fun j : Fin (k + 1) ↦ bitZ (bits j.succ)) := by
          unfold bitsVal
          rw [Fin.sum_univ_succ, Finset.mul_sum]
          simp only [Fin.val_zero, _root_.pow_zero, mul_one, b0]
          congr 1
          refine Finset.sum_congr rfl fun j _ ↦ ?_
          rw [Fin.val_succ, pow_succ]
          ring
        rw [regVal_head_tail rT β, hbits_split]
        have hfull := zmod2_const_adder_val b0 (β (rT 0)) (β c_in)
        let X := regVal rT_rest β + bitsVal (fun j : Fin (k + 1) ↦ bitZ (bits j.succ)) +
          ((β c_in + bitZ b0) * (β (rT 0) + bitZ b0) + bitZ b0).val
        rw [add_two_mul_mod _ X (2 ^ (k + 1)) (ZMod.val_lt _), ← pow_succ']
        congr 1
        dsimp only [X]
        linarith [hfull]
      · intro Θ hΘ
        rw [gidneyConstAuxDyn, gidneyConstAuxCircuit]
        have hcin_Cr : c_in ∉ rC_rest.image :=
          fun hj ↦ hcin_C (QRegister.image_compose_subset rC _ hj)
        have ht0_Cr : rT 0 ∉ rC_rest.image :=
          fun hj ↦ hdisj_TC.apply_not_mem_right 0 (QRegister.image_compose_subset rC _ hj)
        have hpre_sub : s_step.pre.support ⊆ {c_in, rT 0} := by
          dsimp only [s_step, gidneyConstStep]
          exact Circuit.support_seq _ _ ▸ Finset.union_subset
            ((support_optXWire_subset b0 c_in).trans (Finset.singleton_subset_iff.mpr (by simp)))
            ((support_optXWire_subset b0 (rT 0)).trans (Finset.singleton_subset_iff.mpr (by simp)))
        have hpre_anc : rC 0 ∉ s_step.pre.support := fun hm ↦ by
          rcases Finset.mem_insert.mp (hpre_sub hm) with h | h
          · exact hcin_c h.symm
          · exact htc (Finset.mem_singleton.mp h).symm
        have hpre_rest : Disjoint s_step.pre.support rC_rest.image :=
          Finset.disjoint_of_subset_left hpre_sub (by simp [hcin_Cr, ht0_Cr])
        have hmidPre_sub : s_step.midPre.support ⊆ {c_in, rC 0} := by
          dsimp only [s_step, gidneyConstStep]
          exact Circuit.support_seq _ _ ▸ Finset.union_subset
            ((support_optXWire_subset b0 c_in).trans (Finset.singleton_subset_iff.mpr (by simp)))
            ((support_optXWire_subset b0 (rC 0)).trans (Finset.singleton_subset_iff.mpr (by simp)))
        have hmidPre_rest : Disjoint s_step.midPre.support rC_rest.image := by
          refine Finset.disjoint_of_subset_left hmidPre_sub ?_
          simp [Finset.disjoint_insert_left, Finset.disjoint_singleton_left, hcin_Cr, hc0_C_rest]
        exact TempAndStep.restrictToZeroAncilla_wp_wrapDynamic_head_tail
          v s_step d_inner c_inner rC rfl hpre_anc hpre_rest hcin_Cr ht0_Cr hmidPre_rest
          hc_body hwp_rest Θ hΘ
end GidneyConstAux
def kickFun43 (θ₀ θ₁ : ℕ) (u : Fin (2 ^ (1 + 42))) : Fin (2 ^ (1 + 42)) :=
  ⟨u.val % 2 + 2 * ((u.val / 2 + (if u.val % 2 = 0 then θ₀ else θ₁)) % 2 ^ 42), by
    have h1 : u.val % 2 < 2 := Nat.mod_lt _ (by decide)
    have h2 : (u.val / 2 + (if u.val % 2 = 0 then θ₀ else θ₁)) % 2 ^ 42 < 2 ^ 42 :=
      Nat.mod_lt _ (by decide)
    have hpow : 2 ^ (1 + 42) = 2 * 2 ^ 42 := by decide
    omega⟩
theorem kickFun43_comp_id {θ₀ θ₁ : ℕ} (hsum : θ₀ + θ₁ = 2 ^ 42) (u : Fin (2 ^ (1 + 42))) :
    kickFun43 θ₁ θ₀ (kickFun43 θ₀ θ₁ u) = u := by
  apply Fin.ext
  dsimp only [kickFun43]
  have hm2 : (u.val % 2 + 2 * ((u.val / 2 + (if u.val % 2 = 0 then θ₀ else θ₁)) % 2 ^ 42)) % 2 =
      u.val % 2 := by
    rw [Nat.add_mul_mod_self_left, Nat.mod_mod]
  have hd2 : (u.val % 2 + 2 * ((u.val / 2 + (if u.val % 2 = 0 then θ₀ else θ₁)) % 2 ^ 42)) / 2 =
      (u.val / 2 + (if u.val % 2 = 0 then θ₀ else θ₁)) % 2 ^ 42 := by
    rw [Nat.add_mul_div_left _ _ (by decide : 0 < 2),
      Nat.div_eq_of_lt (Nat.mod_lt _ (by decide)), zero_add]
  simp only [hm2, hd2]
  have hlt_div : u.val / 2 < 2 ^ 42 := by
    have hu := u.isLt
    have hpow : 2 ^ (1 + 42) = 2 * 2 ^ 42 := by decide
    omega
  by_cases h0 : u.val % 2 = 0
  · simp only [h0, ↓reduceIte, Nat.mod_add_mod, Nat.add_assoc, hsum,
      Nat.add_mod_right, Nat.mod_eq_of_lt hlt_div]
    omega
  · have hsum' : θ₁ + θ₀ = 2 ^ 42 := by omega
    simp only [h0, ↓reduceIte, Nat.mod_add_mod, Nat.add_assoc, hsum',
      Nat.add_mod_right, Nat.mod_eq_of_lt hlt_div]
    omega
def kickPerm43 (C_d : Fin (2 ^ 42)) : Equiv.Perm (Fin (2 ^ (1 + 42))) where
  toFun := kickFun43 C_d.val (2 ^ 42 - C_d.val)
  invFun := kickFun43 (2 ^ 42 - C_d.val) C_d.val
  left_inv := kickFun43_comp_id (by have := C_d.isLt; omega)
  right_inv := kickFun43_comp_id (by have := C_d.isLt; omega)
def uKickGidney43 (C_d : Fin (2 ^ 42)) : Unitary (2 ^ (1 + 42)) := fwdPermUnitary (kickPerm43 C_d)
def optX43 : Bool → Circuit (1 + 42)
  | false => Circuit.identity
  | true => Circuit.X ⟨0, by decide⟩
def cPre43 : Circuit (1 + 42) :=
  ((Circuit.S ⟨0, by decide⟩).seq (Circuit.Z ⟨0, by decide⟩)).seq (Circuit.H ⟨0, by decide⟩)
def cPost43 : Circuit (1 + 42) := (Circuit.H ⟨0, by decide⟩).seq (Circuit.S ⟨0, by decide⟩)
noncomputable def uSignalRotGidney43 (C_d : Fin (2 ^ 42)) : Unitary (2 ^ (1 + 42)) :=
  cPost43.eval * (uKickGidney43 C_d * cPre43.eval)
lemma ones_comp_add_ones_comp {P y C_sub : ℕ} (hy : y < P) (hC0 : 0 < C_sub) (hClt : C_sub < P) :
    (P - 1) - (((P - 1 - y) + C_sub) % P) = (y + (P - C_sub)) % P := by
  by_cases hcy : C_sub ≤ y
  · rw [Nat.mod_eq_of_lt (by omega), show y + (P - C_sub) = (y - C_sub) + P * 1 by omega,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
    omega
  · rw [show (P - 1 - y) + C_sub = ((P - 1 - y) + C_sub - P) + P * 1 by omega,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    omega
lemma bitsVal_odd_div_two (k_len C_sub : ℕ) (hC_lt : C_sub < 2 ^ (k_len + 2))
    (hodd : C_sub % 2 = 1) : 1 + 2 * bitsVal (fun j : Fin (k_len + 1) ↦ bitZ (decide (((C_sub
    / 2) / 2 ^ j.val) % 2 = 1))) = C_sub := by
  have hhalf_lt : C_sub / 2 < 2 ^ (k_len + 1) := by
    rw [pow_succ'] at hC_lt; omega
  have hbits : bitsVal (fun j : Fin (k_len + 1) ↦
      bitZ (decide (((C_sub / 2) / 2 ^ j.val) % 2 = 1))) = C_sub / 2 := by
    unfold bitsVal
    have hterm : ∀ j : Fin (k_len + 1), (bitZ (decide (((C_sub / 2) / 2 ^ j.val) % 2 = 1))).val =
          (C_sub / 2) / 2 ^ j.val % 2 := fun j ↦ by
      have hmod2 : ((C_sub / 2) / 2 ^ j.val) % 2 < 2 := Nat.mod_lt _ (by decide)
      by_cases h1 : ((C_sub / 2) / 2 ^ j.val) % 2 = 1
      · simp [h1, bitZ]
      · have h0 : ((C_sub / 2) / 2 ^ j.val) % 2 = 0 := by omega
        simp [h0, bitZ]
    simp only [hterm]
    exact sum_div_two_pow_mod_two_mul_two_pow (k_len + 1) (C_sub / 2) hhalf_lt
  rw [hbits]
  omega
lemma regVal_split_at {W n : ℕ} (r : QRegister W n) (tz rem : ℕ) (hW : tz + rem = W)
    (γ : BitAssignment n) : regVal r γ = regVal (r.slice 0 tz (by omega)) γ + 2 ^ tz * regVal
    (r.slice tz rem (by omega)) γ := by
  have hdisj : (r.slice 0 tz (by omega)).DisjointWires (r.slice tz rem (by omega)) := by
    rw [QRegister.disjoint_iff]; intro i j hij
    simp only [QRegister.slice_apply] at hij
    have hv := congrArg Fin.val (r.wires.injective hij)
    dsimp at hv; omega
  rw [← regVal_concat (r.slice 0 tz (by omega)) (r.slice tz rem (by omega)) hdisj γ]
  unfold regVal bitsVal
  have hcast : ∀ (f : Fin (tz + rem) → ℕ) (g : Fin W → ℕ),
      (∀ (i : ℕ) (hi1 : i < tz + rem) (hi2 : i < W), f ⟨i, hi1⟩ = g ⟨i, hi2⟩) →
      (∑ x : Fin (tz + rem), f x) = ∑ y : Fin W, g y := by
    intro f g hfg
    subst hW
    exact Finset.sum_congr rfl fun x _ ↦ hfg x.val x.isLt x.isLt
  refine (hcast _ _ fun i hi1 hi2 ↦ ?_).symm
  dsimp only
  congr 2
  by_cases hlt : i < tz
  · have hidx : (⟨i, hi1⟩ : Fin (tz + rem)) = Fin.castAdd rem ⟨i, hlt⟩ := Fin.ext rfl
    rw [hidx, QRegister.concat_apply_left, QRegister.slice_apply]
    exact congrArg (fun u ↦ γ (r u)) (Fin.ext (by dsimp; omega))
  · have hidx : (⟨i, hi1⟩ : Fin (tz + rem)) = Fin.natAdd tz ⟨i - tz, by omega⟩ :=
      Fin.ext (by dsimp; omega)
    rw [hidx, QRegister.concat_apply_right, QRegister.slice_apply]
    exact congrArg (fun u ↦ γ (r u)) (Fin.ext (by dsimp; omega))
section Dyn43
variable {Var : Type} {n : ℕ}
def dKickGidney43Dyn (v : Var) (C_d : Fin (2 ^ 42)) (rMid43 : QRegister (1 + 42) n)
    (rCarry : QRegister (activeMsbWidth42 C_d.val - 2) n)
    (hDisj : rMid43.DisjointWires rCarry) : DynamicCircuit Var n :=
  let qSig : Wire n := rMid43 ⟨0, by decide⟩
  let rCat : QRegister 42 n := rMid43.slice 1 42 (by decide)
  if hb0 : activeMsbWidth42 C_d.val = 0 then
    .circuit .identity
  else if hb1 : activeMsbWidth42 C_d.val = 1 then
    .circuit (Circuit.X (rCat ⟨41, by decide⟩))
  else
    let tz := trailingZeros42 C_d.val
    let k_len := activeMsbWidth42 C_d.val - 2
    have htz_eq : tz + (k_len + 2) = 42 := by
      dsimp [tz, k_len]
      unfold activeMsbWidth42 at hb0 hb1 ⊢
      have := trailingZeros42_le_42 C_d.val
      omega
    let rSub : QRegister (k_len + 2) n := rCat.slice tz (k_len + 2) (by omega)
    let rT : QRegister (k_len + 1) n := rSub.slice 1 (k_len + 1) (by omega)
    let c_in : Wire n := rSub 0
    let C_sub : ℕ := C_d.val / 2 ^ tz
    let bits : Fin (k_len + 1) → Bool := fun j ↦ decide (((C_sub / 2) / 2 ^ j.val) % 2 = 1)
    have hqCat : qSig ∉ rCat.image := by
      rw [QRegister.mem_image]; rintro ⟨j, hj⟩
      simp only [qSig, rCat, QRegister.slice_apply] at hj
      have hv := congrArg Fin.val (rMid43.wires.injective hj)
      dsimp at hv; omega
    have hqSub : qSig ∉ rSub.image := fun hm ↦ hqCat (QRegister.image_compose_subset rCat _ hm)
    have hdisj_TC : rT.DisjointWires rCarry :=
      (((hDisj.compose_left _).compose_left _).compose_left _)
    have hcin_T : c_in ∉ rT.image := QRegExt.head_not_mem_tail_image rSub
    have hcin_C : c_in ∉ rCarry.image :=
      ((hDisj.compose_left _).compose_left _).apply_not_mem_right 0
    .seq (.circuit (cnotFanoutCircuit qSig rSub hqSub))
      (.seq (gidneyConstAuxDyn v k_len bits rT rCarry c_in hdisj_TC hcin_T hcin_C)
        (.circuit (Circuit.X c_in ;;ᶜ cnotFanoutCircuit qSig rSub hqSub)))
theorem kickFun43_mk_val (c₀ c₁ x : ℕ) (hx : x < 2 ^ (1 + 42)) : (kickFun43 c₀ c₁ ⟨x, hx⟩).val
    = (x % 2) + 2 * (((x / 2) + (if x % 2 = 0 then c₀ else c₁)) % 2 ^ 42) := rfl
@[simp] theorem count_dKickGidney43Dyn_toff (v : Var) (C_d : Fin (2 ^ 42))
    (rMid43 : QRegister (1 + 42) n) (rCarry : QRegister (activeMsbWidth42 C_d.val - 2) n)
    (hDisj : rMid43.DisjointWires rCarry) : (dKickGidney43Dyn v C_d rMid43 rCarry hDisj).count
    .TOFF = 0 := by
  unfold dKickGidney43Dyn
  dsimp only
  split_ifs with hb0 hb1
  · rfl
  · simp [Circuit.X, Circuit.single]
  · simp [Circuit.X, Circuit.single]
@[simp] theorem count_dKickGidney43Dyn_t (v : Var) (C_d : Fin (2 ^ 42))
    (rMid43 : QRegister (1 + 42) n) (rCarry : QRegister (activeMsbWidth42 C_d.val - 2) n)
    (hDisj : rMid43.DisjointWires rCarry) : (dKickGidney43Dyn v C_d rMid43 rCarry hDisj).count
    .T = 2 * gidneyRotToffEquiv C_d.val := by
  unfold dKickGidney43Dyn gidneyRotToffEquiv
  dsimp only
  split_ifs with hb0 hb1
  · simp [hb0]
  · simp [hb1, Circuit.X, Circuit.single]
  · change ((DynamicCircuit.circuit (Var := Var) (cnotFanoutCircuit _ _ _)).count .T +
      ((gidneyConstAuxDyn v _ _ _ rCarry _ _ _ _).count .T +
        (Circuit.X _ ;;ᶜ cnotFanoutCircuit _ _ _).count .T)) = _
    rw [DynamicCircuit.count, Circuit.count_seq, count_cnotFanoutCircuit_t,
      count_gidneyConstAuxDyn_t]
    have hx : ∀ w : Wire n, (Circuit.X w).count .T = 0 := fun _ ↦ rfl
    rw [hx]
    omega
end Dyn43
theorem uKickGidney43_mulVec_ket (C_d : Fin (2 ^ 42))
    (β : BitAssignment (1 + 42)) (m : Fin (2 ^ 42)) :
    let q0 : Wire (1 + 42) := ⟨0, by decide⟩
    let rK0 : QRegister 42 (1 + 42) := QRegister.block 1 42 (by decide)
    (uKickGidney43 C_d).1.mulVec (ket (writeReg β rK0 (basisBits 42 m))) =
      ket (writeReg β rK0 (basisBits 42
        (modAddPerm 42 (if β q0 = 0 then C_d.val else 2 ^ 42 - C_d.val) m))) := by
  intro q0 rK0
  let β_in := writeReg β rK0 (basisBits 42 m)
  let g_in := (basisBitsEquiv (1 + 42)).symm β_in
  have hket_in : ket β_in = Pi.single g_in 1 := rfl
  change (fwdPermUnitary (kickPerm43 C_d)).1.mulVec (ket β_in) = _
  rw [hket_in, fwdPermUnitary_mulVec_single, single_eq_ket]
  apply congrArg ket
  let m' := modAddPerm 42 (if β q0 = 0 then C_d.val else 2 ^ 42 - C_d.val) m
  let β_out := writeReg β rK0 (basisBits 42 m')
  apply (basisBitsEquiv (1 + 42)).symm.injective
  rw [basisBitsEquiv_symm_basisBits]
  apply Fin.ext
  rw [← bitsVal_eq_symm_val]
  change (kickFun43 C_d.val (2 ^ 42 - C_d.val) g_in).val = regVal (QRegister.whole (1 + 42)) β_out
  have hg_in_val : g_in.val = regVal (QRegister.whole (1 + 42)) β_in := by
    rw [← bitsVal_eq_symm_val]; rfl
  have hwhole_split : ∀ γ : BitAssignment (1 + 42),
      regVal (QRegister.whole (1 + 42)) γ = (γ q0).val + 2 * regVal rK0 γ := by
    intro γ
    have hslice : (QRegister.whole (1 + 42)).slice 1 42 (by decide) = rK0 := by
      apply SingleCatClosureAlt.qreg_ext; intro i
      rfl
    simpa [q0, hslice] using regVal_head_tail (q := 42) (QRegister.whole (1 + 42)) γ
  have hq0_not_K : q0 ∉ Set.range rK0.wires := by
    rintro ⟨i, hi⟩
    have hv := congrArg Fin.val hi
    simp [q0, rK0] at hv
  have hm_val (μ : Fin (2 ^ 42)) : regVal rK0 (writeReg β rK0 (basisBits 42 μ)) = μ.val := by
    change bitsVal (fun i ↦ writeReg β rK0 (basisBits 42 μ) (rK0 i)) = μ.val
    rw [show (fun i ↦ writeReg β rK0 (basisBits 42 μ) (rK0 i)) = basisBits 42 μ from
      funext fun i ↦ writeReg_apply_reg β rK0 _ i, bitsVal_basisBits]
  have hq_in : β_in q0 = β q0 := writeReg_apply_of_not_mem β rK0 _ q0 hq0_not_K
  have hq_out : β_out q0 = β q0 := writeReg_apply_of_not_mem β rK0 _ q0 hq0_not_K
  have hm_in : regVal rK0 β_in = m.val := hm_val m
  have hm_out : regVal rK0 β_out = m'.val := hm_val m'
  dsimp only [kickFun43]
  rw [hg_in_val, hwhole_split β_in, hwhole_split β_out, hq_in, hq_out, hm_in, hm_out]
  have hq_lt : (β q0).val < 2 := ZMod.val_lt _
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hq_lt,
    Nat.add_mul_div_left _ _ (by decide), Nat.div_eq_of_lt hq_lt, zero_add,
    if_congr (ZMod.val_eq_zero (β q0)) rfl rfl]
  rfl
theorem intertwinesCat_uSignalRotGidney43 (C_d : Fin (2 ^ 42)) (U_cat_0 : Unitary (2 ^ 42))
    (hU : ∀ k : Fin (2 ^ 42), U_cat_0.1 k 0 = FullScaleBESector.phaseGradientState 42 k) :
    let q0 : Wire (1 + 42) := ⟨0, by decide⟩
    let rK0 : QRegister 42 (1 + 42) := QRegister.block 1 42 (by decide)
    let θ_d := -((4 * Real.pi * (C_d.val : ℝ)) / 2 ^ 42)
    PhaseGradSignalRot.IntertwinesCat
      (rK0.embedUnitary U_cat_0).1 (rK0.basisOutcomeProjector 0)
      (uSignalRotGidney43 C_d).1
      ((QRegister.singleton q0).embedUnitary (ryUnitary θ_d)).1 := by
  intro q0 rK0 θ_d
  let rSig := QRegister.singleton q0
  have hSigCat : rSig.DisjointWires rK0 := by
    rw [QRegister.disjoint_iff]; intro i j h; fin_cases i
    have hv := congrArg Fin.val h
    simp [q0, rK0, rSig, QRegister.singleton] at hv
  let P_Cat0 := rK0.basisOutcomeProjector 0
  let D := twoPhaseDiagMatrix 42 C_d.val (2 ^ 42 - C_d.val)
  have hKick : PhaseGradSignalRot.IntertwinesCat
      (rK0.embedUnitary U_cat_0).1 P_Cat0 (uKickGidney43 C_d).1
      (rSig.embedUnitary (twoPhaseDiagUnitary 42 C_d.val (2 ^ 42 - C_d.val))).1 := by
    have hComm_U : rSig.embedMatrix D * (rK0.embedUnitary U_cat_0).1 =
        (rK0.embedUnitary U_cat_0).1 * rSig.embedMatrix D :=
      rSig.embedMatrix_comm_of_disjoint rK0 hSigCat D U_cat_0.1
    have hComm_Cat0 : rSig.embedMatrix D * P_Cat0 = P_Cat0 * rSig.embedMatrix D :=
      rSig.embedMatrix_comm_of_disjoint rK0 hSigCat D (compProj 0)
    refine ⟨?_, hComm_U, hComm_Cat0⟩
    apply matrix_ext_ket
    intro β
    simp only [← Matrix.mulVec_mulVec]
    rw [basisOutcomeProjector_zero_mulVec_ket]
    by_cases hCat0 : localIdx rK0 β = 0
    · simp only [hCat0, ↓reduceIte]
      let θ := if β q0 = 0 then C_d.val else 2 ^ 42 - C_d.val
      let φ := Complex.exp ((2 * Real.pi * Complex.I * ((θ : ℕ) : ℂ)) / 2 ^ 42)
      have hRHS : (rK0.embedUnitary U_cat_0).1.mulVec ((rSig.embedMatrix D).mulVec (ket β)) =
          ∑ m' : Fin (2 ^ 42), (φ * FullScaleBESector.phaseGradientState 42 m') • ket
          (writeReg β rK0 (basisBits 42 m')) := by
        rw [singleton_embedMatrix_twoPhaseDiagMatrix_mulVec_ket, Matrix.mulVec_smul,
          QRegister.embedUnitary_val, embedMatrix_mulVec_ket, hCat0, Finset.smul_sum]
        refine Finset.sum_congr rfl fun m' _ ↦ ?_
        rw [hU m', smul_smul]
      have hLHS : (uKickGidney43 C_d).1.mulVec ((rK0.embedUnitary U_cat_0).1.mulVec (ket β)) =
          ∑ m' : Fin (2 ^ 42), (φ * FullScaleBESector.phaseGradientState 42 m') • ket
          (writeReg β rK0 (basisBits 42 m')) := by
        rw [QRegister.embedUnitary_val, embedMatrix_mulVec_ket, hCat0, Matrix.mulVec_sum]
        have h_term (m : Fin (2 ^ 42)) : (uKickGidney43 C_d).1.mulVec
            (U_cat_0.1 m 0 • ket (writeReg β rK0 (basisBits 42 m))) =
            FullScaleBESector.phaseGradientState 42 m • ket
            (writeReg β rK0 (basisBits 42 (modAddPerm 42 θ m))) := by
          rw [hU m, Matrix.mulVec_smul, uKickGidney43_mulVec_ket C_d β m]
        simp_rw [h_term]
        rw [← Equiv.sum_comp (modAddPerm 42 θ).symm]
        refine Finset.sum_congr rfl fun m' _ ↦ ?_
        rw [(modAddPerm 42 θ).apply_symm_apply]
        have h_kick := congrFun (modAddUnitary_mulVec_phaseGradientState 42 θ) m'
        have h_perm :
            ((modAddUnitary 42 θ).1.mulVec (FullScaleBESector.phaseGradientState 42)) m' =
              FullScaleBESector.phaseGradientState 42 ((modAddPerm 42 θ).symm m') := by
          change (Equiv.Perm.permMatrix ℂ ((modAddPerm 42 θ)⁻¹)).mulVec
            (FullScaleBESector.phaseGradientState 42) m' = _
          rw [Matrix.permMatrix_mulVec]
          rfl
        rw [← h_perm, h_kick]
        rfl
      change (uKickGidney43 C_d).1.mulVec ((rK0.embedUnitary U_cat_0).1.mulVec (ket β)) =
        (rK0.embedUnitary U_cat_0).1.mulVec ((rSig.embedMatrix D).mulVec (ket β))
      rw [hLHS, hRHS]
    · simp only [hCat0, ↓reduceIte, Matrix.mulVec_zero]
  let U_pre : Unitary 2 := Qubit.H * (Qubit.Z * Qubit.S)
  let U_post : Unitary 2 := Qubit.S * Qubit.H
  have hPre_eval : cPre43.eval = rSig.embedUnitary U_pre := by
    dsimp only [cPre43, U_pre, rSig, q0]
    rw [rSig.embedUnitary_mul, rSig.embedUnitary_mul]
    rfl
  have hPost_eval : cPost43.eval = rSig.embedUnitary U_post := by
    dsimp only [cPost43, U_post, rSig, q0]
    rw [rSig.embedUnitary_mul]
    rfl
  have hOne_comm : ∀ M : Operator 2, rSig.embedMatrix M * (1 : Operator (2 ^ (1 + 42))) =
      (1 : Operator (2 ^ (1 + 42))) * rSig.embedMatrix M := by
    intro M; simp
  have hPre := by
    simpa [mul_one] using intertwinesCat_singleton_q_sig q0 rK0 1 hSigCat hOne_comm U_cat_0 U_pre
  have hPost := by
    simpa [mul_one] using intertwinesCat_singleton_q_sig q0 rK0 1 hSigCat hOne_comm U_cat_0 U_post
  have hComb := hPost.mul (hKick.mul hPre)
  have hEval : (uSignalRotGidney43 C_d).1 =
      (rSig.embedUnitary U_post).1 * ((uKickGidney43 C_d).1 * (rSig.embedUnitary U_pre).1) := by
    simp only [uSignalRotGidney43, Submonoid.coe_mul, hPre_eval, hPost_eval]
  have hLocEq :
      U_post * (twoPhaseDiagUnitary 42 C_d.val (2 ^ 42 - C_d.val) * U_pre) = ryUnitary θ_d := by
    apply Subtype.ext
    change (Qubit.S.1 * Qubit.H.1) * (twoPhaseDiagMatrix 42 C_d.val (2 ^ 42 - C_d.val) *
      (Qubit.H.1 * (Qubit.Z.1 * Qubit.S.1))) = (ryUnitary θ_d).1
    rw [← Matrix.mul_assoc, twoPhaseDiagMatrix_sym 42 C_d.val (le_of_lt C_d.isLt),
      sH_conj_rzDiagMatrix]
    congr 2; dsimp only [θ_d]; ring
  have hEff : (rSig.embedUnitary U_post).1 * ((rSig.embedUnitary (twoPhaseDiagUnitary 42
      C_d.val (2 ^ 42 - C_d.val))).1 * (rSig.embedUnitary U_pre).1) =
      (rSig.embedUnitary (ryUnitary θ_d)).1 := by
    rw [← embedUnitary_mul_val, ← embedUnitary_mul_val, hLocEq]
  rw [hEval, ← hEff]
  exact hComb
abbrev rMid43InSingleCat (mPayload B_tot kWorkConst : ℕ) (hB42 : 42 ≤ B_tot) :
    QRegister (1 + 42) (kActSingleCatClosure mPayload B_tot kWorkConst) :=
  (QRegister.singleton (qSigInSingleCat mPayload B_tot kWorkConst)).concat
    ((rCatTotInSingleCat mPayload B_tot kWorkConst).compose (rTopCatSlice 42 B_tot hB42))
    (((qSigInSingleCat_disj_catScratch mPayload B_tot kWorkConst).compose_right _).compose_right _)
theorem rMid43InSingleCat_zero {mPayload B_tot kWorkConst : ℕ} (hB42 : 42 ≤ B_tot) :
    rMid43InSingleCat mPayload B_tot kWorkConst hB42 ⟨0, by decide⟩ =
      qSigInSingleCat mPayload B_tot kWorkConst := by
  have h1 : (⟨0, by decide⟩ : Fin (1 + 42)) = Fin.castAdd 42 (⟨0, by decide⟩ : Fin 1) := rfl
  change (rMid43InSingleCat mPayload B_tot kWorkConst hB42) _ = _
  rw [h1, rMid43InSingleCat, QRegister.concat_apply_left]
  rfl
theorem rBEInSingleCat_disj_rMid43 {mPayload B_tot kWorkConst : ℕ} (hB42 : 42 ≤ B_tot) :
    (rBEInSingleCat mPayload B_tot kWorkConst).DisjointWires
      (rMid43InSingleCat mPayload B_tot kWorkConst hB42) := by
  have hSig := rBEInSingleCat_disj_qSig mPayload B_tot kWorkConst
  have hCat := (rBEInSingleCat_disj_catTot mPayload B_tot kWorkConst).compose_right
    (rTopCatSlice 42 B_tot hB42)
  exact (FullSysCatSegmentBridge.disjointWires_concat_left _ hSig.symm hCat.symm).symm
end GidneySignalRotPart1
end
end ModGidneySignalRotPart1
section ModGidneySignalRotPart2
@[expose] public section
namespace GidneySignalRotPart2
open Operator Matrix Circuit _root_.DynamicCircuit DynCircuitExt QProg HermitianMat
open scoped Matrix ComplexOrder MatrixOrder Circuit.Notation Matrix.Norms.L2Operator BigOperators
open SpecsAux.SpecMirror
open PhaseGradSignalRot hiding IntertwinesCat
open TwosCompAndWire0Cancel
open GridGuard654ReflAux GridGuard654Flag288
open GidneySignalRotPart1
section SupportAndEmbed
theorem activeMsbWidth42_sub_two_le_40 (c : ℕ) : activeMsbWidth42 c - 2 ≤ 40 := by
  unfold activeMsbWidth42
  omega
theorem basisOutcomeProjector_zero_eq_of_image_eq {n m₁ m₂ : ℕ}
    (r₁ : QRegister m₁ n) (r₂ : QRegister m₂ n) (h : r₁.image = r₂.image) :
    r₁.basisOutcomeProjector 0 = r₂.basisOutcomeProjector 0 := by
  have h1 := (proj_zero_absorb_of_image_subset (rSmall := r₁) (rBig := r₂) (by rw [h])).2
  have h2 := (proj_zero_absorb_of_image_subset (rSmall := r₂) (rBig := r₁) (by rw [h])).1
  exact h2.symm.trans h1
theorem restrictAssertionToZeroAncilla_congr_image {Var : Type} {n m₁ m₂ : ℕ}
    [NeZero (2 ^ n)] (A : CQAssertionCompat Var (2 ^ n)) (r₁ : QRegister m₁ n) (r₂ : QRegister m₂ n)
    (h : r₁.image = r₂.image) : CQAssertion.restrictToZeroAncilla A r₁ =
    CQAssertion.restrictToZeroAncilla A r₂ := by
  funext σ
  refine Subtype.ext (Subtype.ext ?_)
  simp [CQAssertion.restrictToZeroAncilla_coe, basisOutcomeProjector_zero_eq_of_image_eq r₁ r₂ h]
theorem restrictZero_wp_qAssign_congr_of_comm_proj {Var : Type} [Fintype Var] {n m : ℕ}
    [NeZero (2 ^ n)] (U : Unitary (2 ^ n)) (r : QRegister m n) (hcomm : U.1 *
    r.basisOutcomeProjector 0 = r.basisOutcomeProjector 0 * U.1)
    {Ψ₁ Ψ₂ : CQAssertionCompat Var (2 ^ n)} (hΨ : CQAssertion.restrictToZeroAncilla Ψ₁ r =
    CQAssertion.restrictToZeroAncilla Ψ₂ r) : CQAssertion.restrictToZeroAncilla
    (wpQAssignCompat U Ψ₁) r = CQAssertion.restrictToZeroAncilla (wpQAssignCompat U Ψ₂) r := by
  let P := r.basisOutcomeProjector 0
  have hP_herm : Pᴴ = P := r.basisOutcomeProjector_conjTranspose 0
  have hadj : P * U.1ᴴ = U.1ᴴ * P := by
    have h := congrArg conjTranspose hcomm
    rwa [conjTranspose_mul, conjTranspose_mul, hP_herm] at h
  funext σ
  refine Subtype.ext (Subtype.ext ?_)
  have hΨ_σ : P * (Ψ₁ σ).1.1 * P = P * (Ψ₂ σ).1.1 * P := by
    simpa [P, CQAssertion.restrictToZeroAncilla_coe, hP_herm, Matrix.mul_assoc] using
      congrArg (fun X ↦ (X σ).1.1) hΨ
  have hexp (Φ : CQAssertionCompat Var (2 ^ n)) :
      (CQAssertion.restrictToZeroAncilla (wpQAssignCompat U Φ) r σ).1.1 =
        U.1ᴴ * (P * (Φ σ).1.1 * P) * U.1 := by
    calc (CQAssertion.restrictToZeroAncilla (wpQAssignCompat U Φ) r σ).1.1
        = (P * U.1ᴴ) * (Φ σ).1.1 * (U.1 * P) := by
          simp [P, CQAssertion.restrictToZeroAncilla_coe, wpQAssignCompat, qAssignObsMap,
            Observable.conj_coe, Unitary.coe_star, Matrix.star_eq_conjTranspose, hP_herm,
            Matrix.mul_assoc]
      _ = (U.1ᴴ * P) * (Φ σ).1.1 * (P * U.1) := by rw [hadj, ← hcomm]
      _ = U.1ᴴ * (P * (Φ σ).1.1 * P) * U.1 := by simp only [Matrix.mul_assoc]
  rw [hexp Ψ₁, hΨ_σ, ← hexp Ψ₂]
end SupportAndEmbed
section Ref43
theorem classicalPerm_mul_proj_eq_fwdPermUnitary {n k m : ℕ} (rAct : QRegister k n)
    (rWork : QRegister m n) (σ : Equiv.Perm (Fin (2 ^ k))) (c_ref : Circuit n)
    (f : BitAssignment n → BitAssignment n) (hperm : ClassicalPerm c_ref f)
    (hout : ∀ β w, w ∉ rAct.image → f β w = β w) (hval : ∀ β, (∀ j : Fin m, β (rWork j) = 0) →
    regVal rAct (f β) = (σ ⟨regVal rAct β, regVal_lt_two_pow rAct β⟩).val) : c_ref.eval.1 *
    rWork.basisOutcomeProjector 0 = (rAct.embedUnitary (fwdPermUnitary σ)).1 *
    rWork.basisOutcomeProjector 0 := by
  apply matrix_ext_basisKet
  intro β
  simp only [← Matrix.mulVec_mulVec, register_basisOutcomeProjector_zero_mulVec_basisKet]
  by_cases h0 : ∀ j : Fin m, β (rWork j) = 0
  · simp only [h0, implies_true, ↓reduceIte]
    rw [hperm β]
    let g_idx := (basisBitsEquiv n).symm β
    have hg_bits : basisBits n g_idx = β := basisBits_basisBitsEquiv_symm_eq β
    have hextr_eq : rAct.extractIndex g_idx = ⟨regVal rAct β, regVal_lt_two_pow rAct β⟩ := by
      ext
      exact (regVal_eq_extractIndex_val rAct β).symm
    let outIdx := σ (rAct.extractIndex g_idx)
    rw [QRegister.embedUnitary_val, basisKet, basisState, rAct.embedMatrix_mulVec_single_factors,
      fwdPermUnitary_mulVec_single, QRegister.tensorState_single_replaceIndex,
      pi_single_eq_basisKet, pi_single_eq_basisKet, basisBits_basisBitsEquiv_symm_eq]
    apply congrArg basisKet
    have hbits_eq : (fun i : Fin k ↦ f β (rAct i)) = basisBits k outIdx := by
      apply (basisBitsEquiv k).symm.injective
      ext
      rw [← bitsVal_eq_symm_val, ← bitsVal_eq_symm_val, bitsVal_basisBits]
      change regVal rAct (f β) = outIdx.val
      dsimp only [outIdx]
      rw [hextr_eq]
      exact hval β h0
    funext w
    by_cases hw : w ∈ Set.range rAct.wires
    · obtain ⟨i, rfl⟩ := hw
      rw [rAct.basisBits_replaceIndex_apply]
      exact congrFun hbits_eq i
    · have hw_img : w ∉ rAct.image := fun hm ↦ hw ((QRegister.mem_image rAct w).mp hm)
      rw [rAct.basisBits_replaceIndex_of_not_mem g_idx outIdx w hw, hg_bits, hout β w hw_img]
  · simp [h0]
def cKickGidney43Ref {n : ℕ} (C_d : Fin (2 ^ 42)) (rMid43 : QRegister (1 + 42) n)
    (rCarry : QRegister (activeMsbWidth42 C_d.val - 2) n)
    (hDisj : rMid43.DisjointWires rCarry) : Circuit n :=
  let qSig : Wire n := rMid43 ⟨0, by decide⟩
  let rCat : QRegister 42 n := rMid43.slice 1 42 (by decide)
  if hb0 : activeMsbWidth42 C_d.val = 0 then
    .identity
  else if hb1 : activeMsbWidth42 C_d.val = 1 then
    Circuit.X (rCat ⟨41, by decide⟩)
  else
    let tz := trailingZeros42 C_d.val
    let k_len := activeMsbWidth42 C_d.val - 2
    have htz_eq : tz + (k_len + 2) = 42 := by
      change trailingZeros42 C_d.val + (activeMsbWidth42 C_d.val - 2 + 2) = 42
      have hle := trailingZeros42_le_42 C_d.val
      have h0 : activeMsbWidth42 C_d.val ≠ 0 := hb0
      have h1 : activeMsbWidth42 C_d.val ≠ 1 := hb1
      unfold activeMsbWidth42 at h0 h1 ⊢
      generalize trailingZeros42 C_d.val = z at hle h0 h1 ⊢
      omega
    have hSub_le : tz + (k_len + 2) ≤ 42 := htz_eq.le
    have hT_le : 1 + (k_len + 1) ≤ k_len + 2 := Nat.add_comm 1 (k_len + 1) ▸ le_rfl
    let rSub : QRegister (k_len + 2) n := rCat.slice tz (k_len + 2) hSub_le
    let rT : QRegister (k_len + 1) n := rSub.slice 1 (k_len + 1) hT_le
    let c_in : Wire n := rSub 0
    let C_sub : ℕ := C_d.val / 2 ^ tz
    let bits : Fin (k_len + 1) → Bool := fun j ↦ decide (((C_sub / 2) / 2 ^ j.val) % 2 = 1)
    have hqCat : qSig ∉ rCat.image := by
      rw [QRegister.mem_image]; rintro ⟨j, hj⟩
      simp only [qSig, rCat, QRegister.slice_apply] at hj
      have hv := congrArg Fin.val (rMid43.wires.injective hj)
      dsimp at hv
      rw [Nat.add_comm] at hv
      exact Nat.succ_ne_zero j.val hv
    have hqSub : qSig ∉ rSub.image := fun hm ↦ hqCat (QRegister.image_compose_subset rCat _ hm)
    have hdisj_TC : rT.DisjointWires rCarry :=
      (((hDisj.compose_left _).compose_left _).compose_left _)
    have hcin_T : c_in ∉ rT.image := QRegExt.head_not_mem_tail_image rSub
    have hcin_C : c_in ∉ rCarry.image :=
      ((hDisj.compose_left _).compose_left _).apply_not_mem_right 0
    TwosCompAndWire0Cancel.cnotFanoutCircuit qSig rSub hqSub ;;ᶜ
      (gidneyConstAuxCircuit k_len bits rT rCarry c_in hdisj_TC hcin_T hcin_C ;;ᶜ
        (Circuit.X c_in ;;ᶜ TwosCompAndWire0Cancel.cnotFanoutCircuit qSig rSub hqSub))
theorem storeConst_dKickGidney43Dyn {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    [NeZero (2 ^ n)] (v : Var) (C_d : Fin (2 ^ 42)) (rMid43 : QRegister (1 + 42) n)
    (rCarry : QRegister (activeMsbWidth42 C_d.val - 2) n)
    (hDisj : rMid43.DisjointWires rCarry) : GridGuard654ReflAux.StoreConst
    (dKickGidney43Dyn v C_d rMid43 rCarry hDisj) := by
  unfold dKickGidney43Dyn
  dsimp only
  split_ifs with hb0 hb1
  · exact GridGuard654ReflAux.StoreConst.circuit _
  · exact GridGuard654ReflAux.StoreConst.circuit _
  · exact (GridGuard654ReflAux.StoreConst.circuit _).seq
      ((show GridGuard654ReflAux.StoreConst _ from
          storeConst_gidneyConstAuxDyn v _ _ _ rCarry _ _ _ _).seq
        (GridGuard654ReflAux.StoreConst.circuit _))
private lemma lemHex434 {Var : Type} [Fintype Var] [DecidableEq Var] {n k : ℕ} [NeZero (2 ^ n)]
    (v : Var) (cFan cAux cPostSub : Circuit n) (dAux : DynamicCircuit Var n)
    (rCarry : QRegister k n) (hcFan_disj : Disjoint cFan.support rCarry.image)
    (hwpAux : ∀ Θ : CQAssertionCompat Var (2 ^ n), (∀ σ val, Θ (Function.update σ v val) = Θ σ) →
        CQAssertion.restrictToZeroAncilla (wp dAux.compile Θ) rCarry =
        CQAssertion.restrictToZeroAncilla (wpQAssignCompat cAux.eval Θ) rCarry)
    (Θ : CQAssertionCompat Var (2 ^ n)) (hΘ : ∀ σ val, Θ (Function.update σ v val) = Θ σ) :
    CQAssertion.restrictToZeroAncilla (wp (DynamicCircuit.seq (Var := Var) (.circuit cFan)
        (.seq dAux (.circuit cPostSub))).compile Θ) rCarry = CQAssertion.restrictToZeroAncilla
      (wpQAssignCompat (cFan ;;ᶜ (cAux ;;ᶜ cPostSub)).eval Θ) rCarry := by
  let Ψ2 := wpQAssignCompat cPostSub.eval Θ
  have hΨ2_const : ∀ σ val, Ψ2 (Function.update σ v val) = Ψ2 σ :=
    fun σ val ↦ by simp only [Ψ2, wpQAssignCompat, hΘ σ val]
  have hwp1 : wp (DynamicCircuit.seq (Var := Var) (.circuit cFan)
      (.seq dAux (.circuit cPostSub))).compile Θ =
        wpQAssignCompat cFan.eval (wp dAux.compile Ψ2) := by
    change wp (DynamicCircuit.circuit cFan).compile
      (wp dAux.compile (wp (DynamicCircuit.circuit cPostSub).compile Θ)) = _
    simp only [DynamicCircuit.compile_circuit, DynCircuitExt.wp_circuit_compile_compat, Ψ2]
  rw [hwp1, restrictToZeroAncilla_wp_qAssign_comm_of_disjoint cFan rCarry hcFan_disj,
    hwpAux Ψ2 hΨ2_const,
    ← restrictToZeroAncilla_wp_qAssign_comm_of_disjoint cFan rCarry hcFan_disj]
  simp only [Ψ2, Circuit.eval_seq, wpQAssignCompat_comp, mul_assoc]
private lemma lemHex435 {n W tz k_len : ℕ} (htz_eq : tz + (k_len + 2) = W) (hLow_le : 0 + tz ≤ W)
    (hSub_le : tz + (k_len + 2) ≤ W) (hT_le : 1 + (k_len + 1) ≤ k_len + 2)
    {c : ℕ} (hc_lt : c < 2 ^ W) (_hc_ne0 : c ≠ 0)
    (hdvd_tz : 2 ^ tz ∣ c) (hodd : (c / 2 ^ tz) % 2 = 1) (qSig : Wire n) (rCat : QRegister W n)
    (hqSub : qSig ∉ (rCat.slice tz (k_len + 2) hSub_le).image) (rCarry : QRegister k_len n)
    (hSubCarry : Disjoint (rCat.slice tz (k_len + 2) hSub_le).image rCarry.image)
    (fAux : BitAssignment n → BitAssignment n)
    (houtAux : ∀ β w, w ∉ ((rCat.slice tz (k_len + 2) hSub_le).slice 1 (k_len + 1) hT_le).image →
      fAux β w = β w) (hvalAux : ∀ β, (∀ i : Fin k_len, β (rCarry i) = 0) →
      regVal ((rCat.slice tz (k_len + 2) hSub_le).slice 1 (k_len + 1) hT_le) (fAux β) =
        (regVal ((rCat.slice tz (k_len + 2) hSub_le).slice 1 (k_len + 1) hT_le) β +
          bitsVal (fun j : Fin (k_len + 1) ↦
            bitZ (decide ((((c / 2 ^ tz) / 2) / 2 ^ j.val) % 2 = 1))) +
          (β ((rCat.slice tz (k_len + 2) hSub_le) 0)).val) % 2 ^ (k_len + 1)) (β : BitAssignment n)
    (h0 : ∀ i : Fin k_len, β (rCarry i) = 0) :
    let rSub := rCat.slice tz (k_len + 2) hSub_le
    let c_in := rSub 0
    let fX0 : BitAssignment n → BitAssignment n := fun γ ↦ Function.update γ c_in (γ c_in + 1)
    let fTot : BitAssignment n → BitAssignment n :=
      ((xorCtrlMap qSig rSub ∘ fX0) ∘ fAux) ∘ xorCtrlMap qSig rSub
    (fTot β qSig).val + 2 * regVal rCat (fTot β) = ((β qSig).val + 2 * regVal rCat β) % 2 +
        2 * ((((β qSig).val + 2 * regVal rCat β) / 2 +
          (if ((β qSig).val + 2 * regVal rCat β) % 2 = 0 then c else 2 ^ W - c)) % 2 ^ W) := by
  intro rSub c_in fX0 fTot
  have hqSub' : qSig ∉ rSub.image := hqSub
  let rLow : QRegister tz n := rCat.slice 0 tz hLow_le
  let rT : QRegister (k_len + 1) n := rSub.slice 1 (k_len + 1) hT_le
  let C_sub : ℕ := c / 2 ^ tz
  let bits : Fin (k_len + 1) → Bool := fun j ↦ decide (((C_sub / 2) / 2 ^ j.val) % 2 = 1)
  have hcin_T : c_in ∉ rT.image := QRegExt.head_not_mem_tail_image rSub
  have hcin_in_Sub : c_in ∈ rSub.image := (QRegister.mem_image rSub c_in).mpr ⟨0, rfl⟩
  have hC_eq : c = 2 ^ tz * C_sub := (Nat.mul_div_cancel' hdvd_tz).symm
  have hC_sub_lt : C_sub < 2 ^ (k_len + 2) := by
    have hlt : c < 2 ^ (tz + (k_len + 2)) := htz_eq ▸ hc_lt
    exact Nat.div_lt_of_lt_mul (by rwa [Nat.pow_add] at hlt)
  have hC_sub_pos : 0 < C_sub :=
    Nat.pos_of_ne_zero (fun h00 ↦ by dsimp [C_sub] at h00; simp [h00] at hodd)
  have hbits_val : 1 + 2 * bitsVal (fun j ↦ bitZ (bits j)) = C_sub :=
    bitsVal_odd_div_two k_len C_sub hC_sub_lt hodd
  have houtSub {w : Wire n} (hw : w ∉ rSub.image) : fTot β w = β w := by
    have hwT : w ∉ rT.image := fun hm ↦ hw (QRegister.image_compose_subset rSub _ hm)
    have hw_cin : w ≠ c_in := fun h ↦ hw (h ▸ hcin_in_Sub)
    dsimp only [fTot, fX0, Function.comp_apply]
    unfold xorCtrlMap
    simp only [hw, ↓reduceIte, Function.update_of_ne hw_cin, houtAux _ w hwT]
  have hq_preserved : fTot β qSig = β qSig := houtSub hqSub'
  have hLow_preserved : regVal rLow (fTot β) = regVal rLow β :=
    regVal_congr rLow fun i ↦ houtSub fun hm ↦ by
      rcases (QRegister.mem_image rSub _).mp hm with ⟨j, hj⟩
      have hv := congrArg Fin.val (rCat.wires.injective hj)
      dsimp [rLow, rSub] at hv
      exact Nat.ne_of_lt (by have := i.isLt; omega) hv
  let β₁ := xorCtrlMap qSig rSub β
  have hβ₁_carry : ∀ i : Fin k_len, β₁ (rCarry i) = 0 := fun i ↦ by
    have hnotSub : rCarry i ∉ rSub.image := fun hm ↦ Finset.disjoint_left.mp hSubCarry hm
        ((QRegister.mem_image rCarry _).mpr ⟨i, rfl⟩)
    dsimp only [β₁, xorCtrlMap]
    simp only [hnotSub, ↓reduceIte]
    exact h0 i
  have hAddStep : regVal rSub (fX0 (fAux β₁)) = (regVal rSub β₁ + C_sub) % 2 ^ (k_len + 2) := by
    rw [regVal_head_tail rSub (fX0 (fAux β₁))]
    have hT_eq : regVal rT (fX0 (fAux β₁)) = regVal rT (fAux β₁) := by
      refine regVal_congr rT fun j ↦ ?_
      have hj_ne : rT j ≠ c_in := fun h ↦ hcin_T (h ▸ (QRegister.mem_image rT _).mpr ⟨j, rfl⟩)
      exact Function.update_of_ne hj_ne _ _
    have hcin_eq : fAux β₁ c_in = β₁ c_in := houtAux β₁ c_in hcin_T
    have hfX0_cin : fX0 (fAux β₁) c_in = β₁ c_in + 1 := by
      dsimp only [fX0]; rw [Function.update_self, hcin_eq]
    rw [hT_eq, hfX0_cin, hvalAux β₁ hβ₁_carry]
    have hb0_id : ∀ z : ZMod 2, (z + 1).val + 2 * z.val = z.val + 1 := by decide
    let X := regVal rT β₁ + bitsVal (fun j ↦ bitZ (bits j)) + (β₁ c_in).val
    rw [add_two_mul_mod _ X (2 ^ (k_len + 1)) (ZMod.val_lt _), ← pow_succ']
    congr 1
    rw [regVal_head_tail rSub β₁]
    have hz := hb0_id (β₁ c_in)
    have hlin : ∀ a1 a0 t b cs : ℕ, a1 + 2 * a0 = a0 + 1 → 1 + 2 * b = cs →
        a1 + 2 * (t + b + a0) = (a0 + 2 * t) + cs := by intros; omega
    exact hlin _ _ _ _ _ hz hbits_val
  let β₂ := fX0 (fAux β₁)
  have hβ₂_q : β₂ qSig = β qSig := by
    have hqT : qSig ∉ rT.image := fun hm ↦ hqSub' (QRegister.image_compose_subset rSub _ hm)
    have hq_ne_cin : qSig ≠ c_in := fun h ↦ hqSub' (h ▸ hcin_in_Sub)
    dsimp only [β₂, fX0]
    rw [Function.update_of_ne hq_ne_cin, houtAux _ qSig hqT]
    dsimp only [β₁, xorCtrlMap]
    simp only [hqSub', ↓reduceIte]
  have hSub_final : regVal rSub (fTot β) = (regVal rSub β + (if (β qSig).val = 0 then C_sub
      else 2 ^ (k_len + 2) - C_sub)) % 2 ^ (k_len + 2) := by
    change regVal rSub (xorCtrlMap qSig rSub β₂) = _
    rcases bit_cases (β qSig) with hq0 | hq1
    · have hβ₁_sub : regVal rSub β₁ = regVal rSub β := by
        refine regVal_congr rSub fun j ↦ ?_
        have hmem : rSub j ∈ rSub.image := (QRegister.mem_image rSub _).mpr ⟨j, rfl⟩
        dsimp only [β₁, xorCtrlMap]
        simp only [hmem, ↓reduceIte, hq0, add_zero]
      have hfin_sub : regVal rSub (xorCtrlMap qSig rSub β₂) = regVal rSub β₂ := by
        refine regVal_congr rSub fun j ↦ ?_
        have hmem : rSub j ∈ rSub.image := (QRegister.mem_image rSub _).mpr ⟨j, rfl⟩
        dsimp only [xorCtrlMap]
        simp only [hmem, ↓reduceIte, hβ₂_q, hq0, add_zero]
      rw [hfin_sub, hq0, ZMod.val_zero]
      simp only [↓reduceIte]
      dsimp only [β₂]
      rw [hAddStep, hβ₁_sub]
    · have h1_val : (β qSig).val = 1 := by rw [hq1]; rfl
      have hflip : ∀ δ : BitAssignment n, δ qSig = 1 →
          regVal rSub (xorCtrlMap qSig rSub δ) = 2 ^ (k_len + 2) - 1 - regVal rSub δ := by
        intro δ hδ
        have hcongr : regVal rSub (xorCtrlMap qSig rSub δ) =
            bitsVal (fun j : Fin (k_len + 2) ↦ δ (rSub j) + 1) := by
          have hfun : (fun j : Fin (k_len + 2) ↦ xorCtrlMap qSig rSub δ (rSub j)) =
              (fun j : Fin (k_len + 2) ↦ δ (rSub j) + 1) := by
            funext j
            have hmem : rSub j ∈ rSub.image := (QRegister.mem_image rSub _).mpr ⟨j, rfl⟩
            dsimp only [xorCtrlMap]
            simp only [hmem, ↓reduceIte, hδ]
          change bitsVal (fun j : Fin (k_len + 2) ↦ xorCtrlMap qSig rSub δ (rSub j)) = _
          rw [hfun]
        rw [hcongr]
        have hsum := bitsVal_flip_add_self (fun j : Fin (k_len + 2) ↦ δ (rSub j))
        have hsub_id : ∀ a b p : ℕ, a + b = p - 1 → a = p - 1 - b := by intros; omega
        exact hsub_id _ _ _ hsum
      rw [h1_val]
      simp only [Nat.one_ne_zero, ↓reduceIte]
      rw [hflip β₂ (by rw [hβ₂_q]; exact hq1)]
      dsimp only [β₂]
      rw [hAddStep, hflip β hq1]
      exact ones_comp_add_ones_comp (regVal_lt_two_pow rSub β) hC_sub_pos hC_sub_lt
  rw [hq_preserved]
  have hq_lt : (β qSig).val < 2 := ZMod.val_lt _
  have hm2 : ((β qSig).val + 2 * regVal rCat β) % 2 = (β qSig).val := by
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hq_lt]
  have hd2 : ((β qSig).val + 2 * regVal rCat β) / 2 = regVal rCat β := by
    rw [Nat.add_mul_div_left _ _ (by decide), Nat.div_eq_of_lt hq_lt, zero_add]
  rw [hm2, hd2]
  let θ_sub : ℕ := if (β qSig).val = 0 then C_sub else 2 ^ (k_len + 2) - C_sub
  have hθ_mul : (if (β qSig).val = 0 then c else 2 ^ W - c) = 2 ^ tz * θ_sub := by
    dsimp only [θ_sub]
    split_ifs with h00
    · exact hC_eq
    · have h2W : 2 ^ W = 2 ^ tz * 2 ^ (k_len + 2) := by rw [← htz_eq, Nat.pow_add]
      rw [hC_eq]
      nth_rw 1 [h2W]
      rw [← Nat.mul_sub]
  rw [hθ_mul, add_mul_pow_mod_split (regVal rCat β) θ_sub tz (k_len + 2) htz_eq]
  have hSplitCat := regVal_split_at rCat tz (k_len + 2) htz_eq β
  have hLow_lt : regVal rLow β < 2 ^ tz := regVal_lt_two_pow rLow β
  have hm_mod : regVal rCat β % 2 ^ tz = regVal rLow β := by
    rw [hSplitCat]; dsimp only [rLow]
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hLow_lt]
  have hm_div : regVal rCat β / 2 ^ tz = regVal rSub β := by
    rw [hSplitCat, Nat.add_mul_div_left _ _ (Nat.two_pow_pos tz),
      Nat.div_eq_of_lt hLow_lt, zero_add]
  rw [regVal_split_at rCat tz (k_len + 2) htz_eq (fTot β)]
  dsimp only [rLow, rSub] at hLow_preserved hSub_final ⊢
  rw [hLow_preserved, hSub_final, hm_mod, hm_div]
theorem cKickGidney43Ref_props {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    [NeZero (2 ^ n)] (v : Var) (C_d : Fin (2 ^ 42)) (rMid43 : QRegister (1 + 42) n)
    (rCarry : QRegister (activeMsbWidth42 C_d.val - 2) n)
    (hDisj : rMid43.DisjointWires rCarry) : (∀ Θ : CQAssertionCompat Var (2 ^ n), (∀ σ val, Θ
    (Function.update σ v val) = Θ σ) → CQAssertion.restrictToZeroAncilla (wp (dKickGidney43Dyn v
    C_d rMid43 rCarry hDisj).compile Θ) rCarry = CQAssertion.restrictToZeroAncilla
    (wpQAssignCompat (cKickGidney43Ref C_d rMid43 rCarry hDisj).eval Θ) rCarry) ∧
    ((cKickGidney43Ref C_d rMid43 rCarry hDisj).eval.1 * rCarry.basisOutcomeProjector 0 =
    rCarry.basisOutcomeProjector 0 * (cKickGidney43Ref C_d rMid43 rCarry hDisj).eval.1) ∧
    ((cKickGidney43Ref C_d rMid43 rCarry hDisj).eval.1 * rCarry.basisOutcomeProjector 0 =
    (rMid43.embedUnitary (uKickGidney43 C_d)).1 * rCarry.basisOutcomeProjector 0) := by
  have hMidCarryDisj : Disjoint rMid43.image rCarry.image :=
    (QRegExt.disjointWires_iff_disjoint_image rMid43 rCarry).mp hDisj
  have hSuff : ∃ f : BitAssignment n → BitAssignment n, ClassicalPerm
      (cKickGidney43Ref C_d rMid43 rCarry hDisj) f ∧ (∀ β w, w ∉ rMid43.image → f β w = β w) ∧
      (∀ β, (∀ j, β (rCarry j) = 0) → regVal rMid43 (f β) = (kickPerm43 C_d ⟨regVal rMid43 β,
      regVal_lt_two_pow rMid43 β⟩).val) ∧ (∀ Θ : CQAssertionCompat Var (2 ^ n), (∀ σ val, Θ
      (Function.update σ v val) = Θ σ) → CQAssertion.restrictToZeroAncilla (wp (dKickGidney43Dyn
      v C_d rMid43 rCarry hDisj).compile Θ) rCarry = CQAssertion.restrictToZeroAncilla
      (wpQAssignCompat (cKickGidney43Ref C_d rMid43 rCarry hDisj).eval Θ) rCarry) := by
    let qSig : Wire n := rMid43 ⟨0, by decide⟩
    let rCat : QRegister 42 n := rMid43.slice 1 42 (by decide)
    have hMidHead : ∀ γ : BitAssignment n, regVal rMid43 γ = (γ qSig).val + 2 * regVal rCat γ :=
      fun γ ↦ regVal_head_tail (q := 42) rMid43 γ
    unfold dKickGidney43Dyn cKickGidney43Ref
    dsimp only
    split_ifs with hb0 hb1
    · refine ⟨id, ClassicalPerm.identity, fun _ _ _ ↦ rfl, fun β _ ↦ ?_, fun Θ _ ↦ ?_⟩
      · have hC0 : C_d.val = 0 := (activeMsbWidth42_eq_zero_iff C_d.isLt).mp hb0
        change regVal rMid43 β = (kickFun43 C_d.val (2 ^ 42 - C_d.val) ⟨regVal rMid43 β, _⟩).val
        rw [kickFun43_mk_val, hMidHead β, hC0]
        have hm2 : ((β qSig).val + 2 * regVal rCat β) % 2 = (β qSig).val := by
          rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (ZMod.val_lt _)]
        have hd2 : ((β qSig).val + 2 * regVal rCat β) / 2 = regVal rCat β := by
          rw [Nat.add_mul_div_left _ _ (by decide), Nat.div_eq_of_lt (ZMod.val_lt _), zero_add]
        rw [hm2, hd2, Nat.sub_zero]
        split_ifs
        · rw [Nat.add_zero, Nat.mod_eq_of_lt (regVal_lt_two_pow rCat β)]
        · rw [Nat.add_mod_right, Nat.mod_eq_of_lt (regVal_lt_two_pow rCat β)]
      · rw [DynamicCircuit.compile_circuit, DynCircuitExt.wp_circuit_compile_compat]
    · let w41 : Wire n := rCat ⟨41, by decide⟩
      let f1 : BitAssignment n → BitAssignment n := fun β ↦ Function.update β w41 (β w41 + 1)
      refine ⟨f1, fun β ↦ evolve_X_basisKet w41 β, fun β w hw ↦ ?_, fun β _ ↦ ?_, fun Θ _ ↦ ?_⟩
      · have hw41_mem : w41 ∈ rMid43.image := QRegister.image_compose_subset rMid43 _
            ((QRegister.mem_image rCat w41).mpr ⟨⟨41, by decide⟩, rfl⟩)
        exact Function.update_of_ne (by rintro rfl; exact hw hw41_mem) _ _
      · have htz41 : trailingZeros42 C_d.val = 41 := by
          have hle := trailingZeros42_le_42 C_d.val
          unfold activeMsbWidth42 at hb1
          omega
        have hC_ne0 : C_d.val ≠ 0 := fun h0 ↦ hb0 ((activeMsbWidth42_eq_zero_iff C_d.isLt).mpr h0)
        have hdvd41 : 2 ^ 41 ∣ C_d.val := htz41 ▸ two_pow_trailingZeros42_dvd C_d.val
        have hC_eq : C_d.val = 2 ^ 41 := by
          rcases hdvd41 with ⟨q, hq⟩
          have := C_d.isLt
          omega
        have hw41_ne_q : w41 ≠ qSig := by
          intro h
          simp only [w41, qSig, rCat, QRegister.slice_apply] at h
          have hv := congrArg Fin.val (rMid43.wires.injective h)
          exact absurd hv (by decide)
        have hfq : f1 β qSig = β qSig := Function.update_of_ne hw41_ne_q.symm _ _
        have hlow_eq : regVal (rCat.slice 0 41 (by decide)) (f1 β) =
            regVal (rCat.slice 0 41 (by decide)) β := by
          refine regVal_congr _ fun i ↦ ?_
          have hne : (rCat.slice 0 41 (by decide)) i ≠ w41 := by
            intro h
            simp only [w41, QRegister.slice_apply] at h
            have hv := congrArg Fin.val (rCat.wires.injective h)
            dsimp at hv; rw [Nat.zero_add] at hv
            exact Nat.ne_of_lt i.isLt hv
          exact Function.update_of_ne hne _ _
        have hhi_val : ∀ γ : BitAssignment n,
            regVal (rCat.slice 41 1 (by decide)) γ = (γ w41).val := fun γ ↦ by
          unfold regVal bitsVal; rw [Fin.sum_univ_one]
          simp only [Fin.val_zero, _root_.pow_zero, mul_one, QRegister.slice_apply]; rfl
        have hf1_w41 : (f1 β w41).val = ((β w41).val + 1) % 2 := by
          dsimp only [f1]; rw [Function.update_self]
          have hz : ∀ z : ZMod 2, (z + 1).val = (z.val + 1) % 2 := by decide
          exact hz (β w41)
        change regVal rMid43 (f1 β) =
          (kickFun43 C_d.val (2 ^ 42 - C_d.val) ⟨regVal rMid43 β, _⟩).val
        rw [kickFun43_mk_val, hMidHead (f1 β), hMidHead β, hfq, hC_eq,
          regVal_split_at rCat 41 1 rfl (f1 β), regVal_split_at rCat 41 1 rfl β,
          hlow_eq, hhi_val (f1 β), hhi_val β, hf1_w41]
        have hq_lt : (β qSig).val < 2 := ZMod.val_lt _
        have hlow_lt : regVal (rCat.slice 0 41 (by decide)) β < 2 ^ 41 := regVal_lt_two_pow _ β
        generalize (β qSig).val = q at hq_lt ⊢
        generalize regVal (rCat.slice 0 41 (by decide)) β = low at hlow_lt ⊢
        generalize (β w41).val = hi
        have hm2 : (q + 2 * (low + 2 ^ 41 * hi)) % 2 = q := by
          rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hq_lt]
        have hd2 : (q + 2 * (low + 2 ^ 41 * hi)) / 2 = low + 2 ^ 41 * hi := by
          rw [Nat.add_mul_div_left _ _ (by decide), Nat.div_eq_of_lt hq_lt, zero_add]
        have hsub : 2 ^ 42 - 2 ^ 41 = (2 : ℕ) ^ 41 := by decide
        rw [hm2, hd2, hsub]
        have hite : (if q = 0 then (2 : ℕ) ^ 41 else 2 ^ 41) = 2 ^ 41 * 1 := by
          split_ifs <;> exact (Nat.mul_one _).symm
        rw [hite]
        have hm_mod : (low + 2 ^ 41 * hi) % 2 ^ 41 = low := by
          rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlow_lt]
        have hm_div : (low + 2 ^ 41 * hi) / 2 ^ 41 = hi := by
          rw [Nat.add_mul_div_left _ _ (Nat.two_pow_pos 41), Nat.div_eq_of_lt hlow_lt, zero_add]
        rw [add_mul_pow_mod_split (low + 2 ^ 41 * hi) 1 41 1 rfl, hm_mod, hm_div, pow_one]
      · rw [DynamicCircuit.compile_circuit, DynCircuitExt.wp_circuit_compile_compat]
    · let tz := trailingZeros42 C_d.val
      let k_len := activeMsbWidth42 C_d.val - 2
      have htz_eq : tz + (k_len + 2) = 42 := by
        dsimp [tz, k_len]
        unfold activeMsbWidth42 at hb0 hb1 ⊢
        have := trailingZeros42_le_42 C_d.val
        omega
      have hLow_le : 0 + tz ≤ 42 := by omega
      have hSub_le : tz + (k_len + 2) ≤ 42 := htz_eq.le
      have hT_le : 1 + (k_len + 1) ≤ k_len + 2 := Nat.add_comm 1 (k_len + 1) ▸ le_rfl
      let rSub : QRegister (k_len + 2) n := rCat.slice tz (k_len + 2) hSub_le
      let rT : QRegister (k_len + 1) n := rSub.slice 1 (k_len + 1) hT_le
      let c_in : Wire n := rSub 0
      let C_sub : ℕ := C_d.val / 2 ^ tz
      let bits : Fin (k_len + 1) → Bool := fun j ↦ decide (((C_sub / 2) / 2 ^ j.val) % 2 = 1)
      have hqCat : qSig ∉ rCat.image := by
        rw [QRegister.mem_image]; rintro ⟨j, hj⟩
        simp only [qSig, rCat, QRegister.slice_apply] at hj
        have hv := congrArg Fin.val (rMid43.wires.injective hj)
        dsimp at hv; rw [Nat.add_comm] at hv
        exact Nat.succ_ne_zero j.val hv
      have hqSub : qSig ∉ rSub.image := fun hm ↦ hqCat (QRegister.image_compose_subset rCat _ hm)
      have hdisj_TC : rT.DisjointWires rCarry :=
        (((hDisj.compose_left _).compose_left _).compose_left _)
      have hcin_T : c_in ∉ rT.image := QRegExt.head_not_mem_tail_image rSub
      have hcin_C : c_in ∉ rCarry.image :=
        ((hDisj.compose_left _).compose_left _).apply_not_mem_right 0
      obtain ⟨fAux, hpermAux, houtAux, hvalAux, hwpAux⟩ :=
        gidneyConstAux_correct (Var := Var) v k_len bits rT rCarry c_in hdisj_TC hcin_T hcin_C
      let cFan := TwosCompAndWire0Cancel.cnotFanoutCircuit qSig rSub hqSub
      let cPostSub := Circuit.X c_in ;;ᶜ cFan
      let cAux := gidneyConstAuxCircuit k_len bits rT rCarry c_in hdisj_TC hcin_T hcin_C
      let dAux := gidneyConstAuxDyn v k_len bits rT rCarry c_in hdisj_TC hcin_T hcin_C
      let fX0 : BitAssignment n → BitAssignment n := fun γ ↦ Function.update γ c_in (γ c_in + 1)
      let fTot : BitAssignment n → BitAssignment n :=
        ((xorCtrlMap qSig rSub ∘ fX0) ∘ fAux) ∘ xorCtrlMap qSig rSub
      have hSub_in_Mid : rSub.image ⊆ rMid43.image :=
        (QRegister.image_compose_subset rCat _).trans (QRegister.image_compose_subset rMid43 _)
      have hq_in_Mid : qSig ∈ rMid43.image :=
        (QRegister.mem_image rMid43 qSig).mpr ⟨⟨0, by decide⟩, rfl⟩
      have hcin_in_Sub : c_in ∈ rSub.image := (QRegister.mem_image rSub c_in).mpr ⟨0, rfl⟩
      have hSubCarryDisj : Disjoint rSub.image rCarry.image :=
        Finset.disjoint_of_subset_left hSub_in_Mid hMidCarryDisj
      have hcFan_disj : Disjoint cFan.support rCarry.image := by
        refine Finset.disjoint_of_subset_left
          (TwosCompAndWire0Cancel.support_cnotFanoutCircuit_subset qSig rSub hqSub) ?_
        rw [Finset.disjoint_insert_left]
        exact ⟨Finset.disjoint_left.mp hMidCarryDisj hq_in_Mid, hSubCarryDisj⟩
      have hpermTot : ClassicalPerm (cFan ;;ᶜ (cAux ;;ᶜ cPostSub)) fTot := by
        have h1 := TwosCompAndWire0Cancel.classicalPerm_cnotFanoutCircuit qSig rSub hqSub
        have hx : ClassicalPerm (Circuit.X c_in) fX0 := fun γ ↦ evolve_X_basisKet c_in γ
        exact h1.seq (hpermAux.seq (hx.seq h1))
      have houtTot : ∀ β w, w ∉ rMid43.image → fTot β w = β w := by
        intro β w hw
        have hwSub : w ∉ rSub.image := fun hm ↦ hw (hSub_in_Mid hm)
        have hwT : w ∉ rT.image := fun hm ↦ hwSub (QRegister.image_compose_subset rSub _ hm)
        have hw_ne_cin : w ≠ c_in := fun h ↦ hwSub (h ▸ hcin_in_Sub)
        dsimp only [fTot, fX0, Function.comp_apply]
        unfold xorCtrlMap
        simp only [hwSub, ↓reduceIte, Function.update_of_ne hw_ne_cin, houtAux _ w hwT]
      refine ⟨fTot, hpermTot, houtTot, fun β h0 ↦ ?_, fun Θ hΘ ↦ ?_⟩
      · have hC_ne0 : C_d.val ≠ 0 :=
          fun h00 ↦ hb0 ((activeMsbWidth42_eq_zero_iff C_d.isLt).mpr h00)
        change regVal rMid43 (fTot β) =
          (kickFun43 C_d.val (2 ^ 42 - C_d.val) ⟨regVal rMid43 β, _⟩).val
        rw [kickFun43_mk_val, hMidHead (fTot β), hMidHead β]
        exact lemHex435 htz_eq hLow_le hSub_le hT_le C_d.isLt hC_ne0
          (two_pow_trailingZeros42_dvd C_d.val)
          (odd_div_two_pow_trailingZeros42 hC_ne0 C_d.isLt)
          qSig rCat hqSub rCarry hSubCarryDisj fAux houtAux hvalAux β h0
      · exact lemHex434 v cFan cAux cPostSub dAux rCarry hcFan_disj hwpAux Θ hΘ
  obtain ⟨f, hperm, hout, hval, hwp⟩ := hSuff
  refine ⟨hwp, ?_, ?_⟩
  · exact classicalPerm_comm_proj_zero rCarry hperm fun β j ↦ hout β (rCarry j)
      (Finset.disjoint_right.mp hMidCarryDisj ((QRegister.mem_image rCarry _).mpr ⟨j, rfl⟩))
  · exact classicalPerm_mul_proj_eq_fwdPermUnitary rMid43 rCarry (kickPerm43 C_d) _ f
      hperm hout hval
end Ref43
end GidneySignalRotPart2
end
end ModGidneySignalRotPart2
section ModGidneySignalRotGuardWrap
@[expose] public section
namespace GidneySignalRotGuardWrap
section ConfigGidneySignalRotGuardWrap
set_option exponentiation.threshold 256
open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt Real
open scoped Matrix ComplexOrder MatrixOrder Circuit.Notation Matrix.Norms.L2Operator BigOperators
open SpecsAux.SpecMirror
open SpecsAux.BridgeFermionicComm
open SpecsAux.BridgeFermionicComm.SpecInner
open SpecsAux.FullScaleBESector hiding phaseGradientState
open SpecsAux.PhaseGradCatalystCore
open SpecsAux.BridgeDuhamel
open PhaseGradSignalRot hiding IntertwinesCat
open TFreeLaurentGQSP CatalyzedLaurentGQSP
open BidirectionalCatalyzedGQSP
open BidirectionalCatalyzedGQSPBridge
open GeneralBetaAndAlphaTopEndpoint
open GidneySignalRotPart1
def biPrefixGidneyRotToffSum (M : ℕ) (C : Fin (M + 1) → Fin (2 ^ 42)) (t : ℕ) : ℕ :=
  ∑ j ∈ Finset.range (t + 1), gidneyRotToffEquiv (biCode M C j).val
theorem biPrefixGidneyRotToffSum_eq_univ_sum (M : ℕ) (C : Fin (M + 1) → Fin (2 ^ 42)) :
    biPrefixGidneyRotToffSum M C M = ∑ t : Fin (M + 1), gidneyRotToffEquiv (C t).val := by
  unfold biPrefixGidneyRotToffSum biCode
  rw [← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  simp only [dite_eq_left j.isLt, Fin.eta]
end ConfigGidneySignalRotGuardWrap
end GidneySignalRotGuardWrap
end
end ModGidneySignalRotGuardWrap
section ModGidneySignalRotHoistBridge
@[expose] public section
namespace GidneySignalRotHoistBridge
section ConfigGidneySignalRotHoistBridge
set_option backward.isDefEq.respectTransparency true
set_option exponentiation.threshold 256
local instance (priority := 1000000) instNeZeroTwoPowGidneyHoist (k : ℕ) : NeZero (2 ^ k) :=
  ⟨Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos k)⟩
open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt Real
open scoped Matrix BigOperators Matrix.Norms.L2Operator
open DyadicQft64.PhasePerm SpecsAux.SpecMirror
open SingleCatSpine (rTopCatSlice)
open SingleCatClosure (qSigInSingleCat rCatTotInSingleCat)
open InterWalkRSum42Hoist
  (IsHigh3924Reg qSig80_ge_3924 isHigh3924Reg_concat)
open GidneySignalRotPart1 (rMid43InSingleCat)
theorem isHigh3924Reg_rMid43InSingleCat80 :
    IsHigh3924Reg (rMid43InSingleCat 80 48 40 (by decide : 42 ≤ 48)) := by
  refine isHigh3924Reg_concat _ (fun i ↦ by fin_cases i; exact qSig80_ge_3924) (fun i ↦ ?_)
  have := i.isLt
  dsimp [rCatTotInSingleCat, SingleCatClosure.rCatScratchInSingleCat,
    SingleCatClosure.rAncInSingleCat, SingleCatClosure.inCatScratchSingleCat,
    SingleCatClosure.inCatTotSingleCat, rTopCatSlice, QRegister.compose_apply,
    InterWalkRSum42Hoist.qreg_block_apply, SpecsAux.SpecMirror.systemQubits,
      SpecsAux.SpecMirror.numElectrons,
    SpecsAux.SpecMirror.electronBits, SpecsAux.SpecMirror.projectileBits]
  omega
end ConfigGidneySignalRotHoistBridge
end GidneySignalRotHoistBridge
end
end ModGidneySignalRotHoistBridge

end QuantumComputation.Specs.StoppingPowerSolution
