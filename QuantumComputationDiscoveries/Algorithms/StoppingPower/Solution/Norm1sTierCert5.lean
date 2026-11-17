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

public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.Norm1sLatHi2617
public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.Norm1sLatHi2618
public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.Norm1sLatHi2717
public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.Norm1sLatHi2917
public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.Norm1sLatHi2918
public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.Norm1sLatLo2617
public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.Norm1sLatLo2618
public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.Norm1sLatLo2717
public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.Norm1sLatLo2917
public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.Norm1sLatLo2918

set_option Elab.async false

@[expose] public section
set_option allowUnsafeReducibility true

namespace QuantumComputation.Specs.StoppingPowerSolution
open SpecsAux

section Slot3Norm1s36LatticeCert
local instance (priority := 1000000) instNeZeroTwoPow_Slot3Norm1s36LatticeCert (k : ℕ) :
    NeZero (2 ^ k) := ⟨(Nat.two_pow_pos k).ne'⟩

public section

/-
Top-level 3D Octant-Orbit Lattice Discrepancy Certificate for Parametric `(K, D)` 1-Sided
Normalized Slot-3 Momentum Oracles (`Bk = 36`, `M0 = 127`), closing the lattice discrepancy
obligations of `Slot3Norm1s262CoreSpec` across all 5 `Norm1sTier` operating tiers.
-/

namespace Slot3Norm1s36LatticeCert

section ConfigSlot3Norm1s36LatticeCert

set_option maxRecDepth 4096

open Real
open scoped BigOperators

open Slot3Norm1s36_161w (Norm1sTier)
open Slot3Norm1s36Physics80 (norm1sAcceptCountK)
open MomSlots35Slot3ProjNuclear (cRad7Computable)
open ModWrapCoarse8PureMomentum (modFold3D sumNatAbsSq shellIndex nonzeroBox3D box3D)

attribute [local irreducible] box3D nonzeroBox3D

set_option maxHeartbeats 400000 in -- Large circuit/arithmetic proof
/-- Explicit per-`ν` kernel discrepancy upper bound `E_nu` across all `Norm1sTier` operating
  points. -/
noncomputable abbrev eNuNorm1s (t : Norm1sTier) (ν : Fin 3 → ℤ) : ℝ :=
  Slot3Norm1s36LatticeBase.eNuNorm1s t ν

set_option maxHeartbeats 400000 in -- Large circuit/arithmetic proof
theorem eNuNorm1s_nonneg (t : Norm1sTier) : ∀ ν ∈ nonzeroBox3D (127 : ℤ), 0 ≤ eNuNorm1s t ν :=
    Slot3Norm1s36LatticeBase.eNuNorm1s_nonneg t

set_option maxHeartbeats 400000 in -- Large circuit/arithmetic proof
theorem eNuNorm1s_bound (t : Norm1sTier) :
    ∀ ν ∈ nonzeroBox3D (127 : ℤ),
      ∀ Δ ∈ box3D (2 * (127 : ℤ)),
        modFold3D 127 Δ = ν →
          |((2 ^ (38 - t.kBits) *
              norm1sAcceptCountK t (shellIndex ν) (sumNatAbsSq Δ) : ℕ) : ℝ) -
            ((cRad7Computable (shellIndex ν) / sumNatAbsSq Δ : ℕ) : ℝ)| ≤ eNuNorm1s t ν :=
  Slot3Norm1s36LatticeBase.eNuNorm1s_bound t

set_option maxRecDepth 2000

end ConfigSlot3Norm1s36LatticeCert

end Slot3Norm1s36LatticeCert
end
set_option exponentiation.threshold 256
end Slot3Norm1s36LatticeCert

section Slot3Prep273AndSwap3
local instance (priority := 1000000) instNeZeroTwoPow_Slot3Prep273AndSwap3 (k : ℕ) :
    NeZero (2 ^ k) := ⟨(Nat.two_pow_pos k).ne'⟩

/-!
# `273`-Wire Slot-3 State Preparation & `0`-Gate `piSwap3Core` Oracle Wrapper

Provides:
1. **Part A (`273`-Wire State Preparation)**:
   - Narrows `ShiftedMagS1.progPre48 : TempPhaseProg 321` (whose peak wire is `302 < 306 = 33 + 15 +
   258`)
     to `progPre48_306 : TempPhaseProg 306` via `PosSlots24OrbitToggleFastM.narrowTempPhaseProg`.
   - Builds `dPrep3_216_273` and `dPrep3_216Inv_273` on `(rWork : QRegister 273 n)`
     (`rMeas = rWork.slice 0 15`, `rScr = rWork.slice 15 258`, `progNotZero33` on `33 + 240 = 273`)
     at `0` `.TOFF` and `≤ 1,697` `.T` (`= tPrep216`).
2. **Part B (`0`-Gate `piSwap3Core` Conjugator & `mkSlot3Swap3MomOracle80`)**:
   - Defines involutive `piSwap3Core : QRegister (momCoreWires 80) (momCoreWires 80)` and
     `uPiSwap3Core : Unitary (2 ^ (momCoreWires 80))` swapping `[3954..3957) ↔ [4026..4029)`
     (`rfl`-identical
     to `Slot3StreamUncK35Shift3.uPiSwap3Core`), proving `piSwap3Core.embedUnitary U = unitaryConj
     uPiSwap3Core U`.
   - Wraps any `273`-wire `uCore149_216` realizer into a `MomSingleSlotOracle 80 48 3` (`mWork =
   273`,
     `tSlot = 3394 + tCore`) with `FixesLow3924` (`h3924_momCat` / `h3924_core`) and `epsIntr ≤ 3 /
     1000000`.
-/

public section

namespace Slot3Prep273AndSwap3

section ConfigSlot3Prep273AndSwap3

set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 4096

local instance (priority :=
  10) instLoc_Slot3Prep273AndSwap3_1InstNeZeroTwoPowS3Prep (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩

open Operator Matrix QProg Circuit _root_.DynamicCircuit DynCircuitExt Real LocalClassicalPerm
open scoped Matrix BigOperators Matrix.Norms.L2Operator
open SpecsAux.SpecMirror
open SpecsAux.PhaseGradCatalystCore
open PosMomSelectSandwich (slotBitProj)
open PosMomSelectDynamic (unitaryConj unitaryConj_val)
open FullSysPrepare6Slot (fullSysCoinIdx coinSelOutcome)
open FullSysMomSlots0135Concrete
open MomSlots35Slot3ProjNuclear
  (
     uPrep3 s3SamePrefix3954)
open ShiftedMagS1
  (itePos iteNeg ditePos diteNeg)
open Slot3Exact216Oracle80
  (s3QutritPairCore uQutrit3 uPrep3_216 alphaSlot3_216)
open InterWalkRSum42Hoist (FixesLow3924 h3924_momCat)
open InterWalkRSum42Hoist (preservesFeature_permutationUnitary)
open InterWalkRSum42Hoist (low3924Bits)

/-! ## Section 1: `273`-Wire State Preparation (`dPrep3_216_273` / `dPrep3_216Inv_273`) -/

theorem dynCount_seq {Var : Type} {n k : ℕ} (d₁ d₂ : DynamicCircuit Var n) (g : PrimitiveGate k) :
    (DynamicCircuit.seq d₁ d₂).count g = d₁.count g + d₂.count g := rfl

/-! ## Section 2: `0`-Gate `piSwap3Core` Conjugator & `mkSlot3Swap3MomOracle80` -/

theorem basisBits_symm_apply {k : ℕ} (f : BitAssignment k) (w : Wire k) : basisBits k
    ((basisBitsEquiv k).symm f) w = f w := congrFun ((basisBitsEquiv k).apply_symm_apply f) w

/-- Involutive wire map swapping `3954 + j ↔ 4026 + j` (`j : Fin 3`) on `momCoreWires 80 = 4034`
(`rfl`-identical to `Slot3StreamUncK35Shift3.piSwap3WireFun`). -/
def piSwap3WireFun (w : Wire (momCoreWires 80)) : Wire (momCoreWires 80) :=
  if h1 : 3954 ≤ w.val ∧ w.val < 3957 then
    ⟨w.val + 72, by
      dsimp [momCoreWires, momSelWires, SpecsAux.SpecMirror.systemQubits,
        SpecsAux.SpecMirror.numElectrons, SpecsAux.SpecMirror.electronBits,
          SpecsAux.SpecMirror.projectileBits]
      omega⟩
  else if h2 : 4026 ≤ w.val ∧ w.val < 4029 then
    ⟨w.val - 72, by have := w.isLt; omega⟩
  else w

theorem piSwap3WireFun_involutive (w : Wire (momCoreWires 80)) :
    piSwap3WireFun (piSwap3WireFun w) = w := by
  apply Fin.ext
  by_cases h1 : 3954 ≤ w.val ∧ w.val < 3957
  · have hw1 : piSwap3WireFun w = ⟨w.val + 72, by
        dsimp [momCoreWires, momSelWires, SpecsAux.SpecMirror.systemQubits,
          SpecsAux.SpecMirror.numElectrons, SpecsAux.SpecMirror.electronBits,
            SpecsAux.SpecMirror.projectileBits]
        omega⟩ := ditePos h1
    rw [hw1]
    unfold piSwap3WireFun
    rw [diteNeg (by dsimp; omega), ditePos (by dsimp; omega)]
    dsimp; omega
  · by_cases h2 : 4026 ≤ w.val ∧ w.val < 4029
    · have hw2 : piSwap3WireFun w = ⟨w.val - 72, by have := w.isLt; omega⟩ := by
        unfold piSwap3WireFun; rw [diteNeg h1, ditePos h2]
      rw [hw2]
      unfold piSwap3WireFun
      rw [ditePos (by dsimp; omega)]
      dsimp; omega
    · have hw3 : piSwap3WireFun w = w := by
        unfold piSwap3WireFun; rw [diteNeg h1, diteNeg h2]
      rw [hw3, hw3]

/-- Bundled `Equiv.Perm` on `Wire (momCoreWires 80)` swapping `[3954..3957) ↔ [4026..4029)`. -/
def piSwap3Wire : Equiv.Perm (Wire (momCoreWires 80)) where
  toFun := piSwap3WireFun
  invFun := piSwap3WireFun
  left_inv := piSwap3WireFun_involutive
  right_inv := piSwap3WireFun_involutive

theorem piSwap3Wire_fix_lt3954 (w : Wire (momCoreWires 80)) (hw : w.val < 3954) :
    piSwap3Wire w = w := by
  apply Fin.ext; change (piSwap3WireFun w).val = w.val
  unfold piSwap3WireFun; split_ifs <;> omega

/-- Basis-index permutation on `Fin (2 ^ (momCoreWires 80))` induced by `piSwap3Wire`. -/
noncomputable def piSwap3CorePerm : Equiv.Perm (Fin (2 ^ (momCoreWires 80))) :=
  let f (z : Fin (2 ^ (momCoreWires 80))) :=
    (basisBitsEquiv (momCoreWires 80)).symm fun w ↦ basisBits (momCoreWires 80) z (piSwap3Wire w)
  have hf (z) : f (f z) = z := (basisBitsEquiv (momCoreWires 80)).injective <| funext fun w ↦ by
    change basisBits _ ((basisBitsEquiv _).symm _) w = basisBits _ z w
    rw [basisBits_symm_apply, basisBits_symm_apply]
    exact congrArg (basisBits _ z) (piSwap3WireFun_involutive w)
  { toFun := f, invFun := f, left_inv := hf, right_inv := hf }

@[simp] theorem basisBits_piSwap3CorePerm (z : Fin (2 ^ (momCoreWires 80)))
    (w : Wire (momCoreWires 80)) : basisBits (momCoreWires 80) (piSwap3CorePerm z) w =
    basisBits (momCoreWires 80) z (piSwap3Wire w) := basisBits_symm_apply _ w

theorem piSwap3CorePerm_involutive (z : Fin (2 ^ (momCoreWires 80))) : piSwap3CorePerm
    (piSwap3CorePerm z) = z := piSwap3CorePerm.left_inv z

/-- Core `3-SWAP` unitary on `momCoreWires 80 = 4034` vacating `[3954..3957)`
(`rfl`-identical to `Slot3StreamUncK35Shift3.uPiSwap3Core`). -/
noncomputable def uPiSwap3Core : Unitary (2 ^ (momCoreWires 80)) :=
  Operator.permutationUnitary piSwap3CorePerm

/-- Core `3-SWAP` register permutation `piSwap3Core : QRegister (momCoreWires 80) (momCoreWires
  80)`. -/
def piSwap3Core : QRegister (momCoreWires 80) (momCoreWires 80) := ⟨piSwap3Wire.toEmbedding⟩

theorem uPiSwap3Core_apply (i j : Fin (2 ^ (momCoreWires 80))) :
    uPiSwap3Core.1 i j = if i = piSwap3CorePerm j then 1 else 0 :=
  SpecsAux.BridgeFermionicComm.permutationUnitary_apply piSwap3CorePerm i j

theorem uPiSwap3Core_self_adj : uPiSwap3Core.1ᴴ = uPiSwap3Core.1 := by
  ext i j
  rw [Matrix.conjTranspose_apply, uPiSwap3Core_apply, uPiSwap3Core_apply]
  by_cases h : j = piSwap3CorePerm i
  · subst h; rw [itePos rfl, itePos (piSwap3CorePerm_involutive i).symm, star_one]
  · have h2 : i ≠ piSwap3CorePerm j := fun hij ↦ h (by rw [hij, piSwap3CorePerm_involutive])
    rw [iteNeg h, iteNeg h2, star_zero]

@[simp] theorem uPiSwap3Core_inv : uPiSwap3Core⁻¹ = uPiSwap3Core := by
  apply Subtype.ext
  change star uPiSwap3Core.1 = uPiSwap3Core.1
  rw [Matrix.star_eq_conjTranspose, uPiSwap3Core_self_adj]

/-- Core `[0 .. 4034)` sub-register inside `momCoreWires 80 + 48`. -/
abbrev rCore0_80 : QRegister (momCoreWires 80) (momCoreWires 80 + 48) :=
  .block 0 (momCoreWires 80) (mom_zero_add_le _ 48)

/-- Catalyst `[4034 .. 4082)` sub-register inside `momCoreWires 80 + 48`. -/
abbrev rCat0_80 : QRegister 48 (momCoreWires 80 + 48) := .block (momCoreWires 80) 48 le_rfl

theorem hCoreCatDisj80 : rCore0_80.DisjointWires rCat0_80 :=
  QRegister.block_disjoint_of_le 0 (momCoreWires 80) (momCoreWires 80) 48
    (mom_zero_add_le _ 48) le_rfl (mom_zero_add_le_self _)

/-- Extended `(4034 + 48)`-wire register permutation applying `piSwap3Core` on `rCore0_80`
and identity on `rCat0_80`. -/
def piSwap3Cat : QRegister (momCoreWires 80 + 48) (momCoreWires 80 + 48) :=
  (rCore0_80.compose piSwap3Core).concat rCat0_80 (hCoreCatDisj80.compose_left piSwap3Core)

theorem piSwap3Cat_apply_val (q : Wire (momCoreWires 80 + 48)) : (piSwap3Cat q).val = if h :
    q.val < momCoreWires 80 then (piSwap3Wire ⟨q.val, h⟩).val else q.val := by
  unfold piSwap3Cat
  refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) q
  · have hiLt : (Fin.castAdd 48 i).val < momCoreWires 80 := i.isLt
    rw [QRegister.concat_apply_left, ditePos hiLt]; exact Nat.zero_add _
  · have hge : ¬ ((Fin.natAdd (momCoreWires 80) j).val < momCoreWires 80) := by
      change ¬ (momCoreWires 80 + j.val < momCoreWires 80); omega
    rw [QRegister.concat_apply_right, diteNeg hge]; rfl

theorem piSwap3Cat_involutive (q : Wire (momCoreWires 80 + 48)) :
    piSwap3Cat (piSwap3Cat q) = q := by
  apply Fin.ext
  rw [piSwap3Cat_apply_val, piSwap3Cat_apply_val]
  by_cases h : q.val < momCoreWires 80
  · rw [ditePos h]
    have h2 : (piSwap3Wire ⟨q.val, h⟩).val < momCoreWires 80 := (piSwap3Wire ⟨q.val, h⟩).isLt
    rw [ditePos h2]
    exact congrArg Fin.val (piSwap3WireFun_involutive ⟨q.val, h⟩)
  · rw [diteNeg h, diteNeg h]

theorem piSwap3Cat_extractIndex_involutive (z : Fin (2 ^ (momCoreWires 80 + 48))) :
    piSwap3Cat.extractIndex (piSwap3Cat.extractIndex z) = z := by
  apply (basisBitsEquiv _).injective; funext q
  change basisBits _ _ q = basisBits _ _ q
  rw [QRegister.basisBits_extractIndex, QRegister.basisBits_extractIndex, piSwap3Cat_involutive]

open Classical in
theorem embed_uPiSwap3Core_apply (i j : Fin (2 ^ (momCoreWires 80 + 48))) :
    (rCore0_80.embedUnitary uPiSwap3Core).1 i j =
      if i = piSwap3Cat.extractIndex j then 1 else 0 := by
  rw [QRegister.embedUnitary_val, QRegister.embedMatrix_apply_of_agreeOutside, uPiSwap3Core_apply]
  have hIff : (rCore0_80.extractIndex i = piSwap3CorePerm (rCore0_80.extractIndex j) ∧
      rCore0_80.AgreeOutside i j) ↔ i = piSwap3Cat.extractIndex j := by
    constructor
    · rintro ⟨hCore, hOut⟩
      apply (basisBitsEquiv _).injective; funext q
      change basisBits _ i q = basisBits _ (piSwap3Cat.extractIndex j) q
      rw [QRegister.basisBits_extractIndex]
      by_cases hq : q.val < momCoreWires 80
      · let w : Wire (momCoreWires 80) := ⟨q.val, hq⟩
        have hpEq : piSwap3Cat q = rCore0_80 (piSwap3Wire w) := Fin.ext (by
          rw [piSwap3Cat_apply_val, ditePos hq]
          exact (Nat.zero_add _).symm)
        rw [hpEq, show q = rCore0_80 w from Fin.ext (Nat.zero_add q.val).symm,
          ← QRegister.basisBits_extractIndex rCore0_80 i w, hCore,
          basisBits_piSwap3CorePerm, QRegister.basisBits_extractIndex rCore0_80 j]
      · have hnot : q ∉ Set.range rCore0_80.wires := fun ⟨w, hw⟩ ↦ hq <| by
          rw [← hw]
          have := w.isLt
          dsimp [rCore0_80]
          omega
        rw [show piSwap3Cat q = q from Fin.ext (by rw [piSwap3Cat_apply_val, diteNeg hq]),
          hOut q hnot]
    · rintro rfl
      refine ⟨(basisBitsEquiv _).injective (funext fun w ↦ ?_), fun q hnot ↦ ?_⟩
      · change basisBits _ _ w = basisBits _ _ w
        rw [QRegister.basisBits_extractIndex, basisBits_piSwap3CorePerm,
          QRegister.basisBits_extractIndex, QRegister.basisBits_extractIndex]
        have hwLt : (rCore0_80 w).val < momCoreWires 80 := by
          have := w.isLt
          dsimp [rCore0_80]
          omega
        refine congrArg (basisBits _ j) (Fin.ext ?_)
        rw [piSwap3Cat_apply_val, ditePos hwLt,
          show (⟨(rCore0_80 w).val, hwLt⟩ : Wire (momCoreWires 80)) = w from
            Fin.ext (Nat.zero_add w.val)]
        exact (Nat.zero_add _).symm
      · have hq : ¬ (q.val < momCoreWires 80) := fun hlt ↦
          hnot ⟨⟨q.val, hlt⟩, Fin.ext (by dsimp [rCore0_80]; omega)⟩
        rw [QRegister.basisBits_extractIndex,
          show piSwap3Cat q = q from Fin.ext (by rw [piSwap3Cat_apply_val, diteNeg hq])]
  by_cases hi : i = piSwap3Cat.extractIndex j
  · rcases hIff.mpr hi with ⟨h1, h2⟩
    rw [itePos h2, itePos h1, mul_one, itePos hi]
  · by_cases h2 : rCore0_80.AgreeOutside i j
    · have h1 : rCore0_80.extractIndex i ≠ piSwap3CorePerm (rCore0_80.extractIndex j) :=
        fun h1 ↦ hi (hIff.mp ⟨h1, h2⟩)
      rw [itePos h2, iteNeg h1, mul_one, iteNeg hi]
    · rw [iteNeg h2, mul_zero, iteNeg hi]

theorem embed_uPiSwap3Core_self_adj :
    (rCore0_80.embedUnitary uPiSwap3Core).1ᴴ = (rCore0_80.embedUnitary uPiSwap3Core).1 := by
  ext i j
  rw [Matrix.conjTranspose_apply, embed_uPiSwap3Core_apply, embed_uPiSwap3Core_apply]
  by_cases h : j = piSwap3Cat.extractIndex i
  · have h' : i = piSwap3Cat.extractIndex j := by rw [h, piSwap3Cat_extractIndex_involutive]
    rw [itePos h, itePos h', star_one]
  · have h' : i ≠ piSwap3Cat.extractIndex j :=
      fun hi ↦ h (by rw [hi, piSwap3Cat_extractIndex_involutive])
    rw [iteNeg h, iteNeg h', star_zero]

theorem uPiSwap3Core_comm_slotBitProj {w : Wire (momCoreWires 80)} (hw : w.val < 3954)
    (b : Fin 2) : uPiSwap3Core.1 * slotBitProj w b = slotBitProj w b * uPiSwap3Core.1 := by
  ext i j
  rw [slotBitProj, Matrix.mul_diagonal, Matrix.diagonal_mul, uPiSwap3Core_apply]
  by_cases hij : i = piSwap3CorePerm j
  · subst hij
    rw [basisBits_piSwap3CorePerm, piSwap3Wire_fix_lt3954 w hw]
    ring
  · simp [hij]

theorem uPiSwap3Core_comm_momCoinProj (c : Fin 8) :
    uPiSwap3Core.1 * momCoinProj 80 c = momCoinProj 80 c * uPiSwap3Core.1 := by
  rw [momCoinProj]
  exact op_comm_triple _ _ _ _
    (uPiSwap3Core_comm_slotBitProj (by dsimp [iSlot0Mom]; omega) (coinBitFin2 c 0))
    (uPiSwap3Core_comm_slotBitProj (by dsimp [iSlot1Mom]; omega) (coinBitFin2 c 1))
    (uPiSwap3Core_comm_slotBitProj (by dsimp [iSlot2Mom]; omega) (coinBitFin2 c 2))

theorem uPiSwap3Core_mul_coreHadamard_ancProj :
    let P_anc := (momAncReg 80).basisOutcomeProjector
      (coinSelOutcome (momCoin3Sel 80) (fullSysCoinIdx 3))
    uPiSwap3Core.1 * ((coreHadamardMom 80).1 * P_anc) =
      (coreHadamardMom 80).1 * P_anc := by
  intro P_anc
  let u₀ := coinSelOutcome (momCoin3Sel 80) (fullSysCoinIdx 3)
  have hP : P_anc = Matrix.diagonal (fun x ↦
      if (momAncReg 80).extractIndex x = u₀ then (1 : ℂ) else 0) :=
    QRegister.basisOutcomeProjector_eq_diagonal (momAncReg 80) u₀
  ext i g
  rw [Matrix.mul_apply, Finset.sum_eq_single (piSwap3CorePerm i)]
  · rw [uPiSwap3Core_apply, itePos (piSwap3CorePerm_involutive i).symm, one_mul,
      hP, Matrix.mul_diagonal, Matrix.mul_diagonal]
    by_cases hg : (momAncReg 80).extractIndex g = u₀
    · rw [itePos hg, mul_one, mul_one]
      let rEmpty : QRegister 0 (momCoreWires 80) := .block 0 0 (Nat.zero_le _)
      have hHad (z : Fin (2 ^ (momCoreWires 80))) : (coreHadamardMom 80).1 z g =
          if s3SamePrefix3954 z g then
            (∑ l : Fin 1, (1 : Unitary 1).1 0 l) * (((1 / √2 : ℝ) ^ 80 : ℝ) : ℂ)
          else 0 := by
        have h0 :=
          MomSlots35Slot3ProjNuclear.s3EmbedSub_mul_coreHadamard_apply
            rEmpty (fun idx ↦ Fin.elim0 idx) (1 : Unitary (2 ^ 0)) z g hg
        rw [QRegister.embedUnitary_one rEmpty, one_mul] at h0
        simpa [show rEmpty.extractIndex z = (0 : Fin (2 ^ 0)) from Fin.ext (by omega)] using h0
      have hPref : s3SamePrefix3954 (piSwap3CorePerm i) g ↔ s3SamePrefix3954 i g :=
        forall₂_congr fun w hw ↦ by rw [basisBits_piSwap3CorePerm, piSwap3Wire_fix_lt3954 w hw]
      rw [hHad (piSwap3CorePerm i), hHad i]
      exact ite_congr (propext hPref) (fun _ ↦ rfl) (fun _ ↦ rfl)
    · rw [iteNeg hg, mul_zero, mul_zero]
  · intro k _ hk
    have hne : i ≠ piSwap3CorePerm k := fun h ↦ hk (by rw [h, piSwap3CorePerm_involutive])
    rw [uPiSwap3Core_apply, iteNeg hne, zero_mul]
  · intro habs; exact absurd (Finset.mem_univ _) habs

theorem topBlock_unitaryConj_absorb {D : ℕ} (H U M : Unitary D) (P B : Operator D)
    (hPSA : Pᴴ = P) (hAbsorb : U.1 * (H.1 * P) = H.1 * P)
    (hBase : P * (unitaryConj H M).1 * P = B) : P * (unitaryConj H (unitaryConj U M)).1 * P =
    B := by
  have hL : (P * H.1ᴴ) * U.1ᴴ = P * H.1ᴴ := by
    simpa only [Matrix.conjTranspose_mul, hPSA] using congrArg Matrix.conjTranspose hAbsorb
  rw [← hBase, unitaryConj_val, unitaryConj_val, unitaryConj_val]
  calc P * (H.1ᴴ * (U.1ᴴ * M.1 * U.1) * H.1) * P
      = ((P * H.1ᴴ) * U.1ᴴ) * M.1 * (U.1 * (H.1 * P)) := by simp only [Matrix.mul_assoc]
    _ = P * (H.1ᴴ * M.1 * H.1) * P := by
          rw [hL, hAbsorb]
          simp only [Matrix.mul_assoc]

section Low3924AndWeights

open InterWalkRSum42Hoist (h3924_momCore)
open InterWalkRSum42Hoist (fixesLow3924_embedMatrix_high)

theorem fixesLow3924_uPrep3_216 : FixesLow3924 h3924_momCore (uPrep3_216 (le_refl 80)).1 := by
  have hP : FixesLow3924 h3924_momCore (uPrep3 (le_refl 80)).1 := by
    unfold uPrep3; rw [QRegister.embedUnitary_val]
    exact fixesLow3924_embedMatrix_high h3924_momCore
      Slot3Exact216Oracle80.s3Coarse33Core_80_ge_3924 _
  have hQ : ∀ j : Fin 3, FixesLow3924 h3924_momCore
      ((s3QutritPairCore (le_refl 80) j).embedUnitary
        Slot3Exact216Oracle80.cPrepQutrit2.eval).1 := fun j ↦ by
    rw [QRegister.embedUnitary_val]
    exact fixesLow3924_embedMatrix_high h3924_momCore
      (Slot3Exact216Oracle80.s3QutritPairCore_80_ge_3924 j) _
  unfold uPrep3_216 uQutrit3
  simp only [Submonoid.coe_mul]
  exact ((hQ 2).mul ((hQ 1).mul (hQ 0))).mul hP

theorem fixesLow3924_uPiSwap3Core : FixesLow3924 h3924_momCore uPiSwap3Core.1 := by
  refine preservesFeature_permutationUnitary (low3924Bits h3924_momCore) piSwap3CorePerm
    (fun j ↦ ?_)
  funext q
  dsimp only [low3924Bits]
  rw [basisBits_piSwap3CorePerm,
    piSwap3Wire_fix_lt3954 _ (lt_trans q.isLt (by decide : 3924 < 3954))]

open Classical in
theorem fixesLow3924_of_embed_rCore0 {A : Operator (2 ^ (momCoreWires 80))}
    (h : FixesLow3924 h3924_momCat (rCore0_80.embedMatrix A)) : FixesLow3924 h3924_momCore A
    := by
  intro x y hne
  let pad0 (z : Fin (2 ^ (momCoreWires 80))) : Fin (2 ^ (momCoreWires 80 + 48)) :=
    (basisBitsEquiv (momCoreWires 80 + 48)).symm
      (fun q ↦
        if hq : q.val < momCoreWires 80 then basisBits (momCoreWires 80) z ⟨q.val, hq⟩ else 0)
  have hext (z) : rCore0_80.extractIndex (pad0 z) = z :=
    (basisBitsEquiv (momCoreWires 80)).injective <| funext fun w ↦ by
      change basisBits _ _ w = basisBits _ z w
      rw [QRegister.basisBits_extractIndex]
      change basisBits _ ((basisBitsEquiv _).symm _) (rCore0_80 w) = _
      have hw : (rCore0_80 w).val < momCoreWires 80 := by
        have := w.isLt
        dsimp [rCore0_80]
        omega
      rw [basisBits_symm_apply, ditePos hw]
      exact congrArg (basisBits _ z) (Fin.ext (Nat.zero_add w.val))
  have hOut : rCore0_80.AgreeOutside (pad0 x) (pad0 y) := fun q hnot ↦ by
    have hq : ¬ (q.val < momCoreWires 80) := fun hlt ↦
      hnot ⟨⟨q.val, hlt⟩, Fin.ext (Nat.zero_add q.val)⟩
    change basisBits _ ((basisBitsEquiv _).symm _) q = basisBits _ ((basisBitsEquiv _).symm _) q
    rw [basisBits_symm_apply, basisBits_symm_apply, diteNeg hq, diteNeg hq]
  have hlow := h (pad0 x) (pad0 y) (by
    rwa [QRegister.embedMatrix_apply_of_agreeOutside, itePos hOut, mul_one, hext, hext])
  funext q
  have hq := congrFun hlow q
  dsimp only [low3924Bits] at hq ⊢
  change basisBits _ ((basisBitsEquiv _).symm _) _ =
    basisBits _ ((basisBitsEquiv _).symm _) _ at hq
  have hlt : q.val < momCoreWires 80 := lt_of_lt_of_le q.isLt h3924_momCore
  rwa [basisBits_symm_apply, basisBits_symm_apply, ditePos hlt, ditePos hlt] at hq

theorem alphaSlot3_216_eq_wIdealRat3 :
    alphaSlot3_216 = ZeroSubwireCoinPrep80.wIdealRat 3 := by
  unfold alphaSlot3_216 ZeroSubwireCoinPrep80.wIdealRat
  rw [ModWrapCoarse8PureMomentum.boost127_coarse8_w13_eq]
  norm_num

end Low3924AndWeights

end ConfigSlot3Prep273AndSwap3

end Slot3Prep273AndSwap3
end
set_option exponentiation.threshold 256
end Slot3Prep273AndSwap3

section Slot3PrepWideAndSwap3
local instance (priority := 1000000) instNeZeroTwoPow_Slot3PrepWideAndSwap3 (k : ℕ) :
    NeZero (2 ^ k) := ⟨(Nat.two_pow_pos k).ne'⟩

/-!
# Slot-3 `262`-Wire Preparation (`1,649 T`) and `piSwap3Core` Oracle Constructors

Provides two reusable Slot-3 building blocks for `mWork = 262`:

1. **Part A (`262`-Wire `1,649 T` Slot-3 State Preparation)**:
   - Lifts the `88 T` `32`-wire `PhaseQrom8BitPruned22.phaseQrom8BitPruned22` QROM phase lookup
     and `81`-AND (`324 T`) `progStage1Pruned81`, narrowing Stage 1 onto `M48_262 = 48 + 247 = 295`
     wires (`247` clean workspace wires).
   - Replaces the `250`-AND (`1,000 T`) `progStage2` with `progStage2Cz_295` (`249` `TempAnd`s =
     `996 T` on `M48_262 = 295` wires) by zeroing the `6` parked Stage-2 wires
     `{54, 55, 56, 57, 121, 126}` via `24` pure-Clifford CNOTs (`cZero6`), running the `16`-bit
     unsigned `<` comparator across `[54, 55, 56, 57, 121, 126, 285..294]`, and kicking the target
     sign directly via `.cz ⟨212⟩ ⟨294⟩` (`0 T`).
   - Replaces `progNotZero33` (`32` `TempAnd`s = `128 T`) with `progNotZero33Cz` (`31` `TempAnd`s =
     `124 T` on `33 + 33 = 66` wires, `33 ≤ 262`), giving `dCoarseGood33_262` at `1,408 T`,
     `dOaa33_262` at `1,532 T`, and `dPrep3_216_262` / `dPrep3_216Inv_262` at `1,649 T` each
     (`3,298 T` round-trip, `0 TOFF`, `mWork = 262`).

2. **Part B (`swap3PiOracle80` and Generic / Exact-`216` `262`-Wire Slot-3 Oracle Constructors)**:
   - Provides `swap3PiOracle80 : MomSingleSlotOracle 80 48 3 → MomSingleSlotOracle 80 48 3`
     conjugating any Slot-3 oracle by `Slot3Prep273AndSwap3.piSwap3Core` (`0` extra gates,
     preserving `mWork`, `tSlot`, `wSlot`, `eShift`, `epsIntr`, and `FixesLow3924`).
   - Provides generic `(K, D)` `262`-wire Slot-3 circuits (`dSlot3Raw262`, `dSlot3Swap3_262`) and
     `MomSingleSlotOracle 80 48 3` constructors (`mkSlot3RawMomOracle80_Wide`,
     `MomSingleSlotOracle 80 48 3` constructors (`mkSlot3RawMomOracle80_Wide`,
     `mkSlot3Swap3MomOracle80Gen_Wide`, `mkSlot3Swap3MomOracle80_262`,
     `mkSlot3Swap3MomOracle80OfAct149_262`) at `tSlot = 3298 + tCore`.
-/

public section

namespace Slot3PrepWideAndSwap3

section ConfigSlot3PrepWideAndSwap3

set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 4096

local instance (priority :=
  10) instLoc_Slot3PrepWideAndSwap3_1InstNeZeroTwoPowS3Pre (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩

/-! ## Section 1: `88 T` `PhaseQrom8BitPruned22` (`32`-Wire Clean Workspace) -/

namespace PhaseQrom8BitPruned22

section PhaseQrom8BitPruned22_Body

set_option backward.isDefEq.respectTransparency false
open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt HermitianMat Real
open scoped Matrix ComplexOrder MatrixOrder BigOperators Circuit.Notation

/-! ## Section 1: Private Ket & Mask Helpers -/

@[local simp] theorem pq22_basisBits_symm {q : ℕ} (β : BitAssignment q) : basisBits q
    ((basisBitsEquiv q).symm β) = β := (basisBitsEquiv q).apply_symm_apply β

/-! ## Section 2: Zero-`T` CNOT Completion of `j = 0` One-Hot Split (`11`-`TempAnd` Nibble
  Expansion) -/

/-! ## Section 3: `88 T` `phaseQrom8BitPruned22`, `1,608 T` `dOaa33Pruned`, and
  `stepBPodPruned288` -/

set_option backward.isDefEq.respectTransparency true

end PhaseQrom8BitPruned22_Body

end PhaseQrom8BitPruned22

/-! ## Section 2: `81`-AND `progStage1Pruned81` and Narrowing to `M48_262 = 295` -/

open Operator Matrix QProg Circuit _root_.DynamicCircuit DynCircuitExt Real LocalClassicalPerm
open HermitianMat
open scoped Matrix BigOperators Matrix.Norms.L2Operator ComplexOrder MatrixOrder Circuit.Notation
open SpecsAux.SpecMirror
open SpecsAux.PhaseGradCatalystCore
open PosMomSelectDynamic (unitaryConj unitaryConj_val)
open FullSysPrepare6Slot (fullSysCoinIdx coinSelOutcome)
open FullSysMomSlots0135Concrete
open _root_.QuantumComputation.Specs.StoppingPowerSolution (CliffProg cleanRem
   wire_ne_of_lt wire_ne_of_gt mul_mulVec_prog writeRegProg writeRegProg_apply_reg
   writeRegProg_apply_of_not_mem localIdxProg embedMatrix_mulVec_ket_prog
   RealizesCleanUnitary_seq_asym)
open MeasureBranchHadamardSem
  (ket bit_cases ket_TOFF eval_seq_mulVec matrix_ext_ket
   ket_projector_zero projZeroAll ket_projZeroAll projZeroAll_conjTranspose
   toffoli_eval_sq projZeroAll_eq_basisOutcomeProjector_zero RealizesCleanUnitary)
open StreamingBchComparator (PreservesStoreConst)
open MomSlot0CircuitHalf (padZeroBits phaseDiagUnitary)
open MomSlots35Slot3ProjNuclear
  (predNotZero33)
open ShiftedMagS1
open StepBBlock0 (sel149)
open Slot3Exact216Oracle80
  (uPrep3_216)
open MomSlot0LocalAndMomCombine288
  (TempCzProg withCliffAllocCz withCliffAllocCz_countTempAnd
   withTempBitCz withTempBitCz_countTempAnd)
open Slot3Prep273AndSwap3
  (uPiSwap3Core uPiSwap3Core_self_adj rCore0_80 embed_uPiSwap3Core_self_adj
    uPiSwap3Core_comm_momCoinProj uPiSwap3Core_mul_coreHadamard_ancProj topBlock_unitaryConj_absorb
    fixesLow3924_uPiSwap3Core)
open InterWalkRSum42Hoist (FixesLow3924 h3924_momCore)

/-! ## Section 3: Subspace-Predicate Clean-Workspace `TempCzProg` Realizer & `progNotZero33Cz` -/

open Classical in
/-- Orthogonal basis-subspace projector onto computational basis states satisfying `R`. -/
noncomputable def projPred {n : ℕ} (R : BitAssignment n → Prop) : Matrix (Fin (2 ^ n))
    (Fin (2 ^ n)) ℂ := Matrix.diagonal (fun z ↦ if R (basisBits n z) then 1 else 0)

open Classical in
theorem ket_projPred {n : ℕ} (R : BitAssignment n → Prop) (β : BitAssignment n) :
    (projPred R).mulVec (ket β) = if R β then ket β else 0 := by
  let z := (basisBitsEquiv n).symm β
  have hket : ket β = Pi.single z (1 : ℂ) := funext fun x ↦ by simp [z, ket, basisState]
  have hbb : basisBits n z = β := (basisBitsEquiv n).apply_symm_apply β
  rw [hket, projPred, Matrix.mulVec_single_one]
  by_cases hR : R β
  · simp only [hR, ↓reduceIte]
    funext x
    rcases eq_or_ne x z with rfl | hx
    · simp [Matrix.diagonal, hbb, hR]
    · simp [Matrix.diagonal, hx]
  · simp only [hR, ↓reduceIte]
    funext x
    rcases eq_or_ne x z with rfl | hx
    · simp [Matrix.diagonal, hbb, hR]
    · simp [Matrix.diagonal, hx]

theorem projPred_conjTranspose {n : ℕ} (R : BitAssignment n → Prop) :
    (projPred R)ᴴ = projPred R := by
  ext i j
  by_cases hij : i = j
  · subst hij
    by_cases hR : R (basisBits n i) <;> simp [projPred, Matrix.diagonal, hR]
  · simp [projPred, Matrix.diagonal, hij, Ne.symm hij]

/-- Reversible Toffoli bit-assignment update on wire `anc` controlled by `c₁, c₂`. -/
def toffStep {M : ℕ} (c₁ c₂ anc : Wire M) (γ : BitAssignment M) : BitAssignment M :=
  Function.update γ anc (γ anc + γ c₁ * γ c₂)

theorem toffStep_involutive {M : ℕ} (c₁ c₂ anc : Wire M) (h₁a : c₁ ≠ anc) (h₂a : c₂ ≠ anc)
    (γ : BitAssignment M) : toffStep c₁ c₂ anc (toffStep c₁ c₂ anc γ) = γ := by
  funext w
  by_cases hw : w = anc
  · subst hw
    simp [toffStep, Function.update_self, Function.update_of_ne h₁a,
      Function.update_of_ne h₂a, add_assoc, CharTwo.add_self_eq_zero]
  · simp [toffStep, Function.update_of_ne hw]

open Classical in
/-- General temporary-AND clean-workspace bracket for an arbitrary basis-subspace projector
`projPred R_body` (allowing `R_body` to enforce algebraic invariants that read `anc`). -/
theorem RealizesCleanUnitary.withTempAnd_projPred {Var : Type} [Fintype Var] [DecidableEq Var]
    {n : ℕ} [NeZero (2 ^ n)] (v : Var) (c₁ c₂ anc : Wire n) (h₁₂ : c₁ ≠ c₂) (h₁a : c₁ ≠ anc)
    (h₂a : c₂ ≠ anc) (R_body : BitAssignment n → Prop) (body : DynamicCircuit Var n)
    (U_body U_clean : Unitary (2 ^ n))
    (hbody : RealizesCleanUnitary v (projPred R_body) body U_body) (hket_eq : ∀ β :
    BitAssignment n, β anc = 0 → R_body (toffStep c₁ c₂ anc β) → (Circuit.TOFF c₁ c₂ anc h₁₂
    h₁a h₂a).eval.1.mulVec (U_body.1.mulVec (ket (toffStep c₁ c₂ anc β))) = U_clean.1.mulVec
    (ket β)) (hket_clean : ∀ β : BitAssignment n, β anc = 0 → R_body (toffStep c₁ c₂ anc β) →
    ((QRegister.singleton anc).basisOutcomeProjector 0).mulVec (U_clean.1.mulVec (ket β)) =
    U_clean.1.mulVec (ket β)) : RealizesCleanUnitary v
    (projPred (fun β ↦ β anc = 0 ∧ R_body (toffStep c₁ c₂ anc β))) (.seq
    (DynamicCircuit.andCompute c₁ c₂ anc h₁a h₂a) (.seq body (DynamicCircuit.andUncompute v c₁
    c₂ anc h₁₂))) U_clean := by
  let R_all : BitAssignment n → Prop := fun β ↦ β anc = 0 ∧ R_body (toffStep c₁ c₂ anc β)
  let P₀ := (QRegister.singleton anc).basisOutcomeProjector 0
  let P_body := projPred R_body
  let P_all := projPred R_all
  let T_anc := (Circuit.TOFF c₁ c₂ anc h₁₂ h₁a h₂a).eval
  let V := T_anc * U_body * T_anc
  have hP₀_herm : P₀ᴴ = P₀ := QRegister.basisOutcomeProjector_conjTranspose _ 0
  have hPall_herm : P_allᴴ = P_all := projPred_conjTranspose R_all
  have hT_sq : T_anc * T_anc = 1 := toffoli_eval_sq c₁ c₂ anc h₁₂ h₁a h₂a
  have hT_inv : T_anc⁻¹ = T_anc := inv_eq_of_mul_eq_one_left hT_sq
  have hT_adj : T_anc.1ᴴ = T_anc.1 := by
    simpa [Matrix.star_eq_conjTranspose] using congrArg Subtype.val hT_inv
  have hT_ket (γ) : T_anc.1.mulVec (ket γ) = ket (toffStep c₁ c₂ anc γ) :=
    ket_TOFF c₁ c₂ anc h₁₂ h₁a h₂a γ
  have hPall_P₀ : P_all * P₀ = P_all := matrix_ext_ket fun β ↦ by
    simp only [P_all, P₀, mul_mulVec_prog, ket_projector_zero, ket_projPred]
    by_cases h0 : β anc = 0
    · simp only [h0, ↓reduceIte, ket_projPred]
    · simp only [h0, show ¬ R_all β from fun h ↦ h0 h.1, ↓reduceIte, Matrix.mulVec_zero]
  have hswap1 : P_all * T_anc.1ᴴ = (P₀ * T_anc.1ᴴ) * P_body := by
    rw [hT_adj]
    refine matrix_ext_ket fun γ ↦ ?_
    have hinv_γ := toffStep_involutive c₁ c₂ anc h₁a h₂a γ
    simp only [P_all, P₀, P_body, mul_mulVec_prog, ket_projPred]
    by_cases hRb : R_body γ
    · simp only [hRb, ↓reduceIte, hT_ket, ket_projector_zero, ket_projPred]
      by_cases h0 : (toffStep c₁ c₂ anc γ) anc = 0
      · simp only [h0, show R_all (toffStep c₁ c₂ anc γ) from ⟨h0, by rwa [hinv_γ]⟩, ↓reduceIte]
      · simp only [h0, show ¬ R_all (toffStep c₁ c₂ anc γ) from fun h ↦ h0 h.1, ↓reduceIte]
    · simp only [hRb, ↓reduceIte, hT_ket, ket_projPred, Matrix.mulVec_zero]
      have hnot : ¬ R_all (toffStep c₁ c₂ anc γ) :=
        fun h ↦ hRb (Eq.mp (congrArg R_body hinv_γ) h.2)
      simp only [hnot, ↓reduceIte]
  have hV_eq_clean : V.1 * P_all = U_clean.1 * P_all := matrix_ext_ket fun β ↦ by
    change (T_anc.1 * U_body.1 * T_anc.1 * P_all).mulVec (ket β) =
      (U_clean.1 * P_all).mulVec (ket β)
    simp only [P_all, mul_mulVec_prog, ket_projPred]
    by_cases hRa : R_all β
    · simp only [hRa, ↓reduceIte, hT_ket]
      exact hket_eq β hRa.1 hRa.2
    · simp only [hRa, ↓reduceIte, Matrix.mulVec_zero]
  have hU_clean_P₀ : P₀ * (U_clean.1 * P_all) = U_clean.1 * P_all := matrix_ext_ket fun β ↦ by
    simp only [P_all, mul_mulVec_prog, ket_projPred]
    by_cases hRa : R_all β
    · simp only [hRa, ↓reduceIte]
      exact hket_clean β hRa.1 hRa.2
    · simp only [hRa, ↓reduceIte, Matrix.mulVec_zero]
  have hclean_adj : P_all * U_clean.1ᴴ * P₀ = P_all * U_clean.1ᴴ := by
    simpa [conjTranspose_mul, hP₀_herm, hPall_herm, ← Matrix.mul_assoc] using
      congrArg conjTranspose hU_clean_P₀
  have hU_eq : U_body * T_anc = T_anc * V := by
    dsimp [V]
    rw [← mul_assoc, ← mul_assoc, hT_sq, one_mul]
  refine ⟨fun Ψ _ σ val ↦ ?_, fun Θ hΘ σ ↦ ?_⟩
  · simp only [DynamicCircuit.andCompute, DynamicCircuit.compile_seq,
      DynamicCircuit.compile_circuit, wp_qSeq, wp_circuit_compile_compat, wpQAssignCompat]
    congr 1
    exact congrArg (fun x ↦ (x : Observable (Fin (2 ^ n))))
      (hbody.1 (wp (DynamicCircuit.andUncompute v c₁ c₂ anc h₁₂).compile Ψ)
        (fun σ' v' ↦ wp_andUncompute_update_self v c₁ c₂ anc h₁₂ Ψ σ' v') σ val)
  · let Ψ := wp (DynamicCircuit.andUncompute v c₁ c₂ anc h₁₂).compile Θ
    have hΨ_inv (σ' v') : Ψ (Function.update σ' v v') = Ψ σ' :=
      wp_andUncompute_update_self v c₁ c₂ anc h₁₂ Θ σ' v'
    have hstep1 : ((wp (.qSeq (DynamicCircuit.andCompute (Var := Var) c₁ c₂ anc h₁a h₂a).compile
        (.qSeq body.compile (DynamicCircuit.andUncompute v c₁ c₂ anc h₁₂).compile)) Θ σ).1).conj
        P₀ = ((wpQAssignCompat T_anc (wp body.compile Ψ) σ).1).conj P₀ :=
      congrArg Subtype.val <| congrFun
        (restrictToZeroAncilla_wp_andCompute_seq_compat c₁ c₂ anc h₁₂ h₁a h₂a
          (.qSeq body.compile (DynamicCircuit.andUncompute v c₁ c₂ anc h₁₂).compile) Θ) σ
    have hstep_uncomp : ((wpQAssignCompat T_anc Ψ σ).1).conj P₀ = (Θ σ).1.conj P₀ :=
      congrArg Subtype.val <| congrFun
        (restrictAssertionToZeroAncilla_wpQAssign_toffoli_wp_andUncompute_of_update_eq
          v c₁ c₂ anc h₁₂ h₁a h₂a Θ hΘ) σ
    change ((wp (.qSeq (DynamicCircuit.andCompute (Var := Var) c₁ c₂ anc h₁a h₂a).compile
        (.qSeq body.compile (DynamicCircuit.andUncompute v c₁ c₂ anc h₁₂).compile)) Θ σ).1).conj
      P_all = ((wpQAssignCompat U_clean Θ σ).1).conj P_all
    rw [← hPall_P₀, ← HermitianMat.conj_conj, hstep1]
    simp only [wpQAssignCompat, qAssignObsMap, Observable.conj_coe, Unitary.coe_star,
      Matrix.star_eq_conjTranspose, HermitianMat.conj_conj]
    rw [← Matrix.mul_assoc P_all P₀, hPall_P₀, hswap1, ← HermitianMat.conj_conj,
      hbody.2 Ψ hΨ_inv σ]
    simp only [wpQAssignCompat, qAssignObsMap, Observable.conj_coe, Unitary.coe_star,
      Matrix.star_eq_conjTranspose, HermitianMat.conj_conj]
    have hprod_adj :
        (P₀ * T_anc.1ᴴ) * (P_body * U_body.1ᴴ) = (P_all * U_clean.1ᴴ * P₀) * T_anc.1ᴴ := by
      have h1 : (P₀ * T_anc.1ᴴ) * (P_body * U_body.1ᴴ) = P_all * (U_body * T_anc).1ᴴ := by
        rw [Submonoid.coe_mul, conjTranspose_mul, ← Matrix.mul_assoc, ← hswap1, Matrix.mul_assoc]
      have h2 : P_all * V.1ᴴ = P_all * U_clean.1ᴴ := by
        simpa [conjTranspose_mul, hPall_herm] using congrArg conjTranspose hV_eq_clean
      rw [h1, hU_eq, Submonoid.coe_mul, conjTranspose_mul, ← Matrix.mul_assoc, h2, hclean_adj]
    have hmid : (Ψ σ).1.conj (P₀ * T_anc.1ᴴ) = (Θ σ).1.conj P₀ := by
      simpa [wpQAssignCompat, qAssignObsMap, Observable.conj_coe, Unitary.coe_star,
        Matrix.star_eq_conjTranspose, HermitianMat.conj_conj] using hstep_uncomp
    rw [hprod_adj, Matrix.mul_assoc (P_all * U_clean.1ᴴ) P₀ T_anc.1ᴴ, ← HermitianMat.conj_conj,
      hmid, HermitianMat.conj_conj, hclean_adj]

theorem eval_onRegister_czProg_ket {M n : ℕ} (rComb : QRegister M n) (p : TempCzProg M)
    (β : BitAssignment n) : ((p.onRegister rComb).toToffCircuit).eval.1.mulVec (ket β) =
    ((-1 : ℂ) ^ (p.evalSign (fun idx ↦ β (rComb idx))).val) • ket
    (writeRegProg β rComb (p.evalBits (fun idx ↦ β (rComb idx)))) := by
  let γ : BitAssignment M := fun idx ↦ β (rComb idx)
  rw [p.onRegister_toToffCircuit_eval rComb, Circuit.eval_onRegister,
    QRegister.embedUnitary_val, embedMatrix_mulVec_ket_prog]
  have hloc : localIdxProg rComb β = (basisBitsEquiv M).symm γ := rfl
  rw [hloc]
  have hcol : ∀ l : Fin (2 ^ M), (p.toToffCircuit).eval.1 l ((basisBitsEquiv M).symm γ) = if l
      = (basisBitsEquiv M).symm (p.evalBits γ) then ((-1 : ℂ) ^ (p.evalSign γ).val) else 0
      := by
    intro l
    have hk := congrFun (p.toToffCircuit_eval_ket γ) l
    simpa [ket, basisState, Matrix.mulVec_single_one, Pi.single_apply, eq_comm] using hk
  simp_rw [hcol, ite_smul, zero_smul]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  have hbb : basisBits M ((basisBitsEquiv M).symm (p.evalBits γ)) = p.evalBits γ :=
    (basisBitsEquiv M).apply_symm_apply _
  rw [hbb]

theorem PreservesStoreConst_toDyn_cz {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    (v : Var) : ∀ p : TempCzProg n, PreservesStoreConst (p.toDyn v)
  | .nil => PreservesStoreConst.circuit _
  | .cliff _ => PreservesStoreConst.circuit _
  | .cz _ _ _ => PreservesStoreConst.circuit _
  | .seq p₁ p₂ =>
      PreservesStoreConst.seq (PreservesStoreConst_toDyn_cz v p₁) (PreservesStoreConst_toDyn_cz v
        p₂)
  | .tempAnd c₁ c₂ anc h₁₂ _ _ body =>
      PreservesStoreConst.seq (PreservesStoreConst.circuit _)
        (PreservesStoreConst.seq (PreservesStoreConst_toDyn_cz v body)
          (PreservesStoreConst.andUncompute v c₁ c₂ anc h₁₂))

/-- Subspace-predicate validity certificate for `p : TempCzProg M` entering on states satisfying
`Q : BitAssignment M → Prop` (supporting clean recycling of algebraically zeroed wires). -/
def ValidCleanPredCz {M : ℕ} : (BitAssignment M → Prop) → TempCzProg M → Prop
  | _, .nil => True
  | _, .cliff _ => True
  | _, .cz _ _ _ => True
  | Q, .seq p₁ p₂ =>
      ∃ Q_mid : BitAssignment M → Prop,
        ValidCleanPredCz Q p₁ ∧ ValidCleanPredCz Q_mid p₂ ∧
          (∀ γ : BitAssignment M, Q γ → Q_mid (p₁.evalBits γ))
  | Q, .tempAnd c₁ c₂ anc _ _ _ body =>
      (∀ γ : BitAssignment M, Q γ → γ anc = 0) ∧
        ValidCleanPredCz (fun β₁ ↦ Q (toffStep c₁ c₂ anc β₁)) body ∧
          (∀ β₁ : BitAssignment M, Q (toffStep c₁ c₂ anc β₁) →
            body.evalBits β₁ c₁ = β₁ c₁ ∧
              body.evalBits β₁ c₂ = β₁ c₂ ∧
              body.evalBits β₁ anc = β₁ anc)

theorem validCleanPredCz_mono {M : ℕ} :
    ∀ {p : TempCzProg M} {Q₁ Q₂ : BitAssignment M → Prop},
      (∀ γ, Q₁ γ → Q₂ γ) → ValidCleanPredCz Q₂ p → ValidCleanPredCz Q₁ p
  | .nil, _, _, _, _ => trivial
  | .cliff _, _, _, _, _ => trivial
  | .cz _ _ _, _, _, _, _ => trivial
  | .seq _ _, _, _, himp, ⟨Q_mid, hv₁, hv₂, hpres⟩ =>
      ⟨Q_mid, validCleanPredCz_mono himp hv₁, hv₂, fun γ hγ ↦ hpres γ (himp γ hγ)⟩
  | .tempAnd _ _ _ _ _ _ _, _, _, himp, ⟨hanc, hvB, hpB⟩ =>
      ⟨fun γ hγ ↦ hanc γ (himp γ hγ),
       validCleanPredCz_mono (fun _ h₁ ↦ himp _ h₁) hvB,
       fun β₁ h₁ ↦ hpB β₁ (himp _ h₁)⟩

theorem realizes_of_validCleanPredCz
    {Var : Type} [Fintype Var] [DecidableEq Var] {M n : ℕ} [NeZero (2 ^ n)]
    (v : Var) (rComb : QRegister M n) :
    ∀ (p : TempCzProg M) (Q : BitAssignment M → Prop),
      ValidCleanPredCz Q p →
      RealizesCleanUnitary v (projPred (fun β : BitAssignment n ↦ Q (fun idx ↦ β (rComb idx))))
        ((p.onRegister rComb).toDyn v) (((p.onRegister rComb).toToffCircuit).eval)
  | .nil, _, _ => RealizesCleanUnitary.circuit v _ _
  | .cliff _, _, _ => RealizesCleanUnitary.circuit v _ _
  | .cz _ _ _, _, _ => RealizesCleanUnitary.circuit v _ _
  | .seq p₁ p₂, Q, ⟨Q_mid, hv₁, hv₂, hpres⟩ => by
      let P₁ := projPred (fun β : BitAssignment n ↦ Q (fun idx ↦ β (rComb idx)))
      let P₂ := projPred (fun β : BitAssignment n ↦ Q_mid (fun idx ↦ β (rComb idx)))
      have hP₁ : P₁ᴴ = P₁ := projPred_conjTranspose _
      have hP₂ : P₂ᴴ = P₂ := projPred_conjTranspose _
      have ih₁ := realizes_of_validCleanPredCz v rComb p₁ Q hv₁
      have ih₂ := realizes_of_validCleanPredCz v rComb p₂ Q_mid hv₂
      have hclean : P₂ * (((p₁.onRegister rComb).toToffCircuit).eval.1 * P₁) =
          ((p₁.onRegister rComb).toToffCircuit).eval.1 * P₁ := by
        apply matrix_ext_ket
        intro β
        simp only [P₁, P₂, mul_mulVec_prog, ket_projPred]
        by_cases hQ : Q (fun idx ↦ β (rComb idx))
        · simp only [hQ, ↓reduceIte, eval_onRegister_czProg_ket, Matrix.mulVec_smul, ket_projPred]
          have hwr : (fun idx ↦ writeRegProg β rComb (p₁.evalBits (fun idx ↦ β (rComb idx)))
              (rComb idx)) = p₁.evalBits (fun idx ↦ β (rComb idx)) :=
            funext fun _ ↦ writeRegProg_apply_reg _ _ _ _
          simp only [hwr, hpres _ hQ, ↓reduceIte]
        · simp only [hQ, ↓reduceIte, Matrix.mulVec_zero]
      have heq : (p₂.onRegister rComb).toToffCircuit.eval *
          (p₁.onRegister rComb).toToffCircuit.eval =
          ((TempCzProg.seq p₁ p₂).onRegister rComb).toToffCircuit.eval := by
        simp [TempCzProg.onRegister, TempCzProg.toToffCircuit, Circuit.eval_seq]
      simpa [TempCzProg.onRegister, TempCzProg.toDyn, heq] using
        RealizesCleanUnitary_seq_asym hP₁ hP₂ ih₁ ih₂ hclean
  | .tempAnd c₁ c₂ anc h₁₂ h₁a h₂a body, Q, ⟨hanc0, hvBody, hpresBody⟩ => by
      let Q₁ : BitAssignment M → Prop := fun β₁ ↦ Q (toffStep c₁ c₂ anc β₁)
      have ihBody := realizes_of_validCleanPredCz v rComb body Q₁ hvBody
      let U_body := ((body.onRegister rComb).toToffCircuit).eval
      let U_clean :=
        (((TempCzProg.tempAnd c₁ c₂ anc h₁₂ h₁a h₂a body).onRegister rComb).toToffCircuit).eval
      have hpull : ∀ β : BitAssignment n,
          (fun idx ↦ toffStep (rComb c₁) (rComb c₂) (rComb anc) β (rComb idx)) =
            toffStep c₁ c₂ anc (fun idx ↦ β (rComb idx)) := by
        intro β
        funext idx
        by_cases hia : idx = anc
        · subst hia
          simp [toffStep, Function.update_self]
        · have hrne : rComb idx ≠ rComb anc := rComb.wires.injective.ne hia
          simp [toffStep, Function.update_of_ne hia, Function.update_of_ne hrne]
      have hstep := RealizesCleanUnitary.withTempAnd_projPred
        v (rComb c₁) (rComb c₂) (rComb anc)
        (rComb.wires.injective.ne h₁₂) (rComb.wires.injective.ne h₁a) (rComb.wires.injective.ne h₂a)
        (fun β : BitAssignment n ↦ Q₁ (fun idx ↦ β (rComb idx)))
        ((body.onRegister rComb).toDyn v) U_body U_clean ihBody
        (by
          intro β _ _
          dsimp only [U_clean, U_body, TempCzProg.onRegister, TempCzProg.toToffCircuit, toffStep]
          simp only [eval_seq_mulVec, ket_TOFF])
        (by
          intro β hβ_anc0 hR₁
          let γ : BitAssignment M := fun idx ↦ β (rComb idx)
          let β₁ : BitAssignment M := toffStep c₁ c₂ anc γ
          have hQ₁ : Q₁ β₁ := by
            dsimp only [Q₁, β₁, γ] at hR₁ ⊢
            rwa [hpull β] at hR₁
          obtain ⟨hc₁, hc₂, ha⟩ := hpresBody β₁ hQ₁
          have hfinal_anc :
              (TempCzProg.tempAnd c₁ c₂ anc h₁₂ h₁a h₂a body).evalBits γ anc = 0 := by
            dsimp only [TempCzProg.evalBits]
            change Function.update (body.evalBits β₁) anc
              (body.evalBits β₁ anc + body.evalBits β₁ c₁ * body.evalBits β₁ c₂) anc = 0
            rw [Function.update_self, ha, hc₁, hc₂]
            dsimp only [β₁, toffStep]
            have hγ0 : γ anc = 0 := hβ_anc0
            simp [hγ0, Function.update_self, Function.update_of_ne h₁a,
              Function.update_of_ne h₂a, CharTwo.add_self_eq_zero]
          rw [show U_clean.1.mulVec (ket β) = _ from
              eval_onRegister_czProg_ket rComb
                (TempCzProg.tempAnd c₁ c₂ anc h₁₂ h₁a h₂a body) β,
            Matrix.mulVec_smul, ket_projector_zero, writeRegProg_apply_reg, hfinal_anc]
          simp)
      have hP_eq : projPred (fun β : BitAssignment n ↦ β (rComb anc) = 0 ∧ Q₁ (fun idx ↦
          toffStep (rComb c₁) (rComb c₂) (rComb anc) β (rComb idx))) =
          projPred (fun β : BitAssignment n ↦ Q (fun idx ↦ β (rComb idx))) :=
        congrArg projPred <| funext fun β ↦ propext <| by
          rw [hpull β]
          dsimp only [Q₁]
          rw [toffStep_involutive c₁ c₂ anc h₁a h₂a]
          exact ⟨fun h ↦ h.2, fun hQ ↦ ⟨hanc0 _ hQ, hQ⟩⟩
      simpa [U_clean, TempCzProg.onRegister, TempCzProg.toDyn, hP_eq] using hstep

open Classical in
/-- One-call bridge from a `ValidCleanPredCz (cleanRem (kAct + mClean) mClean)` `TempCzProg` to
`DynamicCircuit.RealizesEmbeddedUnitaryWithCleanWorkspace rAct rWork (phaseDiagUnitary pred)`. -/
theorem realizes_phaseDiagUnitary_cleanWorkspace_cz
    {Var : Type} [Fintype Var] [DecidableEq Var] {n kAct mClean mWork : ℕ} [NeZero (2 ^ n)]
    (v : Var) (rAct : QRegister kAct n) (rWork : QRegister mWork n)
    (hdisj : rAct.DisjointWires rWork) (hw_len : mClean ≤ mWork)
    (pred : BitAssignment kAct → ZMod 2)
    (p : TempCzProg (kAct + mClean))
    (hValid : ValidCleanPredCz (cleanRem (kAct + mClean) mClean) p)
    (hBits : ∀ α : BitAssignment kAct, p.evalBits (padZeroBits α) = padZeroBits α)
    (hSign : ∀ α : BitAssignment kAct, p.evalSign (padZeroBits α) = pred α) :
    let rSub : QRegister mClean n := rWork.slice 0 mClean (by omega)
    let rComb : QRegister (kAct + mClean) n := rAct.concat rSub (hdisj.compose_right _)
    let dyn := (p.onRegister rComb).toDyn v
    DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace rAct rWork (phaseDiagUnitary pred) dyn ∧
      dyn.count PrimitiveGate.TOFF = 0 ∧
      dyn.count PrimitiveGate.T = 4 * p.countTempAnd := by
  intro rSub rComb dyn
  refine ⟨?_, TempCzProg.toDyn_count_toff v _, by
    rw [TempCzProg.toDyn_count_t, TempCzProg.onRegister_countTempAnd]⟩
  have hSmall := realizes_of_validCleanPredCz v rComb p (cleanRem (kAct + mClean) mClean) hValid
  let P_small := projPred (fun β : BitAssignment n ↦
    cleanRem (kAct + mClean) mClean (fun idx ↦ β (rComb idx)))
  let P_work := projZeroAll mWork rWork.wires
  have hPs : P_smallᴴ = P_small := projPred_conjTranspose _
  have hPw : P_workᴴ = P_work := projZeroAll_conjTranspose mWork _
  have hj' (j : Fin mClean) : rSub j = rWork ⟨j.val, by omega⟩ := by
    rw [QRegister.slice_apply]
    exact congrArg rWork (Fin.ext (Nat.zero_add j.val))
  have hsub : P_small * P_work = P_work := matrix_ext_ket fun β ↦ by
    simp only [P_small, P_work, mul_mulVec_prog, ket_projZeroAll]
    by_cases hw : ∀ i : Fin mWork, β (rWork i) = 0
    · have hcl : cleanRem (kAct + mClean) mClean (fun idx ↦ β (rComb idx)) := fun w hw_lo ↦ by
        rw [show w = Fin.natAdd kAct ⟨w.val - kAct, by have := w.isLt; omega⟩ from
          Fin.ext (by dsimp; omega)]
        dsimp only [rComb]
        rw [QRegister.concat_apply_right, hj']
        exact hw _
      simp only [hw, imp_true_iff, ↓reduceIte, ket_projPred, hcl]
    · simp [hw]
  have hUeq : ((p.onRegister rComb).toToffCircuit).eval.1 * P_work =
      (rAct.embedUnitary (phaseDiagUnitary pred)).1 * P_work := matrix_ext_ket fun β ↦ by
    simp only [P_work, mul_mulVec_prog, ket_projZeroAll]
    by_cases hw : ∀ i : Fin mWork, β (rWork i) = 0
    · simp only [hw, imp_true_iff, ↓reduceIte, eval_onRegister_czProg_ket]
      let α : BitAssignment kAct := fun i ↦ β (rAct i)
      have hpad : (fun idx ↦ β (rComb idx)) = padZeroBits α := funext fun idx ↦
        Fin.addCases
          (fun i ↦ by
            dsimp only [rComb, padZeroBits, α]
            simp)
          (fun j ↦ by
            dsimp only [rComb, padZeroBits]
            rw [QRegister.concat_apply_right, Fin.addCases_right, hj']
            exact hw _)
          idx
      have hwComb : writeRegProg β rComb (padZeroBits α) = β := funext fun w ↦ by
        by_cases hmem : w ∈ Set.range rComb.wires
        · obtain ⟨idx, rfl⟩ := hmem
          rw [writeRegProg_apply_reg, ← hpad]
        · exact writeRegProg_apply_of_not_mem _ _ _ _ hmem
      have hwAct : writeRegProg β rAct α = β := funext fun w ↦ by
        by_cases hmem : w ∈ Set.range rAct.wires
        · obtain ⟨i, rfl⟩ := hmem
          exact writeRegProg_apply_reg _ _ _ _
        · exact writeRegProg_apply_of_not_mem _ _ _ _ hmem
      have hbb : basisBits kAct (localIdxProg rAct β) = α :=
        (basisBitsEquiv kAct).apply_symm_apply α
      rw [hpad, hBits α, hSign α, hwComb, QRegister.embedUnitary_val, embedMatrix_mulVec_ket_prog]
      have hEvalAct (l : Fin (2 ^ kAct)) : (phaseDiagUnitary pred).1 l (localIdxProg rAct β) =
          if l = localIdxProg rAct β then ((-1 : ℂ) ^ (pred α).val) else 0 := by
        rcases eq_or_ne l (localIdxProg rAct β) with rfl | hl
        · simp [phaseDiagUnitary, hbb]
        · simp [phaseDiagUnitary, hl]
      simp_rw [hEvalAct, ite_smul, zero_smul]
      simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, hbb, hwAct]
    · simp [hw]
  have hTarget :=
    RealizesCleanUnitary.congr_unitary hPw (RealizesCleanUnitary.mono_proj hPs hPw hsub hSmall) hUeq
  intro M_obs
  obtain ⟨M_out, hM_out⟩ := PreservesStoreConst_toDyn_cz v (p.onRegister rComb) M_obs
  refine ⟨M_out, hM_out, ?_⟩
  have hconj := hTarget.2 (fun _ ↦ M_obs) (fun _ _ ↦ rfl) default
  rw [← show wp dyn.compile (fun _ ↦ M_obs) default = M_out from congrFun hM_out default,
    ← projZeroAll_eq_basisOutcomeProjector_zero rWork]
  simpa [P_work, hPw, wpQAssignCompat, qAssignObsMap, Observable.conj_coe, Unitary.coe_star,
    Matrix.star_eq_conjTranspose, HermitianMat.conj_apply_mat, Matrix.mul_assoc] using
    congrArg Subtype.val hconj

/-- Compositional `ScopedCzPredBlock` specification wrapping an inner `leaf : TempCzProg M`. -/
structure ScopedCzPredBlock (M : ℕ) (Q : BitAssignment M → Prop)
    (setup : BitAssignment M → BitAssignment M) (leaf p : TempCzProg M) : Prop where
  valid : ValidCleanPredCz Q p
  bits : ∀ β : BitAssignment M, Q β → p.evalBits β = β
  sign : ∀ β : BitAssignment M, Q β → p.evalSign β = leaf.evalSign (setup β)

theorem ScopedCzPredBlock.cz_leaf {M : ℕ} (Q : BitAssignment M → Prop) (c t : Wire M)
    (hct : c ≠ t) : ScopedCzPredBlock M Q id (.cz c t hct) (.cz c t hct) :=
    ⟨trivial, fun _ _ ↦ rfl, fun _ _ ↦ rfl⟩

theorem ScopedCzPredBlock.withCliffAllocCz_block {M : ℕ}
    {Q Q_in : BitAssignment M → Prop}
    {sBody : BitAssignment M → BitAssignment M} {leaf body : TempCzProg M}
    (c : CliffProg M)
    (hQ : ∀ β, Q β → Q_in (c.eval β))
    (hBody : ScopedCzPredBlock M Q_in sBody leaf body) :
    ScopedCzPredBlock M Q (sBody ∘ c.eval) leaf (withCliffAllocCz c body) where
  valid :=
    ⟨Q_in, trivial,
      ⟨fun _ ↦ True, hBody.valid, trivial, fun _ _ ↦ trivial⟩,
      hQ⟩
  bits β hβ := by
    dsimp [withCliffAllocCz, TempCzProg.evalBits]
    rw [hBody.bits (c.eval β) (hQ β hβ), c.inv_eval]
  sign β hβ := by
    dsimp [withCliffAllocCz, TempCzProg.evalSign, TempCzProg.evalBits]
    rw [zero_add, add_zero, hBody.sign (c.eval β) (hQ β hβ)]

theorem ScopedCzPredBlock.withTempBitCz_block {M : ℕ} {Q Q_in : BitAssignment M → Prop}
    (c₁ c₂ anc : Wire M) (h₁₂ : c₁ ≠ c₂) (h₁a : c₁ ≠ anc) (h₂a : c₂ ≠ anc)
    (hanc0 : ∀ β, Q β → β anc = 0)
    (hQ : ∀ β, Q β → Q_in (Function.update β anc (β c₁ * β c₂)))
    {sBody : BitAssignment M → BitAssignment M} {leaf body : TempCzProg M}
    (hBody : ScopedCzPredBlock M Q_in sBody leaf body) : ScopedCzPredBlock M Q
    (fun β ↦ sBody (Function.update β anc (β c₁ * β c₂))) leaf
    (withTempBitCz c₁ c₂ anc h₁₂ h₁a h₂a body) := by
  have hImp (β₁) (h₀ : Q (toffStep c₁ c₂ anc β₁)) : Q_in β₁ := by
    let β := toffStep c₁ c₂ anc β₁
    rw [← toffStep_involutive c₁ c₂ anc h₁a h₂a β₁]
    change Q_in (Function.update β anc (β anc + β c₁ * β c₂))
    rw [hanc0 β h₀, zero_add]
    exact hQ β h₀
  refine ⟨⟨hanc0, validCleanPredCz_mono hImp hBody.valid, fun β₁ h₀ ↦ ?_⟩,
    fun β hβ ↦ ?_, fun β hβ ↦ ?_⟩
  · have hb := hBody.bits β₁ (hImp β₁ h₀)
    exact ⟨congrFun hb c₁, congrFun hb c₂, congrFun hb anc⟩
  · dsimp [withTempBitCz, TempCzProg.evalBits]
    let β₁ := Function.update β anc (β anc + β c₁ * β c₂)
    have hβ₁_eq : β₁ = Function.update β anc (β c₁ * β c₂) := by
      dsimp [β₁]
      rw [hanc0 β hβ, zero_add]
    change Function.update (body.evalBits β₁) anc
      (body.evalBits β₁ anc + body.evalBits β₁ c₁ * body.evalBits β₁ c₂) = β
    rw [hBody.bits β₁ (hβ₁_eq ▸ hQ β hβ)]
    exact toffStep_involutive c₁ c₂ anc h₁a h₂a β
  · dsimp [withTempBitCz, TempCzProg.evalSign]
    rw [hanc0 β hβ, zero_add, hBody.sign _ (hQ β hβ)]

theorem ScopedCzPredBlock.seq_spec {M : ℕ} {Q : BitAssignment M → Prop}
    {s₁ s₂ : BitAssignment M → BitAssignment M} {leaf₁ leaf₂ p₁ p₂ : TempCzProg M}
    (h₁ : ScopedCzPredBlock M Q s₁ leaf₁ p₁) (h₂ : ScopedCzPredBlock M Q s₂ leaf₂ p₂) :
    ValidCleanPredCz Q (.seq p₁ p₂) ∧ (∀ β, Q β → (TempCzProg.seq p₁ p₂).evalBits β = β) ∧ (∀
    β, Q β → (TempCzProg.seq p₁ p₂).evalSign β = leaf₁.evalSign (s₁ β) + leaf₂.evalSign (s₂
    β)) :=
  ⟨⟨Q, h₁.valid, h₂.valid, fun γ hγ ↦ by rw [h₁.bits γ hγ]; exact hγ⟩,
   fun β hβ ↦ by dsimp [TempCzProg.evalBits]; rw [h₁.bits β hβ, h₂.bits β hβ],
   fun β hβ ↦ by dsimp [TempCzProg.evalSign]; rw [h₁.sign β hβ, h₁.bits β hβ, h₂.sign β hβ]⟩

/-- Output wire of a `K`-step AND-chain starting at `cur` from accumulator `acc`. -/
def andChainOut {M : ℕ} : (K : ℕ) → (cur : ℕ) → (hcur : cur + K ≤ M) → Wire M → Wire M
  | 0, _, _, acc => acc
  | K + 1, cur, _, _ => andChainOut K (cur + 1) (by omega) ⟨cur, by omega⟩

/-- `K`-step AND-chain for `TempCzProg M` (`K` `TempAnd`s = `4 * K` `.T`), passing the output wire
`andChainOut K cur hcur acc` to `body`. -/
def withAndChainCz {M : ℕ} :
    (K : ℕ) → (cur : ℕ) → (hcur : cur + K ≤ M) →
    (acc : Wire M) → (hacc : acc.val < cur) →
    (ctrls : Fin K → Wire M) → (hctrls : ∀ i, (ctrls i).val < cur) →
    (hne0 : ∀ i, acc ≠ ctrls i) →
    (body : Wire M → TempCzProg M) → TempCzProg M
  | 0, _, _, acc, _, _, _, _, body => body acc
  | K + 1, cur, hcur, acc, _, ctrls, hctrls, hne0, body =>
      let wNext : Wire M := ⟨cur, by omega⟩
      withTempBitCz acc (ctrls 0) wNext (hne0 0)
        (wire_ne_of_lt (by dsimp [wNext]; omega))
        (wire_ne_of_lt (by have := hctrls 0; dsimp [wNext]; omega))
        (withAndChainCz K (cur + 1) (by omega) wNext (by dsimp [wNext]; omega)
          (fun i ↦ ctrls i.succ) (fun i ↦ by have := hctrls i.succ; omega)
          (fun i ↦ wire_ne_of_gt (by have := hctrls i.succ; dsimp [wNext]; omega))
          body)

@[local simp] theorem withAndChainCz_countTempAnd {M : ℕ} :
    ∀ (K : ℕ) (cur : ℕ) (hcur : cur + K ≤ M)
      (acc : Wire M) (hacc : acc.val < cur)
      (ctrls : Fin K → Wire M) (hctrls : ∀ i, (ctrls i).val < cur)
      (hne0 : ∀ i, acc ≠ ctrls i)
      (body : Wire M → TempCzProg M)
      (cB : ℕ), (∀ out, (body out).countTempAnd = cB) →
      (withAndChainCz K cur hcur acc hacc ctrls hctrls hne0 body).countTempAnd = K + cB
  | 0, _, _, acc, _, _, _, _, body, cB, hcB => by
      simpa [withAndChainCz] using hcB acc
  | K + 1, cur, _, acc, _, ctrls, hctrls, hne0, body, cB, hcB => by
      dsimp only [withAndChainCz]
      rw [withTempBitCz_countTempAnd,
        withAndChainCz_countTempAnd K (cur + 1) (by omega) _ _ _ _ _ body cB hcB]
      omega

theorem withAndChainCz_scoped {M : ℕ}
    {leaf : TempCzProg M}
    {sLeaf : BitAssignment M → BitAssignment M}
    {body : Wire M → TempCzProg M} :
    ∀ (K : ℕ) (cur : ℕ) (hcur : cur + K ≤ M)
      (acc : Wire M) (hacc : acc.val < cur)
      (ctrls : Fin K → Wire M) (hctrls : ∀ i, (ctrls i).val < cur)
      (hne0 : ∀ i, acc ≠ ctrls i),
      ScopedCzPredBlock M (cleanRem M (M - (cur + K))) sLeaf leaf
        (body (andChainOut K cur hcur acc)) →
      ∃ sChain : BitAssignment M → BitAssignment M,
        ScopedCzPredBlock M (cleanRem M (M - cur)) (sLeaf ∘ sChain) leaf
          (withAndChainCz K cur hcur acc hacc ctrls hctrls hne0 body) ∧
        (∀ β : BitAssignment M, cleanRem M (M - cur) β →
          (∀ w : Wire M, w.val < cur → sChain β w = β w) ∧
          sChain β (andChainOut K cur hcur acc) = β acc * ∏ i : Fin K, β (ctrls i))
  | 0, cur, _, acc, _, _, _, _, hBody =>
      ⟨id, by simpa [andChainOut, withAndChainCz] using hBody,
       fun β _ ↦ ⟨fun _ _ ↦ rfl, by simp [andChainOut]⟩⟩
  | K + 1, cur, hcur, acc, _, ctrls, hctrls, hne0, hBody => by
      let wNext : Wire M := ⟨cur, by omega⟩
      have heq : cur + 1 + K = cur + (K + 1) := by omega
      obtain ⟨sRest, hRestBlk, hRestSpec⟩ :=
        withAndChainCz_scoped K (cur + 1) (by omega) wNext (by dsimp [wNext]; omega)
          (fun i ↦ ctrls i.succ) (fun i ↦ by have := hctrls i.succ; omega)
          (fun i ↦ wire_ne_of_gt (by have := hctrls i.succ; dsimp [wNext]; omega))
          (by simpa [andChainOut, heq] using hBody)
      have hStep := ScopedCzPredBlock.withTempBitCz_block
        (Q := cleanRem M (M - cur)) (Q_in := cleanRem M (M - (cur + 1)))
        acc (ctrls 0) wNext (hne0 0)
        (wire_ne_of_lt (by dsimp [wNext]; omega))
        (wire_ne_of_lt (by have := hctrls 0; dsimp [wNext]; omega))
        (fun β hβ ↦ hβ wNext (by dsimp [wNext]; omega))
        (fun β hβ w hw ↦ by
          rw [Function.update_of_ne (wire_ne_of_gt (by dsimp [wNext]; omega))]
          exact hβ w (by omega))
        hRestBlk
      refine ⟨fun β ↦ sRest (Function.update β wNext (β acc * β (ctrls 0))),
        hStep, fun β hβ ↦ ?_⟩
      let β₁ := Function.update β wNext (β acc * β (ctrls 0))
      have hcl₁ : cleanRem M (M - (cur + 1)) β₁ := fun w hw ↦ by
        dsimp [β₁]
        rw [Function.update_of_ne (wire_ne_of_gt (by dsimp [wNext]; omega))]
        exact hβ w (by omega)
      obtain ⟨hbelow, hout_val⟩ := hRestSpec β₁ hcl₁
      refine ⟨fun w hw ↦ ?_, ?_⟩
      · dsimp only
        rw [hbelow w (by omega)]
        exact Function.update_of_ne (wire_ne_of_lt (by dsimp [wNext]; omega)) _ _
      · dsimp only [andChainOut]
        rw [hout_val]
        have hw_self : β₁ wNext = β acc * β (ctrls 0) := Function.update_self _ _ _
        have hc_rest : ∀ i : Fin K, β₁ (ctrls i.succ) = β (ctrls i.succ) := fun i ↦
          Function.update_of_ne (wire_ne_of_lt (by have := hctrls i.succ; dsimp [wNext]; omega)) _ _
        simp_rw [hw_self, hc_rest, Fin.prod_univ_succ]
        ring

/-- `31`-`TempAnd` (`124 T`, `0 TOFF`) `33`-bit nonzero reflection `(-1)^[x ≠ 0]` on `33 + 33`
  wires:
flips `0..32`, computes the `32`-way AND of `0..31` into `⟨63⟩` (`31` `TempAnd`s on `33..63`),
kicks `.cz ⟨63⟩ ⟨32⟩`, and flips the global `-1` phase via `0`-`T` `.cz ⟨64⟩ ⟨65⟩` on two clean
scratch wires toggled to `|1⟩`, giving `1 + ∏_{i=0}^{32} (α_i + 1) = predNotZero33 α`. -/
def progNotZero33Cz : TempCzProg (33 + 33) :=
  let all33 : Fin 33 → Wire (33 + 33) := fun i ↦ ⟨i.val, by omega⟩
  let w0 : Wire (33 + 33) := ⟨0, by decide⟩
  let rest31 : Fin 31 → Wire (33 + 33) := fun i ↦ ⟨i.val + 1, by omega⟩
  let w32 : Wire (33 + 33) := ⟨32, by decide⟩
  let w64 : Wire (33 + 33) := ⟨64, by decide⟩
  let w65 : Wire (33 + 33) := ⟨65, by decide⟩
  .seq
    (withCliffAllocCz (.seq (.x w64) (.x w65)) (.cz w64 w65 (by decide)))
    (withCliffAllocCz (xVec 33 all33)
      (withAndChainCz 31 33 (by decide) w0 (by decide) rest31
        (fun i ↦ by dsimp [rest31]; omega)
        (fun i ↦ wire_ne_of_lt (by dsimp [w0, rest31]; omega))
        (fun out ↦
          if hne : out ≠ w32 then .cz out w32 hne else .nil)))

theorem progNotZero33Cz_count : progNotZero33Cz.countTempAnd = 31 := by
  dsimp only [progNotZero33Cz]
  simp only [TempCzProg.countTempAnd, withCliffAllocCz_countTempAnd, zero_add]
  exact withAndChainCz_countTempAnd 31 33 (by decide) _ _ _ _ _ _ 0
    (fun out ↦ by split_ifs <;> rfl)

theorem progNotZero33Cz_spec : ValidCleanPredCz (cleanRem (33 + 33) 33) progNotZero33Cz ∧ (∀ α
    : BitAssignment 33, progNotZero33Cz.evalBits (padZeroBits α) = padZeroBits α) ∧ (∀ α :
    BitAssignment 33, progNotZero33Cz.evalSign (padZeroBits α) = predNotZero33 α) := by
  let all33 : Fin 33 → Wire (33 + 33) := fun i ↦ ⟨i.val, by omega⟩
  let w0 : Wire (33 + 33) := ⟨0, by decide⟩
  let rest31 : Fin 31 → Wire (33 + 33) := fun i ↦ ⟨i.val + 1, by omega⟩
  let w32 : Wire (33 + 33) := ⟨32, by decide⟩
  let w63 : Wire (33 + 33) := ⟨63, by decide⟩
  let w64 : Wire (33 + 33) := ⟨64, by decide⟩
  let w65 : Wire (33 + 33) := ⟨65, by decide⟩
  have hGlob : ScopedCzPredBlock (33 + 33) (cleanRem (33 + 33) 33)
      (CliffProg.seq (.x w64) (.x w65)).eval (.cz w64 w65 (by decide))
      (withCliffAllocCz (.seq (.x w64) (.x w65)) (.cz w64 w65 (by decide))) :=
    ScopedCzPredBlock.withCliffAllocCz_block (Q_in := fun _ ↦ True)
      (.seq (.x w64) (.x w65)) (fun _ _ ↦ trivial)
      (ScopedCzPredBlock.cz_leaf _ w64 w65 (by decide))
  have hout63 : andChainOut (M := 33 + 33) 31 33 (by decide) w0 = w63 :=
    Fin.ext (by decide)
  have hBody63 : ScopedCzPredBlock (33 + 33) (cleanRem (33 + 33) ((33 + 33) - (33 + 31))) id
      (.cz w63 w32 (by decide)) ((fun out : Wire (33 + 33) ↦ if hne : out ≠ w32 then
      TempCzProg.cz out w32 hne else .nil) (andChainOut 31 33 (by decide) w0)) := by
    rw [hout63]
    dsimp only
    rw [ditePos (by decide : w63 ≠ w32)]
    exact ScopedCzPredBlock.cz_leaf _ w63 w32 (by decide)
  obtain ⟨sChain, hChainBlk, hChainSpec⟩ :=
    withAndChainCz_scoped (M := 33 + 33)
      (body := fun out ↦ if hne : out ≠ w32 then .cz out w32 hne else .nil)
      31 33 (by decide) w0 (by decide) rest31
      (fun i ↦ by dsimp [rest31]; omega)
      (fun i ↦ wire_ne_of_lt (by dsimp [w0, rest31]; omega))
      hBody63
  have hx_supp : (xVec 33 all33).SupportsBelow 33 :=
    xVec_supportsBelow 33 all33 (fun i ↦ by dsimp [all33]; omega)
  have hMain : ScopedCzPredBlock (33 + 33) (cleanRem (33 + 33) 33)
      (sChain ∘ (xVec 33 all33).eval) (.cz w63 w32 (by decide))
      (withCliffAllocCz (xVec 33 all33)
        (withAndChainCz 31 33 (by decide) w0 (by decide) rest31
          (fun i ↦ by dsimp [rest31]; omega)
          (fun i ↦ wire_ne_of_lt (by dsimp [w0, rest31]; omega))
          (fun out ↦ if hne : out ≠ w32 then .cz out w32 hne else .nil))) :=
    ScopedCzPredBlock.withCliffAllocCz_block (xVec 33 all33)
      (fun β hβ w hw ↦ by
        rw [CliffProg.eval_outside (xVec 33 all33) hx_supp β w hw]
        exact hβ w hw)
      hChainBlk
  obtain ⟨hvSeq, hbSeq, hsSeq⟩ := ScopedCzPredBlock.seq_spec hGlob hMain
  refine ⟨hvSeq, fun α ↦ hbSeq (padZeroBits α) (padZeroBits_cleanRem α), fun α ↦ ?_⟩
  have hpad : cleanRem (33 + 33) 33 (padZeroBits α) := padZeroBits_cleanRem α
  refine Eq.trans (hsSeq (padZeroBits α) hpad) ?_
  have hGlobSign : (TempCzProg.cz w64 w65 (by decide)).evalSign
      ((CliffProg.seq (.x w64) (.x w65)).eval (padZeroBits α)) = 1 := by
    dsimp [TempCzProg.evalSign, CliffProg.eval]
    rw [Function.update_self, Function.update_of_ne (by decide : w64 ≠ w65),
      Function.update_self, Function.update_of_ne (by decide : w65 ≠ w64),
      hpad w64 (by decide), hpad w65 (by decide)]
    decide
  rw [hGlobSign]
  let βx := (xVec 33 all33).eval (padZeroBits α)
  have hx_cl : cleanRem (33 + 33) 33 βx := fun w hw ↦ by
    dsimp only [βx]
    rw [CliffProg.eval_outside (xVec 33 all33) hx_supp _ w hw]
    exact hpad w hw
  have hall_inj : Function.Injective all33 := fun _ _ h ↦ by
    have hv := congrArg Fin.val h
    dsimp [all33] at hv
    exact Fin.ext hv
  have hx_val (i : Fin 33) : βx (all33 i) = α i + 1 := by
    dsimp [βx]
    rw [xVec_eval 33 all33 hall_inj, itePos ⟨i, rfl⟩,
      padZeroBits_ltAux α (all33 i) (by dsimp [all33]; omega)]
  obtain ⟨hbelow, hout_prod⟩ := hChainSpec βx hx_cl
  rw [hout63] at hout_prod
  dsimp only [Function.comp_apply, TempCzProg.evalSign]
  rw [hout_prod, hbelow w32 (by decide)]
  unfold predNotZero33
  by_cases hzero : ((basisBitsEquiv 33).symm α).val = 0
  · have hx1 (k : Fin 33) : βx (all33 k) = 1 := by
      have hb := congrFun ((basisBitsEquiv 33).apply_symm_apply α) k
      rw [show (basisBitsEquiv 33).symm α = 0 from Fin.ext hzero] at hb
      have hk0 : α k = 0 := by
        simpa [-Nat.reducePow, basisBits_eq_testBit] using hb.symm
      simpa [hk0] using hx_val k
    rw [itePos hzero, show βx w0 = 1 from hx1 0, show βx w32 = 1 from hx1 ⟨32, by decide⟩]
    simp [show ∀ i : Fin 31, βx (rest31 i) = 1 from fun i ↦ hx1 ⟨i.val + 1, by omega⟩]
  · rw [iteNeg hzero]
    obtain ⟨k, hk1⟩ : ∃ k : Fin 33, α k = 1 := by
      by_contra hnone
      have hall0 : α = 0 := funext fun k ↦
        (bit_cases (α k)).resolve_right fun hk1 ↦ hnone ⟨k, hk1⟩
      subst hall0
      have h0idx : (basisBitsEquiv 33).symm 0 = 0 := by
        apply (basisBitsEquiv 33).injective
        rw [(basisBitsEquiv 33).apply_symm_apply]
        funext k
        change (0 : ZMod 2) = basisBits 33 0 k
        simp [-Nat.reducePow, basisBits_eq_testBit]
      exact hzero (congrArg Fin.val h0idx)
    have hxk0 : βx (all33 k) = 0 := by simpa [hk1, CharTwo.add_self_eq_zero] using hx_val k
    have hprod0 : (βx w0 * ∏ i : Fin 31, βx (rest31 i)) * βx w32 = 0 := by
      rcases eq_or_ne k 0 with rfl | hk0'
      · simp [show βx w0 = 0 from hxk0]
      · rcases eq_or_ne k ⟨32, by decide⟩ with rfl | hk32
        · simp [show βx w32 = 0 from hxk0]
        · have hv0 : k.val ≠ 0 := Fin.val_ne_of_ne hk0'
          have hv32 : k.val ≠ 32 := Fin.val_ne_of_ne hk32
          let i₀ : Fin 31 := ⟨k.val - 1, by omega⟩
          have hi₀ : βx (rest31 i₀) = 0 := by
            rwa [show rest31 i₀ = all33 k from Fin.ext (by dsimp [rest31, all33, i₀]; omega)]
          rw [Finset.prod_eq_zero (Finset.mem_univ i₀) hi₀]
          simp
    rw [hprod0, add_zero]

attribute [local irreducible] progNotZero33Cz

/-! ## Section 4: `249`-AND `progStage2Cz_295`, `dCoarseGood33_262` (`1,408 T`), and
  `dPrep3_216_262` (`1,649 T`) -/

/-! ## Section 5: `swap3PiOracle80` and `262`-Wire Slot-3 `MomSingleSlotOracle` Constructors -/

open SpecsAux.BridgeFermionicComm.SpecInner (permElectron)
open SpecsAux.SpecMirror.SixChannelHamiltonianSplit (sixChannelShifted)
open TwosCompAndWire0Cancel (smToTwosSysUnitary)

/-- `0`-gate `piSwap3Core` conjugator on any `MomSingleSlotOracle 80 48 3`, preserving
`mWork`, `tSlot`, `wSlot`, `eShift`, `epsIntr`, and `bUnitTwos`. -/
noncomputable def swap3PiOracle80 (s3 : MomSingleSlotOracle 80 48 3) :
    MomSingleSlotOracle 80 48 3 where
  mWork := s3.mWork
  wSlot := s3.wSlot
  eShift := s3.eShift
  epsIntr := s3.epsIntr
  uSlotCat := fun cfg ↦ unitaryConj (rCore0_80.embedUnitary uPiSwap3Core) (s3.uSlotCat cfg)
  uSlotEff := fun cfg ↦ unitaryConj uPiSwap3Core (s3.uSlotEff cfg)
  bUnitTwos := s3.bUnitTwos
  hWNonneg := s3.hWNonneg
  hIntertwines := fun cfg U_catTwist hcol ↦ by
    have hPi : IntertwinesMomCat U_catTwist (rCore0_80.embedUnitary uPiSwap3Core) uPiSwap3Core :=
      intertwinesMomCat_of_coreOnly U_catTwist uPiSwap3Core
    have hProd := (hPi.mul (s3.hIntertwines cfg U_catTwist hcol)).mul hPi
    have hCatEq : (rCore0_80.embedUnitary uPiSwap3Core * s3.uSlotCat cfg) *
        rCore0_80.embedUnitary uPiSwap3Core =
        unitaryConj (rCore0_80.embedUnitary uPiSwap3Core) (s3.uSlotCat cfg) := by
      apply Subtype.ext
      change (rCore0_80.embedUnitary uPiSwap3Core).1 * (s3.uSlotCat cfg).1 *
        (rCore0_80.embedUnitary uPiSwap3Core).1 = _
      rw [unitaryConj_val, embed_uPiSwap3Core_self_adj]
    have hEffEq : (uPiSwap3Core * s3.uSlotEff cfg) * uPiSwap3Core =
        unitaryConj uPiSwap3Core (s3.uSlotEff cfg) := by
      apply Subtype.ext
      change uPiSwap3Core.1 * (s3.uSlotEff cfg).1 * uPiSwap3Core.1 = _
      rw [unitaryConj_val, uPiSwap3Core_self_adj]
    rwa [hCatEq, hEffEq] at hProd
  hSA := fun cfg ↦
    (unitaryConj_sa_and_offProj uPiSwap3Core (s3.uSlotEff cfg)
      (uPiSwap3Core_comm_momCoinProj (fullSysCoinIdx 3)) (s3.hSA cfg) (s3.hOffCoin cfg)).1
  hOffCoin := fun cfg ↦
    (unitaryConj_sa_and_offProj uPiSwap3Core (s3.uSlotEff cfg)
      (uPiSwap3Core_comm_momCoinProj (fullSysCoinIdx 3)) (s3.hSA cfg) (s3.hOffCoin cfg)).2
  hTopBlock := fun cfg ↦
    topBlock_unitaryConj_absorb (coreHadamardMom 80) uPiSwap3Core (s3.uSlotEff cfg) _ _
      (QRegister.basisOutcomeProjector_conjTranspose _ _)
      uPiSwap3Core_mul_coreHadamard_ancProj (s3.hTopBlock cfg)
  hUnitNorm := s3.hUnitNorm
  hPermSm := s3.hPermSm
  hErrIntrSm := s3.hErrIntrSm

theorem fixesLow3924_swap3PiOracle80_eff (s3 : MomSingleSlotOracle 80 48 3)
    (cfg : SpecsAux.SpecMirror.Configuration)
    (hEff : FixesLow3924 h3924_momCore (s3.uSlotEff cfg).1) : FixesLow3924 h3924_momCore
    ((swap3PiOracle80 s3).uSlotEff cfg).1 := fixesLow3924_uPiSwap3Core.unitaryConj hEff

/-- Generic `(K, D)` `262`-wire unpermuted `MomSingleSlotOracle 80 48 3` constructor
(`tSlot = 3298 + tCore`, arbitrary `uCore149`, `uCoreEff`, `wSlot`, `eShift`, `epsIntr`,
`bUnitTwos`). -/
noncomputable def mkSlot3RawMomOracle80_Wide
    (wSlot : SpecsAux.SpecMirror.Configuration → ℝ)
    (eShift : SpecsAux.SpecMirror.Configuration → ℝ)
    (epsIntr : ℝ)
    (uCore149 : SpecsAux.SpecMirror.Configuration → Unitary (2 ^ 149))
    (uCoreEff : SpecsAux.SpecMirror.Configuration → Unitary (2 ^ (momCoreWires 80)))
    (bUnitTwos : SpecsAux.SpecMirror.Configuration →
      Operator (2 ^ SpecsAux.SpecMirror.systemQubits))
    (hWNonneg : ∀ cfg, 0 ≤ wSlot cfg)
    (hIntertwines : ∀ cfg (U_catTwist : Unitary (2 ^ 48)),
      (∀ m : Fin (2 ^ 48), U_catTwist.1 m 0 = PhaseGradCatalystCore.phaseGradientState 48 m) →
      IntertwinesMomCat U_catTwist
        (unitaryConj (rCore0_80.embedUnitary (uPrep3_216 (le_refl 80)))
          ((sel149 (le_refl 80)).embedUnitary (uCore149 cfg)))
        (unitaryConj (uPrep3_216 (le_refl 80)) (uCoreEff cfg)))
    (hSA : ∀ cfg, (unitaryConj (uPrep3_216 (le_refl 80)) (uCoreEff cfg)).1ᴴ =
      (unitaryConj (uPrep3_216 (le_refl 80)) (uCoreEff cfg)).1)
    (hOffCoin : ∀ cfg,
      (unitaryConj (uPrep3_216 (le_refl 80)) (uCoreEff cfg)).1 *
        (1 - momCoinProj 80 (fullSysCoinIdx 3)) =
      1 - momCoinProj 80 (fullSysCoinIdx 3))
    (hTopBlock : ∀ cfg,
      let c := fullSysCoinIdx 3
      let P_anc := (momAncReg 80).basisOutcomeProjector (coinSelOutcome (momCoin3Sel 80) c)
      P_anc * (unitaryConj (coreHadamardMom 80)
        (unitaryConj (uPrep3_216 (le_refl 80)) (uCoreEff cfg))).1 * P_anc =
      P_anc * (momSysReg 80).embedMatrix (bUnitTwos cfg) * P_anc)
    (hUnitNorm : ∀ cfg, ‖bUnitTwos cfg‖ ≤ 1)
    (hPermSm : ∀ cfg (g : Equiv.Perm (Fin SpecsAux.SpecMirror.numElectrons))
      (x y : Fin (2 ^ SpecsAux.SpecMirror.systemQubits)),
      IsGridState x → IsGridState y →
      (smToTwosSysUnitary.1 * bUnitTwos cfg * smToTwosSysUnitary.1)
        (permElectron g x) (permElectron g y) =
      (smToTwosSysUnitary.1 * bUnitTwos cfg * smToTwosSysUnitary.1) x y)
    (hErrIntrSm : ∀ cfg (spinUp : Finset (Fin SpecsAux.SpecMirror.numElectrons)),
      let E_vec : Fin 6 → ℝ := fun j ↦ if j = 3 then eShift cfg else 0
      ‖fermionicProjector spinUp *
          ((wSlot cfg : ℂ) • (smToTwosSysUnitary.1 * bUnitTwos cfg * smToTwosSysUnitary.1) -
            sixChannelShifted cfg E_vec 3) *
          fermionicProjector spinUp‖ ≤ epsIntr) :
    MomSingleSlotOracle 80 48 3 where
  mWork := 262
  wSlot := wSlot
  eShift := eShift
  epsIntr := epsIntr
  uSlotCat := fun cfg ↦ unitaryConj (rCore0_80.embedUnitary (uPrep3_216 (le_refl 80)))
    ((sel149 (le_refl 80)).embedUnitary (uCore149 cfg))
  uSlotEff := fun cfg ↦ unitaryConj (uPrep3_216 (le_refl 80)) (uCoreEff cfg)
  bUnitTwos := bUnitTwos
  hWNonneg := hWNonneg
  hIntertwines := hIntertwines
  hSA := hSA
  hOffCoin := hOffCoin
  hTopBlock := hTopBlock
  hUnitNorm := hUnitNorm
  hPermSm := hPermSm
  hErrIntrSm := hErrIntrSm

/-- Generic `(K, D)` `262`-wire `piSwap3Core`-conjugated `MomSingleSlotOracle 80 48 3` constructor
(`mWork = 262`, `tSlot = 3298 + tCore`). -/
noncomputable def mkSlot3Swap3MomOracle80Gen_Wide
    (wSlot : SpecsAux.SpecMirror.Configuration → ℝ)
    (eShift : SpecsAux.SpecMirror.Configuration → ℝ)
    (epsIntr : ℝ)
    (uCore149 : SpecsAux.SpecMirror.Configuration → Unitary (2 ^ 149))
    (uCoreEff : SpecsAux.SpecMirror.Configuration → Unitary (2 ^ (momCoreWires 80)))
    (bUnitTwos : SpecsAux.SpecMirror.Configuration →
      Operator (2 ^ SpecsAux.SpecMirror.systemQubits))
    (hWNonneg : ∀ cfg, 0 ≤ wSlot cfg)
    (hIntertwines : ∀ cfg (U_catTwist : Unitary (2 ^ 48)),
      (∀ m : Fin (2 ^ 48), U_catTwist.1 m 0 = PhaseGradCatalystCore.phaseGradientState 48 m) →
      IntertwinesMomCat U_catTwist
        (unitaryConj (rCore0_80.embedUnitary (uPrep3_216 (le_refl 80)))
          ((sel149 (le_refl 80)).embedUnitary (uCore149 cfg)))
        (unitaryConj (uPrep3_216 (le_refl 80)) (uCoreEff cfg)))
    (hSA : ∀ cfg, (unitaryConj (uPrep3_216 (le_refl 80)) (uCoreEff cfg)).1ᴴ =
      (unitaryConj (uPrep3_216 (le_refl 80)) (uCoreEff cfg)).1)
    (hOffCoin : ∀ cfg,
      (unitaryConj (uPrep3_216 (le_refl 80)) (uCoreEff cfg)).1 *
        (1 - momCoinProj 80 (fullSysCoinIdx 3)) =
      1 - momCoinProj 80 (fullSysCoinIdx 3))
    (hTopBlock : ∀ cfg,
      let c := fullSysCoinIdx 3
      let P_anc := (momAncReg 80).basisOutcomeProjector (coinSelOutcome (momCoin3Sel 80) c)
      P_anc * (unitaryConj (coreHadamardMom 80)
        (unitaryConj (uPrep3_216 (le_refl 80)) (uCoreEff cfg))).1 * P_anc =
      P_anc * (momSysReg 80).embedMatrix (bUnitTwos cfg) * P_anc)
    (hUnitNorm : ∀ cfg, ‖bUnitTwos cfg‖ ≤ 1)
    (hPermSm : ∀ cfg (g : Equiv.Perm (Fin SpecsAux.SpecMirror.numElectrons))
      (x y : Fin (2 ^ SpecsAux.SpecMirror.systemQubits)),
      IsGridState x → IsGridState y →
      (smToTwosSysUnitary.1 * bUnitTwos cfg * smToTwosSysUnitary.1)
        (permElectron g x) (permElectron g y) =
      (smToTwosSysUnitary.1 * bUnitTwos cfg * smToTwosSysUnitary.1) x y)
    (hErrIntrSm : ∀ cfg (spinUp : Finset (Fin SpecsAux.SpecMirror.numElectrons)),
      let E_vec : Fin 6 → ℝ := fun j ↦ if j = 3 then eShift cfg else 0
      ‖fermionicProjector spinUp *
          ((wSlot cfg : ℂ) • (smToTwosSysUnitary.1 * bUnitTwos cfg * smToTwosSysUnitary.1) -
            sixChannelShifted cfg E_vec 3) *
          fermionicProjector spinUp‖ ≤ epsIntr) :
    MomSingleSlotOracle 80 48 3 :=
  swap3PiOracle80 (mkSlot3RawMomOracle80_Wide wSlot eShift epsIntr uCore149 uCoreEff bUnitTwos
    hWNonneg hIntertwines hSA hOffCoin hTopBlock hUnitNorm hPermSm hErrIntrSm)

set_option maxRecDepth 2000

end ConfigSlot3PrepWideAndSwap3

end Slot3PrepWideAndSwap3
end
set_option exponentiation.threshold 256
end Slot3PrepWideAndSwap3

section Slot3Exact216Oracle80_Wide
local instance (priority := 1000000) instNeZeroTwoPow_Slot3Exact216Oracle80_Wide (k : ℕ) :
    NeZero (2 ^ k) := ⟨(Nat.two_pow_pos k).ne'⟩

public section

/-
Untruncated Exact-216 (`Br = 38`, `Bk = 42`) Slot-3 Momentum Oracle at `mWork = 262`.

Provides:
1. Reference trajectory `st2..st8` bridging `st0` (`padZeroBits 288 α`) and `st1` (`pStep1`)
   through `fwdPrep216_275`, `midAct216_275`, and `revUncomp216_275` under `clearMW` /
   `clearMuCoinMW`.
2. `swapMW12` (`[177..189) ↔ [411..423)`) `StepBundle` adapter for `accXorTrim275` (`340 T`) and
   `397`-wire `StepBundle` adapter for `dMidKick216_397` (`6,848 T`) on `rCombBase`.
3. `16,392`-`T`, `0`-`.TOFF` dynamic core `dCoreExact216_262` realizing `uCore149_216 cfg` on
   `mWork = 262` clean scratch wires via `rDummy26 = rCore.slice 18 26`.
4. Turnkey `slot3Exact216Ora80_262 : MomSingleSlotOracle 80 48 3` (`mWork = 262`, `tSlot = 19,690`,
   `0` `.TOFF`) with `CommutesWithReg rEC80`, `wSlot = wIdealRat 3`, `eShift = 0`,
   `epsIntr ≤ 3 / 1000000`, and `FixesLow3924` certificates on `uSlotCat` and `uSlotEff`.
-/

namespace Slot3Exact216Oracle80_Wide

section ConfigSlot3Exact216Oracle80_Wide

set_option maxRecDepth 4096
set_option exponentiation.threshold 256

set_option maxHeartbeats 400000 in -- Large circuit/arithmetic proof
local instance (priority :=
  100) instLoc_Slot3Exact216Oracle80_Wide_1InstNeZeroTwoPow (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩

noncomputable section

open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt HermitianMat Real
open scoped Matrix ComplexOrder MatrixOrder BigOperators

open SpecsAux.SpecMirror
open FullSysMomSlots0135Concrete (momCoreWires)
open Slot3StreamUncK35Shift3 (uPiSwap3Core_eq_of_perm)

set_option maxHeartbeats 400000 in -- Large circuit/arithmetic proof
theorem uPiSwap3Core_prep273_eq_streamUnc :
    Slot3Prep273AndSwap3.uPiSwap3Core = Slot3StreamUncK35Shift3.uPiSwap3Core := by
  refine uPiSwap3Core_eq_of_perm
    Slot3Prep273AndSwap3.uPiSwap3Core Slot3Prep273AndSwap3.piSwap3CorePerm rfl (fun z w ↦ ?_)
  rw [Slot3Prep273AndSwap3.basisBits_piSwap3CorePerm]
  refine congrArg (basisBits (momCoreWires 80) z) ?_
  apply Fin.ext
  dsimp [Slot3Prep273AndSwap3.piSwap3Wire, Slot3Prep273AndSwap3.piSwap3WireFun,
    Slot3StreamUncK35Shift3.piSwap3Wire, Slot3StreamUncK35Shift3.piSwap3WireFun]

end

set_option maxRecDepth 2000

end ConfigSlot3Exact216Oracle80_Wide

end Slot3Exact216Oracle80_Wide
end
set_option exponentiation.threshold 256
end Slot3Exact216Oracle80_Wide

section HarmonicScheduleBridge
local instance (priority := 1000000) instNeZeroTwoPow_HarmonicScheduleBridge (k : ℕ) :
    NeZero (2 ^ k) := ⟨(Nat.two_pow_pos k).ne'⟩

/-
Harmonic & Per-Horizon Schedule Bridge (`HarmonicScheduleBridge`).

Provides:
1. Harmonic schedules `harmonicSchedule k j = k * (j + 1)`, constant `alphaOfBetaSchedule`,
   and universal `BetaGeneralCertSpec` -> `36/37` `gidneyRotToffEquiv` sum bound.
2. Tightened `catPrepErr1q := 16811 / 10^9` single-catalyst prep bound (any `B_tot : ℕ`),
   parametric `(catErr, ε_BE)` step-error caps, exact `2^48` `rnCap` lemmas across
   `ε_BE` regimes, and parametric `gidneySingleCat_of_gridPerturbation_twos_step_gen`.
3. Width-polymorphic hoisted stream init/uninit (`hoAncillasM mWork`, `220 ≤ mWork`),
   `HoistedRSum42TwistBundleGen`, and `GidneyGuardWrapDynBundle`.
4. Parametric `tHoistedSelOfTwist`, hoisted Gidney segment circuits/counts/realizations,
   `E_stream42 -> pSum42Zero` intertwining, and turnkey harmonic & per-horizon closures.
-/

public section

namespace HarmonicScheduleBridge

section ConfigHarmonicScheduleBridge

set_option backward.isDefEq.respectTransparency true
set_option exponentiation.threshold 8192
set_option maxRecDepth 4096

set_option maxHeartbeats 400000 in -- Large circuit/arithmetic proof
local instance (priority :=
  1000000) instLoc_HarmonicScheduleBridge_1InstNeZeroTwoPowHarm (k : ℕ) : NeZero (2 ^ k) :=
  ⟨Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos k)⟩

open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt Real
open scoped Matrix BigOperators Matrix.Norms.L2Operator

open DyadicQft64.PhasePerm SpecsAux.SpecMirror
open InterWalkRSum42Hoist (mActHoist)

/- == Section 1: Harmonic Schedules, `BetaGeneralCertSpec` Bridge & Tight `catPrepErr1q` == -/

set_option maxHeartbeats 400000 in -- Large circuit/arithmetic proof
abbrev hoAncillasM (mWork : ℕ) : ℕ := mActHoist + mWork

set_option maxRecDepth 2000
set_option exponentiation.threshold 256

end ConfigHarmonicScheduleBridge

end HarmonicScheduleBridge
end
set_option exponentiation.threshold 256
end HarmonicScheduleBridge

section ApexTwistOut334
local instance (priority := 1000000) instNeZeroTwoPow_ApexTwistOut334 (k : ℕ) :
    NeZero (2 ^ k) := ⟨(Nat.two_pow_pos k).ne'⟩

/-
# `HoistedTwistRestOutBundle 334` Over `dStream42Init` and `HoistedRSum42TwistBundleGen`

Builds a `HoistedTwistRestOutBundle (mPayload := 80) (mPGTwist := 48) 334` directly from
`InterWalkRSum42Hoist.dStream42Init` / `dStream42Uninit` and any `288`-wire hoisted twist
bundle `twHoist : HoistedRSum42TwistBundleGen 288 (fun c ↦ uTwistRestHoisted (trunc36Cfg c)) tHoist`
by contracting the `46` complement wires (`1` signal + `3` slack-save + `42` `rSum0`) around
`rCTFull` (`4,082` wires) inside `kFull80 = 4,128` onto clean workspace `[0 .. 46)` alongside
`[46 .. 334)` (`288` wires).
-/

public section

namespace ApexTwistOut334

section ConfigApexTwistOut334

set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency true
set_option exponentiation.threshold 8192

local instance (priority :=
  1000000) instLoc_ApexTwistOut334_1InstNeZeroTwoPowApexTwistOu (k : ℕ) : NeZero (2 ^ k) :=
  ⟨Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos k)⟩

open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt Real
open SpecsAux.SpecMirror
open FullSysCatSegmentBridge (fullSysCoreWires)
open InterWalkRSum42Hoist (qreg_block_apply kFull80 rCoreFull rPG48Full rSum0 rCSFull uXor32Full
  uStreamFull uStream42Init)

theorem mul_comm_proj_aux {d : ℕ} {A B P : Matrix (Fin d) (Fin d) ℂ}
    (hA : A * P = P * A) (hB : B * P = P * B) : (A * B) * P = P * (A * B) := by
  rw [Matrix.mul_assoc, hB, ← Matrix.mul_assoc, hA, Matrix.mul_assoc]

theorem fullSysCoreWires80_eq : fullSysCoreWires 80 = 4034 := rfl

/-- Signal wire `[4034 .. 4035)` inside `kFull80 = 4128`. -/
def rGap1Full : QRegister 1 kFull80 := QRegister.block 4034 1 (by decide)

/-- Slack-save wires `[4083 .. 4086)` inside `kFull80 = 4128`. -/
def rGap3Full : QRegister 3 kFull80 := QRegister.block 4083 3 (by decide)

theorem rGap1Full_val (i : Fin 1) : (rGap1Full i).val = 4034 + i.val := by
  rw [rGap1Full, qreg_block_apply]

theorem rGap3Full_val (i : Fin 3) : (rGap3Full i).val = 4083 + i.val := by
  rw [rGap3Full, qreg_block_apply]

theorem rSum0_val (i : Fin 42) : (rSum0 i).val = 4086 + i.val := by
  have hk : InterWalkRSum42Hoist.kActOrig = 4086 := rfl
  rw [rSum0, qreg_block_apply]; dsimp only; rw [hk]

theorem rCoreFull_val (i : Fin (fullSysCoreWires 80)) : (rCoreFull i).val = i.val := by
  let w1 := FullSysCatSegmentBridge.beCoreBlock 80 i
  have hw1 : w1.val = i.val := by
    change (QRegister.block 0 (fullSysCoreWires 80) _ i).val = i.val
    rw [qreg_block_apply]; dsimp only; omega
  let w2 := InterWalkRSum42Hoist.rBEOrig w1
  have hw2 : w2.val = w1.val := by
    change (QRegister.block 0 _ _ w1).val = w1.val
    rw [qreg_block_apply]; dsimp only; omega
  change (InterWalkRSum42Hoist.rAct0 w2).val = i.val
  rw [InterWalkRSum42Hoist.rAct0, qreg_block_apply]
  dsimp only; omega

theorem rPG48Full_val (i : Fin 48) : (rPG48Full i).val = 4035 + i.val := by
  let q : Fin 48 := SingleCatSpine.rTopCatSlice 48 48 le_rfl i
  have hq : q.val = i.val := by
    change (QRegister.block (48 - 48) 48 _ i).val = i.val
    rw [qreg_block_apply]; dsimp only; omega
  have hCat : SingleCatClosure.rCatSelLoc 80 48 q =
      Fin.natAdd (FullSysCatSegmentBridge.fullSysBEWires 80) q := by
    ext; change (QRegister.block _ 48 _ q).val = _
    rw [qreg_block_apply]; simp
  let s1 := SingleCatClosure.inCatTotSingleCat 48 40 q
  have hs1 : s1.val = q.val := by
    change (QRegister.block 0 48 _ q).val = q.val
    rw [qreg_block_apply]; dsimp only; omega
  let s2 := SingleCatClosure.inCatScratchSingleCat 80 48 40 s1
  have hs2 : s2.val = 87 + s1.val := by
    have hSeg : PolymorphicTopClosure.mSegAncPoly 80 = 87 := rfl
    change (QRegister.block (PolymorphicTopClosure.mSegAncPoly 80) _ _ s1).val = 87 + s1.val
    rw [qreg_block_apply]; dsimp only; omega
  let s3 := SingleCatClosure.rAncInSingleCat 80 48 40 s2
  have hs3 : s3.val = 3948 + s2.val := by
    have hSys : SpecsAux.SpecMirror.systemQubits = 3948 := rfl
    change (QRegister.block SpecsAux.SpecMirror.systemQubits _ _ s2).val = 3948 + s2.val
    rw [qreg_block_apply]; dsimp only; omega
  change (InterWalkRSum42Hoist.rAct0
    (InterWalkRSum42Hoist.rSegOrig
      (SingleCatClosure.rCatSelLoc 80 48 q))).val = 4035 + i.val
  rw [hCat, QRegister.concat_apply_right]
  change (InterWalkRSum42Hoist.rAct0 s3).val = 4035 + i.val
  rw [InterWalkRSum42Hoist.rAct0, qreg_block_apply]
  dsimp only; omega

theorem hGap1_disj_Gap3 : rGap1Full.DisjointWires rGap3Full := by
  rw [QRegister.disjoint_iff]; intro i j h
  have hv := congrArg Fin.val h; rw [rGap1Full_val, rGap3Full_val] at hv; omega

/-- Combined `4`-wire active gap (`rGap1Full ++ rGap3Full`) inside `kFull80 = 4128`. -/
noncomputable def rGap4Full : QRegister 4 kFull80 :=
  rGap1Full.concat rGap3Full hGap1_disj_Gap3

theorem hGap4_disj_Sum0 : rGap4Full.DisjointWires rSum0 :=
  QRegExt.disjointWires_concat_left
    (by
      rw [QRegister.disjoint_iff];
      intro i j h;
      have hv :=
        congrArg Fin.val h; rw [rGap1Full_val, rSum0_val] at hv; omega)
    (by
      rw [QRegister.disjoint_iff];
      intro i j h;
      have hv :=
        congrArg Fin.val h; rw [rGap3Full_val, rSum0_val] at hv; omega)

theorem hCoreFull_disj_Gap4 : rCoreFull.DisjointWires rGap4Full :=
  QRegExt.disjointWires_concat_right
    (by
      rw [QRegister.disjoint_iff];
      intro i j h;
      have hv :=
        congrArg Fin.val h; rw [rCoreFull_val, rGap1Full_val] at hv; have hi : i.val < 4034 :=
        fullSysCoreWires80_eq ▸ i.isLt; omega)
    (by
      rw [QRegister.disjoint_iff];
      intro i j h;
      have hv :=
        congrArg Fin.val h; rw [rCoreFull_val, rGap3Full_val] at hv; have hi : i.val < 4034 :=
        fullSysCoreWires80_eq ▸ i.isLt; omega)

theorem hPG48Full_disj_Gap4 : rPG48Full.DisjointWires rGap4Full :=
  QRegExt.disjointWires_concat_right
    (by
      rw [QRegister.disjoint_iff];
      intro i j h;
      have hv :=
        congrArg Fin.val h; rw [rPG48Full_val, rGap1Full_val] at hv; omega)
    (by
      rw [QRegister.disjoint_iff];
      intro i j h;
      have hv :=
        congrArg Fin.val h; rw [rPG48Full_val, rGap3Full_val] at hv; omega)

theorem uStream42Init_comm_gap4 : uStream42Init.1 * rGap4Full.basisOutcomeProjector 0 =
    rGap4Full.basisOutcomeProjector 0 * uStream42Init.1 := by
  have hX : uXor32Full.1 * rGap4Full.basisOutcomeProjector 0 =
      rGap4Full.basisOutcomeProjector 0 * uXor32Full.1 :=
    (QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint rCoreFull) rGap4Full
      hCoreFull_disj_Gap4 _ 0
  have hS : ∀ w : Fin 3, (uStreamFull w).1 * rGap4Full.basisOutcomeProjector 0 =
      rGap4Full.basisOutcomeProjector 0 * (uStreamFull w).1 := fun w ↦
    (QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint (rCSFull w)) rGap4Full
      (QRegExt.disjointWires_concat_left
        hCoreFull_disj_Gap4 ((QRegister.disjoint_comm.mp hGap4_disj_Sum0).compose_left _)) _ 0
  unfold uStream42Init
  simp only [Submonoid.coe_mul]
  exact mul_comm_proj_aux hX (mul_comm_proj_aux (hS 2) (mul_comm_proj_aux (hS 1) (mul_comm_proj_aux
    (hS 0) hX)))

end ConfigApexTwistOut334

end ApexTwistOut334
end
set_option exponentiation.threshold 256
end ApexTwistOut334

section GidneyTwoAngleGuardWrap220
local instance (priority := 1000000) instNeZeroTwoPow_GidneyTwoAngleGuardWrap220 (k : ℕ) :
    NeZero (2 ^ k) := ⟨(Nat.two_pow_pos k).ne'⟩

/-
Two-Angle SU(2) Gidney Signal-Rotation & 220-Wire Split-Center Guard Closure
(`GidneyTwoAngleGuardWrap220`).

Provides:
1. Per-step 2-angle Gidney rotation Toffoli-equivalent cost `gidneyTwoAngleRotToffEquiv`
   (`= (w_C - 2) + (w_D - 2) + max (w_C - 2) (w_D - 2)`) and tail-recursive `listZipSumTR`
   sum theorem for `(C_opt_list, D_opt_list)`.
2. Two-angle 43-wire dynamic signal-rotation primitive `dSigMidTwoAngleGidney43Dyn`
   (`optX43 preX ;; dKickGidney43Dyn C_d ;; H(q0) ;; dKickGidney43Dyn D_d ;; H(q0) ;; optX43 postX`)
   sharing `twoAngleCarryWidth42 C_d.val D_d.val <= 40` clean carry wires (`0` `.TOFF`, `0`
   `rConst42`),
   reference `Circuit n` counterpart, and clean-carry `wp` / commutation / projection bundle.
3. Catalyst intertwining (`twoAngleSigUnitary42`, `intertwinesCat_uSignalRotTwoAngle43`,
   `intertwinesCat_uGuardWrapTwoAngleSingleCat`) and `fixesLow3924_uGuardWrapTwoAngleSingleCat80`.
4. Parametric `SplitGuardParams` 2-angle guard-wrap (`dGuardSignalWrapTwoAngleGidneySplit`,
   `dGuardSignalWrapTwoAngleGidneyPolySingleCatDyn`, `Classical.choose`-sealed
   `dGuardSignalWrapTwoAngleGidneyPolyOpaqueDyn`), `GidneyTwoAngleGuardWrapDynBundle`,
   turnkey `220`-wire (`31,384 T`) & `288`-wire (`31,112 T`) bundles, and single-catalyst
   2-angle segment circuits (`uSegTwoAngleSingleCat`,
   `mkSegTwoAngleGidneyPolySingleCatDyn`).
-/

public section

namespace GidneyTwoAngleGuardWrap220

section ConfigGidneyTwoAngleGuardWrap220

set_option exponentiation.threshold 256
set_option maxRecDepth 4096

local instance (priority :=
  1000000) instLoc_GidneyTwoAngleGuardWrap220_1InstNeZeroTwoPow (k : ℕ) : NeZero (2 ^ k) :=
  ⟨Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos k)⟩

open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt Real HermitianMat
open scoped Matrix ComplexOrder MatrixOrder Circuit.Notation Matrix.Norms.L2Operator BigOperators

open SpecsAux.SpecMirror
open SpecsAux.FullScaleBESector hiding phaseGradientState
open SpecsAux.PhaseGradCatalystCore
open PhaseGradSignalRot hiding IntertwinesCat
open TFreeLaurentGQSP CatalyzedLaurentGQSP
open BidirectionalCatalyzedGQSP
open BidirectionalCatalyzedGQSPBridge
open FullSysCatSegmentBridge
open GidneySignalRotPart1
open GidneySignalRotPart2

/- == Section 1: 2-Angle Carry Width, Toffoli-Equiv Cost & Tail-Recursive List Sums == -/

def gidneyTwoAngleRotToffEquiv (c d : ℕ) : ℕ := (activeMsbWidth42 c - 2) +
    (activeMsbWidth42 d - 2) + max (activeMsbWidth42 c - 2) (activeMsbWidth42 d - 2)

/-- 43-wire 2-angle `0-rConst42` Gidney signal-rotation unitary (`rfl`-matching
  `HarmonicTwoAngleBridge`). -/
noncomputable def uSignalRotTwoAngle43 (C_d D_d : Fin (2 ^ 42)) : Unitary (2 ^ (1 + 42)) :=
  (Circuit.H ⟨0, by decide⟩).eval *
    (uKickGidney43 D_d * ((Circuit.H ⟨0, by decide⟩).eval * uKickGidney43 C_d))

/-- 43-wire 2-angle signal-rotation unitary wrapped by `optX43 preX` and `optX43 postX`. -/
noncomputable def uSigMidTwoAngle43 (preX postX : Bool) (C_d D_d : Fin (2 ^ 42)) :
    Unitary (2 ^ (1 + 42)) :=
  (optX43 postX).eval * (uSignalRotTwoAngle43 C_d D_d * (optX43 preX).eval)

theorem slice_zero_disjoint_rest {n k m : ℕ} (r : QRegister k n) (hm : m ≤ k) :
    (r.slice 0 m (FullSysCatSegmentBridge.fullSys_zero_add_le_of_le hm)).DisjointWires
      (r.slice m (k - m) (Nat.add_sub_of_le hm).le) := by
  rw [QRegister.disjoint_iff]
  intro i j hij
  have hv := congrArg Fin.val (r.wires.injective hij)
  dsimp [QRegister.slice] at hv
  have := i.isLt
  omega

theorem slice_zero_concat_image_eq {n k m : ℕ} (r : QRegister k n) (hm : m ≤ k) : ((r.slice 0
    m (FullSysCatSegmentBridge.fullSys_zero_add_le_of_le hm)).concat (r.slice m (k - m)
    (Nat.add_sub_of_le hm).le) (slice_zero_disjoint_rest r hm)).image = r.image := by
  ext w
  simp only [QRegister.mem_image]
  refine ⟨?_, ?_⟩
  · rintro ⟨idx, rfl⟩
    refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) idx
    · rw [QRegister.concat_apply_left]
      exact ⟨⟨0 + i.val, by have := i.isLt; omega⟩, rfl⟩
    · rw [QRegister.concat_apply_right]
      exact ⟨⟨m + j.val, by have := j.isLt; omega⟩, rfl⟩
  · rintro ⟨idx, rfl⟩
    by_cases hlt : idx.val < m
    · refine ⟨Fin.castAdd (k - m) ⟨idx.val, hlt⟩, ?_⟩
      rw [QRegister.concat_apply_left]
      exact congrArg r (Fin.ext (Nat.zero_add idx.val))
    · refine ⟨Fin.natAdd m ⟨idx.val - m, by have := idx.isLt; omega⟩, ?_⟩
      rw [QRegister.concat_apply_right]
      exact congrArg r (Fin.ext (Nat.add_sub_of_le (Nat.le_of_not_lt hlt)))

theorem basisOutcomeProjector_zero_slice_split {n k m : ℕ} (r : QRegister k n) (hm : m ≤ k) :
    r.basisOutcomeProjector 0 = (r.slice 0 m
    (FullSysCatSegmentBridge.fullSys_zero_add_le_of_le hm)).basisOutcomeProjector 0 *
    (r.slice m (k - m) (Nat.add_sub_of_le hm).le).basisOutcomeProjector 0 :=
  (basisOutcomeProjector_zero_eq_of_image_eq r _ (slice_zero_concat_image_eq r hm).symm).trans
    (QRegExt.basisOutcomeProjector_concat_zero _ _ (slice_zero_disjoint_rest r hm))

end ConfigGidneyTwoAngleGuardWrap220

end GidneyTwoAngleGuardWrap220

end
set_option exponentiation.threshold 256
end GidneyTwoAngleGuardWrap220

section HoistBorrow42ProjBridge
local instance (priority := 1000000) instNeZeroTwoPow_HoistBorrow42ProjBridge (k : ℕ) :
    NeZero (2 ^ k) := ⟨(Nat.two_pow_pos k).ne'⟩

/-
# Borrowed-`rSum42` Subspace Realization & Hoisted Schedule Bridge (`HoistBorrow42ProjBridge`)

Generalizes clean-workspace dynamic-circuit composition to arbitrary input operators / partial
isometries (`RealizesOnProj E_in U d`), so hoisted subroutines inside the post-twist `pSum42Zero`
window can borrow the zeroed `42`-wire `rSum0` register alongside `rWork` (`rWorkBorrow42`,
width `42 + mWork`, `+0 T`, `+0` qubits) without requiring unitarity off `E_stream42`:

1. **`RealizesOnProj E_in U d`**: store-closed weakest-precondition compression
   `E_inᴴ * M'.1.1 * E_in = E_inᴴ * (U.1ᴴ * M.1.1 * U.1) * E_in`, supporting both Hermitian
   projectors (`pZero`) and partial isometries (`pHoist = embedMatrix E_stream42 * P_work`),
   with asymmetric intertwining composition `RealizesOnProj.seq_intertwine` / `seq_trans`,
   iteration `repeatSeqIdentity`, adaptive schedule `runScheduleCircuitAdaptive`, and direct
   endpoint discharge `toRealizesUnitaryFromBasisOutcomesAndZeroWorkspace`.
2. **`rWorkBorrow42`, `pHoist`, `pZero`, & Clean Lifters**: `rWorkBorrow42 rAct rWork hDisj`
   concatenates `rAct.compose rSum0` with `rWork`, proves wire disjointness from all `rAct0`
   subregisters (`rSegFull`, `rCore`, `rPG48`, `rCTFull`), identifies
   `pZero rAct rWork = (rWorkBorrow42 rAct rWork hDisj).basisOutcomeProjector 0`, and lifts
   standard `RealizesEmbeddedUnitaryWithCleanWorkspace` leaves on `(rAct, rWork)` and
   `(rAct.compose sel, rWorkBorrow42)` in 1 line.
3. **`HoistedBorrow42SelectSpec` & Turnkey Per-Horizon Gidney Closures**: decouples hoisted
   `SELECT` width completely from `hsel.mWorkSelect`, provides
   `hoistedBorrow42SelectSpecOfPostTwist`
   for any `pZero`-window `rWorkBorrow42` circuit (`Slot3`, `3-Pass Barrel`, `QFT`, `PosPhase`),
   and exports `mkPerHorizonBorrow42GidneyProgramM`, `_const_cost`, and
   `_correctness_of_gridPerturbation`.
-/

public section

namespace HoistBorrow42ProjBridge

section ConfigHoistBorrow42ProjBridge

set_option backward.isDefEq.respectTransparency true
set_option exponentiation.threshold 8192
set_option maxRecDepth 16384

local instance (priority :=
  1000000) instLoc_HoistBorrow42ProjBridge_1InstNeZeroTwoPowBor (k : ℕ) : NeZero (2 ^ k) :=
  ⟨Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos k)⟩

open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt Real
open scoped Matrix BigOperators Matrix.Norms.L2Operator

open SpecsAux.SpecMirror
open SpecsAux.PhaseGradCatalystCore (unitarySandwichPow)
open FullSysWalkStepEndpoint
  (fullSys_zero_add_le cleanBasisScheduleProgramGen
   approximatesTimeEvolution_conj_sysUnitary unitarySandwichPow_conj_outer)
open InterWalkRSum42Hoist (qreg_ext kFull80 uStream42Init)
open GidneySignalRotHoistBridge (coe_pow_unitary)

/- == Section 1: `RealizesOnProj` — Store-Closed Subspace / Partial-Isometry Realization == -/

/-- Store-closed subspace or partial-isometry unitary realization: for every post-observable `M`,
`wp d.compile` maps `fun _ ↦ M` to a store-independent observable `fun _ ↦ M'` satisfying
`E_inᴴ * M'.1.1 * E_in = E_inᴴ * (U.1ᴴ * M.1.1 * U.1) * E_in`. -/
def RealizesOnProj {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)]
    (E_in : Operator (2 ^ n)) (U : Unitary (2 ^ n)) (d : DynamicCircuit Var n) : Prop := ∀ M :
    Observable (Fin (2 ^ n)), ∃ M' : Observable (Fin (2 ^ n)), wp d.compile (fun _ ↦ M) = (fun _ ↦
      M') ∧
    E_inᴴ * M'.1.1 * E_in = E_inᴴ * (U.1ᴴ * M.1.1 * U.1) * E_in

theorem RealizesOnProj.identity {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ} [NeZero (2 ^
    n)]
    (E_in : Operator (2 ^ n)) :
    RealizesOnProj (Var := Var) E_in 1 .identity := by
  intro M
  exact ⟨M, rfl, by simp⟩

/-- Sequential composition of `RealizesOnProj` across an intertwining transition `U₁.1 * E₁ = E₂ *
  V`
(no Hermitianity or idempotence required on `E₁`, `E₂`, or `V`). -/
theorem RealizesOnProj.seq_intertwine {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    [NeZero (2 ^ n)] {E₁ E₂ V : Operator (2 ^ n)} {U₁ U₂ : Unitary (2 ^ n)}
    {d₁ d₂ : DynamicCircuit Var n} (hTrans : U₁.1 * E₁ = E₂ * V)
    (h₁ : RealizesOnProj E₁ U₁ d₁) (h₂ : RealizesOnProj E₂ U₂ d₂) : RealizesOnProj E₁
    (U₂ * U₁) (.seq d₁ d₂) := by
  intro M
  obtain ⟨M₂, hwp₂, hproj₂⟩ := h₂ M
  obtain ⟨M₁, hwp₁, hproj₁⟩ := h₁ M₂
  refine ⟨M₁, by simp only [DynamicCircuit.compile_seq, wp_qSeq, hwp₂, hwp₁], ?_⟩
  have hTransH : E₁ᴴ * U₁.1ᴴ = Vᴴ * E₂ᴴ := by
    simpa only [Matrix.conjTranspose_mul] using congrArg Matrix.conjTranspose hTrans
  calc
    E₁ᴴ * M₁.1.1 * E₁ = E₁ᴴ * (U₁.1ᴴ * M₂.1.1 * U₁.1) * E₁ := hproj₁
    _ = (E₁ᴴ * U₁.1ᴴ) * M₂.1.1 * (U₁.1 * E₁) := by simp only [Matrix.mul_assoc]
    _ = Vᴴ * (E₂ᴴ * M₂.1.1 * E₂) * V := by
        rw [hTransH, hTrans]; simp only [Matrix.mul_assoc]
    _ = Vᴴ * (E₂ᴴ * (U₂.1ᴴ * M.1.1 * U₂.1) * E₂) * V := by rw [hproj₂]
    _ = (Vᴴ * E₂ᴴ) * (U₂.1ᴴ * M.1.1 * U₂.1) * (E₂ * V) := by simp only [Matrix.mul_assoc]
    _ = E₁ᴴ * ((U₂ * U₁).1ᴴ * M.1.1 * (U₂ * U₁).1) * E₁ := by
        rw [← hTransH, ← hTrans]
        simp only [Submonoid.coe_mul, Matrix.conjTranspose_mul, Matrix.mul_assoc]

/-- Lift any clean-workspace `(rAct, rWork)` circuit `d` (`rAct.DisjointWires rWork`) to
`RealizesOnProj (rAct.embedMatrix A * rWork.basisOutcomeProjector 0) (rAct.embedUnitary u) d`. -/
theorem RealizesOnProj.of_clean_embed {Var : Type} [Fintype Var] [DecidableEq Var] {k m n : ℕ}
    [NeZero (2 ^ n)] {rAct : QRegister k n} {rWork : QRegister m n}
    (hDisj : rAct.DisjointWires rWork) (A : Operator (2 ^ k)) {u : Unitary (2 ^ k)}
    {d : DynamicCircuit Var n} (hd : DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace
    rAct rWork u d) : RealizesOnProj (rAct.embedMatrix A * rWork.basisOutcomeProjector 0)
    (rAct.embedUnitary u) d := by
  intro M
  obtain ⟨M', hwp, hproj⟩ := hd M
  refine ⟨M', hwp, ?_⟩
  let B := rAct.embedMatrix A
  let P := rWork.basisOutcomeProjector 0
  have hBP : B * P = P * B :=
    (QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint rAct) rWork hDisj A 0
  have hEH : (B * P)ᴴ = Bᴴ * P := by
    rw [hBP, Matrix.conjTranspose_mul, QRegister.basisOutcomeProjector_conjTranspose]
  change (B * P)ᴴ * M'.1.1 * (B * P) =
    (B * P)ᴴ * ((rAct.embedUnitary u).1ᴴ * M.1.1 * (rAct.embedUnitary u).1) * (B * P)
  calc
    (B * P)ᴴ * M'.1.1 * (B * P) = (Bᴴ * P) * M'.1.1 * (P * B) := by
        rw [hEH, hBP]
    _ = Bᴴ * (P * M'.1.1 * P) * B := by
        simp only [Matrix.mul_assoc]
    _ = Bᴴ * (P * ((rAct.embedUnitary u).1ᴴ * M.1.1 * (rAct.embedUnitary u).1) * P) * B := by
        rw [hproj]
    _ = (Bᴴ * P) * ((rAct.embedUnitary u).1ᴴ * M.1.1 * (rAct.embedUnitary u).1) * (P * B) := by
        simp only [Matrix.mul_assoc]
    _ = (B * P)ᴴ * ((rAct.embedUnitary u).1ᴴ * M.1.1 * (rAct.embedUnitary u).1) * (B * P) := by
        rw [← hEH, ← hBP]

theorem pow_mul_intertwine {d : ℕ} {A E B : Operator d} (h : A * E = E * B) :
    ∀ k : ℕ, A ^ k * E = E * B ^ k
  | 0 => by simp
  | k + 1 => by
      rw [pow_succ, pow_succ, Matrix.mul_assoc, h, ← Matrix.mul_assoc,
        pow_mul_intertwine h k, Matrix.mul_assoc]

theorem RealizesOnProj.repeatSeqIdentity
    {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)]
    {E V : Operator (2 ^ n)} {U : Unitary (2 ^ n)} {d : DynamicCircuit Var n}
    (hPres : U.1 * E = E * V) (hd : RealizesOnProj E U d) :
    ∀ R : ℕ, RealizesOnProj E (U ^ R) (Nat.repeat (.seq d) R .identity)
  | 0 => by
      simpa [Nat.repeat] using RealizesOnProj.identity (Var := Var) E
  | R + 1 => by
      simpa only [Nat.repeat, pow_succ] using
        hd.seq_intertwine hPres (hd.repeatSeqIdentity hPres R)

/-- Discharge `RealizesUnitaryFromBasisOutcomesAndZeroWorkspace` directly from `RealizesOnProj E_in`
whenever `E_in` fixes `rAnc.basisOutcomeProjector 0` (`E_in * P_anc = P_anc`). -/
theorem RealizesOnProj.toRealizesUnitaryFromBasisOutcomesAndZeroWorkspace
    {Var : Type} [Fintype Var] [DecidableEq Var] {kSys mAct mWork n : ℕ} [NeZero (2 ^ n)]
    (rSys : QRegister kSys n) (outcomes : Finset (Fin (2 ^ kSys)))
    (rActAnc : QRegister mAct n) (rWork : QRegister mWork n)
    (hSysAct : rSys.DisjointWires rActAnc)
    (hSubWork : rActAnc.DisjointWires rWork)
    (hSysAnc : rSys.DisjointWires (rActAnc.concat rWork hSubWork))
    {E_in : Operator (2 ^ n)} {u : Unitary (2 ^ (kSys + mAct))} {d : DynamicCircuit Var n}
    (hAbsorb : E_in * (rActAnc.concat rWork hSubWork).basisOutcomeProjector 0 =
      (rActAnc.concat rWork hSubWork).basisOutcomeProjector 0)
    (hd : RealizesOnProj E_in ((rSys.concat rActAnc hSysAct).embedUnitary u) d) :
    let rAnc := rActAnc.concat rWork hSubWork
    let locAct : QRegister (kSys + mAct) (kSys + (mAct + mWork)) :=
      QRegister.block 0 (kSys + mAct) (by omega)
    RealizesUnitaryFromBasisOutcomesAndZeroWorkspace
      rSys outcomes rAnc hSysAnc (locAct.embedUnitary u) d.compile := by
  intro rAnc locAct M
  obtain ⟨M', hwp, hproj⟩ := hd M
  intro σ
  apply le_of_eq
  ext1
  ext1
  let P_anc := rAnc.basisOutcomeProjector 0
  let P_sys := rSys.basisOutcomesProjector outcomes
  have hc : P_anc * P_sys = P_sys * P_anc := by
    dsimp only [P_anc, P_sys]
    rw [QRegister.basisOutcomeProjector_eq_diagonal, QRegister.basisOutcomesProjector,
      Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    exact congrArg Matrix.diagonal (funext fun _ ↦ mul_comm _ _)
  have hCommOut (A : Operator (2 ^ n)) :
      P_anc * (P_sys * A * P_sys) * P_anc = P_sys * (P_anc * A * P_anc) * P_sys := by
    calc P_anc * (P_sys * A * P_sys) * P_anc
        = (P_anc * P_sys) * A * (P_sys * P_anc) := by simp only [Matrix.mul_assoc]
      _ = (P_sys * P_anc) * A * (P_anc * P_sys) := by rw [hc]
      _ = P_sys * (P_anc * A * P_anc) * P_sys := by simp only [Matrix.mul_assoc]
  have hAbsorbH : P_anc * E_inᴴ = P_anc := by
    simpa only [P_anc, Matrix.conjTranspose_mul, QRegister.basisOutcomeProjector_conjTranspose]
      using congrArg Matrix.conjTranspose hAbsorb
  have hSand (A : Operator (2 ^ n)) :
      P_anc * A * P_anc = P_anc * (E_inᴴ * A * E_in) * P_anc := by
    calc P_anc * A * P_anc
        = (P_anc * E_inᴴ) * A * (E_in * P_anc) := by rw [hAbsorbH, hAbsorb]
      _ = P_anc * (E_inᴴ * A * E_in) * P_anc := by simp only [Matrix.mul_assoc]
  have hRegEq : (rSys.concat rAnc hSysAnc).compose locAct = rSys.concat rActAnc hSysAct :=
    qreg_ext fun idx ↦ Fin.addCases
      (fun i ↦ by
        simp [QRegister.compose,
          show locAct (Fin.castAdd mAct i) =
            Fin.castAdd (mAct + mWork) i from Fin.ext (by simp [locAct])])
      (fun j ↦ by
        simp [QRegister.compose, rAnc,
          show locAct (Fin.natAdd kSys j) =
            Fin.natAdd kSys (Fin.castAdd mWork j) from Fin.ext (by simp [locAct])]) idx
  have hWpQ : (wpQAssignCompat ((rSys.concat rAnc hSysAnc).embedUnitary (locAct.embedUnitary
      u)) (fun _ ↦ M) σ).1.1 = ((rSys.concat rActAnc hSysAct).embedUnitary u).1ᴴ * M.1.1 *
      ((rSys.concat rActAnc hSysAct).embedUnitary u).1 := by
    rw [← QRegister.embedUnitary_compose, hRegEq]
    simp [wpQAssignCompat, qAssignObsMap, Matrix.star_eq_conjTranspose, Matrix.mul_assoc]
  have hRestrOut (B : CQAssertionCompat Var (2 ^ n)) (r : QRegister kSys n)
      (outs : Finset (Fin (2 ^ kSys))) (st : Store Var) :
      (CQAssertion.restrictToBasisOutcomes B r outs st).1 =
        (B st).1.conj (r.basisOutcomesProjector outs) := rfl
  simp only [CQAssertion.restrictToZeroAncilla_coe, hRestrOut, HermitianMat.conj_apply_mat,
    QRegister.basisOutcomeProjector_conjTranspose, QRegister.basisOutcomesProjector_conjTranspose,
    hwp]
  change P_anc * (P_sys * (wpQAssignCompat _ (fun _ ↦ M) σ).1.1 * P_sys) * P_anc =
    P_anc * (P_sys * M'.1.1 * P_sys) * P_anc
  rw [hCommOut, hCommOut, hWpQ, hSand, hSand M'.1.1, hproj]

theorem embedUnitary_pow {k n : ℕ} (r : QRegister k n) (U : Unitary (2 ^ k)) :
    ∀ t : ℕ, (r.embedUnitary U) ^ t = r.embedUnitary (U ^ t)
  | 0 => by simp
  | t + 1 => by rw [pow_succ, pow_succ, embedUnitary_pow r U t, QRegister.embedUnitary_mul]

/-- Symbolic `{kSys mAct mWork : ℕ}` basis-wrapped schedule correctness over `RealizesOnProj`. -/
theorem cleanBasisSchedule_correctness_onProj_gen
    {Cfg Spin Var : Type} [Fintype Var] [DecidableEq Var]
    {kSys mAct mWork n : ℕ} [NeZero (2 ^ n)]
    {R : Fin 10 → ℕ}
    {mkBasisFwd mkInit mkUninit mkBasisInv :
      (rAct : QRegister (kSys + mAct) n) →
      (rWork : QRegister mWork n) → rAct.DisjointWires rWork → DynamicCircuit Var n}
    {mkSeg : Cfg → Fin 10 →
      (rAct : QRegister (kSys + mAct) n) →
      (rWork : QRegister mWork n) → rAct.DisjointWires rWork → DynamicCircuit Var n}
    {E₀ E_seg V_init V_seg : QRegister (kSys + mAct) n → QRegister mWork n → Operator (2 ^ n)}
    {H : Operator (2 ^ kSys)} {P_sector : Spin → Operator (2 ^ kSys)}
    {outcomes : Finset (Fin (2 ^ kSys))}
    {U_sys : Unitary (2 ^ kSys)}
    {V_prep V_inv : Unitary (2 ^ (kSys + mAct))}
    {W_seg : Cfg → Fin 10 → Unitary (2 ^ (kSys + mAct))}
    (c : Cfg) (j : Fin 10)
    (hEvolConj : ∀ s : Spin,
      ApproximatesTimeEvolution (U_sys.1 * H * U_sys.1ᴴ) (j.val + 1 : ℝ) 0.01
        (U_sys.1 * P_sector s * U_sys.1ᴴ)
        (unitarySandwichPow V_inv (W_seg c j) V_prep (R j)))
    (hAbsorb : ∀ (rSys' : QRegister kSys n) (rActAnc : QRegister mAct n) (rWork : QRegister mWork n)
      (hSysAct : rSys'.DisjointWires rActAnc) (hSubWork : rActAnc.DisjointWires rWork),
      E₀ (rSys'.concat rActAnc hSysAct) rWork *
        (rActAnc.concat rWork hSubWork).basisOutcomeProjector 0 =
      (rActAnc.concat rWork hSubWork).basisOutcomeProjector 0)
    (hTransInit : ∀ rAct rWork, rAct.DisjointWires rWork →
      (rAct.embedUnitary (V_prep *
        (QRegister.block 0 kSys (fullSys_zero_add_le kSys mAct) :
          QRegister kSys (kSys + mAct)).embedUnitary U_sys)).1 * E₀ rAct rWork =
        E_seg rAct rWork * V_init rAct rWork)
    (hPresSeg : ∀ rAct rWork, rAct.DisjointWires rWork →
      (rAct.embedUnitary (W_seg c j)).1 * E_seg rAct rWork = E_seg rAct rWork * V_seg rAct rWork)
    (hInit : ∀ rAct rWork hD,
      RealizesOnProj (E₀ rAct rWork)
        (rAct.embedUnitary (V_prep *
          (QRegister.block 0 kSys (fullSys_zero_add_le kSys mAct) :
            QRegister kSys (kSys + mAct)).embedUnitary U_sys))
        (.seq (mkBasisFwd rAct rWork hD) (mkInit rAct rWork hD)))
    (hSeg : ∀ rAct rWork hD,
      RealizesOnProj (E_seg rAct rWork) (rAct.embedUnitary (W_seg c j)) (mkSeg c j rAct rWork hD))
    (hUninit : ∀ rAct rWork hD,
      RealizesOnProj (E_seg rAct rWork)
        (rAct.embedUnitary
          (((QRegister.block 0 kSys (fullSys_zero_add_le kSys mAct) :
            QRegister kSys (kSys + mAct)).embedUnitary U_sys)⁻¹ * V_inv))
        (.seq (mkUninit rAct rWork hD) (mkBasisInv rAct rWork hD)))
    (rSys : QRegister kSys n)
    (rAnc : QRegister (mAct + mWork) n)
    (hdisj : rSys.DisjointWires rAnc) :
    ∃ W : Unitary (2 ^ (kSys + (mAct + mWork))),
      (∀ s : Spin, ApproximatesTimeEvolution H (j.val + 1 : ℝ) 0.01 (P_sector s) W) ∧
      RealizesUnitaryFromBasisOutcomesAndZeroWorkspace rSys outcomes rAnc hdisj W
        (cleanBasisScheduleProgramGen R mkBasisFwd mkInit mkSeg mkUninit mkBasisInv
          c j rSys rAnc).compile := by
  let sysAct : QRegister kSys (kSys + mAct) := .block 0 kSys (fullSys_zero_add_le kSys mAct)
  let U_full : Unitary (2 ^ (kSys + mAct)) := sysAct.embedUnitary U_sys
  let V_prep' := V_prep * U_full
  let V_inv' := U_full⁻¹ * V_inv
  let locAct : QRegister (kSys + mAct) (kSys + (mAct + mWork)) :=
    QRegister.block 0 (kSys + mAct) (by omega)
  let U_act := unitarySandwichPow V_inv' (W_seg c j) V_prep' (R j)
  refine ⟨locAct.embedUnitary U_act, fun s ↦ ?_, ?_⟩
  · refine approximatesTimeEvolution_embed_clean_work H (j.val + 1 : ℝ) 0.01 (P_sector s) U_act ?_
    dsimp only [U_act, V_prep', V_inv']
    rw [unitarySandwichPow_conj_outer]
    exact approximatesTimeEvolution_conj_sysUnitary U_sys H (P_sector s) (j.val + 1 : ℝ) 0.01
      (unitarySandwichPow V_inv (W_seg c j) V_prep (R j)) (hEvolConj s)
  · simp only [cleanBasisScheduleProgramGen, cleanScheduleProgramGen, dite_eq_left hdisj]
    let rActAnc : QRegister mAct n := rAnc.compose (QRegister.block 0 mAct (by omega))
    let rWork : QRegister mWork n := rAnc.compose (QRegister.block mAct mWork (by omega))
    let hSysAct : rSys.DisjointWires rActAnc := hdisj.compose_right _
    have hSubWork : rActAnc.DisjointWires rWork := by
      rw [QRegister.disjoint_iff]
      intro a b hab
      have hv := congrArg Fin.val (rAnc.wires.injective hab)
      simp at hv
      omega
    have hAncEq : rActAnc.concat rWork hSubWork = rAnc :=
      qreg_ext fun idx ↦ Fin.addCases
        (fun a ↦ by
          rw [QRegister.concat_apply_left]
          refine congrArg rAnc (Fin.ext ?_)
          simp)
        (fun b ↦ by
          rw [QRegister.concat_apply_right]
          refine congrArg rAnc (Fin.ext ?_)
          simp)
        idx
    let rAct : QRegister (kSys + mAct) n := rSys.concat rActAnc hSysAct
    let hD : rAct.DisjointWires rWork := cleanScheduleActWorkDisj hdisj
    have hPowPres : ((rAct.embedUnitary (W_seg c j)) ^ (R j)).1 * E_seg rAct rWork =
        E_seg rAct rWork * (V_seg rAct rWork) ^ (R j) := by
      rw [coe_pow_unitary]
      exact pow_mul_intertwine (hPresSeg rAct rWork hD) (R j)
    have hRunRaw : RealizesOnProj (E₀ rAct rWork)
        (rAct.embedUnitary V_inv' * (rAct.embedUnitary (W_seg c j)) ^ (R j) *
          rAct.embedUnitary V_prep')
        (runScheduleCircuitAdaptive R
          (.seq (mkBasisFwd rAct rWork hD) (mkInit rAct rWork hD))
          (fun j' ↦ mkSeg c j' rAct rWork hD)
          (.seq (mkUninit rAct rWork hD) (mkBasisInv rAct rWork hD)) j) := by
      simpa only [runScheduleCircuitAdaptive, mul_assoc] using
        (hInit rAct rWork hD).seq_intertwine (hTransInit rAct rWork hD)
          (((hSeg rAct rWork hD).repeatSeqIdentity (hPresSeg rAct rWork hD) (R j)).seq_intertwine
            hPowPres (hUninit rAct rWork hD))
    have hUnitEq : rAct.embedUnitary V_inv' * (rAct.embedUnitary (W_seg c j)) ^ (R j) *
        rAct.embedUnitary V_prep' = rAct.embedUnitary U_act := by
      dsimp only [U_act, unitarySandwichPow]
      rw [embedUnitary_pow, ← QRegister.embedUnitary_mul, ← QRegister.embedUnitary_mul]
    rw [hUnitEq] at hRunRaw
    exact realizesUnitary_of_anc_eq hAncEq
      (RealizesOnProj.toRealizesUnitaryFromBasisOutcomesAndZeroWorkspace
        rSys outcomes rActAnc rWork hSysAct hSubWork (by rwa [hAncEq])
        (hAbsorb rSys rActAnc rWork hSysAct hSubWork) hRunRaw)

/- == Section 2: `rWorkBorrow42`, `pHoist`, `pZero`, Disjointness, & Clean-`Borrow42` Lifters == -/

theorem disjointWires_concat_right {k m₁ m₂ n : ℕ} {rA : QRegister k n} {rB : QRegister m₁ n}
    {rC : QRegister m₂ n} {hBC : rB.DisjointWires rC} (hAB : rA.DisjointWires rB)
    (hAC : rA.DisjointWires rC) : rA.DisjointWires (rB.concat rC hBC) := by
  rw [QRegister.disjoint_iff]
  intro i idx hEq
  refine Fin.addCases (m := m₁) (n := m₂)
    (motive := fun idx ↦ rA i = (rB.concat rC hBC) idx → False)
    (fun j hj ↦ hAB.ne i j (by simpa only [QRegister.concat_apply_left] using hj))
    (fun j hj ↦ hAC.ne i j (by simpa only [QRegister.concat_apply_right] using hj))
    idx hEq

theorem basisOutcomeProjector_concat_zero {m₁ m₂ n : ℕ}
    (r₁ : QRegister m₁ n) (r₂ : QRegister m₂ n) (h₁₂ : r₁.DisjointWires r₂) :
    (r₁.concat r₂ h₁₂).basisOutcomeProjector 0 =
      r₁.basisOutcomeProjector 0 * r₂.basisOutcomeProjector 0 := by
  have hZeroBits : ∀ {ℓ : ℕ} (x : Fin (2 ^ ℓ)), x = 0 ↔ ∀ t : Fin ℓ, basisBits ℓ x t = 0 := by
    intro ℓ x
    rw [← (basisBitsEquiv ℓ).apply_eq_iff_eq, funext_iff]
    simp only [basisBits_eq_div_mod, Fin.val_zero, Nat.zero_div, Nat.zero_mod, Nat.cast_zero]
  rw [QRegister.basisOutcomeProjector_eq_diagonal, QRegister.basisOutcomeProjector_eq_diagonal,
    QRegister.basisOutcomeProjector_eq_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1; funext g
  have hiff : (r₁.concat r₂ h₁₂).extractIndex g = 0 ↔
      r₁.extractIndex g = 0 ∧ r₂.extractIndex g = 0 := by
    rw [hZeroBits, hZeroBits, hZeroBits]
    simp only [QRegister.basisBits_extractIndex]
    constructor
    · intro h
      exact ⟨fun i ↦ by simpa only [QRegister.concat_apply_left] using h (Fin.castAdd m₂ i),
        fun j ↦ by simpa only [QRegister.concat_apply_right] using h (Fin.natAdd m₁ j)⟩
    · rintro ⟨h1, h2⟩ idx
      refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) idx
      · simpa only [QRegister.concat_apply_left] using h1 i
      · simpa only [QRegister.concat_apply_right] using h2 j
  by_cases h1 : r₁.extractIndex g = 0 <;> by_cases h2 : r₂.extractIndex g = 0 <;>
    simp [hiff, h1, h2]

theorem embedIntertwine {mWork n : ℕ}
    {rAct : QRegister kFull80 n} {rWork : QRegister mWork n} (hDisj : rAct.DisjointWires rWork)
    {A E₁ E₂ B : Operator (2 ^ kFull80)} (h : A * E₁ = E₂ * B) :
    rAct.embedMatrix A * (rAct.embedMatrix E₁ * rWork.basisOutcomeProjector 0) =
      (rAct.embedMatrix E₂ * rWork.basisOutcomeProjector 0) * rAct.embedMatrix B := by
  calc
    rAct.embedMatrix A * (rAct.embedMatrix E₁ * rWork.basisOutcomeProjector 0)
        = rAct.embedMatrix (A * E₁) * rWork.basisOutcomeProjector 0 := by
            rw [← Matrix.mul_assoc, ← rAct.embedMatrix_mul]
    _ = rAct.embedMatrix E₂ * (rAct.embedMatrix B * rWork.basisOutcomeProjector 0) := by
          rw [h, rAct.embedMatrix_mul, Matrix.mul_assoc]
    _ = (rAct.embedMatrix E₂ * rWork.basisOutcomeProjector 0) * rAct.embedMatrix B := by
          rw [(QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint rAct) rWork hDisj B 0,
            ← Matrix.mul_assoc]

/- == Section 3: `HoistedBorrow42SelectSpec` & `hoistedBorrow42SelectSpecOfPostTwist` == -/

/- == Section 5: Turnkey Per-Horizon Gidney Schedule Closure on `HoistedBorrow42SelectSpec` == -/

attribute [local irreducible] uStream42Init
set_option maxRecDepth 2000
set_option exponentiation.threshold 256

end ConfigHoistBorrow42ProjBridge

end HoistBorrow42ProjBridge
end
set_option exponentiation.threshold 256
end HoistBorrow42ProjBridge

set_option exponentiation.threshold 256

end QuantumComputation.Specs.StoppingPowerSolution
