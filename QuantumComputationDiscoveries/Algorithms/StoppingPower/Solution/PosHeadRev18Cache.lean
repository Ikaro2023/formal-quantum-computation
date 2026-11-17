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

public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.DisjointWiresSymm

@[expose] public section

namespace QuantumComputation.Specs.StoppingPowerSolution
open SpecsAux

section ModPosHeadRev18Cache
@[expose] public section
namespace PosHeadRev18CacheAux
open Operator QProg Matrix HermitianMat LocalClassicalPerm
open scoped Matrix BigOperators ComplexOrder MatrixOrder Circuit.Notation
open Dyadic128CoulombMath
open CanonRank7Circuit
open BchCubeDecoder
open PosSlots24BranchConcrete
open GridGuard654ReflAux (polBit litAndSymStep)
instance (priority := 100000) instNeZeroTwoPowHeadRev18 (n : ℕ) : NeZero (2 ^ n) :=
  ⟨(Nat.two_pow_pos n).ne'⟩
noncomputable section Main
section HeadRev18Concrete
variable {Var : Type} {n : ℕ}
def phcHead_rQRev18 (rCore : QRegister posCoreWires n) : QRegister 18 n where
  wires :=
    { toFun := fun k ↦ (rHeadFine21 rCore) ⟨7 * (k.val / 6) + (5 - k.val % 6) + 1, by omega⟩
      inj' := fun k₁ k₂ h ↦ by
        have hv := congrArg Fin.val ((rHeadFine21 rCore).wires.injective h)
        ext; dsimp only at hv; omega }
theorem phcHead_rQRev18_mem_core (rCore : QRegister posCoreWires n) (k : Fin 18) :
    phcHead_rQRev18 rCore k ∈ rCore.image :=
  slice_image_subset rCore _
    (slice_image_subset (rSubPayloadCore rCore) _
      (QRegister.mem_image _ _ |>.mpr ⟨_, rfl⟩))
theorem phcHead_nuc_ne_core (rCore : QRegister posCoreWires n) (a b : Fin 8) (h : a ≠ b) :
    rNucIdx rCore a ≠ rNucIdx rCore b := (rNucIdx rCore).wires.injective.ne h
theorem phcHead_anc_ne_core (rCore : QRegister posCoreWires n) (a b : Fin 8) (h : a ≠ b) :
    rAnchorIdx rCore a ≠ rAnchorIdx rCore b := (rAnchorIdx rCore).wires.injective.ne h
theorem phcHead_y0_mem_core (rCore : QRegister posCoreWires n) (w : Fin 3) (j : Fin 6) :
    axisBitRev6 (rElecSlot rCore 0) w j ∈ rCore.image :=
  slice_image_subset rCore _ (QRegister.mem_image _ _ |>.mpr ⟨_, rfl⟩)
theorem phcHead_dBit_mem_core (rCore : QRegister posCoreWires n) (idx : Fin 21) :
    rHeadFine21 rCore idx ∈ rCore.image :=
  slice_image_subset rCore _
    (slice_image_subset (rSubPayloadCore rCore) _
      (QRegister.mem_image _ _ |>.mpr ⟨idx, rfl⟩))
theorem phcHead_b0_mem_core (rCore : QRegister posCoreWires n) (w : Fin 3) :
    rCosetB0 rCore w ∈ rCore.image :=
  slice_image_subset rCore _
    (slice_image_subset (rSubPayloadCore rCore) _
      (QRegister.mem_image _ _ |>.mpr ⟨w, rfl⟩))
theorem phcHead_b0_ne_d0 (rCore : QRegister posCoreWires n) (w : Fin 3) :
    rCosetB0 rCore w ≠ rHeadFine21 rCore ⟨7 * w.val, by omega⟩ := by
  intro h
  dsimp [rCosetB0, rHeadFine21, QRegister.slice_apply,
    PosSlots24CompactHead123Alt.qreg_slice_wires,
    PosSlots24CompactHead123Alt.qreg_whole_wires,
    PosSlots24CompactHead123Alt.emb_trans_apply,
    PosSlots24CompactHead123Alt.emb_refl_apply,
    PosSlots24CompactHead123Alt.emb_mk_apply,
    PosSlots24CompactHead123Alt.qreg_block_apply,
    PosSlots24CompactHead123Alt.qreg_block_wires_apply] at h
  have hv := congrArg Fin.val ((rSubPayloadCore rCore).wires.injective h)
  dsimp only at hv; omega
theorem phcHead_y0_ne_q (rCore : QRegister posCoreWires n) (w : Fin 3) (j : Fin 6) :
    axisBitRev6 (rElecSlot rCore 0) w j ≠ rHeadFine21 rCore ⟨7 * w.val + j.val + 1, by omega⟩ := by
  intro h
  dsimp [axisBitRev6, rElecSlot, rHeadFine21, rSubPayloadCore, QRegister.slice_apply,
    PosSlots24CompactHead123Alt.qreg_slice_wires,
    PosSlots24CompactHead123Alt.qreg_whole_wires,
    PosSlots24CompactHead123Alt.emb_trans_apply,
    PosSlots24CompactHead123Alt.emb_refl_apply,
    PosSlots24CompactHead123Alt.emb_mk_apply,
    PosSlots24CompactHead123Alt.qreg_block_apply,
    PosSlots24CompactHead123Alt.qreg_block_wires_apply] at h
  have hv := congrArg Fin.val (rCore.wires.injective h)
  dsimp only at hv; omega
theorem phcHead_s0_ne_y0 (rCore : QRegister posCoreWires n) (w : Fin 3) (j : Fin 6) :
    wSlot0Core rCore ≠ axisBitRev6 (rElecSlot rCore 0) w j := by
  intro h
  dsimp [wSlot0Core, axisBitRev6, rElecSlot, QRegister.slice_apply,
    PosSlots24CompactHead123Alt.qreg_slice_wires,
    PosSlots24CompactHead123Alt.qreg_whole_wires,
    PosSlots24CompactHead123Alt.emb_trans_apply,
    PosSlots24CompactHead123Alt.emb_refl_apply,
    PosSlots24CompactHead123Alt.emb_mk_apply,
    PosSlots24CompactHead123Alt.qreg_block_apply,
    PosSlots24CompactHead123Alt.qreg_block_wires_apply] at h
  have hv := congrArg Fin.val (rCore.wires.injective h)
  dsimp only at hv; omega
theorem phcHead_wSlot2_ne_wSlot1 (rCore : QRegister posCoreWires n) : wSlot2Core rCore ≠
    wSlot1Core rCore := rCore.wires.injective.ne (by decide)
theorem phcHead_polBit_lt216_decide (x0 x1 x2 x3 x4 x5 x6 x7 : ZMod 2) : polBit true (polBit
    false (polBit false (polBit false x7 * polBit false x6)) * polBit false (polBit true
    (polBit true x5 * polBit true (polBit false (polBit false x4 * polBit false x3))))) = if
    decide (x0.val * 1 + x1.val * 2 + x2.val * 4 + x3.val * 8 + x4.val * 16 + x5.val * 32 +
    x6.val * 64 + x7.val * 128 < 216) then 1 else 0 := by
  revert x0 x1 x2 x3 x4 x5 x6 x7
  decide +kernel
theorem phcHead_polBit_lt218_decide (y0 y1 y2 y3 y4 y5 y6 y7 : ZMod 2) : polBit true (polBit
    false (polBit false (polBit false y7 * polBit false y6)) * polBit false (polBit true
    (polBit true y5 * polBit true (polBit false (polBit false (polBit false y4 * polBit false
    y3) * polBit false (polBit true (polBit true y2 * polBit true y1))))))) = if decide
    (y0.val * 1 + y1.val * 2 + y2.val * 4 + y3.val * 8 + y4.val * 16 + y5.val * 32 + y6.val *
    64 + y7.val * 128 < 218) then 1 else 0 := by
  revert y0 y1 y2 y3 y4 y5 y6 y7
  decide +kernel
theorem phcHead_decide_imp_lt_eq (b : Bool) (P : Prop) [Decidable P] :
    decide (b → P) = decide (b → decide P = true) := by
  by_cases hp : P <;> simp [hp]
theorem phcHead_zmod2_polBit_headEn_eval (nLt aLt : Bool) (s0 s1 s2 sr ih : ZMod 2) : polBit
    false (polBit false (polBit false (polBit false (polBit true s2 * polBit true s1) * polBit
    false (polBit true sr * polBit false (if aLt then 1 else 0)))) * polBit false (polBit
    false (polBit true (polBit true s0 * polBit true (if nLt then 1 else 0))) * polBit false
    ih)) = if ((s2 == 0) && Bool.not (s1 == 1) && Bool.not (sr == 1) && (decide (Bool.not (s0
    == 1) → nLt = true) && aLt) && (ih == 1)) then 1 else 0 := by
  revert nLt aLt s0 s1 s2 sr ih
  decide
theorem phcHead_litAndSymStep_anc (polA polB polOut : Bool) (a b anc : Wire n)
    (hab : a ≠ b) (ha : a ≠ anc) (hb : b ≠ anc) :
    (litAndSymStep polA polB polOut a b anc hab ha hb).anc = anc := rfl
theorem phcHead_litAndSymStep_S (polA polB polOut : Bool) (a b anc : Wire n)
    (hab : a ≠ b) (ha : a ≠ anc) (hb : b ≠ anc) :
    (litAndSymStep polA polB polOut a b anc hab ha hb).S = {a, b, anc} := rfl
end HeadRev18Concrete
end Main
end PosHeadRev18CacheAux
end
end ModPosHeadRev18Cache

end QuantumComputation.Specs.StoppingPowerSolution
